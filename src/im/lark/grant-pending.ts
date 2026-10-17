/**
 * 授权申请的状态表（per bot:chat:target）。两个职责合一：
 *  - nonce 防旧卡重放：每次发卡生成 nonce，卡片按钮带它；处置时校验仍匹配。
 *  - 节流：pending 期间 / denied 冷却期间，不重复弹卡。
 *
 * 持久化：按 bot 落盘到 `${dataDir}/grant-pending-<appId>.json`，每次变更原子写，首次访问
 * 某个 bot 时懒加载。daemon 重启前发出、管理员还没处置的授权卡，重启后照样能点——nonce、
 * 卡上暂存的有效期/额度、授权后要重放的原始消息都还在（以前纯内存，重启后点旧卡只会提示失效）。
 *  - 只落「已确认送达」的 pending（发卡成功后由调用方 markPendingDelivered）：发卡途中重启时，
 *    磁盘上不会留下一条没人看得到的 pending，否则申请人会被白白节流到 STALE_PENDING_MS。
 *  - denied 冷却一并落盘，重启不会让刚被拒的人立刻再弹卡。
 *  - 过期条目（denied 冷却已过 / pending 超过 STALE_PENDING_MS 未处置）加载时直接丢弃，与内存
 *    回收同一条规则（isExpired），所以内存里顺手回收的条目不必单独回写。
 *  - 文件读不出 / 损坏时按空表处理（损坏文件被隔离，见 utils/json-file.ts）：旧卡失效、节流清零，
 *    不会凭空放行任何人。
 * owner 私聊发卡名额（tryReserveOwnerDmSlot）仍是纯内存：只是限流，重启清零无害。
 */
import { randomUUID } from 'node:crypto';
import { mkdirSync, readdirSync, unlinkSync } from 'node:fs';
import { dirname, join } from 'node:path';
import { config } from '../../config.js';
import { DEFAULT_GRANT_DURATION_MS, DEFAULT_GRANT_QUOTA } from '../../services/grant-policy.js';
import { atomicWriteFileSync } from '../../utils/atomic-write.js';
import { errorMessage } from '../../utils/error-message.js';
import { isJsonObject, readJsonFileSoft } from '../../utils/json-file.js';
import { logger } from '../../utils/logger.js';

const DENY_COOLDOWN_MS = 10 * 60 * 1000;
/** pending 卡超过此窗口仍未处置即视作废弃（owner 一直没点），可回收。
 *  远大于一次正常授权交互所需时间，正常流程不会被误删。 */
const STALE_PENDING_MS = 24 * 60 * 60 * 1000;
/** 回收节流：每个表已无用条目（denied 冷却已过 / pending 已废弃）的清扫
 *  最多每分钟跑一次，避免在热路径上对全表做 O(n) 扫描。 */
const PRUNE_INTERVAL_MS = 60 * 1000;

const FILE_PREFIX = 'grant-pending-';
const FILE_SUFFIX = '.json';
const FILE_VERSION = 1;

type Entry = {
  state: 'pending' | 'denied';
  nonce?: string;
  ts: number;
  quota?: number;
  durationMs?: number;
  messageData?: any;
  /** 卡片已确认送达。只有送达的 pending 才落盘（denied 不看这个字段）。 */
  delivered?: boolean;
};
type PersistedFile = { version: unknown; entries: Record<string, unknown> };

/** larkAppId → (chat:target → Entry)。按 bot 分表，一个 bot 一个文件。 */
const tables = new Map<string, Map<string, Entry>>();
let lastPrunedAt = 0;

const key = (c: string, t: string) => `${c}:${t}`;

function filePathFor(larkAppId: string): string {
  // appId 来自 bots.json（cli_xxx）；编码一下，异常值里的 `/` 也逃不出 dataDir。
  return join(config.session.dataDir, `${FILE_PREFIX}${encodeURIComponent(larkAppId)}${FILE_SUFFIX}`);
}

function isExpired(e: Entry, now: number): boolean {
  return now - e.ts >= (e.state === 'denied' ? DENY_COOLDOWN_MS : STALE_PENDING_MS);
}

function isPersisted(e: Entry): boolean {
  return e.state === 'denied' || e.delivered === true;
}

/** 磁盘条目 → 内存条目；形状不对返回 null（整条丢弃）。 */
function parseEntry(raw: unknown): Entry | null {
  if (!isJsonObject(raw)) return null;
  const { state, nonce, ts, quota, durationMs, messageData } = raw;
  if (typeof ts !== 'number' || !Number.isFinite(ts)) return null;
  if (state === 'denied') return { state, ts };
  if (state !== 'pending' || typeof nonce !== 'string' || !nonce) return null;
  // 字段缺省 = 不限额 / 永久。值损坏时不能退化成缺省（等于放大授权），整条丢弃 → 旧卡失效。
  if (quota !== undefined && !(Number.isSafeInteger(quota) && quota > 0)) return null;
  if (durationMs !== undefined && !(typeof durationMs === 'number' && Number.isFinite(durationMs) && durationMs > 0)) {
    return null;
  }
  const e: Entry = { state, nonce, ts, delivered: true };
  if (quota !== undefined) e.quota = quota;
  if (durationMs !== undefined) e.durationMs = durationMs;
  // 重放用的原始消息只是锦上添花：坏了就不重放，卡片照样能点。
  if (isJsonObject(messageData)) e.messageData = messageData;
  return e;
}

function load(larkAppId: string): Map<string, Entry> {
  const map = new Map<string, Entry>();
  const path = filePathFor(larkAppId);
  const data = readJsonFileSoft<PersistedFile | null>(path, {
    fallback: () => null,
    validate: (v): v is PersistedFile => isJsonObject(v) && isJsonObject(v.entries),
    label: 'grant-pending',
  });
  if (!data) return map;
  if (data.version !== FILE_VERSION) {
    logger.warn(`[grant-pending:${larkAppId}] ignoring ${path}: unsupported version ${String(data.version)}`);
    return map;
  }
  const now = Date.now();
  let malformed = 0;
  for (const [k, raw] of Object.entries(data.entries)) {
    const e = parseEntry(raw);
    if (!e) { malformed++; continue; }
    if (!isExpired(e, now)) map.set(k, e);
  }
  if (malformed > 0) logger.warn(`[grant-pending:${larkAppId}] dropped ${malformed} malformed entries from ${path}`);
  return map;
}

/** 取某个 bot 的表；该 bot 首次访问时从磁盘加载。 */
function tableFor(larkAppId: string): Map<string, Entry> {
  let map = tables.get(larkAppId);
  if (!map) {
    map = load(larkAppId);
    tables.set(larkAppId, map);
  }
  return map;
}

function serialize(map: Map<string, Entry>, withMessageData: boolean): string {
  const entries: Record<string, unknown> = {};
  for (const [k, e] of map) {
    if (!isPersisted(e)) continue;
    entries[k] = e.state === 'denied'
      ? { state: e.state, ts: e.ts }
      : {
          state: e.state,
          nonce: e.nonce,
          ts: e.ts,
          quota: e.quota,
          durationMs: e.durationMs,
          ...(withMessageData && e.messageData !== undefined ? { messageData: e.messageData } : {}),
        };
  }
  return `${JSON.stringify({ version: FILE_VERSION, entries })}\n`;
}

/** 把某个 bot 的表整体回写。失败只告警：内存仍是权威，只是这段时间的变更扛不过重启。 */
function persist(larkAppId: string): void {
  const map = tables.get(larkAppId);
  if (!map) return;
  const path = filePathFor(larkAppId);
  try {
    let body: string;
    try {
      body = serialize(map, true);
    } catch (err) {
      // messageData 就是飞书推来的 JSON 事件，理论上必能序列化；万一不能，宁可丢掉重放也要保住卡片。
      logger.warn(`[grant-pending:${larkAppId}] messageData not serializable, persisting without replay payloads: ${errorMessage(err)}`);
      body = serialize(map, false);
    }
    mkdirSync(dirname(path), { recursive: true });
    // 含原始消息正文，按凭据级文件处理：0600、不跟随叶子 symlink。
    atomicWriteFileSync(path, body, { mode: 0o600, followTargetSymlink: false });
  } catch (err) {
    logger.warn(`[grant-pending:${larkAppId}] persist to ${path} failed; pending grant cards may not survive a restart: ${errorMessage(err)}`);
  }
}

/** 回收已无效条目，避免 table 随「不同未授权用户 × 群」无限增长。
 *  - denied：冷却已过 → 不再节流，纯属垃圾，删除（允许将来重新申请）。
 *  - pending：超过 STALE_PENDING_MS 仍未处置 → owner 已放弃，删除。
 *  按时间节流，最多每 PRUNE_INTERVAL_MS 全表扫一次（denied 的即时回收另由
 *  isThrottled 顺手做，这里兜住「再也没人 check」的残留条目）。 */
function pruneStale(now: number): void {
  if (now - lastPrunedAt < PRUNE_INTERVAL_MS) return;
  lastPrunedAt = now;
  for (const map of tables.values()) {
    for (const [k, e] of map) {
      if (isExpired(e, now)) map.delete(k);
    }
  }
  pruneOwnerDmSent(now);
}

/** 开一张待处置的卡，返回 nonce。`quota` 为可选的消息额度（已解析），落授权时透传给 grant-store。
 *  `messageData` 为触发本次授权申请的原始飞书消息事件，授权成功后可重放，让用户无需再 @ 一遍。
 *  卡片发出去以后要调 markPendingDelivered，这条 pending 才会落盘、扛过 daemon 重启。 */
export function openPending(
  larkAppId: string,
  chatId: string,
  target: string,
  quota: number | undefined = DEFAULT_GRANT_QUOTA,
  messageData?: any,
  durationMs: number | undefined = DEFAULT_GRANT_DURATION_MS,
): string {
  return openPendingMulti(larkAppId, chatId, [target], quota, messageData, durationMs);
}

/** owner 一次 /grant 多个目标：同一张卡 → 多个 target 共用同一 nonce，
 *  owner 点一次范围即对全部目标生效。校验时每个 target 独立 checkNonce。
 *  `quota`（若有）对每个 target 各自生效（每人 N 条额度）。
 *  `messageData` 为触发本次授权申请的原始飞书消息事件，授权成功后可重放。 */
export function openPendingMulti(
  larkAppId: string,
  chatId: string,
  targets: string[],
  quota: number | undefined = DEFAULT_GRANT_QUOTA,
  messageData?: any,
  durationMs: number | undefined = DEFAULT_GRANT_DURATION_MS,
): string {
  const nonce = randomUUID();
  const ts = Date.now();
  const map = tableFor(larkAppId);
  pruneStale(ts);
  // 被新卡覆盖的旧条目可能已落盘（旧 nonce / denied）；新条目尚未送达不落盘，
  // 所以要回写一次把旧的抹掉，否则重启后旧卡复活。
  let replacedPersisted = false;
  for (const target of targets) {
    const k = key(chatId, target);
    const prev = map.get(k);
    if (prev && isPersisted(prev)) replacedPersisted = true;
    map.set(k, { state: 'pending', nonce, ts, quota, durationMs, messageData });
  }
  if (replacedPersisted) persist(larkAppId);
  return nonce;
}

/** 卡片已送达（发卡 API 成功）→ 标记并落盘，从此这张卡能扛过 daemon 重启。
 *  只认 nonce 仍匹配的 pending：发卡期间已被处置 / 被新卡覆盖的条目不会被复活。 */
export function markPendingDelivered(larkAppId: string, chatId: string, targets: string[], nonce: string): void {
  const map = tableFor(larkAppId);
  let changed = false;
  for (const target of targets) {
    const e = map.get(key(chatId, target));
    if (e && e.state === 'pending' && e.nonce === nonce && !e.delivered) {
      e.delivered = true;
      changed = true;
    }
  }
  if (changed) persist(larkAppId);
}

/** 回读 pending 上挂的限制（owner 点授权按钮时用）。 */
export function getPendingGrantLimits(
  larkAppId: string,
  chatId: string,
  target: string,
): { quota?: number; durationMs?: number } | undefined {
  const e = tableFor(larkAppId).get(key(chatId, target));
  return e && e.state === 'pending' ? { quota: e.quota, durationMs: e.durationMs } : undefined;
}

/** 同一张多目标卡共用一组限制；nonce 不匹配时拒绝暂存。 */
export function updatePendingGrantLimits(
  larkAppId: string,
  chatId: string,
  targets: string[],
  nonce: string,
  patch: { quota?: number | null; durationMs?: number | null },
): boolean {
  const map = tableFor(larkAppId);
  const entries = targets.map(target => map.get(key(chatId, target)));
  if (entries.some(e => !e || e.state !== 'pending' || e.nonce !== nonce)) return false;
  for (const e of entries as Entry[]) {
    if ('quota' in patch) {
      if (patch.quota === null || patch.quota === undefined) delete e.quota;
      else e.quota = patch.quota;
    }
    if ('durationMs' in patch) {
      if (patch.durationMs === null || patch.durationMs === undefined) delete e.durationMs;
      else e.durationMs = patch.durationMs;
    }
  }
  if ((entries as Entry[]).some(isPersisted)) persist(larkAppId);
  return true;
}

/** 回读 pending 上挂的原始消息事件（授权成功后重放，让用户无需再 @ 一遍）。无 / 非 pending → undefined。 */
export function getPendingMessage(larkAppId: string, chatId: string, target: string): any {
  const e = tableFor(larkAppId).get(key(chatId, target));
  return e && e.state === 'pending' ? e.messageData : undefined;
}

/** 卡片处置前校验：必须仍 pending 且 nonce 匹配。 */
export function checkNonce(larkAppId: string, chatId: string, target: string, nonce: string): boolean {
  const e = tableFor(larkAppId).get(key(chatId, target));
  return !!e && e.state === 'pending' && e.nonce === nonce;
}

/** 授权成功 / revoke → 清除，允许将来重新申请。 */
export function clearPending(larkAppId: string, chatId: string, target: string): void {
  const map = tableFor(larkAppId);
  const k = key(chatId, target);
  const prev = map.get(k);
  if (!prev) return;
  map.delete(k);
  if (isPersisted(prev)) persist(larkAppId);
}

/** 拒绝 → 转 denied 冷却态（不清除），旧 nonce 失效，冷却期内不再弹卡。 */
export function markDenied(larkAppId: string, chatId: string, target: string): void {
  const now = Date.now();
  const map = tableFor(larkAppId);
  pruneStale(now);
  map.set(key(chatId, target), { state: 'denied', ts: now });
  persist(larkAppId);
}

/** 入口 A 节流判断：pending 中、或 denied 冷却未过 → true（静默不发卡）。
 *  只需要「要不要发卡」的布尔（对话路径静默丢弃，无需区分原因）；要给用户回话、
 *  需要区分「等 owner 处理」和「已被拒绝」时用 throttleReason。 */
export function isThrottled(larkAppId: string, chatId: string, target: string): boolean {
  return throttleReason(larkAppId, chatId, target) !== null;
}

/**
 * 节流原因（null = 未节流，可发卡）。
 *
 * 与 isThrottled 的关系：后者是本函数的布尔化封装。拆开是因为两者的**消费方式**不同——
 * 对话路径（maybeSendGrantRequestCard）节流时静默 return，用户看不到任何反馈，所以
 * pending 与 denied 混成一个 true 无害；而 ask 卡片点击必须回一句 toast，混用会在
 * owner **已经拒绝**后仍告诉点击者「等 owner 处理」，把已决事项说成待决（pi review F1）。
 *
 * 顺带回收无效条目（与旧 isThrottled 行为一致，不能丢）：废弃的 pending 过 24h、
 * 冷却已过的 denied，都即时删除，让同一发送方能重新申请。磁盘上的同一条加载时会按
 * 同一规则丢弃，所以这里不回写。
 */
export function throttleReason(
  larkAppId: string,
  chatId: string,
  target: string,
): 'pending' | 'denied' | null {
  const map = tableFor(larkAppId);
  const k = key(chatId, target);
  const e = map.get(k);
  if (!e) return null;
  // 废弃 pending（owner 一直没处置，或发卡失败残留）过 stale 窗口 → 本 key 即时回收，
  // 让同一发送方能重新申请。否则只有「别的 target 触发全表 prune」才会清（已送达的 pending
  // 落了盘，daemon 重启也清不掉），单一发送方反复 @ 会被永久静默压死、owner 永远看不到卡片。
  // 冷却已过的 denied 不再节流，且无任何用途 → 顺手删除，避免「每个被拒用户」永久占位。
  if (!isExpired(e, Date.now())) return e.state;
  map.delete(k);
  return null;
}

/** owner 维度节流：转投 owner 私聊的申请卡，每个 (bot, owner) 滑动窗口内最多发这么多张。
 *  上面的 per (chat, target) 节流只挡「同一个人反复申请」；私聊转投后任何能看到 bot 的人
 *  都能让 owner 私聊收卡，需要再加一层总量上限，避免被大量不同申请人刷屏。 */
const OWNER_DM_WINDOW_MS = 60 * 60 * 1000;
export const OWNER_DM_MAX_PER_WINDOW = 20;
const ownerDmSent = new Map<string, number[]>();

/** 申请占用一个 owner 私聊发卡名额：窗口内未满 → 记账并返回 true；已满 → false（本次不发）。 */
export function tryReserveOwnerDmSlot(larkAppId: string, ownerOpenId: string, now: number = Date.now()): boolean {
  const k = `${larkAppId}:${ownerOpenId}`;
  const recent = (ownerDmSent.get(k) ?? []).filter(ts => now - ts < OWNER_DM_WINDOW_MS);
  if (recent.length >= OWNER_DM_MAX_PER_WINDOW) {
    ownerDmSent.set(k, recent);
    return false;
  }
  recent.push(now);
  ownerDmSent.set(k, recent);
  return true;
}

/** 退还 tryReserveOwnerDmSlot 在 `reservedAt` 记下的名额：发送失败不能占用后续额度，
 *  否则持续故障会烧光窗口额度，恢复后同一 owner 的转投仍被挡到窗口滑过。 */
export function releaseOwnerDmSlot(larkAppId: string, ownerOpenId: string, reservedAt: number): void {
  const k = `${larkAppId}:${ownerOpenId}`;
  const recent = ownerDmSent.get(k);
  if (!recent) return;
  const i = recent.lastIndexOf(reservedAt);
  if (i >= 0) recent.splice(i, 1);
  if (recent.length === 0) ownerDmSent.delete(k);
}

function pruneOwnerDmSent(now: number): void {
  for (const [k, list] of ownerDmSent) {
    const recent = list.filter(ts => now - ts < OWNER_DM_WINDOW_MS);
    if (recent.length === 0) ownerDmSent.delete(k);
    else if (recent.length !== list.length) ownerDmSent.set(k, recent);
  }
}

/** 模拟 daemon 重启：丢掉全部内存状态，磁盘文件保留。 */
export function _simulateRestartForTest(): void { tables.clear(); ownerDmSent.clear(); lastPrunedAt = 0; }
/** 彻底清空：内存 + 当前 dataDir 下的全部落盘文件。 */
export function _resetForTest(): void {
  _simulateRestartForTest();
  let names: string[] = [];
  try { names = readdirSync(config.session.dataDir); } catch { return; }
  for (const name of names) {
    if (!name.startsWith(FILE_PREFIX) || !name.endsWith(FILE_SUFFIX)) continue;
    try { unlinkSync(join(config.session.dataDir, name)); } catch { /* best effort */ }
  }
}
export function _tableSizeForTest(): number {
  let size = 0;
  for (const map of tables.values()) size += map.size;
  return size;
}
export function _filePathForTest(larkAppId: string): string { return filePathFor(larkAppId); }
export function _ownerDmKeyCountForTest(): number { return ownerDmSent.size; }
