'use strict';

const fs = require('fs');
const PROGRAM_START_MS = Date.now();

let inputString = '';
let currentLine = 0;

process.stdin.resume();
process.stdin.setEncoding('utf-8');

process.stdin.on('data', function(inputStdin) {
    inputString += inputStdin;
});

process.stdin.on('end', function() {
    inputString = inputString.split('\n');
    main();
});

function readLine() {
    return inputString[currentLine++];
}

/*
 * Complete the 'solve' function below.
 *
 * The function is expected to return a STRING_ARRAY.
 * The function accepts STRING_ARRAY grid as parameter.
 */
function solve(grid) {
    const HARD_LIMIT_MS = 8300;
    const MAX_RESTARTS = 100000;
    const CHECK_EVERY_NODES = 128;
    const COMPLETE_NODE_LIMIT = 30000;
    const COMPLETE_BUDGET_MS = 600;
    const LNS_BASE_NODES = 500;
    const LNS_MAX_NODES = 4000;

    const N = 1, E = 2, S = 4, W = 8;
    const DIR_BITS = [N, E, S, W];
    const OPP_BITS = [S, W, N, E];
    const DR = [-1, 0, 1, 0];
    const DC = [0, 1, 0, -1];
    const AXIS_STRAIGHT = [2, 1, 2, 1];

    const STATE_MASKS = [0, E | W, N | S, N | E, N | W, S | E, S | W];
    const STATE_CHARS = ['.', '-', '|', 'L', 'J', 'F', '7'];
    const CHAR_TO_MASK = { '.': 0, '-': E | W, '|': N | S, L: N | E, J: N | W, F: S | E, '7': S | W };
    const CHAR_TO_STATE = { '.': 0, '-': 1, '|': 2, L: 3, J: 4, F: 5, '7': 6 };
    const STATES_WITH = [0, 0, 0, 0];
    const STATES_WITHOUT = [0, 0, 0, 0];
    const TURN_WITH_EDGE = [0, 0, 0, 0];

    for (let d = 0; d < 4; d++) {
        let withMask = 0, withoutMask = 0, turnMask = 0;
        for (let s = 0; s < STATE_MASKS.length; s++) {
            if (STATE_MASKS[s] & DIR_BITS[d]) {
                withMask |= 1 << s;
                if (s !== AXIS_STRAIGHT[d]) turnMask |= 1 << s;
            } else {
                withoutMask |= 1 << s;
            }
        }
        STATES_WITH[d] = withMask;
        STATES_WITHOUT[d] = withoutMask;
        TURN_WITH_EDGE[d] = turnMask;
    }

    function elapsedMs() {
        return process.uptime() * 1000;
    }

    function popcount7(x) {
        x = x - ((x >> 1) & 0x55);
        x = (x & 0x33) + ((x >> 2) & 0x33);
        return (x + (x >> 4)) & 0x0f;
    }

    function oneState(mask) {
        for (let i = 0; i < 7; i++) if (mask === (1 << i)) return i;
        return -1;
    }

    function domainStates(mask) {
        const out = [];
        for (let s = 0; s < 7; s++) if (mask & (1 << s)) out.push(s);
        return out;
    }

    function mulberry32(seed) {
        let a = seed >>> 0;
        return function rand() {
            a = (a + 0x6D2B79F5) >>> 0;
            let t = a;
            t = Math.imul(t ^ (t >>> 15), t | 1);
            t ^= t + Math.imul(t ^ (t >>> 7), t | 61);
            return ((t ^ (t >>> 14)) >>> 0) / 4294967296;
        };
    }

    function hashGrid(g) {
        let h = 2166136261 >>> 0;
        for (const row of g) {
            for (let i = 0; i < row.length; i++) {
                h ^= row.charCodeAt(i);
                h = Math.imul(h, 16777619) >>> 0;
            }
        }
        return h >>> 0;
    }

    function loopLength(lines) {
        let n = 0;
        for (const row of lines) {
            for (let i = 0; i < row.length; i++) if (row[i] !== '.') n++;
        }
        return n;
    }

    function fallbackGrid(R, C) {
        if (R < 2 || C < 2) return Array.from({ length: R }, () => '.'.repeat(C));
        const out = Array.from({ length: R }, () => Array(C).fill('.'));
        for (let c = 0; c < C; c++) {
            out[0][c] = c === 0 ? 'F' : (c === C - 1 ? '7' : '-');
            out[R - 1][c] = c === 0 ? 'L' : (c === C - 1 ? 'J' : '-');
        }
        for (let r = 1; r < R - 1; r++) {
            out[r][0] = '|';
            out[r][C - 1] = '|';
        }
        return out.map(row => row.join(''));
    }

    function remember(candidate) {
        if (!candidate) return false;
        const v = validate(grid, candidate);
        if (!v.ok) return false;
        const len = loopLength(candidate);
        if (len < bestLen) {
            const oldLen = bestLen;
            best = candidate;
            bestLen = len;
            const t = elapsedMs();
            if (firstSolutionMs < 0) firstSolutionMs = t;
            lastImproveMs = t;
            if (oldLen < Infinity && (oldLen - len) / oldLen >= 0.03) lastBigImproveMs = t;
            return true;
        }
        return false;
    }

    function tryRectangleLoop(g) {
        const R = g.length;
        const C = g[0].length;
        let minR = R, maxR = -1, minC = C, maxC = -1;
        for (let r = 0; r < R; r++) {
            for (let c = 0; c < C; c++) {
                if (g[r][c] !== 'W' && g[r][c] !== 'B') continue;
                if (r < minR) minR = r;
                if (r > maxR) maxR = r;
                if (c < minC) minC = c;
                if (c > maxC) maxC = c;
            }
        }
        if (maxR < 0) return null;
        minR = Math.max(0, minR - 1);
        maxR = Math.min(R - 1, maxR + 1);
        minC = Math.max(0, minC - 1);
        maxC = Math.min(C - 1, maxC + 1);
        if (maxR - minR < 2 || maxC - minC < 2) {
            minR = 0; maxR = R - 1; minC = 0; maxC = C - 1;
        }
        for (let tries = 0; tries < 2; tries++) {
            const out = Array.from({ length: R }, () => Array(C).fill('.'));
            for (let c = minC; c <= maxC; c++) {
                out[minR][c] = c === minC ? 'F' : (c === maxC ? '7' : '-');
                out[maxR][c] = c === minC ? 'L' : (c === maxC ? 'J' : '-');
            }
            for (let r = minR + 1; r < maxR; r++) {
                out[r][minC] = '|';
                out[r][maxC] = '|';
            }
            const lines = out.map(row => row.join(''));
            if (validate(g, lines).ok) return lines;
            minR = 0; maxR = R - 1; minC = 0; maxC = C - 1;
        }
        return null;
    }

    function validate(g, outLines) {
        const R = g.length;
        const C = g[0] ? g[0].length : 0;
        if (!Array.isArray(outLines) || outLines.length !== R) return { ok: false };
        const used = new Uint8Array(R * C);
        let start = -1, usedCount = 0;

        function idx(r, c) { return r * C + c; }
        function inside(r, c) { return r >= 0 && r < R && c >= 0 && c < C; }

        for (let r = 0; r < R; r++) {
            if (outLines[r].length !== C) return { ok: false };
            for (let c = 0; c < C; c++) {
                const ch = outLines[r][c];
                if (!(ch in CHAR_TO_MASK)) return { ok: false };
                const mask = CHAR_TO_MASK[ch];
                const id = idx(r, c);
                if (mask) {
                    used[id] = 1;
                    start = id;
                    usedCount++;
                }
            }
        }
        if (start < 0) return { ok: false };

        for (let r = 0; r < R; r++) {
            for (let c = 0; c < C; c++) {
                const mask = CHAR_TO_MASK[outLines[r][c]];
                if (!mask) continue;
                let dcnt = 0;
                for (let d = 0; d < 4; d++) {
                    if (!(mask & DIR_BITS[d])) continue;
                    const nr = r + DR[d], nc = c + DC[d];
                    if (!inside(nr, nc)) return { ok: false };
                    const nmask = CHAR_TO_MASK[outLines[nr][nc]];
                    if (!(nmask & OPP_BITS[d])) return { ok: false };
                    dcnt++;
                }
                if (dcnt !== 2) return { ok: false };
            }
        }

        const stack = [start];
        const seen = new Uint8Array(R * C);
        seen[start] = 1;
        let seenCount = 0;
        while (stack.length) {
            const id = stack.pop();
            seenCount++;
            const r = Math.floor(id / C), c = id - r * C;
            const mask = CHAR_TO_MASK[outLines[r][c]];
            for (let d = 0; d < 4; d++) {
                if (!(mask & DIR_BITS[d])) continue;
                const nid = idx(r + DR[d], c + DC[d]);
                if (!seen[nid]) {
                    seen[nid] = 1;
                    stack.push(nid);
                }
            }
        }
        if (seenCount !== usedCount) return { ok: false };

        for (let r = 0; r < R; r++) {
            for (let c = 0; c < C; c++) {
                const p = g[r][c];
                if (p !== 'W' && p !== 'B') continue;
                const mask = CHAR_TO_MASK[outLines[r][c]];
                if (!mask) return { ok: false };
                if (p === 'W') {
                    if (mask !== (E | W) && mask !== (N | S)) return { ok: false };
                    const dirs = mask === (E | W) ? [3, 1] : [0, 2];
                    let hasTurn = false;
                    for (const d of dirs) {
                        const nr = r + DR[d], nc = c + DC[d];
                        if (!inside(nr, nc)) return { ok: false };
                        const nmask = CHAR_TO_MASK[outLines[nr][nc]];
                        const straight = (d === 0 || d === 2) ? (N | S) : (E | W);
                        if (nmask !== straight) hasTurn = true;
                    }
                    if (!hasTurn) return { ok: false };
                } else {
                    if (mask === (E | W) || mask === (N | S)) return { ok: false };
                    for (let d = 0; d < 4; d++) {
                        if (!(mask & DIR_BITS[d])) continue;
                        const nr = r + DR[d], nc = c + DC[d];
                        if (!inside(nr, nc)) return { ok: false };
                        const nmask = CHAR_TO_MASK[outLines[nr][nc]];
                        const straight = (d === 0 || d === 2) ? (N | S) : (E | W);
                        if (nmask !== straight) return { ok: false };
                    }
                }
            }
        }
        return { ok: true };
    }

    class Solver {
        constructor(g, seed, deadlineMs) {
            this.grid = g;
            this.R = g.length;
            this.C = g[0].length;
            this.V = this.R * this.C;
            this.HN = this.R * (this.C - 1);
            this.EN = this.HN + (this.R - 1) * this.C;
            this.deadlineMs = deadlineMs;
            this.rand = mulberry32(seed);
            this.nodes = 0;
            this.nodeLimit = Infinity;
            this.bestBound = Infinity;
            this.answer = null;
            this.timedOut = false;
            this.stopAttempt = false;
            this.queuePops = 0;
            this.lastExhausted = false;

            this.domain = new Uint8Array(this.V);
            this.edges = new Int8Array(this.EN);
            this.edges.fill(-1);
            this.deg = new Uint8Array(this.V);
            this.used = new Uint8Array(this.V);
            this.usedCount = 0;
            this.onEdges = 0;
            this.pearl = new Uint8Array(this.V);
            this.pearlCells = [];
            this.trailType = [];
            this.trailIdx = [];
            this.trailOld = [];
            this.queue = [];
            this.inQueue = new Uint8Array(this.V);
            this.reachSeen = new Int32Array(this.V);
            this.reachStack = new Int32Array(this.V);
            this.reachStamp = 1;
            this.dist = new Int32Array(this.V);
            this.distQueue = new Int32Array(this.V);
            this.nbrTab = new Int32Array(this.V * 4);
            this.eidTab = new Int32Array(this.V * 4);
            this.edgeA = new Int32Array(this.EN);
            this.edgeB = new Int32Array(this.EN);
            this.buildTables();
            this.initDomains();
        }

        buildTables() {
            this.nbrTab.fill(-1);
            this.eidTab.fill(-1);
            for (let r = 0; r < this.R; r++) {
                for (let c = 0; c < this.C; c++) {
                    const i = r * this.C + c;
                    for (let d = 0; d < 4; d++) {
                        const nr = r + DR[d], nc = c + DC[d];
                        const k = i * 4 + d;
                        if (nr < 0 || nr >= this.R || nc < 0 || nc >= this.C) continue;
                        this.nbrTab[k] = nr * this.C + nc;
                        if (d === 1) this.eidTab[k] = r * (this.C - 1) + c;
                        else if (d === 3) this.eidTab[k] = r * (this.C - 1) + c - 1;
                        else if (d === 2) this.eidTab[k] = this.HN + r * this.C + c;
                        else this.eidTab[k] = this.HN + (r - 1) * this.C + c;
                    }
                }
            }
            for (let r = 0; r < this.R; r++) {
                for (let c = 0; c + 1 < this.C; c++) {
                    const eid = r * (this.C - 1) + c;
                    this.edgeA[eid] = r * this.C + c;
                    this.edgeB[eid] = r * this.C + c + 1;
                }
            }
            for (let r = 0; r + 1 < this.R; r++) {
                for (let c = 0; c < this.C; c++) {
                    const eid = this.HN + r * this.C + c;
                    this.edgeA[eid] = r * this.C + c;
                    this.edgeB[eid] = (r + 1) * this.C + c;
                }
            }
        }

        idx(r, c) { return r * this.C + c; }
        inBounds(r, c) { return r >= 0 && r < this.R && c >= 0 && c < this.C; }

        neighbor(i, d) {
            return this.nbrTab[i * 4 + d];
        }

        edgeId(i, d) {
            return this.eidTab[i * 4 + d];
        }

        initDomains() {
            for (let r = 0; r < this.R; r++) {
                for (let c = 0; c < this.C; c++) {
                    const i = this.idx(r, c);
                    const ch = this.grid[r][c];
                    let base = 0;
                    for (let s = 0; s < STATE_MASKS.length; s++) {
                        const sm = STATE_MASKS[s];
                        if ((sm & N) && r === 0) continue;
                        if ((sm & S) && r === this.R - 1) continue;
                        if ((sm & W) && c === 0) continue;
                        if ((sm & E) && c === this.C - 1) continue;
                        base |= 1 << s;
                    }
                    if (ch === 'W') {
                        this.pearl[i] = 1;
                        this.pearlCells.push(i);
                        base = 0;
                        if (c > 0 && c + 1 < this.C) base |= 1 << 1;
                        if (r > 0 && r + 1 < this.R) base |= 1 << 2;
                    } else if (ch === 'B') {
                        this.pearl[i] = 2;
                        this.pearlCells.push(i);
                        base = 0;
                        for (const s of [3, 4, 5, 6]) {
                            const sm = STATE_MASKS[s];
                            let ok = true;
                            for (let d = 0; d < 4; d++) {
                                if (!(sm & DIR_BITS[d])) continue;
                                const r2 = r + 2 * DR[d], c2 = c + 2 * DC[d];
                                if (!this.inBounds(r2, c2)) {
                                    ok = false;
                                    break;
                                }
                            }
                            if (ok) base |= 1 << s;
                        }
                    }
                    this.domain[i] = base;
                }
            }
        }

        mark() { return this.trailType.length; }

        undo(mark) {
            while (this.trailType.length > mark) {
                const type = this.trailType.pop();
                const idx = this.trailIdx.pop();
                const old = this.trailOld.pop();
                if (type === 0) this.edges[idx] = old;
                else if (type === 1) this.domain[idx] = old;
                else if (type === 2) this.deg[idx] = old;
                else if (type === 3) this.used[idx] = old;
                else if (type === 4) this.usedCount = old;
                else if (type === 5) this.onEdges = old;
            }
            while (this.queue.length) this.inQueue[this.queue.pop()] = 0;
        }

        enqueue(i) {
            if (i < 0 || this.inQueue[i]) return;
            this.inQueue[i] = 1;
            this.queue.push(i);
        }

        enqueueAroundCell(i) {
            this.enqueue(i);
            for (let d = 0; d < 4; d++) this.enqueue(this.neighbor(i, d));
        }

        setEdge(eid, val) {
            if (eid < 0) return val === 0;
            const cur = this.edges[eid];
            if (cur === val) return true;
            if (cur !== -1) return false;
            let a = -1, b = -1;
            let closesCycle = false;
            if (val === 1) {
                a = this.edgeA[eid];
                b = this.edgeB[eid];
                if (this.deg[a] >= 2 || this.deg[b] >= 2) return false;
                if (this.deg[a] === 1 && this.deg[b] === 1) {
                    const info = this.pathInfo(a, b);
                    if (info.connected) {
                        if (info.pearls !== this.pearlCells.length || info.len !== this.usedCount) return false;
                        closesCycle = true;
                    }
                }
            }
            this.trailType.push(0);
            this.trailIdx.push(eid);
            this.trailOld.push(cur);
            this.edges[eid] = val;
            if (val === 1) {
                this.setScalar(5, this.onEdges);
                this.onEdges++;
                this.bumpDegree(a);
                this.bumpDegree(b);
                if (!this.used[a]) this.setUsed(a, 1);
                if (!this.used[b]) this.setUsed(b, 1);
                if (this.deg[a] > 2 || this.deg[b] > 2) return false;
            }
            this.enqueueAroundCell(this.edgeA[eid]);
            this.enqueueAroundCell(this.edgeB[eid]);
            if (closesCycle) {
                const lines = this.outputFromEdges();
                if (!validate(this.grid, lines).ok) return false;
                this.answer = lines;
            }
            return true;
        }

        edgeEnds(eid) {
            return [this.edgeA[eid], this.edgeB[eid]];
        }

        setScalar(type, old) {
            this.trailType.push(type);
            this.trailIdx.push(0);
            this.trailOld.push(old);
        }

        bumpDegree(i) {
            this.trailType.push(2);
            this.trailIdx.push(i);
            this.trailOld.push(this.deg[i]);
            this.deg[i]++;
        }

        setUsed(i, val) {
            this.trailType.push(3);
            this.trailIdx.push(i);
            this.trailOld.push(this.used[i]);
            this.used[i] = val;
            this.setScalar(4, this.usedCount);
            this.usedCount += val ? 1 : -1;
        }

        pathInfo(a, b) {
            let prev = -1;
            let cur = a;
            let len = 1;
            let pearls = this.pearl[cur] ? 1 : 0;
            const limit = this.usedCount + 1;
            while (cur !== b) {
                let next = -1;
                for (let d = 0; d < 4; d++) {
                    const eid = this.edgeId(cur, d);
                    if (eid < 0 || this.edges[eid] !== 1) continue;
                    const v = this.neighbor(cur, d);
                    if (v !== prev) {
                        next = v;
                        break;
                    }
                }
                if (next < 0) return { connected: false, len, pearls };
                prev = cur;
                cur = next;
                len++;
                if (this.pearl[cur]) pearls++;
                if (len > limit) return { connected: false, len, pearls };
            }
            return { connected: true, len, pearls };
        }

        restrictDomain(i, newMask) {
            newMask &= this.domain[i];
            if (newMask === 0) return false;
            if (newMask === this.domain[i]) return true;
            this.trailType.push(1);
            this.trailIdx.push(i);
            this.trailOld.push(this.domain[i]);
            this.domain[i] = newMask;
            this.enqueueAroundCell(i);
            return true;
        }

        initialPropagate() {
            for (let i = 0; i < this.V; i++) this.enqueue(i);
            return this.propagate();
        }

        propagate() {
            while (this.queue.length) {
                if (((++this.queuePops) & 1023) === 0 && elapsedMs() > this.deadlineMs) {
                    this.timedOut = true;
                    return false;
                }
                const i = this.queue.pop();
                this.inQueue[i] = 0;
                if (!this.filterCell(i)) return false;
                if (!this.forceFromDomain(i)) return false;
                if (!this.singletonImplications(i)) return false;
            }
            return true;
        }

        filterCell(i) {
            const dom = this.domain[i];
            let next = 0;
            const pearl = this.pearl[i];
            for (let s = 0; s < 7; s++) {
                if (!(dom & (1 << s))) continue;
                const sm = STATE_MASKS[s];
                let ok = true;
                for (let d = 0; d < 4; d++) {
                    const eid = this.edgeId(i, d);
                    const bitOn = (sm & DIR_BITS[d]) !== 0;
                    const est = eid < 0 ? 0 : this.edges[eid];
                    if (est === 1 && !bitOn) { ok = false; break; }
                    if (est === 0 && bitOn) { ok = false; break; }
                    const ni = this.neighbor(i, d);
                    if (ni < 0) {
                        if (bitOn) { ok = false; break; }
                        continue;
                    }
                    const nd = this.domain[ni];
                    const oppDir = (d + 2) & 3;
                    if (bitOn) {
                        if ((nd & STATES_WITH[oppDir]) === 0) { ok = false; break; }
                    } else if ((nd & STATES_WITHOUT[oppDir]) === 0) {
                        ok = false; break;
                    }
                }
                if (!ok) continue;

                if (pearl === 2) {
                    for (let d = 0; d < 4 && ok; d++) {
                        if (!(sm & DIR_BITS[d])) continue;
                        const ni = this.neighbor(i, d);
                        if (ni < 0 || (this.domain[ni] & (1 << AXIS_STRAIGHT[d])) === 0) ok = false;
                    }
                } else if (pearl === 1) {
                    if (s === 1) {
                        const li = this.neighbor(i, 3), ri = this.neighbor(i, 1);
                        ok = li >= 0 && ri >= 0 &&
                            (((this.domain[li] & TURN_WITH_EDGE[1]) !== 0) || ((this.domain[ri] & TURN_WITH_EDGE[3]) !== 0));
                    } else if (s === 2) {
                        const ui = this.neighbor(i, 0), di = this.neighbor(i, 2);
                        ok = ui >= 0 && di >= 0 &&
                            (((this.domain[ui] & TURN_WITH_EDGE[2]) !== 0) || ((this.domain[di] & TURN_WITH_EDGE[0]) !== 0));
                    }
                }
                if (ok) next |= 1 << s;
            }
            return this.restrictDomain(i, next);
        }

        forceFromDomain(i) {
            const dom = this.domain[i];
            for (let d = 0; d < 4; d++) {
                const eid = this.edgeId(i, d);
                if (eid < 0) continue;
                if ((dom & STATES_WITH[d]) === 0) {
                    if (!this.setEdge(eid, 0)) return false;
                } else if ((dom & STATES_WITHOUT[d]) === 0) {
                    if (!this.setEdge(eid, 1)) return false;
                }
            }
            return true;
        }

        singletonImplications(i) {
            const s = oneState(this.domain[i]);
            if (s < 0) return true;
            const sm = STATE_MASKS[s];
            if (this.pearl[i] === 2) {
                for (let d = 0; d < 4; d++) {
                    if (!(sm & DIR_BITS[d])) continue;
                    const ni = this.neighbor(i, d);
                    if (ni < 0) return false;
                    if (!this.restrictDomain(ni, 1 << AXIS_STRAIGHT[d])) return false;
                }
            } else if (this.pearl[i] === 1) {
                if (s === 1) {
                    const li = this.neighbor(i, 3), ri = this.neighbor(i, 1);
                    if (!this.whiteTurnImplication(li, 1, ri, 3)) return false;
                } else if (s === 2) {
                    const ui = this.neighbor(i, 0), di = this.neighbor(i, 2);
                    if (!this.whiteTurnImplication(ui, 2, di, 0)) return false;
                }
            }
            return true;
        }

        whiteTurnImplication(a, aBackDir, b, bBackDir) {
            if (a < 0 || b < 0) return false;
            const aCanTurn = (this.domain[a] & TURN_WITH_EDGE[aBackDir]) !== 0;
            const bCanTurn = (this.domain[b] & TURN_WITH_EDGE[bBackDir]) !== 0;
            if (!aCanTurn && !bCanTurn) return false;
            if (!aCanTurn && !this.restrictDomain(b, TURN_WITH_EDGE[bBackDir])) return false;
            if (!bCanTurn && !this.restrictDomain(a, TURN_WITH_EDGE[aBackDir])) return false;
            return true;
        }

        attempt(seed, nodeLimit, bound, rootMark, deadlineMs) {
            this.rand = mulberry32(seed);
            this.nodeLimit = nodeLimit;
            this.bestBound = bound;
            this.deadlineMs = deadlineMs;
            this.nodes = 0;
            this.queuePops = 0;
            this.answer = null;
            this.timedOut = false;
            this.stopAttempt = false;
            this.lastExhausted = false;
            let thrown = null;
            let result = null;
            try {
                if (this.connectivityCheck()) {
                    this.dfs();
                    result = this.answer;
                }
                this.lastExhausted = !this.answer && !this.stopAttempt && !this.timedOut;
            } catch (e) {
                thrown = e;
            }
            this.undo(rootMark);
            if (thrown) throw thrown;
            return result;
        }

        attemptWindow(seed, nodeLimit, bound, rootMark, deadlineMs, r0, r1, c0, c1, bestState) {
            this.rand = mulberry32(seed);
            this.nodeLimit = nodeLimit;
            this.bestBound = bound;
            this.deadlineMs = deadlineMs;
            this.nodes = 0;
            this.queuePops = 0;
            this.answer = null;
            this.timedOut = false;
            this.stopAttempt = false;
            this.lastExhausted = false;
            let thrown = null;
            let result = null;
            try {
                let ok = true;
                let checked = 0;
                for (let r = 0; r < this.R && ok; r++) {
                    for (let c = 0; c < this.C; c++) {
                        if (r >= r0 && r <= r1 && c >= c0 && c <= c1) continue;
                        const i = r * this.C + c;
                        if (!this.restrictDomain(i, 1 << bestState[i])) {
                            ok = false;
                            break;
                        }
                        if (((++checked) & 255) === 0 && elapsedMs() > this.deadlineMs) {
                            this.timedOut = true;
                            ok = false;
                            break;
                        }
                    }
                }
                if (ok && this.propagate() && this.connectivityCheck()) {
                    this.dfs();
                    result = this.answer;
                }
                this.lastExhausted = !this.answer && !this.stopAttempt && !this.timedOut;
            } catch (e) {
                thrown = e;
            }
            this.undo(rootMark);
            if (thrown) throw thrown;
            return result;
        }

        dfs() {
            if (this.answer) return true;
            this.nodes++;
            if (this.nodes > this.nodeLimit) {
                this.stopAttempt = true;
                return false;
            }
            if ((this.nodes & 15) === 0 && elapsedMs() > this.deadlineMs) {
                this.timedOut = true;
                return false;
            }
            if (!this.connectivityCheck()) return false;
            if ((this.nodes & (CHECK_EVERY_NODES - 1)) === 0) {
                if (!this.componentCheck(false)) return false;
            }

            if (this.usedCount >= this.bestBound) return false;

            const branch = this.chooseBranch();
            if (!branch) return false;

            if (branch.kind === 'state') {
                const vals = this.shuffleStates(branch.states);
                for (const s of vals) {
                    const mark = this.mark();
                    if (this.restrictDomain(branch.cell, 1 << s) && this.propagate() && this.dfs()) {
                        if (this.answer || elapsedMs() > this.deadlineMs || this.bestBound <= this.lowerPearlBound()) {
                            this.undo(mark);
                            return true;
                        }
                    }
                    this.undo(mark);
                    if (this.timedOut || this.stopAttempt) return false;
                }
                return false;
            }

            const edges = this.orderEdges(branch.cell, branch.edges);
            for (const eid of edges) {
                const mark = this.mark();
                if (this.setEdge(eid, 1) && this.propagate() && this.dfs()) {
                    if (this.answer || elapsedMs() > this.deadlineMs || this.bestBound <= this.lowerPearlBound()) {
                        this.undo(mark);
                        return true;
                    }
                }
                this.undo(mark);
                if (this.timedOut || this.stopAttempt) return false;
            }
            return false;
        }

        lowerPearlBound() {
            return Math.max(4, this.pearlCells.length);
        }

        connectivityCheck() {
            if (this.pearlCells.length === 0) return true;
            const start = this.pearlCells[0];
            if (this.domain[start] === 1) return false;
            this.reachStamp++;
            if (this.reachStamp > 2000000000) {
                this.reachSeen.fill(0);
                this.reachStamp = 1;
            }
            const stamp = this.reachStamp;
            let top = 0;
            let pearlsSeen = 0;
            this.reachSeen[start] = stamp;
            this.reachStack[top++] = start;
            while (top > 0) {
                const u = this.reachStack[--top];
                if (this.pearl[u]) pearlsSeen++;
                for (let d = 0; d < 4; d++) {
                    const eid = this.edgeId(u, d);
                    if (eid < 0 || this.edges[eid] === 0) continue;
                    const v = this.neighbor(u, d);
                    if (v < 0 || this.domain[v] === 1 || this.reachSeen[v] === stamp) continue;
                    this.reachSeen[v] = stamp;
                    this.reachStack[top++] = v;
                }
            }
            return pearlsSeen === this.pearlCells.length;
        }

        chooseBranch() {
            let bestCell = -1;
            let bestEdges = null;
            let bestScore = 99;
            let bestTies = 0;
            let randomCell = -1;
            let randomEdges = null;
            let randomTies = 0;

            for (let i = 0; i < this.V; i++) {
                let on = 0;
                let lastOnDir = -1;
                for (let d = 0; d < 4; d++) {
                    const eid = this.edgeId(i, d);
                    if (eid >= 0 && this.edges[eid] === 1) {
                        on++;
                        lastOnDir = d;
                    }
                }
                if (on !== 1) continue;
                const cand = [];
                for (let d = 0; d < 4; d++) {
                    const eid = this.edgeId(i, d);
                    if (eid < 0 || this.edges[eid] !== -1) continue;
                    let possible = false;
                    for (let s = 0; s < 7; s++) {
                        if ((this.domain[i] & (1 << s)) &&
                            (STATE_MASKS[s] & DIR_BITS[lastOnDir]) &&
                            (STATE_MASKS[s] & DIR_BITS[d])) {
                            possible = true;
                            break;
                        }
                    }
                    if (possible) cand.push(eid);
                }
                if (cand.length > 0) {
                    if (cand.length <= 3 && this.rand() < 1 / (++randomTies)) {
                        randomCell = i;
                        randomEdges = cand;
                    }
                    if (cand.length < bestScore) {
                        bestCell = i;
                        bestEdges = cand;
                        bestScore = cand.length;
                        bestTies = 1;
                    } else if (cand.length === bestScore && this.rand() < 1 / (++bestTies)) {
                        bestCell = i;
                        bestEdges = cand;
                    }
                }
            }
            if (randomCell >= 0 && this.rand() < 0.15) return { kind: 'edge', cell: randomCell, edges: randomEdges };
            if (bestCell >= 0) return { kind: 'edge', cell: bestCell, edges: bestEdges };

            let bestDomainCell = -1;
            let bestDomainCount = 99;
            let bestDomainTies = 0;
            for (const i of this.pearlCells) {
                const cnt = popcount7(this.domain[i]);
                if (cnt <= 1) continue;
                if (cnt < bestDomainCount) {
                    bestDomainCell = i;
                    bestDomainCount = cnt;
                    bestDomainTies = 1;
                } else if (cnt === bestDomainCount && this.rand() < 1 / (++bestDomainTies)) {
                    bestDomainCell = i;
                }
            }
            if (bestDomainCell >= 0) return { kind: 'state', cell: bestDomainCell, states: domainStates(this.domain[bestDomainCell]) };

            let bestLooseCell = -1;
            let bestLooseScore = 1e9;
            let bestLooseTies = 0;
            for (let i = 0; i < this.V; i++) {
                const cnt = popcount7(this.domain[i]);
                if (cnt <= 1) continue;
                const forcedBonus = this.touchesForced(i) ? -1000 : 0;
                const score = forcedBonus + cnt * 100;
                if (score < bestLooseScore) {
                    bestLooseScore = score;
                    bestLooseCell = i;
                    bestLooseTies = 1;
                } else if (score === bestLooseScore && this.rand() < 1 / (++bestLooseTies)) {
                    bestLooseCell = i;
                }
            }
            if (bestLooseCell >= 0) return { kind: 'state', cell: bestLooseCell, states: domainStates(this.domain[bestLooseCell]) };
            return null;
        }

        touchesForced(i) {
            for (let d = 0; d < 4; d++) {
                const eid = this.edgeId(i, d);
                if (eid >= 0 && this.edges[eid] === 1) return true;
                const ni = this.neighbor(i, d);
                if (ni >= 0) {
                    for (let nd = 0; nd < 4; nd++) {
                        const ne = this.edgeId(ni, nd);
                        if (ne >= 0 && this.edges[ne] === 1) return true;
                    }
                }
            }
            return false;
        }

        shuffleStates(states) {
            const arr = states.slice();
            arr.sort((a, b) => this.statePreference(a) - this.statePreference(b));
            for (let i = arr.length - 1; i > 0; i--) {
                if (this.rand() < 0.35) {
                    const j = Math.floor(this.rand() * (i + 1));
                    const t = arr[i]; arr[i] = arr[j]; arr[j] = t;
                }
            }
            return arr;
        }

        statePreference(s) {
            if (s === 0) return 4;
            if (s === 1 || s === 2) return 1;
            return 2;
        }

        orderEdges(cell, edges) {
            const arr = edges.slice();
            if (arr.length > 1 && this.rand() < 0.15) {
                for (let i = arr.length - 1; i > 0; i--) {
                    const j = Math.floor(this.rand() * (i + 1));
                    const t = arr[i]; arr[i] = arr[j]; arr[j] = t;
                }
                return arr;
            }
            this.buildDistanceMap(cell);
            arr.sort((a, b) => this.edgeDistanceScore(cell, a) - this.edgeDistanceScore(cell, b));
            return arr;
        }

        edgeDistanceScore(cell, eid) {
            const other = this.otherCell(cell, eid);
            const d = other >= 0 ? this.dist[other] : -1;
            return (d >= 0 ? d : 1000000) + this.rand() * 1.5;
        }

        buildDistanceMap(endpoint) {
            this.dist.fill(-1);
            let head = 0, tail = 0;
            const partner = this.partnerEndpoint(endpoint);
            for (let i = 0; i < this.V; i++) {
                if (this.deg[i] === 1 && i !== endpoint && i !== partner) {
                    this.dist[i] = 0;
                    this.distQueue[tail++] = i;
                }
            }
            for (const p of this.pearlCells) {
                if (this.deg[p] === 0 && this.dist[p] < 0) {
                    this.dist[p] = 0;
                    this.distQueue[tail++] = p;
                }
            }
            if (tail === 0 && partner >= 0) {
                this.dist[partner] = 0;
                this.distQueue[tail++] = partner;
            }
            while (head < tail) {
                const u = this.distQueue[head++];
                const ndist = this.dist[u] + 1;
                for (let d = 0; d < 4; d++) {
                    const eid = this.edgeId(u, d);
                    if (eid < 0 || this.edges[eid] === 0) continue;
                    const v = this.neighbor(u, d);
                    if (v < 0 || this.dist[v] >= 0 || this.deg[v] >= 2 || this.domain[v] === 1) continue;
                    this.dist[v] = ndist;
                    this.distQueue[tail++] = v;
                }
            }
        }

        partnerEndpoint(endpoint) {
            let prev = -1;
            let cur = endpoint;
            let guard = this.usedCount + 1;
            while (guard-- > 0) {
                let next = -1;
                for (let d = 0; d < 4; d++) {
                    const eid = this.edgeId(cur, d);
                    if (eid < 0 || this.edges[eid] !== 1) continue;
                    const v = this.neighbor(cur, d);
                    if (v !== prev) {
                        next = v;
                        break;
                    }
                }
                if (next < 0) return cur;
                prev = cur;
                cur = next;
                if (cur !== endpoint && this.deg[cur] === 1) return cur;
            }
            return -1;
        }

        otherCell(cell, eid) {
            if (this.edgeA[eid] === cell) return this.edgeB[eid];
            if (this.edgeB[eid] === cell) return this.edgeA[eid];
            return -1;
        }

        componentCheck(strict) {
            const deg = new Uint8Array(this.V);
            let onEdges = 0;
            for (let e = 0; e < this.EN; e++) {
                if (this.edges[e] !== 1) continue;
                const a = this.edgeA[e], b = this.edgeB[e];
                onEdges++;
                deg[a]++; deg[b]++;
                if (deg[a] > 2 || deg[b] > 2) return false;
            }
            if (!onEdges) return true;

            const seen = new Uint8Array(this.V);
            const stack = [];
            for (let i = 0; i < this.V; i++) {
                if (deg[i] === 0 || seen[i]) continue;
                let vertices = 0, degreeSum = 0, pearls = 0;
                stack.push(i);
                seen[i] = 1;
                while (stack.length) {
                    const u = stack.pop();
                    vertices++;
                    degreeSum += deg[u];
                    if (this.pearl[u]) pearls++;
                    for (let d = 0; d < 4; d++) {
                        const eid = this.edgeId(u, d);
                        if (eid < 0 || this.edges[eid] !== 1) continue;
                        const v = this.neighbor(u, d);
                        if (v >= 0 && !seen[v]) {
                            seen[v] = 1;
                            stack.push(v);
                        }
                    }
                }
                const compEdges = degreeSum >> 1;
                if (vertices === compEdges) {
                    if (pearls !== this.pearlCells.length || compEdges >= this.bestBound) return false;
                    if (strict) return true;
                }
            }
            return true;
        }

        outputFromEdges() {
            const chars = Array.from({ length: this.R }, () => Array(this.C).fill('.'));
            for (let i = 0; i < this.V; i++) {
                let mask = 0;
                for (let d = 0; d < 4; d++) {
                    const eid = this.edgeId(i, d);
                    if (eid >= 0 && this.edges[eid] === 1) mask |= DIR_BITS[d];
                }
                for (let s = 0; s < STATE_MASKS.length; s++) {
                    if (STATE_MASKS[s] === mask) {
                        const r = Math.floor(i / this.C), c = i - r * this.C;
                        chars[r][c] = STATE_CHARS[s];
                        break;
                    }
                }
            }
            return chars.map(row => row.join(''));
        }
    }

    const R = grid.length;
    const C = grid[0] ? grid[0].length : 0;
    if (!R || !C) return [];

    const hardDeadline = HARD_LIMIT_MS;
    const seedBase = hashGrid(grid);
    let best = null;
    let bestLen = Infinity;
    let firstSolutionMs = -1;
    let lastImproveMs = -1;
    let lastBigImproveMs = -1;
    let pearlCount = 0;
    const pearlIds = new Int32Array(R * C);
    for (const row of grid) {
        for (let i = 0; i < row.length; i++) if (row[i] === 'W' || row[i] === 'B') pearlCount++;
    }
    let pearlAt = 0;
    for (let r = 0; r < R; r++) {
        for (let c = 0; c < C; c++) {
            if (grid[r][c] === 'W' || grid[r][c] === 'B') pearlIds[pearlAt++] = r * C + c;
        }
    }
    const globalDeadline = () => hardDeadline;
    const lowerBound = () => Math.max(4, pearlCount);

    function luby(i) {
        let k = 1;
        while ((1 << k) - 1 < i) k++;
        if (i === (1 << k) - 1) return 1 << (k - 1);
        return luby(i - (1 << (k - 1)) + 1);
    }

    function softCap() {
        const base = R * C < 400 ? 1300 : (R * C < 1200 ? 2500 : 4000);
        if (lastBigImproveMs >= 0 && elapsedMs() - lastBigImproveMs <= 500) return 5200;
        return base;
    }

    function improvementWindowOpen() {
        if (firstSolutionMs < 0 || lastImproveMs < 0) return false;
        const stagMs = Math.max(350, 0.4 * (elapsedMs() - firstSolutionMs));
        return elapsedMs() - lastImproveMs <= stagMs && elapsedMs() < softCap() && elapsedMs() < hardDeadline - 70;
    }

    function fullRestartWindowOpen() {
        if (!best) return elapsedMs() < hardDeadline - 70;
        if (bestLen <= lowerBound()) return false;
        const t = elapsedMs();
        if (t >= hardDeadline - 70 || t >= softCap()) return false;
        if (firstSolutionMs >= 0 && t - firstSolutionMs < 900) return true;
        return improvementWindowOpen();
    }

    function buildBestState(out, state, loopCells) {
        let count = 0;
        for (let r = 0; r < R; r++) {
            const row = out[r];
            for (let c = 0; c < C; c++) {
                const i = r * C + c;
                const s = CHAR_TO_STATE[row[c]];
                state[i] = s;
                if (s !== 0) loopCells[count++] = i;
            }
        }
        return count;
    }

    try {
        remember(tryRectangleLoop(grid));
    } catch (e) {
    }

    let solver = null;
    let rootMark = 0;
    let rootReady = false;
    try {
        solver = new Solver(grid, seedBase, globalDeadline());
        if (solver.initialPropagate() && solver.connectivityCheck()) {
            rootMark = solver.mark();
            rootReady = true;
        }
    } catch (e) {
        rootReady = false;
    }

    let optimal = bestLen <= lowerBound();
    if (rootReady) {
        const nodeUnit = 300;
        for (let restart = 1; restart <= MAX_RESTARTS && fullRestartWindowOpen(); restart++) {
            const gd = best ? Math.min(hardDeadline, softCap()) : globalDeadline();
            const nodeLimit = nodeUnit * luby(restart);
            let candidate = null;
            try {
                candidate = solver.attempt(seedBase ^ Math.imul(0x9E3779B1, restart), nodeLimit, bestLen, rootMark, gd);
                remember(candidate);
            } catch (e) {
                try {
                    solver.undo(rootMark);
                } catch (ignored) {
                }
            }
            if (bestLen <= lowerBound()) {
                optimal = true;
                break;
            }
            if (solver.lastExhausted) {
                if (best) optimal = true;
                break;
            }
        }
    }

    optimal = optimal || bestLen <= lowerBound();
    if (rootReady && best && !optimal && improvementWindowOpen()) {
        for (let rounds = 0; rounds < 8 && elapsedMs() < hardDeadline - 70; rounds++) {
            const before = bestLen;
            let candidate = null;
            try {
                candidate = solver.attempt(seedBase ^ Math.imul(0xC2B2AE35, rounds + 1),
                    COMPLETE_NODE_LIMIT, bestLen, rootMark, Math.min(hardDeadline, elapsedMs() + COMPLETE_BUDGET_MS));
                remember(candidate);
            } catch (e) {
                try {
                    solver.undo(rootMark);
                } catch (ignored) {
                }
            }
            if (solver.lastExhausted || bestLen <= lowerBound()) {
                optimal = true;
                break;
            }
            if (bestLen >= before) break;
        }
    }

    if (rootReady && best && !optimal) {
        const bestState = new Uint8Array(R * C);
        const loopCells = new Int32Array(R * C);
        let loopCount = buildBestState(best, bestState, loopCells);
        let rand = mulberry32(seedBase ^ 0xD1B54A32);
        let wMax = 10;
        let stale = 0;
        let truncStale = 0;
        let windowNodes = LNS_BASE_NODES;
        let windows = 0;
        while (loopCount > 0 && improvementWindowOpen() && windows < 100000) {
            windows++;
            let center;
            if (pearlCount > 0 && rand() < 0.5) center = pearlIds[Math.floor(rand() * pearlCount)];
            else center = loopCells[Math.floor(rand() * loopCount)];
            const cr = Math.floor(center / C), cc = center - cr * C;
            const h = Math.min(R, 6 + Math.floor(rand() * Math.max(1, wMax - 5)));
            const w = Math.min(C, 6 + Math.floor(rand() * Math.max(1, wMax - 5)));
            let r0 = cr - Math.floor(h / 2), c0 = cc - Math.floor(w / 2);
            if (r0 < 0) r0 = 0;
            if (c0 < 0) c0 = 0;
            let r1 = r0 + h - 1, c1 = c0 + w - 1;
            if (r1 >= R) { r1 = R - 1; r0 = Math.max(0, r1 - h + 1); }
            if (c1 >= C) { c1 = C - 1; c0 = Math.max(0, c1 - w + 1); }

            let hasLoop = false;
            for (let r = r0; r <= r1 && !hasLoop; r++) {
                for (let c = c0; c <= c1; c++) {
                    if (bestState[r * C + c] !== 0) {
                        hasLoop = true;
                        break;
                    }
                }
            }
            if (!hasLoop) continue;

            const before = bestLen;
            try {
                const candidate = solver.attemptWindow(seedBase ^ Math.imul(0x85EBCA6B, windows),
                    windowNodes, bestLen, rootMark, hardDeadline, r0, r1, c0, c1, bestState);
                remember(candidate);
            } catch (e) {
                try {
                    solver.undo(rootMark);
                } catch (ignored) {
                }
            }
            if (bestLen < before) {
                loopCount = buildBestState(best, bestState, loopCells);
                wMax = 10;
                stale = 0;
                truncStale = 0;
                windowNodes = LNS_BASE_NODES;
                if (bestLen <= lowerBound()) {
                    optimal = true;
                    break;
                }
            } else {
                stale++;
                if (solver.timedOut || solver.stopAttempt) truncStale++;
                if (stale >= 15) {
                    wMax = Math.min(24, wMax + 2);
                    stale = 0;
                }
                if (truncStale >= 8) {
                    windowNodes = Math.min(LNS_MAX_NODES, windowNodes * 2);
                    truncStale = 0;
                }
            }
        }
    }

    if (best) {
        try {
            if (validate(grid, best).ok) return best;
        } catch (e) {
            return best;
        }
    }

    return fallbackGrid(R, C);
}

function main() {
    const rows = inputString.map(s => String(s).trim()).filter(Boolean);
    const gridCount = parseInt(rows[0], 10);
    let grid = rows.slice(1, 1 + gridCount);
    let result;
    try {
        result = solve(grid);
    } catch (e) {
        const width = grid[0] ? grid[0].length : 0;
        result = Array.from({ length: isFinite(gridCount) ? gridCount : 0 }, () => '.'.repeat(width));
    }

    fs.writeFileSync(process.env.OUTPUT_PATH, result.join('\n') + '\n');
}

