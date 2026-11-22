// Tiny stack VM, make.fun tiny-stack ISA v1.
// /input/<id>/program.bin+input.bin -> /output/<id>/stdout.bin+exit.txt.
// Deterministic; semantics per ISA.md + vm.mjs.
import { mkdirSync, readdirSync, readFileSync, writeFileSync } from 'node:fs';
import { join } from 'node:path';

// Per-opcode facts as digit strings in OPS order: A=pops, B=pushes, C=imm bytes.
const OPS = [0, 1, 2, 3, 4, 5, 6, 7, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 32, 33, 34, 48, 49, 50, 51, 52, 64, 65, 80, 81, 82, 83];
const A = '0001122322222221222122222201100121101';
const B = '0110223311111111111111111100000100010';
const C = '0140000000000000000000000022220000000';
const POPS = new Uint8Array(256), PUSH = new Uint8Array(256), IMM = new Uint8Array(256);
for (let i = 0; i < OPS.length; i++) {
  const o = OPS[i];
  POPS[o] = A.charCodeAt(i) - 48; PUSH[o] = B.charCodeAt(i) - 48; IMM[o] = C.charCodeAt(i) - 48;
}

function run(p: Uint8Array, inp: Uint8Array): [number, Uint8Array, number] {
  const n = p.length;
  const st = new Int32Array(256);
  const cs = new Int32Array(64);
  const mem = new Int32Array(256);
  const out = new Uint8Array(65536);
  const dig = new Uint8Array(11);
  let sp = 0, cp = 0, pc = 0, steps = 0, olen = 0, ip = 0;
  for (;;) {
    if (steps === 1000000) return [10, out, olen];
    if (pc < 0 || pc >= n) return [9, out, olen];
    const op = p[pc];
    const im = IMM[op];
    if (pc + im >= n) return [9, out, olen];
    steps++;
    const nx = pc + 1 + im;
    if (sp < POPS[op]) return [2, out, olen];
    if (sp - POPS[op] + PUSH[op] > 256) return [3, out, olen];
    pc = nx;
    switch (op) {
      case 0x00: return [0, out, olen];
      case 0x01: st[sp++] = (p[nx - 1] << 24) >> 24; break;
      case 0x02: st[sp++] = p[nx - 4] | (p[nx - 3] << 8) | (p[nx - 2] << 16) | (p[nx - 1] << 24); break;
      case 0x03: sp--; break;
      case 0x04: st[sp] = st[sp - 1]; sp++; break;
      case 0x05: { const t = st[sp - 1]; st[sp - 1] = st[sp - 2]; st[sp - 2] = t; break; }
      case 0x06: st[sp] = st[sp - 2]; sp++; break;
      case 0x07: { const a = st[sp - 3]; st[sp - 3] = st[sp - 2]; st[sp - 2] = st[sp - 1]; st[sp - 1] = a; break; }
      case 0x17: st[sp - 1] = (-st[sp - 1]) | 0; break;
      case 0x1b: st[sp - 1] = ~st[sp - 1]; break;
      case 0x10: case 0x11: case 0x12: case 0x13: case 0x14: case 0x15:
      case 0x16: case 0x18: case 0x19: case 0x1a: case 0x1c: case 0x1d:
      case 0x1e: case 0x20: case 0x21: case 0x22: {
        const b = st[sp - 1], a = st[sp - 2];
        let r: number;
        switch (op) {
          case 0x10: r = (a + b) | 0; break;
          case 0x11: r = (a - b) | 0; break;
          case 0x12: r = Math.imul(a, b); break;
          case 0x13:
            if (b === 0) return [4, out, olen];
            r = a === -2147483648 && b === -1 ? a : (a / b) | 0; break;
          case 0x14:
            if (b === 0) return [4, out, olen];
            r = b === -1 ? 0 : (a % b) | 0; break;
          case 0x15:
            if (b === 0) return [4, out, olen];
            r = Math.floor((a >>> 0) / (b >>> 0)) | 0; break;
          case 0x16:
            if (b === 0) return [4, out, olen];
            r = ((a >>> 0) % (b >>> 0)) | 0; break;
          case 0x18: r = a & b; break;
          case 0x19: r = a | b; break;
          case 0x1a: r = a ^ b; break;
          case 0x1c: r = a << (b & 31); break;
          case 0x1d: r = a >> (b & 31); break;
          case 0x1e: r = (a >>> (b & 31)) | 0; break;
          case 0x20: r = a === b ? 1 : 0; break;
          case 0x21: r = a < b ? 1 : 0; break;
          default: r = (a >>> 0) < (b >>> 0) ? 1 : 0;
        }
        sp -= 2; st[sp++] = r; break;
      }
      case 0x30: case 0x31: case 0x32: {
        const rel = ((p[nx - 2] | (p[nx - 1] << 8)) << 16) >> 16;
        let take = true;
        if (op !== 0x30) { const v = st[--sp]; take = op === 0x31 ? v === 0 : v !== 0; }
        if (take) pc = nx + rel;
        break;
      }
      case 0x33:
        if (cp === 64) return [7, out, olen];
        cs[cp++] = nx; pc = p[nx - 2] | (p[nx - 1] << 8); break;
      case 0x34:
        if (cp === 0) return [8, out, olen];
        pc = cs[--cp]; break;
      case 0x40: { const a = st[sp - 1]; if (a < 0 || a > 255) return [6, out, olen]; st[sp - 1] = mem[a]; break; }
      case 0x41: { const a = st[sp - 1], v = st[sp - 2]; if (a < 0 || a > 255) return [6, out, olen]; sp -= 2; mem[a] = v; break; }
      case 0x50: {
        const v = st[sp - 1], neg = v < 0;
        let mag = neg ? -v : v, d = 0;
        do { dig[d++] = 48 + (mag % 10); mag = (mag / 10) | 0; } while (mag > 0);
        const len = d + (neg ? 1 : 0);
        if (olen + len > 65536) return [11, out, olen];
        sp--;
        if (neg) out[olen++] = 45;
        while (d > 0) out[olen++] = dig[--d];
        break;
      }
      case 0x51:
        if (olen + 1 > 65536) return [11, out, olen];
        out[olen++] = st[--sp] & 255; break;
      case 0x52: st[sp++] = ip < inp.length ? inp[ip++] : -1; break;
      case 0x53: return [st[--sp] & 255, out, olen];
      default: return [5, out, olen];
    }
  }
}

const IN = process.env.MAKEFUN_INPUT_DIR ?? '/input';
const OUT = process.env.MAKEFUN_OUTPUT_DIR ?? '/output';
for (const id of readdirSync(IN).sort()) {
  const [code, out, olen] = run(
    new Uint8Array(readFileSync(join(IN, id, 'program.bin'))),
    new Uint8Array(readFileSync(join(IN, id, 'input.bin'))),
  );
  mkdirSync(join(OUT, id), { recursive: true });
  writeFileSync(join(OUT, id, 'stdout.bin'), out.subarray(0, olen));
  writeFileSync(join(OUT, id, 'exit.txt'), `${code}\n`);
}
