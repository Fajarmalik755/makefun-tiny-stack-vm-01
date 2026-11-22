// Tiny stack VM: a faithful interpreter of make.fun's tiny stack ISA v1 (ISA.md).
// Node 22, stdlib only, fully deterministic: one run answers every instance in
// MAKEFUN_INPUT_DIR and writes stdout.bin + exit.txt per instance to MAKEFUN_OUTPUT_DIR.
import { mkdirSync, readdirSync, readFileSync, writeFileSync } from 'node:fs';
import { join } from 'node:path';

const I = process.env.MAKEFUN_INPUT_DIR ?? '/input';
const O = process.env.MAKEFUN_OUTPUT_DIR ?? '/output';

// Opcode tables, indexed by opcode byte: immediate length, pops, pushes, valid.
// Entries are [opcode, immediate bytes, pops, pushes].
const IM = new Uint8Array(256), PO = new Uint8Array(256), PU = new Uint8Array(256), OK = new Uint8Array(256);
for (const [o, im, po, pu] of [
  [0, 0, 0, 0], [1, 1, 0, 1], [2, 4, 0, 1], [3, 0, 1, 0], [4, 0, 1, 2],
  [5, 0, 2, 2], [6, 0, 2, 3], [7, 0, 3, 3],
  [48, 2, 0, 0], [49, 2, 1, 0], [50, 2, 1, 0], [51, 2, 0, 0], [52, 0, 0, 0],
  [64, 0, 1, 1], [65, 0, 2, 0], [80, 0, 1, 0], [81, 0, 1, 0], [82, 0, 0, 1], [83, 0, 1, 0],
]) { IM[o] = im; PO[o] = po; PU[o] = pu; OK[o] = 1; }
// Binary ops 0x10..0x22 all pop 2, push 1, no immediate; NEG (0x17) and NOT (0x1b) pop 1.
for (let o = 16; o <= 34; o++) { PO[o] = 2; PU[o] = 1; OK[o] = 1; }
PO[23] = 1; PO[27] = 1;

// Runs one program on its input. Returns [output bytes, output length, exit code].
function run(p, inp) {
  const n = p.length;
  const D = new Int32Array(256);
  let sp = 0;
  const C = new Int32Array(64);
  let cp = 0;
  const M = new Int32Array(256);
  const out = new Uint8Array(65536);
  let ol = 0, ip = 0, pc = 0, st = 0;
  for (;;) {
    if (st === 1000000) return [out, ol, 10];
    if (pc < 0 || pc >= n) return [out, ol, 9];
    const op = p[pc];
    if (!OK[op]) return [out, ol, 5];
    const im = IM[op];
    if (pc + im >= n) return [out, ol, 9];
    st++;
    const nx = pc + 1 + im;
    const po = PO[op], pu = PU[op];
    if (sp < po) return [out, ol, 2];
    if (sp - po + pu > 256) return [out, ol, 3];
    pc = nx;
    switch (op) {
      case 0: return [out, ol, 0];
      case 1: D[sp++] = (p[nx - 1] << 24) >> 24; break;
      case 2: D[sp++] = p[nx - 4] | (p[nx - 3] << 8) | (p[nx - 2] << 16) | (p[nx - 1] << 24); break;
      case 3: sp--; break;
      case 4: D[sp] = D[sp - 1]; sp++; break;
      case 5: { const t = D[sp - 1]; D[sp - 1] = D[sp - 2]; D[sp - 2] = t; break; }
      case 6: D[sp] = D[sp - 2]; sp++; break;
      case 7: { const a = D[sp - 3]; D[sp - 3] = D[sp - 2]; D[sp - 2] = D[sp - 1]; D[sp - 1] = a; break; }
      case 16: case 17: case 18: case 19: case 20: case 21: case 22:
      case 24: case 25: case 26: case 28: case 29: case 30: case 32: case 33: case 34: {
        const b = D[sp - 1], a = D[sp - 2];
        let r;
        if (op === 16) r = (a + b) | 0;
        else if (op === 17) r = (a - b) | 0;
        else if (op === 18) r = Math.imul(a, b);
        else if (op === 19) {
          if (b === 0) return [out, ol, 4];
          r = a === -2147483648 && b === -1 ? a : (a / b) | 0;
        } else if (op === 20) {
          if (b === 0) return [out, ol, 4];
          r = b === -1 ? 0 : (a % b) | 0;
        } else if (op === 21) {
          if (b === 0) return [out, ol, 4];
          r = Math.floor((a >>> 0) / (b >>> 0)) | 0;
        } else if (op === 22) {
          if (b === 0) return [out, ol, 4];
          r = ((a >>> 0) % (b >>> 0)) | 0;
        } else if (op === 24) r = a & b;
        else if (op === 25) r = a | b;
        else if (op === 26) r = a ^ b;
        else if (op === 28) r = a << (b & 31);
        else if (op === 29) r = a >> (b & 31);
        else if (op === 30) r = (a >>> (b & 31)) | 0;
        else if (op === 32) r = a === b ? 1 : 0;
        else if (op === 33) r = a < b ? 1 : 0;
        else r = (a >>> 0) < (b >>> 0) ? 1 : 0;
        sp -= 2;
        D[sp++] = r;
        break;
      }
      case 23: D[sp - 1] = -D[sp - 1] | 0; break;
      case 27: D[sp - 1] = ~D[sp - 1]; break;
      case 48: pc = nx + (((p[nx - 2] | (p[nx - 1] << 8)) << 16) >> 16); break;
      case 49: { const v = D[--sp]; if (v === 0) pc = nx + (((p[nx - 2] | (p[nx - 1] << 8)) << 16) >> 16); break; }
      case 50: { const v = D[--sp]; if (v !== 0) pc = nx + (((p[nx - 2] | (p[nx - 1] << 8)) << 16) >> 16); break; }
      case 51: if (cp === 64) return [out, ol, 7]; C[cp++] = nx; pc = p[nx - 2] | (p[nx - 1] << 8); break;
      case 52: if (cp === 0) return [out, ol, 8]; pc = C[--cp]; break;
      case 64: { const a = D[sp - 1]; if (a < 0 || a > 255) return [out, ol, 6]; D[sp - 1] = M[a]; break; }
      case 65: { const a = D[sp - 1], v = D[sp - 2]; if (a < 0 || a > 255) return [out, ol, 6]; sp -= 2; M[a] = v; break; }
      case 80: { // PRINT: decimal ASCII, limit checked before writing anything.
        let x = D[sp - 1], neg = 0;
        if (x < 0) { neg = 1; x = -x; }
        let t = x, len = 0;
        do { len++; t = (t / 10) | 0; } while (t);
        if (ol + len + neg > 65536) return [out, ol, 11];
        sp--;
        if (neg) out[ol++] = 45;
        let w = ol + len;
        t = x;
        do { out[--w] = 48 + (t % 10); t = (t / 10) | 0; } while (t);
        ol += len;
        break;
      }
      case 81: if (ol + 1 > 65536) return [out, ol, 11]; out[ol++] = D[--sp] & 255; break;
      case 82: D[sp++] = ip < inp.length ? inp[ip++] : -1; break;
      case 83: return [out, ol, D[--sp] & 255];
    }
  }
}

for (const id of readdirSync(I).sort()) {
  const [out, ol, code] = run(
    new Uint8Array(readFileSync(join(I, id, 'program.bin'))),
    new Uint8Array(readFileSync(join(I, id, 'input.bin'))),
  );
  mkdirSync(join(O, id), { recursive: true });
  writeFileSync(join(O, id, 'stdout.bin'), out.subarray(0, ol));
  writeFileSync(join(O, id, 'exit.txt'), code + '\n');
}
