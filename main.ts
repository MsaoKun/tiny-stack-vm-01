// Independent implementation of make.fun's tiny stack ISA v1.
// Reads /input/<id>/{program.bin,input.bin}; writes /output/<id>/{stdout.bin,exit.txt}.
import { mkdirSync, readdirSync, readFileSync, writeFileSync } from 'node:fs';
import { join } from 'node:path';

const STEP_LIMIT = 1000000, OUTPUT_MAX = 65536, STACK_MAX = 256, CALLS_MAX = 64, MEM_WORDS = 256;

// Per-opcode metadata: immediate byte count, pop count, push count.
const imm = new Uint8Array(256), pops = new Uint8Array(256), pushes = new Uint8Array(256), known = new Uint8Array(256);
function def(b, i, p, q) { known[b] = 1; imm[b] = i; pops[b] = p; pushes[b] = q; }
def(0x00, 0, 0, 0); def(0x01, 1, 0, 1); def(0x02, 4, 0, 1); def(0x03, 0, 1, 0);
def(0x04, 0, 1, 2); def(0x05, 0, 2, 2); def(0x06, 0, 2, 3); def(0x07, 0, 3, 3);
def(0x10, 0, 2, 1); def(0x11, 0, 2, 1); def(0x12, 0, 2, 1); def(0x13, 0, 2, 1);
def(0x14, 0, 2, 1); def(0x15, 0, 2, 1); def(0x16, 0, 2, 1); def(0x17, 0, 1, 1);
def(0x18, 0, 2, 1); def(0x19, 0, 2, 1); def(0x1a, 0, 2, 1); def(0x1b, 0, 1, 1);
def(0x1c, 0, 2, 1); def(0x1d, 0, 2, 1); def(0x1e, 0, 2, 1);
def(0x20, 0, 2, 1); def(0x21, 0, 2, 1); def(0x22, 0, 2, 1);
def(0x30, 2, 0, 0); def(0x31, 2, 1, 0); def(0x32, 2, 1, 0);
def(0x33, 2, 0, 0); def(0x34, 0, 0, 0);
def(0x40, 0, 1, 1); def(0x41, 0, 2, 0);
def(0x50, 0, 1, 0); def(0x51, 0, 1, 0); def(0x52, 0, 0, 1); def(0x53, 0, 1, 0);

function vm(p, input) {
  const n = p.length;
  const D = new Int32Array(STACK_MAX);
  const C = new Int32Array(CALLS_MAX);
  const M = new Int32Array(MEM_WORDS);
  const out = new Uint8Array(OUTPUT_MAX);
  let sp = 0, csp = 0, olen = 0, ip = 0, pc = 0, steps = 0;
  const finish = (exit) => ({ out: out.slice(0, olen), exit });
  const trap = (code) => finish(code);

  for (;;) {
    if (steps >= STEP_LIMIT) return trap(10);       // step limit
    if (pc < 0 || pc >= n) return trap(9);          // pc outside program
    const b = p[pc];
    if (!known[b]) return trap(5);                  // unknown opcode
    const k = imm[b];
    if (pc + k >= n) return trap(9);                // immediate cut off
    steps++;
    const next = pc + 1 + k;
    if (sp < pops[b]) return trap(2);                // underflow
    if (sp - pops[b] + pushes[b] > STACK_MAX) return trap(3); // overflow
    pc = next;
    switch (b) {
      case 0x00: return finish(0);                  // HALT
      case 0x01: D[sp++] = (p[next - 1] << 24) >> 24; break;           // PUSH8 sign-extended
      case 0x02: D[sp++] = p[next-4] | (p[next-3] << 8) | (p[next-2] << 16) | (p[next-1] << 24); break; // PUSH32
      case 0x03: sp--; break;                       // POP
      case 0x04: D[sp] = D[sp-1]; sp++; break;      // DUP
      case 0x05: { const t = D[sp-1]; D[sp-1] = D[sp-2]; D[sp-2] = t; break; } // SWAP
      case 0x06: D[sp] = D[sp-2]; sp++; break;      // OVER
      case 0x07: { const t = D[sp-3]; D[sp-3] = D[sp-2]; D[sp-2] = D[sp-1]; D[sp-1] = t; break; } // ROT
      case 0x17: D[sp-1] = -D[sp-1] | 0; break;     // NEG
      case 0x1b: D[sp-1] = ~D[sp-1]; break;         // NOT
      case 0x10: case 0x11: case 0x12: case 0x13: case 0x14: case 0x15: case 0x16:
      case 0x18: case 0x19: case 0x1a: case 0x1c: case 0x1d: case 0x1e:
      case 0x20: case 0x21: case 0x22: {
        const a = D[sp-2], c = D[sp-1];
        let r = 0;
        switch (b) {
          case 0x10: r = (a + c) | 0; break;                                  // ADD
          case 0x11: r = (a - c) | 0; break;                                  // SUB
          case 0x12: r = Math.imul(a, c); break;                              // MUL (low 32 bits)
          case 0x13: if (c === 0) return trap(4); r = (a === -2147483648 && c === -1) ? a : (a / c) | 0; break; // DIV
          case 0x14: if (c === 0) return trap(4); r = c === -1 ? 0 : (a % c) | 0; break; // MOD
          case 0x15: if (c === 0) return trap(4); r = Math.floor((a >>> 0) / (c >>> 0)) | 0; break; // DIVU
          case 0x16: if (c === 0) return trap(4); r = ((a >>> 0) % (c >>> 0)) | 0; break; // MODU
          case 0x18: r = a & c; break;                                        // AND
          case 0x19: r = a | c; break;                                        // OR
          case 0x1a: r = a ^ c; break;                                        // XOR
          case 0x1c: r = a << (c & 31); break;                                // SHL
          case 0x1d: r = a >> (c & 31); break;                                // SHR (arithmetic)
          case 0x1e: r = (a >>> (c & 31)) | 0; break;                         // SHRU (logical)
          case 0x20: r = a === c ? 1 : 0; break;                              // EQ
          case 0x21: r = a < c ? 1 : 0; break;                                // LT (signed)
          case 0x22: r = (a >>> 0) < (c >>> 0) ? 1 : 0; break;                // LTU (unsigned)
        }
        sp -= 2; D[sp++] = r; break;
      }
      case 0x30: case 0x31: case 0x32: {             // JMP / JZ / JNZ
        const rel = ((p[next-2] | (p[next-1] << 8)) << 16) >> 16;
        let take = true;
        if (b !== 0x30) { const v = D[--sp]; take = b === 0x31 ? v === 0 : v !== 0; }
        if (take) pc = next + rel;
        break;
      }
      case 0x33:                                    // CALL
        if (csp === CALLS_MAX) return trap(7);
        C[csp++] = next; pc = p[next-2] | (p[next-1] << 8); break;
      case 0x34:                                    // RET
        if (csp === 0) return trap(8);
        pc = C[--csp]; break;
      case 0x40: {                                  // LOAD
        const addr = D[sp-1];
        if (addr < 0 || addr >= MEM_WORDS) return trap(6);
        D[sp-1] = M[addr]; break;
      }
      case 0x41: {                                  // STORE
        const addr = D[sp-1], v = D[sp-2];
        if (addr < 0 || addr >= MEM_WORDS) return trap(6);
        sp -= 2; M[addr] = v; break;
      }
      case 0x50: {                                  // PRINT
        const s = '' + D[sp-1];
        if (olen + s.length > OUTPUT_MAX) return trap(11);
        sp--;
        for (let i = 0; i < s.length; i++) out[olen++] = s.charCodeAt(i);
        break;
      }
      case 0x51:                                    // PUTC
        if (olen + 1 > OUTPUT_MAX) return trap(11);
        out[olen++] = D[--sp] & 255; break;
      case 0x52: D[sp++] = ip < input.length ? input[ip++] : -1; break; // IN
      case 0x53: return finish(D[--sp] & 255);      // EXIT
    }
  }
}

const I = process.env.MAKEFUN_INPUT_DIR ?? '/input';
const O = process.env.MAKEFUN_OUTPUT_DIR ?? '/output';
for (const id of readdirSync(I).sort()) {
  const r = vm(new Uint8Array(readFileSync(join(I, id, 'program.bin'))),
               new Uint8Array(readFileSync(join(I, id, 'input.bin'))));
  mkdirSync(join(O, id), { recursive: true });
  writeFileSync(join(O, id, 'stdout.bin'), Buffer.from(r.out));
  writeFileSync(join(O, id, 'exit.txt'), `${r.exit}\n`);
}
