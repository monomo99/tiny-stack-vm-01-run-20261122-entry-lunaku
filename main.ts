// Exact interpreter for make.fun's tiny stack ISA v1 (kit ISA.md; the
// kit's reference vm.mjs rules where the text is ambiguous). One run
// answers every <input>/<id>/ by writing <output>/<id>/stdout.bin and
// exit.txt. Deterministic: no clock, env, network, or outside files.
import { mkdirSync, readdirSync, readFileSync, statSync, writeFileSync } from 'node:fs';
import { join } from 'node:path';

// Opcode tables by byte: IMM = immediate length, POP = values popped
// (-1 = not an opcode), PSH = values pushed.
const IMM = new Int8Array(256), POP = new Int8Array(256).fill(-1), PSH = new Int8Array(256);
const def = (op, imm, pops, pushes) => { IMM[op] = imm; POP[op] = pops; PSH[op] = pushes; };
def(0, 0, 0, 0); def(1, 1, 0, 1); def(2, 4, 0, 1); def(3, 0, 1, 0);
def(4, 0, 1, 2); def(5, 0, 2, 2); def(6, 0, 2, 3); def(7, 0, 3, 3);
for (const op of [16, 17, 18, 19, 20, 21, 22, 24, 25, 26, 28, 29, 30, 32, 33, 34]) def(op, 0, 2, 1);
def(23, 0, 1, 1); def(27, 0, 1, 1); // NEG, NOT
def(48, 2, 0, 0); def(49, 2, 1, 0); def(50, 2, 1, 0); // JMP, JZ, JNZ
def(51, 2, 0, 0); def(52, 0, 0, 0); // CALL, RET
def(64, 0, 1, 1); def(65, 0, 2, 0); // LOAD, STORE
def(80, 0, 1, 0); def(81, 0, 1, 0); def(82, 0, 0, 1); def(83, 0, 1, 0); // PRINT, PUTC, IN, EXIT

// Run one program on its input. Returns [exit code, bytes written].
function exec(prog, input) {
  const n = prog.length, st = new Int32Array(256), cs = new Int32Array(64), mem = new Int32Array(256);
  const out = new Uint8Array(65536);
  let sp = 0, cp = 0, olen = 0, ip = 0, pc = 0, steps = 0;
  const fin = (code) => [code, out.subarray(0, olen)];
  for (;;) {
    if (steps === 1000000) return fin(10); // step limit
    if (pc < 0 || pc >= n) return fin(9); // pc outside the program
    const op = prog[pc], pops = POP[op];
    if (pops < 0) return fin(5); // unknown opcode
    const imm = IMM[op];
    if (pc + imm >= n) return fin(9); // immediate cut off by the end
    steps++;
    if (sp < pops) return fin(2); // stack underflow
    if (sp - pops + PSH[op] > 256) return fin(3); // stack overflow
    const nx = pc + 1 + imm; // address of the next instruction
    pc = nx;
    switch (op) {
      case 0: return fin(0); // HALT
      case 1: st[sp++] = (prog[nx - 1] << 24) >> 24; break; // PUSH8, sign-extended
      case 2: st[sp++] = prog[nx - 4] | (prog[nx - 3] << 8) | (prog[nx - 2] << 16) | (prog[nx - 1] << 24); break; // PUSH32
      case 3: sp--; break; // POP
      case 4: st[sp] = st[sp - 1]; sp++; break; // DUP
      case 5: { const t = st[sp - 1]; st[sp - 1] = st[sp - 2]; st[sp - 2] = t; break; } // SWAP
      case 6: st[sp] = st[sp - 2]; sp++; break; // OVER
      case 7: { const a = st[sp - 3]; st[sp - 3] = st[sp - 2]; st[sp - 2] = st[sp - 1]; st[sp - 1] = a; break; } // ROT
      case 23: st[sp - 1] = (-st[sp - 1]) | 0; break; // NEG, wraps
      case 27: st[sp - 1] = ~st[sp - 1]; break; // NOT
      case 16: case 17: case 18: case 19: case 20: case 21: case 22:
      case 24: case 25: case 26: case 28: case 29: case 30:
      case 32: case 33: case 34: { // two-operand ops: b is the top, a below it
        const b = st[sp - 1], a = st[sp - 2];
        let r;
        if (op === 16) r = (a + b) | 0; // ADD, wraps
        else if (op === 17) r = (a - b) | 0; // SUB, wraps
        else if (op === 18) r = Math.imul(a, b); // MUL, low 32 bits of the exact product
        else if (op === 19) { // DIV, signed, truncated toward zero
          if (b === 0) return fin(4);
          r = a === -2147483648 && b === -1 ? a : (a / b) | 0;
        } else if (op === 20) { // MOD, signed remainder, sign of a
          if (b === 0) return fin(4);
          r = b === -1 ? 0 : (a % b) | 0;
        } else if (op === 21) { // DIVU, unsigned quotient read back signed
          if (b === 0) return fin(4);
          r = Math.floor((a >>> 0) / (b >>> 0)) | 0;
        } else if (op === 22) { // MODU, unsigned remainder read back signed
          if (b === 0) return fin(4);
          r = ((a >>> 0) % (b >>> 0)) | 0;
        } else if (op === 24) r = a & b; // AND
        else if (op === 25) r = a | b; // OR
        else if (op === 26) r = a ^ b; // XOR
        else if (op === 28) r = a << (b & 31); // SHL, only the low 5 bits count
        else if (op === 29) r = a >> (b & 31); // SHR, arithmetic
        else if (op === 30) r = (a >>> (b & 31)) | 0; // SHRU, logical
        else if (op === 32) r = a === b ? 1 : 0; // EQ
        else if (op === 33) r = a < b ? 1 : 0; // LT, signed
        else r = (a >>> 0) < (b >>> 0) ? 1 : 0; // LTU, unsigned
        sp -= 2;
        st[sp++] = r;
        break;
      }
      case 48: case 49: case 50: { // JMP / JZ / JNZ: signed 16-bit offset from nx
        const rel = ((prog[nx - 2] | (prog[nx - 1] << 8)) << 16) >> 16;
        if (op === 48) pc = nx + rel;
        else { const v = st[--sp]; if ((op === 49) === (v === 0)) pc = nx + rel; }
        break;
      }
      case 51: // CALL: unsigned 16-bit target, push nx as the return address
        if (cp === 64) return fin(7);
        cs[cp++] = nx;
        pc = prog[nx - 2] | (prog[nx - 1] << 8);
        break;
      case 52: // RET
        if (cp === 0) return fin(8);
        pc = cs[--cp];
        break;
      case 64: { // LOAD
        const addr = st[sp - 1];
        if (addr < 0 || addr >= 256) return fin(6);
        st[sp - 1] = mem[addr];
        break;
      }
      case 65: { // STORE ( v addr -- )
        const addr = st[sp - 1], v = st[sp - 2];
        if (addr < 0 || addr >= 256) return fin(6);
        sp -= 2;
        mem[addr] = v;
        break;
      }
      case 80: { // PRINT: decimal ASCII, '-' when negative
        const s = String(st[sp - 1]);
        if (olen + s.length > 65536) return fin(11);
        sp--;
        for (let i = 0; i < s.length; i++) out[olen++] = s.charCodeAt(i);
        break;
      }
      case 81: // PUTC: one byte, v AND 255
        if (olen + 1 > 65536) return fin(11);
        out[olen++] = st[--sp] & 255;
        break;
      case 82: // IN: next input byte, -1 once the input is used up
        st[sp++] = ip < input.length ? input[ip++] : -1;
        break;
      case 83: // EXIT: exit with the low byte of v
        return fin(st[--sp] & 255);
      default: return fin(5); // unreachable: POP[op] < 0 already trapped above
    }
  }
}

// Driver: answer every instance directory in the input dir, sorted. One
// instance's failure must never take the other 39 down with it.
const IN_DIR = process.env.MAKEFUN_INPUT_DIR ?? '/input';
const OUT_DIR = process.env.MAKEFUN_OUTPUT_DIR ?? '/output';
for (const id of readdirSync(IN_DIR).sort()) {
  const dir = join(IN_DIR, id);
  if (!statSync(dir).isDirectory()) continue;
  let code = 1, bytes = new Uint8Array(0);
  try {
    const [c, b] = exec(readFileSync(join(dir, 'program.bin')), readFileSync(join(dir, 'input.bin')));
    code = c; bytes = b;
  } catch { code = 1; bytes = new Uint8Array(0); }
  mkdirSync(join(OUT_DIR, id), { recursive: true });
  writeFileSync(join(OUT_DIR, id, 'stdout.bin'), bytes);
  writeFileSync(join(OUT_DIR, id, 'exit.txt'), code + '\n');
}
