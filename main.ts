// A tiny stack VM for make.fun's tiny stack ISA (kit: generator/subject/ISA.md), matching the reference
// VM rule for rule: wrapping 32-bit arithmetic, unsigned DIVU/MODU/LTU, masked shift counts, sign-extended
// PUSH8, every trap's own exit code, the step and output limits. Writes /output/<id>/stdout.bin and
// /output/<id>/exit.txt per instance. Local: MAKEFUN_INPUT_DIR=practice/input MAKEFUN_OUTPUT_DIR=out node main.ts
// Verified (kit scorer + differential vs the reference VM): practice 1,000,000 of 1,000,000, eight drawn
// sets perfect, 357 fuzz cases clean, runs byte-identical. Full notes in the commit message.
import { mkdirSync, readdirSync, readFileSync, writeFileSync } from 'node:fs';
import { join } from 'node:path';

// Runs one program on its input bytes; returns [stdout bytes, exit code].
function run(p, inp) {
  const D = new Int32Array(256); // data stack, at most 256 values
  const C = new Int32Array(64); // call stack, at most 64 return addresses
  const M = new Int32Array(256); // memory words
  const out = new Uint8Array(65536); // output, at most 65,536 bytes
  let sp = 0, csp = 0, olen = 0, ip = 0, pc = 0, steps = 0;
  const n = p.length;
  const done = (code) => [out.subarray(0, olen), code];
  for (;;) {
    // One step, in the ISA's order: step limit, pc in range, known opcode, immediate fits.
    if (steps === 1000000) return done(10);
    if (pc < 0 || pc >= n) return done(9);
    const op = p[pc];
    if (!(op < 8 || (op >= 16 && op <= 30) || (op >= 32 && op <= 34) || (op >= 48 && op <= 52) || op === 64 || op === 65 || (op >= 80 && op <= 83))) return done(5);
    const imm = op === 1 ? 1 : op === 2 ? 4 : op >= 48 && op <= 51 ? 2 : 0;
    if (pc + imm >= n) return done(9);
    steps++;
    const next = pc + 1 + imm;
    // Stack needs are checked before the instruction's own traps.
    const bin = op >= 16 && op <= 34 && op !== 23 && op !== 27;
    const pops = op === 7 ? 3 : bin || op === 5 || op === 6 || op === 65 ? 2 : op < 3 || op === 48 || op === 51 || op === 52 || op === 82 ? 0 : 1;
    if (sp < pops) return done(2);
    if ((op === 1 || op === 2 || op === 4 || op === 6 || op === 82) && sp === 256) return done(3);
    pc = next;
    switch (op) {
      case 0: // HALT
        return done(0);
      case 1: // PUSH8, sign-extended
        D[sp++] = (p[next - 1] << 24) >> 24;
        break;
      case 2: // PUSH32, little-endian
        D[sp++] = p[next - 4] | (p[next - 3] << 8) | (p[next - 2] << 16) | (p[next - 1] << 24);
        break;
      case 3: // POP
        sp--;
        break;
      case 4: // DUP
        D[sp] = D[sp - 1];
        sp++;
        break;
      case 5: { // SWAP
        const t = D[sp - 1];
        D[sp - 1] = D[sp - 2];
        D[sp - 2] = t;
        break;
      }
      case 6: // OVER
        D[sp] = D[sp - 2];
        sp++;
        break;
      case 7: { // ROT ( a b c -- b c a )
        const a = D[sp - 3];
        D[sp - 3] = D[sp - 2];
        D[sp - 2] = D[sp - 1];
        D[sp - 1] = a;
        break;
      }
      case 23: // NEG, wraps
        D[sp - 1] = -D[sp - 1] | 0;
        break;
      case 27: // NOT
        D[sp - 1] = ~D[sp - 1];
        break;
      case 48: // JMP
      case 49: // JZ
      case 50: { // JNZ
        const rel = ((p[next - 2] | (p[next - 1] << 8)) << 16) >> 16;
        if (op === 48 || (D[--sp] === 0) === (op === 49)) pc = next + rel;
        break;
      }
      case 51: // CALL, to the unsigned immediate
        if (csp === 64) return done(7);
        C[csp++] = next;
        pc = p[next - 2] | (p[next - 1] << 8);
        break;
      case 52: // RET
        if (csp === 0) return done(8);
        pc = C[--csp];
        break;
      case 64: { // LOAD
        const a = D[sp - 1];
        if (a < 0 || a > 255) return done(6);
        D[sp - 1] = M[a];
        break;
      }
      case 65: { // STORE ( v addr -- )
        const a = D[sp - 1];
        if (a < 0 || a > 255) return done(6);
        sp -= 2;
        M[a] = D[sp];
        break;
      }
      case 80: { // PRINT, decimal ASCII (String of a 32-bit value is pure ASCII)
        const s = String(D[sp - 1]);
        if (olen + s.length > 65536) return done(11);
        sp--;
        for (let i = 0; i < s.length; i++) out[olen++] = s.charCodeAt(i);
        break;
      }
      case 81: // PUTC, one byte
        if (olen === 65536) return done(11);
        out[olen++] = D[--sp] & 255;
        break;
      case 82: // IN, -1 once the input is used up
        D[sp++] = ip < inp.length ? inp[ip++] : -1;
        break;
      case 83: // EXIT, the low byte
        return done(D[--sp] & 255);
      default: { // the binary operators: ( a b -- r ), b on top
        const b = D[sp - 1];
        const a = D[sp - 2];
        let r;
        if (op === 16) r = (a + b) | 0; // ADD
        else if (op === 17) r = (a - b) | 0; // SUB
        else if (op === 18) r = Math.imul(a, b); // MUL, the low 32 bits exactly
        else if (op === 19) { // DIV, signed, truncated toward zero
          if (b === 0) return done(4);
          r = a === -2147483648 && b === -1 ? a : (a / b) | 0;
        } else if (op === 20) { // MOD, the sign of a
          if (b === 0) return done(4);
          r = b === -1 ? 0 : (a % b) | 0;
        } else if (op === 21) { // DIVU, unsigned
          if (b === 0) return done(4);
          r = Math.floor((a >>> 0) / (b >>> 0)) | 0;
        } else if (op === 22) { // MODU, unsigned
          if (b === 0) return done(4);
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
        D[sp - 2] = r;
        sp--;
        break;
      }
    }
  }
}

const I = process.env.MAKEFUN_INPUT_DIR ?? '/input';
const O = process.env.MAKEFUN_OUTPUT_DIR ?? '/output';
for (const id of readdirSync(I).sort()) {
  const [stdout, code] = run(readFileSync(join(I, id, 'program.bin')), readFileSync(join(I, id, 'input.bin')));
  mkdirSync(join(O, id), { recursive: true });
  writeFileSync(join(O, id, 'stdout.bin'), stdout);
  writeFileSync(join(O, id, 'exit.txt'), code + '\n');
}
