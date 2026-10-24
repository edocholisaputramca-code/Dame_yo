#!/usr/bin/env python3
"""End-to-end ghost-chain solver for the provided x86-64 ELF.

Needs: Python 3, z3-solver, pycryptodome, GNU binutils (as/objcopy).
The recovered EVM opcode log can instead be supplied with --log.
"""
from __future__ import annotations

import argparse
import ctypes
import hashlib
import mmap
import platform
import struct
import subprocess
import tempfile
from pathlib import Path

try:
    import z3
    from Crypto.Cipher import ChaCha20_Poly1305
    from Crypto.Hash import SHA256
    from Crypto.Protocol.KDF import HKDF
except ImportError as exc:
    raise SystemExit(
        "Missing dependency. Install with: pip install z3-solver pycryptodome"
    ) from exc

ROOT = Path(__file__).resolve().parent
TARGET = bytes.fromhex(
    "b404b899fae88de12751ea68f7cb27b4d42f9787ebda92705e253ccf7ffa6222"
)
FLAG_TEXT = "ION{dame_dame_yo_decode_my_bytecode}"
# The flag text is transcribed from the decrypted PNG watermark; the script
# performs the EVM solve and authenticated decryption, but not OCR.

# Hook assembled into the extracted stage0 code at its opcode-dispatch boundary.
HOOK_ASM = r"""
.text
.globl stub_start
stub_start:
    push %rax
    push %rbx
    push %rcx
    push %rdx
    push %rsi
    push %rdi
    push %r8
    push %r9
    push %r10
    push %r11
    lea 0x50(%rsp), %r10
    movabs $0x2222222222222222, %rdi
    mov 0x300(%rdi), %eax
    mov %eax, %ecx
    lea (%rcx,%rcx,2), %ecx
    shl $6, %ecx
    lea 0x304(%rdi,%rcx), %rdi
    mov %eax, 0(%rdi)
    # Current instruction packet at saved rsi + saved rax - 8
    mov 40(%rsp), %r10
    mov 72(%rsp), %ecx
    lea -8(%r10,%rcx), %r10
    mov 0(%r10), %edx
    mov %edx, 4(%rdi)
    mov 4(%r10), %edx
    mov %edx, 8(%rdi)
    # Decoded bytes/operands from saved GP registers
    mov 32(%rsp), %edx
    mov %edx, 12(%rdi)
    mov 48(%rsp), %edx
    mov %edx, 16(%rdi)
    mov 24(%rsp), %edx
    mov %edx, 20(%rdi)
    mov 16(%rsp), %edx
    mov %edx, 24(%rdi)
    mov 72(%rsp), %edx
    mov %edx, 28(%rdi)
    # 8 VM registers at rsp+a0..bc
    lea 0x50(%rsp), %r10
    mov 0xa0(%r10), %edx
    mov %edx, 32(%rdi)
    mov 0xa4(%r10), %edx
    mov %edx, 36(%rdi)
    mov 0xa8(%r10), %edx
    mov %edx, 40(%rdi)
    mov 0xac(%r10), %edx
    mov %edx, 44(%rdi)
    mov 0xb0(%r10), %edx
    mov %edx, 48(%rdi)
    mov 0xb4(%r10), %edx
    mov %edx, 52(%rdi)
    mov 0xb8(%r10), %edx
    mov %edx, 56(%rdi)
    mov 0xbc(%r10), %edx
    mov %edx, 60(%rdi)
    # 16 VM memory words at rsp+c0..fc
    mov 0xc0(%r10), %edx
    mov %edx, 64(%rdi)
    mov 0xc4(%r10), %edx
    mov %edx, 68(%rdi)
    mov 0xc8(%r10), %edx
    mov %edx, 72(%rdi)
    mov 0xcc(%r10), %edx
    mov %edx, 76(%rdi)
    mov 0xd0(%r10), %edx
    mov %edx, 80(%rdi)
    mov 0xd4(%r10), %edx
    mov %edx, 84(%rdi)
    mov 0xd8(%r10), %edx
    mov %edx, 88(%rdi)
    mov 0xdc(%r10), %edx
    mov %edx, 92(%rdi)
    mov 0xe0(%r10), %edx
    mov %edx, 96(%rdi)
    mov 0xe4(%r10), %edx
    mov %edx, 100(%rdi)
    mov 0xe8(%r10), %edx
    mov %edx, 104(%rdi)
    mov 0xec(%r10), %edx
    mov %edx, 108(%rdi)
    mov 0xf0(%r10), %edx
    mov %edx, 112(%rdi)
    mov 0xf4(%r10), %edx
    mov %edx, 116(%rdi)
    mov 0xf8(%r10), %edx
    mov %edx, 120(%rdi)
    mov 0xfc(%r10), %edx
    mov %edx, 124(%rdi)
    # Selected local source values and VM controls
    mov 0x10(%r10), %edx
    mov %edx, 128(%rdi)
    mov 0x30(%r10), %edx
    mov %edx, 132(%rdi)
    mov 0x40(%r10), %edx
    mov %edx, 136(%rdi)
    mov 0x44(%r10), %edx
    mov %edx, 140(%rdi)
    mov 0x48(%r10), %edx
    mov %edx, 144(%rdi)
    mov %ebp, %edx
    mov %edx, 148(%rdi)
    mov 8(%rsp), %edx
    mov %edx, 152(%rdi)
    mov 0(%rsp), %edx
    mov %edx, 156(%rdi)
    mov %r14d, %edx
    mov %edx, 160(%rdi)
    mov %r15d, %edx
    mov %edx, 164(%rdi)
    mov 40(%rsp), %edx
    mov %edx, 168(%rdi)
    mov 72(%rsp), %edx
    mov %edx, 172(%rdi)
    movabs $0x2222222222222222, %rdi
    addl $1, 0x300(%rdi)
    pop %r11
    pop %r10
    pop %r9
    pop %r8
    pop %rdi
    pop %rsi
    pop %rdx
    pop %rcx
    pop %rbx
    pop %rax
    mov %edi, %ecx
    cmp $0x90, %dl
    .byte 0xe9, 0, 0, 0, 0
.globl stub_end
stub_end:
"""


def lz_unpack(src: bytes, out_len: int) -> bytes:
    out = bytearray()
    i = 0
    while i < len(src):
        control = src[i]
        i += 1
        if control < 0x80:
            n = control + 1
            if i + n > len(src) or len(out) + n > out_len:
                raise ValueError("bad DYP1 literal")
            out.extend(src[i:i + n])
            i += n
        else:
            if i + 2 > len(src):
                raise ValueError("truncated DYP1 back-reference")
            distance = int.from_bytes(src[i:i + 2], "little")
            i += 2
            n = (control & 0x7f) + 3
            if not distance or distance > len(out) or len(out) + n > out_len:
                raise ValueError("bad DYP1 back-reference")
            for _ in range(n):
                out.append(out[-distance])
    if len(out) != out_len:
        raise ValueError(f"DYP1 length mismatch: {len(out)} != {out_len}")
    return bytes(out)


def decode_dyp1(binary: bytes) -> tuple[bytes, int]:
    marker = b"DYP1\x01\x00P\x00"
    at = binary.find(marker)
    if at < 0 or binary.find(marker, at + 1) >= 0:
        raise ValueError("expected exactly one DYP1 v1 pack")
    pack = binary[at:]
    enc_len, plain_len = struct.unpack_from("<II", pack, 8)
    key, expected = pack[16:48], pack[48:80]
    enc = pack[80:80 + enc_len]
    if len(enc) != enc_len:
        raise ValueError("truncated DYP1 pack")
    dec = bytearray(enc_len)
    for pos in range(0, enc_len, 32):
        ctr = (pos // 32).to_bytes(3, "little")
        ks = hashlib.sha256(b"DAMEYO-PACK-v1\0" + key + ctr + b"\0").digest()
        block = enc[pos:pos + 32]
        dec[pos:pos + len(block)] = bytes(a ^ b for a, b in zip(block, ks))
    payload = lz_unpack(bytes(dec), plain_len)
    actual = hashlib.sha256(payload).digest()
    if actual != expected:
        raise ValueError("DYP1 SHA-256 check failed")
    return payload, at


def parse_dyc1(payload: bytes) -> tuple[bytes, bytes, bytes, bytes]:
    if payload[:4] != b"DYC1" or struct.unpack_from("<H", payload, 4)[0] != 1:
        raise ValueError("DYC1 header/version mismatch")
    if struct.unpack_from("<I", payload, 8)[0] != len(payload):
        raise ValueError("DYC1 declared length mismatch")
    if struct.unpack_from("<I", payload, 0x0c)[0] != 0x6c:
        raise ValueError("unexpected DYC1 header size")
    stage0_len = struct.unpack_from("<I", payload, 0x10)[0]
    evm_off = struct.unpack_from("<I", payload, 0x18)[0]
    evm_len = struct.unpack_from("<I", payload, 0x1c)[0]
    env_off = struct.unpack_from("<I", payload, 0x20)[0]
    env_len = struct.unpack_from("<I", payload, 0x24)[0]
    stage0 = payload[0x6c:0x6c + stage0_len]
    evm = payload[evm_off:evm_off + evm_len]
    env = payload[env_off:env_off + env_len]
    digest = payload[0x30:0x50]
    if len(stage0) != stage0_len or len(evm) != evm_len or len(env) != env_len:
        raise ValueError("DYC1 section is truncated")
    return stage0, evm, digest, env


def assemble_hook() -> bytes:
    with tempfile.TemporaryDirectory(prefix="ghost_chain_hook_") as td:
        td = Path(td)
        asm, obj, binary = td / "hook.s", td / "hook.o", td / "hook.bin"
        asm.write_text(HOOK_ASM)
        subprocess.run(["as", "--64", "-o", str(obj), str(asm)], check=True)
        subprocess.run(
            ["objcopy", "-O", "binary", "--only-section=.text", str(obj), str(binary)],
            check=True,
        )
        return binary.read_bytes()


def native_run(stage0: bytes, evm: bytes, token: bytes, hook: bytes) -> tuple[int, bytes, bytes]:
    if platform.machine().lower() not in ("x86_64", "amd64"):
        raise RuntimeError("native stage0 instrumentation requires x86-64 Linux")
    if len(token) != 32:
        raise ValueError("ticket must be 32 bytes")
    mark = bytes.fromhex("2222222222222222")
    stub = bytearray(hook)
    pos, start = [], 0
    while True:
        i = stub.find(mark, start)
        if i < 0:
            break
        pos.append(i)
        start = i + 1
    if len(pos) != 2:
        raise RuntimeError("hook pointer markers not found exactly twice")

    mem = mmap.mmap(
        -1, len(stage0) + len(stub) + 4096,
        flags=mmap.MAP_PRIVATE | mmap.MAP_ANONYMOUS,
        prot=mmap.PROT_READ | mmap.PROT_WRITE | mmap.PROT_EXEC,
    )
    mem.write(stage0)
    base = ctypes.addressof(ctypes.c_char.from_buffer(mem))
    dbg = (ctypes.c_ubyte * 0x50000)()
    db = ctypes.addressof(dbg)
    for i in pos:
        struct.pack_into("<Q", stub, i, db)
    j = stub.rfind(b"\xe9\x00\x00\x00\x00")
    if j < 0:
        raise RuntimeError("hook return jump not found")
    struct.pack_into("<i", stub, j + 1, (base + 0x82d) - (base + len(stage0) + j + 5))
    mem.seek(len(stage0))
    mem.write(stub)
    mem.seek(0x828)
    mem.write(b"\xe9" + struct.pack("<i", (base + len(stage0)) - (base + 0x828 + 5)))

    fn = ctypes.CFUNCTYPE(
        ctypes.c_int, ctypes.c_void_p, ctypes.c_void_p, ctypes.c_size_t, ctypes.c_void_p
    )(base)
    token_buf = ctypes.create_string_buffer(token)
    evm_buf = ctypes.create_string_buffer(evm)
    ctx = (ctypes.c_ubyte * 0x4000)()
    rc = fn(
        ctypes.addressof(token_buf), ctypes.addressof(evm_buf), len(evm), ctypes.addressof(ctx)
    )
    log = bytes(dbg)
    context = bytes(ctx)
    return rc, log, context


def load_program(log: bytes) -> list[dict]:
    n = struct.unpack_from("<I", log, 0x300)[0]
    if n <= 0 or n > (len(log) - 0x304) // 192:
        raise ValueError(f"bad captured instruction count: {n}")
    program = []
    for i in range(n):
        v = struct.unpack_from("<48I", log, 0x304 + i * 192)
        program.append({
            "op": v[4] & 0xff,
            "dst": v[3] & 0xff,
            "src1": v[5] & 0xff,
            "src2": v[6] & 0xff,
            "imm": v[2],
            "sources": (v[32], v[33], v[35], v[37]),
        })
    return program


def solve_token(program: list[dict]) -> tuple[bytes, bool]:
    mask = 0xffffffff
    xs = [z3.BitVec(f"ticket_{i}", 32) for i in range(8)]
    regs = [z3.BitVecVal(0, 32) for _ in range(8)]
    mem = xs + [z3.BitVecVal(0, 32) for _ in range(8)]
    solver = z3.SolverFor("QF_BV")
    solver.set("timeout", 600000)
    for i, ins in enumerate(program):
        op, d, a, b, imm = (ins[k] for k in ("op", "dst", "src1", "src2", "imm"))
        if op == 0x76:
            if imm > 3:
                raise ValueError(f"bad source selector at instruction {i}")
            regs[d] = z3.BitVecVal(ins["sources"][imm] & mask, 32)
        elif op == 0x89:
            regs[d] = z3.BitVecVal(imm & mask, 32)
        elif op in (0x8f, 0x81):
            ix = z3.simplify(regs[a])
            if not z3.is_bv_value(ix):
                raise ValueError(f"nonconstant memory index at instruction {i}")
            j = ix.as_long()
            if j >= 16:
                raise ValueError(f"memory index out of range at instruction {i}")
            if op == 0x8f:
                regs[d] = mem[j]
            else:
                mem[j] = regs[d]
        elif op == 0x90:
            sh = z3.simplify(regs[b])
            if not z3.is_bv_value(sh):
                raise ValueError(f"nonconstant rotate at instruction {i}")
            regs[d] = z3.RotateLeft(regs[a], sh.as_long() & 31)
        elif op == 0x0d:
            regs[d] = regs[a] ^ regs[b]
        elif op == 0x13:
            regs[d] = regs[a] * regs[b]
        elif op == 0xf6:
            regs[d] = regs[a] + regs[b]
        elif op == 0xae:
            regs[d] = regs[a]
        elif op in (0x75, 0xbf, 0x34):
            pass
        else:
            raise ValueError(f"unknown opcode 0x{op:02x} at instruction {i}")

    expected = struct.unpack("<8I", TARGET)
    for out, word in zip(mem[:8], expected):
        solver.add(out == z3.BitVecVal(word, 32))
    result = solver.check()
    if result != z3.sat:
        raise RuntimeError(f"Z3 result: {result}; {solver.reason_unknown() if result == z3.unknown else ''}")
    model = solver.model()
    words = [model.eval(x, model_completion=True).as_long() for x in xs]
    token = struct.pack("<8I", *words)
    solver.add(z3.Or(*[x != z3.BitVecVal(w, 32) for x, w in zip(xs, words)]))
    unique = solver.check() == z3.unsat
    return token, unique


def emulate(token: bytes, program: list[dict]) -> tuple[bytes, list[int]]:
    regs = [0] * 8
    mem = list(struct.unpack("<8I", token)) + [0] * 8
    trace: list[int] = []
    for i, ins in enumerate(program):
        op, d, a, b, imm = (ins[k] for k in ("op", "dst", "src1", "src2", "imm"))
        if op == 0x76:
            regs[d] = ins["sources"][imm] & 0xffffffff
        elif op == 0x89:
            regs[d] = imm & 0xffffffff
        elif op == 0x8f:
            regs[d] = mem[regs[a]]
        elif op == 0x81:
            mem[regs[a]] = regs[d]
        elif op == 0x90:
            sh = regs[b] & 31
            x = regs[a]
            regs[d] = ((x << sh) | (x >> ((32 - sh) & 31))) & 0xffffffff
        elif op == 0x0d:
            regs[d] = regs[a] ^ regs[b]
        elif op == 0x13:
            regs[d] = (regs[a] * regs[b]) & 0xffffffff
        elif op == 0xf6:
            regs[d] = (regs[a] + regs[b]) & 0xffffffff
        elif op == 0xae:
            regs[d] = regs[a]
        elif op == 0xbf:
            trace.append(regs[d])
        elif op in (0x75, 0x34):
            pass
        else:
            raise ValueError(f"unknown opcode 0x{op:02x} at instruction {i}")
    return struct.pack("<8I", *mem[:8]), trace


def main() -> None:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--elf", type=Path, default=ROOT / "extracted/dist/dame_yo")
    ap.add_argument("--log", type=Path, help="reuse a previously captured 327680-byte opcode log")
    ap.add_argument("--out", type=Path, default=ROOT / "decrypted_asset.png")
    ap.add_argument("--ticket-out", type=Path, default=ROOT / "ticket.bin")
    ap.add_argument("--log-out", type=Path, default=ROOT / "evm_instruction_log.generated.bin")
    args = ap.parse_args()

    binary = args.elf.read_bytes()
    payload, pack_off = decode_dyp1(binary)
    stage0, evm, dyc_digest, envelope = parse_dyc1(payload)
    print(f"DYP1 at {pack_off:#x}; decoded {len(payload)} bytes; SHA-256 verified")
    print(f"DYC1 digest: {dyc_digest.hex()}")

    if args.log:
        log = args.log.read_bytes()
    else:
        hook = assemble_hook()
        rc, log, _ = native_run(stage0, evm, bytes(32), hook)
        if rc != 0:
            raise RuntimeError(f"native stage0 zero-input run failed: {rc}")
        args.log_out.write_bytes(log)
    program = load_program(log)
    token, unique = solve_token(program)
    emu_out, trace = emulate(token, program)
    if emu_out != TARGET:
        raise RuntimeError("Z3 token failed emulator target check")

    if not args.log:
        rc, _, native_ctx = native_run(stage0, evm, token, hook)
        if rc != 0 or native_ctx[16:48] != TARGET:
            raise RuntimeError("Z3 token failed native stage0 check")
        trace_native = native_ctx[0x30:0x30 + len(trace) * 4]
        trace_model = b"".join(struct.pack("<I", x) for x in trace)
        if trace_native != trace_model:
            raise RuntimeError("native trace does not match emulator trace")

    trace_bytes = b"".join(struct.pack("<I", x) for x in trace)
    trace_digest = hashlib.sha256(
        b"DAMEYO-TRACE-v1\0" + (12).to_bytes(4, "little") + trace_bytes
    ).digest()
    key = HKDF(
        master=token + trace_digest,
        key_len=32,
        salt=dyc_digest,
        hashmod=SHA256,
        context=b"DAMEYO-PNG-v1\0",
    )

    if envelope[:4] != b"DYAE":
        raise ValueError("DYAE1 envelope magic mismatch")
    payload_len = int.from_bytes(envelope[0x28:0x30], "little")
    nonce, tag, ciphertext = envelope[0x30:0x3c], envelope[0x3c:0x4c], envelope[0x4c:]
    if payload_len != len(ciphertext):
        raise ValueError("DYAE1 ciphertext length mismatch")
    aad = b"DAMEYO-ASSET-v1\0" + payload_len.to_bytes(8, "little")
    cipher = ChaCha20_Poly1305.new(key=key, nonce=nonce)
    cipher.update(aad)
    png = cipher.decrypt_and_verify(ciphertext, tag)
    if not png.startswith(b"\x89PNG\r\n\x1a\n"):
        raise ValueError("decrypted plaintext is not a PNG")

    args.out.write_bytes(png)
    args.ticket_out.write_bytes(token)
    print(f"EVM instructions: {len(program)}; trace words: {len(trace)}")
    print(f"Ticket: {token.hex()}")
    print(f"Unique under model: {unique}")
    print(f"Trace digest: {trace_digest.hex()}")
    print(f"HKDF key: {key.hex()}")
    print(f"Authenticated ChaCha20-Poly1305 decryption: OK ({len(png)} bytes)")
    print(f"Wrote PNG: {args.out}")
    print(f"Wrote ticket: {args.ticket_out}")
    print(f"Flag in PNG watermark: {FLAG_TEXT}")


if __name__ == "__main__":
    main()
