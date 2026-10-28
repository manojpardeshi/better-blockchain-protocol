//! A minimal RV32IM emulator that counts retired instructions.
//!
//! It stands in for a zkVM's executor: SP1 and RISC Zero prove RV32IM
//! execution, and their cycle counts track the number of retired
//! instructions (RISC Zero adds paging cycles; both replace some work with
//! precompiles). This lets us measure what the Sigil step relation costs
//! as a guest program without the zkVM toolchains, which this environment
//! cannot download.
//!
//! Usage: rv32-count <guest.elf> <input-file>
//! The input is mapped at 0x0600_0000; a0 = its address, a1 = its length.
//! Syscalls (a7): 93 exit(a0), 64 write(fd=a0, ptr=a1, len=a2),
//! 0x1000 read the retired-instruction counter into a0 (low) / a1 (high).

use std::env;
use std::fs;
use std::io::Write;
use std::process::exit;

const MEM_SIZE: usize = 0x0800_0000;
const INPUT_ADDR: u32 = 0x0600_0000;

struct Cpu {
    x: [u32; 32],
    pc: u32,
    mem: Vec<u8>,
    retired: u64,
}

impl Cpu {
    #[inline]
    fn check(&self, a: u32, n: u32) -> usize {
        let a = a as usize;
        if a + n as usize > self.mem.len() {
            panic!("memory access out of range: {a:#x} (pc {:#x})", self.pc);
        }
        a
    }
    #[inline]
    fn ld(&self, a: u32, n: u32) -> u32 {
        let i = self.check(a, n);
        match n {
            1 => self.mem[i] as u32,
            2 => u16::from_le_bytes([self.mem[i], self.mem[i + 1]]) as u32,
            _ => u32::from_le_bytes(self.mem[i..i + 4].try_into().unwrap()),
        }
    }
    #[inline]
    fn st(&mut self, a: u32, n: u32, v: u32) {
        let i = self.check(a, n);
        self.mem[i..i + n as usize].copy_from_slice(&v.to_le_bytes()[..n as usize]);
    }
}

fn load_elf(cpu: &mut Cpu, elf: &[u8]) -> u32 {
    assert!(&elf[0..4] == b"\x7fELF" && elf[4] == 1 && elf[5] == 1, "need a 32-bit little-endian ELF");
    let u16_at = |o: usize| u16::from_le_bytes([elf[o], elf[o + 1]]) as usize;
    let u32_at = |o: usize| u32::from_le_bytes(elf[o..o + 4].try_into().unwrap());
    assert_eq!(u16_at(18), 0xF3, "not RISC-V");
    let entry = u32_at(24);
    let (phoff, phentsize, phnum) = (u32_at(28) as usize, u16_at(42), u16_at(44));
    for i in 0..phnum {
        let ph = phoff + i * phentsize;
        if u32_at(ph) != 1 {
            continue; // PT_LOAD only
        }
        let (off, vaddr, filesz, memsz) = (u32_at(ph + 4) as usize, u32_at(ph + 8) as usize, u32_at(ph + 16) as usize, u32_at(ph + 20) as usize);
        cpu.mem[vaddr..vaddr + filesz].copy_from_slice(&elf[off..off + filesz]);
        cpu.mem[vaddr + filesz..vaddr + memsz].fill(0);
    }
    entry
}

fn sext(v: u32, bits: u32) -> i32 {
    ((v << (32 - bits)) as i32) >> (32 - bits)
}

fn run(cpu: &mut Cpu) -> u32 {
    loop {
        let ins = cpu.ld(cpu.pc, 4);
        cpu.retired += 1;
        let op = ins & 0x7f;
        let rd = ((ins >> 7) & 31) as usize;
        let f3 = (ins >> 12) & 7;
        let rs1 = ((ins >> 15) & 31) as usize;
        let rs2 = ((ins >> 20) & 31) as usize;
        let f7 = ins >> 25;
        let a = cpu.x[rs1];
        let b = cpu.x[rs2];
        let imm_i = sext(ins >> 20, 12) as u32;
        let mut next = cpu.pc.wrapping_add(4);
        let mut wr: Option<u32> = None;
        match op {
            0x37 => wr = Some(ins & 0xffff_f000),                         // LUI
            0x17 => wr = Some(cpu.pc.wrapping_add(ins & 0xffff_f000)),    // AUIPC
            0x6f => {                                                     // JAL
                let imm = ((ins >> 31) << 20) | (((ins >> 12) & 0xff) << 12) | (((ins >> 20) & 1) << 11) | (((ins >> 21) & 0x3ff) << 1);
                wr = Some(next);
                next = cpu.pc.wrapping_add(sext(imm, 21) as u32);
            }
            0x67 => {                                                     // JALR
                wr = Some(next);
                next = a.wrapping_add(imm_i) & !1;
            }
            0x63 => {                                                     // branches
                let imm = ((ins >> 31) << 12) | (((ins >> 7) & 1) << 11) | (((ins >> 25) & 0x3f) << 5) | (((ins >> 8) & 0xf) << 1);
                let take = match f3 {
                    0 => a == b,
                    1 => a != b,
                    4 => (a as i32) < (b as i32),
                    5 => (a as i32) >= (b as i32),
                    6 => a < b,
                    7 => a >= b,
                    _ => panic!("bad branch {ins:#x}"),
                };
                if take {
                    next = cpu.pc.wrapping_add(sext(imm, 13) as u32);
                }
            }
            0x03 => {                                                     // loads
                let addr = a.wrapping_add(imm_i);
                wr = Some(match f3 {
                    0 => sext(cpu.ld(addr, 1), 8) as u32,
                    1 => sext(cpu.ld(addr, 2), 16) as u32,
                    2 => cpu.ld(addr, 4),
                    4 => cpu.ld(addr, 1),
                    5 => cpu.ld(addr, 2),
                    _ => panic!("bad load {ins:#x}"),
                });
            }
            0x23 => {                                                     // stores
                let imm = sext(((ins >> 25) << 5) | ((ins >> 7) & 31), 12) as u32;
                let addr = a.wrapping_add(imm);
                match f3 {
                    0 => cpu.st(addr, 1, b),
                    1 => cpu.st(addr, 2, b),
                    2 => cpu.st(addr, 4, b),
                    _ => panic!("bad store {ins:#x}"),
                }
            }
            0x13 => {                                                     // OP-IMM
                let sh = (ins >> 20) & 31;
                wr = Some(match f3 {
                    0 => a.wrapping_add(imm_i),
                    1 => a << sh,
                    2 => ((a as i32) < (imm_i as i32)) as u32,
                    3 => (a < imm_i) as u32,
                    4 => a ^ imm_i,
                    5 => if f7 & 0x20 != 0 { ((a as i32) >> sh) as u32 } else { a >> sh },
                    6 => a | imm_i,
                    _ => a & imm_i,
                });
            }
            0x33 => {                                                     // OP / M
                wr = Some(if f7 == 1 {
                    match f3 {
                        0 => a.wrapping_mul(b),
                        1 => ((a as i32 as i64 * b as i32 as i64) >> 32) as u32,
                        2 => ((a as i32 as i64 * b as u64 as i64) >> 32) as u32,
                        3 => ((a as u64 * b as u64) >> 32) as u32,
                        4 => if b == 0 { u32::MAX } else if a == 0x8000_0000 && b == u32::MAX { a } else { ((a as i32) / (b as i32)) as u32 },
                        5 => if b == 0 { u32::MAX } else { a / b },
                        6 => if b == 0 { a } else if a == 0x8000_0000 && b == u32::MAX { 0 } else { ((a as i32) % (b as i32)) as u32 },
                        _ => if b == 0 { a } else { a % b },
                    }
                } else {
                    match (f3, f7) {
                        (0, 0) => a.wrapping_add(b),
                        (0, 0x20) => a.wrapping_sub(b),
                        (1, _) => a << (b & 31),
                        (2, _) => ((a as i32) < (b as i32)) as u32,
                        (3, _) => (a < b) as u32,
                        (4, _) => a ^ b,
                        (5, 0) => a >> (b & 31),
                        (5, 0x20) => ((a as i32) >> (b & 31)) as u32,
                        (6, _) => a | b,
                        (7, _) => a & b,
                        _ => panic!("bad op {ins:#x}"),
                    }
                });
            }
            0x0f => {}                                                    // FENCE
            0x73 => {                                                     // ECALL
                if ins != 0x0000_0073 {
                    panic!("unsupported system instruction {ins:#x} at {:#x}", cpu.pc);
                }
                match cpu.x[17] {
                    93 => return cpu.x[10],
                    64 => {
                        let (p, n) = (cpu.x[11] as usize, cpu.x[12] as usize);
                        let s = &cpu.mem[p..p + n];
                        if cpu.x[10] == 2 { std::io::stderr().write_all(s).unwrap() } else { std::io::stdout().write_all(s).unwrap() }
                        cpu.x[10] = n as u32;
                    }
                    0x1000 => {
                        cpu.x[10] = cpu.retired as u32;
                        cpu.x[11] = (cpu.retired >> 32) as u32;
                    }
                    n => panic!("unknown syscall {n}"),
                }
            }
            _ => panic!("illegal instruction {ins:#010x} at {:#x}", cpu.pc),
        }
        if let Some(v) = wr {
            if rd != 0 {
                cpu.x[rd] = v;
            }
        }
        cpu.pc = next;
    }
}

fn main() {
    let args: Vec<String> = env::args().collect();
    if args.len() != 3 {
        eprintln!("usage: rv32-count <guest.elf> <input>");
        exit(2);
    }
    let elf = fs::read(&args[1]).expect("read elf");
    let input = fs::read(&args[2]).expect("read input");
    let mut cpu = Cpu { x: [0; 32], pc: 0, mem: vec![0; MEM_SIZE], retired: 0 };
    cpu.pc = load_elf(&mut cpu, &elf);
    let base = INPUT_ADDR as usize;
    cpu.mem[base..base + input.len()].copy_from_slice(&input);
    cpu.x[10] = INPUT_ADDR;
    cpu.x[11] = input.len() as u32;
    let t = std::time::Instant::now();
    let code = run(&mut cpu);
    println!("RETIRED {} EXIT {code} HOST_SECONDS {:.3}", cpu.retired, t.elapsed().as_secs_f64());
    exit(code as i32);
}
