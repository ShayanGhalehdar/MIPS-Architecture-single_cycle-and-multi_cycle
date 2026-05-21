# MIPS Processor in Verilog — Single-Cycle and Multi-Cycle

Two Verilog implementations of a subset MIPS processor: a single-cycle datapath and a multi-cycle datapath, each with its own control unit and testbench. Built as Computer Architecture coursework.

## What's Implemented

Both versions support a representative MIPS subset:

- R-type ALU: `add`, `sub`, `and`, `or`, `slt`
- Immediate: `addi`, `andi`, `ori`, `lw`, `sw`, `lui`
- Branch/jump: `beq`, `bne`, `j`, `jal`, `jr`

The single-cycle version computes every instruction in one clock; the multi-cycle version breaks execution into IF / ID / EX / MEM / WB stages controlled by a finite-state machine, sharing the ALU and a single memory port across stages.

## Repository Structure

```
Single Cycle/
  building_blocks.v         — ALU, register file, sign extender, mux, etc.
  single_cycle_mips.v       — Top-level datapath + control
  tb__basic/                — Basic instruction test
  tb__isort/                — Insertion-sort program test
  transcript                — ModelSim transcript

Multi Cycle/
  multi_cycle_mips.v        — Top-level datapath with FSM controller
  multi_cycle_mips__tb.v.txt — Testbench
  isort32.cod.txt           — Object code for an insertion-sort program
  isort32.hex.txt           — Hex memory image
  isort32.dsm.txt           — Disassembly
  MIPS_instructions_table.pdf — Instruction encoding reference
  TestSet1/                 — Additional test vectors
  transcript                — ModelSim transcript
```

## How to Simulate (ModelSim / QuestaSim)

```tcl
# Single cycle
cd "Single Cycle"
vlib work
vlog building_blocks.v single_cycle_mips.v
vsim -c work.tb -do "run -all; quit"
```

The `isort32` test programs run an in-memory insertion sort and are a good end-to-end correctness check.

## License

MIT — see [LICENSE](LICENSE).
