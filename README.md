# AXI-Stream Audio Peak/RMS Analyzer
This project takes a stream of audio samples, computes per-frame peak and RMS, raises an IRQ if clipping or RMS exceeds a CSR-programmable limit, using SystemVerilog.

## Features

- AXI-Stream input interface (16-bit signed samples)
- Real-time peak and RMS calculation
- Programmable peak/RMS thresholds
- Interrupt output on threshold exceed
- RTL + UVM-style testbench with:
  - Constrained-random stimulus
  - Scoreboard comparison
  - Weighted functional coverage
  - Protocol and behavioral SVA assertions

## Repo Structure

- `rtl/`: Design logic
- `tb/`: Testbench components
- `assertions/`: SystemVerilog assertions
- `coverage/`: Functional coverage bins
- `sim/`: Scripts for running simulations
- `docs/`: Block diagrams and design notes
- `scripts/`: Python/MATLAB DSP models

## Running Simulation

```bash
# Compile
vlog -f sim/compile.f
# Simulate
vsim -do sim/run_modelsim.do
```
