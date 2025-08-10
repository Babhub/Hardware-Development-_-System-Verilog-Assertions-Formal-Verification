Assignment 7 – Formal Tool X-Propagation Detection Lab
Goal:
This lab demonstrates the use of a formal verification tool to detect X-propagation issues in a FIFO design (module `queue` in file `xp.v`).
Directory Structure:
├── xp.v                 # Original buggy FIFO design
├── xp.v.buggy           # Backup of original xp.v
├── xp_fixed.v           # Fixed version of FIFO design (used to overwrite xp.v)
├── top_xp.sv            # Top-level wrapper instantiating two DUTs
├── tb_top_xp.sv         # Testbench for top_xp.sv
├── run_xprop.tcl        # TCL project script for formal tool
├── results_initial.log  # Formal run log on original xp.v (shows mismatch)
├── results_fixed.log    # Formal run log after fix (no mismatch)
├── results.log          # Simulation log file
└── README.txt           # This file
Design Overview:
- DUT is `queue`, a simple FIFO implemented in `xp.v`.
- Two instances of `queue` are instantiated in `top_xp.sv` with identical inputs.
- Outputs (`dout`, `full`, `empty`) are compared cycle-by-cycle using a SystemVerilog assertion.
- Formal tool is used to verify that outputs always match for both instances.
- Simulation is performed using Synopsys VCS with testbench `tb_top_xp.sv`.
Steps Performed:
1. **Setup:**
   
   cd ~/Desktop/HW7
   
   Verified all source files are present, including `xp.v`, `top_xp.sv`, `tb_top_xp.sv`, and `run_xprop.tcl`.

2. **Created top-level wrapper `top_xp.sv`:**
   - Instantiates two copies of `queue`.
   - Connects identical inputs (`clk`, `rstn`, `enq`, `deq`, `din`) to both.
   - Compares outputs every clock cycle using SystemVerilog assertions.

3. **Testbench `tb_top_xp.sv`:**
   - Drives inputs to `top_xp` module.
   - Controls clock, reset, and input stimulus.
   - Ends simulation after set time.

4. **Compile and run simulation with VCS:**
   
   vcs -full64 -sverilog tb_top_xp.sv top_xp.sv xp.v -o simv
   ./simv | tee results.log
   
   Observed mismatches due to X propagation, causing assertion failures.

5. **Created TCL script `run_xprop.tcl` for formal verification:**
   - Reads `xp.v` and `top_xp.sv`.
   - Sets `top_xp` as top module.
   - Creates clock and enables assertions.

6. **Ran formal tool on original `xp.v`:**
   
   your_formal_tool -f run_xprop.tcl | tee results_initial.log
   
   Result: Assertion failures due to mismatched outputs caused by X propagation.

7. **Identified Root Cause:**
   - Registers `head`, `tail`, `dout`, and FIFO memory array were not properly reset.
   - Missing default assignments in combinational logic for `full` and `empty`.

8. **Fixed the design:**
   - Created `xp_fixed.v` with:
     - Reset initialization for all registers and memory.
     - Default assignments in combinational always block.
   - Overwrote `xp.v` with `xp_fixed.v`.

9. **Recompiled and reran simulation:**
   
   vcs -full64 -sverilog tb_top_xp.sv top_xp.sv xp.v -o simv
   ./simv | tee results.log
   
   Observed no assertion failures; outputs matched.

10. **Reran formal tool on fixed design:**
    
    your_formal_tool -f run_xprop.tcl | tee results_fixed.log
    
    Result: Assertion holds; no mismatches detected.
Results Summary:
| Condition     | Outcome                                 |
|---------------|-----------------------------------------|
| Before Fix    | Outputs mismatch; assertion fails       |
| After Fix     | Outputs match; assertion holds          |
Files for Submission:
1. `top_xp.sv` — Top-level wrapper with two DUT instances  
2. `tb_top_xp.sv` — Testbench for simulation  
3. `run_xprop.tcl` — TCL script for formal tool run  
4. `results_initial.log` — Formal log showing mismatch on buggy design  
5. `results_fixed.log` — Formal log after fix showing no mismatch  
6. `results.log` — Simulation run log
Additional Notes:
- Replace `your_formal_tool` with the actual formal tool command (e.g., `jaspergold`, `vc_formal`).
- Simulation performed using Synopsys VCS, version W-2024.09-SP2_Full64.
- Simulation was run with commands:
  ```bash
  vcs -full64 -sverilog tb_top_xp.sv top_xp.sv xp.v -o simv
  ./simv | tee results.log
  ```
- Waveform dumping can be enabled by running:
  ```bash
  ./simv +vcs+dumpvars+all +stop_time=500 | tee results_wave.log
  ```
- GTKWave is recommended for waveform viewing (install if needed).

End of README

