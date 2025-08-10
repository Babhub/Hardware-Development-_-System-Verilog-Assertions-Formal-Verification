===========================================================
Assignment 7 – Formal Tool X-Propagation Detection Lab
===========================================================

Goal:
-----
This lab demonstrates the use of a formal verification tool
to detect X-propagation issues in a FIFO design (module name
queue from file xp.v).

Directory Structure:
--------------------
 ├── xp.v                 # Original buggy FIFO design
 ├── xp.v.buggy           # Backup of original xp.v
 ├── xp_fixed.v           # Fixed version of FIFO design (used to overwrite xp.v)
 ├── top_xp.sv            # Top-level wrapper instantiating two DUTs
 ├── run_xprop.tcl        # TCL project script for formal tool
 ├── results_initial.log  # Formal run log on original xp.v (shows mismatch)
 ├── results_fixed.log    # Formal run log after fix (no mismatch)
 └── README.txt           # This file

Design Overview:
----------------
- DUT is queue, a simple FIFO implemented in xp.v.
- Two instances of queue are instantiated in top_xp.sv with identical inputs.
- Outputs (dout, full, empty) are compared cycle-by-cycle using a SystemVerilog assertion.
- Formal tool is used to prove whether outputs always match for both instances.

Steps Performed:
----------------
1. Accessed the lab file from the terminal:
   cd Desktop
   cd HW7

2. Created top-level wrapper top_xp.sv:
   - Instantiates two copies of queue.
   - Drives them with identical clk, rstn, enq, deq, and din.
   - Compares outputs each clock cycle after reset using a property/assert.

3. Created project TCL script run_xprop.tcl:
   - Reads xp.v and top_xp.sv.
   - Sets top_xp as top module.
   - Creates a clock and prepares for assertion checking.

4. Ran formal tool on original xp.v:
   your_formal_tool -f run_xprop.tcl | tee results_initial.log
   -> Assertion fails due to mismatched outputs (caused by X-propagation).

5. Root Cause Identified:
   - Missing reset initialization for head, tail, dout, and FIFO memory array. Or in other words, Registers (head, tail, dout, FIFO memory) not reset.
   - Combinational block lacked default assignments for full and empty.

6. Fixed design:
   - Created xp_fixed.v with reset initialization for all registers and memory.
   - Added default assignments in combinational always block.
   - Overwrote xp.v with xp_fixed.v.

7. Reran formal tool:
   your_formal_tool -f run_xprop.tcl | tee results_fixed.log
   -> Assertion proved, no mismatches.

Results:
--------
- Before Fix (xp.v): Outputs from two DUT instances mismatch.
- After Fix (xp_fixed.v): Outputs always match; assertion holds for all possible inputs.

Attached Files for Submission:
---------------------
1) Top-level wrapper file:  top_xp.sv
2) TCL script file:         run_xprop.tcl
3) Log file:                results_initial.log (buggy) and results_fixed.log (fixed)


===========================================================
End of README
===========================================================
