# run_xprop.tcl  -- generic front-end for your formal tool
puts "Reading design..."
read_verilog xp.v
read_verilog top_xp.sv

puts "Setting top..."
set_top top_xp

# create a clock (tool-specific name may vary)
# many formal tools expect a create_clock command or add_clock
create_clock clk -period 10

puts "Files loaded. Use your formal tool to check assertions."
# Tool-specific check commands:
# - JasperGold example: check -a
# - Synopsys VC Formal example: verify -assertions
# - (Replace the next line with the correct command for your tool)
# check_assertions -all

puts "End of run_xprop.tcl"
