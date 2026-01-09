# ----------------------------
# working for questa / modelSim
# ----------------------------

# create work library
vlib work
vmap work work

vlog -sv ../rtl/skid_buffer.sv ../tb/tb_top.sv

# sim
vsim -coverage work.tb_top

add wave -r /*

run -all

# show coverage in transcript
coverage report -details

quit -f
