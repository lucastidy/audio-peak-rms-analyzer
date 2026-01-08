vlib work
vlog -sv ./peak_rms_core.sv ./tb_top.sv
vsim -c tb_top -do "run -all; quit"