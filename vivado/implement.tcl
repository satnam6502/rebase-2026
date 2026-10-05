# Out-of-context implementation of a generated sorter with Vivado.
#
#   vivado -mode batch -source vivado/implement.tcl -tclargs NAME SVDIR OUTDIR [PART] [PERIOD_NS]
#
# Synthesises, places and routes NAME (from SVDIR/NAME.sv), then writes
# utilisation and timing reports and NAME_placement.tsv, the slice and BEL that
# Vivado chose for every relatively placed cell.

set name   [lindex $argv 0]
set svdir  [lindex $argv 1]
set outdir [lindex $argv 2]
set part   [expr {[llength $argv] > 3 ? [lindex $argv 3] : "xc7a200tsbg484-1"}]
set period [expr {[llength $argv] > 4 ? [lindex $argv 4] : 4.0}]
# Optional slice for the macro origin, e.g. X36Y50 (vivado/find_origin.py finds one).
set origin [expr {[llength $argv] > 5 ? [lindex $argv 5] : ""}]

file mkdir $outdir
create_project -in_memory -part $part
read_verilog -sv [file join $svdir $name.sv]
synth_design -top $name -part $part -mode out_of_context
create_clock -name clk -period $period [get_ports clk]
if {$origin ne ""} {
  # Anchor the relatively placed macro: place the LUT at RLOC X0Y0 (BEL A6LUT) in
  # SLICE_<origin>; the rest of the macro follows it.
  set anchor [lindex [get_cells -hierarchical -filter {RLOC == X0Y0 && REF_NAME =~ LUT*}] 0]
  if {$anchor ne ""} { place_cell $anchor SLICE_${origin}/A6LUT }
}
place_design
route_design

report_utilization -file [file join $outdir ${name}_utilization.rpt]
report_timing_summary -max_paths 5 -file [file join $outdir ${name}_timing.rpt]

set f [open [file join $outdir ${name}_placement.tsv] w]
set placed [get_cells -hierarchical -filter {IS_PRIMITIVE && DONT_TOUCH}]
foreach c $placed {
  puts $f "[get_property NAME $c]\t[get_property RLOC $c]\t[get_property LOC $c]\t[get_property BEL $c]"
}
close $f

set wns [get_property SLACK [get_timing_paths -max_paths 1 -setup]]
set summary [open [file join $outdir ${name}_summary.txt] w]
puts $summary "design $name"
puts $summary "part $part"
puts $summary "period_ns $period"
puts $summary "wns_ns $wns"
puts $summary "slices [llength [get_sites -of_objects $placed]]"
close $summary
