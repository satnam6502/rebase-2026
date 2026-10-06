// Behavioural models of the UNISIM primitives that ruby-lean emits, for
// simulating without Vivado (sim/verilate.sh). They model only the ports and
// parameters the emitter uses; `make sim` against the real UNISIM library
// remains the reference.

module LUT1 #(parameter logic [1:0] INIT = '0) (input logic I0, output logic O);
  assign O = INIT[I0];
endmodule

module LUT2 #(parameter logic [3:0] INIT = '0) (input logic I0, I1, output logic O);
  assign O = INIT[{I1, I0}];
endmodule

module LUT3 #(parameter logic [7:0] INIT = '0) (input logic I0, I1, I2, output logic O);
  assign O = INIT[{I2, I1, I0}];
endmodule

module LUT4 #(parameter logic [15:0] INIT = '0) (input logic I0, I1, I2, I3, output logic O);
  assign O = INIT[{I3, I2, I1, I0}];
endmodule

module LUT5 #(parameter logic [31:0] INIT = '0) (input logic I0, I1, I2, I3, I4, output logic O);
  assign O = INIT[{I4, I3, I2, I1, I0}];
endmodule

module LUT6 #(parameter logic [63:0] INIT = '0)
    (input logic I0, I1, I2, I3, I4, I5, output logic O);
  assign O = INIT[{I5, I4, I3, I2, I1, I0}];
endmodule

// Each stage propagates the carry if S is set and otherwise generates DI.
module CARRY4 (input logic CI, CYINIT, input logic [3:0] DI, S, output logic [3:0] O, CO);
  logic [4:0] c;
  assign c[0] = CI | CYINIT;
  for (genvar i = 0; i < 4; i++) begin : stage
    assign c[i + 1] = S[i] ? c[i] : DI[i];
    assign O[i] = S[i] ^ c[i];
  end
  assign CO = c[4:1];
endmodule

module FDCE #(parameter logic INIT = 1'b0) (input logic C, CE, CLR, D, output logic Q);
  initial Q = INIT;
  always @(posedge C or posedge CLR)
    if (CLR) Q <= 1'b0;
    else if (CE) Q <= D;
endmodule
