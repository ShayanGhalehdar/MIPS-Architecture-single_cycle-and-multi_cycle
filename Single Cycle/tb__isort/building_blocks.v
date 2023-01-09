
`timescale 1ns/10ps

//==============================================================================

module async_mem(
   input clk,
   input write,
   input [31:0] address,
   input [31:0] write_data,
   output [31:0] read_data
);

	reg [31:0] mem_data [0:(1<<16)-1];

// assign #7 read_data = mem_data[ address[17:2] ];  // address to read data delay of 7ns
   assign    read_data = mem_data[ address[17:2] ];  // zero delay, address to read data

   always @( posedge clk )
      if ( write )
         mem_data[ address[17:2] ] <= write_data;

endmodule

//==============================================================================
`define DEBUG	
// comment this line to disable register content writing below
//==============================================================================

module reg_file(
	input  clk,
	input  write,
	input  [ 4:0] WR,
	input  [31:0] WD,
	input  [ 4:0] RR1,
	input  [ 4:0] RR2,
	output [31:0] RD1,
	output [31:0] RD2
	);

	reg [31:0] reg_data [0:31];

	assign RD1 = reg_data[RR1];
	assign RD2 = reg_data[RR2];

// Data Forwarding in Register File for future use
//	assign RD1 = (RR1 == WR && write && RR1) ? WD : reg_data[RR1];
//	assign RD2 = (RR2 == WR && write && RR2) ? WD : reg_data[RR2];
	
	always @(posedge clk) begin
		if(write) begin
			reg_data[WR] <= WD;

			`ifdef DEBUG
			if(WR)
				$display("$%0d = %x", WR, WD);
			`endif
		end
		reg_data[0] <= 32'h00000000;
	end

endmodule

/*==============================================================================

module my_alu(
   input  [2:0] Op,
   input  [31:0] A,
   input  [31:0] B,
   output [31:0] X,
   output        Z
   );

   wire sub = Op != `ADD;
   wire [31:0] bb = sub ? ~B : B;
   wire [32:0] sum = A + bb + sub;
   wire sltu = ! sum[32];

   wire v = sub ?
            ( A[31] != B[31] && A[31] != sum[31] )
          : ( A[31] == B[31] && A[31] != sum[31] );

   wire slt = v ^ sum[31];

   reg [31:0] x;

   always @( * )
      case( Op )
         `ADD : x = sum;
         `SUB : x = sum;
         `SLT : x = slt;
         `SLTU: x = sltu;
         `AND : x = A & B;
         `OR  : x = A | B;
         `NOR : x = ~(A | B);
         `XOR : x = A ^ B;
         default : x = 32'hxxxxxxxx;
      endcase

   assign X = x;
   assign Z = x == 32'h00000000;

endmodule

//============================================================================*/


