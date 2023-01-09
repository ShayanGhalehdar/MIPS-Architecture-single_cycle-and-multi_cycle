//===========================================================
//
//			Shayan Ghaleh Dar 97102271
//
//			Implemented Instructions are:
//			R format:  add(u), sub(u), and, or, xor, nor, slt, sltu;
//			I format:  beq, bne, lw, sw, addiu, slti, sltiu, andi, ori, xori, lui.
//
//===========================================================

`timescale 1ns/1ns

module single_cycle_mips 
(
	input clk,
	input reset
);
 
	initial begin
		$display("Single Cycle MIPS Implemention");
		$display("Shayan Ghaleh Dar 97102271");
	end

	reg [31:0] PC;          // Keep PC as it is, its name is used in higher level test bench
  wire [31:0] RD;
  wire [31:0] RD1;
  wire [31:0] RD2;
  wire [31:26] Opr = RD[31:26];
  wire [25:21] rs = RD[25:21];
  wire [20:16] rt = RD[20:16];
  wire [20:16] rd = RD[15:11];
  
  wire RegWrite;
  wire RegDst;
  wire ALUSrc;
  wire [3:0] ALUControl;
  wire Branch;
  wire MemWrite;
  wire MemtoReg;
  
  wire [31:0] ALUResult;
  wire [31:0] ReadData;
  wire Zero;
  
  wire [4:0] WriteReg;
  wire [31:0] SignImm;
  wire [31:0] SrcA;
  wire [31:0] SrcB;
  reg [31:0] Result;
  wire [31:0] PCPlus4;
  wire [31:0] PCBranch;
  wire PCSrc;
  
  assign WriteReg = RegDst ? rd : rt;
  assign SrcA = RD1;
  assign SrcB = ALUSrc ? SignImm : RD2; 
  assign SignImm=(Opr==6'b001011||Opr==6'b001100||Opr==6'b001101||Opr==6'b001110) ? {16'h0000,RD[15:0]} : {{16{RD[15]}},RD[15:0]};
  assign PCPlus4 = reset ? PCPlus4 : PC+4;
  assign PCBranch = reset ? PCBranch : (SignImm<<2)+PCPlus4;
  assign PCSrc = reset ? PCSrc : ((Zero && Branch && Opr==6'b000100)||(!Zero && Branch && Opr==6'b000101));
  
  always@(posedge clk)
  begin
    if(reset)
      PC=32'h00000000;
    else if(reset==0 && PCPlus4!=32'h00000000)
      case(PCSrc)
        0 : PC = PCPlus4;
        1 : PC = PCBranch;
      endcase
  
  end
  
  always@(*)
  begin
     if(Opr==6'b100011)
        Result <= ReadData;
     else 
        Result <= ALUResult;
  end

  module Control(
   input [31:26] Op,
   input [5:0] Funct,
   output reg RegWrite,
   output reg RegDst,
   output reg ALUSrc,
   output reg [3:0] ALUControl,
   output reg Branch,
   output reg MemWrite,
   output reg MemtoReg
   );
  
   always@(*)
   begin
   if(Op==6'b000000 || Op[31:29]==3'b001 || Op==6'b100011)
     RegWrite=1;
   else
     RegWrite=0;
  
   if(Op==6'b000000)
     RegDst=1;
   else if (Op[31:29]==3'b001 || Op==6'b100011)
     RegDst=0;
   else if (Op==6'b000100 || Op==6'b000101 || Op==6'b101011)
     RegDst=1'bx;
    
   if(Op==6'b000000 || Op==6'b000100 || Op==6'b000101)
     ALUSrc=0;
   else if(Op==6'b100011 || Op==6'b101011 || Op[31:29]==3'b001)
     ALUSrc=1;
  
   if(Op==6'b000000)
   begin
     case(Funct)
       6'b100000 : ALUControl=4'b0010;
       6'b100001 : ALUControl=4'b0010;
       6'b100010 : ALUControl=4'b0110;
       6'b100011 : ALUControl=4'b0110;
       6'b100100 : ALUControl=4'b0000;
       6'b100101 : ALUControl=4'b0001;
       6'b100110 : ALUControl=4'b0011;
       6'b100111 : ALUControl=4'b0001;
       6'b101010 : ALUControl=4'b0111;
       6'b101011 : ALUControl=4'b1000;
     endcase
   end
   else if(Op!=6'b000000)
   begin
     case(Op)
       6'b000100 : ALUControl=4'b0110;
       6'b000101 : ALUControl=4'b0110;
       6'b001000 : ALUControl=4'b0010;
       6'b001001 : ALUControl=4'b0010;
       6'b001010 : ALUControl=4'b0111;
       6'b001011 : ALUControl=4'b1000;
       6'b001100 : ALUControl=4'b0000;
       6'b001101 : ALUControl=4'b0001;
       6'b001110 : ALUControl=4'b0011;
       6'b001111 : ALUControl=4'b0101;
       6'b100011 : ALUControl=4'b0010;
       6'b101011 : ALUControl=4'b0010;
     endcase
   end  
   if(Op==6'b000100 || Op==6'b000101)
     Branch=1;
   else
     Branch=0;
     
   if(Op==6'b101011)
     MemWrite=1;
   else 
     MemWrite=0;
    
   if(Op==6'b100011)
     MemtoReg=1;
   else if(Op==6'b101011 || Op==6'b000100 || Op==6'b000101)
     MemtoReg=1'bx;
   else
     MemtoReg=0; 
  
   end
  endmodule
  
  
	module my_alu(
   input  [3:0] Op,
   input  [31:0] A,
   input  [31:0] B,
   output  [31:0] X,
   output        Z
   );

   wire sub = Op != 4'b0010;
   wire [31:0] bb = sub ? ~B : B;
   wire [32:0] sum = A + bb + sub;
   wire sltu = ! sum[32];

   wire v = sub ?
            ( A[31] != B[31] && A[31] != sum[31] )
          : ( A[31] == B[31] && A[31] != sum[31] );

   wire slt = v ^ sum[31];

   reg [31:0] x;

   always @(*)
      case(Op)
         4'b0000 : x = A & B;
         4'b0001 : x = A | B;
         4'b0010 : x = sum;
         4'b0011 : x = A ^ B;
         4'b0100 : x = ~(A | B);
         4'b0101 : x = (B<<16)&(32'hffff0000);
         4'b0110 : x = sum;
         4'b0111 : x = slt;
         4'b1000 : x = sltu; 
         default : x = 32'hxxxxxxxx;
      endcase
   
   assign X = x;
   assign Z = x == 32'h00000000;
  endmodule

	
//========================================================== 
//	instantiated modules
//========================================================== 

//	Instruction Memory
	async_mem imem			// keep the exact instance name
	(
		.clk		   ('b0),
		.write		('b0),		// no write for instruction memory
		.address	   (PC),		   // address instruction memory with pc
		.write_data	('bx),
		.read_data	(RD)
	);
	
// Data Memory
	async_mem dmem			// keep the exact instance name
	(
		.clk		   (clk),
		.write		(MemWrite),
		.address	   (ALUResult),
		.write_data	(RD2),
		.read_data	(ReadData)
	);
	
// Register File
  reg_file regf
  (
    .clk (clk),
    .write (RegWrite),
    .WR (WriteReg),
    .WD (Result),
    .RR1 (rs),
    .RR2 (rt),
    .RD1 (RD1),
    .RD2 (RD2)
  );
//Control Unit
  Control ctrl
  (
    .Op(Opr),
    .Funct(RD[5:0]),
    .RegWrite(RegWrite),
    .RegDst(RegDst),
    .ALUSrc(ALUSrc),
    .ALUControl(ALUControl),
    .Branch(Branch),
    .MemWrite(MemWrite),
    .MemtoReg(MemtoReg)
  );
//ALU
  my_alu myalu
  (
    .Op(ALUControl),
    .A(SrcA),
    .B(SrcB),
    .X(ALUResult),
    .Z(Zero)
  );

endmodule