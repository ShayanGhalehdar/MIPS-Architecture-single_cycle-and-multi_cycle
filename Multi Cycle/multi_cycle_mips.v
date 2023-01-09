//================================
//  Shayan GhalehDar - 97102271
//================================

`timescale 1ns/100ps

   `define ADD  3'b000
   `define SUB  3'b001
   `define SLT  3'b010
   `define SLTU 3'b011
   `define AND  3'b100
   `define XOR  3'b101
   `define OR   3'b110
   `define NOR  3'b111

module multi_cycle_mips(

   input clk,
   input reset,

   // Memory Ports
   output  [31:0] mem_addr,
   input   [31:0] mem_read_data,
   output  [31:0] mem_write_data,
   output         mem_read,
   output         mem_write
);

   // Data Path Registers
   reg MRE, MWE;//memory write enable and memory read enable
   reg [31:0] A, B, PC, IR, MDR, MAR;//MDR = memory data register & MAR = memory addres register & IR = instruction register

   // Data Path Control Lines, donot forget, regs are not always regs !!
   reg setMRE, clrMRE, setMWE, clrMWE;//memory read & write enable
   reg Awrt, Bwrt, RFwrt, PCwrt, IRwrt, MDRwrt, MARwrt, IorD;
   reg [1:0] PCSrc;
   reg [31:0] hi;
   reg [31:0] lo;
   reg mult_start;
   reg ready_mult;

   wire mul_start = mult_start;
   wire [63:0]Out_w = {hi , lo};
   wire ready_mul = ready_mult;

   // Memory Ports Binding
   assign mem_addr = MAR;//memory address register
   assign mem_read = MRE;
   assign mem_write = MWE;
   assign mem_write_data = B;

   // Mux & ALU Control Lines
   reg [2:0] aluOp;
   reg [1:0] aluSelB;
   reg SgnExt, aluSelA;
   reg [2:0]MemtoReg;
   reg [1:0]RegDst;
   
   // Wiring
   wire aluZero;
   wire [31:0] aluResult, rfRD1, rfRD2;
   wire [31:0] pcjump;
   assign pcjump = {PC [31:28] , IR[25:0] , 2'b00 };

   // Clocked Registers
   always @( posedge clk ) begin
      if( reset )
         PC <= #0.1 32'h00000000;
      else if( PCwrt )
		case(PCSrc)
			2'b00: PC <= #0.1 aluResult;
			2'b01: PC <= #0.1 pcjump;
			2'b10: PC <= #0.1 A;
		endcase
      if( Awrt ) A <= #0.1 rfRD1;
      if( Bwrt ) B <= #0.1 rfRD2;

      if( MARwrt ) MAR <= #0.1 IorD ? aluResult : PC;

      if( IRwrt ) IR <= #0.1 mem_read_data;
      if( MDRwrt ) MDR <= #0.1 mem_read_data;//when we want to load we read data from data memory(the lower mux)

      if( reset | clrMRE ) MRE <= #0.1 1'b0;
          else if( setMRE) MRE <= #0.1 1'b1;

      if( reset | clrMWE ) MWE <= #0.1 1'b0;
          else if( setMWE) MWE <= #0.1 1'b1;
   end

   //mux_regdst
   reg [4:0]A3;
   always@(*)
    begin
	case(RegDst)
		2'b01:A3 = IR[15:11];
		2'b00:A3 = IR[20:16];
		2'b10:A3 = 5'b11111;
    endcase
	end
	
	 //mux_memtoreg
   reg [31:0]WD3;
   always@(*)
    begin
	case(MemtoReg)
		3'b001:WD3 = MDR;
		3'b000:WD3 = aluResult;
		3'b010:WD3 = PC;
		3'b011:WD3 = IR[15:0]<< 16;
		3'b100:WD3 = hi;
		3'b101:WD3 = lo;
    endcase
	end
	
   // Register File
   reg_file rf(
      .clk( clk ),
      .write( RFwrt ),

      .RR1( IR[25:21] ),
      .RR2( IR[20:16] ),
      .RD1( rfRD1 ),
      .RD2( rfRD2 ),

      .WR( A3 ),
      .WD( MemtoReg ? MDR : aluResult )
   );

   // Sign/Zero Extension
   wire [31:0] SZout = SgnExt ? {{16{IR[15]}}, IR[15:0]} : {16'h0000, IR[15:0]};//SgnExt = 1 => SZout = signextnd (imm) and Sgnext = 0 => SZot = zeroext (imm)

   // ALU-A Mux
   wire [31:0] aluA = aluSelA ? A : PC;

   // ALU-B Mux
   reg [31:0] aluB;
   always @(*)
   case (aluSelB)
      2'b00: aluB = B;
      2'b01: aluB = 32'h4;
      2'b10: aluB = SZout;
      2'b11: aluB = SZout << 2;
   endcase

   my_alu alu(
      .A( aluA ),
      .B( aluB ),
      .Op( aluOp ),

      .X( aluResult ),
      .Z( aluZero )
   );
   
   multiplier4 ml(
	 .clk(clk),
	 .A(A),
	 .B(B),
	 .start(mul_start),
	 .ready(ready_mul),
	 .Out(Out_w)
   );
   /////////////////////////////out


   // Controller Starts Here

   // Controller State Registers
   reg [4:0] state, nxt_state;

   // State Names & Numbers
   localparam
    RESET = 0, FETCH1 = 1, FETCH2 = 2, FETCH3 = 3, DECODE = 4,
    EX_ALU_R = 7, EX_ALU_I = 8,EX_LUI = 9,
    EX_LW_1 = 11, EX_LW_2 = 12, EX_LW_3 = 13, EX_LW_4 = 14, EX_LW_5 = 15,
	EX_MFHI = 16, EX_MFLO = 17,
	EX_J = 18, EX_JL = 19,
    EX_SW_1 = 21, EX_SW_2 = 22, EX_SW_3 = 23,
    EX_BRA_1 = 25, EX_BRA_2 = 26,
    EX_JR = 27, EX_JLR1 = 28, EX_JLR2 = 29,
	EX_MULT = 30;

   // State Clocked Register 
   always @(posedge clk)
      if(reset)
         state <= #0.1 RESET;
      else
         state <= #0.1 nxt_state;

   task PrepareFetch;
      begin
         IorD = 0;
         setMRE = 1;
         MARwrt = 1;
         nxt_state = FETCH1;
      end
   endtask

   // State Machine Body Starts Here
   always @( * ) begin

      nxt_state = 'bx;

      aluOp = 'bx; SgnExt = 'bx;
      aluSelA = 'bx; aluSelB = 'bx;
      MemtoReg = 'bx; RegDst = 'bx;

      PCwrt = 0; PCSrc = 0;
      Awrt = 0; Bwrt = 0;
      RFwrt = 0; IRwrt = 0;
      MDRwrt = 0; MARwrt = 0;
      setMRE = 0; clrMRE = 0;
      setMWE = 0; clrMWE = 0;
	  mult_start = 0;

      case(state)

         RESET:
            PrepareFetch;

         FETCH1:
            nxt_state = FETCH2;

         FETCH2:
            nxt_state = FETCH3;

         FETCH3: begin
            IRwrt = 1;
            PCwrt = 1;
            clrMRE = 1;
            aluSelA = 0;
            aluSelB = 2'b01;
            aluOp = `ADD;
            nxt_state = DECODE;//pc = pc + 4; done!
         end

		DECODE: begin
            Awrt = 1;
            Bwrt = 1;
            case( IR[31:26] )
                6'b000_000:             // R-format
                  case( IR[5:3] )
                     3'b000: ;
                     3'b001: nxt_state = EX_JR;
                     3'b010: case( IR[2:0] )
						3'b000: nxt_state = EX_MFHI;
						3'b010: nxt_state = EX_MFLO;
					 endcase
                     3'b011: begin nxt_state = EX_MULT; mult_start = 1; end
                     3'b100: nxt_state = EX_ALU_R;//add(u) & sub(u) & and & or & xor & nor
                     3'b101: nxt_state = EX_ALU_R;//slt & sltu
                     3'b110: ;
                     3'b111: ;
                  endcase

               6'b001_000,             // addi
               6'b001_001,             // addiu
               6'b001_010,             // slti
               6'b001_011,             // sltiu
               6'b001_100,             // andi
               6'b001_101,             // ori
               6'b001_110:             // xori
                  nxt_state = EX_ALU_I;

               6'b100_011:
                  nxt_state = EX_LW_1;

               6'b101_011:
                  nxt_state = EX_SW_1;

               6'b000_100,
               6'b000_101:
                  nxt_state = EX_BRA_1;//beq & bne
				6'b001_111:
					nxt_state = EX_LUI;
					
				6'b000_010:
					nxt_state = EX_J;
				6'b000_011:
					nxt_state = EX_JL;
					
					
                  
                  

               // rest of instructiones should be decoded here

            endcase
         end

		EX_ALU_R: begin
	    aluSelA = 1;
	    aluSelB = 2'b00;
	    case(IR[5:0])
		6'b100_000,
		6'b100_001:
		    aluOp = `ADD;
		6'b100_010,
		6'b100_011:
		    aluOp = `SUB;
		6'b101_010:
		    aluOp = `SLT;
		6'b101_011:
		    aluOp = `SLTU;
		6'b100_100:
		    aluOp = `AND;
		6'b100_101:
		    aluOp = `OR;
		6'b100_110:
		    aluOp = `XOR;
		6'b100_111:
		    aluOp = `NOR;
		default : aluOp = 3'bxxx;
	    endcase
	    RegDst = 1;
	    MemtoReg = 0;
	    RFwrt = 1;
		PCwrt = 0;
        PrepareFetch;
         end

		EX_ALU_I: begin
        aluSelA = 1;
	    aluSelB = 2'b10;
	    case(IR[31:26])//for operation
		6'b001_000,
		6'b001_001:
		    aluOp = `ADD;
		6'b001_010:
		    aluOp = `SLT;
		6'b001_011:
		    aluOp = `SLTU;
		6'b001_100:
		    aluOp = `AND;
		6'b001_101:
		    aluOp = `OR;
		6'b001_110:
		    aluOp = `XOR;
		default : aluOp = 3'bxxx;
	    endcase
	    case (IR[31:26])//for true extend of imm
		6'b001_000,//addi
		6'b001_010://slti
		    SgnExt = 1'b1;//addi & slti need signext of imm not zero extend
		6'b001_010,
		6'b001_011,
		6'b001_100,
		6'b001_101,
		6'b001_110:
		    SgnExt = 1'b0;
		default : SgnExt = 1'bx;
	    endcase
	    RegDst = 0;
	    MemtoReg = 0;
	    RFwrt = 1;
		PCwrt = 0;
		PrepareFetch;
         end

		EX_LW_1: begin
			IRwrt = 0;
			SgnExt = 1;
			aluSelA = 1;
			aluSelB = 2'b10;
			aluOp = `ADD;
			IorD = 1;
			setMRE = 1;
			clrMWE = 1;
			MARwrt = 1;
			IRwrt = 0;
			PCwrt = 0;
			nxt_state = EX_LW_2;
		end

		EX_LW_2: begin
        nxt_state = EX_LW_3;
	end

		EX_LW_3: begin
            nxt_state = EX_LW_4;
	 end

		EX_LW_4: begin
            nxt_state = EX_LW_5;
			MDRwrt = 1;
		end

		EX_LW_5: begin
			MemtoReg = 1;
			RegDst = 0;
			RFwrt = 1;
			PrepareFetch;
		end

		EX_SW_1: begin
			SgnExt = 1;
			aluSelA = 1;
			aluSelB = 2'b10;
			aluOp = `ADD;
			IorD = 1;
			clrMRE = 1;
			setMWE = 1;
			MARwrt = 1;
			PCwrt = 0;
			IRwrt = 0;
			nxt_state = EX_SW_2;
		end
		
		EX_SW_2: begin
			clrMWE = 1;
			nxt_state = EX_SW_3;
		end
		
		EX_SW_3: begin
			PrepareFetch;
		end

        EX_BRA_1: begin
			aluSelA = 1;
			aluSelB = 2'b00;
			aluOp = `SUB;
			PCwrt = 0;
			case (IR[31:26])
				6'b000_100://beq
				begin
					if(aluZero)
						nxt_state = EX_BRA_2;
					else
						PrepareFetch;
				end
				6'b000_101://bne
				begin
					if(!aluZero)
						nxt_state = EX_BRA_2;
					else
						PrepareFetch;
				end
			endcase		
        end
		
		EX_BRA_2: begin
			SgnExt = 1;
			aluSelA = 0;
			aluSelB = 2'b11;
			aluOp = `ADD;
			PCwrt = 1;
			IorD = 1;
			setMRE = 1;
			MARwrt = 1;
			nxt_state = FETCH1;
		end
		
		EX_J: begin
			if(IR[0])
			begin
				MemtoReg = 3'b010;
				RegDst = 2'b10;
				RFwrt = 1;
				nxt_state = EX_JL;
			end
			else
			begin
				PCSrc = 1;
				PCwrt = 1;
				PrepareFetch;
			end
			
		end
		
		EX_JL: begin
			PCSrc = 1;
			PCwrt = 1;
			PrepareFetch;	
		end
		
		EX_LUI: begin
			RegDst = 0;
			MemtoReg = 3'b011;
			RFwrt = 1;
			PCwrt = 0;
			PrepareFetch;
		end
		
		EX_MFHI: begin
			RegDst = 1;
			MemtoReg = 3'b100;
			RFwrt = 1;
			PCwrt = 0;
			PrepareFetch;
		end
		
		EX_MFLO: begin
			RegDst = 1;
			MemtoReg = 3'b101;
			RFwrt = 1;
			PCwrt = 0;
			PrepareFetch;
		end
		
		EX_MULT: begin
			if(ready_mult)
			begin
				PrepareFetch;
				mult_start = 0;
			end
			else
			begin
				nxt_state = EX_MULT;
			end
		end

		EX_JR: begin
			PCSrc = 2'b10;
			PCwrt = 1;
			PrepareFetch;
		end
		
		EX_JLR1: begin
			MemtoReg = 3'b010;
			RegDst = 2'b10;
			RFwrt = 1;
			nxt_state = EX_JLR2;
		end
		
		EX_JLR2: begin
			PCSrc = 2'b10;
			PCwrt = 1;
			PrepareFetch;
		end
		
	endcase
	

   end

endmodule








//==============================================================================

module my_alu(
   input [2:0] Op,
   input [31:0] A,
   input [31:0] B,

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
         `AND : x =   A & B;
         `OR  : x =   A | B;
         `NOR : x = ~(A | B);
         `XOR : x =   A ^ B;
         default : x = 32'hxxxxxxxx;
      endcase

   assign #2 X = x;
   assign #2 Z = x == 32'h00000000;

endmodule

//==============================================================================

module reg_file(
   input clk,
   input write,
   input [4:0] WR,
   input [31:0] WD,
   input [4:0] RR1,
   input [4:0] RR2,
   output [31:0] RD1,
   output [31:0] RD2
);

   reg [31:0] rf_data [0:31];

   assign #2 RD1 = rf_data[ RR1 ];
   assign #2 RD2 = rf_data[ RR2 ];   

   always @( posedge clk ) begin
      if ( write )
         rf_data[ WR ] <= WD;

      rf_data[0] <= 32'h00000000;//we should not write on register 0
   end

endmodule

//==============================================================================

module multiplier4
(
   input clk,  
   input start,
   input [31 :0] A, 
   input [31 :0] B, 
   output [63 : 0] Out,
   output ready
    );

reg [32  :0] Multiplicand ;
reg [31:0] Multiplier;
reg [2*31 :0] Product;
integer counter;

wire sub = counter == 31; 
wire [32 :0]adder_output; 
wire [32 :0]in;
wire [32 :0]innot;

assign adder_output = innot + {Product[2*31] ,Product[2*31 : 32]} + sub;
assign in = Multiplier[0] ? Multiplicand : 0;
assign innot = sub ? ~in : in; 
assign ready = counter == 32 ;
assign Out = Product;
 

always @ (posedge clk)
   if(start) begin
      counter <= 0 ;
      Multiplier <= B;
      Product <= 0;
      Multiplicand <= {A[31], A} ;
   end

	else if(! ready) begin
         	counter <= counter + 1;
        	Multiplier <= Multiplier >> 1;
			Product <= {adder_output , Product[31:1]};
  	end   

endmodule
