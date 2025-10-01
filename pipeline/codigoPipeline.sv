module top(input  logic        clk, reset, 
           output logic [31:0] WriteDataM, DataAdrM, 
           output logic        MemWriteM);

  logic [31:0] PCF, InstrF, ReadDataM;
  
  // instantiate processor and memories
  riscv riscv(clk, reset, PCF, InstrF, MemWriteM, DataAdrM, 
              WriteDataM, ReadDataM);
  imem imem(PCF, InstrF);
  dmem dmem(clk, MemWriteM, DataAdrM, WriteDataM, ReadDataM);
endmodule

module riscv(input  logic        clk, reset,
             output logic [31:0] PCF,
             input  logic [31:0] InstrF,
             output logic        MemWriteM,
             output logic [31:0] ALUResultM, WriteDataM,
             input  logic [31:0] ReadDataM);

  logic [6:0]  opD;
  logic [2:0]  funct3D;
  logic        funct7b5D;
  logic [1:0]  ImmSrcD;
  logic        ZeroE;
  logic        PCSrcE;
  logic [2:0]  ALUControlE;
  logic        ALUSrcE;
  logic 	   ResultSrcEb0;
  logic        RegWriteM;
  logic [1:0]  ResultSrcW;
  logic        RegWriteW;

  logic [1:0]  ForwardAE, ForwardBE;
  logic        StallF, StallD, FlushD, FlushE;

  logic [4:0] Rs1D, Rs2D, Rs1E, Rs2E, RdE, RdM, RdW;
  
  controller c(clk, reset,
               opD, funct3D, funct7b5D, ImmSrcD,
               FlushE, ZeroE, PCSrcE, ALUControlE, ALUSrcE, ResultSrcEb0,
               MemWriteM, RegWriteM, 
			   RegWriteW, ResultSrcW);

  datapath dp(clk, reset,
              StallF, PCF, InstrF,
			  opD, funct3D, funct7b5D, StallD, FlushD, ImmSrcD,
			  FlushE, ForwardAE, ForwardBE, PCSrcE, ALUControlE, ALUSrcE, ZeroE,
              MemWriteM, WriteDataM, ALUResultM, ReadDataM,
              RegWriteW, ResultSrcW,
              Rs1D, Rs2D, Rs1E, Rs2E, RdE, RdM, RdW);

  // Instancia a unidade de forwarding
  forwardingUnit fu(Rs1E, Rs2E, RdM, RdW,
                  RegWriteM, RegWriteW,
                  ForwardAE, ForwardBE);

// Instancia a unidade de detecção de hazard
  hazardUnit hu(Rs1D, Rs2D, RdE,
              ResultSrcEb0,
              PCSrcE,
              StallF, StallD, FlushD, FlushE);

endmodule


module controller(input  logic		 clk, reset,
                  // Decode stage control signals
                  input logic [6:0]  opD,
                  input logic [2:0]  funct3D,
                  input logic 	     funct7b5D,
                  output logic [1:0] ImmSrcD,
                  // Execute stage control signals
                  input logic 	     FlushE, 
                  input logic 	     ZeroE, 
                  output logic       PCSrcE,        // for datapath and Hazard Unit
                  output logic [2:0] ALUControlE, 
                  output logic 	     ALUSrcE,
                  output logic       ResultSrcEb0,  // for Hazard Unit
                  // Memory stage control signals
                  output logic 	     MemWriteM,
                  output logic       RegWriteM,     // for Hazard Unit				  
                  // Writeback stage control signals
                  output logic 	     RegWriteW,     // for datapath and Hazard Unit
                  output logic [1:0] ResultSrcW);

  // pipelined control signals
  logic 	  RegWriteD, RegWriteE;
  logic [1:0] ResultSrcD, ResultSrcE, ResultSrcM;
  logic       MemWriteD, MemWriteE;
  logic		  JumpD, JumpE;
  logic		  BranchD, BranchE;
  logic	[1:0] ALUOpD;
  logic [2:0] ALUControlD;
  logic 	  ALUSrcD;
	
  // Decode stage logic
  maindec md(opD, ResultSrcD, MemWriteD, BranchD,
             ALUSrcD, RegWriteD, JumpD, ImmSrcD, ALUOpD);
  aludec  ad(opD[5], funct3D, funct7b5D, ALUOpD, ALUControlD);
  
  // Execute stage pipeline control register and logic
  floprc #(10) controlregE(clk, reset, FlushE,
                           {RegWriteD, ResultSrcD, MemWriteD, JumpD, BranchD, ALUControlD, ALUSrcD},
                           {RegWriteE, ResultSrcE, MemWriteE, JumpE, BranchE, ALUControlE, ALUSrcE});

  assign PCSrcE = (BranchE & ZeroE) | JumpE;
  assign ResultSrcEb0 = ResultSrcE[0];
  
  // Memory stage pipeline control register
  flopr #(4) controlregM(clk, reset,
                         {RegWriteE, ResultSrcE, MemWriteE},
                         {RegWriteM, ResultSrcM, MemWriteM});
  
  // Writeback stage pipeline control register
  flopr #(3) controlregW(clk, reset,
                         {RegWriteM, ResultSrcM},
                         {RegWriteW, ResultSrcW});     
endmodule

//Unidade de detecção de Hazard
//Pseudo codigo
/*module hazardUnit(input [31:0]  ID/EX.rd,input ID/EX.MemWrite,
                  input [6:0] opcode, output [31:0] stallPC,output stallMux);

  //Quando stallMux for 0 ele envia os sinais de controle, caso contrario ele coloca 0 para os registradores
  //de controle WB,M,EX
  stallMUX = 0 
  if (ID/EX.MemWrite and ((ID/EX.r2 == IF/ID.r1) or (ID/EX.r2 == IF/ID.r2)))
    stallPC = 0
    stallMux = 1

    //Lembrar de colocar um mux de duas entradas uma entrada para  os dados do controle que vao para os registradores de controle
    // a segunda entrada será o numero 0 e o seletor do mux sera o stallMUX

endmodule
*/

module hazardUnit(input  logic [4:0] Rs1D, Rs2D, RdE,       // Entradas: Registradores
                  input  logic       ResultSrcEb0,          // Entrada: Identifica se a instr em EX é lw
                  input  logic       PCSrcE,                // Entrada: Identifica se um branch foi tomado
                  output logic       StallF, StallD, FlushD, FlushE); // Saídas de controle

  logic load_use_hazard;

  // A condição para o hazard Load-Use é:
  // 1. A instrução no estágio EX é um lw (ResultSrcE[0] é 1 para lw)
  // 2. O registrador de destino do lw (RdE) é o mesmo que um dos registradores
  //    de origem da instrução no estágio ID (Rs1D ou Rs2D). Acrescentei o RDE ser diferente de 0
  assign load_use_hazard = ResultSrcEb0 && (RdE != 5'b0) && ( (RdE == Rs1D) || (RdE == Rs2D) );

  // Gerar os sinais de stall e flush
  assign StallF = load_use_hazard;
  assign StallD = load_use_hazard;  // Inserimos uma bolha no estágio EX se houver stall
  assign FlushE = PCSrcE || StallD; //Mudança nesta parte que estava dando erro
  // Descartamos a instrução no estágio D se um branch for tomado no estágio E
  assign FlushD = PCSrcE;
endmodule
//unit forwarding
//Pseudo codigo
/*
module forwardingUnit(input [4:0] ID/EX.r1,ID/EX.r2,
                      MEM/WB.rd,
                      input MEM/WB.RegWrite, EX/MEM.RegWrite,
                      output[1:0] forwardA,forwardB);
  forwardA = 00;
  forwardB = 00;
  //Hazard EX:
    if(EX/MEM.WriteReg and (EX/MEM.rd != 0) and (EX/MEM.rd == ID/EX.r1))
      forwardA = 10
    if(EX/MEM.RegWrite and (EX/MEM.rd != 0) and (EX/MEM.rd == ID/EX.r2))
    forwardB = 10

  //Hazard MEM:
  if(MEM/WB.WriteReg and (MEM/WB.rd != 0) and (MEM/WB.rd == ID/EX.r1))
      forwardA = 01
  if(MEM/WB.WriteReg and (MEM/WB.rd != 0) and (MEM/WB.rd == ID/EX.r2))
      forwardB = 01

  //Hazard caso especial
  if ( MEM/WB.WriteReg and ( MEM/WB.rd != 0) and not (EX/MEM.WriteReg and (EX/MEM.rd != 0) and (EX/MEM.rd != ID/EX.r1)) and (MEM/WB.rd = ID/EX.r1))
    forwardA = 01
  if ( MEM/WB.RegWrite and ( MEM/WB.rd != 0) and not (EX/MEM.RegWrite and (EX/MEM.rd != 0) and (EX/MEM.rd != ID/EX.r2)) and (MEM/WB.rd = ID/EX.r2))
    forwardB = 01


endmodule
*/
module forwardingUnit(input  logic [4:0] Rs1E, Rs2E, RdM, RdW, // Entradas: Registradores nos estágios E, M, W
                      input  logic       RegWriteM, RegWriteW, // Entradas: Sinais de controle
                      output logic [1:0] ForwardAE, ForwardBE); // Saídas: Sinais de seleção para os MUXes

  always_comb begin
    // Padrão: Sem forwarding
    ForwardAE = 2'b00;
    ForwardBE = 2'b00;

    // Checa se a instrução no estágio MEM vai escrever um resultado
    // e se esse resultado é necessário como operando A ou B no estágio EX.
    if (RegWriteM && (RdM != 5'b0) && (RdM == Rs1E)) begin
      ForwardAE = 2'b10; // Encaminha o resultado da ULA (ALUResultM)
    end
    else if ( RegWriteW && (RdW != 5'b0) && (RdW == Rs1E)) begin
      ForwardAE = 2'b01;
    end
    if (RegWriteM && (RdM != 5'b0) && (RdM == Rs2E)) begin
    ForwardBE = 2'b10; // Encaminha o resultado da ULA (ALUResultM)
    end
    else if (RegWriteW && (RdW != 5'b0) && (RdW == Rs2E)) begin
      ForwardBE = 2'b01; // Encaminha o resultado final (ResultW)
    end
  end
endmodule



module maindec(input  logic [6:0] op,
               output logic [1:0] ResultSrc,
               output logic       MemWrite,
               output logic       Branch, ALUSrc,
               output logic       RegWrite, Jump,
               output logic [1:0] ImmSrc,
               output logic [1:0] ALUOp);

  logic [10:0] controls;

  assign {RegWrite, ImmSrc, ALUSrc, MemWrite,
          ResultSrc, Branch, ALUOp, Jump} = controls;

  always_comb
    case(op)
    // RegWrite_ImmSrc_ALUSrc_MemWrite_ResultSrc_Branch_ALUOp_Jump
      7'b0000011: controls = 11'b1_00_1_0_01_0_00_0; // lw
      7'b0100011: controls = 11'b0_01_1_1_00_0_00_0; // sw
      7'b0110011: controls = 11'b1_xx_0_0_00_0_10_0; // R-type 
      7'b1100011: controls = 11'b0_10_0_0_00_1_01_0; // beq
      7'b0010011: controls = 11'b1_00_1_0_00_0_10_0; // I-type ALU
      7'b1101111: controls = 11'b1_11_0_0_10_0_00_1; // jal
      7'b0000000: controls = 11'b0_00_0_0_00_0_00_0; // need valid values at reset
      default:    controls = 11'bx_xx_x_x_xx_x_xx_x; // non-implemented instruction
    endcase
endmodule

module aludec(input  logic       opb5,
              input  logic [2:0] funct3,
              input  logic       funct7b5, 
              input  logic [1:0] ALUOp,
              output logic [2:0] ALUControl);

  logic  RtypeSub;
  assign RtypeSub = funct7b5 & opb5;  // TRUE for R-type subtract instruction

  always_comb
    case(ALUOp)
      2'b00:                ALUControl = 3'b000; // addition
      2'b01:                ALUControl = 3'b001; // subtraction
      default: case(funct3) // R-type or I-type ALU
                 3'b000:  if (RtypeSub) 
                            ALUControl = 3'b001; // sub
                          else          
                            ALUControl = 3'b000; // add, addi
                 3'b010:    ALUControl = 3'b101; // slt, slti
                 3'b110:    ALUControl = 3'b011; // or, ori
                 3'b111:    ALUControl = 3'b010; // and, andi
                 default:   ALUControl = 3'bxxx; // ???
               endcase
    endcase
endmodule

module datapath(input logic clk, reset,
                // Fetch stage signals
                input  logic        StallF,
                output logic [31:0] PCF,
                input  logic [31:0] InstrF,
                // Decode stage signals
                output logic [6:0]  opD,
                output logic [2:0]	funct3D, 
                output logic        funct7b5D,
                input  logic        StallD, FlushD,
                input  logic [1:0]  ImmSrcD,
                // Execute stage signals
                input  logic        FlushE,
                input  logic [1:0]  ForwardAE, ForwardBE,
                input  logic        PCSrcE,
                input  logic [2:0]  ALUControlE,
                input  logic        ALUSrcE,
                output logic        ZeroE,
                // Memory stage signals
                input  logic        MemWriteM, 
                output logic [31:0] WriteDataM, ALUResultM,
                input  logic [31:0] ReadDataM,
                // Writeback stage signals
                input  logic        RegWriteW, 
                input  logic [1:0]  ResultSrcW,
                // Hazard Unit signals 
                output logic [4:0]  Rs1D, Rs2D, Rs1E, Rs2E,
                output logic [4:0]  RdE, RdM, RdW);

  // Fetch stage signals
  logic [31:0] PCNextF, PCPlus4F;
  // Decode stage signals
  logic [31:0] InstrD;
  logic [31:0] PCD, PCPlus4D;
  logic [31:0] RD1D, RD2D;
  logic [31:0] ImmExtD;
  logic [4:0]  RdD;
  // Execute stage signals
  logic [31:0] RD1E, RD2E;
  logic [31:0] PCE, ImmExtE;
  logic [31:0] SrcAE, SrcBE;
  logic [31:0] ALUResultE;
  logic [31:0] WriteDataE;
  logic [31:0] PCPlus4E;
  logic [31:0] PCTargetE;
  // Memory stage signals
  logic [31:0] PCPlus4M;
  // Writeback stage signals
  logic [31:0] ALUResultW;
  logic [31:0] ReadDataW;
  logic [31:0] PCPlus4W;
  logic [31:0] ResultW;

  // Fetch stage pipeline register and logic
  mux2    #(32) pcmux(PCPlus4F, PCTargetE, PCSrcE, PCNextF);
  flopenr #(32) pcreg(clk, reset, ~StallF, PCNextF, PCF);
  adder         pcadd(PCF, 32'h4, PCPlus4F);

  // Decode stage pipeline register and logic
  flopenrc #(96) regD(clk, reset, FlushD, ~StallD, 
                      {InstrF, PCF, PCPlus4F},
                      {InstrD, PCD, PCPlus4D});
  assign opD       = InstrD[6:0];
  assign funct3D   = InstrD[14:12];
  assign funct7b5D = InstrD[30];
  assign Rs1D      = InstrD[19:15];
  assign Rs2D      = InstrD[24:20];
  assign RdD       = InstrD[11:7];
	
  regfile        rf(clk, RegWriteW, Rs1D, Rs2D, RdW, ResultW, RD1D, RD2D);
  extend         ext(InstrD[31:7], ImmSrcD, ImmExtD);
 
  // Execute stage pipeline register and logic
  floprc #(175) regE(clk, reset, FlushE, 
                     {RD1D, RD2D, PCD, Rs1D, Rs2D, RdD, ImmExtD, PCPlus4D}, 
                     {RD1E, RD2E, PCE, Rs1E, Rs2E, RdE, ImmExtE, PCPlus4E});
	
  mux3   #(32)  faemux(RD1E, ResultW, ALUResultM, ForwardAE, SrcAE);
  mux3   #(32)  fbemux(RD2E, ResultW, ALUResultM, ForwardBE, WriteDataE);
  mux2   #(32)  srcbmux(WriteDataE, ImmExtE, ALUSrcE, SrcBE);
  alu           alu(SrcAE, SrcBE, ALUControlE, ALUResultE, ZeroE);
  adder         branchadd(ImmExtE, PCE, PCTargetE);

  // Memory stage pipeline register
  flopr  #(101) regM(clk, reset, 
                     {ALUResultE, WriteDataE, RdE, PCPlus4E},
                     {ALUResultM, WriteDataM, RdM, PCPlus4M});
	
  // Writeback stage pipeline register and logic
  flopr  #(101) regW(clk, reset, 
                     {ALUResultM, ReadDataM, RdM, PCPlus4M},
                     {ALUResultW, ReadDataW, RdW, PCPlus4W});
  mux3   #(32)  resultmux(ALUResultW, ReadDataW, PCPlus4W, ResultSrcW, ResultW);	
endmodule


module regfile(input  logic        clk, 
               input  logic        we3, 
               input  logic [ 4:0] a1, a2, a3, 
               input  logic [31:0] wd3, 
               output logic [31:0] rd1, rd2);

  logic [31:0] rf[31:0];

  // three ported register file
  // read two ports combinationally (A1/RD1, A2/RD2)
  // write third port on rising edge of clock (A3/WD3/WE3)
  // write occurs on falling edge of clock
  // register 0 hardwired to 0

  always_ff @(negedge clk)
    if (we3) rf[a3] <= wd3;	

  assign rd1 = (a1 != 0) ? rf[a1] : 0;
  assign rd2 = (a2 != 0) ? rf[a2] : 0;
endmodule

module adder(input  [31:0] a, b,
             output [31:0] y);

  assign y = a + b;
endmodule

module extend(input  logic [31:7] instr,
              input  logic [1:0]  immsrc,
              output logic [31:0] immext);
 
  always_comb
    case(immsrc) 
               // I-type 
      2'b00:   immext = {{20{instr[31]}}, instr[31:20]};  
               // S-type (stores)
      2'b01:   immext = {{20{instr[31]}}, instr[31:25], instr[11:7]}; 
               // B-type (branches)
      2'b10:   immext = {{20{instr[31]}}, instr[7], instr[30:25], instr[11:8], 1'b0}; 
               // J-type (jal)
      2'b11:   immext = {{12{instr[31]}}, instr[19:12], instr[20], instr[30:21], 1'b0}; 
      default: immext = 32'bx; // undefined
    endcase             
endmodule

module flopr #(parameter WIDTH = 8)
              (input  logic             clk, reset,
               input  logic [WIDTH-1:0] d, 
               output logic [WIDTH-1:0] q);

  always_ff @(posedge clk, posedge reset)
    if (reset) q <= 0;
    else       q <= d;
endmodule

module flopenr #(parameter WIDTH = 8)
                (input  logic             clk, reset, en,
                 input  logic [WIDTH-1:0] d, 
                 output logic [WIDTH-1:0] q);

  always_ff @(posedge clk, posedge reset)
    if (reset)   q <= 0;
    else if (en) q <= d;
endmodule

module flopenrc #(parameter WIDTH = 8)
                (input  logic             clk, reset, clear, en,
                 input  logic [WIDTH-1:0] d, 
                 output logic [WIDTH-1:0] q);

  always_ff @(posedge clk, posedge reset)
    if (reset)   q <= 0;
    else if (en) 
      if (clear) q <= 0;
      else       q <= d;
endmodule

module floprc #(parameter WIDTH = 8)
              (input  logic clk,
               input  logic reset,
               input  logic clear,
               input  logic [WIDTH-1:0] d, 
               output logic [WIDTH-1:0] q);

  always_ff @(posedge clk, posedge reset)
    if (reset) q <= 0;
    else       
      if (clear) q <= 0;
      else       q <= d;
endmodule

module mux2 #(parameter WIDTH = 8)
             (input  logic [WIDTH-1:0] d0, d1, 
              input  logic             s, 
              output logic [WIDTH-1:0] y);

  assign y = s ? d1 : d0; 
endmodule

module mux3 #(parameter WIDTH = 8)
             (input  logic [WIDTH-1:0] d0, d1, d2,
              input  logic [1:0]       s, 
              output logic [WIDTH-1:0] y);

  assign y = s[1] ? d2 : (s[0] ? d1 : d0); 
endmodule

module imem(input  logic [31:0] a,
            output logic [31:0] rd);

  logic [31:0] RAM[63:0];

  initial
      $readmemh("riscvtest.txt",RAM);

  assign rd = RAM[a[31:2]]; // word aligned
endmodule

module dmem(input  logic        clk, we,
            input  logic [31:0] a, wd,
            output logic [31:0] rd);

  logic [31:0] RAM[63:0];

  assign rd = RAM[a[31:2]]; // word aligned

  always_ff @(posedge clk)
    if (we) RAM[a[31:2]] <= wd;
endmodule

module alu(input  logic [31:0] a, b,
           input  logic [2:0]  alucontrol,
           output logic [31:0] result,
           output logic        zero);

  logic [31:0] condinvb, sum;
  logic        v;              // overflow
  logic        isAddSub;       // true when is add or subtract operation

  assign condinvb = alucontrol[0] ? ~b : b;
  assign sum = a + condinvb + alucontrol[0];
  assign isAddSub = ~alucontrol[2] & ~alucontrol[1] |
                    ~alucontrol[1] &  alucontrol[0];

  always_comb
    case (alucontrol)
      3'b000:  result = sum;         // add
      3'b001:  result = sum;         // subtract
      3'b010:  result = a & b;       // and
      3'b011:  result = a | b;       // or
      3'b100:  result = a ^ b;       // xor
      3'b101:  result = sum[31] ^ v; // slt
      3'b110:  result = a << b[4:0]; // sll
      3'b111:  result = a >> b[4:0]; // srl
      default: result = 32'bx;
    endcase

  assign zero = (result == 32'b0);
  assign v = ~(alucontrol[0] ^ a[31] ^ b[31]) & (a[31] ^ sum[31]) & isAddSub;
  
endmodule

