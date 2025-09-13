//COMPILE: iverilog.exe -g2012 -o riscvsingle_p1.vcd -tvvp .\riscvsingle_p1.sv
//SIMULATE: vvp riscvsingle_p1

module testbench();

  logic        clk;
  logic        reset;

  logic [31:0] WriteData, DataAdr;
  logic        MemWrite;

  // instantiate device to be tested
  top dut(clk, reset, WriteData, DataAdr, MemWrite);
  
  // initialize test
  initial
    begin
      reset <= 1; # 22; reset <= 0;
    end

  // generate clock to sequence tests
  always
    begin
      clk <= 1; # 5; clk <= 0; # 5;
    end

  // check results
  always @(negedge clk)
    begin
      if(MemWrite) begin // ára entrar aqui uma instrução de store foi chamada
        /*Carregamos o valor 25 para um registrador
        	Outro registrador vai ser carregado com o valor 100 do endereço,
            sendo usado como endereço base do store
            
            então resumindo:
				Quando a instrução store for acionada o "MemWrite" vai ser ligado e 				o arquivo de teste irá monitorar se o resultado 25 foi colocado no 
                endereço 100, se não foi ocorreu algum erro
        */
        if(DataAdr === 100 & WriteData === 25) begin
          $display("Simulation succeeded");
          $stop;
        end else if (DataAdr !== 96) begin
          $display("Simulation failed");
          $stop;
        end
      end
    end
endmodule