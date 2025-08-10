module aep_bounds(input clk,
                  input rst,
                  input [1:0] din,
                  input [2:0] sigB,
                  input [1:0] sigC,
                  output wire [1:0] mem_out);

   wire [1:0]            mem_out_pass;
   reg [1:0]            memA [1:0];
   integer              i;

   assign               mem_out = memA[sigB];
   assign               mem_out_pass = memA[din[0]];
   
   always @(posedge clk or posedge rst)
      if (rst) begin
        for (i=0;i<2;i=i+1) begin
           memA[i] <= 2'b0;
        end
     end else begin
       memA[din] <= sigC;
     end
endmodule
