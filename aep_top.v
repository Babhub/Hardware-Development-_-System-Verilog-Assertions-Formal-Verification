module aep_top (input clk,
                input rst,
                input [1:0] din,
                output wire [1:0] dout_full1,
                output wire [1:0] dout_full2,
                output wire [1:0] dout_full3,
                output wire [1:0] mem_out
                );

   wire [1:0]           next_state;
   wire [1:0]           next_s;
   wire                 sigA;
   wire [2:0]           sigB;
   wire [1:0]           sigC;
   wire                 sigD;
   wire                 sigE;

   wire                 sigX;

   wire                 multi_out;

   //full case
   aep_full aep_full (din,dout_full1,dout_full2,dout_full3);

   //parallel case
   reg [1:0]            din_d;
   always @(posedge clk or posedge rst)
     if (rst) din_d <= 2'b0;
     else din_d <= din;
   
   aep_parallel aep_parallel (din_d,next_state,next_s);

   //out of bounds
   assign               sigB = {din[1:0],sigC[0]};
   assign               sigC = din[0]? 2'b11: 2'b00;
   aep_bounds aep_bounds (clk,rst,din,sigB,sigC,mem_out);

   //x assignment
   aep_x aep_x (clk,rst,sigX);

   //multiple driver
   aep_multi aep_multi (din,multi_out);
   assign               sigA = multi_out & sigB[0];
   

   //floating bus
   
   aep_float aep_float (din,sigA,sigD,sigE);
   
endmodule // aep_test

module bufmod (input din,
               output dout);
   assign             dout = din;
endmodule // bufmod

   
     
     
