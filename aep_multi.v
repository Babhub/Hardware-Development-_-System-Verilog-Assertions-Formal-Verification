module aep_multi (input [1:0] din,
                  output wire multi_out);

   bufmod bufA (din[0],multi_out);
   bufmod bufB (din[1],multi_out);

   wire                 multi_out1;
   assign               multi_out1 = din[0]? 1'b1: 1'bz;
   assign               multi_out1 = din[1]? 1'b0: 1'bz;

   wire                 flip_enable;
   assign               flip_enable = ~din[0];
   
   wire                 multi_out_pass;
   assign               multi_out_pass = din[0]? 1'b1: 1'bz;
   assign               multi_out_pass = flip_enable? 1'b0: 1'bz;
endmodule
