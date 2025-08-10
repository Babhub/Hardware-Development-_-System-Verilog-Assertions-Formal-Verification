module aep_full (input [1:0] din,
                 output reg [1:0] dout_fail,
                 output reg [1:0] dout_pass1,
                 output reg [1:0] dout_pass2
                 );

   always @(din)
   case (din) //synopsys full_case
     0: dout_fail = 2'b00;
     1: dout_fail = 2'b01;
     2: dout_fail = 2'b10;
   endcase // case(in)

   always @(din)
   case (din) //synopsys full_case
     0: dout_pass1 = 2'b00;
     1: dout_pass1 = 2'b01;
     2: dout_pass1 = 2'b10;
     3: dout_pass1 = 2'b11;
   endcase // case(in)

   always @(din)
   case (din) //synopsys full_case
     0: dout_pass2 = 2'b00;
     1: dout_pass2 = 2'b01;
     2: dout_pass2 = 2'b10;
     default: dout_pass2 = 2'b11;
   endcase // case(in)
endmodule
