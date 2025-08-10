module aep_x (input clk,
              input rst,
              output reg sigX);

   always @(posedge clk or posedge rst)
     if (rst) sigX <= 1'bx;
     else
       sigX <= 1'bx;
endmodule
