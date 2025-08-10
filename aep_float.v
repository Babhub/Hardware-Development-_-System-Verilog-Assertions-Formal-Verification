module aep_float (input [1:0] din,
                  input sigA,
                  output wire sigD,
                  output wire sigE);
   wire                  sigF;
   assign                sigF = 1'bz;
   assign sigD = din[0]? sigA:1'bz;
   assign sigE = din[1]? sigA:sigF;
endmodule
