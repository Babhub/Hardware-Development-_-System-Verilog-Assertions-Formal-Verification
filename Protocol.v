// protocol.v
module protocol (
    input wire clk,
    output reg sop, vld, eop,
    output reg [3:0] len
);

reg [3:0] counter = 0;

always @(posedge clk) begin
    case ($time)
        20: begin  // cycle 2
            sop <= 1;
            vld <= 1;
            len <= 5;
            counter <= 5;
            eop <= 0;
        end
        30,40,50: begin
            sop <= 0;
            vld <= 1;
            counter <= counter - 1;
            eop <= 0;
        end
        60: begin
            sop <= 0;
            vld <= 1;
            counter <= 0;
            eop <= 1;
        end
        130: begin // cycle 13
            sop <= 1;
            vld <= 1;
            len <= 1;
            counter <= 1;
            eop <= 0;
        end
        140: begin
            sop <= 0;
            vld <= 1;
            counter <= 0;
            eop <= 1;
        end
        default: begin
            sop <= 0;
            vld <= 0;
            len <= 0;
            eop <= 0;
        end
    endcase
end

endmodule
