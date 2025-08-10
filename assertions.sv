module assertions (
    input logic clk,
    input logic rst_n,

    input logic req,
    input logic gnt,
    input logic hitcnt,
    input logic [270:0] index,
    input logic index_w,
    input logic req_32,
    input logic strb,
    input logic o1, o2, o3,
    input logic be_n,
    input logic fail_n,
    input logic abort_n,
    input logic [1:0] st,
    input logic [31:0] addr,
    input logic [31:0] data,
    input logic start,
    input logic end_
);

    // 1. There could be maximum 2 requests within 10 cycles
    property max_two_reqs_in_10;
        @(posedge clk)
        disable iff (!rst_n)
        (req[*0:$]) |=> ($countones({req, req[*1:9]}) <= 2);
    endproperty
    assert property (max_two_reqs_in_10);

    // 2. There should be minimum 2 requests within 10 cycles
    property min_two_reqs_in_10;
        @(posedge clk)
        disable iff (!rst_n)
        req |-> (##0 req[*1:9]) ##1 ($countones({req, req[*1:9]}) >= 2);
    endproperty
    assert property (min_two_reqs_in_10);

    // 3. After 3 requests, grant should assert within 3 cycles
    property gnt_after_3_reqs_in_3;
        int count = 0;
        @(posedge clk)
        disable iff (!rst_n)
        (req, count = count + 1) |-> (count == 3) ##[1:3] gnt;
    endproperty
    // Alternative:
    // Add FSM outside this block to count reqs and then use:
    // assert property (req_count_3 |-> ##[1:3] gnt);

    // 4. No new request until grant occurs
    property no_req_until_gnt;
        @(posedge clk)
        disable iff (!rst_n)
        req |-> !req [*1:$] until_with gnt;
    endproperty
    assert property (no_req_until_gnt);

    // 5. hitcnt can be asserted only when index[270] is 1 and index[269] is 0 and index_w is 1
    property hitcnt_condition;
        @(posedge clk)
        disable iff (!rst_n)
        hitcnt |-> (index[270] && !index[269] && index_w);
    endproperty
    assert property (hitcnt_condition);

    // 6. when req_32 is asserted for only one cycle, it should not generate another req until strb or 10 cycles later
    property req32_condition;
        @(posedge clk)
        disable iff (!rst_n)
        (req_32 && !req_32[1]) |-> (!req until (strb or ##10 req));
    endproperty
    assert property (req32_condition);

    // 7. when out of reset, outputs must not be X or Z at rising clk
    property valid_outputs_on_reset;
        @(posedge clk)
        disable iff (!rst_n)
        !$isunknown(o1) && !$isunknown(o2) && !$isunknown(o3);
    endproperty
    assert property (valid_outputs_on_reset);

    // 8. After be_n is low, addr is held until !fail_n or !abort_n
    property addr_held_after_be;
        logic [31:0] saved_addr;
        @(posedge clk)
        disable iff (!rst_n)
        be_n == 0 |-> (saved_addr = addr) ##1
        (addr == saved_addr)[*] until (fail_n == 0 || abort_n == 0);
    endproperty
    assert property (addr_held_after_be);

    // 9. For write transfers, data is held stable during wait states
    property stable_data_in_wait;
        logic [31:0] saved_data;
        @(posedge clk)
        disable iff (!rst_n)
        (st inside {2'b10, 2'b11}) |-> (saved_data = data) ##1
        (data == saved_data)[*] while (st inside {2'b10, 2'b11});
    endproperty
    assert property (stable_data_in_wait);

    // 10. For every start pulse, there should be an end pulse
    property start_end_pair;
        @(posedge clk)
        disable iff (!rst_n)
        start |-> ##[1:$] end_;
    endproperty
    assert property (start_end_pair);

endmodule
