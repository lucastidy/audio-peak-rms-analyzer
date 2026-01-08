module skid_buffer #(
  parameter int DATA_W = 32
) (
  input  logic                 clk,
  input  logic                 rst_n,

  // Upstream (slave side)
  input  logic                 s_valid,
  output logic                 s_ready,
  input  logic [DATA_W-1:0]    s_data,
  input  logic                 s_last,

  // Downstream (master side)
  output logic                 m_valid,
  input  logic                 m_ready,
  output logic [DATA_W-1:0]    m_data,
  output logic                 m_last
);

  // 1-deep skid storage
  logic                have_skid;
  logic [DATA_W-1:0]   skid_data;
  logic                skid_last;

  // When skid is full, we must stop accepting from upstream.
  // Otherwise, we can accept if downstream can take it or if we're empty.
  // Classic elastic behavior: accept if not full AND (downstream ready OR we're going to buffer).
  // In practice for 1-deep, s_ready is simply: !have_skid && (m_ready || !m_valid) but we compute cleanly below.

  // Output mux: if we have buffered data, present that; else present input.
  always_comb begin
    if (have_skid) begin
      m_valid = 1'b1;
      m_data  = skid_data;
      m_last  = skid_last;
    end else begin
      m_valid = s_valid;
      m_data  = s_data;
      m_last  = s_last;
    end
  end

  // Upstream ready:
  // If we already buffered something, we can't accept more (1-deep).
  // If no skid, we can accept when either downstream is ready (consume same cycle) OR s_valid is 0 (no transfer anyway).
  // A safe/simple form: s_ready = !have_skid && m_ready;
  // BUT that throttles unnecessarily when s_valid=0. That’s fine but annoying.
  // Better: allow "ready" when buffer empty and either downstream ready OR we won't be asserting m_valid (because s_valid=0).
  always_comb begin
    if (have_skid) s_ready = 1'b0;
    else           s_ready = (m_ready || !s_valid);
  end

  // Sequential control:
  // - If no skid and input valid but downstream not ready, capture into skid (so output holds stable next cycles).
  // - If skid is present and downstream ready, skid is consumed (clear it).
  always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
      have_skid <= 1'b0;
      skid_data <= '0;
      skid_last <= 1'b0;
    end else begin
      // Consume skid if present and accepted
      if (have_skid && m_ready) begin
        have_skid <= 1'b0;
      end

      // Capture skid if needed: only when we are NOT already holding skid,
      // upstream is presenting valid, and downstream can't accept this cycle.
      if (!have_skid && s_valid && !m_ready) begin
        have_skid <= 1'b1;
        skid_data <= s_data;
        skid_last <= s_last;
      end
    end
  end

endmodule


// // peak_rms_core.sv
// // computes per-frame peak and RMS values from AXI-Stream input.
// // Exposes peak/rms results and flags threshold exceeding events.

//  peak_rms_core #(parameter DATA_WIDTH = 16)(
//     input logic clk,
//     input logic rst_n,
//     input logic signed [DATA_WIDTH-1:0] tdata,
//     input logic tvalid,
//     input logic tlast,
//     output logic tready,
//     input logic signed [DATA_WIDTH-1:0] threshold_peak,
//     input logic signed [DATA_WIDTH-1:0] threshold_rms,
//     output logic signed [DATA_WIDTH-1:0] peak_val,
//     output logic signed [DATA_WIDTH-1:0] rms_val,
//     output logic peak_exceeded,
//     output logic rms_exceeded
// );

//     // accumulators and counters
//     logic signed [DATA_WIDTH-1:0] peak_accum;
//     logic [2*DATA_WIDTH-1:0] square_accum;
//     logic [$clog2(65536):0] sample_count;   


//     // output driving regs
//     logic signed [DATA_WIDTH-1:0] peak_reg;
//     logic signed [DATA_WIDTH-1:0] rms_reg;

//     assign peak_val = peak_reg;
//     assign rms_val = rms_reg;

//     assign tready = 1'b1;

//     always_ff @(posedge clk) begin
//         if (!rst_n) begin
//             peak_accum <= '0;
//             square_accum <= '0;
//             sample_count <= '0;
//             peak_reg <= '0;
//             rms_reg <= '0;
//             peak_exceeded <= 1'b0;
//             rms_exceeded <= 1'b0;
//         end else if (tvalid && tready) begin
//             logic [DATA_WIDTH-1:0] abs_samp;

//             abs_samp = (tdata < 0) ? -tdata : tdata; // get abs of sample
//             if ($signed(abs_samp) > $signed(peak_reg)) begin
//                 abs_samp = $signed(abs_samp); // update peak if larger
//                 peak_exceeded <= (abs_samp > threshold_peak);
//                 peak_reg <= abs_samp;
//             end
//             // accumulate square for RMS
//             square_accum <= square_accum + $signed(tdata * tdata);
//             sample_count <= sample_count + 1;
//             if (tlast) begin
//                 // end of frame, compute RMS and reset accumulators
//                 logic [DATA_WIDTH-1:0] rms_temp;
//                 rms_temp = $signed($sqrt(square_accum / sample_count));
//                 rms_reg <= rms_temp;
//                 rms_exceeded <= (rms_temp > threshold_rms);
//                 // reset accumulators for next frame
//                 square_accum <= '0;
//                 peak_accum <= '0;
//                 sample_count <= '0;
//             end
//         end
//     end

