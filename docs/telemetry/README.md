# LIMEX workflow telemetry

This directory binds selected presentation-video candidates to exact file
digests and decoded-frame timecode ranges.

The receipt in `receipts/RECEIPT_LIMEX_V3_6_SOCIAL_VIDEO_TIMECODES.json`
records four contiguous, half-open frame intervals covering the complete
46-second timeline at 30 frames per second. Each phase digest was measured over
the decoded `yuv420p` video bytes in display order with FFmpeg 8.1.2.

The phase hash procedure is:

```sh
ffmpeg -v error -i INPUT.mp4 -map 0:v:0 \
  -vf "select='gte(n,START_FRAME)*lt(n,END_FRAME)'" \
  -fps_mode passthrough -pix_fmt yuv420p -f rawvideo - \
  | shasum -a 256
```

These hashes are tamper-evident identity measurements. They make later byte or
decoded-frame-range changes detectable when compared with the bound preimages.
They do not prove authorship, semantic truth, platform publication, formal
correctness, or universal runtime behavior.

The additive agentic-trace receipt binds this downstream video receipt while
recording that no contemporaneous upstream inference trace exists for V3.6.
It therefore specifies the pre-action evidence required for a future causal audit
without retroactively claiming that an LLM rather than a static script caused it.
