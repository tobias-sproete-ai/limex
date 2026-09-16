# Independent two-line audit summary

Two separately implemented analysis lines reconstructed and classified the
available local telemetry before COO adjudication. They were not given each
other's intermediate or final result before submission.

This operational separation is not conventional double blinding. The source
corpus and research question were known, and the final adjudicator was internal
to SFH.

| Measure | Line A | Line B |
|---|---:|---:|
| Local chronology | 7,177,296,749 | 6,992,896,767 |
| Goldbach-only classification | 4,800,018,574 | 4,857,024,799 |
| Mixed classification | 527,030,352 | 368,899,295 |
| Goldbach-related upper value | 5,327,048,926 | 5,225,924,094 |
| Guardian reviews included | yes | no |
| Exact prompt boundary applied | yes | no |

The chronology difference is fully reconciled in `README.md`. The final range
preserves classification disagreement instead of averaging it.

## Bound audit outputs

```text
LINE_A_REPORT_SHA256 = b5644c9e2ba93b5ffbfae3acddd1a2bb2b21deb54f12b20256ed15371bd1098b
LINE_A_RESULT_SHA256 = 6d749f632f86107d01429c49b5c71dfd2e34619cdb6d75cd0cc5d48e4b07edfe
LINE_B_REPORT_SHA256 = c4a280af3f69e43bfb12314a33f5392c828d4aef2a4d56f5d126f5523bff9e69
LINE_B_RESULT_SHA256 = c52f25b4b347eca7d3d9066a89893fe3c1017b5a0985952bc905f2cbf493d3ff
README_AUDIT_A_SHA256 = 3b1edf3e15751e19b15a67a3f2f6b11482cd8210fb26cc7ce06814b3e5218ae1
README_AUDIT_B_SHA256 = 91df08c38a9dbb672b3cdd2defff0995f958897216d345620294f566aaebfd5a
```

The underlying audit reports remain access-controlled because their source
corpus contains private and commercially sensitive content.
