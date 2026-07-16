# Certificate status

| Claim | Status |
|---|---|
| `D_mono(17,0)=26` | exact witness + exact rational dual + CP-SAT + HiGHS |
| `D_mono(17,1)=26` | exact witness + exact rational dual + CP-SAT + HiGHS |
| `D_mono(21,0)=32` | exact witness + exact slack reduction + exact BnB proof + CP-SAT + HiGHS |
| `D_mono(21,1)=32` | exact witness + exact slack reduction + exact BnB proof + CP-SAT + HiGHS |
| Deterministic checker | standard-library-only, exact integer/rational arithmetic |
| Standard LRAT/FRAT/VeriPB proof | not claimed |
| Timed-out proof-logging runs | `NO_RESULT`, excluded from evidence |

The exact 21×21 proof trees contain 1,857 nodes/929 leaves for parity 0 and 41 nodes/21 leaves for parity 1, with denominator `100000000` for all leaf dual multipliers.
