# Row-70 exact test update

The candidate line is `16 → 26`, opponent `70`, response `60`.

The five unresolved children remain:

```text
34, 62, 66, 82, 98
```

## Exact negative results

- `34 → 219` is N, answered by `281`.
- `34 → 289` is N, answered by `293`.
- Every tested odd reply to child `34` through `301` is N. This is not a complete bound because the quotient position is long.
- `62 → 99` is N, answered by `38`.
- `66 → 89` is N, answered by `49`.
- `82 → 89` is N, answered by `161`.

## Latest dedicated test

A new resumable exact pass tested `98 → 83` against the preserved compact ledger.
It timed out without classifying the root, but merged `1,608,086` new outcomes with zero conflicts. The child-98 ledger now contains `7,226,001` exact states.

No P response has yet been found for any of the five remaining children.

## Honest boundary

The full row `70 → 60`, the opening strategy `16 → 26`, and `A248380(16)` remain unproved. These five quotient positions are long, so testing a few hundred odd replies is not an exhaustive search; known long Sylver positions can have very large unique winning moves.
