# Strengthened Erdős 138 consecutive-gap theorem

This project imports the AlphaProof Nexus proof at commit
`0647711a71183c1ea492ad60860776617ce1ea88` and tests the endpoint strengthening

```text
W(k + 1) - W(k) ≥ k + 1   for k > 0.
```

The only mathematical change is allowing the greedy extension index `i = k`, which the
intersection argument appears to support.

Verification:

```bash
lake update
lake exe cache get
lake build
```

The result remains a proof candidate until the kernel build passes and prior art is audited.
