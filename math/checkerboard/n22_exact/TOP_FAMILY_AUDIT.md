# Complete canonical top-family manifest audits

Audit date: 2026-07-18

Source workflow run: `29534870067`

These results were independently aggregated from all eight uploaded JSONL
manifests for each top mask.  Every manifest contains exactly one closed shard
summary, no `UNKNOWN` branch, and no witness.  The union of the eight
`assigned_lefts` lists equals the complete expected left-mask family.

**Trust boundary:** these are complete search ledgers, but they are not yet
machine-checkable UNSAT proofs.  The SAT conclusions still need DRAT/LRAT or
VeriPB replay.  The dedicated top-34 CaDiCaL/DRAT workflow is intended to
replace the 82 branch-level UNSAT claims by one independently checked proof of
the unsplit top-34 CNF.

## Top mask 34

- shards: 8/8 closed;
- expected left masks: 39/39 covered exactly once;
- direct left-level UNSAT results: 38;
- right-boundary UNSAT results below the final left mask: 44;
- terminal leaf UNSAT results: 0;
- unknown branches: 0;
- total recorded solver time: 2,657.386 seconds.

Artifact ZIP SHA-256 values:

```text
1d665612cf3a62822d1821939ada90e28209f24e2a997b9417fbf8f066745384  dmono22-34-0.zip
11b91b051c47960e115d641e0f9726044e5d22798c9bcd1b83e8e68b751d0f9a  dmono22-34-1.zip
fa738ecb06e5a864b9c66896ac92be8a198696cb50ea6fd97da625d373cca866  dmono22-34-2.zip
420688ec83a05f0051a1adedc8348291e87af0c615243178e7cf589e3f8bc597  dmono22-34-3.zip
f9575b8f6f4c78f93723a770143888564de07c5930141fa1623a4f7c25b2cc9e  dmono22-34-4.zip
b8a7c61670a396404e984496176bda4ddc42b39d98cc048c9281c4ed0f874718  dmono22-34-5.zip
cc283c28d905475c09c792c338f3c5d567298028f443def39879d2c568254e5f  dmono22-34-6.zip
fa242416545a0204bda7d4af95a0bde3c597f471408bc9f389f666980dc4630f  dmono22-34-7.zip
```

## Top mask 24

- shards: 8/8 closed;
- expected left masks: 40/40 covered exactly once;
- direct left-level UNSAT results: 30;
- right-boundary UNSAT results: 432;
- terminal leaf UNSAT results: 1,096;
- symmetry-covered terminal cases: 192;
- unknown branches: 0;
- total recorded solver time: 28,077.912 seconds.

Artifact ZIP SHA-256 values:

```text
f91fe9d21b5405c097c89cdb35325c40b24108dd758fee1abce5aa83251af6c9  dmono22-24-0.zip
f14cd866ed5f5ff8496c5773684e34b65eea77aa560892dc04354dfc66901c09  dmono22-24-1.zip
99a06b1ebda9832f58334dbb39e97a0db93f92fe2fc331c44f579ba203cdd505  dmono22-24-2.zip
d9bac7c66613d7eec82ab7581f0a8527d1f6b6f04b5ec6e4bf90816878bebec4  dmono22-24-3.zip
c27dd2fb4d2ae9ea10c1c73bf70ee2ac87dea1e692606416ecdcac34154f8fdb  dmono22-24-4.zip
a761b34fcb14b091f3425457da571d44a9a69f04973ffeb279d7b107e89d5501  dmono22-24-5.zip
8cdec517bf2606cf8147d4cfcb26844ba86cb2ea59ffb9a00cb6e589529bbe39  dmono22-24-6.zip
bb8fa947a8708172a5e1926e97809d4beaa7814b61a0f51fe8b5bfeb80c68187  dmono22-24-7.zip
```

## Reproduction

After downloading and extracting the eight artifacts for a top mask:

```bash
python3 audit_shard_manifests.py 34 'double_34_*.jsonl'
python3 audit_shard_manifests.py 24 'double_24_*.jsonl'
```
