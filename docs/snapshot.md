# Snapshot Archives

This repository supports reproducible snapshot archives capturing all runtime artefacts from a proof run.

```bash
cargo run --bin bourbaki_snapshot -- create --output snapshots
```

A `*.tar.zst` archive will be created with a `manifest.json` entry describing file hashes, RNG seed, git commit and container digest. To verify a snapshot:

```bash
cargo run --bin bourbaki_snapshot -- verify --archive snapshots/<file>.tar.zst
```

Verification recomputes each file hash and fails on any mismatch.
