# Verified build archive for local recovery

Author/publisher: root. This changes only build tooling, not mathematics,
policy, toolchain, manifests, providers or acceptance rules.

Temporary Work environments may lose all local build outputs between turns.
The existing GitHub Actions cache speeds CI but has no supported archive
download in the connected tools. Recompiling the common accepted source in
three separate cold worktrees then repeats substantial work.

The existing Lean CI now optionally archives only the project, pinned EPPA
and vendored Ramsey build output directories AFTER its unchanged full build,
transitive standard-axiom audit and all three final complete-source guards.
The artifact also records the actual checkout commit and SHA256 values for
lean-toolchain, lake-manifest.json, lakefile.toml and CCO.lean.

Exports run on successful main pushes/manual workflow runs, and on the
dedicated work/cache-export-* validation PR only. Ordinary mathematical WIP
PRs skip export. The action is pinned to the actual upload-artifact v4 commit
ea165f8d65b6e75b540449e92b4886f43607fa02; its official action.yml inputs were
read. The artifact name is unique per run/attempt; retention is one day and
the already compressed tarball avoids a second compression pass. No source
or credential directories are included.

This archive is a compilation seed, not proof or an accepted dependency.
Recovery must identify the exact successful run/artifact and compare the
recorded pinned input hashes, inspect archive member paths before extracting
into an independently owned worktree, retain the current actual sources,
run the existing repair/rehash build and complete source/provider guards,
and obtain the usual exact-head transitive audit. A mismatched or stale
archive is repaired or rejected; no guard or audit is bypassed.

Local validation: existing Python/coordination checks and diff check. The
exact PR CI must additionally exercise archive creation/upload after the
full audit. Independent exact-head review, the sole infrastructure lock,
history-preserving expected-head merge and successful actual-main CI are
still required before integration is complete.
