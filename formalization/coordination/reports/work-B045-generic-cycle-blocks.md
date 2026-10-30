# B045 — generic cyclic path blocks

Actual author: `/root/b046_orbital_cover/nine_colour_model/coordinate_potentials`.
This identity previously implemented the independent B046 coordinate proof;
it now contributes B045 code and cannot independently review either batch.

New branch `work/B045-cycle-blocks`, physical worktree `cco-b039`, starts at
accepted main `6a3ed6e3a485b3218b5038b38494a7de1f821241`. It preserves the complete
earlier B046 branch and its commits `d06c3cc`, `7270743`, `0861c15`. The one
remaining untracked parent Core compilation copy was archived with SHA256
inventory in `runtime/B045-cycleblocks-preserved-B046-private-copies/manifest.json`.
No accepted source, contract, toolchain or manifest changed.

## Actual proof

`CCO/CloneSAP/CCO/GenericCycleBlocks.lean` imports only the finite source API
and Mathlib graph paths. It contains no old/clone source assumption and no
provider premise. It supplies generic support for B045 C18, whose genuine
source instance is assembled by `/root/b045_clone_sap/clone_cco`.

The exact consumed API was agreed with that actual implementation author:

- `CCO.CloneSAP.CCO.WalkBlock G` has fields `first`, `last`,
  `walk : G.Walk first last`.
- `WalkBlock.prefixWalk` concatenates finitely many ordered blocks and their
  actual joining edges, with literal zero/successor equations.
- `prefix_support` locates every concatenated vertex in its original block.
  `prefix_isPath` uses the original simple-path proofs and pairwise disjoint
  entire supports, hence also handles length-zero paths correctly.
- `prefix_length` proves that each bridge contributes an actual edge, even
  when every block has length zero.
- `prefix_block_edges` and `prefix_bridge_edges` retain every original
  internal edge and connector edge.
- `cyclic_blocks G` takes n≥3, a family `Fin n → WalkBlock G`, each actual
  path proof, pairwise support-disjointness, and bridges from each block's
  last vertex to the next block's first vertex using the native `cyclicNext`.
  It constructs a genuine `G.Walk x x` with `IsCycle`, retaining every block
  edge and every cyclic bridge edge. The closing proof uses the concatenated
  path and the final real bridge; length is at least the number of blocks.

This is precisely the simple-cycle step in clone_sap PROOF_NOTES N04:
connector paths in distinct c-components may be nil, but they remain
pairwise vertex-disjoint, so expansion of a genuine quotient cycle is a
genuine original specified simple cycle. No equality-labelled CCO theorem
or assumed cycle-lifting property is introduced.

## Verification

Pinned local Lean 4.34.1 with unchanged manifest: narrow target
`lake build CCO.CloneSAP.CCO.GenericCycleBlocks` passed 990 jobs.
All unrelated dependencies were reused. No full-root build, test suite,
axiom audit, GitHub mutation or coordination transition was run by this
helper. Parent assembly and final exact-head/main CI remain required.
