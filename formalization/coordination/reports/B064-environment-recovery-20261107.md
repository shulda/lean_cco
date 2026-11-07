# B064 environment recovery — current source preserved, fresh verification required

At approximately2026-11-07T15:20Z the environment removed older transient
scratch directories during active work. The old common CCO Git object
store and runtime/shared package directory disappeared. Both root and
all live authors independently observed the missing actual paths; the
remaining cleanup staging tree was atomically rescued into the current
workspace. It retained the old axiom-audit executable/object store and some
older reports, but not the missing native B064 object history or runtime.
No source reset, force push, rebase, squash or intentional history discard
was performed. The cleanup itself is not claimed to be a project action.

## Surviving exact source and evidence

- Public PR89 head29dbd5673bb53cafc76bca4905303499ebe11937, tree
  42290422d91bb1a23765b9f5b2275105efc50473, exact successful CI42378740236,
  remains untouched, as does accepted main0c50fac628c63d5460390b698336687055675ee6.
  Canonical STATE909 retains63ACCEPTED and B064 IN_PROGRESS, with no lock.
- The current root source tree survived:142 UnfilteredEP modules/13,391lines,
  including actual normalized hidden EP, ANY-genuine-history C95 and original
  finite/infinite C104. Independent reader /root/b064_control personally
  read and bound all142 module Git blobs immediately before the loss to
  nativee458fd5c3ce1ab497836e80153924a43f31f0dc6,
  whole treeb23cdcaecb0d102be47fe3722ffe306b3aa66b4f. Its read manifest
  SHA256f14dff8b9eb4c70919533798430ad2c3fe4a4e343b1de4900a13a4fa5d2e050c
  and personally authored review notes survive.
- Local original SourceExports build4149 and complete root5344 PASS logs
  survive. These are historical compilation receipts, not validation of
  any later recovered/public head. All author maps and new strict generic
  synchronized-pair proof source also survive in the current workspace.
- The final extra normalized visible JEP module, authored after that root
  snapshot, was reconstructed verbatim from its recorded patch and checked:
  Git blobd32dbd04eb919e24050d8a4a52dfbfac0c69520c,
  SHA25654ed4f153a7bb917668be6489cd1711829d235af0a08c017260c57bc68eadaaa.
  Its original targeted4063 PASS receipt also survives. Its lost native head
  wasa87eacbb5dd017f2a35b1c9868c18db25f6f813f; no old Git object is claimed
  to exist merely because that SHA is recorded.

## Recovery without changing the mathematical contract

A new standalone Git checkout was made from the exact existing public29db
head, with its complete available public ancestry. The entire current root
source was overlaid WITHOUT deleting or reverting any current file and
excluding only .git/.lake. The before/after original source snapshot and
new checkout all have the SAME all-file SHA256
13ae0852b551b4c9a65f1dd8baf3ebcab2c583f7de90bb2ad60324d3d4dbf941:
3688files,2784Leanfiles,142UnfilteredEPmodules, all3600 public tracked paths
present, zero source mismatches or deletions. This recovery is a NEW WIP
snapshot atop the last public head. It does NOT pretend to reconstruct
irrecoverable individual private native commits. All available public
history and surviving native export/provenance records remain preserved.
All historical and current actual authors remain in canonical authorship.

Pinned Lean4.34.1 was downloaded again from its exact official release:
580432872bytes, SHA256
47bf4bbd78f70c2e9670598ab7124d92b6efb7330ff33e5fbb4030f6fd72e4e4;
lean and lake report compiler commit5045d0056413266e57c625dcd7c365b10e377c52.
The unchanged lake-manifest pins are restored by exact detached Git fetch,
not lake update. Existing physical project build outputs are seeds only;
all current-source guards, actual build and transitive audit must pass again.

There is no source/API/toolchain/provider pin change. The strict C37–C42
I10 dependency firewall correction remains a real source obligation until
its separate explicit-A04 synchronized-context theorem compiles and is
independently reviewed. B064 is not submitted/approved/accepted merely by
recovering its files. Fresh exact public CI and whole-package nonauthor
review, the sole integration lock and actual resulting-main CI remain
mandatory. The same actual reviewer identity retains its independence;
no prior approval is borrowed, renamed or inferred from saved local logs.
