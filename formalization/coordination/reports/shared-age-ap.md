# Shared ordinary age-amalgamation evidence type

Both preserved WIP packages independently declared the same full name `CCO.AgeAP`.
Each declaration states ordinary amalgamation of actual finite induced substructures:
a commuting square, with no freshness or exact-intersection condition. Importing
both package declarations would collide even though the individual roots compile.

This infrastructure change extracts only that identical evidence type to
`CCO/AgeAP.lean` and imports it from the public root. The public name, universes,
field and mathematical contract are preserved. Source proofs remain in their
original package modules and are not accepted by this infrastructure PR.
The two package consumers will import the shared type and remove only their
duplicate declarations, preserving all original theorem bodies and paths.

Local validation on pinned Lean 4.34.1 / Lake 5.0.0 and pinned manifest:
full root build, 776 jobs; official transitive allowlist audit, 654 declarations;
33 actual olean output parts consistent before and after the audit. The allowed
axioms remain propext, Classical.choice and Quot.sound. A repeated cached root
build took 1.310 seconds (this does not include an audit or CI environment setup).
Feature-consumer compatibility and independent exact-head CI are separate gates.
