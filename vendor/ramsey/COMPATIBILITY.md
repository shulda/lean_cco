# Lean4.34.1 Ramsey compatibility port

UPSTREAM.json records exact original commit/tree/blob provenance for all105
Lean source modules and the successor LICENSE. COMPATIBILITY.patch records
every source change from that snapshot; original namespaces and theorem
statements remain unchanged.

- Remove all15 broad Mathlib.Tactic imports. The two basic structure modules
  explicitly import Mathlib.Tactic.Ext and Mathlib.Basic.Finite.Prod.
- Use receiving Mathlib.Data.Prod.Lex instead of the newer
  Mathlib.Order.Prod.Lex.Basic in the three actual consumers.
- Import Mathlib.Data.Fintype.Option in the line-schedule consumer and
  Mathlib.SetTheory.Cardinal.Finite in the Nat.card consumer.
- Adapt one finite-variable-word length proof with Nat.lt_succ_of_lt;
  its statement and hypotheses are unchanged.

The standalone package retains receiving Lean4.34.1 and the exact nine
resolved Mathlib dependency entries. No unrestricted lake update was run.
The receiving CCO package retains its existing tenth AllThoseEPPA pin.

Native checkpoint: lake --rehash build +PartiteConstruction.Structure.Basic
+PartiteConstruction.Structure.FreeAmalgamationClass
+PartiteConstruction.Functional.WeakInvariant passed (986 jobs including
cached dependencies), log round16-b037-native-basics.log outside the repo.
This is an early native checkpoint, not final105-facade acceptance.

Complete E01 facade: lake --rehash build +CCORamsey passed,1182 jobs
including dependencies, with106 actual provider oleans (105 original modules
plus the receiving facade). Missing positive tuple notation/finite-sum and
fin_cases dependencies are now imported explicitly in their consumers:
Mathlib.Data.Fin.VecNotation, Mathlib.Basic.Finite.Sum, Mathlib.Tactic.FinCases.
No broad Mathlib or Mathlib.Tactic import remains. A final warm facade build
and separate provider source/artifact checks follow.
