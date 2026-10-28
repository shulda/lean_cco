import CCO.RawExact.AtomicStepTrace
import CCO.RawExact.SortTrace

/-!
# B002 C12: original sorts and atomic word letters form a true typed chain

Both lists follow the REAL named original sorts, and every link
carries the corresponding genuine typed diversity atom. Identity
letters give no positions/edges. No global source homogeneity, CCO
or quotient-sort assumption is needed.
-/

universe u v w

namespace CCO.RawExact

variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)

/-- Exact source/target type for each consecutive genuine RAW
diversity letter in a finite old-sort sequence. -/
inductive TypedAtomicChain :
    List ι → List (TypedAtomicStep S) → Prop where
  | singleton (i : ι) : TypedAtomicChain [i] []
  | step {i j : ι} (a : S.Atom i j)
      {sortTail : List ι}
      {more : List (TypedAtomicStep S)}
      (tail : TypedAtomicChain (j :: sortTail) more) :
      TypedAtomicChain
        (i :: j :: sortTail)
        ((⟨i,j,a⟩ : TypedAtomicStep S) :: more)

/-- Every RAW word has the correct original source sort first,
including a length-zero identity word. -/
theorem wordSortTrace_cons {i j : ι}
    (word : RawWord S i j) :
    ∃ rest : List ι, wordSortTrace S word = i :: rest := by
  induction word with
  | nil i => exact ⟨[], rfl⟩
  | identity tail ih =>
      simpa only [wordSortTrace] using ih
  | atom a tail ih =>
      exact ⟨wordSortTrace S tail, rfl⟩

/-- All word letters are genuinely correctly typed, and their
sort trace agrees with the vertex sort trace of every real walk. -/
theorem rawAtomicSteps_typed {i j : ι}
    (word : RawWord S i j) :
    TypedAtomicChain S
      (wordSortTrace S word)
      (rawAtomicSteps S word) := by
  induction word with
  | nil i =>
      exact TypedAtomicChain.singleton i
  | identity tail ih =>
      simpa only [wordSortTrace, rawAtomicSteps] using ih
  | atom a tail ih =>
      obtain ⟨rest, hrest⟩ := wordSortTrace_cons S tail
      rw [hrest] at ih
      simpa only [wordSortTrace, rawAtomicSteps, hrest] using
        (TypedAtomicChain.step a ih)

end CCO.RawExact
