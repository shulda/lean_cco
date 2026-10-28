import CCO.RealClosure.Bounds.TerminalLattice
import CCO.Selectors.NR2

/-! The fixed-original-sort numerical NR2 premise agrees with the existing
FULL original NR2 API. This is actual relative-class algebra, with no
endpoint exactness, SAP, CCO or finite-source premise. -/
universe u v w t
namespace CCO.RealClosure.Bounds
open CCO.ParityHasse.Original
variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X) {i : ι}
variable {G : Type t} [Group G] [∀ j, MulAction G (X j)]
variable (H : HomogeneousSource S G)
include H

/-- Actual index two gives the literal two-distinct-class decomposition at
every original point, using uniformity under the ORIGINAL ambient action. -/
theorem terminal_relativeIndexTwo (E F : ColourEq S i) (hEF : E ≤ F)
    (a : X i) (htwo : relativeIndex E.val F.val a = 2) :
    Selectors.RelativeIndexTwo E.val F.val := by
  refine ⟨fun _ _ h => hEF h,?_⟩
  intro x
  let Q := RelativeClass E.val F.val x
  have hcard : Nat.card Q = 2 := (relativeIndex_uniform S H E F x a).trans htwo
  obtain ⟨q₀,q₁,hne,hall⟩ := Nat.card_eq_two_iff.mp hcard
  have cover : ∀ q : Q, q = q₀ ∨ q = q₁ := by
    simpa only [Set.mem_insert_iff,Set.mem_singleton_iff] using
      (Set.eq_univ_iff_forall.mp hall)
  let qx : Q := Quotient.mk _ ⟨x,F.val.refl x⟩
  have other : ∃ qb : Q, qb ≠ qx ∧ ∀ q : Q, q = qx ∨ q = qb := by
    rcases cover qx with hx | hx
    · refine ⟨q₁,?_,?_⟩
      · intro h
        exact hne (hx.symm.trans h.symm)
      · intro q
        exact (cover q).elim (fun h => Or.inl (h.trans hx.symm)) Or.inr
    · refine ⟨q₀,?_,?_⟩
      · intro h
        exact hne (h.trans hx)
      · intro q
        exact (cover q).elim Or.inr (fun h => Or.inl (h.trans hx.symm))
  obtain ⟨qb,hbne,hcover⟩ := other
  obtain ⟨b,rfl⟩ := Quotient.exists_rep qb
  refine ⟨b.val,b.property,?_,?_⟩
  · intro h
    exact hbne (Quotient.sound (E.val.symm h))
  · intro z
    constructor
    · intro hxz
      rcases hcover (Quotient.mk _ ⟨z,hxz⟩) with h | h
      · have hh := Quotient.exact h
        exact Or.inl (E.val.symm hh)
      · have hh := Quotient.exact h
        exact Or.inr (E.val.symm hh)
    · rintro (hz | hz)
      · exact hEF hz
      · exact F.val.trans b.property (hEF hz)

/-- This consumes the EXISTING full-original NR2 predicate. No exact
sublattice or chosen quotient language replaces its quantifiers. -/
theorem sortNR2_of_originalNR2 (nr2 : Selectors.OriginalNR2 S) : SortNR2 S i := by
  intro E F hEF a htwo
  exact nr2 i E.val F.val E.property F.property (terminal_relativeIndexTwo S H E F hEF a htwo)

/-- The CCO-FREE original-NR2 headline, on ANY fixed original named sort. -/
theorem terminal_raw_word_of_originalNR2 (nr2 : Selectors.OriginalNR2 S)
    (E : ColourEq S i) :
    ∃ word : RawWord S i i, RawWord.relation S word = E.val.r :=
  terminal_one_raw_word S H (sortNR2_of_originalNR2 S H nr2) E

/-- The terminal source upgrade restores CCO (and retains the source SAP
hypothesis), AFTER the independent original-NR2 word result. -/
theorem terminal_source_of_originalNR2 (_sap : AgeSAP S)
    (cco : SemanticCCO.{u,v,max u v,w} S) (nr2 : Selectors.OriginalNR2 S) :
    (∀ E : ColourEq S i, ∃ word : RawWord S i i, RawWord.relation S word = E.val.r) ∧
    (letI := ColourEq.lattice S H (i := i); Nonempty (DistribLattice (ColourEq S i))) :=
  ⟨terminal_raw_word_of_originalNR2 S H nr2,
    ⟨terminalDistribLattice S H cco (sortNR2_of_originalNR2 S H nr2)⟩⟩

end CCO.RealClosure.Bounds
