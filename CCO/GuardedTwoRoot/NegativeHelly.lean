import CCO.TransitionClosure.OriginalPositiveWordHelly

/-! The separate NEGATIVE certificate branch. Its premise is an
incompatible finite family. This file is not used to construct the actual
positive common survivor of a locally vetted old source support. -/

universe u v w r
namespace CCO.GuardedTwoRoot
open CCO.TransitionClosure CCO.StrongExact
variable {ι : Type u} {X : ι → Type v} (S : AtomicSource.{u,v,w} ι X)
variable {G : Type r} [Group G] [∀ i : ι, MulAction G (X i)]
variable (H : HomogeneousSource S G) (sap : AgeSAP S)
variable (cco : SemanticCCO.{u,v,max u v,w} S)

include H sap cco in
/-- C29: incompatible positive profiles have a two-word negative
certificate, from the actual accepted old-source 2-Helly theorem. -/
theorem incompatible_positive_profiles {i j : ι} (ws : List (PositiveWord S i j))
    (hEmpty : present S ws = ∅) :
    ∃ u ∈ ws, ∃ v ∈ ws,
      PositiveWord.profile S u ∩ PositiveWord.profile S v = ∅ := by
  classical
  by_contra hNo
  have hPair : PairwiseWordProfiles S ws := by
    intro u hu v hv
    by_contra hEmptyPair
    exact hNo ⟨u,hu,v,hv,Set.not_nonempty_iff_eq_empty.mp hEmptyPair⟩
  have hCommon := original_positive_word_two_helly S H sap cco ws hPair
  rw [hEmpty] at hCommon
  exact Set.not_nonempty_empty hCommon

include H sap cco in
/-- The two incompatible words are different; no false identity edge
or empty positive word is introduced into the certificate. -/
theorem incompatible_positive_profiles_distinct {i j : ι} (ws : List (PositiveWord S i j))
    (hEmpty : present S ws = ∅) :
    ∃ u ∈ ws, ∃ v ∈ ws, u ≠ v ∧
      PositiveWord.profile S u ∩ PositiveWord.profile S v = ∅ := by
  obtain ⟨u,hu,v,hv,huv⟩ := incompatible_positive_profiles S H sap cco ws hEmpty
  refine ⟨u,hu,v,hv,?_,huv⟩
  intro he
  subst v
  have hn := PositiveWord.profile_nonempty_of_SAP S H sap u
  rw [Set.inter_self] at huv
  exact hn.ne_empty huv

include H sap cco in
/-- The same negative-only certificate for actual nonempty exact menus. -/
theorem incompatible_exact_menus {i j : ι} (menus : List (S.Menu i j))
    (hExact : ∀ A ∈ menus, Exact S A) (hEmpty : meetMenus S menus = ∅) :
    ∃ A ∈ menus, ∃ B ∈ menus, A ∩ B = ∅ := by
  classical
  by_contra hNo
  have hPair : ∀ A ∈ menus, ∀ B ∈ menus, (A ∩ B).Nonempty := by
    intro A hA B hB
    by_contra hEmptyPair
    exact hNo ⟨A,hA,B,hB,Set.not_nonempty_iff_eq_empty.mp hEmptyPair⟩
  have hCommon := original_exact_menus_two_helly S H sap cco menus hExact hPair
  rw [hEmpty] at hCommon
  exact Set.not_nonempty_empty hCommon

end CCO.GuardedTwoRoot
