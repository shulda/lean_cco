import CCO.OldIdempotentForest.ForestAdapter
import Mathlib.Data.List.Infix
import Mathlib.Data.List.OfFn

/-! An indexed receiving adapter for a composable list of actual positive
reachable profiles.  Indices preserve every ORIGINAL occurrence even when
two letters have the same profile.  All contiguous intervals are proved
nonzero from the original SAP source, rather than a forest callback. -/

universe u v w r

namespace CCO.OldIdempotentForest

noncomputable section

variable {ι : Type u} {X : ι → Type v} (S : AtomicSource.{u,v,w} ι X)
variable {G : Type r} [Group G] [∀ i, MulAction G (X i)]
variable (H : HomogeneousSource S G) (sap : AgeSAP S)

def indexedProfileEval (letters : List (ReachableProfile S)) :
    List (Fin letters.length) → TypedProfileState S :=
  profileEval S H sap (fun k => .positive (letters.get k))

theorem indexedProfileEval_append (letters : List (ReachableProfile S))
    (left right : List (Fin letters.length)) (hl : left ≠ []) (hr : right ≠ []) :
    indexedProfileEval S H sap letters (left ++ right) =
      profileMul S H sap (indexedProfileEval S H sap letters left)
        (indexedProfileEval S H sap letters right) :=
  profileEval_append S H sap _ left right hl hr

/-- Original occurrence order reads back the literal original profile
list, without selecting representatives of equal profiles. -/
theorem finRange_map_get (letters : List (ReachableProfile S)) :
    (List.finRange letters.length).map letters.get = letters := by
  rw [← List.ofFn_eq_map]
  exact List.ofFn_get letters

theorem indexedProfileEval_eq_map (letters : List (ReachableProfile S))
    (indices : List (Fin letters.length)) :
    indexedProfileEval S H sap letters indices =
      profileEval S H sap TypedProfileState.positive (indices.map letters.get) := by
  simpa only [indexedProfileEval, Function.comp_def] using
    (profileEval_map S H sap letters.get TypedProfileState.positive indices).symm

/-- Every positive contiguous original occurrence interval remains a
genuinely composable positive list, so its value is not the mismatch zero. -/
theorem indexedProfileEval_interval_nonzero (letters : List (ReachableProfile S))
    (hcomp : letters.IsChain ReachableProfile.Compatible)
    (lo hi : ℕ) (hlo : lo < hi) (hhi : hi ≤ letters.length) :
    indexedProfileEval S H sap letters
      (((List.finRange letters.length).drop lo).take (hi-lo)) ≠ .zero := by
  rw [indexedProfileEval_eq_map, List.map_take, List.map_drop, finRange_map_get]
  exact positive_interval_nonzero S H sap letters hcomp lo hi hlo hhi

/-- The equivalent infix interface is useful for unannotated received
subtrees: infixes preserve adjacency, unlike arbitrary sublists. -/
theorem indexedProfileEval_infix_nonzero (letters : List (ReachableProfile S))
    (hcomp : letters.IsChain ReachableProfile.Compatible)
    (indices : List (Fin letters.length)) (hne : indices ≠ [])
    (hindices : indices <:+: List.finRange letters.length) :
    indexedProfileEval S H sap letters indices ≠ .zero := by
  rw [indexedProfileEval_eq_map]
  apply positive_chain_nonzero
  · intro h
    exact hne (List.map_eq_nil_iff.mp h)
  · have hmapped := hindices.map letters.get
    rw [finRange_map_get] at hmapped
    exact hcomp.infix hmapped

/-- Actual finite-semigroup forest application for a composable original
profile list, together with the locally proved nonzero interval clause.
The stronger provider bound is only weakened to the stipulated constant. -/
theorem exists_composable_forest (letters : List (ReachableProfile S))
    (hne : letters ≠ []) (hcomp : letters.IsChain ReachableProfile.Compatible) :
    letI : Semigroup (TypedProfileState S) := profileSemigroup S H sap
    ∃ t : FactorizationTree (Fin letters.length),
      t.value = List.finRange letters.length ∧
      t.IsRamsey (indexedProfileEval S H sap letters) ∧
      t.height ≤ 3 * Nat.card (TypedProfileState S) ∧
      ∀ lo hi, lo < hi → hi ≤ letters.length →
        indexedProfileEval S H sap letters
          (((List.finRange letters.length).drop lo).take (hi-lo)) ≠ .zero := by
  letI : Semigroup (TypedProfileState S) := profileSemigroup S H sap
  have hword : List.finRange letters.length ≠ [] :=
    List.length_pos_iff.mp (by simpa only [List.length_finRange] using
      (List.length_pos_iff.mpr hne))
  have hmul : ∀ left right : List (Fin letters.length), left ≠ [] → right ≠ [] →
      indexedProfileEval S H sap letters (left ++ right) =
        indexedProfileEval S H sap letters left * indexedProfileEval S H sap letters right := by
    intro left right hl hr
    exact indexedProfileEval_append S H sap letters left right hl hr
  obtain ⟨t, hyield, hramsey, hheight⟩ := CCO.FactorizationForest.classical_bound
    (indexedProfileEval S H sap letters) hmul (List.finRange letters.length) hword
  refine ⟨t, hyield, hramsey, ?_, ?_⟩
  · have hh : t.height ≤ 3 * Nat.card (TypedProfileState S) - 1 := by
      simpa only [Nat.card_eq_fintype_card] using hheight
    exact hh.trans (Nat.sub_le _ _)
  · exact indexedProfileEval_interval_nonzero S H sap letters hcomp

end
end CCO.OldIdempotentForest
