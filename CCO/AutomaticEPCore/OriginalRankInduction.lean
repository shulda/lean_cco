import CCO.AutomaticEPCore.QuotientOriginalSeparator
import CCO.AutomaticEPCore.IsoGateSeparation

/-! Close the ORIGINAL-diversity-rank separation induction over genuine
one-original-sort AP+homomorphic CCO sources and their actual terminal
maximal-character towers. The recursively used source is the literal
selected full-exact quotient, including finite and non-SAP quotients.
No original SAP, quotient SAP, Ramsey/EP or extra separator axiom enters. -/

universe u v w t
namespace CCO.AutomaticEPCore
open CCO.APCharacter CCO.APCharacter.Towers CCO.ExactEPGeometry
open CCO.ParityHasse.Original
noncomputable section

/-- The mathematically exact outer induction STEP. Every lower-rank
premise ranges over ALL actual one-original-sort sources in the quotient
carrier universe. The same-F case uses the proved original functional
action; the other cases use the genuine C25 old-terminal-type lift. -/
theorem original_tower_separation_from_lower_rank
    (A : CurrentSource.{u,v,w,t}) (base : A.Sorts)
    (hOne : ∀ i : A.Sorts, base = i)
    (lower :
      ∀ (Q : CurrentSource.{u,v,v,t}) (q : Q.Sorts)
        (one : ∀ j : Q.Sorts, q = j),
        originalDiversityRank Q q < originalDiversityRank A base →
          ActualTowerSeparation Q q one) :
    ActualTowerSeparation A base hOne := by
  classical
  intro next history terminal s t different
  by_cases hId : (⊥ : ExactEq A.source base) ∈
      IsoGateTower.gates A base hOne history
  · let F := leastPositiveExact A base
    by_cases hOcc : (originalExactOccupancySetoid
        A next.current next.reduct base hOne F).r s t
    · exact IsoGateTower.identity_same_occupancy_bipartite_separator
        A base hOne history hId s t different hOcc
    · have hDiff : ¬prefixSupport next.reduct
          (originalExactGlobalRelation A base hOne F) s t := hOcc
      have hPos : (⊥ : ExactEq A.source base) < F :=
        IsoGateTower.identity_gate_least_exact_positive A base hOne history hId
      let Q := originalCodedQuotient A base hOne F (CertifiedGateTower.initial A)
      have hRank : originalDiversityRank Q.current (Quotient.mk'' base) <
          originalDiversityRank A base :=
        original_initial_selected_quotient_rank_lt A base hOne F hPos
      exact actual_quotient_rank_step_original_separator A base hOne F
        history terminal s t hDiff
        (lower Q.current (Quotient.mk'' base)
          (original_initial_selected_quotient_one_sort A base hOne F) hRank)
  · obtain ⟨E,hGate,hDiff⟩ :=
      IsoGateTower.distinct_final_types_have_separating_gate
        A base hOne history s t different
    have hNe : E ≠ (⊥ : ExactEq A.source base) := by
      intro he
      exact hId (he ▸ hGate)
    have hPos : (⊥ : ExactEq A.source base) < E :=
      lt_of_le_of_ne bot_le hNe.symm
    let Q := originalCodedQuotient A base hOne E (CertifiedGateTower.initial A)
    have hRank : originalDiversityRank Q.current (Quotient.mk'' base) <
        originalDiversityRank A base :=
      original_initial_selected_quotient_rank_lt A base hOne E hPos
    exact actual_quotient_rank_step_original_separator A base hOne E
      history terminal s t hDiff
      (lower Q.current (Quotient.mk'' base)
        (original_initial_selected_quotient_one_sort A base hOne E) hRank)

/-- The strong induction is carried out FIRST in the quotient's actual
atom universe v, so every recursive selected quotient has exactly the
same source universe. Every rank, including zero, is covered. -/
theorem actual_tower_separation_same_universe
    (A : CurrentSource.{u,v,v,t}) (base : A.Sorts)
    (hOne : ∀ i : A.Sorts, base = i) :
    ActualTowerSeparation A base hOne := by
  have hStrong : ∀ n : ℕ, ∀ (B : CurrentSource.{u,v,v,t})
      (b : B.Sorts) (one : ∀ i : B.Sorts, b = i),
      originalDiversityRank B b = n → ActualTowerSeparation B b one := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro B b one hRank
      apply original_tower_separation_from_lower_rank B b one
      intro Q q qOne hLess
      have hLt : originalDiversityRank Q q < n := by
        rw [hRank] at hLess
        exact hLess
      exact ih (originalDiversityRank Q q) hLt Q q qOne rfl
  exact hStrong (originalDiversityRank A base) A base hOne rfl

/-- FULL one-original-sort source quantifiers, including arbitrary
original atom universe w and finite/non-SAP quotient cases. The
induction is no longer a caller-supplied provider hypothesis. -/
theorem actual_tower_separation
    (A : CurrentSource.{u,v,w,t}) (base : A.Sorts)
    (hOne : ∀ i : A.Sorts, base = i) :
    ActualTowerSeparation A base hOne := by
  apply original_tower_separation_from_lower_rank A base hOne
  intro Q q one _
  exact actual_tower_separation_same_universe Q q one

end
end CCO.AutomaticEPCore
