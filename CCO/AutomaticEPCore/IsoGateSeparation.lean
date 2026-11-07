import CCO.AutomaticEPCore.IsoGatePrefixInvariants
import CCO.AutomaticEPCore.FunctionalSeparation
import CCO.AutomaticEPCore.SeparatingGate

/-! Both source reductions are valid in the ACTUAL quotient receiving
category: guarded original meet support produces a selected separating
gate, and the identity branch has a genuine original functional bipartite
separator within each least-F occupancy class. -/

universe u v w t
namespace CCO.AutomaticEPCore
open CCO.APCharacter.Towers CCO.ExactEPGeometry
open CCO.ParityHasse.Original
open CCO.RigidGroupoid.Geometry
noncomputable section

theorem original_gate_meet_support_iff
    (A B : CurrentSource.{u,v,w,t}) (P : UnaryReduct A.source B.source)
    (meetSupport : ExactMeetSupport A.source B.source P)
    (base : A.Sorts) (hOne : ∀ i : A.Sorts, base = i)
    (L : List (ExactEq A.source base)) (s t : B.Sorts) :
    prefixSupport P (originalExactGlobalRelation A base hOne
      (originalExactGateMeet A.source base L)) s t ↔
      ∀ E ∈ L, prefixSupport P (originalExactGlobalRelation A base hOne E) s t := by
  classical
  constructor
  · rintro ⟨x,y,related⟩ E hE
    exact ⟨x,y,(originalExactGateMeet_iff A.source base L _ _).mp related E hE⟩
  · intro each
    let R (f : Fin L.length) : TRel A.Point (P.parent s) (P.parent t) :=
      fun x y => originalExactGlobalRelation A base hOne (L.get f)
        ⟨P.parent s,x⟩ ⟨P.parent t,y⟩
    have exacts (f : Fin L.length) : FullExact A.source (R f) :=
      original_global_exact_full A base hOne (L.get f) (P.parent s) (P.parent t)
    have oldNonempty : ∃ x : A.Point (P.parent s),
        ∃ y : A.Point (P.parent t), ∀ f, R f x y := by
      obtain ⟨x⟩ := A.source.nonemptySort base
      refine ⟨hOne (P.parent s) ▸ x,hOne (P.parent t) ▸ x,?_⟩
      intro f
      change (L.get f)
        ((hOne (P.parent s)).symm ▸ (hOne (P.parent s) ▸ x))
        ((hOne (P.parent t)).symm ▸ (hOne (P.parent t) ▸ x))
      have hs : (hOne (P.parent s)).symm ▸ (hOne (P.parent s) ▸ x) = x := by
        cases hOne (P.parent s)
        rfl
      have ht : (hOne (P.parent t)).symm ▸ (hOne (P.parent t) ▸ x) = x := by
        cases hOne (P.parent t)
        rfl
      rw [hs,ht]
    obtain ⟨x,y,all⟩ := (fullExact_family_support_iff P meetSupport R exacts oldNonempty).mpr
      (fun f => each (L.get f) (List.get_mem L f))
    refine ⟨x,y,(originalExactGateMeet_iff A.source base L _ _).mpr ?_⟩
    intro E hE
    obtain ⟨f,hf⟩ := List.mem_iff_get.mp hE
    rw [← hf]
    exact all f

namespace IsoGateTower

variable (A : CurrentSource.{u,v,w,t}) (base : A.Sorts)
variable (hOne : ∀ i : A.Sorts, base = i)

theorem distinct_final_types_have_separating_gate
    {next : CertifiedGateTower.ExactPrefix A}
    (history : History Step (CertifiedGateTower.initial A) next)
    (s t : next.current.Sorts) (different : s ≠ t) :
    ∃ E ∈ gates A base hOne history,
      ¬prefixSupport next.reduct (originalExactGlobalRelation A base hOne E) s t := by
  classical
  by_contra none
  have each : ∀ E ∈ gates A base hOne history,
      prefixSupport next.reduct (originalExactGlobalRelation A base hOne E) s t := by
    intro E hE
    by_contra noSupport
    exact none ⟨E,hE,noSupport⟩
  apply different
  apply (common_kernel_support_identity A base hOne history s t).mp
  exact (original_gate_meet_support_iff A next.current next.reduct
    (history_meet_support A history (ExactMeetSupport.identity A.source))
    base hOne (gates A base hOne history) s t).mpr each

theorem identity_gate_least_exact_positive
    {s next : CertifiedGateTower.ExactPrefix A}
    (history : History Step s next)
    (identityGate : (⊥ : ExactEq A.source base) ∈ gates A base hOne history) :
    (⊥ : ExactEq A.source base) < leastPositiveExact A base := by
  induction history with
  | nil _ => cases identityGate
  | cons step tail ih =>
    cases chosen : Classical.choice step with
    | rename I =>
      apply ih
      simpa only [gates_cons,stepGate,chosen,Option.toList_none,List.nil_append] using identityGate
    | split actual =>
      have member : (⊥ : ExactEq A.source base) = certifiedStepOriginalGate A base hOne actual ∨
          (⊥ : ExactEq A.source base) ∈ gates A base hOne tail := by
        simpa only [gates_cons,stepGate,chosen,Option.toList_some,List.singleton_append,
          List.mem_cons] using identityGate
      rcases member with head | remaining
      · exact (certified_identity_step_least_exact A base hOne actual head.symm).1
      · exact ih remaining

theorem identity_same_occupancy_bipartite_separator
    {next : CertifiedGateTower.ExactPrefix A}
    (history : History Step (CertifiedGateTower.initial A) next)
    (identityGate : (⊥ : ExactEq A.source base) ∈ gates A base hOne history)
    (s t : next.current.Sorts) (different : s ≠ t)
    (occupancy : (originalExactOccupancySetoid A next.current next.reduct
      base hOne (leastPositiveExact A base)).r s t) :
    ∃ a : A.source.Atom base base, (atomGraph A.source a).IsBipartite ∧
      originalAtomTable A next.current next.reduct base hOne a s t := by
  apply exact_functional_occupancy_bipartite_separator A next.current next.reduct
    base hOne (leastPositiveExact A base) _ s t different occupancy
  exact least_exact_history_transitive A base hOne
    (identity_gate_least_exact_positive A base hOne history identityGate)
    history (exact_functional_prefix_transitive_initial A base hOne _)

end IsoGateTower
end
end CCO.AutomaticEPCore
