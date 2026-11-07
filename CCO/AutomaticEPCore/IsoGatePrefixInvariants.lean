import CCO.AutomaticEPCore.IsoGateQuotientTower
import CCO.AutomaticEPCore.PrefixTransitivity
import CCO.ExactEPGeometry.CertifiedMeetTower
import CCO.ExactEPGeometry.CertifiedHistoryLabels

/-! The exact-meet, common original kernel and SAME least-F orbit
invariants survive EVERY explicit whole-source renaming in the actual
coded-tower receiving category. Splits retain the proved source duties. -/

universe u v w t
namespace CCO.AutomaticEPCore
open CCO.APCharacter.Towers CCO.ExactEPGeometry
noncomputable section

theorem named_iso_exact_meet_support {A B : CurrentSource.{u,v,w,t}}
    (I : NamedCurrentSourceIso A B) :
    ExactMeetSupport A.source B.source (namedIsoReduct I) := by
  constructor
  intro F inst i j D nonempty _
  obtain ⟨a,b,all⟩ := nonempty
  obtain ⟨x,rfl⟩ := (namedIsoReduct_point_bijective I i).2 a
  obtain ⟨y,rfl⟩ := (namedIsoReduct_point_bijective I j).2 b
  exact ⟨x,y,all⟩

theorem named_iso_original_labels {A : CurrentSource.{u,v,w,t}}
    (s : CertifiedGateTower.ExactPrefix A) {B : CurrentSource.{u,v,w,t}}
    (I : NamedCurrentSourceIso s.current B)
    (R : Sigma A.Point → Sigma A.Point → Prop)
    (labels : OriginalRelationRespectsLabels s.reduct R) :
    OriginalRelationRespectsLabels (namedIsoExactPrefix s I).reduct R := by
  intro p q related
  apply I.sorts.symm.injective
  exact labels ((namedIsoReduct I).project p) ((namedIsoReduct I).project q) related

theorem named_iso_exact_functional_transitive
    (A : CurrentSource.{u,v,w,t}) (s : CertifiedGateTower.ExactPrefix A)
    {B : CurrentSource.{u,v,w,t}} (I : NamedCurrentSourceIso s.current B)
    (base : A.Sorts) (hOne : ∀ i : A.Sorts, base = i) (E : ExactEq A.source base)
    (previous : exactFunctionalPrefixTransitive A s.current s.reduct base hOne E) :
    exactFunctionalPrefixTransitive A B (namedIsoExactPrefix s I).reduct base hOne E := by
  intro p q occupancy
  have oldOccupancy : (originalExactOccupancySetoid A s.current s.reduct
      base hOne E).r ((namedIsoReduct I).parent p) ((namedIsoReduct I).parent q) := by
    obtain ⟨x,y,related⟩ := occupancy
    exact ⟨(namedIsoReduct I).point p x,(namedIsoReduct I).point q y,related⟩
  obtain ⟨h,move⟩ := previous _ _ oldOccupancy
  refine ⟨h,?_⟩
  apply I.sorts.symm.injective
  exact (original_functional_type_perm_parent A s.current s.reduct base hOne
    B (namedIsoReduct I) h.val p).trans move

namespace IsoGateTower

variable (A : CurrentSource.{u,v,w,t}) (base : A.Sorts)
variable (hOne : ∀ i : A.Sorts, base = i)

theorem history_meet_support {s next : CertifiedGateTower.ExactPrefix A}
    (history : History Step s next)
    (initial : ExactMeetSupport A.source s.current.source s.reduct) :
    ExactMeetSupport A.source next.current.source next.reduct := by
  apply History.preserves (fun p : CertifiedGateTower.ExactPrefix A =>
    ExactMeetSupport A.source p.current.source p.reduct) _ history initial
  intro s next step previous
  cases Classical.choice step with
  | rename I =>
    exact ExactMeetSupport.compose s.reduct (namedIsoReduct I) s.transport previous
      (named_iso_exact_meet_support I)
  | split actual => exact CertifiedGateTower.step_meet_support actual previous

theorem history_original_exact_preserves_labels
    {s next : CertifiedGateTower.ExactPrefix A}
    (history : History Step s next) (E : ExactEq A.source base)
    (bound : ∀ G ∈ gates A base hOne history, E ≤ G)
    (initial : OriginalRelationRespectsLabels s.reduct
      (originalExactGlobalRelation A base hOne E)) :
    OriginalRelationRespectsLabels next.reduct
      (originalExactGlobalRelation A base hOne E) := by
  revert bound initial
  induction history with
  | nil s => exact fun _ initial => initial
  | @cons s mid next step tail ih =>
    intro bound initial
    have tailBound : ∀ G ∈ gates A base hOne tail, E ≤ G := by
      intro G hG
      apply bound G
      rw [gates_cons]
      exact List.mem_append_right _ hG
    apply ih tailBound
    cases chosen : Classical.choice step with
    | rename I => exact named_iso_original_labels s I _ initial
    | split actual =>
      apply certifiedStep_original_exact_preserves_labels A base hOne actual E _ initial
      apply bound
      simp only [gates_cons,stepGate,chosen,Option.toList_some,List.singleton_append,
        List.mem_cons,true_or]

def commonKernel {s next : CertifiedGateTower.ExactPrefix A}
    (history : History Step s next) : ExactEq A.source base :=
  originalExactGateMeet A.source base (gates A base hOne history)

theorem common_kernel_preserves_final_labels
    {next : CertifiedGateTower.ExactPrefix A}
    (history : History Step (CertifiedGateTower.initial A) next) :
    OriginalRelationRespectsLabels next.reduct
      (originalExactGlobalRelation A base hOne (commonKernel A base hOne history)) := by
  apply history_original_exact_preserves_labels A base hOne history
  · intro G hG
    exact originalExactGateMeet_le_member A.source base _ G hG
  · exact originalRelationRespectsLabels_zero A.source
      (fun i j => (hOne i).symm.trans (hOne j)) _

theorem common_kernel_support_identity
    {next : CertifiedGateTower.ExactPrefix A}
    (history : History Step (CertifiedGateTower.initial A) next)
    (p q : next.current.Sorts) :
    prefixSupport next.reduct
      (originalExactGlobalRelation A base hOne (commonKernel A base hOne history)) p q ↔ p = q := by
  constructor
  · rintro ⟨x,y,related⟩
    exact common_kernel_preserves_final_labels A base hOne history ⟨p,x⟩ ⟨q,y⟩ related
  · rintro rfl
    obtain ⟨x⟩ := next.current.source.nonemptySort p
    exact ⟨x,x,(commonKernel A base hOne history).val.val.refl _⟩

theorem least_exact_history_transitive
    (positive : (⊥ : ExactEq A.source base) < leastPositiveExact A base)
    {s next : CertifiedGateTower.ExactPrefix A}
    (history : History Step s next)
    (initial : exactFunctionalPrefixTransitive A s.current s.reduct
      base hOne (leastPositiveExact A base)) :
    exactFunctionalPrefixTransitive A next.current next.reduct
      base hOne (leastPositiveExact A base) := by
  apply History.preserves (fun p : CertifiedGateTower.ExactPrefix A =>
    exactFunctionalPrefixTransitive A p.current p.reduct
      base hOne (leastPositiveExact A base)) _ history initial
  intro s next step previous
  cases Classical.choice step with
  | rename I => exact named_iso_exact_functional_transitive A s I base hOne _ previous
  | split actual => exact least_exact_prefix_transitive_step A base hOne positive actual previous

end IsoGateTower
end
end CCO.AutomaticEPCore
