import CCO.SimultaneousQuotients.Towers.Flattening
import CCO.RigidGroupoid.Geometry.Quotient.Calculus

/-! Safe upward exactness for the total original kernel of a current
exact quotient step. This file never imports one-sort reverse descent. -/

universe u v w t
namespace CCO.SimultaneousQuotients.Towers
open RawExact

variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)
variable {G : Type t} [Group G] [∀ i, MulAction G (X i)]
variable (H : HomogeneousSource S G) (cco : SemanticCCO.{u,v,max u v,w} S)
variable (J : ∀ i, Setoid (X i)) (E : ∀ i, NonemptyExact S i i)
variable (represents : ∀ i, evaluate S (E i).words = (J i).r)
variable (F : ∀ i, Setoid (Quotient (J i)))
variable (B : ∀ i, NonemptyExact (ExactCRT.CanonicalTyped.source S H J E represents) i i)
variable (repF : ∀ i, evaluate (ExactCRT.CanonicalTyped.source S H J E represents)
  (B i).words = (F i).r)

/-- C43: an explicit original exact presentation of the total kernel.
The only direction used is the already proved quotient-to-old pullback. -/
noncomputable def totalExact (i : ι) : NonemptyExact S i i :=
  ExactCRT.CanonicalTyped.exactPullback S H J E represents cco (B i)

include repF in
theorem totalExact_represents (i : ι) :
    evaluate S (totalExact S H cco J E represents B i).words = (totalKernel (J i) (F i)).r := by
  rw [totalExact,ExactCRT.CanonicalTyped.exactPullback_relation,repF i]
  rfl

include cco repF in
/-- Exactness of current-stage kernels supplies original-group invariance
of their full pulled-back equivalences. -/
theorem total_invariant (i : ι) :
    RawExact.CanonicalQuotients.Invariant G (totalKernel (J i) (F i)) := by
  refine ⟨?_⟩
  intro g x y hxy
  rw [←totalExact_represents S H cco J E represents F B repF i] at hxy ⊢
  exact presentation_invariant_of_homogeneous S H
    (totalExact S H cco J E represents B i).words g x y hxy

include cco repF in
/-- The source's total initial kernels are genuine full exact equivalences
and contain their previous kernels, for every named sort independently. -/
theorem total_kernel_data (i : ι) :
    J i ≤ totalKernel (J i) (F i) ∧
      RigidGroupoid.Geometry.FullExact S (totalKernel (J i) (F i)).r := by
  exact ⟨original_le_total (J i) (F i),
    ⟨totalExact S H cco J E represents B i,
      totalExact_represents S H cco J E represents F B repF i⟩⟩

end CCO.SimultaneousQuotients.Towers
