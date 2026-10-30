import CCO.SimultaneousQuotients.Towers.InitialSource
import CCO.SimultaneousQuotients.Towers.Orbitals
import CCO.SimultaneousQuotients.Descent.OneSort

/-! Actual two-stage canonical quotient consumers, and zero-stage checks.
Every current-source property and safe upward exactness instance is supplied
by the proved source construction, not an abstract provider. -/

universe u v w t
namespace CCO.SimultaneousQuotients.Towers
open RawExact

variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)
variable {G : Type t} [Group G] [∀ i, MulAction G (X i)] [∀ i, Countable (X i)]
variable (H : HomogeneousSource S G) (cco : SemanticCCO.{u,v,max u v,w} S)
variable (J : ∀ i, Setoid (X i)) (E : ∀ i, NonemptyExact S i i)
variable (represents : ∀ i, evaluate S (E i).words = (J i).r)
variable (F : ∀ i, Setoid (Quotient (J i)))
variable (B : ∀ i, NonemptyExact (SimultaneousQuotients.source S H J E represents) i i)
variable (repF : ∀ i, evaluate (SimultaneousQuotients.source S H J E represents)
  (B i).words = (F i).r)

noncomputable def twoSteps : ExactTower (firstStage S H cco J E represents) :=
  .step ⟨F,B,repF⟩ (.nil _)

/-- This is literally the nested class, sent to the canonical total class
of the original point. Neither set of classes is replaced by a section. -/
theorem two_step_class (i : ι) (x : X i) :
    initialFlatten S H cco J E represents (twoSteps S H cco J E represents F B repF) i
      (Quotient.mk'' (Quotient.mk'' x : Quotient (J i))) =
    (Quotient.mk'' x : Quotient (Setoid.ker
      (initialProject S H cco J E represents (twoSteps S H cco J E represents F B repF) i))) :=
  initialFlatten_projection S H cco J E represents (twoSteps S H cco J E represents F B repF) i x

include H cco E represents B repF in
/-- An explicit initial exact presentation of the total two-stage kernel. -/
theorem two_step_exact (i : ι) :
    RigidGroupoid.Geometry.FullExact S (totalKernel (J i) (F i)).r := by
  refine ⟨initialTotalExact S H cco J E represents (twoSteps S H cco J E represents F B repF) i,?_⟩
  have h := initialTotalExact_represents S H cco J E represents
    (twoSteps S H cco J E represents F B repF) i
  apply h.trans
  funext x y
  exact propext Quotient.eq

/-- Complete actual atomic structure isomorphism, including a bijection
of every typed palette and optional colour preservation. -/
noncomputable def two_step_isomorphism :
    AtomicIso (twoSteps S H cco J E represents F B repF).finalStage.source
      (initialDirectSource S H cco J E represents (twoSteps S H cco J E represents F B repF)) :=
  initialStructureIso S H cco J E represents (twoSteps S H cco J E represents F B repF)

/-- The zero-stage projection and kernel are genuine identities. -/
theorem zero_stage (P : Stage.{u,v,t} ι G) (i : ι) :
    (ExactTower.nil P).project i = id ∧ (ExactTower.nil P).totalKernel i = ⊥ :=
  ⟨ExactTower.zero_project i,ExactTower.zero_kernel i⟩

end CCO.SimultaneousQuotients.Towers
