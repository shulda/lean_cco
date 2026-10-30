import CCO.APCharacter.PhaseWitnesses
import CCO.StabilizerSAP

/-! B047 C23--C25. A nonidentity actual self-arrow excludes an identity
real kernel in an old SAP source. This uses only old stabilizer infinitude,
not any property of a marked expansion or abstract quotient SAP. -/

universe u v w t
set_option backward.isDefEq.respectTransparency.types false
namespace CCO.PairSafeSplit.SAP
open APCharacter RigidGroupoid.Geometry
noncomputable section
variable {ι : Type u} {X : ι → Type v} (S : AtomicSource.{u,v,w} ι X)
variable {G : Type t} [Group G] [∀ i, MulAction G (X i)]
variable (H : HomogeneousSource S G)

theorem kernel_ne_identity (H : HomogeneousSource S G) (sap : AgeSAP S) {i : ι} (K : Kernel S i)
    (R : Arrow S K K) (hne : R ≠ Arrow.id K) : K.setoid ≠ ⊥ := by
  intro hK
  obtain ⟨x,y,hxy⟩ := R.exact.nonempty S
  have hneXY : x ≠ y := by
    intro he
    subst y
    exact hne (R.eq_of_common_real_pair H (Arrow.id K) hxy (K.setoid.refl x))
  let B : FiniteInduced (X := X) := ⟨{(⟨i,x⟩ : Sigma X)},Set.finite_singleton _⟩
  have hyB : (⟨i,y⟩ : Sigma X) ∉ B.vertices := by
    intro hy
    have he : (⟨i,y⟩ : Sigma X) = ⟨i,x⟩ := hy
    have he' : y=x := by simpa only [Sigma.mk.injEq,heq_eq_eq,true_and] using he
    exact hneXY he'.symm
  have hInf := RealAction.infinite_stabilizer_orbit_of_SAP S H sap B ⟨i,y⟩ hyB
  apply hInf
  apply (Set.finite_singleton (⟨i,y⟩ : Sigma X)).subset
  rintro q ⟨g,hg,hgq⟩
  have hgx : g • x = x := by
    have hh := hg (⟨i,x⟩ : Sigma X) (by exact Set.mem_singleton _)
    simpa only [Sigma.smul_mk,Sigma.mk.injEq,heq_eq_eq,true_and] using hh
  have hr : R.rel x (g • y) := by
    simpa only [hgx] using R.exact.invariant S H g x y hxy
  have he : y = g • y := by
    have hk : K.rel y (g • y) := by
      rw [← R.target]
      exact ⟨x,hxy,hr⟩
    change K.setoid y (g • y) at hk
    rw [hK] at hk
    exact hk
  have htag : g • (⟨i,y⟩ : Sigma X) = ⟨i,y⟩ :=
    congrArg (Sigma.mk i) he.symm
  exact hgq.symm.trans htag

variable {S H} {C : ExactCalculus S} {r : ι} {A : Kernel S r}

def reachedKernelEq (P : SourcePhase S H C A) (b : Reached S A) :
    ParityHasse.Original.ColourEq S b.val :=
  ⟨(Reached.kernel H C b).setoid,
    ParityHasse.Relative.Exact.colourInvariant S H (Reached.kernel H C b).exact⟩

theorem reached_kernel_ne_bot (P : SourcePhase S H C A) (sap : AgeSAP S)
    (b : Reached S A) : reachedKernelEq P b ≠ ⊥ := by
  intro he
  apply kernel_ne_identity S H sap (Reached.kernel H C b) (P.atSort b)
    (P.atSort_nonidentity b)
  exact congrArg Subtype.val he

theorem reached_kernel_gt_bot (P : SourcePhase S H C A) (sap : AgeSAP S)
    (b : Reached S A) : ⊥ < reachedKernelEq P b :=
  lt_of_le_of_ne bot_le (reached_kernel_ne_bot P sap b).symm

/-- The original whole marking, not a homogeneous-seed premise, is
constant on every whole reached real gate class. -/
theorem marking_gate_eq (P : SourcePhase S H C A) (mark : Sigma X → Bit)
    (hm : P.masks.GlobalMarking mark) (b : Reached S A) (x y : X b.val)
    (hxy : (Reached.kernel H C b).rel x y) : mark ⟨b.val,y⟩ = mark ⟨b.val,x⟩ := by
  letI := Reached.groupoid H C (A := A)
  have hh := hm.2 (⟨b.val,x⟩ : Sigma X) (⟨b.val,y⟩ : Sigma X)
  have he := hh.2.2 x y rfl b.property b.property (Arrow.id (Reached.kernel H C b)) hxy
  change mark ⟨b.val,y⟩ = mark ⟨b.val,x⟩ + P.character.value (CategoryTheory.CategoryStruct.id b) at he
  exact he.trans ((congrArg (fun z : Bit => mark ⟨b.val,x⟩ + z)
    (P.character.map_id b)).trans (add_zero _))

end
end CCO.PairSafeSplit.SAP
