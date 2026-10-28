import CCO.RigidGroupoid.Geometry.RootedGroupoid

/-! C22–C23: enlargement of exact factors inside an actual rigid arrow.
The middle gate is constructed from the first enlarged factor.  Real
relations are not asserted to be functions or equal to their enlargements. -/

universe u v w t
namespace CCO.RigidGroupoid.Phase
open Geometry

variable {ι : Type u} {X : ι → Type v} (S : AtomicSource.{u,v,w} ι X)
variable {G : Type t} [Group G] [∀ i, MulAction G (X i)]
variable (H : HomogeneousSource S G) (C : ExactCalculus S)
variable {i j k : ι} {A : Kernel S i} {D : Kernel S k}

include H

theorem first_square_le {P : TRel X i j} {Q : TRel X j k}
    (hQ : FullExact S Q) (R : Arrow S A D)
    (hPQ : ∀ x z, TRel.comp P Q x z → R.rel x z) :
    ∀ x x', TRel.comp P (TRel.converse P) x x' → A.rel x x' := by
  rintro x x' ⟨y,hxy,hx'y⟩
  obtain ⟨z,hyz⟩ := hQ.serial S H y
  rw [← R.source]
  exact ⟨z,hPQ x z ⟨y,hxy,hyz⟩,hPQ x' z ⟨y,hx'y,hyz⟩⟩

/-- C22: the first bridge and hence its target gate are built from `A;P`. -/
def firstBridge {P : TRel X i j} {Q : TRel X j k}
    (hP : FullExact S P) (hQ : FullExact S Q) (R : Arrow S A D)
    (hPQ : ∀ x z, TRel.comp P Q x z → R.rel x z) : Bridge S A j where
  rel := TRel.comp A.rel P
  exact := C.comp A.exact hP
  left := by rw [← TRel.comp_assoc,A.comp_self]
  source := by
    funext x x'
    apply propext
    constructor
    · rintro ⟨y,⟨a,hxa,hay⟩,a',hx'a',ha'y⟩
      exact A.setoid.trans hxa
        (A.setoid.trans (first_square_le S H hQ R hPQ a a' ⟨y,hay,ha'y⟩)
          (A.setoid.symm hx'a'))
    · intro hxx'
      obtain ⟨y,hx'y⟩ := hP.serial S H x'
      exact ⟨y,⟨x',hxx',hx'y⟩,x',A.setoid.refl x',hx'y⟩

theorem le_firstBridge {P : TRel X i j} {Q : TRel X j k}
    (hP : FullExact S P) (hQ : FullExact S Q) (R : Arrow S A D)
    (hPQ : ∀ x z, TRel.comp P Q x z → R.rel x z) :
    ∀ x y, P x y → (firstBridge S H C hP hQ R hPQ).rel x y := by
  intro x y hxy
  exact ⟨x,A.setoid.refl x,hxy⟩

/-- C23's containing second bridge uses the CONSTRUCTED middle gate. -/
def secondArrow {P : TRel X i j} {Q : TRel X j k}
    (hP : FullExact S P) (hQ : FullExact S Q) (R : Arrow S A D)
    (hPQ : ∀ x z, TRel.comp P Q x z → R.rel x z) :
    Arrow S ((firstBridge S H C hP hQ R hPQ).targetKernel H C) D :=
  ((firstBridge S H C hP hQ R hPQ).toArrow H C).inv.comp C R

theorem le_secondArrow {P : TRel X i j} {Q : TRel X j k}
    (hP : FullExact S P) (hQ : FullExact S Q) (R : Arrow S A D)
    (hPQ : ∀ x z, TRel.comp P Q x z → R.rel x z) :
    ∀ y z, Q y z → (secondArrow S H C hP hQ R hPQ).rel y z := by
  intro y z hyz
  obtain ⟨x,hxy⟩ := hP.coserial S H y
  exact ⟨x,le_firstBridge S H C hP hQ R hPQ x y hxy,hPQ x z ⟨y,hxy,hyz⟩⟩

/-- A coserial subrelation fills a containing bridge after saturation by
that bridge's actual source gate. This is the pointwise filling argument. -/
theorem saturated_coserial_fills {B : Kernel S j} (T : Arrow S B D)
    {Q : TRel X j k} (hQ : TRel.Coserial Q)
    (hQT : ∀ y z, Q y z → T.rel y z) :
    TRel.comp B.rel Q = T.rel := by
  funext y z
  apply propext
  constructor
  · rintro ⟨y',hyy',hy'z⟩
    rw [← T.left]
    exact ⟨y',hyy',hQT y' z hy'z⟩
  · intro hyz
    obtain ⟨y',hy'z⟩ := hQ z
    have hyy' : B.rel y y' := by
      rw [← T.source]
      exact ⟨z,hyz,hQT y' z hy'z⟩
    exact ⟨y',hyy',hy'z⟩

theorem second_saturation {P : TRel X i j} {Q : TRel X j k}
    (hP : FullExact S P) (hQ : FullExact S Q) (R : Arrow S A D)
    (hPQ : ∀ x z, TRel.comp P Q x z → R.rel x z) :
    TRel.comp ((firstBridge S H C hP hQ R hPQ).targetKernel H C).rel Q =
      (secondArrow S H C hP hQ R hPQ).rel :=
  saturated_coserial_fills S H (secondArrow S H C hP hQ R hPQ)
    (hQ.coserial S H) (le_secondArrow S H C hP hQ R hPQ)

theorem enlarged_product {P : TRel X i j} {Q : TRel X j k}
    (hP : FullExact S P) (hQ : FullExact S Q) (R : Arrow S A D)
    (hPQ : ∀ x z, TRel.comp P Q x z → R.rel x z) :
    TRel.comp (firstBridge S H C hP hQ R hPQ).rel
      (secondArrow S H C hP hQ R hPQ).rel = R.rel := by
  let T := (firstBridge S H C hP hQ R hPQ).toArrow H C
  change (T.comp C (T.inv.comp C R)).rel = R.rel
  rw [← Arrow.comp_assoc,Arrow.comp_inv,Arrow.id_comp]

/-- Full C22–C23 consumer, with both actual inclusions and exact product. -/
theorem rigid_factorisation {P : TRel X i j} {Q : TRel X j k}
    (hP : FullExact S P) (hQ : FullExact S Q) (R : Arrow S A D)
    (hPQ : ∀ x z, TRel.comp P Q x z → R.rel x z) :
    ∃ R₁ : Bridge S A j, ∃ R₂ : Arrow S (R₁.targetKernel H C) D,
      (∀ x y, P x y → R₁.rel x y) ∧
      (∀ y z, Q y z → R₂.rel y z) ∧
      TRel.comp R₁.rel R₂.rel = R.rel ∧
      TRel.comp (R₁.targetKernel H C).rel Q = R₂.rel :=
  ⟨firstBridge S H C hP hQ R hPQ,secondArrow S H C hP hQ R hPQ,
    le_firstBridge S H C hP hQ R hPQ,le_secondArrow S H C hP hQ R hPQ,
    enlarged_product S H C hP hQ R hPQ,second_saturation S H C hP hQ R hPQ⟩

/-- The source input is only a bridge: its target gate is itself constructed
by the accepted bridge-kernel calculus before the factorisation is used. -/
theorem rigid_bridge_factorisation {P : TRel X i j} {Q : TRel X j k}
    (hP : FullExact S P) (hQ : FullExact S Q) (R : Bridge S A k)
    (hPQ : ∀ x z, TRel.comp P Q x z → R.rel x z) :
    ∃ R₁ : Bridge S A j,
      ∃ R₂ : Arrow S (R₁.targetKernel H C) (R.targetKernel H C),
        (∀ x y, P x y → R₁.rel x y) ∧
        (∀ y z, Q y z → R₂.rel y z) ∧
        TRel.comp R₁.rel R₂.rel = R.rel := by
  obtain ⟨R₁,R₂,hP₁,hQ₂,hprod,_⟩ :=
    rigid_factorisation S H C hP hQ (R.toArrow H C) hPQ
  exact ⟨R₁,R₂,hP₁,hQ₂,hprod⟩

/-- If the middle sort already has a reached gate from the SAME source
object, the constructed gate agrees with it by accepted path uniqueness. -/
theorem constructed_middle_gate_unique {P : TRel X i j} {Q : TRel X j k}
    (hP : FullExact S P) (hQ : FullExact S Q) (R : Arrow S A D)
    (hPQ : ∀ x z, TRel.comp P Q x z → R.rel x z) (T : Bridge S A j) :
    (firstBridge S H C hP hQ R hPQ).targetKernel H C = T.targetKernel H C :=
  bridge_targetKernel_unique S H C _ T

end CCO.RigidGroupoid.Phase
