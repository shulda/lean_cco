import CCO.RigidGroupoid.Geometry.Bridge
import Mathlib.Order.Hom.Basic

/-!
# Bridge conjugation on the ORIGINAL full exact equivalence intervals

No quotient exact descent, homogeneity, parity or finiteness is used. The actual
bridge equations and exact convolution give inverse monotone maps above the
two endpoint kernels. The equivalences here remain original real relations.
-/

universe u v w
namespace CCO.RigidGroupoid.Geometry

variable {ι : Type u} {X : ι → Type v} (S : AtomicSource.{u,v,w} ι X)

@[ext] theorem Kernel.ext_setoid {i : ι} {A B : Kernel S i}
    (h : A.setoid = B.setoid) : A = B := by
  cases A
  cases B
  cases h
  rfl

theorem Kernel.ext_rel {i : ι} {A B : Kernel S i} (h : A.rel = B.rel) : A = B := by
  apply Kernel.ext_setoid S
  apply Setoid.ext
  intro x y
  exact (congrFun (congrFun h x) y).to_iff

instance kernelPartialOrder (i : ι) : PartialOrder (Kernel S i) :=
  PartialOrder.lift Kernel.setoid (fun _ _ h => Kernel.ext_setoid S h)

abbrev ExactAbove {i : ι} (A : Kernel S i) := {Z : Kernel S i // A ≤ Z}

variable {S} {i j : ι} {A : Kernel S i} {B : Kernel S j}

def conjugateKernel (C : ExactCalculus S) (R : Arrow S A B)
    (Z : Kernel S j) (hZ : B.setoid ≤ Z.setoid) : Kernel S i where
  setoid := {
    r := TRel.comp (TRel.comp R.rel Z.rel) (TRel.converse R.rel)
    iseqv := ⟨by
      intro x
      have hx : TRel.comp R.rel (TRel.converse R.rel) x x := by
        simpa only [R.source] using A.setoid.refl x
      obtain ⟨b,hxb,_⟩ := hx
      exact ⟨b,⟨b,hxb,Z.setoid.refl b⟩,hxb⟩,
      by
        rintro x y ⟨b,⟨a,hxa,hab⟩,hyb⟩
        exact ⟨a,⟨b,hyb,Z.setoid.symm hab⟩,hxa⟩,
      by
        rintro x y z ⟨b,⟨a,hxa,hab⟩,hyb⟩ ⟨d,⟨c,hyc,hcd⟩,hzd⟩
        have hbc : B.rel b c := by
          rw [← R.target]
          exact ⟨y,hyb,hyc⟩
        exact ⟨d,⟨a,hxa,Z.setoid.trans hab (Z.setoid.trans (hZ hbc) hcd)⟩,hzd⟩⟩
  }
  exact := C.comp (C.comp R.exact Z.exact) (fullExact_converse S R.exact)

theorem le_conjugateKernel (C : ExactCalculus S) (R : Arrow S A B)
    (Z : Kernel S j) (hZ : B.setoid ≤ Z.setoid) :
    A.setoid ≤ (conjugateKernel C R Z hZ).setoid := by
  intro x y hxy
  have hh : TRel.comp R.rel (TRel.converse R.rel) x y := by rwa [R.source]
  obtain ⟨b,hxb,hyb⟩ := hh
  exact ⟨b,⟨b,hxb,Z.setoid.refl b⟩,hyb⟩

def conjugate (C : ExactCalculus S) (R : Arrow S A B) (Z : ExactAbove S B) :
    ExactAbove S A :=
  ⟨conjugateKernel C R Z.val Z.property, le_conjugateKernel C R Z.val Z.property⟩

@[simp] theorem conjugate_rel (C : ExactCalculus S) (R : Arrow S A B)
    (Z : ExactAbove S B) :
    (conjugate C R Z).val.rel = TRel.comp (TRel.comp R.rel Z.val.rel) (TRel.converse R.rel) := rfl

theorem conjugate_mono (C : ExactCalculus S) (R : Arrow S A B) :
    Monotone (conjugate C R) := by
  intro Z W hZW x y
  rintro ⟨b,⟨a,hxa,hab⟩,hyb⟩
  exact ⟨b,⟨a,hxa,hZW hab⟩,hyb⟩

theorem inverse_conjugation_rel (R : Arrow S A B) (Z : Kernel S j)
    (hZ : B.setoid ≤ Z.setoid) :
    TRel.comp (TRel.comp (TRel.converse R.rel)
      (TRel.comp (TRel.comp R.rel Z.rel) (TRel.converse R.rel))) R.rel = Z.rel := by
  calc
    _ = TRel.comp (TRel.comp (TRel.comp (TRel.converse R.rel) R.rel) Z.rel)
        (TRel.comp (TRel.converse R.rel) R.rel) := by simp only [TRel.comp_assoc]
    _ = TRel.comp (TRel.comp B.rel Z.rel) B.rel := by rw [R.target]
    _ = Z.rel := by rw [B.left_absorb hZ, B.right_absorb hZ]

@[simp] theorem conjugate_inv_conjugate (C : ExactCalculus S) (R : Arrow S A B)
    (Z : ExactAbove S B) : conjugate C R.inv (conjugate C R Z) = Z := by
  apply Subtype.ext
  apply Kernel.ext_rel S
  change TRel.comp (TRel.comp (TRel.converse R.rel)
    (TRel.comp (TRel.comp R.rel Z.val.rel) (TRel.converse R.rel)))
      (TRel.converse (TRel.converse R.rel)) = Z.val.rel
  rw [TRel.converse_converse]
  exact inverse_conjugation_rel R Z.val Z.property

@[simp] theorem conjugate_conjugate_inv (C : ExactCalculus S) (R : Arrow S A B)
    (Z : ExactAbove S A) : conjugate C R (conjugate C R.inv Z) = Z := by
  have hh := conjugate_inv_conjugate C R.inv Z
  simpa only [Arrow.inv_inv] using hh

def intervalOrderIso (C : ExactCalculus S) (R : Arrow S A B) :
    ExactAbove S B ≃o ExactAbove S A where
  toFun := conjugate C R
  invFun := conjugate C R.inv
  left_inv := conjugate_inv_conjugate C R
  right_inv := conjugate_conjugate_inv C R
  map_rel_iff' := by
    intro Z W
    constructor
    · intro h
      change conjugate C R Z ≤ conjugate C R W at h
      have hh := conjugate_mono C R.inv h
      simpa only [conjugate_inv_conjugate] using hh
    · intro h
      exact conjugate_mono C R h

def baseAbove (A : Kernel S i) : ExactAbove S A := ⟨A,le_rfl⟩

@[simp] theorem conjugate_base (C : ExactCalculus S) (R : Arrow S A B) :
    conjugate C R (baseAbove B) = baseAbove A := by
  apply Subtype.ext
  apply Kernel.ext_rel S
  change TRel.comp (TRel.comp R.rel B.rel) (TRel.converse R.rel) = A.rel
  rw [R.right,R.source]

theorem conjugate_strict (C : ExactCalculus S) (R : Arrow S A B) (Z : ExactAbove S B) :
    A < (conjugate C R Z).val ↔ B < Z.val := by
  change baseAbove A < conjugate C R Z ↔ baseAbove B < Z
  rw [← conjugate_base C R]
  exact (intervalOrderIso C R).lt_iff_lt

end CCO.RigidGroupoid.Geometry
