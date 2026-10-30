import CCO.RigidGroupoid.Geometry.Quotient.Algebra
import Mathlib.Data.Setoid.Basic

/-! Canonical class flattening for actual successive quotient relations.
There is no section, reverse exact descent, or literal identification of
nested classes with classes of original points. -/

namespace CCO.SimultaneousQuotients.Towers
open RawExact

variable {A B : Type*}

/-- Total pulled-back kernel on original points. -/
abbrev totalKernel (J : Setoid A) (F : Setoid (Quotient J)) : Setoid A :=
  F.comap (Quotient.mk'' : A → Quotient J)

theorem original_le_total (J : Setoid A) (F : Setoid (Quotient J)) :
    J ≤ totalKernel J F := by
  intro x y hxy
  change F (Quotient.mk'' x) (Quotient.mk'' y)
  rw [show (Quotient.mk'' x : Quotient J) = Quotient.mk'' y from Quotient.sound hxy]

/-- The nested class of [x] maps canonically to the total original class
of x. The reverse direction is definable by the quotient maps themselves. -/
def flatten (J : Setoid A) (F : Setoid (Quotient J)) :
    Quotient F ≃ Quotient (totalKernel J F) where
  toFun := Quotient.lift
    (Quotient.lift (Quotient.mk'' : A → Quotient (totalKernel J F))
      (fun _ _ h => Quotient.sound (original_le_total J F h)))
    (fun q r h => by
      induction q using Quotient.inductionOn with
      | _ x =>
        induction r using Quotient.inductionOn with
        | _ y => exact Quotient.sound h)
  invFun := Quotient.lift
    (fun x : A => Quotient.mk'' (Quotient.mk'' x : Quotient J))
    (fun _ _ h => Quotient.sound h)
  left_inv q := by
    induction q using Quotient.inductionOn with
    | _ r => induction r using Quotient.inductionOn with | _ x => rfl
  right_inv q := by
    induction q using Quotient.inductionOn with | _ x => rfl

@[simp] theorem flatten_original (J : Setoid A) (F : Setoid (Quotient J)) (x : A) :
    flatten J F (Quotient.mk'' (Quotient.mk'' x : Quotient J)) =
      (Quotient.mk'' x : Quotient (totalKernel J F)) := rfl

/-- Naturality is an equality of the two actual projection functions. -/
theorem flatten_projection (J : Setoid A) (F : Setoid (Quotient J)) :
    (flatten J F) ∘ (fun x : A => Quotient.mk'' (Quotient.mk'' x : Quotient J)) =
      (Quotient.mk'' : A → Quotient (totalKernel J F)) := rfl

/-- Saturating twice adds no information after the larger kernels have
absorbed the first ones. It applies to every old relation, including equality. -/
theorem double_saturation (J H : Setoid A) (K L : Setoid B)
    (hJ : J ≤ H) (hK : K ≤ L) (R : A → B → Prop) :
    (fun x y => ∃ b, (∃ a, H x a ∧
      (∃ d, (∃ c, J a c ∧ R c d) ∧ K d b)) ∧ L b y) =
      (fun x y => ∃ d, (∃ c, H x c ∧ R c d) ∧ L d y) := by
  funext x y
  apply propext
  constructor
  · rintro ⟨b,⟨a,hxa,⟨d,⟨c,hac,hcd⟩,hdb⟩⟩,hby⟩
    exact ⟨d,⟨c,H.trans hxa (hJ hac),hcd⟩,L.trans (hK hdb) hby⟩
  · rintro ⟨d,⟨c,hxc,hcd⟩,hdy⟩
    exact ⟨d,⟨c,hxc,⟨d,⟨c,J.refl c,hcd⟩,K.refl d⟩⟩,hdy⟩

end CCO.SimultaneousQuotients.Towers
