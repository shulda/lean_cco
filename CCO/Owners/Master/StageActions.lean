import CCO.Owners.Master.Diagram
import CCO.Owners.Master.LargestCoverAction
import CCO.Owners.Provider.Induced
import Mathlib.Algebra.Group.Action.End

/-! Honest full automorphism maps in a finite owner stage, followed by
largest-cover descent to every nested pair. -/

namespace CCO.Owners.Master.Diagram.Stage

variable {P G : Type*} [DecidableEq P] [Group G]
variable {A : Ambient P} {Valid : Finset P → Prop} {U : Finset P}
variable [∀ V, MulAction G (A.X V)]
variable (B : Stage A Valid U)

abbrev FullAut (V : Finset P) :=
  Product.OrbitalAut G (A.X V) (Subtype.val : B.Point V → A.X V)

variable (equivA : ∀ {V W : Finset P} (h : W ⊆ V) (g : G) (x : A.X V),
  A.r h (g • x) = g • A.r h x)

/-- Equality kernels and every target pair orbital are preserved by the
actual ambient equivariant projection. No imaginary automorphism is lifted. -/
def quotient {V W} (hV : Valid V) (hW : Valid W)
    (hVU : V ⊆ U) (hWV : W ⊆ V) :
    Product.OrbitalQuotient (G := G)
      (Subtype.val : B.Point V → A.X V) (Subtype.val : B.Point W → A.X W) where
  ambient := A.r hWV
  equivariant := equivA hWV
  projection := B.r hV hW hVU hWV
  surjective := B.r_surjective hV hW hVU hWV
  target_injective := Subtype.val_injective
  commutes _ := rfl

noncomputable def action {V W} (hV : Valid V) (hW : Valid W)
    (hVU : V ⊆ U) (hWV : W ⊆ V) : B.FullAut (G := G) V →* B.FullAut (G := G) W :=
  (B.quotient equivA hV hW hVU hWV).action

@[simp] theorem action_projection {V W} (hV : Valid V) (hW : Valid W)
    (hVU : V ⊆ U) (hWV : W ⊆ V) (g : B.FullAut (G := G) V) (x : B.Point V) :
    (B.action equivA hV hW hVU hWV g).val (B.r hV hW hVU hWV x) =
      B.r hV hW hVU hWV (g.val x) :=
  (B.quotient equivA hV hW hVU hWV).action_projection g x

@[simp] theorem action_self {V} (hV : Valid V) (hVU : V ⊆ U) :
    B.action equivA hV hV hVU (Finset.Subset.refl V) = MonoidHom.id (B.FullAut (G := G) V) := by
  apply MonoidHom.ext
  intro g
  apply Subtype.ext
  apply Equiv.ext
  intro x
  change (B.action equivA hV hV hVU (Finset.Subset.refl V) g).val x = g.val x
  have h := B.action_projection equivA hV hV hVU (Finset.Subset.refl V) g x
  simpa only [r_self] using h

theorem action_comp_apply {V W T} (hV : Valid V) (hW : Valid W) (hT : Valid T)
    (hVU : V ⊆ U) (hWV : W ⊆ V) (hTW : T ⊆ W) (g : B.FullAut (G := G) V) :
    B.action equivA hW hT (hWV.trans hVU) hTW
      (B.action equivA hV hW hVU hWV g) =
        B.action equivA hV hT hVU (hTW.trans hWV) g := by
  apply Subtype.ext
  apply Equiv.ext
  intro y
  obtain ⟨x, rfl⟩ := B.r_surjective hV hT hVU (hTW.trans hWV) y
  have hleft :
      (B.action equivA hW hT (hWV.trans hVU) hTW
        (B.action equivA hV hW hVU hWV g)).val
          (B.r hV hT hVU (hTW.trans hWV) x) =
            B.r hV hT hVU (hTW.trans hWV) (g.val x) := by
    rw [← B.r_comp hV hW hT hVU hWV hTW x]
    rw [action_projection, action_projection, r_comp]
  exact hleft.trans (B.action_projection equivA hV hT hVU (hTW.trans hWV) g x).symm

theorem action_comp {V W T} (hV : Valid V) (hW : Valid W) (hT : Valid T)
    (hVU : V ⊆ U) (hWV : W ⊆ V) (hTW : T ⊆ W) :
    (B.action equivA hW hT (hWV.trans hVU) hTW).comp
      (B.action equivA hV hW hVU hWV) =
        B.action equivA hV hT hVU (hTW.trans hWV) := by
  apply MonoidHom.ext
  exact B.action_comp_apply equivA hV hW hT hVU hWV hTW

/-- Once M3 is known for maps out of the largest object, it follows for
ALL nested pairs through the genuine coherent full-group maps. -/
theorem nested_M3_of_largest (hU : Valid U)
    (largest : ∀ (V : Finset P) (hV : Valid V) (hVU : V ⊆ U),
      Function.Surjective (B.action equivA hU hV (Finset.Subset.refl U) hVU) ∧
        GroupActions.FibreTransitive (B.action equivA hU hV (Finset.Subset.refl U) hVU)
          (B.r hU hV (Finset.Subset.refl U) hVU))
    {V W} (hV : Valid V) (hW : Valid W) (hVU : V ⊆ U) (hWV : W ⊆ V) :
    Function.Surjective (B.action equivA hV hW hVU hWV) ∧
      GroupActions.FibreTransitive (B.action equivA hV hW hVU hWV)
        (B.r hV hW hVU hWV) := by
  have hUW := largest W hW (hWV.trans hVU)
  apply largest_cover_action
    (B.action equivA hU hV (Finset.Subset.refl U) hVU)
    (B.action equivA hV hW hVU hWV)
    (B.action equivA hU hW (Finset.Subset.refl U) (hWV.trans hVU))
    (fun g => B.action_comp_apply equivA hU hV hW (Finset.Subset.refl U) hVU hWV g)
    (B.r hU hV (Finset.Subset.refl U) hVU) (B.r hV hW hVU hWV)
    (B.r_surjective hU hV (Finset.Subset.refl U) hVU)
  · intro g x
    exact (B.action_projection equivA hU hV (Finset.Subset.refl U) hVU g x).symm
  · exact hUW.1
  · simpa only [GroupActions.FibreTransitive, Function.comp_apply, r_comp] using hUW.2

end CCO.Owners.Master.Diagram.Stage
