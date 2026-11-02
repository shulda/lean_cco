import CCO.ExactEPGeometry.SelectedSortExactArrows

/-!
# B062 C83/C93: actual class transport along equivariant selected sorts

The C82 selected-source construction cannot delete intermediate RAW
sort names. It instead uses real equivariant bijections from every
all-parent quotient carrier to one selected E-occupancy carrier.

This file gives a literal equivalence of WHOLE gate-class quotient
sets under those real bijections, and proves naturality under every
complete Arrow. Neither step identifies the quotient gate with
logical identity or assumes an automorphism-group section/SAP.
The final B062 consumer uses the already constructed
originalSelectedSortRetyping and actual full selected Arrow equivalence.
-/

universe u v w t

namespace CCO.ExactEPGeometry

open RigidGroupoid.Geometry

noncomputable section

variable {ι κ : Type u} {X : ι → Type v}
variable {S : AtomicSource.{u,v,w} ι X}
variable [Fintype κ] {sigma : κ ↪ ι}
variable {G : Type t} [Group G] [∀ i : ι, MulAction G (X i)]
variable (D : SelectedRetyping (X := X) sigma (G := G))
variable (H : HomogeneousSource S G)

namespace SelectedRetyping

/-- Transport a TRUE old full-gate equivalence class by the complete
bijective retagging of its underlying point. -/
noncomputable def gateClassMap {i : ι} (K : Kernel S i) :
    K.Class → (D.transportKernel H K).Class :=
  Quotient.lift
    (fun x => (D.transportKernel H K).project (D.pointEquiv i x))
    (fun x y h => Quotient.sound (by
      change K.rel ((D.pointEquiv i).symm (D.pointEquiv i x))
        ((D.pointEquiv i).symm (D.pointEquiv i y))
      simpa only [Equiv.symm_apply_apply] using h))

/-- Conversely the actual selected full-gate class has a unique
old class obtained by the genuine inverse carrier equivalence. -/
noncomputable def gateClassMapInv {i : ι} (K : Kernel S i) :
    (D.transportKernel H K).Class → K.Class :=
  Quotient.lift
    (fun y => K.project ((D.pointEquiv i).symm y))
    (fun y z h => Quotient.sound (by
      exact h))

/-- Every real full gate K survives equivariant retagging as an
equivalent complete gate-class quotient, with no new class collapse. -/
noncomputable def gateClassEquiv {i : ι} (K : Kernel S i) :
    K.Class ≃ (D.transportKernel H K).Class where
  toFun := D.gateClassMap H K
  invFun := D.gateClassMapInv H K
  left_inv := by
    intro q
    induction q using Quotient.inductionOn with
    | _ x =>
      change K.project ((D.pointEquiv i).symm (D.pointEquiv i x)) =
        K.project x
      rw [Equiv.symm_apply_apply]
  right_inv := by
    intro q
    induction q using Quotient.inductionOn with
    | _ y =>
      change (D.transportKernel H K).project
          (D.pointEquiv i ((D.pointEquiv i).symm y)) =
        (D.transportKernel H K).project y
      rw [Equiv.apply_symm_apply]

/-- Every complete old Arrow commutes with the class equivalences
when transported to the ACTUAL selected quotient source; the
middle witnesses are not omitted in this equality. -/
theorem gateClassMap_arrow_natural
    {i j : ι} {Kp : Kernel S i} {Kq : Kernel S j}
    (R : Arrow S Kp Kq) (p : Kp.Class) :
    D.gateClassMap H Kq (R.quotientMap H p) =
      (D.transportArrow H R).quotientMap
        (selectedSortHomogeneous S sigma H)
        (D.gateClassMap H Kp p) := by
  induction p using Quotient.inductionOn with
  | _ x =>
    let y := R.pointImage H x
    have hR : R.rel x y := R.pointImage_spec H x
    have hRetag : (D.transportArrow H R).rel
        (D.pointEquiv i x) (D.pointEquiv j y) := by
      change R.rel ((D.pointEquiv i).symm (D.pointEquiv i x))
        ((D.pointEquiv j).symm (D.pointEquiv j y))
      simpa only [Equiv.symm_apply_apply] using hR
    have hQuot :=
      ((D.transportArrow H R).quotientMap_eq_iff
        (selectedSortHomogeneous S sigma H)
        (D.pointEquiv i x) (D.pointEquiv j y)).mpr hRetag
    change D.gateClassMap H Kq
        (R.quotientMap H (Kp.project x)) =
      (D.transportArrow H R).quotientMap
        (selectedSortHomogeneous S sigma H)
        (D.gateClassMap H Kp (Kp.project x))
    rw [R.quotientMap_project H x]
    change (D.transportKernel H Kq).project (D.pointEquiv j y) =
      (D.transportArrow H R).quotientMap
        (selectedSortHomogeneous S sigma H)
        ((D.transportKernel H Kp).project (D.pointEquiv i x))
    exact hQuot.symm

end SelectedRetyping

end
end CCO.ExactEPGeometry
