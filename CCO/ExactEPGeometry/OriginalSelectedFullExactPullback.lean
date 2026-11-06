import CCO.ExactEPGeometry.SelectedSortRawInclusion
import CCO.ExactEPGeometry.OriginalOccupancyQuotientSource
import CCO.ExactCRT.CanonicalTypedQuotients
import CCO.RigidGroupoid.Geometry.Bridge

/-!
# B062 C103: real FULL selected-quotient bridges pull back to current bridges

First include every selected RAW word literally into the already constructed
all-parent quotient source. The accepted canonical typed I10 exact-pullback
theorem then supplies a genuine current RAW presentation, with every middle
kernel and logical equality included. This works at arbitrary different
selected endpoint sorts and supplies all full kernels/bridges needed to
compare the COMPLETE actual reached groupoids. No quotient SAP or section
of a quotient automorphism group is assumed.
-/

universe u v w t
namespace CCO.ExactEPGeometry

open APCharacter.Towers
open RigidGroupoid.Geometry

noncomputable section

variable (A B : CurrentSource.{u,v,w,t})
variable (P : UnaryReduct A.source B.source)
variable (transport : ExactTraceTransport A.source B.source P)
variable (base : A.Sorts) (hOne : ∀ i : A.Sorts, base = i)
variable (E : ExactEq A.source base)

/-- Reverse FULL RAW exactness on the TRUE selected source, including
different occupancy endpoint sorts. The literal old projections are onto
each selected quotient carrier, and all provider premises are discharged. -/
theorem originalExactSelectedFullExact_pullback
    {c d : OriginalOccupancy A B P base hOne E}
    (R : (originalExactSelectedQuotientCurrentSource
      A B P transport base hOne E).Point c →
      (originalExactSelectedQuotientCurrentSource
        A B P transport base hOne E).Point d → Prop)
    (hR : FullExact (originalExactSelectedQuotientCurrentSource
      A B P transport base hOne E).source R) :
    let sigma := originalOccupancyRepresentative A B P base hOne E
    let Q := originalExactSelectedQuotientCurrentSource A B P transport base hOne E
    FullExact B.source (GroupActions.pullback
      (fun x : B.Point (sigma c) => (Quotient.mk'' x : Q.Point c))
      (fun y : B.Point (sigma d) => (Quotient.mk'' y : Q.Point d)) R) := by
  let Q := originalExactAllCurrentQuotientCurrentSource A B P transport base hOne E
  let sigma := originalOccupancyRepresentativeEmbedding A B P base hOne E
  letI : Finite (OriginalOccupancy A B P base hOne E) :=
    originalOccupancyFinite A B P base hOne E
  letI : Fintype (OriginalOccupancy A B P base hOne E) := Fintype.ofFinite _
  have hAll : FullExact Q.source R := selectedSortFullExact_inclusion Q.source sigma R hR
  let J := originalExactCurrentKernelFamily A B P transport base hOne E
  let W := originalExactCurrentKernelWords A B P transport base hOne E
  let hW := originalExactCurrentKernelWords_relation A B P transport base hOne E
  change FullExact (CCO.ExactCRT.CanonicalTyped.source B.source B.homogeneous J W hW) R at hAll
  obtain ⟨F,hF⟩ := hAll
  let oldF := CCO.ExactCRT.CanonicalTyped.exactPullback B.source B.homogeneous J W hW B.cco F
  refine ⟨oldF,?_⟩
  have hPull := CCO.ExactCRT.CanonicalTyped.exactPullback_relation
    B.source B.homogeneous J W hW B.cco F
  exact hPull.trans (congrArg (GroupActions.pullback
    (fun x : B.Point (sigma c) => (Quotient.mk'' x : Quotient (J (sigma c))))
    (fun y : B.Point (sigma d) => (Quotient.mk'' y : Quotient (J (sigma d))))) hF)

/-- The literal inverse image of ANY true selected full exact kernel,
at its true canonical current representative parent. -/
def originalExactSelectedKernelPullback
    {c : OriginalOccupancy A B P base hOne E}
    (K : Kernel (originalExactSelectedQuotientCurrentSource
      A B P transport base hOne E).source c) :
    Kernel B.source (originalOccupancyRepresentative A B P base hOne E c) where
  setoid := Setoid.comap
    (fun x : B.Point (originalOccupancyRepresentative A B P base hOne E c) =>
      (Quotient.mk'' x : (originalExactSelectedQuotientCurrentSource
        A B P transport base hOne E).Point c)) K.setoid
  exact := originalExactSelectedFullExact_pullback A B P transport base hOne E K.rel K.exact

/-- An ARBITRARY whole bridge in the selected quotient gives a genuine
whole current bridge at its canonical selected parents. All bridge laws
follow using actual quotient surjectivity at the displayed middle sort. -/
def originalExactSelectedBridgePullback
    {c d : OriginalOccupancy A B P base hOne E}
    (K : Kernel (originalExactSelectedQuotientCurrentSource
      A B P transport base hOne E).source c)
    (R : Bridge (originalExactSelectedQuotientCurrentSource
      A B P transport base hOne E).source K d) :
    Bridge B.source (originalExactSelectedKernelPullback A B P transport base hOne E K)
      (originalOccupancyRepresentative A B P base hOne E d) := by
  let Q := originalExactSelectedQuotientCurrentSource A B P transport base hOne E
  let sigma := originalOccupancyRepresentative A B P base hOne E
  let pi := fun c => fun x : B.Point (sigma c) => (Quotient.mk'' x : Q.Point c)
  let oldK := originalExactSelectedKernelPullback A B P transport base hOne E K
  refine {
    rel := GroupActions.pullback (pi c) (pi d) R.rel
    exact := originalExactSelectedFullExact_pullback A B P transport base hOne E R.rel R.exact
    left := ?_
    source := ?_
  }
  · funext x y
    apply propext
    constructor
    · rintro ⟨z,hxz,hzy⟩
      have h : TRel.comp K.rel R.rel (pi c x) (pi d y) := ⟨pi c z,hxz,hzy⟩
      exact (Iff.of_eq (congrFun (congrFun R.left (pi c x)) (pi d y))).mp h
    · intro hxy
      have h : TRel.comp K.rel R.rel (pi c x) (pi d y) :=
        (Iff.of_eq (congrFun (congrFun R.left (pi c x)) (pi d y))).mpr hxy
      obtain ⟨z,hxz,hzy⟩ := h
      obtain ⟨zz,hzz⟩ := Quotient.mk''_surjective z
      change pi c zz = z at hzz
      refine ⟨zz,?_,?_⟩
      · change K.rel (pi c x) (pi c zz)
        rw [hzz]
        exact hxz
      · change R.rel (pi c zz) (pi d y)
        rw [hzz]
        exact hzy
  · funext x y
    apply propext
    constructor
    · rintro ⟨z,hxz,hyz⟩
      have h : TRel.comp R.rel (TRel.converse R.rel) (pi c x) (pi c y) :=
        ⟨pi d z,hxz,hyz⟩
      exact (Iff.of_eq (congrFun (congrFun R.source (pi c x)) (pi c y))).mp h
    · intro hxy
      have h : TRel.comp R.rel (TRel.converse R.rel) (pi c x) (pi c y) :=
        (Iff.of_eq (congrFun (congrFun R.source (pi c x)) (pi c y))).mpr hxy
      obtain ⟨z,hxz,hyz⟩ := h
      obtain ⟨zz,hzz⟩ := Quotient.mk''_surjective z
      change pi d zz = z at hzz
      refine ⟨zz,?_,?_⟩
      · change R.rel (pi c x) (pi d zz)
        rw [hzz]
        exact hxz
      · change R.rel (pi c y) (pi d zz)
        rw [hzz]
        exact hyz

end
end CCO.ExactEPGeometry
