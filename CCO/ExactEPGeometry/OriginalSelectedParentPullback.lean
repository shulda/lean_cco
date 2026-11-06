import CCO.ExactEPGeometry.SelectedRetypingExactPullback
import CCO.ExactEPGeometry.OriginalSelectedFullExactPullback
import CCO.ExactEPGeometry.OriginalSelectedSortRetyping
import CCO.ExactEPGeometry.OriginalSelectedFiniteReachedInjectivity

/-!
# B062 C103: arbitrary-parent exact pullback through the TRUE selected E-source

Use the same canonical current-to-selected point map as the finite-age
construction. At EVERY old named parent it is onto its real selected
E-class carrier. Full exact relations pull back first through the genuine
equivariant all-parent-to-selected carriers (exact orbital graphs), and then
through the accepted typed quotient I10 theorem. Thus arbitrary selected
full kernels and bridges pull back at the specified old parents, retaining
the selected root gate rather than replacing it by an unrelated kernel.
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

/-- Literal component of the actual current-to-selected point map. -/
def originalSelectedLocalProjection (i : B.Sorts) (x : B.Point i) :
    (originalExactSelectedQuotientCurrentSource A B P transport base hOne E).Point
      (Quotient.mk'' i : OriginalOccupancy A B P base hOne E) :=
  (originalCurrentToSelectedPoint A B P transport base hOne E ⟨i,x⟩).2

theorem originalSelectedLocalProjection_surjective (i : B.Sorts) :
    Function.Surjective (originalSelectedLocalProjection A B P transport base hOne E i) := by
  let Qall := originalExactAllCurrentQuotientCurrentSource A B P transport base hOne E
  letI : ∀ k : Qall.Sorts, MulAction B.G (Qall.Point k) := Qall.action
  let D := originalSelectedSortRetyping A B P transport base hOne E
  change Function.Surjective (fun x : B.Point i => D.pointEquiv i (Quotient.mk'' x))
  exact (D.pointEquiv i).surjective.comp Quotient.mk''_surjective

/-- Actual reverse FULL RAW exactness on any displayed pair of old
parents. Every intermediate exactness provider is source-constructed. -/
theorem originalExactSelectedAtParentsFullExact_pullback
    {i j : B.Sorts}
    (R : (originalExactSelectedQuotientCurrentSource A B P transport base hOne E).Point
      (Quotient.mk'' i : OriginalOccupancy A B P base hOne E) →
      (originalExactSelectedQuotientCurrentSource A B P transport base hOne E).Point
        (Quotient.mk'' j : OriginalOccupancy A B P base hOne E) → Prop)
    (hR : FullExact (originalExactSelectedQuotientCurrentSource
      A B P transport base hOne E).source R) :
    FullExact B.source (GroupActions.pullback
      (originalSelectedLocalProjection A B P transport base hOne E i)
      (originalSelectedLocalProjection A B P transport base hOne E j) R) := by
  let Qall := originalExactAllCurrentQuotientCurrentSource A B P transport base hOne E
  letI : ∀ k : Qall.Sorts, MulAction B.G (Qall.Point k) := Qall.action
  letI : Finite (OriginalOccupancy A B P base hOne E) :=
    originalOccupancyFinite A B P base hOne E
  letI : Fintype (OriginalOccupancy A B P base hOne E) := Fintype.ofFinite _
  let sigma := originalOccupancyRepresentativeEmbedding A B P base hOne E
  let D : SelectedRetyping (X := Qall.Point) sigma (G := B.G) :=
    originalSelectedSortRetyping A B P transport base hOne E
  let CQ := exactCalculus_of_homogeneous_CCO Qall.source Qall.homogeneous Qall.cco
  have hAll : FullExact Qall.source
      (GroupActions.pullback (D.pointEquiv i) (D.pointEquiv j) R) :=
    D.pullbackFullExact Qall.source Qall.homogeneous CQ R hR
  let J := originalExactCurrentKernelFamily A B P transport base hOne E
  let W := originalExactCurrentKernelWords A B P transport base hOne E
  let hW := originalExactCurrentKernelWords_relation A B P transport base hOne E
  change FullExact (CCO.ExactCRT.CanonicalTyped.source B.source B.homogeneous J W hW)
    (GroupActions.pullback (D.pointEquiv i) (D.pointEquiv j) R) at hAll
  obtain ⟨F,hF⟩ := hAll
  let oldF := CCO.ExactCRT.CanonicalTyped.exactPullback B.source B.homogeneous J W hW B.cco F
  refine ⟨oldF,?_⟩
  have hPull := CCO.ExactCRT.CanonicalTyped.exactPullback_relation
    B.source B.homogeneous J W hW B.cco F
  exact hPull.trans (congrArg (GroupActions.pullback
    (fun x : B.Point i => (Quotient.mk'' x : Quotient (J i)))
    (fun y : B.Point j => (Quotient.mk'' y : Quotient (J j)))) hF)

/-- Full selected kernels pulled back at the specified original parent. -/
def originalExactSelectedAtParentKernelPullback {i : B.Sorts}
    (K : Kernel (originalExactSelectedQuotientCurrentSource A B P transport base hOne E).source
      (Quotient.mk'' i : OriginalOccupancy A B P base hOne E)) : Kernel B.source i where
  setoid := Setoid.comap (originalSelectedLocalProjection A B P transport base hOne E i) K.setoid
  exact := originalExactSelectedAtParentsFullExact_pullback A B P transport base hOne E K.rel K.exact

/-- Arbitrary full selected bridges lift to the specified old endpoints,
using surjectivity at the actual displayed middle occupancy sort. -/
def originalExactSelectedAtParentsBridgePullback {i j : B.Sorts}
    (K : Kernel (originalExactSelectedQuotientCurrentSource A B P transport base hOne E).source
      (Quotient.mk'' i : OriginalOccupancy A B P base hOne E))
    (R : Bridge (originalExactSelectedQuotientCurrentSource A B P transport base hOne E).source K
      (Quotient.mk'' j : OriginalOccupancy A B P base hOne E)) :
    Bridge B.source (originalExactSelectedAtParentKernelPullback A B P transport base hOne E K) j := by
  let pi := originalSelectedLocalProjection A B P transport base hOne E
  refine {
    rel := GroupActions.pullback (pi i) (pi j) R.rel
    exact := originalExactSelectedAtParentsFullExact_pullback A B P transport base hOne E R.rel R.exact
    left := ?_
    source := ?_
  }
  · funext x y
    apply propext
    constructor
    · rintro ⟨z,hxz,hzy⟩
      have h : TRel.comp K.rel R.rel (pi i x) (pi j y) := ⟨pi i z,hxz,hzy⟩
      exact (Iff.of_eq (congrFun (congrFun R.left (pi i x)) (pi j y))).mp h
    · intro hxy
      have h : TRel.comp K.rel R.rel (pi i x) (pi j y) :=
        (Iff.of_eq (congrFun (congrFun R.left (pi i x)) (pi j y))).mpr hxy
      obtain ⟨z,hxz,hzy⟩ := h
      obtain ⟨zz,hzz⟩ := originalSelectedLocalProjection_surjective A B P transport base hOne E i z
      change pi i zz = z at hzz
      exact ⟨zz,Eq.mpr (congrArg (fun a => K.rel (pi i x) a) hzz) hxz,
        Eq.mpr (congrArg (fun a => R.rel a (pi j y)) hzz) hzy⟩
  · funext x y
    apply propext
    constructor
    · rintro ⟨z,hxz,hyz⟩
      have h : TRel.comp R.rel (TRel.converse R.rel) (pi i x) (pi i y) := ⟨pi j z,hxz,hyz⟩
      exact (Iff.of_eq (congrFun (congrFun R.source (pi i x)) (pi i y))).mp h
    · intro hxy
      have h : TRel.comp R.rel (TRel.converse R.rel) (pi i x) (pi i y) :=
        (Iff.of_eq (congrFun (congrFun R.source (pi i x)) (pi i y))).mpr hxy
      obtain ⟨z,hxz,hyz⟩ := h
      obtain ⟨zz,hzz⟩ := originalSelectedLocalProjection_surjective A B P transport base hOne E j z
      change pi j zz = z at hzz
      exact ⟨zz,Eq.mpr (congrArg (fun a => R.rel (pi i x) a) hzz) hxz,
        Eq.mpr (congrArg (fun a => R.rel (pi i y) a) hzz) hyz⟩

end
end CCO.ExactEPGeometry
