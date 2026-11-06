import CCO.ExactEPGeometry.OriginalRetainedMixedActualNextAgeIff
import CCO.ExactEPGeometry.OriginalSelectedArbitraryTriangleAge

/-!
# B062 C89–C96: both full finite-age directions for arbitrary quotient diagrams

The input is an ARBITRARY complete old selected-quotient orbital diagram,
with genuine reached/inactive occupancy names and corrected character bits.
Local triangle legality and every full quotient mask are equivalent to
realizing that diagram together with a concrete ACTUAL successor quotient
chart. The input is not assumed already realized. The entire new saturated
palette of the output chart is supplied by its `newAtomicPalette` theorem.

The forward direction first realizes the complete old quotient diagram
using the already proved AP+HOM CCO triangle-age theorem. The reverse
direction reads actual marking legality, then transports the resulting
mask from a realized pair to every pair in the same genuine old orbital.
There is no quotient SAP, automorphism-group section or new source provider.
-/

universe u v w t
namespace CCO.ExactEPGeometry

open APCharacter
open APCharacter.Towers
open APCharacter.SourceAge
open RigidGroupoid.Geometry
open CategoryTheory
open CCO.RawExact

noncomputable section

private theorem sourceColour_eq_of_mem_same_actual_orbital
    (Q : CurrentSource.{u,v,w,t}) {i j : Q.Sorts}
    (rel : Q.Point i → Q.Point j → Prop)
    (hActual : ∃ a b, rel = GroupActions.orbital (G := Q.G) a b)
    (x u : Q.Point i) (y v : Q.Point j)
    (hxy : rel x y) (huv : rel u v) :
    Q.source.colour x y = Q.source.colour u v := by
  obtain ⟨a,b,hRel⟩ := hActual
  rw [hRel] at hxy huv
  obtain ⟨g,hgx,hgy⟩ := hxy
  obtain ⟨h,hhu,hhv⟩ := huv
  have hxy' := Q.source.colourInvariant_of_homogeneous Q.homogeneous g a b
  have huv' := Q.source.colourInvariant_of_homogeneous Q.homogeneous h a b
  rw [hgx,hgy] at hxy'
  rw [hhu,hhv] at huv'
  exact hxy'.trans huv'.symm

/-- C96 on every complete finite selected quotient orbital diagram:
triangle legality and corrected masks are EQUIVALENT to realization
in the TRUE next quotient age with all child names, all old colours
and distinct original E-classes. The chart also carries its entire
NEW atomic palette through `newAtomicPalette`. -/
theorem originalRetainedArbitraryMixedDiagram_iff_actualNextAge
    (A B : CurrentSource.{u,v,w,t})
    (P : UnaryReduct A.source B.source)
    (transport : ExactTraceTransport A.source B.source P)
    (tp : ExactTraceProduct A.source B.source P)
    (hOne : ∀ i j : A.Sorts, i = j)
    {r : B.Sorts} (Kroot : Kernel B.source r)
    (phase : SourcePhase B.source B.homogeneous
      (exactCalculus_of_homogeneous_CCO B.source B.homogeneous B.cco) Kroot)
    (E : ExactEq A.source (P.parent r))
    (hE : E ≤ PrefixExactLargestLift.largest A B P transport tp r
      (current_kernel_exact_eq B Kroot)) :
    let base := P.parent r
    let hBase : ∀ i : A.Sorts, base = i := fun i => hOne base i
    let Occ := OriginalReachedOccupancy A B P base hBase E Kroot
    letI := originalRetainedOccupancyGroupoid A B P transport tp hOne Kroot E hE
    let Q := originalExactSelectedQuotientCurrentSource A B P transport base hBase E
    letI : ∀ c : Q.Sorts, MulAction B.G (Q.Point c) := Q.action
    let anchor := originalReachedOccupancyAnchor A B P base hBase E Kroot
    let K := fun o : Occ => originalRetainedSelectedKernel
      A B P transport tp hOne Kroot E hE (anchor o)
    let chi := originalRetainedSelectedOccupancyCharacter
      A B P transport tp hOne Kroot phase E hE
    ∀ (n m : Nat) (owners : Fin n → Occ) (inactiveSort : Fin m → Q.Sorts),
    let sort : Sum (Fin n) (Fin m) → Q.Sorts := fun v =>
      match v with
      | Sum.inl i => Quotient.mk'' (anchor (owners i)).val
      | Sum.inr j => inactiveSort j
    ∀ (rel : ∀ v w : Sum (Fin n) (Fin m),
        Q.Point (sort v) → Q.Point (sort w) → Prop) (bits : Fin n → ZMod 2),
      (∀ v w : Sum (Fin n) (Fin m),
        letI : MulAction B.G (Q.Point (sort v)) := Q.action (sort v)
        letI : MulAction B.G (Q.Point (sort w)) := Q.action (sort w)
        ∃ x y, rel v w = GroupActions.orbital (G := B.G) x y) →
      (∀ v w : Sum (Fin n) (Fin m), ∀ x y, rel v w x y ↔ rel w v y x) →
      (∀ v : Sum (Fin n) (Fin m), ∀ x y, rel v v x y ↔ x = y) →
      (∀ v w : Sum (Fin n) (Fin m), v ≠ w → ∀ x y, rel v w x y →
        (⟨sort v,x⟩ : Sigma Q.Point) ≠ (⟨sort w,y⟩ : Sigma Q.Point)) →
      (∀ j : Fin m, ¬Nonempty (Bridge B.source Kroot
        (originalOccupancyRepresentative A B P base hBase E (inactiveSort j)))) →
      ((∀ v w z : Sum (Fin n) (Fin m), ∃ x y q,
          rel v w x y ∧ rel v z x q ∧ rel w z y q) ∧
        (∀ i j : Fin n, ∀ x y, rel (Sum.inl i) (Sum.inl j) x y →
          originalSelectedCompleteAtomicMask Q (K (owners i)) (K (owners j))
            (fun (R : owners i ⟶ owners j) => chi.value R)
            (Q.source.colour x y) (bits i) (bits j))) ↔
      ∃ point : ∀ v : Sum (Fin n) (Fin m), Q.Point (sort v),
        (∀ v w, rel v w (point v) (point w)) ∧
        Function.Injective (fun v => (⟨sort v,point v⟩ : Sigma Q.Point)) ∧
        let old : Sum (Fin n) (Fin m) → Sigma B.Point := fun v =>
          match v with
          | Sum.inl i => ⟨(anchor (owners i)).val,
              originalSelectedReachedEclassRepresentative A B P transport hOne
                Kroot E (anchor (owners i)) (point (Sum.inl i))⟩
          | Sum.inr j => originalSelectedTaggedRepresentative
              A B P transport base hBase E ⟨inactiveSort j,point (Sum.inr j)⟩
        let allBits : Sum (Fin n) (Fin m) → ZMod 2 := fun v =>
          match v with | Sum.inl i => bits i | Sum.inr _ => 0
        Nonempty (OriginalActualNextQuotientChart
          A B P base hBase E Kroot phase old allBits) := by
  let base := P.parent r
  let hBase : ∀ i : A.Sorts, base = i := fun i => hOne base i
  let Occ := OriginalReachedOccupancy A B P base hBase E Kroot
  letI : Groupoid Occ := originalRetainedOccupancyGroupoid
    A B P transport tp hOne Kroot E hE
  let Q := originalExactSelectedQuotientCurrentSource A B P transport base hBase E
  letI : ∀ c : Q.Sorts, MulAction B.G (Q.Point c) := Q.action
  let anchor := originalReachedOccupancyAnchor A B P base hBase E Kroot
  let K := fun o : Occ => originalRetainedSelectedKernel
    A B P transport tp hOne Kroot E hE (anchor o)
  let chi := originalRetainedSelectedOccupancyCharacter
    A B P transport tp hOne Kroot phase E hE
  dsimp only
  intro n m owners inactiveSort
  let sort : Sum (Fin n) (Fin m) → Q.Sorts := fun v =>
    match v with
    | Sum.inl i => Quotient.mk'' (anchor (owners i)).val
    | Sum.inr j => inactiveSort j
  intro rel bits hActual hReverse hDiagonal hSeparate hInactive
  let D : ActualOrbitalDiagram B.G Q.Point (Sum (Fin n) (Fin m)) := {
    sort := sort
    relation := rel
    actual := hActual
    reverse := hReverse
    diagonal := hDiagonal
    separates := hSeparate
  }
  constructor
  · rintro ⟨hTriangles,hMasks⟩
    obtain ⟨point,hReal,hInjective⟩ := originalExactSelectedQuotient_arbitraryTriangleAge
      A B P transport base hBase E D hTriangles
    let activePoint (i : Fin n) := point (Sum.inl i)
    let inactivePoint (j : Fin m) : Sigma Q.Point :=
      ⟨inactiveSort j,point (Sum.inr j)⟩
    have hSelected : Function.Injective (fun v : Sum (Fin n) (Fin m) =>
        match v with
        | Sum.inl i => (⟨Quotient.mk'' (anchor (owners i)).val,activePoint i⟩ : Sigma Q.Point)
        | Sum.inr j => inactivePoint j) := by
      intro v w hvw
      apply hInjective
      cases v <;> cases w <;> exact hvw
    have hInactive' : ∀ j : Fin m, ¬Nonempty (Bridge B.source Kroot
        (originalSelectedTaggedRepresentative
          A B P transport base hBase E (inactivePoint j)).1) := hInactive
    have hMasks' : ∀ i j : Fin n,
        originalSelectedCompleteAtomicMask Q (K (owners i)) (K (owners j))
          (fun (R : owners i ⟶ owners j) => chi.value R)
          (Q.source.colour (activePoint i) (activePoint j)) (bits i) (bits j) := by
      intro i j
      exact hMasks i j _ _ (hReal (Sum.inl i) (Sum.inl j))
    exact ⟨point,hReal,hInjective,
      (originalRetainedMixedSelectedMasks_iff_actualNextChart
        A B P transport tp hOne Kroot phase E hE
        n m owners activePoint bits inactivePoint hSelected hInactive').mp hMasks'⟩
  · rintro ⟨point,hReal,hInjective,hChart⟩
    let activePoint (i : Fin n) := point (Sum.inl i)
    let inactivePoint (j : Fin m) : Sigma Q.Point :=
      ⟨inactiveSort j,point (Sum.inr j)⟩
    have hSelected : Function.Injective (fun v : Sum (Fin n) (Fin m) =>
        match v with
        | Sum.inl i => (⟨Quotient.mk'' (anchor (owners i)).val,activePoint i⟩ : Sigma Q.Point)
        | Sum.inr j => inactivePoint j) := by
      intro v w hvw
      apply hInjective
      cases v <;> cases w <;> exact hvw
    have hInactive' : ∀ j : Fin m, ¬Nonempty (Bridge B.source Kroot
        (originalSelectedTaggedRepresentative
          A B P transport base hBase E (inactivePoint j)).1) := hInactive
    have hMasks := (originalRetainedMixedSelectedMasks_iff_actualNextChart
      A B P transport tp hOne Kroot phase E hE
      n m owners activePoint bits inactivePoint hSelected hInactive').mpr hChart
    constructor
    · intro v w z
      exact ⟨point v,point w,point z,hReal v w,hReal v z,hReal w z⟩
    · intro i j x y hxy
      have hc : Q.source.colour x y =
          Q.source.colour (activePoint i) (activePoint j) :=
        sourceColour_eq_of_mem_same_actual_orbital Q
          (rel (Sum.inl i) (Sum.inl j)) (hActual (Sum.inl i) (Sum.inl j))
          x (activePoint i) y (activePoint j) hxy (hReal (Sum.inl i) (Sum.inl j))
      rw [hc]
      exact hMasks i j

end
end CCO.ExactEPGeometry
