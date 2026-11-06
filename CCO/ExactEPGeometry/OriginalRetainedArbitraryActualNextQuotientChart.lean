import CCO.ExactEPGeometry.OriginalRetainedArbitraryMixedMarkedTriangleAge
import CCO.ExactEPGeometry.OriginalRetainedMixedActualNextQuotientChart

/-!
# B062 C89–C95: every legal mixed marked quotient diagram has a true next witness

Begin with an ARBITRARY complete finite diagram of genuine OLD selected
quotient orbitals, legal triangles and the corrected full-character
masks, mixing reached and actually inactive occupancy sorts. Realize its
whole unmarked diagram in the already constructed AP+HOM CCO quotient
prefix. The actual selected E-points supply distinct global E-classes.

The genuine marked-age construction then supplies ONE true SingleStep
successor chart with the prescribed child bits, the full old pair-colour
table, distinct original E-classes and ALL old E-saturated orbital blocks.
No already-realized input diagram, quotient SAP, global action section or
extra E-distinctness assumption is used. Identification of the NEW
quotient palette and reverse full finite age remains a separate obligation.
-/

universe u v w t
namespace CCO.ExactEPGeometry

open APCharacter
open APCharacter.Towers
open APCharacter.SourceAge
open RigidGroupoid.Geometry
open CategoryTheory
open CCO.RawExact
open OwnerTransversal.CountableColour

noncomputable section

/-- Source C89–C95 for every arbitrary locally allowed complete
mixed quotient diagram. The output is in the ACTUAL successor and
has no collapse after the original E quotient. -/
theorem originalRetainedArbitraryMixedDiagram_actualNextQuotientChart
    (A B : CurrentSource.{u,v,w,t})
    (P : UnaryReduct A.source B.source)
    (transport : ExactTraceTransport A.source B.source P)
    (tp : ExactTraceProduct A.source B.source P)
    (hOne : ∀ i j : A.Sorts, i = j)
    {r : B.Sorts} (Kroot : Kernel B.source r)
    (phase : SourcePhase B.source B.homogeneous
      (exactCalculus_of_homogeneous_CCO
        B.source B.homogeneous B.cco) Kroot)
    (E : ExactEq A.source (P.parent r))
    (hE : E ≤ PrefixExactLargestLift.largest A B P transport tp r
      (current_kernel_exact_eq B Kroot)) :
    let base := P.parent r
    let hBase : ∀ i : A.Sorts, base = i := fun i => hOne base i
    let Occ := OriginalReachedOccupancy A B P base hBase E Kroot
    letI := originalRetainedOccupancyGroupoid
      A B P transport tp hOne Kroot E hE
    let Q := originalExactSelectedQuotientCurrentSource
      A B P transport base hBase E
    letI : ∀ c : Q.Sorts, MulAction B.G (Q.Point c) := Q.action
    let anchor := originalReachedOccupancyAnchor
      A B P base hBase E Kroot
    let K := fun o : Occ => originalRetainedSelectedKernel
      A B P transport tp hOne Kroot E hE (anchor o)
    let chi := originalRetainedSelectedOccupancyCharacter
      A B P transport tp hOne Kroot phase E hE
    ∀ (n m : Nat) (owners : Fin n → Occ)
      (inactiveSort : Fin m → Q.Sorts),
      let sort : Sum (Fin n) (Fin m) → Q.Sorts :=
        fun v => match v with
        | Sum.inl i => Quotient.mk'' (anchor (owners i)).val
        | Sum.inr j => inactiveSort j
      ∀ (rel : ∀ v w : Sum (Fin n) (Fin m),
          Q.Point (sort v) → Q.Point (sort w) → Prop)
        (bits : Fin n → ZMod 2),
        (∀ v w : Sum (Fin n) (Fin m),
          letI : MulAction B.G (Q.Point (sort v)) :=
            Q.action (sort v)
          letI : MulAction B.G (Q.Point (sort w)) :=
            Q.action (sort w)
          ∃ x y, rel v w = GroupActions.orbital (G := B.G) x y) →
        (∀ v w : Sum (Fin n) (Fin m), ∀ x y,
          rel v w x y ↔ rel w v y x) →
        (∀ v : Sum (Fin n) (Fin m), ∀ x y,
          rel v v x y ↔ x = y) →
        (∀ v w : Sum (Fin n) (Fin m), v ≠ w → ∀ x y,
          rel v w x y →
          (⟨sort v,x⟩ : Sigma Q.Point) ≠
            (⟨sort w,y⟩ : Sigma Q.Point)) →
        (∀ v w z : Sum (Fin n) (Fin m), ∃ x y q,
          rel v w x y ∧ rel v z x q ∧ rel w z y q) →
        (∀ i j : Fin n, ∀ x y,
          rel (Sum.inl i) (Sum.inl j) x y →
          originalSelectedCompleteAtomicMask Q
            (K (owners i)) (K (owners j))
            (fun (R : owners i ⟶ owners j) => chi.value R)
            (Q.source.colour x y) (bits i) (bits j)) →
        (∀ j : Fin m,
          ¬Nonempty (Bridge B.source Kroot
            (originalOccupancyRepresentative
              A B P base hBase E (inactiveSort j)))) →
        ∃ point : ∀ v : Sum (Fin n) (Fin m), Q.Point (sort v),
          (∀ v w, rel v w (point v) (point w)) ∧
          Function.Injective
            (fun v => (⟨sort v,point v⟩ : Sigma Q.Point)) ∧
          let old : Sum (Fin n) (Fin m) → Sigma B.Point :=
            fun v => match v with
            | Sum.inl i =>
                ⟨(anchor (owners i)).val,
                  originalSelectedReachedEclassRepresentative
                    A B P transport hOne Kroot E
                      (anchor (owners i)) (point (Sum.inl i))⟩
            | Sum.inr j =>
                originalSelectedTaggedRepresentative
                  A B P transport base hBase E
                    ⟨inactiveSort j,point (Sum.inr j)⟩
          let allBits : Sum (Fin n) (Fin m) → ZMod 2 :=
            fun v => match v with
            | Sum.inl i => bits i
            | Sum.inr _ => 0
          ∃ next : Sum (Fin n) (Fin m) ↪
              Sigma (SingleStep.successor B phase).Point,
            (∀ v, UnarySource.childLabel (SingleStep.identification B phase)
              (next v).1 = ((old v).1,allBits v)) ∧
            (∀ v w, taggedColour B.source
              ((SingleStep.projection B phase).project (next v))
              ((SingleStep.projection B phase).project (next w)) =
                taggedColour B.source (old v) (old w)) ∧
            (∀ v w, (currentOriginalExactSetoid A B P base hBase E).r
              (old v) (old w) ↔
              (currentOriginalExactSetoid A (SingleStep.successor B phase)
                (P.compose (SingleStep.projection B phase))
                base hBase E).r (next v) (next w)) ∧
            Function.Injective (fun v : Sum (Fin n) (Fin m) =>
              (Quotient.mk'' (next v) :
                Quotient (currentOriginalExactSetoid A
                  (SingleStep.successor B phase)
                  (P.compose (SingleStep.projection B phase))
                  base hBase E))) ∧
            (∀ (a : Age.Colour B.source) (v w : Sum (Fin n) (Fin m)),
              originalCurrentExactSaturatedColour A B P base hBase E
                a (old v) (old w) ↔
              originalCurrentExactSaturatedColour A B P base hBase E
                a ((SingleStep.projection B phase).project (next v))
                  ((SingleStep.projection B phase).project (next w))) := by
  let base := P.parent r
  let hBase : ∀ i : A.Sorts, base = i := fun i => hOne base i
  let Occ := OriginalReachedOccupancy A B P base hBase E Kroot
  letI : Groupoid Occ := originalRetainedOccupancyGroupoid
    A B P transport tp hOne Kroot E hE
  let Q := originalExactSelectedQuotientCurrentSource
    A B P transport base hBase E
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
  change ∀ (rel : ∀ v w : Sum (Fin n) (Fin m),
          Q.Point (sort v) → Q.Point (sort w) → Prop)
        (bits : Fin n → ZMod 2),
        (∀ v w : Sum (Fin n) (Fin m),
          letI : MulAction B.G (Q.Point (sort v)) :=
            Q.action (sort v)
          letI : MulAction B.G (Q.Point (sort w)) :=
            Q.action (sort w)
          ∃ x y, rel v w = GroupActions.orbital (G := B.G) x y) →
        (∀ v w : Sum (Fin n) (Fin m), ∀ x y,
          rel v w x y ↔ rel w v y x) →
        (∀ v : Sum (Fin n) (Fin m), ∀ x y,
          rel v v x y ↔ x = y) →
        (∀ v w : Sum (Fin n) (Fin m), v ≠ w → ∀ x y,
          rel v w x y →
          (⟨sort v,x⟩ : Sigma Q.Point) ≠
            (⟨sort w,y⟩ : Sigma Q.Point)) →
        (∀ v w z : Sum (Fin n) (Fin m), ∃ x y q,
          rel v w x y ∧ rel v z x q ∧ rel w z y q) →
        (∀ i j : Fin n, ∀ x y,
          rel (Sum.inl i) (Sum.inl j) x y →
          originalSelectedCompleteAtomicMask Q
            (K (owners i)) (K (owners j))
            (fun (R : owners i ⟶ owners j) => chi.value R)
            (Q.source.colour x y) (bits i) (bits j)) →
        (∀ j : Fin m,
          ¬Nonempty (Bridge B.source Kroot
            (originalOccupancyRepresentative
              A B P base hBase E (inactiveSort j)))) →
        ∃ point : ∀ v : Sum (Fin n) (Fin m), Q.Point (sort v),
          (∀ v w, rel v w (point v) (point w)) ∧
          Function.Injective
            (fun v => (⟨sort v,point v⟩ : Sigma Q.Point)) ∧
          let old : Sum (Fin n) (Fin m) → Sigma B.Point :=
            fun v => match v with
            | Sum.inl i =>
                ⟨(anchor (owners i)).val,
                  originalSelectedReachedEclassRepresentative
                    A B P transport hOne Kroot E
                      (anchor (owners i)) (point (Sum.inl i))⟩
            | Sum.inr j =>
                originalSelectedTaggedRepresentative
                  A B P transport base hBase E
                    ⟨inactiveSort j,point (Sum.inr j)⟩
          let allBits : Sum (Fin n) (Fin m) → ZMod 2 :=
            fun v => match v with
            | Sum.inl i => bits i
            | Sum.inr _ => 0
          ∃ next : Sum (Fin n) (Fin m) ↪
              Sigma (SingleStep.successor B phase).Point,
            (∀ v, UnarySource.childLabel (SingleStep.identification B phase)
              (next v).1 = ((old v).1,allBits v)) ∧
            (∀ v w, taggedColour B.source
              ((SingleStep.projection B phase).project (next v))
              ((SingleStep.projection B phase).project (next w)) =
                taggedColour B.source (old v) (old w)) ∧
            (∀ v w, (currentOriginalExactSetoid A B P base hBase E).r
              (old v) (old w) ↔
              (currentOriginalExactSetoid A (SingleStep.successor B phase)
                (P.compose (SingleStep.projection B phase))
                base hBase E).r (next v) (next w)) ∧
            Function.Injective (fun v : Sum (Fin n) (Fin m) =>
              (Quotient.mk'' (next v) :
                Quotient (currentOriginalExactSetoid A
                  (SingleStep.successor B phase)
                  (P.compose (SingleStep.projection B phase))
                  base hBase E))) ∧
            (∀ (a : Age.Colour B.source) (v w : Sum (Fin n) (Fin m)),
              originalCurrentExactSaturatedColour A B P base hBase E
                a (old v) (old w) ↔
              originalCurrentExactSaturatedColour A B P base hBase E
                a ((SingleStep.projection B phase).project (next v))
                  ((SingleStep.projection B phase).project (next w)))
  intro rel bits hActual hReverse hDiagonal hSeparate hTriangles hMasks hInactive
  letI : Finite (Sum (Fin n) (Fin m)) := inferInstance
  let D : ActualOrbitalDiagram B.G Q.Point (Sum (Fin n) (Fin m)) := {
    sort := sort
    relation := rel
    actual := hActual
    reverse := hReverse
    diagonal := hDiagonal
    separates := hSeparate
  }
  have hLegal : D.TrianglesLegal := hTriangles
  obtain ⟨point,hReal,hInjective⟩ :=
    originalExactSelectedQuotient_arbitraryTriangleAge
      A B P transport base hBase E D hLegal
  let activePoint (i : Fin n) :
      Q.Point (Quotient.mk'' (anchor (owners i)).val) :=
    point (Sum.inl i)
  let inactivePoint (j : Fin m) : Sigma Q.Point :=
    ⟨inactiveSort j,point (Sum.inr j)⟩
  have hMasksReal : ∀ i j : Fin n,
      originalSelectedCompleteAtomicMask Q
        (K (owners i)) (K (owners j))
        (fun (R : owners i ⟶ owners j) => chi.value R)
        (Q.source.colour (activePoint i) (activePoint j))
        (bits i) (bits j) := by
    intro i j
    exact hMasks i j (activePoint i) (activePoint j)
      (hReal (Sum.inl i) (Sum.inl j))
  have hSelected : Function.Injective
      (fun v : Sum (Fin n) (Fin m) =>
        match v with
        | Sum.inl i =>
            (⟨(Quotient.mk'' (anchor (owners i)).val :
                OriginalOccupancy A B P base hBase E),activePoint i⟩ :
                Sigma Q.Point)
        | Sum.inr j => inactivePoint j) := by
    intro v w hvw
    apply hInjective
    cases v <;> cases w <;> exact hvw
  have hInactiveSelected : ∀ j : Fin m,
      ¬Nonempty (Bridge B.source Kroot
        (originalSelectedTaggedRepresentative
          A B P transport base hBase E (inactivePoint j)).1) := by
    intro j
    exact hInactive j
  have hNext :=
    originalRetainedMixedSelectedMasks_actualNextQuotientChart
      A B P transport tp hOne Kroot phase E hE
        n m owners activePoint bits hMasksReal
          inactivePoint hSelected hInactiveSelected
  exact ⟨point,hReal,hInjective,hNext⟩

end
end CCO.ExactEPGeometry
