import CCO.ExactEPGeometry.OriginalSelectedArbitraryTriangleAge
import CCO.ExactEPGeometry.OriginalSelectedFiniteMarkedWitness

/-!
# B062 C89–C95: arbitrary locally legal reached-occupancy marked diagrams

Take an ARBITRARY finite diagram of the already constructed selected
original-E quotient prefix, with actual source orbitals, true diagonal,
reverse, injective diversity, and locally realizable triangles. The
C89 unmarked theorem first constructs ALL its quotient points jointly;
they are NOT assumed to have been realized before this theorem.

If its true quotient pair orbitals also satisfy the complete C88/C91
selected full-Arrow character masks for the prescribed bits, those
locally legal masks transfer to the newly realized points. C91–C95
then construct a compatible original global marking, distinct real
old E-class representatives, and ONE finite marked object embedded
in the actual AP-only homogeneous marked successor with its full fine
old orbital table and unary names intact.

This is the active-reached-occupancy part of the locally legal marked
age implication. It does NOT cover inactive occupancy classes, identify
all possible quotient marked successors in the converse direction,
or prove the entire quotient tower C96/C103. No quotient SAP, group
section, assumed old fine pair-orbital table or new provider occurs.
-/

universe u v w t

namespace CCO.ExactEPGeometry

open APCharacter
open APCharacter.Towers
open RigidGroupoid.Geometry
open CategoryTheory
open CCO.RawExact
open OwnerTransversal.CountableColour

noncomputable section

/-- All locally legal true reached-occupancy orbital diagrams (not
previously embedded ones) admit one actual old MARKED successor witness.
The quantified triangle and complete-Arrow character conditions are
checked on the specified orbital relations, before selecting points.
The entire fine old colour table is recovered from real representatives. -/
theorem originalRetainedArbitraryMarkedTriangleAge
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
    ∀ (n : Nat) (owners : Fin n → Occ)
      (rel : ∀ i j : Fin n,
        Q.Point (Quotient.mk'' (anchor (owners i)).val) →
        Q.Point (Quotient.mk'' (anchor (owners j)).val) → Prop)
      (bits : Fin n → ZMod 2),
      (∀ i j : Fin n,
        letI : MulAction B.G
            (Q.Point (Quotient.mk'' (anchor (owners i)).val)) :=
          Q.action (Quotient.mk'' (anchor (owners i)).val)
        letI : MulAction B.G
            (Q.Point (Quotient.mk'' (anchor (owners j)).val)) :=
          Q.action (Quotient.mk'' (anchor (owners j)).val)
        ∃ x y, rel i j = GroupActions.orbital (G := B.G) x y) →
      (∀ i j : Fin n, ∀ x y, rel i j x y ↔ rel j i y x) →
      (∀ i : Fin n, ∀ x y, rel i i x y ↔ x = y) →
      (∀ i j : Fin n, i ≠ j → ∀ x y, rel i j x y →
        (⟨(Quotient.mk'' (anchor (owners i)).val : Q.Sorts),x⟩ :
          Sigma Q.Point) ≠
        (⟨(Quotient.mk'' (anchor (owners j)).val : Q.Sorts),y⟩ :
          Sigma Q.Point)) →
      (∀ i j k : Fin n, ∃ x y z,
        rel i j x y ∧ rel i k x z ∧ rel j k y z) →
      (∀ i j : Fin n, ∀ x y, rel i j x y →
        originalSelectedCompleteAtomicMask Q
          (K (owners i)) (K (owners j))
          (fun (R : owners i ⟶ owners j) => chi.value R)
          (Q.source.colour x y) (bits i) (bits j)) →
      ∃ point : ∀ i : Fin n,
          Q.Point (Quotient.mk'' (anchor (owners i)).val),
        (∀ i j : Fin n, rel i j (point i) (point j)) ∧
        let old : Fin n → Sigma B.Point := fun i =>
          ⟨(anchor (owners i)).val,
            originalSelectedReachedEclassRepresentative
              A B P transport hOne Kroot E
                (anchor (owners i)) (point i)⟩
        ∃ f : Fin n ↪ phase.MarkedLimit B.cco,
          (∀ i, (phase.markedCoding B.cco).table.owner (f i) =
            APCharacter.Age.ownerEquiv B.source ((old i).1,bits i)) ∧
          ∀ i j, (phase.markedCoding B.cco).table.colour (f i) (f j) =
            APCharacter.Age.colourEquiv B.source
              (taggedColour B.source (old i) (old j)) := by
  let base := P.parent r
  let hBase : ∀ i : A.Sorts, base = i := fun i => hOne base i
  let Occ := OriginalReachedOccupancy A B P base hBase E Kroot
  letI : Groupoid Occ := originalRetainedOccupancyGroupoid
    A B P transport tp hOne Kroot E hE
  let Q := originalExactSelectedQuotientCurrentSource
    A B P transport base hBase E
  letI : ∀ c : Q.Sorts, MulAction B.G (Q.Point c) := Q.action
  let anchor := originalReachedOccupancyAnchor A B P base hBase E Kroot
  let sort : ∀ {n : Nat}, (Fin n → Occ) → Fin n → Q.Sorts :=
    fun owners i => Quotient.mk'' (anchor (owners i)).val
  let K := fun o : Occ => originalRetainedSelectedKernel
    A B P transport tp hOne Kroot E hE (anchor o)
  let chi := originalRetainedSelectedOccupancyCharacter
    A B P transport tp hOne Kroot phase E hE
  change ∀ (n : Nat) (owners : Fin n → Occ)
      (rel : ∀ i j : Fin n,
        Q.Point (Quotient.mk'' (anchor (owners i)).val) →
        Q.Point (Quotient.mk'' (anchor (owners j)).val) → Prop)
      (bits : Fin n → ZMod 2),
      (∀ i j : Fin n,
        letI : MulAction B.G
            (Q.Point (Quotient.mk'' (anchor (owners i)).val)) :=
          Q.action (Quotient.mk'' (anchor (owners i)).val)
        letI : MulAction B.G
            (Q.Point (Quotient.mk'' (anchor (owners j)).val)) :=
          Q.action (Quotient.mk'' (anchor (owners j)).val)
        ∃ x y, rel i j = GroupActions.orbital (G := B.G) x y) →
      (∀ i j : Fin n, ∀ x y, rel i j x y ↔ rel j i y x) →
      (∀ i : Fin n, ∀ x y, rel i i x y ↔ x = y) →
      (∀ i j : Fin n, i ≠ j → ∀ x y, rel i j x y →
        (⟨(Quotient.mk'' (anchor (owners i)).val : Q.Sorts),x⟩ :
          Sigma Q.Point) ≠
        (⟨(Quotient.mk'' (anchor (owners j)).val : Q.Sorts),y⟩ :
          Sigma Q.Point)) →
      (∀ i j k : Fin n, ∃ x y z,
        rel i j x y ∧ rel i k x z ∧ rel j k y z) →
      (∀ i j : Fin n, ∀ x y, rel i j x y →
        originalSelectedCompleteAtomicMask Q
          (K (owners i)) (K (owners j))
          (fun (R : owners i ⟶ owners j) => chi.value R)
          (Q.source.colour x y) (bits i) (bits j)) →
      ∃ point : ∀ i : Fin n,
          Q.Point (Quotient.mk'' (anchor (owners i)).val),
        (∀ i j : Fin n, rel i j (point i) (point j)) ∧
        let old : Fin n → Sigma B.Point := fun i =>
          ⟨(anchor (owners i)).val,
            originalSelectedReachedEclassRepresentative
              A B P transport hOne Kroot E
                (anchor (owners i)) (point i)⟩
        ∃ f : Fin n ↪ phase.MarkedLimit B.cco,
          (∀ i, (phase.markedCoding B.cco).table.owner (f i) =
            APCharacter.Age.ownerEquiv B.source ((old i).1,bits i)) ∧
          ∀ i j, (phase.markedCoding B.cco).table.colour (f i) (f j) =
            APCharacter.Age.colourEquiv B.source
              (taggedColour B.source (old i) (old j))
  intro n owners rel bits hActual hReverse hDiagonal hSeparate hTriangles hMasks
  let D : ActualOrbitalDiagram B.G Q.Point (Fin n) := {
    sort := sort owners
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
  have hMasksReal : ∀ i j : Fin n,
      originalSelectedCompleteAtomicMask Q
        (K (owners i)) (K (owners j))
        (fun (R : owners i ⟶ owners j) => chi.value R)
        (Q.source.colour (point i) (point j))
        (bits i) (bits j) := by
    intro i j
    exact hMasks i j (point i) (point j) (hReal i j)
  obtain ⟨f,hOwners,hColours⟩ :=
    originalRetainedSelectedFiniteOrbitalOldMarkedWitness
      A B P transport tp hOne Kroot phase E hE
        n owners point bits hMasksReal hInjective
  exact ⟨point,hReal,⟨f,hOwners,hColours⟩⟩

end
end CCO.ExactEPGeometry
