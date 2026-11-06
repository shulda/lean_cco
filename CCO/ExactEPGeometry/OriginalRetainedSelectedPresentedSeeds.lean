import CCO.ExactEPGeometry.OriginalRetainedSelectedMaskReadout

/-!
# B062 C91–C93: finite presentations of actual selected gate-action points

The source C91 local equations are indexed by quotient vertices, which can
present the SAME projected K/E gate point several times. The genuine C92 gate
identity forces their bit prescriptions to agree. Hence the existing full
free-groupoid seed-extension provider applies to the *set* of actual points,
not to an artificially duplicated list. This lemma performs that descent
and gives ONE global compatible marking for EVERY prescribed vertex.

The result is deliberately conditional on the actual C91 pair-local
equations. Proving those equations from the real quotient atomic masks,
and transferring the resulting marked diagram to the genuine new source
age, remain separate C91/C94–C96 obligations.
-/

universe u v w t z

namespace CCO.ExactEPGeometry

open APCharacter
open APCharacter.Towers
open RigidGroupoid.Geometry
open CCO.RigidGroupoid.Phase
open CategoryTheory

noncomputable section

/-- For any finite family of actual selected K/E groupoid points, even
with repeated presentations of the same point, pairwise full-arrow
character equations imply existence of a SINGLE global full-character
marking attaining every prescribed bit. The real duplicate consistency
uses the whole gate identity and its character zero. -/
theorem originalRetainedSelectedPresentedSeedExtension
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
    letI := originalRetainedOccupancyGroupoid
      A B P transport tp hOne Kroot E hE
    let F := originalRetainedSelectedPointFunctor
      A B P transport tp hOne Kroot E hE
    let chi := originalRetainedSelectedOccupancyCharacter
      A B P transport tp hOne Kroot phase E hE
    ∀ {V : Type z} [Finite V]
      (points : V → Abstract.Point F) (bits : V → ZMod 2),
      (∀ (i j : V) (R : (points i).1 ⟶ (points j).1),
        F.map R (points i).2 = (points j).2 →
          bits j = bits i + chi.value R) →
      ∃ mark, Abstract.IsMarking F chi mark ∧
        ∀ i : V, mark (points i) = bits i := by
  let Occ := OriginalReachedOccupancy A B P (P.parent r)
    (fun i => hOne (P.parent r) i) E Kroot
  letI : Groupoid Occ :=
    originalRetainedOccupancyGroupoid A B P transport tp
      hOne Kroot E hE
  let F := originalRetainedSelectedPointFunctor
    A B P transport tp hOne Kroot E hE
  let chi := originalRetainedSelectedOccupancyCharacter
    A B P transport tp hOne Kroot phase E hE
  change ∀ {V : Type z} [Finite V]
    (points : V → Abstract.Point F) (bits : V → ZMod 2),
    (∀ (i j : V) (R : (points i).1 ⟶ (points j).1),
      F.map R (points i).2 = (points j).2 →
        bits j = bits i + chi.value R) →
    ∃ mark, Abstract.IsMarking F chi mark ∧
      ∀ i : V, mark (points i) = bits i
  intro V _ points bits hLocal
  classical
  have hDuplicate (i j : V) (hij : points i = points j) :
      bits i = bits j := by
    exact originalRetainedSelectedDuplicateBit
      A B P transport tp hOne Kroot phase E hE
      (points i) (points j) (bits i) (bits j) hij
      (fun R hR => hLocal i j R hR)
  let assignment : Abstract.Point F → ZMod 2 := fun q =>
    if h : ∃ i : V, points i = q then
      bits (Classical.choose h)
    else 0
  have assignment_spec (i : V) :
      assignment (points i) = bits i := by
    have h : ∃ j : V, points j = points i := ⟨i,rfl⟩
    dsimp [assignment]
    rw [dif_pos h]
    exact hDuplicate (Classical.choose h) i (Classical.choose_spec h)
  have hCompatible : Abstract.SeedCompatible F chi
      (Set.range points) assignment := by
    intro a b R q hsrc htgt
    obtain ⟨i, hi⟩ := hsrc
    obtain ⟨j, hj⟩ := htgt
    have hp := hLocal i j
    rw [hi, hj] at hp
    have hpair : bits j = bits i + chi.value R := hp R rfl
    calc
      assignment ⟨b,F.map R q⟩ = assignment (points j) :=
        congrArg assignment hj.symm
      _ = bits j := assignment_spec j
      _ = bits i + chi.value R := hpair
      _ = assignment (points i) + chi.value R :=
        congrArg (· + chi.value R) (assignment_spec i).symm
      _ = assignment ⟨a,q⟩ + chi.value R :=
        congrArg (· + chi.value R) (congrArg assignment hi)
  obtain ⟨mark, hMark, hOnRange⟩ :=
    (Abstract.exists_marking_extends_iff F
      (originalRetainedSelectedPointFunctor_free
        A B P transport tp hOne Kroot E hE)
      chi (Set.range points) assignment).mpr hCompatible
  exact ⟨mark, hMark, fun i =>
    (hOnRange (points i) ⟨i,rfl⟩).trans (assignment_spec i)⟩

end
end CCO.ExactEPGeometry
