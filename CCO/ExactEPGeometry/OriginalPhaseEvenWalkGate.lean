import CCO.ExactEPGeometry.OriginalPhaseOddWalkParity

/-!
# B062 C100: even powers of the REAL phase-odd pivot lie in its full gate

Any actual arrow with the SAME displayed source and target kernel is
its own inverse: its full relation is symmetric under the original
homogeneous pair-flip. Therefore the complete composition of the
source phase distinguished odd Arrow with itself is the entire kernel
identity K, not logical point equality. If a real atom is contained
in that odd Arrow, EVERY two-step atomic walk is K-related and all
even walks remain K-related by transitivity. This derives the source
side K intersect X = Y together with the previously proved exclusion
of all odd walks from the whole K.

No assumption that K is logical identity, that the old atomic
relation is a function, or that quotient SAP holds is used.
-/

universe u v w t

namespace CCO.ExactEPGeometry

open APCharacter
open APCharacter.Towers
open RigidGroupoid.Geometry
open CCO.ParityHasse.Original

noncomputable section

/-- Any invariant equivalence absorbing every two-step R path also
absorbs EVERY even-length R walk, including genuine length zero.
No symmetry or seriality of R is assumed. -/
theorem evenWalk_subset_gate_of_twoStep
    {X : Type v} (K : Setoid X) (R : X → X → Prop)
    (hTwo : ∀ a z : X, (∃ m, R a m ∧ R m z) → K.r a z) :
    ∀ a z : X, EvenWalk R a z → K.r a z := by
  have hAll : ∀ k : Nat, ∀ a z : X,
      relPow R (2*k) a z → K.r a z := by
    intro k
    induction k with
    | zero =>
        intro a z h
        have haz : a = z := h
        subst z
        exact K.refl a
    | succ k ih =>
        intro a z h
        have hsum : relPow R (2*k+2) a z := by
          simpa only [Nat.mul_succ] using h
        have hSplit : RawSymmetric.compose
            (relPow R (2*k)) (relPow R 2) a z := by
          exact (Iff.of_eq (congrFun
            (congrFun (relPow_add R (2*k) 2) a) z)).mp hsum
        obtain ⟨m,ham,hmz⟩ := hSplit
        have hmz2 : ∃ s, R m s ∧ R s z := by
          change (∃ s, R m s ∧ ∃ q, R s q ∧ q = z) at hmz
          obtain ⟨s,hms,q,hsq,hqz⟩ := hmz
          subst q
          exact ⟨s,hms,hsq⟩
        exact K.trans (ih a m ham) (hTwo m z hmz2)
  intro a z hEven
  obtain ⟨k,rfl⟩ := even_iff_exists_two_mul.mp hEven.2.1
  exact hAll k a z hEven.2.2

/-- On the true reached original kernel K_b, all even walks of ANY
actual atom contained in the source-certified odd Arrow are K_b-related.
The Arrow self-square is proved from the actual symmetric source and
its full exact bridge composition, not from a hypothesized functional
involution on old points. -/
theorem originalPhaseOddAtom_evenWalk_inGate
    (B : CurrentSource.{u,v,w,t})
    {r : B.Sorts} (Kroot : Kernel B.source r)
    (phase : SourcePhase B.source B.homogeneous
      (exactCalculus_of_homogeneous_CCO
        B.source B.homogeneous B.cco) Kroot)
    (b : Reached B.source Kroot)
    (c : B.source.Atom b.val b.val)
    (hContained : ∀ x y : B.Point b.val,
      B.source.atomRel c x y → (phase.atSort b).rel x y)
    (x y : B.Point b.val)
    (hEven : EvenWalk (B.source.atomRel c) x y) :
    (Reached.kernel B.homogeneous
      (exactCalculus_of_homogeneous_CCO
        B.source B.homogeneous B.cco) b).rel x y := by
  let C := exactCalculus_of_homogeneous_CCO
    B.source B.homogeneous B.cco
  let K := Reached.kernel B.homogeneous C b
  let odd := phase.atSort b
  have hInv : odd.inv = odd :=
    Arrow.ext (odd.exact.same_sort_converse B.source B.homogeneous)
  have hSquare : odd.comp C odd = Arrow.id K := by
    have hs := Arrow.comp_inv C odd
    rw [hInv] at hs
    exact hs
  have hTwo : ∀ a z : B.Point b.val,
      (∃ m, B.source.atomRel c a m ∧
        B.source.atomRel c m z) → K.rel a z := by
    rintro a z ⟨m,ham,hmz⟩
    have hAA : (odd.comp C odd).rel a z :=
      ⟨m,hContained a m ham,hContained m z hmz⟩
    have h := congrFun (congrFun
      (congrArg Arrow.rel hSquare) a) z
    exact (Iff.of_eq h).mp hAA
  exact evenWalk_subset_gate_of_twoStep K.setoid
    (B.source.atomRel c) hTwo x y hEven

/-- The source C100 complement relation at the true old reached sort:
K intersects the entire c-connectivity EXACTLY in the entire c-even
profile, because odd profiles avoid K and even profiles lie inside K.
This remains valid when K has nontrivial classes of old real points. -/
theorem originalPhaseOddAtom_gate_inter_connected_iff_even
    (B : CurrentSource.{u,v,w,t})
    {r : B.Sorts} (Kroot : Kernel B.source r)
    (phase : SourcePhase B.source B.homogeneous
      (exactCalculus_of_homogeneous_CCO
        B.source B.homogeneous B.cco) Kroot)
    (b : Reached B.source Kroot)
    (c : B.source.Atom b.val b.val)
    (hContained : ∀ x y : B.Point b.val,
      B.source.atomRel c x y → (phase.atSort b).rel x y)
    (x y : B.Point b.val) :
    ((Reached.kernel B.homogeneous
      (exactCalculus_of_homogeneous_CCO
        B.source B.homogeneous B.cco) b).rel x y ∧
      ConnectedWalk (B.source.atomRel c) x y) ↔
      EvenWalk (B.source.atomRel c) x y := by
  constructor
  · rintro ⟨hGate,hConn⟩
    rcases (connectedWalk_iff_even_or_odd
      (B.source.atomRel c) x y).mp hConn with he | ho
    · exact he
    · obtain ⟨n,hn,hWalk⟩ := ho
      exact False.elim
        ((originalPhaseOddAtom_oddWalk_outsideGate
          B Kroot phase b c hContained n hn x y hWalk) hGate)
  · intro he
    exact ⟨originalPhaseOddAtom_evenWalk_inGate
        B Kroot phase b c hContained x y he,
      (connectedWalk_iff_even_or_odd
        (B.source.atomRel c) x y).mpr (Or.inl he)⟩

end
end CCO.ExactEPGeometry
