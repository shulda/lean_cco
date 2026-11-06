import CCO.ExactEPGeometry.OriginalPhaseEvenWalkGate
import CCO.ParityHasse.Relative.Gate

/-!
# B062 C103: actual full SourcePhase kernels are maximal parity gates

A real SourcePhase already contains a nonidentity dominant full odd Arrow
at every actually reached object. Choose a genuine atom inside that whole
Arrow. Its even walks lie in the complete kernel, its odd walks avoid the
kernel, and every strictly larger full RAW-exact equivalence contains that
atom by the SAME Arrow dominance. Thus the actual kernel, without replacing
it by another existential gate, is maximal among ALL parity complements.

The genuine positive RAW parity presentations then construct a complete
MaximalGate certificate with precisely that same kernel. Logical identity
and the full gate identity remain distinct. No quotient SAP, new maximality
premise, selected orbit, or replacement SourcePhase is supplied.
-/

universe u v w t
namespace CCO.ExactEPGeometry
open APCharacter APCharacter.Towers RigidGroupoid.Geometry
open CCO.ParityHasse.Original CCO.ParityHasse.Relative
noncomputable section

variable (B : CurrentSource.{u,v,w,t})
variable {r : B.Sorts} (Kroot : Kernel B.source r)
variable (phase : SourcePhase B.source B.homogeneous
  (exactCalculus_of_homogeneous_CCO B.source B.homogeneous B.cco) Kroot)

/-- Every actual odd-arrow atom certifies maximality of the SAME full
reached kernel, with maximality quantified over all full-exact candidates. -/
theorem actualPhaseOddAtom_maximalCandidate
    (b : Reached B.source Kroot)
    (c : B.source.Atom b.val b.val)
    (hContained : ∀ x y : B.Point b.val,
      B.source.atomRel c x y → (phase.atSort b).rel x y) :
    let C := exactCalculus_of_homogeneous_CCO B.source B.homogeneous B.cco
    let K := Reached.kernel B.homogeneous C b
    Maximal (Candidate B.source
      (evenColourEq B.source B.homogeneous c)
      (connectivityColourEq B.source B.homogeneous c))
      (current_kernel_exact_eq B K).val := by
  let C := exactCalculus_of_homogeneous_CCO B.source B.homogeneous B.cco
  let K := Reached.kernel B.homogeneous C b
  let Kc := (current_kernel_exact_eq B K).val
  let Y := evenColourEq B.source B.homogeneous c
  let U := connectivityColourEq B.source B.homogeneous c
  letI : PartialOrder (Kernel B.source b.val) := kernelPartialOrder B.source b.val
  have hYK : Y ≤ Kc := by
    intro x y h
    exact originalPhaseOddAtom_evenWalk_inGate B Kroot phase b c hContained x y h
  have hMeet : Kc ⊓ U = Y := by
    apply ColourEq.ext B.source b.val
    intro x y
    exact originalPhaseOddAtom_gate_inter_connected_iff_even B Kroot phase b c hContained x y
  refine ⟨⟨K.exact,hYK,hMeet⟩,?_⟩
  intro Z hZ hKZ
  by_cases hZK : Z ≤ Kc
  · exact hZK
  · let Zk : Kernel B.source b.val := ⟨Z.val,hZ.1⟩
    have hStrict : K < Zk := by
      refine lt_iff_le_and_ne.mpr ⟨hKZ,?_⟩
      intro hEq
      apply hZK
      intro x y hxy
      change K.rel x y
      rw [hEq]
      exact hxy
    obtain ⟨x,y,hAtom⟩ := B.source.realized c
    have hZxy : Z x y := phase.atSort_dominant b Zk hStrict x y (hContained x y hAtom)
    have hConn : U x y := ⟨1,(relPow_one (B.source.atomRel c) x y).mpr hAtom⟩
    have hEven : Y x y := by
      have h : (Z ⊓ U) x y := ⟨hZxy,hConn⟩
      rw [hZ.2.2] at h
      exact h
    have hGate : K.rel x y := hYK hEven
    have hOdd : relPow (B.source.atomRel c) 1 x y :=
      (relPow_one (B.source.atomRel c) x y).mpr hAtom
    exact False.elim
      ((originalPhaseOddAtom_oddWalk_outsideGate B Kroot phase b c hContained
        1 odd_one x y hOdd) hGate)

/-- Every ACTUAL SourcePhase gives a real reachable bipartite pivot,
its full index-two parity interval, and a genuine maximal gate whose kernel
is EXACTLY the existing reached kernel. The supplied phase and character
are retained; no new phase is selected from the maximal gate. -/
theorem actualPhaseAtSort_maximalGate
    (b : Reached B.source Kroot) :
    let C := exactCalculus_of_homogeneous_CCO B.source B.homogeneous B.cco
    let K := Reached.kernel B.homogeneous C b
    ∃ c : B.source.Atom b.val b.val,
      (∀ x y : B.Point b.val,
        B.source.atomRel c x y → (phase.atSort b).rel x y) ∧
      (∀ x : B.Point b.val, ∀ n : Nat,
        Odd n → ¬relPow (B.source.atomRel c) n x x) ∧
      (∀ x : B.Point b.val,
        relativeIndex (evenColourEq B.source B.homogeneous c).val
          (connectivityColourEq B.source B.homogeneous c).val x = 2) ∧
      ∃ M : MaximalGate B.source B.homogeneous
        (evenColourEq B.source B.homogeneous c)
        (connectivityColourEq B.source B.homogeneous c),
        M.kernel = (current_kernel_exact_eq B K).val := by
  let C := exactCalculus_of_homogeneous_CCO B.source B.homogeneous B.cco
  let K := Reached.kernel B.homogeneous C b
  let Kc := (current_kernel_exact_eq B K).val
  obtain ⟨c,_hNonempty,hAtom⟩ := originalReachedPhaseOdd_hasDiversAtomicPivot B Kroot phase b
  have hContained : ∀ x y : B.Point b.val,
      B.source.atomRel c x y → (phase.atSort b).rel x y := fun x y h => (hAtom x y h).1
  have hNoOdd : ∀ x : B.Point b.val, ∀ n : Nat,
      Odd n → ¬relPow (B.source.atomRel c) n x x := by
    intro x n hn hPath
    exact (originalPhaseOddAtom_oddWalk_outsideGate B Kroot phase b c hContained
      n hn x x hPath) (K.setoid.refl x)
  let Y := evenColourEq B.source B.homogeneous c
  let U := connectivityColourEq B.source B.homogeneous c
  have hIndex : ∀ x : B.Point b.val, relativeIndex Y.val U.val x = 2 :=
    parity_seed_index_two B.source B.homogeneous c hNoOdd
  have hMax : Maximal (Candidate B.source Y U) Kc :=
    actualPhaseOddAtom_maximalCandidate B Kroot phase b c hContained
  obtain ⟨_Ye,O,_hYe,hO⟩ := parity_profiles_nonempty_exact B.source B.homogeneous c
  have hOddRel : odd Y.val U.val = OddWalk (B.source.atomRel c) := by
    funext x y
    apply propext
    constructor
    · rintro ⟨hConn,hNotEven⟩
      rcases (connectedWalk_iff_even_or_odd (B.source.atomRel c) x y).mp hConn with hEven | hOdd
      · exact False.elim (hNotEven hEven)
      · exact hOdd
    · intro hOdd
      refine ⟨(connectedWalk_iff_even_or_odd (B.source.atomRel c) x y).mpr (Or.inr hOdd),?_⟩
      intro hEven
      exact (even_odd_disjoint (B.source.atomRel c)
        (fun x y h => by
          change B.source.colour y x = some c
          have hs := (B.source.colour_swap x y c).mp h
          simpa only [B.source.symmetricLoop c] using hs) hNoOdd x y) ⟨hEven,hOdd⟩
  have hOddExact : Exact B.source (odd Y.val U.val) := by
    refine ⟨O,?_⟩
    rw [hOddRel]
    funext x y
    exact propext (hO x y)
  let a : B.Point b.val := Classical.choice (B.source.nonemptySort b.val)
  let M : MaximalGate B.source B.homogeneous Y U := {
    kernel := Kc
    maximal := hMax
    exact := gate_exact B.source B.homogeneous B.cco Y U Kc hMax.1.1 hOddExact
    bisaturated := gate_bisaturated B.source B.homogeneous Y U Kc hMax.1.2.1 hMax.1.2.2
    square := gate_square B.source B.homogeneous Y U Kc hMax.1.2.1 hMax.1.2.2 a (hIndex a)
    split := gate_partition B.source B.homogeneous Y U Kc hMax.1.2.1 hMax.1.2.2
    disjoint := gate_disjoint B.source B.homogeneous Y U Kc hMax.1.2.1 hMax.1.2.2
    relative_index :=
      (relativeIndex_uniform B.source B.homogeneous Kc
        (ColourEq.join B.source B.homogeneous Kc U) a _).symm.trans
        (maximal_transposition_index B.source B.homogeneous Y U Kc hMax.1.2.2 a (hIndex a))
    dominant := gate_dominance B.source B.homogeneous Y U Kc
      (even_le_connectivity B.source B.homogeneous c) a (hIndex a) hMax
  }
  exact ⟨c,hContained,hNoOdd,hIndex,M,rfl⟩

include phase in
/-- The root form keeps precisely the original supplied SourcePhase kernel,
so its canonical successor is a genuine maximal-character construction. -/
theorem actualPhaseRoot_maximalGate :
    ∃ c : B.source.Atom r r,
      (∀ x : B.Point r, ∀ n : Nat,
        Odd n → ¬relPow (B.source.atomRel c) n x x) ∧
      (∀ x : B.Point r,
        relativeIndex (evenColourEq B.source B.homogeneous c).val
          (connectivityColourEq B.source B.homogeneous c).val x = 2) ∧
      ∃ M : MaximalGate B.source B.homogeneous
        (evenColourEq B.source B.homogeneous c)
        (connectivityColourEq B.source B.homogeneous c),
        M.kernel = (current_kernel_exact_eq B Kroot).val := by
  let C := exactCalculus_of_homogeneous_CCO B.source B.homogeneous B.cco
  obtain ⟨c,_hContained,hNoOdd,hIndex,M,hKernel⟩ :=
    actualPhaseAtSort_maximalGate B Kroot phase (Reached.root Kroot)
  refine ⟨c,hNoOdd,hIndex,M,?_⟩
  exact hKernel.trans (congrArg (fun K => (current_kernel_exact_eq B K).val)
    (Reached.root_kernel B.homogeneous C (A := Kroot)))

end
end CCO.ExactEPGeometry
