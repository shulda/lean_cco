import CCO.TerminalLattice.FullCoverConnectivity
import CCO.ParityHasse.Original.RelativeIndices

/-!
# B050 C14: bipartite full-quotient orbital components force index two

No SAP, CCO, global NR2, assumed quotient completion or exact
sublattice enters this source argument. An old FULL invariant cover
J⋖K controls the invariant even-walk equivalence on ACTUAL J-classes.
If no odd closed walk exists, the even-walk relation cannot equal K/J
because the specified non-diagonal quotient orbital has an odd edge;
therefore it is the true quotient diagonal. Connectivity then yields
exactly the two ORIGINAL J-classes of an original K-class.
-/

universe u v w t

namespace CCO.TerminalLattice

variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)
variable {G : Type t} [Group G] [∀ i : ι, MulAction G (X i)]

open ParityHasse.Original

/-- Actual even walks of a complete external OLD quotient orbital. -/
def originalQuotientEven (H : HomogeneousSource S G) {i : ι}
    (J : ColourEq S i) (a b : X i) : Setoid (Quotient J.val) :=
  evenSetoid (originalQuotientOrbital S (G := G) J a b)
    (originalQuotientOrbital_symmetric S H J a b)

/-- Parity equivalence is invariant under the SAME induced old G
action. This proves the precise full-lattice eligibility of the parity
test, without an extra equivariance axiom. -/
theorem originalQuotientEven_invariant
    (H : HomogeneousSource S G) {i : ι}
    (J : ColourEq S i) (a b : X i) :
    letI : MulAction G (Quotient J.val) := originalQuotientAction S H J
    ∀ (g : G) q r,
      originalQuotientEven S H J a b q r →
      originalQuotientEven S H J a b (g • q) (g • r) := by
  letI : MulAction G (Quotient J.val) := originalQuotientAction S H J
  rintro g q r ⟨n, hnEven, hnWalk⟩
  exact ⟨n, hnEven, relPow_group_invariant
    (originalQuotientOrbital S (G := G) J a b)
    (originalQuotientOrbital_invariant S H J a b)
    n g q r hnWalk⟩

/-- In the absence of odd quotient closed walks, FULL original
cover prevents any nontrivial even-walk equivalence above the true
quotient diagonal. The root orbital edge is genuinely non-diagonal. -/
theorem originalQuotientEven_eq_diagonal_of_noOdd
    (H : HomogeneousSource S G) {i : ι}
    (J K : ColourEq S i) (hJK : J ⋖ K)
    (a b : X i) (hab : K a b) (hne : ¬ J a b)
    (noOdd : ∀ (q : Quotient J.val) (n : Nat), Odd n →
      ¬ relPow (originalQuotientOrbital S (G := G) J a b) n q q) :
    ∀ q r : Quotient J.val,
      originalQuotientEven S H J a b q r ↔ q = r := by
  let R := originalQuotientOrbital S (G := G) J a b
  let E := originalQuotientEven S H J a b
  have hFull := originalQuotientConnected_full_cover S H J K hJK a b hab hne
  have hEvenUpper : ∀ x y : X i,
      E (Quotient.mk J.val x) (Quotient.mk J.val y) → K x y := by
    rintro x y ⟨n, _, hnWalk⟩
    exact (originalUpperSetoid_mk S J K hJK.le x y).mp
      ((hFull _ _).mp ⟨n, hnWalk⟩)
  have hCases := originalFullCover_quotient_eq_or_upper
    S H J K hJK E (originalQuotientEven_invariant S H J a b) hEvenUpper
  rcases hCases with hJ | hK
  · intro q r
    refine Quotient.inductionOn₂ q r ?_
    intro x y
    exact (hJ x y).trans (Quotient.eq).symm
  · have hEven : EvenWalk R (Quotient.mk J.val a) (Quotient.mk J.val b) :=
      (hK a b).mpr hab
    have hOdd : OddWalk R (Quotient.mk J.val a) (Quotient.mk J.val b) :=
      ⟨1, odd_one, (relPow_one R _ _).mpr
        (originalQuotientOrbital_root S (G := G) J a b)⟩
    exact False.elim ((even_odd_disjoint R
      (originalQuotientOrbital_symmetric S H J a b) noOdd
      (Quotient.mk J.val a) (Quotient.mk J.val b)) ⟨hEven, hOdd⟩)

/-- The two literal J-classes inside K[a] are represented by a and
its external orbital neighbour b. There is no global index hypothesis,
only the actual FULL original cover and the absence of odd quotient walks. -/
theorem originalQuotient_noOdd_two_classes
    (H : HomogeneousSource S G) {i : ι}
    (J K : ColourEq S i) (hJK : J ⋖ K)
    (a b : X i) (hab : K a b) (hne : ¬ J a b)
    (noOdd : ∀ (q : Quotient J.val) (n : Nat), Odd n →
      ¬ relPow (originalQuotientOrbital S (G := G) J a b) n q q) :
    ∀ x : X i, K a x ↔ J a x ∨ J b x := by
  let R := originalQuotientOrbital S (G := G) J a b
  have hs := originalQuotientOrbital_symmetric S H J a b
  have hEven := originalQuotientEven_eq_diagonal_of_noOdd
    S H J K hJK a b hab hne noOdd
  have hConn := originalQuotientConnected_full_cover
    S H J K hJK a b hab hne
  let qa : Quotient J.val := Quotient.mk J.val a
  let qb : Quotient J.val := Quotient.mk J.val b
  have hRoot : R qa qb := originalQuotientOrbital_root S (G := G) J a b
  intro x
  constructor
  · intro hKax
    have hC : ConnectedWalk R qa (Quotient.mk J.val x) :=
      (hConn qa (Quotient.mk J.val x)).mpr
        ((originalUpperSetoid_mk S J K hJK.le a x).mpr hKax)
    rcases (connectedWalk_iff_even_or_odd R qa (Quotient.mk J.val x)).mp hC with he | ho
    · exact Or.inl (Quotient.exact ((hEven qa (Quotient.mk J.val x)).mp he))
    · obtain ⟨n, hnOdd, hnWalk⟩ := ho
      have hReverse : relPow R n (Quotient.mk J.val x) qa :=
        relPow_symmetric R hs n qa (Quotient.mk J.val x) hnWalk
      have hNext : relPow R (n+1) (Quotient.mk J.val x) qb := by
        rw [relPow_add]
        exact ⟨qa, hReverse, (relPow_one R qa qb).mpr hRoot⟩
      have hEvenBX : EvenWalk R (Quotient.mk J.val x) qb :=
        ⟨n+1, hnOdd.add_one, hNext⟩
      exact Or.inr (J.val.symm (Quotient.exact
        ((hEven (Quotient.mk J.val x) qb).mp hEvenBX)))
  · rintro (hJax | hJbx)
    · exact hJK.le hJax
    · exact K.val.trans hab (hJK.le hJbx)

/-- C14: absent odd walks force EXACT local [K:J]=2 at an original
point, even if K is proper and neither equivalence is exact/represented.
This is not an assumed "index-two" graph oracle. -/
theorem originalQuotient_noOdd_index_two
    (H : HomogeneousSource S G) {i : ι}
    (J K : ColourEq S i) (hJK : J ⋖ K)
    (a b : X i) (hab : K a b) (hne : ¬ J a b)
    (noOdd : ∀ (q : Quotient J.val) (n : Nat), Odd n →
      ¬ relPow (originalQuotientOrbital S (G := G) J a b) n q q) :
    relativeIndex J.val K.val a = 2 := by
  let Q := RelativeClass J.val K.val a
  let qa : Q := Quotient.mk _ ⟨a, K.val.refl a⟩
  let qb : Q := Quotient.mk _ ⟨b, hab⟩
  have hdiff : qa ≠ qb := by
    intro heq
    have hJ := Quotient.exact heq
    exact hne hJ
  apply Nat.card_eq_two_iff.mpr
  refine ⟨qa, qb, hdiff, ?_⟩
  apply Set.eq_univ_iff_forall.mpr
  intro q
  refine Quotient.inductionOn q ?_
  intro x
  rcases (originalQuotient_noOdd_two_classes S H J K hJK a b hab hne noOdd
      x.val).mp x.property with hx | hx
  · exact Or.inl (Quotient.sound (J.val.symm hx))
  · exact Or.inr (Quotient.sound (J.val.symm hx))

end CCO.TerminalLattice
