import CCO.TransitionClosure.OriginalFirstHitCoverConnected

/-!
# B049 source07 C14-C15: a genuine first K-external quotient walk exists

For the ACTUAL original full invariant meet-irreducible J with
its FULL cover K, the proved old-G quotient connectivity includes K/J.
A genuine J-saturated Sbar state coming from P exiting J must therefore
eventually walk between some distinct J-classes inside one K-class.

If P avoids the real external K°\J° fine atoms, length one cannot do
so. Length zero is genuine J-quotient equality and cannot do so either.
The resulting witness has length AT LEAST TWO, with no shortcut
assumption about a quotient action, quotient SAP/CCO, or external-layer
reachability. The separate source hypothesis P meets J° gives TRUE
diagonal loops and hence power monotonicity when needed.
-/

universe u v w t

namespace CCO.TransitionClosure

variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)
variable {G : Type t} [Group G] [∀ s : ι, MulAction G (X s)]

open ParityHasse.Original
open CCO.TerminalLattice

/-- Original source C14/C15: a profile P truly exiting J but
avoiding K\J has some genuine Sbar-power of length >=2
joining DISTINCT original J-classes inside a single K-class.

The FULL meet-irreducible and full cover hypotheses discharge
the connectedness-to-K/J step. The proof does not assume that
Sbar stays in K/J; it may and typically does leave K/J. -/
theorem originalJMenuQuotientState_external_power_exists
    (H : HomogeneousSource S G)
    {i : ι} (J K : ColourEq S i)
    (hMI : letI : Lattice (ColourEq S i) :=
      ColourEq.lattice S H (i := i); InfIrred J)
    (hJK : letI : Lattice (ColourEq S i) :=
      ColourEq.lattice S H (i := i); J ⋖ K)
    (P : S.Menu i i)
    (hExit : ∃ a : S.Atom i i,
      a ∈ P ∧ a ∉ originalEquivDiversityPalette S J)
    (hAvoid : ∀ a : S.Atom i i,
      a ∈ P →
      a ∈ originalEquivDiversityPalette S K →
      a ∈ originalEquivDiversityPalette S J) :
    ∃ n : Nat, 2 ≤ n ∧
      ∃ x y : X i, K x y ∧ ¬ J x y ∧
        relPow (originalJMenuQuotientState S J P) n
          (Quotient.mk J.val x) (Quotient.mk J.val y) := by
  letI : Lattice (ColourEq S i) := ColourEq.lattice S H (i := i)
  have hNotLE : ¬ K ≤ J := not_le_of_gt hJK.1
  have hPair : ∃ x y : X i, K x y ∧ ¬ J x y := by
    by_contra hNone
    apply hNotLE
    intro x y hKxy
    by_contra hNotJ
    exact hNone ⟨x,y,hKxy,hNotJ⟩
  obtain ⟨x,y,hKxy,hNotJxy⟩ := hPair
  have hUpper : originalUpperSetoid S J K hJK.1.le
      (Quotient.mk J.val x) (Quotient.mk J.val y) :=
    (originalUpperSetoid_mk S J K hJK.1.le x y).mpr hKxy
  have hConnected :=
    originalJMenuQuotientConnected_contains_full_MI_cover
      S H J K hMI hJK P hExit
        (Quotient.mk J.val x) (Quotient.mk J.val y) hUpper
  obtain ⟨n,hWalk⟩ := hConnected
  have hNonzero : n ≠ 0 := by
    intro hZero
    have hZeroWalk := hWalk
    rw [hZero] at hZeroWalk
    have hClassEq : Quotient.mk J.val x = Quotient.mk J.val y := hZeroWalk
    exact hNotJxy (Quotient.exact hClassEq)
  have hNotOne : n ≠ 1 := by
    intro hOne
    have hOneWalk := hWalk
    rw [hOne] at hOneWalk
    have hR : originalJMenuQuotientState S J P
        (Quotient.mk J.val x) (Quotient.mk J.val y) :=
      (relPow_one (originalJMenuQuotientState S J P)
        (Quotient.mk J.val x) (Quotient.mk J.val y)).mp hOneWalk
    exact hNotJxy
      (originalJMenuQuotientState_K_inside_diagonal
        S J K hJK.1.le P hAvoid x y hKxy hR)
  have hAtLeastTwo : 2 ≤ n := by omega
  exact ⟨n,hAtLeastTwo,x,y,hKxy,hNotJxy,hWalk⟩

/-- True J-QUOTIENT diagonal inclusion makes every Sbar-power
monotone in its exponent. Each extra step is a REAL quotient
diagonal edge supplied by an original P atom in J°, not a
fictitious old STRONG identity atom. -/
theorem originalJMenuQuotientState_power_mono
    (H : HomogeneousSource S G)
    {i : ι} (J : ColourEq S i) (P : S.Menu i i)
    (hMeet : (P ∩ originalEquivDiversityPalette S J).Nonempty)
    (n : Nat) (q r : Quotient J.val)
    (h : relPow (originalJMenuQuotientState S J P) n q r) :
    relPow (originalJMenuQuotientState S J P) (n+1) q r :=
  ⟨q,originalJMenuQuotientState_contains_diagonal S H J P hMeet q,h⟩

end CCO.TransitionClosure
