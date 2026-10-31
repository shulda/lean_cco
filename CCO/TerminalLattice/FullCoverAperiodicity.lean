import CCO.TerminalLattice.FullCoverParity
import Mathlib.Algebra.Ring.Parity

/-!
# B050 C16: local non-index-two FULL cover yields long quotient walks

Every complete quotient orbital uses the original ambient full G-action,
not a reduct group. No original CCO, SAP, global NR2, exactness or
distributivity is needed in this graph argument.

C14 has proved that if all quotient odd closed walks are absent, the
actual relative [K:J] is exactly two. Original source transitivity
transports any missing odd cycle to every quotient vertex. Therefore
local index != 2 supplies an odd closed walk at EVERY quotient vertex,
and a route, odd detour and two-edge backtracks yield every large length.
Finiteness of quotient pair-orbits is the separate C17 uniformisation.
-/

universe u v w t

namespace CCO.TerminalLattice

open ParityHasse.Original

/-- Two-edge immediate returns permit literal length padding of ANY
finite undirected serial relational walk, including closed walks.
No synthetic identity edge is introduced. -/
theorem relPow_pad_two
    {A : Type u} (R : A → A → Prop)
    (hs : ∀ x y, R x y → R y x)
    (hser : ∀ x, ∃ y, R x y)
    {x y : A} {n : Nat}
    (h : relPow R n x y) (k : Nat) :
    relPow R (n+2*k) x y := by
  induction k with
  | zero => simpa only [Nat.mul_zero, Nat.add_zero] using h
  | succ k ih =>
      have hp := relPow_mono_two R hs hser (n+2*k) x y ih
      convert hp using 1 <;> omega

/-- Connected endpoints admitting an odd closed detour at the FIRST
endpoint have R-walks of every sufficiently large exact length.
Both x=y and x!=y are covered, with genuine positive loops. -/
theorem relPow_all_large_of_odd_detour
    {A : Type u} (R : A → A → Prop)
    (hs : ∀ x y, R x y → R y x)
    (hser : ∀ x, ∃ y, R x y)
    {x y : A}
    (reach : ∃ l, relPow R l x y)
    (oddLoop : ∃ m, Odd m ∧ relPow R m x x) :
    ∃ N : Nat, 0 < N ∧
      ∀ n, N ≤ n → relPow R n x y := by
  obtain ⟨l, hl⟩ := reach
  obtain ⟨m, hmOdd, hmClosed⟩ := oddLoop
  have hDetour : relPow R (m+l) x y := by
    rw [relPow_add]
    exact ⟨x, hmClosed, hl⟩
  have hmPos : 0 < m := by
    have hm := Nat.odd_iff.mp hmOdd
    omega
  refine ⟨m+l, by omega, ?_⟩
  intro n hn
  rcases Nat.even_or_odd (n-l) with he | ho
  · obtain ⟨k, hk⟩ := he
    have heq : n = l+2*k := by omega
    rw [heq]
    exact relPow_pad_two R hs hser hl k
  · have he : Even (n-(m+l)) := by
      apply Nat.even_iff.mpr
      have h₁ := Nat.odd_iff.mp hmOdd
      have h₂ := Nat.odd_iff.mp ho
      omega
    obtain ⟨k, hk⟩ := he
    have heq : n = (m+l)+2*k := by omega
    rw [heq]
    exact relPow_pad_two R hs hser hDetour k

variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)
variable {G : Type t} [Group G] [∀ i : ι, MulAction G (X i)]

/-- Actual original sort transitivity descends to its literal
quotient J under the SAME G action. No quotient homogeneity is assumed. -/
theorem originalQuotient_transitive
    (H : HomogeneousSource S G) {i : ι}
    (J : ParityHasse.Original.ColourEq S i) :
    letI : MulAction G (Quotient J.val) := originalQuotientAction S H J
    ∀ q r : Quotient J.val, ∃ g : G, g • q = r := by
  letI : MulAction G (Quotient J.val) := originalQuotientAction S H J
  intro q r
  refine Quotient.inductionOn₂ q r ?_
  intro x y
  obtain ⟨g, hgy⟩ := S.original_sort_transitive_of_homogeneous H i x y
  refine ⟨g, ?_⟩
  change Quotient.mk J.val (g • x) = Quotient.mk J.val y
  exact congrArg (Quotient.mk J.val) hgy

/-- A complete quotient orbital is serial at every actual J-class,
including when that class is represented by any chosen old real point.
It uses no original SAP. -/
theorem originalQuotientOrbital_serial
    (H : HomogeneousSource S G) {i : ι}
    (J : ParityHasse.Original.ColourEq S i) (a b : X i) :
    ∀ q : Quotient J.val,
      ∃ r, originalQuotientOrbital S (G := G) J a b q r := by
  intro q
  refine Quotient.inductionOn q ?_
  intro x
  obtain ⟨g, hga⟩ := S.original_sort_transitive_of_homogeneous H i a x
  refine ⟨Quotient.mk J.val (g • b), g, ?_, rfl⟩
  exact congrArg (Quotient.mk J.val) hga

/-- Under a FULL original cover J⋖K, local [K:J] != 2 forces an
ACTUAL odd closed walk of the external complete quotient orbital at
EVERY quotient point. This does not postulate nonbipartiteness or a
quotient parity provider. -/
theorem originalQuotient_odd_closed_of_nonindex_two
    (H : HomogeneousSource S G) {i : ι}
    (J K : ParityHasse.Original.ColourEq S i) (hJK : J ⋖ K)
    (a b : X i) (hab : K a b) (hne : ¬ J a b)
    (hNotTwo : ParityHasse.Original.relativeIndex J.val K.val a ≠ 2)
    (q : Quotient J.val) :
    ∃ m : Nat, Odd m ∧
      ParityHasse.Original.relPow
        (originalQuotientOrbital S (G := G) J a b) m q q := by
  classical
  let R := originalQuotientOrbital S (G := G) J a b
  letI : MulAction G (Quotient J.val) := originalQuotientAction S H J
  by_contra hAbsent
  have hNoOddAtQ (n : Nat) (hn : Odd n) : ¬ ParityHasse.Original.relPow R n q q := by
    intro h
    exact hAbsent ⟨n, hn, h⟩
  have hNoOddAll :
      ∀ (r : Quotient J.val) (n : Nat), Odd n →
        ¬ ParityHasse.Original.relPow R n r r := by
    intro r n hn hrr
    obtain ⟨g, hgr⟩ := originalQuotient_transitive S H J q r
    have hback :=
      relPow_group_invariant R
        (originalQuotientOrbital_invariant S H J a b)
        n g⁻¹ r r hrr
    have hq : g⁻¹ • r = q := by
      rw [← hgr]
      exact inv_smul_smul g q
    have hqq : ParityHasse.Original.relPow R n q q := by
      simpa only [hq] using hback
    exact hNoOddAtQ n hn hqq
  exact hNotTwo (originalQuotient_noOdd_index_two
    S H J K hJK a b hab hne hNoOddAll)

/-- SOURCE C16: outside the LOCAL index-two cover, every ordered pair
in the same actual K/J-class, including q=r, admits walks of EVERY
sufficiently large exact length. CCO, SAP, global NR2 and exactness
are absent, and no uniform N over pairs is claimed yet (C17). -/
theorem originalQuotient_all_large_walks
    (H : HomogeneousSource S G) {i : ι}
    (J K : ParityHasse.Original.ColourEq S i) (hJK : J ⋖ K)
    (a b : X i) (hab : K a b) (hne : ¬ J a b)
    (hNotTwo : ParityHasse.Original.relativeIndex J.val K.val a ≠ 2)
    (q r : Quotient J.val)
    (hqr : originalUpperSetoid S J K hJK.le q r) :
    ∃ N : Nat, 0 < N ∧
      ∀ n, N ≤ n →
        ParityHasse.Original.relPow
          (originalQuotientOrbital S (G := G) J a b) n q r := by
  let R := originalQuotientOrbital S (G := G) J a b
  have hReach : ∃ l, ParityHasse.Original.relPow R l q r :=
    (originalQuotientConnected_full_cover
      S H J K hJK a b hab hne q r).mpr hqr
  have hOdd :=
    originalQuotient_odd_closed_of_nonindex_two
      S H J K hJK a b hab hne hNotTwo q
  exact relPow_all_large_of_odd_detour R
    (originalQuotientOrbital_symmetric S H J a b)
    (originalQuotientOrbital_serial S H J a b)
    hReach hOdd

end CCO.TerminalLattice
