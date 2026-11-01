import CCO.TerminalLattice.QuotientOrbitals
import CCO.ParityHasse.Original.ParitySeed

/-!
# B050 C13: connectedness of one complete quotient orbital at a FULL cover

This is the ORIGINAL source theorem's graph component statement. For an
actual full original invariant cover J ⋖ K and one external complete
quotient orbital of the SAME old full group, its connected components
are EXACTLY the K/J classes. No SAP, CCO, NR2, source exactness,
quotient homogeneity or independent quotient automorphism group occurs.

The generated equivalence is pulled back to the real original sort,
then the actual full cover, not a cover in an exact sublattice, applies.
-/

universe u v w t z

namespace CCO.TerminalLattice

/-- A motion preserves every RAW relational walk length whenever it
preserves each constituent edge. No graph finiteness assumed. -/
theorem relPow_group_invariant
    {A : Type u} {G : Type t} [Group G] [MulAction G A]
    (R : A → A → Prop)
    (hR : ∀ (g : G) x y, R x y → R (g • x) (g • y)) :
    ∀ (n : Nat) (g : G) x y,
      ParityHasse.Original.relPow R n x y →
      ParityHasse.Original.relPow R n (g • x) (g • y) := by
  intro n
  induction n with
  | zero =>
      intro g x y hxy
      change x = y at hxy
      subst y
      rfl
  | succ n ih =>
      intro g x y hxy
      obtain ⟨mid, hxm, hmy⟩ := hxy
      exact ⟨g • mid, hR g x mid hxm, ih g mid y hmy⟩

variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)
variable {G : Type t} [Group G] [∀ i : ι, MulAction G (X i)]

open ParityHasse.Original

/-- Full actual G-quotient orbital connectedness is an equivalence,
defined using genuine finite walks (including length zero equality). -/
def originalQuotientConnected (H : HomogeneousSource S G) {i : ι}
    (J : ColourEq S i) (a b : X i) : Setoid (Quotient J.val) :=
  connectivitySetoid (originalQuotientOrbital S (G := G) J a b)
    (originalQuotientOrbital_symmetric S H J a b)

/-- The new equivalence is invariant under precisely the induced OLD
G quotient action. Its original real pullback is therefore in the FULL
original invariant-equivalence lattice. -/
theorem originalQuotientConnected_invariant
    (H : HomogeneousSource S G) {i : ι}
    (J : ColourEq S i) (a b : X i) :
    letI : MulAction G (Quotient J.val) := originalQuotientAction S H J
    ∀ (g : G) q r,
      originalQuotientConnected S H J a b q r →
      originalQuotientConnected S H J a b (g • q) (g • r) := by
  letI : MulAction G (Quotient J.val) := originalQuotientAction S H J
  rintro g q r ⟨n, hn⟩
  exact ⟨n, relPow_group_invariant
    (originalQuotientOrbital S (G := G) J a b)
    (originalQuotientOrbital_invariant S H J a b)
    n g q r hn⟩

/-- Every edge in a complete external quotient orbital belonging to K
projects to two K-equivalent OLD endpoints. A non-full fine subset
would not suffice for the converse semantic lift. -/
theorem originalQuotientOrbital_le_upper
    (H : HomogeneousSource S G) {i : ι}
    (J K : ColourEq S i) (hJK : J ≤ K)
    (a b : X i) (hab : K a b) :
    ∀ q r,
      originalQuotientOrbital S (G := G) J a b q r →
        originalUpperSetoid S J K hJK q r := by
  rintro q r ⟨g, hq, hr⟩
  have hK : K (g • a) (g • b) :=
    colourInvariant_groupInvariant S H K.2 g a b hab
  change originalQuotientToUpper S J K hJK q =
    originalQuotientToUpper S J K hJK r
  rw [← hq, ← hr, originalQuotientToUpper_mk,
    originalQuotientToUpper_mk]
  exact Quotient.sound hK

/-- All paths in one external quotient orbital stay inside their
original K/J class. No connected-component conclusion is presumed. -/
theorem originalQuotientConnected_le_upper
    (H : HomogeneousSource S G) {i : ι}
    (J K : ColourEq S i) (hJK : J ≤ K)
    (a b : X i) (hab : K a b) :
    ∀ q r,
      originalQuotientConnected S H J a b q r →
        originalUpperSetoid S J K hJK q r := by
  rintro q r ⟨n, hn⟩
  exact relPow_le_setoid
    (originalQuotientOrbital S (G := G) J a b)
    (originalUpperSetoid S J K hJK)
    (originalQuotientOrbital_le_upper S H J K hJK a b hab)
    n q r hn

/-- SOURCE C13, with ALL original quantifiers: every component of a
single complete external G-orbital is precisely one actual K/J-class,
when J⋖K in the FULL original invariant lattice. Its proof needs no
SAP, CCO, NR2 or exactness. In particular no unverified quotient
graph-cover lemma is passed as a hypothesis. -/
theorem originalQuotientConnected_full_cover
    (H : HomogeneousSource S G) {i : ι}
    (J K : ColourEq S i) (hJK : J ⋖ K)
    (a b : X i) (hab : K a b) (hne : ¬ J a b) :
    ∀ q r : Quotient J.val,
      originalQuotientConnected S H J a b q r ↔
        originalUpperSetoid S J K hJK.le q r := by
  let C := originalQuotientConnected S H J a b
  have hInv : letI : MulAction G (Quotient J.val) :=
      originalQuotientAction S H J
      ∀ (g : G) q r, C q r → C (g • q) (g • r) :=
    originalQuotientConnected_invariant S H J a b
  have hUpper : ∀ x y : X i,
      C (Quotient.mk J.val x) (Quotient.mk J.val y) → K x y := by
    intro x y hxy
    exact (originalUpperSetoid_mk S J K hJK.le x y).mp
      (originalQuotientConnected_le_upper S H J K hJK.le a b hab
        (Quotient.mk J.val x) (Quotient.mk J.val y) hxy)
  have hCases := originalFullCover_quotient_eq_or_upper
    S H J K hJK C hInv hUpper
  have hRoot : C (Quotient.mk J.val a) (Quotient.mk J.val b) := by
    refine ⟨1, ?_⟩
    exact (relPow_one
      (originalQuotientOrbital S (G := G) J a b)
      (Quotient.mk J.val a) (Quotient.mk J.val b)).mpr
      (originalQuotientOrbital_root S (G := G) J a b)
  rcases hCases with hJ | hK
  · exact False.elim (hne ((hJ a b).mp hRoot))
  · intro q r
    refine Quotient.inductionOn₂ q r ?_
    intro x y
    exact (hK x y).trans (originalUpperSetoid_mk S J K hJK.le x y).symm

end CCO.TerminalLattice
