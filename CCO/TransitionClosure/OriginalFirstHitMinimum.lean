import CCO.TransitionClosure.OriginalFirstHitPowerExistence
import Mathlib.Data.Nat.Find

/-!
# B049 source07 OWI C15-C16: genuine LEAST original K-external Sbar power

The first-hit quotient walk is not guessed or supplied as an oracle:
original FULL MI J with its FULL cover K forces old Sbar connectedness
to cover K/J, and an actual representative pair supplies some
K-external exact-length walk of length at least two. Since lengths
are natural numbers, choose the least genuine hit by Nat.find.

No length zero or length one can be a K-external first hit:
zero means true quotient equality and one would contradict the
proved OWI-S exclusion of K/J-offdiagonal Sbar edges.
Hence the resulting n is >=2 and every smaller exponent misses
K/J external, *including* 0 and 1.

No new old SAP/CCO, quotient CCO/SAP, source index-two hypothesis,
synthetic STRONG diagonal or extra reachability premise is used.
-/

universe u v w t

namespace CCO.TransitionClosure

variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)
variable {G : Type t} [Group G] [∀ s : ι, MulAction G (X s)]

open ParityHasse.Original
open CCO.TerminalLattice

/-- Exact finite K-external hit at one quotient-power exponent.
The witness carries ACTUAL old representatives and their full
K/J external class distinction, not an abstract quotient edge. -/
def OriginalJMenuKExternalHit
    {i : ι} (J K : ColourEq S i) (P : S.Menu i i)
    (n : Nat) : Prop :=
  ∃ x y : X i, K x y ∧ ¬ J x y ∧
    relPow (originalJMenuQuotientState S J P) n
      (Quotient.mk J.val x) (Quotient.mk J.val y)

/-- Source07 least first-hit exponent, genuinely DERIVED
from the original full MI-cover and the old raw word state P.
Every earlier exact-length quotient power misses the external
layer. Subsequent OWI-ST uses this strict minimality at n-1. -/
theorem originalJMenuQuotientState_least_external_power
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
      OriginalJMenuKExternalHit S J K P n ∧
      ∀ m : Nat, m < n →
        ¬ OriginalJMenuKExternalHit S J K P m := by
  classical
  obtain ⟨N, _hN, x, y, hKxy, hNotJxy, hWalk⟩ :=
    originalJMenuQuotientState_external_power_exists
      S H J K hMI hJK P hExit hAvoid
  have hExist : ∃ n : Nat, OriginalJMenuKExternalHit S J K P n :=
    ⟨N,x,y,hKxy,hNotJxy,hWalk⟩
  let n := Nat.find hExist
  have hHit : OriginalJMenuKExternalHit S J K P n :=
    Nat.find_spec hExist
  have hNotZero : ¬ OriginalJMenuKExternalHit S J K P 0 := by
    rintro ⟨a,b,_,hNotJ,h⟩
    have hEq : Quotient.mk J.val a = Quotient.mk J.val b := h
    exact hNotJ (Quotient.exact hEq)
  have hNotOne : ¬ OriginalJMenuKExternalHit S J K P 1 := by
    rintro ⟨a,b,hKab,hNotJ,h⟩
    have hEdge : originalJMenuQuotientState S J P
        (Quotient.mk J.val a) (Quotient.mk J.val b) :=
      (relPow_one (originalJMenuQuotientState S J P)
        (Quotient.mk J.val a) (Quotient.mk J.val b)).mp h
    exact hNotJ
      (originalJMenuQuotientState_K_inside_diagonal
        S J K hJK.1.le P hAvoid a b hKab hEdge)
  have hNtwo : 2 ≤ n := by
    by_contra hBad
    have hCases : n = 0 ∨ n = 1 := by omega
    rcases hCases with hZero | hOne
    · exact hNotZero (by simpa only [hZero] using hHit)
    · exact hNotOne (by simpa only [hOne] using hHit)
  refine ⟨n,hNtwo,hHit,?_⟩
  intro m hm
  exact Nat.find_min hExist hm

end CCO.TransitionClosure
