import CCO.TransitionClosure.OriginalFirstHitMinimum
import CCO.TerminalLattice.OriginalQuotientPeirceCover

/-!
# B049 source07 C15-C16: genuine first-hit K/J intersections and Peirce rotation

All relations live on the ACTUAL quotient of one ORIGINAL old sort by J.
The Sbar relation is the real quotient saturation of the original menu P.
The external layer Ubar is K/J with its TRUE quotient diagonal deleted.

The least hit is obtained from the proven full original MI-cover lemma.
At the previous exponent the intersection with K/J is EXACTLY the true
diagonal, while (Sbar ; Ubar) inside K/J is EXACTLY Ubar. A witness to
the first hit rotates to a genuine intersection of those two profiles.

No quotient SAP/CCO, Set-Pasch theorem, hypothetical cover connectivity,
positive identity letter, NR2 or replacement for an actual original atom.
-/

universe u v w t

namespace CCO.TransitionClosure

variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)
variable {G : Type t} [Group G] [∀ s : ι, MulAction G (X s)]

open ParityHasse.Original
open CCO.TerminalLattice

/-- If P meets the ORIGINAL J-diversity palette, the literal
quotient-diagonal edges of Sbar give ALL true diagonal walks at
EVERY length, even length zero. -/
theorem originalJMenuQuotientState_power_diagonal
    (H : HomogeneousSource S G)
    {i : ι} (J : ColourEq S i) (P : S.Menu i i)
    (hMeet : (P ∩ originalEquivDiversityPalette S J).Nonempty)
    (n : Nat) (q : Quotient J.val) :
    relPow (originalJMenuQuotientState S J P) n q q := by
  induction n with
  | zero => rfl
  | succ n ih =>
      exact ⟨q, originalJMenuQuotientState_contains_diagonal
        S H J P hMeet q, ih⟩

/-- Source OWI-S strengthened to literal quotient points: a genuine
Sbar edge whose endpoints are K/J-related is necessarily a TRUE
J-quotient diagonal pair. The original palette avoidance hypothesis
is still explicit. -/
theorem originalJMenuQuotientState_K_implies_eq
    {i : ι} (J K : ColourEq S i) (hJK : J ≤ K)
    (P : S.Menu i i)
    (hAvoid : ∀ a : S.Atom i i,
      a ∈ P →
      a ∈ originalEquivDiversityPalette S K →
      a ∈ originalEquivDiversityPalette S J) :
    ∀ q r : Quotient J.val,
      originalUpperSetoid S J K hJK q r →
      originalJMenuQuotientState S J P q r →
      q = r := by
  intro q r hUpper hState
  induction q using Quotient.inductionOn with
  | _ x =>
      induction r using Quotient.inductionOn with
      | _ y =>
          have hKxy : K x y :=
            (originalUpperSetoid_mk S J K hJK x y).mp hUpper
          exact Quotient.sound
            (originalJMenuQuotientState_K_inside_diagonal
              S J K hJK P hAvoid x y hKxy hState)

/-- Source C15 OWI-S at the genuinely LEAST first K-external hit:
the previous quotient power restricted to K/J is exactly Delta_Q.
One inclusion is minimality; the reverse uses real quotient diagonal
edges supplied by a P atom in J-diversity, not a fictitious STRONG
identity factor. -/
theorem originalJMenuQuotientState_previous_power_K_diagonal
    (H : HomogeneousSource S G)
    {i : ι} (J K : ColourEq S i) (hJK : J ≤ K)
    (P : S.Menu i i)
    (hMeet : (P ∩ originalEquivDiversityPalette S J).Nonempty)
    (n : Nat) (hn : 2 ≤ n)
    (hLeast : ∀ m : Nat, m < n →
      ¬ OriginalJMenuKExternalHit S J K P m) :
    ∀ q r : Quotient J.val,
      originalUpperSetoid S J K hJK q r →
      (relPow (originalJMenuQuotientState S J P) (n-1) q r ↔ q = r) := by
  intro q r hUpper
  constructor
  · intro hPower
    by_contra hNE
    have hNoHit : ¬ OriginalJMenuKExternalHit S J K P (n-1) :=
      hLeast (n-1) (by omega)
    induction q using Quotient.inductionOn with
    | _ x =>
        induction r using Quotient.inductionOn with
        | _ y =>
            have hKxy : K x y :=
              (originalUpperSetoid_mk S J K hJK x y).mp hUpper
            have hNotJ : ¬ J x y := by
              intro hJ
              exact hNE (Quotient.sound hJ)
            exact hNoHit ⟨x,y,hKxy,hNotJ,hPower⟩
  · intro hEq
    subst r
    exact originalJMenuQuotientState_power_diagonal S H J P hMeet (n-1) q

/-- Source C15 OWI-ST: within K/J the literal quotient product
Sbar ; Ubar equals precisely Ubar. A middle point in Ubar stays
K-related to the right endpoint, so a K-related Sbar first edge
must be the TRUE quotient diagonal. Conversely Sbar contains
that diagonal by an actual J-diversity P atom. -/
theorem originalJMenuQuotientState_comp_external_K_iff
    (H : HomogeneousSource S G)
    {i : ι} (J K : ColourEq S i) (hJK : J ≤ K)
    (P : S.Menu i i)
    (hMeet : (P ∩ originalEquivDiversityPalette S J).Nonempty)
    (hAvoid : ∀ a : S.Atom i i,
      a ∈ P →
      a ∈ originalEquivDiversityPalette S K →
      a ∈ originalEquivDiversityPalette S J) :
    ∀ q r : Quotient J.val,
      originalUpperSetoid S J K hJK q r →
      (RawSymmetric.compose
          (originalJMenuQuotientState S J P)
          (originalQuotientExternalLayer S J K hJK) q r ↔
        originalQuotientExternalLayer S J K hJK q r) := by
  intro q r hUpper
  constructor
  · rintro ⟨z,hQZ,hZR⟩
    have hKQZ : originalUpperSetoid S J K hJK q z :=
      (originalUpperSetoid S J K hJK).trans hUpper
        ((originalUpperSetoid S J K hJK).symm hZR.1)
    have hEq : q = z :=
      originalJMenuQuotientState_K_implies_eq
        S J K hJK P hAvoid q z hKQZ hQZ
    simpa only [hEq] using hZR
  · intro hU
    exact ⟨q, originalJMenuQuotientState_contains_diagonal
      S H J P hMeet q, hU⟩

/-- Source C16 OWI-P: a REAL first-hit n-step quotient walk, with
K-related but J-distinct endpoints, yields an ACTUAL intersection
Abar ∩ (Sbar;Ubar), where Abar=Sbar^(n-1).
Rotate its first Sbar edge by true ORIGINAL same-sort symmetry;
the remaining n-1 edges are an unmodified genuine quotient walk. -/
theorem originalJMenuQuotientState_previous_meets_comp_external
    {i : ι} (J K : ColourEq S i) (hJK : J ≤ K)
    (P : S.Menu i i) (n : Nat) (hN : 0 < n)
    (hHit : OriginalJMenuKExternalHit S J K P n) :
    ∃ q r : Quotient J.val,
      relPow (originalJMenuQuotientState S J P) (n-1) q r ∧
      RawSymmetric.compose
        (originalJMenuQuotientState S J P)
        (originalQuotientExternalLayer S J K hJK) q r := by
  obtain ⟨x,y,hKxy,hNotJ,hPower⟩ := hHit
  have hU : originalQuotientExternalLayer S J K hJK
      (Quotient.mk J.val x) (Quotient.mk J.val y) :=
    ⟨(originalUpperSetoid_mk S J K hJK x y).mpr hKxy,
      fun hEq => hNotJ (Quotient.exact hEq)⟩
  have hnSucc : n = (n-1)+1 := by omega
  rw [hnSucc] at hPower
  obtain ⟨z,hFirst,hTail⟩ := hPower
  refine ⟨z,Quotient.mk J.val y,hTail,
    Quotient.mk J.val x,?_,hU⟩
  exact originalJMenuQuotientState_symmetric
    S J P (Quotient.mk J.val x) z hFirst

/-- Combined SOURCE07 C15-C16 first-hit quotient geometry.
All input obligations come from the ACTUAL original homogeneous
FULL MI-cover, genuine P exit/avoidance and old quotient diagonal.
This establishes the exact three quotient intersections needed
next for the positive OLD three-word Helly contradiction. -/
theorem originalJMenuQuotientState_first_hit_K_geometry
    (H : HomogeneousSource S G)
    {i : ι} (J K : ColourEq S i)
    (hMI : letI : Lattice (ColourEq S i) :=
      ColourEq.lattice S H (i := i); InfIrred J)
    (hJK : letI : Lattice (ColourEq S i) :=
      ColourEq.lattice S H (i := i); J ⋖ K)
    (P : S.Menu i i)
    (hMeet : (P ∩ originalEquivDiversityPalette S J).Nonempty)
    (hExit : ∃ a : S.Atom i i,
      a ∈ P ∧ a ∉ originalEquivDiversityPalette S J)
    (hAvoid : ∀ a : S.Atom i i,
      a ∈ P →
      a ∈ originalEquivDiversityPalette S K →
      a ∈ originalEquivDiversityPalette S J) :
    ∃ n : Nat, 2 ≤ n ∧
      (∀ q r : Quotient J.val,
        originalUpperSetoid S J K hJK.1.le q r →
        (relPow (originalJMenuQuotientState S J P) (n-1) q r ↔ q=r)) ∧
      (∀ q r : Quotient J.val,
        originalUpperSetoid S J K hJK.1.le q r →
        (RawSymmetric.compose
            (originalJMenuQuotientState S J P)
            (originalQuotientExternalLayer S J K hJK.1.le) q r ↔
          originalQuotientExternalLayer S J K hJK.1.le q r)) ∧
      (∃ q r : Quotient J.val,
        relPow (originalJMenuQuotientState S J P) (n-1) q r ∧
        RawSymmetric.compose
          (originalJMenuQuotientState S J P)
          (originalQuotientExternalLayer S J K hJK.1.le) q r) := by
  obtain ⟨n,hn,hHit,hLeast⟩ :=
    originalJMenuQuotientState_least_external_power
      S H J K hMI hJK P hExit hAvoid
  refine ⟨n,hn,?_,?_,?_⟩
  · exact originalJMenuQuotientState_previous_power_K_diagonal
      S H J K hJK.1.le P hMeet n hn hLeast
  · exact originalJMenuQuotientState_comp_external_K_iff
      S H J K hJK.1.le P hMeet hAvoid
  · exact originalJMenuQuotientState_previous_meets_comp_external
      S J K hJK.1.le P n (by omega) hHit

end CCO.TransitionClosure
