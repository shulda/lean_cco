import CCO.TransitionClosure.OriginalFirstHitConnectivity
import Mathlib.Order.Irreducible

/-!
# B049 source07 C13-C14: FULL original MI cover lies in Sbar connectivity

The pinned original first-hit lemma assumes that J is an actual
FULL original meet-irreducible equivalence with its FULL unique cover K.
The source's first-hit Sbar is the *genuine* quotient relation induced
by one positive old fine menu P, with true quotient-diagonal states.
Its finite-walk connectedness lifts back to an actual invariant full
equivalence E on the ORIGINAL named sort and the ORIGINAL ambient group.

If P exits J then J < E. In any lattice, meet irreducibility of J
plus J ⋖ K forces K ≤ E. This proves the exact source C13-C14
connectivity containment, without assuming a quotient SAP/CCO,
quotient reduct homogeneity, K-internal graph edges, or a stronger
"every above-J equivalence contains K" hypothesis.
-/

universe u v w t

namespace CCO.TransitionClosure

variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)
variable {G : Type t} [Group G] [∀ s : ι, MulAction G (X s)]

open ParityHasse.Original
open CCO.TerminalLattice

/-- Pure finite-interval-free lattice fact: if J is genuinely
MEET-IRREDUCIBLE and K covers J, any element above J already
contains K. This does NOT silently replace meet-irreducibility by
the stronger property; the implication is proved. -/
theorem original_meet_irred_full_cover_le
    {L : Type*} [Lattice L] {J K E : L}
    (hMI : InfIrred J) (hJK : J ⋖ K) (hJE : J < E) :
    K ≤ E := by
  have hInf : J ≤ K ⊓ E := le_inf hJK.1.le hJE.le
  by_cases hEq : K ⊓ E = J
  · rcases hMI.2 hEq with hK | hE
    · exact False.elim ((ne_of_gt hJK.1) hK)
    · exact False.elim ((ne_of_gt hJE) hE)
  · have hJInf : J < K ⊓ E :=
      lt_of_le_of_ne hInf (Ne.symm hEq)
    rcases eq_or_lt_of_le (inf_le_left : K ⊓ E ≤ K) with hK | hK
    · calc
        K = K ⊓ E := hK.symm
        _ ≤ E := inf_le_right
    · exact False.elim ((hJK.2 hJInf) hK)

/-- The OLD quotient graph connectedness is pulled back to a
genuine FULL invariant equivalence of the ACTUAL original sort.
Original pair homogeneity, rather than arbitrary quotient
homogeneity, certifies its original named-pair colour invariance. -/
def originalJMenuConnectedFullColourEq
    (H : HomogeneousSource S G)
    {i : ι} (J : ColourEq S i) (P : S.Menu i i) :
    ColourEq S i := by
  let C := originalJMenuQuotientConnected S H J P
  let R : Setoid (X i) :=
    Setoid.comap (fun x : X i => Quotient.mk J.val x) C
  refine ⟨R, ?_⟩
  apply groupInvariant_colourInvariant S H
  intro g x y hxy
  letI : MulAction G (Quotient J.val) :=
    originalQuotientAction S H J
  have hC :=
    originalJMenuQuotientConnected_groupInvariant
      S H J P g
        (Quotient.mk J.val x) (Quotient.mk J.val y) hxy
  simpa [R, C, Setoid.comap, originalQuotient_mk_smul S H J] using hC

/-- J is actually contained in the lifted old connectedness:
pairs of J-equivalent real points have EQUAL quotient images.
The quotient diagonal is real equality on J-classes, not a
synthetic old diversity identity atom. -/
theorem originalJMenuConnectedFullColourEq_above_J
    (H : HomogeneousSource S G)
    {i : ι} (J : ColourEq S i) (P : S.Menu i i) :
    J ≤ originalJMenuConnectedFullColourEq S H J P := by
  intro x y hJxy
  have hQ : originalJMenuQuotientConnected S H J P
      (Quotient.mk J.val x) (Quotient.mk J.val y) := by
    rw [Quotient.sound hJxy]
    exact (originalJMenuQuotientConnected S H J P).refl _
  simpa [originalJMenuConnectedFullColourEq, Setoid.comap] using hQ

/-- The original P atom outside J gives a literal real pair in
the lifted connectivity equivalence but outside J. Hence J<E
in the FULL invariant-equivalence lattice, not an exact sublattice.
No assumption that Sbar is contained in K/J is made. -/
theorem originalJMenuConnectedFullColourEq_strict
    (H : HomogeneousSource S G)
    {i : ι} (J : ColourEq S i) (P : S.Menu i i)
    (hExit : ∃ a : S.Atom i i,
      a ∈ P ∧ a ∉ originalEquivDiversityPalette S J) :
    J < originalJMenuConnectedFullColourEq S H J P := by
  let E := originalJMenuConnectedFullColourEq S H J P
  have hJE : J ≤ E :=
    originalJMenuConnectedFullColourEq_above_J S H J P
  apply lt_of_le_of_ne hJE
  obtain ⟨a,ha,hNotJ⟩ := hExit
  obtain ⟨x,y,hcol⟩ := S.realized a
  have hJxy : ¬ J x y := by
    intro h
    exact hNotJ ⟨x,y,h,hcol⟩
  have hS : originalJMenuQuotientState S J P
        (Quotient.mk J.val x) (Quotient.mk J.val y) :=
    ⟨x,y,rfl,rfl,⟨a,ha,hcol⟩⟩
  have hE : E x y := by
    change originalJMenuQuotientConnected S H J P
      (Quotient.mk J.val x) (Quotient.mk J.val y)
    exact ⟨1,(relPow_one
      (originalJMenuQuotientState S J P)
      (Quotient.mk J.val x) (Quotient.mk J.val y)).mpr hS⟩
  intro hEq
  have hJvia : J x y := by
    rw [hEq]
    exact hE
  exact hJxy hJvia

/-- Source07 C13-C14: for a FULL original meet-irreducible
J with its genuine FULL cover K, ANY original menu P exiting J
has J-quotient connectedness containing the entire K/J relation.
The proof uses only the real original ambient G and full-invariant
lattice; no SAP, CCO or K-contained-edge assumption is imported. -/
theorem originalJMenuQuotientConnected_contains_full_MI_cover
    (H : HomogeneousSource S G)
    {i : ι} (J K : ColourEq S i)
    (hMI : letI : Lattice (ColourEq S i) :=
      ColourEq.lattice S H (i := i); InfIrred J)
    (hJK : letI : Lattice (ColourEq S i) :=
      ColourEq.lattice S H (i := i); J ⋖ K)
    (P : S.Menu i i)
    (hExit : ∃ a : S.Atom i i,
      a ∈ P ∧ a ∉ originalEquivDiversityPalette S J) :
    ∀ q r : Quotient J.val,
      originalUpperSetoid S J K hJK.1.le q r →
        originalJMenuQuotientConnected S H J P q r := by
  letI : Lattice (ColourEq S i) := ColourEq.lattice S H (i := i)
  let E := originalJMenuConnectedFullColourEq S H J P
  have hJE : J < E :=
    originalJMenuConnectedFullColourEq_strict S H J P hExit
  have hKE : K ≤ E :=
    original_meet_irred_full_cover_le hMI hJK hJE
  intro q r hUpper
  induction q using Quotient.inductionOn with
  | _ x =>
    induction r using Quotient.inductionOn with
    | _ y =>
      have hKxy : K x y :=
        (originalUpperSetoid_mk S J K hJK.1.le x y).mp hUpper
      simpa [E, originalJMenuConnectedFullColourEq, Setoid.comap] using (hKE hKxy)

end CCO.TransitionClosure
