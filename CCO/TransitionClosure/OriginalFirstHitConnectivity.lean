import CCO.TransitionClosure.OriginalPositiveSaturationWord
import CCO.TerminalLattice.OriginalQuotientInvariantFinite
import CCO.TerminalLattice.FullCoverConnectivity

/-!
# B049 source07 C12-C14: ORIGINAL quotient state and connectivity

The first-hit quotient state Sbar is the ACTUAL old J-saturation
of an arbitrary original same-sort fine-atom menu P. The previously
proved full-preimage lemma retains all real distinct endpoint pairs,
including quotient-diagonal relations. This file shows that Sbar is
symmetric and invariant under precisely the ORIGINAL full homogeneous
source group, not an enlarged quotient automorphism group.

Its genuine undirected connectivity is a group-invariant Setoid
on the real J-quotient, and any OLD P atom outside J produces an
actual nontrivial connected pair. Under the later source hypothesis
that J is a FULL original meet-irreducible with unique cover K,
this is the input for K/J lying in Sbar-connectivity.

No CCO, SAP on quotient/hidden sorts, full cover, new axiom,
synthetic STRONG identity or assumed path saturation is used.
-/

universe u v w t

namespace CCO.TransitionClosure

variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)
variable {G : Type t} [Group G] [∀ s : ι, MulAction G (X s)]

open ParityHasse.Original
open CCO.TerminalLattice

/-- Every actual same-sort fine old atom is symmetric. Therefore
ANY old menu's quotient J-state, even if it is not a complete
quotient orbital, is a symmetric binary relation on OLD J-classes. -/
theorem originalJMenuQuotientState_symmetric
    {i : ι} (J : ColourEq S i) (P : S.Menu i i) :
    ∀ q r : Quotient J.val,
      originalJMenuQuotientState S J P q r →
      originalJMenuQuotientState S J P r q := by
  rintro q r ⟨u,v,hu,hv,a,ha,hcol⟩
  have hRev : S.colour v u = some a := by
    have h := (S.colour_swap u v a).mp hcol
    simpa only [S.symmetricLoop a] using h
  exact ⟨v,u,hv,hu,⟨a,ha,hRev⟩⟩

/-- The original actual full group G acts on the old J quotient,
and the source J-saturation relation is invariant under that
SAME ambient G. Membership is witnessed by actual OLD pairs
carrying exactly the prescribed original fine atom. -/
theorem originalJMenuQuotientState_groupInvariant
    (H : HomogeneousSource S G)
    {i : ι} (J : ColourEq S i) (P : S.Menu i i) :
    letI : MulAction G (Quotient J.val) :=
      originalQuotientAction S H J
    ∀ g : G, ∀ q r : Quotient J.val,
      originalJMenuQuotientState S J P q r →
      originalJMenuQuotientState S J P (g • q) (g • r) := by
  letI : MulAction G (Quotient J.val) :=
    originalQuotientAction S H J
  rintro g q r ⟨u,v,hu,hv,a,ha,hCol⟩
  refine ⟨g • u, g • v, ?_, ?_, ⟨a,ha,?_⟩⟩
  · have hMove := congrArg (fun z : Quotient J.val => g • z) hu
    simpa only [originalQuotient_mk_smul S H J] using hMove
  · have hMove := congrArg (fun z : Quotient J.val => g • z) hv
    simpa only [originalQuotient_mk_smul S H J] using hMove
  · exact (S.colourInvariant_of_homogeneous H g u v).trans hCol

/-- The actual Sbar belongs to the finite B050 type of ALL
ORIGINAL-G invariant quotient binary states. This is a derived
instance, not an unproven quotient action/source hypothesis. -/
def originalJMenuInvariantQuotientState
    (H : HomogeneousSource S G)
    {i : ι} (J : ColourEq S i) (P : S.Menu i i) :
    OriginalInvariantQuotientState S H J :=
  ⟨originalJMenuQuotientState S J P,
    originalJMenuQuotientState_groupInvariant S H J P⟩

/-- Genuine ORIGINAL undirected quotient graph connectivity
of Sbar. Every edge is a REAL old J-class edge witnessed by
some atom in P, and the setoid is reflexive, symmetric and
transitive via finite REAL quotient walks. -/
def originalJMenuQuotientConnected
    (H : HomogeneousSource S G)
    {i : ι} (J : ColourEq S i) (P : S.Menu i i) :
    Setoid (Quotient J.val) :=
  connectivitySetoid
    (originalJMenuQuotientState S J P)
    (originalJMenuQuotientState_symmetric S J P)

/-- The connectivity setoid is invariant under the SAME original
G-action; it is therefore a genuine FULL invariant equivalence
on the old quotient, not merely a graph-component partition. -/
theorem originalJMenuQuotientConnected_groupInvariant
    (H : HomogeneousSource S G)
    {i : ι} (J : ColourEq S i) (P : S.Menu i i) :
    letI : MulAction G (Quotient J.val) :=
      originalQuotientAction S H J
    ∀ g : G, ∀ q r : Quotient J.val,
      originalJMenuQuotientConnected S H J P q r →
      originalJMenuQuotientConnected S H J P (g • q) (g • r) := by
  letI : MulAction G (Quotient J.val) :=
    originalQuotientAction S H J
  rintro g q r ⟨n,hn⟩
  exact ⟨n,relPow_group_invariant
    (originalJMenuQuotientState S J P)
    (originalJMenuQuotientState_groupInvariant S H J P)
    n g q r hn⟩

/-- A menu P exiting J gives an ACTUAL off-diagonal old quotient
graph edge, hence a genuine nontrivial connected pair. This
is the source's strictly-above-J first-hit starting condition. -/
theorem originalJMenuQuotientConnected_nontrivial
    (H : HomogeneousSource S G)
    {i : ι} (J : ColourEq S i) (P : S.Menu i i)
    (hExit : ∃ a : S.Atom i i,
      a ∈ P ∧ a ∉ originalEquivDiversityPalette S J) :
    ∃ q r : Quotient J.val,
      q ≠ r ∧ originalJMenuQuotientConnected S H J P q r := by
  obtain ⟨q,r,hne,hState⟩ :=
    originalJMenuQuotientState_has_offdiagonal S J P hExit
  refine ⟨q,r,hne,⟨1,?_⟩⟩
  exact (relPow_one (originalJMenuQuotientState S J P) q r).mpr hState

end CCO.TransitionClosure
