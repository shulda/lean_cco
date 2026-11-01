import CCO.TerminalLattice.OriginalQuotientNoReturn
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Pi

/-!
# B050 source09 OWL: FINITELY MANY original-G-invariant quotient states

Although an original J-class quotient may be infinite, the number of
binary relations invariant under the ORIGINAL ambient automorphism group
is finite. Every such relation is determined by its truth table on the
finite set of actual old same-sort OPTIONAL fine pair colours.

For a given old pair colour c, the table records whether there is a
REAL old pair of colour c whose J-classes lie in the relation. Old
complete-pair homogeneity transports that membership to every other
old pair of the same colour under the SAME group G. This includes the
old diagonal optional colour and quotient-diagonal states, and does
not posit a new quotient automorphism action or quotient homogeneity.

We also prove that invariant states are closed under real quotient
composition and that every nonempty invariant state is serial by
original sort transitivity. These are needed for the literal finite
escape/recurrence argument of source09.
-/

universe u v w t

namespace CCO.TerminalLattice

variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)
variable {G : Type t} [Group G] [∀ j : ι, MulAction G (X j)]

open ParityHasse.Original

/-- A binary relation on the J quotient invariant under the precise
OLD ambient G-action, not an enlarged quotient-reduct automorphism
group. The possible J-QUOTIENT diagonal is retained. -/
def OriginalInvariantQuotientState
    (H : HomogeneousSource S G) {i : ι} (J : ColourEq S i) :=
  {R : Quotient J.val → Quotient J.val → Prop //
    letI : MulAction G (Quotient J.val) :=
      originalQuotientAction S H J
    ∀ g : G, ∀ q r : Quotient J.val,
      R q r → R (g • q) (g • r)}

/-- The finite truth table of an invariant quotient state indexed by
actual OLD optional same-sort fine pair colours, including real
old diagonal. No quotient homogeneity or abstract orbital finite
type is assumed. -/
def originalInvariantQuotientColourCode
    (H : HomogeneousSource S G) {i : ι}
    (J : ColourEq S i)
    (R : OriginalInvariantQuotientState S H J) :
    Option (S.Atom i i) → Prop :=
  fun c => ∃ x y : X i,
    S.colour x y = c ∧
    R.val (Quotient.mk J.val x) (Quotient.mk J.val y)

/-- Different original invariant quotient states have DIFFERENT
finite old pair-colour truth tables. This is a genuinely injective
encoding, obtained by original homogeneous pair extension and the
actual ORIGINAL induced action on J-classes. -/
theorem originalInvariantQuotientColourCode_injective
    (H : HomogeneousSource S G) {i : ι}
    (J : ColourEq S i) :
    Function.Injective (originalInvariantQuotientColourCode S H J) := by
  intro R T hCode
  apply Subtype.ext
  funext q r
  apply propext
  induction q using Quotient.inductionOn with
  | _ a =>
    induction r using Quotient.inductionOn with
    | _ b =>
      letI : MulAction G (Quotient J.val) :=
        originalQuotientAction S H J
      have hAt :=
        congrFun hCode (S.colour a b)
      constructor
      · intro hR
        have hOldCode :
            originalInvariantQuotientColourCode S H J R (S.colour a b) :=
          ⟨a,b,rfl,hR⟩
        obtain ⟨x,y,hColXY,hTXY⟩ := Eq.mp hAt hOldCode
        obtain ⟨g,hgx,hgy⟩ :=
          S.pair_homogeneous_of_homogeneous H x a y b hColXY
        have hMove := T.property g
          (Quotient.mk J.val x) (Quotient.mk J.val y) hTXY
        simpa only [originalQuotient_mk_smul S H J,hgx,hgy] using hMove
      · intro hT
        have hOldCode :
            originalInvariantQuotientColourCode S H J T (S.colour a b) :=
          ⟨a,b,rfl,hT⟩
        obtain ⟨x,y,hColXY,hRXY⟩ := Eq.mp hAt.symm hOldCode
        obtain ⟨g,hgx,hgy⟩ :=
          S.pair_homogeneous_of_homogeneous H x a y b hColXY
        have hMove := R.property g
          (Quotient.mk J.val x) (Quotient.mk J.val y) hRXY
        simpa only [originalQuotient_mk_smul S H J,hgx,hgy] using hMove

/-- SOURCE09 finite-state input: there are only FINITELY many
ORIGINAL-G invariant quotient binary relations. This holds without
a finite quotient carrier and without source SAP/CCO: we have an
actual injection into the finite Boolean table of original optional
same-sort atom colours, which are finite by the ORIGINAL atomic
source contract. -/
theorem originalInvariantQuotientState_finite
    (H : HomogeneousSource S G) {i : ι}
    (J : ColourEq S i) :
    Finite (OriginalInvariantQuotientState S H J) := by
  classical
  letI : Fintype (S.Atom i i) := S.finiteAtom i i
  exact Finite.of_injective
    (originalInvariantQuotientColourCode S H J)
    (originalInvariantQuotientColourCode_injective S H J)

/-- The composition of TWO arbitrary original invariant quotient
states is an ORIGINAL invariant quotient state under the same
induced OLD G-action. No completeness, exclusion of quotient
diagonal, or separate quotient-group assumption. -/
def originalInvariantQuotientState_comp
    (H : HomogeneousSource S G) {i : ι} (J : ColourEq S i)
    (R T : OriginalInvariantQuotientState S H J) :
    OriginalInvariantQuotientState S H J := by
  letI : MulAction G (Quotient J.val) :=
    originalQuotientAction S H J
  refine ⟨RawSymmetric.compose R.val T.val, ?_⟩
  intro g q r h
  obtain ⟨mid,hR,hT⟩ := h
  exact ⟨g • mid,R.property g q mid hR,
    T.property g mid r hT⟩

/-- Every NONEMPTY invariant quotient state is serial, because the
actual original ambient group acts transitively on its fixed real
sort and hence on the J-classes. This is true even when the state
includes its quotient diagonal; nonemptiness is an actual quotient
pair, not an artificial old diversity atom. -/
theorem originalInvariantQuotientState_serial
    (H : HomogeneousSource S G) {i : ι}
    (J : ColourEq S i)
    (R : OriginalInvariantQuotientState S H J)
    (hNonempty : ∃ q r : Quotient J.val, R.val q r) :
    ∀ q : Quotient J.val, ∃ r, R.val q r := by
  obtain ⟨q0,r0,hR0⟩ := hNonempty
  induction q0 using Quotient.inductionOn with
  | _ a =>
    induction r0 using Quotient.inductionOn with
    | _ b =>
      intro q
      induction q using Quotient.inductionOn with
      | _ x =>
        letI : MulAction G (Quotient J.val) :=
          originalQuotientAction S H J
        obtain ⟨g,hga⟩ :=
          S.original_sort_transitive_of_homogeneous H i a x
        have hMoved := R.property g
          (Quotient.mk J.val a) (Quotient.mk J.val b) hR0
        refine ⟨Quotient.mk J.val (g • b), ?_⟩
        simpa only [originalQuotient_mk_smul S H J,hga] using hMoved

end CCO.TerminalLattice
