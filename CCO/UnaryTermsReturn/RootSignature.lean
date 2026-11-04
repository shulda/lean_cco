import CCO.UnaryTermsReturn.SharedAtomTransitions
import CCO.TransitionClosure.OriginalNamedRawUnaryLanguage

/-!
# B052 D06/C04–C05: actual transition-closed root signatures

The source10 root signature retains every direct quotient-transition
equation at each *actual* represented proper FULL original kernel, and
every equation forced by a branch of a theta intersection. The model
in this module is an ACTUAL original root pair; it is not an
arbitrarily assigned partial hidden diagram.

Every nonempty original-G invariant typed RAW relation R through
the pair, satisfying the true quotient kernel condition, induces
its canonical B040 quotient bijection with a genuinely named
target under old SAP and terminal FULL NR2. This equality is
preserved by every further genuine named hidden unary word.
Thus taking the full functional closure of the root equations
does not introduce an inconsistency.

The shared-old-atom equality of two different branch functions
and their actual target kernels is the separately proved source10
C04 theorem in SharedAtomTransitions. We do not identify distinct
RAW relations, add an identity-labelled STRONG atom, or assume
homogeneity/SAP of arbitrary hidden partial substructures.
-/

universe u v w t

namespace CCO.UnaryTermsReturn

variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)
variable {G : Type t} [Group G] [∀ i : ι, MulAction G (X i)]

open CCO.TransitionClosure
open CCO.QuotientTransport
open CCO.ParityHasse.Original

/-- The actual existing named coordinate at the target of
a genuine B040 old-G quotient transport out of a represented
proper FULL original MI source. Its existence consumes only
the original old SAP and the original FULL NR2 naming gate. -/
noncomputable def originalRootNamedTarget
    (H : HomogeneousSource S G)
    (sap : AgeSAP S) (nr2 : Selectors.OriginalNR2 S)
    {i j : ι}
    (J : OriginalNamedHiddenCoordinate S H i)
    {R : QuotientTransport.Rel (X i) (X j)}
    (T : Transport (originalColourEqAsInvEq S H J.val) R) :
    OriginalNamedHiddenCoordinate S H j :=
  original_named_hidden_transport_target S H sap nr2 J T

/-- One direct ACTUAL root constraint x R y is interpreted
exactly as the canonical hidden quotient transition equation.
Neither its output quotient nor its action is caller-supplied.
This includes mixed old sorts and true equality-inclusive RAW
relations. -/
theorem original_root_direct_named_transition
    (H : HomogeneousSource S G)
    (sap : AgeSAP S) (nr2 : Selectors.OriginalNR2 S)
    {i j : ι}
    (J : OriginalNamedHiddenCoordinate S H i)
    {R : QuotientTransport.Rel (X i) (X j)}
    (T : Transport (originalColourEqAsInvEq S H J.val) R)
    (x : X i) (y : X j) (hxy : R x y) :
    T.quotientEquiv (Quotient.mk J.val.val x) =
      Quotient.mk (originalRootNamedTarget S H sap nr2 J T).val.val y :=
  T.quotientEquiv_edge hxy

/-- ALL forced images of a genuine direct root equation under
ANY further named unary word agree. Full functional closure is
checked at the *same* literal target named coordinate; the
word's syntax may contain arbitrary upward maps, inverses and
composed RAW transitions of unbounded finite length. -/
theorem original_root_named_transition_closed_under_terms
    (H : HomogeneousSource S G)
    (sap : AgeSAP S) (nr2 : Selectors.OriginalNR2 S)
    {i j k : ι}
    (J : OriginalNamedHiddenCoordinate S H i)
    {R : QuotientTransport.Rel (X i) (X j)}
    (T : Transport (originalColourEqAsInvEq S H J.val) R)
    (F : OriginalNamedHiddenCoordinate S H k)
    (word : OriginalNamedRawUnaryTerm S H sap nr2
      (originalRootNamedTarget S H sap nr2 J T) F)
    (x : X i) (y : X j) (hxy : R x y) :
    OriginalNamedRawUnaryTerm.eval S H sap nr2 word
      (T.quotientEquiv (Quotient.mk J.val.val x)) =
    OriginalNamedRawUnaryTerm.eval S H sap nr2 word
      (Quotient.mk (originalRootNamedTarget S H sap nr2 J T).val.val y) :=
  congrArg (OriginalNamedRawUnaryTerm.eval S H sap nr2 word)
    (original_root_direct_named_transition S H sap nr2 J T x y hxy)

/-- A pair of distinct original-G RAW branches through one
actual fine atom has the SAME canonical transported full
kernel, so the two direct root equations are simultaneous.
This is a statement about actual quotient functions; it
does not claim the two input binary relations are equal. -/
theorem original_root_shared_atom_functional_closure_consistent
    (H : HomogeneousSource S G)
    {i j : ι} (J : ColourEq S i)
    (R Q : QuotientTransport.Rel (X i) (X j))
    (T : Transport (originalColourEqAsInvEq S H J) R)
    (U : Transport (originalColourEqAsInvEq S H J) Q)
    (a : S.Atom i j)
    (haR : a ∈ S.diversityGuard R)
    (haQ : a ∈ S.diversityGuard Q)
    {Z : Type*} (f : Quotient U.target.val → Z)
    (q : Quotient J.val) :
    ∃ hEq : T.target = U.target,
      f (InvEq.quotientCongr hEq (T.quotientEquiv q)) =
        f (U.quotientEquiv q) := by
  obtain ⟨hEq,hMaps⟩ :=
    original_shared_atom_raw_transports_agree S H J R Q T U a haR haQ
  exact ⟨hEq, congrArg f (hMaps q)⟩

end CCO.UnaryTermsReturn
