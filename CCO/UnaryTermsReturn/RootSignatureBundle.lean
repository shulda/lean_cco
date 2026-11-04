import CCO.UnaryTermsReturn.RootSignature

/-!
# B052 D06/C04–C05: full actual transition-closed root equation package

A single original old pair of roots x,y may carry a guarded
theta-intersection constraint together with EVERY branch profile
that contains their actual fine orbital. Each branch is a
genuine original-G RAW quotient-functional relation over an
ACTUAL named proper full source coordinate.

Rather than collapsing equations for different J kernels to
untyped data, a datum retains its exact J, R, canonical B040
transport T, and the real source edge x R y. No root-signature
equations are postulated: the resulting quotient identity is
proved from that edge by the genuine B040 quotient action.

An arbitrary set of these concrete branches is simultaneously
satisfied at the same actual pair, along with the full unary
term closure of EVERY root equation. Shared-atom consistency
at common J is the compiled source10 C04 result in
SharedAtomTransitions; different J retain their literal types.
No hidden hereditary SAP or partial-source completion is
inferred from this ACTUAL-root statement.
-/

universe u v w t

namespace CCO.UnaryTermsReturn

variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)
variable {G : Type t} [Group G] [∀ i : ι, MulAction G (X i)]

open CCO.TransitionClosure
open CCO.QuotientTransport
open CCO.ParityHasse.Original

/-- One actual direct/branch-forced guarded root equation.
The relation is nonempty because its ACTUAL edge is present;
the named target is derived, not caller supplied. -/
structure OriginalActualRootEquationDatum
    (H : HomogeneousSource S G)
    {i j : ι} (x : X i) (y : X j) where
  J : OriginalNamedHiddenCoordinate S H i
  R : QuotientTransport.Rel (X i) (X j)
  T : Transport (originalColourEqAsInvEq S H J.val) R
  edge : R x y

/-- Literal source10 D06 direct quotient equation at a
named, actual original fine root pair. -/
def OriginalActualRootEquation
    (H : HomogeneousSource S G)
    (sap : AgeSAP S) (nr2 : Selectors.OriginalNR2 S)
    {i j : ι} {x : X i} {y : X j}
    (d : OriginalActualRootEquationDatum S H x y) : Prop :=
  d.T.quotientEquiv (Quotient.mk d.J.val.val x) =
    Quotient.mk (originalRootNamedTarget S H sap nr2 d.J d.T).val.val y

/-- EVERY direct or theta-branch equation from a REAL
root pair is satisfied simultaneously. This quantifies
over the ENTIRE caller-specified set of genuine relations;
it does not select a single convenient branch. -/
theorem original_actual_root_bundle_consistent
    (H : HomogeneousSource S G)
    (sap : AgeSAP S) (nr2 : Selectors.OriginalNR2 S)
    {i j : ι} (x : X i) (y : X j)
    (branches : Set (OriginalActualRootEquationDatum S H x y)) :
    ∀ d ∈ branches, OriginalActualRootEquation S H sap nr2 d := by
  intro d hd
  exact original_root_direct_named_transition
    S H sap nr2 d.J d.T x y d.edge

/-- Full functional closure: for EVERY root equation
and EVERY genuine named B049 unary continuation from its
actual target, the induced equality remains true. This
retains the exact transported target coordinate separately
for each original J, including branch profiles with
different kernels, and arbitrary finite term syntax. -/
theorem original_actual_root_bundle_all_named_continuations
    (H : HomogeneousSource S G)
    (sap : AgeSAP S) (nr2 : Selectors.OriginalNR2 S)
    {i j : ι} (x : X i) (y : X j)
    (branches : Set (OriginalActualRootEquationDatum S H x y)) :
    ∀ d ∈ branches, ∀ {k : ι}
      (F : OriginalNamedHiddenCoordinate S H k)
      (word : OriginalNamedRawUnaryTerm S H sap nr2
        (originalRootNamedTarget S H sap nr2 d.J d.T) F),
      OriginalNamedRawUnaryTerm.eval S H sap nr2 word
        (d.T.quotientEquiv (Quotient.mk d.J.val.val x)) =
      OriginalNamedRawUnaryTerm.eval S H sap nr2 word
        (Quotient.mk
          (originalRootNamedTarget S H sap nr2 d.J d.T).val.val y) := by
  intro d hd k F word
  exact original_root_named_transition_closed_under_terms
    S H sap nr2 d.J d.T F word x y d.edge

end CCO.UnaryTermsReturn
