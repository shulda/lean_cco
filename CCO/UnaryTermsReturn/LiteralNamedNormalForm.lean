import CCO.UnaryTermsReturn.NamedNormalMap
import CCO.UnaryTermsReturn.TermComposition

/-!
# B052 C11/C24: literal named hidden unary normal form

The B049 all-FULL RAW normalisation is not on its own a
source10 named-term normal form. We first show, via the actual
B040 upper-interval full lattice and terminal original NR2,
that the intermediate source K of EVERY genuine named word
is an existing represented proper original meet-irreducible.

The WHOLE actual nonempty RAW relation in that B049 normal
datum is then reinterpreted by a genuine B049 named primitive
symbol, or by the existing identity when the old logical
diagonal is included. The result is an ACTUAL well-typed
named syntax word θ with literal pointwise equality
w = θ∘u_(D,K) on every original representative.

No new arbitrary transition symbol, fake STRONG identity
letter, hidden-age SAP, quotient group chart, or empty factor.
-/

universe u v w t
namespace CCO.UnaryTermsReturn

variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)
variable {G : Type t} [Group G] [∀ i : ι, MulAction G (X i)]

open CCO.TransitionClosure
open CCO.QuotientTransport
open CCO.ParityHasse.Original

/-- Every finite genuine named hidden term of UNBOUNDED length
from D to F has a literal actual named normal form:

    D --up--> K --theta--> F,

with source original FULL D<=K and theta either one
original RAW named transition or the already named identity.
The proof constructs theta, not only its invariant graph.
No arbitrary hidden homogeneity/SAP or new terminal premise. -/
theorem original_named_hidden_term_literal_normal_form
    (H : HomogeneousSource S G) (sap : AgeSAP S)
    (nr2 : Selectors.OriginalNR2 S)
    {i j : ι}
    (D : OriginalNamedHiddenCoordinate S H i)
    (F : OriginalNamedHiddenCoordinate S H j)
    (w : OriginalNamedRawUnaryTerm S H sap nr2 D F) :
    ∃ K : OriginalNamedHiddenCoordinate S H i,
      D.val ≤ K.val ∧
      ∃ theta : OriginalNamedRawUnaryTerm S H sap nr2 K F,
        ∀ x : X i,
          OriginalNamedRawUnaryTerm.eval S H sap nr2 w
            (Quotient.mk D.val.val x) =
          OriginalNamedRawUnaryTerm.eval S H sap nr2 theta
            (Quotient.mk K.val.val x) := by
  obtain ⟨N,hSource,hF,⟨K,hK,hDK⟩,hEdge⟩ :=
    original_named_hidden_term_has_named_normal_middle
      S H sap nr2 D F w
  let R : OriginalNonemptyInvariantTypedRel (X := X) (G := G) i j :=
    N.val.2.val.2
  let T0 := originalCanonicalRawTransitionDatum_transport S H N.val.2
  have T : Transport (originalColourEqAsInvEq S H K.val) R.val.val := by
    rw [hK]
    exact T0
  have hTTarget :
      originalTransportTargetColourEq S H K.val T = F.val := by
    rw [hK]
    exact hF
  obtain ⟨theta,hTheta⟩ :=
    original_named_raw_transport_has_named_expression
      S H sap nr2 K F R T hTTarget
  refine ⟨K,hDK,theta,?_⟩
  intro x
  obtain ⟨y,hxy⟩ := T.serial x
  have hW :
      OriginalNamedRawUnaryTerm.eval S H sap nr2 w
          (Quotient.mk D.val.val x) =
        Quotient.mk F.val.val y :=
    hEdge x y hxy
  have hTh :
      OriginalNamedRawUnaryTerm.eval S H sap nr2 theta
          (Quotient.mk K.val.val x) =
        Quotient.mk F.val.val y :=
    hTheta x y hxy
  exact hW.trans hTh.symm

end CCO.UnaryTermsReturn
