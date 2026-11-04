import CCO.UnaryTermsReturn.LiteralNamedNormalForm
import CCO.UnaryTermsReturn.RealSourceKernel
import CCO.UnaryTermsReturn.TermComposition

/-!
# B052 source10 QT-NF and literal forced source factorisation

The full B049 original RAW normal form, B040 FULL interval
transport and B011 terminal FULL NR2 identify the real-source
kernel of EVERY actual non-identity named unary term with one
genuinely represented proper original FULL MI K.

We now retain a genuinely NAMED quotient term theta:K→F,
not just an arbitrary equivariant quotient bijection. Its
actual semantics is injective, and for all real x the given
source term equals theta applied to the K-class of x.
Consequently its exact original kernel is literally K (QT-NF).

For EVERY represented proper J <= that SAME K, construct the
actual name sigma:J→F as the named upward map J→K followed
by theta; verify the original source equality at ALL real
points. No arbitrary quotient sections, extra symbols,
pseudo-STRONG identity or hidden SAP/CCO.
-/

universe u v w t
namespace CCO.UnaryTermsReturn

variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)
variable {G : Type t} [Group G] [∀ i : ι, MulAction G (X i)]

open CCO.TransitionClosure
open CCO.ParityHasse.Original

/-- The source10 QT-NF with ONE and the SAME actual NAMED
proper source kernel K, literal named theta syntax,
pointwise source-value equality and the biconditional
real kernel. A real identity term remains separately
handled by real equality, not by a proper hidden symbol. -/
theorem original_real_named_term_literal_QTNF
    (H : HomogeneousSource S G) (sap : AgeSAP S)
    (nr2 : Selectors.OriginalNR2 S)
    {i j : ι}
    (D : OriginalNamedHiddenCoordinate S H i)
    (F : OriginalNamedHiddenCoordinate S H j)
    (w : OriginalNamedRawUnaryTerm S H sap nr2 D F) :
    ∃ K : OriginalNamedHiddenCoordinate S H i,
      D.val ≤ K.val ∧
      ∃ theta : OriginalNamedRawUnaryTerm S H sap nr2 K F,
        Function.Injective (OriginalNamedRawUnaryTerm.eval S H sap nr2 theta) ∧
        (∀ x : X i,
          OriginalNamedRawUnaryTerm.eval S H sap nr2 w
            (Quotient.mk D.val.val x) =
          OriginalNamedRawUnaryTerm.eval S H sap nr2 theta
            (Quotient.mk K.val.val x)) ∧
        (∀ x y : X i,
          (OriginalNamedRawUnaryTerm.eval S H sap nr2 w
              (Quotient.mk D.val.val x) =
            OriginalNamedRawUnaryTerm.eval S H sap nr2 w
              (Quotient.mk D.val.val y)) ↔ K.val x y) := by
  obtain ⟨K,hDK,theta,hPoint,hInj⟩ :=
    original_named_hidden_term_literal_normal_form
      S H sap nr2 D F w
  refine ⟨K,hDK,theta,hInj,hPoint,?_⟩
  intro x y
  rw [hPoint x,hPoint y]
  constructor
  · intro h
    exact Quotient.exact (hInj h)
  · intro h
    exact congrArg
      (OriginalNamedRawUnaryTerm.eval S H sap nr2 theta)
      (Quotient.sound h)

/-- Source10 C26–C27 literal forced factorisation. One
K is produced from the ORIGINAL term and is valid
simultaneously for EVERY actual represented J<=K.
The factor sigma is real named syntax in the finite
terminal language, not an abstract quotient map. -/
theorem original_real_named_term_forced_factorisation
    (H : HomogeneousSource S G) (sap : AgeSAP S)
    (nr2 : Selectors.OriginalNR2 S)
    {i j : ι}
    (D : OriginalNamedHiddenCoordinate S H i)
    (F : OriginalNamedHiddenCoordinate S H j)
    (w : OriginalNamedRawUnaryTerm S H sap nr2 D F) :
    ∃ K : OriginalNamedHiddenCoordinate S H i,
      D.val ≤ K.val ∧
      ∀ J : OriginalNamedHiddenCoordinate S H i,
        J.val ≤ K.val →
        ∃ sigma : OriginalNamedRawUnaryTerm S H sap nr2 J F,
          ∀ x : X i,
            OriginalNamedRawUnaryTerm.eval S H sap nr2 w
              (Quotient.mk D.val.val x) =
            OriginalNamedRawUnaryTerm.eval S H sap nr2 sigma
              (Quotient.mk J.val.val x) := by
  obtain ⟨K,hDK,theta,hPoint,hInj⟩ :=
    original_named_hidden_term_literal_normal_form
      S H sap nr2 D F w
  refine ⟨K,hDK,?_⟩
  intro J hJK
  let sigma :=
    originalNamedForcedFactor S H sap nr2 J K F hJK theta
  refine ⟨sigma,?_⟩
  intro x
  calc
    OriginalNamedRawUnaryTerm.eval S H sap nr2 w
        (Quotient.mk D.val.val x) =
      OriginalNamedRawUnaryTerm.eval S H sap nr2 theta
        (Quotient.mk K.val.val x) := hPoint x
    _ = OriginalNamedRawUnaryTerm.eval S H sap nr2 sigma
        (Quotient.mk J.val.val x) :=
      originalNamedForcedFactor_real_point
        S H sap nr2 J K F hJK theta x

end CCO.UnaryTermsReturn
