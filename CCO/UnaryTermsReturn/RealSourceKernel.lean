import CCO.UnaryTermsReturn.NormalizedKernels

/-!
# B052 C22–C24: precise original real-source QT-NF kernel

A genuine term from one original REAL sort first projects to an
ACTUAL represented proper hidden coordinate D and then follows
an arbitrary named hidden unary word. B049's complete original
RAW normalisation and the new FULL named-middle theorem yield
a named proper MI K on the ORIGINAL real source sort.

The source-to-final function is a quotient bijection after the
literal K projection: use one actual RAW successor for EVERY real
x, B049's edge normalisation and injectivity of the B040 actual
quotient map. This proves the full two-sided equality kernel,
without assuming it or choosing a section.

The REAL identity term is separately treated using true equality,
not by pretending Id is a proper hidden quotient coordinate.
The further claim that the quotient bijection is explicitly a
NAMED unary term (rather than a genuine B040 map) is separate.
-/

universe u v w t

namespace CCO.UnaryTermsReturn

variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)
variable {G : Type t} [Group G] [∀ i : ι, MulAction G (X i)]

open CCO.TransitionClosure
open CCO.ParityHasse.Original
open CCO.QuotientTransport

/-- Source10 QT-NF for EVERY literal real projection followed by
ANY finite named hidden unary word. K is a represented proper
FULL original meet-irreducible, and equality of final values is
equivalent to ORIGINAL membership in the actual K equivalence.

This states a real source instance, not an arbitrary unary partial
function, and keeps the exact final named coordinate F. -/
theorem original_real_named_term_exact_kernel
    (H : HomogeneousSource S G) (sap : AgeSAP S)
    (nr2 : Selectors.OriginalNR2 S)
    {i j : ι}
    (D : OriginalNamedHiddenCoordinate S H i)
    (F : OriginalNamedHiddenCoordinate S H j)
    (w : OriginalNamedRawUnaryTerm S H sap nr2 D F) :
    ∃ K : OriginalNamedHiddenCoordinate S H i,
      ∀ x x' : X i,
        (OriginalNamedRawUnaryTerm.eval S H sap nr2 w
          (Quotient.mk D.val.val x) =
         OriginalNamedRawUnaryTerm.eval S H sap nr2 w
          (Quotient.mk D.val.val x')) ↔ K.val x x' := by
  obtain ⟨N, hSource, hTarget, ⟨K,hKernel,hDK⟩, hEdge⟩ :=
    original_named_hidden_term_has_named_normal_middle
      S H sap nr2 D F w
  let J : ColourEq S i := N.val.2.val.1
  let T := originalCanonicalRawTransitionDatum_transport S H N.val.2
  have hAt : ∀ x : X i,
      OriginalNamedRawUnaryTerm.eval S H sap nr2 w
          (Quotient.mk D.val.val x) =
        T.quotientEquiv (Quotient.mk J.val x) := by
    intro x
    obtain ⟨y,hxy⟩ := T.serial x
    have hTerm := hEdge x y hxy
    have hMap :
        T.quotientEquiv (Quotient.mk J.val x) =
          (Quotient.mk
            (originalTransportTargetColourEq S H J T).val y) :=
      T.quotientEquiv_edge hxy
    rw [← hTarget] at hTerm
    exact hTerm.trans hMap.symm
  refine ⟨K, ?_⟩
  intro x x'
  constructor
  · intro heq
    have hMapEq :
        T.quotientEquiv (Quotient.mk J.val x) =
          T.quotientEquiv (Quotient.mk J.val x') := by
      calc
        T.quotientEquiv (Quotient.mk J.val x) =
            OriginalNamedRawUnaryTerm.eval S H sap nr2 w
              (Quotient.mk D.val.val x) := (hAt x).symm
        _ = OriginalNamedRawUnaryTerm.eval S H sap nr2 w
              (Quotient.mk D.val.val x') := heq
        _ = T.quotientEquiv (Quotient.mk J.val x') := hAt x'
    have hJ : J x x' :=
      Quotient.exact (T.quotientEquiv.injective hMapEq)
    simpa only [hKernel] using hJ
  · intro hK
    have hJ : J x x' := by simpa only [hKernel] using hK
    have hQuot :
        (Quotient.mk J.val x) = Quotient.mk J.val x' :=
      Quotient.sound hJ
    calc
      OriginalNamedRawUnaryTerm.eval S H sap nr2 w
          (Quotient.mk D.val.val x) =
          T.quotientEquiv (Quotient.mk J.val x) := hAt x
      _ = T.quotientEquiv (Quotient.mk J.val x') :=
        congrArg T.quotientEquiv hQuot
      _ = OriginalNamedRawUnaryTerm.eval S H sap nr2 w
          (Quotient.mk D.val.val x') := (hAt x').symm

/-- The ONLY real-valued real-source term in this language is
the actual real identity. Its kernel is literally equality,
represented by the original FULL bottom equivalence, not an
extra or synthetic hidden coordinate. -/
theorem original_real_identity_exact_kernel {i : ι} :
    ∀ x y : X i, (x = y ↔ (⊥ : ColourEq S i) x y) := by
  intro x y
  exact Iff.rfl

end CCO.UnaryTermsReturn
