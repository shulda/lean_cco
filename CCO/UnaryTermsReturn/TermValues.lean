import CCO.TransitionClosure.OriginalNamedRawUnaryLanguage

/-!
# B052 C08–C15 — finite values of actual named unary term functions

A real old point may be projected to an ACTUAL represented hidden
coordinate, and then subjected to an arbitrarily long named unary
word from B049. Each resulting value is a genuine old quotient point,
tagged with its true target FULL equivalence. There are finitely many
distinct such values for every pair of fixed original sort indices,
even if the original point/quotient carriers and the word syntax are
infinite. This is a consequence of FINITENESS OF THE FUNCTION IMAGE,
not of the syntactic expression type.

For a hidden input, the same conclusion follows by choosing an
actual old representative for that input quotient class. The result
does not assert bounded closures for arbitrary partial unary
structures, nor a uniform numeric bound before the finite
many-sorted aggregation is built.
-/

universe u v w t

namespace CCO.UnaryTermsReturn

variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)
variable {G : Type t} [Group G] [∀ i : ι, MulAction G (X i)]

open CCO.TransitionClosure
open CCO.ParityHasse.Original

/-- All real-source named unary expressions from real sort i
to some proper represented hidden coordinate on original sort j,
with the ACTUAL initial source quotient projection encoded by D. -/
abbrev OriginalRealToHiddenNamedTermDatum
    (H : HomogeneousSource S G) (sap : AgeSAP S)
    (nr2 : Selectors.OriginalNR2 S) (i j : ι) :=
  OriginalNamedRawUnaryTermDatum S H sap nr2 i j

/-- Interpret a real-source term at an actual original point:
project to D, apply its original named quotient unary term, and
tag the real FULL target kernel. The result is an interpreted
quotient value, not a term string or a chosen quotient section. -/
noncomputable def originalRealToHiddenNamedTermValue
    (H : HomogeneousSource S G) (sap : AgeSAP S)
    (nr2 : Selectors.OriginalNR2 S)
    {i j : ι} (x : X i)
    (d : OriginalRealToHiddenNamedTermDatum S H sap nr2 i j) :
    Σ F : ColourEq S j, Quotient F.val :=
  ⟨d.2.1.val,
    OriginalNamedRawUnaryTerm.eval S H sap nr2 d.2.2
      (Quotient.mk d.1.val.val x)⟩

/-- B052 C13 real-input FINITE functional image, per pair of
original sorts. Crucially the domain is the COMPLETE actual
named B049 grammar, including all finite alternating transitions,
inverses and upward quotient maps, not just primitive transitions.
All resulting target quotient labels are retained. -/
theorem original_real_to_hidden_named_values_finite
    (H : HomogeneousSource S G) (sap : AgeSAP S)
    (nr2 : Selectors.OriginalNR2 S)
    {i j : ι} (x : X i) :
    (Set.range (originalRealToHiddenNamedTermValue
      S H sap nr2 (j := j) x)).Finite := by
  let evaluate :
      OriginalCanonicalRawTransitionFunction S i j →
        (Σ F : ColourEq S j, Quotient F.val) :=
    fun f => ⟨f.2.1, f.2.2 (Quotient.mk f.1.val x)⟩
  have hFunctions :=
    original_named_raw_unary_term_functions_finite
      S H sap nr2 (i := i) (j := j)
  have hValues := hFunctions.image evaluate
  change (Set.range (fun d : OriginalNamedRawUnaryTermDatum
    S H sap nr2 i j =>
      evaluate (originalNamedRawUnaryTermDatum_function
        S H sap nr2 d))).Finite
  apply hValues.subset
  rintro z ⟨d, rfl⟩
  exact ⟨originalNamedRawUnaryTermDatum_function S H sap nr2 d,
    ⟨d, rfl⟩, rfl⟩

/-- A term starting at one LITERAL original hidden coordinate D.
The target is another represented original FULL quotient, with
both sorts and exact target quotient carried by dependent indices. -/
abbrev OriginalHiddenToHiddenNamedTermDatum
    (H : HomogeneousSource S G) (sap : AgeSAP S)
    (nr2 : Selectors.OriginalNR2 S)
    {i : ι} (D : OriginalNamedHiddenCoordinate S H i) (j : ι) :=
  Σ E : OriginalNamedHiddenCoordinate S H j,
    OriginalNamedRawUnaryTerm S H sap nr2 D E

/-- Actual value of a hidden-input word, with its target FULL
quotient tag, on one ORIGINAL represented quotient class. -/
noncomputable def originalHiddenToHiddenNamedTermValue
    (H : HomogeneousSource S G) (sap : AgeSAP S)
    (nr2 : Selectors.OriginalNR2 S)
    {i : ι} (D : OriginalNamedHiddenCoordinate S H i)
    {j : ι} (q : Quotient D.val.val)
    (d : OriginalHiddenToHiddenNamedTermDatum
      S H sap nr2 D j) :
    Σ F : ColourEq S j, Quotient F.val :=
  ⟨d.1.val, OriginalNamedRawUnaryTerm.eval S H sap nr2 d.2 q⟩

/-- B052 C13–C15: also an ORPHAN hidden quotient generator,
without a real generator inside its finite induced substructure,
has only finitely many actual unary term VALUES at each target
old sort. We use a real representative only in the ambient
quotient for the mathematical proof; it is not adjoined to the
hidden diagram or assumed to be in the orphan substructure. -/
theorem original_hidden_to_hidden_named_values_finite
    (H : HomogeneousSource S G) (sap : AgeSAP S)
    (nr2 : Selectors.OriginalNR2 S)
    {i j : ι} (D : OriginalNamedHiddenCoordinate S H i)
    (q : Quotient D.val.val) :
    (Set.range
      (originalHiddenToHiddenNamedTermValue
        S H sap nr2 D (j := j) q)).Finite := by
  induction q using Quotient.inductionOn with
  | _ x =>
      have hReal :=
        original_real_to_hidden_named_values_finite
          S H sap nr2 (i := i) (j := j) x
      apply hReal.subset
      rintro z ⟨d, rfl⟩
      exact ⟨⟨D, d.1, d.2⟩, rfl⟩

end CCO.UnaryTermsReturn
