import CCO.TransitionClosure.OriginalWholeTransitionCylinder
import CCO.TransitionClosure.OriginalUnaryTermFiniteFunctions
import CCO.TransitionClosure.OriginalFullMITransport

/-!
# B049 source07 C36-C40/C51: true represented hidden quotient coordinates

This makes the named hidden object B_(i,J) an ACTUAL old sortwise
quotient by a nonidentity proper FULL meet-irreducible of the WHOLE
original homogeneous group-invariant equivalence lattice. It records
an ACTUAL equality-inclusive original RAW word for J rather than
silently assuming that generic transport preserves exactness.

B011 terminal FULL original NR2 constructs the representation.
B040 interval transport plus actual ORIGINAL SAP and the independent
terminal NR2 provider construct a genuinely named hidden target,
excluding equality and Top. The canonical unary map is the ACTUAL
B040 quotient bijection, not an abstract new function.

Original full mixed unary terms whose endpoints are restricted to
these named coordinates have finite SEMANTIC function image by the
already proved normal-form induction. This supplies a sound finite
upper bound on the genuine named hidden term functions, but DOES NOT
yet identify all intermediate named-language terms or construct the
full compatible hidden-cylinder partition. Those remain explicit
receiving obligations. Neither quotient SAP/CCO nor a synthetic
STRONG identity is introduced.
-/

universe u v w t

namespace CCO.TransitionClosure

variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)
variable {G : Type t} [Group G] [∀ s : ι, MulAction G (X s)]

open ParityHasse.Original
open CCO.QuotientTransport

/-- The ACTUAL represented proper meet-irreducible original
coordinate, excluding original equality and carrying a proof of
one genuine original RAW word. All lattice quantifiers range
over FULL original equivalences, not an exact sublattice. -/
abbrev OriginalNamedHiddenCoordinate
    (H : HomogeneousSource S G) (i : ι) :=
  {J : ColourEq S i //
    (⊥ : ColourEq S i) < J ∧
    ProperMeetIrreducible (originalColourEqAsInvEq S H J) ∧
    ∃ word : RawWord S i i,
      RawWord.relation S word = J.val.r}

/-- Only finitely many genuinely named proper hidden coordinates
exist on each original real sort. This is an actual consequence of
the finite original colour-orbital palette, not finite quotient
carrier cardinality or an assumption of finite term syntax. -/
theorem original_named_hidden_coordinates_finite
    (H : HomogeneousSource S G) {i : ι} :
    Finite (OriginalNamedHiddenCoordinate S H i) := by
  exact Finite.of_injective Subtype.val Subtype.val_injective

/-- B011 terminal FULL NR2 places EVERY genuine nonzero
proper FULL original meet-irreducible in the represented hidden
coordinate language. The raw word witness is PROVED, not
an additional property demanded of the source J. -/
noncomputable def original_full_MI_named_hidden_of_terminalNR2
    (H : HomogeneousSource S G)
    (nr2 : Selectors.OriginalNR2 S)
    {i : ι} (J : ColourEq S i)
    (hJbot : (⊥ : ColourEq S i) < J)
    (hJMI : ProperMeetIrreducible (originalColourEqAsInvEq S H J)) :
    OriginalNamedHiddenCoordinate S H i :=
  ⟨J,hJbot,hJMI,
    RealClosure.Bounds.terminal_raw_word_of_originalNR2 S H nr2 J⟩

/-- C37/C51: literal B040 transport of one actually named
hidden original coordinate produces another ACTUALLY named
proper hidden original coordinate, under exactly the original
visible SAP plus terminal FULL original NR2 gates.

The target is the real F=Rᵒᵖ;J;R original FULL equivalence,
not a chosen represented quotient chart or a quotient-age
SAP inference. -/
noncomputable def original_named_hidden_transport_target
    (H : HomogeneousSource S G) (sap : AgeSAP S)
    (nr2 : Selectors.OriginalNR2 S)
    {i j : ι} (D : OriginalNamedHiddenCoordinate S H i)
    {R : QuotientTransport.Rel (X i) (X j)}
    (T : Transport (originalColourEqAsInvEq S H D.val) R) :
    OriginalNamedHiddenCoordinate S H j := by
  obtain ⟨hMI,hBot,_hTop,hRaw⟩ :=
    originalTransportTargetColourEq_properMI_named_NR2
      S H sap nr2 D.val D.property.1 D.property.2.1 T
  exact ⟨originalTransportTargetColourEq S H D.val T,
    hBot,hMI,hRaw⟩

/-- The actual original quotient-transition unary FUNCTION
between the above named hidden carriers, using the literal
B040 quotient action and not postulating another quotient map. -/
noncomputable def original_named_hidden_transport_function
    (H : HomogeneousSource S G) (sap : AgeSAP S)
    (nr2 : Selectors.OriginalNR2 S)
    {i j : ι} (D : OriginalNamedHiddenCoordinate S H i)
    {R : QuotientTransport.Rel (X i) (X j)}
    (T : Transport (originalColourEqAsInvEq S H D.val) R) :
    Quotient D.val.val →
      Quotient (original_named_hidden_transport_target
        S H sap nr2 D T).val.val := by
  change Quotient (originalColourEqAsInvEq S H D.val).val →
    Quotient T.target.val
  exact T.quotientEquiv

/-- C37 genuine semantic interpretation of a named hidden
transition on an actual original RAW R-edge. -/
theorem original_named_hidden_transport_function_edge
    (H : HomogeneousSource S G) (sap : AgeSAP S)
    (nr2 : Selectors.OriginalNR2 S)
    {i j : ι} (D : OriginalNamedHiddenCoordinate S H i)
    {R : QuotientTransport.Rel (X i) (X j)}
    (T : Transport (originalColourEqAsInvEq S H D.val) R)
    (x : X i) (y : X j) (hxy : R x y) :
    original_named_hidden_transport_function S H sap nr2 D T
        (Quotient.mk D.val.val x) =
      Quotient.mk
        (original_named_hidden_transport_target S H sap nr2 D T).val.val y := by
  change T.quotientEquiv (Quotient.mk'' x) = Quotient.mk'' y
  exact T.quotientEquiv_edge hxy

/-- An actual OLD generated unary term whose source and target
are both named represented hidden coordinates. Its internal
quotient kernels may include further FULL old coordinates;
this is a conservative SUPERSET of the finally named
hidden-only grammar, not a false identification of two languages. -/
abbrev OriginalNamedHiddenOldTermDatum
    (H : HomogeneousSource S G) (i j : ι) :=
  {d : OriginalOldUnaryTermDatum S H i j //
    (∃ E : OriginalNamedHiddenCoordinate S H i,
      E.val = d.1) ∧
    (∃ F : OriginalNamedHiddenCoordinate S H j,
      F.val = d.2.1)}

/-- C39/C40 honest named-endpoint semantic finiteness:
ALL old mixed terms between these actual represented hidden
endpoints, including unbounded lengths and unrestricted FULL
intermediate kernels, have a finite image of ACTUAL functions.

Consequently the genuine source named-hidden term language,
once its semantics is embedded in this old generated language,
cannot have more semantic functions. That final embedding and
the complete binary hidden language remain separate tasks.
This is not a claim that the syntactic term family is finite. -/
theorem original_named_hidden_endpoint_unary_functions_finite
    (H : HomogeneousSource S G) {i j : ι} :
    (Set.range (fun d : OriginalNamedHiddenOldTermDatum S H i j =>
      originalOldUnaryTermDatum_function S H d.val)).Finite := by
  have hAll := original_old_unary_term_functions_finite
    S H (i := i) (j := j)
  apply hAll.subset
  rintro f ⟨d,rfl⟩
  exact ⟨d.val,rfl⟩

end CCO.TransitionClosure
