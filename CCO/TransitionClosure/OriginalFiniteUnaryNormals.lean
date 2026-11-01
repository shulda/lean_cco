import CCO.TransitionClosure.OriginalFiniteCanonicalTransitions

/-!
# B049 source07 C38-C39: finite normal-pattern canonical RAW unary maps

A normal pattern from one ACTUAL old quotient i/E to another j/F
consists of one original upward coarsening E≤J followed by one
canonical B040 RAW quotient transition q_(R,J). Its data are
exactly an original FULL invariant source E, one valid finite
canonical transition datum (J,R), and the ACTUAL inclusion E≤J.

All such NORMAL PATTERNS form a finite type for any fixed pair
of ORIGINAL named sorts, and their ACTUAL semantic functions
form a finite IMAGE. Thus one obtains semantic, not syntactic,
finiteness without claiming yet that every arbitrarily mixed
transition/upward word reduces to such a pattern. That is the
separate C39 induction using the already proved TQC/TQU rewrites.

The function is evaluated on real equivalence classes, without
quotient sections, hidden SAP, guessed new equivalences, equality
relabeling or new axioms.
-/

universe u v w t

namespace CCO.TransitionClosure

variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)
variable {G : Type t} [Group G] [∀ s : ι, MulAction G (X s)]

open CCO.ParityHasse.Original
open CCO.QuotientTransport

/-- Actual finite NORMAL-FORM data, with an initial upward
projection from one original FULL E to one original FULL J
and exactly ONE genuine canonical RAW transition datum (J,R).
The final quotient target is the literal transported kernel
Rᵒᵖ;J;R. No finite syntax bound is assumed. -/
abbrev OriginalCanonicalUnaryNormalDatum (i j : ι) :=
  {p : ColourEq S i ×
       OriginalCanonicalRawTransitionDatum S (G := G) i j //
    p.1 ≤ p.2.val.1}

/-- The set of ALL original E≤J initial coarsenings and
finite original canonical RAW transition data is finite.
The proof uses the ACTUAL finite full invariant lattice and
the independently proved finite original old-G RAW relation
tables; source quotient carriers may be infinite. -/
theorem originalCanonicalUnaryNormalDatum_finite
    (H : HomogeneousSource S G) {i j : ι} :
    Finite (OriginalCanonicalUnaryNormalDatum S (G := G) i j) := by
  haveI : Finite (OriginalCanonicalRawTransitionDatum S (G := G) i j) :=
    originalCanonicalRawTransitionDatum_finite S H
  exact Finite.of_injective Subtype.val Subtype.val_injective

/-- The ACTUAL normal-form unary function: quotient projection
E→J first, and then one canonical B040 quotient bijection
for the original-G invariant RAW relation R. This is a
pointwise function between genuinely interpreted OLD
quotient classes, not a syntactic expression code. -/
noncomputable def originalCanonicalUnaryNormalDatum_function
    (H : HomogeneousSource S G)
    {i j : ι} (D : OriginalCanonicalUnaryNormalDatum S (G := G) i j) :
    OriginalCanonicalRawTransitionFunction S i j := by
  let T := originalCanonicalRawTransitionDatum_transport S H D.val.2
  let F := originalTransportTargetColourEq S H D.val.2.val.1 T
  exact ⟨D.val.1,F,fun q =>
    T.quotientEquiv (Quot.mapRight D.property q)⟩

/-- Exact source C39 finite SEMANTIC normal-function image,
for all actual old full source/middle equivalences, nonempty
invariant RAW relations and literal canonical kernels.
Distinct normal data may denote the SAME function and are
not required to be injectively encoded as syntactic terms. -/
theorem original_canonical_unary_normal_functions_finite
    (H : HomogeneousSource S G) {i j : ι} :
    (Set.range
      (originalCanonicalUnaryNormalDatum_function S H
        (i := i) (j := j))).Finite := by
  letI : Finite (OriginalCanonicalUnaryNormalDatum S (G := G) i j) :=
    originalCanonicalUnaryNormalDatum_finite S H
  exact Set.finite_range _

/-- The normal function is evaluated on the LITERAL original
class of a real old point x by first coarsening to its J-class,
then applying the source-derived canonical R-map.

The witness y is one actual old R-successor of x; the equality
is on the REAL output F quotient, including the true equality
cases. No arbitrary section of an original quotient is chosen. -/
theorem originalCanonicalUnaryNormalDatum_real_edge
    (H : HomogeneousSource S G)
    {i j : ι} (D : OriginalCanonicalUnaryNormalDatum S (G := G) i j)
    (x : X i) (y : X j)
    (hR : D.val.2.val.2.val.val x y) :
    let T := originalCanonicalRawTransitionDatum_transport S H D.val.2
    let f := originalCanonicalUnaryNormalDatum_function S H D
    f.2.2 (Quotient.mk D.val.1.val x) =
      Quotient.mk (originalTransportTargetColourEq S H D.val.2.val.1 T).val y := by
  change (originalCanonicalRawTransitionDatum_transport S H D.val.2).quotientEquiv
    (Quot.mapRight D.property (Quotient.mk D.val.1.val x)) = _
  exact (originalCanonicalRawTransitionDatum_transport S H D.val.2).quotientEquiv_edge hR

end CCO.TransitionClosure
