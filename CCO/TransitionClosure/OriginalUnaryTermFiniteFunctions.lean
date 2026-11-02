import CCO.TransitionClosure.OriginalUnaryTermNormalization

/-!
# B049 source07 C38-C40: finite semantic image of all OLD unary terms

An arbitrary finite, well-typed word in genuine FULL old quotient
projections and canonical original RAW transitions has exactly the
same interpreted unary quotient function as one finite normal pattern.
This is proved on ALL real quotient classes using seriality of the
source's ACTUAL canonical RAW relation and the prior structural
induction on syntactic terms.

The semantic image is therefore contained in the independently
proved finite image of normal-pattern functions. The number of
syntactic terms is not asserted finite. This is the FULL original
invariant-quotient generated language, not yet the smaller named
represented-terminal hidden-coordinate export; no quotient SAP,
terminal NR2, or fake positive STRONG identity is introduced.
-/

universe u v w t

namespace CCO.TransitionClosure

variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)
variable {G : Type t} [Group G] [∀ s : ι, MulAction G (X s)]

open CCO.ParityHasse.Original
open CCO.QuotientTransport

/-- All finite unary expressions from one ACTUAL original sort
to another, with their freely varying FULL real start/end
equivalence kernels recorded in the dependent indices. -/
abbrev OriginalOldUnaryTermDatum
    (H : HomogeneousSource S G) (i j : ι) :=
  Σ E : ColourEq S i, Σ F : ColourEq S j,
    OriginalOldUnaryWord S H i E j F

/-- The semantic function of an arbitrary original generated
term, with its true source AND target quotient types recorded.
This set may contain many equal terms; we count functions. -/
noncomputable def originalOldUnaryTermDatum_function
    (H : HomogeneousSource S G)
    {i j : ι} (d : OriginalOldUnaryTermDatum S H i j) :
    OriginalCanonicalRawTransitionFunction S i j :=
  OriginalOldUnaryWord.function S H d.2.2

/-- SOURCE C38/C39, the actual function-level content of the
whole arbitrary mixed-term induction: the term's TRUE quotient
function, not just its representative edges, equals the function
of one FINITE original normal datum. Identity and arbitrarily
many mixed-sort transition/upward alternations are included. -/
theorem OriginalOldUnaryWord.normal_function
    (H : HomogeneousSource S G)
    {i j : ι} {E : ColourEq S i} {F : ColourEq S j}
    (w : OriginalOldUnaryWord S H i E j F) :
    ∃ N : OriginalCanonicalUnaryNormalDatum S (G := G) i j,
      OriginalOldUnaryWord.function S H w =
        originalCanonicalUnaryNormalDatum_function S H N := by
  obtain ⟨N,hSource,hTarget,hEdge⟩ :=
    OriginalOldUnaryWord.normal_relation S H w
  refine ⟨N,?_⟩
  subst E
  subst F
  have hFun :
      OriginalOldUnaryWord.eval S H w =
        (originalCanonicalUnaryNormalDatum_function S H N).2.2 := by
    funext q
    induction q using Quotient.inductionOn with
    | _ x =>
        let T := originalCanonicalRawTransitionDatum_transport S H N.val.2
        obtain ⟨y,hxy⟩ := T.serial x
        exact (hEdge x y hxy).trans
          (originalCanonicalUnaryNormalDatum_real_edge S H N x y hxy).symm
  change
    (⟨N.val.1,
        originalTransportTargetColourEq S H N.val.2.val.1
          (originalCanonicalRawTransitionDatum_transport S H N.val.2),
        OriginalOldUnaryWord.eval S H w⟩ :
          OriginalCanonicalRawTransitionFunction S i j) =
      (⟨N.val.1,
        originalTransportTargetColourEq S H N.val.2.val.1
          (originalCanonicalRawTransitionDatum_transport S H N.val.2),
        (originalCanonicalUnaryNormalDatum_function S H N).2.2⟩ :
          OriginalCanonicalRawTransitionFunction S i j)
  rw [hFun]

/-- C39/C40 finite SEMANTIC image of the WHOLE original
generated unary language, for each pair of actual old named
sorts, allowing ALL full input/output quotient kernels and
ALL finite mixed terms. The ambient carriers may be infinite.
This is not finiteness of syntax or a terminal represented
membership/hidden-sorts theorem. -/
theorem original_old_unary_term_functions_finite
    (H : HomogeneousSource S G) {i j : ι} :
    (Set.range
      (originalOldUnaryTermDatum_function S H (i := i) (j := j))).Finite := by
  have hFinite :=
    original_canonical_unary_normal_functions_finite S H (i := i) (j := j)
  apply hFinite.subset
  intro f hf
  obtain ⟨d,rfl⟩ := hf
  obtain ⟨N,hN⟩ := OriginalOldUnaryWord.normal_function S H d.2.2
  exact ⟨N,hN.symm⟩

end CCO.TransitionClosure
