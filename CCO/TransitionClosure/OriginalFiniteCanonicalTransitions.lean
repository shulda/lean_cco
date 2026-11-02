import CCO.TransitionClosure.OriginalTransportTargetFull
import CCO.TransitionClosure.OriginalFiniteInvariantRelations

/-!
# B049 source07 C35-C40: finitely many ACTUAL canonical RAW transition functions

The data consist only of a FULL ORIGINAL colour-invariant source
equivalence J and a NONEMPTY invariant typed RAW relation R on
actual old sorts, satisfying its LITERAL R;Rᵒᵖ ⊆ J condition.
These data are FINITE because original homogeneous finite pair
orbitals determine every invariant binary relation, and the full
original invariant equivalence lattice is finite.

Each datum constructs its B040 canonical transport and thus an
ACTUAL quotient bijection from old J-classes to real F=Rᵒᵖ;J;R
classes on the target sort. We count the IMAGE of these
canonical maps, not the infinitely many syntactic expressions
that might denote them. Composable data stay in the finite
family under the exact RAW product, with the SAME middle
target kernel, by the accepted B040 composite lemma.

This is the finite transition-only family; the separate
TQU upward rewrite and terminal named coordinate gates
must still be combined to prove the full arbitrary mixed-term
normal form. No old or hidden quotient SAP/CCO, no additional
equivalence, no syntactic finiteness axiom or new identity.
-/

universe u v w t

namespace CCO.TransitionClosure

variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)
variable {G : Type t} [Group G] [∀ s : ι, MulAction G (X s)]

open ParityHasse.Original
open CCO.QuotientTransport

/-- SOURCE C35: a concrete original source-equivalence J plus
a NONEMPTY invariant OLD typed RAW relation R with the
FULL actual kernel bound R;Rᵒᵖ⊆J. This is FINITE data,
not syntax and not arbitrary quotient-reduct invariance. -/
abbrev OriginalCanonicalRawTransitionDatum (i j : ι) :=
  {p : ColourEq S i ×
      OriginalNonemptyInvariantTypedRel (X := X) (G := G) i j //
    ∀ x z : X i,
      QuotientTransport.compose p.2.val.val
        (QuotientTransport.converse p.2.val.val) x z →
          p.1 x z}

/-- Actual full source finiteness, including TRUE logical
identity for same-sort RAW relations. The condition on
the source kernel only takes a SUBTYPE of a finite type,
never increases the number of function tables. -/
theorem originalCanonicalRawTransitionDatum_finite
    (H : HomogeneousSource S G) {i j : ι} :
    Finite (OriginalCanonicalRawTransitionDatum S (G := G) i j) := by
  haveI : Finite
      (OriginalNonemptyInvariantTypedRel (X := X) (G := G) i j) :=
    originalNonemptyInvariantTypedRel_finite S H
  exact Finite.of_injective Subtype.val Subtype.val_injective

/-- Source-facing actual B040 canonical transport associated
with a FINITE old RAW datum. All hypotheses come from its
literal old source equivalence and genuine nonempty old relation.
The only group action is the homogeneous ORIGINAL ambient G. -/
noncomputable def originalCanonicalRawTransitionDatum_transport
    (H : HomogeneousSource S G)
    {i j : ι} (D : OriginalCanonicalRawTransitionDatum S (G := G) i j) :
    Transport (originalColourEqAsInvEq S H D.val.1)
      D.val.2.val.val :=
  typed_quotient_transport
    (originalColourEqAsInvEq S H D.val.1)
    D.val.2.val.val
    D.val.2.val.property
    D.val.2.property
    (S.original_sort_transitive_of_homogeneous H i)
    (S.original_sort_transitive_of_homogeneous H j)
    (fun x z h => D.property x z h)

/-- The target quotient really is a FULL original invariant
equivalence, and the result records the actual map on genuine
old quotient classes. This heterogeneous sigma allows maps
with different domains and targets without identifying
unrelated sorts or setoids. -/
abbrev OriginalCanonicalRawTransitionFunction (i j : ι) :=
  Σ J : ColourEq S i,
    Σ F : ColourEq S j, Quotient J.val → Quotient F.val

/-- Actual canonical quotient FUNCTION (not a syntactic term)
of one finite old RAW source datum. Its target is exactly
the original FULL transported kernel, not a chosen quotient
chart. The function remains an actual B040 bijection. -/
noncomputable def originalCanonicalRawTransitionDatum_function
    (H : HomogeneousSource S G)
    {i j : ι} (D : OriginalCanonicalRawTransitionDatum S (G := G) i j) :
    OriginalCanonicalRawTransitionFunction S i j := by
  let T := originalCanonicalRawTransitionDatum_transport S H D
  let F := originalTransportTargetColourEq S H D.val.1 T
  exact ⟨D.val.1,F,T.quotientEquiv⟩

/-- Source07 C38 finite ORIGINAL canonical quotient FUNCTIONS
at a fixed pair of named original sorts. This is finiteness
of ACTUAL semantic maps (an image of finite old invariant
relation/source-equivalence tables), not of expressions.

The old original carriers and quotient carriers need not be
finite. Equality of two distinct DATA records is not asserted;
their functions are allowed to coincide. -/
theorem original_canonical_raw_transition_functions_finite
    (H : HomogeneousSource S G) {i j : ι} :
    (Set.range
      (originalCanonicalRawTransitionDatum_function S H
        (i := i) (j := j))).Finite := by
  letI : Finite (OriginalCanonicalRawTransitionDatum S (G := G) i j) :=
    originalCanonicalRawTransitionDatum_finite S H
  exact Set.finite_range _

/-- SOURCE C33/C38 closure of actual finite RAW datum under
composable B040 transitions. The SECOND transport is anchored
to the literal first target kernel, not a separate equivariant
quotient chart. Its source-relation product is the true
old RAW R;Q; the result is still one of the FINITE data.
No new abstract object is added by a composite term. -/
def originalCanonicalRawTransitionDatum_comp
    (H : HomogeneousSource S G)
    {i j k : ι}
    (D : OriginalCanonicalRawTransitionDatum S (G := G) i j)
    (Q : OriginalNonemptyInvariantTypedRel (X := X) (G := G) j k)
    (U : Transport
      (originalCanonicalRawTransitionDatum_transport S H D).target
      Q.val.val) :
    OriginalCanonicalRawTransitionDatum S (G := G) i k := by
  let R := D.val.2
  let E := D.val.1
  let P : OriginalNonemptyInvariantTypedRel (X := X) (G := G) i k :=
    originalNonemptyInvariantTypedRel_comp S H R Q
  let T := originalCanonicalRawTransitionDatum_transport S H D
  let C := T.composite U
  refine ⟨⟨E,P⟩, ?_⟩
  intro x z hXZ
  obtain ⟨y,hXY,hZY⟩ := hXZ
  exact C.kernel x z y hXY hZY

/-- The actual composite RAW datum has precisely the canonical
composition quotient function, with exact B040 target congruence.
No term normalization beyond TWO composable genuine transition
steps is being postulated here. -/
theorem originalCanonicalRawTransitionDatum_comp_semantics
    (H : HomogeneousSource S G)
    {i j k : ι}
    (D : OriginalCanonicalRawTransitionDatum S (G := G) i j)
    (Q : OriginalNonemptyInvariantTypedRel (X := X) (G := G) j k)
    (U : Transport
      (originalCanonicalRawTransitionDatum_transport S H D).target
      Q.val.val)
    (q : Quotient D.val.1.val) :
    let T := originalCanonicalRawTransitionDatum_transport S H D
    let Dcomp := originalCanonicalRawTransitionDatum_comp S H D Q U
    InvEq.quotientCongr (T.composite_target U)
      ((originalCanonicalRawTransitionDatum_transport S H Dcomp).quotientEquiv q) =
        U.quotientEquiv (T.quotientEquiv q) := by
  dsimp
  have hTransport :
      originalCanonicalRawTransitionDatum_transport S H
        (originalCanonicalRawTransitionDatum_comp S H D Q U) =
        (originalCanonicalRawTransitionDatum_transport S H D).composite U :=
    Subsingleton.elim _ _
  rw [hTransport]
  exact (originalCanonicalRawTransitionDatum_transport S H D).composite_quotient U q

end CCO.TransitionClosure
