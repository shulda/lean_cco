import CCO.PairHomogeneity
import Mathlib.Data.Fintype.Option

/-!
# B049 source07 C59: literal canonical old qf tuple-type definitional enrichment

The original SOURCE07 visible language is FINITE and BINARY. Its current
nonempty individually named old sorts are already unary type tags.
Consequently its complete realised quantifier-free tuple types, through
the maximum OLD relation arity TWO, are:

* the unique empty tuple type;
* the unique one-point type for EACH FIXED original named sort;
* for each compatible fixed ordered sort pair (i,j), precisely the
  REALISED optional old fine colour S.colour x y, including true old
  same-sort equality as NONE and genuine diversity orbitals as SOME a.

Only actually realised colours are named here: no invented cross-sort
identity, unoccupied optional type or higher-arity relational symbol.

These old canonical predicates are DEFINED by equality to the actual
old colour. They partition every compatible original old pair, are
finite even when the old real sorts are infinite, and are preserved
by the original homogeneous G action. Crucially, preserving ALL the
new labels is logically EQUIVALENT to preserving the existing old
pair colours on any typed partial domain. Thus adding their names is
a literal qf definitional expansion and does NOT modify embeddings,
partial automorphisms, SAP or old homogeneity; any external EPPA/Ramsey
transfer remains subject to its own provider contracts.

No new axiom, STRONG identity, quotient SAP/CCO or independent hidden
automorphism action is assumed. This is the SOURCE07 binary old-tuple
naming gate, not a proof of a separate hidden-language Ramsey theorem.
-/

universe u v w t

namespace CCO.TransitionClosure

variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)
variable {G : Type t} [Group G] [∀ i : ι, MulAction G (X i)]

/-- Source07 nullary OLD qf tuple type: there is exactly one
empty tuple on the actual compatible empty list of old sort tags. -/
abbrev OriginalOldNullaryType := PUnit

/-- Each FIXED original named sort supplies exactly one old unary
qf type, as original sort-transitivity is already assumed. -/
abbrev OriginalOldUnaryType (_i : ι) := PUnit

/-- True realised complete OLD canonical binary qf types on fixed
named sorts i,j. The actual atom colour is optional because the
original logical diagonal is NOT an irreflexive diversity atom. -/
abbrev OriginalOldRealizedPairType (i j : ι) :=
  {c : Option (S.Atom i j) //
    ∃ x : X i, ∃ y : X j, S.colour x y = c}

/-- The actual old pair's one complete canonical fine qf type. -/
def originalOldRealizedPairType_of_pair
    {i j : ι} (x : X i) (y : X j) :
    OriginalOldRealizedPairType S i j :=
  ⟨S.colour x y, ⟨x,y,rfl⟩⟩

/-- Every realised complete binary old qf type is a member of
an ACTUALLY FINITE family. No finiteness of original real sorts
or quotient classes is asserted. -/
theorem originalOldRealizedPairType_finite {i j : ι} :
    Finite (OriginalOldRealizedPairType S i j) := by
  letI : Fintype (S.Atom i j) := S.finiteAtom i j
  exact Finite.of_injective Subtype.val Subtype.val_injective

/-- Definitional new old complete qf pair-type predicate: the
original optional old fine colour equals its truly realised name. -/
def originalOldRealizedPairTypePredicate
    {i j : ι} (c : OriginalOldRealizedPairType S i j)
    (x : X i) (y : X j) : Prop :=
  S.colour x y = c.val

/-- Actual partition: EVERY compatible old typed real pair has
EXACTLY ONE full qf pair-type label. In particular equality and
diversity are distinguished by genuine old colour NONE/SOME. -/
theorem originalOldRealizedPairTypePredicate_existsUnique
    {i j : ι} (x : X i) (y : X j) :
    ∃! c : OriginalOldRealizedPairType S i j,
      originalOldRealizedPairTypePredicate S c x y := by
  refine ⟨originalOldRealizedPairType_of_pair S x y, rfl, ?_⟩
  intro c hc
  apply Subtype.ext
  exact hc.symm

/-- Each complete old qf pair-type predicate is invariant under
the ACTUAL original homogeneous action G on the original sorts. -/
theorem originalOldRealizedPairTypePredicate_invariant
    (H : HomogeneousSource S G)
    {i j : ι} (c : OriginalOldRealizedPairType S i j)
    (g : G) (x : X i) (y : X j)
    (h : originalOldRealizedPairTypePredicate S c x y) :
    originalOldRealizedPairTypePredicate S c (g • x) (g • y) := by
  exact (S.colourInvariant_of_homogeneous H g x y).trans h

/-- QF DEFINITIONAL EXTENSION / REDUCT equivalence:
on any typed old partial domain, a pair of sort-respecting
maps preserves all NEW complete qf two-point predicates iff it
preserves the ORIGINAL full optional old pair-colour itself.

No global totality, new embedding assumption, quotient action or
old age condition is inserted. Applying this equivalence to
injections on arbitrary finite partial old diagrams certifies
that the added predicate names change neither old embeddings
nor old partial automorphism maps. -/
theorem originalOldRealizedPairTypePredicate_preservation_iff
    {i j : ι} (f : X i → X i) (g : X j → X j) :
    (∀ x y, S.colour (f x) (g y) = S.colour x y) ↔
      (∀ c : OriginalOldRealizedPairType S i j,
        ∀ x y,
        originalOldRealizedPairTypePredicate S c (f x) (g y) ↔
          originalOldRealizedPairTypePredicate S c x y) := by
  constructor
  · intro h c x y
    change S.colour (f x) (g y) = c.val ↔ S.colour x y = c.val
    rw [h x y]
  · intro h x y
    have hh := (h (originalOldRealizedPairType_of_pair S x y) x y).mpr rfl
    exact hh

/-- C59 partial-domain version. A sort-preserving map whose
domain is ANY chosen subset of each old named sort preserves
the existing canonical fine OLD pair colour on every specified
domain pair iff it preserves EVERY newly named realised complete
qf pair-type predicate ON THOSE SAME PAIRS.

There is no extension to the full old carrier, no loss of source
pinning, no assumption on injectivity, no name for an unrealised
old type and no hidden-quotient SAP. For an injective typed
partial map this is exactly preservation/reflection of the
binary relational diagram needed for a partial embedding. -/
theorem originalOldRealizedPairTypePredicate_partial_preservation_iff
    {i j : ι} (A : Set (X i)) (B : Set (X j))
    (f : A → X i) (g : B → X j) :
    (∀ (x : A) (y : B),
       S.colour (f x) (g y) = S.colour x.val y.val) ↔
      (∀ (c : OriginalOldRealizedPairType S i j)
          (x : A) (y : B),
        originalOldRealizedPairTypePredicate S c (f x) (g y) ↔
          originalOldRealizedPairTypePredicate S c x.val y.val) := by
  constructor
  · intro h c x y
    change S.colour (f x) (g y) = c.val ↔
      S.colour x.val y.val = c.val
    rw [h x y]
  · intro h x y
    have hh :=
      (h (originalOldRealizedPairType_of_pair S x.val y.val) x y).mpr rfl
    exact hh

/-- C59 for the ENTIRE many-sorted original old binary
language, simultaneously across all compatible sort pairs.
A partial map has an arbitrary domain predicate D_i on EACH
literal source sort i; the equivalence holds for EVERY
chosen family of typed partial maps, with NO further
hypotheses and NO ambient-domain extension.

In particular, restricting to injections proves that the
new old qf tuple-predicate names do not alter the original
partial embeddings or partial automorphisms. The actual
original sort labels are already part of the dependent
types, so this checks cross-sort pairs too. -/
theorem originalOldRealizedPairTypePredicate_allSorts_partial_iff
    (D : ∀ i : ι, Set (X i))
    (f : ∀ i : ι, D i → X i) :
    (∀ (i j : ι) (x : D i) (y : D j),
      S.colour (f i x) (f j y) = S.colour x.val y.val) ↔
      (∀ (i j : ι) (c : OriginalOldRealizedPairType S i j)
           (x : D i) (y : D j),
        originalOldRealizedPairTypePredicate S c (f i x) (f j y) ↔
          originalOldRealizedPairTypePredicate S c x.val y.val) := by
  constructor
  · intro h i j c x y
    exact
      (originalOldRealizedPairTypePredicate_partial_preservation_iff
        S (D i) (D j) (f i) (f j)).mp
          (fun u v => h i j u v) c x y
  · intro h i j x y
    exact
      (originalOldRealizedPairTypePredicate_partial_preservation_iff
        S (D i) (D j) (f i) (f j)).mpr
          (fun c u v => h i j c u v) x y

end CCO.TransitionClosure
