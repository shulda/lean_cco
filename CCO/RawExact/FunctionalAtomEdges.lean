import CCO.Finite

/-!
# B002 C12: glue functional symmetric original atom labels into one diagram

The last step of the RAW private-fan construction needs to identify
a single typed atomic label on every prescribed edge, even when
several independent private-path occurrences describe that edge.

This module proves the generic *construction* from an explicit
functional, converse-compatible label relation. Supplying these
conditions for the real private fan is a separate mathematical
obligation, and no unproved provider is silently instantiated.
The correctness test below constructs this data from ACTUAL old
binary colours, including all distinct original-sort pairs.
-/

universe u v w z

namespace CCO.RawExact

variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)

/-- A family of prescribed typed ORIGINAL atomic edge labels.
Uniqueness and converse are visible mathematical proof fields,
not axioms asserting an arbitrary graph can be coloured. -/
structure TypedAtomEdgeData (V : Type z) (sort : V → ι) where
  label : ∀ (p q : V), S.Atom (sort p) (sort q) → Prop
  functional : ∀ (p q : V) (a b : S.Atom (sort p) (sort q)),
    label p q a → label p q b → a = b
  converse : ∀ (p q : V) (a : S.Atom (sort p) (sort q)),
    label p q a ↔ label q p (S.conv a)

namespace TypedAtomEdgeData

variable {V : Type z} {sort : V → ι}
variable (B : TypedAtomEdgeData S V sort)

/-- A purely local, noncomputable selection of an already-proved
unique edge label. A missing edge has value `none`, NOT an identity atom. -/
noncomputable def edge (p q : V) :
    Option (S.Atom (sort p) (sort q)) := by
  classical
  exact if h : ∃ a : S.Atom (sort p) (sort q), B.label p q a then
    some (Classical.choose h)
  else
    none

/-- The selected atomic label is EXACTLY the given specification;
choice adds no new relation, and functional uniqueness is essential. -/
theorem edge_some_iff (p q : V)
    (a : S.Atom (sort p) (sort q)) :
    edge S B p q = some a ↔ B.label p q a := by
  classical
  unfold edge
  by_cases h : ∃ b : S.Atom (sort p) (sort q), B.label p q b
  · rw [dif_pos h]
    constructor
    · intro hEq
      have ha : Classical.choose h = a := Option.some.inj hEq
      rw [← ha]
      exact Classical.choose_spec h
    · intro ha
      have hEq : Classical.choose h = a :=
        B.functional p q (Classical.choose h) a
          (Classical.choose_spec h) ha
      rw [hEq]
  · rw [dif_neg h]
    constructor
    · intro hEq
      cases hEq
    · intro ha
      exact False.elim (h ⟨a, ha⟩)

/-- Every genuine finite functional converse-compatible edge
specification yields a real `PartialDiagram` on the original
typed diversity palette, without extra mathematical assumptions. -/
noncomputable def toPartialDiagram [Finite V] : PartialDiagram S V where
  finite_type := inferInstance
  vertexSort := sort
  edge := fun p q _ => edge S B p q
  edge_reverse := by
    intro p q hpq a
    exact (edge_some_iff S B p q a).trans
      ((B.converse p q a).trans
        (edge_some_iff S B q p (S.conv a)).symm)

/-- Public consumer: the edge of the actual finite diagram is
present with a precisely given atom iff it was genuinely specified. -/
theorem toPartialDiagram_edge_some_iff [Finite V]
    (p q : V) (hpq : p ≠ q)
    (a : S.Atom (sort p) (sort q)) :
    (toPartialDiagram S B).edge p q hpq = some a ↔ B.label p q a :=
  edge_some_iff S B p q a

end TypedAtomEdgeData

/-- A concrete sound instance: the original source's actual
colours on a family of real points are automatically functional
and satisfy the typed converse law. Neither CCO nor SAP is needed. -/
def actualPointAtomEdgeData
    {V : Type z} (sort : V → ι)
    (point : ∀ p : V, X (sort p)) :
    TypedAtomEdgeData S V sort where
  label := fun p q a => S.colour (point p) (point q) = some a
  functional := by
    intro p q a b ha hb
    exact Option.some.inj (ha.symm.trans hb)
  converse := by
    intro p q a
    exact S.colour_swap (point p) (point q) a

/-- An actual finite original-source tuple gives a bona fide
partial diagram with exactly its recorded diversity edges.
Equality outputs stay absent rather than becoming fake atoms. -/
theorem actualPointAtomEdgeData_correct
    {V : Type z} [Finite V] (sort : V → ι)
    (point : ∀ p : V, X (sort p))
    (p q : V) (hpq : p ≠ q)
    (a : S.Atom (sort p) (sort q)) :
    (TypedAtomEdgeData.toPartialDiagram S (actualPointAtomEdgeData S sort point)).edge p q hpq =
      some a ↔ S.colour (point p) (point q) = some a :=
  TypedAtomEdgeData.toPartialDiagram_edge_some_iff S (actualPointAtomEdgeData S sort point) p q hpq a

end CCO.RawExact
