import CCO.RawExact.DistinctCentres
import CCO.Finite

/-!
# B002 C12: complete original-centre induced diagrams

Distinct actual tagged original centres carry exactly the literal old
pair colours, including the genuine optional diagonal. Whenever two
formal indices are different, injectivity makes that colour a REAL
diversity atom. The centre subdiagram is therefore complete and has
an old homomorphism with every centre point fixed.

This is the marked-centre base of an eventual private-word fan; it
does not add artificial equality edges or assume any CCO theorem.
-/

universe u v w z

namespace CCO.RawExact

variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)

/-- Genuine finite induced centre graph on an injectively listed set
of ACTUAL tagged real points, never just on sort names. -/
def actualCentreDiagram
    {I : Type z} [Finite I]
    (centres : I ↪ Sigma X) : PartialDiagram S I where
  finite_type := inferInstance
  vertexSort := fun t => (centres t).1
  edge := fun p q _ => S.colour (centres p).2 (centres q).2
  edge_reverse := by
    intro p q hpq a
    exact S.colour_swap (centres p).2 (centres q).2 a

theorem actualCentreDiagram_complete
    {I : Type z} [Finite I]
    (centres : I ↪ Sigma X) :
    (actualCentreDiagram S centres).IsComplete := by
  intro p q hpq
  cases hc : S.colour (centres p).2 (centres q).2 with
  | none =>
      have hpqEq : (centres p : Sigma X) = centres q :=
        (S.colour_none_iff (centres p).2 (centres q).2).mp hc
      exact False.elim (hpq (centres.injective hpqEq))
  | some a =>
      exact ⟨a, hc⟩

/-- Its literal original centre map already is a real homomorphism.
Only attaching the private paths creates new consistency conditions. -/
def actualCentreDiagram_realization
    {I : Type z} [Finite I]
    (centres : I ↪ Sigma X) :
    DiagramHom (actualCentreDiagram S centres) where
  point := fun t => (centres t).2
  preserves_edge := by
    intro p q hpq a ha
    exact ha

theorem actualCentreDiagram_cycles
    {I : Type z} [Finite I]
    (centres : I ↪ Sigma X) :
    ∀ C : SimpleCycle (actualCentreDiagram S centres), CycleHom C := by
  intro C
  exact ⟨fun p => (centres (C.vertices p)).2, by
    intro p a ha
    exact ha⟩

end CCO.RawExact
