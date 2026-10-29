import CCO.OwnerTransversal.NamedSource
import CCO.OwnerTransversal.CountableColourLanguage

/-! A small readout interface for the actual internally constructed
transversal.  The source instance is supplied by the finite-chart
construction; these intermediate fields are not new source hypotheses. -/
universe v w t
namespace CCO.OwnerTransversal
noncomputable section
open ParityHasse.Original RealHull.Geometry RealClosure.Bounds CountableColour
variable {M : Type v} (S : AtomicSource.{0,v,w} Unit (fun _ => M))
variable {G : Type t} [Group G] [MulAction G M] (H : HomogeneousSource S G)
variable [Countable M] [DecidableEq M] (R : ResidualData S H)
variable (B : Finset (Owner S H R))

def tableStructure {U : Type*} (T : Table ↥B (FullColour S) U) :
    FiniteKernel.BinaryStructure U where
  Unary := ↥B
  Binary := FullColour S
  unary b x := T.owner x = b
  binary c x y := T.colour x y = c

abbrev TableAut {U : Type*} (T : Table ↥B (FullColour S) U) :=
  (tableStructure S H R B T).Aut

namespace TableAut
variable {S H R B} {U : Type*} {T : Table ↥B (FullColour S) U}
theorem owner (f : TableAut S H R B T) (x : U) : T.owner (f.val x) = T.owner x :=
  (f.property.1 (T.owner x) x).mpr rfl
theorem colour (f : TableAut S H R B T) (x y : U) :
    T.colour (f.val x) (f.val y) = T.colour x y :=
  (f.property.2 (T.colour x y) x y).mpr rfl
end TableAut

/-- All fields describe the actual age K and its actual homogeneity.
In particular `embed` realizes source charts, not arbitrary invented
triangle tables; `realize_pair` retains every literal old colour. -/
structure TransversalModel (U : Type) where
  table : Table ↥B (FullColour S) U
  realize_pair : ∀ x y : U, x ≠ y → ∃ a b : NamedCarrier S H R B,
    owner S H R a.val = (table.owner x).val ∧
    owner S H R b.val = (table.owner y).val ∧
    col S a.val b.val = table.colour x y ∧ ¬ finitePacket S H a.val b.val
  embed : ∀ {n : ℕ} (a : Fin n → NamedCarrier S H R B),
    (∀ i j, i ≠ j → ¬ finitePacket S H (a i).val (a j).val) →
    ∃ f : Fin n ↪ U,
      (∀ i, (table.owner (f i)).val = owner S H R (a i).val) ∧
      ∀ i j, table.colour (f i) (f j) = col S (a i).val (a j).val
  pair_homogeneous : ∀ x y x' y' : U,
    table.owner x = table.owner x' → table.owner y = table.owner y' →
    table.colour x y = table.colour x' y' →
    ∃ f : TableAut S H R B table, f.val x = x' ∧ f.val y = y'

end
end CCO.OwnerTransversal
