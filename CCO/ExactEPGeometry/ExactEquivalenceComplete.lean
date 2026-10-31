import CCO.ExactEPGeometry.ExactEquivalenceLattice
import Mathlib.Data.Fintype.Order

/-!
# B062 E2: finite actual exact-equivalence lattices are complete

The ORIGINAL full-RAW-exact equivalence lattice is a finite bounded
lattice, with actual represented RAW products as joins. The standard
Mathlib finite-lattice construction upgrades this precise finite lattice
to a complete lattice, retaining all its actual finite operations.
It does NOT include nonexact invariant equivalences or quotient SAP.
-/

universe u v w t

namespace CCO.ExactEPGeometry.ExactEq

open CCO.ExactEPGeometry

noncomputable section

/-- Complete-lattice structure on the genuine finite full-RAW-exact
equivalences of one actual homogeneous HOM-CCO source sort. The input
lattice, bounds and finiteness have been independently proved on the
represented relation level; only the finite-order completion is reused. -/
@[instance_reducible] def completeLattice
    {ι : Type u} {X : ι → Type v}
    (S : AtomicSource.{u,v,w} ι X)
    {G : Type t} [Group G] [∀ i : ι, MulAction G (X i)]
    (H : HomogeneousSource S G)
    (cco : SemanticCCO.{u,v,max u v,w} S)
    (i : ι) : CompleteLattice (ExactEq S i) := by
  letI : Fintype (ExactEq S i) := Fintype.ofFinite _
  letI : Lattice (ExactEq S i) := ExactEq.lattice S H cco
  letI : BoundedOrder (ExactEq S i) :=
    { toOrderTop := inferInstance
      toOrderBot := inferInstance }
  exact Fintype.toCompleteLattice (ExactEq S i)

end
end CCO.ExactEPGeometry.ExactEq
