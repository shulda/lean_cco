import CCO.UnfilteredEP.QuotientUpperRanks
import CCO.ResetOrder.Hierarchy.Lattice

/-! Actual quotient transitions preserve MI-parent fibres. The parent is
computed in the entire finite FULL original lattice, not a chart sublattice.
This supplies the semantic parent-key law for the hierarchical normalizer. -/

universe u v w t
namespace CCO.UnfilteredEP
open ParityHasse.Original TransitionClosure QuotientTransport ResetOrder.Hierarchy
noncomputable section
variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)
variable {G : Type t} [Group G] [∀ i, MulAction G (X i)]
variable (H : HomogeneousSource S G) {i j : ι}
variable (D : ColourEq S i) (E : ColourEq S j)
variable (e : Quotient D.val ≃ Quotient E.val)
variable (equivariant : QuotientEquivariant S H D E e)

/-- The actual full-lattice parent, with all structures constructed
from finite original colours and homogeneous source symmetry. -/
def sourceMIParent : ColourEq S i := by
  letI : Lattice (ColourEq S i) := ColourEq.lattice S H
  letI : Fintype (ColourEq S i) := Fintype.ofFinite _
  exact miParent D

theorem le_sourceMIParent : D ≤ sourceMIParent S H D := by
  letI : Lattice (ColourEq S i) := ColourEq.lattice S H
  letI : Fintype (ColourEq S i) := Fintype.ofFinite _
  exact le_miParent D

theorem sourceMIParent_cover (hD : InfIrred D) : D ⋖ sourceMIParent S H D := by
  letI : Lattice (ColourEq S i) := ColourEq.lattice S H
  letI : Fintype (ColourEq S i) := Fintype.ofFinite _
  exact miParent_covBy hD

/-- C44: the actual FULL unique parent is transported to the actual
FULL unique parent at the other end of the quotient bijection. -/
theorem quotientUpperIso_parent (hD : InfIrred D) (hE : InfIrred E) :
    (quotientUpperIso S H D E e equivariant
      ⟨sourceMIParent S H D,le_sourceMIParent S H D⟩).val = sourceMIParent S H E := by
  have moved := (quotientUpperIso_cover S H D E e equivariant
    ⟨D,le_rfl⟩ ⟨sourceMIParent S H D,le_sourceMIParent S H D⟩).mpr
      (sourceMIParent_cover S H D hD)
  have bottom := quotientUpperIso_bottom S H D E e equivariant
  rw [bottom] at moved
  letI : Lattice (ColourEq S j) := ColourEq.lattice S H
  letI : Fintype (ColourEq S j) := Fintype.ofFinite _
  exact miParent_unique hE moved

/-- The actual upward quotient map to the full MI parent. -/
def sourceParentUp : Quotient D.val → Quotient (sourceMIParent S H D).val :=
  Quotient.map id (fun _ _ h => le_sourceMIParent S H D h)

/-- Equality after the actual parent projection is exactly the descended
FULL parent equivalence on the original represented quotient. -/
theorem sourceParentUp_eq_iff (q r : Quotient D.val) :
    sourceParentUp S H D q = sourceParentUp S H D r ↔
      Transport.descend (E := originalColourEqAsInvEq S H D)
        (originalColourEqAsInvEq S H (sourceMIParent S H D))
        (le_sourceMIParent S H D) q r := by
  induction q using Quotient.inductionOn with | _ x =>
    induction r using Quotient.inductionOn with | _ y =>
      exact Quotient.eq

include equivariant in
/-- The parent KEY law: transported points have equal parent precisely
when the original quotient points do, on every actual quotient fibre. -/
theorem quotient_parent_iff (hD : InfIrred D) (hE : InfIrred E)
    (q r : Quotient D.val) :
    sourceParentUp S H D q = sourceParentUp S H D r ↔
      sourceParentUp S H E (e q) = sourceParentUp S H E (e r) := by
  rw [sourceParentUp_eq_iff,sourceParentUp_eq_iff]
  have relation := quotientUpperIso_relation S H D E e equivariant
    ⟨sourceMIParent S H D,le_sourceMIParent S H D⟩ q r
  have parent := quotientUpperIso_parent S H D E e equivariant hD hE
  have same : quotientUpperIso S H D E e equivariant
      ⟨sourceMIParent S H D,le_sourceMIParent S H D⟩ =
      ⟨sourceMIParent S H E,le_sourceMIParent S H E⟩ := Subtype.ext parent
  have sameRelation := congrArg
    (fun K : {K : ColourEq S j // E ≤ K} =>
      Transport.descend (E := originalColourEqAsInvEq S H E)
        (originalColourEqAsInvEq S H K.val) K.property (e q) (e r)) same
  exact relation.symm.trans (Iff.of_eq sameRelation)

end
end CCO.UnfilteredEP
