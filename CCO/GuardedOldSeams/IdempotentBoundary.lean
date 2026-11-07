import CCO.GuardedOldSeams.IdempotentLattice
import CCO.GuardedOldSeams.EnvelopeMI

/-! Actual scope boundaries: diversity is irreflexive; the monolith unit
does not extend to atomic profiles; represented-MI reconstruction itself
forces exactness and hence cannot reconstruct a nonexact invariant. -/
universe u v w t
namespace CCO.GuardedOldSeams
open CCO.ParityHasse.Original CCO.TerminalLattice
noncomputable section
variable {ι : Type u} {X : ι → Type v} (S : AtomicSource.{u,v,w} ι X)

theorem diversity_irreflexive {i : ι} (e : S.Menu i i) :
    ∀ x : X i, ¬ S.menuRel e x x := fun x h => menuRel_ne S h rfl

theorem diversity_not_reflexive {i : ι} (e : S.Menu i i) :
    ¬(∀ x : X i, S.menuRel e x x) := by
  intro h
  obtain ⟨x⟩ := S.nonemptySort i
  exact diversity_irreflexive S e x (h x)

theorem top_diversity_eq_univ {i : ι} :
    originalEquivDiversityPalette S (⊤ : ColourEq S i) = Set.univ := by
  ext a
  constructor
  · intro _; trivial
  · intro _
    obtain ⟨x,y,hxy⟩ := S.realized a
    exact ⟨x,y,trivial,hxy⟩

variable {G : Type t} [Group G] [∀ i, MulAction G (X i)]
variable (H : HomogeneousSource S G) (sap : AgeSAP S)
include H sap

theorem primitive_monolith_eq_top {i : ι}
    (primitive : ∀ E : ColourEq S i, E = ⊥ ∨ E = ⊤) :
    originalMonolith S H sap i = ⊤ := by
  rcases primitive (originalMonolith S H sap i) with h | h
  · exact False.elim ((ne_of_gt (originalMonolith_gt_bot S H sap i)) h)
  · exact h

/-- C67: in ANY genuine original primitive SAP source with two actual
same-sort atoms (in particular the random-graph control), the monolith
diversity sends the positive ONE-LETTER profile to all diversity, not itself. -/
theorem primitive_monolith_not_unit_atom {i : ι}
    (primitive : ∀ E : ColourEq S i, E = ⊥ ∨ E = ⊤)
    (a b : S.Atom i i) (hne : b ≠ a) :
    (∃ word : PositiveWord S i i, PositiveWord.profile S word = {a}) ∧
    S.product (originalEquivDiversityPalette S (originalMonolith S H sap i)) {a} =
      Set.univ ∧
    S.product (originalEquivDiversityPalette S (originalMonolith S H sap i)) {a} ≠ {a} := by
  have hTop := original_top_gt_bot S H sap i
  have hProd := (TerminalProfiles.original_equiv_diversity_reproduction S H sap
    (⊤ : ColourEq S i) hTop {a} (Set.singleton_nonempty a) (by
      rw [top_diversity_eq_univ]; exact Set.subset_univ _)).1
  rw [top_diversity_eq_univ] at hProd
  rw [primitive_monolith_eq_top S H sap primitive,top_diversity_eq_univ]
  refine ⟨⟨PositiveWord.single a,rfl⟩,hProd,?_⟩
  intro h
  have hb : b ∈ ({a} : S.Menu i i) := by rw [← h,hProd]; trivial
  exact hne (Set.mem_singleton_iff.mp hb)

variable (cco : SemanticCCO.{u,v,max u v,w} S)

/-- The represented-MI hull of an ARBITRARY original relation, formed
INSIDE the actual finite exact lattice. Its actual relation is a full
intersection, including Top for the empty family. -/
def representedMIHull {i : ι} (E : Setoid (X i)) : ExactCRT.ExactEq S H cco i := by
  classical
  letI : Fintype (ExactCRT.ExactEq S H cco i) := Fintype.ofFinite _
  exact (Finset.univ.filter fun J : ExactCRT.ExactEq S H cco i =>
    (∀ x y, E x y → J.val x y) ∧ InfIrred J).inf id

omit sap in
theorem representedMIHull_apply {i : ι} (E : Setoid (X i)) (x y : X i) :
    (representedMIHull S H cco E).val x y ↔
      ∀ J : ExactCRT.ExactEq S H cco i,
        (∀ a b, E a b → J.val a b) → InfIrred J → J.val x y := by
  classical
  letI : Fintype (ExactCRT.ExactEq S H cco i) := Fintype.ofFinite _
  unfold representedMIHull
  rw [represented_exact_finset_inf_apply S H cco]
  constructor
  · intro h J hEJ hJ
    exact h J (Finset.mem_filter.mpr ⟨Finset.mem_univ J,hEJ,hJ⟩)
  · intro h J hJ
    exact h J (Finset.mem_filter.mp hJ).2.1 (Finset.mem_filter.mp hJ).2.2

omit sap in
/-- C69: equality to the represented-MI intersection NECESSARILY makes
the original invariant exact; a nonexact invariant cannot be reconstructed. -/
theorem nonexact_not_represented_mi {i : ι} (E : ColourEq S i)
    (nonexact : ¬ExactCRT.IsExactEq S E.val) :
    ¬(∀ x y, E x y ↔ ∀ J : ExactCRT.ExactEq S H cco i,
      (∀ a b, E a b → J.val a b) → InfIrred J → J.val x y) := by
  intro heq
  have hE : E.val = (representedMIHull S H cco E.val).val := by
    apply Setoid.ext
    intro x y
    exact (heq x y).trans (representedMIHull_apply S H cco E.val x y).symm
  exact nonexact (hE ▸ (representedMIHull S H cco E.val).property)

end
end CCO.GuardedOldSeams
