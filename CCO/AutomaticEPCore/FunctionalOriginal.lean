import CCO.PairHomogeneity
import CCO.ParityHasse.Original.OrbitalBipartite
import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.Combinatorics.SimpleGraph.Bipartite
import Mathlib.SetTheory.Cardinal.Order

/-!
# The original equivariant functional group

C09–C13 use only the actual original transitive homogeneous symmetric
orbital source. The group consists of ALL equivariant real permutations;
it is not the automorphism group of a chosen marked expansion. AP, SAP,
CCO, exactness, quotient towers and terminality are absent from this proof.
-/

namespace CCO.AutomaticEPCore

universe u v w r

/-- All permutations commuting with the given original action. -/
def originalFunctionalGroup (G : Type r) (M : Type v) [Group G] [MulAction G M] :
    Subgroup (Equiv.Perm M) where
  carrier := {h | ∀ (g : G) (x : M), h (g • x) = g • h x}
  one_mem' := by intro g x; rfl
  mul_mem' := by
    intro h k hh hk g x
    change h (k (g • x)) = g • h (k x)
    rw [hk,hh]
  inv_mem' := by
    intro h hh g x
    apply h.injective
    change h (h.symm (g • x)) = h (g • h.symm x)
    rw [h.apply_symm_apply,hh,h.apply_symm_apply]

abbrev OriginalFunctionalGroup (G : Type r) (M : Type v) [Group G] [MulAction G M] :=
  ↥(originalFunctionalGroup G M)

variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)
variable {G : Type r} [Group G] [∀ i : ι, MulAction G (X i)]
variable (H : HomogeneousSource S G) {i : ι}

include S H

/-- Evaluation at one original point determines the entire equivariant
permutation, using transitivity of the SAME original group. -/
theorem original_functional_eval_injective (x : X i) :
    Function.Injective (fun h : OriginalFunctionalGroup G (X i) => h.val x) := by
  intro h k he
  change h.val x = k.val x at he
  apply Subtype.ext
  apply Equiv.ext
  intro y
  obtain ⟨g,hg⟩ := S.original_sort_transitive_of_homogeneous H i x y
  rw [← hg,h.property,k.property,he]

/-- A fixed real point forces an original equivariant permutation to be
identity. This is not a marked-source freeness assertion. -/
theorem original_functional_eq_one_of_fixed
    (h : OriginalFunctionalGroup G (X i)) (x : X i) (hx : h.val x = x) :
    h = 1 := by
  apply original_functional_eval_injective S H x
  exact hx

theorem original_functional_no_fixed
    (h : OriginalFunctionalGroup G (X i)) (hne : h ≠ 1) (x : X i) :
    h.val x ≠ x :=
  fun hx => hne (original_functional_eq_one_of_fixed S H h x hx)

/-- A functional graph is one complete original pair orbital, including
logical equality exactly when the permutation is identity. -/
theorem original_functional_colour_iff
    (h : OriginalFunctionalGroup G (X i)) (x₀ x y : X i) :
    S.colour x y = S.colour x₀ (h.val x₀) ↔ h.val x = y := by
  constructor
  · intro hcol
    obtain ⟨g,hgx,hgy⟩ := S.pair_homogeneous_of_homogeneous H
      x₀ x (h.val x₀) y hcol.symm
    rw [← hgx,h.property,hgy]
  · rintro rfl
    obtain ⟨g,hg⟩ := S.original_sort_transitive_of_homogeneous H i x₀ x
    rw [← hg,h.property]
    exact S.colourInvariant_of_homogeneous H g x₀ (h.val x₀)

/-- The graph of EVERY nonidentity equivariant permutation is ONE actual
original diversity atom, with the full relation biconditional. -/
theorem original_functional_graph_atom
    (h : OriginalFunctionalGroup G (X i)) (hne : h ≠ 1) :
    ∃ a : S.Atom i i, ∀ x y : X i, S.atomRel a x y ↔ h.val x = y := by
  obtain ⟨x₀⟩ := S.nonemptySort i
  cases hc : S.colour x₀ (h.val x₀) with
  | none =>
      have he := (S.colour_none_iff x₀ (h.val x₀)).mp hc
      have hx : h.val x₀ = x₀ := by
        have htag : x₀ = h.val x₀ := by
          simpa only [Sigma.mk.injEq,heq_eq_eq,true_and] using he
        exact htag.symm
      exact False.elim (original_functional_no_fixed S H h hne x₀ hx)
  | some a =>
      refine ⟨a,?_⟩
      intro x y
      change S.colour x y = some a ↔ h.val x = y
      rw [← hc]
      exact original_functional_colour_iff S H h x₀ x y

/-- Symmetry of actual same-sort orbital atoms makes every original
functional permutation involutive. -/
theorem original_functional_involutive (h : OriginalFunctionalGroup G (X i)) :
    Function.Involutive h.val := by
  by_cases hOne : h = 1
  · subst h
    intro x
    rfl
  · obtain ⟨a,ha⟩ := original_functional_graph_atom S H h hOne
    intro x
    apply (ha (h.val x) x).mp
    have hx := (ha x (h.val x)).mpr rfl
    change S.colour (h.val x) x = some a
    simpa only [S.symmetricLoop] using (S.colour_swap x (h.val x) a).mp hx

theorem original_functional_square_one (h : OriginalFunctionalGroup G (X i)) :
    h * h = 1 := by
  apply Subtype.ext
  apply Equiv.ext
  exact original_functional_involutive S H h

theorem original_functional_inv_eq (h : OriginalFunctionalGroup G (X i)) :
    h⁻¹ = h := by
  have hs := original_functional_square_one S H h
  calc
    h⁻¹ = h⁻¹ * 1 := (mul_one _).symm
    _ = h⁻¹ * (h * h) := by rw [hs]
    _ = h := by rw [← mul_assoc,inv_mul_cancel,one_mul]

/-- Every product also has exponent two, so this original functional
group is abelian, rather than just a collection of involutions. -/
theorem original_functional_mul_comm (h k : OriginalFunctionalGroup G (X i)) :
    h * k = k * h := by
  calc
    h * k = (h * k)⁻¹ := (original_functional_inv_eq S H (h * k)).symm
    _ = k⁻¹ * h⁻¹ := mul_inv_rev h k
    _ = k * h := by rw [original_functional_inv_eq S H k,
      original_functional_inv_eq S H h]

/-- Explicit commutative-group structure, retaining the same permutation
multiplication and action. -/
@[instance_reducible] def originalFunctionalCommGroup :
    CommGroup (OriginalFunctionalGroup G (X i)) where
  __ := (inferInstance : Group (OriginalFunctionalGroup G (X i)))
  mul_comm := original_functional_mul_comm S H

/-- The original functional group is finite because its graph code is
one of the finitely many actual orbital atoms or logical identity. -/
theorem original_functional_finite : Finite (OriginalFunctionalGroup G (X i)) := by
  let : Fintype (S.Atom i i) := S.finiteAtom i i
  obtain ⟨x₀⟩ := S.nonemptySort i
  apply Finite.of_injective (fun h : OriginalFunctionalGroup G (X i) =>
    S.colour x₀ (h.val x₀))
  intro h k he
  apply original_functional_eval_injective S H x₀
  exact (original_functional_colour_iff S H h x₀ x₀ (k.val x₀)).mp he.symm

/-- A fixed-point-free functional atom is an actual bipartite graph.
A classical ordering only witnesses the two sides of each matching pair;
no preferred component orientation is included in the structure. -/
theorem original_functional_atom_bipartite
    (h : OriginalFunctionalGroup G (X i)) (hne : h ≠ 1)
    (a : S.Atom i i)
    (ha : ∀ x y : X i, S.atomRel a x y ↔ h.val x = y) :
    (ParityHasse.Original.atomGraph S a).IsBipartite := by
  classical
  let : LinearOrder (X i) := linearOrderOfSTO WellOrderingRel
  let colour : X i → Fin 2 := fun x => if x < h.val x then 0 else 1
  refine ⟨{ toFun := colour, map_rel' := ?_ }⟩
  intro x y hxy
  have hfun : h.val x = y := (ha x y).mp hxy
  subst y
  have hInv := original_functional_involutive S H h x
  by_cases hx : x < h.val x
  · have hhx : ¬ h.val x < h.val (h.val x) := by
      rw [hInv]
      exact not_lt_of_gt hx
    simp only [colour,ite_eq_left hx,ite_eq_right hhx]
    decide
  · have hlt : h.val x < x := lt_of_le_of_ne (le_of_not_gt hx)
      (original_functional_no_fixed S H h hne x)
    have hhx : h.val x < h.val (h.val x) := by rw [hInv]; exact hlt
    simp only [colour,ite_eq_right hx,ite_eq_left hhx]
    decide

/-- C13 with the actual old orbital and the actual whole-graph bipartition. -/
theorem original_functional_bipartite_atom
    (h : OriginalFunctionalGroup G (X i)) (hne : h ≠ 1) :
    ∃ a : S.Atom i i,
      (∀ x y : X i, S.atomRel a x y ↔ h.val x = y) ∧
        (ParityHasse.Original.atomGraph S a).IsBipartite := by
  obtain ⟨a,ha⟩ := original_functional_graph_atom S H h hne
  exact ⟨a,ha,original_functional_atom_bipartite S H h hne a ha⟩

end CCO.AutomaticEPCore
