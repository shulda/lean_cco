import CCO.RawExact.ExactCalculusSource
import CCO.RawExact.ExactSaturations
import CCO.RawExact.ActualOrbitalExact
import CCO.RawExact.PrivatePaths

/-!
# Actual quotient exactness and private word witnesses from source CCO

The quotient maps are actual equivariant maps on original real sorts.
Their full-exact kernels are explicit source data. Original pair-orbital
presentations and heterogeneous ball Helly are constructed, so neither
remains an uninstantiated provider in these C14/C18/C19 exports.
-/

universe u v w

namespace CCO.RawExact

variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)
variable {G : Type*} [Group G] [∀ p : ι, MulAction G (X p)]
variable (H : HomogeneousSource S G)
variable (cco : SemanticCCO.{u,v,max u v,w} S)

include H cco

/-- C14: the pullback of an actual quotient pair orbital is nonempty
full exact, from the two actual exact kernels alone. -/
theorem exact_actual_orbit_pullback_of_CCO
    {i j : ι} {Q R : Type*} [MulAction G Q] [MulAction G R]
    (τ : X i → Q) (σ : X j → R)
    (equivτ : ∀ (g : G) x, τ (g • x) = g • τ x)
    (equivσ : ∀ (g : G) y, σ (g • y) = g • σ y)
    (E : NonemptyExact S i i) (K : NonemptyExact S j j)
    (hE : GroupActions.kernel τ = evaluate S E.words)
    (hK : GroupActions.kernel σ = evaluate S K.words)
    (a : X i) (b : X j) :
    ∃ D : NonemptyExact S i j,
      evaluate S D.words = GroupActions.pullback τ σ
        (GroupActions.orbital (G := G) (τ a) (σ b)) := by
  obtain ⟨A, hA⟩ := actual_original_orbital_exact S H a b
  exact exact_actual_orbit_pullback_of_helly S H
    (heterogeneousExactBallHelly_of_CCO S H cco)
    τ σ equivτ equivσ E K hE hK a b A hA

/-- C18: after constructing the actual orbital presentation, EVERY
choice of real representatives admits all its private word walks.
No compatible family of representatives or quotient section is assumed. -/
theorem actual_orbital_private_paths_of_CCO
    {i j : ι} {Q R : Type*} [MulAction G Q] [MulAction G R]
    (τ : X i → Q) (σ : X j → R)
    (equivτ : ∀ (g : G) x, τ (g • x) = g • τ x)
    (equivσ : ∀ (g : G) y, σ (g • y) = g • σ y)
    (E : NonemptyExact S i i) (K : NonemptyExact S j j)
    (hE : GroupActions.kernel τ = evaluate S E.words)
    (hK : GroupActions.kernel σ = evaluate S K.words)
    (a : X i) (b : X j) :
    ∃ D : NonemptyExact S i j,
      evaluate S D.words = GroupActions.pullback τ σ
        (GroupActions.orbital (G := G) (τ a) (σ b)) ∧
      ∀ (q : Q) (r : R),
        GroupActions.orbital (G := G) (τ a) (σ b) q r →
        ∀ (x : X i) (y : X j), τ x = q → σ y = r →
          Nonempty (PrivatePaths S x y D.words) := by
  obtain ⟨D, hD⟩ := exact_actual_orbit_pullback_of_CCO S H cco
    τ σ equivτ equivσ E K hE hK a b
  refine ⟨D, hD, ?_⟩
  intro q r hqr x y hx hy
  exact orbital_private_paths_of_quotient_pair S τ σ (τ a) (σ b)
    D.words hD q r hqr x y hx hy

/-- C19: full exactness of the actual real-to-quotient request,
including the original logical diagonal. -/
theorem exact_actual_request_of_CCO
    {Q : Type*} [MulAction G Q] {i j : ι}
    (π : X j → Q)
    (equivπ : ∀ (g : G) c, π (g • c) = g • π c)
    (K : NonemptyExact S j j)
    (hK : GroupActions.kernel π = evaluate S K.words)
    (x : X i) (c : X j) :
    ∃ D : NonemptyExact S i j,
      evaluate S D.words =
        GroupActions.pullback (fun y : X i => y) π
          (GroupActions.orbital (G := G) x (π c)) :=
  exact_actual_request_of_helly S H
    (heterogeneousExactBallHelly_of_CCO S H cco) π equivπ K hK x c

/-- C16 exactness: the actual join of two full-exact invariant
equivalences is their represented product and is again full exact. -/
theorem exact_equivalence_join_of_CCO
    {i : ι} (E K : NonemptyExact S i i)
    (hE : RawSymmetric.EquivRel (evaluate S E.words))
    (hK : RawSymmetric.EquivRel (evaluate S K.words)) :
    ∃ J : NonemptyExact S i i,
      evaluate S J.words = RawSymmetric.compose (evaluate S E.words) (evaluate S K.words) ∧
      RawSymmetric.EquivRel (evaluate S J.words) ∧
      (∀ x y, evaluate S E.words x y → evaluate S J.words x y) ∧
      (∀ x y, evaluate S K.words x y → evaluate S J.words x y) ∧
      (∀ L : X i → X i → Prop, RawSymmetric.EquivRel L →
        (∀ x y, evaluate S E.words x y → L x y) →
        (∀ x y, evaluate S K.words x y → L x y) →
        ∀ x y, evaluate S J.words x y → L x y) := by
  let J := convolutionExact S H E K
  have hJ : evaluate S J.words =
      RawSymmetric.compose (evaluate S E.words) (evaluate S K.words) :=
    convolutionExact_represents S H (heterogeneousExactBallHelly_of_CCO S H cco) E K
  have hJoin := S.same_sort_join_of_homogeneous H
    (evaluate S E.words) (evaluate S K.words) hE hK
    (presentation_invariant_of_homogeneous S H E.words)
    (presentation_invariant_of_homogeneous S H K.words)
  refine ⟨J, hJ, ?_⟩
  rw [hJ]
  exact hJoin

end CCO.RawExact
