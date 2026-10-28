import CCO.RawExact.AtomicExact
import CCO.RawExact.QuotientRequests

/-!
# Equality-inclusive exact presentations of actual original and mixed orbitals

The atomic presentation is constructed from the actual original pair.
The optional `none` case forces literal tagged equality and therefore a
true same-sort identity word. Exact quotient requests are then supplied
by their actual exact kernel and the proved C09 convolution consumer;
only C13 remains explicit.
-/

universe u v w

namespace CCO.RawExact

variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)

/-- The actual optional colour of every original pair is nonempty exact,
including the genuine logical diagonal. -/
theorem actual_pair_colour_exact {i j : ι} (x : X i) (c : X j) :
    ∃ A : NonemptyExact S i j,
      evaluate S A.words = S.rawAtomRel (S.colour x c) := by
  cases hc : S.colour x c with
  | some a =>
      refine ⟨exactDiversityAtom S a, ?_⟩
      rw [exactDiversityAtom_relation S a]
      rfl
  | none =>
      have htag : (⟨i, x⟩ : Sigma X) = ⟨j, c⟩ :=
        (S.colour_none_iff x c).mp hc
      cases htag
      refine ⟨exactIdentityAtom S i, ?_⟩
      exact exactIdentityAtom_is_optional_none S i

/-- Original homogeneity identifies the constructed exact relation with
the complete actual original pair orbit. No atomic provider is assumed. -/
theorem actual_original_orbital_exact
    {G : Type*} [Group G] [∀ p : ι, MulAction G (X p)]
    (H : HomogeneousSource S G) {i j : ι}
    (x : X i) (c : X j) :
    ∃ A : NonemptyExact S i j,
      evaluate S A.words = GroupActions.orbital (G := G) x c := by
  obtain ⟨A, hA⟩ := actual_pair_colour_exact S x c
  exact ⟨A, hA.trans (actual_pair_orbital_of_homogeneous S H x c).symm⟩

/-- An actual equivariant quotient with a full-exact kernel has exact
mixed real-to-quotient requests. The atomic and request presentations
are constructed rather than left as additional arbitrary providers. -/
theorem exact_actual_request_of_helly
    {G Q : Type*} [Group G]
    [∀ p : ι, MulAction G (X p)] [MulAction G Q]
    (H : HomogeneousSource S G)
    (hHelly : HeterogeneousExactBallHelly S)
    {i j : ι} (π : X j → Q)
    (equivπ : ∀ (g : G) c, π (g • c) = g • π c)
    (K : NonemptyExact S j j)
    (hK : GroupActions.kernel π = evaluate S K.words)
    (x : X i) (c : X j) :
    ∃ D : NonemptyExact S i j,
      evaluate S D.words =
        GroupActions.pullback (fun y : X i => y) π
          (GroupActions.orbital (G := G) x (π c)) := by
  obtain ⟨A, hA⟩ := actual_original_orbital_exact S H x c
  refine ⟨convolutionExact S H A K, ?_⟩
  calc
    evaluate S (convolutionExact S H A K).words =
        TRel.comp (evaluate S A.words) (evaluate S K.words) :=
      convolutionExact_represents S H hHelly A K
    _ = TRel.comp (GroupActions.orbital (G := G) x c)
          (GroupActions.kernel π) := by rw [hA, hK]
    _ = GroupActions.pullback (fun y : X i => y) π
          (GroupActions.orbital (G := G) x (π c)) :=
      (original_quotient_request_pullback π equivπ x c).symm

end CCO.RawExact
