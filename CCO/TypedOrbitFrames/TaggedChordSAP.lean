import CCO.TypedOrbitFrames.OldTupleSAP

/-!
# B053 C04: genuine original SAP gluing from matching FULL tagged chord colours

The actual shorter OLD typed cycle homomorphisms give two tuples of
original tagged real points whose closing chord pairs have the SAME
complete typed atomic pair colour. This generic receiver converts
that exact original pair-colour equality into the concrete old
diversity atom needed by C03's true finite-induced-image AgeSAP
gluing bridge; it never applies SAP to a noninjective formal source.

The first designated pair must be an actual diversity chord, not
the old logical diagonal. Original pair homogeneity and the same
old colour ensure that the second is also diversity.
-/

universe u v w t z p
namespace CCO.TypedOrbitFrames

variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)

/-- Every pair of actual old finite tuples whose chord images
have the SAME original FULL typed non-diagonal atomic colour
admits one original AgeSAP image amalgam matching both chord
endpoints and preserving ALL original old typed pair colours.
No additional representability or CCO premise is introduced. -/
theorem original_old_tuples_matching_tagged_chord_sap
    {G : Type t} [Group G] [∀ i : ι, MulAction G (X i)]
    (H : HomogeneousSource S G) (sap : AgeSAP S)
    {V : Type z} {W : Type p} [Finite V] [Finite W]
    (f : V → Sigma X) (g : W → Sigma X)
    (u₀ u₁ : V) (v₀ v₁ : W)
    (hSame : taggedColour S (f u₀) (f u₁) =
       taggedColour S (g v₀) (g v₁))
    (hNonDiag : f u₀ ≠ f u₁) :
    ∃ (M : FiniteInduced (X := X))
      (fl : V → Sigma X) (gr : W → Sigma X),
      (∀ u, fl u ∈ M.vertices) ∧
      (∀ v, gr v ∈ M.vertices) ∧
      (∀ u v, taggedColour S (fl u) (fl v) =
        taggedColour S (f u) (f v)) ∧
      (∀ u v, taggedColour S (gr u) (gr v) =
        taggedColour S (g u) (g v)) ∧
      fl u₀ = gr v₀ ∧ fl u₁ = gr v₁ := by
  cases hfu₀ : f u₀ with
  | mk i x =>
    cases hfu₁ : f u₁ with
    | mk j y =>
      cases hgv₀ : g v₀ with
      | mk i' x' =>
        cases hgv₁ : g v₁ with
        | mk j' y' =>
          have hSort₀ : i = i' := by
            exact congrArg Sigma.fst
              (show (⟨i, ⟨j, S.colour x y⟩⟩ :
                Σ m : ι, Σ n : ι, Option (S.Atom m n)) =
                  ⟨i', ⟨j', S.colour x' y'⟩⟩ by
                simpa only [taggedColour, hfu₀, hfu₁,
                  hgv₀, hgv₁] using hSame)
          cases hSort₀
          have hSort₁ : j = j' :=
            congrArg
              (fun q : Σ m : ι, Σ n : ι, Option (S.Atom m n) => q.2.1)
              (by simpa only [taggedColour, hfu₀, hfu₁,
                hgv₀, hgv₁] using hSame)
          cases hSort₁
          have hColours : S.colour x y = S.colour x' y' := by
            have ht : (⟨i, ⟨j, S.colour x y⟩⟩ :
                Σ m : ι, Σ n : ι, Option (S.Atom m n)) =
                  ⟨i, ⟨j, S.colour x' y'⟩⟩ := by
              simpa only [taggedColour, hfu₀, hfu₁,
                hgv₀, hgv₁] using hSame
            simpa only [Sigma.mk.injEq, heq_eq_eq, true_and]
              using ht
          have hneq : (⟨i,x⟩ : Sigma X) ≠ ⟨j,y⟩ := by
            simpa only [hfu₀,hfu₁] using hNonDiag
          have hsome : S.colour x y ≠ none := by
            intro hnone
            exact hneq ((S.colour_none_iff x y).mp hnone)
          cases hcolour : S.colour x y with
          | none =>
              exact False.elim (hsome hcolour)
          | some a =>
              have hcolour' : S.colour x' y' = some a :=
                hColours.symm.trans hcolour
              exact original_old_tuples_same_chord_sap
                S H sap f g a x x' y y' hcolour hcolour'
                u₀ u₁ v₀ v₁ hfu₀ hfu₁ hgv₀ hgv₁

end CCO.TypedOrbitFrames
