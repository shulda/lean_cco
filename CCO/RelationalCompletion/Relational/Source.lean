import CCO.RelationalCompletion.Relational.Unfolding

universe u v
namespace CCO.RelationalCompletion.Relational.Structure
variable {L : Language.{u}} {V W : Type v}

/-- The source's finite-family/countable-target specialization. The core is
stronger: countability and completeness of the marked factors are unused.
The conclusion is an injective HE and ACTUAL separate target-image isomorphisms;
it is not a source-factor embedding, a fixed-position assertion, or a joint
image-union isomorphism. -/
theorem finite_family_unfolding (A : Structure L V) (U : Structure L W)
    [Finite V] [Countable W] (hom : U.Homogeneous) (sap : U.AgeSAP)
    (h : V → W) (hh : A.IsHE U h) {m : ℕ} (S : Fin m → Set V)
    (hinj : ∀ i, Set.InjOn h (S i)) :
    ∃ k : V → W, A.IsHE U k ∧ Function.Injective k ∧
      ∀ i, Nonempty (Iso (U.induce (h '' S i)) (U.induce (k '' S i))) := by
  obtain ⟨k, hk, hki, hkt⟩ := collision_unfolding A U hom sap h hh S hinj
  exact ⟨k, hk, hki, fun i => ⟨SameImageType.imageIso (hkt i) (hinj i) hki.injOn⟩⟩

/-- C16: already injective sources need no modification, including empty and
singleton carriers. This statement requires neither SAP nor homogeneity. -/
theorem already_injective (A : Structure L V) (U : Structure L W)
    (h : V → W) (hh : A.IsHE U h) (hi : Function.Injective h)
    {ι : Type*} (S : ι → Set V) :
    ∃ k : V → W, A.IsHE U k ∧ Function.Injective k ∧
      (k = h) ∧ ∀ i, U.SameImageType h k (S i) :=
  ⟨h, hh, hi, rfl, fun _ => SameImageType.refl⟩

end CCO.RelationalCompletion.Relational.Structure
