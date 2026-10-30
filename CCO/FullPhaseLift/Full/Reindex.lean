import CCO.FullPhaseLift.Full.ChosenPair

/-! Finite ordinal charts are only a size normalization of the RAW A03
quantifiers. This transports every signed tuple and the SAME complete
frozen factors, including empty carriers/factors and nullary declarations. -/

universe v w z
namespace CCO.FullPhaseLift.Full
open Canonical
variable {L : Signature} {M : Type w} {V : Type v} {W : Type z}

theorem smallSupport_of_injective_comp {n : ℕ} {xs : Fin n → W} {f : W → V}
    (hf : Function.Injective f) (h : SmallSupport (f ∘ xs)) : SmallSupport xs := by
  intro i j k
  rcases h i j k with he | he | he
  · exact Or.inl (hf he)
  · exact Or.inr (Or.inl (hf he))
  · exact Or.inr (Or.inr (hf he))

def FrozenFactor.reindex {U : BoolTable L M} {D : Partial L V}
    (F : FrozenFactor U D) (e : W ≃ V) : FrozenFactor U (D.pullback e) where
  size := F.size
  inclusion := F.inclusion.trans e.symm.toEmbedding
  table := F.table
  age := F.age
  agrees r xs := by
    simpa [Partial.pullback,Function.comp_def] using F.agrees r xs

theorem consistent_reindex {U : BoolTable L M} {D : Partial L V}
    (h : Consistent U D) (e : W ≃ V) : Consistent U (D.pullback e) := by
  intro n hn j
  obtain ⟨p,hp⟩ := h n hn (j.trans e.toEmbedding)
  exact ⟨p,hp⟩

theorem higherCovered_reindex {U : BoolTable L M} {D : Partial L V} {m : ℕ}
    (F : Fin m → FrozenFactor U D) (h : HigherCovered F) (e : W ≃ V) :
    HigherCovered (fun j => (F j).reindex e) := by
  intro r xs b hd hs
  have hn : ¬ SmallSupport (e ∘ xs) :=
    fun hh => hs (smallSupport_of_injective_comp e.injective hh)
  obtain ⟨j,hj⟩ := h r (e ∘ xs) b hd hn
  refine ⟨j,?_⟩
  rintro x ⟨a,rfl⟩
  obtain ⟨c,hc⟩ := hj ⟨a,rfl⟩
  refine ⟨c,?_⟩
  change e.symm ((F j).inclusion c) = xs a
  simpa only [Function.comp_apply,Equiv.symm_apply_apply] using congrArg e.symm hc

theorem pairCompletion_reindex {U : BoolTable L M} {D : Partial L V} {m : ℕ}
    (F : Fin m → FrozenFactor U D) (h : PairCompletion U D F) (e : W ≃ V) :
    PairCompletion U (D.pullback e) (fun j => (F j).reindex e) := by
  obtain ⟨p,hp,hi⟩ := h
  refine ⟨e.toEmbedding.trans p,?_,?_⟩
  · intro r xs b hs hd
    exact hp r (e ∘ xs) b (hs.comp e) hd
  · intro j a b hab
    apply hi j
    change p ((F j).inclusion a) = p ((F j).inclusion b)
    change p (e (e.symm ((F j).inclusion a))) =
      p (e (e.symm ((F j).inclusion b))) at hab
    simpa only [Equiv.apply_symm_apply] using hab

/-- The exact raw source interface applies to arbitrary finite carriers
and vertex universes; normalization changes neither any signed declaration
nor any complete factor or its final map. -/
theorem SupportNormal.realize_finite {U : BoolTable L M} (normal : SupportNormal U)
    [Finite V] (D : Partial L V) (m : ℕ) (F : Fin m → FrozenFactor U D)
    (hc : Consistent U D) (hcov : HigherCovered F) (hp : PairCompletion U D F) :
    ∃ f : V → M, Realizes U D f ∧ ∀ j, (F j).FixedBy f := by
  classical
  letI : Fintype V := Fintype.ofFinite V
  let e : Fin (Fintype.card V) ≃ V := (Fintype.equivFin V).symm
  let D' := D.pullback e
  let F' : Fin m → FrozenFactor U D' := fun j => (F j).reindex e
  obtain ⟨f,hf,hfix⟩ := normal (Fintype.card V) D' m F'
    (consistent_reindex hc e) (higherCovered_reindex F hcov e)
    (pairCompletion_reindex F hp e)
  refine ⟨f ∘ e.symm,?_,?_⟩
  · intro r xs b hd
    have hd' : D' r (e.symm ∘ xs) = some b := by
      simpa [D',Partial.pullback,Function.comp_def] using hd
    exact hf r (e.symm ∘ xs) b hd'
  · intro j
    exact hfix j

theorem lift_chosen_pairs_finite {U : BoolTable L M}
    (sep : SeparatesPoints U) (normal : SupportNormal U) [Finite V]
    (D : Partial L V) (m : ℕ) (F : Fin m → FrozenFactor U D)
    (covered : HigherCovered F) (p : V ↪ M) (hp : LowRealizes U D p) :
    ∃ q : V ↪ M, Realizes U D q ∧ (∀ j, (F j).FixedBy q) ∧ LowEquivalent U q p := by
  let D' := augmentLow U D p
  let F' : Fin m → FrozenFactor U D' := fun j => (F j).augment p hp
  have hpair : PairCompletion U D' F' := by
    refine ⟨p,?_,?_⟩
    · intro r xs b hs hd
      change augmentLow U D p r xs = some b at hd
      rw [augmentLow_small U D p r xs hs] at hd
      exact Option.some.inj hd
    · intro j
      exact p.injective.comp (F j).inclusion.injective
  obtain ⟨q,hq,hfix⟩ := normal.realize_finite D' m F'
    (augmentLow_consistent U D p) (higherCovered_augment F covered p hp) hpair
  have hl : LowEquivalent U q p := by
    intro r xs hs
    exact hq r xs _ (augmentLow_small U D p r xs hs)
  let q' : V ↪ M := ⟨q,injective_of_lowEquivalent U sep p q hl⟩
  refine ⟨q',?_,?_,hl⟩
  · intro r xs b hd
    exact hq r xs b (augmentLow_extends U D p hp r xs b hd)
  · intro j
    exact hfix j

end CCO.FullPhaseLift.Full
