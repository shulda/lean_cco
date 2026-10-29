import CCO.UnarySupport.LocalEmbeddings

universe u v w
namespace CCO.UnarySupport.Structure.Hom
variable {L : Signature.{u}} {V : Type v} {W : Type w}
variable {C : Structure L V} {H : Structure L W}

def NullaryAgreement (f : Hom C H) : Prop :=
  ∀ R, L.arity R = 0 → ∀ xs, H.rel R (f.point ∘ xs) ↔ C.rel R xs

theorem nullaryAgreement_of_nonempty (f : Hom C H) (hf : f.LocallyInduced)
    (hne : Nonempty V) : f.NullaryAgreement := by
  obtain ⟨x⟩ := hne
  exact fun R hR xs => f.local_nullary hf x R hR xs

theorem locallyInduced_full (f : Hom C H) (hC : C.Total)
    (hbin : ∀ R, L.arity R ≤ 2) (hf : f.LocallyInduced)
    (hnull : f.NullaryAgreement) : f.HomEmbedding := by
  classical
  intro S hS hirr
  by_cases hne : S.Nonempty
  · exact f.locallyInduced_nonempty hC hbin hf S hS hne hirr
  · apply f.embeddingOn_of_total hC hS
    · intro x hx
      exact False.elim (hne ⟨x, hx⟩)
    · intro R xs hxs hr
      by_cases hn : 0 < L.arity R
      · exact False.elim (hne ⟨xs ⟨0, hn⟩, hxs ⟨0, hn⟩⟩)
      · exact (hnull R (by omega) xs).1 hr

theorem locallyInduced_positive (f : Hom C H) (hC : C.Total)
    (hbin : ∀ R, L.arity R ≤ 2) (hf : f.LocallyInduced)
    (hpos : ∀ R, 0 < L.arity R) : f.HomEmbedding := by
  apply f.locallyInduced_full hC hbin hf
  intro R hR
  have h := hpos R
  omega

theorem locallyInduced_nonempty_source (f : Hom C H) (hC : C.Total)
    (hbin : ∀ R, L.arity R ≤ 2) (hf : f.LocallyInduced)
    (hne : Nonempty V) : f.HomEmbedding :=
  f.locallyInduced_full hC hbin hf (f.nullaryAgreement_of_nonempty hf hne)

end CCO.UnarySupport.Structure.Hom
