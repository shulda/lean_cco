import CCO.Owners.Product.SparseTransport

/-! Empty original sets and empty partial domains do not use nonempty
point lifting. In particular empty requests are included in sparse EPPA. -/
namespace CCO.Owners.Product
variable {G A U : Type*} [Group G] [MulAction G A] {ι : U → A}

theorem eppa_empty_original : EPPAFor (G := G) (ι := ι) (∅ : Set U) := by
  intro p hdom _
  refine ⟨1,?_⟩
  intro x
  exact False.elim (hdom x.property)

theorem eppa_empty_carrier [IsEmpty U] (a : Set U) : EPPAFor (G := G) (ι := ι) a := by
  intro p _ _
  exact ⟨1,fun x => isEmptyElim x.val⟩

theorem empty_partial_identity (p : OrbitalPartial (G := G) ι) (he : p.domain = ∅) :
    p.Extends 1 := by
  intro x
  exact False.elim ((show p.domain ⊆ ∅ from le_of_eq he) x.property)

end CCO.Owners.Product
