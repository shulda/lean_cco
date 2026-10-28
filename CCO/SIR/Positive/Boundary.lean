import CCO.SIR.Positive.Independence

universe u v w
namespace CCO.SIR.Positive
variable {ι : Type u} {X : ι → Type v} (S : AtomicSource.{u,v,w} ι X)
variable [DecidableEq (Sigma X)]

/-- C01: the exact normalized overlap is equivalent to the original
arbitrary finite-set overlap condition. -/
theorem normalized_overlap_iff (A B C : Finset (Sigma X)) :
    (A ∪ C) ∩ (B ∪ C) = C ↔ ∀ x ∈ A, x ∈ B → x ∈ C := by
  constructor
  · intro he x hx hy
    have hm : x ∈ (A ∪ C) ∩ (B ∪ C) := by simp [hx,hy]
    rwa [he] at hm
  · intro ho
    ext x
    simp only [Finset.mem_inter,Finset.mem_union]
    constructor
    · rintro ⟨ha|hc,hb|hc'⟩
      · exact ho x ha hb
      · exact hc'
      · exact hc
      · exact hc
    · exact fun hc => ⟨Or.inr hc,Or.inr hc⟩

theorem independent_cross_distinct (h : Selectors.HereditarySelector S)
    {A B C : Finset (Sigma X)} (hi : Independent S h A C B)
    {a b : Sigma X} (ha : a ∈ A) (hb : b ∈ B) (haC : a ∉ C) : a ≠ b := by
  rintro rfl
  exact haC (hi.1 a ha hb)

theorem independent_empty_left (h : Selectors.HereditarySelector S)
    (B C : Finset (Sigma X)) : Independent S h ∅ C B := by
  simp [Independent]

theorem independent_empty_right (h : Selectors.HereditarySelector S)
    (A C : Finset (Sigma X)) : Independent S h A C ∅ := by
  simp [Independent]

theorem independent_left_in_base (h : Selectors.HereditarySelector S)
    {A B C : Finset (Sigma X)} (hAC : A ⊆ C) : Independent S h A C B :=
  ⟨fun a ha _ => hAC ha,fun a ha _ _ hnot => False.elim (hnot (hAC ha))⟩

end CCO.SIR.Positive
