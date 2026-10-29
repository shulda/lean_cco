import CCO.ProfileHelly.Theorem

/-! A receiving use of the actual Helly-to-SAP theorem: three arbitrary
complete factors over one complete base have simultaneous induced embeddings,
and EVERY pair meets exactly in that original base, including an empty base.
No amalgamation provider is assumed by this consumer. -/
universe u v z
namespace CCO.ProfileHelly
variable {ι : Type u} {T : Table.{u,v} ι}

theorem three_factor_amalgam (laws : TableLaws T) (helly : Word.Helly (T := T))
    {A L M R : Type z} [Finite A] [Finite L] [Finite M] [Finite R]
    {sortA : A → ι} {sortL : L → ι} {sortM : M → ι} {sortR : R → ι}
    (B : CompleteNetwork T sortA) (C : CompleteNetwork T sortL)
    (D : CompleteNetwork T sortM) (E : CompleteNetwork T sortR)
    (f : Network.Embedding B.toNetwork C.toNetwork)
    (g : Network.Embedding B.toNetwork D.toNetwork)
    (h : Network.Embedding B.toNetwork E.toNetwork) :
    ∃ (W : Type z) (_ : Finite W) (sortW : W → ι) (N : CompleteNetwork T sortW)
      (l : Network.Embedding C.toNetwork N.toNetwork)
      (r : Network.Embedding D.toNetwork N.toNetwork)
      (s : Network.Embedding E.toNetwork N.toNetwork),
      (∀ a, l.point (f.point a) = r.point (g.point a)) ∧
      (∀ a, l.point (f.point a) = s.point (h.point a)) ∧
      (∀ x y, l.point x = r.point y ↔ ∃ a, f.point a = x ∧ g.point a = y) ∧
      (∀ x y, l.point x = s.point y ↔ ∃ a, f.point a = x ∧ h.point a = y) ∧
      ∀ x y, r.point x = s.point y ↔ ∃ a, g.point a = x ∧ h.point a = y := by
  have sap : StrongAmalgamation.{u,v,z} T := (source_providers laws helly).2.2
  obtain ⟨W₁,finite₁,sort₁,N₁,l₁,r₁,comm₁,cross₁⟩ :=
    sap A L M sortA sortL sortM B C D f g
  letI : Finite W₁ := finite₁
  obtain ⟨W₂,finite₂,sort₂,N₂,j,k,comm₂,cross₂⟩ :=
    sap A W₁ R sortA sort₁ sortR B N₁ E (l₁.comp f) h
  refine ⟨W₂,finite₂,sort₂,N₂,j.comp l₁,j.comp r₁,k,?_,?_,?_,?_,?_⟩
  · intro a
    exact congrArg j.point (comm₁ a)
  · exact comm₂
  · intro x y
    change j.point (l₁.point x) = j.point (r₁.point y) ↔ _
    constructor
    · intro he
      exact (cross₁ x y).mp (j.injective he)
    · intro he
      exact congrArg j.point ((cross₁ x y).mpr he)
  · intro x y
    change j.point (l₁.point x) = k.point y ↔ _
    constructor
    · intro he
      obtain ⟨a,ha,hb⟩ := (cross₂ (l₁.point x) y).mp he
      exact ⟨a,l₁.injective ha,hb⟩
    · rintro ⟨a,ha,hb⟩
      exact (cross₂ (l₁.point x) y).mpr
        ⟨a,congrArg l₁.point ha,hb⟩
  · intro x y
    change j.point (r₁.point x) = k.point y ↔ _
    constructor
    · intro he
      obtain ⟨a,ha,hb⟩ := (cross₂ (r₁.point x) y).mp he
      exact ⟨a,r₁.injective ((comm₁ a).symm.trans ha),hb⟩
    · rintro ⟨a,ha,hb⟩
      exact (cross₂ (r₁.point x) y).mpr
        ⟨a,(comm₁ a).trans (congrArg r₁.point ha),hb⟩

end CCO.ProfileHelly
