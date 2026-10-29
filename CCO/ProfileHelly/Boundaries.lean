import CCO.ProfileHelly.EdgeCompletion

/-! Duplicate indexed families and small formal carriers. Every word remains
positive; disconnected pairs are filled from the actual nonempty palette. -/
universe u v z q
namespace CCO.ProfileHelly
variable {ι : Type u} {T : Table.{u,v} ι}

namespace Word

/-- Finite indexed Helly allows duplicate profiles and repeated words.
Only the finite IMAGE family is passed to the given Helly property. -/
theorem indexed_helly (helly : Helly (T := T)) {i j : ι}
    {I : Type q} [Finite I] [Nonempty I] (w : I → Word T i j)
    (hp : ∀ a b, ((w a).profile ∩ (w b).profile).Nonempty) :
    ∃ c : T.Atom i j, ∀ a, c ∈ (w a).profile := by
  classical
  let F := (Set.finite_range (fun a => (w a).profile)).toFinset
  have mem (a : I) : (w a).profile ∈ F := by simp [F]
  have image (A : T.Menu i j) : A ∈ F ↔ ∃ a, (w a).profile = A := by simp [F]
  obtain ⟨a⟩ := ‹Nonempty I›
  have hF : F.Nonempty := ⟨(w a).profile,mem a⟩
  have words : ∀ A ∈ F, ∃ p : Word T i j, p.profile = A := by
    intro A hA
    obtain ⟨a,rfl⟩ := (image A).mp hA
    exact ⟨w a,rfl⟩
  have pairs : ∀ A ∈ F, ∀ B ∈ F, (A ∩ B).Nonempty := by
    intro A hA B hB
    obtain ⟨a,rfl⟩ := (image A).mp hA
    obtain ⟨b,rfl⟩ := (image B).mp hB
    exact hp a b
  obtain ⟨c,hc⟩ := helly i j F hF words pairs
  exact ⟨c,fun a => Set.mem_iInter₂.mp hc _ (mem a)⟩

/-- If pairwise means DISTINCT indices, actual positive-profile totality
supplies the diagonal comparisons, including repeated profile values. -/
theorem indexed_helly_pairwise (laws : TableLaws T) (helly : Helly (T := T))
    {i j : ι} {I : Type q} [Finite I] [Nonempty I] (w : I → Word T i j)
    (hp : Pairwise (fun a b => ((w a).profile ∩ (w b).profile).Nonempty)) :
    ∃ c : T.Atom i j, ∀ a, c ∈ (w a).profile := by
  classical
  apply indexed_helly helly w
  intro a b
  by_cases h : a = b
  · subst b
    obtain ⟨c,hc⟩ := profile_nonempty laws (w a)
    exact ⟨c,hc,hc⟩
  · exact hp h

end Word

namespace Network
variable {V : Type z} {sort : V → ι} (D : Network T sort)

/-- C37: with at most two actual formal vertices every simple endpoint path
has length at most one. Two different arcs therefore cannot form a cycle. -/
theorem algebraic_of_card_le_two [Finite V] (hV : Nat.card V ≤ 2) : D.Algebraic := by
  classical
  let : Fintype V := Fintype.ofFinite V
  intro x y hxy p r _ hne
  have hp := p.property.length_lt
  have hr := r.property.length_lt
  have hc : Fintype.card V ≤ 2 := by simpa only [Nat.card_eq_fintype_card] using hV
  have hp' : p.val.length ≤ 1 := by omega
  have hr' : r.val.length ≤ 1 := by omega
  exact False.elim (hne (Subtype.ext (SimpleGraph.Walk.eq_of_length_le_one hp' hr')))

/-- Empty, singleton and two-vertex partial networks all have an actual
fixed-carrier complete extension under the SAME table/Helly assumptions. -/
theorem complete_of_card_le_two [Finite V] (laws : TableLaws T)
    (helly : Word.Helly (T := T)) (hV : Nat.card V ≤ 2) :
    ∃ E : CompleteNetwork T sort, D.Extends E.toNetwork :=
  D.complete_of_algebraic laws helly (D.algebraic_of_card_le_two hV)

theorem algebraic_of_subsingleton [Subsingleton V] : D.Algebraic := by
  intro x y hxy
  exact False.elim (hxy (Subsingleton.elim _ _))

theorem complete_of_subsingleton [Subsingleton V] (laws : TableLaws T)
    (helly : Word.Helly (T := T)) :
    ∃ E : CompleteNetwork T sort, D.Extends E.toNetwork :=
  D.complete_of_algebraic laws helly D.algebraic_of_subsingleton

end Network
end CCO.ProfileHelly
