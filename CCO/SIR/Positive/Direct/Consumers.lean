import CCO.SIR.Positive.Direct.Geometry

namespace CCO.SIR.Positive.Direct

/-- Actual old-language one-sort transitivity, with no named-sheet action. -/
theorem transitive (x y : Point) : ∃ g : Aut, g • x = y :=
  source.original_sort_transitive_of_homogeneous homogeneous () x y

/-- At the empty base the direct SIR chooses precisely the old n cross
atoms; real disjointness follows from that literal condition. -/
theorem independent_empty_iff (A B : Finset Point) :
    Independent A ∅ B ↔ ∀ a ∈ A, ∀ b ∈ B, colour a b = some .n := by
  constructor
  · intro h a ha b hb
    rw [colour_n]
    intro hF
    rcases h.2 a ha (by simp) b hb (by simp) hF with ⟨c,hc,_⟩
    simpa using hc
  · intro h
    constructor
    · intro a ha hb
      have hh := (colour_n a a).mp (h a ha a hb)
      exact False.elim (hh rfl)
    · intro a ha _ b hb _ hF
      exact False.elim (((colour_n a b).mp (h a ha b hb)) hF)

/-- A side already contained in the named base has no new cross duties. -/
theorem independent_of_left_subset {A B C : Finset Point} (hAC : A ⊆ C) :
    Independent A C B :=
  ⟨fun _ ha _ => hAC ha,fun a ha hac => False.elim (hac (hAC ha))⟩

/-- A genuine anchored parent admits cross points in its two different
sheets. The old d atom is permitted; no sheet name is adjoined. -/
theorem anchored_pair_independent :
    Independent {(0,false,1)} {(0,false,0)} {(0,true,1)} := by
  constructor
  · intro x hx hb
    simp only [Finset.mem_singleton] at hx hb
    have hh := hx.symm.trans hb
    have hh' : (false : Bool) = true := congrArg sheet hh
    contradiction
  · intro a ha _ b hb _ _
    simp only [Finset.mem_singleton] at ha hb
    subst a; subst b
    exact ⟨(0,false,0),by simp,rfl⟩

/-- The same two real points are dependent over the empty real base. -/
theorem anchored_pair_not_empty_independent :
    ¬ Independent {(0,false,1)} ∅ {(0,true,1)} := by
  intro h
  have hh := (independent_empty_iff _ _).mp h (0,false,1) (by simp) (0,true,1) (by simp)
  have hf := (colour_n _ _).mp hh
  exact hf rfl

/-- An actual independent realization exists over ANY fixed finite real
parameter sets; this consumer has no CCO, NR2, HS or model provider. -/
theorem real_type_existence (A B C : Finset Point) :
    ∃ g : Aut, (∀ c ∈ C, g • c = c) ∧ Independent (transport g A) C B :=
  stationaryIndependence.existence A B C

/-- Explicit pointwise stationarity, with a prescribed old map g on A. -/
theorem real_pointwise_stationarity (A B C : Finset Point) (g : Aut)
    (hg : ∀ c ∈ C, g • c = c)
    (hA : Independent A C B) (hG : Independent (transport g A) C B) :
    ∃ h : Aut, (∀ b ∈ B ∪ C, h • b = b) ∧ ∀ a ∈ A, h • a = g • a :=
  stationaryIndependence.stationarity A B C g hg hA hG

end CCO.SIR.Positive.Direct
