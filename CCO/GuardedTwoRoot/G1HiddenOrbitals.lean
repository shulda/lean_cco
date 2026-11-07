import CCO.GuardedTwoRoot.G1HiddenModel

/-! The coarse source uses the COMPLETE actual hidden pair orbitals,
not a relationally empty reduct. Every distinct pair has a named symbol,
and two instances of any symbol are moved together by a genuine original
block/bit/clone wreath automorphism. -/

namespace CCO.GuardedTwoRoot.G1.Hidden
open CCO.UnaryFreshFrames
noncomputable section

theorem named_pair_exists (x y : Point) (hne : x ≠ y) :
    ∃ R : RelationName, model.rel R ![x,y] := by
  cases x with
  | inl x =>
    cases y with
    | inl y =>
      cases hc : colour x y with
      | none => exact False.elim (hne (congrArg Sum.inl ((colour_none x y).mp hc)))
      | some a => exact ⟨.inl a,(real_relation a x y).mpr hc⟩
    | inr q =>
      by_cases hb : block x = q
      · exact ⟨.inr (.inr (false,true)),(mixed_forward true x q).mpr (by simp [hb])⟩
      · exact ⟨.inr (.inr (false,false)),(mixed_forward false x q).mpr (by simp [hb])⟩
  | inr q =>
    cases y with
    | inl y =>
      by_cases hb : q = block y
      · exact ⟨.inr (.inr (true,true)),(mixed_reverse true y q).mpr (by simp [hb])⟩
      · exact ⟨.inr (.inr (true,false)),(mixed_reverse false y q).mpr (by simp [hb])⟩
    | inr t =>
      exact ⟨.inr (.inl false),(quotient_offdiagonal q t).mpr
        (fun he => hne (congrArg Sum.inr he))⟩

theorem same_name_owner {R : RelationName} {x y x' y' : Point}
    (h : model.rel R ![x,y]) (h' : model.rel R ![x',y']) :
    owner x = owner y ↔ owner x' = owner y' := by
  cases R with
  | inl a =>
    have hx : sort x = false := h.1
    have hy : sort y = false := h.2.1
    have hx' : sort x' = false := h'.1
    have hy' : sort y' = false := h'.2.1
    rw [← owner_realValue _ hx,← owner_realValue _ hy,
      ← owner_realValue _ hx',← owner_realValue _ hy']
    exact G1.block_of_colour (h.2.2.trans h'.2.2.symm)
  | inr name =>
    cases name with
    | inl same => exact h.2.2.trans h'.2.2.symm
    | inr pair => exact h.2.2.trans h'.2.2.symm

theorem real_pair_name {R : RelationName} {x y : Point}
    (h : model.rel R ![x,y]) (hx : sort x = false) (hy : sort y = false) :
    ∃ a : Atom, R = .inl a ∧ colour (realValue x) (realValue y) = some a := by
  cases R with
  | inl a => exact ⟨a,rfl,h.2.2⟩
  | inr name =>
    cases name with
    | inl same =>
      have hh : false = true := hx.symm.trans h.1
      cases hh
    | inr pair =>
      rcases pair with ⟨direction,same⟩
      cases direction
      · have hh : false = true := hy.symm.trans h.2.1
        cases hh
      · have hh : false = true := hx.symm.trans h.1
        cases hh

theorem same_name_real_colour {R : RelationName} {x y x' y' : Point}
    (h : model.rel R ![x,y]) (h' : model.rel R ![x',y'])
    (hx : sort x = false) (hy : sort y = false) :
    colour (realValue x) (realValue y) = colour (realValue x') (realValue y') := by
  obtain ⟨a,rfl,ha⟩ := real_pair_name h hx hy
  exact ha.trans h'.2.2.symm

/-- Each named hidden relation is ONE actual orbital of the original
block/bit/clone action, including the true quotient diagonal. -/
theorem same_name_motion {R : RelationName} {x y x' y' : Point}
    (h : model.rel R ![x,y]) (h' : model.rel R ![x',y']) :
    ∃ g : model.Aut, g • x = x' ∧ g • y = y' := by
  let f : Bool → Point := fun b => if b then y else x
  let t : Bool → Point := fun b => if b then y' else x'
  have hSort : ∀ b, sort (f b) = sort (t b) := by
    intro b
    cases b
    · exact h.1.trans h'.1.symm
    · exact h.2.1.trans h'.2.1.symm
  have hOwner : ∀ b c, owner (f b) = owner (f c) ↔ owner (t b) = owner (t c) := by
    intro b c
    cases b <;> cases c
    · exact ⟨fun _ => rfl,fun _ => rfl⟩
    · exact same_name_owner h h'
    · exact eq_comm.trans ((same_name_owner h h').trans eq_comm)
    · exact ⟨fun _ => rfl,fun _ => rfl⟩
  have hColour : ∀ b c, sort (f b) = false → sort (f c) = false →
      colour (realValue (f b)) (realValue (f c)) =
        colour (realValue (t b)) (realValue (t c)) := by
    intro b c hb hc
    cases b <;> cases c
    · exact ((colour_none _ _).mpr rfl).trans ((colour_none _ _).mpr rfl).symm
    · exact same_name_real_colour h h' hb hc
    · exact (colour_symm _ _).trans
        ((same_name_real_colour h h' hc hb).trans (colour_symm _ _))
    · exact ((colour_none _ _).mpr rfl).trans ((colour_none _ _).mpr rfl).symm
  obtain ⟨g,hg⟩ := finite_extension f t hSort hOwner hColour
  exact ⟨g,hg false,hg true⟩

end
end CCO.GuardedTwoRoot.G1.Hidden
