import CCO.UnaryFreshFrames.Examples.TwoCoverOrbits

/-! The second C49 obstruction has ALL forced named factors, but an actual
unforced relative index TWO. Algebraicity is witnessed for the full group,
while explicit automorphisms witness motion off named unary closure. -/
namespace CCO.UnaryFreshFrames.Examples.TwoCover
open Structure

theorem full_aut_middle_fibre (q : ℕ) (d : Bool) (g : model.Aut)
    (hg : g • rootPoint q = rootPoint q) :
    g • middle q d ∈ ({middle q false, middle q true} : Set Point) := by
  have hs : sort (g • middle q d) = 1 := model.aut_sort g (middle q d)
  have hr := model.aut_func g 1 (middle q d)
  change g • rootPoint q = operation 1 (g • middle q d) at hr
  rw [hg] at hr
  generalize he : g • middle q d = y at hs hr ⊢
  rcases y with ⟨⟨r,c⟩,n⟩ | (⟨r,c⟩ | r)
  · simp [sort] at hs
  · have heq : q = r := by simpa [operation,rootPoint] using hr
    subst r
    cases c <;> simp [middle]
  · simp [sort] at hs

theorem full_middle_orbit (q : ℕ) (d : Bool) :
    orbitOver model.Aut {rootPoint q} (middle q d) = {middle q false, middle q true} := by
  ext y
  constructor
  · rintro ⟨g, rfl⟩
    exact full_aut_middle_fibre q d g.val (g.property (rootPoint q) rfl)
  · rintro (rfl | rfl)
    all_goals apply (mem_orbitOver_iff model.Aut).mpr
    · exact ⟨wreathAut 1 (fun _ => Equiv.swap d false) (fun _ => 1),
        fun z hz => (by have he : z = rootPoint q := hz; subst z; rfl),
        by change middle q (Equiv.swap d false d) = _; simp⟩
    · exact ⟨wreathAut 1 (fun _ => Equiv.swap d true) (fun _ => 1),
        fun z hz => (by have he : z = rootPoint q := hz; subst z; rfl),
        by change middle q (Equiv.swap d true d) = _; simp⟩

theorem algebraic_off_closure (q : ℕ) (d : Bool) :
    middle q d ∈ Acl model.Aut {rootPoint q} ∧
      middle q d ∉ model.closureAt (rootPoint q) := by
  refine ⟨?_,middle_off_root_closure q d⟩
  change (orbitOver model.Aut {rootPoint q} (middle q d)).Finite
  rw [full_middle_orbit]
  exact (Set.finite_singleton _).insert _

/-- Actual real-source kernel inclusion for a named projection F. -/
def ForcedBy (F : Fin 4) {j : language.Sorts} (t : Term language 0 j) : Prop :=
  ∀ x y, sort x = 0 → sort y = 0 → operation F x = operation F y →
    model.eval t x = model.eval t y

/-- One named-term equality globalizes using actual real-sort transitivity. -/
theorem factor_tau_from_one {j : language.Sorts} (t : Term language 0 j)
    (s : Term language 1 j)
    (he : model.eval t (real 0 false 0) = model.eval s (middle 0 false)) :
    ∀ q d n, model.eval t (real q d n) = model.eval s (middle q d) := by
  intro q d n
  obtain ⟨g, hg⟩ := real_transitive 0 q false d 0 n
  have hm := model.aut_func g 0 (real 0 false 0)
  change g • middle 0 false = operation 0 (g • real 0 false 0) at hm
  rw [hg] at hm
  calc
    model.eval t (real q d n) = g • model.eval t (real 0 false 0) :=
      (congrArg (model.eval t) hg).symm.trans (model.aut_eval g t _).symm
    _ = g • model.eval s (middle 0 false) := congrArg (fun z => g • z) he
    _ = model.eval s (g • middle 0 false) := model.aut_eval g s _
    _ = model.eval s (middle q d) := congrArg (model.eval s) hm

theorem factor_p_from_one {j : language.Sorts} (t : Term language 0 j)
    (s : Term language 2 j)
    (he : model.eval t (real 0 false 0) = model.eval s (rootPoint 0)) :
    ∀ q d n, model.eval t (real q d n) = model.eval s (rootPoint q) := by
  intro q d n
  obtain ⟨g, hg⟩ := real_transitive 0 q false d 0 n
  have hm := model.aut_func g 2 (real 0 false 0)
  change g • rootPoint 0 = operation 2 (g • real 0 false 0) at hm
  rw [hg] at hm
  calc
    model.eval t (real q d n) = g • model.eval t (real 0 false 0) :=
      (congrArg (model.eval t) hg).symm.trans (model.aut_eval g t _).symm
    _ = g • model.eval s (rootPoint 0) := congrArg (fun z => g • z) he
    _ = model.eval s (g • rootPoint 0) := model.aut_eval g s _
    _ = model.eval s (rootPoint q) := congrArg (model.eval s) hm

/-- All forced terms for the actual quotient p have the named identity
factor on Q. A common flip moves every non-Q point of the reference closure. -/
theorem forced_p_named_factor {j : language.Sorts} (t : Term language 0 j)
    (hForced : ForcedBy 2 t) :
    ∃ s : Term language 2 j, ∀ x, sort x = 0 →
      model.eval t x = model.eval s (operation 2 x) := by
  let a := wreathAut 1 (fun _ => Equiv.swap false true) (fun _ => Equiv.swap 0 1)
  have hmove : a • real 0 false 0 = real 0 true 1 := by
    change real 0 (Equiv.swap false true false) (Equiv.swap 0 1 0) = _
    simp
  have hfixed : model.eval t (real 0 false 0) = a • model.eval t (real 0 false 0) := by
    have h := hForced (real 0 false 0) (real 0 true 1) rfl rfl rfl
    exact h.trans ((congrArg (model.eval t) hmove).symm.trans (model.aut_eval a t _).symm)
  have hm : model.eval t (real 0 false 0) ∈ model.closureAt (real 0 false 0) :=
    ⟨real 0 false 0, rfl, j, t, rfl⟩
  rw [real_closure] at hm
  have hr : model.eval t (real 0 false 0) = rootPoint 0 := by
    rcases hm with h | h | h | h
    · rw [h] at hfixed
      have he : (0 : ℕ) = 1 := congrArg coordinate hfixed
      exact False.elim (Nat.zero_ne_one he)
    · rw [h] at hfixed
      have he : false = true := congrArg bit hfixed
      exact False.elim (Bool.false_ne_true he)
    · rw [h] at hfixed
      have he : true = false := congrArg bit hfixed
      exact False.elim (Bool.false_ne_true he.symm)
    · exact h
  have hj : j = 2 := (model.eval_sort t rfl).symm.trans (congrArg model.sort hr)
  subst j
  refine ⟨(Term.id (L := language) (2 : Fin 3)), ?_⟩
  intro x hx
  obtain ⟨q,d,n,rfl⟩ := real_of_sort hx
  exact factor_p_from_one t (Term.id (L := language) (2 : Fin 3)) hr q d n

/-- For the actual quotient τ, the named factors are id_V, swap_V, or r.
This covers EVERY existing named real-source term, not just generators. -/
theorem forced_tau_named_factor {j : language.Sorts} (t : Term language 0 j)
    (hForced : ForcedBy 0 t) :
    ∃ s : Term language 1 j, ∀ x, sort x = 0 →
      model.eval t x = model.eval s (operation 0 x) := by
  let a := wreathAut 1 (fun _ => 1) (fun _ => Equiv.swap 0 1)
  have hmove : a • real 0 false 0 = real 0 false 1 := by
    change real 0 false (Equiv.swap 0 1 0) = _
    simp
  have hfixed : model.eval t (real 0 false 0) = a • model.eval t (real 0 false 0) := by
    have h := hForced (real 0 false 0) (real 0 false 1) rfl rfl rfl
    exact h.trans ((congrArg (model.eval t) hmove).symm.trans (model.aut_eval a t _).symm)
  have hm : model.eval t (real 0 false 0) ∈ model.closureAt (real 0 false 0) :=
    ⟨real 0 false 0, rfl, j, t, rfl⟩
  rw [real_closure] at hm
  rcases hm with h | h | h | h
  · rw [h] at hfixed
    have he : (0 : ℕ) = 1 := congrArg coordinate hfixed
    exact False.elim (Nat.zero_ne_one he)
  · have hj : j = 1 := (model.eval_sort t rfl).symm.trans (congrArg model.sort h)
    subst j
    refine ⟨(Term.id (L := language) (1 : Fin 3)), ?_⟩
    intro x hx
    obtain ⟨q,d,n,rfl⟩ := real_of_sort hx
    exact factor_tau_from_one t (Term.id (L := language) (1 : Fin 3)) h q d n
  · have hj : j = 1 := (model.eval_sort t rfl).symm.trans (congrArg model.sort h)
    subst j
    refine ⟨(Term.func (L := language) (3 : Fin 4) (Term.id (L := language) (1 : Fin 3))), ?_⟩
    intro x hx
    obtain ⟨q,d,n,rfl⟩ := real_of_sort hx
    exact factor_tau_from_one t (Term.func (L := language) (3 : Fin 4) (Term.id (L := language) (1 : Fin 3))) h q d n
  · have hj : j = 2 := (model.eval_sort t rfl).symm.trans (congrArg model.sort h)
    subst j
    refine ⟨(Term.func (L := language) (1 : Fin 4) (Term.id (L := language) (1 : Fin 3))), ?_⟩
    intro x hx
    obtain ⟨q,d,n,rfl⟩ := real_of_sort hx
    exact factor_tau_from_one t (Term.func (L := language) (1 : Fin 4) (Term.id (L := language) (1 : Fin 3))) h q d n

end CCO.UnaryFreshFrames.Examples.TwoCover
