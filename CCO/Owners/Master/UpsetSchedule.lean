import Mathlib.Order.Preorder.Finite
import Mathlib.Data.Finset.Lattice.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Basic

/-! The maximal-complement schedule for the finite owner diagram.
No source geometry, group, EPPA or packet hypothesis is used here. -/

namespace CCO.Owners.Master

variable {P : Type*} [PartialOrder P] [DecidableEq P]

def IsUpset (U : Finset P) : Prop :=
  ∀ ⦃p q⦄, p ∈ U → p ≤ q → q ∈ U

def Next (U : Finset P) (p : P) : Prop :=
  p ∉ U ∧ ∀ ⦃q⦄, p < q → q ∈ U

theorem empty_upset : IsUpset (∅ : Finset P) := by simp [IsUpset]

theorem inter_upset {U V : Finset P} (hU : IsUpset U) (hV : IsUpset V) :
    IsUpset (U ∩ V) := by
  intro p q hp hpq
  exact Finset.mem_inter.mpr ⟨hU (Finset.mem_inter.mp hp).1 hpq,
    hV (Finset.mem_inter.mp hp).2 hpq⟩

theorem union_upset {U V : Finset P} (hU : IsUpset U) (hV : IsUpset V) :
    IsUpset (U ∪ V) := by
  intro p q hp hpq
  rcases Finset.mem_union.mp hp with hp | hp
  · exact Finset.mem_union_left _ (hU hp hpq)
  · exact Finset.mem_union_right _ (hV hp hpq)

theorem next_insert_upset {U : Finset P} {p : P} (hU : IsUpset U) (hp : Next U p) :
    IsUpset (insert p U) := by
  intro q r hq hqr
  rcases Finset.mem_insert.mp hq with rfl | hq
  · rcases eq_or_lt_of_le hqr with rfl | hpr
    · exact Finset.mem_insert_self _ _
    · exact Finset.mem_insert_of_mem (hp.2 hpr)
  · exact Finset.mem_insert_of_mem (hU hq hqr)

theorem next_no_old_predecessor {U : Finset P} {p q : P}
    (hU : IsUpset U) (hp : Next U p) (hq : q ∈ U) : ¬ q ≤ p :=
  fun hqp => hp.1 (hU hq hqp)

theorem next_erase_subset {U V : Finset P} {p : P}
    (hV : V ⊆ insert p U) : V.erase p ⊆ U := by
  intro q hq
  have h := hV (Finset.mem_erase.mp hq).2
  exact (Finset.mem_insert.mp h).resolve_left (Finset.mem_erase.mp hq).1

theorem next_erase_upset {U V : Finset P} {p : P}
    (hU : IsUpset U) (hp : Next U p) (hV : IsUpset V)
    (hVU : V ⊆ insert p U) : IsUpset (V.erase p) := by
  intro q r hq hqr
  have hqU := next_erase_subset hVU hq
  refine Finset.mem_erase.mpr ⟨?_, hV (Finset.mem_erase.mp hq).2 hqr⟩
  intro hr
  subst r
  exact next_no_old_predecessor hU hp hqU hqr

variable [Fintype P]

noncomputable def strictUpper (p : P) : Finset P := by
  classical
  exact Finset.univ.filter (p < ·)

noncomputable def principalUpper (p : P) : Finset P := by
  classical
  exact Finset.univ.filter (p ≤ ·)

@[simp] theorem mem_strictUpper {p q : P} : q ∈ strictUpper p ↔ p < q := by
  classical
  simp [strictUpper]

@[simp] theorem mem_principalUpper {p q : P} : q ∈ principalUpper p ↔ p ≤ q := by
  classical
  simp [principalUpper]

theorem strictUpper_upset (p : P) : IsUpset (strictUpper p) := by
  intro q r hq hqr
  exact mem_strictUpper.mpr (lt_of_lt_of_le (mem_strictUpper.mp hq) hqr)

theorem principalUpper_upset (p : P) : IsUpset (principalUpper p) := by
  intro q r hq hqr
  exact mem_principalUpper.mpr ((mem_principalUpper.mp hq).trans hqr)

theorem strictUpper_insert (p : P) : insert p (strictUpper p) = principalUpper p := by
  ext q
  simp only [Finset.mem_insert, mem_strictUpper, mem_principalUpper]
  exact ⟨fun h => h.elim (fun h => h ▸ le_rfl) le_of_lt,
    fun h => (eq_or_lt_of_le h).imp Eq.symm id⟩

theorem exists_next (U : Finset P) (hU : U ≠ Finset.univ) : ∃ p, Next U p := by
  have hne : (Finset.univ \ U).Nonempty := by
    by_contra h
    apply hU
    apply Finset.eq_univ_of_forall
    intro p
    by_contra hp
    exact h ⟨p, Finset.mem_sdiff.mpr ⟨Finset.mem_univ p, hp⟩⟩
  obtain ⟨p, hp, hmax⟩ := (Finset.univ \ U).exists_maximal hne
  refine ⟨p, (Finset.mem_sdiff.mp hp).2, ?_⟩
  intro q hpq
  by_contra hq
  exact (not_le_of_gt hpq) (hmax (Finset.mem_sdiff.mpr ⟨Finset.mem_univ q, hq⟩) hpq.le)

theorem next_strictUpper_subset {U : Finset P} {p : P} (hp : Next U p) :
    strictUpper p ⊆ U := fun _ hq => hp.2 (mem_strictUpper.mp hq)

theorem next_strictUpper_subset_erase {V : Finset P} {p : P}
    (hV : IsUpset V) (hpV : p ∈ V) : strictUpper p ⊆ V.erase p := by
  intro q hq
  have hpq := mem_strictUpper.mp hq
  exact Finset.mem_erase.mpr ⟨ne_of_gt hpq, hV hpV hpq.le⟩

theorem next_erase_inter_principal {V : Finset P} {p : P}
    (hV : IsUpset V) (hpV : p ∈ V) :
    V.erase p ∩ principalUpper p = strictUpper p := by
  ext q
  constructor
  · intro h
    obtain ⟨hqV, hpq⟩ := Finset.mem_inter.mp h
    exact mem_strictUpper.mpr (lt_of_le_of_ne (mem_principalUpper.mp hpq)
      (Finset.mem_erase.mp hqV).1.symm)
  · intro h
    exact Finset.mem_inter.mpr ⟨next_strictUpper_subset_erase hV hpV h,
      mem_principalUpper.mpr (mem_strictUpper.mp h).le⟩

theorem next_erase_union_principal {V : Finset P} {p : P}
    (hV : IsUpset V) (hpV : p ∈ V) :
    V.erase p ∪ principalUpper p = V := by
  ext q
  constructor
  · intro h
    rcases Finset.mem_union.mp h with h | h
    · exact (Finset.mem_erase.mp h).2
    · exact hV hpV (mem_principalUpper.mp h)
  · intro h
    by_cases hqp : q = p
    · exact Finset.mem_union_right _ (mem_principalUpper.mpr (hqp ▸ le_rfl))
    · exact Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨hqp,h⟩)

/-- Every step chooses a maximal element of the remaining complement, and
the final processed set is the whole poset. -/
def ValidAfter (U : Finset P) : List P → Prop
  | [] => U = Finset.univ
  | p :: rest => Next U p ∧ ValidAfter (insert p U) rest

theorem validAfter_toFinset {U : Finset P} {l : List P} (h : ValidAfter U l) :
    l.toFinset = Finset.univ \ U := by
  induction l generalizing U with
  | nil =>
    change U = Finset.univ at h
    subst U
    simp
  | cons p rest ih =>
    obtain ⟨hp, hrest⟩ := h
    rw [List.toFinset_cons, ih hrest]
    ext q
    by_cases hqp : q = p
    · subst q
      simp [hp.1]
    · simp [hqp]

theorem validAfter_nodup {U : Finset P} {l : List P} (h : ValidAfter U l) :
    l.Nodup := by
  induction l generalizing U with
  | nil => exact List.nodup_nil
  | cons p rest ih =>
    obtain ⟨hp, hrest⟩ := h
    refine List.nodup_cons.mpr ⟨?_, ih hrest⟩
    intro hpRest
    have hpMem : p ∈ rest.toFinset := List.mem_toFinset.mpr hpRest
    rw [validAfter_toFinset hrest] at hpMem
    simpa using hpMem

theorem validAfter_length {U : Finset P} {l : List P} (h : ValidAfter U l) :
    l.length = (Finset.univ \ U).card := by
  rw [← List.toFinset_card_of_nodup (validAfter_nodup h), validAfter_toFinset h]

theorem complement_insert {U : Finset P} (p : P) :
    Finset.univ \ insert p U = (Finset.univ \ U).erase p := by
  ext q
  simp [and_comm, and_left_comm]

/-- The construction terminates after exactly one stage per unprocessed
point. In particular the empty poset uses the empty schedule. -/
theorem exists_validAfter (U : Finset P) : ∃ l, ValidAfter U l := by
  by_cases hU : U = Finset.univ
  · exact ⟨[], hU⟩
  obtain ⟨p, hp⟩ := exists_next U hU
  obtain ⟨rest, hrest⟩ := exists_validAfter (insert p U)
  exact ⟨p :: rest, hp, hrest⟩
termination_by (Finset.univ \ U).card
decreasing_by
  rw [complement_insert]
  exact Finset.card_erase_lt_of_mem (Finset.mem_sdiff.mpr ⟨Finset.mem_univ p, hp.1⟩)

theorem validAfter_prefix_upset {U : Finset P} (hU : IsUpset U)
    (pre rest : List P) (h : ValidAfter U (pre ++ rest)) :
    IsUpset (U ∪ pre.toFinset) := by
  induction pre generalizing U with
  | nil => simpa using hU
  | cons p pre ih =>
    obtain ⟨hp, hrest⟩ := h
    have hnext := ih (next_insert_upset hU hp) hrest
    have heq : insert p U ∪ pre.toFinset = U ∪ (p :: pre).toFinset := by
      ext q
      simp [or_assoc, or_left_comm]
    rwa [heq] at hnext

/-- A complete maximal-first schedule, including its exact stage count. -/
theorem exists_schedule : ∃ l : List P,
    ValidAfter ∅ l ∧ l.Nodup ∧ l.toFinset = Finset.univ ∧ l.length = Fintype.card P := by
  obtain ⟨l, hl⟩ := exists_validAfter (∅ : Finset P)
  refine ⟨l, hl, validAfter_nodup hl, ?_, ?_⟩
  · simpa using validAfter_toFinset hl
  · simpa using validAfter_length hl

end CCO.Owners.Master
