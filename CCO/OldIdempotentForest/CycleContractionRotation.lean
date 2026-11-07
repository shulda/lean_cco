import CCO.StrongExact.CycleIndexRotation

/-! Literal finite cyclic rotation arithmetic for ordered branch
contraction. These operations change only original occurrence indices;
they introduce no new vertices or completion data. -/

namespace CCO.OldIdempotentForest.CycleGeometry

open CCO.StrongExact

/-- Advance an original cycle occurrence by a natural number of steps. -/
def cycleShift {n : Nat} (hn : 0 < n) (start : Fin n) (distance : Nat) : Fin n :=
  ⟨(start.val + distance) % n,Nat.mod_lt _ hn⟩

theorem cycleShift_val {n : Nat} (hn : 0 < n) (start : Fin n) (distance : Nat) :
    (cycleShift hn start distance).val = (start.val + distance) % n := rfl

/-- Compatibility with the accepted successor-iteration API. -/
theorem cycleShift_eq_advance {n : Nat} (hn : 0 < n) (start : Fin n) (distance : Nat) :
    cycleShift hn start distance = thetaCycleAdvance hn start distance := by
  apply Fin.ext
  exact (thetaCycleAdvance_val hn start distance).symm

@[simp] theorem cycleShift_zero {n : Nat} (hn : 0 < n) (start : Fin n) :
    cycleShift hn start 0 = start := by
  apply Fin.ext
  exact (Nat.mod_eq_of_lt start.isLt)

@[simp] theorem cycleShift_one {n : Nat} (hn : 0 < n) (start : Fin n) :
    cycleShift hn start 1 = cyclicNext hn start := rfl

theorem cycleShift_succ {n : Nat} (hn : 0 < n) (start : Fin n) (distance : Nat) :
    cycleShift hn start (distance + 1) = cyclicNext hn (cycleShift hn start distance) := by
  rw [cycleShift_eq_advance,cycleShift_eq_advance]
  rfl

theorem cycleShift_add {n : Nat} (hn : 0 < n) (start : Fin n) (first second : Nat) :
    cycleShift hn start (first + second) =
      cycleShift hn (cycleShift hn start first) second := by
  simpa only [cycleShift_eq_advance] using thetaCycleAdvance_add hn start first second

theorem cycleShift_from_next {n : Nat} (hn : 0 < n) (start : Fin n) (distance : Nat) :
    cycleShift hn (cyclicNext hn start) distance = cycleShift hn start (distance + 1) := by
  simpa only [cycleShift_eq_advance] using thetaCycleAdvance_from_next hn start distance

@[simp] theorem cycleShift_period {n : Nat} (hn : 0 < n) (start : Fin n) :
    cycleShift hn start n = start := by
  apply Fin.ext
  change (start.val + n) % n = start.val
  simp [Nat.add_mod,Nat.mod_eq_of_lt start.isLt]

theorem cycleShift_add_period {n : Nat} (hn : 0 < n) (start : Fin n) (distance : Nat) :
    cycleShift hn start (distance + n) = cycleShift hn start distance := by
  rw [cycleShift_add,cycleShift_period]

theorem cycleShift_injective_lt {n : Nat} (hn : 0 < n) (start : Fin n)
    (first second : Nat) (hfirst : first < n) (hsecond : second < n)
    (heq : cycleShift hn start first = cycleShift hn start second) : first = second := by
  apply thetaCycleAdvance_injective_lt hn start first second hfirst hsecond
  simpa only [cycleShift_eq_advance] using heq

theorem cycleShift_ne_start {n : Nat} (hn : 0 < n) (start : Fin n)
    (distance : Nat) (hpos : 0 < distance) (hlt : distance < n) :
    cycleShift hn start distance ≠ start := by
  intro heq
  have hzero : cycleShift hn start distance = cycleShift hn start 0 :=
    heq.trans (cycleShift_zero hn start).symm
  have := cycleShift_injective_lt hn start distance 0 hlt hn hzero
  omega

theorem cycleShift_reaches {n : Nat} (hn : 0 < n) (start target : Fin n) :
    ∃ distance : Nat, distance < n ∧ cycleShift hn start distance = target := by
  obtain ⟨distance,hlt,heq⟩ := thetaCycleAdvance_reaches hn start target
  exact ⟨distance,hlt,(cycleShift_eq_advance hn start distance).trans heq⟩

/-- The complete original cyclic occurrence set in a chosen linear order. -/
noncomputable def cycleShiftEquiv {n : Nat} (hn : 0 < n) (start : Fin n) : Fin n ≃ Fin n :=
  Equiv.ofBijective (fun p => cycleShift hn start p.val)
    ⟨fun p q heq => Fin.ext (cycleShift_injective_lt hn start p.val q.val p.isLt q.isLt heq),
      fun target => by
        obtain ⟨distance,hlt,heq⟩ := cycleShift_reaches hn start target
        exact ⟨⟨distance,hlt⟩,heq⟩⟩

theorem cycleShiftEquiv_apply {n : Nat} (hn : 0 < n) (start p : Fin n) :
    cycleShiftEquiv hn start p = cycleShift hn start p.val := rfl

theorem cycleShiftEquiv_eq_rotation {n : Nat} (hn : 0 < n) (start : Fin n) :
    cycleShiftEquiv hn start = cycleRotation hn start := by
  ext p
  rw [cycleShiftEquiv_apply,cycleRotation_apply,cycleShift_eq_advance]

@[simp] theorem cycleShiftEquiv_zero {n : Nat} (hn : 0 < n) (start : Fin n) :
    cycleShiftEquiv hn start ⟨0,hn⟩ = start := cycleShift_zero hn start

/-- Rotation preserves each exact successor edge, including the wrap. -/
theorem cycleShiftEquiv_next {n : Nat} (hn : 0 < n) (start p : Fin n) :
    cycleShiftEquiv hn start (cyclicNext hn p) =
      cyclicNext hn (cycleShiftEquiv hn start p) := by
  rw [cycleShiftEquiv_eq_rotation]
  exact cycleRotation_next hn start p

theorem cycleShift_last_next {n : Nat} (hn : 0 < n) (start : Fin n) :
    cyclicNext hn (cycleShift hn start (n - 1)) = start := by
  rw [← cycleShift_succ]
  have hlength : n - 1 + 1 = n := by omega
  rw [hlength,cycleShift_period]

/-- Starting immediately after an original cut makes that cut's source
the final linear occurrence; no new edge is inserted. -/
theorem cycleShift_after_cut_last {n : Nat} (hn : 0 < n) (cut : Fin n) :
    cycleShift hn (cyclicNext hn cut) (n - 1) = cut := by
  rw [cycleShift_from_next]
  have hlength : n - 1 + 1 = n := by omega
  rw [hlength,cycleShift_period]

theorem cycleShiftEquiv_after_cut_last {n : Nat} (hn : 0 < n) (cut : Fin n) :
    cycleShiftEquiv hn (cyclicNext hn cut) ⟨n - 1,by omega⟩ = cut :=
  cycleShift_after_cut_last hn cut

end CCO.OldIdempotentForest.CycleGeometry
