import CCO.RawExact.SimpleCycleDegreeTwo
import CCO.RawExact.CyclicDeletion

/-!
# Contracting private positions in a cyclic word expansion

A labelled cycle retains a source edge identifier on every traversed
segment. Suppressing an internal position whose two segment labels agree
preserves the set of labels and the marked vertices. Repetition-free
marked cycles can then be read in the original diagram.
-/

universe u v

namespace CCO.RawExact.CyclicSuppression

variable {V : Type u} {E : Type v}

/-- A finite simple cyclic enumeration with an explicit edge identifier
and a proved realization relation for each consecutive segment. -/
structure LabelledCycle (R : E → V → V → Prop) where
  length : Nat
  length_ge_three : 3 ≤ length
  length_pos : 0 < length
  vertices : Fin length ↪ V
  label : Fin length → E
  realises : ∀ p, R (label p) (vertices p) (vertices (cyclicNext length_pos p))

variable {R : E → V → V → Prop}

def VertexOn (C : LabelledCycle R) (v : V) : Prop := ∃ p, C.vertices p = v

def LabelOn (C : LabelledCycle R) (e : E) : Prop := ∃ p, C.label p = e

/-- Three distinct marked vertices displayed on the cycle. -/
structure ThreeMarked (C : LabelledCycle R) (M : V → Prop) where
  points : Fin 3 ↪ V
  marked : ∀ k, M (points k)
  onCycle : ∀ k, VertexOn C (points k)

/-- Removing a nonmarked position from a cycle with three distinct
marked positions never reduces its length below three. -/
theorem length_ge_four_of_private (C : LabelledCycle R) (M : V → Prop)
    (hThree : ThreeMarked C M) (p : Fin C.length) (hp : ¬ M (C.vertices p)) :
    4 ≤ C.length := by
  classical
  obtain ⟨a, ha⟩ := hThree.onCycle 0
  obtain ⟨b, hb⟩ := hThree.onCycle 1
  obtain ⟨c, hc⟩ := hThree.onCycle 2
  have hab : a ≠ b := by
    intro h
    exact hThree.points.injective.ne (by decide : (0 : Fin 3) ≠ 1)
      (ha.symm.trans ((congrArg C.vertices h).trans hb))
  have hac : a ≠ c := by
    intro h
    exact hThree.points.injective.ne (by decide : (0 : Fin 3) ≠ 2)
      (ha.symm.trans ((congrArg C.vertices h).trans hc))
  have hbc : b ≠ c := by
    intro h
    exact hThree.points.injective.ne (by decide : (1 : Fin 3) ≠ 2)
      (hb.symm.trans ((congrArg C.vertices h).trans hc))
  have hap : a ≠ p := by
    intro h
    apply hp
    rw [← h, ha]
    exact hThree.marked 0
  have hbp : b ≠ p := by
    intro h
    apply hp
    rw [← h, hb]
    exact hThree.marked 1
  have hcp : c ≠ p := by
    intro h
    apply hp
    rw [← h, hc]
    exact hThree.marked 2
  have hCard := Finset.card_le_card (Finset.subset_univ ({a, b, c, p} : Finset (Fin C.length)))
  simpa [hab, hac, hbc, hap, hbp, hcp] using hCard

/-- Delete one contractible position while preserving the literal set
of all edge identifiers and every other literal vertex. -/
theorem suppress_private (C : LabelledCycle R) (p : Fin C.length)
    (hLong : 4 ≤ C.length)
    (hContract : ∀ (e f : E) (a b : V),
      R e a (C.vertices p) → R f (C.vertices p) b → a ≠ b →
        e = f ∧ R e a b) :
    ∃ C' : LabelledCycle R,
      C'.length + 1 = C.length ∧
      (∀ v, VertexOn C' v ↔ VertexOn C v ∧ v ≠ C.vertices p) ∧
      (∀ e, LabelOn C' e ↔ LabelOn C e) := by
  rcases C with ⟨L, hThree, hPos, vertices, label, realises⟩
  cases L with
  | zero => omega
  | succ m =>
      change 4 ≤ m + 1 at hLong
      have hm : 0 < m := by omega
      have hmThree : 3 ≤ m := by omega
      let vertices' : Fin m ↪ V :=
        ⟨fun r => vertices (skipIndex p r),
          fun _ _ h => skipIndex_injective p (vertices.injective h)⟩
      have realises' : ∀ r : Fin m,
          R (label (skipIndex p r)) (vertices' r) (vertices' (cyclicNext hm r)) := by
        intro r
        rcases skipIndex_cyclicNext hm p r with hOrdinary | ⟨hDeleted, hAfter⟩
        · change R (label (skipIndex p r)) (vertices (skipIndex p r))
            (vertices (skipIndex p (cyclicNext hm r)))
          rw [hOrdinary]
          exact realises (skipIndex p r)
        · have hBefore := realises (skipIndex p r)
          rw [hDeleted] at hBefore
          have hDifferent : vertices (skipIndex p r) ≠ vertices (cyclicNext (Nat.succ_pos m) p) := by
            have hNew : vertices' r ≠ vertices' (cyclicNext hm r) :=
              vertices'.injective.ne (cyclicNext_ne_self_of_two_le hm (by omega) r).symm
            change vertices (skipIndex p r) ≠ vertices (skipIndex p (cyclicNext hm r)) at hNew
            simpa only [hAfter] using hNew
          have hChord := (hContract (label (skipIndex p r)) (label p)
            (vertices (skipIndex p r)) (vertices (cyclicNext (Nat.succ_pos m) p))
            hBefore (realises p) hDifferent).2
          change R (label (skipIndex p r)) (vertices (skipIndex p r))
            (vertices (skipIndex p (cyclicNext hm r)))
          rw [hAfter]
          exact hChord
      let C' : LabelledCycle R := ⟨m, hmThree, hm, vertices', fun r => label (skipIndex p r), realises'⟩
      refine ⟨C', rfl, ?_, ?_⟩
      · intro v
        change (∃ r, vertices (skipIndex p r) = v) ↔
          (∃ q, vertices q = v) ∧ v ≠ vertices p
        constructor
        · rintro ⟨r, hr⟩
          refine ⟨⟨skipIndex p r, hr⟩, ?_⟩
          intro hEqual
          exact skipIndex_ne p r (vertices.injective (hr.trans hEqual))
        · rintro ⟨⟨q, hq⟩, hDifferent⟩
          have hqp : q ≠ p := by
            intro h
            exact hDifferent (hq.symm.trans (congrArg vertices h))
          obtain ⟨r, hr⟩ := exists_skipIndex_eq p q hqp
          exact ⟨r, (congrArg vertices hr).trans hq⟩
      · intro e
        change (∃ r, label (skipIndex p r) = e) ↔ ∃ q, label q = e
        constructor
        · rintro ⟨r, hr⟩
          exact ⟨skipIndex p r, hr⟩
        · rintro ⟨q, hq⟩
          by_cases hqp : q = p
          · subst q
            obtain ⟨r, hPrev⟩ := exists_skipped_cyclic_predecessor hm p
            have hBefore := realises (skipIndex p r)
            rw [hPrev] at hBefore
            have hDifferent : vertices (skipIndex p r) ≠ vertices (cyclicNext (Nat.succ_pos m) p) := by
              intro h
              have hIndex := vertices.injective h
              exact cyclicNext_no_two_cycle (Nat.succ_pos m) hThree p (skipIndex p r)
                hIndex.symm hPrev
            have hLabels := (hContract (label (skipIndex p r)) (label p)
              (vertices (skipIndex p r)) (vertices (cyclicNext (Nat.succ_pos m) p))
              hBefore (realises p) hDifferent).1
            exact ⟨r, hLabels.trans hq⟩
          · obtain ⟨r, hr⟩ := exists_skipIndex_eq p q hqp
            exact ⟨r, (congrArg label hr).trans hq⟩

/-- Repeatedly suppress private vertices. With three distinct marked
vertices present, the result is an actual simple cycle of marked vertices
in the same cyclic order, preserving EVERY original edge identifier. -/
theorem compress_marked (M : V → Prop)
    (hContract : ∀ v, ¬ M v → ∀ (e f : E) (a b : V),
      R e a v → R f v b → a ≠ b → e = f ∧ R e a b)
    (C : LabelledCycle R) (hThree : ThreeMarked C M) :
    ∃ C' : LabelledCycle R,
      (∀ p, M (C'.vertices p)) ∧
      (∀ v, M v → (VertexOn C' v ↔ VertexOn C v)) ∧
      (∀ e, LabelOn C' e ↔ LabelOn C e) := by
  classical
  suffices h : ∀ N : Nat, ∀ C : LabelledCycle R, C.length = N → ThreeMarked C M →
      ∃ C' : LabelledCycle R,
        (∀ p, M (C'.vertices p)) ∧
        (∀ v, M v → (VertexOn C' v ↔ VertexOn C v)) ∧
        (∀ e, LabelOn C' e ↔ LabelOn C e) from h C.length C rfl hThree
  intro N
  induction N using Nat.strong_induction_on with
  | h N ih =>
      intro C hLength hThree
      by_cases hAll : ∀ p, M (C.vertices p)
      · exact ⟨C, hAll, fun _ _ => Iff.rfl, fun _ => Iff.rfl⟩
      · obtain ⟨p, hp⟩ := not_forall.mp hAll
        have hLong : 4 ≤ C.length := length_ge_four_of_private C M hThree p hp
        obtain ⟨C', hShorter, hVertices, hLabels⟩ := suppress_private C p hLong
          (hContract (C.vertices p) hp)
        have hSmall : C'.length < N := by omega
        have hPointsNe : ∀ k, hThree.points k ≠ C.vertices p := by
          intro k hEqual
          apply hp
          rw [← hEqual]
          exact hThree.marked k
        let hThree' : ThreeMarked C' M := {
          points := hThree.points
          marked := hThree.marked
          onCycle := fun k => (hVertices (hThree.points k)).mpr
            ⟨hThree.onCycle k, hPointsNe k⟩
        }
        obtain ⟨C'', hAll'', hVertices'', hLabels''⟩ := ih C'.length hSmall C' rfl hThree'
        refine ⟨C'', hAll'', ?_, ?_⟩
        · intro v hv
          have hvNe : v ≠ C.vertices p := by
            intro hEqual
            apply hp
            rw [← hEqual]
            exact hv
          have hStep : VertexOn C' v ↔ VertexOn C v :=
            ⟨fun h => ((hVertices v).mp h).1, fun h => (hVertices v).mpr ⟨h, hvNe⟩⟩
          exact (hVertices'' v hv).trans hStep
        · intro e
          exact (hLabels'' e).trans (hLabels e)

end CCO.RawExact.CyclicSuppression
