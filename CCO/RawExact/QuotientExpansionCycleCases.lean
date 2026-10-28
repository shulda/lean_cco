import CCO.RawExact.QuotientExpansionCompression

/-!
# Every raw expansion cycle uses one marked edge or a genuine marked cycle

Whole-path closure puts both endpoints of each traversed word on the
cycle. If three marked vertices occur, suppression gives their simple
cyclic order with every edge identifier retained. Otherwise exactly two
marked vertices occur and every traversed word belongs to their ONE edge.
-/

universe u v w
namespace CCO.RawExact.QuotientExpansion

variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)
variable {n : Nat} (sort : Fin n → ι) (P : Menus S sort)
variable (hNonempty : ∀ e, TRel.Nonempty (evaluate S (P e)))

/-- Even one traversed edge of a private word forces both its marked
endpoints onto the raw cycle. An interior invokes whole-path closure. -/
theorem traversed_word_endpoints
    (C : SimpleCycle (diagram S sort P hNonempty))
    (o : Occurrence S sort P) (p q : PathPosition S (word S sort P o))
    (hpq : pathAdjacent S (word S sort P o) p q)
    (hpOn : CycleVertex C (atPosition S sort P o p))
    (hqOn : CycleVertex C (atPosition S sort P o q)) :
    CycleVertex C (mark S sort P (left o.1)) ∧
      CycleVertex C (mark S sort P (right o.1)) := by
  have hpBound := p.isLt
  have hqBound := q.isLt
  have hPositive : 0 < diversityLength S (word S sort P o) := by
    rcases hpq with h | h <;> omega
  have hFromInterior : ∀ r : Interior S sort P o,
      CycleVertex C (interior S sort P o r) →
        CycleVertex C (mark S sort P (left o.1)) ∧ CycleVertex C (mark S sort P (right o.1)) := by
    intro r hr
    have hAll := (whole_path_on_cycle_of_interior S sort P C
      (simpleCycle_adjacent S sort P hNonempty C) o r hr).1
    have hLeft := hAll (pathStart S (word S sort P o))
    have hRight := hAll (pathFinish S (word S sort P o))
    rw [at_start] at hLeft
    rw [at_finish S sort P o hPositive] at hRight
    exact ⟨hLeft, hRight⟩
  by_cases hpInt : p.val ≠ 0 ∧ p.val ≠ diversityLength S (word S sort P o)
  · apply hFromInterior ⟨p, hpInt⟩
    rw [← at_interior S sort P o ⟨p, hpInt⟩]
    exact hpOn
  · by_cases hqInt : q.val ≠ 0 ∧ q.val ≠ diversityLength S (word S sort P o)
    · apply hFromInterior ⟨q, hqInt⟩
      rw [← at_interior S sort P o ⟨q, hqInt⟩]
      exact hqOn
    · have hpEnds : p = pathStart S (word S sort P o) ∨ p = pathFinish S (word S sort P o) := by
        by_cases hp0 : p.val = 0
        · exact Or.inl (Fin.ext hp0)
        · exact Or.inr (Fin.ext (by by_contra hEnd; exact hpInt ⟨hp0, hEnd⟩))
      have hqEnds : q = pathStart S (word S sort P o) ∨ q = pathFinish S (word S sort P o) := by
        by_cases hq0 : q.val = 0
        · exact Or.inl (Fin.ext hq0)
        · exact Or.inr (Fin.ext (by by_contra hEnd; exact hqInt ⟨hq0, hEnd⟩))
      rcases hpEnds with rfl | rfl <;> rcases hqEnds with rfl | rfl
      · exact False.elim (pathAdjacent_irrefl S _ _ hpq)
      · rw [at_start] at hpOn
        rw [at_finish S sort P o hPositive] at hqOn
        exact ⟨hpOn, hqOn⟩
      · rw [at_finish S sort P o hPositive] at hpOn
        rw [at_start] at hqOn
        exact ⟨hqOn, hpOn⟩
      · exact False.elim (pathAdjacent_irrefl S _ _ hpq)

/-- Initial labels are independent of the chosen witness occurrence,
including the merged direct-edge case. -/
theorem initial_label_of_path_witness
    (C : SimpleCycle (diagram S sort P hNonempty)) (k : Fin C.length)
    (o : Occurrence S sort P) (p q : PathPosition S (word S sort P o))
    (hpq : pathAdjacent S (word S sort P o) p q)
    (hv : C.vertices k = atPosition S sort P o p)
    (hw : C.vertices (cyclicNext C.length_pos k) = atPosition S sort P o q) :
    (initialCycle S sort P hNonempty C).label k = o.1 := by
  obtain ⟨p', q', hpq', hv', hw'⟩ := cycleOccurrence_spec S sort P hNonempty C k
  change (cycleOccurrence S sort P hNonempty C k).1 = o.1
  by_cases hSame : cycleOccurrence S sort P hNonempty C k = o
  · exact congrArg Sigma.fst hSame
  · exact (different_overlapping_edges_are_same_direct_edge S sort P
      (cycleOccurrence S sort P hNonempty C k) o hSame p' q' p q hpq' hpq
      (hv'.symm.trans hv) (hw'.symm.trans hw)).1

/-- Every used identifier has both literal marked endpoints on the cycle. -/
theorem used_label_endpoints
    (C : SimpleCycle (diagram S sort P hNonempty)) (e : Edge n)
    (he : CyclicSuppression.LabelOn (initialCycle S sort P hNonempty C) e) :
    CycleVertex C (mark S sort P (left e)) ∧ CycleVertex C (mark S sort P (right e)) := by
  obtain ⟨k, hk⟩ := he
  obtain ⟨p, q, hpq, hv, hw⟩ := cycleOccurrence_spec S sort P hNonempty C k
  have h := traversed_word_endpoints S sort P hNonempty C
    (cycleOccurrence S sort P hNonempty C k) p q hpq ⟨k, hv⟩ ⟨cyclicNext C.length_pos k, hw⟩
  change (cycleOccurrence S sort P hNonempty C k).1 = e at hk
  rwa [hk] at h

/-- Without three marked vertices, any used edge already lists ALL
marked vertices of the raw cycle. -/
theorem marked_support_of_no_three
    (C : SimpleCycle (diagram S sort P hNonempty)) (e : Edge n)
    (he : CyclicSuppression.LabelOn (initialCycle S sort P hNonempty C) e)
    (hNoThree : ¬ Nonempty (CyclicSuppression.ThreeMarked
      (initialCycle S sort P hNonempty C) (IsMarked S sort P))) :
    ∀ m, CycleVertex C (mark S sort P m) → m = left e ∨ m = right e := by
  classical
  have hEnds := used_label_endpoints S sort P hNonempty C e he
  intro m hm
  by_cases hmLeft : m = left e
  · exact Or.inl hmLeft
  · by_cases hmRight : m = right e
    · exact Or.inr hmRight
    · let a := mark S sort P (left e)
      let b := mark S sort P (right e)
      let c := mark S sort P m
      have hab : a ≠ b := by intro h; exact left_ne_right e (Sum.inl.inj h)
      have hac : a ≠ c := by intro h; exact hmLeft (Sum.inl.inj h).symm
      have hbc : b ≠ c := by intro h; exact hmRight (Sum.inl.inj h).symm
      let points : Fin 3 → Vertex S sort P := fun k => if k = 0 then a else if k = 1 then b else c
      have hInjective : Function.Injective points := by
        intro i j hij
        fin_cases i <;> fin_cases j <;> simp_all [points]
      let T : CyclicSuppression.ThreeMarked (initialCycle S sort P hNonempty C) (IsMarked S sort P) := {
        points := ⟨points, hInjective⟩
        marked := by
          intro k
          fin_cases k <;> simp [points, a, b, c, IsMarked, mark]
        onCycle := by
          intro k
          fin_cases k
          · obtain ⟨p, hp⟩ := hEnds.1
            refine ⟨p, ?_⟩
            change C.vertices p = points 0
            simpa [points, a] using hp
          · obtain ⟨p, hp⟩ := hEnds.2
            refine ⟨p, ?_⟩
            change C.vertices p = points 1
            simpa [points, b] using hp
          · obtain ⟨p, hp⟩ := hm
            refine ⟨p, ?_⟩
            change C.vertices p = points 2
            simpa [points, c] using hp
      }
      exact False.elim (hNoThree ⟨T⟩)

/-- In the two-mark case every traversed word has the SAME actual
underlying marked edge, even when direct paths have merged. -/
theorem labels_single_edge_of_no_three
    (C : SimpleCycle (diagram S sort P hNonempty)) (e : Edge n)
    (he : CyclicSuppression.LabelOn (initialCycle S sort P hNonempty C) e)
    (hNoThree : ¬ Nonempty (CyclicSuppression.ThreeMarked
      (initialCycle S sort P hNonempty C) (IsMarked S sort P))) :
    ∀ f, CyclicSuppression.LabelOn (initialCycle S sort P hNonempty C) f → f = e := by
  intro f hf
  have hEnds := used_label_endpoints S sort P hNonempty C f hf
  have hLeft := marked_support_of_no_three S sort P hNonempty C e he hNoThree (left f) hEnds.1
  have hRight := marked_support_of_no_three S sort P hNonempty C e he hNoThree (right f) hEnds.2
  rcases hLeft with hL | hL <;> rcases hRight with hR | hR
  · exact False.elim (left_ne_right f (hL.trans hR.symm))
  · exact edge_eq_of_unordered_endpoints f e (Or.inl ⟨hL, hR⟩)
  · exact edge_eq_of_unordered_endpoints f e (Or.inr ⟨hL, hR⟩)
  · exact False.elim (left_ne_right f (hL.trans hR.symm))

/-- Actual C26 marker dichotomy. The first case is one underlying edge;
the second is a literal simple cyclic embedding of distinct marks with
ALL original used edge identifiers retained. -/
theorem cycle_marked_cases (C : SimpleCycle (diagram S sort P hNonempty)) :
    (∃ e : Edge n,
      CyclicSuppression.LabelOn (initialCycle S sort P hNonempty C) e ∧
      (∀ m, CycleVertex C (mark S sort P m) → m = left e ∨ m = right e) ∧
      (∀ f, CyclicSuppression.LabelOn (initialCycle S sort P hNonempty C) f → f = e)) ∨
    Nonempty (MarkedProjection S sort P hNonempty C) := by
  classical
  by_cases hThree : Nonempty (CyclicSuppression.ThreeMarked
      (initialCycle S sort P hNonempty C) (IsMarked S sort P))
  · exact Or.inr (marked_projection_of_three S sort P hNonempty C hThree.some)
  · let k : Fin C.length := ⟨0, C.length_pos⟩
    let e := (initialCycle S sort P hNonempty C).label k
    have he : CyclicSuppression.LabelOn (initialCycle S sort P hNonempty C) e := ⟨k, rfl⟩
    exact Or.inl ⟨e, he,
      marked_support_of_no_three S sort P hNonempty C e he hThree,
      labels_single_edge_of_no_three S sort P hNonempty C e he hThree⟩

end CCO.RawExact.QuotientExpansion
