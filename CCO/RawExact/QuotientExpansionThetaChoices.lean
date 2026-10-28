import CCO.RawExact.QuotientExpansionThetaBranches

/-!
# The two literal original word occurrences selected by a two-mark cycle

Every private interior met by this same cycle belongs to one of these
occurrences, since its entire first edge must meet one of the two actual
cycle neighbours of the left mark. No abstract path decomposition is assumed.
-/

universe u v w
namespace CCO.RawExact.QuotientExpansion
variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)
variable {n : Nat} (sort : Fin n → ι) (P : Menus S sort)
variable (hNonempty : ∀ e, TRel.Nonempty (evaluate S (P e)))
variable (C : SimpleCycle (diagram S sort P hNonempty))

structure TwoMarkChoices (e : Edge n) where
  first : Occurrence S sort P
  second : Occurrence S sort P
  first_label : first.1 = e
  second_label : second.1 = e
  firstPosition : PathPosition S (word S sort P first)
  secondPosition : PathPosition S (word S sort P second)
  first_val : firstPosition.val = 1
  second_val : secondPosition.val = 1
  neighbours_ne : atPosition S sort P first firstPosition ≠ atPosition S sort P second secondPosition
  first_edge : CycleEdge C (mark S sort P (left e)) (atPosition S sort P first firstPosition)
  second_edge : CycleEdge C (mark S sort P (left e)) (atPosition S sort P second secondPosition)
  exhaust : ∀ v, CycleEdge C (mark S sort P (left e)) v →
    v = atPosition S sort P first firstPosition ∨ v = atPosition S sort P second secondPosition

theorem TwoMarkChoices.occurrences_ne {e : Edge n}
    (choice : TwoMarkChoices S sort P hNonempty C e) : choice.first ≠ choice.second := by
  rcases choice with ⟨first, second, hf, hs, p, q, hp, hq, hne, he1, he2, hex⟩
  intro h
  change first = second at h
  subst second
  apply hne
  exact congrArg (atPosition S sort P first) (Fin.ext (hp.trans hq.symm))

/-- Actual single-label support constructs two distinct branch germs. -/
theorem two_mark_choices (e : Edge n)
    (he : CyclicSuppression.LabelOn (initialCycle S sort P hNonempty C) e)
    (hAll : ∀ f, CyclicSuppression.LabelOn (initialCycle S sort P hNonempty C) f → f = e) :
    Nonempty (TwoMarkChoices S sort P hNonempty C e) := by
  have hOn := (used_label_endpoints S sort P hNonempty C e he).1
  obtain ⟨a, b, hab, hA, hB, hExhaust⟩ := cycle_mark_neighbours S sort P hNonempty C (left e) hOn
  obtain ⟨first, p, hpLabel, hp, ha⟩ := single_label_left_edge_first_step S sort P hNonempty C e hAll a hA
  obtain ⟨second, q, hqLabel, hq, hb⟩ := single_label_left_edge_first_step S sort P hNonempty C e hAll b hB
  subst a
  subst b
  exact ⟨⟨first, second, hpLabel, hqLabel, p, q, hp, hq, hab, hA, hB, hExhaust⟩⟩

/-- EVERY private occurrence touched in its interior is one of the two
actual choices, and not merely some word carrying their underlying label. -/
theorem TwoMarkChoices.interior_occurrence {e : Edge n}
    (choice : TwoMarkChoices S sort P hNonempty C e)
    (hAll : ∀ f, CyclicSuppression.LabelOn (initialCycle S sort P hNonempty C) f → f = e)
    (o : Occurrence S sort P) (p : Interior S sort P o)
    (hOn : CycleVertex C (interior S sort P o p)) :
    o = choice.first ∨ o = choice.second := by
  have hpBound := p.1.isLt
  have hp0 := p.property.1
  have hpEnd := p.property.2
  have hLen : 1 < diversityLength S (word S sort P o) := by omega
  let first : PathPosition S (word S sort P o) := ⟨1, by omega⟩
  have hfirst0 : first.val ≠ 0 := by dsimp [first]; omega
  have hfirstEnd : first.val ≠ diversityLength S (word S sort P o) := by dsimp [first]; omega
  have hWhole := whole_path_on_cycle_of_interior S sort P C (simpleCycle_adjacent S sort P hNonempty C) o p hOn
  have hStartEdge := hWhole.2 (pathStart S (word S sort P o)) first (Or.inl rfl)
  have hLabel := hAll o.1 (occurrence_label_on_cycle S sort P hNonempty C o
    (pathStart S (word S sort P o)) first (Or.inl rfl) hStartEdge)
  have hFirstEdge : CycleEdge C (mark S sort P (left e)) (atPosition S sort P o first) := by
    simpa only [at_start, hLabel] using hStartEdge
  rcases choice.exhaust _ hFirstEdge with hFirst | hSecond
  · left
    exact interior_occurrence_unique S sort P o choice.first ⟨first, hfirst0, hfirstEnd⟩
      choice.firstPosition ((at_interior S sort P o ⟨first, hfirst0, hfirstEnd⟩).symm.trans hFirst)
  · right
    exact interior_occurrence_unique S sort P o choice.second ⟨first, hfirst0, hfirstEnd⟩
      choice.secondPosition ((at_interior S sort P o ⟨first, hfirst0, hfirstEnd⟩).symm.trans hSecond)

/-- The two chosen first neighbours exhaust all traversed edges at the left mark. -/
theorem TwoMarkChoices.left_edge_covered {e : Edge n}
    (choice : TwoMarkChoices S sort P hNonempty C e)
    (v : Vertex S sort P) (hEdge : CycleEdge C (mark S sort P (left e)) v) :
    OccurrenceEdge S sort P choice.first (mark S sort P (left e)) v ∨
      OccurrenceEdge S sort P choice.second (mark S sort P (left e)) v := by
  rcases choice.exhaust v hEdge with hFirst | hSecond
  · exact Or.inl ⟨pathStart S _, choice.firstPosition,
      (pathAdjacent_start_iff S _ _).mpr choice.first_val,
      (by simp only [at_start, choice.first_label]), hFirst⟩
  · exact Or.inr ⟨pathStart S _, choice.secondPosition,
      (pathAdjacent_start_iff S _ _).mpr choice.second_val,
      (by simp only [at_start, choice.second_label]), hSecond⟩

end CCO.RawExact.QuotientExpansion
