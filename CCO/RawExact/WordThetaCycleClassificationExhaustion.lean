import CCO.RawExact.WordThetaCycleClassificationChoices

/-!
# Literal whole-cycle exhaustion by the two chosen private theta branches

Root edges are the two chosen incidences. Every other edge is on a private
word path, and any private interior on the cycle belongs to one of those
same two occurrences. This gives exact equality of the cycle's edge and
vertex supports with the union of TWO WHOLE original paths.
-/

universe u v w
namespace CCO.RawExact
variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)
variable {root : ι} {I : Type (max u v)} [Finite I] {sort : I → ι}
variable (menus : ∀ t : I, NonemptyExact S root (sort t)) (centres : ∀ t : I, X (sort t))
variable {E : PartialDiagram S (PrivateFanVertex S menus centres)} (C : SimpleCycle E)

/-- The orientation of a private word edge may be reversed without changing its occurrence. -/
theorem privateOccurrenceEdge_symm (o : WordOccurrence S menus) (v w : PrivateFanVertex S menus centres) :
    PrivateOccurrenceEdge S menus centres o v w ↔ PrivateOccurrenceEdge S menus centres o w v := by
  constructor <;> rintro ⟨p, q, hpq, hv, hw⟩
  · exact ⟨q, p, (pathAdjacent_symm S _ _ _).mp hpq, hw, hv⟩
  · exact ⟨q, p, (pathAdjacent_symm S _ _ _).mp hpq, hw, hv⟩

theorem ThetaCycleRootChoices.root_edge_covered (choice : ThetaCycleRootChoices S menus centres C)
    (v : PrivateFanVertex S menus centres) (hEdge : CycleEdge C (privateFanRoot S menus centres) v) :
    PrivateOccurrenceEdge S menus centres choice.left (privateFanRoot S menus centres) v ∨
      PrivateOccurrenceEdge S menus centres choice.right (privateFanRoot S menus centres) v := by
  rcases choice.exhaust v hEdge with hLeft | hRight
  · exact Or.inl ⟨pathStart S _, choice.firstLeft,
      (pathAdjacent_start_iff S _ _).mpr choice.firstLeft_val,
      (privateFanAt_start S menus centres choice.left).symm, hLeft⟩
  · exact Or.inr ⟨pathStart S _, choice.firstRight,
      (pathAdjacent_start_iff S _ _).mpr choice.firstRight_val,
      (privateFanAt_start S menus centres choice.right).symm, hRight⟩

/-- EVERY actual cycle edge belongs to one of the two selected whole branches. -/
theorem ThetaCycleRootChoices.cycle_edge_covered (choice : ThetaCycleRootChoices S menus centres C)
    (hCycleAdj : ∀ k, privateFanAdjacent S menus centres
      (C.vertices k) (C.vertices (cyclicNext C.length_pos k)))
    (hCentres : ∀ c d : DistinctCentres sort centres, c = d)
    (v w : PrivateFanVertex S menus centres) (hEdge : CycleEdge C v w) :
    PrivateOccurrenceEdge S menus centres choice.left v w ∨
      PrivateOccurrenceEdge S menus centres choice.right v w := by
  by_cases hv : v = privateFanRoot S menus centres
  · subst v
    exact ThetaCycleRootChoices.root_edge_covered S menus centres C choice w hEdge
  · by_cases hw : w = privateFanRoot S menus centres
    · subst w
      have hRev := (cycleEdge_symm C _ _).mp hEdge
      rcases ThetaCycleRootChoices.root_edge_covered S menus centres C choice v hRev with hLeft | hRight
      · exact Or.inl ((privateOccurrenceEdge_symm S menus centres _ _ _).mpr hLeft)
      · exact Or.inr ((privateOccurrenceEdge_symm S menus centres _ _ _).mpr hRight)
    · have hAdj := cycleEdge_adjacent C (privateFanAdjacent S menus centres)
        (fun v w h => (privateFanAdjacent_symm S menus centres v w).mp h) hCycleAdj hEdge
      rcases hAdj with hOld | hPath
      · obtain ⟨c, d, hcd, _, _⟩ := hOld
        exact False.elim (hcd (hCentres c d))
      · obtain ⟨o, p, q, hStep, rfl, rfl⟩ := hPath
        have hp0 : p.val ≠ 0 := by
          intro h
          have hp : p = pathStart S (occurrenceWord S menus o) := Fin.ext h
          rw [hp, privateFanAt_start S menus centres o] at hv
          exact hv rfl
        have hq0 : q.val ≠ 0 := by
          intro h
          have hq : q = pathStart S (occurrenceWord S menus o) := Fin.ext h
          rw [hq, privateFanAt_start S menus centres o] at hw
          exact hw rfl
        have hOccurrence : o = choice.left ∨ o = choice.right := by
          by_cases hpEnd : p.val = diversityLength S (occurrenceWord S menus o)
          · have hqEnd : q.val ≠ diversityLength S (occurrenceWord S menus o) := by
              rcases hStep with h | h <;> omega
            have hOn : CycleVertex C (privateFanInterior S menus centres o ⟨q, hq0, hqEnd⟩) := by
              rw [← privateFanAt_interior S menus centres o q hq0 hqEnd]
              exact (cycleEdge_vertices C hEdge).2
            exact ThetaCycleRootChoices.interior_occurrence S menus centres C choice hCycleAdj o ⟨q, hq0, hqEnd⟩ hOn
          · have hOn : CycleVertex C (privateFanInterior S menus centres o ⟨p, hp0, hpEnd⟩) := by
              rw [← privateFanAt_interior S menus centres o p hp0 hpEnd]
              exact (cycleEdge_vertices C hEdge).1
            exact ThetaCycleRootChoices.interior_occurrence S menus centres C choice hCycleAdj o ⟨p, hp0, hpEnd⟩ hOn
        rcases hOccurrence with hLeft | hRight
        · subst o
          exact Or.inl ⟨p, q, hStep, rfl, rfl⟩
        · subst o
          exact Or.inr ⟨p, q, hStep, rfl, rfl⟩

/-- Exact whole-cycle classification in the one-centre private fan: TWO DISTINCT
positive whole paths, with equality of BOTH literal vertex and traversed-edge supports. -/
theorem privateFan_one_centre_cycle_two_whole_paths
    (hCycleAdj : ∀ k, privateFanAdjacent S menus centres
      (C.vertices k) (C.vertices (cyclicNext C.length_pos k)))
    (hCentres : ∀ c d : DistinctCentres sort centres, c = d) :
    ∃ left right : WordOccurrence S menus,
      left ≠ right ∧
      0 < diversityLength S (occurrenceWord S menus left) ∧
      0 < diversityLength S (occurrenceWord S menus right) ∧
      (∀ v, CycleVertex C v ↔
        (∃ p, privateFanAtWordPosition S menus centres left p = v) ∨
        (∃ p, privateFanAtWordPosition S menus centres right p = v)) ∧
      (∀ v w, CycleEdge C v w ↔
        PrivateOccurrenceEdge S menus centres left v w ∨
        PrivateOccurrenceEdge S menus centres right v w) := by
  obtain ⟨choice⟩ := privateFan_one_centre_cycle_root_choices S menus centres C hCycleAdj hCentres
  have hLeft := privateFan_whole_path_on_cycle_of_root_edge S menus centres C hCycleAdj
    choice.left choice.firstLeft choice.firstLeft_val choice.left_edge
  have hRight := privateFan_whole_path_on_cycle_of_root_edge S menus centres C hCycleAdj
    choice.right choice.firstRight choice.firstRight_val choice.right_edge
  have hPosLeft : 0 < diversityLength S (occurrenceWord S menus choice.left) := by
    have h := choice.firstLeft.isLt
    have hval := choice.firstLeft_val
    omega
  have hPosRight : 0 < diversityLength S (occurrenceWord S menus choice.right) := by
    have h := choice.firstRight.isLt
    have hval := choice.firstRight_val
    omega
  have hCovered := ThetaCycleRootChoices.cycle_edge_covered S menus centres C choice hCycleAdj hCentres
  refine ⟨choice.left, choice.right, ThetaCycleRootChoices.occurrences_ne S menus centres C choice,
    hPosLeft, hPosRight, ?_, ?_⟩
  · intro v
    constructor
    · intro hOn
      obtain ⟨a, b, _, hA, _⟩ := cycle_two_distinct_neighbours C v hOn
      rcases hCovered v a hA with ⟨p, q, _, hv, _⟩ | ⟨p, q, _, hv, _⟩
      · exact Or.inl ⟨p, hv.symm⟩
      · exact Or.inr ⟨p, hv.symm⟩
    · rintro (⟨p, hp⟩ | ⟨p, hp⟩)
      · rw [← hp]
        exact hLeft.1 p
      · rw [← hp]
        exact hRight.1 p
  · intro v w
    constructor
    · exact hCovered v w
    · rintro (⟨p, q, hStep, rfl, rfl⟩ | ⟨p, q, hStep, rfl, rfl⟩)
      · exact hLeft.2 p q hStep
      · exact hRight.2 p q hStep

end CCO.RawExact
