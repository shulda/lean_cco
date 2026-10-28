import CCO.RawExact.WordThetaCycleClassificationBranches

/-!
# A genuine one-centre theta cycle selects exactly two root branch germs

Both germs come from literal original word occurrences. Their first neighbours
are different, so the occurrences differ; duplicated direct edges cannot be
selected as two different simple-cycle incidences. All chosen branches are
positive, and both are present as WHOLE private paths on the cycle.
-/

universe u v w
namespace CCO.RawExact
variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)
variable {root : ι} {I : Type (max u v)} [Finite I] {sort : I → ι}
variable (menus : ∀ t : I, NonemptyExact S root (sort t)) (centres : ∀ t : I, X (sort t))
variable {E : PartialDiagram S (PrivateFanVertex S menus centres)} (C : SimpleCycle E)

structure ThetaCycleRootChoices where
  left : WordOccurrence S menus
  right : WordOccurrence S menus
  firstLeft : PathPosition S (occurrenceWord S menus left)
  firstRight : PathPosition S (occurrenceWord S menus right)
  firstLeft_val : firstLeft.val = 1
  firstRight_val : firstRight.val = 1
  neighbours_ne : privateFanAtWordPosition S menus centres left firstLeft ≠
    privateFanAtWordPosition S menus centres right firstRight
  left_edge : CycleEdge C (privateFanRoot S menus centres)
    (privateFanAtWordPosition S menus centres left firstLeft)
  right_edge : CycleEdge C (privateFanRoot S menus centres)
    (privateFanAtWordPosition S menus centres right firstRight)
  exhaust : ∀ v, CycleEdge C (privateFanRoot S menus centres) v →
    v = privateFanAtWordPosition S menus centres left firstLeft ∨
    v = privateFanAtWordPosition S menus centres right firstRight

theorem ThetaCycleRootChoices.occurrences_ne (choice : ThetaCycleRootChoices S menus centres C) :
    choice.left ≠ choice.right := by
  rcases choice with ⟨left, right, pl, pr, hpl, hpr, hne, hleft, hright, hexhaust⟩
  intro h
  change left = right at h
  subst right
  apply hne
  exact congrArg (privateFanAtWordPosition S menus centres left) (Fin.ext (hpl.trans hpr.symm))

theorem privateFan_one_centre_cycle_root_choices
    (hCycleAdj : ∀ k, privateFanAdjacent S menus centres
      (C.vertices k) (C.vertices (cyclicNext C.length_pos k)))
    (hCentres : ∀ c d : DistinctCentres sort centres, c = d) :
    Nonempty (ThetaCycleRootChoices S menus centres C) := by
  obtain ⟨o, p, hOn⟩ := privateFan_one_centre_cycle_has_interior S menus centres C hCentres
  have hWhole := privateFan_whole_path_on_cycle_of_interior S menus centres C hCycleAdj o p hOn
  have hRoot : CycleVertex C (privateFanRoot S menus centres) := by
    have h := hWhole.1 (pathStart S (occurrenceWord S menus o))
    rwa [privateFanAt_start S menus centres o] at h
  obtain ⟨a, b, hab, hA, hB, hExhaust⟩ := privateFan_cycle_root_neighbours S menus centres C hRoot
  have hAdjA := cycleEdge_adjacent C (privateFanAdjacent S menus centres)
    (fun v w h => (privateFanAdjacent_symm S menus centres v w).mp h) hCycleAdj hA
  have hAdjB := cycleEdge_adjacent C (privateFanAdjacent S menus centres)
    (fun v w h => (privateFanAdjacent_symm S menus centres v w).mp h) hCycleAdj hB
  obtain ⟨left, pl, hpl, ha⟩ := privateFan_root_edges_are_first_steps S menus centres a hAdjA
  obtain ⟨right, pr, hpr, hb⟩ := privateFan_root_edges_are_first_steps S menus centres b hAdjB
  subst a
  subst b
  exact ⟨⟨left, right, pl, pr, hpl, hpr, hab, hA, hB, hExhaust⟩⟩

/-- Every private occurrence met by the cycle is one of its two selected root branches. -/
theorem ThetaCycleRootChoices.interior_occurrence
    (choice : ThetaCycleRootChoices S menus centres C)
    (hCycleAdj : ∀ k, privateFanAdjacent S menus centres
      (C.vertices k) (C.vertices (cyclicNext C.length_pos k)))
    (o : WordOccurrence S menus) (p : PrivateInteriorPosition S menus o)
    (hOn : CycleVertex C (privateFanInterior S menus centres o p)) :
    o = choice.left ∨ o = choice.right := by
  have hpBound := p.1.isLt
  have hp0 := p.property.1
  have hpEnd := p.property.2
  have hLen : 1 < diversityLength S (occurrenceWord S menus o) := by omega
  let first : PathPosition S (occurrenceWord S menus o) := ⟨1, by omega⟩
  have hfirst0 : first.val ≠ 0 := by dsimp [first]; omega
  have hfirstEnd : first.val ≠ diversityLength S (occurrenceWord S menus o) := by dsimp [first]; omega
  have hWhole := privateFan_whole_path_on_cycle_of_interior S menus centres C hCycleAdj o p hOn
  have hFirstEdge : CycleEdge C (privateFanRoot S menus centres) (privateFanAtWordPosition S menus centres o first) := by
    have h := hWhole.2 (pathStart S (occurrenceWord S menus o)) first (Or.inl rfl)
    rwa [privateFanAt_start S menus centres o] at h
  rcases choice.exhaust _ hFirstEdge with hLeft | hRight
  · left
    have hOccurrence := privateFanAt_interior_occurrence S menus centres o
      ⟨first, hfirst0, hfirstEnd⟩ choice.left choice.firstLeft
      (hLeft.symm.trans (privateFanAt_interior S menus centres o first hfirst0 hfirstEnd))
    exact hOccurrence.symm
  · right
    have hOccurrence := privateFanAt_interior_occurrence S menus centres o
      ⟨first, hfirst0, hfirstEnd⟩ choice.right choice.firstRight
      (hRight.symm.trans (privateFanAt_interior S menus centres o first hfirst0 hfirstEnd))
    exact hOccurrence.symm

end CCO.RawExact
