import CCO.PairSafeSplit.Terminal.Current

/-! B047 C41/C42/C44--C46: all facts below concern the SAME actual B044
marked limit and its old-reduct identification. They are not facts about
arbitrary seed markings or childwise automorphisms. -/

universe u v w t
namespace CCO.PairSafeSplit.Terminal.Readout
open APCharacter APCharacter.Towers APCharacter.SourceAge
open RigidGroupoid.Geometry RigidGroupoid.Phase
open SourceAge.UnarySource
noncomputable section

variable (B : APCharacter.Towers.CurrentSource.{u,v,w,t})
variable {r : B.Sorts} {K : Kernel B.source r}
variable (P : SourcePhase B.source B.homogeneous
  (exactCalculus_of_homogeneous_CCO B.source B.homogeneous B.cco) K)

abbrev identification := SingleStep.identification B P
abbrev marking := UnarySource.mark (identification B P)

/-- Every actual rigid arrow has its original character equation in the
marking pulled back from the genuinely homogeneous marked limit. -/
theorem marking_arrow {b c : Reached B.source K}
    (R : Arrow B.source
      (Reached.kernel B.homogeneous
        (exactCalculus_of_homogeneous_CCO B.source B.homogeneous B.cco) b)
      (Reached.kernel B.homogeneous
        (exactCalculus_of_homogeneous_CCO B.source B.homogeneous B.cco) c))
    (x : B.Point b.val) (y : B.Point c.val) (hR : R.rel x y) :
    letI := Reached.groupoid B.homogeneous
      (exactCalculus_of_homogeneous_CCO B.source B.homogeneous B.cco) (A := K)
    marking B P ⟨c.val,y⟩ = marking B P ⟨b.val,x⟩ + P.character.value R := by
  letI := Reached.groupoid B.homogeneous
    (exactCalculus_of_homogeneous_CCO B.source B.homogeneous B.cco) (A := K)
  exact ((UnarySource.global_marking (identification B P)).2
    (⟨b.val,x⟩ : Sigma B.Point) (⟨c.val,y⟩ : Sigma B.Point)).2.2
      x y rfl b.property c.property R hR

theorem transported_odd_orientation (b : Reached B.source K)
    (x y : B.Point b.val) (h : (P.atSort b).rel x y) :
    marking B P ⟨b.val,y⟩ = marking B P ⟨b.val,x⟩ + 1 := by
  have he := marking_arrow B P (P.atSort b) x y h
  rw [P.atSort_detects] at he
  exact he

/-- Whole gate classes, including their logical diagonal, have one bit. -/
theorem gate_constant (b : Reached B.source K) (x y : B.Point b.val)
    (h : (Reached.kernel B.homogeneous
      (exactCalculus_of_homogeneous_CCO B.source B.homogeneous B.cco) b).setoid x y) :
    marking B P ⟨b.val,y⟩ = marking B P ⟨b.val,x⟩ := by
  letI := Reached.groupoid B.homogeneous
    (exactCalculus_of_homogeneous_CCO B.source B.homogeneous B.cco) (A := K)
  have he := marking_arrow B P (Arrow.id _) x y h
  have hz : P.character.value (Arrow.id (Reached.kernel B.homogeneous
      (exactCalculus_of_homogeneous_CCO B.source B.homogeneous B.cco) b)) = 0 :=
    P.character.map_id b
  rw [hz,add_zero] at he
  exact he

/-- Exactly two valid and ACTUALLY inhabited child sorts occur at every
active parent. No colour table with an empty syntactic child is counted. -/
theorem active_children_card (b : Reached B.source K) :
    Fintype.card (β (identification B P) b.val) = 2 :=
  CharacterRank.active_card P B.cco (identification B P)
    ((CharacterRank.mem_active P b.val).mpr b.property)

theorem active_child_nonempty (b : Reached B.source K) (ε : Bit) :
    Nonempty (Rank.Point (β (identification B P)) (tag (identification B P))
      ⟨b.val,⟨ε,fun hn => False.elim (hn b.property)⟩⟩) :=
  UnarySource.inhabited (identification B P) _

theorem inactive_children_card (i : B.Sorts) (hi : ¬Nonempty (Bridge B.source K i)) :
    Fintype.card (β (identification B P) i) = 1 :=
  CharacterRank.inactive_card P B.cco (identification B P)
    (fun h => hi ((CharacterRank.mem_active P i).mp h))

/-- Every occurring child atom is ONE full whole-expanded pair orbital. -/
theorem whole_expanded_orbitals
    {c d : Rank.Child (β (identification B P))}
    (a : (UnarySource.source (identification B P)).Atom c d) :
    ∃ x : Rank.Point (β (identification B P)) (tag (identification B P)) c,
      ∃ y : Rank.Point (β (identification B P)) (tag (identification B P)) d,
        (UnarySource.source (identification B P)).atomRel a x y ∧
        (UnarySource.source (identification B P)).atomRel a =
          GroupActions.orbital (G := FullGroup (identification B P)) x y :=
  (UnarySource.source (identification B P)).diversity_atom_is_orbital_of_homogeneous
    (UnarySource.homogeneous (identification B P)) a

/-- One actual realized original diversity colour is missing inside BOTH
children of every active parent. Remaining names cannot split into orbits. -/
theorem lost_original_colour (b : Reached B.source K) :
    ∃ a : B.source.Atom b.val b.val,
      ∀ ε : β (identification B P) b.val,
        ¬Rank.Occurs B.source (β (identification B P)) (tag (identification B P))
          ⟨b.val,ε⟩ ⟨b.val,ε⟩ a :=
  CharacterRank.lost_colour P B.cco (identification B P)
    ((CharacterRank.mem_active P b.val).mpr b.property)

/-- The numerical drop is ACTUALLY discharged from the exact identified
whole marked source; no rank or lost-colour callback is an input. -/
theorem actual_potential_drop :
    (SingleStep.successor B P).potential < B.potential :=
  SingleStep.potential_decreases B P

end
end CCO.PairSafeSplit.Terminal.Readout
