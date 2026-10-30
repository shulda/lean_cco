import CCO.FullPhaseLift.Tower.Selected

/-! Original Y/O orientation for the ACTUAL FULL successor mark. This
mark comes from the FULL Fraisse limit and its FULL old-reduct isomorphism,
not from an unrelated preselected global marking on the binary reduct. -/
universe u v w t m
namespace CCO.FullPhaseLift.Tower.Readout
open APCharacter RigidGroupoid.Geometry
noncomputable section
variable {ι : Type u} {X : ι → Type v} {S : AtomicSource.{u,v,w} ι X}
variable {G : Type t} [Group G] [∀ i, MulAction G (X i)]
variable {H : HomogeneousSource S G} {C : ExactCalculus S} {r : ι} {K : Kernel S r}
variable (P : SourcePhase S H C K) (mark : Sigma X → Bit) (hm : P.masks.GlobalMarking mark)

include hm in
theorem legal_marking_arrow {b c : Reached S K}
    (R : Arrow S (Reached.kernel H C b) (Reached.kernel H C c))
    (x : X b.val) (y : X c.val) (hR : R.rel x y) :
    letI := Reached.groupoid H C (A := K)
    mark ⟨c.val,y⟩ = mark ⟨b.val,x⟩ + P.character.value R := by
  letI := Reached.groupoid H C (A := K)
  exact (hm.2 (⟨b.val,x⟩ : Sigma X) (⟨c.val,y⟩ : Sigma X)).2.2
    x y rfl b.property c.property R hR

include hm in
theorem legal_marking_gate (b : Reached S K) (x y : X b.val)
    (h : (Reached.kernel H C b).rel x y) : mark ⟨b.val,y⟩ = mark ⟨b.val,x⟩ := by
  letI := Reached.groupoid H C (A := K)
  have he := legal_marking_arrow P mark hm (Arrow.id _) x y h
  have hz : P.character.value (Arrow.id (Reached.kernel H C b)) = 0 := P.character.map_id b
  rw [hz,add_zero] at he
  exact he

end
end CCO.FullPhaseLift.Tower.Readout

namespace CCO.FullPhaseLift.Tower.SelectedStep
open APCharacter RigidGroupoid.Geometry
noncomputable section
variable {M : Type m} [Countable M] {A B : CurrentSource M} (s : SelectedStep A B)

abbrev fullMark : Sigma A.pair.base.Point → Bit :=
  SingleStep.mark A s.phase ∘ (Canonical.pack A.table).symm

/-- Every ORIGINAL selected even pair has equal actual FULL-source bits. -/
theorem original_even (x y : A.pair.base.Point s.sort)
    (h : ParityHasse.Original.evenColourEq A.pair.base.source A.pair.base.homogeneous s.atom x y) :
    s.fullMark ⟨s.sort,y⟩ = s.fullMark ⟨s.sort,x⟩ := by
  apply Readout.legal_marking_gate s.phase s.fullMark (SingleStep.global_legal A s.phase)
    (Reached.root s.parity.kernel) x y
  change (Reached.kernel A.pair.base.homogeneous
    (exactCalculus_of_homogeneous_CCO A.pair.base.source A.pair.base.homogeneous A.pair.base.cco)
      (Reached.root s.parity.kernel)).rel x y
  rw [Reached.root_kernel]
  exact s.parity.original_even_le_kernel x y h

/-- Every ORIGINAL O=U\Y pair has opposite actual FULL-source bits. -/
theorem original_odd (x y : A.pair.base.Point s.sort)
    (h : ParityHasse.Relative.odd
      (ParityHasse.Original.evenColourEq A.pair.base.source A.pair.base.homogeneous s.atom).val
      (ParityHasse.Original.connectivityColourEq A.pair.base.source A.pair.base.homogeneous s.atom).val x y) :
    s.fullMark ⟨s.sort,y⟩ = s.fullMark ⟨s.sort,x⟩ + 1 := by
  have he := Readout.legal_marking_arrow s.phase s.fullMark (SingleStep.global_legal A s.phase)
    (b := Reached.root s.parity.kernel) (c := Reached.root s.parity.kernel)
    s.phase.odd x y (s.parity.original_odd_le_phase A.pair.base.cco x y h)
  rw [s.phase.detects] at he
  exact he

theorem original_odd_walk (x y : A.pair.base.Point s.sort)
    (h : ParityHasse.Original.OddWalk (A.pair.base.source.atomRel s.atom) x y) :
    s.fullMark ⟨s.sort,y⟩ = s.fullMark ⟨s.sort,x⟩ + 1 :=
  s.original_odd x y ((s.parity.odd_sheet x y).mp h)

end
end CCO.FullPhaseLift.Tower.SelectedStep
