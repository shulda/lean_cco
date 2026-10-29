import CCO.Owners.Master.Assembly

/-! An empty Birkhoff poset means the actual source itself is a
singleton. The initial decorated system is already the final one and
uses ZERO ordinary EPPA provider calls. -/

universe v w t z
namespace CCO.Owners.Master
noncomputable section
open RawExact ExactCRT

variable {A : Type v} (S : AtomicSource.{0,v,w} Unit (fun _ => A))
variable {G : Type t} [Group G] [MulAction G A]
variable (H : HomogeneousSource S G) (cco : SemanticCCO.{0,v,v,w} S)
variable [IsEmpty (Position S H cco)]

theorem empty_positions_univ : (Finset.univ : Finset (Position S H cco)) = ∅ := by
  ext p
  exact isEmptyElim p

include S H cco in
theorem empty_positions_source_subsingleton : Subsingleton A := by
  have h : (⊥ : Exact S H cco) = ⊤ := by
    rw [← coordinateKernel_univ S H cco,empty_positions_univ S H cco,
      coordinateKernel_empty S H cco]
  constructor
  intro a b
  have hab : (⊥ : Exact S H cco).val a b := by rw [h]; trivial
  exact hab

theorem empty_positions_zero_schedule :
    ValidAfter (∅ : Finset (Position S H cco)) [] := by
  change ∅ = Finset.univ
  exact (empty_positions_univ S H cco).symm

/-- The actual singleton-source boundary needs no ordinary EPPA input. -/
theorem empty_positions_actual_master [Countable A] (T : Set A) :
    Nonempty (ActualMaster.{v,w,t,z} S H cco T) := by
  have B : SourceStage.{v,w,t,z} S H cco T Finset.univ := by
    rw [empty_positions_univ S H cco]
    exact initialSourceStage S H cco T
  exact ⟨B.actualMaster S H cco⟩

end
end CCO.Owners.Master
