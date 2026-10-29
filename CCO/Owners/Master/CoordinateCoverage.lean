import CCO.Owners.Master.ExactCoordinates
import CCO.Owners.Master.UpsetSchedule

/-! Every actual exact equivalence occurs among the upset coordinates.
The inverse uses all nonzero join-irreducibles rather than a selected
subfamily, and reverses inclusions exactly. -/

universe v w t z
namespace CCO.Owners.Master
noncomputable section
open RawExact ExactCRT
variable {A : Type v} (S : AtomicSource.{0,v,w} Unit (fun _ => A))
variable {G : Type t} [Group G] [MulAction G A]
variable (H : HomogeneousSource S G) (cco : SemanticCCO.{0,v,v,w} S)

def exactPositions (E : Exact S H cco) : Finset (Position S H cco) := by
  classical
  exact Finset.univ.filter (fun p => ¬p.val ≤ E)

@[simp] theorem mem_exactPositions (E : Exact S H cco) (p : Position S H cco) :
    p ∈ exactPositions S H cco E ↔ ¬p.val ≤ E := by
  classical
  simp [exactPositions]

theorem exactPositions_upset (E : Exact S H cco) : IsUpset (exactPositions S H cco E) := by
  intro p q hp hpq
  apply (mem_exactPositions S H cco E q).mpr
  intro hq
  exact (mem_exactPositions S H cco E p).mp hp ((show p.val ≤ q.val from hpq).trans hq)

@[simp] theorem coordinateKernel_exactPositions (E : Exact S H cco) :
    coordinateKernel S H cco (exactPositions S H cco E) = E := by
  classical
  apply (exactBirkhoff S H cco ()).injective
  ext p
  change p.val ≤ coordinateKernel S H cco (exactPositions S H cco E) ↔ p.val ≤ E
  rw [position_le_coordinateKernel S H cco _ (exactPositions_upset S H cco E)]
  simp

@[simp] theorem exactPositions_coordinateKernel (V : Finset (Position S H cco))
    (hV : IsUpset V) : exactPositions S H cco (coordinateKernel S H cco V) = V := by
  classical
  ext p
  rw [mem_exactPositions,position_le_coordinateKernel S H cco V hV]
  simp

theorem exactPositions_antitone {E F : Exact S H cco} (hEF : E ≤ F) :
    exactPositions S H cco F ⊆ exactPositions S H cco E := by
  intro p hp
  apply (mem_exactPositions S H cco E p).mpr
  intro he
  exact (mem_exactPositions S H cco F p).mp hp (he.trans hEF)

theorem exactPositions_subset_iff (E F : Exact S H cco) :
    exactPositions S H cco F ⊆ exactPositions S H cco E ↔ E ≤ F := by
  constructor
  · intro h
    simpa only [coordinateKernel_exactPositions] using coordinateKernel_antitone S H cco h
  · exact exactPositions_antitone S H cco

end
end CCO.Owners.Master
