import CCO.MIGeometry.FactorSafety
import CCO.Owners.Master.RelativeExact

/-! The actual maximal factor and owner kernels used by the rank step.
The index is the exhaustive original set of minimal infinite directions.
No recursively supplied factor witness or current-rank master is used. -/

universe v w t
namespace CCO.RankInduction.Factors
noncomputable section
open RawExact ExactCRT ParityHasse.Original AclOwners MIGeometry
open FinitePackets.Normalization RealClosure.Bounds

variable {M : Type v} (S : AtomicSource.{0,v,w} Unit (fun _ => M))
variable {G : Type t} [Group G] [MulAction G M] (H : HomogeneousSource S G)
variable [Countable M] [DecidableEq M] (cco : SemanticCCO.{0,v,0,w} S)

abbrev Core (D : Direction S) := hatExact S H cco D
abbrev Owner (normalized : NoFiniteExactKernel S) (D : Direction S) :=
  ownerExact S H cco normalized D
abbrev Joint (normalized : NoFiniteExactKernel S) := jointOwnerExact S H cco normalized

/-- Every original factor kernel lies below its entire coarse owner cut. -/
theorem core_le_owner (normalized : NoFiniteExactKernel S) (D : Direction S) :
    Core S H cco D ≤ Owner S H cco normalized D := by
  change hat S H cco D ≤ exactColour S H cco (ownerExact S H cco normalized D)
  rw [ownerExact_pairwiseMeet S H cco normalized D]
  intro x y hxy E
  letI := ColourEq.lattice S H (i := ())
  exact (show hat S H cco D ≤ ColourEq.join S H (hat S H cco D)
    (hat S H cco E.val) from le_sup_left) hxy

/-- The unique surviving direction lies below the same eligible coarse cut. -/
theorem direction_le_owner (normalized : NoFiniteExactKernel S) (D : Direction S) :
    D.val ≤ exactColour S H cco (Owner S H cco normalized D) := by
  rw [ownerExact_pairwiseMeet S H cco normalized D]
  intro x y hxy E
  letI := ColourEq.lattice S H (i := ())
  have he : D.val ≤ hat S H cco E.val :=
    direction_le_hat_other S H cco normalized E.val D E.property
  exact (show hat S H cco E.val ≤ ColourEq.join S H (hat S H cco D)
    (hat S H cco E.val) from le_sup_right) (he hxy)

/-- The actual joint-owner quotient maps to each actual coarse owner. -/
theorem joint_le_owner (normalized : NoFiniteExactKernel S) (D : Direction S) :
    Joint S H cco normalized ≤ Owner S H cco normalized D := by
  intro x y hxy
  have h : jointOwner S H cco normalized x y := hxy
  rw [← owners_meet_jointOwner S H cco normalized] at h
  exact h D

/-- All maximal factors together separate the original real points. -/
theorem cores_separate (normalized : NoFiniteExactKernel S) (x y : M)
    (hxy : ∀ D : Direction S, (Core S H cco D).val x y) : x = y := by
  have h : allHat S H cco x y := hxy
  rw [allHat_eq_bot S H cco normalized] at h
  exact h

/-- The literal family meet of owners is the strict joint-owner kernel. -/
theorem owners_meet (normalized : NoFiniteExactKernel S) (x y : M) :
    (∀ D : Direction S, (Owner S H cco normalized D).val x y) ↔
      (Joint S H cco normalized).val x y := by
  change (colourFamilyMeet S (fun D => exactColour S H cco
    (ownerExact S H cco normalized D))) x y ↔ jointOwner S H cco normalized x y
  rw [owners_meet_jointOwner S H cco normalized]

/-- JOG uses actual equivalence joins, with no owner-coordinate relaxation. -/
theorem join_gate (normalized : NoFiniteExactKernel S) (D E : Direction S)
    (hne : D ≠ E) :
    (Core S H cco D).val ⊔ (Core S H cco E).val =
      (Owner S H cco normalized D).val ⊔ (Owner S H cco normalized E).val :=
  (congrArg (fun Q : ExactL S H cco => Q.val)
    (ownerExact_JOG S H cco normalized D E hne)).symm

/-- Every minimal infinite direction is nonidentity, including Top. -/
theorem direction_ne_bot (D : Direction S) :
    (show ExactL S H cco from ⟨D.val.val, direction_exact S H cco D⟩) ≠ ⊥ := by
  intro he
  have hz : D.val = ⊥ := Subtype.ext
    (congrArg (fun Q : ExactL S H cco => Q.val) he)
  exact D.property.1 (hz ▸ finiteClasses_bot S)

/-- The actual kernel of the fine-owner quotient contains that direction. -/
def Fine (D : Direction S) : ExactL S H cco :=
  (show ExactL S H cco from ⟨D.val.val, direction_exact S H cco D⟩) ⊔ Core S H cco D

theorem fine_ne_bot (D : Direction S) : Fine S H cco D ≠ ⊥ := by
  intro he
  apply direction_ne_bot S H cco D
  exact le_antisymm (he ▸ (show
    (⟨D.val.val, direction_exact S H cco D⟩ : ExactL S H cco) ≤ Fine S H cco D
    from le_sup_left)) bot_le

/-- This is the STRICT original source used by the lower U hypothesis. -/
theorem joint_ne_bot (normalized : NoFiniteExactKernel S)
    (many : 2 ≤ directionCount S) : Joint S H cco normalized ≠ ⊥ := by
  letI := nonempty_directions_of_two S many
  intro he
  exact jointOwner_ne_bot S H cco normalized
    (Subtype.ext (congrArg (fun Q : ExactL S H cco => Q.val) he))

end
end CCO.RankInduction.Factors
