import CCO.OwnerTransversal.SourceData

/-! The normalized MI source starts with its UNIQUE full invariant
direction.  Its exactness, residual equation, absolute closure and thin
packet group are outputs; neither EPPA nor a safe palette is used here. -/
universe v w t
namespace CCO.RelativeMI
noncomputable section
open ParityHasse.Original RealHull.Geometry RealClosure.Bounds
open FinitePackets.Geometry FinitePackets.Normalization AclOwners OwnerTransversal

variable {M : Type v} (S : AtomicSource.{0,v,w} Unit (fun _ => M))
variable {G : Type t} [Group G] [MulAction G M] (H : HomogeneousSource S G)
variable [Countable M] [DecidableEq M]

/-- C24: a complementary infinite core contains a full minimal infinite
direction. Uniqueness therefore rules out the nonresidual alternative. -/
theorem unique_direction_residual (cco : SemanticCCO.{0,v,0,w} S)
    (normalized : NoFiniteExactKernel S) (D : Direction S)
    (unique : ∀ D' : Direction S, D' = D) :
    correspondenceEq S H cco D.val (direction_exact S H cco D) = finitePacket S H := by
  have hne : D.val ≠ ⊥ := by
    intro he
    apply D.property.1
    simpa only [he] using finiteClasses_bot S
  rcases correspondence_gluing_dichotomy S H cco normalized D.val
      (direction_exact S H cco D) hne with h | ⟨C,hC,_,_,hDC,_,_⟩
  · exact h
  · obtain ⟨D',hle⟩ := exists_direction_le S hC
    rw [unique D'] at hle
    have hbot : D.val ≤ ⊥ := by
      rw [← hDC]
      exact le_inf le_rfl hle
    exact False.elim (hne (le_antisymm hbot bot_le))

/-- The actual residual source required by the accepted full-owner
construction is derived from the principal normalized hypotheses. -/
def normalizedResidual (cco : SemanticCCO.{0,v,0,w} S)
    (normalized : NoFiniteExactKernel S) (D : Direction S)
    (unique : ∀ D' : Direction S, D' = D) : ResidualData S H where
  cco := cco
  normalized := normalized
  E := D.val
  exact := direction_exact S H cco D
  infinite := D.property.1
  minimalExact := by
    intro K _ hKD hK
    by_contra hDK
    exact hK (D.property.2 K (lt_of_le_of_ne hKD (fun he => hDK he.ge)))
  residual := unique_direction_residual S H cco normalized D unique

@[simp] theorem normalizedResidual_E (cco : SemanticCCO.{0,v,0,w} S)
    (normalized : NoFiniteExactKernel S) (D : Direction S)
    (unique : ∀ D' : Direction S, D' = D) :
    (normalizedResidual S H cco normalized D unique).E = D.val := rfl

/-- This is ABSOLUTE real closure in the original source, including the
empty real base; closure only in a later named-owner reduct is insufficient. -/
theorem normalized_absolute_acl [Infinite M] (cco : SemanticCCO.{0,v,0,w} S)
    (normalized : NoFiniteExactKernel S) (D : Direction S)
    (unique : ∀ D' : Direction S, D' = D) (A : Finset M) :
    FullRealAcl S A = packetClosure S H A :=
  (normalizedResidual S H cco normalized D unique).full_real_acl S H A

/-- Thinness is derived without asserting that the finite bottom is exact. -/
theorem normalized_packet_thin (cco : SemanticCCO.{0,v,0,w} S)
    (normalized : NoFiniteExactKernel S) (D : Direction S)
    (unique : ∀ D' : Direction S, D' = D) : ThinBottom S (finitePacket S H) :=
  (normalizedResidual S H cco normalized D unique).packet_thin S H

end
end CCO.RelativeMI
