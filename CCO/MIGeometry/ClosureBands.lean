import CCO.MIGeometry.UnaryFactors
import CCO.AclOwners.ProjectionBands
import CCO.AclOwners.HarmlessFullAut

/-! The genuinely general finite-common-kernel closure identity is
instantiated with maximal cores. No safe palette or tuple-surjectivity
premise occurs in either closure equation. -/
universe v w t
namespace CCO.MIGeometry
open ParityHasse.Original RealClosure.Bounds
open FinitePackets.Geometry FinitePackets.Normalization RawExact AclOwners
variable {M : Type v} (S : AtomicSource.{0,v,w} Unit (fun _ => M))
variable {G : Type t} [Group G] [MulAction G M] (H : HomogeneousSource S G)
variable [Countable M] [DecidableEq M] (cco : SemanticCCO.{0,v,0,w} S)

theorem hat_joint_finite (normalized : NoFiniteExactKernel S) (x : M) :
    Finite {y // jointKernel S (hat S H cco) x y} := by
  letI : Subsingleton {y // jointKernel S (hat S H cco) x y} := ⟨by
    intro a b
    apply Subtype.ext
    have ha : (allHat S H cco) x a.val := a.property
    have hb : (allHat S H cco) x b.val := b.property
    rw [allHat_eq_bot S H cco normalized] at ha hb
    exact ha.symm.trans hb⟩
  infer_instance

/-- Actual quotient acl pullbacks, before substituting the unary packets. -/
theorem hat_closure_pullback (normalized : NoFiniteExactKernel S) (A : Finset M) :
    letI : ∀ D : Direction S, MulAction G (Quotient (hat S H cco D).val) :=
      fun D => originalQuotientAction S H (hat S H cco D)
    letI : ∀ D : Direction S, DecidableEq (Quotient (hat S H cco D).val) :=
      fun _ => Classical.decEq _
    Acl G A = {x | ∀ D : Direction S,
      (Quotient.mk'' x : Quotient (hat S H cco D).val) ∈
        Acl G (A.image (Quotient.mk'' : M → Quotient (hat S H cco D).val))} :=
  exact_closure_pullback S H cco (hat S H cco) (hatPresentation S H cco)
    (hatPresentation_represents S H cco) (hat_joint_finite S H cco normalized) A

/-- Every finite real input, including empty, is reconstructed from the
FULL original correspondence bands of ALL maximal normalized factors. -/
theorem maximal_closure_bands (normalized : NoFiniteExactKernel S) (A : Finset M) :
    Acl G A = {x | ∀ D : Direction S, ∃ a ∈ A, oldCorrespondence S H cco D a x} := by
  classical
  apply closure_bands_of_quotient_unary S H cco (hat S H cco) (oldCorrespondence S H cco)
    (hat_le_correspondence S H cco) (hatPresentation S H cco)
    (hatPresentation_represents S H cco) (hat_joint_finite S H cco normalized)
  intro D U
  ext x
  exact hat_quotient_acl S H cco normalized D U x

theorem maximal_full_closure_bands (normalized : NoFiniteExactKernel S) (A : Finset M) :
    FullRealAcl S A = {x | ∀ D : Direction S, ∃ a ∈ A, oldCorrespondence S H cco D a x} := by
  rw [fullRealAcl_eq S H]
  exact maximal_closure_bands S H cco normalized A

end CCO.MIGeometry
