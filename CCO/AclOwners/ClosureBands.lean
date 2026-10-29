import CCO.AclOwners.CoordinateSource
import CCO.AclOwners.ProjectionBands
import CCO.AclOwners.HarmlessFullAut

/-! C33: the actual original-core closure bands. The complete original
minimal-direction list supplies an IDENTITY common kernel; every unary
quotient formula is instantiated from the true canonical quotient source.
No safe palette, rooted construction, master witness or EPPA is an input. -/

universe v w t
namespace CCO.AclOwners
open RealClosure.Bounds ParityHasse.Original FinitePackets.Normalization
open FinitePackets.Geometry RawExact
variable {M : Type v} (S : AtomicSource.{0,v,w} Unit (fun _ => M))
variable {G : Type t} [Group G] [MulAction G M] (H : HomogeneousSource S G)
variable [Countable M] [DecidableEq M] (cco : SemanticCCO.{0,v,0,w} S)

/-- Every joint fibre of ALL original core coordinates is a genuine
singleton. No compatible-tuple surjectivity is needed for this fact. -/
theorem oldCore_joint_finite (normalized : NoFiniteExactKernel S) (x : M) :
    Finite {y // jointKernel S (oldCore S H cco) x y} := by
  letI : Subsingleton {y // jointKernel S (oldCore S H cco) x y} := ⟨by
    intro a b
    apply Subtype.ext
    have ha : x = a.val := (all_oldCore_iff_eq S H cco normalized x a.val).mp a.property
    have hb : x = b.val := (all_oldCore_iff_eq S H cco normalized x b.val).mp b.property
    exact ha.symm.trans hb⟩
  infer_instance

/-- The source closure-band identity, with actual full original
correspondences and the ENTIRE original minimal-direction index type. -/
theorem canonical_closure_bands (normalized : NoFiniteExactKernel S) (A : Finset M) :
    Acl G A = {x | ∀ D : Direction S, ∃ a ∈ A, oldCorrespondence S H cco D a x} := by
  classical
  apply closure_bands_of_quotient_unary S H cco
    (oldCore S H cco) (oldCorrespondence S H cco) (fun _ => core_le S _)
    (fun D => coreExact S H (oldCorrespondence S H cco D))
    (fun D => coreExact_represents S H (oldCorrespondence S H cco D))
    (oldCore_joint_finite S H cco normalized)
  intro D U
  ext x
  exact oldCore_quotient_acl S H cco normalized D U x

/-- The same source equation in literal FULL original automorphism
stabilizer semantics, rather than a chosen witness subgroup. -/
theorem canonical_full_closure_bands (normalized : NoFiniteExactKernel S) (A : Finset M) :
    FullRealAcl S A = {x | ∀ D : Direction S, ∃ a ∈ A, oldCorrespondence S H cco D a x} := by
  rw [fullRealAcl_eq S H]
  exact canonical_closure_bands S H cco normalized A

end CCO.AclOwners
