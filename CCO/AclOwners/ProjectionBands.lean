import CCO.AclOwners.ProjectionAlgebraicity

/-! Substitution of independently proved unary quotient formulas into
the general finite-kernel closure pullback. The source canonical-core
consumer supplies these formulas; this lemma does not assume a rooted,
master or EPPA provider. -/
universe v w t z
namespace CCO.AclOwners
open RealClosure.Bounds ParityHasse.Original FinitePackets.Normalization RawExact
variable {M : Type v} (S : AtomicSource.{0,v,w} Unit (fun _ => M))
variable {G : Type t} [Group G] [MulAction G M] (H : HomogeneousSource S G)

/-- Generic closure-band substitution. The hypotheses mention actual
quotient relations and every finite unary target, with no tuple fullness. -/
theorem closure_bands_of_quotient_unary [Countable M] [DecidableEq M]
    (cco : SemanticCCO.{0,v,0,w} S) {I : Type z} [Finite I]
    (C R : I → ColourEq S ()) (hle : ∀ i, C i ≤ R i)
    (B : ∀ _ : I, NonemptyExact S () ())
    (hB : ∀ i, evaluate S (B i).words = (C i).val.r)
    (hfib : ∀ x, Finite {y // jointKernel S C x y}) :
    letI : ∀ i, MulAction G (Quotient (C i).val) := fun i => originalQuotientAction S H (C i)
    letI : ∀ i, DecidableEq (Quotient (C i).val) := fun _ => Classical.decEq _
    (∀ i (U : Finset (Quotient (C i).val)),
      Acl G U = {q | ∃ u ∈ U, quotientColourEq S H (C i) (R i) (hle i) u q}) →
    ∀ A : Finset M, Acl G A = {x | ∀ i, ∃ a ∈ A, R i a x} := by
  classical
  letI : ∀ i, MulAction G (Quotient (C i).val) := fun i => originalQuotientAction S H (C i)
  letI : ∀ i, DecidableEq (Quotient (C i).val) := fun _ => Classical.decEq _
  intro hunary A
  rw [exact_closure_pullback S H cco C B hB hfib A]
  ext x
  constructor
  · intro hx i
    have hi := hx i
    rw [hunary i] at hi
    obtain ⟨q,hq,hqx⟩ := hi
    obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hq
    exact ⟨a,ha,(quotientColourEq_projection S H (C i) (R i) (hle i) a x).mp hqx⟩
  · intro hx i
    rw [hunary i]
    obtain ⟨a,ha,hax⟩ := hx i
    exact ⟨Quotient.mk'' a,Finset.mem_image.mpr ⟨a,ha,rfl⟩,
      (quotientColourEq_projection S H (C i) (R i) (hle i) a x).mpr hax⟩
end CCO.AclOwners
