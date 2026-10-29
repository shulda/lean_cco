import CCO.AclOwners.CorrespondenceGeometry
import CCO.AclOwners.HarmlessFullAut
import CCO.RealClosure.Bounds.Singleton
import CCO.FinitePackets.Normalization.TerminalThin
import CCO.FinitePackets.Normalization.ColourTransport
import CCO.FinitePackets.Normalization.SubgroupInterval

/-! The residual branch starts with minimality only among infinite EXACT
equivalences.  Full invariant-lattice minimality, the unique direction,
the represented positive word and harmlessness of all named owners are
outputs below.  No original-age SAP or EPPA is part of this datum. -/

universe v w t
namespace CCO.OwnerTransversal
noncomputable section
open ParityHasse.Original RealHull.Geometry RealClosure.Bounds
open FinitePackets.Geometry FinitePackets.Normalization AclOwners

variable {M : Type v} (S : AtomicSource.{0,v,w} Unit (fun _ => M))
variable {G : Type t} [Group G] [MulAction G M] (H : HomogeneousSource S G)
variable [Countable M] [DecidableEq M]

/-- The source-scoped hypotheses A01/A05.  In particular `minimalExact`
does not quantify over unrepresented full invariant equivalences. -/
structure ResidualData where
  cco : SemanticCCO.{0,v,0,w} S
  normalized : NoFiniteExactKernel S
  E : ColourEq S ()
  exact : ExactCRT.IsExactEq S (i := ()) E.val
  infinite : ¬ FiniteClasses S E
  minimalExact : ∀ K : ColourEq S (), ExactCRT.IsExactEq S (i := ()) K.val →
    K ≤ E → ¬ FiniteClasses S K → E ≤ K
  residual : correspondenceEq S H cco E exact = finitePacket S H

namespace ResidualData
variable (R : ResidualData S H)
include R

/-- Finite-index exact cores convert EXACT minimality to FULL minimality.
This is a proved conversion, rather than an extra residual assumption. -/
theorem isDirection : IsDirection S R.E := by
  refine ⟨R.infinite, ?_⟩
  intro K hK
  by_contra hinf
  have hcore : R.E ≤ core S K :=
    R.minimalExact (core S K) (core_exact S H K)
      ((core_le S K).trans hK.le) (core_infinite_of_infinite S H R.cco K hinf)
  exact (not_le_of_gt hK) (hcore.trans (core_le S K))

def direction : Direction S := ⟨R.E, R.isDirection S H⟩

@[simp] theorem direction_val : (R.direction S H).val = R.E := rfl

/-- C19: every other full invariant direction would lie in the finite
correspondence, contrary to its infinite classes. -/
theorem direction_unique (D : Direction S) : D = R.direction S H := by
  by_contra hne
  have hle := direction_le_other_correspondence S H R.cco R.normalized
    (R.direction S H) D (Ne.symm hne)
  have hc : oldCorrespondence S H R.cco (R.direction S H) = finitePacket S H := by
    exact R.residual
  rw [hc] at hle
  exact D.property.1 (finiteClasses_of_le S hle (finitePacket_finite S H))

theorem directionCount_eq_one : directionCount S = 1 := by
  exact Nat.card_eq_one_iff_exists.mpr ⟨R.direction S H, R.direction_unique S H⟩

theorem owner_containsDirections : ContainsDirections S R.E := by
  intro D
  rw [R.direction_unique S H D]
  exact le_rfl

/-- The positive represented word used by the generic anchored theorem
is constructed from the residual source, not supplied as a new provider. -/
theorem positive_word : ∃ p : Atom S, ∃ n : ℕ,
    RawWord.relation S (RealHull.Canonical.positiveEvenWord S p n) = R.E.val.r :=
  direction_positive_word S H R.cco (R.direction S H)

theorem owner_ne_identity : R.E ≠ ⊥ := by
  intro h
  exact R.infinite (h ▸ finiteClasses_bot S)

variable [Infinite M]

/-- C20, with the actual greatest finite packet and the empty-base
convention inherited from the absolute real-closure theorem. -/
theorem real_acl (A : Finset M) : Acl G A = packetClosure S H A :=
  acl_rank_one S H R.cco (R.directionCount_eq_one S H) A

theorem full_real_acl (A : Finset M) : FullRealAcl S A = packetClosure S H A := by
  rw [fullRealAcl_eq S H, R.real_acl S H A]

/-- C21: owners are fixed individually; the assertion is about the FULL
original automorphism stabilizer and arbitrary finite real bases. -/
theorem named_owner_acl {I : Type*} [Finite I]
    (q : I → Quotient R.E.val) (A : Finset M) :
    FullOwnerAcl S A (fun _ : I => R.E) q = packetClosure S H A := by
  rw [full_mixed_harmless_owners S H R.cco (fun _ : I => R.E)
    (fun _ => R.owner_containsDirections S H) q A, R.full_real_acl S H A]

omit [Infinite M] in
/-- The original finite packet is thin after the stated finite-exact
normalization, with no claim that the finite packet itself is exact. -/
theorem packet_thin : ThinBottom S (finitePacket S H) :=
  terminal_greatest_finite_packet_thin S H R.normalized

abbrev PacketGroup := Translation S (finitePacket S H) G

def ownerStabilizer : Subgroup (PacketGroup S H) :=
  equivalenceTranslations S (finitePacket S H) R.E

end ResidualData
end
end CCO.OwnerTransversal
