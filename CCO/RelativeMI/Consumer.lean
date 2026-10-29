import CCO.RelativeMI.FixedWitness
import CCO.RelativeMI.SourceSeed
import CCO.RelativeMI.Padding
import CCO.RelativeMI.SourceContext
import CCO.RelativeMI.SequentialUse

/-! The principal normalized relative MI theorem constructs every local
source, fine-owner, safe-padding, HKN, selector, decoder and image-group
provider before trimming ONE actual original-language witness. Ordinary
EPPA is assumed ONLY for the actual lower quotient Q/E. -/
universe v w t
namespace CCO.RelativeMI
noncomputable section
open ParityHasse.Original RealHull.Geometry RealClosure.Bounds
open FinitePackets.Normalization OwnerTransversal AclOwners
open Owners.Product Owners.Provider ExactCRT RawExact
variable {M : Type v} (S : AtomicSource.{0,v,w} Unit (fun _ => M))
variable {G : Type t} [Group G] [MulAction G M] (H : HomogeneousSource S G)
variable [Countable M] [DecidableEq M] [Infinite M]
variable (J : ColourEq S ())
local instance relativeMICoarseAction : MulAction G (Coarse S H J) := originalQuotientAction S H J

/-- The finite coarse EPPA-witness condition is retained literally from
the source, even though the local lower-quotient construction is stronger
than an intermediate step that inspects this condition. -/
def CoarseEPPAFor (A0 : Finset M) (B : Finset (Coarse S H J)) : Prop :=
  EPPAFor (G := G) (ι := (Subtype.val : ↥B → Coarse S H J))
    {b | b.val ∈ coarseOwner S H J '' (↑A0 : Set M)}

theorem normalized_relative_mi
    (cco : SemanticCCO.{0,v,0,w} S) (normalized : NoFiniteExactKernel S)
    (D : Direction S) (unique : ∀ D' : Direction S, D' = D)
    (hJ : IsExactEq S (i := ()) J.val) (hDJ : D.val ≤ J)
    (ep : letI := originalQuotientAction S H D.val
      OrdinaryEPPA G (Quotient D.val.val))
    (safe : Set (S.Atom () ())) (hSafe : StrongClosedAmalgamation S G safe)
    (A0 : Finset M) (hne : A0.Nonempty) (B : Finset (Coarse S H J))
    (overA0 : ∀ x : ↥A0, coarseOwner S H J x.val ∈ B)
    (_eppaB : CoarseEPPAFor S H J A0 B)
    (orbit : CoarseOrbitCover S H J A0 B overA0)
    (closedB : ∀ b ∈ B, ∀ c,
      ownerPacket S H (coarseOwner S H J) Quotient.mk''_surjective (fun _ _ => rfl) b c → c ∈ B) :
    Nonempty (OriginalWitness S H J A0 B overA0 safe) := by
  classical
  let R := normalizedResidual S H cco normalized D unique
  letI : MulAction G (Owner S H R) := originalQuotientAction S H R.E
  have hEJ : R.E ≤ J := hDJ
  have epFine : OrdinaryEPPA G (Owner S H R) := ep
  obtain ⟨F⟩ := actual_fine_stage S H R J A0 B overA0 closedB hEJ hJ epFine
  let seed := sourceSeed S H R F.U A0
  let P := safePadding S H R F.U F.invariant safe hSafe seed (sourceSeed_closed S H R F.U A0)
  let A := liftedSource S H R F.U P.carrier
  have hA : (HKNReservoir.sourceStructure S H R F.U F.invariant).IsClosed A :=
    liftedSource_closed S H R F.U F.invariant P.carrier P.closed
  letI : Finite A := (liftedSource_finite S H R F.U P.carrier).to_subtype
  have oldContains := liftedSource_contains S H R F.U A0 P.carrier P.contains F.contains
  have support := liftedSource_support S H R F.U F.invariant P.carrier P.covers
  have hneA := liftedSource_nonempty S H R F.U A0 P.carrier P.contains F.contains hne
  have padding := liftedSource_safe_cross S H R F.U A0 P.carrier safe P.safe_cross
  let Δ := F.compatibleGroup S H R J A0 B overA0 hEJ
  let hΔ := F.diagonal_mem S H R J A0 B overA0 hEJ
  have hs := orbitSafe_system S H R F.U F.invariant safe hSafe
  obtain ⟨r,q,hq,hout⟩ := actual_safe_decoder S H R F.U F.invariant Δ hΔ A hA hneA safe hs
  letI := r.stage.finiteNew
  obtain ⟨out⟩ := hout
  letI : Finite (ResidualData.PacketGroup S H) :=
    translation_finite S (finitePacket S H) H (R.packet_thin S H)
  let world := F.decoderFixedWorld S H R J A0 B overA0 hEJ A hA oldContains support safe hs padding r q hq out
  exact ⟨world.witness S H J A0 B overA0 orbit⟩

/-- Genuine receiving use: ONE constructed actual witness simultaneously
supports two exact owner requests, their composition, and an independently
selected rooted unsafe transport. -/
theorem normalized_relative_mi_joint_use
    (cco : SemanticCCO.{0,v,0,w} S) (normalized : NoFiniteExactKernel S)
    (D : Direction S) (unique : ∀ D' : Direction S, D' = D)
    (hJ : IsExactEq S (i := ()) J.val) (hDJ : D.val ≤ J)
    (ep : letI := originalQuotientAction S H D.val
      OrdinaryEPPA G (Quotient D.val.val))
    (safe : Set (S.Atom () ())) (hSafe : StrongClosedAmalgamation S G safe)
    (A0 : Finset M) (hne : A0.Nonempty) (B : Finset (Coarse S H J))
    (overA0 : ∀ x : ↥A0, coarseOwner S H J x.val ∈ B)
    (_eppaB : CoarseEPPAFor S H J A0 B)
    (orbit : CoarseOrbitCover S H J A0 B overA0)
    (closedB : ∀ b ∈ B, ∀ c,
      ownerPacket S H (coarseOwner S H J) Quotient.mk''_surjective (fun _ _ => rfl) b c → c ∈ B) :
    ∃ W : OriginalWitness S H J A0 B overA0 safe,
      ∀ (r1 r2 : OriginalRequest S H J A0 B overA0)
        (x : r1.part.domain) (y : r2.part.domain), r1.part.map x = y.val →
        ∀ Z : Set W.carrier, UnsafeSet S (Subtype.val : W.carrier → M) safe Z →
        ∀ z ∈ Z,
        let quotient := (inducedQuotient (coarseOwner S H J) (fun _ _ => rfl)
          W.carrier (↑B) W.over W.onto).action
        ∃ β1 β2 β0 : OrbitalAut G M (Subtype.val : W.carrier → M),
          (quotient β1 = r1.owner ∧ ∀ a : r1.part.domain,
            (β1.val (W.sourcePoint a.val)).val = (r1.part.map a).val) ∧
          (quotient β2 = r2.owner ∧ ∀ a : r2.part.domain,
            (β2.val (W.sourcePoint a.val)).val = (r2.part.map a).val) ∧
          quotient (β2*β1) = r2.owner*r1.owner ∧
          ((β2*β1).val (W.sourcePoint x.val)).val = (r2.part.map y).val ∧
          (∀ a ∈ Z, (β0.val a).val ∈ RealClosure.Bounds.packetClosure S H A0) ∧
          (β0.val z).val ∈ A0 := by
  obtain ⟨W⟩ := normalized_relative_mi S H J cco normalized D unique hJ hDJ ep
    safe hSafe A0 hne B overA0 _eppaB orbit closedB
  exact ⟨W,fun r1 r2 x y hxy Z hZ z hz => W.sequential_and_rooted r1 r2 x y hxy Z hZ z hz⟩

end
end CCO.RelativeMI
