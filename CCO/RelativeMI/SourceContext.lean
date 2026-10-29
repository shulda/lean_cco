import CCO.RelativeMI.CompatibleGroup
import CCO.OwnerTransversal.ClosedSAP
import CCO.OwnerTransversal.Inflation
import CCO.SafeReadings.TransversalSAP

/-! C30 specializes all standing full-owner source providers to the
ACTUALLY CONSTRUCTED fine stage, before a safe palette or decoder exists. -/
universe v w t
namespace CCO.RelativeMI.FineStage
noncomputable section
open ParityHasse.Original RealHull.Geometry RealClosure.Bounds
open FinitePackets.Normalization OwnerTransversal SafeReadings AclOwners

variable {M : Type v} (S : AtomicSource.{0,v,w} Unit (fun _ => M))
variable {G : Type t} [Group G] [MulAction G M] (H : HomogeneousSource S G)
variable [Countable M] [DecidableEq M] [Infinite M] (R : ResidualData S H)
variable (J : ColourEq S ()) (A0 : Finset M) (B : Finset (Coarse S H J))
variable (overA0 : ∀ x : ↥A0, coarseOwner S H J x.val ∈ B) (hEJ : R.E ≤ J)
variable (F : FineStage S H R J A0 B overA0 hEJ)

/-- Absolute closure is stated in ORIGINAL M; named closure, actual
named homogeneity and genuine transversal SAP are separately discharged. -/
theorem actual_source_context :
    (∀ A : Finset M, FullRealAcl S A = RealClosure.Bounds.packetClosure S H A) ∧
    (∀ A : Finset (NamedCarrier S H R F.U),
      Acl (NamedAut S H R F.U) A = namedPacketClosure S H R F.U A) ∧
    (namedStructure S H R F.U).Homogeneous ∧
    AgeSAP (TransversalSource.source S H R F.U) :=
  ⟨R.full_real_acl S H,named_acl S H R F.U F.invariant,
    named_homogeneous S H R F.U,TransversalSource.ageSAP S H R F.U⟩

/-- Strong amalgamation of EVERY complete closed named span, with
arbitrary induced embeddings and the empty base retained. -/
theorem actual_closed_source_amalgamation
    (C L P : Finset (NamedCarrier S H R F.U))
    (hC : PacketClosed S H R F.U C) (hL : PacketClosed S H R F.U L)
    (hP : PacketClosed S H R F.U P)
    (e : NamedEmbedding S H R F.U C L) (d : NamedEmbedding S H R F.U C P) :
    ∃ D : Finset (NamedCarrier S H R F.U), PacketClosed S H R F.U D ∧
      ∃ (i : NamedEmbedding S H R F.U L D) (j : NamedEmbedding S H R F.U P D),
        (∀ c, i.toEmbedding (e.toEmbedding c) = j.toEmbedding (d.toEmbedding c)) ∧
        (∀ l p, i.toEmbedding l = j.toEmbedding p ↔
          ∃ c, e.toEmbedding c = l ∧ d.toEmbedding c = p) :=
  closed_strong_amalgamation S H R F.U C L P hC hL hP e d

/-- The full inflation of THIS actual primitive source recovers N_U,
including literal fine names, owners and EVERY actual thin function. -/
theorem actual_inflation_readout :
    ∃ e : Inflation.Carrier S H R F.U ≃ NamedCarrier S H R F.U,
      (∀ x, TransversalAge.ownerLabel S H R F.U (e x) =
        (Inflation.table S H R F.U F.invariant).owner x) ∧
      (∀ x y, col S (e x).val (e y).val =
        (Inflation.table S H R F.U F.invariant).colour x y) ∧
      ∀ (g : ResidualData.PacketGroup S H) x,
        e ((Inflation.action S H R F.U).smul g x) = packetPoint S H R F.U F.invariant g (e x) :=
  Inflation.recovery_readout S H R F.U F.invariant

end
end CCO.RelativeMI.FineStage
