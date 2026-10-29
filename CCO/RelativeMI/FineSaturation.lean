import CCO.RelativeMI.FineOwners
import CCO.OwnerTransversal.PacketAction

/-! C27--C28: saturating the one fine EPPA host by the ORIGINAL thin
group introduces no new coarse owner. Every selected full fine map has
an original lift and therefore extends across this same saturation. -/
universe v w t
namespace CCO.RelativeMI
noncomputable section
open ParityHasse.Original RealHull.Geometry RealClosure.Bounds
open FinitePackets.Normalization OwnerTransversal AclOwners
open Owners.Product Owners.Provider ExactCRT RawExact

variable {M : Type v} (S : AtomicSource.{0,v,w} Unit (fun _ => M))
variable {G : Type t} [Group G] [MulAction G M] (H : HomogeneousSource S G)
variable [Countable M] [DecidableEq M] (R : ResidualData S H)
variable (J : ColourEq S ())
local instance : MulAction G (Owner S H R) := originalQuotientAction S H R.E
local instance : MulAction G (Coarse S H J) := originalQuotientAction S H J

/-- This is commutation with ORIGINAL motions, before any assertion
about the full finite owner automorphism group. -/
theorem fine_packet_original (e : ResidualData.PacketGroup S H) (g : G)
    (q : Owner S H R) :
    packetOwnerMove S H R e (g • q) = g • packetOwnerMove S H R e q := by
  induction q using Quotient.inductionOn with
  | _ x =>
      exact congrArg (owner S H R)
        (translation_equivariant S (finitePacket S H) G e g x)

variable (A0 : Finset M) (B : Finset (Coarse S H J))
variable (overA0 : ∀ x : ↥A0, coarseOwner S H J x.val ∈ B)

structure FineStage (hEJ : R.E ≤ J) where
  U : Finset (Owner S H R)
  invariant : PacketInvariant S H R U
  contains : ∀ x ∈ RealClosure.Bounds.packetClosure S H A0, owner S H R x ∈ U
  over : ∀ q : ↥U, fineProjection S H R J hEJ q.val ∈ B
  onto : Function.Surjective (ownerProjection (fineProjection S H R J hEJ)
    (↑U : Set (Owner S H R)) (↑B : Set (Coarse S H J)) over)
  extensions : ∀ r : OriginalRequest S H J A0 B overA0,
    ∃ α : OrbitalAut G (Owner S H R) (Subtype.val : ↥U → Owner S H R),
      (∀ x : r.part.domain,
        (α.val ⟨owner S H R x.val.val,
          contains x.val.val ⟨x.val.val,x.val.property,(finitePacket S H).val.refl _⟩⟩).val =
            owner S H R (r.part.map x).val) ∧
      (∀ q : ↥U, fineProjection S H R J hEJ (α.val q).val =
        (r.owner.val (ownerProjection (fineProjection S H R J hEJ) (↑U) (↑B) over q)).val)

variable (closedB : ∀ b ∈ B, ∀ c,
  ownerPacket S H (coarseOwner S H J) Quotient.mk''_surjective (fun _ _ => rfl) b c → c ∈ B)

include closedB in
/-- The full finite host is an actual output of `fine_base` in the
principal constructor below, never an additional principal hypothesis. -/
theorem fine_stage_from_base (hEJ : R.E ≤ J)
    (F : FineBase S H R J A0 B overA0 hEJ) :
    Nonempty (FineStage S H R J A0 B overA0 hEJ) := by
  classical
  let K := ResidualData.PacketGroup S H
  let : Finite K := translation_finite S (finitePacket S H) H (R.packet_thin S H)
  let : Finite F.carrier := F.finite.to_subtype
  let sat : Set (Owner S H R) := Set.range
    (fun p : K × F.carrier => packetOwnerMove S H R p.1 p.2.val)
  have hsat : sat.Finite := Set.finite_range _
  let U := hsat.toFinset
  have inc (q : F.carrier) : q.val ∈ U :=
    hsat.mem_toFinset.mpr ⟨⟨1,q⟩,packetOwnerMove_one S H R q.val⟩
  have hU : PacketInvariant S H R U := by
    intro e x hx
    obtain ⟨⟨f,q⟩,heq⟩ := hsat.mem_toFinset.mp hx
    apply hsat.mem_toFinset.mpr
    refine ⟨⟨e*f,q⟩,?_⟩
    exact (packetOwnerMove_mul S H R e f q.val).trans
      (congrArg (packetOwnerMove S H R e) heq)
  have oldU (x : M) (hx : x ∈ RealClosure.Bounds.packetClosure S H A0) : owner S H R x ∈ U :=
    inc ⟨owner S H R x,F.contains x hx⟩
  have overU : ∀ q : ↥U, fineProjection S H R J hEJ q.val ∈ B := by
    intro u
    obtain ⟨⟨e,q⟩,heq⟩ := hsat.mem_toFinset.mp u.property
    change packetOwnerMove S H R e q.val = u.val at heq
    obtain ⟨x,hx⟩ := Quotient.mk''_surjective q.val
    change owner S H R x = q.val at hx
    have base : coarseOwner S H J x ∈ B := by
      change fineProjection S H R J hEJ (owner S H R x) ∈ B
      rw [hx]
      exact F.over q
    rw [← heq,← hx]
    change coarseOwner S H J (e.val x) ∈ B
    exact closedB (coarseOwner S H J x) base _
      (packet_projection S H (coarseOwner S H J) Quotient.mk''_surjective
        (fun _ _ => rfl) x (e.val x) (translation_in_packet S (finitePacket S H) G e x))
  have ontoU : Function.Surjective (ownerProjection (fineProjection S H R J hEJ)
      (↑U : Set (Owner S H R)) (↑B) overU) := by
    intro b
    obtain ⟨q,hq⟩ := F.onto b
    exact ⟨⟨q.val,inc q⟩,hq⟩
  let presentation := exactPresentation S R.exact
  have homogeneous : HomogeneousSource (actualQuotientSource S H R.E) G :=
    actualQuotient_homogeneous S H R.E presentation
      (exactPresentation_represents S R.exact) R.cco
  refine ⟨⟨U,hU,oldU,overU,ontoU,?_⟩⟩
  intro r
  obtain ⟨β,hβ,hβown⟩ := F.extensions r
  obtain ⟨g,hg⟩ := extend_induced_aut (actualQuotientSource S H R.E) homogeneous
    F.carrier F.finite β
  have gB (b : ↥B) : g • b.val = (r.owner.val b).val := by
    obtain ⟨q,hq⟩ := F.onto b
    have hπ : fineProjection S H R J hEJ q.val = b.val := congrArg Subtype.val hq
    calc
      _ = g • fineProjection S H R J hEJ q.val := congrArg (fun b => g • b) hπ.symm
      _ = fineProjection S H R J hEJ (g • q.val) :=
        (fineProjection_equivariant S H R J hEJ g q.val).symm
      _ = fineProjection S H R J hEJ (β.val q).val :=
        congrArg (fineProjection S H R J hEJ) (hg q)
      _ = (r.owner.val (ownerProjection (fineProjection S H R J hEJ) F.carrier (↑B) F.over q)).val :=
        hβown q
      _ = (r.owner.val b).val := congrArg (fun b : ↥B => (r.owner.val b).val) hq
  have mapsU (u : ↥U) : g • u.val ∈ U := by
    obtain ⟨⟨e,q⟩,heq⟩ := hsat.mem_toFinset.mp u.property
    apply hsat.mem_toFinset.mpr
    refine ⟨⟨e,β.val q⟩,?_⟩
    calc
      _ = packetOwnerMove S H R e (g • q.val) :=
        congrArg (packetOwnerMove S H R e) (hg q).symm
      _ = g • packetOwnerMove S H R e q.val := fine_packet_original S H R e g q.val
      _ = g • u.val := congrArg (fun q => g • q) heq
  let α : OrbitalAut G (Owner S H R) (Subtype.val : ↥U → Owner S H R) :=
    restrictAut (ambientAut (A := Owner S H R) g) (↑U : Set (Owner S H R)) mapsU
  refine ⟨α,?_,?_⟩
  · intro x
    change g • owner S H R x.val.val = owner S H R (r.part.map x).val
    exact (hg ⟨owner S H R x.val.val,
      F.contains x.val.val ⟨x.val.val,x.val.property,(finitePacket S H).val.refl _⟩⟩).trans (hβ x)
  · intro q
    change fineProjection S H R J hEJ (g • q.val) = _
    exact (fineProjection_equivariant S H R J hEJ g q.val).trans
      (gB (ownerProjection (fineProjection S H R J hEJ) (↑U) (↑B) overU q))

include closedB in
/-- The complete fine-owner stage is constructed from the original
geometry and ONLY the lower-quotient ordinary EPPA premise. -/
theorem actual_fine_stage (hEJ : R.E ≤ J) (hJ : IsExactEq S (i := ()) J.val)
    (ep : OrdinaryEPPA G (Owner S H R)) :
    Nonempty (FineStage S H R J A0 B overA0 hEJ) := by
  obtain ⟨F⟩ := fine_base S H R J A0 B overA0 closedB hEJ hJ ep
  exact fine_stage_from_base S H R J A0 B overA0 closedB hEJ F

end
end CCO.RelativeMI
