import CCO.RelativeMI.DecodedImage
import CCO.RelativeMI.PaddingExclusion
import CCO.RelativeMI.SourceRequests
import CCO.RelativeMI.OrbitWitness

/-! Assemble EVERY internal fixed-world field from the actual fine
stage, one safe decoder, and its literal padded source. The group is the
semilinear permutation IMAGE; every prescribed owner component is retained.
The principal constructor supplies the padding and decoder below. -/
universe v w t
namespace CCO.RelativeMI.FineStage
noncomputable section
open AllThoseEPPA HKNReservoir ParityHasse.Original RealHull.Geometry RealClosure.Bounds
open FinitePackets.Normalization OwnerTransversal TransversalAge SafeReadings Selectors FullRows
open Owners.Product Owners.Provider
variable {M : Type v} (S : AtomicSource.{0,v,w} Unit (fun _ => M))
variable {G : Type t} [Group G] [MulAction G M] (H : HomogeneousSource S G)
variable [Countable M] [DecidableEq M] [Infinite M] (R : ResidualData S H)
variable (J : ColourEq S ()) (A0 : Finset M) (B : Finset (Coarse S H J))
variable (overA0 : ∀ x : ↥A0, coarseOwner S H J x.val ∈ B) (hEJ : R.E ≤ J)
local instance fixedWitnessCoarseAction : MulAction G (Coarse S H J) := originalQuotientAction S H J
variable (F : FineStage S H R J A0 B overA0 hEJ)
variable (A : Set (SourceCarrier S H R F.U))
variable (hA : (sourceStructure S H R F.U F.invariant).IsClosed A)
variable [Finite A]
variable (oldContains : ∀ x ∈ RealClosure.Bounds.packetClosure S H A0,
  ∃ a : A, a.val.down.val = x)
variable (support : ∀ u : ↥F.U, ∃ a : A, (sourceData S H R F.U F.invariant).owner a.val = u)
variable (safe : Set (S.Atom () ()))
variable (hs : SafeSystem (TransversalSource.source S H R F.U) (orbitSafe S H R F.U F.invariant safe))
variable (padding : ∀ a : A, a.val.down.val ∉ RealClosure.Bounds.packetClosure S H A0 →
  ∀ b : A, ¬ finitePacket S H a.val.down.val b.val.down.val →
    ∃ d ∈ safe, col S a.val.down.val b.val.down.val = some d)
variable (r : CompletableReservoir S H R F.U F.invariant (F.compatibleGroup S H R J A0 B overA0 hEJ) A hA (reservoirThreshold S H R F.U))
local instance fixedWitnessFiniteNew : Finite r.stage.New := r.stage.finiteNew
variable (q : JointReading S H R F.U F.invariant (F.compatibleGroup S H R J A0 B overA0 hEJ))
variable (hq : q.SafeOn S H R F.U F.invariant (F.compatibleGroup S H R J A0 B overA0 hEJ) (orbitSafe S H R F.U F.invariant safe))
variable (out : DecoderOutput S H R F.U F.invariant (F.compatibleGroup S H R J A0 B overA0 hEJ) q (F.diagonal_mem S H R J A0 B overA0 hEJ) A hA (r.stage.model) (locallyInSource_of_faithful (sourceTag S H R F.U (F.compatibleGroup S H R J A0 B overA0 hEJ)) r.stage.inclusion r.stage.faithful) (r.certificate) r.stage.inclusion r.stage.inclusion_lang)

def decoderFixedWorld : FixedWorld S H J A0 B overA0 safe (Vertex (PacketRecovery.PacketIndex (r.stage.model)) (ResidualData.PacketGroup S H)) (decodedPermutationImage S H R F.U F.invariant (F.compatibleGroup S H R J A0 B overA0 hEJ) q (F.diagonal_mem S H R J A0 B overA0 hEJ) A hA (r.stage.model) (locallyInSource_of_faithful (sourceTag S H R F.U (F.compatibleGroup S H R J A0 B overA0 hEJ)) r.stage.inclusion r.stage.faithful) (r.certificate)) := by
  classical
  letI := TransversalPure.thinCommGroup S H R
  let real : (Vertex (PacketRecovery.PacketIndex (r.stage.model)) (ResidualData.PacketGroup S H)) ↪ M := out.realEmbedding
  let component := decodedOwnerComponent S H R F.U F.invariant (F.compatibleGroup S H R J A0 B overA0 hEJ) q (F.diagonal_mem S H R J A0 B overA0 hEJ) A hA (r.stage.model) (locallyInSource_of_faithful (sourceTag S H R F.U (F.compatibleGroup S H R J A0 B overA0 hEJ)) r.stage.inclusion r.stage.faithful) (r.certificate)
    r.stage.inclusion r.stage.inclusion_lang support
  let coarse := (F.coarseHom S H R J A0 B overA0 hEJ).comp component
  have fine (x : (Vertex (PacketRecovery.PacketIndex (r.stage.model)) (ResidualData.PacketGroup S H))) : coarseOwner S H J (real x) =
      fineProjection S H R J hEJ (vertexOwner S H R F.U F.invariant (F.compatibleGroup S H R J A0 B overA0 hEJ) A hA (r.stage.model) (locallyInSource_of_faithful (sourceTag S H R F.U (F.compatibleGroup S H R J A0 B overA0 hEJ)) r.stage.inclusion r.stage.faithful) x).val :=
    (fineProjection_owner S H R J hEJ (real x)).symm.trans
      (congrArg (fineProjection S H R J hEJ) (out.realEmbedding_owner x))
  have over (x : (Vertex (PacketRecovery.PacketIndex (r.stage.model)) (ResidualData.PacketGroup S H))) : coarseOwner S H J (real x) ∈ B :=
    (fine x).symm ▸ F.over (vertexOwner S H R F.U F.invariant (F.compatibleGroup S H R J A0 B overA0 hEJ) A hA (r.stage.model) (locallyInSource_of_faithful (sourceTag S H R F.U (F.compatibleGroup S H R J A0 B overA0 hEJ)) r.stage.inclusion r.stage.faithful) x)
  have langs (γ : (F.compatibleGroup S H R J A0 B overA0 hEJ)) : ∃ g : Structure.Automorphism (sourceAction S H R F.U (F.compatibleGroup S H R J A0 B overA0 hEJ))
      (encode (decodedData S H R F.U F.invariant (F.compatibleGroup S H R J A0 B overA0 hEJ) q (F.diagonal_mem S H R J A0 B overA0 hEJ) A hA (r.stage.model) (locallyInSource_of_faithful (sourceTag S H R F.U (F.compatibleGroup S H R J A0 B overA0 hEJ)) r.stage.inclusion r.stage.faithful) (r.certificate))), g.lang = γ :=
    DecoderOutput.every_language S H R F.U F.invariant (F.compatibleGroup S H R J A0 B overA0 hEJ) q (F.diagonal_mem S H R J A0 B overA0 hEJ) A hA (r.stage.model) (locallyInSource_of_faithful (sourceTag S H R F.U (F.compatibleGroup S H R J A0 B overA0 hEJ)) r.stage.inclusion r.stage.faithful) (r.certificate)
      r.stage.inclusion r.stage.inclusion_lang out γ
  refine {
    real := real
    source := ?_
    over := over
    colours := ?_
    packetThin := R.packet_thin S H
    thin := decodedThinImageHom S H R F.U F.invariant (F.compatibleGroup S H R J A0 B overA0 hEJ) q (F.diagonal_mem S H R J A0 B overA0 hEJ) A hA (r.stage.model) (locallyInSource_of_faithful (sourceTag S H R F.U (F.compatibleGroup S H R J A0 B overA0 hEJ)) r.stage.inclusion r.stage.faithful) (r.certificate)
    thin_real := ?_
    coarse := coarse
    coarse_surjective := ?_
    coarse_real := ?_
    requests := ?_
    multipacket := ?_ }
  · intro a ha
    obtain ⟨x,hx⟩ := oldContains a ⟨a,ha,(finitePacket S H).val.refl _⟩
    exact ⟨zeroRowEmbed S H R F.U F.invariant (F.compatibleGroup S H R J A0 B overA0 hEJ) A hA (r.stage.model) (locallyInSource_of_faithful (sourceTag S H R F.U (F.compatibleGroup S H R J A0 B overA0 hEJ)) r.stage.inclusion r.stage.faithful) r.stage.inclusion x,
      (out.realEmbedding_source_fixed x).trans hx⟩
  · intro g x y
    exact DecoderOutput.realEmbedding_image_colour S H R F.U F.invariant (F.compatibleGroup S H R J A0 B overA0 hEJ) q (F.diagonal_mem S H R J A0 B overA0 hEJ) A hA (r.stage.model) (locallyInSource_of_faithful (sourceTag S H R F.U (F.compatibleGroup S H R J A0 B overA0 hEJ)) r.stage.inclusion r.stage.faithful) (r.certificate)
      r.stage.inclusion r.stage.inclusion_lang out g x y
  · intro g x
    change real (translate g x) = g.val (real x)
    exact out.realEmbedding_translate g x
  · exact (F.coarseHom_surjective S H R J A0 B overA0 hEJ).comp
      (decodedOwnerComponent_surjective S H R F.U F.invariant (F.compatibleGroup S H R J A0 B overA0 hEJ) q (F.diagonal_mem S H R J A0 B overA0 hEJ) A hA (r.stage.model) (locallyInSource_of_faithful (sourceTag S H R F.U (F.compatibleGroup S H R J A0 B overA0 hEJ)) r.stage.inclusion r.stage.faithful) (r.certificate)
        r.stage.inclusion r.stage.inclusion_lang support langs)
  · intro g x
    let u := vertexOwner S H R F.U F.invariant (F.compatibleGroup S H R J A0 B overA0 hEJ) A hA (r.stage.model) (locallyInSource_of_faithful (sourceTag S H R F.U (F.compatibleGroup S H R J A0 B overA0 hEJ)) r.stage.inclusion r.stage.faithful) x
    let δ := component g
    have ho : vertexOwner S H R F.U F.invariant (F.compatibleGroup S H R J A0 B overA0 hEJ) A hA (r.stage.model) (locallyInSource_of_faithful (sourceTag S H R F.U (F.compatibleGroup S H R J A0 B overA0 hEJ)) r.stage.inclusion r.stage.faithful) (g.val x) = δ.val.val u :=
      decodedImage_owner S H R F.U F.invariant (F.compatibleGroup S H R J A0 B overA0 hEJ) q (F.diagonal_mem S H R J A0 B overA0 hEJ) A hA (r.stage.model) (locallyInSource_of_faithful (sourceTag S H R F.U (F.compatibleGroup S H R J A0 B overA0 hEJ)) r.stage.inclusion r.stage.faithful) (r.certificate)
        r.stage.inclusion r.stage.inclusion_lang support g x
    have hc := congrArg Subtype.val (F.coarseHom_projection S H R J A0 B overA0 hEJ δ u)
    have hb : (⟨coarseOwner S H J (real x),over x⟩ : ↥B) =
        F.projection S H R J A0 B overA0 hEJ u := Subtype.ext (fine x)
    change coarseOwner S H J (real (g.val x)) = ((F.coarseHom S H R J A0 B overA0 hEJ δ).val _).val
    rw [fine,ho]
    exact hc.symm.trans (congrArg (fun b : ↥B => ((F.coarseHom S H R J A0 B overA0 hEJ δ).val b).val) hb.symm)
  · intro request
    obtain ⟨p,hcoarse,hpoints⟩ := F.source_request S H R J A0 B overA0 hEJ A hA oldContains request
    obtain ⟨g,hg,hpoint⟩ := out.extends_original p
    refine ⟨decodedAutImage S H R F.U F.invariant (F.compatibleGroup S H R J A0 B overA0 hEJ) q (F.diagonal_mem S H R J A0 B overA0 hEJ) A hA (r.stage.model) (locallyInSource_of_faithful (sourceTag S H R F.U (F.compatibleGroup S H R J A0 B overA0 hEJ)) r.stage.inclusion r.stage.faithful) (r.certificate) g,?_,?_⟩
    · change F.coarseHom S H R J A0 B overA0 hEJ
        (component (decodedAutImage S H R F.U F.invariant (F.compatibleGroup S H R J A0 B overA0 hEJ) q (F.diagonal_mem S H R J A0 B overA0 hEJ) A hA (r.stage.model) (locallyInSource_of_faithful (sourceTag S H R F.U (F.compatibleGroup S H R J A0 B overA0 hEJ)) r.stage.inclusion r.stage.faithful) (r.certificate) g)) = request.owner
      rw [decodedOwnerComponent_autImage S H R F.U F.invariant (F.compatibleGroup S H R J A0 B overA0 hEJ) q (F.diagonal_mem S H R J A0 B overA0 hEJ) A hA (r.stage.model) (locallyInSource_of_faithful (sourceTag S H R F.U (F.compatibleGroup S H R J A0 B overA0 hEJ)) r.stage.inclusion r.stage.faithful) (r.certificate)
        r.stage.inclusion r.stage.inclusion_lang support g,hg]
      exact hcoarse
    · intro x v hv
      obtain ⟨a,ha,hsrc,hval⟩ := hpoints x
      have he : v = zeroRowEmbed S H R F.U F.invariant (F.compatibleGroup S H R J A0 B overA0 hEJ) A hA (r.stage.model) (locallyInSource_of_faithful (sourceTag S H R F.U (F.compatibleGroup S H R J A0 B overA0 hEJ)) r.stage.inclusion r.stage.faithful) r.stage.inclusion a :=
        real.injective (hv.trans (ha.symm.trans (out.realEmbedding_source_fixed a).symm))
      rw [he]
      change real (g (zeroRowEmbed S H R F.U F.invariant (F.compatibleGroup S H R J A0 B overA0 hEJ) A hA (r.stage.model) (locallyInSource_of_faithful (sourceTag S H R F.U (F.compatibleGroup S H R J A0 B overA0 hEJ)) r.stage.inclusion r.stage.faithful) r.stage.inclusion a)) = _
      rw [hpoint a hsrc]
      exact (out.realEmbedding_source_fixed (p.point a)).trans hval
  · intro X hX multi
    have hUnsafe : DecodedUnsafe S H R F.U F.invariant (F.compatibleGroup S H R J A0 B overA0 hEJ) q (F.diagonal_mem S H R J A0 B overA0 hEJ) A hA (r.stage.model) (locallyInSource_of_faithful (sourceTag S H R F.U (F.compatibleGroup S H R J A0 B overA0 hEJ)) r.stage.inclusion r.stage.faithful) (r.certificate) safe X := by
      intro x hx y hy hxy hsafe
      obtain ⟨a,ha,hcol⟩ := hsafe
      exact hX x hx y hy hxy a ((out.realEmbedding_colour x y).trans hcol) ha
    have multiple : ∃ x ∈ X, ∃ y ∈ X, x.1 ≠ y.1 := by
      obtain ⟨x,hx,y,hy,hF⟩ := multi
      refine ⟨x,hx,y,hy,?_⟩
      intro hp
      let k : (ResidualData.PacketGroup S H) := y.2*x.2⁻¹
      have ht : translate k x = y := by
        apply Prod.ext
        · exact hp
        · change (y.2*x.2⁻¹)*x.2 = y.2
          simp only [mul_assoc,inv_mul_cancel,mul_one]
      have hr : k.val (real x) = real y :=
        (out.realEmbedding_translate k x).symm.trans (congrArg real ht)
      exact hF (hr ▸ translation_in_packet S (finitePacket S H) G k (real x))
    obtain ⟨g,hg⟩ := unsafe_into_original_seed S H R F.U F.invariant (F.compatibleGroup S H R J A0 B overA0 hEJ) q (F.diagonal_mem S H R J A0 B overA0 hEJ) A hA (r.stage.model) (locallyInSource_of_faithful (sourceTag S H R F.U (F.compatibleGroup S H R J A0 B overA0 hEJ)) r.stage.inclusion r.stage.faithful) (r.certificate) safe hs hq
      r.stage.inclusion r.stage.faithful {a | a.val.down.val ∈ RealClosure.Bounds.packetClosure S H A0}
      padding X hUnsafe multiple
    refine ⟨decodedAutImage S H R F.U F.invariant (F.compatibleGroup S H R J A0 B overA0 hEJ) q (F.diagonal_mem S H R J A0 B overA0 hEJ) A hA (r.stage.model) (locallyInSource_of_faithful (sourceTag S H R F.U (F.compatibleGroup S H R J A0 B overA0 hEJ)) r.stage.inclusion r.stage.faithful) (r.certificate) g,?_⟩
    intro x hx
    obtain ⟨a,ha,he⟩ := hg x hx
    change real (g x) ∈ _
    rw [he,out.realEmbedding_source_fixed]
    exact ha

end
end CCO.RelativeMI.FineStage
