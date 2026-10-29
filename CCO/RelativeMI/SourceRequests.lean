import CCO.RelativeMI.SourceContext
import CCO.HKNReservoir.RequestSaturation

/-! C32: ORIGINAL partial requests with their ENTIRE prescribed fine-owner
component become genuine HKN requests on the fixed finite padded source.
No closed-domain or nonempty-carrier assumption is added. -/
universe v w t z
namespace CCO.RelativeMI
noncomputable section
open ParityHasse.Original RealHull.Geometry RealClosure.Bounds
open FinitePackets.Normalization OwnerTransversal AclOwners HKNReservoir
open Owners.Product Owners.Provider

private def imageMap {I : Type*} {V : Type*} (a b : I → V) (x : V) : V :=
  by classical exact if h : ∃ i, a i = x then b h.choose else x

private theorem imageMap_apply {I : Type*} {V : Type*} (a b : I → V)
    (ha : Function.Injective a) (i : I) : imageMap a b (a i) = b i := by
  have h : ∃ j, a j = a i := ⟨i, rfl⟩
  rw [imageMap, dite_eq_left h]
  exact congrArg b (ha h.choose_spec)

/-- The fallback is the input itself, so empty I AND empty V are allowed. -/
private def partialBetween {I : Type*} {V : Type*} (a b : I → V)
    (ha : Function.Injective a) (hb : Function.Injective b) : PartialEquiv V V where
  toFun := imageMap a b
  invFun := imageMap b a
  source := Set.range a
  target := Set.range b
  map_source' := by
    rintro x ⟨i, rfl⟩
    exact ⟨i, (imageMap_apply a b ha i).symm⟩
  map_target' := by
    rintro x ⟨i, rfl⟩
    exact ⟨i, (imageMap_apply b a hb i).symm⟩
  left_inv' := by
    rintro x ⟨i, rfl⟩
    rw [imageMap_apply a b ha, imageMap_apply b a hb]
  right_inv' := by
    rintro x ⟨i, rfl⟩
    rw [imageMap_apply b a hb, imageMap_apply a b ha]

variable {M : Type v} (S : AtomicSource.{0,v,w} Unit (fun _ => M))
variable {G : Type t} [Group G] [MulAction G M] (H : HomogeneousSource S G)
variable [Countable M] [DecidableEq M] [Infinite M] (R : ResidualData S H)
variable (J : ColourEq S ()) (A0 : Finset M) (B : Finset (Coarse S H J))
variable (overA0 : ∀ x : ↥A0, coarseOwner S H J x.val ∈ B) (hEJ : R.E ≤ J)
local instance sourceRequestsFineAction : MulAction G (Owner S H R) := originalQuotientAction S H R.E
local instance sourceRequestsCoarseAction : MulAction G (Coarse S H J) := originalQuotientAction S H J

namespace FineStage
variable (F : FineStage S H R J A0 B overA0 hEJ)
variable (Aplus : Set (SourceCarrier S H R F.U))
variable (hAplus : (sourceStructure S H R F.U F.invariant).IsClosed Aplus)
variable (oldContains : ∀ x ∈ RealClosure.Bounds.packetClosure S H A0,
  ∃ a : Aplus, a.val.down.val = x)
include oldContains

omit [Infinite M] in
/-- The caller supplies literal old-point containment from its ACTUAL
padding construction; no extension theorem is a new input. -/
theorem request_of_selected (r : OriginalRequest S H J A0 B overA0)
    (δ : F.compatibleGroup S H R J A0 B overA0 hEJ)
    (hδ : ∀ x : r.part.domain,
      (δ.val.val ⟨owner S H R x.val.val,
        F.contains x.val.val ⟨x.val.val,x.val.property,(finitePacket S H).val.refl _⟩⟩).val =
          owner S H R (r.part.map x).val) :
    ∃ p : HKNReservoir.Request (sourceTag S H R F.U
        (F.compatibleGroup S H R J A0 B overA0 hEJ))
        (finiteSourceData S H R F.U F.invariant Aplus hAplus),
      p.lang = δ ∧ ∀ x : r.part.domain,
        ∃ a : Aplus, a.val.down.val = x.val.val ∧ a ∈ p.point.source ∧
          (p.point a).val.down.val = (r.part.map x).val := by
  classical
  let old : ↥A0 → Aplus := fun x =>
    (oldContains x.val ⟨x.val,x.property,(finitePacket S H).val.refl _⟩).choose
  have old_real (x : ↥A0) : (old x).val.down.val = x.val :=
    (oldContains x.val ⟨x.val,x.property,(finitePacket S H).val.refl _⟩).choose_spec
  let src : r.part.domain → Aplus := fun x => old x.val
  let tgt : r.part.domain → Aplus := fun x => old (r.part.map x)
  have hs : Function.Injective src := by
    intro x y h
    apply Subtype.ext
    apply Subtype.ext
    simpa only [src, old_real] using congrArg (fun a : Aplus => a.val.down.val) h
  have ht : Function.Injective tgt := by
    intro x y h
    apply r.part.injective
    apply Subtype.ext
    simpa only [tgt, old_real] using congrArg (fun a : Aplus => a.val.down.val) h
  let e := partialBetween src tgt hs ht
  have he (x : r.part.domain) : e (src x) = tgt x := imageMap_apply src tgt hs x
  have howner (x : r.part.domain) :
      (finiteSourceData S H R F.U F.invariant Aplus hAplus).owner (tgt x) =
        sourceTag S H R F.U (F.compatibleGroup S H R J A0 B overA0 hEJ) δ
          ((finiteSourceData S H R F.U F.invariant Aplus hAplus).owner (src x)) := by
    apply Subtype.ext
    change owner S H R (tgt x).val.down.val =
      (δ.val.val ⟨owner S H R (src x).val.down.val,(src x).val.down.property⟩).val
    simpa only [src, tgt, old_real] using (hδ x).symm
  have hcolour (x y : r.part.domain) :
      col S (tgt x).val.down.val (tgt y).val.down.val =
        col S (src x).val.down.val (src y).val.down.val := by
    obtain ⟨g, hgx, hgy⟩ := r.part.pair x y
    have hc := col_invariant S H g x.val.val y.val.val
    rw [hgx, hgy] at hc
    simpa only [src, tgt, old_real] using hc
  let p : HKNReservoir.Request (sourceTag S H R F.U
      (F.compatibleGroup S H R J A0 B overA0 hEJ))
      (finiteSourceData S H R F.U F.invariant Aplus hAplus) := {
    lang := δ
    point := e
    owner := by
      rintro a ⟨x, rfl⟩
      rw [he]
      exact howner x
    fine := by
      rintro a u v ⟨x, rfl⟩ ⟨y, rfl⟩
      change col S (e (src x)).val.down.val (e (src y)).val.down.val = some a ↔
        col S (src x).val.down.val (src y).val.down.val = some a
      rw [he, he, hcolour] }
  refine ⟨p, rfl, ?_⟩
  intro x
  exact ⟨src x, old_real x.val, ⟨x, rfl⟩, by change (e (src x)).val.down.val = _; rw [he]; exact old_real _⟩

omit [Infinite M] in
/-- Every original request, including empty and singleton real domains,
retains its EXACT prescribed coarse permutation on ALL B. -/
theorem source_request (r : OriginalRequest S H J A0 B overA0) :
    ∃ p : HKNReservoir.Request (sourceTag S H R F.U
        (F.compatibleGroup S H R J A0 B overA0 hEJ))
        (finiteSourceData S H R F.U F.invariant Aplus hAplus),
      F.coarseHom S H R J A0 B overA0 hEJ p.lang = r.owner ∧
      ∀ x : r.part.domain, ∃ a : Aplus, a.val.down.val = x.val.val ∧
        a ∈ p.point.source ∧ (p.point a).val.down.val = (r.part.map x).val := by
  obtain ⟨δ, hcoarse, hδ⟩ := F.prescribed S H R J A0 B overA0 hEJ r
  obtain ⟨p, hp, hreal⟩ := F.request_of_selected S H R J A0 B overA0 hEJ Aplus hAplus oldContains r δ hδ
  exact ⟨p, hp ▸ hcoarse, hreal⟩

/-- The accepted actual source provider realizes the finite request by
ONE joint real/ENTIRE-U lift, before functional saturation. -/
theorem source_request_ambient [Finite Aplus] (r : OriginalRequest S H J A0 B overA0) :
    ∃ p : HKNReservoir.Request (sourceTag S H R F.U
        (F.compatibleGroup S H R J A0 B overA0 hEJ))
        (finiteSourceData S H R F.U F.invariant Aplus hAplus),
      F.coarseHom S H R J A0 B overA0 hEJ p.lang = r.owner ∧
      (∀ x : r.part.domain, ∃ a : Aplus, a.val.down.val = x.val.val ∧
        a ∈ p.point.source ∧ (p.point a).val.down.val = (r.part.map x).val) ∧
      ∃ σ : ExactAut (sourceTag S H R F.U
          (F.compatibleGroup S H R J A0 B overA0 hEJ)) (sourceData S H R F.U F.invariant),
        σ.lang = p.lang ∧ ∀ x ∈ p.point.source, σ.perm x.val = (p.point x).val := by
  obtain ⟨p, hc, hr⟩ := F.source_request S H R J A0 B overA0 hEJ Aplus hAplus oldContains r
  obtain ⟨σ, hl, hm⟩ := HKNReservoir.request_ambient S H R F.U F.invariant
    (F.compatibleGroup S H R J A0 B overA0 hEJ) Aplus hAplus p
  exact ⟨p, hc, hr, σ, hl, hm⟩

/-- Functional saturation gives an ACTUAL full-packet partial automorphism
on the SAME finite Aplus with the SAME entire prescribed component.
All original values and every named thin translate are retained. -/
theorem source_request_full_packets [Finite Aplus]
    (r : OriginalRequest S H J A0 B overA0) :
    ∃ q : AllThoseEPPA.Structure.PartialAutomorphism
        (sourceAction S H R F.U (F.compatibleGroup S H R J A0 B overA0 hEJ))
        (encode (finiteSourceData S H R F.U F.invariant Aplus hAplus)),
      F.coarseHom S H R J A0 B overA0 hEJ q.lang = r.owner ∧
      ∀ x : r.part.domain, ∃ a : Aplus, a.val.down.val = x.val.val ∧
        a ∈ q.source ∧ (q a).val.down.val = (r.part.map x).val ∧
        ∀ k : ResidualData.PacketGroup S H,
          (finiteSourceData S H R F.U F.invariant Aplus hAplus).move k a ∈ q.source ∧
          q ((finiteSourceData S H R F.U F.invariant Aplus hAplus).move k a) =
            (finiteSourceData S H R F.U F.invariant Aplus hAplus).move k (q a) := by
  obtain ⟨p, hc, hr⟩ := F.source_request S H R J A0 B overA0 hEJ Aplus hAplus oldContains r
  obtain ⟨q, hl, hs, _ht, hmatch, hmove⟩ := HKNReservoir.saturate_request S H R F.U F.invariant
    (F.compatibleGroup S H R J A0 B overA0 hEJ) Aplus hAplus p
  have h1 (a : Aplus) :
      (finiteSourceData S H R F.U F.invariant Aplus hAplus).move 1 a = a :=
    Subtype.ext (source_move_one S H R F.U F.invariant a.val)
  refine ⟨q, hl ▸ hc, ?_⟩
  intro x
  obtain ⟨a, ha, hsrc, hval⟩ := hr x
  have hqa : a ∈ q.source := hs ▸ subset_saturation _ h1 _ hsrc
  refine ⟨a, ha, hqa, ?_, ?_⟩
  · rw [hmatch a hsrc]
    exact hval
  · intro k
    refine ⟨hs ▸ ⟨k, a, hsrc, rfl⟩, ?_⟩
    rw [hmove k a hsrc, hmatch a hsrc]

end FineStage
end
end CCO.RelativeMI
