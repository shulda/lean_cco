import CCO.HKNReservoir.SourceAutomorphisms
import CCO.HKNReservoir.Certificate
import CCO.OwnerTransversal.NamedHomogeneity

/-! Final alignment is ONE actual named-owner automorphism of the
already injective completion. It changes no recorded colour or function
and fixes the entire prescribed source simultaneously. -/
universe v w t x
namespace CCO.HKNReservoir
noncomputable section
open ParityHasse.Original RealHull.Geometry RealClosure.Bounds
open FinitePackets.Normalization OwnerTransversal OwnerTransversal.TransversalAge
variable {M : Type v} (S : AtomicSource.{0,v,w} Unit (fun _ => M))
variable {G : Type t} [Group G] [MulAction G M] (H : HomogeneousSource S G)
variable [Countable M] [DecidableEq M] [Infinite M] (R : ResidualData S H)
variable (B : Finset (Owner S H R)) (hB : PacketInvariant S H R B)
variable {W : Type x} (A : Set (SourceCarrier S H R B)) [Finite A]

/-- The actual finite joint lifting theorem aligns the full protected
base. Its real colours include equality, and all B owners are fixed. -/
theorem align_source_base (j : A → W) (q : W → NamedCarrier S H R B)
    (ho : ∀ a, ownerLabel S H R B (q (j a)) = (sourceData S H R B hB).owner a.val)
    (hc : ∀ a b, col S (q (j a)).val (q (j b)).val = col S a.val.down.val b.val.down.val) :
    ∃ k : NamedAut S H R B, ∀ a : A, k.val (q (j a)) = a.val.down := by
  letI := originalQuotientAction S H R.E
  let src : A → M := fun a => (q (j a)).val
  let tgt : A → M := fun a => a.val.down.val
  let owners : ↥B → Owner S H R := Subtype.val
  have cover (a : A) : ∃ b, owners b = owner S H R (src a) ∧ owners b = owner S H R (tgt a) :=
    ⟨ownerLabel S H R B (q (j a)),rfl,congrArg Subtype.val (ho a)⟩
  obtain ⟨g,hg,howners⟩ := residual_joint_lifting S H R src tgt owners owners hc
    (fun i j => GroupActions.orbital_nonempty _ _) cover
  have hfix : ∀ b ∈ B, g • b = b := fun b hb => howners ⟨b,hb⟩
  exact ⟨restrictMotion S H R B g hfix,fun a => Subtype.ext (hg a)⟩

/-- Forward preservation of all recorded source fine atoms already gives
ALL optional source colours: equality is checked at equal inputs. -/
theorem source_base_colours_of_fine (j : A → W) (q : W → NamedCarrier S H R B)
    (hf : ∀ (a b : A) c, (sourceData S H R B hB).fine c a.val b.val →
      col S (q (j a)).val (q (j b)).val = some c) :
    ∀ a b, col S (q (j a)).val (q (j b)).val = col S a.val.down.val b.val.down.val := by
  intro a b
  by_cases hab : a = b
  · subst b
    rw [(col_none S _ _).mpr rfl,(col_none S _ _).mpr rfl]
  · obtain ⟨c,hc⟩ := source_fine_complete S H R B hB (fun he => hab (Subtype.ext he))
    exact (hf a b c hc).trans hc.symm

def alignedMap (k : NamedAut S H R B) (q : W → NamedCarrier S H R B) : W → NamedCarrier S H R B :=
  fun x => k.val (q x)

theorem alignedMap_injective (k : NamedAut S H R B) (q : W → NamedCarrier S H R B)
    (hq : Function.Injective q) : Function.Injective (alignedMap S H R B k q) := k.val.injective.comp hq

theorem alignedMap_owner (k : NamedAut S H R B) (q : W → NamedCarrier S H R B) (x : W) :
    ownerLabel S H R B (alignedMap S H R B k q x) = ownerLabel S H R B (q x) :=
  Subtype.ext (NamedAut.owner_fixed k (q x))

theorem alignedMap_colours (k : NamedAut S H R B) (q : W → NamedCarrier S H R B) (x y : W) :
    col S (alignedMap S H R B k q x).val (alignedMap S H R B k q y).val = col S (q x).val (q y).val :=
  NamedAut.colour_fixed k (q x) (q y)

theorem alignedMap_move (k : NamedAut S H R B) (q : W → NamedCarrier S H R B)
    (move : ResidualData.PacketGroup S H → W → W)
    (hq : ∀ g x, q (move g x) = packetPoint S H R B hB g (q x)) (g : ResidualData.PacketGroup S H) (x : W) :
    alignedMap S H R B k q (move g x) = packetPoint S H R B hB g (alignedMap S H R B k q x) := by
  change k.val (q (move g x)) = _
  rw [hq,namedAut_commutes S H R B hB k]
  rfl

/-- The final source alignment preserves injectivity, ALL optional fine
colours, every literal owner and every named packet function. -/
theorem align_completion (j : A → W) (q : W → NamedCarrier S H R B) (hq : Function.Injective q)
    (move : ResidualData.PacketGroup S H → W → W)
    (hm : ∀ g x, q (move g x) = packetPoint S H R B hB g (q x))
    (ho : ∀ a, ownerLabel S H R B (q (j a)) = (sourceData S H R B hB).owner a.val)
    (hc : ∀ a b, col S (q (j a)).val (q (j b)).val = col S a.val.down.val b.val.down.val) :
    ∃ k : NamedAut S H R B,
      (∀ a : A, alignedMap S H R B k q (j a) = a.val.down) ∧
      Function.Injective (alignedMap S H R B k q) ∧
      (∀ x, ownerLabel S H R B (alignedMap S H R B k q x) = ownerLabel S H R B (q x)) ∧
      (∀ x y, col S (alignedMap S H R B k q x).val (alignedMap S H R B k q y).val = col S (q x).val (q y).val) ∧
      ∀ g x, alignedMap S H R B k q (move g x) = packetPoint S H R B hB g (alignedMap S H R B k q x) := by
  obtain ⟨k,hk⟩ := align_source_base S H R B hB A j q ho hc
  exact ⟨k,hk,alignedMap_injective S H R B k q hq,alignedMap_owner S H R B k q,
    alignedMap_colours S H R B k q,alignedMap_move S H R B hB k q move hm⟩

section Certificates
open AllThoseEPPA
variable (Δ : Subgroup (SourceGamma S H R B))
variable (hA : (sourceStructure S H R B hB).IsClosed A)
variable (E : Structure (Signature ↥B (ResidualData.PacketGroup S H) (S.Atom () ())) W)
variable (hLocal : LocallyInSource (sourceTag S H R B Δ) (encode (finiteSourceData S H R B hB A hA)) E)

namespace PacketCertificate
variable {S H R B hB Δ A hA E hLocal}

/-- Postcompose a genuine completion certificate by one actual named
motion, retaining ALL structural records and exact named functions. -/
def namedMotion (c : PacketCertificate S H R B hB Δ A hA E hLocal) (k : NamedAut S H R B) :
    PacketCertificate S H R B hB Δ A hA E hLocal where
  point x := k.val (c.point x)
  injective := k.val.injective.comp c.injective
  owner x := (alignedMap_owner S H R B k c.point x).trans (c.owner x)
  move g x := by rw [c.move,namedAut_commutes S H R B hB k]
  fine a x y ha := (NamedAut.colour_fixed k (c.point x) (c.point y)).trans (c.fine a x y ha)

@[simp] theorem namedMotion_point (c : PacketCertificate S H R B hB Δ A hA E hLocal)
    (k : NamedAut S H R B) (x : W) : (c.namedMotion k).point x = k.val (c.point x) := rfl
end PacketCertificate

/-- The distinguished source was globally normalized FIRST. Its exact
embedding and the actual certificate now discharge all finite-base
hypotheses, giving a certificate that fixes A pointwise. -/
theorem align_source_certificate (c : PacketCertificate S H R B hB Δ A hA E hLocal)
    (j : Structure.Embedding (sourceAction S H R B Δ) (encode (finiteSourceData S H R B hB A hA)) E)
    (hl : j.lang = 1) :
    ∃ k : NamedAut S H R B, ∀ a : A, (c.namedMotion k).point (j a) = a.val.down := by
  have ho (a : A) : ownerLabel S H R B (c.point (j a)) = (sourceData S H R B hB).owner a.val := by
    let b := (finiteSourceData S H R B hB A hA).owner a
    have hr : E.rel (.owner b) (fun _ => j a) := by
      have h := embedding_owner_iff (sourceTag S H R B Δ) j b a
      rw [hl,map_one,Equiv.Perm.one_apply] at h
      exact h.mpr rfl
    exact (c.owner (j a)).trans ((PacketRecovery.owner_iff (sourceTag S H R B Δ)
      (finiteSourceData S H R B hB A hA) E hLocal (j a) b).mp hr)
  have hc := source_base_colours_of_fine S H R B hB A j.toFun c.point (by
    intro a b d hd
    exact c.fine d (j a) (j b) ((embedding_fine_iff (sourceTag S H R B Δ) j d a b).mpr hd))
  exact align_source_base S H R B hB A j.toFun c.point ho hc
end Certificates

end
end CCO.HKNReservoir
