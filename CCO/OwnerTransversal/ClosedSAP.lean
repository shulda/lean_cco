import CCO.OwnerTransversal.NamedHomogeneity
import CCO.OwnerTransversal.ClosedAvoidance

/-! Strong amalgamation of arbitrary finite PACKET-closed named induced
spans.  Alignment and one simultaneous avoidance move are both actual
named automorphisms.  Original real-age SAP is never assumed. -/

universe v w t
namespace CCO.OwnerTransversal
noncomputable section
open ParityHasse.Original RealHull.Geometry RealClosure.Bounds

variable {M : Type v} (S : AtomicSource.{0,v,w} Unit (fun _ => M))
variable {G : Type t} [Group G] [MulAction G M] (H : HomogeneousSource S G)
variable [Countable M] [DecidableEq M] (R : ResidualData S H)
variable (B : Finset (Owner S H R))

def NamedEmbedding.ofAut (A L : Finset (NamedCarrier S H R B))
    (f : NamedAut S H R B) (hf : ∀ a ∈ A, f.val a ∈ L) : NamedEmbedding S H R B A L where
  toEmbedding := {
    toFun a := ⟨f.val a.val,hf a.val a.property⟩
    inj' := fun _ _ h => Subtype.ext (f.val.injective (congrArg Subtype.val h)) }
  owner a := NamedAut.owner_fixed f a.val
  colours a b := NamedAut.colour_fixed f a.val b.val

/-- C26: literal disjointness outside the displayed common closed span,
including arbitrary non-inclusion input embeddings and the empty base. -/
theorem closed_strong_amalgamation [Infinite M]
    (C L P : Finset (NamedCarrier S H R B))
    (hC : PacketClosed S H R B C) (hL : PacketClosed S H R B L)
    (hP : PacketClosed S H R B P)
    (e : NamedEmbedding S H R B C L) (d : NamedEmbedding S H R B C P) :
    ∃ (D : Finset (NamedCarrier S H R B)), PacketClosed S H R B D ∧
      ∃ (i : NamedEmbedding S H R B L D) (j : NamedEmbedding S H R B P D),
        (∀ c, i.toEmbedding (e.toEmbedding c) = j.toEmbedding (d.toEmbedding c)) ∧
        (∀ l p, i.toEmbedding l = j.toEmbedding p ↔
          ∃ c, e.toEmbedding c = l ∧ d.toEmbedding c = p) := by
  classical
  obtain ⟨a,ha⟩ := named_embedding_extends S H R B C L e
  obtain ⟨b,hb⟩ := named_embedding_extends S H R B C P d
  let C₀ := C.image a.val
  let k : NamedAut S H R B := a * b⁻¹
  let P₀ := P.image k.val
  have hC₀ : PacketClosed S H R B C₀ := packetClosed_image S H R B C hC a
  obtain ⟨f,hfix,hdis⟩ := closed_disjoint_copy S H R B C₀ P₀ L hC₀
  let g : NamedAut S H R B := f * k
  have hcomm (c : ↥C) : g.val (d.toEmbedding c).val = (e.toEmbedding c).val := by
    change f.val (a.val (b.val.symm (d.toEmbedding c).val)) = _
    rw [← hb c,Equiv.symm_apply_apply]
    rw [hfix (a.val c.val) (Finset.mem_image.mpr ⟨c.val,c.property,rfl⟩),ha c]
  let D := L ∪ P.image g.val
  have hD : PacketClosed S H R B D := packetClosed_union S H R B L _ hL
    (packetClosed_image S H R B P hP g)
  let i : NamedEmbedding S H R B L D := NamedEmbedding.ofAut S H R B L D 1
    (fun l hl => Finset.mem_union_left _ hl)
  let j : NamedEmbedding S H R B P D := NamedEmbedding.ofAut S H R B P D g
    (fun p hp => Finset.mem_union_right _ (Finset.mem_image.mpr ⟨p,hp,rfl⟩))
  refine ⟨D,hD,i,j,?_,?_⟩
  · intro c
    apply Subtype.ext
    exact (hcomm c).symm
  · intro l p
    constructor
    · intro he
      have hlg : l.val = g.val p.val := congrArg Subtype.val he
      have hlC : l.val ∈ C₀ := hdis (k.val p.val)
        (Finset.mem_image.mpr ⟨p.val,p.property,rfl⟩) l.val l.property hlg.symm
      obtain ⟨c,hc,hcl⟩ := Finset.mem_image.mp hlC
      let c' : ↥C := ⟨c,hc⟩
      have hel : e.toEmbedding c' = l := Subtype.ext ((ha c').symm.trans hcl)
      have hdp : d.toEmbedding c' = p := by
        apply Subtype.ext
        apply g.val.injective
        exact (hcomm c').trans ((congrArg Subtype.val hel).trans hlg)
      exact ⟨c',hel,hdp⟩
    · rintro ⟨c,rfl,rfl⟩
      apply Subtype.ext
      exact (hcomm c).symm

end
end CCO.OwnerTransversal
