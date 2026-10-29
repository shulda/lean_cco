import CCO.OwnerTransversal.ClosedSAP

/-! Actual closed strong amalgamation with the ENTIRE left realization
fixed literally. The right motion is one named automorphism, and the
intersection remains exactly the displayed complete closed span. -/
universe v w t
namespace CCO.HKNReservoir.Actual
noncomputable section
open ParityHasse.Original RealHull.Geometry RealClosure.Bounds OwnerTransversal
variable {M : Type v} (S : AtomicSource.{0,v,w} Unit (fun _ => M))
variable {G : Type t} [Group G] [MulAction G M] (H : HomogeneousSource S G)
variable [Countable M] [DecidableEq M] [Infinite M] (R : ResidualData S H)
variable (B : Finset (Owner S H R))

/-- C07 support: closed SAP, followed by inverse alignment of its WHOLE
left image, permits tree attachment without changing any old colour. -/
theorem closed_span_fix_left
    (C L P : Finset (NamedCarrier S H R B))
    (hC : PacketClosed S H R B C) (hL : PacketClosed S H R B L)
    (hP : PacketClosed S H R B P)
    (e : NamedEmbedding S H R B C L) (d : NamedEmbedding S H R B C P) :
    ∃ k : NamedAut S H R B,
      (∀ c, k.val (d.toEmbedding c).val = (e.toEmbedding c).val) ∧
      (∀ (l : ↥L) (p : ↥P), l.val = k.val p.val ↔
        ∃ c, e.toEmbedding c = l ∧ d.toEmbedding c = p) := by
  obtain ⟨D,_,i,j,hbase,hoverlap⟩ := closed_strong_amalgamation S H R B C L P hC hL hP e d
  obtain ⟨a,ha⟩ := named_embedding_extends S H R B L D i
  obtain ⟨b,hb⟩ := named_embedding_extends S H R B P D j
  let k : NamedAut S H R B := a⁻¹ * b
  have hk (p : ↥P) : a.val (k.val p.val) = (j.toEmbedding p).val := by
    change a.val (a.val.symm (b.val p.val)) = _
    exact (a.val.apply_symm_apply _).trans (hb p)
  have hcomm (c : ↥C) : k.val (d.toEmbedding c).val = (e.toEmbedding c).val := by
    apply a.val.injective
    rw [hk,ha]
    exact (congrArg Subtype.val (hbase c)).symm
  refine ⟨k,hcomm,?_⟩
  intro l p
  constructor
  · intro he
    have hh : i.toEmbedding l = j.toEmbedding p := by
      apply Subtype.ext
      exact (ha l).symm.trans ((congrArg a.val he).trans (hk p))
    exact (hoverlap l p).mp hh
  · rintro ⟨c,rfl,rfl⟩
    exact (hcomm c).symm

end
end CCO.HKNReservoir.Actual
