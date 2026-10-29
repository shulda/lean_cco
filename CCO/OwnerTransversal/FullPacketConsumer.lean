import CCO.OwnerTransversal.Consumers
import CCO.OwnerTransversal.Inflation
import CCO.OwnerTransversal.PacketCompletion

/-! A genuine full-packet consumer of actual collision completion and
actual countable recovery into the SAME internally built primitive U.
No source model, back-and-forth, SAP or EPPA provider is an input. -/
open scoped FirstOrder
open FirstOrder FirstOrder.Language
universe v w t
namespace CCO.OwnerTransversal
noncomputable section
open ParityHasse.Original RealHull.Geometry RealClosure.Bounds
open FinitePackets.Normalization
variable {M : Type v} (S : AtomicSource.{0,v,w} Unit (fun _ => M))
variable {G : Type t} [Group G] [MulAction G M] (H : HomogeneousSource S G)
variable [Countable M] [DecidableEq M] [Infinite M] (R : ResidualData S H)
variable (B : Finset (Owner S H R)) (hB : PacketInvariant S H R B)

/-- Complete a recorded full-packet diagram in the ACTUAL inflation,
retaining its entire protected source copy under the recovered isomorphism.
Every literal owner and recorded fine matrix and every t_g is retained. -/
theorem full_packets_in_primitive_inflation
    {I : Type} [Fintype I] [DecidableEq I] {P : OriginPattern S H R I}
    (f : OriginMap S H R B P) (A : Finset I)
    (hA : Set.InjOn (inflateOrigins S H R B hB f.point) {p | p.1 ∈ A}) :
    letI := Inflation.sourceStructure S H R B hB
    letI := Inflation.inflationStructure S H R B hB
    ∃ (e : Inflation.Carrier S H R B ≃[Inflation.Signature S H R B] NamedCarrier S H R B)
      (r : (I × ResidualData.PacketGroup S H) ↪ Inflation.Carrier S H R B),
      (∀ p, p.1 ∈ A → r p = e.symm (inflateOrigins S H R B hB f.point p)) ∧
      (∀ i g k, r (i,g*k) = (Inflation.action S H R B).smul g (r (i,k))) ∧
      (∀ p, ((Inflation.table S H R B hB).owner (r p)).val =
        owner S H R (inflateOrigins S H R B hB f.point p).val) ∧
      (∀ i j a, P.edge i j = some a → ∀ g k : ResidualData.PacketGroup S H,
        (Inflation.table S H R B hB).colour (r (i,g)) (r (j,k)) =
          col S (inflateOrigins S H R B hB f.point (i,g)).val
            (inflateOrigins S H R B hB f.point (j,k)).val) ∧
      ∀ s : ↥B, ∀ Q : SortEquivalence S H R B (TransversalAge.model S H R B) s,
        Q.eqv = ⊥ ∨ Q.eqv = ⊤ := by
  letI := packetNamedAction S H R B hB
  letI := Inflation.action S H R B
  letI := Inflation.sourceStructure S H R B hB
  letI := Inflation.inflationStructure S H R B hB
  obtain ⟨g,hginj,hfix,hown,hrec⟩ := OriginMap.packet_completion hB f A hA
  obtain ⟨e⟩ := Inflation.recovery S H R B hB
  have hp := PacketLanguage.embedding_preserves (Inflation.table S H R B hB)
    (Inflation.namedTable S H R B) e.toEmbedding
  let r : (I × ResidualData.PacketGroup S H) ↪ Inflation.Carrier S H R B :=
    ⟨fun p => e.symm (inflateOrigins S H R B hB g.point p),e.symm.injective.comp hginj⟩
  have he (p : I × ResidualData.PacketGroup S H) :
      e (r p) = inflateOrigins S H R B hB g.point p := e.apply_symm_apply _
  refine ⟨e,r,?_,?_,?_,?_,residual_owner_sorts_primitive S H R B⟩
  · intro p hpa
    exact congrArg e.symm (hfix p hpa)
  · intro i k l
    apply e.injective
    have ht : e ((Inflation.action S H R B).smul k (r (i,l))) =
        packetPoint S H R B hB k (e (r (i,l))) := hp.2.2 k (r (i,l))
    rw [ht,he,he]
    exact inflateOrigins_equivariant S H R B hB g.point i k l
  · intro p
    have hh := congrArg Subtype.val (hp.1 (r p))
    change owner S H R (e (r p)).val = ((Inflation.table S H R B hB).owner (r p)).val at hh
    rw [he] at hh
    exact hh.symm.trans (hown p)
  · intro i j a hij k l
    have hh := hp.2.1 (r (i,k)) (r (j,l))
    change col S (e (r (i,k))).val (e (r (j,l))).val =
      (Inflation.table S H R B hB).colour (r (i,k)) (r (j,l)) at hh
    rw [he,he] at hh
    exact hh.symm.trans (hrec i j a hij k l)

end
end CCO.OwnerTransversal
