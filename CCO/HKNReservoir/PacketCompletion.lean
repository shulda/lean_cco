import CCO.OwnerTransversal.PacketCompletion

/-! Universe-polymorphic realization on the SAME formal full-packet carrier.
The accepted origin-separation theorem supplies the collision repair;
no independent origins or packet completion provider is assumed. -/
universe v w t z x
namespace CCO.HKNReservoir
noncomputable section
open ParityHasse.Original RealHull.Geometry RealClosure.Bounds
open FinitePackets.Normalization OwnerTransversal
variable {M : Type v} (S : AtomicSource.{0,v,w} Unit (fun _ => M))
variable {G : Type t} [Group G] [MulAction G M] (H : HomogeneousSource S G)
variable [Countable M] [DecidableEq M] [Infinite M] (R : ResidualData S H)
variable (B : Finset (Owner S H R)) (hB : PacketInvariant S H R B)

/-- C18–C19: the entire protected union of packets stays fixed, every
recorded chord retains its FULL matrix, and every named function is exact. -/
theorem protected_packet_completion
    {I : Type z} [Fintype I] [DecidableEq I] {X : Type x}
    [MulAction (ResidualData.PacketGroup S H) X]
    (D : PacketCoordinates.RegularPackets (K := ResidualData.PacketGroup S H) (P := X) (I := I))
    (P : OriginPattern S H R I) (q : X → NamedCarrier S H R B)
    (commutes : ∀ e x, q (e • x) = packetPoint S H R B hB e (q x))
    (howner : ∀ i, owner S H R (q (D.origin i)).val = P.owner i)
    (hrecords : ∀ i j a, P.edge i j = some a →
      col S (q (D.origin i)).val (q (D.origin j)).val = some a)
    (A : Finset I) (hinj : Set.InjOn q {x | D.packet x ∈ A}) :
    ∃ q' : X → NamedCarrier S H R B, Function.Injective q' ∧
      (∀ e x, q' (e • x) = packetPoint S H R B hB e (q' x)) ∧
      (∀ x, D.packet x ∈ A → q' x = q x) ∧
      (∀ x, owner S H R (q' x).val = owner S H R (q x).val) ∧
      (∀ (i : I) (e k : ResidualData.PacketGroup S H), col S (q' (e • D.origin i)).val (q' (k • D.origin i)).val =
        col S (q (e • D.origin i)).val (q (k • D.origin i)).val) ∧
      ∀ i j a, P.edge i j = some a → ∀ e k : ResidualData.PacketGroup S H,
        col S (q' (e • D.origin i)).val (q' (k • D.origin j)).val =
          col S (q (e • D.origin i)).val (q (k • D.origin j)).val := by
  let f : OriginMap S H R B P := ⟨fun i => q (D.origin i),howner,hrecords⟩
  have hc (p : I × ResidualData.PacketGroup S H) :
      inflateOrigins S H R B hB f.point p = q (D.coordinates.symm p) := by
    rcases p with ⟨i,e⟩
    exact (commutes e (D.origin i)).symm
  have hi : Set.InjOn (inflateOrigins S H R B hB f.point) {p | p.1 ∈ A} := by
    intro p hp r hr he
    apply D.coordinates.symm.injective
    apply hinj
    · change D.packet (D.coordinates.symm p) ∈ A
      rw [← D.coordinates_fst (D.coordinates.symm p),Equiv.apply_symm_apply]
      exact hp
    · change D.packet (D.coordinates.symm r) ∈ A
      rw [← D.coordinates_fst (D.coordinates.symm r),Equiv.apply_symm_apply]
      exact hr
    · exact (hc p).symm.trans (he.trans (hc r))
  obtain ⟨g,hg,hfix,hown,hrec⟩ := OriginMap.packet_completion hB f A hi
  let q' : X → NamedCarrier S H R B := fun x => inflateOrigins S H R B hB g.point (D.coordinates x)
  have old (x : X) : inflateOrigins S H R B hB f.point (D.coordinates x) = q x := by
    rw [hc,Equiv.symm_apply_apply]
  have hco (i : I) (e : ResidualData.PacketGroup S H) : D.coordinates (e • D.origin i) = (i,e) :=
    D.coordinates.apply_symm_apply (i,e)
  refine ⟨q',hg.comp D.coordinates.injective,?_,?_,?_,?_,?_⟩
  · intro e x
    change inflateOrigins S H R B hB g.point (D.coordinates (e • x)) = _
    rw [D.coordinates_action]
    exact inflateOrigins_equivariant S H R B hB g.point _ _ _
  · intro x hx
    exact (hfix (D.coordinates x) ((D.coordinates_fst x).symm ▸ hx)).trans (old x)
  · intro x
    exact (hown (D.coordinates x)).trans (congrArg (fun y : NamedCarrier S H R B => owner S H R y.val) (old x))
  · intro i e k
    change col S (inflateOrigins S H R B hB g.point (D.coordinates (e • D.origin i))).val
      (inflateOrigins S H R B hB g.point (D.coordinates (k • D.origin i))).val = _
    rw [hco,hco]
    exact (OriginMap.inflated_internal hB g f i e k).trans
      (congrArg₂ (fun x y : NamedCarrier S H R B => col S x.val y.val) (hc (i,e)) (hc (i,k)))
  · intro i j a hij e k
    change col S (inflateOrigins S H R B hB g.point (D.coordinates (e • D.origin i))).val
      (inflateOrigins S H R B hB g.point (D.coordinates (k • D.origin j))).val = _
    rw [hco,hco]
    exact (hrec i j a hij e k).trans
      (congrArg₂ (fun x y : NamedCarrier S H R B => col S x.val y.val) (hc (i,e)) (hc (j,k)))
end
end CCO.HKNReservoir
