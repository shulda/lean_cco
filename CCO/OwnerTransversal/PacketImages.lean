import CCO.OwnerTransversal.NamedSource

/-! A whole formal packet maps ONTO an actual real F-class under commuting
packet functions. Hence packet images are equal or disjoint, and literal
point injectivity on protected whole packets implies separated origins.
Owner-label stabilizers may be nontrivial throughout. -/

universe v w t z
namespace CCO.OwnerTransversal
noncomputable section
open ParityHasse.Original RealHull.Geometry RealClosure.Bounds
open FinitePackets.Geometry FinitePackets.Normalization AclOwners

variable {M : Type v} (S : AtomicSource.{0,v,w} Unit (fun _ => M))
variable {G : Type t} [Group G] [MulAction G M] (H : HomogeneousSource S G)
variable [Countable M] [DecidableEq M] (R : ResidualData S H)
variable (B : Finset (Owner S H R)) (hB : PacketInvariant S H R B)

theorem packetPoint_one (x : NamedCarrier S H R B) :
    packetPoint S H R B hB 1 x = x := Subtype.ext rfl

theorem packetPoint_mul (e f : ResidualData.PacketGroup S H)
    (x : NamedCarrier S H R B) :
    packetPoint S H R B hB (e * f) x =
      packetPoint S H R B hB e (packetPoint S H R B hB f x) := Subtype.ext rfl

theorem packetPoint_injective (e : ResidualData.PacketGroup S H) :
    Function.Injective (packetPoint S H R B hB e) := by
  intro x y he
  exact Subtype.ext (e.val.injective (congrArg Subtype.val he))

/-- C27: the range is the ENTIRE actual finite packet, not just its owner. -/
theorem packetPoint_range (x : NamedCarrier S H R B) :
    Set.range (fun e : ResidualData.PacketGroup S H => packetPoint S H R B hB e x) =
      {y : NamedCarrier S H R B | finitePacket S H x.val y.val} := by
  ext y
  constructor
  · rintro ⟨e,rfl⟩
    exact translation_in_packet S (finitePacket S H) G e x.val
  · intro hxy
    obtain ⟨e,he,_⟩ := translation_regular S (finitePacket S H) H
      (R.packet_thin S H) x.val y.val hxy
    exact ⟨e,Subtype.ext he⟩

theorem packetPoint_range_eq {x y : NamedCarrier S H R B}
    (hxy : finitePacket S H x.val y.val) :
    Set.range (fun e : ResidualData.PacketGroup S H => packetPoint S H R B hB e x) =
      Set.range (fun e : ResidualData.PacketGroup S H => packetPoint S H R B hB e y) := by
  rw [packetPoint_range,packetPoint_range]
  ext z
  exact ⟨fun hxz => (finitePacket S H).val.trans ((finitePacket S H).val.symm hxy) hxz,
    fun hyz => (finitePacket S H).val.trans hxy hyz⟩

theorem packetPoint_ranges_disjoint_or_eq (x y : NamedCarrier S H R B) :
    Disjoint
      (Set.range (fun e : ResidualData.PacketGroup S H => packetPoint S H R B hB e x))
      (Set.range (fun e : ResidualData.PacketGroup S H => packetPoint S H R B hB e y)) ∨
    Set.range (fun e : ResidualData.PacketGroup S H => packetPoint S H R B hB e x) =
      Set.range (fun e : ResidualData.PacketGroup S H => packetPoint S H R B hB e y) := by
  by_cases hxy : finitePacket S H x.val y.val
  · exact Or.inr (packetPoint_range_eq S H R B hB hxy)
  · left
    rw [packetPoint_range,packetPoint_range]
    apply Set.disjoint_left.mpr
    intro z hxz hyz
    exact hxy ((finitePacket S H).val.trans hxz ((finitePacket S H).val.symm hyz))

theorem commutingPacket_range
    (q : ResidualData.PacketGroup S H → NamedCarrier S H R B)
    (commutes : ∀ e, q e = packetPoint S H R B hB e (q 1)) :
    Set.range q = {y : NamedCarrier S H R B | finitePacket S H (q 1).val y.val} := by
  have hq : q = fun e => packetPoint S H R B hB e (q 1) := funext commutes
  rw [hq,packetPoint_range]
  simp only [packetPoint_one]

variable {I : Type z}

theorem protected_origins_separated
    (q : I × ResidualData.PacketGroup S H → NamedCarrier S H R B)
    (commutes : ∀ i e f, q (i,e * f) = packetPoint S H R B hB e (q (i,f)))
    (A : Set I) (injective : Set.InjOn q {p | p.1 ∈ A}) :
    ∀ i ∈ A, ∀ j ∈ A, i ≠ j →
      ¬ finitePacket S H (q (i,1)).val (q (j,1)).val := by
  intro i hi j hj hij hF
  obtain ⟨e,he,_⟩ := translation_regular S (finitePacket S H) H
    (R.packet_thin S H) (q (i,1)).val (q (j,1)).val hF
  have hpoints : q (i,e) = q (j,1) := by
    have hq := commutes i e 1
    rw [mul_one] at hq
    exact hq.trans (Subtype.ext he)
  have hpairs : (i,e) = (j,1) := injective hi hj hpoints
  exact hij (congrArg Prod.fst hpairs)

end
end CCO.OwnerTransversal
