import CCO.OwnerTransversal.OriginRepair
import CCO.OwnerTransversal.PacketImages
import CCO.OwnerTransversal.PacketCoordinates
import CCO.OwnerTransversal.PacketCharts

/-! Actual packet-record collision repair and origin inflation.  Finite
coordinates index whole regular packets, retain every named function and
record the COMPLETE fine matrix on each specified pair of packets. -/
universe v w t z
namespace CCO.OwnerTransversal
noncomputable section
open ParityHasse.Original RealHull.Geometry RealClosure.Bounds
open FinitePackets.Normalization
variable {M : Type v} (S : AtomicSource.{0,v,w} Unit (fun _ => M))
variable {G : Type t} [Group G] [MulAction G M] (H : HomogeneousSource S G)
variable [Countable M] [DecidableEq M] (R : ResidualData S H)
variable (B : Finset (Owner S H R)) (hB : PacketInvariant S H R B)

/-- C28: fix a WHOLE closed neighbour image and move the WHOLE colliding
packet by one actual named automorphism. Unrecorded targets need not be
fixed. The caller updates only this one formal packet. -/
theorem repair_whole_packet [Infinite M]
    (C Z : Finset (NamedCarrier S H R B)) (hC : PacketClosed S H R B C)
    (x : NamedCarrier S H R B) (hx : x ∉ C) :
    ∃ f : NamedAut S H R B, (∀ c ∈ C, f.val c = c) ∧
      ∀ e : ResidualData.PacketGroup S H, ∀ z ∈ Z,
        f.val (packetPoint S H R B hB e x) ≠ z := by
  classical
  let A := namedPacketFinset S H R B {x}
  obtain ⟨f,hfix,havoid⟩ := finite_closed_avoidance S H R B C A Z hC
  refine ⟨f,hfix,?_⟩
  intro e z hz
  have hF := translation_in_packet S (finitePacket S H) G e x.val
  have hmem : packetPoint S H R B hB e x ∈ A := by
    apply (mem_namedPacketFinset S H R B {x} _).mpr
    exact ⟨x.val,Finset.mem_image.mpr ⟨x,Finset.mem_singleton_self _,rfl⟩,hF⟩
  have hnot : packetPoint S H R B hB e x ∉ C := by
    intro h
    exact hx (hC _ h x ((finitePacket S H).val.symm hF))
  exact havoid _ hmem hnot z hz

theorem translation_owner_eq (e : ResidualData.PacketGroup S H)
    {x y : NamedCarrier S H R B} (hxy : owner S H R x.val = owner S H R y.val) :
    owner S H R (packetPoint S H R B hB e x).val =
      owner S H R (packetPoint S H R B hB e y).val := by
  apply Quotient.sound
  apply (R.E.property x.val y.val (e.val x.val) (e.val y.val)
    (translation_preserves_colour S (finitePacket S H) H (R.packet_thin S H) e _ _).symm).mp
  exact Quotient.exact hxy

def inflateOrigins {I : Type z} (f : I → NamedCarrier S H R B)
    (p : I × ResidualData.PacketGroup S H) : NamedCarrier S H R B :=
  packetPoint S H R B hB p.2 (f p.1)

theorem inflateOrigins_equivariant {I : Type z} (f : I → NamedCarrier S H R B)
    (i : I) (e g : ResidualData.PacketGroup S H) :
    inflateOrigins S H R B hB f (i,e*g) =
      packetPoint S H R B hB e (inflateOrigins S H R B hB f (i,g)) :=
  packetPoint_mul S H R B hB e g (f i)

theorem inflateOrigins_injective {I : Type z} (f : I → NamedCarrier S H R B)
    (hs : ∀ i j, i ≠ j → ¬ finitePacket S H (f i).val (f j).val) :
    Function.Injective (inflateOrigins S H R B hB f) := by
  rintro ⟨i,e⟩ ⟨j,g⟩ heq
  have hF : finitePacket S H (f i).val (f j).val := by
    have he := translation_in_packet S (finitePacket S H) G e (f i).val
    have hg := translation_in_packet S (finitePacket S H) G g (f j).val
    have hval := congrArg Subtype.val heq
    change e.val (f i).val = g.val (f j).val at hval
    rw [hval] at he
    exact (finitePacket S H).val.trans he ((finitePacket S H).val.symm hg)
  have hij : i = j := by by_contra hne; exact hs i j hne hF
  subst j
  have heg : e = g := by
    apply (packetTranslationEquiv S (finitePacket S H) H (R.packet_thin S H) (f i).val).injective
    apply Subtype.ext
    change e.val (f i).val = g.val (f i).val
    exact congrArg (fun z : NamedCarrier S H R B => z.val) heq
  exact Prod.ext rfl heg

namespace OriginMap
variable {S H R B} {I : Type z} [Fintype I] [DecidableEq I]
variable {P : OriginPattern S H R I}

omit [Fintype I] [DecidableEq I] in
theorem inflated_owners (f g : OriginMap S H R B P)
    (p : I × ResidualData.PacketGroup S H) :
    CCO.OwnerTransversal.owner S H R (inflateOrigins S H R B hB f.point p).val =
      CCO.OwnerTransversal.owner S H R (inflateOrigins S H R B hB g.point p).val := by
  apply translation_owner_eq S H R B hB p.2
  exact (f.owner p.1).trans (g.owner p.1).symm

omit [Fintype I] [DecidableEq I] in
/-- Every displayed off-packet record retains its ENTIRE fine matrix,
including colours changed by independent endpoint translations. -/
theorem inflated_records (f g : OriginMap S H R B P)
    (i j : I) (a : Atom S) (hij : P.edge i j = some a)
    (e k : ResidualData.PacketGroup S H) :
    col S (inflateOrigins S H R B hB f.point (i,e)).val
      (inflateOrigins S H R B hB f.point (j,k)).val =
    col S (inflateOrigins S H R B hB g.point (i,e)).val
      (inflateOrigins S H R B hB g.point (j,k)).val := by
  change col S (e.val (f.point i).val) (k.val (f.point j).val) =
    col S (e.val (g.point i).val) (k.val (g.point j).val)
  rw [two_endpoint_transport S (finitePacket S H) H (R.packet_thin S H),
    two_endpoint_transport S (finitePacket S H) H (R.packet_thin S H),
    f.edge i j a hij,g.edge i j a hij]

omit [Fintype I] [DecidableEq I] in
/-- Internal fine colours also agree, including equal coordinates. -/
theorem inflated_internal (f g : OriginMap S H R B P)
    (i : I) (e k : ResidualData.PacketGroup S H) :
    col S (inflateOrigins S H R B hB f.point (i,e)).val
      (inflateOrigins S H R B hB f.point (i,k)).val =
    col S (inflateOrigins S H R B hB g.point (i,e)).val
      (inflateOrigins S H R B hB g.point (i,k)).val := by
  change col S (e.val (f.point i).val) (k.val (f.point i).val) =
    col S (e.val (g.point i).val) (k.val (g.point i).val)
  rw [two_endpoint_transport S (finitePacket S H) H (R.packet_thin S H),
    two_endpoint_transport S (finitePacket S H) H (R.packet_thin S H),
    (col_none S _ _).mpr rfl,(col_none S _ _).mpr rfl]

/-- C29–30: descent on the actual origin map gives a globally injective
completion on all full packets, fixes the whole protected packet base,
and retains owners, every t_g, and every displayed complete matrix. -/
theorem packet_completion [Infinite M] (f : OriginMap S H R B P)
    (A : Finset I)
    (hinj : Set.InjOn (inflateOrigins S H R B hB f.point) {p | p.1 ∈ A}) :
    ∃ g : OriginMap S H R B P,
      Function.Injective (inflateOrigins S H R B hB g.point) ∧
      (∀ p : I × ResidualData.PacketGroup S H, p.1 ∈ A →
        inflateOrigins S H R B hB g.point p = inflateOrigins S H R B hB f.point p) ∧
      (∀ p : I × ResidualData.PacketGroup S H,
        CCO.OwnerTransversal.owner S H R (inflateOrigins S H R B hB g.point p).val =
        CCO.OwnerTransversal.owner S H R (inflateOrigins S H R B hB f.point p).val) ∧
      ∀ i j a, P.edge i j = some a → ∀ e k : ResidualData.PacketGroup S H,
        col S (inflateOrigins S H R B hB g.point (i,e)).val
          (inflateOrigins S H R B hB g.point (j,k)).val =
        col S (inflateOrigins S H R B hB f.point (i,e)).val
          (inflateOrigins S H R B hB f.point (j,k)).val := by
  have hs := protected_origins_separated S H R B hB
    (inflateOrigins S H R B hB f.point) (inflateOrigins_equivariant S H R B hB f.point)
    (A : Set I) hinj
  simp only [inflateOrigins,packetPoint_one] at hs
  obtain ⟨g,hg,hsep⟩ := OriginMap.separate f A hs
  refine ⟨g,inflateOrigins_injective S H R B hB g.point hsep,?_,
    inflated_owners hB g f,?_⟩
  · rintro ⟨i,e⟩ hi
    change packetPoint S H R B hB e (g.point i) = packetPoint S H R B hB e (f.point i)
    rw [hg i hi]
  · intro i j a hij e k
    exact inflated_records hB g f i j a hij e k

end OriginMap

/-- C29 on an arbitrary literal regular-packet carrier.  The origins
and the coordinate chart are constructed by `RegularPackets`, so a
product representation is not an extra completion/provider assumption. -/
theorem packet_completion_on_regular_carrier [Infinite M]
    {I : Type} [Fintype I] [DecidableEq I] {X : Type*}
    [MulAction (ResidualData.PacketGroup S H) X]
    (D : PacketCoordinates.RegularPackets
      (K := ResidualData.PacketGroup S H) (P := X) (I := I))
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
      ∀ i j a, P.edge i j = some a → ∀ e k : ResidualData.PacketGroup S H,
        col S (q' (e • D.origin i)).val (q' (k • D.origin j)).val =
          col S (q (e • D.origin i)).val (q (k • D.origin j)).val := by
  let f : OriginMap S H R B P := ⟨fun i => q (D.origin i),howner,hrecords⟩
  have hcoord (p : I × ResidualData.PacketGroup S H) :
      inflateOrigins S H R B hB f.point p = q (D.coordinates.symm p) := by
    rcases p with ⟨i,e⟩
    exact (commutes e (D.origin i)).symm
  have hinflate : Set.InjOn (inflateOrigins S H R B hB f.point) {p | p.1 ∈ A} := by
    intro p hp r hr hpr
    apply D.coordinates.symm.injective
    apply hinj
    · change D.packet (D.coordinates.symm p) ∈ A
      rw [← D.coordinates_fst (D.coordinates.symm p),Equiv.apply_symm_apply]
      exact hp
    · change D.packet (D.coordinates.symm r) ∈ A
      rw [← D.coordinates_fst (D.coordinates.symm r),Equiv.apply_symm_apply]
      exact hr
    · exact (hcoord p).symm.trans (hpr.trans (hcoord r))
  obtain ⟨g,hg,hfix,hown,hrec⟩ := OriginMap.packet_completion hB f A hinflate
  let q' : X → NamedCarrier S H R B := fun x => inflateOrigins S H R B hB g.point (D.coordinates x)
  have old (x : X) : inflateOrigins S H R B hB f.point (D.coordinates x) = q x := by
    rw [hcoord,Equiv.symm_apply_apply]
  refine ⟨q',hg.comp D.coordinates.injective,?_,?_,?_,?_⟩
  · intro e x
    change inflateOrigins S H R B hB g.point (D.coordinates (e • x)) = _
    rw [D.coordinates_action]
    exact inflateOrigins_equivariant S H R B hB g.point _ _ _
  · intro x hx
    exact (hfix (D.coordinates x) ((D.coordinates_fst x).symm ▸ hx)).trans (old x)
  · intro x
    exact (hown (D.coordinates x)).trans (congrArg (fun y : NamedCarrier S H R B => owner S H R y.val) (old x))
  · intro i j a hij e k
    have he : D.coordinates (e • D.origin i) = (i,e) := by
      exact D.coordinates.apply_symm_apply (i,e)
    have hk : D.coordinates (k • D.origin j) = (j,k) := by
      exact D.coordinates.apply_symm_apply (j,k)
    change col S (inflateOrigins S H R B hB g.point (D.coordinates (e • D.origin i))).val
      (inflateOrigins S H R B hB g.point (D.coordinates (k • D.origin j))).val = _
    rw [he,hk]
    exact (hrec i j a hij e k).trans (congrArg₂ (fun x y : NamedCarrier S H R B => col S x.val y.val)
      (hcoord (i,e)) (hcoord (j,k)))
end
end CCO.OwnerTransversal
