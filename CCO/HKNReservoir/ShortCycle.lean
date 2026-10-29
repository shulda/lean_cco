import CCO.HKNReservoir.SourcePacketOrigins
import CCO.HKNReservoir.SourceOriginDiagram
import CCO.HKNReservoir.ActualPacketCompletion
import CCO.HKNReservoir.TypedOrigins
import CCO.HKNReservoir.PacketCardinality
import CCO.HKNReservoir.LocalTreeReadout
import CCO.HKNReservoir.DistinguishedNormalization
import CCO.HKNReservoir.Requests
import CCO.OwnerTransversal.TransversalExtension

/-! C19: short origin cycles use the FULL induced union of their packets.
The local HKN budget counts actual vertices, including every unary translate;
all recorded chords of that whole closed support remain available. -/
universe v w t
namespace CCO.HKNReservoir
noncomputable section
open AllThoseEPPA ParityHasse.Original RealHull.Geometry RealClosure.Bounds
open FinitePackets.Normalization OwnerTransversal TransversalAge
variable {M : Type v} (S : AtomicSource.{0,v,w} Unit (fun _ => M))
variable {G : Type t} [Group G] [MulAction G M] (H : HomogeneousSource S G)
variable [Countable M] [DecidableEq M] [Infinite M] (R : ResidualData S H)
variable (B : Finset (Owner S H R)) (hB : PacketInvariant S H R B)
variable (Δ : Subgroup (SourceGamma S H R B))
set_option quotPrecheck false
local notation "L" => Signature ↥B (ResidualData.PacketGroup S H) (S.Atom () ())
local notation "act" => sourceAction S H R B Δ
local notation "N" => sourceStructure S H R B hB
variable (A : Set (SourceCarrier S H R B))
variable (hA : (sourceStructure S H R B hB).IsClosed A)
variable {Z : Type (max v w)}
variable (E : Structure (Signature ↥B (ResidualData.PacketGroup S H) (S.Atom () ())) Z)
variable (hLocal : LocallyInSource (sourceTag S H R B Δ)
  (encode (finiteSourceData S H R B hB A hA)) E)

def sourcePacketSupport (J : Finset (PacketRecovery.PacketIndex E)) : Set Z :=
  {x | PacketRecovery.packet E x ∈ J}

include hLocal in
theorem sourcePacketSupport_closed (J : Finset (PacketRecovery.PacketIndex E)) :
    E.IsClosed (sourcePacketSupport S H R B E J) := by
  let tag := sourceTag S H R B Δ
  let D := finiteSourceData S H R B hB A hA
  let hD := finiteSource_regularData S H R B hB A hA
  let := PacketRecovery.action tag D E hLocal hD
  let packets := PacketRecovery.packets tag D E hLocal hD
  intro n F xs hxs y hy
  cases F with
  | translate k =>
    have ht : xs = (fun _ => xs 0) := funext (fun i => congrArg xs (Subsingleton.elim _ _))
    have hv : E.func (.translate k) xs = {PacketRecovery.move tag D E hLocal k (xs 0)} :=
      (congrArg (E.func (.translate k)) ht).trans (PacketRecovery.func_value tag D E hLocal k (xs 0))
    have he : y = PacketRecovery.move tag D E hLocal k (xs 0) := by
      rw [hv] at hy
      exact hy
    subst y
    change packets.packet (k • xs 0) ∈ J
    rw [packets.invariant]
    exact hxs 0

include hLocal in
theorem sourcePacketSupport_finite (J : Finset (PacketRecovery.PacketIndex E)) :
    (sourcePacketSupport S H R B E J).Finite := by
  let tag := sourceTag S H R B Δ
  let D := finiteSourceData S H R B hB A hA
  let hD := finiteSource_regularData S H R B hB A hA
  let := PacketRecovery.action tag D E hLocal hD
  let : Finite (ResidualData.PacketGroup S H) := translation_finite S (finitePacket S H) H (R.packet_thin S H)
  exact finite_fullPacketUnion (PacketRecovery.packets tag D E hLocal hD) J

include hLocal in
theorem sourcePacketSupport_card (J : Finset (PacketRecovery.PacketIndex E)) :
    (sourcePacketSupport S H R B E J).ncard = J.card * Nat.card (ResidualData.PacketGroup S H) := by
  let tag := sourceTag S H R B Δ
  let D := finiteSourceData S H R B hB A hA
  let hD := finiteSource_regularData S H R B hB A hA
  let := PacketRecovery.action tag D E hLocal hD
  let : Finite (ResidualData.PacketGroup S H) := translation_finite S (finitePacket S H) H (R.packet_thin S H)
  exact card_fullPacketUnion (PacketRecovery.packets tag D E hLocal hD) J

/-- Local HKN trees are requested on the WHOLE induced support. Their
realization preserves all records, including every chord between its origins. -/
theorem sourcePacketSupport_local_map [Finite A] (b : Nat)
    (trees : DistinguishedNormalization.LocalTrees act
      (encode (finiteSourceData S H R B hB A hA)) E
      (b * Nat.card (ResidualData.PacketGroup S H)))
    (J : Finset (PacketRecovery.PacketIndex E)) (hJ : J.card ≤ b) :
    ∃ q : Structure.Homomorphism act
      (E.induce (sourcePacketSupport S H R B E J)
        (sourcePacketSupport_closed S H R B hB Δ A hA E hLocal J)) N,
      q.lang = 1 ∧ Structure.Homomorphism.IsHomomorphismEmbedding act q := by
  let P := sourcePacketSupport S H R B E J
  have hP : E.IsClosed P := sourcePacketSupport_closed S H R B hB Δ A hA E hLocal J
  have hsize : P.ncard ≤ b * Nat.card (ResidualData.PacketGroup S H) := by
    rw [sourcePacketSupport_card S H R B hB Δ A hA E hLocal J]
    exact Nat.mul_le_mul_right _ hJ
  obtain ⟨W,D,⟨T⟩,f,hf⟩ := trees P hP hsize
  let a : Structure.Embedding act (encode (finiteSourceData S H R B hB A hA)) N := by
    rw [finiteSourceStructure]
    exact (N).inclusion act A hA
  exact local_tree_readout S H R B hB Δ _
    (finiteSource_irreducible S H R B hB A hA) a T f hf

/-- A local bound on k WHOLE packets yields actual separated U-origins,
retaining EVERY fine record of their full induced support, including chords. -/
theorem full_packet_origin_completion [Finite A] (b : Nat)
    (trees : DistinguishedNormalization.LocalTrees act
      (encode (finiteSourceData S H R B hB A hA)) E
      (b * Nat.card (ResidualData.PacketGroup S H)))
    (J : Finset (PacketRecovery.PacketIndex E)) (hJ : J.card ≤ b) :
    ∃ u : ↥J ↪ U S H R B,
      (∀ i, (limitTable S H R B).owner (u i) =
        sourceOriginOwner S H R B hB Δ A hA E hLocal i.val) ∧
      ∀ i j a, E.rel (.fine a)
        (![sourceOrigin S H R B hB Δ A hA E hLocal i.val,
          sourceOrigin S H R B hB Δ A hA E hLocal j.val]) →
        (limitTable S H R B).colour (u i) (u j) = some a := by
  classical
  let tag := sourceTag S H R B Δ
  let D₀ := finiteSourceData S H R B hB A hA
  let hD := finiteSource_regularData S H R B hB A hA
  let P := sourcePacketSupport S H R B E J
  have hP : E.IsClosed P := sourcePacketSupport_closed S H R B hB Δ A hA E hLocal J
  let E₀ := E.induce P hP
  let h₀ : LocallyInSource tag (encode D₀) E₀ :=
    TreeLike.everyIrreducibleEmbedsIn_induced act (encode D₀) E hLocal P hP
  let : Finite P := sourcePacketSupport_finite S H R B hB Δ A hA E hLocal J
  obtain ⟨q,hq,_⟩ := sourcePacketSupport_local_map S H R B hB Δ A hA E hLocal b trees J hJ
  obtain ⟨q',hinj,hm,_,ho,hfine⟩ := actual_protected_packet_completion S H R B hB Δ A hA
    E₀ h₀ q hq ∅ (by simp)
  let o (i : ↥J) : P := ⟨sourceOrigin S H R B hB Δ A hA E hLocal i.val,by
    change PacketRecovery.packet E (PacketRecovery.origin tag D₀ E hLocal hD i.val) ∈ J
    rw [PacketRecovery.packet_origin]
    exact i.property⟩
  have hop (i : ↥J) : PacketRecovery.packet E (o i).val = i.val :=
    PacketRecovery.packet_origin tag D₀ E hLocal hD i.val
  have hown (i : ↥J) : ownerLabel S H R B (q' (o i)) =
      sourceOriginOwner S H R B hB Δ A hA E hLocal i.val := by
    apply (ho (o i)).trans
    apply (PacketRecovery.owner_iff tag D₀ E₀ h₀ (o i) _).mp
    change E.rel (.owner (PacketRecovery.owner tag D₀ E hLocal (o i).val)) (fun _ => (o i).val)
    exact (PacketRecovery.owner_iff tag D₀ E hLocal (o i).val _).mpr rfl
  have hsep : ∀ i j : ↥J, i ≠ j → ¬finitePacket S H (q' (o i)).val (q' (o j)).val := by
    intro i j hij hF
    obtain ⟨g,hg,_⟩ := translation_regular S (finitePacket S H) H (R.packet_thin S H)
      (q' (o i)).val (q' (o j)).val hF
    have he : q' (PacketRecovery.move tag D₀ E₀ h₀ g (o i)) = q' (o j) :=
      (hm g (o i)).trans (Subtype.ext hg)
    have hp := congrArg (fun x : P => PacketRecovery.packet E x.val) (hinj he)
    rw [PacketRecovery.induced_move tag D₀ E hLocal P hP h₀] at hp
    let := PacketRecovery.action tag D₀ E hLocal hD
    have hpi := (PacketRecovery.packets tag D₀ E hLocal hD).invariant g (o i).val
    change PacketRecovery.packet E (PacketRecovery.move tag D₀ E hLocal g (o i).val) =
      PacketRecovery.packet E (o i).val at hpi
    rw [hpi,hop,hop] at hp
    exact hij (Subtype.ext hp)
  obtain ⟨u,hu,hc⟩ := embed_origins S H R B (fun i : ↥J => q' (o i)) hsep
  refine ⟨u,fun i => (hu i).trans (hown i),?_⟩
  intro i j a ha
  apply (hc i j).trans
  apply hfine (o i) (o j) a
  change E.rel (.fine a) (Subtype.val ∘ ![o i,o j])
  have he : (Subtype.val ∘ ![o i,o j]) =
      ![sourceOrigin S H R B hB Δ A hA E hLocal i.val,
        sourceOrigin S H R B hB Δ A hA E hLocal j.val] := by
    funext p
    fin_cases p <;> rfl
  exact he.symm ▸ ha

/-- Every short simple cycle of the ACTUAL typed origin diagram has an
actual homomorphism into the internally constructed U source. -/
theorem short_origin_cycle [Finite A] [Finite Z] (b : Nat)
    (trees : DistinguishedNormalization.LocalTrees act
      (encode (finiteSourceData S H R B hB A hA)) E
      (b * Nat.card (ResidualData.PacketGroup S H)))
    (C : SimpleCycle (sourceOriginDiagram S H R B hB Δ A hA E hLocal))
    (hC : C.length ≤ b) : CycleHom C := by
  classical
  let J : Finset (PacketRecovery.PacketIndex E) := Finset.univ.image C.vertices
  have hJ : J.card ≤ b := (Finset.card_image_le.trans (by simp)).trans hC
  let index (p : Fin C.length) : ↥J := ⟨C.vertices p,Finset.mem_image.mpr ⟨p,Finset.mem_univ _,rfl⟩⟩
  obtain ⟨u,ho,hc⟩ := full_packet_origin_completion S H R B hB Δ A hA E hLocal b trees J hJ
  let point (p : Fin C.length) : SafeReadings.TransversalSource.Carrier S H R B
      (sourceOriginOwner S H R B hB Δ A hA E hLocal (C.vertices p)) :=
    ⟨u (index p),ho (index p)⟩
  refine ⟨point,?_⟩
  intro p a ha
  apply (SafeReadings.TransversalSource.colour_some_iff S H R B _ _ a).mpr
  exact hc (index p) (index (cyclicNext C.length_pos p)) a.val
    ((sourceOriginDiagram_edge S H R B hB Δ A hA E hLocal _ _ (C.next_ne p) a).mp ha)

end
end CCO.HKNReservoir
