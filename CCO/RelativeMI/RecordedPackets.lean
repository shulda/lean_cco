import CCO.FullRows.RowCertificate
import CCO.FullRows.ZeroRowRequests
import CCO.HKNReservoir.PacketMatrices
import CCO.HKNReservoir.Requests

/-! A recorded clique means the WHOLE closed union of its actual packets
is irreducible. It need not satisfy a local-tree size budget. No safety or
selector, completion choice, EPPA premise or owner faithfulness is used. -/
universe v w t y
namespace CCO.RelativeMI
noncomputable section
open AllThoseEPPA HKNReservoir ParityHasse.Original RealHull.Geometry RealClosure.Bounds
open FinitePackets.Normalization OwnerTransversal TransversalAge FullRows
variable {M : Type v} (S : AtomicSource.{0,v,w} Unit (fun _ => M))
variable {G : Type t} [Group G] [MulAction G M] (H : HomogeneousSource S G)
variable [Countable M] [DecidableEq M] [Infinite M] (R : ResidualData S H)
variable (B : Finset (Owner S H R)) (hB : PacketInvariant S H R B)
variable (Δ : Subgroup (SourceGamma S H R B))
variable (A : Set (SourceCarrier S H R B))
variable (hA : (sourceStructure S H R B hB).IsClosed A)
variable {Z : Type y} [Finite Z]
variable (E : Structure (Signature ↥B (ResidualData.PacketGroup S H) (S.Atom () ())) Z)
variable (hLocal : LocallyInSource (sourceTag S H R B Δ) (encode (finiteSourceData S H R B hB A hA)) E)
local notation "K" => ResidualData.PacketGroup S H
local notation "I" => PacketRecovery.PacketIndex E
local notation "tag" => sourceTag S H R B Δ
local notation "D₀" => finiteSourceData S H R B hB A hA
local notation "P₀" => sourceOriginPattern S H R B hB Δ A hA E hLocal
local notation "coords" => reservoirCoordinates S H R B hB Δ A hA E hLocal

def recordedPacketSet (J : Set I) : Set Z := {x | PacketRecovery.packet E x ∈ J}

include hLocal in
theorem recordedPacketSet_closed (J : Set I) : E.IsClosed (recordedPacketSet S H R B E J) := by
  let hD := finiteSource_regularData S H R B hB A hA
  letI := PacketRecovery.action tag D₀ E hLocal hD
  let packets := PacketRecovery.packets tag D₀ E hLocal hD
  intro n F xs hxs y hy
  cases F with
  | translate k =>
    have ht : xs = (fun _ => xs 0) := funext (fun i => congrArg xs (Subsingleton.elim _ _))
    have hv : E.func (.translate k) xs = {PacketRecovery.move tag D₀ E hLocal k (xs 0)} :=
      (congrArg (E.func (.translate k)) ht).trans (PacketRecovery.func_value tag D₀ E hLocal k (xs 0))
    have he : y = PacketRecovery.move tag D₀ E hLocal k (xs 0) := by
      rw [hv] at hy
      exact hy
    subst y
    change packets.packet (k • xs 0) ∈ J
    rw [packets.invariant]
    exact hxs 0

include hLocal in
theorem same_packet_fine_complete (x y : Z) (hxy : x ≠ y)
    (hpacket : PacketRecovery.packet E x = PacketRecovery.packet E y) :
    ∃ a, E.rel (.fine a) (![x,y]) := by
  let P := E.closureAtSet x
  have hP : E.IsClosed P := E.isClosed_closureSet {x}
  let e := PacketRecovery.closureEmbedding tag D₀ E hLocal x
  have hy : y ∈ P := by
    change y ∈ E.closureAtSet x
    rw [(PacketRecovery.packet_eq E x y).mp hpacket]
    exact E.mem_closureAtSet y
  let x₀ : P := ⟨x,E.mem_closureAtSet x⟩
  let y₀ : P := ⟨y,hy⟩
  have hne : e x₀ ≠ e y₀ := fun he => hxy (congrArg Subtype.val (e.injective he))
  obtain ⟨a,ha⟩ := (finiteSource_fineData S H R B hB A hA).complete _ _ hne
  exact ⟨a,(PacketRecovery.embedding_fine tag D₀ E hP e a x₀ y₀).mpr ha⟩

theorem recorded_clique_fine_complete (J : Set I)
    (hJ : ∀ i ∈ J, ∀ j ∈ J, i ≠ j → ∃ a, (P₀).edge i j = some a)
    (x y : recordedPacketSet S H R B E J) (hxy : x ≠ y) :
    ∃ a, E.rel (.fine a) (![x.val,y.val]) := by
  by_cases hij : PacketRecovery.packet E x.val = PacketRecovery.packet E y.val
  · exact same_packet_fine_complete S H R B hB Δ A hA E hLocal x.val y.val
      (fun he => hxy (Subtype.ext he)) hij
  · let i := (coords x.val).1
    let j := (coords y.val).1
    have hi : i = PacketRecovery.packet E x.val := reservoirCoordinates_fst S H R B hB Δ A hA E hLocal x.val
    have hj : j = PacketRecovery.packet E y.val := reservoirCoordinates_fst S H R B hB Δ A hA E hLocal y.val
    have hine : i ≠ j := fun he => hij (hi.symm.trans (he.trans hj))
    obtain ⟨a,ha⟩ := hJ i (hi.symm ▸ x.property) j (hj.symm ▸ y.property) hine
    have hrel := (sourceOriginPattern_edge S H R B hB Δ A hA E hLocal i j a).mp ha
    have hne := PacketRecovery.origin_closures_distinct tag D₀ E hLocal
      (finiteSource_regularData S H R B hB A hA) hine
    obtain ⟨b,hb,_⟩ := PacketRecovery.recorded_matrix_complete tag D₀ E hLocal
      (finiteSource_regularData S H R B hB A hA) (finiteSource_fineData S H R B hB A hA)
      (sourceOrigin S H R B hB Δ A hA E hLocal i)
      (sourceOrigin S H R B hB Δ A hA E hLocal j) a hrel hne
      (coords x.val).2 (coords y.val).2
    have hx : PacketRecovery.move tag D₀ E hLocal (coords x.val).2
        (sourceOrigin S H R B hB Δ A hA E hLocal i) = x.val := (coords).symm_apply_apply x.val
    have hy : PacketRecovery.move tag D₀ E hLocal (coords y.val).2
        (sourceOrigin S H R B hB Δ A hA E hLocal j) = y.val := (coords).symm_apply_apply y.val
    exact ⟨b,hx ▸ hy ▸ hb⟩

theorem recordedPacketSet_irreducible (J : Set I)
    (hJ : ∀ i ∈ J, ∀ j ∈ J, i ≠ j → ∃ a, (P₀).edge i j = some a) :
    (E.induce (recordedPacketSet S H R B E J)
      (recordedPacketSet_closed S H R B hB Δ A hA E hLocal J)).IsIrreducible := by
  constructor
  intro d
  obtain ⟨x,hx⟩ := (Set.ne_univ_iff_exists_notMem d.left).mp d.left_proper
  obtain ⟨y,hy⟩ := (Set.ne_univ_iff_exists_notMem d.right).mp d.right_proper
  have hyl : y ∈ d.left := (show y ∈ d.left ∪ d.right from d.cover ▸ Set.mem_univ y).resolve_right hy
  have hxy : x ≠ y := fun he => hx (he ▸ hyl)
  obtain ⟨a,ha⟩ := recorded_clique_fine_complete S H R B hB Δ A hA E hLocal J hJ x y hxy
  have ha' : (E.induce (recordedPacketSet S H R B E J)
      (recordedPacketSet_closed S H R B hB Δ A hA E hLocal J)).rel (.fine a) (![x,y]) := by
    change E.rel (.fine a) (Subtype.val ∘ ![x,y])
    have ht : Subtype.val ∘ (![x,y] : Fin 2 → recordedPacketSet S H R B E J) = ![x.val,y.val] := by
      funext i
      fin_cases i <;> rfl
    rw [ht]
    exact ha
  rcases d.rel_local (.fine a) (![x,y]) ha' with hl | hr
  · exact hx (hl 0)
  · exact hy (hr 1)

end
end CCO.RelativeMI
