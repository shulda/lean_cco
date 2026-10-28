import CCO.RealClosure.Bounds.Singleton
import CCO.RealClosure.Bounds.PaletteCost
import CCO.RealClosure.Bounds.SmallClosures

/-! Source-facing real closure exports with all providers discharged.
Finite ambient sources have r=0 and constant whole-source closure; the
infinite-source polynomial branch is kept separate. -/
universe v w t
namespace CCO.RealClosure.Bounds
open ParityHasse.Original RealHull.Geometry RealHull.Canonical
variable {M : Type v} (S : AtomicSource.{0,v,w} Unit (fun _ => M)) [DecidableEq M]
variable {G : Type t} [Group G] [MulAction G M] (H : HomogeneousSource S G)

theorem directionCount_zero_of_finite [Finite M] : directionCount S = 0 := by
  letI : IsEmpty (Direction S) := ⟨fun D => D.property.1
    (finiteClasses_of_le S le_top ((finiteClasses_top_iff S).mpr inferInstance))⟩
  exact Nat.card_of_isEmpty

theorem finitePacket_top_of_finite [Finite M] : finitePacket S H = ⊤ :=
  le_antisymm le_top (le_finitePacket S H ⊤ ((finiteClasses_top_iff S).mpr inferInstance))

theorem packetSize_finite_source [Finite M] : packetSize S H = Nat.card M := by
  rw [packetSize,finitePacket_top_of_finite S H]
  exact Nat.card_congr (Equiv.Set.univ M)

/-- All finite-source bases, including empty, have the same whole-source
closure and a constant finite bound. This is not the infinite r>=1 branch. -/
theorem finite_source_closure_bound [Finite M] (A : Finset M) :
    Acl G A = Set.univ ∧ directionCount S = 0 ∧
      Nat.card (Acl G A) = packetSize S H := by
  refine ⟨acl_finite_source A,directionCount_zero_of_finite S,?_⟩
  rw [acl_finite_source,packetSize_finite_source S H]
  exact Nat.card_congr (Equiv.Set.univ M)

/-- A source consumer simultaneously exposes the independent palette cost,
bounded real character, singleton packets, finite-fibre bounds and dcl case.
No abstract lattice, class-Helly or finite-packet provider is left as input. -/
theorem real_closure_source_core (cco : SemanticCCO.{0,v,0,w} S) (A : Finset M) :
    (2^(directionCount S) - 1 ≤ outsideAtomCount S H) ∧
    (directionCount S ≤ Nat.log 2 (outsideAtomCount S H + 1)) ∧
    (Acl G A = ⋃ (B : Finset M) (_ : B ⊆ A) (_ : B.card ≤ directionCount S), Acl G B) ∧
    (∀ a : M, Acl G {a} = {x | finitePacket S H a x}) ∧
    (packetSize S H ≤ 2^(internalAtomCount S H)) ∧
    (∀ x y : M, x ∈ Acl G A → finitePacket S H x y → y ∈ Acl G A) ∧
    (finitePacket S H = ⊥ → Acl G A = Dcl G A) :=
  ⟨direction_palette_bound S H cco,direction_log_bound S H cco,
    acl_bounded_union S H cco A,acl_singleton S H cco,packet_size_le_power S H cco,
    fun _ _ hx hxy => acl_packet_saturated S H A hx hxy,
    fun hF => acl_eq_dcl_of_packet_identity S H cco hF A⟩
end CCO.RealClosure.Bounds
