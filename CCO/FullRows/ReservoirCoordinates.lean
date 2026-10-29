import CCO.HKNReservoir.Reservoir

/-! Actual structural coordinates of the accepted completable reservoir.
Offsets are read from REAL packet images; no owner action is made free. -/
universe v w t y
namespace CCO.FullRows
noncomputable section
open AllThoseEPPA HKNReservoir ParityHasse.Original RealHull.Geometry RealClosure.Bounds
open FinitePackets.Normalization OwnerTransversal TransversalAge
variable {M : Type v} (S : AtomicSource.{0,v,w} Unit (fun _ => M))
variable {G : Type t} [Group G] [MulAction G M] (H : HomogeneousSource S G)
variable [Countable M] [DecidableEq M] [Infinite M] (R : ResidualData S H)
variable (B : Finset (Owner S H R)) (hB : PacketInvariant S H R B)
variable (Δ : Subgroup (SourceGamma S H R B))
variable (A : Set (SourceCarrier S H R B))
variable (hA : (sourceStructure S H R B hB).IsClosed A)
variable {Z : Type y}
variable (E : Structure (Signature ↥B (ResidualData.PacketGroup S H) (S.Atom () ())) Z)
variable (hLocal : LocallyInSource (sourceTag S H R B Δ) (encode (finiteSourceData S H R B hB A hA)) E)
set_option quotPrecheck false
local notation "tag" => sourceTag S H R B Δ
local notation "D₀" => finiteSourceData S H R B hB A hA
local notation "act" => sourceAction S H R B Δ
local notation "move" => PacketRecovery.move tag D₀ E hLocal
local notation "own" => PacketRecovery.owner tag D₀ E hLocal

/-- Every real vertex is coordinatized by ONE actual structural packet
index and its unique real thin phase. -/
def reservoirCoordinates : Z ≃ PacketRecovery.PacketIndex E × ResidualData.PacketGroup S H := by
  letI := PacketRecovery.action tag D₀ E hLocal (finiteSource_regularData S H R B hB A hA)
  exact (PacketRecovery.packets tag D₀ E hLocal (finiteSource_regularData S H R B hB A hA)).coordinates

theorem reservoirCoordinates_move (g : ResidualData.PacketGroup S H) (x : Z) :
    reservoirCoordinates S H R B hB Δ A hA E hLocal (move g x) =
      ((reservoirCoordinates S H R B hB Δ A hA E hLocal x).1,
        g*(reservoirCoordinates S H R B hB Δ A hA E hLocal x).2) := by
  letI := PacketRecovery.action tag D₀ E hLocal (finiteSource_regularData S H R B hB A hA)
  exact (PacketRecovery.packets tag D₀ E hLocal (finiteSource_regularData S H R B hB A hA)).coordinates_action g x

theorem reservoirCoordinates_symm (i : PacketRecovery.PacketIndex E) (g : ResidualData.PacketGroup S H) :
    (reservoirCoordinates S H R B hB Δ A hA E hLocal).symm (i,g) =
      move g (sourceOrigin S H R B hB Δ A hA E hLocal i) := rfl

theorem reservoirAutomorphism_move
    (s : Structure.Automorphism act E) (g : ResidualData.PacketGroup S H) (x : Z) :
    s (move g x) = move g (s x) := by
  have hh := (automorphismEmbedding tag s).map_func (.translate g) (fun _ => x)
  rw [PacketRecovery.func_value tag D₀ E hLocal] at hh
  change s '' {move g x} = E.func (.translate g) (fun _ => s x) at hh
  rw [Set.image_singleton,PacketRecovery.func_value tag D₀ E hLocal] at hh
  exact Set.singleton_injective hh

theorem reservoirAutomorphism_owner (s : Structure.Automorphism act E) (x : Z) :
    own (s x) = tag s.lang (own x) := by
  have hh := ((automorphismEmbedding tag s).map_rel_iff (.owner (own x)) (fun _ => x)).mpr
    ((PacketRecovery.owner_iff tag D₀ E hLocal x _).mpr rfl)
  exact (PacketRecovery.owner_iff tag D₀ E hLocal (s x) _).mp hh

/-- Conjugate the ACTUAL structural automorphism by the real coordinate
chart; the next purely finite row theorem extracts its sigma and offsets. -/
def reservoirCoordinateEquiv (s : Structure.Automorphism act E) :
    Equiv.Perm (PacketRecovery.PacketIndex E × ResidualData.PacketGroup S H) :=
  (reservoirCoordinates S H R B hB Δ A hA E hLocal).symm.trans
    ((automorphismPerm tag s).trans (reservoirCoordinates S H R B hB Δ A hA E hLocal))

theorem reservoirCoordinateEquiv_move (s : Structure.Automorphism act E)
    (g : ResidualData.PacketGroup S H)
    (p : PacketRecovery.PacketIndex E × ResidualData.PacketGroup S H) :
    reservoirCoordinateEquiv S H R B hB Δ A hA E hLocal s (p.1,g*p.2) =
      ((reservoirCoordinateEquiv S H R B hB Δ A hA E hLocal s p).1,
        g*(reservoirCoordinateEquiv S H R B hB Δ A hA E hLocal s p).2) := by
  let c := reservoirCoordinates S H R B hB Δ A hA E hLocal
  have hs : c.symm (p.1,g*p.2) = move g (c.symm p) := by
    apply c.injective
    rw [c.apply_symm_apply,reservoirCoordinates_move,c.apply_symm_apply]
  change c (s (c.symm (p.1,g*p.2))) = _
  rw [hs,reservoirAutomorphism_move,reservoirCoordinates_move]
  rfl
end
end CCO.FullRows
