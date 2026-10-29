import CCO.SafeReadings.TransversalGauge
import CCO.SafeReadings.TransversalCCO

universe v w t
namespace CCO.SafeReadings.TransversalGauge
noncomputable section
open ParityHasse.Original RealHull.Geometry RealClosure.Bounds
open FinitePackets.Normalization OwnerTransversal TransversalAge TransversalSource
variable {M : Type v} (S : AtomicSource.{0,v,w} Unit (fun _ => M))
variable {G : Type t} [Group G] [MulAction G M] (H : HomogeneousSource S G)
variable [Countable M] [DecidableEq M] [Infinite M] (R : ResidualData S H)
include R

/-- This is actual translation of the FIRST original real vertex,
with all displayed literal old colours; no action on U is postulated. -/
theorem original_triangle_left (g : ResidualData.PacketGroup S H)
    (a b c a' c' : S.Atom () ())
    (ha : (some a' : FullColour S) = switchColour S (finitePacket S H) g (some a))
    (hc : (some c' : FullColour S) = switchColour S (finitePacket S H) g (some c)) :
    S.Triangle a b c ↔ S.Triangle a' b c' := by
  constructor
  · rintro ⟨x,y,z,hxy,hyz,hxz⟩
    change col S x y = _ at hxy
    change col S y z = _ at hyz
    change col S x z = _ at hxz
    refine ⟨g.val x,y,z,?_,hyz,?_⟩
    · exact (switchColour_left S (finitePacket S H) H g x y).trans
        ((congrArg (switchColour S (finitePacket S H) g) hxy).trans ha.symm)
    · exact (switchColour_left S (finitePacket S H) H g x z).trans
        ((congrArg (switchColour S (finitePacket S H) g) hxz).trans hc.symm)
  · rintro ⟨x,y,z,hxy,hyz,hxz⟩
    change col S x y = _ at hxy
    change col S y z = _ at hyz
    change col S x z = _ at hxz
    refine ⟨g.val x,y,z,?_,hyz,?_⟩
    · change col S (g.val x) y = some a
      rw [switchColour_left S (finitePacket S H) H g x y,hxy,ha,
        switchColour_involutive S (finitePacket S H) H (R.packet_thin S H)]
    · change col S (g.val x) z = some c
      rw [switchColour_left S (finitePacket S H) H g x z,hxz,hc,
        switchColour_involutive S (finitePacket S H) H (R.packet_thin S H)]

/-- Actual translation of the LAST original real vertex. -/
theorem original_triangle_right (g : ResidualData.PacketGroup S H)
    (a b c b' c' : S.Atom () ())
    (hb : (some b' : FullColour S) = switchColour S (finitePacket S H) g (some b))
    (hc : (some c' : FullColour S) = switchColour S (finitePacket S H) g (some c)) :
    S.Triangle a b c ↔ S.Triangle a b' c' := by
  constructor
  · rintro ⟨x,y,z,hxy,hyz,hxz⟩
    change col S x y = _ at hxy
    change col S y z = _ at hyz
    change col S x z = _ at hxz
    refine ⟨x,y,g.val z,hxy,?_,?_⟩
    · exact (switchColour_right S (finitePacket S H) H g y z).trans
        ((congrArg (switchColour S (finitePacket S H) g) hyz).trans hb.symm)
    · exact (switchColour_right S (finitePacket S H) H g x z).trans
        ((congrArg (switchColour S (finitePacket S H) g) hxz).trans hc.symm)
  · rintro ⟨x,y,z,hxy,hyz,hxz⟩
    change col S x y = _ at hxy
    change col S y z = _ at hyz
    change col S x z = _ at hxz
    refine ⟨x,y,g.val z,hxy,?_,?_⟩
    · change col S y (g.val z) = some b
      rw [switchColour_right S (finitePacket S H) H g y z,hyz,hb,
        switchColour_involutive S (finitePacket S H) H (R.packet_thin S H)]
    · change col S x (g.val z) = some c
      rw [switchColour_right S (finitePacket S H) H g x z,hxz,hc,
        switchColour_involutive S (finitePacket S H) H (R.packet_thin S H)]

variable (B : Finset (Owner S H R)) (hB : PacketInvariant S H R B)

/-- Actual one-endpoint transport of the U triangle table. -/
theorem triangle_left (g : ResidualData.PacketGroup S H) {i j k : ↥B}
    (a : (source S H R B).Atom i j) (b : (source S H R B).Atom j k) (c : (source S H R B).Atom i k) :
    (source S H R B).Triangle a b c ↔
      (source S H R B).Triangle (leftEquiv S H R B hB g i j a) b (leftEquiv S H R B hB g i k c) :=
  (source_triangle_iff_original S H R B a b c).trans
    ((original_triangle_left S H R g a.val b.val c.val _ _
      (leftEquiv_label S H R B hB g a) (leftEquiv_label S H R B hB g c)).trans
      (source_triangle_iff_original S H R B _ _ _).symm)

theorem triangle_right (g : ResidualData.PacketGroup S H) {i j k : ↥B}
    (a : (source S H R B).Atom i j) (b : (source S H R B).Atom j k) (c : (source S H R B).Atom i k) :
    (source S H R B).Triangle a b c ↔
      (source S H R B).Triangle a (rightEquiv S H R B hB g j k b) (rightEquiv S H R B hB g i k c) :=
  (source_triangle_iff_original S H R B a b c).trans
    ((original_triangle_right S H R g a.val b.val c.val _ _
      (rightEquiv_label S H R B hB g b) (rightEquiv_label S H R B hB g c)).trans
      (source_triangle_iff_original S H R B _ _ _).symm)

end
end CCO.SafeReadings.TransversalGauge
