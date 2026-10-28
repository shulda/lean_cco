import CCO.RealClosure.Bounds.Packet
import CCO.RealHull.Geometry.Supports

/-! Literal OLD diversity atoms outside the greatest finite ORIGINAL packet.
The packet is not assumed exact. Shared counting data for CRT and acl. -/
universe v w t
namespace CCO.RealClosure.Bounds
open ParityHasse.Original RealHull.Geometry
variable {M : Type v} (S : AtomicSource.{0,v,w} Unit (fun _ => M))
variable {G : Type t} [Group G] [MulAction G M] (H : HomogeneousSource S G)
abbrev OutsideAtom := {p : Atom S // p ∉ diversitySupport S (finitePacket S H)}
noncomputable def outsideAtomCount : ℕ := Nat.card (OutsideAtom S H)
end CCO.RealClosure.Bounds
