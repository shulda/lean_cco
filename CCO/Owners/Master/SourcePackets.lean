import CCO.Owners.Master.SourceStep

/-! Full ambient packet closure at every new finite induced quotient.
Both projected packets stay in their ACTUAL target packets; no exactness
of the packet, algebraic-closure identity or quotient-group lift is used. -/

universe v w t z
namespace CCO.Owners.Master
noncomputable section
open RawExact ExactCRT Provider Product

variable {A : Type v} (S : AtomicSource.{0,v,w} Unit (fun _ => A))
variable {G : Type t} [Group G] [MulAction G A] [Countable A]
variable (H : HomogeneousSource S G) (cco : SemanticCCO.{0,v,v,w} S)
variable {T : Set A} {U : Finset (Position S H cco)}
variable (B : SourceStage.{v,w,t,z} S H cco T U)
variable {p : Position S H cco} (next : Next U p)

theorem sourceStep_closed (upU : IsUpset U) (W : LocalFactor S H cco B next)
    (V : Finset (Position S H cco)) (upV : IsUpset V) (within : V ⊆ insert p U) :
    FullPacketClosed (quotientSource S H cco (coordinateKernel S H cco V))
      (quotientSource_homogeneous S H cco (coordinateKernel S H cco V))
      ((sourceStep S H cco B next upU W).stage.B V) := by
  let D := sourceStep S H cco B next upU W
  intro x hx y hxy
  by_cases hp : p ∈ V
  · have hx' := (D.mem_new_new hp (D.principal_subset upV within hp) x).mp hx
    apply (D.mem_new_new hp (D.principal_subset upV within hp) y).mpr
    constructor
    · apply B.decorations.closed (V.erase p) (next_erase_upset upU next upV within)
        (next_erase_subset within) _ hx'.1
      exact relative_packet_projection S H cco _ _
        (coordinateKernel_antitone S H cco (Finset.erase_subset p V)) x y hxy
    · apply W.closed _ hx'.2
      exact relative_packet_projection S H cco _ _
        (coordinateKernel_antitone S H cco (D.principal_subset upV within hp)) x y hxy
  · apply (D.mem_new_old hp y).mpr
    exact B.decorations.closed V upV (D.old_subset within hp) x
      ((D.mem_new_old hp x).mp hx) y hxy

end
end CCO.Owners.Master
