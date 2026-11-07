import CCO.UnfilteredEP.HierarchyRawPaths
import CCO.UnfilteredEP.QuotientParentTransport
import CCO.ResetOrder.Hierarchy.Reindex

/-!
# B064 C44: actual synchronized charting of every finite proper object

The entire FULL upper-interval transport preserves ranks and unique-parent
fibres. All chart maps and their inverses are existing named terms and
therefore restrict to the SAME finite closed member. The representative
of each transition orbit is chosen once at the symbol level, independently
of the finite object or any order on its carrier.
-/

set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 250000
set_option maxHeartbeats 900000
universe u v w z
namespace CCO.UnfilteredEP
open CCO.APRamseyReadout CCO.CloneTupleGeometry CCO.ParityHasse.Original
open CCO.ResetOrder.Hierarchy
noncomputable section
variable (B : OwnerStage.{u,v,w}) (ht : B.Terminal)

namespace NamedCutPath
variable {B ht} {D E : HiddenCut B} (p : NamedCutPath B ht D E)

theorem fullEquivariant : QuotientEquivariant (cloneSource B) (cloneHomogeneous B)
    D.2.val E.2.val p.quotientEquiv :=
  quotientEquivariant_of_original (cloneSource B) (cloneHomogeneous B)
    D.2.val E.2.val p.quotientEquiv p.equivariant

include p in
/-- The rank counts ALL strict upper FULL invariant equivalences. -/
theorem rank_transport : hiddenCutRank B D = hiddenCutRank B E :=
  quotientStrictUpper_card (cloneSource B) (cloneHomogeneous B)
    D.2.val E.2.val p.quotientEquiv p.fullEquivariant

end NamedCutPath

variable {V : Type z} (C : CCO.UnarySupport.Structure (Sig B ht) V)
variable (hC : ActualAge B ht C)

/-- Parent equivalence is preserved and reflected by each actual named
quotient path, on the entire finite member. -/
theorem finite_path_parent_transport {D E : HiddenCut B}
    (p : NamedCutPath B ht D E) (x y : HiddenCutCarrier B ht C D) :
    (actualCutSystem B ht C hC).parent E
      (finitePathEquiv B ht C hC p x) (finitePathEquiv B ht C hC p y) ↔
      (actualCutSystem B ht C hC).parent D x y := by
  obtain ⟨e⟩ := hC.2
  obtain ⟨q,hq⟩ := finite_cut_point_realized B ht C e D x
  obtain ⟨r,hr⟩ := finite_cut_point_realized B ht C e D y
  have hx := finitePathValue_realization B ht C hC e p x q hq
  have hy := finitePathValue_realization B ht C hC e p y r hr
  change (actualCutSystem B ht C hC).parent E
    (finitePathValue B ht C hC p x) (finitePathValue B ht C hC p y) ↔ _
  rw [actualCutSystem_parent_realization B ht C hC e E _ _ _ _ hx hy,
    actualCutSystem_parent_realization B ht C hC e D x y q r hq hr]
  exact (quotient_parent_iff (cloneSource B) (cloneHomogeneous B)
    D.2.val E.2.val p.quotientEquiv p.fullEquivariant
    (fullMIOfNamed B D.1 D.2).property.2
    (fullMIOfNamed B E.1 E.2).property.2 q r).symm

/-- Symbol-level transition orbits do not depend on the finite carrier. -/
abbrev CutOrbit := (NamedCutPath.ambientPaths (B := B) (ht := ht)).Orbit
abbrev CutInOrbit (r : CutOrbit B ht) := (NamedCutPath.ambientPaths (B := B) (ht := ht)).InOrbit r
abbrev cutOrbitEquiv := (NamedCutPath.ambientPaths (B := B) (ht := ht)).orbitEquiv
abbrev cutRepresentative := (NamedCutPath.ambientPaths (B := B) (ht := ht)).canonicalRepresentative

def reindexedCutSystem := (actualCutSystem B ht C hC).reindex (cutOrbitEquiv B ht)

/-- Every input field of the accepted B036 hierarchical normalizer is
now discharged at the actual current source and the SAME finite object. -/
def actualCutCharting :
    Charting (reindexedCutSystem B ht C hC) (cutRepresentative B ht) where
  paths r := (finiteCutPaths B ht C hC).comap (fun j : CutInOrbit B ht r => j.val)
  chosen r j := (NamedCutPath.ambientPaths (B := B) (ht := ht)).representativePath (cutRepresentative B ht) r j
  parent_transport r := by
    intro j k p x y
    exact finite_path_parent_transport B ht C hC p x y
  rank_orbit r j :=
    (NamedCutPath.rank_transport
      ((NamedCutPath.ambientPaths (B := B) (ht := ht)).representativePath (cutRepresentative B ht) r j)).symm

end
end CCO.UnfilteredEP
