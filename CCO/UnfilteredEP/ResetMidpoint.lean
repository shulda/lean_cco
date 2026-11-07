import CCO.UnfilteredEP.TerminalReset
import CCO.TerminalLattice.OriginalQuotientResetSquare

/-! C52-C55: a prescribed actual quotient pair in one parent fibre has
a reset midpoint in that SAME actual source. The complete reset menu may
contain many real fine atoms. This alone does not yet claim freshness
over a larger hidden member or an ordered midpoint amalgamation. -/

universe u v w
namespace CCO.UnfilteredEP
open CCO.APRamseyReadout CCO.CloneTupleGeometry CCO.ParityHasse.Original
open CCO.TerminalLattice
noncomputable section
variable (B : OwnerStage.{u,v,w}) (ht : B.Terminal)

abbrev ResetGroup := CCO.TerminalPowers.FullAut (cloneSource B)

/-- The actual source-chosen COMPLETE quotient orbital and BOTH of its
source squares, not a hypothetical supplied reset relation. -/
structure ActualResetMenu {i : B.Sorts} (J : FullCloneProperMI B.source i) where
  first : CloneSAP.Carrier B.Point i
  second : CloneSAP.Carrier B.Point i
  parent : fullMIParent B J first second
  external : ¬ J.val first second
  strong : (cloneSource B).product
    (originalQuotientOrbitalPalette (cloneSource B) (G := ResetGroup B) J.val first second)
    (originalQuotientOrbitalPalette (cloneSource B) (G := ResetGroup B) J.val first second) =
      originalEquivDiversityPalette (cloneSource B) (fullMIParent B J)
  raw : RawSymmetric.compose
    ((cloneSource B).menuRel
      (originalQuotientOrbitalPalette (cloneSource B) (G := ResetGroup B) J.val first second))
    ((cloneSource B).menuRel
      (originalQuotientOrbitalPalette (cloneSource B) (G := ResetGroup B) J.val first second)) =
        (fullMIParent B J).val.r

def actualResetMenu {i : B.Sorts} (J : FullCloneProperMI B.source i) : ActualResetMenu B J := by
  let witness := actual_terminal_reset B ht J
  let p := witness.choose
  let z := witness.choose_spec.choose
  have hs := witness.choose_spec.choose_spec
  exact ⟨p,z,hs.1,hs.2.1,hs.2.2.1,hs.2.2.2⟩

namespace ActualResetMenu
variable {B} {i : B.Sorts} {J : FullCloneProperMI B.source i}
variable (m : ActualResetMenu B J)

def relation : Quotient J.val.val → Quotient J.val.val → Prop :=
  originalQuotientOrbital (cloneSource B) (G := ResetGroup B) J.val m.first m.second

theorem irreflexive (q : Quotient J.val.val) : ¬ m.relation q q :=
  originalQuotientOrbital_irreflexive (cloneSource B) (cloneHomogeneous B)
    J.val m.first m.second m.external q

theorem symmetric {q t : Quotient J.val.val} : m.relation q t → m.relation t q :=
  originalQuotientOrbital_symmetric (cloneSource B) (cloneHomogeneous B)
    J.val m.first m.second q t

/-- C51's quotient RAW square is equality-inclusive at the J level. -/
theorem quotient_square :
    RawSymmetric.compose m.relation m.relation =
      (originalUpperSetoid (cloneSource B) J.val (fullMIParent B J)
        (fullMIParent_cover B J).le).r :=
  original_quotient_square_full_of_strong (cloneSource B)
    (cloneHomogeneous B) (cloneSAP B) J.val (fullMIParent B J)
    (fullMIParent_cover B J).le (bot_lt_iff_ne_bot.mpr J.property.1)
    m.first m.second m.strong

theorem inside_parent {q t : Quotient J.val.val} (h : m.relation q t) :
    originalUpperSetoid (cloneSource B) J.val (fullMIParent B J)
      (fullMIParent_cover B J).le q t :=
  originalQuotientOrbital_inside_originalUpper (cloneSource B) (cloneHomogeneous B)
    J.val (fullMIParent B J) (fullMIParent_cover B J).le m.first m.second m.parent q t h

/-- The same chosen complete m works for EVERY prescribed pair in a
parent fibre. Both legs are external, so the new J point differs from
BOTH endpoints, including the case of coincident real representatives. -/
theorem midpoint (q t : Quotient J.val.val)
    (hparent : originalUpperSetoid (cloneSource B) J.val (fullMIParent B J)
      (fullMIParent_cover B J).le q t) :
    ∃ z : Quotient J.val.val, m.relation q z ∧ m.relation z t ∧
      z ≠ q ∧ z ≠ t ∧
      originalUpperSetoid (cloneSource B) J.val (fullMIParent B J)
        (fullMIParent_cover B J).le q z := by
  have hwalk : RawSymmetric.compose m.relation m.relation q t := by
    rw [m.quotient_square]
    exact hparent
  obtain ⟨z,hqz,hzt⟩ := hwalk
  refine ⟨z,hqz,hzt,?_,?_,m.inside_parent hqz⟩
  · intro he
    subst z
    exact m.irreflexive q hqz
  · intro he
    subst z
    exact m.irreflexive t hzt

end ActualResetMenu
end
end CCO.UnfilteredEP
