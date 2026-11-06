import CCO.CloneTupleGeometry.OwnerTerminalGeometry
import CCO.FinitePackets.Geometry.Sigma
import CCO.AclOwners.UnaryTransfer

/-! Auxiliary N10 finite-packet separation at the ACTUAL terminal owner
source. Original finite equivalences are pulled back through the literal
finite unary reduct. Their classes contain finitely many owner fibres,
so actual FULL terminality forces the pullback to be exactly the clone
kernel. This conclusion needs no optional F-MI assumption. This auxiliary
module is never an ancestor of the four main geometry exports. -/

set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 250000
set_option maxHeartbeats 900000
universe u v w t
namespace CCO.CloneTupleGeometry
open APCharacter.Towers ParityHasse.Original
noncomputable section
variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X) (D : OwnerStage.{u,v,w})
variable (R : UnaryReduct S D.source) (i : D.Sorts)

/-- Restrict the pullback of an ORIGINAL FULL equivalence to one actual
final clone sort. Its old-owner finite packet has not been normalized. -/
def originalPacketPullback (F : ColourEq S (R.parent i)) :
    ColourEq (CloneSAP.source D.source) i :=
  ⟨Setoid.comap (fun x : CloneSAP.Carrier D.Point i => R.point i x.1) F.val,by
    intro x y x' y' hcol
    have hc : D.source.colour x.1 y.1 = D.source.colour x'.1 y'.1 := by
      simpa only [CloneSAP.colour_erase] using
        congrArg (fun c => c.bind (CloneSAP.eraseAtom D.source)) hcol
    have ho : S.colour (R.point i x.1) (R.point i y.1) =
        S.colour (R.point i x'.1) (R.point i y'.1) := by
      rw [R.colour,R.colour,hc]
    exact F.property _ _ _ _ ho⟩

theorem cloneKernel_le_originalPacketPullback (F : ColourEq S (R.parent i)) :
    fullCloneKernel D.source i ≤ originalPacketPullback S D R i F := by
  intro x y hxy
  change x.1 = y.1 at hxy
  change F (R.point i x.1) (R.point i y.1)
  rw [hxy]

private def packetRelativeMap (F : ColourEq S (R.parent i))
    (a : CloneSAP.Carrier D.Point i) :
    RelativeClass (fullCloneKernel D.source i).val
      (originalPacketPullback S D R i F).val a →
      {y // F (R.point i a.1) y} :=
  Quotient.lift (fun x => ⟨R.point i x.val.1,x.property⟩) (by
    intro x y hxy
    apply Subtype.ext
    change x.val.1 = y.val.1 at hxy
    exact congrArg (R.point i) hxy)

private theorem packetRelativeMap_injective (F : ColourEq S (R.parent i))
    (a : CloneSAP.Carrier D.Point i) :
    Function.Injective (packetRelativeMap S D R i F a) := by
  intro q r h
  induction q using Quotient.inductionOn with | _ x =>
    induction r using Quotient.inductionOn with | _ y =>
      apply Quotient.sound
      change x.val.1 = y.val.1
      have hp : R.point i x.val.1 = R.point i y.val.1 := congrArg Subtype.val h
      have he : (⟨i,x.val.1⟩ : Sigma D.Point) = ⟨i,y.val.1⟩ :=
        R.bijective.1 (congrArg (fun z => (⟨R.parent i,z⟩ : Sigma X)) hp)
      exact eq_of_heq (Sigma.mk.inj he).2

/-- The genuine original finite packet gives finite actual relative
quotient classes ABOVE K, despite each clone fibre itself being infinite. -/
theorem originalPacketPullback_finite (F : ColourEq S (R.parent i))
    (hF : ∀ x, Finite {y // F x y}) (a : CloneSAP.Carrier D.Point i) :
    Finite (RelativeClass (fullCloneKernel D.source i).val
      (originalPacketPullback S D R i F).val a) := by
  letI := hF (R.point i a.1)
  exact Finite.of_injective _ (packetRelativeMap_injective S D R i F a)

/-- Actual FULL terminality separates every original finite packet in
one final owner sort. No F-MI or preserved algebraicity is used here. -/
theorem terminal_originalPacketPullback (ht : D.Terminal)
    (F : ColourEq S (R.parent i)) (hF : ∀ x, Finite {y // F x y}) :
    originalPacketPullback S D R i F = fullCloneKernel D.source i := by
  have hle := cloneKernel_le_originalPacketPullback S D R i F
  by_contra hne
  obtain ⟨x⟩ := D.source.nonemptySort i
  exact ht ⟨i,fullCloneKernel D.source i,originalPacketPullback S D R i F,(x,0),
    lt_of_le_of_ne hle (Ne.symm hne),originalPacketPullback_finite S D R i F hF (x,0)⟩

/-- Each original finite packet meets each final owner sort at most once;
packets may still have algebraic partners in OTHER final sorts. -/
theorem terminal_same_packet_owner_eq (ht : D.Terminal)
    (F : ColourEq S (R.parent i)) (hF : ∀ x, Finite {y // F x y})
    (x y : D.Point i) (hxy : F (R.point i x) (R.point i y)) : x = y := by
  have h : originalPacketPullback S D R i F (x,0) (y,0) := hxy
  rw [terminal_originalPacketPullback S D R i ht F hF] at h
  exact h

variable {G : Type t} [Group G] [∀ j, MulAction G (X j)]
variable (H : HomogeneousSource S G)

/-- Source instance for the ORIGINAL greatest finite-class equivalence
Sigma(Id), not a later exact/normalized finite packet. -/
theorem terminal_original_sigma_packet (ht : D.Terminal) (x y : D.Point i)
    (hxy : FinitePackets.Geometry.sigma S H (⊥ : ColourEq S (R.parent i))
      (R.point i x) (R.point i y)) : x = y := by
  apply terminal_same_packet_owner_eq S D R i ht _ ?_ x y hxy
  intro z
  exact (AclOwners.Unary.finiteClasses_iff _).mpr
    (FinitePackets.Geometry.finiteIndex_sigma S H (⊥ : ColourEq S (R.parent i))) z

end
end CCO.CloneTupleGeometry
