import CCO.UnfilteredEP.ProperHiddenSupport
import CCO.UnaryHN.Ordered.Shuffle

/-! Actual ALL-global-order SAP for the same proper hidden age. This is
proved from its real unordered strong amalgam and the finite two-order
shuffle over the WHOLE common base. The strong intersection clause is
retained literally. No normalized-SAP assertion is assumed here. -/

universe u v w
namespace CCO.UnfilteredEP
open APRamseyReadout CloneTupleGeometry UnarySupport
noncomputable section
variable (B : OwnerStage.{u,v,w}) (ht : B.Terminal)

/-- The entire prescribed finite source orders are amalgamated, with
all domains/values/fine cylinders and exact strong intersection fixed. -/
theorem proper_hidden_all_orders_strong
    {H V W : Type (max u v)}
    (Root : Structure (Sig B ht) H)
    (Left : Structure (Sig B ht) V) (Right : Structure (Sig B ht) W)
    [oH : LinearOrder H] [oV : LinearOrder V] [oW : LinearOrder W]
    (hL : ProperAge B ht Left) (hR : ProperAge B ht Right)
    (sL : Root.Embedding Left) (sR : Root.Embedding Right)
    (leftOrdered : StrictMono sL.point) (rightOrdered : StrictMono sR.point) :
    ∃ (Z : Type (max u v)) (_ : Finite Z)
      (C : Structure (Sig B ht) Z), ProperAge B ht C ∧
      ∃ (o : LinearOrder Z) (f : Left.Embedding C) (g : Right.Embedding C),
        (∀ p, f.point (sL.point p) = g.point (sR.point p)) ∧
        (∀ a b, f.point a = g.point b → ∃ p, a = sL.point p ∧ b = sR.point p) ∧
        (∀ x y, @LT.lt Z o.toLT (f.point x) (f.point y) ↔ x < y) ∧
        (∀ x y, @LT.lt Z o.toLT (g.point x) (g.point y) ↔ x < y) := by
  letI : Finite V := hL.1.1
  letI : Finite W := hR.1.1
  letI : Finite H := Finite.of_injective sL.point sL.injective
  letI : Fintype H := Fintype.ofFinite _
  letI : Fintype V := Fintype.ofFinite _
  letI : Fintype W := Fintype.ofFinite _
  obtain ⟨Z,finite,C,hC,f,g,commute,strong⟩ :=
    (proper_hidden_age_sap B ht).strong hL hR sL sR
  letI : Finite Z := finite
  obtain ⟨o,orderL,orderR⟩ := CCO.UnaryHN.Native.Ordered.shuffle_orders
    sL.point sR.point leftOrdered rightOrdered f.point g.point f.injective g.injective
    (fun x y equal => strong x y equal)
  letI : LinearOrder Z := o
  have monoL : StrictMono f.point := orderL
  have monoR : StrictMono g.point := orderR
  exact ⟨Z,finite,C,hC,o,f,g,commute,strong,
    fun _ _ => monoL.lt_iff_lt,fun _ _ => monoR.lt_iff_lt⟩

end
end CCO.UnfilteredEP
