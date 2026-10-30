import CCO.ResetOrder.Hierarchy.QuotientSystem
import CCO.ResetOrder.Hierarchy.Reindex

/-! Actual quotient-cut transitions supply the abstract chart hypotheses.
Restriction uses named inverse paths inside the SAME finite closed object.
Rank equality is derived from the transported actual upper intervals. -/
universe u v w
namespace CCO.ResetOrder.Hierarchy.QuotientSystem
variable {S : Type u} {L : S → Type u} {V : S → Type v}
variable [∀ s, Lattice (L s)] [∀ s, OrderTop (L s)] [∀ s, Fintype (L s)]
variable {P : Priority (L := L)} {R : ∀ s, EquivalenceLattice (L s) (V s)}

structure CutTransitions where
  paths : TransitionPaths.{u,v,w} (Index (L := L)) (AmbientPoint R)
  upperIntervals : ∀ {i j} (p : paths.Path i j),
    {l : L i.1 // i.2.val < l} ≃ {m : L j.1 // j.2.val < m}
  parentChart : ∀ {i j} (p : paths.Path i j),
    (R i.1).Point (miParent i.2.val) ≃ (R j.1).Point (miParent j.2.val)
  parent_commute : ∀ {i j} (p : paths.Path i j) x,
    parentChart p ((R i.1).up (le_miParent i.2.val) x) =
      (R j.1).up (le_miParent j.2.val) (paths.map p x)

namespace CutTransitions
variable (T : CutTransitions (R := R)) (A : ClosedObject P R)

def Closed : Prop := ∀ {i j} (p : T.paths.Path i j) x,
  x ∈ A.points i → T.paths.map p x ∈ A.points j

def restrictedMap (h : T.Closed A) {i j} (p : T.paths.Path i j) : A.Carrier i ≃ A.Carrier j where
  toFun x := ⟨T.paths.map p x.val, h p x.val x.property⟩
  invFun y := ⟨T.paths.map (T.paths.inverse p) y.val, h (T.paths.inverse p) y.val y.property⟩
  left_inv x := Subtype.ext (T.paths.map_inverse p x.val)
  right_inv y := by
    apply Subtype.ext
    apply (T.paths.map (T.paths.inverse p)).injective
    rw [T.paths.map_inverse]

def restrict (h : T.Closed A) : TransitionPaths (Index (L := L)) A.Carrier where
  Path := T.paths.Path
  identity := T.paths.identity
  compose := T.paths.compose
  inverse := T.paths.inverse
  map := T.restrictedMap A h
  map_identity i x := Subtype.ext (T.paths.map_identity i x.val)
  map_compose p q x := Subtype.ext (T.paths.map_compose p q x.val)
  map_inverse p x := Subtype.ext (T.paths.map_inverse p x.val)
  holonomy p x := Subtype.ext (T.paths.holonomy p x.val)

theorem parent_transport (h : T.Closed A) {i j} (p : T.paths.Path i j)
    (x y : A.Carrier i) :
    A.parent j (T.restrictedMap A h p x) (T.restrictedMap A h p y) ↔ A.parent i x y := by
  change (R j.1).up (le_miParent j.2.val) (T.paths.map p x.val) =
    (R j.1).up (le_miParent j.2.val) (T.paths.map p y.val) ↔ _
  rw [← T.parent_commute p x.val, ← T.parent_commute p y.val]
  exact (T.parentChart p).injective.eq_iff

theorem rank_transport {i j} (p : T.paths.Path i j) :
    (schedule P).rank i = (schedule P).rank j := upperRank_transport (T.upperIntervals p)

noncomputable def charting (h : T.Closed A)
    (rep : ∀ r, (T.restrict A h).InOrbit r) :
    Charting (A.system.reindex (T.restrict A h).orbitEquiv) rep where
  paths r := (T.restrict A h).comap (fun j : (T.restrict A h).InOrbit r => j.val)
  chosen r j := (T.restrict A h).representativePath rep r j
  parent_transport r p x y := T.parent_transport A h p x y
  rank_orbit r j := (T.rank_transport (P := P)
    ((T.restrict A h).representativePath rep r j)).symm

end CutTransitions
end CCO.ResetOrder.Hierarchy.QuotientSystem
