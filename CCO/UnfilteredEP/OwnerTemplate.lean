import CCO.UnfilteredEP.TemplateAge
import CCO.CloneTupleGeometry.OwnerSafeTower
import CCO.TerminalHiddenHN.UnaryLiftBases

/-! The actual original-atom table of ANY genuine owner history.
All labels are retained and every table entry is witnessed by an actual
pair in the endpoint. No whole-diagram realization is assumed here. -/

universe u v w
namespace CCO.UnfilteredEP
open CCO.CloneTupleGeometry CCO.APCharacter CCO.APCharacter.Towers
noncomputable section

abbrev OwnerOriginalAtom (B : OwnerStage.{u,v,w}) :=
  Σ i, Σ j, B.source.Atom i j

def ownerFiniteAge (B : OwnerStage.{u,v,w}) :
    FiniteAge.{u,max u w,max u v,max u v} B.Sorts (OwnerOriginalAtom B) where
  Obj := FiniteInduced (X := B.Point)
  Point A := A.vertices
  finitePoint A := A.finite_vertices.to_subtype
  sort _ x := x.val.1
  colour _ x y := (B.source.colour x.val.2 y.val.2).map (fun a => ⟨x.val.1,y.val.1,a⟩)
  diagonal A x y := by
    rw [Option.map_eq_none_iff]
    exact (B.source.colour_none_iff x.val.2 y.val.2).trans
      ⟨fun h => Subtype.ext h,fun h => congrArg Subtype.val h⟩

def reductTemplate {B D : OwnerStage.{u,v,w}} (P : UnaryReduct B.source D.source) :
    FiniteTemplate B.Sorts (OwnerOriginalAtom B) D.Sorts where
  sort := P.parent
  rel a s t := ∃ p q : Sigma D.Point, p.1 = s ∧ q.1 = t ∧
    taggedColour B.source (P.project p) (P.project q) = ⟨a.1,a.2.1,some a.2.2⟩

abbrev ownerTemplate {B D : OwnerStage.{u,v,w}} (h : History OwnerStage.Next B D) :=
  reductTemplate (OwnerStage.historyReduct h)

/-- All-pairs compatibility is pointwise only. The diagonal is literal
old equality, while every off-diagonal test has actual endpoint witnesses. -/
def PairCompatible {B D : OwnerStage.{u,v,w}} (P : UnaryReduct B.source D.source)
    {V : Type*} (old : V → Sigma B.Point) (labels : V → D.Sorts) : Prop :=
  ∀ x y, ∃ p q : Sigma D.Point, p.1 = labels x ∧ q.1 = labels y ∧
    taggedColour B.source (P.project p) (P.project q) =
      taggedColour B.source (old x) (old y)

/-- A pair-local legal marking supplies all compatibility witnesses,
including true equality on the diagonal via an actual point of its tag. -/
theorem marking_pairCompatible {B D : OwnerStage.{u,v,w}}
    (P : UnaryReduct B.source D.source) (A : FiniteInduced (X := B.Point))
    (a : (ownerFiniteAge B).Marking (reductTemplate P) A) :
    PairCompatible P (fun x : A.vertices => x.val) a.label := by
  intro x y
  cases hcol : B.source.colour x.val.2 y.val.2 with
  | some atom =>
    have hp := a.pairs x y ⟨x.val.1,y.val.1,atom⟩ (by
      change (B.source.colour x.val.2 y.val.2).map _ = _
      rw [hcol]
      rfl)
    simpa only [reductTemplate,taggedColour,hcol] using hp
  | none =>
    have hxy : x = y := Subtype.ext ((B.source.colour_none_iff _ _).mp hcol)
    subst y
    obtain ⟨q⟩ := D.source.nonemptySort (a.label x)
    let p : Sigma D.Point := ⟨a.label x,q⟩
    refine ⟨p,p,rfl,rfl,?_⟩
    change (⟨P.parent (a.label x),P.parent (a.label x),
      B.source.colour (P.point _ q) (P.point _ q)⟩ : Age.Colour B.source) = _
    rw [(B.source.colour_none_iff _ _).mpr rfl]
    change _ = (⟨x.val.1,x.val.1,B.source.colour x.val.2 x.val.2⟩ : Age.Colour B.source)
    rw [(B.source.colour_none_iff _ _).mpr rfl]
    exact congrArg (fun i => (⟨i,i,none⟩ : Age.Colour B.source)) (a.sorted x)

end
end CCO.UnfilteredEP
