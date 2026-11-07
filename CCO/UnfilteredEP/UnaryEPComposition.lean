import CCO.UnfilteredEP.RealExpansionEP
import CCO.TerminalHiddenHN.UnaryLift

/-! B064 C90–C92: relation-only EP composition on the same original
carriers. The terminal EP host is chosen first, then unary EP chooses
ONE original host before ANY full competing expansion is received.
All later restrictions retain exactly the prescribed original vertex
maps. No functions, closure premises or Ramsey provider are added. -/

universe u v w l k
namespace CCO.UnfilteredEP
open CCO.TerminalHiddenHN CCO.APCharacter.Towers
noncomputable section

variable {ι κ : Type u} {X : ι → Type v} {Y : κ → Type v}
variable {S : AtomicSource.{u,v,w} ι X} {T : AtomicSource.{u,v,w} κ Y}

/-- Retain the entire old terminal source and add no predicate symbols.
Its unary lift records precisely the actual terminal sort labels. -/
def unitReadoutData (T : AtomicSource.{u,v,w} κ Y) :
    RealExpansionData.{u,v,w,0,0} T where
  Unary := PEmpty
  Binary := PEmpty
  finiteUnary := inferInstance
  finiteBinary := inferInstance
  unarySort := PEmpty.elim
  leftSort := PEmpty.elim
  rightSort := PEmpty.elim
  Expansion _ := PUnit
  nonempty _ := ⟨PUnit.unit⟩
  unary _ R := PEmpty.elim R
  binary _ R := PEmpty.elim R
  unary_sorted _ R := PEmpty.elim R
  binary_sorted _ R := PEmpty.elim R
  faithful a b _ _ := by cases a; cases b; rfl
  restrict _ _ := PUnit.unit
  restrict_unary _ _ R := PEmpty.elim R
  restrict_binary _ _ R := PEmpty.elim R

/-- Genuine unary EP and genuine relative relational EP compose with
the universal competitor quantifier on ONE fixed original host. -/
theorem unaryLift_EP (P : UnaryReduct S T) (E : RealExpansionData.{u,v,w,l,k} T)
    (unaryEP : (UnaryLift.data P (unitReadoutData T)).EP)
    (terminalEP : E.EP) : (UnaryLift.data P E).EP := by
  intro A a
  rcases a with ⟨ta,L,a,rfl⟩
  obtain ⟨W,hW⟩ := terminalEP L.object a
  let U := UnaryLift.projectedObject P W
  let N := UnaryLift.canonicalLift P U
  let unaryTarget := UnaryLift.fromLift P (unitReadoutData T) N PUnit.unit
  obtain ⟨B,hB⟩ := unaryEP U unaryTarget
  refine ⟨B,?_⟩
  intro b
  rcases b with ⟨tb,M,b,rfl⟩
  let unaryCompetitor := UnaryLift.fromLift P (unitReadoutData T) M PUnit.unit
  obtain ⟨f⟩ := hB unaryCompetitor
  let g := UnaryLift.toTerminalEmbedding P (unitReadoutData T) N M f
  let inv := UnaryLift.projectedInverse P W
  let old : InducedEmbedding T W M.object := {
    toEmbedding := inv.toEmbedding.trans g.old.toEmbedding
    preserves_sort x := (g.old.preserves_sort _).trans (inv.preserves_sort x)
    preserves_colours x y := (inv.preserves_colours x y).trans (g.old.preserves_colours _ _) }
  obtain ⟨e⟩ := hW (E.restrict old b)
  exact ⟨UnaryLift.toOldEmbedding P E L M ((E.restrictionEmbedding old b).comp e)⟩

end
end CCO.UnfilteredEP
