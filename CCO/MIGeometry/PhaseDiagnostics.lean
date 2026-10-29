import CCO.MIGeometry.RectangleSafety
import CCO.RealClosure.Bounds.Examples.PhaseCorner

/-! C12 finite pair-table diagnostics inside the accepted actual infinite
Cartesian-phase source. These statements certify the displayed pair table;
they assert no new exact-lattice classification or safe-amalgamation premise. -/
namespace CCO.MIGeometry.PhaseDiagnostics
open ParityHasse.Original RealHull.Geometry
open RealClosure.Bounds.Examples.Phase
open FinitePackets.Normalization

def diagonalLift : Colour := ⟨(false,true,false),by decide⟩
def wideFlip : Colour := ⟨(true,false,true),by decide⟩
def safe : Set Colour := {a | a.val.1 = false ∨ a.val.2.1 = false}

/-- Different recipient rows can have the SAME actual opposite quotient
point. The corresponding diversity atom must therefore use its diagonal. -/
theorem opposite_diagonal_lift (r r' c : ℕ) (s : Bool) (hr : r ≠ r') :
    (Quotient.mk'' (r,c,s) : Quotient rowPhaseEq.val) ≠ Quotient.mk'' (r',c,s) ∧
    (Quotient.mk'' (r,c,s) : Quotient columnPhaseEq.val) = Quotient.mk'' (r',c,s) ∧
    colour (r,c,s) (r',c,s) = some diagonalLift := by
  refine ⟨?_,Quotient.sound ⟨rfl,rfl⟩,?_⟩
  · intro h
    exact hr (Quotient.exact h).1
  · apply (colour_some _ _ _).mpr
    simp [pattern,RealClosure.Bounds.Examples.Phase.row,column,phase,diagonalLift,hr]

@[simp] theorem thin_flip_unsafe : flipColour ∉ safe := by simp [safe,flipColour]
@[simp] theorem wide_flip_safe : wideFlip ∈ safe := by simp [safe,wideFlip]

/-- One fixed recipient pair has a safe lift and an unsafe lift. Thus
existential safety cannot replace universal fine support. -/
theorem existential_is_not_full_support :
    ∃ q : (actualQuotientSource source homogeneous rowPhaseEq).Atom () (),
      col (actualQuotientSource source homogeneous rowPhaseEq)
        (Quotient.mk'' (0,0,false)) (Quotient.mk'' (0,0,true)) = some q ∧
      col (actualQuotientSource source homogeneous rowPhaseEq)
        (Quotient.mk'' (0,0,false)) (Quotient.mk'' (0,1,true)) = some q ∧
      colour (0,0,false) (0,1,true) = some wideFlip ∧ wideFlip ∈ safe ∧
      q ∉ fullSupportPalette source homogeneous rowPhaseEq safe := by
  let TY := actualQuotientSource source homogeneous rowPhaseEq
  have hn : (Quotient.mk'' (0,0,false) : Quotient rowPhaseEq.val) ≠ Quotient.mk'' (0,0,true) := by
    intro he
    have h := (Quotient.exact he).2
    change false = true at h
    exact Bool.false_ne_true h
  obtain ⟨q,hq⟩ := col_some_of_ne TY hn
  have he : (Quotient.mk'' (0,0,true) : Quotient rowPhaseEq.val) = Quotient.mk'' (0,1,true) :=
    Quotient.sound ⟨rfl,rfl⟩
  have hwide : colour (0,0,false) (0,1,true) = some wideFlip :=
    (colour_some _ _ _).mpr rfl
  refine ⟨q,hq,he ▸ hq,hwide,wide_flip_safe,?_⟩
  intro hfull
  obtain ⟨a,ha,hcol⟩ := hfull (0,0,false) (0,0,true) hq
  have hthin : colour (0,0,false) (0,0,true) = some flipColour :=
    (colour_some _ _ _).mpr rfl
  have heq : a = flipColour := Option.some.inj (hcol.symm.trans hthin)
  exact thin_flip_unsafe (heq ▸ ha)

end CCO.MIGeometry.PhaseDiagnostics
