import CCO.SimultaneousQuotients.Boundaries.PhaseSource
import CCO.RawExact.Presentations
import Mathlib.Data.Setoid.Basic

/-! The actual phase cuts are FULL equality-inclusive exact equivalences:
the square of the old same-phase diversity atom recovers their real diagonal. -/
namespace CCO.SimultaneousQuotients.Boundaries.Phase
variable (I : Type) [Fintype I] [DecidableEq I]

def phaseKernel (i : I) : Setoid (Point I i) := Setoid.ker Point.phase

def falseSquare (i : I) : RawWord (source I) i i :=
  .atom (j := i) false (.atom false (.nil i))

theorem false_square (i : I) (x y : Point I i) :
    RawWord.relation (source I) (falseSquare I i) x y ↔ x.phase = y.phase := by
  constructor
  · rintro ⟨z,hxz,w,hzw,hw⟩
    change w = y at hw
    subst w
    have hx := ((colour_some I x z false).mp hxz).2
    have hy := ((colour_some I z y false).mp hzw).2
    have hx' : x.phase = z.phase := by
      cases hpx : x.phase <;> cases hpz : z.phase <;> simp_all
    have hy' : z.phase = y.phase := by
      cases hpz : z.phase <;> cases hpy : y.phase <;> simp_all
    exact hx'.trans hy'
  · intro h
    let z : Point I i := ⟨x.phase,x.index + y.index + 1⟩
    have hxz : (⟨i,x⟩ : Tagged I) ≠ ⟨i,z⟩ := by
      intro he
      have hi := congrArg (taggedIndex I) he
      change x.index = x.index + y.index + 1 at hi
      omega
    have hzy : (⟨i,z⟩ : Tagged I) ≠ ⟨i,y⟩ := by
      intro he
      have hi := congrArg (taggedIndex I) he
      change x.index + y.index + 1 = y.index at hi
      omega
    refine ⟨z,(colour_some I x z false).mpr ⟨hxz,?_⟩,
      y,(colour_some I z y false).mpr ⟨hzy,?_⟩,rfl⟩
    · exact Bool.xor_self x.phase
    · change (x.phase ^^ y.phase) = false
      rw [h,Bool.xor_self]

def phaseExact (i : I) : RawExact.NonemptyExact (source I) i i where
  words := [falseSquare I i]
  nonempty := by
    refine ⟨⟨false,0⟩,⟨false,0⟩,?_⟩
    intro w hw
    obtain rfl := List.mem_singleton.mp hw
    exact (false_square I i _ _).mpr rfl

theorem phaseExact_spec (i : I) :
    RawExact.evaluate (source I) (phaseExact I i).words = (phaseKernel I i).r := by
  funext x y
  apply propext
  constructor
  · intro h
    exact (false_square I i x y).mp (h _ (List.mem_singleton_self _))
  · intro h w hw
    obtain rfl := List.mem_singleton.mp hw
    exact (false_square I i x y).mpr h

def phaseQuotientEquiv (i : I) : Quotient (phaseKernel I i) ≃ Bool :=
  Setoid.quotientKerEquivOfRightInverse Point.phase (fun b => ⟨b,0⟩) (fun _ => rfl)

@[simp] theorem phaseQuotientEquiv_mk (i : I) (x : Point I i) :
    phaseQuotientEquiv I i (Quotient.mk (phaseKernel I i) x) = x.phase := rfl

theorem phaseCut_nontrivial (i : I) :
    phaseKernel I i ≠ ⊥ ∧ phaseKernel I i ≠ ⊤ := by
  constructor
  · intro heq
    have h : phaseKernel I i (⟨false,0⟩ : Point I i) ⟨false,1⟩ := rfl
    rw [heq] at h
    have hn := congrArg Point.index h
    cases hn
  · intro heq
    have h : phaseKernel I i (⟨false,0⟩ : Point I i) ⟨true,0⟩ := by rw [heq]; trivial
    cases h

end CCO.SimultaneousQuotients.Boundaries.Phase
