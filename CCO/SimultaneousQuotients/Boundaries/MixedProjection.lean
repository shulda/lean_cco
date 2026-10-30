import CCO.SimultaneousQuotients.Boundaries.PhaseExact
import CCO.SimultaneousQuotients.Boundaries.PhaseSAP

/-! C55: factorwise projection of a mixed word strictly enlarges its
represented endpoint relation, in a genuine infinite homogeneous SAP+CCO
source. The old endpoint profile nevertheless remains a named atomic block. -/
namespace CCO.SimultaneousQuotients.Boundaries.Phase
namespace Mixed

abbrev SortIndex := Fin 3
abbrev S := source SortIndex
abbrev X := Point SortIndex

/-- Collapse the middle ORIGINAL sort only; retain actual equality elsewhere. -/
def mixedCuts (i : SortIndex) : Setoid (X i) := if i = 1 then ⊤ else ⊥

def exactCut (i : SortIndex) : RawExact.NonemptyExact S i i where
  words := if i = 1 then [] else [.nil i]
  nonempty := by
    refine ⟨⟨false,0⟩,⟨false,0⟩,?_⟩
    intro w hw
    by_cases h : i = 1
    · simp only [if_pos h,List.not_mem_nil] at hw
    · simp only [if_neg h,List.mem_singleton] at hw
      subst w
      rfl

theorem exactCut_spec (i : SortIndex) :
    RawExact.evaluate S (exactCut i).words = (mixedCuts i).r := by
  funext x y
  apply propext
  by_cases h : i = 1
  · have hc : mixedCuts i = ⊤ := by unfold mixedCuts; rw [if_pos h]
    rw [hc]
    simp [RawExact.evaluate,exactCut,h]
  · have hc : mixedCuts i = ⊥ := by unfold mixedCuts; rw [if_neg h]
    rw [hc]
    simp [RawExact.evaluate,exactCut,h,RawWord.relation,TRel.ident]

abbrev Q (i : SortIndex) := Quotient (mixedCuts i)
def project (i : SortIndex) (x : X i) : Q i := Quotient.mk (mixedCuts i) x

def image {i j : SortIndex} (R : X i → X j → Prop) (x : Q i) (y : Q j) : Prop :=
  ∃ a b, project i a = x ∧ project j b = y ∧ R a b

def oldWord : RawWord S 0 2 := .atom (j := 1) false (.atom false (.nil 2))

theorem different_sorts {i j : SortIndex} (h : i ≠ j) (x : X i) (y : X j) :
    (⟨i,x⟩ : Tagged SortIndex) ≠ ⟨j,y⟩ := fun he => h (congrArg Sigma.fst he)

theorem word_phase (x : X 0) (y : X 2) :
    RawWord.relation S oldWord x y ↔ x.phase = y.phase := by
  constructor
  · rintro ⟨z,hxz,w,hzw,hw⟩
    change w = y at hw
    subst w
    have hx := ((colour_some SortIndex x z false).mp hxz).2
    have hy := ((colour_some SortIndex z y false).mp hzw).2
    cases hpx : x.phase <;> cases hpy : y.phase <;> cases hpz : z.phase <;> simp_all
  · intro h
    let z : X 1 := ⟨x.phase,0⟩
    refine ⟨z,(colour_some SortIndex x z false).mpr
      ⟨different_sorts (by decide) x z,Bool.xor_self x.phase⟩,
      y,(colour_some SortIndex z y false).mpr ⟨different_sorts (by decide) z y,?_⟩,rfl⟩
    change (x.phase ^^ y.phase) = false
    rw [h,Bool.xor_self]

/-- Thus this counterexample concerns factorwise WORD descent: the old
endpoint relation still is one actual named quotient atomic relation. -/
theorem oldWord_is_atomic (x : X 0) (y : X 2) :
    RawWord.relation S oldWord x y ↔ S.atomRel false x y := by
  rw [word_phase]
  change x.phase = y.phase ↔ colour SortIndex x y = some false
  rw [colour_some]
  have hd := different_sorts (by decide : (0 : SortIndex) ≠ 2) x y
  constructor
  · intro hp
    exact ⟨hd,by rw [hp]; exact Bool.xor_self y.phase⟩
  · intro hp
    have hx := hp.2
    cases hpx : x.phase <;> cases hpy : y.phase <;> simp_all

/-- The retained endpoint equality kernels preserve the old atomic profile
as its actual named A-C quotient block, despite the failure of word descent. -/
theorem projected_oldWord_is_atomic (x : Q 0) (y : Q 2) :
    image (RawWord.relation S oldWord) x y ↔
      image (S.atomRel (i := 0) (j := 2) false) x y := by
  simp only [image,oldWord_is_atomic]

/-- Projecting any old word witness always supplies a projected factor
witness. The later counterexample proves this inclusion is strict. -/
theorem old_word_projects (x : Q 0) (y : Q 2)
    (h : image (RawWord.relation S oldWord) x y) :
    ∃ b : Q 1,
      image (S.atomRel (i := 0) (j := 1) false) x b ∧
      image (S.atomRel (i := 1) (j := 2) false) b y := by
  obtain ⟨a,c,ha,hc,b,hab,d,hbd,hd⟩ := h
  change d = c at hd
  subst d
  exact ⟨project 1 b,⟨a,b,ha,rfl,hab⟩,⟨b,c,rfl,hc,hbd⟩⟩

theorem projected_left_edge_total (x : Q 0) (y : Q 1) :
    image (S.atomRel (i := 0) (j := 1) false) x y := by
  induction x using Quotient.inductionOn with
  | _ a =>
    induction y using Quotient.inductionOn with
    | _ b =>
      let c : X 1 := ⟨a.phase,0⟩
      refine ⟨a,c,rfl,Quotient.sound trivial,?_⟩
      exact (colour_some SortIndex a c false).mpr
        ⟨different_sorts (i := 0) (j := 1) (by decide) a c,Bool.xor_self a.phase⟩

theorem projected_right_edge_total (x : Q 1) (y : Q 2) :
    image (S.atomRel (i := 1) (j := 2) false) x y := by
  induction x using Quotient.inductionOn with
  | _ a =>
    induction y using Quotient.inductionOn with
    | _ b =>
      let c : X 1 := ⟨b.phase,0⟩
      refine ⟨c,b,Quotient.sound trivial,rfl,?_⟩
      exact (colour_some SortIndex c b false).mpr
        ⟨different_sorts (i := 1) (j := 2) (by decide) c b,Bool.xor_self b.phase⟩

def leftPoint : X 0 := ⟨false,0⟩
def rightPoint : X 2 := ⟨true,0⟩
def middleFalse : X 1 := ⟨false,0⟩
def middleTrue : X 1 := ⟨true,0⟩

/-- Both projected edge orbitals admit the displayed incompatible old phases,
because their intermediate top-quotient vertex is the SAME actual class. -/
theorem projected_word_holds :
    ∃ b : Q 1,
      image (S.atomRel (i := 0) (j := 1) false) (project 0 leftPoint) b ∧
      image (S.atomRel (i := 1) (j := 2) false) b (project 2 rightPoint) := by
  refine ⟨project 1 middleFalse,
    ⟨leftPoint,middleFalse,rfl,rfl,?_⟩,
    ⟨middleTrue,rightPoint,?_,rfl,?_⟩⟩
  · change colour SortIndex leftPoint middleFalse = some false
    exact (colour_some SortIndex leftPoint middleFalse false).mpr
      ⟨different_sorts (i := 0) (j := 1) (by decide) leftPoint middleFalse,rfl⟩
  · exact Quotient.sound trivial
  · change colour SortIndex middleTrue rightPoint = some false
    exact (colour_some SortIndex middleTrue rightPoint false).mpr
      ⟨different_sorts (i := 1) (j := 2) (by decide) middleTrue rightPoint,rfl⟩

theorem projected_old_word_fails :
    ¬ image (RawWord.relation S oldWord) (project 0 leftPoint) (project 2 rightPoint) := by
  rintro ⟨x,y,hx,hy,hword⟩
  have hx' : x = leftPoint := by
    have he : (mixedCuts 0).r x leftPoint := Quotient.exact hx
    exact he
  have hy' : y = rightPoint := by
    have he : (mixedCuts 2).r y rightPoint := Quotient.exact hy
    exact he
  subst x
  subst y
  have hp := (word_phase leftPoint rightPoint).mp hword
  cases hp

/-- The strict mixed-word failure occurs WITH all actual source hypotheses. -/
theorem actual_counterexample :
    HomogeneousSource S (Aut SortIndex) ∧ AgeSAP S ∧ SemanticCCO S ∧
    (∃ b : Q 1,
      image (S.atomRel (i := 0) (j := 1) false) (project 0 leftPoint) b ∧
      image (S.atomRel (i := 1) (j := 2) false) b (project 2 rightPoint)) ∧
    ¬ image (RawWord.relation S oldWord) (project 0 leftPoint) (project 2 rightPoint) :=
  ⟨homogeneous SortIndex,strongAmalgamation SortIndex,semanticCCO SortIndex,
    projected_word_holds,projected_old_word_fails⟩

end Mixed
end CCO.SimultaneousQuotients.Boundaries.Phase
