import CCO.PairSafeSplit.Infinity.TypeFibres
import CCO.CloneSAP.Lattice.Definability
import Mathlib.ModelTheory.Complexity

/-! Explicit named first-order semantics for C22/C26. The main infinity
proofs use stronger direct invariance, so this syntax layer is independent. -/

universe u v w t
namespace CCO.PairSafeSplit.Infinity
open FirstOrder FirstOrder.Language
open CCO.QuotientTransport.Definability
open RealAction
variable {ι : Type u} {X : ι → Type v} (S : AtomicSource.{u,v,w} ι X)
variable {G : Type t} [Group G] [∀ i : ι, MulAction G (X i)]

def parameterValuation (B : FiniteInduced (X := X)) (x : Sigma X) :
    Option B.vertices → Sigma X
  | none => x
  | some b => b.val

def formulaSet (B : FiniteInduced (X := X))
    (φ : (namedLanguage S).Formula (Option B.vertices)) : Set (Sigma X) :=
  {x | φ.Realize (parameterValuation B x)}

/-- Every quantified formula with actual base parameters is preserved by
the actual original stabilizer. No invariant-to-definable premise is used. -/
theorem formulaSet_invariant (H : HomogeneousSource S G)
    (B : FiniteInduced (X := X)) (φ : (namedLanguage S).Formula (Option B.vertices))
    (g : G) (hg : g ∈ pointwiseStabilizer B.vertices) (x : Sigma X)
    (hx : x ∈ formulaSet S B φ) : g • x ∈ formulaSet S B φ := by
  have h := (StrongHomClass.realize_formula (CloneSAP.Lattice.namedAut S H g) φ).mpr hx
  have he : (CloneSAP.Lattice.namedAut S H g) ∘ parameterValuation B x =
      parameterValuation B (g • x) := by
    funext b
    cases b with
    | none => rfl
    | some b => exact hg b.val b.property
  rw [he] at h
  exact h

/-- C22 for literal arbitrary-depth formulas over the finite real base. -/
theorem finite_formulaSet_subset_base (H : HomogeneousSource S G) (sap : AgeSAP S)
    (B : FiniteInduced (X := X)) (φ : (namedLanguage S).Formula (Option B.vertices))
    (hφ : (formulaSet S B φ).Finite) : formulaSet S B φ ⊆ B.vertices :=
  finite_invariant_subset_base S H sap B _ hφ
    (fun g hg x hx => formulaSet_invariant S H B φ g hg x hx)

noncomputable def typeFormula (B : FiniteInduced (X := X)) {i : ι} (x : X i) :
    (namedLanguage S).Formula (Option B.vertices) := by
  letI : Fintype B.vertices := B.finite_vertices.fintype
  let self : (namedLanguage S).Formula (Option B.vertices) :=
    FirstOrder.Language.Relations.formula₂ (L := namedLanguage S)
    (NamedSymbol.pairName i i none) (.var none) (.var none)
  let left : B.vertices → (namedLanguage S).Formula (Option B.vertices) :=
    fun b => FirstOrder.Language.Relations.formula₂
    (L := namedLanguage S) (NamedSymbol.pairName i b.val.1 (S.colour x b.val.2))
      (.var none) (.var (some b))
  let right : B.vertices → (namedLanguage S).Formula (Option B.vertices) :=
    fun b => FirstOrder.Language.Relations.formula₂
    (L := namedLanguage S) (NamedSymbol.pairName b.val.1 i (S.colour b.val.2 x))
      (.var (some b)) (.var none)
  exact self ⊓ (Formula.iInf left ⊓ Formula.iInf right)

private theorem typed_literal {i j : ι} (c : Option (S.Atom i j))
    (x : X i) (y : X j) :
    taggedRelation (fun a : X i => fun b : X j => S.colour a b = c)
      ⟨i,x⟩ ⟨j,y⟩ ↔ S.colour x y = c := by
  constructor
  · rintro ⟨a,b,ha,hb,h⟩
    have ha' : x = a := eq_of_heq (Sigma.mk.inj ha).2
    have hb' : y = b := eq_of_heq (Sigma.mk.inj hb).2
    simpa only [ha',hb'] using h
  · intro h
    exact ⟨x,y,rfl,rfl,h⟩

/-- C26: the displayed finite atomic conjunction really defines the
realized complete one-point type in the original named structure. -/
theorem typeFormula_realize (B : FiniteInduced (X := X)) {i : ι} (x y : X i) :
    (typeFormula S B x).Realize (parameterValuation B ⟨i,y⟩) ↔ y ∈ typeFibre S B x := by
  classical
  simp only [typeFormula,Formula.realize_inf,Formula.realize_iInf,
    Formula.realize_rel₂]
  change (taggedRelation (fun a b : X i => S.colour a b = none) ⟨i,y⟩ ⟨i,y⟩ ∧
    ((∀ b : B.vertices, taggedRelation
      (fun a : X i => fun z : X b.val.1 => S.colour a z = S.colour x b.val.2)
        ⟨i,y⟩ b.val) ∧
    (∀ b : B.vertices, taggedRelation
      (fun a : X b.val.1 => fun z : X i => S.colour a z = S.colour b.val.2 x)
        b.val ⟨i,y⟩))) ↔ _
  simp only [typed_literal]
  have hyy : S.colour y y = none := (S.colour_none_iff _ _).mpr rfl
  have hxx : S.colour x x = none := (S.colour_none_iff _ _).mpr rfl
  rw [hyy]
  constructor
  · rintro ⟨_,hl,hr⟩
    refine ⟨?_,?_,?_⟩
    · simp only [taggedColour,hxx,hyy]
    · intro b hb
      have hc := (typed_literal S (S.colour x b.2) y b.2).mp (hl ⟨b,hb⟩)
      exact congrArg (fun c => (⟨i,b.1,c⟩ : Σ a, Σ d, Option (S.Atom a d))) hc.symm
    · intro b hb
      have hc := (typed_literal S (S.colour b.2 x) b.2 y).mp (hr ⟨b,hb⟩)
      exact congrArg (fun c => (⟨b.1,i,c⟩ : Σ a, Σ d, Option (S.Atom a d))) hc.symm
  · intro h
    refine ⟨rfl,?_,?_⟩
    · intro b
      apply (typed_literal S (S.colour x b.val.2) y b.val.2).mpr
      have hc := h.2.1 b.val b.property
      simpa only [taggedColour,Sigma.mk.injEq,heq_eq_eq,true_and] using hc.symm
    · intro b
      apply (typed_literal S (S.colour b.val.2 x) b.val.2 y).mpr
      have hc := h.2.2 b.val b.property
      simpa only [taggedColour,Sigma.mk.injEq,heq_eq_eq,true_and] using hc.symm

private theorem finite_inf_qf {L : FirstOrder.Language} {α β : Type*} [Finite β]
    (f : β → L.Formula α) (hf : ∀ b, (f b).IsQF) : (Formula.iInf f).IsQF := by
  classical
  letI : Fintype β := Fintype.ofFinite β
  change (((Finset.univ : Finset β).toList.map f).foldr (fun a b => a ⊓ b) ⊤).IsQF
  generalize (Finset.univ : Finset β).toList = bs
  induction bs with
  | nil => exact BoundedFormula.IsQF.top
  | cons b bs ih => exact (hf b).inf ih

private theorem binary_literal_qf {L : FirstOrder.Language} {α : Type*}
    (r : L.Relations 2) (a b : L.Term α) : (r.formula₂ a b).IsQF := r.isQF _

/-- The defining formula is genuinely quantifier-free, not only equivalent
to some unspecified formula. The empty conjunction stays quantifier-free. -/
theorem typeFormula_qf (B : FiniteInduced (X := X)) {i : ι} (x : X i) :
    (typeFormula S B x).IsQF := by
  letI : Fintype B.vertices := B.finite_vertices.fintype
  unfold typeFormula
  apply BoundedFormula.IsQF.inf
  · exact binary_literal_qf _ _ _
  · apply BoundedFormula.IsQF.inf
    · apply finite_inf_qf
      intro b
      exact binary_literal_qf _ _ _
    · apply finite_inf_qf
      intro b
      exact binary_literal_qf _ _ _

def parameterBase {n : ℕ} (a : Fin n → Sigma X) : FiniteInduced (X := X) :=
  ⟨Set.range a,Set.finite_range _⟩

noncomputable def parameterIndex {n : ℕ} (a : Fin n → Sigma X) :
    Option (parameterBase a).vertices → Option (Fin n)
  | none => none
  | some b => some (Classical.choose b.property)

def tupleValuation {n : ℕ} (a : Fin n → Sigma X) (x : Sigma X) :
    Option (Fin n) → Sigma X
  | none => x
  | some k => a k

/-- A parameter tuple may have repetitions; only its actual real range
forms the pointwise base. No enumeration or injectivity assumption is added. -/
noncomputable def tupleTypeFormula {n : ℕ} (a : Fin n → Sigma X) {i : ι} (x : X i) :
    (namedLanguage S).Formula (Option (Fin n)) :=
  (typeFormula S (parameterBase a) x).relabel (parameterIndex a)

theorem tupleTypeFormula_realize {n : ℕ} (a : Fin n → Sigma X) {i : ι} (x y : X i) :
    (tupleTypeFormula S a x).Realize (tupleValuation a ⟨i,y⟩) ↔
      SameTypeOver S (parameterBase a) (⟨i,x⟩ : Sigma X) ⟨i,y⟩ := by
  rw [tupleTypeFormula,Formula.realize_relabel]
  have he : tupleValuation a ⟨i,y⟩ ∘ parameterIndex a =
      parameterValuation (parameterBase a) ⟨i,y⟩ := by
    funext b
    cases b with
    | none => rfl
    | some b => exact Classical.choose_spec b.property
  rw [he]
  exact typeFormula_realize S (parameterBase a) x y

theorem tupleTypeFormula_qf {n : ℕ} (a : Fin n → Sigma X) {i : ι} (x : X i) :
    (tupleTypeFormula S a x).IsQF :=
  (typeFormula_qf S (parameterBase a) x).relabel (Sum.inl ∘ parameterIndex a)

end CCO.PairSafeSplit.Infinity
