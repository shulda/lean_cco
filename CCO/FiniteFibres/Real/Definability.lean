import CCO.FiniteFibres.Real.Basic
import Mathlib.ModelTheory.Definability

/-! C29 uses actual formulas of the ORIGINAL finite binary language.
Each old diversity name is a binary predicate; no orbit, fibre, sheet,
equivalence or hidden-coordinate predicate is added. Logical equality is
the first-order equality symbol. -/
universe v w
namespace CCO.FiniteFibres.Real
open RealHull.Geometry FirstOrder FirstOrder.Language

variable {M : Type v} (S : AtomicSource.{0,v,w} Unit (fun _ => M))

def originalLanguage : FirstOrder.Language where
  Functions := fun _ => Empty
  Relations := fun n => {a : Atom S // n = 2}

instance originalStructure : (originalLanguage S).Structure M where
  funMap := fun f => nomatch f
  RelMap := fun {n} r xs => by
    obtain ⟨a,hn⟩ := r
    subst n
    exact col S (xs 0) (xs 1) = some a

def originalAutEquiv (g : Aut S) : M ≃[originalLanguage S] M where
  toEquiv := g.val
  map_fun' := fun f => nomatch f
  map_rel' := by
    intro n r xs
    obtain ⟨a,hn⟩ := r
    subst n
    change (col S (g • xs 0) (g • xs 1) = some a) ↔ col S (xs 0) (xs 1) = some a
    rw [show col S (g • xs 0) (g • xs 1) = col S (xs 0) (xs 1) from g.property _ _]

/-- Conversely, every automorphism of that literal first-order language
preserves the original optional colour. Thus this is the FULL original
automorphism group in either presentation. -/
theorem languageAut_colour (g : M ≃[originalLanguage S] M) (x y : M) :
    col S (g x) (g y) = col S x y := by
  cases hc : col S x y with
  | none =>
    have he : x = y := (col_none S x y).mp hc
    subst y
    exact (col_none S (g x) (g x)).mpr rfl
  | some a =>
    have hh := g.map_rel (⟨a,rfl⟩ : (originalLanguage S).Relations 2) ![x,y]
    change (col S (g x) (g y) = some a) ↔ col S x y = some a at hh
    exact hh.mpr hc

def languageAutToOriginal (g : M ≃[originalLanguage S] M) : Aut S :=
  ⟨g.toEquiv,languageAut_colour S g⟩

def relationNames : (Σ n, (originalLanguage S).Relations n) ≃ Atom S where
  toFun p := p.2.val
  invFun a := ⟨2,⟨a,rfl⟩⟩
  left_inv := by rintro ⟨n,⟨a,hn⟩⟩; subst n; rfl
  right_inv _ := rfl

theorem originalLanguage_finite : Finite (Σ n, (originalLanguage S).Relations n) := by
  letI := S.finiteAtom () ()
  exact Finite.of_injective (relationNames S) (relationNames S).injective

variable [DecidableEq M] (A : Finset M) (q : ↥A → Atom S)

noncomputable def fibreFormula : (originalLanguage S).Formula (↥A ⊕ Fin 1) :=
  Formula.iInf (fun a : ↥A =>
    FirstOrder.Language.Relations.formula₂ (L := originalLanguage S) ⟨q a,rfl⟩
      (.var (Sum.inr 0)) (.var (Sum.inl a)))

theorem fibreFormula_realize (v : Fin 1 → M) :
    (fibreFormula S A q).Realize (Sum.elim Subtype.val v) ↔ v 0 ∈ FibreSet S A q := by
  simp only [fibreFormula,Formula.realize_iInf,Formula.realize_rel₂,Term.realize_var]
  rfl

/-- The actual realized qf fibre is definable over exactly the displayed
real parameters by one finite conjunction of old diversity spokes. -/
theorem fibre_definable : (A : Set M).Definable₁ (originalLanguage S) (FibreSet S A q) := by
  change (A : Set M).Definable (originalLanguage S)
    {v : Fin 1 → M | v 0 ∈ FibreSet S A q}
  rw [Set.definable_iff_exists_formula_sum]
  refine ⟨fibreFormula S A q,?_⟩
  ext v
  exact (fibreFormula_realize S A q v).symm

theorem definable_invariant (Z : Set M)
    (hZ : (A : Set M).Definable₁ (originalLanguage S) Z)
    (g : Aut S) (hg : ∀ a ∈ A, g • a = a) (x : M) :
    g • x ∈ Z ↔ x ∈ Z := by
  obtain ⟨φ,hφ⟩ := (Set.definable_iff_exists_formula_sum).mp hZ
  have hReal (x : M) : φ.Realize (Sum.elim Subtype.val (fun _ : Fin 1 => x)) ↔ x ∈ Z := by
    exact (Set.ext_iff.mp hφ (fun _ => x)).symm
  have hAssignment : (originalAutEquiv S g) ∘ Sum.elim (fun a : ↥A => a.val) (fun _ : Fin 1 => x) =
      Sum.elim (fun a : ↥A => a.val) (fun _ : Fin 1 => g • x) := by
    funext z
    cases z with
    | inl a => exact hg a.val a.property
    | inr _ => rfl
  have hInv := StrongHomClass.realize_formula (originalAutEquiv S g) φ
    (v := Sum.elim Subtype.val (fun _ : Fin 1 => x))
  change φ.Realize ((originalAutEquiv S g) ∘
    Sum.elim (fun a : ↥A => a.val) (fun _ : Fin 1 => x)) ↔
      φ.Realize (Sum.elim (fun a : ↥A => a.val) (fun _ : Fin 1 => x)) at hInv
  rw [hAssignment] at hInv
  exact (hReal (g • x)).symm.trans (hInv.trans (hReal x))

/-- Usual real algebraicity via arbitrary first-order formulas over A is
EXACTLY finite full-stabilizer orbit algebraicity. The difficult reverse
direction uses the actual realized qf fibre; no imaginary sort is introduced. -/
theorem usual_algebraic_iff {G : Type*} [Group G] [MulAction G M]
    (H : HomogeneousSource S G) (x : M) :
    (∃ Z : Set M, Z.Finite ∧ (A : Set M).Definable₁ (originalLanguage S) Z ∧ x ∈ Z) ↔
      x ∈ acl S A := by
  constructor
  · rintro ⟨Z,hfin,hdef,hx⟩
    apply hfin.subset
    rintro y ⟨g,hg,rfl⟩
    exact (definable_invariant S A Z hdef g hg x).mpr hx
  · intro hx
    by_cases hxA : x ∈ A
    · exact ⟨{x},Set.finite_singleton x,
        Set.Definable.singleton_of_mem (originalLanguage S) hxA,Set.mem_singleton x⟩
    · exact ⟨FibreSet S A (spokes S A x hxA),
        (algebraic_iff_finite_fibre S H A x hxA).mp hx,
        fibre_definable S A (spokes S A x hxA),spokes_colour S A x hxA⟩

end CCO.FiniteFibres.Real
