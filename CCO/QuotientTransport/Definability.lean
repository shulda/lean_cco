import CCO.RawSource
import Mathlib.ModelTheory.Semantics
import Mathlib.Tactic.FinCases

/-! B040 C13/C25: actual parameter-free first-order formulas, independently
of the group-action transport algebra. Tagged relation representations keep
quantified intermediate witnesses in their actual original sorts. -/

open scoped FirstOrder
open FirstOrder FirstOrder.Language

universe u v w z

namespace CCO.QuotientTransport.Definability

section Formulas

variable {L : FirstOrder.Language} {M : Type*} [L.Structure M]

/-- A transparent parameter-free formula certificate, with no added constants. -/
def FormulaDefines (φ : L.Formula (Fin 2)) (R : M → M → Prop) : Prop :=
  ∀ x y, φ.Realize ![x, y] ↔ R x y

def HasFormula (R : M → M → Prop) : Prop :=
  ∃ φ : L.Formula (Fin 2), FormulaDefines φ R

def converseFormula (φ : L.Formula (Fin 2)) : L.Formula (Fin 2) :=
  φ.relabel (fun i => if i = 0 then 1 else 0)

theorem converseFormula_realize (φ : L.Formula (Fin 2)) (x y : M) :
    (converseFormula φ).Realize ![x, y] ↔ φ.Realize ![y, x] := by
  rw [converseFormula, Formula.realize_relabel]
  have vector : ![x, y] ∘ (fun i : Fin 2 => if i = 0 then 1 else 0) = ![y, x] := by
    funext i
    fin_cases i <;> rfl
  rw [vector]

/-- One actual existentially quantified intermediate point, equality allowed. -/
noncomputable def compFormula (φ ψ : L.Formula (Fin 2)) : L.Formula (Fin 2) :=
  ((φ.relabel (fun i => if i = 0 then Sum.inl 0 else Sum.inr ())) ⊓
    (ψ.relabel (fun i => if i = 0 then Sum.inr () else Sum.inl 1))).iExs Unit

theorem compFormula_realize (φ ψ : L.Formula (Fin 2)) (x z : M) :
    (compFormula φ ψ).Realize ![x, z] ↔
      ∃ y : M, φ.Realize ![x, y] ∧ ψ.Realize ![y, z] := by
  simp only [compFormula, Formula.realize_iExs, Formula.realize_inf,
    Formula.realize_relabel]
  have left : ∀ t : Unit → M,
      Sum.elim ![x, z] t ∘ (fun i : Fin 2 => if i = 0 then Sum.inl 0 else Sum.inr ()) =
        ![x, t ()] := by
    intro t; funext i; fin_cases i <;> rfl
  have right : ∀ t : Unit → M,
      Sum.elim ![x, z] t ∘ (fun i : Fin 2 => if i = 0 then Sum.inr () else Sum.inl 1) =
        ![t (), z] := by
    intro t; funext i; fin_cases i <;> rfl
  simp only [left, right]
  constructor
  · rintro ⟨t, h⟩; exact ⟨t (), h⟩
  · rintro ⟨y, h⟩; exact ⟨fun _ => y, h⟩

theorem HasFormula.converse {R : M → M → Prop} (h : HasFormula (L := L) R) :
    HasFormula (L := L) (fun x y => R y x) := by
  obtain ⟨φ, hφ⟩ := h
  exact ⟨converseFormula φ, fun x y => (converseFormula_realize φ x y).trans (hφ y x)⟩

theorem HasFormula.comp {R S : M → M → Prop}
    (hR : HasFormula (L := L) R) (hS : HasFormula (L := L) S) :
    HasFormula (L := L) (fun x z => ∃ y, R x y ∧ S y z) := by
  obtain ⟨φ, hφ⟩ := hR
  obtain ⟨ψ, hψ⟩ := hS
  refine ⟨compFormula φ ψ, fun x z => ?_⟩
  rw [compFormula_realize]
  exact exists_congr (fun y => and_congr (hφ x y) (hψ y z))

/-- The actual C13 formula R-converse;E;R, with its full realization theorem. -/
noncomputable def transportFormula (r e : L.Formula (Fin 2)) : L.Formula (Fin 2) :=
  compFormula (converseFormula r) (compFormula e r)

theorem transportFormula_realize (r e : L.Formula (Fin 2)) (y y' : M) :
    (transportFormula r e).Realize ![y, y'] ↔
      ∃ x x', r.Realize ![x, y] ∧ e.Realize ![x, x'] ∧ r.Realize ![x', y'] := by
  simp only [transportFormula, compFormula_realize, converseFormula_realize]
  constructor
  · rintro ⟨x, hr, x', he, hr'⟩
    exact ⟨x, x', hr, he, hr'⟩
  · rintro ⟨x, x', hr, he, hr'⟩
    exact ⟨x, hr, x', he, hr'⟩

end Formulas

section Typed

variable {ι : Type u} {X : ι → Type v}
variable {L : FirstOrder.Language} [L.Structure (Sigma X)]

/-- A typed relation as an actual tagged ambient relation, false off its sorts. -/
def taggedRelation {i j : ι} (R : TRel X i j) : Sigma X → Sigma X → Prop :=
  fun p q => ∃ x y, p = ⟨i, x⟩ ∧ q = ⟨j, y⟩ ∧ R x y

def TypedHasFormula {i j : ι} (R : TRel X i j) : Prop :=
  HasFormula (L := L) (taggedRelation R)

theorem taggedRelation_converse {i j : ι} (R : TRel X i j) :
    taggedRelation (TRel.converse R) = (fun p q => taggedRelation R q p) := by
  funext p q
  apply propext
  constructor <;> rintro ⟨x, y, hx, hy, hr⟩ <;> exact ⟨y, x, hy, hx, hr⟩

theorem taggedRelation_comp {i j k : ι} (R : TRel X i j) (S : TRel X j k) :
    taggedRelation (TRel.comp R S) =
      (fun p q => ∃ r : Sigma X, taggedRelation R p r ∧ taggedRelation S r q) := by
  funext p q
  apply propext
  constructor
  · rintro ⟨x, z, rfl, rfl, y, hr, hs⟩
    exact ⟨⟨j, y⟩, ⟨x, y, rfl, rfl, hr⟩, ⟨y, z, rfl, rfl, hs⟩⟩
  · rintro ⟨r, ⟨x, y, rfl, rfl, hr⟩, ⟨y', z, hy, rfl, hs⟩⟩
    have equal : y = y' := eq_of_heq (Sigma.mk.inj hy).2
    subst y'
    exact ⟨x, z, rfl, rfl, y, hr, hs⟩

theorem TypedHasFormula.converse {i j : ι} {R : TRel X i j}
    (h : TypedHasFormula (L := L) R) : TypedHasFormula (L := L) (TRel.converse R) := by
  unfold TypedHasFormula
  rw [taggedRelation_converse]
  exact HasFormula.converse h

theorem TypedHasFormula.comp {i j k : ι} {R : TRel X i j} {S : TRel X j k}
    (hR : TypedHasFormula (L := L) R) (hS : TypedHasFormula (L := L) S) :
    TypedHasFormula (L := L) (TRel.comp R S) := by
  unfold TypedHasFormula
  rw [taggedRelation_comp]
  exact HasFormula.comp hR hS

/-- C13 under the explicit formula gate; no group-action assumption occurs. -/
theorem typed_transport_has_formula {i j : ι} {R : TRel X i j} {E : TRel X i i}
    (hR : TypedHasFormula (L := L) R) (hE : TypedHasFormula (L := L) E) :
    TypedHasFormula (L := L) (TRel.comp (TRel.converse R) (TRel.comp E R)) :=
  hR.converse.comp (hE.comp hR)

/-- C25: every finite typed prefix has a first-order existential formula.
Identity formulas are supplied for the named original sorts, including nil. -/
theorem typedWord_has_formula {Letter : ι → ι → Type w}
    (repr : ∀ {i j}, Letter i j → TRel X i j)
    (identities : ∀ i, TypedHasFormula (L := L) (TRel.ident X i))
    (letters : ∀ i j (a : Letter i j), TypedHasFormula (L := L) (repr a))
    {i j : ι} (word : TypedWord Letter i j) :
    TypedHasFormula (L := L) (word.eval repr) := by
  induction word with
  | nil i => exact identities i
  | cons a tail ih => exact (letters _ _ a).comp ih

end Typed

section NamedAtomicSource

variable {ι : Type u} {X : ι → Type v} (S : AtomicSource.{u,v,w} ι X)

/-- Exactly the original named sorts and equality-inclusive optional pair colours. -/
inductive NamedSymbol : ℕ → Type (max u w) where
  | sortName : ι → NamedSymbol 1
  | pairName : (i j : ι) → Option (S.Atom i j) → NamedSymbol 2

abbrev namedLanguage : FirstOrder.Language.{0,max u w} where
  Functions _ := Empty
  Relations := NamedSymbol S

instance namedStructure : (namedLanguage S).Structure (Sigma X) where
  funMap f := Empty.elim f
  RelMap name args := match name with
    | .sortName i => (args 0).1 = i
    | .pairName i j c => taggedRelation (fun x : X i => fun y : X j => S.colour x y = c)
        (args 0) (args 1)

def symbolCode {n : ℕ} : NamedSymbol S n →
    ι ⊕ (Σ i, Σ j, Option (S.Atom i j))
  | .sortName i => Sum.inl i
  | .pairName i j c => Sum.inr ⟨i, j, c⟩

theorem symbolCode_injective (n : ℕ) : Function.Injective (@symbolCode _ _ S n) := by
  intro a b h
  cases a with
  | sortName i =>
    cases b with
    | sortName j =>
      have equal : i = j := Sum.inl.inj h
      subst j
      rfl
  | pairName i j c =>
    cases b with
    | pairName k l d =>
      have equal : (⟨i, j, c⟩ : Σ i, Σ j, Option (S.Atom i j)) = ⟨k, l, d⟩ := Sum.inr.inj h
      cases equal
      rfl

/-- The intended source signature is actually finite at every arity. -/
instance finiteNamedSymbol (n : ℕ) : Finite (NamedSymbol S n) := by
  letI := S.finiteSort
  letI := S.finiteAtom
  exact Finite.of_injective (symbolCode S) (symbolCode_injective S n)

/-- All relation symbols together form a finite set, not merely each arity. -/
instance finiteTotalNamedSymbols : Finite (Σ n, NamedSymbol S n) := by
  letI := S.finiteSort
  letI := S.finiteAtom
  let code : (Σ n, NamedSymbol S n) → ι ⊕ (Σ i, Σ j, Option (S.Atom i j)) :=
    fun name => symbolCode S name.2
  apply Finite.of_injective code
  rintro ⟨n, a⟩ ⟨m, b⟩ h
  cases a with
  | sortName i =>
    cases b with
    | sortName j =>
      have equal : i = j := Sum.inl.inj h
      subst j
      rfl
    | pairName k l c => cases h
  | pairName i j c =>
    cases b with
    | sortName k => cases h
    | pairName k l d =>
      have equal : (⟨i, j, c⟩ : Σ i, Σ j, Option (S.Atom i j)) = ⟨k, l, d⟩ := Sum.inr.inj h
      cases equal
      rfl

def pairFormula {i j : ι} (c : Option (S.Atom i j)) :
    (namedLanguage S).Formula (Fin 2) :=
  FirstOrder.Language.Relations.formula₂ (L := namedLanguage S)
    (NamedSymbol.pairName i j c) (.var 0) (.var 1)

theorem pairFormula_realize {i j : ι} (c : Option (S.Atom i j)) (p q : Sigma X) :
    (pairFormula S c).Realize ![p, q] ↔
      taggedRelation (fun x : X i => fun y : X j => S.colour x y = c) p q := by
  rw [pairFormula, Formula.realize_rel₂]
  rfl

/-- The optional none name adds no new relation: it is the actual logical
diagonal with its two original sort guards. -/
theorem pairFormula_none_realize {i j : ι} (p q : Sigma X) :
    (pairFormula S (i := i) (j := j) none).Realize ![p, q] ↔
      p = q ∧ p.1 = i ∧ q.1 = j := by
  rw [pairFormula_realize]
  constructor
  · rintro ⟨x, y, rfl, rfl, colour⟩
    exact ⟨(S.colour_none_iff x y).mp colour, rfl, rfl⟩
  · rintro ⟨rfl, hi, hj⟩
    rcases p with ⟨k, x⟩
    dsimp at hi hj
    subst i
    subst j
    exact ⟨x, x, rfl, rfl, (S.colour_none_iff x x).mpr rfl⟩

/-- A literal FINITE disjunction of named pair colours actually occurring in R.
No invariant-to-definable oracle is a field or premise of this construction. -/
noncomputable def sourceFormula {i j : ι} (R : TRel X i j) :
    (namedLanguage S).Formula (Fin 2) := by
  letI := S.finiteAtom i j
  exact Formula.iSup (fun c : {c : Option (S.Atom i j) // c ∈ S.rawSupport R} =>
    pairFormula S c.val)

variable {G : Type z} [Group G] [∀ i, MulAction G (X i)]

/-- C13: actual finite named pair orbitals discharge the separate formula gate.
Pair transitivity is derived from the unchanged original homogeneous-source API.
The formula is parameter-free on the actual tagged original structure. -/
theorem sourceFormula_realize (H : HomogeneousSource S G) {i j : ι}
    (R : TRel X i j) (invariant : TRel.Invariant (G := G) R)
    (p q : Sigma X) :
    (sourceFormula S R).Realize ![p, q] ↔ taggedRelation R p q := by
  letI := S.finiteAtom i j
  simp only [sourceFormula, Formula.realize_iSup]
  constructor
  · rintro ⟨c, hc⟩
    obtain ⟨x, y, rfl, rfl, colour⟩ := (pairFormula_realize S c.val p q).mp hc
    obtain ⟨a, b, hab, hcol⟩ := c.property
    obtain ⟨g, hgx, hgy⟩ :=
      S.pair_homogeneous_of_homogeneous H a x b y (hcol.trans colour.symm)
    exact ⟨x, y, rfl, rfl, by simpa only [hgx, hgy] using invariant g a b hab⟩
  · rintro ⟨x, y, rfl, rfl, hr⟩
    refine ⟨⟨S.colour x y, x, y, hr, rfl⟩, ?_⟩
    exact (pairFormula_realize S (S.colour x y) ⟨i, x⟩ ⟨j, y⟩).mpr
      ⟨x, y, rfl, rfl, rfl⟩

theorem source_invariant_has_formula (H : HomogeneousSource S G) {i j : ι}
    (R : TRel X i j) (invariant : TRel.Invariant (G := G) R) :
    TypedHasFormula (L := namedLanguage S) R :=
  ⟨sourceFormula S R, sourceFormula_realize S H R invariant⟩

/-- Identity/empty-prefix formulas, with the actual original sort retained. -/
theorem source_identity_has_formula (H : HomogeneousSource S G) (i : ι) :
    TypedHasFormula (L := namedLanguage S) (TRel.ident X i) := by
  apply source_invariant_has_formula S H
  intro g x y equal
  exact congrArg (fun x : X i => g • x) equal

/-- C25 instantiated for every finite typed prefix in the intended source. -/
theorem source_typedWord_has_formula (H : HomogeneousSource S G)
    {Letter : ι → ι → Type*} (repr : ∀ {i j}, Letter i j → TRel X i j)
    (invariant : ∀ i j (a : Letter i j), TRel.Invariant (G := G) (repr a))
    {i j : ι} (word : TypedWord Letter i j) :
    TypedHasFormula (L := namedLanguage S) (word.eval repr) :=
  typedWord_has_formula repr (source_identity_has_formula S H)
    (fun i j a => source_invariant_has_formula S H (repr a) (invariant i j a)) word

/-- C13/C25: every actual prefix and every definable base/coarsening relation
produce their literal transported relation by first-order composition. -/
theorem source_prefix_transport_has_formula (H : HomogeneousSource S G)
    {Letter : ι → ι → Type*} (repr : ∀ {i j}, Letter i j → TRel X i j)
    (invariant : ∀ i j (a : Letter i j), TRel.Invariant (G := G) (repr a))
    {i j : ι} (word : TypedWord Letter i j) (E : TRel X i i)
    (baseFormula : TypedHasFormula (L := namedLanguage S) E) :
    TypedHasFormula (L := namedLanguage S)
      (TRel.comp (TRel.converse (word.eval repr)) (TRel.comp E (word.eval repr))) :=
  typed_transport_has_formula (source_typedWord_has_formula S H repr invariant word) baseFormula

end NamedAtomicSource
end CCO.QuotientTransport.Definability
