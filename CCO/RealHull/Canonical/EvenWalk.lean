import CCO.RealHull.Geometry.GeneratedSupport
import Mathlib.Logic.Relation

/-! Original graph connectivity and its two parity sheets. No RAW-exactness
of the generated connected support is assumed. -/
universe v w t
namespace CCO.RealHull.Canonical
open CCO.RealHull.Geometry CCO.ParityHasse.Original
variable {M : Type v} (S : AtomicSource.{0,v,w} Unit (fun _ => M))

def gamma (p : Atom S) : Support S := generatedSupport S {p}
def evenSupport (p : Atom S) : Support S := generatedSupport S (square S p)
def Edge (p : Atom S) (x y : M) : Prop := col S x y = some p
def Walk (p : Atom S) : M → M → Prop := Relation.ReflTransGen (Edge S p)
def TwoStep (p : Atom S) (x z : M) : Prop := ∃ y, Edge S p x y ∧ Edge S p y z
def EvenWalk (p : Atom S) : M → M → Prop := Relation.ReflTransGen (TwoStep S p)

theorem edge_symm {p : Atom S} {x y : M} (h : Edge S p x y) : Edge S p y x :=
  (col_symm S y x).trans h

theorem twoStep_symm {p : Atom S} {x y : M} (h : TwoStep S p x y) :
    TwoStep S p y x := by
  obtain ⟨z,hxz,hzy⟩ := h
  exact ⟨z,edge_symm S hzy,edge_symm S hxz⟩

private theorem rtc_symm {X : Type*} {r : X → X → Prop}
    (hs : ∀ {x y}, r x y → r y x) {x y : X}
    (h : Relation.ReflTransGen r x y) : Relation.ReflTransGen r y x := by
  induction h with
  | refl => exact .refl
  | tail hxy hyz ih => exact ih.head (hs hyz)

theorem walk_symm {p : Atom S} {x y : M} (h : Walk S p x y) : Walk S p y x :=
  rtc_symm (edge_symm S) h

theorem evenWalk_symm {p : Atom S} {x y : M} (h : EvenWalk S p x y) : EvenWalk S p y x :=
  rtc_symm (twoStep_symm S) h

/-- Adding one p-edge at either end of an even walk keeps the length even. -/
theorem evenWalk_sandwich {p : Atom S} {a b c d : M}
    (hab : Edge S p a b) (hbc : EvenWalk S p b c) (hcd : Edge S p c d) :
    EvenWalk S p a d := by
  induction hbc generalizing d with
  | refl => exact .single ⟨b,hab,hcd⟩
  | @tail c e hw hce ih =>
    obtain ⟨m,hcm,hme⟩ := hce
    exact (ih hcm).trans (.single ⟨e,hme,hcd⟩)

/-- Literal parity decomposition of an ordinary finite walk. -/
theorem walk_parity {p : Atom S} {x y : M} (h : Walk S p x y) :
    EvenWalk S p x y ∨ ∃ z, EvenWalk S p x z ∧ Edge S p z y := by
  induction h with
  | refl => exact Or.inl .refl
  | tail hxy hyz ih =>
    rcases ih with he | ⟨u,heu,huy⟩
    · exact Or.inr ⟨_,he,hyz⟩
    · exact Or.inl (heu.trans (.single ⟨_,huy,hyz⟩))

/-- Every component is covered by the two even classes of the endpoints of
one p-edge. They may coincide, giving the non-bipartite case. -/
theorem two_sheet_cover {p : Atom S} {x y z : M} (hxy : Edge S p x y)
    (hxz : Walk S p x z) : EvenWalk S p x z ∨ EvenWalk S p y z := by
  rcases walk_parity S hxz with he | ⟨u,hxu,huz⟩
  · exact Or.inl he
  · exact Or.inr (evenWalk_sandwich S (edge_symm S hxy) hxu huz)

variable {G : Type t} [Group G] [MulAction G M]
variable (H : HomogeneousSource S G)
include H

theorem walk_invariant (g : G) {p : Atom S} {x y : M} (h : Walk S p x y) :
    Walk S p (g • x) (g • y) := by
  exact h.lift (g • ·) (fun _ _ hc => (col_invariant S H g _ _).trans hc)

theorem evenWalk_invariant (g : G) {p : Atom S} {x y : M} (h : EvenWalk S p x y) :
    EvenWalk S p (g • x) (g • y) := by
  exact h.lift (g • ·) (fun _ _ ⟨z,hxz,hzy⟩ =>
    ⟨g • z,(col_invariant S H g _ _).trans hxz,(col_invariant S H g _ _).trans hzy⟩)

private theorem walk_colour (p : Atom S) : ColourInvariant S () (Walk S p) := by
  intro x y x' y' hc
  have go : ∀ x y x' y', col S x y = col S x' y' → Walk S p x y → Walk S p x' y' := by
    intro a b a' b' hab hw
    obtain ⟨g,hga,hgb⟩ := S.pair_homogeneous_of_homogeneous H a a' b b' hab
    simpa only [hga,hgb] using walk_invariant S H g hw
  exact ⟨go _ _ _ _ hc,go _ _ _ _ hc.symm⟩

private theorem evenWalk_colour (p : Atom S) : ColourInvariant S () (EvenWalk S p) := by
  intro x y x' y' hc
  have go : ∀ x y x' y', col S x y = col S x' y' → EvenWalk S p x y → EvenWalk S p x' y' := by
    intro a b a' b' hab hw
    obtain ⟨g,hga,hgb⟩ := S.pair_homogeneous_of_homogeneous H a a' b b' hab
    simpa only [hga,hgb] using evenWalk_invariant S H g hw
  exact ⟨go _ _ _ _ hc,go _ _ _ _ hc.symm⟩

def walkEquivalence (p : Atom S) : ColourEq S () :=
  ⟨⟨Walk S p,⟨fun _ => .refl,walk_symm S,Relation.ReflTransGen.trans⟩⟩,walk_colour S H p⟩

def evenWalkEquivalence (p : Atom S) : ColourEq S () :=
  ⟨⟨EvenWalk S p,⟨fun _ => .refl,evenWalk_symm S,Relation.ReflTransGen.trans⟩⟩,
    evenWalk_colour S H p⟩

/-- Generated original p-support is exactly ordinary p-walk connectivity. -/
theorem gamma_iff_walk (p : Atom S) (x y : M) :
    supportEquiv S (gamma S p) x y ↔ Walk S p x y := by
  constructor
  · intro hxy
    have hgen := generated_plus_le S ({p} : Set (Atom S))
      (equivalenceSupport S (walkEquivalence S H p)) (by
        intro a ha
        have hap : a = p := Set.mem_singleton_iff.mp ha
        subst a
        obtain ⟨u,v,huv⟩ := colour_realized S (some p)
        exact ⟨u,v,Relation.ReflTransGen.single huv,huv⟩)
    exact (mem_plus_diversitySupport S (walkEquivalence S H p) x y).mp (hgen hxy)
  · intro hxy
    induction hxy with
    | refl => exact (supportEquiv S (gamma S p)).val.refl _
    | tail hw hedge ih =>
      apply (supportEquiv S (gamma S p)).val.trans ih
      change col S _ _ ∈ plus S (gamma S p).val
      rw [hedge]
      exact (some_mem_plus S _ p).mpr (subset_generated S {p} (Set.mem_singleton p))

/-- Generated square support is exactly even p-walk connectivity. -/
theorem evenSupport_iff_evenWalk (p : Atom S) (x y : M) :
    supportEquiv S (evenSupport S p) x y ↔ EvenWalk S p x y := by
  constructor
  · intro hxy
    have hgen := generated_plus_le S (square S p)
      (equivalenceSupport S (evenWalkEquivalence S H p)) (by
        intro a ha
        obtain ⟨u,z,v,huz,hzv,huv⟩ := ha
        exact ⟨u,v,Relation.ReflTransGen.single ⟨z,huz,hzv⟩,huv⟩)
    exact (mem_plus_diversitySupport S (evenWalkEquivalence S H p) x y).mp (hgen hxy)
  · intro hxy
    induction hxy with
    | refl => exact (supportEquiv S (evenSupport S p)).val.refl _
    | tail hw hstep ih =>
      apply (supportEquiv S (evenSupport S p)).val.trans ih
      obtain ⟨z,huz,hzv⟩ := hstep
      change col S _ _ ∈ plus S (evenSupport S p).val
      cases hc : col S _ _ with
      | none => exact none_mem_plus S _
      | some a =>
        apply (some_mem_plus S _ a).mpr
        exact subset_generated S (square S p) ⟨_,z,_,huz,hzv,hc⟩

/-- In one p-component, any three points have two endpoints in the same
parity sheet. This is a finite two-sheet argument, not a Ramsey theorem. -/
theorem three_points_even_pair {p : Atom S} {x y z : M}
    (hxy : Walk S p x y) (hxz : Walk S p x z) :
    EvenWalk S p x y ∨ EvenWalk S p y z ∨ EvenWalk S p x z := by
  obtain ⟨u,hu⟩ := colour_serial S H (some p) x
  rcases two_sheet_cover S hu hxy with h | hy
  · exact Or.inl h
  rcases two_sheet_cover S hu hxz with h | hz
  · exact Or.inr (Or.inr h)
  · exact Or.inr (Or.inl ((evenWalk_symm S hy).trans hz))

/-- A looped old colour in a p-component cannot cross its odd sheet. -/
theorem looped_mem_even {p r : Atom S} (hr : r ∈ square S r)
    (hΓ : r ∈ (gamma S p).val) : r ∈ (evenSupport S p).val := by
  obtain ⟨x,y,z,hxy,hyz,hxz⟩ := hr
  have hx : Walk S p x y := (gamma_iff_walk S H p x y).mp (by
    change col S x y ∈ plus S (gamma S p).val
    rw [Set.mem_singleton_iff.mp hxy]
    exact (some_mem_plus S _ r).mpr hΓ)
  have hz : Walk S p x z := (gamma_iff_walk S H p x z).mp (by
    change col S x z ∈ plus S (gamma S p).val
    rw [hxz]
    exact (some_mem_plus S _ r).mpr hΓ)
  rcases three_points_even_pair S H hx hz with he | he | he
  · have hh := (evenSupport_iff_evenWalk S H p x y).mpr he
    change col S x y ∈ plus S (evenSupport S p).val at hh
    rw [Set.mem_singleton_iff.mp hxy] at hh
    exact (some_mem_plus S _ r).mp hh
  · have hh := (evenSupport_iff_evenWalk S H p y z).mpr he
    change col S y z ∈ plus S (evenSupport S p).val at hh
    rw [Set.mem_singleton_iff.mp hyz] at hh
    exact (some_mem_plus S _ r).mp hh
  · have hh := (evenSupport_iff_evenWalk S H p x z).mpr he
    change col S x z ∈ plus S (evenSupport S p).val at hh
    rw [hxz] at hh
    exact (some_mem_plus S _ r).mp hh

/-- Actual even classes INSIDE one actual p-component. -/
def evenSheets (p : Atom S) (x : M) :
    Setoid {y : M // supportEquiv S (gamma S p) x y} :=
  Setoid.comap Subtype.val (evenWalkEquivalence S H p).val

/-- The quotient is proved finite before its natural cardinal is bounded.
It consists of the even sheets of the two endpoints of any p-edge. -/
theorem even_sheet_index_le_two (p : Atom S) (x : M) :
    Finite (Quotient (evenSheets S H p x)) ∧
      Nat.card (Quotient (evenSheets S H p x)) ≤ 2 := by
  obtain ⟨y,hxy⟩ := colour_serial S H (some p) x
  have hy : supportEquiv S (gamma S p) x y :=
    (gamma_iff_walk S H p x y).mpr (.single hxy)
  let x₀ : {z : M // supportEquiv S (gamma S p) x z} :=
    ⟨x,(supportEquiv S (gamma S p)).val.refl x⟩
  let x₁ : {z : M // supportEquiv S (gamma S p) x z} := ⟨y,hy⟩
  let f : Bool → Quotient (evenSheets S H p x) :=
    fun b => Quotient.mk _ (if b then x₁ else x₀)
  have hf : Function.Surjective f := by
    intro q
    induction q using Quotient.inductionOn with
    | h z =>
      have hw := (gamma_iff_walk S H p x z.val).mp z.property
      rcases two_sheet_cover S hxy hw with h₀ | h₁
      · refine ⟨false,?_⟩
        change Quotient.mk _ x₀ = Quotient.mk _ z
        exact Quotient.sound h₀
      · refine ⟨true,?_⟩
        change Quotient.mk _ x₁ = Quotient.mk _ z
        exact Quotient.sound h₁
  exact ⟨Finite.of_surjective f hf,by
    simpa only [Nat.card_eq_fintype_card,Fintype.card_bool] using
      Nat.card_le_card_of_surjective f hf⟩

end CCO.RealHull.Canonical
