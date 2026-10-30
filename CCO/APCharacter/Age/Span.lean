import CCO.APCharacter.Age.Charts
import Mathlib.Data.Set.Finite.Range

/-! The formal union of two marked complete legs over their prescribed
common base. It is a set-theoretic free union only; its eventual old or
marked realization may identify additional cross-leg points. -/
universe u v w
namespace CCO.APCharacter.Age.Span
variable {A B C : Type} (f : A ↪ B) (g : A ↪ C)
noncomputable section
abbrev Carrier (_f : A ↪ B) (g : A ↪ C) := B ⊕ {c : C // c ∉ Set.range g}
def left : B ↪ Carrier f g := Function.Embedding.inl

def rightFun (c : C) : Carrier f g := by
  classical
  classical
  exact if h : c ∈ Set.range g then Sum.inl (f (Classical.choose h)) else Sum.inr ⟨c,h⟩

theorem right_base (a : A) : rightFun f g (g a) = Sum.inl (f a) := by
  classical
  have h : g a ∈ Set.range g := ⟨a,rfl⟩
  rw [rightFun,dite_eq_left h]
  exact congrArg (fun z => Sum.inl (f z)) (g.injective (Classical.choose_spec h))

def right : C ↪ Carrier f g where
  toFun := rightFun f g
  inj' := by
    classical
  classical
    intro c d h
    by_cases hc : c ∈ Set.range g <;> by_cases hd : d ∈ Set.range g
    · simp only [rightFun,dite_eq_left hc,dite_eq_left hd] at h
      have he := f.injective (Sum.inl.inj h)
      exact (Classical.choose_spec hc).symm.trans
        ((congrArg g he).trans (Classical.choose_spec hd))
    · simp only [rightFun,dite_eq_left hc,dite_eq_right hd] at h
      cases h
    · simp only [rightFun,dite_eq_right hc,dite_eq_left hd] at h
      cases h
    · simp only [rightFun,dite_eq_right hc,dite_eq_right hd] at h
      exact congrArg Subtype.val (Sum.inr.inj h)

theorem commute (a : A) : left f g (f a) = right f g (g a) :=
  (right_base f g a).symm

theorem covers (x : Carrier f g) :
    (∃ b, left f g b = x) ∨ ∃ c, right f g c = x := by
  classical
  cases x with
  | inl b => exact Or.inl ⟨b,rfl⟩
  | inr c =>
    apply Or.inr
    exact ⟨c.val,by change rightFun f g c.val = _; rw [rightFun,dite_eq_right c.property]⟩

theorem overlap (b : B) (c : C) : left f g b = right f g c ↔
    ∃ a, f a = b ∧ g a = c := by
  classical
  constructor
  · intro h
    by_cases hc : c ∈ Set.range g
    · rw [show right f g c = rightFun f g c from rfl,rightFun,dite_eq_left hc] at h
      exact ⟨Classical.choose hc,(Sum.inl.inj h).symm,Classical.choose_spec hc⟩
    · rw [show right f g c = rightFun f g c from rfl,rightFun,dite_eq_right hc] at h
      cases h
  · rintro ⟨a,rfl,rfl⟩
    exact commute f g a

variable {ι : Type u} {X : ι → Type v} {S : AtomicSource.{u,v,w} ι X}
variable (p : B → Sigma X) (q : C → Sigma X) (b : B → Bit) (c : C → Bit)
def point : Carrier f g → Sigma X := Sum.elim p (fun z => q z.val)
def bits : Carrier f g → Bit := Sum.elim b (fun z => c z.val)

@[simp] theorem point_left (x : B) : point f g p q (left f g x) = p x := rfl
@[simp] theorem bits_left (x : B) : bits f g b c (left f g x) = b x := rfl

include f in
theorem point_right (agree : ∀ a, p (f a) = q (g a)) (x : C) :
    point f g p q (right f g x) = q x := by
  classical
  by_cases hx : x ∈ Set.range g
  · change point f g p q (rightFun f g x) = _
    rw [rightFun,dite_eq_left hx]
    exact (agree (Classical.choose hx)).trans (congrArg q (Classical.choose_spec hx))
  · change point f g p q (rightFun f g x) = _
    rw [rightFun,dite_eq_right hx]
    rfl

include f in
theorem bits_right (agree : ∀ a, b (f a) = c (g a)) (x : C) :
    bits f g b c (right f g x) = c x := by
  classical
  by_cases hx : x ∈ Set.range g
  · change bits f g b c (rightFun f g x) = _
    rw [rightFun,dite_eq_left hx]
    exact (agree (Classical.choose hx)).trans (congrArg c (Classical.choose_spec hx))
  · change bits f g b c (rightFun f g x) = _
    rw [rightFun,dite_eq_right hx]
    rfl

def sameLeg (x y : Carrier f g) : Prop :=
  (∃ a b, left f g a = x ∧ left f g b = y) ∨
  (∃ a b, right f g a = x ∧ right f g b = y)

theorem sameLeg_symm {x y : Carrier f g} (h : sameLeg f g x y) : sameLeg f g y x := by
  classical
  rcases h with ⟨a,b,rfl,rfl⟩ | ⟨a,b,rfl,rfl⟩
  · exact Or.inl ⟨b,a,rfl,rfl⟩
  · exact Or.inr ⟨b,a,rfl,rfl⟩

variable [Finite B] [Finite C]

def diagram : PartialDiagram S (Carrier f g) := by
  classical
  exact {
    finite_type := inferInstance
    vertexSort x := (point f g p q x).1
    edge x y _ := if sameLeg f g x y then
      S.colour (point f g p q x).2 (point f g p q y).2 else none
    edge_reverse := by
      intro x y h a
      by_cases hxy : sameLeg f g x y
      · simp only [ite_eq_left hxy,ite_eq_left (sameLeg_symm f g hxy)]
        exact S.colour_swap _ _ a
      · have hyx : ¬sameLeg f g y x := fun h => hxy (sameLeg_symm f g h)
        simp only [ite_eq_right hxy,ite_eq_right hyx]
        simp }

/-- The old partial union already has a homomorphism; no marked homogeneity
or strong amalgamation is used to obtain its individual cycle witnesses. -/
def oldHom : DiagramHom (diagram (S := S) f g p q) where
  point x := (point f g p q x).2
  preserves_edge := by
    classical
    intro x y h a he
    dsimp only [diagram] at a he ⊢
    change (if sameLeg f g x y then _ else none) = some a at he
    by_cases hxy : sameLeg f g x y
    · rw [ite_eq_left hxy] at he
      exact he
    · rw [ite_eq_right hxy] at he
      cases he

theorem cycle_feasible (K : SimpleCycle (diagram (S := S) f g p q)) : CycleHom K := by
  refine ⟨fun a => (oldHom (S := S) f g p q).point (K.vertices a),?_⟩
  intro a col hcol
  exact (oldHom (S := S) f g p q).preserves_edge _ _ _ _ hcol

theorem localLegal (M : MaskData S)
    (hp : Legal S M p b) (hq : Legal S M q c)
    (ha : ∀ a, p (f a) = q (g a)) (hb : ∀ a, b (f a) = c (g a)) :
    M.LocalLegal (diagram (S := S) f g p q) (bits f g b c) := by
  classical
  constructor
  · intro x
    cases x with
    | inl x => exact hp.1 x
    | inr x => exact hq.1 x.val
  · intro x y h a he
    dsimp only [diagram] at a he ⊢
    have hxy : sameLeg f g x y := by
      by_contra hn
      change (if sameLeg f g x y then _ else none) = some a at he
      rw [ite_eq_right hn] at he
      cases he
    have hcol : S.colour (point f g p q x).2 (point f g p q y).2 = some a := by
      change (if sameLeg f g x y then _ else none) = some a at he
      rw [ite_eq_left hxy] at he
      exact he
    rw [← hcol]
    rcases hxy with ⟨x',y',rfl,rfl⟩ | ⟨x',y',rfl,rfl⟩
    · exact hp.2 x' y'
    · have hx := point_right f g p q ha x'
      have hy := point_right f g p q ha y'
      simp only [bits_right f g b c hb]
      exact Eq.mpr (congrArg₂ (fun s t : Sigma X =>
        M.allowed (S.colour s.2 t.2) (c x') (c y')) hx hy) (hq.2 x' y')

/-- Completeness is required only on each leg. Cross-leg nonedges may
collapse in the eventual marked completion. -/
theorem leg_complete {W : Type} (j : W ↪ Carrier f g) (r : W → Sigma X)
    (hr : Function.Injective r) (hj : ∀ x, point f g p q (j x) = r x)
    (hleg : ∀ x y, sameLeg f g (j x) (j y)) (x y : W) (hne : x ≠ y) :
    ∃ a, (diagram (S := S) f g p q).edge (j x) (j y) (j.injective.ne hne) = some a := by
  classical
  cases hc : S.colour (point f g p q (j x)).2 (point f g p q (j y)).2 with
  | some a =>
    exact ⟨a,by change (if sameLeg f g (j x) (j y) then _ else none) = _
                rw [ite_eq_left (hleg x y),hc]
                rfl⟩
  | none =>
    have he := (S.colour_none_iff _ _).mp hc
    change point f g p q (j x) = point f g p q (j y) at he
    rw [hj x,hj y] at he
    exact False.elim (hne (hr he))

end
end CCO.APCharacter.Age.Span
