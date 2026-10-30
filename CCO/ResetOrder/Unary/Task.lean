import CCO.ResetOrder.Unary.FiniteAge

/-! Actual task structures, with every old partial-unary domain retained.
The full Ramsey language may add additional unary functions. -/
universe u v
namespace CCO.ResetOrder.Unary
open CCO.ResetOrder.Unary.Primitive

structure Fibres (L : Signature.{u}) where
  Allowed : Age.{u,v} L
  hereditary : Hereditary Allowed
  same : (A : Object.{u,v} L) → A.Carrier → A.Carrier → Prop
  reset : (A : Object.{u,v} L) → A.Carrier → A.Carrier → Prop
  same_symm : ∀ A, Allowed A → ∀ x y, same A x y → same A y x
  same_trans : ∀ A, Allowed A → ∀ x y z, same A x y → same A y z → same A x z
  same_natural : ∀ {A B} (f : A.Emb B) x y,
    same B (f.point x) (f.point y) ↔ same A x y
  reset_natural : ∀ {A B} (f : A.Emb B) x y,
    reset B (f.point x) (f.point y) ↔ reset A x y
  reset_symm : ∀ A, Allowed A → ∀ x y, reset A x y → reset A y x
  reset_ne : ∀ A, Allowed A → ∀ x y, reset A x y → x ≠ y
  reset_same : ∀ A, Allowed A → ∀ x y, reset A x y → same A x y

structure FibreOrder {L : Signature.{u}} (P : Fibres.{u,v} L) (A : Object.{u,v} L) where
  valid : P.Allowed A
  lt : A.Carrier → A.Carrier → Prop
  same : ∀ {x y}, lt x y → P.same A x y
  irrefl : ∀ x, ¬ lt x x
  trans : ∀ {x y z}, lt x y → lt y z → lt x z
  total : ∀ {x y}, P.same A x y → x ≠ y → lt x y ∨ lt y x

structure TaskObject {L : Signature.{u}} (P : Fibres.{u,v} L) where
  old : Object.{u,v} L
  order : FibreOrder P old

structure TaskHom {L : Signature.{u}} {P : Fibres.{u,v} L} (A B : TaskObject P) where
  old : A.old.Emb B.old
  order_iff : ∀ x y, B.order.lt (old.point x) (old.point y) ↔ A.order.lt x y

def taskIdentity {L : Signature.{u}} {P : Fibres.{u,v} L} (A : TaskObject P) : TaskHom A A where
  old := identity A.old.data
  order_iff _ _ := Iff.rfl

def taskCompose {L : Signature.{u}} {P : Fibres.{u,v} L} {A B C : TaskObject P}
    (g : TaskHom B C) (f : TaskHom A B) : TaskHom A C where
  old := compose g.old f.old
  order_iff x y := (g.order_iff _ _).trans (f.order_iff x y)

def reverse {L : Signature.{u}} {P : Fibres.{u,v} L} (A : TaskObject P) : TaskObject P where
  old := A.old
  order := {
    valid := A.order.valid
    lt := fun x y => A.order.lt y x
    same := fun h => P.same_symm A.old A.order.valid _ _ (A.order.same h)
    irrefl := A.order.irrefl
    trans := fun hxy hyz => A.order.trans hyz hxy
    total := fun h hn => A.order.total (P.same_symm _ A.order.valid _ _ h) (Ne.symm hn) }

def taskHomOfPreserves {L : Signature.{u}} {P : Fibres.{u,v} L}
    {A B : TaskObject P} (f : A.old.Emb B.old)
    (preserves : ∀ x y, A.order.lt x y → B.order.lt (f.point x) (f.point y)) : TaskHom A B where
  old := f
  order_iff x y := by
    constructor
    · intro h
      have hsame : P.same A.old x y := (P.same_natural f x y).1 (B.order.same h)
      have hne : x ≠ y := by intro he; subst y; exact B.order.irrefl _ h
      obtain ha | ha := A.order.total hsame hne
      · exact ha
      · exact False.elim (B.order.irrefl _ (B.order.trans h (preserves _ _ ha)))
    · exact preserves x y

def taskInduce {L : Signature.{u}} {P : Fibres.{u,v} L} (A : TaskObject P)
    (S : Set A.old.Carrier) (hS : A.old.data.IsClosed S) : TaskObject P where
  old := A.old.induce S hS
  order := {
    valid := P.hereditary A.order.valid ⟨A.old.inclusion S hS⟩
    lt := fun x y => A.order.lt x.val y.val
    same := fun h => (P.same_natural (A.old.inclusion S hS) _ _).1 (A.order.same h)
    irrefl := fun x => A.order.irrefl x.val
    trans := fun hxy hyz => A.order.trans hxy hyz
    total := fun h hn => A.order.total
      ((P.same_natural (A.old.inclusion S hS) _ _).2 h)
      (fun he => hn (Subtype.ext he)) }

def taskInclusion {L : Signature.{u}} {P : Fibres.{u,v} L} (A : TaskObject P)
    (S : Set A.old.Carrier) (hS : A.old.data.IsClosed S) : TaskHom (taskInduce A S hS) A where
  old := A.old.inclusion S hS
  order_iff _ _ := Iff.rfl

/-- Actual code interpretations; the law is relation-by-relation naturality,
not an assumed embedding, monochromatic source copy or EP provider. -/
structure TaskCodes {L : Signature.{u}} (P : Fibres.{u,v} L) where
  Symbol : ℕ → Type u
  value : (A : TaskObject P) → {n : ℕ} → Symbol n → (Fin n → A.old.Carrier) → Prop
  natural : ∀ {A B} (f : TaskHom A B) {n} (R : Symbol n) xs,
    value B R (f.old.point ∘ xs) ↔ value A R xs

structure ExtraLanguage (L : Signature.{u}) where
  Func : Type u
  Rel : Type u
  input : Func → L.Sorts
  output : Func → L.Sorts
  arity : Rel → ℕ
  argument : (R : Rel) → Fin (arity R) → L.Sorts

def ExtraLanguage.signature {L : Signature.{u}} (X : ExtraLanguage L) : Signature where
  Sorts := L.Sorts
  Func := L.Func ⊕ X.Func
  Rel := L.Rel ⊕ X.Rel
  input := Sum.elim L.input X.input
  output := Sum.elim L.output X.output
  arity := Sum.elim L.arity X.arity
  argument := fun R => match R with
    | .inl R => L.argument R
    | .inr R => X.argument R

structure FullObject {L : Signature.{u}} (P : Fibres.{u,v} L) (X : ExtraLanguage L) where
  task : TaskObject P
  func : X.Func → task.old.Carrier → Set task.old.Carrier
  functional : ∀ F x y z, y ∈ func F x → z ∈ func F x → y = z
  func_sorted : ∀ F x y, y ∈ func F x →
    task.old.data.sort x = X.input F ∧ task.old.data.sort y = X.output F
  rel : (R : X.Rel) → (Fin (X.arity R) → task.old.Carrier) → Prop
  rel_sorted : ∀ R xs, rel R xs → ∀i, task.old.data.sort (xs i) = X.argument R i

def FullObject.unary {L : Signature.{u}} {P : Fibres.{u,v} L} {X : ExtraLanguage L}
    (A : FullObject P X) : Structure X.signature A.task.old.Carrier where
  sort := A.task.old.data.sort
  func := Sum.elim A.task.old.data.func A.func
  functional F := by cases F with
    | inl F => exact A.task.old.data.functional F
    | inr F => exact A.functional F
  func_sorted F := by cases F with
    | inl F => exact A.task.old.data.func_sorted F
    | inr F => exact A.func_sorted F
  rel R := match R with
    | .inl R => A.task.old.data.rel R
    | .inr R => A.rel R
  rel_sorted R := by cases R with
    | inl R => exact A.task.old.data.rel_sorted R
    | inr R => exact A.rel_sorted R

structure FullHom {L : Signature.{u}} {P : Fibres.{u,v} L} {X : ExtraLanguage L}
    (A B : FullObject P X) where
  task : TaskHom A.task B.task
  map_func : ∀ F x y, y ∈ A.func F x → task.old.point y ∈ B.func F (task.old.point x)
  reflect_func : ∀ F x y, y ∈ B.func F (task.old.point x) →
    ∃z, z ∈ A.func F x ∧ task.old.point z = y
  rel_iff : ∀ R xs, B.rel R (task.old.point ∘ xs) ↔ A.rel R xs

abbrev FullHom.point {L : Signature.{u}} {P : Fibres.{u,v} L} {X : ExtraLanguage L}
    {A B : FullObject P X} (f : FullHom A B) := f.task.old.point

def FullHom.unary {L : Signature.{u}} {P : Fibres.{u,v} L} {X : ExtraLanguage L}
    {A B : FullObject P X} (f : FullHom A B) : Hom A.unary B.unary where
  point := f.point
  sort_eq := f.task.old.sort_eq
  injective := f.task.old.injective
  map_func F := by cases F with
    | inl F => exact f.task.old.map_func F
    | inr F => exact f.map_func F
  reflect_func F := by cases F with
    | inl F => exact f.task.old.reflect_func F
    | inr F => exact f.reflect_func F
  map_rel R := by cases R with
    | inl R => exact f.task.old.map_rel R
    | inr R => exact fun xs h => (f.rel_iff R xs).2 h
  reflect_rel R := by cases R with
    | inl R => exact f.task.old.reflect_rel R
    | inr R => exact fun xs h => (f.rel_iff R xs).1 h

def fullIdentity {L : Signature.{u}} {P : Fibres.{u,v} L} {X : ExtraLanguage L}
    (A : FullObject P X) : FullHom A A where
  task := taskIdentity A.task
  map_func _ _ _ h := h
  reflect_func _ _ y h := ⟨y,h,rfl⟩
  rel_iff _ _ := Iff.rfl

def fullCompose {L : Signature.{u}} {P : Fibres.{u,v} L} {X : ExtraLanguage L}
    {A B C : FullObject P X} (g : FullHom B C) (f : FullHom A B) : FullHom A C where
  task := taskCompose g.task f.task
  map_func F x y h := g.map_func F _ _ (f.map_func F x y h)
  reflect_func F x y h := by
    obtain ⟨b,hb,hby⟩ := g.reflect_func F _ y h
    obtain ⟨a,ha,hab⟩ := f.reflect_func F x b hb
    exact ⟨a,ha,(congrArg g.point hab).trans hby⟩
  rel_iff R xs := (g.rel_iff R _).trans (f.rel_iff R xs)

@[ext] theorem fullHom_ext {L : Signature.{u}} {P : Fibres.{u,v} L} {X : ExtraLanguage L}
    {A B : FullObject P X} {f g : FullHom A B} (h : ∀x, f.point x = g.point x) : f = g := by
  cases f with
  | mk f fm ff hf =>
    cases g with
    | mk g gm gf hg =>
      have he : f = g := by
        cases f with
        | mk f hf =>
          cases g with
          | mk g hg =>
            have he := hom_ext h
            cases he
            rfl
      cases he
      rfl

theorem fullClosed_old {L : Signature.{u}} {P : Fibres.{u,v} L} {X : ExtraLanguage L}
    {A : FullObject P X} {S : Set A.task.old.Carrier} (hS : A.unary.IsClosed S) :
    A.task.old.data.IsClosed S := fun F x hx _y hy => hS (.inl F) x hx hy

def fullInduce {L : Signature.{u}} {P : Fibres.{u,v} L} {X : ExtraLanguage L}
    (A : FullObject P X) (S : Set A.task.old.Carrier) (hS : A.unary.IsClosed S) : FullObject P X where
  task := taskInduce A.task S (fullClosed_old hS)
  func F x := {y | y.val ∈ A.func F x.val}
  functional F x y z hy hz := Subtype.ext (A.functional F x.val y.val z.val hy hz)
  func_sorted F x y hy := A.func_sorted F x.val y.val hy
  rel R xs := A.rel R (Subtype.val ∘ xs)
  rel_sorted R xs h := A.rel_sorted R (Subtype.val ∘ xs) h

def fullInclusion {L : Signature.{u}} {P : Fibres.{u,v} L} {X : ExtraLanguage L}
    (A : FullObject P X) (S : Set A.task.old.Carrier) (hS : A.unary.IsClosed S) :
    FullHom (fullInduce A S hS) A where
  task := taskInclusion A.task S (fullClosed_old hS)
  map_func _ _ _ h := h
  reflect_func F x y h := ⟨⟨y,hS (.inr F) x.val x.property h⟩,h,rfl⟩
  rel_iff _ _ := Iff.rfl

def reorder {L : Signature.{u}} {P : Fibres.{u,v} L} {X : ExtraLanguage L}
    (A : FullObject P X) (o : FibreOrder P A.task.old) : FullObject P X where
  task := ⟨A.task.old,o⟩
  func := A.func
  functional := A.functional
  func_sorted := A.func_sorted
  rel := A.rel
  rel_sorted := A.rel_sorted

def oldOfFullUnary {L : Signature.{u}} {P : Fibres.{u,v} L} {X : ExtraLanguage L}
    {A B : FullObject P X} (f : Hom A.unary B.unary) : A.task.old.Emb B.task.old where
  point := f.point
  injective := f.injective
  sort_eq := f.sort_eq
  map_func F := f.map_func (.inl F)
  reflect_func F := f.reflect_func (.inl F)
  map_rel R := f.map_rel (.inl R)
  reflect_rel R := f.reflect_rel (.inl R)

def fullHomOfUnaryPreserves {L : Signature.{u}} {P : Fibres.{u,v} L} {X : ExtraLanguage L}
    {A B : FullObject P X} (f : Hom A.unary B.unary)
    (h : ∀x y, A.task.order.lt x y → B.task.order.lt (f.point x) (f.point y)) : FullHom A B where
  task := taskHomOfPreserves (oldOfFullUnary f) h
  map_func F := f.map_func (.inr F)
  reflect_func F := f.reflect_func (.inr F)
  rel_iff R xs := ⟨f.reflect_rel (.inr R) xs,f.map_rel (.inr R) xs⟩

end CCO.ResetOrder.Unary
