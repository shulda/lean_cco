import Mathlib.Algebra.Group.Action.Basic

/-!
# Equality-inclusive typed represented relations

The sorts are indices of a family of *actual* real carriers.  A RAW relation
is a predicate on the two carriers, not a set of formal colours.  In
particular, `ident` is genuine equality and `top` allows every real pair.
-/

universe u v w

namespace CCO

abbrev TRel {ι : Type u} (X : ι → Type v) (i j : ι) : Type v :=
  X i → X j → Prop

namespace TRel

variable {ι : Type u} {X : ι → Type v}
variable {i j k l : ι}

def ident (X : ι → Type v) (i : ι) : TRel X i i :=
  fun x y => x = y

def top (X : ι → Type v) (i j : ι) : TRel X i j :=
  fun _ _ => True

def comp (R : TRel X i j) (S : TRel X j k) : TRel X i k :=
  fun x z => ∃ y, R x y ∧ S y z

def converse (R : TRel X i j) : TRel X j i :=
  fun y x => R x y

def Nonempty (R : TRel X i j) : Prop :=
  ∃ x y, R x y

def Serial (R : TRel X i j) : Prop :=
  ∀ x, ∃ y, R x y

def Coserial (R : TRel X i j) : Prop :=
  ∀ y, ∃ x, R x y

theorem comp_assoc (R : TRel X i j) (S : TRel X j k)
    (T : TRel X k l) :
    comp (comp R S) T = comp R (comp S T) := by
  funext x z
  apply propext
  constructor
  · rintro ⟨y, ⟨w, hwR, hwS⟩, hyT⟩
    exact ⟨w, hwR, y, hwS, hyT⟩
  · rintro ⟨w, hwR, y, hyS, hyT⟩
    exact ⟨y, ⟨w, hwR, hyS⟩, hyT⟩

theorem comp_ident (R : TRel X i j) :
    comp R (ident X j) = R := by
  funext x y
  apply propext
  constructor
  · rintro ⟨z, h, rfl⟩
    exact h
  · intro h
    exact ⟨y, h, rfl⟩

theorem ident_comp (R : TRel X i j) :
    comp (ident X i) R = R := by
  funext x y
  apply propext
  constructor
  · rintro ⟨z, rfl, h⟩
    exact h
  · intro h
    exact ⟨x, rfl, h⟩

theorem converse_converse (R : TRel X i j) :
    converse (converse R) = R := rfl

theorem converse_comp (R : TRel X i j) (S : TRel X j k) :
    converse (comp R S) = comp (converse S) (converse R) := by
  funext z x
  apply propext
  constructor
  · rintro ⟨y, hR, hS⟩
    exact ⟨y, hS, hR⟩
  · rintro ⟨y, hS, hR⟩
    exact ⟨y, hR, hS⟩

theorem comp_mono {R R' : TRel X i j} {S S' : TRel X j k}
    (hR : ∀ x y, R x y → R' x y)
    (hS : ∀ y z, S y z → S' y z) :
    ∀ x z, comp R S x z → comp R' S' x z := by
  rintro x z ⟨y, hxy, hyz⟩
  exact ⟨y, hR x y hxy, hS y z hyz⟩

theorem top_comp (R : TRel X j k) (h : Coserial R) :
    comp (top X i j) R = top X i k := by
  funext x z
  apply propext
  constructor
  · intro _
    trivial
  · intro _
    obtain ⟨y, hyz⟩ := h z
    exact ⟨y, trivial, hyz⟩

theorem comp_top (R : TRel X i j) (h : Serial R) :
    comp R (top X j k) = top X i k := by
  funext x z
  apply propext
  constructor
  · intro _
    trivial
  · intro _
    obtain ⟨y, hxy⟩ := h x
    exact ⟨y, hxy, trivial⟩

variable {G : Type*} [Group G]
variable [MulAction G (X i)] [MulAction G (X j)]

def Invariant (R : TRel X i j) : Prop :=
  ∀ (g : G) x y, R x y → R (g • x) (g • y)

theorem invariant_serial (R : TRel X i j)
    (trans : ∀ a b : X i, ∃ g : G, g • a = b)
    (hInv : Invariant (G := G) R) (hR : Nonempty R) :
    Serial R := by
  obtain ⟨a, b, hab⟩ := hR
  intro x
  obtain ⟨g, hg⟩ := trans a x
  refine ⟨g • b, ?_⟩
  rw [← hg]
  exact hInv g a b hab

theorem invariant_coserial (R : TRel X i j)
    (trans : ∀ a b : X j, ∃ g : G, g • a = b)
    (hInv : Invariant (G := G) R) (hR : Nonempty R) :
    Coserial R := by
  obtain ⟨a, b, hab⟩ := hR
  intro y
  obtain ⟨g, hg⟩ := trans b y
  refine ⟨g • a, ?_⟩
  rw [← hg]
  exact hInv g a b hab

end TRel

/-! A word is a genuinely composable sequence of typed letters.
There is one empty word only at a loop sort; it evaluates to real identity. -/
inductive TypedWord {ι : Type u} (L : ι → ι → Type w) :
    ι → ι → Type (max u w) where
  | nil (i : ι) : TypedWord L i i
  | cons {i j k : ι} (a : L i j) (tail : TypedWord L j k) : TypedWord L i k

namespace TypedWord

variable {ι : Type u} {L : ι → ι → Type w} {X : ι → Type v}

def append {i j k : ι} (u : TypedWord L i j)
    (v : TypedWord L j k) : TypedWord L i k :=
  match u with
  | .nil _ => v
  | .cons a tail => .cons a (append tail v)

def eval (repr : ∀ {i j : ι}, L i j → TRel X i j)
    {i j : ι} : TypedWord L i j → TRel X i j
  | .nil i => TRel.ident X i
  | .cons a tail => TRel.comp (repr a) (eval repr tail)

theorem eval_append (repr : ∀ {i j : ι}, L i j → TRel X i j)
    {i j k : ι} (u : TypedWord L i j) (v : TypedWord L j k) :
    eval repr (append u v) =
      TRel.comp (eval repr u) (eval repr v) := by
  induction u with
  | nil _ =>
      simp only [append, eval, TRel.ident_comp]
  | cons a tail ih =>
      simp only [append, eval, ih, TRel.comp_assoc]

end TypedWord

end CCO
