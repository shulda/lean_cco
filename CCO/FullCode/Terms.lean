import CCO.FullCode.Basic

/-! Typed terms, their genuine partial graphs, and induced transport. -/
universe u v w
namespace CCO.FullCode
variable {L : Language.{u}} {V : Type v} {W : Type w}

inductive Term (L : Language.{u}) : L.Sorts → L.Sorts → Type u
  | id (s : L.Sorts) : Term L s s
  | app (F : L.Func) {s : L.Sorts} (t : Term L s (L.input F)) :
      Term L s (L.output F)

namespace Term
def eval (C : Structure L V) : {s t : L.Sorts} → Term L s t → V → Set V
  | _, _, .id _, x => {x}
  | _, _, .app F t, x => {y | ∃ z, z ∈ eval C t x ∧ y ∈ C.func F z}

theorem functional (C : Structure L V) {s t : L.Sorts} (a : Term L s t)
    (x : V) : (a.eval C x).Subsingleton := by
  induction a with
  | id => exact Set.subsingleton_singleton
  | app F a ih =>
    rintro y ⟨b, hb, hy⟩ z ⟨c, hc, hz⟩
    have hbc := ih hb hc
    exact C.functional F b y z hy (hbc ▸ hz)

theorem sorted (C : Structure L V) {s t : L.Sorts} (a : Term L s t)
    {x y : V} (hx : C.sort x = s) (hy : y ∈ a.eval C x) : C.sort y = t := by
  induction a with
  | id => exact (Set.mem_singleton_iff.mp hy) ▸ hx
  | app F a _ =>
    obtain ⟨z, _, hz⟩ := hy
    exact (C.func_sorted F z y hz).2

theorem transport {C : Structure L V} {D : Structure L W}
    (f : Structure.Embedding C D) {s t : L.Sorts} (a : Term L s t)
    (x : V) (y : W) :
    y ∈ a.eval D (f.point x) ↔ ∃ z, z ∈ a.eval C x ∧ f.point z = y := by
  induction a generalizing y with
  | id =>
    constructor
    · intro h; exact ⟨x, rfl, (Set.mem_singleton_iff.mp h).symm⟩
    · rintro ⟨z, hz, rfl⟩
      exact congrArg f.point (Set.mem_singleton_iff.mp hz)
  | app F a ih =>
    constructor
    · rintro ⟨b, hb, hy⟩
      obtain ⟨c, hc, hcb⟩ := (ih b).mp hb
      obtain ⟨z, hz, hzy⟩ := f.reflect_func F c y (hcb ▸ hy)
      exact ⟨z, ⟨c, hc, hz⟩, hzy⟩
    · rintro ⟨z, ⟨b, hb, hz⟩, rfl⟩
      exact ⟨f.point b, (ih _).mpr ⟨b, hb, rfl⟩, f.map_func F b z hz⟩

theorem map_iff {C : Structure L V} {D : Structure L W}
    (f : Structure.Embedding C D) {s t : L.Sorts} (a : Term L s t) (x y : V) :
    f.point y ∈ a.eval D (f.point x) ↔ y ∈ a.eval C x := by
  rw [a.transport f]
  constructor
  · rintro ⟨z, hz, hzy⟩
    exact (f.injective hzy) ▸ hz
  · intro hy; exact ⟨y, hy, rfl⟩

end Term

structure NormalForms (L : Language.{u}) where
  count : L.Sorts → L.Sorts → ℕ
  form : ∀ s t, Fin (count s t) → Term L s t
  normalize : ∀ {s t}, Term L s t → Fin (count s t)

def NormalForms.Valid (N : NormalForms L) (C : Structure L V) : Prop :=
  ∀ (s t : L.Sorts) (a : Term L s t) (x : V), C.sort x = s →
    a.eval C x = (N.form s t (N.normalize a)).eval C x

abbrev CoordinateTerm (L : Language.{u}) {n : ℕ} (ctx : Fin n → L.Sorts)
    (s : L.Sorts) := (j : Fin n) × Term L (ctx j) s

def CoordinateTerm.eval {n : ℕ} {ctx : Fin n → L.Sorts} {s : L.Sorts}
    (a : CoordinateTerm L ctx s) (C : Structure L V) (xs : Fin n → V) : Set V :=
  a.2.eval C (xs a.1)

inductive Formula (L : Language.{u}) {n : ℕ} (ctx : Fin n → L.Sorts) : Type u
  | truth : Formula L ctx
  | equal {s : L.Sorts} (a b : CoordinateTerm L ctx s) : Formula L ctx
  | unary (U : L.Unary) (a : CoordinateTerm L ctx (L.unarySort U)) : Formula L ctx
  | binary (R : L.Binary) (a : CoordinateTerm L ctx (L.leftSort R))
      (b : CoordinateTerm L ctx (L.rightSort R)) : Formula L ctx
  | neg (p : Formula L ctx) : Formula L ctx
  | conj (p q : Formula L ctx) : Formula L ctx

namespace Formula
def eval {n : ℕ} {ctx : Fin n → L.Sorts} (C : Structure L V) (xs : Fin n → V) :
    Formula L ctx → Prop
  | .truth => True
  | .equal a b => ∃ x, x ∈ a.eval C xs ∧ x ∈ b.eval C xs
  | .unary U a => ∃ x, x ∈ a.eval C xs ∧ C.unary U x
  | .binary R a b => ∃ x y, x ∈ a.eval C xs ∧ y ∈ b.eval C xs ∧ C.binary R x y
  | .neg p => ¬ eval C xs p
  | .conj p q => eval C xs p ∧ eval C xs q

theorem transport {C : Structure L V} {D : Structure L W}
    (f : Structure.Embedding C D) {n : ℕ} {ctx : Fin n → L.Sorts}
    (p : Formula L ctx) (xs : Fin n → V) :
    p.eval D (f.point ∘ xs) ↔ p.eval C xs := by
  induction p with
  | truth => exact Iff.rfl
  | equal a b =>
    constructor
    · rintro ⟨y, ha, hb⟩
      obtain ⟨x, hx, rfl⟩ := (a.2.transport f _ _).mp ha
      exact ⟨x, hx, (b.2.map_iff f _ _).mp hb⟩
    · rintro ⟨x, ha, hb⟩
      exact ⟨f.point x, (a.2.map_iff f _ _).mpr ha, (b.2.map_iff f _ _).mpr hb⟩
  | unary U a =>
    constructor
    · rintro ⟨y, ha, hy⟩
      obtain ⟨x, hx, rfl⟩ := (a.2.transport f _ _).mp ha
      exact ⟨x, hx, (f.unary_iff U x).mp hy⟩
    · rintro ⟨x, hx, hy⟩
      exact ⟨f.point x, (a.2.map_iff f _ _).mpr hx, (f.unary_iff U x).mpr hy⟩
  | binary R a b =>
    constructor
    · rintro ⟨x, y, hx, hy, hxy⟩
      obtain ⟨z, hz, rfl⟩ := (a.2.transport f _ _).mp hx
      obtain ⟨t, ht, rfl⟩ := (b.2.transport f _ _).mp hy
      exact ⟨z, t, hz, ht, (f.binary_iff R z t).mp hxy⟩
    · rintro ⟨x, y, hx, hy, hxy⟩
      exact ⟨f.point x, f.point y, (a.2.map_iff f _ _).mpr hx,
        (b.2.map_iff f _ _).mpr hy, (f.binary_iff R x y).mpr hxy⟩
  | neg p ih => exact not_congr ih
  | conj p q hp hq => exact and_congr hp hq

end Formula
end CCO.FullCode
