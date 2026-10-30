import CCO.ResetOrder.Unary.Task

/-! Genuine qf terms/formulas retain partial domains and arbitrary relation
arities, including nullary truth. Their naturality is PROVED structurally. -/
universe u v w
namespace CCO.ResetOrder.Unary.Definable
open CCO.UnarySupport

inductive Term (L : Signature.{u}) (n : ℕ) : Type u
  | var (i : Fin n)
  | app (F : L.Func) (t : Term L n)

namespace Term
variable {L : Signature.{u}} {n : ℕ}
def eval {V : Type v} (C : Structure L V) (xs : Fin n → V) : Term L n → Set V
  | .var i => {xs i}
  | .app F t => {y | ∃z, z ∈ eval C xs t ∧ y ∈ C.func F z}

theorem transport {V : Type v} {W : Type w} {C : Structure L V} {D : Structure L W}
    (f : Hom C D) (xs : Fin n → V) (t : Term L n) (y : W) :
    y ∈ t.eval D (f.point ∘ xs) ↔ ∃z, z ∈ t.eval C xs ∧ f.point z = y := by
  induction t generalizing y with
  | var i =>
    constructor
    · intro h; exact ⟨xs i,rfl,h.symm⟩
    · rintro ⟨z,hz,rfl⟩; exact congrArg f.point hz
  | app F t ih =>
    constructor
    · rintro ⟨b,hb,hby⟩
      obtain ⟨a,ha,hab⟩ := (ih b).1 hb
      obtain ⟨z,hz,hzy⟩ := f.reflect_func F a y (hab ▸ hby)
      exact ⟨z,⟨a,ha,hz⟩,hzy⟩
    · rintro ⟨z,⟨a,ha,haz⟩,rfl⟩
      exact ⟨f.point a,(ih _).2 ⟨a,ha,rfl⟩,f.map_func F a z haz⟩

theorem mapped_iff {V : Type v} {W : Type w} {C : Structure L V} {D : Structure L W}
    (f : Hom C D) (xs : Fin n → V) (t : Term L n) (z : V) :
    f.point z ∈ t.eval D (f.point ∘ xs) ↔ z ∈ t.eval C xs := by
  rw [t.transport f xs]
  exact ⟨fun ⟨a,ha,he⟩ => f.injective he ▸ ha,fun h => ⟨z,h,rfl⟩⟩
end Term

inductive OldFormula (L : Signature.{u}) (n : ℕ) : Type u
  | truth
  | equal (t s : Term L n)
  | rel (R : L.Rel) (ts : Fin (L.arity R) → Term L n)
  | neg (p : OldFormula L n)
  | conj (p q : OldFormula L n)

namespace OldFormula
variable {L : Signature.{u}} {n : ℕ}
def eval {V : Type v} (C : Structure L V) (xs : Fin n → V) : OldFormula L n → Prop
  | .truth => True
  | .equal t s => ∃z, z ∈ t.eval C xs ∧ z ∈ s.eval C xs
  | .rel R ts => ∃ys : Fin (L.arity R) → V, (∀i, ys i ∈ (ts i).eval C xs) ∧ C.rel R ys
  | .neg p => ¬ p.eval C xs
  | .conj p q => p.eval C xs ∧ q.eval C xs

theorem transport {V : Type v} {W : Type w} {C : Structure L V} {D : Structure L W}
    (f : Hom C D) (xs : Fin n → V) (p : OldFormula L n) :
    p.eval D (f.point ∘ xs) ↔ p.eval C xs := by
  classical
  induction p with
  | truth => exact Iff.rfl
  | equal t s =>
    constructor
    · rintro ⟨y,ht,hs⟩
      obtain ⟨z,hz,rfl⟩ := (t.transport f xs y).1 ht
      exact ⟨z,hz,(s.mapped_iff f xs z).1 hs⟩
    · rintro ⟨z,ht,hs⟩
      exact ⟨f.point z,(t.mapped_iff f xs z).2 ht,(s.mapped_iff f xs z).2 hs⟩
  | rel R ts =>
    constructor
    · rintro ⟨ys,hy,hR⟩
      have pre : ∀i, ∃z, z ∈ (ts i).eval C xs ∧ f.point z = ys i :=
        fun i => ((ts i).transport f xs (ys i)).1 (hy i)
      let zs := fun i => Classical.choose (pre i)
      have hz : ∀i, zs i ∈ (ts i).eval C xs := fun i => (Classical.choose_spec (pre i)).1
      have he : f.point ∘ zs = ys := funext (fun i => (Classical.choose_spec (pre i)).2)
      refine ⟨zs,hz,f.reflect_rel R zs ?_⟩
      rw [he]
      exact hR
    · rintro ⟨ys,hy,hR⟩
      exact ⟨f.point ∘ ys,fun i => ((ts i).mapped_iff f xs (ys i)).2 (hy i),f.map_rel R ys hR⟩
  | neg p ih => exact not_congr ih
  | conj p q hp hq => exact and_congr hp hq
end OldFormula

inductive TaskFormula (L : Signature.{u}) (n : ℕ) : Type u
  | old (p : OldFormula L n)
  | order (t s : Term L n)
  | neg (p : TaskFormula L n)
  | conj (p q : TaskFormula L n)

namespace TaskFormula
variable {L : Signature.{u}} {P : Fibres.{u,v} L} {n : ℕ}
def eval (A : TaskObject P) (xs : Fin n → A.old.Carrier) : TaskFormula L n → Prop
  | .old p => p.eval A.old.data xs
  | .order t s => ∃x y, x ∈ t.eval A.old.data xs ∧ y ∈ s.eval A.old.data xs ∧ A.order.lt x y
  | .neg p => ¬ p.eval A xs
  | .conj p q => p.eval A xs ∧ q.eval A xs

theorem transport {A B : TaskObject P} (f : TaskHom A B) (xs : Fin n → A.old.Carrier)
    (p : TaskFormula L n) : p.eval B (f.old.point ∘ xs) ↔ p.eval A xs := by
  induction p with
  | old p => exact p.transport f.old xs
  | order t s =>
    constructor
    · rintro ⟨x,y,hx,hy,hxy⟩
      obtain ⟨a,ha,rfl⟩ := (t.transport f.old xs x).1 hx
      obtain ⟨b,hb,rfl⟩ := (s.transport f.old xs y).1 hy
      exact ⟨a,b,ha,hb,(f.order_iff a b).1 hxy⟩
    · rintro ⟨a,b,ha,hb,hab⟩
      exact ⟨f.old.point a,f.old.point b,(t.mapped_iff f.old xs a).2 ha,
        (s.mapped_iff f.old xs b).2 hb,(f.order_iff a b).2 hab⟩
  | neg p ih => exact not_congr ih
  | conj p q hp hq => exact and_congr hp hq
end TaskFormula

def codesOfFormulas {L : Signature.{u}} (P : Fibres.{u,v} L)
    (Symbol : ℕ → Type u) (formula : ∀{n}, Symbol n → TaskFormula L n) : TaskCodes P where
  Symbol := Symbol
  value := fun A {n} R xs => (formula R).eval A xs
  natural := fun {A B} f {n} R xs => (formula R).transport f xs

theorem old_binary_natural {L : Signature.{u}} (p : OldFormula L 2)
    {A B : Object.{u,v} L} (f : A.Emb B) (xs : Fin 2 → A.Carrier) :
    p.eval B.data (f.point ∘ xs) ↔ p.eval A.data xs := p.transport f xs

end CCO.ResetOrder.Unary.Definable
