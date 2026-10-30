import CCO.ResetOrder.Generic.Induced

universe u v w
namespace CCO.ResetOrder.Generic
variable {S : Type u} {L M N : Language S}

/-- An actual signature reduct retaining the named sort partition. -/
structure Reduct (L M : Language S) where
  func : {n : ℕ} → L.Func n → M.Func n
  rel : {n : ℕ} → L.Rel n → M.Rel n
  input : ∀ {n} (F : L.Func n), M.input (func F) = L.input F
  output : ∀ {n} (F : L.Func n), M.output (func F) = L.output F
  argument : ∀ {n} (R : L.Rel n), M.argument (rel R) = L.argument R

namespace Reduct

def identity (L : Language S) : Reduct L L where
  func F := F
  rel R := R
  input _ := rfl
  output _ := rfl
  argument _ := rfl

def data (ρ : Reduct L M) {V : Type v} (C : Structure M V) : Structure L V where
  sort := C.sort
  func F := C.func (ρ.func F)
  functional F := C.functional (ρ.func F)
  func_sorted F xs y hy := by
    simpa only [ρ.input F, ρ.output F] using C.func_sorted (ρ.func F) xs y hy
  rel R := C.rel (ρ.rel R)
  rel_sorted R xs hy := by
    simpa only [ρ.argument R] using C.rel_sorted (ρ.rel R) xs hy

def object (ρ : Reduct L M) (C : Object.{u,v} M) : Object.{u,v} L :=
  ⟨C.Carrier, C.finite, ρ.data C.data⟩

def embedding (ρ : Reduct L M) {V : Type v} {W : Type w}
    {A : Structure M V} {B : Structure M W} (e : A.Embedding B) :
    (ρ.data A).Embedding (ρ.data B) where
  point := e.point
  injective := e.injective
  sort_eq := e.sort_eq
  func_eq F := e.func_eq (ρ.func F)
  rel_iff R := e.rel_iff (ρ.rel R)

def compose (ρ : Reduct L M) (σ : Reduct M N) : Reduct L N where
  func F := σ.func (ρ.func F)
  rel R := σ.rel (ρ.rel R)
  input F := (σ.input (ρ.func F)).trans (ρ.input F)
  output F := (σ.output (ρ.func F)).trans (ρ.output F)
  argument R := (σ.argument (ρ.rel R)).trans (ρ.argument R)

@[simp] theorem data_compose (ρ : Reduct L M) (σ : Reduct M N)
    {V : Type v} (C : Structure N V) : (ρ.compose σ).data C = ρ.data (σ.data C) := rfl

@[simp] theorem object_compose (ρ : Reduct L M) (σ : Reduct M N)
    (C : Object.{u,v} N) : (ρ.compose σ).object C = ρ.object (σ.object C) := rfl

/-- Every upper function is retained; adding arbitrary relations/orders is allowed. -/
def KeepsFunctions (ρ : Reduct L M) : Prop :=
  ∀ {n} (F : M.Func n), ∃ G : L.Func n, ρ.func G = F

theorem closed_range_of_keepsFunctions (ρ : Reduct L M) (hρ : ρ.KeepsFunctions)
    {V : Type v} {W : Type w} {A : Structure L V} {C : Structure M W}
    (e : A.Embedding (ρ.data C)) : C.Closed (Set.range e.point) := by
  intro n F xs hx y hy
  obtain ⟨G, rfl⟩ := hρ F
  exact e.closed_range G xs hx hy

theorem keepsFunctions_compose (ρ : Reduct L M) (σ : Reduct M N)
    (hρ : ρ.KeepsFunctions) (hσ : σ.KeepsFunctions) : (ρ.compose σ).KeepsFunctions := by
  intro n F
  obtain ⟨G, rfl⟩ := hσ F
  obtain ⟨H, rfl⟩ := hρ G
  exact ⟨H, rfl⟩

/-- Restriction commutes with reduct on the EXACT original carrier. -/
theorem data_pullback (ρ : Reduct L M) {V : Type v} {W : Type w}
    (C : Structure M W) (f : V → W) (hf : Function.Injective f) :
    ρ.data (C.pullback f hf) = (ρ.data C).pullback f hf := rfl

/-- The actual upper pullback reduces to precisely the given intermediate object. -/
theorem pullback_reduct_eq (ρ : Reduct L M) {V : Type v} {W : Type w}
    {A : Structure L V} {C : Structure M W} (e : A.Embedding (ρ.data C))
    (hclosed : C.Closed (Set.range e.point)) :
    ρ.data (C.pullback e.point e.injective) = A := by
  apply Structure.Embedding.same_map_domain_unique
    (ρ.embedding (C.pullbackEmbedding e.point e.injective hclosed)) e
  rfl

end Reduct
end CCO.ResetOrder.Generic
