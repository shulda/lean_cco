import CCO.ProfileHelly.Embeddings
import CCO.ProfileHelly.Fill

/-! Exact factor image readout for the standalone abstract table.
These finite induced-image facts do not use any completion/CCO/SAP law. -/
universe u v z y
namespace CCO.ProfileHelly.Network
variable {ι : Type u} {T : Table.{u,v} ι}
variable {V : Type z} {W : Type y} {sort : V → ι} {targetSort : W → ι}

private theorem tagged_payload {i j k l : ι} (hi : k = i) (hj : l = j)
    (a : Option (T.Atom i j)) (b : Option (T.Atom k l))
    (h : (⟨k,l,b⟩ : Σ i,Σ j,Option (T.Atom i j)) = ⟨i,j,a⟩) :
    b.map (castAtom hi hj) = a := by
  cases hi
  cases hj
  have h₁ := eq_of_heq (Sigma.mk.inj_iff.mp h).2
  have h₂ := eq_of_heq (Sigma.mk.inj_iff.mp h₁).2
  cases b <;> exact h₂

private theorem triangle_cast {i j k i' j' k' : ι}
    (hi : i = i') (hj : j = j') (hk : k = k')
    (a : T.Atom i j) (b : T.Atom j k) (c : T.Atom i k) :
    T.triangle (castAtom hi hj a) (castAtom hj hk b) (castAtom hi hk c) ↔ T.triangle a b c := by
  cases hi
  cases hj
  cases hk
  rfl

namespace Embedding
variable (C : CompleteNetwork T sort) {D : Network T targetSort}
variable (f : Embedding C.toNetwork D)

theorem complete_image (x y : W) (hx : ∃ a, f.point a = x) (hy : ∃ b, f.point b = y)
    (hne : x ≠ y) : ∃ a, D.edge x y = some a := by
  obtain ⟨p,rfl⟩ := hx
  obtain ⟨q,rfl⟩ := hy
  obtain ⟨a,ha⟩ := C.complete p q (fun h => hne (congrArg f.point h))
  have hh := congrArg (fun c : Σ i,Σ j,Option (T.Atom i j) => c.2.2.isSome) (f.preserves p q)
  change (D.edge (f.point p) (f.point q)).isSome = (C.edge p q).isSome at hh
  rw [ha] at hh
  cases he : D.edge (f.point p) (f.point q) with
  | none => rw [he] at hh; cases hh
  | some b => exact ⟨b,rfl⟩

theorem legal_image (x y z : W) (hx : ∃ p, f.point p = x)
    (hy : ∃ q, f.point q = y) (hz : ∃ r, f.point r = z)
    (hxy : x ≠ y) (hyz : y ≠ z) (hxz : x ≠ z)
    (a : T.Atom (targetSort x) (targetSort y))
    (b : T.Atom (targetSort y) (targetSort z))
    (c : T.Atom (targetSort x) (targetSort z))
    (ha : D.edge x y = some a) (hb : D.edge y z = some b) (hc : D.edge x z = some c) :
    T.triangle a b c := by
  obtain ⟨p,rfl⟩ := hx
  obtain ⟨q,rfl⟩ := hy
  obtain ⟨r,rfl⟩ := hz
  have hpq := tagged_payload (f.sort_eq p) (f.sort_eq q) _ _ (f.preserves p q)
  have hqr := tagged_payload (f.sort_eq q) (f.sort_eq r) _ _ (f.preserves q r)
  have hpr := tagged_payload (f.sort_eq p) (f.sort_eq r) _ _ (f.preserves p r)
  change (D.edge (f.point p) (f.point q)).map _ = C.edge p q at hpq
  change (D.edge (f.point q) (f.point r)).map _ = C.edge q r at hqr
  change (D.edge (f.point p) (f.point r)).map _ = C.edge p r at hpr
  rw [ha,Option.map_some] at hpq
  rw [hb,Option.map_some] at hqr
  rw [hc,Option.map_some] at hpr
  have ht := C.legal p q r (fun h => hxy (congrArg f.point h))
    (fun h => hyz (congrArg f.point h)) (fun h => hxz (congrArg f.point h))
    _ _ _ hpq.symm hqr.symm hpr.symm
  exact (triangle_cast (f.sort_eq p) (f.sort_eq q) (f.sort_eq r) a b c).mp ht

end Embedding
end CCO.ProfileHelly.Network
