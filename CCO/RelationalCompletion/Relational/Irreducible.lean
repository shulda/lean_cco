import CCO.RelationalCompletion.Relational.Language

universe u v w
namespace CCO.RelationalCompletion.Relational.Structure
variable {L : Language.{u}} {V : Type v} {W : Type w}

/-- C01: one positive relation tuple witnesses irreducibility of its full
induced distinct-entry support, even with repeated coordinates or no entries. -/
theorem tuple_support_irreducible (A : Structure L V) {n} (R : L.Rel n)
    (xs : Fin n → V) (h : A.rel R xs) : (A.induce (Set.range xs)).Irreducible := by
  intro P Q hsplit
  let ys : Fin n → Set.range xs := fun i => ⟨xs i, ⟨i, rfl⟩⟩
  have hy : (A.induce (Set.range xs)).rel R ys := h
  rcases hsplit.2 R ys hy with hp | hq
  · left
    apply Set.eq_univ_of_forall
    rintro ⟨x, i, rfl⟩
    exact hp i
  · right
    apply Set.eq_univ_of_forall
    rintro ⟨x, i, rfl⟩
    exact hq i

/-- C02: the actual same-map embedding condition separates a collision fibre
on every irreducible source piece. -/
theorem IsHE.fibre_unique {A : Structure L V} {B : Structure L W} {h : V → W}
    (hh : A.IsHE B h) {S : Set V} (hS : (A.induce S).Irreducible)
    {x y : V} (hx : x ∈ S) (hy : y ∈ S) (he : h x = h y) : x = y :=
  (hh.irreducible S hS).1 hx hy he

/-- C02 including all repeated occurrences of a displayed tuple. -/
theorem IsHE.tuple_fibre_unique {A : Structure L V} {B : Structure L W} {h : V → W}
    (hh : A.IsHE B h) {n} (R : L.Rel n) (xs : Fin n → V) (hr : A.rel R xs)
    (i j : Fin n) (he : h (xs i) = h (xs j)) : xs i = xs j :=
  hh.fibre_unique (A.tuple_support_irreducible R xs hr) ⟨i, rfl⟩ ⟨j, rfl⟩ he

/-- C03 needs injectivity of the distinguished restriction, without assuming
that its SOURCE diagram is reflected. -/
theorem injOn_fibre_unique {h : V → W} {S : Set V} (hs : Set.InjOn h S)
    {x y : V} (hx : x ∈ S) (hy : y ∈ S) (he : h x = h y) : x = y := hs hx hy he

end CCO.RelationalCompletion.Relational.Structure
