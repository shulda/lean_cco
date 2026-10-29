import CCO.HKNReservoir.PacketRecovery

universe u v w z x y
namespace CCO.HKNReservoir
open AllThoseEPPA
variable {B : Type u} {K : Type v} [Group K] {Atom : Type w}
variable {V : Type x} {W : Type y} {Γ : Type z} [Group Γ]

/-- Completeness/uniqueness of ORIGINAL source fine colours only. -/
structure FineData (D : Data B K Atom V) : Prop where
  irreflexive : ∀ a x, ¬D.fine a x x
  unique : ∀ a b x y, D.fine a x y → D.fine b x y → a = b
  symmetric : ∀ a x y, D.fine a x y → D.fine a y x
  complete : ∀ x y, x ≠ y → ∃ a, D.fine a x y

namespace PacketRecovery
variable (tag : Γ →* Equiv.Perm B) (D : Data B K Atom V)
variable (E : Structure (Signature B K Atom) W)
variable (hLocal : LocallyInSource tag (encode D) E)

/-- Fine names are fixed by the ONE global language component. -/
theorem embedding_fine {P : Set W} (hP : E.IsClosed P)
    (e : Structure.Embedding (HKNReservoir.action tag) (E.induce P hP) (encode D))
    (a : Atom) (x y : P) :
    E.rel (.fine a) (![x.val,y.val]) ↔ D.fine a (e x) (e y) := by
  have h := e.map_rel_iff (.fine a) (![x,y])
  have ht : Subtype.val ∘ (![x,y] : Fin 2 → P) = ![x.val,y.val] := by
    funext i; fin_cases i <;> rfl
  change D.fine a (e x) (e y) ↔ E.rel (.fine a) (Subtype.val ∘ ![x,y]) at h
  rw [ht] at h
  exact h.symm

def pairSet (x y : W) : Set W := E.closureAtSet x ∪ E.closureAtSet y

theorem pair_closed (x y : W) : E.IsClosed (pairSet E x y) :=
  closed_union E (E.isClosed_closureSet {x}) (E.isClosed_closureSet {y})

def leftPoint (x y : W) : pairSet E x y := ⟨x,Or.inl (E.mem_closureAtSet x)⟩
def rightPoint (x y : W) : pairSet E x y := ⟨y,Or.inr (E.mem_closureAtSet y)⟩

/-- ONE recorded fine edge makes the WHOLE two-closure piece faithful. -/
noncomputable def pairEmbedding (x y : W) (a : Atom) (ha : E.rel (.fine a) (![x,y])) :
    Structure.Embedding (HKNReservoir.action tag)
      (E.induce (pairSet E x y) (pair_closed E x y)) (encode D) :=
  Classical.choice (hLocal _ (pair_closed E x y)
    (two_packet_irreducible E (E.isClosed_closureSet {x}) (E.isClosed_closureSet {y}) rfl rfl a ha))

/-- Every entry is reflected by the SAME actual two-packet embedding. -/
theorem recorded_matrix_reflection (x y : W) (a : Atom) (ha : E.rel (.fine a) (![x,y]))
    (g h : K) (c : Atom) :
    E.rel (.fine c) (![move tag D E hLocal g x,move tag D E hLocal h y]) ↔
      D.fine c
        (D.move g (pairEmbedding tag D E hLocal x y a ha (leftPoint E x y)))
        (D.move h (pairEmbedding tag D E hLocal x y a ha (rightPoint E x y))) := by
  let e := pairEmbedding tag D E hLocal x y a ha
  let p := leftPoint E x y
  let q := rightPoint E x y
  let pg : pairSet E x y := ⟨move tag D E hLocal g x,move_closed tag D E hLocal (pair_closed E x y) g p.property⟩
  let qh : pairSet E x y := ⟨move tag D E hLocal h y,move_closed tag D E hLocal (pair_closed E x y) h q.property⟩
  have hr := embedding_fine tag D E (pair_closed E x y) e c pg qh
  have hg : e pg = D.move g (e p) := embedding_move tag D E hLocal (pair_closed E x y) e g p
  have hh : e qh = D.move h (e q) := embedding_move tag D E hLocal (pair_closed E x y) e h q
  exact hr.trans (Iff.of_eq (congrArg₂ (D.fine c) hg hh))

variable (hD : RegularData D)

include hD in
theorem pair_source_orbits_distinct (x y : W) (a : Atom) (ha : E.rel (.fine a) (![x,y]))
    (hne : E.closureAtSet x ≠ E.closureAtSet y) (g : K) :
    D.move g (pairEmbedding tag D E hLocal x y a ha (leftPoint E x y)) ≠
      pairEmbedding tag D E hLocal x y a ha (rightPoint E x y) := by
  intro he
  let e := pairEmbedding tag D E hLocal x y a ha
  let p := leftPoint E x y
  let q := rightPoint E x y
  have hg := embedding_move tag D E hLocal (pair_closed E x y) e g p
  have heq : move tag D E hLocal g x = y :=
    congrArg Subtype.val (e.injective (hg.trans he))
  have ho : orbit tag D E hLocal y = orbit tag D E hLocal x :=
    orbit_eq_of_mem tag D E hLocal hD ⟨g,heq⟩
  apply hne
  rw [closure_eq_orbit tag D E hLocal hD,closure_eq_orbit tag D E hLocal hD,ho]

include hD in
theorem pair_source_points_distinct (x y : W) (a : Atom) (ha : E.rel (.fine a) (![x,y]))
    (hne : E.closureAtSet x ≠ E.closureAtSet y) (g h : K) :
    D.move g (pairEmbedding tag D E hLocal x y a ha (leftPoint E x y)) ≠
      D.move h (pairEmbedding tag D E hLocal x y a ha (rightPoint E x y)) := by
  intro he
  apply pair_source_orbits_distinct tag D E hLocal hD x y a ha hne (h⁻¹*g)
  rw [hD.mul,he,← hD.mul,inv_mul_cancel,hD.one]

/-- A single edge forces exactly ONE fine colour on EVERY cross entry;
regularity and completeness are transferred from the source, not assumed
as matrix axioms on the raw HKN output. -/
theorem recorded_matrix_complete (hD : RegularData D) (hFine : FineData D)
    (x y : W) (a : Atom) (ha : E.rel (.fine a) (![x,y]))
    (hne : E.closureAtSet x ≠ E.closureAtSet y) (g h : K) :
    ∃! c : Atom, E.rel (.fine c) (![move tag D E hLocal g x,move tag D E hLocal h y]) := by
  have hd := pair_source_points_distinct tag D E hLocal hD x y a ha hne g h
  obtain ⟨c,hc⟩ := hFine.complete _ _ hd
  refine ⟨c,(recorded_matrix_reflection tag D E hLocal x y a ha g h c).mpr hc,?_⟩
  intro d hd
  exact hFine.unique d c _ _ ((recorded_matrix_reflection tag D E hLocal x y a ha g h d).mp hd) hc

/-- The entire internal fine matrix of each packet is reflected as well. -/
theorem internal_matrix_reflection (x : W) (g h : K) (a : Atom) :
    E.rel (.fine a) (![move tag D E hLocal g x,move tag D E hLocal h x]) ↔
      D.fine a (D.move g (closureEmbedding tag D E hLocal x ⟨x,E.mem_closureAtSet x⟩))
        (D.move h (closureEmbedding tag D E hLocal x ⟨x,E.mem_closureAtSet x⟩)) := by
  let e := closureEmbedding tag D E hLocal x
  let p : E.closureAtSet x := ⟨x,E.mem_closureAtSet x⟩
  let hP : E.IsClosed (E.closureAtSet x) := E.isClosed_closureSet {x}
  have hr := embedding_fine tag D E hP e a
    ⟨move tag D E hLocal g x,move_closed tag D E hLocal hP g p.property⟩
    ⟨move tag D E hLocal h x,move_closed tag D E hLocal hP h p.property⟩
  rw [embedding_move tag D E hLocal hP e g p,embedding_move tag D E hLocal hP e h p] at hr
  exact hr


/-- Local reflection already forbids contradictory fine records globally. -/
theorem fine_unique (hLocal : LocallyInSource tag (encode D) E) (hFine : FineData D) (x y : W) (a b : Atom)
    (ha : E.rel (.fine a) (![x,y])) (hb : E.rel (.fine b) (![x,y])) : a = b := by
  let e := pairEmbedding tag D E hLocal x y a ha
  let p := leftPoint E x y
  let q := rightPoint E x y
  exact hFine.unique a b (e p) (e q)
    ((embedding_fine tag D E (pair_closed E x y) e a p q).mp ha)
    ((embedding_fine tag D E (pair_closed E x y) e b p q).mp hb)

theorem fine_symmetric (hLocal : LocallyInSource tag (encode D) E) (hFine : FineData D) (x y : W) (a : Atom)
    (ha : E.rel (.fine a) (![x,y])) : E.rel (.fine a) (![y,x]) := by
  let e := pairEmbedding tag D E hLocal x y a ha
  let p := leftPoint E x y
  let q := rightPoint E x y
  apply (embedding_fine tag D E (pair_closed E x y) e a q p).mpr
  exact hFine.symmetric a (e p) (e q) ((embedding_fine tag D E (pair_closed E x y) e a p q).mp ha)

theorem fine_irreflexive (hLocal : LocallyInSource tag (encode D) E) (hFine : FineData D) (x : W) (a : Atom) : ¬E.rel (.fine a) (![x,x]) := by
  intro ha
  let e := closureEmbedding tag D E hLocal x
  let p : E.closureAtSet x := ⟨x,E.mem_closureAtSet x⟩
  exact hFine.irreflexive a (e p)
    ((embedding_fine tag D E (E.isClosed_closureSet {x}) e a p p).mp ha)

end PacketRecovery
end CCO.HKNReservoir
