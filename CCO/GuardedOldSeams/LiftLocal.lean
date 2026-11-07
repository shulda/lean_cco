import CCO.GuardedTwoRoot.SourceJoins
import CCO.UnarySupport.LocalTheorem

/-! The local-to-global part of the guarded lift. The two-root witnesses
below concern only the actual irreducible closure of their displayed
roots. They do not assume an embedding of the ambient partial source. -/

universe u v w
namespace CCO.GuardedOldSeams
open CCO.UnarySupport CCO.UnarySupport.Structure

section Partial
variable {L : Signature.{u}} {P : Type v} {Q : Type w}
variable {C : Structure L P} {A : Structure L Q}

/-- Two homomorphisms into a functional target which agree on the
generators agree on their entire actual unary closure. -/
theorem hom_agree_on_closure (f g : Hom C A) (B : Set P)
    (h : ∀ x ∈ B, f.point x = g.point x) :
    ∀ x ∈ C.closure B, f.point x = g.point x := by
  apply C.closure_minimal (S := {x | f.point x = g.point x}) ?_ h
  intro F x hx y hy
  exact A.functional F (f.point x) (f.point y) (g.point y)
    (f.map_func F x y hy) (hx ▸ g.map_func F x y hy)

/-- An induced closure embedding agreeing with a global homomorphism
at its generators agrees at every old vertex of that closure. -/
theorem closure_embedding_agrees (f : Hom C A) (B : Set P)
    (e : Embedding (C.closureStructure B) A)
    (h : ∀ x (hx : x ∈ B), e.point ⟨x,C.subset_closure B hx⟩ = f.point x) :
    ∀ x : C.closure B, e.point x = f.point x.val := by
  let g : Hom (C.closureStructure B) A := {
    point x := f.point x.val
    sort_eq x := f.sort_eq x.val
    map_func F x y hy := f.map_func F x.val y.val hy
    map_rel R xs hr := f.map_rel R (Subtype.val ∘ xs) hr }
  have hEq : ∀ x ∈ (C.closureStructure B).closure
      {x | x.val ∈ B}, e.point x = g.point x :=
    hom_agree_on_closure e.toHom g _ (fun x hx => h x.val hx)
  intro x
  have hx : x ∈ (C.closureStructure B).closure {x | x.val ∈ B} := by
    have hi := C.closure_induce_image (C.isClosed_closure B) {x | x.val ∈ B}
    have hs : Subtype.val '' {x : C.closure B | x.val ∈ B} = B := by
      ext y
      constructor
      · rintro ⟨z,hz,rfl⟩
        exact hz
      · intro hy
        exact ⟨⟨y,C.subset_closure B hy⟩,hy,rfl⟩
    rw [hs] at hi
    change Subtype.val '' (C.closureStructure B).closure {x | x.val ∈ B} =
      C.closure B at hi
    have hxImage : x.val ∈ Subtype.val ''
        (C.closureStructure B).closure {x | x.val ∈ B} := by
      rw [hi]
      exact x.property
    obtain ⟨y,hy,he⟩ := hxImage
    exact (Subtype.ext he : y = x) ▸ hy
  exact hEq x hx

/-- A complete local embedding whose points agree with a global map
really is a restriction embedding, including unary domain reflection. -/
theorem embeddingOn_of_agree (f : Hom C A) {D : Set P} (hD : C.IsClosed D)
    (e : Embedding (C.induce D hD) A)
    (he : ∀ x, e.point x = f.point x.val) : f.EmbeddingOn D := by
  refine ⟨?_,?_,?_⟩
  · intro x hx y hy hxy
    exact congrArg Subtype.val (e.injective ((he ⟨x,hx⟩).trans
      (hxy.trans (he ⟨y,hy⟩).symm)))
  · intro R xs hxs
    constructor
    · intro hr
      let ys : Fin (L.arity R) → D := fun i => ⟨xs i,hxs i⟩
      apply e.reflect_rel R ys
      have hp : e.point ∘ ys = f.point ∘ xs := funext (fun i => he (ys i))
      exact hp.symm ▸ hr
    · exact f.map_rel R xs
  · intro F x hx y hy
    obtain ⟨z,hz,hzy⟩ := e.reflect_func F ⟨x,hx⟩ y ((he ⟨x,hx⟩).symm ▸ hy)
    exact ⟨z.val,z.property,hz,(he z).symm.trans hzy⟩

/-- The exact local witnesses needed for reconstruction. No completion
of an unjoined pair, or of the whole source, is contained in this data. -/
structure RootLocalEmbeddings (point : P → Q) where
  sort_eq : ∀ p, A.sort (point p) = C.sort p
  singleton : ∀ p, ∃ e : Embedding (C.singletonStructure p) A,
    e.point ⟨p,C.mem_closureAt p⟩ = point p
  pair : ∀ p q, p ≠ q → (C.closureStructure {p,q}).Irreducible →
    ∃ e : Embedding (C.closureStructure {p,q}) A,
      e.point ⟨p,C.subset_closure _ (by simp)⟩ = point p ∧
      e.point ⟨q,C.subset_closure _ (by simp)⟩ = point q

variable {point : P → Q}

/-- The canonical root map preserves precisely the displayed source
functions and binary relations. Self tuples use their singleton witness. -/
noncomputable def RootLocalEmbeddings.hom
    (d : RootLocalEmbeddings (C := C) (A := A) point)
    (hbin : ∀ R, L.arity R = 2) : Hom C A where
  point := point
  sort_eq := d.sort_eq
  map_func F p q hpq := by
    by_cases he : p = q
    · subst q
      obtain ⟨e,hp⟩ := d.singleton p
      exact hp ▸ e.map_func F ⟨p,C.mem_closureAt p⟩ ⟨p,C.mem_closureAt p⟩ hpq
    · obtain ⟨e,hp,hq⟩ := d.pair p q he
        (CCO.GuardedTwoRoot.displayed_unary_pair_irreducible C F p q hpq)
      exact hp ▸ hq ▸ e.map_func F
        ⟨p,C.subset_closure _ (by simp)⟩ ⟨q,C.subset_closure _ (by simp)⟩ hpq
  map_rel R xs hr := by
    let zero : Fin (L.arity R) := ⟨0,by rw [hbin R]; omega⟩
    let one : Fin (L.arity R) := ⟨1,by rw [hbin R]; omega⟩
    have hi (i : Fin (L.arity R)) : i = zero ∨ i = one := by
      have hz := i.isLt
      have hb := hbin R
      by_cases h : i.val = 0
      · exact Or.inl (Fin.ext h)
      · exact Or.inr (Fin.ext (by dsimp [one]; omega))
    by_cases he : xs zero = xs one
    · obtain ⟨e,hp⟩ := d.singleton (xs zero)
      let ys : Fin (L.arity R) → C.closureAt (xs zero) :=
        fun i => ⟨xs i,by rcases hi i with rfl | rfl <;> simpa only [← he] using C.mem_closureAt (xs zero)⟩
      have hp' : e.point ∘ ys = point ∘ xs := by
        funext i
        rcases hi i with rfl | rfl
        · exact hp
        · change e.point (ys one) = point (xs one)
          have hy : ys one = ys zero := Subtype.ext he.symm
          rw [hy,← he]
          exact hp
      exact hp' ▸ e.map_rel R ys hr
    · have hr' : C.rel R (fun i => if i.val = 0 then xs zero else xs one) := by
        have ht : (fun i : Fin (L.arity R) => if i.val = 0 then xs zero else xs one) = xs := by
          funext i
          rcases hi i with rfl | rfl <;> simp [zero,one]
        exact ht.symm ▸ hr
      obtain ⟨e,hp,hq⟩ := d.pair (xs zero) (xs one) he
        (CCO.GuardedTwoRoot.displayed_binary_pair_irreducible C R (hbin R) _ _ hr')
      let ys : Fin (L.arity R) → C.closure {xs zero,xs one} :=
        fun i => ⟨xs i,by rcases hi i with rfl | rfl <;> exact C.subset_closure _ (by simp)⟩
      have hp' : e.point ∘ ys = point ∘ xs := by
        funext i
        rcases hi i with rfl | rfl
        · exact hp
        · exact hq
      exact hp' ▸ e.map_rel R ys hr

theorem RootLocalEmbeddings.hom_locallyInduced
    (d : RootLocalEmbeddings (C := C) (A := A) point)
    (hbin : ∀ R, L.arity R = 2) : (d.hom hbin).LocallyInduced := by
  intro D hD
  cases hD with
  | singleton p =>
    obtain ⟨e,hp⟩ := d.singleton p
    apply embeddingOn_of_agree (d.hom hbin) (C.isClosed_closure {p}) e
    apply closure_embedding_agrees
    intro x hx
    have hxp : x = p := hx
    subst x
    exact hp
  | binary R hR xs hr hd =>
    obtain ⟨i,j,hij⟩ := hd
    have hRange : Set.range xs = {xs i,xs j} := by
      ext x
      constructor
      · rintro ⟨k,rfl⟩
        have hk : k = i ∨ k = j := by
          have hi := i.isLt
          have hj := j.isLt
          have hk := k.isLt
          have hne : i.val ≠ j.val := fun h => hij (congrArg xs (Fin.ext h))
          by_cases h : k.val = i.val
          · exact Or.inl (Fin.ext h)
          · exact Or.inr (Fin.ext (by omega))
        rcases hk with rfl | rfl <;> simp
      · rintro (rfl | rfl)
        · exact ⟨i,rfl⟩
        · exact ⟨j,rfl⟩
    have hirr : (C.closureStructure {xs i,xs j}).Irreducible := by
      rw [← hRange]
      exact CCO.HiddenSAPReadings.SourceSupport.displayed_tuple_closure_irreducible C R xs hr
    obtain ⟨e,hi,hj⟩ := d.pair (xs i) (xs j) hij hirr
    rw [hRange]
    apply embeddingOn_of_agree (d.hom hbin) (C.isClosed_closure {xs i,xs j}) e
    apply closure_embedding_agrees
    intro x hx
    rcases hx with rfl | rfl
    · exact hi
    · exact hj

/-- Actual positive binary local cover, including the empty source.
There is no hypothesis about all irreducible source substructures. -/
theorem RootLocalEmbeddings.homEmbedding
    (d : RootLocalEmbeddings (C := C) (A := A) point)
    (hC : C.Total) (hbin : ∀ R, L.arity R = 2) : (d.hom hbin).HomEmbedding := by
  apply (d.hom hbin).locallyInduced_positive hC
    (fun R => (hbin R).le) (d.hom_locallyInduced hbin)
  intro R
  rw [hbin R]
  omega

end Partial
end CCO.GuardedOldSeams
