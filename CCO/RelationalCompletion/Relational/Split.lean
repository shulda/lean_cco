import CCO.RelationalCompletion.Relational.Clone
import CCO.RelationalCompletion.Relational.Irreducible

universe u v w
namespace CCO.RelationalCompletion.Relational.Structure
variable {L : Language.{u}} {V : Type v} {W : Type w}

/-- C09: simultaneous movement of every occurrence of a selected source point. -/
noncomputable def split (h : V → W) (T : Set V) (fresh : W) : V → W := by
  classical
  exact fun x => if x ∈ T then fresh else h x

/-- On any set with an injective old restriction a fibre split is either
unchanged or EXACTLY the full induced clone composed with that restriction. -/
theorem split_restriction (U : Structure L W) (h : V → W) (T I : Set V) (v : Set.range h)
    (ht : ∀ x ∈ T, h x = v.val) (hi : Set.InjOn h I)
    (e : Embedding (U.induce (Set.range h)) U)
    (hfix : ∀ y : Set.range h, y ≠ v → e.point y = y.val) :
    (∀ x ∈ I, split h T (e.point v) x = h x) ∨
    (∀ x ∈ I, split h T (e.point v) x = e.point ⟨h x, ⟨x, rfl⟩⟩) := by
  classical
  by_cases hx : ∃ x, x ∈ I ∧ x ∈ T
  · obtain ⟨x, hxi, hxt⟩ := hx
    right
    intro y hyi
    by_cases hyt : y ∈ T
    · simp only [split, ite_eq_left hyt]
      congr 1
      exact Subtype.ext (ht y hyt).symm
    · simp only [split, ite_eq_right hyt]
      symm
      apply hfix
      intro he
      have hxy : h y = h x := (congrArg Subtype.val he).trans (ht x hxt).symm
      exact hyt (hi hyi hxi hxy ▸ hxt)
  · left
    intro x hxi
    simp only [split, ite_eq_right (fun hxt => hx ⟨x, hxi, hxt⟩)]

/-- C12: every separately protected injective restriction remains injective. -/
theorem split_injOn (U : Structure L W) (h : V → W) (T I : Set V)
    (v : Set.range h) (ht : ∀ x ∈ T, h x = v.val) (hi : Set.InjOn h I)
    (e : Embedding (U.induce (Set.range h)) U)
    (hfix : ∀ y : Set.range h, y ≠ v → e.point y = y.val) :
    Set.InjOn (split h T (e.point v)) I := by
  rcases split_restriction U h T I v ht hi e hfix with hs | hs
  · intro x hx y hy hxy
    exact hi hx hy ((hs x hx).symm.trans (hxy.trans (hs y hy)))
  · intro x hx y hy hxy
    have he : e.point ⟨h x, ⟨x, rfl⟩⟩ = e.point ⟨h y, ⟨y, rfl⟩⟩ :=
      (hs x hx).symm.trans (hxy.trans (hs y hy))
    exact hi hx hy (congrArg Subtype.val (e.injective he))

/-- C12: the FULL induced target-image type is preserved, without any
reflection hypothesis on the SOURCE protected set. -/
theorem split_sameImageType (U : Structure L W) (h : V → W) (T I : Set V)
    (v : Set.range h) (ht : ∀ x ∈ T, h x = v.val) (hi : Set.InjOn h I)
    (e : Embedding (U.induce (Set.range h)) U)
    (hfix : ∀ y : Set.range h, y ≠ v → e.point y = y.val) :
    U.SameImageType h (split h T (e.point v)) I := by
  intro n R xs hxs
  rcases split_restriction U h T I v ht hi e hfix with hs | hs
  · have hh : split h T (e.point v) ∘ xs = h ∘ xs := funext (fun i => hs _ (hxs i))
    rw [hh]
  · let ys : Fin n → Set.range h := fun i => ⟨h (xs i), ⟨xs i, rfl⟩⟩
    have hh : split h T (e.point v) ∘ xs = e.point ∘ ys :=
      funext (fun i => hs _ (hxs i))
    rw [hh]
    exact (e.rel_iff R ys).symm

/-- C11: the SAME new vertex map is induced on every old induced piece. -/
theorem split_embedsOn (A : Structure L V) (U : Structure L W) (h : V → W)
    (T I : Set V) (v : Set.range h) (ht : ∀ x ∈ T, h x = v.val)
    (hi : A.EmbedsOn U h I) (e : Embedding (U.induce (Set.range h)) U)
    (hfix : ∀ y : Set.range h, y ≠ v → e.point y = y.val) :
    A.EmbedsOn U (split h T (e.point v)) I := by
  refine ⟨split_injOn U h T I v ht hi.1 e hfix, ?_⟩
  intro n R xs hxs
  exact (split_sameImageType U h T I v ht hi.1 e hfix R xs hxs).symm.trans
    (hi.2 R xs hxs)

/-- C10/C11: global positive preservation uses the actual irreducibility of
EACH displayed tuple support. No binary or distinct-coordinate simplification. -/
theorem IsHE.split {A : Structure L V} {U : Structure L W} {h : V → W}
    (hh : A.IsHE U h) (T : Set V) (v : Set.range h) (ht : ∀ x ∈ T, h x = v.val)
    (e : Embedding (U.induce (Set.range h)) U)
    (hfix : ∀ y : Set.range h, y ≠ v → e.point y = y.val) :
    A.IsHE U (split h T (e.point v)) where
  positive R xs hr := by
    have hi := hh.irreducible (Set.range xs) (A.tuple_support_irreducible R xs hr)
    exact (split_sameImageType U h T (Set.range xs) v ht hi.1 e hfix R xs
      (fun i => ⟨i, rfl⟩)).mp (hh.positive R xs hr)
  irreducible I hI := split_embedsOn A U h T I v ht (hh.irreducible I hI) e hfix

end CCO.RelationalCompletion.Relational.Structure
