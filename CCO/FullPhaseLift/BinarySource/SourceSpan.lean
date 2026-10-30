import CCO.Finite
import Mathlib.Data.Set.Finite.Range
import Mathlib.Logic.Equiv.Set

/-! B048 actual strong pair spans. Only actual AtomicSource AgeSAP is
used; every formal point is on a leg and the common base is exact. -/
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace CCO.FullPhaseLift.BinarySource
noncomputable section

private def sourceChart {ι : Type u} {X : ι → Type v} {a : ℕ}
    (p : Fin a ↪ Sigma X) : FiniteInduced (X := X) :=
  ⟨Set.range p,Set.finite_range p⟩

private def chartEquiv {ι : Type u} {X : ι → Type v} {a : ℕ}
    (p : Fin a ↪ Sigma X) : Fin a ≃ (sourceChart p).vertices :=
  Equiv.ofInjective p p.injective

private theorem chartEquiv_val {ι : Type u} {X : ι → Type v} {a : ℕ}
    (p : Fin a ↪ Sigma X) (x : Fin a) : (chartEquiv p x).val = p x := rfl

private theorem chartEquiv_symm_val {ι : Type u} {X : ι → Type v} {a : ℕ}
    (p : Fin a ↪ Sigma X) (x : (sourceChart p).vertices) :
    p ((chartEquiv p).symm x) = x.val :=
  congrArg Subtype.val ((chartEquiv p).apply_symm_apply x)

private def chartEmbedding {ι : Type u} {X : ι → Type v}
    (S : AtomicSource.{u,v,w} ι X) {a b : ℕ}
    (p : Fin a ↪ Sigma X) (q : Fin b ↪ Sigma X) (f : Fin a ↪ Fin b)
    (names : ∀ x y, taggedColour S (p x) (p y) = taggedColour S (q (f x)) (q (f y))) :
    InducedEmbedding S (sourceChart p) (sourceChart q) where
  toEmbedding := (chartEquiv p).symm.toEmbedding.trans (f.trans (chartEquiv q).toEmbedding)
  preserves_sort := by
    intro x
    change (q (f ((chartEquiv p).symm x))).1 = x.val.1
    have h := (congrArg (fun c => c.1) (names ((chartEquiv p).symm x) ((chartEquiv p).symm x))).symm
    change (q (f ((chartEquiv p).symm x))).1 = (p ((chartEquiv p).symm x)).1 at h
    rwa [chartEquiv_symm_val] at h
  preserves_colours := by
    intro x y
    change taggedColour S x.val y.val =
      taggedColour S (q (f ((chartEquiv p).symm x))) (q (f ((chartEquiv p).symm y)))
    have h := names ((chartEquiv p).symm x) ((chartEquiv p).symm y)
    rwa [chartEquiv_symm_val,chartEquiv_symm_val] at h

/-- A strict finite pair amalgam, with its carrier restricted to the
union of the two legs. This generic actual-source helper is also used by
the marked-pair adapter; it assumes only genuine AtomicSource AgeSAP. -/
theorem strict_pair_span {ι : Type u} {X : ι → Type v}
    (S : AtomicSource.{u,v,w} ι X) (sap : AgeSAP S) {a b c : ℕ}
    (p : Fin a ↪ Sigma X) (q : Fin b ↪ Sigma X)
    (s : Fin c ↪ Fin a) (t : Fin c ↪ Fin b)
    (names : ∀ x y, taggedColour S (p (s x)) (p (s y)) =
      taggedColour S (q (t x)) (q (t y))) :
    ∃ (V : Type (max u v)) (_ : Finite V)
      (j : Fin a ↪ V) (k : Fin b ↪ V) (target : V ↪ Sigma X),
      (∀ x, j (s x) = k (t x)) ∧
      (∀ x y, j x = k y → ∃ z, s z = x ∧ t z = y) ∧
      (∀ x y, taggedColour S (p x) (p y) = taggedColour S (target (j x)) (target (j y))) ∧
      (∀ x y, taggedColour S (q x) (q y) = taggedColour S (target (k x)) (target (k y))) ∧
      (∀ z, (∃ x, j x = z) ∨ ∃ y, k y = z) := by
  classical
  let base := s.trans p
  let left := chartEmbedding S base p s (fun _ _ => rfl)
  let right := chartEmbedding S base q t names
  obtain ⟨D,l,r,comm,inter⟩ := sap.strong_amalgamate (sourceChart base) (sourceChart p) (sourceChart q) left right
  let j0 : Fin a ↪ D.vertices := (chartEquiv p).toEmbedding.trans l.toEmbedding
  let k0 : Fin b ↪ D.vertices := (chartEquiv q).toEmbedding.trans r.toEmbedding
  let V := {z : D.vertices // z ∈ Set.range j0 ∪ Set.range k0}
  letI : Finite D.vertices := D.finite_vertices.to_subtype
  letI : Finite V := inferInstance
  let j : Fin a ↪ V := ⟨fun x => ⟨j0 x,Or.inl ⟨x,rfl⟩⟩,fun x y h => j0.injective (congrArg Subtype.val h)⟩
  let k : Fin b ↪ V := ⟨fun y => ⟨k0 y,Or.inr ⟨y,rfl⟩⟩,fun x y h => k0.injective (congrArg Subtype.val h)⟩
  let target : V ↪ Sigma X := ⟨fun z => z.val.val,by
    intro x y h
    exact Subtype.ext (Subtype.ext h)⟩
  refine ⟨V,inferInstance,j,k,target,?_,?_,?_,?_,?_⟩
  · intro x
    apply Subtype.ext
    have h := comm (chartEquiv base x)
    have hl : left.toEmbedding (chartEquiv base x) = chartEquiv p (s x) := by
      change chartEquiv p (s ((chartEquiv base).symm (chartEquiv base x))) = _
      rw [(chartEquiv base).symm_apply_apply]
    have hr : right.toEmbedding (chartEquiv base x) = chartEquiv q (t x) := by
      change chartEquiv q (t ((chartEquiv base).symm (chartEquiv base x))) = _
      rw [(chartEquiv base).symm_apply_apply]
    rw [hl,hr] at h
    exact h
  · intro x y h
    have he : l.toEmbedding (chartEquiv p x) = r.toEmbedding (chartEquiv q y) := congrArg Subtype.val h
    obtain ⟨z,hz,hz'⟩ := inter _ _ he
    let i := (chartEquiv base).symm z
    refine ⟨i,?_,?_⟩
    · apply (chartEquiv p).injective
      exact hz
    · apply (chartEquiv q).injective
      exact hz'
  · intro x y
    exact l.preserves_colours (chartEquiv p x) (chartEquiv p y)
  · intro x y
    exact r.preserves_colours (chartEquiv q x) (chartEquiv q y)
  · intro z
    rcases z.property with ⟨x,hx⟩ | ⟨y,hy⟩
    · exact Or.inl ⟨x,Subtype.ext hx⟩
    · exact Or.inr ⟨y,Subtype.ext hy⟩


end
end CCO.FullPhaseLift.BinarySource
