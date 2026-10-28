import CCO.FiniteHelpers
import CCO.AgeAP
import CCO.PairHomogeneity
import Mathlib.Data.Set.Finite.Range

/-!
# Ordinary amalgamation of the actual finite induced age

The `AgeAP` interface requires only a commuting amalgamation square. Unlike
`AgeSAP`, it imposes no fresh-point or exact-overlap condition. The proved
finite-tuple extension glues an actual legal triangle over a complete edge;
old tuple points may move and non-neighbours may coincide across factors.

The homogeneous-source-to-AP theorem is a separate discharge, without SAP.
-/

universe u v w z
namespace CCO
variable {ι : Type u} {X : ι → Type v} {S : AtomicSource.{u,v,w} ι X}

def reverseTagged (S : AtomicSource ι X) (c : Σ i : ι, Σ j : ι, Option (S.Atom i j)) :
    Σ i : ι, Σ j : ι, Option (S.Atom i j) :=
  ⟨c.2.1, c.1, c.2.2.map S.conv⟩

theorem taggedColour_reverse (S : AtomicSource ι X) (p q : Sigma X) :
    taggedColour S q p = reverseTagged S (taggedColour S p q) := by
  rcases p with ⟨i, x⟩
  rcases q with ⟨j, y⟩
  simp only [taggedColour, reverseTagged, S.colour_reverse x y]

theorem taggedColour_self_eq_of_sort {p q : Sigma X} (h : p.1 = q.1) :
    taggedColour S p p = taggedColour S q q := by
  rcases p with ⟨i, x⟩
  rcases q with ⟨j, y⟩
  cases h
  simp [taggedColour, (S.colour_none_iff x x).mpr rfl,
    (S.colour_none_iff y y).mpr rfl]

theorem taggedColour_reverse_eq {p q r t : Sigma X}
    (h : taggedColour S p q = taggedColour S r t) :
    taggedColour S q p = taggedColour S t r := by
  calc
    _ = reverseTagged S (taggedColour S p q) := taggedColour_reverse S _ _
    _ = reverseTagged S (taggedColour S r t) := congrArg (reverseTagged S) h
    _ = _ := (taggedColour_reverse S _ _).symm

def pointPair (p q : Sigma X) : FiniteInduced (X := X) where
  vertices := {p, q}
  finite_vertices := (Set.finite_singleton q).insert p

/-- An isomorphism of literal complete two-point bases from equality of their full pair colours. -/
noncomputable def pairInducedEmbedding (p q p' q' : Sigma X) (hpq : p ≠ q) (hp'q' : p' ≠ q')
    (hcol : taggedColour S p q = taggedColour S p' q')
    (B : FiniteInduced (X := X)) (hp' : p' ∈ B.vertices) (hq' : q' ∈ B.vertices) :
    InducedEmbedding S (pointPair p q) B := by
  classical
  let C : FiniteInduced (X := X) := pointPair p q
  let f : ↥C.vertices → ↥B.vertices := fun r =>
    if r.val = p then ⟨p', hp'⟩ else ⟨q', hq'⟩
  have hc (r : ↥C.vertices) : r.val = p ∨ r.val = q := by
    simpa [C, pointPair] using r.property
  have hfp (r : ↥C.vertices) (hr : r.val = p) : (f r).val = p' := by simp [f, hr]
  have hfq (r : ↥C.vertices) (hr : r.val = q) : (f r).val = q' := by simp [f, hr, hpq.symm]
  have hs1 : p.1 = p'.1 := congrArg (fun c : Σ i : ι, Σ j : ι, Option (S.Atom i j) => c.1) hcol
  have hs2 : q.1 = q'.1 := congrArg (fun c : Σ i : ι, Σ j : ι, Option (S.Atom i j) => c.2.1) hcol
  refine { toEmbedding := { toFun := f, inj' := ?_ }, preserves_sort := ?_, preserves_colours := ?_ }
  · intro r t h
    apply Subtype.ext
    have hv := congrArg Subtype.val h
    rcases hc r with hr | hr <;> rcases hc t with ht | ht
    · exact hr.trans ht.symm
    · rw [hfp r hr, hfq t ht] at hv
      exact False.elim (hp'q' hv)
    · rw [hfq r hr, hfp t ht] at hv
      exact False.elim (hp'q' hv.symm)
    · exact hr.trans ht.symm
  · intro r
    rcases hc r with hr | hr
    · change (f r).val.1 = r.val.1
      rw [hfp r hr, hr]
      exact hs1.symm
    · change (f r).val.1 = r.val.1
      rw [hfq r hr, hr]
      exact hs2.symm
  · intro r t
    change taggedColour S r.val t.val = taggedColour S (f r).val (f t).val
    rcases hc r with hr | hr <;> rcases hc t with ht | ht
    · rw [hfp r hr, hfp t ht, hr, ht]
      exact taggedColour_self_eq_of_sort hs1
    · rw [hfp r hr, hfq t ht, hr, ht]
      exact hcol
    · rw [hfq r hr, hfp t ht, hr, ht]
      exact taggedColour_reverse_eq hcol
    · rw [hfq r hr, hfq t ht, hr, ht]
      exact taggedColour_self_eq_of_sort hs2

/-- Ordinary AP glues one legal triangle to a finite actual tuple over its COMPLETE edge.
The old tuple can move, and no separation from its non-neighbours is claimed. -/
theorem AgeAP.extend_tuple_triangle (ap : AgeAP S)
    {W : Type z} [Finite W] (point : W → Sigma X) (root last : W)
    (x y z : Sigma X) (hne : point root ≠ point last) (hxy : x ≠ y)
    (hcol : taggedColour S (point root) (point last) = taggedColour S x y) :
    ∃ (out : W → Sigma X) (next : Sigma X),
      (∀ q, (out q).1 = (point q).1) ∧ next.1 = z.1 ∧
      (∀ q r, taggedColour S (out q) (out r) = taggedColour S (point q) (point r)) ∧
      taggedColour S (out root) next = taggedColour S x z ∧
      taggedColour S (out last) next = taggedColour S y z := by
  classical
  let A : FiniteInduced (X := X) := ⟨Set.range point, Set.finite_range point⟩
  let C : FiniteInduced (X := X) := pointPair (point root) (point last)
  let B : FiniteInduced (X := X) := FiniteInduced.ofFinset {x, y, z}
  have hA (q : W) : point q ∈ A.vertices := ⟨q, rfl⟩
  have hxB : x ∈ B.vertices := by simp [B, FiniteInduced.ofFinset]
  have hyB : y ∈ B.vertices := by simp [B, FiniteInduced.ofFinset]
  have hzB : z ∈ B.vertices := by simp [B, FiniteInduced.ofFinset]
  have hrC : point root ∈ C.vertices := by simp [C, pointPair]
  have hlC : point last ∈ C.vertices := by simp [C, pointPair]
  have hCA : C.vertices ⊆ A.vertices := by
    intro p hp
    have h : p = point root ∨ p = point last := by simpa [C, pointPair] using hp
    rcases h with rfl | rfl
    · exact hA root
    · exact hA last
  let eCA := inducedInclusion S C A hCA
  let eCB := pairInducedEmbedding (point root) (point last) x y hne hxy hcol B hxB hyB
  obtain ⟨T, eAT, eBT, hbase⟩ := ap.amalgamate C A B eCA eCB
  let old (q : W) : ↥A.vertices := ⟨point q, hA q⟩
  let bx : ↥B.vertices := ⟨x, hxB⟩
  let by' : ↥B.vertices := ⟨y, hyB⟩
  let bz : ↥B.vertices := ⟨z, hzB⟩
  let out (q : W) : Sigma X := (eAT.toEmbedding (old q)).val
  let next : Sigma X := (eBT.toEmbedding bz).val
  have hroot : eAT.toEmbedding (old root) = eBT.toEmbedding bx := by
    have h := hbase ⟨point root, hrC⟩
    have hh : eCB.toEmbedding ⟨point root, hrC⟩ = bx := by
      apply Subtype.ext
      change (if point root = point root then (⟨x, hxB⟩ : ↥B.vertices) else ⟨y, hyB⟩).val = x
      simp
    rw [hh] at h
    exact h
  have hlast : eAT.toEmbedding (old last) = eBT.toEmbedding by' := by
    have h := hbase ⟨point last, hlC⟩
    have hh : eCB.toEmbedding ⟨point last, hlC⟩ = by' := by
      apply Subtype.ext
      change (if point last = point root then (⟨x, hxB⟩ : ↥B.vertices) else ⟨y, hyB⟩).val = y
      simp [hne.symm]
    rw [hh] at h
    exact h
  refine ⟨out, next, ?_, eBT.preserves_sort bz, ?_, ?_, ?_⟩
  · intro q
    exact eAT.preserves_sort (old q)
  · intro q r
    exact (eAT.preserves_colours (old q) (old r)).symm
  · have h := eBT.preserves_colours bx bz
    rw [← hroot] at h
    exact h.symm
  · have h := eBT.preserves_colours by' bz
    rw [← hlast] at h
    exact h.symm

/-- Homogeneity of the actual source supplies ordinary age AP, without invoking SAP. -/
theorem AtomicSource.ageAP_of_homogeneous
    {G : Type*} [Group G] [∀ q : ι, MulAction G (X q)]
    (H : HomogeneousSource S G) : AgeAP S := by
  classical
  refine ⟨?_⟩
  intro C A B eCA eCB
  letI : Finite ↥C.vertices := C.finite_vertices.to_subtype
  let f (c : ↥C.vertices) : Sigma X := (eCA.toEmbedding c).val
  let h (c : ↥C.vertices) : Sigma X := (eCB.toEmbedding c).val
  have hcol : ∀ c d, taggedColour S (f c) (f d) = taggedColour S (h c) (h d) := by
    intro c d
    exact (eCA.preserves_colours c d).symm.trans (eCB.preserves_colours c d)
  obtain ⟨g, hg⟩ := H.extends_finite_diagram f h hcol
  let T : FiniteInduced (X := X) := {
    vertices := (fun p : Sigma X => g • p) '' A.vertices ∪ B.vertices
    finite_vertices := (A.finite_vertices.image (fun p => g • p)).union B.finite_vertices }
  let eAT : InducedEmbedding S A T := {
    toEmbedding := {
      toFun := fun a => ⟨g • a.val, Or.inl ⟨a.val, a.property, rfl⟩⟩
      inj' := by
        intro a b hab
        exact Subtype.ext ((MulAction.injective g) (congrArg Subtype.val hab)) }
    preserves_sort := fun a => H.preserves_sort g a.val
    preserves_colours := fun a b => (H.preserves_colours g a.val b.val).symm }
  let eBT := inducedInclusion S B T (fun _ hp => Or.inr hp)
  refine ⟨T, eAT, eBT, ?_⟩
  intro c
  apply Subtype.ext
  exact hg c

end CCO
