import CCO.APCharacter.Towers.UnaryReduct
import CCO.RawSource

/-!
# B062 C44–C46 / C49: actual old-orbital support on a unary prefix

A genuine unary reduct is bijective on its TOTAL old carrier, but may
divide one old sort into several current unary sorts. Support records
real projected pairs, not formal colours or possibly empty nominal tags.

The finite-type support of a composition is calculated by an ACTUAL
current middle sort: the old middle point is lifted through the
bijection, and two independent current witnesses are aligned by
current homogeneous automorphisms. Invariance of old orbitals under
current automorphisms is DERIVED from old/current fine-colour
homogeneity and the genuine unary reduct's colour equation; no
automorphism-group section or equivariance of reducts is assumed.
The same argument gives actual equivalence supports and complete
occupancy of each equivalence class.
-/

universe u v w t z

namespace CCO.ExactEPGeometry

open APCharacter.Towers

noncomputable section

variable {ι κ : Type u} {X : ι → Type v} {Y : κ → Type v}
variable {S : AtomicSource.{u,v,w} ι X}
variable {T : AtomicSource.{u,v,w} κ Y}

/-- An actual old pair relation between global tagged old points. -/
def globalRelation (R : ∀ i j : ι, TRel X i j) :
    Sigma X → Sigma X → Prop
  | ⟨i,x⟩, ⟨j,y⟩ => R i j x y

/-- Phi of an ACTUAL original relation, on actual current named sorts.
No finiteness, quotient actions or imaginary representatives are assumed. -/
def prefixSupport (P : UnaryReduct S T)
    (R : Sigma X → Sigma X → Prop) (i j : κ) : Prop :=
  ∃ x : Y i, ∃ y : Y j,
    R (P.project ⟨i,x⟩) (P.project ⟨j,y⟩)

/-- Explicit invariance under the ACTUAL new group, as seen through the
old projection. The following theorem proves it for old invariant
orbital unions; it is not an additional source-theorem assumption. -/
def PrefixInvariant (P : UnaryReduct S T)
    {K : Type z} [Group K] [∀ i, MulAction K (Y i)]
    (R : Sigma X → Sigma X → Prop) : Prop :=
  ∀ {i j : κ} (g : K) (x : Y i) (y : Y j),
    R (P.project ⟨i,x⟩) (P.project ⟨j,y⟩) →
      R (P.project ⟨i,g • x⟩) (P.project ⟨j,g • y⟩)

/-- Invariance of an original typed orbital union AFTER taking the
actual unary reduct. This follows from preservation of complete old
pair colours and old pair homogeneity, not from a fictitious section
from the current automorphism group onto the old automorphism group. -/
theorem globalRelation_prefix_invariant
    {G : Type t} [Group G] [∀ i, MulAction G (X i)]
    {K : Type z} [Group K] [∀ i, MulAction K (Y i)]
    (HS : HomogeneousSource S G) (HT : HomogeneousSource T K)
    (P : UnaryReduct S T)
    (R : ∀ i j : ι, TRel X i j)
    (hInv : ∀ i j, TRel.Invariant (G := G) (R i j)) :
    PrefixInvariant (K := K) P (globalRelation R) := by
  intro i j g x y hxy
  have hColour :
      S.colour (P.point i x) (P.point j y) =
        S.colour (P.point i (g • x)) (P.point j (g • y)) := by
    calc
      _ = Option.map (P.atom i j) (T.colour x y) := P.colour i j x y
      _ = Option.map (P.atom i j) (T.colour (g • x) (g • y)) :=
        congrArg (Option.map (P.atom i j))
          ((T.colourInvariant_of_homogeneous HT) g x y).symm
      _ = _ := (P.colour i j (g • x) (g • y)).symm
  obtain ⟨h,hx,hy⟩ := (S.pair_homogeneous_of_homogeneous HS)
    (P.point i x) (P.point i (g • x))
    (P.point j y) (P.point j (g • y)) hColour
  have hOld := hInv (P.parent i) (P.parent j) h
    (P.point i x) (P.point j y) hxy
  change R (P.parent i) (P.parent j)
    (P.point i (g • x)) (P.point j (g • y))
  simpa only [hx,hy] using hOld

/-- Phi preserves union of genuine binary relations, with real pair
witnesses on both sides. -/
theorem prefixSupport_union (P : UnaryReduct S T)
    (R U : Sigma X → Sigma X → Prop) (i j : κ) :
    prefixSupport P (fun x y => R x y ∨ U x y) i j ↔
      prefixSupport P R i j ∨ prefixSupport P U i j := by
  constructor
  · rintro ⟨x,y,h⟩
    rcases h with hR | hU
    · exact Or.inl ⟨x,y,hR⟩
    · exact Or.inr ⟨x,y,hU⟩
  · rintro (⟨x,y,h⟩ | ⟨x,y,h⟩)
    · exact ⟨x,y,Or.inl h⟩
    · exact ⟨x,y,Or.inr h⟩

/-- Phi preserves actual converse, including the true old diagonal. -/
theorem prefixSupport_converse (P : UnaryReduct S T)
    (R : Sigma X → Sigma X → Prop) (i j : κ) :
    prefixSupport P (fun x y => R y x) i j ↔
      prefixSupport P R j i := by
  constructor
  · rintro ⟨x,y,h⟩
    exact ⟨y,x,h⟩
  · rintro ⟨y,x,h⟩
    exact ⟨x,y,h⟩

/-- Phi of actual logical identity is equality of REALIZED type names.
The converse needs the canonical nonempty current named sorts, not an
unjustified assumption that arbitrary labels are inhabited. -/
theorem prefixSupport_identity (P : UnaryReduct S T)
    (i j : κ) :
    prefixSupport P Eq i j ↔ i = j := by
  constructor
  · rintro ⟨x,y,h⟩
    have heq : (⟨i,x⟩ : Sigma Y) = ⟨j,y⟩ :=
      P.bijective.1 h
    exact congrArg Sigma.fst heq
  · intro hij
    subst j
    let x : Y i := Classical.choice (T.nonemptySort i)
    exact ⟨x,x,rfl⟩

/-- C45: Phi commutes with real old relation composition, and the
middle support TYPE is explicitly a genuine current sort. Forward:
lift the OLD witness through the actual total reduct bijection.
Backward: align the TWO current middle witnesses by a current
automorphism, and move the second leg using proved invariance. -/
theorem prefixSupport_comp
    {K : Type z} [Group K] [∀ i, MulAction K (Y i)]
    (P : UnaryReduct S T) (HT : HomogeneousSource T K)
    (R U : Sigma X → Sigma X → Prop)
    (hU : PrefixInvariant (K := K) P U) (i k : κ) :
    prefixSupport P (RawSymmetric.compose R U) i k ↔
      ∃ j : κ, prefixSupport P R i j ∧ prefixSupport P U j k := by
  constructor
  · rintro ⟨x,z,y,hxy,hyz⟩
    obtain ⟨⟨j,b⟩,hb⟩ := P.bijective.2 y
    refine ⟨j,⟨x,b,?_⟩,⟨b,z,?_⟩⟩
    · change R (P.project ⟨i,x⟩)
        (⟨P.parent j, P.point j b⟩ : Sigma X)
      simpa only [← hb] using hxy
    · change U (⟨P.parent j, P.point j b⟩ : Sigma X)
        (P.project ⟨k,z⟩)
      simpa only [← hb] using hyz
  · rintro ⟨j,⟨x,y,hxy⟩,⟨y',z,hyz⟩⟩
    obtain ⟨g,hgy⟩ :=
      (T.original_sort_transitive_of_homogeneous HT j) y' y
    refine ⟨x,g • z, P.project ⟨j,y⟩, hxy, ?_⟩
    have hMoved := hU g y' z hyz
    simpa only [hgy] using hMoved

/-- Source-strength C45 for ANY two old invariant typed relations
(the second invariance suffices), on one actual homogeneous unary prefix.
The premise is old invariance and both ACTUAL source homogeneities, all
available from the original source and genuine prefix. -/
theorem prefixSupport_comp_old_invariant
    {G : Type t} [Group G] [∀ i, MulAction G (X i)]
    {K : Type z} [Group K] [∀ i, MulAction K (Y i)]
    (HS : HomogeneousSource S G) (HT : HomogeneousSource T K)
    (P : UnaryReduct S T)
    (R U : ∀ i j : ι, TRel X i j)
    (hU : ∀ i j, TRel.Invariant (G := G) (U i j))
    (i k : κ) :
    prefixSupport P
        (RawSymmetric.compose (globalRelation R) (globalRelation U)) i k ↔
      ∃ j : κ, prefixSupport P (globalRelation R) i j ∧
        prefixSupport P (globalRelation U) j k :=
  prefixSupport_comp P HT (globalRelation R) (globalRelation U)
    (globalRelation_prefix_invariant HS HT P U hU) i k

/-- C46: support of a real invariant equivalence is a real equivalence
on the entire realized unary type set. The only middle alignment is
current fiber homogeneity. -/
theorem prefixSupport_equivalence
    {K : Type z} [Group K] [∀ i, MulAction K (Y i)]
    (P : UnaryReduct S T) (HT : HomogeneousSource T K)
    (E : Sigma X → Sigma X → Prop) (hEq : RawSymmetric.EquivRel E)
    (hInv : PrefixInvariant (K := K) P E) :
    RawSymmetric.EquivRel (prefixSupport P E) := by
  refine ⟨?_,?_,?_⟩
  · intro i
    let x : Y i := Classical.choice (T.nonemptySort i)
    exact ⟨x,x,hEq.refl _⟩
  · rintro i j ⟨x,y,hxy⟩
    exact ⟨y,x,hEq.symm _ _ hxy⟩
  · rintro i j k ⟨x,y,hxy⟩ ⟨y',z,hyz⟩
    obtain ⟨g,hgy⟩ :=
      (T.original_sort_transitive_of_homogeneous HT j) y' y
    have hMoved : E (P.project ⟨j,y⟩) (P.project ⟨k,g • z⟩) := by
      simpa only [hgy] using hInv g y' z hyz
    exact ⟨x,g • z,hEq.trans _ _ _ hxy hMoved⟩

/-- C49: EACH individual original E-class meeting current sort i
meets EVERY current sort in its support-equivalence class. No global
representative section and no SAP of the quotient is assumed. -/
theorem prefixSupport_occupancy
    {K : Type z} [Group K] [∀ i, MulAction K (Y i)]
    (P : UnaryReduct S T) (HT : HomogeneousSource T K)
    (E : Sigma X → Sigma X → Prop)
    (hInv : PrefixInvariant (K := K) P E)
    (i j : κ) (x : Y i) :
    prefixSupport P E i j ↔
      ∃ y : Y j, E (P.project ⟨i,x⟩) (P.project ⟨j,y⟩) := by
  constructor
  · rintro ⟨x',y,hxy⟩
    obtain ⟨g,hgx⟩ :=
      (T.original_sort_transitive_of_homogeneous HT i) x' x
    refine ⟨g • y,?_⟩
    have hMoved := hInv g x' y hxy
    simpa only [hgx] using hMoved
  · rintro ⟨y,hxy⟩
    exact ⟨x,y,hxy⟩

end
end CCO.ExactEPGeometry
