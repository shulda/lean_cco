import CCO.FiniteKernel.BinarySource
import Mathlib.Algebra.Group.Subgroup.Ker
import Mathlib.Algebra.Group.Pi.Basic
import Mathlib.Logic.Equiv.Sigma
import Mathlib.Data.Fintype.Sigma
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Set.Finite.Range

/-!
# Actual full-group projections on entire named finite axes

The axes are literal unary predicates of the original arbitrary unary/binary
structure, pairwise disjoint and finite. They need NOT cover the universe;
the complement and every other named sort may be infinite. All restrictions
below concern the FULL original Aut, not an owner kernel or finer source image.
-/

universe u v w z
namespace CCO.FiniteKernel

variable {X : Type u} (S : BinaryStructure.{u,v,w} X) (I : Type z)

structure NamedAxes where
  name : I → S.Unary
  finite_axis : ∀ i, {x : X | S.unary (name i) x}.Finite
  disjoint : ∀ i j x, S.unary (name i) x → S.unary (name j) x → i = j

namespace NamedAxes
noncomputable section
variable {S I} (P : NamedAxes S I)

def axis (i : I) : Set X := {x | S.unary (P.name i) x}
abbrev Point (i : I) := ↥(P.axis i)
instance pointFinite (i : I) : Finite (P.Point i) := (P.finite_axis i).to_subtype
instance pointFintype (i : I) : Fintype (P.Point i) := Fintype.ofFinite _
abbrev Intrinsic (i : I) := (S.induced (P.axis i)).Aut

instance intrinsicFinite (i : I) : Finite (P.Intrinsic i) := by
  classical
  change Finite {g : Equiv.Perm (P.Point i) // g ∈ (S.induced (P.axis i)).autGroup}
  infer_instance

def restrictPerm (i : I) (g : S.Aut) : Equiv.Perm (P.Point i) where
  toFun x := ⟨g.val x.val,(g.property.1 (P.name i) x.val).mpr x.property⟩
  invFun x := ⟨g⁻¹.val x.val,((g⁻¹).property.1 (P.name i) x.val).mpr x.property⟩
  left_inv x := Subtype.ext (g.val.symm_apply_apply x.val)
  right_inv x := Subtype.ext (g.val.apply_symm_apply x.val)

def restrict (i : I) : S.Aut →* P.Intrinsic i where
  toFun g := ⟨P.restrictPerm i g,
    ⟨fun r x => g.property.1 r x.val,fun r x y => g.property.2 r x.val y.val⟩⟩
  map_one' := by apply Subtype.ext; apply Equiv.ext; intro x; apply Subtype.ext; rfl
  map_mul' g h := by apply Subtype.ext; apply Equiv.ext; intro x; apply Subtype.ext; rfl

@[simp] theorem restrict_apply (i : I) (g : S.Aut) (x : P.Point i) :
    (((P.restrict i) g).val x).val = g.val x.val := rfl

def pairRestriction (i j : I) : S.Aut →* (P.Intrinsic i × P.Intrinsic j) where
  toFun g := (P.restrict i g,P.restrict j g)
  map_one' := by simp only [map_one,Prod.one_eq_mk]
  map_mul' g h := by simp only [map_mul,Prod.mk_mul_mk]

def actualPair (i j : I) : Subgroup (P.Intrinsic i × P.Intrinsic j) :=
  (P.pairRestriction i j).range

def projection (A : Finset I) : S.Aut →* (∀ i : ↥A, P.Intrinsic i.val) where
  toFun g i := P.restrict i.val g
  map_one' := by funext i; exact (P.restrict i.val).map_one
  map_mul' g h := by funext i; exact (P.restrict i.val).map_mul g h

def actualImage (A : Finset I) : Subgroup (∀ i : ↥A, P.Intrinsic i.val) :=
  (P.projection A).range

def selectedPoints (A : Finset I) : Set X := {x | ∃ i ∈ A, x ∈ P.axis i}

theorem selectedPoints_finite (A : Finset I) : (P.selectedPoints A).Finite := by
  classical
  let f : (Σ i : ↥A, P.Point i.val) → X := fun p => p.2.val
  have hf : (Set.range f).Finite := Set.finite_range f
  apply hf.subset
  rintro x ⟨i,hi,hx⟩
  exact ⟨⟨⟨i,hi⟩,⟨x,hx⟩⟩,rfl⟩

def selectedFinset (A : Finset I) : Finset X := (P.selectedPoints_finite A).toFinset

@[simp] theorem mem_selectedFinset (A : Finset I) (x : X) :
    x ∈ P.selectedFinset A ↔ ∃ i ∈ A, x ∈ P.axis i := Set.Finite.mem_toFinset _

def unionEquiv (A : Finset I) : (Σ i : ↥A, P.Point i.val) ≃ ↥(P.selectedFinset A) :=
  Equiv.ofBijective
    (fun p => ⟨p.2.val,(P.mem_selectedFinset A _).mpr ⟨p.1.val,p.1.property,p.2.property⟩⟩) (by
      constructor
      · rintro ⟨i,x⟩ ⟨j,y⟩ h
        have hv : x.val = y.val := congrArg Subtype.val h
        have hi : i = j := Subtype.ext (P.disjoint i.val j.val x.val x.property (hv ▸ y.property))
        subst j
        have hxy : x = y := Subtype.ext hv
        subst y
        rfl
      · intro x
        obtain ⟨i,hi,hx⟩ := (P.mem_selectedFinset A x.val).mp x.property
        exact ⟨⟨⟨i,hi⟩,⟨x.val,hx⟩⟩,Subtype.ext rfl⟩)

def selectedPerm (A : Finset I) (p : ∀ i : ↥A, P.Intrinsic i.val) :
    Equiv.Perm ↥(P.selectedFinset A) :=
  (P.unionEquiv A).symm.trans ((Equiv.sigmaCongrRight (fun i => (p i).val)).trans (P.unionEquiv A))

theorem selectedPerm_on_axis (A : Finset I) (p : ∀ i : ↥A, P.Intrinsic i.val)
    (i : ↥A) (x : P.Point i.val) :
    (P.selectedPerm A p (P.unionEquiv A ⟨i,x⟩)).val = ((p i).val x).val := by
  change ((P.unionEquiv A) ((Equiv.sigmaCongrRight (fun i => (p i).val))
    ((P.unionEquiv A).symm ((P.unionEquiv A) ⟨i,x⟩)))).val = _
  rw [Equiv.symm_apply_apply]
  rfl

theorem pair_preserves_binary {i j : I} {g : P.Intrinsic i} {h : P.Intrinsic j}
    (hp : (g,h) ∈ P.actualPair i j) (r : S.Binary) (x : P.Point i) (y : P.Point j) :
    S.binary r ((g.val x).val) ((h.val y).val) ↔ S.binary r x.val y.val := by
  obtain ⟨a,ha⟩ := hp
  have hi := congrArg Prod.fst ha
  have hj := congrArg Prod.snd ha
  have hix : a.val x.val = ((g.val x).val) :=
    congrArg (fun k : P.Intrinsic i => ((k.val x).val)) hi
  have hjy : a.val y.val = ((h.val y).val) :=
    congrArg (fun k : P.Intrinsic j => ((k.val y).val)) hj
  have hh := a.property.2 r x.val y.val
  rw [hix,hjy] at hh
  exact hh

/-- C17: actual pair-image witnesses preserve every cross binary instance.
The WHOLE selected axes form one finite induced partial isomorphism, which
the original full-source homogeneity extends. The ambient complement is
unrestricted and is never patched pointwise.
-/
theorem finite_extension (H : S.Homogeneous) (A : Finset I)
    (p : ∀ i : ↥A, P.Intrinsic i.val)
    (hp : ∀ i j : ↥A, i.val ≠ j.val → (p i,p j) ∈ P.actualPair i.val j.val) :
    ∃ g : S.Aut, P.projection A g = p := by
  classical
  let U := P.selectedFinset A
  let f : ↥U → X := fun x => (P.selectedPerm A p x).val
  have hu : ∀ r x, S.unary r (f x) ↔ S.unary r x.val := by
    intro r x
    obtain ⟨⟨i,a⟩,rfl⟩ := (P.unionEquiv A).surjective x
    change S.unary r (P.selectedPerm A p (P.unionEquiv A ⟨i,a⟩)).val ↔ S.unary r a.val
    rw [P.selectedPerm_on_axis]
    exact (p i).property.1 r a
  have hb : ∀ r x y, S.binary r (f x) (f y) ↔ S.binary r x.val y.val := by
    intro r x y
    obtain ⟨⟨i,a⟩,rfl⟩ := (P.unionEquiv A).surjective x
    obtain ⟨⟨j,b⟩,rfl⟩ := (P.unionEquiv A).surjective y
    change S.binary r (P.selectedPerm A p (P.unionEquiv A ⟨i,a⟩)).val
      (P.selectedPerm A p (P.unionEquiv A ⟨j,b⟩)).val ↔ S.binary r a.val b.val
    rw [P.selectedPerm_on_axis,P.selectedPerm_on_axis]
    by_cases hij : i = j
    · subst j
      exact (p i).property.2 r a b
    · exact P.pair_preserves_binary (hp i j (fun h => hij (Subtype.ext h))) r a b
  obtain ⟨g,hg⟩ := H U f
    (fun x y hxy => (P.selectedPerm A p).injective (Subtype.ext hxy)) hu hb
  refine ⟨g,?_⟩
  funext i
  apply Subtype.ext
  apply Equiv.ext
  intro x
  apply Subtype.ext
  change g.val x.val = ((p i).val x).val
  have hh := hg (P.unionEquiv A ⟨i,x⟩)
  exact hh.trans (P.selectedPerm_on_axis A p i x)

theorem finite_projection (H : S.Homogeneous) (A : Finset I)
    (p : ∀ i : ↥A, P.Intrinsic i.val) :
    p ∈ P.actualImage A ↔
      ∀ i j : ↥A, i.val ≠ j.val → (p i,p j) ∈ P.actualPair i.val j.val := by
  constructor
  · rintro ⟨g,rfl⟩ i j _
    exact ⟨g,rfl⟩
  · exact P.finite_extension H A p

/-- C16: the entire finite named axis gives an actual finite partial map,
so restriction of FULL original Aut is onto its FULL intrinsic group.
-/
theorem restrict_surjective (H : S.Homogeneous) (i : I) : Function.Surjective (P.restrict i) := by
  classical
  intro a
  let A : Finset I := {i}
  let p : ∀ j, P.Intrinsic j := Function.update (fun _ => 1) i a
  obtain ⟨g,hg⟩ := P.finite_extension H A (fun j => p j.val) (by
    intro j k hjk
    have hj : j.val = i := Finset.mem_singleton.mp j.property
    have hk : k.val = i := Finset.mem_singleton.mp k.property
    exact False.elim (hjk (hj.trans hk.symm)))
  refine ⟨g,?_⟩
  have hh := congrFun hg (⟨i,Finset.mem_singleton_self i⟩ : ↥A)
  change P.restrict i g = p i at hh
  simpa only [p,Function.update_self] using hh

theorem actual_pair_subdirect_left (H : S.Homogeneous) (i j : I) (a : P.Intrinsic i) :
    ∃ b : P.Intrinsic j, (a,b) ∈ P.actualPair i j := by
  obtain ⟨g,hg⟩ := P.restrict_surjective H i a
  exact ⟨P.restrict j g,g,by change (P.restrict i g,P.restrict j g) = _; rw [hg]⟩

theorem actual_pair_subdirect_right (H : S.Homogeneous) (i j : I) (b : P.Intrinsic j) :
    ∃ a : P.Intrinsic i, (a,b) ∈ P.actualPair i j := by
  obtain ⟨g,hg⟩ := P.restrict_surjective H j b
  exact ⟨P.restrict i g,g,by change (P.restrict i g,P.restrict j g) = _; rw [hg]⟩

/-- C20: flatness is forced by ONE actual global lift of each prescribed
motion. It is not a cocycle assertion about arbitrarily chosen pair maps.
-/
theorem actual_graph_transport_flat (H : S.Homogeneous) (i j k : I)
    (thetaij : P.Intrinsic i ≃* P.Intrinsic j)
    (thetaik : P.Intrinsic i ≃* P.Intrinsic k)
    (thetajk : P.Intrinsic j ≃* P.Intrinsic k)
    (hij : ∀ a b, (a,b) ∈ P.actualPair i j ↔ thetaij a = b)
    (hik : ∀ a c, (a,c) ∈ P.actualPair i k ↔ thetaik a = c)
    (hjk : ∀ b c, (b,c) ∈ P.actualPair j k ↔ thetajk b = c) :
    thetaik = thetaij.trans thetajk := by
  apply DFunLike.ext
  intro a
  obtain ⟨g,hg⟩ := P.restrict_surjective H i a
  have h1 := (hij (P.restrict i g) (P.restrict j g)).mp ⟨g,rfl⟩
  have h2 := (hik (P.restrict i g) (P.restrict k g)).mp ⟨g,rfl⟩
  have h3 := (hjk (P.restrict j g) (P.restrict k g)).mp ⟨g,rfl⟩
  rw [hg] at h1 h2
  exact h2.trans (h3.symm.trans (congrArg thetajk h1.symm))

end
end NamedAxes
end CCO.FiniteKernel
