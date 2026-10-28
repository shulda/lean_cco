import CCO.RealHull.Geometry.ClassHomogeneity
import CCO.RealHull.Geometry.OnePoint
import Mathlib.Data.Fintype.Sum

/-! The actual realised diversity type over one WHOLE finite real anchor.
All predicates are literal original pair colours; no global equivalence or
globalisation is assumed in this file. -/

universe v w t
namespace CCO.RealHull.Geometry

variable {M : Type v} (S : AtomicSource.{0,v,w} Unit (fun _ => M))
variable [DecidableEq M] (A : Finset M) (q : ↥A → Atom S)

def FibreSet : Set M := {y | ∀ a : ↥A, col S y a.val = some (q a)}

theorem fibre_not_anchor (x : FibreSet S A q) : x.val ∉ A := by
  intro hx
  have hh := x.property ⟨x.val,hx⟩
  rw [(col_none S _ _).mpr rfl] at hh
  cases hh

noncomputable abbrev fibreSource [Nonempty (FibreSet S A q)] :=
  inducedSource S () (FibreSet S A q)

def AnchorStabilizer {G : Type t} [Group G] [MulAction G M] : Subgroup G where
  carrier := {g | ∀ a ∈ A, g • a = a}
  one_mem' := by intro a _; exact one_smul _ _
  mul_mem' := by intro g h hg hh a ha; rw [mul_smul,hh a ha,hg a ha]
  inv_mem' := by
    intro g hg a ha
    have hh := congrArg (fun x : M => g⁻¹ • x) (hg a ha)
    simpa only [inv_smul_smul] using hh.symm

variable {G : Type t} [Group G] [MulAction G M]
variable (H : HomogeneousSource S G)
include H

theorem fibre_extension_ambient {V : Type v} [Finite V]
    (f h : V → FibreSet S A q)
    (hc : ∀ x y, col S (f x).val (f y).val = col S (h x).val (h y).val) :
    ∃ g : G, (∀ a ∈ A, g • a = a) ∧ ∀ x, g • (f x).val = (h x).val := by
  letI : Fintype V := Fintype.ofFinite V
  let F : V ⊕ ↥A → Sigma (fun _ : Unit => M) := fun x =>
    ⟨(),Sum.elim (fun v => (f v).val) Subtype.val x⟩
  let J : V ⊕ ↥A → Sigma (fun _ : Unit => M) := fun x =>
    ⟨(),Sum.elim (fun v => (h v).val) Subtype.val x⟩
  have hpair : ∀ x y, taggedColour S (F x) (F y) = taggedColour S (J x) (J y) := by
    intro x y
    have hcolour : col S (F x).2 (F y).2 = col S (J x).2 (J y).2 := by
      cases x with
      | inl x =>
        cases y with
        | inl y => exact hc x y
        | inr a => exact ((f x).property a).trans ((h x).property a).symm
      | inr a =>
        cases y with
        | inl y =>
          exact (col_symm S _ _).trans
            (((f y).property a).trans (((h y).property a).symm.trans (col_symm S _ _)))
        | inr b => rfl
    exact congrArg (fun c => (⟨(),(),c⟩ : Σ i : Unit, Σ j : Unit, Option (S.Atom i j))) hcolour
  obtain ⟨g,hg⟩ := H.extends_finite_diagram F J hpair
  refine ⟨g,?_,?_⟩
  · intro a ha
    exact congrArg (fun x => x.2) (hg (.inr ⟨a,ha⟩))
  · intro x
    exact congrArg (fun x => x.2) (hg (.inl x))

theorem fibre_motion_membership (g : G) (hg : ∀ a ∈ A, g • a = a) (x : M) :
    g • x ∈ FibreSet S A q ↔ x ∈ FibreSet S A q := by
  have hcol (a : ↥A) : col S (g • x) a.val = col S x a.val := by
    have hh := col_invariant S H g x a.val
    rw [hg a.val a.property] at hh
    exact hh
  constructor <;> intro hx a
  · exact (hcol a).symm.trans (hx a)
  · exact (hcol a).trans (hx a)

def fibrePerm (g : G) (hg : ∀ a ∈ A, g • a = a) : Equiv.Perm (FibreSet S A q) where
  toFun x := ⟨g • x.val,(fibre_motion_membership S A q H g hg x.val).mpr x.property⟩
  invFun y := ⟨g⁻¹ • y.val,by
    apply (fibre_motion_membership S A q H g hg (g⁻¹ • y.val)).mp
    simpa only [smul_inv_smul] using y.property⟩
  left_inv x := Subtype.ext (inv_smul_smul g x.val)
  right_inv x := Subtype.ext (smul_inv_smul g x.val)

def fibreAutMotion (g : G) (hg : ∀ a ∈ A, g • a = a) :
    inducedAut S () (FibreSet S A q) :=
  ⟨fibrePerm S A q H g hg,fun x y =>
    (inducedColour_eq_iff S () _ _ _ _ _).mpr (col_invariant S H g x.val y.val)⟩

theorem fibre_finite_extension {V : Type v} [Finite V]
    (f h : V → FibreSet S A q)
    (hc : ∀ x y, col S (f x).val (f y).val = col S (h x).val (h y).val) :
    ∃ g : inducedAut S () (FibreSet S A q), ∀ x, g • f x = h x := by
  classical
  by_cases hv : Nonempty V
  · obtain ⟨g,hfix,hg⟩ := fibre_extension_ambient S A q H f h hc
    exact ⟨fibreAutMotion S A q H g hfix, fun x => Subtype.ext (hg x)⟩
  · exact ⟨1,fun x => False.elim (hv ⟨x⟩)⟩

theorem fibre_homogeneous [Nonempty (FibreSet S A q)] :
    HomogeneousSource (fibreSource S A q) (inducedAut S () (FibreSet S A q)) :=
  induced_homogeneous_of_extension S () _ (fibre_finite_extension S A q H)

theorem fibre_transitive_ambient (x y : FibreSet S A q) :
    ∃ g : G, (∀ a ∈ A, g • a = a) ∧ g • x.val = y.val := by
  obtain ⟨g,hfix,hg⟩ := fibre_extension_ambient S A q H
    (fun _ : ULift.{v} Unit => x) (fun _ => y)
    (by intro a b; exact ((col_none S _ _).mpr rfl).trans ((col_none S _ _).mpr rfl).symm)
  exact ⟨g,hfix,hg (ULift.up ())⟩

/-- The stabilizer orbit is EXACTLY the displayed finite conjunction of
original spoke formulas (and consequently avoids each named parameter).
-/
theorem fibre_orbit_eq (x : FibreSet S A q) :
    {y : M | ∃ g : G, (∀ a ∈ A, g • a = a) ∧ g • x.val = y} = FibreSet S A q := by
  ext y
  constructor
  · rintro ⟨g,hfix,rfl⟩
    exact (fibre_motion_membership S A q H g hfix x.val).mpr x.property
  · intro hy
    exact fibre_transitive_ambient S A q H x ⟨y,hy⟩

theorem finite_fibre_iff_finite_stabilizer_orbit (x : FibreSet S A q) :
    (FibreSet S A q).Finite ↔
      {y : M | ∃ g : G, (∀ a ∈ A, g • a = a) ∧ g • x.val = y}.Finite := by
  rw [fibre_orbit_eq S A q H x]

omit H in
/-- Every actually occurring internal colour satisfies every original square
constraint, over the SAME whole anchor.
-/
theorem fibre_atom_square (c : InducedAtom S () (FibreSet S A q)) (a : ↥A) :
    c.val ∈ square S (q a) := by
  obtain ⟨x,y,hxy⟩ := c.property
  exact ⟨x.val,a.val,y.val,x.property a,(col_symm S _ _).trans (y.property a),hxy⟩

end CCO.RealHull.Geometry
