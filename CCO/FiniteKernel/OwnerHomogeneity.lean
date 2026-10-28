import CCO.FiniteKernel.ActualMarginals
import Mathlib.Data.Fintype.Sigma
import Mathlib.Data.Finset.Union
import Mathlib.Data.Set.Finite.Range
import Mathlib.Logic.Function.Basic

/-! Relative OWNER-EXPANSION homogeneity extends every local solution on a
finite union of WHOLE fibres. Original reduct homogeneity is not substituted.
The actual global group of this expansion is precisely the owner kernel.
-/

universe u v w z
namespace CCO.FiniteKernel.FinitePartition
noncomputable section
variable {X : Type u} {S : BinaryStructure.{u,v,w} X} {I : Type z}
variable (P : FinitePartition S I)

def selectedPoints (A : Finset I) : Set X := {x | P.owner x ∈ A}

theorem selectedPoints_finite (A : Finset I) : (P.selectedPoints A).Finite := by
  classical
  letI : ∀ i : ↥A, Fintype (P.Fibre i.val) := fun _ => Fintype.ofFinite _
  let f : (Σ i : ↥A, P.Fibre i.val) → X := fun p => p.2.val
  have hf : (Set.range f).Finite := Set.finite_range f
  apply hf.subset
  intro x hx
  exact ⟨⟨⟨P.owner x,hx⟩,⟨x,rfl⟩⟩,rfl⟩

def selectedFinset (A : Finset I) : Finset X := (P.selectedPoints_finite A).toFinset

@[simp] theorem mem_selectedFinset (A : Finset I) (x : X) :
    x ∈ P.selectedFinset A ↔ P.owner x ∈ A := Set.Finite.mem_toFinset _

def extendAssignment [DecidableEq I] (A : Finset I) (h : P.solutions A) :
    ∀ i, P.Intrinsic i := fun i => if hi : i ∈ A then h.val ⟨i,hi⟩ else 1

theorem assembled_unary (p : ∀ i, P.Intrinsic i) (r : S.Unary) (x : X) :
    S.unary r (P.assemble p x) ↔ S.unary r x := by
  rw [P.assemble_on_fibre p (P.owner x) ⟨x,rfl⟩]
  exact (p (P.owner x)).property.1 r ⟨x,rfl⟩

theorem assembled_selected_binary [DecidableEq I] (A : Finset I) (h : P.solutions A)
    (r : S.Binary) (x y : X) (hx : P.owner x ∈ A) (hy : P.owner y ∈ A) :
    S.binary r (P.assemble (P.extendAssignment A h) x)
      (P.assemble (P.extendAssignment A h) y) ↔ S.binary r x y := by
  let p := P.extendAssignment A h
  by_cases hxy : P.owner x = P.owner y
  · let xx : P.Fibre (P.owner x) := ⟨x,rfl⟩
    let yy : P.Fibre (P.owner x) := ⟨y,hxy.symm⟩
    rw [P.assemble_on_fibre p (P.owner x) xx,P.assemble_on_fibre p (P.owner x) yy]
    exact (p (P.owner x)).property.2 r xx yy
  · let xx : P.Fibre (P.owner x) := ⟨x,rfl⟩
    let yy : P.Fibre (P.owner y) := ⟨y,rfl⟩
    rw [P.assemble_on_fibre p (P.owner x) xx,P.assemble_on_fibre p (P.owner y) yy]
    have hp := h.property ⟨P.owner x,hx⟩ ⟨P.owner y,hy⟩ hxy
    simpa only [p,extendAssignment,dite_eq_left hx,dite_eq_left hy] using hp.1 r xx yy

/-- C09 actual finite projection equality under homogeneity of the expansion
naming EVERY owner. This statement has no countability premise. -/
theorem owner_homogeneous_extension
    (H : (S.ownerExpansion P.owner).Homogeneous)
    (A : Finset I) (h : P.solutions A) :
    ∃ n : P.kernel, P.projection A n = h.val := by
  classical
  let p := P.extendAssignment A h
  let U := P.selectedFinset A
  let f : ↥U → X := fun x => P.assemble p x.val
  have hu : ∀ r x, (S.ownerExpansion P.owner).unary r (f x) ↔
      (S.ownerExpansion P.owner).unary r x.val := by
    intro r x
    cases r with
    | inl r => exact P.assembled_unary p r x.val
    | inr i =>
      change P.owner (P.assemble p x.val) = i ↔ P.owner x.val = i
      rw [P.assemble_owner]
  have hb : ∀ r x y, (S.ownerExpansion P.owner).binary r (f x) (f y) ↔
      (S.ownerExpansion P.owner).binary r x.val y.val := by
    intro r x y
    exact P.assembled_selected_binary A h r x.val y.val
      ((P.mem_selectedFinset A x.val).mp x.property)
      ((P.mem_selectedFinset A y.val).mp y.property)
  obtain ⟨g,hg⟩ := H U f
    (fun x y hxy => Subtype.ext ((P.assemble p).injective hxy)) hu hb
  have hgp := (S.ownerExpansion_aut_iff P.owner g.val).mp g.property
  let n : P.kernel := ⟨⟨g.val,hgp.1⟩,(P.mem_kernel_iff _).mpr hgp.2⟩
  refine ⟨n,?_⟩
  funext i
  apply Subtype.ext
  apply Equiv.ext
  intro x
  apply Subtype.ext
  have hx : x.val ∈ U := by
    apply (P.mem_selectedFinset A x.val).mpr
    simpa only [x.property] using i.property
  have hp : p i.val = h.val i := by simp only [p,extendAssignment,dite_eq_left i.property]
  exact (hg ⟨x.val,hx⟩).trans ((P.assemble_on_fibre p i.val x).trans
    (congrArg (fun a : P.Intrinsic i.val => ((a.val x).val)) hp))

theorem owner_homogeneous_projection
    (H : (S.ownerExpansion P.owner).Homogeneous) (A : Finset I) :
    Set.range (P.projection A) = (P.solutions A : Set (∀ i : ↥A, P.Intrinsic i.val)) := by
  ext g
  constructor
  · rintro ⟨n,rfl⟩
    exact P.projection_solution A n
  · intro hg
    exact P.owner_homogeneous_extension H A ⟨g,hg⟩

theorem owner_homogeneous_binding
    (H : (S.ownerExpansion P.owner).Homogeneous) (i : I) : P.binding i = ⊤ := by
  classical
  apply top_unique
  intro g _
  let A : Finset I := {i}
  let p : ∀ j, P.Intrinsic j := Function.update (fun _ => 1) i g
  have hp : (fun j : ↥A => p j.val) ∈ P.solutions A := by
    intro j k hjk
    have hj : j.val = i := Finset.mem_singleton.mp j.property
    have hk : k.val = i := Finset.mem_singleton.mp k.property
    exact False.elim (hjk (hj.trans hk.symm))
  obtain ⟨n,hn⟩ := P.owner_homogeneous_extension H A ⟨_,hp⟩
  refine ⟨n,?_⟩
  have hh := congrFun hn (⟨i,Finset.mem_singleton_self i⟩ : ↥A)
  change P.restrictFibre i n = p i at hh
  simpa only [p,Function.update_self] using hh

theorem owner_homogeneous_pair
    (H : (S.ownerExpansion P.owner).Homogeneous) (i j : I) (hij : i ≠ j) :
    P.actualPair i j = P.pairGroup i j := by
  classical
  ext gh
  constructor
  · exact P.actual_pair_compatible hij
  · intro hgh
    change P.Compatible gh.1 gh.2 at hgh
    let p : ∀ k, P.Intrinsic k := Function.update (Function.update (fun _ => 1) j gh.2) i gh.1
    let A : Finset I := {i,j}
    have hp : (fun a : ↥A => p a.val) ∈ P.solutions A := by
      rintro ⟨a,ha⟩ ⟨b,hb⟩ hab
      change a ≠ b at hab
      simp only [A,Finset.mem_insert,Finset.mem_singleton] at ha hb
      rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
      · exact False.elim (hab rfl)
      · simpa [p,hij,hij.symm] using hgh
      · simpa [p,hij,hij.symm] using (Compatible.symm P hgh)
      · exact False.elim (hab rfl)
    obtain ⟨n,hn⟩ := P.owner_homogeneous_extension H A ⟨_,hp⟩
    refine ⟨n,?_⟩
    apply Prod.ext
    · have hh := congrFun hn (⟨i,by simp [A]⟩ : ↥A)
      change P.restrictFibre i n = gh.1
      simpa [projection,p] using hh
    · have hh := congrFun hn (⟨j,by simp [A]⟩ : ↥A)
      change P.restrictFibre j n = gh.2
      simpa [projection,p,hij.symm] using hh

end
end CCO.FiniteKernel.FinitePartition
