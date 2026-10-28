import CCO.RealClosure.Bounds.Examples.CoordinateAut
import CCO.RealHull.Geometry.ClassSource
import CCO.ParityHasse.Original.OrbitalAlgebra

/-! Every full invariant equivalence of the literal coordinate source is a
coordinate-change equivalence. A fresh third natural value proves the
singleton-support step; no finite snapshot is used. -/
universe u
namespace CCO.RealClosure.Bounds.Examples.Coordinate
open ParityHasse.Original
variable (I : Type u) [Fintype I] [DecidableEq I]

def changeEq (J : Finset I) : ColourEq (source I) () :=
  ⟨⟨fun x y => ∀ i, i ∉ J → x i = y i,
    ⟨fun _ _ _ => rfl,fun h i hi => (h i hi).symm,
      fun h k i hi => (h i hi).trans (k i hi)⟩⟩,
    fun x y x' y' hc => by
      constructor <;> intro h i hi
      · exact (coordinates_of_colour_eq I hc i).mp (h i hi)
      · exact (coordinates_of_colour_eq I hc i).mpr (h i hi)⟩

noncomputable def allowedCoords (E : ColourEq (source I) ()) : Finset I := by
  classical
  exact Finset.univ.filter (fun i => E (fun _ => 0) (axisPoint I i 1))

@[simp] theorem mem_allowed (E : ColourEq (source I) ()) (i : I) :
    i ∈ allowedCoords I E ↔ E (fun _ => 0) (axisPoint I i 1) := by
  classical
  simp [allowedCoords]

/-- An arbitrary old atom in E forces each singleton difference support. -/
theorem equivalence_forces_coordinate (E : ColourEq (source I) ())
    {x y : Point I} (hE : E x y) {i : I} (hi : i ∈ support I x y) :
    i ∈ allowedCoords I E := by
  classical
  let J := support I x y
  let z : Point I := fun j => if j ∈ J then if j = i then 2 else 1 else 0
  have hs0 : support I (fun _ => 0) z = J := by
    ext j
    simp only [mem_support]
    by_cases hj : j ∈ J <;> by_cases hji : j = i <;> simp [z,hj,hji]
  have hs1 : support I z (axisPoint I i 1) = J := by
    ext j
    simp only [mem_support]
    by_cases hj : j ∈ J <;> by_cases hji : j = i
    · subst j; simp [z,hj,axisPoint]
    · simp [z,hj,axisPoint,hji]
    · subst j; exact False.elim (hj hi)
    · simp [z,hj,axisPoint,hji]
  have h0 : E (fun _ => 0) z :=
    (E.property x y (fun _ => 0) z ((colour_eq_iff I _ _ _ _).mpr hs0.symm)).mp hE
  have h1 : E z (axisPoint I i 1) :=
    (E.property x y z (axisPoint I i 1) ((colour_eq_iff I _ _ _ _).mpr hs1.symm)).mp hE
  exact (mem_allowed I E i).mpr (E.val.trans h0 h1)

/-- A permitted coordinate change can take ANY pair differing only there. -/
theorem coordinate_change_mem (E : ColourEq (source I) ()) (i : I)
    (hi : i ∈ allowedCoords I E) (x y : Point I)
    (hxy : ∀ j, j ≠ i → x j = y j) : E x y := by
  classical
  by_cases he : x i = y i
  · have hh : x = y := funext (fun j => by
      by_cases hji : j = i
      · simpa only [hji] using he
      · exact hxy j hji)
    exact hh ▸ E.val.refl x
  have hs : support I x y = support I (fun _ => 0) (axisPoint I i 1) := by
    ext j
    simp only [mem_support]
    by_cases hji : j = i
    · subst j; simp [he,axisPoint]
    · simp [hxy j hji,axisPoint,hji]
  exact (E.property (fun _ => 0) (axisPoint I i 1) x y
    ((colour_eq_iff I _ _ _ _).mpr hs.symm)).mp ((mem_allowed I E i).mp hi)

theorem change_allowed_le (E : ColourEq (source I) ()) :
    changeEq I (allowedCoords I E) ≤ E := by
  classical
  suffices aux : ∀ J : Finset I, J ⊆ allowedCoords I E →
      ∀ x y : Point I, (∀ i, i ∉ J → x i = y i) → E x y by
    exact aux (allowedCoords I E) (Finset.Subset.refl _)
  intro J
  induction J using Finset.induction_on with
  | empty =>
    intro _ x y hxy
    have he : x = y := funext (fun i => hxy i (Finset.notMem_empty _))
    exact he ▸ E.val.refl x
  | @insert i J hi ih =>
    intro hJ x y hxy
    let z : Point I := Function.update x i (y i)
    have hxz : E x z := coordinate_change_mem I E i
      (hJ (Finset.mem_insert_self _ _)) x z (fun j hji => by simp [z,hji])
    have hzy : E z y := ih (fun j hj => hJ (Finset.mem_insert_of_mem hj)) z y (by
      intro j hj
      by_cases hji : j = i
      · subst j; simp [z]
      · simpa [z,hji] using hxy j (by simpa [Finset.mem_insert,hji] using hj))
    exact E.val.trans hxz hzy

@[simp] theorem full_equivalence_classification (E : ColourEq (source I) ()) :
    changeEq I (allowedCoords I E) = E := by
  apply ColourEq.ext
  intro x y
  constructor
  · intro h
    exact (change_allowed_le I E) h
  · intro hxy i hi
    by_contra hne
    exact hi (equivalence_forces_coordinate I E hxy ((mem_support I x y i).mpr hne))

@[simp] theorem allowed_change (J : Finset I) : allowedCoords I (changeEq I J) = J := by
  ext i
  rw [mem_allowed]
  constructor
  · intro hi
    by_contra hn
    have hh := hi i hn
    simpa [axisPoint] using hh
  · intro hi j hj
    have hji : j ≠ i := fun he => hj (he.symm ▸ hi)
    simp [axisPoint,hji]

theorem changeEq_le_iff (J K : Finset I) : changeEq I J ≤ changeEq I K ↔ J ⊆ K := by
  constructor
  · intro h i hi
    rw [← allowed_change I K]
    apply (mem_allowed I (changeEq I K) i).mpr
    apply h
    exact (mem_allowed I (changeEq I J) i).mp (by simpa using hi)
  · intro h x y hxy i hi
    exact hxy i (fun hj => hi (h hj))

noncomputable def fullEquivOrderIso : Finset I ≃o ColourEq (source I) () where
  toFun := changeEq I
  invFun := allowedCoords I
  left_inv := allowed_change I
  right_inv := full_equivalence_classification I
  map_rel_iff' := fun {J K} => changeEq_le_iff I J K

/-- Every nonempty coordinate-change class contains an actual copy of Nat. -/
def classNatEmbedding {J : Finset I} {i : I} (hi : i ∈ J) (x : Point I) :
    ℕ ↪ RealHull.Geometry.ClassPoint (source I) () (changeEq I J) x where
  toFun n := ⟨Function.update x i n,by
    intro j hj
    have hji : j ≠ i := fun he => hj (he.symm ▸ hi)
    simp [hji]⟩
  inj' n m h := by
    have hh := congrArg (fun y : RealHull.Geometry.ClassPoint (source I) () (changeEq I J) x =>
      y.val i) h
    simpa only [Function.update_self] using hh
end CCO.RealClosure.Bounds.Examples.Coordinate
