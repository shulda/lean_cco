import CCO.RealClosure.Bounds.Examples.Coordinate

/-! Full automorphism identification with the product of all coordinate
permutation groups; no extra coordinate predicates are named. -/
universe u
namespace CCO.RealClosure.Bounds.Examples.Coordinate
variable (I : Type u) [Fintype I] [DecidableEq I]

def axisPoint (i : I) (n : ℕ) : Point I := fun j => if j = i then n else 0
@[simp] theorem axisPoint_self (i : I) (n : ℕ) : axisPoint I i n i = n := by simp [axisPoint]

def readCoordinate (g : Aut I) (i : I) (n : ℕ) : ℕ := (g • axisPoint I i n) i

theorem aut_evaluate (g : Aut I) (x : Point I) (i : I) :
    (g • x) i = readCoordinate I g i (x i) := by
  have he : x i = axisPoint I i (x i) i := (axisPoint_self I i (x i)).symm
  exact (coordinates_of_colour_eq I (g.property x (axisPoint I i (x i))) i).mpr he

def recoverCoordinate (g : Aut I) (i : I) : Equiv.Perm ℕ where
  toFun := readCoordinate I g i
  invFun := readCoordinate I g⁻¹ i
  left_inv n := by
    change readCoordinate I g⁻¹ i ((g • axisPoint I i n) i) = n
    rw [← aut_evaluate I g⁻¹ (g • axisPoint I i n) i]
    simp only [inv_smul_smul,axisPoint_self]
  right_inv n := by
    change readCoordinate I g i ((g⁻¹ • axisPoint I i n) i) = n
    rw [← aut_evaluate I g (g⁻¹ • axisPoint I i n) i]
    simp only [smul_inv_smul,axisPoint_self]

def coordinateAutHom : (I → Equiv.Perm ℕ) →* Aut I where
  toFun := coordinateAut I
  map_one' := by apply Subtype.ext; apply Equiv.ext; intro x; funext i; rfl
  map_mul' g h := by apply Subtype.ext; apply Equiv.ext; intro x; funext i; rfl

theorem coordinateAut_bijective : Function.Bijective (coordinateAutHom I) := by
  constructor
  · intro g h he
    funext i
    apply Equiv.ext
    intro n
    have hh := congrArg (fun p : Aut I => (p • axisPoint I i n) i) he
    change g i (axisPoint I i n i) = h i (axisPoint I i n i) at hh
    simpa only [axisPoint_self] using hh
  · intro g
    refine ⟨recoverCoordinate I g,?_⟩
    apply Subtype.ext
    apply Equiv.ext
    intro x
    funext i
    exact (aut_evaluate I g x i).symm

noncomputable def fullAutIso : (I → Equiv.Perm ℕ) ≃* Aut I :=
  MulEquiv.ofBijective (coordinateAutHom I) (coordinateAut_bijective I)
end CCO.RealClosure.Bounds.Examples.Coordinate
