import CCO.RawOrbitals

universe v
namespace CCO.ParityHasse.Relative
section Relations
variable {A : Type v}
abbrev Rel (A : Type v) := A → A → Prop
abbrev mul (R T : Rel A) : Rel A := RawSymmetric.compose R T

def Bisaturated (K : Setoid A) (R : Rel A) : Prop :=
  mul K R = R ∧ mul R K = R

theorem mul_assoc (R T U : Rel A) : mul (mul R T) U = mul R (mul T U) := by
  funext x y; apply propext
  constructor
  · rintro ⟨z, ⟨q,hxq,hqz⟩,hzy⟩; exact ⟨q,hxq,z,hqz,hzy⟩
  · rintro ⟨q,hxq,z,hqz,hzy⟩; exact ⟨z,⟨q,hxq,hqz⟩,hzy⟩

theorem mul_mono {R T U V : Rel A} (hRU : R ≤ U) (hTV : T ≤ V) :
    mul R T ≤ mul U V := by
  rintro x y ⟨z,hxz,hzy⟩; exact ⟨z,hRU _ _ hxz,hTV _ _ hzy⟩

theorem bisaturated_self (K : Setoid A) : Bisaturated K K := by
  have h : mul K K = K := by
    funext x y; apply propext
    exact ⟨fun ⟨_,h,k⟩ => K.trans h k, fun h => ⟨y,h,K.refl y⟩⟩
  exact ⟨h,h⟩

theorem Bisaturated.left {K : Setoid A} {R : Rel A} (h : Bisaturated K R)
    {x y z : A} (hxy : K x y) (hyz : R y z) : R x z := by
  rw [← h.1]; exact ⟨y,hxy,hyz⟩

theorem Bisaturated.right {K : Setoid A} {R : Rel A} (h : Bisaturated K R)
    {x y z : A} (hxy : R x y) (hyz : K y z) : R x z := by
  rw [← h.2]; exact ⟨y,hxy,hyz⟩

theorem Bisaturated.mul {K : Setoid A} {R T : Rel A}
    (hR : Bisaturated K R) (hT : Bisaturated K T) : Bisaturated K (mul R T) := by
  constructor
  · rw [← mul_assoc, hR.1]
  · rw [mul_assoc, hT.2]

end Relations
end CCO.ParityHasse.Relative
