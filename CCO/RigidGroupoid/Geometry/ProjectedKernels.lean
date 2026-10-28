import CCO.RigidGroupoid.Geometry.QuotientBijection
import CCO.RigidGroupoid.Geometry.Quotient.Algebra

/-! Projected gates are actual equivalences on the actual finer quotients.
Their quotient WORD exactness is deliberately a separate explicit premise.
All elementary projection equations below are independent of that premise. -/

universe u v w q r
namespace CCO.RigidGroupoid.Geometry
variable {ι : Type u} {X : ι → Type v} {Q : ι → Type q}
variable {S : AtomicSource.{u,v,w} ι X} (T : AtomicSource.{u,q,r} ι Q)

namespace Kernel
variable {i : ι} (A : Kernel S i) (π : X i → Q i)
variable (surjπ : Function.Surjective π)
variable (hEA : ∀ x y, π x = π y → A.rel x y)

include hEA

theorem left_kernel : TRel.comp (GroupActions.kernel π) A.rel = A.rel := by
  funext x y
  apply propext
  constructor
  · rintro ⟨z,hxz,hzy⟩
    exact A.setoid.trans (hEA x z hxz) hzy
  · exact fun h => ⟨x,rfl,h⟩

theorem right_kernel : TRel.comp A.rel (GroupActions.kernel π) = A.rel := by
  funext x y
  apply propext
  constructor
  · rintro ⟨z,hxz,hzy⟩
    exact A.setoid.trans hxz (hEA z y hzy)
  · exact fun h => ⟨y,h,rfl⟩

def projectedSetoid : Setoid (Q i) where
  r := Quotient.image π π A.rel
  iseqv := ⟨by
    intro q
    obtain ⟨x,rfl⟩ := surjπ q
    exact ⟨x,x,rfl,rfl,A.setoid.refl x⟩,
    by
      rintro q r ⟨x,y,hx,hy,hxy⟩
      exact ⟨y,x,hy,hx,A.setoid.symm hxy⟩,
    by
      rintro q r s ⟨x,y,hx,hy,hxy⟩ ⟨y',z,hy',hz,hy'z⟩
      exact ⟨x,z,hx,hz,A.setoid.trans hxy
        (A.setoid.trans (hEA y y' (hy.trans hy'.symm)) hy'z)⟩⟩

theorem projected_pullback :
    GroupActions.pullback π π (A.projectedSetoid π surjπ hEA).r = A.rel := by
  funext x y
  apply propext
  constructor
  · rintro ⟨a,b,ha,hb,hab⟩
    exact A.setoid.trans (hEA x a ha.symm) (A.setoid.trans hab (hEA b y hb))
  · exact fun h => ⟨x,y,rfl,rfl,h⟩

def projectedKernel
    (hExact : FullExact T (A.projectedSetoid π surjπ hEA).r) : Kernel T i :=
  ⟨A.projectedSetoid π surjπ hEA,hExact⟩

end Kernel

namespace Arrow
variable {i j : ι} {A : Kernel S i} {B : Kernel S j} (R : Arrow S A B)
variable (π : X i → Q i) (σ : X j → Q j)
variable (hEA : ∀ x y, π x = π y → A.rel x y)
variable (hEB : ∀ x y, σ x = σ y → B.rel x y)

include hEA hEB

theorem nested_bisaturated : Quotient.Bisaturated π σ R.rel := by
  funext x y
  apply propext
  constructor
  · rintro ⟨b,⟨a,ha,hab⟩,hb⟩
    have hr : R.rel x b := by
      rw [← R.left]
      exact ⟨a,hEA x a ha,hab⟩
    rw [← R.right]
    exact ⟨b,hr,hEB b y hb⟩
  · intro hxy
    exact ⟨y,⟨x,rfl,hxy⟩,rfl⟩

theorem image_pullback_nested :
    GroupActions.pullback π σ (Quotient.image π σ R.rel) = R.rel :=
  Quotient.pullback_image_of_bisaturated π σ R.rel (R.nested_bisaturated π σ hEA hEB)

end Arrow
end CCO.RigidGroupoid.Geometry
