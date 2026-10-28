import CCO.RigidGroupoid.Geometry.Basic

/-! Finite-family readout of the accepted original full exact-menu Helly.
This concerns old represented relation intersections, not arbitrary quotient
point sets or different-centre balls. -/

universe u v w t r
namespace CCO.RigidGroupoid.Phase
open Geometry

variable {ι : Type u} {X : ι → Type v} (S : AtomicSource.{u,v,w} ι X)
variable {G : Type t} [Group G] [∀ i, MulAction G (X i)]
variable (H : HomogeneousSource S G) (cco : SemanticCCO.{u,v,max u v,w} S)

include H cco

theorem fullExact_family_helly {i j : ι} {I : Type r} [Fintype I]
    (R : I → TRel X i j) (hR : ∀ a, FullExact S (R a))
    (hPair : ∀ a b, TRel.Nonempty (fun x y => R a x y ∧ R b x y)) :
    TRel.Nonempty (fun x y => ∀ a, R a x y) := by
  classical
  let D (a : I) : RawExact.NonemptyExact S i j := Classical.choose (hR a)
  have hD (a : I) : RawExact.evaluate S (D a).words = R a :=
    Classical.choose_spec (hR a)
  let L := (Finset.univ.toList : List I).map D
  obtain ⟨x,y,hxy⟩ := RawExact.exactMenuHelly_of_CCO S H cco L (by
    intro d hd e he _
    obtain ⟨a,_,rfl⟩ := List.mem_map.mp hd
    obtain ⟨b,_,rfl⟩ := List.mem_map.mp he
    simpa only [hD] using hPair a b)
  refine ⟨x,y,?_⟩
  intro a
  have ha : D a ∈ L := List.mem_map.mpr ⟨a,by simp,rfl⟩
  simpa only [hD] using hxy (D a) ha

end CCO.RigidGroupoid.Phase
