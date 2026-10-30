import CCO.PointGeneratedSAP.Copies
import Mathlib.Data.Set.Card

/-! A finite original-stabilizer orbit is contradicted by k+1 actual copies.
The reverse implication never assumes PGO or finite-action avoidance. -/
universe u v
namespace CCO.PointGeneratedSAP
open UnaryFreshFrames
variable {L : Language.{u}} {V : Type v} {H : Structure L V}
variable {O : Original L V H} (C : Interpretation H O)
namespace Interpretation
include C

theorem self_mem_orbitOver (D : Set O.Real) (u : V) : u ∈ C.orbitOver D u := by
  apply (C.mem_orbitOver_iff D u u).mpr
  exact ⟨1,fun _ _ => one_smul _ _,by rw [map_one,one_smul]⟩

/-- C12: a finite original orbit has positive cardinality. -/
theorem finite_orbit_card_pos (D : Set O.Real) (u : V) (hf : (C.orbitOver D u).Finite) :
    0 < (C.orbitOver D u).ncard :=
  (Set.ncard_pos hf).mpr ⟨u,C.self_mem_orbitOver D u⟩

/-- C13: one actual real source places u in a finite PG object over D. -/
theorem exists_extension (D : Set O.Real) (hD : D.Finite) (u : V) :
    ∃ B : Piece O, H.closure (Subtype.val '' D) ⊆ B.points ∧ u ∈ B.points := by
  obtain ⟨r,hr⟩ := C.generating u
  let B := Piece.ofReal C (insert r D) (hD.insert r)
  refine ⟨B,?_,?_⟩
  · exact H.closure_mono (Set.image_mono (Set.subset_insert _ _))
  · apply H.closure_mono (B := Subtype.val '' insert r D) _ hr
    intro x hx
    have he : x = r.val := hx
    exact ⟨r,Set.mem_insert _ _,he.symm⟩

/-- C15–C20: every n supplies distinct points in EXACTLY the original
Aut(M/D)-orbit of u, by genuine common-base original automorphisms. -/
theorem exists_many_orbit_points (hom : O.Homogeneous) (sap : AgeSAP O)
    (D : Set O.Real) (hD : D.Finite) (u : V)
    (hu : u ∉ H.closure (Subtype.val '' D)) (n : ℕ) :
    ∃ f : Fin n → V, Function.Injective f ∧ ∀ i, f i ∈ C.orbitOver D u := by
  let A := Piece.ofReal C D hD
  obtain ⟨B,hAB,huB⟩ := C.exists_extension D hD u
  obtain ⟨g,hfix,hinter⟩ := C.exists_same_base_automorphisms
    (C.freshMotion_of_ageSAP hom sap) A B hAB n
  refine ⟨fun i => C.lift (g i) • u,?_,?_⟩
  · intro i j he
    by_contra hn
    exact hu (hinter i j hn u huB u huB he)
  · intro i
    apply (C.mem_orbitOver_iff D u _).mpr
    refine ⟨g i,?_,rfl⟩
    intro d hd
    apply Subtype.ext
    rw [← C.lift_real]
    exact hfix i d.val (H.subset_closure _ ⟨d,hd,rfl⟩)

/-- C12/C21: k+1 injected into the k-element original orbit is impossible.
No cardinality restriction on the ambient source is imposed. -/
theorem PGO_of_ageSAP (hom : O.Homogeneous) (sap : AgeSAP O) : C.PGO := by
  classical
  intro D hD u hu hf
  let : Fintype (C.orbitOver D u) := hf.fintype
  let k := Fintype.card (C.orbitOver D u)
  obtain ⟨f,hinj,hmem⟩ := C.exists_many_orbit_points hom sap D hD u hu (k+1)
  let q : Fin (k+1) → C.orbitOver D u := fun i => ⟨f i,hmem i⟩
  have hq : Function.Injective q := by
    intro i j he
    exact hinj (congrArg Subtype.val he)
  have hh := Fintype.card_le_of_injective q hq
  have hbad : k+1 ≤ k := by simpa only [Fintype.card_fin] using hh
  exact Nat.not_succ_le_self k hbad

end Interpretation
end CCO.PointGeneratedSAP
