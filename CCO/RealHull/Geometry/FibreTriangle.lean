import CCO.RealHull.Geometry.FibreFullness
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases

/-! Original legal triangles of fibre palette colours are realised INSIDE the
actual fibre over its whole fixed anchor. Internal triangle legality is a
CONCLUSION, not an extra premise for one-cover square transfer. -/

universe v w t
namespace CCO.RealHull.Geometry

variable {M : Type v} (S : AtomicSource.{0,v,w} Unit (fun _ => M))
variable [DecidableEq M] (A : Finset M) (q : ↥A → Atom S)
variable [Nonempty (FibreSet S A q)]
variable {G : Type t} [Group G] [MulAction G M]

theorem original_triangle_in_fibre (H : HomogeneousSource S G)
    (cco : SemanticCCO.{0,v,0,w} S)
    (a b c : InducedAtom S () (FibreSet S A q))
    (htri : S.Triangle a.val b.val c.val) :
    (fibreSource S A q).Triangle (i := ()) (j := ()) (k := ()) a b c := by
  obtain ⟨x,y,z,hxy,hyz,hxz⟩ := htri
  change col S x y = some a.val at hxy
  change col S y z = some b.val at hyz
  change col S x z = some c.val at hxz
  let old : Fin 3 → M := ![x,y,z]
  let edge : Fin 3 → Fin 3 → Option (InducedAtom S () (FibreSet S A q)) :=
    ![![none,some a,some c],![some a,none,some b],![some c,some b,none]]
  let D : CompleteDiagram (S := fibreSource S A q) (Fin 3) := {
    diagram := {
      finite_type := inferInstance
      vertexSort := fun _ => ()
      edge := fun x y _ => edge x y
      edge_reverse := by intro x y _ d; fin_cases x <;> fin_cases y <;> rfl
    }
    complete := by
      intro x y hne
      fin_cases x <;> fin_cases y
      all_goals first
        | exact False.elim (hne rfl)
        | exact ⟨a,rfl⟩
        | exact ⟨b,rfl⟩
        | exact ⟨c,rfl⟩
  }
  have hdiag (x : M) : col S x x = none := (col_none S _ _).mpr rfl
  have hold (i j : Fin 3) : (edge i j).map Subtype.val = col S (old i) (old j) := by
    fin_cases i <;> fin_cases j
    · exact (hdiag x).symm
    · exact hxy.symm
    · exact hxz.symm
    · exact ((col_symm S y x).trans hxy).symm
    · exact (hdiag y).symm
    · exact hyz.symm
    · exact ((col_symm S z x).trans hxz).symm
    · exact ((col_symm S z y).trans hyz).symm
    · exact (hdiag z).symm
  have hOriginal : FibreOriginalTriangles S A q D := by
    intro i j k hij hjk hik d e f hd he hf
    change edge i j = some d at hd
    change edge j k = some e at he
    change edge i k = some f at hf
    refine ⟨old i,old j,old k,?_,?_,?_⟩
    · exact (hold i j).symm.trans (by rw [hd]; rfl)
    · exact (hold j k).symm.trans (by rw [he]; rfl)
    · exact (hold i k).symm.trans (by rw [hf]; rfl)
  obtain ⟨point,_,hp⟩ := original_complete_in_fibre S A q H cco D hOriginal
  refine ⟨point 0,point 1,point 2,?_,?_,?_⟩
  · exact (inducedColour_some_iff S () _ _ _ a).mpr (hp 0 1 (by decide) a rfl)
  · exact (inducedColour_some_iff S () _ _ _ b).mpr (hp 1 2 (by decide) b rfl)
  · exact (inducedColour_some_iff S () _ _ _ c).mpr (hp 0 2 (by decide) c rfl)

end CCO.RealHull.Geometry
