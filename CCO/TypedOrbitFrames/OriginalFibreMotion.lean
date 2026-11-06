import CCO.TypedOrbitFrames.OriginalClassFibre
import CCO.ParityHasse.Original.OrbitalAlgebra

/-!
# B053 D04/C32--C33: one actual old automorphism acts on a whole class fibre

The source11 simultaneous representative argument is not allowed
to choose independent real motions for each quotient coordinate.
In the genuine OLD homogeneous source, for x,y in one ACTUAL
invariant-equivalence class, ANY old-group motion g sending x to y
stabilizes the entire class setwise. For a finite family of
compatible actual original equivalence classes, the SAME motion
preserves all class conditions simultaneously, because its
moved base point lies in every one of them.

This is an original-real action result only. It does NOT claim
the hidden quotient age is homogeneous, nor that the full
hidden automorphism group equals the original acting group,
nor that the fibre has infinitely many J-coordinate orbits.
The latter requires full relative-index infinitude separately.
-/

universe u v w t
namespace CCO.TypedOrbitFrames

open CCO.ParityHasse.Original

variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)
variable {G : Type t} [Group G] [∀ j : ι, MulAction G (X j)]

/-- One actual old-group element that moves x to y within
the SAME original E-class preserves the WHOLE E-class setwise.
Uses the true old colour-invariance and equivalence laws. -/
theorem original_equiv_class_setwise_preserved
    (H : HomogeneousSource S G)
    {i : ι} (E : ColourEq S i)
    (x y : X i) (hxy : E x y)
    (g : G) (hg : g • x = y) :
    ∀ z : X i, E x z ↔ E x (g • z) := by
  have hinv :
      ∀ (h : G) (a b : X i),
        E a b → E (h • a) (h • b) :=
    colourInvariant_groupInvariant S H E.property
  intro z
  constructor
  · intro hxz
    have hyz : E y (g • z) := by
      simpa only [hg] using hinv g x z hxz
    exact E.val.trans hxy hyz
  · intro hxz
    have hyz : E y (g • z) :=
      E.val.trans (E.val.symm hxy) hxz
    have hback := hinv g⁻¹ y (g • z) hyz
    have hleft : g⁻¹ • y = x := by
      rw [← hg, inv_smul_smul]
    simpa only [hleft, inv_smul_smul] using hback

/-- The genuine original setwise stabilizer of an E-class
is transitive on that very E-class. There is ONE old group
element for a specified pair of points, not separately
chosen orbit representatives. -/
theorem original_equiv_class_setwise_transitive
    (H : HomogeneousSource S G)
    {i : ι} (E : ColourEq S i)
    (x y : X i) (hxy : E x y) :
    ∃ g : G, g • x = y ∧
      (∀ z : X i, E x z ↔ E x (g • z)) := by
  obtain ⟨g,hg⟩ := S.original_sort_transitive_of_homogeneous H i x y
  exact ⟨g,hg,original_equiv_class_setwise_preserved S H E x y hxy g hg⟩

/-- For an ACTUAL compatible finite family of original quotient
class vertices, the real action preserving the ENTIRE intersection
is transitive. No independent coordinate-wise choice is made.

The requirement x,y in the literal joint fibre is essential;
the original old-sort transitivity alone does not preserve a
fixed fibre over arbitrary real base anchors. -/
theorem original_actual_class_fibre_motion
    (H : HomogeneousSource S G)
    {i : ι} {m : Nat}
    (E : Fin m → ColourEq S i) (c : Fin m → X i)
    {x y : X i}
    (hx : x ∈ originalActualClassFibre S E c)
    (hy : y ∈ originalActualClassFibre S E c) :
    ∃ g : G, g • x = y ∧
      ∀ z : X i,
        z ∈ originalActualClassFibre S E c ↔
        g • z ∈ originalActualClassFibre S E c := by
  obtain ⟨g,hg⟩ := S.original_sort_transitive_of_homogeneous H i x y
  refine ⟨g,hg,?_⟩
  intro z
  constructor
  · intro hz j
    have hxy : E j x y :=
      (E j).val.trans ((E j).val.symm (hx j)) (hy j)
    have hxz : E j x z :=
      (E j).val.trans ((E j).val.symm (hx j)) (hz j)
    have hxgz :=
      (original_equiv_class_setwise_preserved S H
        (E j) x y hxy g hg z).mp hxz
    exact (E j).val.trans (hx j) hxgz
  · intro hz j
    have hxy : E j x y :=
      (E j).val.trans ((E j).val.symm (hx j)) (hy j)
    have hxgz : E j x (g • z) :=
      (E j).val.trans ((E j).val.symm (hx j)) (hz j)
    have hxz :=
      (original_equiv_class_setwise_preserved S H
        (E j) x y hxy g hg z).mpr hxgz
    exact (E j).val.trans (hx j) hxz

end CCO.TypedOrbitFrames
