import CCO.FinitePackets.Normalization.Translations
import CCO.Owners.Product.Orbitals

/-! A single endpoint switch takes ONE actual original pair orbital to ONE
pair orbital, including equality.  Only after deriving the two-endpoint law
do we promote a translation to an automorphism of the complete original
orbital language.  No freeness of its action on colours is asserted. -/
universe v w t
namespace CCO.FinitePackets.Normalization
open CCO.RealHull.Geometry CCO.ParityHasse.Original
variable {M : Type v} (S : AtomicSource.{0,v,w} Unit (fun _ => M))
variable (F : ColourEq S ()) {G : Type t} [Group G] [MulAction G M]
variable (H : HomogeneousSource S G)

noncomputable def colourPair (c : FullColour S) : M × M :=
  ⟨Classical.choose (colour_realized S c),
    Classical.choose (Classical.choose_spec (colour_realized S c))⟩

theorem colourPair_colour (c : FullColour S) :
    col S (colourPair S c).1 (colourPair S c).2 = c :=
  Classical.choose_spec (Classical.choose_spec (colour_realized S c))

include H

noncomputable def switchColour (e : Translation S F G) (c : FullColour S) : FullColour S :=
  col S (e.val (colourPair S c).1) (colourPair S c).2

theorem switchColour_at (e : Translation S F G) (c : FullColour S) {x y : M}
    (hxy : col S x y = c) : col S (e.val x) y = switchColour S F e c := by
  obtain ⟨g,hgx,hgy⟩ := S.pair_homogeneous_of_homogeneous H
    (colourPair S c).1 x (colourPair S c).2 y ((colourPair_colour S c).trans hxy.symm)
  rw [← hgx,← hgy,translation_equivariant S F G e g (colourPair S c).1]
  exact col_invariant S H g _ _

theorem switchColour_left (e : Translation S F G) (x y : M) :
    col S (e.val x) y = switchColour S F e (col S x y) :=
  switchColour_at S F H e _ rfl

theorem switchColour_right (e : Translation S F G) (x y : M) :
    col S x (e.val y) = switchColour S F e (col S x y) := by
  rw [col_symm S x (e.val y),switchColour_left S F H e y x,col_symm S y x]

theorem switchColour_mul (e f : Translation S F G) (c : FullColour S) :
    switchColour S F (e * f) c = switchColour S F e (switchColour S F f c) := by
  let p := colourPair S c
  calc
    switchColour S F (e * f) c = col S (e.val (f.val p.1)) p.2 := rfl
    _ = switchColour S F e (col S (f.val p.1) p.2) := switchColour_left S F H e _ _
    _ = switchColour S F e (switchColour S F f c) := rfl

omit H in
@[simp] theorem switchColour_one (c : FullColour S) :
    switchColour S F (1 : Translation S F G) c = c := colourPair_colour S c

variable (hthin : ThinBottom S F)
include hthin

theorem switchColour_involutive (e : Translation S F G) :
    Function.Involutive (switchColour S F e) := by
  intro c
  rw [← switchColour_mul S F H,translation_square S F H hthin,switchColour_one]

noncomputable def switchColourPerm (e : Translation S F G) : Equiv.Perm (FullColour S) where
  toFun := switchColour S F e
  invFun := switchColour S F e
  left_inv := switchColour_involutive S F H hthin e
  right_inv := switchColour_involutive S F H hthin e

/-- Literal represented composition of one thin old atom with ANY old atom. -/
theorem thin_atom_product (e : Translation S F G) (c : FullColour S) :
    prod S {translationColour S F (G := G) e} {c} = {switchColour S F e c} := by
  ext d
  constructor
  · rintro ⟨x,y,z,hxy,hyz,hxz⟩
    have hneigh : e.val x = y := by
      exact ((hthin _ (translationColour_below S F H e) x).unique
        (translationColour_at S F H e x) (Set.mem_singleton_iff.mp hxy))
    have hinv : e.val y = x := by
      have he := congrArg (fun f : Translation S F G => f.val x)
        (translation_square S F H hthin e)
      change e.val (e.val x) = x at he
      simpa only [hneigh] using he
    have hs := switchColour_at S F H e c (Set.mem_singleton_iff.mp hyz)
    rw [hinv] at hs
    exact Set.mem_singleton_iff.mpr (hxz.symm.trans hs)
  · intro hd
    have hd' : d = switchColour S F e c := hd
    let p := colourPair S c
    refine ⟨e.val p.1,p.1,p.2,?_,colourPair_colour S c,?_⟩
    · exact (col_symm S _ _).trans (translationColour_at S F H e p.1)
    · exact hd'.symm

/-- The equality-inclusive source transport formula. -/
theorem two_endpoint_transport (e f : Translation S F G) (x y : M) :
    col S (e.val x) (f.val y) = switchColour S F (e * f) (col S x y) := by
  rw [switchColour_left S F H,switchColour_right S F H,← switchColour_mul S F H]

theorem translation_preserves_colour (e : Translation S F G) (x y : M) :
    col S (e.val x) (e.val y) = col S x y := by
  rw [two_endpoint_transport S F H hthin,translation_square S F H hthin,switchColour_one]

/-- This is the accepted FULL orbital automorphism type, on the original M. -/
def translationAut (e : Translation S F G) : CCO.Owners.Product.OrbitalAut G M id := by
  refine ⟨e.val,(CCO.Owners.Product.mem_orbitalAut_iff e.val).mpr ?_⟩
  intro x y
  obtain ⟨g,hgx,hgy⟩ := S.pair_homogeneous_of_homogeneous H x (e.val x) y (e.val y)
    (translation_preserves_colour S F H hthin e x y).symm
  exact ⟨g,hgx,hgy⟩

def translationAutHom : Translation S F G →* CCO.Owners.Product.OrbitalAut G M id where
  toFun := translationAut S F H hthin
  map_one' := Subtype.ext rfl
  map_mul' _ _ := Subtype.ext rfl

theorem fullAut_preserves_colour (k : CCO.Owners.Product.OrbitalAut G M id) (x y : M) :
    col S (k.val x) (k.val y) = col S x y := by
  obtain ⟨g,hgx,hgy⟩ := CCO.Owners.Product.orbitalAut_pair k x y
  change g • x = k.val x at hgx
  change g • y = k.val y at hgy
  rw [← hgx,← hgy]
  exact col_invariant S H g x y

/-- Centrality against EVERY actual original automorphism, beyond the
displayed homogeneous motion group G used to build the translations. -/
theorem translation_central (e : Translation S F G)
    (k : CCO.Owners.Product.OrbitalAut G M id) :
    translationAut S F H hthin e * k = k * translationAut S F H hthin e := by
  apply Subtype.ext
  apply Equiv.ext
  intro x
  change e.val (k.val x) = k.val (e.val x)
  exact ((hthin _ (translationColour_below S F H e) (k.val x)).unique
    (translationColour_at S F H e (k.val x))
    ((fullAut_preserves_colour S F H hthin k x (e.val x)).trans
      (translationColour_at S F H e x)))

end CCO.FinitePackets.Normalization
