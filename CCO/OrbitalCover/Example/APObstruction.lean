import CCO.OrbitalCover.Example.Orientation
import CCO.RelationalCompletion.Relational.Homogeneous
import Mathlib.Data.Fin.VecNotation

/-! An actual finite-age ordinary-AP obstruction for EVERY orientation.
The two off-base images may initially coincide; opposite unary values
exclude this escape before any diversity-colour argument is made. -/
namespace CCO.OrbitalCover.Example
open scoped CharTwo
namespace Obstruction

def b (h : Nat → Nat → Bit) (ε : Bit) : Point := ⟨0,0,ε,ε+h 0 0,0⟩
def d (h : Nat → Nat → Bit) : Point := ⟨1,1,h 1 1,0,0⟩
def z (ε : Bit) : Point := ⟨0,1,ε,0,0⟩

@[simp] theorem b_d (h : Nat → Nat → Bit) (ε : Bit) :
    colour (b h ε) (d h)=some (none,none) := by
  simp [colour,pattern,coordinateColour,b,d,Point.mk.injEq]
@[simp] theorem b_z (h : Nat → Nat → Bit) (ε : Bit) :
    colour (b h ε) (z ε)=some (some 0,none) := by
  simp [colour,pattern,coordinateColour,b,z,Point.mk.injEq]
@[simp] theorem z_d (h : Nat → Nat → Bit) (ε : Bit) :
    colour (z ε) (d h)=some (none,some 0) := by
  simp [colour,pattern,coordinateColour,z,d,Point.mk.injEq]

def leg (h : Nat → Nat → Bit) (ε : Bit) (j : Fin 3) : Point :=
  if j=0 then b h ε else if j=1 then d h else z ε
def base (h : Nat → Nat → Bit) (ε : Bit) (j : Fin 2) : Point :=
  if j=0 then b h ε else d h
def inclusion : Fin 2 ↪ Fin 3 :=
  ⟨fun j => ⟨j.val,Nat.lt_trans j.isLt (by decide)⟩,by
    intro i j heq
    exact Fin.ext (congrArg (fun k : Fin 3 => k.val) heq)⟩

@[simp] theorem leg_zero (h) (ε) : leg h ε 0=b h ε := by simp [leg]
@[simp] theorem leg_one (h) (ε) : leg h ε 1=d h := by simp [leg]
@[simp] theorem leg_two (h) (ε) : leg h ε 2=z ε := by simp [leg]
@[simp] theorem leg_inclusion (h) (ε) (j : Fin 2) :
    leg h ε (inclusion j)=base h ε j := by
  fin_cases j
  · change leg h ε 0=b h ε
    exact leg_zero h ε
  · change leg h ε 1=d h
    exact leg_one h ε

theorem leg_injective (h) (ε) : Function.Injective (leg h ε) := by
  intro x y heq
  fin_cases x <;> fin_cases y <;>
    simp [leg,b,d,z,Point.mk.injEq] at heq ⊢

theorem base_injective (h) (ε) : Function.Injective (base h ε) := by
  have he : base h ε=leg h ε ∘ inclusion := by
    funext j; exact (leg_inclusion h ε j).symm
  rw [he]
  exact (leg_injective h ε).comp inclusion.injective

theorem base_colours (h) (ε δ : Bit) (i j : Fin 2) :
    colour (base h ε i) (base h ε j)=colour (base h δ i) (base h δ j) := by
  fin_cases i <;> fin_cases j <;>
    simp [base,colour,pattern,coordinateColour,b,d,Point.mk.injEq]

theorem marks {P : Point → Bit} (hP : Orientation P) (ε : Bit) :
    P (b (orientationOffset P) ε)=0 ∧
    P (d (orientationOffset P))=0 ∧
    P (z ε)=ε+orientationOffset P 0 1 := by
  simp [orientation_normal_form hP,b,d,z,add_assoc]

theorem base_marks {P : Point → Bit} (hP : Orientation P) (ε : Bit) (i : Fin 2) :
    P (base (orientationOffset P) ε i)=0 := by
  fin_cases i
  · exact (marks hP ε).1
  · exact (marks hP ε).2.1

/-- Both base paths force the complete owner of two extension images
to agree. This includes logical identity as a possible input; marks
will subsequently rule out that identification. -/
theorem owner_forced {B D Z₀ Z₁ : Point}
    (hb0 : colour B Z₀=some (some 0,none))
    (hb1 : colour B Z₁=some (some 0,none))
    (hd0 : colour Z₀ D=some (none,some 0))
    (hd1 : colour Z₁ D=some (none,some 0)) :
    ownerSetoid Z₀ Z₁ := by
  have hb0' := congrArg Prod.fst ((colour_some _ _ _).mp hb0).2
  have hb1' := congrArg Prod.fst ((colour_some _ _ _).mp hb1).2
  have hd0' := congrArg Prod.snd ((colour_some _ _ _).mp hd0).2
  have hd1' := congrArg Prod.snd ((colour_some _ _ _).mp hd1).2
  have hbu0 := (coordinateColour_some _ _ _ _ _).mp hb0'
  have hbu1 := (coordinateColour_some _ _ _ _ _).mp hb1'
  have hdv0 := (coordinateColour_some _ _ _ _ _).mp hd0'
  have hdv1 := (coordinateColour_some _ _ _ _ _).mp hd1'
  apply (owner_iff _ _).mpr
  exact ⟨hbu0.1.symm.trans hbu1.1,hdv0.1.trans hdv1.1.symm,
    (CharTwo.add_eq_zero.mp hbu0.2).symm.trans (CharTwo.add_eq_zero.mp hbu1.2),
    (CharTwo.add_eq_zero.mp hdv0.2).trans (CharTwo.add_eq_zero.mp hdv1.2).symm⟩

end Obstruction

open RelationalCompletion.Relational

inductive MarkedSymbol : Nat → Type
  | unary (b : Bit) : MarkedSymbol 1
  | binary (c : Colour) : MarkedSymbol 2

def markedLanguage : Language := ⟨MarkedSymbol⟩

/-- The actual original nine binary colours and the one unary bit label
(written by its two complementary unary atoms). -/
def markedModel (P : Point → Bit) : Structure markedLanguage Point where
  rel R xs := match R with
    | .unary b => P (xs 0)=b
    | .binary c => colour (xs 0) (xs 1)=some c

def markedPullback {V : Type} (P : Point → Bit) (f : V → Point) :
    Structure markedLanguage V where
  rel R xs := (markedModel P).rel R (f ∘ xs)

def actualMarkedEmbedding {V : Type} (P : Point → Bit) (f : V → Point)
    (hf : Function.Injective f) :
    Structure.Embedding (markedPullback P f) (markedModel P) :=
  ⟨f,hf,fun _ _ => Iff.rfl⟩

def markedMap {V W : Type} (P : Point → Bit) (f : V → Point) (g : W → Point)
    (e : V ↪ W)
    (hc : ∀ x y, colour (g (e x)) (g (e y))=colour (f x) (f y))
    (hp : ∀ x, P (g (e x))=P (f x)) :
    Structure.Embedding (markedPullback P f) (markedPullback P g) where
  point := e
  injective := e.injective
  rel_iff := by
    intro n R xs
    cases R with
    | unary b => change P (g (e (xs 0)))=b ↔ P (f (xs 0))=b; rw [hp]
    | binary c =>
      change (colour (g (e (xs 0))) (g (e (xs 1)))=some c) ↔
        (colour (f (xs 0)) (f (xs 1))=some c)
      rw [hc]

theorem markedEmbedding_mark {V : Type} {P : Point → Bit} {f : V → Point}
    (e : Structure.Embedding (markedPullback P f) (markedModel P)) (x : V) :
    P (e.point x)=P (f x) := by
  exact (e.rel_iff (.unary (P (f x))) (fun _ => x)).mpr rfl

theorem markedEmbedding_colour {V : Type} {P : Point → Bit} {f : V → Point}
    (e : Structure.Embedding (markedPullback P f) (markedModel P))
    (x y : V) (c : Colour) (hc : colour (f x) (f y)=some c) :
    colour (e.point x) (e.point y)=some c :=
  (e.rel_iff (.binary c) ![x,y]).mpr hc

/-- C29–C35, `prop:bad-diagonal-split`: the actual finite relational age
fails ordinary AP for EVERY predicate orienting the preselected cover.
No homogeneity, definability or regularity of that predicate is assumed. -/
theorem every_orientation_not_AP {P : Point → Bit} (hP : Orientation P) :
    ¬ (markedModel P).AgeAP := by
  intro hap
  let h := orientationOffset P
  let A := markedPullback P (Obstruction.base h 0)
  let B := markedPullback P (Obstruction.leg h 0)
  let C := markedPullback P (Obstruction.leg h 1)
  let s : Structure.Embedding A B := markedMap P _ _ Obstruction.inclusion
    (by intro x y; simp) (by intro x; simp)
  let t : Structure.Embedding A C := markedMap P _ _ Obstruction.inclusion
    (by intro x y; simpa only [Obstruction.leg_inclusion] using
      Obstruction.base_colours h 1 0 x y)
    (by intro x; simp only [Obstruction.leg_inclusion]
        rw [Obstruction.base_marks hP,Obstruction.base_marks hP])
  have ha : (markedModel P).Age A :=
    ⟨actualMarkedEmbedding P _ (Obstruction.base_injective h 0)⟩
  have hb : (markedModel P).Age B :=
    ⟨actualMarkedEmbedding P _ (Obstruction.leg_injective h 0)⟩
  have hc : (markedModel P).Age C :=
    ⟨actualMarkedEmbedding P _ (Obstruction.leg_injective h 1)⟩
  obtain ⟨V,hV,D,⟨e⟩,l,r,heq⟩ := hap (Fin 2) (Fin 3) (Fin 3) A B C ha hb hc s t
  let L := e.comp l
  let R := e.comp r
  have hbase (i : Fin 2) : L.point (Obstruction.inclusion i)=
      R.point (Obstruction.inclusion i) := congrArg e.point (heq i)
  have h0 : L.point 0=R.point 0 := hbase 0
  have h1 : L.point 1=R.point 1 := hbase 1
  have hlb : colour (L.point 0) (L.point 2)=some (some 0,none) :=
    markedEmbedding_colour L 0 2 _ (by simp)
  have hrb : colour (L.point 0) (R.point 2)=some (some 0,none) := by
    rw [h0]
    exact markedEmbedding_colour R 0 2 _ (by simp)
  have hld : colour (L.point 2) (L.point 1)=some (none,some 0) :=
    markedEmbedding_colour L 2 1 _ (by simp)
  have hrd : colour (R.point 2) (L.point 1)=some (none,some 0) := by
    rw [h1]
    exact markedEmbedding_colour R 2 1 _ (by simp)
  have hp0 : P (L.point 2)=h 0 1 := by
    rw [markedEmbedding_mark L]
    simpa only [Obstruction.leg_two,zero_add] using (Obstruction.marks hP 0).2.2
  have hp1 : P (R.point 2)=1+h 0 1 := by
    rw [markedEmbedding_mark R]
    exact (Obstruction.marks hP 1).2.2
  have hDifferent : P (L.point 2)≠P (R.point 2) := by
    rw [hp0,hp1]
    intro hz
    have : (0:Bit)=1 := add_right_cancel (show 0+h 0 1=1+h 0 1 by simpa using hz)
    exact zero_ne_one this
  have hDistinct : L.point 2≠R.point 2 := by
    intro hz
    exact hDifferent (congrArg P hz)
  have howner := Obstruction.owner_forced hlb hrb hld hrd
  have hclone : colour (L.point 2) (R.point 2)=some (some 0,some 0) := by
    apply (colour_some _ _ _).mpr
    refine ⟨hDistinct,?_⟩
    obtain ⟨hu,hv,hp,hq⟩ := (owner_iff _ _).mp howner
    simp [pattern,coordinateColour,hu,hv,hp,hq]
  have hdiag : diagonalSetoid (L.point 2) (R.point 2) := by
    obtain ⟨hu,hv,hp,hq⟩ := (owner_iff _ _).mp howner
    exact (diagonal_iff _ _).mpr ⟨hu,hv,by rw [hp,hq]⟩
  exact hDifferent (hP.same _ _ hdiag)

end CCO.OrbitalCover.Example
