import CCO.ParityHasse.Original.Equivalences
import CCO.PairHomogeneity
import Mathlib.Algebra.Group.Subgroup.Actions
import Mathlib.Algebra.Group.Action.End

/-!
# Actual induced one-sort sources with literal old diversity names

The palette is the finite subtype of OLD colours actually occurring in the
displayed nonempty set. This construction assumes neither homogeneity nor CCO.
The full automorphism group consists of every colour-preserving permutation.
-/

universe u v w
namespace CCO.RealHull.Geometry

open ParityHasse.Original

variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X) (i : ι) (Z : Set (X i))

def InducedAtom := {c : S.Atom i i // ∃ x y : Z, S.colour x.val y.val = some c}

noncomputable instance inducedAtomFintype : Fintype (InducedAtom S i Z) := by
  letI := S.finiteAtom i i
  unfold InducedAtom
  exact Fintype.ofFinite _

noncomputable def inducedColour (x y : Z) : Option (InducedAtom S i Z) :=
  match hc : S.colour x.val y.val with
  | none => none
  | some c => some ⟨c, x, y, hc⟩

theorem inducedColour_projection (x y : Z) :
    (inducedColour S i Z x y).map Subtype.val = S.colour x.val y.val := by
  unfold inducedColour
  split <;> rename_i hc <;> exact hc.symm

theorem inducedColour_some_iff (x y : Z) (c : InducedAtom S i Z) :
    inducedColour S i Z x y = some c ↔ S.colour x.val y.val = some c.val := by
  constructor
  · intro h
    rw [← inducedColour_projection S i Z x y, h]
    rfl
  · intro h
    have hp := inducedColour_projection S i Z x y
    cases hc : inducedColour S i Z x y with
    | none =>
      have hh := hp.trans h
      rw [hc] at hh
      change (none : Option (S.Atom i i)) = some c.val at hh
      cases hh
    | some d =>
      have hh := hp.trans h
      rw [hc] at hh
      change some d.val = some c.val at hh
      have hd : d.val = c.val := Option.some.inj hh
      exact congrArg some (Subtype.ext hd)

theorem inducedColour_none_iff (x y : Z) :
    inducedColour S i Z x y = none ↔ x = y := by
  constructor
  · intro h
    have ho := inducedColour_projection S i Z x y
    rw [h] at ho
    apply Subtype.ext
    have hs := (S.colour_none_iff x.val y.val).mp ho.symm
    simpa only [Sigma.mk.injEq, heq_eq_eq, true_and] using hs
  · rintro rfl
    have hn : S.colour x.val x.val = none := (S.colour_none_iff _ _).mpr rfl
    cases hc : inducedColour S i Z x x with
    | none => rfl
    | some c =>
      have hh := (inducedColour_some_iff S i Z x x c).mp hc
      rw [hn] at hh
      cases hh

theorem inducedColour_eq_iff (x y x' y' : Z) :
    inducedColour S i Z x y = inducedColour S i Z x' y' ↔
      S.colour x.val y.val = S.colour x'.val y'.val := by
  constructor
  · intro h
    exact (inducedColour_projection S i Z x y).symm.trans
      ((congrArg (Option.map Subtype.val) h).trans (inducedColour_projection S i Z x' y'))
  · intro h
    cases hc : inducedColour S i Z x y with
    | none =>
      have hn : S.colour x.val y.val = none := by
        rw [← inducedColour_projection S i Z x y, hc]
        rfl
      have he := (S.colour_none_iff x'.val y'.val).mp (h.symm.trans hn)
      have hxy : x' = y' := Subtype.ext (by
        simpa only [Sigma.mk.injEq, heq_eq_eq, true_and] using he)
      exact ((inducedColour_none_iff S i Z x' y').mpr hxy).symm
    | some c =>
      exact ((inducedColour_some_iff S i Z x' y' c).mpr
        (h.symm.trans ((inducedColour_some_iff S i Z x y c).mp hc))).symm

noncomputable def inducedSource [Nonempty Z] : AtomicSource Unit (fun _ => Z) where
  Atom _ _ := InducedAtom S i Z
  finiteSort := inferInstance
  finiteAtom _ _ := inducedAtomFintype S i Z
  nonemptySort _ := inferInstance
  conv := id
  conv_invol _ := rfl
  symmetricLoop _ := rfl
  colour := inducedColour S i Z
  colour_none_iff := by
    intro j k x y
    cases j; cases k
    simpa only [Sigma.mk.injEq, heq_eq_eq, true_and] using inducedColour_none_iff S i Z x y
  colour_swap := by
    intro j k x y c
    rw [inducedColour_some_iff, inducedColour_some_iff]
    simpa only [id_eq,S.symmetricLoop] using S.colour_swap x.val y.val c.val
  realized := by
    intro j k c
    obtain ⟨x,y,hc⟩ := c.property
    exact ⟨x,y,(inducedColour_some_iff S i Z x y c).mpr hc⟩

/-- The WHOLE induced-language automorphism group; no ambient extension is
required by the definition. -/
def inducedAut : Subgroup (Equiv.Perm Z) where
  carrier := {g | ∀ x y, inducedColour S i Z (g x) (g y) = inducedColour S i Z x y}
  one_mem' := by intro x y; rfl
  mul_mem' := by
    intro a b ha hb x y
    exact (ha (b x) (b y)).trans (hb x y)
  inv_mem' := by
    intro g hg x y
    have hh := hg (g⁻¹ x) (g⁻¹ y)
    simpa using hh.symm

instance inducedAutAction : MulAction (inducedAut S i Z) Z where
  smul g x := g.val x
  one_smul _ := rfl
  mul_smul _ _ _ := rfl

abbrev ClassPoint (E : ColourEq S i) (a : X i) := {x : X i // E a x}

instance classPointNonempty (E : ColourEq S i) (a : X i) : Nonempty (ClassPoint S i E a) :=
  ⟨⟨a,E.val.refl a⟩⟩

noncomputable abbrev classSource (E : ColourEq S i) (a : X i) :=
  letI : Nonempty {x | E a x} := ⟨⟨a,E.val.refl a⟩⟩
  inducedSource S i {x | E a x}

end CCO.RealHull.Geometry
