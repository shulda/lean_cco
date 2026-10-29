import CCO.PairHomogeneity
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.Algebra.Group.Subgroup.Actions

/-! Every automorphism preserves ALL original typed fine colours. The
acting group is not replaced by that of an induced one-sort reduct. -/
universe u v w t
namespace CCO.TerminalPowers
variable {ι : Type u} {X : ι → Type v} (S : AtomicSource.{u,v,w} ι X)

def fullAutGroup : Subgroup (∀ i, Equiv.Perm (X i)) where
  carrier := {e | ∀ (i j : ι) (x : X i) (y : X j),
    S.colour (e i x) (e j y) = S.colour x y}
  one_mem' := fun _ _ _ _ => rfl
  mul_mem' := by
    intro e f he hf i j x y
    exact (he i j (f i x) (f j y)).trans (hf i j x y)
  inv_mem' := by
    intro e he i j x y
    change S.colour ((e i).symm x) ((e j).symm y) = S.colour x y
    have h := he i j ((e i).symm x) ((e j).symm y)
    simpa only [Equiv.apply_symm_apply] using h.symm

abbrev FullAut := ↥(fullAutGroup S)

instance fullAutAction (i : ι) : MulAction (FullAut S) (X i) where
  smul g x := g.val i x
  one_smul _ := rfl
  mul_smul _ _ _ := rfl

theorem fullAut_colour (g : FullAut S) (i j : ι) (x : X i) (y : X j) :
    S.colour (g • x) (g • y) = S.colour x y := g.property i j x y

variable {G : Type t} [Group G] [∀ i, MulAction G (X i)]

def motionAut (H : HomogeneousSource S G) (g : G) : FullAut S :=
  ⟨fun _i => MulAction.toPerm g,fun _i _j x y => S.colourInvariant_of_homogeneous H g x y⟩

theorem full_homogeneous (H : HomogeneousSource S G) : HomogeneousSource S (FullAut S) where
  preserves_sort := by intro g p; rfl
  preserves_colours := by
    rintro g ⟨i,x⟩ ⟨j,y⟩
    exact congrArg (fun c => (⟨i,j,c⟩ : Σ i, Σ j, Option (S.Atom i j)))
      (fullAut_colour S g i j x y)
  extends_finite_diagram := by
    intro V _ f h hc
    obtain ⟨g,hg⟩ := H.extends_finite_diagram f h hc
    exact ⟨motionAut S H g,hg⟩

end CCO.TerminalPowers
