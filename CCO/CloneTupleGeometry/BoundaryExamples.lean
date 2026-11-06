import CCO.CloneTupleGeometry.OwnerTerminalGeometry
import CCO.CloneTupleGeometry.StrongClone
import CCO.CloneSAP.ExactKernel

/-! B060 N08/C53--C57 boundaries. The first example is an ACTUAL infinite
homogeneous two-coloured source, not a conditional graph provider. The
singleton-owner marking is an actual arbitrary clone-saturated label, not
a legal safe-character marking. Existing finite window computations remain
diagnostics only: they do not certify infinite SAP/CCO, the marked Fraisse
construction, Ramsey/HN/EPPA or a Lean proof of those unbounded statements. -/

set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace CCO.CloneTupleGeometry.Boundaries
open TerminalPowers ParityHasse.Original
noncomputable section

namespace BareCoordinates

/-- The homogeneous two-point owner source, with one literal diversity
colour. Its pure clone has infinitely many points in each of two cliques. -/
def ownerSource : AtomicSource Unit (fun _ => Bool) where
  Atom _ _ := Unit
  finiteSort := inferInstance
  finiteAtom _ _ := inferInstance
  nonemptySort _ := inferInstance
  conv _ := ()
  conv_invol := by intros; rfl
  symmetricLoop := by intros; rfl
  colour x y := if x = y then none else some ()
  colour_none_iff := by
    intro i j x y
    cases i
    cases j
    simp only [ite_eq_left_iff,Option.some_ne_none,imp_false,Sigma.mk.injEq,heq_eq_eq,true_and]
    exact not_not
  colour_swap := by
    intro i j x y a
    cases a
    simp only [eq_comm]
  realized := by
    intro i j a
    exact ⟨false,true,rfl⟩

/-- Every finite full partial isomorphism extends by one permutation of
the two old owners, including empty and repeated-point diagrams. -/
theorem owner_homogeneous : HomogeneousSource ownerSource (Equiv.Perm Bool) where
  preserves_sort := by
    intro g p
    rcases p with ⟨i,x⟩
    rfl
  preserves_colours := by
    intro g p q
    rcases p with ⟨i,x⟩
    rcases q with ⟨j,y⟩
    cases i
    cases j
    change (⟨(),(),if g x = g y then none else some ()⟩ :
      Σ i : Unit, Σ j : Unit, Option (ownerSource.Atom i j)) =
      ⟨(),(),if x = y then none else some ()⟩
    simp only [g.injective.eq_iff]
  extends_finite_diagram := by
    intro V _ f h hc
    have heq (a b : V) : (f a).2 = (f b).2 ↔ (h a).2 = (h b).2 := by
      have he := CloneSAP.tagged_diagonal ownerSource (hc a b)
      have hf : f a = f b ↔ (f a).2 = (f b).2 :=
        ⟨fun h => congrArg (fun p : Sigma (fun _ : Unit => Bool) => p.2) h,
          fun h => Sigma.ext (Unit.ext _ _) (heq_of_eq h)⟩
      have hh : h a = h b ↔ (h a).2 = (h b).2 :=
        ⟨fun h => congrArg (fun p : Sigma (fun _ : Unit => Bool) => p.2) h,
          fun h => Sigma.ext (Unit.ext _ _) (heq_of_eq h)⟩
      exact hf.symm.trans (he.trans hh)
    obtain ⟨g,hg⟩ := CloneSAP.exists_permutation_of_eq_pattern
      (fun a => (f a).2) (fun a => (h a).2) heq
    refine ⟨g,fun a => ?_⟩
    exact Sigma.ext (Unit.ext _ _) (heq_of_eq (hg a))

abbrev source := CloneSAP.source ownerSource
abbrev Point := Bool × ℕ

theorem homogeneous : HomogeneousSource source (FullAut source) :=
  CloneSAP.homogeneous ownerSource owner_homogeneous

instance points_infinite : Infinite Point := inferInstance

def red : source.Atom () () := Sum.inr ⟨rfl⟩
def blue : source.Atom () () := Sum.inl ()

def x : Point := (false,0)
def y : Point := (false,1)
def z : Point := (true,0)

theorem red_pair : source.colour x y = some red :=
  (CloneSAP.source_clone_iff ownerSource x y).mpr ⟨rfl,Nat.zero_ne_one⟩

theorem blue_pair : source.colour x z = some blue :=
  (CloneSAP.colour_old_iff ownerSource x z ()).mpr rfl

/-- The CHOSEN equality/Top reduct has literally the same pair data,
while fine colours differ. This does not assert a failure for the family
of ALL FULL MI coordinates (the example also has a same-clique kernel).
Top is the constant True observation and adds no information. -/
theorem same_bare_code_different_fine_colour :
    decide (x = y) = decide (x = z) ∧
      source.colour (i := ()) (j := ()) x y ≠ source.colour (i := ()) (j := ()) x z := by
  constructor
  · decide
  · rw [red_pair,blue_pair]
    simp [red,blue]

/-- C53: even an arbitrary predicate of the COMPLETE equality/Top pair
code cannot recover RED in this concrete infinite homogeneous source. -/
theorem bare_code_does_not_define_red :
    ¬∃ p : Bool → Prop, ∀ a b : Point,
      source.colour a b = some red ↔ p (decide (a = b)) := by
  rintro ⟨p,hp⟩
  have hred := (hp x y).mp red_pair
  have hcode := same_bare_code_different_fine_colour.1
  have hother : source.colour x z = some red := (hp x z).mpr (hcode ▸ hred)
  rw [blue_pair] at hother
  simp [red,blue] at hother

end BareCoordinates

section SingletonOwnerLabel
variable {ι : Type u} {X : ι → Type v} (S : AtomicSource.{u,v,w} ι X)
variable {i : ι} (q : X i)

/-- Label one actual owner and pull the predicate back to its entire
unchanged infinite clone fibre. -/
def singletonOwnerLabel (x : CloneSAP.Carrier X i) : Prop := x.1 = q

theorem singleton_label_fibre_constant (r : X i) (n m : ℕ) :
    singletonOwnerLabel q (r,n) ↔ singletonOwnerLabel q (r,m) := Iff.rfl

/-- Invariance under the ACTUAL independent fibre-permutation source
automorphisms, with the original owner automorphism equal to identity. -/
theorem singleton_label_fibre_aut_invariant
    (σ : ∀ j : ι, X j → Equiv.Perm ℕ) (x : CloneSAP.Carrier X i) :
    singletonOwnerLabel q (CloneSAP.liftEquiv S (1 : FullAut S) σ i x) ↔
      singletonOwnerLabel q x := Iff.rfl

def labelledOwnerEquiv : {r : X i // r = q} ≃ Unit where
  toFun _ := ()
  invFun _ := ⟨q,rfl⟩
  left_inv r := Subtype.ext r.property.symm
  right_inv _ := rfl

def labelledCloneEquiv : {x : CloneSAP.Carrier X i // singletonOwnerLabel q x} ≃ ℕ where
  toFun x := x.val.2
  invFun n := ⟨(q,n),rfl⟩
  left_inv x := Subtype.ext (Prod.ext x.property.symm rfl)
  right_inv _ := rfl

/-- C55: the marked owner type has exactly ONE owner although every clone
in that owner's fibre is marked and the marked clone carrier is infinite.
Thus clone saturation alone cannot replace the genuine character proof. -/
theorem arbitrary_clone_saturated_label_single_owner [Infinite (X i)] :
    Infinite (X i) ∧
    Nat.card {r : X i // r = q} = 1 ∧
    Infinite {x : CloneSAP.Carrier X i // singletonOwnerLabel q x} ∧
    (∀ r : X i, ∀ n m : ℕ, singletonOwnerLabel q (r,n) ↔ singletonOwnerLabel q (r,m)) := by
  refine ⟨inferInstance,?_,?_,singleton_label_fibre_constant q⟩
  · exact (Nat.card_congr (labelledOwnerEquiv q)).trans (by simp)
  · exact Infinite.of_injective (labelledCloneEquiv q).symm (labelledCloneEquiv q).symm.injective

end SingletonOwnerLabel

section FullStrongBoundary
variable {ι : Type u} {X : ι → Type v} (S : AtomicSource.{u,v,w} ι X)

/-- C54 retains the real FULL diagonal output and the separate genuine
STRONG singleton palette equation in the same concrete source. -/
theorem full_clone_square_and_strong_square (i : ι) :
    RawWord.relation (CloneSAP.source S) (CloneSAP.kernelWord S i) =
      (CloneSAP.kernelSetoid (X := X) i).r ∧
    (CloneSAP.source S).product
      ({Sum.inr ⟨rfl⟩} : (CloneSAP.source S).Menu i i)
      ({Sum.inr ⟨rfl⟩} : (CloneSAP.source S).Menu i i) = {Sum.inr ⟨rfl⟩} ∧
    ∀ q : X i, RawWord.relation (CloneSAP.source S) (CloneSAP.kernelWord S i) (q,0) (q,0) ∧
      ¬(CloneSAP.source S).atomRel (Sum.inr ⟨rfl⟩) (q,0) (q,0) := by
  refine ⟨CloneSAP.kernelWord_relation S i,pure_clone_strong_square S i,?_⟩
  intro q
  constructor
  · rw [CloneSAP.kernelWord_relation]
  · intro h
    exact ((CloneSAP.source_clone_iff S (q,0) (q,0)).mp h).2 rfl
end FullStrongBoundary

/-- C57: every infinite owner stage has an actual nonempty fixed finite
proper-MI coordinate family; no empty tuple can collapse its owners. -/
theorem no_empty_owner_coordinate_family (B : OwnerStage.{u,v,w}) (i : B.Sorts) :
    Finite (FullCloneProperMI B.source i) ∧ Nonempty (FullCloneProperMI B.source i) :=
  ⟨inferInstance,B.clone_MI_nonempty i⟩

end
end CCO.CloneTupleGeometry.Boundaries
