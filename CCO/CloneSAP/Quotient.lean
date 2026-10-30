import CCO.CloneSAP.Owner
import Mathlib.Data.Quot

universe u v w
namespace CCO.CloneSAP
variable {ι : Type u} {X : ι → Type v} (S : AtomicSource ι X)
open TerminalPowers

/-- The actual definable K-class relation on a current original sort. -/
def kernelSetoid (i : ι) : Setoid (Carrier X i) where
  r x y := x.1 = y.1
  iseqv := ⟨fun _ => rfl,Eq.symm,Eq.trans⟩

/-- C25: the real K quotient is canonically the original owner sort. -/
def quotientOwnerEquiv (i : ι) : Quotient (kernelSetoid (X := X) i) ≃ X i where
  toFun := Quotient.lift Prod.fst (fun _ _ h => h)
  invFun x := Quotient.mk _ (x,0)
  left_inv q := Quotient.inductionOn q (fun x => Quotient.sound rfl)
  right_inv _ := rfl

@[simp] theorem quotientOwner_mk {i : ι} (x : Carrier X i) :
    quotientOwnerEquiv (X := X) i (Quotient.mk _ x) = x.1 := rfl

/-- All old named binary relations, including mixed sorts, are retained
literally under the canonical owner quotient. -/
theorem quotient_colour {i j : ι} (x : Carrier X i) (y : Carrier X j) :
    S.colour (quotientOwnerEquiv i (Quotient.mk _ x))
      (quotientOwnerEquiv j (Quotient.mk _ y)) =
      ((source S).colour x y).bind (eraseAtom S) := (colour_erase S x y).symm

/-- Every whole clone automorphism preserves owner equality in BOTH directions. -/
theorem aut_kernel (g : FullAut (source S)) {i : ι} (x y : Carrier X i) :
    (g.val i x).1 = (g.val i y).1 ↔ x.1 = y.1 := by
  have hc : taggedColour (source S) ⟨i,g.val i x⟩ ⟨i,g.val i y⟩ =
      taggedColour (source S) ⟨i,x⟩ ⟨i,y⟩ :=
    congrArg (fun c => (⟨i,i,c⟩ : Σ i, Σ j, Option ((source S).Atom i j))) (g.property i i x y)
  have hh := tagged_diagonal S (tagged_owner_eq S hc)
  simpa only [owner,Sigma.mk.injEq,heq_eq_eq,true_and] using hh

/-- Owner projection is independent of a preferred clone. Index0 only writes
one representative of the quotient-induced map; the next theorem erases it. -/
def descendFun (g : FullAut (source S)) (i : ι) (x : X i) : X i := (g.val i (x,0)).1

theorem descendFun_apply (g : FullAut (source S)) {i : ι} (x : Carrier X i) :
    descendFun S g i x.1 = (g.val i x).1 := (aut_kernel S g _ _).mpr rfl

/-- C05: every actual whole clone automorphism projects to an actual whole
original automorphism, without a caller-supplied quotient action or section. -/
noncomputable def descendAut (g : FullAut (source S)) : FullAut S := by
  let e : ∀ i, Equiv.Perm (X i) := fun i => {
    toFun := descendFun S g i
    invFun := descendFun S g⁻¹ i
    left_inv x := by
      have he := descendFun_apply S g⁻¹ (g.val i (x,0))
      change descendFun S g⁻¹ i ((g.val i) (x,0)).1 = x
      calc
        _ = (g⁻¹.val i (g.val i (x,0))).1 := he
        _ = x := by change ((g.val i).symm (g.val i (x,0))).1 = x; simp
    right_inv x := by
      have he := descendFun_apply S g (g⁻¹.val i (x,0))
      change descendFun S g i ((g⁻¹.val i) (x,0)).1 = x
      calc
        _ = (g.val i (g⁻¹.val i (x,0))).1 := he
        _ = x := by change ((g.val i) ((g.val i).symm (x,0))).1 = x; simp }
  refine ⟨e,?_⟩
  intro i j x y
  have he := congrArg (fun c => c.bind (eraseAtom S)) (g.property i j (x,0) (y,0))
  change S.colour (g.val i (x,0)).1 (g.val j (y,0)).1 = S.colour x y
  simpa only [colour_erase] using he

@[simp] theorem descendAut_apply (g : FullAut (source S)) {i : ι} (x : Carrier X i) :
    (descendAut S g).val i x.1 = (g.val i x).1 := by
  change descendFun S g i x.1 = (g.val i x).1
  exact descendFun_apply S g x

end CCO.CloneSAP
