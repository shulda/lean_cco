import CCO.AclOwners.CorrespondenceGeometry
import CCO.RawExact.FineColoursSource

/-! Complete original spoke colours force the original fine cross
colour across two complementary exact directions. No safe amalgamation
or quotient tuple realization is used in this algebraic readout. -/
universe v w t
namespace CCO.AclOwners
open ParityHasse.Original RealHull.Geometry RealClosure.Bounds RawExact
variable {M : Type v} (S : AtomicSource.{0,v,w} Unit (fun _ => M))
variable {G : Type t} [Group G] [MulAction G M] (H : HomogeneousSource S G)
variable (cco : SemanticCCO.{0,v,0,w} S)
include H cco

theorem fine_colour_of_two_anchor_spokes
    (E F : ColourEq S ()) (hE : ExactCRT.IsExactEq S (i := ()) E.val)
    (hF : ExactCRT.IsExactEq S (i := ()) F.val) (hEF : E ⊓ F = ⊥)
    (x y u v x' y' u' v' : M) (hxu : E x u) (hyv : F y v)
    (hxu' : col S x' u' = col S x u) (huy' : col S u' y' = col S u y)
    (hxv' : col S x' v' = col S x v) (hvy' : col S v' y' = col S v y) :
    col S x' y' = col S x y := by
  obtain ⟨BE,hBE⟩ := hE
  obtain ⟨BF,hBF⟩ := hF
  have hsE : saturate E.val.r (S.rawAtomRel (col S x y)) E.val.r x' y' := by
    obtain ⟨g,hgu,hgy⟩ := S.pair_homogeneous_of_homogeneous H u u' y y' huy'.symm
    have hEu : E x' u' := (E.property x u x' u' hxu'.symm).mp hxu
    have hEx : E u' (g • x) := by
      have hi := (class_group_invariant S () H E g u x).mpr (E.val.symm hxu)
      rwa [hgu] at hi
    have hc : col S (g • x) y' = col S x y := by
      simpa only [hgy] using col_invariant S H g x y
    exact ⟨y',⟨g • x,E.val.trans hEu hEx,hc⟩,E.val.refl y'⟩
  have hsF : saturate F.val.r (S.rawAtomRel (col S x y)) F.val.r x' y' := by
    obtain ⟨g,hgx,hgv⟩ := S.pair_homogeneous_of_homogeneous H x x' v v' hxv'.symm
    have hFv : F v' y' := (F.property v y v' y' hvy'.symm).mp (F.val.symm hyv)
    have hFy : F (g • y) v' := by
      have hi := (class_group_invariant S () H F g y v).mpr hyv
      rwa [hgv] at hi
    have hc : col S x' (g • y) = col S x y := by
      simpa only [hgx] using col_invariant S H g x y
    exact ⟨g • y,⟨x',F.val.refl x',hc⟩,F.val.trans hFy hFv⟩
  let B : Bool → NonemptyExact S () () := fun b => if b then BF else BE
  have hrepr : ∀ b : Bool, evaluate S (B b).words = (if b then F else E).val.r := by
    intro b
    cases b <;> simp only [B,Bool.false_eq_true,if_false,if_true] <;> assumption
  have hEquiv : ∀ b : Bool, RawSymmetric.EquivRel (evaluate S (B b).words) := by
    intro b
    rw [hrepr]
    exact ⟨(if b then F else E).val.refl,
      fun _ _ h => (if b then F else E).val.symm h,
      fun _ _ _ h k => (if b then F else E).val.trans h k⟩
  have hmeet : familyMeet (fun b => evaluate S (B b).words) = Eq := by
    funext a b
    apply propext
    constructor
    · intro h
      have hi : (E ⊓ F) a b := by
        constructor
        · have hh := h false
          change evaluate S (B false).words a b at hh
          simpa only [hrepr,Bool.false_eq_true,ite_false] using hh
        · have hh := h true
          change evaluate S (B true).words a b at hh
          simpa only [hrepr,ite_true] using hh
      rwa [hEF] at hi
    · rintro rfl k
      simpa only [hrepr] using (if k then F else E).val.refl a
  have hall : ∀ b, saturate (evaluate S (B b).words)
      (S.rawAtomRel (col S x y)) (evaluate S (B b).words) x' y' := by
    intro b
    rw [hrepr]
    cases b
    · exact hsE
    · exact hsF
  have hread := fine_colour_reconstruction_of_CCO S H
    (semanticCCO_change_universe S cco) B hEquiv (col S x y)
  have hfine := (Iff.of_eq (congrFun (congrFun hread x') y')).mp hall
  rw [hmeet] at hfine
  rcases hfine with ⟨b,⟨a,ha,hab⟩,hb⟩
  cases ha
  cases hb
  exact hab

end CCO.AclOwners
