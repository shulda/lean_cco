import CCO.ExactEPGeometry.OriginalCoherentProjectedGateExact

/-!
# B062 C83: all-parent exact descent for EVERY genuine full reached Arrow

This source module extends the proved original-E coherent typed
current word intertwining (C82) from projected gate identities to the
entire actual complete groupoid of current RAW-exact Arrow objects.

Every actual full current Arrow R:Kp -> Kq is E-bisaturated on its
true displayed endpoints whenever the two genuine locally exact
E-kernels e_p,e_q lie below Kp,Kq. This is derived from the WHOLE
source and target gate Arrow equations, not from an assumed quotient
action, independent mixed descent, or SAP. The previously proved
coherent current exact word descent therefore gives the FULL exact
image relation on the already constructed ALL-PARENT simultaneous
E-quotient CurrentSource.

C83's further one-representative-per-occupancy selection is NOT
asserted here: selected-sort restriction can erase intermediate
RAW-word sorts, and needs the separate actual quotient-prefix tower
transport required in the frozen proof.
-/

universe u v w t

namespace CCO.ExactEPGeometry

open APCharacter.Towers
open RigidGroupoid.Geometry

noncomputable section

/-- Actual C83 ALL-PARENT strength: every genuinely represented full
current Arrow with gates Kp,Kq containing their SAME-original-E
local kernels has a FULL RAW-exact image on the true all-parent
simultaneous quotient source. Both source/target saturations and
all typed word-TI certificates are discharged, not assumptions. -/
theorem original_coherent_allparent_arrow_image_exact
    (A B : CurrentSource.{u,v,w,t})
    (P : UnaryReduct A.source B.source)
    (transport : ExactTraceTransport A.source B.source P)
    (tp : ExactTraceProduct A.source B.source P)
    (base : A.Sorts) (hOne : ∀ i : A.Sorts, base = i)
    (E : ExactEq A.source base)
    {i j : B.Sorts} (Kp : Kernel B.source i)
    (Kq : Kernel B.source j)
    (hEp : originalExactOnCurrentSort
      A B P transport base hOne E i ≤ current_kernel_exact_eq B Kp)
    (hEq : originalExactOnCurrentSort
      A B P transport base hOne E j ≤ current_kernel_exact_eq B Kq)
    (R : Arrow B.source Kp Kq) :
    let Q := originalExactAllCurrentQuotientCurrentSource A B P
      transport base hOne E
    FullExact Q.source
      (Quotient.image
        (fun x : B.Point i => (Quotient.mk'' x : Q.Point i))
        (fun y : B.Point j => (Quotient.mk'' y : Q.Point j))
        R.rel) := by
  dsimp only
  let W := originalExactCurrentKernelWords
    A B P transport base hOne E
  let ep := originalExactOnCurrentSort
    A B P transport base hOne E i
  let eq := originalExactOnCurrentSort
    A B P transport base hOne E j
  let Ep : Kernel B.source i := ⟨ep.val.val,ep.property⟩
  let Eq : Kernel B.source j := ⟨eq.val.val,eq.property⟩
  have hWep : RawExact.evaluate B.source (W i).words = Ep.rel :=
    originalExactCurrentKernelWords_relation
      A B P transport base hOne E i
  have hWeq : RawExact.evaluate B.source (W j).words = Eq.rel :=
    originalExactCurrentKernelWords_relation
      A B P transport base hOne E j
  have hEpK : Ep.setoid ≤ Kp.setoid := hEp
  have hEqK : Eq.setoid ≤ Kq.setoid := hEq
  have hLeft : TRel.comp Ep.rel R.rel = R.rel := by
    calc
      TRel.comp Ep.rel R.rel =
          TRel.comp Ep.rel (TRel.comp Kp.rel R.rel) :=
        (congrArg (fun T => TRel.comp Ep.rel T) R.left).symm
      _ = TRel.comp (TRel.comp Ep.rel Kp.rel) R.rel := by
        rw [← TRel.comp_assoc]
      _ = TRel.comp Kp.rel R.rel := by rw [Ep.left_absorb hEpK]
      _ = R.rel := R.left
  have hRight : TRel.comp R.rel Eq.rel = R.rel := by
    calc
      TRel.comp R.rel Eq.rel =
          TRel.comp (TRel.comp R.rel Kq.rel) Eq.rel :=
        (congrArg (fun T => TRel.comp T Eq.rel) R.right).symm
      _ = TRel.comp R.rel (TRel.comp Kq.rel Eq.rel) :=
        TRel.comp_assoc R.rel Kq.rel Eq.rel
      _ = TRel.comp R.rel Kq.rel := by rw [Eq.right_absorb hEqK]
      _ = R.rel := R.right
  have hSat : RawExact.saturate
      (RawExact.evaluate B.source (W i).words) R.rel
      (RawExact.evaluate B.source (W j).words) = R.rel := by
    rw [hWep,hWeq]
    change TRel.comp (TRel.comp Ep.rel R.rel) Eq.rel = R.rel
    rw [hLeft,hRight]
  obtain ⟨D,hD⟩ := R.exact
  have hSatD : RawExact.saturate
      (RawExact.evaluate B.source (W i).words)
      (RawExact.evaluate B.source D.words)
      (RawExact.evaluate B.source (W j).words) =
        RawExact.evaluate B.source D.words := by
    simpa only [hD] using hSat
  obtain ⟨F,hF⟩ := original_coherent_current_exact_descent
    A B P transport tp base hOne E D hSatD
  refine ⟨F,?_⟩
  change RawExact.evaluate
      (CCO.ExactCRT.CanonicalTyped.source B.source B.homogeneous
        (originalExactCurrentKernelFamily A B P transport base hOne E)
        (originalExactCurrentKernelWords A B P transport base hOne E)
        (originalExactCurrentKernelWords_relation
          A B P transport base hOne E)) F.words =
    CCO.ExactCRT.quotientRelation
      (CCO.ExactCRT.CanonicalTyped.projection
        (originalExactCurrentKernelFamily A B P transport base hOne E) i)
      (CCO.ExactCRT.CanonicalTyped.projection
        (originalExactCurrentKernelFamily A B P transport base hOne E) j)
      R.rel
  rw [← hD]
  exact hF

/-- Real C83 source application: on the ENTIRE FULL reached
groupoid of the actual source phase, every current full Arrow
descends EXACTLY on the previously constructed all-parent quotient
source, using the already proved E_b<=K_b for ALL reached b.
The displayed current endpoints need not be E-occupied together:
this is every full groupoid Hom, not just I_bc generators. -/
theorem original_retained_full_reached_arrow_exact_allparent
    (A B : CurrentSource.{u,v,w,t})
    (P : UnaryReduct A.source B.source)
    (transport : ExactTraceTransport A.source B.source P)
    (tp : ExactTraceProduct A.source B.source P)
    (hOne : ∀ i j : A.Sorts, i = j)
    {r : B.Sorts} (Kroot : Kernel B.source r)
    (E : ExactEq A.source (P.parent r))
    (hE : E ≤ PrefixExactLargestLift.largest A B P transport tp r
      (current_kernel_exact_eq B Kroot))
    (b c : Reached B.source Kroot)
    (R : Arrow B.source
      (Reached.kernel B.homogeneous
        (exactCalculus_of_homogeneous_CCO
          B.source B.homogeneous B.cco) b)
      (Reached.kernel B.homogeneous
        (exactCalculus_of_homogeneous_CCO
          B.source B.homogeneous B.cco) c)) :
    let Q := originalExactAllCurrentQuotientCurrentSource A B P
      transport (P.parent r) (fun i => hOne (P.parent r) i) E
    FullExact Q.source
      (Quotient.image
        (fun x : B.Point b.val => (Quotient.mk'' x : Q.Point b.val))
        (fun y : B.Point c.val => (Quotient.mk'' y : Q.Point c.val))
        R.rel) := by
  dsimp only
  exact original_coherent_allparent_arrow_image_exact
    A B P transport tp (P.parent r)
    (fun i => hOne (P.parent r) i) E
    (Reached.kernel B.homogeneous
      (exactCalculus_of_homogeneous_CCO
        B.source B.homogeneous B.cco) b)
    (Reached.kernel B.homogeneous
      (exactCalculus_of_homogeneous_CCO
        B.source B.homogeneous B.cco) c)
    (original_retained_current_E_below_full_gate
      A B P transport tp hOne Kroot E hE b)
    (original_retained_current_E_below_full_gate
      A B P transport tp hOne Kroot E hE c)
    R

end
end CCO.ExactEPGeometry
