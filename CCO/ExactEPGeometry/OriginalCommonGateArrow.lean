import CCO.ExactEPGeometry.CurrentBridgeOldGateBound

/-!
# B062 C51–C55: actual ORIGINAL gate correspondence for a current bridge

The pinned source has ONE original homogeneous symmetric carrier. For
two current named types with the SAME original parent, the preceding
actual current Arrow / displayed-middle TP / stable-power lemmas
already prove the old D;Dᵒᵖ <= G_p, where G_p is the canonical
largest ORIGINAL full RAW-exact lift of the current gate.

This file explicitly performs ONLY the justified original-sort equality
transport, then uses original symmetry Dᵒᵖ=D to construct the genuine
whole full-exact Arrow C=G_p;D over the ORIGINAL carrier. It records the
same real old/current D trace; the final C|p,q = R assertion requires
one more actual (TP) application and remains separately open here.

No arbitrary mixed-original commutation, quotient SAP, automorphism
section, implicit equality-coded diversity edges or new provider.
-/

universe u v w t

namespace CCO.ExactEPGeometry

open APCharacter.Towers
open RigidGroupoid.Geometry

noncomputable section

variable {ι : Type u} {X : ι → Type v}

/-- An original nonempty exact cross-sort relation with an ACTUAL
equality of its original endpoint sorts can be transported to the
genuinely SAME original carrier. The source's old-square bound,
which is initially written as D;Dᵒᵖ, then yields a true full-exact
self Arrow at the ORIGINAL gate. This equality-of-sorts premise
does NOT say that any two independently named current sorts agree. -/
theorem original_full_arrow_of_same_parent_square
    (S : AtomicSource.{u,v,w} ι X)
    {G : Type t} [Group G] [∀ i : ι, MulAction G (X i)]
    (H : HomogeneousSource S G)
    (cco : SemanticCCO.{u,v,max u v,w} S)
    {i j : ι} (hSame : i = j) (K : Kernel S i)
    (D : RawExact.NonemptyExact S i j)
    (hSquare : ∀ a b : X i,
      TRel.comp (RawExact.evaluate S D.words)
        (TRel.converse (RawExact.evaluate S D.words)) a b →
          K.rel a b) :
    ∃ E : RawExact.NonemptyExact S i i,
      ∃ C : Arrow S K K,
        C.rel = TRel.comp K.rel (RawExact.evaluate S E.words) ∧
        (∀ a : X i, ∀ b : X j,
          RawExact.evaluate S E.words a (hSame.symm ▸ b) ↔
            RawExact.evaluate S D.words a b) := by
  cases hSame
  let R := RawExact.evaluate S D.words
  have hFull : FullExact S R := ⟨D,rfl⟩
  have hSym : TRel.converse R = R :=
    hFull.same_sort_converse S H
  have hOldSquare : ∀ a b : X i,
      TRel.comp R R a b → K.rel a b := by
    intro a b hab
    apply hSquare a b
    rw [hSym]
    exact hab
  let C : Arrow S K K :=
    original_saturated_exact_arrow S H cco K R hFull hOldSquare
  exact ⟨D,C,rfl,fun _ _ => Iff.rfl⟩

/-- The L_p(K_p) gate as a REAL original Kernel, not the entire original
lattice of possibly NONEXACT invariant equivalences. -/
def original_largest_gate_kernel
    (A B : CurrentSource.{u,v,w,t})
    (P : UnaryReduct A.source B.source)
    (transport : ExactTraceTransport A.source B.source P)
    (tp : ExactTraceProduct A.source B.source P)
    (p : B.Sorts) (K : Kernel B.source p) :
    Kernel A.source (P.parent p) := by
  let L := PrefixExactLargestLift.largest A B P transport tp p
    (current_kernel_exact_eq B K)
  exact ⟨L.val.val,L.property⟩

/-- Source C51–C55 main real application up to the ORIGINAL arrow:
for one genuine current full RAW-exact Arrow between types sharing
their actual original parent, construct the OLD full-exact
correspondence C=G_p;D and an old same-parent exact D whose literal
p,q trace is the entire current R. The old D-square gate bound and
exact-source arrow are actually PROVED by previously checked
C22/C28/E1–E3 source providers; neither is postulated here.

The next separate obligation is to prove C itself has the same current
trace R using (TP), K_p;R=R and true L_p(K_p)|p²=K_p. -/
theorem current_arrow_has_original_correspondence
    (A B : CurrentSource.{u,v,w,t})
    (P : UnaryReduct A.source B.source)
    (transport : ExactTraceTransport A.source B.source P)
    (tp : ExactTraceProduct A.source B.source P)
    {p q : B.Sorts}
    (hSame : P.parent p = P.parent q)
    (Kp : Kernel B.source p) (Kq : Kernel B.source q)
    (R : Arrow B.source Kp Kq) :
    let K := original_largest_gate_kernel A B P transport tp p Kp
    ∃ E : RawExact.NonemptyExact A.source (P.parent p) (P.parent p),
      ∃ C : Arrow A.source K K,
        (∀ x : B.Point p, ∀ y : B.Point q,
          R.rel x y ↔ RawExact.evaluate A.source E.words
            (P.point p x) (hSame.symm ▸ P.point q y)) ∧
        C.rel = TRel.comp K.rel (RawExact.evaluate A.source E.words) := by
  dsimp only
  obtain ⟨D,hBridge,hBound⟩ :=
    current_arrow_old_square_below_largest A B P transport tp Kp Kq R
  let K := original_largest_gate_kernel A B P transport tp p Kp
  have hOldSquare : ∀ a b : A.Point (P.parent p),
      TRel.comp (RawExact.evaluate A.source D.words)
        (TRel.converse (RawExact.evaluate A.source D.words)) a b →
          K.rel a b := hBound
  obtain ⟨E,C,hC,hEq⟩ :=
    original_full_arrow_of_same_parent_square
      A.source A.homogeneous A.cco hSame K D hOldSquare
  refine ⟨E,C,?_,hC⟩
  intro x y
  exact (hBridge x y).trans
    (hEq (P.point p x) (P.point q y)).symm

end
end CCO.ExactEPGeometry
