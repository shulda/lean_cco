import CCO.RigidGroupoid.Geometry.Bridge
import CCO.RawSource

/-!
# B062 C51–C54: an actual ORIGINAL full exact quotient correspondence

This is the algebraic part of the source's old-bridge saturation step.
The original source is a symmetric homogeneous named sort, its genuine
RAW composition is equality inclusive, and every exact represented
relation is invariant. For an exact old gate K and a real old exact
relation D with D;D contained in K, put C=K;D.

Original same-sort invariant relations commute, C is FULL exact,
C;K=K;C=C, C is symmetric, and C;C=K. Thus C is an actual
RigidGroupoid.Geometry.Arrow K K, a WHOLE quotient correspondence,
not a single-valued map on original points.

The inequality D;D <= K is NOT treated as automatically available;
in the source it must be obtained from a genuine CURRENT full bridge,
the two-way exact trace lift, the fixed-middle-sort (TP), and the
canonical largest original exact gate. That source application remains
a separate C51–C58 obligation; no quotient SAP or group section is added.
-/

universe u v w t

namespace CCO.ExactEPGeometry

open RigidGroupoid.Geometry

noncomputable section

variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)
variable {G : Type t} [Group G] [∀ i : ι, MulAction G (X i)]
variable (H : HomogeneousSource S G)
variable (cco : SemanticCCO.{u,v,max u v,w} S)

/-- C51–C54 ORIGINAL saturated exact gate correspondence. In the
one-sort symmetric source, the positive second power of D is below
the full old gate K. The conclusion is a genuine FULL EXACT GROUPoid
arrow K -> K, not a function on actual points or a quotient section.
The source-specific bridge/TP argument must supply hSquare. -/
noncomputable def original_saturated_exact_arrow
    {i : ι} (K : Kernel S i)
    (D : TRel X i i) (hD : FullExact S D)
    (hSquare : ∀ x y, TRel.comp D D x y → K.rel x y) :
    Arrow S K K := by
  have hKInv : TRel.Invariant (G := G) K.rel :=
    K.exact.invariant S H
  have hDInv : TRel.Invariant (G := G) D :=
    hD.invariant S H
  have hComm : TRel.comp K.rel D = TRel.comp D K.rel := by
    exact S.same_sort_commute_of_homogeneous H K.rel D hKInv hDInv
  have hDSym : TRel.converse D = D :=
    hD.same_sort_converse S H
  have hCExact : FullExact S (TRel.comp K.rel D) :=
    (exactCalculus_of_homogeneous_CCO S H cco).comp K.exact hD
  have hCSym : TRel.converse (TRel.comp K.rel D) =
      TRel.comp K.rel D :=
    hCExact.same_sort_converse S H
  have hLeft : TRel.comp K.rel (TRel.comp K.rel D) =
      TRel.comp K.rel D := by
    calc
      _ = TRel.comp (TRel.comp K.rel K.rel) D :=
        (TRel.comp_assoc _ _ _).symm
      _ = _ := by rw [K.comp_self]
  have hRight : TRel.comp (TRel.comp K.rel D) K.rel =
      TRel.comp K.rel D := by
    calc
      _ = TRel.comp K.rel (TRel.comp D K.rel) :=
        TRel.comp_assoc _ _ _
      _ = TRel.comp K.rel (TRel.comp K.rel D) := by rw [← hComm]
      _ = TRel.comp K.rel D := hLeft
  have hCC : TRel.comp (TRel.comp K.rel D)
      (TRel.comp K.rel D) = K.rel := by
    funext x y
    apply propext
    constructor
    · rintro ⟨z,⟨a,hXa,hAz⟩,⟨b,hZb,hBy⟩⟩
      have hDK : TRel.comp D K.rel a b := ⟨z,hAz,hZb⟩
      have hKD : TRel.comp K.rel D a b := by
        rw [hComm]
        exact hDK
      obtain ⟨d,hAd,hDb⟩ := hKD
      have hDy : K.rel d y := hSquare d y ⟨b,hDb,hBy⟩
      exact K.setoid.trans (K.setoid.trans hXa hAd) hDy
    · intro hxy
      obtain ⟨z,hXz⟩ := hD.serial S H x
      have hZx : D z x := by
        have h : TRel.converse D z x := hXz
        rw [hDSym] at h
        exact h
      have hDK : TRel.comp D K.rel z y := ⟨x,hZx,hxy⟩
      have hKD : TRel.comp K.rel D z y := by
        rw [hComm]
        exact hDK
      exact ⟨z,⟨x,K.setoid.refl x,hXz⟩,hKD⟩
  exact {
    rel := TRel.comp K.rel D
    exact := hCExact
    left := hLeft
    right := hRight
    source := by rw [hCSym]; exact hCC
    target := by rw [hCSym]; exact hCC
  }

/-- The represented source C^2 = G identity for the original full
exact gate-correspondence C=G;D, without replacing the corresponding
whole orbital by a function. -/
theorem original_saturated_exact_square
    {i : ι} (K : Kernel S i)
    (D : TRel X i i) (hD : FullExact S D)
    (hSquare : ∀ x y, TRel.comp D D x y → K.rel x y) :
    TRel.comp (TRel.comp K.rel D) (TRel.comp K.rel D) = K.rel :=
  (original_saturated_exact_arrow S H cco K D hD hSquare).source

end
end CCO.ExactEPGeometry
