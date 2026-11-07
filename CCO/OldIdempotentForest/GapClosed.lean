import CCO.OldIdempotentForest.GapSuffix
import CCO.OldIdempotentForest.GapCoordinates

/-! Actual closed-word holonomy is transferred to the valid OLD singleton.
The resulting boundary equality exists BEFORE deleting any old root. -/

universe u v w r z
namespace CCO.OldIdempotentForest
open CCO.GuardedOldSeams CCO.GuardedTwoRoot CCO.QuotientTransport
open CCO.UnaryTermsReturn CCO.TransitionClosure CCO.ParityHasse.Original
open CCO.HiddenSAPReadings CCO.TypedOrbitFrames CCO.UnaryFreshFrames
noncomputable section
variable {ι : Type u} {X : ι → Type v} (S : AtomicSource.{u,v,w} ι X)
variable {G : Type r} [Group G] [∀ i, MulAction G (X i)]
variable (H : HomogeneousSource S G) (sap : AgeSAP S) (nr2 : Selectors.OriginalNR2 S)
local notation "Lang" => originalCompletedLanguage S H sap nr2
local notation "Hidden" => originalCompletedStructure S H sap nr2

/-- Only the endpoint SORT equality is cast. Every original atomic
letter and position of the concatenated positive word is retained. -/
def gapCloseWord {i j : ι} (h : i = j) (W : PositiveWord S i j) : PositiveWord S j j := by
  cases h
  exact W

def gapIdentityPrefix {i j : ι} (h : i = j) : Word G X j i := by
  cases h
  exact .nil i

include sap in
theorem gap_closed_raw_bound {i j : ι} (hij : i = j)
    (W : PositiveWord S i j) (raw : Word G X i j)
    (inside : ∀ x y, raw.eval x y → PositiveWord.represented S W x y)
    (idem : S.product (PositiveWord.profile S (gapCloseWord S hij W))
      (PositiveWord.profile S (gapCloseWord S hij W)) =
        PositiveWord.profile S (gapCloseWord S hij W))
    (D : OriginalNamedHiddenCoordinate S H j)
    (above : envelope S (PositiveWord.profile S (gapCloseWord S hij W)) idem ≤ D.val) :
    Return.Bound (originalColourEqAsInvEq S H D.val) (gapIdentityPrefix (G := G) (X := X) hij) raw := by
  cases hij
  rintro x z ⟨y,hxy,hyz⟩
  change x = y at hxy
  subst y
  apply above
  by_cases hxz : x = z
  · exact Or.inl hxz
  · exact Or.inr ((positive_profile_pair_iff S H sap W x z).mpr ⟨hxz,inside x z hyz⟩)

theorem gap_initial_sort_eq {i j : ι} (hij : i = j)
    (D : OriginalNamedHiddenCoordinate S H j) (raw : Word G X i j)
    (h : Return.Bound (originalColourEqAsInvEq S H D.val)
      (gapIdentityPrefix (G := G) (X := X) hij) raw) :
    gapHiddenSort S H sap nr2 (originalNamedReturnPrefixCoordinate S H sap nr2 D
      (gapIdentityPrefix (G := G) (X := X) hij) raw h) = gapHiddenSort S H sap nr2 D := by
  cases hij
  exact congrArg (gapHiddenSort S H sap nr2)
    (original_named_return_empty_prefix_coordinate_eq S H sap nr2 D raw h)

def gapInitialReadback {i j : ι} (hij : i = j)
    (D : OriginalNamedHiddenCoordinate S H j) (raw : Word G X i j)
    (h : Return.Bound (originalColourEqAsInvEq S H D.val)
      (gapIdentityPrefix (G := G) (X := X) hij) raw) :
    CCO.UnaryFreshFrames.Term Lang
      (gapHiddenSort S H sap nr2 (originalNamedReturnPrefixCoordinate S H sap nr2 D
        (gapIdentityPrefix (G := G) (X := X) hij) raw h)) (gapHiddenSort S H sap nr2 D) :=
  Eq.mp (congrArg (fun C => CCO.UnaryFreshFrames.Term Lang
      (gapHiddenSort S H sap nr2 (originalNamedReturnPrefixCoordinate S H sap nr2 D
        (gapIdentityPrefix (G := G) (X := X) hij) raw h)) C)
    (gap_initial_sort_eq S H sap nr2 hij D raw h)) (.id _)

theorem gap_cast_identity_eval {C D : (Lang).Sorts} (h : C = D)
    (x : OriginalCompletedNamedCarrier S H) :
    (Hidden).eval (Eq.mp (congrArg (fun E => CCO.UnaryFreshFrames.Term Lang C E) h) (.id C)) x = x := by
  cases h
  rfl

theorem gap_initial_prefix_label {i j : ι} (hij : i = j)
    (D : OriginalNamedHiddenCoordinate S H j) (raw : Word G X i j)
    (h : Return.Bound (originalColourEqAsInvEq S H D.val)
      (gapIdentityPrefix (G := G) (X := X) hij) raw) (x : X i) :
    (Return.prefixTransport (originalColourEqAsInvEq S H D.val)
      (originalReturnSortTransitivity S H) (gapIdentityPrefix (G := G) (X := X) hij) raw h).label x =
        Quotient.mk D.val.val (Eq.mp (congrArg X hij) x) := by
  cases hij
  exact Return.initial_label (originalColourEqAsInvEq S H D.val)
    (originalReturnSortTransitivity S H) raw h x

theorem gap_initial_readback_semantics {i j : ι} (hij : i = j)
    (D : OriginalNamedHiddenCoordinate S H j) (raw : Word G X i j)
    (h : Return.Bound (originalColourEqAsInvEq S H D.val)
      (gapIdentityPrefix (G := G) (X := X) hij) raw) (x : X i) :
    (Hidden).eval (gapInitialReadback S H sap nr2 hij D raw h)
      (originalCompletedNamedHiddenNode S H
        (originalNamedReturnPrefixCoordinate S H sap nr2 D
          (gapIdentityPrefix (G := G) (X := X) hij) raw h) (Quotient.mk _ x)) =
    originalCompletedNamedHiddenNode S H D
      ((Return.prefixTransport (originalColourEqAsInvEq S H D.val)
        (originalReturnSortTransitivity S H) (gapIdentityPrefix (G := G) (X := X) hij) raw h).label x) := by
  have hid := gap_cast_identity_eval S H sap nr2 (gap_initial_sort_eq S H sap nr2 hij D raw h)
  apply (hid _).trans
  cases hij
  have hK := original_named_return_empty_prefix_coordinate_eq S H sap nr2 D raw h
  exact (congrArg (fun K : OriginalNamedHiddenCoordinate S H i =>
      originalCompletedNamedHiddenNode S H K (Quotient.mk K.val.val x)) hK).trans
    (congrArg (originalCompletedNamedHiddenNode S H D)
      (Return.initial_label (originalColourEqAsInvEq S H D.val)
        (originalReturnSortTransitivity S H) raw h x).symm)

variable {P : Type z} [Finite P]
variable (F : CCO.UnarySupport.Structure (originalPartialSignature S H sap nr2) P)
variable (hUnary : UnaryAdmissible F (originalPartialTarget S H sap nr2))

/-- The boundary term values are the actual canonical D-coordinates.
The possibly different written endpoint sort names use only their proved
same-real-sort equality; no new representative coordinate is named. -/
structure GapCoordinateCertificate {b c : P}
    (hij : gapSort S H sap nr2 F b = gapSort S H sap nr2 F c)
    (D : OriginalNamedHiddenCoordinate S H (gapSort S H sap nr2 F c)) where
  left : CCO.UnaryFreshFrames.Term Lang (F.sort b) (gapHiddenSort S H sap nr2 D)
  right : CCO.UnaryFreshFrames.Term Lang (F.sort c) (gapHiddenSort S H sap nr2 D)
  equation : LiteralOldEquation S H sap nr2 F left right b c
  left_reading : ∀ x, (Hidden).eval left (rootMap S H sap nr2 (F.sort b) x) =
    originalCompletedNamedHiddenNode S H D (Quotient.mk D.val.val (Eq.mp (congrArg X hij) x))
  right_reading : ∀ y, (Hidden).eval right (rootMap S H sap nr2 (F.sort c) y) =
    originalCompletedNamedHiddenNode S H D (Quotient.mk D.val.val y)

include hUnary in
/-- Source OGC: canonical return, actual OLD sides and ONE valid source
singleton yield a literal equality BEFORE any interval deletion. -/
theorem old_gap_coordinate_equation {b c : P}
    (path : SourceMacroPath S H sap nr2 F b c)
    (hij : gapSort S H sap nr2 F b = gapSort S H sap nr2 F c)
    (idem : S.product (PositiveWord.profile S (gapCloseWord S hij path.flatten))
      (PositiveWord.profile S (gapCloseWord S hij path.flatten)) =
        PositiveWord.profile S (gapCloseWord S hij path.flatten))
    (D : OriginalNamedHiddenCoordinate S H (gapSort S H sap nr2 F c))
    (above : envelope S (PositiveWord.profile S (gapCloseWord S hij path.flatten)) idem ≤ D.val) :
    Nonempty (GapCoordinateCertificate S H sap nr2 F hij D) := by
  let h := gap_closed_raw_bound S H sap hij path.flatten path.rawWord
    path.raw_inside_flatten idem D above
  let p := gapIdentityPrefix (G := G) (X := X) hij
  obtain ⟨out⟩ := gap_return_suffix S H sap nr2 F hUnary path D p h
  let K := originalNamedReturnPrefixCoordinate S H sap nr2 D p path.rawWord h
  let τ0 := rootCoordinateTerm S H sap nr2 (F.sort b) K out.leftKernel
  let τm := rootCoordinateTerm S H sap nr2 (F.sort c) D out.rightKernel
  let ρ := gapInitialReadback S H sap nr2 hij D path.rawWord h
  have hIdentity : ∀ q : OriginalCompletedNamedCarrier S H,
      (Hidden).sort q = F.sort b →
      (Hidden).eval (out.term.comp τ0) q = (Hidden).eval (ρ.comp τ0) q := by
    intro q hq
    let v := (Hidden).eval τ0 q
    have hvSort : (Hidden).sort v = gapHiddenSort S H sap nr2 K := (Hidden).eval_sort τ0 hq
    obtain ⟨vq,hvq⟩ := original_completed_hidden_carrier_exists S H sap nr2 K ⟨v,hvSort⟩
    obtain ⟨x,hx⟩ := Quotient.exists_rep vq
    have hv : v = originalCompletedNamedHiddenNode S H K (Quotient.mk K.val.val x) :=
      hvq.trans (congrArg (originalCompletedNamedHiddenNode S H K) hx.symm)
    exact ((Hidden).eval_comp out.term τ0 q).trans
      ((congrArg ((Hidden).eval out.term) hv).trans
        ((out.semantics x).trans
          ((gap_initial_readback_semantics S H sap nr2 hij D path.rawWord h x).symm.trans
            ((congrArg ((Hidden).eval ρ) hv.symm).trans ((Hidden).eval_comp ρ τ0 q).symm))))
  have hOldId := gap_unary_admissible_identity S H sap nr2 F hUnary
    (out.term.comp τ0) (ρ.comp τ0) hIdentity b rfl
  obtain ⟨v,hv,hvm⟩ := out.equation
  obtain ⟨v',hv',hv0⟩ := hOldId
  have hEq : v = v' := F.eval_functional _ hv hv'
  refine ⟨{ left := ρ.comp τ0, right := τm
            equation := ⟨v,hEq.symm ▸ hv0,hvm⟩
            left_reading := ?_, right_reading := ?_ }⟩
  · intro x
    exact ((Hidden).eval_comp ρ τ0 _).trans
      ((congrArg ((Hidden).eval ρ) (rootCoordinateTerm_eval S H sap nr2 (F.sort b) K out.leftKernel x)).trans
        ((gap_initial_readback_semantics S H sap nr2 hij D path.rawWord h x).trans
          (congrArg (originalCompletedNamedHiddenNode S H D)
            (gap_initial_prefix_label S H hij D path.rawWord h x))))
  · exact rootCoordinateTerm_eval S H sap nr2 (F.sort c) D out.rightKernel

end
end CCO.OldIdempotentForest
