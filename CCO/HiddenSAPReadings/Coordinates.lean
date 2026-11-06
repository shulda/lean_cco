import CCO.HiddenSAPReadings.PairOrbitals

/-! Exact quotient coordinates for the literal completed carrier. Original
reals occupy their real Id quotient; no representative is inserted into a
finite closed domain. The equivalence only reorganizes existing vertices. -/
universe u v w r
namespace CCO.HiddenSAPReadings
open CCO.ParityHasse.Original CCO.TransitionClosure CCO.UnaryTermsReturn
open CCO.TypedOrbitFrames
noncomputable section
variable {ι : Type u} {X : ι → Type v} (S : AtomicSource.{u,v,w} ι X)
variable {G : Type r} [Group G] [∀ i : ι, MulAction G (X i)]
variable (H : HomogeneousSource S G)

abbrev CoordinateValue (C : OriginalCompletedCoordinateCode S H) :=
  Quotient (originalCompletedCoordinateKernel S H C).val

def sigmaVertex (p : Sigma (CoordinateValue S H)) : OriginalCompletedNamedCarrier S H :=
  coordinateVertex S H p.1 p.2

theorem sigmaVertex_bijective : Function.Bijective (sigmaVertex S H) := by
  constructor
  · rintro ⟨C,q⟩ ⟨D,r⟩ h
    have hCD : C = D := (coordinateVertex_sort S H C q).symm.trans
      ((congrArg (originalCompletedVertexSort S H) h).trans (coordinateVertex_sort S H D r))
    cases hCD
    exact congrArg (Sigma.mk C) (coordinateVertex_injective S H C h)
  · intro x
    obtain ⟨C,q,hq⟩ := original_completed_coordinate_reading_exists S H x
    exact ⟨⟨C,q⟩,reading_vertex S H hq⟩

def coordinateEquiv : Sigma (CoordinateValue S H) ≃ OriginalCompletedNamedCarrier S H :=
  Equiv.ofBijective (sigmaVertex S H) (sigmaVertex_bijective S H)

theorem coordinateEquiv_apply (C : OriginalCompletedCoordinateCode S H)
    (q : CoordinateValue S H C) : coordinateEquiv S H ⟨C,q⟩ = coordinateVertex S H C q := rfl

theorem coordinateEquiv_index (x : OriginalCompletedNamedCarrier S H) :
    ((coordinateEquiv S H).symm x).1 = originalCompletedVertexSort S H x := by
  have h := coordinateVertex_sort S H ((coordinateEquiv S H).symm x).1
    ((coordinateEquiv S H).symm x).2
  change originalCompletedVertexSort S H
    (coordinateEquiv S H ((coordinateEquiv S H).symm x)) = _ at h
  rw [Equiv.apply_symm_apply] at h
  exact h.symm

def sameSortValue (x y : OriginalCompletedNamedCarrier S H)
    (h : originalCompletedVertexSort S H x = originalCompletedVertexSort S H y) :
    CoordinateValue S H ((coordinateEquiv S H).symm x).1 :=
  ((coordinateEquiv_index S H x).trans
    (h.trans (coordinateEquiv_index S H y).symm)).symm ▸
      ((coordinateEquiv S H).symm y).2

theorem sigma_cast_value {C D : OriginalCompletedCoordinateCode S H}
    (h : C = D) (q : CoordinateValue S H D) :
    (⟨C,h.symm ▸ q⟩ : Sigma (CoordinateValue S H)) = ⟨D,q⟩ := by
  cases h
  rfl

theorem sameSortValue_vertex (x y : OriginalCompletedNamedCarrier S H)
    (h : originalCompletedVertexSort S H x = originalCompletedVertexSort S H y) :
    coordinateVertex S H ((coordinateEquiv S H).symm x).1
      (sameSortValue S H x y h) = y := by
  have hp : (⟨((coordinateEquiv S H).symm x).1,sameSortValue S H x y h⟩ :
      Sigma (CoordinateValue S H)) = (coordinateEquiv S H).symm y := by
    exact sigma_cast_value S H ((coordinateEquiv_index S H x).trans
      (h.trans (coordinateEquiv_index S H y).symm)) _
  exact (congrArg (coordinateEquiv S H) hp).trans
    ((coordinateEquiv S H).apply_symm_apply y)

theorem same_sort_transitive (x y : OriginalCompletedNamedCarrier S H)
    (h : originalCompletedVertexSort S H x = originalCompletedVertexSort S H y) :
    ∃ g : G, originalCompletedNamedAct S H g x = y := by
  let p := (coordinateEquiv S H).symm x
  let q := sameSortValue S H x y h
  obtain ⟨a,ha⟩ := Quotient.exists_rep p.2
  obtain ⟨b,hb⟩ := Quotient.exists_rep q
  obtain ⟨g,hg⟩ := S.original_sort_transitive_of_homogeneous H p.1.1 a b
  have hMove : (originalColourEqAsInvEq S H
      (originalCompletedCoordinateKernel S H p.1)).act g p.2 = q := by
    rw [← ha,← hb]
    exact congrArg (Quotient.mk _) hg
  refine ⟨g,?_⟩
  calc
    originalCompletedNamedAct S H g x =
        coordinateVertex S H p.1
          ((originalColourEqAsInvEq S H (originalCompletedCoordinateKernel S H p.1)).act g p.2) := by
      rw [coordinateVertex_equivariant]
      exact congrArg (originalCompletedNamedAct S H g)
        ((coordinateEquiv S H).apply_symm_apply x).symm
    _ = y := by rw [hMove]; exact sameSortValue_vertex S H x y h

/-- Full kernels, including the actual empty-word equality coordinate. -/
theorem coordinate_kernel_exact (nr2 : Selectors.OriginalNR2 S)
    (C : OriginalCompletedCoordinateCode S H) :
    ∃ E : RawExact.NonemptyExact S C.1 C.1,
      GroupActions.kernel (Quotient.mk (originalCompletedCoordinateKernel S H C).val) =
        RawExact.evaluate S E.words := by
  obtain ⟨word,hw⟩ := RealClosure.Bounds.terminal_raw_word_of_originalNR2 S H nr2
    (originalCompletedCoordinateKernel S H C)
  obtain ⟨x⟩ := S.nonemptySort C.1
  have heval : RawExact.evaluate S [word] =
      (originalCompletedCoordinateKernel S H C).val.r := by
    funext a b
    simpa only [RawExact.evaluate,List.mem_singleton,forall_eq] using congrFun (congrFun hw a) b
  refine ⟨⟨[word],x,x,?_⟩,?_⟩
  · rw [heval]
  · rw [heval]
    funext a b
    exact propext Quotient.eq

end
end CCO.HiddenSAPReadings
