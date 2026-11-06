import CCO.TypedOrbitFrames.CompletedStructureAction
import CCO.UnaryTermsReturn.CompletedNamedBinaryCoverage

/-! The accepted semantic cylinder language is the FULL original pair-orbital
language. This identification is proved using common fine representatives;
no finer hidden pair partition or hidden homogeneity is assumed. -/

universe u v w r
namespace CCO.HiddenSAPReadings
open CCO.ParityHasse.Original CCO.TransitionClosure CCO.UnaryTermsReturn
open CCO.TypedOrbitFrames
noncomputable section
variable {ι : Type u} {X : ι → Type v} (S : AtomicSource.{u,v,w} ι X)
variable {G : Type r} [Group G] [∀ i : ι, MulAction G (X i)]
variable (H : HomogeneousSource S G)

/-- A real coordinate is the genuine equality quotient. -/
def coordinateVertex (C : OriginalCompletedCoordinateCode S H) :
    Quotient (originalCompletedCoordinateKernel S H C).val →
      OriginalCompletedNamedCarrier S H :=
  match C with
  | ⟨i,.inl _⟩ => fun q => Quotient.liftOn q (fun x => .inl ⟨i,x⟩)
      (by intro x y h; cases h; rfl)
  | ⟨_,.inr D⟩ => originalCompletedNamedHiddenNode S H D

theorem reading_vertex {x : OriginalCompletedNamedCarrier S H}
    {C : OriginalCompletedCoordinateCode S H}
    {q : Quotient (originalCompletedCoordinateKernel S H C).val}
    (h : OriginalCompletedCoordinateReading S H x C q) :
    coordinateVertex S H C q = x := by cases h <;> rfl

theorem vertex_reading (C : OriginalCompletedCoordinateCode S H)
    (q : Quotient (originalCompletedCoordinateKernel S H C).val) :
    OriginalCompletedCoordinateReading S H (coordinateVertex S H C q) C q := by
  rcases C with ⟨i,_ | D⟩
  · induction q using Quotient.inductionOn with
    | _ x => exact .real x
  · exact .hidden D q

theorem coordinateVertex_sort (C : OriginalCompletedCoordinateCode S H)
    (q : Quotient (originalCompletedCoordinateKernel S H C).val) :
    originalCompletedVertexSort S H (coordinateVertex S H C q) = C :=
  original_completed_reading_sort S H (vertex_reading S H C q)

theorem coordinateVertex_injective (C : OriginalCompletedCoordinateCode S H) :
    Function.Injective (coordinateVertex S H C) := by
  rcases C with ⟨i,_ | D⟩
  · intro q r h
    induction q using Quotient.inductionOn with
    | _ x =>
      induction r using Quotient.inductionOn with
      | _ y =>
        apply Quotient.sound
        exact sigma_mk_injective (Sum.inl.inj h)
  · exact original_completed_hidden_node_injective S H D

theorem coordinateVertex_equivariant (C : OriginalCompletedCoordinateCode S H)
    (g : G) (q : Quotient (originalCompletedCoordinateKernel S H C).val) :
    coordinateVertex S H C
        ((originalColourEqAsInvEq S H (originalCompletedCoordinateKernel S H C)).act g q) =
      originalCompletedNamedAct S H g (coordinateVertex S H C q) := by
  rcases C with ⟨i,_ | D⟩
  · induction q using Quotient.inductionOn with
    | _ x => rfl
  · rfl

/-- Equality of two complete semantic labels gives ONE old motion of
both actual quotient positions, by a common old fine atom. -/
theorem same_cylinder_motion {i j : ι} (J : ColourEq S i) (K : ColourEq S j)
    (P : S.Menu i j) (hP : P ∈ originalTypedCylinderNames S J K)
    (q q' : Quotient J.val) (r r' : Quotient K.val)
    (h : originalTypedCylinderSemanticRelation S J K P q r)
    (h' : originalTypedCylinderSemanticRelation S J K P q' r') :
    ∃ g : G, (originalColourEqAsInvEq S H J).act g q = q' ∧
      (originalColourEqAsInvEq S H K).act g r = r' := by
  obtain ⟨c,hc⟩ := hP
  have hmem : c ∈ P := hc ▸ originalTypedCylinderName_contains_atom S J K c
  obtain ⟨x,y,hx,hy,hxy⟩ := h ▸ hmem
  obtain ⟨x',y',hx',hy',hxy'⟩ := h' ▸ hmem
  obtain ⟨g,hgx,hgy⟩ := S.pair_homogeneous_of_homogeneous H x x' y y'
    (hxy.trans hxy'.symm)
  refine ⟨g,?_,?_⟩
  · rw [← hx,← hx']
    exact congrArg (Quotient.mk J.val) hgx
  · rw [← hy,← hy']
    exact congrArg (Quotient.mk K.val) hgy

/-- Each completed binary predicate is ONE actual original orbital. -/
theorem same_binary_motion (name : OriginalCompletedCylinderBinaryName S H)
    {a b a' b' : OriginalCompletedNamedCarrier S H}
    (h : originalCompletedCylinderBinaryPredicate S H name a b)
    (h' : originalCompletedCylinderBinaryPredicate S H name a' b') :
    ∃ g : G, originalCompletedNamedAct S H g a = a' ∧
      originalCompletedNamedAct S H g b = b' := by
  obtain ⟨_,q,r,hq,hr,hqr⟩ := h
  obtain ⟨_,q',r',hq',hr',hqr'⟩ := h'
  obtain ⟨g,hgq,hgr⟩ := same_cylinder_motion S H _ _ name.2.2.val
    name.2.2.property q q' r r' hqr hqr'
  refine ⟨g,?_,?_⟩
  · rw [← reading_vertex S H hq,← reading_vertex S H hq',
      ← coordinateVertex_equivariant,hgq]
  · rw [← reading_vertex S H hr,← reading_vertex S H hr',
      ← coordinateVertex_equivariant,hgr]

end
end CCO.HiddenSAPReadings
