import CCO.TerminalHiddenHN.Interpretation
import CCO.FullCode.Consumer

/-! Original real roots are literal length-one tagged roots. Their
compatibility is exactly the named real-sort condition. Ambient hidden
vertices are covered by ACTUAL onto real-source terms, with no SAP,
cofinality, order or Ramsey premise used to manufacture that cover. -/

universe u v w r l k a
namespace CCO.TerminalHiddenHN.RealInterpretation
open CCO.UnaryFreshFrames
noncomputable section
variable {ι : Type u} {X : ι → Type v} {S : CCO.AtomicSource.{u,v,w} ι X}
variable {G : Type r} [Group G] [∀ i, MulAction G (X i)]
variable {U : Language.{max u l}} {V : Type k} {P : Structure U V}
variable (D : RealInterpretation (G := G) S U P)

private abbrev rootSchemeFor (B : CCO.FullCode.Language.{max u l})
    (real : ι ↪ B.Sorts) : CCO.FullCode.RootScheme B where
  Tag := ULift.{l} ι
  finiteTag := by letI : Fintype ι := S.finiteSort; infer_instance
  arity _ := 1
  coordinateSort tag _ := real tag.down
  delta _ := .truth

abbrev realRootScheme : CCO.FullCode.RootScheme D.codeLanguage :=
  rootSchemeFor (S := S) D.codeLanguage D.realSort

abbrev orderedRealRootScheme : CCO.FullCode.RootScheme D.orderedLanguage :=
  rootSchemeFor (S := S) D.orderedLanguage D.realSort

/-- Valid real roots of ANY hidden host are exactly its points with one
of the named original real sorts. This condition is quantifier free. -/
theorem realRoot_exists_iff {W : Type a} (C : CCO.FullCode.Structure D.codeLanguage W) (x : W) :
    (∃ q : CCO.FullCode.Root C D.realRootScheme, q.coordinate 0 = x) ↔
      ∃ i : ι, C.sort x = D.realSort i := by
  constructor
  · rintro ⟨q,rfl⟩
    exact ⟨q.tag.down,q.sorted 0⟩
  · rintro ⟨i,hi⟩
    exact ⟨{
      tag := ⟨i⟩
      coordinate := fun _ => x
      sorted := fun _ => hi
      valid := True.intro },rfl⟩

theorem orderedRealRoot_exists_iff {W : Type a}
    (C : CCO.FullCode.Structure D.orderedLanguage W) (x : W) :
    (∃ q : CCO.FullCode.Root C D.orderedRealRootScheme, q.coordinate 0 = x) ↔
      ∃ i : ι, C.sort x = D.realSort i := by
  constructor
  · rintro ⟨q,rfl⟩
    exact ⟨q.tag.down,q.sorted 0⟩
  · rintro ⟨i,hi⟩
    exact ⟨{
      tag := ⟨i⟩
      coordinate := fun _ => x
      sorted := fun _ => hi
      valid := True.intro },rfl⟩

private theorem rootSchemeFor_coordinate_injective
    {B : CCO.FullCode.Language.{max u l}} (real : ι ↪ B.Sorts)
    {W : Type a} (C : CCO.FullCode.Structure B W) :
    Function.Injective (fun q : CCO.FullCode.Root C (rootSchemeFor (S := S) B real) => q.coordinate 0) := by
  intro q t h
  have hs : real q.tag.down = real t.tag.down :=
    (q.sorted 0).symm.trans ((congrArg C.sort h).trans (t.sorted 0))
  have ht : q.tag = t.tag := by apply ULift.ext; exact real.injective hs
  apply CCO.FullCode.Root.ext_coordinates ht
  intro j
  have hj : j = (0 : Fin 1) := Fin.eq_zero j
  subst j
  exact h.trans (congrArg t.coordinate (Subsingleton.elim _ _))

theorem realRoot_coordinate_injective {W : Type a}
    (C : CCO.FullCode.Structure D.codeLanguage W) :
    Function.Injective (fun q : CCO.FullCode.Root C D.realRootScheme => q.coordinate 0) :=
  rootSchemeFor_coordinate_injective (S := S) D.realSort C

theorem orderedRealRoot_coordinate_injective {W : Type a}
    (C : CCO.FullCode.Structure D.orderedLanguage W) :
    Function.Injective (fun q : CCO.FullCode.Root C D.orderedRealRootScheme => q.coordinate 0) :=
  rootSchemeFor_coordinate_injective (S := S) D.realSort C

def realRoot (x : Sigma X) : CCO.FullCode.Root D.codeModel D.realRootScheme where
  tag := ⟨x.1⟩
  coordinate _ := D.realPoint x
  sorted _ := D.sort_realPoint x
  valid := True.intro

def orderedRealRoot [LinearOrder V] (x : Sigma X) :
    CCO.FullCode.Root D.orderedModel D.orderedRealRootScheme where
  tag := ⟨x.1⟩
  coordinate _ := D.realPoint x
  sorted _ := D.sort_realPoint x
  valid := True.intro

theorem realRoot_injective : Function.Injective D.realRoot := by
  intro x y h
  apply D.realPoint_injective
  exact congrArg (fun q : CCO.FullCode.Root D.codeModel D.realRootScheme => q.coordinate 0) h

theorem orderedRealRoot_injective [LinearOrder V] : Function.Injective D.orderedRealRoot := by
  intro x y h
  apply D.realPoint_injective
  exact congrArg (fun q : CCO.FullCode.Root D.orderedModel D.orderedRealRootScheme => q.coordinate 0) h

/-- A finite original real object keeps its actual marked old vertices. -/
def realObject (A : CCO.FiniteInduced (X := X)) :
    CCO.FullCode.Object D.codeModel D.realRootScheme A.vertices where
  root x := D.realRoot x.val
  injective := D.realRoot_injective.comp Subtype.val_injective

def orderedRealObject [LinearOrder V] (A : CCO.FiniteInduced (X := X)) :
    CCO.FullCode.Object D.orderedModel D.orderedRealRootScheme A.vertices where
  root x := D.orderedRealRoot x.val
  injective := D.orderedRealRoot_injective.comp Subtype.val_injective

/-- Both views have exactly the original interpreted unary closure;
order comparisons do not generate vertices. -/
theorem codeModel_closed_iff (T : Set V) : D.codeModel.IsClosed T ↔ P.Closed T := by
  letI := D.finiteSorts
  letI := D.finiteFuncs
  letI := D.finiteRels
  exact CCO.HiddenSAPReadings.partialTarget_closed_iff P T

theorem orderedModel_closed_iff [LinearOrder V] (T : Set V) :
    D.orderedModel.IsClosed T ↔ P.Closed T := D.codeModel_closed_iff T

theorem codeModel_closure (T : Set V) : D.codeModel.closure T = P.closure T := by
  apply Set.Subset.antisymm
  · exact D.codeModel.closure_minimal
      ((D.codeModel_closed_iff _).mpr (P.closure_closed T)) (P.subset_closure T)
  · exact P.closure_minimal
      ((D.codeModel_closed_iff _).mp (D.codeModel.isClosed_closure T)) (D.codeModel.subset_closure T)

theorem orderedModel_closure [LinearOrder V] (T : Set V) :
    D.orderedModel.closure T = P.closure T := by
  apply Set.Subset.antisymm
  · exact D.orderedModel.closure_minimal
      ((D.orderedModel_closed_iff _).mpr (P.closure_closed T)) (P.subset_closure T)
  · exact P.closure_minimal
      ((D.orderedModel_closed_iff _).mp (D.orderedModel.isClosed_closure T)) (D.orderedModel.subset_closure T)

theorem realObject_coordinates (A : CCO.FiniteInduced (X := X)) :
    (D.realObject A).coordinates = D.realPoint '' A.vertices := by
  ext x
  constructor
  · rintro ⟨q,j,hq⟩
    exact ⟨q.val,q.property,hq⟩
  · rintro ⟨q,hq,rfl⟩
    exact ⟨⟨q,hq⟩,0,rfl⟩

theorem orderedRealObject_coordinates [LinearOrder V] (A : CCO.FiniteInduced (X := X)) :
    (D.orderedRealObject A).coordinates = D.realPoint '' A.vertices := by
  ext x
  constructor
  · rintro ⟨q,j,hq⟩
    exact ⟨q.val,q.property,hq⟩
  · rintro ⟨q,hq,rfl⟩
    exact ⟨⟨q,hq⟩,0,rfl⟩

theorem realObject_support (A : CCO.FiniteInduced (X := X)) :
    (D.realObject A).support = P.closure (D.realPoint '' A.vertices) := by
  change D.codeModel.closure _ = _
  rw [D.realObject_coordinates,D.codeModel_closure]

theorem orderedRealObject_support [LinearOrder V] (A : CCO.FiniteInduced (X := X)) :
    (D.orderedRealObject A).support = P.closure (D.realPoint '' A.vertices) := by
  change D.orderedModel.closure _ = _
  rw [D.orderedRealObject_coordinates,D.orderedModel_closure]

/-- The cover is provided by the interpretation's genuine onto terms,
not by selecting a representative inside an orphan-containing host. -/
theorem realRootScheme_covered : CCO.FullCode.RootCovered D.codeModel D.realRootScheme := by
  letI := D.finiteSorts
  letI := D.finiteFuncs
  letI := D.finiteRels
  intro x
  obtain ⟨i,q,hq⟩ := D.projection (P.sort x)
  obtain ⟨z,hz⟩ := hq ⟨x,rfl⟩
  have he : P.eval q (D.root i z).val = x := congrArg Subtype.val hz
  refine ⟨D.realRoot ⟨i,z⟩,0,freshTermToFull U D.binary q,?_⟩
  exact (freshTermToFull_eval U D.binary P q (D.root i z).val x
    (D.root i z).property).mpr he.symm

theorem orderedRealRootScheme_covered [LinearOrder V] :
    CCO.FullCode.RootCovered D.orderedModel D.orderedRealRootScheme := by
  letI := D.finiteSorts
  letI := D.finiteFuncs
  letI := D.finiteRels
  intro x
  obtain ⟨i,q,hq⟩ := D.projection (P.sort x)
  obtain ⟨z,hz⟩ := hq ⟨x,rfl⟩
  have he : P.eval q (D.root i z).val = x := congrArg Subtype.val hz
  refine ⟨D.orderedRealRoot ⟨i,z⟩,0,freshTermToOrdered U D.binary q,?_⟩
  exact (freshTermToOrdered_eval U D.binary P q (D.root i z).val x
    (D.root i z).property).mpr he.symm

end
end CCO.TerminalHiddenHN.RealInterpretation
