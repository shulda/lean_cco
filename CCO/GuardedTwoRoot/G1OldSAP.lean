import CCO.GuardedTwoRoot.G1Orbits
import CCO.UnaryFreshFrames.SAPAvoidance
import Mathlib.Data.Fin.VecNotation

/-! C40: original visible SAP from the proved actual old homogeneity
and actual infinite clone orbits. The accepted ancestral hereditary
criterion is applied to a PURE RELATIONAL encoding of exactly the old
p/q/r source, and the finite-age encoding is proved in both directions.
No hidden SAP, finite-index exclusion or orbit provider is assumed. -/

namespace CCO.GuardedTwoRoot.G1
open CCO.UnaryFreshFrames
noncomputable section

abbrev Tagged := Sigma (fun _ : Unit => Real)

abbrev pureLanguage : Language where
  Sorts := Unit
  Func := Empty
  Rel := Atom
  input := Empty.elim
  output := Empty.elim
  arity _ := 2
  argument _ _ := ()

def pureModel : Structure pureLanguage Tagged where
  sort _ := ()
  func F := Empty.elim F
  func_sort F := Empty.elim F
  func_offsort F := Empty.elim F
  rel a xs := colour (xs 0).2 (xs 1).2 = some a
  rel_sort _ _ _ _ := rfl

def pureMotion (g : Aut) : pureModel.Aut := by
  refine ⟨MulAction.toPerm g,fun _ => rfl,?_,?_⟩
  · intro F
    exact Empty.elim F
  · intro a xs
    exact (congrArg (· = some a) (aut_colour g (xs 0).2 (xs 1).2)).to_iff

theorem pure_embedding_colour {A : pureModel.Piece} {T : Set Tagged}
    (f : A.Embedding T) (x y : A.points) :
    colour (f.point x).2 (f.point y).2 = colour x.val.2 y.val.2 := by
  cases h : colour x.val.2 y.val.2 with
  | none =>
    have he : x = y := Subtype.ext (tagged_ext ((colour_none _ _).mp h))
    subst y
    exact (colour_none _ _).mpr rfl
  | some a =>
    exact (f.rel_iff a ![x,y]).mpr h

theorem pure_homogeneous : pureModel.Homogeneous := by
  intro A f g
  letI : Finite A.points := A.finite.to_subtype
  obtain ⟨a,ha⟩ := finite_extension (fun x => (f.point x).2) (fun x => (g.point x).2)
    (fun x y => (pure_embedding_colour f x y).trans (pure_embedding_colour g x y).symm)
  exact ⟨pureMotion a,fun x => tagged_ext (ha x)⟩

theorem pure_infinite_closed_orbits : pureModel.InfiniteClosedOrbits pureModel.Aut := by
  intro A hA _ x hx
  let D : Set Real := Sigma.snd '' A
  have hD : D.Finite := hA.image _
  have hxD : x.2 ∉ D := by
    rintro ⟨y,hy,he⟩
    exact hx ((tagged_ext he) ▸ hy)
  obtain ⟨image,motion,hInj,hMove,hFix,_⟩ := infinite_clone_family D hD x.2 hxD
  apply Set.infinite_of_injective_forall_mem (f := fun n => (⟨(),image n⟩ : Tagged))
  · intro n m he
    exact hInj (congrArg Sigma.snd he)
  · intro n
    apply (mem_orbitOver_iff _).mpr
    refine ⟨pureMotion (motion n),?_,?_⟩
    · intro y hy
      exact tagged_ext (hFix n y.2 ⟨y,hy,rfl⟩)
    · exact tagged_ext (hMove n)

theorem pure_ageSAP : pureModel.AgeSAP :=
  pureModel.ageSAP_of_infiniteClosedOrbits pure_homogeneous pure_infinite_closed_orbits

def oldPiece (A : FiniteInduced (X := fun _ : Unit => Real)) : pureModel.Piece :=
  ⟨A.vertices,A.finite_vertices,fun F => Empty.elim F⟩

def oldEmbedding {A B : FiniteInduced (X := fun _ : Unit => Real)}
    (e : InducedEmbedding source A B) : (oldPiece A).Embedding B.vertices where
  point x := (e.toEmbedding x).val
  mem_point x := (e.toEmbedding x).property
  injective := by
    intro x y he
    exact e.toEmbedding.injective (Subtype.ext he)
  sort_eq _ := rfl
  func_eq F := Empty.elim F
  rel_iff a xs := by
    change Fin 2 → A.vertices at xs
    have hc := congrArg (fun t : Σ _ : Unit, Σ _ : Unit, Option Atom => t.2.2)
      (e.preserves_colours (xs 0) (xs 1))
    exact (congrArg (· = some a) hc.symm).to_iff

theorem tagged_colour_canonical (x y : Tagged) :
    taggedColour source x y = (⟨(),(),colour x.2 y.2⟩ : Σ _ : Unit, Σ _ : Unit, Option Atom) := by
  rcases x with ⟨⟨⟩,x⟩
  rcases y with ⟨⟨⟩,y⟩
  rfl

def toOldEmbedding {A : FiniteInduced (X := fun _ : Unit => Real)}
    {D : pureModel.Piece} (f : (oldPiece A).Embedding D.points) :
    InducedEmbedding source A ⟨D.points,D.finite⟩ where
  toEmbedding := ⟨fun x => ⟨f.point x,f.mem_point x⟩,by
    intro x y he
    exact f.injective (congrArg Subtype.val he)⟩
  preserves_sort _ := Subsingleton.elim _ _
  preserves_colours x y := by
    rw [tagged_colour_canonical,tagged_colour_canonical]
    exact congrArg (fun c => (⟨(),(),c⟩ : Σ _ : Unit, Σ _ : Unit, Option Atom))
      (pure_embedding_colour f x y).symm

/-- ACTUAL age SAP for the original complete three-atom real source. -/
theorem old_ageSAP : CCO.AgeSAP source := by
  constructor
  intro C A B eCA eCB
  obtain ⟨D,l,r,commute,strong⟩ := pure_ageSAP
    (oldPiece C) (oldPiece A) (oldPiece B) (oldEmbedding eCA) (oldEmbedding eCB)
  refine ⟨⟨D.points,D.finite⟩,toOldEmbedding l,toOldEmbedding r,?_,?_⟩
  · intro c
    exact Subtype.ext (commute c)
  · intro a b he
    obtain ⟨c,hca,hcb⟩ := strong a b (congrArg Subtype.val he)
    exact ⟨c,Subtype.ext hca,Subtype.ext hcb⟩

end
end CCO.GuardedTwoRoot.G1
