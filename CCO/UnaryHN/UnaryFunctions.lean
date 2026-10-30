import CCO.UnaryHN.NativeTransferBasis
import Lean.Elab.Tactic.Omega

/-! The actual unary domain and closed-image lemmas used in the functional
HN construction.  No relational graph or weak induced subset replaces a
functional substructure. -/

universe u v
namespace CCO.UnaryHN.Native

open StructuralRamsey
open StructuralRamsey.Structure

variable {L : Language.{u}} {V W X : Type v}

theorem one_point_hull_irreducible (C : Structure L V) (c : V) :
    (C.induce (C.functionClosure (Set.range (fun _ : PUnit.{v+1} => c)))
      (C.functionClosure_isClosed (Set.range (fun _ : PUnit.{v+1} => c)))).Irreducible := by
  let q : PUnit.{v+1} → V := fun _ => c
  let H := C.induce (C.functionClosure (Set.range q))
    (C.functionClosure_isClosed (Set.range q))
  have hGen : H.Generates (closureLift C q) := closureLift_generates C q
  intro G E F Z Root Left Right Whole sL sR iL iR hFree e
  rcases hFree.covers (e (closureLift C q PUnit.unit)) with ⟨x, hx⟩ | ⟨x, hx⟩
  · left
    intro a
    have hClosed : H.IsClosed {a | e a ∈ Set.range iL} :=
      e.preimage_isClosed (Set.range iL) iL.range_isClosed
    have hSeed : ∀ z : PUnit.{v+1}, e (closureLift C q z) ∈ Set.range iL := by
      intro z
      have hz : z = PUnit.unit := Subsingleton.elim _ _
      subst z
      exact ⟨x, hx.symm⟩
    obtain ⟨y, hy⟩ := hGen _ hClosed hSeed a
    exact ⟨y, hy.symm⟩
  · right
    intro a
    have hClosed : H.IsClosed {a | e a ∈ Set.range iR} :=
      e.preimage_isClosed (Set.range iR) iR.range_isClosed
    have hSeed : ∀ z : PUnit.{v+1}, e (closureLift C q z) ∈ Set.range iR := by
      intro z
      have hz : z = PUnit.unit := Subsingleton.elim _ _
      subst z
      exact ⟨x, hx.symm⟩
    obtain ⟨y, hy⟩ := hGen _ hClosed hSeed a
    exact ⟨y, hy.symm⟩

/-- In unary languages an HE reflects domains at every point because it
embeds that point's WHOLE generated closed irreducible structure. -/
theorem HE.full {C : Structure L V} {D : Structure L W} {p : V → W}
    (hUnary : Unary L) (hp : HE C D p) : C.IsHomomorphism D p := by
  refine ⟨hp.1.1, ?_⟩
  intro F x
  ext y
  constructor
  · rintro ⟨z, hz, rfl⟩
    exact hp.1.2 F x z hz
  · intro hy
    have hPos : 0 < L.funcArity F := by rw [hUnary F]; decide
    let i0 : Fin (L.funcArity F) := ⟨0, hPos⟩
    have hIndex : ∀ i : Fin (L.funcArity F), i = i0 := by
      intro i
      apply Fin.ext
      have hi : i.val < 1 := Nat.lt_of_lt_of_eq i.isLt (hUnary F)
      change i.val = 0
      omega
    let c := x i0
    let q : PUnit.{v+1} → V := fun _ => c
    let S := C.functionClosure (Set.range q)
    have hS := C.functionClosure_isClosed (Set.range q)
    let H := C.induce S hS
    let inc : Embedding H C := inclusion C S hS
    obtain ⟨g, hg⟩ := hp.2 H (one_point_hull_irreducible C c) inc
    let cH : S := closureLift C q PUnit.unit
    let xH : Fin (L.funcArity F) → S := fun _ => cH
    have hArgs : Subtype.val ∘ xH = x := by
      funext i
      rw [hIndex i]
      rfl
    have hGArgs : g ∘ xH = p ∘ x := by
      funext i
      rw [hIndex i]
      exact hg cH
    have hy' : y ∈ D.func F (g ∘ xH) := by rw [hGArgs]; exact hy
    rw [← g.map_func F xH] at hy'
    obtain ⟨z, hz, hzy⟩ := hy'
    refine ⟨z.val, ?_, ?_⟩
    · change z.val ∈ C.func F (Subtype.val ∘ xH) at hz
      rwa [hArgs] at hz
    · exact (hg z).symm.trans hzy

theorem full_image_closed {C : Structure L V} {D : Structure L W} {p : V → W}
    (hp : C.IsHomomorphism D p) (S : Set V) (hS : C.IsClosed S) :
    D.IsClosed (p '' S) := by
  intro F x hx y hy
  choose a ha hEq using hx
  have hArgs : p ∘ a = x := funext hEq
  rw [← hArgs, ← hp.2 F a] at hy
  obtain ⟨z, hz, hzy⟩ := hy
  exact ⟨z, hS F a ha hz, hzy⟩

def embedding_codRestrict {C : Structure L V} {D : Structure L W}
    (e : Embedding C D) (S : Set W) (hS : D.IsClosed S)
    (hRange : ∀ x, e x ∈ S) : Embedding C (D.induce S hS) where
  toFun x := ⟨e x, hRange x⟩
  injective := by intro x y h; exact e.injective (congrArg Subtype.val h)
  map_rel_iff R xs := e.map_rel_iff R xs
  map_func F xs := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      change e x ∈ D.func F (e ∘ xs)
      rw [← e.map_func F xs]
      exact ⟨x, hx, rfl⟩
    · intro hy
      change y.val ∈ D.func F (e ∘ xs) at hy
      rw [← e.map_func F xs] at hy
      obtain ⟨x, hx, hxy⟩ := hy
      exact ⟨x, hx, Subtype.ext hxy⟩

theorem HE.codRestrict {C : Structure L V} {D : Structure L W} {p : V → W}
    (hp : HE C D p) (S : Set W) (hS : D.IsClosed S)
    (hRange : ∀ x, p x ∈ S) :
    HE C (D.induce S hS) (fun x => ⟨p x, hRange x⟩) := by
  refine ⟨⟨hp.1.1, hp.1.2⟩, ?_⟩
  intro Z E hE e
  obtain ⟨g, hg⟩ := hp.2 E hE e
  have hGRange : ∀ z, g z ∈ S := by intro z; rw [hg z]; exact hRange (e z)
  exact ⟨embedding_codRestrict g S hS hGRange, fun z => Subtype.ext (hg z)⟩

theorem HasCompletion.pullback {K : Class.{u,v} L}
    {C : Structure L V} {D : Structure L W} {p : V → W}
    (hp : HE C D p) (hD : HasCompletion K D) : HasCompletion K C := by
  obtain ⟨Z, hZ, T, hT, q, hq⟩ := hD
  exact ⟨Z, hZ, T, hT, q ∘ p, hq.comp hp⟩

end CCO.UnaryHN.Native
