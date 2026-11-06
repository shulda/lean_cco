import CCO.ExactEPGeometry.OriginalPhaseSelectedPalette
import CCO.ExactEPGeometry.OriginalRetainedOccupancyChildEquiv
import CCO.OwnerTransversal.CountableColourLanguage

/-!
# B062 C96/C103: complete common tables of the TWO actual retained sources

The common owner is the actual child sort of the retained selected phase.
The common binary colour is the COMPLETE OLD selected quotient colour,
including its owner names and logical identity. Together they encode the
entire real new atomic palette on both actual sources. Canonical marked
point sets are independent; no point identification is assumed here.
-/

universe u v w t
namespace CCO.ExactEPGeometry
open APCharacter APCharacter.SourceAge APCharacter.Towers
open RigidGroupoid.Geometry OwnerTransversal.CountableColour
noncomputable section

/-- A true unary reduct forgets precisely the child names: equal
new tagged pair colours are exactly equal child owners and equal COMPLETE
old projected pair colours. Atom injectivity includes the optional diagonal. -/
theorem unaryReductTaggedColour_iff
    {ι κ : Type u} {X : ι → Type v} {Y : κ → Type v}
    {S : AtomicSource.{u,v,w} ι X} {T : AtomicSource.{u,v,w} κ Y}
    (R : UnaryReduct S T) (q s q' s' : Sigma Y) :
    taggedColour T q' s' = taggedColour T q s ↔
      q'.1 = q.1 ∧ s'.1 = s.1 ∧
      taggedColour S (R.project q') (R.project s') =
        taggedColour S (R.project q) (R.project s) := by
  rcases q with ⟨i,x⟩
  rcases s with ⟨j,y⟩
  rcases q' with ⟨i',x'⟩
  rcases s' with ⟨j',y'⟩
  constructor
  · intro h
    have hi : i' = i := (Sigma.mk.inj h).1
    subst i'
    have hj : j' = j := (Sigma.mk.inj (eq_of_heq (Sigma.mk.inj h).2)).1
    subst j'
    have hc : T.colour x' y' = T.colour x y :=
      eq_of_heq (Sigma.mk.inj (eq_of_heq (Sigma.mk.inj h).2)).2
    refine ⟨rfl,rfl,?_⟩
    change (⟨R.parent i,R.parent j,S.colour (R.point i x') (R.point j y')⟩ : Age.Colour S) =
      ⟨R.parent i,R.parent j,S.colour (R.point i x) (R.point j y)⟩
    rw [R.colour,R.colour,hc]
  · rintro ⟨hi,hj,h⟩
    dsimp only at hi hj
    subst i'
    subst j'
    have hc : S.colour (R.point i x') (R.point j y') = S.colour (R.point i x) (R.point j y) :=
      eq_of_heq (Sigma.mk.inj (eq_of_heq (Sigma.mk.inj h).2)).2
    have hm : (T.colour x' y').map (R.atom i j) = (T.colour x y).map (R.atom i j) :=
      (R.colour i j x' y').symm.trans (hc.trans (R.colour i j x y))
    have hn := Option.map_injective (R.atom_injective i j) hm
    exact congrArg (fun a => (⟨i,j,a⟩ : Age.Colour T)) hn

variable (A B : CurrentSource.{u,v,w,t})
variable (P : UnaryReduct A.source B.source)
variable (transport : ExactTraceTransport A.source B.source P)
variable (tp : ExactTraceProduct A.source B.source P)
variable (hOne : ∀ i j : A.Sorts, i = j)
variable {r : B.Sorts} (Kroot : Kernel B.source r)
variable (phase : SourcePhase B.source B.homogeneous
  (exactCalculus_of_homogeneous_CCO B.source B.homogeneous B.cco) Kroot)
variable (E : ExactEq A.source (P.parent r))
variable (hE : E ≤ PrefixExactLargestLift.largest A B P transport tp r
  (current_kernel_exact_eq B Kroot))

/-- Actual successor original-E quotient, named by the TRUE selected
child sorts and COMPLETE old selected quotient colours. -/
def originalRetainedQuotientComparisonTable :
    let base := P.parent r
    let hBase : ∀ i : A.Sorts, base = i := fun i => hOne base i
    let N := SingleStep.successor B phase
    let R := SingleStep.projection B phase
    let hN := ExactTraceTransport.compose P R transport (canonical_step_exact_transport B phase)
    let QN := originalExactSelectedQuotientCurrentSource A N (P.compose R) hN base hBase E
    let QB := originalExactSelectedQuotientCurrentSource A B P transport base hBase E
    let φ := originalRetainedActualSelectedPhase A B P transport tp hOne Kroot phase E hE
    let M := SingleStep.successor QB φ
    Table M.Sorts (Age.Colour QB.source) (Sigma QN.Point) := by
  let base := P.parent r
  let hBase : ∀ i : A.Sorts, base = i := fun i => hOne base i
  let f := originalPhaseSelectedPointEquiv A B P transport Kroot phase base hBase E
  let QB := originalExactSelectedQuotientCurrentSource A B P transport base hBase E
  exact {
    owner := fun q => originalRetainedOccupancyChildEquiv A B P transport tp hOne Kroot phase E hE q.1
    colour := fun q s => taggedColour QB.source (f q) (f s)
  }

/-- Actual selected SourcePhase successor with the SAME literal owner
and old-colour code, under its true bijective unary reduct. -/
def originalRetainedSuccessorComparisonTable :
    let base := P.parent r
    let hBase : ∀ i : A.Sorts, base = i := fun i => hOne base i
    let QB := originalExactSelectedQuotientCurrentSource A B P transport base hBase E
    let φ := originalRetainedActualSelectedPhase A B P transport tp hOne Kroot phase E hE
    let M := SingleStep.successor QB φ
    Table M.Sorts (Age.Colour QB.source) (Sigma M.Point) := by
  let base := P.parent r
  let hBase : ∀ i : A.Sorts, base = i := fun i => hOne base i
  let QB := originalExactSelectedQuotientCurrentSource A B P transport base hBase E
  let φ := originalRetainedActualSelectedPhase A B P transport tp hOne Kroot phase E hE
  let RM := SingleStep.projection QB φ
  exact {
    owner := Sigma.fst
    colour := fun x y => taggedColour QB.source (RM.project x) (RM.project y)
  }

/-- Literal owner readout on the actual quotient table. -/
theorem originalRetainedQuotientComparisonTable_owner :
    let base := P.parent r
    let hBase : ∀ i : A.Sorts, base = i := fun i => hOne base i
    let N := SingleStep.successor B phase
    let R := SingleStep.projection B phase
    let hN := ExactTraceTransport.compose P R transport (canonical_step_exact_transport B phase)
    let QN := originalExactSelectedQuotientCurrentSource A N (P.compose R) hN base hBase E
    ∀ q : Sigma QN.Point,
      (originalRetainedQuotientComparisonTable A B P transport tp hOne Kroot phase E hE).owner q =
        originalRetainedOccupancyChildEquiv A B P transport tp hOne Kroot phase E hE q.1 := by
  dsimp only
  intro q
  rfl

/-- Literal COMPLETE old colour readout on the actual quotient table. -/
theorem originalRetainedQuotientComparisonTable_colour :
    let base := P.parent r
    let hBase : ∀ i : A.Sorts, base = i := fun i => hOne base i
    let N := SingleStep.successor B phase
    let R := SingleStep.projection B phase
    let hN := ExactTraceTransport.compose P R transport (canonical_step_exact_transport B phase)
    let QN := originalExactSelectedQuotientCurrentSource A N (P.compose R) hN base hBase E
    let QB := originalExactSelectedQuotientCurrentSource A B P transport base hBase E
    let f := originalPhaseSelectedPointEquiv A B P transport Kroot phase base hBase E
    ∀ q s : Sigma QN.Point,
      (originalRetainedQuotientComparisonTable A B P transport tp hOne Kroot phase E hE).colour q s =
        taggedColour QB.source (f q) (f s) := by
  dsimp only
  intro q s
  rfl

/-- Literal actual child-owner readout on the true selected successor. -/
theorem originalRetainedSuccessorComparisonTable_owner :
    let base := P.parent r
    let hBase : ∀ i : A.Sorts, base = i := fun i => hOne base i
    let QB := originalExactSelectedQuotientCurrentSource A B P transport base hBase E
    let φ := originalRetainedActualSelectedPhase A B P transport tp hOne Kroot phase E hE
    let M := SingleStep.successor QB φ
    ∀ q : Sigma M.Point,
      (originalRetainedSuccessorComparisonTable A B P transport tp hOne Kroot phase E hE).owner q = q.1 := by
  dsimp only
  intro q
  rfl

/-- Literal old-colour readout under the actual unary projection. -/
theorem originalRetainedSuccessorComparisonTable_colour :
    let base := P.parent r
    let hBase : ∀ i : A.Sorts, base = i := fun i => hOne base i
    let QB := originalExactSelectedQuotientCurrentSource A B P transport base hBase E
    let φ := originalRetainedActualSelectedPhase A B P transport tp hOne Kroot phase E hE
    let M := SingleStep.successor QB φ
    let RM := SingleStep.projection QB φ
    ∀ q s : Sigma M.Point,
      (originalRetainedSuccessorComparisonTable A B P transport tp hOne Kroot phase E hE).colour q s =
        taggedColour QB.source (RM.project q) (RM.project s) := by
  dsimp only
  intro q s
  rfl

/-- Both common owners plus the common old colour encode the ENTIRE
actual successor quotient atomic palette, with no erased child labels. -/
theorem originalRetainedQuotientComparisonTable_palette_iff :
    let base := P.parent r
    let hBase : ∀ i : A.Sorts, base = i := fun i => hOne base i
    let N := SingleStep.successor B phase
    let R := SingleStep.projection B phase
    let hN := ExactTraceTransport.compose P R transport (canonical_step_exact_transport B phase)
    let QN := originalExactSelectedQuotientCurrentSource A N (P.compose R) hN base hBase E
    let T := originalRetainedQuotientComparisonTable A B P transport tp hOne Kroot phase E hE
    ∀ (q s q' s' : Sigma QN.Point),
      taggedColour QN.source q' s' = taggedColour QN.source q s ↔
        T.owner q' = T.owner q ∧ T.owner s' = T.owner s ∧ T.colour q' s' = T.colour q s := by
  dsimp only
  intro q s q' s'
  let e := originalRetainedOccupancyChildEquiv A B P transport tp hOne Kroot phase E hE
  have h := originalPhaseSelectedTaggedColour_iff A B P transport tp hOne Kroot phase E q s q' s'
  constructor
  · intro hc
    obtain ⟨hq,hs,hColour⟩ := h.mp hc
    exact ⟨congrArg e hq,congrArg e hs,hColour⟩
  · rintro ⟨hq,hs,hColour⟩
    exact h.mpr ⟨e.injective hq,e.injective hs,hColour⟩

/-- On the actual selected SourcePhase successor the SAME common code
also preserves and reflects every full atomic pair colour. -/
theorem originalRetainedSuccessorComparisonTable_palette_iff :
    let base := P.parent r
    let hBase : ∀ i : A.Sorts, base = i := fun i => hOne base i
    let QB := originalExactSelectedQuotientCurrentSource A B P transport base hBase E
    let φ := originalRetainedActualSelectedPhase A B P transport tp hOne Kroot phase E hE
    let M := SingleStep.successor QB φ
    let T := originalRetainedSuccessorComparisonTable A B P transport tp hOne Kroot phase E hE
    ∀ (q s q' s' : Sigma M.Point),
      taggedColour M.source q' s' = taggedColour M.source q s ↔
        T.owner q' = T.owner q ∧ T.owner s' = T.owner s ∧ T.colour q' s' = T.colour q s := by
  let base := P.parent r
  let hBase : ∀ i : A.Sorts, base = i := fun i => hOne base i
  let QB := originalExactSelectedQuotientCurrentSource A B P transport base hBase E
  let φ := originalRetainedActualSelectedPhase A B P transport tp hOne Kroot phase E hE
  dsimp only
  intro q s q' s'
  exact unaryReductTaggedColour_iff (SingleStep.projection QB φ) q s q' s'

end
end CCO.ExactEPGeometry
