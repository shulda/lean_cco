import CCO.APRamseyReadout.CoordinateBridge
import CCO.APRamseyReadout.OwnerAction
import CCO.FullCode.LanguageExpansion
import CCO.TypedOrbitFrames.ActualProjectionSystem
import Mathlib.Tactic.Choose

/-! Fixed nonempty selected-MI charts are literal tagged finite tuples.
Their qf domain is the existing clone-marker membership formula, rendered
in the shared actual hidden language with equality kept separate from
off-diagonal cylinders. Symbol enumerations are fixed once, not per point. -/

universe u v w p z
namespace CCO.APRamseyReadout
open CCO.CloneTupleGeometry CCO.CloneTupleGeometry.OwnerStage
open CCO.UnaryTermsReturn CCO.TypedOrbitFrames CCO.TransitionClosure
open CCO.FullCode
noncomputable section
variable (B : OwnerStage.{u,v,w}) (ht : B.Terminal) (F : Charts.{u,v,w,p} B)

abbrev chartCoordinate (i : B.Sorts) (k : Fin (chartArity F i)) : NamedCoordinate B i :=
  namedCoordinateHF B ht i (chartSymbol F i k)

abbrev chartSort (i : B.Sorts) (k : Fin (chartArity F i)) : (CoordinateLanguage B ht).Sorts :=
  coordinateSort B ht (chartCoordinate B ht F i k)

private def formulaConjoin {L : Language.{u}} {n : ℕ} {ctx : Fin n → L.Sorts} :
    List (Formula L ctx) → Formula L ctx
  | [] => .truth
  | f :: fs => .conj f (formulaConjoin fs)

private theorem formulaConjoin_eval {L : Language.{u}} {V : Type z} (C : Structure L V)
    {n : ℕ} {ctx : Fin n → L.Sorts} (xs : Fin n → V) (fs : List (Formula L ctx)) :
    (formulaConjoin fs).eval C xs ↔ ∀ f ∈ fs, f.eval C xs := by
  induction fs with
  | nil => simp [formulaConjoin,Formula.eval]
  | cons f fs ih => simp [formulaConjoin,Formula.eval,ih]

private def formulaAll {L : Language.{u}} {n r : ℕ} {ctx : Fin n → L.Sorts}
    (f : Fin r → Formula L ctx) : Formula L ctx := formulaConjoin (List.ofFn f)

private theorem formulaAll_eval {L : Language.{u}} {V : Type z} (C : Structure L V)
    {n r : ℕ} {ctx : Fin n → L.Sorts} (xs : Fin n → V) (f : Fin r → Formula L ctx) :
    (formulaAll f).eval C xs ↔ ∀ k, (f k).eval C xs := by
  rw [formulaAll,formulaConjoin_eval]
  simp

def chartPairFormula (i : B.Sorts) (k l : Fin (chartArity F i)) :
    QuotientPairQF.Formula (cloneSource B) (chartSymbol F i k).val (chartSymbol F i l).val →
      Formula (CoordinateLanguage B ht) (chartSort B ht F i)
  | .falsum => .neg .truth
  | .truth => .truth
  | .equal => by
      classical
      exact if h : chartSort B ht F i k = chartSort B ht F i l then
        .equal ⟨k,.id _⟩ ⟨l,(Term.id _).retype rfl h.symm⟩ else .neg .truth
  | .named R => .binary (namedBinary B ht (chartCoordinate B ht F i k)
      (chartCoordinate B ht F i l) R) ⟨k,.id _⟩ ⟨l,.id _⟩
  | .neg f => .neg (chartPairFormula i k l f)
  | .conj f g => .conj (chartPairFormula i k l f) (chartPairFormula i k l g)
  | .disj f g => .neg (.conj (.neg (chartPairFormula i k l f)) (.neg (chartPairFormula i k l g)))

theorem chartPairFormula_eval (i : B.Sorts) {V : Type z}
    (C : Structure (CoordinateLanguage B ht) V) (xs : Fin (chartArity F i) → V)
    (sorted : ∀ k, C.sort (xs k) = chartSort B ht F i k)
    (k l : Fin (chartArity F i))
    (test : QuotientPairQF.Formula (cloneSource B) (chartSymbol F i k).val (chartSymbol F i l).val) :
    (chartPairFormula B ht F i k l test).eval C xs ↔
      pairEval B ht (chartCoordinate B ht F i k) (chartCoordinate B ht F i l)
        C (xs k) (xs l) test := by
  classical
  induction test with
  | falsum => simp [chartPairFormula,Formula.eval,pairEval]
  | truth => exact Iff.rfl
  | equal =>
      by_cases hs : chartSort B ht F i k = chartSort B ht F i l
      · simp [chartPairFormula,hs,Formula.eval,CoordinateTerm.eval,Term.eval_retype,Term.eval,pairEval]
      · have hne : xs k ≠ xs l := by
          intro h
          exact hs ((sorted k).symm.trans ((congrArg C.sort h).trans (sorted l)))
        simp [chartPairFormula,hs,Formula.eval,pairEval,hne]
  | named R => simp [chartPairFormula,Formula.eval,CoordinateTerm.eval,Term.eval,pairEval]
  | neg f ih => exact not_congr ih
  | conj f g hf hg => exact and_congr hf hg
  | disj f g hf hg =>
      simpa only [chartPairFormula,Formula.eval,not_and_or,not_not,pairEval] using or_congr hf hg

def tupleDomain (i : B.Sorts) : Formula (CoordinateLanguage B ht) (chartSort B ht F i) :=
  formulaAll fun k => formulaAll fun l => chartPairFormula B ht F i k l
    (QuotientPairQF.membershipFormula (cloneSource B) (chartSymbol F i k).val
      (chartSymbol F i l).val (Sum.inr ⟨rfl⟩))

theorem tupleDomain_eval (i : B.Sorts) {V : Type z}
    (C : Structure (CoordinateLanguage B ht) V) (xs : Fin (chartArity F i) → V)
    (sorted : ∀ k, C.sort (xs k) = chartSort B ht F i k) :
    (tupleDomain B ht F i).eval C xs ↔ ∀ k l,
      pairEval B ht (chartCoordinate B ht F i k) (chartCoordinate B ht F i l) C (xs k) (xs l)
        (QuotientPairQF.membershipFormula (cloneSource B) (chartSymbol F i k).val
          (chartSymbol F i l).val (Sum.inr ⟨rfl⟩)) := by
  simp only [tupleDomain,formulaAll_eval,chartPairFormula_eval B ht F i C xs sorted]

abbrev tupleScheme : RootScheme (CoordinateLanguage B ht) where
  Tag := ULift.{max v w} B.Sorts
  finiteTag := by letI := B.source.finiteSort; infer_instance
  arity i := chartArity F i.down
  coordinateSort i := chartSort B ht F i.down
  delta i := tupleDomain B ht F i.down

theorem tupleScheme_positive (i : (tupleScheme B ht F).Tag) :
    0 < (tupleScheme B ht F).arity i := chartArity_pos F i.down

def tupleNodes (i : B.Sorts) (q : (F i).Tuple) : Fin (chartArity F i) → Values B :=
  fun k => coordinateNode B ht (chartSymbol F i k) (q ((chartEnumeration F i).symm k))

theorem tupleNodes_sorted (i : B.Sorts) (q : (F i).Tuple) (k : Fin (chartArity F i)) :
    (CoordinateTarget B ht).sort (tupleNodes B ht F i q k) = chartSort B ht F i k := rfl

theorem tupleDomain_target_eval (i : B.Sorts) (q : (F i).Tuple) :
    (tupleDomain B ht F i).eval (CoordinateTarget B ht) (tupleNodes B ht F i q) ↔
      (F i).Compatible q := by
  rw [tupleDomain_eval B ht F i _ _ (tupleNodes_sorted B ht F i q)]
  have hp (k l : Fin (chartArity F i)) :
      pairEval B ht (chartCoordinate B ht F i k) (chartCoordinate B ht F i l)
        (CoordinateTarget B ht) (tupleNodes B ht F i q k) (tupleNodes B ht F i q l)
        (QuotientPairQF.membershipFormula (cloneSource B) (chartSymbol F i k).val
          (chartSymbol F i l).val (Sum.inr ⟨rfl⟩)) ↔
      Sum.inr ⟨rfl⟩ ∈ CCO.TransitionClosure.originalTypedQuotientPairSpectrum (cloneSource B)
        (chartSymbol F i k).val (chartSymbol F i l).val
        (q ((chartEnumeration F i).symm k)) (q ((chartEnumeration F i).symm l)) :=
    (pairEval_target B ht _ _ _ _ _).trans
      (QuotientPairQF.membershipFormula_eval (cloneSource B) (cloneHomogeneous B) _ _ _ _ _)
  constructor
  · intro h a b
    obtain ⟨k,rfl⟩ := (chartEnumeration F i).symm.surjective a
    obtain ⟨l,rfl⟩ := (chartEnumeration F i).symm.surjective b
    exact (hp k l).mp (h k l)
  · intro h k l
    exact (hp k l).mpr (h ((chartEnumeration F i).symm k) ((chartEnumeration F i).symm l))

/-- Actual owners become the literal ordered tuple of their fixed
selected quotient coordinates, with no quotient of tuples. -/
def ownerRoot (x : Sigma B.Point) : Root (CoordinateTarget B ht) (tupleScheme B ht F) where
  tag := ⟨x.1⟩
  coordinate := tupleNodes B ht F x.1 ((F x.1).ownerTuple x.2)
  sorted := tupleNodes_sorted B ht F x.1 ((F x.1).ownerTuple x.2)
  valid := (tupleDomain_target_eval B ht F x.1 _).mpr ((F x.1).ownerTuple_compatible x.2)

@[simp] theorem ownerRoot_tag (x : Sigma B.Point) : (ownerRoot B ht F x).tag = ⟨x.1⟩ := rfl

theorem ownerRoot_injective : Function.Injective (ownerRoot B ht F) := by
  rintro ⟨i,x⟩ ⟨j,y⟩ h
  have hij : i = j := congrArg (fun r => r.tag.down) h
  subst j
  have he : (F i).ownerTuple x = (F i).ownerTuple y := by
    funext a
    obtain ⟨k,rfl⟩ := (chartEnumeration F i).symm.surjective a
    have hc := congrArg (fun r : Root (CoordinateTarget B ht) (tupleScheme B ht F) =>
      (⟨r.tag,r.coordinate⟩ : (t : (tupleScheme B ht F).Tag) ×
        (Fin ((tupleScheme B ht F).arity t) → Values B))) h
    have hcoords := eq_of_heq (Sigma.mk.inj hc).2
    have ha := congrFun hcoords k
    apply namedNode_injective B (chartCoordinate B ht F i k)
    exact ha
  have hxy := (F i).ownerTuple_injective he
  cases hxy
  rfl

@[simp] theorem ownerRoot_coordinate (i : B.Sorts) (x : B.Point i)
    (k : Fin (chartArity F i)) :
    (ownerRoot B ht F ⟨i,x⟩).coordinate k =
      namedNode B (chartCoordinate B ht F i k)
        ((F i).ownerTuple x ((chartEnumeration F i).symm k)) := rfl

/-- The canonical owner action moves every marked coordinate by the
same actual imaginary action; no automorphism section is selected. -/
theorem ownerRoot_coordinate_smul (g : CCO.TerminalPowers.FullAut B.source)
    (i : B.Sorts) (x : B.Point i) (k : Fin (chartArity F i)) :
    ownerHiddenHom B ht g • (ownerRoot B ht F ⟨i,x⟩).coordinate k =
      (ownerRoot B ht F ⟨i,g • x⟩).coordinate k := rfl

/-- Every actual valid tuple is the tuple of one owner. Coordinate
decoding recovers existing quotient VALUES, never representatives. -/
theorem ownerRoot_surjective : Function.Surjective (ownerRoot B ht F) := by
  intro r
  rcases r with ⟨⟨i⟩,xs,hs,hv⟩
  have hnode (a : (F i).Index) :
      ∃ q : Quotient ((F i).symbol a).val.val,
        xs ((chartEnumeration F i) a) =
          namedNode B (namedCoordinateHF B ht i ((F i).symbol a)) q := by
    obtain ⟨k,rfl⟩ := (chartEnumeration F i).symm.surjective a
    rw [Equiv.apply_symm_apply]
    exact original_completed_hidden_carrier_exists (cloneSource B) (HF B) (cloneSAP B)
      (CCO.TerminalHiddenHN.NR2 (cloneSource B) (fullCovers B ht))
      (chartCoordinate B ht F i k) ⟨xs k,hs k⟩
  choose q hq using hnode
  have hcoords : tupleNodes B ht F i q = xs := by
    funext k
    have h := hq ((chartEnumeration F i).symm k)
    simpa only [tupleNodes, coordinateNode, chartCoordinate, chartSymbol, Equiv.apply_symm_apply] using h.symm
  have hvalid : (tupleDomain B ht F i).eval (CoordinateTarget B ht) (tupleNodes B ht F i q) := by
    rw [hcoords]
    exact hv
  obtain ⟨x,hx⟩ := (F i).compatible_realized ht q
    ((tupleDomain_target_eval B ht F i q).mp hvalid)
  refine ⟨⟨i,x⟩,?_⟩
  refine Root.ext_coordinates (r := ownerRoot B ht F ⟨i,x⟩)
    (s := ⟨⟨i⟩,xs,hs,hv⟩) rfl ?_
  intro k
  exact (congrFun (congrArg (tupleNodes B ht F i) hx) k).trans (congrFun hcoords k)

def ownerRootEquiv : Sigma B.Point ≃ Root (CoordinateTarget B ht) (tupleScheme B ht F) :=
  Equiv.ofBijective (ownerRoot B ht F) ⟨ownerRoot_injective B ht F,ownerRoot_surjective B ht F⟩

end
end CCO.APRamseyReadout
