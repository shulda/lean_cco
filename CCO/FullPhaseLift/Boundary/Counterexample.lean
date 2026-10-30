import CCO.FullPhaseLift.Boundary.Profiles
import CCO.FullPhaseLift.Full.ChosenPair
import CCO.FullPhaseLift.Full.ActualShadow
import CCO.FullPhaseLift.Boundary.OneColour
import CCO.FullPhaseLift.Canonical.Homogeneity
import CCO.FullPhaseLift.Full.ExpansionHomogeneity

/-! B048 C32: a literal full signed four-point diagram, with four genuine
complete induced old factors, has a strict realized canonical pair target
but NO full completion in the actual homogeneous K₄³-free model. -/

universe z
namespace CCO.FullPhaseLift.Boundary.HypergraphClass
open Canonical Full
noncomputable section

abbrev workingTable := expand modelTable
abbrev forbiddenTable := expand (table (completeTriple (Fin 4)))
abbrev tripleTable := expand (table (completeTriple (Fin 3)))

def forbiddenDiagram : Partial (expansion signature) (Fin 4) :=
  fun r xs => some (forbiddenTable r xs)

def factorInclusion (i : Fin 4) : Fin 3 ↪ Fin 4 :=
  (finSuccAboveEquiv i).toEmbedding.trans ⟨Subtype.val,Subtype.val_injective⟩

theorem factorInclusion_range (i x : Fin 4) (hx : x ≠ i) :
    ∃ j, factorInclusion i j = x := by
  refine ⟨(finSuccAboveEquiv i).symm ⟨x,hx⟩,?_⟩
  exact congrArg Subtype.val ((finSuccAboveEquiv i).apply_symm_apply ⟨x,hx⟩)

def oldFactorEmbedding (i : Fin 4) :
    Embedding (table (completeTriple (Fin 3))) (table (completeTriple (Fin 4))) :=
  relationEmbedding _ _ (factorInclusion i) (factorInclusion i).injective (by
    intro x y z
    simp only [completeTriple,ne_eq,(factorInclusion i).injective.eq_iff])

def frozenTriple (i : Fin 4) : FrozenFactor workingTable forbiddenDiagram where
  size := 3
  inclusion := factorInclusion i
  table := tripleTable
  age := by
    obtain ⟨e⟩ := valid_embeds (table (completeTriple (Fin 3))) complete_three_valid
    exact ⟨expandEmbedding e⟩
  agrees r xs := congrArg some (embedding_read (expandEmbedding (oldFactorEmbedding i)) r xs)

private theorem support_of_small_domain {V : Type} {n : ℕ} (hn : n ≤ 2)
    (xs : Fin n → V) : SmallSupport xs :=
  (smallSupport_fin hn (id : Fin n → Fin n)).comp xs

set_option maxRecDepth 8192 in
theorem all_higher_frozen : HigherCovered frozenTriple := by
  intro r xs b _ hs
  cases r using Fin.addCases with
  | left a =>
    have ha : (expansion signature).arity (Fin.castAdd _ a) = 3 := by simp [expansion]
    obtain ⟨i,hi⟩ := every_tuple_in_factor (xs ∘ Fin.cast ha.symm)
    refine ⟨i,?_⟩
    rintro x ⟨j,rfl⟩
    apply factorInclusion_range
    have hh := hi (Fin.cast ha j)
    have he : Fin.cast ha.symm (Fin.cast ha j) = j := Fin.ext rfl
    simpa only [Function.comp_apply,he] using hh
  | right b =>
    cases b using Fin.addCases with
    | left a =>
      have ha : (expansion signature).arity (Fin.natAdd signature.size (Fin.castAdd _ a)) ≤ 2 := by
        simp [expansion]
      exact (hs (support_of_small_domain ha xs)).elim
    | right a =>
      have ha : (expansion signature).arity (Fin.natAdd signature.size (Fin.natAdd _ a)) ≤ 2 := by
        simp [expansion]
      exact (hs (support_of_small_domain ha xs)).elim

/-- The four-point EMPTY higher structure is an actual old age object.
It supplies the chosen pair diagram while all specified higher triples
of the forbidden partial structure remain in the four frozen factors. -/
theorem strict_pair_target :
    ∃ p : Fin 4 ↪ Model, LowRealizes workingTable forbiddenDiagram p := by
  obtain ⟨e⟩ := valid_embeds (table (fun (_ _ _ : Fin 4) => False)) (empty_valid _)
  let p : Fin 4 ↪ Model := ⟨e.point,e.injective⟩
  refine ⟨p,?_⟩
  intro r xs b hs hd
  have hb : forbiddenTable r xs = b := Option.some.inj hd
  exact (expand_low (table (completeTriple (Fin 4))) modelTable
    (complete_noRepeats _) model_noRepeats p r xs hs).trans hb

theorem working_separates : SeparatesPoints workingTable := by
  intro x y hxy
  obtain ⟨r,slots,hr,hd⟩ := expand_separates modelTable x y hxy
  refine ⟨r,slots,?_,hd⟩
  have h : twoPoint x y = ![x,y] := by
    funext i
    fin_cases i <;> rfl
  rw [h]
  exact hr

/-- Every attempted full completion, not merely a chosen finite target,
would embed the complete four-point hypergraph into the K₄³-free model. -/
theorem no_full_completion (q : Fin 4 ↪ Model)
    (hq : Realizes workingTable forbiddenDiagram q) : False := by
  classical
  apply model_k4Free q q.injective
  intro i j k hij hik hjk
  let xs := tuple3 i j k
  have h := hq (oldSymbol signature 0)
    (xs ∘ Fin.cast (oldSymbol_arity signature 0)) _ rfl
  change expand modelTable (oldSymbol signature 0)
      (q ∘ (xs ∘ Fin.cast (oldSymbol_arity signature 0))) =
    expand (table (completeTriple (Fin 4))) (oldSymbol signature 0)
      (xs ∘ Fin.cast (oldSymbol_arity signature 0)) at h
  rw [← Function.comp_assoc,expand_old,expand_old] at h
  change relation modelTable (q i) (q j) (q k)
  unfold relation
  rw [← tuple3_comp]
  change modelTable 0 (q ∘ xs) = true
  rw [h]
  change decide (completeTriple (Fin 4) i j k) = true
  exact decide_eq_true ⟨hij,hik,hjk⟩

/-- Counterexample to the internal strict-target specialization of A03.
The source-facing raw shadow form also fails via its complete-shadow
specialization; no cycle or negative-menu normalization is assumed here. -/
theorem no_strict_support_normal : ¬StrictSupportNormal workingTable := by
  intro normal
  obtain ⟨p,hp⟩ := strict_pair_target
  obtain ⟨q,hq,_,_⟩ := lift_chosen_pairs workingTable working_separates normal
    4 forbiddenDiagram 4 frozenTriple all_higher_frozen p hp
  exact no_full_completion q hq

def workingSymmetry : SameSortSymmetric workingTable :=
  sameSortSymmetric_expand (sameSortSymmetric_of_noRepeats modelTable model_noRepeats)

/-- The ACTUAL source A03 with its signed local shadow refinement and
cycle certificates fails, not just an unexplained internal replacement. -/
theorem no_raw_support_normal : ¬Shadow.SupportNormal workingTable workingSymmetry := by
  intro h
  exact no_strict_support_normal (Shadow.SupportNormal.to_strict workingTable workingSymmetry h)

theorem working_full_homogeneous : (toRelational workingTable).Homogeneous :=
  expand_homogeneous modelTable
    (homogeneous_of_firstOrder (inferInstance : signature.firstOrder.Structure Model) model_homogeneous)

theorem working_unary_equal (x y : Model) :
    unaryProfile workingTable x = unaryProfile workingTable y := by
  apply expand_profile_eq
  · exact (unary_zero modelTable model_noRepeats x).trans (unary_zero modelTable model_noRepeats y).symm
  · intro _ _
    exact ⟨fun _ => rfl,fun _ => rfl⟩

theorem working_pair_equal {x y a b : Model} (hxy : x ≠ y) (hab : a ≠ b) :
    pairProfile workingTable x y = pairProfile workingTable a b := by
  apply expand_profile_eq
  · exact (pair_zero modelTable model_noRepeats x y).trans (pair_zero modelTable model_noRepeats a b).symm
  · intro i j
    fin_cases i <;> fin_cases j <;> simp [hxy,hab,Ne.symm hxy,Ne.symm hab]

local instance : Subsingleton (UnaryName workingTable) where
  allEq i j := by
    apply Subtype.ext
    obtain ⟨x,hx⟩ := i.property
    obtain ⟨y,hy⟩ := j.property
    exact hx.symm.trans ((working_unary_equal x y).trans hy)

local instance (i j : UnaryName workingTable) : Subsingleton (PairAtom workingTable i j) where
  allEq a b := by
    apply Subtype.ext
    obtain ⟨x,y,hxy,ha⟩ := a.property
    obtain ⟨u,v,huv,hb⟩ := b.property
    exact ha.symm.trans ((working_pair_equal hxy huv).trans hb)

local instance : Infinite (Sigma (Carrier workingTable)) := by
  letI : Infinite Model := model_infinite
  exact Infinite.of_injective (pack workingTable) (pack workingTable).injective

abbrev workingSource := source workingTable workingSymmetry

local instance : ∀ i j : UnaryName workingTable, Subsingleton (workingSource.Atom i j) :=
  fun i j => inferInstanceAs (Subsingleton (PairAtom workingTable i j))

theorem working_pair_ageSAP : CCO.AgeSAP workingSource := OneColour.ageSAP workingSource

theorem working_pair_cco : SemanticCCO.{0,0,z,0} workingSource := OneColour.semanticCCO workingSource

/-- C32 in one actual model: countable full homogeneity and the canonical
pair SAP/CCO premises hold, while the literal higher-support interface
fails at four complete induced three-point factors. -/
theorem full_language_boundary :
    Countable Model ∧ Infinite Model ∧ (toRelational workingTable).Homogeneous ∧
      CCO.AgeSAP workingSource ∧ SemanticCCO.{0,0,z,0} workingSource ∧
      ¬Shadow.SupportNormal workingTable workingSymmetry :=
  ⟨inferInstance,model_infinite,working_full_homogeneous,working_pair_ageSAP,
    working_pair_cco,no_raw_support_normal⟩

end
end CCO.FullPhaseLift.Boundary.HypergraphClass
