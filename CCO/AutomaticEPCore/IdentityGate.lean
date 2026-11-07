import CCO.AutomaticEPCore.FunctionalOriginal
import CCO.AutomaticEPCore.TerminalLoopless
import CCO.ExactEPGeometry.CertifiedOriginalKernel
import CCO.ExactEPGeometry.ExactEquivalenceComplete

/-! B063 C32–C38: an ACTUAL original identity gate supplies a genuine
functional involution and a least positive FULL-EXACT equivalence. This
least relation is not a least arbitrary invariant or a finite-packet hull.
The selected phase may have another odd arrow: no character-one assertion
about the initially stored GateChoice.c is made by these lemmas. -/

namespace CCO.AutomaticEPCore

open CCO.ParityHasse.Original
open CCO.ExactEPGeometry
open CCO.ExactEPGeometry.OldGateMaximality
open CCO.APCharacter.Towers

universe u v w r
noncomputable section

variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)
variable {G : Type r} [Group G] [∀ j : ι, MulAction G (X j)]
variable (H : HomogeneousSource S G) {i : ι}

/-- C33: with literal even equivalence equal to real identity, the actual
symmetric nonempty original atom has square exactly real identity. -/
theorem identity_even_atom_square (c : S.Atom i i)
    (hEven : evenColourEq S H c = ⊥) (x y : X i) :
    (∃ z, S.atomRel c x z ∧ S.atomRel c z y) ↔ x = y := by
  constructor
  · rintro ⟨z,hxz,hzy⟩
    have he : evenColourEq S H c x y :=
      ⟨2,even_two,z,hxz,y,hzy,rfl⟩
    rw [hEven] at he
    exact he
  · rintro rfl
    have invariant : ColourInvariant S i (S.atomRel c) := by
      intro a b a' b' hcol
      change S.colour a b = some c ↔ S.colour a' b' = some c
      rw [hcol]
    obtain ⟨z,hxz⟩ := invariant_nonempty_serial S H invariant (S.realized c) x
    refine ⟨z,hxz,?_⟩
    exact colourInvariant_symmetric S invariant x z hxz

/-- C34: the real functional permutation is CONSTRUCTED from the actual
unique atom neighbour. It belongs to the SAME original functional group. -/
theorem identity_even_atom_functional (c : S.Atom i i)
    (hEven : evenColourEq S H c = ⊥) :
    ∃ h : OriginalFunctionalGroup G (X i), h ≠ 1 ∧
      ∀ x y : X i, S.atomRel c x y ↔ h.val x = y := by
  classical
  have invariant : ColourInvariant S i (S.atomRel c) := by
    intro a b a' b' hcol
    change S.colour a b = some c ↔ S.colour a' b' = some c
    rw [hcol]
  have serial := invariant_nonempty_serial S H invariant (S.realized c)
  let f : X i → X i := fun x => Classical.choose (serial x)
  have hf (x : X i) : S.atomRel c x (f x) := Classical.choose_spec (serial x)
  have unique (x y : X i) (hxy : S.atomRel c x y) : f x = y :=
    (identity_even_atom_square S H c hEven (f x) y).mp
      ⟨x,colourInvariant_symmetric S invariant x (f x) (hf x),hxy⟩
  have involutive : Function.Involutive f := by
    intro x
    exact unique (f x) x (colourInvariant_symmetric S invariant x (f x) (hf x))
  let permutation : Equiv.Perm (X i) :=
    { toFun := f
      invFun := f
      left_inv := involutive
      right_inv := involutive }
  let h : OriginalFunctionalGroup G (X i) :=
    ⟨permutation,by
      intro g x
      apply unique
      change S.colour (g • x) (g • f x) = some c
      rw [S.colourInvariant_of_homogeneous H]
      exact hf x⟩
  refine ⟨h,?_,?_⟩
  · intro he
    obtain ⟨x⟩ := S.nonemptySort i
    have hfx : f x = x := congrArg (fun h : OriginalFunctionalGroup G (X i) => h.val x) he
    exact S.atomRel_ne (hf x) (by rw [hfx])
  · intro x y
    constructor
    · exact unique x y
    · intro he
      change f x = y at he
      rw [← he]
      exact hf x

/-- C32–C35 local original-gate theorem. The maximality quantifier is over
ALL FULL-EXACT original equivalences. U need not itself be exact. -/
theorem identity_maximal_gate_functional
    (c : S.Atom i i) (Y : ExactEq S i) (U : ColourEq S i)
    (hY : Y.val = evenColourEq S H c)
    (hU : U = connectivityColourEq S H c)
    (maximal : Maximal (OriginalGateCandidate S i Y U) (⊥ : ExactEq S i)) :
    ∃ h : OriginalFunctionalGroup G (X i), h ≠ 1 ∧
      (∀ x y : X i, S.atomRel c x y ↔ h.val x = y) ∧
      ∀ E : ExactEq S i, ⊥ < E → ∀ x : X i, E x (h.val x) := by
  have hYbot : Y = (⊥ : ExactEq S i) := le_antisymm maximal.1.1 bot_le
  have hEven : evenColourEq S H c = ⊥ := by
    rw [← hY,hYbot]
    rfl
  obtain ⟨h,hne,hGraph⟩ := identity_even_atom_functional S H c hEven
  have bipartite := original_functional_atom_bipartite S H h hne c hGraph
  have noOdd := bipartite_graph_no_odd_power (atomGraph S c) bipartite
  have cover : Y.val ⋖ U := by
    rw [hY,hU]
    exact parity_seed_cover S H c noOdd
  refine ⟨h,hne,hGraph,?_⟩
  intro E hE x
  have hCases : E.val ⊓ U = Y.val ∨ E.val ⊓ U = U :=
    cover.eq_or_eq (by rw [hYbot]; exact bot_le) inf_le_right
  have hUleE : U ≤ E.val := by
    rcases hCases with hComplement | hContained
    · have candidate : OriginalGateCandidate S i Y U E := by
        refine ⟨?_,hComplement⟩
        rw [hYbot]
        exact bot_le
      exact False.elim (hE.not_ge (maximal.2 candidate bot_le))
    · rw [← hContained]
      exact inf_le_left
  apply hUleE
  rw [hU]
  exact ⟨1,(relPow_one _ _ _).mpr ((hGraph x (h.val x)).mpr rfl)⟩

/-- C36's ONE finite FULL-EXACT meet, defined using the proved actual
complete lattice. This definition is meaningful before an identity step;
its positivity is proved only after such a genuine step supplies h. -/
def leastPositiveExact (A : CurrentSource.{u,v,w,r}) (i : A.Sorts) :
    ExactEq A.source i := by
  letI := ExactEq.completeLattice A.source A.homogeneous A.cco i
  exact sInf {E : ExactEq A.source i | ⊥ < E}

/-- The least positive-exact meet is below every positive exact relation,
not asserted below arbitrary positive invariant relations. -/
theorem leastPositiveExact_le (A : CurrentSource.{u,v,w,r}) (i : A.Sorts)
    (E : ExactEq A.source i) (hE : ⊥ < E) : leastPositiveExact A i ≤ E := by
  let := ExactEq.completeLattice A.source A.homogeneous A.cco i
  exact sInf_le hE

/-- The finite complete-lattice meet is the literal pointwise intersection
of ALL positive FULL-EXACT original relations, including a possibly Top F. -/
theorem leastPositiveExact_iff (A : CurrentSource.{u,v,w,r}) (i : A.Sorts)
    (x y : A.Point i) :
    leastPositiveExact A i x y ↔ ∀ E : ExactEq A.source i, ⊥ < E → E x y := by
  classical
  let := ExactEq.completeLattice A.source A.homogeneous A.cco i
  let : Fintype (ExactEq A.source i) := Fintype.ofFinite _
  let family : List (ExactEq A.source i) :=
    (Finset.univ.filter (fun E : ExactEq A.source i => ⊥ < E)).toList
  have hMem (E : ExactEq A.source i) : E ∈ family ↔ ⊥ < E := by simp [family]
  have hEq : leastPositiveExact A i = originalExactGateMeet A.source i family := by
    apply le_antisymm
    · apply (originalExactGateMeet_greatest A.source i family _).mpr
      intro E hE
      exact leastPositiveExact_le A i E ((hMem E).mp hE)
    · change originalExactGateMeet A.source i family ≤ sInf _
      apply le_sInf
      intro E hE
      exact originalExactGateMeet_le_member A.source i family E ((hMem E).mpr hE)
  rw [hEq,originalExactGateMeet_iff]
  constructor
  · intro h E hE
    exact h E ((hMem E).mpr hE)
  · intro h E hE
    exact h E ((hMem E).mp hE)

/-- EVERY functional graph lying in every positive exact equivalence lies
in the SAME F, not just the initial positivity witness. -/
theorem functional_graph_in_leastPositiveExact
    (A : CurrentSource.{u,v,w,r}) (i : A.Sorts)
    (h : OriginalFunctionalGroup A.G (A.Point i))
    (hInside : ∀ E : ExactEq A.source i, ⊥ < E → ∀ x, E x (h.val x)) :
    ∀ x, leastPositiveExact A i x (h.val x) := by
  intro x
  exact (leastPositiveExact_iff A i x (h.val x)).mpr (fun E hE => hInside E hE x)

/-- C36 positivity is proved from ONE actual nonidentity functional graph,
without replacing the exact meet by an arbitrary invariant equivalence. -/
theorem leastPositiveExact_pos_of_functional
    (A : CurrentSource.{u,v,w,r}) (i : A.Sorts)
    (h : OriginalFunctionalGroup A.G (A.Point i)) (hne : h ≠ 1)
    (hInside : ∀ E : ExactEq A.source i, ⊥ < E → ∀ x, E x (h.val x)) :
    (⊥ : ExactEq A.source i) < leastPositiveExact A i := by
  apply bot_lt_iff_ne_bot.mpr
  intro hBot
  obtain ⟨x⟩ := A.source.nonemptySort i
  have hFx := functional_graph_in_leastPositiveExact A i h hInside x
  rw [hBot] at hFx
  exact original_functional_no_fixed A.source A.homogeneous h hne x hFx.symm

/-- C37's functional subgroup uses the actual SAME original group and the
literal original pair relation of F. No quotient-section action is used. -/
def functionalSubgroupInside (F : ExactEq S i) :
    Subgroup (OriginalFunctionalGroup G (X i)) where
  carrier := {h | ∀ x, F x (h.val x)}
  one_mem' := fun x => F.val.val.refl x
  mul_mem' := by
    intro h k hh hk x
    exact F.val.val.trans (hk x) (hh (k.val x))
  inv_mem' := by
    intro h hh x
    have hx := hh (h.val.symm x)
    have hfx : F (h.val.symm x) x := by simpa only [Equiv.apply_symm_apply] using hx
    exact F.val.val.symm hfx

/-- Normality is justified by the proved original functional group being
abelian, not by a presumed automorphism action on a fixed marking. -/
theorem functionalSubgroupInside_normal (H : HomogeneousSource S G) (F : ExactEq S i) :
    (functionalSubgroupInside (G := G) S F).Normal := by
  let := originalFunctionalCommGroup S H (i := i)
  infer_instance

/-- A supplied actual nonidentity member makes this genuine subgroup
nontrivial; later identity steps can supply other members in the same F. -/
theorem functionalSubgroupInside_nontrivial (F : ExactEq S i)
    (h : OriginalFunctionalGroup G (X i)) (hne : h ≠ 1)
    (hF : ∀ x, F x (h.val x)) :
    Nontrivial (functionalSubgroupInside (G := G) S F) := by
  refine ⟨⟨⟨h,hF⟩,1,?_⟩⟩
  intro he
  exact hne (congrArg Subtype.val he)

/-- C38: every actual original FULL-EXACT gate is identity or contains the
same least positive exact meet. This does not quantify over nonexact gates. -/
theorem original_gate_identity_or_leastPositiveExact
    (A : CurrentSource.{u,v,w,r}) (i : A.Sorts) (E : ExactEq A.source i) :
    E = ⊥ ∨ leastPositiveExact A i ≤ E := by
  by_cases hE : E = ⊥
  · exact Or.inl hE
  · exact Or.inr (leastPositiveExact_le A i E (bot_lt_iff_ne_bot.mpr hE))

/-- The exact source-parent old pivot retained by a certified step, moved
ONLY by equality of the unique original sort to the fixed base carrier. -/
def certifiedStepOriginalPivot
    (A : CurrentSource.{u,v,w,r}) (base : A.Sorts)
    (hOne : ∀ i : A.Sorts, base = i)
    {s next : CertifiedGateTower.ExactPrefix A}
    (step : CertifiedGateTower.Step s next) : A.source.Atom base base := by
  let choice : CertifiedGateTower.GateChoice s := Classical.choose step
  have hb := hOne (s.reduct.parent choice.p)
  cases hb
  exact s.reduct.atom choice.p choice.p choice.c

/-- Actual C32–C36 source discharge: the witness comes from the literal
GateChoice stored by this step and its original maximal lift. The result
asserts no character value for choice.c; the phase may select another odd
arrow, which must be handled from its own actual `detects` certificate. -/
theorem certified_identity_step_functional
    (A : CurrentSource.{u,v,w,r}) (base : A.Sorts)
    (hOne : ∀ i : A.Sorts, base = i)
    {s next : CertifiedGateTower.ExactPrefix A}
    (step : CertifiedGateTower.Step s next)
    (identityGate : certifiedStepOriginalGate A base hOne step = ⊥) :
    ∃ h : OriginalFunctionalGroup A.G (A.Point base), h ≠ 1 ∧
      (∀ x y, A.source.atomRel (certifiedStepOriginalPivot A base hOne step) x y ↔ h.val x = y) ∧
      (∀ E : ExactEq A.source base, ⊥ < E → ∀ x, E x (h.val x)) ∧
      (∀ x, leastPositiveExact A base x (h.val x)) ∧
      (⊥ : ExactEq A.source base) < leastPositiveExact A base := by
  classical
  let choice : CertifiedGateTower.GateChoice s := Classical.choose step
  have hb := hOne (s.reduct.parent choice.p)
  cases hb
  have hGate : PrefixExactLargestLift.largest A s.current s.reduct
      s.transport s.product choice.p
      (⟨choice.M.kernel,choice.M.maximal.1.1⟩ : ExactEq s.current.source choice.p) = ⊥ := by
    exact identityGate
  have hMax : Maximal
      (OriginalGateCandidate A.source (s.reduct.parent choice.p) choice.Yold choice.Uold)
      (⊥ : ExactEq A.source (s.reduct.parent choice.p)) := by
    rw [← hGate]
    exact choice.maximal_old
  obtain ⟨h,hne,hGraph,hInside⟩ := identity_maximal_gate_functional
    A.source A.homogeneous (s.reduct.atom choice.p choice.p choice.c)
    choice.Yold choice.Uold choice.old_even choice.old_connectivity hMax
  exact ⟨h,hne,hGraph,hInside,functional_graph_in_leastPositiveExact A _ h hInside,
    leastPositiveExact_pos_of_functional A _ h hne hInside⟩

/-- The canonical H_F is defined on the fixed ORIGINAL point carrier,
using the SAME least-positive-exact F for every identity-gate step. -/
def leastPositiveFunctionalSubgroup (A : CurrentSource.{u,v,w,r}) (i : A.Sorts) :
    Subgroup (OriginalFunctionalGroup A.G (A.Point i)) :=
  functionalSubgroupInside (G := A.G) A.source (leastPositiveExact A i)

/-- C36–C38 packaged for a TRUE certified identity step. Positivity,
leastness, subgroup nontriviality and normality are all discharged from
that actual step; no abstract positive-F provider remains. -/
theorem certified_identity_step_least_exact
    (A : CurrentSource.{u,v,w,r}) (base : A.Sorts)
    (hOne : ∀ i : A.Sorts, base = i)
    {s next : CertifiedGateTower.ExactPrefix A}
    (step : CertifiedGateTower.Step s next)
    (identityGate : certifiedStepOriginalGate A base hOne step = ⊥) :
    (⊥ : ExactEq A.source base) < leastPositiveExact A base ∧
      (∀ E : ExactEq A.source base, ⊥ < E → leastPositiveExact A base ≤ E) ∧
      Nontrivial (leastPositiveFunctionalSubgroup A base) ∧
      (leastPositiveFunctionalSubgroup A base).Normal := by
  obtain ⟨h,hne,_,_,hF,hPositive⟩ :=
    certified_identity_step_functional A base hOne step identityGate
  exact ⟨hPositive,leastPositiveExact_le A base,
    functionalSubgroupInside_nontrivial A.source (leastPositiveExact A base) h hne hF,
    functionalSubgroupInside_normal A.source A.homogeneous (leastPositiveExact A base)⟩

end
end CCO.AutomaticEPCore
