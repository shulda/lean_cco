import CCO.PairSafeSplit.Strong.NoOrthogonal
import CCO.ParityHasse.Relative.Separation

/-! B047 C57. The only dangerous FULL-to-STRONG transfer case is excluded
at the ORIGINAL SAP source, using real identity as the closure base. -/

universe u v w t
namespace CCO.PairSafeSplit.Strong
open ParityHasse.Original
open ParityHasse.Relative
variable {ι : Type u} {X : ι → Type v} (S : AtomicSource.{u,v,w} ι X)
variable {G : Type t} [Group G] [∀ i, MulAction G (X i)]
variable (H : HomogeneousSource S G) (sap : AgeSAP S)
variable (cco : SemanticCCO.{u,v,max u v,w} S)

include H sap cco in
/-- A nontrivial reflexive FULL exact relation and a nontrivial FULL exact
equivalence have a common real diversity pair. No STRONG saturation is used. -/
theorem reflexive_exact_meets_gate {i : ι} (D : X i → X i → Prop)
    (hD : Exact S D) (hRef : ∀ x, D x x) (hDiv : ∃ x y, D x y ∧ x ≠ y)
    (K : ColourEq S i) (hK : Exact S K) (hne : K ≠ ⊥) :
    ∃ x y, D x y ∧ K x y ∧ x ≠ y := by
  classical
  by_contra hn
  have hDK : (fun x y => D x y ∧ K x y) = Eq := by
    funext x y
    apply propext
    constructor
    · intro h
      exact Classical.byContradiction (fun hne => hn ⟨x,y,h.1,h.2,hne⟩)
    · rintro rfl
      exact ⟨hRef x,K.val.refl x⟩
  let CD : ColourEq S i := closureEq S H ⊥ D (hD.colourInvariant S H)
    (identity_bisaturated S D)
  let CK : ColourEq S i := closureEq S H ⊥ K K.2 (identity_bisaturated S K)
  have sep := identity_separation S H cco D K hD hK hRef K.val.refl hDK
  have meet : CD ⊓ CK = ⊥ := by
    apply ColourEq.ext S i
    intro x y
    exact (congrFun (congrFun sep x) y).to_iff
  have cd : CD ≠ ⊥ := by
    intro he
    obtain ⟨x,y,hxy,hne⟩ := hDiv
    have hh : CD x y := ⟨1,by rw [power_one _ _ (identity_bisaturated S D)]; exact hxy⟩
    rw [he] at hh
    exact hne hh
  have ck : CK ≠ ⊥ := by
    intro he
    obtain ⟨x,y,hxy,hne⟩ := exists_distinct_related S K hne
    have hh : CK x y := ⟨1,by rw [power_one _ _ (identity_bisaturated S K)]; exact hxy⟩
    rw [he] at hh
    exact hne hh
  exact nontrivial_equivalences_meet S H sap CD CK cd ck meet

include H in
theorem exact_diagonal_uniform {i : ι} (D : X i → X i → Prop)
    (hD : Exact S D) {x : X i} (hx : D x x) : ∀ y, D y y := by
  intro y
  apply (hD.colourInvariant S H x x y y ?_).mp hx
  exact ((S.colour_none_iff x x).mpr rfl).trans ((S.colour_none_iff y y).mpr rfl).symm

include H sap cco in
/-- In particular, a nonempty diversity domain disjoint from gate diversity
cannot also contain a hidden RAW identity output. -/
theorem no_extra_identity {i : ι} (D : X i → X i → Prop)
    (hD : Exact S D) (hDiv : ∃ x y, D x y ∧ x ≠ y)
    (K : ColourEq S i) (hK : Exact S K) (hne : K ≠ ⊥)
    (hMeet : ∀ x y, D x y → K x y → x = y) : ∀ x, ¬ D x x := by
  intro x hx
  obtain ⟨a,b,hab,hK,hne⟩ := reflexive_exact_meets_gate S H sap cco D hD
    (exact_diagonal_uniform S H D hD hx) hDiv K hK hne
  exact hne (hMeet a b hab hK)

end CCO.PairSafeSplit.Strong
