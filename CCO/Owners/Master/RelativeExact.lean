import CCO.Owners.Master.QuotientSources
import CCO.ExactCRT.SameSortDescent

/-! Actual relative exactness for every nested pair of original exact
equivalences. The kernel is represented by projected ORIGINAL RAW words
in the genuine complete canonical quotient language. -/

universe v w t
namespace CCO.Owners.Master

open RawExact ExactCRT CanonicalQuotients

variable {A : Type v} (S : AtomicSource.{0,v,w} Unit (fun _ => A))
variable {G : Type t} [Group G] [MulAction G A]
variable (H : HomogeneousSource S G) (cco : SemanticCCO.{0,v,v,w} S)
variable (E F : ExactEq S H cco ()) (hEF : E ≤ F)

local instance relativeInvariantE : Invariant G E.val := Product.exactInvariant S H cco E
local instance relativeInvariantF : Invariant G F.val := Product.exactInvariant S H cco F

theorem exists_relativeExact :
    ∃ D : NonemptyExact (quotientSource S H cco E) () (),
      GroupActions.kernel (Abstract.quotientMap hEF) =
        evaluate (quotientSource S H cco E) D.words := by
  let e := exactPresentation S E.property
  let f := exactPresentation S F.property
  have he : evaluate S e.words = E.val.r := exactPresentation_represents S E.property
  have hf : evaluate S f.words = F.val.r := exactPresentation_represents S F.property
  let π : ∀ _ : Unit, A → Quotient E.val := fun _ => Quotient.mk''
  have onto : ∀ i, Function.Surjective (π i) := fun _ => Quotient.mk''_surjective
  have equivπ : ∀ i (g : G) x, π i (g • x) = g • π i x := fun _ _ _ => rfl
  have hker : ∀ i, GroupActions.kernel (π i) = evaluate S e.words := by
    intro i
    rw [he]
    funext x y
    exact propext Quotient.eq
  have hSat : saturate (evaluate S e.words) (evaluate S f.words)
      (evaluate S e.words) = evaluate S f.words := by
    rw [he,hf]
    funext x y
    apply propext
    constructor
    · rintro ⟨b,⟨a,hxa,hab⟩,hby⟩
      exact F.val.trans (hEF hxa) (F.val.trans hab (hEF hby))
    · intro hxy
      exact ⟨y,⟨x,E.val.refl x,hxy⟩,E.val.refl y⟩
  let T := quotientSource S H cco E
  have orbit : ∀ {i j} (x : Quotient E.val) (y : Quotient E.val)
      (x' : Quotient E.val) (y' : Quotient E.val),
      T.colour (i := i) (j := j) x y = T.colour (i := i) (j := j) x' y' ↔
        GroupActions.orbital (G := G) x y x' y' :=
    quotientSource_colour_orbital S H cco E
  have hTI : ∀ word, word ∈ f.words → WordTI S (fun _ => evaluate S e.words) word := by
    intro word _
    exact oneSort_wordTI S H (fun _ => e) word
  let d := descendExact S T H cco π onto equivπ (fun _ => e) hker orbit f hSat hTI
  refine ⟨d,?_⟩
  rw [show evaluate T d.words = quotientRelation (π ()) (π ()) (evaluate S f.words) from
    descendExact_relation S T H cco π onto equivπ (fun _ => e) hker orbit f hSat hTI,hf]
  funext q r
  apply propext
  induction q using Quotient.inductionOn with
  | _ x =>
    induction r using Quotient.inductionOn with
    | _ y =>
      change (Quotient.mk F.val x = Quotient.mk F.val y) ↔
        ∃ a b, Quotient.mk E.val a = Quotient.mk E.val x ∧
          Quotient.mk E.val b = Quotient.mk E.val y ∧ F.val a b
      rw [Quotient.eq]
      constructor
      · intro hxy
        exact ⟨x,y,rfl,rfl,hxy⟩
      · rintro ⟨a,b,ha,hb,hab⟩
        exact F.val.trans (hEF (E.val.symm (Quotient.exact ha)))
          (F.val.trans hab (hEF (Quotient.exact hb)))

noncomputable def relativeExact : NonemptyExact (quotientSource S H cco E) () () :=
  Classical.choose (exists_relativeExact S H cco E F hEF)

theorem relativeExact_kernel :
    GroupActions.kernel (Abstract.quotientMap hEF) =
      evaluate (quotientSource S H cco E) (relativeExact S H cco E F hEF).words :=
  Classical.choose_spec (exists_relativeExact S H cco E F hEF)

end CCO.Owners.Master
