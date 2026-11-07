import CCO.TerminalHiddenHN.TermNormalizer
import CCO.TerminalHiddenHN.OrderedCodec

/-! Actual finite term normal forms for both faithful FullCode languages.
The forms are valid at EVERY hidden input. Adding a global order changes
no function graph, so validity is independent of the chosen host order. -/

universe u v w r z
namespace CCO.TerminalHiddenHN
open CCO.TypedOrbitFrames CCO.UnaryFreshFrames
noncomputable section

variable {ι : Type u} {X : ι → Type v} (S : AtomicSource.{u,v,w} ι X)
variable {G : Type r} [Group G] [∀ i, MulAction G (X i)]
variable (H : HomogeneousSource S G) (sap : AgeSAP S)
variable (hCover : ∀ i, OriginalAllFullCoversInfinite S (i := i))

def binaryNormalForms : CCO.FullCode.NormalForms
    (binaryLanguage (Sig S H sap hCover) (sig_binary S H sap hCover)) where
  count := termFunctionCount S H sap hCover
  form s t k := freshTermToFull (Lang S H sap hCover) (sig_binary S H sap hCover)
    (normalTerm S H sap hCover s t k)
  normalize q := normalTermIndex S H sap hCover
    (fullTermToFresh (Lang S H sap hCover) (sig_binary S H sap hCover) q)

theorem binary_actual_term_eval
    {s t : (Lang S H sap hCover).Sorts}
    (q : CCO.FullCode.Term
      (binaryLanguage (Sig S H sap hCover) (sig_binary S H sap hCover)) s t)
    (x y : Values S H) (hx : (Hidden S H sap hCover).sort x = s) :
    y ∈ q.eval
      (binaryStructure (Sig S H sap hCover) (sig_binary S H sap hCover)
        (Target S H sap hCover)) x ↔
      y = (Hidden S H sap hCover).eval
        (fullTermToFresh (Lang S H sap hCover) (sig_binary S H sap hCover) q) x := by
  have h := freshTermToFull_eval (Lang S H sap hCover) (sig_binary S H sap hCover)
    (Hidden S H sap hCover)
    (fullTermToFresh (Lang S H sap hCover) (sig_binary S H sap hCover) q) x y hx
  simpa only [freshTermToFull_fullTermToFresh] using h

theorem binaryNormalForms_valid :
    (binaryNormalForms S H sap hCover).Valid
      (binaryStructure (Sig S H sap hCover) (sig_binary S H sap hCover)
        (Target S H sap hCover)) := by
  intro s t q x hx
  apply Set.ext
  intro y
  change y ∈ q.eval
      (binaryStructure (Sig S H sap hCover) (sig_binary S H sap hCover)
        (Target S H sap hCover)) x ↔
    y ∈ (freshTermToFull (Lang S H sap hCover) (sig_binary S H sap hCover)
      (normalTerm S H sap hCover s t (normalTermIndex S H sap hCover
        (fullTermToFresh (Lang S H sap hCover) (sig_binary S H sap hCover) q)))).eval
      (binaryStructure (Sig S H sap hCover) (sig_binary S H sap hCover)
        (Target S H sap hCover)) x
  have hleft := binary_actual_term_eval S H sap hCover q x y hx
  have heq := normalTerm_eval S H sap hCover
    (fullTermToFresh (Lang S H sap hCover) (sig_binary S H sap hCover) q) x hx
  have hright := freshTermToFull_eval (Lang S H sap hCover) (sig_binary S H sap hCover)
    (Hidden S H sap hCover)
    (normalTerm S H sap hCover s t (normalTermIndex S H sap hCover
      (fullTermToFresh (Lang S H sap hCover) (sig_binary S H sap hCover) q))) x y hx
  exact hleft.trans ((Iff.of_eq (congrArg (fun a => y = a) heq)).trans hright.symm)

def orderedNormalForms : CCO.FullCode.NormalForms
    (orderedLanguage (Sig S H sap hCover) (sig_binary S H sap hCover)) where
  count := (binaryNormalForms S H sap hCover).count
  form s t k := baseTermToOrdered (Sig S H sap hCover) (sig_binary S H sap hCover)
    ((binaryNormalForms S H sap hCover).form s t k)
  normalize q := (binaryNormalForms S H sap hCover).normalize
    (orderedTermToBase (Sig S H sap hCover) (sig_binary S H sap hCover) q)

/-- Arbitrary global orders on arbitrary partial hosts introduce NO
new normal-form hypothesis and need not embed into a prechosen old order. -/
theorem orderedNormalForms_valid_of_binary
    {V : Type z} (C : CCO.UnarySupport.Structure (Sig S H sap hCover) V)
    [LinearOrder V]
    (hC : (binaryNormalForms S H sap hCover).Valid
      (binaryStructure (Sig S H sap hCover) (sig_binary S H sap hCover) C)) :
    (orderedNormalForms S H sap hCover).Valid
      (orderedStructure (Sig S H sap hCover) (sig_binary S H sap hCover) C) := by
  intro s t q x hx
  change q.eval
      (orderedStructure (Sig S H sap hCover) (sig_binary S H sap hCover) C) x =
    (baseTermToOrdered (Sig S H sap hCover) (sig_binary S H sap hCover)
      ((binaryNormalForms S H sap hCover).form s t
        ((binaryNormalForms S H sap hCover).normalize
          (orderedTermToBase (Sig S H sap hCover) (sig_binary S H sap hCover) q)))).eval
      (orderedStructure (Sig S H sap hCover) (sig_binary S H sap hCover) C) x
  rw [orderedTermToBase_eval,baseTermToOrdered_eval]
  exact hC s t
    (orderedTermToBase (Sig S H sap hCover) (sig_binary S H sap hCover) q) x hx

end
end CCO.TerminalHiddenHN
