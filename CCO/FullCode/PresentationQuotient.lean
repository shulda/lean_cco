import CCO.FullCode.EmbeddingBijection
import CCO.FullCode.StructureTransport

/-! The literal quotient of DEFINED marked presentations, and its exact
diagram. A realizing host supplies coherence; no arbitrary code is certified. -/
universe u v a
namespace CCO.FullCode.Object
variable {L : Language.{u}} {V : Type v} {C : Structure L V}
  {S : RootScheme L} {A : Type a} (O : Object C S A) (N : NormalForms L)

abbrev DefinedPresentation :=
  {ap : A × Presentation N S // ((O.root ap.1).presentation N ap.2).Nonempty}

noncomputable def presentationValue (p : O.DefinedPresentation N) : V := Classical.choose p.property

theorem presentationValue_mem (p : O.DefinedPresentation N) :
    O.presentationValue N p ∈ (O.root p.val.1).presentation N p.val.2 := Classical.choose_spec p.property

def presentationSetoid : Setoid (O.DefinedPresentation N) where
  r p q := O.presentationValue N p = O.presentationValue N q
  iseqv := ⟨fun _ => rfl, Eq.symm, Eq.trans⟩

theorem presentationSetoid_iff (p q : O.DefinedPresentation N) :
    (O.presentationSetoid N).r p q ↔
      EqualityCode N (O.root p.val.1) (O.root q.val.1) p.val.2 q.val.2 := by
  constructor
  · intro h
    exact ⟨O.presentationValue N p, O.presentationValue_mem N p, h ▸ O.presentationValue_mem N q⟩
  · rintro ⟨x, hp, hq⟩
    exact ((O.root p.val.1).presentation_functional N p.val.2 (O.presentationValue_mem N p) hp).trans
      ((O.root q.val.1).presentation_functional N q.val.2 hq (O.presentationValue_mem N q))

noncomputable def quotientToSupport : Quotient (O.presentationSetoid N) → O.support :=
  Quotient.lift (fun p => ⟨O.presentationValue N p,
    O.presentation_mem_support N _ _ (O.presentationValue_mem N p)⟩)
      (fun _ _ h => Subtype.ext h)

theorem quotientToSupport_injective : Function.Injective (O.quotientToSupport N) := by
  intro x y
  refine Quotient.inductionOn₂ x y ?_
  intro p q h
  apply Quotient.sound
  exact congrArg Subtype.val h

theorem quotientToSupport_surjective (hN : N.Valid C) : Function.Surjective (O.quotientToSupport N) := by
  intro x
  obtain ⟨a, p, hx⟩ := (O.mem_support_iff_presentation N hN x.val).mp x.property
  let d : O.DefinedPresentation N := ⟨⟨a, p⟩, x.val, hx⟩
  refine ⟨Quotient.mk _ d, Subtype.ext ?_⟩
  exact (O.root a).presentation_functional N p (O.presentationValue_mem N d) hx

noncomputable def presentationQuotientEquiv (hN : N.Valid C) :
    Quotient (O.presentationSetoid N) ≃ O.support :=
  Equiv.ofBijective (O.quotientToSupport N)
    ⟨O.quotientToSupport_injective N, O.quotientToSupport_surjective N hN⟩

theorem unary_recovered (p : O.DefinedPresentation N) (U : L.Unary) :
    UnaryCode N U (O.root p.val.1) p.val.2 ↔ C.unary U (O.presentationValue N p) := by
  constructor
  · rintro ⟨x, hx, hU⟩
    exact ((O.root p.val.1).presentation_functional N p.val.2 hx
      (O.presentationValue_mem N p)) ▸ hU
  · intro hU
    exact ⟨_, O.presentationValue_mem N p, hU⟩

theorem binary_recovered (p q : O.DefinedPresentation N) (R : L.Binary) :
    BinaryCode N R (O.root p.val.1) (O.root q.val.1) p.val.2 q.val.2 ↔
      C.binary R (O.presentationValue N p) (O.presentationValue N q) := by
  constructor
  · rintro ⟨x, y, hx, hy, hR⟩
    have hxp := (O.root p.val.1).presentation_functional N p.val.2 hx
      (O.presentationValue_mem N p)
    have hyq := (O.root q.val.1).presentation_functional N q.val.2 hy
      (O.presentationValue_mem N q)
    exact hxp ▸ hyq ▸ hR
  · intro hR
    exact ⟨_, _, O.presentationValue_mem N p, O.presentationValue_mem N q, hR⟩

theorem function_graph_recovered (hN : N.Valid C) (p : O.DefinedPresentation N)
    (F : L.Func) (hp : p.val.2.2.1 = L.input F) (y : V) :
    y ∈ C.func F (O.presentationValue N p) ↔
      y ∈ (O.root p.val.1).presentation N (p.val.2.follow F hp) := by
  rw [(O.root p.val.1).presentation_follow N hN p.val.2 F hp y]
  constructor
  · intro hF; exact ⟨_, O.presentationValue_mem N p, hF⟩
  · rintro ⟨x, hx, hF⟩
    exact ((O.root p.val.1).presentation_functional N p.val.2 hx
      (O.presentationValue_mem N p)) ▸ hF

noncomputable def quotientStructure (hN : N.Valid C) :
    Structure L (Quotient (O.presentationSetoid N)) :=
  O.supportStructure.comapEquiv (O.presentationQuotientEquiv N hN)

noncomputable def quotientEmbedding (hN : N.Valid C) :
    Structure.Embedding (O.quotientStructure N hN) O.supportStructure :=
  O.supportStructure.comapEquivEmbedding (O.presentationQuotientEquiv N hN)

end CCO.FullCode.Object
