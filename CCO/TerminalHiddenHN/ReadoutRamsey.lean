import CCO.TerminalHiddenHN.ReadoutComparisons
import CCO.FullCode.ClosureTransport
import CCO.FullCode.RamseyAge

/-! Conditional readout Ramsey for the SAME entire ordered hidden age.
An arbitrary finite host can have orphan vertices. Its generated real
support is read back through its actual underlying induced embedding;
the host is never enlarged and no root-cover hypothesis is imposed. -/

universe u v w r l k z
namespace CCO.TerminalHiddenHN.RealInterpretation
open CCO.UnaryFreshFrames
noncomputable section
variable {ι : Type u} {X : ι → Type v} {S : CCO.AtomicSource.{u,v,w} ι X}
variable {G : Type r} [Group G] [∀ i, MulAction G (X i)]
variable {U : Language.{max u l}} {V : Type k} {P : Structure U V}
variable (D : RealInterpretation (G := G) S U P)

/-- EVERY finite induced closed presentation, including orphan-only
members and arbitrary carrier copies. -/
def actualAge {W : Type z} (C : CCO.UnarySupport.Structure D.signature W) : Prop :=
  Finite W ∧ Nonempty (C.Embedding D.partialModel)

abbrev orderedAge : CCO.FullCode.FiniteHidden.{max u l,z} D.orderedLanguage → Prop :=
  CCO.TerminalHiddenHN.orderedFullCodeAge D.signature D.binary D.actualAge

theorem actualAge_hereditary : CCO.UnaryHN.Raw.Hereditary.{max u l,z} D.actualAge := by
  intro W Z C E hE f
  letI : Finite Z := hE.1
  obtain ⟨g⟩ := hE.2
  exact ⟨Finite.of_injective f.point f.injective,
    ⟨CCO.TerminalHiddenHN.embedding_comp f g⟩⟩

theorem orderedAge_hereditary : CCO.FullCode.HereditaryHidden.{max u l,z} D.orderedAge :=
  CCO.TerminalHiddenHN.orderedFullCodeAge_hereditary _ _ D.actualAge_hereditary

def readoutFinite (H : CCO.HomogeneousSource S G)
    {A : CCO.FiniteInduced (X := X)} (a : D.ReadoutOn A) :
    CCO.FullCode.FiniteHidden.{max u l,k} D.orderedLanguage where
  Carrier := D.realClosure A
  model := D.readoutModel a
  finite := (D.realClosurePiece H A).finite.to_subtype

theorem readoutFinite_mem (H : CCO.HomogeneousSource S G)
    {A : CCO.FiniteInduced (X := X)} (a : D.ReadoutOn A) :
    D.orderedAge (D.readoutFinite H a) :=
  ⟨D.readoutPartialModel A,a.order,⟨(D.realClosurePiece H A).finite.to_subtype,
    ⟨D.partialModel.inclusion _ ((D.codeModel_closed_iff _).mpr (P.closure_closed _))⟩⟩,rfl⟩

/-- Original marked roots generate the whole source closure model. -/
theorem readout_base_generated (A : CCO.FiniteInduced (X := X)) :
    (binaryStructure D.signature D.binary (D.readoutPartialModel A)).closure
      (Set.range (D.closurePoint (A := A))) = Set.univ := by
  let j := binaryEmbedding D.signature D.binary
    (D.partialModel.inclusion (D.realClosure A)
      ((D.codeModel_closed_iff _).mpr (P.closure_closed _)))
  have hj : j.point '' Set.range (D.closurePoint (A := A)) = D.realPoint '' A.vertices := by
    ext y
    constructor
    · rintro ⟨x,⟨a,rfl⟩,rfl⟩
      exact ⟨a.val,a.property,rfl⟩
    · rintro ⟨a,ha,rfl⟩
      exact ⟨D.closurePoint ⟨a,ha⟩,⟨⟨a,ha⟩,rfl⟩,rfl⟩
  have he := j.closure_image (Set.range (D.closurePoint (A := A)))
  rw [hj] at he
  change D.codeModel.closure (D.realPoint '' A.vertices) = _ at he
  rw [D.codeModel_closure] at he
  apply Set.eq_univ_of_forall
  intro x
  have hx : x.val ∈ j.point ''
      (binaryStructure D.signature D.binary (D.readoutPartialModel A)).closure
        (Set.range (D.closurePoint (A := A))) := he ▸ x.property
  obtain ⟨y,hy,hyx⟩ := hx
  exact (show y = x from Subtype.ext hyx) ▸ hy

section Host
variable {W : Type z} (C : CCO.UnarySupport.Structure D.signature W)
variable (e : C.Embedding D.partialModel)

/-- Actual original roots present in the WHOLE host; hidden orphans do
not count as new original roots. -/
def hostOriginal [Finite W] : CCO.FiniteInduced (X := X) where
  vertices := D.realPoint ⁻¹' Set.range e.point
  finite_vertices := Set.Finite.preimage D.realPoint_injective.injOn (Set.finite_range e.point)

private theorem host_range_closed : P.Closed (Set.range e.point) :=
  (D.codeModel_closed_iff _).mp
    (CCO.HiddenSAPReadings.SourceSupport.embedding_range_closed e)

theorem hostClosure_mem_range [Finite W] (x : D.realClosure (D.hostOriginal C e)) :
    x.val ∈ Set.range e.point :=
  P.closure_minimal (D.host_range_closed C e)
    (by rintro _ ⟨p,hp,rfl⟩; exact hp) x.property

/-- The actual closure inclusion factors through the SAME original host
embedding, reflecting all partial graphs and all cylinders. -/
def hostPartialMap [Finite W] :
    (D.readoutPartialModel (D.hostOriginal C e)).Embedding C :=
  binaryEmbeddingInverse D.signature D.binary
    ((binaryEmbedding D.signature D.binary
      (D.partialModel.inclusion _ ((D.codeModel_closed_iff _).mpr (P.closure_closed _)))).factor
        (binaryEmbedding D.signature D.binary e)
        (by rintro _ ⟨x,rfl⟩; exact D.hostClosure_mem_range C e x))

theorem hostPartialMap_spec [Finite W] (x : D.realClosure (D.hostOriginal C e)) :
    e.point ((D.hostPartialMap C e).point x) = x.val := by
  unfold hostPartialMap
  change (binaryEmbedding D.signature D.binary e).point
    ((binaryEmbedding D.signature D.binary
      (D.partialModel.inclusion _ ((D.codeModel_closed_iff _).mpr (P.closure_closed _)))).factorPoint
      (binaryEmbedding D.signature D.binary e)
      (by rintro _ ⟨y,rfl⟩; exact D.hostClosure_mem_range C e y) x) = x.val
  exact CCO.FullCode.Structure.Embedding.factorPoint_spec _ _ _ x

def hostReadout [Finite W] [LinearOrder W] : D.ReadoutOn (D.hostOriginal C e) :=
  ⟨LinearOrder.lift' (D.hostPartialMap C e).point (D.hostPartialMap C e).injective⟩

def hostReadback [Finite W] [LinearOrder W] :
    CCO.FullCode.Structure.Embedding (D.readoutModel (D.hostReadout C e))
      (orderedStructure D.signature D.binary C) := by
  letI : LinearOrder (D.realClosure (D.hostOriginal C e)) := (D.hostReadout C e).order
  exact orderedEmbedding D.signature D.binary ⟨D.hostPartialMap C e,fun _ _ => Iff.rfl⟩

/-- ANY source embedding into the orphan-bearing host lies inside its
real-generated support. The proof uses exact original unary generation. -/
theorem host_factor_image [Finite W] [LinearOrder W]
    {A : CCO.FiniteInduced (X := X)} {a : D.ReadoutOn A}
    (f : CCO.FullCode.Structure.Embedding (D.readoutModel a)
      (orderedStructure D.signature D.binary C)) :
    Set.range f.point ⊆ Set.range (D.hostReadback C e).point := by
  letI : LinearOrder (D.realClosure A) := a.order
  let fb := orderedBinaryEmbedding D.signature D.binary f
  let j := (binaryEmbedding D.signature D.binary e).comp fb
  have hr : j.point '' Set.range (D.closurePoint (A := A)) ⊆
      D.realPoint '' (D.hostOriginal C e).vertices := by
    rintro _ ⟨x,⟨p,rfl⟩,rfl⟩
    have hs : P.sort (j.point (D.closurePoint p)) = D.realSort p.val.1 :=
      (j.sort_eq _).trans (D.sort_realPoint p.val)
    obtain ⟨z,hz⟩ := D.realPoint_surjective_on_sort _ _ hs
    refine ⟨⟨p.val.1,z⟩,?_,hz⟩
    refine ⟨f.point (D.closurePoint p),?_⟩
    change e.point (f.point (D.closurePoint p)) = D.realPoint ⟨p.val.1,z⟩
    exact hz.symm
  have hg := j.closure_image (Set.range (D.closurePoint (A := A)))
  rw [D.readout_base_generated A,Set.image_univ] at hg
  rintro _ ⟨x,rfl⟩
  have hx : j.point x ∈ D.realClosure (D.hostOriginal C e) := by
    have hi := (D.codeModel.closure_minimal
      ((D.codeModel_closed_iff _).mpr (P.closure_closed _))
      (hr.trans (P.subset_closure _)))
    exact hi (hg.symm ▸ Set.mem_range_self x)
  let y : D.realClosure (D.hostOriginal C e) := ⟨j.point x,hx⟩
  refine ⟨y,e.injective ?_⟩
  change e.point ((D.hostPartialMap C e).point y) = j.point x
  exact D.hostPartialMap_spec C e y

def hostPullback (H : CCO.HomogeneousSource S G) [Finite W] [LinearOrder W]
    {A : CCO.FiniteInduced (X := X)} {a : D.ReadoutOn A}
    (f : CCO.FullCode.Structure.Embedding (D.readoutModel a)
      (orderedStructure D.signature D.binary C)) :
    D.ReadoutEmbedding H a (D.hostReadout C e) :=
  D.readoutEmbedding_of_hidden H (f.factor (D.hostReadback C e) (D.host_factor_image C e f))

theorem hostPullback_spec (H : CCO.HomogeneousSource S G) [Finite W] [LinearOrder W]
    {A : CCO.FiniteInduced (X := X)} {a : D.ReadoutOn A}
    (f : CCO.FullCode.Structure.Embedding (D.readoutModel a)
      (orderedStructure D.signature D.binary C)) :
    (D.hostReadback C e).comp ((D.hostPullback C e H f).toHidden H) = f := by
  have hi := (D.readoutHiddenEquiv H a (D.hostReadout C e)).apply_symm_apply
    (f.factor (D.hostReadback C e) (D.host_factor_image C e f))
  change (D.hostReadback C e).comp ((D.readoutHiddenEquiv H a (D.hostReadout C e))
    ((D.readoutHiddenEquiv H a (D.hostReadout C e)).symm _)) = _
  rw [hi]
  exact f.factor_comp _ _

theorem hostPullback_comp (H : CCO.HomogeneousSource S G) [Finite W] [LinearOrder W]
    {A B : CCO.FiniteInduced (X := X)} {a : D.ReadoutOn A} {b : D.ReadoutOn B}
    (g : CCO.FullCode.Structure.Embedding (D.readoutModel b)
      (orderedStructure D.signature D.binary C)) (f : D.ReadoutEmbedding H a b) :
    (D.hostPullback C e H g).comp H f = D.hostPullback C e H (g.comp (f.toHidden H)) := by
  apply (D.readoutHiddenEquiv H a (D.hostReadout C e)).injective
  apply CCO.FullCode.Structure.Embedding.ext
  intro x
  apply (D.hostReadback C e).injective
  have hl := congrArg (fun h => h.point x) (D.hostPullback_spec C e H (g.comp (f.toHidden H)))
  have hr := congrArg (fun h => h.point ((f.toHidden H).point x)) (D.hostPullback_spec C e H g)
  change (D.hostReadback C e).point (((D.hostPullback C e H g).comp H f).toHidden H |>.point x) =
    (D.hostReadback C e).point ((D.hostPullback C e H (g.comp (f.toHidden H))).toHidden H |>.point x)
  rw [D.readout_toHidden_comp]
  exact hr.trans hl.symm

end Host

/-- The hidden Ramsey input is on the SAME whole ordered age. The
finite original host/readout is fixed before colouring ALL embeddings. -/
theorem readout_ramsey (H : CCO.HomogeneousSource S G)
    (ramsey : CCO.FullCode.HasHiddenRamsey.{max u l,k} D.orderedAge)
    (A B : CCO.FiniteInduced (X := X)) (a : D.ReadoutOn A) (b : D.ReadoutOn B)
    (n : ℕ) (hn : 0 < n) :
    ∃ C : CCO.FiniteInduced (X := X), ∃ c : D.ReadoutOn C,
      ∀ color : D.ReadoutEmbedding H a c → Fin n,
        ∃ g : D.ReadoutEmbedding H b c, ∃ shade : Fin n,
          ∀ f : D.ReadoutEmbedding H a b, color (g.comp H f) = shade := by
  obtain ⟨E,hE,arrow⟩ := ramsey (D.readoutFinite H a) (D.readoutFinite H b)
    (D.readoutFinite_mem H a) (D.readoutFinite_mem H b) n hn
  obtain ⟨C,o,hC,he⟩ := hE
  obtain ⟨e⟩ := hC.2
  letI : LinearOrder E.Carrier := o
  refine ⟨D.hostOriginal C e,D.hostReadout C e,?_⟩
  intro color
  have arrow' : CCO.FullCode.HiddenArrow (D.readoutModel a) (D.readoutModel b)
      (orderedStructure D.signature D.binary C) n := he ▸ arrow
  obtain ⟨g,shade,hg⟩ := arrow' (fun f => color (D.hostPullback C e H f))
  refine ⟨D.hostPullback C e H g,shade,?_⟩
  intro f
  rw [D.hostPullback_comp]
  exact hg (f.toHidden H)

end
end CCO.TerminalHiddenHN.RealInterpretation
