import CCO.APCharacter.Primality

/-!
# B062 / C07–C10: AP-only nonempty exact-meet mask primality

This is the actual source-level application of the already proved
AP-character primality provider. It uses RAW exact word evaluations and
the genuine character masks. The ambient old intersection MUST be nonempty;
neither SAP nor the STRONG-only saturation-intersection lemma is assumed.

The input list is the flattened family of nonempty exact presentations.
The separate theorem that identifies its mask with a trace between two
types of the homogeneous marked limit belongs to the actual marked-age
consumer and remains open.
-/

universe u v w t

namespace CCO.ExactEPGeometry

open RigidGroupoid.Geometry RigidGroupoid.Phase

noncomputable section

variable {ι : Type u} {X : ι → Type v}
variable {S : AtomicSource.{u,v,w} ι X}
variable {G : Type t} [Group G] [∀ i : ι, MulAction G (X i)]
variable {H : HomogeneousSource S G} {C : ExactCalculus S}
variable {r : ι} {A : Kernel S r}

/-- The real represented intersection of a finite family of RAW
nonempty exact domains. The empty family denotes typed Top, not Id. -/
def rawExactFamily (S : AtomicSource ι X) {i j : ι}
    (L : List (RawExact.NonemptyExact S i j)) : TRel X i j :=
  fun x y => ∀ d ∈ L, RawExact.evaluate S d.words x y

theorem rawExactFamily_nil (i j : ι) :
    rawExactFamily S ([] : List (RawExact.NonemptyExact S i j)) =
      TRel.top X i j := by
  funext x y
  apply propext
  simp [rawExactFamily, TRel.top]

/-- C10 at the genuinely accepted AP-only phase-mask interface:
a nonempty old RAW exact intersection whose every constituent meets
the allowed (ε,η) mask also meets that same mask simultaneously.

The positive-old-meet hypothesis is essential. The extra conditions
`hv`, `hw` are the actual active/inactive character constraints,
not arbitrary additional assumptions about the desired output. -/
theorem rawExactFamily_mask_primality
    (P : APCharacter.SourcePhase S H C A)
    (cco : SemanticCCO.{u,v,max u v,w} S)
    {i j : ι} (L : List (RawExact.NonemptyExact S i j))
    (ε η : Bit)
    (hv : P.validBit i ε) (hw : P.validBit j η)
    (hMeet : TRel.Nonempty (rawExactFamily S L))
    (hEach : ∀ d ∈ L, ∃ x y,
      RawExact.evaluate S d.words x y ∧
      P.allows (S.colour x y) ε η) :
    TRel.Nonempty (fun x y =>
      rawExactFamily S L x y ∧ P.allows (S.colour x y) ε η) := by
  obtain ⟨x, y, hOld, hAllowed⟩ :=
    P.phase_primality cco L ε η hv hw hMeet hEach
  exact ⟨x, y, hOld, hAllowed⟩

end
end CCO.ExactEPGeometry
