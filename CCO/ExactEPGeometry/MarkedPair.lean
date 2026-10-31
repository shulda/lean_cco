import CCO.ExactEPGeometry.TracePrimality
import CCO.APCharacter.MarkedSource

/-!
# B062 C05/C10: actual AP-character masked pairs in the marked limit

Start with the genuine SOURCE mask, extend a prescribed finite pair to
ONE globally legal character marking using the accepted free-action seed
theorem, and then embed its finite induced diagram into the actual homogeneous
marked age. Diagonal pairs use a singleton, not a diversity edge.

This proves the first-stage real marked-age realization needed after the
nonempty exact-meet primality provider. It does not claim arbitrary current
prefix exact trace-surjectivity or the reverse trace-product equality.
-/

universe u v w t

namespace CCO.ExactEPGeometry

open APCharacter RigidGroupoid.Geometry RigidGroupoid.Phase

noncomputable section

variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)

/-- A literal legal old pair remains legal in reverse orientation. The
logical diagonal case is handled by the real equality and identity mask;
there is no additional equality-coloured diversity atom. -/
theorem allowed_reverse_real {M : MaskData S} {i j : ι}
    (x : X i) (y : X j) (ε η : Bit)
    (h : M.allowed (S.colour x y) ε η) :
    M.allowed (S.colour y x) η ε := by
  cases hc : S.colour x y with
  | none =>
      have heq : (⟨i, x⟩ : Sigma X) = ⟨j, y⟩ :=
        (S.colour_none_iff x y).mp hc
      have hij : i = j := congrArg Sigma.fst heq
      cases hij
      have hxy : x = y := by
        simpa only [Sigma.mk.injEq, heq_eq_eq, true_and] using heq
      subst y
      have hb : ε = η := ((M.identity i ε η).mp (by simpa only [hc] using h)).1
      subst η
      have hdiag : S.colour x x = none := (S.colour_none_iff x x).mpr rfl
      simpa only [hdiag, hc] using h
  | some a =>
      have hrev : S.colour y x = some (S.conv a) :=
        (S.colour_swap x y a).mp hc
      rw [hrev]
      exact (M.reverse a ε η).mp (by simpa only [hc] using h)

/-- The four ordered edges of the two-position diagram are legal,
including both loops and the possible collision of the two positions. -/
theorem actual_bool_pair_legal (M : MaskData S)
    {i j : ι} (x : X i) (y : X j) (ε η : Bit)
    (hv : M.validBit i ε) (hw : M.validBit j η)
    (h : M.allowed (S.colour x y) ε η) :
    Age.Legal S M
      (fun b : Bool => if b then (⟨j, y⟩ : Sigma X) else ⟨i, x⟩)
      (fun b : Bool => if b then η else ε) := by
  constructor
  · intro b
    cases b
    · exact hv
    · exact hw
  · intro b c
    cases b <;> cases c
    · change M.allowed (S.colour x x) ε ε
      rw [(S.colour_none_iff x x).mpr rfl]
      exact (M.identity i ε ε).mpr ⟨rfl, hv⟩
    · exact h
    · exact allowed_reverse_real S x y ε η h
    · change M.allowed (S.colour y y) η η
      rw [(S.colour_none_iff y y).mpr rfl]
      exact (M.identity j η η).mpr ⟨rfl, hw⟩

/-- A genuinely legal old atomic pair with specified phase bits extends
to ONE real global character marking, even if both positions are equal. -/
theorem global_marking_prescribed_pair (M : MaskData S)
    (seeds : M.FiniteSeedExtension)
    {i j : ι} (x : X i) (y : X j) (ε η : Bit)
    (hv : M.validBit i ε) (hw : M.validBit j η)
    (h : M.allowed (S.colour x y) ε η) :
    ∃ mark : Sigma X → Bit, M.GlobalMarking mark ∧
      mark ⟨i, x⟩ = ε ∧ mark ⟨j, y⟩ = η := by
  let point : Bool → Sigma X :=
    fun b => if b then (⟨j, y⟩ : Sigma X) else ⟨i, x⟩
  let bits : Bool → Bit := fun b => if b then η else ε
  have legal : Age.Legal S M point bits :=
    actual_bool_pair_legal S M x y ε η hv hw h
  obtain ⟨mark, hmark, he⟩ :=
    Age.finite_seed_small S M seeds point bits legal
  exact ⟨mark, hmark, by simpa [point, bits] using he false,
    by simpa [point, bits] using he true⟩

variable {G : Type t} [Group G] [∀ i : ι, MulAction G (X i)]
variable (H : HomogeneousSource S G) {M : MaskData S}
variable (completion : Age.CompletionProperty S M)

/-- An actual globally marked pair has its exact unary AND binary names
in the genuine homogeneous marked limit. When the old pair is on the
diagonal, embed a singleton; otherwise embed an injective two-point chart.
No homogeneity of the arbitrary global marking is assumed. -/
theorem global_marked_pair_in_limit
    (mark : Sigma X → Bit) (hm : M.GlobalMarking mark)
    (p q : Sigma X) :
    ∃ a b : Age.Limit S H completion,
      (Age.limitCoding S H completion).table.owner a =
        Age.ownerEquiv S (p.1, mark p) ∧
      (Age.limitCoding S H completion).table.owner b =
        Age.ownerEquiv S (q.1, mark q) ∧
      (Age.limitCoding S H completion).table.colour a b =
        Age.colourEquiv S (taggedColour S p q) := by
  by_cases hpq : p = q
  · let point : Unit → Sigma X := fun _ => p
    let bits : Unit → Bit := fun _ => mark p
    have hi : Function.Injective point := by
      intro x y _
      exact Subsingleton.elim x y
    have legal : Age.Legal S M point bits :=
      ⟨fun _ => hm.1 p, fun _ _ => hm.2 p p⟩
    obtain ⟨f, ho, hc⟩ := Age.embed_realized S H completion point bits hi legal
    refine ⟨f (), f (), ?_, ?_, ?_⟩
    · simpa only [point, bits] using ho ()
    · simpa only [hpq, point, bits] using ho ()
    · simpa only [hpq, point, bits] using hc () ()
  · let point : Bool → Sigma X := fun b => if b then q else p
    let bits : Bool → Bit := fun b => mark (point b)
    have hi : Function.Injective point := by
      intro x y hxy
      cases x <;> cases y
      · rfl
      · exact False.elim (hpq hxy)
      · exact False.elim (hpq hxy.symm)
      · rfl
    have legal : Age.Legal S M point bits :=
      ⟨fun b => hm.1 (point b), fun b c => hm.2 (point b) (point c)⟩
    obtain ⟨f, ho, hc⟩ := Age.embed_realized S H completion point bits hi legal
    refine ⟨f false, f true, ?_, ?_, ?_⟩
    · simpa [point, bits] using ho false
    · simpa [point, bits] using ho true
    · simpa [point, bits] using hc false true

variable {S H completion}

/-- Real marked-age witness for the AP-only nonempty RAW exact intersection.
The old pair realizes the ENTIRE intersection; its unique global marking
is not mistaken for the homogeneous output. Both actual endpoint labels
and their original atomic pair orbital survive inside the OUTPUT limit. -/
theorem marked_exact_family_witness
    {C : ExactCalculus S} {r : ι} {A : Kernel S r}
    (P : APCharacter.SourcePhase S H C A)
    (cco : SemanticCCO.{u,v,max u v,w} S)
    {i j : ι} (L : List (RawExact.NonemptyExact S i j))
    (ε η : Bit)
    (hv : P.validBit i ε) (hw : P.validBit j η)
    (hMeet : TRel.Nonempty (rawExactFamily S L))
    (hEach : ∀ d ∈ L, ∃ x y,
      RawExact.evaluate S d.words x y ∧
      P.allows (S.colour x y) ε η) :
    ∃ (a b : Age.Limit S H (P.completion_property cco))
      (x : X i) (y : X j),
      rawExactFamily S L x y ∧
      (Age.limitCoding S H (P.completion_property cco)).table.owner a =
        Age.ownerEquiv S (i, ε) ∧
      (Age.limitCoding S H (P.completion_property cco)).table.owner b =
        Age.ownerEquiv S (j, η) ∧
      (Age.limitCoding S H (P.completion_property cco)).table.colour a b =
        Age.colourEquiv S (taggedColour S (⟨i, x⟩ : Sigma X) ⟨j, y⟩) := by
  obtain ⟨x, y, hAll, hAllowed⟩ :=
    rawExactFamily_mask_primality (S := S) P cco L ε η hv hw hMeet hEach
  obtain ⟨mark, hm, hmx, hmy⟩ :=
    global_marking_prescribed_pair S P.masks P.finite_seed_extension
      x y ε η hv hw hAllowed
  obtain ⟨a, b, ho1, ho2, hc⟩ :=
    global_marked_pair_in_limit S H (P.completion_property cco)
      mark hm ⟨i, x⟩ ⟨j, y⟩
  refine ⟨a, b, x, y, hAll, ?_, ?_, hc⟩
  · simpa only [hmx] using ho1
  · simpa only [hmy] using ho2

end
end CCO.ExactEPGeometry
