import CCO.StrongExact.FinitePC

/-!
# STRONG survivor domains and all-coordinate triangle consistency

A survivor is an *actual* fine colour occurring on a designated pair in
some injective completion of the entire partial diagram. Survivor menus are
not asserted to be exact here. This is the independent semantic
(necessity) half of the three-root occurrence and canonical-PC claims.

Unlike consistency of just one triangle, all three support inclusions
are established, each using a possibly different whole-diagram completion.
These facts require neither SAP, CCO, nor an unproved selector provider.
-/

universe u v w z

namespace CCO.PartialDiagram

variable {ι : Type u} {X : ι → Type v}
variable {S : AtomicSource.{u, v, w} ι X} {V : Type z}
variable (D : PartialDiagram S V)

/-- An atom occurs as the literal fine colour of a pair of distinct
formal vertices in an injective completion of the whole old diagram. -/
def survivor (x y : V) (_hxy : x ≠ y) :
    S.Menu (D.vertexSort x) (D.vertexSort y) :=
  {a | ∃ f : DiagramHom D, f.IsInjective ∧
    S.colour (f.point x) (f.point y) = some a}

/-- The exact survivor sets on all three pairs of distinct formal
vertices satisfy all three PC inclusions, not just nonempty support. -/
theorem survivor_PC (x y z : V)
    (hxy : x ≠ y) (hyz : y ≠ z) (hxz : x ≠ z) :
    S.PC (D.survivor x y hxy)
      (D.survivor y z hyz) (D.survivor x z hxz) := by
  refine ⟨?_, ?_, ?_⟩
  · rintro c ⟨f, hf, hc⟩
    have hXY : f.image x ≠ f.image y := fun he => hxy (hf he)
    have hYZ : f.image y ≠ f.image z := fun he => hyz (hf he)
    obtain ⟨a, ha⟩ := S.some_colour_of_ne (f.point x) (f.point y) hXY
    obtain ⟨b, hb⟩ := S.some_colour_of_ne (f.point y) (f.point z) hYZ
    exact ⟨a, ⟨f, hf, ha⟩, b, ⟨f, hf, hb⟩,
      ⟨f.point x, f.point y, f.point z, ha, hb, hc⟩⟩
  · rintro a ⟨f, hf, ha⟩
    have hYZ : f.image y ≠ f.image z := fun he => hyz (hf he)
    have hXZ : f.image x ≠ f.image z := fun he => hxz (hf he)
    obtain ⟨b, hb⟩ := S.some_colour_of_ne (f.point y) (f.point z) hYZ
    obtain ⟨c, hc⟩ := S.some_colour_of_ne (f.point x) (f.point z) hXZ
    have htri : S.Triangle a b c :=
      ⟨f.point x, f.point y, f.point z, ha, hb, hc⟩
    exact ⟨c, ⟨f, hf, hc⟩, S.conv b,
      S.mem_opposite (⟨f, hf, hb⟩), S.triangle_rotate htri⟩
  · rintro b ⟨f, hf, hb⟩
    have hXY : f.image x ≠ f.image y := fun he => hxy (hf he)
    have hXZ : f.image x ≠ f.image z := fun he => hxz (hf he)
    obtain ⟨a, ha⟩ := S.some_colour_of_ne (f.point x) (f.point y) hXY
    obtain ⟨c, hc⟩ := S.some_colour_of_ne (f.point x) (f.point z) hXZ
    have htri : S.Triangle a b c :=
      ⟨f.point x, f.point y, f.point z, ha, hb, hc⟩
    have hrot : S.Triangle (S.conv a) c b := by
      simpa only [S.conv_invol] using
        (S.triangle_rotate (S.triangle_cycle htri))
    exact ⟨S.conv a, S.mem_opposite (⟨f, hf, ha⟩),
      c, ⟨f, hf, hc⟩, hrot⟩

/-- Semantic survivor domains form one typed network on genuinely
distinct formal vertices, with no artificial diagonal coordinates. -/
def survivorNetwork : StrongPC.Network D :=
  fun p => D.survivor p.src p.dst p.ne

/-- Every real completion colour is in its own survivor network. -/
theorem supports_survivorNetwork (f : DiagramHom D)
    (hf : f.IsInjective) :
    StrongPC.SupportsCompletion D (D.survivorNetwork) f := by
  intro p a ha
  exact ⟨f, hf, ha⟩

/-- The network of actual whole-diagram survivors is stable under
all three-distinct-vertex STRONG PC updates. -/
theorem survivorNetwork_stable :
    StrongPC.Stable D (D.survivorNetwork) := by
  intro p
  apply Set.Subset.antisymm
  · exact StrongPC.step_refines D (D.survivorNetwork) p
  · intro a ha
    obtain ⟨f, hf, hcol⟩ := ha
    exact StrongPC.supports_step D (D.survivorNetwork) f hf
      (D.supports_survivorNetwork f hf) p a hcol

theorem survivorNetwork_refines_initial :
    StrongPC.Refines D (D.survivorNetwork) (StrongPC.initial D) := by
  intro p a ha
  obtain ⟨f, _, hcol⟩ := ha
  exact StrongPC.supports_initial D f p a hcol

/-- A semantic, source-independent consumer of C10 greatestness:
every atom realized in some injective completion survives EVERY
synchronous PC iteration, even if different atoms have witnesses in
different completions. -/
theorem survivorNetwork_refines_iterate (n : Nat) :
    StrongPC.Refines D (D.survivorNetwork)
      (StrongPC.iterate D (StrongPC.initial D) n) :=
  StrongPC.stable_refines_iterate D
    (D.survivorNetwork) (StrongPC.initial D)
    D.survivorNetwork_stable
    D.survivorNetwork_refines_initial n


/-- The actual whole-diagram survivor network sits inside the greatest
finite PC fixed point, even though the reverse inclusion is not yet
known without C07–C12 exactness and path semantics. -/
theorem survivorNetwork_refines_fixedNetwork :
    StrongPC.Refines D D.survivorNetwork (StrongPC.fixedNetwork D) :=
  StrongPC.fixedNetwork_greatest D (D.survivorNetwork)
    D.survivorNetwork_stable D.survivorNetwork_refines_initial

end CCO.PartialDiagram
