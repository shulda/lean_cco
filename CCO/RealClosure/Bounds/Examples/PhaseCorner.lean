import CCO.RealClosure.Bounds.Examples.PhaseExact
import CCO.RealHull.Canonical.Hull
import CCO.SAPPoint

/-! Two literal old colours define an off-packet real corner. Their square
profiles are exact original row/phase and column/phase equivalences. -/
namespace CCO.RealClosure.Bounds.Examples.Phase
open ParityHasse.Original RealHull.Geometry

def a : Point := (0,1,false)
def b : Point := (1,0,false)
def p : Colour := ⟨(true,false,false),by decide⟩
def q : Colour := ⟨(false,true,false),by decide⟩

@[simp] theorem corner_a : colour origin a = some p := by decide
@[simp] theorem corner_b : colour origin b = some q := by decide

theorem corner_unique (y : Point) (ha : colour y a = some p) (hb : colour y b = some q) :
    y = origin := by
  have hA := coordinates_of_colour_eq (ha.trans corner_a.symm)
  have hB := coordinates_of_colour_eq (hb.trans corner_b.symm)
  have hr : row y = 0 := hA.1.mpr rfl
  have hc : column y = 0 := hB.2.1.mpr rfl
  have hs : phase y = false := by simpa only [a,origin,phase,Bool.xor_false] using hA.2.2
  exact Prod.ext hr (Prod.ext hc hs)

/-- Definability is witnessed by the TWO literal fine colours over {a,b}. -/
theorem corner_definable : origin ∈ Dcl Aut ({a,b} : Finset Point) := by
  intro g hg
  apply corner_unique
  · have hh := aut_colour g origin a
    rw [hg a (Finset.mem_insert_self _ _)] at hh
    exact hh.trans corner_a
  · have hh := aut_colour g origin b
    rw [hg b (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))] at hh
    exact hh.trans corner_b

theorem corner_algebraic : origin ∈ Acl Aut ({a,b} : Finset Point) :=
  dcl_subset_acl (G := Aut) _ corner_definable

theorem corner_outside_packets : ¬ ∃ z ∈ ({a,b} : Finset Point), packetEq z origin := by
  rintro ⟨z,hz,hrel⟩
  rcases Finset.mem_insert.mp hz with rfl | hz
  · exact Nat.one_ne_zero hrel.2
  · have he : z = b := Finset.mem_singleton.mp hz
    subst z
    exact Nat.one_ne_zero hrel.1

theorem corner_outside_finitePacket :
    ¬ ∃ z ∈ ({a,b} : Finset Point), finitePacket source homogeneous z origin := by
  rw [finitePacket_eq]
  exact corner_outside_packets

@[simp] theorem p_edge (x y : Point) : colour x y = some p ↔
    row x = row y ∧ column x ≠ column y ∧ phase x = phase y := by
  rw [colour_some]
  rcases x with ⟨r,c,s⟩; rcases y with ⟨r',c',s'⟩
  cases s <;> cases s' <;> simp [pattern,p,Prod.ext_iff,row,column,phase]

@[simp] theorem q_edge (x y : Point) : colour x y = some q ↔
    row x ≠ row y ∧ column x = column y ∧ phase x = phase y := by
  rw [colour_some]
  rcases x with ⟨r,c,s⟩; rcases y with ⟨r',c',s'⟩
  cases s <;> cases s' <;> simp [pattern,q,Prod.ext_iff,row,column,phase]

def rowPhaseEq : ColourEq source () :=
  ⟨⟨fun x y => row x = row y ∧ phase x = phase y,
    ⟨fun _ => ⟨rfl,rfl⟩,fun h => ⟨h.1.symm,h.2.symm⟩,
      fun h k => ⟨h.1.trans k.1,h.2.trans k.2⟩⟩⟩,by
    intro x y x' y' hc
    have hh := coordinates_of_colour_eq hc
    have hp : phase x = phase y ↔ phase x' = phase y' := by
      have hphase := hh.2.2
      cases hx : phase x <;> cases hy : phase y <;> cases hx' : phase x' <;> cases hy' : phase y' <;> simp_all
    exact and_congr hh.1 hp⟩

def columnPhaseEq : ColourEq source () :=
  ⟨⟨fun x y => column x = column y ∧ phase x = phase y,
    ⟨fun _ => ⟨rfl,rfl⟩,fun h => ⟨h.1.symm,h.2.symm⟩,
      fun h k => ⟨h.1.trans k.1,h.2.trans k.2⟩⟩⟩,by
    intro x y x' y' hc
    have hh := coordinates_of_colour_eq hc
    have hp : phase x = phase y ↔ phase x' = phase y' := by
      have hphase := hh.2.2
      cases hx : phase x <;> cases hy : phase y <;> cases hx' : phase x' <;> cases hy' : phase y' <;> simp_all
    exact and_congr hh.2.1 hp⟩

def doubleWord (c : Colour) : RawWord source () () := .atom (i := ()) (j := ()) (k := ()) c (.atom (i := ()) (j := ()) (k := ()) c (.nil ()))

theorem p_square (x y : Point) : RawWord.relation source (doubleWord p) x y ↔ rowPhaseEq x y := by
  constructor
  · rintro ⟨z,hxz,w,hzw,hwy⟩
    change w = y at hwy
    subst w
    have hx := (p_edge x z).mp hxz
    have hy := (p_edge z y).mp hzw
    exact ⟨hx.1.trans hy.1,hx.2.2.trans hy.2.2⟩
  · intro hxy
    let c := max (column x) (column y) + 1
    have hxc : column x ≠ c := by dsimp [c]; omega
    have hcy : c ≠ column y := by dsimp [c]; omega
    let z : Point := (row x,c,phase x)
    exact ⟨z,(p_edge x z).mpr ⟨rfl,hxc,rfl⟩,y,
      (p_edge z y).mpr ⟨hxy.1,hcy,hxy.2⟩,rfl⟩

theorem q_square (x y : Point) : RawWord.relation source (doubleWord q) x y ↔ columnPhaseEq x y := by
  constructor
  · rintro ⟨z,hxz,w,hzw,hwy⟩
    change w = y at hwy
    subst w
    have hx := (q_edge x z).mp hxz
    have hy := (q_edge z y).mp hzw
    exact ⟨hx.2.1.trans hy.2.1,hx.2.2.trans hy.2.2⟩
  · intro hxy
    let r := max (row x) (row y) + 1
    have hxr : row x ≠ r := by dsimp [r]; omega
    have hry : r ≠ row y := by dsimp [r]; omega
    let z : Point := (r,column x,phase x)
    exact ⟨z,(q_edge x z).mpr ⟨hxr,rfl,rfl⟩,y,
      (q_edge z y).mpr ⟨hry,hxy.1,hxy.2⟩,rfl⟩

theorem rowPhase_exact : ExactCRT.IsExactEq source (i := ()) rowPhaseEq.val := by
  apply isExactEq_of_word source rowPhaseEq (doubleWord p)
  funext x y
  exact propext (p_square x y)

theorem columnPhase_exact : ExactCRT.IsExactEq source (i := ()) columnPhaseEq.val := by
  apply isExactEq_of_word source columnPhaseEq (doubleWord q)
  funext x y
  exact propext (q_square x y)

theorem row_column_phase_inf : rowPhaseEq ⊓ columnPhaseEq = (⊥ : ColourEq source ()) := by
  apply ColourEq.ext
  intro x y
  constructor
  · rintro ⟨hrow,hcol⟩
    exact Prod.ext hrow.1 (Prod.ext hcol.1 hrow.2)
  · rintro rfl
    exact ⟨⟨rfl,rfl⟩,⟨rfl,rfl⟩⟩

theorem exact_corner_class_singleton :
    {y : Point | rowPhaseEq a y ∧ columnPhaseEq b y} = {origin} := by
  ext y
  constructor
  · rintro ⟨hr,hc⟩
    exact Set.mem_singleton_iff.mpr (Prod.ext hr.1.symm (Prod.ext hc.1.symm hr.2.symm))
  · rintro rfl
    exact ⟨⟨rfl,rfl⟩,⟨rfl,rfl⟩⟩
theorem p_gamma : gammaEq source p = rowPhaseEq := by
  apply le_antisymm
  · exact gamma_le_of_atom source rowPhaseEq ⟨origin,a,⟨rfl,rfl⟩,corner_a⟩
  · intro x y hxy
    obtain ⟨z,hxz,w,hzw,hwy⟩ := (p_square x y).mpr hxy
    change w = y at hwy
    subst w
    exact (RealHull.Canonical.gamma_iff_walk source homogeneous p x y).mpr
      ((Relation.ReflTransGen.single hxz).trans (.single hzw))

theorem q_gamma : gammaEq source q = columnPhaseEq := by
  apply le_antisymm
  · exact gamma_le_of_atom source columnPhaseEq ⟨origin,b,⟨rfl,rfl⟩,corner_b⟩
  · intro x y hxy
    obtain ⟨z,hxz,w,hzw,hwy⟩ := (q_square x y).mpr hxy
    change w = y at hwy
    subst w
    exact (RealHull.Canonical.gamma_iff_walk source homogeneous q x y).mpr
      ((Relation.ReflTransGen.single hxz).trans (.single hzw))

theorem canonical_corner_singleton :
    {y : Point | gammaEq source p a y ∧ gammaEq source q b y} = {origin} := by
  rw [p_gamma,q_gamma]
  exact exact_corner_class_singleton

def flipColour : Colour := ⟨(true,true,true),by decide⟩

@[simp] theorem flip_edge (x y : Point) : colour x y = some flipColour ↔
    row x = row y ∧ column x = column y ∧ phase x ≠ phase y := by
  rw [colour_some]
  rcases x with ⟨r,c,s⟩; rcases y with ⟨r',c',s'⟩
  cases s <;> cases s' <;> simp [pattern,flipColour,Prod.ext_iff,row,column,phase]

theorem notSAP : ¬ AgeSAP source := by
  intro hsap
  obtain ⟨c,x,y,z,hxy,hyz,hxz⟩ := source.realPointGluing_of_SAP homogeneous hsap
    (i := ()) (j := ()) (k := ()) flipColour flipColour
  have hA := (flip_edge x y).mp hxy
  have hB := (flip_edge y z).mp hyz
  have hs : phase x = phase z := by
    cases hx : phase x <;> cases hy : phase y <;> cases hz : phase z <;> simp_all
  have he : x = z := Prod.ext (hA.1.trans hB.1) (Prod.ext (hA.2.1.trans hB.2.1) hs)
  have hn : colour x z = none := (colour_none x z).mpr he
  change colour x z = some c at hxz
  rw [hn] at hxz
  cases hxz
end CCO.RealClosure.Bounds.Examples.Phase
