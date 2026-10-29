# B026 proof notes — safe augmented selectors and rectangular readings

Frozen mathematical source 490c3f36; preparation base 64da92cf. Complete local human proof expansions only; no Lean implementation or global source-relative EPPA certification. The source TeX is unchanged. All twelve source exports have their full local proof support below; reservoir/locality-bound are excluded.

Provider support selection is now explicit in module.json. The historical support discussion below records why internal support is not a direct export: the validated provider_support_claims field is the selected assembly solution. It permits only proved strict transitive ancestors of selected exported claims and retains their mathematical premises. No older provider/public contract is modified.

## N01: Actual source, typing and legitimate shared support

Let actual finite owner sorts have finite nonempty diversity palettes P_st. All actual triangles use three distinct vertices, even for repeated sorts. Equality is not a strong colour. Underlying literal old fine names are symmetric: typed converse reverses owner tags and fixes the name. A finite Gamma acts purely on owner tags and fixes the same literal names, preserving typed legal triangles and multiplication.

Original H_st comprises nonempty finite meets of positive-path profiles, with empty presentation equal genuine diversity Top. It contains singleton atoms and Top, is converse/product/nonempty-meet closed, has finite 2-Helly and NONEMPTY-result meet-product distribution. The latter original facts use SAP+CCO providers. Every individual sort is primitive only where loop saturation/no-return is invoked.

S_st is GIVEN, nonempty, typed converse-compatible and Gamma-covariant, and strongly S-amalgamates EVERY finite complete typed span, including empty base. It is not manufactured by the selector or reservoir. Strong-S-amalgamation of closed spans alone is insufficient here.

Define K_st = H_st union {D intersect S_st : D in H_st, D intersect S_st nonempty}. Its members are actual subsets of P_st, not a contracted new multiplication algebra. A skeleton presentation X=D_X intersect S^e has e in {0,1}, S^0=P_st, and evaluated X nonempty; skeletons need not be unique.

## 2. Resolve shared support without illegal provider_claims

The existing strong_selectors direct exports are:
- lem:typed-set-pasch -> C02;
- lem:typed-injectivisation -> C04,C05;
- lem:typed-helly -> C07;
- lem:typed-exact-products -> C08;
- lem:typed-PC-fixedpoint-exact -> C13;
- lem:typed-bilateral -> C15;
- lem:typed-all-PC -> C14,C17;
- lem:typed-gate-image -> C18;
- lem:typed-pure-action-gate-engine -> C26.

Do not list internal C01/C03/C10/C16/C25 under exports that do not select them. In particular exact-products does not directly export C01/C03, all-PC does not directly export C16, and pure-action engine does not directly export C25.

Safe options:
(a) retain precisely these exported provider_claims and write the short internal support as local B026 proof steps derived from actual triangle definitions and the given source SAP; or
(b) explicitly create a separately pinned shared auxiliary support export and review it as a deliberate metadata/API addition.

Option (a) is sufficient and leaves old/public contracts unchanged. The necessary support is:
- Boolean monotonicity, converse, atomic Peirce/PC rotations: direct definition of actual legal triangles.
- Supported-fork duplication: the SAP proof immediately below, not a silently imported C03 declaration.
- Supported restrictions: part of the explicit gate-transport proof below; no imported C16 needed.
- Minimal viable filter visibility: proved below, no imported C25 needed.
- Completion survivor induction: elementary finite-PC argument, or use the already source-proved dependency closure of a legitimate original PC export without falsely selecting C10 as a direct export.

### Local SAP duplication support

For any c:i->k and nonempty X subset P_ij, X subset {c}*bar{c}*X. Fix x in X. Strongly amalgamate a realized c-edge i0--k0 and x-edge i0--j0 over i0. This gives a complete triangle with all vertices distinct. Strongly amalgamate two copies of this triangle over its complete k0--j0 edge; denote their distinct remaining vertices i0,i1. Then i0,k0,i1,j0 are distinct and the path has colours c,bar c,x, while i0--j0 has x. Thus x is in the displayed product. Actual homogeneity aligns named edge representatives if necessary. This is the support used in restricted-menu gate proof and is valid for arbitrary subsets; no exactness or CCO is used.

For loop W, W subset W^3 also has the source's direct two-triangle four-cycle proof: for a in W realize two a-edges with third edge b, and strongly glue two copies over b. It follows that a lies in a*a*a. This avoids trying to infer W subset W^3 from a fork with an unrelated c.

## N02: Arbitrary-subset absorption and uniform primitive loop powers

### lem:locality-absorb — reuse, do not duplicate mathematics

For nonempty A subset P_st and B subset P_tu, A*P_tu=P_su and P_st*B=P_su. Fix an output atom and one input atom and strongly glue the two actual edges over their common endpoint; their off-base vertices are distinct. This is exactly the arbitrary-subset absorption already in C02, and needs neither primitivity nor CCO.

### lem:locality-positive — new uniform consequence

For arbitrary nonempty W subset P_tt (not required exact or a word profile), let m=|P_tt|. Duplication gives the increasing nonempty even-power chain E_k=W^(2k). Any equality E_k=E_(k+1) propagates by associativity, and the stable J satisfies J*J=J. The actual relation Delta_t union J is an invariant equivalence: symmetry is inherited from original same-sort atoms; transitivity for three distinct points uses J*J subset J, and equality cases use Delta. J nonempty rules out equality, so primitivity forces J=P_tt.

In the chain E_1,...,E_m either an adjacent equality occurs, giving fullness, or there are m strictly increasing nonempty subsets of an m-atom set, so E_m is full. Thus W^(2m)=P_tt, including m=1. Absorption gives every later power. The real diagonal is used only in the interpreted equivalence, never adjoined to the strong menu algebra.

## N03: Same-vertex recolouring, traces and skeleton calculus

### lem:one-edge-safe-recolour

For complete finite C and distinct x,y, strong-S-amalgamate C minus x and C minus y over their complete common part C minus {x,y}. Strongness keeps the off-base singleton vertices distinct; the one new edge xy is safe. Restrict to the two factor images and identify them with the old vertex set. All other colours and owners are fixed. Two vertices and empty base are included.

### lem:safe-trace-product

For nonsingleton D in original H, no member of any finite positive-profile presentation can have length one, since its singleton profile would force nonempty D to be that singleton. Realize all selected positive paths over one complete root edge of colour d in D, individually injectively, and amalgamate their complete witnesses over this edge. Individual injectivity ensures none of their path edges is the root edge, regardless of overlaps between different witnesses. Recolour only that root edge. All paths survive, so the new safe colour lies in D intersect S. Empty Top presentation requires only a realized root edge.

For arbitrary nonempty E subset P_tu, take any c in D*E with witness triangle xy=d, yz=e, xz=c. Glue the D witnesses to that triangle over xy, then recolour xy only. This keeps yz, xz and every path witness, so c lies in (D intersect S)*E. Monotonicity proves equality. No presentation of E is used. Singleton D meeting S is trivial; unsafe singleton D has empty trace and is excluded. Converse gives the left-factor analogue using converse-compatibility of S.

### lem:augmented-safe-skeleton-calculus

For X=D_X intersect S^e and Y=D_Y intersect S^f nonempty:
X*Y=D_X*D_Y.
If e=1 remove the first trace using arbitrary multiplier Y; if f=1 remove the second trace with the left-sided identity. Thus the product is original H. No uniqueness of skeleton is required.

For a nonempty finite indexing list with NONEMPTY evaluated intersection,
intersection_i X_i = (intersection_i D_Xi) intersect S^(max e_i).
The original meet is nonempty because it contains the evaluated result. Empty indexing list is typed Top separately. This gives nonempty-result meet closure; all empty evaluated intersections remain excluded.

If Y intersect Z is nonempty, its underlying original meet D_Y intersect D_Z is nonempty, so
X*(Y intersect Z)
 = D_X*(D_Y intersect D_Z)
 = (D_X*D_Y) intersect (D_X*D_Z)
 = (X*Y) intersect (X*Z).
The other direction follows by converse. Distribution is not asserted when Y intersect Z is empty.

## N04: Augmented finite 2-Helly

For a pairwise-intersecting finite list of K menus, their original skeletons are pairwise intersecting, hence share d by original 2-Helly. If all menus are untraced, d works. If any original skeleton is {e}, its LISTED augmented menu is necessarily {e}, and pairwise intersection with that menu forces e into every listed augmented menu. Otherwise all skeletons have positive-path presentations of lengths at least two or empty Top presentations. Glue all path witnesses over the same d-root edge and recolour once. The new atom is safe and belongs to every skeleton, hence every listed menu.

This proof does not take an arbitrary original common atom and merely assume it is safe.

## N05: Explicit finite-menu gate extraction and augmented supported restrictions

The following is a local extracted lemma, not a new human article theorem label. Its assumptions are exactly those proved for K above and the actual triangle support below.

Let K be finite typed menu families, invariant under the full Gamma action (which bijects typed families and preserves products/converse), containing Top and all singletons, closed under products/converse/nonempty intersections, with 2-Helly and both NONEMPTY-result product/meet distributivities. Products are the actual atomic triangle products, so Peirce rotations hold, and supported-fork duplication from section 2 holds for any singleton multiplier. Let J be a converse-closed, Gamma-invariant subfamily downward relative to K and containing every singleton. J need not be product closed. Let F be a tagged subfamily closed under converse, Gamma, and left/right products by ALL K menus, not only J.

Assume relative visibility: parallel A,B in F that both meet one D in J have A intersect B nonempty. Set
G(D)=D intersect intersection{A in F : A intersect D nonempty}.
An empty active list leaves D unchanged.

### Gate nonemptiness, converse and heredity

The finite list D and its active filters is pairwise intersecting by visibility; 2-Helly makes G(D) nonempty. Meet closure puts it in K, then downward closure in J. Converse bijects active lists. If E subset D meets G(D), every filter active on D also meets E via a survivor; conversely activity on E implies activity on D. Hence active lists coincide and G(E)=E intersect G(D).

### Bilateral support, with a fixed factor not required current

For D in J_ij, E in J_kj and fixed P in K_ik assume D subset P*E and E subset bar P*D. For active A in F_kj on E, choose e in A intersect E. The second support inclusion and atomic Peirce supply d in D intersect(P*A). Thus P*A is active on D and belongs F. Therefore G(D) lies in P*E and every P*A. Nonempty G(E) just proved allows finite nonempty-result distribution:
G(D) subset (P*E) intersect intersection_A(P*A)
 = P*(E intersect intersection_A A)
 = P*G(E).
Swap D,E and bar P for the second inclusion; converse gives fixed-right support. Empty active list is handled directly, not by asserting P*Top=identity.

### All three PC coordinates

Suppose PC(A,B,C) and c in G(C). Bilateral left/right support gives c in A*G(B) and c in G(A)*B. Let
A_c=A intersect({c}*bar B),
B_c=B intersect(bar A*{c}).
Products are K, intersections are nonempty since they meet G(A),G(B), and both restrictions are current by downwardness. Heredity gives G(A_c)=A_c intersect G(A), likewise B.

Using nonempty-result distribution and the actual SAP duplication inclusions,
{c}*bar B_c
 = ({c}*bar B) intersect({c}*bar{c}*A) contains A_c,
bar{c}*A_c
 = (bar{c}*A) intersect(bar{c}*{c}*bar B) contains bar B_c.
Both intersections to which distribution is applied have already been proved nonempty. Bilateral support on (A_c,bar B_c) with fixed singleton {c} therefore gives
G(A_c) subset {c}*G(bar B_c).
Choose a in nonempty G(A_c), obtain b in G(B_c), and rotate Peirce to conclude c in a*b. Thus c in G(A)*G(B). Apply the same argument to both typed rotations for all three PC inclusions. Sort labels and menu variables may coincide.

This explicitly supplies the internal C16-style support within K, instead of pretending the original theorem's variables already range over K.

### Image/composition/covariance

For any nonempty K submenu E of G(D), downwardness places E in J and heredity gives G(E)=E. Thus G is idempotent, its image is exactly its fixed current family, and that image remains downward/converse/Gamma invariant with every singleton. Composition heredity follows by applying the survivor identity twice. A proper active trace makes G(D) a strict subset, so D disappears from the image. Pure Gamma bijects all active lists because F was closed under the WHOLE Gamma action before gate construction. Seed choices need not themselves be invariant.

## N06: Positive-provenance typed returns and parallel separation

The original gate-engine statement only quantifies original H. The following separate proof discharges its needed analogue for K.

For a generation path, associate the transformation
T(X)=L*(gamma X)^epsilon*R.
Outside factors are either ABSENT OPERATIONS, or nonempty finite products of actual K generators. Record a syntactic present/absent bit. Products, transport and converse concatenate/transport/exchange factors and never change present to absent: nonemptiness follows from SAP. A present factor is an arbitrary nonempty atomic subset, not necessarily an original word profile or original exact menu.

For a typed return, q=2|Gamma| iterations cancel the central Gamma action and converse. Consequently T^q(X)=P*X*Q, where each present factor is a genuine nonempty loop subset at its original endpoint, and at least one factor is present when any multiplication occurred. Iterating k=2m_0, m_0=max_t|P_tt|, saturates each present factor by section 3, so T^(4|Gamma|m_0)(X)=P_st for every nonempty parallel X. A proper fixed menu cannot admit such return.

Full menus cannot reach proper menus by absorption and action/converse preservation of Top. If parallel A,B generate the same closed family, compose paths A->B->A. For proper A no multiplication occurs anywhere; only pure Gamma and typed converse remain. BOTH fix literal old fine names, hence parallel A=B. The full case follows from full absorption.

The converse-name assumption is essential. Same-sort symmetry alone does not exclude the source's two-sort directed counterexample with converse swapping two cross atoms and Gamma exchanging sort names.

## N07: Visible seed descent, safe retraction and whole-orbit bound

Among all viable K seeds C with a proper nonempty trace on some current menu, choose one minimizing its finite Gamma/converse/product-generated family F(C). If visibility failed at D', disjoint parallel A,B in F(C) both meeting D' are themselves viable seeds. Their generated families are subfamilies of F(C). If both have equal cardinality, they both equal F(C); no-return separation then gives A=B, contradiction. At least one is strictly smaller, contradicting minimality. Thus visibility holds and the extracted gate lemma applies.

Iterate strict gates until all current menus are singletons. The finite current family strictly shrinks and preserves singletons. This is the actual proof of the augmented version; it does not instantiate the original-H statement outside its domain.

Define T on ALL K by T(D)=D intersect S if that intersection is nonempty, otherwise D. It is K-valued, nonempty, conservative and idempotent. Any changed input must be original exact, since a traced menu lies wholly in S. Remove changed traces successively with the arbitrary-multiplier identity to obtain T(D)*T(E)=D*E for all compatible K menus. Hence all three PC right products are unchanged while the left menus shrink. Converse and Gamma compatibility follow from S. For E subset D meeting T(D), a case split on D intersect S gives T(E)=E intersect T(D).

Choose the gate descent on the image T(K), or construct a selector h0 on all K and precompose T. In the former version the resulting hS=h0 after T directly realizes the stated bound after T. The image T(K) is current by the same idempotence/heredity argument. Composition preserves survivor heredity, covariance, converse and PC. If D meets S, hS(D) lies in D intersect S.

A strict covariant gate removes a nonsingleton current D and all Gamma-translates from its image. Since images are nested, at most the number N_Gamma of initial Gamma-orbits of tagged nonsingleton K menus can be removed. N_Gamma <= sum_st(|K_st|-|P_st|) <= sum_st(2|H_st|-|P_st|). No free/faithful Gamma action is needed.

## N08: Safe certificate, greatest PC and actual age membership

Given an injective completion certificate of a finite partial diagram, pull its complete colouring back to that vertex set. Recolour each originally unrecorded edge in turn by one-edge recolouring. Recorded edges and earlier safe holes stay fixed. This yields a safe injective certificate, not an equivariant choice of certificate.

Initialize original PC with recorded singletons and genuine full hole palettes. Every certificate edge survives every update by the elementary completion-survivor induction, so each hole's final original exact domain meets S. Original exactness follows from the legitimate original fixed-domain provider (or original product/nonempty-meet closure induction). Greatest PC is canonical under pure owner automorphisms. Apply hS on its original domains. Records survive, holes are safe, and every triangle is legal by all-three-PC preservation.

To conclude actual source age membership either use the precise triangle-defined source API or invoke actual CCO/SAP cycle completion: triangle legality on a complete graph implies every specified cycle profile is realized by triangulation/associativity, CCO completes the diagram, and SAP injectivization is available. Do not replace this step by bare triangle legality in an arbitrary age.

SC01 Existential same-vertex safe certificate.
For a finite typed partial diversity diagram P with coherent converse records
and AT MOST one literal atomic colour on each unordered pair, assume one
injective completion in the actual age and GIVEN all-span strong S-amalgamation.
There is a complete legal colouring on the SAME FORMAL vertex set and owners,
agreeing with all records, safe on each originally unrecorded pair.
Proof: pull the initial injective realization back to the formal vertices.
Enumerate the original holes. Apply one-edge recolouring successively;
each operation fixes all other pairs, including records and previous safe
choices. This is finite induction, with empty/singleton vertex sets vacuous.
It yields an existence certificate, with no equivariance claim.

SC02 Greatest PC exact domains retain the safe certificate.
Initialize records by singletons and holes by full diversity Top. The finite
oriented PC process has a greatest stable refinement. SC01's selected atom
on every pair survives every update, by its legal triangles; hence every final
domain is nonempty and every hole's domain meets its typed S.
Imported actual C13 makes these domains ORIGINAL exact. This statement reuses
C10's finite survivor induction explicitly. For zero/one vertices there are
no domains and no third-vertex updates; for two vertices domains stay their
initial singleton/Top menus.

SC03 Canonical pure-owner equivariant safe completion.
Apply the one joint augmented selector h_S to these final domains. Every
record remains its singleton; each hole is selected in S. Full three-coordinate
PC preservation gives legal triangles. To conclude age membership/injective
realizability of the complete same-vertex colouring, USE the actual
triangle-defined U_B-age provider B025 C34. An abstract variant must state
that provider separately or establish every simple cycle then use CCO/SAP
C06; legal triangles alone are insufficient in an arbitrary age.
For every structural diagram automorphism sigma with associated pure
gamma in Gamma, canonical greatestness gives
  D^infty_(sigma x),(sigma y)=gamma D^infty_xy
(as literal colours this is the same subset, with transported tags).
Covariance of h_S preserves every such map simultaneously.
No equivariant realization certificate, frame/origin section or averaging
is needed.

The preceding age-membership point is a FORMALIZATION_DETAIL expansion of
lem:safe-global-completion, not a new source theorem repair in actual U_B,
because B025 C34 already supplies exactly that bridge.

## N09: Actual endpoint transport and independent rectangular readings

Let B be a finite nonempty actual owner set, U_B the homogeneous primitive
transversal furnished by B025, and P_st=L_st minus F its nonempty finite
DIVERSITY palettes. A typed menu includes its ordered endpoint tags even when
two actual subsets of literal names agree. Every triangle has three distinct
FORMAL vertices; owner tags s,t,u and menu variables need not be distinct.
No equality atom belongs to a loop diversity palette.

Let H_st be the ORIGINAL nonempty strong exact families: nonempty finite
intersections of positive atomic path profiles, with the empty restriction list
evaluating to full P_st. The reading argument below uses only these ORIGINAL
families. Augmented safe traces are not needed to prove rectangular readings.

A joint singleton selector h has:
- h_st(D) in D;
- typed converse compatibility;
- survivor heredity: E subset D and h_st(D) in E imply h_st(E)=h_st(D);
- all three PC coordinates: PC(D,A,P) implies T(h(D),h(A),h(P)).
A finite pure owner group Gamma fixes every LITERAL old fine-colour name,
transports types, original exact families, strong products and triangle tables.
Typed converse also fixes each literal old fine name; this is the
SYMMETRIC-ORIGINAL premise, not merely symmetry of same-sort typed atoms.

For moving readings, G is the actual finite elementary abelian thin group,
written additively. Its owner action rho:G -> Sym(B) need NOT be faithful.
Each gamma in Gamma commutes with rho(G), and rho(G) is contained in Gamma.
The colour involution g sends a:P_st to ga:P_(gs),t for switching the first
endpoint, and equivalently to P_s,(gt) for switching the second.
Independent vertex switches (r,q,p) transform triangle colours (a,b,c) into
((r+q)a,(q+p)b,(r+p)c). The diagonal switch fixes colours.

Define, with the MOVED input type,
    h^g_st(D) = g h_(gs),t(gD).
The expression g h_st(gD) is generally ill-typed.

For safe completion separately, S_st subset P_st is a GIVEN nonempty typed
converse-compatible pure-Gamma-covariant palette with strong S-amalgamation of
EVERY finite COMPLETE typed span, INCLUDING empty base. No claim constructs S.
The safe selector h_S is on the augmented family, preserves PC/converse/
survivor heredity and selects inside S whenever its input meets S.

Identifiers Rxx below are proposed local milestone names, not existing IDs.

R01 Actual three-vertex gauge transport.
For all s,t,u in B, all r,q,p in G and atoms a in P_st,
b in P_tu,c in P_su,
  T(a,b,c) iff T((r+q)a,(q+p)b,(r+p)c).
The reverse map uses the same switches. Moreover transport is bijective on
menus, inclusion, finite intersections, converse and arbitrary-subset strong
products, with the forced endpoint labels.
Dependencies: actual B025 inflation and thin-bottom, not full_rows decoder.
Proof: realize the three formal vertices in DISTINCT F-packets. Real thin
translations stay in those packets, so independent switches keep them distinct.
Use the literal fine-colour law; switch back for equivalence.

R02 Original exact-menu gauge transport.
For any D in H_st and g in G, gD belongs to H_(gs),t and also H_s,(gt).
Dependencies: R01, original exact positive-word presentation C08.
Proof: for an injective path choose endpoint shifts g and zero at all other
vertices; only its first letter changes, or its sole letter if length one.
For right transport change its last letter. Actual distinct packets keep the
path injective after transport. Strong profile transport is exact in both
directions. Distribute the bijection across each finite meet; empty list Top
maps to Top. No choice of an equivariant transversal origin is made.

R03 Shifted readings preserve conservation and individual heredity.
For all g in G,D in H_st, h^g_st(D) belongs to D. For every original exact
E subset D with h^g_st(D) in E, h^g_st(E)=h^g_st(D).
Dependencies: h, R02. Apply g to inclusion/membership, use h heredity, apply
g back. These laws are for each fixed g independently.

R04 Left/right readings, then converse.
For every g,D,
  h_(gs),t(gD)=h_s,(gt)(gD).
Hence h^g_ts(bar D)=bar(h^g_st(D)).
Dependencies: pure covariance of h, diagonal rho(g) in Gamma, R02.
Proof: apply rho(g) to the moved pair (gs,t); it becomes (s,gt) and fixes
the literal names gD. Then use typed converse of h and actual switch/converse
commutation. In particular, a second-endpoint switch may be read using the
same h^g, even when s=t.

R05 Pure Gamma covariance and switching.
For every gamma in Gamma,g in G,D in H_st,
  h^g_(gamma s),(gamma t)(D)=h^g_st(D).
For every u,v in G,D in H_st,
  h^(u+v)_(vs),t(vD)=v h^u_st(D).
Dependencies: R03,R04,pure h covariance,gamma(gs)=g gamma(s).
Calculation:
 (u+v)h_((u+v)vs),t((u+v)vD)
 = (u+v)h_(us),t(uD)
 = v h^u_st(D).
This uses exponent two, not faithfulness of rho.

R06 Bilateral refinement to a full PC triple.
For nonempty ORIGINAL exact D in H_st,A in H_tu,P in H_su
with D subset P*bar A and A subset bar D*P, define
  P'=P intersect(D*A).
Then P' is nonempty ORIGINAL exact and PC(D,A,P').
Dependencies: original exact C08, atomic Peirce C01, duplication C03.
Nonempty: choose d in D; d in p*bar a for p in P,a in A; Peirce gives
p in d*a. Duplication:
  D subset(D*A)*bar A and A subset bar D*(D*A).
Use distribution at the NONEMPTY evaluated meet P' to get
  P'*bar A=(P*bar A) intersect((D*A)*bar A) superseteq D,
  bar D*P'=(bar D*P) intersect(bar D*(D*A)) superseteq A.
The third PC coordinate is by definition.

R07 Bilateral support for two independently selected readings.
Under R06, for ALL independently chosen g,k in G,
  P intersect(h^g_st(D)*h^k_tu(A)) is nonempty.
Dependencies: R01-R04,R06,all-PC h.
Switch outer vertices by (g,0,k); PC becomes
  (gD:(gs)->t, kA:t->(ku), (g+k)P':(gs)->(ku)).
h yields a legal triangle. The selected first atom is g h^g_st(D);
the second is k h^k_tu(A), by R04's right-endpoint expression.
Undo those outer switches. The resulting third atom belongs to P' subset P.
No parameter for P was chosen and no equation on g,k was imposed.

R08 Explicit rotations preserve the two particular selected atoms.
Assume PC(D_st,A_tu,P_su); fix independently g,k,ell in G and put
a=h^g_st(D), b=h^k_tu(A), c=h^ell_su(P).
Then a in {c}*bar A and b in bar D*{c}.
Dependencies: R04,R07.
For a,c apply R07 to
  X=bar D:t->s, Y=P:s->u, Z=A:t->u,
with parameters g,ell. The hypotheses are the rotated original PC
inclusions. It gives a0 in A with T(bar a,c,a0), equivalently T(a,a0,c).
For b,c apply R07 to
  X=P:s->u, Y=bar A:u->t, Z=D:s->t,
with parameters ell,k. It gives d0 in D with T(c,bar b,d0),
equivalently T(d0,b,c). No g+k=ell relation appears.

R09 Original exact survivor restrictions with common c-support.
Define
  D'=D intersect({c}*bar A), A'=A intersect(bar D*{c}).
They are nonempty ORIGINAL exact menus, containing a,b, respectively.
Individual heredity gives h^g(D')=a,h^k(A')=b.
Moreover D' subset {c}*bar A' and A' subset bar D'*{c}.
Dependencies: R03,R08,original singleton/product/meet C08.
If d in D', choose a0 in A with T(d,a0,c). The same witness and d in D
show a0 in bar D*{c}, hence a0 in A'. Reverse symmetrically.

R10 Full independent rectangular readings.
For every PC triple of original exact menus, and ALL (g,k,ell) in G^3,
  T(h^g_st(D),h^k_tu(A),h^ell_su(P)).
Dependencies: R07,R09. Apply R07 to (D',A',{c}); it gives
{c} intersect(a*b) nonempty.
This covers coinciding owner tags and coinciding menu variables: only the
three FORMAL vertices are required to be distinct.

Source exports: lem:covariant-loop-full uses local absorption/uniform-positive
claims; lem:covariant-no-return uses positivity-tracked typed generation;
thm:covariant-HS uses no-return plus original engine C26; prop:moving-readings
uses R01-R10 together. No safe S assumption belongs in R01-R10.

Auxiliary equation bindings, if desired:
eq:covariant-HS -> original pure selector;
eq:shifted-reading -> R03 definition;
eq:reading-switch -> R05;
eq:reading-bilateral -> R06-R07;
eq:reading-rectangular -> R08-R10.

- The moving-readings branch never depends on S, augmented gates, the safe
  completion consumer, HKN reservoir, full_rows decoder, normalized MI
  construction or ordinary EPPA. This is an important DAG firewall.
- The safe completion branch uses a GIVEN all-finite-span strong
  S-amalgamation provider, including empty base. It does not derive this
  premise from its own completion conclusion.
- Pure owner covariance fixes literal colours. It cannot be replaced by an
  atom-permuting group; the two-element atom swap obstructs a fixed singleton.
- Same-sort symmetry alone does not guarantee the needed parallel-name
  separation under typed converse. Keep the symmetric-original RAW-name
  premise; the source's directed cross-sort two-colour example is a valid
  negative control.
- Unilateral G switches move BOTH labels and colours and need not preserve
  arbitrary safe S or full interpacket matrix safety. Rectangular readings
  alone do not discharge orbit-safe-strong or orbit-safe-all-row-interface.
- G may act nonfaithfully on owners; gamma lifts need not form a group section.
- Actual B025 source instances retain their current countability scope;
  the abstract finite-algebra calculations do not require countability.
- No optional global original raw-SAP injectivity is used for actual
  transversal restoration/primitivity/SAP.
- Only locality-absorb and locality-positive belong in B026; locality-bound
  and the completable HKN reservoir remain the next package.

No new mathematical computation was run in this review. Bounded controls for
independent G^3 parameters, repeated owner labels and nonfaithful owner action
would diagnose implementation mistakes but cannot certify the actual source
theorems or the remaining global candidate.

## Assembly clarifications

C24 (the ORIGINAL pure-owner selector) invokes the original conditional engine ONLY after C17 discharges its actual literal-name no-return premise. It is independent of S; the notes' augmented return proof also specializes to original H. C18-C23 are a separately proved finite-menu extraction. C25 binds their Q axioms to K using C10-C13 and actual SAP Peirce/fork support.

For the safe completion conclusion, A07 explicitly supplies the triangle-defined actual-age bridge; I11/C40 supplies its concrete B025 C34 specialization. The alternative I06 route requires an explicit cycle-witness induction: triangulate a specified cycle along a fan of chords in the complete legal diagram, use actual legal triangle witnesses and SAP to glue over each complete chord edge with fresh auxiliary vertices, and read the resulting closing colour in the positive strong path profile. Then apply semantic CCO and injectivization. Neither route assumes a bare arbitrary-age triangle principle.

The orbit bound after T can be implemented by running gates on the fixed image T(K), which is a current downward family by heredity/idempotence, or by bounding the larger K descent before precomposing T. In both versions at most the initial K nonsingleton-orbit count suffices.

No proper safe trace is required to be original exact. No strong identity atom, invariant origin/frame section, free owner action, relation g+k=ell or EPPA premise occurs. Actual B025 source countability is retained by its own provider scope, not by the abstract finite calculations.

## Source-premise separation

A01 is only the actual homogeneous symmetric-original finite typed SAP source. A05 adds semantic typed CCO for original exact/PC providers; A06 adds primitive individual sorts exactly at the stable-equivalence step C04; A07 supplies the actual triangle-defined age bridge at C33. I11 gives their concrete B025 full-owner instance under its unchanged standing source hypotheses. C01-C03 use SAP only. C04-C05 add primitivity but no CCO. C14-C17 use arbitrary-subset primitive powers and finite pure owner transformations, without exact-menu/CCO dependencies. C02 proves its duplication directly by SAP and does not import the named all-PC theorem I08. C06/C31 use the GIVEN strong-S spans and their supplied legal complete certificate, without CCO, primitivity or triangle-definedness.


### Final contract audit: abstract versus actual transport

C34–C39 use the explicitly supplied endpoint transport A04 and original exact algebra, with no I11/I12 dependency. The distinct-F-packet realization argument below is the concrete justification in C40; only that specialization imports B025 and its retained countability. The ambient Q in D09 is explicitly Gamma-invariant before generating F_Gamma(C); current J and generated F invariance alone would not suffice for an arbitrary Q. Actual Q=H and Q=K satisfy this by the proved transport/covariance laws. These are contract qualifications, not source theorem repairs.
