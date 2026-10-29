# B035 — full tuple codes, Ramsey readout and fixed-host EP

Frozen source `490c3f36d85db5a0b3ced0598e6c431825254ec5`;
`sections/full_code_tuple_ep_transfer.tex`. This private module prepares
six results, two labelled equations, 12 definitions, 51 claims and eight
tasks. No mathematical provider is imported. Hidden Ramsey and hidden EP
are separate conditional inputs, not external theorems proved here.
Source TeX and the separate human edition remain unchanged.

Reconstruction uses only finite full tuple codes and partial unary terms.
Ramsey readout adds hidden Ramsey, without cofinality or EP. The ambient
root-cover lemma and same-host lemma are independent additional tools.
Abstract EP uses its four explicit contracts; the last corollary discharges
those contracts in the ambient full-code setting. Added expansion functions
require the normalization argument below before a restriction is legal.

## N01: Typed partial terms, marked roots and quantifier-free transport

**D01–D02; C01–C02.** A hidden embedding is an injective sort map reflecting
all relations AND partial-function domains, and preserving defined values.
For a unary term, prove by induction on its composition length that its
definedness agrees in source and target, and that defined values commute
with the embedding. At a composition F(t(x)), first apply induction to t,
then reflect F's applicability at that actual value. Undefined inner values
stay undefined. Identity terms are included.

Atomic term equalities and relation instances are consequently preserved
and reflected under the same partial-term semantics. Induction over Boolean
connectives, including negation, transports every quantifier-free formula.
This justifies preservation and reflection of each root compatibility
formula delta. No existential witness outside the source is used.

Roots are literal TAGGED tuples, not tuple equivalence classes. A coordinate
term selects one of the root's ordered coordinates and applies a typed
unary normal form. Normal forms agree with their terms as PARTIAL functions:
both domains and values agree uniformly, including nowhere-defined
composites. Equality only on the common defined domain would not suffice.

Finitely many tags, finite coordinate tuples and finite lists of forms give
a finite code signature. Tags distinguish equal tuples of different tags.
Zero-coordinate roots, if allowed, have at most one root per tag; since the
hidden language is nullary-free, their quantifier-free compatibility has
constant truth. They do not create an injectivity exception.

## N02: The full code reconstructs a marked induced support

**D03–D04; C03–C08.** For a fixed source root set A, list its DEFINED
presentations (a,j,t), where t is a normal form on coordinate j of root a.
Every actual unary-chain value has such a presentation by normal forms.
Conversely each presentation is an actual chain value, so these values are
exactly the unary-generated support. Normalizing F composed with t shows
the set is closed under every already-defined named unary value.

The diagonal code E_tau,tau(a,a) says exactly that tau(a) is defined.
Thus the code determines which presentations exist, not just their sort
applicability. Among the defined presentations, the full E codes identify
exactly equal hidden values, within one root and across different roots.
Their quotient is the hidden support's underlying typed set. Coherence is
supplied by the assumption that A belongs to the actual induced full-code
age; this is not a theorem about arbitrary uninterpreted code structures.

Every hidden unary predicate is read using a presentation of its argument.
Every hidden binary relation or comparison is read using two presentations,
possibly from the same root. Equality codes make these readings independent
of representatives. Keeping all same-root instances is essential even if
A has only one visible root.

For a defined presentation tau(a), compute the chosen normal form of
F composed with tau. Its definedness code determines exactly whether F
is defined at the corresponding quotient point; its equality class gives
the value when defined. This recovers the entire partial-function graph,
including its domain. It does not assume that F is total.

These steps reconstruct all hidden data on the actual induced support.
Any two identifications agreeing on the root coordinates agree on every
defined unary chain, hence every support point. The isomorphism is unique
OVER THOSE MARKED COORDINATE PRESENTATIONS.

The unmarked hidden structure h(A) need not remember which subset A of all
possible roots was selected. That selected root set and its presentations
remain part of the source data in the embedding correspondence.

## N03: Both embedding constructions and their naturality

**D05; C09–C15.** Given a visible full-code embedding f, define

\[
 \overline f(\tau(a))=\tau(f(a)).
\]

Definedness reflection ensures that every required target presentation
exists. Equality preservation gives well-definedness on the quotient, and
equality reflection gives injectivity. The full unary/binary codes give
relational inducedness; the composition/definedness calculation in N02
gives reflection of function domains and preservation of values. Thus this
is an actual induced hidden embedding into the host.

Conversely, for a hidden embedding g from h(A), apply g to each root's
coordinates and keep its tag. N01 transports delta, so the image is a valid
root. Two distinct roots either have different tags or differ at some
identity-coordinate value; injectivity of g preserves that distinction.
The zero-coordinate case is already separated by tags. Term transport and
hidden inducedness preserve and reflect every full-code predicate, giving
an induced visible root embedding.

Starting with f, its extension agrees on all root coordinates, so reading
the roots back returns f. Starting with g, evaluating each presentation
shows that extending the induced root map returns g. This proves the
bijection of ALL embedding sets in FCODE, not merely a surjection on
unmarked copies or on isomorphism types.

For a visible a:A->B, the same presentation rule lands in h(B), rather than
requiring the full ambient hidden host. Uniqueness over coordinates implies

\[
 h(b\circ a)=h(b)\circ h(a),\qquad h(\operatorname{id})=\operatorname{id}.
\]

Direct evaluation gives the same naturality. Neither Ramsey, EP, cofinality
nor a same-host theorem occurs in C01–C15. Multiary functions or higher
hidden relation arities are outside this unary/binary code theorem.

## N04: Ramsey readout colors all hidden embeddings

**D06; C16–C20.** Given finite A^o,B^o and k, their generated supports are
actual finite H^o members by heredity. Use the supplied hidden Ramsey
property to choose

\[
 D^o\longrightarrow(h(B^o))^{h(A^o)}_k.
\]

Take any coloring of Emb(A^o,N(D^o)). Through the inverse of FCODE this is
a coloring of ALL hidden Emb(h(A^o),D^o). Hidden Ramsey supplies a g from
h(B^o) into D^o constant on its composites with every h(A^o) embedding.
The reverse FCODE construction sends g to a copy of the SELECTED B^o
roots inside N(D^o).

For each a:A^o->B^o, N03 supplies h(a):h(A^o)->h(B^o). Its composite with g
has the hidden common color; naturality identifies that color with the
corresponding visible composite. This is the desired visible arrow.
N(D^o) is finite, including any zero-coordinate tags, and belongs to V^o.

Empty sources or empty generated supports use the same embedding
correspondence. A hidden witness D^o may have orphan points outside
h(N(D^o)); the proof never replaces it by that support and never assumes
a root cover. No visible SAP, EP, or extra visible tuple order is needed.
An order already present in the hidden language remains in the full code.

## N05: Ambient root cover gives a finite cofinal host

**D07; C21–C25.** For a finite hidden D, embed it into the possibly infinite
ambient P. For each of its finitely many image points z choose a valid
root r_z and a defined coordinate-term value equal to z. Close ALL
coordinates of ALL these finitely many roots under the actual unary
functions of P, obtaining E.

Only finitely many coordinate points are chosen. The finite normal forms
from their input sorts make this closure finite. It is old-unary-closed,
induced and contains the embedded D. Since each chosen root's coordinates
lie in E, N01's partial-term/qf argument makes that SAME tuple valid in E.

Every point of E, not merely each original z, is by construction an actual
unary-chain value of a coordinate of a chosen r_z. Those roots all lie in
N(E), hence E is contained in h(N(E)). Conversely E's unary closedness
gives h(N(E)) contained in E. The equality holds on this very E, proving
RC and cofinality. Empty D can use the empty coordinate closure. No Ramsey,
EP, CCO, SAP, finiteness of P or ambient homogeneity is needed.

## N06: Canonical reducts and lifting every expansion to the SAME E

**D08–D09; C26–C31.** Fix a full-root-generated E and its complete
unexpanded visible root object B=N(E). A competing allowed B^o has an
actual induced full-code realization in some finite hidden D^o. Its
generated support h(B^o) is an induced expanded H^o member by heredity,
uniquely reconstructed over the marked root coordinates by N02–N03.

The explicit support/reduct compatibility identifies its unexpanded reduct
with the canonical h(B), over the SAME coordinate presentations. Since E
is full-root-generated, h(B)=E. This is stronger than an unrelated abstract
isomorphism type: it supplies the root-coordinate identification needed
to transport the structure onto the existing E.

Transport all expanded relations, comparisons, function values and domains
along this marked identification. Isomorphism-closure gives an allowed
E^o whose reduct is exactly E. Root tags and delta are unexpanded, so the
root carrier remains exactly B=N(E), independently of the competing code.
Marked transport reproduces EVERY code of B^o on that carrier, rather than
merely a subcode on a selected subset of roots.

All points of E have root-term presentations. The complete code therefore
determines every expanded relation and function domain/value there. With
the marked identification fixed, any two lifts coincide. Orphans would
permit invisible expansion data, so uniqueness without full generation is
not automatic.

Relational expansions retaining unary functions satisfy the function part
of reduct commutation automatically. Expansions adding functions need the
explicit hypothesis: finite normal forms alone do not prevent their
generated support from acquiring extra old points. N09 gives a concrete
idempotent-function countercheck. This local same-host lemma uses neither
Ramsey, EP nor ambient cofinality.

## N07: EP normalizes the witness before legal restriction

**D10–D12; C32–C39 and C48–C51.** The EP convention is

\[
 \forall A^o\ \exists B\ \forall\text{ allowed }B^o\
       \exists\text{ expanded embedding }A^o\hookrightarrow B^o.
\]

This fixed-expanded-source convention is explicitly stated in
`sections/expansion_property_unfiltered.tex`. It requires one unexpanded B
chosen before any competing expansion. No simultaneous witness for all
expansions of the same A or extra JEP premise is added here.

Fix A^o. Abstract contract (i) supplies H_A^o, a compatible hidden expansion
whose reduct is the OLD-unary-generated h(A), with its marked source
roots. Hidden EP supplies an unexpanded D such that every expansion D^o
contains H_A^o. This choice precedes any visible competing expansion.

There is a real extra step for expansions that ADD unary functions.
An old induced D inside E need not be closed under the added functions of
an arbitrary E^o. Ordinary heredity alone does not justify the printed
restriction step in that general scope. C48–C51 expand the proof using
the hypotheses already present, as follows.

**C48: normalize using only OLD functions.** Put

\[
 D_0=h_{\rm old}(N(D))\subseteq D.
\]

D is finite, so this old-unary closure is finite, without a further
normal-form bound. It is an actual old induced closed substructure.
Every root of N(D) has all coordinates in D0 by construction. Quantifier-free
validity reflects along the old induced inclusion D0->D, so it remains a
valid root in D0. The converse follows under inclusion, hence

\[
 N(D_0)=N(D),\qquad h_{\rm old}(N(D_0))=D_0.
\]

This includes empty root sets and zero-coordinate tags. Do not use the
ADDED expanded functions in this normalization.

**C49–C50: reasonableness retains the EP-witness property.** Take ANY allowed
expansion D0^o. Reasonableness lifts the chosen old inclusion D0->D to an
expanded embedding into SOME allowed D^o on D. This makes D0^o an actual
expanded closed substructure in that chosen extension; it says nothing
about an arbitrary expansion of D.

Hidden EP gives u:H_A^o->D^o. Each image source root is valid in N(D),
by quantifier-free transport in the OLD language. Every source point is
an OLD unary term of a source root coordinate, because the reduct of
H_A^o is exactly old-generated h(A). Its image therefore lies in D0.
Thus the WHOLE image of u is in D0; since the given D0^o inclusion is an
actual expanded embedding, u factors as an expanded embedding through it.
This works for every D0^o. Consequently D0, not just D, is an EP witness
for the particular H_A^o.

**C34–C35: choose and fix the visible host.** Apply abstract cofinality (ii)
to D0 and fix j:D0->E with h(N(E))=E. Put B=N(E)|_V. E, j and B are all
fixed now. Given ANY allowed expansion B^o, abstract same-host contract
(iii) supplies an allowed E^o on this exact E with code B^o.

**C51: prove expanded closure before restricting.** Inside that arbitrary
E^o take its induced visible full-code subset on

\[
 S=j(N(D_0)).
\]

Its canonical OLD generated support is j(D0), since D0 is old-root-generated
and j preserves the old term values. Abstract contract (i), in its explicit
coordinate-preserving support/reduct form, says its ACTUAL expanded
generated support has reduct exactly that same marked old support. Hence
its underlying set is j(D0). Being an actual generated expanded support,
it is closed under every added function as well. Thus j(D0) really is an
induced expanded substructure of E^o.

**C36–C38: restrict and read out.** Restrict there and pull back along the
fixed j to obtain an allowed D0^o. Its inherited EP-witness property gives
H_A^o->D0^o, hence H_A^o->E^o. Apply the REVERSE FCODE construction to the
marked source roots. Qf validity puts them in fixed N(E); full code and
contract (iv)'s fine-atom faithfulness give A^o->B^o.

This works for EVERY B^o of the B chosen earlier, proving EP. Unique
extension of a map already known visible does not alone supply this
reverse hidden-to-visible construction; the surrounding full-code setting
does. Hidden Ramsey is not used. The abstract theorem uses contracts
(i)–(iv), not the concrete cofinality or same-host proofs as extra inputs.

For purely relational expansions retaining functions, the original
restriction step is automatic. The normalized proof above covers the
source's broader added-unary-function scope without an extra closure
premise. It uses reasonableness substantively. We retain the stated
cofinality hypothesis and do not claim that it is logically indispensable
under every stronger combination of the other full-code contracts.

## N08: The ambient corollary discharges the four contracts

**C40–C43.** Under the corollary's actual application premises:

- Canonical unexpanded fine-code reconstruction and compatibility of the
  reduct of expanded generated supports give contract (i).
- Ambient root coverage plus N05 give finite cofinal full-root-generated
  E above each finite hidden D, supplying (ii).
- For EACH such E, instantiate the bound local same-host lemma N06 with
  B=N(E). Exact full codes and the same coordinate-preserving reduct
  compatibility yield (iii) for EVERY allowed B^o.
- N03 supplies both directions of the embedding correspondence, unique
  extensions and root transport. Together with the explicitly supplied
  original fine-atom faithfulness, these give (iv).

Now apply the CONDITIONAL abstract transfer N07 with these contracts
discharged and the supplied hidden EP/reasonable precompact expansion
setting. There is no remaining abstract four-contract axiom to assume in
addition to those concrete premises. The fine-atom definability of a
particular MI/MR encoding, however, is an application obligation, not a
conclusion of this abstract module. No CCO, SAP or EPPA input enters.

## N09: Bounded diagnostics and exact scope boundaries

**C44–C47.** Controls independently enumerate small partial-unary structures,
root tuples and maps, and compare their actual hidden/visible embedding
sets. They also exercise the boundaries below. Variants described here
have the direct human arguments indicated; finite searches do not prove
unbounded Ramsey, EP or the general reconstruction theorem.

1. A singleton with undefined F versus F fixed at that point requires
   same-root definedness code E_F,F. Retaining only sort applicability or
   equality where both evaluations exist loses this distinction.
2. A one-root pair (a,b) with a!=b versus (c,c) requires same-root coordinate
   equality. Their unmarked one-root reducts can agree after that code is
   omitted, but their hidden supports have different sizes.
3. Roots (a,b),(b,c) versus two disjoint target pairs require CROSS-root
   equality. Without it the shared source coordinate could be assigned
   incompatible images.
4. Omitting a hidden order changes the embedding sets. On a two-point
   unordered source, a fixed order on a host colors an embedding according
   to whether its two images increase or decrease. Every two-point image
   has both orientations, so no copy is monochromatic for embeddings.
   This is why an existing hidden comparison must remain in the full code.
5. A point not generated by ANY valid root defeats the full-root equality.
   It may carry invisible expansion data and destroy uniqueness of a lift.
   More concretely, valid roots can be singleton Root points, with a
   hereditary expanded class allowing a red root singleton but forbidding
   red roots whenever a nonroot orphan is present. The singleton's allowed
   red code then has no lift on that same orphan-containing host. This
   lemma-level boundary is not claimed to be a reasonable EP expansion.
6. Let unexpanded E be a single Root point a. Add total idempotent F and
   allow a two-point expanded host a,b with b nonroot and F(a)=F(b)=b.
   The single visible root has F(a)!=a, impossible on the SAME singleton E.
   Normal forms id,F are finite. It is the support-reduct commutation,
   not finite normalization, that fails: expanded support has two points,
   canonical old support one.
7. For the printed EP restriction step, a finite extra-function structure
   can have an old induced D that is not expanded-closed, although its
   old-root-generated D0 is closed. The control checks the actual domains
   and generated supports before permitting a restriction. In general
   C48–C51 establish the corresponding closure using reasonableness and
   the full-code reduct contract; the finite instance is a diagnostic.
8. A favorable chosen expansion does not imply success for every competing
   expansion. Likewise a host chosen after inspecting an expansion does
   not establish a single host working for all expansions. A finite
   incidence-matrix countercheck isolates this logical quantifier issue;
   it is not a structural counterexample satisfying all source hypotheses.

Omitted code may be removed only after a separately proved uniform
quantifier-free definability result preserving the embedding sets. Arbitrary
visible predicates, tuple quotients, representative selections, multiary
hidden functions, or missing higher-arity relation information are outside
the stated full-code theorem. No such encoding change is made here.

The printed EP restriction argument has been expanded under existing
hypotheses, and the article feedback queues that proof insertion for the
human edition. This private registration changes neither public Work
coordination nor the overall EPPA candidate/HKN adapter obligations.
