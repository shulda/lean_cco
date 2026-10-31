# Jeden Work tým nebo samostatné Chat projekty

Policy `AUTONOMY.json` registruje role; živý `execution_mode` v
`coordination:formalization/coordination/STATE.json` vybírá `work` nebo `chat`.
Režim se při běžném návratu přepíná jedním validovaným CAS eventem, bez nové
politiky, přepisování BOARD nebo resetu historie. `claims_paused` dočasně
zastaví pouze nové claimy; dokončení, opravy a skutečné review pokračují.

| Režim | Implementace | Kapacita | Kontrola |
|---|---|---|---|
| work | Jeden tým, project 3, actor root; oddělené worktrees/subagenti | Standardně 2 neuzavřené batche, třetí jen s konkrétním plánem skutečně nezávislé aktivní práce | Samostatný skutečný neautorský registrovaný reader |
| chat | Nové projekty dle `chat_project_actors`, při prvním nasazení project 4/5/6 a actor chat-1/2/3 | Nejvýše 1 neuzavřený batch na projekt, při prvním nasazení 3 dohromady | Projekt kontroluje jen batch, na jehož žádné části se nikdy nepodílel |

Všechna ACCEPTED pravidla, source pin, skutečné hypotézy/provider discharge,
samostatné neautorské schválení, expected-head merge, jediný integrační zámek
a CI/audit přesného PR i výsledného mainu platí v obou režimech. SUBMITTED,
REVIEWING, INTEGRATING, CHANGES_REQUESTED a BLOCKED dál zabírají slot.
Zelený sibling neposkytuje závislost. Kontrola nemůže být jen přejmenovaný autor.

Role Chat projektu platí napříč jeho chaty: nový chat ve stejném projektu
nevynuluje autorství. Každý projekt má samostatné stabilní actor/project ID;
historické původní projekty 1/2 ani Work tým 3 se jako nové Chat projekty
nepoužívají znovu. Skutečnou identitu a neautorství uvádí každý kontrolor ve
vlastním reportu. Pokud začne psát opravy kontrolovaného kódu, stává se autorem
a další kontrolu musí vykonat jiný skutečný neautor.

Chat má prioritu: dokončit vlastní zámek či rozpracovanou kontrolu, opravit svůj
batch, provést čekající cizí kontrolu, pokračovat ve vlastním důkazu, jinak
claimnout nejnižší vydaný dependency-ready batch. V průběhu cizí main CI může
pokračovat vlastní nezávislá implementace. Schválený autor i reviewer mohou
zajistit běžnou integraci, vždy pouze pod jedním veřejným zámkem.

## Zprovoznění

Použij [CHAT_PROJECTS.md](CHAT_PROJECTS.md): každý řádek má hotové projektové
instrukce i první prompt s konkrétní identitou. Připoj GitHub nástroje pro
repozitář `shulda/lean_cco`. Ověř skutečné čtení, zápis souborů, větve, PR
a merge; samotný čtecí konektor nestačí. První prompt tuto schopnost ověřuje.
Dokumentace OpenAI dostupnost pluginů podmiňuje plánem/nastavením/pluginem;
bez skutečného zápisového nástroje se publikace nesmí předstírat.
Zdroj: https://learn.chatgpt.com/docs/use-chatgpt (ověřeno 31. října 2026).

Žádný lokální Lean, Python, token ani terminál nejsou pro koordinační requesty
nutné. [CHAT_REQUESTS.md](CHAT_REQUESTS.md) vysvětluje malý JSON inbox,
automatickou validaci na GitHub Actions a účinné výsledky. Lean běží v obvyklém
CI s dosavadními cache a axiom auditem; broker sám žádné důkazy neschvaluje.
Není přidán žádný placený model/API ani nový externí běžící server.

## Přidání a odložení projektu

Odložení prázdného projektu nevyžaduje úpravu politiky: dokonči jeho claim,
review lease a integrační zámek a prostě ho přestaň promptovat. Registrace
a historie zůstávají, aby nemohl později přejmenováním obejít neautorství.
Projekt s rozdělanou prací se nejdřív výslovně předává, nikoli tiše odkládá.

Další nový projekt je malá append-only policy změna, nikoli nový protokol:

```bash
python3 tools/configure_execution_profiles.py --add-chat-worker 4 \
  --output /tmp/AUTONOMY-next.json --manifest-output /tmp/profiles-next.json
```

Založ infrastrukturní PR z aktuálního mainu, použij navrženou policy, spusť
`python3 tools/check_formalization_coordination.py` pro generování nové sady
instrukcí a proveď běžné testy/nezávislé review/exact PR CI. V `start_infrastructure`
je `profile_deployment` manifest celých starých/nových snapshotů. Po merge a
zeleném skutečném main CI použij `promote_profiles` s explicitními starými/new
snapshoty. Při pouhém přidání projektu lze zachovat aktuální rozpracované claimy
a review beze změny; nepřepínej současně režim. Staré identity/role, matematika,
catalogue i přijetí jsou chráněné. Nový projekt začne až po účinné aktivaci.

## Návrat a předání

Viz [RETURN_TO_WORK.md](RETURN_TO_WORK.md). Čistá fronta znamená jeden event
`switch_mode`; při WIP použij `pause_claims`, skutečné zastavení všech workerů
a úplné `handover_mode`. Nový vlastník zachová přesnou větev/PR/head a celé
staré claim/base/CI/autor/history údaje. Starý review zůstane v historii, ale
účinné schválení se nepřenáší. Nejnovější WIP se nikdy neresetuje na starší green.

Při třech přebíraných batchích musí Work dodat skutečný třetí-slot plán podle
dosavadních pravidel; jinak nejprve jeden dokonči. Po přidání více Chat projektů
nejprve sniž počet neuzavřených claimů na kapacitu cílového profilu.
