# Koordinace z Chatu bez lokálního Pythonu

Autor kódu používá vlastní branch/PR přes skutečné GitHub nástroje. Pro změny
fronty může místo lokálního validátoru vytvořit malý JSON soubor na větvi
`coordination-requests`. Workflow `Coordination requests` zpracuje **celý aktuální
inbox** pomocí kódu z důvěryhodného mainu. Nikdy nespouští kód request větve.
Neprovádí automatické matematické review ani samotný merge PR.

Kanonická autorita zůstává `coordination:formalization/coordination/STATE.json`.
`STATUS.json` obsahuje jen malý odvozený přehled a `next_actions`. Jeho revize musí
odpovídat skutečnému STATE; samotné doporučení nedává vlastnictví. GitHub request
commit také není claim. Zápis je účinný až po validovaném exact-parent non-force
CAS a ověřeném receipt. Přímé použití Python helperu/CAS zůstává možné ve Worku.

## První test

Vymysli nový unikátní ID, například `20261031_status_c8d46a2f`. Pro Chat 1 vytvoř
na `coordination-requests` nový soubor
`coordination/requests/chat-1/20261031_status_c8d46a2f.json`:

```json
{
  "schema_version": 1,
  "request_id": "20261031_status_c8d46a2f",
  "actor_id": "chat-1",
  "project_id": 4,
  "policy_revision": 13,
  "operation": "status"
}
```

**Vždy načti policy_revision z živého STATE; 13 je pouze výchozí příklad.
Během nasazování může main už obsahovat novější policy, zatímco starý ledger
platí pod skutečným infrastrukturním zámkem.** Chat 2 má
actor `chat-2` a project 5, Chat 3 actor `chat-3` a project 6. Každý request má
nový ID a soubor; příklad ID nekopíruj opakovaně. Existující request nikdy neměň.
Nový chat v témže skutečném projektu používá stále stejnou identitu, nové ID
requestu a živý stav. Nedoplňuj autorství pod jiným projektem.

Počkej na workflow a přečti na aktuálním headu coordination soubor
`formalization/coordination/requests/results/chat-1/20261031_status_c8d46a2f.json`.
Výsledek obsahuje request blob, skutečného rodiče coordination a odpověď:

- `applied`: event je účinný na uvedené `effective_revision`; ověř ho ve STATE.
- `no_change`: nic nebylo přidělené, přečti `next_action` (např. čekání na přípravu).
- `rejected`: nic se nestalo; přečti důvod, obnov kontext a pošli nový request ID.

Chybějící receipt znamená nedokončené zpracování, nikoli automatické přidělení.
Nezalož kvůli tomu druhý spekulativní claim. Pokud workflow selhalo přechodně,
nový `status` request ho znovu spustí a celý dosud nevyřízený inbox se zpracuje.
Při redelivery starého souboru se existující receipt nepřepočítá a claim neopakuje.
Při chybně změněném starém requestu platí původní receipt svázaný s původním
blobem; opravu pošli novým ID. Nezveřejňuj žádný GitHub token.

## Převzetí nejbližší práce

Použij stejné pole identity a `operation: "claim_next"`. Není potřeba
`expected_revision`: nejnižší aktuální volný dependency-ready batch vybírá
validátor až na serveru, takže dva souběžní klienti nemusí oba prohrát na stejném
čísle. Broker sám ověří green CI/audit aktuálního mainu a respektuje režim,
kapacitu, vlastnictví i priority oprav/review. Když `next_action` nedoporučuje
claim, dostaneš `no_change`, nikoli jinou automaticky provedenou práci.

Po `applied` zkontroluj skutečný STATE včetně claim revision, own project/actor,
base main/CI a `branch`, například `chat/chat-1/B049`. Teprve potom vytvoř
tuto větev z přesného `base_main_sha`, přečti kontrakt/zdroj/notes a formalizuj.
Při souběhu zápisů broker starou STATE proposal nikdy pouze nepřerodí na nový
rodič: načte čerstvý stav a znovu vybere práci/validuje. Žádná dependency z PR.

## Ostatní eventy

Načti skutečný STATE a jeho `revision`. Request má `operation: "event"`,
`expected_revision`, `event` a `data` podle [QUEUE_OPERATIONS.md](QUEUE_OPERATIONS.md):

```json
{
  "schema_version": 1,
  "request_id": "UNIQUE_NEW_ID",
  "actor_id": "chat-1",
  "project_id": 4,
  "policy_revision": 13,
  "operation": "event",
  "expected_revision": 400,
  "event": "submit",
  "data": {
    "package_id": "B049",
    "head_sha": "FULL_40_CHARACTER_ACTUAL_HEAD",
    "pr_number": 999,
    "ci": {"run_id": 123456},
    "report_path": "formalization/coordination/submissions/B049.md"
  }
}
```

Čísla/heads jsou pouze ilustrace; zjisti je skutečně. Odevzdání dál vyžaduje
celý kontrakt bez otevřených providerů. Broker CI data nezískává z tvrzení
klienta: čte skutečný run/head/job/log, allowlist audit, všechny aktuální CCO
moduly a piny/úplné cache guards obou providerů. Zelený cizí head nestačí.
`checkpoint` uvádí skutečné dokončené `observed_ci` i při failure.

Review report ukládej pod vlastní cestou, např. `reviews/B049-chat-2.md`,
samostatným reportovým commitem na coordination; nesmí změnit STATE. Uveď
celý head a skutečnou identitu `chat-project:cco-chat-2`. Před `review` zveřejni
neautorství a plán čtení; před `approve` doplň vlastní skutečné úplné čtení,
zdroj/provider/consumer/CI findings a rozhodnutí. `independence` obsahuje
`identity`, `non_author: true`, věcnou `summary` alespoň 80 znaků a celý
`report_path`. Nic neschvaluj podle cizího reportu. Při účasti na implementaci
se přidej mezi autory přes vlastníka a další review přenech jinému skutečnému
neautorovi; label ani nový chat stejného projektu tě neosamostatní.

Po cizím schválení `start_integration` uvádí schválený head, aktuální
`base_main_sha`, `head_contains_main: true` a `ci.run_id`. Broker čte skutečné
PR refs a ancestry. Po účinném zámku **znovu načti main a PR**, a pomocí GitHub
nástroje proveď expected-head `merge_method: merge`. Merge provádí uživatelský
GitHub nástroj. Poté vždy skutečně ověř spuštění main CI; broker se omezuje
na koordinaci a zdrojové PR sám nemerguje. Vyčkej skutečný main CI
a pošli `accept` s `integration_commit` a `main_ci.run_id`. Broker ověří merged
PR, schválený strom, pořadí rodičů i skutečný úspěšný main audit. Cizí zámek
respektuj. Po již merged selhání zámek drž; cancel platí jen před merge.

Specifické eventy se starou `expected_revision` jsou odmítnuty. Receipt
zahrnuje source/request blob a odpověď; nový STATE event nese i `request_id`.
Při změně jen reportů může server zvolit novější rodičovský commit se stejnou
STATE revision — vždy znovu validuje čerstvý ledger a provede CAS nad tímto
přesným rodičem. Běžný broker smí zapsat pouze STATE, vlastní receipt a STATUS;
nikdy BOARD, policy ani zdrojové soubory. Chybné requesty nezastaví jiné workery.

Workflow má jednu concurrency skupinu. GitHub může nahradit čekající běh novějším;
proto každý běh čte celý aktuální inbox, nikoli jen soubor z původního eventu.
Dokončené requesty zůstávají jako historie, ale neposílají se znovu do validátoru.
Pokud se mění samotný `coordination.yml`, aktualizuj také inbox větev mergem
nového mainu, se zachováním všech requestů; nikdy ji neresetuj.

Pokud hlavní CI vlastního či cizího integračního zámku ještě běží, finish
zůstává prioritou, ale můžeš využít optional_review_while_ci_pending nebo
optional_repair_while_ci_pending. Samostatná cizí kontrola a oprava již vlastněného
batchů nezískává nový claim. Oprava během cizí integrace zůstává na původním
připnutém zeleném base (server ho ověří), finální integrace opravy pak znovu
vyžaduje aktuální main v headu, nový CI a skutečný review příslušného headu.

Pro jednorázový test serverových oprávnění lze u status requestu přidat
`data: {"verify_ci": true}`. Broker navíc načte skutečný úspěšný aktuální main
run/job/log, zkontroluje všechny source/provider guards a audit a uloží jejich
receipt. Nevytváří claim ani nový Lean build; běžné status requesty tento
opakovaný rozsáhlejší CI read nepotřebují.
