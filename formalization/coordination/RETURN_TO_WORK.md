# Návrat z Chat poolu na jeden Work tým

Zachováváme jednu frontu, stejné batch kontrakty, skutečné autorství a accepted
historii. Pro návrat není potřeba přepsat policy nebo znovu vydat staré batche.
Work projekt dostane [WORK_PROJECT_INSTRUCTIONS.md](WORK_PROJECT_INSTRUCTIONS.md)
a [FIRST_PROMPT_WORK.md](FIRST_PROMPT_WORK.md). Změnu musí skutečně požadovat
uživatel; žádný worker ji nesmí vyvodit jen z pomalé odezvy jiného projektu.

## Čistá fronta

1. Nech Chat projekty dokončit jejich claimy, cizí review a integrační zámky.
   Až jsou prázdné, stačí je přestat promptovat. Nemusí se mazat identity.
2. Novému Worku dej první prompt výše a pokyn, že přechod autorizuješ.
3. Work ověří aktuální main/CI, prázdné aktivní claimy a nulový integrační zámek.
   Navrhne jediný `switch_mode` event jako project 3/actor root:

```json
{
  "actor_id": "root",
  "user_authorized": true,
  "summary": "Skutečný uživatel autorizoval návrat; všechny aktuální Chat projekty jsou zastavené a fronta je bez aktivních claimů i review.",
  "target_mode": "work",
  "base_main_sha": "ACTUAL_GREEN_MAIN_SHA",
  "base_ci": {"run_id": 123, "head_sha": "ACTUAL_GREEN_MAIN_SHA", "conclusion": "success", "axiom_audit": "allowlist"}
}
```

Čísla a SHA se zjistí živě. Použij aktuální `coordination_queue.py` a exact-parent
non-force CAS podle QUEUE_OPERATIONS.md. Účinný STATE poté má `execution_mode:
"work"`; všechny staré package records zůstávají stejné. Neaktivní Chat klient
dostane odmítnutí nového claimu i při použití starých instrukcí.

## Pokud chceme převzít rozpracovanou práci

1. Koordinátor na skutečný pokyn uživatele zveřejní `pause_claims` se
   `user_authorized: true` a věcnou `summary` alespoň 80 znaků. Nové claimy se
   zastaví, dosavadní práce a její checkpointy mohou pokračovat.
2. Každému aktuálnímu Chat workeru pošli:

   > Připrav předání na Work. Nepřebírej novou práci. Publikuj všechny WIP
   > commity na původní větvi, aktuální PR/head, skutečný CI výsledek i při
   > failure a report s přesnými otevřenými důkazy. Zapiš aktuální checkpoint
   > a potom potvrď, že jsi zastavil všechny zápisy. Nic neresetuj na starší green.

3. Uživatel skutečně potvrdí zastavení všech workerů. Work znovu načte celé
   živé claimy i skutečné PR/branch heads. Je-li nový head ještě mimo ledger,
   nejprve jej worker musí checkpointnout; běžící CI se může dokončit i chybou.
   Nedokončené či nepublikované WIP se nesmí při přepnutí ignorovat.
4. Nejdřív dokonči každý případný integrační zámek, včetně main CI po merge.
   Při merged-main failure zachovej zámek; tento režimový event ho neobejde.
5. Jediné `handover_mode` přenese **všechny** skutečné aktivní claimy.
   Data obsahují výše uvedený green main/CI a skutečné uživatelské zdůvodnění,
   `target_mode: "work"`, `previous_workers_stopped: true` a `transfers`:

```json
{
  "package_id": "B049",
  "previous_owner_project_id": 4,
  "new_owner_project_id": 3,
  "head_sha": "LATEST_CHECKPOINTED_WIP_SHA",
  "pr_number": 999,
  "branch": "chat/chat-1/B049"
}
```

Každý řádek musí souhlasit se skutečným STATE; nevymýšlej příkladové hodnoty.
Předání ponechá claim revision, původní base/CI, všechny dosavadní autory,
původní branch/PR/head, observed failure a last green checkpoint. Celý původní
record se zachová v handover history. Nový vlastník se přidá mezi přispěvatele
a pokračuje z nejnovějšího WIP. Účinný stav se vrací do IN_PROGRESS a vyžaduje
nové skutečně neautorské review; staré review/approval zůstane pouze v historii.

Work standardně drží dva aktivní batche. Při předání tří buď nejdřív jeden
dokonči, nebo dodej `third_batch_exception` se skutečným disjunktním plánem,
dedikovaným implementerem a přesně ukotvenými dvěma ostatními heads podle
`claim_third`. Nejde o formální výjimku jen proto, že starý pool měl tři členy.

## Znovu zpátky do Chatu

Při čisté frontě `switch_mode` s `target_mode: "chat"`. Při WIP stejný úplný
pause/stop/handover postup, ale každý claim dostane odlišného cílového Chat
vlastníka z aktuální policy. Nejvýše jeden neuzavřený batch na projekt.
Role a autorství se nemažou a souhlasy se nepřenášejí.

## Lokální Lean a kontrolní role po restartu

Nový Work musí znovu ověřit instalaci přesného Lean/Lake toolchainu, manifest
a malý inkrementální build. Lokální cache nemusí přežít dočasné prostředí;
GitHub source, CI cache a protokol jsou samostatné. Piny se kvůli setupu nemění.
Při konkrétní síťové překážce ulož přesnou chybu a přejdi na CI bez opakovaných
dlouhých stejných pokusů. Existující scripts pro skutečné Mathlib kořeny a
úplné provider/project cache guards zůstávají v platnosti.

Work má samostatného skutečně neautorského readera. Pokud původní registrovaný
agent už není dostupný, nepředstírej jeho pokračování pod stejnou identitou:
zaregistruj skutečně nového readera explicitním reviewer_recovery postupem.
Ten už podporuje bootstrap neautorské kontroly vlastní registrační změny.
Původní review ani metadata nejsou náhradou nového skutečného celého čtení.
