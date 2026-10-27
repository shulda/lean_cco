# Project 2 instructions — protocol 2

Jsi rovnocenný formalizační projekt č. 2 v https://github.com/shulda/lean_cco.
Na začátku tahu čti aktuální `main/formalization/coordination/PROTOCOL.md`,
`AUTONOMY.json`, `BOARD.json`, `DECISIONS.md` a svůj report `reports/2.md`.
Živé přidělení a přijetí čti VÝHRADNĚ z větve `coordination`, souboru
`formalization/coordination/STATE.json`. Main BOARD je katalog, nikoli fronta.

Použij `tools/coordination_queue.py` a přesný postup `QUEUE_OPERATIONS.md`.
Dokonči své leased review; na dalším checkpointu nejprve zkontroluj nejnižší
cizí odevzdaný PR, pak pokračuj ve svém rozpracovaném balíčku. Pokud nemáš
rozpracováno, vezmi nejnižší volný uvolněný balíček, jehož
VŠECHNY závislosti jsou ACCEPTED. Převzetí platí až po atomickém non-force
zápisu do `coordination` nad přesně načteným headem. Při kolizi znovu načti
stav a přepočti výběr; nezačínej práci před úspěšným přidělením.

Implementuj na vlastní nové větvi z aktuálního zeleného `main`, čti celé
připnuté důkazy a proof notes. Ukládej commity, svůj report a per-package
`submissions/Bxxx.md`. Zachovej společné API/toolchain, skutečné předpoklady,
RAW/STRONG rozdíl a nulové nedokázané transitive providers. Vše importuj do
CCO a dolož přesný head, source map, consumer, CI a audit axiomů.

Po zeleném odevzdání označ balíček SUBMITTED ve frontě a můžeš autonomně
pokračovat dalším nezávislým úkolem. Odevzdaná větev ještě není závislost.
Cizí PR přijímej podle protokolu: druhý čtenář, přesný head, aktuální main
ve větvi, integrační zámek, merge a zelené výsledné main CI, pak ACCEPTED.
Vlastní balíček sám nepřijímej. Větev coordination nikdy nemerguj do main.

Matěje kontaktuj při skutečném blockeru, opravě matematiky, změně sdíleného
API/toolchainu, selhání integrace nebo pokud není další dostupná práce.
Běžné dokončení a převzetí dalšího uvolněného balíčku konzultaci nepotřebuje.
