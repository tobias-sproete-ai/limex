# SFH FUZZI — reproduzierbarer Software-Stresstest

SFH FUZZI belastet den deterministischen LIMEX-Funktionskern mit hoher logischer Ereignisdichte, Reihenfolgeänderungen, Fragmentierung, Dropouts, Hash-Manipulation und harten Größenlimits. Zusätzlich prüft die Capsule einen getrennten Global-Hold-Release-Referenzadapter auf Crash-Recovery und Postcondition-Readback.

„Frequenz“ bezeichnet hier ausschließlich logische Ereignisdichte. Dieses Artefakt ist kein physischer Hz-, Funk-, EMI-, Spannungs-, Sensor-, Treiber-, RTOS- oder Hardwaretest.

## Reproduzierbarer Capsule-Stand

- Software-Stresstest: `18/18` Vektoren, `81` Assertions, `0` Fehler.
- Hold-Release-Referenzadapter: `31/31` Fälle, `195` Assertions, `0` Fehler.
- Der Referenzadapter attestiert nur `reference_postcondition_satisfied`; er gibt niemals eine Produktaktion frei (`action_allowed=false`, `fail_closed=true`).
- Referenzlauf: macOS ARM64, Node.js `v24.13.1`.

Der vollständige LIMEX-Successor-Precheck (`82/82` Befehle; `2.216/2.216` native Checks) ist private Upstream-Evidenz und aus dieser schmalen Public-Capsule nicht reproduzierbar. Seine Hashbindung wird im Receipt deklariert, nicht als öffentlich nachprüfbarer Lauf ausgegeben.

Authority-Ablaufentscheidungen verwenden die intern beobachtete lokale Systemuhr; ein übergebener Zeitwert ist nur ein Kohärenzsignal. Damit wird kein TSA-, Secure-Monotonic- oder Hardware-Clock-Attest behauptet.

Bei fehlendem oder korruptem Security-State bleibt die Referenzstrecke dauerhaft gesperrt: Der aktuelle Trust Anchor wird im wiederhergestellten Hold-Zustand widerrufen. Sichere Ganzzahlzähler werden vor jeder Fortschreibung auf Erschöpfung geprüft; eine Übergrenze erzeugt keine Teilmutation.

Der Recovery-Preflight erfolgt vollständig vor jeder Quarantäne-, Rename- oder Write-Operation. Damit erzeugt auch die Kombination aus Carrier-Korruption und Zählererschöpfung keine Teilmutation.

## Ausführen

Die Capsule hat keine externen Paketabhängigkeiten. Für einen vergleichbaren Lauf wird Node.js `v24.13.1` verwendet:

```bash
npm test
```

Einzelaufrufe:

```bash
node tests/run_fuzzi_sfh_software_stress_v1.mjs
node tests/run_global_hold_release_adapter_v1_adversarial.mjs
```

`probe` ist ein autorisierungsgerichteter Fail-Closed-Aufruf und endet ohne extern gebundenes Produkt-Enforcement erwartungsgemäß nonzero. Für den rein diagnostischen Referenz-Readback existiert `inspect-reference`.

Die Prüfsummen werden separat geprüft:

```bash
shasum -a 256 -c SHA256SUMS
```

## Inhalt

- `scripts/`: Funktionskern, kanonischer Parser und Referenzadapter.
- `tests/`: ausführbare Stress- und Fehler-Injektionsharnische.
- `receipts/`: Ergebnisdateien der gebundenen Referenzläufe.
- `schemas/`: lokales JSON-Schema des Capsule-Receipts.
- `GOLDSTANDARD_SFH_FUZZI_v1_0.md`: menschenlesbarer Goldstandard.
- `MARCUS_AND_TOBIAS.md`: Freigabe zur freien Nutzung und technische Motivation der FUZZI-Weiterentwicklung.
- `RECEIPT_SFH_FUZZI_v1_0.json`: maschinenlesbare Provenienz und Claim-Grenzen.
- `ARTIFACT_MANIFEST.json`: Hashbindung aller Payload-Dateien einschließlich Receipt, unter Selbstausschluss.
- `REPO_INTEGRATION_CONTRACT.json`: Zielpfad und aktueller Release-/Integrationsstatus.
- `NOTICE.md`: Lizenz- und Nutzungsstatus.

## Release-Grenze

Das Veröffentlichungsziel dieser Komponente ist `components/sfh-fuzzi/` unter dem eigenständigen Tag `sfh-fuzzi-v1.0.0`. Erst der extern lesbare GitHub-Tag samt Release belegt die erfolgte Veröffentlichung; diese Datei nimmt den externen Schritt nicht vorweg. Die öffentliche Freigabe in `NOTICE.md` erlaubt Nutzung, Kopie, Änderung und Weitergabe der durch diesen Tag identifizierten Version ohne Lizenzgebühr oder gesonderten Vertrag. Die oben erklärten Test- und Autoritätsgrenzen bleiben unverändert.
