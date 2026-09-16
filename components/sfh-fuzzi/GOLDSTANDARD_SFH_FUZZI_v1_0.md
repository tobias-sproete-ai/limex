# GOLDSTANDARD — SFH FUZZI v1.0

## Urteil

```ini
CAPSULE_STATUS                    = PUBLIC_RELEASE_CANDIDATE__DOUBLE_BLIND_REAUDIT_PASS_WITH_DECLARED_LIMITS
SUCCESSOR_ASSEMBLY_PRECHECK       = PASS (82/82 commands; private upstream evidence)
NATIVE_VALIDATOR                  = PASS (2216/2216; private upstream evidence)
SOFTWARE_STRESS_HARNESS           = PASS (18/18; 81 assertions)
HOLD_RELEASE_REFERENCE_HARNESS    = PASS (31/31; 195 assertions)
REFERENCE_POSTCONDITION           = TESTED
PRODUCT_ACTION_AUTHORIZATION      = ALWAYS_DENIED_BY_REFERENCE_ADAPTER
PRODUCT_ENFORCEMENT_GATE          = NOT_IMPLEMENTED
PHYSICAL_HARDWARE_FREQUENCY_TEST  = NOT_EXECUTED
INSTALLATION                      = NOT_EXECUTED
PUBLIC_RELEASE                    = CEO_AUTHORIZED__EXACT_TAG_AND_ASSET_READBACK_PENDING
```

Die Capsule ist ein reproduzierbarer Software-Stresstest und ein Referenztest für einen getrennten Global-Hold-Release-Adapter. Sie ist kein physischer Frequenzbandtest. „FUZZI“ bezeichnet hier die dynamische Belastung des logischen Ereignis- und Zustandsraums.

## 1. Gebundene LIMEX-Identitäten

| Objekt | Identität |
|---|---|
| Installierte, unveränderte R5.5.17-Basis | Full-tree SHA-256 `a0ef24468437e15c08e0caa82ed3e552dad23dfa401b0d5927c410aa03a11325` |
| Reparierter R5.5.18-Successor-Kandidat | Full-tree SHA-256 `8954a7a9697e538ee82918e8c73e4c393850e0ce426840a306b6b95c662be8a7` |
| Self-excluded Runtime-Identität des Kandidaten | `LIMEX_TREE_SHA256_3898ff3fd3f78bf014f06058394f93ec7eaf27e0ee8ceb8868416e02ca751f26` |
| Successor-Precheck Run 07 | SHA-256 `fc7ca1f74d441f6a3f5717ba35408c28a5df1fe6c67d53d7183d4ec9710d6582` |
| Referenz-Node-Binary | SHA-256 `29ecb10b64e8de28f5073f0b91f2fdc9ee60a0e21995edfcacb02eb0aae01a79`, Version `v24.13.1` |

Der vollständige Nachfolger-Precheck führte 82 von 82 Befehlen erfolgreich aus; der kanonische Validator meldete 2.216 Checks und 0 Fehler. Diese vollständige Evidenz verbleibt privat, weil die Public-Capsule bewusst nur den kleinsten reproduzierbaren FUZZI-Ausschnitt enthält.

## 2. Software-Stresstest

| Metrik | Ergebnis |
|---|---:|
| Vektoren | 18 |
| PASS / FAIL | 18 / 0 |
| Assertions | 81 |
| Maximale akzeptierte Batchdichte | 256 logische Events |
| Erste verworfene Übergrenze | 257 Events |
| Logische Frame-Drops | 0 |
| Obergrenze Closure-Artefakt | 65.536 Bytes akzeptiert; 65.537 Bytes verworfen |

Gemessene Latenzen sind Beobachtungen eines einzelnen Userspace-Laufs, keine harte Echtzeitgarantie. Die JavaScript-Tests attestieren ihre äußere Sandbox- oder Netzgrenze nicht selbst.

## 3. Hold-Release-Referenzadapter

Der reparierte Adapter bestand 31 adversariale Fälle mit 195 Assertions. Neun neue Negativregressionen schließen die in den unabhängigen Prüflinien entdeckten Schein-PASS-Pfade:

1. Ein kohärenter Neuaufbau aller Dateien im Adapter-Root kann eine Referenz-Postcondition darstellen, aber niemals `action_allowed=true` erzeugen.
2. Ein Commit-Replay prüft den aktuellen Target-/ACK-Zustand erneut und bricht bei Re-Hold mit `RELEASE_POSTCONDITION_READBACK_MISMATCH` ab.
3. Der autorisierungsgerichtete CLI-Aufruf `probe` endet bei fehlender Produktautorität nonzero; `inspect-reference` bleibt rein diagnostisch.
4. Ein bereits konsumierter Release-Request kann nach `GLOBAL_REOPEN` wegen der veralteten Epoch weder über die API noch über die CLI als idempotenter PASS wiederverwendet werden.
5. Nicht-endliche oder nicht-ganzzahlige Zeitträger werden an API und CLI fail-closed verworfen; `NaN` kann die signierte Authority-Expiry nicht mehr umgehen.
6. Ein formal gültiger, aber rückdatierter Zeitparameter kann eine abgelaufene Authority weder über API noch CLI wieder gültig machen: Ablaufentscheidungen verwenden die intern beobachtete lokale Uhr; der übergebene Zeitwert dient nur der Kohärenzprüfung.
7. Ist der persistierte Security-State korrupt oder fehlt er, wird der aktuelle Trust Anchor im wiederhergestellten Hold-Zustand zwingend widerrufen; verlorene Revocation- oder One-use-Historie kann damit keinen Release wiederbeleben.
8. Epoch-, Transition- und Mutation-Zähler werden vor jeder Mutation auf sichere Fortschreibbarkeit geprüft. Bei Erschöpfung folgt `ADAPTER_COUNTER_EXHAUSTED` ohne Teilmutation und ohne PASS.
9. Auch die Kombination aus korruptem State/Target und erschöpftem Zähler wird vor jeder Quarantäne-, Rename- oder Write-Operation vollständig vorgeprüft; ein Abbruch verändert weder Dateien noch Dateimenge.

Die SHA-256-Hüllen schützen gegen partielle und zufällige Korruption. Sie sind kein Authentizitätsanker gegen einen Writer des gesamten Adapter-Roots. Ein Produkt-Enforcement-Gate benötigt einen externen, vom Root-Writer nicht erzeugbaren Trust Anchor und ein signiertes Enforcement-Receipt. Dieses Gate ist ausdrücklich nicht Bestandteil dieser Capsule. Die lokale Systemuhr ist weder TSA noch sichere monotone oder hardwareattestierte Zeitquelle; genau diese Nicht-Implikation bleibt offen ausgewiesen.

## 4. Audit-Genealogie

Der erste lokale Kandidat erreichte grüne Selbsttests, wurde aber in zwei unabhängigen Read-only-Prüflinien auf `FAIL_CLOSED` gesetzt. Gefunden wurden die Referenz-/Produktautoritätsvermischung sowie unvollständige Repo-, Lizenz-, Schema- und Provenienzbindung. Nachfolgende Re-Audits fanden zusätzlich die veraltete `SHA256SUMS`-Datei, einen falschen idempotenten Request-Replay-PASS nach erneutem Global Hold, ungültige und rückdatierte Zeitträger, den Verlust von Revocation-/One-use-Daten bei korrupter State-Recovery, unsichere Zählerfortschreibungen an `Number.MAX_SAFE_INTEGER` sowie eine Recovery-Teilmutation vor abgeschlossenem Zähler-Preflight. Diese Befunde wurden im vorliegenden Kandidaten eng begrenzt repariert. Der historische Run 01 und die negativen Auditberichte bleiben privat und unverändert erhalten.

Die vorliegende Reparatur ist ein Same-Gate-Fix. Sie erweitert den Scope nicht um Hardware, Netzwerkdienste, Produktintegration oder autonome Freigabe. Zwei voneinander unabhängige Read-only-Prüflinien haben den identischen, vor der Statusmaterialisierung eingefrorenen Capsule-Baum `b1313868f90f5b0ef1c4f2c5bf21a922c90c38cbbc50b7ca231eb66c3519f52e` (19 Dateien; 198.099 Bytes) mit `PASS_WITH_DECLARED_LIMITS` bewertet:

- Security-Prüflinie A: Bericht SHA-256 `a7d312f3b896535f5b79fce6bd4e21253fd6c8f320331ef7a145fb37af8a0659`
- Repo-/Release-Prüflinie B: Bericht SHA-256 `e2ef422882d0e4876ae2e9ce7d4d59669808917c4e990d04a329a196794ea50f`

Beide Prüflinien bestätigten die Capsule-Eingangs- und Abschlussidentität, `SHA256SUMS`, den vollständigen `npm test`-Lauf sowie die Beseitigung der früheren Revocation-, Replay-, Safe-Integer- und Recovery-Teilmutationsbefunde. Die Berichte liegen außerhalb der öffentlichen Repo-Capsule im privaten Upstream-Evidenzpfad. `PASS_WITH_DECLARED_LIMITS` gilt ausschließlich innerhalb der in Abschnitt 5 festgeschriebenen Grenzen.

## 5. Nicht-Implikationen

Die Resultate beweisen nicht:

- eine installierte oder aktivierte R5.5.18-Version;
- ein Produkt-Enforcement-Gate oder eine reale Produktfreigabe;
- physische RF-, EMI-, Sensor-, Spannungs-, Bus-, Kernel-, RTOS- oder Hardwareeigenschaften;
- harte Echtzeitfähigkeit oder zertifizierte Recovery-Zeiten;
- eine vertrauenswürdige externe, monotone oder hardwareattestierte Zeitquelle;
- universelle Fehlerfreiheit, öffentliche Freigabe oder rechtliche Konformität.

## 6. Repo- und Nutzungsgrenze

Der Zielpfad ist `components/sfh-fuzzi/` im LIMEX-Repository auf `main`; die Veröffentlichung wird an den eigenständigen Tag `sfh-fuzzi-v1.0.0` gebunden. Der unmittelbar vor der Integration ausgeführte Remote-Abgleich ergab `ahead 0, behind 0`. Die CEO-Veröffentlichungsfreigabe liegt vor.

`NOTICE.md` räumt für die veröffentlichten Dateien die freie Nutzung, Kopie, Änderung und Weitergabe ohne Lizenzgebühr oder separaten Vertrag ein. `package.json` verweist auf diese Freigabe, bleibt aber mit `private: true` gegen eine unbeabsichtigte npm-Veröffentlichung gesperrt. Die Freigabe erweitert weder die technischen Testaussagen noch Produkt-, Patent-, Marken- oder Zertifizierungsautorität.

Die Hashkette ist zirkelfrei: Das Receipt bindet die Payload und schließt sich selbst, `ARTIFACT_MANIFEST.json` und `SHA256SUMS` aus; das Manifest bindet Payload plus Receipt und schließt nur sich selbst und `SHA256SUMS` aus; `SHA256SUMS` bindet abschließend jede andere reguläre Capsule-Datei.

## 7. Komplexitäts-Stopp

`DROHENDES UNNÖTIGES KOMPLEXITÄTSWACHSTUM` ist gesperrt. Kein generisches HAL, keine synthetischen Hardwaregrenzen und kein vorgetäuschtes Produkt-Enforcement werden ergänzt. Das nächste reale Gate ist ausschließlich die Veröffentlichung des exakten Tags mit anschließendem Readback von Commit, Tag und Release-Assets.
