# LIMEX Settle — öffentlicher Reinraum-Release-Candidate

`RELEASE = LIMEX_SETTLE_CLEANROOM_V1_1_RC1`

`PUBLICATION_STATUS = BLOCKED__NO_PUBLIC_RELEASE_DISPATCH`

Dieses Paket enthält eine eigenständige Referenzimplementierung eines deterministischen, fail-closed arbeitenden Settlement- und Release-Seal-Kerns. Technische Leistungsnachweise bleiben von Rechnung und Zahlung getrennt, mehrdeutige oder wiederholte Zustandsübergänge werden abgewiesen, Release-Eingaben werden inhaltsgebunden und Ausgaben von Sprachmodellen erhalten keine Ausführungsautorität.

Das Paket enthält bewusst keine organisationsbezogene Identität, Personenidentität, Host-Pfade, Repository-Koordinaten, Zugangsdaten, privaten Betriebsbelege oder Inventare ausgeschlossener Quellen. Die Reinraum-Provenienz bindet ausschließlich öffentliche Paketpfade, Vorgänger-Prüfsummen und die Transformationsklasse.

## Lokale Verifikation

```sh
python3 -B scripts/validate_cleanroom_release.py
python3 -B scripts/build_manifest.py
python3 -B scripts/verify_frozen_package.py --expected-root-sha256 <VERTRAUENSWUERDIG_BEZOGENER_PACKAGE_ROOT_SHA256>
```

Der erste Befehl führt die begrenzten Reinraum-, Quelltext-, Sicherheitsnachweis- und 107-Test-Gates in einer lokalen Netzwerksperre aus. Der zweite erzeugt das selbstausschließende Manifest und die Prüfsummenliste. Der dritte verifiziert die eingefrorene Identität und das gesperrte Veröffentlichungs-Gate ohne Mutation.

Die lokale Speichergrenze ist bewusst strikt: State- und Ledger-Verzeichnisse müssen ausschließlich dem Eigentümer zugänglich sein, vorhandene Zustandsdateien werden erneut geprüft, erweiterte macOS-ALLOW-ACLs werden abgewiesen und auf nicht unterstützten ACL-Plattformen schließt das System fail-closed. State-Operationen bleiben an einen einzigen geöffneten Verzeichnis-Deskriptor gebunden und brechen bei einer Verschiebung des konfigurierten Namensraums ab. Die getrackten Git-Bytes erhalten zusätzlich eine aggregierte SHA-256-Identität sowie anwendungsseitige Datei-, Byte-, Ausgabe- und Zeitbudgets; HEAD muss unmittelbar auf ein Commit-Objekt auflösen, und HEAD, Index und rohe Worktree-Bytes werden ohne repository-gesteuerte Inhaltsfilter oder Replace-Objekte verglichen. Jeder Git-Unterprozess deaktiviert Lazy Object Fetching, interaktive Prompts, Credential Helper und Transporte. Für diese Fassung wird weder eine plattformübergreifende Speicher-Attestierung noch eine harte Ressourcenbegrenzung des Betriebssystemprozesses behauptet.

## Freigabegrenze

Dies ist ein technisch validierter Kandidat, kein produktiver Zahlungsweg, keine Wallet, keine Blockchain, keine Bankanbindung, kein Produktivdienst, keine Safety-Zertifizierung, keine patentrechtliche Bewertung und keine Veröffentlichungsfreigabe. Die öffentliche Auslieferung bleibt gesperrt, bis sämtliche Bedingungen in `PUBLIC_RELEASE_GATE.json` unabhängig für exakt diese Bytes erfüllt sind.
