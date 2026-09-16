# LIMEX Science · öffentlicher Cleanroom RC4

Dieser Kandidat trennt zwei verschiedene Ebenen:

1. **Öffentliche Forschungsartefakte.** Nach einer autorisierten Veröffentlichung kann technisch nicht mehr erzwungen werden, dass heruntergeladene Dateien nur von akkreditierten Wissenschaftlern genutzt werden. Die rechtmäßige Nutzung richtet sich nach Lizenz und Gesetz.
2. **Knappes Sponsored Compute.** Dieser Dienst bleibt individuell sowie an Projekt, Zweck, Schlüssel, Laufzeit, Scope und Budget gebunden. Jede Nutzung wird erneut geprüft.

Der enthaltene Python-Kern ist eine deterministische Strukturprüfung. Er kann absichtlich keine reale Person identifizieren, keinem Identity Provider vertrauen, kein Token ausstellen, keine Rechenaufgabe starten und kein Konto aktivieren. Sein stärkstes Ergebnis lautet `HOLD_EXTERNAL_VERIFICATION_REQUIRED`; jedes Ergebnis enthält `external_effect = DENY` und `access_grant = null`.

Eine echte Akkreditierung benötigt einen getrennt betriebenen Dienst, der signierte Belege gegen festgelegte Vertrauensanker, aktuelle Widerrufsdaten und einen Besitznachweis des gebundenen Schlüssels prüft. Danach sind zwei voneinander unabhängige fachliche Reviews erforderlich. Weder ORCID noch Hochschul-Login reichen allein aus.

Aktueller Freigabestatus: `RC4__PENDING_POST_FREEZE_AUDIT_AND_DIGEST_BOUND_CONFIRMATION__NO_SPONSORED_COMPUTE`.

Der Forschungsinhalt wird in dieser Zugangskapsel nicht dupliziert. `RESEARCH_PAYLOAD_BINDING.json` bindet ihn bytegenau an den unveränderlichen Repository-Tag `goldbach-v1.8.767`; `proof_status = NO_PROOF` bleibt unverändert.

Für einen neu assemblierten Nachfolger laufen Validator und Manifest-Builder vor dem Freeze. Nach dem Freeze sind nur noch Unit-Tests, `verify_frozen_package.py` und die Prüfung von `SHA256SUMS.txt` vorgesehen. Validator und Builder lehnen ein bereits eingefrorenes Paket absichtlich ab.
