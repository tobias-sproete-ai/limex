# Goldstandard: Tokenverbrauch des Goldbach-Quests

Stand: 16. September 2026  
Messzeitraum: 1. September 2026, 18:47:42.915 UTC, bis 15. September 2026, 01:55:05 UTC  
Endzustand: abgeschlossener Deploy `goldbach-v1.8.767`

## Ergebnis

Eine **exakte globale Einzelzahl** für das gesamte Goldbach-Quest ist aus den vorhandenen Telemetriedaten nicht beweisbar. Neun sichtbare Remote-Windows-Goldbach-Tasks besitzen im lokalen Datenbestand keinen auswertbaren Tokenledger. Ihr Verbrauch ist positiv oder null, aber numerisch nicht beobachtbar und wird nicht geschätzt.

Der belastbare lokale Befund lautet:

| Messgröße | Tokens | Milliarden Tokens | Status |
|---|---:|---:|---|
| Strikt als Goldbach-only klassifiziert | **4.800.018.574** | **4,800018574** | lokal beobachtet; semantische Klassifikation partiell |
| Mixed / nicht innerhalb eines Turns separierbar | **527.030.352** | **0,527030352** | lokal beobachtet; Goldbach-Anteil nicht identifizierbar |
| Goldbach-bezogener lokaler Korridor | **4.800.018.574 bis 5.327.048.926** | **4,800018574 bis 5,327048926** | defensibler lokaler Bereich |
| Vollständiger lokaler Zeitkorridor einschließlich Nebenquests | **7.177.296.749** | **7,177296749** | lokal beobachtet; kein Goldbach-only-Wert |
| Remote-Windows-Anteil | nicht messbar | nicht messbar | `NOT_IDENTIFIABLE` |

Die kurze Antwort ist daher:

> **Das Goldbach-Quest hat lokal nachweisbar zwischen 4,800018574 und 5,327048926 Milliarden Tokens verbraucht. Hinzu kommt ein nicht quantifizierbarer Verbrauch von neun Remote-Windows-Tasks. Eine höhere Genauigkeit als dieses Intervall wäre Scheingenauigkeit.**

## Was die Zahlen bedeuten

- Die Untergrenze enthält nur Turns, die der Doppelblindprüfung zufolge ausschließlich Goldbach-Mathematik, Lean-Formalisierung, Goldbach-Audit oder Goldbach-spezifischen Deploy betreffen.
- Die Obergrenze addiert sämtliche gemischten Turns vollständig. Sie ist konservativ, weil nicht jeder Token dieser Turns Goldbach zuzurechnen ist.
- Der lokale Bruttokorridor umfasst zusätzlich 1.850.247.823 Tokens eindeutig nicht Goldbach-bezogener Nebenquests innerhalb desselben Zeitfensters. Er darf nicht als Goldbach-Verbrauch bezeichnet werden.
- `cached_input_tokens` ist bereits Teil der Eingabetokens. `reasoning_output_tokens` ist bereits Teil der Ausgabetokens. Beide wurden nicht doppelt addiert.
- Aus Tokenzahlen wird weder Energieverbrauch noch Rechenleistung abgeleitet.

## Doppelblindabgleich

### Linie A

- Lokaler Bruttokorridor: 7.177.296.749 Tokens
- Goldbach-only: 4.800.018.574 Tokens
- Mixed: 527.030.352 Tokens
- Goldbach-only plus Mixed: 5.327.048.926 Tokens
- Guardian-Reviews: 192.354.896 Tokens, im Gesamtumfang enthalten
- Start wurde am letzten kumulativen Tokenzähler unmittelbar vor dem ersten Goldbach-Prompt geschnitten; 8.645.268 vorherige Tokens des gemischten Ausgangsturns wurden entfernt.

### Linie B

- Lokaler Bruttokorridor: 6.992.896.767 Tokens
- Goldbach-only: 4.857.024.799 Tokens
- Mixed: 368.899.295 Tokens
- Goldbach-only plus Mixed: 5.225.924.094 Tokens
- Automatische Guardian-Review-Turns wurden nicht in denselben Umfang aufgenommen.
- Der Ausgangsturn wurde vollständig statt am Goldbach-Prompt erfasst.

### COO-Adjudikation

Für die Frage nach dem **gesamten Quest** ist Linie A der vollständigere lokale Zensus, weil Guardian-Reviews reale Modellaufrufe des Goldbach-Prozesses sind und der Start promptgenau abgegrenzt wurde. Die abweichende semantische Zuordnung einzelner Turns zwischen A und B belegt zugleich, dass keine punktgenaue Goldbach-only-Zahl behauptet werden darf. Deshalb wird das konservative Intervall von 4,800018574 bis 5,327048926 Milliarden Tokens berichtet.

## Messgrenzen

1. Die modernen lokalen Turns wurden über genau einen finalen `turn_token_usage`-Snapshot je `(thread_id, turn_id)` gezählt.
2. Kumulative `thread_token_usage`-Werte wurden nicht summiert.
3. Der frühe Legacy-Abschnitt wurde über kumulative Zähler rekonstruiert und bleibt hinsichtlich der turninternen Zuordnung partiell.
4. Neun Remote-Windows-Tasks sind sichtbar, aber ohne lokale Host-Telemetrie nicht numerisch messbar.
5. Das Ergebnis ist ein Tokenzensus, keine Energie-, Kosten- oder Wirkungsmessung.

## Status

```text
LOCAL_GOLDBACH_ONLY_LOWER_BOUND = 4.800018574_BILLION_TOKENS
LOCAL_GOLDBACH_RELATED_UPPER_BOUND = 5.327048926_BILLION_TOKENS
LOCAL_FULL_CHRONOLOGY = 7.177296749_BILLION_TOKENS
REMOTE_WINDOWS_TOKEN_USAGE = NOT_IDENTIFIABLE
GLOBAL_EXACT_GOLDBACH_TOKEN_TOTAL = NOT_IDENTIFIABLE
ENERGY_INFERENCE = NOT_PERFORMED
```

