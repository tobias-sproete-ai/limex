# Goldstandard LIMEX Science cleanroom and individual accreditation V1.0 RC4

Status: `PASS_WITH_DECLARED_LIMITS__LIVE_ACCREDITATION_FAIL_CLOSED`  
Public release: `BLOCKED__PENDING_POST_FREEZE_AUDIT_AND_DIGEST_CONFIRMATION`  
Sponsored compute: `NOT_IMPLEMENTED__NO_ACCESS_GRANTS`

## 1. Ergebnis

Der Science-Cleanroom-Kandidat materialisiert eine reproduzierbare, nicht autorisierende Akkreditierungsarchitektur. Zwei unabhängige Prüflinien kamen zum selben Befund:

- Öffentliche Forschungsartefakte und ein knapper Sponsored-Compute-Dienst sind getrennte Ebenen.
- Ein institutioneller Login belegt keine wissenschaftliche Berechtigung.
- Eine authentisierte ORCID iD ist ein Provenienzsignal, kein Kompetenz-, Wahrheits- oder Absichtsnachweis.
- Jede Person benötigt eine eigene, nicht übertragbare, projekt- und zweckgebundene Zulassung.
- Ein institutioneller und ein gleichwertiger unabhängiger Forschendenpfad bleiben erhalten.
- Zwei verschiedene menschliche Fachprüfer müssen exakt denselben eingefrorenen Scope genehmigen und Interessenkonflikte ausschließen.
- Scope, Budget, Gültigkeit, Policy, Projekt, Zweck und der vom Antragsteller gehaltene Schlüssel sind gemeinsam zu binden.
- Widerruf, Suspendierung, Re-Akkreditierung und Einspruch dürfen nie automatisch Zugriff reaktivieren.
- Die versiegelte Release-Identität kennt keine privilegierte Gründerrolle, keinen Founder-Key, keinen Wiederöffnungspfad und keinen gleichidentischen Mutationsmechanismus.

## 2. Entscheidende Sicherheitsgrenze

Der enthaltene Kern prüft ausschließlich die strukturelle Konsistenz eines geschlossenen Datenpakets. Er prüft keine echten Signaturen oder Vertrauensketten. Deshalb kennt er nur zwei zulässige Ergebnisse:

```text
DENY_FAIL_CLOSED
HOLD_EXTERNAL_VERIFICATION_REQUIRED
```

Beide Ergebnisse enthalten:

```text
external_effect = DENY
access_grant = null
```

Selbst ein formal vollständiges Paket akkreditiert somit niemanden. Erst ein separat betriebener, unabhängig auditierter Dienst darf echte Signaturen, Trust Anchors, aktuelle Widerrufe und Holder-of-Key-Nachweise prüfen. Ein wiederum getrennter Capability-Issuer wäre für kurzlebige, sendergebundene Berechtigungen zuständig. Beides ist nicht Bestandteil dieses Kandidaten.

## 3. Individuelle Akkreditierung

Ein künftiger Grant bindet genau eine natürliche Person. Shared-, Labor- und Gruppen-Accounts sind unzulässig. Automatisierte Jobs dürfen nur als kurzlebige Unter-Capability eines aktiven persönlichen Grants ausgeführt werden.

### Institutioneller Pfad

Erforderlich sind eine extern verifizierte föderierte Identität auf dem festgelegten Assurance-Niveau, eine aktuelle Forschungszugehörigkeit oder -rolle, Holder-of-Key, zwei Fachreviews, aktuelle Widerrufsinformationen und akzeptierte Bedingungen.

### Unabhängiger Pfad

Fehlende Hochschulzugehörigkeit ist kein automatischer Ausschluss. Erforderlich sind ein zugelassener starker Identitätsnachweis, ein reproduzierbares scopebezogenes Forschungsartefakt, Holder-of-Key, dieselben zwei Fachreviews, aktuelle Widerrufsinformationen und zunächst eine enge Pilotquote. Publikationszahl oder Rang ersetzen diese Prüfung nicht.

## 4. Missbrauchsschutz und verbleibende Realität

Eine wasserdichte Behauptung absoluter Missbrauchsfreiheit wäre falsch. Identitätsprüfung beweist keine gute Absicht. Holder-of-Key beweist keinen ausschließlichen menschlichen Besitz. Reviewer können kolludieren. Ein zugelassener Identity Provider kann kompromittiert werden. Widerruf holt bereits gelesene Daten oder erzeugte Outputs nicht zurück.

Die belastbare Zielsetzung lautet deshalb: Kein Dienstzugang ohne vollständige und aktuelle Belegkette; keine ungebundenen Bearer- oder Sponsor-Schlüssel; minimale Scopes und Quoten; erneute Prüfung bei jedem Aufruf; sofortiger Hold bei Unklarheit; nachvollziehbare Gründe und unabhängiger Einspruch.

## 5. Datenschutz und Fairness

Routineprotokolle verwenden pseudonyme Subjektkennungen. Rohbelege bleiben in der separaten Verifier-Domäne. Pseudonymisierung ist keine Anonymisierung. Zweckbindung, Rechtsgrundlage, Aufbewahrung, Zugriff, Korrektur, Löschung und Backup-/Provider-Weitergabe bleiben vor einem Pilotbetrieb eigenständig rechtlich und technisch zu schließen.

Ablehnungen benötigen strukturierte Begründungen und einen menschlichen Einspruchspfad. Ein Einspruch bleibt bis zur neuen, konfliktfreien Prüfung auf `DENY` und setzt nie selbst `ACTIVE`.

## 6. Evidenz dieses Kandidaten

- geschlossene JSON-Schemas für Antrag und nicht autorisierende Entscheidung;
- deterministischer Python-Projektor ohne Netzwerk- oder Compute-Schnittstelle;
- institutioneller und unabhängiger Pfad;
- Bindung von Subjekt, Projekt, Zweck, Schlüssel, Scope, Budget, Laufzeit, Reviews, Widerruf und Bedingungen;
- negative Tests gegen ORCID-Scheinautorität, fehlenden Holder-of-Key, Replay, stale evidence, Reviewer-Kollision, Scope-/Budget-Drift und Widerruf;
- Bedrohungsmodell und 15 offene Runtime-Gates;
- Cleanroom- und Manifestwerkzeuge mit einem Public-Release-Gate, das bis zum Post-Freeze-Audit und zur digestgebundenen Bestätigung gesperrt bleibt.
- 49 lokale Unit- und Release-Control-Regressionstests; die erste Prüflinie ergänzte 35 Bindungs-, 1.140 Typ-/Shape- und 56 Lifecycle-Prüfungen ohne autorisierenden Ausgang.

`PASS` bedeutet nur: Der lokale Kandidat erfüllt seinen erklärten strukturellen Scope. Es bedeutet nicht, dass ein Mensch akkreditiert, ein Dienst implementiert oder eine Veröffentlichung freigegeben ist.

## 7. Offene Pflichtgates

Vor dem ersten Sponsored-Compute-Pilot bleiben insbesondere offen:

1. reale, signaturprüfende Identity-/Federation-Adapter mit zugelassenen Trust Anchors;
2. separater WebAuthn-/DPoP-/mTLS-artiger Holder-of-Key-Verifier;
3. attestierte Reviewer-, Konflikt- und Appeal-SOP;
4. sendergebundener Capability-Issuer und Gateway ohne rohe Sponsor-Schlüssel;
5. atomare Budget-, Revocation-, Tenant-, Tool-, Daten- und Egress-Durchsetzung;
6. Datenschutz-, Rechts-, Lizenz- und Dienstbedingungen;
7. unabhängige Abuse-/Privacy-Tests und ein kleiner quota-gebundener Pilot;
8. digestgebundene Betriebs- und Release-Autorität.

## 8. Forschungs- und Release-Grenze

Der Goldbach-/Lean-Payload wird nicht dupliziert, sondern durch `RESEARCH_PAYLOAD_BINDING.json` an den unveränderlichen Tag `goldbach-v1.8.767`, dessen Toolchain-, Build-, Quellabschluss- und Axiomenbelege gebunden. Unverändert gilt:

```text
proof_status = NO_PROOF
```

RC4 bleibt bis zum externen Post-Freeze-Audit und zur digestgebundenen Bestätigung unveröffentlicht. Es erfolgte weder eine Akkreditierung noch eine Rechenfreigabe.

## 9. Komplexitätsschranke

Ein vollautomatischer SSO-/ORCID-/Proxy-/Token-Marktplatz vor realem Compute-Partner und Pilot wäre `DROHENDES UNNÖTIGES KOMPLEXITÄTSWACHSTUM`. Zulässig ist zuerst nur: reproduzierbarer Capsule, kleiner manuell geprüfter Pilot, Messung realer Engpässe und danach gezielte Automatisierung.

## 10. Werkzeugtransparenz

Die Erarbeitung nutzte LIMEX unter dem lokalen Kompatibilitäts-Paketnamen R5.5, zwei unabhängige read-only Prüflinien und eine COO-Synthese. Das Modellumfeld wurde als Codex GPT-6 Astra deklariert; diese Angabe ist keine kryptografische Provider-Attestierung. Externe Standards dienten nur zur Schnittstellen-Einordnung und attestieren LIMEX nicht.
