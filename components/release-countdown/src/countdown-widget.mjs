import {
  COUNTDOWN_STATE,
  CountdownModel,
  DEFAULT_RESYNC_INTERVAL_MS,
  MonotonicServerClock,
  ReleaseReceiptLatch,
  TARGET_UTC_ISO,
  fetchServerTimeSample
} from "./countdown-core.mjs";

const TEMPLATE = document.createElement("template");
TEMPLATE.innerHTML = `
  <style>
    :host {
      --limex-black: #0a0a0a;
      --limex-white: #ffffff;
      --limex-grey: #555555;
      --limex-red: #ff3b30;
      display: block;
      color: var(--limex-white);
      background: var(--limex-black);
      font-family: "Space Mono", "JetBrains Mono", ui-monospace, SFMono-Regular, Menlo, Consolas, monospace;
      font-variant-numeric: tabular-nums;
      font-feature-settings: "tnum" 1, "zero" 1;
    }

    * { box-sizing: border-box; }

    .panel {
      border: 1px solid var(--limex-grey);
      background: var(--limex-black);
      min-inline-size: 20rem;
    }

    header, footer {
      padding: 1rem 1.25rem;
      text-transform: uppercase;
      letter-spacing: 0.06em;
    }

    header {
      border-block-end: 1px solid var(--limex-grey);
      display: grid;
      gap: 0.35rem;
    }

    .system { font-weight: 700; }
    .target { color: #b8b8b8; font-size: 0.78rem; }

    .grid {
      display: grid;
      grid-template-columns: repeat(4, minmax(4.5rem, 1fr));
      gap: 0;
      padding: clamp(1.5rem, 5vw, 4rem) 1rem;
    }

    .unit {
      display: grid;
      justify-items: center;
      gap: 0.6rem;
      border-inline-end: 1px solid var(--limex-grey);
    }

    .unit:last-child { border-inline-end: 0; }

    .value {
      inline-size: 3ch;
      text-align: center;
      font-size: clamp(2rem, 8vw, 5.5rem);
      line-height: 1;
      font-weight: 700;
      letter-spacing: -0.08em;
    }

    .label {
      color: #9b9b9b;
      font-size: 0.7rem;
      letter-spacing: 0.12em;
    }

    footer {
      border-block-start: 1px solid var(--limex-grey);
      color: #b8b8b8;
      font-size: 0.78rem;
    }

    :host([data-state="${COUNTDOWN_STATE.TARGET_REACHED_LOCKED}"]) .panel,
    :host([data-state="${COUNTDOWN_STATE.RELEASE_VERIFIED}"]) .panel {
      border-color: var(--limex-red);
    }

    :host([data-state="${COUNTDOWN_STATE.RELEASE_VERIFIED}"]) footer {
      color: var(--limex-red);
    }

    @media (max-width: 34rem) {
      .grid { padding-inline: 0.25rem; }
      .value { font-size: clamp(1.8rem, 12vw, 3rem); }
      .label { font-size: 0.58rem; }
    }

    @media (prefers-reduced-motion: reduce) {
      * { scroll-behavior: auto !important; }
    }
  </style>
  <section class="panel" aria-labelledby="limex-countdown-title">
    <header>
      <div id="limex-countdown-title" class="system">LIMEX // DEPLOYMENT GATE</div>
      <time class="target" datetime="${TARGET_UTC_ISO}">TARGET : 2026-09-15 23:59:00 MESZ</time>
    </header>
    <div class="grid" role="timer" aria-live="off" aria-atomic="true">
      <div class="unit"><span class="value" data-value="days">--</span><span class="label">DAYS</span></div>
      <div class="unit"><span class="value" data-value="hours">--</span><span class="label">HOURS</span></div>
      <div class="unit"><span class="value" data-value="minutes">--</span><span class="label">MINS</span></div>
      <div class="unit"><span class="value" data-value="seconds">--</span><span class="label">SECS</span></div>
    </div>
    <footer>STATUS : <span data-status>${COUNTDOWN_STATE.SYNCING}</span></footer>
  </section>
`;

export class LimexReleaseCountdown extends HTMLElement {
  #clock = new MonotonicServerClock();
  #model = new CountdownModel();
  #receiptLatch = new ReleaseReceiptLatch();
  #frame = null;
  #resyncTimer = null;
  #lastRenderedSecond = null;
  #syncFailed = false;

  constructor() {
    super();
    this.attachShadow({ mode: "open" }).append(TEMPLATE.content.cloneNode(true));
  }

  connectedCallback() {
    this.#model = new CountdownModel({
      targetUtcMs: Date.parse(this.getAttribute("target-utc") || TARGET_UTC_ISO)
    });
    this.#syncAndRun();
    document.addEventListener("visibilitychange", this.#handleVisibility);
  }

  disconnectedCallback() {
    if (this.#frame !== null) cancelAnimationFrame(this.#frame);
    if (this.#resyncTimer !== null) clearTimeout(this.#resyncTimer);
    document.removeEventListener("visibilitychange", this.#handleVisibility);
  }

  async applyVerifiedReleaseReceipt(receipt, verifier) {
    await this.#receiptLatch.admit(
      receipt,
      verifier,
      this.getAttribute("target-utc") || TARGET_UTC_ISO
    );
    this.#lastRenderedSecond = null;
    this.#renderFrame();
  }

  #handleVisibility = () => {
    if (!document.hidden) this.#syncAndRun();
  };

  async #syncAndRun() {
    const endpoint = this.getAttribute("time-endpoint") || "/api/time";
    const resyncMs = Number(this.getAttribute("resync-ms") || DEFAULT_RESYNC_INTERVAL_MS);
    try {
      const sample = await fetchServerTimeSample({ url: endpoint });
      this.#clock.bind(sample);
      this.#syncFailed = false;
      this.#renderFrame();
      if (this.#frame === null) this.#frame = requestAnimationFrame(this.#tick);
    } catch (error) {
      this.#syncFailed = true;
      this.#setStatus(
        this.#clock.ready ? COUNTDOWN_STATE.SYNC_STALE : COUNTDOWN_STATE.SYNC_UNAVAILABLE
      );
      this.dispatchEvent(new CustomEvent("limex-time-sync-error", {
        detail: { message: String(error?.message || error) }
      }));
    } finally {
      if (this.#resyncTimer !== null) clearTimeout(this.#resyncTimer);
      this.#resyncTimer = setTimeout(() => this.#syncAndRun(), resyncMs);
    }
  }

  #tick = () => {
    this.#renderFrame();
    this.#frame = requestAnimationFrame(this.#tick);
  };

  #renderFrame() {
    if (!this.#clock.ready) return;
    const snapshot = this.#model.snapshot(this.#clock.nowMs(), this.#receiptLatch.verified);
    const secondKey = Math.floor(snapshot.remainingMs / 1_000);
    if (secondKey === this.#lastRenderedSecond && !snapshot.targetReached) return;
    this.#lastRenderedSecond = secondKey;

    for (const unit of ["days", "hours", "minutes", "seconds"]) {
      this.shadowRoot.querySelector(`[data-value="${unit}"]`).textContent =
        String(snapshot.parts[unit]).padStart(2, "0");
    }
    this.#setStatus(this.#syncFailed ? COUNTDOWN_STATE.SYNC_STALE : snapshot.state);
  }

  #setStatus(state) {
    this.dataset.state = state;
    this.shadowRoot.querySelector("[data-status]").textContent = state;
  }
}

if (!customElements.get("limex-release-countdown")) {
  customElements.define("limex-release-countdown", LimexReleaseCountdown);
}
