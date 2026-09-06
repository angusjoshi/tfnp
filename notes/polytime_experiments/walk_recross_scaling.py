"""d-scaling of offset-walk level recrossings - cycle 41's decisive datum.

Cycle 39 measured recross/level ~ 0.5-1.5 at d=6 and read it as "O(1)".
But the abstract annealed walk model (conditionally fair step signs +
geometric step envelope with ratio q = 1 - Theta(1/d), the real shrinkage
rate) admits ~1/(1-q) ~ d nearly-flat steps, and a flat fair walk recrosses
its own past levels Theta(sqrt(#flat steps)) times in expectation
(Littlewood-Offord / local CLT floor). At d=6 the two hypotheses
   recross/level = O(1)        (per-level transience, FW structure)
   recross/level = c*sqrt(d)   (the abstract-model floor)
are numerically indistinguishable. This instrument separates them: pure
apex-walk analysis (no sampling beyond the harness's own) at d = 4,6,8,10.

Also measured, per (oracle, d):
  stepband  - mean rounds/level within ONE NEXT STEP of the level
              (|v_t - v_r| < |delta_t|): the quantity the Lean crossing-toll
              identity converts to crossings at rate exactly 1/2;
  escband   - mean rounds/level inside the escape band
              (|v_t - v_r| <= sum_{s>=t}|delta_s|, walk_no_recross's fence);
  qhat      - fitted per-round geometric step-decay ratio, and the implied
              flat-window 1/(1-qhat) (the abstract model's floor is
              ~sqrt(flat-window)).

Usage: [venv]/python walk_recross_scaling.py
"""
import numpy as np
import adversary_game as G
from cells_adversarial import ssg_cuts


def walk_stats(cuts, d):
    T = len(cuts)
    if T < 6:
        return None
    offs = []
    for i in range(d):
        for j in range(i + 1, d):
            for sg in (1.0, -1.0):
                offs.append(np.array([c[i] + sg * c[j] for c, _ in cuts]))
    tot_cross = tot_stepband = tot_escband = 0
    per_level_max = n_levels = 0
    logsteps_t, logsteps_v = [], []
    for v in offs:
        dl = np.abs(np.diff(v))                      # |delta_t|, t=0..T-2
        bud = np.concatenate([np.cumsum(dl[::-1])[::-1], [0.0]])  # B_t
        for t, s in enumerate(dl):
            if s > 1e-14:
                logsteps_t.append(t)
                logsteps_v.append(np.log(s))
        for r in range(T - 1):
            level = v[r]
            crossings = stepband = escband = 0
            for t in range(r + 1, T - 1):
                lo, hi = min(v[t], v[t + 1]), max(v[t], v[t + 1])
                if lo < level < hi:
                    crossings += 1
                if abs(v[t] - level) < dl[t]:
                    stepband += 1
                if abs(v[t] - level) <= bud[t]:
                    escband += 1
            tot_cross += crossings
            tot_stepband += stepband
            tot_escband += escband
            per_level_max = max(per_level_max, crossings)
            n_levels += 1
    qhat = np.nan
    if len(logsteps_t) > 10:
        A = np.vstack([np.ones(len(logsteps_t)), np.array(logsteps_t)]).T
        coef, *_ = np.linalg.lstsq(A, np.array(logsteps_v), rcond=None)
        qhat = float(np.exp(coef[1]))
    return dict(T=T, n=n_levels,
                cross=tot_cross / max(n_levels, 1), cmax=per_level_max,
                stepband=tot_stepband / max(n_levels, 1),
                escband=tot_escband / max(n_levels, 1), qhat=qhat)


def randbal_replicates(T=20, seeds=(2, 3)):
    """The annealed-decisive replicate pass (randbal only, extra seeds)."""
    for d in (4, 6, 8, 10):
        for seed in seeds:
            st = walk_stats(G.play(d, seed, T, mode="randbal",
                                   verbose=False)[1], d)
            if st is None:
                print(f"d={d} seed={seed}: trajectory too short", flush=True)
                continue
            print(f"d={d} randbal seed={seed}: T={st['T']} levels={st['n']} "
                  f"recross/level={st['cross']:.2f} max={st['cmax']} "
                  f"stepband={st['stepband']:.2f}", flush=True)


if __name__ == "__main__":
    import sys
    if len(sys.argv) > 1 and sys.argv[1] == "seeds":
        randbal_replicates()
        raise SystemExit
    T = 20
    for d in (4, 6, 8, 10):
        runs = [("ssg", lambda d=d: ssg_cuts(d, 1, T, np.random.default_rng(7))),
                ("randbal", lambda d=d: G.play(d, 1, T, mode="randbal",
                                               verbose=False)[1])]
        if d <= 8:
            runs.append(("cellmax", lambda d=d: G.play(d, 1, T, mode="cellmax",
                                                       verbose=False)[1]))
        for label, mk in runs:
            st = walk_stats(mk(), d)
            if st is None:
                print(f"d={d} {label:>8}: trajectory too short", flush=True)
                continue
            fw = 1.0 / max(1e-9, 1.0 - st["qhat"]) if np.isfinite(st["qhat"]) \
                else float("nan")
            print(f"d={d} {label:>8}: T={st['T']} levels={st['n']} "
                  f"recross/level={st['cross']:.2f} max={st['cmax']} "
                  f"stepband={st['stepband']:.2f} escband={st['escband']:.2f} "
                  f"qhat={st['qhat']:.3f} flatwin={fw:.1f}", flush=True)
