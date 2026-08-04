"""Per-round mass-weighted cell-partition entropy H_t on all four trajectory
types. The proof-target hypothesis (cell_sampler.md §4): balanced cuts keep
H_t ~ log(d t) (concentration) rather than ~ t log d (equidistribution).
H_t is estimated from exact-rejection samples of each prefix (biased low for
tails; fine for the growth trend). Also prints the increment dH per round.

Usage: python cell_entropy.py
"""
import numpy as np
import adversary_game as G
from cells_adversarial import cell_sig, ssg_cuts


def entropy(S, cuts):
    sig = cell_sig(S, cuts)
    _, inv = np.unique(sig, axis=0, return_inverse=True)
    counts = np.bincount(inv)
    p = counts / counts.sum()
    return float(-(p * np.log(p + 1e-12)).sum()), len(counts)


def main():
    d, T = 6, 14
    rng = np.random.default_rng(4242)
    tracks = {}
    _, tracks["adversary"] = G.play(d, 1, T, mode="adversary", verbose=False)
    _, tracks["cellmax"] = G.play(d, 1, T, mode="cellmax", verbose=False)
    _, tracks["toward"] = G.play(d, 106, T, mode="toward", verbose=False)
    tracks["random-SSG"] = ssg_cuts(d, 1, T, rng)
    print(f"d={d}: H_t (nats) and #cells per prefix; benchmarks: "
          f"log(d*t) at t=14 = {np.log(d*14):.2f}, t*log(d) = {14*np.log(d):.2f}")
    print(f"{'t':>3}" + "".join(f" | {k:>16}" for k in tracks))
    prev = {k: 0.0 for k in tracks}
    for t in range(2, T + 1):
        row = f"{t:>3}"
        for k, cuts in tracks.items():
            S, _ = G.rejection_sample(cuts[:t], d, rng, want=2400)
            if len(S) < 400:
                row += f" | {'exhausted':>16}"
                continue
            H, nc = entropy(S, cuts[:t])
            row += f" | H={H:5.2f} dH={H-prev[k]:+4.2f}"
            prev[k] = H
        print(row, flush=True)


if __name__ == "__main__":
    main()
