"""Render docs/research/dossier_growth.svg from the measurement results.

Static SVG (it is embedded in Markdown), log-log: dossier bytes against the
number of transitions in the whole history so far. Reads
research/results/dossier_growth.json and research/results/economy_2400.json,
written by ``python3 -m research.measure_dossiers``.

    python3 -m research.plot_growth
"""

import json
import math
import os

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(HERE)
OUT = os.path.join(ROOT, "docs", "research", "dossier_growth.svg")

W, H = 760, 460
L, R, T, B = 78, 175, 66, 58           # plot margins
X0, X1 = 1, 4_000                      # transitions
Y0, Y1 = 500, 20_000_000               # bytes

SURFACE, INK, INK2, MUTED, GRID = "#fcfcfb", "#0b0b0b", "#52514e", "#8a8984", "#e6e5e1"
SERIES = {"chain": "#2a78d6", "fanin": "#eb6834", "economy": "#1baf7a"}


def sx(x):
    return L + (math.log10(x) - math.log10(X0)) / (math.log10(X1) - math.log10(X0)) * (W - L - R)


def sy(y):
    return T + (1 - (math.log10(y) - math.log10(Y0)) / (math.log10(Y1) - math.log10(Y0))) * (H - T - B)


def human(b):
    for unit, k in (("MB", 1e6), ("KB", 1e3)):
        if b >= k:
            v = b / k
            return f"{v:.0f} {unit}" if v >= 10 else f"{v:.1f} {unit}".replace(".0 ", " ")
    return f"{b:.0f} B"


def marker(kind, x, y, color):
    if kind == "chain":
        return f'<circle cx="{x:.1f}" cy="{y:.1f}" r="4.5" fill="{color}" stroke="{SURFACE}" stroke-width="2"/>'
    if kind == "fanin":
        return f'<rect x="{x - 4.5:.1f}" y="{y - 4.5:.1f}" width="9" height="9" rx="1.5" fill="{color}" stroke="{SURFACE}" stroke-width="2"/>'
    return (f'<path d="M{x:.1f},{y - 5.5:.1f} L{x + 5.5:.1f},{y + 4.5:.1f} L{x - 5.5:.1f},{y + 4.5:.1f} Z" '
            f'fill="{color}" stroke="{SURFACE}" stroke-width="2"/>')


def main():
    with open(os.path.join(HERE, "results", "dossier_growth.json")) as f:
        g = json.load(f)
    with open(os.path.join(HERE, "results", "economy_2400.json")) as f:
        e = json.load(f)
    series = {
        "chain": [(r["transitions"], r["json_bytes"]) for r in g["chain"]],
        "fanin": [(r["transitions"], r["json_bytes"]) for r in g["fanin"]],
        "economy": [(r["history_total"], r["json_bytes"]) for r in e["economy"]["rows"]],
    }
    labels = {"chain": ["one parcel,", "hop after hop"], "fanin": ["4-ary consolidation", "of 8-hop coins"],
              "economy": ["24-wallet economy,", "2 assets, swaps"]}
    per_tx = g["chain"][-1]["json_bytes"] / g["chain"][-1]["transitions"]
    s = [f'<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 {W} {H}" width="{W}" height="{H}" '
         f'font-family="system-ui, -apple-system, Segoe UI, sans-serif" role="img" '
         f'aria-label="Dossier size against history length, log-log">',
         f'<rect width="{W}" height="{H}" fill="{SURFACE}"/>',
         f'<text x="{L}" y="24" font-size="15" font-weight="600" fill="{INK}">Dossier size vs. history length (n = 4, canonical JSON)</text>',
         f'<text x="{L}" y="41" font-size="12" fill="{INK2}">y: bytes the payee receives · x: transitions so far (chain, fan-in: the coin’s own</text>',
         f'<text x="{L}" y="56" font-size="12" fill="{INK2}">history; economy: every transition in the economy) · both axes log</text>']
    for x in (1, 10, 100, 1000):
        s.append(f'<line x1="{sx(x):.1f}" x2="{sx(x):.1f}" y1="{T}" y2="{H - B}" stroke="{GRID}" stroke-width="1"/>')
        s.append(f'<text x="{sx(x):.1f}" y="{H - B + 18}" font-size="11" fill="{MUTED}" text-anchor="middle">{x:,}</text>')
    for y in (1e3, 1e4, 1e5, 1e6, 1e7):
        s.append(f'<line x1="{L}" x2="{W - R}" y1="{sy(y):.1f}" y2="{sy(y):.1f}" stroke="{GRID}" stroke-width="1"/>')
        s.append(f'<text x="{L - 8}" y="{sy(y) + 4:.1f}" font-size="11" fill="{MUTED}" text-anchor="end">{human(y)}</text>')
    s.append(f'<text x="{(L + W - R) / 2:.0f}" y="{H - 16}" font-size="12" fill="{INK2}" text-anchor="middle">transitions in the history</text>')
    # Upper bound: the dossier is the entire history.
    s.append(f'<line x1="{sx(1):.1f}" y1="{sy(per_tx):.1f}" x2="{sx(X1):.1f}" y2="{sy(per_tx * X1):.1f}" '
             f'stroke="{MUTED}" stroke-width="1.5" stroke-dasharray="5 4"/>')
    s.append(f'<line x1="{sx(1.15):.1f}" x2="{sx(1.9):.1f}" y1="{sy(4e6):.1f}" y2="{sy(4e6):.1f}" '
             f'stroke="{MUTED}" stroke-width="1.5" stroke-dasharray="5 4"/>')
    s.append(f'<text x="{sx(2.1):.1f}" y="{sy(4e6) + 4:.1f}" font-size="11" fill="{INK2}">'
             f'dossier = whole history (≈ {per_tx / 1e3:.1f} KB per transition)</text>')
    # Constant-size alternatives.
    for b, text in ((156_068, "Plonky2 toy PCD proof (ZK): 156 KB, any history"),
                    (1_000, "PCD statement + 32-byte ideal proof: ≈1 KB")):
        s.append(f'<line x1="{L}" x2="{W - R}" y1="{sy(b):.1f}" y2="{sy(b):.1f}" stroke="{INK2}" stroke-width="1.5"/>')
        s.append(f'<text x="{sx(1.15):.1f}" y="{sy(b) - 6:.1f}" font-size="11" fill="{INK2}">{text}</text>')
    for name, pts in series.items():
        c = SERIES[name]
        path = " ".join(f"{'M' if i == 0 else 'L'}{sx(x):.1f},{sy(y):.1f}" for i, (x, y) in enumerate(pts))
        s.append(f'<path d="{path}" fill="none" stroke="{c}" stroke-width="2" stroke-linejoin="round"/>')
        s.extend(marker(name, sx(x), sy(y), c) for x, y in pts)
    # Legend (right gutter), shapes + labels in text ink.
    ly = T + 8
    for name in ("chain", "fanin", "economy"):
        s.append(marker(name, W - R + 16, ly, SERIES[name]))
        line1, line2 = labels[name]
        s.append(f'<text x="{W - R + 28}" y="{ly + 4}" font-size="11" fill="{INK}">{line1}</text>')
        if line2:
            s.append(f'<text x="{W - R + 28}" y="{ly + 18}" font-size="11" fill="{INK}">{line2}</text>')
        ly += 44
    s.append("</svg>")
    os.makedirs(os.path.dirname(OUT), exist_ok=True)
    with open(OUT, "w") as f:
        f.write("\n".join(s) + "\n")
    print(OUT)


if __name__ == "__main__":
    main()
