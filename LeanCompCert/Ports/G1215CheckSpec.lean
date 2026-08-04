import LeanCompCert.Ports.G1215CheckRun

/-!
# One candidate of the `G1215Check` round — HANDOFF, not yet proved

Layer three of the port would re-block the flat `gRound` fold per candidate
and describe one candidate's block in closed form, exactly as
`Ports/GFoldCheckSpec.lean` does for the sibling `GFoldCheck` port.  The
block structure of `Ports/G1215Check.lean` was chosen so that this file is a
transcription of that one: same `BlockedFold.block` re-association, same three
round regimes (`q < tdiv`, `q = tdiv`, `q > tdiv`), same `orFold` extraction.

What differs, and what the transcription therefore has to carry:

* **two** accumulators, so `bAcc` becomes a pair and `block_eq_candidate`
  reports `gAccU c j` and `gAccL c j`;
* **two** mantissa recursions, `mantX c n i` for the upper check and
  `mantX c (n+1) i` for the lower one, both driven by this port's `advX`
  (`⌊X·n/2^a⌋`, no half-word split);
* the pass flag is the disjunction over `b = 1 … bmax` of `hitOf`, which fires
  at the single `b = eOf c n`, so `candPass` reduces to one exponent rather
  than a genuine search;
* the good flag is multiplied once more, in the **epilogue**, by the two
  final-sum tests `accU ≤ finU` and `finL ≤ accL`; `rows_of_denote` must
  therefore report those two facts as well as the per-candidate ones.

The reference objects this file owes the consumer:

```text
gTermU (D n) : Nat   -- sq * ceil(2^44 / phi), from tdbBlock D n
gTermL (D n) : Nat   -- sq * floor(2^44 / phi)
gAccU (c j) / gAccL (c j) : Nat
mantX (n i) : Nat × Nat
hitAt (c n i accU accL) : Nat
candPass (c n accU accL) : Bool
rows_of_denote :
  (gProgram c).denote = some 1 →
    (∀ j < c.len, gAccU c j ≤ ACAP ∧ gAccL c j ≤ ACAP ∧
       candPass c (c.lo + j) (gAccU c j) (gAccL c j) = true) ∧
    gAccU c (c.len - 1) ≤ c.finU ∧ c.finL ≤ gAccL c (c.len - 1)
```

Blocked on: the six mantissa-block value lemmas listed in
`Ports/G1215CheckRun.lean`, and then `gProgram_denote`.
-/
