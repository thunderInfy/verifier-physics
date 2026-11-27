# tecno:04: checking the transcription of ^Q

Item `fjordholm_mishra_tadmor_2012_tecno:04` is FALSE because of one sign in the printed numerical entropy flux ^Q.
The REFUTED verdict of `stated_identity` is about the formula as transcribed, so we checked the transcription
against the source before calling the sign a misprint.

## Source read

Publisher PDF on the author's site (the URL in `SOURCES.md`):
https://www.math.umd.edu/~tadmor/references/files/Fjordholm_Mishra_Tadmor_TeCNO%20SINUM2012.pdf, rendered
as page images (PDF pages 8 and 9 = journal pp. 551 and 552). A plain-text fetch of the PDF gave no usable text,
so we read the rendered pages.

Not blind: the person who re-read the page had already read the item's sentence and justification in
`items.jsonl`. This is a second reading of the printed page, not an independent transcription.

## What p. 551 prints (Section 3.1, Lemma 3.1)

- (3.2): F_{i+1/2} = ~F_{i+1/2} − (1/2) D_{i+1/2} [[v]]_{i+1/2}, "Here, D is any symmetric positive definite
  matrix."
- Lemma 3.1 (Tadmor [30]), (3.3): d/dt E(u_i) + (1/Δx)(^Q_{i+1/2} − ^Q_{i−1/2})
  = −(1/(4Δx)) ([[v]]^T_{i+1/2} D_{i+1/2} [[v]]_{i+1/2} + [[v]]^T_{i−1/2} D_{i−1/2} [[v]]_{i−1/2}) ≤ 0,
- "where ^Q_{i+1/2} = ~Q_{i+1/2} **+** (1/2) v̄^T_{i+1/2} D_{i+1/2} [[v]]_{i+1/2}", with an overbar on v (the
  interface average).

p. 552, Lemma 3.2, defines ^Q^k_{i+1/2} = ~Q^{2p}_{i+1/2} **−** (1/2) v̄^T_{i+1/2} D_{i+1/2} ⟨⟨v⟩⟩_{i+1/2}, with
a minus sign.

The rendered page agrees with the collector's transcription (`items.jsonl`): plus sign in Lemma 3.1, minus sign
in Lemma 3.2, overbar on v in both.

## Erratum or later version

Searched on 2026-11-27. We found none:

- Web search for the title with "erratum" / "corrigendum": no erratum for this paper. The only hit was a correction
  to an unrelated J. Sci. Comput. paper (https://link.springer.com/article/10.1007/s10915-018-0758-y).
- No arXiv version of the TeCNO paper turned up. The authors' companion arXiv paper, "ENO reconstruction and ENO
  interpolation are stable" (https://arxiv.org/abs/1112.1131), does not contain Lemma 3.1.
- The author's directory listing https://www.math.umd.edu/~tadmor/pub/TV+entropy/ has
  `Fjordholm_Mishra_Tadmor_SINUM2012.pdf` with no errata file. It does have one for a different paper
  (`Fjordholm_Mishra_Tadmor_FoCM2012+errata.pdf`).
- The precursor conference paper, "Entropy stable ENO scheme" (HYP 2010,
  https://www.math.umd.edu/~tadmor/pub/TV+entropy/Fjordholm_Mishra_Tadmor_HYP2010.pdf), has no first-order
  counterpart of Lemma 3.1. Its high-order Lemma 2.1 (pp. 10–11, the counterpart of Lemma 3.2) defines
  ^Q = ~Q^{2p} **−** (1/2)⟨V̄_{i+1/2}, ^D_{i+1/2} ⟨V⟩_{i+1/2}⟩, with a minus sign. That agrees with Lemma 3.2
  and with the corrected (3.3). It is an earlier paper, not a correction of the 2012 one.
- We did not check the SIAM article page (doi 10.1137/110836961) for a linked erratum.

## Conclusion

Two readings of the printed page agree (ours was not blind), and we found no erratum or later version that fixes
the sign. Both the same paper's Lemma 3.2 and the 2010 precursor use the minus sign. So "misprint" is a fair word for the plus sign in Lemma 3.1, given those limits. In code and in the
results we say "the identity (3.3) as transcribed is REFUTED". With the minus sign of Lemma 3.2 it is VERIFIED
(`schemes/identity/entropy-balance-*-corrected.json`).
