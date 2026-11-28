# Outside benchmark v3: sources and access check

Accessed 2026-11-28. "Accessed: yes" means we opened the full text (through a text extraction of the PDF at the URL
given) and could read it; every quote in `items.jsonl` and `known_false.jsonl` comes from that text. A source we could
not open, or whose text could not be quoted, is listed under "Dropped" with the reason, and nothing from it is used.

None of these sources, nor another version of the same work, appears in `benchmark/outside/SOURCES.md` (v1) or
`benchmark/outside_v2/SOURCES.md` (v2). The collector read those two files only to exclude their sources.

**Topic choice is not independent of v1 and v2.** The list of topics to cover (time stepping, limiters, monotone and
TVD schemes, entropy, positivity, high-order reconstruction, DG, systems, multi-D) was written by the team after
seeing the v1 and v2 results. The sentences within each source are then taken by the fixed sampling rule in
`README.md`, not chosen.

Where we read a preprint or report, the journal reference after "published in" is for identification only: we did not
open the journal version, and its volume and page numbers were not checked against it.

Type is `paper` (journal article, preprint or technical report) or `notes` (lecture notes).

## Sampled sources

| id | type | topic | citation | URL read | accessed | notes |
|---|---|---|---|---|---|---|
| `jiang_shu_1993_dg_cell_entropy` | paper | DG, entropy, multi-D, time stepping | G. Jiang and C.-W. Shu, *On cell entropy inequality for discontinuous Galerkin methods*, NASA CR-191493, ICASE Report No. 93-37, June 1993; published in Math. Comp. 62 (1994) 531–538. | https://ntrs.nasa.gov/api/citations/19940006808/downloads/19940006808.pdf | yes | Scan with OCR. Prose readable; most displayed formulas garbled. No numbered theorems: abstract and concluding remarks only. |
| `shu_osher_1988_eno2` | paper | ENO reconstruction, TVD Runge–Kutta time stepping, systems, multi-D | C.-W. Shu and S. Osher, *Efficient implementation of essentially non-oscillatory shock capturing schemes, II*, NASA CR-181656, ICASE Report No. 88-24, April 1988; later published in J. Comput. Phys. (journal reference not checked). | https://ntrs.nasa.gov/api/citations/19880014833/downloads/19880014833.pdf | yes | Scan with OCR; prose readable. (Part I, ICASE 87-33, had no PDF we could find; not used.) |
| `ranocha_etal_2020_rrk_entropy` | paper | time stepping (relaxation RK), entropy stability, systems | H. Ranocha, M. Sayyari, L. Dalcin, M. Parsani and D. I. Ketcheson, *Relaxation Runge–Kutta methods: fully-discrete explicit entropy-stable schemes for the compressible Euler and Navier–Stokes equations*, arXiv:1905.09129v1 (2019); published in SIAM J. Sci. Comput. 42 (2020) A612–A638. | https://arxiv.org/pdf/1905.09129v1 | yes | We read the arXiv v1 preprint. A different work from the v2 source by one of its authors (arXiv:1905.09847). |
| `osher_chakravarthy_1983_entropy` | paper | TVD, limiters, entropy condition, systems | S. Osher and S. Chakravarthy, *High resolution schemes and the entropy condition*, NASA CR-172218, ICASE report, September 1983; published in SIAM J. Numer. Anal. 21 (1984) 955–984. | https://ntrs.nasa.gov/api/citations/19840002768/downloads/19840002768.pdf | yes | Scan with OCR; prose readable, formulas often garbled. |
| `yee_1989_tvd_tm` | notes | TVD, upwind and symmetric limiters, implicit time stepping, systems, multi-D | H. C. Yee, *A class of high-resolution explicit and implicit shock-capturing methods*, NASA TM-101088, February 1989 (lecture notes, von Karman Institute lecture series). | https://ntrs.nasa.gov/api/citations/19890016281/downloads/19890016281.pdf | yes | Scan with OCR, long (we read the extraction up to its 400,000-character limit, which covers the abstract and the body through the concluding remarks of Section VIII; see the per-item locations). Typed as notes: it is a survey written as lecture notes. |
| `perthame_shu_1993_positivity` | paper | positivity, Euler, finite volume, 2D | B. Perthame and C.-W. Shu, *On positivity preserving finite volume schemes for Euler equations*, NASA CR-191534, ICASE Report No. 93-67, 1993; published in Numer. Math. 73 (1996) 119–130. | https://ntrs.nasa.gov/api/citations/19940014844/downloads/19940014844.pdf | yes | Scan with OCR, extracted almost one word per line; readable when rejoined. |
| `shu_am257_notes` | notes | monotone, TVD, Godunov/Lax–Friedrichs/Roe/E-O schemes, ENO/WENO, DG | C.-W. Shu, *Numerical methods for hyperbolic conservation laws (AM257)*, course notes, Brown University, semester I 2006, typed by a student (A. Klöckner). | https://andreask.cs.illinois.edu/dl/academic/notes/257/257.pdf | yes | Born-digital. Student-typed notes of lectures; a different work from the v1 source `shu1997_icase_notes`. |
| `yang_xiong_qiu_xu_2014_mpp_fv` | paper | maximum-principle-preserving flux limiters, high-order finite volume, RK time stepping | P. Yang, T. Xiong, J.-M. Qiu and Z. Xu, *High order maximum principle preserving finite volume method for convection dominated problems*, arXiv:1404.4041v1 (2014); later published in J. Sci. Comput. (journal reference not checked). | https://arxiv.org/pdf/1404.4041v1 | yes | We read the arXiv v1 preprint. |

8 sampled sources: 6 `paper`, 2 `notes`.

## Dropped or not selected

| candidate | reason |
|---|---|
| B. Cockburn and C.-W. Shu, *The Runge–Kutta discontinuous Galerkin method for conservation laws V: multidimensional systems*, ICASE Report 97-43 (J. Comput. Phys. 141 (1998)) | Opened (https://conservancy.umn.edu/server/api/core/bitstreams/5d08d516-b9da-4985-8c44-a769532ab0cc/content; the DTIC copy https://apps.dtic.mil/sti/pdfs/ADA329450.pdf returned almost no text), but the text layer drops nearly every digit ("This is the fth paper", "( . )" for equation numbers), so statements and formulas could not be quoted without filling them in. Off the list. |
| C.-W. Shu and S. Osher, *Efficient implementation of ENO shock-capturing schemes* (Part I), ICASE Report 87-33 / J. Comput. Phys. 77 (1988) | No open PDF found (NTRS record only; a guessed NTRS download URL returned HTTP 404). Off the list. |
| Z. Xu, *Parametrized maximum principle preserving flux limiters for high order schemes solving hyperbolic conservation laws: one-dimensional scalar problem*, Math. Comp. 83 (2014) | No open copy found (AMS). Off the list; its limiter is covered through `yang_xiong_qiu_xu_2014_mpp_fv`. |
| A. Harten, *On a class of high resolution total-variation-stable finite-difference schemes*, SIAM J. Numer. Anal. 21 (1984) | Not opened: only OSTI catalogue records found; the NTRS PDF the search offered is the 1982 report already used in v1 (`harten_1982_highres`). Off the list. |
| B. Cockburn, S. Hou and C.-W. Shu, RKDG IV: the multidimensional case, Math. Comp. 54 (1990) | No open copy found (AMS). Off the list. |
