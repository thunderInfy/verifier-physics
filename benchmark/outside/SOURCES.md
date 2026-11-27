# Outside benchmark: sources and access check

Accessed 2026-11-27. "Accessed: yes" means we opened the full text and could read it; every quote in
`items.jsonl` and `known_false.jsonl` comes from that text. A source we could not open is listed under "Dropped" with
the reason, and nothing from it is used.

Text was obtained either as a born-digital PDF text layer or as the OCR layer of a scanned report. For scanned
sources the prose is readable but displayed mathematics is often garbled; where a formula could not be read, the item
says so instead of filling it in.

`id` is the key used by the split rule in `FROZEN.md`. Type is `paper` (journal article, technical report or
survey article) or `notes` (lecture notes).

## Sampled sources (items are collected from these)

| id | type | citation | URL read | accessed | notes |
|---|---|---|---|---|---|
| `shu1997_icase_notes` | notes | C.-W. Shu, *Essentially non-oscillatory and weighted essentially non-oscillatory schemes for hyperbolic conservation laws*, NASA/CR-97-206253, ICASE Report No. 97-65, November 1997. Also in Lecture Notes in Math. 1697 (1998). | https://www3.nd.edu/~zxu2/acms60790S13/Shu-WENO-notes.pdf (copy of the ICASE report; the NTRS record is https://ntrs.nasa.gov/citations/19980007543) | yes | Born-digital text. The NTRS archive link returned only the catalogue page; the FSU mirror (https://data.coaps.fsu.edu/pub/eric/OCP5930/Papers/icase.97-65.pdf) is a scan of the same report. |
| `jiang_shu_1995_weno` | paper | G.-S. Jiang and C.-W. Shu, *Efficient implementation of weighted ENO schemes*, NASA CR-198228, ICASE Report No. 95-73, October 1995; published in J. Comput. Phys. 126 (1996) 202–228. | https://ntrs.nasa.gov/api/citations/19960007052/downloads/19960007052.pdf | yes | TeX-generated PDF whose text layer splits words and drops ligatures ("sc hemes", "nite" for "finite"); quotes are rejoined at those breaks only. We read the ICASE report, not the JCP version (the JCP copy we found returned 404). |
| `gottlieb_shu_1998_tvdrk` | paper | S. Gottlieb and C.-W. Shu, *Total variation diminishing Runge–Kutta schemes*, Math. Comp. 67 (1998) 73–85. | https://www.cfm.brown.edu/people/sg/SSP1.pdf | yes | Born-digital. |
| `gottlieb_shu_tadmor_2001_ssp` | paper | S. Gottlieb, C.-W. Shu and E. Tadmor, *Strong stability-preserving high-order time discretization methods*, SIAM Review 43 (2001) 89–112. | https://www.cfm.brown.edu/people/sg/SSPsiamreview.pdf | yes | Born-digital. |
| `zhang_shu_2010_maxprinciple` | paper | X. Zhang and C.-W. Shu, *On maximum-principle-satisfying high order schemes for scalar conservation laws*, J. Comput. Phys. 229 (2010) 3091–3120. | https://www.math.purdue.edu/~zhan1966/research/paper/maximum_principle.pdf | yes | Author preprint, born-digital. |
| `zhang_shu_2010_euler_positivity` | paper | X. Zhang and C.-W. Shu, *On positivity preserving high order discontinuous Galerkin schemes for compressible Euler equations on rectangular meshes*, J. Comput. Phys. 229 (2010) 8918–8934. | https://www.math.purdue.edu/~zhan1966/research/paper/euler.pdf | yes | Author preprint, born-digital. |
| `zhang_shu_2011_survey` | paper | X. Zhang and C.-W. Shu, *Maximum-principle-satisfying and positivity-preserving high order schemes for conservation laws: survey and new developments*, Proc. R. Soc. A 467 (2011) 2752–2776. | https://www.math.purdue.edu/~zhan1966/research/paper/review.pdf | yes | Author preprint (page header "Proc. R. Soc. A 1–26"), born-digital. |
| `tadmor_1987_viscosity` | paper | E. Tadmor, *The numerical viscosity of entropy stable schemes for systems of conservation laws. I*, Math. Comp. 49 (1987) 91–103. | https://drum.lib.umd.edu/bitstreams/1802811c-4afd-403e-a079-29257a5f0906/download (UMD repository, record https://drum.lib.umd.edu/handle/1903/8424) | yes | Scan with OCR; prose readable, formulas often garbled. The AMS PDF returned HTTP 403. |
| `tadmor_2003_acta` | paper | E. Tadmor, *Entropy stability theory for difference approximations of nonlinear conservation laws and related time-dependent problems*, Acta Numerica 12 (2003) 451–512. | https://www.math.umd.edu/~tadmor/pub/TV+entropy/Tadmor_Acta2003.pdf | yes | Born-digital. Survey article. |
| `heoc_1986_eno3` | paper | A. Harten, B. Engquist, S. Osher and S. R. Chakravarthy, *Uniformly high order accurate essentially non-oscillatory schemes, III*, NASA CR-178101, ICASE Report No. 86-22, April 1986; published in J. Comput. Phys. 71 (1987) 231–303. | https://ntrs.nasa.gov/api/citations/19860016815/downloads/19860016815.pdf | yes | Scan with OCR; prose readable, formulas often garbled. |
| `osher_tadmor_1985_convergence` | paper | S. Osher and E. Tadmor, *On the convergence of difference approximations to scalar conservation laws*, NASA CR-172614, ICASE Report No. 85-28, May 1985; published in Math. Comp. 50 (1988) 19–51. | https://ntrs.nasa.gov/api/citations/19850022413/downloads/19850022413.pdf | yes | Scan with OCR; prose readable, formulas often garbled. We read the ICASE report, not the Math. Comp. version. |
| `harten_1982_highres` | paper | A. Harten, *High resolution schemes for hyperbolic conservation laws*, Courant Institute report DOE/ER/03077-175, NASA CR-169381, March 1982; published in J. Comput. Phys. 49 (1983) 357–393. | https://ntrs.nasa.gov/api/citations/19830002586/downloads/19830002586.pdf | yes | Poor scan with OCR: prose readable with effort, most displayed formulas illegible. We read the report, not the JCP version (the JCP copy we found returned 404). |
| `mfa_oslo_notes` | notes | S. Mishra, U. S. Fjordholm and R. Abgrall, *Numerical methods for conservation laws and related equations*, lecture notes, course MAT4301, University of Oslo (autumn 2023 posting). | https://uio.no/studier/emner/matnat/math/MAT4301/h23/numcl_notes.pdf | yes | Born-digital. |
| `fjordholm_mishra_tadmor_2012_tecno` | paper | U. S. Fjordholm, S. Mishra and E. Tadmor, *Arbitrarily high-order accurate entropy stable essentially nonoscillatory schemes for systems of conservation laws*, SIAM J. Numer. Anal. 50 (2012) 544–573. | https://www.math.umd.edu/~tadmor/references/files/Fjordholm_Mishra_Tadmor_TeCNO%20SINUM2012.pdf | yes | Born-digital (publisher PDF on the author's site). |
| `henrick_aslam_powers_2005_mapped` | paper | A. K. Henrick, T. D. Aslam and J. M. Powers, *Mapped weighted essentially non-oscillatory schemes: achieving optimal order near critical points*, J. Comput. Phys. 207 (2005) 542–567. | https://www3.nd.edu/~powers/paper.list/jcp.weno5m.05.pdf | yes | Born-digital. |

15 sampled sources: 13 `paper`, 2 `notes`.

## Read for the known-false set only (not sampled for `items.jsonl`)

| id | type | citation | URL read | accessed | notes |
|---|---|---|---|---|---|
| `shu_1990_eno_accuracy` | paper | C.-W. Shu, *Numerical experiments on the accuracy of ENO and modified ENO schemes*, ICASE Report No. 90-55, August 1990; published in J. Sci. Comput. 5 (1990) 127–149. | https://ntrs.nasa.gov/api/citations/19900019812/downloads/19900019812.pdf | yes | Scan with OCR. |
| `wang_spiteri_2007_weno_instability` | paper | R. Wang and R. J. Spiteri, *Linear instability of the fifth-order WENO method*, SIAM J. Numer. Anal. 45 (2007) 1871–1901. | https://www.cs.usask.ca/~spiteri/63786-gg.pdf | yes | Author preprint (header "Vol. 0, No. 0"), born-digital. |
| `motamed_macdonald_ruuth_2010_weno_stability` | paper | M. Motamed, C. B. Macdonald and S. J. Ruuth, *On the linear stability of the fifth-order WENO discretization*, Oxford Centre for Collaborative Applied Mathematics Report 10/42 (2010); published in J. Sci. Comput. 47 (2011) 127–149. | https://ora.ox.ac.uk/objects/uuid:b48a4adc-815d-439a-8012-2d7ac5053a28/files/mb5754dd5606d9cf87fb93569b4c54c83 | yes | Report version, born-digital. |

## Dropped or not selected

| candidate | reason |
|---|---|
| M. G. Crandall and A. Majda, *Monotone difference approximations for scalar conservation laws*, Math. Comp. 34 (1980) 1–21 | Not opened: AMS PDF returned HTTP 403; the typeset.io copy returned no content (HTTP 202). Off the list. |
| J. B. Goodman and R. J. LeVeque, *On the accuracy of stable schemes for 2D scalar conservation laws*, Math. Comp. 45 (1985) 15–21 | Not opened: AMS PDF returned HTTP 403; no other open copy found. Off the list. |
| C.-W. Shu, *TVB uniformly high-order schemes for conservation laws*, Math. Comp. 49 (1987) 105–121 | Not opened: AMS PDF returned HTTP 403. Off the list. |
| G.-S. Jiang and C.-W. Shu, J. Comput. Phys. 126 (1996) (journal version) | The copy at ece.uvic.ca returned 404; the DTIC copy of the report was down for maintenance. Replaced by the NTRS copy of the ICASE report (`jiang_shu_1995_weno`). |
| A. Harten, J. Comput. Phys. 49 (1983) (journal version) | ece.uvic.ca copy returned 404. Replaced by the NTRS copy of the 1982 report (`harten_1982_highres`). |
| B. Cockburn and C.-W. Shu, TVB Runge–Kutta local projection DG II, Math. Comp. 52 (1989) | ece.uvic.ca copy returned 404; AMS blocked. Off the list. |
| A. Harten, P. D. Lax and B. van Leer, *On upstream differencing and Godunov-type schemes*, SIAM Rev. 25 (1983) | ece.uvic.ca copy returned 404. Off the list. |
| T. Y. Hou and P. G. LeFloch, *Why nonconservative schemes converge to wrong solutions*, Math. Comp. 62 (1994) | No open copy found (AMS blocked, typeset.io returns no content). Off the list. |
| E. Tadmor, *Approximate solutions of nonlinear conservation laws*, CIME lectures 1997, https://www.math.umd.edu/~tadmor/conf/CIME%20Lectures%201997%20Tadmor.pdf | Readable, not selected: 139 pages with about 46 theorem statements, most overlapping `tadmor_2003_acta`; it would have made one author dominate the item count. Decided before any item was collected. |
| A. M. Rogerson and E. Meiburg, *A numerical study of the convergence properties of ENO schemes*, J. Sci. Comput. 5 (1990) | Not opened (no open copy looked for beyond search results). Its finding is used only as restated and re-tested in `shu_1990_eno_accuracy`. |
