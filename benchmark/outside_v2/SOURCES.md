# Outside benchmark v2: sources and access check

Accessed 2026-11-28. "Accessed: yes" means we opened the full text (through a text extraction of the PDF at the URL
given) and could read it; every quote in `items.jsonl` and `known_false.jsonl` comes from that text. A source we could
not open is listed under "Dropped" with the reason, and nothing from it is used.

None of these sources, nor another version of the same work, appears in `benchmark/outside/SOURCES.md` (v1).

Where we read a preprint or report, the journal reference after "published in" is for identification only: we did not
open the journal version, and its volume and page numbers were not checked against it.

Type is `paper` (journal article, preprint or technical report) or `notes` (lecture notes).

## Sampled sources

| id | type | topic | citation | URL read | accessed | notes |
|---|---|---|---|---|---|---|
| `kurganov_tadmor_2000_central` | paper | central schemes, TVD, semi-discrete | A. Kurganov and E. Tadmor, *New high-resolution central schemes for nonlinear conservation laws and convection–diffusion equations*, J. Comput. Phys. 160 (2000) 241–282. | https://www.math.umd.edu/~tadmor/centpack/publications/files/KT_semi-discrete.JCP00-centpack.pdf | yes | Publisher PDF on the author's site. |
| `chandrashekar_2013_kep_es` | paper | entropy stability, kinetic energy preservation, systems | P. Chandrashekar, *Kinetic energy preserving and entropy stable finite volume schemes for compressible Euler and Navier–Stokes equations*, arXiv:1209.4994v1 (2012); published in Commun. Comput. Phys. 14 (2013) 1252–1286. | https://arxiv.org/pdf/1209.4994v1 | yes | We read the arXiv v1 preprint. |
| `ketcheson_2019_relaxation_rk` | paper | time stepping (relaxation Runge–Kutta) | D. I. Ketcheson, *Relaxation Runge–Kutta methods: conservation and stability for inner-product norms*, arXiv:1905.09847v1 (2019); published in SIAM J. Numer. Anal. 57 (2019) 2850–2870. | https://arxiv.org/pdf/1905.09847v1 | yes | We read the arXiv v1 preprint. |
| `cockburn_shu_2001_rkdg_review` | paper | DG, TVB limiters, SSP time stepping | B. Cockburn and C.-W. Shu, *Runge–Kutta discontinuous Galerkin methods for convection-dominated problems*, J. Sci. Comput. 16 (2001) 173–261. | https://ccam.xmu.edu.cn/teacher/jxqiu/undergraduate/RKDG_Review.pdf | yes | Publisher PDF (course mirror). Review article. |
| `guermond_popov_2016_invariant_domains` | paper | invariant domains / positivity, systems, multi-D, continuous FE | J.-L. Guermond and B. Popov, *Invariant domains and first-order continuous finite element approximation for hyperbolic systems*, arXiv:1509.07461v1 (2015); published in SIAM J. Numer. Anal. 54 (2016) 2466–2489. | https://arxiv.org/pdf/1509.07461v1 | yes | We read the arXiv v1 preprint. |
| `borges_costa_don_2006_wenoz` | paper | high-order reconstruction (WENO-Z) | R. Borges, B. Costa and W. S. Don, *An improved weighted essentially non-oscillatory scheme for hyperbolic conservation laws*, report dated June 23, 2006, DTIC ADA458949; journal version (with M. Carmona) J. Comput. Phys. 227 (2008) 3191–3211. | https://ia803107.us.archive.org/8/items/DTIC_ADA458949/DTIC_ADA458949.pdf | yes | We read the 2006 report, not the JCP version (paywalled). |
| `chen_shu_2017_esdg` | paper | entropy stable DG, summation by parts, systems, multi-D | T. Chen and C.-W. Shu, *Entropy stable high order discontinuous Galerkin methods with suitable quadrature rules for hyperbolic conservation laws*, J. Comput. Phys. 345 (2017) 427–461. | https://www.math.umd.edu/~tadmor/references/files/Chen%20&%20Shu%20entropy%20stable%20DG%20JCP2017.pdf | yes | Publisher PDF hosted on a third party's site. |
| `cockburn_cime_dg_notes` | notes | DG, cell entropy inequality, TVDM/TVBM limiters | B. Cockburn, *An introduction to the discontinuous Galerkin method for convection-dominated problems*, lecture notes, in: Advanced Numerical Approximation of Nonlinear Hyperbolic Equations (CIME 1997), Lecture Notes in Math. 1697 (1998) 151–268. | https://www-users.cse.umn.edu/~bcockbur/lecture_notes/cime.pdf | yes | Author's copy; TeX PDF whose text layer splits some words ("Co c kburn"); quotes rejoined at those breaks only. Same topic area as `cockburn_shu_2001_rkdg_review` but a different work. |
| `hu_adams_shu_2013_pp_flux_limiter` | paper | positivity-preserving flux limiter, Euler | X. Y. Hu, N. A. Adams and C.-W. Shu, *Positivity-preserving method for high-order conservative schemes solving compressible Euler equations*, arXiv:1203.1540v5 (2012, title on arXiv: "Positivity-preserving flux limiters for high-order conservative schemes"); published in J. Comput. Phys. 242 (2013) 169–180. | https://arxiv.org/pdf/1203.1540v5 | yes | We read the arXiv v5 preprint. |
| `barsukow_uzh_notes` | notes | monotone, TVD, Lax–Wendroff theorem, entropy | W. Barsukow, *Introduction to conservation laws: theory and numerics*, lecture notes, University of Zurich, 2021/22. | http://user.math.uzh.ch/barsukow/exercises2122/conservationlaws.pdf | yes | Born-digital course notes. |

10 sampled sources: 8 `paper`, 2 `notes`.

## Dropped or not selected

| candidate | reason |
|---|---|
| E. Tadmor, *Selected topics in approximate solutions of nonlinear conservation laws. High-resolution central schemes*, IMA 2009 lecture notes | Readable (search result), not selected: overlaps `kurganov_tadmor_2000_central` in topic and author. Decided before any item was collected. |
| R. Borges, M. Carmona, B. Costa, W. S. Don, J. Comput. Phys. 227 (2008) (journal version) | Paywalled (ScienceDirect). Replaced by the 2006 DTIC report (`borges_costa_don_2006_wenoz`). |
