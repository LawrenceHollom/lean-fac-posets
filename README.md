# The structure of FAC posets: a Lean verification

This repository contains a Lean formalisation of all statements in the most recent draft (as of 2026-11-23) of my (Lawrence Hollom) paper *The structure of FAC posets and the Aharoni–Korman conjecture*.
This README is human-written, but the rest of the project is entirely AI-generated from the LaTeX source code of the paper. 
I have carefully checked (by reading it myself) that the statement of the main theorems do indeed line up with the statements in the pdf.

While it proves every statement from the paper, there are a few places in which the proof techniques in the Lean and the pdf deviate. 
These are highlighted in comments in the annotated version of the paper, available [on my website](https://lawrencehollom.github.io/).

The [proof map](ROADMAP.md) describes the correspondence between the manuscript and the Lean code.
The project contains roughly 14k LOC.

One thing which may at first look a bit strange is the existence of both `PaperChainExtension` and `H`, which might make it sound as though this proof isn't using the definition from the paper. 
That is somewhat true: for ease of formalisation, the version here works with a version of H(P) with formal endpoints added. However, a proof is given in `DirectonalQuotients.lean` that these two extensions are identical up to these endpoints.