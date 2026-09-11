# Algorithmic Comparisons for the Low-Weight Polynomial Multiple Problem (LWPM)

This repository contains the code and experimental artifacts supporting a paper.

> **Algorithmic Comparisons for the Low-Weight Polynomial Multiple Problem**

The goal of this project is to experimentally compare fundamentally different
algorithmic paradigms for solving the **Low-Weight Polynomial Multiple (LWPM)**
problem, a core computational task in the cryptanalysis of stream ciphers.

The repository is provided for **reproducibility and transparency** and is
intended to accompany the experimental sections of the paper.

---

## Overview

The Low-Weight Polynomial Multiple (LWPM) problem asks to find a polynomial
\( Q(x) \) such that the product \( P(x)Q(x) \) has small Hamming weight,
subject to degree constraints.

This repository implements and evaluates several algorithmic approaches to LWPM:

- **Optimisation-based solvers**
  - Mixed Integer Linear Programming (MILP)
  - Maximum Satisfiability (MAXSAT), including XOR-MAXSAT formulations

- **Coding-theoretic solvers**
  - Reduction of LWPM to Syndrome Decoding (SDP)
  - Classical Information Set Decoding (ISD), using Stern's algorithm

The experiments focus on **bounded-degree and low-weight regimes** that are
directly relevant to cryptanalytic applications.




---

## Some instructions

You can find some instructions on how to reproduce our experiments here and some in the  respective folders.


**How to run IGMaxHS (our MAX-SAT approach):**

The translation of the LWPM problem into MAX-SAT is based on the MAXSAT solver IGMaxHS by Ole Lubke [[1],[2]].

**Steps:**

1. Follow the intslation instructions from [[2]].
2. Build the dynamic IGMaxHS library that is loaded by Python ("make lsh" in the repository's root). This will create build/dynamic/lib/libmaxhs.so.
3. Add the files code_igmax_less_than_w.py and code_igmax_w_fixed.py in incremental-gaussmaxhs\python\ directory
4. Run files:
   a) python code_igmax_less_than_w.py
   b) python code_igmax_w_fixed.py

## References
<a id="1">[1]</a>
Lübke, Ole (2024).
IGMaxHS-An Incremental MaxSAT Solver with Support for XOR Clauses.
arXiv preprint arXiv:2410.15897

<a id="2">[2]</a>
Lübke, Ole
IGMaxHS solver (https://collaborating.tuhh.de/cda7728/incremental-gaussmaxhs)
