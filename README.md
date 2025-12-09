# Schematic Invariant Synthesis with Limited Grounding
**Bachelor's Thesis | University of Basel | 2024**

This repository contains the implementation of a **Schematic Invariant Synthesis algorithm** integrated into the [Fast Downward](https://www.fast-downward.org/) classical planning system.

Developed as a Bachelor's Thesis at the **AI Basel Group** under the supervision of Tanja Schindler and Prof. Dr. Malte Helmert.

### Thesis
* **[Read the full Thesis (PDF)](./Bachelor_Thesis.pdf)**
* **Official Record:** [University of Basel - Completed Theses](https://ai.dmi.unibas.ch/theses.html)

### Technical Implementation
This project replaces the standard invariant synthesis in Fast Downward's translation module with a hybrid approach based on **Jussi Rintanen's 2017 AAAI paper**.

**Key Features Implemented:**
* **Schematic Invariant Synthesis:** Implements a hybrid algorithm that reduces schematic invariants to ground invariants to verify them efficiently.
* **Limited Grounding:** Uses a specialized limited grounding function $D'(t)$ to instantiate schematic variables with a minimal set of objects, reducing the search space while maintaining correctness.
* **Maximal Clique Enumeration:** Implements the **Tomita et al.** algorithm to generate mutex groups from the discovered ground invariants, which are then used to simplify the planning task.

### Evaluation
The implementation was evaluated on the sciCORE cluster using standard IPC benchmarks (STRIPS).
* **Correctness:** Successfully identifies correct ground invariants and valid plans.
* **Integration:** Fully integrated into the Python translation layer of Fast Downward.

### ⚖️ License & Context

  * **Base System:** Forked from [Fast Downward](https://github.com/aibasel/downward) (specifically the `issue1127` branch supporting negative literals).
  * **License:** GPL v3.
  * For original Fast Downward documentation, see [README\_FAST\_DOWNWARD.md](https://github.com/mariotachikawa/Schematic-Invariant-Synthesis-for-Downward/blob/main/README_FAST_DOWNWARD.md).
