# TPWL_Final_Project

## GitHub configuration

Welcome to our MA4N1 project. Our project is contained in the file called TPWLFinalProject.lean

Each person also has their own file, these files contain each person's rough work. The format we followed was that each person worked on their code in their personal section before pushing the completed code to the main file. The content of the project is completely contained within the TPWLFinalProject file. 

The file begins with some ancillary theorems necessary for the proof, and then proceeds with the proof. First proving existence, then using existence to prove uniqueness. After the proof, we prove some corollaries of Riesz's theorem.

We are happy for the group to be given a joint mark for the project (we do not want it to be marked individually). 

Summary of everyone's contributions:

- Archie
Completed the setup of Riesz Representation theorem (Outline 1-3). Proved Pythagorus Theorem and completed the proof for the polarization identity (Mike wrote the statement, I wrote the proof). Proved a corrollary of Riesz that states that elements of the dual space attain their norms.

- Mateo:
Set up the Github repository, completed the first parts of the existence proof (the parts before Mike's section). Proved the Functional_Coker_Dim lemma, the exists_unit_vector_of_finrank_one lemma, proved the UandUperpCompl lemma, proved the PerpIsPerp lemma, proved the Quotient_Iso_Perp lemma.

- Thomas:
Completed the uniqueness part of the Riesz Representatin Theorem (Outline steps 8-9) and also proved the "isClosed_ker_of_strongDual lemma", which replaces the imported lemma "ContinuousLinearMap.isClosed_ker" from "Mathlib.Topology.Algebra.Module.LinearMap"

- Mike:

 completed the final steps of the existence part of the Riesz Representation Theorem proof (Outline Steps 6–7) and also formalized two interesting lemmas: the polarization identity and the parallelogram law in complex inner product spaces. (Note / acknowledgement: Because my local Lean was unreliable (stuck loading), I wrote and tested the code in Lean 4 Web and then sent it to Mateo, who kindly tested it in the repository environment and integrated/committed it on my behalf (so the Git history may show Mateo as the committer).)


