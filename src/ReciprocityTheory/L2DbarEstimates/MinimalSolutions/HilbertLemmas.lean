import ReciprocityTheory.L2DbarEstimates.MinimalSolutions.Bundle0001
import ReciprocityTheory.L2DbarEstimates.MinimalSolutions.Bundle0002

namespace ReciprocityTheory.L2DbarEstimates

theorem hilbertLemmas (E H₁ H₂ : Type*) [AddCommGroup E] [Module ℂ E]
    [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁] [CompleteSpace H₁]
    [NormedAddCommGroup H₂] [InnerProductSpace ℂ H₂] [CompleteSpace H₂] :
    CVXStatement H₁ ∧ RieszOnRangeStatement E H₁ ∧ MinimalSolutionStatement E H₁ ∧
      SplitStatement E H₁ H₂ ∧ HormanderLemmaStatement E H₁ H₂ ∧
      OntoWithBoundStatement E H₁ H₂ :=
  ⟨cvx H₁, rieszOnRange E H₁, minimalSolution E H₁, split E H₁ H₂, hormanderLemma E H₁ H₂,
    ontoWithBound E H₁ H₂⟩

end ReciprocityTheory.L2DbarEstimates
