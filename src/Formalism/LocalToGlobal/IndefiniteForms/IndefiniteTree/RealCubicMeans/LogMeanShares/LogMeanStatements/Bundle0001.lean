import Mathlib

-- bundled from Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.RealCubicMeans.LogMeanShares.LogMeanStatements.HSClaim
section
noncomputable section

namespace Formalism.NormVectorIdentities.Items

def hsLogRho (C n D j0 Λ δ h : ℝ) : ℝ :=
  Real.log Λ + C * Real.log (n * D * j0 * δ * (2 + |h| + Real.log Λ))

def hsG (D n : ℝ) : ℝ := (D + 1) * (Real.log n + 1) / 2 + 1

def hsR (T D : ℕ) : ℝ := (Nat.choose (T - 1) D : ℝ)

def hsZ (T D : ℕ) (δ d : ℝ) : ℝ := 1 - hsR T D * δ / d

def HSClaimS (C : ℝ) (T D : ℕ) (n j0 Λ β ΛD ΛT J δ h d deg : ℝ) : Prop :=
  0 ≤ hsZ T D δ d ∧ hsZ T D δ d ≤ 1 ∧
    (1 - hsZ T D δ d) * ((T : ℝ) * h - 3 * ((D : ℝ) + 1) * |h| - J
        - C * (D : ℝ) ^ 2 * Real.log (Real.exp (hsLogRho C n D j0 Λ δ h) * T)
        - ((T : ℝ) + D + 1) * Real.log β - ((T : ℝ) + (D : ℝ) ^ 2) * (hsG D n + 2))
      - hsZ T D δ d * ((T : ℝ) * Real.log (2 * Real.exp (hsLogRho C n D j0 Λ δ h) * Real.sqrt β)
        + Real.log ΛD + Real.log ΛT) ≤ deg / d

end Formalism.NormVectorIdentities.Items
end
end

-- bundled from Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.RealCubicMeans.LogMeanShares.LogMeanStatements.LineDegreeClosedFormula
section
noncomputable section

open NumberField IsDedekindDomain

namespace Formalism.NormVectorIdentities.Items

variable (K : Type) [Field K] [NumberField K]

def degLineS (nFin : HeightOneSpectrum (𝓞 K) → ℝ) (nInf : (K →+* ℂ) → ℝ) : ℝ :=
  -((∑ᶠ la, Real.log (nFin la)) + ∑ σ : K →+* ℂ, Real.log (nInf σ)) / (Module.finrank ℚ K : ℝ)

def LineDegreeClosedFormula (nFin : HeightOneSpectrum (𝓞 K) → ℝ) (nInf : (K →+* ℂ) → ℝ) (corr : ℝ) (p q : ℕ) (logOm dK rd : ℝ) :
    Prop :=
  degLineS K nFin nInf + corr = -(((p : ℝ) - q) / 2 * logOm + (q : ℝ) * (2 * Real.log (Real.sqrt dK) - Real.log rd))

end Formalism.NormVectorIdentities.Items
end
end

-- bundled from Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.RealCubicMeans.LogMeanShares.LogMeanStatements.MeanLogS
section
noncomputable section

open NumberField

namespace Formalism.NormVectorIdentities.Items

section abelian₂

variable {K V ι : Type*} [Field K] [NumberField K] [AddCommGroup V] [Module K V] [Fintype ι] [DecidableEq ι]

def vecS (b : Module.Basis ι K V) (v : InfinitePlace K) (x : V) : ι → ℂ :=
  fun i => v.embedding (b.repr x i)

def fcoordS (b : Module.Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ) (v : InfinitePlace K) (x : V) : ι → ℂ :=
  Matrix.mulVec (X v)⁻¹ (vecS b v x)

def cnormS (u : ι → ℂ) : ℝ := Real.sqrt (∑ i, ‖u i‖ ^ 2)

def normS (b : Module.Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ) (v : InfinitePlace K) (x : V) : ℝ :=
  cnormS (fcoordS b X v x)

variable (K) in

def nPlS : ℕ := Fintype.card (InfinitePlace K)

end abelian₂

variable {K : Type} [Field K] [NumberField K] [StarRing K] {n : ℕ}

def meanLogS (X : InfinitePlace K → Matrix (Fin n) (Fin n) ℂ) (x : Fin n → K) : ℝ :=
  (1 / (nPlS K : ℝ)) * ∑ v, Real.log (normS (Pi.basisFun K (Fin n)) X v x ^ 2)

def LamS (M : Submodule (𝓞 K) (Fin n → K)) (X : InfinitePlace K → Matrix (Fin n) (Fin n) ℂ) (La : ℝ) : Prop :=
  ∀ x ∈ M, x ≠ 0 → -(2 * La) ≤ meanLogS X x

end Formalism.NormVectorIdentities.Items
end
end

