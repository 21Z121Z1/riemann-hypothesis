import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.RestrictionEqZeroIffMemVanishingFiltration
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.HasseKpAlgebraMapKl
import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle0013

-- bundled from Formalism.PeriodIntegrals.HasseJidPow
section
noncomputable section

open Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.Gaps.EtaleWeightGaps

def PI.HasseJidPow : Prop :=
  ∀ {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ} (X : PJ D B P j) (la : HeightOneSpectrum (𝓞 B.KO))
    {N : ℕ} {wL : WeightFamilies.Wt D j} (w : Fin N → B.Cusp j wL) (u : WeightFamilies.Wt D j) (β : Idx D j N →₀ ℕ) (a : ℕ)
    (x : Lw X la w),
    x ∈ JHfr X la w u a → hasse X la w β x ∈ JHfr X la w u (a - β.sum fun _ n => n)
end
end

-- bundled from Formalism.PeriodIntegrals.HassePresH
section
noncomputable section

open Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.Gaps.EtaleWeightGaps

def PI.HassePresH : Prop :=
  ∀ {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ} (X : PJ D B P j) (la : HeightOneSpectrum (𝓞 B.KO))
    {N : ℕ} {wL : WeightFamilies.Wt D j} (w : Fin N → B.Cusp j wL) (u : WeightFamilies.Wt D j) (β : Idx D j N →₀ ℕ) (x : Lw X la w),
    x ∈ Hfr X la w u → hasse X la w β x ∈ Hfr X la w u
end
end

-- bundled from Formalism.PeriodIntegrals.RepsIndep
section
noncomputable section

namespace PI.RepsIndep

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.MainNotions.UniformConstantsAndStatements NumberField
open scoped ENNReal

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def StepFix (D : D7) : Prop :=
  ∀ {T : D.host.E} (F0 : FlagG (VS D) D.R.rS T) (Λ Λ' : Submodule (𝓞 D.host.E) (VS D).V),
    IsRowLat D F0 Λ → IsRowLat D F0 Λ' →
    ∀ γ ∈ stabF D F0, Formalism.HermitianLatticesTheory.gmap γ Λ' = Λ →
      ∃ γ₀ ∈ stabF D F0, (∀ a, γ₀ (F0.e a) = F0.e a) ∧ Formalism.HermitianLatticesTheory.gmap γ₀ Λ' = Λ

def StepCnt (D : D7) : Prop :=
  ∀ {T : D.host.E} (T' : D.host.E) (F0 : FlagG (VS D) D.R.rS T) (Λ : Submodule (𝓞 D.host.E) (VS D).V),
    IsRowLat D F0 Λ →
    ∀ γ₀ ∈ stabF D F0, (∀ a, γ₀ (F0.e a) = F0.e a) →
      ∀ Z : Cnt.GramM D, cntZ D T' (Formalism.HermitianLatticesTheory.gmap γ₀ Λ) (lf D F0) Z = cntZ D T' Λ (lf D F0) Z

def Assembly : Prop :=
  ∀ D : D7, StepFix D → StepCnt D → ∀ u u' : D.what₂.Word, Formalism.MainNotions.S.MainBoundWithDegrees.NuTotIndep D u u'

end PI.RepsIndep
end
end

