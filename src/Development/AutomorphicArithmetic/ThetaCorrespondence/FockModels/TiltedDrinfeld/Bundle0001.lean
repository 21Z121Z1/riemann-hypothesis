import Development.AutomorphicArithmetic.ThetaCorrespondence.FockModels.TiltedDrinfeld.ExistsCoeEqUntiltPFlat
import Development.AutomorphicArithmetic.ThetaCorrespondence.FockModels.TiltedDrinfeld.ExistsBeta
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0142
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLocalPrimeAinf
import Development.AutomorphicArithmetic.ThetaCorrespondence.LocalComparison.Bundle0001
import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0086

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.FockModels.TiltedDrinfeld.BasedP
section
noncomputable section

namespace period_ring_base

open Formalism.Per6 hiding σB aB
open GroundTheory.PAdicHodge DeRhamPotentiallySemistable.DRPst PfDRPst Matrix

theorem base_κ_cont (l : ℕ) [Fact l.Prime] : Continuous (κ : GQ l → ℚ_[l]) := continuous_κ l

theorem base_no_kummer (l : ℕ) [Fact l.Prime] : ∀ L : Fld l, FiniteDimensional ℚ_[l] L → ∀ x : B l,
    ¬ ∀ σ ∈ L.fixingSubgroup, σB σ x - x = qB l (κ σ) * t l := by
  intro L hL x h
  obtain ⟨P, AI, ⟨T0⟩⟩ := GlobalTheory.MemLoc.exists_locPrime_tied l
  obtain ⟨T⟩ := UpperTheory.Lit.Cmp.locTied6 l P AI ⟨T0⟩
  obtain ⟨β, hβ⟩ := UpperTheory.Lit.Drps.exists_beta T
  have := GlobalTheory.Pst.nontrivial_B P
  refine GlobalTheory.Pst.StLat.kummer_not_frac l P AI T0 ⟨L, hL⟩ 1 (T.eB.symm (x + qB l β * t l)) one_ne_zero fun g hg => ?_
  apply T.eB.injective
  rw [map_one, one_mul, one_mul, one_mul, one_mul, map_sub, DualB.tie_σB T, RingEquiv.apply_symm_apply, hβ, map_add,
    ← h g hg]
  ring

end period_ring_base
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.FockModels.TiltedDrinfeld.LinearIndepOnOfInvariant
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module GlobalTheory.Pst

namespace UpperTheory.Lit.Drps

variable {l : ℕ} [Fact l.Prime]

section Coord

variable {S : Type} [CommRing S] [Algebra ℚ_[l] S] {V : Type} [AddCommGroup V] [Module ℚ_[l] V]
  {d : ℕ} (b : Basis (Fin d) ℚ_[l] V)

def cS (i : Fin d) : V ⊗[ℚ_[l]] S →ₗ[ℚ_[l]] S :=
  (TensorProduct.lid ℚ_[l] S).toLinearMap ∘ₗ (b.coord i).rTensor S

@[simp] theorem cS_tmul (i : Fin d) (v : V) (s : S) : cS b i (v ⊗ₜ s) = b.coord i v • s := by
  simp [cS]

end Coord

section Periods

variable {G : Type} [Group G] {K₀ K : Type} [Field K₀] [Field K]
    [Algebra ℚ_[l] K₀] [Algebra ℚ_[l] K] [Algebra K₀ K] [IsScalarTower ℚ_[l] K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra ℚ_[l] B] [Algebra K₀ B] [IsScalarTower ℚ_[l] K₀ B]
    [Algebra ℚ_[l] BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower ℚ_[l] K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower ℚ_[l] K₀ BdR]
    (PD : PeriodData G ℚ_[l] K₀ K B BdR)
    {V : Type} [AddCommGroup V] [Module ℚ_[l] V] [FiniteDimensional ℚ_[l] V]
    {d : ℕ} (b : Basis (Fin d) ℚ_[l] V) (ρ : Representation ℚ_[l] G V)

end Periods

section Pst

variable {P : LocPrime l} {AI : LocAinf l P} {K : FinExt l}
  {V : Type} [AddCommGroup V] [Module ℚ_[l] V] [FiniteDimensional ℚ_[l] V]
  (ρ : Representation ℚ_[l] ↥(GK K) V)

end Pst

end UpperTheory.Lit.Drps
end
end

