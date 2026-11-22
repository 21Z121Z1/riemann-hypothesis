import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0021
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.CombAtSingleZero
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCombAt
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0029
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RestrictedBlockUnipotentSymmetric
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LevelHyperspecialTrivialCharacterSplitsOffPlaces
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CharacterNormMatrixInverse.FmatMulInv
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.LevelSubgroupCharacterUnitary
import Formalism.LocalToGlobal.SiegelLatticeTheory.TraceIntegralEstimates.Bundle0012
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0303
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsSingle
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0052
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.PoincareInHH
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.InHHAlg
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.Bundle0006
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ProjectionMovesTypeVectorsModLevel
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0363
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0077
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0055
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0030
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0358
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0352
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0070
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0817
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0351
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.FrameTopAlt
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilDatumTransportSourceRationalIsometry
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0104
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0296
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0354
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0214
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0017
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0012
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0186
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1736
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0897
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0265
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0302
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0134
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0494
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0247
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0277
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0227
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0252
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0183
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0228

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsCoprimeMultiplierLevelCharacterSumCongr
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.NPartConj

variable (I : Formalism.MainNotions.S.AutInst)

theorem nsmul_mL' {g k : ℕ} {v : Formalism.L2.SG.HidaSetting.VA I} (hv : v ∈ Formalism.L2.SG.HidaSetting.mL I g) :
    ((k : I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F) • v) ∈ Formalism.L2.SG.HidaSetting.mL I g := by
  rw [Nat.cast_smul_eq_nsmul]; exact nsmul_mem hv k

theorem nsmul_Lf' {k : ℕ} {v : Formalism.L2.SG.HidaSetting.VA I} (hv : v ∈ I.Lf) :
    ((k : I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F) • v) ∈ I.Lf := by
  rw [Nat.cast_smul_eq_nsmul]; exact nsmul_mem hv k

theorem mL_le_Lf' (g : ℕ) : Formalism.L2.SG.HidaSetting.mL I g ≤ I.Lf :=
  Submodule.span_le.2 (by rintro _ ⟨y, hy, rfl⟩; exact nsmul_Lf' I hy)

theorem K_mL' {x : I.Gf} (hx : x ∈ I.Kset) {g : ℕ} {v : Formalism.L2.SG.HidaSetting.VA I}
    (hv : v ∈ Formalism.L2.SG.HidaSetting.mL I g) : I.fmat x *ᵥ v ∈ Formalism.L2.SG.HidaSetting.mL I g := by
  have h : Formalism.L2.SG.HidaSetting.mL I g ≤
      (Formalism.L2.SG.HidaSetting.mL I g).comap (Formalism.L2.SG.Pf.unitaryCongruence.mvO I (I.fmat x)) :=
    Submodule.span_le.2 (by
      rintro _ ⟨y, hy, rfl⟩
      show I.fmat x *ᵥ ((g : I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F) • y) ∈ Formalism.L2.SG.HidaSetting.mL I g
      rw [Matrix.mulVec_smul]
      exact Formalism.L2.SG.Pf.unitaryCongruence.smul_mem_mL I (Formalism.L2.SG.Pf.unitaryCongruence.K_mv I hx hy))
  exact h hv

theorem K_sub_mL' {x : I.Gf} (hx : x ∈ I.Kset) {g : ℕ} {v : Formalism.L2.SG.HidaSetting.VA I}
    (hv : v ∈ Formalism.L2.SG.HidaSetting.mL I g) : (I.fmat x - 1) *ᵥ v ∈ Formalism.L2.SG.HidaSetting.mL I g := by
  rw [Matrix.sub_mulVec, Matrix.one_mulVec]; exact sub_mem (K_mL' I hx hv) hv

theorem hcn_of {x : I.Gf} (hx : x ∈ I.Kset) {g : ℕ} {n N N0 : Formalism.L2.SG.HidaSetting.VA I}
    (hN : I.fmat x *ᵥ N0 = N) {c : ℕ}
    (h : (c : I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F) • (n - N0) ∈ Formalism.L2.SG.HidaSetting.mL I g) :
    (c : I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F) • (I.fmat x *ᵥ n) - (c : I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F) • N ∈
      Formalism.L2.SG.HidaSetting.mL I g := by
  have e : (c : I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F) • (I.fmat x *ᵥ n) - (c : I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F) • N =
      I.fmat x *ᵥ ((c : I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F) • (n - N0)) := by
    rw [Matrix.mulVec_smul, Matrix.mulVec_sub, hN, smul_sub]
  rw [e]; exact K_mL' I hx h

theorem conj_sub (x m : I.Gf) (n : Formalism.L2.SG.HidaSetting.VA I) :
    (I.fmat (x⁻¹ * m * x) - 1) *ᵥ n = I.fmat x⁻¹ *ᵥ ((I.fmat m - 1) *ᵥ (I.fmat x *ᵥ n)) := by
  rw [Formalism.L2.SG.Pf.unitaryCongruence.fmat_mul, Formalism.L2.SG.Pf.unitaryCongruence.fmat_mul]
  simp only [Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.mulVec_sub, Matrix.mulVec_mulVec,
    ← Matrix.mul_assoc, Formalism.L2.SG.Pf.unitaryCongruence.fmat_inv_mul, Matrix.one_mulVec]
  rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Formalism.L2.SG.Pf.unitaryCongruence.fmat_inv_mul, Matrix.sub_mulVec,
    Matrix.one_mulVec]

theorem term_cong {g : ℕ} {x m : I.Gf} (hx : x ∈ I.Kset) (hm : m ∈ I.Kset)
    {f F n N : Formalism.L2.SG.HidaSetting.VA I} (hf : f ∈ I.Lf) (hn : n ∈ I.Lf) (hFx : I.fmat x *ᵥ F = F) {c : ℕ}
    (hcf : (c : I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F) • (f - F) ∈ Formalism.L2.SG.HidaSetting.mL I g)
    (hcn : (c : I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F) • (I.fmat x *ᵥ n) - (c : I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F) • N ∈
      Formalism.L2.SG.HidaSetting.mL I g) :
    Formalism.L2.SG.HidaSetting.ZMod' I g (((c * c : ℕ) : I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F) *
      (Formalism.L2.SG.HidaSetting.hA I f ((I.fmat (x⁻¹ * m * x) - 1) *ᵥ n) -
        Formalism.L2.SG.HidaSetting.hA I F ((I.fmat m - 1) *ᵥ N))) := by
  set C : I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F := (c : I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F) with hC
  have e1 : Formalism.L2.SG.HidaSetting.hA I f ((I.fmat (x⁻¹ * m * x) - 1) *ᵥ n) =
      Formalism.L2.SG.HidaSetting.hA I (I.fmat x *ᵥ f) ((I.fmat m - 1) *ᵥ (I.fmat x *ᵥ n)) := by
    rw [conj_sub, PIW.NormChiNBi.hA_left_inv, inv_inv]
  have hsig : Formalism.L2.SG.HidaSetting.sigA I C = C := by rw [hC, map_natCast]
  have esc : ∀ u v : Formalism.L2.SG.HidaSetting.VA I, Formalism.L2.SG.HidaSetting.hA I (C • u) ((I.fmat m - 1) *ᵥ (C • v)) =
      C * C * Formalism.L2.SG.HidaSetting.hA I u ((I.fmat m - 1) *ᵥ v) := by
    intro u v
    rw [Matrix.mulVec_smul, PIW.NormChiNBi.hA_smul_left, PIW.NormChiNBi.hA_smul_right, hsig]; ring
  have hδf : C • (I.fmat x *ᵥ f) - C • F ∈ Formalism.L2.SG.HidaSetting.mL I g := by
    have e : C • (I.fmat x *ᵥ f) - C • F = I.fmat x *ᵥ (C • (f - F)) := by
      rw [Matrix.mulVec_smul, Matrix.mulVec_sub, hFx, smul_sub]
    rw [e]; exact K_mL' I hx hcf
  have hA'L : C • F ∈ I.Lf := by
    have e : C • F = C • f - C • (f - F) := by rw [smul_sub]; abel
    rw [e]; exact sub_mem (nsmul_Lf' I hf) (mL_le_Lf' I g hcf)
  have hBL : (I.fmat m - 1) *ᵥ (C • (I.fmat x *ᵥ n)) ∈ I.Lf :=
    Formalism.L2.SG.Pf.unitaryCongruence.K_sub_mv I hm (nsmul_Lf' I (Formalism.L2.SG.Pf.unitaryCongruence.K_mv I hx hn))
  have key : ((c * c : ℕ) : I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F) *
      (Formalism.L2.SG.HidaSetting.hA I f ((I.fmat (x⁻¹ * m * x) - 1) *ᵥ n) -
        Formalism.L2.SG.HidaSetting.hA I F ((I.fmat m - 1) *ᵥ N)) =
      Formalism.L2.SG.HidaSetting.hA I (C • (I.fmat x *ᵥ f) - C • F) ((I.fmat m - 1) *ᵥ (C • (I.fmat x *ᵥ n))) +
      Formalism.L2.SG.HidaSetting.hA I (C • F) ((I.fmat m - 1) *ᵥ (C • (I.fmat x *ᵥ n) - C • N)) := by
    rw [PIW.NormChiNBi.hA_sub_left, Matrix.mulVec_sub, PIW.NormChiNBi.hA_sub_right, e1, esc, esc, esc, Nat.cast_mul]
    ring
  rw [key]
  obtain ⟨s, hs, hs'⟩ := PIW.NormChiNBi.hA_mL_left I g hδf hBL
  obtain ⟨t, ht, ht'⟩ := PIW.NormChiNBi.hA_mL_right I g (K_sub_mL' I hm hcn) hA'L
  exact ⟨s + t, add_mem hs ht, by rw [hs', ht', mul_add]⟩

end GlobalTheory.NPartConj

namespace GlobalTheory.NPartConj

theorem term_each (D : D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (u : D.what₂.Word) (m : X.B.I.Gf)
    (hm : m ∈ X.B.I.Kset) (a : Fin D.R.rS) :
    ∃ c : ℕ, Nat.Coprime c X.B.g ∧ ZMod' X.B.I X.B.g ((c : X.B.I.E ⊗[X.B.I.F] Formalism.MainNotions.S.Af X.B.I.F) *
      (hA X.B.I (X.f0 a) ((X.B.I.fmat ((X.xu u)⁻¹ * m * X.xu u) - 1) *ᵥ nxt X.e0 X.z0 a) -
        hA X.B.I (incl X.B.I (X.fR a)) ((X.B.I.fmat m - 1) *ᵥ incl X.B.I (nxt X.eR (X.zR u) a)))) := by
  obtain ⟨c1, hc1, h1⟩ := (X.basisApprox a).2
  have hFx : X.B.I.fmat (X.xu u) *ᵥ incl X.B.I (X.fR a) = incl X.B.I (X.fR a) := (X.xu_fix u a).2
  have hx := X.xu_K u
  obtain ⟨c2, hc2, N0, hN0, h2⟩ : ∃ c2 : ℕ, Nat.Coprime c2 X.B.g ∧ ∃ N0 : VA X.B.I,
      X.B.I.fmat (X.xu u) *ᵥ N0 = incl X.B.I (nxt X.eR (X.zR u) a) ∧
      ((c2 : X.B.I.E ⊗[X.B.I.F] Formalism.MainNotions.S.Af X.B.I.F) • (nxt X.e0 X.z0 a - N0)) ∈ mL X.B.I X.B.g := by
    unfold nxt
    split_ifs with h
    · obtain ⟨c2, hc2, h2⟩ := (X.basisApprox ⟨a.1 + 1, h⟩).1
      exact ⟨c2, hc2, _, (X.xu_fix u _).1, h2⟩
    · obtain ⟨c2, hc2, h2⟩ := X.xu_z u
      refine ⟨c2, hc2, X.B.I.fmat (X.xu u)⁻¹ *ᵥ incl X.B.I (X.zR u), ?_, ?_⟩
      · rw [Matrix.mulVec_mulVec, PIW.NormChiNBi.fmat_mul_inv', Matrix.one_mulVec]
      · have h3 := neg_mem h2
        rwa [← smul_neg, neg_sub] at h3
  have hcop : Nat.Coprime (c1 * c2) X.B.g := Nat.Coprime.mul hc1 hc2
  refine ⟨(c1 * c2) * (c1 * c2), Nat.Coprime.mul hcop hcop, ?_⟩
  have hcf : ((c1 * c2 : ℕ) : X.B.I.E ⊗[X.B.I.F] Formalism.MainNotions.S.Af X.B.I.F) • (X.f0 a - incl X.B.I (X.fR a)) ∈
      mL X.B.I X.B.g := by
    rw [Nat.cast_mul, mul_comm, mul_smul]; exact nsmul_mL' X.B.I h1
  have hcN : ((c1 * c2 : ℕ) : X.B.I.E ⊗[X.B.I.F] Formalism.MainNotions.S.Af X.B.I.F) • (nxt X.e0 X.z0 a - N0) ∈
      mL X.B.I X.B.g := by
    rw [Nat.cast_mul, mul_smul]; exact nsmul_mL' X.B.I h2
  exact term_cong X.B.I hx hm (X.vectorsInLattice.1 a).2 (PIW.NormChiNBi.nxt_mem X a) hFx hcf
    (hcn_of X.B.I hx hN0 hcN)

theorem nsum_cong : ∀ (D : D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (u : D.what₂.Word) (m : X.B.I.Gf), m ∈ X.B.I.Kset → ∃ c : ℕ, Nat.Coprime c X.B.g ∧ ZMod' X.B.I X.B.g ((c : X.B.I.E ⊗[X.B.I.F] Formalism.MainNotions.S.Af X.B.I.F) * ∑ a, (hA X.B.I (X.f0 a) ((X.B.I.fmat ((X.xu u)⁻¹ * m * X.xu u) - 1) *ᵥ nxt X.e0 X.z0 a) - hA X.B.I (incl X.B.I (X.fR a)) ((X.B.I.fmat m - 1) *ᵥ incl X.B.I (nxt X.eR (X.zR u) a)))) := by
  intro D X u m hm
  choose c hc h using term_each D X u m hm
  refine ⟨∏ a, c a, Nat.Coprime.prod_left fun a _ => hc a, ?_⟩
  rw [Finset.mul_sum]
  refine Formalism.L2.SG.Pf.unitaryCongruence.Z_sum X.B.I X.B.g _ _ fun a _ => ?_
  obtain ⟨k, hk⟩ := Finset.dvd_prod_of_mem c (Finset.mem_univ a)
  rw [hk]
  have e : ∀ T : X.B.I.E ⊗[X.B.I.F] Formalism.MainNotions.S.Af X.B.I.F,
      ((c a * k : ℕ) : X.B.I.E ⊗[X.B.I.F] Formalism.MainNotions.S.Af X.B.I.F) * T =
        (k : X.B.I.E ⊗[X.B.I.F] Formalism.MainNotions.S.Af X.B.I.F) * ((c a : X.B.I.E ⊗[X.B.I.F] Formalism.MainNotions.S.Af X.B.I.F) * T) := by
    intro T; push_cast; ring
  rw [e]
  exact Formalism.L2.SG.Pf.unitaryCongruence.Z_smul X.B.I X.B.g (natCast_mem _ k) (h a)

end GlobalTheory.NPartConj
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsCoprimeMultiplierNegativeVectorTermNear
section
open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.DIV GlobalTheory.FlagBasis GlobalTheory.LevNorm
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.ScalW

theorem znear_term : ∀ (D : D7) (X : HidaSetting D) (u : D.what₂.Word), ∃ M : ℕ, Nat.Coprime M X.B.g ∧ ∀ y ∈ X.B.I.Lf, (M : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • (hA X.B.I (X.B.I.fmat (X.xu u)⁻¹ *ᵥ GlobalTheory.ScalW.zV X u) y • (X.B.I.fmat (X.xu u)⁻¹ *ᵥ GlobalTheory.ScalW.zV X u) - hA X.B.I X.z0 y • X.z0) ∈ mL X.B.I X.B.g := by
  intro D X u
  obtain ⟨c, hc, hm⟩ := X.xu_z u
  obtain ⟨-, hz0, -⟩ := X.vectorsInLattice
  set z' := X.B.I.fmat (X.xu u)⁻¹ *ᵥ GlobalTheory.ScalW.zV X u with hz'
  have hm' : (c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • (z' - X.z0) ∈ mL X.B.I X.B.g := hm
  refine ⟨c * c, Nat.Coprime.mul hc hc, ?_⟩
  intro y hy
  have hcz : (c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • z' ∈ X.B.I.Lf := by
    have e : (c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • z' =
        (c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • X.z0 + (c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • (z' - X.z0) := by
      rw [smul_sub]; abel
    rw [e]
    exact add_mem (GlobalTheory.St.G.FrameClose.nat_smul_mem c hz0) (GlobalTheory.St.G.FrameClose.mL_le _ hm')
  obtain ⟨t1, ht1, e1⟩ := GlobalTheory.St.G.FrameClose.zmod_of_mL hm' hy
  rw [GlobalTheory.St.G.FrameClose.hA_nat_left, GlobalTheory.St.G.FrameClose.hA_sub_left] at e1
  have hs : hA X.B.I X.z0 y ∈ IntAf X.B.I.F X.B.I.E := GlobalTheory.St.G.FrameClose.hA_int hz0 hy
  have hs' : (c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) * hA X.B.I X.z0 y ∈ IntAf X.B.I.F X.B.I.E :=
    mul_mem (natCast_mem _ c) hs
  have e : ((c * c : ℕ) : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • (hA X.B.I z' y • z' - hA X.B.I X.z0 y • X.z0) =
      t1 • ((X.B.g : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • ((c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • z')) +
      ((c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) * hA X.B.I X.z0 y) •
        ((c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • (z' - X.z0)) := by
    simp only [smul_smul, smul_sub, Nat.cast_mul]
    have e2 : (c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) * hA X.B.I z' y =
        (X.B.g : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) * t1 + (c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) * hA X.B.I X.z0 y := by
      linear_combination e1
    have e3 : (c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) * (c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) * hA X.B.I z' y =
        t1 * ((X.B.g : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) * (c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F)) +
        (c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) * hA X.B.I X.z0 y * (c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) := by
      linear_combination (c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) * e2
    rw [e3, add_smul, show (c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) * (c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) * hA X.B.I X.z0 y = (c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) * hA X.B.I X.z0 y * (c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) by ring]
    abel
  rw [e]
  refine add_mem ?_ ?_
  · exact (mL X.B.I X.B.g).smul_mem (⟨_, ht1⟩ : IntAf X.B.I.F X.B.I.E) (Submodule.subset_span ⟨_, hcz, rfl⟩)
  · exact (mL X.B.I X.B.g).smul_mem (⟨_, hs'⟩ : IntAf X.B.I.F X.B.I.E) hm'

end GlobalTheory.ScalW
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsCoprimeMultiplierOneSubNormCongrZero
section
open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.DIV GlobalTheory.FlagBasis GlobalTheory.LevNorm
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section

namespace GlobalTheory.TorusCong

open Formalism.L2.SG.Pf.unitaryCongruence GlobalTheory.St.G.FrameClose

theorem one_sub_T_zmod : ∀ (D : D7) (X : HidaSetting D) (u : D.what₂.Word), ∃ M : ℕ, Nat.Coprime M X.B.g ∧ ZMod' X.B.I X.B.g ((M : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) * (1 - (((D.mem u).A.T : ℕ) : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F))) := by
  intro D X u
  obtain ⟨c', hc', hm⟩ := X.xu_z u
  obtain ⟨-, hz0, -⟩ := X.vectorsInLattice
  set z' : VA X.B.I := X.B.I.fmat (X.xu u)⁻¹ *ᵥ incl X.B.I (X.zR u) with hz'
  have hm' : (c' : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • (z' - X.z0) ∈ mL X.B.I X.B.g := hm
  have hzz : hA X.B.I z' z' = -(((D.mem u).A.T : ℕ) : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) := by
    rw [hz', Formalism.L2.SG.PoincareInHH.Cut.hA_fmat, HidaSetting.zR, Formalism.L2.SG.PoincareInHH.Cut.hA_crd, X.zu_norm,
      map_neg, map_natCast, map_neg, map_natCast]
  set m : VA X.B.I := (c' : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • (z' - X.z0) with hmdef
  set w0 : VA X.B.I := (c' : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • X.z0 with hw0def
  have hw0 : w0 ∈ X.B.I.Lf := nat_smul_mem c' hz0
  have hw : m + w0 ∈ X.B.I.Lf := add_mem (mL_le X.B.g hm') hw0
  have h1 : ZMod' X.B.I X.B.g (hA X.B.I m (m + w0)) := zmod_of_mL hm' hw
  have h2 : ZMod' X.B.I X.B.g (hA X.B.I w0 m) := by
    rw [hA_symm]; exact Z_sig _ _ (zmod_of_mL hm' hw0)
  have hsplit : hA X.B.I (m + w0) (m + w0) - hA X.B.I w0 w0 = hA X.B.I m (m + w0) + hA X.B.I w0 m := by
    rw [hA_add_left, hA_add_right, hA_add_right]; ring
  have hmw : m + w0 = (c' : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • z' := by
    rw [hmdef, hw0def, ← smul_add, sub_add_cancel]
  have hsq : ∀ x : VA X.B.I, hA X.B.I ((c' : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • x) ((c' : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • x)
      = (c' : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) ^ 2 * hA X.B.I x x := by
    intro x; rw [hA_nat_left, hA_smul_right]; ring
  have hA1 : ZMod' X.B.I X.B.g ((c' : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) ^ 2 * (hA X.B.I z' z' - hA X.B.I X.z0 X.z0)) := by
    have e : (c' : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) ^ 2 * (hA X.B.I z' z' - hA X.B.I X.z0 X.z0) =
        hA X.B.I m (m + w0) + hA X.B.I w0 m := by
      rw [← hsplit, hmw, hw0def, hsq, hsq]; ring
    rw [e]; exact Z_add _ _ h1 h2
  have hA2 : ZMod' X.B.I X.B.g ((c' : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) ^ 2 * (hA X.B.I X.z0 X.z0 + 1)) := by
    have := Z_smul X.B.I X.B.g (natCast_mem (IntAf X.B.I.F X.B.I.E) (c' ^ 2)) X.formsAtZero.1
    simpa [Nat.cast_pow] using this
  refine ⟨c' ^ 2, Nat.Coprime.pow_left 2 hc', ?_⟩
  have e : ((c' ^ 2 : ℕ) : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) * (1 - (((D.mem u).A.T : ℕ) : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F)) =
      (c' : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) ^ 2 * (hA X.B.I z' z' - hA X.B.I X.z0 X.z0) +
      (c' : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) ^ 2 * (hA X.B.I X.z0 X.z0 + 1) := by
    rw [hzz, Nat.cast_pow]; ring
  rw [e]; exact Z_add _ _ hA1 hA2

end GlobalTheory.TorusCong
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsFiniteRepsHalfStandardHomModNsmul
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.SeeSaw GlobalTheory.AdForm GlobalTheory.LocMod

noncomputable section

set_option synthInstance.maxHeartbeats 400000

namespace GlobalTheory.HalfStdFin

theorem exists_reps_half_stdHom : ∀ (D : D7) (S T : HSp D) (Q : Finset (Formalism.L2.DIV.Pl D.host.E)) (E₂ : AE D), IsIdemSum E₂ Q → ∀ k : ℕ, 0 < k → ∃ R : Finset (WO S T), ∀ u ∈ stdHom S T, IsHalf E₂ u → ∃ r ∈ R, ∃ v ∈ stdHom S T, IsHalf E₂ v ∧ u = r + k • v := by
  classical
  intro D S T Q E₂ _ k hk
  obtain ⟨R, hR, h⟩ := GlobalTheory.LatFinMod.latO_finite_mod D S T (Formalism.L2.Col.stdLat D.host.E S.rank)
    (Formalism.L2.Col.stdLat D.host.E T.rank) (Formalism.L2.Col.stdLat_lattice (E := D.host.E) (n := S.rank)).fg
    (Formalism.L2.Col.stdLat_lattice (E := D.host.E) (n := T.rank)).fg (fun _ => True) k hk
  rw [coe_colStdLat, coe_colStdLat] at h
  let G : WO S T → Prop := fun r => ∃ u ∈ stdHom S T, IsHalf E₂ u ∧ ∃ w ∈ stdHom S T, u = r + k • w
  let pick : WO S T → WO S T := fun r => if hG : G r then hG.choose else 0
  refine ⟨hR.toFinset.image pick, fun u hu hh => ?_⟩
  obtain ⟨r, hr, w, hw, huw⟩ := h u hu
  have hG : G r := ⟨u, hu, hh, w, hw, huw⟩
  obtain ⟨_, hh₀, w₀, hw₀, hu₀w⟩ := hG.choose_spec
  have hp : pick r = hG.choose := dif_pos hG
  have hdiff : u = hG.choose + k • (w - w₀) := by
    rw [hu₀w, smul_sub, huw]; abel
  exact ⟨pick r, Finset.mem_image_of_mem _ (hR.mem_toFinset.2 hr), w - w₀, sub_mem hw hw₀,
    GlobalTheory.HalfLatFin.isHalf_of_nsmul E₂ hk hh hh₀ hdiff, by rw [hp]; exact hdiff⟩

end GlobalTheory.HalfStdFin

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsHaarAdelicUnitaryProductRealFiniteStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_haar_adelicUnitary_product_real_finite : ∀ (D : D7) (V : HSp D) (μf : Measure (GfC V)), μf.IsHaarMeasure → ∃ (μR : Measure (GA D V)) (μi : Measure (GinfC V)), μR.IsHaarMeasure ∧ ∀ (S : Set (GinfC V)) (E : Set (GfC V)), μR {h | ∃ a ∈ S, ∃ k ∈ E, h = (a : GA D V) * k} = μi S * μf E := by
  first | exact @GlobalTheory.AdelicHaarProd.haar_prod | exact GlobalTheory.AdelicHaarProd.haar_prod | (intros; apply GlobalTheory.AdelicHaarProd.haar_prod <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsHaarFinitePointsFourierJacobiBesselStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_haar_finitePoints_fourierJacobi_bessel : ∀ (D : D7) (V : HSp D), (∃ μ : Measure (GfC V), μ.IsHaarMeasure) ∧ ∀ (V₀ : HSp D) (ρ : ℕ) (d : HypDec V V₀ ρ), (∃ μ : Measure ((jacGrp d).subgroupOf (GfC V)), μ.IsHaarMeasure) ∧ ∀ (A L : HSp D) (o : OrthDec V₀ A L), ∃ μ : Measure ((besGrp d o).subgroupOf (GfC V)), μ.IsHaarMeasure := by
  first | exact @GlobalTheory.HaarExist.haar_exists | exact GlobalTheory.HaarExist.haar_exists | (intros; apply GlobalTheory.HaarExist.haar_exists <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsHeightDoublingEmbeddingLePowMulHeights
section
open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP

noncomputable section

namespace GlobalTheory.Cont.HeightIo

theorem height_io_le_mul {D : D7} (V : HSp D) (g₁ g₂ : GA D V) :
    GlobalTheory.Grow.height (dblSp V) (io V (g₁, g₂)) ≤ GlobalTheory.Grow.height V g₁ * GlobalTheory.Grow.height V g₂ := by
  have h := GlobalTheory.BlockHeight.heightGL_blk_le D.host.F finSumFinEquiv
    (Formalism.L2.Theta.matHom (dblSp V) (io V (g₁, g₂))) (Formalism.L2.Theta.matHom V g₁) (Formalism.L2.Theta.matHom V g₂) rfl rfl
  show ((GlobalTheory.AdelicU.heightGL D.host.F _ : ℝ≥0) : ℝ) ≤
    ((GlobalTheory.AdelicU.heightGL D.host.F _ : ℝ≥0) : ℝ) * ((GlobalTheory.AdelicU.heightGL D.host.F _ : ℝ≥0) : ℝ)
  exact_mod_cast h

theorem height_io_bound : ∀ (D : D7) (V : HSp D), ∃ (C : ℝ) (c : ℕ), ∀ g₁ g₂ : GA D V,
    GlobalTheory.Grow.height (dblSp V) (io V (g₁, g₂)) ≤ C * (GlobalTheory.Grow.height V g₁ * GlobalTheory.Grow.height V g₂) ^ c := by
  intro D V
  refine ⟨1, 1, fun g₁ g₂ => ?_⟩
  rw [one_mul, pow_one]
  exact height_io_le_mul V g₁ g₂

end GlobalTheory.Cont.HeightIo

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsIsIdemSumConjOfIsIdemSum
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.SeeSaw GlobalTheory.AdForm GlobalTheory.LocMod

namespace GlobalTheory.IdemSumConj

theorem exists_isIdemSum_cA :
    ∀ (D : D7) (Q : Finset (Formalism.L2.DIV.Pl D.host.E)) (E₂ : AE D), IsIdemSum E₂ Q →
      ∃ Q' : Finset (Formalism.L2.DIV.Pl D.host.E), IsIdemSum (cA D E₂) Q' := by
  intro D P e h
  classical
  refine ⟨P.image Formalism.L2.DIV.conjPl, ?_⟩
  obtain ⟨⟨es, hes, he⟩, hc⟩ := h
  refine ⟨⟨fun Q => cA D (es (Formalism.L2.DIV.conjPl Q)), ?_, ?_⟩, ?_⟩
  · intro Q hQ
    obtain ⟨PP, hPP, rfl⟩ := Finset.mem_image.1 hQ
    show Formalism.L2.NTheta.IsIdemAt (cA D (es (Formalism.L2.DIV.conjPl (Formalism.L2.DIV.conjPl PP)))) (Formalism.L2.DIV.conjPl PP)
    rw [Formalism.L2.DIV.conjPl_conjPl]
    exact GlobalTheory.MovedIdem.isIdemAt_conj (hes PP hPP) fun x => Iff.rfl
  · rw [Finset.sum_image (fun a _ b _ (hab : Formalism.L2.DIV.conjPl a = Formalism.L2.DIV.conjPl b) => by
      rw [← Formalism.L2.DIV.conjPl_conjPl a, hab, Formalism.L2.DIV.conjPl_conjPl b])]
    simp only [Formalism.L2.DIV.conjPl_conjPl]
    rw [he, map_sum]
  · rw [GlobalTheory.MovedIdem.cA_cA, mul_comm]; exact hc

end GlobalTheory.IdemSumConj
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsLevelElementsStepVectorStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_level_elements_step_vector : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : RealPack ex), PkHyp W → ∀ t j, j + 1 < D.R.m → ∀ [Fintype (lvP W).H], ∃ κ : (lvP W).H → GA D (Yc D j), (∀ p, κ p ∈ levS (Yc D j) ((pk W).βY j) ((pk W).datYt t j (lvP W))) ∧ ∀ v, IsStepVecOf (pk W).ψ (pk W).θ (Yc D j) (Yc D (j + 1)) (cart ((pk W).MY j)) (cart ((pk W).MY (j + 1))) ((pk W).ΛY j) ((pk W).ΛY (j + 1)) ((pk W).βY j) ((pk W).βY (j + 1)) ((pk W).datYt t j (lvP W)) ((pk W).chi (j + 1)) ((pk W).Q t) ((pk W).xiR t) ((pk W).vac j) v → ∀ Q, pureTensorO (pk W).ψ (pk W).θ (Yc D j) (Yc D (j + 1)) (cart ((pk W).MY j)) (cart ((pk W).MY (j + 1))) (onb ((pk W).MY j)) (onb ((pk W).MY (j + 1))) v Q = ∑ p, (levChi (Yc D j) ((pk W).βY j) ((pk W).datYt t j (lvP W)) (κ p))⁻¹ • ((pk W).ωY t j (κ p, 1)) ((pk W).ptY t j Q) := by
  first | exact @GlobalTheory.FockVecSum.fockVec_eq_sum | exact GlobalTheory.FockVecSum.fockVec_eq_sum | (intros; apply GlobalTheory.FockVecSum.fockVec_eq_sum <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsRealThetaIntertwinerExchangedPair
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.S Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open GlobalTheory.Chain GlobalTheory.ChainFr GlobalTheory.PairLift GlobalTheory.Chain.RealIt
open scoped TensorProduct InnerProductSpace ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Chain.RealIt

theorem itPairUp : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → ∀ (D : D7) (k : Fin D.R.m) (V W : HSp D)
    (S S' : D.what₂.Tau → SPar) (M : DSModel V S) (M' : DSModel W S') (θ : InfFam D) (ψ : AddChar (AF D.host.F) ℂ),
    S = parB (Ptw D) k → S' = parB (Ptw D) (k + 1) → IsInfFam θ → ChainPar D k →
    ∃ It : PolF D V.rank W.rank →ₗ[ℂ] SmT M →ₗ[ℂ] SmT M', ∀ (ω : (GA D W × GA D V →* Module.End ℂ (WO W V → ℂ)))
      (f : WO W V → ℂ), IsWeilExp ψ W V (expT D k) (expS D k) ω → IsVacVec ψ θ M' M f →
        IsItW θ M' M ω (ptOf ψ θ M' M f) It := by
  intro hDS hHC D k V W S S' M M' θ ψ hS hS' hθ hP
  subst hS hS'
  obtain ⟨X, hX, h1, h2, -⟩ := GlobalTheory.T.exists_real_discreteSeries_data_theta_properties hDS hHC
  have hB := GlobalTheory.T.thetaModels_are_coverDiscreteSeries_of_harishChandra hDS hHC D
  have key : ∀ τ, (0 < V.rank ∧ 0 < W.rank) ∧ ∃ A, LocIt M M' τ (expS D k τ) (expT D k τ) A := fun τ => by
    obtain ⟨al, be, ga, de, hd, -, e1, e2⟩ := hP τ
    exact exists_locIt hX h1 h2 hB M M' τ hd (congrArg dualPar e1) (congrArg dualPar e2)
  choose hr A hA using key
  have hA' : ∀ τ, ∃ A', LocIt M' M τ (expT D k τ) (expS D k τ) A' := fun τ =>
    GlobalTheory.T.localFockIntertwiner_adjoint_exchangedPair D V W _ _ M M' τ _ _ (A τ) (hA τ)
  choose A' hA' using hA'
  obtain ⟨It, I, hI⟩ := GlobalTheory.T.exists_globalFockIntertwiner_tensor_realPlaces D W V _ _ M' M (expT D k) (expS D k) A' GlobalTheory.ContrObj.contraction.2
    (GlobalTheory.T.gluing_law_holds D _ _) hA'
  refine ⟨It, fun ω f ⟨χS, χT, hω, he⟩ hf => ?_⟩
  have hv := fun τ => GlobalTheory.T.thetaVacuumCharacters_realPlaces D W V _ _ M' M θ ψ χS χT ω f τ _ _ hθ hω (he τ).1 (he τ).2 hf
  exact isItW_of_globIt hθ hI (fun τ => ⟨(hr τ).2, (hr τ).1⟩)
    (GlobalTheory.T.fockVectors_overVacuum_isometry D W V _ _ M' M ψ θ hω.std hθ f hf).2.2.2.2 (fun τ => (hv τ).2.1) fun τ => (hv τ).2.2

end GlobalTheory.Chain.RealIt

end
end

