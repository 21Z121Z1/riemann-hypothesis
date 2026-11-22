import Mathlib
import Development.WeilBound.CoreStatements.AutomorphicKernels.UnitarySchrodingerModel.WhitKAOfGen
import Development.WeilBound.CoreStatements.AutomorphicKernels.UnitarySchrodingerModel.CoefDataExists
import Development.WeilBound.CoreStatements.PublishedTheorems.SiegelWeilSchrodinger.SiegelWeilUnitarySchrodingerLit
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0370
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0375
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.Bundle0003
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0203
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0755
import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.ThetaIdempotents.HeckeEta
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FourierZeroHolds
import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.HermitianCellMeasures.Bundle0001
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0756
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0736
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0741
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0752
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.ZelevinskyInterleaving.LInjective
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0003
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0009
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0007
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0757
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0747
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PartialConstantTermBound
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0758

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HolValueAtFinsetSum
section
noncomputable section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.IwaAd

open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS

theorem holValueAt_finset_sum {ι : Type*} (T : Finset ι) {f : ι → ℂ → ℂ} {c : ι → ℂ} {s₀ : ℂ}
    (a : ∀ i ∈ T, HolValueAt (f i) s₀ (c i)) :
    HolValueAt (fun z => ∑ i ∈ T, f i z) s₀ (∑ i ∈ T, c i) := by
  classical
  induction T using Finset.induction_on with
  | empty => simpa using holValueAt_const 0 s₀
  | insert i T hi ih =>
    have h := (a i (Finset.mem_insert_self i T)).add
      (ih fun j hj => a j (Finset.mem_insert_of_mem hj))
    simpa only [Finset.sum_insert hi] using h

theorem whitKAOfGen : PositivityTheory.PfSWUS.WhitKAOfGen := by
  intro hGen hDict D n V ψ χ θ μ ω H l s ν Φ hS hR lam 𝓖 nb hC w hw β hβ a k hk
  obtain ⟨N, φs, vals, ⟨t, ht⟩, hv, hm⟩ := hDict D n V ψ χ θ μ ω H l s ν Φ hS hR lam 𝓖 nb hC w hw β hβ a k hk
  obtain ⟨⟨𝓕, h𝓕⟩, -⟩ := GlobalTheory.Mem.Vol.fundamentalDomain_adelicUnitary D.host.F D.host.E D.sp.cm.sig V.rank V.gram ν hS.hν
  have key : ∀ j, HolValueAt (whitT ψ V μ lam nb w H (φs j) (adj a.1 * β.1.map (incA D) * a.1) k) (s0 V n) (vals j) := by
    intro j
    obtain ⟨d, bs, θG, lG, εG, frG, gG, PG, lamG, L₁, L₂, ΦG, Φf, Φv, μG, νG, ψG, hDat, C, ⟨t', ht'⟩, hval⟩ := hm j
    have h := hGen _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hDat ⟨t', fun z hz => (ht' z hz).1⟩ ν 𝓕 hS.hν h𝓕
    have e : ((V.rank : ℂ) - n) / 2 = s0 V n := by
      simp only [s0]
      ring
    rw [hval ν 𝓕 hS.hν h𝓕]
    have h2 := (holValueAt_const C _).mul h
    rw [e] at h2
    exact h2.congr ⟨t', fun z hz => ((ht' z hz).2).symm⟩
  rw [hv]
  exact (holValueAt_finset_sum Finset.univ fun j _ => key j).congr ⟨t, fun z hz => (ht z hz).symm⟩

end GlobalTheory.CompanionTheory.IwaAd

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IntegrableOfSummableFundamentalDomainStatement
section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integrable_of_summable_fundamental_domain : ∀ (D : D7) (ρ : ℕ) (lz : Measure (hermA D ρ)) (𝓖 : Set (hermA D ρ)), IsCovolOneH lz 𝓖 →
  ∀ f : hermA D ρ → ℝ, Continuous f → (∀ z, 0 ≤ f z) → Summable (fun ζ : ratHerm D ρ => f ζ.1) →
  ∀ K : Set (hermA D ρ), (∀ x, ∃ γ ∈ ratHerm D ρ, γ + x ∈ K) → ∀ κ : ℝ, 0 ≤ κ →
    (∀ ζ ∈ ratHerm D ρ, ∀ z ∈ K, f (ζ + z) ≤ κ * f ζ) → Integrable f lz := by
  first | exact @GlobalTheory.CompanionTheory.HermFD.integrable_of_periodisation_bound | exact GlobalTheory.CompanionTheory.HermFD.integrable_of_periodisation_bound | (intros; apply GlobalTheory.CompanionTheory.HermFD.integrable_of_periodisation_bound <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.InvarianceOfConstantFourierCoefficientStatement
section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.invariance_of_constant_fourier_coefficient : ∀ (D : D7) (p : ℕ) (ψ : AddChar (AF D.host.F) ℂ) (nb : hermA D p → G D p) (lam : Measure (hermA D p)) (𝓖 : Set (hermA D p)), CoefData (D := D) (n := p) nb lam 𝓖 → ∀ (F : G D p → ℂ), Continuous F → LeftInv (GF D p) F → ∀ β : HermE D p, β.1 = 0 → (∀ g, fc ψ lam 𝓖 nb F β g = F g) → ∀ (b : hermA D p) (g : G D p), F (nb b * g) = F g := by
  first | exact @GlobalTheory.CompanionTheory.ConstN.nb_inv_of_const | exact GlobalTheory.CompanionTheory.ConstN.nb_inv_of_const | (intros; apply GlobalTheory.CompanionTheory.ConstN.nb_inv_of_const <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsClosedHermSMx
section
noncomputable section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw PositivityTheory.Rg.Rsw.L
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.RswTop

theorem topC : PositivityTheory.Rg.Rsw.Cell.TopC := by
  intro D p e
  obtain ⟨h1, h2, h3, h4, -⟩ := GlobalTheory.CompanionTheory.MuC.hermS_facts D p e
  exact ⟨inferInstance, inferInstance, inferInstance, h2, h1, h3, h4⟩

end GlobalTheory.CompanionTheory.RswTop
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsOpenStandardLatticeStabilizerStatement
section
open Matrix MeasureTheory GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.LeibOrd GlobalTheory.SplitWeil GlobalTheory.JHMult GlobalTheory.CompanionTheory.BZShell GlobalTheory.CompanionTheory.MirPair GlobalTheory.CompanionTheory.BZCore
open scoped Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isOpen_standard_lattice_stabilizer : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {d : ℕ}, IsOpen {g : GL (Fin d) k | (lat0 : COSub k d).act g = lat0} := by
  first | exact @GlobalTheory.CompanionTheory.BZCore.isOpen_stabilizer_standard_lattice | exact GlobalTheory.CompanionTheory.BZCore.isOpen_stabilizer_standard_lattice | (intros; apply GlobalTheory.CompanionTheory.BZCore.isOpen_stabilizer_standard_lattice <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LanglandsExhaustionGl
section
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.M

namespace GlobalTheory.CompanionTheory.LanglandsMultiseg

theorem langlandsMultisegments_of_clauses (hA : GlobalTheory.Published.IrreducibleAdmissibleGL)
    (hSoc : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], LSocleGL k)
    (hSeg : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], LSegJacquet k)
    (hFree : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], LOrderFree k)
    (hE : GlobalTheory.Published.LanglandsExhaustionGL) : GlobalTheory.Published.LanglandsMultisegments := by
  intro k _ _ _ _ _
  exact ⟨GlobalTheory.T.langlands_injective_of_socle hA (hSoc k) (hSeg k),
    fun 𝔪 𝔫 x y hd h₀ h₁ hy =>
      GlobalTheory.T.langlands_sum_subquotient_product hA (hSoc k) (hSeg k)
        (hFree k) (hE k) 𝔪 𝔫 x y hd h₀ h₁ hy⟩

end GlobalTheory.CompanionTheory.LanglandsMultiseg
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LatticeVolumeScalingLawsStatement
section
open Matrix MeasureTheory GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.LeibOrd GlobalTheory.SplitWeil GlobalTheory.JHMult GlobalTheory.CompanionTheory.BZShell GlobalTheory.CompanionTheory.MirPair GlobalTheory.CompanionTheory.BZCore
open scoped Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lattice_volume_scaling_laws : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (d : ℕ), ∃ vol : COSub k d → ℝ, (∀ L, 0 < vol L) ∧ (∀ (L' L : COSub k d) (S : Finset (Fin d → k)), L'.sub ≤ L.sub → IsReps L' L S → vol L = (S.card : ℝ) * vol L') ∧ ∀ (g : GL (Fin d) k) (L : COSub k d), ((vol (L.act g) : ℝ) : ℂ) ^ 2 * ((dpow d (-2) g : ℂˣ) : ℂ) = ((vol L : ℝ) : ℂ) ^ 2 := by
  first | exact @GlobalTheory.CompanionTheory.BZCore.exists_vol_cosub | exact GlobalTheory.CompanionTheory.BZCore.exists_vol_cosub | (intros; apply GlobalTheory.CompanionTheory.BZCore.exists_vol_cosub <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalOrbitGLNearOneStatement
section
open Matrix MeasureTheory GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.LeibOrd GlobalTheory.SplitWeil GlobalTheory.JHMult GlobalTheory.CompanionTheory.BZShell GlobalTheory.CompanionTheory.MirPair GlobalTheory.CompanionTheory.BZCore
open scoped Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_orbit_GL_near_one : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {d : ℕ} (z : GL (Fin d) k) (ϖ : k) (hz : (z : Matrix (Fin d) (Fin d) k) = ϖ • (1 : Matrix (Fin d) (Fin d) k)) (hϖ : ValuativeRel.valuation k ϖ < 1) (hϖ0 : ϖ ≠ 0) (U : Set (GL (Fin d) k)), U ∈ 𝓝 (1 : GL (Fin d) k) → ∀ x : Fin d → k, x ≠ 0 → ∃ s : ℕ, ∀ y : Fin d → k, y - x ∈ (latZ z (s : ℤ)).sub → ∃ g ∈ U, (g : Matrix (Fin d) (Fin d) k).mulVec x = y := by
  first | exact @GlobalTheory.CompanionTheory.BZCore.exists_mem_nhds_one_mulVec_eq | exact GlobalTheory.CompanionTheory.BZCore.exists_mem_nhds_one_mulVec_eq | (intros; apply GlobalTheory.CompanionTheory.BZCore.exists_mem_nhds_one_mulVec_eq <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MaximumPrincipleLatticeFunctionsStatement
section
open Matrix MeasureTheory GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.LeibOrd GlobalTheory.SplitWeil GlobalTheory.JHMult GlobalTheory.CompanionTheory.BZShell GlobalTheory.CompanionTheory.MirPair GlobalTheory.CompanionTheory.BZCore
open scoped Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.maximum_principle_lattice_functions : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {d : ℕ} (hd : 0 < d) (z : GL (Fin d) k) (ϖ : k) (hz : (z : Matrix (Fin d) (Fin d) k) = ϖ • (1 : Matrix (Fin d) (Fin d) k)) (hϖ : ValuativeRel.valuation k ϖ < 1) (hϖ0 : ϖ ≠ 0) (F : COSub k d → (Fin d → k) → ℂ) (c : ℂ), Refines F → (∀ (L : COSub k d) (x l : Fin d → k), l ∈ L.sub → F L (x + l) = F L x) → (∀ (L : COSub k d) (x : Fin d → k), F (L.act z) ((z : Matrix (Fin d) (Fin d) k).mulVec x) = F L x) → (∀ x : Fin d → k, x ≠ 0 → ∃ s : ℕ, ∀ y : Fin d → k, y - x ∈ (latZ z (s : ℤ)).sub → ∀ r : ℕ, s ≤ r → F (latZ z (r : ℤ)) y = c) → ∀ (r : ℕ) (x : Fin d → k), F (latZ z (r : ℤ)) x = c := by
  first | exact @GlobalTheory.CompanionTheory.BZCore.MaxPrin.eq_const | exact GlobalTheory.CompanionTheory.BZCore.MaxPrin.eq_const | (intros; apply GlobalTheory.CompanionTheory.BZCore.MaxPrin.eq_const <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NpowHalfAddHalf
section
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw PositivityTheory.Rg.Rsw.L PositivityTheory.Rg.Rsw.Cell

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.SetCell

variable {D : D7} {p : ℕ}

theorem mem_K_of_mem_KOff {S : Finset (Pl D)} {u : G D p} (hu : u ∈ KOff D p S) : u ∈ K D p := by
  obtain ⟨hf, h1, h2⟩ := mem_levelOff.1 hu
  refine mem_levelAll.2 ⟨fun v => ?_, fun w => ?_⟩
  · by_cases hv : v ∈ S
    · rw [h1 v hv]; exact one_mem _
    · exact h2 v hv
  · rw [mem_finPts_iff_forall.1 hf w]; exact one_mem _

theorem height_mul_K {H : G D p → ℝ≥0} (hH : IsHeight H) {k : G D p} (hk : k ∈ K D p) (g : G D p) :
    H (g * k) = H g := by
  obtain ⟨q, hq, k', hk', rfl⟩ := GlobalTheory.StdUnn.Iwasawa.exists_mul D p g
  rw [mul_assoc, GlobalTheory.CompanionTheory.HtEx.height_eq hH ⟨q, hq⟩ (mul_mem hk' hk), GlobalTheory.CompanionTheory.HtEx.height_eq hH ⟨q, hq⟩ hk']

theorem w_mem_GF {w : G D p} (hw : IsW w) : w ∈ GF D p := by
  have hY : mat w⁻¹ = blk4 0 (-1) 1 0 := by
    have e2 : mat w⁻¹ * mat w = 1 :=
      (show mat (w⁻¹ * w) = mat w⁻¹ * mat w from rfl).symm.trans (by rw [inv_mul_cancel]; rfl)
    have e3 : mat w * blk4 0 (-1) 1 0 = 1 := by
      rw [show mat w = _ from hw, GlobalTheory.StdUnn.Model.submatrix_fromBlocks_mul]
      simp [GlobalTheory.StdUnn.Model.block_matrix_one]
    calc mat w⁻¹ = mat w⁻¹ * (mat w * blk4 0 (-1) 1 0) := by rw [e3, mul_one]
      _ = blk4 0 (-1) 1 0 := by rw [← mul_assoc, e2, one_mul]
  refine GlobalTheory.CompanionTheory.PcB.mem_GF w (blk4 0 1 (-1) 0) (blk4 0 (-1) 1 0) ?_ ?_
  · rw [show mat w = _ from hw, GlobalTheory.CompanionTheory.PcB.rational_map_block_matrix, GlobalTheory.CompanionTheory.PcB.rat_zero', GlobalTheory.CompanionTheory.PcB.rat_one', GlobalTheory.CompanionTheory.PcB.rat_neg',
      GlobalTheory.CompanionTheory.PcB.rat_one']
  · rw [hY, GlobalTheory.CompanionTheory.PcB.rational_map_block_matrix, GlobalTheory.CompanionTheory.PcB.rat_zero', GlobalTheory.CompanionTheory.PcB.rat_one', GlobalTheory.CompanionTheory.PcB.rat_neg',
      GlobalTheory.CompanionTheory.PcB.rat_one']

theorem npow_half_add_half (r : ℝ≥0) : npow r ((p : ℂ) / 2 + (p : ℂ) / 2) = (((r : ℝ) ^ p : ℝ) : ℂ) := by
  have e : (p : ℂ) / 2 + (p : ℂ) / 2 = (p : ℂ) := by ring
  rw [e, npow, Complex.cpow_natCast]
  push_cast
  rfl

def hp (H : G D p → ℝ≥0) (g : G D p) : ℝ := (H g : ℝ) ^ p

theorem hp_law {H : G D p → ℝ≥0} (hH : IsHt H) {q : G D p} (hq : q ∈ P D p) {a : GL (Fin p) (AE D)}
    (ha : blkA (mat q) = a.1) (g : G D p) :
    hp H (q * g) = (absA D (Matrix.GeneralLinearGroup.det a) : ℝ) ^ p * hp H g := by
  simp only [hp]
  rw [hH.2.2 q hq a ha g, NNReal.coe_mul, mul_pow]

theorem hp_pos {H : G D p → ℝ≥0} (hH : IsHt H) (g : G D p) : 0 < hp H g :=
  pow_pos (by exact_mod_cast hH.2.1 g) _

theorem exists_block {q : G D p} (hq : q ∈ P D p) : ∃ a : GL (Fin p) (AE D), blkA (mat q) = a.1 :=
  ⟨GlobalTheory.StdUnn.HeightExists.leviBlock (D := D) (n := p) ⟨q, hq⟩, rfl⟩

theorem isRho_iff_sec {H : G D p → ℝ≥0} (hH : IsHt H) (f : G D p → ℂ) : IsRho f ↔ Sec (P D p) (hp H) f := by
  constructor
  · rintro ⟨c, l⟩
    refine ⟨c, fun q hq g => ?_⟩
    obtain ⟨a, ha⟩ := exists_block hq
    rw [l q hq a ha g, hp_law hH hq ha g, npow_half_add_half]
    simp only [MonoidHom.one_apply, Circle.coe_one, one_mul]
    push_cast
    ring
  · rintro ⟨c, l⟩
    refine ⟨c, fun q hq a ha g => ?_⟩
    have h1 := l q hq g
    rw [hp_law hH hq ha g] at h1
    have h0 : ((hp H g : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (hp_pos hH g).ne'
    rw [npow_half_add_half]
    simp only [MonoidHom.one_apply, Circle.coe_one, one_mul]
    apply mul_right_cancel₀ h0
    rw [h1]
    push_cast
    ring

theorem setC : HtExist → PositivityTheory.Rg.Rsw.Cell.SetC := by
  intro hEx D p mu hmu
  obtain ⟨H, hH⟩ := GlobalTheory.StdUnn.exists_height D p
  have hI : IsHt H := GlobalTheory.CompanionTheory.HtEx.isHt_of_isHeight hH
  have hS := isRho_iff_sec hI
  refine ⟨hp H, ?_, hS, ?_, ?_⟩
  · refine ⟨GlobalTheory.StdUnn.HeightExists.isClosed_P, (hEx D p).2, ?_, hp_pos hI, ?_, ?_, ?_, ?_⟩
    · exact (NNReal.continuous_coe.comp hI.1).pow p
    · intro q hq g g'
      obtain ⟨a, ha⟩ := exists_block hq
      rw [hp_law hI hq ha g, hp_law hI hq ha g']
      ring
    · exact fun f f' hf hf' => hmu.add f f' ((hS f).2 hf) ((hS f').2 hf')
    · exact fun c f hf => hmu.smul c f ((hS f).2 hf)
    · exact fun f hf h0 => hmu.pos f ((hS f).2 hf) h0
  · intro S u hu g
    simp only [hp]
    rw [height_mul_K hH (mem_K_of_mem_KOff hu) g]
  · intro nb hnb w hw y
    have hN : ∀ f, IsRho f → mu (fun g => f (g * nb y)) = mu f := fun f hf => hmu.inv_n (nb y) y.1 (hnb y) f hf
    have hW := w_mem_GF hw
    refine ⟨fun f hf => hN f ((hS f).2 hf), fun f hf => ?_⟩
    have hf' := (hS f).2 hf
    have r1 := GlobalTheory.CompanionTheory.MuC.isRho_right hf' w⁻¹
    have r2 := GlobalTheory.CompanionTheory.MuC.isRho_right r1 (nb y)
    have e3 := hmu.inv_rat w hW _ r2
    have e2 := hN _ r1
    have e1 := hmu.inv_rat w⁻¹ ((GF D p).inv_mem hW) f hf'
    calc mu (fun g => f (g * (w * nb y * w⁻¹))) = mu (fun g => f (g * w * nb y * w⁻¹)) := by
          simp only [mul_assoc]
      _ = mu f := by rw [e3, e2, e1]

end GlobalTheory.CompanionTheory.SetCell

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PairingLatticeRefinementCardStatement
section
open Matrix MeasureTheory GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.LeibOrd GlobalTheory.SplitWeil GlobalTheory.JHMult GlobalTheory.CompanionTheory.BZShell GlobalTheory.CompanionTheory.MirPair GlobalTheory.CompanionTheory.BZCore
open scoped Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pairing_lattice_refinement_card : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {d : ℕ} {V V' : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V'] (B : SchF k d V →ₗ[ℂ] SchF k d V' →ₗ[ℂ] ℂ), (∀ x f f', B (shiftF x f) (shiftF x f') = B f f') → ∀ (L' L : COSub k d) (S : Finset (Fin d → k)), L'.sub ≤ L.sub → IsReps L' L S → ∀ (x : Fin d → k) (a : V) (a' : V'), mL B L x a a' = (S.card : ℂ) * ∑ s ∈ S, mL B L' (x + s) a a' := by
  first | exact @GlobalTheory.CompanionTheory.BZCore.mL_refine | exact GlobalTheory.CompanionTheory.BZCore.mL_refine | (intros; apply GlobalTheory.CompanionTheory.BZCore.mL_refine <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PartialCoefficientSubStatement
section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.partial_coefficient_sub : PcBound → ∀ (D : D7) (n ρ p : ℕ) (hn : ρ + p = n) (M : Maps D hn) (m : Meas D ρ p) (ψ : AddChar (AF D.host.F) ℂ), IsCharAF D.host.F ψ → ∀ (b₀ : HermE D ρ) (F F' : G D n → ℂ), Continuous F → LeftInv (GF D n) F → Continuous F' → LeftInv (GF D n) F' → ∀ (y : Mx D ρ p) (g : G D n), pc M m ψ b₀ (F - F') (M.sh y * g) = pc M m ψ b₀ F (M.sh y * g) - pc M m ψ b₀ F' (M.sh y * g) := by
  first | exact @GlobalTheory.CompanionTheory.PcAdd.pc_sub | exact GlobalTheory.CompanionTheory.PcAdd.pc_sub | (intros; apply GlobalTheory.CompanionTheory.PcAdd.pc_sub <;> assumption)
end

