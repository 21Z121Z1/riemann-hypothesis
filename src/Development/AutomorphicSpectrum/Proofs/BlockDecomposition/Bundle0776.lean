import Mathlib
import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.ThetaIdempotents.HeckeEta
import Formalism.LocalToGlobal.BesselHermitianTheta.Bundle0003
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1870
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0771
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0158
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0312
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0768
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0760
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0375
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PartialConstantTermBound
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FourierZeroHolds
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.KvFintype
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.WeilSiegelTheta.Bundle0001
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0772
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0480
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0346
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0020
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsSmoothModerateOfIsAutFunSm
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0272
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UniqueIrreducibleSubLengthTwo
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0004

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PeriodisationBound
section
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology Pointwise
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.FJE

variable {D : D7} {ρ p : ℕ}

theorem maj_add_le (θ : InfFam D) (K K₀ : Set (Mx D ρ p)) (N : ℕ) (R : ℝ) (hR0 : 0 ≤ R)
    (hR : ∀ w ∈ K₀, GlobalTheory.Unf.realSize θ (-w) ≤ R) (g w : Mx D ρ p) (hw : w ∈ K₀) :
    GlobalTheory.Unf.maj θ K N (g + w) ≤ (1 + R) ^ N * GlobalTheory.Unf.maj θ (K + (-K₀)) N g := by
  by_cases hb : GlobalTheory.Unf.InBox K (g + w)
  · have hb' : GlobalTheory.Unf.InBox (K + (-K₀)) g := by
      obtain ⟨k, hk, h0⟩ := hb
      refine ⟨k + -w, Set.add_mem_add hk (Set.neg_mem_neg.2 hw), ?_⟩
      have e : g - (k + -w) = g + w - k := by abel
      rw [e]; exact h0
    unfold GlobalTheory.Unf.maj
    rw [if_pos hb, if_pos hb']
    have h0 := GlobalTheory.Unf.realSize_nonneg θ g
    have h1 := GlobalTheory.Unf.realSize_nonneg θ (g + w)
    have h2 : 1 + GlobalTheory.Unf.realSize θ g ≤ (1 + R) * (1 + GlobalTheory.Unf.realSize θ (g + w)) := by
      have h3 := GlobalTheory.MajSum.realSize_add_le θ (g + w) (-w)
      rw [add_neg_cancel_right] at h3
      have h4 := hR w hw
      nlinarith
    have hp : (0:ℝ) < (1 + GlobalTheory.Unf.realSize θ (g + w)) ^ N := by positivity
    have hq : (0:ℝ) < (1 + GlobalTheory.Unf.realSize θ g) ^ N := by positivity
    have h5 : (1 + GlobalTheory.Unf.realSize θ g) ^ N ≤ (1 + R) ^ N * (1 + GlobalTheory.Unf.realSize θ (g + w)) ^ N := by
      rw [← mul_pow]
      exact pow_le_pow_left₀ (by linarith) h2 N
    rw [← div_eq_mul_inv, inv_eq_one_div, div_le_div_iff₀ hp hq, one_mul]
    exact h5
  · have h0 : GlobalTheory.Unf.maj θ K N (g + w) = 0 := by unfold GlobalTheory.Unf.maj; rw [if_neg hb]
    rw [h0]
    exact mul_nonneg (by positivity) (GlobalTheory.Unf.maj_nonneg θ _ N g)

theorem continuous_realSize {θ : InfFam D} (hθ : IsInfFam θ) :
    Continuous (GlobalTheory.Unf.realSize θ : Mx D ρ p → ℝ) := by
  unfold GlobalTheory.Unf.realSize
  refine continuous_finset_sum _ fun τ _ => continuous_finset_sum _ fun i _ =>
    continuous_finset_sum _ fun j _ => ?_
  exact ((GlobalTheory.RealWeil.continuous_compAt hθ τ ρ p).matrix_elem i j).norm

theorem periodisation_bound : ∀ {D : D7} {ρ p : ℕ} (θ : InfFam D), IsInfFam θ → ∀ φ ∈ schwartzA θ ρ p,
    ∃ B : ℝ, ∀ y : Mx D ρ p,
      Summable (fun ξ : Matrix (Fin ρ) (Fin p) D.host.E => ‖φ (GlobalTheory.CompanionTheory.FJE.rt ξ + y)‖) ∧
      ∑' ξ : Matrix (Fin ρ) (Fin p) D.host.E, ‖φ (GlobalTheory.CompanionTheory.FJE.rt ξ + y)‖ ≤ B := by
  intro D ρ p θ hθ φ hφ
  obtain ⟨-, K, hK, hbd⟩ := GlobalTheory.SchwartzMaj.hasMaj_of_mem hθ hφ
  obtain ⟨N, hN⟩ := GlobalTheory.MajSum.tsum_maj_ne_top D θ hθ ρ p
  obtain ⟨i1, -, -, -, -, K₀, hK₀, hcov⟩ := lattice_Mx D ρ p
  obtain ⟨C, hC⟩ := hbd N
  have hK' : IsCompact (K + (-K₀)) := hK.add hK₀.neg
  obtain ⟨R₀, hR₀⟩ := hK₀.exists_bound_of_continuousOn (f := fun w => GlobalTheory.Unf.realSize θ (-w))
    ((continuous_realSize hθ).comp continuous_neg).continuousOn
  have hR : ∀ w ∈ K₀, GlobalTheory.Unf.realSize θ (-w) ≤ |R₀| := fun w hw =>
    (le_abs_self _).trans ((hR₀ w hw).trans (le_abs_self _))
  have hg : Summable fun γ : ratMx D ρ p => GlobalTheory.Unf.maj θ (K + (-K₀)) N (γ : Mx D ρ p) := by
    have h := ENNReal.summable_toReal (hN _ hK')
    refine h.congr fun γ => ?_
    exact ENNReal.toReal_ofReal (GlobalTheory.Unf.maj_nonneg θ _ N _)
  set c : ℝ := |C| * (1 + |R₀|) ^ N with hc
  have hc0 : 0 ≤ c := by positivity
  refine ⟨c * ∑' γ : ratMx D ρ p, GlobalTheory.Unf.maj θ (K + (-K₀)) N (γ : Mx D ρ p), fun y => ?_⟩
  obtain ⟨γ, hγ, hy⟩ := hcov y
  obtain ⟨ξ₀, rfl⟩ := mem_ratMx.1 hγ
  let e : Matrix (Fin ρ) (Fin p) D.host.E → ratMx D ρ p := fun ξ => ⟨rat (ξ - ξ₀), rat_mem _⟩
  have he : Function.Injective e := fun a b h => by
    have := rat_injective (congrArg Subtype.val h)
    exact sub_left_injective this
  have key : ∀ ξ, ‖φ (rt ξ + y)‖ ≤ c * GlobalTheory.Unf.maj θ (K + (-K₀)) N (e ξ : Mx D ρ p) := by
    intro ξ
    have e1 : rt ξ + y = rat (ξ - ξ₀) + (rat ξ₀ + y) := by
      have : rat (ξ - ξ₀) = rt ξ - rat ξ₀ := by
        ext i j
        simp [rat, rt]
      rw [this]; abel
    rw [e1]
    refine (hC _).trans ?_
    have h1 := maj_add_le θ K K₀ N |R₀| (abs_nonneg _) hR (rat (ξ - ξ₀)) (rat ξ₀ + y) hy
    calc C * GlobalTheory.Unf.maj θ K N (rat (ξ - ξ₀) + (rat ξ₀ + y))
        ≤ |C| * GlobalTheory.Unf.maj θ K N (rat (ξ - ξ₀) + (rat ξ₀ + y)) :=
          mul_le_mul_of_nonneg_right (le_abs_self C) (GlobalTheory.Unf.maj_nonneg θ _ N _)
      _ ≤ |C| * ((1 + |R₀|) ^ N * GlobalTheory.Unf.maj θ (K + (-K₀)) N (rat (ξ - ξ₀))) :=
          mul_le_mul_of_nonneg_left h1 (abs_nonneg C)
      _ = c * GlobalTheory.Unf.maj θ (K + (-K₀)) N (e ξ : Mx D ρ p) := by rw [hc, mul_assoc]
  have hs' : Summable fun ξ => c * GlobalTheory.Unf.maj θ (K + (-K₀)) N (e ξ : Mx D ρ p) :=
    (hg.comp_injective he).mul_left c
  have hs : Summable fun ξ => ‖φ (rt ξ + y)‖ :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) key hs'
  refine ⟨hs, (hs.tsum_le_tsum key hs').trans ?_⟩
  rw [tsum_mul_left]
  refine mul_le_mul_of_nonneg_left ?_ hc0
  exact tsum_comp_le_tsum_of_inj hg (fun _ => GlobalTheory.Unf.maj_nonneg θ _ N _) he

end GlobalTheory.CompanionTheory.FJE
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SectionEigenfunctionMaximalCompactBis
section
open GlobalTheory.CompanionTheory.Jp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.section_eigenfunction_maximal_compact : GlobalTheory.CompanionTheory.Jp.SectionEigenfunctionMaximalCompact := by
  first | exact @GlobalTheory.CompanionTheory.Jp.B3.eigen_of_rightInvariant | exact GlobalTheory.CompanionTheory.Jp.B3.eigen_of_rightInvariant | (intros; apply GlobalTheory.CompanionTheory.Jp.B3.eigen_of_rightInvariant <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SectionLeftInvariantRationalParabolic
section
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.FJE

theorem leftInv_of_isLaw : ∀ {D : D7} {n : ℕ} (χ : (AE D)ˣ →* Circle) (s : ℂ) (f : G D n → ℂ), IsHeckeChar D χ → IsLaw χ s f → LeftInv (P D n ⊓ GF D n) f := by
  intro D n χ s f hχ hf γ hγ g
  obtain ⟨a, ha⟩ := GlobalTheory.StdUnn.LeftInvSect.exists_blkA hγ.1
  obtain ⟨u, hu⟩ := GlobalTheory.StdUnn.LeftInvSect.det_rat hγ.2 a ha
  have h1 : absA D (Units.map (incA D).toMonoidHom u) = 1 := absE_inclR u
  rw [hf γ hγ.1 a ha g, hu, hχ.2 u, h1]
  simp

end GlobalTheory.CompanionTheory.FJE
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ShAdd
section
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.FJE

theorem sh_add : ∀ {D : D7} {n ρ p : ℕ} {hn : ρ + p = n} (M : Maps D hn) (y y' : Mx D ρ p),
    M.sh y * M.sh y' = M.sh (y + y') :=
  fun M y y' => GlobalTheory.CompanionTheory.PcB.sh_mul M y y'

end GlobalTheory.CompanionTheory.FJE
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ShiftConjHeisenberg
section
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.FJE

theorem sh_mul_nzx {D : D7} {n ρ p : ℕ} {hn : ρ + p = n} (M : Maps D hn) (y : Mx D ρ p)
    (z : hermA D ρ) (x : Mx D ρ p) :
    M.sh y * M.nzx z x = M.nzx (z + GlobalTheory.CompanionTheory.FJE.jc y x) x * M.sh y := by
  have e : GlobalTheory.CompanionTheory.PcB.tw (z + jc y x) x y = z := by
    apply Subtype.ext
    show z.1 + ((HMul.hMul y (adj x) : Mx D ρ ρ) + (HMul.hMul x (adj y) : Mx D ρ ρ))
      - (HMul.hMul x (adj y) : Mx D ρ ρ) - (HMul.hMul y (adj x) : Mx D ρ ρ) = z.1
    abel
  have h := GlobalTheory.CompanionTheory.PcB.nzx_sh M (z + jc y x) x y
  rw [e] at h
  exact h.symm

end GlobalTheory.CompanionTheory.FJE
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.StronglyMeasurableCoefficientComposition
section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CompanionTheory.FJE

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 2000000 in

theorem Wz_stronglyMeasurable : ∀ {D : D7} {n ρ p : ℕ} {hn : ρ + p = n} (M : Maps D hn) (m : Meas D ρ p) (ψ : AddChar (AF D.host.F) ℂ), IsCharAF D.host.F ψ → ∀ (b₀ : HermE D ρ) (f : G D n → ℂ), Continuous f → ∀ {X : Type} [TopologicalSpace X] [SecondCountableTopology X] [MeasurableSpace X] [BorelSpace X] (c : X → G D n), Continuous c → StronglyMeasurable fun v => Wz M m ψ b₀ f (c v) := by
  intro D n ρ p hn M m ψ hψ b₀ f hf X _ _ _ _ c hc
  obtain ⟨i1, i2, i3, i4, -, -⟩ := lattice_Mx D ρ ρ
  haveI : IsTopologicalAddGroup (Mx D ρ ρ) := i1
  haveI : LocallyCompactSpace (Mx D ρ ρ) := i2
  haveI : SecondCountableTopology (Mx D ρ ρ) := i3
  haveI : T2Space (Mx D ρ ρ) := i4
  haveI : BorelSpace (Mx D ρ ρ) := ⟨rfl⟩
  haveI : BorelSpace (hermA D ρ) := Subtype.borelSpace _
  haveI : SecondCountableTopology (hermA D ρ) := Topology.IsInducing.subtypeVal.secondCountableTopology
  haveI : T2Space (hermA D ρ) := Topology.IsEmbedding.subtypeVal.t2Space
  haveI : LocallyCompactSpace (hermA D ρ) :=
    (GlobalTheory.CompanionTheory.FourierN.isClosed_hermA (D := D) (n := ρ)).isClosedEmbedding_subtypeVal.locallyCompactSpace
  haveI := m.hz.1
  haveI : SFinite m.lz := inferInstance
  have hchz : Continuous fun z : hermA D ρ => conj (chz ψ b₀ z) :=
    Complex.continuous_conj.comp
      (hψ.1.comp ((GlobalTheory.CompanionTheory.FourierN.continuous_pr b₀.1).comp continuous_subtype_val))
  have hcont : Continuous fun u : X × hermA D ρ => f (M.w * M.nzx u.2 0 * c u.1) * conj (chz ψ b₀ u.2) := by
    refine (hf.comp ((continuous_const.mul ?_).mul (hc.comp continuous_fst))).mul (hchz.comp continuous_snd)
    exact M.nzx_cont.comp (continuous_snd.prodMk continuous_const)
  exact hcont.stronglyMeasurable.integral_prod_right

end GlobalTheory.CompanionTheory.FJE
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SumCharacterOrthogonalityMatricesStatement
section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS
open IsDedekindDomain NumberField
open PositivityTheory.Rg.Rsw PositivityTheory.Rg.Rsw.L
open GlobalTheory.CompanionTheory.Jp
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sum_character_orthogonality_matrices : ∀ (k : Type) [Field k] [Fintype k] (n : ℕ) (ψ₀ : AddChar k ℂ), ψ₀ ≠ 1 → ∀ β T : Matrix (Fin n) (Fin n) k, T ≠ β → ∑ Y : Matrix (Fin n) (Fin n) k, coY ψ₀ β Y * ψ₀ (Matrix.trace (Y * T)) = 0 := by
  first | exact @GlobalTheory.CompanionTheory.Jp.coY_sum_mul_eq_zero | exact GlobalTheory.CompanionTheory.Jp.coY_sum_mul_eq_zero | (intros; apply GlobalTheory.CompanionTheory.Jp.coY_sum_mul_eq_zero <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ThetaIntegralContinuous
section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CompanionTheory.BigCellJ

theorem integrable_schwartzA {D : D7} {θ : InfFam D} (hθ : IsInfFam θ) {m n : ℕ} {μ : Measure (Mx D m n)}
    {𝓕 : Set (Mx D m n)} (hμ : IsCovolOne (ratMx D m n) μ 𝓕) {φ : Mx D m n → ℂ}
    (hφ : φ ∈ schwartzA θ m n) : Integrable φ μ := by
  obtain ⟨i1, i2, i3, i4, i5, K, hK, hKc⟩ := GlobalTheory.TowerRestrict.lattice_Mx D m n
  haveI : BorelSpace (Mx D m n) := ⟨rfl⟩
  haveI := hμ.1
  haveI i6 : DiscreteTopology (ratMx D m n) := i5
  haveI : SecondCountableTopology (ratMx D m n) := TopologicalSpace.Subtype.secondCountableTopology _
  haveI : Countable (ratMx D m n) := TopologicalSpace.separableSpace_iff_countable.1 inferInstance
  have hc : Continuous φ := (GlobalTheory.CompanionTheory.WeilTheta.schwartzA_continuous_and_dominated D θ hθ _ _ φ hφ).1
  have hU : GlobalTheory.CompanionTheory.Hypotheses₂.OneV.PoiAbs.UnifSummable (ratMx D m n).subtype φ := fun Q hQ => by
    obtain ⟨b, hb1, hb2⟩ := GlobalTheory.CompanionTheory.ThetaPoisson.translates_bound hθ ⟨φ, hφ⟩ Q hQ
    refine ⟨b, hb1, fun c x hx => ?_⟩
    have h := hb2 x hx c
    rwa [add_comm] at h
  exact GlobalTheory.CompanionTheory.Hypotheses₂.OneV.PoiAbs.integrable_of_unif hc hU μ hK fun x => by
    obtain ⟨γ, hγ, h⟩ := hKc x
    refine ⟨⟨-γ, (ratMx D m n).neg_mem hγ⟩, ?_⟩
    simpa [sub_neg_eq_add, add_comm] using h

theorem continuous_halfTr {D : D7} : Continuous (halfTr : AE D → AF D.host.F) := by
  haveI := isTopologicalRing_tens (F := D.host.F) (E := D.host.E) (R := AF D.host.F)
  haveI : IsModuleTopology (AF D.host.F) (AE D) := ⟨rfl⟩
  have ht : Continuous (trA : AE D → AF D.host.F) :=
    IsModuleTopology.continuous_of_linearMap (Algebra.trace (AF D.host.F) (AE D))
  unfold halfTr
  exact continuous_const.mul ht

theorem continuous_integral_twist {X Y : Type*} [TopologicalSpace X] [FirstCountableTopology X]
    [TopologicalSpace Y] [SecondCountableTopology Y] [MeasurableSpace Y] [OpensMeasurableSpace Y]
    {μ : Measure Y} {φ : Y → ℂ} {g : X → Y → ℂ} (hi : Integrable φ μ)
    (hj : Continuous fun p : X × Y => g p.1 p.2) (hn : ∀ b y, ‖g b y‖ = 1) :
    Continuous fun b => ∫ y, φ y * g b y ∂μ := by
  have hg1 : ∀ b, AEStronglyMeasurable (g b) μ := fun b =>
    (hj.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable
  have hg2 : ∀ y, Continuous fun b => g b y := fun y =>
    hj.comp (continuous_id.prodMk continuous_const)
  refine continuous_of_dominated (bound := fun y => ‖φ y‖) (fun b => ?_) (fun b => ?_) hi.norm ?_
  · exact hi.aestronglyMeasurable.mul (hg1 b)
  · refine Filter.Eventually.of_forall fun y => ?_
    rw [norm_mul, hn, mul_one]
  · refine Filter.Eventually.of_forall fun y => ?_
    exact (hg2 y).const_mul (φ y)

theorem continuous_inner_self {D : D7} (V : HSp D) (r : ℕ) :
    Continuous fun y : Mx D V.rank r => (GlobalTheory.StdUnn.inner V y y : Mx D r r) := by
  haveI := isTopologicalRing_tens (F := D.host.F) (E := D.host.E) (R := AF D.host.F)
  unfold GlobalTheory.StdUnn.inner
  exact GlobalTheory.MixModel.continuous_adj.matrix_mul (continuous_const.matrix_mul continuous_id)

theorem continuous_phase {D : D7} (V : HSp D) (r : ℕ) {ψ : AddChar (AF D.host.F) ℂ}
    (hψ : IsCharAF D.host.F ψ) :
    Continuous fun p : hermA D r × Mx D V.rank r =>
      ψ (halfTr (Matrix.trace (HMul.hMul p.1.1 (GlobalTheory.StdUnn.inner V p.2 p.2) : Mx D r r))) := by
  haveI := isTopologicalRing_tens (F := D.host.F) (E := D.host.E) (R := AF D.host.F)
  exact hψ.1.comp (continuous_halfTr.comp
    ((continuous_subtype_val.comp continuous_fst).matrix_mul
      ((continuous_inner_self V r).comp continuous_snd)).matrix_trace)

theorem jt_continuous : ∀ (D : D7) (r : ℕ) (V : HSp D) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D)
    (μ : Measure (Mx D V.rank r)) (φ : Mx D V.rank r → ℂ), IsCharAF D.host.F ψ → IsInfFam θ →
    (∃ 𝓕, IsCovolOne (ratMx D V.rank r) μ 𝓕) → φ ∈ schwartzA θ V.rank r → Continuous (Jt ψ V μ φ) := by
  intro D r V ψ θ μ φ hψ hθ ⟨𝓕, hμ⟩ hφ
  obtain ⟨i1, i2, i3, i4, i5, -⟩ := GlobalTheory.TowerRestrict.lattice_Mx D V.rank r
  obtain ⟨j1, j2, j3, j4, j5, -⟩ := GlobalTheory.TowerRestrict.lattice_Mx D r r
  haveI : BorelSpace (Mx D V.rank r) := ⟨rfl⟩
  haveI : SecondCountableTopology (hermA D r) := TopologicalSpace.Subtype.secondCountableTopology _
  haveI : FirstCountableTopology (hermA D r) :=
    TopologicalSpace.SecondCountableTopology.to_firstCountableTopology _
  exact continuous_integral_twist (g := fun (b : hermA D r) (y : Mx D V.rank r) =>
      ψ (halfTr (Matrix.trace (HMul.hMul b.1 (GlobalTheory.StdUnn.inner V y y) : Mx D r r))))
    (integrable_schwartzA hθ hμ hφ) (continuous_phase V r hψ) (fun b y => hψ.2.1 _)

end GlobalTheory.CompanionTheory.BigCellJ

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ThetaIntegralLeFundamentalSetStatement
section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.SiegelFormula
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.theta_integral_le_fundamental_set : ∀ (D : D7) (V : HSp D) (ν : Measure (GA D V)), ν.IsHaarMeasure → ∀ {n : ℕ} (φ : Mx D V.rank n → ℂ), Continuous φ → ∀ S : Set (GA D V), MeasurableSet S → (∀ g, ∃ γ ∈ GQ V, γ * g ∈ S) → absThetaInt V ν φ ≤ ∫⁻ g in S, absTheta V φ g ∂ν := by
  first | exact @GlobalTheory.CompanionTheory.WeilConv.absThetaInt_le_of_meets_orbits | exact GlobalTheory.CompanionTheory.WeilConv.absThetaInt_le_of_meets_orbits | (intros; apply GlobalTheory.CompanionTheory.WeilConv.absThetaInt_le_of_meets_orbits <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ThetaSumInvariantWeylInvolutionStatement
section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.EC
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.theta_sum_invariant_weyl_involution : ∀ (D : D7) (n : ℕ) (V : HSp D) ψ χ θ μ ω, HidaSetting D n V ψ χ θ μ ω →
  ∀ g : G D n, mat g = blk4 0 1 (-1) 0 →
  ∀ Φ : schwartzA θ V.rank n,
    ∑' ξ : Matrix (Fin V.rank) (Fin n) D.host.E, (ω g Φ).1 (ξ.map (incA D)) =
      ∑' ξ : Matrix (Fin V.rank) (Fin n) D.host.E, Φ.1 (ξ.map (incA D)) := by
  first | exact @GlobalTheory.CompanionTheory.ThetaPoisson.theta_weyl | exact GlobalTheory.CompanionTheory.ThetaPoisson.theta_weyl | (intros; apply GlobalTheory.CompanionTheory.ThetaPoisson.theta_weyl <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnipotentAdditiveLaw
section
noncomputable section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.NzxAdd

theorem nzx_add : ∀ {D : D7} {n ρ p : ℕ} {hn : ρ + p = n} (M : Maps D hn) (z z' : hermA D ρ) (x x' : Mx D ρ p), M.nzx z x * M.nzx z' x' = M.nzx (z + z') (x + x') := by
  intro D n ρ p hn M z z' x x'
  exact GlobalTheory.CompanionTheory.PcB.nzx_mul M z z' x x'

end GlobalTheory.CompanionTheory.NzxAdd
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UniqueIrreducibleSubLengthTwoStatement
section
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.JHMult
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unique_irreducible_sub_length_two : (∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (d : ℕ), 0 < d →
    ∀ σ : IrrRep (GL (Fin d) k), IsCuspidal σ.ρ →
      ∃ S : Subrepresentation (multiProd (GlobalTheory.Published.consecBlocks 2 d) (segTerm σ.ρ 2)),
        S.toRepresentation.IsIrreducible ∧
        (∀ S' : Subrepresentation (multiProd (GlobalTheory.Published.consecBlocks 2 d) (segTerm σ.ρ 2)),
          S'.toRepresentation.IsIrreducible → S' = S) ∧
        Nonempty ((jac (GlobalTheory.Published.consecBlocks 2 d) S.toRepresentation).Equiv (piTensor (segTerm σ.ρ 2)))) →
  GlobalTheory.Published.SegmentRepresentation := by
  first | exact @GlobalTheory.CompanionTheory.SegZRep.segmentRepresentation_of_two | exact GlobalTheory.CompanionTheory.SegZRep.segmentRepresentation_of_two | (intros; apply GlobalTheory.CompanionTheory.SegZRep.segmentRepresentation_of_two <;> assumption)
end

