import Mathlib
import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.ThetaIdempotents.HeckeEta
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0823
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0013
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0810
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0811
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NondegenerateCharacterCellFactorization
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0801
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0827
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PartialConstantTermBound
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.BaseOneSide.PsiSide
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0224
import Development.AbelianVarietyTheory.Definitions.Foundations.T2SpaceTensorProductFiniteExtension
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0773
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0828
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0321
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0224
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0429
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0042
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0483
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0471
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0498
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0477
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0460
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0814
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0470
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0481
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0463
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0821
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0446
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ArchimedeanBinaryGramDensity
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0181
import Development.WeilBound.CoreStatements.ThetaDilations.ThetaLint
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0034
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0028
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0055
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0033
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0032
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0044
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0024
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0058
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0026
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0054
import GroundTheory.IdeleRoots.TorusPowers.HeckeTensor
import GroundTheory.GlobalFields.IdeleGroups.NormOneCompact
import GroundTheory.GlobalFields.TateThesis.Bundle0006

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HeisenbergCentreRationalForm
section
noncomputable section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS GlobalTheory.Eis GlobalTheory.CompanionTheory.SwUnf
open PositivityTheory.GramSchwartzFunctions.EC GlobalTheory.StdUnn.Model GlobalTheory.StdUnn.LeftInvSect GlobalTheory.CompanionTheory.Hypotheses₂.WeilU
open PositivityTheory.Rg.Rsw
open GlobalTheory.CompanionTheory.ZUnf GlobalTheory.Eis

namespace GlobalTheory.CompanionTheory.ZUnf.Centre

open GlobalTheory.CompanionTheory.PcB

variable {D : D7} {n ρ p : ℕ} {hn : ρ + p = n}

theorem centre_commutes_embedded_block {R : Type} [CommRing R] (hn : ρ + p = n) (z : Matrix (Fin ρ) (Fin ρ) R)
    (a b c d : Matrix (Fin p) (Fin p) R) :
    HMul.hMul (blk4 1 (bl hn z 0 0 0) 0 1)
        (blk4 (bl hn 1 0 0 a) (bl hn 0 0 0 b) (bl hn 0 0 0 c) (bl hn 1 0 0 d)) =
      HMul.hMul (blk4 (bl hn 1 0 0 a) (bl hn 0 0 0 b) (bl hn 0 0 0 c) (bl hn 1 0 0 d))
        (blk4 1 (bl hn z 0 0 0) 0 1) := by
  have h1 : HMul.hMul (bl hn z 0 0 0) (bl hn 0 0 0 c) = 0 := by
    rw [blockMatrix_multiply]
    simp [bl]
  have h2 : HMul.hMul (bl hn z 0 0 0) (bl hn 1 0 0 d) = bl hn z 0 0 0 := by
    rw [blockMatrix_multiply]
    simp
  have h3 : HMul.hMul (bl hn 1 0 0 a) (bl hn z 0 0 0) = bl hn z 0 0 0 := by
    rw [blockMatrix_multiply]
    simp
  have h4 : HMul.hMul (bl hn 0 0 0 c) (bl hn z 0 0 0) = 0 := by
    rw [blockMatrix_multiply]
    simp [bl]
  rw [submatrix_fromBlocks_mul, submatrix_fromBlocks_mul, h1, h2, h3, h4]
  congr 1 <;> simp [add_comm]

theorem nzx_add (M : Maps D hn) (a b : hermA D ρ) : M.nzx (a + b) 0 = M.nzx a 0 * M.nzx b 0 := by
  rw [nzx_mul, add_zero]

theorem nzx_comm_sh (M : Maps D hn) (z : hermA D ρ) (y : Mx D ρ p) :
    M.nzx z 0 * M.sh y = M.sh y * M.nzx z 0 := by
  have h : tw z 0 y = z := by
    apply Subtype.ext
    simp [tw]
  have e := nzx_sh M z 0 y
  rwa [h] at e

theorem nzx_comm_emb (M : Maps D hn) (z : hermA D ρ) (h : G D p) :
    M.nzx z 0 * M.emb h = M.emb h * M.nzx z 0 := by
  obtain ⟨b, d, hb⟩ := SmallCell.exists_blocks (mat h)
  apply GlobalTheory.CompanionTheory.FourierN.mat_injective
  rw [mat_mul', mat_mul', M.nzx_mat, M.emb_mat h _ _ _ _ hb, adj_zero]
  exact centre_commutes_embedded_block hn z.1 _ _ _ _

theorem nzx_rat_mat (M : Maps D hn) (l : ratHerm D ρ) :
    ∃ ζ : Matrix (Fin ρ) (Fin ρ) D.host.E,
      ζ.map (incA D) = l.1.1 ∧ mat (M.nzx l.1 0) = blk4 1 ((bl hn ζ 0 0 0).map (incA D)) 0 1 := by
  obtain ⟨b, hb⟩ := BigCell.exists_hermQ l
  have e : ∀ {a c : ℕ}, (0 : Matrix (Fin a) (Fin c) D.host.E).map (incA D) = 0 := rat_zero'
  refine ⟨b.1, hb, ?_⟩
  rw [blockMatrix_map₂, hb, e, e, e, M.nzx_mat, adj_zero]

theorem nzx_mem_GF (M : Maps D hn) (l : ratHerm D ρ) : M.nzx l.1 0 ∈ GF D n := by
  have h := nzx_rat M l.1 l.2 0
  rwa [rat_zero'] at h

end GlobalTheory.CompanionTheory.ZUnf.Centre

namespace GlobalTheory.CompanionTheory.ZUnf

theorem centre_nzx : ∀ {D : D7} {n ρ p : ℕ} {hn : ρ + p = n} (M : Maps D hn),
    (∀ a b, M.nzx (a + b) 0 = M.nzx a 0 * M.nzx b 0) ∧ (∀ z y, M.nzx z 0 * M.sh y = M.sh y * M.nzx z 0) ∧
    (∀ z h, M.nzx z 0 * M.emb h = M.emb h * M.nzx z 0) ∧
    ∀ l : ratHerm D ρ, M.nzx l.1 0 ∈ GF D n ∧ ∃ ζ : Matrix (Fin ρ) (Fin ρ) D.host.E,
      ζ.map (incA D) = l.1.1 ∧ mat (M.nzx l.1 0) = blk4 1 ((bl hn ζ 0 0 0).map (incA D)) 0 1 :=
  fun M => ⟨Centre.nzx_add M, Centre.nzx_comm_sh M, Centre.nzx_comm_emb M,
    fun l => ⟨Centre.nzx_mem_GF M l, Centre.nzx_rat_mat M l⟩⟩

end GlobalTheory.CompanionTheory.ZUnf
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermitianExistencePrinciple
section
noncomputable section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain Topology
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.RgBase

open PositivityTheory.Rg.Base1

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem norm_tmul_one {σ : E →ₐ[F] E} (h : IsCMExt F E σ) (x : AF F ⊗[F] E) :
    (Algebra.norm (AF F) x) ⊗ₜ[F] (1 : E) = sigR (AF F) σ x * x := by
  have e := GlobalTheory.Doubling.algebraMap_norm_eq h (R := AF F) x
  rw [Algebra.TensorProduct.algebraMap_apply] at e
  rw [mul_comm]
  exact e

theorem isNm_iff {σ : E →ₐ[F] E} (h : IsCMExt F E σ) (x : (AF F ⊗[F] E)ˣ) (a : (AF F)ˣ) :
    IsNm σ x a ↔ Algebra.norm (AF F) (x : AF F ⊗[F] E) = a := by
  have hinj : Function.Injective (fun r : AF F => r ⊗ₜ[F] (1 : E)) :=
    Algebra.TensorProduct.includeLeft_injective (S := F) (algebraMap F E).injective
  unfold IsNm
  rw [← norm_tmul_one h]
  exact ⟨fun e => (hinj e).symm, fun e => by rw [e]⟩

theorem hEx : HEx := by
  intro F E _ _ _ _ _ σ h
  haveI : Algebra.IsQuadraticExtension F E := ⟨h.2.2.1⟩
  refine ⟨(GlobalTheory.IdeleNormChar.normSign (K := F) E).ker, ?_, ?_, ?_⟩
  · intro a
    rw [MonoidHom.mem_ker]
    constructor
    · intro ha
      obtain ⟨t, x, hx⟩ := (GlobalTheory.IdeleNormChar.normSign_eq_one_iff E a).1 ha
      refine ⟨t, x, a / GlobalTheory.QuadSymbol.toUnits F (AdeleRing (𝓞 F) F) t, ?_, ?_⟩
      · exact (isNm_iff h x _).2 (congrArg Units.val hx)
      · exact (mul_div_cancel (GlobalTheory.QuadSymbol.toUnits F (AdeleRing (𝓞 F) F) t) a).symm
    · rintro ⟨t, x, n, hn, rfl⟩
      have h1 : GlobalTheory.IdeleNormChar.normSign E (pr t) = 1 := GlobalTheory.IdeleNormChar.normSign_toUnits E t
      have h2 : GlobalTheory.IdeleNormChar.normSign E n = 1 :=
        GlobalTheory.IdeleNormChar.normSign_of_mem E ⟨x, Units.ext ((isNm_iff h x n).1 hn)⟩
      rw [map_mul, h1, h2, one_mul]
  · refine Subgroup.isOpen_of_mem_nhds _ (g := 1) ?_
    filter_upwards [GlobalTheory.IdeleNormChar.eventually_normSign (K := F) E] with a ha
    exact ha
  · obtain ⟨b, hb⟩ := GlobalTheory.IdeleNormChar.exists_normSign_ne_one (K := F) E
    have hr : (GlobalTheory.IdeleNormChar.normSign (K := F) E).range = ⊤ := by
      rw [eq_top_iff]
      intro u _
      rcases Int.units_eq_one_or u with rfl | rfl
      · exact one_mem _
      · exact ⟨b, (Int.units_eq_one_or _).resolve_left hb⟩
    rw [Subgroup.index_ker, hr, Subgroup.card_top, Nat.card_eq_fintype_card, Fintype.card_units_int]

end GlobalTheory.CompanionTheory.RgBase

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsPlacesOfHasRealPar
section
noncomputable section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC GlobalTheory.CompanionTheory.IwaAd PositivityTheory.PfSWUS GlobalTheory.CompanionTheory.SiegelND GlobalTheory.CompanionTheory.MM

namespace GlobalTheory.CompanionTheory.MM

theorem isPlaces_of_hasRealPar : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (l : D.what₂.Tau → ℝ), IsCharAF D.host.F ψ → IsInfFam θ → HasRealPar ψ θ l → PositivityTheory.SiegelWeilFormula.Gen.IsPlaces D.sp.cm.sig ψ θ l ∧ Nonempty D.what₂.Tau := by
  intro D ψ θ l hψ hθ hl
  refine ⟨⟨fun τ => GlobalTheory.Mem.VolExists.infEmb_continuous (hθ τ),
    GlobalTheory.Mem.VolExists.infEmb_bijective (isCMExt_host D) (GlobalTheory.Mem.Vol.isCMFam_host _ D.host _ D.eTau) hθ,
    fun τ z => GlobalTheory.Mem.VolExists.infEmb_sigR (isCMExt_host D) (hθ τ) z,
    fun τ => GlobalTheory.CompanionTheory.IfrAdd.realPar_ne_zero hψ hθ hl τ, hl⟩, ?_⟩
  exact D.eTau.nonempty_congr.2 inferInstance

end GlobalTheory.CompanionTheory.MM
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JacquetKernelLatticeConjCompactStatement
section
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.Rodier GlobalTheory.CompanionTheory.BZPsiPG GlobalTheory.CompanionTheory.BZPsiPG.FibKer
open scoped TensorProduct

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.jacquet_kernel_lattice_conj_compact : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) {X : Type} [AddCommGroup X] [Module ℂ X] (ρ : Representation ℂ (Multiplicative (Fin n → k)) X) (c : k) (κ : GL (Fin n) k), κ ∈ GlobalTheory.SplitWeil.KO k (Fin n) → ∀ x, x ∈ twKer ρ (Lc n c) 1 → x ∈ twKer (MonoidHom.comp ρ (mulH κ)) (Lc n c) 1 := by
  first | exact @GlobalTheory.CompanionTheory.BZPsiPG.FibKer.IntTwist.twKer_Lc_le_twist | exact GlobalTheory.CompanionTheory.BZPsiPG.FibKer.IntTwist.twKer_Lc_le_twist | (intros; apply GlobalTheory.CompanionTheory.BZPsiPG.FibKer.IntTwist.twKer_Lc_le_twist <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalDensityFormula
section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology Filter
open PositivityTheory.Rg.Base1 PositivityTheory.SiegelWeilFormula.Densx
open scoped TensorProduct ENNReal NNReal

noncomputable section

namespace GlobalTheory.CompanionTheory.SW.RankOne

theorem dens : Dens := by
  intro F E _ _ _ _ _ σ J d b li lam μ 𝓕 mi m hσ hJ hli hlam hμ hF hmi hm S φ A hT
  obtain ⟨hφ, hφc, hφ0, hφU, hA, -⟩ := hT
  have : BorelSpace (Ainf F) := ⟨rfl⟩
  obtain ⟨c1, c2, -, c4⟩ := GlobalTheory.CompanionTheory.SW.ArchFibre.fibre_integral (Ainf F)
    (GlobalTheory.CompanionTheory.SW.isLocR_Ainf F hσ.1) hσ hJ b li hli.1 mi hmi φ hφ hφc hφ0 hφU
  have hv : ∀ v ∈ S, Continuous (fun s : Fv F v => (m v (hermScal (Fv F v) σ s) (A v)).toReal) ∧
      HasCompactSupport (fun s : Fv F v => (m v (hermScal (Fv F v) σ s) (A v)).toReal) ∧
      ENNReal.ofReal (∫ s, (m v (hermScal (Fv F v) σ s) (A v)).toReal ∂(lam v)) =
        coordW (Fv F v) b (lam v) 1 1 (A v) := fun v hvS => by
    have : BorelSpace (Fv F v) := ⟨rfl⟩
    exact GlobalTheory.CompanionTheory.SW.FibreCpt.masses_field (Fv F v) (GlobalTheory.T.completion_is_local_ring F v) hσ hJ b (lam v) (hlam v).1
      (m v) (hm v) (A v) (hA v hvS).1 (hA v hvS).2.1 (hA v hvS).2.2
  refine ⟨c1, c2, fun v hvS => ⟨continuous_const.mul (hv v hvS).1, (hv v hvS).2.1.mul_left⟩, ?_⟩
  have hI0 : 0 ≤ ∫ y, Gi mi φ y ∂li :=
    integral_nonneg fun s => integral_nonneg fun X => hφ0 X
  have hJ0 : ∀ v ∈ S, 0 ≤ ∫ s, gv m A v s ∂(lam v) := fun v _ =>
    integral_nonneg fun s => mul_nonneg (NNReal.coe_nonneg _) ENNReal.toReal_nonneg
  have hloc : ∀ v ∈ S, ENNReal.ofReal (∫ s, gv m A v s ∂(lam v)) =
      (cfac E v : ℝ≥0∞) * coordW (Fv F v) b (lam v) 1 1 (A v) := fun v hvS => by
    have e : ∫ s, gv m A v s ∂(lam v) =
        (cfac E v : ℝ) * ∫ s, (m v (hermScal (Fv F v) σ s) (A v)).toReal ∂(lam v) :=
      integral_const_mul _ _
    rw [e, ENNReal.ofReal_mul (NNReal.coe_nonneg _), ENNReal.ofReal_coe_nnreal, (hv v hvS).2.2]
  rw [ENNReal.ofReal_mul hI0, ENNReal.ofReal_prod_of_nonneg hJ0, Finset.prod_congr rfl hloc,
    Finset.prod_mul_distrib]
  have e0 : ENNReal.ofReal (∫ y, Gi mi φ y ∂li) = ∫⁻ X, ENNReal.ofReal (φ X) ∂(coordW (Ainf F) b li 1 1) := c4
  rw [e0, vol]
  ring

end GlobalTheory.CompanionTheory.SW.RankOne

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalHaarLatticeUnipotentIntegralStatement
section
noncomputable section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC GlobalTheory.CompanionTheory.IwaAd PositivityTheory.PfSWUS GlobalTheory.CompanionTheory.SiegelND GlobalTheory.CompanionTheory.MM
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_haar_lattice_unipotent_integral : ∀ (D : D7) (n : ℕ) (θ : InfFam D), IsInfFam θ → ∀ (H : G D n → ℝ≥0), IsHeight H → ∀ (nb : hermA D n → G D n), IsNMap nb → ∀ w : G D n, mat w = blk4 0 1 (-1) 0 → ∀ (a : GL (Fin n) (AE D)) (lamG : ∀ v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers D.host.F), Measure (Fin n → HeckeCharacterZeroLocus.SiegelWeilU.Fv D.host.F v ⊗[D.host.F] D.host.E)), (∀ v, (lamG v).IsAddHaarMeasure) → ∀ b : hermA D n, PositivityTheory.SiegelWeilFormula.Gen.nuA θ (gAt θ a) lamG (latAt a.1) (latAt (adj (a⁻¹).1)) b.1 = ((H (w * nb (pull a b)) : ℝ≥0) : ℝ)⁻¹ := by
  first | exact @GlobalTheory.CompanionTheory.HeightNu.heightNu | exact GlobalTheory.CompanionTheory.HeightNu.heightNu | (intros; apply GlobalTheory.CompanionTheory.HeightNu.heightNu <;> assumption)
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocallyConstantCosetIndicatorSumStatement
section
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.Rodier GlobalTheory.CompanionTheory.BZPsiPG GlobalTheory.CompanionTheory.BZPsiPG.FibKer
open scoped TensorProduct

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.locally_constant_coset_indicator_sum : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (t : ℕ) {Z : Type} [AddCommGroup Z] [Module ℂ Z] (φ : (Fin t → k) → Z) (c : k), c ≠ 0 → HasCompactSupport φ → (∀ o ∈ Lc t c, ∀ v, φ (v + o.toAdd) = φ v) → ∃ A : Finset (Fin t → k), ∀ v, φ v = ∑ a ∈ A, (cosetSet t c a).indicator (fun _ => φ a) v := by
  first | exact @GlobalTheory.CompanionTheory.BZPsiPG.FibKer.eq_sum_coset_indicators | exact GlobalTheory.CompanionTheory.BZPsiPG.FibKer.eq_sum_coset_indicators | (intros; apply GlobalTheory.CompanionTheory.BZPsiPG.FibKer.eq_sum_coset_indicators <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NondegenerateCentreCharacterCell
section
noncomputable section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS GlobalTheory.Eis GlobalTheory.CompanionTheory.SwUnf
open PositivityTheory.GramSchwartzFunctions.EC GlobalTheory.StdUnn.Model GlobalTheory.StdUnn.LeftInvSect GlobalTheory.CompanionTheory.Hypotheses₂.WeilU
open PositivityTheory.Rg.Rsw
open GlobalTheory.CompanionTheory.ZUnf GlobalTheory.Eis

namespace GlobalTheory.CompanionTheory.ZUnf.SmallZ
open GlobalTheory.CompanionTheory.SwUnf.SmallCell

variable {D : D7} {n ρ p : ℕ}

theorem zinc_inl {K : Type} [Field K] (hn : ρ + p = n) (u : Fin ρ → K) (a : Fin ρ) :
    zinc hn u ((finSumFinEquiv.trans (finCongr hn)) (Sum.inl a)) = u a := by
  change Sum.elim u (fun _ : Fin p => (0 : K)) ((finSumFinEquiv.trans (finCongr hn)).symm _) = u a
  rw [Equiv.symm_apply_apply, Sum.elim_inl]

theorem zinc_inr {K : Type} [Field K] (hn : ρ + p = n) (u : Fin ρ → K) (a : Fin p) :
    zinc hn u ((finSumFinEquiv.trans (finCongr hn)) (Sum.inr a)) = 0 := by
  change Sum.elim u (fun _ : Fin p => (0 : K)) ((finSumFinEquiv.trans (finCongr hn)).symm _) = 0
  rw [Equiv.symm_apply_apply, Sum.elim_inr]

theorem blockMatrix_inl_inl {R : Type} [Zero R] (hn : ρ + p = n) (a : Matrix (Fin ρ) (Fin ρ) R) (i j : Fin ρ) :
    bl hn a 0 0 0 ((finSumFinEquiv.trans (finCongr hn)) (Sum.inl i))
      ((finSumFinEquiv.trans (finCongr hn)) (Sum.inl j)) = a i j := by
  simp only [bl, Matrix.submatrix_apply, Equiv.symm_apply_apply, Matrix.fromBlocks_apply₁₁]

theorem blockMatrix_inl_inr {R : Type} [Zero R] (hn : ρ + p = n) (a : Matrix (Fin ρ) (Fin ρ) R) (i : Fin ρ) (j : Fin p) :
    bl hn a 0 0 0 ((finSumFinEquiv.trans (finCongr hn)) (Sum.inl i))
      ((finSumFinEquiv.trans (finCongr hn)) (Sum.inr j)) = 0 := by
  simp only [bl, Matrix.submatrix_apply, Equiv.symm_apply_apply, Matrix.fromBlocks_apply₁₂, Matrix.zero_apply]

theorem blockMatrix_inr_inl {R : Type} [Zero R] (hn : ρ + p = n) (a : Matrix (Fin ρ) (Fin ρ) R) (i : Fin p) (j : Fin ρ) :
    bl hn a 0 0 0 ((finSumFinEquiv.trans (finCongr hn)) (Sum.inr i))
      ((finSumFinEquiv.trans (finCongr hn)) (Sum.inl j)) = 0 := by
  simp only [bl, Matrix.submatrix_apply, Equiv.symm_apply_apply, Matrix.fromBlocks_apply₂₁, Matrix.zero_apply]

theorem blockMatrix_inr_inr {R : Type} [Zero R] (hn : ρ + p = n) (a : Matrix (Fin ρ) (Fin ρ) R) (i j : Fin p) :
    bl hn a 0 0 0 ((finSumFinEquiv.trans (finCongr hn)) (Sum.inr i))
      ((finSumFinEquiv.trans (finCongr hn)) (Sum.inr j)) = 0 := by
  simp only [bl, Matrix.submatrix_apply, Equiv.symm_apply_apply, Matrix.fromBlocks_apply₂₂, Matrix.zero_apply]

def rk2 {m : ℕ} (τ : AE D) (v r : Fin m → D.host.E) : Mx D m m :=
  τ • ((rat (Matrix.replicateCol (Fin 1) v) : Mx D m 1) ⬝ (rat (Matrix.replicateRow (Fin 1) r) : Mx D 1 m) +
    adj (rat (Matrix.replicateRow (Fin 1) r) : Mx D 1 m) ⬝ adj (rat (Matrix.replicateCol (Fin 1) v) : Mx D m 1))

theorem rank_two_matrix_apply {m : ℕ} (τ : AE D) (v r : Fin m → D.host.E) (i j : Fin m) :
    rk2 τ v r i j = τ * (incA D (v i) * incA D (r j) + cA D (incA D (r i)) * cA D (incA D (v j))) := by
  simp only [rk2, Matrix.smul_apply, Matrix.add_apply, Matrix.mul_apply, Finset.univ_unique, Finset.sum_singleton, smul_eq_mul]
  rfl

theorem rk_term (τ : AE D) (a b c d : D.host.E) (h1 : a = 0 ∨ b = 0) (h2 : c = 0 ∨ d = 0) :
    τ * (incA D a * incA D b + cA D (incA D c) * cA D (incA D d)) = 0 := by
  have e1 : incA D a * incA D b = 0 := by
    rcases h1 with rfl | rfl
    · rw [map_zero (incA D), zero_mul]
    · rw [map_zero (incA D), mul_zero]
  have e2 : cA D (incA D c) * cA D (incA D d) = 0 := by
    rcases h2 with rfl | rfl
    · rw [map_zero (incA D), map_zero (cA D), zero_mul]
    · rw [map_zero (incA D), map_zero (cA D), mul_zero]
  rw [e1, e2, add_zero, mul_zero]

theorem rank_two_embedding_small (hn : ρ + p = n) (τ : AE D) (v r : Fin ρ → D.host.E) :
    rk2 τ (zinc hn v) (zinc hn r) = bl hn (rk2 τ v r) 0 0 0 := by
  ext i j
  obtain ⟨i, rfl⟩ := (finSumFinEquiv.trans (finCongr hn)).surjective i
  obtain ⟨j, rfl⟩ := (finSumFinEquiv.trans (finCongr hn)).surjective j
  rcases i with i | i <;> rcases j with j | j
  · rw [blockMatrix_inl_inl, rank_two_matrix_apply, rank_two_matrix_apply, zinc_inl, zinc_inl, zinc_inl, zinc_inl]
  · rw [blockMatrix_inl_inr, rank_two_matrix_apply]
    exact rk_term _ _ _ _ _ (Or.inr (zinc_inr hn r j)) (Or.inr (zinc_inr hn v j))
  · rw [blockMatrix_inr_inl, rank_two_matrix_apply]
    exact rk_term _ _ _ _ _ (Or.inl (zinc_inr hn v i)) (Or.inl (zinc_inr hn r i))
  · rw [blockMatrix_inr_inr, rank_two_matrix_apply]
    exact rk_term _ _ _ _ _ (Or.inl (zinc_inr hn v i)) (Or.inl (zinc_inr hn r i))

theorem small : ∀ {D : D7} {n ρ p : ℕ} (hn : ρ + p = n) {ψ : AddChar (AF D.host.F) ℂ}, IsCharAF D.host.F ψ → ∀ (b₀ : HermE D ρ), b₀.1.det ≠ 0 →
    ∀ (W : Submodule D.host.E (Fin ρ → D.host.E)), W ≠ ⊥ → ∃ ν : hermA D ρ, chz ψ b₀ ν ≠ 1 ∧
    ∀ (γ u : G D n), γ ∈ GF D n → ∀ x : Matrix (Fin (n + n)) (Fin (n + n)) D.host.E, mat γ = x.map (incA D) → zKer hn x = W →
      mat u = blk4 1 (bl hn ν.1 0 0 0) 0 1 →
      ∃ q ∈ P D n, ∃ a : GL (Fin n) (AE D), blkA (mat q) = a.1 ∧ Matrix.GeneralLinearGroup.det a = 1 ∧ γ * u = q * γ := by
  intro D n ρ p hn ψ hψ β hβ W hW
  obtain ⟨v, hvW, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hW
  have hw : β.1 *ᵥ v ≠ 0 := fun h => hv0 (Matrix.eq_zero_of_mulVec_eq_zero hβ h)
  obtain ⟨i0, hi0⟩ := Function.ne_iff.1 hw
  let r : Fin ρ → D.host.E := Pi.single i0 ((β.1 *ᵥ v) i0)⁻¹
  let V0 : Matrix (Fin ρ) (Fin 1) D.host.E := Matrix.replicateCol _ v
  let R0 : Matrix (Fin 1) (Fin ρ) D.host.E := Matrix.replicateRow _ r
  have hbV : β.1 ⬝ V0 = Matrix.replicateCol _ (β.1 *ᵥ v) := by
    ext i j
    simp [V0, Matrix.mul_apply, Matrix.mulVec, dotProduct]
  have hS0 : R0 ⬝ β.1 ⬝ V0 = (1 : Matrix (Fin 1) (Fin 1) D.host.E) := by
    rw [Matrix.mul_assoc, hbV]
    ext a b
    obtain rfl : a = b := Subsingleton.elim _ _
    simp [R0, r, Matrix.mul_apply, Pi.single_apply, inv_mul_cancel₀ (show (β.1 *ᵥ v) i0 ≠ 0 from hi0)]
  have hS : (rat R0 : Mx D 1 ρ) ⬝ (rat β.1 : Mx D ρ ρ) ⬝ (rat V0 : Mx D ρ 1) = 1 := by
    rw [← rat_mul, ← rat_mul, hS0]
    ext a b
    obtain rfl : a = b := Subsingleton.elim _ _
    simp [rat]
  obtain ⟨x0, hx0⟩ := hψ.2.2.2
  obtain ⟨t, ht⟩ := exists_scalar (D := D) x0
  have hν : adj (rk2 (algebraMap (AF D.host.F) (AE D) t) v r) = rk2 (algebraMap (AF D.host.F) (AE D) t) v r := by
    unfold rk2
    rw [adj_smul, cA_algebraMap', adj_add, adj_mul, adj_mul, adj_adj, adj_adj, add_comm]
  refine ⟨⟨_, hν⟩, ?_, ?_⟩
  · have h := trace_val (rat β.1) (adj_rat_herm β) (rat V0) (rat R0) (algebraMap (AF D.host.F) (AE D) t) hS
    change ψ (halfTr (Matrix.trace ((rat β.1 : Mx D ρ ρ) ⬝ _))) ≠ 1
    change ψ (halfTr (Matrix.trace ((rat β.1 : Mx D ρ ρ) ⬝ (algebraMap (AF D.host.F) (AE D) t • _)))) ≠ 1
    rw [h, ht]
    exact hx0
  · intro γ u hγ x hx hW' hu
    refine cell_absorb (rat (Matrix.replicateCol (Fin 1) (zinc hn v))) (rat (Matrix.replicateRow (Fin 1) (zinc hn r)))
      (algebraMap (AF D.host.F) (AE D) t) ((rank_two_embedding_small hn _ v r).symm) γ u hu ?_
    have hv : lowerC x *ᵥ zinc hn v = 0 := by
      rw [← hW'] at hvW
      exact hvW
    have h0 : (HMul.hMul (lowerC x) (Matrix.replicateCol (Fin 1) (zinc hn v)) : Matrix (Fin n) (Fin 1) D.host.E) = 0 := by
      refine Matrix.ext fun i j => ?_
      have := congrFun hv i
      simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct] using this
    rw [hx, lowerC_map]
    change (rat (lowerC x) : Mx D n n) ⬝ (rat (Matrix.replicateCol (Fin 1) (zinc hn v)) : Mx D n 1) = 0
    rw [← rat_mul, h0]
    ext i j
    simp [rat]

end GlobalTheory.CompanionTheory.ZUnf.SmallZ
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OfE
section
noncomputable section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology Filter PositivityTheory.Rg.Base1 GroundTheory.Global
open scoped TensorProduct ENNReal NNReal Matrix Classical

namespace GlobalTheory.CompanionTheory.SW.RankOneSiegelWeil

section

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]

def Psi (φ : (Fin 1 → Fin 1 → Ainf F ⊗[F] E) → ℝ)
    (A : ∀ v : HeightOneSpectrum (𝓞 F), Set (Fin 1 → Fin 1 → Fv F v ⊗[F] E))
    (Y : Fin 1 → Fin 1 → AF F ⊗[F] E) : ℝ≥0∞ :=
  {Y : Fin 1 → Fin 1 → AF F ⊗[F] E | ∀ v, projV v (projFin Y) ∈ A v}.indicator
    (fun Y => ENNReal.ofReal (φ (projInf Y))) Y

def Th (φ : (Fin 1 → Fin 1 → Ainf F ⊗[F] E) → ℝ)
    (A : ∀ v : HeightOneSpectrum (𝓞 F), Set (Fin 1 → Fin 1 → Fv F v ⊗[F] E))
    (y : (AF F ⊗[F] E)ˣ) : ℝ≥0∞ :=
  ∑' X : ({X : Fin 1 → Fin 1 → E | X ≠ 0} : Set _),
    Psi φ A (fun a i => (y : AF F ⊗[F] E) * inclR (AF F) (X.1 a i))

def ofF : (AF F)ˣ →* (AF F ⊗[F] E)ˣ :=
  Units.map (Algebra.TensorProduct.includeLeft : AF F →ₐ[F] AF F ⊗[F] E).toMonoidHom

def ofE : Eˣ →* (AF F ⊗[F] E)ˣ := Units.map (inclR (AF F)).toMonoidHom

end

def cV {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] (v : HeightOneSpectrum (𝓞 F)) :
    AF F ⊗[F] E →ₐ[F] Fv F v ⊗[F] E :=
  (Algebra.TensorProduct.map (evalV F v) (AlgHom.id F E)).comp
    (Algebra.TensorProduct.map (sndA F) (AlgHom.id F E))

def cI {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] :
    AF F ⊗[F] E →ₐ[F] Ainf F ⊗[F] E :=
  Algebra.TensorProduct.map (fstA F) (AlgHom.id F E)

def ue {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]
    (σ : E →ₐ[F] E) (J : Matrix (Fin 1) (Fin 1) E) (h : HA R σ J) : (R ⊗[F] E)ˣ :=
  Matrix.GeneralLinearGroup.det (HA.mat R σ J h)

end GlobalTheory.CompanionTheory.SW.RankOneSiegelWeil

end
end

