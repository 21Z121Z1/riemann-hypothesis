import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0777
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0773
import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.ThetaIdempotents.HeckeEta
import Formalism.LocalToGlobal.BesselHermitianTheta.Bundle0003
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1870
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0771
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0755
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0780
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0778
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0015
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0016
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0009
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.NotIsFinitePartOfBot
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0534
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0681
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0756
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0748
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.WeilSiegelTheta.Bundle0001
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.RegularClassTraces.RegClassFin
import Development.WeilBound.ThetaLifts.Reductions.SiegelCore
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0026
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0001
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0028
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.StandardMaximalParabolic
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CentralizerTensorForms
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ParabolicLeviDecomposition
import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.Bundle0001
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0053
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0601
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0366
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0357
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0162
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0157
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0779
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0515
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0915
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0529
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HaarImageGLScaling

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AbsValueAdelicProductFormulaStatement
section
noncomputable section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC GlobalTheory.CompanionTheory.IwaAd PositivityTheory.PfSWUS GlobalTheory.CompanionTheory.SiegelND GlobalTheory.CompanionTheory.MM
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.absValue_adelic_product_formula : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ x : (AE D)ˣ, absA D x = (∏ τ, ‖θ τ (infPart D x.1)‖₊ ^ 2) * ∏ᶠ v, absEv D.host.F D.host.E v (unitFin D.host.F D.host.E v x) := by
  first | exact @GlobalTheory.CompanionTheory.AbsProd.absA_eq_prod | exact GlobalTheory.CompanionTheory.AbsProd.absA_eq_prod | (intros; apply GlobalTheory.CompanionTheory.AbsProd.absA_eq_prod <;> assumption)
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ArchimedeanHeightDeterminantFormulaStatement
section
noncomputable section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC GlobalTheory.CompanionTheory.IwaAd PositivityTheory.PfSWUS GlobalTheory.CompanionTheory.SiegelND GlobalTheory.CompanionTheory.MM
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.archimedean_height_determinant_formula : ∀ (D : D7) (n : ℕ) (θ : InfFam D), IsInfFam θ → ∀ (a d : GL (Fin n) (AE D)) (b : hermA D n) (k₁ k₂ k₃ k₄ : Mx D n n) (τ : D.what₂.Tau), (blk4 k₁ k₂ k₃ k₄).map ((θ τ).comp (infPart D)) * ((blk4 k₁ k₂ k₃ k₄).map ((θ τ).comp (infPart D)))ᴴ = 1 → d.1 * k₃ = -1 → d.1 * k₄ = -(pull a b).1 → (1 + (((gAt θ a τ)⁻¹).1 * (PositivityTheory.SiegelWeilFormula.Gen.matInf b.1).map (θ τ) * (((gAt θ a τ)⁻¹).1)ᴴ) * (((gAt θ a τ)⁻¹).1 * (PositivityTheory.SiegelWeilFormula.Gen.matInf b.1).map (θ τ) * (((gAt θ a τ)⁻¹).1)ᴴ)).det.re = ‖θ τ (infPart D (Matrix.GeneralLinearGroup.det d).1)‖ ^ 2 := by
  first | exact @GlobalTheory.CompanionTheory.MM.RealId.det_one_add_sq | exact GlobalTheory.CompanionTheory.MM.RealId.det_one_add_sq | (intros; apply GlobalTheory.CompanionTheory.MM.RealId.det_one_add_sq <;> assumption)
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CentreCoefficientEquivariance
section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CompanionTheory.ZcShift

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1000000 in

theorem zc_shift : ∀ {D : D7} {n ρ p : ℕ} {hn : ρ + p = n} (M : Maps D hn) (m : Meas D ρ p) (ψ : AddChar (AF D.host.F) ℂ), IsCharAF D.host.F ψ → ∀ (b₀ : HermE D ρ) (F : G D n → ℂ), LeftInv (GF D n) F → ∀ (c : hermA D ρ) (h : G D n), zc M m ψ b₀ F (M.nzx c 0 * h) = chz ψ b₀ c * zc M m ψ b₀ F h := by
  intro D n ρ p hn M m ψ hψ b₀ F hF c h
  obtain ⟨hadd, hnorm, hrat, -⟩ := GlobalTheory.T.centre_character_properties ψ hψ b₀
  obtain ⟨hl, hFD, -⟩ := m.hz
  obtain ⟨i1, i2, i3, i4, -, -⟩ := GlobalTheory.TowerResNonzero.lattice_ratMx D ρ ρ
  haveI : BorelSpace (Mx D ρ ρ) := ⟨rfl⟩
  haveI : BorelSpace (hermA D ρ) := Subtype.borelSpace _
  haveI : SecondCountableTopology (hermA D ρ) := TopologicalSpace.Subtype.secondCountableTopology _
  haveI : DiscreteTopology (ratHerm D ρ) := GlobalTheory.CompanionTheory.FourierN.discrete_ratHerm
  haveI : Countable (ratHerm D ρ) := countable_of_Lindelof_of_discrete
  have hnz : ∀ z z' : hermA D ρ, M.nzx z 0 * M.nzx z' 0 = M.nzx (z + z') 0 := fun z z' => by
    have := GlobalTheory.T.unipotent_heisenberg_mul M z z' 0 0
    rwa [add_zero] at this
  have hconj : conj (chz ψ b₀ c) * chz ψ b₀ c = 1 := by
    rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq, hnorm c]
    simp
  set u : hermA D ρ → ℂ := fun z => F (M.nzx z 0 * h) * conj (chz ψ b₀ z) with hu
  have hper : ∀ γ ∈ ratHerm D ρ, ∀ x, u (γ + x) = u x := by
    intro γ hγ x
    simp only [hu]
    rw [← hnz, mul_assoc, hF _ ((GlobalTheory.T.rational_points_heisenberg_group M).2.2 γ hγ), hadd, hrat γ hγ, one_mul]
  have hpt : ∀ z : hermA D ρ, F (M.nzx z 0 * (M.nzx c 0 * h)) * conj (chz ψ b₀ z) = chz ψ b₀ c * u (z + c) := by
    intro z
    simp only [hu]
    rw [← mul_assoc, hnz, hadd, map_mul]
    linear_combination (-(F (M.nzx (z + c) 0 * h) * conj (chz ψ b₀ z))) * hconj
  unfold zc
  simp only [hpt]
  rw [integral_const_mul]
  congr 1
  exact GlobalTheory.CompanionTheory.ConstN.setIntegral_add_right (ratHerm D ρ) m.lz hFD u hper c

end GlobalTheory.CompanionTheory.ZcShift

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ChernIntegralEqIntersectionStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.Published.ArDegreeModel
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chern_integral_eq_intersection : ∀ (Y : Var ℂ) (Δ : Y.Dv) (L : LB Y.X) (r : L.ι → Y.Fnˣ) (hL : L.IsLB) (n : ℕ) (b : Fin n → L.Sec) (hb : ⨆ j, nonzeroLocus (b j) = ⊤), Presents Δ L r → (Weight.fsBasis Y.str (RingHom.id ℂ) hL b hb 1 (by simp)).chernInt Y.dim Set.univ (fun _ => 1) = ((Y.inter fun _ => Δ : ℤ) : ℝ) := by
  first | exact @GlobalTheory.CompanionTheory.ChernDegree.chernInt_fsBasis_eq_inter | exact GlobalTheory.CompanionTheory.ChernDegree.chernInt_fsBasis_eq_inter | (intros; apply GlobalTheory.CompanionTheory.ChernDegree.chernInt_fsBasis_eq_inter <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CuspFiniteVectorsHolds
section
open NumberField MeasureTheory Topology Matrix GlobalTheory.AutomorphicL2Unitary GlobalTheory.DiscreteSum GlobalTheory.OpTrace GlobalTheory.UnitaryBC GlobalTheory.DiscSpec GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL

noncomputable section

namespace GlobalTheory.CompanionTheory.CuspFinite

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ}
  {μ : Measure (GA E a)} [μ.IsHaarMeasure] [μ.IsMulRightInvariant]

theorem mem_of_stable {H : Submodule ℂ (L2 (latticeGL E a) μ)} (hH : H ≤ L2cusp μ)
    (hi : IsIrredSubrep (R (latticeGL E a) μ) H) (W : Submodule ℂ (Sm E a)) (hs : IsStable W) (h0 : W ≠ ⊥)
    (hW : ∀ φ ∈ W, IsCuspForm φ ∧ (∀ t g, φ.1 (splitCentre E a t * g) = φ.1 g) ∧
      ∃ h : MemL2Quotient (latticeGL E a) μ φ.1, h.toL2 ∈ H) (φ : Sm E a)
    (hφ : IsCuspForm φ ∧ (∀ t g, φ.1 (splitCentre E a t * g) = φ.1 g) ∧
      ∃ h : MemL2Quotient (latticeGL E a) μ φ.1, h.toL2 ∈ H) : φ ∈ W :=
  GlobalTheory.T.irreducible_smooth_module_unique E a μ H hH hi W hs h0 hW φ hφ

theorem exists_cusp_form_of_K_finite {H : Submodule ℂ (L2 (latticeGL E a) μ)} (hH : H ≤ L2cusp μ)
    (hi : IsIrredSubrep (R (latticeGL E a) μ) H) {F : L2 (latticeGL E a) μ} (hF : F ∈ H) (hk : IsKFinL2 μ F) :
    ∃ φ : Sm E a, lift (latticeGL E a) F =ᵐ[μ] φ.1 ∧ IsCuspForm φ ∧ (∀ t g, φ.1 (splitCentre E a t * g) = φ.1 g) ∧
      ∃ h : MemL2Quotient (latticeGL E a) μ φ.1, h.toL2 ∈ H := by
  obtain ⟨φ, e, hm, hl, hz, hlev, hkf, hzf⟩ := GlobalTheory.T.K_finite_L2_smooth_representative E a μ H hH hi F hF hk
  have hc : Continuous φ.1 := ContAut.continuous_of_isOpen_stab E a φ hlev
  have hFe : hm.toL2 = F := l2DiscreteQuotient_ext_iff_lift_ae_eq.2 (hm.lift_toL2_ae_eq.trans e.symm)
  have hcusp : IsCuspidal φ.1 := GlobalTheory.T.cuspidal_of_L2_cuspidal_mem E a μ φ.1 hc hl hz hm (by rw [hFe]; exact hH hF)
  exact ⟨φ, e, ⟨⟨hl, hlev, hkf, hzf, GlobalTheory.T.smooth_K_finite_center E a μ φ hl hz hlev hkf hzf hm⟩, hcusp⟩, hz, hm,
    by rw [hFe]; exact hF⟩

end GlobalTheory.CompanionTheory.CuspFinite

namespace GlobalTheory.CompanionTheory.Published

open GlobalTheory.CompanionTheory.CuspFinite in

theorem cuspFiniteVectorsGL : GlobalTheory.Published.CuspFiniteVectorsGL := by
  intro E _ _ _ a μ _ _ H hH hi
  obtain ⟨V, hV, hs⟩ := GlobalTheory.T.irreducible_cuspidal_smooth_module E a μ H hH hi
  have hkf : ∀ F ∈ H, IsKFinL2 μ F → F ∈ classes V μ := fun F hF hk => by
    obtain ⟨φ, e, h1, h2, h3⟩ := exists_cusp_form_of_K_finite hH hi hF hk
    exact ⟨φ, (hV φ).2 ⟨h1, h2, h3⟩, e⟩
  have hcl : classes V μ ≤ H := by
    rintro F ⟨φ, hφ, e⟩
    obtain ⟨-, -, h, hH'⟩ := (hV φ).1 hφ
    have : F = h.toL2 := l2DiscreteQuotient_ext_iff_lift_ae_eq.2 (e.trans h.lift_toL2_ae_eq.symm)
    exact this ▸ hH'
  have hdense : H ≤ (classes V μ).topologicalClosure :=
    (GlobalTheory.T.K_finite_vectors_dense E a μ H hi.1).trans (Submodule.topologicalClosure_mono
      (Submodule.span_le.2 fun F hF => hkf F hF.1 hF.2))
  have hne : V ≠ ⊥ := by
    intro hb
    refine hi.2.1 (eq_bot_iff.2 (hdense.trans (Submodule.topologicalClosure_minimal _ ?_ ?_)))
    · rintro F ⟨φ, hφ, e⟩
      rw [hb, Submodule.mem_bot] at hφ
      have h0 : φ.1 = 0 := by rw [hφ]; rfl
      rw [h0] at e
      exact (Submodule.mem_bot ℂ).2 (l2DiscreteQuotient_ext_iff_lift_ae_eq.2 (e.trans (show lift (latticeGL E a) (0 : L2 (latticeGL E a) μ) =ᵐ[μ] 0 from
        ae_quotMeasure_iff.1 (Lp.coeFn_zero ℂ 2 _)).symm))
    · rw [Submodule.bot_coe]
      exact isClosed_singleton
  have hirr : ∀ W ≤ V, IsStable W → W = ⊥ ∨ W = V := fun W hWV hWs => by
    by_cases h0 : W = ⊥
    · exact Or.inl h0
    · exact Or.inr (le_antisymm hWV fun φ hφ =>
        mem_of_stable hH hi W hWs h0 (fun ψ hψ => (hV ψ).1 (hWV hψ)) φ ((hV φ).1 hφ))
  let π : CuspSub E a := ⟨V, fun φ hφ => ((hV φ).1 hφ).1, hs, hne, hirr⟩
  exact ⟨π, fun φ hφ => ((hV φ).1 hφ).2.1, fun φ hφ => ((hV φ).1 hφ).2.2.1,
    le_antisymm (Submodule.topologicalClosure_minimal _ hcl hi.1.1) hdense, hkf⟩

end GlobalTheory.CompanionTheory.Published

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EisensteinThetaInvarianceStatement
section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.EC
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eisenstein_theta_invariance : PositivityTheory.GramSchwartzFunctions.EC.ThetaInv := by
  first | exact @GlobalTheory.CompanionTheory.EisCellsTheta.thetaInv | exact GlobalTheory.CompanionTheory.EisCellsTheta.thetaInv | (intros; apply GlobalTheory.CompanionTheory.EisCellsTheta.thetaInv <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EllipticTraceFromLocalInputs
section
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Chamber GlobalTheory.TruncKer GlobalTheory.Cusp

noncomputable section
namespace GlobalTheory.CompanionTheory.EllTrace
open GlobalTheory.TruncKer

theorem countable_GF {D : D7} (V : HSp D) : Countable (GF V) := by
  haveI : Countable D.host.E :=
    (Module.finBasis ℚ D.host.E).equivFun.injective.countable
  haveI : Countable (Matrix (Fin V.rank) (Fin V.rank) D.host.E) :=
    (show Countable (Fin V.rank → Fin V.rank → D.host.E) from inferInstance)
  haveI : Countable (GL (Fin V.rank) D.host.E) := Units.val_injective.countable
  infer_instance

theorem kernel_diag_hasSum {D : D7} (V : HSp D) {f : GA D V → ℂ} (hf : f ∈ CcGA V) (x : GA D V) :
    (Function.support fun δ : GF V => f (x⁻¹ * rat V δ * x)).Finite ∧
    HasSum (fun δ : GF V => f (x⁻¹ * rat V δ * x)) (GlobalTheory.AutomorphicL2Unitary.kernel (GQ V) f x x) := by
  have hcs := continuous_of_mem_ccAd hf
  have hr : (ratEmb D.sp.cm.sig V.gram).range = GQ V := by rw [range_ratEmb]; rfl
  let e : GF V ≃* GQ V :=
    (MonoidHom.ofInjective (ratEmb_injective D.sp.cm.sig V.gram)).trans (MulEquiv.subgroupCongr hr)
  have he : ∀ δ : GF V, ((e δ : GQ V) : GA D V) = rat V δ := fun δ => rfl
  refine ⟨?_, ?_⟩
  · have hC : IsCompact ((fun g : GA D V => x * g * x⁻¹) '' tsupport f) :=
      hcs.2.isCompact.image (by fun_prop)
    have hfin := finite_mem_compact (Γ := GQ V) hC
    refine (hfin.preimage e.injective.injOn).subset fun δ hδ => ?_
    refine ⟨x⁻¹ * rat V δ * x, subset_tsupport _ hδ, ?_⟩
    simp only [he]
    group
  · have := hasSum_kernel (Γ := GQ V) hcs.2 x x
    exact (e.toEquiv.hasSum_iff (f := fun γ : GQ V => f (x⁻¹ * (γ : GA D V) * x))).2 this

theorem charpoly_eq_of_isConj {D : D7} {V : HSp D} {a b : GF V} (h : IsConj a b) :
    a.1.1.charpoly = b.1.1.charpoly := by
  obtain ⟨c, rfl⟩ := isConj_iff.1 h
  change a.1.1.charpoly = ((c.1 : GL _ _) * a.1 * (c.1)⁻¹ : GL _ _).1.charpoly
  rw [Units.val_mul, Units.val_mul, Matrix.coe_units_inv, Matrix.charpoly_units_conj]

theorem ellTrace_of_middle : MainStatements.RegularCuspidalTrace.RegClassInt → MainStatements.RegularCuspidalTrace.RegClassFin → (∀ (D : D7) (V : HSp D) (μ : Measure (GA D V)) [μ.IsHaarMeasure] [μ.IsMulRightInvariant], GlobalTheory.IndefiniteRowSideFullHecke.CuspidalNoRadicalFixed.CuspidalOperators V μ) → GlobalTheory.IndefiniteRowSideFullHecke.ConstantTermVanishing.ParabolicAndConstTerm → GlobalTheory.IndefiniteRowSideFullHecke.IwahoriSubgroup.IwahoriEigenvalues → GlobalTheory.IndefiniteRowSideFullHecke.CentralizerTensorForms.RegularSemisimple → GlobalTheory.IndefiniteRowSideFullHecke.NonFieldTypeVanishingAlt.NonFieldTypeVanishing → HyperZero → EllTrace := by
  intro hInt hFinC hCO hPC hIw _hRS hNF hHZ D V lam S M T U μa μf μ _ _ fa ff hT
  have hT' := hT
  obtain ⟨hodd, -, -, hnf, hμ, harch, hfin⟩ := hT'
  have hμ' := hμ
  obtain ⟨hμa, hμf, -, -⟩ := hμ'
  set f := tensor D.sp.cm.sig V.gram fa ff with hfdef
  have hcc : f ∈ CcGA V := tensor_mem_ccAd harch.mem hfin.isFinFamily
  have hcs := continuous_of_mem_ccAd hcc
  obtain ⟨hH, -⟩ := GlobalTheory.T.typeHypothesis_forms_agree D V T hnf
  haveI := hμa
  haveI := hμf
  have hconst := hPC.2 D V hodd S M T hH U μa μf f ⟨fa, ff, harch, hfin, rfl⟩
  have hcusp : GlobalTheory.IndefiniteRowSideFullHecke.CuspidalNoRadicalFixed.IsCuspidalOp V μ f :=
    hCO D V μ f hcc (fun 𝔉 h𝔉 ν hν x y => ((hconst 𝔉 h𝔉).1 ν x y).2)
      (fun 𝔉 h𝔉 ν hν x y => ((hconst 𝔉 h𝔉).2 ν x y).2)
  have hcuspFn : MainStatements.RegularCuspidalTrace.IsCuspFn f := fun 𝔉 h => (hconst 𝔉 h).1
  refine ⟨hcusp.traceClass, ?_⟩
  rw [hcusp.trace_eq_integral]
  haveI : Countable (GF V) := countable_GF V
  let ι := {𝔬 : Set (GF V) // ∃ γ : GF V, IsRegSS γ.1.1 ∧ 𝔬 = {δ | IsConj γ δ}}
  haveI : Countable ι := by
    have hs : Function.Surjective
        (fun γ : {γ : GF V // IsRegSS γ.1.1} => (⟨{δ | IsConj γ.1 δ}, γ.1, γ.2, rfl⟩ : ι)) := by
      rintro ⟨_, γ, hγ, rfl⟩
      exact ⟨⟨γ, hγ⟩, rfl⟩
    exact hs.countable
  let k : ι → GlobalTheory.AutomorphicL2Unitary.Quot (GQ V) → ℂ := fun i =>
    GlobalTheory.AutomorphicL2Unitary.descend (GQ V) (fun x => ∑' δ : i.1, f (x⁻¹ * rat V δ * x))
  have hkint : ∀ i : ι, Integrable (k i) (autMeasure V μ) := by
    rintro ⟨_, γ, hγ, rfl⟩
    obtain ⟨hcl, -⟩ := (GlobalTheory.T.regularSemisimple_rational_class_kernel_integrals D V γ hγ).2 f
    have := hInt D V μ f hcc hcuspFn γ hγ
    rw [show GlobalTheory.IndefiniteRowSideFullHecke.NonFieldTypeVanishingAlt.classKernel (GQ V) (rat V γ) f = fun x => ∑' δ : {δ | IsConj γ δ}, f (x⁻¹ * rat V δ * x)
      from funext hcl] at this
    exact this
  have hreg : ∀ (δ : GF V) (x : GA D V), f (x⁻¹ * rat V δ * x) ≠ 0 → IsRegSS δ.1.1 :=
    fun δ x h => GlobalTheory.T.isRegularSemisimple_of_testFunction_ne_zero hIw D V T U μf ff hfin fa δ x h
  have hPc : ∀ a b : GF V, IsConj a b → Irreducible a.1.1.charpoly → Irreducible b.1.1.charpoly :=
    fun a b h ha => charpoly_eq_of_isConj h ▸ ha
  refine GlobalTheory.T.integral_hasSum_eq_integral_indicator_hasSum' (autMeasure V μ) k hkint ?_
    {i : ι | ∀ δ ∈ i.1, Irreducible δ.1.1.charpoly} _ _ (fun q => ?_) (fun q => ?_) ?_
  · refine ((hFinC D V f hcc).preimage Subtype.val_injective.injOn).subset fun i hi => ⟨i.2, ?_⟩
    by_contra hno
    apply hi
    have hz : ∀ q, k i q = 0 := by
      intro q
      change (∑' δ : i.1, f (q.out⁻¹ * rat V δ * q.out)) = 0
      have : ∀ δ : i.1, f (q.out⁻¹ * rat V δ * q.out) = 0 := fun δ => by
        by_contra h
        exact hno ⟨q.out, δ.1, δ.2, h⟩
      simp [this]
    simp [hz]
  · obtain ⟨hsupp, hsum⟩ := kernel_diag_hasSum V hcc q.out
    have := (GlobalTheory.T.hasSum_conjClasses_regroup_with_invariant_selection _ hsupp (fun δ => IsRegSS δ.1.1) (fun δ => Irreducible δ.1.1.charpoly)
      (fun δ h => hreg δ _ h) hPc).1
    rw [hsum.tsum_eq] at this
    exact this
  · obtain ⟨hsupp, -⟩ := kernel_diag_hasSum V hcc q.out
    have := (GlobalTheory.T.hasSum_conjClasses_regroup_with_invariant_selection _ hsupp (fun δ => IsRegSS δ.1.1) (fun δ => Irreducible δ.1.1.charpoly)
      (fun δ h => hreg δ _ h) hPc).2
    have hfs : (Function.support fun δ : {δ : GF V // Irreducible δ.1.1.charpoly} =>
        f (q.out⁻¹ * rat V δ.1 * q.out)).Finite :=
      (hsupp.preimage Subtype.val_injective.injOn).subset fun δ hδ => hδ
    have e : GlobalTheory.AutomorphicL2Unitary.descend (GQ V) (ellKernel V f) q =
        ∑' δ : {δ : GF V // Irreducible δ.1.1.charpoly}, f (q.out⁻¹ * rat V δ.1 * q.out) := by
      change ellKernel V f q.out = _
      rw [ellKernel, tsum_eq_finsum hfs]
    rw [e]
    exact this
  · rintro ⟨_, γ, hγ, rfl⟩ hi
    have hirr : ¬ Irreducible γ.1.1.charpoly := fun h =>
      hi fun δ hδ => hPc γ δ hδ h
    have hZ : GlobalTheory.IndefiniteRowSideFullHecke.NonFieldTypeVanishingAlt.ZeroClause μ f (ratEmb D.sp.cm.sig V.gram γ) := by
      by_cases hA : GlobalTheory.IndefiniteRowSideFullHecke.NonFieldTypeVanishingAlt.IsNonFieldAniso D.sp.cm.sig V.gram γ.1.1
      · exact hNF.zero hodd hH hμ ⟨fa, ff, harch, hfin, rfl⟩ hA
      · exact hHZ D V lam S M T U μa μf μ fa ff hT γ hγ hirr hA
    obtain ⟨hcl, hiff⟩ := (GlobalTheory.T.regularSemisimple_rational_class_kernel_integrals D V γ hγ).2 f
    have := ((hiff hcs.1 hcs.2 μ 0).1 hZ).2
    rw [show GlobalTheory.IndefiniteRowSideFullHecke.NonFieldTypeVanishingAlt.classKernel (GQ V) (rat V γ) f = fun x => ∑' δ : {δ | IsConj γ δ}, f (x⁻¹ * rat V δ * x)
      from funext hcl] at this
    exact this

end GlobalTheory.CompanionTheory.EllTrace
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FrameIntegralEqThetaPartNondegenerateStatement
section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC GlobalTheory.CompanionTheory.SiegelND
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.frame_integral_eq_theta_part_nondegenerate : ∀ (D : D7) (r : ℕ) (V : HSp D) (θ : InfFam D), IsInfFam θ → ∀ ν : Measure (GA D V), ν.IsHaarMeasure →
  ∀ φ : Mx D V.rank r → ℂ, φ ∈ schwartzA θ V.rank r → GlobalTheory.SiegelFormula.absThetaInt V ν φ < ⊤ →
  ∀ (μH : Measure (GA D V)) (𝓕 : Set (GA D V)), μH.IsHaarMeasure → IsFundamentalDomain (GQ V) 𝓕 μH →
  ∀ β : HermE D r, β.1.det ≠ 0 → IfrB V ν φ β = thetaPartD V μH 𝓕 φ β := by
  first | exact @GlobalTheory.CompanionTheory.SiegelND.ThetaGlue.ifrB_eq_thetaPartD | exact GlobalTheory.CompanionTheory.SiegelND.ThetaGlue.ifrB_eq_thetaPartD | (intros; apply GlobalTheory.CompanionTheory.SiegelND.ThetaGlue.ifrB_eq_thetaPartD <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FrameIntegralThetaMeasureFormulaStatement
section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.CompanionTheory.WeilSiegel.Frame
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.frame_integral_theta_measure_formula : ∀ (D : D7) (r : ℕ) (V : HSp D) (θ : InfFam D), IsInfFam θ → ∀ (ν : Measure (GA D V)), ν.IsHaarMeasure → ∀ 𝓕 : Set (GA D V), IsFundamentalDomain (GQ V) 𝓕 ν → ∀ φ : Mx D V.rank r → ℂ, φ ∈ schwartzA θ V.rank r → GlobalTheory.SiegelFormula.absThetaInt V ν φ < ⊤ → ∀ β : HermE D r, Integrable (fun X => φ (trM X)) (GlobalTheory.CompanionTheory.SW.thetaMeas D.sp.cm.sig V.gram ν 𝓕 (framesE D.sp.cm.sig V.gram β.1)) ∧ IfrB V ν φ β = ∫ X, φ (trM X) ∂(GlobalTheory.CompanionTheory.SW.thetaMeas D.sp.cm.sig V.gram ν 𝓕 (framesE D.sp.cm.sig V.gram β.1)) := by
  first | exact @GlobalTheory.CompanionTheory.WeilSiegel.Frame.glue | exact GlobalTheory.CompanionTheory.WeilSiegel.Frame.glue | (intros; apply GlobalTheory.CompanionTheory.WeilSiegel.Frame.glue <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HaarImageGLScalingStatement
section
noncomputable section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC GlobalTheory.CompanionTheory.IwaAd PositivityTheory.PfSWUS GlobalTheory.CompanionTheory.SiegelND GlobalTheory.CompanionTheory.MM
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.haar_image_GL_scaling : ∀ (D : D7) (n : ℕ) (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers D.host.F)) (lam : Measure (Fin n → HeckeCharacterZeroLocus.SiegelWeilU.Fv D.host.F v ⊗[D.host.F] D.host.E)), lam.IsAddHaarMeasure → ∀ (g : GL (Fin n) (HeckeCharacterZeroLocus.SiegelWeilU.Fv D.host.F v ⊗[D.host.F] D.host.E)) (S : Set (Fin n → HeckeCharacterZeroLocus.SiegelWeilU.Fv D.host.F v ⊗[D.host.F] D.host.E)), lam ((fun x => g.1.mulVec x) '' S) = (absEv D.host.F D.host.E v (Matrix.GeneralLinearGroup.det g) : ℝ≥0∞) * lam S := by
  first | exact @GlobalTheory.CompanionTheory.LocalModule.haar_mulVec_image_host | exact GlobalTheory.CompanionTheory.LocalModule.haar_mulVec_image_host | (intros; apply GlobalTheory.CompanionTheory.LocalModule.haar_mulVec_image_host <;> assumption)
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HeisenbergCharacterIntegralVanishes
section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CompanionTheory.FJE

variable {D : D7} {ρ p : ℕ}

open scoped Pointwise

theorem trace_single_mul_eq {R : Type} [CommRing R] {a b : ℕ} (j : Fin a) (i : Fin b) (w : R)
    (M : Matrix (Fin b) (Fin a) R) : Matrix.trace (Matrix.single j i w * M) = w * M i j := by
  simp [Matrix.trace, Matrix.mul_apply, Matrix.single_apply, ite_and, Finset.sum_ite_eq, Finset.sum_ite_eq']

theorem trA_algebraMap_half [Nontrivial (AF D.host.F)] (t : AF D.host.F) :
    trA (D := D) (algebraMap (AF D.host.F) (AE D) (algebraMap D.host.F (AF D.host.F) (1 / 2) * t)) = t := by
  have h2 : Module.finrank D.host.F D.host.E = 2 := Algebra.IsQuadraticExtension.finrank_eq_two _ _
  show Algebra.trace (AF D.host.F) (AE D) (algebraMap (AF D.host.F) (AE D)
    (algebraMap D.host.F (AF D.host.F) (1 / 2) * t)) = t
  rw [Algebra.trace_algebraMap, Module.finrank_baseChange, h2, two_nsmul, ← add_mul, ← map_add]
  norm_num

theorem exists_chv_ne_one (ψ : AddChar (AF D.host.F) ℂ) (hψ : IsCharAF D.host.F ψ) (b₀ : HermE D ρ)
    (hdet : b₀.1.det ≠ 0) (ζ : Matrix (Fin ρ) (Fin p) D.host.E) (hζ : ζ ≠ 0) :
    ∃ x₀ : Mx D ρ p, chv ψ b₀ x₀ (rt ζ) ≠ 1 := by
  obtain ⟨-, -, -, t, ht⟩ := hψ
  have hB : b₀.1 * ζ ≠ 0 := by
    intro h0
    apply hζ
    have hu : IsUnit b₀.1.det := isUnit_iff_ne_zero.2 hdet
    calc ζ = b₀.1⁻¹ * (b₀.1 * ζ) := by
          rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hu, Matrix.one_mul]
      _ = 0 := by rw [h0, Matrix.mul_zero]
  obtain ⟨i, j, hij⟩ : ∃ i j, (b₀.1 * ζ) i j ≠ 0 := by
    by_contra hc
    push_neg at hc
    exact hB (Matrix.ext hc)
  obtain ⟨c, hc⟩ : ∃ c : AE D, c = algebraMap (AF D.host.F) (AE D)
      (algebraMap D.host.F (AF D.host.F) (1 / 2) * t) * incA D ((b₀.1 * ζ) i j)⁻¹ := ⟨_, rfl⟩
  refine ⟨adj (Matrix.single j i c), ?_⟩
  have key : Matrix.trace (pr b₀ (adj (Matrix.single j i c)) (rt ζ)) =
      algebraMap (AF D.host.F) (AE D) (algebraMap D.host.F (AF D.host.F) (1 / 2) * t) := by
    show Matrix.trace (adj (adj (Matrix.single j i c)) ⬝ (b₀.1.map (incA D) ⬝ rt ζ)) = _
    rw [adj_adj, show b₀.1.map (incA D) ⬝ rt ζ = rat (b₀.1 * ζ) from (rat_mul _ _).symm,
      trace_single_mul_eq]
    show c * incA D ((b₀.1 * ζ) i j) = _
    rw [hc, mul_assoc, ← map_mul, inv_mul_cancel₀ hij, map_one, mul_one]
  show ψ (trA (Matrix.trace (pr b₀ _ (rt ζ)))) ≠ 1
  haveI : Nontrivial (AF D.host.F) :=
    nontrivial_of_ne t 0 (fun h => ht (by rw [h, AddChar.map_zero_eq_one]))
  rw [key, trA_algebraMap_half]
  exact ht

theorem integral_chv_rt_eq_zero {D : D7} {ρ p : ℕ} (m : Meas D ρ p) (ψ : AddChar (AF D.host.F) ℂ)
    (hψ : IsCharAF D.host.F ψ) (b₀ : HermE D ρ) (hdet : b₀.1.det ≠ 0)
    (ζ : Matrix (Fin ρ) (Fin p) D.host.E) (hζ : ζ ≠ 0) :
    ∫ x in m.𝓕, chv ψ b₀ x (rt ζ) ∂m.μ = 0 := by
  obtain ⟨x₀, hx₀⟩ := exists_chv_ne_one ψ hψ b₀ hdet ζ hζ
  obtain ⟨hadd, -, -, -, hrat, -⟩ := GlobalTheory.T.heisenberg_character_bilinear_laws ψ hψ b₀
  have hper : ∀ γ ∈ ratMx D ρ p, ∀ a, chv ψ b₀ (γ + a) (rt ζ) = chv ψ b₀ a (rt ζ) := by
    intro γ hγ a
    obtain ⟨g, rfl⟩ := mem_ratMx.1 hγ
    rw [hadd, show rat g = rt g from rfl, hrat, one_mul]
  have h := covolOne_integral_add m.hμ (fun x => chv ψ b₀ x (rt ζ)) hper x₀
  simp only [hadd] at h
  rw [MeasureTheory.integral_mul_const] at h
  have h2 : (∫ x in m.𝓕, chv ψ b₀ x (rt ζ) ∂m.μ) * (chv ψ b₀ x₀ (rt ζ) - 1) = 0 := by
    rw [mul_sub, mul_one, h, sub_self]
  exact (mul_eq_zero.1 h2).resolve_right (sub_ne_zero.2 hx₀)

end GlobalTheory.CompanionTheory.FJE
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LatticeImageLowerBlocksStatement
section
noncomputable section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC GlobalTheory.CompanionTheory.IwaAd PositivityTheory.PfSWUS GlobalTheory.CompanionTheory.SiegelND GlobalTheory.CompanionTheory.MM
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lattice_image_lower_blocks : ∀ (D : D7) (n : ℕ) (k : G D n) (k₁ k₂ k₃ k₄ : Mx D n n), k ∈ K D n → mat k = blk4 k₁ k₂ k₃ k₄ → ∀ v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers D.host.F), {x | ∃ y ∈ (latLoc D.host.F (stdLattice D.host.E n) v), ∃ y' ∈ (latLoc D.host.F (stdLattice D.host.E n) v), x = (PositivityTheory.SiegelWeilFormula.Gen.matV v k₃).mulVec y + (PositivityTheory.SiegelWeilFormula.Gen.matV v k₄).mulVec y'} = ((latLoc D.host.F (stdLattice D.host.E n) v) : Set (Fin n → HeckeCharacterZeroLocus.SiegelWeilU.Fv D.host.F v ⊗[D.host.F] D.host.E)) := by
  first | exact @GlobalTheory.CompanionTheory.MM.LowerRows.lowerRows_onto | exact GlobalTheory.CompanionTheory.MM.LowerRows.lowerRows_onto | (intros; apply GlobalTheory.CompanionTheory.MM.LowerRows.lowerRows_onto <;> assumption)
end
end

