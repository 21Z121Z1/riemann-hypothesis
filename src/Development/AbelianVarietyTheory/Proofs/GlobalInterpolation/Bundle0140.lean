import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.Bundle0002
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0134
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0136
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0137
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0130
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0131
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0086
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0036
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0252
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0004
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Bundle0004
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0127
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0138
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0129
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.Bundle0010
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.Bundle0012
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0321
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.FundamentalDomainNeZero
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.FrameTransport
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SumPlacesEqTrace
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0191
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0241
import Formalism.GL3MeanSquares.Bundle0001
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0009
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0001
import Formalism.SharpRestriction.InertJacobiLevels.Bundle0007
import Formalism.LocalToGlobal.GlobalTheory.IsResidueClassZero
import Formalism.SharpRestriction.GrowthBounds.SmallOrderPrimes
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Bundle0002
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Bundle0003
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.ThinScalesIffHostBound
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.LogCondLeThree
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.AuxiliaryPrimeMemAvoidedPrimes
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0117
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0115
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0113
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0124
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0120

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.AdelicUnitaryGroupHaarPropertiesProof
section
namespace GlobalTheory

theorem adelicUnitaryHaar_holds : GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryHaarMeasure.AdelicUnitaryHaar := by
  intro F E _ _ _ _ _ σ hσ M J hJ
  exact ⟨GlobalTheory.T.adelic_unitaryGroup_stabilisers_unimodular F E σ hσ M J hJ, GlobalTheory.T.archimedean_unitaryGroup_stabilisers_unimodular F E σ hσ M J hJ,
    GlobalTheory.T.finiteAdelicUnitaryGroup_stabilizers_unimodular F E σ hσ M J hJ, GlobalTheory.T.localUnitaryGroup_stabilizers_unimodular_finitePlace F E σ hσ M J hJ,
    GlobalTheory.T.unitaryRationalPoints_countable_discrete_fundDomains_cm F E σ hσ M J hJ, GlobalTheory.T.isCountableDiscreteWithFundDomains_rationalVectorStabilizer F E σ hσ M J hJ⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.AdmissibleLatticeBasisExists
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker Formalism.L2.Th1.H GlobalTheory.IndefiniteRowSideFullHecke.JetSumTable GlobalTheory.MomT

namespace GlobalTheory.HomLocBasis

open GlobalTheory.PlaceInt.LocBasis Module

theorem exists_basis_primeTo {K V : Type} [Field K] [NumberField K] [AddCommGroup V] [Module K V] [Module (𝓞 K) V]
    [IsScalarTower (𝓞 K) K V] (m : ℕ) (hm : 0 < m) (L : Submodule (𝓞 K) V) (hfg : L.FG) :
    ∃ (r : ℕ) (b : Fin r → V), LinearIndependent K b ∧ (∀ i, b i ∈ L) ∧
      ∀ w ∈ L, ∃ k : ℕ, Nat.Coprime k m ∧ k • w ∈ Submodule.span (𝓞 K) (Set.range b) := by
  first
  | exact @_root_.GlobalTheory.CoprimeBasisExistence.exists_basis_coprime
  | exact _root_.GlobalTheory.CoprimeBasisExistence.exists_basis_coprime
  | (apply _root_.GlobalTheory.CoprimeBasisExistence.exists_basis_coprime <;> assumption)
  | (intros; apply _root_.GlobalTheory.CoprimeBasisExistence.exists_basis_coprime <;> assumption)
  | (intros; apply @_root_.GlobalTheory.CoprimeBasisExistence.exists_basis_coprime <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.CoprimeBasisExistence.exists_basis_coprime ..)

open Formalism.MainNotions.TaylorLogMetric in

theorem exists_nnBasis : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (p N N' : ℕ) (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)), p.Prime → Nat.Coprime (Ideal.absNorm cc) p → TaylorLogMetric.admitted D N N' L L' → ∃ (r : ℕ) (b : Fin r → Matrix (Fin N') (Fin N) D.host.E), TaylorLogMetric.NNBasis D (TaylorLogMetric.tor0 D cc δ) δ p L L' b := by
  intro D cc δ p N N' L L' hp hcc hA
  have hL : StandardLatticesGL3.SD D L := hA.2.2.1
  have hL' : StandardLatticesGL3.SD D L' := hA.2.2.2
  obtain ⟨s, y, y', hy, hy', hexp⟩ := GlobalTheory.HomDual.exists_dual_family_hom D
    (GlobalTheory.exists_trace_dual_family_halfDifferent D) N N' L L' hL hL'
  let Y : Submodule (𝓞 D.host.K) (Matrix (Fin N') (Fin N) D.host.E) :=
    Submodule.span (𝓞 D.host.K) (Set.range y)
  have hYle : ∀ x ∈ Y, x ∈ YYl D L L' := by
    intro x hx
    obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun _).1 hx
    exact (YYl D L L').sum_mem fun i _ => GlobalTheory.ThetaConj.smul_mem_YYl D L L' (c i) (hy i)
  have hYge : ∀ x ∈ YYl D L L', x ∈ Y := by
    intro x hx
    have hi : ∀ i, ∃ t : 𝓞 D.host.K, (t : D.host.K) = hYY D x (y' i) := fun i =>
      GlobalTheory.NormSum.TraceInt.hYY_integral D N N' L L' hL hL' x hx (y' i) (hy' i)
    choose t ht using hi
    refine (Submodule.mem_span_range_iff_exists_fun _).2 ⟨t, ?_⟩
    conv_rhs => rw [hexp x]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← ht]; rfl
  obtain ⟨r, b, hli, hb, hw⟩ := exists_basis_primeTo p hp.pos Y (Submodule.fg_span (Set.finite_range y))
  set n : ℕ := Ideal.absNorm cc with hn
  have hn0 : n ≠ 0 := by
    intro h
    rw [h, Nat.coprime_zero_left] at hcc
    exact hp.one_lt.ne' hcc
  have hnK : (n : D.host.K) ≠ 0 := by exact_mod_cast hn0
  refine ⟨r, fun i => n • b i, ⟨?_, fun i => ?_, fun w hwY => ?_⟩, fun i => ?_⟩
  · have := hli.units_smul fun _ => Units.mk0 _ hnK
    have e : (fun i => n • b i) = (fun _ : Fin r => Units.mk0 _ hnK) • b := by
      funext i
      simp [Units.smul_def, Nat.cast_smul_eq_nsmul]
    rw [e]; exact this
  · refine ⟨1, by simp, ?_⟩
    rw [Nat.cast_one, one_smul]
    exact nsmul_mem (hYle _ (hb i)) n
  · obtain ⟨k, hk, hkw⟩ := hw w (hYge w hwY)
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun _).1 hkw
    refine ⟨n * k, Nat.Coprime.mul_left hcc hk, c, ?_⟩
    rw [Nat.cast_smul_eq_nsmul, mul_smul, ← hc, Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [smul_comm]; rfl
  · refine AddSubgroup.subset_closure ⟨δ * n, AddSubgroup.subset_closure ⟨(n : 𝓞 D.host.K), Ideal.absNorm_mem cc, ?_⟩,
      b i, hYle _ (hb i), ?_⟩
    · simp
    · funext τ j k
      change δ * embT D τ ((n • b i) j k) = δ * n * embT D τ (b i j k)
      rw [Matrix.smul_apply, map_nsmul, nsmul_eq_mul, mul_assoc]

end GlobalTheory.HomLocBasis
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.EqOfThetaHeisenbergTranslates
section
open NumberField IsDedekindDomain MeasureTheory Topology Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx GlobalTheory.SWQ
open scoped TensorProduct NNReal ENNReal

namespace GlobalTheory.SWQ

theorem countable_numberField (F : Type) [Field F] [NumberField F] : Countable F := by
  exact (Module.finBasis ℚ F).equivFun.injective.countable

theorem Bd_comm {F : Type} [Field F] {N : ℕ} (R : Type) [CommRing R] [Algebra F R] (a : Fin N → F)
    (u u' : Fin N → R) : Bd R a u u' = Bd R a u' u := by
  unfold Bd
  refine Finset.sum_congr rfl fun l _ => ?_
  ring

theorem continuous_Bd_left {F : Type} [Field F] [NumberField F] {N : ℕ} (a : Fin N → F)
    (u : Fin N → AF F) : Continuous fun y : Fin N → AF F => Bd (AF F) a u y := by
  unfold Bd
  exact continuous_finsetSum _ fun l _ => continuous_const.mul (continuous_apply l)

theorem integral_twisted_periodise {F : Type} [Field F] [NumberField F] {N : ℕ} {ψ : AddChar (AF F) ℂ}
    {lam : InfinitePlace F → ℝ} {ν : Measure (AF F)} {a : Fin N → F} (hC : Ctx ψ lam ν a)
    (G : (Fin N → AF F) → ℂ) (hG : Decay G) (D : Set (Fin N → AF F))
    (hD : IsAddFundamentalDomain (AddSubgroup.closure (Set.range (rat : (Fin N → F) → (Fin N → AF F))))
      D (muV N ν)) (h1 : muV N ν D = 1) (x : Fin N → AF F) :
    ∫ y in D, (∑' ξ : Fin N → F, ψ (Bd (AF F) a (rat ξ) y) * G (rat ξ + x)) ∂(muV N ν) = G x := by
  have hTR : IsTotallyReal F := hC.1
  have hψc : Continuous ψ := hC.2.1.1
  have hψn : ∀ z, ‖ψ z‖ = 1 := hC.2.1.2.1
  have : Countable F := countable_numberField F
  have : IsFiniteMeasure ((muV N ν).restrict D) :=
    ⟨by rw [Measure.restrict_apply_univ, h1]; exact ENNReal.one_lt_top⟩
  have hsum : Summable fun ξ : Fin N → F => ‖G (rat ξ + x)‖ :=
    (GlobalTheory.T.rapidDecay_adelic_integrable_periodisation_continuous F N hTR G hG).2.1 x
  have hnorm : ∀ (ξ : Fin N → F) (y : Fin N → AF F),
      ‖ψ (Bd (AF F) a (rat ξ) y) * G (rat ξ + x)‖ = ‖G (rat ξ + x)‖ := by
    intro ξ y
    rw [norm_mul, hψn, one_mul]
  have hint : ∀ ξ : Fin N → F,
      Integrable (fun y => ψ (Bd (AF F) a (rat ξ) y) * G (rat ξ + x)) ((muV N ν).restrict D) := by
    intro ξ
    refine Integrable.mono' (integrable_const ‖G (rat ξ + x)‖) ?_
      (ae_of_all _ fun y => (hnorm ξ y).le)
    exact ((hψc.comp (continuous_Bd_left a (rat ξ))).mul continuous_const).aestronglyMeasurable
  have hsum' : Summable fun ξ : Fin N → F =>
      ∫ y in D, ‖ψ (Bd (AF F) a (rat ξ) y) * G (rat ξ + x)‖ ∂(muV N ν) := by
    refine hsum.congr fun ξ => ?_
    simp_rw [hnorm]
    simp [Measure.real, h1]
  rw [← integral_tsum_of_summable_integral_norm hint hsum']
  rw [tsum_eq_single 0]
  · have hr : (rat (0 : Fin N → F) : Fin N → AF F) = 0 := by
      funext l
      simp [rat]
    simp [hr, Bd, h1, Measure.real]
  · intro ξ hξ
    rw [integral_mul_const]
    simp_rw [Bd_comm (AF F) a (rat ξ)]
    rw [GlobalTheory.T.integral_adelicVectors_character_orthogonality F N ψ lam ν a hC D hD h1 ξ hξ, zero_mul]

theorem eq_of_theta_rho : ∀ (F : Type) [Field F] [NumberField F] (N : ℕ) (ψ : AddChar (AF F) ℂ)
    (lam : InfinitePlace F → ℝ) (ν : Measure (AF F)) (a : Fin N → F), Ctx ψ lam ν a →
    ∀ G G' : (Fin N → AF F) → ℂ, Decay G → Decay G' →
      (∀ x y, th (rho ψ a x y G) = th (rho ψ a x y G')) → G = G' := by
  intro F _ _ N ψ lam ν a hC G G' hG hG' hth
  obtain ⟨D, -, hD, h1⟩ :=
    (GlobalTheory.SWQ.rat_lattice_fundamentalDomain F N ν hC.2.2.2.1).2.2.2.2
  funext x
  have key : ∀ y : Fin N → AF F,
      (∑' ξ : Fin N → F, ψ (Bd (AF F) a (rat ξ) y) * G (rat ξ + x)) =
        ∑' ξ : Fin N → F, ψ (Bd (AF F) a (rat ξ) y) * G' (rat ξ + x) := by
    intro y
    set c : AF F := algebraMap F (AF F) (1 / 2) * Bd (AF F) a x y with hc
    have hne : ψ c ≠ 0 := by
      intro h0
      have h := hC.2.1.2.1 c
      rw [h0, norm_zero] at h
      exact zero_ne_one h
    have e : ∀ H : (Fin N → AF F) → ℂ,
        th (rho ψ a x y H) = ψ c * ∑' ξ : Fin N → F, ψ (Bd (AF F) a (rat ξ) y) * H (rat ξ + x) := by
      intro H
      simp only [th, rho, AddChar.map_add_eq_mul]
      rw [← tsum_mul_left]
      congr 1
      funext ξ
      ring
    have h := hth x y
    rw [e, e] at h
    exact mul_left_cancel₀ hne h
  rw [← integral_twisted_periodise hC G hG D hD h1 x]
  simp_rw [key]
  exact integral_twisted_periodise hC G' hG' D hD h1 x

end GlobalTheory.SWQ
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsAdelicUnitaryComplementRangeStabiliserStatement
section
open NumberField MeasureTheory Matrix Topology Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice GlobalTheory.IndefiniteRowSideFullHecke.InfiniteCoordinateUnfold GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryHaarMeasure GlobalTheory.IndefiniteRowSideFullHecke.SelfDualLatticeStabilizers GlobalTheory.Mem.Vol GlobalTheory.Mem.VolExists
open scoped ENNReal TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_adelic_unitary_complement_range_stabiliser : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M M' : ℕ) (J : Matrix (Fin M) (Fin M) E) (J' : Matrix (Fin M') (Fin M') E) (B : Matrix (Fin M) (Fin M') E) (x : Fin 1 → Fin M → E), M' + 1 = M → IsHermND σ J → IsHermND σ J' → Formalism.UG.cT (σ : E →+* E) B * J * B = J' → (∀ j, hE σ J (x 0) (fun i => B i j) = 0) → hE σ J (x 0) (x 0) ≠ 0 → ∃ φ : HA (AF F) σ J' →* HA (AF F) σ J, Continuous φ ∧ Function.Injective φ ∧ φ.range = Hstab (AF F) σ J x ∧ (∀ g, FrameRel J J' B (φ g) g) ∧ ∀ g, φ g ∈ ratPts (AF F) σ J ↔ g ∈ ratPts (AF F) σ J' := by
  first | exact @GlobalTheory.StabiliserOfVector.exists_hom_range_stabiliser | exact GlobalTheory.StabiliserOfVector.exists_hom_range_stabiliser | (intros; apply GlobalTheory.StabiliserOfVector.exists_hom_range_stabiliser <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsArchimedeanExponentsAdeleCharacter
section
open NumberField IsDedekindDomain MeasureTheory Topology Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx GlobalTheory.SWQ
open scoped TensorProduct NNReal ENNReal

namespace GlobalTheory.SWQ.LamExists

theorem re_mul_of_isReal {F : Type} [Field F] [NumberField F] (hF : IsTotallyReal F) (a : F) (x : Ainf F)
    (w : InfinitePlace F) : re (algebraMap F (Ainf F) a * x) w = re (algebraMap F (Ainf F) a) w * re x w := by
  have hr : (InfinitePlace.Completion.extensionEmbedding w (algebraMap F (Ainf F) a w)).im = 0 := by
    show (InfinitePlace.Completion.extensionEmbedding w (a : w.Completion)).im = 0
    rw [InfinitePlace.Completion.extensionEmbedding_coe]
    have := InfinitePlace.isReal_iff.1 (hF.isReal w)
    exact Complex.conj_eq_iff_im.1 (RingHom.congr_fun this a)
  show (InfinitePlace.Completion.extensionEmbedding w (algebraMap F (Ainf F) a w * x w)).re = _
  rw [map_mul, Complex.mul_re, hr, zero_mul, sub_zero]
  rfl

theorem re_ne_zero {F : Type} [Field F] [NumberField F] (a : F) (ha : a ≠ 0) (w : InfinitePlace F)
    (hF : IsTotallyReal F) : re (algebraMap F (Ainf F) a) w ≠ 0 := by
  have hr : (InfinitePlace.Completion.extensionEmbedding w (algebraMap F (Ainf F) a w)).im = 0 := by
    show (InfinitePlace.Completion.extensionEmbedding w (a : w.Completion)).im = 0
    rw [InfinitePlace.Completion.extensionEmbedding_coe]
    have := InfinitePlace.isReal_iff.1 (hF.isReal w)
    exact Complex.conj_eq_iff_im.1 (RingHom.congr_fun this a)
  intro h0
  have : InfinitePlace.Completion.extensionEmbedding w (algebraMap F (Ainf F) a w) = 0 :=
    Complex.ext h0 hr
  change InfinitePlace.Completion.extensionEmbedding w (a : w.Completion) = 0 at this
  rw [InfinitePlace.Completion.extensionEmbedding_coe, map_eq_zero] at this
  exact ha this

end GlobalTheory.SWQ.LamExists

theorem GlobalTheory.SWQ.exists_isLam : ∀ (F : Type) [Field F] [NumberField F], IsTotallyReal F → ∀ ψ : AddChar (AF F) ℂ, IsCharAF F ψ → ∃ lam, IsLam ψ lam := by
  intro F _ _ hF ψ hψ
  haveI := hF
  obtain ⟨ψ₀, h₀⟩ := GlobalTheory.SnMass.Inhab.exists_isStdChar F
  obtain ⟨a, ha, h⟩ := GlobalTheory.AdeleCharTwist.exists_mul_eq F ψ₀ ψ h₀.1 hψ
  refine ⟨fun w => re (algebraMap F (Ainf F) a) w, fun w => GlobalTheory.SWQ.LamExists.re_ne_zero a ha w hF, fun x => ?_⟩
  rw [GlobalTheory.GaugeEx.CharLoc.psiInf_twist h, h₀.2.1]
  exact congrArg (fun t : ℝ => Complex.exp (2 * Real.pi * Complex.I * (t : ℂ)))
    (Finset.sum_congr rfl fun w _ => GlobalTheory.SWQ.LamExists.re_mul_of_isReal hF a x w)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsComplementFrameCompatibleStabilizerEmbeddiStatement
section
open NumberField MeasureTheory Matrix Topology Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice GlobalTheory.IndefiniteRowSideFullHecke.InfiniteCoordinateUnfold GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryHaarMeasure GlobalTheory.IndefiniteRowSideFullHecke.SelfDualLatticeStabilizers GlobalTheory.Mem.Vol GlobalTheory.Mem.VolExists
open scoped ENNReal TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_complement_frame_compatible_stabilizerEmbedding : ∀ (P Q P' Q' M M' : ℕ), P' + Q' + 1 = P + Q → M' = P' + Q' → ∀ (G : Matrix (Fin M) (Fin M) ℂ) (G' : Matrix (Fin M') (Fin M') ℂ) (B : Matrix (Fin M) (Fin M') ℂ) (x : Fin M → ℂ) (A : Matrix (Fin P ⊕ Fin Q) (Fin M) ℂ), Aᴴ * Formalism.UG.Jpq P Q * A = G → Bᴴ * G * B = G' → G'.det ≠ 0 → (Bᴴ * G) *ᵥ x = 0 → star (A *ᵥ x) ⬝ᵥ Formalism.UG.Jpq P Q *ᵥ (A *ᵥ x) ≠ 0 → ∀ j : UpqT P' Q' →* UpqT P Q, IsStabEmb (A *ᵥ x) j → ∃ A' : Matrix (Fin P' ⊕ Fin Q') (Fin M') ℂ, A'ᴴ * Formalism.UG.Jpq P' Q' * A' = G' ∧ ∀ (g : Matrix (Fin M) (Fin M) ℂ) (g' : Matrix (Fin M') (Fin M') ℂ) (t : UpqT P Q) (t' : UpqT P' Q'), g *ᵥ x = x → g * B = B * g' → UpqT.mat t * A = A * g → UpqT.mat t' * A' = A' * g' → t = j t' := by
  first | exact @GlobalTheory.StabFrameCompat.exists_compatible_frame | exact GlobalTheory.StabFrameCompat.exists_compatible_frame | (intros; apply GlobalTheory.StabFrameCompat.exists_compatible_frame <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsMeasurableRealOrbitMapOfAdelicOrbitStatement
section
open NumberField MeasureTheory Matrix Topology Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice GlobalTheory.IndefiniteRowSideFullHecke.InfiniteCoordinateUnfold GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryHaarMeasure GlobalTheory.IndefiniteRowSideFullHecke.SelfDualLatticeStabilizers GlobalTheory.Mem.Vol GlobalTheory.Mem.VolExists
open scoped ENNReal TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_measurable_realOrbitMap_of_adelicOrbit : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (I : Type) [Fintype I] (τ : I → (E →+* ℂ)), IsCMFam τ → ∀ (θ : I → (Ainf F ⊗[F] E →+* ℂ)), (∀ ρ, IsInfEmb (τ ρ) (θ ρ)) → ∀ (M P Q : ℕ) (J : Matrix (Fin M) (Fin M) E) (A : I → Matrix (Fin P ⊕ Fin Q) (Fin M) ℂ) (N : I → Matrix (Fin M) (Fin P ⊕ Fin Q) ℂ), (∀ ρ, N ρ * A ρ = 1) → (∀ ρ, A ρ * N ρ = 1) → ∀ x : Fin 1 → Fin M → E, AllSome (fun pt : (I → UpqT P Q) → (Fin 1 → Fin M → Ainf F ⊗[F] E) => ∀ g ρ, infCoord (θ ρ) (A ρ) (pt g) = UpqT.mat (g ρ)⁻¹ *ᵥ (A ρ *ᵥ fun i => τ ρ (x 0 i))) fun pt => Measurable pt ∧ (∀ g g', (∀ ρ, UpqT.mat (g ρ)⁻¹ *ᵥ (A ρ *ᵥ fun i => τ ρ (x 0 i)) = UpqT.mat (g' ρ)⁻¹ *ᵥ (A ρ *ᵥ fun i => τ ρ (x 0 i))) → pt g = pt g') ∧ ∀ (h : HA (AF F) σ J) (t : I → UpqT P Q), (∀ ρ, UpqT.mat (t ρ) * A ρ = A ρ * infMat σ J (θ ρ) h) → pt t = projInf (h⁻¹ • ratTup (F := F) (AF F) x) := by
  first | exact @GlobalTheory.RealOrbitMap.realOrbit | exact GlobalTheory.RealOrbitMap.realOrbit | (intros; apply GlobalTheory.RealOrbitMap.realOrbit <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.FinPartInvSmulMemLatHatIffStabMulLevelStatement
section
open NumberField MeasureTheory Matrix Topology Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice GlobalTheory.IndefiniteRowSideFullHecke.InfiniteCoordinateUnfold GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryHaarMeasure GlobalTheory.IndefiniteRowSideFullHecke.SelfDualLatticeStabilizers GlobalTheory.Mem.Vol GlobalTheory.Mem.VolExists
open scoped ENNReal TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finPart_inv_smul_mem_latHat_iff_stab_mul_level : StabTransitive → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → UnramifiedAtFinite F E → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ L : Submodule (𝓞 E) (Fin M → E), IsSelfDualLat σ J L → ∀ β : F, (β = 1 ∨ β = -1) → ∀ x : Fin 1 → Fin M → E, x 0 ∈ L → hE σ J (x 0) (x 0) = algebraMap F E β → ∀ h : HA (AF F) σ J, projFin (h⁻¹ • ratTup (F := F) (AF F) x) 0 ∈ latHat F E (L : Set (Fin M → E)) ↔ ∃ a ∈ Hstab (AF F) σ J x, a⁻¹ * h ∈ stab σ J (L : Set (Fin M → E)) := by
  first | exact @GlobalTheory.AdelicOrbit.mem_latHat_iff | exact GlobalTheory.AdelicOrbit.mem_latHat_iff | (intros; apply GlobalTheory.AdelicOrbit.mem_latHat_iff <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.HermitianFormAndSelfDualLatticeInFrameCoordsStatement
section
open NumberField MeasureTheory Matrix Topology Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice GlobalTheory.IndefiniteRowSideFullHecke.InfiniteCoordinateUnfold GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryHaarMeasure GlobalTheory.IndefiniteRowSideFullHecke.SelfDualLatticeStabilizers GlobalTheory.Mem.Vol GlobalTheory.Mem.VolExists
open scoped ENNReal TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermitian_form_and_selfDual_lattice_in_frame_coords : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] (cm : CMData F E) (W : HSpace E), (∀ a b : W.V, hE cm.sig W.gram (fun i => W.frame.repr a i) (fun i => W.frame.repr b i) = W.hT a b) ∧ ∃ L : Submodule (𝓞 E) (Fin W.rank → E), IsSelfDualLat cm.sig W.gram L ∧ (L : Set (Fin W.rank → E)) = latC W := by
  first | exact @GlobalTheory.FrameDict.dict | exact GlobalTheory.FrameDict.dict | (intros; apply GlobalTheory.FrameDict.dict <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.HostExOfPublished
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.GlobalTheoryTheory GlobalTheory.EX NumberField

namespace GlobalTheory.EX

theorem hostEx_of_zeroFreeRegion :
    GlobalTheory.Mem.An.ExplZeta → GlobalTheory.Mem.An.ExplChi → GlobalTheory.Mem.An.LogDerOne → GlobalTheory.Mem.An.ZeroCount → Formalism.ZeroFreeDirichlet.ZFRDirichlet → GlobalTheory.Mem.An.TZRat → GlobalTheory.Mem.An.PageThm → GlobalTheory.Mem.An.Jutila → GlobalTheory.Mem.An.QuadraticHeckeZeroEstimates → HostEx :=
  fun hZ hC hL hN hD hR hP hJ hQ =>
    GlobalTheory.T.host_existence_of_choices (GlobalTheory.EX.qdChoice_of_explicitFormula hZ hC hL hN hD hR hP hJ)
      (GlobalTheory.T.thin_choice_of_zero_density hZ hC hL hN hD) (GlobalTheory.T.norm_primes_and_level_prime hQ).1
      (GlobalTheory.EX.smallPrimeOne_of_tzRat hR) GlobalTheory.T.tops_choice

end GlobalTheory.EX
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.IsClosedEmbeddingOfIsStabilizerEmbeddingUpqStatement
section
open NumberField MeasureTheory Matrix Topology Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice GlobalTheory.IndefiniteRowSideFullHecke.InfiniteCoordinateUnfold GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryHaarMeasure GlobalTheory.IndefiniteRowSideFullHecke.SelfDualLatticeStabilizers GlobalTheory.Mem.Vol GlobalTheory.Mem.VolExists
open scoped ENNReal TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isClosedEmbedding_of_isStabilizerEmbeddingUpq : ∀ (P Q P' Q' : ℕ), P' + Q' + 1 = P + Q → ∀ (x₀ : Fin P ⊕ Fin Q → ℂ), star x₀ ⬝ᵥ Formalism.UG.Jpq P Q *ᵥ x₀ ≠ 0 → ∀ j : UpqT P' Q' →* UpqT P Q, IsStabEmb x₀ j → IsClosedEmbedding j := by
  first | exact @GlobalTheory.StabEmbClosed.isClosedEmbedding_of_isStabEmb | exact GlobalTheory.StabEmbClosed.isClosedEmbedding_of_isStabEmb | (intros; apply GlobalTheory.StabEmbClosed.isClosedEmbedding_of_isStabEmb <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.LatHatStabiliserIffComplementFrameRelStatement
section
open NumberField MeasureTheory Matrix Topology Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice GlobalTheory.IndefiniteRowSideFullHecke.InfiniteCoordinateUnfold GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryHaarMeasure GlobalTheory.IndefiniteRowSideFullHecke.SelfDualLatticeStabilizers GlobalTheory.Mem.Vol GlobalTheory.Mem.VolExists
open scoped ENNReal TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.latHat_stabiliser_iff_complement_frameRel : StabTransitive → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → UnramifiedAtFinite F E → ∀ (M M' : ℕ) (J : Matrix (Fin M) (Fin M) E) (J' : Matrix (Fin M') (Fin M') E) (B : Matrix (Fin M) (Fin M') E) (x : Fin 1 → Fin M → E), M' + 1 = M → IsHermND σ J → IsHermND σ J' → Formalism.UG.cT (σ : E →+* E) B * J * B = J' → (∀ j, hE σ J (x 0) (fun i => B i j) = 0) → hE σ J (x 0) (x 0) ≠ 0 → ∀ (L : Submodule (𝓞 E) (Fin M → E)) (L' : Set (Fin M' → E)), IsSelfDualLat σ J L → ∀ β : F, (β = 1 ∨ β = -1) → x 0 ∈ L → hE σ J (x 0) (x 0) = algebraMap F E β → (∀ y, y ∈ L' ↔ B *ᵥ y ∈ L) → ∀ (g : HA (AF F) σ J) (g' : HA (AF F) σ J'), g ∈ Hstab (AF F) σ J x → FrameRel J J' B g g' → (g ∈ stab σ J (L : Set (Fin M → E)) ↔ g' ∈ stab σ J' L') := by
  first | exact @GlobalTheory.StabFrame.stab_iff_of_frameRel | exact GlobalTheory.StabFrame.stab_iff_of_frameRel | (intros; apply GlobalTheory.StabFrame.stab_iff_of_frameRel <;> assumption)
end

