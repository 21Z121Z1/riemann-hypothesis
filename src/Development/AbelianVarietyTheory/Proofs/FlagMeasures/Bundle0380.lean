import Mathlib
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.Bundle0001
import Development.AbelianVarietyTheory.BlockTheory.SiegelWeilLocal.Bundle0002
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0116
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0016
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0152
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0356
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0377
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0210
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0140
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0177
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0004
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0222
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0251
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0118
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0194
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0302
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0009
import Formalism.FormalDegreeBessel.Bundle0002
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0359
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0173
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0175
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0214
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0181
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FlagClassMeasureBoundLatticeStabiliser
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0010
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0378
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.Measures
import Formalism.HermitianLattices.Bundle0003
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.SiegelMassRatioOfLI
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.LiStatOf
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0132

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.DefiniteUnitaryGroupCountEqMainTerm
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec
open scoped InnerProductSpace ContDiff

namespace GlobalTheory.Dec

theorem GFset_eq_one_of_place (I : AutInst) (γ : I.GA) (hγ : γ ∈ I.GFset) (v : InfinitePlace I.F)
    (h : uMat (γ.1 v) = 1) : γ = 1 := by
  obtain ⟨g, -, hinf, hfin⟩ := hγ
  have hdet : ∀ w, IsUnit (I.P w).det := fun w => (Matrix.isUnit_iff_isUnit_det _).mp (I.P_unit w)
  set M : Matrix (Fin I.n) (Fin I.n) I.E := (g : Matrix (Fin I.n) (Fin I.n) I.E) with hM
  have e1 : (I.P v)⁻¹ * M.map (I.φ v) * I.P v = 1 := (hinf v).symm.trans h
  have e2 : M.map (I.φ v) * I.P v = I.P v := by
    have := congrArg (I.P v * ·) e1
    simpa [Matrix.mul_assoc, Matrix.mul_nonsing_inv_cancel_left _ _ (hdet v)] using this
  have e3 : M.map (I.φ v) = 1 := by
    have := congrArg (· * (I.P v)⁻¹) e2
    simpa [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ (hdet v)] using this
  have hg : M = 1 := by
    apply Matrix.map_injective (I.φ v).injective
    dsimp only
    rw [e3, Matrix.map_one _ (map_zero _) (map_one _)]
  refine Prod.ext (funext fun w => ?_) ?_
  · have hw : uMat (γ.1 w) = 1 := by
      rw [hinf w, hg, Matrix.map_one _ (map_zero _) (map_one _), Matrix.mul_one,
        Matrix.nonsing_inv_mul _ (hdet w)]
    exact Subtype.ext (Units.ext (by simpa using hw))
  · have hf : I.fmat γ.2 = 1 := by
      rw [hfin, hg, Matrix.map_one _ (map_zero _) (map_one _)]
    exact Subtype.ext (Units.ext (by simpa using hf))

theorem one_mem_GFset_def (I : AutInst) : (1 : I.GA) ∈ I.GFset := by
  refine ⟨1, Subgroup.one_mem _, fun v => ?_, ?_⟩
  · rw [Units.val_one, Matrix.map_one _ (map_zero _) (map_one _), Matrix.mul_one,
      Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).mp (I.P_unit v))]
    rfl
  · rw [Units.val_one, Matrix.map_one _ (map_zero _) (map_one _)]
    rfl

theorem definite_count_of_finite : ∀ (B : RowsAut) (d : InfinitePlace B.I.F → ℝ) (p : ℕ),
    GlobalTheory.IndefiniteRowSideFullHecke.DefiniteFiniteCount.DefiniteHyp B d p → FiniteDimensional ℂ (B.I.eHom B.σs B.μf B.fund B.R B.Re) →
      (B.D : ℝ) = mainTerm B d := by
  intro B d p hH hfin
  have hn : B.I.n = p := hH.rank_eq
  obtain ⟨hDS, hSig, hp, -, hprime, hgt, hsplit⟩ := hH
  have hn1 : 1 ≤ B.I.n := hn ▸ hp

  have hq : ∀ v, (univ.filter fun a => B.I.ε v a = false).card = 0 := fun v => (hSig v).2
  have hrk : ∀ v, rkR (B.I.ε v) = 0 := fun v => by
    unfold rkR
    rw [hq v]
    exact Nat.min_zero _
  have hpos : ∀ v a, B.I.ε v a = true := fun v a => by
    by_contra hne
    have ha : a ∈ univ.filter fun a => B.I.ε v a = false := by simpa using hne
    rw [Finset.card_eq_zero.mp (hq v)] at ha
    exact Finset.notMem_empty a ha
  have hJ : ∀ v, Formalism.REAL.Jm (B.I.ε v) = 1 := fun v => by
    unfold Formalism.REAL.Jm
    simp [hpos v]
  have hunit : ∀ v (g : Formalism.REAL.UJ (B.I.ε v)), (uMat g)ᴴ * uMat g = 1 := fun v g => by
    have h0 : (uMat g)ᴴ * Formalism.REAL.Jm (B.I.ε v) * uMat g = Formalism.REAL.Jm (B.I.ε v) := g.2
    rwa [hJ v, Matrix.mul_one] at h0
  have hdHS : ∀ v (g : Formalism.REAL.UJ (B.I.ε v)), dHS (uMat g) = 0 := fun v g =>
    (GlobalTheory.T.logSingularValuesEuclidNorm_cartan_properties B.I.n (B.I.ε v)).2.2.2 (hrk v) g

  have hrad := GlobalTheory.T.isRadical_span_prime_of_ncard_primesOver_eq_finrank B.I.E B.g₀ hprime hsplit
  have hNU := (GlobalTheory.NearElement.near_unipotent B d (1 / 10 ^ 5) (by norm_num) le_rfl hn1 hgt hrad _ _
    rfl rfl).1
  have hkey : ∀ x γ : B.I.GA, γ ∈ B.I.GFset → phe B d (x⁻¹ * γ * x) ≠ 0 → γ = 1 := by
    intro x γ hγ hne
    have hep : (0 : ℝ) ≤ 1 / 10 ^ 5 / ((B.I.n : ℝ) ^ 8 * (B.I.f : ℝ) ^ 2) := by positivity
    obtain ⟨-, hu, -⟩ := hNU x γ ⟨hγ, hne, fun v => by rw [hdHS]; exact hep⟩
    obtain ⟨v⟩ : Nonempty (InfinitePlace B.I.F) := inferInstance
    apply GFset_eq_one_of_place B.I γ hγ v
    apply GlobalTheory.unipotent_isometry_definite_eq_one B.I.n B.I.n _ 1 one_ne_zero _ (hu v)
    simpa using hunit v (γ.1 v)

  have hker : ∀ x, kern B.I (phe B d) x x = phe B d 1 := by
    intro x
    unfold kern
    rw [tsum_eq_single (⟨1, one_mem_GFset_def B.I⟩ : B.I.GFset)]
    · simp
    · intro γ hγ
      by_contra hne
      exact hγ (Subtype.ext (hkey x γ.1 γ.2 hne))
  have hph1 : ph B d 1 = ((∏ v, d v : ℝ) : ℂ) := by
    unfold ph
    have hc : ∀ v, ⟪B.w v, B.σ v (uMat ((1 : B.I.Ginf) v)) (B.w v)⟫_ℂ = 1 := by
      intro v
      have hs : B.σ v (uMat ((1 : B.I.Ginf) v)) = 1 := by
        rw [show uMat ((1 : B.I.Ginf) v) = 1 from rfl]
        exact (hDS v).2.1.2.2.1.1.1
      rw [hs, ContinuousLinearMap.one_apply, inner_self_eq_norm_sq_to_K, (hDS v).2.2.1.1]
      simp
    rw [Finset.prod_congr rfl (fun v _ => hc v)]
    simp

  have hloc : LocDec B 0 := by
    intro v g
    have hd : decE (rkR (B.I.ε v)) 0 (dOp (uMat g)) = 1 := by simp [decE]
    rw [hd]
    calc ‖⟪B.w v, B.σ v (uMat g) (B.w v)⟫_ℂ‖ ≤ ‖B.w v‖ * ‖B.σ v (uMat g) (B.w v)‖ :=
          norm_inner_le_norm _ _
      _ = 1 := by rw [(hDS v).2.1.2.2.1.2.1 _ g.2 _, (hDS v).2.2.1.1]; norm_num
  have hbig : HBig B 32 0 := by
    intro v
    rw [hrk v]
    simp
  obtain ⟨hcont, hbd, hmaj⟩ := GlobalTheory.T.discrete_series_coefficient_integrable_majorant B d 0 hDS hloc
  have hm := hmaj 0 le_rfl (fun v => Or.inl (hrk v))
  simp only [zero_mul, Real.exp_zero, mul_one] at hm
  have hint : Integrable (ph B d) (muInf B.I) :=
    hm.mono' hcont.aestronglyMeasurable (Filter.Eventually.of_forall hbd)
  obtain ⟨T, hT⟩ := (GlobalTheory.T.globalConvolutionOrthogonalProjector_proof B d hDS hint).2.2.1
  obtain ⟨-, -, -, -, -, -, -, hD, -⟩ := GlobalTheory.T.kernelB' B d 0 hDS hn1 hloc hbig hfin T hT
  simp_rw [hker] at hD
  rw [setIntegral_const] at hD
  have hphe : phe B d 1 = ((∏ v, d v : ℝ) : ℂ) * B.e 1 := by
    show ph B d (1 : B.I.GA).1 * B.e (1 : B.I.GA).2 = _
    rw [Prod.fst_one, Prod.snd_one, hph1]
  rw [hphe] at hD
  have he1 := (GlobalTheory.rowsAut_idem_elementary B).1
  have hre := congrArg Complex.re hD
  simp only [Complex.real_smul, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, he1,
    mul_zero, sub_zero, zero_mul, Complex.natCast_re] at hre
  unfold mainTerm AutInst.Dstar AutInst.vol
  rw [← hre, measureReal_def]
  ring

end GlobalTheory.Dec
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsContinuousBesselMapSmoothVectors
section
open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf
open scoped InnerProductSpace

namespace GlobalTheory.SgInf.BesselExt

variable {k r : ℕ}

theorem one_memG : (1 : Mat k r) ∈ GG k r := by
  show (1 : Mat k r)ᴴ * Hpk k r * 1 = Hpk k r
  simp

theorem mul_memG {x y : Mat k r} (hx : x ∈ GG k r) (hy : y ∈ GG k r) : x * y ∈ GG k r := by
  show (x * y)ᴴ * Hpk k r * (x * y) = Hpk k r
  have hx' : xᴴ * Hpk k r * x = Hpk k r := hx
  have hy' : yᴴ * Hpk k r * y = Hpk k r := hy
  calc (x * y)ᴴ * Hpk k r * (x * y) = yᴴ * (xᴴ * Hpk k r * x) * y := by
        rw [Matrix.conjTranspose_mul]; simp only [Matrix.mul_assoc]
    _ = Hpk k r := by rw [hx', hy']

section Sm
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem smooth_add {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {σ : Mat k r → (H →L[ℂ] H)} {u u' : H} (hu : IsSmoothVec σ u) (hu' : IsSmoothVec σ u') :
    IsSmoothVec σ (u + u') := by
  intro g₀ hg₀
  obtain ⟨U, F, hU, hg, hF, hFe⟩ := hu g₀ hg₀
  obtain ⟨U', F', hU', hg', hF', hFe'⟩ := hu' g₀ hg₀
  refine ⟨U ∩ U', F + F', hU.inter hU', ⟨hg, hg'⟩, (hF.mono Set.inter_subset_left).add
    (hF'.mono Set.inter_subset_right), fun g hg hgH => ?_⟩
  have e1 := hFe g hg.1 hgH
  have e2 := hFe' g hg.2 hgH
  simp only at e1 e2
  simp only [map_add, Pi.add_apply, e1, e2]

theorem smooth_smul {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {σ : Mat k r → (H →L[ℂ] H)} {u : H} (b : ℂ) (hu : IsSmoothVec σ u) :
    IsSmoothVec σ (b • u) := by
  intro g₀ hg₀
  obtain ⟨U, F, hU, hg, hF, hFe⟩ := hu g₀ hg₀
  refine ⟨U, b • F, hU, hg, hF.const_smul b, fun g hg hgH => ?_⟩
  have e1 := hFe g hg hgH
  simp only at e1
  simp only [map_smul, Pi.smul_apply, e1]

end Sm

theorem ae_rtrans {B : Type*} {μG : Measure (Mt k r)} (hU : IsUnimod (GG k r) μG) {y : Mat k r}
    (hy : y ∈ GG k r) {f g : Mat k r → B}
    (h : (fun x : Mt k r => f (Matrix.of x)) =ᵐ[μG] fun x => g (Matrix.of x)) :
    (fun x : Mt k r => f (Matrix.of x * y)) =ᵐ[μG] fun x => g (Matrix.of x * y) := by
  have hmp : MeasurePreserving (rmulM y : Mt k r → Mt k r) μG μG :=
    ⟨(continuous_rmulM y).measurable, hU.1 y hy⟩
  exact hmp.quasiMeasurePreserving.ae_eq_comp h

theorem ae_ltrans {B : Type*} {μG : Measure (Mt k r)} (hH : IsHaarOn (GG k r) μG) {y : Mat k r}
    (hy : y ∈ GG k r) {f g : Mat k r → B}
    (h : (fun x : Mt k r => f (Matrix.of x)) =ᵐ[μG] fun x => g (Matrix.of x)) :
    (fun x : Mt k r => f (y * Matrix.of x)) =ᵐ[μG] fun x => g (y * Matrix.of x) := by
  have hc : Continuous (lmulM y : Mt k r → Mt k r) :=
    (continuous_const (y := y)).matrix_mul (continuous_id (X := Mat k r))
  have hmp : MeasurePreserving (lmulM y : Mt k r → Mt k r) μG μG :=
    ⟨hc.measurable, hH.2.2.2 y hy⟩
  exact hmp.quasiMeasurePreserving.ae_eq_comp h

end GlobalTheory.SgInf.BesselExt

open GlobalTheory.SgInf.BesselExt in
theorem GlobalTheory.SgInf.exists_besselExt : ∀ (k r : ℕ) {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp] [CompleteSpace Wp] (σ : Mat k r → (H →L[ℂ] H)) (w : H) (a : ℝ) (μG : Measure (Mt k r)) (d : ℝ) (z : Fin (2 * r + k + 1) → ℂ) (c : Fin r → ℂ) (π : Mat k r → (Wp →L[ℂ] Wp)) (μS : Measure (Mt k r)) , Std σ w a μG d → Side z π μS → IsSmoothVec σ w → ∀ v ∈ DD σ w, ∀ ξ : Wp, ∃ l : H → Wp, IsBesselMapSm z (psiGen k r z c) σ π l ∧ ∀ u ∈ DD σ w, l u = be (psiGen k r z c) π μS σ u v ξ := by
  intro k r H _ _ _ Wp _ _ _ _ σ w a μG d z c π μS hStd hSide hw v hv ξ
  obtain ⟨T, hTD, hadd, hsmul, hloc, hR, hL⟩ := GlobalTheory.T.besselMatrixCoeff_extends_bounded_equivariant k r σ w a μG d z c π μS hStd hSide v hv ξ
  have hrep : IsURepOn (GG k r) σ := hStd.2.1
  have hHaar : IsHaarOn (GG k r) μG := hStd.2.2.2.2.1
  have hUni : IsUnimod (GG k r) μG := GlobalTheory.T.isUnimodular_besselModelUnitaryGroup k r μG hHaar
  have hDDi := GlobalTheory.T.smooth_vectors_dense_invariant k r σ w hrep
  have hPi := GlobalTheory.T.besselSubgroupRepTwisted_isUnitaryRep k r z c π hSide.1 hSide.2.1 hSide.2.2.1
  obtain ⟨C, Ws, hWs, hreg⟩ := GlobalTheory.T.boundedEquivariantMap_smooth_continuous_seminorm_bound k r σ μG T hrep hHaar hadd hsmul hloc hR
  classical
  let F : H → Mat k r → Wp := fun u => if h : IsSmoothVec σ u then (hreg u h).choose else 0
  have hF : ∀ u, IsSmoothVec σ u → ContinuousOn (F u) (GG k r) ∧
      (fun x : Mt k r => F u (Matrix.of x)) =ᵐ[μG] (fun x => T u (Matrix.of x)) ∧
      ‖F u 1‖ ≤ C * (Ws.map fun ws => ‖dsigW σ ws u‖).sum := by
    intro u hu
    have := (hreg u hu).choose_spec
    simp only [F, dif_pos hu]
    exact this
  have hDDsm : ∀ u ∈ DD σ w, IsSmoothVec σ u := fun u hu => (hDDi.2.2.2.2 hw).1 u (hDDi.2.2.1 hu)
  refine ⟨fun u => F u 1, ⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · intro u hu u' hu'
    have hs := smooth_add hu hu'
    refine GlobalTheory.T.besselModel_eqOn_of_continuousOn_ae_eq k r μG (F (u + u')) (fun x => F u x + F u' x) hHaar (hF _ hs).1
      ((hF u hu).1.add (hF u' hu').1) ?_ 1 one_memG
    filter_upwards [(hF _ hs).2.1, hadd u u', (hF u hu).2.1, (hF u' hu').2.1] with x h1 h2 h3 h4
    rw [h1, h2, h3, h4]
  · intro b u hu
    have hs := smooth_smul b hu
    refine GlobalTheory.T.besselModel_eqOn_of_continuousOn_ae_eq k r μG (F (b • u)) (fun x => b • F u x) hHaar (hF _ hs).1
      ((hF u hu).1.const_smul b) ?_ 1 one_memG
    filter_upwards [(hF _ hs).2.1, hsmul b u, (hF u hu).2.1] with x h1 h2 h3
    rw [h1, h2, h3]
  · intro h hh m hm u hu
    have hhG : h ∈ GG k r := hh.1
    have hmG : m ∈ GG k r := hm.1
    have htG : h * m ∈ GG k r := mul_memG hhG hmG
    have htS : h * m ∈ Sset k r z := ⟨h, hh, m, hm, rfl⟩
    have hsu : IsSmoothVec σ (σ (h * m) u) := ((hDDi.2.2.2.1 u hu).1 _ htG)

    have h1 : ∀ x ∈ GG k r, F (σ (h * m) u) x = F u (x * (h * m)) := by
      refine GlobalTheory.T.besselModel_eqOn_of_continuousOn_ae_eq k r μG _ _ hHaar (hF _ hsu).1 ?_ ?_
      · exact (hF u hu).1.comp ((continuous_id.mul continuous_const).continuousOn)
          (fun x hx => mul_memG hx htG)
      · filter_upwards [(hF _ hsu).2.1, hR _ htG u, ae_rtrans hUni htG (hF u hu).2.1] with x h1 h2 h3
        rw [h1, h2, h3]

    have h2 : ∀ x ∈ GG k r, F u ((h * m) * x) = PiS (psiGen k r z c) π (h * m) (F u x) := by
      refine GlobalTheory.T.besselModel_eqOn_of_continuousOn_ae_eq k r μG (fun x => F u ((h * m) * x)) (fun x => PiS (psiGen k r z c) π (h * m) (F u x))
        hHaar ?_ ?_ ?_
      · exact (hF u hu).1.comp ((continuous_const.mul continuous_id).continuousOn)
          (fun x hx => mul_memG htG hx)
      · exact (PiS (psiGen k r z c) π (h * m)).continuous.comp_continuousOn (hF u hu).1
      · filter_upwards [ae_ltrans hHaar htG (hF u hu).2.1, hL _ htS u, (hF u hu).2.1] with x h1 h2 h3
        rw [h1, h2, h3]
    show F (σ (h * m) u) 1 = psiGen k r z c m • π h (F u 1)
    rw [h1 1 one_memG, Matrix.one_mul, ← Matrix.mul_one (h * m), h2 1 one_memG, (hPi.1 h hh m hm).2]
    rfl
  · refine ⟨C, Ws, hWs, fun u hu => (hF u hu).2.2⟩
  · intro u hu
    have hsu := hDDsm u hu
    have hcont : ContinuousOn (Afun (psiGen k r z c) π μS σ u v ξ) (GG k r) := by
      have hD1 := GlobalTheory.T.besselForm_converges_equivariant_hermitian k r σ w a μG d z c π μS hStd hSide (DD σ w) hDDi.1 hStd.2.2.2.2.2.2.2.1 u hu v hv
      exact (ContinuousLinearMap.apply ℂ Wp ξ).continuous.comp_continuousOn hD1.2.2.2
    have := GlobalTheory.T.besselModel_eqOn_of_continuousOn_ae_eq k r μG (F u) _ hHaar (hF u hsu).1 hcont
      (by rw [← hTD u hu]; exact (hF u hsu).2.1) 1 one_memG
    show F u 1 = _
    rw [this]
    simp only [Afun, hrep.1.1, ContinuousLinearMap.one_apply]
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.FibreVolumeNormalFormStabiliser
section
noncomputable section

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.Amp.FibreVolume

variable {k r : ℕ}

theorem hpk_unit : IsUnit (Hpk k r).det :=
  Matrix.isUnit_det_of_left_inverse (hpkFacts k r).2.1

theorem GG_one : (1 : Mat k r) ∈ GG k r := (uHGroup _ _ hpk_unit).1

theorem GG_mul {a b : Mat k r} (ha : a ∈ GG k r) (hb : b ∈ GG k r) : a * b ∈ GG k r :=
  (uHGroup _ _ hpk_unit).2.1 a ha b hb

theorem GG_unit {a : Mat k r} (ha : a ∈ GG k r) : IsUnit a.det := ((uHGroup _ _ hpk_unit).2.2 a ha).1

theorem GG_inv {a : Mat k r} (ha : a ∈ GG k r) : a⁻¹ ∈ GG k r := ((uHGroup _ _ hpk_unit).2.2 a ha).2

theorem N_sub_S (z : Fin (2 * r + k + 1) → ℂ) {n : Mat k r} (hn : n ∈ Nset k r) : n ∈ Sset k r z :=
  ⟨1, ⟨GG_one, fun a => ⟨Matrix.one_mulVec _, Matrix.one_mulVec _⟩, Matrix.one_mulVec _⟩, n, hn, (one_mul n).symm⟩

theorem continuous_two (a b : Mat k r) : Continuous (fun x : Mt k r => (a * Matrix.of x * b : Mat k r)) :=
  (continuous_const.matrix_mul (continuous_id (X := Mat k r))).matrix_mul continuous_const

theorem measurable_two (a b : Mat k r) :
    Measurable (fun x : Mt k r => (Matrix.of.symm (a * Matrix.of x * b) : Mt k r)) :=
  Continuous.measurable (α := Mt k r) (γ := Mt k r) (continuous_two a b)

def twoEquiv (a b : Mat k r) (ha : IsUnit a.det) (hb : IsUnit b.det) : Mt k r ≃ᵐ Mt k r where
  toFun x := Matrix.of.symm (a * Matrix.of x * b)
  invFun x := Matrix.of.symm (a⁻¹ * Matrix.of x * b⁻¹)
  left_inv x := by
    simp only [Equiv.apply_symm_apply, Equiv.symm_apply_eq]
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ ha, Matrix.one_mul,
      Matrix.mul_nonsing_inv_cancel_right _ _ hb]
  right_inv x := by
    simp only [Equiv.apply_symm_apply, Equiv.symm_apply_eq]
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ ha, Matrix.one_mul,
      Matrix.nonsing_inv_mul_cancel_right _ _ hb]
  measurable_toFun := measurable_two a b
  measurable_invFun := measurable_two _ _

theorem map_twoEquiv {μ : Measure (Mt k r)} {a b : Mat k r} (ha : IsUnit a.det) (hb : IsUnit b.det)
    (hl : μ.map (lmulM a) = μ) (hr : μ.map (rmulM b) = μ) : μ.map (twoEquiv a b ha hb) = μ := by
  have h1 : Measurable (lmulM a : Mt k r → Mt k r) :=
    Continuous.measurable (α := Mt k r) (γ := Mt k r)
      (continuous_const.matrix_mul (continuous_id (X := Mat k r)))
  have h2 : Measurable (rmulM b : Mt k r → Mt k r) := (continuous_rmulM b).measurable
  have : (twoEquiv a b ha hb : Mt k r → Mt k r) = rmulM b ∘ lmulM a := rfl
  rw [this, ← Measure.map_map h2 h1, hl, hr]

theorem Tz_eq {z z' : Fin (2 * r + k + 1) → ℂ} {g : Mat k r} {c : ℂ} (hg : g ∈ GG k r) (hc : ‖c‖ = 1)
    (h : g *ᵥ z' = c • z) : Tz k r z' = Tz k r z := by
  have h1 : herm (Hpk k r) (g *ᵥ z') (g *ᵥ z') = herm (Hpk k r) z' z' := by
    have hg' : gᴴ * Hpk k r * g = Hpk k r := hg
    unfold herm
    rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hg']
  have h2 : herm (Hpk k r) (c • z) (c • z) = herm (Hpk k r) z z := by
    have hcc : star c * c = 1 := by
      rw [Complex.star_def, Complex.conj_mul', hc]; simp
    unfold herm
    rw [star_smul, Matrix.mulVec_smul, smul_dotProduct, dotProduct_smul, smul_smul, hcc, one_smul]
  unfold Tz
  rw [← h1, h, h2]

theorem fibre_volume : ∀ (k r j : ℕ) (hj : j ≤ r) (z z' : (Fin (2 * r + k + 1) → ℂ)), ∀ (γ : Mat k r) (De s : ℝ) (μR : Measure (Mt k r)), 1 ≤ j → j + 2 ≤ k → DeOK k r z z' γ De → 0 < s → IsNormalFormStabilizerMeasure k r hj z z' γ s μR → ∀ g₁ ∈ GG k r, lebN k r {n | Yj k r hj z z' γ (Matrix.of n * g₁) = 0} = 0 ∧ ∀ φ, SubCut (GG k r) μR φ → ∀ R₀ y : ℝ, 1 ≤ R₀ → 0 < y → ∫⁻ n, φ (rmulM g₁ n) * (Eset0 k r hj z z' γ R₀ y).indicator 1 (rmulM g₁ n) ∂(lebN k r) ≤ ENNReal.ofReal (fibVol0 k r j R₀ De y / s) := by
  intro k r j hj z z' γ De s μR h1 h2 hDe hs hN g₁ hg₁
  obtain ⟨hz, hz', hT, n₁, hn₁, n₂, hn₂, g₀, β, c, hg₀, rfl, rfl⟩ := hN
  obtain ⟨n₀, hn₀, a, ha, m, hm, κ, hκ, hg⟩ := GlobalTheory.T.iwasawa_decomposition_isotropic_flag k r g₁ hg₁
  have hT' : 0 < Tz k r z' := by rw [Tz_eq hg₀.1 hg₀.2.1 hg₀.2.2.1]; exact hT
  have hDe₀ : DeOK k r z z' g₀ De := by
    refine ⟨hDe.1, fun l hl => ?_⟩
    have := hDe.2 l hl
    rwa [dInv k r z z' hz hz' n₁ (N_sub_S z hn₁) n₂ (N_sub_S z' hn₂)] at this
  have key := GlobalTheory.T.flagUnipotent_gramNull_and_fibreVolume_normalForm k r j hj z z' g₀ β c hz hz' hT hg₀ h1 h2 De hDe₀ m hm a ha
  set A : Mat k r := uEmb k r (Matrix.diagonal fun b => (a b : ℂ)) * mEmb k r m with hA
  have hg' : g₁ = n₀ * A * κ := by rw [hg, hA]; simp only [Matrix.mul_assoc]
  clear_value A
  have u₀ := GG_unit hn₀.1
  have u₂ := GG_unit hn₂.1
  have uκ := GG_unit hκ.1
  have hAG : A ∈ GG k r := by
    have : A = n₀⁻¹ * g₁ * κ⁻¹ := by
      rw [hg', ← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ u₀, Matrix.one_mul,
        Matrix.mul_nonsing_inv_cancel_right _ _ uκ]
    rw [this]; exact GG_mul (GG_mul (GG_inv hn₀.1) hg₁) (GG_inv hκ.1)
  have hH := GlobalTheory.T.flagUnipotentLebesgueMeasure_isHaarOn k r
  have hU := ((GlobalTheory.T.unimodular_besselSubgroups_UW_N k r z hz hT (lebN k r)).2.1 hH).1
  set T := twoEquiv n₂ n₀ u₂ u₀ with hTdef
  have hmap : (lebN k r).map T = lebN k r := map_twoEquiv u₂ u₀ (hH.2.2.2 _ hn₂) (hU.1 _ hn₀)
  have hae : ∀ᵐ n ∂(lebN k r), Matrix.of n ∈ Nset k r := hH.2.2.1
  have hTof : ∀ n, (Matrix.of (T n) : Mat k r) = n₂ * Matrix.of n * n₀ := fun n => rfl
  have hγ : n₁ * g₀ * n₂ ∈ GG k r := GG_mul (GG_mul hn₁.1 hg₀.1) hn₂.1
  have hY : ∀ n : Mt k r, Matrix.of n ∈ Nset k r →
      Yj k r hj z z' (n₁ * g₀ * n₂) (Matrix.of n * g₁) = Yj k r hj z z' g₀ (Matrix.of (T n) * A) := by
    intro n hn
    rw [(GlobalTheory.T.flagGramNumberNormalized_invariance k r j hj z z' g₀ hz hz' hg₀.1 _ (GG_mul hn.1 hg₁)).2.1 n₁ hn₁ n₂ hn₂, hTof,
      ← (GlobalTheory.T.flagGramNumberNormalized_invariance k r j hj z z' g₀ hz hz' hg₀.1 _
        (GG_mul (GG_mul (GG_mul hn₂.1 hn.1) hn₀.1) hAG)).1 κ hκ, hg']
    simp only [Matrix.mul_assoc]
  refine ⟨?_, fun φ hφ R₀ y hR hy => ?_⟩
  · have h0 := key.1
    rw [← hmap, MeasurableEquiv.map_apply] at h0
    rw [← h0]
    apply measure_congr
    filter_upwards [hae] with n hn
    show (Yj k r hj z z' (n₁ * g₀ * n₂) (Matrix.of n * g₁) = 0) = (Yj k r hj z z' g₀ (Matrix.of (T n) * A) = 0)
    rw [hY n hn]
  · have hE : ∀ n : Mt k r, Matrix.of n ∈ Nset k r →
        (rmulM g₁ n ∈ Eset0 k r hj z z' (n₁ * g₀ * n₂) R₀ y ↔ rmulM A (T n) ∈ Eset0 k r hj z z' g₀ R₀ y) := by
      intro n hn
      have hx : Matrix.of (T n) * A ∈ GG k r := GG_mul (GG_mul (GG_mul hn₂.1 hn.1) hn₀.1) hAG
      have e1 : Sg2 k r z' (Matrix.of n * g₁) = Sg2 k r z' (Matrix.of (T n) * A) := by
        rw [← (GlobalTheory.T.two_sided_size_function_pos_invariant_continuous k r z' hz' hT').2.1 _ hx n₂⁻¹ (N_sub_S z' ((nSubgroup k r).2.2 _ hn₂)) κ hκ, hTof, hg']
        simp only [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ u₂, Matrix.one_mul]
      have e2 : Sg2 k r z (n₁ * g₀ * n₂ * (Matrix.of n * g₁)) = Sg2 k r z (g₀ * (Matrix.of (T n) * A)) := by
        rw [← (GlobalTheory.T.two_sided_size_function_pos_invariant_continuous k r z hz hT).2.1 _ (GG_mul hg₀.1 hx) n₁ (N_sub_S z hn₁) κ hκ, hTof, hg']
        simp only [Matrix.mul_assoc]
      simp only [Eset0, Set.mem_setOf_eq, of_rmulM]
      rw [e1, e2, hY n hn]
      exact and_congr_left fun _ => iff_of_true (GG_mul hn.1 hg₁) hx
    set ψ : Mt k r → ℝ≥0∞ := fun x =>
      ENNReal.ofReal s * φ (Matrix.of.symm (n₂⁻¹ * Matrix.of x * (n₀⁻¹ * g₁))) with hψ
    have hψT : ∀ n, ψ (T n) = ENNReal.ofReal s * φ (rmulM g₁ n) := by
      intro n
      have : n₂⁻¹ * Matrix.of (T n) * (n₀⁻¹ * g₁) = Matrix.of n * g₁ := by
        rw [hTof]
        simp only [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ u₂, Matrix.one_mul,
          Matrix.mul_nonsing_inv_cancel_right _ _ u₀]
      simp only [hψ, this]; rfl
    have hsub : SubCut (Nset k r) (lebR0 k r j β) ψ := by
      refine ⟨(hφ.1.comp (measurable_two _ _)).const_mul _, fun x hx => ?_⟩
      have hw : n₂⁻¹ * Matrix.of x * (n₀⁻¹ * g₁) ∈ GG k r :=
        GG_mul (GG_mul (GG_inv hn₂.1) hx.1) (GG_mul (GG_inv hn₀.1) hg₁)
      have h := hφ.2 (Matrix.of.symm (n₂⁻¹ * Matrix.of x * (n₀⁻¹ * g₁))) hw
      have hc : (conjM n₂⁻¹ : Mt k r → Mt k r) =
          twoEquiv n₂⁻¹ n₂⁻¹⁻¹ (GG_unit (GG_inv hn₂.1)) (GG_unit (GG_inv (GG_inv hn₂.1))) := rfl
      rw [hc, lintegral_map_equiv, lintegral_smul_measure, smul_eq_mul,
        ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top] at h
      refine le_of_eq_of_le (lintegral_congr fun ρ => ?_) h
      have : n₂⁻¹ * (Matrix.of ρ * Matrix.of x) * (n₀⁻¹ * g₁) =
          n₂⁻¹ * Matrix.of ρ * n₂⁻¹⁻¹ * (n₂⁻¹ * Matrix.of x * (n₀⁻¹ * g₁)) := by
        rw [Matrix.nonsing_inv_nonsing_inv _ u₂]
        simp only [← Matrix.mul_assoc, Matrix.mul_nonsing_inv_cancel_right _ _ u₂]
      exact congrArg (fun w : Mat k r => ENNReal.ofReal s * φ (Matrix.of.symm w)) this
    have h := key.2 ψ hsub R₀ y hR hy
    rw [← hmap, lintegral_map_equiv] at h
    have h' : ENNReal.ofReal s * ∫⁻ n, φ (rmulM g₁ n) *
        (Eset0 k r hj z z' (n₁ * g₀ * n₂) R₀ y).indicator 1 (rmulM g₁ n) ∂(lebN k r) ≤
        ENNReal.ofReal (fibVol0 k r j R₀ De y) := by
      rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      refine le_of_eq_of_le (lintegral_congr_ae ?_) h
      filter_upwards [hae] with n hn
      rw [hψT, ← mul_assoc]
      refine congrArg (fun t => ENNReal.ofReal s * φ (rmulM g₁ n) * t) ?_
      by_cases hm : rmulM g₁ n ∈ Eset0 k r hj z z' (n₁ * g₀ * n₂) R₀ y
      · rw [Set.indicator_of_mem hm, Set.indicator_of_mem ((hE n hn).1 hm)]; rfl
      · rw [Set.indicator_of_notMem hm, Set.indicator_of_notMem (fun h => hm ((hE n hn).2 h))]
    rw [ENNReal.ofReal_div_of_pos hs, ENNReal.le_div_iff_mul_le (Or.inl (by simpa using hs))
      (Or.inl ENNReal.ofReal_ne_top), mul_comm]
    exact h'

end GlobalTheory.Amp.FibreVolume
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.FlagClassMeasureBoundLatticeStabiliserStatement
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flagClass_measure_bound_lattice_stabiliser : ∀ (I I₀ : AutInst) (e : I₀.E ≃+* I.E) (xf : I.Gf) (a : ℕ) (j : Fin a → ℕ) (S : Fin (a + 1) → Submodule (𝓞 I.E) (Fin I.n → I.E)) (Λ : ∀ i, Submodule (𝓞 I.E) (Fin (j i) → I.E)) (x₀ : I₀.Gf) (T T' : ∀ i, Matrix (Fin I.n) (Fin (j i)) I.E) (T₀ : Matrix (Fin I.n) (Fin I₀.n) I.E), (∀ i, 1 ≤ j i) → IsAdapted I I₀ e xf j S Λ x₀ T T' T₀ → ∀ (p q : ℕ), HasSig I p q → ∀ (c : InfinitePlace I.F → ℝ) (c₀ : InfinitePlace I₀.F → ℝ), IsGaugeAll I c → IsGaugeAll I₀ c₀ → ∀ B : Set (Fin a → ℝ), MeasurableSet B → B ⊆ simplexH a → ENNReal.ofReal (∏ v, c v) * covol (flagGroup I xf S) (Measure.pi fun v => Formalism.REAL.muG (I.ε v)) {g | sizesAt I xf S g ∈ B} ≤ ENNReal.ofReal (cIw p q j ^ I.f * (2 * Formalism.HermitianLatticesTheory.vInv I.E) ^ ((I.f : ℝ) * dimN I.n j / 2)) * (∏ i, ENNReal.ofReal (2 ^ (I.f * j i ^ 2)) * slabVol I.E (j i) (Λ i)) * (ENNReal.ofReal (∏ v, c₀ v) * covol (latGroup I₀ x₀) (Measure.pi fun v => Formalism.REAL.muG (I₀.ε v)) Set.univ) * ∫⁻ τ in B, ENNReal.ofReal (dens I.n I.f j τ) := by
  first | exact @GlobalTheory.FlagBase.OneClass.bound | exact GlobalTheory.FlagBase.OneClass.bound | (intros; apply GlobalTheory.FlagBase.OneClass.bound <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.GramFibreMeasureFreeTupleNeZeroFiniteStatement
section
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures
open scoped TensorProduct ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gramFibreMeasure_freeTuple_ne_zero_finite : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (v : HeightOneSpectrum (𝓞 F)), ∀ a : ℕ, ∀ (μ : Measure (Fin a → Fin n → Fv F v ⊗[F] E)) (ν : Measure (HermR (Fv F v) σ a)), μ.IsAddHaarMeasure → ν.IsAddHaarMeasure → ∀ fib : HermR (Fv F v) σ a → Measure (Fin a → Fin n → Fv F v ⊗[F] E), IsFibreFamily μ (gramR (Fv F v) σ J) Subtype.val {X | LinearIndependent (Fv F v ⊗[F] E) X} ν Set.univ fib → ∀ (x : Fin a → Fin n → Fv F v ⊗[F] E) (S : HermR (Fv F v) σ a), LinearIndependent (Fv F v ⊗[F] E) x → gramR (Fv F v) σ J x = (S : Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)) → fib S ≠ 0 ∧ ∀ K : Set (Fin a → Fin n → Fv F v ⊗[F] E), IsCompact K → K ⊆ {X | LinearIndependent (Fv F v ⊗[F] E) X} → fib S K < ⊤ := by
  first | exact @GlobalTheory.LocalFibreNonzero.fibre_nonzero_finite | exact GlobalTheory.LocalFibreNonzero.fibre_nonzero_finite | (intros; apply GlobalTheory.LocalFibreNonzero.fibre_nonzero_finite <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.SiegelMassRatioUnimodularDefinite
section
namespace GlobalTheory.Mass

theorem siegelMassRatio_holds : Formalism.HermitianLatticesTheory.SiegelMassRatio :=
  Formalism.HermitianLattices.Ext.L3.siegelMassRatio_of_LI binary_hermitian_represents Formalism.HermitianLattices.Ext.L3.liStat

end GlobalTheory.Mass
end

