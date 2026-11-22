import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0015
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0011
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0550
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0563
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0594
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0595
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0598
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0597
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0403
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0406
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0579
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0607
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnipotentBlockColumnIndex
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0017
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.OneSubPhiOntoOfFilZero
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0005
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0006
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsPotentialPhiSub
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteClassesSubsetAdmissibleOfGoodO
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsCrystallineIffMemH1f
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsAdaptedOfSurjective
import Formalism.SharpRestriction.LevelLetterCocycles.ArcLiftingSetup
import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0007
import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0013
import Formalism.GaloisCohomology.LocalTateDualityK
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.RationalDualityOfAllCoefficients
import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0041
import ReciprocityTheory.ReductiveGroups.TraceFormulas.LatDefs
import ReciprocityTheory.GaloisValuations.Global
import Formalism.WachLatticeTwists.CoprimeLiftBounds.Statement
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import ReciprocityTheory.NeutralLocalFields.Bundle0001
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0078
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0155
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0144
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0119
import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0006
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0003

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SemistablePeriodFrameIsDeRham
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

namespace GlobalTheory.BKLim.WDR

theorem frame_isDR : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (τ : Ainf l), bk.IsPer τ → ∀ (d : ℕ) (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) (ℤ_[l])), (∀ g, IsUnit (ρ g)) → ∀ (s : WSeed bk d ρ τ) (N : ℕ) (F : Frame bk N d ρ) (Y : Matrix (Fin d) (Fin d) (Ainf l)) (Z : Matrix (Fin d) (Fin d) (bk.DS bk.ρ₀)), Y.map (inclW l) = inclW l τ ^ s.N • F.T → IsUnit Z → (∀ i : bk.DS bk.ρ₀ →+* bk.DA bk.ρ₀, IsDiscMap bk.ev i → s.W * Z.map i = Y.map bk.iA) → (∀ (g : ↥(GK K)) (G : bk.DA bk.ρ₀ →+* bk.DA bk.ρ₀) (i : bk.DS bk.ρ₀ →+* bk.DA bk.ρ₀), IsDiscMap (Per.σA (g : GQ l)) G → IsDiscMap bk.ev i → G (bk.iS bk.E) ^ s.N • (s.X.map bk.iS * Z.map i * (F.ε g).map bk.iA) = bk.iS bk.E ^ s.N • (s.κ g * (s.X.map bk.iS * Z.map i).map G)) → F.IsDR := by
  intro l hl K bk τ hτ d ρ hρ s N F Y Z hY hZ hWZ hκ
  have hl1 : (1 : ℝ≥0) < l := by exact_mod_cast hl.out.one_lt
  have h0 : 0 < bk.ρ₀ := NNReal.rpow_pos (zero_lt_one.trans hl1)
  have h1 : bk.ρ₀ < 1 := NNReal.rpow_lt_one_of_one_lt_of_neg hl1
    (neg_lt_zero.2 (one_div_pos.2 (Nat.cast_pos.2 bk.deg_pos)))
  have hpow : bk.ρ₀ ^ l ≤ bk.ρ₀ := pow_le_of_le_one h0.le h1.le hl.out.ne_zero
  obtain ⟨hmap, -, -⟩ := GlobalTheory.BSP.exists_discMaps l K bk
  obtain ⟨i, hi⟩ := hmap _ _ bk.ev (X : bk.S) (bk.ev X) bk.ρ₀ bk.ρ₀ 1 h0 (by rw [pow_one]) (by rw [pow_one])
  obtain ⟨Ψ, hΨ⟩ := hmap _ _ (frobS l bk.a) (X : bk.S) (X : bk.S) bk.ρ₀ bk.ρ₀ l h0 (by rw [frobS_X]) hpow
  obtain ⟨Φ, hΦ⟩ := hmap _ _ (WittVector.frobenius : Ainf l →+* Ainf l) (bk.ev X) (bk.ev X) bk.ρ₀ bk.ρ₀ l h0
    (by rw [← bk.ev_frob, frobS_X, map_pow]) hpow
  set V : Matrix (Fin d) (Fin d) (bk.DS bk.ρ₀) := s.X.map (toDisc l (X : bk.S) bk.ρ₀) * Z with hV
  have hVi : V.map i = s.X.map bk.iS * Z.map i := by
    rw [hV, Matrix.map_mul, Matrix.map_map]
    congr 1
    ext a b
    exact hi.ext _
  set H := s.F.map ((toDisc l (X : bk.S) bk.ρ₀).comp C) * V.map Ψ with hH
  have hHu : IsUnit H := GlobalTheory.T.semistablePeriod_frame_frobenius_isUnit_disc l K bk τ d ρ s Ψ Z hΨ hZ
  intro m
  exact GlobalTheory.T.exists_beta_of_disc_cocycle_alt l K bk d s.N s.κ (fun g => (F.ε g).map WittVector.frobenius) H i hi hHu s.log
    (fun g G hG => GlobalTheory.T.semistablePeriod_frameCocycle_frobenius_twist_on_disc l K bk τ d ρ s g G Φ i Ψ V (F.ε g) hG hΦ hi hΨ
      (GlobalTheory.T.semistablePeriod_cocycle_frobenius_relation_on_disc l K bk τ hτ d ρ hρ s g G Φ hG hΦ) (by rw [hVi]; exact hκ g G i hG hi)) m

end GlobalTheory.BKLim.WDR
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SemistableSeedModuleLAdicClosed
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

noncomputable section

namespace GlobalTheory.BKLim

theorem wseed_module_lAdic_closed : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (τ : Ainf l) (hτ : bk.IsPer τ) (d : ℕ) (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) ℤ_[l]) (hρ : ∀ g, IsUnit (ρ g)) (s : WSeed bk d ρ τ), ∀ y : ℕ → Fin d → Ainf l, (∀ n, (fun y : Fin d → Ainf l => ∃ x : Fin d → bk.DS bk.ρ₀, ∀ j : bk.DS bk.ρ₀ →+* bk.DA bk.ρ₀, IsDiscMap bk.ev j → s.W *ᵥ (fun a => j (x a)) = fun a => bk.iA (y a)) (y n)) → (∀ n a, (l : Ainf l) ^ n ∣ y (n + 1) a - y n a) → ∀ z : Fin d → Ainf l, (∀ n a, (l : Ainf l) ^ n ∣ z a - y n a) → (fun y : Fin d → Ainf l => ∃ x : Fin d → bk.DS bk.ρ₀, ∀ j : bk.DS bk.ρ₀ →+* bk.DA bk.ρ₀, IsDiscMap bk.ev j → s.W *ᵥ (fun a => j (x a)) = fun a => bk.iA (y a)) z := by
  intro l _ K bk τ hτ d ρ hρ s y hy _hcau z hz
  beta_reduce at hy ⊢
  obtain ⟨hρ0, hρ1⟩ := bk.ρ₀_mem_Ioo_zero_one
  have hX : ‖toDisc l (bk.ev X) bk.ρ₀ (bk.ev X)‖ ≤ bk.ρ₀ := by
    simpa using norm_toDisc_pow_le (l := l) (u := bk.ev X) (ρ := bk.ρ₀) 1 hρ0
  set j₀ : bk.DS bk.ρ₀ →+* bk.DA bk.ρ₀ := Disc.map bk.ev hX with hj₀
  have hj₀d : IsDiscMap bk.ev j₀ := isDiscMap_map bk.ev hX
  obtain ⟨ι, ⟨TB⟩⟩ := GlobalTheory.BSP.AinfTopBasis.main l K bk
  obtain ⟨cD, hc_to, hc_mul, hc_norm, -⟩ := GlobalTheory.BSP.disc_coefficients l K bk (Ainf l) bk.ev ι TB bk.ρ₀ hρ0 hρ1 j₀ hj₀d
  obtain ⟨r, hr⟩ := GlobalTheory.BSP.pow_l_mem_span_coeff l K bk τ hτ ι TB (2 * s.N * d)
  obtain ⟨f, hf⟩ := Finsupp.mem_span_range_iff_exists_finsupp.1 hr

  set V : Matrix (Fin d) (Fin d) (bk.DA bk.ρ₀) := s.W'.det • adjugate s.W with hV
  have hVW : V * s.W = bk.iA (τ ^ (2 * s.N * d)) • (1 : Matrix (Fin d) (Fin d) (bk.DA bk.ρ₀)) := by
    have hd : s.W.det * s.W'.det = bk.iA (τ ^ (2 * s.N * d)) := by
      rw [← det_mul, s.W_mul, det_smul, det_one, mul_one, Fintype.card_fin, map_pow]
      ring
    rw [hV, smul_mul, adjugate_mul, smul_smul, mul_comm, hd]

  let Φ : bk.DA bk.ρ₀ → bk.DS bk.ρ₀ := fun w => ∑ i ∈ f.support, toDisc l (X : bk.S) bk.ρ₀ (f i) * cD i w
  have key : ∀ (x : Fin d → bk.DS bk.ρ₀) (a : Fin d),
      (l : bk.DS bk.ρ₀) ^ r * x a = Φ ((V *ᵥ (s.W *ᵥ fun b => j₀ (x b))) a) := by
    intro x a
    have hsm : ∀ (c : bk.DA bk.ρ₀) (v : Fin d → bk.DA bk.ρ₀), (c • (1 : Matrix (Fin d) (Fin d) (bk.DA bk.ρ₀))) *ᵥ v = c • v := by
      intro c v; ext b; simp [mulVec, dotProduct, Matrix.one_apply]
    rw [mulVec_mulVec, hVW, hsm]
    have h1 : ∀ i, cD i ((bk.iA (τ ^ (2 * s.N * d)) • fun b => j₀ (x b)) a) =
        x a * toDisc l (X : bk.S) bk.ρ₀ (TB.c i (τ ^ (2 * s.N * d))) := by
      intro i
      rw [Pi.smul_apply, smul_eq_mul, mul_comm, hc_mul, hc_to]
    simp only [Φ, h1]
    have h2 := congrArg (toDisc l (X : bk.S) bk.ρ₀) hf
    rw [Finsupp.sum, map_sum, map_pow, map_natCast] at h2
    rw [← h2, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [smul_eq_mul, map_mul]; ring
  obtain ⟨u, hu⟩ : IsUnit ((l : bk.DS bk.ρ₀) ^ r) := (isUnit_l_disc l (X : bk.S) bk.ρ₀).pow r
  have hsol : ∀ (x : Fin d → bk.DS bk.ρ₀) (a : Fin d),
      x a = ↑u⁻¹ * Φ ((V *ᵥ (s.W *ᵥ fun b => j₀ (x b))) a) := by
    intro x a
    rw [← key, ← hu, Units.inv_mul_cancel_left]

  have hcont : ∀ {F : bk.DS bk.ρ₀ →+* bk.DA bk.ρ₀}, IsDiscMap bk.ev F → Continuous F := fun hF =>
    AddMonoidHomClass.continuous_of_bound _ 1 fun x => (hF.norm_le x).trans (one_mul _).ge
  have hcDc : ∀ i, Continuous (cD i) := fun i =>
    AddMonoidHomClass.continuous_of_bound _ 1 fun x => (hc_norm i x).trans (one_mul _).ge
  let G : (Fin d → bk.DA bk.ρ₀) → (Fin d → bk.DA bk.ρ₀) := fun v =>
    s.W *ᵥ fun a => j₀ (↑u⁻¹ * Φ ((V *ᵥ v) a))
  have hGc : Continuous G := by
    refine continuous_const.matrix_mulVec (continuous_pi fun a => (hcont hj₀d).comp (continuous_const.mul ?_))
    exact continuous_finsetSum _ fun i _ => continuous_const.mul
      ((hcDc i).comp ((continuous_apply a).comp (continuous_const.matrix_mulVec continuous_id)))
  have hGy : ∀ n, G (fun a => bk.iA (y n a)) = fun a => bk.iA (y n a) := by
    intro n
    obtain ⟨x, hx⟩ := hy n
    have hxe := hx j₀ hj₀d
    have h3 : G (s.W *ᵥ fun b => j₀ (x b)) = s.W *ᵥ fun b => j₀ (x b) := by
      dsimp only [G]; congr 1; funext a; rw [← hsol x a]
    rwa [hxe] at h3

  have hl1 : (1 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).one_lt
  have ht : Filter.Tendsto (fun n => fun a => bk.iA (y n a)) Filter.atTop (nhds fun a => bk.iA (z a)) := by
    rw [tendsto_pi_nhds]; intro a
    have h0 : Filter.Tendsto (fun n => bk.iA (z a - y n a)) Filter.atTop (nhds 0) := by
      refine squeeze_zero_norm (fun n => ?_)
        (tendsto_pow_atTop_nhds_zero_of_lt_one (by positivity) (inv_lt_one_of_one_lt₀ hl1))
      obtain ⟨w, hw⟩ := hz n a
      rw [hw]; exact norm_toDisc_natPow_mul_le _ _ n w
    have h4 := (tendsto_const_nhds (x := bk.iA (z a))).sub h0
    simpa only [sub_zero, map_sub, sub_sub_cancel] using h4
  have hfix : G (fun a => bk.iA (z a)) = fun a => bk.iA (z a) :=
    (isClosed_eq hGc continuous_id).mem_of_tendsto ht (Filter.Eventually.of_forall hGy)
  refine ⟨fun a => ↑u⁻¹ * Φ ((V *ᵥ fun b => bk.iA (z b)) a), fun j hj => ?_⟩
  rw [hj.unique hj₀d]
  exact hfix

end GlobalTheory.BKLim
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SetIntegralFundamentalDomainEqMassMulAverageStatement
section
open NumberField IsDedekindDomain MeasureTheory Matrix GlobalTheory.CuspRep GlobalTheory.CuspGeneric
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.setIntegral_fundamentalDomain_eq_mass_mul_average : ∀ (G : Type) [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G] [LocallyCompactSpace G] [SecondCountableTopology G] [T2Space G] (Γ : AddSubgroup G), IsCoLat Γ → ∀ [MeasurableSpace G] [BorelSpace G] (μ : Measure G) (𝓕 : Set G), μ.IsAddHaarMeasure → IsAddFundamentalDomain Γ 𝓕 μ → ∀ Φ : G → ℂ, Per Γ Φ → μ 𝓕 ≠ 0 ∧ μ 𝓕 ≠ ⊤ ∧ IntegrableOn Φ 𝓕 μ ∧ ∫ x in 𝓕, Φ x ∂μ = ((μ 𝓕).toReal : ℂ) * avg Γ Φ := by
  first | exact @GlobalTheory.CuspGeneric.setIntegral_eq_mass_mul_avg | exact GlobalTheory.CuspGeneric.setIntegral_eq_mass_mul_avg | (intros; apply GlobalTheory.CuspGeneric.setIntegral_eq_mass_mul_avg <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TameTypeOfExtensionLattice
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

noncomputable section

namespace GlobalTheory.TameExt

open GlobalTheory.IndefiniteRowSideFullHecke.CrystallineExtensions

theorem aeval_intertwine {R M N : Type} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N]
    [Module R N] (f : M →ₗ[R] N) (a : Module.End R M) (b : Module.End R N) (hab : ∀ v, b (f v) = f (a v))
    (p : Polynomial R) (v : M) : Polynomial.aeval b p (f v) = f (Polynomial.aeval a p v) := by
  have hpow : ∀ (n : ℕ) v, (b ^ n) (f v) = f ((a ^ n) v) := by
    intro n
    induction n with
    | zero => intro v; rfl
    | succ n ih =>
      intro v
      rw [pow_succ, Module.End.mul_apply, hab, ih, pow_succ, Module.End.mul_apply]
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp only [map_add, LinearMap.add_apply, hp, hq]
  | monomial n c =>
    simp only [Polynomial.aeval_monomial, Module.End.mul_apply, Module.algebraMap_end_apply, hpow, map_smul]

section Gen

variable {G H : Type} [Group G] [Group H] (ι : H →* G)
  {Qp K₀ K K₀' K' B BdR : Type} [Field Qp] [Field K₀] [Field K] [Field K₀'] [Field K']
  [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
  [Algebra Qp K₀'] [Algebra Qp K'] [Algebra K₀' K'] [IsScalarTower Qp K₀' K']
  [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
  [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
  [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
  [Algebra K₀' B] [IsScalarTower Qp K₀' B]
  [Algebra K₀' BdR] [Algebra K' BdR] [IsScalarTower Qp K' BdR]
  [IsScalarTower K₀' K' BdR] [IsScalarTower Qp K₀' BdR]
  (PD : PeriodData G Qp K₀ K B BdR) (PD' : PeriodData H Qp K₀' K' B BdR)
  {LL : Type} [Field LL] [Algebra Qp LL]
  {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]

theorem actVB_comp' (hι : ∀ h b, PD'.actB h b = PD.actB (ι h) b) (ρ : Representation LL G V) (h : H)
    (v : V ⊗[Qp] B) : actVB PD' (ρ.comp ι) h v = actVB PD ρ (ι h) v := by
  induction v using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul v b =>
    change ρ (ι h) v ⊗ₜ[Qp] PD'.actB h b = ρ (ι h) v ⊗ₜ[Qp] PD.actB (ι h) b
    rw [hι]

theorem actVB_mulVB' (ρ : Representation LL G V) (g : G) (k : K₀')
    (hk : PD.actB g (algebraMap K₀' B k) = algebraMap K₀' B k) (v : V ⊗[Qp] B) :
    actVB PD ρ g (mulVB (LL := LL) k v) = mulVB (LL := LL) k (actVB PD ρ g v) := by
  induction v using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul v b =>
    change ρ g v ⊗ₜ[Qp] PD.actB g (algebraMap K₀' B k * b) = ρ g v ⊗ₜ[Qp] (algebraMap K₀' B k * PD.actB g b)
    rw [map_mul, hk]

theorem snd_actVB' (ρ : Representation LL H (V × LL)) (hρ : ∀ h v, (ρ h v).2 = v.2) (h : H)
    (w : (V × LL) ⊗[Qp] B) :
    AlgebraTensorModule.map (LinearMap.id : LL →ₗ[LL] LL) (((PD'.actB h).toAlgHom.toLinearMap).restrictScalars Qp)
        (AlgebraTensorModule.rTensor Qp B (LinearMap.snd LL V LL) w) =
      AlgebraTensorModule.rTensor Qp B (LinearMap.snd LL V LL) (actVB PD' ρ h w) := by
  induction w using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | add w w' hw hw' => simp only [map_add, hw, hw']
  | tmul v b =>
    have h2 : LinearMap.snd LL V LL (ρ h v) = v.2 := hρ h v
    simp only [actVB, AlgebraTensorModule.map_tmul, AlgebraTensorModule.rTensor_tmul, h2]
    rfl

theorem aeval_extRep' [TopologicalSpace G] [TopologicalSpace V] [ContinuousAdd V] [ContinuousConstSMul LL V]
    [FiniteDimensional Qp LL]
    (hι : ∀ h b, PD'.actB h b = PD.actB (ι h) b) (ρ : Representation LL G V) (c : ↥(continuousCocycles ρ))
    (hc : ∃ β : V ⊗[Qp] B, ∀ h, (c : G → V) h ⊗ₜ[Qp] (1 : B) = actVB PD ρ h β - β)
    (g : G) (hg : ∀ k : K₀', PD.actB g (algebraMap K₀' B k) = algebraMap K₀' B k)
    (P : Polynomial LL) (hP : (Polynomial.X - Polynomial.C 1) ∣ P)
    (hTP : ∀ x ∈ Dcris PD' (ρ.comp ι), Polynomial.aeval (actVB PD ρ g : Module.End LL (V ⊗[Qp] B)) P x = 0)
    (x : (V × LL) ⊗[Qp] B) (hx : x ∈ Dcris PD' ((extRep ρ c).comp ι)) :
    Polynomial.aeval (actVB PD (extRep ρ c) g : Module.End LL ((V × LL) ⊗[Qp] B)) P x = 0 := by
  have hE := extRep_isExt ρ c
  obtain ⟨y, hy, hpy⟩ := (GlobalTheory.CrysExt.coboundary_iff_lift PD hE.1 hE.2).1 hc
  have hyfix : ∀ h : G, actVB PD (extRep ρ c) h y = y := (GlobalTheory.CrysSub.mem_Dcris _ _ _).1 hy
  have hf : ∀ (h : H) (v : V), LinearMap.inl LL V LL ((ρ.comp ι) h v) =
      ((extRep ρ c).comp ι) h (LinearMap.inl LL V LL v) := fun h v => hE.1.2.2.2.1 _ v
  have hq : ∀ (h : H) (v : V × LL), LinearMap.snd LL V LL (((extRep ρ c).comp ι) h v) =
      Representation.trivial LL H LL h (LinearMap.snd LL V LL v) := fun h v => hE.1.2.2.2.2 _ v
  have hkF : ∀ (h : H) (k : K₀'), PD.actB (ι h) (algebraMap K₀' B k) = algebraMap K₀' B k :=
    fun h k => (hι h _).symm.trans (AlgEquiv.commutes _ k)
  have hsm : ∀ (k : K₀') (v : (V × LL) ⊗[Qp] B),
      AlgebraTensorModule.rTensor Qp B (LinearMap.snd LL V LL) (mulVB (LL := LL) k v) =
        mulVB (LL := LL) k (AlgebraTensorModule.rTensor Qp B (LinearMap.snd LL V LL) v) := by
    intro k v
    induction v using TensorProduct.induction_on with
    | zero => simp
    | tmul v b => simp [mulVB]
    | add x y hx hy => simp only [map_add, hx, hy]

  have hlift1 : ∀ u : LL ⊗[Qp] K₀', ∃ x₁ : (V × LL) ⊗[Qp] B,
      x₁ ∈ Dcris PD' ((extRep ρ c).comp ι) ∧
      AlgebraTensorModule.rTensor Qp B (LinearMap.snd LL V LL) x₁ = GlobalTheory.CrysExt.incl Qp K₀' B LL u ∧
      actVB PD (extRep ρ c) g x₁ = x₁ := by
    intro u
    induction u using TensorProduct.induction_on with
    | zero => exact ⟨0, zero_mem _, by simp, by simp⟩
    | tmul a k =>
      refine ⟨a • mulVB (LL := LL) k y, (GlobalTheory.CrysSub.mem_Dcris _ _ _).2 fun h => ?_, ?_, ?_⟩
      · rw [map_smul, actVB_comp' ι PD PD' hι, actVB_mulVB' PD _ _ k (hkF h k), hyfix]
      · rw [map_smul, hsm, hpy]
        simp [mulVB, smul_tmul']
      · rw [map_smul, actVB_mulVB' PD _ _ k (hg k), hyfix]
    | add u v hu hv =>
      obtain ⟨x₁, h1, h2, h3⟩ := hu
      obtain ⟨x₂, h4, h5, h6⟩ := hv
      exact ⟨x₁ + x₂, add_mem h1 h4, by rw [map_add, map_add, h2, h5], by rw [map_add, h3, h6]⟩

  obtain ⟨u, hu⟩ := (GlobalTheory.CrysExt.invariant_iff (fun h : H => PD'.actB h) PD'.invB _).1 fun h => by
    rw [snd_actVB' PD' ((extRep ρ c).comp ι) (fun h v => hE.1.2.2.2.2 (ι h) v) h x, (GlobalTheory.CrysSub.mem_Dcris _ _ _).1 hx h]
  obtain ⟨x₁, hx₁, hsx₁, hgx₁⟩ := hlift1 u

  have hD : x - x₁ ∈ Dcris PD' ((extRep ρ c).comp ι) := sub_mem hx hx₁
  have hker : (⟨x - x₁, hD⟩ : ↥(Dcris PD' ((extRep ρ c).comp ι))) ∈
      LinearMap.ker (GlobalTheory.CrysSub.Dmap PD' _ _ _ hq) := by
    rw [LinearMap.mem_ker]
    apply Subtype.ext
    change AlgebraTensorModule.rTensor Qp B (LinearMap.snd LL V LL) (x - x₁) = 0
    rw [map_sub, hsx₁, hu, sub_self]
  obtain ⟨x₀, hx₀⟩ := GlobalTheory.CrysSub.exact_Dmap PD' (ρ.comp ι) ((extRep ρ c).comp ι)
    (Representation.trivial LL H LL) (LinearMap.inl LL V LL) (LinearMap.snd LL V LL)
    hf hq LinearMap.inl_injective Function.Exact.inl_snd LinearMap.snd_surjective hker
  have hx0 : AlgebraTensorModule.rTensor Qp B (LinearMap.inl LL V LL) (x₀ : V ⊗[Qp] B) = x - x₁ :=
    congrArg Subtype.val hx₀
  have hxe : x = x₁ + AlgebraTensorModule.rTensor Qp B (LinearMap.inl LL V LL) (x₀ : V ⊗[Qp] B) := by
    rw [hx0]; abel

  have hpart1 : Polynomial.aeval (actVB PD (extRep ρ c) g : Module.End LL ((V × LL) ⊗[Qp] B)) P x₁ = 0 := by
    obtain ⟨Q, rfl⟩ := hP
    rw [mul_comm, map_mul, Module.End.mul_apply]
    have h1 : Polynomial.aeval (actVB PD (extRep ρ c) g : Module.End LL ((V × LL) ⊗[Qp] B))
        (Polynomial.X - Polynomial.C (1 : LL)) x₁ = 0 := by
      rw [map_sub, Polynomial.aeval_X, Polynomial.aeval_C, map_one, LinearMap.sub_apply, Module.End.one_apply,
        hgx₁, sub_self]
    rw [h1, map_zero]
  have hpart2 := aeval_intertwine (AlgebraTensorModule.rTensor Qp B (LinearMap.inl LL V LL))
    (actVB PD ρ g) (actVB PD (extRep ρ c) g)
    (fun v => (GlobalTheory.CrysSub.rTensor_act _ _ _ _ hE.1.2.2.2.1 g v).symm) P (x₀ : V ⊗[Qp] B)
  rw [hxe, map_add, hpart1, hpart2, hTP _ x₀.2, map_zero, add_zero]

end Gen

end GlobalTheory.TameExt

namespace GlobalTheory.TameExt

theorem tameType_extLat {l : ℕ} [Fact l.Prime] {a e : ℕ} [NeZero a] [NeZero e] (ϖ : PiSys l e) {LL : FinExt l}
    [HasUnr a LL] [TameDescentExponentData ↥LL.1 l e a] (Pl : LocPrime l) (T : QLat LL) (Sig : Finset (ZMod e))
    (h0 : (0 : ZMod e) ∈ Sig) (hT : TameType a ϖ Pl T Sig) (z : ↥(latticeCocycles T.L))
    (hz : (z : Gl l → T.V) ∈ finiteCocycles (Pl.PD (Formalism.MainNotions.ElementDenominator.qlExt l)) T.ρ) :
    TameType a ϖ Pl (GlobalTheory.FiniteAdm.extLat (O := ↥(OL LL)) Subtype.val_injective T z) Sig := by
  intro g hg w hw x hx
  have hFD : FiniteDimensional ℚ_[l] ↥LL.1 := LL.2
  have hP : (Polynomial.X - Polynomial.C (1 : ↥LL.1)) ∣ ∏ c ∈ Sig, (Polynomial.X - Polynomial.C (w ^ c.val)) := by
    have h1 := Finset.dvd_prod_of_mem (fun c : ZMod e => Polynomial.X - Polynomial.C (w ^ c.val)) h0
    rwa [ZMod.val_zero, pow_zero] at h1
  exact aeval_extRep' (inclG (ϖ.field a)) (Pl.PD (Formalism.MainNotions.ElementDenominator.qlExt l)) (Pl.PD (ϖ.field a))
    (fun h b => (Pl.PD_actB _ h b).trans (Pl.PD_actB _ (inclG _ h) b).symm) T.ρ ⟨z, z.2.1⟩ hz.2 g
    (fun k => (Pl.PD_actB _ g _).trans (Pl.actQ_Kur _ ⟨k, k.2.2⟩ ⟨k, k.2.2⟩
      ((IntermediateField.mem_fixingSubgroup_iff _ _).1 (GlobalTheory.BKGal.UnitModel.fix_Kur hg) _ k.2.2)))
    _ hP (hT g hg w hw) x hx

end GlobalTheory.TameExt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TheoremBOfLocalFilteredHypotheses
section
open Formalism Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N

namespace GlobalTheory

theorem theoremB_of_admitted_inputs :
    ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F),
    ∀ (C CR CA CB CK Ckap : ℝ), (320 : ℝ) ≤ C → CrystallineLiftingBounds.adm22 D HW F → CrystallineLiftingBounds.adm23 D HW F →
      Formalism.MainNotions.N.LetterConditionGlobal D HW F → ArcLiftingSetup.Stmt D HW F Cm C CR CA CB CK Ckap :=
  fun D HW F Cm C CR CA CB CK Ckap hC a22 a23 c4 =>
    Formalism.MainNotions.N.Ln17.frobenius_statement_of_fontaine D HW F Cm C CR CA CB CK Ckap hC a22 a23 c4

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnramifiedGaloisHomsBoundedClassNumberOfArtinRec
section
open Formalism.NG Formalism.RepresentationBoundsCohomology.BR NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal

namespace GlobalTheory.UnramifiedClassBound
open Neutral.HilbertClassField

theorem vhE_of_globalArtinReciprocity (hA : GlobalTheory.Published.GlobalArtinReciprocity) : ReciprocityTheory.ChartRestriction.T2.VhE := by
  intro E Ω _ _ _ _ _ Av hAv l _ O _ _ _ _ _ hl M _ _ hM ρ hρ S hS hU
  obtain ⟨eM⟩ := hM
  obtain ⟨art, hsurj, hker, -⟩ := GlobalTheory.T.hilbertClassField_of_globalArtinReciprocity hA E Ω

  let ψ : (Additive (ClassGroup (𝓞 E)) →+ M) →ₗ[O] coZ1s ρ :=
    { toFun := fun f => ⟨fun g => f (Additive.ofMul (art g)), fun g h => by
        show f (Additive.ofMul (art (g * h))) = f (Additive.ofMul (art g)) + ρ g (f (Additive.ofMul (art h)))
        rw [hρ, map_mul, ofMul_mul, map_add]⟩
      map_add' := fun f f' => rfl
      map_smul' := fun r f => rfl }
  let Φ := (Submodule.mkQ ((coB1 ρ).comap (coZ1s ρ).subtype)) ∘ₗ ψ
  have hle : S ≤ LinearMap.range Φ := by
    intro x hx
    obtain ⟨z, rfl, hlc⟩ := hS x hx
    have hz : ∀ g h : G E Ω, (z : G E Ω → M) (g * h) = (z : G E Ω → M) g + (z : G E Ω → M) h := by
      intro g h
      have := z.2 g h
      rw [hρ] at this
      exact this
    have hI : ∀ v, ∀ σ ∈ Ine (F := E) (Av v), (z : G E Ω → M) σ = 0 := by
      intro v σ hσ
      have h1 := hU v hx
      rw [unrH1, LinearMap.mem_ker, Formalism.NG.resH1, Submodule.mkQ_apply, Submodule.mapQ_apply,
        Submodule.Quotient.mk_eq_zero] at h1
      obtain ⟨w, hw⟩ := h1
      have := congrFun hw ⟨σ, hσ⟩
      simp only [coD0, resRep, LinearMap.coe_mk, AddHom.coe_mk] at this
      exact (show (z : G E Ω → M) σ = _ from this.symm).trans (by simp [hρ])
    have hkill := GlobalTheory.T.hilbertSubgroup_le_ker_of_kills_inertia E Ω Av hAv M z hz hlc hI (fun c hc => GlobalTheory.T.galoisAddHom_vanishes_complexConjugation E Ω l O hl M z hz c hc)
    let zH : G E Ω →* Multiplicative M :=
      { toFun := fun g => Multiplicative.ofAdd ((z : G E Ω → M) g)
        map_one' := by
          have := hz 1 1
          simp only [mul_one] at this
          have h0 : (z : G E Ω → M) 1 = 0 := by
            have := congrArg (fun t => t - (z : G E Ω → M) 1) this
            simpa using this.symm
          simp [h0]
        map_mul' := fun g h => by simp [hz g h] }
    have hk : art.ker ≤ zH.ker := by
      intro σ hσ
      rw [hker] at hσ
      simp [zH, MonoidHom.mem_ker, hkill σ hσ]
    let Lf := (MonoidHom.liftOfSurjective art hsurj) ⟨zH, hk⟩
    let f : Additive (ClassGroup (𝓞 E)) →+ M :=
      { toFun := fun a => Multiplicative.toAdd (Lf (Additive.toMul a))
        map_zero' := by simp
        map_add' := fun a b => by simp }
    refine ⟨f, ?_⟩
    change Submodule.mkQ _ (ψ f) = Submodule.mkQ _ z
    congr 1
    apply Subtype.ext
    funext g
    show Multiplicative.toAdd (Lf (art g)) = (z : G E Ω → M) g
    rw [MonoidHom.liftOfRightInverse_comp_apply]
    rfl
  calc Module.length O S ≤ Module.length O (LinearMap.range Φ) :=
        Module.length_le_of_injective (Submodule.inclusion hle) (Submodule.inclusion_injective hle)
    _ ≤ Module.length O (Additive (ClassGroup (𝓞 E)) →+ M) :=
        Module.length_le_of_surjective Φ.rangeRestrict Φ.surjective_rangeRestrict
    _ ≤ _ := by
        have := GlobalTheory.T.length_addMonoidHom_finite_group_fractionQuotient_le l O M eM (Additive (ClassGroup (𝓞 E)))
        rwa [show Nat.card (Additive (ClassGroup (𝓞 E))) = classNumber E from by
          rw [NumberField.classNumber, ← Nat.card_eq_fintype_card]; rfl] at this
end GlobalTheory.UnramifiedClassBound
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachIntegralComplexCocycleClassFiniteStatement
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL Formalism.MainNotions.DeltaInvariantLattices
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.wachIntegralComplex_cocycle_class_finite : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW), Pr2c D HW F := by
  first | exact @GlobalTheory.NL.IntComplex.main | exact GlobalTheory.NL.IntComplex.main | (intros; apply GlobalTheory.NL.IntComplex.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WhittakerLawUpperTriangularUnipotentAdelicStatement
section
open NumberField IsDedekindDomain MeasureTheory Matrix GlobalTheory.CuspRep GlobalTheory.CuspGeneric
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.whittakerLaw_upperTriangularUnipotent_adelic : ∀ (E : Type) [Field E] [NumberField E] (a : ℕ) (ψ : AddChar (Ad E) ℂ) (f : GA E a → ℂ), (∀ k, 0 < k → ∀ (y : UnipotentBlockColumnIndex a k k → Ad E) (g : GA E a), f (blkU y * g) = ψ (dot (eLast a k) y) * f g) → ∀ u : GL (Fin a) (Ad E), (∀ i j : Fin a, j < i → u.val i j = 0) → (∀ j : Fin a, u.val j j = 1) → ∀ g : GA E a, f (u * g) = ψ (∑ p : Fin a × Fin a with (p.2 : ℕ) = p.1 + 1, u.val p.1 p.2) * f g := by
  first | exact @GlobalTheory.CuspGeneric.tri_law | exact GlobalTheory.CuspGeneric.tri_law | (intros; apply GlobalTheory.CuspGeneric.tri_law <;> assumption)
end

