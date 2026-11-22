import Mathlib
import Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinHalfPlane.MirabolicGenerators.SideUnfold
import Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinHalfPlane.UnitTestFunctions.LiftUnit
import Development.WeilBound.CoreStatements.AutomorphicKernels.EisensteinSeriesG2.HeisenbergTheta.HeisenbergThetaConstant.ThetaC

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnfoldingOfAverage
section
noncomputable section

open MeasureTheory Filter Topology
open PositivityTheory.RgEis PositivityTheory.RgEis.MG

namespace GlobalTheory.CompanionTheory.RgEisUnfold

section SlopeTestRemainingChoices

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {W : Type} [NormedAddCommGroup W] [NormedSpace ℂ W] [FiniteDimensional ℂ W]
  {K : Subgroup G} [CompactSpace K] [MeasurableSpace K] [BorelSpace K]

theorem integrable_of_continuous (μ : Measure K) [IsProbabilityMeasure μ] {F : K → (W →L[ℂ] W)}
    (hF : Continuous F) : Integrable F μ :=
  hF.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

theorem exists_avgCLM (μ : Measure K) [IsProbabilityMeasure μ] {ρ : K →* (W →L[ℂ] W)}
    (hρ : Continuous ρ) :
    ∃ A : C(K, ℂ) →L[ℂ] (W →L[ℂ] W), ∀ f : C(K, ℂ), A f = avg μ ρ f := by
  haveI : CompleteSpace W := FiniteDimensional.complete ℂ W
  obtain ⟨C, hC⟩ := isCompact_univ.exists_bound_of_continuousOn hρ.continuousOn
  have hint : ∀ f : C(K, ℂ), Integrable (fun κ => f κ • ρ κ) μ := fun f =>
    integrable_of_continuous μ (f.continuous.smul hρ)
  let A₀ : C(K, ℂ) →ₗ[ℂ] (W →L[ℂ] W) :=
    { toFun := fun f => avg μ ρ f
      map_add' := fun f g => by
        simp only [avg, ContinuousMap.coe_add, Pi.add_apply, add_smul]
        exact integral_add (hint f) (hint g)
      map_smul' := fun a f => by
        simp only [avg, ContinuousMap.coe_smul, Pi.smul_apply, smul_eq_mul, mul_smul,
          RingHom.id_apply]
        exact integral_smul a _ }
  refine ⟨A₀.mkContinuous C fun f => ?_, fun f => rfl⟩
  have h : ∀ᵐ κ ∂μ, ‖f κ • ρ κ‖ ≤ C * ‖f‖ := Eventually.of_forall fun κ => by
    rw [norm_smul, mul_comm]
    exact mul_le_mul (hC κ (Set.mem_univ _)) (f.norm_coe_le_norm κ) (norm_nonneg _)
      ((norm_nonneg _).trans (hC κ (Set.mem_univ _)))
  have := norm_integral_le_of_norm_le_const h
  simpa [avg, A₀] using this

theorem avg_translate (μ : Measure K) [μ.IsHaarMeasure] [IsProbabilityMeasure μ]
    {ρ : K →* (W →L[ℂ] W)} (hρ : Continuous ρ) {φ : K → ℂ} (hφ : Continuous φ) (κ₁ : K) :
    avg μ ρ (fun κ => φ (κ₁ * κ)) = ρ κ₁⁻¹ * avg μ ρ φ := by
  haveI : CompleteSpace W := FiniteDimensional.complete ℂ W
  have hc : Continuous fun κ : K => κ₁ * κ := continuous_const.mul continuous_id
  have hI : Integrable (fun κ => φ (κ₁ * κ) • ρ (κ₁ * κ)) μ :=
    integrable_of_continuous μ ((hφ.comp hc).smul (hρ.comp hc))
  have h1 : avg μ ρ φ = ∫ κ, φ (κ₁ * κ) • ρ (κ₁ * κ) ∂μ :=
    (integral_mul_left_eq_self (fun κ => φ κ • ρ κ) κ₁).symm
  have h2 := ContinuousLinearMap.integral_comp_comm
    (ContinuousLinearMap.compL ℂ W W W (ρ κ₁⁻¹)) hI
  rw [h1]
  refine Eq.trans ?_ h2
  unfold avg
  refine integral_congr_ae (Eventually.of_forall fun κ => ?_)
  have h3 : (ρ κ₁⁻¹).comp (ρ (κ₁ * κ)) = ρ κ := by
    change ρ κ₁⁻¹ * ρ (κ₁ * κ) = ρ κ
    rw [← map_mul, inv_mul_cancel_left]
  change φ (κ₁ * κ) • ρ κ = ContinuousLinearMap.compL ℂ W W W (ρ κ₁⁻¹) (φ (κ₁ * κ) • ρ (κ₁ * κ))
  rw [map_smul, ContinuousLinearMap.compL_apply, h3]

end SlopeTestRemainingChoices

theorem unfold : SecLaw → AvgMem → Unfold := by
  intro hSec hAvg G _ _ _ _ _ W _ _ _ K ρ hK hρ _ _ μ hμ hpr Γ P c hpar φ Λ T hφ hLaw hΛ hT g u hu
    hb w
  haveI : CompactSpace K := isCompact_iff_compactSpace.mp hK
  haveI : CompleteSpace W := FiniteDimensional.complete ℂ W
  have hsec := (hSec G W K ρ hK hρ Γ P c hpar).1
  have hmem := hAvg G W K ρ hK hρ μ hμ hpr Γ P c hpar φ hφ hLaw w
  have key : ∀ q : Cos P Γ, ∃ (p : G) (κ₁ : K), p ∈ P ∧ rep q * g = p * κ₁ := fun q => by
    obtain ⟨p, hp, k, hk, e⟩ := hpar.iwa (rep q * g)
    exact ⟨p, ⟨k, hk⟩, hp, e⟩
  choose p κ₁ hp hpk using key
  have hterm : ∀ q (κ : K), T (rep q * (g * κ)) =
      (c (p q) * Complex.exp (Λ (p q))) * φ (κ₁ q * κ) := fun q κ => by
    have e : rep q * (g * (κ : G)) = p q * ((κ₁ q * κ : K) : G) := by
      rw [← mul_assoc, hpk q, Subgroup.coe_mul, mul_assoc]
    rw [e]
    exact hT _ (hp q) _
  have hc : ∀ q, Continuous fun κ : K => φ (κ₁ q * κ) := fun q =>
    hφ.comp (continuous_const.mul continuous_id)
  let f' : Cos P Γ → C(K, ℂ) := fun q => ⟨fun κ => φ (κ₁ q * κ), hc q⟩
  let f : Cos P Γ → C(K, ℂ) := fun q => (c (p q) * Complex.exp (Λ (p q))) • f' q
  have hfa : ∀ q κ, f q κ = T (rep q * (g * κ)) := fun q κ => by
    rw [hterm]
    simp [f, f']
  have hu0 : ∀ q, 0 ≤ u q := fun q => (norm_nonneg _).trans (hb q 1)
  have hsum : Summable f := Summable.of_norm_bounded hu fun q =>
    (ContinuousMap.norm_le _ (hu0 q)).2 fun κ => by
      rw [hfa]
      exact hb q κ
  obtain ⟨A, hA⟩ := exists_avgCLM μ hρ
  have hF : (fun κ : K => ∑' q : Cos P Γ, T (rep q * (g * κ))) = ⇑(∑' q, f q) := by
    funext κ
    rw [← ContinuousMap.tsum_apply hsum]
    exact tsum_congr fun q => (hfa q κ).symm
  rw [hF, ← hA]
  have hL := ((ContinuousLinearMap.apply ℂ W w).comp A).map_tsum hsum
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.apply_apply] at hL
  rw [hL]
  unfold eis
  refine tsum_congr fun q => ?_
  have e1 : A (f q) w = (c (p q) * Complex.exp (Λ (p q))) • (ρ (κ₁ q)⁻¹ (avg μ ρ φ w)) := by
    have : A (f' q) = ρ (κ₁ q)⁻¹ * avg μ ρ φ := by
      rw [hA]
      exact avg_translate μ hρ hφ (κ₁ q)
    have e2 : A (f q) = (c (p q) * Complex.exp (Λ (p q))) • A (f' q) := map_smul A _ _
    rw [e2, this]
    rfl
  rw [e1, hpk q, hΛ _ _ (κ₁ q).2, hsec _ hmem _ (hp q), smul_smul, mul_comm]

end GlobalTheory.CompanionTheory.RgEisUnfold
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ValEqOneOfMulEq
section
noncomputable section

open NumberField IsDedekindDomain

namespace GlobalTheory.CompanionTheory.EisTF

open PositivityTheory.RgEis PositivityTheory.RgEis.TF GroundTheory.Global

theorem val_eq_one_of_mul_eq {F Γ : Type*} [Field F] [LinearOrderedCommGroupWithZero Γ]
    (w : Valuation F Γ) {a b u u' m mi y : F} (ha : w a ≤ 1) (hb : w b ≤ 1) (hu : w u ≤ 1)
    (hu' : w u' ≤ 1) (huu : u * u' = 1) (hy : w y ≤ 1) (hm : m * mi = 1) (hmi : 1 < w mi)
    (h : a * b - u = m * y) : w a = 1 := by
  have key : ∀ {p q : Γ}, p ≤ 1 → q ≤ 1 → p * q = 1 → p = 1 := by
    intro p q hp hq hpq
    refine le_antisymm hp (not_lt.mp fun hc => ?_)
    have h2 : p * q < 1 := lt_of_le_of_lt (mul_le_of_le_one_right' hq) hc
    rw [hpq] at h2
    exact lt_irrefl _ h2
  have hwu : w u = 1 := key hu hu' (by rw [← map_mul, huu, map_one])
  have hwm : w m < 1 := by
    refine not_le.mp fun hc => ?_
    have h1 : w m * w mi = 1 := by rw [← map_mul, hm, map_one]
    have h2 : w mi ≤ w m * w mi := le_mul_of_one_le_left' hc
    rw [h1] at h2
    exact absurd hmi (not_lt.mpr h2)
  have hmy : w (m * y) < w u := by
    rw [map_mul, hwu]
    exact lt_of_le_of_lt (mul_le_of_le_one_right' hy) hwm
  have hab : a * b = m * y + u := sub_eq_iff_eq_add.mp h
  have hprod : w a * w b = 1 := by
    rw [← map_mul, hab, Valuation.map_add_eq_of_lt_right _ hmy, hwu]
  exact key ha hb hprod

theorem liftUnit : LiftUnit := by
  intro k _ _ M hM a ha b hb u hu hab
  obtain ⟨y, hy, hyeq⟩ := hab
  classical
  have hint : ∀ x : FiniteAdeleRing (𝓞 k) k, x ∈ OH k →
      ∀ v : HeightOneSpectrum (𝓞 k), Valued.v (x v) ≤ 1 :=
    fun x hx v => (HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 k) k v).mp (hx v)
  have hM0 : ∀ v : HeightOneSpectrum (𝓞 k), (M : v.adicCompletion k) ≠ 0 := by
    intro v
    rw [← map_natCast (algebraMap k (v.adicCompletion k)) M]
    exact (map_ne_zero _).mpr (Nat.cast_ne_zero.mpr hM)
  have hMle : ∀ v : HeightOneSpectrum (𝓞 k), Valued.v (M : v.adicCompletion k) ≤ 1 := fun v =>
    (HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 k) k v).mp (natCast_mem _ M)
  obtain ⟨huU1, huU2⟩ := Subgroup.mem_comap.mp hu
  have hu1 : (u : FiniteAdeleRing (𝓞 k) k) ∈ OH k := fun v => huU1 v
  have hu2 : ((u⁻¹ : (FiniteAdeleRing (𝓞 k) k)ˣ) : FiniteAdeleRing (𝓞 k) k) ∈ OH k :=
    fun v => huU2 v
  have hunit : ∀ v : HeightOneSpectrum (𝓞 k), Valued.v (M : v.adicCompletion k) < 1 →
      Valued.v (a v) = 1 := by
    intro v hv
    have hmul : (u : FiniteAdeleRing (𝓞 k) k) v *
        ((u⁻¹ : (FiniteAdeleRing (𝓞 k) k)ˣ) : FiniteAdeleRing (𝓞 k) k) v = 1 :=
      congrArg (fun z : FiniteAdeleRing (𝓞 k) k => z v) (Units.mul_inv u)
    have hcomp : a v * b v - (u : FiniteAdeleRing (𝓞 k) k) v = (M : v.adicCompletion k) * y v :=
      congrArg (fun z : FiniteAdeleRing (𝓞 k) k => z v) hyeq
    exact val_eq_one_of_mul_eq Valued.v (hint a ha v) (hint b hb v) (hint _ hu1 v) (hint _ hu2 v)
      hmul (hint y hy v) (mul_inv_cancel₀ (hM0 v))
      ((Valuation.one_lt_val_iff Valued.v (inv_ne_zero (hM0 v))).mpr (by rwa [inv_inv])) hcomp
  let f : ∀ v : HeightOneSpectrum (𝓞 k), v.adicCompletion k := fun v =>
    if Valued.v (M : v.adicCompletion k) < 1 then a v else 1
  let g : ∀ v : HeightOneSpectrum (𝓞 k), v.adicCompletion k := fun v =>
    if Valued.v (M : v.adicCompletion k) < 1 then (a v)⁻¹ else 1
  have hf : ∀ v : HeightOneSpectrum (𝓞 k), f v ∈ v.adicCompletionIntegers k := by
    intro v
    by_cases hv : Valued.v (M : v.adicCompletion k) < 1
    · simp only [f, if_pos hv]
      exact ha v
    · simp only [f, if_neg hv]
      exact one_mem _
  have hg : ∀ v : HeightOneSpectrum (𝓞 k), g v ∈ v.adicCompletionIntegers k := by
    intro v
    by_cases hv : Valued.v (M : v.adicCompletion k) < 1
    · simp only [g, if_pos hv]
      rw [HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 k) k v, map_inv₀, hunit v hv, inv_one]
    · simp only [g, if_neg hv]
      exact one_mem _
  let F : FiniteAdeleRing (𝓞 k) k := RestrictedProduct.mk f (Filter.Eventually.of_forall hf)
  let G : FiniteAdeleRing (𝓞 k) k := RestrictedProduct.mk g (Filter.Eventually.of_forall hg)
  have hFG : F * G = 1 := by
    refine RestrictedProduct.ext _ _ fun v => ?_
    show f v * g v = 1
    by_cases hv : Valued.v (M : v.adicCompletion k) < 1
    · simp only [f, g, if_pos hv]
      refine mul_inv_cancel₀ fun h0 => ?_
      have h1 := hunit v hv
      rw [h0, map_zero] at h1
      exact zero_ne_one h1
    · simp only [f, g, if_neg hv, mul_one]
  have hGF : G * F = 1 := by
    rw [mul_comm]
    exact hFG
  let U : (FiniteAdeleRing (𝓞 k) k)ˣ := ⟨F, G, hFG, hGF⟩
  have hU : U ∈ finiteIntegralUnits k :=
    Subgroup.mem_comap.mpr
      (Submonoid.mem_units_of_val_mem_inv_val_mem _ (fun v => hf v) (fun v => hg v))
  refine ⟨U, hU, ?_⟩
  let Y : ∀ v : HeightOneSpectrum (𝓞 k), v.adicCompletion k := fun v =>
    if Valued.v (M : v.adicCompletion k) < 1 then 0 else (a v - 1) * (M : v.adicCompletion k)⁻¹
  have hY : ∀ v : HeightOneSpectrum (𝓞 k), Y v ∈ v.adicCompletionIntegers k := by
    intro v
    by_cases hv : Valued.v (M : v.adicCompletion k) < 1
    · simp only [Y, if_pos hv]
      exact zero_mem _
    · simp only [Y, if_neg hv]
      have hM1 : Valued.v (M : v.adicCompletion k) = 1 := le_antisymm (hMle v) (not_lt.mp hv)
      rw [HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 k) k v, map_mul, map_inv₀, hM1, inv_one,
        mul_one]
      exact (Valuation.map_sub Valued.v (a v) 1).trans
        (max_le (hint a ha v) (Valuation.map_one Valued.v).le)
  refine ⟨RestrictedProduct.mk Y (Filter.Eventually.of_forall hY), fun v => hY v, ?_⟩
  refine RestrictedProduct.ext _ _ fun v => ?_
  show a v - f v = (M : v.adicCompletion k) * Y v
  by_cases hv : Valued.v (M : v.adicCompletion k) < 1
  · simp only [f, Y, if_pos hv, sub_self, mul_zero]
  · simp only [f, Y, if_neg hv]
    rw [mul_comm, mul_assoc, inv_mul_cancel₀ (hM0 v), mul_one]

end GlobalTheory.CompanionTheory.EisTF
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.VecKapMul
section
noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open scoped NumberField.AdeleRing
open GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.GodementSection
open PositivityTheory.RgEis PositivityTheory.RgEis.MG

namespace GlobalTheory.CompanionTheory.RgEisTerm

section Lin

variable {R : Type} [CommRing R] {ι : Type} [Fintype ι] [DecidableEq ι]

theorem stab_diag_mul {i : ι} {g : GL ι R} (hg : g ∈ stab R ({i} : Set ι)) :
    (g : Matrix ι ι R) i i * ((g⁻¹ : GL ι R) : Matrix ι ι R) i i = 1 := by
  have h : ((g * g⁻¹ : GL ι R) : Matrix ι ι R) i i = 1 := by simp
  rw [Units.val_mul, Matrix.mul_apply, Finset.sum_eq_single i] at h
  · exact h
  · intro b _ hb
    rw [(hg b (by simpa using hb) i rfl).2, mul_zero]
  · intro h'; exact absurd (Finset.mem_univ i) h'

theorem det_uniq {n R : Type} [CommRing R] [Unique n] [DecidableEq n] (F : Fintype n) (A : Matrix n n R) :
    @Matrix.det n _ F R _ A = A default default :=
  Matrix.det_unique A

theorem bdet_singleton {i : ι} {g : GL ι R} (hg : g ∈ stab R ({i} : Set ι)) :
    ((bdet ({i} : Set ι) g : Rˣ) : R) = (g : Matrix ι ι R) i i := by
  classical
  unfold bdet
  split_ifs with h
  · rw [IsUnit.unit_spec, det_uniq]; rfl
  · refine absurd ?_ h
    rw [det_uniq]
    exact IsUnit.of_mul_eq_one _ (stab_diag_mul hg)

theorem bdet_inv_singleton {i : ι} {g : GL ι R} (hg : g ∈ stab R ({i} : Set ι)) :
    (((bdet ({i} : Set ι) g)⁻¹ : Rˣ) : R) = ((g⁻¹ : GL ι R) : Matrix ι ι R) i i :=
  Units.inv_eq_of_mul_eq_one_right (by rw [bdet_singleton hg]; exact stab_diag_mul hg)

theorem inv_mulVec_single {i : ι} {g : GL ι R} (hg : g ∈ stab R ({i} : Set ι)) :
    ((g⁻¹ : GL ι R) : Matrix ι ι R) *ᵥ Pi.single i 1 =
      (((bdet ({i} : Set ι) g)⁻¹ : Rˣ) : R) • (Pi.single i 1 : ι → R) := by
  funext r
  rw [Matrix.mulVec_single_one, bdet_inv_singleton hg]
  by_cases h : r = i
  · subst h; simp
  · have := (hg r (by simpa using h) i rfl).2
    rw [Pi.smul_apply, Pi.single_eq_of_ne h, smul_zero]
    exact this

end Lin

section ZetaNonvanishing₂

variable {k : Type} [Field k] [NumberField k] {ι : Type} [Fintype ι] [DecidableEq ι]

theorem modPow_eq_exp (x : IdeleGroup k) (s : ℂ) :
    modPow x s = Complex.exp (s * ((adStd k).lg x : ℝ)) := by
  have hpos : (0 : ℝ) < (IdeleGroup.ideleModule k x : ℝ) := (IdeleGroup.ideleModule k x).2
  have hne : ((IdeleGroup.ideleModule k x : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hpos.ne'
  rw [modPow, Complex.cpow_def_of_ne_zero hne, ← Complex.ofReal_log hpos.le, mul_comm]
  rfl

theorem modPow_inv_neg (x : IdeleGroup k) (s : ℂ) : modPow x⁻¹ (-s) = modPow x s := by
  have h1 : modPow x⁻¹ (-s) * modPow x (-s) = 1 := by
    rw [← modPow_mul, inv_mul_cancel, modPow_one]
  have h2 : modPow x (-s) * modPow x s = 1 := by
    rw [← modPow_add, neg_add_cancel]; simp [modPow]
  calc modPow x⁻¹ (-s) = modPow x⁻¹ (-s) * (modPow x (-s) * modPow x s) := by rw [h2, mul_one]
    _ = modPow x s := by rw [← mul_assoc, h1, one_mul]

theorem lineZeta_smul (Ψ : (ι → 𝔸[k]) → ℂ) (ω : HeckeCharacter k) (s : ℂ) (u : IdeleGroup k)
    (v : ι → 𝔸[k]) :
    lineZeta Ψ ω s ((u : 𝔸[k]) • v) =
      (((ω.toIdele u)⁻¹ : Circle) : ℂ) * modPow u (-s) * lineZeta Ψ ω s v := by
  have h := globalZeta_mul_right (fun t : 𝔸[k] => Ψ (t • v)) ω s u
  simp only [lineZeta, smul_smul, mul_comm] at h ⊢
  simpa only [mul_comm] using h

theorem lineZeta_inv_smul (Ψ : (ι → 𝔸[k]) → ℂ) (ω : HeckeCharacter k) (s : ℂ) (u : IdeleGroup k)
    (v : ι → 𝔸[k]) :
    lineZeta Ψ ω s (((u⁻¹ : IdeleGroup k) : 𝔸[k]) • v) =
      (ω.toIdele u : ℂ) * modPow u s * lineZeta Ψ ω s v := by
  rw [lineZeta_smul, modPow_inv_neg, map_inv, inv_inv]

theorem lineZeta_rat (Ψ : (ι → 𝔸[k]) → ℂ) (ω : HeckeCharacter k) (s : ℂ) (x : kˣ)
    (v : ι → 𝔸[k]) :
    lineZeta Ψ ω s (algebraMap k 𝔸[k] x • v) = lineZeta Ψ ω s v := by
  have h := lineZeta_smul Ψ ω s (IdeleGroup.diagonal k x) v
  rw [IdeleGroup.coe_diagonal] at h
  rw [h, HeckeCharacter.toIdele_diagonal]
  simp [modPow, IdeleGroup.ideleModule_diagonal]

end ZetaNonvanishing₂

section Main

variable {k : Type} [Field k] [NumberField k] {ι : Type} [Fintype ι] [DecidableEq ι] {G : Type} [Group G]

theorem dgl_inv_mulVec_single (d : ι → IdeleGroup k) (i : ι) :
    (((dgl d)⁻¹ : GL ι 𝔸[k]) : Matrix ι ι 𝔸[k]) *ᵥ Pi.single i 1 =
      (((d i)⁻¹ : IdeleGroup k) : 𝔸[k]) • (Pi.single i 1 : ι → 𝔸[k]) := by
  change Matrix.diagonal (fun i => (((d i)⁻¹ : IdeleGroup k) : 𝔸[k])) *ᵥ _ = _
  funext r
  rw [Matrix.mulVec_diagonal, Pi.smul_apply, smul_eq_mul]
  by_cases h : r = i
  · subst h; rfl
  · rw [Pi.single_eq_of_ne h, mul_zero, mul_zero]

theorem dgl_mulVec_single (d : ι → IdeleGroup k) (i : ι) :
    ((dgl d : GL ι 𝔸[k]) : Matrix ι ι 𝔸[k]) *ᵥ Pi.single i 1 =
      (d i : 𝔸[k]) • (Pi.single i 1 : ι → 𝔸[k]) := by
  change Matrix.diagonal (fun i => (d i : 𝔸[k])) *ᵥ _ = _
  funext r
  rw [Matrix.mulVec_diagonal, Pi.smul_apply, smul_eq_mul]
  by_cases h : r = i
  · subst h; rfl
  · rw [Pi.single_eq_of_ne h, mul_zero, mul_zero]

theorem vec_mul (π : G →* GL ι 𝔸[k]) (d : ι → IdeleGroup k) (i : ι) {p : G} (κ : G)
    (hp : π p ∈ stab 𝔸[k] ({i} : Set ι)) :
    MG.vec (π (p * κ) * dgl d) i =
      (((bdet ({i} : Set ι) (π p) * d i)⁻¹ : IdeleGroup k) : 𝔸[k]) • MG.vec (kap π d κ) i := by
  have hinv : (π (p * κ) * dgl d)⁻¹ = (kap π d κ)⁻¹ * ((dgl d)⁻¹ * (π p)⁻¹) := by
    simp only [kap, map_mul, _root_.mul_inv_rev, inv_inv, mul_assoc, inv_mul_cancel_left, mul_inv_cancel_left]
  have hs : (((bdet ({i} : Set ι) (π p) * d i)⁻¹ : IdeleGroup k) : 𝔸[k]) =
      (((d i)⁻¹ : IdeleGroup k) : 𝔸[k]) * (((bdet ({i} : Set ι) (π p))⁻¹ : IdeleGroup k) : 𝔸[k]) := by
    rw [← Units.val_mul, _root_.mul_inv_rev]
  unfold MG.vec
  rw [hinv, Units.val_mul, Units.val_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
    inv_mulVec_single hp, Matrix.mulVec_smul, dgl_inv_mulVec_single, smul_smul, Matrix.mulVec_smul, hs,
    mul_comm]

theorem vec_kap (π : G →* GL ι 𝔸[k]) (d : ι → IdeleGroup k) (i : ι) (g : G) :
    MG.vec (kap π d g) i = (d i : 𝔸[k]) • MG.vec (π g * dgl d) i := by
  have hinv : (kap π d g)⁻¹ = (π g * dgl d)⁻¹ * dgl d := by
    simp only [kap, _root_.mul_inv_rev, inv_inv, mul_assoc, inv_mul_cancel_left, inv_mul_cancel, mul_one]
  unfold MG.vec
  rw [hinv, Units.val_mul, ← Matrix.mulVec_mulVec, dgl_mulVec_single, Matrix.mulVec_smul]

theorem vec_kap_mul (π : G →* GL ι 𝔸[k]) (d : ι → IdeleGroup k) (i : ι) {r : G} (κ : G)
    (hr : π r ∈ stab 𝔸[k] ({i} : Set ι)) :
    MG.vec (kap π d (r * κ)) i =
      (((bdet ({i} : Set ι) (π r))⁻¹ : IdeleGroup k) : 𝔸[k]) • MG.vec (kap π d κ) i := by
  have hs : (d i : 𝔸[k]) * (((bdet ({i} : Set ι) (π r) * d i)⁻¹ : IdeleGroup k) : 𝔸[k]) =
      (((bdet ({i} : Set ι) (π r))⁻¹ : IdeleGroup k) : 𝔸[k]) := by
    rw [← Units.val_mul, _root_.mul_inv_rev, mul_comm (d i)⁻¹, mul_inv_cancel_comm_assoc]
  rw [vec_kap, vec_mul π d i κ hr, smul_smul, hs]

end Main

theorem term : Term := by
  intro G _ _ _ _ K _ k _ _ ι _ _ π Γ P i ω d c η S
  have hmem : ∀ p ∈ P, π p ∈ stab 𝔸[k] ({i} : Set ι) := fun p hp => (S.mem p).1 hp
  refine ⟨fun p hp κ _ => vec_mul π d i κ (hmem p hp), fun Ψ s => ⟨?_, ?_, fun x v => lineZeta_rat Ψ ω s x v⟩⟩
  · intro p hp κ _
    have hc := (S.val p hp).1
    have hη := (S.val p hp).2
    rw [vec_mul π d i κ (hmem p hp), lineZeta_inv_smul, map_mul, Circle.coe_mul, modPow_mul,
      modPow_eq_exp (bdet ({i} : Set ι) (π p)) s, hc, hη]
    simp only [zt]
    ring
  · intro r κ hr
    have hc := (S.val r hr).1
    have hη := (S.val r hr).2
    have h0 : η r = 0 := by
      have h1 := S.ht.right 1 r r.2
      have h2 := S.ht.left r hr 1
      rw [one_mul] at h1
      rw [mul_one] at h2
      linarith
    have hm : modPow (bdet ({i} : Set ι) (π r)) s = 1 := by
      rw [modPow_eq_exp, ← hη, h0]; simp
    show zt π d i Ψ ω s ((r * κ : K) : G) = c r * zt π d i Ψ ω s κ
    rw [Subgroup.coe_mul]
    simp only [zt]
    rw [vec_kap_mul π d i κ ((S.mem r).1 hr), lineZeta_inv_smul, hm, hc, mul_one]

end GlobalTheory.CompanionTheory.RgEisTerm
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.VolCharOneEq
section
open NumberField Matrix MeasureTheory Filter Topology
open scoped NumberField.AdeleRing
open PositivityTheory.He2M1 GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.GJMatrix IdeleGroup PositivityTheory.RgEis

namespace GlobalTheory.CompanionTheory.EpsteinVol

theorem volChar_one_eq {k : Type} [Field k] [NumberField k] :
    ∃ V : ℝ, 0 < V ∧ volChar (1 : HeckeCharacter k) = (V : ℂ) := by
  haveI := GroundTheory.Global.isHaarMeasure_normOneMeasure k
  haveI : Countable ↥(GroundTheory.Global.diagonalNormOne k).op := by
    haveI := GroundTheory.Global.countable_diagonalNormOne k
    refine Function.Injective.countable (f := fun x : ↥(GroundTheory.Global.diagonalNormOne k).op =>
      (⟨x.1.unop, Subgroup.mem_op.mp x.2⟩ : ↥(GroundTheory.Global.diagonalNormOne k))) ?_
    intro x y h
    apply Subtype.ext
    apply MulOpposite.unop_injective
    exact congrArg Subtype.val h
  have hfin : GroundTheory.Global.normOneMeasure k (GroundTheory.Global.normOneFundamentalDomain k) < ⊤ :=
    GroundTheory.Global.normOneMeasure_normOneFundamentalDomain_lt_top k
  have hne : GroundTheory.Global.normOneMeasure k (GroundTheory.Global.normOneFundamentalDomain k) ≠ 0 :=
    (GroundTheory.Global.isFundamentalDomain_normOneFundamentalDomain k
      (GroundTheory.Global.normOneMeasure k)).measure_ne_zero (NeZero.ne _)
  refine ⟨(GroundTheory.Global.normOneMeasure k (GroundTheory.Global.normOneFundamentalDomain k)).toReal,
    ENNReal.toReal_pos hne hfin.ne, ?_⟩
  have h2 : volChar (1 : HeckeCharacter k) =
      ∫ _u in GroundTheory.Global.normOneFundamentalDomain k, (1 : ℂ) ∂GroundTheory.Global.normOneMeasure k := by
    unfold volChar
    congr 1
  rw [h2, MeasureTheory.setIntegral_const]
  simp [Measure.real]

end GlobalTheory.CompanionTheory.EpsteinVol
end

