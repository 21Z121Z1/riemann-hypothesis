import Mathlib
import Formalism.PeriodIntegrals.Bundle0022
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.PseudoCoefficientSeparation
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Formalism.RealPlaceAnalysis.Bundle0003
import Formalism.RealPlaceAnalysis.Bundle0002
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0253
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0016
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0006
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.OffQOfSizeRows
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FactTypePrime
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0101
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0114
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdelicPointComponentsAtPlacesLatticesVacua
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0249
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemHomLatticeCompletionIffSupportedMaps
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0257
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0224
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0051
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0991

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.KStableSubspaceExponentFunctional
section
open MeasureTheory Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.FlagMeas GlobalTheory.GKModule GlobalTheory.RealInd GlobalTheory.OpTrace
open GlobalTheory.SmoothGlob (lieSet)
open GlobalTheory.Dec (IsHaarSub HasInfChar UEquiv gelfVal)
open GlobalTheory.Orb (IsPseudoCoeff ujMat ujRep)
open scoped InnerProductSpace
open PI.DSInfCharCap (actU Egl)

namespace GlobalTheory.IndFunctional

theorem exists_factor {A H : Type} [AddCommGroup A] [Module ℂ A] [AddCommGroup H] [Module ℂ H]
    (ι : A →ₗ[ℂ] H) (L : A →ₗ[ℂ] ℂ) (hL : ∀ a, ι a = 0 → L a = 0) :
    ∃ ℓ : H →ₗ[ℂ] ℂ, ∀ a, ℓ (ι a) = L a := by
  have hle : LinearMap.ker ι ≤ LinearMap.ker L := fun a ha => hL a ha
  obtain ⟨ℓ, hℓ⟩ := LinearMap.exists_extend
    (((LinearMap.ker ι).liftQ L hle).comp ι.quotKerEquivRange.symm.toLinearMap)
  refine ⟨ℓ, fun a => ?_⟩
  have := LinearMap.congr_fun hℓ ⟨ι a, LinearMap.mem_range_self ι a⟩
  simp only [LinearMap.comp_apply, Submodule.subtype_apply, LinearEquiv.coe_coe,
    LinearMap.quotKerEquivRange_symm_apply_image] at this
  rw [this]
  rfl

theorem apply_one_eq_zero {n : ℕ} {ε : Fin n → Bool} (I : IndModule ε) (f : I.fns) (hf : I.ι f = 0) :
    f.1 1 = 0 := by
  have hc : Continuous f.1 := (mem_indFun_top.1 f.2).1
  have hck : Continuous fun k : KG ε => ‖f.1 k‖ ^ 2 := (hc.comp continuous_subtype_val).norm.pow 2
  have hint : Integrable (fun k : KG ε => ‖f.1 k‖ ^ 2) (muK ε) :=
    hck.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have h0 : ∫ k : KG ε, ‖f.1 k‖ ^ 2 ∂muK ε = 0 := by
    rw [← I.model.norm_sq f, hf, norm_zero]; norm_num
  have hae := (integral_eq_zero_iff_of_nonneg (fun k => by positivity) hint).1 h0
  have heq : (fun k : KG ε => ‖f.1 k‖ ^ 2) = fun _ => 0 :=
    (Continuous.ae_eq_iff_eq (muK ε) hck continuous_const).1 hae
  have := congrFun heq ⟨1, (KG ε).one_mem⟩
  simpa using this

theorem functional : GlobalTheory.Published.Langlands.Induced → ∀ (n : ℕ) (ε : Fin n → Bool) (I : IndModule ε) (h : 0 < I.a), I.j ⟨0, h⟩ = 1 → ∀ H₀ T : Matrix (Fin n) (Fin n) ℂ, H₀ ∈ lieSet ε → T ∈ lieSet ε → (∀ x : ℝ, IsSplit ε I.W (Pi.single ⟨0, h⟩ x) (expG ε H₀ x)) → (∀ θ : ℝ, expG ε T θ ∈ KG ε ⊓ I.M ∧ ∀ m ∈ I.M, expG ε T θ * m = m * expG ε T θ) → ∀ Y : Submodule ℂ I.H, Y ≤ kFinVec ε I.ρ → Y ≠ ⊥ → IsKStableOn ε I.ρ Y → ∃ (ℓ : I.H →ₗ[ℂ] ℂ) (γ : ℂ), (∃ y ∈ Y, ℓ y ≠ 0) ∧ (∀ X ∈ lieSet ε, (∀ t, expG ε X t ∈ flagN ε I.W) → ∀ w ∈ kFinVec ε I.ρ, ℓ (dRep I.ρ X w) = 0) ∧ (∀ w ∈ kFinVec ε I.ρ, ℓ (dRep I.ρ H₀ w) = (I.s ⟨0, h⟩ + n - 1) * ℓ w) ∧ ∀ w ∈ kFinVec ε I.ρ, ℓ (dRep I.ρ T w) = γ * ℓ w := by
  intro hInd n ε I h hj H₀ T hH₀ hT hsp hTθ Y hYk hY0 hYs
  obtain ⟨-, -, -, hkf, hder, -⟩ := hInd n ε I
  obtain ⟨hσ, -⟩ := I.temp.2.2
  have huM1 : uMat (1 : UJ ε) = 1 := rfl
  have hσ1 : I.σ 1 = 1 := hσ.1.1
  have hσmul : ∀ a ∈ I.M, ∀ b ∈ I.M, I.σ (uMat (a * b)) = (I.σ (uMat a)).comp (I.σ (uMat b)) :=
    fun a ha b hb => hσ.1.2 _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
  have hσiso : ∀ m ∈ I.M, ∀ x, ‖I.σ (uMat m) x‖ = ‖x‖ := fun m hm x => hσ.2.1 _ ⟨m, hm, rfl⟩ x
  have hinner : ∀ m ∈ I.M, ∀ a b, ⟪I.σ (uMat m) a, I.σ (uMat m) b⟫_ℂ = ⟪a, b⟫_ℂ := fun m hm a b =>
    (⟨(I.σ (uMat m)).toLinearMap, hσiso m hm⟩ : I.V →ₗᵢ[ℂ] I.V).inner_map_map a b
  have hN1 : (1 : UJ ε) ∈ flagN ε I.W := ⟨fun i y _ => by simp [huM1], fun y _ => by simp [huM1]⟩
  have law : ∀ f : I.fns, ∀ u ∈ flagN ε I.W, ∀ m ∈ I.M, ∀ x t, IsSplit ε I.W x t →
      f.1 (u * m * t) = Complex.exp (pairing I.j (I.s + rho n I.j) x) • I.σ (uMat m) (f.1 1) := by
    intro f u hu m hm x t ht
    simpa using (mem_indFun_top.1 f.2).2 u hu m hm x t ht 1
  have law0 : ∀ f : I.fns, ∀ u ∈ flagN ε I.W, ∀ m ∈ I.M, f.1 (u * m) = I.σ (uMat m) (f.1 1) := by
    intro f u hu m hm
    simpa [pairing] using law f u hu m hm 0 1 isSplit_one
  have kf : ∀ w ∈ kFinVec ε I.ρ, ∃ f : I.fns, IsKFinFun f.1 ∧ I.ι f = w := fun w hw => (hkf w).1 hw
  have dat1 : ∀ X ∈ lieSet ε, ∀ w ∈ kFinVec ε I.ρ, ∃ f f' : I.fns, I.ι f = w ∧ I.ι f' = dRep I.ρ X w ∧
      HasDerivAt (fun t : ℝ => f.1 (expG ε X t)) (f'.1 1) 0 := by
    intro X hX w hw
    obtain ⟨f, hfk, rfl⟩ := kf w hw
    obtain ⟨f', hd, he⟩ := hder f hfk X hX
    exact ⟨f, f', rfl, he.symm, by simpa using hd 1⟩

  obtain ⟨y, hyY, hy0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hY0
  obtain ⟨f, hfk, rfl⟩ := kf y (hYk hyY)
  have hf0 : f.1 ≠ 0 := fun e => hy0 (by rw [show f = 0 from Subtype.ext e, map_zero])
  obtain ⟨k₀, hk₀, hfk₀⟩ := (GlobalTheory.T.induced_k_finite_restriction n ε I.toDatum f.1 f.2 hfk).2.2 hf0
  let f₁ : I.fns := ⟨fun g => f.1 (g * k₀), indFun_mul_right f.2 trivial⟩
  have hf₁k : IsKFinFun f₁.1 := by
    have hle : Submodule.span ℂ {φ : UJ ε → I.V | ∃ k ∈ KG ε, φ = fun g => f₁.1 (g * k)} ≤
        Submodule.span ℂ {φ : UJ ε → I.V | ∃ k ∈ KG ε, φ = fun g => f.1 (g * k)} := by
      refine Submodule.span_mono ?_
      rintro φ ⟨k, hk, rfl⟩
      exact ⟨k * k₀, mul_mem hk hk₀, by funext g; simp [f₁, mul_assoc]⟩
    haveI : FiniteDimensional ℂ (Submodule.span ℂ {φ : UJ ε → I.V | ∃ k ∈ KG ε, φ = fun g => f.1 (g * k)}) := hfk
    exact Submodule.finiteDimensional_of_le hle
  have hy₁ : I.ρ (uMat k₀) (I.ι f) = I.ι f₁ := I.model.transl k₀ trivial f f₁ fun g => rfl
  have hy₁Y : I.ι f₁ ∈ Y := hy₁ ▸ hYs (uMat k₀) hk₀ _ hyY
  have hx₀ : f₁.1 1 ≠ 0 := by simpa [f₁] using hfk₀
  obtain ⟨U, hUfd, hx₀U, hUst⟩ := (GlobalTheory.T.induced_k_finite_restriction n ε I.toDatum f₁.1 f₁.2 hf₁k).2.1

  have hum : ∀ θ, (expG ε T θ)⁻¹ ∈ KG ε ⊓ I.M := fun θ => inv_mem (hTθ θ).1
  obtain ⟨v, -, hvx, hv⟩ := GlobalTheory.T.commuting_isometries_common_eigenvector U hUfd (fun θ => I.σ (uMat (expG ε T θ)⁻¹)) (f₁.1 1) hx₀U hx₀
    (fun θ x hx => hUst _ (hum θ) x hx) (fun θ x => hσiso _ (hum θ).2 x) (fun θ θ' x => by
      rw [← ContinuousLinearMap.comp_apply, ← hσmul _ (hum θ).2 _ (hum θ').2, ← ContinuousLinearMap.comp_apply,
        ← hσmul _ (hum θ').2 _ (hum θ).2, (Commute.inv_left ((hTθ θ).2 _ (hum θ').2)).eq])
  choose c hc using hv
  have key : ∀ θ x, ⟪v, I.σ (uMat (expG ε T θ)) x⟫_ℂ = starRingEnd ℂ (c θ) * ⟪v, x⟫_ℂ := by
    intro θ x
    have h1 : I.σ (uMat (expG ε T θ)⁻¹) (I.σ (uMat (expG ε T θ)) x) = x := by
      rw [← ContinuousLinearMap.comp_apply, ← hσmul _ (hum θ).2 _ (hTθ θ).1.2, inv_mul_cancel, huM1, hσ1]
      rfl
    rw [← hinner _ (hum θ).2, h1, hc θ, inner_smul_left]

  obtain ⟨ℓ, hℓ⟩ := exists_factor I.ι ((innerSL ℂ v).toLinearMap ∘ₗ (LinearMap.proj 1) ∘ₗ I.fns.subtype)
    (fun a ha => by simp [apply_one_eq_zero I a ha])
  have hℓ' : ∀ a : I.fns, ℓ (I.ι a) = ⟪v, a.1 1⟫_ℂ := fun a => by rw [hℓ]; rfl
  have hinD : ∀ {F : ℝ → I.V} {F' : I.V}, HasDerivAt F F' 0 → HasDerivAt (fun t => ⟪v, F t⟫_ℂ) ⟪v, F'⟫_ℂ 0 :=
    fun hF => (((innerSL ℂ v).restrictScalars ℝ).hasFDerivAt).comp_hasDerivAt (0 : ℝ) hF
  have lawT : ∀ (g : I.fns) θ, ⟪v, g.1 (expG ε T θ)⟫_ℂ = starRingEnd ℂ (c θ) * ⟪v, g.1 1⟫_ℂ := by
    intro g θ
    have := law0 g 1 hN1 _ (hTθ θ).1.2
    rw [one_mul] at this
    rw [this, key]

  obtain ⟨f₁', hd₁, -⟩ := hder f₁ hf₁k T hT
  set γ := ⟪v, f₁'.1 1⟫_ℂ / ⟪v, f₁.1 1⟫_ℂ
  have hg : HasDerivAt (fun θ : ℝ => starRingEnd ℂ (c θ)) γ 0 := by
    have := (hinD (by simpa using hd₁ 1)).div_const ⟪v, f₁.1 1⟫_ℂ
    have e : (fun θ : ℝ => starRingEnd ℂ (c θ)) = fun θ => ⟪v, f₁.1 (expG ε T θ)⟫_ℂ / ⟪v, f₁.1 1⟫_ℂ := by
      funext θ
      rw [lawT, mul_div_assoc, div_self hvx, mul_one]
    rw [e]
    exact this
  refine ⟨ℓ, γ, ⟨I.ι f₁, hy₁Y, by rw [hℓ']; exact hvx⟩, ?_, ?_, ?_⟩
  · intro X hX hXN w hw
    obtain ⟨g, g', rfl, he, hd⟩ := dat1 X hX w hw
    rw [← he, hℓ']
    have hconst : (fun t : ℝ => g.1 (expG ε X t)) = fun _ => g.1 1 := funext fun t => by
      simpa [huM1, hσ1] using law0 g _ (hXN t) 1 (one_mem _)
    rw [hconst] at hd
    rw [hd.unique (hasDerivAt_const _ _), inner_zero_right]
  · intro w hw
    obtain ⟨g, g', rfl, he, hd⟩ := dat1 H₀ hH₀ w hw
    rw [← he, hℓ', hℓ']
    have hIio : Finset.Iio (⟨0, h⟩ : Fin I.a) = ∅ := by
      ext l; simp [Fin.lt_iff_val_lt_val]
    have hpair : ∀ t : ℝ, pairing I.j (I.s + rho n I.j) (Pi.single ⟨0, h⟩ t) = (I.s ⟨0, h⟩ + n - 1) * t := by
      intro t
      rw [pairing, Finset.sum_eq_single ⟨0, h⟩]
      · simp [hj, rho, hIio]
        left; ring
      · intro b _ hb; simp [Pi.single_apply, hb]
      · simp
    have hfun : (fun t : ℝ => g.1 (expG ε H₀ t)) = fun t : ℝ => Complex.exp ((I.s ⟨0, h⟩ + n - 1) * t) • g.1 1 :=
      funext fun t => by
        have := law g 1 hN1 1 (one_mem _) _ _ (hsp t)
        rw [one_mul, one_mul, hpair, huM1, hσ1] at this
        simpa using this
    rw [hfun] at hd
    have hd' : HasDerivAt (fun t : ℝ => Complex.exp ((I.s ⟨0, h⟩ + n - 1) * t) • g.1 1)
        ((I.s ⟨0, h⟩ + n - 1) • g.1 1) 0 := by
      have := (((hasDerivAt_id (0 : ℝ)).ofReal_comp.const_mul (I.s ⟨0, h⟩ + n - 1)).cexp).smul_const (g.1 1)
      simpa using this
    rw [hd.unique hd', inner_smul_right]
  · intro w hw
    obtain ⟨g, g', rfl, he, hd⟩ := dat1 T hT w hw
    rw [← he, hℓ', hℓ']
    have h2 := hinD hd
    have h3 : HasDerivAt (fun θ : ℝ => ⟪v, g.1 (expG ε T θ)⟫_ℂ) (γ * ⟪v, g.1 1⟫_ℂ) 0 := by
      have e : (fun θ : ℝ => ⟪v, g.1 (expG ε T θ)⟫_ℂ) = fun θ => starRingEnd ℂ (c θ) * ⟪v, g.1 1⟫_ℂ := by
        funext θ
        rw [lawT]
      rw [e]
      exact hg.mul_const ⟪v, g.1 1⟫_ℂ
    exact h2.unique h3

end GlobalTheory.IndFunctional
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LatticeStabilizerAtPlaceMemDepthCongruenceGridNo
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000
noncomputable section
namespace GlobalTheory.LevelOffS

variable {D : D7}

theorem valued_algebraMap {v : GlobalTheory.FinPl.Pl D} (y : D.host.F) :
    Valued.v (algebraMap D.host.F (v.adicCompletion D.host.F) y) = v.valuation D.host.F y :=
  HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v y

theorem inv_int {v : GlobalTheory.FinPl.Pl D} {c : 𝓞 D.host.F} (hc : c ∉ v.asIdeal) :
    evalV D.host.F v (algebraMap D.host.F (Af D.host.F) (algebraMap (𝓞 D.host.F) D.host.F c)⁻¹) ∈
      v.adicCompletionIntegers D.host.F := by
  rw [AlgHom.commutes, HeightOneSpectrum.mem_adicCompletionIntegers]
  have h1 : v.intValuation c = 1 := le_antisymm (v.intValuation_le_one c)
    (not_lt.1 fun h => hc ((v.intValuation_lt_one_iff_mem c).1 h))
  have h2 : Valued.v (algebraMap D.host.F (v.adicCompletion D.host.F) (algebraMap (𝓞 D.host.F) D.host.F c)) = 1 := by
    rw [valued_algebraMap]
    exact (HeightOneSpectrum.valuation_of_algebraMap v c).trans h1
  rw [map_inv₀, map_inv₀, h2, inv_one]

theorem coe_ne_zero_of_nmem {v : GlobalTheory.FinPl.Pl D} {c : 𝓞 D.host.F} (hc : c ∉ v.asIdeal) :
    algebraMap (𝓞 D.host.F) D.host.F c ≠ 0 := by
  intro h
  apply hc
  rw [show c = 0 from IsFractionRing.injective (𝓞 D.host.F) D.host.F (h.trans (map_zero _).symm)]
  exact zero_mem _

theorem smul_pairA (r : D.host.F) (α : Af D.host.F) : r • pairA D.host.F 0 α = pairA D.host.F 0 (r • α) :=
  Prod.ext (smul_zero (A := Ainf D.host.F) r) rfl

theorem smul_vec_apply (c : 𝓞 D.host.F) {n : ℕ} (x : Fin n → D.host.E) (i : Fin n) :
    (algebraMap (𝓞 D.host.F) (𝓞 D.host.E) c • x) i = algebraMap (𝓞 D.host.F) D.host.F c • x i := by
  rw [Pi.smul_apply, Algebra.smul_def, Algebra.smul_def]
  congr 1

theorem latV_le_smul {S : HSp D} (Λ : Lat S) {v : GlobalTheory.FinPl.Pl D} (𝔪 : Ideal (𝓞 D.host.E)) {c : 𝓞 D.host.F}
    (hc : c ∉ v.asIdeal) (hcm : algebraMap (𝓞 D.host.F) (𝓞 D.host.E) c ∈ 𝔪) :
    latV S Λ (· = v) ≤ latV S (𝔪 • Λ) (· = v) := by
  unfold GlobalTheory.FinPl.latV GlobalTheory.FinPl.latMul
  rw [AddSubgroup.closure_le]
  rintro _ ⟨α, hα, hαv, a, ha, x, hx, rfl⟩
  rw [Set.mem_singleton_iff] at ha
  subst ha
  set cF : D.host.F := algebraMap (𝓞 D.host.F) D.host.F c with hcF
  have hc0 : cF ≠ 0 := coe_ne_zero_of_nmem hc
  refine AddSubgroup.subset_closure ⟨α * algebraMap D.host.F (Af D.host.F) cF⁻¹, fun w => ?_, fun w hw => ?_, 1, rfl,
    algebraMap (𝓞 D.host.F) (𝓞 D.host.E) c • x, Submodule.smul_mem_smul hcm hx, ?_⟩
  · rw [map_mul]
    by_cases hw : w = v
    · subst hw
      exact mul_mem (hα w) (inv_int hc)
    · rw [hαv w hw, zero_mul]
      exact zero_mem _
  · rw [map_mul, hαv w hw, zero_mul]
  · funext i
    rw [smul_vec_apply, one_mul, one_mul, ← TensorProduct.smul_tmul, smul_pairA]
    congr 2
    rw [Algebra.smul_def, mul_left_comm, ← map_mul, mul_inv_cancel₀ hc0, map_one, mul_one]

theorem finPart_finIn (z : Af D.host.F ⊗[D.host.F] D.host.E) : finPart D (GlobalTheory.FinPlLoc.finIn D z) = z := by
  induction z using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero]
  | tmul a e => rw [GlobalTheory.FinPlLoc.finIn_tmul, GlobalTheory.FinPlLoc.finPart_pair]
  | add x y hx hy => rw [map_add, map_add, hx, hy]

theorem finIn_mem_idAt (z : Af D.host.F ⊗[D.host.F] D.host.E) : GlobalTheory.FinPlLoc.finIn D z ∈ idAt D (fun _ => True) := by
  unfold GlobalTheory.FinPl.idAt
  exact Ideal.mem_inf.2 ⟨RingHom.mem_ker.2 (GlobalTheory.FinPlLoc.infPart_finIn z),
    (Submodule.mem_iInf _).2 fun w => absurd trivial w.2⟩

theorem hatL_mono {n : ℕ} {Λ Λ' : Submodule (𝓞 D.host.E) (Fin n → D.host.E)} (h : Λ ≤ Λ') :
    Formalism.L2.Herm.hatL (F := D.host.F) Λ ≤ Formalism.L2.Herm.hatL (F := D.host.F) Λ' :=
  Submodule.span_mono (Set.image_mono h)

theorem mem_GfC_of_grpAt {S : HSp D} {P : GlobalTheory.FinPl.Pl D → Prop} {κ : GA D S} (h : κ ∈ grpAt S P) : κ ∈ GfC S := by
  unfold GlobalTheory.FinPl.grpAt at h
  rw [GlobalTheory.FinPlLoc.mem_congGrp] at h
  show infHom S κ = 1
  apply Units.ext
  ext i j
  have h1 := GlobalTheory.FinPlLoc.infPart_of_idAt (h i j)
  rw [map_sub, sub_eq_zero] at h1
  change infPart D (mt S κ i j) = (1 : Matrix (Fin S.rank) (Fin S.rank) (Ainf D.host.F ⊗[D.host.F] D.host.E)) i j
  rw [h1, Matrix.one_apply, Matrix.one_apply]
  split_ifs <;> simp

theorem finE_coe {S : HSp D} (κ : GA D S) :
    ((Lev.finE S κ : GL (Fin S.rank) (Lev.EAf D)) : Matrix (Fin S.rank) (Fin S.rank) (Lev.EAf D)) =
      (mt S κ).map ((Lev.swapAE D).comp (finPart D)) := rfl

theorem sub_mem_hatL_of_inK {S : HSp D} (Λ : Lat S) {v : GlobalTheory.FinPl.Pl D} (𝔪 : Ideal (𝓞 D.host.E)) {c : 𝓞 D.host.F}
    (hc : c ∉ v.asIdeal) (hcm : algebraMap (𝓞 D.host.F) (𝓞 D.host.E) c ∈ 𝔪) {κ : GA D S}
    (hκ : InK S Λ (· = v) κ) (x : Fin S.rank → Lev.EAf D) (hx : x ∈ Formalism.L2.Herm.hatL (F := D.host.F) Λ) :
    ((Lev.finE S κ : GL (Fin S.rank) (Lev.EAf D)) : Matrix (Fin S.rank) (Fin S.rank) (Lev.EAf D)) *ᵥ x - x ∈
      Formalism.L2.Herm.hatL (F := D.host.F) (𝔪 • Λ) := by
  obtain ⟨z, hz⟩ : ∃ z : Fin S.rank → Af D.host.F ⊗[D.host.F] D.host.E, ∀ i, Lev.swapAE D (z i) = x i :=
    ⟨fun i => (Algebra.TensorProduct.comm D.host.F D.host.E (Af D.host.F)) (x i), fun i => by
      show (Algebra.TensorProduct.comm D.host.F (Af D.host.F) D.host.E)
        ((Algebra.TensorProduct.comm D.host.F D.host.E (Af D.host.F)) (x i)) = x i
      generalize x i = y
      induction y using TensorProduct.induction_on with
      | zero => simp
      | tmul a b => rfl
      | add p q hp hq => rw [map_add, map_add, hp, hq]⟩
  set y0 : Fin S.rank → AE D := fun i => GlobalTheory.FinPlLoc.finIn D (z i) with hy0def
  have hφ : ∀ i, (Lev.swapAE D).comp (finPart D) (y0 i) = x i := fun i => by
    rw [RingHom.comp_apply, hy0def, finPart_finIn, hz]
  have hy0 : y0 ∈ latV S Λ (fun _ => True) := by
    refine GlobalTheory.HatLatV.mem_latV_of_hatL D S Λ _ y0 (fun i => finIn_mem_idAt _) ?_
    convert hx using 1
    funext i
    exact hφ i
  set e := GlobalTheory.FinPlLoc.idem D (· = v) with he
  have hey : e • y0 ∈ latV S Λ (· = v) := GlobalTheory.FinPlLoc.smul_latV v (GlobalTheory.FinPlLoc.idem_mem_intAt _) hy0
  have hmv : mt S κ *ᵥ (e • y0) ∈ latV S Λ (· = v) := (hκ.2 _ (GlobalTheory.FinPlLoc.latV_idAt hey)).1 hey
  have hgrp := hκ.1
  unfold GlobalTheory.FinPl.grpAt at hgrp
  rw [GlobalTheory.FinPlLoc.mem_congGrp] at hgrp
  have hN : ∀ i j, e * (mt S κ - 1) i j = (mt S κ - 1) i j := fun i j =>
    (GlobalTheory.FinPlLoc.mem_idAt_iff _ _).1 (by rw [Matrix.sub_apply]; exact hgrp i j)
  have hd : mt S κ *ᵥ (e • y0) - e • y0 = mt S κ *ᵥ y0 - y0 := by
    have h1 : ∀ w : Fin S.rank → AE D, mt S κ *ᵥ w - w = (mt S κ - 1) *ᵥ w := fun w => by
      rw [Matrix.sub_mulVec, Matrix.one_mulVec]
    rw [h1, h1, Matrix.mulVec_smul]
    funext i
    simp only [Pi.smul_apply, smul_eq_mul, Matrix.mulVec, dotProduct, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← mul_assoc, hN i j]
  have hd' : mt S κ *ᵥ y0 - y0 ∈ latV S (𝔪 • Λ) (· = v) :=
    latV_le_smul Λ 𝔪 hc hcm (hd ▸ sub_mem hmv hey)
  have hfin := GlobalTheory.LatVHat.latV_mem_hatL D S (𝔪 • Λ) _ _ hd'
  convert hfin using 1
  funext i
  have hx' : x = ⇑((Lev.swapAE D).comp (finPart D)) ∘ y0 := funext fun j => (hφ j).symm
  rw [finE_coe, Pi.sub_apply, Pi.sub_apply, hx', ← RingHom.map_mulVec]
  change _ = (Lev.swapAE D).comp (finPart D) ((mt S κ *ᵥ y0 - y0) i)
  rw [Pi.sub_apply, map_sub]
  rfl

theorem exists_unit_mem_modul {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc) {v : GlobalTheory.FinPl.Pl D}
    (hv : v ∉ G.pl.S0) : ∃ c : 𝓞 D.host.F, c ∉ v.asIdeal ∧ algebraMap (𝓞 D.host.F) (𝓞 D.host.E) c ∈ G.modul := by
  classical
  have hex : ∀ u ∈ G.pl.S0, ∃ c ∈ u.asIdeal, c ∉ v.asIdeal := by
    intro u hu
    by_contra h
    push_neg at h
    have huv : u = v := HeightOneSpectrum.ext (u.isMaximal.eq_of_le v.isPrime.ne_top h)
    exact hv (huv ▸ hu)
  choose! f hf hfv using hex
  refine ⟨∏ u ∈ G.pl.S0, f u ^ G.pl.depth sc u, fun hmem => ?_, ?_⟩
  · obtain ⟨u, hu, hu'⟩ := (Ideal.IsPrime.prod_mem_iff (hp := v.isPrime)).1 hmem
    exact hfv u hu (v.isPrime.mem_of_pow_mem _ hu')
  · show _ ∈ ∏ u ∈ G.pl.S0, (G.pl.w u).asIdeal ^ G.pl.depth sc u
    rw [map_prod]
    apply Ideal.prod_mem_prod
    intro u hu
    rw [map_pow]
    apply Ideal.pow_mem_pow
    have h1 := G.pl.under_w hu
    have h2 : f u ∈ ((G.pl.w u).under (𝓞 D.host.F)).asIdeal := by rw [h1]; exact hf u hu
    exact h2

end GlobalTheory.LevelOffS

open GlobalTheory.LevelOffS in

theorem GlobalTheory.LevelOffS.inK_mem_lev : All fun {D} _ _ _ {G} _ _ => ∀ i, i ≤ D.R.m → ∀ v, v ∉ G.pl.S0 → ∀ κ, InK (G.V (.grid i 0)) (G.Λ (.grid i 0)) (· = v) κ → κ ∈ lev G (.grid i 0) := by
  intro D hD T L μ0 hL sc G W M hM i hi v hv κ hκ
  obtain ⟨c, hc, hcm⟩ := exists_unit_mem_modul G hv
  refine Subgroup.mem_inf.2 ⟨mem_GfC_of_grpAt hκ.1, ?_⟩
  rw [Subgroup.mem_comap]
  show _ ∈ GlobalTheory.ChiGrid.congLev D.sp.cm (G.V (.grid i 0)).gram (G.Λ (.grid i 0)) G.modul
  rw [GlobalTheory.ChiGrid.mem_congLev]
  have hle : Formalism.L2.Herm.hatL (F := D.host.F) (G.modul • G.Λ (.grid i 0)) ≤ Formalism.L2.Herm.hatL (F := D.host.F) (G.Λ (.grid i 0)) :=
    hatL_mono Submodule.smul_le_right
  refine ⟨GlobalTheory.DefFree.finE_mem _ κ, fun x => ⟨fun hx => ?_, fun hx => ?_⟩,
    fun x hx => sub_mem_hatL_of_inK _ _ hc hcm hκ x hx⟩
  · have h1 := hle (sub_mem_hatL_of_inK _ _ hc hcm hκ x hx)
    have h2 := add_mem h1 hx
    rwa [sub_add_cancel] at h2
  · have h1 := hle (sub_mem_hatL_of_inK _ _ hc hcm (inK_inv hκ) _ hx)
    have h2 := add_mem h1 hx
    rw [sub_add_cancel, Matrix.mulVec_mulVec, ← Units.val_mul, ← map_mul, inv_mul_cancel, map_one, Units.val_one,
      Matrix.one_mulVec] at h2
    exact h2
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LocallyIntegrableSnd
section
open MeasureTheory Matrix Formalism.REAL Formalism.MainNotions.S GlobalTheory.OpTrace GlobalTheory.HCChar GlobalTheory.SUChar
open GlobalTheory.Orb (ujMat ujRep CcMat IsCharFn IsRegSS)
open GlobalTheory.DSSU (SUJ SUset Ext)
open GlobalTheory.SqIntSU (scalarMul circleHaar)

noncomputable section

namespace GlobalTheory.ExtCharInt

attribute [local instance] GlobalTheory.SqIntSU.circleBorelMS GlobalTheory.SqIntSU.circleBorelSpace GlobalTheory.SqIntSU.circleHaar_isHaar
  GlobalTheory.SqIntSU.circleHaar_finite GlobalTheory.SqIntSU.locallyCompact_special GlobalTheory.SqIntSU.secondCountable_special
  GlobalTheory.SqIntSU.sigmaCompact_special GlobalTheory.DSSU.borelSpace_SUJ

theorem scalarMul_cen {n : ℕ} [NeZero n] (ε : Fin n → Bool) (j : ZMod n) (z : Circle) (g : SUJ ε) :
    scalarMul ε (z * ZMod.toCircle j, GlobalTheory.ExtChar.cen ε j * g) = scalarMul ε (z, g) := by
  rw [GlobalTheory.SqIntSU.scalarMul_apply, GlobalTheory.SqIntSU.scalarMul_apply]
  show GlobalTheory.SqIntSU.unitScalar ε (z * ZMod.toCircle j) *
      (GlobalTheory.SqIntSU.unitScalar ε (ZMod.toCircle j)⁻¹ * (g : UJ ε)) = _
  rw [← mul_assoc, ← GlobalTheory.SqIntSU.unitScalar_mul, mul_inv_cancel_right]

theorem locallyIntegrable_snd {n : ℕ} (ε : Fin n → Bool) (μ' : Measure (SUJ ε)) [SFinite μ'] (Θ' : SUJ ε → ℂ)
    (h : LocallyIntegrable Θ' μ') :
    LocallyIntegrable (fun p : Circle × SUJ ε => Θ' p.2) (circleHaar.prod μ') := by
  intro x
  obtain ⟨U, hU, hi⟩ := h x.2
  refine ⟨Set.univ ×ˢ U, prod_mem_nhds Filter.univ_mem hU, ?_⟩
  rw [IntegrableOn, ← Measure.prod_restrict, Measure.restrict_univ]
  exact hi.comp_snd circleHaar

theorem integral_extChar : ∀ (n : ℕ) [NeZero n] (ε : Fin n → Bool) (μ' : Measure (SUJ ε)) [μ'.IsHaarMeasure] (m : ℤ) (Θ' : SUJ ε → ℂ), LocallyIntegrable Θ' μ' → LocallyIntegrable (GlobalTheory.ExtChar.extChar ε m Θ') (letI := GlobalTheory.SqIntSU.circleBorelMS; Measure.map (scalarMul ε) (circleHaar.prod μ')) → ∀ f : UJ ε → ℂ, Continuous f → HasCompactSupport f → ∫ x, f x * GlobalTheory.ExtChar.extChar ε m Θ' x ∂(letI := GlobalTheory.SqIntSU.circleBorelMS; Measure.map (scalarMul ε) (circleHaar.prod μ')) = ∫ g, (∫ z, f (scalarMul ε (z, g)) * (z : ℂ) ^ m ∂circleHaar) * Θ' g ∂μ' := by
  intro n _ ε μ' _ m Θ' hΘ hE f hf hfc
  haveI : SFinite μ' := inferInstance
  have hsc : Continuous (scalarMul ε) := GlobalTheory.SqIntSU.continuous_scalarMul ε
  have hI : Integrable (fun x => f x * GlobalTheory.ExtChar.extChar ε m Θ' x)
      (Measure.map (scalarMul ε) (circleHaar.prod μ')) := by
    simpa only [smul_eq_mul] using hE.integrable_smul_left_of_hasCompactSupport hf hfc
  rw [integral_map hsc.aemeasurable hI.aestronglyMeasurable]

  set G : Circle × SUJ ε → ℂ := fun p => f (scalarMul ε p) * (p.1 : ℂ) ^ m * Θ' p.2 with hGdef
  have hzc : Continuous fun z : Circle => (z : ℂ) ^ m :=
    Continuous.zpow₀ continuous_subtype_val m (fun z => Or.inl (Circle.coe_ne_zero z))
  have hc : Continuous fun p : Circle × SUJ ε => f (scalarMul ε p) * (p.1 : ℂ) ^ m :=
    (hf.comp hsc).mul (hzc.comp continuous_fst)
  have hprop : IsProperMap (scalarMul ε) :=
    isProperMap_iff_tendsto_cocompact.2 ⟨hsc, GlobalTheory.SqIntSU.scalarMul_proper ε⟩
  have hcs : HasCompactSupport fun p : Circle × SUJ ε => f (scalarMul ε p) * (p.1 : ℂ) ^ m := by
    refine HasCompactSupport.intro (hprop.isCompact_preimage hfc) fun p hp => ?_
    have : f (scalarMul ε p) = 0 := image_eq_zero_of_notMem_tsupport hp
    simp [this]
  have hG : Integrable G (circleHaar.prod μ') := by
    simpa only [smul_eq_mul, hGdef] using
      (locallyIntegrable_snd ε μ' Θ' hΘ).integrable_smul_left_of_hasCompactSupport hc hcs

  have hT : ∀ j : ZMod n, MeasurePreserving (Prod.map (fun z : Circle => z * ZMod.toCircle j)
      (fun g : SUJ ε => GlobalTheory.ExtChar.cen ε j * g)) (circleHaar.prod μ') (circleHaar.prod μ') := fun j =>
    (measurePreserving_mul_right circleHaar _).prod (measurePreserving_mul_left μ' _)
  have hEmb : ∀ j : ZMod n, MeasurableEmbedding (Prod.map (fun z : Circle => z * ZMod.toCircle j)
      (fun g : SUJ ε => GlobalTheory.ExtChar.cen ε j * g)) := fun j =>
    ((MeasurableEquiv.mulRight (ZMod.toCircle j)).prodCongr
      (MeasurableEquiv.mulLeft (GlobalTheory.ExtChar.cen ε j))).measurableEmbedding
  have hpt : ∀ p : Circle × SUJ ε, f (scalarMul ε p) * GlobalTheory.ExtChar.extChar ε m Θ' (scalarMul ε p) =
      (n : ℂ)⁻¹ * ∑ j : ZMod n, G (Prod.map (fun z : Circle => z * ZMod.toCircle j)
        (fun g : SUJ ε => GlobalTheory.ExtChar.cen ε j * g) p) := by
    rintro ⟨z, g⟩
    rw [GlobalTheory.ExtChar.extChar_scalarMul, GlobalTheory.ExtChar.avgChar, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum,
      Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [hGdef, Prod.map, scalarMul_cen, Circle.coe_mul, mul_zpow]
    ring
  simp only [hpt]
  rw [integral_const_mul, integral_finset_sum (f := fun j p => G (Prod.map (fun z : Circle => z * ZMod.toCircle j)
      (fun g : SUJ ε => GlobalTheory.ExtChar.cen ε j * g) p)) _ (fun j _ => ((hT j).integrable_comp_emb (hEmb j)).2 hG)]
  simp only [fun j => (hT j).integral_comp (hEmb j) G]
  rw [Finset.sum_const, Finset.card_univ, ZMod.card, nsmul_eq_mul, ← mul_assoc,
    inv_mul_cancel₀ (Nat.cast_ne_zero.2 (NeZero.ne n)), one_mul, integral_prod_symm G hG]
  refine integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
  simp only [hGdef]
  exact integral_mul_const _ _

end GlobalTheory.ExtCharInt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.MxAtOfMemDepLat
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

noncomputable section
namespace GlobalTheory.CharXFB
variable {D : D7}

def hA (T : HSp D) (y z : Fin T.rank → AE D) : AE D := ∑ k, cA D (z k) * (gA T *ᵥ y) k

theorem pairS_eq_sum (T : HSp D) {ρ : ℕ} (x x' : Mx D T.rank ρ) :
    pairS T x x' = ∑ p, hA T (fun k => x k p) (fun k => x' k p) := by
  simp only [pairS, hA, Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.mulVec, dotProduct]
  rfl

theorem mxAt_of_mem_depLat {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {p : Pair T}
    {u : WO (G.pS p) (G.pT p)} (hu : u ∈ depLat G p) : MxAt (fun _ => True) u :=
  GlobalTheory.FinPl.LatMem.latO_mxAt hu.1

example (T : HSp D) : hA T 0 0 = 0 := by simp [hA]

end GlobalTheory.CharXFB
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RealPlaceDeterminantPowerMulCompactTorusElementStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.realPlaceDeterminantPower_mul_compactTorusElement : ∀ (D : D7) (S T : HSp D) (C : Ctx S T) (B : C.Bas), C.IsB B → ∀ (m : D.what₂.Tau → ℤ) (ρ : D.what₂.Tau) (t : Fin T.rank → ℝ) (g : GA D T), detPow C.θ T m (g * torAt C.θ T B ρ t) = cexp (((∑ a, ((m ρ : ℤ) : ℝ) * t a : ℝ) : ℂ) * I) * detPow C.θ T m g := by
  first | exact @GlobalTheory.AdSpan.DetTor.detPow_mul_torAt | exact GlobalTheory.AdSpan.DetTor.detPow_mul_torAt | (intros; apply GlobalTheory.AdSpan.DetTor.detPow_mul_torAt <;> assumption)
end

