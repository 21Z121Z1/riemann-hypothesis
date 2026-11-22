import Mathlib
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Bundle0003
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsArith
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsEigFrames
import GroundTheory.HeightsAndTheta.Heights.HeightsOfSets.HeightsSetAll

-- bundled from Development.AutomorphicSpectrum.Definitions.MetricPeriods.HasMultiplierLine
section
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Small.LineModel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry GroundTheory.Heights₂.Heights.HilbertSamuel

section General

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]

theorem mem_of_aeval (y : (Σ k, ι k) → Ω) {g : MRing ι} {d : K → ℕ}
    (hg : IsMultiHomog g d) (h0 : aeval y g = 0) : g ∈ mCoordIdeal y := by
  show g ∈ RingHom.ker (mConeMap y)
  rw [RingHom.mem_ker, ProjLine.mConeMap_eq_of_isMultiHomog y hg, h0, map_zero, zero_mul]

theorem eval_map_eq (z : (Σ k, ι k) → ℂ) (f : MRing ι) :
    eval z (map (Int.castRingHom ℂ) f) = aeval z f := by
  rw [eval_map, aeval_def]; rfl

theorem ptsOver_complex (P : Ideal (MRing ι)) : ptsOver ℂ P = mcPts P := by
  ext z
  simp only [ptsOver, mcPts, Set.mem_setOf_eq, eval_map_eq]

theorem hasVal_unique (y : (Σ k, ι k) → Ω) (a : K → ℤ) (s : Ω) {𝕜 : Type} [Field 𝕜]
    {z : (Σ k, ι k) → 𝕜} (hz : z ∈ ptsOver 𝕜 (mCoordIdeal y)) {w w' : 𝕜}
    (h : HasVal y a s z w) (h' : HasVal y a s z w') : w = w' := by
  obtain ⟨dg, dh, g, h, hg, hh, hd, e1, n1, v1⟩ := h
  obtain ⟨dg', dh', g', h', hg', hh', hd', e1', n1', v1'⟩ := h'
  have hdeg : dg' + dh = dg + dh' := by
    funext k
    have := hd k; have := hd' k
    simp only [Pi.add_apply]; omega
  have hom : IsMultiHomog (g * h' + -(g' * h)) (dg + dh') :=
    ProjLine.mhAdd (ProjLine.mhMul hg hh') (ProjLine.mhNeg (hdeg ▸ ProjLine.mhMul hg' hh))
  have h0 := hz.2 _ (mem_of_aeval y hom (by simp only [map_add, map_neg, map_mul, e1, e1']; ring))
  simp only [map_add, map_neg, map_mul, v1, v1'] at h0
  have : (w - w') * (aeval z h * aeval z h') = 0 := by linear_combination h0
  exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_right (mul_ne_zero n1 n1'))

theorem hasVal_form (y : (Σ k, ι k) → Ω) {g : MRing ι} {d : K → ℕ} (hg : IsMultiHomog g d)
    {𝕜 : Type} [Field 𝕜] (z : (Σ k, ι k) → 𝕜) :
    HasVal y (fun k => (d k : ℤ)) (aeval y g) z (aeval z g) :=
  ⟨d, 0, g, 1, hg, ProjLine.isMultiHomog_one, fun k => by simp, by simp, by simp, by simp⟩

theorem one_off (y : (Σ k, ι k) → Ω) : IsFormOff (mCoordIdeal y) 1 := by
  refine ⟨⟨0, ProjLine.isMultiHomog_one⟩, fun h => ?_⟩
  have : mConeMap y 1 = 0 := h
  simp at this

theorem hasMultiplier_refl (y : (Σ k, ι k) → Ω) (F : Type) [Field F] [NumberField F] [Algebra F Ω]
    (L : HermLine ι) : HasMultiplier y F L L 0 := by
  have key : ∀ {𝕜 : Type} [Field 𝕜] {z : (Σ k, ι k) → 𝕜}, z ∈ ptsOver 𝕜 (mCoordIdeal y) →
      ∀ w, HasVal y (L.a - L.a) 1 z w → w = 1 := by
    intro 𝕜 _ z hz w hw
    refine hasVal_unique y _ _ hz hw ?_
    have := hasVal_form y (ProjLine.isMultiHomog_one (ι := ι)) z
    simpa [sub_self, Pi.zero_def] using this
  refine ⟨1, 1, ∅, 0, 0, one_ne_zero, one_off y, by simp, by simp, by simp, by simp, ⟨?_, ?_⟩,
    by simp [embMean]⟩
  · intro p _ z hz _ w hw
    simp [key hz.1 w hw]
  · intro sg z hz _ _ w hw
    rw [← ptsOver_complex] at hz
    simp [key hz w hw]

theorem liesOver_rat [CharZero Ω] (y : (Σ k, ι k) → Ω) (sg : ℚ →+* ℂ) {z : (Σ k, ι k) → ℂ}
    (hz : z ∈ mcPts (mCoordIdeal y)) : LiesOver y sg z := by
  intro d g h θ hg hh e
  have hC : ∀ r : ℤ, IsMultiHomog (C r : MRing ι) 0 := by
    classical
    intro r m hm k
    rw [mem_support_iff, coeff_C] at hm
    split_ifs at hm with h
    · subst h
      simp
    · exact absurd rfl hm
  have hom : IsMultiHomog (C (θ.den : ℤ) * g + -(C θ.num * h)) (0 + d) :=
    ProjLine.mhAdd (ProjLine.mhMul (hC _) hg) (ProjLine.mhNeg (ProjLine.mhMul (hC _) hh))
  have h0 := hz.2 _ (mem_of_aeval y hom (by
    simp only [map_add, map_neg, map_mul, e, eq_intCast, map_intCast, map_natCast, eq_ratCast,
      Int.cast_natCast]
    have : (θ.den : Ω) * (θ : Ω) = θ.num := by exact_mod_cast Rat.den_mul_eq_num θ
    rw [← this]; ring))
  rw [eval_map_eq] at h0
  rw [eval_map_eq, eval_map_eq]
  simp only [map_add, map_neg, map_mul, eq_intCast, map_intCast, map_natCast, Int.cast_natCast] at h0
  have h1 : (θ.den : ℂ) * (θ : ℂ) = θ.num := by exact_mod_cast Rat.den_mul_eq_num θ
  have h2 : (θ.den : ℂ) ≠ 0 := by exact_mod_cast θ.den_ne_zero
  rw [eq_ratCast]
  apply mul_left_cancel₀ h2
  rw [← mul_assoc, h1]
  linear_combination h0

end General

open ProjLine

theorem isModelOver_line : IsModelOver (ι := GlobalTheory (Fin 2)) y ℚ 1 where
  one_le := le_rfl
  arith := isArithVar_y'
  bir := birational_y
  uniq z hz := ⟨Rat.castHom ℂ, liesOver_rat y _ hz, fun _ _ => Subsingleton.elim _ _⟩

theorem isNefH_line : IsNefH (mCoordIdeal (ι := GlobalTheory (Fin 2)) y) fsLine1 where
  semipos := ⟨⊥, bot_le, isSemipositiveRel_fs _ _⟩
  conj := isConjInvariantH_fs _
  nef := ProjLine.nefOnFibres_of_nonneg _ _ fun _ => zero_le_one

theorem coord_le_fs (z : Ix (Fin 2) → ℂ) (p : Ix (Fin 2)) : ‖z p‖ ≤ fsLine1.h z :=
  PiLp.norm_apply_le (WithLp.toLp 2 z) p

theorem isGenH_line : IsGenH (mCoordIdeal (ι := GlobalTheory (Fin 2)) y) fsLine1 1 where
  pos := one_pos
  semipos := ⟨⊥, bot_le, isSemipositiveRel_fs _ _⟩
  conj := isConjInvariantH_fs _
  mono := ⟨fun _ => 1, rfl, fun z _ μ hμ => by
    have h1 : ∑ p, μ p = 1 := by
      rw [Fintype.sum_sigma, Fintype.sum_unique]; exact hμ _
    rw [norm_prod, one_mul]
    calc ∏ p, ‖z p ^ μ p‖ ≤ ∏ p, fsLine1.h z ^ μ p :=
          Finset.prod_le_prod (fun _ _ => norm_nonneg _) fun p _ => by
            rw [norm_pow]; exact pow_le_pow_left₀ (norm_nonneg _) (coord_le_fs z p) _
      _ = fsLine1.h z := by rw [Finset.prod_pow_eq_pow_sum, h1, pow_one]⟩

def triv : HermLine (GlobalTheory (Fin 2)) := HermLine.ofWeight (fun _ => 0) (fun _ _ _ => rfl)

theorem hasMultiplier_line : HasMultiplier (ι := GlobalTheory (Fin 2)) y ℚ triv fsLine1 0 := by
  have hX : IsMultiHomog (X ⟨(), 1⟩ : MRing (GlobalTheory (Fin 2))) (fun _ => 1) := by
    convert isMultiHomog_X (ι := GlobalTheory (Fin 2)) ⟨(), 1⟩ using 1
    funext k
    simp
  have key : ∀ {𝕜 : Type} [Field 𝕜] {z : Ix (Fin 2) → 𝕜}, z ∈ ptsOver 𝕜 (mCoordIdeal (ι := GlobalTheory (Fin 2)) y) →
      ∀ w, HasVal (ι := GlobalTheory (Fin 2)) y (fsLine1.a - triv.a) (y ⟨(), 1⟩) z w → w = z ⟨(), 1⟩ := by
    intro 𝕜 _ z hz w hw
    refine hasVal_unique y _ _ hz hw ?_
    have := hasVal_form y hX z
    simp only [aeval_X] at this
    have e : fsLine1.a - triv.a = fun _ => ((1 : ℕ) : ℤ) := by
      funext k; simp [triv, HermLine.ofWeight, HermLine.ofCone]
    rw [e]; exact this
  have hne : y ⟨(), 1⟩ ≠ 0 := linearIndependent_y.ne_zero _
  refine ⟨y ⟨(), 1⟩, 1, ∅, 0, 0, hne, one_off y, by simp, by simp, by simp, by simp, ⟨?_, ?_⟩,
    by simp [embMean]⟩
  · intro p _ z hz _ w hw
    rw [key hz.1 w hw]
    have := norm_le_pi_norm (fun i : Fin 2 => z ⟨(), i⟩) 1
    simpa [supMet, triv, HermLine.ofWeight, HermLine.ofCone] using this
  · intro sg z hz _ _ w hw
    rw [← ptsOver_complex] at hz
    rw [key hz w hw]
    have := coord_le_fs z ⟨(), 1⟩
    simpa [triv, HermLine.ofWeight] using this

theorem multBound_half (L : HermLine (GlobalTheory (Fin 2))) (c : ℕ → ℝ) (t : (ℚ →+* ℂ) → ℝ)
    (H : MultBound (ι := GlobalTheory (Fin 2)) y L L (2⁻¹) 1 c t) :
    2 ≤ Real.exp (c 2) ∧ 2⁻¹ ≤ Real.exp (t (Rat.castHom ℂ)) := by
  have hv : ∀ {𝕜 : Type} [Field 𝕜] [CharZero 𝕜] (z : Ix (Fin 2) → 𝕜),
      HasVal (ι := GlobalTheory (Fin 2)) y (L.a - L.a) 2⁻¹ z (2⁻¹ : 𝕜) := by
    intro 𝕜 _ _ z
    refine ⟨0, 0, 1, 1 + 1, isMultiHomog_one, mhAdd isMultiHomog_one isMultiHomog_one, by simp, ?_, ?_, ?_⟩
    · simp only [map_one, map_add]; norm_num
    · simp only [map_one, map_add]; norm_num
    · simp only [map_one, map_add]; norm_num
  have hp : ∀ (𝕜 : Type) [Field 𝕜], (1 : Ix (Fin 2) → 𝕜) ∈ ptsOver 𝕜 (mCoordIdeal (ι := GlobalTheory (Fin 2)) y) := by
    intro 𝕜 _
    refine ⟨fun _ => ⟨0, one_ne_zero⟩, fun f hf => ?_⟩
    rw [mCoordIdeal_y, Ideal.mem_bot] at hf
    simp [hf]
  constructor
  · have := H.fin 2 1 ⟨hp _, fun _ => isAlgebraic_one⟩ (by simp) _ (hv 1)
    have h1 : supMet L.a (1 : Ix (Fin 2) → PadicAlgCl 2) = 1 := by
      have : ‖fun _ : Fin 2 => (1 : PadicAlgCl 2)‖ = 1 := by simp
      simp [supMet, this]
    have h2 : ‖(2 : PadicAlgCl 2)‖ = 2⁻¹ := by
      have := PadicAlgCl.norm_extends (p := 2) (2 : ℚ_[2])
      have h3 : ‖(2 : ℚ_[2])‖ = 2⁻¹ := by simpa using (Padic.norm_p (p := 2))
      rw [← h3, ← this]; congr 1
    rw [h1, norm_inv, h2] at this
    simpa using this
  · have hz := hp ℂ
    rw [ptsOver_complex] at hz
    have := H.arch _ 1 hz (liesOver_rat y (Rat.castHom ℂ) hz) (by simp) _ (hv 1)
    have hpos := L.pos 1 hz.1
    have h2 := le_of_mul_le_mul_right this hpos
    simpa using h2

end GlobalTheory.CompanionTheory.Ar.Small.LineModel
end
end

-- bundled from Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsFundSet
section
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Cusp

open NumberField Matrix MeasureTheory GlobalTheory.CompanionTheory.Ar
open scoped ComplexOrder

section Ball

variable {Ψ : Type} [Fintype Ψ] {j j' n : ℕ}

def ballMat (q : Ψ × Fin j × Fin j' ≃ Fin n) (t : Fin n → ℂ) (τ : Ψ) : Matrix (Fin j) (Fin j') ℂ :=
  Matrix.of fun a b => t (q (τ, a, b))

def ballDom (q : Ψ × Fin j × Fin j' ≃ Fin n) : Set (Fin n → ℂ) :=
  {t | ∀ τ, (1 - (ballMat q t τ)ᴴ * ballMat q t τ).PosDef}

def ballPot (q : Ψ × Fin j × Fin j' ≃ Fin n) (t : Fin n → ℂ) : ℝ :=
  -∑ τ, Real.log (1 - (ballMat q t τ)ᴴ * ballMat q t τ).det.re

def ballDens (q : Ψ × Fin j × Fin j' ≃ Fin n) (t : Fin n → ℂ) : ℝ := Real.exp ((j + j' : ℕ) * ballPot q t)

end Ball

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {g : ℕ} {Λ : Type} [AddCommGroup Λ] [Module (𝓞 E) Λ]

def autGrp (form : Λ →ₗ[ℤ] Λ →ₗ[ℤ] ℤ) : Subgroup (Λ ≃ₗ[𝓞 E] Λ) where
  carrier := {γ | ∀ x y, form (γ x) (γ y) = form x y}
  one_mem' _ _ := rfl
  mul_mem' {a b} ha hb x y := by
    show form (a (b x)) (a (b y)) = form x y
    rw [ha, hb]
  inv_mem' {a} ha x y := by
    have h := ha (a.symm x) (a.symm y)
    simp only [LinearEquiv.apply_symm_apply] at h
    exact h.symm

def RiemLat.HasSig {Ψ : Type} (R : RiemLat E g Λ) (σ : Ψ → (𝓞 E →+* ℂ)) (j j' : ℕ) : Prop :=
  ∀ τ, Module.finrank ℂ (eigSp R.B (σ τ)) = j' ∧ Module.finrank ℂ (eigSp R.B ((starRingEnd ℂ).comp (σ τ))) = j

def RiemLat.EqvBy (R R' : RiemLat E g Λ) (γ : Λ ≃ₗ[𝓞 E] Λ) : Prop :=
  ∃ h : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ), ∀ x, R'.P (γ x) = h (R.P x)

variable (E) in

structure UnivFam (Ψ : Type) [Fintype Ψ] (j j' n g : ℕ) (Λ : Type) [AddCommGroup Λ] [Module (𝓞 E) Λ] where

  q : Ψ × Fin j × Fin j' ≃ Fin n

  σ : Ψ → (𝓞 E →+* ℂ)
  cm : IsCMFam σ

  form : Λ →ₗ[ℤ] Λ →ₗ[ℤ] ℤ

  R : (Fin n → ℂ) → RiemLat E g Λ
  form_eq : ∀ t, (R t).form = form
  hol : IsHolFam (ballDom q) R
  sig : ∀ t ∈ ballDom q, (R t).HasSig σ j j'

  b : Ψ → Fin j' → (Fin n → ℂ) → Fin g → ℂ
  frames : IsEigFrames (ballDom q) (fun t => (R t).B) σ b
  logDet_eq : ∀ t ∈ ballDom q, (R t).logDet (fun τ i => b τ i t) = ballPot q t
  univ : ∀ R' : RiemLat E g Λ, R'.form = form → R'.HasSig σ j j' → ∃! t, t ∈ ballDom q ∧ (R t).EqvBy R' 1

namespace UnivFam

variable {Ψ : Type} [Fintype Ψ] {j j' n : ℕ} (F : UnivFam E Ψ j j' n g Λ)

def Eqv (Γ : Subgroup (Λ ≃ₗ[𝓞 E] Λ)) (t t' : Fin n → ℂ) : Prop := ∃ γ ∈ Γ, (F.R t).EqvBy (F.R t') γ

def IsFundSet (Γ : Subgroup (Λ ≃ₗ[𝓞 E] Λ)) (FF : Set (Fin n → ℂ)) : Prop :=
  MeasurableSet FF ∧ FF ⊆ ballDom F.q ∧ (∀ t ∈ ballDom F.q, ∃ t' ∈ FF, F.Eqv Γ t t') ∧
    ∀ t ∈ FF, ∀ t' ∈ FF, F.Eqv Γ t t' → t = t'

def IsArith (Γ : Subgroup (Λ ≃ₗ[𝓞 E] Λ)) : Prop := Γ ≤ autGrp F.form ∧ Γ.relIndex (autGrp F.form) ≠ 0

end UnivFam

end GlobalTheory.CompanionTheory.Ar.Cusp
end
end

-- bundled from Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsOrthFull
section
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar

open GroundTheory.Heights₂.Heights NumberField TensorProduct ComplexAt

variable {K : Type} [Field K] [NumberField K]

def sqAt (E : HermitianBundle.{0} K) (σ : K →+* ℂ) (x : Fibre σ E.carrier) : ℝ :=
  ((E.metric.form σ).inner x x).re

def OrthAt (E : HermitianBundle.{0} K) (F F' : Submodule (𝓞 K) E.carrier) : Prop :=
  ∀ (σ : K →+* ℂ), ∀ x ∈ F, ∀ y ∈ F',
    (E.metric.form σ).inner ((1 : ComplexAt σ) ⊗ₜ[𝓞 K] x) ((1 : ComplexAt σ) ⊗ₜ[𝓞 K] y) = 0

structure SatFlag (E : HermitianBundle.{0} K) (r : ℕ) where

  F : Fin (r + 1) → Submodule (𝓞 K) E.carrier
  mono : Monotone F
  sat : ∀ i, E.Saturated (F i)
  rank : ∀ i, E.rank (F i) = i

namespace SatFlag

variable {E : HermitianBundle.{0} K} {r : ℕ}

def top (A : SatFlag E r) : Submodule (𝓞 K) E.carrier := A.F (Fin.last r)

def grDeg (A : SatFlag E r) (i : Fin r) : ℝ := E.normDegree (A.F i.succ) - E.normDegree (A.F i.castSucc)

end SatFlag

structure FlagPair (E : HermitianBundle.{0} K) (Ψ : Type) (j k : ℕ) where

  W : Ψ → SatFlag E j

  S : Ψ → SatFlag E k

namespace FlagPair

variable {E : HermitianBundle.{0} K} {Ψ : Type} [Fintype Ψ] {j k : ℕ}

def lamDeg (A : FlagPair E Ψ j k) (lam : Ψ → Fin (j + k) → ℝ) : ℝ :=
  ∑ τ, (-(∑ i : Fin j, lam τ (Fin.castAdd k i) * (A.W τ).grDeg i) +
    ∑ i : Fin k, lam τ (Fin.natAdd j i) * (A.S τ).grDeg i.rev)

def flatDeg (A : FlagPair E Ψ j k) (τ : Ψ) : ℝ := E.normDegree (A.W τ).top - E.normDegree (A.S τ).top

def part (A : FlagPair E Ψ j k) : Ψ ⊕ Ψ → Submodule (𝓞 K) E.carrier :=
  Sum.elim (fun τ => (A.W τ).top) (fun τ => (A.S τ).top)

def IsOrthFull (A : FlagPair E Ψ j k) : Prop :=
  (∀ a b, a ≠ b → OrthAt E (A.part a) (A.part b)) ∧ Fintype.card Ψ * (j + k) = Module.finrank (𝓞 K) E.carrier

end FlagPair

end GlobalTheory.CompanionTheory.Ar
end
end

