import Mathlib
import GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.IntToFracInjective
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Bundle0003
import GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.Bundle0002
import GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.Bundle0003

-- bundled from GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.ComapMaximalIdealParDVR
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Vertical

open MvPolynomial NumberField IsDedekindDomain

noncomputable section

section Objects

variable {K : Type*} [Field K] [NumberField K]

theorem comap_maximalIdeal_parDVR (e n : ℕ) (v : HeightOneSpectrum (𝓞 K)) :
    (IsLocalRing.maximalIdeal (ParDVR e n v)).comap (algebraMap (𝓞 K) (ParDVR e n v)) = v.asIdeal := by
  have h1 : algebraMap (𝓞 K) (ParDVR e n v) =
      (algebraMap (MvPolynomial (Par e n) (𝓞 K)) (ParDVR e n v)).comp C :=
    IsScalarTower.algebraMap_eq _ _ _
  have h2 : (IsLocalRing.maximalIdeal (ParDVR e n v)).comap
      (algebraMap (MvPolynomial (Par e n) (𝓞 K)) (ParDVR e n v)) = parPrime e n v :=
    Localization.AtPrime.comap_maximalIdeal
  rw [h1, ← Ideal.comap_comap, h2]
  ext x
  simp only [Ideal.mem_comap, parPrime]
  constructor
  · intro hx
    rw [MvPolynomial.mem_map_C_iff] at hx
    simpa using hx 0
  · intro hx
    exact Ideal.mem_map_of_mem _ hx

def resToKappa (e n : ℕ) (v : HeightOneSpectrum (𝓞 K)) :
    v.asIdeal.ResidueField →+* (IsLocalRing.maximalIdeal (ParDVR e n v)).ResidueField :=
  Ideal.ResidueField.map v.asIdeal (IsLocalRing.maximalIdeal (ParDVR e n v))
    (algebraMap (𝓞 K) (ParDVR e n v)) (comap_maximalIdeal_parDVR e n v).symm

def parYκ (e n : ℕ) (v : HeightOneSpectrum (𝓞 K)) :
    Par e n → (IsLocalRing.maximalIdeal (ParDVR e n v)).ResidueField :=
  fun p => algebraMap (ParDVR e n v) (IsLocalRing.maximalIdeal (ParDVR e n v)).ResidueField (parY e n v p)

end Objects

def SpecCompDim.Statement : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (n e : ℕ) (I : Ideal (MvPolynomial (Fin n) K))
    (f : MvPolynomial (Fin (e + 1) × Fin n) K) (v : HeightOneSpectrum (𝓞 K)),
    IsProjPrime I → IsChowForm I (e + 1) f → ∀ W ∈ specComps I v,
      IsProjPrime (reduceMod v W) ∧
        ringKrullDim (MvPolynomial (Fin n) v.asIdeal.ResidueField ⧸ reduceMod v W) = ((e + 1 : ℕ) : WithBot ℕ∞)

def ChartDomain.Statement : Prop :=
  ∀ (D : Type) [CommRing D] [IsDomain D] (n e : ℕ) (Q : Ideal (MvPolynomial (Fin n) D)) (j : Fin n),
    Q.IsPrime → (∀ c : D, C c ∈ Q → c = 0) → X j ∉ Q →
      IsDomain (Localization.Away (secCoord (Q.map (MvPolynomial.map (C : D →+* MvPolynomial (Par e n) D))) X j)) ∧
        Function.Injective (algebraMap D
          (Localization.Away (secCoord (Q.map (MvPolynomial.map (C : D →+* MvPolynomial (Par e n) D))) X j)))

def SecAlgField.Statement : Prop :=
  ∀ (k : Type) [Field k] (n e : ℕ) (Q : Ideal (MvPolynomial (Fin n) k))
    (g : MvPolynomial (Fin (e + 1) × Fin n) k), IsProjPrime Q → IsChowForm Q (e + 1) g →
      IsField (SecAlg (Q.map (MvPolynomial.map (algebraMap k (FractionRing (MvPolynomial (Par e n) k)))))
        (fun p => algebraMap (MvPolynomial (Par e n) k) (FractionRing (MvPolynomial (Par e n) k)) (X p)))

def ParFracIsFractionRing.Statement : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (e n : ℕ) (v : HeightOneSpectrum (𝓞 K)),
    letI := (parToFrac e n v).toAlgebra
    IsFractionRing (ParDVR e n v) (ParFrac K e n)

def ResidueAlgIndep.Statement : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (e n : ℕ) (v : HeightOneSpectrum (𝓞 K)),
    letI := (resToKappa e n v).toAlgebra
    AlgebraicIndependent v.asIdeal.ResidueField (parYκ e n v)

end

end GroundTheory.Heights₂.Heights.Vertical
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.Inhabitants
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Vertical

open MvPolynomial NumberField IsDedekindDomain

noncomputable section

theorem NormLength.hypotheses_inhabited :
    Function.Injective (fun x : ℤ_[2] => (1 : ℤ_[2]) * x) := fun x y h => by
  simpa using h

theorem LengthDecomp.hypotheses_inhabited :
    Module.length ℤ_[2] (ℤ_[2] ⧸ Ideal.span {(2 : ℤ_[2])}) ≠ ⊤ :=
  Ring.ord_ne_top (mem_nonZeroDivisors_of_ne_zero two_ne_zero)

theorem PrimitiveUnit.hypotheses_inhabited :
    (∃ m, IsUnit ((1 : MvPolynomial (Fin 1) ℤ_[2]).coeff m)) ∧
      (1 : MvPolynomial (Fin 1) ℤ_[2]).map (algebraMap ℤ_[2] ℚ_[2]) =
        C (1 : ℚ_[2]) * (1 : MvPolynomial (Fin 1) ℤ_[2]).map (algebraMap ℤ_[2] ℚ_[2]) :=
  ⟨⟨0, by simp⟩, by simp⟩

theorem NormFormEval.hypotheses_inhabited : Module.Free ℚ ℚ ∧ Module.Finite ℚ ℚ :=
  ⟨inferInstance, inferInstance⟩

theorem ChartTorsion.hypotheses_inhabited :
    (⊥ : Ideal (MvPolynomial (Fin 1) ℤ)).IsPrime ∧
      (∀ c : ℤ, C c ∈ (⊥ : Ideal (MvPolynomial (Fin 1) ℤ)) → c = 0) ∧
      C (1 : ℤ) * (0 : MvPolynomial (Fin 1 ⊕ (Fin 1 × Fin 1)) ℤ) ∈ incIdeal ⊥ 1 := by
  refine ⟨Ideal.isPrime_bot, fun c hc => ?_, by simp⟩
  rw [Ideal.mem_bot] at hc
  exact (C_eq_zero).mp hc

theorem IncidenceNull.hypotheses_inhabited :
    IsChowForm (⊥ : Ideal (MvPolynomial (Fin 1) ℚ)) 1 (X (0, 0)) :=
  isChowForm_point ℚ

abbrev pointPar : Par 0 1 → FractionRing (MvPolynomial (Par 0 1) ℚ) :=
  fun p => algebraMap (MvPolynomial (Par 0 1) ℚ) (FractionRing (MvPolynomial (Par 0 1) ℚ)) (X p)

theorem pointPar_algebraicIndependent : AlgebraicIndependent ℚ pointPar := by
  have h := MvPolynomial.algebraicIndependent_X (Par 0 1) ℚ
  have hinj : Function.Injective (IsScalarTower.toAlgHom ℚ (MvPolynomial (Par 0 1) ℚ)
      (FractionRing (MvPolynomial (Par 0 1) ℚ))) :=
    IsFractionRing.injective (MvPolynomial (Par 0 1) ℚ) (FractionRing (MvPolynomial (Par 0 1) ℚ))
  have h2 := h.map' hinj
  have e : (⇑(IsScalarTower.toAlgHom ℚ (MvPolynomial (Par 0 1) ℚ)
      (FractionRing (MvPolynomial (Par 0 1) ℚ))) ∘ X) = pointPar := by
    funext p
    simp only [Function.comp_apply, IsScalarTower.coe_toAlgHom', pointPar]
  rw [e] at h2
  exact h2

theorem ChowNormForm.hypotheses_inhabited :
    AlgebraicIndependent ℚ pointPar ∧ IsProjPrime (⊥ : Ideal (MvPolynomial (Fin 1) ℚ)) ∧
      IsChowForm (⊥ : Ideal (MvPolynomial (Fin 1) ℚ)) (0 + 1) (X (0, 0)) :=
  ⟨pointPar_algebraicIndependent, isProjPrime_point ℚ, isChowForm_point ℚ⟩

theorem SecLinNZD.hypotheses_inhabited :
    AlgebraicIndependent ℚ pointPar ∧ IsProjPrime (⊥ : Ideal (MvPolynomial (Fin 1) ℚ)) ∧
      IsChowForm (⊥ : Ideal (MvPolynomial (Fin 1) ℚ)) (0 + 1) (X (0, 0)) ∧
      linForm (fun _ => (1 : ℚ)) ∉ (⊥ : Ideal (MvPolynomial (Fin 1) ℚ)) :=
  ⟨pointPar_algebraicIndependent, isProjPrime_point ℚ, isChowForm_point ℚ, linForm_one_not_mem_point ℚ⟩

abbrev pointForm : MvPolynomial (Fin (0 + 1) × Fin 1) (𝓞 ℚ) := X (0, 0)

theorem pointForm_map : pointForm.map (algebraMap (𝓞 ℚ) ℚ) = X (0, 0) := by
  simp [pointForm]

theorem NormIdentity.hypotheses_inhabited (v : HeightOneSpectrum (𝓞 ℚ)) :
    IsProjPrime (⊥ : Ideal (MvPolynomial (Fin 1) ℚ)) ∧
      IsChowForm (⊥ : Ideal (MvPolynomial (Fin 1) ℚ)) (0 + 1) (pointForm.map (algebraMap (𝓞 ℚ) ℚ)) ∧
      linForm (fun j => (((fun _ => (1 : 𝓞 ℚ)) : Fin 1 → 𝓞 ℚ) j : ℚ)) ∉
        (⊥ : Ideal (MvPolynomial (Fin 1) ℚ)) ∧
      ∃ m, pointForm.coeff m ∉ v.asIdeal := by
  refine ⟨isProjPrime_point ℚ, by rw [pointForm_map]; exact isChowForm_point ℚ, ?_, ?_⟩
  · simpa using linForm_one_not_mem_point ℚ
  · refine ⟨Finsupp.single (0, 0) 1, ?_⟩
    have h1 : pointForm.coeff (Finsupp.single (0, 0) 1) = 1 := by simp [pointForm]
    rw [h1]
    exact fun h => v.isPrime.ne_top ((Ideal.eq_top_iff_one _).mpr h)

theorem SecBFinite.hypotheses_inhabited :
    IsProjPrime (⊥ : Ideal (MvPolynomial (Fin 1) ℚ)) ∧
      IsChowForm (⊥ : Ideal (MvPolynomial (Fin 1) ℚ)) (0 + 1) (X (0, 0)) :=
  ⟨isProjPrime_point ℚ, isChowForm_point ℚ⟩

theorem GaussDVR.hypotheses_inhabited : (1 : MvPolynomial (Par 0 1) (𝓞 ℚ)) ≠ 0 := one_ne_zero

theorem PrimitiveScale.hypotheses_inhabited : (X 0 : MvPolynomial (Fin 1) ℚ) ≠ 0 := X_ne_zero 0

end

end GroundTheory.Heights₂.Heights.Vertical
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.IsChowFormCMul
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Vertical

open MvPolynomial NumberField IsDedekindDomain

noncomputable section

theorem isChowForm_C_mul {F : Type*} [Field F] {n k : ℕ} {I : Ideal (MvPolynomial (Fin n) F)}
    {f : MvPolynomial (Fin k × Fin n) F} (hf : IsChowForm I k f) {c : F} (hc : c ≠ 0) :
    IsChowForm I k (C c * f) := by
  refine ⟨mul_ne_zero (C_ne_zero.mpr hc) hf.1, fun g => ?_⟩
  have hu : IsUnit (C c : MvPolynomial (Fin k × Fin n) F) := hc.isUnit.map C
  rw [hf.2 g, IsUnit.mul_left_dvd hu]

theorem specFirst_C_mul {R : Type*} [CommSemiring R] {n k : ℕ} (c : R)
    (f : MvPolynomial (Fin (k + 1) × Fin n) R) (u : Fin n → R) :
    specFirst (C c * f) u = C c * specFirst f u := by
  simp [specFirst]

theorem Main.proof (h1 : GaussEq.Statement) (h2 : PrimitiveScale.Statement)
    (h3 : VertTermEq.Statement) : ChowFormSectionVertical.Statement := by
  intro K _ _ n e I f u hI hf hu v
  obtain ⟨c, g, hc, hg, hprim⟩ := h2 K v _ f hf.1
  have hcf : IsChowForm I (e + 1) (g.map (algebraMap (𝓞 K) K)) := by
    rw [hg]
    exact isChowForm_C_mul hf hc
  obtain ⟨h1a, h1b⟩ := h1 K n e I g u v hI hcf hu hprim
  rw [hg, specFirst_C_mul, gaussNorm_C_mul] at h1a
  rw [hg, gaussNorm_C_mul] at h1b
  rw [h3]
  set a := NumberField.HeightOneSpectrum.adicAbv K v c
  set N : ℝ := (Ideal.absNorm v.asIdeal : ℝ)
  set D := vertDeg e I u v
  have hN : 0 < N := by
    have h := Ideal.absNorm_ne_zero_of_nonZeroDivisors
      (⟨v.asIdeal, mem_nonZeroDivisors_of_ne_zero v.ne_bot⟩ : nonZeroDivisors (Ideal (𝓞 K)))
    have h' : 0 < Ideal.absNorm v.asIdeal := Nat.pos_of_ne_zero h
    exact Nat.cast_pos.mpr h'
  have ha : a ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at h1b
    exact zero_ne_one h1b
  have hfu : 0 < gaussNorm v (specFirst f fun j => (u j : K)) := by
    refine lt_of_le_of_ne (gaussNorm_nonneg v _) fun h0 => ?_
    rw [← h0, mul_zero, zero_mul] at h1a
    exact zero_ne_one h1a
  have hff : gaussNorm v f = gaussNorm v (specFirst f fun j => (u j : K)) * N ^ D := by
    have e1 : a * gaussNorm v f = a * (gaussNorm v (specFirst f fun j => (u j : K)) * N ^ D) := by
      rw [h1b, ← mul_assoc, h1a]
    exact mul_left_cancel₀ ha e1
  rw [hff, Real.log_mul hfu.ne' (pow_ne_zero _ hN.ne'), Real.log_pow]
  ring

end

end GroundTheory.Heights₂.Heights.Vertical
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.PChowSecDegree
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Vertical

open MvPolynomial

noncomputable section

theorem isHomogeneous_specRest {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S) {n e d : ℕ}
    {g : MvPolynomial (Fin (e + 1) × Fin n) R} (hg : IsMultiHomog d g) (y : Par e n → S) :
    (specRest φ g y).IsHomogeneous d := by
  classical
  rw [specRest, g.as_sum, eval₂_sum]
  refine IsHomogeneous.sum _ _ _ fun m hm => ?_
  rw [eval₂_monomial, Finsupp.prod]
  have hdeg : ∀ ij : Fin (e + 1) × Fin n,
      (Fin.cases (motive := fun _ => MvPolynomial (Fin n) S) (X ij.2)
        (fun i => C (y (.inl (i, ij.2)))) ij.1 : MvPolynomial (Fin n) S).IsHomogeneous
        (groupWeight (e + 1) n ij 0) := by
    rintro ⟨i, j⟩
    refine Fin.cases ?_ (fun i => ?_) i
    · simpa [groupWeight] using isHomogeneous_X (R := S) j
    · have h0 : groupWeight (e + 1) n (i.succ, j) 0 = 0 := by simp [groupWeight]
      rw [h0]
      exact isHomogeneous_C _ _
  have hsum : ∑ ij ∈ m.support, groupWeight (e + 1) n ij 0 * m ij = d := by
    have hw := hg (mem_support_iff.mp hm)
    have h0 := congrFun hw 0
    rw [Finsupp.weight_apply, Finsupp.sum, Finset.sum_apply] at h0
    rw [← h0]
    refine Finset.sum_congr rfl fun ij _ => ?_
    rw [Pi.smul_apply, smul_eq_mul, mul_comm]
  have h := (isHomogeneous_C (σ := Fin n) (φ (coeff m g))).mul
    (IsHomogeneous.prod m.support _ _ fun ij _ => (hdeg ij).pow (m ij))
  rw [zero_add, hsum] at h
  exact h

theorem isHomogeneous_det_linear {R : Type*} [CommRing R] {σ ι : Type*} [Fintype ι] [DecidableEq ι]
    (N : Matrix ι ι (MvPolynomial σ R)) (hN : ∀ i k, (N i k).IsHomogeneous 1) :
    N.det.IsHomogeneous (Fintype.card ι) := by
  rw [Matrix.det_apply]
  refine IsHomogeneous.sum _ _ _ fun τ _ => ?_
  have hp := IsHomogeneous.prod Finset.univ (fun i => N (τ i) i) (fun _ => 1) fun i _ => hN (τ i) i
  simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_one] at hp
  rw [Units.smul_def, zsmul_eq_mul, ← map_intCast (C : R →+* MvPolynomial σ R)]
  simpa using (isHomogeneous_C σ ((τ.sign : ℤ) : R)).mul hp

theorem ChowSecDegree.proof (h1 : ChowNormForm.Statement) (h2 : ChowFormHomog.Statement)
    (h3 : NormFormEval.Statement) : ChowSecDegree.Statement := by
  intro k E _ _ _ _ n e Q g y hy hQ hg
  classical
  obtain ⟨hfin, c, hc, heq⟩ := h1 k E n e Q g y hy hQ hg
  set QE := Q.map (MvPolynomial.map (algebraMap k E))
  have : Module.Finite E (SecAlg QE y) := hfin
  have : Module.Free E (SecAlg QE y) := Module.Free.of_divisionRing E (SecAlg QE y)
  let b : Module.Basis (Module.Free.ChooseBasisIndex E (SecAlg QE y)) E (SecAlg QE y) :=
    Module.Free.chooseBasis E (SecAlg QE y)
  have hN : (normForm (R := E) (SecAlg QE y) (secCoord QE y)).IsHomogeneous
      (Module.finrank E (SecAlg QE y)) := by
    rw [normForm_eq_det b, Module.finrank_eq_card_chooseBasisIndex]
    refine isHomogeneous_det_linear _ fun i k' => ?_
    simp only [Matrix.sum_apply, Matrix.smul_apply, Matrix.map_apply, smul_eq_mul]
    exact IsHomogeneous.sum _ _ _ fun j _ => by
      simpa using (isHomogeneous_X E j).mul (isHomogeneous_C (Fin n) _)
  have hone : (∑ j, algebraMap E (SecAlg QE y) (y (.inr j)) * secCoord QE y j) = 1 := by
    have hmem : chartForm y - 1 ∈ secIdeal QE y := Ideal.mem_sup_right (Ideal.subset_span rfl)
    have h := Ideal.Quotient.eq.mpr hmem
    rw [map_one] at h
    rw [← h]
    simp [chartForm, linForm, secCoord, map_sum, map_mul]
    rfl
  have hN0 : normForm (R := E) (SecAlg QE y) (secCoord QE y) ≠ 0 := by
    intro h0
    have hv := h3 E (SecAlg QE y) n (secCoord QE y) (fun j => y (.inr j))
    rw [h0, map_zero, hone, map_one] at hv
    exact zero_ne_one hv
  have hG : (specRest (algebraMap k E) g y).IsHomogeneous (chowDegree Q (e + 1)) :=
    isHomogeneous_specRest _ (h2 k n (e + 1) Q g hg) y
  rw [heq] at hG
  have hCN : (C c * normForm (R := E) (SecAlg QE y) (secCoord QE y)).IsHomogeneous
      (Module.finrank E (SecAlg QE y)) := by
    simpa using hN.C_mul c
  exact hCN.inj_right hG (mul_ne_zero (C_ne_zero.mpr hc) hN0)

end

end GroundTheory.Heights₂.Heights.Vertical
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.PFiniteOrd
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Vertical

theorem FiniteOrd.proof : FiniteOrd.Statement := by
  intro R B _ _ _ _ _ _ b hb 𝔫
  have : IsNoetherianRing B := IsNoetherianRing.of_finite R B

  have hB : ringKrullDim B ≤ ringKrullDim R :=
    Order.krullDim_le_of_strictMono
      (fun p : PrimeSpectrum B ↦
        (⟨Ideal.comap (algebraMap R B) p.asIdeal, inferInstance⟩ : PrimeSpectrum R))
      (fun p q hpq ↦ Ideal.IsIntegral.comap_lt_comap (R := R) (A := B) hpq)
  have hS : ringKrullDim (Localization.AtPrime 𝔫.asIdeal) ≤ 1 := by
    rw [IsLocalization.AtPrime.ringKrullDim_eq_height 𝔫.asIdeal (Localization.AtPrime 𝔫.asIdeal)]
    refine Ideal.height_le_ringKrullDim_of_isPrime.trans (hB.trans ?_)
    rw [IsDiscreteValuationRing.ringKrullDim_eq_one R]
  have : Ring.KrullDimLE 1 (Localization.AtPrime 𝔫.asIdeal) :=
    Ring.krullDimLE_iff.mpr (by exact_mod_cast hS)
  have hbB : b ∈ nonZeroDivisors B := by
    refine mem_nonZeroDivisors_iff.mpr ⟨fun x hx ↦ ?_, fun x hx ↦ hb (by simpa [mul_comm, mul_zero] using hx)⟩
    exact hb (by simpa [mul_comm, mul_zero] using hx)
  have hbS : algebraMap B (Localization.AtPrime 𝔫.asIdeal) b ∈
      nonZeroDivisors (Localization.AtPrime 𝔫.asIdeal) :=
    IsLocalization.map_nonZeroDivisors_le 𝔫.asIdeal.primeCompl _ ⟨b, hbB, rfl⟩
  exact Ring.ord_ne_top hbS

end GroundTheory.Heights₂.Heights.Vertical
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.PGaussEq
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Vertical

open MvPolynomial NumberField IsDedekindDomain

noncomputable section

theorem gaussNormOf_rename {R : Type*} [CommRing R] (w : AbsoluteValue R ℝ) {σ τ : Type*}
    {f : σ → τ} (hf : Function.Injective f) (x : MvPolynomial σ R) :
    gaussNormOf w (rename f x) = gaussNormOf w x := by
  classical
  apply le_antisymm
  · refine gaussNormOf_le w (gaussNormOf_nonneg w x) fun d => ?_
    by_cases hd : ∃ m, Finsupp.mapDomain f m = d
    · obtain ⟨m, rfl⟩ := hd
      rw [coeff_rename_mapDomain f hf]
      exact le_gaussNormOf w x m
    · rw [coeff_rename_eq_zero f x d fun m h => (hd ⟨m, h⟩).elim, map_zero]
      exact gaussNormOf_nonneg w x
  · refine gaussNormOf_le w (gaussNormOf_nonneg w _) fun m => ?_
    rw [← coeff_rename_mapDomain f hf]
    exact le_gaussNormOf w _ _

theorem specFirst_map {R S : Type*} [CommSemiring R] [CommSemiring S] (φ : R →+* S) {n k : ℕ}
    (g : MvPolynomial (Fin (k + 1) × Fin n) R) (u : Fin n → R) :
    specFirst (g.map φ) (fun j => φ (u j)) = (specFirst g u).map φ := by
  unfold specFirst
  rw [map_bind₁]
  congr 2
  funext ij
  rcases ij with ⟨i, j⟩
  refine Fin.cases ?_ (fun i => ?_) i
  · simp [specFirstVar]
  · simp [specFirstVar]

theorem gaussNorm_map_eq_one {K : Type*} [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))
    {σ : Type*} (g : MvPolynomial σ (𝓞 K)) (hg : ∃ m, g.coeff m ∉ v.asIdeal) :
    gaussNorm v (g.map (algebraMap (𝓞 K) K)) = 1 := by
  obtain ⟨m, hm⟩ := hg
  apply le_antisymm
  · refine gaussNormOf_le _ zero_le_one fun d => ?_
    rw [coeff_map, ← FinitePlace.norm_embedding]
    exact FinitePlace.norm_le_one K (v := v) (g.coeff d)
  · have h1 := le_gaussNormOf (NumberField.HeightOneSpectrum.adicAbv K v) (g.map (algebraMap (𝓞 K) K)) m
    rw [coeff_map, ← FinitePlace.norm_embedding, (FinitePlace.norm_eq_one_iff_notMem K (v := v) _).mpr hm] at h1
    exact h1

theorem GaussEq.proof (h1 : OrdEq.Statement) (h2 : GaussDVR.Statement) (h3 : ParDVRIsDVR.Statement) :
    GaussEq.Statement := by
  intro K _ _ n e I g u v hI hf hu hprim
  have := h3 K e n v
  have hord := h1 K n e I g u v hI hf hu hprim
  refine ⟨?_, gaussNorm_map_eq_one v g hprim⟩
  set h := rename (Sum.inl : Fin e × Fin n → Par e n) (specFirst g u) with hh
  have hne : h ≠ 0 := by
    intro h0
    rw [h0, map_zero, Ring.ord_eq_addVal, IsDiscreteValuationRing.addVal_zero] at hord
    exact ENat.top_ne_natCast _ hord
  have hG := h2 K e n v h hne
  rw [hord, ENat.toNat_natCast] at hG
  have hmap : h.map (algebraMap (𝓞 K) K) =
      rename (Sum.inl : Fin e × Fin n → Par e n) ((specFirst g u).map (algebraMap (𝓞 K) K)) := by
    rw [hh, map_rename]
  rw [hmap, gaussNorm_eq_gaussNormOf, gaussNormOf_rename _ Sum.inl_injective, ← gaussNorm_eq_gaussNormOf,
    ← specFirst_map] at hG
  exact hG

end

end GroundTheory.Heights₂.Heights.Vertical
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.PNormFormLocalization
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Vertical

open MvPolynomial

noncomputable section

theorem NormFormLocalization.proof : NormFormLocalization.Statement := by
  intro R F A A' _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ n x
  classical
  let b := Module.Free.chooseBasis R A
  let b' := b.localizationLocalization F (nonZeroDivisors R) A'
  have hM : ∀ j, Algebra.leftMulMatrix b' (algebraMap A A' (x j)) =
      (algebraMap R F).mapMatrix (Algebra.leftMulMatrix b (x j)) := fun j =>
    (Algebra.map_leftMulMatrix_localization R (nonZeroDivisors R) b (x j)).symm
  rw [normForm_eq_det b, normForm_eq_det b', RingHom.map_det]
  congr 1
  ext i k
  simp only [hM, RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.sum_apply, Matrix.smul_apply,
    smul_eq_mul, map_sum, map_mul, map_X, map_C]

end

end GroundTheory.Heights₂.Heights.Vertical
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.PVertTermEq
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Vertical

open MvPolynomial NumberField IsDedekindDomain

noncomputable section

theorem vertComps_finite {K : Type*} [Field K] [NumberField K] {n : ℕ}
    (I : Ideal (MvPolynomial (Fin n) K)) (u : Fin n → 𝓞 K) (v : HeightOneSpectrum (𝓞 K)) :
    (vertComps I u v).Finite :=
  (Ideal.finite_minimalPrimes_of_isNoetherianRing _ _).subset fun _ hW => hW.1.1

theorem VertTermEq.proof : VertTermEq.Statement := by
  intro K _ _ n e I u v
  have hfin := vertComps_finite I u v
  unfold vertTermAt vertDeg
  rw [finsum_mem_eq_finite_toFinset_sum _ hfin, finsum_mem_eq_finite_toFinset_sum _ hfin,
    Nat.cast_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun W _ => ?_
  push_cast
  ring

end

end GroundTheory.Heights₂.Heights.Vertical
end

