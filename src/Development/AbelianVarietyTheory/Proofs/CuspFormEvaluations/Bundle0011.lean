import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.Bundle0001
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.HasSumPolyDerivMulProdAddMatrix
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0010
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.Bundle0008
import Development.AbelianVarietyTheory.Definitions.ThetaValues.FlatMemLatIffStdLat
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.TraceHermNondegenerate
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0006
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.PointwiseNormSqPullbackTensorEqProd
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ContinuousThetaSectionPointwiseNormSq
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsBasisSpanEqOfCommensurable
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0010

-- bundled from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.L2CanThEqInvSqrtTwoPowMulDetIm
section
open Complex Matrix MeasureTheory
open ReciprocityTheory.ChartRestriction.G.I2 ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped Real

namespace GlobalTheory.CanTh

noncomputable section

variable {g : ℕ} {τ : Matrix (Fin g) (Fin g) ℂ}

variable (τ) in

def realPt : (Fin g ⊕ Fin g → ℝ) →ₗ[ℝ] (Fin g → ℂ) where
  toFun p := (fun i => (p (.inl i) : ℂ)) + τ *ᵥ fun i => (p (.inr i) : ℂ)
  map_add' p q := by
    funext i
    simp only [mulVec, dotProduct, Pi.add_apply, ofReal_add, mul_add, Finset.sum_add_distrib]
    ring
  map_smul' c p := by
    funext i
    simp only [mulVec, dotProduct, Pi.add_apply, Pi.smul_apply, smul_eq_mul, ofReal_mul,
      RingHom.id_apply, real_smul, mul_add, Finset.mul_sum, mul_left_comm]

theorem realPt_apply (p : Fin g ⊕ Fin g → ℝ) :
    realPt τ p = (fun i => (p (.inl i) : ℂ)) + τ *ᵥ fun i => (p (.inr i) : ℂ) := rfl

theorem realPt_injective (hs : τ.IsSymm) (hp : (τ.map Complex.im).PosDef) :
    Function.Injective (realPt τ) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro p hp0
  rw [realPt_apply] at hp0
  have him : ∀ i, ∑ j, (τ i j).im * p (.inr j) = 0 := by
    intro i
    have := congrArg (fun z => (z i).im) hp0
    simpa [mulVec, dotProduct] using this
  have hu : (fun i => p (.inr i)) = 0 := by
    by_contra hne
    have hpos := hp.dotProduct_mulVec_pos hne
    have hzero : (τ.map Complex.im) *ᵥ (fun i => p (.inr i)) = 0 := by
      funext i
      simpa [mulVec, dotProduct] using him i
    rw [hzero] at hpos
    simp at hpos
  have hu' : ∀ j, p (.inr j) = 0 := fun j => congrFun hu j
  have hre : ∀ i, p (.inl i) = 0 := by
    intro i
    have := congrArg (fun z => (z i).re) hp0
    simpa [mulVec, dotProduct, hu'] using this
  funext j
  rcases j with i | i
  · exact hre i
  · exact hu' i

theorem norm_canTh_realPt (hp : (τ.map Complex.im).PosDef) (a b : Fin g → ℝ)
    (p : Fin g ⊕ Fin g → ℝ) :
    ‖canTh τ a b (realPt τ p)‖ ^ 2 *
        Real.exp (-π * (hermForm (imInv τ) (realPt τ p) (realPt τ p)).re) =
      ‖thetaChar τ (fun i => (a i : ℂ)) (fun i => (b i : ℂ)) (realPt τ p)‖ ^ 2 *
        Real.exp (-2 * π * ((fun i => p (.inr i)) ⬝ᵥ (τ.map Complex.im) *ᵥ fun i => p (.inr i))) := by
  have hQ : realPt τ p ⬝ᵥ imInv τ *ᵥ realPt τ p =
      hermForm (imInv τ) (realPt τ p) (realPt τ p) +
        2 * I * (realPt τ p ⬝ᵥ fun i => (p (.inr i) : ℂ)) := by
    have h := dot_imInv_eq_hermForm_add hp (fun i => p (.inr i)) (fun i => p (.inl i)) (realPt τ p)
    rw [realPt_apply] at h ⊢
    exact h
  have hIm : (realPt τ p ⬝ᵥ fun i => (p (.inr i) : ℂ)).im =
      (fun i => p (.inr i)) ⬝ᵥ (τ.map Complex.im) *ᵥ fun i => p (.inr i) := by
    rw [realPt_apply]
    simp [dotProduct, mulVec, Complex.mul_im, Finset.mul_sum, mul_comm, mul_left_comm]
  have hre : ((π : ℂ) / 2 * (hermForm (imInv τ) (realPt τ p) (realPt τ p) +
      2 * I * (realPt τ p ⬝ᵥ fun i => (p (.inr i) : ℂ)))).re =
      π / 2 * (hermForm (imInv τ) (realPt τ p) (realPt τ p)).re -
        π * (realPt τ p ⬝ᵥ fun i => (p (.inr i) : ℂ)).im := by
    simp [Complex.mul_re]
    ring
  have key : ∀ A B C T : ℝ, 2 * A + B = C → Real.exp A ^ 2 * T * Real.exp B = T * Real.exp C := by
    intro A B C T h
    rw [← h, Real.exp_add, sq, ← Real.exp_add A A, two_mul]
    ring
  rw [canTh, hQ, norm_mul, mul_pow, Complex.norm_exp, hre, hIm]
  apply key
  ring

variable (hs : τ.IsSymm) (hp : (τ.map Complex.im).PosDef)
  (φ : EuclideanSpace ℂ (Fin g) ≃ₗ[ℂ] (Fin g → ℂ))

def realCoord : (Fin g ⊕ Fin g → ℝ) ≃ₗ[ℝ] EuclideanSpace ℂ (Fin g) :=
  ((realPt τ).linearEquivOfInjective (realPt_injective hs hp) (by
    simp [Module.finrank_pi_fintype, mul_two])).trans (φ.symm.restrictScalars ℝ)

theorem apply_realCoord (p : Fin g ⊕ Fin g → ℝ) : φ (realCoord hs hp φ p) = realPt τ p := by
  simp [realCoord]

def sumBasis : Module.Basis (Fin g ⊕ Fin g) ℝ (EuclideanSpace ℂ (Fin g)) :=
  (Pi.basisFun ℝ _).map (realCoord hs hp φ)

def perBasis : Module.Basis (Fin (2 * Fintype.card (Fin g))) ℝ (EuclideanSpace ℂ (Fin g)) :=
  (sumBasis hs hp φ).reindex (finSumFinEquiv.trans (finCongr (by simp [two_mul])))

theorem mem_lat_perBasis (y : EuclideanSpace ℂ (Fin g)) :
    y ∈ lat (perBasis hs hp φ) ↔
      ∃ m : Fin g ⊕ Fin g → ℤ, y = realCoord hs hp φ fun j => (m j : ℝ) := by
  have hsum : ∀ m : Fin g ⊕ Fin g → ℤ,
      ∑ j, m j • sumBasis hs hp φ j = realCoord hs hp φ fun j => (m j : ℝ) := by
    intro m
    have hm : (fun j => (m j : ℝ)) = ∑ j, (m j : ℝ) • Pi.single j (1 : ℝ) := by
      ext k
      simp [Finset.sum_apply, Pi.single_apply]
    simp only [sumBasis, Module.Basis.map_apply, Pi.basisFun_apply]
    rw [hm, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_smul, Int.cast_smul_eq_zsmul]
  show y ∈ Submodule.span ℤ (Set.range (perBasis hs hp φ)) ↔ _
  rw [perBasis, Module.Basis.range_reindex, Submodule.mem_span_range_iff_exists_fun]
  constructor
  · rintro ⟨c, hc⟩
    exact ⟨c, by rw [← hc, hsum]⟩
  · rintro ⟨m, hm⟩
    exact ⟨m, by rw [hsum, hm]⟩

variable (hφ : ∀ v w, Hf v w = hermForm (imInv τ) (φ v) (φ w))

include hφ in

theorem im_Hf_realCoord (p q : Fin g ⊕ Fin g → ℝ) :
    (Hf (realCoord hs hp φ p) (realCoord hs hp φ q)).im =
      ∑ i, p (.inr i) * q (.inl i) - ∑ i, p (.inl i) * q (.inr i) := by
  rw [hφ, apply_realCoord, apply_realCoord, realPt_apply, realPt_apply, im_hermForm_imInv hs hp]
  simp [dotProduct]

private theorem eq_realCoord_of_eq_int_add_tau_mulVec {y : EuclideanSpace ℂ (Fin g)} {m n : Fin g → ℤ}
    (h : φ y = (fun i => (m i : ℂ)) + τ *ᵥ fun i => (n i : ℂ)) :
    y = realCoord hs hp φ fun j => ((Sum.elim m n j : ℤ) : ℝ) := by
  apply φ.injective
  rw [apply_realCoord, realPt_apply, h]
  simp

def torus (a b : Fin g → ℝ) : GT (Fin g) where
  b := perBasis hs hp φ
  integral x y hx hy := by
    obtain ⟨m, rfl⟩ := (mem_lat_perBasis hs hp φ x).1 hx
    obtain ⟨n, rfl⟩ := (mem_lat_perBasis hs hp φ y).1 hy
    refine ⟨∑ i, m (.inr i) * n (.inl i) - ∑ i, m (.inl i) * n (.inr i), ?_⟩
    rw [im_Hf_realCoord hs hp φ hφ]
    push_cast
    rfl
  perfect f := by
    let e : Fin g ⊕ Fin g → lat (perBasis hs hp φ) := fun j =>
      ⟨_, (mem_lat_perBasis hs hp φ _).2 ⟨Pi.single j 1, rfl⟩⟩
    refine ⟨_, (mem_lat_perBasis hs hp φ _).2
      ⟨Sum.elim (fun i => -f (e (.inr i))) fun i => f (e (.inl i)), rfl⟩, fun y => ?_⟩
    obtain ⟨n, hn⟩ := (mem_lat_perBasis hs hp φ y).1 y.2
    have hy : y = ∑ j, n j • e j := by
      apply Subtype.ext
      simp only [hn, e, AddSubmonoidClass.coe_finset_sum, Submodule.coe_smul_of_tower,
        ← map_zsmul, ← map_sum]
      congr 1
      funext j
      simp [Pi.single_apply]
    rw [hn, im_Hf_realCoord hs hp φ hφ, hy, map_sum]
    simp [mul_comm]
  ka y := cexp (((π * ∑ i, (realCoord hs hp φ).symm y (.inl i) * (realCoord hs hp φ).symm y (.inr i) +
    2 * π * (∑ i, a i * (realCoord hs hp φ).symm y (.inl i) -
      ∑ i, b i * (realCoord hs hp φ).symm y (.inr i)) : ℝ) : ℂ) * I)
  ka_abs _ _ := norm_exp_ofReal_mul_I _

variable (a b : Fin g → ℝ)

theorem mem_lat_torus (y : EuclideanSpace ℂ (Fin g)) :
    y ∈ lat (torus hs hp φ hφ a b).b ↔
      ∃ m n : Fin g → ℤ, φ y = (fun i => (m i : ℂ)) + τ *ᵥ fun i => (n i : ℂ) := by
  show y ∈ lat (perBasis hs hp φ) ↔ _
  rw [mem_lat_perBasis]
  constructor
  · rintro ⟨k, rfl⟩
    refine ⟨fun i => k (.inl i), fun i => k (.inr i), ?_⟩
    rw [apply_realCoord, realPt_apply]
    simp
  · rintro ⟨m, n, h⟩
    exact ⟨Sum.elim m n, eq_realCoord_of_eq_int_add_tau_mulVec hs hp φ h⟩

theorem torus_ka {y : EuclideanSpace ℂ (Fin g)} {m n : Fin g → ℤ}
    (h : φ y = (fun i => (m i : ℂ)) + τ *ᵥ fun i => (n i : ℂ)) :
    (torus hs hp φ hφ a b).ka y = canMult a b m n := by
  rw [eq_realCoord_of_eq_int_add_tau_mulVec hs hp φ h]
  simp only [torus, LinearEquiv.symm_apply_apply, canMult, Sum.elim_inl, Sum.elim_inr]
  congr 1
  simp only [dotProduct]
  push_cast
  ring

theorem canTh_mem_Sec : (fun v => canTh τ a b (φ v)) ∈ (torus hs hp φ hφ a b).Sec 1 := by
  show _ ∧ _
  refine ⟨(differentiable_canTh hp a b).comp
    (LinearMap.toContinuousLinearMap φ.toLinearMap).differentiable, ?_⟩
  intro γ hγ v
  obtain ⟨m, n, h⟩ := (mem_lat_torus hs hp φ hφ a b γ).1 hγ
  beta_reduce
  rw [map_add, h, canTh_add_period hs hp a b m n rfl, torus_ka hs hp φ hφ a b h, hφ, hφ, h]
  simp only [Nat.cast_one, one_mul]
  ring_nf

private theorem norm_sq_eq_re_Hf (w : EuclideanSpace ℂ (Fin g)) : ‖w‖ ^ 2 = (Hf w w).re := by
  rw [EuclideanSpace.norm_sq_eq, Hf, Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Complex.mul_conj, Complex.ofReal_re, Complex.normSq_eq_norm_sq]

theorem l2_canTh_eq_inv_sqrt_two_pow_mul_det_im : (torus hs hp φ hφ a b).l2 1 (fun v => canTh τ a b (φ v)) =
    (Real.sqrt (2 ^ g * (τ.map Complex.im).det))⁻¹ := by
  have hpt : ∀ x : Fin g ⊕ Fin g → ℝ,
      (torus hs hp φ hφ a b).ptN2 1 (fun v => canTh τ a b (φ v))
          ((sumBasis hs hp φ).equivFun.symm x) =
        ‖thetaChar τ (fun i => (a i : ℂ)) (fun i => (b i : ℂ))
            ((fun i => (x (.inl i) : ℂ)) + τ.mulVec (fun i => (x (.inr i) : ℂ)))‖ ^ 2 *
          Real.exp (-2 * Real.pi *
            ((fun i => x (.inr i)) ⬝ᵥ (τ.map Complex.im).mulVec (fun i => x (.inr i)))) := by
    intro x
    have hx : (sumBasis hs hp φ).equivFun.symm x = realCoord hs hp φ x := by
      simp [sumBasis, Module.Basis.map_equivFun]
    simp only [hx, GT.ptN2]
    rw [norm_sq_eq_re_Hf, hφ, apply_realCoord, Nat.cast_one, one_mul, norm_canTh_realPt hp,
      realPt_apply]
  have hfd : ZSpan.fundamentalDomain (torus hs hp φ hφ a b).b =
      ZSpan.fundamentalDomain (sumBasis hs hp φ) :=
    ZSpan.fundamentalDomain_reindex (b := sumBasis hs hp φ) _
  rw [GT.l2, hfd, avg_fd_cube, cubeIco_eq]
  simp_rw [hpt]
  exact GlobalTheory.ThetaNorm.integral_norm_sq_thetaChar g τ a b hs hp

end

end GlobalTheory.CanTh
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.NormalisedThetaValueBound
section
namespace GlobalTheory.TensorLat

open NumberField Complex ReciprocityTheory.ChartRestriction.G.I2 ReciprocityTheory.ChartRestriction.G.FD
open ReciprocityTheory.GeometryOfNumbersTheory (stdLat)

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

theorem isogeny_sum_tensorLat (T : PT E) (w₀ : 𝓞 E) (hw : (w₀ : E) + cc (w₀ : E) = 1)
    (heps : ∀ x ∈ T.L, (T.eps x : ℝ) = Real.cos (Real.pi * (Hf x (act w₀ x)).im))
    (Λ' : Submodule (𝓞 E) (Fin n → E)) (hfg : Λ'.FG)
    (hint : ∀ x ∈ Λ', ∀ y ∈ Λ', IsIntegral ℤ (herm 1 x y))
    (hdual : ∀ x, (∀ y ∈ Λ', IsIntegral ℤ (herm 1 x y)) → x ∈ Λ')
    (R : Finset (Fin n → Vsp T.dim)) (hR : ∀ y ∈ R, y ∈ tensorLat T Λ')
    (hR' : ∀ y ∈ tensorLat T Λ', ∃! r, r ∈ R ∧ ∀ k, y k - r k ∈ T.L)
    (F : (Fin n → Vsp T.dim) → ℂ) (hF : F ∈ T.Sec 1 n)
    (Y' : GT (Fin n × Idx T.dim)) (hY' : ∀ γ, flat γ ∈ lat Y'.b ↔ γ ∈ tensorLat T Λ')
    (hka' : ∀ γ, Y'.ka (flat γ) = tensorEps w₀ γ) :
    (∑ y ∈ R, tensorEps w₀ y • T.U 1 y F) ∘ flat.symm ∈ Y'.Sec 1 ∧
      Y'.l2 1 ((∑ y ∈ R, tensorEps w₀ y • T.U 1 y F) ∘ flat.symm) = R.card * T.l2 1 F := by
  classical
  obtain ⟨⟨Y, hY, hka⟩, h2, h3, h4⟩ := principal_torus_of_selfDual T (stdLat E n) stdLat_fg
    (fun _ hx => mem_stdLat_iff_herm.1 hx) (fun _ hx => mem_stdLat_iff_herm.2 hx) w₀ hw
  obtain ⟨-, h2', -, -⟩ := principal_torus_of_selfDual T Λ' hfg hint hdual w₀ hw
  obtain ⟨hFm, hFl⟩ := (h3 heps Y hY hka).2 F hF
  set U : ℕ → EuclideanSpace ℂ (Fin n × Idx T.dim) → (EuclideanSpace ℂ (Fin n × Idx T.dim) → ℂ) →
      EuclideanSpace ℂ (Fin n × Idx T.dim) → ℂ := fun q a G v =>
    cexp (q * Real.pi * Hf v a - q * Real.pi * Hf a a / 2) * G (v - a) with hUdef
  have hU : ∀ (q : ℕ) a G v,
      U q a G v = cexp (q * Real.pi * Hf v a - q * Real.pi * Hf a a / 2) * G (v - a) :=
    fun _ _ _ _ => rfl
  let e : (Fin n → Vsp T.dim) ↪ EuclideanSpace ℂ (Fin n × Idx T.dim) :=
    ⟨flat, (flat (n := n) (ι := Idx T.dim)).injective⟩
  have he : ∀ y, e y = flat y := fun _ => rfl
  have key := isogeny_sum_mem_and_norm U hU Y Y' (h2 Y hY hka).2 (h2' Y' hY' hka').2
    (fun x _ _ => by
      obtain ⟨γ, rfl⟩ := (flat (n := n) (ι := Idx T.dim)).surjective x
      rw [hka, hka'])
    (R.map e)
    (fun y hy => by
      obtain ⟨γ, hγ, rfl⟩ := Finset.mem_map.1 hy
      exact (hY' γ).2 (hR γ hγ))
    (fun y hy => by
      obtain ⟨γ, rfl⟩ := (flat (n := n) (ι := Idx T.dim)).surjective y
      obtain ⟨r, ⟨hr, hr'⟩, hu⟩ := hR' γ ((hY' γ).1 hy)
      refine ⟨flat r, ⟨Finset.mem_map.2 ⟨r, hr, rfl⟩, ?_⟩, ?_⟩
      · rw [← map_sub, hY, mem_tensorLat_stdLat]
        exact hr'
      · rintro z ⟨hz, hz'⟩
        obtain ⟨r', hr2, rfl⟩ := Finset.mem_map.1 hz
        rw [he, ← map_sub, hY, mem_tensorLat_stdLat] at hz'
        rw [he, hu r' ⟨hr2, hz'⟩])
    (F ∘ flat.symm) hFm
  have e1 : (∑ y ∈ R.map e, Y'.ka y • U 1 y (F ∘ flat.symm)) =
      (∑ y ∈ R, tensorEps w₀ y • T.U 1 y F) ∘ flat.symm := by
    rw [Finset.sum_map]
    funext v
    simp only [he, hka', h4 U hU, Finset.sum_apply, Function.comp_apply, Pi.smul_apply]
  rw [e1, Finset.card_map, hFl] at key
  exact key

theorem exists_min_period (T : PT E) (Λ' : Submodule (𝓞 E) (Fin n → E)) (hfg : Λ'.FG)
    (hint : ∀ x ∈ Λ', ∀ y ∈ Λ', IsIntegral ℤ (herm 1 x y))
    (hdual : ∀ x, (∀ y ∈ Λ', IsIntegral ℤ (herm 1 x y)) → x ∈ Λ')
    {lam : ℝ} (hlam : 0 < lam) (hmin : ∀ x ∈ T.L, x ≠ 0 → lam ≤ ‖x‖) :
    ∃ lam' : ℝ, 0 < lam' ∧ (∀ γ ∈ tensorLat T Λ', γ ≠ 0 → lam' ≤ ‖flat γ‖) ∧
      (1 + 4 * Real.sqrt (2 * Fintype.card (Fin n × Idx T.dim)) / (Real.sqrt Real.pi * lam')) ^
          Fintype.card (Fin n × Idx T.dim) =
        (1 + 4 * Real.sqrt (2 * Fintype.card (Idx T.dim) * n) *
          (2 * (fdeg E : ℝ) ^ ((3 : ℝ) / 2) * n ^ 2 * rdE E) / (Real.sqrt Real.pi * lam)) ^
          (Fintype.card (Idx T.dim) * n) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact ⟨1, one_pos, fun γ _ h => absurd (Subsingleton.elim γ 0) h, by simp⟩
  have hf : (0 : ℝ) < fdeg E := by
    have h1 := ShortVectors.finrank_eq (E := E)
    have h2 : 0 < Module.finrank ℚ E := Module.finrank_pos
    exact_mod_cast (by omega : 0 < fdeg E)
  have hr : 0 < rdE E := Real.rpow_pos_of_pos
    (abs_pos.mpr (by exact_mod_cast NumberField.discr_ne_zero E)) _
  have hρ : 0 < 2 * (fdeg E : ℝ) ^ ((3 : ℝ) / 2) * n ^ 2 * rdE E := by positivity
  have hpi : 0 < Real.sqrt Real.pi := Real.sqrt_pos.mpr Real.pi_pos
  set ρ := 2 * (fdeg E : ℝ) ^ ((3 : ℝ) / 2) * n ^ 2 * rdE E with hρdef
  refine ⟨lam / ρ, by positivity, fun γ hγ h0 => ?_, ?_⟩
  · rw [div_le_iff₀' hρ]
    exact le_mul_norm_flat_of_selfDual T Λ' hfg hint hdual hmin hγ h0
  · rw [Fintype.card_prod, Fintype.card_fin, mul_comm n, Nat.cast_mul, ← mul_assoc]
    congr 2
    field_simp

open Classical in

theorem norm_sum_jet_isogeny_sum_le (T : PT E) (w₀ : 𝓞 E) (hw : (w₀ : E) + cc (w₀ : E) = 1)
    (heps : ∀ x ∈ T.L, (T.eps x : ℝ) = Real.cos (Real.pi * (Hf x (act w₀ x)).im))
    (Λ' : Submodule (𝓞 E) (Fin n → E)) (hfg : Λ'.FG)
    (hint : ∀ x ∈ Λ', ∀ y ∈ Λ', IsIntegral ℤ (herm 1 x y))
    (hdual : ∀ x, (∀ y ∈ Λ', IsIntegral ℤ (herm 1 x y)) → x ∈ Λ')
    (R : Finset (Fin n → Vsp T.dim)) (hR : ∀ y ∈ R, y ∈ tensorLat T Λ')
    (hR' : ∀ y ∈ tensorLat T Λ', ∃! r, r ∈ R ∧ ∀ k, y k - r k ∈ T.L)
    (F : (Fin n → Vsp T.dim) → ℂ) (hF : F ∈ T.Sec 1 n)
    (lam : ℝ) (hlam : 0 < lam) (hmin : ∀ γ ∈ T.L, γ ≠ 0 → lam ≤ ‖γ‖)
    {κ : Type} (J : Finset κ) (c : κ → ℂ) (hc : ∀ j ∈ J, ‖c j‖ ≤ 1) (y : κ → Fin n → Vsp T.dim)
    (P : MvPolynomial (Letter n T.dim) ℂ) (a : ℕ) (hP : P.IsHomogeneous a) :
    ‖∑ j ∈ J, c j * polyDeriv P dir (T.U 1 (y j) (∑ r ∈ R, tensorEps w₀ r • T.U 1 r F)) 0‖ ≤
      J.card * (∑ m ∈ P.support, ‖P.coeff m‖) * (Real.pi * Real.exp 1 * a) ^ ((a : ℝ) / 2) *
        Real.sqrt 2 * (1 + 4 * Real.sqrt (2 * Fintype.card (Idx T.dim) * n) *
          (2 * (fdeg E : ℝ) ^ ((3 : ℝ) / 2) * n ^ 2 * rdE E) / (Real.sqrt Real.pi * lam)) ^
          (Fintype.card (Idx T.dim) * n) * Real.sqrt (R.card * T.l2 1 F) := by
  obtain ⟨Y', hY', hka'⟩ := exists_tensorTorus (X := T) hfg hint hdual w₀
  obtain ⟨hm, hl⟩ := isogeny_sum_tensorLat T w₀ hw heps Λ' hfg hint hdual R hR hR' F hF Y' hY' hka'
  obtain ⟨lam', hlam', hmin', hC⟩ := exists_min_period T Λ' hfg hint hdual hlam hmin
  set U : ℕ → EuclideanSpace ℂ (Fin n × Idx T.dim) → (EuclideanSpace ℂ (Fin n × Idx T.dim) → ℂ) →
      EuclideanSpace ℂ (Fin n × Idx T.dim) → ℂ := fun q a G v =>
    cexp (q * Real.pi * Hf v a - q * Real.pi * Hf a a / 2) * G (v - a) with hUdef
  have hU : ∀ (q : ℕ) a G v,
      U q a G v = cexp (q * Real.pi * Hf v a - q * Real.pi * Hf a a / 2) * G (v - a) :=
    fun _ _ _ _ => rfl
  have key := theta_value_bound sup_le_l2_principal_torus U hU Y' _ hm lam' hlam'
    (fun x hx h0 => by
      obtain ⟨γ, rfl⟩ := (flat (n := n) (ι := Idx T.dim)).surjective x
      exact hmin' γ ((hY' γ).1 hx) fun h => h0 (by rw [h, map_zero]))
    J c hc (fun j => flat (y j)) P a hP
  rw [hl, hC] at key
  refine le_of_eq_of_le ?_ (key.trans_eq (by ring))
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [translate_comp_flat_symm T U hU, ← polyDeriv_comp_flat_symm, map_zero]
  congr!

end GlobalTheory.TensorLat

namespace GlobalTheory

open NumberField Complex ReciprocityTheory.ChartRestriction.G.I2 ReciprocityTheory.ChartRestriction.G.FD TensorLat

open Classical in

theorem normalised_theta_value_bound {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}
    (T : PT E) (w₀ : 𝓞 E) (hw : (w₀ : E) + cc (w₀ : E) = 1)
    (heps : ∀ x ∈ T.L, (T.eps x : ℝ) = Real.cos (Real.pi * (Hf x (act w₀ x)).im))
    (s : (Fin 1 → Vsp T.dim) → ℂ) (hs : s ∈ T.Sec 1 1) (hs0 : s ≠ 0)
    (Λ' : Submodule (𝓞 E) (Fin n → E)) (hfg : Λ'.FG)
    (hint : ∀ x ∈ Λ', ∀ y ∈ Λ', IsIntegral ℤ (herm 1 x y))
    (hdual : ∀ x, (∀ y ∈ Λ', IsIntegral ℤ (herm 1 x y)) → x ∈ Λ')
    (R : Finset (Fin n → Vsp T.dim)) (hR : ∀ y ∈ R, y ∈ tensorLat T Λ')
    (hR' : ∀ y ∈ tensorLat T Λ', ∃! r, r ∈ R ∧ ∀ k, y k - r k ∈ T.L)
    (β : ℂ) (hβ : ‖β‖ ^ 2 = R.card)
    (lam : ℝ) (hlam : 0 < lam) (hmin : ∀ γ ∈ T.L, γ ≠ 0 → lam ≤ ‖γ‖)
    {κ : Type} (J : Finset κ) (c : κ → ℂ) (hc : ∀ j ∈ J, ‖c j‖ ≤ 1) (y : κ → Fin n → Vsp T.dim)
    (P : MvPolynomial (Letter n T.dim) ℂ) (a : ℕ) (hP : P.IsHomogeneous a) :
    β ≠ 0 ∧ 0 < T.l2 1 s ∧
    ‖β⁻¹ * ∑ j ∈ J, c j * polyDeriv P dir (T.U 1 (y j)
        (∑ r ∈ R, tensorEps w₀ r • T.U 1 r (ReciprocityTheory.ChartRestriction.G.I2.tens T fun _ => s))) 0‖ /
        Real.sqrt (T.l2 1 s) ^ n ≤
      J.card * (∑ m ∈ P.support, ‖P.coeff m‖) * (Real.pi * Real.exp 1 * a) ^ ((a : ℝ) / 2) *
        Real.sqrt 2 * (1 + 4 * Real.sqrt (2 * Fintype.card (Idx T.dim) * n) *
          (2 * (fdeg E : ℝ) ^ ((3 : ℝ) / 2) * n ^ 2 * rdE E) / (Real.sqrt Real.pi * lam)) ^
          (Fintype.card (Idx T.dim) * n) := by
  have hl : 0 < T.l2 1 s := ThetaBound.l2_pos_of_mem_sec_of_ne_zero T le_rfl hs hs0
  have hRpos : 0 < R.card := by
    obtain ⟨r, ⟨hr, -⟩, -⟩ := hR' 0 (Submodule.zero_mem _)
    exact Finset.card_pos.2 ⟨r, hr⟩
  have hβ0 : β ≠ 0 := by
    rintro rfl
    rw [norm_zero, zero_pow two_ne_zero] at hβ
    exact hRpos.ne (by exact_mod_cast hβ)
  refine ⟨hβ0, hl, ?_⟩
  have key := norm_sum_jet_isogeny_sum_le T w₀ hw heps Λ' hfg hint hdual R hR hR'
    (ReciprocityTheory.ChartRestriction.G.I2.tens T fun _ => s) (tens_mem T fun _ => hs) lam hlam hmin J c hc y P a hP
  have hsq : Real.sqrt (R.card * T.l2 1 (ReciprocityTheory.ChartRestriction.G.I2.tens T fun _ : Fin n => s)) =
      ‖β‖ * Real.sqrt (T.l2 1 s) ^ n := by
    rw [l2_tens_eq_prod, Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← hβ,
      Real.sqrt_eq_iff_mul_self_eq (by positivity) (by positivity), mul_mul_mul_comm, ← mul_pow,
      Real.mul_self_sqrt hl.le, sq]
  have hb : 0 < ‖β‖ := norm_pos_iff.2 hβ0
  have hs' : 0 < Real.sqrt (T.l2 1 s) ^ n := pow_pos (Real.sqrt_pos.2 hl) n
  rw [hsq] at key
  rw [norm_mul, norm_inv, div_le_iff₀ hs', inv_mul_le_iff₀ hb]
  exact key.trans_eq (by ring)

example {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ} (T : PT E) :
    (∀ y ∈ ({0} : Finset (Fin n → Vsp T.dim)), y ∈ tensorLat T (ReciprocityTheory.GeometryOfNumbersTheory.stdLat E n)) ∧
      ∀ y ∈ tensorLat T (ReciprocityTheory.GeometryOfNumbersTheory.stdLat E n),
        ∃! r, r ∈ ({0} : Finset (Fin n → Vsp T.dim)) ∧ ∀ k, y k - r k ∈ T.L := by
  refine ⟨fun y hy => by rw [Finset.mem_singleton.1 hy]; exact Submodule.zero_mem _,
    fun y hy => ⟨0, ⟨Finset.mem_singleton_self _, fun k => ?_⟩,
      fun r hr => Finset.mem_singleton.1 hr.1⟩⟩
  simpa using mem_tensorLat_stdLat.1 hy k

end GlobalTheory
end

