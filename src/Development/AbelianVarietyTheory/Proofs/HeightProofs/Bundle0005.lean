import Mathlib
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Bundle0003
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0003
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes

-- bundled from Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsSignatureDecompositionDiagonal
section
open Matrix

namespace GlobalTheory.MonomialDiag

private theorem star_inv_sqrt_abs_mul_mul_inv_sqrt_abs_eq_sign (x : ℝ) (hx : x ≠ 0) :
    star ((Real.sqrt |x| : ℝ) : ℂ)⁻¹ * (x : ℂ) * ((Real.sqrt |x| : ℝ) : ℂ)⁻¹ =
      if 0 < x then (1 : ℂ) else -1 := by
  have hst : star ((Real.sqrt |x| : ℝ) : ℂ) = ((Real.sqrt |x| : ℝ) : ℂ) := Complex.conj_ofReal _
  have hs : Real.sqrt |x| * Real.sqrt |x| = |x| := Real.mul_self_sqrt (abs_nonneg x)
  rw [star_inv₀, hst,
    show ((Real.sqrt |x| : ℝ) : ℂ)⁻¹ * (x : ℂ) * ((Real.sqrt |x| : ℝ) : ℂ)⁻¹ =
      ((x / (Real.sqrt |x| * Real.sqrt |x|) : ℝ) : ℂ) by push_cast; ring, hs]
  split_ifs with h
  · rw [abs_of_pos h, div_self hx, Complex.ofReal_one]
  · rw [abs_of_neg (lt_of_le_of_ne (not_lt.mp h) hx), div_neg_self hx]
    push_cast
    ring

private theorem star_sqrt_abs_mul_sign_mul_sqrt_abs_eq (x : ℝ) (hx : x ≠ 0) :
    star ((Real.sqrt |x| : ℝ) : ℂ) * (if 0 < x then (1 : ℂ) else -1) * ((Real.sqrt |x| : ℝ) : ℂ) =
      (x : ℂ) := by
  have hst : star ((Real.sqrt |x| : ℝ) : ℂ) = ((Real.sqrt |x| : ℝ) : ℂ) := Complex.conj_ofReal _
  have hs : Real.sqrt |x| * Real.sqrt |x| = |x| := Real.mul_self_sqrt (abs_nonneg x)
  rw [hst]
  split_ifs with h
  · rw [mul_one, ← Complex.ofReal_mul, hs, abs_of_pos h]
  · rw [mul_neg_one, neg_mul, ← Complex.ofReal_mul, hs, abs_of_neg (lt_of_le_of_ne (not_lt.mp h) hx)]
    push_cast
    ring

private theorem Jpq_equiv_apply_eq_ite_sign {n p q : ℕ} (d : Fin n → ℝ) (e : Fin n ≃ Fin p ⊕ Fin q)
    (he : ∀ i, 0 < d i ↔ (e i).isLeft = true) (i j : Fin n) :
    Formalism.UG.Jpq p q (e i) (e j) = if i = j then (if 0 < d i then (1 : ℂ) else -1) else 0 := by
  unfold Formalism.UG.Jpq
  by_cases hij : i = j
  · subst hij
    rw [if_pos rfl]
    have hi := he i
    revert hi
    generalize e i = x
    rcases x with a | a <;> intro hi <;> simp_all
  · have hne : e i ≠ e j := fun h => hij (e.injective h)
    rw [if_neg hij]
    revert hne
    generalize e i = x
    generalize e j = y
    rcases x with a | a <;> rcases y with b | b <;> intro hne <;> simp_all

private theorem conjTranspose_mul_diagonal_mul_inv_sqrt_eq_Jpq {n p q : ℕ} (d : Fin n → ℝ) (hd : ∀ i, d i ≠ 0)
    (e : Fin n ≃ Fin p ⊕ Fin q) (he : ∀ i, 0 < d i ↔ (e i).isLeft = true)
    (C : Matrix (Fin n) (Fin p ⊕ Fin q) ℂ)
    (hC : ∀ i a, C i a = if i = e.symm a then ((Real.sqrt |d i| : ℝ) : ℂ)⁻¹ else 0) :
    Cᴴ * Matrix.diagonal (fun i => (d i : ℂ)) * C = Formalism.UG.Jpq p q := by
  ext a b
  have key := Jpq_equiv_apply_eq_ite_sign d e he (e.symm a) (e.symm b)
  rw [e.apply_symm_apply, e.apply_symm_apply] at key
  rw [key, Matrix.mul_apply, Finset.sum_eq_single (e.symm b)]
  · rw [Matrix.mul_diagonal, Matrix.conjTranspose_apply, hC, hC]
    simp only [↓reduceIte]
    by_cases hab : e.symm a = e.symm b
    · rw [if_pos hab.symm, if_pos hab, hab]
      exact star_inv_sqrt_abs_mul_mul_inv_sqrt_abs_eq_sign _ (hd _)
    · rw [if_neg (Ne.symm hab), if_neg hab, star_zero, zero_mul, zero_mul]
  · intro i _ hi
    rw [hC i b, if_neg hi, mul_zero]
  · intro h
    exact absurd (Finset.mem_univ _) h

private theorem conjTranspose_mul_Jpq_mul_sqrt_eq_diagonal {n p q : ℕ} (d : Fin n → ℝ) (hd : ∀ i, d i ≠ 0)
    (e : Fin n ≃ Fin p ⊕ Fin q) (he : ∀ i, 0 < d i ↔ (e i).isLeft = true)
    (B : Matrix (Fin p ⊕ Fin q) (Fin n) ℂ)
    (hB : ∀ a i, B a i = if a = e i then ((Real.sqrt |d i| : ℝ) : ℂ) else 0) :
    Bᴴ * Formalism.UG.Jpq p q * B = Matrix.diagonal (fun i => (d i : ℂ)) := by
  ext i j
  rw [Matrix.mul_apply, Finset.sum_eq_single (e j)]
  · rw [Matrix.mul_apply, Finset.sum_eq_single (e i)]
    · rw [Matrix.conjTranspose_apply, hB, hB]
      simp only [↓reduceIte]
      rw [Jpq_equiv_apply_eq_ite_sign d e he, Matrix.diagonal_apply]
      by_cases hij : i = j
      · subst hij
        simp only [↓reduceIte]
        exact star_sqrt_abs_mul_sign_mul_sqrt_abs_eq _ (hd _)
      · rw [if_neg hij, if_neg hij, mul_zero, zero_mul]
    · intro b _ hb
      rw [Matrix.conjTranspose_apply, hB, if_neg hb, star_zero, zero_mul]
    · intro h
      exact absurd (Finset.mem_univ _) h
  · intro a _ ha
    rw [hB a j, if_neg ha, mul_zero]
  · intro h
    exact absurd (Finset.mem_univ _) h

theorem exists_monomial : ∀ (n p q : ℕ) (G Q : Matrix (Fin n) (Fin n) ℂ) (d : Fin n → ℝ), Formalism.UG.HasSignature G p q → Q.det ≠ 0 → (∀ i, d i ≠ 0) → Qᴴ * G * Q = Matrix.diagonal (fun i => (d i : ℂ)) → ∃ A : Matrix (Fin p ⊕ Fin q) (Fin n) ℂ, Aᴴ * Formalism.UG.Jpq p q * A = G ∧ ∀ a i j, (A * Q) a i ≠ 0 → (A * Q) a j ≠ 0 → i = j := by
  intro n p q G Q d hG hQ hd hQG
  classical
  obtain ⟨hcard, Q₁, hQ₁⟩ := Formalism.UG.P.sig_data G p q hG
  rw [Fintype.card_fin] at hcard

  let e₀ : Fin n ≃ Fin (Fintype.card {i // 0 < d i}) ⊕ Fin (Fintype.card {i // ¬ 0 < d i}) :=
    (Equiv.sumCompl (fun i => 0 < d i)).symm.trans
      (Equiv.sumCongr (Fintype.equivFin _) (Fintype.equivFin _))
  have he₀ : ∀ i, 0 < d i ↔ (e₀ i).isLeft = true := by
    intro i
    by_cases h : 0 < d i
    · simp [e₀, h]
    · simp [e₀, h]
  have hn₀ : n = Fintype.card {i // 0 < d i} + Fintype.card {i // ¬ 0 < d i} := by
    simpa using Fintype.card_congr e₀

  have h₂ : (Q * Matrix.of (fun i a => if i = e₀.symm a then ((Real.sqrt |d i| : ℝ) : ℂ)⁻¹ else 0))ᴴ *
      G * (Q * Matrix.of (fun i a => if i = e₀.symm a then ((Real.sqrt |d i| : ℝ) : ℂ)⁻¹ else 0)) =
      Formalism.UG.Jpq _ _ := by
    rw [Matrix.conjTranspose_mul]
    calc _ = (Matrix.of (fun i a => if i = e₀.symm a then ((Real.sqrt |d i| : ℝ) : ℂ)⁻¹ else 0))ᴴ *
          (Qᴴ * G * Q) * Matrix.of (fun i a => if i = e₀.symm a then ((Real.sqrt |d i| : ℝ) : ℂ)⁻¹ else 0) := by
          simp only [Matrix.mul_assoc]
      _ = _ := by
          rw [hQG]
          exact conjTranspose_mul_diagonal_mul_inv_sqrt_eq_Jpq d hd e₀ he₀ _ (fun i a => rfl)
  have i1 := Formalism.UG.P.sig_dim G Q₁ hQ₁ _ h₂
  have i2 := Formalism.UG.P.sig_dim G _ h₂ Q₁ hQ₁
  rw [Fintype.card_fin] at i1 i2
  have hp : Fintype.card {i // 0 < d i} = p := by omega
  have hq : Fintype.card {i // ¬ 0 < d i} = q := by omega
  let e : Fin n ≃ Fin p ⊕ Fin q := e₀.trans (Equiv.sumCongr (finCongr hp) (finCongr hq))
  have he : ∀ i, 0 < d i ↔ (e i).isLeft = true := by
    intro i
    rw [he₀ i]
    simp only [e, Equiv.trans_apply]
    cases e₀ i <;> rfl
  let B : Matrix (Fin p ⊕ Fin q) (Fin n) ℂ :=
    Matrix.of (fun a i => if a = e i then ((Real.sqrt |d i| : ℝ) : ℂ) else 0)
  have hB : Bᴴ * Formalism.UG.Jpq p q * B = Matrix.diagonal (fun i => (d i : ℂ)) :=
    conjTranspose_mul_Jpq_mul_sqrt_eq_diagonal d hd e he B (fun a i => rfl)
  have hQu : IsUnit Q.det := isUnit_iff_ne_zero.mpr hQ
  have hQQ : Q * Q⁻¹ = 1 := Q.mul_nonsing_inv hQu
  have hQQ' : (Q⁻¹)ᴴ * Qᴴ = 1 := by
    rw [← Matrix.conjTranspose_mul, hQQ, Matrix.conjTranspose_one]
  refine ⟨B * Q⁻¹, ?_, ?_⟩
  · calc (B * Q⁻¹)ᴴ * Formalism.UG.Jpq p q * (B * Q⁻¹) = (Q⁻¹)ᴴ * (Bᴴ * Formalism.UG.Jpq p q * B) * Q⁻¹ := by
          rw [Matrix.conjTranspose_mul]
          simp only [Matrix.mul_assoc]
      _ = (Q⁻¹)ᴴ * (Qᴴ * G * Q) * Q⁻¹ := by rw [hB, hQG]
      _ = ((Q⁻¹)ᴴ * Qᴴ) * G * (Q * Q⁻¹) := by simp only [Matrix.mul_assoc]
      _ = G := by rw [hQQ', hQQ, Matrix.one_mul, Matrix.mul_one]
  · intro a i j hi hj
    have hBQ : B * Q⁻¹ * Q = B := by
      rw [Matrix.mul_assoc, Q.nonsing_inv_mul hQu, Matrix.mul_one]
    rw [hBQ] at hi hj
    have hai : a = e i := by
      by_contra h
      exact hi (by simp [B, h])
    have haj : a = e j := by
      by_contra h
      exact hj (by simp [B, h])
    exact e.injective (hai.symm.trans haj)

end GlobalTheory.MonomialDiag
end

-- bundled from Development.AbelianVarietyTheory.Proofs.HeightProofs.HasSmoothLogNearOneOfIsUnitaryLieExpData
section
open GlobalTheory.SmoothForms NumberField Matrix
open scoped ContDiff Topology

namespace GlobalTheory.SmoothForms

theorem anti_map_exp {𝔸 : Type} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [FiniteDimensional ℝ 𝔸] (σ : 𝔸 →ₗ[ℝ] 𝔸)
    (anti : ∀ a b, σ (a * b) = σ b * σ a) (one : σ 1 = 1) (X : 𝔸) :
    σ (NormedSpace.exp X) = NormedSpace.exp (σ X) := by
  haveI : CompleteSpace 𝔸 := FiniteDimensional.complete ℝ 𝔸
  have hp : ∀ n : ℕ, σ (X ^ n) = σ X ^ n := fun n => by
    induction n with
    | zero => simpa using one
    | succ n ih => rw [pow_succ, anti, ih, pow_succ']
  have h1 := (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℝ) X).map σ.toAddMonoidHom
    σ.continuous_of_finiteDimensional
  refine h1.unique ?_
  convert NormedSpace.exp_series_hasSum_exp' (𝕂 := ℝ) (σ X) using 1
  funext n
  simp [hp]

theorem exists_local_log (𝔸 : Type) [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [FiniteDimensional ℝ 𝔸] :
    ∃ l : 𝔸 → 𝔸, ContDiffAt ℝ ∞ l 1 ∧ (∀ᶠ h in 𝓝 (1 : 𝔸), NormedSpace.exp (l h) = h) ∧
      ∀ᶠ X in 𝓝 (0 : 𝔸), l (NormedSpace.exp X) = X := by
  haveI : CompleteSpace 𝔸 := FiniteDimensional.complete ℝ 𝔸
  have hc : ContDiffAt ℝ ∞ (NormedSpace.exp : 𝔸 → 𝔸) 0 := (NormedSpace.exp_analytic (𝕂 := ℝ) 0).contDiffAt
  have hd : HasFDerivAt (NormedSpace.exp : 𝔸 → 𝔸)
      ((ContinuousLinearEquiv.refl ℝ 𝔸 : 𝔸 ≃L[ℝ] 𝔸) : 𝔸 →L[ℝ] 𝔸) 0 := hasFDerivAt_exp_zero
  have hn : (∞ : WithTop ℕ∞) ≠ 0 := by simp
  refine ⟨hc.localInverse hd hn, ?_, ?_, (hc.hasStrictFDerivAt' hd hn).eventually_left_inverse⟩
  · have := hc.to_localInverse hd hn
    rwa [NormedSpace.exp_zero] at this
  · have := (hc.hasStrictFDerivAt' hd hn).eventually_right_inverse
    rw [NormedSpace.exp_zero] at this
    exact this

theorem hasLog_of_isLieData (𝔸 L G : Type) [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [FiniteDimensional ℝ 𝔸]
    [NormedAddCommGroup L] [NormedSpace ℝ L] [Group G] (σ : 𝔸 →ₗ[ℝ] 𝔸) (j : L →ₗ[ℝ] 𝔸) (s : 𝔸 → G)
    (H : IsLieData σ j s) : HasLog σ j := by
  haveI : CompleteSpace 𝔸 := FiniteDimensional.complete ℝ 𝔸
  letI : NormedAlgebra ℚ 𝔸 := NormedAlgebra.restrictScalars ℚ ℝ 𝔸
  haveI : FiniteDimensional ℝ L := FiniteDimensional.of_injective j H.inj
  obtain ⟨l, h1, h2, h3⟩ := exists_local_log 𝔸
  obtain ⟨p, hp⟩ := j.exists_leftInverse_of_injective (LinearMap.ker_eq_bot.2 H.inj)
  have hp' : ∀ Y, p (j Y) = Y := fun Y => LinearMap.congr_fun hp Y
  have hl : l 1 = 0 := by simpa using h3.self_of_nhds
  refine ⟨fun h => p (l h), (LinearMap.toContinuousLinearMap p).contDiff.contDiffAt.comp 1 h1, ?_, ?_⟩
  · have ht : Filter.Tendsto (fun h => -σ (l h)) (𝓝 1) (𝓝 0) := by
      have := (σ.continuous_of_finiteDimensional.continuousAt.comp h1.continuousAt).neg.tendsto
      have e : (-(⇑σ ∘ l)) 1 = 0 := by simp [hl]
      rw [e] at this
      exact this
    filter_upwards [h2, ht.eventually h3] with h ha hb hu
    have e1 : NormedSpace.exp (σ (l h)) * h = 1 := by
      rw [← anti_map_exp σ H.anti H.one, ha, hu]
    have e2 : NormedSpace.exp (-σ (l h)) * NormedSpace.exp (σ (l h)) = 1 := by
      rw [← NormedSpace.exp_add_of_commute (Commute.refl _).neg_left, neg_add_cancel, NormedSpace.exp_zero]
    have e3 : NormedSpace.exp (-σ (l h)) = h := by
      rw [← mul_one (NormedSpace.exp (-σ (l h))), ← e1, ← mul_assoc, e2, one_mul]
    rw [e3] at hb
    obtain ⟨Y, hY⟩ := (H.skew (l h)).1 (neg_eq_iff_eq_neg.1 hb.symm)
    rw [← hY, hp', hY, ha]
  · have ht : Filter.Tendsto j (𝓝 0) (𝓝 0) := by
      simpa using j.continuous_of_finiteDimensional.tendsto 0
    filter_upwards [ht.eventually h3] with X hX
    rw [hX, hp']

end GlobalTheory.SmoothForms
end

-- bundled from Development.AbelianVarietyTheory.Proofs.HeightProofs.MemAdjoinGlActionOfCommuteTensorPerm
section
open GlobalTheory.SmoothForms NumberField Matrix
open scoped ContDiff Topology

noncomputable section

namespace GlobalTheory.SymmTensor

variable {n d : ℕ}

def tens (X : Fin d → Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin d → Fin n) (Fin d → Fin n) ℂ :=
  Matrix.of fun I K => ∏ p, X p (I p) (K p)

def sym (X : Fin d → Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin d → Fin n) (Fin d → Fin n) ℂ :=
  ∑ π : Equiv.Perm (Fin d), tens (X ∘ π)

theorem tens_mul (X Y : Fin d → Matrix (Fin n) (Fin n) ℂ) : tens X * tens Y = tens (X * Y) := by
  ext I K
  simp only [tens, Matrix.mul_apply, Matrix.of_apply, Pi.mul_apply, ← Finset.prod_mul_distrib]
  rw [Finset.prod_univ_sum, Fintype.piFinset_univ]

theorem tens_one : tens (1 : Fin d → Matrix (Fin n) (Fin n) ℂ) = 1 := by
  ext I K
  simp only [tens, Matrix.of_apply, Pi.one_apply, Matrix.one_apply]
  rw [Finset.prod_ite_zero]
  simp [funext_iff]

theorem tens_single_apply (p : Fin d) (Y : Matrix (Fin n) (Fin n) ℂ) (I K : Fin d → Fin n) :
    tens (Pi.mulSingle p Y) I K = if ∀ q, q ≠ p → I q = K q then Y (I p) (K p) else 0 := by
  simp only [tens, Matrix.of_apply]
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ p), Pi.mulSingle_eq_same]
  have : ∀ q ∈ Finset.univ.erase p, (Pi.mulSingle p Y : Fin d → Matrix (Fin n) (Fin n) ℂ) q (I q) (K q)
      = if I q = K q then 1 else 0 := fun q hq => by
    rw [Pi.mulSingle_eq_of_ne (Finset.ne_of_mem_erase hq), Matrix.one_apply]
  rw [Finset.prod_congr rfl this, Finset.prod_ite_zero]
  simp

theorem sum_tens_single (Y : Matrix (Fin n) (Fin n) ℂ) :
    ∑ p : Fin d, tens (Pi.mulSingle p Y) = ∑ a, ∑ b, Y a b • polar n d a b := by
  ext I K
  simp only [Matrix.sum_apply, tens_single_apply, polar, Matrix.smul_apply, Matrix.of_apply, smul_eq_mul,
    Finset.mul_sum]
  symm
  rw [Finset.sum_congr rfl fun a _ => Finset.sum_comm, Finset.sum_comm]
  refine Finset.sum_congr rfl fun p _ => ?_
  by_cases h : ∀ q, q ≠ p → I q = K q
  · simp [eq_true h, ite_and]
  · simp [eq_false h]

theorem sym_comp (X : Fin d → Matrix (Fin n) (Fin n) ℂ) (σ : Equiv.Perm (Fin d)) : sym (X ∘ σ) = sym X :=
  Fintype.sum_equiv (Equiv.mulLeft σ) _ _ fun _ => rfl

theorem sym_mul (X : Fin d → Matrix (Fin n) (Fin n) ℂ) (Y : Matrix (Fin n) (Fin n) ℂ) :
    sym X * ∑ p : Fin d, tens (Pi.mulSingle p Y) = ∑ i : Fin d, sym (X * Pi.mulSingle i Y) := by
  simp only [sym, Finset.sum_mul, Finset.mul_sum, tens_mul]
  rw [Finset.sum_comm]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun π _ => Fintype.sum_equiv π _ _ fun p => ?_
  congr 1
  funext q
  by_cases h : q = p
  · subst h; simp
  · have : π q ≠ π p := fun e => h (π.injective e)
    simp [h, this]

theorem sym_mem (X : Fin d → Matrix (Fin n) (Fin n) ℂ) :
    sym X ∈ Algebra.adjoin ℂ (Set.range fun p : Fin n × Fin n => polar n d p.1 p.2) := by
  set A := Algebra.adjoin ℂ (Set.range fun p : Fin n × Fin n => polar n d p.1 p.2)
  suffices H : ∀ s : Finset (Fin d), ∀ X : Fin d → Matrix (Fin n) (Fin n) ℂ, (∀ i ∉ s, X i = 1) → sym X ∈ A from
    H Finset.univ X (by simp)
  intro s
  induction s using Finset.induction_on with
  | empty =>
    intro X hX
    obtain rfl : X = 1 := funext fun i => hX i (by simp)
    refine A.sum_mem fun π _ => ?_
    rw [show (1 : Fin d → Matrix (Fin n) (Fin n) ℂ) ∘ π = 1 from rfl, tens_one]
    exact A.one_mem
  | insert j s hj ih =>
    intro X hX
    set Z := Function.update X j 1 with hZ
    have hZ1 : ∀ i ∉ s, Z i = 1 := fun i hi => by
      by_cases h : i = j
      · subst h; simp [hZ]
      · rw [hZ, Function.update_of_ne h]; exact hX i (by simp [h, hi])
    have hP : ∑ p : Fin d, tens (Pi.mulSingle p (X j)) ∈ A := by
      rw [sum_tens_single]
      exact A.sum_mem fun a _ => A.sum_mem fun b _ => A.smul_mem (Algebra.subset_adjoin ⟨(a, b), rfl⟩) _
    have h1 := A.mul_mem (ih Z hZ1) hP
    rw [sym_mul, ← Finset.sum_add_sum_compl s] at h1
    have h2 : ∑ i ∈ s, sym (Z * Pi.mulSingle i (X j)) ∈ A := A.sum_mem fun i hi => ih _ fun k hk => by
      have : k ≠ i := fun e => hk (e ▸ hi)
      simp [hZ1 k hk, this]
    have h3 := A.sub_mem h1 h2
    have h4 : ∀ i ∈ sᶜ, sym (Z * Pi.mulSingle i (X j)) = sym X := fun i hi => by
      have hi : i ∉ s := by simpa using hi
      rw [← sym_comp X (Equiv.swap i j)]
      congr 1
      funext k
      by_cases hki : k = i
      · subst hki; simp [hZ1 k hi]
      · by_cases hkj : k = j
        · subst hkj
          simp [hZ, hki, hX i (by simp [hi, Ne.symm hki])]
        · simp [hZ, hki, hkj, Equiv.swap_apply_of_ne_of_ne hki hkj]
    rw [add_sub_cancel_left, Finset.sum_congr rfl h4, Finset.sum_const, ← Nat.cast_smul_eq_nsmul ℂ] at h3
    have h5 : ((sᶜ.card : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (Finset.card_ne_zero.2 ⟨j, by simpa using hj⟩)
    have := A.smul_mem h3 ((sᶜ.card : ℕ) : ℂ)⁻¹
    rwa [smul_smul, inv_mul_cancel₀ h5, one_smul] at this

theorem tens_unit_apply (I K I' K' : Fin d → Fin n) (π : Equiv.Perm (Fin d)) :
    tens ((fun p => Matrix.single (I p) (K p) (1 : ℂ)) ∘ π) I' K' =
      if I = I' ∘ π.symm then if K = K' ∘ π.symm then 1 else 0 else 0 := by
  simp only [tens, Matrix.of_apply, Function.comp_apply, Matrix.single_apply]
  rw [Finset.prod_ite_zero, ← ite_and]
  simp only [Finset.mem_univ, forall_const, Finset.prod_const_one, forall_and, funext_iff, Function.comp_apply]
  refine if_congr (and_congr ?_ ?_) rfl rfl <;>
  exact ⟨fun h q => by simpa using h (π.symm q), fun h q => by simpa using h (π q)⟩

theorem mem_adjoin_polar (n d : ℕ) (T : Matrix (Fin d → Fin n) (Fin d → Fin n) ℂ)
    (hT : ∀ π, T * permMat n d π = permMat n d π * T) :
    T ∈ Algebra.adjoin ℂ (Set.range fun p : Fin n × Fin n => polar n d p.1 p.2) := by
  set A := Algebra.adjoin ℂ (Set.range fun p : Fin n × Fin n => polar n d p.1 p.2)
  have h1 : ∀ (π : Equiv.Perm (Fin d)) I K, T (I ∘ π) (K ∘ π) = T I K := fun π I K => by
    have := congrFun (congrFun (hT π) (I ∘ π)) K
    simp only [Matrix.mul_apply, permMat, Matrix.of_apply, mul_ite, ite_mul, mul_one, mul_zero, one_mul, zero_mul,
      π.surjective.injective_comp_right.eq_iff] at this
    simpa using this
  have h2 : ∑ I, ∑ K, T I K • sym (fun p => Matrix.single (I p) (K p) (1 : ℂ)) = ((d.factorial : ℕ) : ℂ) • T := by
    ext I' K'
    simp only [sym, Matrix.sum_apply, Matrix.smul_apply, tens_unit_apply, smul_eq_mul, Finset.mul_sum]
    rw [Finset.sum_congr rfl fun a _ => Finset.sum_comm, Finset.sum_comm]
    simp [h1, Fintype.card_perm]
  have h3 : ((d.factorial : ℕ) : ℂ) • T ∈ A :=
    h2 ▸ A.sum_mem fun I _ => A.sum_mem fun K _ => A.smul_mem (sym_mem _) _
  have h5 : ((d.factorial : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.2 d.factorial_ne_zero
  have := A.smul_mem h3 ((d.factorial : ℕ) : ℂ)⁻¹
  rwa [smul_smul, inv_mul_cancel₀ h5, one_smul] at this

end GlobalTheory.SymmTensor

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.HeightProofs.QuadraticExtNormFormOverAlgebra
section
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open scoped TensorProduct

namespace GlobalTheory.QuadNormBase

theorem norm_of_basis {R A : Type} [CommRing R] [CommRing A] [Algebra R A]
    (B : Module.Basis (Fin 2) R A) (d : R) (h0 : B 0 = 1) (h1 : B 1 * B 1 = d • B 0) (x y : R) :
    Algebra.norm R (x • B 0 + y • B 1) = x ^ 2 - d * y ^ 2 := by
  have e0 : (x • B 0 + y • B 1) * B 0 = x • B 0 + y • B 1 := by rw [h0, mul_one]
  have e1 : (x • B 0 + y • B 1) * B 1 = (y * d) • B 0 + x • B 1 := by
    rw [add_mul, smul_mul_assoc, smul_mul_assoc, h1, smul_smul, add_comm]
    congr 1
    rw [h0, one_mul]
  rw [Algebra.norm_eq_matrix_det B, Matrix.det_fin_two]
  simp only [Algebra.leftMulMatrix_eq_repr_mul, e0, e1]
  simp
  ring

theorem exists_basis (F E : Type) [Field F] [CharZero F] [Field E] [Algebra F E] (σ : E →ₐ[F] E)
    (hr : Module.finrank F E = 2) (hσ : ∀ x, σ (σ x) = x) (hne : ∃ x, σ x ≠ x) :
    ∃ (δ : F) (b : Module.Basis (Fin 2) F E), ¬ IsSquare δ ∧ b 0 = 1 ∧ σ (b 1) = - b 1 ∧
      b 1 * b 1 = algebraMap F E δ := by
  haveI : CharZero E := charZero_of_injective_algebraMap (algebraMap F E).injective
  obtain ⟨x0, hx0⟩ := hne
  have hsm : ∀ (c : F) (e : E), σ (c • e) = c • σ e := fun c e => by
    rw [Algebra.smul_def, Algebra.smul_def, map_mul, AlgHom.commutes]
  set θ : E := x0 - σ x0 with hθ
  have hθ0 : θ ≠ 0 := sub_ne_zero.2 hx0.symm
  have hσθ : σ θ = -θ := by rw [hθ, map_sub, hσ]; ring
  have hli : LinearIndependent F ![(1 : E), θ] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    have h2 := congrArg σ hst
    rw [map_add, hsm, hsm, map_one, hσθ, map_zero, smul_neg] at h2
    have h3 : (2 : E) * (t • θ) = 0 := by linear_combination hst - h2
    have h4 : t • θ = 0 := by simpa only [mul_eq_zero, two_ne_zero, false_or] using h3
    have ht : t = 0 := (smul_eq_zero.1 h4).resolve_right hθ0
    subst ht
    exact ⟨by simpa using hst, rfl⟩
  let b : Module.Basis (Fin 2) F E :=
    basisOfLinearIndependentOfCardEqFinrank hli (by simp [hr])
  have hb0 : b 0 = 1 := by simp [b]
  have hb1 : b 1 = θ := by simp [b]
  have hrep := b.sum_repr (θ * θ)
  rw [Fin.sum_univ_two, hb0, hb1] at hrep
  set s := b.repr (θ * θ) 0
  set t := b.repr (θ * θ) 1
  have h2 := congrArg σ hrep
  rw [map_add, hsm, hsm, map_one, map_mul, hσθ, smul_neg] at h2
  have h3 : (2 : E) * (t • θ) = 0 := by linear_combination hrep - h2
  have h4 : t • θ = 0 := by simpa only [mul_eq_zero, two_ne_zero, false_or] using h3
  have hsq : θ * θ = algebraMap F E s := by
    rw [← hrep, h4, add_zero, Algebra.algebraMap_eq_smul_one]
  refine ⟨s, b, ?_, hb0, by rw [hb1, hσθ], by rw [hb1, hsq]⟩
  rintro ⟨r, hr⟩
  rw [hr, map_mul, mul_self_eq_mul_self_iff] at hsq
  have hfix : σ θ = θ := by
    rcases hsq with h | h
    · rw [h, AlgHom.commutes]
    · rw [h, map_neg, AlgHom.commutes]
  have h5 : (2 : E) * θ = 0 := by linear_combination hσθ - hfix
  exact hθ0 (by simpa only [mul_eq_zero, two_ne_zero, false_or] using h5)

theorem norm_form : ∀ (F E : Type) [Field F] [CharZero F] [Field E] [Algebra F E] (σ : E →ₐ[F] E), Module.finrank F E = 2 → (∀ x, σ (σ x) = x) → (∃ x, σ x ≠ x) → ∃ δ : F, ¬ IsSquare δ ∧ ∀ (R : Type) [CommRing R] [Algebra F R], (∀ z : R ⊗[F] E, ∃ x y : R, Algebra.norm R z = x ^ 2 - algebraMap F R δ * y ^ 2 ∧ z * sigR R σ z = algebraMap R (R ⊗[F] E) (x ^ 2 - algebraMap F R δ * y ^ 2)) ∧ ∀ x y : R, ∃ z : R ⊗[F] E, z * sigR R σ z = algebraMap R (R ⊗[F] E) (x ^ 2 - algebraMap F R δ * y ^ 2) := by
  intro F E _ _ _ _ σ hr hσ hne
  obtain ⟨δ, b, hδ, hb0, hb1, hsq⟩ := exists_basis F E σ hr hσ hne
  refine ⟨δ, hδ, ?_⟩
  intro R _ _
  let B := Algebra.TensorProduct.basis R b
  have hB : ∀ i, B i = 1 ⊗ₜ[F] b i := fun i => Algebra.TensorProduct.basis_apply b i
  have h0 : B 0 = 1 := by rw [hB, hb0]; rfl
  have h1 : B 1 * B 1 = algebraMap F R δ • B 0 := by
    rw [hB, hB, Algebra.TensorProduct.tmul_mul_tmul, hsq, hb0, Algebra.algebraMap_eq_smul_one (A := E),
      TensorProduct.tmul_smul, one_mul, algebraMap_smul]
  have hs : ∀ (r : R) (e : E), sigR R σ (r ⊗ₜ[F] e) = r ⊗ₜ[F] σ e := fun r e => rfl
  have key : ∀ x y : R, (x • B 0 + y • B 1) * sigR R σ (x • B 0 + y • B 1) =
      algebraMap R (R ⊗[F] E) (x ^ 2 - algebraMap F R δ * y ^ 2) := by
    intro x y
    have e : sigR R σ (x • B 0 + y • B 1) = x • B 0 - y • B 1 := by
      rw [map_add, hB, hB, TensorProduct.smul_tmul', TensorProduct.smul_tmul', hs, hs, hb1, hb0,
        map_one, TensorProduct.tmul_neg, sub_eq_add_neg]
    rw [e]
    rw [h0] at h1 ⊢
    generalize algebraMap F R δ = d at h1 ⊢
    simp only [Algebra.smul_def, mul_one, map_sub, map_mul, map_pow] at h1 ⊢
    linear_combination (-(algebraMap R (R ⊗[F] E) y) ^ 2) * h1
  refine ⟨fun z => ?_, fun x y => ⟨_, key x y⟩⟩
  have hz := B.sum_repr z
  rw [Fin.sum_univ_two] at hz
  refine ⟨B.repr z 0, B.repr z 1, ?_, ?_⟩
  · rw [← norm_of_basis B _ h0 h1, hz]
  · rw [← key, hz]

end GlobalTheory.QuadNormBase
end

