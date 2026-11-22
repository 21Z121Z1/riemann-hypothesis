import Mathlib

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SummableProdPowMultiIndex
section
namespace GlobalTheory.CompanionTheory.Summability

theorem summable_prod_pow_multiIndex : ∀ (r : ℕ) (x : Fin r → ℝ), (∀ i, 0 ≤ x i) → (∀ i, x i < 1) →
    Summable (fun j : Fin r → ℕ => ∏ i, x i ^ j i) := by
  intro r
  induction r with
  | zero =>
    intro x _ _
    exact (hasSum_fintype _).summable
  | succ r ih =>
    intro x h0 h1
    let e : ℕ × (Fin r → ℕ) ≃ (Fin (r + 1) → ℕ) :=
      { toFun := fun p => Fin.cons p.1 p.2
        invFun := fun j => (j 0, Fin.tail j)
        left_inv := fun p => by simp
        right_inv := fun j => by simp }
    rw [← e.summable_iff]
    have hA : Summable (fun n : ℕ => x 0 ^ n) := summable_geometric_of_lt_one (h0 0) (h1 0)
    have hB : Summable (fun j : Fin r → ℕ => ∏ i, x i.succ ^ j i) :=
      ih (fun i => x i.succ) (fun i => h0 _) (fun i => h1 _)
    have hM := hA.mul_of_nonneg hB (fun n => pow_nonneg (h0 0) n)
      (fun j => Finset.prod_nonneg (fun i _ => pow_nonneg (h0 _) _))
    refine hM.congr ?_
    rintro ⟨n, j⟩
    simp [e, Fin.prod_univ_succ]

end GlobalTheory.CompanionTheory.Summability
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SummableTwistedSquareCoefficients
section
namespace GlobalTheory.CompanionTheory.LSeriesBound

theorem lseriesSummable_twist_squares (M N k : ℕ) [NeZero M] (hM : N ∣ M)
    (χ : DirichletCharacter ℂ N) (a : ℕ → ℂ) (hk : 1 ≤ k)
    (hb : ∀ n : ℕ, Nat.Coprime n N → ‖a (n ^ 2)‖ ≤ 2 * (n : ℝ) * (n : ℝ) ^ (k - 1))
    (s : ℂ) (hs : 2 < s.re) :
    LSeriesSummable (fun n : ℕ => DirichletCharacter.changeLevel hM χ⁻¹ (n : ZMod M) * a (n ^ 2))
      (s + k - 1) := by
  have hre : (s + (k : ℂ) - 1).re = s.re + (k : ℝ) - 1 := by simp
  have hsum : Summable (fun n : ℕ => 2 * (n : ℝ) ^ (1 - s.re)) :=
    (Real.summable_nat_rpow.mpr (by linarith)).mul_left 2
  refine Summable.of_norm_bounded hsum (fun n => ?_)
  rw [LSeries.norm_term_eq]
  split_ifs with hn
  · positivity
  have hn0 : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
  have hf : ‖DirichletCharacter.changeLevel hM χ⁻¹ (n : ZMod M) * a (n ^ 2)‖
      ≤ 2 * (n : ℝ) ^ k := by
    by_cases hu : IsUnit (n : ZMod M)
    · have hcop : Nat.Coprime n M := (ZMod.isUnit_iff_coprime n M).mp hu
      have hcopN : Nat.Coprime n N := Nat.Coprime.coprime_dvd_right hM hcop
      have h1 : ‖DirichletCharacter.changeLevel hM χ⁻¹ (n : ZMod M)‖ ≤ 1 :=
        DirichletCharacter.norm_le_one _ _
      have h2 := hb n hcopN
      have h3 : 2 * (n : ℝ) * (n : ℝ) ^ (k - 1) = 2 * (n : ℝ) ^ k := by
        obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
        simp only [Nat.add_sub_cancel, pow_succ]
        ring
      rw [norm_mul]
      calc _ ≤ 1 * ‖a (n ^ 2)‖ := by gcongr
        _ ≤ 2 * (n : ℝ) ^ k := by rw [one_mul, ← h3]; exact h2
    · rw [MulChar.map_nonunit _ hu]
      simp only [zero_mul, norm_zero]
      positivity
  rw [hre, div_le_iff₀ (Real.rpow_pos_of_pos hn0 _)]
  have hpow : (n : ℝ) ^ (1 - s.re) * (n : ℝ) ^ (s.re + (k : ℝ) - 1) = (n : ℝ) ^ k := by
    rw [← Real.rpow_add hn0, ← Real.rpow_natCast]
    congr 1
    ring
  calc _ ≤ 2 * (n : ℝ) ^ k := hf
    _ = _ := by rw [← hpow]; ring

end GlobalTheory.CompanionTheory.LSeriesBound
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TZero
section
noncomputable section

open Finset

namespace GlobalTheory.CompanionTheory.CoefId

variable {n : ℕ}

def mon (e : Fin n → ℤ) (z : Fin n → ℂ) : ℂ := ∏ a, z a ^ e a

def dl (n : ℕ) : Fin n → ℤ := fun j => ((n - 1 - (j : ℕ) : ℕ) : ℤ)

def prs (n : ℕ) : Finset (Fin n × Fin n) := univ.filter fun p => p.1 < p.2

def score (T : Finset (Fin n × Fin n)) : Fin n → ℤ := fun c =>
  ((T.filter fun p => p.1 = c).card : ℤ) + (((prs n \ T).filter fun p => p.2 = c).card : ℤ)

def tZero (lev : Fin n → ℕ) : Finset (Fin n × Fin n) := (prs n).filter fun p => lev p.1 < lev p.2

end GlobalTheory.CompanionTheory.CoefId
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TendstoOfAsymptoticBounds
section
open Filter Topology

namespace GlobalTheory.CompanionTheory.Analysis

theorem tendsto_factorial_mul_div_pow_of_eps_bounds (f : ℕ → ℝ) (G : ℝ) (D : ℕ)
    (hl : ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop, (G - ε) * (n : ℝ) ^ D / (D.factorial : ℝ) ≤ f n)
    (hu : ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop, f n ≤ (G + ε) * (n : ℝ) ^ D / (D.factorial : ℝ)) :
    Tendsto (fun n : ℕ => (D.factorial : ℝ) * f n / (n : ℝ) ^ D) atTop (𝓝 G) := by
  have hfac : (0 : ℝ) < (D.factorial : ℝ) := by exact_mod_cast D.factorial_pos
  have hev : ∀ᶠ n : ℕ in atTop, (0 : ℝ) < (n : ℝ) ^ D := by
    filter_upwards [eventually_ge_atTop 1] with n hn
    have : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    positivity
  rw [tendsto_order]
  refine ⟨fun a ha => ?_, fun b hb => ?_⟩
  · filter_upwards [hl ((G - a) / 2) (by linarith), hev] with n hn hp
    rw [div_le_iff₀ hfac] at hn
    have key : G - (G - a) / 2 ≤ (D.factorial : ℝ) * f n / (n : ℝ) ^ D := by
      rw [le_div_iff₀ hp]
      linarith
    linarith
  · filter_upwards [hu ((b - G) / 2) (by linarith), hev] with n hn hp
    rw [le_div_iff₀ hfac] at hn
    have key : (D.factorial : ℝ) * f n / (n : ℝ) ^ D ≤ G + (b - G) / 2 := by
      rw [div_le_iff₀ hp]
      linarith
    linarith

end GlobalTheory.CompanionTheory.Analysis
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TensorEquivBaseChangeTensor
section
open TensorProduct

namespace GlobalTheory.CompanionTheory.TensorPushout

theorem tensor_equiv_baseChange_tensor :
    ∀ (K A B R X Y : Type) [CommRing K] [CommRing A] [CommRing B] [CommRing R] [Algebra K A]
      [Algebra K B] [Algebra K R] [Algebra A R] [Algebra B R] [IsScalarTower K A R]
      [IsScalarTower K B R] [Algebra.IsPushout K A B R] [AddCommGroup X] [Module K X] [Module A X]
      [IsScalarTower K A X] [AddCommGroup Y] [Module K Y] [Module B Y] [IsScalarTower K B Y],
      ∃ t : X ⊗[K] Y ≃ₗ[K] (R ⊗[A] X) ⊗[R] (R ⊗[B] Y),
        ∀ x y, t (x ⊗ₜ y) = ((1 : R) ⊗ₜ[A] x) ⊗ₜ[R] ((1 : R) ⊗ₜ[B] y) := by
  intro K A B R X Y
  intros
  refine ⟨((TensorProduct.AlgebraTensorModule.cancelBaseChange K A A X Y).symm.restrictScalars K).trans <|
    (((Algebra.IsPushout.cancelBaseChange K A B R Y).symm.lTensor X).restrictScalars K).trans <|
    ((TensorProduct.comm A X (R ⊗[B] Y)).restrictScalars K).trans <|
    ((TensorProduct.AlgebraTensorModule.cancelBaseChange A R R (R ⊗[B] Y) X).symm.restrictScalars K).trans <|
    ((TensorProduct.comm R (R ⊗[B] Y) (R ⊗[A] X)).restrictScalars K), fun x y => ?_⟩
  simp only [LinearEquiv.trans_apply, LinearEquiv.restrictScalars_apply,
    TensorProduct.AlgebraTensorModule.cancelBaseChange_symm_tmul, LinearEquiv.lTensor_tmul,
    Algebra.IsPushout.cancelBaseChange_symm_tmul, map_one, TensorProduct.comm_tmul]

end GlobalTheory.CompanionTheory.TensorPushout
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TensorPrimeLocalizationCriterion
section
open TensorProduct

namespace GlobalTheory.CompanionTheory.KrullLocal

theorem exists_ringHom_of_fractions {B C D : Type} [CommRing B] [CommRing C] [CommRing D]
    [Algebra B C] (q : Ideal C) [hq : q.IsPrime] (φ : B →+* D)
    (hu : ∀ t : B, algebraMap B C t ∉ q → IsUnit (φ t))
    (h1 : ∀ c : C, ∃ b t : B, algebraMap B C t ∉ q ∧ ∃ v : C, v ∉ q ∧
      v * (algebraMap B C t * c) = v * algebraMap B C b)
    (h2 : ∀ b : B, (∃ v : C, v ∉ q ∧ v * algebraMap B C b = 0) → φ b = 0) :
    ∃ g : C →+* D, (∀ b, g (algebraMap B C b) = φ b) ∧ ∀ v, v ∉ q → IsUnit (g v) := by
  classical
  choose bb tt ht vv hv hvt using h1
  have hmul : ∀ {x y : C}, x ∉ q → y ∉ q → x * y ∉ q := fun hx hy hm =>
    (hq.mem_or_mem hm).elim hx hy
  have hone : (1 : C) ∉ q := fun h => hq.ne_top ((Ideal.eq_top_iff_one q).2 h)
  have hone' : algebraMap B C 1 ∉ q := by simpa using hone
  let f : C → D := fun c => φ (bb c) * Ring.inverse (φ (tt c))
  have hft : ∀ c, f c * φ (tt c) = φ (bb c) := by
    intro c
    simp only [f]
    rw [mul_assoc, Ring.inverse_mul_cancel _ (hu _ (ht c)), mul_one]
  have key : ∀ (c : C) (b t : B) (v : C), algebraMap B C t ∉ q → v ∉ q →
      v * (algebraMap B C t * c) = v * algebraMap B C b → f c * φ t = φ b := by
    intro c b t v htq hvq h
    have hz : φ (tt c * b - t * bb c) = 0 := by
      apply h2
      refine ⟨vv c * v, hmul (hv c) hvq, ?_⟩
      have h' := hvt c
      simp only [map_sub, map_mul]
      linear_combination (-(vv c * algebraMap B C (tt c))) * h + (v * algebraMap B C t) * h'
    have hz' : φ (tt c) * φ b = φ (tt c) * (f c * φ t) := by
      have e : φ (tt c) * φ b - φ t * φ (bb c) = 0 := by simpa using hz
      rw [← hft c] at e
      linear_combination e
    exact ((hu _ (ht c)).mul_left_cancel hz').symm
  have hhom1 : f 1 = 1 := by
    have := key 1 1 1 1 hone' hone (by simp)
    simpa using this
  have hhom0 : f 0 = 0 := by
    have := key 0 0 1 1 hone' hone (by simp)
    simpa using this
  have hhommul : ∀ c c', f (c * c') = f c * f c' := by
    intro c c'
    have e := key (c * c') (bb c * bb c') (tt c * tt c') (vv c * vv c')
      (by rw [map_mul]; exact hmul (ht c) (ht c')) (hmul (hv c) (hv c'))
      (by
        have h := hvt c
        have h' := hvt c'
        simp only [map_mul]
        linear_combination (vv c' * algebraMap B C (tt c') * c') * h +
          (vv c * algebraMap B C (bb c)) * h')
    have hU : IsUnit (φ (tt c * tt c')) := by
      rw [map_mul]; exact (hu _ (ht c)).mul (hu _ (ht c'))
    apply hU.mul_right_cancel
    rw [e, map_mul, map_mul, ← hft c, ← hft c']
    ring
  have hhomadd : ∀ c c', f (c + c') = f c + f c' := by
    intro c c'
    have e := key (c + c') (tt c' * bb c + tt c * bb c') (tt c * tt c') (vv c * vv c')
      (by rw [map_mul]; exact hmul (ht c) (ht c')) (hmul (hv c) (hv c'))
      (by
        have h := hvt c
        have h' := hvt c'
        simp only [map_mul, map_add]
        linear_combination (vv c' * algebraMap B C (tt c')) * h +
          (vv c * algebraMap B C (tt c)) * h')
    have hU : IsUnit (φ (tt c * tt c')) := by
      rw [map_mul]; exact (hu _ (ht c)).mul (hu _ (ht c'))
    apply hU.mul_right_cancel
    rw [e, map_add, map_mul, map_mul, map_mul, ← hft c, ← hft c']
    ring
  refine ⟨{ toFun := f, map_one' := hhom1, map_mul' := hhommul, map_zero' := hhom0,
            map_add' := hhomadd }, ?_, ?_⟩
  · intro b
    have := key (algebraMap B C b) b 1 1 hone' hone (by simp [mul_comm])
    simpa using this
  · intro v hvq
    have hb : algebraMap B C (bb v) ∉ q := by
      intro hm
      have h := hvt v
      have : vv v * (algebraMap B C (tt v) * v) ∈ q := by
        rw [h]; exact q.mul_mem_left _ hm
      exact hmul (hv v) (hmul (ht v) hvq) this
    have hU := hu _ hb
    rw [← hft v] at hU
    exact isUnit_of_mul_isUnit_left hU

theorem exists_mul_eq_tmul {B R C : Type} [CommRing B] [CommRing R] [CommRing C] [Algebra B R]
    [Algebra B C] (q : Ideal C) [hq : q.IsPrime]
    (h1 : ∀ c : C, ∃ b t : B, algebraMap B C t ∉ q ∧ ∃ v : C, v ∉ q ∧
      v * (algebraMap B C t * c) = v * algebraMap B C b)
    (w : R ⊗[B] C) :
    ∃ (s : B) (v : C) (r : R), algebraMap B C s ∉ q ∧ v ∉ q ∧
      ((1 : R) ⊗ₜ[B] (v * algebraMap B C s)) * w = r ⊗ₜ[B] v := by
  have hmul : ∀ {x y : C}, x ∉ q → y ∉ q → x * y ∉ q := fun hx hy hm =>
    (hq.mem_or_mem hm).elim hx hy
  have hone : (1 : C) ∉ q := fun h => hq.ne_top ((Ideal.eq_top_iff_one q).2 h)
  induction w using TensorProduct.induction_on with
  | zero => exact ⟨1, 1, 0, by simpa using hone, hone, by simp⟩
  | tmul r0 c =>
    obtain ⟨b, t, ht, v, hv, h⟩ := h1 c
    refine ⟨t, v, b • r0, ht, hv, ?_⟩
    rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_assoc, h, TensorProduct.smul_tmul,
      Algebra.smul_def, mul_comm]
  | add x y hx hy =>
    obtain ⟨s, v, r, hs, hv, e⟩ := hx
    obtain ⟨s', v', r', hs', hv', e'⟩ := hy
    refine ⟨s * s', v * v', s' • r + s • r', by rw [map_mul]; exact hmul hs hs', hmul hv hv', ?_⟩
    have a1 : ((1 : R) ⊗ₜ[B] (v * v' * algebraMap B C (s * s'))) =
        ((1 : R) ⊗ₜ[B] (v' * algebraMap B C s')) * ((1 : R) ⊗ₜ[B] (v * algebraMap B C s)) := by
      rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, map_mul]
      congr 1
      ring
    have a2 : ((1 : R) ⊗ₜ[B] (v * v' * algebraMap B C (s * s'))) =
        ((1 : R) ⊗ₜ[B] (v * algebraMap B C s)) * ((1 : R) ⊗ₜ[B] (v' * algebraMap B C s')) := by
      rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, map_mul]
      congr 1
      ring
    rw [mul_add]
    nth_rewrite 1 [a1]
    rw [a2, mul_assoc, mul_assoc, e, e', Algebra.TensorProduct.tmul_mul_tmul,
      Algebra.TensorProduct.tmul_mul_tmul, one_mul, one_mul, TensorProduct.add_tmul,
      TensorProduct.smul_tmul, TensorProduct.smul_tmul, Algebra.smul_def, Algebra.smul_def]
    congr 2 <;> ring

theorem map_eq_zero_of_smul_tmul {B R C M D N : Type} [CommRing B] [CommRing R] [CommRing C]
    [Algebra B R] [Algebra B C] [AddCommGroup M] [Module R M] [CommRing D] [Algebra R D]
    [AddCommGroup N] [Module R N] [Module D N] [IsScalarTower R D N]
    (J : Ideal B) (hJ : ∀ a ∈ J, algebraMap R D (algebraMap B R a) = 0)
    (Q₀ : Ideal (R ⊗[B] C)) (hQ : Q₀.IsPrime)
    (hunit : ∀ r : R, r ∉ Q₀.comap (Algebra.TensorProduct.includeLeftRingHom : R →+* R ⊗[B] C) →
      IsUnit (algebraMap R D r))
    (h1 : ∀ c : C, ∃ b t : B,
      t ∉ (Q₀.comap (Algebra.TensorProduct.includeRight : C →ₐ[B] R ⊗[B] C)).comap (algebraMap B C) ∧
      ∃ v : C, v ∉ Q₀.comap (Algebra.TensorProduct.includeRight : C →ₐ[B] R ⊗[B] C) ∧
        v * (algebraMap B C t * c) = v * algebraMap B C b)
    (h2 : ∀ b : B, (∃ v : C, v ∉ Q₀.comap (Algebra.TensorProduct.includeRight : C →ₐ[B] R ⊗[B] C) ∧
        v * algebraMap B C b = 0) → ∃ t : B,
      t ∉ (Q₀.comap (Algebra.TensorProduct.includeRight : C →ₐ[B] R ⊗[B] C)).comap (algebraMap B C) ∧
      t * b ∈ J)
    (ι : M →ₗ[R] N) (y : M) (w : R ⊗[B] C) (hw0 : w ∉ Q₀)
    (hw : w • ((1 : R ⊗[B] C) ⊗ₜ[R] y) = 0) : ι y = 0 := by
  set q : Ideal C := Q₀.comap (Algebra.TensorProduct.includeRight : C →ₐ[B] R ⊗[B] C) with hqdef
  haveI hq : q.IsPrime := Ideal.comap_isPrime _ _
  have hLR : ∀ t : B, (algebraMap B R t) ⊗ₜ[B] (1 : C) = (1 : R) ⊗ₜ[B] algebraMap B C t := by
    intro t
    rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]
  have hmemq : ∀ c : C, c ∈ q ↔ (1 : R) ⊗ₜ[B] c ∈ Q₀ := fun c => Iff.rfl
  have hmemp : ∀ r : R, r ∈ Q₀.comap (Algebra.TensorProduct.includeLeftRingHom : R →+* R ⊗[B] C) ↔
      r ⊗ₜ[B] (1 : C) ∈ Q₀ := fun r => Iff.rfl
  let φ₀ : B →+* D := (algebraMap R D).comp (algebraMap B R)
  have hu : ∀ t : B, algebraMap B C t ∉ q → IsUnit (φ₀ t) := by
    intro t ht
    apply hunit
    rw [hmemp, hLR]
    exact fun h => ht ((hmemq _).2 h)
  have h1' : ∀ c : C, ∃ b t : B, algebraMap B C t ∉ q ∧ ∃ v : C, v ∉ q ∧
      v * (algebraMap B C t * c) = v * algebraMap B C b := h1
  obtain ⟨g, hg, hgu⟩ := exists_ringHom_of_fractions q φ₀ hu h1' (by
    intro b hb
    obtain ⟨t, ht, htb⟩ := h2 b hb
    have e : φ₀ (t * b) = 0 := hJ _ htb
    rw [map_mul] at e
    exact (hu t ht).mul_right_eq_zero.1 e)
  letI : Algebra B D := φ₀.toAlgebra
  haveI : IsScalarTower B R D := .of_algebraMap_eq (fun _ => rfl)
  let gA : C →ₐ[B] D := { g with commutes' := hg }
  let fA : R →ₐ[B] D := IsScalarTower.toAlgHom B R D
  let φ : R ⊗[B] C →ₐ[B] D := Algebra.TensorProduct.productMap fA gA
  have hφ : ∀ (r : R) (c : C), φ (r ⊗ₜ[B] c) = algebraMap R D r * g c := by
    intro r c
    simp [φ, fA, gA]
  have hφr : ∀ (r : R) (τ : R ⊗[B] C), φ (r • τ) = algebraMap R D r * φ τ := by
    intro r τ
    rw [Algebra.smul_def, map_mul, Algebra.TensorProduct.algebraMap_apply, hφ]
    simp
  let Ψ : (R ⊗[B] C) ⊗[R] M →ₗ[R] N := TensorProduct.lift (LinearMap.mk₂ R
    (fun (τ : R ⊗[B] C) (m : M) => φ τ • ι m)
    (fun a b m => by simp [add_smul])
    (fun r a m => by rw [hφr, mul_smul, algebraMap_smul])
    (fun a m n => by simp)
    (fun r a m => by rw [map_smul, smul_comm]))
  have hΨ : φ w • ι y = 0 := by
    have e := congrArg Ψ hw
    rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one, map_zero] at e
    simpa [Ψ] using e
  obtain ⟨s, v, r, hs, hv, e⟩ := exists_mul_eq_tmul (R := R) q h1' w
  have hr : r ∉ Q₀.comap (Algebra.TensorProduct.includeLeftRingHom : R →+* R ⊗[B] C) := by
    intro hm
    rw [hmemp] at hm
    have h3 : (r ⊗ₜ[B] v) ∈ Q₀ := by
      have := Q₀.mul_mem_right ((1 : R) ⊗ₜ[B] v) hm
      simpa [Algebra.TensorProduct.tmul_mul_tmul] using this
    rw [← e] at h3
    rcases hQ.mem_or_mem h3 with h4 | h4
    · have : v * algebraMap B C s ∈ q := (hmemq _).2 h4
      exact (hq.mem_or_mem this).elim hv hs
    · exact hw0 h4
  have hunitw : IsUnit (φ w) := by
    have e2 := congrArg φ e
    rw [map_mul, hφ, hφ] at e2
    have hU : IsUnit (algebraMap R D r * g v) := (hunit r hr).mul (hgu v hv)
    rw [← e2] at hU
    exact isUnit_of_mul_isUnit_right hU
  obtain ⟨u, hu'⟩ := hunitw
  have : ι y = (↑u⁻¹ : D) • (φ w • ι y) := by
    rw [← hu', smul_smul, Units.inv_mul, one_smul]
  rw [this, hΨ, smul_zero]

theorem smul_eq_zero_of_smul_one_tmul_eq_zero : ∀ {B R C M : Type} [CommRing B] [CommRing R] [CommRing C] [Algebra B R] [Algebra B C] [AddCommGroup M] [Module R M] [Module B M] [IsScalarTower B R M] (J : Ideal B), (∀ a ∈ J, ∀ m : M, a • m = 0) → ∀ Q₀ : Ideal (R ⊗[B] C), Q₀.IsPrime → (∀ c : C, ∃ b t : B, t ∉ (Q₀.comap (Algebra.TensorProduct.includeRight : C →ₐ[B] R ⊗[B] C)).comap (algebraMap B C) ∧ ∃ v : C, v ∉ Q₀.comap (Algebra.TensorProduct.includeRight : C →ₐ[B] R ⊗[B] C) ∧ v * (algebraMap B C t * c) = v * algebraMap B C b) → (∀ b : B, (∃ v : C, v ∉ Q₀.comap (Algebra.TensorProduct.includeRight : C →ₐ[B] R ⊗[B] C) ∧ v * algebraMap B C b = 0) → ∃ t : B, t ∉ (Q₀.comap (Algebra.TensorProduct.includeRight : C →ₐ[B] R ⊗[B] C)).comap (algebraMap B C) ∧ t * b ∈ J) → ∀ (y : M) (w : R ⊗[B] C), w ∉ Q₀ → w • ((1 : R ⊗[B] C) ⊗ₜ[R] y) = 0 → ∃ u : R, u ∉ Q₀.comap (Algebra.TensorProduct.includeLeftRingHom : R →+* R ⊗[B] C) ∧ u • y = 0 := by
  intro B R C M _ _ _ _ _ _ _ _ _ J hJ Q₀ hQ h1 h2 y w hw0 hw
  let p : Ideal R := Q₀.comap (Algebra.TensorProduct.includeLeftRingHom : R →+* R ⊗[B] C)
  haveI hp : p.IsPrime := Ideal.comap_isPrime _ _
  let A := Localization.AtPrime p
  let N := LocalizedModule p.primeCompl M
  letI : Module (A ⧸ Module.annihilator A N) N := Module.quotientAnnihilator
  haveI : IsScalarTower R (A ⧸ Module.annihilator A N) N := by
    refine ⟨fun r d n => ?_⟩
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective d
    have e : ∀ (x : A) (n : N), (Ideal.Quotient.mk (Module.annihilator A N) x) • n = x • n :=
      fun _ _ => rfl
    have e2 : r • Ideal.Quotient.mk (Module.annihilator A N) a =
        Ideal.Quotient.mk (Module.annihilator A N) (r • a) := rfl
    rw [e2, e, e, smul_assoc]
  have hJ' : ∀ a ∈ J, algebraMap R (A ⧸ Module.annihilator A N) (algebraMap B R a) = 0 := by
    intro a ha
    rw [IsScalarTower.algebraMap_apply R A (A ⧸ Module.annihilator A N),
      Ideal.Quotient.algebraMap_eq, Ideal.Quotient.eq_zero_iff_mem, Module.mem_annihilator]
    intro n
    induction n using LocalizedModule.induction_on with
    | _ m s =>
      rw [algebraMap_smul, LocalizedModule.smul'_mk, algebraMap_smul, hJ a ha, LocalizedModule.zero_mk]
  have hunit : ∀ r : R, r ∉ p → IsUnit (algebraMap R (A ⧸ Module.annihilator A N) r) := by
    intro r hr
    rw [IsScalarTower.algebraMap_apply R A (A ⧸ Module.annihilator A N)]
    exact (IsLocalization.map_units A (⟨r, hr⟩ : p.primeCompl)).map _
  have hy := map_eq_zero_of_smul_tmul (D := A ⧸ Module.annihilator A N) J hJ' Q₀ hQ hunit h1 h2
    (LocalizedModule.mkLinearMap p.primeCompl M) y w hw0 hw
  obtain ⟨s, hs⟩ := (IsLocalizedModule.eq_zero_iff p.primeCompl
    (LocalizedModule.mkLinearMap p.primeCompl M)).1 hy
  exact ⟨s, s.2, hs⟩

end GlobalTheory.CompanionTheory.KrullLocal
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TensorPrimeOverIdealCompletion
section
open TensorProduct

namespace GlobalTheory.CompanionTheory.KrullBaseChange

theorem krull_after_base_change {B R C M : Type} [CommRing B] [CommRing R] [CommRing C]
    [Algebra B R] [Algebra B C] [AddCommGroup M] [Module R M] [Module B M] [IsScalarTower B R M]
    [Module.Finite R M] [IsNoetherianRing (R ⊗[B] C)] (I : Ideal B) (y : M)
    (hy : ∀ n : ℕ, y ⊗ₜ[B] (1 : C) ∈
      LinearMap.range ((I ^ (n + 1) • ⊤ : Submodule B M).subtype.rTensor C))
    (Q₁ : Ideal (R ⊗[B] C)) (hQ : Q₁.IsPrime)
    (hI : I.map (algebraMap B R) ≤
      Q₁.comap (Algebra.TensorProduct.includeLeftRingHom : R →+* R ⊗[B] C)) :
    ∃ w : R ⊗[B] C, w ∉ Q₁ ∧ w • ((1 : R ⊗[B] C) ⊗ₜ[R] y) = 0 := by
  classical
  set K : Ideal (R ⊗[B] C) := I.map (algebraMap B (R ⊗[B] C)) with hK
  have hKQ : K ≤ Q₁ := by
    rw [hK, Ideal.map_le_iff_le_comap]
    intro b hb
    have h1 := hI (Ideal.mem_map_of_mem (algebraMap B R) hb)
    simpa [Ideal.mem_comap, Algebra.TensorProduct.algebraMap_apply] using h1
  have key : ∀ (b : B) (c : C), (1 : R) ⊗ₜ[B] (b • c) = (algebraMap B R b) • ((1 : R) ⊗ₜ[B] c) := by
    intro b c
    rw [TensorProduct.smul_tmul', ← TensorProduct.smul_tmul, smul_eq_mul, mul_one,
      Algebra.algebraMap_eq_smul_one]
  let φ : M ⊗[B] C →+ (R ⊗[B] C) ⊗[R] M :=
    (TensorProduct.liftAddHom
      { toFun := fun m =>
          { toFun := fun c => ((1 : R) ⊗ₜ[B] c) ⊗ₜ[R] m
            map_zero' := by simp
            map_add' := by intro a b; simp [TensorProduct.tmul_add, TensorProduct.add_tmul] }
        map_zero' := by ext c; simp
        map_add' := by intro a b; ext c; simp [TensorProduct.tmul_add] }
      (by
        intro b m c
        have h : (b • m : M) = (algebraMap B R b) • m := (algebraMap_smul R b m).symm
        simp only [AddMonoidHom.coe_mk, ZeroHom.coe_mk, h, key]
        rw [TensorProduct.smul_tmul]))
  have hφ : ∀ (m : M) (c : C), φ (m ⊗ₜ[B] c) = ((1 : R) ⊗ₜ[B] c) ⊗ₜ[R] m := fun m c => rfl
  have hmem : ∀ (n : ℕ) (z : M), z ∈ (I ^ n • ⊤ : Submodule B M) → ∀ c : C,
      ((1 : R) ⊗ₜ[B] c) ⊗ₜ[R] z ∈ (K ^ n • ⊤ : Submodule (R ⊗[B] C) ((R ⊗[B] C) ⊗[R] M)) := by
    intro n z hz c
    induction hz using Submodule.smul_induction_on' with
    | smul b hb m hm =>
      have h : (b • m : M) = (algebraMap B R b) • m := (algebraMap_smul R b m).symm
      have h2 : ((1 : R) ⊗ₜ[B] c) ⊗ₜ[R] (b • m) =
          (algebraMap B (R ⊗[B] C) b) • (((1 : R) ⊗ₜ[B] c) ⊗ₜ[R] m) := by
        have h3 : (algebraMap B R b) • ((1 : R) ⊗ₜ[B] c) =
            (algebraMap B (R ⊗[B] C) b) • ((1 : R) ⊗ₜ[B] c) := by
          rw [Algebra.TensorProduct.algebraMap_apply, smul_eq_mul,
            Algebra.TensorProduct.tmul_mul_tmul, TensorProduct.smul_tmul', smul_eq_mul]
          simp
        rw [h, ← TensorProduct.smul_tmul, h3, TensorProduct.smul_tmul']
      rw [h2]
      refine Submodule.smul_mem_smul ?_ Submodule.mem_top
      rw [hK, ← Ideal.map_pow]
      exact Ideal.mem_map_of_mem _ hb
    | add x _ y _ hx hy =>
      rw [TensorProduct.tmul_add]
      exact Submodule.add_mem _ hx hy
  have hall : ∀ n : ℕ, ∀ x : (I ^ (n + 1) • ⊤ : Submodule B M) ⊗[B] C,
      φ ((I ^ (n + 1) • ⊤ : Submodule B M).subtype.rTensor C x) ∈
        (K ^ (n + 1) • ⊤ : Submodule (R ⊗[B] C) ((R ⊗[B] C) ⊗[R] M)) := by
    intro n x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul z c =>
      simpa [hφ] using hmem (n + 1) z z.2 c
    | add a b ha hb =>
      rw [map_add, map_add]
      exact Submodule.add_mem _ ha hb
  have hone : φ (y ⊗ₜ[B] (1 : C)) = (1 : R ⊗[B] C) ⊗ₜ[R] y := rfl
  have hinf : ((1 : R ⊗[B] C) ⊗ₜ[R] y) ∈
      (⨅ i : ℕ, K ^ i • ⊤ : Submodule (R ⊗[B] C) ((R ⊗[B] C) ⊗[R] M)) := by
    rw [Submodule.mem_iInf]
    intro i
    obtain ⟨x, hx⟩ := hy i
    have h := hall i x
    rw [hx, hone] at h
    exact Submodule.smul_mono_left (Ideal.pow_le_pow_right (Nat.le_succ i)) h
  haveI : Module.Finite (R ⊗[B] C) ((R ⊗[B] C) ⊗[R] M) := Module.Finite.base_change R (R ⊗[B] C) M
  haveI : IsNoetherian (R ⊗[B] C) ((R ⊗[B] C) ⊗[R] M) := isNoetherian_of_isNoetherianRing_of_finite _ _
  obtain ⟨⟨r, hr⟩, e⟩ := (Ideal.mem_iInf_smul_pow_eq_bot_iff K _).1 hinf
  refine ⟨1 - r, ?_, ?_⟩
  · intro hw
    exact hQ.ne_top ((Ideal.eq_top_iff_one _).2 (by
      have := Q₁.add_mem hw (hKQ hr)
      simpa using this))
  · rw [sub_smul, one_smul]
    exact sub_eq_zero.2 e.symm

end GlobalTheory.CompanionTheory.KrullBaseChange
end

