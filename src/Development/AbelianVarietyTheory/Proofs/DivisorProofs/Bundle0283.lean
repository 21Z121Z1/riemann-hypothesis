import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0066
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0207
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0226
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0211
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0244
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0245
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0003
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StabilizerEqCentralizer
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0216
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0215

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitEqMulPowOnEtaleExcisionNbhdZeroLocus
section
open GlobalTheory.EtC

namespace GlobalTheory.EtC

theorem unit_eq_mul_qth_power_near_zeroLocus : ∀ (k B : Type) [Field k] [IsAlgClosed k] [CommRing B] [IsDedekindDomain B] [Algebra k B] [Algebra.FiniteType k B] (q : ℕ), IsUnit (q : k) → ∀ f : B, f ≠ 0 → ∀ (A₂ : Type) [CommRing A₂] [Algebra B A₂], IsExcisionNbhd B A₂ f → ∀ c : (Localization.Away (algebraMap B A₂ f))ˣ, ∀ (b₁ : B) (m : ℕ) (e : A₂), e - 1 ∈ Ideal.span {algebraMap B A₂ f} → algebraMap A₂ (Localization.Away (algebraMap B A₂ f)) (algebraMap B A₂ b₁) = (c : Localization.Away (algebraMap B A₂ f)) * algebraMap A₂ (Localization.Away (algebraMap B A₂ f)) (e * algebraMap B A₂ f ^ m) → ∀ g : B, IsCoprime f g → ∀ (u : (Localization.Away (f * g))ˣ) (n d : B), IsCoprime f n → IsCoprime f d → algebraMap B (Localization.Away (f * g)) (b₁ * d) = (u : Localization.Away (f * g)) * algebraMap B (Localization.Away (f * g)) (n * f ^ m) → ∃ (A₃ : Type) (_ : CommRing A₃) (_ : Algebra B A₃) (_ : Algebra A₂ A₃) (_ : IsScalarTower B A₂ A₃), IsExcisionNbhd B A₃ f ∧ IsUnit (algebraMap B A₃ g) ∧ ∃ v : (Localization.Away (algebraMap B A₃ f))ˣ, ∀ (φ : Localization.Away (algebraMap B A₂ f) →+* Localization.Away (algebraMap B A₃ f)) (ψ : Localization.Away (f * g) →+* Localization.Away (algebraMap B A₃ f)), φ.comp (algebraMap A₂ _) = (algebraMap A₃ _).comp (algebraMap A₂ A₃) → ψ.comp (algebraMap B _) = (algebraMap A₃ _).comp (algebraMap B A₃) → φ (c : Localization.Away (algebraMap B A₂ f)) = ψ (u : Localization.Away (f * g)) * (v : Localization.Away (algebraMap B A₃ f)) ^ q := by
  intro k B _ _ _ _ _ _ q hq f hf A₂ _ _ hA₂ c b₁ m e he hc g hg u n d hn hd hu
  have hq0 : q ≠ 0 := by
    rintro rfl; simp at hq
  obtain ⟨j, rfl⟩ : ∃ j, q = j + 1 := ⟨q - 1, by omega⟩
  obtain ⟨x₁, y₁, hxy₁⟩ := (hg.mul_right hn).mul_right hd
  obtain ⟨a, ha⟩ : ∃ a : A₂, a = algebraMap B A₂ (g * n * d) * e := ⟨_, rfl⟩
  have hab : a * algebraMap B A₂ y₁ - 1 ∈ Ideal.span {algebraMap B A₂ f} := by
    obtain ⟨t, ht⟩ := Ideal.mem_span_singleton.mp he
    have h1 := congrArg (algebraMap B A₂) hxy₁
    simp only [map_add, map_mul, map_one] at h1
    rw [Ideal.mem_span_singleton, ha]
    refine ⟨-(algebraMap B A₂ x₁) * e + t, ?_⟩
    simp only [map_mul]
    linear_combination e * h1 + ht
  have hA₂' : IsExcisionNbhd B (Localization.Away a) f := GlobalTheory.T.isExcisionNbhd_away_of_inverse_mod B A₂ f hA₂ a (algebraMap B A₂ y₁) hab
  have hdvd : ∀ z : A₂, z ∣ a → IsUnit (algebraMap A₂ (Localization.Away a) z) := fun z hz =>
    isUnit_of_dvd_unit (map_dvd _ hz) (IsLocalization.Away.algebraMap_isUnit a)
  have hgu := hdvd (algebraMap B A₂ g) ⟨algebraMap B A₂ n * algebraMap B A₂ d * e, by rw [ha]; simp only [map_mul]; ring⟩
  have hnu := hdvd (algebraMap B A₂ n) ⟨algebraMap B A₂ g * algebraMap B A₂ d * e, by rw [ha]; simp only [map_mul]; ring⟩
  have hdu := hdvd (algebraMap B A₂ d) ⟨algebraMap B A₂ g * algebraMap B A₂ n * e, by rw [ha]; simp only [map_mul]; ring⟩
  have heu := hdvd e ⟨algebraMap B A₂ (g * n * d), by rw [ha]; ring⟩
  obtain ⟨ε₀, hε₀⟩ : ∃ ε₀ : A₂, ε₀ = algebraMap B A₂ n * (algebraMap B A₂ d * e) ^ j := ⟨_, rfl⟩
  have hεu : IsUnit (algebraMap A₂ (Localization.Away a) ε₀) := by
    rw [hε₀, map_mul, map_pow, map_mul]; exact hnu.mul ((hdu.mul heu).pow j)
  obtain ⟨x₂, y₂, h₂⟩ := hn.mul_right (hd.pow_right (n := j))
  obtain ⟨r, hr⟩ := GlobalTheory.T.exists_pow_sub_mem_span_of_isUnit_mod k B (j + 1) hq f hf (n * d ^ j) y₂
    (Ideal.mem_span_singleton.mpr ⟨-x₂, by linear_combination h₂⟩)
  have hcong : ε₀ - algebraMap B A₂ r ^ (j + 1) ∈ Ideal.span {algebraMap B A₂ f} := by
    have h1 : algebraMap B A₂ f ∣ algebraMap B A₂ (n * d ^ j - r ^ (j + 1)) :=
      map_dvd _ (Ideal.mem_span_singleton.mp hr)
    have h2 : algebraMap B A₂ f ∣ e ^ j - 1 :=
      (Ideal.mem_span_singleton.mp he).trans (by simpa using sub_dvd_pow_sub_pow e 1 j)
    have h3 : ε₀ - algebraMap B A₂ r ^ (j + 1) = algebraMap B A₂ (n * d ^ j - r ^ (j + 1)) +
        algebraMap B A₂ n * algebraMap B A₂ d ^ j * (e ^ j - 1) := by
      rw [hε₀]; simp only [map_sub, map_mul, map_pow]; ring
    rw [Ideal.mem_span_singleton, h3]; exact dvd_add h1 (dvd_mul_of_dvd_right h2 _)
  have hcong' : algebraMap A₂ (Localization.Away a) ε₀ - algebraMap B (Localization.Away a) r ^ (j + 1) ∈
      Ideal.span {algebraMap B (Localization.Away a) f} := by
    rw [IsScalarTower.algebraMap_apply B A₂ (Localization.Away a) r,
      IsScalarTower.algebraMap_apply B A₂ (Localization.Away a) f, ← map_pow, ← map_sub,
      Ideal.mem_span_singleton]
    exact map_dvd _ (Ideal.mem_span_singleton.mp hcong)
  have hqu : IsUnit ((j + 1 : ℕ) : Localization.Away a) := by
    have := hq.map ((algebraMap B (Localization.Away a)).comp (algebraMap k B)); rwa [map_natCast] at this
  obtain ⟨A₃, _, _, hA₃, x, hx⟩ := GlobalTheory.T.exists_excisionNbhd_with_root_of_isUnit (Localization.Away a) (algebraMap B (Localization.Away a) f)
    (j + 1) hqu _ _ hεu hcong'
  letI : Algebra B A₃ := RingHom.toAlgebra ((algebraMap (Localization.Away a) A₃).comp (algebraMap B (Localization.Away a)))
  letI : Algebra A₂ A₃ := RingHom.toAlgebra ((algebraMap (Localization.Away a) A₃).comp (algebraMap A₂ (Localization.Away a)))
  haveI t1 : IsScalarTower B (Localization.Away a) A₃ := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI t3 : IsScalarTower B A₂ A₃ := IsScalarTower.of_algebraMap_eq (fun z => by
    show algebraMap (Localization.Away a) A₃ (algebraMap B (Localization.Away a) z) =
      algebraMap (Localization.Away a) A₃ (algebraMap A₂ (Localization.Away a) (algebraMap B A₂ z))
    rw [IsScalarTower.algebraMap_apply B A₂ (Localization.Away a) z])
  refine ⟨A₃, inferInstance, inferInstance, inferInstance, t3, GlobalTheory.T.isExcisionNbhd_trans' B (Localization.Away a) A₃ f hA₂' hA₃, ?_, ?_⟩
  · have : algebraMap B A₃ g = algebraMap (Localization.Away a) A₃
        (algebraMap A₂ (Localization.Away a) (algebraMap B A₂ g)) := by
      rw [← IsScalarTower.algebraMap_apply B A₂ (Localization.Away a)]; rfl
    rw [this]; exact hgu.map _
  have hDu : IsUnit (algebraMap A₃ (Localization.Away (algebraMap B A₃ f))
      (algebraMap A₂ A₃ (algebraMap B A₂ d * e))) := by
    have hde : IsUnit (algebraMap A₂ (Localization.Away a) (algebraMap B A₂ d * e)) := by
      rw [map_mul]; exact hdu.mul heu
    exact (hde.map (algebraMap (Localization.Away a) A₃)).map _
  have hX : algebraMap A₃ (Localization.Away (algebraMap B A₃ f)) x ^ (j + 1) =
      algebraMap A₃ (Localization.Away (algebraMap B A₃ f)) (algebraMap A₂ A₃ (algebraMap B A₂ n)) *
      (algebraMap A₃ (Localization.Away (algebraMap B A₃ f)) (algebraMap A₂ A₃ (algebraMap B A₂ d)) *
       algebraMap A₃ (Localization.Away (algebraMap B A₃ f)) (algebraMap A₂ A₃ e)) ^ j := by
    rw [← map_pow, ← hx]
    show algebraMap A₃ _ (algebraMap A₂ A₃ ε₀) = _
    rw [hε₀]; simp only [map_mul, map_pow]
  have hXu : IsUnit (algebraMap A₃ (Localization.Away (algebraMap B A₃ f)) x) :=
    (isUnit_pow_iff (Nat.succ_ne_zero j)).mp (by rw [← map_pow, ← hx]; exact (hεu.map _).map _)
  have hFu : IsUnit (algebraMap A₃ (Localization.Away (algebraMap B A₃ f)) (algebraMap A₂ A₃ (algebraMap B A₂ f))) := by
    rw [← IsScalarTower.algebraMap_apply B A₂ A₃]; exact IsLocalization.Away.algebraMap_isUnit _
  refine ⟨hXu.unit * hDu.unit⁻¹, fun φ ψ hφ hψ => ?_⟩
  have hφ' : ∀ y, φ (algebraMap A₂ _ y) = algebraMap A₃ (Localization.Away (algebraMap B A₃ f)) (algebraMap A₂ A₃ y) :=
    fun y => RingHom.congr_fun hφ y
  have hψ' : ∀ z, ψ (algebraMap B _ z) =
      algebraMap A₃ (Localization.Away (algebraMap B A₃ f)) (algebraMap A₂ A₃ (algebraMap B A₂ z)) := fun z => by
    have := RingHom.congr_fun hψ z
    simp only [RingHom.comp_apply] at this
    rw [this, IsScalarTower.algebraMap_apply B A₂ A₃ z]
  have H1 := congrArg φ hc
  have H2 := congrArg ψ hu
  simp only [map_mul, map_pow, hφ'] at H1
  simp only [map_mul, map_pow, hψ'] at H2
  have hW := hDu.mul_val_inv
  rw [Units.val_mul, IsUnit.unit_spec]
  generalize (↑hDu.unit⁻¹ : Localization.Away (algebraMap B A₃ f)) = W at hW ⊢
  simp only [map_mul] at hW hFu
  have key0 : φ c * algebraMap A₃ (Localization.Away (algebraMap B A₃ f)) (algebraMap A₂ A₃ (algebraMap B A₂ d)) *
      algebraMap A₃ (Localization.Away (algebraMap B A₃ f)) (algebraMap A₂ A₃ e) =
      ψ u * algebraMap A₃ (Localization.Away (algebraMap B A₃ f)) (algebraMap A₂ A₃ (algebraMap B A₂ n)) := by
    apply (hFu.pow m).mul_right_cancel
    linear_combination -(algebraMap A₃ (Localization.Away (algebraMap B A₃ f)) (algebraMap A₂ A₃ (algebraMap B A₂ d))) * H1 + H2
  calc φ c = φ c * (algebraMap A₃ (Localization.Away (algebraMap B A₃ f)) (algebraMap A₂ A₃ (algebraMap B A₂ d)) *
        algebraMap A₃ (Localization.Away (algebraMap B A₃ f)) (algebraMap A₂ A₃ e) * W) ^ (j + 1) := by
        rw [hW, one_pow, mul_one]
    _ = _ := by
      linear_combination (algebraMap A₃ (Localization.Away (algebraMap B A₃ f)) (algebraMap A₂ A₃ (algebraMap B A₂ d)) *
        algebraMap A₃ (Localization.Away (algebraMap B A₃ f)) (algebraMap A₂ A₃ e)) ^ j * W ^ (j + 1) * key0 -
        ψ u * W ^ (j + 1) * hX

end GlobalTheory.EtC
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryPQContinuousCharacterEqDetPowProd
section
open Matrix
open scoped ComplexOrder

namespace GlobalTheory.UpqChar

theorem det_conj_rect {ι κ : Type} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (B : Matrix ι κ ℂ) (B' : Matrix κ ι ℂ) (h1 : B * B' = 1) (h2 : B' * B = 1)
    (M : Matrix κ κ ℂ) : (B * M * B').det = M.det := by
  classical
  have hcard : Fintype.card κ = Fintype.card ι := by
    let e : (κ → ℂ) ≃ₗ[ℂ] (ι → ℂ) :=
      { toFun := fun v => B *ᵥ v
        invFun := fun v => B' *ᵥ v
        map_add' := fun v w => Matrix.mulVec_add B v w
        map_smul' := fun a v => by simp [Matrix.mulVec_smul]
        left_inv := fun v => by simp [Matrix.mulVec_mulVec, h2]
        right_inv := fun v => by simp [Matrix.mulVec_mulVec, h1] }
    simpa using e.finrank_eq
  let e : ι ≃ κ := Fintype.equivOfCardEq hcard.symm
  have hC : B.submatrix id e * B'.submatrix e id = 1 := by
    rw [Matrix.submatrix_mul_equiv, h1, Matrix.submatrix_id_id]
  have hM : B * M * B' = B.submatrix id e * M.submatrix e e * B'.submatrix e id := by
    rw [Matrix.submatrix_mul_equiv, Matrix.submatrix_mul_equiv, Matrix.submatrix_id_id]
  have hd : (B.submatrix id e).det * (B'.submatrix e id).det = 1 := by
    rw [← Matrix.det_mul, hC, Matrix.det_one]
  rw [hM, Matrix.det_mul, Matrix.det_mul, Matrix.det_submatrix_equiv_self]
  calc (B.submatrix id e).det * M.det * (B'.submatrix e id).det
      = ((B.submatrix id e).det * (B'.submatrix e id).det) * M.det := by ring
    _ = M.det := by rw [hd, one_mul]

theorem char_unitary {p : ℕ} (f : Matrix.unitaryGroup (Fin p) ℂ → ℂ)
    (hmul : ∀ a b, f (a * b) = f a * f b) (hn : ∀ a, ‖f a‖ = 1) (hc : Continuous f) :
    ∃ x : ℤ, ∀ a, f a = (Matrix.det (a : Matrix (Fin p) (Fin p) ℂ)) ^ x := by
  have hone : f 1 = 1 := by
    have h := hmul 1 1
    rw [mul_one] at h
    have hne : f 1 ≠ 0 := fun h0 => by simpa [h0] using hn 1
    exact mul_left_cancel₀ hne (by rw [mul_one]; exact h.symm)
  have hmem : ∀ a, f a ∈ Submonoid.unitSphere ℂ := fun a => mem_sphere_zero_iff_norm.2 (hn a)
  let c : Matrix.unitaryGroup (Fin p) ℂ →* Circle :=
    { toFun := fun a => ⟨f a, hmem a⟩
      map_one' := Circle.ext hone
      map_mul' := fun a b => Circle.ext (hmul a b) }
  have hcont : Continuous c := Continuous.subtype_mk hc hmem
  obtain ⟨m, hm⟩ := GlobalTheory.T.unitaryGroup_continuous_char_eq_det_zpow p c hcont
  exact ⟨m, fun a => hm a⟩

private theorem matrix_eq_zero_of_eq_neg {ι κ : Type} (X : Matrix ι κ ℂ) (h : X = -X) : X = 0 := by
  ext i j
  have h' := congrFun (congrFun h i) j
  simp only [Matrix.neg_apply] at h'
  simp only [Matrix.zero_apply]
  linear_combination h' / 2

theorem char_Upq : ∀ (n p q : ℕ) (G s : Matrix (Fin n) (Fin n) ℂ) (B : Matrix (Fin n) (Fin p ⊕ Fin q) ℂ) (B' : Matrix (Fin p ⊕ Fin q) (Fin n) ℂ), B * B' = 1 → B' * B = 1 → Bᴴ * G * B = Matrix.fromBlocks 1 0 0 (-1) → s * B = B * Matrix.fromBlocks 1 0 0 (-1) → ∀ c : Matrix (Fin n) (Fin n) ℂ → ℂ, (∀ k k' : Matrix (Fin n) (Fin n) ℂ, kᴴ * G * k = G → s * k = k * s → k'ᴴ * G * k' = G → s * k' = k' * s → c (k * k') = c k * c k') → (∀ k : Matrix (Fin n) (Fin n) ℂ, kᴴ * G * k = G → s * k = k * s → ‖c k‖ = 1) → ContinuousOn c {k | kᴴ * G * k = G ∧ s * k = k * s} → ∃ x y : ℤ, ∀ k : Matrix (Fin n) (Fin n) ℂ, kᴴ * G * k = G → s * k = k * s → c k = ((1 / 2 : ℂ) • (1 + s) * k + (1 / 2 : ℂ) • (1 - s)).det ^ x * ((1 / 2 : ℂ) • (1 - s) * k + (1 / 2 : ℂ) • (1 + s)).det ^ y := by
  intro n p q G s B B' hBB' hB'B hG hs c hmul hnorm hcont
  classical
  obtain ⟨J, hJdef⟩ : ∃ J : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ, J = Matrix.fromBlocks 1 0 0 (-1) :=
    ⟨_, rfl⟩
  rw [← hJdef] at hG hs
  replace hs : s * B = B * J := hs
  replace hG : Bᴴ * G * B = J := hG
  replace hBB' : B * B' = 1 := hBB'
  replace hB'B : B' * B = 1 := hB'B
  have hconj : ∀ X Y : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ,
      (B * X * B') * (B * Y * B') = B * (X * Y) * B' := by
    intro X Y
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc B' B, hB'B, Matrix.one_mul]
  have hsJ : s = B * J * B' := by
    rw [← hs, Matrix.mul_assoc, hBB', Matrix.mul_one]
  have hGJ : G = B'ᴴ * J * B' := by
    rw [← hG]
    have h0 : (B * B')ᴴ = 1 := by rw [hBB', Matrix.conjTranspose_one]
    rw [Matrix.conjTranspose_mul] at h0
    calc G = (B'ᴴ * Bᴴ) * G * (B * B') := by rw [h0, hBB', Matrix.one_mul, Matrix.mul_one]
      _ = B'ᴴ * (Bᴴ * G * B) * B' := by simp only [Matrix.mul_assoc]
  have hK : ∀ (a : Matrix (Fin p) (Fin p) ℂ) (d : Matrix (Fin q) (Fin q) ℂ), aᴴ * a = 1 → dᴴ * d = 1 →
      (B * Matrix.fromBlocks a 0 0 d * B')ᴴ * G * (B * Matrix.fromBlocks a 0 0 d * B') = G ∧
      s * (B * Matrix.fromBlocks a 0 0 d * B') = (B * Matrix.fromBlocks a 0 0 d * B') * s := by
    intro a d ha hd
    constructor
    · have hm : (Matrix.fromBlocks a 0 0 d)ᴴ * J * Matrix.fromBlocks a 0 0 d = J := by
        rw [hJdef, Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
        simp [ha, hd]
      calc (B * Matrix.fromBlocks a 0 0 d * B')ᴴ * G * (B * Matrix.fromBlocks a 0 0 d * B')
          = B'ᴴ * ((Matrix.fromBlocks a 0 0 d)ᴴ * (Bᴴ * G * B) * Matrix.fromBlocks a 0 0 d) * B' := by
            simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
        _ = G := by rw [hG, hm, ← hGJ]
    · rw [hsJ, hconj, hconj, hJdef, Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
      simp
  let kA : Matrix.unitaryGroup (Fin p) ℂ → Matrix (Fin n) (Fin n) ℂ :=
    fun a => B * (Matrix.fromBlocks (a : Matrix (Fin p) (Fin p) ℂ) 0 0 1 : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) * B'
  let kD : Matrix.unitaryGroup (Fin q) ℂ → Matrix (Fin n) (Fin n) ℂ :=
    fun d => B * (Matrix.fromBlocks 1 0 0 (d : Matrix (Fin q) (Fin q) ℂ) : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) * B'
  have hKA : ∀ a : Matrix.unitaryGroup (Fin p) ℂ, (kA a)ᴴ * G * kA a = G ∧ s * kA a = kA a * s := by
    intro a
    refine hK _ _ ?_ (by simp)
    rw [← Matrix.star_eq_conjTranspose]
    exact Matrix.mem_unitaryGroup_iff'.1 a.2
  have hKD : ∀ d : Matrix.unitaryGroup (Fin q) ℂ, (kD d)ᴴ * G * kD d = G ∧ s * kD d = kD d * s := by
    intro d
    refine hK _ _ (by simp) ?_
    rw [← Matrix.star_eq_conjTranspose]
    exact Matrix.mem_unitaryGroup_iff'.1 d.2
  have hkAmul : ∀ a b : Matrix.unitaryGroup (Fin p) ℂ, kA (a * b) = kA a * kA b := by
    intro a b
    show B * (Matrix.fromBlocks ((a * b : Matrix.unitaryGroup (Fin p) ℂ) : Matrix (Fin p) (Fin p) ℂ) 0 0 1 : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) * B' =
      (B * (Matrix.fromBlocks (a : Matrix (Fin p) (Fin p) ℂ) 0 0 1 : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) * B') *
        (B * (Matrix.fromBlocks (b : Matrix (Fin p) (Fin p) ℂ) 0 0 1 : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) * B')
    rw [hconj, Matrix.fromBlocks_multiply]
    simp
  have hkDmul : ∀ a b : Matrix.unitaryGroup (Fin q) ℂ, kD (a * b) = kD a * kD b := by
    intro a b
    show B * (Matrix.fromBlocks 1 0 0 ((a * b : Matrix.unitaryGroup (Fin q) ℂ) : Matrix (Fin q) (Fin q) ℂ) : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) * B' =
      (B * (Matrix.fromBlocks 1 0 0 (a : Matrix (Fin q) (Fin q) ℂ) : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) * B') *
        (B * (Matrix.fromBlocks 1 0 0 (b : Matrix (Fin q) (Fin q) ℂ) : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) * B')
    rw [hconj, Matrix.fromBlocks_multiply]
    simp
  have hkAc : Continuous kA := by
    show Continuous (fun a : Matrix.unitaryGroup (Fin p) ℂ =>
      B * (Matrix.fromBlocks (a : Matrix (Fin p) (Fin p) ℂ) 0 0 1 : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) * B')
    fun_prop
  have hkDc : Continuous kD := by
    show Continuous (fun d : Matrix.unitaryGroup (Fin q) ℂ =>
      B * (Matrix.fromBlocks 1 0 0 (d : Matrix (Fin q) (Fin q) ℂ) : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) * B')
    fun_prop
  obtain ⟨x, hx⟩ := char_unitary (fun a => c (kA a))
    (fun a b => by
      show c (kA (a * b)) = c (kA a) * c (kA b)
      rw [hkAmul]
      exact hmul _ _ (hKA a).1 (hKA a).2 (hKA b).1 (hKA b).2)
    (fun a => hnorm _ (hKA a).1 (hKA a).2) (hcont.comp_continuous hkAc hKA)
  obtain ⟨y, hy⟩ := char_unitary (fun d => c (kD d))
    (fun a b => by
      show c (kD (a * b)) = c (kD a) * c (kD b)
      rw [hkDmul]
      exact hmul _ _ (hKD a).1 (hKD a).2 (hKD b).1 (hKD b).2)
    (fun d => hnorm _ (hKD d).1 (hKD d).2) (hcont.comp_continuous hkDc hKD)
  have hx' : ∀ a : Matrix.unitaryGroup (Fin p) ℂ, c (kA a) = (a : Matrix (Fin p) (Fin p) ℂ).det ^ x := hx
  have hy' : ∀ d : Matrix.unitaryGroup (Fin q) ℂ, c (kD d) = (d : Matrix (Fin q) (Fin q) ℂ).det ^ y := hy
  refine ⟨x, y, fun k hk1 hk2 => ?_⟩
  obtain ⟨m, hmdef⟩ : ∃ m, m = B' * k * B := ⟨_, rfl⟩
  have hk_eq : k = B * m * B' := by
    calc k = (B * B') * k * (B * B') := by rw [hBB', Matrix.one_mul, Matrix.mul_one]
      _ = B * m * B' := by simp only [hmdef, Matrix.mul_assoc]
  have hJm : J * m = m * J := by
    have hJ : J = B' * s * B := by
      rw [Matrix.mul_assoc, hs, ← Matrix.mul_assoc, hB'B, Matrix.one_mul]
    rw [hJ, hmdef]
    calc B' * s * B * (B' * k * B) = B' * (s * k) * B := by
          simp only [Matrix.mul_assoc]
          rw [← Matrix.mul_assoc B B', hBB', Matrix.one_mul]
      _ = B' * (k * s) * B := by rw [hk2]
      _ = B' * k * B * (B' * s * B) := by
          simp only [Matrix.mul_assoc]
          rw [← Matrix.mul_assoc B B', hBB', Matrix.one_mul]
  have hoff : m.toBlocks₁₂ = 0 ∧ m.toBlocks₂₁ = 0 := by
    have h := hJm
    rw [hJdef, ← Matrix.fromBlocks_toBlocks m, Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply,
      Matrix.fromBlocks_inj] at h
    obtain ⟨-, hb, hc, -⟩ := h
    simp only [Matrix.one_mul, Matrix.zero_mul, Matrix.mul_one, Matrix.mul_zero, add_zero, zero_add,
      Matrix.neg_mul, Matrix.mul_neg] at hb hc
    exact ⟨matrix_eq_zero_of_eq_neg _ hb, matrix_eq_zero_of_eq_neg _ hc.symm⟩
  obtain ⟨a, d, hmad⟩ : ∃ a d, m = Matrix.fromBlocks a 0 0 d :=
    ⟨m.toBlocks₁₁, m.toBlocks₂₂, by rw [← hoff.1, ← hoff.2, Matrix.fromBlocks_toBlocks]⟩
  have hmU : mᴴ * J * m = J := by
    rw [← hG, hmdef]
    calc (B' * k * B)ᴴ * (Bᴴ * G * B) * (B' * k * B)
        = Bᴴ * (kᴴ * ((B * B')ᴴ * G * (B * B')) * k) * B := by
          simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = Bᴴ * G * B := by rw [hBB', Matrix.conjTranspose_one, Matrix.one_mul, Matrix.mul_one, hk1]
  rw [hmad, hJdef, Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply,
    Matrix.fromBlocks_inj] at hmU
  obtain ⟨ha, -, -, hd⟩ := hmU
  simp only [Matrix.conjTranspose_zero, Matrix.mul_one, Matrix.mul_zero,
    add_zero, zero_add, Matrix.neg_mul, Matrix.mul_neg, neg_inj] at ha hd
  have ha' : a ∈ Matrix.unitaryGroup (Fin p) ℂ :=
    Matrix.mem_unitaryGroup_iff'.2 (by rw [Matrix.star_eq_conjTranspose]; exact ha)
  have hd' : d ∈ Matrix.unitaryGroup (Fin q) ℂ :=
    Matrix.mem_unitaryGroup_iff'.2 (by rw [Matrix.star_eq_conjTranspose]; exact hd)
  have hkAD : k = kA ⟨a, ha'⟩ * kD ⟨d, hd'⟩ := by
    rw [hk_eq, hmad]
    show B * Matrix.fromBlocks a 0 0 d * B' =
      (B * (Matrix.fromBlocks a 0 0 1 : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) * B') * (B * (Matrix.fromBlocks 1 0 0 d : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) * B')
    rw [hconj, Matrix.fromBlocks_multiply]
    simp
  have h1 : (1 : Matrix (Fin n) (Fin n) ℂ) = B * (1 : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) * B' := by rw [Matrix.mul_one, hBB']
  have hJ1 : (1 / 2 : ℂ) • (1 + J) = (Matrix.fromBlocks (1 : Matrix (Fin p) (Fin p) ℂ) 0 0 0 : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) := by
    rw [hJdef]
    ext (i | i) (j | j) <;> simp [Matrix.one_apply] <;> (try split_ifs) <;> norm_num
  have hJ2 : (1 / 2 : ℂ) • (1 - J) = (Matrix.fromBlocks 0 0 0 (1 : Matrix (Fin q) (Fin q) ℂ) : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) := by
    rw [hJdef]
    ext (i | i) (j | j) <;> simp [Matrix.one_apply] <;> (try split_ifs) <;> norm_num
  have hP1 : (1 / 2 : ℂ) • (1 + s) = B * (Matrix.fromBlocks (1 : Matrix (Fin p) (Fin p) ℂ) 0 0 0 : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) * B' := by
    rw [← hJ1, hsJ, h1, ← Matrix.add_mul, ← Matrix.mul_add, Matrix.mul_smul, Matrix.smul_mul]
  have hP2 : (1 / 2 : ℂ) • (1 - s) = B * (Matrix.fromBlocks 0 0 0 (1 : Matrix (Fin q) (Fin q) ℂ) : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) * B' := by
    rw [← hJ2, hsJ, h1, ← Matrix.sub_mul, ← Matrix.mul_sub, Matrix.mul_smul, Matrix.smul_mul]
  have hE1 : (1 / 2 : ℂ) • (1 + s) * k + (1 / 2 : ℂ) • (1 - s) = B * (Matrix.fromBlocks a 0 0 1 : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) * B' := by
    rw [hP1, hP2, hk_eq, hmad, hconj, ← Matrix.add_mul, ← Matrix.mul_add, Matrix.fromBlocks_multiply,
      Matrix.fromBlocks_add]
    simp
  have hE2 : (1 / 2 : ℂ) • (1 - s) * k + (1 / 2 : ℂ) • (1 + s) = B * (Matrix.fromBlocks 1 0 0 d : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) * B' := by
    rw [hP1, hP2, hk_eq, hmad, hconj, ← Matrix.add_mul, ← Matrix.mul_add, Matrix.fromBlocks_multiply,
      Matrix.fromBlocks_add]
    simp
  rw [hE1, hE2, det_conj_rect B B' hBB' hB'B, det_conj_rect B B' hBB' hB'B,
    Matrix.det_fromBlocks_zero₂₁, Matrix.det_fromBlocks_zero₂₁, Matrix.det_one, Matrix.det_one, mul_one,
    one_mul, hkAD, hmul _ _ (hKA _).1 (hKA _).2 (hKD _).1 (hKD _).2, hx', hy']

end GlobalTheory.UpqChar
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeierstrassConstantQExpansionStatement
section
open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate
open GlobalTheory.QFam GlobalTheory.WpFam
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weierstrass_constant_q_expansion : ∀ (N : ℕ) [NeZero N], HasQ N gN (cG N) := by
  first | exact @GlobalTheory.WpFam.hasQ_gN | exact GlobalTheory.WpFam.hasQ_gN | (intros; apply GlobalTheory.WpFam.hasQ_gN <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeierstrassEisensteinNonholomorphicIdentityStatement
section
open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate
open GlobalTheory.QFam GlobalTheory.WpFam
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weierstrass_eisenstein_nonholomorphic_identity : ∀ (N : ℕ) (y : Fin 2 → ZMod N) (τ : ℍ), ((Real.pi / τ.im : ℝ) : ℂ) / (2 * Real.pi * Complex.I) ^ 2 - wB N y τ = -(G2s τ / (2 * (Real.pi : ℂ) * Complex.I) ^ 2 + wp N y τ) := by
  first | exact @GlobalTheory.wB_nonhol_correction | exact GlobalTheory.wB_nonhol_correction | (intros; apply GlobalTheory.wB_nonhol_correction <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightedOrbitSumEqPairOrbitSum
section
open GlobalTheory.OrbitUnfold GlobalTheory.OrbitUnfold.ConjSelf

namespace GlobalTheory.OrbitUnfold

variable {Γ Y : Type} [Group Γ] [MulAction Γ Y]

theorem card_stabilizer_pair_eq (y : Y) (γ : ConjSelf Γ) :
    Nat.card (MulAction.stabilizer Γ (y, γ)) =
      Nat.card (MulAction.stabilizer (MulAction.stabilizer Γ y) γ) := by
  have hmap : (MulAction.stabilizer (MulAction.stabilizer Γ y) γ).map
      (MulAction.stabilizer Γ y).subtype = MulAction.stabilizer Γ (y, γ) := by
    ext η
    simp only [Subgroup.mem_map, MulAction.mem_stabilizer_iff, Subgroup.coe_subtype, Prod.smul_mk,
      Prod.mk.injEq]
    constructor
    · rintro ⟨k, hk, rfl⟩
      exact ⟨k.2, hk⟩
    · rintro ⟨h1, h2⟩
      exact ⟨⟨η, h1⟩, h2, rfl⟩
  rw [← hmap, Subgroup.card_map_of_injective (Subgroup.subtype_injective _)]

end GlobalTheory.OrbitUnfold

namespace GlobalTheory.OrbitUnfold

variable {Γ Y : Type} [Group Γ] [MulAction Γ Y]

theorem inner_sum_eq (F : Y → Γ → ℂ)
    (hF : ∀ (η : Γ) (y : Y) (γ : Γ), F (η • y) (η * γ * η⁻¹) = F y γ) (y : Y)
    (hfin : (MulAction.stabilizer Γ y : Set Γ).Finite) (hsupp : (Function.support (F y)).Finite) :
    ∑ᶠ o' : MulAction.orbitRel.Quotient (MulAction.stabilizer Γ y) (ConjSelf Γ),
        pairTerm F (y, Quotient.out o') =
      ((Nat.card (MulAction.stabilizer Γ y) : ℕ) : ℂ)⁻¹ * ∑ᶠ γ : Γ, F y γ := by
  haveI : Finite (MulAction.stabilizer Γ y) := hfin.to_subtype
  have hinv : ∀ (k : MulAction.stabilizer Γ y) (z : ConjSelf Γ),
      F y (val (k • z)) = F y (val z) := by
    intro k z
    have hk : (k : Γ) • y = y := k.2
    have e1 : val (k • z) = (k : Γ) * val z * (k : Γ)⁻¹ := rfl
    have e2 := hF (k : Γ) y (val z)
    rw [hk] at e2
    rw [e1, e2]
  have hs : (Function.support (fun z : ConjSelf Γ => F y (val z))).Finite := hsupp
  have key := GlobalTheory.T.finsum_orbits_inv_stabilizer_card_mass (K := MulAction.stabilizer Γ y) (Z := ConjSelf Γ)
    (fun z => F y (val z)) hinv hs
  refine Eq.trans ?_ key
  refine finsum_congr fun o' => ?_
  unfold pairTerm
  rw [card_stabilizer_pair_eq]

theorem orbitSum_eq_pairSum (F : Y → Γ → ℂ)
    (hF : ∀ (η : Γ) (y : Y) (γ : Γ), F (η • y) (η * γ * η⁻¹) = F y γ)
    (hstab : ∀ y : Y, (MulAction.stabilizer Γ y : Set Γ).Finite)
    (hsupp : ∀ y : Y, (Function.support (F y)).Finite)
    (horb : {o : MulAction.orbitRel.Quotient Γ Y | ∃ γ, F (Quotient.out o) γ ≠ 0}.Finite) :
    ∑ᶠ o : MulAction.orbitRel.Quotient Γ Y,
        ((Nat.card (MulAction.stabilizer Γ (Quotient.out o)) : ℕ) : ℂ)⁻¹ * ∑ᶠ γ : Γ, F (Quotient.out o) γ =
      pairSum F := by
  have hg := GlobalTheory.T.finite_support_stabilizerWeightedPairTerm F hF hsupp horb
  have hπ : ∀ (h : Γ) (x : Y × ConjSelf Γ), (h • x).1 = h • x.1 := fun _ _ => rfl
  have hinj : ∀ y : Y, Function.Injective (fun γ : ConjSelf Γ => (y, γ)) :=
    fun y a b hab => (Prod.mk.inj hab).2
  have hsurj : ∀ (y : Y) (x : Y × ConjSelf Γ), x.1 = y → ∃ e : ConjSelf Γ, (y, e) = x := by
    rintro y ⟨a, b⟩ rfl
    exact ⟨b, rfl⟩
  have hequi : ∀ (y : Y), ∀ h ∈ MulAction.stabilizer Γ y, ∀ e : ConjSelf Γ,
      ((y, h • e) : Y × ConjSelf Γ) = h • (y, e) := by
    intro y h hh e
    have hh' : h • y = y := hh
    rw [Prod.smul_mk, hh']
  have h := GlobalTheory.T.finsum_orbitRel_fibred_equivariant (H := Γ) (X := Y × ConjSelf Γ) (B := Y) (E := ConjSelf Γ) Prod.fst
    hπ (fun y => MulAction.stabilizer Γ y) (fun _ => le_rfl)
    (fun y γ => (y, γ)) hinj (fun _ _ => rfl) hsurj hequi
    Quotient.out (fun q => Quotient.out_eq q)
    (fun o => pairTerm F (Quotient.out o)) hg
  unfold pairSum
  rw [h]
  refine finsum_congr fun q => ?_
  rw [← inner_sum_eq F hF (Quotient.out q) (hstab _) (hsupp _)]
  refine finsum_congr fun o' => ?_
  exact (pairTerm_out F hF (Quotient.out q, Quotient.out o')).symm

end GlobalTheory.OrbitUnfold
end

