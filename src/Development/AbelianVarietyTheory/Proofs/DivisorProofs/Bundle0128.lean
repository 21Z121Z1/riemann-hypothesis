import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0012
import Formalism.SatakeDualWeyl.Statement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0012
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0014
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0010
import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.IsIsoTermComparisonRestrictScalars
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0007
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0008

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CartanInvolutionConjOfPosDef
section
open MeasureTheory Complex Matrix GlobalTheory.RealWeil
open scoped RealInnerProductSpace ContDiff Real ComplexOrder

namespace GlobalTheory

open scoped MatrixOrder in

theorem cartanInvolution_conj_of_posDef (ι : Type) [Fintype ι] [DecidableEq ι]
    (s s' : Matrix ι ι ℂ) (hs : sᴴ = s) (hss : s * s = 1) (hs's' : s' * s' = 1)
    (hM : (s * s').PosDef) :
    ∃ a : Matrix ι ι ℂ, aᴴ * s * a = s ∧ a * s = s' * a := by
  set M := s * s' with hMdef
  have hMpsd : M.PosSemidef := hM.posSemidef
  have hM0 : 0 ≤ M := Matrix.nonneg_iff_posSemidef.mpr hMpsd
  set R := CFC.sqrt M with hRdef
  have hR0 : 0 ≤ R := CFC.sqrt_nonneg M
  have hRpsd : R.PosSemidef := Matrix.nonneg_iff_posSemidef.mp hR0
  have hRR : R * R = M := CFC.sqrt_mul_sqrt_self M hM0
  have hRh : Rᴴ = R := hRpsd.isHermitian
  have hsM : s * M = s' := by rw [hMdef, ← Matrix.mul_assoc, hss, Matrix.one_mul]
  have hMinv : M⁻¹ = s * M * s := by
    apply Matrix.inv_eq_left_inv
    calc s * M * s * M = (s * M) * (s * M) := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hsM, hs's']
  have hsRs : CFC.sqrt M⁻¹ = s * R * s := by
    refine CFC.sqrt_unique ?_ ?_
    · calc s * R * s * (s * R * s) = s * (R * R) * s := by
            simp only [Matrix.mul_assoc]
            rw [← Matrix.mul_assoc s s, hss, Matrix.one_mul]
        _ = M⁻¹ := by rw [hRR, hMinv]
    · have h := hRpsd.conjTranspose_mul_mul_same s
      rw [hs] at h
      exact Matrix.nonneg_iff_posSemidef.mpr h
  have hRinv : R⁻¹ = s * R * s := by
    rw [← hsRs]
    exact hMpsd.inv_sqrt
  have hMu : IsUnit M.det := isUnit_iff_ne_zero.mpr hM.det_pos.ne'
  have hRu : IsUnit R.det := by
    rw [← hRR, Matrix.det_mul] at hMu
    exact isUnit_of_mul_isUnit_left hMu
  have hsRinv : s * R⁻¹ = R * s := by
    rw [hRinv, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hss, Matrix.one_mul]
  refine ⟨R⁻¹, ?_, ?_⟩
  · rw [Matrix.conjTranspose_nonsing_inv, hRh, Matrix.mul_assoc, hsRinv, ← Matrix.mul_assoc,
      Matrix.nonsing_inv_mul _ hRu, Matrix.one_mul]
  · calc R⁻¹ * s = s * R := by rw [hRinv, Matrix.mul_assoc, hss, Matrix.mul_one]
      _ = s * M * R⁻¹ := by
        rw [← hRR, Matrix.mul_assoc s, Matrix.mul_assoc R, Matrix.mul_nonsing_inv _ hRu,
          Matrix.mul_one]
      _ = s' * R⁻¹ := by rw [hsM]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CayleyTransformSkewMemUnitaryGroup
section
set_option autoImplicit false
noncomputable section
open NumberField

namespace GlobalTheory.CayleyUnitary

open Formalism.UG

theorem cT_add' {E : Type} [Field E] (σ : E →+* E) {n : ℕ} (A B : Matrix (Fin n) (Fin n) E) :
    cT σ (A + B) = cT σ A + cT σ B := by
  unfold cT; rw [Matrix.map_add _ (map_add σ), Matrix.transpose_add]

theorem cT_sub' {E : Type} [Field E] (σ : E →+* E) {n : ℕ} (A B : Matrix (Fin n) (Fin n) E) :
    cT σ (A - B) = cT σ A - cT σ B := by
  unfold cT; rw [Matrix.map_sub _ (map_sub σ), Matrix.transpose_sub]

theorem cayley_mem_UJ {E : Type} [Field E] (σ : E →+* E) {n : ℕ} (J S : Matrix (Fin n) (Fin n) E) :
    J.det ≠ 0 → cT σ S * J + J * S = 0 → (1 - S).det ≠ 0 →
    ∃ γ : GL (Fin n) E, γ ∈ UJ σ J ∧ (γ : Matrix (Fin n) (Fin n) E) = (1 + S) * (1 - S)⁻¹ := by
  intro hJ hS hd
  have hneg : cT σ S * J = -(J * S) := eq_neg_of_add_eq_zero_left hS
  have hBu : IsUnit (1 - S).det := isUnit_iff_ne_zero.mpr hd
  have hBBi : (1 - S) * (1 - S)⁻¹ = 1 := Matrix.mul_nonsing_inv _ hBu
  have h1 : cT σ (1 + S) * J = J * (1 - S) := by
    rw [cT_add', cT_one, Matrix.add_mul, Matrix.one_mul, hneg, Matrix.mul_sub, Matrix.mul_one, sub_eq_add_neg]
  have h2 : J * (1 + S) = cT σ (1 - S) * J := by
    rw [cT_sub', cT_one, Matrix.sub_mul, Matrix.one_mul, hneg, Matrix.mul_add, Matrix.mul_one, sub_neg_eq_add]
  have hc : (1 - S) * (1 + S) = (1 + S) * (1 - S) := by
    rw [Matrix.sub_mul, Matrix.mul_add, Matrix.mul_add, Matrix.add_mul, Matrix.mul_sub, Matrix.mul_sub]
    simp only [Matrix.one_mul, Matrix.mul_one]; abel
  have key : cT σ ((1 + S) * (1 - S)⁻¹) * J * ((1 + S) * (1 - S)⁻¹) = J := by
    rw [cT_mul]
    calc cT σ (1 - S)⁻¹ * cT σ (1 + S) * J * ((1 + S) * (1 - S)⁻¹)
        = cT σ (1 - S)⁻¹ * (cT σ (1 + S) * J) * (1 + S) * (1 - S)⁻¹ := by
          simp only [Matrix.mul_assoc]
      _ = cT σ (1 - S)⁻¹ * J * ((1 - S) * (1 + S)) * (1 - S)⁻¹ := by
          rw [h1]; simp only [Matrix.mul_assoc]
      _ = cT σ (1 - S)⁻¹ * (J * (1 + S)) * ((1 - S) * (1 - S)⁻¹) := by
          rw [hc]; simp only [Matrix.mul_assoc]
      _ = J := by
          rw [h2, hBBi, Matrix.mul_one, ← Matrix.mul_assoc, ← cT_mul, hBBi, cT_one, Matrix.one_mul]
  have hdet : ((1 + S) * (1 - S)⁻¹).det ≠ 0 := by
    intro h0
    have := congrArg Matrix.det key
    rw [Matrix.det_mul, h0, mul_zero] at this
    exact hJ this.symm
  refine ⟨Matrix.nonsingInvUnit _ (isUnit_iff_ne_zero.mpr hdet), ?_, rfl⟩
  show cT σ ((1 + S) * (1 - S)⁻¹) * J * ((1 + S) * (1 - S)⁻¹) = J
  exact key

end GlobalTheory.CayleyUnitary
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CcSubst
section
open Polynomial

namespace GlobalTheory.PicDiv.DeformZerosHasse

variable {k J I : Type} [Field k] [Fintype J] [Fintype I]

noncomputable def sys (N : ℕ) (ξ : J → PowerSeries k) (s : I → J → PowerSeries k)
    (x : J ⊕ I → PowerSeries k) : Option (I × Fin N) → PowerSeries k
  | none => ∑ j, x (Sum.inl j) * ξ j
  | some (i, l) => ∑ j, x (Sum.inl j) *
      ((GlobalTheory.PicDiv.hasse l.1 (s i j)).subst (x (Sum.inr i)) : PowerSeries k)

noncomputable def linFun (N : ℕ) (ξ : J → PowerSeries k) (s : I → J → PowerSeries k) (y₀ : J → k)
    (v : J ⊕ I → k) : Option (I × Fin N) → k
  | none => ∑ j, v (Sum.inl j) * PowerSeries.constantCoeff (ξ j)
  | some (i, l) => ∑ j, v (Sum.inl j) *
        PowerSeries.constantCoeff (GlobalTheory.PicDiv.hasse l.1 (s i j))
      + v (Sum.inr i) * ∑ j, y₀ j * PowerSeries.coeff 1 (GlobalTheory.PicDiv.hasse l.1 (s i j))

noncomputable def lin (N : ℕ) (ξ : J → PowerSeries k) (s : I → J → PowerSeries k) (y₀ : J → k) :
    (J ⊕ I → k) →ₗ[k] (Option (I × Fin N) → k) where
  toFun := linFun N ξ s y₀
  map_add' v w := by
    funext e; rcases e with _ | ⟨i, l⟩ <;> simp [linFun, add_mul, Finset.sum_add_distrib] <;> ring
  map_smul' c v := by
    funext e; rcases e with _ | ⟨i, l⟩ <;> simp [linFun, Finset.mul_sum, mul_assoc, mul_add]

lemma cc_subst (φ a : PowerSeries k) (ha : PowerSeries.constantCoeff a = 0) :
    PowerSeries.constantCoeff (φ.subst a : PowerSeries k) = PowerSeries.constantCoeff φ :=
  (GlobalTheory.taylor_subst_first_order k φ a 0 1 le_rfl ha).1

end GlobalTheory.PicDiv.DeformZerosHasse

namespace GlobalTheory.PicDiv.DeformZerosHasse

variable {k : Type} [Field k]

lemma dvd_step {m : ℕ} (hm : 1 ≤ m) (y g S S' : PowerSeries k) (y0 c A : k)
    (hy : PowerSeries.constantCoeff y = y0) (hS : PowerSeries.constantCoeff S = A)
    (hT : (PowerSeries.X : PowerSeries k) ^ (m + 1) ∣
      S' - S - PowerSeries.X ^ m * PowerSeries.C c) :
    (PowerSeries.X : PowerSeries k) ^ (m + 1) ∣
      (y + PowerSeries.X ^ m * g) * S' - y * S
        - PowerSeries.X ^ m * PowerSeries.C (PowerSeries.constantCoeff g * A + y0 * c) := by
  obtain ⟨r, hr⟩ := hT
  have hS' : S' = S + PowerSeries.X ^ m * PowerSeries.C c + PowerSeries.X ^ (m + 1) * r := by
    linear_combination hr
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, by omega⟩
  have heq : (y + PowerSeries.X ^ (n + 1) * g) * S' - y * S
      - PowerSeries.X ^ (n + 1) * PowerSeries.C (PowerSeries.constantCoeff g * A + y0 * c)
      = PowerSeries.X ^ (n + 1) * (y * PowerSeries.C c - PowerSeries.C (y0 * c)
          + (g * S - PowerSeries.C (PowerSeries.constantCoeff g * A)))
        + PowerSeries.X ^ (n + 1 + 1) * (y * r + PowerSeries.X ^ n *
          (g * PowerSeries.C c + PowerSeries.X * g * r)) := by
    rw [hS', map_add]; ring
  rw [heq]
  refine dvd_add ?_ (dvd_mul_right _ _)
  rw [pow_succ]
  refine mul_dvd_mul_left _ ?_
  rw [PowerSeries.X_dvd_iff]
  simp [hy, hS]

end GlobalTheory.PicDiv.DeformZerosHasse

namespace GlobalTheory.PicDiv.DeformZerosHasse

theorem deform : ∀ (k J I : Type) [Field k] [Fintype J] [Fintype I] (N : ℕ) (ξ : J → PowerSeries k) (s : I → J → PowerSeries k) (y₀ : J → k), 1 ≤ N → (N : k) ≠ 0 →
 ∑ j, y₀ j * PowerSeries.constantCoeff (ξ j) = 0 →
 (∀ i, ∀ l < N, ∑ j, y₀ j * PowerSeries.coeff l (s i j) = 0) → (∀ i, ∑ j, y₀ j * PowerSeries.coeff N (s i j) ≠ 0) →
 (∀ (e₀ : k) (e : I → ℕ → k), ∃ h : J → k, ∑ j, h j * PowerSeries.constantCoeff (ξ j) = e₀ ∧ ∀ i, ∀ l, l + 1 < N → ∑ j, h j * PowerSeries.coeff l (s i j) = e i l) →
 ∃ (y : J → PowerSeries k) (a : I → PowerSeries k), (∀ j, PowerSeries.constantCoeff (y j) = y₀ j) ∧ (∀ i, PowerSeries.constantCoeff (a i) = 0) ∧
   ∑ j, y j * ξ j = 0 ∧ ∀ i, ∀ l < N, ∑ j, y j * ((GlobalTheory.PicDiv.hasse l (s i j)).subst (a i) : PowerSeries k) = 0 := by
  intro k J I _ _ _ N ξ s y₀ hN hNk h0 hlow hN' hsurj
  have hA : ∀ (f : PowerSeries k) (l : ℕ), PowerSeries.constantCoeff (GlobalTheory.PicDiv.hasse l f)
      = PowerSeries.coeff l f := fun f l => GlobalTheory.PicDiv.constantCoeff_hasse l f
  have hB : ∀ (f : PowerSeries k) (l : ℕ), PowerSeries.coeff 1 (GlobalTheory.PicDiv.hasse l f)
      = ((l + 1 : ℕ) : k) * PowerSeries.coeff (l + 1) f := fun f l => GlobalTheory.PicDiv.coeff_one_hasse l f
  have hsur : Function.Surjective (lin N ξ s y₀) := by
    intro w
    obtain ⟨hv, hv0, hvl⟩ := hsurj (w none)
      (fun i l => if hl : l < N then w (some (i, ⟨l, hl⟩)) else 0)
    have hN1 : N - 1 < N := by omega
    have hS : ∀ i, ∑ j, y₀ j * PowerSeries.coeff 1 (GlobalTheory.PicDiv.hasse (N - 1) (s i j)) ≠ 0 := by
      intro i
      simp only [hB]
      have e1 : N - 1 + 1 = N := by omega
      rw [e1]
      calc ∑ j, y₀ j * (((N : ℕ) : k) * PowerSeries.coeff N (s i j))
          = ((N : ℕ) : k) * ∑ j, y₀ j * PowerSeries.coeff N (s i j) := by
            rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun j _ => by ring
        _ ≠ 0 := mul_ne_zero hNk (hN' i)
    refine ⟨Sum.elim hv (fun i => (w (some (i, ⟨N - 1, hN1⟩)) - ∑ j, hv j *
        PowerSeries.constantCoeff (GlobalTheory.PicDiv.hasse (N - 1) (s i j))) /
        ∑ j, y₀ j * PowerSeries.coeff 1 (GlobalTheory.PicDiv.hasse (N - 1) (s i j))), ?_⟩
    funext e
    rcases e with _ | ⟨i, l⟩
    · simpa [lin, linFun] using hv0
    · simp only [lin, linFun, LinearMap.coe_mk, AddHom.coe_mk, Sum.elim_inl, Sum.elim_inr]
      rcases Nat.lt_or_ge (l.1 + 1) N with hl | hl
      · have h1 : ∑ j, hv j * PowerSeries.constantCoeff (GlobalTheory.PicDiv.hasse l.1 (s i j))
            = w (some (i, l)) := by
          simp only [hA]
          have := hvl i l.1 hl
          rw [dif_pos l.2] at this
          exact this
        have h2 : ∑ j, y₀ j * PowerSeries.coeff 1 (GlobalTheory.PicDiv.hasse l.1 (s i j)) = 0 := by
          simp only [hB]
          calc ∑ j, y₀ j * (((l.1 + 1 : ℕ) : k) * PowerSeries.coeff (l.1 + 1) (s i j))
              = ((l.1 + 1 : ℕ) : k) * ∑ j, y₀ j * PowerSeries.coeff (l.1 + 1) (s i j) := by
                rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun j _ => by ring
            _ = 0 := by rw [hlow i (l.1 + 1) (by omega), mul_zero]
        rw [h1, h2, mul_zero, add_zero]
      · have hl' : l = ⟨N - 1, hN1⟩ := Fin.ext (by simp; omega)
        subst hl'
        rw [div_mul_cancel₀ _ (hS i)]
        ring
  have hbase : ∀ e, PowerSeries.constantCoeff
      (sys N ξ s (fun i => PowerSeries.C (Sum.elim y₀ 0 i)) e) = 0 := by
    intro e
    rcases e with _ | ⟨i, l⟩
    · simp [sys, map_sum, h0]
    · simp only [sys, map_sum, map_mul, PowerSeries.constantCoeff_C, Sum.elim_inl, Sum.elim_inr]
      have h' : ∀ j, PowerSeries.constantCoeff ((GlobalTheory.PicDiv.hasse l.1 (s i j)).subst
          (PowerSeries.C ((0 : I → k) i)) : PowerSeries k) = PowerSeries.coeff l.1 (s i j) := by
        intro j; rw [cc_subst _ _ (by simp), hA]
      simp only [h']
      exact hlow i l.1 l.2
  have htay : ∀ (x h : J ⊕ I → PowerSeries k) (m : ℕ), 1 ≤ m →
      (∀ i, PowerSeries.constantCoeff (x i) = Sum.elim y₀ 0 i) → ∀ e,
      (PowerSeries.X : PowerSeries k) ^ (m + 1) ∣ sys N ξ s (fun i => x i + PowerSeries.X ^ m * h i) e
        - sys N ξ s x e - PowerSeries.X ^ m *
          PowerSeries.C (lin N ξ s y₀ (fun i => PowerSeries.constantCoeff (h i)) e) := by

    intro x h m hm hx0 e
    rcases e with _ | ⟨i, l⟩
    · simp only [sys, lin, linFun, LinearMap.coe_mk, AddHom.coe_mk, Sum.elim_inl]
      have heq : ∑ j, (x (Sum.inl j) + PowerSeries.X ^ m * h (Sum.inl j)) * ξ j - ∑ j, x (Sum.inl j) * ξ j
          - PowerSeries.X ^ m * PowerSeries.C (∑ j, PowerSeries.constantCoeff (h (Sum.inl j)) * PowerSeries.constantCoeff (ξ j))
          = PowerSeries.X ^ m * (∑ j, h (Sum.inl j) * ξ j - PowerSeries.C (∑ j, PowerSeries.constantCoeff (h (Sum.inl j)) * PowerSeries.constantCoeff (ξ j))) := by
        rw [mul_sub, Finset.mul_sum]; simp only [add_mul, Finset.sum_add_distrib, mul_assoc]; ring
      rw [heq, pow_succ]
      refine mul_dvd_mul_left _ ?_
      rw [PowerSeries.X_dvd_iff]
      simp [map_sum]
    · simp only [sys, lin, linFun, LinearMap.coe_mk, AddHom.coe_mk]
      set a := x (Sum.inr i)
      set b := h (Sum.inr i)
      have ha : PowerSeries.constantCoeff a = 0 := by simpa using hx0 (Sum.inr i)
      have key : ∀ j, (PowerSeries.X : PowerSeries k) ^ (m + 1) ∣
          (x (Sum.inl j) + PowerSeries.X ^ m * h (Sum.inl j)) *
            ((GlobalTheory.PicDiv.hasse l.1 (s i j)).subst (a + PowerSeries.X ^ m * b) : PowerSeries k)
          - x (Sum.inl j) * ((GlobalTheory.PicDiv.hasse l.1 (s i j)).subst a : PowerSeries k)
          - PowerSeries.X ^ m * PowerSeries.C (PowerSeries.constantCoeff (h (Sum.inl j)) *
              PowerSeries.constantCoeff (GlobalTheory.PicDiv.hasse l.1 (s i j))
              + y₀ j * (PowerSeries.constantCoeff b * PowerSeries.coeff 1 (GlobalTheory.PicDiv.hasse l.1 (s i j)))) := by
        intro j
        have T := GlobalTheory.taylor_subst_first_order k (GlobalTheory.PicDiv.hasse l.1 (s i j)) a b m hm ha
        exact dvd_step hm _ _ _ _ _ _ _ (by simpa using hx0 (Sum.inl j)) T.1 T.2
      have heq : ∑ j, (x (Sum.inl j) + PowerSeries.X ^ m * h (Sum.inl j)) *
            ((GlobalTheory.PicDiv.hasse l.1 (s i j)).subst (a + PowerSeries.X ^ m * b) : PowerSeries k)
          - ∑ j, x (Sum.inl j) * ((GlobalTheory.PicDiv.hasse l.1 (s i j)).subst a : PowerSeries k)
          - PowerSeries.X ^ m * PowerSeries.C (∑ j, PowerSeries.constantCoeff (h (Sum.inl j)) *
              PowerSeries.constantCoeff (GlobalTheory.PicDiv.hasse l.1 (s i j))
              + PowerSeries.constantCoeff b * ∑ j, y₀ j * PowerSeries.coeff 1 (GlobalTheory.PicDiv.hasse l.1 (s i j)))
          = ∑ j, ((x (Sum.inl j) + PowerSeries.X ^ m * h (Sum.inl j)) *
            ((GlobalTheory.PicDiv.hasse l.1 (s i j)).subst (a + PowerSeries.X ^ m * b) : PowerSeries k)
          - x (Sum.inl j) * ((GlobalTheory.PicDiv.hasse l.1 (s i j)).subst a : PowerSeries k)
          - PowerSeries.X ^ m * PowerSeries.C (PowerSeries.constantCoeff (h (Sum.inl j)) *
              PowerSeries.constantCoeff (GlobalTheory.PicDiv.hasse l.1 (s i j))
              + y₀ j * (PowerSeries.constantCoeff b * PowerSeries.coeff 1 (GlobalTheory.PicDiv.hasse l.1 (s i j))))) := by
        rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, ← map_sum,
          Finset.sum_add_distrib, Finset.mul_sum (a := PowerSeries.constantCoeff b)]
        congr 4
        refine Finset.sum_congr rfl fun j _ => by ring
      rw [heq]
      exact Finset.dvd_sum fun j _ => key j
  obtain ⟨x, hx0, hx⟩ := GlobalTheory.newton_powerSeries_target k (J ⊕ I) (Option (I × Fin N)) (sys N ξ s) (Sum.elim y₀ 0)
    (lin N ξ s y₀) hsur hbase htay
  refine ⟨fun j => x (Sum.inl j), fun i => x (Sum.inr i), fun j => by simpa using hx0 (Sum.inl j),
    fun i => by simpa using hx0 (Sum.inr i), hx none, ?_⟩
  intro i l hl
  exact hx (some (i, ⟨l, hl⟩))

end GlobalTheory.PicDiv.DeformZerosHasse
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechComplexDirectLimit
section
open CategoryTheory Limits Filter

namespace GlobalTheory

namespace CubeColim

variable {ι : Type} [LinearOrder ι] [Fintype ι]

theorem termMap_comp {X Y Z : Cube.{0} ι ℤ} (f : X ⟶ Y) (g : Y ⟶ Z) (p : ℕ)
    (x : Cube.Term X p) :
    Cube.termMap (f ≫ g) p x = Cube.termMap g p (Cube.termMap f p x) := rfl

theorem trans_congr {A : ℕ → Cube.{0} ι ℤ} (μ : ∀ (j c d : ℕ), c + j = d → (A c ⟶ A d))
    {j j' c d : ℕ} (h : c + j = d) (h' : c + j' = d) (e : j = j') : μ j c d h = μ j' c d h' := by
  subst e; rfl

theorem nonempty_of_card {m : ℕ} (hm : 0 < m) (s : {s : Finset ι // s.card = m}) :
    s.1.Nonempty :=
  Finset.card_pos.1 (by rw [s.2]; exact hm)

theorem exists_lift {A : ℕ → Cube.{0} ι ℤ} {B : Cube.{0} ι ℤ}
    (μ : ∀ (j c d : ℕ), c + j = d → (A c ⟶ A d)) (ρ : ∀ c, A c ⟶ B)
    (h1 : ∀ j c d h, μ j c d h ≫ ρ d = ρ c)
    (h3 : ∀ s : Finset ι, s.Nonempty → ∀ b : B.obj s, ∃ c, ∃ a : (A c).obj s, (ρ c).app s a = b)
    {m : ℕ} (hm : 0 < m) (z : Cube.Term B m) :
    ∃ C, ∃ a : Cube.Term (A C) m, Cube.termMap (ρ C) m a = z := by
  choose c a ha using fun s : {s : Finset ι // s.card = m} => h3 s.1 (nonempty_of_card hm s) (z s)
  have hc : ∀ s, c s + (Finset.univ.sup c - c s) = Finset.univ.sup c := fun s => by
    have := Finset.le_sup (f := c) (Finset.mem_univ s); omega
  refine ⟨Finset.univ.sup c,
    fun s => ((μ _ (c s) _ (hc s)).app s.1).hom (a s), funext fun s => ?_⟩
  have e := congrArg (fun f => (f.app s.1).hom (a s)) (h1 _ (c s) _ (hc s))
  simp only [NatTrans.comp_app, ModuleCat.hom_comp, LinearMap.comp_apply] at e
  rw [Cube.termMap_apply, e]
  exact ha s

theorem exists_kill {A : ℕ → Cube.{0} ι ℤ} {B : Cube.{0} ι ℤ}
    (μ : ∀ (j c d : ℕ), c + j = d → (A c ⟶ A d)) (ρ : ∀ c, A c ⟶ B)
    (h2 : ∀ (j j' c d e : ℕ) (h : c + j = d) (h' : d + j' = e) (h'' : c + (j + j') = e),
      μ j c d h ≫ μ j' d e h' = μ (j + j') c e h'')
    (h4 : ∀ s : Finset ι, s.Nonempty → ∀ c (a : (A c).obj s), (ρ c).app s a = 0 →
      ∃ j, (μ j c (c + j) rfl).app s a = 0)
    {m : ℕ} (hm : 0 < m) (c : ℕ) (x : Cube.Term (A c) m) (hx : Cube.termMap (ρ c) m x = 0) :
    ∃ J, Cube.termMap (μ J c (c + J) rfl) m x = 0 := by
  choose j hj using fun s : {s : Finset ι // s.card = m} =>
    h4 s.1 (nonempty_of_card hm s) c (x s) (congrFun hx s)
  refine ⟨Finset.univ.sup j, funext fun s => ?_⟩
  have hle := Finset.le_sup (f := j) (Finset.mem_univ s)
  have hcomp := h2 (j s) (Finset.univ.sup j - j s) c (c + j s) (c + Finset.univ.sup j) rfl
    (by omega) (by omega)
  have e : μ (Finset.univ.sup j) c (c + Finset.univ.sup j) rfl =
      μ (j s + (Finset.univ.sup j - j s)) c (c + Finset.univ.sup j) (by omega) :=
    trans_congr μ _ _ (by omega)
  rw [Cube.termMap_apply, e, ← hcomp]
  simp only [NatTrans.comp_app, ModuleCat.hom_comp, LinearMap.comp_apply]
  have e : ((μ (j s) c (c + j s) rfl).app s.1).hom (x s) = 0 := hj s
  rw [e, map_zero]
  rfl

theorem exists_cocycle_lift {A : ℕ → Cube.{0} ι ℤ} {B : Cube.{0} ι ℤ}
    (μ : ∀ (j c d : ℕ), c + j = d → (A c ⟶ A d)) (ρ : ∀ c, A c ⟶ B)
    (h1 : ∀ j c d h, μ j c d h ≫ ρ d = ρ c)
    (h2 : ∀ (j j' c d e : ℕ) (h : c + j = d) (h' : d + j' = e) (h'' : c + (j + j') = e),
      μ j c d h ≫ μ j' d e h' = μ (j + j') c e h'')
    (h3 : ∀ s : Finset ι, s.Nonempty → ∀ b : B.obj s, ∃ c, ∃ a : (A c).obj s, (ρ c).app s a = b)
    (h4 : ∀ s : Finset ι, s.Nonempty → ∀ c (a : (A c).obj s), (ρ c).app s a = 0 →
      ∃ j, (μ j c (c + j) rfl).app s a = 0)
    {m : ℕ} (hm : 0 < m) (z : Cube.Term B m) (hz : Cube.d B m z = 0) :
    ∃ C, ∀ c, C ≤ c → ∃ a : Cube.Term (A c) m,
      Cube.termMap (ρ c) m a = z ∧ Cube.d (A c) m a = 0 := by
  obtain ⟨C₀, a, ha⟩ := exists_lift μ ρ h1 h3 hm z
  have hda : Cube.termMap (ρ C₀) (m + 1) (Cube.d (A C₀) m a) = 0 := by
    rw [Cube.termMap_d, ha, hz]
  obtain ⟨J, hJ⟩ := exists_kill μ ρ h2 h4 (Nat.succ_pos m) C₀ _ hda
  refine ⟨C₀ + J, fun c hc => ⟨Cube.termMap (μ (c - C₀) C₀ c (by omega)) m a, ?_, ?_⟩⟩
  · rw [← termMap_comp, h1, ha]
  · rw [← Cube.termMap_d]
    have e : μ (c - C₀) C₀ c (by omega) =
        μ J C₀ (C₀ + J) rfl ≫ μ (c - C₀ - J) (C₀ + J) c (by omega) := by
      rw [h2 J (c - C₀ - J) C₀ (C₀ + J) c rfl (by omega) (by omega)]
      exact trans_congr μ _ _ (by omega)
    rw [e, termMap_comp, hJ, map_zero]

end CubeColim

theorem cechComplex_homology_isZero_of_colimit :
    ∀ {ι : Type} [LinearOrder ι] [Fintype ι] (A : ℕ → Cube.{0} ι ℤ) (B : Cube.{0} ι ℤ) (μ : ∀ (j c d : ℕ), c + j = d → (A c ⟶ A d)) (ρ : ∀ c, A c ⟶ B), (∀ j c d h, μ j c d h ≫ ρ d = ρ c) → (∀ (j j' c d e : ℕ) (h : c + j = d) (h' : d + j' = e) (h'' : c + (j + j') = e), μ j c d h ≫ μ j' d e h' = μ (j + j') c e h'') → (∀ s : Finset ι, s.Nonempty → ∀ b : B.obj s, ∃ c, ∃ a : (A c).obj s, (ρ c).app s a = b) → (∀ s : Finset ι, s.Nonempty → ∀ c (a : (A c).obj s), (ρ c).app s a = 0 → ∃ j, (μ j c (c + j) rfl).app s a = 0) → ∀ n : ℕ, (∀ᶠ c in atTop, IsZero ((cechComplex (A c)).homology n)) → IsZero ((cechComplex B).homology n) := by
  intro ι _ _ A B μ ρ h1 h2 h3 h4 n hn
  obtain ⟨N, hN⟩ := eventually_atTop.1 hn
  rw [← HomologicalComplex.exactAt_iff_isZero_homology]
  cases n with
  | zero =>
    rw [cochainComplex_exactAt_zero_iff, cechComplex_d B 0]
    change Function.Injective (Cube.d B 1)
    rw [injective_iff_map_eq_zero]
    intro z hz
    obtain ⟨C, hC⟩ := CubeColim.exists_cocycle_lift μ ρ h1 h2 h3 h4 one_pos z hz
    obtain ⟨a, ha, hda⟩ := hC (max C N) (le_max_left _ _)
    have hex := (HomologicalComplex.exactAt_iff_isZero_homology _ _).2
      (hN (max C N) (le_max_right _ _))
    rw [cochainComplex_exactAt_zero_iff, cechComplex_d _ 0] at hex
    change Function.Injective (Cube.d (A (max C N)) 1) at hex
    rw [injective_iff_map_eq_zero] at hex
    rw [← ha, hex a hda, map_zero]
  | succ p =>
    rw [cechComplex_exactAt_succ_iff]
    intro z
    refine ⟨fun hz => ?_, ?_⟩
    · obtain ⟨C, hC⟩ := CubeColim.exists_cocycle_lift μ ρ h1 h2 h3 h4 (m := p + 2) (by omega) z hz
      obtain ⟨a, ha, hda⟩ := hC (max C N) (le_max_left _ _)
      have hex := (HomologicalComplex.exactAt_iff_isZero_homology _ _).2
        (hN (max C N) (le_max_right _ _))
      rw [cechComplex_exactAt_succ_iff] at hex
      obtain ⟨y, hy⟩ := (hex a).1 hda
      exact ⟨Cube.termMap (ρ _) (p + 1) y, by rw [← Cube.termMap_d, hy, ha]⟩
    · rintro ⟨y, rfl⟩
      exact Cube.d_d B (p + 1) y

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CenOrderFinite
section
open scoped TensorProduct
open GlobalTheory.LKInvGood

namespace GlobalTheory

theorem cenOrder_finite : ∀ (F : Type) [Field F] [NumberField F] (ℓ : ℕ) [Fact ℓ.Prime],
    Module.Finite ℤ_[ℓ] (cenOrder ℓ F) := by
  intro F _ _ ℓ _
  classical
  let f : NumberField.RingOfIntegers F → ℚ_[ℓ] ⊗[ℚ] F := fun a => (1 : ℚ_[ℓ]) ⊗ₜ[ℚ] (a : F)
  obtain ⟨s, hs⟩ := (inferInstance : Module.Finite ℤ (NumberField.RingOfIntegers F)).fg_top
  have hint : ∀ x ∈ (f '' (s : Set (NumberField.RingOfIntegers F))), IsIntegral ℤ_[ℓ] x := by
    rintro _ ⟨a, -, rfl⟩
    have h1 : IsIntegral ℤ ((a : F)) := NumberField.RingOfIntegers.isIntegral_coe a
    have h2 : IsIntegral ℤ (f a) := by
      have := h1.map ((Algebra.TensorProduct.includeRight : F →ₐ[ℚ] ℚ_[ℓ] ⊗[ℚ] F).restrictScalars ℤ)
      simpa [f] using this
    exact h2.tower_top
  have hfin : Module.Finite ℤ_[ℓ] (Algebra.adjoin ℤ_[ℓ] (f '' (s : Set (NumberField.RingOfIntegers F)))) :=
    Algebra.finite_adjoin_of_finite_of_isIntegral ((s.finite_toSet).image f) hint
  have heq : cenOrder ℓ F = Algebra.adjoin ℤ_[ℓ] (f '' (s : Set (NumberField.RingOfIntegers F))) := by
    apply le_antisymm
    · apply Algebra.adjoin_le
      rintro _ ⟨a, rfl⟩
      let A := Algebra.adjoin ℤ_[ℓ] (f '' (s : Set (NumberField.RingOfIntegers F)))
      let N : Submodule ℤ (NumberField.RingOfIntegers F) :=
        { carrier := {x | f x ∈ A}
          add_mem' := by
            intro x y hx hy
            simp only [Set.mem_setOf_eq, f, map_add, TensorProduct.tmul_add] at hx hy ⊢
            exact A.add_mem hx hy
          zero_mem' := by
            simp only [Set.mem_setOf_eq, f, map_zero, TensorProduct.tmul_zero]
            exact A.zero_mem
          smul_mem' := by
            intro c x hx
            simp only [Set.mem_setOf_eq, f, zsmul_eq_mul, map_mul, map_intCast] at hx ⊢
            have : (1 : ℚ_[ℓ]) ⊗ₜ[ℚ] ((c : F) * (x : F)) = c • ((1 : ℚ_[ℓ]) ⊗ₜ[ℚ] (x : F)) := by
              rw [← zsmul_eq_mul, TensorProduct.tmul_smul]
            rw [this]
            exact A.toSubring.zsmul_mem hx c }
      have hsN : (s : Set _) ⊆ N := fun x hx => show f x ∈ A from Algebra.subset_adjoin ⟨x, hx, rfl⟩
      have : a ∈ N := by
        have := Submodule.span_le.mpr hsN
        rw [hs] at this
        exact this Submodule.mem_top
      exact this
    · apply Algebra.adjoin_mono
      rintro _ ⟨a, -, rfl⟩
      exact ⟨a, rfl⟩
  rw [heq]
  exact hfin

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClosedCoverAffineNbhdMapsIntoAffineStatement
section
open AlgebraicGeometry CategoryTheory Limits
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_affine_nbhd_preimage_le_of_closed_cover : ∀ (Y Y₁ Y₂ X : Scheme.{0}) (j₁ : Y₁ ⟶ Y) (j₂ : Y₂ ⟶ Y) [IsClosedImmersion j₁] [IsClosedImmersion j₂] (a₁ : Y₁ ⟶ X) (a₂ : Y₂ ⟶ X), (∀ y : Y, (∃ y₁, j₁ y₁ = y) ∨ ∃ y₂, j₂ y₂ = y) → (∀ (y₁ : Y₁) (y₂ : Y₂), j₁ y₁ = j₂ y₂ → a₁ y₁ = a₂ y₂) → ∀ y : Y, ∃ (W : Y.Opens) (U : X.affineOpens), IsAffineOpen W ∧ y ∈ W ∧ j₁ ⁻¹ᵁ W ≤ a₁ ⁻¹ᵁ U.1 ∧ j₂ ⁻¹ᵁ W ≤ a₂ ⁻¹ᵁ U.1 := by
  first | exact @GlobalTheory.closedCover_affine_nbhd_maps_into_affine | exact GlobalTheory.closedCover_affine_nbhd_maps_into_affine | (intros; apply GlobalTheory.closedCover_affine_nbhd_maps_into_affine <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmAlgCharEqArgMulAbsStatement
section
open NumberField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cm_algChar_eq_arg_mul_abs : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : (E →+* ℂ) → ℤ) (w0 : ℤ),
    (∀ φ, n φ + n (NumberField.ComplexEmbedding.conjugate φ) = w0) → ∀ k : E, k ≠ 0 →
    (∏ w : InfinitePlace E, (w.embedding k / ((‖w.embedding k‖ : ℝ) : ℂ)) ^ (2 * n w.embedding - w0)) *
      ∏ φ : E →+* ℂ, ((‖φ k‖ : ℝ) : ℂ) ^ ((((w0 : ℝ) / 2 : ℝ)) : ℂ) = ∏ φ : E →+* ℂ, φ k ^ n φ := by
  first | exact @GlobalTheory.Div.CMAlgChar.algChar_eq_arg_mul_abs | exact GlobalTheory.Div.CMAlgChar.algChar_eq_arg_mul_abs | (intros; apply GlobalTheory.Div.CMAlgChar.algChar_eq_arg_mul_abs <;> assumption)
end

