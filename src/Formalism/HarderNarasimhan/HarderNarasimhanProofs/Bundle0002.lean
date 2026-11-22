import Formalism.HarderNarasimhan.Bundle0001
import Formalism.HarderNarasimhan.HarderNarasimhanProofs.DegSupermodZ
import Mathlib
import Formalism.HarderNarasimhan.Bundle0002
import Formalism.LatticeSlopes.ExistsSaturatedSlopeEqMuMax
import Formalism.CorankShare.CorankShareProofs.SumNormSqLeHilbertSchmidt

-- bundled from Formalism.HarderNarasimhan.HarderNarasimhanProofs.DegSupermod
section
open Module Submodule

noncomputable section

namespace Formalism.HN

section

variable {R V E : Type*} [Ring R] [AddCommGroup V] [Module R V] [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (ρ : V →+ E)

theorem degSupermod_mem_zl (N : Submodule R V) (y : E) :
    y ∈ zl ρ N ↔ ∃ x ∈ N, ρ x = y := Iff.rfl

theorem degSupermod_zl_mono {A B : Submodule R V} (h : A ≤ B) : zl ρ A ≤ zl ρ B := by
  intro y hy
  obtain ⟨x, hx, rfl⟩ := (degSupermod_mem_zl ρ A y).mp hy
  exact (degSupermod_mem_zl ρ B _).mpr ⟨x, h hx, rfl⟩

theorem degSupermod_zl_sup (A B : Submodule R V) : zl ρ (A ⊔ B) = zl ρ A ⊔ zl ρ B := by
  simp only [zl, Submodule.sup_toAddSubgroup, AddSubgroup.map_sup]
  first
    | exact SupHomClass.map_sup AddSubgroup.toIntSubmodule _ _
    | (ext y; simp [Submodule.mem_sup, AddSubgroup.mem_sup])

theorem degSupermod_zl_inf {L A B : Submodule R V} (hinj : Set.InjOn ρ (L : Set V))
    (hA : A ≤ L) (hB : B ≤ L) : zl ρ (A ⊓ B) = zl ρ A ⊓ zl ρ B := by
  refine le_antisymm (le_inf (degSupermod_zl_mono ρ inf_le_left)
    (degSupermod_zl_mono ρ inf_le_right)) ?_
  rintro y ⟨hyA, hyB⟩
  obtain ⟨a, ha, rfl⟩ := (degSupermod_mem_zl ρ A y).mp hyA
  obtain ⟨b, hb, hba⟩ := (degSupermod_mem_zl ρ B _).mp hyB

  have hab : b = a := hinj (hB hb) (hA ha) hba
  subst hab
  exact (degSupermod_mem_zl ρ (A ⊓ B) _).mpr ⟨b, ⟨ha, hb⟩, rfl⟩

end

universe u v w in
theorem degSupermod_of (h : DegSupermodZ.{w}) : DegSupermod.{u, v, w} := by
  intro R V E _ _ _ _ _ _ ρ L A B hL hA hB
  haveI := hL.2
  have key := h E (zl ρ L) (zl ρ A) (zl ρ B) hL.2 (degSupermod_zl_mono ρ hA)
    (degSupermod_zl_mono ρ hB)
  rw [← degSupermod_zl_sup ρ A B, ← degSupermod_zl_inf ρ hL.1 hA hB] at key
  exact key

theorem degree_supermodular : DegSupermod := degSupermod_of degree_supermodular_integral

end Formalism.HN
end
end

-- bundled from Formalism.HarderNarasimhan.HarderNarasimhanProofs.FrameLinearAlgebraFirst
section
noncomputable section

namespace Formalism.HN

namespace PframeLA1

open Finset Module LinearMap Formalism.CorankShareLayerCake.FR Formalism.CorankShareLayerCake.FR.Pgsn2pfrla
open scoped InnerProductSpace

lemma final_real1 (D R w e ε η t X tW : ℝ) (hD : 0 < D) (hR : 0 < R) (he0 : 0 ≤ e) (he : e ≤ 1/4)
    (hε : 0 ≤ ε) (hw0 : 0 ≤ w) (hwD : w ≤ D) (ht : R * (1 - √e) ≤ t) (hX0 : 0 ≤ X)
    (hX : X ≤ η * t ^ 2 / D) (hlow : t / D * w - √w * √X ≤ tW)
    (hup : tW ≤ ε * R + R * √(ε * e)) : w ≤ (η + 4 * ε + 4 * √e) * D := by
  have hsw : √w ^ 2 = w := Real.sq_sqrt hw0
  have hsX : √X ^ 2 = X := Real.sq_sqrt hX0
  have hse0 : 0 ≤ √e := Real.sqrt_nonneg e
  have hse : √e ≤ 1 / 2 := by
    rw [show (1 / 2 : ℝ) = √((1 / 2) ^ 2) by rw [Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt (by linarith)
  have hRt : R ≤ 2 * t := by nlinarith [mul_le_mul_of_nonneg_left hse hR.le]
  have htpos : 0 < t := by linarith
  have hη : 0 ≤ η := by
    have h1 : 0 ≤ η * t ^ 2 / D := le_trans hX0 hX
    have h2 : 0 ≤ η * t ^ 2 := by
      have := mul_nonneg h1 hD.le
      rwa [div_mul_cancel₀ _ hD.ne'] at this
    by_contra hneg
    push_neg at hneg
    have : η * t ^ 2 < 0 := mul_neg_of_neg_of_pos hneg (by positivity)
    linarith
  by_cases hε4 : 1 / 4 ≤ ε
  · nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ η + 4 * ε + 4 * √e - 1) hD.le]
  push_neg at hε4
  set q := √(ε * e) with hq
  have hq0 : 0 ≤ q := Real.sqrt_nonneg _
  have hqe : q ≤ √e := Real.sqrt_le_sqrt (by nlinarith)
  set y := D / t * √X with hy
  have hy2 : y ^ 2 ≤ η * D := by
    have h1 : y ^ 2 = D ^ 2 * X / t ^ 2 := by rw [hy, mul_pow, div_pow, hsX]; ring
    rw [h1, div_le_iff₀ (by positivity)]
    have h2 : X * D ≤ η * t ^ 2 := (le_div_iff₀ hD).mp hX
    nlinarith [mul_le_mul_of_nonneg_left h2 hD.le]
  have hyt : y * t = D * √X := by rw [hy]; field_simp
  have hDt : D * (t / D) = t := by field_simp
  have hkey : t * (w - √w * y) ≤ t * (2 * D * (ε + q)) := by
    have h1 : t / D * w - √w * √X ≤ R * (ε + q) := by linarith
    have h2 : t * w - D * (√w * √X) ≤ D * (R * (ε + q)) := by
      have := mul_le_mul_of_nonneg_left h1 hD.le
      have e1 : D * (t / D * w - √w * √X) = t * w - D * (√w * √X) := by
        linear_combination w * hDt
      linarith
    have h3 : D * (R * (ε + q)) ≤ D * (2 * t * (ε + q)) := by
      apply mul_le_mul_of_nonneg_left _ hD.le
      nlinarith
    have e2 : t * (√w * y) = D * (√w * √X) := by linear_combination √w * hyt
    nlinarith
  have hmain : w - √w * y ≤ 2 * D * (ε + q) := le_of_mul_le_mul_left hkey htpos
  have hamgm : √w * y ≤ (w + y ^ 2) / 2 := by nlinarith [sq_nonneg (√w - y)]
  nlinarith [mul_le_mul_of_nonneg_left hqe hD.le]

end PframeLA1

open Finset Module LinearMap Formalism.CorankShareLayerCake.FR Formalism.CorankShareLayerCake.FR.Pgsn2pfrla PframeLA1
open scoped InnerProductSpace

private lemma hs2_nonneg {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [FiniteDimensional ℂ E] [NormedAddCommGroup F] [InnerProductSpace ℂ F] [FiniteDimensional ℂ F]
    (A : E →ₗ[ℂ] F) : 0 ≤ hs2 A := by
  rw [hilbert_schmidt_eq_basis_sum A (stdOrthonormalBasis ℂ E)]
  exact Finset.sum_nonneg (fun m _ => sq_nonneg _)

theorem frame_linear_algebra_first : FrameLA1 := by
  intro ι _ V _ _ _ H _ _ _ B c Nτ e η ε hc hd hK he0 he hη hQ hN
  set W : Submodule ℂ H := (⨆ i, (Nτ i).map (B i))ᗮ with hW
  have hwD : (finrank ℂ W : ℝ) ≤ (finrank ℂ H : ℝ) := by exact_mod_cast Submodule.finrank_le W
  by_cases hD0 : finrank ℂ H = 0
  · have h0 : finrank ℂ W = 0 := by have := Submodule.finrank_le W; omega
    simp [h0, hD0]
  have hD : 0 < (finrank ℂ H : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hD0
  have hR : 0 < ∑ i, (finrank ℂ (V i) : ℝ) := by rw [← Nat.cast_sum]; exact_mod_cast hd
  have hnk : ∀ i, (finrank ℂ (Nτ i) : ℝ) ≤ finrank ℂ (V i) := fun i => by
    exact_mod_cast Submodule.finrank_le (Nτ i)
  have hKnn : 0 ≤ ∑ i, ((finrank ℂ (V i) : ℝ) - finrank ℂ (Nτ i)) :=
    Finset.sum_nonneg (fun i _ => sub_nonneg.mpr (hnk i))
  have hε : 0 ≤ ε := by
    by_contra h
    push_neg at h
    have : ε * ∑ i, (finrank ℂ (V i) : ℝ) < 0 := mul_neg_of_neg_of_pos h hR
    linarith

  have hfull : ∀ i, (finrank ℂ (V i) : ℝ) - √(finrank ℂ (V i) : ℝ) * √(hs2 (frK (c i) (B i) - LinearMap.id))
      ≤ c i * ∑ m, ‖B i (stdOrthonormalBasis ℂ (V i) m)‖ ^ 2 := by
    intro i
    have h := fam_bound (c i) (B i) (stdOrthonormalBasis ℂ (V i)).orthonormal
    simp only [Fintype.card_fin] at h
    have := (abs_le.mp h).1
    linarith
  have hCS1 : ∑ i, √(finrank ℂ (V i) : ℝ) * √(hs2 (frK (c i) (B i) - LinearMap.id))
      ≤ (∑ i, (finrank ℂ (V i) : ℝ)) * √e := by
    calc _ ≤ √(∑ i, (finrank ℂ (V i) : ℝ)) * √(∑ i, hs2 (frK (c i) (B i) - LinearMap.id)) :=
          Real.sum_sqrt_mul_sqrt_le Finset.univ (fun i => Nat.cast_nonneg _) (fun i => hs2_nonneg _)
      _ ≤ √(∑ i, (finrank ℂ (V i) : ℝ)) * √(e * ∑ i, (finrank ℂ (V i) : ℝ)) :=
          mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hK) (Real.sqrt_nonneg _)
      _ = (∑ i, (finrank ℂ (V i) : ℝ)) * √e := by
          rw [Real.sqrt_mul he0]
          have := Real.mul_self_sqrt hR.le
          linear_combination √e * this
  have ht : (∑ i, (finrank ℂ (V i) : ℝ)) * (1 - √e) ≤ (LinearMap.trace ℂ H (frQ c B)).re := by
    rw [tQ_eq c B]
    have h2 := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hfull i)
    rw [Finset.sum_sub_distrib] at h2
    nlinarith [hCS1]

  set b := stdOrthonormalBasis ℂ W with hb
  set g : Fin (finrank ℂ W) → H := fun l => (b l : H) with hgdef
  have hg : Orthonormal ℂ g := b.orthonormal.comp_linearIsometry W.subtypeₗᵢ
  set tW : ℝ := ∑ l, (⟪g l, frQ c B (g l)⟫_ℂ).re with htWdef
  have htW : tW = ∑ i, c i * ∑ l, ‖adjoint (B i) (g l)‖ ^ 2 := by
    rw [htWdef]
    simp only [re_inner_Q, Finset.mul_sum]
    exact Finset.sum_comm
  have hWi : ∀ i, c i * ∑ l, ‖adjoint (B i) (g l)‖ ^ 2 ≤
      ((finrank ℂ (V i) : ℝ) - finrank ℂ (Nτ i)) +
        √((finrank ℂ (V i) : ℝ) - finrank ℂ (Nτ i)) * √(hs2 (frK (c i) (B i) - LinearMap.id)) := by
    intro i
    have hperp : ∀ l, ∀ n ∈ Nτ i, ⟪B i n, g l⟫_ℂ = 0 := by
      intro l n hn
      have hmem : B i n ∈ ⨆ j, (Nτ j).map (B j) :=
        Submodule.mem_iSup_of_mem i (Submodule.mem_map_of_mem hn)
      exact (Submodule.mem_orthogonal _ _).mp (b l).2 _ hmem
    have h1 := W_upper (B i) (Nτ i) hg hperp
    have hf : Orthonormal ℂ (fun m => ((stdOrthonormalBasis ℂ (Nτ i)ᗮ m : (Nτ i)ᗮ) : V i)) :=
      (stdOrthonormalBasis ℂ (Nτ i)ᗮ).orthonormal.comp_linearIsometry (Nτ i)ᗮ.subtypeₗᵢ
    have h2 := fam_bound (c i) (B i) hf
    simp only [Fintype.card_fin] at h2
    have hk : (finrank ℂ (Nτ i)ᗮ : ℝ) = finrank ℂ (V i) - finrank ℂ (Nτ i) := by
      have := Submodule.finrank_add_finrank_orthogonal (Nτ i)
      rw [eq_sub_iff_add_eq]
      exact_mod_cast (by omega : finrank ℂ (Nτ i)ᗮ + finrank ℂ (Nτ i) = finrank ℂ (V i))
    rw [hk] at h2
    have h3 := (abs_le.mp h2).2
    have h4 := mul_le_mul_of_nonneg_left h1 (hc i).le
    linarith
  have hup : tW ≤ ε * (∑ i, (finrank ℂ (V i) : ℝ)) + (∑ i, (finrank ℂ (V i) : ℝ)) * √(ε * e) := by
    rw [htW]
    have h1 := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hWi i)
    rw [Finset.sum_add_distrib] at h1
    have hCS : ∑ i, √((finrank ℂ (V i) : ℝ) - finrank ℂ (Nτ i)) * √(hs2 (frK (c i) (B i) - LinearMap.id))
        ≤ (∑ i, (finrank ℂ (V i) : ℝ)) * √(ε * e) := by
      calc _ ≤ √(∑ i, ((finrank ℂ (V i) : ℝ) - finrank ℂ (Nτ i))) *
              √(∑ i, hs2 (frK (c i) (B i) - LinearMap.id)) :=
            Real.sum_sqrt_mul_sqrt_le Finset.univ (fun i => sub_nonneg.mpr (hnk i))
              (fun i => hs2_nonneg _)
        _ ≤ √(ε * ∑ i, (finrank ℂ (V i) : ℝ)) * √(e * ∑ i, (finrank ℂ (V i) : ℝ)) :=
            mul_le_mul (Real.sqrt_le_sqrt hN) (Real.sqrt_le_sqrt hK) (Real.sqrt_nonneg _)
              (Real.sqrt_nonneg _)
        _ = (∑ i, (finrank ℂ (V i) : ℝ)) * √(ε * e) := by
            rw [← Real.sqrt_mul (mul_nonneg hε hR.le),
              show ε * (∑ i, (finrank ℂ (V i) : ℝ)) * (e * ∑ i, (finrank ℂ (V i) : ℝ))
                = ε * e * (∑ i, (finrank ℂ (V i) : ℝ)) ^ 2 by ring,
              Real.sqrt_mul (mul_nonneg hε he0), Real.sqrt_sq hR.le]
            ring
    linarith

  set s : ℝ := (LinearMap.trace ℂ H (frQ c B)).re / (finrank ℂ H : ℝ) with hs
  set A : H →ₗ[ℂ] H := frQ c B - (s : ℂ) • LinearMap.id with hA
  have hlow : (LinearMap.trace ℂ H (frQ c B)).re / (finrank ℂ H : ℝ) * (finrank ℂ W : ℝ)
      - √(finrank ℂ W : ℝ) * √(hs2 A) ≤ tW := by
    have h := sum_re_inner_bound A hg
    simp only [Fintype.card_fin] at h
    have h1 : ∀ l, ⟪g l, g l⟫_ℂ = 1 := fun l => by
      rw [inner_self_eq_norm_sq_to_K, hg.1 l]; simp
    have hsum : ∑ l, (⟪g l, A (g l)⟫_ℂ).re
        = tW - s * (finrank ℂ W : ℝ) := by
      simp only [hA, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply, inner_sub_right,
        inner_smul_right, h1, mul_one, Complex.sub_re, Complex.ofReal_re, Finset.sum_sub_distrib,
        Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, htWdef]
      ring
    rw [hsum] at h
    have := (abs_le.mp h).1
    linarith
  have hX : hs2 A
      ≤ η * (LinearMap.trace ℂ H (frQ c B)).re ^ 2 / (finrank ℂ H : ℝ) := by
    set u := stdOrthonormalBasis ℂ H with hu
    have hterm : ∀ n, ‖A (u n)‖ ^ 2
        = ‖frQ c B (u n)‖ ^ 2 - 2 * s * (⟪u n, frQ c B (u n)⟫_ℂ).re + s ^ 2 := by
      intro n
      simp only [hA, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply]
      have hsym : (⟪frQ c B (u n), u n⟫_ℂ).re = (⟪u n, frQ c B (u n)⟫_ℂ).re :=
        inner_re_symm (𝕜 := ℂ) _ _
      rw [norm_sub_sq (𝕜 := ℂ), inner_smul_right, norm_smul, u.orthonormal.1 n]
      simp only [RCLike.re_to_complex, Complex.re_ofReal_mul, Complex.norm_real, Real.norm_eq_abs,
        mul_one, sq_abs, hsym]
      ring
    have htr : (LinearMap.trace ℂ H (frQ c B)).re = ∑ n, (⟪u n, frQ c B (u n)⟫_ℂ).re := by
      rw [LinearMap.trace_eq_sum_inner (frQ c B) u, Complex.re_sum]
    have hT2 : (LinearMap.trace ℂ H (frQ c B ∘ₗ frQ c B)).re = ∑ n, ‖frQ c B (u n)‖ ^ 2 := trace_frame_sq_eq_sum c B
    rw [hilbert_schmidt_eq_basis_sum _ u]
    simp only [hterm, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    rw [← htr, ← hT2]
    have hsD : s * (finrank ℂ H : ℝ) = (LinearMap.trace ℂ H (frQ c B)).re := by
      rw [hs]; field_simp
    have hst : (LinearMap.trace ℂ H (frQ c B)).re ^ 2 / (finrank ℂ H : ℝ)
        = s * (LinearMap.trace ℂ H (frQ c B)).re := by
      rw [hs]; field_simp
    have hQ' : (LinearMap.trace ℂ H (frQ c B ∘ₗ frQ c B)).re
        ≤ (1 + η) * (LinearMap.trace ℂ H (frQ c B)).re ^ 2 / (finrank ℂ H : ℝ) := hQ
    rw [show (1 + η) * (LinearMap.trace ℂ H (frQ c B)).re ^ 2 / (finrank ℂ H : ℝ)
        = (LinearMap.trace ℂ H (frQ c B)).re ^ 2 / (finrank ℂ H : ℝ)
          + η * (LinearMap.trace ℂ H (frQ c B)).re ^ 2 / (finrank ℂ H : ℝ) by ring] at hQ'
    have hDs2 : (finrank ℂ H : ℝ) * s ^ 2 = s * (LinearMap.trace ℂ H (frQ c B)).re := by
      rw [← hsD]; ring
    linarith
  exact final_real1 _ _ _ e ε η _ _ tW hD hR he0 he hε (Nat.cast_nonneg _) hwD ht
    (hs2_nonneg _) hX hlow hup

end Formalism.HN
end
end

-- bundled from Formalism.HarderNarasimhan.HarderNarasimhanProofs.GramBlock
section
open Module

noncomputable section

namespace Formalism.HN

theorem gramBlock_norm_sum_sq {P F : Type*} [Fintype P] [NormedAddCommGroup F]
    [InnerProductSpace ℝ F] (y : P → F) (h : ∀ v w, v ≠ w → inner ℝ (y v) (y w) = 0) :
    ‖∑ v, y v‖ ^ 2 = ∑ v, ‖y v‖ ^ 2 := by
  classical
  rw [← real_inner_self_eq_norm_sq]
  simp_rw [sum_inner, inner_sum]
  refine Finset.sum_congr rfl fun v _ => ?_
  rw [Finset.sum_eq_single v (fun w _ hw => h v w (Ne.symm hw)) (by simp),
    real_inner_self_eq_norm_sq]

theorem gramBlock_gram_comb {ι E F : Type*} [Fintype ι] [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    (g : E →ₗ[ℝ] F) (f : ι → E) (M : Matrix ι ι ℝ) :
    Matrix.gram ℝ (fun j => g (∑ i, M i j • f i)) = M.transpose * Matrix.gram ℝ (fun i => g (f i)) * M := by
  ext j l
  simp only [Matrix.gram_apply, Matrix.mul_apply, Matrix.transpose_apply, map_sum, map_smul,
    sum_inner, inner_sum, real_inner_smul_left, real_inner_smul_right, Finset.sum_mul]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

private theorem det_gram_le_one_of_norm_sum_sq_le {κ F : Type*} [Fintype κ] [DecidableEq κ]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] (w : κ → F)
    (hw : ∀ x : κ → ℝ, ‖∑ a, x a • w a‖ ^ 2 ≤ ∑ a, x a ^ 2) :
    (Matrix.gram ℝ w).det ≤ 1 := by
  have hP := Matrix.posSemidef_gram ℝ w
  rw [hP.isHermitian.det_eq_prod_eigenvalues]
  apply Finset.prod_le_one
  · intro i _
    simpa using hP.eigenvalues_nonneg i
  · intro i _
    have hv : ∑ a, (hP.isHermitian.eigenvectorBasis i).ofLp a ^ 2 = 1 := by
      have h1 := PiLp.norm_sq_eq_of_L2 (fun _ : κ => ℝ) (hP.isHermitian.eigenvectorBasis i)
      rw [hP.isHermitian.eigenvectorBasis.orthonormal.1 i] at h1
      simpa [Real.norm_eq_abs, sq_abs] using h1.symm
    have h2 := hP.isHermitian.eigenvalues_eq i
    rw [Matrix.star_dotProduct_gram_mulVec, RCLike.re_to_real, real_inner_self_eq_norm_sq] at h2
    simp only [RCLike.ofReal_real_eq_id, id]
    rw [h2, ← hv]
    exact hw _

theorem gram_block_determinant : GramBlock := by
  intro P E E' ι _ _ _ _ _ _ _ _ _ _ Ev Ev' T c W u hEv hEv' hc hT hW hu hspan
  classical
  let k : P → ℕ := fun v => Module.finrank ℝ (W ⊓ Ev v : Submodule ℝ E)
  let B : ∀ v, OrthonormalBasis (Fin (k v)) ℝ (W ⊓ Ev v : Submodule ℝ E) :=
    fun v => stdOrthonormalBasis ℝ _
  let f : (Σ v, Fin (k v)) → E := fun a => (B a.1 a.2 : E)
  have hfW : ∀ a, f a ∈ W ⊓ Ev a.1 := fun a => (B a.1 a.2).2
  have hfon : Orthonormal ℝ f := by
    rw [orthonormal_iff_ite]
    rintro ⟨v, i⟩ ⟨w, j⟩
    by_cases hvw : v = w
    · subst hvw
      have h1 := orthonormal_iff_ite.1 (B v).orthonormal i j
      rw [Submodule.coe_inner] at h1
      simp only [f]
      rw [h1]
      by_cases hij : i = j
      · simp [hij]
      · simp [hij]
    · rw [if_neg (fun h => hvw (congrArg Sigma.fst h))]
      exact hEv v w hvw _ (hfW ⟨v, i⟩).2 _ (hfW ⟨w, j⟩).2
  have hspanf : Submodule.span ℝ (Set.range f) = W := by
    apply le_antisymm
    · rw [Submodule.span_le]
      rintro _ ⟨a, rfl⟩
      exact (hfW a).1
    · conv_lhs => rw [hW]
      refine iSup_le fun v => ?_
      intro x hx
      have key : ((∑ i, inner ℝ (B v i) (⟨x, hx⟩ : (W ⊓ Ev v : Submodule ℝ E)) • B v i :
          (W ⊓ Ev v : Submodule ℝ E)) : E) = x := by
        rw [(B v).sum_repr']
      rw [← key, Submodule.coe_sum]
      refine Submodule.sum_mem _ fun i _ => ?_
      rw [Submodule.coe_smul]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨⟨v, i⟩, rfl⟩)
  have hcard : Fintype.card (Σ v, Fin (k v)) = Fintype.card ι := by
    have h1 := finrank_span_eq_card hfon.linearIndependent
    have h2 := finrank_span_eq_card hu
    rw [hspanf] at h1
    rw [hspan] at h2
    omega
  let e := Fintype.equivOfCardEq hcard
  let f' : ι → E := f ∘ e.symm
  have hf'on : Orthonormal ℝ f' := hfon.comp _ e.symm.injective
  have hspan' : Submodule.span ℝ (Set.range f') = W := by
    rw [Set.range_comp, e.symm.surjective.range_eq, Set.image_univ]
    exact hspanf
  have hex : ∀ j, ∃ a : ι → ℝ, ∑ i, a i • f' i = u j := by
    intro j
    have : u j ∈ Submodule.span ℝ (Set.range f') := by
      rw [hspan', ← hspan]
      exact Submodule.subset_span ⟨j, rfl⟩
    exact (Submodule.mem_span_range_iff_exists_fun ℝ).1 this
  choose a ha using hex
  let M : Matrix ι ι ℝ := fun i j => a j i
  have huM : u = fun j => ∑ i, M i j • f' i := funext fun j => (ha j).symm
  have hG1 : Matrix.gram ℝ f' = 1 := by
    ext i j
    rw [Matrix.gram_apply, orthonormal_iff_ite.1 hf'on, Matrix.one_apply]
  have hGu : (Matrix.gram ℝ u).det = M.det ^ 2 := by
    have h1 := gramBlock_gram_comb (LinearMap.id : E →ₗ[ℝ] E) f' M
    simp only [LinearMap.id_apply] at h1
    simp only [huM]
    rw [h1, hG1, Matrix.mul_one, Matrix.det_mul, Matrix.det_transpose]
    ring
  have hGT : (Matrix.gram ℝ (fun i => T (u i))).det =
      M.det ^ 2 * (Matrix.gram ℝ (fun i => T (f' i))).det := by
    simp only [huM]
    rw [gramBlock_gram_comb T f' M, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose]
    ring
  have hreidx : (Matrix.gram ℝ (fun i => T (f' i))).det =
      (Matrix.gram ℝ (fun a => T (f a))).det := by
    have h1 : Matrix.gram ℝ (fun i => T (f' i)) =
        (Matrix.gram ℝ (fun a => T (f a))).submatrix e.symm e.symm := by
      ext i j
      rfl
    rw [h1, Matrix.det_submatrix_equiv_self]
  have hTf : ∀ a, T (f a) ∈ Ev' a.1 ∧ ‖T (f a)‖ ≤ c a.1 := by
    intro a
    have h1 := hT a.1 (f a) (hfW a).2
    rw [hfon.1 a, mul_one] at h1
    exact h1
  have hprod : ∏ v, c v ^ (2 * Module.finrank ℝ (W ⊓ Ev v : Submodule ℝ E)) =
      ∏ a : (Σ v, Fin (k v)), c a.1 ^ 2 := by
    rw [Fintype.prod_sigma]
    refine Finset.prod_congr rfl fun v _ => ?_
    simp [Finset.prod_const, ← pow_mul, k]
  have hA : (Matrix.gram ℝ (fun a => T (f a))).det ≤ ∏ a : (Σ v, Fin (k v)), c a.1 ^ 2 := by
    by_cases h0 : ∃ a : (Σ v, Fin (k v)), c a.1 = 0
    · obtain ⟨a, ha0⟩ := h0
      have hz : T (f a) = 0 := by
        have h1 := (hTf a).2
        rw [ha0] at h1
        exact norm_le_zero_iff.1 h1
      rw [Matrix.det_eq_zero_of_row_eq_zero a (fun j => by rw [Matrix.gram_apply, hz, inner_zero_left])]
      exact Finset.prod_nonneg fun _ _ => sq_nonneg _
    · push_neg at h0
      have hpos : ∀ a : (Σ v, Fin (k v)), 0 < c a.1 := fun a => lt_of_le_of_ne (hc a.1) (h0 a).symm
      let w : (Σ v, Fin (k v)) → E' := fun a => (c a.1)⁻¹ • T (f a)
      have hgram : Matrix.gram ℝ (fun a => T (f a)) =
          Matrix.diagonal (fun a => c a.1) * Matrix.gram ℝ w * Matrix.diagonal (fun a => c a.1) := by
        ext a b
        simp only [Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.gram_apply, w,
          real_inner_smul_left, real_inner_smul_right]
        field_simp [(hpos a).ne', (hpos b).ne']
      have hnorm : ∀ x : (Σ v, Fin (k v)) → ℝ, ‖∑ a, x a • w a‖ ^ 2 ≤ ∑ a, x a ^ 2 := by
        intro x
        let z : P → E := fun v => ∑ i, x ⟨v, i⟩ • f ⟨v, i⟩
        let y : P → E' := fun v => (c v)⁻¹ • T (z v)
        have hsum : ∑ a, x a • w a = ∑ v, y v := by
          rw [Fintype.sum_sigma]
          refine Finset.sum_congr rfl fun v _ => ?_
          simp only [y, z, w, map_sum, map_smul, Finset.smul_sum, smul_smul, mul_comm]
        have hzE : ∀ v, z v ∈ Ev v := fun v =>
          Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (hfW ⟨v, i⟩).2
        have hyE : ∀ v, y v ∈ Ev' v := fun v => Submodule.smul_mem _ _ (hT v _ (hzE v)).1
        have hyz : ∀ v, ‖y v‖ ≤ ‖z v‖ := by
          intro v
          rcases (hc v).eq_or_lt with h | h
          · simp [y, ← h]
          · have hv := (hT v _ (hzE v)).2
            simp only [y]
            rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos h]
            calc (c v)⁻¹ * ‖T (z v)‖ ≤ (c v)⁻¹ * (c v * ‖z v‖) := by gcongr
              _ = ‖z v‖ := by field_simp
        have hzsum : ∑ v, z v = ∑ a, x a • f a := by
          rw [Fintype.sum_sigma]
        rw [hsum, gramBlock_norm_sum_sq y (fun v w hvw => hEv' v w hvw _ (hyE v) _ (hyE w))]
        calc ∑ v, ‖y v‖ ^ 2 ≤ ∑ v, ‖z v‖ ^ 2 :=
              Finset.sum_le_sum fun v _ => pow_le_pow_left₀ (norm_nonneg _) (hyz v) 2
          _ = ‖∑ v, z v‖ ^ 2 :=
              (gramBlock_norm_sum_sq z (fun v w hvw => hEv v w hvw _ (hzE v) _ (hzE w))).symm
          _ = ∑ a, x a ^ 2 := by
              rw [hzsum, ← real_inner_self_eq_norm_sq, hfon.inner_sum x x Finset.univ]
              simp [sq]
      have hle : (Matrix.gram ℝ w).det ≤ 1 := det_gram_le_one_of_norm_sum_sq_le w hnorm
      have hP0 : 0 ≤ ∏ a : (Σ v, Fin (k v)), c a.1 := Finset.prod_nonneg fun a _ => (hpos a).le
      rw [hgram, Matrix.det_mul, Matrix.det_mul, Matrix.det_diagonal]
      calc (∏ a : (Σ v, Fin (k v)), c a.1) * (Matrix.gram ℝ w).det * ∏ a : (Σ v, Fin (k v)), c a.1
          ≤ (∏ a : (Σ v, Fin (k v)), c a.1) * 1 * ∏ a : (Σ v, Fin (k v)), c a.1 :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hle hP0) hP0
        _ = ∏ a : (Σ v, Fin (k v)), c a.1 ^ 2 := by
            rw [mul_one, ← Finset.prod_mul_distrib]
            simp [sq]
  refine ⟨?_, fun hiso => ?_⟩
  · rw [hGT, hGu, hreidx, hprod, mul_comm]
    exact mul_le_mul_of_nonneg_right hA (sq_nonneg _)
  · have hdiag : Matrix.gram ℝ (fun a => T (f a)) = Matrix.diagonal (fun a => c a.1 ^ 2) := by
      ext a b
      rw [Matrix.gram_apply, Matrix.diagonal_apply]
      by_cases hab : a.1 = b.1
      · obtain ⟨v, i⟩ := a
        obtain ⟨w, j⟩ := b
        simp only at hab
        subst hab
        rw [hiso v _ (hfW ⟨v, i⟩).2 _ (hfW ⟨v, j⟩).2, orthonormal_iff_ite.1 hfon]
        split_ifs <;> simp
      · rw [if_neg (fun h => hab (congrArg Sigma.fst h))]
        exact hEv' _ _ hab _ (hTf a).1 _ (hTf b).1
    rw [hGT, hGu, hreidx, hdiag, Matrix.det_diagonal, hprod]
    ring

end Formalism.HN
end
end

