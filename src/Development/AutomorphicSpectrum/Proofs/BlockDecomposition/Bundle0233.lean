import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IwahoriFactorisation.StrictDominance.UnitaryExtremality.SatPowNonvan
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConjTransposeAntidiagFixed
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.WaveSt
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0203
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0226
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0222
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0223
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0224
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0221
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0227
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnitaryCharacterFacts

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RootMapMemCompactOfIntegral
section
open GlobalTheory.PRep Formalism.UG GlobalTheory.LFun PositivityTheory.SphericalProduct GlobalTheory.CompanionTheory.SwapRoot

noncomputable section

namespace GlobalTheory.CompanionTheory.SwapRoot

section RootInt

variable {L : Type} [Field L]

theorem partner_nU (σ : L →+* L) (x : L) : partner σ (nU x) = !![1, -σ x; 0, 1] := by
  have hi : (((nU x)⁻¹ : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) = !![1, -x; 0, 1] := rfl
  have hc : cT σ (!![1, -x; 0, 1] : Matrix (Fin 2) (Fin 2) L) = !![1, 0; -σ x, 1] := by
    ext p r
    fin_cases p <;> fin_cases r <;> simp [cT]
  simp only [partner, hi, hc, w2]
  rw [Matrix.mul_fin_two, Matrix.mul_fin_two]
  simp

variable [Valued L (WithZero (Multiplicative ℤ))]

theorem val_cM_conj_le_one {n : ℕ} (c : Fin 2 → Fin n) (P : Matrix (Fin 2) (Fin 2) L)
    (hP : ∀ p r, Valued.v (P p r) ≤ 1) (b d : Fin n) :
    Valued.v ((cM L c * P * (cM L c).transpose) b d) ≤ 1 := by
  rw [cM_conj_apply]
  refine Valuation.map_sum_le _ fun p _ => Valuation.map_sum_le _ fun r _ => ?_
  split_ifs
  · exact hP p r
  · rw [map_zero]; exact zero_le

theorem blockM_int {n : ℕ} (a : ℕ) (h : 2 * (a + 2) ≤ n) (X Y : Matrix (Fin 2) (Fin 2) L)
    (hX : ∀ p r, Valued.v ((X - 1) p r) ≤ 1) (hY : ∀ p r, Valued.v ((Y - 1) p r) ≤ 1) :
    Formalism.UG.P.fIwasawaInt (blockM a h X Y) := by
  intro b d
  simp only [blockM, Matrix.add_apply]
  exact Valuation.map_add_le _ (Valuation.map_add_le _ (Formalism.UG.P.fIwasawa_int_one b d)
    (val_cM_conj_le_one _ _ hX b d)) (val_cM_conj_le_one _ _ hY b d)

theorem val_unip_sub_one_le {y : L} (hy : Valued.v y ≤ 1) (p r : Fin 2) :
    Valued.v (((!![1, y; 0, 1] : Matrix (Fin 2) (Fin 2) L) - 1) p r) ≤ 1 := by
  fin_cases p <;> fin_cases r <;> simp [hy]

theorem uR_mem_KU : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (ϖ : L) (σ : L →+* L) (q n : ℕ)
    (hU : IsUnramInv ϖ σ q) (a : ℕ) (h : 2 * (a + 2) ≤ n) (x : L), Valued.v x ≤ 1 → uR σ hU.1 a h x ∈ KU σ n := by
  intro L _ _ ϖ σ q n hU a h x hx
  have hσv := hU.2.1
  have hI : Formalism.UG.P.fIwasawaInt (((uR σ hU.1 a h x : GU σ n) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) := by
    show Formalism.UG.P.fIwasawaInt (blockM a h (nU x : GL (Fin 2) L).val (partner σ (nU x)))
    rw [partner_nU]
    refine blockM_int a h _ _ (val_unip_sub_one_le hx) (val_unip_sub_one_le ?_)
    rw [Valuation.map_neg, hσv]
    exact hx
  have hK := Formalism.UG.P.fIwasawa_mk_mem_K σ hσv _ (Formalism.UG.P.fIwasawa_mem_un σ (uR σ hU.1 a h x)) hI
  have he : Formalism.UG.P.fIwasawaMk σ _ (Formalism.UG.P.fIwasawa_mem_un σ (uR σ hU.1 a h x)) = uR σ hU.1 a h x :=
    Subtype.ext (Units.ext (Formalism.UG.P.fIwasawa_mk_val σ _ _))
  rwa [he] at hK

end RootInt

end GlobalTheory.CompanionTheory.SwapRoot

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SimpleReflectionMemMaximalCompact
section
noncomputable section

open GlobalTheory.PRep Formalism.UG GlobalTheory.LFun PositivityTheory.SphericalProduct GlobalTheory.CompanionTheory.SwapRoot Matrix

namespace GlobalTheory.CompanionTheory.SwapRoot

variable {L : Type} [Field L]

theorem partner_wU (σ : L →+* L) : partner σ (wU L) = w2 L := by
  have hw : (((wU L)⁻¹ : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) = w2 L := rfl
  have hc : cT σ (w2 L) = w2 L := by
    delta cT w2
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  delta partner
  rw [hw, hc, weyl_mul_weyl, one_mul]

variable [Valued L (WithZero (Multiplicative ℤ))]

theorem cM_conj_int {n : ℕ} (c : Fin 2 → Fin n) (P : Matrix (Fin 2) (Fin 2) L)
    (hP : ∀ p r, Valued.v (P p r) ≤ 1) (b d : Fin n) :
    Valued.v ((cM L c * P * (cM L c)ᵀ) b d) ≤ 1 := by
  have hA : ∀ (x : Fin n) (p : Fin 2), Valued.v (cM L c x p) ≤ 1 := by
    intro x p
    show Valued.v (if x = c p then (1 : L) else 0) ≤ 1
    split_ifs <;> simp
  rw [Matrix.mul_apply]
  refine Valuation.map_sum_le (Valued.v : Valuation L (WithZero (Multiplicative ℤ))) fun r _ => ?_
  rw [Valuation.map_mul, Matrix.transpose_apply, Matrix.mul_apply]
  refine mul_le_one' ?_ (hA d r)
  refine Valuation.map_sum_le (Valued.v : Valuation L (WithZero (Multiplicative ℤ))) fun p _ => ?_
  rw [Valuation.map_mul]
  exact mul_le_one' (hA b p) (hP p r)

theorem weyl_sub_one_entries_integral (p r : Fin 2) : Valued.v ((w2 L - 1) p r) ≤ 1 := by
  delta w2
  fin_cases p <;> fin_cases r <;> simp [Matrix.one_apply]

theorem block_matrix_weyl_integral {n : ℕ} (a : ℕ) (h : 2 * (a + 2) ≤ n) :
    Formalism.UG.P.fIwasawaInt (blockM a h (w2 L) (w2 L)) := by
  delta blockM
  intro i j
  simp only [Matrix.add_apply]
  refine Valuation.map_add_le _ (Valuation.map_add_le _ ?_ (cM_conj_int _ _ weyl_sub_one_entries_integral i j))
    (cM_conj_int _ _ weyl_sub_one_entries_integral i j)
  rw [Matrix.one_apply]
  split_ifs <;> simp

theorem sR_mem_KU : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (ϖ : L)
    (σ : L →+* L) (q n : ℕ) (hU : IsUnramInv ϖ σ q) (a : ℕ) (h : 2 * (a + 2) ≤ n),
    sR σ hU.1 a h ∈ KU σ n := by
  intro L _ _ ϖ σ q n hU a h
  have hval : (((sR σ hU.1 a h : GU σ n) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) =
      blockM a h (w2 L) (w2 L) := by
    show blockM a h (w2 L) (partner σ (wU L)) = _
    rw [partner_wU]
  have hwinv : (wU L)⁻¹ = wU L := Units.ext rfl
  have hginv : (sR σ hU.1 a h)⁻¹ = sR σ hU.1 a h := by
    show ((rootHom σ hU.1 a h) (wU L))⁻¹ = (rootHom σ hU.1 a h) (wU L)
    rw [← map_inv, hwinv]
  have hBB : blockM a h (w2 L) (w2 L) * blockM a h (w2 L) (w2 L) = 1 := by
    have h1 := ((sR σ hU.1 a h : GU σ n) : GL (Fin n) L).mul_inv
    rw [← Subgroup.coe_inv, hginv, hval] at h1
    exact h1
  have hint : ∀ i j, blockM a h (w2 L) (w2 L) i j ∈ intL L := fun i j => block_matrix_weyl_integral (L := L) a h i j
  let Bi : Matrix (Fin n) (Fin n) (intL L) := Matrix.of fun i j => ⟨blockM a h (w2 L) (w2 L) i j, hint i j⟩
  have hBi : ∀ i j, ((Bi * Bi) i j : L) = (blockM a h (w2 L) (w2 L) * blockM a h (w2 L) (w2 L)) i j := by
    intro i j
    simp [Bi, Matrix.mul_apply]
  have hy : Bi * Bi = 1 := by
    ext i j
    rw [hBi, hBB, Matrix.one_apply, Matrix.one_apply]
    split_ifs <;> simp
  show ((sR σ hU.1 a h : GU σ n) : GL (Fin n) L) ∈ GU σ n ⊓ (bc (intL L).subtype).range
  refine Subgroup.mem_inf.2 ⟨(sR σ hU.1 a h).2, ⟨⟨Bi, Bi, hy, hy⟩, ?_⟩⟩
  apply Units.ext
  rw [hval]
  ext i j
  rfl

end GlobalTheory.CompanionTheory.SwapRoot

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SimpleReflectionRootBorelDecomp
section
noncomputable section

open GlobalTheory.PRep Formalism.UG GlobalTheory.LFun PositivityTheory.SphericalProduct GlobalTheory.CompanionTheory.SwapRoot

namespace GlobalTheory.CompanionTheory.SwapFactor

section Local
variable {L : Type} [Field L]

def betaU (x : L) (hx : x ≠ 0) : GL (Fin 2) L where
  val := !![-x⁻¹, 1; 0, x]
  inv := !![-x, 1; 0, x⁻¹]
  val_inv := by
    ext p r; fin_cases p <;> fin_cases r <;> simp [Matrix.mul_apply, Fin.sum_univ_two, hx]
  inv_val := by
    ext p r; fin_cases p <;> fin_cases r <;> simp [Matrix.mul_apply, Fin.sum_univ_two, hx]

theorem wU_mul_nU (x : L) (hx : x ≠ 0) :
    wU L * nU x = betaU x hx * (wU L * nU x⁻¹ * wU L) := by
  apply Units.ext
  ext p r
  fin_cases p <;> fin_cases r <;>
    simp [betaU, wU, nU, w2, Matrix.mul_apply, Fin.sum_univ_two, hx]

theorem partner_betaU_lower (σ : L →+* L) (x : L) (hx : x ≠ 0) : partner σ (betaU x hx) 1 0 = 0 := by
  have : ((betaU x hx)⁻¹ : GL (Fin 2) L).val = !![-x, 1; 0, x⁻¹] := rfl
  have hw : ∀ M : Matrix (Fin 2) (Fin 2) L, (w2 L * M * w2 L) 1 0 = M 0 1 := fun M => by
    simp [w2, Matrix.mul_apply, Fin.sum_univ_two, Matrix.vecMul, dotProduct]
  rw [partner, hw, this]
  simp [cT]

theorem arith (u v Q : ℂ) (hQ : Q ≠ 0) (o N : ℤ) :
    u ^ (-o) * Q ^ (-(-o) * N) * (v ^ o * Q ^ (-o * (N - 2))) = ((u / v) / Q ^ 2) ^ (-o) := by
  have h2 : (Q ^ 2) ^ (-o) = Q ^ (-(2 * o)) := by
    rw [← zpow_natCast, ← zpow_mul]; congr 1; push_cast; ring
  have h3 : Q ^ (-(-o) * N) * Q ^ (-o * (N - 2)) = Q ^ (2 * o) := by
    rw [← zpow_add₀ hQ]; congr 1; ring
  have h4 : v ^ o = (v ^ (-o))⁻¹ := by rw [zpow_neg, inv_inv]
  rw [div_zpow, div_zpow, h2, zpow_neg Q (2 * o)]
  calc _ = u ^ (-o) * (v ^ (-o))⁻¹ * (Q ^ (-(-o) * N) * Q ^ (-o * (N - 2))) := by rw [h4]; ring
    _ = _ := by rw [h3]; simp [div_eq_mul_inv]

end Local

section Root
variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {n : ℕ} {σ : L →+* L}

theorem ordL_neg' (x : L) (hx : x ≠ 0) : ordL (-x) = ordL x := by
  have h1 := v_eq_exp' (neg_ne_zero.2 hx)
  rw [Valuation.map_neg, v_eq_exp' hx] at h1
  have := WithZero.exp_injective h1
  omega

theorem ordL_one' : ordL (1 : L) = 0 := by simp [ordL]; rfl

theorem isBorel_root (hσ : ∀ x, σ (σ x) = x) (a : ℕ) (h : 2 * (a + 2) ≤ n) (x : L) (hx : x ≠ 0) :
    IsBorelU (rootHom σ hσ a h (betaU x hx)) := by
  intro i j hji
  rw [rootHom_val]
  by_cases hI : (∃ p, i = cI n a h p) ∧ ∃ r, j = cI n a h r
  · obtain ⟨⟨p, rfl⟩, r, rfl⟩ := hI
    rw [blockM_cI]
    have hlt : (cI n a h r : ℕ) < (cI n a h p : ℕ) := hji
    simp only [cI] at hlt
    have hp : p = 1 := Fin.ext (by have := p.2; simp only [Fin.val_one]; omega)
    have hr : r = 0 := Fin.ext (by have := r.2; simp only [Fin.val_zero]; omega)
    subst hp hr
    rfl
  by_cases hJ : (∃ p, i = cJ n a h p) ∧ ∃ r, j = cJ n a h r
  · obtain ⟨⟨p, rfl⟩, r, rfl⟩ := hJ
    rw [blockM_cJ]
    have hlt : (cJ n a h r : ℕ) < (cJ n a h p : ℕ) := hji
    simp only [cJ] at hlt
    have hp : p = 1 := Fin.ext (by have := p.2; simp only [Fin.val_one]; omega)
    have hr : r = 0 := Fin.ext (by have := r.2; simp only [Fin.val_zero]; omega)
    subst hp hr
    exact partner_betaU_lower σ x hx
  rw [blockM_out]
  · exact Matrix.one_apply_ne (ne_of_gt hji)
  · by_contra hc
    push_neg at hc
    exact hI ⟨by simpa [eq_comm] using hc.1, by simpa using hc.2⟩
  · by_contra hc
    push_neg at hc
    exact hJ ⟨by simpa using hc.1, by simpa using hc.2⟩

theorem diag_a (hσ : ∀ x, σ (σ x) = x) (a : ℕ) (h : 2 * (a + 2) ≤ n) (x : L) (hx : x ≠ 0) (hk : a < n) :
    (((rootHom σ hσ a h (betaU x hx) : GU σ n) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) ⟨a, hk⟩ ⟨a, hk⟩ = -x⁻¹ := by
  have e : (⟨a, hk⟩ : Fin n) = cI n a h 0 := Fin.ext (by simp [cI])
  rw [e, rootHom_val, blockM_cI]
  rfl

theorem root_hom_diag_entry_eq (hσ : ∀ x, σ (σ x) = x) (a : ℕ) (h : 2 * (a + 2) ≤ n) (x : L) (hx : x ≠ 0) (hk : a + 1 < n) :
    (((rootHom σ hσ a h (betaU x hx) : GU σ n) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) ⟨a + 1, hk⟩ ⟨a + 1, hk⟩ = x := by
  have e : (⟨a + 1, hk⟩ : Fin n) = cI n a h 1 := Fin.ext (by simp [cI])
  rw [e, rootHom_val, blockM_cI]
  rfl

theorem diag_other (hσ : ∀ x, σ (σ x) = x) (a : ℕ) (h : 2 * (a + 2) ≤ n) (x : L) (hx : x ≠ 0) (k : Fin n)
    (hk : k.val < n / 2) (h1 : k.val ≠ a) (h2 : k.val ≠ a + 1) :
    (((rootHom σ hσ a h (betaU x hx) : GU σ n) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) k k = 1 := by
  rw [rootHom_val, blockM_out]
  · exact Matrix.one_apply_eq k
  · left
    intro p e
    have := congrArg Fin.val e
    have hp := p.2
    simp only [cI] at this
    omega
  · left
    intro p e
    have := congrArg Fin.val e
    have hp := p.2
    simp only [cJ] at this
    omega

end Root

theorem sR_uR_factor : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (ϖ : L) (σ : L →+* L) (q n : ℕ) (hU : IsUnramInv ϖ σ q) (a : ℕ) (h : 2 * (a + 2) ≤ n) (χ : Fin (n / 2) → ℂˣ) (i j : Fin (n / 2)), i.val = a → j.val = a + 1 → ∀ x : L, x ≠ 0 →
    ∃ b : GU σ n, IsBorelU b ∧
      chiDeltaU q (fun k => (χ k : ℂ)) b = (((χ i : ℂ) / (χ j : ℂ)) / (q : ℂ) ^ 2) ^ (-ordL x) ∧
      sR σ hU.1 a h * uR σ hU.1 a h x = b * (sR σ hU.1 a h * uR σ hU.1 a h x⁻¹ * sR σ hU.1 a h) := by
  intro L _ _ ϖ σ q n hU a h χ i j hi hj x hx
  have hq : (q : ℂ) ≠ 0 := by
    have : 2 ≤ q := hU.2.2.2.2.2.1
    exact Nat.cast_ne_zero.2 (by omega)
  refine ⟨rootHom σ hU.1 a h (betaU x hx), isBorel_root hU.1 a h x hx, ?_, ?_⟩
  · have hij : i ≠ j := fun e => by
      have := congrArg Fin.val e
      omega
    have ha : a < n := by omega
    have ha1 : a + 1 < n := by omega
    have hin : i.val < n := by omega
    have hjn : j.val < n := by omega
    unfold chiDeltaU
    rw [Finset.prod_eq_mul i j hij ?_ (by simp) (by simp)]
    · rw [dif_pos hin, dif_pos hjn]
      have ei : (⟨i.val, hin⟩ : Fin n) = ⟨a, ha⟩ := Fin.ext hi
      have ej : (⟨j.val, hjn⟩ : Fin n) = ⟨a + 1, ha1⟩ := Fin.ext hj
      rw [ei, ej, diag_a, root_hom_diag_entry_eq, ordL_neg' _ (inv_ne_zero hx), ordL_inv' hx, hi, hj]
      have hN : ((n : ℤ) - 1 - 2 * ((a + 1 : ℕ) : ℤ)) = ((n : ℤ) - 1 - 2 * (a : ℤ)) - 2 := by
        push_cast; ring
      rw [hN]
      exact arith _ _ _ hq _ _
    · intro k _ hk
      have hkn : k.val < n := by omega
      rw [dif_pos hkn, diag_other hU.1 a h x hx ⟨k.val, hkn⟩ (by simpa using k.2)
        (fun e => hk.1 (Fin.ext (by simpa [hi] using e)))
        (fun e => hk.2 (Fin.ext (by simpa [hj] using e))), ordL_one']
      simp
  · simp only [sR, uR, ← map_mul]
    exact congrArg _ (wU_mul_nU x hx)

end GlobalTheory.CompanionTheory.SwapFactor

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SobolevInequalityOnGroup
section
noncomputable section
open MeasureTheory Matrix Finset
open scoped ContDiff
namespace GlobalTheory.CompanionTheory.SobGL
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.RgBcC
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem bound_on_cube (n : ℕ) (Q : Set (Idx n → ℝ)) (hQc : IsCompact Q) (hQ : ∀ t ∈ Q, 1 + cm t ∈ GLs n)
    (L : List (Idx n)) : ∃ (W : Finset (List (Idx n))) (B : ℝ), 0 ≤ B ∧
      ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] (f : Mat n → V), ContDiffOn ℝ ∞ f (GLs n) →
        ∀ t ∈ Q, ‖Dw L f (1 + cm t)‖ ^ 2 ≤ B * ∑ w ∈ W, ‖Rw w f (1 + cm t)‖ ^ 2 := by
  obtain ⟨m, c, w, hc, hrep⟩ := GlobalTheory.T.derivative_as_right_words n L
  obtain ⟨-, hcm, -, -⟩ := GlobalTheory.T.chart_and_right_words_smooth n
  have hK : IsCompact ((fun t => 1 + cm t) '' Q) := hQc.image (continuous_const.add hcm)
  have hKsub : (fun t => 1 + cm t) '' Q ⊆ GLs n := by
    rintro _ ⟨t, ht, rfl⟩
    exact hQ t ht
  have hb : ∀ i, ∃ M, ∀ y ∈ (fun t => 1 + cm t) '' Q, ‖c i y‖ ≤ M := fun i =>
    hK.exists_bound_of_continuousOn ((hc i).continuousOn.mono hKsub)
  choose M hM using hb
  refine ⟨Finset.univ.image w, (∑ i, M i ^ 2) * m, by positivity, ?_⟩
  intro V _ _ f hf t ht
  have hy : 1 + cm t ∈ GLs n := hQ t ht
  have hyK : 1 + cm t ∈ (fun t => 1 + cm t) '' Q := ⟨t, ht, rfl⟩
  rw [hrep V f hf _ hy]
  have h1 : ‖∑ i, c i (1 + cm t) • Rw (w i) f (1 + cm t)‖ ≤
      ∑ i, M i * ‖Rw (w i) f (1 + cm t)‖ := by
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
    rw [norm_smul]
    exact mul_le_mul_of_nonneg_right (hM i _ hyK) (norm_nonneg _)
  have h3 : ∑ i, ‖Rw (w i) f (1 + cm t)‖ ^ 2 ≤
      (m : ℝ) * ∑ u ∈ Finset.univ.image w, ‖Rw u f (1 + cm t)‖ ^ 2 := by
    have hi : ∀ i, ‖Rw (w i) f (1 + cm t)‖ ^ 2 ≤ ∑ u ∈ Finset.univ.image w, ‖Rw u f (1 + cm t)‖ ^ 2 :=
      fun i => Finset.single_le_sum (f := fun u => ‖Rw u f (1 + cm t)‖ ^ 2)
        (fun u _ => by positivity) (Finset.mem_image_of_mem w (Finset.mem_univ i))
    calc ∑ i, ‖Rw (w i) f (1 + cm t)‖ ^ 2
        ≤ ∑ _i : Fin m, ∑ u ∈ Finset.univ.image w, ‖Rw u f (1 + cm t)‖ ^ 2 :=
          Finset.sum_le_sum fun i _ => hi i
      _ = (m : ℝ) * ∑ u ∈ Finset.univ.image w, ‖Rw u f (1 + cm t)‖ ^ 2 := by simp
  calc ‖∑ i, c i (1 + cm t) • Rw (w i) f (1 + cm t)‖ ^ 2
      ≤ (∑ i, M i * ‖Rw (w i) f (1 + cm t)‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
    _ ≤ (∑ i, M i ^ 2) * ∑ i, ‖Rw (w i) f (1 + cm t)‖ ^ 2 := Finset.sum_mul_sq_le_sq_mul_sq _ _ _
    _ ≤ (∑ i, M i ^ 2) * ((m : ℝ) * ∑ u ∈ Finset.univ.image w, ‖Rw u f (1 + cm t)‖ ^ 2) :=
        mul_le_mul_of_nonneg_left h3 (by positivity)
    _ = (∑ i, M i ^ 2) * m * ∑ u ∈ Finset.univ.image w, ‖Rw u f (1 + cm t)‖ ^ 2 := by ring

theorem sobG : PositivityTheory.RgBcC.SobG := by
  intro n _ _ μ _
  obtain ⟨hGo, hcm, hcm0, hsm⟩ := GlobalTheory.T.chart_and_right_words_smooth n
  set U0 : Set (Idx n → ℝ) := {t | 1 + cm t ∈ GLs n} with hU0def
  have hU0 : IsOpen U0 := hGo.preimage (continuous_const.add hcm)
  have h0 : (0 : Idx n → ℝ) ∈ U0 := by
    show 1 + cm 0 ∈ GLs n
    rw [hcm0, add_zero]
    show Matrix.det (1 : Mat n) ≠ 0
    simp
  obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.mp hU0 0 h0
  set ε : ℝ := δ / 2 with hε
  have hεpos : 0 < ε := by positivity
  set Q : Set (Idx n → ℝ) := Set.Icc 0 (fun _ => ε) with hQdef
  have hQc : IsCompact Q := isCompact_Icc
  have hQU : Q ⊆ U0 := by
    intro t ht
    apply hball
    rw [Metric.mem_ball, dist_zero_right]
    refine lt_of_le_of_lt ((pi_norm_le_iff_of_nonneg hεpos.le).mpr fun i => ?_) (by linarith)
    rw [Real.norm_eq_abs, abs_of_nonneg (ht.1 i)]
    exact ht.2 i
  have hQG : ∀ t ∈ Q, 1 + cm t ∈ GLs n := fun t ht => hQU ht
  obtain ⟨T, C1, hC1, hsob⟩ := GlobalTheory.T.poincare_value_bound_on_cube (Idx n) ε hεpos
  have hbd := fun L => bound_on_cube n Q hQc hQG L
  choose W B hB hWB using hbd
  have hK : IsCompact ((fun t => 1 + cm t) '' Q) := hQc.image (continuous_const.add hcm)
  have hKsub : (fun t => 1 + cm t) '' Q ⊆ GLs n := by
    rintro _ ⟨t, ht, rfl⟩
    exact hQG t ht
  obtain ⟨hlg, hlgc⟩ := GlobalTheory.T.length_continuous_proper_sublevel n
  obtain ⟨r, hr⟩ := hK.exists_bound_of_continuousOn (hlg.mono hKsub)
  set S : Set (G n) := {y | lg (y : Mat n) ≤ r} with hSdef
  have hSc : IsCompact S := hlgc r
  have hcov : ∀ t ∈ Q, ∃ y ∈ S, (y : Mat n) = 1 + cm t := by
    intro t ht
    have hdet : IsUnit (1 + cm t).det := isUnit_iff_ne_zero.mpr (hQG t ht)
    refine ⟨Matrix.nonsingInvUnit _ hdet, ?_, rfl⟩
    show lg (1 + cm t) ≤ r
    have h := hr _ ⟨t, ht, rfl⟩
    rw [Real.norm_eq_abs] at h
    exact (le_abs_self _).trans h
  obtain ⟨C2, hC2, hcmp⟩ := GlobalTheory.T.haar_chart_integral_comparison n μ Q S hQc hSc hcov
  refine ⟨T.biUnion W, r, C1 * C2 * ∑ L ∈ T, B L, ?_⟩
  intro V _ _ _ f hf x hx
  obtain ⟨hgs, hgR⟩ := GlobalTheory.T.left_translate_right_derivative n V f hf x hx
  obtain ⟨hFs, hpd⟩ := GlobalTheory.T.chart_partial_eq_right_word n V (fun y => f (x * y)) hgs
  have hxmul : ∀ y ∈ GLs n, x * y ∈ GLs n := by
    intro y hy
    show Matrix.det (x * y) ≠ 0
    rw [Matrix.det_mul]
    exact mul_ne_zero hx hy
  have hRc : ∀ w, ContinuousOn (Rw w f) (GLs n) := fun w => ((hsm V f hf).1 w).continuousOn
  let φ : Mat n → ℝ := fun y => ∑ w ∈ T.biUnion W, ‖Rw w f (x * y)‖ ^ 2
  have hφc : ContinuousOn φ (GLs n) := by
    apply continuousOn_finsetSum
    intro w _
    exact (((hRc w).comp (continuous_const.mul continuous_id).continuousOn
      (fun y hy => hxmul y hy)).norm).pow 2
  have hφ0 : ∀ y, 0 ≤ φ y := fun y => Finset.sum_nonneg fun _ _ => by positivity
  have hmain := hcmp φ hφc hφ0
  have hF := hsob V U0 (fun t => f (x * (1 + cm t))) hU0 hQU hFs
  have hstep : ∀ L ∈ T, ∫ t in Q, ‖pd L (fun t => f (x * (1 + cm t))) t‖ ^ 2 ≤
      B L * (C2 * ∫ y in S, φ (y : Mat n) ∂μ) := by
    intro L hL
    have hcongr : ∫ t in Q, ‖pd L (fun t => f (x * (1 + cm t))) t‖ ^ 2 =
        ∫ t in Q, ‖Dw L (fun y => f (x * y)) (1 + cm t)‖ ^ 2 :=
      setIntegral_congr_fun measurableSet_Icc (fun t ht => by rw [hpd L t (hQG t ht)])
    rw [hcongr]
    have hle : ∀ t ∈ Q, ‖Dw L (fun y => f (x * y)) (1 + cm t)‖ ^ 2 ≤ B L * φ (1 + cm t) := by
      intro t ht
      refine (hWB L V (fun y => f (x * y)) hgs t ht).trans (mul_le_mul_of_nonneg_left ?_ (hB L))
      calc ∑ w ∈ W L, ‖Rw w (fun y => f (x * y)) (1 + cm t)‖ ^ 2
          = ∑ w ∈ W L, ‖Rw w f (x * (1 + cm t))‖ ^ 2 :=
            Finset.sum_congr rfl fun w _ => by rw [hgR w _ (hQG t ht)]
        _ ≤ φ (1 + cm t) :=
            Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_biUnion_of_mem W hL)
              (fun _ _ _ => by positivity)
    have hint : IntegrableOn (fun t => B L * φ (1 + cm t)) Q volume := by
      refine ContinuousOn.integrableOn_compact hQc ?_
      exact continuousOn_const.mul
        (hφc.comp (continuous_const.add hcm).continuousOn (fun t ht => hQG t ht))
    calc ∫ t in Q, ‖Dw L (fun y => f (x * y)) (1 + cm t)‖ ^ 2
        ≤ ∫ t in Q, B L * φ (1 + cm t) :=
          integral_mono_of_nonneg (Filter.Eventually.of_forall fun _ => by positivity) hint
            ((ae_restrict_iff' measurableSet_Icc).mpr (Filter.Eventually.of_forall hle))
      _ = B L * ∫ t in Q, φ (1 + cm t) := integral_const_mul _ _
      _ ≤ B L * (C2 * ∫ y in S, φ (y : Mat n) ∂μ) := mul_le_mul_of_nonneg_left hmain (hB L)
  have hsplit : ∫ y in S, φ (y : Mat n) ∂μ =
      ∑ w ∈ T.biUnion W, ∫ y in S, ‖Rw w f (x * (y : Mat n))‖ ^ 2 ∂μ := by
    refine integral_finsetSum _ fun w _ => ?_
    refine ContinuousOn.integrableOn_compact hSc (Continuous.continuousOn ?_)
    have hval : ∀ y : G n, x * (y : Mat n) ∈ GLs n := fun y =>
      hxmul _ ((Matrix.isUnit_iff_isUnit_det _).mp y.isUnit).ne_zero
    exact (((hRc w).comp_continuous (continuous_const.mul Units.continuous_val) hval).norm).pow 2
  have hF0 : f (x * (1 + cm 0)) = f x := by rw [hcm0, add_zero, mul_one]
  calc ‖f x‖ ^ 2 = ‖f (x * (1 + cm 0))‖ ^ 2 := by rw [hF0]
    _ ≤ C1 * ∑ L ∈ T, ∫ t in Q, ‖pd L (fun t => f (x * (1 + cm t))) t‖ ^ 2 := hF
    _ ≤ C1 * ∑ L ∈ T, B L * (C2 * ∫ y in S, φ (y : Mat n) ∂μ) :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum hstep) hC1
    _ = C1 * C2 * (∑ L ∈ T, B L) * ∫ y in S, φ (y : Mat n) ∂μ := by
        rw [← Finset.sum_mul]
        ring
    _ = C1 * C2 * (∑ L ∈ T, B L) *
        ∑ w ∈ T.biUnion W, ∫ y in S, ‖Rw w f (x * (y : Mat n))‖ ^ 2 ∂μ := by rw [hsplit]

end GlobalTheory.CompanionTheory.SobGL
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnitaryChamberDecompositionStatement
section
open GlobalTheory.PRep Formalism.UG GlobalTheory.LFun PositivityTheory.SphericalProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitary_chamber_decomposition : PositivityTheory.SphericalProduct.ChamberU := by
  first | exact @GlobalTheory.CompanionTheory.ChamberInd.chamberU | exact GlobalTheory.CompanionTheory.ChamberInd.chamberU | (intros; apply GlobalTheory.CompanionTheory.ChamberInd.chamberU <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnitaryCharacterFactsStatement
section
open GlobalTheory.PRep Formalism.UG GlobalTheory.LFun PositivityTheory.SphericalProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitary_character_facts : PositivityTheory.SphericalProduct.CharU := by
  first | exact @GlobalTheory.CompanionTheory.TorusChar.charU | exact GlobalTheory.CompanionTheory.TorusChar.charU | (intros; apply GlobalTheory.CompanionTheory.TorusChar.charU <;> assumption)
end

