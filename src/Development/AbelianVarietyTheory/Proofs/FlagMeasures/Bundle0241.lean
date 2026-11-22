import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsVolData
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0233
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0005
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0236
import Formalism.SharpRestriction.CuspSpanNormBounds.FractionFieldToGenericStalkAlgebraMapEq
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0007
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0001
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsPrincipalIdealRingOfHenselian
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TermExponentsNonnegAndDefectGroupBound
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0214
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0234
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0080
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0012

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.IntegralUnipotentEntryMemInverseDifferentLattice
section
open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgAlg GlobalTheory.SgGlob GlobalTheory.SnMass GlobalTheory.SnMass.VolN
open scoped TensorProduct ENNReal nonZeroDivisors

noncomputable section

namespace GlobalTheory.SnMass.VolN.IntU

theorem hpk_row (k r : ℕ) (a : Fin r) (j : Fin (2 * r + k + 1)) :
    Hpk k r (esI k r a) j = if j = eI k r a then 1 else 0 := by
  simp only [Hpk, esI, eI, Fin.ext_iff]
  split_ifs <;> first | rfl | omega

theorem hpk_mulVec_esI (k r : ℕ) (a : Fin r) (z : Fin (2 * r + k + 1) → ℂ) :
    (Hpk k r *ᵥ z) (esI k r a) = z (eI k r a) := by
  simp [Matrix.mulVec, dotProduct, hpk_row]

theorem coord_eI {E : Type} [Field E] {k r : ℕ} (σ : E →+* E) (τ : E →+* ℂ)
    (hτ : ∀ x, τ (σ x) = star (τ x)) (J : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) E)
    (B : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (hB : Bᴴ * Hpk k r * B = J.map τ)
    (x y : Fin (2 * r + k + 1) → E) (a : Fin r) (s : ℝ) (hs : s ≠ 0)
    (hy : B *ᵥ (fun i => τ (y i)) = (s : ℂ)⁻¹ • bvec (esI k r a)) :
    (B *ᵥ fun i => τ (x i)) (eI k r a) = (s : ℂ) * τ (form σ J x y) := by
  have key : star (B *ᵥ (fun i => τ (y i))) ⬝ᵥ (Hpk k r *ᵥ (B *ᵥ fun i => τ (x i))) =
      star (fun i => τ (y i)) ⬝ᵥ (J.map τ *ᵥ fun i => τ (x i)) := by
    rw [← hB]
    simp only [Matrix.star_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul, Matrix.mulVec_mulVec,
      Matrix.mul_assoc]
  have lhs : star (B *ᵥ (fun i => τ (y i))) ⬝ᵥ (Hpk k r *ᵥ (B *ᵥ fun i => τ (x i))) =
      (s : ℂ)⁻¹ * (B *ᵥ fun i => τ (x i)) (eI k r a) := by
    rw [hy, star_smul, bvec, ← hpk_mulVec_esI k r a (B *ᵥ fun i => τ (x i))]
    simp [Pi.star_def, dotProduct, Pi.single_apply, -Matrix.mulVec_mulVec]
  have rhs : star (fun i => τ (y i)) ⬝ᵥ (J.map τ *ᵥ fun i => τ (x i)) = τ (form σ J x y) := by
    simp only [form, dotProduct, map_sum, map_mul, hτ, RingHom.map_mulVec]
    rfl
  rw [lhs, rhs] at key
  rw [← key, ← mul_assoc, mul_inv_cancel₀ (by exact_mod_cast hs), one_mul]

end GlobalTheory.SnMass.VolN.IntU

namespace GlobalTheory.SnMass.VolN.IntU

theorem form_smul_smul {E : Type} [Field E] {n : ℕ} (σ : E →+* E) (J : Matrix (Fin n) (Fin n) E)
    (c c' : E) (x y : Fin n → E) : form σ J (c • x) (c' • y) = c * σ c' * form σ J x y := by
  simp only [form, dotProduct, Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

theorem mem_of_pair {E : Type} [Field E] [NumberField E] (σ : E →+* E) (hσ : ∀ x, σ (σ x) = x)
    (𝔞 𝔟 : FractionalIdeal (𝓞 E)⁰ E) (h𝔞 : 𝔞 ≠ 0) (h𝔟 : 𝔟 ≠ 0) (hst : FrameDual.Stab σ 𝔞⁻¹) (u : E)
    (hu : ∀ c ∈ 𝔟, ∀ c' ∈ 𝔞⁻¹, c * σ c' * u ∈ (algebraMap (𝓞 E) E).range) : u ∈ 𝔞 * 𝔟⁻¹ := by
  have hI : 𝔟 * 𝔞⁻¹ ≠ 0 := mul_ne_zero h𝔟 (inv_ne_zero h𝔞)
  have e : 𝔞 * 𝔟⁻¹ = (𝔟 * 𝔞⁻¹)⁻¹ := by rw [mul_inv, inv_inv, mul_comm]
  rw [e, FractionalIdeal.mem_inv_iff hI]
  intro y hy
  refine FractionalIdeal.mul_induction_on hy (fun c hc d hd => ?_) (fun y₁ y₂ h₁ h₂ => ?_)
  · have := hu c hc (σ d) (hst d hd)
    rw [hσ] at this
    obtain ⟨t, ht⟩ := this
    exact (FractionalIdeal.mem_one_iff _).2 ⟨t, by rw [ht]; ring⟩
  · rw [mul_add]; exact Submodule.add_mem (1 : FractionalIdeal (𝓞 E)⁰ E).coeToSubmodule h₁ h₂

end GlobalTheory.SnMass.VolN.IntU

open GlobalTheory.SnMass.VolN.IntU in

theorem GlobalTheory.SnMass.VolN.gM_entry_mem_ideLat : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (k r : ℕ) (J : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) E) (Λ : Submodule (𝓞 E) (Fin (2 * r + k + 1) → E)) (P : Matrix (Fin (2 * r + k + 1)) (Fin (r + 1)) E) (f : Matrix (Fin (2 * r + k + 1)) (Fin r) E) (T : F) (A : InfinitePlace E → Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (s : Fin r → ℝ), IsVolData σ J Λ P f T A s → ∀ γ ∈ GN (σ : E →+* E) J Λ P, ∀ p : UTr r, (fun w => gM A γ w (eI k r p.1.1) (eI k r p.1.2)) ∈ ideLat (dInv E (r - p.1.1.val) * (dInv E (r - p.1.2.val))⁻¹) (s p.1.1 / s p.1.2) := by
  intro F E _ _ _ _ _ σ k r J Λ P f T A s hV γ hγ p
  obtain ⟨hCM, -, hND, hSD, -, -, hTup, hMod, hs, hAd⟩ := hV
  obtain ⟨⟨a, b⟩, hab⟩ := p
  dsimp only
  have hconj : ∀ (τ : E →+* ℂ) (x : E), τ (σ x) = star (τ x) := hCM.2.2.2
  have hσ : ∀ x, (σ : E →+* E) ((σ : E →+* E) x) = x := by
    intro x
    show σ (σ x) = x
    exact (Classical.arbitrary (InfinitePlace E)).embedding.injective (by rw [hconj, hconj, star_star])
  set eb : Fin (2 * r + k + 1) → E := fun i => P i b.castSucc with heb
  set fa : Fin (2 * r + k + 1) → E := fun i => f i a with hfa
  refine ⟨form (σ : E →+* E) J (γ *ᵥ eb) fa, ?_, fun w => ?_⟩
  · refine mem_of_pair (σ : E →+* E) hσ _ _ (FrameDual.dInv_ne_zero _) (FrameDual.dInv_ne_zero _)
      ((FrameDual.stab_dInv hσ _).inv hσ (FrameDual.dInv_ne_zero _)) _ ?_
    intro c hc c' hc'
    have h1 : c • eb ∈ Λ := hTup (Submodule.subset_span
      ⟨Fin.castAdd r b.castSucc, c, by rw [FrameDual.frameDualTupleIdeals_castAdd]; exact hc, by
        funext i; simp [heb, sideM]⟩)
    have h2 : c' • fa ∈ Λ := hTup (Submodule.subset_span
      ⟨Fin.natAdd (r + 1) a, c', by rw [FrameDual.frameDualTupleIdeals_natAdd]; exact hc', by
        funext i; simp [hfa, sideM]⟩)
    have h3 : γ *ᵥ (c • eb) ∈ Λ := by
      rw [← hγ.2]; exact ⟨_, h1, rfl⟩
    have h4 := (hSD.2 _).1 h3 _ h2
    rwa [Matrix.mulVec_smul, form_smul_smul] at h4
  · set τ := w.embedding with hτ
    have hB := hMod w
    have hdet : IsUnit (A w).det := by
      refine Ne.isUnit fun h0 => hND.2 ?_
      have := congrArg Matrix.det hB
      rw [Matrix.det_mul, Matrix.det_mul, h0, mul_zero, ← RingHom.mapMatrix_apply, ← RingHom.map_det] at this
      exact (map_eq_zero τ).1 this.symm
    have hsb : (s b : ℂ) ≠ 0 := by exact_mod_cast (hs b).ne'
    have hbv : bvec (eI k r b) = (s b : ℂ)⁻¹ • (A w *ᵥ fun i => τ (eb i)) := by
      rw [(hAd w b).1, smul_smul, inv_mul_cancel₀ hsb, one_smul]
    have hmap : (γ.map τ *ᵥ fun i => τ (eb i)) = fun i => τ ((γ *ᵥ eb) i) := by
      funext i; exact (RingHom.map_mulVec τ γ eb i).symm
    have hent : gM A γ w (eI k r a) (eI k r b) =
        (s b : ℂ)⁻¹ * (A w *ᵥ fun i => τ ((γ *ᵥ eb) i)) (eI k r a) := by
      have e1 : gM A γ w (eI k r a) (eI k r b) = (gM A γ w *ᵥ bvec (eI k r b)) (eI k r a) := by
        simp [bvec]
      rw [e1, hbv, Matrix.mulVec_smul, gM, Matrix.mulVec_mulVec, Matrix.mul_assoc (A w * γ.map τ),
        Matrix.nonsing_inv_mul _ hdet, Matrix.mul_one, ← Matrix.mulVec_mulVec, hmap]
      rfl
    show gM A γ w (eI k r a) (eI k r b) = _
    rw [hent, coord_eI (σ : E →+* E) τ (hconj τ) J (A w) hB (γ *ᵥ eb) fa a (s a) (hs a).ne' (hAd w a).2]
    push_cast
    ring
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.IntegralUnipotentMemModelUnipotentAtPlace
section
open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgAlg GlobalTheory.SgGlob GlobalTheory.SnMass GlobalTheory.SnMass.VolN
open scoped TensorProduct ENNReal nonZeroDivisors

noncomputable section

namespace GlobalTheory.SnMass.VolN

theorem map_cT_of_conj {E : Type} [Field E] (σ : E →+* E) (τ : E →+* ℂ) (hτ : ∀ x, τ (σ x) = star (τ x))
    {a b : Type} (M : Matrix a b E) : (cT σ M).map τ = (M.map τ)ᴴ := by
  ext i j
  simp [cT, Matrix.conjTranspose_apply, hτ]

theorem gM_mem_Nset (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (k r : ℕ) (J : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) E)
    (Λ : Submodule (𝓞 E) (Fin (2 * r + k + 1) → E)) (P : Matrix (Fin (2 * r + k + 1)) (Fin (r + 1)) E)
    (f : Matrix (Fin (2 * r + k + 1)) (Fin r) E) (T : F)
    (A : InfinitePlace E → Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (s : Fin r → ℝ) :
    IsVolData σ J Λ P f T A s → ∀ γ ∈ GN (σ : E →+* E) J Λ P, ∀ w, gM A γ w ∈ Nset k r := by
  intro hV γ hγ w
  obtain ⟨hCM, -, hJ, -, -, hD, -, hM, hs, hAd⟩ := hV
  obtain ⟨⟨hU, ⟨ν, hν, hγe⟩, hX⟩, -⟩ := hγ
  set τ := w.embedding with hτdef
  have hτ : ∀ x, τ ((σ : E →+* E) x) = star (τ x) := fun x => hCM.2.2.2 τ x
  set B := A w with hBdef
  set G := γ.map τ with hGdef
  set H := Hpk k r with hHdef
  set Ew := (eOf P).map τ with hEwdef
  have hJw : Bᴴ * H * B = J.map τ := hM w

  have hdet : B.det ≠ 0 := by
    intro h0
    have h1 := congrArg Matrix.det hJw
    rw [Matrix.det_mul, Matrix.det_mul, h0, mul_zero] at h1
    have h2 : τ J.det = (J.map τ).det := by rw [RingHom.map_det]; rfl
    exact hJ.2 ((map_eq_zero τ).1 (h2.trans h1.symm))
  have hBu : IsUnit B.det := isUnit_iff_ne_zero.mpr hdet
  have hBB : B * B⁻¹ = 1 := Matrix.mul_nonsing_inv B hBu
  have hBiB : B⁻¹ * B = 1 := Matrix.nonsing_inv_mul B hBu

  have hGU : Gᴴ * J.map τ * G = J.map τ := by
    have h1 := congrArg (fun M => M.map τ) hU
    simp only [IsUn, Matrix.map_mul, map_cT_of_conj _ τ hτ] at h1
    exact h1

  set S : Matrix (Fin (2 * r + k + 1)) (Fin r) ℂ := Matrix.of fun i a => (s a : ℂ) * bvec (eI k r a) i with hSdef
  have hAE : B * Ew = S := by
    ext i a
    have h1 := congrFun (hAd w a).1 i
    simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct, Ew, eOf, S] using h1
  have hgM : gM A γ w = B * G * B⁻¹ := rfl
  refine ⟨?_, ?_, ?_⟩
  ·
    show (gM A γ w)ᴴ * H * gM A γ w = H
    rw [hgM]
    calc (B * G * B⁻¹)ᴴ * H * (B * G * B⁻¹) = (B⁻¹)ᴴ * (Gᴴ * (Bᴴ * H * B) * G) * B⁻¹ := by
          simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = (B⁻¹)ᴴ * (Bᴴ * H * B) * B⁻¹ := by rw [hJw, hGU]
      _ = (B * B⁻¹)ᴴ * H * (B * B⁻¹) := by simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = H := by rw [hBB]; simp
  ·
    have hGE : G * Ew = Ew * ν.map τ := by
      show γ.map τ * (eOf P).map τ = (eOf P).map τ * ν.map τ
      rw [← Matrix.map_mul, ← Matrix.map_mul, hγe]
      rfl
    have hgS : gM A γ w * S = S * ν.map τ := by
      rw [hgM, ← hAE]
      calc B * G * B⁻¹ * (B * Ew) = B * G * (B⁻¹ * B) * Ew := by simp only [Matrix.mul_assoc]
        _ = B * (G * Ew) := by rw [hBiB, Matrix.mul_one, Matrix.mul_assoc]
        _ = B * Ew * ν.map τ := by rw [hGE, Matrix.mul_assoc]
    intro b i hbi
    have h1 := congrFun (congrFun hgS i) b
    have hl : (gM A γ w * S) i b = gM A γ w i (eI k r b) * (s b : ℂ) := by
      simp [S, Matrix.mul_apply, bvec, Pi.single_apply]
    have hr : (S * ν.map τ) i b = (s b : ℂ) * (if i = eI k r b then 1 else 0) := by
      rw [Matrix.mul_apply, Finset.sum_eq_single b]
      · simp [S, bvec, Pi.single_apply, (hν b b).2 rfl]
      · intro a _ hab
        by_cases hia : i = eI k r a
        · have hba : b < a := by
            have : b.val ≤ a.val := by rw [hia] at hbi; exact hbi
            exact lt_of_le_of_ne this (fun h => hab h.symm)
          simp [(hν a b).1 hba]
        · simp [S, bvec, Pi.single_apply, hia]
      · simp
    rw [hl, hr] at h1
    have hs0 : (s b : ℂ) ≠ 0 := by exact_mod_cast (hs b).ne'
    have h2 := mul_right_cancel₀ hs0 (h1.trans (mul_comm _ _))
    exact h2
  ·
    have hH : ∀ (a : Fin r) (j : Fin (2 * r + k + 1)), r ≤ j.val → j.val ≤ r + k → H (eI k r a) j = 0 := by
      intro a j h1 h2
      have ha := a.isLt
      have hv : (eI k r a).val = a.val := rfl
      show Hpk k r (eI k r a) j = 0
      unfold Hpk
      rw [if_neg (by rw [hv]; omega), if_neg (by omega), if_neg (fun h => absurd h.1 (by rw [hv]; omega))]
    set K := cT (σ : E →+* E) (eOf P) * J with hKdef
    have hKf : K * f = 1 := by
      ext a b
      have h1 := congrFun (congrFun hD.1 a.castSucc) b
      simp only [pairM, K, cT, eOf, Matrix.mul_apply, Matrix.map_apply, Matrix.transpose_apply,
        Matrix.submatrix_apply, id, Matrix.of_apply, Matrix.one_apply] at h1 ⊢
      rw [h1]
      simp [Fin.castSucc_inj]
    set Q := 1 - f * K with hQdef
    have hKQ : K * Q = 0 := by
      rw [hQdef, Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc, hKf, Matrix.one_mul, sub_self]
    have hcol : ∀ j, ∃ c, γ *ᵥ (Q *ᵥ Pi.single j 1) - Q *ᵥ Pi.single j 1 = eOf P *ᵥ c := by
      intro j
      apply hX
      rw [Matrix.mulVec_mulVec, hKQ, Matrix.zero_mulVec]
    choose c hc using hcol
    set C : Matrix (Fin r) (Fin (2 * r + k + 1)) E := Matrix.of fun a j => c j a with hCdef
    have hsj : ∀ (M : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) E) i j, (M *ᵥ Pi.single j 1) i = M i j := by
      intro M i j
      simp [Matrix.mulVec, dotProduct, Pi.single_apply]
    have hQC : (γ - 1) * Q = eOf P * C := by
      ext i j
      have h1 := congrFun (hc j) i
      rw [Matrix.mulVec_mulVec, ← Matrix.sub_mulVec] at h1
      have e1 : γ * Q - Q = (γ - 1) * Q := by rw [Matrix.sub_mul, Matrix.one_mul]
      rw [e1, hsj] at h1
      rw [h1, Matrix.mul_apply]
      simp [Matrix.mulVec, dotProduct, C]
    set fw := f.map τ with hfwdef
    set Kw := Ewᴴ * J.map τ with hKwdef
    have hQw : (G - 1) * (1 - fw * Kw) = Ew * C.map τ := by
      have h1 := congrArg τ.mapMatrix hQC
      rw [map_mul, map_sub, map_one, hQdef, map_sub, map_one] at h1
      simp only [RingHom.mapMatrix_apply, Matrix.map_mul, hKdef, map_cT_of_conj _ τ hτ] at h1
      exact h1
    have hKB : Kw * B⁻¹ = Sᴴ * H := by
      show Ewᴴ * J.map τ * B⁻¹ = Sᴴ * H
      rw [← hJw, ← hAE]
      simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      rw [hBB, Matrix.mul_one]
    have hdecomp : gM A γ w - 1 = S * (C.map τ * B⁻¹) + B * (G - 1) * fw * (Sᴴ * H) := by
      have e1 : gM A γ w - 1 = B * (G - 1) * B⁻¹ := by
        rw [hgM, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, hBB]
      rw [e1]
      calc B * (G - 1) * B⁻¹ = B * (G - 1) * ((1 - fw * Kw) + fw * Kw) * B⁻¹ := by
            rw [sub_add_cancel, Matrix.mul_one]
        _ = B * ((G - 1) * (1 - fw * Kw)) * B⁻¹ + B * (G - 1) * fw * (Kw * B⁻¹) := by
            rw [Matrix.mul_add, Matrix.add_mul]; simp only [Matrix.mul_assoc]
        _ = S * (C.map τ * B⁻¹) + B * (G - 1) * fw * (Sᴴ * H) := by
            rw [hQw, hKB, ← hAE]; simp only [Matrix.mul_assoc]
    intro i j hj1 hj2 hi
    have h1 := congrFun (congrFun hdecomp i) j
    rw [Matrix.sub_apply, Matrix.add_apply, Matrix.one_apply] at h1
    have z1 : (S * (C.map τ * B⁻¹)) i j = 0 := by
      rw [Matrix.mul_apply]
      refine Finset.sum_eq_zero fun a _ => ?_
      have hia : i ≠ eI k r a := fun h => by
        have ha := a.isLt
        rw [h] at hi
        exact absurd hi (show ¬ r ≤ a.val by omega)
      simp [S, bvec, Pi.single_apply, hia]
    have z2 : (B * (G - 1) * fw * (Sᴴ * H) : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) i j = 0 := by
      rw [Matrix.mul_apply]
      refine Finset.sum_eq_zero fun a _ => ?_
      have h3 : (Sᴴ * H : Matrix (Fin r) (Fin (2 * r + k + 1)) ℂ) a j = 0 := by
        rw [Matrix.mul_apply]
        refine Finset.sum_eq_zero fun l _ => ?_
        by_cases hl : l = eI k r a
        · subst hl
          rw [hH a j hj1 hj2, mul_zero]
        · simp [S, bvec, Pi.single_apply, hl, Matrix.conjTranspose_apply]
      rw [h3, mul_zero]
    rw [z1, z2, add_zero] at h1
    exact sub_eq_zero.1 h1

end GlobalTheory.SnMass.VolN

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsHaarMeasureOfSigmaFinite
section
open MeasureTheory
open scoped ENNReal NNReal

noncomputable section

namespace GlobalTheory.SnMass.ProdQuot

theorem isHaarMeasure_of_sigmaFinite {H : Type} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H] [LocallyCompactSpace H] (ν : Measure H)
    [SigmaFinite ν] [ν.IsMulLeftInvariant] (hν : ν ≠ 0) : ν.IsHaarMeasure := by
  obtain ⟨K⟩ : Nonempty (TopologicalSpace.PositiveCompacts H) := inferInstance
  have e := Measure.haarMeasure_unique ν K
  rw [e]
  refine Measure.IsHaarMeasure.smul _ (fun hc => hν (by rw [e, hc, zero_smul])) fun hc => hν ?_
  rw [← Measure.measure_univ_eq_zero, ← iUnion_spanningSets ν]
  refine measure_iUnion_null fun n => ?_
  have h1 := measure_spanningSets_lt_top ν n
  have h2 : ν (spanningSets ν n) = ⊤ * Measure.haarMeasure K (spanningSets ν n) := by
    have := congrArg (fun ρ : Measure H => ρ (spanningSets ν n)) e
    simpa [hc] using this
  by_cases h3 : Measure.haarMeasure K (spanningSets ν n) = 0
  · rw [h2, h3, mul_zero]
  · rw [h2, ENNReal.top_mul h3] at h1
    exact absurd h1 (lt_irrefl _)

theorem exists_cutoff {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
    [T2Space G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (R : Subgroup G) (μ : Measure G)
    [SigmaFinite μ] (hR : IsClosed (R : Set G)) (h0 : μ ≠ 0) (hc : μ (R : Set G)ᶜ = 0)
    (hi : ∀ s ∈ R, μ.map (fun x => s * x) = μ ∧ μ.map (fun x => x * s) = μ) :
    ∃ b : G → ℝ≥0, Measurable b ∧ ∀ g, ∫⁻ s, (b (s * g) : ℝ≥0∞) ∂μ = 1 := by
  have hce : Topology.IsClosedEmbedding R.subtype := hR.isClosedEmbedding_subtypeVal
  have hφ : MeasurableEmbedding R.subtype := hce.measurableEmbedding
  haveI : LocallyCompactSpace R := hce.locallyCompactSpace
  haveI : SecondCountableTopology R := hce.isEmbedding.secondCountableTopology
  have h2 : (μ.comap R.subtype).map R.subtype = μ := by
    rw [hφ.map_comap]
    refine Measure.restrict_eq_self_of_ae_mem ?_
    have : Set.range R.subtype = (R : Set G) := Subtype.range_coe
    rw [this]
    exact hc
  set ν : Measure R := μ.comap R.subtype with hν
  haveI : SigmaFinite ν := SigmaFinite.of_map _ hφ.measurable.aemeasurable (by rwa [h2])
  haveI : ν.IsMulLeftInvariant := ⟨fun g => by
    apply hφ.map_injective
    have hm : Measurable fun x : G => (g : G) * x := measurable_const_mul _
    rw [Measure.map_map hφ.measurable (measurable_const_mul g), h2]
    conv_rhs => rw [← (hi g g.2).1, ← h2, Measure.map_map hm hφ.measurable]
    rfl⟩
  haveI : ν.IsMulRightInvariant := ⟨fun g => by
    apply hφ.map_injective
    have hm : Measurable fun x : G => x * (g : G) := measurable_mul_const _
    rw [Measure.map_map hφ.measurable (measurable_mul_const g), h2]
    conv_rhs => rw [← (hi g g.2).2, ← h2, Measure.map_map hm hφ.measurable]
    rfl⟩
  haveI : ν.IsHaarMeasure := isHaarMeasure_of_sigmaFinite ν fun h => h0 (by rw [← h2, h, Measure.map_zero])
  obtain ⟨b, hb, h1⟩ := GlobalTheory.exists_measurable_lintegral_coset_eq_one G R ν R.subtype hce
  refine ⟨fun x => (b x).toNNReal, hb.ennreal_toNNReal, fun g => ?_⟩
  have hm : Measurable fun s => b (s * g) := hb.comp (measurable_mul_const g)
  have h3 : ∫⁻ s, b (s * g) ∂μ = 1 := by
    rw [← h2, hφ.lintegral_map]
    exact h1 g
  rw [← h3]
  refine lintegral_congr_ae ?_
  filter_upwards [ae_lt_top hm (by rw [h3]; exact ENNReal.one_ne_top)] with s hs
  exact ENNReal.coe_toNNReal hs.ne

theorem map_eq {G : Type} [Group G] [MeasurableSpace G] (μG μ ν : Measure G) {b : G → ℝ≥0} (hb : Measurable b)
    (h1 : ∀ g, ∫⁻ s, (b (s * g) : ℝ≥0∞) ∂μ = 1)
    (hν : ∀ f : G → ℝ≥0∞, Measurable f → ∫⁻ x, f x ∂μG = ∫⁻ x, ∫⁻ s, f (s * x) ∂μ ∂ν)
    {F : G → ℂ} (hF : Measurable F) (hi : ∀ᵐ s ∂μ, ∀ x, F (s * x) = F x) :
    ν.map F = (μG.withDensity fun x => b x).map F := by
  have hb' : Measurable fun x => (b x : ℝ≥0∞) := hb.coe_nnreal_ennreal
  ext A hA
  rw [Measure.map_apply hF hA, Measure.map_apply hF hA, withDensity_apply _ (hF hA),
    ← lintegral_indicator (hF hA), hν _ (hb'.indicator (hF hA)), ← lintegral_indicator_one (hF hA)]
  refine lintegral_congr fun x => ?_
  by_cases hx : x ∈ F ⁻¹' A
  · rw [Set.indicator_of_mem hx, Pi.one_apply, ← h1 x]
    refine lintegral_congr_ae ?_
    filter_upwards [hi] with s hs
    rw [Set.indicator_of_mem (by simpa [hs] using hx)]
  · rw [Set.indicator_of_notMem hx, ← lintegral_zero (μ := μ)]
    refine lintegral_congr_ae ?_
    filter_upwards [hi] with s hs
    rw [Set.indicator_of_notMem (by simpa [hs] using hx)]

theorem integral_eq {G : Type} [Group G] [MeasurableSpace G] (μG μ ν : Measure G) {b : G → ℝ≥0} (hb : Measurable b)
    (h1 : ∀ g, ∫⁻ s, (b (s * g) : ℝ≥0∞) ∂μ = 1)
    (hν : ∀ f : G → ℝ≥0∞, Measurable f → ∫⁻ x, f x ∂μG = ∫⁻ x, ∫⁻ s, f (s * x) ∂μ ∂ν)
    {F : G → ℂ} (hF : Measurable F) (hi : ∀ᵐ s ∂μ, ∀ x, F (s * x) = F x) :
    ∫ x, F x ∂ν = ∫ x, (b x : ℂ) * F x ∂μG ∧ (Integrable F ν ↔ Integrable (fun x => (b x : ℂ) * F x) μG) := by
  have h := map_eq μG μ ν hb h1 hν hF hi
  have e : (fun x => (b x : ℂ) * F x) = fun x => b x • F x := by
    ext x
    simp [NNReal.smul_def]
  have hid : ∀ ρ : Measure ℂ, AEStronglyMeasurable (fun z : ℂ => z) ρ := fun ρ => continuous_id.aestronglyMeasurable
  rw [e]
  constructor
  · rw [← integral_withDensity_eq_integral_smul hb, ← integral_map hF.aemeasurable (hid _),
      ← integral_map hF.aemeasurable (hid _), h]
  · rw [← integrable_withDensity_iff_integrable_smul hb]
    have h2 := integrable_map_measure (μ := ν) (hid _) hF.aemeasurable
    have h3 := integrable_map_measure (μ := μG.withDensity fun x => b x) (hid _) hF.aemeasurable
    rw [h] at h2
    exact h2.symm.trans h3

end GlobalTheory.SnMass.ProdQuot
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.NonzeroDefectHeightPowerAbsorbsConstants
section
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.HL.NonzeroDefect

theorem num_first (H q : ℝ) (hq : 2 ≤ q) (hH : 0 ≤ H) (r k : ℕ) :
    2 * H ^ (9 * (r + 1) ^ 2 + 12 * (r + 1)) * (4 * H ^ (4 * (r + 1))) * q ^ (-((k : ℤ) - 1)) ≤
      98 * H ^ (9 * (r + 1) ^ 2 + 12 * (r + 1)) * (4 * H ^ (4 * (r + 1))) * q ^ (-((k : ℤ) - 2 * r - 5)) := by
  have h1 : q ^ (-((k : ℤ) - 1)) ≤ q ^ (-((k : ℤ) - 2 * r - 5)) :=
    zpow_le_zpow_right₀ (by linarith) (by omega)
  have hq0 : 0 < q := by linarith
  gcongr
  norm_num

theorem num_second (H q : ℝ) (hq : 2 ≤ q) (hH : 0 ≤ H) (r k : ℕ) (hk : 4 * r + 7 ≤ k) :
    98 * H ^ (9 * (r + 1) ^ 2 + 12 * (r + 1)) * (4 * H ^ (4 * (r + 1))) *
        (q ^ (1 - ((k : ℤ) - 2 * r - 3))) ^ 2 ≤
      98 * H ^ (9 * (r + 1) ^ 2 + 12 * (r + 1)) * (4 * H ^ (4 * (r + 1))) * q ^ (-((k : ℤ) - 2 * r - 5)) := by
  have hq0 : 0 < q := by linarith
  have h1 : (q ^ (1 - ((k : ℤ) - 2 * r - 3))) ^ 2 ≤ q ^ (-((k : ℤ) - 2 * r - 5)) := by
    rw [← zpow_natCast, ← zpow_mul]
    exact zpow_le_zpow_right₀ (by linarith) (by push_cast; omega)
  gcongr

theorem nonzeroDefect_height_power_absorbs_constants (H : ℝ) (hH : 2 ≤ H) (r : ℕ) :
    H ^ (2 * (r + 2)) * (98 * H ^ (9 * (r + 1) ^ 2 + 12 * (r + 1)) * (4 * H ^ (4 * (r + 1)))) ≤
      H ^ (39 * (r + 1) ^ 2) := by
  have h0 : 0 < H := by linarith
  have h9 : (392 : ℝ) ≤ H ^ 9 := by
    calc (392 : ℝ) ≤ 2 ^ 9 := by norm_num
      _ ≤ H ^ 9 := by gcongr
  calc H ^ (2 * (r + 2)) * (98 * H ^ (9 * (r + 1) ^ 2 + 12 * (r + 1)) * (4 * H ^ (4 * (r + 1))))
      = 392 * (H ^ (2 * (r + 2)) * H ^ (9 * (r + 1) ^ 2 + 12 * (r + 1)) * H ^ (4 * (r + 1))) := by ring
    _ ≤ H ^ 9 * (H ^ (2 * (r + 2)) * H ^ (9 * (r + 1) ^ 2 + 12 * (r + 1)) * H ^ (4 * (r + 1))) := by gcongr
    _ = H ^ (9 + (2 * (r + 2) + (9 * (r + 1) ^ 2 + 12 * (r + 1)) + 4 * (r + 1))) := by
        simp only [pow_add H]
    _ ≤ H ^ (39 * (r + 1) ^ 2) := pow_le_pow_right₀ (by linarith) (by nlinarith [Nat.zero_le r])

theorem ampSq_nonzero_defect : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (r k : ℕ) (S : Frames L r k), 4 * r + 7 ≤ k → (S.ampSq fun d Λ => ¬ S.BBzero d Λ) ≤ ENNReal.ofReal (S.Hp ^ (39 * (r + 1) ^ 2) * (S.q : ℝ) ^ (-((k : ℤ) - 2 * r - 5))) * S.nn := by
  intro F _ _ _ _ _ E _ _ _ L r k S hk
  by_cases hex : ∃ d Λ, S.IsTerm d Λ ∧ ¬ S.BBzero d Λ
  · obtain ⟨d, Λ, hT, hB⟩ := hex
    have hq : (2 : ℝ) ≤ (S.q : ℝ) := by
      have := (GlobalTheory.UnramOrder.order_facts L S.ϖ S.ϖ_irr).2.2.2.2.2.2.1
      exact_mod_cast this
    have hqH : (S.q : ℝ) ≤ S.Hp := (GlobalTheory.HL.Defect.exponents_and_defect L r k S d Λ hT).2.2.2.2.2.2.2.1 hB
    have hH : (2 : ℝ) ≤ S.Hp := hq.trans hqH
    have hH0 : (0 : ℝ) ≤ S.Hp := by linarith
    have hq0 : (0 : ℝ) < (S.q : ℝ) := by linarith
    have key := GlobalTheory.T.ampSq_le_of_hermitianTermTypes_cauchySchwarz L r k S hk
      (ENNReal.ofReal (98 * S.Hp ^ (9 * (r + 1) ^ 2 + 12 * (r + 1)) * (4 * S.Hp ^ (4 * (r + 1))) *
        (S.q : ℝ) ^ (-((k : ℤ) - 2 * r - 5))) * S.nn)
      (fun β => (GlobalTheory.T.hermitianFrames_firstType_ampSq_bound L r k S hk β).trans
        (mul_le_mul_left (ENNReal.ofReal_le_ofReal (num_first _ _ hq hH0 r k)) _))
      (fun β J βJ => (GlobalTheory.T.hermitianDoubleCoset_secondType_family_ampSq_le L r k S hk β J βJ).trans
        (mul_le_mul_left (ENNReal.ofReal_le_ofReal (num_second _ _ hq hH0 r k hk)) _))
    refine key.trans ?_
    rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity), ← mul_assoc]
    refine mul_le_mul_left (ENNReal.ofReal_le_ofReal ?_) _
    exact mul_le_mul_of_nonneg_right (nonzeroDefect_height_power_absorbs_constants _ hH r) (by positivity)
  · have h0 : (S.ampSq fun d Λ => ¬ S.BBzero d Λ) = 0 := by
      have ha : ∀ d, S.amp d (fun Λ => ¬ S.BBzero d Λ) = 0 := by
        intro d
        unfold Frames.amp
        have : ∀ Λ, ¬ (S.IsTerm d Λ ∧ ¬ S.BBzero d Λ) := fun Λ h => hex ⟨d, Λ, h⟩
        simp only [this, if_false, tsum_zero]
      unfold Frames.ampSq Frames.sumData
      simp [ha]
    rw [h0]
    exact zero_le

end GlobalTheory.HL.NonzeroDefect
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.TermDatumOrbitUniqueStatement
section
open ValuativeRel Formalism.MainNotions.S Formalism.MainNotions.S.Loc Formalism.MainNotions.S.LocNG GlobalTheory.LocOver
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.term_datum_orbit_unique : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E] (M : Model F E), M.OK → ∀ {V : Type} [AddCommGroup V] [Module E V] (H : HermSp M V) (r : ℕ), ∀ (k : ℕ) (P : FPair H r), Module.finrank E V = k + 2 * r + 1 → P.RelG (theta M) → ∀ (d d' : Datum P) (t : Term V M r), Over P d t → Over P d' t → Datum.Rel d d' := by
  first | exact @GlobalTheory.LocOver.orbit_over_unique | exact GlobalTheory.LocOver.orbit_over_unique | (intros; apply GlobalTheory.LocOver.orbit_over_unique <;> assumption)
end

