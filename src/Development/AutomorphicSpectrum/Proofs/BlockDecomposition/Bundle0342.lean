import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IsotropicMahlerBounds.LogAbsoluteWedges.LogAbsBasic
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0004
import GroundTheory.AutomorphicForms.Bundle0020
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0328
import Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.FormUniq
import Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.NLeA
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.Imports
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.Bundle0002
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HodgeXD
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0329
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.SiegelWeilOrbitalMeasure
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0320
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0330
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ArtinReesClosedSystem

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OnlyIsotropicSubspaces
section
open NumberField Matrix PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.D1
open GlobalTheory.CuspRep PositivityTheory.Rg.Tf.Loc

namespace GlobalTheory.CompanionTheory.IsotropicDegreeBound

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

theorem conjE_conjE (a : E) : conjE E (conjE E a) = a :=
  IsCMField.complexConj_apply_apply E a

theorem mem_perpD_iff (d : GL (Fin n) E) (W : Submodule E (Fin n → E)) (y : Fin n → E) :
    y ∈ perpD (conjE E) d W ↔ ∀ x ∈ W, (conjE E ∘ x) ⬝ᵥ ((d⁻¹).val *ᵥ y) = 0 := by
  have key : y ∈ perpD (conjE E) d W ↔ (d⁻¹).val *ᵥ y ∈ perp (conjE E) W := by
    constructor
    · rintro ⟨z, hz, rfl⟩
      have : (d⁻¹).val *ᵥ (Matrix.toLin' d.val z) = z := by
        rw [Matrix.toLin'_apply, Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one,
          Matrix.one_mulVec]
      rw [this]
      exact hz
    · intro h
      refine ⟨_, h, ?_⟩
      rw [Matrix.toLin'_apply, Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one,
        Matrix.one_mulVec]
  rw [key]
  exact Iff.rfl

theorem gram_nrm (d : GL (Fin n) E) :
    ((nrm d).val.map (conjE E))ᵀ * (d⁻¹).val * (nrm d).val = (d⁻¹).val := by
  set D := d.val with hD
  set Di := (d⁻¹).val with hDi
  have hval : (nrm d).val = D * (Di.map (conjE E))ᵀ := by
    simp only [nrm, Units.val_mul]
    rfl
  have hinv : Di * D = 1 := by
    rw [hDi, hD, ← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hc : (Di.map (conjE E)) * (D.map (conjE E)) = 1 := by
    rw [← Matrix.map_mul, hinv, Matrix.map_one _ (map_zero _) (map_one _)]
  have hcc : (Di.map (conjE E)).map (conjE E) = Di := by
    ext i j
    simp [conjE_conjE]
  have hm : ((nrm d).val.map (conjE E))ᵀ = Di * (D.map (conjE E))ᵀ := by
    rw [hval, Matrix.map_mul, Matrix.transpose_mul, Matrix.transpose_map, Matrix.transpose_transpose, hcc]
  rw [hm, hval]
  calc Di * (D.map (conjE E))ᵀ * Di * (D * (Di.map (conjE E))ᵀ)
      = Di * (D.map (conjE E))ᵀ * (Di * D) * (Di.map (conjE E))ᵀ := by
        simp only [Matrix.mul_assoc]
    _ = Di * ((Di.map (conjE E)) * (D.map (conjE E)))ᵀ := by
        rw [hinv, Matrix.transpose_mul, Matrix.mul_one, Matrix.mul_assoc]
    _ = Di := by rw [hc, Matrix.transpose_one, Matrix.mul_one]

theorem pairing_nrm (d : GL (Fin n) E) (u v : Fin n → E) :
    (conjE E ∘ ((nrm d).val *ᵥ u)) ⬝ᵥ ((d⁻¹).val *ᵥ ((nrm d).val *ᵥ v)) =
      (conjE E ∘ u) ⬝ᵥ ((d⁻¹).val *ᵥ v) := by
  have h1 : conjE E ∘ ((nrm d).val *ᵥ u) = ((nrm d).val.map (conjE E)) *ᵥ (conjE E ∘ u) := by
    funext i
    exact RingHom.map_mulVec (conjE E) (nrm d).val u i
  rw [h1, ← Matrix.vecMul_transpose, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec,
    gram_nrm]

theorem img_nrm_inf (d : GL (Fin n) E) (W : Submodule E (Fin n → E)) (hW : img (nrm d) W = W) :
    img (nrm d) (W ⊓ perpD (conjE E) d W) = W ⊓ perpD (conjE E) d W := by
  have hinj : Function.Injective (Matrix.toLin' (nrm d).val) := by
    intro a b hab
    have h := congrArg (fun z => ((nrm d)⁻¹).val *ᵥ z) hab
    simpa [Matrix.toLin'_apply, Matrix.mulVec_mulVec, ← Units.val_mul] using h
  have hle : img (nrm d) (W ⊓ perpD (conjE E) d W) ≤ W ⊓ perpD (conjE E) d W := by
    rintro _ ⟨y, ⟨hyW, hyP⟩, rfl⟩
    refine ⟨?_, ?_⟩
    · have : Matrix.toLin' (nrm d).val y ∈ img (nrm d) W := ⟨y, hyW, rfl⟩
      rwa [hW] at this
    · rw [SetLike.mem_coe, mem_perpD_iff]
      intro x hx
      rw [← hW] at hx
      obtain ⟨x', hx', rfl⟩ := hx
      rw [Matrix.toLin'_apply, Matrix.toLin'_apply, pairing_nrm]
      exact (mem_perpD_iff d W y).1 hyP x' hx'
  refine Submodule.eq_of_le_of_finrank_eq hle ?_
  exact (Submodule.equivMapOfInjective _ hinj _).finrank_eq.symm

theorem inf_le_perpD_inf (d : GL (Fin n) E) (W : Submodule E (Fin n → E)) :
    W ⊓ perpD (conjE E) d W ≤ perpD (conjE E) d (W ⊓ perpD (conjE E) d W) := by
  intro y hy
  rw [mem_perpD_iff]
  exact fun x hx => (mem_perpD_iff d W y).1 hy.2 x hx.1

theorem prof_gap {τ : ℝ} (hτ : 0 ≤ τ) {a b m : ℕ} (hab : a < b) (hbm : b ≤ m) :
    prof m τ a + 2 * τ ≤ prof m τ b := by
  have h1 : (a : ℝ) + 1 ≤ b := by exact_mod_cast hab
  have h2 : (b : ℝ) ≤ m := by exact_mod_cast hbm
  have h3 : (2 : ℝ) ≤ ((b : ℝ) - a) * (2 * m + 1 - a - b) := by
    nlinarith [mul_nonneg (sub_nonneg.2 h1) (by linarith : (0 : ℝ) ≤ 2 * m - 1 - a - b)]
  have h4 := mul_nonneg hτ (sub_nonneg.2 h3)
  simp only [prof]
  nlinarith

theorem onlyIsotropic_of : OnlyStable → DegPairing → SizeBasic → OnlyIsotropic := by
  intro h1 h2 h3 E _ _ _ n
  obtain ⟨C₁, hC₁⟩ := h1 E n
  obtain ⟨C₂, hC₂⟩ := h2 E n
  refine ⟨max 0 (max C₁ C₂), fun τ x d hτ => ?_⟩
  have hs0 : 0 ≤ logSize (twConj (thetaA E n) x (ratGL E n d)) := (h3 E n).2.1 _
  have hs1 : 0 ≤ 1 + logSize (twConj (thetaA E n) x (ratGL E n d)) := by linarith
  have l₁ : C₁ ≤ max 0 (max C₁ C₂) := (le_max_left _ _).trans (le_max_right _ _)
  have l₂ : C₂ ≤ max 0 (max C₁ C₂) := (le_max_right _ _).trans (le_max_right _ _)
  have hτ₁ := le_trans (mul_le_mul_of_nonneg_right l₁ hs1) hτ
  have hτ₂ := le_trans (mul_le_mul_of_nonneg_right l₂ hs1) hτ
  have hτ₀ : 0 ≤ τ := le_trans (mul_nonneg (le_max_left _ _) hs1) hτ
  refine ⟨fun hx W _ _ => hx.1 W, fun h => (hC₁ τ x d hτ₁).2 fun W hW => ?_⟩
  have hb := h _ (img_nrm_inf d W hW) (inf_le_perpD_inf d W)
  by_cases heq : W ⊓ perpD (conjE E) d W = W
  · exact h W hW (inf_eq_left.1 heq)
  · have hlt : W ⊓ perpD (conjE E) d W < W := lt_of_le_of_ne inf_le_left heq
    have hr := Submodule.finrank_lt_finrank_of_lt hlt
    have hn : Module.finrank E W ≤ n := by simpa using Submodule.finrank_le W
    have hg := prof_gap hτ₀ hr hn
    have hp := (hC₂ x d).1 W hW
    linarith

end GlobalTheory.CompanionTheory.IsotropicDegreeBound
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OnlyStableSubspaces
section
open Matrix PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.D1

open NumberField IsDedekindDomain
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.Tf.Loc

namespace GlobalTheory.CompanionTheory.OnlyStab

section Core

variable {K : Type} [Field K] {n : ℕ}

theorem prof_nonneg {τ : ℝ} (hτ : 0 ≤ τ) {k : ℕ} (hk : k ≤ n) : 0 ≤ prof n τ k := by
  have h : (k : ℝ) ≤ n := by exact_mod_cast hk
  have h0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  unfold prof
  exact mul_nonneg (mul_nonneg hτ h0) (by linarith)

theorem finrank_le_n (W : Submodule K (Fin n → K)) : Module.finrank K W ≤ n := by
  simpa using Submodule.finrank_le W

theorem prof_second_diff (τ : ℝ) (a b k : ℕ) (hab : a + b = 2 * k) :
    prof n τ a + prof n τ b = 2 * prof n τ k - 2 * τ * ((k : ℝ) - a) ^ 2 := by
  have h : (b : ℝ) = 2 * k - a := by
    have : ((a + b : ℕ) : ℝ) = ((2 * k : ℕ) : ℝ) := by rw [hab]
    push_cast at this
    linarith
  unfold prof
  rw [h]
  ring

theorem core (deg' : Submodule K (Fin n → K) → ℝ) (g : Submodule K (Fin n → K) → Submodule K (Fin n → K))
    (τ D : ℝ) (hτ : 0 < τ) (hD : D < 2 * τ) (hbdd : BddAbove (Set.range deg'))
    (hsub : ∀ W W', deg' W + deg' W' ≤ deg' (W ⊓ W') + deg' (W ⊔ W'))
    (hmove : ∀ W, deg' W - D ≤ deg' (g W))
    (hrank : ∀ W, Module.finrank K (g W) = Module.finrank K W)
    (hst : ∀ W, g W = W → deg' W ≤ prof n τ (Module.finrank K W)) (W₀ : Submodule K (Fin n → K)) :
    deg' W₀ ≤ prof n τ (Module.finrank K W₀) := by
  by_contra hW₀
  push Not at hW₀
  set ψ : Submodule K (Fin n → K) → ℝ := fun W => deg' W - prof n τ (Module.finrank K W) with hψ
  have hψb : BddAbove (Set.range ψ) := by
    obtain ⟨B, hB⟩ := hbdd
    refine ⟨B, ?_⟩
    rintro _ ⟨W, rfl⟩
    have h1 : deg' W ≤ B := hB ⟨W, rfl⟩
    have h2 := prof_nonneg (n := n) hτ.le (finrank_le_n W)
    simp only [hψ]
    linarith
  set s : ℝ := ⨆ W, ψ W with hs
  have hle : ∀ W, ψ W ≤ s := fun W => le_ciSup hψb W
  have hs0 : 0 < s := lt_of_lt_of_le (by simp only [hψ]; linarith) (hle W₀)
  have hε : 0 < min s (τ - D / 2) := lt_min hs0 (by linarith)
  obtain ⟨W, hW⟩ : ∃ W, s - min s (τ - D / 2) < ψ W :=
    exists_lt_of_lt_ciSup (by rw [hs]; linarith [hε])
  have hε1 : min s (τ - D / 2) ≤ s := min_le_left _ _
  have hε2 : min s (τ - D / 2) ≤ τ - D / 2 := min_le_right _ _
  by_cases hg : g W = W
  · have h := hst W hg
    simp only [hψ] at hW
    linarith
  · have hsum := Submodule.finrank_sup_add_finrank_inf_eq W (g W)
    rw [hrank W] at hsum
    have hne : W ⊓ g W ≠ W := fun h => hg
      (Submodule.eq_of_le_of_finrank_le (inf_eq_left.1 h) (by rw [hrank W])).symm
    have hlt : Module.finrank K (W ⊓ g W : Submodule K (Fin n → K)) < Module.finrank K W :=
      Submodule.finrank_lt_finrank_of_lt (lt_of_le_of_ne inf_le_left hne)
    have hid := prof_second_diff (n := n) τ (Module.finrank K (W ⊓ g W : Submodule K (Fin n → K)))
      (Module.finrank K (W ⊔ g W : Submodule K (Fin n → K))) (Module.finrank K W) (by omega)
    have hj : (1 : ℝ) ≤ (Module.finrank K W : ℝ) - Module.finrank K (W ⊓ g W : Submodule K (Fin n → K)) := by
      have : ((Module.finrank K (W ⊓ g W : Submodule K (Fin n → K)) + 1 : ℕ) : ℝ) ≤ Module.finrank K W := by
        exact_mod_cast hlt
      push_cast at this
      linarith
    have hj2 : τ * 1 ≤ τ * ((Module.finrank K W : ℝ) - Module.finrank K (W ⊓ g W : Submodule K (Fin n → K))) ^ 2 :=
      mul_le_mul_of_nonneg_left (by nlinarith) hτ.le
    have h1 := hle (W ⊓ g W)
    have h2 := hle (W ⊔ g W)
    have h3 := hsub W (g W)
    have h4 := hmove W
    simp only [hψ] at h1 h2 hW
    linarith

end Core

section Global

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

theorem finrank_img (g : GL (Fin n) E) (W : Submodule E (Fin n → E)) :
    Module.finrank E (img g W) = Module.finrank E W := by
  have hinj : Function.Injective (Matrix.toLin' g.val) := by
    intro a b hab
    have h : (g⁻¹ : GL (Fin n) E).val *ᵥ (g.val *ᵥ a) = (g⁻¹ : GL (Fin n) E).val *ᵥ (g.val *ᵥ b) := by
      simpa [Matrix.toLin'_apply] using congrArg (fun y => (g⁻¹ : GL (Fin n) E).val *ᵥ y) hab
    simpa [Matrix.mulVec_mulVec, ← Units.val_mul] using h
  exact LinearEquiv.finrank_eq (Submodule.equivMapOfInjective _ hinj W).symm

theorem conjSrc_invol (v : HeightOneSpectrum (𝓞 E)) :
    conjSrc (IsCMField.complexConj E).toRingEquiv (conjSrc (IsCMField.complexConj E).toRingEquiv v) = v :=
  (eq_conjSrc fun x => by
    rw [← conjPl_conjSrc (IsCMField.complexConj E).toRingEquiv v ((IsCMField.complexConj E).toRingEquiv x)]
    exact congrArg _ (IsCMField.complexConj_apply_apply E x)).symm

theorem conjFin_invol (x : Af E) :
    conjFin (IsCMField.complexConj E).toRingEquiv (conjFin (IsCMField.complexConj E).toRingEquiv x) = x := by
  have key : ∀ (v w : HeightOneSpectrum (𝓞 E)) (_ : w = v) (f : w.adicCompletion E → v.adicCompletion E),
      Continuous f → (∀ k : E, f (algebraMap E _ k) = algebraMap E _ k) → f (pLoc E w x) = pLoc E v x := by
    rintro _ v rfl f hf h
    exact congrFun ((HeightOneSpectrum.denseRange_algebraMap (K := E) v).equalizer hf continuous_id (funext h)) _
  refine FiniteAdeleRing.ext _ fun v => key v _ (conjSrc_invol v) (conjLoc _ v ∘ conjLoc _ _)
    ((conjLoc_spec _ _).1.comp (conjLoc_spec _ _).1) fun k => ?_
  rw [Function.comp_apply, (conjLoc_spec _ _).2.1, (conjLoc_spec _ _).2.1]
  exact congrArg _ (IsCMField.complexConj_apply_apply E k)

theorem pInf_conj (x : Ad E) : pInf E (conjAd E x) = starRingEnd (Cinf E) (pInf E x) :=
  (infEq E).symm_apply_apply _

theorem conjAd_invol (x : Ad E) : conjAd E (conjAd E x) = x :=
  ad_ext (by rw [pInf_conj, pInf_conj, starRingEnd_self_apply]) (conjFin_invol _)

theorem thetaA_invol (x : GA E n) : thetaA E n (thetaA E n x) = x := by
  refine Units.ext ?_
  ext i j
  change conjAd E (conjAd E (x.val i j)) = x.val i j
  exact conjAd_invol _

theorem ratGL_thetaE (d : GL (Fin n) E) : ratGL E n (thetaE E n d) = thetaA E n (ratGL E n d) := by
  refine Units.ext ?_
  ext i j
  have h : ((ratGL E n d)⁻¹ : GA E n) = ratGL E n d⁻¹ := (map_inv _ _).symm
  rw [thetaR_val, h]
  change algebraMap E (Ad E) (conjE E ((d⁻¹ : GL (Fin n) E).val j i)) =
    conjAd E (algebraMap E (Ad E) ((d⁻¹ : GL (Fin n) E).val j i))
  rw [conjAd_algebraMap]
  rfl

theorem conj_nrm (x : GA E n) (d : GL (Fin n) E) :
    x⁻¹ * ratGL E n (nrm d) * x =
      twConj (thetaA E n) x (ratGL E n d) * thetaA E n (twConj (thetaA E n) x (ratGL E n d)) := by
  simp only [twConj, nrm, map_mul, map_inv, thetaA_invol, ratGL_thetaE]
  group

end Global

theorem arith (C₁ C₂ c L l τ : ℝ) (hL0 : 0 ≤ L) (hl0 : 0 ≤ l) (hl : l ≤ 2 * L + |c|)
    (hτ : (1 + |C₁| * (2 + |c|) + |C₂|) * (1 + L) ≤ τ) :
    0 < τ ∧ C₁ * (1 + l) < 2 * τ ∧ C₂ * (1 + L) ≤ τ := by
  have ha : 0 ≤ |C₁| := abs_nonneg _
  have hb : 0 ≤ |C₂| := abs_nonneg _
  have hcc : 0 ≤ |c| := abs_nonneg _
  have hprod : 0 ≤ |C₁| * (2 + |c|) * (1 + L) := by positivity
  have hprod2 : 0 ≤ |C₂| * (1 + L) := by positivity
  have hτ' : 1 + L + |C₁| * (2 + |c|) * (1 + L) + |C₂| * (1 + L) ≤ τ := by
    calc _ = (1 + |C₁| * (2 + |c|) + |C₂|) * (1 + L) := by ring
      _ ≤ τ := hτ
  have hτ0 : 0 < τ := by linarith
  refine ⟨hτ0, ?_, ?_⟩
  · have e1 : C₁ * (1 + l) ≤ |C₁| * (1 + l) := mul_le_mul_of_nonneg_right (le_abs_self _) (by linarith)
    have e2 : |C₁| * (1 + l) ≤ |C₁| * (1 + (2 * L + |c|)) := mul_le_mul_of_nonneg_left (by linarith) ha
    have e3 : |C₁| * (1 + (2 * L + |c|)) ≤ |C₁| * (2 + |c|) * (1 + L) := by
      have : 0 ≤ |C₁| * (1 + |c| * L) := by positivity
      nlinarith
    linarith
  · have h3 : C₂ * (1 + L) ≤ |C₂| * (1 + L) := mul_le_mul_of_nonneg_right (le_abs_self _) (by linarith)
    linarith

theorem onlyStable_of : DegSubmod → DegMove → DegBdd → DegPairing → SizeBasic → OnlyStable := by
  intro hSub hMove hBdd hPair hSize E _ _ _ n
  obtain ⟨C₁, h₁⟩ := hMove E n
  obtain ⟨C₂, h₂⟩ := hPair E n
  obtain ⟨-, hnn, hθ, c, hc⟩ := hSize E n
  refine ⟨1 + |C₁| * (2 + |c|) + |C₂|, fun τ x d hτ => ?_⟩
  have hls : logSize (x⁻¹ * ratGL E n (nrm d) * x) ≤
      2 * logSize (twConj (thetaA E n) x (ratGL E n d)) + |c| := by
    rw [conj_nrm]
    have h := hc (twConj (thetaA E n) x (ratGL E n d)) (thetaA E n (twConj (thetaA E n) x (ratGL E n d)))
    rw [hθ] at h
    have := le_abs_self c
    linarith
  obtain ⟨hτ0, hD, hC₂⟩ := arith C₁ C₂ c _ _ τ (hnn _) (hnn _) hls hτ
  constructor
  · exact fun h W _ => h.1 W
  · intro hst
    refine ⟨fun W => ?_, ?_⟩
    · exact core (deg x) (img (nrm d)) τ _ hτ0 hD ((hBdd E n).1 x) (hSub E n x) (fun W => h₁ x (nrm d) W)
        (fun W => finrank_img _ W) hst W
    · have h := (h₂ x d).2
      have := neg_abs_le (deg x (⊤ : Submodule E (Fin n → E)))
      linarith

end GlobalTheory.CompanionTheory.OnlyStab
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PermutationBlockCounts
section
set_option maxSynthPendingDepth 1
open GlobalTheory.SmGL
open GroundTheory.Automorphic.Parabolic (levi parabolicInd jacquetRep JacquetModule sqrtModular leviIncl cellLeviSub normInducing unipotentRadical)
open GroundTheory.Automorphic.Iwasawa (blockUpper)
open GroundTheory.Automorphic (permGL indRep)
open DoubleCoset (doubleCoset)

namespace GlobalTheory.CompanionTheory.CellSizes

theorem card_blk_fiber {α : Type} {N : ℕ} {m : α → Type} [DecidableEq α] [∀ i, Fintype (m i)]
    (e : (Σ i, m i) ≃ Fin N) (i : α) :
    (Finset.univ.filter fun x : Fin N => blk e x = i).card = Fintype.card (m i) := by
  have h : (Finset.univ.filter fun x : Fin N => blk e x = i) =
      (Finset.univ : Finset (m i)).map
        ⟨fun y => e ⟨i, y⟩, fun a b hab => by simpa using e.injective hab⟩ := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map,
      Function.Embedding.coeFn_mk]
    constructor
    · rintro rfl
      exact ⟨(e.symm x).2, e.apply_symm_apply x⟩
    · rintro ⟨y, rfl⟩
      exact blk_apply e i y
  rw [h, Finset.card_map, Finset.card_univ]

theorem sizes_sum : ∀ {α : Type} [Fintype α] [LinearOrder α] {N : ℕ} {m : α → Type} [∀ i, Fintype (m i)] [∀ i, DecidableEq (m i)] {β' : Type} [Fintype β'] [LinearOrder β'] {m' : β' → Type} [∀ j, Fintype (m' j)] [∀ j, DecidableEq (m' j)] (e : (Σ i, m i) ≃ Fin N) (e' : (Σ j, m' j) ≃ Fin N) (w : Equiv.Perm (Fin N)), (∀ i, ∑ j, ((Finset.univ.filter fun x : Fin N => blk e x = i ∧ blk e' (w.symm x) = j).card) = Fintype.card (m i)) ∧ ∀ j, ∑ i, ((Finset.univ.filter fun x : Fin N => blk e x = i ∧ blk e' (w.symm x) = j).card) = Fintype.card (m' j) := by
  intro α _ _ N m _ _ β' _ _ m' _ _ e e' w
  constructor
  · intro i
    have h := Finset.card_eq_sum_card_fiberwise
      (s := Finset.univ.filter fun x : Fin N => blk e x = i)
      (t := (Finset.univ : Finset β')) (f := fun x => blk e' (w.symm x))
      (fun _ _ => Finset.mem_coe.2 (Finset.mem_univ _))
    simp only [Finset.filter_filter] at h
    rw [← h]
    exact card_blk_fiber e i
  · intro j
    have h := Finset.card_eq_sum_card_fiberwise
      (s := Finset.univ.filter fun x : Fin N => blk e' (w.symm x) = j)
      (t := (Finset.univ : Finset α)) (f := fun x => blk e x)
      (fun _ _ => Finset.mem_coe.2 (Finset.mem_univ _))
    simp only [Finset.filter_filter] at h
    have h2 : (Finset.univ.filter fun x : Fin N => blk e' (w.symm x) = j).card =
        (Finset.univ.filter fun y : Fin N => blk e' y = j).card :=
      Finset.card_equiv w.symm (by simp)
    simp only [and_comm (a := blk e _ = _)]
    rw [← h, h2]
    exact card_blk_fiber e' j

end GlobalTheory.CompanionTheory.CellSizes
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RestrictSelfPullCEqStatement
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct DirectSum GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.Onto CrystallineSemistableComparison.Pb CrystallineSemistableComparison.HT GlobalTheory.CompanionTheory.KunGlue
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.restrict_self_pullC_eq : ∀ {R : Type} [CommRing R] {C : Type 1} [Category.{0} C] (F : C ⥤ ModuleCat.{0} R) (U : ObjectProperty C) (k : U ≤ U) (n : ℕ) (x : CH.Cn (U.ι ⋙ F) n), (resU F k).pullC n x = x := by
  first | exact @GlobalTheory.CompanionTheory.KunGlue.resU_self_pullC | exact GlobalTheory.CompanionTheory.KunGlue.resU_self_pullC | (intros; apply GlobalTheory.CompanionTheory.KunGlue.resU_self_pullC <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RestrictedProductHaarMeasureStatement
section
open MeasureTheory Topology
open scoped ENNReal NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.restricted_product_haar_measure : ∀ {ι : Type} [Fintype ι]
  {G₀ : Type} [Group G₀] [TopologicalSpace G₀] [IsTopologicalGroup G₀] [T2Space G₀]
  [LocallyCompactSpace G₀] [SecondCountableTopology G₀]
  {G : ι → Type} [∀ i, Group (G i)] [∀ i, TopologicalSpace (G i)] [∀ i, IsTopologicalGroup (G i)]
  [∀ i, T2Space (G i)] [∀ i, LocallyCompactSpace (G i)] [∀ i, SecondCountableTopology (G i)]
  {W₀ : Type} [TopologicalSpace W₀] [T2Space W₀] [LocallyCompactSpace W₀]
  [SecondCountableTopology W₀] [MeasurableSpace W₀] [BorelSpace W₀]
  {W : ι → Type} [∀ i, TopologicalSpace (W i)] [∀ i, T2Space (W i)] [∀ i, LocallyCompactSpace (W i)]
  [∀ i, SecondCountableTopology (W i)] [∀ i, MeasurableSpace (W i)] [∀ i, BorelSpace (W i)]
  (a₀ : G₀ → W₀ → W₀) (a : ∀ i, G i → W i → W i),
  (Continuous fun p : G₀ × W₀ => a₀ p.1 p.2) → (∀ x, a₀ 1 x = x) →
  (∀ g h x, a₀ (g * h) x = a₀ g (a₀ h x)) →
  (∀ i, Continuous fun p : G i × W i => a i p.1 p.2) → (∀ i x, a i 1 x = x) →
  (∀ i g h x, a i (g * h) x = a i g (a i h x)) →
  ∀ (U₀ : Set W₀) (U : ∀ i, Set (W i)), IsOpen U₀ → (∀ i, IsOpen (U i)) →
  (∀ g, ∀ x ∈ U₀, a₀ g x ∈ U₀) → (∀ i g, ∀ x ∈ U i, a i g x ∈ U i) →
  ∀ (Z₀ : Set W₀) (Z : ∀ i, Set (W i)), IsClosed Z₀ → (∀ i, IsClosed (Z i)) →
  (∀ g, ∀ x ∈ Z₀, a₀ g x ∈ Z₀) → (∀ i g, ∀ x ∈ Z i, a i g x ∈ Z i) →
  (∀ x ∈ Z₀ ∩ U₀, ∀ y ∈ Z₀ ∩ U₀, ∃ g, a₀ g x = y) →
  (∀ i, ∀ x ∈ Z i ∩ U i, ∀ y ∈ Z i ∩ U i, ∃ g, a i g x = y) →
  ∀ (m₀ : Measure W₀) (m : ∀ i, Measure (W i)),
  (∀ K, IsCompact K → K ⊆ U₀ → m₀ K < ⊤) → (∀ i K, IsCompact K → K ⊆ U i → m i K < ⊤) →
  (∀ g, m₀.map (a₀ g) = m₀) → (∀ i g, (m i).map (a i g) = m i) →
  m₀ (Z₀ ∩ U₀)ᶜ = 0 → (∀ i, m i (Z i ∩ U i)ᶜ = 0) →
  ((Z₀ ∩ U₀).Nonempty → m₀ ≠ 0) → (∀ i, (Z i ∩ U i).Nonempty → m i ≠ 0) →
  ∀ (P : Measure (W₀ × ∀ i, W i)), IsFiniteMeasureOnCompacts P →
  (∀ (g₀ : G₀) (g : ∀ i, G i),
      P.map (fun x => (a₀ g₀ x.1, fun i => a i (g i) (x.2 i))) = P) →
  P ((Z₀ ∩ U₀) ×ˢ Set.univ.pi fun i => Z i ∩ U i)ᶜ = 0 →
  ∃ c : ℝ≥0, ∀ (f₀ : W₀ → ℝ≥0∞) (f : ∀ i, W i → ℝ≥0∞), Measurable f₀ →
      (∀ i, Measurable (f i)) →
      ∫⁻ x, f₀ x.1 * ∏ i, f i (x.2 i) ∂P =
        (c : ℝ≥0∞) * ((∫⁻ x, f₀ x ∂m₀) * ∏ i, ∫⁻ x, f i x ∂(m i)) := by
  first | exact @GlobalTheory.CompanionTheory.SW.FactS.OpenFactor.prod_factor_open | exact GlobalTheory.CompanionTheory.SW.FactS.OpenFactor.prod_factor_open | (intros; apply GlobalTheory.CompanionTheory.SW.FactS.OpenFactor.prod_factor_open <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SectionsEqUnivOffBadSupport
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh GlobalTheory.CompanionTheory.GE

set_option autoImplicit false
set_option maxSynthPendingDepth 1

namespace GlobalTheory.CompanionTheory.GE.PSupp

noncomputable section

variable {X : Scheme.{0}}

lemma eq_zero_basicOpen_of_affine (F : X.Modules) [F.IsQuasicoherent] {V : X.Opens}
    (hV : IsAffineOpen V) (h0 : ∀ s : Γ(F, V), s = 0) (f : Γ(X, V)) (m : Γ(F, X.basicOpen f)) :
    m = 0 := by
  have hunit : IsUnit (resO (X.basicOpen_le f) f) := X.toRingedSpace.isUnit_res_basicOpen f
  obtain ⟨e, m', hm'⟩ := qcoh_exists_res_eq F hV f m
  refine eq_zero_of_isUnit_smul (hunit.pow e) ?_
  rw [← hm', h0 m', map_zero]

lemma eq_zero_of_le_affine (F : X.Modules) [F.IsQuasicoherent] {V W : X.Opens}
    (hV : IsAffineOpen V) (h0 : ∀ s : Γ(F, V), s = 0) (hW : W ≤ V) (m : Γ(F, W)) : m = 0 := by
  refine TopCat.Sheaf.eq_of_locally_eq' (⟨F.presheaf, F.isSheaf⟩ : TopCat.Sheaf Ab X)
    (fun i : {f : Γ(X, V) // X.basicOpen f ≤ W} => X.basicOpen i.1) W
    (fun i => homOfLE i.2) ?_ m 0 ?_
  · intro x hx
    obtain ⟨f, hfW, hxf⟩ := hV.exists_basicOpen_le (V := W) ⟨x, hx⟩ (hW hx)
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨f, hfW⟩, hxf⟩
  · intro i
    rw [map_zero]
    exact eq_zero_basicOpen_of_affine F hV h0 i.1 _

lemma cokernel_sections_eq_zero {P : X.Modules} [P.IsQuasicoherent] (S : Subobject P)
    [(S : X.Modules).IsQuasicoherent] {V : X.Opens} (hV : IsAffineOpen V)
    (hS : secs S V = Set.univ) (s : Γ(cokernel S.arrow, V)) : s = 0 := by
  obtain ⟨y, rfl⟩ := surjective_cokernel_π_app S.arrow hV s
  have hmem : y ∈ secs S V := by rw [hS]; trivial
  exact (mem_range_app_iff S.arrow hV y).1 hmem

lemma supportedIn_badSet {P : X.Modules} [P.IsQuasicoherent] (S : Subobject P)
    [(S : X.Modules).IsQuasicoherent] :
    Scheme.Modules.SupportedIn (cokernel S.arrow) (badSet S) := by
  intro U hU s
  refine TopCat.Sheaf.eq_of_locally_eq'
    (⟨(cokernel S.arrow).presheaf, (cokernel S.arrow).isSheaf⟩ : TopCat.Sheaf Ab X)
    (fun i : {V : X.affineOpens // secs S (V : X.Opens) = Set.univ} => U ⊓ (i.1 : X.Opens)) U
    (fun i => homOfLE inf_le_left) ?_ s 0 ?_
  · intro x hx
    have hxb : x ∉ badSet S := fun hb => Set.disjoint_left.1 hU hx hb
    have hxc : x ∈ (badSet S)ᶜ := hxb
    rw [badSet_compl_eq] at hxc
    simp only [Set.mem_iUnion, exists_prop] at hxc
    obtain ⟨V, hV, hxV⟩ := hxc
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨V, hV⟩, ⟨hx, hxV⟩⟩
  · intro i
    rw [map_zero]
    exact eq_zero_of_le_affine _ i.1.2 (cokernel_sections_eq_zero S i.1.2 i.2) inf_le_right _

theorem secs_eq_univ_of_disjoint_badSet {X : Scheme.{0}} {P : X.Modules} (hP : P.IsQuasicoherent)
    (S : Subobject P) (hS : (S : X.Modules).IsQuasicoherent) (U : X.Opens) (hU : IsAffineOpen U)
    (hd : Disjoint (U : Set X) (badSet S)) : secs S U = Set.univ := by
  haveI : P.IsQuasicoherent := hP
  haveI : (S : X.Modules).IsQuasicoherent := hS
  exact GlobalTheory.CompanionTheory.GE.Comb.secs_eq_univ_of_supportedIn hP hS (supportedIn_badSet S) hU hd

end

end GlobalTheory.CompanionTheory.GE.PSupp
end

