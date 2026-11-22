import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0005
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0120
import Development.AbelianVarietyTheory.BlockTheory.SiegelWeilLocal.Bundle0002
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0019
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0020
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0007
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ZetaProdSphereVolumeBounds

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.TrFirstPattern
section
noncomputable section

open Polynomial Formalism.MainNotions.ArithmeticCylinders GlobalTheory.GLq GlobalTheory.GLm
open scoped Classical

namespace GlobalTheory.GLm.FirstPattern

def front (N k s : ℕ) (h : k + s ≤ N) : Equiv.Perm (Fin N) where
  toFun a := ⟨if (a : ℕ) < k then s + a else if (a : ℕ) < k + s then a - k else a, by
    have := a.2; split_ifs <;> omega⟩
  invFun a := ⟨if (a : ℕ) < s then k + a else if (a : ℕ) < k + s then a - s else a, by
    have := a.2; split_ifs <;> omega⟩
  left_inv a := by
    apply Fin.ext
    simp only
    split_ifs <;> omega
  right_inv a := by
    apply Fin.ext
    simp only
    split_ifs <;> omega

theorem front_val (N k s : ℕ) (h : k + s ≤ N) (a : Fin N) :
    ((front N k s h a : Fin N) : ℕ) = if (a : ℕ) < k then s + a else if (a : ℕ) < k + s then a - k else a := rfl

theorem phI_front (N k s : ℕ) (h : k + s ≤ N) (a b : Fin N) :
    phI k s 0 (front N k s h a) (front N k s h b) ↔ (a : ℕ) < b ∧ ¬ ((a : ℕ) < k ∧ (b : ℕ) = k) := by
  simp only [phI, IsW, Fin.lt_def, front_val]
  split_ifs <;> omega

theorem eeI_front (N k s : ℕ) (h : k + s ≤ N) (a b : Fin N) :
    eeI k s (front N k s h a) (front N k s h b) ↔ (b : ℕ) = a + 1 ∧ (b : ℕ) ≠ k := by
  simp only [eeI, IsW, front_val]
  split_ifs <;> omega

theorem eDat_congr (g N : ℕ) [NeZero g] (P P' : Mt g N → Prop) (φ φ' : Mt g N → ZMod g)
    (ψ : AddChar (ZMod g) ℂ) (hP : ∀ M, P M ↔ P' M) (hφ : ∀ M, P' M → φ M = φ' M) :
    eDat g N P φ ψ = eDat g N P' φ' ψ := by
  obtain rfl : P = P' := funext fun M => propext (hP M)
  unfold eDat
  congr 1
  refine Finset.sum_congr rfl fun u hu => ?_
  rw [hφ _ (Finset.mem_filter.1 hu).2]

theorem inPat_iff {g : ℕ} [Fact g.Prime] (N k : ℕ) (hk : k < N) (M : Mt g N) :
    InPat (fun a b : Fin N => (a : ℕ) < b ∧ ¬ ((a : ℕ) < k ∧ (b : ℕ) = k)) M ↔
      IsUniUp M ∧ ∀ a, a < k → entN M a k = 0 := by
  constructor
  · intro h
    refine ⟨fun a b => ⟨fun hab => ?_, fun hab => ?_⟩, fun a ha => ?_⟩
    · have hab' : (b : ℕ) < a := hab
      rw [h a b (by omega), Matrix.one_apply_ne hab.ne']
    · subst hab
      rw [h a a (by omega), Matrix.one_apply_eq]
    · have haN : a < N := by omega
      rw [entN, dif_pos ⟨haN, hk⟩, h _ _ (by simp [ha]), Matrix.one_apply_ne]
      intro e
      have := congrArg Fin.val e
      simp only at this
      omega
  · rintro ⟨hU, hz⟩ a b hab
    rcases lt_trichotomy a b with h | h | h
    · have h' : (a : ℕ) < b := h
      have h2 : (a : ℕ) < k ∧ (b : ℕ) = k := by
        by_contra hh
        exact hab ⟨h', hh⟩
      have := hz a h2.1
      rw [entN, dif_pos ⟨a.2, hk⟩] at this
      have hb : b = ⟨k, hk⟩ := Fin.ext h2.2
      rw [Matrix.one_apply_ne h.ne, hb]
      exact this
    · rw [(hU a b).2 h, h, Matrix.one_apply_eq]
    · rw [(hU a b).1 h, Matrix.one_apply_ne h.ne']

theorem sumAt_eq {g : ℕ} [Fact g.Prime] (N k : ℕ) (M : Mt g N) (hz : ∀ a, a < k → entN M a k = 0) :
    sumAt (fun a b : Fin N => (b : ℕ) = a + 1 ∧ (b : ℕ) ≠ k) M =
      ∑ i ∈ Finset.range (N - 1), entN M i (i + 1) := by
  have h1 : ∀ a : Fin N, (∑ b : Fin N, if ((b : ℕ) = a + 1 ∧ (b : ℕ) ≠ k) then M a b else 0) =
      entN M a (a + 1) := by
    intro a
    by_cases ha : (a : ℕ) + 1 < N
    · rw [Finset.sum_eq_single (⟨a + 1, ha⟩ : Fin N)]
      · by_cases hk : (a : ℕ) + 1 = k
        · rw [if_neg (by simp [hk]), hk, hz a (by omega)]
        · rw [if_pos (by simp [hk]), entN, dif_pos ⟨a.2, ha⟩]
      · intro b _ hb
        rw [if_neg]
        rintro ⟨e, -⟩
        exact hb (Fin.ext e)
      · simp
    · rw [entN, dif_neg (by omega)]
      refine Finset.sum_eq_zero fun b _ => if_neg ?_
      have := b.2
      omega
  have h2 : ∑ i ∈ Finset.range (N - 1), entN M i (i + 1) = ∑ i ∈ Finset.range N, entN M i (i + 1) := by
    refine Finset.sum_subset (Finset.range_subset_range.2 (Nat.sub_le _ _)) fun i _ hi => ?_
    rw [Finset.mem_range] at hi
    rw [entN, dif_neg (by omega)]
  rw [h2, Finset.sum_range, sumAt]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [← h1 a]
  refine Finset.sum_congr rfl fun b _ => ?_
  congr

theorem tr_first_pattern : ∀ (g : ℕ) [Fact g.Prime] (ψ : AddChar (ZMod g) ℂ) (N k s : ℕ), N = k + 2 * s + 1 →
    ∀ χ : Gn g N → ℂ, IsClass χ → tr (ePat g N (phI k s 0) (eeI k s) ψ) χ = tr (eJ' g N k ψ) χ := by
  intro g _ ψ N k s hN χ hχ
  have h : k + s ≤ N := by omega
  rw [← GlobalTheory.GLm.tr_ePat_renumber g ψ N (phI k s 0) (eeI k s) (front N k s h) χ hχ]
  congr 1
  have e1 : (fun a b => phI k s 0 (front N k s h a) (front N k s h b)) =
      fun a b : Fin N => (a : ℕ) < b ∧ ¬ ((a : ℕ) < k ∧ (b : ℕ) = k) :=
    funext fun a => funext fun b => propext (phI_front N k s h a b)
  have e2 : (fun a b => eeI k s (front N k s h a) (front N k s h b)) =
      fun a b : Fin N => (b : ℕ) = a + 1 ∧ (b : ℕ) ≠ k :=
    funext fun a => funext fun b => propext (eeI_front N k s h a b)
  rw [e1, e2, ePat, eJ']
  exact eDat_congr g N _ _ _ _ ψ (inPat_iff N k (by omega)) fun M hM => sumAt_eq N k M hM.2

end GlobalTheory.GLm.FirstPattern
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnitaryAutomorphicCountingUnbundled
section
open MeasureTheory NumberField Formalism.MainNotions.S
open scoped InnerProductSpace

namespace GlobalTheory.CountBridge

theorem fdegOf_eq_of_isFdeg {n : ℕ} {ε : Fin n → Bool} {H : Type} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] (μ : Measure (Formalism.REAL.UJ ε))
    (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (d : ℝ) (hd : IsFdeg μ σ d) (w : H) (hw : ‖w‖ = 1) :
    fdegOf μ σ w = d := by
  obtain ⟨hpos, h⟩ := hd
  have h2 := (h w w w w).2
  have h3 : (fun g => coefOn (ε := ε) σ w w g * star (coefOn σ w w g)) =
      fun g => (((‖coefOn (ε := ε) σ w w g‖ ^ 2 : ℝ)) : ℂ) := by
    funext g
    rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  rw [h3, integral_complex_ofReal, inner_self_eq_norm_sq_to_K, hw] at h2
  have h4 : ∫ g, ‖coefOn (ε := ε) σ w w g‖ ^ 2 ∂μ = 1 / d := by
    apply Complex.ofReal_injective
    rw [h2]
    simp
  unfold fdegOf
  rw [h4, hw]
  simp

theorem le_exp_of_log_le {x y : ℝ} (h : Real.log x ≤ y) : x ≤ Real.exp y :=
  (Real.le_exp_log x).trans (Real.exp_le_exp.mpr h)

theorem one_le_rd (I : AutInst) : 1 ≤ I.rd := by
  unfold AutInst.rd
  apply Real.one_le_rpow
  · have h : (1 : ℤ) ≤ |discr I.E| := Int.one_le_abs (discr_ne_zero I.E)
    exact_mod_cast h
  · positivity

theorem count_unbundled : GlobalTheory.IndefiniteRowSideFullHecke.LatticeCountingTheorem.CountingTheorem → ∀ A : ℝ, ∃ (n₀ : ℕ) (C₀ : ℝ), 0 ≤ C₀ ∧ ∀ n₁ ≥ n₀, ∀ C ≥ C₀, ∀ (I : AutInst) (b : ℝ) (lam : InfinitePlace I.F → Fin I.n → ℝ) (g g₀ : ℕ) (e : I.Gf → ℂ) (H : InfinitePlace I.F → Type) [∀ v, NormedAddCommGroup (H v)] [∀ v, InnerProductSpace ℂ (H v)] [∀ v, CompleteSpace (H v)] (σ : ∀ v, Matrix (Fin I.n) (Fin I.n) ℂ → (H v →L[ℂ] H v)) (w : ∀ v, H v) (Hs : Type) [NormedAddCommGroup Hs] [InnerProductSpace ℂ Hs] [CompleteSpace Hs] (σs : I.Ginf → (Hs →L[ℂ] Hs)) (tens : (∀ v, H v) → Hs) (μf : Measure I.Gf) [SigmaFinite μf] (fund : Set I.GA) (R : I.GA → (I.L2 μf fund →L[ℂ] I.L2 μf fund)) (Re : I.L2 μf fund →L[ℂ] I.L2 μf fund) (h : ℝ), (n₁ ≤ I.n ∧ (∃ p q : ℕ, (∀ v, I.pAt v = p ∧ I.qAt v = q) ∧ q ^ 2 ≤ I.n) ∧ 2 ≤ b ∧ Real.log (Real.log I.rd) ≤ I.n ∧ (∀ v, Formalism.QuantumDeterminants.IsHCParam (lam v)) ∧ (∀ v a, |lam v a| ≤ b ^ 2) ∧ I.IsAdmIdem μf g g₀ e ∧ 1 ≤ g ∧ (g : ℝ) ≤ b ^ A ∧ g₀.Prime ∧ 4 * I.n < g₀ ∧ ∀ P : Ideal (𝓞 I.E), P.IsMaximal → ((g₀ : 𝓞 I.E) ∈ P) → Ideal.absNorm P = g₀ ∧ (g₀ : 𝓞 I.E) ∉ P ^ 2) → ((∀ v, IsDS (I.ε v) (lam v) (σ v)) ∧ (∀ v, IsLowUnit (I.ε v) (lam v) (σ v) (w v)) ∧ I.IsHilbTensor σ σs tens ∧ μf.IsHaarMeasure ∧ I.IsFundDom (I.muA μf) fund ∧ I.IsRightReg μf fund R ∧ I.IsRConvF μf fund R e Re) → (∀ v, Formalism.QuantumDeterminants.GapAtLeast (I.ε v) (lam v) h) → C * (I.n : ℝ) ^ 19 * (I.f : ℝ) ^ 5 * Real.log (b * I.rd) ≤ h → Real.log (I.f : ℝ) ≤ Real.sqrt (I.n : ℝ) → Real.log (Real.log b) ≤ 1 / 16 * (I.n : ℝ) * (I.f : ℝ) * Real.log (I.n : ℝ) → |(I.Dcount σs μf fund R Re : ℝ) - I.Dstar (∏ v, fdegOf (Formalism.REAL.muG (I.ε v)) (σ v) (w v)) μf fund e| ≤ Real.exp (-(1 / 16) * (I.n : ℝ) * (I.f : ℝ) * Real.log (I.n : ℝ)) * I.Dstar (∏ v, fdegOf (Formalism.REAL.muG (I.ε v)) (σ v) (w v)) μf fund e := by
  intro hT A
  obtain ⟨n₀, hn₀⟩ := hT A
  refine ⟨n₀, max 0 (8 * 10 ^ 14 * (A + 4)), le_max_left _ _, ?_⟩
  intro n₁ hn₁ C hC I b lam g g₀ e H _ _ _ σ w Hs _ _ _ σs tens μf _ fund R Re h
    ⟨hn, ⟨p, q, hpq, hq⟩, hb, hrd, hHC, hlam, hadm, hg, hgb, hpr, hg₀, hsplit⟩
    ⟨hDS, hlow, htens, hhaar, hfund, hR, hRe⟩ hgap hh hf hbb
  let B : RowsAut :=
    { I := I, μf := μf, haar := hhaar, fund := fund, fund_spec := hfund, lam := lam, H := H, σ := σ,
      w := w, Hs := Hs, σs := σs, tens := tens, tens_spec := htens, R := R, R_spec := hR, g := g,
      g₀ := g₀, e := e, e_adm := hadm, Re := Re, Re_spec := hRe }
  have hfd : ∀ v, IsFdeg (Formalism.REAL.muG (I.ε v)) (σ v) (fdegOf (Formalism.REAL.muG (I.ε v)) (σ v) (w v)) := by
    intro v
    obtain ⟨_, hnt, hU, hirr, hsq, -⟩ := hDS v
    obtain ⟨d, hd⟩ := GlobalTheory.schur_orthogonality_unitary I.n (I.ε v) (H v) (σ v) hU hirr hsq
    rw [fdegOf_eq_of_isFdeg _ _ d hd _ (hlow v).1]
    exact hd
  have hlog : 0 ≤ Real.log (b * I.rd) := by
    apply Real.log_nonneg
    have := one_le_rd I
    nlinarith
  have hC' : 8 * 10 ^ 14 * (A + 4) ≤ C := (le_max_right _ _).trans hC
  have hH : GlobalTheory.Count.CountHyp B A n₀ (fun v => fdegOf (Formalism.REAL.muG (I.ε v)) (σ v) (w v)) p q b := by
    refine ⟨fun v => ⟨hHC v, hDS v, hlow v, hfd v⟩, hpq, le_trans hn₁ hn, hq, le_exp_of_log_le hrd, hf, hb,
      le_exp_of_log_le hbb, hlam, hg, hgb, hpr, hg₀, GlobalTheory.T.ncard_primesOver_eq_finrank_of_unramified_split I.E g₀ hpr hsplit, ?_⟩
    intro v a a' haa
    refine le_trans ?_ (hgap v a a' haa)
    refine le_trans ?_ hh
    show 8 * 10 ^ 14 * (A + 4) * (I.n : ℝ) ^ 19 * (I.f : ℝ) ^ 5 * Real.log (b * I.rd) ≤ _
    gcongr
  have hres := (hn₀ B _ p q b hH).2
  have he : -(1 / 16) * (I.n : ℝ) * (I.f : ℝ) * Real.log (I.n : ℝ) =
      -(1 / 16 * (I.n : ℝ) * (I.f : ℝ) * Real.log (I.n : ℝ)) := by ring
  rw [he]
  exact hres

end GlobalTheory.CountBridge
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnitaryJLieCoordsConjLinear
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas

noncomputable section

namespace GlobalTheory.UnitaryCoords

open Formalism.REAL

lemma re_trace_eq_zero {n : ℕ} (J Z Y : Matrix (Fin n) (Fin n) ℂ) (hJ : J * J = 1)
    (hZ : Zᴴ * J = J * Z) (hY : Yᴴ * J + J * Y = 0) : ((Z * Yᴴ).trace).re = 0 := by
  have hY' : Yᴴ = -(J * Y * J) := by
    have h1 : Yᴴ * J = -(J * Y) := eq_neg_of_add_eq_zero_left hY
    calc Yᴴ = Yᴴ * J * J := by rw [Matrix.mul_assoc, hJ, Matrix.mul_one]
      _ = _ := by rw [h1, Matrix.neg_mul]
  have hZ' : Zᴴ = J * Z * J := by
    calc Zᴴ = Zᴴ * J * J := by rw [Matrix.mul_assoc, hJ, Matrix.mul_one]
      _ = _ := by rw [hZ]
  have h1 : ((Z * Yᴴ).trace).re = ((Y * Zᴴ).trace).re := by
    have : Y * Zᴴ = (Z * Yᴴ)ᴴ := by
      rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
    rw [this, Matrix.trace_conjTranspose]
    simp
  have h2 : (Y * Zᴴ).trace = -(Z * Yᴴ).trace := by
    rw [hZ', hY', Matrix.mul_neg, Matrix.trace_neg, neg_neg]
    calc (Y * (J * Z * J)).trace = ((Y * J) * (Z * J)).trace := by simp only [Matrix.mul_assoc]
      _ = ((Z * J) * (Y * J)).trace := Matrix.trace_mul_comm _ _
      _ = _ := by simp only [Matrix.mul_assoc]
  rw [h2, Complex.neg_re] at h1
  linarith

lemma uMat_mul' {n : ℕ} {ε : Fin n → Bool} (a b : UJ ε) : uMat (a * b) = uMat a * uMat b := rfl

lemma uMat_mul_inv' {n : ℕ} {ε : Fin n → Bool} (a : UJ ε) : uMat a * uMat a⁻¹ = 1 := by
  rw [← uMat_mul', mul_inv_cancel]; rfl

lemma conjTranspose_mul_J {n : ℕ} {ε : Fin n → Bool} (a : UJ ε) :
    (uMat a)ᴴ * Jm ε = Jm ε * uMat a⁻¹ := by
  have h : (uMat a)ᴴ * Jm ε * uMat a = Jm ε := a.2
  calc (uMat a)ᴴ * Jm ε = (uMat a)ᴴ * Jm ε * (uMat a * uMat a⁻¹) := by
        rw [uMat_mul_inv', Matrix.mul_one]
    _ = _ := by rw [← Matrix.mul_assoc, h]

lemma inv_conjTranspose_mul_J {n : ℕ} {ε : Fin n → Bool} (a : UJ ε) :
    (uMat a⁻¹)ᴴ * Jm ε = Jm ε * uMat a := by
  simpa using conjTranspose_mul_J a⁻¹

lemma coord_eq {n : ℕ} {ε : Fin n → Bool} (a : UJ ε) (Y : Matrix (Fin n) (Fin n) ℂ) (hY : inG ε Y) :
    2 * (((uMat a - 1) * Yᴴ).trace).re = (((uMat a - uMat a⁻¹) * Yᴴ).trace).re := by
  have h := re_trace_eq_zero (Jm ε) (uMat a + uMat a⁻¹ - 1 - 1) Y (Jm_mul_self ε) (by
    simp only [Matrix.conjTranspose_sub, Matrix.conjTranspose_add, Matrix.conjTranspose_one,
      Matrix.sub_mul, Matrix.add_mul, Matrix.mul_sub, Matrix.mul_add, conjTranspose_mul_J a,
      inv_conjTranspose_mul_J a, Matrix.one_mul, Matrix.mul_one]
    abel) hY
  simp only [Matrix.sub_mul, Matrix.add_mul, Matrix.trace_sub, Matrix.trace_add, Complex.sub_re,
    Complex.add_re] at h ⊢
  linarith

lemma inG_sub_inv {n : ℕ} {ε : Fin n → Bool} (a : UJ ε) : inG ε (uMat a - uMat a⁻¹) := by
  unfold inG
  simp only [Matrix.conjTranspose_sub, Matrix.sub_mul, Matrix.mul_sub, conjTranspose_mul_J a,
    inv_conjTranspose_mul_J a]
  abel

lemma coord_sum {n d : ℕ} (E : Fin d → Matrix (Fin n) (Fin n) ℂ)
    (hE : ∀ i k, ((E i * (E k)ᴴ).trace).re = if i = k then 1 else 0) (t : Fin d → ℝ) (i : Fin d) :
    (((∑ k, t k • E k) * (E i)ᴴ).trace).re = t i := by
  rw [Finset.sum_mul, Matrix.trace_sum, Complex.re_sum]
  simp only [Matrix.smul_mul, Matrix.trace_smul, Complex.smul_re, hE]
  simp

theorem coords_conj : ∀ (n : ℕ) (ε : Fin n → Bool) (A : Submodule ℝ (Matrix (Fin n) (Fin n) ℂ)) (d : ℕ) (E : Fin d → Matrix (Fin n) (Fin n) ℂ), (∀ i k, ((E i * (E k)ᴴ).trace).re = if i = k then 1 else 0) → (∀ X, (X ∈ A ∧ Formalism.REAL.inG ε X) ↔ X ∈ Submodule.span ℝ (Set.range E)) → ∀ (g m : Formalism.REAL.UJ ε) (L : Matrix (Fin d) (Fin d) ℝ), uMat g - 1 ∈ A → uMat g⁻¹ - 1 ∈ A → (∀ k, uMat m * E k * uMat m⁻¹ = ∑ i, L i k • E i) → (fun i => (((uMat (m * g * m⁻¹) - 1) * (E i)ᴴ).trace).re) = L *ᵥ (fun i => (((uMat g - 1) * (E i)ᴴ).trace).re) := by
  intro n ε A d E hE hA g m L hg hg' hL
  have hEG : ∀ i, inG ε (E i) := fun i =>
    ((hA (E i)).2 (Submodule.subset_span ⟨i, rfl⟩)).2
  have hX : uMat g - uMat g⁻¹ ∈ Submodule.span ℝ (Set.range E) := by
    refine (hA _).1 ⟨?_, inG_sub_inv g⟩
    have := A.sub_mem hg hg'
    simpa using this
  obtain ⟨t, ht⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).1 hX
  have h1 : ∀ i, 2 * (((uMat g - 1) * (E i)ᴴ).trace).re = t i := fun i => by
    rw [coord_eq g _ (hEG i), ← ht, coord_sum E hE]
  have h2 : uMat (m * g * m⁻¹) - uMat (m * g * m⁻¹)⁻¹ = ∑ i, (∑ k, L i k * t k) • E i := by
    have e : (m * g * m⁻¹)⁻¹ = m * g⁻¹ * m⁻¹ := by group
    rw [e, uMat_mul', uMat_mul', uMat_mul', uMat_mul', ← Matrix.sub_mul, ← Matrix.mul_sub, ← ht,
      Finset.mul_sum, Finset.sum_mul]
    simp only [Matrix.mul_smul, Matrix.smul_mul, hL, Finset.smul_sum, Finset.sum_smul, smul_smul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => ?_
    rw [mul_comm]
  funext i
  have h3 := coord_eq (m * g * m⁻¹) _ (hEG i)
  rw [h2, coord_sum E hE] at h3
  simp only [Matrix.mulVec, dotProduct]
  have h4 : ∑ k, L i k * t k = 2 * ∑ k, L i k * (((uMat g - 1) * (E k)ᴴ).trace).re := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [← h1 k]; ring
  linarith

end GlobalTheory.UnitaryCoords
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnitaryJMapConjEqSmulOfNormalizing
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas

namespace GlobalTheory.ConjScalesMeasure

theorem eq_smul_map_haar {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
    (M : Subgroup G) [LocallyCompactSpace M] (hM : IsClosed (M : Set G)) (μ : Measure G)
    (hμ : μ (M : Set G)ᶜ = 0)
    (hinv : ∀ s ∈ M, μ.map (fun g => s * g) = μ) [IsFiniteMeasureOnCompacts μ] :
    ∃ c : NNReal, μ = (c : ENNReal) • (Measure.haar : Measure M).map (Subtype.val : M → G) := by
  haveI : SecondCountableTopology M := TopologicalSpace.Subtype.secondCountableTopology (M : Set G)
  have hemb : MeasurableEmbedding (Subtype.val : M → G) := MeasurableEmbedding.subtype_coe hM.measurableSet
  set ν : Measure M := μ.comap Subtype.val with hν
  have hmap : ν.map Subtype.val = μ := by
    rw [hν, hemb.map_comap, Subtype.range_coe]
    exact Measure.restrict_eq_self_of_ae_mem hμ
  have hinj : ∀ ρ : Measure M, (ρ.map (Subtype.val : M → G)).comap Subtype.val = ρ := fun ρ => hemb.comap_map ρ
  haveI : ν.IsMulLeftInvariant := by
    refine ⟨fun s => ?_⟩
    rw [← hinj (ν.map _), Measure.map_map hemb.measurable (measurable_const_mul s)]
    have : (Subtype.val : M → G) ∘ (fun g => s * g) = (fun g => (s : G) * g) ∘ Subtype.val := rfl
    rw [this, ← Measure.map_map (measurable_const_mul _) hemb.measurable, hmap, hinv s s.2]
  haveI : IsFiniteMeasureOnCompacts ν := by
    refine ⟨fun K hK => ?_⟩
    rw [hν, hemb.comap_apply]
    exact (hK.image continuous_subtype_val).measure_lt_top
  have e1 := Measure.isMulLeftInvariant_eq_smul ν (Measure.haar : Measure M)
  refine ⟨Measure.haarScalarFactor ν (Measure.haar : Measure M), ?_⟩
  rw [← Measure.map_smul]
  conv_lhs => rw [← hmap, e1]
  rfl

theorem map_conj_eq_smul_of_group {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [LocallyCompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
    (S : Subgroup G) (μ : Measure G) (hS : IsClosed (S : Set G)) (hμ : μ (S : Set G)ᶜ = 0)
    (hinv : ∀ s ∈ S, μ.map (fun g => s * g) = μ) (hfin : IsFiniteMeasureOnCompacts μ) (h0 : μ ≠ 0)
    (m : G) (hm : ∀ g, g ∈ S ↔ m * g * m⁻¹ ∈ S) :
    ∃ c : NNReal, μ.map (fun u => m * u * m⁻¹) = (c : ENNReal) • μ := by
  haveI : LocallyCompactSpace S := hS.isClosedEmbedding_subtypeVal.locallyCompactSpace
  have hcm : Measurable (fun u : G => m * u * m⁻¹) :=
    ((continuous_const.mul continuous_id).mul continuous_const).measurable
  haveI : IsFiniteMeasureOnCompacts (μ.map (fun u => m * u * m⁻¹)) :=
    Measure.IsFiniteMeasureOnCompacts.map μ ((Homeomorph.mulLeft m).trans (Homeomorph.mulRight m⁻¹))
  obtain ⟨a, ha⟩ := eq_smul_map_haar S hS μ hμ hinv
  obtain ⟨b, hb⟩ := eq_smul_map_haar S hS (μ.map (fun u => m * u * m⁻¹))
    (by
      rw [Measure.map_apply hcm hS.measurableSet.compl]
      convert hμ using 2
      ext g
      exact not_congr (hm g).symm)
    (by
      intro s hs
      have hs' : m⁻¹ * s * m ∈ S := (hm _).2 (by simpa [mul_assoc] using hs)
      rw [Measure.map_map (measurable_const_mul s) hcm]
      have : (fun g => s * g) ∘ (fun u : G => m * u * m⁻¹)
          = (fun u : G => m * u * m⁻¹) ∘ (fun g => (m⁻¹ * s * m) * g) := by
        funext g
        simp [mul_assoc]
      rw [this, ← Measure.map_map hcm (measurable_const_mul _), hinv _ hs'])
  have ha0 : a ≠ 0 := by
    rintro rfl
    exact h0 (by simpa using ha)
  refine ⟨b / a, ?_⟩
  rw [hb]
  conv_rhs => rw [ha]
  rw [smul_smul, ← ENNReal.coe_mul, div_mul_cancel₀ _ ha0]

theorem map_conj_eq_smul : ∀ (n : ℕ) (ε : Fin n → Bool) (S : Subgroup (Formalism.REAL.UJ ε)) (μ : Measure (Formalism.REAL.UJ ε)), IsClosed (S : Set (Formalism.REAL.UJ ε)) → μ (S : Set (Formalism.REAL.UJ ε))ᶜ = 0 → (∀ s ∈ S, μ.map (fun g => s * g) = μ) → IsFiniteMeasureOnCompacts μ → μ ≠ 0 → ∀ m : Formalism.REAL.UJ ε, (∀ g, g ∈ S ↔ m * g * m⁻¹ ∈ S) → ∃ c : NNReal, μ.map (fun u => m * u * m⁻¹) = (c : ENNReal) • μ :=
  fun _ _ S μ hS hμ hinv hfin h0 m hm => map_conj_eq_smul_of_group S μ hS hμ hinv hfin h0 m hm

end GlobalTheory.ConjScalesMeasure
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnitarySphereVolumeProductRatioAndInvBounds
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas

namespace GlobalTheory.SphereRatio

theorem sphV_succ (i : ℕ) : sphV (i + 1) = sphV i * (2 * Real.pi ^ (i + 1) / (i.factorial : ℝ)) := by
  unfold sphV
  rw [Finset.prod_Icc_succ_top (by omega)]
  simp

theorem sphV_pos (i : ℕ) : 0 < sphV i := by
  unfold sphV
  refine Finset.prod_pos fun l _ => ?_
  have := Real.pi_pos
  positivity

theorem le_exp : (32.5 : ℝ) ≤ Real.exp 3.49 := by
  have h := Real.sum_le_exp_of_nonneg (x := (3.49 : ℝ)) (by norm_num) 10
  refine le_trans ?_ h
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]
  norm_num

theorem sphV_add_le (m j : ℕ) : sphV (m + j) ≤ sphV m * Real.exp (3.49 * j) := by
  induction j with
  | zero => simp
  | succ j ih =>
    have h := GlobalTheory.zetaProd_sphereVolume_bounds.2.2 (m + j + 1) (by omega)
    rw [Nat.add_sub_cancel] at h
    have h2 := h.trans le_exp
    have hp := Real.pi_pos
    have hm := sphV_pos m
    rw [← add_assoc, sphV_succ]
    calc sphV (m + j) * (2 * Real.pi ^ (m + j + 1) / ((m + j).factorial : ℝ))
        ≤ (sphV m * Real.exp (3.49 * j)) * Real.exp 3.49 :=
          mul_le_mul ih h2 (by positivity) (by positivity)
      _ = sphV m * Real.exp (3.49 * ((j + 1 : ℕ) : ℝ)) := by
          rw [mul_assoc, ← Real.exp_add]
          push_cast
          ring_nf

theorem inv_sphV_le (J : ℕ) : (sphV J)⁻¹ ≤ (J : ℝ) ^ (J * (J - 1) / 2) := by
  induction J with
  | zero => simp [sphV]
  | succ J ih =>
    have hp : (1 : ℝ) ≤ Real.pi := by linarith [Real.pi_gt_three]
    have h1 : (1 : ℝ) ≤ 2 * Real.pi ^ (J + 1) := by
      have := one_le_pow₀ (n := J + 1) hp
      linarith
    have hf : (J.factorial : ℝ) ≤ (J : ℝ) ^ J := by exact_mod_cast Nat.factorial_le_pow J
    have h2 : (2 * Real.pi ^ (J + 1) / (J.factorial : ℝ))⁻¹ ≤ (J : ℝ) ^ J := by
      rw [inv_div]
      exact (div_le_self (by positivity) h1).trans hf
    have he : (J + 1) * (J + 1 - 1) / 2 = J * (J - 1) / 2 + J := Nat.triangle_succ J
    have hJ := sphV_pos J
    rw [sphV_succ, mul_inv, he]
    calc (sphV J)⁻¹ * (2 * Real.pi ^ (J + 1) / (J.factorial : ℝ))⁻¹
        ≤ (J : ℝ) ^ (J * (J - 1) / 2) * (J : ℝ) ^ J :=
          mul_le_mul ih h2 (by positivity) (by positivity)
      _ = (J : ℝ) ^ (J * (J - 1) / 2 + J) := by rw [pow_add]
      _ ≤ ((J + 1 : ℕ) : ℝ) ^ (J * (J - 1) / 2 + J) :=
          pow_le_pow_left₀ (by positivity) (by push_cast; linarith) _

end GlobalTheory.SphereRatio

theorem GlobalTheory.sphV_ratio_and_inv_bounds :
    (∀ q j : ℕ, j ≤ q → Real.log (sphV q / sphV (q - j)) ≤ 3.49 * j) ∧
      ∀ J : ℕ, 0 < sphV J ∧ (sphV J)⁻¹ ≤ (J : ℝ) ^ (J * (J - 1) / 2) := by
  refine ⟨fun q j h => ?_, fun J => ⟨GlobalTheory.SphereRatio.sphV_pos J, GlobalTheory.SphereRatio.inv_sphV_le J⟩⟩
  have h1 := GlobalTheory.SphereRatio.sphV_add_le (q - j) j
  rw [Nat.sub_add_cancel h] at h1
  have hq := GlobalTheory.SphereRatio.sphV_pos q
  have hm := GlobalTheory.SphereRatio.sphV_pos (q - j)
  rw [Real.log_le_iff_le_exp (by positivity), div_le_iff₀ hm, mul_comm]
  exact h1
end

