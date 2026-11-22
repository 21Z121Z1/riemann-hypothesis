import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ExistsIsHaarMeasureSUJ
import Mathlib
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.Bundle0001
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.DiscreteSpectrumKFiniteDecomposition
import Formalism.HarderNarasimhan.ShiftInvariance
import Formalism.RealPlaceAnalysis.FinalF
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsSmoothCompactSupportFixLowestKType
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0264
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0268

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.LowestTypeParameterAscent
section
open MeasureTheory Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Dec GlobalTheory.DSId GlobalTheory.DSSU
open scoped InnerProductSpace

namespace GlobalTheory.SuVPar

open GlobalTheory.DSSU

theorem diag_mem {n : ℕ} (ε : Fin n → Bool) (θ : Fin n → ℝ) (hθ : ∑ a, θ a = 0) :
    Matrix.diagonal (fun a => Complex.exp ((θ a : ℂ) * Complex.I)) ∈ SUset ε := by
  refine ⟨?_, ?_⟩
  · show Formalism.REAL.inUJ ε _
    unfold Formalism.REAL.inUJ Formalism.REAL.Jm
    rw [Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
    congr 1
    funext a
    have h1 : star (Complex.exp ((θ a : ℂ) * Complex.I)) * Complex.exp ((θ a : ℂ) * Complex.I) = 1 := by
      rw [Complex.star_def, ← Complex.exp_conj, ← Complex.exp_add]
      simp [Complex.conj_ofReal]
    calc star (Complex.exp ((θ a : ℂ) * Complex.I)) * (if ε a = true then 1 else -1) *
          Complex.exp ((θ a : ℂ) * Complex.I)
        = (star (Complex.exp ((θ a : ℂ) * Complex.I)) * Complex.exp ((θ a : ℂ) * Complex.I)) *
            (if ε a = true then 1 else -1) := by ring
      _ = _ := by rw [h1, one_mul]
  · rw [Matrix.det_diagonal, ← Complex.exp_sum, ← Finset.sum_mul]
    have : (∑ a, (θ a : ℂ)) = 0 := by exact_mod_cast hθ
    rw [this, zero_mul, Complex.exp_zero]

theorem one_mem {n : ℕ} (ε : Fin n → Bool) : (1 : Matrix (Fin n) (Fin n) ℂ) ∈ SUset ε := by
  have h := diag_mem ε (fun _ => 0) (by simp)
  simpa using h

theorem rho_diff {n : ℕ} (ε : Fin n → Bool) (lam : Fin n → ℝ) (hinj : Function.Injective lam) (a : Fin n) :
    ∃ k : ℤ, rhoNh ε lam a - rhoCh ε lam a = ((n : ℝ) - 1) / 2 - k := by
  set A := (univ.filter fun b => lam b < lam a ∧ ε b ≠ ε a).card
  set B := (univ.filter fun b => lam a < lam b ∧ ε b ≠ ε a).card
  set C := (univ.filter fun b => lam b < lam a ∧ ε b = ε a).card
  set D := (univ.filter fun b => lam a < lam b ∧ ε b = ε a).card
  have key : (A : ℝ) + B + C + D = n - 1 := by
    simp only [A, B, C, D, Finset.card_filter]
    push_cast
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    have hpt : ∀ b : Fin n, ((if lam b < lam a ∧ ε b ≠ ε a then (1:ℝ) else 0) +
        (if lam a < lam b ∧ ε b ≠ ε a then (1:ℝ) else 0) +
        (if lam b < lam a ∧ ε b = ε a then (1:ℝ) else 0) +
        (if lam a < lam b ∧ ε b = ε a then (1:ℝ) else 0)) = 1 - (if a = b then 1 else 0) := by
      intro b
      by_cases hab : a = b
      · subst hab; simp
      · have hne : lam b ≠ lam a := fun h => hab (hinj h).symm
        rcases lt_or_gt_of_ne hne with h | h <;> by_cases he : ε b = ε a <;>
          simp [h, he, hab, not_lt_of_gt h]
    rw [Finset.sum_congr rfl (fun b _ => hpt b), Finset.sum_sub_distrib, Finset.sum_ite_eq]
    simp
  refine ⟨(B + C : ℕ), ?_⟩
  simp only [rhoNh, rhoCh]
  change ((A : ℝ) - B) / 2 - ((C : ℝ) - D) / 2 = _
  push_cast
  linarith

theorem wt_int {n : ℕ} (hn : 1 ≤ n) (ε : Fin n → Bool) {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (m : ℤ) (π' π : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (hE : Ext ε m π' π)
    (Λ : Fin n → ℝ) (hΛ : ∑ a, Λ a = 0) (v : H) (hv : v ≠ 0) (hw : IsWtS π' Λ v) (a : Fin n) :
    ∃ k : ℤ, Λ a + (m : ℝ) / n = k := by
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)

  have h1 : π' 1 v = v := by
    have := hw (fun _ => 0) (by simp)
    simpa using this
  have hπ1 : π 1 = π' 1 := by
    have := hE 1 (by simp) 1 (one_mem ε)
    simpa using this
  set θ : Fin n → ℝ := fun b => (if b = a then 2 * Real.pi else 0) - 2 * Real.pi / n with hθdef
  have hθ : ∑ b, θ b = 0 := by
    simp only [hθdef, Finset.sum_sub_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp
    ring
  set z : ℂ := Complex.exp (((2 * Real.pi / n : ℝ) : ℂ) * Complex.I) with hz
  have hz1 : ‖z‖ = 1 := by rw [hz, Complex.norm_exp_ofReal_mul_I]
  have hzg : z • Matrix.diagonal (fun b => Complex.exp ((θ b : ℂ) * Complex.I)) = 1 := by
    ext i j
    by_cases hij : i = j
    · subst hij
      simp only [Matrix.smul_apply, Matrix.diagonal_apply_eq, Matrix.one_apply_eq, smul_eq_mul, hz]
      rw [← Complex.exp_add]
      rw [Complex.exp_eq_one_iff]
      by_cases hia : i = a
      · refine ⟨1, ?_⟩
        simp only [hθdef, hia, if_true]
        push_cast
        ring
      · refine ⟨0, ?_⟩
        simp only [hθdef, hia, if_false]
        push_cast
        ring
    · simp [Matrix.diagonal_apply_ne _ hij, Matrix.one_apply_ne hij]
  have hmain := hE z hz1 _ (diag_mem ε θ hθ)
  rw [hzg, hπ1] at hmain
  have hv2 := congrArg (fun T : H →L[ℂ] H => T v) hmain
  simp only [h1, ContinuousLinearMap.smul_apply, hw θ hθ, smul_smul] at hv2

  have hsum : (∑ b, Λ b * θ b) = 2 * Real.pi * Λ a := by
    simp only [hθdef, mul_sub, Finset.sum_sub_distrib, mul_ite, mul_zero, Finset.sum_ite_eq',
      Finset.mem_univ, if_true, ← Finset.sum_mul, hΛ, zero_mul, sub_zero]
    ring
  rw [hsum] at hv2
  have hc : z ^ m * Complex.exp (((2 * Real.pi * Λ a : ℝ) : ℂ) * Complex.I) = 1 := by
    by_contra hne
    have : (z ^ m * Complex.exp (((2 * Real.pi * Λ a : ℝ) : ℂ) * Complex.I) - 1) • v = 0 := by
      rw [sub_smul, one_smul, ← hv2, sub_self]
    rcases smul_eq_zero.mp this with h | h
    · exact hne (sub_eq_zero.mp h)
    · exact hv h
  rw [hz, ← Complex.exp_int_mul, ← Complex.exp_add, Complex.exp_eq_one_iff] at hc
  obtain ⟨k, hk⟩ := hc
  refine ⟨k, ?_⟩
  have hpi : (2 * (Real.pi : ℂ) * Complex.I) ≠ 0 := by
    simp [Real.pi_ne_zero, Complex.I_ne_zero]
  have : ((Λ a + (m : ℝ) / n : ℝ) : ℂ) = (k : ℂ) := by
    apply mul_right_cancel₀ hpi
    rw [← hk]
    push_cast
    field_simp
    ring
  exact_mod_cast this

end GlobalTheory.SuVPar

namespace GlobalTheory.SuVPar

theorem parS_lifts : ∀ (n : ℕ), 1 ≤ n → ∀ (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] (m : ℤ) (π' π : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)), Ext ε m π' π → ∀ lam' : Fin n → ℝ, IsParS lam' → (∃ S : Submodule ℂ H, IsKTypeS ε lam' π' (lowCh ε lam') S) → IsParU (fun a => lam' a + (m : ℝ) / n) ∧ ∑ a, (lam' a + (m : ℝ) / n) = (m : ℝ) := by
  intro n hn ε H _ _ m π' π hE lam' hP hS
  obtain ⟨hsum0, hinj, -⟩ := hP
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro a b h
    exact hinj (add_right_cancel h)
  · intro a
    obtain ⟨S, hΛ, -, -, -, ⟨v, -, hv, hw⟩, -⟩ := hS
    obtain ⟨k1, hk1⟩ := wt_int hn ε m π' π hE _ hΛ v hv hw a
    obtain ⟨k2, hk2⟩ := rho_diff ε lam' hinj a
    refine ⟨k1 + k2 - n + 1, ?_⟩
    have hl : lowCh ε lam' a = lam' a + rhoNh ε lam' a - rhoCh ε lam' a := rfl
    push_cast
    linarith
  · rw [Finset.sum_add_distrib, hsum0, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp
    ring

end GlobalTheory.SuVPar
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.RealUnipotentIntegralDiscreteSeriesVanish
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec GlobalTheory.DSId
open scoped InnerProductSpace ComplexOrder ContDiff

namespace GlobalTheory.RealFibre

private lemma prod_mul_mulSingle_mul {ι : Type*} [Fintype ι] {dec : DecidableEq ι} {G : ι → Type*}
    [∀ i, Group (G i)] (f : ∀ i, G i → ℂ) (a b : ∀ i, G i) (v : ι) (m : G v) :
    ∏ u, f u (a u * Pi.mulSingle v m u * b u) =
      f v (a v * m * b v) * ∏ u ∈ Finset.univ.erase v, f u (a u * b u) := by
  rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ v), Pi.mulSingle_eq_same]
  congr 1
  refine Finset.prod_congr rfl fun u hu => ?_
  rw [Pi.mulSingle_eq_of_ne (Finset.ne_of_mem_erase hu), mul_one]

theorem integral_phe_eq_zero_of_isKTypeOf : ∀ (B : RowsAut) (d : InfinitePlace B.I.F → ℝ) (h : ℝ), IsDSData B d → (∀ v, Formalism.MainNotions.S.IsKTypeOf (B.I.ε v) (B.σ v) (Formalism.QuantumDeterminants.lowK (B.I.ε v) (B.lam v)) (Formalism.MainNotions.S.lowKSub (B.I.ε v) (B.lam v) (B.σ v))) → LocDec B h → (∀ v, 120 * (B.I.n : ℝ) * ((rkR (B.I.ε v) : ℕ) : ℝ) ^ ((3 : ℝ) / 2) ≤ h) → ∀ (v : InfinitePlace B.I.F) (Wv : Submodule ℂ (Fin B.I.n → ℂ)), IsIsoC (B.I.ε v) Wv → ∀ ν : Measure (UJ (B.I.ε v)), IsHaarSub (NW (B.I.ε v) Wv) ν → ∀ x y : B.I.GA, ∫ m, phe B d (x * (open Classical in ((Pi.mulSingle v m, 1) : B.I.GA)) * y) ∂ν = 0 := by
  intro B d h hDS hK hLoc hh v Wv hW ν hν x y
  obtain ⟨-, hds, hlow, hfd⟩ := hDS v
  have hU := hds.2.2.1
  obtain ⟨α, hαs, hαc, hαf⟩ :=
    exists_smooth_fix_lowKSub B.I.n (B.I.ε v) (B.lam v) (B.H v) (B.σ v) hU (hK v)
  have hq : 1 ≤ rkR (B.I.ε v) := one_le_rkR_of_isIsoC hW
  have hn : 1 ≤ B.I.n := by
    have hle : rkR (B.I.ε v) ≤ B.I.n := by
      unfold rkR
      exact (min_le_left _ _).trans ((Finset.card_filter_le _ _).trans (by simp))
    omega
  obtain ⟨h0, hc⟩ := rate_lt hn hq (hh v)

  have hF := GlobalTheory.T.unitary_rep_matrixCoeff_integral_eq_zero B.I.n (B.I.ε v) Wv ν hW hν (B.H v) (B.σ v) (d v)
    (h / (8 * Real.sqrt (rkR (B.I.ε v)))) α (B.w v) hU hfd (by exact_mod_cast hc) hlow.1 hαs hαc
    (fun u => hαf (B.w v) hlow.2 u)
    ⟨Real.exp (h / 8), fun g => (hLoc v g).trans (decE_le_exp hq h0 _)⟩ (x.1 v) (y.1 v)

  have hpt : ∀ m : UJ (B.I.ε v), phe B d (x * (open Classical in ((Pi.mulSingle v m, 1) : B.I.GA)) * y) =
      (open Classical in (((∏ u, d u : ℝ) : ℂ) *
        star (∏ u ∈ Finset.univ.erase v, ⟪B.w u, B.σ u (uMat (x.1 u * y.1 u)) (B.w u)⟫_ℂ) *
        B.e (x.2 * y.2))) * star ⟪B.w v, B.σ v (umat (x.1 v * m * y.1 v)) (B.w v)⟫_ℂ := by
    intro m
    simp only [phe, ph, Prod.fst_mul, Prod.snd_mul, Pi.mul_apply, mul_one]
    rw [prod_mul_mulSingle_mul (fun u g => ⟪B.w u, B.σ u (uMat g) (B.w u)⟫_ℂ) x.1 y.1 v m, star_mul]
    ring
  simp_rw [hpt]
  rw [integral_const_mul]
  have hconj : ∫ m, star ⟪B.w v, B.σ v (umat (x.1 v * m * y.1 v)) (B.w v)⟫_ℂ ∂ν =
      star (∫ m, ⟪B.w v, B.σ v (umat (x.1 v * m * y.1 v)) (B.w v)⟫_ℂ ∂ν) := integral_conj
  rw [hconj, hF, star_zero, mul_zero]

end GlobalTheory.RealFibre
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.SignKeyTrueLtFalse
section
open MeasureTheory Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Dec GlobalTheory.DSId GlobalTheory.DSSU
open scoped InnerProductSpace

namespace GlobalTheory.SignRenumber

def signKey {n : ℕ} (ε : Fin n → Bool) (a : Fin n) : ℕ := (if ε a = true then 0 else n) + a.val

lemma signKey_injective {n : ℕ} (ε : Fin n → Bool) : Function.Injective (signKey ε) := by
  intro a b h
  have ha := a.isLt
  have hb := b.isLt
  apply Fin.ext
  unfold signKey at h
  split_ifs at h <;> omega

lemma signKey_lt_iff_of_eq {n : ℕ} (ε : Fin n → Bool) {a b : Fin n} (h : ε a = ε b) :
    signKey ε a < signKey ε b ↔ a < b := by
  unfold signKey
  rw [h, Fin.lt_iff_val_lt_val]
  split_ifs <;> omega

lemma signKey_lt_n_iff {n : ℕ} (ε : Fin n → Bool) (a : Fin n) : signKey ε a < n ↔ ε a = true := by
  have ha := a.isLt
  unfold signKey
  cases h : ε a <;> simp <;> omega

lemma signKey_true_lt_false {n : ℕ} (ε : Fin n → Bool) {a b : Fin n} (ha : ε a = true)
    (hb : ε b = false) : signKey ε a < signKey ε b := by
  have h1 := (signKey_lt_n_iff ε a).mpr ha
  have h2 : ¬ signKey ε b < n := by rw [signKey_lt_n_iff, hb]; simp
  omega

lemma val_eq_rank {n : ℕ} (κ : Fin n → ℕ) (hκ : Function.Injective κ) (f : Equiv.Perm (Fin n))
    (hf : ∀ a b, κ a < κ b → f a < f b) (a : Fin n) :
    (f a).val = (univ.filter (fun b => κ b < κ a)).card := by
  have hiff : ∀ b, f b < f a ↔ κ b < κ a := by
    intro b
    constructor
    · intro h
      rcases lt_trichotomy (κ b) (κ a) with h' | h' | h'
      · exact h'
      · exact absurd (congrArg f (hκ h')) (ne_of_lt h)
      · exact absurd (hf a b h') (not_lt.mpr h.le)
    · exact hf b a
  rw [← Fin.card_Iio (f a)]
  refine Finset.card_nbij' (fun i => f.symm i) (fun b => f b) ?_ ?_ ?_ ?_
  · intro i hi
    simp only [Finset.coe_Iio, Set.mem_Iio, Finset.mem_Iio] at hi
    simp only [Finset.coe_filter, Finset.mem_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq]
    rw [← hiff]
    simpa using hi
  · intro b hb
    simp only [Finset.coe_filter, Finset.mem_filter, Finset.mem_univ, true_and,
      Set.mem_setOf_eq] at hb
    simp only [Finset.coe_Iio, Set.mem_Iio, Finset.mem_Iio]
    exact (hiff b).mpr hb
  · intro i _
    simp
  · intro b _
    simp

def signCount {n : ℕ} (ε : Fin n → Bool) : ℕ := (univ.filter (fun a => ε a = true)).card

def stdSign {n : ℕ} (ε : Fin n → Bool) (i : Fin n) : Bool := decide (i.val < signCount ε)

def renumber {n : ℕ} (ε : Fin n → Bool) : Equiv.Perm (Fin n) := (Tuple.sort (signKey ε))⁻¹

lemma renumber_compat {n : ℕ} (ε : Fin n → Bool) (a b : Fin n)
    (h : signKey ε a < signKey ε b) : renumber ε a < renumber ε b := by
  by_contra h'
  have hm := Tuple.monotone_sort (signKey ε) (not_lt.mp h')
  simp only [Function.comp_apply, renumber, Equiv.Perm.inv_def, Equiv.apply_symm_apply] at hm
  exact absurd hm (not_le.mpr h)

lemma renumber_val {n : ℕ} (ε : Fin n → Bool) (a : Fin n) :
    (renumber ε a).val = (univ.filter (fun b => signKey ε b < signKey ε a)).card :=
  val_eq_rank (signKey ε) (signKey_injective ε) (renumber ε) (renumber_compat ε) a

lemma renumber_lt_of_lt {n : ℕ} (ε : Fin n → Bool) {a b : Fin n} (hab : a < b)
    (he : ε a = ε b) : renumber ε a < renumber ε b :=
  renumber_compat ε a b ((signKey_lt_iff_of_eq ε he).mpr hab)

lemma stdSign_renumber {n : ℕ} (ε : Fin n → Bool) (a : Fin n) :
    stdSign ε (renumber ε a) = ε a := by
  unfold stdSign
  rw [renumber_val]
  cases h : ε a
  · have : signCount ε ≤ (univ.filter (fun b => signKey ε b < signKey ε a)).card := by
      apply Finset.card_le_card
      intro b hb
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hb ⊢
      exact signKey_true_lt_false ε hb h
    simpa using this
  · have : (univ.filter (fun b => signKey ε b < signKey ε a)).card < signCount ε := by
      apply Finset.card_lt_card
      rw [Finset.ssubset_iff_of_subset]
      · exact ⟨a, by simp [h], by simp⟩
      · intro b hb
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hb ⊢
        exact (signKey_lt_n_iff ε b).mp (lt_trans hb ((signKey_lt_n_iff ε a).mpr h))
    simpa using this

lemma signCount_comp {n : ℕ} (ε : Fin n → Bool) (s : Equiv.Perm (Fin n)) :
    signCount (ε ∘ s) = signCount ε := by
  unfold signCount
  refine Finset.card_nbij' (fun a => s a) (fun b => s.symm b) ?_ ?_ ?_ ?_ <;> intro x hx <;> simp_all

lemma stdSign_comp {n : ℕ} (ε : Fin n → Bool) (s : Equiv.Perm (Fin n)) :
    stdSign (ε ∘ s) = stdSign ε := by
  funext i
  unfold stdSign
  rw [signCount_comp]

lemma renumber_comp {n : ℕ} (ε : Fin n → Bool) (s : Equiv.Perm (Fin n))
    (hs : ∀ a b, a < b → ε (s a) = ε (s b) → s a < s b) (a : Fin n) :
    renumber (ε ∘ s) a = renumber ε (s a) := by
  have hc : ∀ x y, signKey (ε ∘ s) x < signKey (ε ∘ s) y →
      (s.trans (renumber ε)) x < (s.trans (renumber ε)) y := by
    intro x y hxy
    simp only [Equiv.trans_apply]
    apply renumber_compat
    by_cases he : ε (s x) = ε (s y)
    · have hxy' := (signKey_lt_iff_of_eq (ε ∘ s) (a := x) (b := y) he).mp hxy
      exact (signKey_lt_iff_of_eq ε he).mpr (hs x y hxy' he)
    · cases hx : ε (s x) <;> cases hy : ε (s y)
      · rw [hx, hy] at he; exact absurd rfl he
      · have h1 : ¬ signKey (ε ∘ s) x < n := by
          rw [signKey_lt_n_iff]; simpa using hx
        have h2 : signKey (ε ∘ s) y < n := by
          rw [signKey_lt_n_iff]; simpa using hy
        omega
      · exact signKey_true_lt_false ε hx hy
      · rw [hx, hy] at he; exact absurd rfl he
  exact Fin.ext ((val_eq_rank _ (signKey_injective _) (renumber (ε ∘ s)) (renumber_compat _) a).trans
    (val_eq_rank _ (signKey_injective _) (s.trans (renumber ε)) hc a).symm)

theorem block_renumbering :
    ∀ n : ℕ, ∃ (std : (Fin n → Bool) → (Fin n → Bool)) (t : (Fin n → Bool) → Equiv.Perm (Fin n)),
      (∀ ε, std ε ∘ t ε = ε ∧ ∀ a b, a < b → ε a = ε b → t ε a < t ε b) ∧
      (∀ (ε : Fin n → Bool) (s : Equiv.Perm (Fin n)), std (ε ∘ s) = std ε ∧
        ((∀ a b, a < b → ε (s a) = ε (s b) → s a < s b) → ∀ a, t (ε ∘ s) a = t ε (s a))) ∧
      ∀ (ε : Fin n → Bool) (lam : Fin n → ℝ), Function.Injective lam →
        ∃ (w s : Equiv.Perm (Fin n)), (∀ a, ε (w a) = ε a) ∧ StrictAnti ((lam ∘ w) ∘ s) ∧
          ∀ a b, a < b → ε (s a) = ε (s b) → s a < s b := by
  intro n
  refine ⟨stdSign, renumber, ?_, ?_, ?_⟩
  · intro ε
    exact ⟨funext fun a => stdSign_renumber ε a, fun a b hab he => renumber_lt_of_lt ε hab he⟩
  · intro ε s
    exact ⟨stdSign_comp ε s, fun hs a => renumber_comp ε s hs a⟩
  · intro ε lam hlam
    obtain ⟨u, hu⟩ : ∃ u : Equiv.Perm (Fin n), StrictAnti (lam ∘ u) := by
      refine ⟨Tuple.sort (fun a => -lam a), ?_⟩
      have hinj : Function.Injective ((fun a => -lam a) ∘ Tuple.sort (fun a => -lam a)) :=
        (neg_injective.comp hlam).comp (Tuple.sort (fun a => -lam a)).injective
      have hmono := (Tuple.monotone_sort (fun a => -lam a)).strictMono_of_injective hinj
      intro a b hab
      have := hmono hab
      simp only [Function.comp_apply, neg_lt_neg_iff] at this
      simpa using this
    let s : Equiv.Perm (Fin n) := (renumber (ε ∘ u)).trans (renumber ε).symm
    have hs_ren : ∀ x, renumber ε (s x) = renumber (ε ∘ u) x := by
      intro x; simp [s]
    have hsx : ∀ x, ε (s x) = ε (u x) := by
      intro x
      have h := stdSign_renumber (ε ∘ u) x
      rw [stdSign_comp] at h
      rw [← stdSign_renumber ε (s x), hs_ren]
      exact h
    refine ⟨s.symm.trans u, s, ?_, ?_, ?_⟩
    · intro a
      simp only [Equiv.trans_apply]
      rw [← hsx, Equiv.apply_symm_apply]
    · have : (lam ∘ ⇑(s.symm.trans u)) ∘ ⇑s = lam ∘ u := by
        funext a; simp
      rw [this]; exact hu
    · intro a b hab he
      rcases lt_trichotomy (s a) (s b) with h | h | h
      · exact h
      · exact absurd (s.injective h) (ne_of_lt hab)
      · have h1 := renumber_lt_of_lt ε h he.symm
        rw [hs_ren, hs_ren] at h1
        have he' : (ε ∘ u) a = (ε ∘ u) b := by
          show ε (u a) = ε (u b)
          rw [← hsx, ← hsx]; exact he
        have h2 := renumber_lt_of_lt (ε ∘ u) hab he'
        exact absurd h1 (not_lt.mpr h2.le)

end GlobalTheory.SignRenumber
end

