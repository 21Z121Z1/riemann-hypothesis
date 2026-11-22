import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0005
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0489
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0492
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0432
import Development.AbelianVarietyTheory.CrystallinePeriods.RingIface
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0494
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0003
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0017
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.OneSubPhiOntoOfFilZero
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0483
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0006
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0495
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0011
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0006
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PowMulMemLatIff
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DeRhamComponentWachLetterBasisFiltration
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IndepOfLinearIndependentDdRE
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0295
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0232
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0224
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0503
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0519
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0481

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CrystallineDiscPeriodsFrobeniusEqMul
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
open Matrix

noncomputable section

namespace GlobalTheory.BSP

theorem mul_comm_of_mul_eq_smul_one {R : Type} [CommRing R] [IsDomain R] {n : Type} [Fintype n] [DecidableEq n]
    (A B : Matrix n n R) (c : R) (hc : c ≠ 0) (h : A * B = c • (1 : Matrix n n R)) :
    B * A = c • (1 : Matrix n n R) := by
  have hdet : B.det ≠ 0 := by
    intro h0
    have h1 := congrArg Matrix.det h
    rw [Matrix.det_mul, h0, mul_zero, Matrix.det_smul, Matrix.det_one, mul_one] at h1
    exact pow_ne_zero _ hc h1.symm
  have h2 : (B * A - c • (1 : Matrix n n R)) * B = 0 := by
    rw [Matrix.sub_mul, Matrix.mul_assoc, h, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, Matrix.one_mul,
      sub_self]
  have h3 : B.det • (B * A - c • (1 : Matrix n n R)) = 0 := by
    have := congrArg (· * B.adjugate) h2
    simp only [Matrix.zero_mul] at this
    rw [Matrix.mul_assoc, Matrix.mul_adjugate, Matrix.mul_smul, Matrix.mul_one] at this
    exact this
  have h4 : B * A - c • (1 : Matrix n n R) = 0 := by
    ext i j
    have := congrFun (congrFun h3 i) j
    simp only [Matrix.smul_apply, smul_eq_mul, Matrix.zero_apply] at this
    simpa using (mul_eq_zero.1 this).resolve_left hdet
  exact sub_eq_zero.1 h4

variable {l : ℕ} [hl : Fact l.Prime]

theorem BK.ρ₀_pos_lt_one {K : FinExt l} (bk : BK K) : 0 < bk.ρ₀ ∧ bk.ρ₀ < 1 := by
  have hl1 : (1 : ℝ≥0) < (l : ℝ≥0) := by exact_mod_cast hl.out.one_lt
  have he : (0 : ℝ) < (bk.Ep.natDegree : ℝ) := by exact_mod_cast bk.deg_pos
  refine ⟨NNReal.rpow_pos (zero_lt_one.trans hl1), NNReal.rpow_lt_one_of_one_lt_of_neg hl1 ?_⟩
  have : (0 : ℝ) < 1 / (bk.Ep.natDegree : ℝ) := by positivity
  linarith

theorem BK.frobenius_ev_E_ne_zero {K : FinExt l} (bk : BK K) {τ : Ainf l} (hτ : bk.IsPer τ) :
    WittVector.frobenius (bk.ev bk.E) ≠ 0 := by
  intro h0
  obtain ⟨h1, ε, η, hε, hφ⟩ := hτ
  have hε1 : ε ≠ 1 := by
    rintro rfl
    obtain ⟨-, hu⟩ := hε
    exact hu (by rw [map_one]; simp)
  have hc0 : τ.coeff 0 ≠ 0 := by
    intro h0
    have h1 := congrArg (fun x => WittVector.constantCoeff x) hφ
    change (WittVector.frobenius τ).coeff 0 = _ at h1
    rw [WittVector.coeff_frobenius_charP, h0, zero_pow (Fact.out : l.Prime).ne_zero, map_mul, map_sub, map_one] at h1
    change 0 = WittVector.constantCoeff (η : Ainf l) * ((WittVector.teichmuller l ε).coeff 0 - 1) at h1
    rw [WittVector.teichmuller_coeff_zero] at h1
    have hη : IsUnit (WittVector.constantCoeff (η : Ainf l)) := η.isUnit.map _
    rcases mul_eq_zero.1 h1.symm with h | h
    · exact hη.ne_zero h
    · exact hε1 (sub_eq_zero.1 h)
  have h2 := congrArg WittVector.frobenius h1
  rw [map_mul, h0, zero_mul] at h2
  have h3 := congrArg (fun x : Ainf l => x.coeff 0) h2
  simp only [WittVector.coeff_frobenius_charP, WittVector.zero_coeff] at h3
  exact hc0 (pow_eq_zero_iff (Fact.out : l.Prime).ne_zero |>.1 (pow_eq_zero_iff (Fact.out : l.Prime).ne_zero |>.1 h3))

theorem Seed.crystallineDiscPeriods_frobenius_eq_mul : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (τ : Ainf l) (hτ : bk.IsPer τ) (d : ℕ)
    (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) ℤ_[l]) (hρ : ∀ g, IsUnit (ρ g)) (s : Seed bk d ρ τ),
    ∀ Φ : bk.DA bk.ρ₀ →+* bk.DA bk.ρ₀, IsDiscMap WittVector.frobenius Φ →
      ((l : bk.DA bk.ρ₀) ^ (s.c₁ + s.c₂) * bk.iS (frobS l bk.a bk.E) ^ s.N) • s.W.map Φ =
        s.W * (s.X' * s.F.map (C : Wq l bk.a →+* bk.S) * s.X.map (frobS l bk.a)).map bk.iS := by
  intro l _ K bk τ hτ d ρ _ s Φ hΦ
  obtain ⟨h0, h1⟩ := bk.ρ₀_pos_lt_one
  haveI : IsDomain (bk.DA bk.ρ₀) := (GlobalTheory.T.breuilKisin_ainfDisc_isDomain_norm_bounds l K bk bk.ρ₀ h0 h1).1
  obtain ⟨ι, ⟨tb⟩⟩ := GlobalTheory.T.ainf_adicTopologicalBasis_over_breuilKisin l K bk
  have hinj : Function.Injective bk.iA := (GlobalTheory.T.closedDisc_toDisc_injective_of_adicBasis l K bk (Ainf l) bk.ev ι tb bk.ρ₀ h0 h1).1
  have hΦS : ∀ x, Φ (bk.iS x) = bk.iS (frobS l bk.a x) := fun x => by
    change Φ (bk.iA (bk.ev x)) = bk.iA (bk.ev (frobS l bk.a x))
    rw [hΦ.ext, bk.ev_frob]
  have he : bk.iS (frobS l bk.a bk.E) ≠ 0 := by
    change bk.iA (bk.ev (frobS l bk.a bk.E)) ≠ 0
    rw [bk.ev_frob, ← map_zero bk.iA]
    exact fun h => bk.frobenius_ev_E_ne_zero hτ (hinj h)
  have hL0 : (l : bk.DA bk.ρ₀) ≠ 0 := fun h =>
    WittVector.p_nonzero l (OCb l) (hinj (by rw [map_natCast, map_zero]; exact h))
  have hQP : s.X.map (bk.iS.comp (frobS l bk.a)) * s.X'.map (bk.iS.comp (frobS l bk.a)) =
      ((l : bk.DA bk.ρ₀) ^ s.c₂ * bk.iS (frobS l bk.a bk.E) ^ (2 * s.N)) • (1 : Matrix (Fin d) (Fin d) (bk.DA bk.ρ₀)) := by
    rw [← Matrix.map_mul, s.X_mul, Matrix.map_smul' _ _ _ (map_mul _), Matrix.map_one _ (map_zero _) (map_one _)]
    simp only [RingHom.comp_apply, map_mul, map_pow, map_natCast]
  have hc : (l : bk.DA bk.ρ₀) ^ s.c₂ * bk.iS (frobS l bk.a bk.E) ^ (2 * s.N) ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ hL0) (pow_ne_zero _ he)
  have hPQ := mul_comm_of_mul_eq_smul_one _ _ _ hc hQP
  have hA : (s.X'.map bk.iS).map Φ = s.X'.map (bk.iS.comp (frobS l bk.a)) := by
    rw [Matrix.map_map]; congr 1; funext x; exact hΦS x
  have hF : (s.F.map (C : Wq l bk.a →+* bk.S)).map bk.iS = s.F.map (bk.iS.comp C) := by
    rw [Matrix.map_map]; rfl
  have hX : (s.X.map (frobS l bk.a)).map bk.iS = s.X.map (bk.iS.comp (frobS l bk.a)) := by
    rw [Matrix.map_map]; rfl
  have h2 := congrArg (· * s.X.map (bk.iS.comp (frobS l bk.a))) (s.φ Φ hΦ)
  simp only [Matrix.map_mul, hA] at h2
  rw [Matrix.smul_mul, Matrix.mul_assoc (s.W.map Φ), hPQ, Matrix.mul_smul, Matrix.mul_one, smul_smul] at h2
  rw [Matrix.map_mul, Matrix.map_mul, hF, hX]
  refine smul_right_injective (Matrix (Fin d) (Fin d) (bk.DA bk.ρ₀)) (pow_ne_zero s.N he) ?_
  dsimp only
  calc bk.iS (frobS l bk.a bk.E) ^ s.N • (((l : bk.DA bk.ρ₀) ^ (s.c₁ + s.c₂) * bk.iS (frobS l bk.a bk.E) ^ s.N) •
        s.W.map Φ)
      = ((l : bk.DA bk.ρ₀) ^ s.c₁ * ((l : bk.DA bk.ρ₀) ^ s.c₂ * bk.iS (frobS l bk.a bk.E) ^ (2 * s.N))) •
        s.W.map Φ := by rw [smul_smul]; congr 1; ring
    _ = _ := h2
    _ = _ := by rw [Matrix.smul_mul]; simp only [Matrix.mul_assoc]

end GlobalTheory.BSP
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CrystallineDiscPeriodsGaloisActionEq
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
open Matrix

noncomputable section

namespace GlobalTheory.BSP

theorem ringHom_ext_of_sep_galPer {R B : Type} [CommRing R] [CommRing B] {f g : R⟦X⟧ →+* B}
    (hC : ∀ r, f (C r) = g (C r)) (hX : f X = g X) (hsep : ∀ b : B, (∀ n, f X ^ n ∣ b) → b = 0) :
    f = g := by
  have hp : ∀ p : Polynomial R, f p = g p := fun p => by
    induction p using Polynomial.induction_on with
    | C a => simpa using hC a
    | add p q hp hq => simp [hp, hq]
    | monomial n a _ => simp [hC, hX]
  ext1 a
  rw [← sub_eq_zero]
  refine hsep _ fun n => ?_
  rw [a.eq_X_pow_mul_shift_add_trunc n, map_add, map_add, hp, map_mul, map_mul, map_pow, map_pow, ← hX]
  exact ⟨_, by rw [add_sub_add_right_eq_sub, ← mul_sub]⟩

theorem mat_mul_right_cancel_galPer {R : Type} [CommRing R] [IsDomain R] {n : Type} [Fintype n] [DecidableEq n]
    {A B P : Matrix n n R} (hP : P.det ≠ 0) (h : A * P = B * P) : A = B := by
  have h2 : (A - B) * P = 0 := by rw [Matrix.sub_mul, h, sub_self]
  have h3 : P.det • (A - B) = 0 := by
    rw [← Matrix.mul_one (A - B), ← Matrix.mul_smul, ← Matrix.mul_adjugate P, ← Matrix.mul_assoc, h2,
      Matrix.zero_mul]
  rw [← sub_eq_zero]
  ext i j
  have h4 := congr_fun₂ h3 i j
  rw [Matrix.smul_apply, smul_eq_mul, Matrix.zero_apply] at h4
  rw [Matrix.zero_apply]
  exact (mul_eq_zero.1 h4).resolve_left hP

theorem mat_smul_cancel_galPer {R : Type} [CommRing R] [IsDomain R] {m n : Type} {c : R} (hc : c ≠ 0)
    {A B : Matrix m n R} (h : c • A = c • B) : A = B := by
  ext i j
  have h1 := congr_fun₂ h i j
  rw [Matrix.smul_apply, Matrix.smul_apply, smul_eq_mul, smul_eq_mul] at h1
  exact mul_left_cancel₀ hc h1

variable {l : ℕ} [hl : Fact l.Prime] {K : FinExt l}

namespace BK

variable (bk : BK K)

theorem X_pow_mem_J_galPer : (X : bk.S) ^ bk.Ep.natDegree ∈ bk.J := by
  have e1 : bk.Ep - Polynomial.X ^ bk.Ep.natDegree =
      ∑ i ∈ Finset.range bk.Ep.natDegree, Polynomial.C (bk.Ep.coeff i) * Polynomial.X ^ i := by
    rw [sub_eq_iff_eq_add']
    exact bk.monic.as_sum
  have h1 : (l : Polynomial (Wq l bk.a)) ∣ bk.Ep - Polynomial.X ^ bk.Ep.natDegree := by
    rw [e1]
    refine Finset.dvd_sum fun i hi => ?_
    obtain ⟨c, hc⟩ := bk.dvd_coeff i (Finset.mem_range.1 hi)
    exact ⟨Polynomial.C c * Polynomial.X ^ i, by rw [hc, map_mul, map_natCast]; ring⟩
  have h2 : (l : bk.S) ∣ bk.E - X ^ bk.Ep.natDegree := by
    have := map_dvd (Polynomial.coeToPowerSeries.ringHom (R := Wq l bk.a)) h1
    simpa using this
  have e2 : (X : bk.S) ^ bk.Ep.natDegree = bk.E - (bk.E - X ^ bk.Ep.natDegree) := by ring
  rw [e2]
  exact Submodule.sub_mem _ (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _))
    (Ideal.mem_sup_left (Ideal.mem_span_singleton.2 h2))

theorem ev_sep_galPer (b : Ainf l) (hb : ∀ n, bk.ev X ^ n ∣ b) : b = 0 := by
  obtain ⟨ι, ⟨tb⟩⟩ := GlobalTheory.T.ainf_adicTopologicalBasis_over_breuilKisin l K bk
  have hc := tb.complete
  refine IsHausdorff.haus hc.toIsHausdorff b fun n => ?_
  rw [SModEq.zero, Ideal.smul_eq_mul, Ideal.mul_top]
  obtain ⟨c, hc⟩ := hb (bk.Ep.natDegree * n)
  rw [hc, pow_mul, ← map_pow]
  exact Ideal.mul_mem_right _ _ (Ideal.pow_mem_pow (Ideal.mem_map_of_mem bk.ev bk.X_pow_mem_J_galPer) n)

theorem σA_ev_galPer {g : ↥(GK K)} (hg : bk.FixFlat g) (a : bk.S) : Per.σA (g : GQ l) (bk.ev a) = bk.ev a := by
  have hg' : Per.σF (g : GQ l) bk.flat = bk.flat := hg
  have hX : ((Per.σA (g : GQ l)).comp bk.ev) X = bk.ev X := by
    show Per.σA _ (bk.ev X) = bk.ev X
    rw [bk.ev_X, GlobalTheory.RingIface.sigA_teich, hg']
  have h := ringHom_ext_of_sep_galPer (f := (Per.σA (g : GQ l)).comp bk.ev) (g := bk.ev)
    (fun w => by
      show Per.σA _ (bk.ev (C w)) = bk.ev (C w)
      rw [bk.ev_C, bk.gal_w]) hX
    (fun b hb => bk.ev_sep_galPer b fun n => by rw [← hX]; exact hb n)
  exact RingHom.congr_fun h a

theorem ev_injective_galPer : Function.Injective bk.ev := by
  obtain ⟨ι, ⟨tb⟩⟩ := GlobalTheory.T.ainf_adicTopologicalBasis_over_breuilKisin l K bk
  have key : ∀ a, tb.c tb.i₀ (bk.ev a * tb.b tb.i₀) = a := fun a => by
    rw [tb.c_mul, tb.c_self, mul_one]
  intro a a' h
  rw [← key a, ← key a', h]

theorem ρ₀_pos_lt_one_galPer : 0 < bk.ρ₀ ∧ bk.ρ₀ < 1 := by
  have hl1 : (1 : ℝ≥0) < l := by exact_mod_cast hl.out.one_lt
  have he : (0 : ℝ) < bk.Ep.natDegree := by exact_mod_cast bk.deg_pos
  refine ⟨NNReal.rpow_pos (zero_lt_one.trans hl1), ?_⟩
  exact NNReal.rpow_lt_one_of_one_lt_of_neg hl1 (neg_neg_of_pos (one_div_pos.2 he))

end BK

theorem seed_gal_periods : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (τ : Ainf l) (hτ : bk.IsPer τ) (d : ℕ)
    (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) ℤ_[l]) (hρ : ∀ g, IsUnit (ρ g)) (s : Seed bk d ρ τ),
    ∀ g : ↥(GK K), bk.FixFlat g → ∀ G : bk.DA bk.ρ₀ →+* bk.DA bk.ρ₀, IsDiscMap (Per.σA (g : GQ l)) G →
      (∀ j : bk.DS bk.ρ₀ →+* bk.DA bk.ρ₀, IsDiscMap bk.ev j → ∀ x, G (j x) = j x) ∧
      bk.iA τ ^ s.N • ((ρ g).map (bk.iA.comp (algebraMap ℤ_[l] (Ainf l))) * s.W.map G) =
        G (bk.iA τ) ^ s.N • s.W := by
  intro l _ K bk τ _ d ρ _ s g hg G hG
  obtain ⟨h0, h1⟩ := bk.ρ₀_pos_lt_one_galPer
  haveI : IsDomain (bk.DA bk.ρ₀) := (GlobalTheory.T.breuilKisin_ainfDisc_isDomain_norm_bounds l K bk bk.ρ₀ h0 h1).1
  obtain ⟨ι, ⟨tb⟩⟩ := GlobalTheory.T.ainf_adicTopologicalBasis_over_breuilKisin l K bk
  have hinj : Function.Injective bk.iA := (GlobalTheory.T.closedDisc_toDisc_injective_of_adicBasis l K bk (Ainf l) bk.ev ι tb bk.ρ₀ h0 h1).1
  have hGS : ∀ a, G (bk.iA (bk.ev a)) = bk.iA (bk.ev a) := fun a => by
    show G (toDisc l (bk.ev X) bk.ρ₀ (bk.ev a)) = _
    rw [hG.ext, bk.σA_ev_galPer hg]
  have hGτ : G (bk.iA τ) = bk.iA (Per.σA (g : GQ l) τ) := hG.ext τ
  refine ⟨fun j hj x => ?_, ?_⟩
  · have hGj : IsDiscMap bk.ev (G.comp j) :=
      ⟨fun a => by
        show G (j (toDisc l X bk.ρ₀ a)) = _
        rw [hj.ext]; exact hGS a,
       fun x => (hG.norm_le _).trans (hj.norm_le x)⟩
    exact RingHom.congr_fun (IsDiscMap.unique hGj hj) x
  · have he : bk.iA (bk.ev bk.E) ≠ 0 := fun h =>
      bk.E_ne_zero (bk.ev_injective_galPer (hinj (h.trans (map_zero _).symm) |>.trans (map_zero _).symm))
    have hl0 : ((l : ℕ) : bk.DA bk.ρ₀) ≠ 0 := (isUnit_l_disc l (bk.ev X) bk.ρ₀).ne_zero
    have hdet : (s.X'.map bk.iS).det ≠ 0 := by
      intro h0'
      have hm := congrArg (fun M => (M.map bk.iS).det) s.X_mul
      rw [Matrix.map_mul, Matrix.det_mul, h0', mul_zero] at hm
      have hc : (((l : bk.S) ^ s.c₂ * bk.E ^ (2 * s.N)) • (1 : Matrix (Fin d) (Fin d) bk.S)).map bk.iS =
          bk.iS ((l : bk.S) ^ s.c₂ * bk.E ^ (2 * s.N)) • (1 : Matrix (Fin d) (Fin d) (bk.DA bk.ρ₀)) := by
        ext i j
        by_cases hij : i = j <;> simp [Matrix.one_apply, hij]
      rw [hc, Matrix.det_smul, Matrix.det_one, mul_one] at hm
      have h3 := pow_eq_zero_iff'.1 hm.symm
      rw [map_mul, map_pow, map_pow, map_natCast] at h3
      exact mul_ne_zero (pow_ne_zero _ hl0) (pow_ne_zero _ he) h3.1
    have hX' : (s.X'.map bk.iS).map G = s.X'.map bk.iS := by
      rw [Matrix.map_map]
      congr 1
      funext a
      exact hGS a
    have hσ : bk.iA (Per.σA (g : GQ l) (bk.ev bk.E * τ)) = bk.iA (bk.ev bk.E) * G (bk.iA τ) := by
      rw [map_mul, bk.σA_ev_galPer hg, map_mul, hGτ]
    have h := s.gal g G hG
    rw [Matrix.map_mul, hX', hσ, map_mul, mul_pow, mul_pow, mul_smul, mul_smul] at h
    have h' := mat_smul_cancel_galPer (pow_ne_zero _ he) h
    refine mat_mul_right_cancel_galPer hdet ?_
    rw [Matrix.smul_mul, Matrix.smul_mul, Matrix.mul_assoc]
    exact h'

end GlobalTheory.BSP
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CrystallineFrobeniusBijOnLettersDirectSumStatement
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.crystallineFrobenius_bijOn_letters_directSum : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL), let W := (HW l).W K s LL h; ∀ T : Lt K LL, IsCrys ((D.loc l).PD K) T.ρ → (∀ i : Let K, Set.BijOn (φVB ((D.loc l).PD K) (LL := ↥LL.1) (V := T.V)) (Di (HW l) h T (i - 1)) (Di (HW l) h T i)) ∧ (⨆ i : Let K, Di (HW l) h T i) = Dcris ((D.loc l).PD K) T.ρ ∧ iSupIndep (fun i : Let K => Di (HW l) h T i) ∧ Function.Injective (ιV ((D.loc l).PD K) (LL := ↥LL.1) (V := T.V)) := by
  first | exact @GlobalTheory.NL.PhiD.phi_letters | exact GlobalTheory.NL.PhiD.phi_letters | (intros; apply GlobalTheory.NL.PhiD.phi_letters <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CrystallinePeriodsExtensionSpanStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per GlobalTheory.IndefiniteRowSideFullHecke.CrystallineSubrepresentation GlobalTheory.RegularRing
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.crystallinePeriods_extension_span : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), IsStd P AI → ∀ (LL : FinExt l) (T : QLat LL) (K K'' : FinExt l), K.1 ≤ K''.1 → IsCrys (P.PD K) (T.ρ.comp (inclG K)) → DcrisK₀ (P.PD K'') (T.ρ.comp (inclG K'')) ≤ Submodule.span ↥(K0 K'') (↑(DcrisK₀ (P.PD K) (T.ρ.comp (inclG K))) : Set (P.R.B ⊗[ℚ_[l]] T.V)) := by
  first | exact @GlobalTheory.Per.DcrisSpan.dcris_span | exact GlobalTheory.Per.DcrisSpan.dcris_span | (intros; apply GlobalTheory.Per.DcrisSpan.dcris_span <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CrystallinePhiModuleMapExistsStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.crystalline_phi_module_map_exists : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e) (ι : Type) [Fintype ι] [DecidableEq ι] (P : PhiMod O K l e a ι) (EE : FCrys l ↥(OL (ϖ.field a))) (c : EE.M (ϖ.prism a) →+ Vec K a ι), Function.Injective c → (∀ x, c x ∈ P.M) → (∀ m ∈ P.M, ∃ x, c x = m) → (∀ (w : (ϖ.prism a).A) (x : EE.M (ϖ.prism a)), c (w • x) = fun τ i => (toAc t K w τ : K⟦X⟧) * c x τ i) → (∀ o : O, ∃ U : FHom EE EE, ∀ x, c (U.u (ϖ.prism a) x) = fun τ i => PowerSeries.C (algebraMap O K o) * c x τ i) → ∀ (sh : K⟦X⟧ →+* K⟦X⟧⟦X⟧), (∀ (f : K⟦X⟧) (i : ℕ), (i.factorial : K⟦X⟧) * coeff i (sh f) = (PowerSeries.derivative K)^[i] f) → ∀ (PP : Obj l ↥(OL (ϖ.field a))) (p₀ p₁ : GlobalTheory.Prism.Hom (ϖ.prism a) PP) (j : ZMod a → PP.A →+* K⟦X⟧⟦X⟧), (∀ τ (x : (Wq l a)⟦X⟧), j τ (p₀.f x) = PowerSeries.C (toAc t K (frobS l a x) τ : K⟦X⟧) ∧ j τ (p₁.f x) = sh (toAc t K (frobS l a x) τ : K⟦X⟧)) → ∀ (lam₀ lam₁ : EE.M PP →+ (ZMod a → ι → K⟦X⟧⟦X⟧)), (∀ (r : PP.A) (y : EE.M PP) τ i, lam₀ (r • y) τ i = j τ r * lam₀ y τ i) → (∀ (r : PP.A) (y : EE.M PP) τ i, lam₁ (r • y) τ i = j τ r * lam₁ y τ i) → (∀ x τ i, lam₀ (EE.tr p₀ x) τ i = PowerSeries.C (frob K l (c x (τ - 1) i))) → (∀ x τ i, lam₁ (EE.tr p₁ x) τ i = sh (frob K l (c x (τ - 1) i))) → ∃ ε : ZMod a → Matrix ι ι K⟦X⟧⟦X⟧, ∀ y τ, lam₀ y τ = ε τ *ᵥ lam₁ y τ := by
  first | exact @GlobalTheory.BKGal.CrysEps.exists_eps | exact GlobalTheory.BKGal.CrysEps.exists_eps | (intros; apply GlobalTheory.BKGal.CrysEps.exists_eps <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CycZpowCrysDRJumpStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cyc_zpow_crys_dR_jump_alt : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ (K LL : FinExt l) (k : ℤ), IsCrys (P.PD K) (charRep (cycLL (P.PD K) ↥LL.1 ^ k)) ∧ IsDR (P.PD K) (charRep (cycLL (P.PD K) ↥LL.1 ^ k)) ∧ ∀ (τ : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1) (a : ℤ), multV (P.PD K) (charRep (cycLL (P.PD K) ↥LL.1 ^ k)) τ a = if a = -k then 1 else 0 := by
  first | exact @GlobalTheory.CycPow.cyc_zpow_crys_dR_jump | exact GlobalTheory.CycPow.cyc_zpow_crys_dR_jump | (intros; apply GlobalTheory.CycPow.cyc_zpow_crys_dR_jump <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CyclotomicTowerFrobeniusFormulaPosWeightStatement
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc GlobalTheory.ExpImage
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cyclotomicTower_frobenius_formula_pos_weight : ∀ (LT : LocTheory) (l : ℕ) [Fact l.Prime] (AI : LocAinf l (LT l)), LocTied l (LT l) AI → ∀ (K : FinExt l) (s : ℕ), Lev l s → ∀ (e : ℕ), 1 ≤ e → ∀ (g : GQ l), g ∈ Gj K s → ((LT l).χQ g : ℚ_[l]) = ((1 + l ^ s : ℕ) : ℚ_[l]) → ∀ (lam : ℕ → ↥(K0 K)) (d : ↥(K0 K)), (∀ a, ‖(lam a : Om l)‖ ≤ 1) → ‖(d : Om l)‖ ≤ 1 → d - (l : ↥(K0 K)) ^ e * frK (LT l) K d = (frK (LT l) K ^ s) (∑ a ∈ primeTo l s, lam a) → ∃ z : GQ l → ℚ_[l], (∀ σ ∈ Gj K s, ‖z σ‖ ≤ 1) ∧ ExpStar LT (Gj K s) e z (algebraMap ℚ_[l] (Om l) ((((1 + l ^ s : ℕ) : ℚ_[l]) ^ e - 1) / (logZl l ((1 + l ^ s : ℕ) : ℚ_[l]) * ((e.factorial : ℚ_[l]) * (l : ℚ_[l]) ^ (s * e)))) * cycVal (LT l) K s e lam d) := by
  first | exact @GlobalTheory.ExpImage.PosWeight.formula_pos | exact GlobalTheory.ExpImage.PosWeight.formula_pos | (intros; apply GlobalTheory.ExpImage.PosWeight.formula_pos <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DeRhamComponentWachLetterBasisFiltrationStatement
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.deRhamComponent_wachLetter_basis_filtration : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL), let W := (HW l).W K s LL h; ∀ T : Lt K LL, IsCrys ((D.loc l).PD K) T.ρ → ∀ (i : Let K) (ζ : ↥LL.1) τ ι, Comp (HW l) h i ζ τ ι → τ.comp (IsScalarTower.toAlgHom ℚ_[l] ↥(K0 K) ↥K.1) = W.emb i → (∀ (r : ℕ) (d : Fin r → T.V ⊗[ℚ_[l]] (D.loc l).R.B) (b : Fin r → (D.loc l).R.BdR), (∀ a, d a ∈ Di (HW l) h T i) → LinearIndependent ↥LL.1 d → ∑ a, mulVR T (b a) (ιV ((D.loc l).PD K) (LL := ↥LL.1) (V := T.V) (d a)) ∈ compKer T ι → ∀ a, b a = 0) ∧ (∀ d ∈ Di (HW l) h T i, ∀ a : ℤ, ιV ((D.loc l).PD K) (LL := ↥LL.1) (V := T.V) d ∈ FilAt ((D.loc l).PD K) T τ a ↔ ιV ((D.loc l).PD K) (LL := ↥LL.1) (V := T.V) d ∈ compKer T ι ⊔ FilV ((D.loc l).PD K) (LL := ↥LL.1) (V := T.V) a) ∧ (∀ w ∈ DdRE ((D.loc l).PD K) T.ρ τ, ∃ d ∈ Di (HW l) h T i, ιV ((D.loc l).PD K) (LL := ↥LL.1) (V := T.V) d - w ∈ ⨆ (τ' : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1) (_ : τ' ≠ τ), DdRE ((D.loc l).PD K) T.ρ τ') ∧ Module.finrank ↥LL.1 ↥(Di (HW l) h T i) = Module.finrank ↥LL.1 T.V := by
  first | exact @GlobalTheory.NL.CompD.component | exact GlobalTheory.NL.CompD.component | (intros; apply GlobalTheory.NL.CompD.component <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DeRhamComponentsCrystallineLettersFinrank
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module

namespace GlobalTheory.Per.Components

theorem card_le_of_idem_indep {R : Type} [CommRing R] {e : R} (he : e * e = e) (he0 : e ≠ 0)
    {ι κ : Type} [Fintype ι] [Fintype κ] (a : ι → κ → R)
    (h : ∀ r : ι → R, (∀ j, ∑ i, r i * a i j = 0) → ∀ i, e * r i = 0) :
    Fintype.card ι ≤ Fintype.card κ := by
  let I : Ideal R := Ideal.span {1 - e}
  have hI : ∀ x, x ∈ I ↔ e * x = 0 := by
    intro x
    rw [Ideal.mem_span_singleton']
    constructor
    · rintro ⟨c, rfl⟩
      linear_combination (-c) * he
    · intro hx
      exact ⟨x, by linear_combination -hx⟩
  haveI : Nontrivial (R ⧸ I) := Ideal.Quotient.nontrivial_iff.2 (by
    intro hT
    have : (1 : R) ∈ I := by rw [hT]; trivial
    rw [hI, mul_one] at this
    exact he0 this)
  have hli : LinearIndependent (R ⧸ I) (fun i j => Ideal.Quotient.mk I (a i j)) := by
    rw [Fintype.linearIndependent_iff]
    intro g hg i
    choose r hr using fun i => Ideal.Quotient.mk_surjective (g i)
    rw [← hr, Ideal.Quotient.eq_zero_iff_mem, hI, ← he, mul_assoc]
    refine h (fun i => e * r i) (fun j => ?_) i
    have := congrFun hg j
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, ← hr, ← map_mul,
      ← map_sum] at this
    rw [Ideal.Quotient.eq_zero_iff_mem, hI, Finset.mul_sum] at this
    simpa only [mul_assoc] using this
  simpa using hli.fintype_card_le_finrank

section Bound

variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B F : Type} [CommRing B] [CommRing F] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp F] [Algebra K₀ F] [Algebra K F] [IsScalarTower Qp K F]
    [IsScalarTower K₀ K F] [IsScalarTower Qp K₀ F]
    (PD : PeriodData G Qp K₀ K B F)
    {LL : Type} [Field LL] [Algebra Qp LL] [FiniteDimensional Qp LL] [FiniteDimensional Qp K]
    [CharZero Qp]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    [FiniteDimensional LL V]

open GlobalTheory.DRFil in

theorem finrank_DdRE_le (hF : IsField F) (ρ : Representation LL G V) (τ : K →ₐ[Qp] LL)
    [FiniteDimensional LL ↥(DdRE PD ρ τ)] : finrank LL ↥(DdRE PD ρ τ) ≤ finrank LL V := by
  haveI := nontrivial_dR PD
  let b := Module.finBasis LL ↥(DdRE PD ρ τ)
  let v := Module.finBasis LL V
  have hli : LinearIndependent LL (fun i => (b i : V ⊗[Qp] F)) :=
    b.linearIndependent.map' (DdRE PD ρ τ).subtype (Submodule.ker_subtype _)
  have h := indep_of_linearIndependent_DdRE PD ρ τ _ hF (fun i => (b i).2) hli
  have := card_le_of_idem_indep (idem_mul_idem (F := F) τ) (idem_ne_zero (F := F) τ)
    (fun i j => ext Qp F (v.coord j) (b i : V ⊗[Qp] F)) (fun r hr => h r (by
      rw [eq_sum_basis v (∑ i, sm Qp F LL V (r i) (b i : V ⊗[Qp] F))]
      refine Finset.sum_eq_zero fun j _ => ?_
      rw [map_sum]
      simp only [ext_sm, sm_self]
      rw [hr j, map_zero, LinearMap.zero_apply]))
  simpa using this

end Bound

theorem exists_baseChange {G : Type} [Group G] (Qp LL LL' : Type) [Field Qp] [Field LL] [Field LL']
    [Algebra Qp LL] [Algebra Qp LL'] [Algebra LL LL'] [IsScalarTower Qp LL LL']
    {V : Type} [AddCommGroup V] [Module LL V] [FiniteDimensional LL V] (ρ : Representation LL G V) :
    ∃ (V' : Type) (_ : AddCommGroup V') (_ : Module LL' V') (_ : Module LL V') (_ : Module Qp V')
      (_ : IsScalarTower Qp LL' V') (_ : IsScalarTower LL LL' V') (_ : FiniteDimensional LL' V')
      (ρ' : Representation LL' G V') (j : V →ₗ[LL] V'),
      IsBaseChange LL' j ∧ ∀ g x, j (ρ g x) = ρ' g (j x) :=
  ⟨LL' ⊗[LL] V, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, (Module.End.baseChangeHom LL LL' V).toMonoidHom.comp ρ, TensorProduct.mk LL LL' V 1,
    TensorProduct.isBaseChange LL V LL', fun _ _ => rfl⟩

theorem components_finrank : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ (K LL : FinExt l) (V : Type) [AddCommGroup V] [Module ↥LL.1 V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] ↥LL.1 V] [FiniteDimensional ↥LL.1 V] (ρ : Representation ↥LL.1 ↥(GK K) V), (∀ τ, FiniteDimensional ↥LL.1 ↥(DdRE (P.PD K) ρ τ) ∧ finrank ↥LL.1 ↥(DdRE (P.PD K) ρ τ) ≤ finrank ↥LL.1 V ∧ (IsDR (P.PD K) ρ → finrank ↥LL.1 ↥(DdRE (P.PD K) ρ τ) = finrank ↥LL.1 V)) ∧ ∀ τ, IsCrys (P.PD K) ρ → finrank ↥LL.1 ↥(DcrisL (P.PD K) ρ τ) = finrank ↥LL.1 V := by
  intro l _ P AI T K LL V _ _ _ _ _ ρ
  haveI := LL.2
  haveI := K.2
  obtain ⟨LL', ⟨f⟩, hK, hK0⟩ := GlobalTheory.exists_finExt_embedding_splitting l K ↥LL.1
  haveI := LL'.2
  letI : Algebra ↥LL.1 ↥LL'.1 := f.toRingHom.toAlgebra
  haveI : IsScalarTower ℚ_[l] ↥LL.1 ↥LL'.1 := IsScalarTower.of_algebraMap_eq fun x => (f.commutes x).symm
  haveI : FiniteDimensional ↥LL.1 ↥LL'.1 := Module.Finite.of_restrictScalars_finite ℚ_[l] _ _
  obtain ⟨V', _, _, _, _, _, _, _, ρ', j, hj, hρj⟩ := exists_baseChange ℚ_[l] ↥LL.1 ↥LL'.1 ρ
  obtain ⟨hV, -, ⟨hc, -⟩, ⟨hd, -⟩, -, hl, he⟩ := GlobalTheory.T.finrank_periodFunctor_coeff_baseChange (P.PD K) ↥LL.1 ↥LL'.1 V V' ρ ρ' j hj hρj
  obtain ⟨h1, h2⟩ := GlobalTheory.T.finrank_dcrisLetter_deRhamComponent_eq_dim l P AI T K LL' V' ρ'
  refine ⟨fun τ => ?_, fun τ hρ => ?_⟩
  · haveI := (GlobalTheory.Per.TiedDdR.ddR_finrank_le l P AI T K LL V ρ).1
    haveI : FiniteDimensional ↥LL.1 ↥(DdRE (P.PD K) ρ τ) :=
      Submodule.finiteDimensional_of_le (S₂ := DdR (P.PD K) ρ) inf_le_left
    refine ⟨this, finrank_DdRE_le (P.PD K) (GlobalTheory.Per.FontaineBound.isField_of_tied T) ρ τ, fun hρ => ?_⟩
    rw [← (he τ).1, ← hV]
    refine h2 hK ?_ _
    unfold IsDR at hρ ⊢
    rw [hd, hV, hρ]
  · rw [← hl τ, ← hV]
    refine h1 hK0 ?_ _
    unfold IsCrys at hρ ⊢
    rw [hc, hV, hρ]

end GlobalTheory.Per.Components
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DeRhamFiltrationDuality
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module

namespace GlobalTheory.TateDualTied

theorem main : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI →
    ∀ K : FinExt l, drDualCore (P.PD K) ∧ Formalism.MainNotions.LocalSituation.filDualCore (P.PD K) := by
  intro l _ P AI T K
  refine ⟨fun LL _ _ _ O _ _ hO A A' m h hm => ?_, fun LL _ _ _ O _ _ hO A A' m h hm => ?_⟩
  · haveI := hO.2.1
    exact (GlobalTheory.TateDualFil.tateDual l P AI T K LL A.ρ A'.ρ m h hm).1
  · haveI := hO.2.1
    exact (GlobalTheory.TateDualFil.tateDual l P AI T K LL A.ρ A'.ρ m h hm).2

end GlobalTheory.TateDualTied
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DividedPowerSeriesSubringEqGeneratorSetStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Filter GlobalTheory.CrysPrism
open scoped Formalism.Per

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_sdSet_of_mem_sd : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] (t : Wq l a →ₐ[ℤ_[l]] O), ∀ F ∈ Sd t K e, F ∈ SdSet t K e := by
  first | exact @GlobalTheory.CrysPrism.sdSet_closed | exact GlobalTheory.CrysPrism.sdSet_closed | (intros; apply GlobalTheory.CrysPrism.sdSet_closed <;> assumption)
end

