import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0052
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.KerInclOn
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.PoincareInHH

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IntegralAdeleCongrZeroOfResiduesSquarefree
section
open NumberField IsDedekindDomain Matrix Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.DIV GlobalTheory.FlagBasis
open scoped TensorProduct

namespace GlobalTheory.AdeleSquarefree

theorem mem_span_of_forall_prime {A : Type} [CommRing A] [IsDedekindDomain A] (x : A) (hx : x ≠ 0)
    (hsq : ∀ Q : HeightOneSpectrum A, x ∈ Q.asIdeal → x ∉ Q.asIdeal ^ 2) (a : A)
    (ha : ∀ Q : HeightOneSpectrum A, x ∈ Q.asIdeal → a ∈ Q.asIdeal) : a ∈ Ideal.span {x} := by
  have h0 : (Ideal.span {x} : Ideal A) ≠ ⊥ := by
    simpa [Ideal.span_singleton_eq_bot] using hx
  have hsf : Squarefree (Ideal.span {x} : Ideal A) := by
    refine (squarefree_iff_irreducible_sq_not_dvd_of_ne_zero h0).2 fun P hP hd => ?_
    have hPp : Prime P := hP.prime
    have hPb : P ≠ ⊥ := hPp.ne_zero
    have hle : Ideal.span {x} ≤ P ^ 2 := by
      rw [pow_two]; exact Ideal.dvd_iff_le.1 hd
    have hx2 : x ∈ P ^ 2 := hle (Ideal.mem_span_singleton_self x)
    exact hsq ⟨P, (Ideal.prime_iff_isPrime hPb).1 hPp, hPb⟩ (Ideal.pow_le_self two_ne_zero hx2) hx2
  have hrad : a ∈ (Ideal.span {x} : Ideal A).radical := by
    rw [Ideal.radical_eq_sInf, Ideal.mem_sInf]
    rintro J ⟨hJ, hJp⟩
    have hJb : J ≠ ⊥ := fun h => h0 (le_bot_iff.1 (h ▸ hJ))
    exact ha ⟨J, hJp, hJb⟩ (hJ (Ideal.mem_span_singleton_self x))
  obtain ⟨n, hn⟩ := hrad
  have hd : (Ideal.span {x} : Ideal A) ∣ (Ideal.span {a}) ^ n := by
    rw [Ideal.span_singleton_pow, Ideal.dvd_iff_le, Ideal.span_singleton_le_iff_mem]
    exact hn
  have h2 := hsf.isRadical n _ hd
  rw [Ideal.dvd_iff_le, Ideal.span_singleton_le_iff_mem] at h2
  exact h2

theorem zmod_of_forall_resS_eq_zero : ∀ (I : AutInst) (g : ℕ), g ≠ 0 →
    (∀ Q : Pl I.E, (g : 𝓞 I.E) ∈ Q.asIdeal → (g : 𝓞 I.E) ∉ Q.asIdeal ^ 2) →
    ∀ s : Formalism.L2.Herm.intAf I.F I.E, (∀ Q : Pl I.E, (g : 𝓞 I.E) ∈ Q.asIdeal → resS I.F Q s = 0) → ZMod' I g s := by
  intro I g hg hsq s hs
  have hg' : (g : 𝓞 I.E) ≠ 0 := by exact_mod_cast hg
  have h0 : (Ideal.span {(g : 𝓞 I.E)} : Ideal (𝓞 I.E)) ≠ ⊥ := by
    simpa [Ideal.span_singleton_eq_bot] using hg
  have hid : idS I.F (Ideal.span {(g : 𝓞 I.E)}) = Ideal.span {oToS I.F I.E (g : 𝓞 I.E)} := by
    rw [idS, Ideal.map_span, Set.image_singleton]
  obtain ⟨q, hq⟩ := (cmpS_bij (F := I.F) _ h0).2 (Ideal.Quotient.mk _ s)
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective q
  have hq' : Ideal.Quotient.mk (idS I.F (Ideal.span {(g : 𝓞 I.E)})) (oToS I.F I.E a) =
      Ideal.Quotient.mk (idS I.F (Ideal.span {(g : 𝓞 I.E)})) s := hq
  have hm := Ideal.Quotient.eq.1 hq'.symm
  rw [hid, Ideal.mem_span_singleton] at hm
  obtain ⟨u, hu⟩ := hm
  have hsu : s = oToS I.F I.E a + oToS I.F I.E (g : 𝓞 I.E) * u := by rw [← hu]; ring
  have ha : a ∈ Ideal.span {(g : 𝓞 I.E)} := by
    refine mem_span_of_forall_prime _ hg' hsq a fun Q hQ => ?_
    have h1 := hs Q hQ
    rw [hsu, map_add, map_mul, resS_oToS, resS_oToS, Ideal.Quotient.eq_zero_iff_mem.2 hQ, zero_mul, add_zero] at h1
    exact Ideal.Quotient.eq_zero_iff_mem.1 h1
  obtain ⟨b, hb⟩ := Ideal.mem_span_singleton.1 ha
  have hfin : s = (g : Formalism.L2.Herm.intAf I.F I.E) * (oToS I.F I.E b + u) := by
    rw [hsu, hb, map_mul, map_natCast]; ring
  refine ⟨((oToS I.F I.E b + u : Formalism.L2.Herm.intAf I.F I.E) : I.E ⊗[I.F] Af I.F), (oToS I.F I.E b + u).2, ?_⟩
  conv_lhs => rw [hfin]
  push_cast
  rfl

end GlobalTheory.AdeleSquarefree
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LevelPrimeWindow
section
noncomputable section

namespace GlobalTheory.Core.Rk

open Formalism.BasicNotions Formalism.MainNotions.S
open scoped InnerProductSpace

theorem levelPrime_window : ∀ (D : D7) (u : D.what₂.Word),
    (RankMu D u → (d0 D u : ℝ) ≤ Real.exp 1 / (D.mem u).A.GamP ^ 2 * D.what₂.Dstar) ∧
    (Real.log (D.mem u).A.Xu - 2 * Real.log (D.mem u).A.GamP / ((D.R.f : ℝ) * D.R.k) ≤ Real.log ((D.mem u).A.T : ℝ)) ∧
    (∀ L C : ℝ, RankMu D u → 1 + 2 * C * mfL D L ≤ 2 * Real.log (D.mem u).A.GamP → Small D u L C) := by
  intro D u
  have hfN : 1 ≤ D.R.f := by
    apply Nat.one_le_iff_ne_zero.2
    unfold Ranks.f Ranks.n; positivity
  have hkN : 5 ≤ D.R.k := by have := D.R.m_add_three_le_k; have := D.R.two_le_m; omega
  have hf : (1 : ℝ) ≤ D.R.f := by exact_mod_cast hfN
  have hk : (5 : ℝ) ≤ D.R.k := by exact_mod_cast hkN
  have hfk : (0 : ℝ) < (D.R.f : ℝ) * D.R.k := by positivity
  have hdu : (0 : ℝ) < (D.mem u).A.duStar := by exact_mod_cast (D.mem u).A.duStar_pos
  have hDs : 0 < (D.mem u).A.Dstar := (D.mem u).A.Dstar_pos
  have hDpos : 0 < D.what₂.Dstar := D.Dstar_eq u ▸ hDs
  have hq : 0 < (D.mem u).A.Dstar / (D.mem u).A.duStar := div_pos hDs hdu
  have hGp : 0 < (D.mem u).A.GamP := lt_trans one_pos (D.mem u).A.one_lt_gammaP
  have hXu : 0 < (D.mem u).A.Xu := Real.rpow_pos_of_pos hq _
  have hTs : 0 < (D.mem u).A.Tstar := mul_pos hXu (Real.rpow_pos_of_pos hGp _)
  have hlogTs : Real.log (D.mem u).A.Tstar =
      Real.log (D.mem u).A.Xu - 2 * Real.log (D.mem u).A.GamP / ((D.R.f : ℝ) * D.R.k) := by
    unfold ColumnsAtT.Tstar
    rw [Real.log_mul hXu.ne' (Real.rpow_pos_of_pos hGp _).ne', Real.log_rpow hGp]
    ring
  obtain ⟨hT1, hT2⟩ := D.T_win u
  have hT0 : (0 : ℝ) < ((D.mem u).A.T : ℝ) := hTs.trans_le hT1
  have part2 : Real.log (D.mem u).A.Xu - 2 * Real.log (D.mem u).A.GamP / ((D.R.f : ℝ) * D.R.k) ≤
      Real.log ((D.mem u).A.T : ℝ) := by
    rw [← hlogTs]; exact Real.log_le_log hTs hT1
  have hTs_pow : (D.mem u).A.Tstar ^ (D.R.f * D.R.k) =
      (D.mem u).A.Dstar / (D.mem u).A.duStar / (D.mem u).A.GamP ^ 2 := by
    have hn : ((D.R.f * D.R.k : ℕ) : ℝ) = (D.R.f : ℝ) * D.R.k := by push_cast; ring
    rw [← Real.rpow_natCast, hn]
    unfold ColumnsAtT.Tstar ColumnsAtT.Xu
    rw [Real.mul_rpow (Real.rpow_pos_of_pos hq _).le (Real.rpow_pos_of_pos hGp _).le, ← Real.rpow_mul hq.le,
      ← Real.rpow_mul hGp.le, one_div_mul_cancel hfk.ne', div_mul_cancel₀ _ hfk.ne', Real.rpow_one,
      Real.rpow_neg hGp.le, Real.rpow_two, div_eq_mul_inv _ ((D.mem u).A.GamP ^ 2)]
  have hexp : (1 + 1 / ((D.R.f : ℝ) * D.R.k)) ^ (D.R.f * D.R.k) ≤ Real.exp 1 := by
    have h := Real.add_one_le_exp (1 / ((D.R.f : ℝ) * D.R.k))
    calc (1 + 1 / ((D.R.f : ℝ) * D.R.k)) ^ (D.R.f * D.R.k)
        ≤ Real.exp (1 / ((D.R.f : ℝ) * D.R.k)) ^ (D.R.f * D.R.k) :=
          pow_le_pow_left₀ (by positivity) (by linarith) _
      _ = Real.exp 1 := by
          rw [← Real.exp_nat_mul]; congr 1; push_cast; field_simp
  have hTpow : ((D.mem u).A.T : ℝ) ^ (D.R.f * D.R.k) ≤
      Real.exp 1 * ((D.mem u).A.Dstar / (D.mem u).A.duStar / (D.mem u).A.GamP ^ 2) := by
    calc ((D.mem u).A.T : ℝ) ^ (D.R.f * D.R.k)
        ≤ ((1 + 1 / ((D.R.f : ℝ) * D.R.k)) * (D.mem u).A.Tstar) ^ (D.R.f * D.R.k) :=
          pow_le_pow_left₀ hT0.le hT2 _
      _ = (1 + 1 / ((D.R.f : ℝ) * D.R.k)) ^ (D.R.f * D.R.k) *
          ((D.mem u).A.Dstar / (D.mem u).A.duStar / (D.mem u).A.GamP ^ 2) := by
          rw [mul_pow, hTs_pow]
      _ ≤ _ := mul_le_mul_of_nonneg_right hexp (by positivity)
  have part1 : RankMu D u → (d0 D u : ℝ) ≤ Real.exp 1 / (D.mem u).A.GamP ^ 2 * D.what₂.Dstar := by
    intro h
    unfold RankMu at h
    rw [h]
    have hT1' : (1 : ℝ) ≤ ((D.mem u).A.T : ℝ) := by
      have : 0 < (D.mem u).A.T := by exact_mod_cast hT0
      exact_mod_cast this
    have hTk : 1 ≤ ((D.mem u).A.T : ℝ) ^ D.R.k := one_le_pow₀ hT1'
    have h1 : (((D.mem u).A.T : ℝ) ^ D.R.k - 1) ^ D.R.f ≤ ((D.mem u).A.T : ℝ) ^ (D.R.f * D.R.k) := by
      rw [mul_comm, pow_mul]
      exact pow_le_pow_left₀ (by linarith) (by linarith) _
    calc ((D.mem u).A.duStar : ℝ) * (((D.mem u).A.T : ℝ) ^ D.R.k - 1) ^ D.R.f
        ≤ ((D.mem u).A.duStar : ℝ) *
          (Real.exp 1 * ((D.mem u).A.Dstar / (D.mem u).A.duStar / (D.mem u).A.GamP ^ 2)) :=
          mul_le_mul_of_nonneg_left (h1.trans hTpow) hdu.le
      _ = Real.exp 1 / (D.mem u).A.GamP ^ 2 * D.what₂.Dstar := by
          rw [← D.Dstar_eq u]
          first | (field_simp; ring) | field_simp
  refine ⟨part1, part2, fun L C hR hLC => ?_⟩
  unfold Small
  have hG2 : Real.exp (2 * Real.log (D.mem u).A.GamP) = (D.mem u).A.GamP ^ 2 := by
    rw [show 2 * Real.log (D.mem u).A.GamP = Real.log ((D.mem u).A.GamP ^ 2) by rw [Real.log_pow]; push_cast; ring,
      Real.exp_log (by positivity)]
  calc (d0 D u : ℝ) ≤ Real.exp 1 / (D.mem u).A.GamP ^ 2 * D.what₂.Dstar := part1 hR
    _ = D.what₂.Dstar * Real.exp (1 - 2 * Real.log (D.mem u).A.GamP) := by
        rw [Real.exp_sub, hG2]; ring
    _ ≤ D.what₂.Dstar * Real.exp (-(2 * C * mfL D L)) :=
        mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 (by linarith)) hDpos.le

end GlobalTheory.Core.Rk

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ScalWIdent
section
open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.DIV GlobalTheory.FlagBasis
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.ScalW

variable {D : D7} (X : HidaSetting D) (u : D.what₂.Word)

def eV (a : Fin D.R.rS) : VA X.B.I := incl X.B.I (X.eR a)

def fV (a : Fin D.R.rS) : VA X.B.I := incl X.B.I (X.fR a)

def zV : VA X.B.I := incl X.B.I (X.zR u)

def prj (y : VA X.B.I) : VA X.B.I :=
  ∑ a, hA X.B.I (fV X a) y • eV X a + ∑ a, hA X.B.I (eV X a) y • fV X a
    - divN X.B.I (D.mem u).A.T (hA X.B.I (zV X u) y) • zV X u

def prjL : VA X.B.I →ₗ[X.B.I.E ⊗[X.B.I.F] Af X.B.I.F] VA X.B.I where
  toFun := prj X u
  map_add' y z := by
    simp only [prj, Formalism.L2.SG.Pf.unitaryCongruence.hA_add_right, add_smul, Finset.sum_add_distrib, divN, mul_add]
    abel
  map_smul' c y := by
    simp only [prj, Formalism.L2.SG.Pf.unitaryCongruence.hA_smul_right, mul_smul, smul_sub, smul_add, Finset.smul_sum, divN,
      RingHom.id_apply, mul_left_comm _ c]

def prjM : Matrix (Fin X.B.I.n) (Fin X.B.I.n) (X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) := LinearMap.toMatrix' (prjL X u)

def hMat (c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) : Matrix (Fin X.B.I.n) (Fin X.B.I.n) (X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) :=
  c • 1 + (1 - c) • prjM X u

def prj0 (y : VA X.B.I) : VA X.B.I :=
  ∑ a, hA X.B.I (X.f0 a) y • X.e0 a + ∑ a, hA X.B.I (X.e0 a) y • X.f0 a - hA X.B.I X.z0 y • X.z0

theorem prjM_mulVec (y : VA X.B.I) : prjM X u *ᵥ y = prj X u y := by
  rw [prjM, LinearMap.toMatrix'_mulVec]; rfl

theorem hMat_mulVec (c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) (y : VA X.B.I) :
    hMat X u c *ᵥ y = c • y + (1 - c) • prj X u y := by
  rw [hMat, Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.smul_mulVec, one_mulVec, prjM_mulVec]

theorem scalW_ident {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V] (mb mc m6 tt dd : R) (S1 S2 S3 S4 z' w0 : V) :
    (mb * mc * m6 * tt) • (S1 + S2 - dd • z' - (S3 + S4 - w0)) = (mc * m6 * tt) • (mb • (S1 - S3)) + (mc * m6 * tt) • (mb • (S2 - S4))
      - (mb * m6) • (mc • ((tt * dd) • z' - w0)) - (mb * mc) • ((m6 * (1 - tt)) • w0) := by
  module

end GlobalTheory.ScalW
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SymmetricUnipotentMemOfFlagBasisDual
section
open NumberField IsDedekindDomain Matrix Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.DIV GlobalTheory.FlagBasis
open scoped TensorProduct

namespace GlobalTheory.FlagDual

theorem dualIdx_lt {n ρ k : ℕ} (hn : n = 2 * ρ + k + 1) {i : ℕ} (hi : i < n) : dualIdx ρ k i < n := by
  unfold dualIdx; split_ifs <;> omega

theorem dualIdx_dualIdx {n ρ k : ℕ} (hn : n = 2 * ρ + k + 1) {i : ℕ} (hi : i < n) :
    dualIdx ρ k (dualIdx ρ k i) = i := by
  unfold dualIdx; split_ifs <;> omega

theorem dualIdx_eq_self_iff {n ρ k i : ℕ} (hn : n = 2 * ρ + k + 1) (hi : i < n) : dualIdx ρ k i = ρ + k ↔ i = ρ + k := by
  unfold dualIdx; split_ifs <;> omega

def tau {n ρ k : ℕ} (hn : n = 2 * ρ + k + 1) (i : Fin n) : Fin n := ⟨dualIdx ρ k i.val, dualIdx_lt hn i.2⟩

def sgn (K : Type) [CommRing K] (ρ k : ℕ) {n : ℕ} (i : Fin n) : K := if i.val = ρ + k then -1 else 1

theorem sgn_mul_self (K : Type) [CommRing K] (ρ k : ℕ) {n : ℕ} (i : Fin n) : sgn K ρ k i * sgn K ρ k i = 1 := by
  unfold sgn; split_ifs <;> simp

theorem gram_col (K : Type) [CommRing K] {n ρ k : ℕ} (hn : n = 2 * ρ + k + 1) (i j : Fin n) :
    flagGram K n ρ k i j = if i = tau hn j then sgn K ρ k j else 0 := by
  have hi := dualIdx_dualIdx hn i.2
  have hj := dualIdx_dualIdx hn j.2
  unfold flagGram sgn
  by_cases h1 : j.val = dualIdx ρ k i.val
  · have h2 : i = tau hn j := by
      ext; show i.val = dualIdx ρ k j.val; rw [h1, hi]
    rw [if_pos h1, if_pos h2]
    have h3 : (i.val = ρ + k ↔ j.val = ρ + k) := by
      rw [h1, dualIdx_eq_self_iff hn i.2]
    by_cases h4 : i.val = ρ + k
    · rw [if_pos h4, if_pos (h3.1 h4)]
    · rw [if_neg h4, if_neg (fun h => h4 (h3.2 h))]
  · have h2 : i ≠ tau hn j := by
      intro h; apply h1; rw [h]; show j.val = dualIdx ρ k (dualIdx ρ k j.val); rw [hj]
    rw [if_neg h1, if_neg h2]

theorem gram_row (K : Type) [CommRing K] {n ρ k : ℕ} (hn : n = 2 * ρ + k + 1) (i j : Fin n) :
    flagGram K n ρ k i j = if j = tau hn i then sgn K ρ k i else 0 := by
  unfold flagGram sgn
  by_cases h1 : j.val = dualIdx ρ k i.val
  · rw [if_pos h1, if_pos (Fin.ext h1)]
  · rw [if_neg h1, if_neg (fun h => h1 (congrArg Fin.val h))]

theorem gram_mul_gram (K : Type) [CommRing K] {n ρ k : ℕ} (hn : n = 2 * ρ + k + 1) :
    flagGram K n ρ k * flagGram K n ρ k = 1 := by
  ext i j
  rw [mul_apply, Finset.sum_eq_single (tau hn i)]
  · rw [gram_row K hn i (tau hn i), if_pos rfl, gram_row K hn (tau hn i) j]
    have hii : tau hn (tau hn i) = i := Fin.ext (dualIdx_dualIdx hn i.2)
    rw [hii]
    by_cases hij : j = i
    · subst hij; rw [if_pos rfl, one_apply_eq]
      have : sgn K ρ k (tau hn j) = sgn K ρ k j := by
        unfold sgn tau; simp only [dualIdx_eq_self_iff hn j.2]
      rw [this, sgn_mul_self]
    · rw [if_neg hij, mul_zero, one_apply_ne (Ne.symm hij)]
  · intro b _ hb; rw [gram_row K hn i b, if_neg hb, zero_mul]
  · intro h; exact absurd (Finset.mem_univ _) h

theorem gram_conj_apply (K : Type) [CommRing K] {n ρ k : ℕ} (hn : n = 2 * ρ + k + 1)
    (A : Matrix (Fin n) (Fin n) K) (i j : Fin n) :
    (flagGram K n ρ k * A * flagGram K n ρ k) i j = sgn K ρ k i * sgn K ρ k j * A (tau hn i) (tau hn j) := by
  rw [mul_apply, Finset.sum_eq_single (tau hn j)]
  · rw [gram_col K hn (tau hn j) j, if_pos rfl, mul_apply, Finset.sum_eq_single (tau hn i)]
    · rw [gram_row K hn i (tau hn i), if_pos rfl]; ring
    · intro b _ hb; rw [gram_row K hn i b, if_neg hb, zero_mul]
    · intro h; exact absurd (Finset.mem_univ _) h
  · intro b _ hb; rw [gram_col K hn b j, if_neg hb, mul_zero]
  · intro h; exact absurd (Finset.mem_univ _) h

end GlobalTheory.FlagDual

namespace GlobalTheory.FlagDual

theorem dual_apply (K : Type) [CommRing K] {n ρ k : ℕ} (hn : n = 2 * ρ + k + 1) (M M' : GL (Fin n) K)
    (h : (M' : Matrix (Fin n) (Fin n) K)ᵀ * flagGram K n ρ k * (M : Matrix (Fin n) (Fin n) K) = flagGram K n ρ k)
    (i j : Fin n) :
    (M' : Matrix (Fin n) (Fin n) K) i j =
      sgn K ρ k j * sgn K ρ k i * ((M⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) (tau hn j) (tau hn i) := by
  set G := flagGram K n ρ k
  have h1 : (M' : Matrix (Fin n) (Fin n) K)ᵀ * G = G * ((M⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
    have hM : (M : Matrix (Fin n) (Fin n) K) * ((M⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = 1 := by
      rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
    calc (M' : Matrix (Fin n) (Fin n) K)ᵀ * G
        = (M' : Matrix (Fin n) (Fin n) K)ᵀ * G * ((M : Matrix (Fin n) (Fin n) K) *
            ((M⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) := by rw [hM, Matrix.mul_one]
      _ = G * ((M⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by rw [← Matrix.mul_assoc, h]
  have h2 : (M' : Matrix (Fin n) (Fin n) K)ᵀ = G * ((M⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * G := by
    rw [← h1, Matrix.mul_assoc, gram_mul_gram K hn, Matrix.mul_one]
  have h3 := congrFun (congrFun h2 j) i
  rw [transpose_apply] at h3
  rw [h3, gram_conj_apply K hn]

end GlobalTheory.FlagDual

theorem GlobalTheory.FlagDual.unipSym_of_dual :
    ∀ (K : Type) [CommRing K] (n ρ k : ℕ), n = 2 * ρ + k + 1 → ∀ M M' : GL (Fin n) K,
      (M' : Matrix (Fin n) (Fin n) K)ᵀ * flagGram K n ρ k * (M : Matrix (Fin n) (Fin n) K) = flagGram K n ρ k →
      M ∈ unipSym K n ρ k → M' ∈ unipSym K n ρ k := by
  intro K _ n ρ k hn M M' h hM
  have hN : M⁻¹ ∈ unipSym K n ρ k := Subgroup.inv_mem _ hM
  obtain ⟨⟨hNl, hNd⟩, hNc⟩ := hN
  have hd := GlobalTheory.FlagDual.dual_apply K hn M M' h
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro i j hji
    have hji' : j.val < i.val := hji
    rw [hd i j]
    by_cases hi : i.val = ρ + k
    · by_cases hj : j.val < ρ
      · rw [hNl (show (GlobalTheory.FlagDual.tau hn i).val < (GlobalTheory.FlagDual.tau hn j).val by
          show dualIdx ρ k i.val < dualIdx ρ k j.val
          unfold dualIdx; split_ifs <;> omega), mul_zero]
      · rw [hNc (GlobalTheory.FlagDual.tau hn j) (GlobalTheory.FlagDual.tau hn i)
          (by show ρ ≤ dualIdx ρ k j.val; unfold dualIdx; split_ifs <;> omega)
          (by show dualIdx ρ k j.val < ρ + k; unfold dualIdx; split_ifs <;> omega)
          (by show dualIdx ρ k i.val = ρ + k; unfold dualIdx; split_ifs <;> omega), mul_zero]
    · rw [hNl (show (GlobalTheory.FlagDual.tau hn i).val < (GlobalTheory.FlagDual.tau hn j).val by
        have := i.2; have := j.2
        show dualIdx ρ k i.val < dualIdx ρ k j.val
        unfold dualIdx; split_ifs <;> omega), mul_zero]
  · intro i
    rw [hd i i, hNd, mul_one, GlobalTheory.FlagDual.sgn_mul_self]
  · intro i j h0 h1 h2
    rw [hd i j, hNl (show (GlobalTheory.FlagDual.tau hn i).val < (GlobalTheory.FlagDual.tau hn j).val by
      show dualIdx ρ k i.val < dualIdx ρ k j.val
      unfold dualIdx; split_ifs <;> omega), mul_zero]
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SymmetricUnipotentMemOfFlagCongruenceDual
section
open NumberField IsDedekindDomain Matrix Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.DIV GlobalTheory.FlagBasis
open scoped TensorProduct

namespace GlobalTheory.FlagCase

theorem dualIdx_lt' {ρ k a : ℕ} (h : a < 2 * ρ + k + 1) : dualIdx ρ k a < 2 * ρ + k + 1 := by
  unfold dualIdx; split_ifs <;> omega

theorem dualIdx_iff' {ρ k a b : ℕ} (ha : a < 2 * ρ + k + 1) (hb : b < 2 * ρ + k + 1) :
    a = dualIdx ρ k b ↔ b = dualIdx ρ k a := by
  unfold dualIdx; split_ifs <;> omega

theorem mul_flagGram_apply {K : Type} [CommRing K] {ρ k : ℕ}
    (A : Matrix (Fin (2 * ρ + k + 1)) (Fin (2 * ρ + k + 1)) K) (i j : Fin (2 * ρ + k + 1)) :
    (A * flagGram K (2 * ρ + k + 1) ρ k) i j =
      A i ⟨dualIdx ρ k j.val, dualIdx_lt' j.2⟩ * (if dualIdx ρ k j.val = ρ + k then -1 else 1) := by
  rw [mul_apply, Finset.sum_eq_single ⟨dualIdx ρ k j.val, dualIdx_lt' j.2⟩]
  · simp only [flagGram, Fin.val_mk]
    rw [if_pos ((dualIdx_iff' j.2 (dualIdx_lt' j.2)).mpr rfl)]
  · intro l _ hl
    simp only [flagGram]
    rw [if_neg, mul_zero]
    intro h
    exact hl (Fin.ext ((dualIdx_iff' j.2 l.2).mp h))
  · intro h; exact absurd (Finset.mem_univ _) h

theorem flagGram_mul_apply {K : Type} [CommRing K] {ρ k : ℕ}
    (A : Matrix (Fin (2 * ρ + k + 1)) (Fin (2 * ρ + k + 1)) K) (i j : Fin (2 * ρ + k + 1)) :
    (flagGram K (2 * ρ + k + 1) ρ k * A) i j =
      (if i.val = ρ + k then -1 else 1) * A ⟨dualIdx ρ k i.val, dualIdx_lt' i.2⟩ j := by
  rw [mul_apply, Finset.sum_eq_single ⟨dualIdx ρ k i.val, dualIdx_lt' i.2⟩]
  · simp only [flagGram, Fin.val_mk, if_true]
  · intro l _ hl
    simp only [flagGram]
    rw [if_neg, zero_mul]
    intro h
    exact hl (Fin.ext h)
  · intro h; exact absurd (Finset.mem_univ _) h

theorem flagCond_dual_unipSym : ∀ (K : Type) [CommRing K] (n ρ k : ℕ), n = 2 * ρ + k + 1 → ∀ M M' : GL (Fin n) K,
    (M' : Matrix (Fin n) (Fin n) K)ᵀ * flagGram K n ρ k * (M : Matrix (Fin n) (Fin n) K) = flagGram K n ρ k →
    FlagCond (fun c : K => c = 0) ρ k 1 (M : Matrix (Fin n) (Fin n) K) →
    FlagCond (fun c : K => c = 0) ρ k 0 (M' : Matrix (Fin n) (Fin n) K) → M ∈ unipSym K n ρ k := by
  intro K _ n ρ k hn M M' hrel hM hM'
  subst hn

  have hkey : (M' : Matrix (Fin (2 * ρ + k + 1)) (Fin (2 * ρ + k + 1)) K)ᵀ * flagGram K (2 * ρ + k + 1) ρ k =
      flagGram K (2 * ρ + k + 1) ρ k * ((M⁻¹ : GL (Fin (2 * ρ + k + 1)) K) : Matrix (Fin (2 * ρ + k + 1)) (Fin (2 * ρ + k + 1)) K) := by
    have h := congrArg (· * ((M⁻¹ : GL (Fin (2 * ρ + k + 1)) K) : Matrix (Fin (2 * ρ + k + 1)) (Fin (2 * ρ + k + 1)) K)) hrel
    simp only [Matrix.mul_assoc] at h
    rw [← h, Units.mul_inv, Matrix.mul_one]

  have hN : ∀ p q : Fin (2 * ρ + k + 1), ρ + k < p.val → q.val ≤ p.val →
      ((M⁻¹ : GL (Fin (2 * ρ + k + 1)) K) : Matrix (Fin (2 * ρ + k + 1)) (Fin (2 * ρ + k + 1)) K) p q = (1 : Matrix (Fin (2 * ρ + k + 1)) (Fin (2 * ρ + k + 1)) K) p q := by
    intro p q hp hq
    have hp2 := p.2
    have hq2 := q.2
    have h1 := congrFun (congrFun hkey ⟨dualIdx ρ k p.val, dualIdx_lt' p.2⟩) q
    rw [mul_flagGram_apply, flagGram_mul_apply, transpose_apply] at h1
    have e1 : (⟨dualIdx ρ k (dualIdx ρ k p.val), dualIdx_lt' (dualIdx_lt' p.2)⟩ : Fin (2 * ρ + k + 1)) = p :=
      Fin.ext ((dualIdx_iff' p.2 (dualIdx_lt' p.2)).mpr rfl).symm
    have hs : (if dualIdx ρ k p.val = ρ + k then (-1 : K) else 1) = 1 :=
      if_neg (by unfold dualIdx; split_ifs <;> omega)
    simp only [Fin.val_mk] at h1
    rw [e1, hs, one_mul] at h1
    have hc := hM'.1 ⟨dualIdx ρ k q.val, dualIdx_lt' q.2⟩ ⟨dualIdx ρ k p.val, dualIdx_lt' p.2⟩
      (by simp only [Fin.val_mk]; unfold dualIdx; split_ifs <;> omega)
      (by simp only [Fin.val_mk]; unfold dualIdx; split_ifs <;> omega)
    simp only [Matrix.sub_apply, sub_eq_zero] at hc
    rw [← h1, hc]
    by_cases hpq : p = q
    · subst hpq
      rw [Matrix.one_apply_eq, Matrix.one_apply_eq, hs, one_mul]
    · have hne : (⟨dualIdx ρ k q.val, dualIdx_lt' q.2⟩ : Fin (2 * ρ + k + 1)) ≠ ⟨dualIdx ρ k p.val, dualIdx_lt' p.2⟩ := by
        intro h
        apply hpq
        have h' := congrArg Fin.val h
        simp only [Fin.val_mk] at h'
        apply Fin.ext
        unfold dualIdx at h'
        split_ifs at h' <;> omega
      rw [Matrix.one_apply_ne hne, zero_mul, Matrix.one_apply_ne hpq]

  have hMrow : ∀ t, ∀ p q : Fin (2 * ρ + k + 1), p.val + t = 2 * ρ + k → ρ + k < p.val → q.val ≤ p.val →
      (M : Matrix (Fin (2 * ρ + k + 1)) (Fin (2 * ρ + k + 1)) K) p q = (1 : Matrix (Fin (2 * ρ + k + 1)) (Fin (2 * ρ + k + 1)) K) p q := by
    intro t
    induction t using Nat.strong_induction_on with
    | _ t ih =>
      intro p q ht hp hq
      have hNM : (((M⁻¹ : GL (Fin (2 * ρ + k + 1)) K) : Matrix (Fin (2 * ρ + k + 1)) (Fin (2 * ρ + k + 1)) K) * (M : Matrix (Fin (2 * ρ + k + 1)) (Fin (2 * ρ + k + 1)) K)) p q = (1 : Matrix (Fin (2 * ρ + k + 1)) (Fin (2 * ρ + k + 1)) K) p q := by
        rw [Units.inv_mul]
      rw [mul_apply, Finset.sum_eq_single p] at hNM
      · rw [hN p p hp le_rfl, Matrix.one_apply_eq, one_mul] at hNM
        exact hNM
      · intro l _ hl
        rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hl) with h | h
        · rw [hN p l hp (le_of_lt h), Matrix.one_apply_ne (fun e => hl (e.symm)), zero_mul]
        · have hl2 := l.2
          rw [ih (2 * ρ + k - l.val) (by omega) l q (by omega) (by omega) (by omega),
            Matrix.one_apply_ne (fun e => by rw [e] at h; omega), mul_zero]
      · intro h; exact absurd (Finset.mem_univ _) h
  have hall : ∀ i j : Fin (2 * ρ + k + 1), j.val ≤ i.val → (M : Matrix (Fin (2 * ρ + k + 1)) (Fin (2 * ρ + k + 1)) K) i j = (1 : Matrix (Fin (2 * ρ + k + 1)) (Fin (2 * ρ + k + 1)) K) i j := by
    intro i j hji
    have hi2 := i.2
    by_cases h1 : j.val < ρ
    · have h := hM.1 i j h1 hji
      simp only [Matrix.sub_apply, sub_eq_zero] at h
      exact h
    by_cases h2 : j.val < ρ + k
    · have h := hM.2.2 i j (by omega) h2 hji
      simp only [Matrix.sub_apply, one_mul, sub_eq_zero] at h
      exact h
    by_cases h3 : j.val = ρ + k
    · have h := hM.2.1 i j h3 (by omega)
      simp only [Matrix.sub_apply, sub_eq_zero] at h
      exact h
    · exact hMrow (2 * ρ + k - i.val) i j (by omega) (by omega) hji
  refine ⟨⟨fun i j hij => ?_, fun i => ?_⟩, fun i j h0 h1 h2 => ?_⟩
  · have hij' : j.val < i.val := hij
    rw [hall i j (le_of_lt hij'), Matrix.one_apply_ne (fun e => by rw [e] at hij'; omega)]
  · rw [hall i i le_rfl, Matrix.one_apply_eq]
  · have h := hM.2.1 i j h2 h0
    simp only [Matrix.sub_apply, sub_eq_zero] at h
    rw [h, Matrix.one_apply_ne (fun e => by rw [e] at h1; omega)]

end GlobalTheory.FlagCase
end

