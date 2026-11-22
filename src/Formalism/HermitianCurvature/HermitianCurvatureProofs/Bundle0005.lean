import Formalism.HermitianCurvature.StatementSz
import Formalism.HermitianCurvature.Bundle0001

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.MassRatioFormula
section
namespace Formalism.FourierDecayAlt.P.Sz1

open Finset Formalism.FourierDecayAlt.Sz

lemma half_eq (r : ℕ) : (2 * r + 2) * (2 * r + 2 - 1) / 2 = (r + 1) * (2 * r + 1) := by
  have h : (2 * r + 2) * (2 * r + 2 - 1) = 2 * ((r + 1) * (2 * r + 1)) := by
    have h1 : 2 * r + 2 - 1 = 2 * r + 1 := by omega
    rw [h1]; ring
  rw [h]; simp

lemma two_sum_Ioc (k p : ℕ) : 2 * ∑ M ∈ Ioc k (k + p), M = 2 * (p * k) + p * (p + 1) := by
  induction p with
  | zero => simp
  | succ p ih =>
    rw [← Nat.add_assoc, Finset.sum_Ioc_succ_top (by omega), mul_add, ih]; ring

lemma sum_Ioc_odd (k r : ℕ) :
    ∑ M ∈ Ioc k (k + (2 * r + 1)), M = (2 * r + 1) * k + (r + 1) * (2 * r + 1) := by
  have h := two_sum_Ioc k (2 * r + 1)
  have h2 : 2 * ((2 * r + 1) * k) + (2 * r + 1) * (2 * r + 1 + 1) =
      2 * ((2 * r + 1) * k + (r + 1) * (2 * r + 1)) := by ring
  rw [h2] at h
  exact Nat.eq_of_mul_eq_mul_left (by norm_num) h

lemma glCard_eq (p : ℕ) (q : ℝ) (hq : q ≠ 0) :
    glCard p q = q ^ (p * p) * ∏ i ∈ range p, (1 - (q ^ (i + 1))⁻¹) := by
  unfold glCard
  rw [← Finset.prod_range_reflect (fun i => (1 - (q ^ (i + 1))⁻¹)) p]
  have h : ∀ j ∈ range p, q ^ p - q ^ j = q ^ p * (1 - (q ^ (p - 1 - j + 1))⁻¹) := by
    intro j hj
    have hj' : j < p := Finset.mem_range.mp hj
    have e1 : p - 1 - j + 1 = p - j := by omega
    have e2 : q ^ p = q ^ j * q ^ (p - j) := by rw [← pow_add]; congr 1; omega
    have hne : q ^ (p - j) ≠ 0 := pow_ne_zero _ hq
    rw [e1, e2]; field_simp
  rw [Finset.prod_congr rfl h, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range,
    ← pow_mul]

lemma prod_split (k d : ℕ) (q : ℝ) :
    ∏ i ∈ range (k + d), (1 - (q ^ (i + 1))⁻¹) =
      (∏ i ∈ range k, (1 - (q ^ (i + 1))⁻¹)) * ∏ j ∈ Ioc k (k + d), (1 - (q ^ j)⁻¹) := by
  induction d with
  | zero => simp
  | succ d ih =>
    rw [← Nat.add_assoc, Finset.prod_range_succ, Finset.prod_Ioc_succ_top (by omega), ih, mul_assoc]

lemma prod_ne_zero (k : ℕ) (q : ℝ) (hq : 1 < q) :
    ∏ i ∈ range k, (1 - (q ^ (i + 1))⁻¹) ≠ 0 := by
  refine Finset.prod_ne_zero_iff.mpr ?_
  intro i _
  have h1 : 1 < q ^ (i + 1) := one_lt_pow₀ hq (by omega)
  have h2 : (q ^ (i + 1))⁻¹ < 1 := inv_lt_one_of_one_lt₀ h1
  linarith

lemma glCard_ne_zero (k : ℕ) (q : ℝ) (hq : 1 < q) : glCard k q ≠ 0 := by
  have hq0 : q ≠ 0 := by linarith
  rw [glCard_eq k q hq0]
  exact mul_ne_zero (pow_ne_zero _ hq0) (prod_ne_zero k q hq)

lemma colIdx_ne_zero (k : ℕ) (q : ℝ) (hq : 1 < q) : colIdx k q ≠ 0 := by
  have hq0 : q ≠ 0 := by linarith
  unfold colIdx
  exact div_ne_zero (glCard_ne_zero k q hq) (pow_ne_zero _ hq0)

lemma vol_chain {ι : Type} [Fintype ι] (S : SizeData ι) (hM : S.MassRatios) (d : ℕ)
    (hd : S.k + d ≤ S.n) :
    S.vol (S.k + d) =
      ((S.v / Real.pi) ^ (∑ M ∈ Ioc S.k (S.k + d), M) *
          ((∏ i ∈ Ico S.k (S.k + d), i.factorial : ℕ) : ℝ)) ^ S.f *
        (S.dF ^ (-(1 / 2 : ℝ))) ^ d * (∏ M ∈ Ioc S.k (S.k + d), S.Lv M) * S.vol S.k := by
  induction d with
  | zero => simp
  | succ d ih =>
    have h := hM (S.k + d + 1) (by omega) (by omega)
    rw [Nat.add_sub_cancel, ih (by omega)] at h
    rw [← Nat.add_assoc, h, Finset.sum_Ioc_succ_top (by omega), Finset.prod_Ioc_succ_top (by omega),
      Finset.prod_Ico_succ_top (by omega), pow_add, pow_succ]
    push_cast
    simp only [mul_pow]
    ring

lemma disc_pow (rd : ℝ) (hrd : 0 < rd) (f p : ℕ) :
    ((rd ^ f) ^ (-(1 / 2 : ℝ))) ^ p = (rd ^ (-((p : ℝ) / 2))) ^ f := by
  rw [← Real.rpow_natCast rd f, ← Real.rpow_mul hrd.le, ← Real.rpow_natCast _ p,
    ← Real.rpow_mul hrd.le, ← Real.rpow_natCast _ f, ← Real.rpow_mul hrd.le]
  congr 1; ring

end Formalism.FourierDecayAlt.P.Sz1

namespace Formalism.FourierDecayAlt.P

open Finset Formalism.FourierDecayAlt.Sz Formalism.FourierDecayAlt.P.Sz1

theorem sumRanks : Formalism.FourierDecayAlt.Sz.SumRanks := by
  intro k r m n hm hn
  subst hm
  have hn' : n = k + (2 * r + 1) := by omega
  subst hn'
  have h1 : 2 * r + 2 - 1 = 2 * r + 1 := by omega
  refine ⟨?_, ?_, ?_⟩
  · rw [half_eq, sum_Ioc_odd, h1]
  · rw [Nat.card_Ioc]; omega
  · rw [half_eq, h1]; ring

theorem levelExponent : Formalism.FourierDecayAlt.Sz.LevelExponent := by
  intro k r m n hm hn
  subst hm
  have hn' : n = k + 2 * r + 1 := by omega
  subst hn'
  rw [half_eq]
  unfold dimN
  constructor <;> ring

theorem indexRatio : Formalism.FourierDecayAlt.Sz.IndexRatio := by
  intro k r m n q hm hn hq
  have hq0 : q ≠ 0 := by linarith
  have hexp := (levelExponent k r m n hm hn).2
  have hn' : n = k + (2 * r + 1) := by omega
  have hn'' : k + 2 * r + 1 = n := by omega
  unfold rowIdx colIdx
  rw [hn'', glCard_eq n q hq0, glCard_eq k q hq0]
  have hsplit : ∏ i ∈ range n, (1 - (q ^ (i + 1))⁻¹) =
      (∏ i ∈ range k, (1 - (q ^ (i + 1))⁻¹)) * ∏ j ∈ Ioc k n, (1 - (q ^ j)⁻¹) := by
    rw [hn']; exact prod_split k (2 * r + 1) q
  have hG := prod_ne_zero k q hq
  have hpow : q ^ (n * n) = q ^ (k * k) * q ^ dimN k r * q ^ (k * m + m * (m - 1) / 2) := by
    rw [← pow_add, ← pow_add]; congr 1; rw [← sq, ← sq, hexp]
  rw [hsplit, hpow]
  have a1 : q ^ (k * k) ≠ 0 := pow_ne_zero _ hq0
  have a2 : q ^ dimN k r ≠ 0 := pow_ne_zero _ hq0
  have a3 : q ^ (k * (k - 1) / 2) ≠ 0 := pow_ne_zero _ hq0
  generalize (∏ i ∈ range k, (1 - (q ^ (i + 1))⁻¹)) = G at hG ⊢
  generalize (∏ j ∈ Ioc k n, (1 - (q ^ j)⁻¹)) = H
  field_simp

theorem factorialCancel : Formalism.FourierDecayAlt.Sz.FactorialCancel := by
  intro k n hkn
  unfold sfac
  rw [mul_comm]
  exact Finset.prod_range_mul_prod_Ico _ hkn

theorem volumeChain : Formalism.FourierDecayAlt.Sz.VolumeChain := by
  intro ι _ S hOk hM
  have hn : S.n = S.k + (2 * S.r + 1) := by unfold SizeData.n SizeData.m; omega
  have hm1 : S.m - 1 = 2 * S.r + 1 := by unfold SizeData.m; omega
  have hmR : (S.m : ℝ) - 1 = ((2 * S.r + 1 : ℕ) : ℝ) := by unfold SizeData.m; push_cast; ring
  have hsum := (sumRanks S.k S.r S.m S.n rfl rfl).1
  have h := vol_chain S hM (2 * S.r + 1) (by omega)
  rw [← hn, hsum] at h
  have hrd : 0 < S.rd := by unfold SizeData.rd; linarith [hOk.hv]
  have hdF : S.dF = S.rd ^ S.f := hOk.hdF
  have hka : S.v / Real.pi = S.ka⁻¹ := by unfold SizeData.ka; rw [inv_div]
  rw [h, hdF, disc_pow S.rd hrd, hka, inv_pow, hmR]
  simp only [mul_pow]
  ring

theorem massRatioFormula : Formalism.FourierDecayAlt.Sz.PropA := by
  intro ι _ S hOk hM hC
  have hvc := volumeChain ι S hOk hM
  have hkn : S.k ≤ S.n := by unfold SizeData.n SizeData.m; omega
  have hfac : ((∏ i ∈ Ico S.k S.n, i.factorial : ℕ) : ℝ) * (sfac S.k : ℝ) = (sfac S.n : ℝ) := by
    exact_mod_cast factorialCancel S.k S.n hkn
  have hg1 : (1 : ℝ) < S.g1 := by exact_mod_cast (lt_of_lt_of_le one_lt_two hOk.hg1)
  have hg2 : (1 : ℝ) < S.g2 := by exact_mod_cast (lt_of_lt_of_le one_lt_two hOk.hg2)
  have hT : (1 : ℝ) < S.T := by exact_mod_cast (lt_of_lt_of_le one_lt_two hOk.hT)
  have hi1 := indexRatio S.k S.r S.m S.n S.g1 rfl rfl hg1
  have hi2 := indexRatio S.k S.r S.m S.n S.g2 rfl rfl hg2
  have hc1 := colIdx_ne_zero S.k S.g1 hg1
  have hc2 := colIdx_ne_zero S.k S.g2 hg2
  rw [div_eq_iff hc1] at hi1
  rw [div_eq_iff hc2] at hi2
  have hsk : (sfac S.k : ℝ) ≠ 0 := by
    unfold sfac
    exact_mod_cast (Finset.prod_ne_zero_iff.mpr fun i _ => Nat.factorial_ne_zero i)
  have hTk : (1 : ℝ) < (S.T : ℝ) ^ S.k := one_lt_pow₀ hT (by have := hOk.hk; omega)
  have hTk0 : (S.T : ℝ) ^ S.k ≠ 0 := by linarith
  have hTk1 : (S.T : ℝ) ^ S.k - 1 ≠ 0 := by linarith
  have hVu : ∏ w, S.Vu w ≠ 0 := Finset.prod_ne_zero_iff.mpr fun w _ => (hOk.hVu w).ne'
  have hvol : S.vol S.k ≠ 0 := hOk.hvol.ne'
  have hdim : ∏ w, S.dimPi w = (∏ w, S.Vu w) / (sfac S.k : ℝ) ^ S.f := by
    unfold SizeData.dimPi SizeData.f
    rw [Finset.prod_div_distrib, Finset.prod_const, Finset.card_univ]
  have hprod : ∏ w, (S.TcritPow w / (S.T : ℝ) ^ S.k) =
      ((S.ka ^ ((S.m - 1) * S.k + S.m * (S.m - 1) / 2))⁻¹ * S.rd ^ (-(((S.m : ℝ) - 1) / 2)) *
        S.g ^ (S.k * S.m + S.m * (S.m - 1) / 2) * (sfac S.n : ℝ) / (S.T : ℝ) ^ S.k) ^ S.f *
        (∏ w, S.dsig w) / (∏ w, S.Vu w) := by
    have h : ∀ w ∈ (Finset.univ : Finset ι), S.TcritPow w / (S.T : ℝ) ^ S.k =
        ((S.ka ^ ((S.m - 1) * S.k + S.m * (S.m - 1) / 2))⁻¹ * S.rd ^ (-(((S.m : ℝ) - 1) / 2)) *
        S.g ^ (S.k * S.m + S.m * (S.m - 1) / 2) * (sfac S.n : ℝ) / (S.T : ℝ) ^ S.k) *
        S.dsig w / S.Vu w := by
      intro w _
      unfold SizeData.TcritPow Sz.TcritPow SizeData.VV
      ring
    rw [Finset.prod_congr rfl h, Finset.prod_div_distrib, Finset.prod_mul_distrib,
      Finset.prod_const, Finset.card_univ]
    rfl
  have hT1 : (1 - ((S.T : ℝ) ^ S.k)⁻¹) = ((S.T : ℝ) ^ S.k - 1) / (S.T : ℝ) ^ S.k := by
    field_simp
  rw [hprod, hC, hdim]
  unfold SizeData.Dstar SizeData.Ea SizeData.idxRow SizeData.idxCol SizeData.g
  rw [hvc, hi1, hi2, hT1, ← hfac]
  generalize (S.ka ^ ((S.m - 1) * S.k + S.m * (S.m - 1) / 2))⁻¹ = A
  generalize S.rd ^ (-(((S.m : ℝ) - 1) / 2)) = B
  generalize ((∏ i ∈ Ico S.k S.n, i.factorial : ℕ) : ℝ) = F
  generalize (∏ M ∈ Ioc S.k S.n, S.Lv M) = L
  generalize (∏ j ∈ Ioc S.k S.n, (1 - (((S.g1 : ℝ)) ^ j)⁻¹)) = P1
  generalize (∏ j ∈ Ioc S.k S.n, (1 - (((S.g2 : ℝ)) ^ j)⁻¹)) = P2
  generalize (∏ w, S.dsig w) = D
  generalize (∏ w, S.Vu w) = V at hVu ⊢
  generalize colIdx S.k (S.g1 : ℝ) = c1 at hc1 ⊢
  generalize colIdx S.k (S.g2 : ℝ) = c2 at hc2 ⊢
  generalize (sfac S.k : ℝ) = s at hsk ⊢
  generalize (S.T : ℝ) ^ S.k = t at hTk0 hTk1 ⊢
  generalize S.vol S.k = v0 at hvol ⊢
  generalize S.k * S.m + S.m * (S.m - 1) / 2 = e
  simp only [mul_pow, div_pow]
  field_simp

end Formalism.FourierDecayAlt.P
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.Minors
section
namespace Formalism.FourierDecayAlt.P.Minors

open Matrix

variable {K : Type} [Field K]

def Lead (r : ℕ) (C : Matrix (Fin r) (Fin r) K) : Prop :=
  ∀ (j : ℕ) (hj : j ≤ r), (C.submatrix (Fin.castLE hj) (Fin.castLE hj)).det ≠ 0

def border {r : ℕ} (A : Matrix (Fin r) (Fin r) K) (v u : Fin r → K) (d : K) :
    Matrix (Fin (r + 1)) (Fin (r + 1)) K :=
  Matrix.of fun i j =>
    Fin.lastCases (motive := fun _ => K) (Fin.lastCases (motive := fun _ => K) d u j)
      (fun i' => Fin.lastCases (motive := fun _ => K) (v i') (A i') j) i

@[simp] lemma border_castSucc_castSucc {r : ℕ} (A : Matrix (Fin r) (Fin r) K) (v u : Fin r → K)
    (d : K) (i j : Fin r) : border A v u d i.castSucc j.castSucc = A i j := by
  simp [border]

@[simp] lemma border_castSucc_last {r : ℕ} (A : Matrix (Fin r) (Fin r) K) (v u : Fin r → K)
    (d : K) (i : Fin r) : border A v u d i.castSucc (Fin.last r) = v i := by
  simp [border]

@[simp] lemma border_last_castSucc {r : ℕ} (A : Matrix (Fin r) (Fin r) K) (v u : Fin r → K)
    (d : K) (j : Fin r) : border A v u d (Fin.last r) j.castSucc = u j := by
  simp [border]

@[simp] lemma border_last_last {r : ℕ} (A : Matrix (Fin r) (Fin r) K) (v u : Fin r → K)
    (d : K) : border A v u d (Fin.last r) (Fin.last r) = d := by
  simp [border]

def borderEquiv (r : ℕ) :
    (Matrix (Fin r) (Fin r) K × (Fin r → K) × (Fin r → K) × K) ≃
      Matrix (Fin (r + 1)) (Fin (r + 1)) K where
  toFun x := border x.1 x.2.1 x.2.2.1 x.2.2.2
  invFun C := (C.submatrix Fin.castSucc Fin.castSucc, fun i => C i.castSucc (Fin.last r),
    fun j => C (Fin.last r) j.castSucc, C (Fin.last r) (Fin.last r))
  left_inv x := by
    obtain ⟨A, v, u, d⟩ := x
    ext <;> simp
  right_inv C := by
    ext i j
    refine Fin.lastCases ?_ (fun i => ?_) i <;> refine Fin.lastCases ?_ (fun j => ?_) j <;> simp

lemma det_border {r : ℕ} (A : Matrix (Fin r) (Fin r) K) (v u : Fin r → K) (d : K) :
    (border A v u d).det = (border A v u 0).det + d * A.det := by
  have hsub : ∀ (e : K) (g : Fin r → Fin (r + 1)),
      (border A v u e).submatrix Fin.castSucc g = (border A v u 0).submatrix Fin.castSucc g := by
    intro e g
    ext i k
    simp [border]
  rw [Matrix.det_succ_row _ (Fin.last r), Matrix.det_succ_row _ (Fin.last r),
    Fin.sum_univ_castSucc, Fin.sum_univ_castSucc]
  have hA : ∀ e : K, (border A v u e).submatrix Fin.castSucc Fin.castSucc = A := by
    intro e
    ext i k
    simp
  have hpow : ((-1 : K) ^ ((Fin.last r : ℕ) + (Fin.last r : ℕ))) = 1 := by
    rw [← two_mul, pow_mul]; simp
  simp only [border_last_castSucc, border_last_last, hpow, Fin.succAbove_last, hsub d, hA]
  ring

lemma lead_border_iff {r : ℕ} (A : Matrix (Fin r) (Fin r) K) (v u : Fin r → K) (d : K) :
    Lead (r + 1) (border A v u d) ↔ Lead r A ∧ (border A v u d).det ≠ 0 := by
  have hsmall : ∀ (j : ℕ) (hj : j ≤ r),
      (border A v u d).submatrix (Fin.castLE (hj.trans (Nat.le_succ r)))
        (Fin.castLE (hj.trans (Nat.le_succ r))) = A.submatrix (Fin.castLE hj) (Fin.castLE hj) := by
    intro j hj
    ext i k
    change border A v u d (Fin.castLE hj i).castSucc (Fin.castLE hj k).castSucc = _
    exact border_castSucc_castSucc A v u d _ _
  have hfull : (border A v u d).submatrix (Fin.castLE (le_refl (r + 1)))
      (Fin.castLE (le_refl (r + 1))) = border A v u d := by
    ext i k
    rfl
  constructor
  · intro h
    refine ⟨fun j hj => ?_, ?_⟩
    · have := h j (hj.trans (Nat.le_succ r))
      rwa [hsmall j hj] at this
    · have := h (r + 1) le_rfl
      rwa [hfull] at this
  · rintro ⟨hA, hd⟩ j hj
    rcases Nat.lt_or_ge j (r + 1) with hlt | hge
    · have hj' : j ≤ r := Nat.lt_succ_iff.mp hlt
      have := hsmall j hj'
      rw [this]
      exact hA j hj'
    · obtain rfl : j = r + 1 := le_antisymm hj hge
      rw [hfull]
      exact hd

lemma det_ne_zero_of_lead {r : ℕ} {A : Matrix (Fin r) (Fin r) K} (h : Lead r A) : A.det ≠ 0 := by
  have := h r le_rfl
  have hfull : A.submatrix (Fin.castLE (le_refl r)) (Fin.castLE (le_refl r)) = A := by
    ext i k
    rfl
  rwa [hfull] at this

noncomputable def leadSuccEquiv (r : ℕ) :
    {C : Matrix (Fin (r + 1)) (Fin (r + 1)) K // Lead (r + 1) C} ≃
      {A : Matrix (Fin r) (Fin r) K // Lead r A} × (Fin r → K) × (Fin r → K) × {t : K // t ≠ 0} :=
  ((borderEquiv r).subtypeEquiv (p := fun x => Lead (r + 1) (borderEquiv r x))
      (fun _ => Iff.rfl)).symm.trans
  { toFun := fun x =>
      (⟨x.1.1, ((lead_border_iff _ _ _ _).mp x.2).1⟩, x.1.2.1, x.1.2.2.1,
        ⟨(border x.1.1 x.1.2.1 x.1.2.2.1 x.1.2.2.2).det, ((lead_border_iff _ _ _ _).mp x.2).2⟩)
    invFun := fun y =>
      ⟨(y.1.1, y.2.1, y.2.2.1, (y.2.2.2.1 - (border y.1.1 y.2.1 y.2.2.1 0).det) / y.1.1.det), by
        rw [show Lead (r + 1) (borderEquiv r _) ↔ _ from lead_border_iff _ _ _ _]
        refine ⟨y.1.2, ?_⟩
        rw [det_border, div_mul_cancel₀ _ (det_ne_zero_of_lead y.1.2)]
        simpa using y.2.2.2.2⟩
    left_inv := by
      rintro ⟨⟨A, v, u, d⟩, h⟩
      have hA := det_ne_zero_of_lead ((lead_border_iff A v u d).mp h).1
      simp only [Subtype.mk.injEq, Prod.mk.injEq, true_and]
      rw [det_border]
      field_simp
      ring
    right_inv := by
      rintro ⟨⟨A, hA⟩, v, u, ⟨t, ht⟩⟩
      have hA' := det_ne_zero_of_lead hA
      simp only [Prod.mk.injEq, Subtype.mk.injEq, true_and]
      rw [det_border, div_mul_cancel₀ _ hA']
      ring }

variable [Fintype K]

lemma card_lead_succ (r : ℕ) :
    Nat.card {C : Matrix (Fin (r + 1)) (Fin (r + 1)) K // Lead (r + 1) C} =
      Nat.card {A : Matrix (Fin r) (Fin r) K // Lead r A} *
        (Fintype.card K ^ r * (Fintype.card K ^ r * (Fintype.card K - 1))) := by
  classical
  rw [Nat.card_congr (leadSuccEquiv r), Nat.card_prod, Nat.card_prod, Nat.card_prod,
    Nat.card_fun, Nat.card_congr (unitsEquivNeZero (G₀ := K)).symm, Nat.card_eq_fintype_card (α := Kˣ),
    Fintype.card_units, Nat.card_eq_fintype_card (α := K), Nat.card_eq_fintype_card (α := Fin r),
    Fintype.card_fin]

lemma card_lead_zero : Nat.card {C : Matrix (Fin 0) (Fin 0) K // Lead 0 C} = 1 := by
  classical
  have h : ∀ C : Matrix (Fin 0) (Fin 0) K, Lead 0 C := by
    intro C j hj
    obtain rfl : j = 0 := Nat.le_zero.mp hj
    rw [Matrix.det_isEmpty]
    exact one_ne_zero
  rw [Nat.card_congr (Equiv.subtypeUnivEquiv h)]
  exact Nat.card_unique (α := Fin 0 → Fin 0 → K)

lemma card_lead (r : ℕ) :
    Nat.card {C : Matrix (Fin r) (Fin r) K // Lead r C} =
      Fintype.card K ^ (r ^ 2 - r) * (Fintype.card K - 1) ^ r := by
  induction r with
  | zero => simpa using card_lead_zero
  | succ r ih =>
    rw [card_lead_succ, ih]
    have h1 : (r + 1) ^ 2 - (r + 1) = r ^ 2 - r + r + r := by
      have : r ≤ r ^ 2 := Nat.le_self_pow two_ne_zero r
      have : (r + 1) ^ 2 = r ^ 2 + 2 * r + 1 := by ring
      omega
    rw [h1, pow_add, pow_add, pow_succ]
    ring

end Formalism.FourierDecayAlt.P.Minors

theorem Formalism.FourierDecayAlt.P.leading_minors_count : Formalism.FourierDecayAlt.LeadingMinorsCount := by
  intro K _ _ r
  exact Formalism.FourierDecayAlt.P.Minors.card_lead r
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.ScalingExponentIdentities
section
namespace Formalism.FourierDecayAlt.P

open Matrix

namespace X

theorem scaled_eq {K : Type} [Field K] (n : ℕ) (Z : Matrix (Fin n) (Fin n) K) (κ : K) (l : ℕ)
    (hl : l ≤ n) :
    (Matrix.of (fun a b : Fin n => κ ^ ((a : ℕ) + (b : ℕ)) * Z a b)).submatrix
        (Fin.castLE hl) (Fin.castLE hl) =
      Matrix.diagonal (fun a : Fin l => κ ^ (a : ℕ)) * Z.submatrix (Fin.castLE hl) (Fin.castLE hl) *
        Matrix.diagonal (fun a : Fin l => κ ^ (a : ℕ)) := by
  ext a b
  simp [Matrix.diagonal_mul, Matrix.mul_diagonal, pow_add]
  ring

theorem prod_pow_fin {K : Type} [Field K] (κ : K) (l : ℕ) :
    (∏ a : Fin l, κ ^ (a : ℕ)) = κ ^ (∑ a ∈ Finset.range l, a) := by
  rw [Finset.prod_pow_eq_pow_sum, Fin.sum_univ_eq_sum_range (fun a => a) l]

theorem two_sum (l : ℕ) : 2 * (∑ a ∈ Finset.range l, a) = l * (l - 1) := by
  rw [mul_comm, Finset.sum_range_id_mul_two]

end X

theorem minor_scaling_law : Formalism.FourierDecayAlt.X.MinorScale := by
  intro K _ n Z κ l hl
  rw [X.scaled_eq n Z κ l hl, Matrix.det_mul, Matrix.det_mul, Matrix.det_diagonal,
    X.prod_pow_fin, ← X.two_sum, pow_mul]
  ring

theorem scaling_exponent_identities : Formalism.FourierDecayAlt.X.ScaleExponents :=
  ⟨fun l => by ring, fun i s => by ring⟩

theorem germ_power_identity : Formalism.FourierDecayAlt.X.GermPowers :=
  fun s => ⟨by ring, by ring⟩

theorem slice_power_identity : Formalism.FourierDecayAlt.X.SlicePowers :=
  fun s M => by ring

theorem weight_exponent_identity : Formalism.FourierDecayAlt.X.WeightExponent :=
  fun k r j s => ⟨by ring, by ring, by ring⟩

end Formalism.FourierDecayAlt.P
end

