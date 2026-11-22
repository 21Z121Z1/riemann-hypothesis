import Formalism.LocalToGlobal.Divisibility.RecBridge
import Formalism.LocalRingCardinality.CoeNeZeroOfNotMem
import Mathlib
import Formalism.SharpRestriction.Divisibility.PrimeDegreeVariant
import Formalism.SharpRestriction.Bundle0001
import Formalism.SharpRestriction.Divisibility.SlopeExcess.FamilyStatementOfScaledLemmas
import Formalism.SharpRestriction.Divisibility.HookProducts.Bundle0002
import Formalism.SharpRestriction.Divisibility.HookProducts.LambdaZeroLeFourB

-- bundled from Formalism.SharpRestriction.Divisibility.HookProducts.AbsPhFSubLeOfLe
section
noncomputable section

namespace Formalism.MainNotions.DIV.HookProducts.RBCompl3

open Formalism.BasicNotions

theorem phF_sub_le {y y' : ℝ} (hy : 0 < y) (hy' : 0 < y') :
    phF y - phF y' ≤ (y - y') * Real.log y := by
  have h1 : Real.log (y / y') ≤ y / y' - 1 := Real.log_le_sub_one_of_pos (div_pos hy hy')
  rw [Real.log_div hy.ne' hy'.ne'] at h1
  have h2 : y' * (Real.log y - Real.log y') ≤ y - y' := by
    have h3 := mul_le_mul_of_nonneg_left h1 hy'.le
    have h4 : y' * (y / y' - 1) = y - y' := by
      rw [mul_sub, mul_div_cancel₀ _ hy'.ne', mul_one]
    rw [h4] at h3
    exact h3
  have key : phF y - phF y' - (y - y') * Real.log y = -(y - y' - y' * (Real.log y - Real.log y')) := by
    unfold phF; ring
  linarith

theorem abs_phF_sub_le_of_le {y y' M : ℝ} (hy' : 1 ≤ y') (h : y' ≤ y) (hyM : y ≤ M) :
    |phF y - phF y'| ≤ (y - y') * Real.log M := by
  have hy : 0 < y := by linarith
  have hy'0 : 0 < y' := by linarith
  have hlow : phF y' - phF y ≤ (y' - y) * Real.log y' := phF_sub_le hy'0 hy
  have hneg : (y' - y) * Real.log y' ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg (by linarith) (Real.log_nonneg hy')
  have hup : phF y - phF y' ≤ (y - y') * Real.log y := phF_sub_le hy hy'0
  have hlog : Real.log y ≤ Real.log M := Real.log_le_log hy hyM
  have hup' : (y - y') * Real.log y ≤ (y - y') * Real.log M :=
    mul_le_mul_of_nonneg_left hlog (by linarith)
  rw [abs_of_nonneg (by linarith)]
  linarith

theorem abs_phF_sub_le {y y' M : ℝ} (hy : 1 ≤ y) (hy' : 1 ≤ y') (hyM : y ≤ M) (hy'M : y' ≤ M) :
    |phF y - phF y'| ≤ |y - y'| * Real.log M := by
  rcases le_total y' y with h | h
  · rw [abs_of_nonneg (sub_nonneg.mpr h)]
    exact abs_phF_sub_le_of_le hy' h hyM
  · rw [abs_sub_comm, abs_sub_comm y y', abs_of_nonneg (sub_nonneg.mpr h)]
    exact abs_phF_sub_le_of_le hy h hy'M

theorem nuRow_head' (D : D7) (u : D.what₂.Word) (j : ℕ) (τ : D.what₂.Tau) (r : ℕ) (hk : r < D.R.k) :
    DV.nuRow D u j τ r = (((D.hcW u τ).u ⟨r, hk⟩ : ℚ) : ℝ) + DV.wSz D j τ -
      (((D.R.N (j - 1) : ℝ) + D.R.N j - 1 - 2 * (r : ℝ)) / 2) := by
  unfold DV.nuRow DV.srcPar
  rw [dif_pos hk]

theorem nuRow_eq_of_not_mid (D : D7) (u u' : D.what₂.Word) (j : ℕ) (τ : D.what₂.Tau) (r : ℕ)
    (hr : ¬ (1 ≤ r ∧ r + 1 < D.R.k)) : DV.nuRow D u j τ r = DV.nuRow D u' j τ r := by
  have hs : DV.srcPar D u τ r = DV.srcPar D u' τ r := by
    unfold DV.srcPar
    by_cases hk : r < D.R.k
    · rw [dif_pos hk, dif_pos hk]
      rcases Nat.eq_zero_or_pos r with h0 | h0
      · subst h0
        rw [D.hcW_first u τ hk, D.hcW_first u' τ hk]
      · have hr' : r = D.R.k - 1 := by omega
        have hfin : (⟨r, hk⟩ : Fin D.R.k) = ⟨D.R.k - 1, by omega⟩ := Fin.ext hr'
        rw [hfin, D.hcW_last u τ (by omega), D.hcW_last u' τ (by omega)]
    · rw [dif_neg hk, dif_neg hk, D.hcW_e u τ, D.hcW_e u' τ]
  unfold DV.nuRow
  rw [hs]

theorem abs_nuRow_sub_le (D : D7) (L : SizeData₂ D) (u u' : D.what₂.Word) (j : ℕ) (τ : D.what₂.Tau) (r : ℕ)
    (hr : 1 ≤ r ∧ r + 1 < D.R.k) : |DV.nuRow D u j τ r - DV.nuRow D u' j τ r| ≤ L.Sc := by
  have hk : r < D.R.k := by omega
  rw [nuRow_head' D u j τ r hk, nuRow_head' D u' j τ r hk]
  have h1 := L.cloud_u u τ ⟨r, hk⟩ hr.1 hr.2
  have h2 := L.cloud_u u' τ ⟨r, hk⟩ hr.1 hr.2
  rw [abs_le]
  constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]

theorem nuRow_le (D : D7) (L : SizeData₂ D) (u : D.what₂.Word) (j : ℕ) (τ : D.what₂.Tau) (r : ℕ)
    (hr : 1 ≤ r ∧ r + 1 < D.R.k) : DV.nuRow D u j τ r ≤ L.Sc + DV.wSz D j τ := by
  have hk : r < D.R.k := by omega
  rw [nuRow_head' D u j τ r hk]
  have h1 := L.cloud_u u τ ⟨r, hk⟩ hr.1 hr.2
  have hN1 : r + 1 ≤ D.R.N (j - 1) := le_trans (by omega : r + 1 ≤ D.R.k) (Nat.le_add_right _ _)
  have hN2 : r + 1 ≤ D.R.N j := le_trans (by omega : r + 1 ≤ D.R.k) (Nat.le_add_right _ _)
  have hN1' : (r : ℝ) + 1 ≤ (D.R.N (j - 1) : ℝ) := by exact_mod_cast hN1
  have hN2' : (r : ℝ) + 1 ≤ (D.R.N j : ℝ) := by exact_mod_cast hN2
  have hs : 0 ≤ ((D.R.N (j - 1) : ℝ) + D.R.N j - 1 - 2 * (r : ℝ)) / 2 := by
    apply div_nonneg _ (by norm_num)
    linarith
  linarith [h1.2]

theorem abs_kerPlace_sub_le (D : D7) (L : SizeData₂ D) (u u' : D.what₂.Word) (i : ℕ) (hi : i < D.R.m)
    (τ : D.what₂.Tau) (M : ℝ) (hM1 : 1 ≤ M) (hM : L.Sc + DV.wSz D (i + 1) τ ≤ M) :
    |DV.kerPlace D L u (i + 1) τ - DV.kerPlace D L u' (i + 1) τ| ≤
      (D.R.k : ℝ) * (L.Sc * (Real.log M + |L.logOm|)) := by
  have hSc : 0 ≤ L.Sc := L.Sc_pos.le
  have hlM : 0 ≤ Real.log M := Real.log_nonneg hM1
  set B : ℝ := L.Sc * (Real.log M + |L.logOm|) with hB
  have hB0 : 0 ≤ B := mul_nonneg hSc (add_nonneg hlM (abs_nonneg _))
  unfold DV.kerPlace
  set S := Finset.range (D.R.N (i + 1 - 1)) with hS
  have e : ((∑ r ∈ S, phF (DV.nuRow D u (i + 1) τ r)) - (∑ r ∈ S, DV.nuRow D u (i + 1) τ r) * L.logOm) -
      ((∑ r ∈ S, phF (DV.nuRow D u' (i + 1) τ r)) - (∑ r ∈ S, DV.nuRow D u' (i + 1) τ r) * L.logOm) =
      ∑ r ∈ S, ((phF (DV.nuRow D u (i + 1) τ r) - phF (DV.nuRow D u' (i + 1) τ r)) -
        (DV.nuRow D u (i + 1) τ r - DV.nuRow D u' (i + 1) τ r) * L.logOm) := by
    simp only [Finset.sum_sub_distrib, ← Finset.sum_mul]
    ring
  rw [e]
  have key : ∀ r ∈ S, |(phF (DV.nuRow D u (i + 1) τ r) - phF (DV.nuRow D u' (i + 1) τ r)) -
      (DV.nuRow D u (i + 1) τ r - DV.nuRow D u' (i + 1) τ r) * L.logOm| ≤
      if (1 ≤ r ∧ r + 1 < D.R.k) then B else 0 := by
    intro r hr
    have hrN : r < D.R.N i := by
      rw [hS, Finset.mem_range] at hr
      simpa using hr
    by_cases hmid : 1 ≤ r ∧ r + 1 < D.R.k
    · rw [if_pos hmid]
      obtain ⟨n1, hn1, he1⟩ := nuRow_nat D u i hi τ r hrN
      obtain ⟨n2, hn2, he2⟩ := nuRow_nat D u' i hi τ r hrN
      have hy1 : (1 : ℝ) ≤ DV.nuRow D u (i + 1) τ r := by rw [he1]; exact_mod_cast hn1
      have hy2 : (1 : ℝ) ≤ DV.nuRow D u' (i + 1) τ r := by rw [he2]; exact_mod_cast hn2
      have hu1 := nuRow_le D L u (i + 1) τ r hmid
      have hu2 := nuRow_le D L u' (i + 1) τ r hmid
      have hd := abs_nuRow_sub_le D L u u' (i + 1) τ r hmid
      have hphi := abs_phF_sub_le (M := M) hy1 hy2 (by linarith) (by linarith)
      have hphi' : |phF (DV.nuRow D u (i + 1) τ r) - phF (DV.nuRow D u' (i + 1) τ r)| ≤ L.Sc * Real.log M :=
        le_trans hphi (mul_le_mul_of_nonneg_right hd hlM)
      have hlo : |(DV.nuRow D u (i + 1) τ r - DV.nuRow D u' (i + 1) τ r) * L.logOm| ≤ L.Sc * |L.logOm| := by
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_right hd (abs_nonneg _)
      have hA := abs_le.1 hphi'
      have hC := abs_le.1 hlo
      have hBe : B = L.Sc * Real.log M + L.Sc * |L.logOm| := by rw [hB]; ring
      rw [hBe, abs_le]
      constructor <;> linarith [hA.1, hA.2, hC.1, hC.2]
    · rw [if_neg hmid, nuRow_eq_of_not_mid D u u' (i + 1) τ r hmid]
      simp
  calc |∑ r ∈ S, ((phF (DV.nuRow D u (i + 1) τ r) - phF (DV.nuRow D u' (i + 1) τ r)) -
        (DV.nuRow D u (i + 1) τ r - DV.nuRow D u' (i + 1) τ r) * L.logOm)|
      ≤ ∑ r ∈ S, |(phF (DV.nuRow D u (i + 1) τ r) - phF (DV.nuRow D u' (i + 1) τ r)) -
        (DV.nuRow D u (i + 1) τ r - DV.nuRow D u' (i + 1) τ r) * L.logOm| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ r ∈ S, (if (1 ≤ r ∧ r + 1 < D.R.k) then B else 0) := Finset.sum_le_sum key
    _ = ((S.filter (fun r => 1 ≤ r ∧ r + 1 < D.R.k)).card : ℝ) * B := by
        rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul]
    _ ≤ (D.R.k : ℝ) * B := by
        apply mul_le_mul_of_nonneg_right _ hB0
        have hsub : S.filter (fun r => 1 ≤ r ∧ r + 1 < D.R.k) ⊆ Finset.range D.R.k := by
          intro r hr
          rw [Finset.mem_filter] at hr
          rw [Finset.mem_range]
          omega
        have := Finset.card_le_card hsub
        rw [Finset.card_range] at this
        exact_mod_cast this

end Formalism.MainNotions.DIV.HookProducts.RBCompl3

end
end

-- bundled from Formalism.SharpRestriction.Divisibility.HookProducts.SharpFunctionalBoundFamily
section
open Module NumberField

noncomputable section

namespace Formalism.MainNotions.DIV.HookProducts

open Formalism.BasicNotions Formalism.BasicNotions.DV Formalism.DivisionValues Formalism.L2.Indef Formalism.L2.DIV Formalism.MainNotions

def FunSharpRec : Prop :=
  ∀ (D : D7) (X0 : BaseLevelRowSide D) (Y : DivX D) {Bs : DefBase D.what₂.LL} {Df0 Df1 : DefSide Bs} {Dc : DefCols Df1}
    {Sp : SPer Dc} {N : IndefNum Bs} (P : IndefCoreR Df0 Df1 Dc Sp N)
    (eRR0 : (Fin P.base.D → D.what₂.LL) ≃ₗ[D.what₂.LL] X0.s.RR.V),
    HLatTie X0.s.RR P.base.RR P.base.XE eRR0 →
    (∀ e : D.what₂.LL →+* ℂ, Y.kapR e = P.cols.κ (InfinitePlace.mk e)) →
    ∀ C : ℝ, C * ((D.R.f : ℝ) * D.R.r / (min (D.host.g 0) (D.host.g 1) : ℕ)) ≤ 1 / 3 →
    LemmaT D X0 C →
    D.div.RR.muMax + meanE D (fun e => Real.log (Y.kapR e)) ≤ N.hh + 14 * lam0 D

theorem funSharpRec : FunSharpRec := by
  intro D X0 Y Bs Df0 Df1 Dc Sp N P eRR0 hRR hkap C hδ hT
  have hmu : X0.principalHermitianLattice.muMax = P.base.muMaxRR := by
    unfold Formalism.BasicNotions.BaseLevelRowSide.principalHermitianLattice Formalism.L2.Indef.IndefData.muMaxRR
    exact (Formalism.MainNotions.DIV.HookProducts.FunSharp.muMax_tie X0.s.RR P.base.RR P.base.XE eRR0 hRR.lat hRR.metric).symm
  have hf0 : P.base.muMaxRR ≤ N.hh - meanLog P.base.κ := P.extra.fun0
  have h1 := (hT hδ (N.hh - meanLog P.base.κ) (hmu ▸ hf0)).1
  have hκ : meanE D (fun e => Real.log (Y.kapR e)) = meanLog P.base.κ := by
    rw [P.extra.level.2.1]
    exact meanEmb_eq_meanLog P.cols.κ _ (fun σ => by rw [hkap σ])
  linarith

structure FunDat (D : D7) (X0 : BaseLevelRowSide D) where
  Bs : DefBase D.what₂.LL
  Df0 : DefSide Bs
  Df1 : DefSide Bs
  Dc : DefCols Df1
  Sp : SPer Dc
  Z : IndefScale Bs
  Cp : ℝ
  CHp : ℝ
  P : IndefCoreR Df0 Df1 Dc Sp (Z.num Cp CHp)
  eRR0 : (Fin P.base.D → D.what₂.LL) ≃ₗ[D.what₂.LL] X0.s.RR.V

def FunTies {eps : ℝ} (Fm : FamP eps) (CHf : List ℝ → ℝ) (x : ℝ) (hx : Fm.x1 < x) (i : Fm.Ix x)
    (T : FunDat (Fm.D x i) (Fm.ex x hx i).p0) : Prop :=
  T.Z.x = (Fm.L x i).sc.x ∧ T.Z.b = (Fm.L x i).sc.b ∧ T.CHp ≤ CHf Fm.cOut ∧
    HLatTie (Fm.ex x hx i).p0.s.RR T.P.base.RR T.P.base.XE T.eRR0 ∧
    ∀ e : (Fm.D x i).what₂.LL →+* ℂ, (Fm.X x i).kapR e = T.P.cols.κ (InfinitePlace.mk e)

def sharpFunctionalExponent (CHf : List ℝ → ℝ) : List ℝ → ℝ := fun l => max (CHf l) 1 + 1

def FunSharpFam : Prop :=
  ∀ {eps : ℝ} (Fm : FamP eps) (CHf : List ℝ → ℝ)
    (Pt : Σ' x0 : ℝ, ∀ x (hx : Fm.x1 < x), x0 ≤ x → ∀ i : Fm.Ix x, FunDat (Fm.D x i) (Fm.ex x hx i).p0),
    (∃ x0 : ℝ, ∀ x ≥ x0, ∀ (hx : Fm.x1 < x) (h : Pt.1 ≤ x) (i : Fm.Ix x), FunTies Fm CHf x hx i (Pt.2 x hx h i)) →
    Formalism.MainNotions.PrimeDegreeVariant.SlopeLossFamily Fm →
    ∃ x0 : ℝ, ∀ x ≥ x0, ∀ (_ : Fm.x1 < x) (i : Fm.Ix x),
      (Fm.D x i).div.RR.muMax + meanE (Fm.D x i) (fun e => Real.log ((Fm.X x i).kapR e)) ≤
        (Fm.L x i).sc.x ^ sharpFunctionalExponent CHf Fm.cOut * (Fm.L x i).sc.b

theorem funSharpFam : FunSharpFam := by
  rintro eps Fm CHf Pt ⟨x0, hpt⟩ ⟨C, -, x5, h5⟩
  refine ⟨max (max x0 x5) (max Pt.1 56), fun x hx hx1 i => ?_⟩
  have g0 : x0 ≤ x := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hx
  have g5 : x5 ≤ x := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hx
  have gP : Pt.1 ≤ x := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hx
  have g56 : (56 : ℝ) ≤ x := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hx
  obtain ⟨hZx, hZb, hCH, hRR, hkap⟩ := hpt x g0 hx1 gP i
  obtain ⟨hδ, hT⟩ := h5 x g5 hx1 i
  have hrec := funSharpRec (Fm.D x i) (Fm.ex x hx1 i).p0 (Fm.X x i) (Pt.2 x hx1 gP i).P (Pt.2 x hx1 gP i).eRR0 hRR hkap C hδ hT
  have hhh : ((Pt.2 x hx1 gP i).Z.num (Pt.2 x hx1 gP i).Cp (Pt.2 x hx1 gP i).CHp).hh =
      (Pt.2 x hx1 gP i).Z.x ^ (Pt.2 x hx1 gP i).CHp * (Pt.2 x hx1 gP i).Z.b := rfl
  rw [hhh, hZx, hZb] at hrec
  have hlam := Formalism.MainNotions.DIV.HookProducts.FunSharp.lambda_zero_le_four_b (Fm.L x i) (Fm.sizes x hx1 i)
  have hsc : (Fm.L x i).sc.x = x := Fm.L_x x i hx1
  rw [hsc] at hrec ⊢
  set B := (Fm.L x i).sc.b with hB
  have hB1 : 1 ≤ B := by
    rw [hB]; unfold Scale.b
    exact Real.one_le_exp (by unfold Scale.L; exact Real.rpow_nonneg (by linarith [(Fm.L x i).sc.one_lt_alt]) _)
  set E := max (CHf Fm.cOut) 1 with hE
  have hx1' : (1 : ℝ) ≤ x := by linarith
  have hx0 : (0 : ℝ) < x := by linarith
  have e1 : x ^ (Pt.2 x hx1 gP i).CHp ≤ x ^ E := Real.rpow_le_rpow_of_exponent_le hx1' (hCH.trans (le_max_left _ _))
  have e2 : x ≤ x ^ E := by
    have := Real.rpow_le_rpow_of_exponent_le hx1' (le_max_right (CHf Fm.cOut) 1)
    rwa [Real.rpow_one] at this
  have e3 : x ^ (sharpFunctionalExponent CHf Fm.cOut) = x * x ^ E := by
    unfold sharpFunctionalExponent; rw [← hE, Real.rpow_add hx0, Real.rpow_one, mul_comm]
  rw [e3]
  have hEpos : 0 ≤ x ^ E * B := by positivity
  have t1 : x ^ (Pt.2 x hx1 gP i).CHp * B ≤ x ^ E * B := mul_le_mul_of_nonneg_right e1 (by linarith)
  have t2 : 56 * B ≤ x ^ E * B := by
    have : 56 * B ≤ x * B := mul_le_mul_of_nonneg_right g56 (by linarith)
    have : x * B ≤ x ^ E * B := mul_le_mul_of_nonneg_right e2 (by linarith)
    linarith
  have t3 : 2 * (x ^ E * B) ≤ x * (x ^ E * B) := mul_le_mul_of_nonneg_right (by linarith) hEpos
  nlinarith

theorem sharp_functional_bound_family {eps : ℝ} (Fm : FamP eps) (CHf : List ℝ → ℝ)
    (Pt : Σ' x0 : ℝ, ∀ x (hx : Fm.x1 < x), x0 ≤ x → ∀ i : Fm.Ix x, FunDat (Fm.D x i) (Fm.ex x hx i).p0)
    (hT : ∃ x0 : ℝ, ∀ x ≥ x0, ∀ (hx : Fm.x1 < x) (h : Pt.1 ≤ x) (i : Fm.Ix x), FunTies Fm CHf x hx i (Pt.2 x hx h i))
    (YF : Formalism.MainNotions.PrimeDegreeVariant.ProvF Fm) (hA : Formalism.MainNotions.PrimeDegreeVariant.AdmFB Fm YF) :
    ∃ x0 : ℝ, ∀ x ≥ x0, ∀ (_ : Fm.x1 < x) (i : Fm.Ix x),
      (Fm.D x i).div.RR.muMax + meanE (Fm.D x i) (fun e => Real.log ((Fm.X x i).kapR e)) ≤
        (Fm.L x i).sc.x ^ sharpFunctionalExponent CHf Fm.cOut * (Fm.L x i).sc.b :=
  funSharpFam Fm CHf Pt hT (Formalism.MainNotions.PrimeDegreeVariant.familyLemmaFive_of_large Fm (Formalism.MainNotions.DIV.Proofs.family_statement_of_scaled_lemmas Fm YF hA).2.2)

end Formalism.MainNotions.DIV.HookProducts
end
end

