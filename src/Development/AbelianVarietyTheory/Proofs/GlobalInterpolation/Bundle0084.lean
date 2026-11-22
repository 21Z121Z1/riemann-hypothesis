import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.Bundle0015
import Formalism.SharpRestriction.InertJacobiLevels.Bundle0007
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Bundle0002
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0005
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0074
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0073
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0067
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0069
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0076

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.SubDSharpInDeg
section
open NumberField IsDedekindDomain MvPolynomial Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.IndefiniteRowSideFullHecke.SubstitutionAdjoint
open scoped Matrix

noncomputable section

namespace GlobalTheory.JetDeg

theorem algHom_hom {K σ ρ M N : Type} [CommRing K] [AddCommMonoid M] [AddCommMonoid N] (w : σ → M) (w' : ρ → N)
    (g : M →+ N) (φ : MvPolynomial σ K →ₐ[K] MvPolynomial ρ K)
    (hφ : ∀ v, IsWeightedHomogeneous w' (φ (X v)) (g (w v))) {f : MvPolynomial σ K} {d : M}
    (hf : IsWeightedHomogeneous w f d) : IsWeightedHomogeneous w' (φ f) (g d) := by
  rw [f.as_sum, map_sum]
  refine IsWeightedHomogeneous.sum _ _ _ fun m hm => ?_
  have hd : Finsupp.weight w m = d := hf (mem_support_iff.mp hm)
  rw [monomial_eq, map_mul, algHom_C, algebraMap_eq, Finsupp.prod, map_prod, ← hd, Finsupp.weight_apply,
    Finsupp.sum, map_sum]
  refine IsWeightedHomogeneous.C_mul ?_ _
  refine IsWeightedHomogeneous.prod _ _ _ fun v _ => ?_
  rw [map_pow, map_nsmul]
  exact (hφ v).pow _

variable {K : Type} [Field K] {ι : Type} [DecidableEq ι] {a b : ℕ}

def posW (a : ℕ) (τ : ι) : ι × Fin a × Fin a → ℕ := fun v => if v.1 = τ then 1 else 0

def derW (a b : ℕ) (τ : ι) : (ι × Fin b × Fin b) ⊕ DVar ι a b → ℕ :=
  Sum.elim (fun _ => 0) fun k => if k.1 = τ then 1 else 0

theorem blockEmb_hom (τ τ' : ι) (ν : Fin a → ℕ) {f : MvPolynomial (Fin a × Fin a) K}
    (hf : IsWeightedHomogeneous (Formalism.GradedWeylDivisibility.colW a a) f ν) :
    IsWeightedHomogeneous (posW a τ) (Formalism.GradedWeylDivisibility.blockEmb K τ' f) (if τ' = τ then ∑ i, ν i else 0) := by
  let g : (Fin a → ℕ) →+ ℕ :=
    { toFun := fun x => if τ' = τ then ∑ i, x i else 0
      map_zero' := by simp
      map_add' := by
        intro x y
        split_ifs <;> simp [Finset.sum_add_distrib] }
  refine algHom_hom (Formalism.GradedWeylDivisibility.colW a a) (posW a τ) g _ (fun v => ?_) hf
  have h := isWeightedHomogeneous_X K (posW a τ) (τ', v)
  have e : g (Formalism.GradedWeylDivisibility.colW a a v) = posW a τ (τ', v) := by
    simp [g, Formalism.GradedWeylDivisibility.colW, posW, Pi.single_apply]
  rw [e]
  simpa [Formalism.GradedWeylDivisibility.blockEmb] using h

theorem frDet_hom (τ τ' : ι) :
    IsWeightedHomogeneous (posW a τ) (frDet K a τ') (if τ' = τ then a else 0) := by
  rw [frDet, Matrix.det_apply]
  refine IsWeightedHomogeneous.sum _ _ _ fun σ _ => ?_
  have h : IsWeightedHomogeneous (posW a τ) (∏ i : Fin a, (X (τ', σ i, i) : Pol K ι a))
      (∑ _i : Fin a, if τ' = τ then 1 else 0) :=
    IsWeightedHomogeneous.prod _ _ _ fun i _ => isWeightedHomogeneous_X K (posW a τ) (τ', σ i, i)
  have e : (∑ _i : Fin a, if τ' = τ then 1 else 0) = if τ' = τ then a else 0 := by
    split_ifs <;> simp
  rw [e] at h
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h1 | h1
  · simpa [h1] using h
  · simpa [h1] using h.neg

theorem subD_hom (τ : ι) {P : Pol K ι a} {d : ℕ} (hP : IsWeightedHomogeneous (posW a τ) P d) :
    IsWeightedHomogeneous (derW a b τ) (subD K ι a b P) d := by
  refine algHom_hom (posW a τ) (derW a b τ) (AddMonoidHom.id ℕ) _ (fun v => ?_) hP
  rw [subD, aeval_X]
  split_ifs with h
  · refine IsWeightedHomogeneous.sum _ _ _ fun β _ => ?_
    have := (isWeightedHomogeneous_X K (derW a b τ) (Sum.inl (v.1, β, (⟨v.2.2.1, h⟩ : Fin b)))).mul
      (isWeightedHomogeneous_X K (derW a b τ) (Sum.inr (v.1, β, v.2.1)))
    simpa [derW, posW] using this
  · exact isWeightedHomogeneous_zero _ _ _

variable [Fintype ι]

theorem VV_hom (lam : ι → DomWeight a) (τ : ι) {P : Pol K ι a} (hP : P ∈ Formalism.L2.DIV.VV K lam) :
    IsWeightedHomogeneous (posW a τ) P (∑ i, (lam τ).natW i) := by
  have : Formalism.L2.DIV.VV K lam ≤ weightedHomogeneousSubmodule K (posW a τ) (∑ i, (lam τ).natW i) := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨F, hF, rfl⟩
    have h := IsWeightedHomogeneous.prod Finset.univ (fun τ' => Formalism.GradedWeylDivisibility.blockEmb K τ' (F τ'))
      (fun τ' => if τ' = τ then ∑ i, (lam τ').natW i else 0) (w := posW a τ)
      fun τ' _ => blockEmb_hom τ τ' _ (hF τ').1
    simpa using h
  exact this hP

theorem sharp_hom (n : ι → ℕ) (τ : ι) {P : Pol K ι a} {d : ℕ} (hP : IsWeightedHomogeneous (posW a τ) P d) :
    IsWeightedHomogeneous (posW a τ) (sharp n P) (d + n τ * a) := by
  refine hP.mul ?_
  have h := IsWeightedHomogeneous.prod Finset.univ (fun τ' => frDet K a τ' ^ n τ')
    (fun τ' => n τ' • if τ' = τ then a else 0) (w := posW a τ)
    fun τ' _ => (frDet_hom τ τ').pow _
  simpa using h

theorem weight_derW (τ : ι) (μ : (ι × Fin b × Fin b) ⊕ DVar ι a b →₀ ℕ) :
    Finsupp.weight (derW a b τ) μ = ∑ β : Fin b, ∑ α : Fin a, μ (Sum.inr (τ, β, α)) := by
  rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp), Fintype.sum_sum_type]
  rw [Fintype.sum_prod_type (α₁ := ι) (α₂ := Fin b × Fin a), Finset.sum_eq_single τ]
  · simp [derW, Fintype.sum_prod_type]
  · intro x _ hx
    simp [derW, hx]
  · simp

theorem natW_cast (lam : DomWeight a) (i : Fin a) : (lam.natW i : ℤ) = lam.w i - lam.detShift := by
  have hi := i.2
  have h : lam.detShift ≤ lam.w i := by
    rw [DomWeight.detShift, dif_pos (by omega)]
    exact lam.anti (by rw [Fin.le_def]; simp only; omega)
  rw [DomWeight.natW]
  omega

end GlobalTheory.JetDeg

open GlobalTheory.JetDeg in

theorem GlobalTheory.subD_sharp_inDeg : ∀ (K : Type) [Field K] (ι : Type) [Fintype ι] (a b : ℕ) (hab : a < b) (lam : ι → DomWeight a) (lam' : ι → DomWeight b) (s s' : ι → ℤ) (n : ι → ℕ), WtCompat hab lam lam' s s' n → ∀ P ∈ Formalism.L2.DIV.VV K lam, ∀ μ ∈ (subD K ι a b (sharp n P)).support, InDeg lam s' (Finsupp.comapDomain Sum.inr μ Sum.inr_injective.injOn) := by
  classical
  intro K _ ι _ a b hab lam lam' s s' n hw P hP μ hμ τ
  have h := subD_hom (b := b) τ (sharp_hom n τ (VV_hom lam τ hP)) (mem_support_iff.mp hμ)
  rw [weight_derW] at h
  simp only [Finsupp.comapDomain_apply]
  rw [h]
  push_cast
  have e : ∀ i, (lam τ).w i + s' τ = ((lam τ).natW i : ℤ) + n τ := fun i => by
    rw [natW_cast, hw.2.2 τ]; ring
  simp [e, Finset.sum_add_distrib, mul_comm]

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.SzRowPrimesConductor
section
open Formalism.BasicNotions Formalism.BasicNotions.LevelStarExponents Formalism.MainNotions Formalism.MainNotions.Inhab GlobalTheory.EX NumberField

namespace GlobalTheory.EX

theorem szRow_primes_conductor : SzRow (fun C D L => (L.sc.x ^ (2 * L.Ct + 5) < (D.host.q : ℝ) ∧ L.sc.x ^ (2 * L.Ct + 5) < (D.host.d : ℝ)) ∧ (L.sc.x ^ (L.sc.ez / 6) ≤ Real.log D.host.q) ∧ (|L.logDerivativeAtOne| ≤ L.sc.x ^ L.sc.eps) ∧ ((condE D : ℝ) ^ 36 * (D.R.t : ℝ) ^ 150 ≤ L.sc.b ^ ((1 : ℝ) / 2)) ∧ (Real.log D.host.pde ≤ L.sc.L ∧ Real.log D.host.pde' ≤ L.sc.L)) := by
  intro eps he he' C hC
  have hC8 : 1 ≤ C.P.Cpde := hC.2.2.2.2.2.2.2.2.2.2.2.2.1
  obtain ⟨xh, hh⟩ := hostBounds eps C.P.Cpde he he' hC8
  obtain ⟨xa, ha⟩ := GlobalTheory.log_add_rpow_mul_log_pow_le_rpow 0 (eps / C.P.Cpde / 5) (2 * C.Ct + 5) 1 (1 / 2) 0
    le_rfl (by positivity) (by norm_num)
  obtain ⟨xb, hb⟩ := GlobalTheory.log_add_rpow_mul_log_pow_le_rpow 0 (eps / C.P.Cpde / 30) 0 1 1 0
    le_rfl (by positivity) (by norm_num)
  obtain ⟨xc, hc⟩ := GlobalTheory.log_add_rpow_mul_log_pow_le_rpow (eps / 5) eps 0 222 (1 / 2) 2
    (by positivity) (by linarith) (by norm_num)
  obtain ⟨xd, hd⟩ := GlobalTheory.log_add_rpow_mul_log_pow_le_rpow (eps / 5) eps 0 (2 * C.P.Cpde) 1 2
    (by positivity) (by linarith) (by norm_num)
  refine ⟨0, fun cD _ => ⟨0, fun ch _ => ⟨max (max (max xh xa) (max xb xc)) (max xd (max (Real.exp 1) (Real.exp C.P.Cpde))), ?_⟩⟩⟩
  intro D L hLe hx hV
  simp only [max_le_iff] at hx
  obtain ⟨⟨⟨hxh, hxa⟩, hxb, hxc⟩, hxd, hxe, hxC⟩ := hx
  obtain ⟨q1, q2, d1, -, hN, -, -, -, p1, p2⟩ := hh L.sc D.R D.host hLe hxh hV.ranks hV.host
  have ha := ha _ hxa
  have hb := hb _ hxb
  have hc := hc _ hxc
  have hd := hd _ hxd
  subst hLe
  have hx0 : 0 < L.sc.x := lt_trans one_pos L.sc.one_lt_alt
  have hl1 : 1 ≤ Real.log L.sc.x := (Real.le_log_iff_exp_le hx0).mpr hxe
  have hl2 : 1 ≤ Real.log L.sc.x ^ 2 := one_le_pow₀ hl1
  have hPl : L.sc.x ^ (L.sc.eps / 5) ≤ L.sc.x ^ (L.sc.eps / 5) * Real.log L.sc.x ^ 2 :=
    le_mul_of_one_le_right (Real.rpow_pos_of_pos hx0 _).le hl2
  simp only [Real.rpow_zero, pow_zero, mul_one, one_mul, zero_mul, zero_add] at ha hb hc hd
  have hq0 : (0 : ℝ) < D.host.q := by
    have := D.host.qd_big.1
    exact_mod_cast (by omega : 0 < D.host.q)
  have hd0 : (0 : ℝ) < D.host.d := by
    have := D.host.qd_big.2
    exact_mod_cast (by omega : 0 < D.host.d)
  have hez : L.sc.eps / C.P.Cpde ≤ L.sc.ez := hostBounds_ez hV.host
  have hx1 : 1 ≤ L.sc.x := L.sc.one_lt_alt.le
  have hZ : 0 < L.sc.x ^ (L.sc.ez / 5) := Real.rpow_pos_of_pos hx0 _
  have ha' : L.sc.x ^ (L.sc.eps / C.P.Cpde / 5) ≤ L.sc.x ^ (L.sc.ez / 5) :=
    Real.rpow_le_rpow_of_exponent_le hx1 (by linarith)
  have hb' : 2 ≤ L.sc.x ^ (L.sc.ez / 30) :=
    le_trans (by linarith) (Real.rpow_le_rpow_of_exponent_le hx1
      (show L.sc.eps / C.P.Cpde / 30 ≤ L.sc.ez / 30 by linarith))
  have hq6 : L.sc.x ^ (L.sc.ez / 6) ≤ L.sc.x ^ (L.sc.ez / 5) / 2 := by
    have e : L.sc.x ^ (L.sc.ez / 5) = L.sc.x ^ (L.sc.ez / 6) * L.sc.x ^ (L.sc.ez / 30) := by
      rw [← Real.rpow_add hx0]; congr 1; ring
    have h6 : 0 < L.sc.x ^ (L.sc.ez / 6) := Real.rpow_pos_of_pos hx0 _
    have := mul_le_mul_of_nonneg_left hb' h6.le
    linarith
  have hdl : L.sc.x ^ (L.sc.ez / 5) ≤ L.sc.x ^ (L.sc.ez / 5) * (Real.log L.sc.x / L.sc.J) ^ 2 :=
    le_mul_of_one_le_right hZ.le (one_le_pow₀ (hostBounds_one_le_log_div hV.host hxC))
  have key : ∀ y : ℝ, 0 < y → L.sc.x ^ (L.sc.ez / 5) / 2 ≤ Real.log y →
      L.sc.x ^ (2 * L.Ct + 5) < y := by
    intro y hy h
    rw [hV.Ct_eq, Real.rpow_def_of_pos hx0, ← Real.lt_log_iff_exp_lt hy]
    linarith
  refine ⟨⟨key _ hq0 q1, key _ hd0 (by linarith)⟩, hq6.trans q1, hV.dlog, ?_, ?_, ?_⟩
  · have hn : (1 : ℝ) ≤ D.R.n := by
      exact_mod_cast D.R.ord_pos
    have hk : 2 ≤ D.R.k := by
      have h1 : (1 : ℝ) < L.sc.x ^ (9 / 2 + 10 * L.sc.eps) :=
        Real.one_lt_rpow L.sc.one_lt_alt (by positivity)
      have h2 : (1 : ℝ) < D.R.k := lt_of_lt_of_le h1 hV.ranks.2.2.1.1
      exact_mod_cast h2
    have hr : 1 ≤ D.R.r := by
      unfold Ranks.r; omega
    have ht : D.R.t ≤ D.host.q := by
      have := D.host.qd_big.1
      nlinarith
    have ht' : (D.R.t : ℝ) ≤ Real.exp (L.sc.x ^ (L.sc.eps / 5)) :=
      le_trans (by exact_mod_cast ht) ((Real.log_le_iff_le_exp hq0).mp q2)
    have hE : (condE D : ℝ) ≤ Real.exp (2 * L.sc.x ^ (L.sc.eps / 5) * Real.log L.sc.x ^ 2) := by
      have hpos : (0 : ℝ) < (D.host.QS : ℝ) * D.host.q * D.host.d := by
        have hQ : (0 : ℝ) < D.host.QS := by exact_mod_cast D.host.QS_pos
        positivity
      have := (Real.log_le_iff_le_exp hpos).mp hN
      unfold condE; push_cast; exact this
    calc (condE D : ℝ) ^ 36 * (D.R.t : ℝ) ^ 150
        ≤ Real.exp (2 * L.sc.x ^ (L.sc.eps / 5) * Real.log L.sc.x ^ 2) ^ 36 *
          Real.exp (L.sc.x ^ (L.sc.eps / 5)) ^ 150 := by gcongr
      _ ≤ L.sc.b ^ ((1 : ℝ) / 2) := by
        unfold Scale.b Scale.L
        rw [← Real.exp_nat_mul, ← Real.exp_nat_mul, ← Real.exp_add, ← Real.exp_mul]
        apply Real.exp_le_exp.mpr
        push_cast
        linarith
  · unfold Scale.L; linarith
  · unfold Scale.L; linarith

end GlobalTheory.EX
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.SzRowSizeDel
section
open Formalism.BasicNotions Formalism.BasicNotions.LevelStarExponents Formalism.MainNotions Formalism.MainNotions.Inhab GlobalTheory.EX NumberField

namespace GlobalTheory.EX

theorem szRow_sizeDel : SzRow (fun _ _ L => SizeDel L) := by
  intro eps he he' C hC
  refine ⟨412, fun cD hcD => ⟨0, fun ch _ => ?_⟩⟩
  obtain ⟨CN, x1, h1⟩ := GlobalTheory.topCount_and_lambda_bounds eps he he'
  obtain ⟨x2, h2⟩ := GlobalTheory.scale_poly_comparison eps (cD + 12) 1 he one_pos
  obtain ⟨x3, h3⟩ := GlobalTheory.log_add_rpow_mul_log_pow_le_rpow 0 (eps / 4) cD 1 (1 / 2) 0 le_rfl
    (by positivity) (by norm_num)
  obtain ⟨x4, h4⟩ := GlobalTheory.EX.rank_basic_bounds eps he he'
  have hCp : 1 ≤ C.P.Cpde := hC.2.2.2.2.2.2.2.2.2.2.2.2.1
  obtain ⟨x5, h5⟩ := GlobalTheory.EX.hostBounds eps C.P.Cpde he he' hCp
  have hLa : 1 ≤ C.GK.La := hC.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 _ (by simp [FC.cMid])
  refine ⟨max (max (max x1 x2) (max x3 x4)) (max x5 32), fun D L hε hx hV => ?_⟩
  simp only [max_le_iff] at hx
  obtain ⟨⟨⟨hx1, hx2⟩, hx3, hx4⟩, hx5, hx6⟩ := hx
  have hx1' : 1 < L.sc.x := L.sc.one_lt_alt
  have hx0 : 0 < L.sc.x := by linarith
  have hΛ : 1 ≤ L.LaG := by
    rw [hV.La_eq]
    refine le_trans ?_ ((h1 L.sc hε hx1).2.2 C.GK hLa).1
    exact Real.one_le_rpow hx1'.le L.sc.eps_pos.le
  have hp1 : 1 ≤ L.sc.x ^ cD := Real.one_le_rpow hx1'.le (by linarith)
  have hDel : (D.s.Del : ℝ) = (⌈L.sc.x ^ cD⌉₊ : ℝ) := by
    rw [hV.Del_eq]; simp [Delv]
  have hD2 : (D.s.Del : ℝ) ≤ 2 * L.sc.x ^ cD := by
    rw [hDel]
    have := Nat.ceil_lt_add_one (a := L.sc.x ^ cD) (by positivity)
    linarith
  have hD0 : L.sc.x ^ cD ≤ (D.s.Del : ℝ) := by
    rw [hDel]; exact Nat.le_ceil _
  have hD1 : 1 ≤ (D.s.Del : ℝ) := hp1.trans hD0
  obtain ⟨hf, hm, hr, hkr, -, hL, -, -, -, -, -, -, -, -, hN, -, -⟩ := h4 L.sc D.R hε hx4 hV.ranks
  obtain ⟨-, -, -, -, -, hrd1, -, hrd, -, -⟩ := h5 L.sc D.R D.host hε hx5 hV.ranks hV.host
  have hk0 : (0 : ℝ) < D.R.k := lt_of_lt_of_le (by positivity) hV.ranks.2.2.1.1
  have hk : (D.R.k : ℝ) ≤ L.sc.x ^ (5 : ℕ) := by
    have : (D.R.k : ℝ) ≤ D.R.r := by exact_mod_cast hkr
    rw [← Real.rpow_natCast]; push_cast; linarith
  have hN' : (D.R.N D.R.m : ℝ) ≤ L.sc.x ^ (402 : ℕ) := by
    rw [← Real.rpow_natCast]; push_cast; exact hN
  have hθ : L.sc.x ^ szTh L ≤ L.sc.x := by
    have : L.sc.x ^ szTh L ≤ L.sc.x ^ (1 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hx1'.le (by rw [szTh, hε]; linarith)
    rwa [Real.rpow_one] at this
  have hθ0 : 0 < L.sc.x ^ szTh L := by positivity
  have hn1 : 1 ≤ D.R.n := D.R.ord_pos
  have hn : (D.R.n : ℝ) ≤ L.sc.x ^ (3 : ℝ) := by
    refine le_trans ?_ hf
    have : D.R.n ≤ D.R.f := by simp only [Ranks.f]; omega
    exact_mod_cast this
  obtain ⟨hw, hwb, -⟩ := (h2 L.sc hε hx2).2.2.2.2.2.1 D.R.n hn1 hn
  have hw' : L.sc.x ^ cD * L.sc.x ^ (12 : ℕ) ≤ L.sc.w'' D.R.n := by
    rw [sub_self, Real.rpow_zero, one_mul, Real.rpow_add hx0] at hw
    rw [← Real.rpow_natCast]; push_cast; exact hw
  have h412 : L.sc.x ^ (412 : ℕ) ≤ (D.s.Del : ℝ) := by
    refine le_trans ?_ hD0
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le hx1'.le (by push_cast; exact hcD)
  have key : 16 * L.sc.x * (D.R.k : ℝ) ^ 2 * (D.s.Del : ℝ) ≤ L.sc.w'' D.R.n := by
    calc 16 * L.sc.x * (D.R.k : ℝ) ^ 2 * (D.s.Del : ℝ)
        ≤ 16 * L.sc.x * (L.sc.x ^ (5 : ℕ)) ^ 2 * (2 * L.sc.x ^ cD) := by gcongr
      _ = 32 * (L.sc.x ^ cD * L.sc.x ^ (11 : ℕ)) := by ring
      _ ≤ L.sc.x * (L.sc.x ^ cD * L.sc.x ^ (11 : ℕ)) := by gcongr
      _ = L.sc.x ^ cD * L.sc.x ^ (12 : ℕ) := by ring
      _ ≤ _ := hw'
  have hP : 0 ≤ (D.R.k : ℝ) ^ 2 * (D.s.Del : ℝ) := by positivity
  have hwΛ : L.sc.w'' D.R.n ≤ L.LaG * L.sc.b' := by
    have hb0 : 0 ≤ L.sc.b' := le_trans (le_trans (by positivity) hw') hwb
    exact hwb.trans (le_mul_of_one_le_left hb0 hΛ)
  have hxP : (D.R.k : ℝ) ^ 2 * (D.s.Del : ℝ) ≤ L.sc.x * ((D.R.k : ℝ) ^ 2 * (D.s.Del : ℝ)) :=
    le_mul_of_one_le_left hP hx1'.le
  have hθP : L.sc.x ^ szTh L * ((D.R.k : ℝ) ^ 2 * (D.s.Del : ℝ)) ≤
      L.sc.x * ((D.R.k : ℝ) ^ 2 * (D.s.Del : ℝ)) := mul_le_mul_of_nonneg_right hθ hP
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · calc (D.R.N D.R.m : ℝ) * (D.R.m : ℝ) ^ 10 ≤ L.sc.x ^ (402 : ℕ) * L.sc.x ^ 10 := by gcongr
      _ = L.sc.x ^ (412 : ℕ) := by rw [← pow_add]
      _ ≤ _ := h412
  · calc L.sc.x ^ szTh L * D.R.m * D.R.N D.R.m ≤ L.sc.x * L.sc.x * L.sc.x ^ (402 : ℕ) := by gcongr
      _ = L.sc.x ^ (404 : ℕ) := by ring
      _ ≤ L.sc.x ^ (412 : ℕ) := pow_le_pow_right₀ hx1'.le (by norm_num)
      _ ≤ _ := h412
  · have h := h3 L.sc.x hx3
    simp only [pow_zero, mul_one, Real.rpow_zero] at h
    have h7 : Real.log (D.s.Del : ℝ) ≤ Real.log (2 * L.sc.x ^ cD) := Real.log_le_log (by linarith) hD2
    rw [Real.log_mul (by norm_num) (by positivity), Real.log_rpow hx0] at h7
    have h8 := Real.log_two_lt_d9
    rw [hε]
    linarith
  · rw [L.Sc_eq]
    linarith
  · have hmk : (D.R.m : ℝ) ≤ D.R.k := by
      have := D.R.m_add_three_le_k
      exact_mod_cast (by omega : D.R.m ≤ D.R.k)
    calc L.sc.x ^ szTh L * D.R.m * D.R.k * (D.s.Del : ℝ)
        ≤ L.sc.x ^ szTh L * D.R.k * D.R.k * (D.s.Del : ℝ) := by gcongr
      _ ≤ _ := by linarith
  · rw [le_div_iff₀ hk0, L.Sc_eq]
    linarith
  · linarith
  · have hv : Real.log D.host.v ≤ L.sc.x := by
      refine le_trans ?_ (hrd.trans hL)
      unfold Host.v
      exact Real.log_le_log (by linarith) (by linarith)
    have hk3 : L.sc.x ^ (3 : ℕ) ≤ (D.R.k : ℝ) := by
      refine le_trans ?_ hV.ranks.2.2.1.1
      rw [← Real.rpow_natCast]
      exact Real.rpow_le_rpow_of_exponent_le hx1'.le (by rw [hε]; push_cast; linarith)
    calc L.sc.x ^ szTh L * D.R.m * Real.log D.host.v ≤ L.sc.x ^ szTh L * D.R.m * L.sc.x := by gcongr
      _ ≤ L.sc.x * L.sc.x * L.sc.x := by gcongr
      _ = L.sc.x ^ (3 : ℕ) := by ring
      _ ≤ _ := hk3

end GlobalTheory.EX
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.SzRowSizeGSizeWords
section
open Formalism.BasicNotions Formalism.BasicNotions.LevelStarExponents Formalism.MainNotions Formalism.MainNotions.Inhab GlobalTheory.EX NumberField

namespace GlobalTheory.EX

theorem log_le_of_le_two_mul_pow_eight {x a y k g : ℝ} (hx : 1 < x) (ha : a ≤ 5) (hy : 0 ≤ y) (hk0 : 0 < k)
    (hk : k ≤ 2 * x ^ a) (hg0 : 0 < g) (hg : g ≤ 2 * (k * Real.exp y) ^ 8) :
    Real.log g ≤ 40 * Real.log x + 9 * y + 9 := by
  have hx0 : 0 < x := by linarith
  have hlx : 0 < Real.log x := Real.log_pos hx
  have hl2 : Real.log 2 ≤ 1 := by
    have := Real.log_two_lt_d9
    linarith
  have h1 : Real.log k ≤ Real.log 2 + a * Real.log x := by
    have := Real.log_le_log hk0 hk
    rwa [Real.log_mul (by norm_num) (Real.rpow_pos_of_pos hx0 a).ne', Real.log_rpow hx0] at this
  have h2 : Real.log g ≤ Real.log 2 + 8 * (Real.log k + y) := by
    have := Real.log_le_log hg0 hg
    rwa [Real.log_mul (by norm_num) (by positivity), Real.log_pow,
      Real.log_mul hk0.ne' (Real.exp_pos y).ne', Real.log_exp, Nat.cast_ofNat] at this
  have h3 : a * Real.log x ≤ 5 * Real.log x := mul_le_mul_of_nonneg_right ha hlx.le
  linarith

theorem szRow_sizeG : SzRow (fun _ _ L => SizeG L) := by
  intro eps he he' C _
  obtain ⟨x0, hx0⟩ := GlobalTheory.log_add_rpow_mul_log_pow_le_rpow eps (eps + eps / 100) 40 9 1 0 he.le
    (by linarith) one_pos
  refine ⟨0, fun cD _ => ⟨0, fun ch _ => ⟨x0, ?_⟩⟩⟩
  intro D L hLe hx hV i j
  obtain ⟨-, -, ⟨hk1, hk2⟩, -⟩ := hV.ranks
  obtain ⟨-, -, -, -, hg, -⟩ := hV.host
  have hx1 := L.sc.one_lt_alt
  have hxp : 0 < L.sc.x := by linarith
  have hk0 : (0 : ℝ) < D.R.k := lt_of_lt_of_le (Real.rpow_pos_of_pos hxp _) hk1
  have hb0 : 0 < L.sc.b := Real.exp_pos _
  refine ⟨(hg i).1, (hg i).2.trans (by linarith [(hg j).1]), ?_⟩
  have hg0 : (0 : ℝ) < D.host.g i := lt_of_lt_of_le (by positivity) (hg i).1
  have hL0 : 0 ≤ L.sc.L := (Real.rpow_pos_of_pos hxp _).le
  have h1 := log_le_of_le_two_mul_pow_eight hx1 (by rw [hLe]; linarith) hL0 hk0 hk2 hg0 (hg i).2
  have h2 := hx0 L.sc.x hx
  have h3 : L.sc.x ^ szTh L * L.sc.L = L.sc.x ^ (eps + eps / 100) := by
    simp only [szTh, Scale.L, hLe]
    rw [← Real.rpow_add hxp, add_comm]
  rw [h3]
  simp only [Scale.L, hLe] at h1
  rw [pow_zero, mul_one, one_mul] at h2
  exact h1.trans h2

theorem szRow_sizeG_sizeWords : SzRow (fun _ _ L => SizeG L ∧ SizeWords L) :=
  szRow_and_imp.1 _ _ szRow_sizeG szRow_card_words_le

end GlobalTheory.EX
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ValDetLe
section
open NumberField IsDedekindDomain MvPolynomial Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.IndefiniteRowSideFullHecke.SubstitutionAdjoint
open scoped Matrix

namespace GlobalTheory.DetIndexPf

theorem val_det_le {K : Type} [Field K] [NumberField K] (w : HeightOneSpectrum (𝓞 K)) {r : ℕ}
    (A C : Matrix (Fin r) (Fin r) K)
    (h : localization₂ w.asIdeal (Submodule.span (𝓞 K) (Set.range fun j : Fin r => fun a : Fin r => A a j)) ≤
      localization₂ w.asIdeal (Submodule.span (𝓞 K) (Set.range fun j : Fin r => fun a : Fin r => C a j))) :
    w.valuation K A.det ≤ w.valuation K C.det := by
  have key : ∀ j : Fin r, ∃ s : 𝓞 K, s ∉ w.asIdeal ∧ ∃ c : Fin r → 𝓞 K,
      ∑ k, c k • (fun a : Fin r => C a k) = s • (fun a : Fin r => A a j) := by
    intro j
    have h1 : (fun a : Fin r => A a j) ∈
        localization₂ w.asIdeal (Submodule.span (𝓞 K) (Set.range fun j : Fin r => fun a : Fin r => A a j)) :=
      ⟨1, w.asIdeal.primeCompl.one_mem, by
        rw [one_smul]; exact Submodule.subset_span ⟨j, rfl⟩⟩
    obtain ⟨s, hs, hx⟩ := h h1
    exact ⟨s, hs, (Submodule.mem_span_range_iff_exists_fun _).1 hx⟩
  choose s hs c hc using key
  have e : A * Matrix.diagonal (fun j => algebraMap (𝓞 K) K (s j)) =
      C * (algebraMap (𝓞 K) K).mapMatrix (Matrix.of fun k j => c j k) := by
    ext a j
    have := congrFun (hc j) a
    rw [Matrix.mul_diagonal, Matrix.mul_apply]
    simp only [Finset.sum_apply, Pi.smul_apply, Algebra.smul_def] at this
    rw [mul_comm, ← this]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp [mul_comm]
  have e2 := congrArg (fun M => w.valuation K (Matrix.det M)) e
  simp only [Matrix.det_mul, Matrix.det_diagonal, map_mul, map_prod, ← RingHom.map_det] at e2
  have h1 : ∏ j, w.valuation K (algebraMap (𝓞 K) K (s j)) = 1 :=
    Finset.prod_eq_one fun j _ => (w.valuation_eq_one_iff_notMem).2 (hs j)
  rw [h1, mul_one] at e2
  rw [e2]
  exact mul_le_of_le_one_right' (w.valuation_le_one _)

theorem detIndex : DetIndex := by
  intro K _ _ w r B B' M' i q _ hM hB
  set C : Matrix (Fin r) (Fin r) K :=
    (B : Matrix (Fin r) (Fin r) K) * Matrix.diagonal (fun j => if j = i then q else 1) with hC
  have hd : C.det = q * (B : Matrix (Fin r) (Fin r) K).det := by
    rw [hC, Matrix.det_mul, Matrix.det_diagonal, mul_comm]
    simp
  have hf : (fun j : Fin r => fun α : Fin r =>
      (if j = i then q else 1) * (B : Matrix (Fin r) (Fin r) K) α j) = fun j : Fin r => fun α : Fin r => C α j := by
    funext j α
    rw [hC, Matrix.mul_diagonal, mul_comm]
  rw [hf] at hM
  have he := hB.symm.trans hM
  rw [← hd]
  exact le_antisymm (val_det_le w _ _ he.le) (val_det_le w _ _ he.ge)

end GlobalTheory.DetIndexPf
end

