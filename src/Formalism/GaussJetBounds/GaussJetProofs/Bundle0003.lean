import Formalism.GaussJetBounds.GaussJetProofs.LogarithmWeightComparison
import Formalism.TorsionNormIteration.InverseIntegralClasses.Bundle0002
import Formalism.GaussJetBounds.Bundle0004
import Formalism.GaussJetBounds.GaussJetProofs.SubstitutionWeightBound

-- bundled from Formalism.GaussJetBounds.GaussJetProofs.ConstantCoeffEvenDerivativeEqZero
section
noncomputable section
open scoped BigOperators

universe u

namespace Formalism.DworkPowerSeriesWeights

open Formalism.IncomingBounds MvPowerSeries

theorem asmS_rho_pos {l : ℕ} (hl : l.Prime) : 0 < rho l := by
  unfold rho
  have h2 : (2 : ℝ) ≤ l := by exact_mod_cast hl.two_le
  apply div_pos one_pos
  nlinarith

theorem lemmaSt_of (hG : GenLogWeight.{u, 0}) (hB : LogBridges.{u}) : LemmaSt.{u} := by
  intro K _ _ _ l d _ hl hpi g hg0 hgl x
  have hb := (hB K l d 0 0).1
  exact hG K l hl hpi (V2 d) (fun y => (y.1, y.2 - 2)) g hg0 (fun x => by rw [← hb x]; exact hgl x) x

theorem asmS_integral_sub_one {K : Type u} [NormedField K] {ι : Type} {pi ρ : ℝ} (h0 : 0 < pi)
    (h1 : pi ≤ 1) (hρ : 0 ≤ ρ) {E : MvPowerSeries ι K} (hE : Integral E)
    (hc : constantCoeff E = 1) : WtGe pi (fun _ => ρ) ρ (E - 1) := by
  classical
  intro n
  unfold MonoWtGe
  by_cases hn : n = 0
  · subst hn
    have h00 : coeff 0 (E - 1) = 0 := by
      rw [map_sub, coeff_zero_eq_constantCoeff_apply, hc, coeff_one, if_pos rfl, sub_self]
    rw [h00, norm_zero]
    exact (Real.rpow_pos_of_pos h0 _).le
  · obtain ⟨i, hi⟩ : ∃ i, n i ≠ 0 := by
      by_contra h
      push_neg at h
      exact hn (Finsupp.ext h)
    have hd : ρ ≤ dot n (fun _ => ρ) := by
      unfold dot Finsupp.sum
      have hmem : i ∈ n.support := Finsupp.mem_support_iff.mpr hi
      have h1' : (1 : ℝ) ≤ n i := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hi
      calc ρ ≤ (n i : ℝ) * ρ := by nlinarith
        _ ≤ ∑ x ∈ n.support, (n x : ℝ) * ρ :=
          Finset.single_le_sum (f := fun x => (n x : ℝ) * ρ)
            (fun x _ => mul_nonneg (Nat.cast_nonneg _) hρ) hmem
    have hc1 : coeff n (E - 1) = coeff n E := by
      rw [map_sub, coeff_one, if_neg hn, sub_zero]
    rw [hc1]
    exact (hE n).trans (Real.one_le_rpow_of_pos_of_le_one_of_nonpos h0 h1 (by linarith))

theorem asmS_cc_be {K : Type u} [Field K] {d : ℕ} [NeZero d] {be : MvPowerSeries (ZMod d) K}
    (h : NoLowBidegree be) : constantCoeff be = 0 := by
  by_contra hne
  have := (h 0 (by rwa [coeff_zero_eq_constantCoeff_apply])).1
  simp [degE] at this

theorem asmS_cc_subst {K : Type u} [Field K] {d : ℕ} [NeZero d] {be : MvPowerSeries (ZMod d) K}
    (hbe0 : constantCoeff be = 0) (a : ZMod d → MvPowerSeries (V2 d) K)
    (ha : ∀ s, constantCoeff (a s) = 0) : constantCoeff (subst a be) = 0 := by
  have ha' : HasSubst a := hasSubst_of_constantCoeff_zero ha
  rw [constantCoeff_subst ha']
  apply finsum_eq_zero_of_forall_eq_zero
  intro n
  by_cases hn : n = 0
  · subst hn
    rw [coeff_zero_eq_constantCoeff_apply, hbe0, zero_smul]
  · obtain ⟨s, hs⟩ : ∃ s, n s ≠ 0 := by
      by_contra h
      push_neg at h
      exact hn (Finsupp.ext h)
    have hp : constantCoeff (n.prod fun s e => a s ^ e) = 0 := by
      simp only [Finsupp.prod, map_prod]
      apply Finset.prod_eq_zero (Finsupp.mem_support_iff.mpr hs)
      rw [map_pow, ha s, zero_pow hs]
    rw [hp, smul_zero]

theorem constantCoeff_evenDerivative_eq_zero {K : Type u} [Field K] {d : ℕ} [NeZero d] {be : MvPowerSeries (ZMod d) K}
    (hbe0 : constantCoeff be = 0) : constantCoeff (de1 be) = 0 := by
  have c0 : constantCoeff (subst (s0 (K := K) (d := d)) be) = 0 :=
    asmS_cc_subst hbe0 _ (fun s => by simp [s0])
  have c1 : constantCoeff (subst (s1 (K := K) (d := d)) be) = 0 :=
    asmS_cc_subst hbe0 _ (fun s => by simp only [s1]; split_ifs <;> simp)
  have c2 : constantCoeff (subst (s2 (K := K) (d := d)) be) = 0 :=
    asmS_cc_subst hbe0 _ (fun s => by simp only [s2]; split_ifs <;> simp)
  simp only [de1, map_sub, c0, c1, c2, sub_zero]

theorem constantCoeff_oddDerivative_eq_zero {K : Type u} [Field K] {d : ℕ} [NeZero d] {be : MvPowerSeries (ZMod d) K}
    (hbe0 : constantCoeff be = 0) : constantCoeff (de2 be) = 0 := by
  have c0 : constantCoeff (subst (s0 (K := K) (d := d)) be) = 0 :=
    asmS_cc_subst hbe0 _ (fun s => by simp [s0])
  have c1 : constantCoeff (subst (s1' (K := K) (d := d)) be) = 0 :=
    asmS_cc_subst hbe0 _ (fun s => by simp only [s1']; split_ifs <;> simp)
  have c2 : constantCoeff (subst (s2' (K := K) (d := d)) be) = 0 :=
    asmS_cc_subst hbe0 _ (fun s => by simp only [s2']; split_ifs <;> simp)
  simp only [de2, map_sub, c0, c1, c2, sub_zero]

theorem asmS_diff (hGW : GenLogWeight.{u, 0}) (hGI : GenLogInverse.{u, 0}) (hB : LogBridges.{u})
    (hSW : SubstWt.{u, 0, 0}) (hQ : Quant.{u}) (hLS : LogStep.{u, 0})
    {K : Type u} [NormedField K] [IsUltrametricDist K] [CharZero K] {l d : ℕ} [NeZero d]
    (hl : l.Prime) (hd : 2 ≤ d) (hde : Even d) (hpi : ‖(l : K)‖ < 1)
    {K0 : Subfield K} (hK0 : Unram l K0) (D : MvPowerSeries (V2 d) K)
    (hD0 : constantCoeff D = 0) (hK : ∀ n, coeff n (mvExp D) ∈ K0)
    (hcong : ∀ n : V2 d →₀ ℕ, coeff n (mvExp D) ≠ 0 →
      ((l ^ d - 1 : ℕ) : ℤ) ∣ ∑ x ∈ n.support, (n x : ℤ) * lw l x.2)
    (hEi : Integral (subst (letterLog (K := K) l) (mvExp D)))
    (hEc : constantCoeff (subst (letterLog (K := K) l) (mvExp D)) = 1) :
    WtGe ‖(l : K)‖ (fun _ => rho l) (1 / ((l : ℝ) - 1)) D := by
  have hl0 : (l : K) ≠ 0 := Nat.cast_ne_zero.mpr hl.ne_zero
  have hpi0 : 0 < ‖(l : K)‖ := norm_pos_iff.mpr hl0
  have hρ : 0 ≤ rho l := (asmS_rho_pos hl).le
  have hLL : ∀ x : V2 d, letterLog (K := K) l x = genLog l (fun y : V2 d => (y.1, y.2 - 2)) x :=
    (hB K l d 0 0).1

  obtain ⟨g, hg0, hgl, -⟩ := hGI K l hl (V2 d) (fun y : V2 d => (y.1, y.2 - 2))
  have hgl' : ∀ x, subst g (letterLog (K := K) l x) = X x := fun x => by rw [hLL x]; exact hgl x
  have hgw : ∀ x, WtGe ‖(l : K)‖ (fun _ => rho l) (rho l) (g x) :=
    lemmaSt_of hGW hB K l d hl hpi g hg0 hgl'
  have hE1 := asmS_integral_sub_one hpi0 hpi.le hρ hEi hEc
  have hW := hSW K ‖(l : K)‖ hpi0 hpi (V2 d) (V2 d) g (fun _ => rho l) (fun _ => rho l) (rho l) _
    hg0 hgw hE1

  have hLL0 : ∀ x, constantCoeff (letterLog (K := K) l x) = 0 := fun x => by
    rw [← coeff_zero_eq_constantCoeff_apply]
    show letterLog (K := K) l x 0 = 0
    unfold letterLog
    refine Finset.sum_eq_zero fun e _ => if_neg ?_
    intro h
    have h' := congrArg (fun f : V2 d →₀ ℕ => f (x.1, x.2 - 2 * (e : ZMod d))) h
    simp only [Finsupp.coe_zero, Pi.zero_apply, Finsupp.single_eq_same] at h'
    exact pow_ne_zero _ (pow_ne_zero _ hl.ne_zero) h'.symm
  have hLa : HasSubst (letterLog (K := K) l : V2 d → MvPowerSeries (V2 d) K) :=
    hasSubst_of_constantCoeff_zero hLL0
  have hga : HasSubst g := hasSubst_of_constantCoeff_zero hg0
  have hcomp : subst g (subst (letterLog (K := K) l) (mvExp D)) = mvExp D := by
    rw [subst_comp_subst_apply hLa hga, show (fun s => subst g (letterLog (K := K) l s)) = X from
      funext hgl', subst_self]
    rfl
  have hsub1 : subst g (subst (letterLog (K := K) l) (mvExp D) - 1) = mvExp D - 1 := by
    rw [← coe_substAlgHom hga, map_sub, map_one, coe_substAlgHom, hcomp]
  rw [hsub1] at hW

  have hQ' : WtGe ‖(l : K)‖ (fun _ => rho l) (1 / ((l : ℝ) - 1)) (mvExp D - 1) := by
    intro n
    by_cases hz : coeff n (mvExp D - 1) = 0
    · unfold MonoWtGe
      rw [hz, norm_zero]
      exact (Real.rpow_pos_of_pos hpi0 _).le
    have hmem : coeff n (mvExp D - 1) ∈ K0 := by
      rw [map_sub, coeff_one]
      split_ifs
      · exact K0.sub_mem (hK n) K0.one_mem
      · exact K0.sub_mem (hK n) K0.zero_mem
    have hdiv : ((l ^ d - 1 : ℕ) : ℤ) ∣ ∑ x ∈ n.support, (n x : ℤ) * lw l x.2 := by
      by_cases hn : n = 0
      · subst hn
        simp
      · apply hcong
        intro h0
        apply hz
        rw [map_sub, coeff_one, if_neg hn, h0, sub_zero]
    exact hQ K l d hl hd hde hpi hpi0 K0 hK0 _ hmem n hdiv (hW n)
  exact hLS K l hl hpi (V2 d) _ D hD0 hQ'

theorem lemmaS_of (hGW : GenLogWeight.{u, 0}) (hGI : GenLogInverse.{u, 0}) (hB : LogBridges.{u})
    (hSW : SubstWt.{u, 0, 0}) (hX : ExpDeInv.{u}) (hQ : Quant.{u}) (hLS : LogStep.{u, 0})
    (hBE : BinomExtract.{u}) : LemmaS.{u} := by
  intro K _ _ _ l d _ hl hlo hd hde hpi K0 hK0 ζ hζ be hBh
  obtain ⟨hK, htor, hlow, ⟨hEi1, hEc1⟩, ⟨hEi2, hEc2⟩⟩ := hBh
  have hbe0 := asmS_cc_be hlow
  have hX' := hX K l d hl hd hde K0 ζ hζ be hK htor hbe0
  obtain ⟨hK1, hc1⟩ := hX' (de1 be) (by simp)
  obtain ⟨hK2, hc2⟩ := hX' (de2 be) (by simp)
  have w1 := asmS_diff hGW hGI hB hSW hQ hLS hl hd hde hpi hK0 (de1 be) (constantCoeff_evenDerivative_eq_zero hbe0) hK1 hc1
    hEi1 hEc1
  have w2 := asmS_diff hGW hGI hB hSW hQ hLS hl hd hde hpi hK0 (de2 be) (constantCoeff_oddDerivative_eq_zero hbe0) hK2 hc2
    hEi2 hEc2
  exact hBE K l d hl hlo hd hde hpi ζ hζ be htor hlow w1 w2

end Formalism.DworkPowerSeriesWeights
end
end

-- bundled from Formalism.GaussJetBounds.GaussJetProofs.LogStep
section
noncomputable section
open scoped BigOperators

universe u v

namespace Formalism.DworkPowerSeriesWeights

open MvPowerSeries
open Formalism.FG.SolveVAux (Low low_mono low_add low_mul low_pow low_one_iff)

theorem padicValNat_factorial_le_sub_one_div {l : ℕ} (hl : l.Prime) {k : ℕ} (hk : k ≠ 0) :
    (padicValNat l k.factorial : ℝ) ≤ ((k : ℝ) - 1) * (1 / ((l : ℝ) - 1)) := by
  have := Fact.mk hl
  have h := sub_one_mul_padicValNat_factorial_lt_of_ne_zero l hk
  have hl2 := hl.two_le
  have h1 : (l - 1) * padicValNat l k.factorial ≤ k - 1 := by omega
  have h2 : (((l - 1) * padicValNat l k.factorial : ℕ) : ℝ) ≤ ((k - 1 : ℕ) : ℝ) := by
    exact_mod_cast h1
  rw [Nat.cast_mul, Nat.cast_sub (by omega : 1 ≤ l), Nat.cast_sub (Nat.one_le_iff_ne_zero.2 hk),
    Nat.cast_one] at h2
  have hpos : (0 : ℝ) < (l : ℝ) - 1 := by
    have : (2 : ℝ) ≤ l := by exact_mod_cast hl2
    linarith
  rw [mul_one_div, le_div_iff₀ hpos, mul_comm]
  exact h2

theorem norm_coeff_exp {K : Type u} [NormedField K] [IsUltrametricDist K] [CharZero K] {l : ℕ}
    (hl : l.Prime) (hπ : ‖(l : K)‖ < 1) (k : ℕ) :
    ‖PowerSeries.coeff k (PowerSeries.exp K)‖ = (‖(l : K)‖ ^ padicValNat l k.factorial)⁻¹ := by
  rw [PowerSeries.coeff_exp, map_div₀, map_one, map_natCast, norm_div, norm_one, one_div,
    Formalism.LT.ExpP.norm_natCast_eq hl hπ (Nat.factorial_ne_zero k)]

theorem logarithm_weight_induction : LogStep.{u, v} := by
  intro K _ _ _ l hl hπ ι r D hD0 hE
  classical
  have hπ0 : 0 < ‖(l : K)‖ := norm_pos_iff.2 (Nat.cast_ne_zero.2 hl.ne_zero)
  have hπ1 : ‖(l : K)‖ ≤ 1 := hπ.le
  have hD1 : Low 1 D := (low_one_iff _).2 hD0
  have hs : PowerSeries.HasSubst D := PowerSeries.HasSubst.of_constantCoeff_zero hD0
  suffices H : ∀ N, ∀ n : ι →₀ ℕ, n.degree = N →
      MonoWtGe ‖(l : K)‖ r (1 / ((l : ℝ) - 1)) n (coeff n D) from fun n => H _ n rfl
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
  intro n hn
  by_cases hn0 : n = 0
  · subst hn0
    rw [monoWtGe_iff, coeff_zero_eq_constantCoeff_apply, hD0, norm_zero]
    exact Real.rpow_nonneg hπ0.le _
  have hTw : WtGe ‖(l : K)‖ r (1 / ((l : ℝ) - 1)) (truncBelow N D) := by
    intro m
    rw [monoWtGe_iff, coeff_truncBelow]
    split_ifs with hm
    · exact ih _ hm m rfl
    · simpa using Real.rpow_nonneg hπ0.le _
  have hlow : Low N (D - truncBelow N D) := by
    intro m hm
    rw [map_sub, coeff_truncBelow, if_pos hm, sub_self]
  have hT1 : Low 1 (truncBelow N D) := by
    intro m hm
    rw [coeff_truncBelow]
    split_ifs
    · exact hD1 m hm
    · rfl
  have hpow : ∀ k, Low (N + k) (D ^ (k + 1) - truncBelow N D ^ (k + 1)) := by
    intro k
    induction k with
    | zero => simpa using hlow
    | succ k ihk =>
      have e : D ^ (k + 1 + 1) - truncBelow N D ^ (k + 1 + 1) =
          (D ^ (k + 1) - truncBelow N D ^ (k + 1)) * D +
            truncBelow N D ^ (k + 1) * (D - truncBelow N D) := by ring
      rw [e]
      exact low_add (low_mono (le_of_eq (by omega)) (low_mul ihk hD1))
        (low_mono (le_of_eq (by omega)) (low_mul (low_pow hT1 (k + 1)) hlow))

  set a : ℕ → K := fun k => PowerSeries.coeff k (PowerSeries.exp K) • coeff n (D ^ k) with ha
  have hafin : (Function.support a).Finite := PowerSeries.coeff_subst_finite hs _ n
  set b : ℕ → K := fun k => if k = 1 then 0 else a k with hb
  set c : ℕ → K := fun k => if k = 1 then a 1 else 0 with hc
  have hbfin : (Function.support b).Finite :=
    hafin.subset fun k hk => by
      simp only [Function.mem_support, hb] at hk ⊢
      split_ifs at hk with h
      · exact absurd rfl hk
      · exact hk
  have hcfin : (Function.support c).Finite :=
    (Set.finite_singleton 1).subset fun k hk => by
      simp only [Function.mem_support, hc] at hk
      split_ifs at hk with h
      · exact h
      · exact absurd rfl hk
  have habc : a = fun k => b k + c k := by
    funext k
    simp only [hb, hc]
    split_ifs with h
    · subst h; simp
    · simp
  have ha1 : a 1 = coeff n D := by
    simp [ha, PowerSeries.coeff_exp]
  have hsum : coeff n (mvExp D) = (∑ᶠ k, b k) + coeff n D := by
    unfold mvExp
    rw [PowerSeries.coeff_subst hs]
    change ∑ᶠ k, a k = _
    rw [habc, finsum_add_distrib hbfin hcfin, finsum_eq_single c 1 (fun k hk => if_neg hk)]
    simp only [hc, if_pos rfl, ha1]
  have hEq : coeff n D = coeff n (mvExp D - 1) + -(∑ᶠ k, b k) := by
    rw [map_sub, coeff_one, if_neg hn0, sub_zero, hsum]
    ring
  rw [monoWtGe_iff, hEq]
  refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (hE n) ?_)
  rw [norm_neg]
  refine norm_finsum_le_of (Real.rpow_nonneg hπ0.le _) fun k => ?_
  simp only [hb]
  split_ifs with hk1
  · simpa using Real.rpow_nonneg hπ0.le _
  rcases Nat.lt_or_ge k 2 with hk2 | hk2
  · have hk0 : k = 0 := by omega
    subst hk0
    simp only [ha, pow_zero, coeff_one, if_neg hn0, smul_zero, norm_zero]
    exact Real.rpow_nonneg hπ0.le _

  have hce : coeff n (D ^ k) = coeff n (truncBelow N D ^ k) := by
    have := hpow (k - 1) n (by omega)
    rw [Nat.sub_add_cancel (by omega), map_sub, sub_eq_zero] at this
    exact this
  have hbd := wtGe_pow hπ0 hTw k n
  rw [monoWtGe_iff] at hbd
  have hv := padicValNat_factorial_le_sub_one_div hl (k := k) (by omega)
  simp only [ha]
  rw [smul_eq_mul, norm_mul, norm_coeff_exp hl hπ, hce]
  set v := padicValNat l k.factorial
  calc (‖(l : K)‖ ^ v)⁻¹ * ‖coeff n (truncBelow N D ^ k)‖
      ≤ (‖(l : K)‖ ^ v)⁻¹ * ‖(l : K)‖ ^ ((k : ℝ) * (1 / ((l : ℝ) - 1)) - dot n r) :=
        mul_le_mul_of_nonneg_left hbd (inv_nonneg.2 (pow_nonneg hπ0.le _))
    _ = ‖(l : K)‖ ^ ((k : ℝ) * (1 / ((l : ℝ) - 1)) - dot n r - (v : ℝ)) := by
        rw [Real.rpow_sub hπ0 _ (v : ℝ), Real.rpow_natCast]
        ring
    _ ≤ ‖(l : K)‖ ^ (1 / ((l : ℝ) - 1) - dot n r) := by
        apply Real.rpow_le_rpow_of_exponent_ge hπ0 hπ1
        nlinarith

end Formalism.DworkPowerSeriesWeights
end
end

-- bundled from Formalism.GaussJetBounds.GaussJetProofs.MfactEqProdUniv
section
noncomputable section
open scoped BigOperators

universe u

namespace Formalism.DworkPowerSeriesWeights

section PairJetAux

lemma mfact_eq_prod_univ {σ : Type} [Fintype σ] (κ : σ →₀ ℕ) :
    mfact κ = ∏ x, (κ x).factorial := by
  unfold mfact
  exact Finsupp.prod_fintype _ _ (fun _ => rfl)

lemma mfact_mul_dvd {σ : Type} [Fintype σ] (μ ν : σ →₀ ℕ) :
    mfact μ * mfact ν ∣ mfact (μ + ν) := by
  rw [mfact_eq_prod_univ, mfact_eq_prod_univ, mfact_eq_prod_univ, ← Finset.prod_mul_distrib]
  exact Finset.prod_dvd_prod_of_dvd _ _ fun x _ =>
    Nat.factorial_mul_factorial_dvd_factorial_add _ _

def pairExp {ι : Type} [Fintype ι] (n : ι → ℕ) : (Bool × ι) →₀ ℕ :=
  ∑ i, n i • (Finsupp.single (false, i) 1 + Finsupp.single (true, i) 1)

lemma pairExp_apply {ι : Type} [Fintype ι] (n : ι → ℕ) (b : Bool) (i : ι) :
    pairExp n (b, i) = n i := by
  classical
  unfold pairExp
  rw [Finsupp.finsetSum_apply]
  rw [Finset.sum_eq_single i]
  · cases b <;> simp
  · intro j _ hj
    cases b <;> simp [hj]
  · intro h; exact absurd (Finset.mem_univ i) h

lemma mfact_pairExp {ι : Type} [Fintype ι] (n : ι → ℕ) :
    mfact (pairExp n) = (∏ i, (n i).factorial) * ∏ i, (n i).factorial := by
  classical
  rw [mfact_eq_prod_univ, Fintype.prod_prod_type, Fintype.prod_bool]
  simp only [pairExp_apply]

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CharZero K]

lemma quad_pow {ι : Type} [Fintype ι] [DecidableEq ι] (u : ι → K) (k : ℕ) :
    (∑ i, MvPowerSeries.C (u i) * MvPowerSeries.X (false, i) * MvPowerSeries.X (true, i) :
      MvPowerSeries (Bool × ι) K) ^ k =
    ∑ n ∈ Finset.piAntidiag Finset.univ k, (Nat.multinomial Finset.univ n : MvPowerSeries (Bool × ι) K) *
      MvPowerSeries.monomial (pairExp n) (∏ i, u i ^ n i) := by
  classical
  rw [Finset.sum_pow_eq_sum_piAntidiag]
  refine Finset.sum_congr rfl fun n _ => ?_
  congr 1
  unfold pairExp
  rw [← MvPowerSeries.prod_monomial]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [← MvPowerSeries.monomial_pow]
  congr 1
  rw [MvPowerSeries.X_def, MvPowerSeries.X_def, ← MvPowerSeries.monomial_zero_eq_C_apply,
    MvPowerSeries.monomial_mul_monomial, MvPowerSeries.monomial_mul_monomial]
  simp

lemma exp_jet (r : ℝ) (hr : 1 ≤ r) (ι : Type) [Fintype ι] (S : K) (u : ι → K) (hS : ‖S‖ ≤ r)
    (hu : ∀ i, ‖u i‖ ≤ 1) (κ : (Bool × ι) →₀ ℕ) :
    ‖((mfact κ : ℕ) : K) * MvPowerSeries.coeff κ
        (mvExp ((-S) • ∑ i, MvPowerSeries.C (u i) * MvPowerSeries.X (false, i) *
          MvPowerSeries.X (true, i)))‖ ≤ r ^ (∑ i, min (κ (false, i)) (κ (true, i))) := by
  classical
  have hr0 : (0 : ℝ) ≤ r := by linarith
  have hQ0 : MvPowerSeries.constantCoeff ((-S) • ∑ i, MvPowerSeries.C (u i) *
      MvPowerSeries.X (false, i) * MvPowerSeries.X (true, i) : MvPowerSeries (Bool × ι) K) = 0 := by
    simp
  have hs := PowerSeries.HasSubst.of_constantCoeff_zero hQ0
  unfold mvExp
  rw [PowerSeries.coeff_subst hs, mul_finsum]
  refine norm_finsum_le_of (pow_nonneg hr0 _) fun k => ?_
  rw [smul_pow, quad_pow, PowerSeries.coeff_exp, Finset.smul_sum, map_sum, Finset.smul_sum,
    Finset.mul_sum]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (pow_nonneg hr0 _) fun n hn => ?_
  rw [Finset.mem_piAntidiag] at hn
  have hk : ∑ i, n i = k := hn.1
  rw [← map_natCast (MvPowerSeries.C (σ := Bool × ι) (R := K)), ← MvPowerSeries.smul_eq_C_mul,
    map_smul, map_smul, MvPowerSeries.coeff_monomial]
  by_cases hκ : κ = pairExp n
  · rw [if_pos hκ]
    have hspec := Nat.multinomial_spec Finset.univ n
    rw [hk] at hspec
    have hk0 : ((k.factorial : ℕ) : K) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero k)
    have hval : ((mfact κ : ℕ) : K) * ((algebraMap ℚ K) (1 / (k.factorial : ℚ)) •
        ((-S) ^ k • ((Nat.multinomial Finset.univ n : ℕ) : K) • ∏ i, u i ^ n i)) =
        ((∏ i, (n i).factorial : ℕ) : K) * ((-S) ^ k * ∏ i, u i ^ n i) := by
      rw [hκ, mfact_pairExp, map_div₀, map_one, map_natCast, ← hspec]
      rw [← hspec] at hk0
      simp only [smul_eq_mul]
      push_cast at hk0 ⊢
      have hP := left_ne_zero_of_mul hk0
      have hM := right_ne_zero_of_mul hk0
      field_simp
    rw [hval, norm_mul, norm_mul, norm_pow, norm_neg, norm_prod]
    have h1 : ‖((∏ i, (n i).factorial : ℕ) : K)‖ ≤ 1 := IsUltrametricDist.norm_natCast_le_one K _
    have h2 : ∏ i, ‖u i ^ n i‖ ≤ 1 := Finset.prod_le_one (fun _ _ => norm_nonneg _) fun i _ => by
      rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) (hu i)
    have h3 : ‖S‖ ^ k ≤ r ^ k := pow_le_pow_left₀ (norm_nonneg _) hS k
    have h4 : ∑ i, min (κ (false, i)) (κ (true, i)) = k := by
      rw [hκ, ← hk]
      simp only [pairExp_apply, min_self]
    rw [h4]
    calc ‖((∏ i, (n i).factorial : ℕ) : K)‖ * (‖S‖ ^ k * ∏ i, ‖u i ^ n i‖)
        ≤ 1 * (r ^ k * 1) := by
          apply mul_le_mul h1 _ (by positivity) zero_le_one
          exact mul_le_mul h3 h2 (Finset.prod_nonneg fun _ _ => norm_nonneg _) (pow_nonneg hr0 _)
      _ = r ^ k := by ring
  · rw [if_neg hκ]
    simp only [smul_zero, mul_zero, norm_zero]
    exact pow_nonneg hr0 _

end PairJetAux

theorem pair_jet_bound : PairJet.{u} := by
  intro K _ _ _ pi h0 h1 ι _ S u hS hu sg hsg κ
  classical
  set r : ℝ := pi ^ (-(1 / 2 : ℝ)) with hrdef
  have hr : 1 ≤ r := Real.one_le_rpow_of_pos_of_le_one_of_nonpos h0 h1.le (by norm_num)
  have hr0 : (0 : ℝ) ≤ r := by linarith
  have hrhs : pi ^ (-(1 / 2 : ℝ) * ∑ i, (min (κ (false, i)) (κ (true, i)) : ℝ)) =
      r ^ (∑ i, min (κ (false, i)) (κ (true, i))) := by
    rw [Real.rpow_mul h0.le, ← Real.rpow_natCast]
    congr 1
    push_cast
    rfl
  rw [hrhs, MvPowerSeries.coeff_mul, Finset.mul_sum]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (pow_nonneg hr0 _) fun p hp => ?_
  rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp
  obtain ⟨c, hc⟩ := mfact_mul_dvd p.1 p.2
  rw [hp] at hc
  have hE := exp_jet r hr ι S u hS hu p.1
  have hG := hsg p.2
  have hcn : ‖((c : ℕ) : K)‖ ≤ 1 := IsUltrametricDist.norm_natCast_le_one K _
  set E := mvExp ((-S) • ∑ i, MvPowerSeries.C (u i) * MvPowerSeries.X (false, i) *
          MvPowerSeries.X (true, i) : MvPowerSeries (Bool × ι) K)
  have hre : ((mfact κ : ℕ) : K) * (MvPowerSeries.coeff p.1 E * MvPowerSeries.coeff p.2 sg) =
      (((mfact p.1 : ℕ) : K) * MvPowerSeries.coeff p.1 E) *
        ((((mfact p.2 : ℕ) : K) * MvPowerSeries.coeff p.2 sg) * ((c : ℕ) : K)) := by
    rw [hc]; push_cast; ring
  rw [hre, norm_mul, norm_mul (((mfact p.2 : ℕ) : K) * MvPowerSeries.coeff p.2 sg)]
  have hmono : r ^ (∑ i, min (p.1 (false, i)) (p.1 (true, i))) ≤
      r ^ (∑ i, min (κ (false, i)) (κ (true, i))) := by
    apply pow_le_pow_right₀ hr
    apply Finset.sum_le_sum fun i _ => ?_
    rw [← hp]
    simp only [Finsupp.add_apply]
    omega
  calc _ ≤ r ^ (∑ i, min (p.1 (false, i)) (p.1 (true, i))) * (1 * 1) := by
        apply mul_le_mul hE _ (by positivity) (pow_nonneg hr0 _)
        exact mul_le_mul hG hcn (norm_nonneg _) zero_le_one
    _ ≤ _ := by rw [mul_one, mul_one]; exact hmono

end Formalism.DworkPowerSeriesWeights
end
end

