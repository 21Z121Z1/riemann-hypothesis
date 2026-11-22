import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0777
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0836
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0819
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.MemZmuOfPowPred
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.MemParahoricOfTrivialReduction
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0066
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0073
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0809
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0797
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.LtChar
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0304
import Development.AbelianVarietyTheory.CrystallinePeriods.RingIface
import Development.AbelianVarietyTheory.CrystallinePeriods.CrisIncl
import Development.AbelianVarietyTheory.CrystallinePeriods.Bundle0001
import Development.AbelianVarietyTheory.Definitions.Foundations.IsProbabilityMeasureMuPart
import Formalism.QuotientMetricDivisors.Statement
import Formalism.MeanHeightDescent.DivisionInequalityWithCovolume
import Development.AbelianVarietyTheory.Counterexamples.RotationExamples.MeasureFailsForLargeConstant
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0837
import Development.AbelianVarietyTheory.Definitions.Divisors.IsAddHaarMeasureVolumeLie
import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0009
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0838
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0066
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CharacterSumLocalConstantFifth
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker GlobalTheory.IndefiniteRowSideFullHecke.PlaceLogThetaBounds GlobalTheory.ColNorms
open scoped ComplexOrder

namespace GlobalTheory.ColNorms.Unfold

open GlobalTheory.TopStep GlobalTheory.LastSteps GlobalTheory.PadicUnfold GlobalTheory.PadicUnfold.Period

section Count

variable {E : Type} [Field E] [NumberField E] {P : HeightOneSpectrum (𝓞 E)}

theorem dvd_of_intAt_div (hq : (Formalism.L2.Col.qOf P).Prime) (d : ℕ) :
    ∀ i : ℕ, IntAt P ((i : E) / (Formalism.L2.Col.qOf P : E) ^ d) → Formalism.L2.Col.qOf P ^ d ∣ i := by
  have hq0 : (Formalism.L2.Col.qOf P : E) ≠ 0 := qOf_ne_zero
  induction d with
  | zero => intro i _; simp
  | succ d ih =>
    intro i hi
    have h1 : IntAt P ((i : E) / (Formalism.L2.Col.qOf P : E)) := by
      convert (intAt_pow (intAt_nat (P := P) (Formalism.L2.Col.qOf P)) d).mul hi using 1
      field_simp
      ring
    have h2 := redP_eq_zero_of_div h1
    have h3 := reduction_coe P ((i : ℕ) : 𝓞 E)
    rw [map_natCast, h2] at h3
    have h4 : ((i : ℕ) : 𝓞 E) ∈ P.asIdeal := Ideal.Quotient.eq_zero_iff_mem.1 h3.symm
    have h5 : Formalism.L2.Col.qOf P ∣ i := by
      by_contra hn
      obtain ⟨a, b, hab⟩ : IsCoprime ((Formalism.L2.Col.qOf P : ℕ) : 𝓞 E) ((i : ℕ) : 𝓞 E) :=
        Nat.Coprime.cast ((Nat.Prime.coprime_iff_not_dvd hq).2 hn)
      exact P.isPrime.ne_top ((Ideal.eq_top_iff_one _).2
        (hab ▸ add_mem (Ideal.mul_mem_left _ _ qOf_mem) (Ideal.mul_mem_left _ _ h4)))
    obtain ⟨j, rfl⟩ := h5
    rw [pow_succ']
    refine Nat.mul_dvd_mul_left _ (ih j ?_)
    convert hi using 1
    push_cast
    field_simp
    ring

open Classical in

theorem card_vals_le (hq : (Formalism.L2.Col.qOf P).Prime) (A B c : ℕ) :
    ((LocE.valsQ E (Formalism.L2.Col.qOf P) A B).filter fun a => IntAt P ((Formalism.L2.Col.qOf P : E) ^ c * a)).card ≤
      Formalism.L2.Col.qOf P ^ (B + c) := by
  have hq0 : (Formalism.L2.Col.qOf P : E) ≠ 0 := qOf_ne_zero
  rcases le_total A c with h | h
  · refine (Finset.card_filter_le _ _).trans (Finset.card_image_le.trans ?_)
    rw [Finset.card_range]
    exact Nat.pow_le_pow_right hq.pos (by omega)
  · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
    refine le_trans (Finset.card_le_card (t := (Finset.range (Formalism.L2.Col.qOf P ^ (B + c))).image
      fun j : ℕ => (j : E) / (Formalism.L2.Col.qOf P : E) ^ c) fun a ha => ?_) (Finset.card_image_le.trans (by rw [Finset.card_range]))
    obtain ⟨ha, hi⟩ := Finset.mem_filter.1 ha
    obtain ⟨i, hr, rfl⟩ := Finset.mem_image.1 ha
    obtain ⟨j, rfl⟩ := dvd_of_intAt_div hq d i (by
      convert hi using 1
      rw [pow_add]
      field_simp)
    refine Finset.mem_image.2 ⟨j, Finset.mem_range.2 ?_, ?_⟩
    · have := Finset.mem_range.1 hr
      rw [show c + d + B = d + (B + c) by ring, pow_add] at this
      exact lt_of_mul_lt_mul_left this (Nat.zero_le _)
    · push_cast
      rw [pow_add]
      field_simp

end Count

section Unfolding

variable {E K : Type} [Field E] [NumberField E] [StarRing E] [Field K] {P : HeightOneSpectrum (𝓞 E)}

omit [StarRing E] in
theorem intAt_zpow_mono {a : E} {u v : ℤ} (h : u ≤ v) (ha : IntAt P (a * (Formalism.L2.Col.qOf P : E) ^ u)) :
    IntAt P (a * (Formalism.L2.Col.qOf P : E) ^ v) := by
  obtain ⟨d, rfl⟩ : ∃ d : ℕ, v = u + d := ⟨(v - u).toNat, by omega⟩
  rw [zpow_add₀ qOf_ne_zero, zpow_natCast, ← mul_assoc]
  exact ha.mul (intAt_pow (intAt_nat _) _)

theorem unfolding_smallHomFunction_levelPrime_bounded (hq : (Formalism.L2.Col.qOf P).Prime) {n' c' n c : ℕ} (hc : c' = c + 1) (A B : ℕ) (psi : E → K)
    (hpsi : ∀ a, IntAt P ((Formalism.L2.Col.qOf P : E) * a) → psi a ^ Formalism.L2.Col.qOf P = 1)
    (Φ : Loc.SF E K (n' + c') (n + c))
    (hΦ : LocSmall (Formalism.L2.Col.qOf P) (LocE.lamY P (Formalism.L2.Col.qOf P) n' c' fun i => i + 1)
      (LocE.lamY P (Formalism.L2.Col.qOf P) n c fun i => i + 1) Φ 1) :
    LocSmall (Formalism.L2.Col.qOf P) (stdAt E n' P) (stdAt E n P)
      (Loc.E1 psi (LocE.valsQ E (Formalism.L2.Col.qOf P) A B) (((Formalism.L2.Col.qOf P : K) ^ B)⁻¹) Φ)
      ((Formalism.L2.Col.qOf P : ℝ) ^ (c' * ((n + c) * (n' + c')))) := by
  classical
  subst hc
  have hent : ∀ y, Φ y ≠ 0 → ∀ (l : Fin (n + c)) (l' : Fin (n' + (c + 1))), IntAt P (y (Pi.single l' 1) l *
      (Formalism.L2.Col.qOf P : E) ^ (LocE.scE n' (fun i => i + 1) l'.1 - LocE.scE n (fun i => i + 1) l.1)) :=
    fun y hy => mem_homS_sclLat.1 (hΦ.1 y hy)
  refine ⟨fun x hx y hy => ?_, fun x z hz => ?_, fun σ x => ?_⟩
  · obtain ⟨t, -, ht⟩ := Finset.exists_ne_zero_of_sum_ne_zero (right_ne_zero_of_mul hx)
    refine mem_stdAt.2 fun l => ?_
    rw [apply_eq_sum]
    refine intAt_sum _ fun j _ => (mem_stdAt.1 hy j).mul ?_
    have h := hent _ (left_ne_zero_of_mul ht) (Fin.castAdd c l) (Fin.castAdd (c + 1) j)
    have hj := j.2
    rw [linearMap_unfolding_apply_single, dif_neg (by unfold Loc.IsFree; simp only [Fin.val_castAdd]; omega), dif_pos (by simp),
      dif_pos (by simp)] at h
    simpa [LocE.scE] using h
  · unfold Loc.E1
    congr 1
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [periodXX1_add_smul, chArg_add, chArg_smul_extZero, add_zero, hΦ.2.1]
    refine mem_homS_sclLat.2 fun l l' => ?_
    rw [extZero_single]
    split_ifs with hs hl
    · simpa [LocE.scE, hs, hl] using mem_stdAt.1 (hz _ (single_mem_stdAt ⟨l'.1, hs⟩)) ⟨l.1, hl⟩
    · simpa using intAt_zero
    · simpa using intAt_zero
  · set q := Formalism.L2.Col.qOf P with hqdef
    have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast hq.one_le
    set F := Fintype.card (Loc.FC n' (c + 1) n c) with hF
    have hFle : F ≤ (n + c) * (n' + (c + 1)) := by
      refine (Fintype.card_subtype_le _).trans ?_
      simp
    set V := (LocE.valsQ E q A B).filter fun a => IntAt P ((q : E) ^ (c + 1) * a) with hV
    have hsum : ∑ t ∈ Fintype.piFinset fun _ : Loc.FC n' (c + 1) n c => LocE.valsQ E q A B,
        Φ (Loc.xx1 x t) * psi (-Loc.chArg (Loc.xx1 x t)) = ∑ t ∈ Fintype.piFinset fun _ : Loc.FC n' (c + 1) n c => V,
        Φ (Loc.xx1 x t) * psi (-Loc.chArg (Loc.xx1 x t)) := by
      symm
      refine Finset.sum_subset (Fintype.piFinset_subset _ _ fun _ => Finset.filter_subset _ _) fun t ht hn => ?_
      by_contra h0
      refine hn (Fintype.mem_piFinset.2 fun p => Finset.mem_filter.2 ⟨Fintype.mem_piFinset.1 ht p, ?_⟩)
      have h := hent _ (left_ne_zero_of_mul h0) p.1.1 p.1.2
      rw [linearMap_unfolding_apply_single, dif_pos p.2] at h
      have h' := intAt_zpow_mono (v := ((c + 1 : ℕ) : ℤ)) (by
        have := p.1.2.2
        unfold LocE.scE
        split_ifs <;> push_cast <;> omega) h
      rwa [zpow_natCast, mul_comm] at h'
    have hterm : ∀ y, ‖σ (Φ y * psi (-Loc.chArg y))‖ ≤ 1 := by
      intro y
      by_cases h0 : Φ y = 0
      · simp [h0]
      have h1 : IntAt P ((q : E) * -Loc.chArg y) := by
        rw [mul_neg, chArg_eq, Finset.mul_sum]
        refine intAt_neg (intAt_sum _ fun i _ => ?_)
        have h := hent y h0 ⟨n + i.1, by omega⟩ ⟨n' + i.1 + 1, by omega⟩
        have h' := intAt_zpow_mono (v := 1) (by
          unfold LocE.scE
          dsimp only
          rw [if_neg (by omega), if_neg (by omega)]
          omega) h
        rwa [zpow_one, mul_comm] at h'
      have h2 : ‖σ (psi (-Loc.chArg y))‖ ^ q = 1 := by rw [← norm_pow, ← map_pow, hpsi _ h1, map_one, norm_one]
      rw [map_mul, norm_mul, (pow_eq_one_iff_of_nonneg (norm_nonneg _) hq.ne_zero).1 h2, mul_one]
      exact hΦ.2.2 σ y
    unfold Loc.E1
    rw [hsum, map_mul, norm_mul, map_pow, map_inv₀, map_pow, map_natCast, norm_pow, norm_inv, norm_pow, Complex.norm_natCast,
      map_sum]
    have hb : ‖∑ t ∈ Fintype.piFinset fun _ : Loc.FC n' (c + 1) n c => V,
        σ (Φ (Loc.xx1 x t) * psi (-Loc.chArg (Loc.xx1 x t)))‖ ≤ ((q : ℝ) ^ (B + (c + 1))) ^ F := by
      refine (norm_sum_le _ _).trans ((Finset.sum_le_card_nsmul _ _ 1 fun t _ => hterm _).trans ?_)
      rw [Fintype.card_piFinset, Finset.prod_const, Finset.card_univ, nsmul_eq_mul, mul_one, Nat.cast_pow]
      refine pow_le_pow_left₀ (Nat.cast_nonneg _) ?_ _
      have hc : V.card ≤ q ^ (B + (c + 1)) := card_vals_le hq A B (c + 1)
      exact_mod_cast hc
    refine (mul_le_mul_of_nonneg_left hb (by positivity)).trans ?_
    rw [← mul_pow, pow_add, inv_mul_cancel_left₀ (by positivity), ← pow_mul]
    exact pow_le_pow_right₀ hq1 (Nat.mul_le_mul_left _ hFle)

end Unfolding

section Index

theorem relIndex_le_card {G T : Type} [Group G] [Finite T] (H M : Subgroup G) (f : G → T)
    (hf : ∀ a ∈ M, ∀ b ∈ M, f a = f b → a⁻¹ * b ∈ H) : H.relIndex M ≤ Nat.card T := by
  refine Nat.card_le_card_of_injective (fun z : M ⧸ H.subgroupOf M => f z.out.1) fun z w h => ?_
  rw [← z.out_eq, ← w.out_eq]
  exact QuotientGroup.eq.2 (Subgroup.mem_subgroupOf.2 (hf _ z.out.2 _ w.out.2 h))

variable {E : Type} [Field E] [NumberField E] [StarRing E] {P : HeightOneSpectrum (𝓞 E)}

theorem relIndex_le (hq : ((Formalism.L2.Col.qOf P : ℕ) : 𝓞 E) ∉ P.asIdeal ^ 2) (k₀ rS r t n c : ℕ)
    (h : Sp E (n + c) ≃ₗ[E] Sp E (n + c)) (hh : h ∈ stabL E _ (LocE.lamY P (Formalism.L2.Col.qOf P) n c fun i => i + 1)) :
    (Loc.Cbe (LocE.JGsym P (Formalism.L2.Col.qOf P) k₀ rS r t n c) h ⊓ Loc.N1 E n c).relIndex
      (Loc.N1 E n c ⊓ stabL E _ (LocE.lamY P (Formalism.L2.Col.qOf P) n c fun i => i + 1)) ≤
        Formalism.L2.Col.qOf P ^ ((n + c) * (n + c)) := by
  have hfin : Finite (𝓞 E ⧸ P.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot _ P.ne_bot
  have hq0 : (Formalism.L2.Col.qOf P : E) ≠ 0 := qOf_ne_zero
  refine (relIndex_le_card _ _ (fun (g : Sp E (n + c) ≃ₗ[E] Sp E (n + c)) (p : Fin (n + c) × Fin (n + c)) =>
    redP P (g (Pi.single p.2 1) p.1 * (Formalism.L2.Col.qOf P : E) ^
      (LocE.scE n (fun i => i + 1) p.2.1 - LocE.scE n (fun i => i + 1) p.1.1))) fun a ha b hb hab => ?_).trans (le_of_eq ?_)
  · have hm := mul_mem (inv_mem ha) hb
    refine ⟨⟨hm.1.1, ?_⟩, hm.1⟩
    have hd : ((Formalism.L2.Col.qOf P : E)⁻¹ • (b.toLinearMap - a.toLinearMap)) ∈
        homS (LocE.lamY P (Formalism.L2.Col.qOf P) n c fun i => i + 1) (LocE.lamY P (Formalism.L2.Col.qOf P) n c fun i => i + 1) := by
      refine mem_homS_sclLat.2 fun l l' => ?_
      have h1 := mem_homS_sclLat.1 (show a.toLinearMap ∈ homS _ _ from fun y hy => (ha.2 y).2 hy) l l'
      have h2 := mem_homS_sclLat.1 (show b.toLinearMap ∈ homS _ _ from fun y hy => (hb.2 y).2 hy) l l'
      have h3 := intAt_div_of_redP hq (intAt_sub h2 h1) (by
        rw [reduction_sub h2 h1, sub_eq_zero]
        exact (congrFun hab (l, l')).symm)
      convert h3 using 1
      simp only [LinearMap.smul_apply, LinearMap.sub_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
      ring
    have hc0 : ∀ x ∈ LocE.lamY P (Formalism.L2.Col.qOf P) n c fun i => i + 1, (Formalism.L2.Col.qOf P : E)⁻¹ • ((a⁻¹ * b) x - x) ∈
        LocE.lamY P (Formalism.L2.Col.qOf P) n c fun i => i + 1 := by
      intro x hx
      refine (ha.2 _).1 ?_
      rw [map_smul, map_sub, show a ((a⁻¹ * b) x) = b x from LinearEquiv.apply_symm_apply _ _]
      exact hd x hx
    have e : (MulAut.conj h⁻¹).toMonoidHom (a⁻¹ * b) = h⁻¹ * (a⁻¹ * b) * h := by simp
    show (MulAut.conj h⁻¹).toMonoidHom (a⁻¹ * b) ∈ LocE.JGsym P (Formalism.L2.Col.qOf P) k₀ rS r t n c
    rw [e]
    have hs := mul_mem (mul_mem (inv_mem hh) hm.2) hh
    have hc := GlobalTheory.CongLevel.conj_cong (Formalism.L2.Col.qOf P) _ _ h hh hc0
    refine ⟨hs, GlobalTheory.CongLevel.mem_flagU (Formalism.L2.Col.qOf P) _ _ _ _ _ (fun s => ?_) (fun s x hx => ?_) (fun s => ?_) _ hs hc⟩
    · exact GlobalTheory.CongLevel.sclLat_le P _ hq0 _ _ _
    · exact GlobalTheory.CongLevel.smul_mem_sclLat P _ hq0 _ _ _ x hx
    · exact GlobalTheory.CongLevel.bvec_mem P _ hq0 _ _ _
  · rw [Nat.card_fun, Nat.card_prod, Nat.card_eq_fintype_card (α := Fin (n + c)), Fintype.card_fin]
    rfl

theorem norm_volN_inv_le {k K : Type} [CommRing k] [Field K] {n c : ℕ}
    (C M : Subgroup ((Fin (n + c) → k) ≃ₗ[k] (Fin (n + c) → k))) (σ : K →+* ℂ) :
    ‖σ (Loc.volN K C M)⁻¹‖ ≤ ((C ⊓ Loc.N1 k n c).relIndex M : ℕ) := by
  unfold Loc.volN
  rw [inv_div, map_div₀, map_natCast, map_natCast, norm_div, Complex.norm_natCast, Complex.norm_natCast]
  rcases Nat.eq_zero_or_pos (M.relIndex (C ⊓ Loc.N1 k n c)) with h | h
  · simp [h]
  · exact div_le_self (Nat.cast_nonneg _) (by exact_mod_cast h)

end Index

theorem rank_le (R : Ranks) {j : ℕ} (hj : j ≤ R.m) : R.N j + cOf R j ≤ R.N R.m := by
  unfold Ranks.N cOf
  obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le hj
  have : d ≤ d * (R.t + 1) := Nat.le_mul_of_pos_right _ (by omega)
  have h2 : R.m * (R.t + 1) = j * (R.t + 1) + d * (R.t + 1) := by rw [hd, add_mul]
  omega

end GlobalTheory.ColNorms.Unfold
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CharacterSumLocalConstantSeventh
section
noncomputable section

namespace GlobalTheory.ColNorms.DatOne

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker GlobalTheory.IndefiniteRowSideFullHecke.PlaceLogThetaBounds GlobalTheory.ColNorms
open scoped ComplexOrder

section Generic

variable {E K : Type} [Field E] [NumberField E] [StarRing E] [Field K]

theorem mem_lamY_iff (P : HeightOneSpectrum (𝓞 E)) (q n c : ℕ) (ex : ℕ → ℕ) (v : Sp E (n + c)) :
    v ∈ LocE.lamY P q n c ex ↔ ∀ l : Fin (n + c), Formalism.L2.Col.IntAt P (((q : E) ^ LocE.scE n ex l.1)⁻¹ * v l) := by
  unfold LocE.lamY LocE.sclLat
  rw [Submodule.mem_comap]
  exact mem_localization_standardLattice P _

theorem proj_mem {P : HeightOneSpectrum (𝓞 E)} {q n c : ℕ} {ex : ℕ → ℕ} {v : Sp E (n + c)} (hv : v ∈ LocE.lamY P q n c ex) :
    LinearMap.funLeft E E (Fin.castAdd c) v ∈ stdAt E n P := by
  refine (mem_localization_standardLattice P _).2 fun i => ?_
  have h := (mem_lamY_iff P q n c ex v).1 hv (Fin.castAdd c i)
  simpa [LocE.scE, LinearMap.funLeft_apply] using h

theorem proj_inX {n c : ℕ} (y : Sp E n) : LinearMap.funLeft E E (Fin.castAdd c) (Loc.inX E n c y) = y := by
  funext i
  simp [LinearMap.funLeft_apply, Loc.inX]

theorem inX_mem_iff (P : HeightOneSpectrum (𝓞 E)) (q n c : ℕ) (ex : ℕ → ℕ) (y : Sp E n) :
    Loc.inX E n c y ∈ LocE.lamY P q n c ex ↔ y ∈ stdAt E n P := by
  constructor
  · intro h
    simpa [proj_inX] using proj_mem h
  · intro h
    refine (mem_lamY_iff P q n c ex _).2 fun l => ?_
    by_cases hl : l.1 < n
    · have := (mem_localization_standardLattice P _).1 h ⟨l.1, hl⟩
      simpa [LocE.scE, Loc.inX, hl] using this
    · have := Formalism.L2.Col.IntAt.coe P (0 : 𝓞 E)
      simpa [Loc.inX, hl] using this

theorem joinCol_inX {n' c' n c : ℕ} (x₀ : HomE E n' n) (y' : Sp E n) (y : Sp E n') :
    (joinCol x₀ y' : HomE E (n' + c') (n + c)) (Loc.inX E n' c' y) = Loc.inX E n c (x₀ y) := by
  have h0 : atNL E (n' + c') n' (Loc.inX E n' c' y) = 0 := by
    unfold atNL
    split_ifs with h
    · simp [Loc.inX]
    · rfl
  simp [joinCol, proj_inX, h0]

theorem joinCol_add {n' c' n c : ℕ} (x₀ z : HomE E n' n) (t : E) (y' : Sp E n) :
    (joinCol (x₀ + t • z) y' : HomE E (n' + c') (n + c)) =
      joinCol x₀ y' + t • (Loc.inX E n c ∘ₗ z ∘ₗ LinearMap.funLeft E E (Fin.castAdd c')) := by
  refine LinearMap.ext fun v => ?_
  simp only [joinCol, LinearMap.comp_apply, LinearMap.add_apply, LinearMap.smul_apply, map_add, map_smul]
  abel

theorem locSmall_joinCol {P : HeightOneSpectrum (𝓞 E)} {q n' c' n c : ℕ} {ex' ex : ℕ → ℕ} {Φ : HomE E (n' + c') (n + c) → K} {β : ℝ}
    (h : LocSmall q (LocE.lamY P q n' c' ex') (LocE.lamY P q n c ex) Φ β) (y' : Sp E n) :
    LocSmall q (stdAt E n' P) (stdAt E n P) (fun x₀ => Φ (joinCol x₀ y')) β := by
  refine ⟨fun x hx y hy => ?_, fun x z hz => ?_, fun σ x => h.2.2 σ _⟩
  · have := h.1 _ hx _ ((inX_mem_iff P q n' c' ex' y).2 hy)
    rw [joinCol_inX] at this
    exact (inX_mem_iff P q n c ex _).1 this
  · show Φ (joinCol (x + (q : E) • z) y') = Φ (joinCol x y')
    rw [joinCol_add]
    exact h.2.1 _ _ fun v hv => (inX_mem_iff P q n c ex _).2 (hz _ (proj_mem hv))

theorem smallDatum_of_frames {a b : ℕ} {ST SG SG' SB : Finset (HeightOneSpectrum (𝓞 E))} [DecidableEq (HeightOneSpectrum (𝓞 E))]
    (d : Deco E a ST SG) (d' : DecoSet E b ST SG')
    (f : Frs E a SB) (f' : Frs E b SB) (hf : ∀ (P : SB) x, f P x ∈ d.at P.1 ↔ x ∈ stdAt E a P.1)
    (hf' : ∀ (P : SB) x, f' P x ∈ d'.1.at P.1 ↔ x ∈ stdAt E b P.1) (c : ℕ) (q : SB → ℕ) (hq : ∀ P, q P ∣ c)
    (hT : ∀ P ∈ ST, (c : 𝓞 E) ∈ P.asIdeal) (Ψ : SB → HomE E a b → K) (β : SB → ℝ)
    (hΨ : ∀ P : SB, LocSmall (q P) (stdAt E a P.1) (stdAt E b P.1) (Ψ P) (β P)) :
    SmallDatum (ST ∪ SB) d.N d'.1.N c (fun x => phiT K d d'.1 x * ∏ P : SB, Ψ P (inFr (f P) (f' P) x)) (∏ P, β P) := by
  refine ⟨fun x hx P hP y hy => ?_, fun x y hy => ?_, fun σ x => ?_⟩
  · obtain ⟨h1, h2⟩ := mul_ne_zero_iff.1 hx
    rcases Finset.mem_union.1 hP with hP | hP
    · unfold phiT at h1
      split_ifs at h1 with h
      · exact (h ⟨P, hP⟩ y hy).1
      · exact absurd rfl h1
    · have h3 := Finset.prod_ne_zero_iff.1 h2 ⟨P, hP⟩ (Finset.mem_univ _)
      have h4 : (f ⟨P, hP⟩).symm y ∈ stdAt E a P := (hf ⟨P, hP⟩ _).1 (by simpa using hy)
      have h5 := (hf' ⟨P, hP⟩ _).2 ((hΨ ⟨P, hP⟩).1 _ h3 _ h4)
      simpa [inFr] using h5
  · obtain ⟨z, hz, rfl⟩ := Submodule.mem_map.1 hy
    have hz' : ∀ P ∈ ST ∪ SB, ∀ y ∈ d.at P, z y ∈ d'.1.at P := hz
    have e0 : (((c : 𝓞 E) • (LinearMap.id : HomE E a b →ₗ[𝓞 E] HomE E a b)) z) = (c : 𝓞 E) • z := rfl
    rw [e0]
    show phiT K d d'.1 _ * _ = phiT K d d'.1 _ * _
    congr 1
    · unfold phiT
      classical
      refine @if_congr _ _ _ (_) (_) _ _ _ _ (forall_congr' fun P => forall_congr' fun y => forall_congr' fun hy => ?_) rfl rfl
      have hzy : z y ∈ d'.1.at P.1 := hz' P.1 (Finset.mem_union_left _ P.2) y hy
      have hc : (c : 𝓞 E) • z y ∈ d'.1.at P.1 := Submodule.smul_mem _ _ hzy
      have e : (x + (c : 𝓞 E) • z) y = x y + (c : 𝓞 E) • z y := rfl
      rw [e, Submodule.add_mem_iff_left _ hc]
      refine and_congr_right fun hx => ?_
      rw [d'.2.f_add P _ hx _ hc, d'.2.f_smul P _ _ hzy, Ideal.Quotient.eq_zero_iff_mem.2 (hT P.1 P.2), zero_mul, add_zero]
    · refine Finset.prod_congr rfl fun P _ => ?_
      obtain ⟨k, hk⟩ := hq P
      have e : inFr (f P) (f' P) (x + (c : 𝓞 E) • z) =
          inFr (f P) (f' P) x + (q P : E) • inFr (f P) (f' P) (k • z) := by
        refine LinearMap.ext fun v => ?_
        have : (c : 𝓞 E) • z = (q P : E) • (k • z) := by
          rw [Nat.cast_smul_eq_nsmul, Nat.cast_smul_eq_nsmul, hk, mul_smul]
        rw [this]
        simp [inFr]
      rw [e]
      refine (hΨ P).2.1 _ _ fun v hv => (hf' P _).1 ?_
      have := nsmul_mem (hz' P.1 (Finset.mem_union_right _ P.2) _ ((hf P v).2 hv)) k
      simpa [inFr] using this
  · show ‖σ (phiT K d d'.1 x * _)‖ ≤ _
    rw [map_mul, norm_mul, map_prod, norm_prod]
    have h1 : ‖σ (phiT K d d'.1 x)‖ ≤ 1 := by
      unfold phiT
      split_ifs <;> simp
    have h2 : ∏ P : SB, ‖σ (Ψ P (inFr (f P) (f' P) x))‖ ≤ ∏ P, β P :=
      Finset.prod_le_prod (fun _ _ => norm_nonneg _) fun P _ => (hΨ P).2.2 σ _
    calc _ ≤ 1 * ∏ P, β P := mul_le_mul h1 h2 (Finset.prod_nonneg fun _ _ => norm_nonneg _) zero_le_one
      _ = _ := one_mul _

end Generic

end GlobalTheory.ColNorms.DatOne
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjugatePeriodMemFiltrationZero
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct GlobalTheory.PZ GlobalTheory.PMC GlobalTheory.AinfK GlobalTheory.AcrisK GlobalTheory.BKReal GlobalTheory.ConjPeriod
open scoped Formalism.Per

noncomputable section

namespace GlobalTheory.ConjPeriod

variable {l : ℕ} [Fact l.Prime] {P : LocPrime l} {AI : LocAinf l P}

abbrev plusR (l : ℕ) [Fact l.Prime] : Subring (Per.BdR l) := (algebraMap (Per.BdRp l) (Per.BdR l)).range

theorem eD_uj_mem (T : LocTied l P AI) (j : ℕ) (a : Per.Acris l) : T.eD (uj T j a) ∈ plusR l := by
  obtain ⟨i, hi, -⟩ := GlobalTheory.CrisIncl.exists_restrict l _ T.incl
  exact ⟨_, (hi ((GlobalTheory.MemLoc.phiA l ^ j) a)).symm⟩

theorem eD_om_mem (T : LocTied l P AI) (x : Om l) : T.eD (algebraMap (Om l) P.R.BdR x) ∈ plusR l := by
  obtain ⟨y, hy, -⟩ := T.om x
  exact ⟨y, hy.symm⟩

theorem l_inv_mem (l : ℕ) [Fact l.Prime] : ∃ u ∈ plusR l, (l : Per.BdR l) * u = 1 := by
  obtain ⟨v, hv⟩ := (GlobalTheory.RingBasics.isUnit_l l).exists_right_inv
  refine ⟨algebraMap (Per.BdRp l) (Per.BdR l) (algebraMap (Per.AinfP l) (Per.BdRp l) v), ⟨_, rfl⟩, ?_⟩
  have h := congrArg ((algebraMap (Per.BdRp l) (Per.BdR l)).comp (algebraMap (Per.AinfP l) (Per.BdRp l))) hv
  rwa [map_mul, map_natCast, map_one] at h

theorem conj_mem_Fil_zero : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (T : LocTied l P AI)
    (K : FinExt l) (j : ℕ) (s : ↥K.1 →ₐ[ℚ_[l]] Om l) (h : Compat T K j s) (b : BK K),
    conj T K j s h b ∈ (P.PD K).Fil 0 := by
  intro l _ P AI T K j s h b
  let f : BK K →+* Per.BdR l := T.eD.toRingHom.comp (conj T K j s h)
  have hz : ∀ z : CK K, f (toB K z) ∈ plusR l := fun z => by
    induction z using GlobalTheory.AcrisK.induction_on with
    | mul a c =>
      rw [map_mul, map_mul]
      refine mul_mem ?_ ?_
      · exact eD_uj_mem T j a |> fun h' => by
          simpa only [f, RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe, conj_inC] using h'
      · rw [← inK_oK]
        simpa only [f, RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe, conj_inK] using
          eD_om_mem T (s (oK K c))
    | add x y hx hy => rw [map_add, map_add]; exact add_mem hx hy
  obtain ⟨D, z, hD⟩ := exists_pow_mul b
  obtain ⟨u, hu, hlu⟩ := l_inv_mem l
  have e : f b = u ^ D * f (toB K z) := by
    rw [← hD, map_mul, map_pow, map_natCast, ← mul_assoc, ← mul_pow, mul_comm u, hlu, one_pow, one_mul]
  have hm : f b ∈ plusR l := e ▸ mul_mem (pow_mem hu D) (hz z)
  obtain ⟨y, hy⟩ := hm
  rw [T.fil]
  change f b ∈ Per.FilD l 0
  rw [← hy]
  exact GlobalTheory.MemLoc.TiedUnif.alg_mem_FilD_zero y

end GlobalTheory.ConjPeriod

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CovolumePerRankLeNegSlopeScaledStatement
section
open NumberField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.covolumePerRank_le_neg_slope_scaled : ∀ (K V : Type) [Field K] [NumberField K] [IsTotallyComplex K] [StarRing K] [AddCommGroup V] [Module K V]
    [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (N : (K →+* ℂ) → V → ℝ), GlobalTheory.AllWt.HasGram N →
    ∀ (L : Submodule (𝓞 K) V) (d : ℕ), 0 < d → ∀ (b : Fin d → V), LinearIndependent K b →
    (∀ x ∈ L, x ∈ Submodule.span K (Set.range b)) →
    ∀ (X : InfinitePlace K → Matrix (Fin d) (Fin d) ℂ) (s : ℝ), 0 < s → s ≤ 1 → (∀ v, IsUnit (X v).det) →
    (∀ v (c : Fin d → K), Formalism.HermitianLatticesTheory.normAt (Pi.basisFun K (Fin d)) X v c = s * N v.embedding (∑ k, c k • b k)) →
    Submodule.IsLattice K (L.comap ((Fintype.linearCombination K b).restrictScalars (𝓞 K))) →
    Formalism.DivisionValues.lcv X (L.comap ((Fintype.linearCombination K b).restrictScalars (𝓞 K))) / (d : ℝ) ≤ -GlobalTheory.AllWt.slope_sq N L := by
  first | exact @GlobalTheory.CovolCore.lcv_div_le_neg_slope_sq | exact GlobalTheory.CovolCore.lcv_div_le_neg_slope_sq | (intros; apply GlobalTheory.CovolCore.lcv_div_le_neg_slope_sq <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EsymmMulSchurPolynomialJacobiTrudiStatement
section
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.esymm_mul_schurPolynomialJacobiTrudi : ∀ (n : ℕ) (l : Fin n → ℕ), Antitone l → ∀ j ≤ n, MvPolynomial.esymm (Fin n) ℤ j * GlobalTheory.JSW.schur n l = ∑ J ∈ (Finset.univ : Finset (Finset (Fin n))).filter (fun J => J.card = j ∧ Antitone (l + (fun i => if i ∈ J then 1 else 0))), GlobalTheory.JSW.schur n (l + (fun i => if i ∈ J then 1 else 0)) := by
  first | exact @GlobalTheory.JSW.esymm_mul_schur | exact GlobalTheory.JSW.esymm_mul_schur | (intros; apply GlobalTheory.JSW.esymm_mul_schur <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleCohomologyFieldEqGaloisCohomologyStatement
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.etaleCohomology_field_eq_galoisCohomology : GlobalTheory.EtC.B7 := by
  first | (exact @GlobalTheory.EtC.FieldTw.field_tw_coh_eq_galois) | (exact GlobalTheory.EtC.FieldTw.field_tw_coh_eq_galois) | (intros; apply GlobalTheory.EtC.FieldTw.field_tw_coh_eq_galois  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEtaleNbhdKillingCurveCohomologyClassStatement
section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_etaleNbhd_killing_curveCohomologyClass : ∀ (q : ℕ) [NeZero q] (k B : Type) [Field k] [IsAlgClosed k] [CommRing B] [IsDedekindDomain B] [Algebra k B] [Algebra.FiniteType k B], IsUnit (q : k) → ∀ f : B, f ≠ 0 → ∀ (n i : ℤ), 0 < n → ∀ x : Ht q (sp B) n i, ∃ (A' : Type) (_ : CommRing A') (_ : Algebra B A'), IsExcisionNbhd B A' f ∧ pull _ (spMap (algebraMap B A')) _ _ x = 0 := by
  first | (exact @GlobalTheory.EtC.CurveNbhdExcision.main) | (exact GlobalTheory.EtC.CurveNbhdExcision.main) | (intros; apply GlobalTheory.EtC.CurveNbhdExcision.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLineBundleSpreadFromLocalSchemeStatement
section
open AlgebraicGeometry CategoryTheory Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_lineBundle_spread_from_localScheme : ∀ {S Y U YU : Scheme.{0}} [IsLocallyNoetherian S] (f : Y ⟶ S) [QuasiCompact f] [QuasiSeparated f] (j : U ⟶ S) [IsOpenImmersion j] (e : YU ⟶ Y) (fU : YU ⟶ U), IsPullback e fU f j → ∀ (L : LB YU), L.IsLB → ∀ (x : S) (N : LB (pullback f (S.fromSpecStalk x))), N.IsLB → (∀ (T : Scheme.{0}) (a : T ⟶ pullback f (S.fromSpecStalk x)) (b : T ⟶ YU), a ≫ pullback.fst f (S.fromSpecStalk x) = b ≫ e → LBIso (N.pull a) (L.pull b)) → ∃ W : S.Opens, x ∈ W ∧ ∃ N' : LB ↑(f ⁻¹ᵁ W), N'.IsLB ∧ ∀ (T : Scheme.{0}) (a : T ⟶ ↑(f ⁻¹ᵁ W)) (b : T ⟶ YU), a ≫ (f ⁻¹ᵁ W).ι = b ≫ e → LBIso (N'.pull a) (L.pull b) := by
  first | exact @GlobalTheory.SpreadLB.exists_spread | exact GlobalTheory.SpreadLB.exists_spread | (intros; apply GlobalTheory.SpreadLB.exists_spread <;> assumption)
end

