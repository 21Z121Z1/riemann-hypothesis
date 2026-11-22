import Mathlib
import Formalism.RealPlaceAnalysis.SmoothOnGVIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0391
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0393
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.WeightedSumBounds.PeriodValuationTheory
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.WeightedSumBounds.Bundle0004
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0004
import Development.AbelianVarietyTheory.Definitions.Divisors.EllFamNontrivial
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0004
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0370
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0011
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0363
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0360

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.OffDiagBlockNormContInv
section
open MeasureTheory Matrix
open Formalism.REAL (UJ KG toM toMK muK expG inG Jm Kset)

namespace GlobalTheory

theorem offDiagBlockNorm_cont_inv : ∀ (n : ℕ) (ε : Fin n → Bool), (Continuous fun g : UJ ε => ∑ z : {z : Fin n × Fin n // ε z.1 = true ∧ ε z.2 = false}, ‖(toM g) z.1.1 z.1.2‖ ^ 2) ∧ ∀ (k k' : KG ε) (g : UJ ε), ∑ z : {z : Fin n × Fin n // ε z.1 = true ∧ ε z.2 = false}, ‖(toM ((k : UJ ε) * g * (k' : UJ ε))) z.1.1 z.1.2‖ ^ 2 = ∑ z : {z : Fin n × Fin n // ε z.1 = true ∧ ε z.2 = false}, ‖(toM g) z.1.1 z.1.2‖ ^ 2 := by
  intro n ε
  refine ⟨?_, ?_⟩
  · have hM : Continuous fun g : UJ ε => toM g :=
      Units.continuous_val.comp continuous_subtype_val
    refine continuous_finset_sum _ fun z _ => ?_
    exact ((continuous_apply z.1.2).comp ((continuous_apply z.1.1).comp hM)).norm.pow 2
  · intro k k' g
    have hk : toM (k : UJ ε) ∈ Kset ε := k.2
    have hk' : toM (k' : UJ ε) ∈ Kset ε := k'.2
    have hmul : toM ((k : UJ ε) * g * (k' : UJ ε)) = toM (k : UJ ε) * toM g * toM (k' : UJ ε) := rfl
    rw [hmul]
    refine GlobalTheory.T.offDiagonalBlock_sum_sq_norm_blockUnitary_invariant n ε _ _ _ ?_ hk.2 ?_ hk'.2
    · exact Matrix.mem_unitaryGroup_iff'.mp hk.1
    · exact Matrix.mem_unitaryGroup_iff'.mp hk'.1

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.OmegaBaseChangeBijectiveOfPEqZero
section
open TensorProduct Coalgebra Bialgebra CategoryTheory WithConv GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup

namespace GlobalTheory

namespace PDiv

theorem liftSemi_toBaseChange_cot_bijective (R R' A : Type) [CommRing R] [CommRing R'] [Algebra R R']
    [CommRing A] [Bialgebra R A] : Function.Bijective (liftSemi (toBaseChange R R' A).cot) := by
  have heq : (counitAlgHom R' (R' ⊗[R] A)).comp
      ((AlgEquiv.refl : (R' ⊗[R] A) ≃ₐ[R'] (R' ⊗[R] A)) : (R' ⊗[R] A) →ₐ[R'] (R' ⊗[R] A)) =
      AugCot.baseChangeAug R' (counitAlgHom R A) := by
    apply Algebra.TensorProduct.ext'
    intro r a
    simp [AugCot.baseChangeAug_tmul, Algebra.smul_def, mul_comm]
  let E : R' ⊗[R] Cot R A ≃ₗ[R'] Cot R' (R' ⊗[R] A) :=
    (AugCot.baseChangeEquiv R' (counitAlgHom R A)).trans (AugCot.congr AlgEquiv.refl heq)
  have key : ∀ x, liftSemi (toBaseChange R R' A).cot x = E x := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => rw [map_add, map_add, hx, hy]
    | tmul r m =>
      obtain ⟨a, rfl⟩ := AugCot.d_surjective (counitAlgHom R A) m
      have h1 := SemiBialgHom.cot_d (toBaseChange R R' A) a
      simp only [liftSemi_tmul, E, LinearEquiv.trans_apply]
      rw [show AugCot.d (counitAlgHom R A) a = dUnit R a from rfl, h1, AugCot.baseChangeEquiv_tmul_d,
        map_smul, AugCot.congr_d]
      rfl
  have hfun : ⇑(liftSemi (toBaseChange R R' A).cot) = ⇑E := funext key
  rw [hfun]
  exact E.bijective

end PDiv

namespace PDivGroup

theorem omega_baseChange_bijective {p : ℕ} {R : Type} [CommRing R] (G : PDivGroup p R) (R' : Type)
    [CommRing R'] [Algebra R R'] (hp : (p : R) = 0) :
    Function.Bijective (liftSemi (G.toBase R').omega) := by
  have hp' : (p : R') = 0 := by rw [← map_natCast (algebraMap R R'), hp, map_zero]
  have hL := G.omegaLevel_one_bijective hp
  have hL' := (G.baseChange R').omegaLevel_one_bijective hp'
  have hg := liftSemi_toBaseChange_cot_bijective R R' (G.A 1)
  let e : R' ⊗[R] G.omega ≃ₗ[R'] R' ⊗[R] Cot R (G.A 1) :=
    LinearEquiv.baseChange R R' _ _ (LinearEquiv.ofBijective (G.omegaLevel 1) hL)
  have key : ∀ x, (G.baseChange R').omegaLevel 1 (liftSemi (G.toBase R').omega x) =
      liftSemi (toBaseChange R R' (G.A 1)).cot (e x) := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => rw [map_add, map_add, map_add, map_add, hx, hy]
    | tmul r w =>
      simp only [liftSemi_tmul, map_smul, e, LinearEquiv.baseChange_tmul, LinearEquiv.ofBijective_apply]
      congr 1
  have hcomp : ⇑((G.baseChange R').omegaLevel 1) ∘ ⇑(liftSemi (G.toBase R').omega) =
      ⇑(liftSemi (toBaseChange R R' (G.A 1)).cot) ∘ ⇑e := funext key
  exact (Function.Bijective.of_comp_iff' hL' _).1 (hcomp ▸ hg.comp e.bijective)

end PDivGroup

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.OrdGeExpOfLogSumTwoRadii
section
open MvPowerSeries ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Sh GlobalTheory.FGDepth

namespace GlobalTheory.ExpWeightTwoRadii

variable {C : Type} [Field C] {M : ℕ}

def WtBelow (v : AddValuation C (WithTop ℝ)) (ρ : Fin M → ℝ) (D : ℕ)
    (g : MvPowerSeries (Fin M) C) (r : ℝ) : Prop :=
  ∀ α : Fin M →₀ ℕ, Finsupp.degree α < D →
    (((r - ∑ m, ρ m * (α m : ℝ) : ℝ)) : WithTop ℝ) ≤ v (coeff α g)

theorem wt_add_index (ρ : Fin M → ℝ) (β γ : Fin M →₀ ℕ) :
    ∑ m, ρ m * ((β + γ) m : ℝ) = (∑ m, ρ m * (β m : ℝ)) + ∑ m, ρ m * (γ m : ℝ) := by
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [Finsupp.add_apply, Nat.cast_add, mul_add]

theorem WtBelow.mul {v : AddValuation C (WithTop ℝ)} {ρ : Fin M → ℝ} {D : ℕ}
    {g h : MvPowerSeries (Fin M) C} {r s : ℝ} (hg0 : constantCoeff g = 0)
    (hh0 : constantCoeff h = 0) (hg : WtBelow v ρ D g r) (hh : WtBelow v ρ D h s) :
    WtBelow v ρ (D + 1) (g * h) (r + s) := by
  classical
  intro α hα
  rw [coeff_mul]
  refine v.map_le_sum fun q hq => ?_
  have hq' : q.1 + q.2 = α := by simpa using hq
  by_cases h1 : q.1 = 0
  · rw [h1, coeff_zero_eq_constantCoeff_apply, hg0, zero_mul, v.map_zero]; exact le_top
  by_cases h2 : q.2 = 0
  · rw [h2, coeff_zero_eq_constantCoeff_apply, hh0, mul_zero, v.map_zero]; exact le_top
  have hd : Finsupp.degree q.1 + Finsupp.degree q.2 = Finsupp.degree α := by
    rw [← hq', map_add]
  have d1 : Finsupp.degree q.1 ≠ 0 := fun e => h1 ((Finsupp.degree_eq_zero_iff _).1 e)
  have d2 : Finsupp.degree q.2 ≠ 0 := fun e => h2 ((Finsupp.degree_eq_zero_iff _).1 e)
  rw [v.map_mul]
  refine le_trans (le_of_eq ?_) (add_le_add (hg q.1 (by omega)) (hh q.2 (by omega)))
  rw [← WithTop.coe_add, ← hq', wt_add_index]
  congr 1
  ring

theorem WtBelow.pow_succ {v : AddValuation C (WithTop ℝ)} {ρ : Fin M → ℝ} {D : ℕ}
    {g : MvPowerSeries (Fin M) C} {r : ℝ} (hg0 : constantCoeff g = 0)
    (hg : WtBelow v ρ D g r) (k : ℕ) :
    WtBelow v ρ D (g ^ (k + 1)) (((k + 1 : ℕ) : ℝ) * r) := by
  induction k with
  | zero => simpa using hg
  | succ k ih =>
    have h := WtBelow.mul (by simp [hg0]) hg0 ih hg
    intro α hα
    have h' := h α (by omega)
    rw [_root_.pow_succ g (k + 1)]
    refine le_trans (le_of_eq ?_) h'
    congr 1
    push_cast
    ring

theorem WtBelow.pow {v : AddValuation C (WithTop ℝ)} {ρ : Fin M → ℝ} {D : ℕ}
    {g : MvPowerSeries (Fin M) C} {r : ℝ} (hg0 : constantCoeff g = 0)
    (hg : WtBelow v ρ D g r) {N : ℕ} (hN : 2 ≤ N) :
    WtBelow v ρ (D + 1) (g ^ N) ((N : ℝ) * r) := by
  obtain ⟨k, rfl⟩ : ∃ k, N = k + 1 + 1 := ⟨N - 2, by omega⟩
  have h := WtBelow.mul (by simp [hg0]) hg0 (hg.pow_succ hg0 k) hg
  rw [_root_.pow_succ g (k + 1)]
  convert h using 1
  push_cast
  ring

theorem ordGe_of_lgSum_radii (v : AddValuation C (WithTop ℝ)) (p : ℕ) (hp : p.Prime)
    {d : ℕ} (good : Fin d → Prop) [DecidablePred good] (c : Fin d → ℕ → Fin d → C)
    (h0 : ∀ a, c a 0 = Pi.single a 1)
    (hc : ∀ a (n : ℕ) b, ((-(n : ℝ) : ℝ) : WithTop ℝ) ≤ v (c a n b))
    (hgood : ∀ a, good a → ∀ (n : ℕ) b, 1 ≤ n → ((1 - (n : ℝ) : ℝ) : WithTop ℝ) ≤ v (c a n b))
    (ρ : Fin M → ℝ) (z t : Fin d → MvPowerSeries (Fin M) C) (r : Fin d → ℝ)
    (hr : ∀ b, r b = if good b then 2 / ((p : ℝ) * (p - 1)) else 2 / ((p : ℝ) - 1))
    (hz : ∀ b, OrdGe v ρ (z b) (r b)) (ht : ∀ b, constantCoeff (t b) = 0)
    (hlg : ∀ b, lgSum p c t b = z b) : ∀ b, OrdGe v ρ (t b) (r b) := by
  classical
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hp1 : (p : ℝ) - 1 ≠ 0 := by linarith
  have hp0 : (p : ℝ) ≠ 0 := by linarith
  set g' : ℝ := 2 / ((p : ℝ) - 1) with hg'
  have hg'1 : g' * ((p : ℝ) - 1) = 2 := by rw [hg']; field_simp
  have hg'0 : 0 < g' := by rw [hg']; apply div_pos <;> linarith
  have hgp : 2 / ((p : ℝ) * (p - 1)) * p = g' := by rw [hg']; field_simp
  have hγ0 : 0 ≤ 2 / ((p : ℝ) * (p - 1)) := by
    apply div_nonneg (by norm_num); apply mul_nonneg <;> linarith
  have hγg : 2 / ((p : ℝ) * (p - 1)) ≤ g' := by
    have := mul_le_mul_of_nonneg_left (show (1 : ℝ) ≤ p by linarith) hγ0
    linarith
  have hre : ∀ e, r e ≤ g' := by
    intro e; rw [hr e]; split_ifs <;> linarith

  have hnum : ∀ (a e : Fin d) (n : ℕ) (L : ℝ), (good a → -(n : ℝ) ≤ L) →
      (-((n : ℝ) + 1) ≤ L) → r e ≤ L + (p : ℝ) ^ (n + 1) * r a := by
    intro a e n L hLg hL
    have hb := one_add_mul_sub_le_pow (a := (p : ℝ)) (by linarith) n
    have hb' := mul_le_mul_of_nonneg_left hb hg'0.le
    have hb1 := one_add_mul_sub_le_pow (a := (p : ℝ)) (by linarith) (n + 1)
    have hb1' := mul_le_mul_of_nonneg_left hb1 hg'0.le
    have e1 : g' * (1 + (n : ℝ) * ((p : ℝ) - 1)) = g' + 2 * n := by
      linear_combination (n : ℝ) * hg'1
    have e2 : g' * (1 + ((n + 1 : ℕ) : ℝ) * ((p : ℝ) - 1)) = g' + 2 * ((n : ℝ) + 1) := by
      push_cast; linear_combination ((n : ℝ) + 1) * hg'1
    have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    have hre' := hre e
    rw [hr a]
    split_ifs with hga
    · have hL' := hLg hga
      have e3 : (p : ℝ) ^ (n + 1) * (2 / ((p : ℝ) * (p - 1))) = g' * (p : ℝ) ^ n := by
        rw [_root_.pow_succ, ← hgp]; ring
      rw [e3]; linarith
    · have e4 : (p : ℝ) ^ (n + 1) * g' = g' * (p : ℝ) ^ (n + 1) := by ring
      rw [e4]; linarith
  have step : ∀ D : ℕ, ∀ a, WtBelow v ρ D (t a) (r a) := by
    intro D
    induction D with
    | zero => intro a α hα; omega
    | succ D ih =>
      intro e α hα
      have h1 : coeff α (lgSum p c t e) = coeff α (z e) := by rw [hlg e]
      have h2 : coeff α (lgSum p c t e) =
          ∑ n ∈ Finset.range (Finsupp.degree α + 1), ∑ a, c a n e * coeff α (t a ^ (p ^ n)) :=
        rfl
      rw [h2, Finset.sum_range_succ'] at h1
      have h3 : ∑ a, c a 0 e * coeff α (t a ^ (p ^ 0)) = coeff α (t e) := by
        simp [h0, Pi.single_apply]
      rw [h3] at h1
      rw [eq_sub_of_add_eq' h1]
      refine v.map_le_sub (hz e α) ?_
      refine v.map_le_sum fun n _ => v.map_le_sum fun a _ => ?_
      have hN : 2 ≤ p ^ (n + 1) := le_trans hp.two_le (Nat.le_self_pow (by omega) p)
      have h4 := (ih a).pow (ht a) hN α hα
      rw [v.map_mul]
      by_cases hga : good a
      · have hc1 := hgood a hga (n + 1) e (by omega)
        refine le_trans ?_ (add_le_add hc1 h4)
        rw [← WithTop.coe_add, WithTop.coe_le_coe]
        have := hnum a e n (1 - ((n + 1 : ℕ) : ℝ)) (fun _ => by push_cast; linarith)
          (by push_cast; linarith)
        push_cast at this ⊢
        linarith
      · have hc1 := hc a (n + 1) e
        refine le_trans ?_ (add_le_add hc1 h4)
        rw [← WithTop.coe_add, WithTop.coe_le_coe]
        have := hnum a e n (-((n + 1 : ℕ) : ℝ)) (fun h => absurd h hga) (by push_cast; linarith)
        push_cast at this ⊢
        linarith
  intro b α
  exact step (Finsupp.degree α + 1) b α (by omega)

theorem ordGe_of_lgSum_twoRadii :
    ∀ (C : Type) [Field C] [CharZero C] (v : AddValuation C (WithTop ℝ)) (p : ℕ), p.Prime → v (p : C) = 1 → ∀ (d M : ℕ) (good : Fin d → Prop) [DecidablePred good] (c : Fin d → ℕ → Fin d → C), (∀ a, c a 0 = Pi.single a 1) → (∀ a (n : ℕ) b, ((-(n : ℝ) : ℝ) : WithTop ℝ) ≤ v (c a n b)) → (∀ a, good a → ∀ (n : ℕ) b, 1 ≤ n → ((1 - (n : ℝ) : ℝ) : WithTop ℝ) ≤ v (c a n b)) → ∀ (ρ : Fin M → ℝ) (z t : Fin d → MvPowerSeries (Fin M) C), (∀ b, OrdGe v ρ (z b) (if good b then 2 / ((p : ℝ) * (p - 1)) else 2 / ((p : ℝ) - 1))) → (∀ b, constantCoeff (t b) = 0) → (∀ b, lgSum p c t b = z b) → ∀ b, OrdGe v ρ (t b) (if good b then 2 / ((p : ℝ) * (p - 1)) else 2 / ((p : ℝ) - 1)) := by
  intro C _ _ v p hp _ d M good _ c h0 hc hgood ρ z t hz ht hlg
  exact ordGe_of_lgSum_radii v p hp good c h0 hc hgood ρ z t
    (fun b => if good b then 2 / ((p : ℝ) * (p - 1)) else 2 / ((p : ℝ) - 1)) (fun _ => rfl)
    hz ht hlg

end GlobalTheory.ExpWeightTwoRadii
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PDivGroupMulPUnitFibreEqLevelOne
section
open scoped TensorProduct

set_option autoImplicit false

noncomputable section

open TensorProduct Coalgebra Bialgebra GlobalTheory.PDiv

namespace GlobalTheory

namespace PDivGroup

variable {p : ℕ} {R : Type} [CommRing R] (G : PDivGroup p R)

open scoped TensorProduct in
set_option autoImplicit false in
open TensorProduct Coalgebra Bialgebra in
variable {p : ℕ} {R : Type} [CommRing R] (G : _root_.GlobalTheory.PDivGroup p R) in
theorem _root_.GlobalTheory.PDivGroup.ker_resOne (n : ℕ) :
    RingHom.ker (G.resOne n :
      G.A (n + 1) →ₐ[R] G.A 1) =
      _root_.GlobalTheory.PDiv.torsionIdeal R (G.A (n + 1)) p := by
  induction n with
  | zero =>
    have hid : (G.resOne 0 :
        G.A 1 →ₐ[R] G.A 1) = AlgHom.id R _ := by
      ext a; exact G.resOne_zero a
    rw [hid]
    refine le_antisymm ?_ ?_
    · intro a ha
      have : a = 0 := ha
      simp [this]
    · refine (_root_.GlobalTheory.PDiv.torsionIdeal_le_ker_iff p
        (AlgHom.id R (G.A (0 + 1)))).2 ?_
      simpa using G.pts_pow_self 1 (WithConv.toConv (AlgHom.id R (G.A 1)))
  | succ n ih =>
    have hcomp : (G.resOne (n + 1) :
        G.A (n + 2) →ₐ[R] G.A 1) =
        (G.resOne n :
          G.A (n + 1) →ₐ[R] G.A 1).comp
          (G.res (n + 1) :
            G.A (n + 2) →ₐ[R] G.A (n + 1)) := by
      ext a; exact G.resOne_succ n a
    have hsurj : Function.Surjective (G.res (n + 1) :
        G.A (n + 2) →ₐ[R] G.A (n + 1)) :=
      G.res_surjective (n + 1)
    have hker : RingHom.ker ((G.resOne n :
        G.A (n + 1) →ₐ[R] G.A 1).comp
          (G.res (n + 1) :
            G.A (n + 2) →ₐ[R] G.A (n + 1))) =
        Ideal.comap (G.res (n + 1) :
          G.A (n + 2) →ₐ[R] G.A (n + 1))
          (RingHom.ker (G.resOne n :
            G.A (n + 1) →ₐ[R] G.A 1)) := by
      ext a; exact Iff.rfl
    rw [hcomp, hker, ih, ← _root_.GlobalTheory.PDiv.map_torsionIdeal
      (G.res_surjective (n + 1)) p]
    erw [Ideal.comap_map_of_surjective _ hsurj]
    refine sup_eq_left.mpr ?_
    have h0 : Ideal.comap (G.res (n + 1) :
        G.A (n + 2) →ₐ[R] G.A (n + 1)) ⊥ =
        _root_.GlobalTheory.PDiv.torsionIdeal R (G.A (n + 2)) (p ^ (n + 1)) := by
      rw [← G.ker_res (n + 1)]
      ext a; exact Iff.rfl
    rw [h0]
    exact _root_.GlobalTheory.PDiv.torsionIdeal_le_of_dvd (dvd_pow_self p (Nat.succ_ne_zero n))

open scoped TensorProduct in
set_option autoImplicit false in
open TensorProduct Coalgebra Bialgebra in
variable {p : ℕ} {R : Type} [CommRing R] (G : _root_.GlobalTheory.PDivGroup p R) in
theorem _root_.GlobalTheory.PDivGroup.kerIdeal_mulP (n : ℕ) :
    _root_.GlobalTheory.PDiv.kerIdeal (G.mulP n) =
      _root_.GlobalTheory.PDiv.torsionIdeal R (G.A (n + 1)) p := by
  unfold _root_.GlobalTheory.PDiv.torsionIdeal
  rw [← G.mulP_comp_res n,
    _root_.GlobalTheory.PDiv.kerIdeal_comp_of_surjective _ (G.res_surjective n)]

end PDivGroup

section TensorQuot

variable {R k M : Type} [CommRing R] [CommRing k] [Algebra R k] [AddCommGroup M] [Module R M]

end TensorQuot

namespace PDivGroup

end PDivGroup

open scoped TensorProduct in
set_option autoImplicit false in
open TensorProduct Coalgebra Bialgebra in
private theorem mem_ker_smul_univ_of_one_tmul_eq_zero {R k M : Type} [CommRing R] [CommRing k]
    [Algebra R k] [AddCommGroup M] [Module R M] (hk : Function.Surjective (algebraMap R k))
    {m : M} (hm : (1 : k) ⊗ₜ[R] m = 0) :
    m ∈ RingHom.ker (algebraMap R k) • (⊤ : Submodule R M) := by
  set f : R →ₐ[R] k := Algebra.ofId R k
  have hf : Function.Surjective f := hk
  let e : (R ⧸ RingHom.ker f) ≃ₐ[R] k := Ideal.quotientKerAlgEquivOfSurjective hf
  have hker : RingHom.ker f = RingHom.ker (algebraMap R k) := rfl
  let g : k ⊗[R] M ≃ₗ[R] M ⧸ (RingHom.ker f • (⊤ : Submodule R M)) :=
    (LinearEquiv.rTensor M e.symm.toLinearEquiv).trans
      (quotTensorEquivQuotSMul M (RingHom.ker f))
  have h1 : e.symm 1 = Ideal.Quotient.mk (RingHom.ker f) 1 := by simp
  have h2 : g ((1 : k) ⊗ₜ[R] m) = Submodule.Quotient.mk m := by
    simp only [g, LinearEquiv.trans_apply, LinearEquiv.rTensor_tmul,
      AlgEquiv.toLinearEquiv_apply, h1, quotTensorEquivQuotSMul_mk_tmul, one_smul]
  rw [hm, map_zero, eq_comm, Submodule.Quotient.mk_eq_zero] at h2
  exact hker ▸ h2

open scoped TensorProduct in
set_option autoImplicit false in
open TensorProduct Coalgebra Bialgebra in
theorem _root_.GlobalTheory.fibre_statement : ∀ (p : ℕ) (R k : Type) [CommRing R] [CommRing k]
    [Algebra R k], Function.Surjective (algebraMap R k) → ∀ (G : _root_.GlobalTheory.PDivGroup p R) (n : ℕ),
      Function.Surjective (fun a : G.A (n + 1) =>
        ((1 : k) ⊗ₜ[R] G.resOne n a : k ⊗[R] G.A 1)) ∧
      ∀ a : G.A (n + 1),
        ((1 : k) ⊗ₜ[R] G.resOne n a : k ⊗[R] G.A 1) = 0 ↔
          a ∈ (RingHom.ker ((algebraMap R k).comp
            (Bialgebra.counitAlgHom R (G.A n) :
              G.A n →+* R))).map
            ((G.mulP n : G.A n →ₐ[R] G.A (n + 1)) :
              G.A n →+* G.A (n + 1)) := by
  intro p R k _ _ _ hk G n
  set ρ := G.resOne n
  set μ := G.mulP n
  set J := RingHom.ker ((algebraMap R k).comp
    (Bialgebra.counitAlgHom R (G.A n) : G.A n →+* R))
  set L := J.map ((μ : G.A n →ₐ[R] G.A (n + 1)) :
    G.A n →+* G.A (n + 1))
  have hρ : Function.Surjective ρ := G.resOne_surjective n
  have hJ : ∀ x : G.A n, x ∈ J ↔
      algebraMap R k (Bialgebra.counitAlgHom R (G.A n) x) = 0 :=
    fun x => Iff.rfl
  refine ⟨?_, fun a => ⟨fun ha => ?_, fun ha => ?_⟩⟩
  · intro t
    induction t using TensorProduct.induction_on with
    | zero => exact ⟨0, by simp⟩
    | tmul c x =>
      obtain ⟨r, rfl⟩ := hk c
      obtain ⟨y, rfl⟩ := hρ x
      refine ⟨r • y, ?_⟩
      show (1 : k) ⊗ₜ[R] ρ (r • y) = _
      rw [map_smul, TensorProduct.tmul_smul, TensorProduct.smul_tmul',
        Algebra.algebraMap_eq_smul_one]
    | add s t hs ht =>
      obtain ⟨a, rfl⟩ := hs
      obtain ⟨b, rfl⟩ := ht
      exact ⟨a + b, by simp [TensorProduct.tmul_add]⟩
  · have hmem := mem_ker_smul_univ_of_one_tmul_eq_zero hk ha
    have hle : RingHom.ker (algebraMap R k) • (⊤ : Submodule R (G.A 1)) ≤
        (L.restrictScalars R).map
          (ρ : G.A (n + 1) →ₐ[R] G.A 1).toLinearMap := by
      refine Submodule.smul_le.mpr fun r hr x _ => ?_
      obtain ⟨y, rfl⟩ := hρ x
      refine ⟨r • y, ?_, map_smul _ r y⟩
      show r • y ∈ L
      rw [Algebra.smul_def]
      refine Ideal.mul_mem_right _ _ ?_
      have h1 : algebraMap R (G.A (n + 1)) r =
          (μ : G.A n →ₐ[R] G.A (n + 1))
            (algebraMap R (G.A n) r) := (AlgHom.commutes _ r).symm
      rw [h1]
      refine Ideal.mem_map_of_mem _ ((hJ _).mpr ?_)
      rw [AlgHom.commutes]
      exact hr
    obtain ⟨b, hb, hab⟩ := hle hmem
    have hker : a - b ∈ RingHom.ker
        (ρ : G.A (n + 1) →ₐ[R] G.A 1) := by
      rw [RingHom.mem_ker, map_sub, sub_eq_zero]
      exact hab.symm
    rw [_root_.GlobalTheory.PDivGroup.ker_resOne,
      ← _root_.GlobalTheory.PDivGroup.kerIdeal_mulP] at hker
    have haug : _root_.GlobalTheory.PDiv.kerIdeal μ ≤ L := by
      unfold _root_.GlobalTheory.PDiv.kerIdeal
      refine Ideal.map_mono fun x hx => (hJ x).mpr ?_
      rw [show Bialgebra.counitAlgHom R (G.A n) x = 0 from hx, map_zero]
    have := L.add_mem (haug hker) hb
    rwa [sub_add_cancel] at this
  · let ψ : G.A (n + 1) →+* k ⊗[R] G.A 1 :=
      (Algebra.TensorProduct.includeRight :
        G.A 1 →ₐ[R] k ⊗[R] G.A 1).toRingHom.comp
        (ρ : G.A (n + 1) →ₐ[R] G.A 1).toRingHom
    have hL : L ≤ RingHom.ker ψ := by
      refine Ideal.map_le_iff_le_comap.mpr fun j hj => ?_
      rw [Ideal.mem_comap, RingHom.mem_ker]
      show (1 : k) ⊗ₜ[R] ρ (μ j) = 0
      rw [G.resOne_mulP, Algebra.algebraMap_eq_smul_one, TensorProduct.tmul_smul,
        TensorProduct.smul_tmul', ← Algebra.algebraMap_eq_smul_one]
      have := (hJ j).mp hj
      rw [Bialgebra.counitAlgHom_apply] at this
      rw [this, TensorProduct.zero_tmul]
    exact hL ha

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PDivGroupOmegaNoPTorsionOfCotangentInjective
section
open scoped TensorProduct

namespace GlobalTheory

open PDiv

theorem omega_eq_zero_of_p_smul_eq_zero :
    ∀ (p : ℕ) (R : Type) [CommRing R] (G : GlobalTheory.PDivGroup p R),
      (∀ n, Function.Injective (GlobalTheory.PDiv.cotMap (G.mulP n))) →
        ∀ w : G.omega, (p : R) • w = 0 → w = 0 := by
  intro p R _ G hinj w hw
  refine Subtype.ext (funext fun n => ?_)
  have hp : (p : R) • w.1 (n + 1) = 0 := congrArg (fun v : G.omega => v.1 (n + 1)) hw
  apply hinj n
  change cotMap (G.mulP n) (w.1 n) = cotMap (G.mulP n) 0
  rw [map_zero, ← w.2 n, ← LinearMap.comp_apply, ← cotMap_comp, G.mulP_comp_res,
    cotMap_mulBy, hp]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PeriodClassInjectiveOfRichChartsStatement
section
open CategoryTheory GlobalTheory.CatCoh GlobalTheory.AnPer GlobalTheory.AnPer.Charts TopologicalSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.periodClass_injective_of_rich_charts : ∀ {I : Type} [Fintype I] {g : ℕ} {Λ : Type} [AddCommGroup Λ] {F : Fam I g Λ} (K : Charts F), K.Rich → ∀ per per' : Λ →+ Hol F.V, K.perCl per = K.perCl per' → per = per' := by
  first | exact @GlobalTheory.AnPer.Charts.perCl_injective | exact GlobalTheory.AnPer.Charts.perCl_injective | (intros; apply GlobalTheory.AnPer.Charts.perCl_injective <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolynomialRingIrreduciblePrimeReduction
section
open GlobalTheory.PD GlobalTheory.CechDR KaehlerDifferential
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.polynomial_ring_irreducible_prime_reduction : ∀ (k F : Type) [Field k] [Field F] [Algebra k F] (d : ℕ) (u : Fin d → F), AlgebraicIndependent k u → ∀ (A : Subalgebra k F), A = Algebra.adjoin k (Set.range u) → ∀ t : A, Irreducible t → Prime t ∧ ∃ m : ℕ, d = m + 1 ∧ ∃ y : Fin m → A, IsTranscendenceBasis k (fun j => Ideal.Quotient.mk (Ideal.span {t}) (y j)) := by
  first | (exact @GlobalTheory.TrBasisQuot.trBasis_mod_irreducible) | (exact GlobalTheory.TrBasisQuot.trBasis_mod_irreducible) | (intros; apply GlobalTheory.TrBasisQuot.trBasis_mod_irreducible  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrimitiveRootFreeActionFinsuppSumStatement
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC GlobalTheory.EtC.KummerSplit
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.primitiveRoot_free_action_finsupp_sum : ∀ (q : ℕ) [NeZero q] (A : Type) [CommRing A] [Nontrivial A] (ζ : Prim q A) (ι : Type) (s : Finset ι) (c : ι → ULift.{1} (ZMod q)) (a : ι → ℕ) (v w : ι → Aˣ), (∀ i ∈ s, (w i : A) = ζ.1 ^ a i * v i) → (∑ i ∈ s, (Finsupp.single (w i) (c i) - Finsupp.single (v i) (c i))) = 0 → ∑ i ∈ s, (c i).down * (a i : ZMod q) = 0 := by
  first | (exact @GlobalTheory.EtC.FreeActSum.free_act_sum) | (exact GlobalTheory.EtC.FreeActSum.free_act_sum) | (intros; apply GlobalTheory.EtC.FreeActSum.free_act_sum  <;> assumption)
end

