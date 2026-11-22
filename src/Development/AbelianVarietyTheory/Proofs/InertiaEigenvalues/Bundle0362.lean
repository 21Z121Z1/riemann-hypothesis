import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0005
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0074
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0105
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0088
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0280
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0246
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0334
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0226
import Formalism.WachLatticeTwists.LatticeDualFibres.FibreDualStable
import Formalism.GaloisCohomology.LocalTateDualityK
import ReciprocityTheory.ReductiveGroups.TraceFormulas.LatDefs
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0170
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0061
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0052
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0331
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0278
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0345
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0291
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FirstHalfLocalCohomologyVanishingOfLocalDualityT
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContinuousAlgebraMapPadicInt
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0305
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0341
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0320
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemOfForallAnnihilatorAnnihilatorFieldModInteger

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemBreuilKisinIdealPowOfNormLe
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP

theorem exists_of_mem_ball_small {l : ℕ} (hl : 1 < l) {A : Type} [CommRing A] (u : A) {ρ : ℝ≥0} (h0 : 0 < ρ)
    (h1 : ρ < 1) (m n : ℕ) {y : PreDisc l u ρ} (hy : y ∈ ball l u ρ ((ρ : ℝ) ^ m / (l : ℝ) ^ n)) :
    ∃ (c : ℕ) (z₁ z₂ : A), algebraMap A (PreDisc l u ρ) ((l : A) ^ c) * y =
      algebraMap A (PreDisc l u ρ) (u ^ m * z₁ + (l : A) ^ (c + n) * z₂) := by
  have hl1 : (1 : ℝ) < l := by exact_mod_cast hl
  have hρ0 : (0 : ℝ) < ρ := h0
  have hρ1 : (ρ : ℝ) ≤ 1 := h1.le
  induction hy using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨a, b, c, hw, rfl⟩ := hx
    have e : algebraMap A (PreDisc l u ρ) ((l : A) ^ c) * (algebraMap A (PreDisc l u ρ) ((l : A) ^ a * u ^ b) *
        IsLocalization.Away.invSelf (l : A) ^ c) = algebraMap A (PreDisc l u ρ) ((l : A) ^ a * u ^ b) := by
      rw [map_pow, mul_left_comm, ← mul_pow, IsLocalization.Away.mul_invSelf, one_pow, mul_one]
    rcases le_or_gt m b with hb | hb
    · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hb
      refine ⟨c, (l : A) ^ a * u ^ k, 0, ?_⟩
      rw [e]; congr 1; ring
    · have hp : (ρ : ℝ) ^ m ≤ (ρ : ℝ) ^ b := pow_le_pow_of_le_one hρ0.le hρ1 hb.le
      have h2 : (l : ℝ) ^ (c + n) ≤ (l : ℝ) ^ a := by
        rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)] at hw
        have h3 : (l : ℝ) ^ (c + n) * (ρ : ℝ) ^ b ≤ (l : ℝ) ^ a * (ρ : ℝ) ^ b :=
          calc (l : ℝ) ^ (c + n) * (ρ : ℝ) ^ b = (l : ℝ) ^ c * (ρ : ℝ) ^ b * (l : ℝ) ^ n := by ring
            _ ≤ _ := hw
            _ ≤ (ρ : ℝ) ^ b * (l : ℝ) ^ a := mul_le_mul_of_nonneg_right hp (by positivity)
            _ = _ := mul_comm _ _
        exact le_of_mul_le_mul_right h3 (by positivity)
      obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le ((pow_le_pow_iff_right₀ hl1).1 h2)
      refine ⟨c, 0, (l : A) ^ k * u ^ b, ?_⟩
      rw [e]; congr 1; ring
  | zero => exact ⟨0, 0, 0, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨c, z₁, z₂, h⟩ := hx
    obtain ⟨c', z₁', z₂', h'⟩ := hy
    refine ⟨c + c', (l : A) ^ c' * z₁ + (l : A) ^ c * z₁', z₂ + z₂', ?_⟩
    simp only [map_add, map_mul, map_pow, pow_add] at h h' ⊢
    linear_combination (algebraMap A (PreDisc l u ρ) (l : A)) ^ c' * h +
      (algebraMap A (PreDisc l u ρ) (l : A)) ^ c * h'
  | smul a x _ hx =>
    obtain ⟨c, z₁, z₂, h⟩ := hx
    refine ⟨c, a * z₁, a * z₂, ?_⟩
    simp only [map_add, map_mul, map_pow, pow_add, Algebra.smul_def] at h ⊢
    linear_combination (algebraMap A (PreDisc l u ρ) a) * h

theorem exists_of_norm_toDisc_lt {l : ℕ} (hl : 1 < l) {A : Type} [CommRing A] (u : A)
    (ht : ∀ x : A, (l : A) * x = 0 → x = 0) (m : ℕ) (hd : ∀ x y : A, (l : A) * x = u ^ m * y → u ^ m ∣ x)
    {ρ : ℝ≥0} (h0 : 0 < ρ) (h1 : ρ < 1) (n : ℕ) (x : A) (hx : ‖toDisc l u ρ x‖ < (ρ : ℝ) ^ m / (l : ℝ) ^ n) :
    ∃ z₁ z₂ : A, x = u ^ m * z₁ + (l : A) ^ n * z₂ := by
  have hb : algebraMap A (PreDisc l u ρ) x ∈ ball l u ρ ((ρ : ℝ) ^ m / (l : ℝ) ^ n) :=
    mem_ball_of_gauge_lt l u ρ ((norm_ofPre l u ρ _).symm.trans_lt hx)
  obtain ⟨c, z₁, z₂, h⟩ := exists_of_mem_ball_small hl u h0 h1 m n hb
  have hn : (l : A) ∈ nonZeroDivisors A := mem_nonZeroDivisors_iff_left.2 ht
  have hi : Function.Injective (algebraMap A (PreDisc l u ρ)) :=
    IsLocalization.injective (M := Submonoid.powers (l : A)) _ (Submonoid.powers_le.2 hn)
  rw [← map_mul] at h
  have h2 := hi h
  have key : ∀ (c : ℕ) (w : A), u ^ m ∣ (l : A) ^ c * w → u ^ m ∣ w := fun c => by
    induction c with
    | zero => intro w hw; simpa using hw
    | succ c ih =>
      rintro w ⟨y, hy⟩
      exact ih w (hd _ y (by rw [← hy]; ring))
  obtain ⟨z, hz⟩ := key c (x - (l : A) ^ n * z₂) ⟨z₁, by rw [pow_add] at h2; linear_combination h2⟩
  exact ⟨z, z₂, by linear_combination hz⟩

theorem BK.X_pow_natDegree_mem_J {l : ℕ} [Fact l.Prime] {K : FinExt l} (bk : BK K) :
    (X : bk.S) ^ bk.Ep.natDegree ∈ bk.J := by
  have h := congrArg (Polynomial.coeToPowerSeries.ringHom (R := Wq l bk.a)) bk.monic.as_sum
  simp only [map_add, map_pow, map_sum, map_mul, Polynomial.coeToPowerSeries.ringHom_apply, Polynomial.coe_X,
    Polynomial.coe_C] at h
  have e : (X : bk.S) ^ bk.Ep.natDegree =
      bk.E - ∑ i ∈ Finset.range bk.Ep.natDegree, C (bk.Ep.coeff i) * (X : bk.S) ^ i := by
    rw [eq_sub_iff_add_eq]; exact h.symm
  rw [e]
  refine sub_mem (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _)) (Ideal.mem_sup_left (sum_mem fun i hi => ?_))
  obtain ⟨w, hw⟩ := bk.dvd_coeff i (Finset.mem_range.1 hi)
  rw [hw, map_mul, map_natCast, mul_assoc]
  exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)

theorem mem_J_pow_of_norm_le : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (A : Type) [CommRing A] (s : bk.S →+* A), (∀ x : A, (l : A) * x = 0 → x = 0) → (∀ (m : ℕ) (x y : A), (l : A) * x = s X ^ m * y → s X ^ m ∣ x) → ∀ (ρ : ℝ≥0), 0 < ρ → ρ < 1 → ∀ n : ℕ, ∃ r : ℝ, 0 < r ∧ ∀ x : A, ‖toDisc l (s X) ρ x‖ ≤ r → x ∈ (bk.J ^ n).map s := by
  intro l hl K bk A _ s ht hd ρ h0 h1 n
  have hl0 : (0 : ℝ) < l := Nat.cast_pos.2 hl.out.pos
  have hρ0 : (0 : ℝ) < ρ := h0
  have hr : 0 < (ρ : ℝ) ^ (bk.Ep.natDegree * n) / (l : ℝ) ^ n := by positivity
  refine ⟨_, half_pos hr, fun x hx => ?_⟩
  obtain ⟨z₁, z₂, rfl⟩ := exists_of_norm_toDisc_lt hl.out.one_lt (s X) ht _ (hd _) h0 h1 n x
    (hx.trans_lt (half_lt_self hr))
  refine add_mem (Ideal.mul_mem_right _ _ ?_) (Ideal.mul_mem_right _ _ ?_)
  · rw [← map_pow, pow_mul]
    exact Ideal.mem_map_of_mem _ (Ideal.pow_mem_pow bk.X_pow_natDegree_mem_J n)
  · rw [← map_natCast s, ← map_pow]
    exact Ideal.mem_map_of_mem _ (Ideal.pow_mem_pow (Ideal.mem_sup_left (Ideal.mem_span_singleton_self _)) n)

end GlobalTheory.BSP
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemMaxUnramifiedOfCrystallineRatio
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct
open scoped Formalism.Per

namespace GlobalTheory.FracAlg

theorem ratio_adjoin {k Ω B D : Type} [Field k] [Field Ω] [Algebra k Ω] [CommRing B] [CommRing D] [IsDomain D]
    (ι : B →+* D) (hι : Function.Injective ι) (o : Ω →+* D)
    (hk : ∀ c : k, ∃ b : B, ι b = o (algebraMap k Ω c)) (x : Ω)
    (hx : ∃ a b : B, b ≠ 0 ∧ ι a = o x * ι b) (y : Ω) (hy : y ∈ IntermediateField.adjoin k {x}) :
    ∃ a b : B, b ≠ 0 ∧ ι a = o y * ι b := by
  have hne : ∀ b : B, b ≠ 0 → ι b ≠ 0 := fun b hb h => hb (hι (by rw [h, map_zero]))
  have hmul : ∀ b b' : B, b ≠ 0 → b' ≠ 0 → b * b' ≠ 0 := fun b b' hb hb' h =>
    mul_ne_zero (hne b hb) (hne b' hb') (by rw [← map_mul, h, map_zero])
  have h1 : (1 : B) ≠ 0 := fun h => one_ne_zero (α := D) (by rw [← map_one ι, h, map_zero])
  induction hy using IntermediateField.adjoin_induction with
  | mem z hz => rw [Set.mem_singleton_iff.1 hz]; exact hx
  | algebraMap c =>
    obtain ⟨b, hb⟩ := hk c
    exact ⟨b, 1, h1, by rw [hb, map_one, mul_one]⟩
  | add z w _ _ hz hw =>
    obtain ⟨a, b, hb, e⟩ := hz
    obtain ⟨a', b', hb', e'⟩ := hw
    refine ⟨a * b' + a' * b, b * b', hmul _ _ hb hb', ?_⟩
    simp only [map_add, map_mul, e, e']
    ring
  | inv z _ hz =>
    obtain ⟨a, b, hb, e⟩ := hz
    by_cases h0 : z = 0
    · exact ⟨0, 1, h1, by simp [h0]⟩
    · have ho : o z ≠ 0 := by simpa using h0
      refine ⟨b, a, fun h => mul_ne_zero ho (hne b hb) (by rw [← e, h, map_zero]), ?_⟩
      rw [e, ← mul_assoc, ← map_mul, inv_mul_cancel₀ h0, map_one, one_mul]
  | mul z w _ _ hz hw =>
    obtain ⟨a, b, hb, e⟩ := hz
    obtain ⟨a', b', hb', e'⟩ := hw
    refine ⟨a * a', b * b', hmul _ _ hb hb', ?_⟩
    simp only [map_mul, e, e']
    ring

section
set_option allowUnsafeReducibility true in
attribute [local irreducible] Per.Acris Per.Bcris

open GlobalTheory.MemLoc in

theorem norm_of_ratio {l : ℕ} [Fact l.Prime] (C : Core l) (a b : Per.Bcris l) (x : Om l) (hb : b ≠ 0)
    (hx : x ≠ 0) (e : C.ι a = C.oD x * C.ι b) : ∃ k : ℤ, ‖x‖ = (l : ℝ) ^ k := by
  obtain ⟨r, a', ha'⟩ := bcris_eq_acris_localization_periodT_alt l C a
  obtain ⟨s, b', hb'⟩ := bcris_eq_acris_localization_periodT_alt l C b
  have hu := (core_t_unit_fil l C).1
  have hA : algebraMap (Per.Acris l) (Per.Bcris l) (a' * C.t ^ s) =
      a * algebraMap (Per.Acris l) (Per.Bcris l) C.t ^ (r + s) := by
    rw [map_mul, map_pow, ← ha', pow_add, mul_assoc]
  have hB : algebraMap (Per.Acris l) (Per.Bcris l) (b' * C.t ^ r) =
      b * algebraMap (Per.Acris l) (Per.Bcris l) C.t ^ (r + s) := by
    rw [map_mul, map_pow, ← hb', add_comm r s, pow_add, mul_assoc]
  refine GlobalTheory.MemLoc.GaussCore.norm_eq_zpow l C (a' * C.t ^ s) (b' * C.t ^ r) x (fun h => hb ?_) hx ?_
  · rw [h, map_zero] at hB
    exact ((hu.pow _).mul_left_eq_zero).1 hB.symm
  · apply (BdRField.bdR_isField l).2.1
    rw [map_mul (algebraMap (Per.BdRp l) (Per.BdR l)), ← C.ι_j, ← C.ι_j, hA, hB, map_mul C.ι, map_mul C.ι, e,
      mul_assoc]
    rfl

end

theorem mem_Kur_of_ratio : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI →
    ∀ (a b : P.R.B) (x : Om l), b ≠ 0 → P.ιB a = algebraMap (Om l) P.R.BdR x * P.ιB b → x ∈ MaximalUnramifiedExtension l := by
  intro l _ P AI T a b x hb e
  obtain ⟨C, hC⟩ := GlobalTheory.MemLoc.FitsEx.exists_fits l P AI T
  obtain ⟨hF, -, hinj, -⟩ := GlobalTheory.Per.TiedField.tied_field l P AI T
  have : IsDomain P.R.BdR := hF.isDomain
  have hint : IsIntegral ℚ_[l] x := Algebra.IsIntegral.isIntegral _
  refine GlobalTheory.UnramValue.le_Kur_of_norm l ⟨IntermediateField.adjoin ℚ_[l] {x}, IntermediateField.adjoin.finiteDimensional hint⟩
    (fun y hy hy0 => ?_) (IntermediateField.mem_adjoin_simple_self ℚ_[l] x)
  obtain ⟨a', b', hb', e'⟩ := ratio_adjoin (k := ℚ_[l]) (P.ιB : P.R.B →+* P.R.BdR) hinj
    (algebraMap (Om l) P.R.BdR)
    (fun c => ⟨algebraMap ℚ_[l] P.R.B c,
      (P.ιB.commutes c).trans (IsScalarTower.algebraMap_apply ℚ_[l] (Om l) P.R.BdR c)⟩) x ⟨a, b, hb, e⟩ y hy
  refine norm_of_ratio C (T.eB a') (T.eB b') y (fun h => hb' (T.eB.injective (h.trans (map_zero _).symm))) hy0 ?_
  rw [← hC.ι, ← hC.ι, ← hC.o, ← map_mul]
  exact congrArg T.eD e'

end GlobalTheory.FracAlg
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NatInvIsoOfLocalTateDualityCyclotomicTwist
section
open ReciprocityTheory.Gal Formalism.RepresentationBoundsCohomology.LOC ReciprocityTheory.ChartRestriction.T2 GlobalTheory.FunctorialityH2

namespace GlobalTheory

theorem natInvIso_of_localTateDuality (hT : Formalism.GaloisCohomology.LocalTateDualityK) : NatInvIso := by
  intro p _ K O _ _ _ _ G _ _ hK hO i ε hε
  haveI := hO.ring; haveI := hO.compact; haveI := hO.t2
  obtain ⟨z, hz⟩ := GlobalTheory.T.exists_generator_H2_twist hT hK hO i hε
  have hq := GlobalTheory.T.every_generator_H2_twist hT hK hO i hε z hz
  have hbij : ∀ (M : Type) [AddCommGroup M] [Module O M] [TopologicalSpace M] [IsTopologicalAddGroup M]
      [ContinuousConstSMul O M] [ContinuousSMul O M] [T2Space M] [Module.Finite O M],
      Function.Bijective (phi ε z M) := by
    intro M _ _ _ _ _ _ _ _
    obtain ⟨n, m, e, ⟨E⟩⟩ := GlobalTheory.T.exists_equiv_dvr_fg_module_structure (O := O) M
    refine bijective_of_retract ε z M (fun _ : Fin n => O) (fun i : Fin m => O ⧸ IsLocalRing.maximalIdeal O ^ e i)
      (fun j => LinearMap.proj j ∘ₗ LinearMap.fst O _ _ ∘ₗ E.toLinearMap)
      (fun j => E.symm.toLinearMap ∘ₗ LinearMap.inl O _ _ ∘ₗ LinearMap.single O (fun _ : Fin n => O) j)
      (fun i => LinearMap.proj i ∘ₗ LinearMap.snd O _ _ ∘ₗ E.toLinearMap)
      (fun i => E.symm.toLinearMap ∘ₗ LinearMap.inr O _ _ ∘ₗ
        LinearMap.single O (fun i : Fin m => O ⧸ IsLocalRing.maximalIdeal O ^ e i) i)
      (fun j => GlobalTheory.T.continuous_linearMap_of_finite _) (fun j => GlobalTheory.T.continuous_linearMap_of_finite _) (fun i => GlobalTheory.T.continuous_linearMap_of_finite _) (fun i => ?_) ?_
      (fun j => ?_) (fun i => hq (e i))
    · have := GlobalTheory.T.continuous_linearMap_of_finite (M := O) (M' := M) ((E.symm.toLinearMap ∘ₗ LinearMap.inr O _ _ ∘ₗ
        LinearMap.single O (fun i : Fin m => O ⧸ IsLocalRing.maximalIdeal O ^ e i) i) ∘ₗ
          (IsLocalRing.maximalIdeal O ^ e i).mkQ)
      exact (Submodule.isOpenQuotientMap_mkQ _).isQuotientMap.continuous_iff.2 this
    · intro x
      conv_rhs => rw [← E.symm_apply_apply x]
      simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply, ← map_sum, ← map_add]
      congr 1
      ext <;> simp [Finset.univ_sum_single]
    · show Function.Bijective (phi ε z O)
      rw [show ⇑(phi ε z O) = fun a : O => a • z from funext (phi_self ε z)]
      exact hz
  refine ⟨⟨fun M _ _ _ _ _ h => by
      haveI := h.csmul; haveI := h.t2; haveI := h.fg
      exact (LinearEquiv.ofBijective (phi ε z M) (hbij M)).symm, ?_⟩⟩
  intro M M' _ _ _ _ _ _ _ _ _ _ h h' f hf w
  haveI := h.csmul; haveI := h.t2; haveI := h.fg
  haveI := h'.csmul; haveI := h'.t2; haveI := h'.fg
  obtain ⟨m, rfl⟩ := (hbij M).2 w
  show (LinearEquiv.ofBijective (phi ε z M') (hbij M')).symm _ =
    f ((LinearEquiv.ofBijective (phi ε z M) (hbij M)).symm _)
  rw [phi_natural ε z M M' f hf (twist_map ε f) m]
  rw [LinearEquiv.ofBijective_symm_apply_apply, LinearEquiv.ofBijective_symm_apply_apply]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NoInvDualOfSetup
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys GlobalTheory.SelFun GlobalTheory.Published GlobalTheory.ResSel GlobalTheory.StepTwo GlobalTheory.TwistDet GlobalTheory.NewPrime GlobalTheory.Published.PoitouTate

namespace GlobalTheory.NewPrime

open IsLocalRing GlobalTheory.ScalarFrob in

theorem noInvDual_of_setup : ∀ (D : Formalism.BasicNotions.D7) (N : NData D.R D.host D.what₂) (X : NTw D.R D.host D.what₂ D.LL0 N) (bkP : BKPh X) (i : X.Tw) (s : X.Sig i), ∀ (A : Type) [CommRing A] [IsLocalRing A] [Finite A] [Algebra (X.O0 i) A] (κ : GE N →* Aˣ) (Q : Finset (PlE D.host)) (ρ : GE N →* GL (Fin D.R.r) (X.O0 i)) (z : GE N), Setup bkP i s κ Q → IsDual i s ρ → IsTameInertiaElementAtTwistPrime X i z → NoInvDual i κ ρ := by
  intro D N X bkP i s A _ _ _ _ κ Q ρ z hS hρ hz Y' _ _ m hm
  obtain ⟨h, hloc, -, -, hκ, -⟩ := hS
  obtain ⟨e, he, -, hu, hε⟩ := GlobalTheory.TwSys.TameScalar.exists_scalar_tmat_of_tame_inertia D N X bkP i s z h.1 hz
  have c0 : residue (X.O0 i) e ≠ 0 := (residue_ne_zero_iff_isUnit _).2 e.isUnit
  have c1 : residue (X.O0 i) e ≠ 1 := by
    rw [← residue_ne_zero_iff_isUnit, map_sub, map_one, sub_ne_zero] at hu
    exact hu
  have e1 : resT i s z = residue (X.O0 i) e • 1 := by
    rw [resT_apply, he]
    ext a b
    by_cases hab : a = b <;> simp [hab]
  have e2 := dual_of_scalar i s (by rw [hε]; simp) c0 e1
  rw [← hρ z] at e2
  have hκ' : ∃ n : ℕ, κ⁻¹ z ^ (X.l i ^ n) = 1 := by
    obtain ⟨n, hn⟩ := hκ z
    exact ⟨n, by rw [MonoidHom.inv_apply, inv_pow, hn, inv_one]⟩
  exact eq_zero_of_scalar Fact.out (GlobalTheory.PrimeToInertia.l_mem i) ρ κ⁻¹ hκ' (inv_ne_one.2 c1) e2 (q := 1) Nat.cast_one m
    (by rw [one_smul]; exact hm z)

end GlobalTheory.NewPrime
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormBaseRingToClosedDiscJPowSmall
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

noncomputable section

namespace GlobalTheory.BSP.DiscSmall

def ballIdeal (l : ℕ) {A : Type} [CommRing A] (u : A) (ρ : ℝ≥0) (r : ℝ) : Ideal A :=
  Submodule.comap (Algebra.linearMap A (PreDisc l u ρ)) (ball l u ρ r)

theorem mem_ballIdeal {l : ℕ} {A : Type} [CommRing A] {u : A} {ρ : ℝ≥0} {r : ℝ} {x : A} :
    x ∈ ballIdeal l u ρ r ↔ algebraMap A (PreDisc l u ρ) x ∈ ball l u ρ r := Iff.rfl

theorem ballIdeal_mul_le {l : ℕ} {A : Type} [CommRing A] {u : A} {ρ : ℝ≥0} {r s : ℝ} (hr : 0 ≤ r) :
    ballIdeal l u ρ r * ballIdeal l u ρ s ≤ ballIdeal l u ρ (r * s) :=
  Ideal.mul_le.2 fun x hx y hy => by
    rw [mem_ballIdeal, map_mul]
    exact mul_mem_ball l u ρ hr hx hy

theorem pow_le_ballIdeal {l : ℕ} {A : Type} [CommRing A] {u : A} {ρ : ℝ≥0} {r : ℝ} (hr : 0 ≤ r)
    {I : Ideal A} (hI : I ≤ ballIdeal l u ρ r) : ∀ n : ℕ, I ^ n ≤ ballIdeal l u ρ (r ^ n)
  | 0 => by
    rw [pow_zero, pow_zero, Ideal.one_eq_top]
    refine (Ideal.eq_top_of_isUnit_mem _ ?_ isUnit_one).ge
    rw [mem_ballIdeal, map_one]
    exact Submodule.subset_span ⟨0, 0, 0, by simp, by simp⟩
  | n + 1 => by
    rw [pow_succ, pow_succ]
    exact (Ideal.mul_mono (pow_le_ballIdeal hr hI n) hI).trans (ballIdeal_mul_le (pow_nonneg hr n))

theorem exists_E_eq {l : ℕ} [Fact l.Prime] {K : FinExt l} (bk : BK K) :
    ∃ q : bk.S, bk.E = (X : bk.S) ^ bk.Ep.natDegree + (l : bk.S) * q := by
  have hd : Polynomial.C (l : Wq l bk.a) ∣ bk.Ep - Polynomial.X ^ bk.Ep.natDegree := by
    refine (Polynomial.C_dvd_iff_dvd_coeff _ _).2 fun i => ?_
    rw [Polynomial.coeff_sub, Polynomial.coeff_X_pow]
    rcases lt_trichotomy i bk.Ep.natDegree with h | h | h
    · rw [if_neg h.ne, sub_zero]; exact bk.dvd_coeff i h
    · rw [h, if_pos rfl, bk.monic.coeff_natDegree, sub_self]; exact dvd_zero _
    · rw [if_neg h.ne', sub_zero, Polynomial.coeff_eq_zero_of_natDegree_lt h]; exact dvd_zero _
  obtain ⟨q, hq⟩ := hd
  have h2 : bk.Ep = Polynomial.X ^ bk.Ep.natDegree + Polynomial.C (l : Wq l bk.a) * q := by
    rw [← hq]; ring
  refine ⟨(q : bk.S), ?_⟩
  show ((bk.Ep : Polynomial (Wq l bk.a)) : (Wq l bk.a)⟦X⟧) = _
  nth_rewrite 1 [h2]
  simp [Polynomial.coe_add, Polynomial.coe_pow, Polynomial.coe_X, Polynomial.coe_mul, Polynomial.coe_C]
  left
  exact map_natCast (Polynomial.coeToPowerSeries.ringHom (R := Wq l bk.a)) l

end GlobalTheory.BSP.DiscSmall

open GlobalTheory.BSP.DiscSmall in

theorem GlobalTheory.BSP.norm_toDisc_J_pow_small : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (A : Type) [CommRing A]
    (s : bk.S →+* A) (ρ : ℝ≥0), 0 < ρ → ρ < 1 → ∀ r : ℝ, 0 < r → ∃ n : ℕ, ∀ x ∈ (bk.J ^ n).map s,
    ‖toDisc l (s X) ρ x‖ ≤ r := by
  intro l hl K bk A _ s ρ hρ0 hρ1 r hr
  have hl0 : (0 : ℝ) < l := Nat.cast_pos.2 hl.out.pos
  have hl1 : (1 : ℝ) < l := Nat.one_lt_cast.2 hl.out.one_lt
  set t : ℝ := max (1 / (l : ℝ)) ((ρ : ℝ) ^ bk.Ep.natDegree) with ht
  have ht0 : 0 < t := lt_max_of_lt_left (one_div_pos.2 hl0)
  have hρ1' : (ρ : ℝ) < 1 := by exact_mod_cast hρ1
  have ht1 : t < 1 := max_lt ((div_lt_one hl0).2 hl1) (pow_lt_one₀ ρ.2 hρ1' bk.deg_pos.ne')
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hr ht1
  have hlmem : algebraMap A (PreDisc l (s X) ρ) (l : A) ∈ ball l (s X) ρ t := by
    refine Submodule.subset_span ⟨1, 0, 0, ?_, by simp⟩
    have : 1 / (l : ℝ) * l ≤ t * l := mul_le_mul_of_nonneg_right (le_max_left _ _) hl0.le
    rw [one_div_mul_cancel hl0.ne'] at this
    simpa using this
  have hJ : bk.J.map s ≤ ballIdeal l (s X) ρ t := by
    rw [Ideal.map_sup, Ideal.map_span, Ideal.map_span, Set.image_singleton, Set.image_singleton, sup_le_iff,
      Ideal.span_le, Ideal.span_le, Set.singleton_subset_iff, Set.singleton_subset_iff]
    constructor
    · show s (l : bk.S) ∈ ballIdeal l (s X) ρ t
      rw [map_natCast, mem_ballIdeal]
      exact hlmem
    · show s bk.E ∈ ballIdeal l (s X) ρ t
      obtain ⟨q, hq⟩ := exists_E_eq bk
      rw [hq, map_add, map_mul, map_pow, map_natCast, mem_ballIdeal, map_add, map_mul, mul_comm, ← Algebra.smul_def]
      refine add_mem (Submodule.subset_span ⟨0, bk.Ep.natDegree, 0, ?_, by simp⟩) (Submodule.smul_mem _ _ hlmem)
      show (l:ℝ)^0 * (ρ:ℝ)^bk.Ep.natDegree ≤ t * (l:ℝ)^0
      simp only [pow_zero, one_mul, mul_one]
      exact le_max_right _ _
  refine ⟨n, fun x hx => ?_⟩
  rw [Ideal.map_pow] at hx
  have hx' := pow_le_ballIdeal ht0.le hJ n hx
  rw [toDisc, RingHom.comp_apply, norm_ofPre]
  exact (gauge_le l (s X) ρ (pow_pos ht0 n) hx').trans hn.le
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PairingEquivariant
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys GlobalTheory.SelFun GlobalTheory.Published GlobalTheory.ResSel GlobalTheory.StepTwo GlobalTheory.TwistDet GlobalTheory.NewPrime GlobalTheory.Published.PoitouTate

namespace GlobalTheory.NewPrime.PairEquiv

section General

variable {A : Type} [CommRing A] {Y Y' : Type} [AddCommGroup Y] [Module A Y] [AddCommGroup Y'] [Module A Y'] {n r : ℕ}

theorem vecPair_matAct {β : Y →+ Y' →+ ZMod n} (hβ : Bal A β) (T : Matrix (Fin r) (Fin r) A) (x : Fin r → Y)
    (y : Fin r → Y') : vecPair r β (matAct T x) y = vecPair r β x (matAct T.transpose y) := by
  rw [vecPair_apply, vecPair_apply]
  change ∑ c, β (∑ a, T c a • x a) (y c) = ∑ a, β (x a) (∑ c, T c a • y c)
  simp only [map_sum, AddMonoidHom.finsetSum_apply]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun c _ => hβ _ _ _

theorem vecPair_smul {β : Y →+ Y' →+ ZMod n} (hβ : Bal A β) (k : A) (x : Fin r → Y)
    (y : Fin r → Y') : vecPair r β (k • x) y = vecPair r β x (k • y) := by
  rw [vecPair_apply, vecPair_apply]
  exact Finset.sum_congr rfl fun a _ => hβ _ _ _

theorem tors_of_finite [IsLocalRing A] [Finite A] (b : Y) :
    ∃ m, ∀ x ∈ IsLocalRing.maximalIdeal A ^ m, x • b = 0 := by
  obtain ⟨m, hm⟩ := IsArtinianRing.isNilpotent_jacobson_bot (R := A)
  rw [IsLocalRing.jacobson_eq_maximalIdeal _ bot_ne_top] at hm
  refine ⟨m, fun x hx => ?_⟩
  rw [hm, Ideal.zero_eq_bot, Ideal.mem_bot] at hx
  rw [hx, zero_smul]

theorem map_padicInt_eq_val {l : ℕ} [Fact l.Prime] (f : ℤ_[l] →+* A) {m : ℕ} (h : (l : A) ^ m = 0) (a : ℤ_[l]) :
    f a = ((PadicInt.toZModPow m a).val : A) := by
  have h1 : a - ((PadicInt.toZModPow m a).val : ℤ_[l]) ∈ RingHom.ker (PadicInt.toZModPow m) := by
    rw [RingHom.mem_ker, map_sub, map_natCast, ZMod.natCast_zmod_val, sub_self]
  rw [PadicInt.ker_toZModPow, Ideal.mem_span_singleton] at h1
  obtain ⟨c, hc⟩ := h1
  have h2 := congrArg f hc
  rw [map_sub, map_natCast, map_mul, map_pow, map_natCast, h, zero_mul, sub_eq_zero] at h2
  exact h2

end General

variable {D : Formalism.BasicNotions.D7} {N : NData D.R D.host D.what₂} {X : NTw D.R D.host D.what₂ D.LL0 N}

theorem transpose_mul_Tdual (i : X.Tw) (s : X.Sig i) (g : GE N) :
    (Tmat i s g).transpose * Tdual i s g = ((eps0 X i g : (X.O0 i)ˣ) : X.O0 i) • 1 := by
  have h3 : IsUnit (Tmat i s g).det := by
    rw [← Tgl_coe]; exact Matrix.isUnits_det_units _
  rw [Tdual, Matrix.mul_smul, ← Matrix.transpose_mul, Matrix.nonsing_inv_mul _ h3, Matrix.transpose_one]

theorem pairing_equivariant : ∀ (D : Formalism.BasicNotions.D7) (N : NData D.R D.host D.what₂) (X : NTw D.R D.host D.what₂ D.LL0 N) (bkP : BKPh X) (i : X.Tw) (s : X.Sig i), ∀ (A : Type) [CommRing A] [IsLocalRing A] [Finite A] [Algebra (X.O0 i) A] (κ : GE N →* Aˣ) (Q : Finset (PlE D.host)) (ρ : GE N →* GL (Fin D.R.r) (X.O0 i)), Setup bkP i s κ Q → Kills i A → IsDual i s ρ → ∀ (Y : Type) [AddCommGroup Y] [Module A Y] [TopologicalSpace Y] [DiscreteTopology Y] (Y' : Type) [AddCommGroup Y'] [Module A Y'] [TopologicalSpace Y'] [DiscreteTopology Y'] (β : Y →+ Y' →+ ZMod (X.l i ^ (nu X i + 1))), Bal A β → ContAction (repOn (Tgl i s) κ Y) ∧ ContAction (repOn ρ κ⁻¹ Y') ∧ (∀ g x y, vecPair D.R.r β (repOn (Tgl i s) κ Y g x) (repOn ρ κ⁻¹ Y' g y) = ((cycMod D.host.E N.Om (X.l i) (nu X i + 1) g : (ZMod (X.l i ^ (nu X i + 1)))ˣ) : ZMod (X.l i ^ (nu X i + 1))) * vecPair D.R.r β x y) ∧ ∀ v, v ∉ placesOver D.host.E (X.l i) → v ∉ Spl i → v ∉ Q → ∀ B : ValuationSubring N.Om, IsPlaceOver B v → ∀ τ ∈ Ine (F := D.host.E) B, repOn (Tgl i s) κ Y τ = 1 ∧ repOn ρ κ⁻¹ Y' τ = 1 := by
  intro D N X bkP i s A _ _ _ _ κ Q ρ hS hK hρ Y _ _ _ _ Y' _ _ _ _ β hβ
  have := hS.2.1
  have hκ := hS.2.2.2.1
  refine ⟨?_, ?_, fun g x y => ?_, fun v hl hv hQ B hB τ hτ => ?_⟩
  · refine GlobalTheory.PrimeToInertia.contAction_repOn (X.twistBaseCoefficientRing_isAdic i) _ ?_ κ hκ tors_of_finite
    simp_rw [Tgl_coe]; exact GlobalTheory.PrimeToInertia.continuous_Tmat i s
  · refine GlobalTheory.PrimeToInertia.contAction_repOn (X.twistBaseCoefficientRing_isAdic i) _ ?_ κ⁻¹ ?_ tors_of_finite
    · simp_rw [hρ _]; exact GlobalTheory.PrimeToInertia.continuous_Tdual i s
    · convert hκ using 2
      ext g
      simp [MonoidHom.mem_ker]
  · have hl : ((X.l i : ℕ) : A) ^ (nu X i + 1) = 0 := by
      have := hK ((X.l i : X.O0 i) ^ nu X i * (X.l i : X.O0 i))
        (Ideal.mul_mem_mul (Ideal.mem_span_singleton_self _) (GlobalTheory.PrimeToInertia.l_mem i))
      rwa [map_mul, map_pow, map_natCast, ← pow_succ] at this
    have he : algebraMap (X.O0 i) A ((eps0 X i g : (X.O0 i)ˣ) : X.O0 i) =
        (((cycMod D.host.E N.Om (X.l i) (nu X i + 1) g : (ZMod (X.l i ^ (nu X i + 1)))ˣ) : ZMod (X.l i ^ (nu X i + 1))).val : A) :=
      map_padicInt_eq_val ((algebraMap (X.O0 i) A).comp (algebraMap ℤ_[X.l i] (X.O0 i))) hl _
    change vecPair _ β ((κ g : A) • matAct ((Tgl i s g : Matrix _ _ (X.O0 i)).map (algebraMap (X.O0 i) A)) x)
      (((κ g)⁻¹ : Aˣ).val • matAct ((ρ g : Matrix _ _ (X.O0 i)).map (algebraMap (X.O0 i) A)) y) = _
    rw [vecPair_smul hβ, smul_smul, Units.mul_inv, one_smul, vecPair_matAct hβ, ← Module.End.mul_apply, ← matAct_mul,
      ← Matrix.transpose_map, ← Matrix.map_mul, hρ, Tgl_coe, transpose_mul_Tdual]
    have e : matAct ((((eps0 X i g : (X.O0 i)ˣ) : X.O0 i) • (1 : Matrix (Fin D.R.r) (Fin D.R.r) (X.O0 i))).map
        (algebraMap (X.O0 i) A)) y =
        ((cycMod D.host.E N.Om (X.l i) (nu X i + 1) g : (ZMod (X.l i ^ (nu X i + 1)))ˣ) : ZMod (X.l i ^ (nu X i + 1))).val • y := by
      funext a
      rw [← Nat.cast_smul_eq_nsmul A, ← he]
      change ∑ b, algebraMap (X.O0 i) A (((eps0 X i g : (X.O0 i)ˣ) : X.O0 i) * (1 : Matrix (Fin D.R.r) (Fin D.R.r) (X.O0 i)) a b) • y b = _
      simp [Matrix.one_apply, apply_ite (algebraMap (X.O0 i) A), ite_smul]
    rw [e, map_nsmul, nsmul_eq_mul, ZMod.natCast_zmod_val]
  · have h1 := GlobalTheory.SelFun.Colim.tgl_eq_one bkP i s hS.1.1 v hl hv B hB τ hτ
    have h2 := hS.2.2.2.2.2.2.2 v hQ B hB τ hτ
    have h3 : cycZ D.host.E N.Om (X.l i) τ = 1 := by
      refine Units.ext (PadicInt.ext_of_toZModPow.mp fun n => ?_)
      rw [cycZ_toZModPow_eq hl hB (q := 1) (fun x hx => by simpa using hτ.2 x hx) n]
      simp
    have h4 : eps0 X i τ = 1 := by
      rw [eps0, MonoidHom.comp_apply, h3, map_one]
    have h5 : ρ τ = 1 := by
      apply Units.ext
      rw [hρ, Tdual, h4, ← Tgl_coe, h1]
      simp
    exact ⟨LinearMap.ext (GlobalTheory.SelFun.Colim.repOn_eq_of_eq_one _ _ h1 h2),
      LinearMap.ext (GlobalTheory.SelFun.Colim.repOn_eq_of_eq_one _ _ h5 (by simp [h2]))⟩

end GlobalTheory.NewPrime.PairEquiv
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PrimePowInvSmulLiftMemDivisibleCocyclesStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.primePow_inv_smul_lift_mem_divisible_cocycles : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (LL : Type) [Field LL] [Algebra ℚ_[l] LL] [TopologicalSpace LL] (O : Type) [CommRing O] [Algebra O LL], GoodO (Qp := ℚ_[l]) LL O → ∀ (A' : GRep ↥(GK K) ℚ_[l] LL O) (LA' : Lattice (O := O) A'.ρ) (r : ℕ) (hI' : StableSub LA' (Ideal.span {((l : ℕ) : O) ^ r} • ⊤ : Submodule O ↥LA'.T)) (c' : ↥(quotientCocycles LA' _ hI')), (fun g => (Submodule.Quotient.mk ((((l : ℕ) : LL) ^ r)⁻¹ • Formalism.MainNotions.LocalSituation.liftQ LA' _ ((c' : ↥(GK K) → ↥LA'.T ⧸ (Ideal.span {((l : ℕ) : O) ^ r} • ⊤ : Submodule O ↥LA'.T)) g)) : A'.V ⧸ LA'.T)) ∈ divisibleCocycles LA' := by
  first | exact @GlobalTheory.DivLift.pow_inv_smul_liftQ_mem_Z1D | exact GlobalTheory.DivLift.pow_inv_smul_liftQ_mem_Z1D | (intros; apply GlobalTheory.DivLift.pow_inv_smul_liftQ_mem_Z1D <;> assumption)
end

