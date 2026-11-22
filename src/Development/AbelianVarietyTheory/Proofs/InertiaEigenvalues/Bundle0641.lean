import Mathlib
import GroundTheory.GlobalFields.IdeleGroups.NormOneCompact
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0071
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsHasCentChar
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsUnitaryOfCharIff
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0002
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0954
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.EmbedsLevelZeroDepthZero
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0011
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0117
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0133
import Development.AbelianVarietyTheory.CrystallinePeriods.RingIface
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0635
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0361
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0340
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0335
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0631
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0017
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.OneSubPhiOntoOfFilZero
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0005
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0006
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteStableLatticesDifferenceTermNeZero
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnitLemmaGroup
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0002
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0075
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Formalism.SharpRestriction.LevelLetterCocycles.PairedCharacterCondition
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0632
import Formalism.SharpRestriction.LevelLetterCocycles.DecompositionData
import Formalism.SharpRestriction.SmoothDesignExistence.ContinuousHom

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIsUnitaryTwistAbsPow
section
noncomputable section

open NumberField IsDedekindDomain Formalism.L2.Host GroundTheory.Global

namespace GlobalTheory.AbsTwist

variable {F : Type} [Field F] [NumberField F]

theorem eq_zero_of_normOne (f : IdeleGroup F → ℝ) (hc : Continuous f) (hm : ∀ x y, f (x * y) = f x + f y)
    (hk : ∀ k, f (IdeleGroup.diagonal F k) = 0) (x : IdeleGroup F) (hx : x ∈ IdeleGroup.normOneSubgroup F) :
    f x = 0 := by
  obtain ⟨D, hD, -, hxD⟩ := IdeleGroup.exists_isCompact_normOneSubgroup F
  obtain ⟨C, hC⟩ := hD.exists_bound_of_continuousOn hc.continuousOn
  have h1 : f 1 = 0 := by
    have := hm 1 1
    rw [mul_one] at this
    linarith
  have hp : ∀ n : ℕ, f (x ^ n) = n * f x := fun n => by
    induction n with
    | zero => simpa using h1
    | succ n ih => rw [pow_succ, hm, ih]; push_cast; ring
  have hb : ∀ n : ℕ, (n : ℝ) * |f x| ≤ C := fun n => by
    obtain ⟨k, hk'⟩ := hxD _ (pow_mem hx n)
    have := hC _ hk'
    rwa [hm, hk, zero_add, hp, Real.norm_eq_abs, abs_mul, Nat.abs_cast] at this
  by_contra h
  obtain ⟨n, hn⟩ := exists_nat_gt (C / |f x|)
  rw [div_lt_iff₀ (abs_pos.2 h)] at hn
  exact absurd (hb n) (not_le.2 hn)

theorem module_expScalar (t : ℝ) :
    (IdeleGroup.ideleModule F (GlobalTheory.HeckeOne.mixedIdele F (GlobalTheory.HeckeOne.expScalar F t)) : ℝ) =
      Real.exp ((Module.finrank ℚ F : ℝ) * t) :=
  GlobalTheory.HeckeOne.ideleNorm_expScalar F t

theorem exists_eq_mul_log_module (f : IdeleGroup F → ℝ) (hc : Continuous f) (hm : ∀ x y, f (x * y) = f x + f y)
    (hk : ∀ k, f (IdeleGroup.diagonal F k) = 0) :
    ∃ a : ℝ, ∀ x, f x = a * Real.log (IdeleGroup.ideleModule F x : ℝ) := by
  let e : ℝ → IdeleGroup F := fun t => GlobalTheory.HeckeOne.mixedIdele F (GlobalTheory.HeckeOne.expScalar F t)
  have hadd : ∀ s t, f (e (s + t)) = f (e s) + f (e t) := fun s t => by
    simp only [e]
    rw [GlobalTheory.HeckeOne.expScalar_add, map_mul, hm]
  have hcont : Continuous fun t => f (e t) :=
    hc.comp ((GlobalTheory.HeckeOne.continuous_mixedIdele F).comp (GlobalTheory.HeckeOne.continuous_expScalar F))
  have hn : (Module.finrank ℚ F : ℝ) ≠ 0 := by exact_mod_cast Module.finrank_pos.ne'
  refine ⟨f (e 1) / Module.finrank ℚ F, fun x => ?_⟩
  set t : ℝ := Real.log (IdeleGroup.ideleModule F x : ℝ) / Module.finrank ℚ F with ht
  have h1 := map_real_smul (AddMonoidHom.mk' (fun t => f (e t)) hadd) hcont t 1
  simp only [smul_eq_mul, mul_one, AddMonoidHom.mk'_apply] at h1
  have h2 : IdeleGroup.ideleModule F (e t) = IdeleGroup.ideleModule F x := Subtype.ext (by
    have h3 := module_expScalar (F := F) t
    rw [ht, mul_div_cancel₀ _ hn, Real.exp_log (IdeleGroup.ideleModule F x).2] at h3
    exact h3)
  have h4 : (e t)⁻¹ * x ∈ IdeleGroup.normOneSubgroup F := by
    rw [IdeleGroup.normOneSubgroup, MonoidHom.mem_ker, map_mul, map_inv, h2, inv_mul_cancel]
  have h5 := hm (e t) ((e t)⁻¹ * x)
  rw [mul_inv_cancel_left, eq_zero_of_normOne f hc hm hk _ h4, add_zero, h1, ht] at h5
  rw [h5]; ring

open GlobalTheory.Mem.Chr.CharModel in

theorem exists_norm_eq_exp (ω : HChar F) :
    ∃ c : ℝ, ∀ x, ‖((ω.1 x : ℂˣ) : ℂ)‖ = Real.exp (c * logNorm F x) := by
  have h0 : ∀ x, ‖((ω.1 x : ℂˣ) : ℂ)‖ ≠ 0 := fun x => norm_ne_zero_iff.2 (Units.ne_zero _)
  obtain ⟨a, ha⟩ := exists_eq_mul_log_module (F := F) (fun x => Real.log ‖((ω.1 x : ℂˣ) : ℂ)‖)
    ((Units.continuous_val.comp ω.2.1).norm.log h0)
    (fun x y => by rw [map_mul, Units.val_mul, norm_mul, Real.log_mul (h0 x) (h0 y)])
    (fun k => by
      have : ω.1 (IdeleGroup.diagonal F k) = 1 := ω.2.2 k
      rw [this]; simp)
  obtain ⟨b, hb⟩ := exists_eq_mul_log_module (F := F) (logNorm F) (continuous_logNorm F) (logNorm_mul F)
    (logNorm_principal F)
  have hb0 : b ≠ 0 := by
    rintro rfl
    refine absChar_not_unitary (F := F) fun x => ?_
    change ‖Complex.exp (1 * logNorm F x)‖ = 1
    rw [hb]; simp
  refine ⟨a / b, fun x => ?_⟩
  rw [← Real.exp_log (norm_pos_iff.2 (Units.ne_zero (ω.1 x))), ha x, hb x]
  congr 1
  field_simp

end GlobalTheory.AbsTwist

namespace GlobalTheory.CuspRep.CG

open Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR GlobalTheory.Mem.Chr.CharModel GlobalTheory.HeckeGal.Model

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ}

omit [IsTotallyComplex E] in

theorem absPow_val_apply (t : ℝ) (x : Ideles E) :
    (((absPow E t).1 x : ℂˣ) : ℂ) = Complex.exp ((t : ℂ) * logNorm E x) := rfl

omit [IsTotallyComplex E] in

theorem absPow_neg_mul (t : ℝ) : absPow E (-t) * absPow E t = 1 := by
  refine Subtype.ext (MonoidHom.ext fun x => Units.ext ?_)
  change (((absPow E (-t)).1 x : ℂˣ) : ℂ) * (((absPow E t).1 x : ℂˣ) : ℂ) = 1
  rw [absPow_val_apply, absPow_val_apply, ← Complex.exp_add]
  push_cast
  ring_nf
  exact Complex.exp_zero

theorem exists_isUnitary_twist_absPow (π : CG E a) (ha : 1 ≤ a) :
    ∃ (π₀ : CG E a) (t : ℝ), π₀.IsUnitary ∧ π = π₀.twist (absPow E t) := by
  obtain ⟨ω, hω⟩ := GlobalTheory.CuspRep.Central.exists_hasCentChar π
  obtain ⟨c, hc⟩ := GlobalTheory.AbsTwist.exists_norm_eq_exp ω
  have ha' : (a : ℝ) ≠ 0 := by exact_mod_cast (show a ≠ 0 by omega)
  refine ⟨π.twist (absPow E (-(c / a))), c / a, ⟨_, fun x => ?_, hω.twist _⟩, ?_⟩
  · change ‖((ω.1 x : ℂˣ) : ℂ) * ((((absPow E (-(c / a))).1 x) ^ a : ℂˣ) : ℂ)‖ = 1
    rw [Units.val_pow_eq_pow_val, absPow_val_apply, norm_mul, norm_pow, hc x,
      show ((-(c / a) : ℝ) : ℂ) * (logNorm E x : ℂ) = ((-(c / a) * logNorm E x : ℝ) : ℂ) by push_cast; ring,
      Complex.norm_exp_ofReal, ← Real.exp_nat_mul, ← Real.exp_add]
    rw [Real.exp_eq_one_iff]
    field_simp
    ring
  · rw [← twist_mul, absPow_neg_mul, twist_one]

theorem HasSat.twist {π : CG E a} {w : HeightOneSpectrum (𝓞 E)} {B : Multiset ℂˣ} (h : π.HasSat w B)
    {ν : HChar E} (hν : ν.UnrAt w) : (π.twist ν).HasSat w (B.map (· * ν.val w)) := by
  induction π using Quotient.inductionOn
  exact GlobalTheory.SphGal.hasSatGL_twist _ _ _ ν w B hν h

omit [IsTotallyComplex E] in

theorem norm_val_absPow (t : ℝ) (w : HeightOneSpectrum (𝓞 E)) :
    ‖(((absPow E t).val w : ℂˣ) : ℂ)‖ = (Ideal.absNorm w.asIdeal : ℝ) ^ (-t) := by
  have hq : 1 < Ideal.absNorm w.asIdeal := NumberField.HeightOneSpectrum.one_lt_absNorm w
  rw [(absPow_isAbsPow E t).2.1 w, Complex.norm_natCast_cpow_of_pos (zero_lt_one.trans hq), Complex.neg_re,
    Complex.ofReal_re]

theorem HasSat.twist_absPow {π : CG E a} {w : HeightOneSpectrum (𝓞 E)} {B : Multiset ℂˣ} (h : π.HasSat w B)
    (t : ℝ) : (π.twist (absPow E t)).HasSat w (B.map (· * (absPow E t).val w)) ∧
      ‖(((absPow E t).val w : ℂˣ) : ℂ)‖ = (Ideal.absNorm w.asIdeal : ℝ) ^ (-t) :=
  ⟨h.twist ((absPow_isAbsPow E t).1 w), norm_val_absPow t w⟩

end GlobalTheory.CuspRep.CG
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsJLeviMulJPlus
section
noncomputable section

open GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel Matrix

namespace GlobalTheory.LocGL.IwahoriFactor

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {α n : Type} {m : α → Type} [Fintype α] [LinearOrder α] [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)]
  [Fintype n] [DecidableEq n]

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [Fintype α] [LinearOrder α]
  [∀ a, Fintype (m a)] [Fintype n] in

theorem one_same (e : (Σ a, m a) ≃ n) (a : α) (i j : m a) :
    (1 : Matrix n n k) (e ⟨a, i⟩) (e ⟨a, j⟩) = (1 : Matrix (m a) (m a) k) i j := by
  simp [Matrix.one_apply]

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [Fintype α] [LinearOrder α]
  [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)] [Fintype n] in

theorem one_ne (e : (Σ a, m a) ≃ n) {a b : α} (h : a ≠ b) (i : m a) (j : m b) :
    (1 : Matrix n n k) (e ⟨a, i⟩) (e ⟨b, j⟩) = 0 :=
  Matrix.one_apply_ne fun e' => h (congrArg Sigma.fst (e.injective e'))

theorem exists_jPlus_mul_KOne (e : (Σ a, m a) ≃ n) {g : GL n k} (hg : g ∈ proRad k e) :
    ∃ u ∈ jPlus k e, ∃ x ∈ KOne k n, g = u * x := by
  obtain ⟨h1, h3⟩ := mem_proRad.1 hg
  obtain ⟨h1, h2⟩ := mem_parahoric.1 h1
  let U : Matrix n n k := Matrix.of fun i j => if blk e i < blk e j then g.val i j else (1 : Matrix n n k) i j
  have hU : StepData.MaxM (U - g.val) := by
    intro i j
    obtain ⟨⟨a, i⟩, rfl⟩ := e.surjective i
    obtain ⟨⟨b, j⟩, rfl⟩ := e.surjective j
    simp only [U, Matrix.sub_apply, Matrix.of_apply, blk_apply]
    rcases lt_trichotomy a b with h | rfl | h
    · simp [h]
    · rw [if_neg (lt_irrefl a), one_same, Valuation.map_sub_swap]
      exact h3 a i j
    · rw [if_neg h.not_gt, one_ne e h.ne', zero_sub, Valuation.map_neg]
      exact h2 a b i j h
  obtain ⟨x, hx, hgx⟩ := StepData.exists_mul_KOne h1 hU
  refine ⟨g * x, ⟨mem_unipRad.2 ⟨mem_parab_iff.2 fun a b i j h => ?_, fun a i j => ?_⟩,
    mul_mem h1 (StepData.KOne_le_KO hx)⟩, x⁻¹, inv_mem hx, by simp⟩
  · rw [hgx]
    simp only [U, Matrix.of_apply, blk_apply]
    rw [if_neg h.not_gt, one_ne e h.ne']
  · rw [hgx]
    simp only [U, Matrix.of_apply, blk_apply]
    rw [if_neg (lt_irrefl a), one_same]

theorem exists_KOne_mul_jPlus (e : (Σ a, m a) ≃ n) {g : GL n k} (hg : g ∈ proRad k e) :
    ∃ x ∈ KOne k n, ∃ u ∈ jPlus k e, g = x * u := by
  obtain ⟨u, hu, x, hx, rfl⟩ := exists_jPlus_mul_KOne e hg
  exact ⟨u * x * u⁻¹, (Subgroup.mem_normalizer_iff.1 (KO_le_normalizer hu.2) x).1 hx, u, hu, by simp⟩

theorem proRad_eq_sup (e : (Σ a, m a) ≃ n) : proRad k e = KOne k n ⊔ jPlus k e := by
  refine le_antisymm (fun g hg => ?_) (sup_le (KOne_le_proRad e) (jPlus_le_proRad e))
  obtain ⟨x, hx, u, hu, rfl⟩ := exists_KOne_mul_jPlus e hg
  exact Subgroup.mul_mem_sup hx hu

theorem exists_mul_mem_parab (e : (Σ a, m a) ≃ n) {x : GL n k} (hx : x ∈ KOne k n) :
    ∃ c ∈ jMinus k e, x * c ∈ parab k e := by
  have hx' := StepData.mem_KOne.1 hx
  have hA : ∀ a : α, ∃ y ∈ KOne k n, y.val =
      Matrix.of fun i l => if a < blk e i then x.val i l else (1 : Matrix n n k) i l := fun a =>
    StepData.exists_mem_KOne fun i l => by
      simp only [Matrix.sub_apply, Matrix.of_apply]
      split_ifs
      · exact hx' i l
      · simp
  choose y hy hyv using hA
  obtain ⟨c, hc, hcv⟩ := StepData.exists_mem_KOne (M := Matrix.of fun i j => (y (blk e j))⁻¹.val i j)
    fun i j => StepData.mem_KOne.1 (inv_mem (hy (blk e j))) i j
  have key : ∀ i j, ∑ l, (if blk e j < blk e i then x.val i l else (1 : Matrix n n k) i l) * c.val l j =
      (1 : Matrix n n k) i j := fun i j => by
    have := congrFun (congrFun (y (blk e j)).mul_inv i) j
    rw [Matrix.mul_apply, hyv] at this
    rw [hcv]
    exact this
  have h1 : ∀ i j, blk e i ≤ blk e j → c.val i j = (1 : Matrix n n k) i j := fun i j h => by
    have := key i j
    simp only [if_neg h.not_gt] at this
    rwa [← Matrix.mul_apply, Matrix.one_mul] at this
  refine ⟨c, ⟨(mem_unipRadLower k).2 ⟨(mem_parabLower_iff k).2 fun a b i j h => ?_, fun a i j => ?_⟩, hc⟩,
    mem_parab_iff.2 fun a b i j h => ?_⟩
  · rw [h1 _ _ (by simpa using h.le), one_ne e h.ne]
  · rw [h1 _ _ (by simp), one_same]
  · have := key (e ⟨a, i⟩) (e ⟨b, j⟩)
    simp only [blk_apply, if_pos h] at this
    rw [Units.val_mul, Matrix.mul_apply, this, one_ne e h.ne']

theorem exists_jLevi_mul_jPlus (e : (Σ a, m a) ≃ n) {p : GL n k} (hp : p ∈ parab k e) (h : p ∈ KOne k n) :
    ∃ d ∈ jLevi k e, ∃ u ∈ jPlus k e, p = d * u := by
  obtain ⟨u, hu, hpu⟩ := exists_levi_mul_unip k e ⟨p, hp⟩
  have hd : leviEmb k e (leviProj k e ⟨p, hp⟩) ∈ jLevi k e :=
    ⟨_, fun a _ => StepData.mem_KOne.2 fun i j => by
      have := StepData.mem_KOne.1 h (e ⟨a, i⟩) (e ⟨a, j⟩)
      rw [Matrix.sub_apply, one_same] at this
      exact this, rfl⟩
  refine ⟨_, hd, u, ⟨hu, ?_⟩, hpu⟩
  rw [(inv_mul_eq_iff_eq_mul.2 hpu).symm]
  exact StepData.KOne_le_KO (mul_mem (inv_mem (jLevi_le_KOne e hd)) h)

theorem conj_mem_jPlus (e : (Σ a, m a) ≃ n) {d u : GL n k} (hd : d ∈ jLevi k e) (hu : u ∈ jPlus k e) :
    d * u * d⁻¹ ∈ jPlus k e := by
  have h := StepData.KOne_le_KO (jLevi_le_KOne e hd)
  obtain ⟨g, -, rfl⟩ := hd
  exact ⟨(Subgroup.mem_normalizer_iff.1 (leviEmb_mem_normalizer k e g) u).1 hu.1,
    (KO k n).mul_mem ((KO k n).mul_mem h hu.2) ((KO k n).inv_mem h)⟩

theorem conj_mem_jMinus (e : (Σ a, m a) ≃ n) {d c : GL n k} (hd : d ∈ jLevi k e) (hc : c ∈ jMinus k e) :
    d * c * d⁻¹ ∈ jMinus k e := by
  have h := jLevi_le_KOne e hd
  obtain ⟨g, -, rfl⟩ := hd
  exact ⟨(Subgroup.mem_normalizer_iff.1 (leviEmb_mem_normalizer_lower k e g) c).1 hc.1,
    (KOne k n).mul_mem ((KOne k n).mul_mem h hc.2) ((KOne k n).inv_mem h)⟩

theorem plus_levi_minus (e : (Σ a, m a) ≃ n) {g : GL n k} (hg : g ∈ proRad k e) :
    ∃ u ∈ jPlus k e, ∃ d ∈ jLevi k e, ∃ c ∈ jMinus k e, g = u * d * c := by
  obtain ⟨u, hu, x, hx, rfl⟩ := exists_jPlus_mul_KOne e hg
  obtain ⟨c, hc, hp⟩ := exists_mul_mem_parab e hx
  obtain ⟨d, hd, v, hv, h⟩ := exists_jLevi_mul_jPlus e hp (mul_mem hx hc.2)
  refine ⟨_, mul_mem hu (conj_mem_jPlus e hd hv), d, hd, c⁻¹, inv_mem hc, ?_⟩
  rw [eq_mul_inv_of_mul_eq h]
  group

theorem levi_plus_minus (e : (Σ a, m a) ≃ n) {g : GL n k} (hg : g ∈ proRad k e) :
    ∃ d ∈ jLevi k e, ∃ u ∈ jPlus k e, ∃ c ∈ jMinus k e, g = d * u * c := by
  obtain ⟨u, hu, d, hd, c, hc, rfl⟩ := plus_levi_minus e hg
  exact ⟨d, hd, _, conj_mem_jPlus e (inv_mem hd) hu, c, hc, by group⟩

theorem plus_minus_levi (e : (Σ a, m a) ≃ n) {g : GL n k} (hg : g ∈ proRad k e) :
    ∃ u ∈ jPlus k e, ∃ c ∈ jMinus k e, ∃ d ∈ jLevi k e, g = u * c * d := by
  obtain ⟨u, hu, d, hd, c, hc, rfl⟩ := plus_levi_minus e hg
  exact ⟨u, hu, _, conj_mem_jMinus e hd hc, d, hd, by group⟩

theorem minus_levi_plus (e : (Σ a, m a) ≃ n) {g : GL n k} (hg : g ∈ proRad k e) :
    ∃ c ∈ jMinus k e, ∃ d ∈ jLevi k e, ∃ u ∈ jPlus k e, g = c * d * u := by
  obtain ⟨u, hu, d, hd, c, hc, h⟩ := plus_levi_minus e (inv_mem hg)
  exact ⟨_, inv_mem hc, _, inv_mem hd, _, inv_mem hu, by rw [← inv_inv g, h]; group⟩

theorem levi_minus_plus (e : (Σ a, m a) ≃ n) {g : GL n k} (hg : g ∈ proRad k e) :
    ∃ d ∈ jLevi k e, ∃ c ∈ jMinus k e, ∃ u ∈ jPlus k e, g = d * c * u := by
  obtain ⟨c, hc, d, hd, u, hu, rfl⟩ := minus_levi_plus e hg
  exact ⟨d, hd, _, conj_mem_jMinus e (inv_mem hd) hc, u, hu, by group⟩

theorem minus_plus_levi (e : (Σ a, m a) ≃ n) {g : GL n k} (hg : g ∈ proRad k e) :
    ∃ c ∈ jMinus k e, ∃ u ∈ jPlus k e, ∃ d ∈ jLevi k e, g = c * u * d := by
  obtain ⟨c, hc, d, hd, u, hu, rfl⟩ := minus_levi_plus e hg
  exact ⟨c, hc, _, conj_mem_jPlus e hd hu, d, hd, by group⟩

theorem proRad_factorisation (e : (Σ a, m a) ≃ n) :
    proRad k e = KOne k n ⊔ jPlus k e ∧ jMinus k e ⊔ jLevi k e ⊔ jPlus k e = proRad k e ∧
    ∀ g ∈ proRad k e,
      ((∃ x ∈ KOne k n, ∃ u ∈ jPlus k e, g = x * u) ∧ ∃ u ∈ jPlus k e, ∃ x ∈ KOne k n, g = u * x) ∧
      (∃ c ∈ jMinus k e, ∃ d ∈ jLevi k e, ∃ u ∈ jPlus k e, g = c * d * u) ∧
      (∃ c ∈ jMinus k e, ∃ u ∈ jPlus k e, ∃ d ∈ jLevi k e, g = c * u * d) ∧
      (∃ d ∈ jLevi k e, ∃ c ∈ jMinus k e, ∃ u ∈ jPlus k e, g = d * c * u) ∧
      (∃ d ∈ jLevi k e, ∃ u ∈ jPlus k e, ∃ c ∈ jMinus k e, g = d * u * c) ∧
      (∃ u ∈ jPlus k e, ∃ c ∈ jMinus k e, ∃ d ∈ jLevi k e, g = u * c * d) ∧
      (∃ u ∈ jPlus k e, ∃ d ∈ jLevi k e, ∃ c ∈ jMinus k e, g = u * d * c) := by
  refine ⟨proRad_eq_sup e, le_antisymm
    (sup_le (sup_le (jMinus_le_proRad e) (jLevi_le_proRad e)) (jPlus_le_proRad e)) fun g hg => ?_, fun g hg =>
    ⟨⟨exists_KOne_mul_jPlus e hg, exists_jPlus_mul_KOne e hg⟩, minus_levi_plus e hg, minus_plus_levi e hg,
      levi_minus_plus e hg, levi_plus_minus e hg, plus_minus_levi e hg, plus_levi_minus e hg⟩⟩
  obtain ⟨c, hc, d, hd, u, hu, rfl⟩ := minus_levi_plus e hg
  exact Subgroup.mul_mem_sup (Subgroup.mul_mem_sup hc hd) hu

end GlobalTheory.LocGL.IwahoriFactor
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsLogTiltKummerCoboundaryBdR
section
noncomputable section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.MemLoc GlobalTheory.Pst.StLat GlobalTheory.Pst.NoLog
open scoped Formalism.Per

namespace GlobalTheory.PMon

theorem exists_log_tilt_BdR : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (T : LocTied l P AI),
    ∃ u : P.R.BdR, ∀ g : GQ l, P.actQdR g u = u + P.ιB ((kummer P g : ℚ_[l]) • P.tB) := by
  intro l _ P AI T
  obtain ⟨Co, hC⟩ := GlobalTheory.MemLoc.FitsEx.exists_fits l P AI T
  obtain ⟨ϖ, hr⟩ := exists_tilt (lRoot l) (lRoot_succ l) l (lRoot_zero l)
  have hϖ : ϖ.untilt = ((l : ℕ) : Per.OC l) := Subtype.ext (by
    have := hr 0
    rw [lRoot_zero, map_natCast] at this
    exact this.trans (SubringClass.coe_natCast _ _).symm)
  obtain ⟨u, hu⟩ := GlobalTheory.T.exists_logOnePlus_kerTheta_deRhamPlus l (beta ϖ) (by
    rw [GlobalTheory.T.kerP_eq_span_beta_of_untilt_eq l ϖ hϖ]; exact Ideal.mem_span_singleton_self _)
  have hg := GlobalTheory.T.galois_logTeichmullerRatio_eq_add_kummer l P Co hC.ζ ϖ hr hϖ u hu
  have hct : ∀ g : GQ l, T.eD (P.ιB ((kummer P g : ℚ_[l]) • P.tB)) =
      algebraMap (Per.BdRp l) (Per.BdR l)
        (Co.j (algebraMap (Per.Ainf l) (Per.Acris l) (Per.zA l (kummer P g)) * Co.t)) := by
    intro g
    rw [hC.ι, Algebra.smul_def, map_mul, T.zB, hC.t, ← Co.ι_j]
    simp only [Core.tB, GlobalTheory.RingIface.zB_alg, map_mul]
  refine ⟨T.eD.symm (algebraMap (Per.BdRp l) (Per.BdR l) u), fun g => ?_⟩
  apply T.eD.injective
  rw [T.actD, RingEquiv.apply_symm_apply, map_add, RingEquiv.apply_symm_apply, hct]
  rw [show Per.σD g (algebraMap (Per.BdRp l) (Per.BdR l) u) =
    algebraMap (Per.BdRp l) (Per.BdR l) (Per.σDp g u) from GlobalTheory.MemLoc.ActLaws.σD_alg _ _, hg, map_add]

end GlobalTheory.PMon
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsMonodromyFrobeniusSolutionFil
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N GlobalTheory.Pst GlobalTheory.PMon TensorProduct Module
open scoped Formalism.Per

namespace GlobalTheory.PMon

theorem lTensor_crisIncl_eq_ιV {l : ℕ} [Fact l.Prime] (P : LocPrime l) (ι : Bst P →ₐ[ℚ_[l]] P.R.BdR)
    (hι : ∀ b, ι (Polynomial.C b) = P.ιB b) (K : FinExt l) (V : Type) [AddCommGroup V] [Module ℚ_[l] V]
    (w : V ⊗[ℚ_[l]] P.R.B) :
    LinearMap.lTensor V ι.toLinearMap (crisIncl P ℚ_[l] V w) = ιV (P.PD K) (LL := ℚ_[l]) (V := V) w := by
  induction w using TensorProduct.induction_on with
  | zero => simp
  | tmul v b =>
    rw [crisIncl_tmul, LinearMap.lTensor_tmul]
    simp only [ιV, AlgebraTensorModule.map_tmul, LinearMap.id_coe, id_eq, AlgHom.toLinearMap_apply,
      LinearMap.coe_restrictScalars, hι, P.PD_ι]
  | add a b ha hb => simp only [map_add, ha, hb]

theorem solve_mon_phi_fil : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (T : LocTied l P AI)
    (ι : Bst P →ₐ[ℚ_[l]] P.R.BdR), (∀ b, ι (Polynomial.C b) = P.ιB b) → ∀ (K : FinExt l) (V : Type)
    [AddCommGroup V] [Module ℚ_[l] V] (x y : V ⊗[ℚ_[l]] Bst P),
    (l : ℚ_[l]) • phiV P ℚ_[l] V x - x = monV P ℚ_[l] V y → ∃ z : V ⊗[ℚ_[l]] Bst P,
      monV P ℚ_[l] V z = x ∧ phiV P ℚ_[l] V z - z = y ∧
      LinearMap.lTensor V ι.toLinearMap z ∈ FilV (P.PD K) (LL := ℚ_[l]) (V := V) 0 := by
  intro l _ P AI T ι hι K V _ _ x y h
  obtain ⟨z₀, hz₀⟩ := GlobalTheory.T.monodromyTensorSemistablePeriodRing_surjective l P V x
  have he : monV P ℚ_[l] V (phiV P ℚ_[l] V z₀ - z₀ - y) = 0 := by
    have h1 : monV P ℚ_[l] V (phiV P ℚ_[l] V z₀) = (l : ℚ_[l]) • phiV P ℚ_[l] V x := by
      rw [← End.mul_apply, monV_phiV, LinearMap.smul_apply, End.mul_apply, hz₀]
    rw [map_sub, map_sub, h1, hz₀, h, sub_self]
  obtain ⟨u, hu⟩ := (GlobalTheory.T.monV_eq_zero_iff_mem_range_crisIncl' l P V _).mp he
  obtain ⟨x₁, y₁, hy₁, hx₁, hxy⟩ := (GlobalTheory.T.tensor_fundamental_exact_sequence_crystalline l P AI T K ℚ_[l] V).1 u
    (-(LinearMap.lTensor V ι.toLinearMap z₀))
  refine ⟨z₀ + crisIncl P ℚ_[l] V x₁, ?_, ?_, ?_⟩
  · have h0 : monV P ℚ_[l] V (crisIncl P ℚ_[l] V x₁) = 0 := (GlobalTheory.T.monV_eq_zero_iff_mem_range_crisIncl' l P V _).mpr ⟨x₁, rfl⟩
    rw [map_add, hz₀, h0, add_zero]
  · have h2 : phiV P ℚ_[l] V (crisIncl P ℚ_[l] V x₁) - crisIncl P ℚ_[l] V x₁ = -crisIncl P ℚ_[l] V u := by
      rw [GlobalTheory.T.frobeniusTensor_crisToSemistable_comm l P K V x₁, ← map_sub, ← hx₁, ← map_neg, neg_sub]
    have h3 : phiV P ℚ_[l] V z₀ - z₀ = crisIncl P ℚ_[l] V u + y := by rw [hu]; abel
    calc phiV P ℚ_[l] V (z₀ + crisIncl P ℚ_[l] V x₁) - (z₀ + crisIncl P ℚ_[l] V x₁)
        = (phiV P ℚ_[l] V z₀ - z₀) + (phiV P ℚ_[l] V (crisIncl P ℚ_[l] V x₁) - crisIncl P ℚ_[l] V x₁) := by
          rw [map_add]; abel
      _ = y := by rw [h2, h3]; abel
  · rw [map_add, lTensor_crisIncl_eq_ιV P ι hι K V x₁]
    have : LinearMap.lTensor V ι.toLinearMap z₀ + ιV (P.PD K) (LL := ℚ_[l]) (V := V) x₁ = y₁ := by
      rw [← sub_eq_zero, add_sub_assoc, hxy, add_neg_cancel]
    rw [this]; exact hy₁

end GlobalTheory.PMon
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExtensionLatticeIsCrysTameTypeWithJumpsStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.extensionLattice_isCrysTameTypeWithJumps : GlobalTheory.Published.FontaineBcris → ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (ϖ : PiSys l e) (LL : FinExt l) [HasUnr a LL] [TameDescentExponentData ↥LL.1 l e a] (Pl : LocPrime l) (AI : LocAinf l Pl), IsStd Pl AI → ∀ (Sig : Finset (ZMod e)) (U : Finset ℤ), (0 : ZMod e) ∈ Sig → (0 : ℤ) ∈ U → IsGood a ϖ Pl (unitLat (Gl l) : QLat LL) Sig U ∧ ∀ T : QLat LL, IsGood a ϖ Pl T Sig U → ∀ c ∈ latticeFiniteCocycles (Pl.PD (Formalism.MainNotions.ElementDenominator.qlExt l)) T.L, ∃ (Tp : QLat LL) (f : LatHom T.L Tp.L) (g : LatHom Tp.L (unitLat (Gl l) : QLat LL).L) (v : Tp.V), IsSESLat (Qp := ℚ_[l]) f g ∧ v ∈ Tp.L.T ∧ g.f v = (1 : ↥LL.1) ∧ (∀ h, Tp.ρ h v - v = f.f (c h)) ∧ IsGood a ϖ Pl Tp Sig U := by
  first | exact @GlobalTheory.ExtGood.extLat_isGood | exact GlobalTheory.ExtGood.extLat_isGood | (intros; apply GlobalTheory.ExtGood.extLat_isGood <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteStableLatticesDifferenceTermNeZeroStatement
section
open GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Desc Polynomial Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_stableLattices_differenceTerm_ne_zero : ∀ (K : UQ) (B : InvAlg K) (ι : Type) [Fintype ι] (e π : ι → B.A) (S : Finset ι), B.P.Separable → IsFrame B e π S → ∀ (I I' : Finset ι), I ⊆ S → I' ⊆ S → ∀ u s : B.A, IsUnit u → IsUnit s → {M ∈ B.Lin | term B π I I' u s M ≠ 0}.Finite := by
  first | exact @GlobalTheory.UnitLemma.Desc.finite_term_ne_zero | exact GlobalTheory.UnitLemma.Desc.finite_term_ne_zero | (intros; apply GlobalTheory.UnitLemma.Desc.finite_term_ne_zero <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FontainePropertiesAllPlaces
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions Formalism.MainNotions.N

namespace GlobalTheory.FontaineAdmissible

theorem fontaineProperties_all_places : ∀ D : D7, Formalism.MainNotions.PairedCharacterCondition.FontaineAtPlacesOverL (D := D) := by
  intro D l _ K LL
  exact GlobalTheory.FontaineAll.fontaineAt_all D l K LL

end GlobalTheory.FontaineAdmissible
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FontainePropertiesAllPlacesAlt
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions Formalism.MainNotions.N

namespace GlobalTheory.FontaineAdm

theorem fontaineProperties_all_places : ∀ (D : D7) (i : D.nd.Loc), Formalism.MainNotions.TruncatedSeriesCountingIdentities.FontaineAtPlacesOverL (D := D) i :=
  fun D i => Formalism.MainNotions.Pk.font_of_all_places (fun l _ K LL => GlobalTheory.FontaineAll.fontaineAt_all D l K LL) i

end GlobalTheory.FontaineAdm
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GaloisCoboundaryFrobeniusFixedStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.galoisCoboundary_frobenius_fixed : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] [TameDescentExponentData K l e a] (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e) (ι : Type) [Fintype ι] [DecidableEq ι] (η H : ℕ) (D : BKDat O K l e a ι η H) (T : LocLat (Gl l) ℚ_[l] K O) (R : GalDat t ϖ (sQ l) D T), ∀ y ∈ D.Y, ∀ b, R.IsPotential y b → ∀ g : Gl l, sQ l g ∈ GK (ϖ.field a) → TWmap (frobOB l O) T (actB (sQ l) T g b - b) = actB (sQ l) T g b - b := by
  first | exact @GlobalTheory.BKGal.PhiFix.frob_fixed_coboundary | exact GlobalTheory.BKGal.PhiFix.frob_fixed_coboundary | (intros; apply GlobalTheory.BKGal.PhiFix.frob_fixed_coboundary <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GaloisDividedTaylorExpansionFrobeniusBasisStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.galois_dividedTaylor_expansion_frobeniusBasis : GlobalTheory.Published.BhattScholzeCrystallineLattices → ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (ϖ : PiSys l e) (LL : FinExt l) [HasUnr a LL] [TameDescentExponentData ↥LL.1 l e a], l ≠ 2 → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (P : PhiMod ↥(OL LL) ↥LL.1 l e a ι) (T : QLat LL) (I : Ident (thetaW a LL) ϖ P T), IsBK (T := resF T (ϖ.field a)) (I.res (inclG (ϖ.field a)) (continuous_subtype_val.subtype_mk _)) → ∀ (hS : ∀ (τ : ZMod a) (j : ι) (k : ℕ) (i : ι), (X : (↥LL.1)⟦X⟧) ^ k * (P.mxInv τ *ᵥ (P.nabla ^ k) (P.phi (bas j)) τ) i ∈ S (↥(OL LL)) (↥LL.1) e) (g : ↥(GK (ϖ.field a))), ∃ Γ, (I.res (inclG (ϖ.field a)) (continuous_subtype_val.subtype_mk _)).IsLMat (g : GQ l) g Γ ∧ ∀ (i j : ι) (r : ℕ), ∃ n₀ : ℕ, ∀ n ≥ n₀, (l : OCr l ↥(OL LL)) ^ r ∣ toOCr l ↥(OL LL) (Γ i j) - ∑ k ∈ Finset.range n, ϖ.muDiv a ↥(OL LL) g k * ϖ.iC (thetaW a LL) ↥LL.1 (fun τ => ⟨_, hS τ j k i⟩) := by
  first | exact @GlobalTheory.CrysGal.galois_taylor_basis | exact GlobalTheory.CrysGal.galois_taylor_basis | (intros; apply GlobalTheory.CrysGal.galois_taylor_basis <;> assumption)
end

