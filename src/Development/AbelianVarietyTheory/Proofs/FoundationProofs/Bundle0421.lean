import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.IsZetaTW
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0022
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0009
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0018
import Development.AbelianVarietyTheory.Definitions.Foundations.EigenfunctionalZeroProjection
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0004
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0020
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0023
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0021
import Development.AbelianVarietyTheory.Definitions.Foundations.ActWBOfInvariant
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0178
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0102
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0274
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0391
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0400
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0088
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0286
import Development.AutomorphicArithmetic.Foundations.IwahoriReduction.SiegelFixedPoints.Thdiam
import Development.AbelianVarietyTheory.Definitions.Foundations.IsLamFR2
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0019
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0396
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0420
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0404

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.CmValuationNewformCongruence
section
noncomputable section

open scoped MatrixGroups Matrix
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.KZ GlobalTheory.Ord2 GlobalTheory.K4

namespace GlobalTheory.LambdaValuationPowers.ZetaCoef

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {l : ℕ} [Fact l.Prime]

theorem norm_algebraMap_le (a : ℤ_[l]) : ‖algebraMap ℤ_[l] (Qbar l) a‖ ≤ 1 := by
  rw [IsScalarTower.algebraMap_apply ℤ_[l] ℚ_[l] (Qbar l), norm_algebraMap']
  exact a.2

theorem exists_isLamG [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (hl : l ≠ 2) {m n : ℕ} (hm : 1 ≤ m) (hmn : m ≤ n) {s : G ℚ Ω}
    (hs : cycMod ℚ Ω l m s = 1) :
    ∃ tt : ZMod (l ^ n), GlobalTheory.Glue.IsLamG ε l n m s tt ∧ ∃ v u : Qbar l, ‖v‖ ≤ 1 ∧ ‖u‖ ≤ 1 ∧
      ((tt.val : ℕ) : Qbar l) = lamv l m s * (1 + (l : Qbar l) ^ m * v) + (l : Qbar l) ^ n * u := by
  have hp : l.Prime := Fact.out
  have : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  have : CharZero Ω := charZero_of_injective_algebraMap (algebraMap ℚ Ω).injective
  have : NeZero (l : Ω) := ⟨Nat.cast_ne_zero.2 hp.ne_zero⟩
  obtain ⟨a, ha, hlam⟩ := exists_lamv_eq hs
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hmn
  have h3 : 3 ≤ l := by have := hp.two_le; omega
  obtain ⟨y, hy⟩ := ZMod.exists_one_add_mul_pow_prime_pow_eq (R := ℤ_[l]) (u := (l : ℤ_[l]) ^ m * a) (v := (l : ℤ_[l]) ^ m) hp
    (dvd_mul_right _ _) (by
      obtain ⟨q, hq⟩ := Nat.exists_eq_add_of_le h3
      obtain ⟨m', rfl⟩ := Nat.exists_eq_add_of_le hm
      refine ⟨((l : ℤ_[l]) ^ (1 + m') * a) ^ q * a ^ 2 * (l : ℤ_[l]) ^ m', ?_⟩
      rw [show ((l : ℤ_[l]) ^ (1 + m') * a) ^ l = ((l : ℤ_[l]) ^ (1 + m') * a) ^ (3 + q) by rw [← hq]]
      ring) 1 k
  set T : ℤ_[l] := a * (1 + (l : ℤ_[l]) ^ m * y) with hT
  set tt : ZMod (l ^ (m + k)) := PadicInt.toZModPow (m + k) T with htt
  have h2 : ((tt.val : ℕ) : ℤ_[l]) - T ∈ RingHom.ker (PadicInt.toZModPow (m + k) : ℤ_[l] →+* ZMod (l ^ (m + k))) := by
    rw [RingHom.mem_ker, map_sub, map_natCast, ZMod.natCast_zmod_val, htt, sub_self]
  rw [PadicInt.ker_toZModPow, Ideal.mem_span_singleton] at h2
  obtain ⟨u, hu⟩ := h2
  refine ⟨tt, ?_, algebraMap ℤ_[l] (Qbar l) y, algebraMap ℤ_[l] (Qbar l) u, norm_algebraMap_le _, norm_algebraMap_le _, ?_⟩
  · have hz := GlobalTheory.Glue.Roots.isPrimitiveRoot_zt ε hp.ne_zero (2 * (m + k))
    have hn : GlobalTheory.Glue.zt ε l (m + k) = GlobalTheory.Glue.zt ε l (2 * (m + k)) ^ l ^ (m + k) := by
      rw [two_mul, GlobalTheory.Glue.Roots.zt_add_pow ε hp.ne_zero]
    change (s ^ (l ^ (m + k - m))) (GlobalTheory.Glue.zt ε l (2 * (m + k))) =
      GlobalTheory.Glue.zt ε l (m + k) ^ tt.val * GlobalTheory.Glue.zt ε l (2 * (m + k))
    have h1 : (s ^ (l ^ k)) (GlobalTheory.Glue.zt ε l (2 * (m + k))) = GlobalTheory.Glue.zt ε l (2 * (m + k)) ^
        (PadicInt.toZModPow (2 * (m + k)) ((cycZ ℚ Ω l (s ^ (l ^ k)) : ℤ_[l]ˣ) : ℤ_[l])).val :=
      cyclotomicCharacter.spec (L := Ω) l (MulSemiringAction.toRingAut (G ℚ Ω) Ω (s ^ (l ^ k))) _ hz.pow_eq_one
    have h4 : ((cycZ ℚ Ω l (s ^ (l ^ k)) : ℤ_[l]ˣ) : ℤ_[l]) =
        ((l ^ (m + k) * tt.val + 1 : ℕ) : ℤ_[l]) - ((l ^ (2 * (m + k)) : ℕ) : ℤ_[l]) * u := by
      rw [map_pow, Units.val_pow_eq_pow_val, ha]
      rw [mul_one] at hy
      rw [hy]
      push_cast
      rw [eq_add_of_sub_eq hu, hT]
      ring
    rw [Nat.add_sub_cancel_left, h1, h4, map_sub, map_mul, map_natCast, map_natCast, ZMod.natCast_self, zero_mul, sub_zero,
      ZMod.val_natCast, ← pow_eq_pow_mod _ hz.pow_eq_one, hn, ← pow_mul, pow_succ]
  · have := congrArg (algebraMap ℤ_[l] (Qbar l)) (eq_add_of_sub_eq hu)
    rw [map_natCast] at this
    rw [this, hlam, hT]
    simp only [map_add, map_mul, map_pow, map_natCast, map_one]
    ring

abbrev pushB {ε : Ω →+* ℂ} (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (n m N : ℕ) [NeZero N] (bB : (Ω ≃ₐ[ℚ] Ω) → X.Fn l)
    (s : Ω ≃ₐ[ℚ] Ω) (y : (ZMod (l ^ m))ˣ) : X.Fn l :=
  GlobalTheory.KA.push (redM l n m (N * N)) (fun (s' : Ω ≃ₐ[ℚ] Ω) (y' : (ZMod (topM l n m (N * N)))ˣ) =>
    X.galB l (repM (topM l n m (N * N)) y')
      (bB ((repM (topM l n m (N * N)) y')⁻¹ * s' * repM (topM l n m (N * N)) (y' * (cycM (topM l n m (N * N)) s')⁻¹)))) s y

theorem pushB_spec [IsAlgClosure ℚ Ω] {ε : Ω →+* ℂ} (X : Tower Ω ε) {N : ℕ} [NeZero N] (w n m : ℕ)
    (pr : X.Fn l → Fin 2 → Qbar l) (W : R2 Ω l) (e : ℕ) (ψ : ZMod l → Qbar l)
    (hgal : ∀ s : Ω ≃ₐ[ℚ] Ω, ∀ b ∈ X.B N l w, X.galB l s b ∈ X.B N l w) (hadd : ∀ b b', pr (b + b') = pr b + pr b')
    (heq : ∀ (s : Ω ≃ₐ[ℚ] Ω) b, b ∈ X.B N l w → pr (X.galB l s b) = rhoK W e ψ s *ᵥ pr b)
    (bB : (Ω ≃ₐ[ℚ] Ω) → X.Fn l) (hB : ∀ σ ∈ fixMu Ω (topMu l n m N), bB σ ∈ X.B N l w) (s : Ω ≃ₐ[ℚ] Ω) (y : (ZMod (l ^ m))ˣ) :
    pushB X l n m N bB s y ∈ X.B N l w ∧ pr (pushB X l n m N bB s y) = YfB X l pr W e ψ n m N bB s y := by
  have hmem : ∀ y' : (ZMod (topM l n m (N * N)))ˣ,
      bB ((repM (topM l n m (N * N)) y')⁻¹ * s * repM (topM l n m (N * N)) (y' * (cycM (topM l n m (N * N)) s)⁻¹)) ∈
        X.B N l w := fun y' => hB _ (shArg_mem_fixMu (topM l n m (N * N)) s y')
  refine ⟨Submodule.sum_mem _ fun y' _ => hgal _ _ (hmem y'), ?_⟩
  refine (map_sum (AddMonoidHom.mk' pr hadd) _ _).trans ?_
  exact Finset.sum_congr rfl fun y' _ => heq _ _ (hmem y')

theorem cycMod_one_of {m : ℕ} (hm : 1 ≤ m) {s : G ℚ Ω} (hs : cycMod ℚ Ω l m s = 1) : cycMod ℚ Ω l 1 s = 1 := by
  obtain ⟨a, ha, -⟩ := exists_lamv_eq hs
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hm
  ext
  change PadicInt.toZModPow 1 ((cycZ ℚ Ω l s : ℤ_[l]ˣ) : ℤ_[l]) = 1
  have e : (l : ℤ_[l]) ^ (1 + k) * a = ((l ^ 1 : ℕ) : ℤ_[l]) * ((l : ℤ_[l]) ^ k * a) := by push_cast; ring
  rw [ha, e, map_add, map_one, map_mul, map_natCast, ZMod.natCast_self, zero_mul, add_zero]

theorem cg_per {per : ℕ → Qbar l} (h : ∀ n, Cg n (per (n + 1)) (per n)) {m n : ℕ} (hmn : m ≤ n) : Cg m (per n) (per m) := by
  induction n, hmn using Nat.le_induction with
  | base => simp [Cg]
  | succ n hn ih =>
    have h1 : Cg m (per (n + 1)) (per n) := GlobalTheory.KummerEisensteinGalois.cg_mono hn (h n)
    unfold Cg at *
    rw [← sub_add_sub_cancel _ (per n)]
    exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le h1 ih)

theorem chain {Y P F pn pm E t a v u C lc μ ν : Qbar l} (hμ : ‖μ‖ < 1) (hlc : ‖lc‖ ≤ 1) (hP : ‖P‖ ≤ 1) (hC : ‖C‖ ≤ 1)
    (hv : ‖v‖ ≤ 1) (hu : ‖u‖ ≤ 1) (hpn : ‖pn‖ = 1) (hpm : ‖pm‖ = 1) (ht : t = a * (1 + μ * v) + ν * u)
    (h1 : ‖Y - P‖ ≤ ‖μ‖) (h2 : ‖F - pn * P‖ ≤ ‖μ‖) (h3 : ‖lc * F - (lc * (E * t) + C)‖ ≤ ‖μ‖) (h4 : ‖pn - pm‖ ≤ ‖μ‖)
    (h5 : ‖E * ν‖ ≤ ‖μ‖) : ‖lc * Y - (lc * (pm⁻¹ * E) * a + pn⁻¹ * C)‖ ≤ ‖μ‖ := by
  have add : ∀ {r : ℝ} {x y : Qbar l}, ‖x‖ ≤ r → ‖y‖ ≤ r → ‖x + y‖ ≤ r := fun hx hy =>
    (IsUltrametricDist.norm_add_le_max _ _).trans (max_le hx hy)
  have mul : ∀ {r : ℝ} {x y : Qbar l}, ‖x‖ ≤ 1 → ‖y‖ ≤ r → ‖x * y‖ ≤ r := fun hx hy => by
    rw [norm_mul]; exact (mul_le_of_le_one_left (norm_nonneg _) hx).trans hy
  have neg : ∀ {r : ℝ} {x : Qbar l}, ‖x‖ ≤ r → ‖-x‖ ≤ r := fun hx => by rwa [norm_neg]
  have hunit : ‖1 + μ * v‖ = 1 := by
    have h : ‖μ * v‖ < ‖(1 : Qbar l)‖ := by
      rw [norm_one, mul_comm]; exact (mul hv le_rfl).trans_lt hμ
    rw [IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm h.ne', max_eq_left h.le, norm_one]
  have hG : ‖lc * E * a‖ ≤ 1 := by
    have e : lc * E * a * (1 + μ * v) = lc * ((F - pn * P) + pn * P) + -C + -(lc * F - (lc * (E * t) + C)) +
        -(lc * (u * (E * ν))) := by rw [ht]; ring
    have h := add (add (add (mul hlc (add (h2.trans hμ.le) (mul hpn.le hP))) (neg hC)) (neg (h3.trans hμ.le)))
      (neg (mul hlc (mul hu (h5.trans hμ.le))))
    rwa [← e, norm_mul, hunit, mul_one] at h
  have hn0 : pn ≠ 0 := fun h => by simp [h] at hpn
  have hm0 : pm ≠ 0 := fun h => by simp [h] at hpm
  have e : pn * (pm * (lc * Y - (lc * (pm⁻¹ * E) * a + pn⁻¹ * C))) =
      pm * (pn * (lc * (Y - P))) + -(pm * (lc * (F - pn * P))) + pm * (lc * F - (lc * (E * t) + C)) +
        pm * (lc * E * a * (v * μ)) + pm * (lc * (u * (E * ν))) + -(lc * E * a * (pn - pm)) := by
    rw [ht]; field_simp; ring
  have h := add (add (add (add (add (mul hpm.le (mul hpn.le (mul hlc h1))) (neg (mul hpm.le (mul hlc h2)))) (mul hpm.le h3))
    (mul hpm.le (mul hG (mul hv le_rfl)))) (mul hpm.le (mul hlc (mul hu h5)))) (neg (mul hG h4))
  rwa [← e, norm_mul, norm_mul, hpn, hpm, one_mul, one_mul] at h

theorem diam_diam {ε : Ω →+* ℂ} (X : Tower Ω ε) {N w a b k : ℕ} (ha : Nat.Coprime a N) (hb : Nat.Coprime b N)
    (hk : k ≡ a * b [MOD N]) {f : X.Fn l} (hf : f ∈ X.B N l w) : X.diam N l b (X.diam N l a f) = X.diam N l k f := by
  have hl0 : l ≠ 0 := (Fact.out : l.Prime).ne_zero
  have hpos : ∀ g : SL(2, ℤ), 0 < (g : Matrix (Fin 2) (Fin 2) ℤ).det := fun g => by rw [g.det_coe]; exact one_pos
  have h := isDiam_mul (isDiam_sgD_of_coprime (l := l) hl0 ha) (isDiam_sgD_of_coprime (l := l) hl0 hb)
  have h' : IsDiam N l k (sgD N l a * sgD N l b) :=
    ⟨h.1, h.2.trans ((ZMod.natCast_eq_natCast_iff _ _ _).2 (by rw [mul_comm]; exact hk.symm))⟩
  rw [Tower.diam, Tower.diam, Tower.diam, Tower.act_act Ω ε X l _ _ (hpos _) (hpos _) f, ← X.act_isDiam_eq hf h',
    Matrix.SpecialLinearGroup.coe_mul]

theorem inChi_avg {ε : Ω →+* ℂ} (X : Tower Ω ε) {N : ℕ} [NeZero N] (hNl : Nat.Coprime N l) {w : ℕ} {χ : ℕ → ℤ_[l]}
    (hχ : ∀ a b k : ℕ, Nat.Coprime a N → Nat.Coprime b N → k ≡ a * b [MOD N] → χ k = χ a * χ b)
    (u : (ZMod N)ˣ → ℤ_[l]) (hu : ∀ δ, u δ * χ (δ : ZMod N).val = 1) {f : X.Fn l} (hf : f ∈ X.B N l w) :
    GlobalTheory.KummerEisensteinGalois.InChi X N w χ (∑ δ : (ZMod N)ˣ, u δ • X.diam N l (δ : ZMod N).val f) := by
  refine ⟨Submodule.sum_mem _ fun δ _ => Submodule.smul_mem _ _
    (GlobalTheory.CyclotomicQExpansion.ThnEx.diam_B X N l w _ (NeZero.pos N) hNl (ZMod.val_coe_unit_coprime δ) f hf), fun d hd => ?_⟩
  rw [map_sum, Finset.smul_sum, ← Equiv.sum_comp (Equiv.mulRight (ZMod.unitOfCoprime d hd))
    (fun δ => χ d • u δ • X.diam N l (δ : ZMod N).val f)]
  refine Finset.sum_congr rfl fun δ _ => ?_
  have hk : ((δ * ZMod.unitOfCoprime d hd : (ZMod N)ˣ) : ZMod N).val ≡ (δ : ZMod N).val * d [MOD N] := by
    rw [← ZMod.natCast_eq_natCast_iff]; simp
  have h1 := hχ _ _ _ (ZMod.val_coe_unit_coprime δ) hd hk
  have h2 := hu (δ * ZMod.unitOfCoprime d hd)
  have h3 : χ d * u (δ * ZMod.unitOfCoprime d hd) = u δ := by
    rw [h1] at h2
    linear_combination (-(χ d * u (δ * ZMod.unitOfCoprime d hd))) * hu δ + u δ * h2
  rw [map_smul, diam_diam X (ZMod.val_coe_unit_coprime δ) hd hk hf, Equiv.coe_mulRight, smul_smul, h3]

theorem exists_isThB_sum [IsAlgClosed Ω] {ε : Ω →+* ℂ} (X : Tower Ω ε) {A : ValuationSubring Ω} {j : Ω →+* Qbar l}
    (hj : ∀ z : Ω, z ∈ A ↔ ‖j z‖ ≤ 1) (hnon : (l : Ω) ∈ A.nonunits) {N w n : ℕ} {ι : Type} (T : Finset ι) (hT : T.Nonempty)
    (u : ι → ℤ_[l]) (f : ι → X.Fn l) (φ : ι → HahnSeries ℚ Ω) (hf : ∀ i, f i ∈ X.B N l w)
    (hφ : ∀ i, GlobalTheory.Glue.IsThB X A N l n (f i) (φ i)) :
    ∃ Φ : HahnSeries ℚ Ω, GlobalTheory.Glue.IsThB X A N l n (∑ i ∈ T, u i • f i) Φ ∧
      ∀ r, Cg n (j (Φ.coeff r)) (∑ i ∈ T, algebraMap ℤ_[l] (Qbar l) (u i) * j ((φ i).coeff r)) := by
  have hint : ∀ {b : X.Fn l} {Φ : HahnSeries ℚ Ω}, GlobalTheory.Glue.IsThB X A N l n b Φ → ∀ r, ‖j (Φ.coeff r)‖ ≤ 1 :=
    fun ⟨_, _, _, _, h, _⟩ r => (hj _).1 (h r)
  have happ : ∀ (a : ℤ_[l]) (z : Qbar l), ‖z‖ ≤ 1 →
      ‖((a.appr n : ℕ) : Qbar l) * z - algebraMap ℤ_[l] (Qbar l) a * z‖ ≤ ‖(l : Qbar l) ^ n‖ := fun a z hz => by
    obtain ⟨q, hq⟩ := Ideal.mem_span_singleton.1 (PadicInt.appr_spec n a)
    have h := congrArg (algebraMap ℤ_[l] (Qbar l)) hq
    rw [map_sub, map_natCast, map_mul, map_pow, map_natCast] at h
    rw [← sub_mul, norm_mul, norm_sub_rev, h]
    refine (mul_le_of_le_one_right (norm_nonneg _) hz).trans ?_
    rw [norm_mul]
    exact mul_le_of_le_one_right (norm_nonneg _) (norm_algebraMap_le q)
  have key : ∀ (a a' : ℤ_[l]) {b b' : X.Fn l} {Φ Φ' : HahnSeries ℚ Ω}, b ∈ X.B N l w → b' ∈ X.B N l w →
      GlobalTheory.Glue.IsThB X A N l n b Φ → GlobalTheory.Glue.IsThB X A N l n b' Φ' →
      ∃ Ψ, GlobalTheory.Glue.IsThB X A N l n (a • b + a' • b') Ψ ∧ ∀ r, ‖j (Ψ.coeff r) -
        (algebraMap ℤ_[l] (Qbar l) a * j (Φ.coeff r) + algebraMap ℤ_[l] (Qbar l) a' * j (Φ'.coeff r))‖ ≤ ‖(l : Qbar l) ^ n‖ := by
    intro a a' b b' Φ Φ' hb hb' h h'
    refine ⟨_, GlobalTheory.ThAdd.isThB_add Ω ε X A N l n w b b' hnon hb hb' a a' Φ Φ' h h', fun r => ?_⟩
    simp only [HahnSeries.coeff_add, HahnSeries.coeff_smul, smul_eq_mul, map_add, map_mul, map_natCast]
    rw [add_sub_add_comm]
    exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (happ _ _ (hint h r)) (happ _ _ (hint h' r)))
  induction hT using Finset.Nonempty.cons_induction with
  | singleton i =>
    obtain ⟨Ψ, h1, h2⟩ := key (u i) 0 (hf i) (hf i) (hφ i) (hφ i)
    exact ⟨Ψ, by simpa using h1, fun r => by simpa [Cg] using h2 r⟩
  | cons i T hi _ ih =>
    obtain ⟨Φ, h1, h2⟩ := ih
    obtain ⟨Ψ, h3, h4⟩ := key (u i) 1 (hf i) (Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (hf i)) (hφ i) h1
    refine ⟨Ψ, by simpa [Finset.sum_cons, -Finset.cons_eq_insert] using h3, fun r => ?_⟩
    rw [Finset.sum_cons]
    unfold Cg
    rw [← sub_add_sub_cancel _ (algebraMap ℤ_[l] (Qbar l) (u i) * j ((φ i).coeff r) + algebraMap ℤ_[l] (Qbar l) 1 * j (Φ.coeff r))]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (h4 r) ?_)
    rw [add_sub_add_left_eq_sub, map_one, one_mul]
    exact h2 r

theorem htCoL_of_fintype {A : ValuationSubring Ω} {c : Coef l} {j : Ω →+* Qbar l}
    {Z : ∀ r : ℕ, G ℚ Ω → (ZMod (l ^ r))ˣ → Qbar l} {m c₀ : ℕ} {y : (ZMod (l ^ m))ˣ} {h : Qbar l} {ι : Type} [Fintype ι]
    (o : ι → Qbar l) (w : ι → Ω) (how : ∀ i, ‖o i‖ ≤ 1 ∧ FixIc c (o i) ∧ ‖j (w i)‖ ≤ 1)
    (H : ∀ s ∈ Ine (F := ℚ) A, cycMod ℚ Ω l m s = 1 →
      Cg m ((l : Qbar l) ^ c₀ * Z m s y) ((l : Qbar l) ^ c₀ * h * lamv l m s + ∑ i, o i * (j (s (w i)) - j (w i)))) :
    HTCoL A c j Z m c₀ y h :=
  ⟨Fintype.card ι, fun i => o ((Fintype.equivFin ι).symm i), fun i => w ((Fintype.equivFin ι).symm i), fun _ => how _,
    fun s hs hc => by
      rw [(Fintype.equivFin ι).symm.sum_comp fun i => o i * (j (s (w i)) - j (w i))]
      exact H s hs hc⟩

theorem norm_pow_mul_le {a : Qbar l} {k : ℕ} (h : ‖a‖ ≤ (l : ℝ) ^ k) : ‖(l : Qbar l) ^ k * a‖ ≤ 1 := by
  have h2 := GlobalTheory.KummerEisensteinGalois.l_pow_mul_norm (l := l) (le_refl k)
  rw [Nat.sub_self, pow_zero, norm_one] at h2
  rw [norm_mul, mul_comm, ← h2]
  exact mul_le_mul_of_nonneg_right h (norm_nonneg _)

end GlobalTheory.LambdaValuationPowers.ZetaCoef

namespace GlobalTheory.LambdaValuationPowers

open ZetaCoef

end GlobalTheory.LambdaValuationPowers
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.KummerCochainEqDlogExplicitReciprocity
section
noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ
open scoped Matrix

namespace GlobalTheory.RecOne

section Der

variable {R S M : Type*} [CommRing R] [CommRing S] [Algebra R S] [AddCommGroup M] [Module R M] [Module S M]

theorem smul_der_pow (d : Derivation R S M) (x : S) (n : ℕ) : x • d (x ^ n) = ((n : S) * x ^ n) • d x := by
  rcases n with _ | n
  · simp
  · rw [Derivation.leibniz_pow, ← Nat.cast_smul_eq_nsmul S, smul_smul, smul_smul]
    congr 1
    rw [Nat.add_sub_cancel]; ring

theorem rel_one (d : Derivation R S M) (e V Z p y : S) (L n : ℕ) (h1 : e • d V = y • d Z)
    (h2 : d (V ^ L) = p • d (Z ^ n)) :
    ((L : S) * V ^ L * Z * y - e * V * p * n * Z ^ n) • d Z = 0 := by
  have a1 := smul_der_pow d V L
  have a2 := smul_der_pow d Z n
  linear_combination (norm := module) (-((L : S) * V ^ L * Z)) • h1 - (e * Z) • a1 + (e * Z * V) • h2 +
    (e * V * p) • a2

theorem rel_two (d : Derivation R S M) (e V Z y y' : S) (n k c : ℕ) (h1 : e • d V = y • d Z)
    (h2 : e • d ((Z ^ n) ^ k * V) = y' • d (Z ^ c)) :
    (y' * c * Z ^ c - Z * (Z ^ n) ^ k * y - e * V * k * n * (Z ^ n) ^ k) • d Z = 0 := by
  have a1 := smul_der_pow d Z c
  have a2 := smul_der_pow d Z (n * k)
  rw [pow_mul, Nat.cast_mul] at a2
  rw [Derivation.leibniz] at h2
  linear_combination (norm := module) (Z * (Z ^ n) ^ k) • h1 - y' • a1 - Z • h2 + (e * V) • a2

end Der

theorem field_step {F : Type*} [Field F] (l L α u V Z ζ K p y y' Z' w w' w₂ k t c e : F) (hL : L ≠ 0) (hα : α ≠ 0)
    (hu : u ≠ 0) (hV : V ≠ 0) (hK : K ≠ 0)
    (h1 : l ^ 4 * (L * u * Z * y - l ^ 2 * V * p * (α * L) * ζ) = α * L * L * w)
    (h1' : l ^ 4 * (L * u * Z' * y' - l ^ 2 * (K * V) * p * (α * L) * ζ) = α * L * L * w')
    (h2 : l ^ 4 * (y' * c * Z' - Z * K * y - l ^ 2 * V * k * (α * L) * K) = α * L * L * w₂)
    (hc : c = 1 + t * L + e * L * L) :
    l ^ 6 * k - (l ^ 6 * (t * (ζ * p / u)) + (w' * u⁻¹ * (K * V)⁻¹ - w * u⁻¹ * V⁻¹)) =
      L * (l ^ 6 * e * (ζ * p * u⁻¹) + (t + e * L) * (w' * u⁻¹ * (K⁻¹ * V⁻¹)) - w₂ * (K⁻¹ * V⁻¹)) := by
  have h3 : (α * L * L) * (l ^ 6 * k * u * K * V - l ^ 6 * t * ζ * p * K * V - w' + w * K) =
      (α * L * L) * (L * (l ^ 6 * e * ζ * p * K * V + (t + e * L) * w' - w₂ * u)) := by
    subst hc
    linear_combination (-(L * u)) * h2 + (1 + t * L + e * L * L) * h1' - K * h1
  have h4 := mul_left_cancel₀ (mul_ne_zero (mul_ne_zero hα hL) hL) h3
  field_simp
  linear_combination h4

theorem kummer_eq_dlog_one : ∀ (l : ℕ) [Fact l.Prime], l ≠ 2 → ∃ c : ℕ, ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (A : ValuationSubring Ω), OverL l A →
  ∀ (m : ℕ) (ζ ζ' : Ω), IsPrimitiveRoot ζ (l ^ m) → ζ' ^ (l ^ m) = ζ →
  ∀ P : Polynomial Ω, (∀ x ∈ P.coeffs, x ∈ A ∧ ∀ s ∈ Ine (F := ℚ) A, s x = x) → P.eval ζ ∈ A → (P.eval ζ)⁻¹ ∈ A → P.eval ζ ≠ 0 →
  ∃ x ∈ A, ∀ s, s ∈ Ine (F := ℚ) A → cycMod ℚ Ω l m s = 1 → ∀ k t : ZMod (l ^ m),
    GlobalTheory.Col.KumVal m ζ (P.eval ζ) s k → s ζ' = ζ ^ t.val * ζ' →
    GlobalTheory.Glue.CgA A l m ((l : Ω) ^ c * (k.val : Ω))
      ((l : Ω) ^ c * ((t.val : Ω) * (ζ * (Polynomial.derivative P).eval ζ / P.eval ζ)) + (s x - x)) := by
  intro l hl hl2
  refine ⟨6, ?_⟩
  intro Ω _ _ _ A hA m ζ ζ' hζ hζ' P hP hu hu' hu0
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap ℚ Ω).injective
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  have hlp : l.Prime := Fact.out
  have hl0 : (l : Ω) ≠ 0 := Nat.cast_ne_zero.2 hlp.ne_zero
  have hpos : ∀ j : ℕ, 0 < l ^ j := fun j => pow_pos hlp.pos j
  haveI : ∀ j : ℕ, NeZero (l ^ j) := fun j => ⟨(hpos j).ne'⟩
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · refine ⟨0, A.zero_mem, fun s _ _ k t _ _ => ⟨0, A.zero_mem, ?_⟩⟩
    have hk : k.val = 0 := by have := ZMod.val_lt k; simpa using this
    have ht : t.val = 0 := by have := ZMod.val_lt t; simpa using this
    rw [hk, ht]; simp
  set φ : fixA A →+* Ω := A.subtype.comp (fixA A).subtype with hφ
  obtain ⟨Q, rfl⟩ : ∃ Q : Polynomial (fixA A), Q.map φ = P := by
    rw [← Polynomial.mem_lifts, Polynomial.lifts_iff_coeff_lifts]
    intro n
    by_cases h0 : P.coeff n = 0
    · exact ⟨0, by simp [h0]⟩
    · obtain ⟨h1, h2⟩ := hP _ (Polynomial.coeff_mem_coeffs h0)
      exact ⟨⟨⟨P.coeff n, h1⟩, h2⟩, rfl⟩
  have hev : ∀ (R : Polynomial (fixA A)) (x : A), ((Polynomial.aeval x R : A) : Ω) = (R.map φ).eval (x : Ω) := by
    intro R x
    rw [Polynomial.eval_map, Polynomial.aeval_def]
    exact Polynomial.hom_eval₂ R (algebraMap (fixA A) A) A.subtype x
  have hsev : ∀ s ∈ Ine (F := ℚ) A, ∀ (R : Polynomial (fixA A)) (x : Ω),
      s ((R.map φ).eval x) = (R.map φ).eval (s x) := by
    intro s hs R x
    rw [Polynomial.eval_map, Polynomial.eval_map]
    have h := Polynomial.hom_eval₂ R φ (s : Ω →+* Ω) x
    have e : (s : Ω →+* Ω).comp φ = φ := RingHom.ext fun a => a.2 s hs
    rw [e] at h
    exact h
  rw [Polynomial.derivative_map]
  set u := (Q.map φ).eval ζ with hudef
  set p := ((Polynomial.derivative Q).map φ).eval ζ with hpdef
  obtain ⟨V, hV⟩ := IsAlgClosed.exists_pow_nat_eq u (hpos m)
  have hV0 : V ≠ 0 := by
    rintro rfl
    exact hu0 (by rw [← hV, zero_pow (hpos m).ne'])
  have hVA : V ∈ A := mem_of_pow_mem A (hpos m).ne' (hV ▸ hu)
  have hVA' : V⁻¹ ∈ A := mem_of_pow_mem A (hpos m).ne' (by rw [inv_pow, hV]; exact hu')
  obtain ⟨α, hα⟩ := GlobalTheory.T.sq_prime_smul_kaehlerDerivation_eq_smul_rootOfUnity l hl2 Ω A hA ⟨V, hVA⟩
  obtain ⟨Z, hZ⟩ := IsAlgClosed.exists_pow_nat_eq ζ' (hpos α)
  have hZζ : Z ^ l ^ (α + m) = ζ := by rw [pow_add, pow_mul, hZ, hζ']
  have hZp : IsPrimitiveRoot Z (l ^ (α + m + m)) := by
    obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
    have h1 : ¬ Z ^ l ^ (α + (m' + 1) + m') = 1 := by
      rw [pow_add, pow_mul, hZζ]
      exact hζ.pow_ne_one_of_pos_of_lt (hpos m').ne' (Nat.pow_lt_pow_right hlp.one_lt (by omega))
    have h2 : Z ^ l ^ (α + (m' + 1) + m' + 1) = 1 := by
      rw [add_assoc (α + (m' + 1)), pow_add, pow_mul, hZζ, hζ.pow_eq_one]
    have h3 := orderOf_eq_prime_pow h1 h2
    have h4 := IsPrimitiveRoot.orderOf Z
    rwa [h3] at h4
  have hZA : Z ∈ A := mem_of_pow_mem A (hpos (α + m + m)).ne' (by rw [hZp.pow_eq_one]; exact A.one_mem)
  have hζA : ζ ∈ A := hZζ ▸ pow_mem hZA _
  have hζA' : ζ⁻¹ ∈ A := mem_of_pow_mem A (hpos m).ne' (by rw [inv_pow, hζ.pow_eq_one, inv_one]; exact A.one_mem)
  have hζ0 : ζ ≠ 0 := hζ.ne_zero (hpos m).ne'
  set VA : A := ⟨V, hVA⟩
  set ZA : A := ⟨Z, hZA⟩
  obtain ⟨y, hy⟩ := hα (α + m + m) (by omega) ZA hZp
  have hZAζ : ((ZA ^ l ^ (α + m) : A) : Ω) = ζ := by simpa using hZζ
  set pA : A := Polynomial.aeval (ZA ^ l ^ (α + m)) (Polynomial.derivative Q) with hpA
  have hpAp : (pA : Ω) = p := by rw [hpA, hev, hZAζ]
  have hpmem : p ∈ A := hpAp ▸ pA.2
  have hVu : VA ^ l ^ m = Polynomial.aeval (ZA ^ l ^ (α + m)) Q := by
    apply Subtype.ext
    rw [hev, hZAζ]
    simpa using hV
  have hd : dA A (VA ^ l ^ m) = pA • dA A (ZA ^ l ^ (α + m)) := by
    rw [hVu, Derivation.map_aeval]
  obtain ⟨w, hwA, hw⟩ := GlobalTheory.T.annihilator_kaehlerDerivation_primitiveRoot l hl2 Ω A hA _ ZA hZp _ (rel_one (dA A) _ VA ZA pA y _ _ hy hd)
  have hw1 : (l : Ω) ^ 4 * ((l : Ω) ^ m * u * Z * y - (l : Ω) ^ 2 * V * p * ((l : Ω) ^ α * (l : Ω) ^ m) * ζ) =
      (l : Ω) ^ α * (l : Ω) ^ m * (l : Ω) ^ m * w := by
    rw [← hV, ← hpAp, ← hZζ, ← pow_add, ← pow_add, ← hw]
    push_cast
    rfl
  refine ⟨w * u⁻¹ * V⁻¹, mul_mem (mul_mem hwA hu') hVA', ?_⟩
  rintro s hs hcyc k t ⟨v, hv, hsv⟩ hst
  have hsA : ∀ x ∈ A, s x ∈ A := fun x hx => (apply_mem_iff_of_mem_Dec (Ine_le_Dec A hs) x).2 hx
  have hsζ : s ζ = ζ := GlobalTheory.Col.fix_of_cycMod le_rfl hcyc hζ.pow_eq_one
  have hsu : s u = u := by rw [hudef, hsev s hs, hsζ]
  have hsp : s p = p := by rw [hpdef, hsev s hs, hsζ]
  have hsV : s V = ζ ^ k.val * V := by
    have h1 : (v / V) ^ l ^ m = 1 := by rw [div_pow, hv, hV, div_self hu0]
    obtain ⟨j, -, hj⟩ := hζ.eq_pow_of_pow_eq_one h1
    have h2 : v = ζ ^ j * V := by rw [hj]; field_simp
    rw [h2, map_mul, map_pow, hsζ] at hsv
    exact mul_left_cancel₀ (pow_ne_zero j hζ0) (by rw [hsv]; ring)
  obtain ⟨c, -, hc⟩ := hZp.eq_pow_of_pow_eq_one (ξ := s Z) (by rw [← map_pow, hZp.pow_eq_one, map_one])
  have htr := GlobalTheory.T.inertia_transports_kaehler_relations_over_invariants Ω A s hs ((l : A) ^ 2) VA y ZA ((l : A) ^ 2) ((ZA ^ l ^ (α + m)) ^ k.val * VA)
    ⟨s y, hsA _ y.2⟩ (ZA ^ c) (by simp) (by push_cast; rw [hZζ]; exact hsV.symm) rfl (by simpa using hc) hy
  obtain ⟨w₂, hw₂A, hw₂⟩ := GlobalTheory.T.annihilator_kaehlerDerivation_primitiveRoot l hl2 Ω A hA _ ZA hZp _ (rel_two (dA A) _ VA ZA y _ _ _ _ hy htr)
  have hw2 : (l : Ω) ^ 4 * (s y * (c : Ω) * s Z - Z * ζ ^ k.val * y -
      (l : Ω) ^ 2 * V * (k.val : Ω) * ((l : Ω) ^ α * (l : Ω) ^ m) * ζ ^ k.val) =
      (l : Ω) ^ α * (l : Ω) ^ m * (l : Ω) ^ m * w₂ := by
    rw [← hc, ← hZζ, ← pow_add, ← pow_add, ← hw₂]
    push_cast
    rfl
  have hw1' := congrArg s hw1
  simp only [map_mul, map_sub, map_pow, map_natCast, hsu, hsp, hsζ, hsV] at hw1'
  obtain ⟨e, he⟩ : ∃ e : ℤ, (c : Ω) = 1 + (t.val : Ω) * (l : Ω) ^ m + (e : Ω) * (l : Ω) ^ m * (l : Ω) ^ m := by
    have h1 : Z ^ (c * l ^ α) = Z ^ (l ^ (α + m) * t.val + l ^ α) := by
      rw [pow_mul, hc, ← map_pow, hZ, hst, pow_add, pow_mul, hZζ, hZ]
    rw [(hZp.isOfFinOrder (hpos _).ne').pow_eq_pow_iff_modEq, ← hZp.eq_orderOf, Nat.modEq_iff_dvd] at h1
    obtain ⟨e, he⟩ := h1
    refine ⟨-e, ?_⟩
    have h2 := congrArg (Int.cast : ℤ → Ω) he
    push_cast at h2
    apply mul_left_cancel₀ (pow_ne_zero α hl0)
    push_cast
    linear_combination -h2
  have hfin := field_step (l : Ω) ((l : Ω) ^ m) ((l : Ω) ^ α) u V Z ζ (ζ ^ k.val) p y (s y) (s Z) w (s w) w₂
    (k.val : Ω) (t.val : Ω) (c : Ω) (e : Ω) (pow_ne_zero _ hl0) (pow_ne_zero _ hl0) hu0 hV0 (pow_ne_zero _ hζ0)
    hw1 hw1' hw2 he
  have hlA : (l : Ω) ∈ A := natCast_mem A l
  have hKV : (ζ ^ k.val)⁻¹ * V⁻¹ ∈ A := mul_mem (by rw [← inv_pow]; exact pow_mem hζA' _) hVA'
  refine ⟨_, ?_, by rw [map_mul, map_mul, map_inv₀, map_inv₀, hsu, hsV]; exact hfin⟩
  refine sub_mem (add_mem (mul_mem (mul_mem (pow_mem hlA _) (intCast_mem A e)) (mul_mem (mul_mem hζA hpmem) hu'))
    (mul_mem (add_mem (natCast_mem A _) (mul_mem (intCast_mem A e) (pow_mem hlA _)))
      (mul_mem (mul_mem (hsA w hwA) hu') hKV))) (mul_mem hw₂A hKV)

end GlobalTheory.RecOne
end
end

