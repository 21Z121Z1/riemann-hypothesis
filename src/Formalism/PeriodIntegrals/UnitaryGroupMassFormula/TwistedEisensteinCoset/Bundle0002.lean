import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.TwistedEisensteinCoset.IaDivDown
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.TwistedEisensteinCoset.IntegralApproximationByInteger
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.TwistedCharacterOne.IsIntegralAtSuperdiagonalSum

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.TwistedEisensteinCoset.IsUnitRedP
section
open NumberField IsDedekindDomain Module

noncomputable section

namespace PI.TwistedEisensteinNonvanishing.W

open Loc LocE

section Red

variable {E : Type} [Field E] [NumberField E] [StarRing E] (P : HeightOneSpectrum (𝓞 E))

private lemma mk_mul_reduction_eq_mk {a : E} {r s : 𝓞 E} (hs : s ∉ P.asIdeal)
    (h : algebraMap (𝓞 E) E s * a = algebraMap (𝓞 E) E r) :
    redP P a * Ideal.Quotient.mk P.asIdeal s = Ideal.Quotient.mk P.asIdeal r := by
  haveI := P.isMaximal
  letI := Ideal.Quotient.field P.asIdeal
  have hs0 : Ideal.Quotient.mk P.asIdeal s ≠ 0 := fun h0 => hs (Ideal.Quotient.eq_zero_iff_mem.1 h0)
  have hex : ∃ c : 𝓞 E ⧸ P.asIdeal, ∃ r s : 𝓞 E, s ∉ P.asIdeal ∧
      algebraMap (𝓞 E) E s * a = algebraMap (𝓞 E) E r ∧
      Ideal.Quotient.mk P.asIdeal s * c = Ideal.Quotient.mk P.asIdeal r :=
    ⟨Ideal.Quotient.mk P.asIdeal r * (Ideal.Quotient.mk P.asIdeal s)⁻¹, r, s, hs, h, by
      field_simp⟩
  unfold redP
  rw [dif_pos hex]
  obtain ⟨r', s', hs', h', hc'⟩ := hex.choose_spec
  have hs'0 : Ideal.Quotient.mk P.asIdeal s' ≠ 0 :=
    fun h0 => hs' (Ideal.Quotient.eq_zero_iff_mem.1 h0)
  have hE : algebraMap (𝓞 E) E (s' * r) = algebraMap (𝓞 E) E (s * r') := by
    rw [map_mul, map_mul, ← h, ← h']
    ring
  have hO : s' * r = s * r' := FaithfulSMul.algebraMap_injective (𝓞 E) E hE
  have hQ : Ideal.Quotient.mk P.asIdeal s' * Ideal.Quotient.mk P.asIdeal r =
      Ideal.Quotient.mk P.asIdeal s * Ideal.Quotient.mk P.asIdeal r' := by
    rw [← map_mul, ← map_mul, hO]
  apply mul_left_cancel₀ hs'0
  rw [hQ, ← hc']
  ring

theorem reduction_mul' {a b : E} (ha : IntAt P a) (hb : IntAt P b) : redP P (a * b) = redP P a * redP P b := by
  haveI := P.isMaximal
  letI := Ideal.Quotient.field P.asIdeal
  obtain ⟨r, s, hs, h⟩ := ha
  obtain ⟨r', s', hs', h'⟩ := hb
  have hss : s * s' ∉ P.asIdeal := fun hm => (P.isPrime.mem_or_mem hm).elim hs hs'
  have hab : algebraMap (𝓞 E) E (s * s') * (a * b) = algebraMap (𝓞 E) E (r * r') := by
    rw [map_mul, map_mul, ← h, ← h']
    ring
  have h1 := mk_mul_reduction_eq_mk P hss hab
  have ha' := mk_mul_reduction_eq_mk P hs h
  have hb' := mk_mul_reduction_eq_mk P hs' h'
  have hss0 : Ideal.Quotient.mk P.asIdeal (s * s') ≠ 0 :=
    fun h0 => hss (Ideal.Quotient.eq_zero_iff_mem.1 h0)
  apply mul_right_cancel₀ hss0
  rw [h1, map_mul, map_mul, ← ha', ← hb']
  ring

theorem reduction_one' : redP P (1 : E) = 1 := by
  have h1 : (1 : 𝓞 E) ∉ P.asIdeal := fun h => P.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h)
  have h := mk_mul_reduction_eq_mk P (a := 1) (r := 1) h1 (by simp)
  simpa using h

theorem isUnit_redP {w : E} (hw : UnitAt P w) : IsUnit (redP P w) := by
  obtain ⟨hw0, hi, hi'⟩ := hw
  have h := reduction_mul' P hi hi'
  rw [mul_inv_cancel₀ hw0, reduction_one'] at h
  exact IsUnit.of_mul_eq_one (b := redP P w⁻¹) h.symm

end Red

theorem muNe_of (hN : NTAll) : MuNeP := by
  intro E K _ _ _ _ P hp hq cq χ hcq a ha
  obtain ⟨e, w, hae, hw0, hw1, hw2⟩ := hN.2.2.1 E P hp hq a ha
  have hex : ∃ z : ℤ, IsUnit (redP P (a / (qOf P : E) ^ z)) := by
    refine ⟨e, ?_⟩
    have : a / (qOf P : E) ^ e = w := by
      rw [hae]
      field_simp [zpow_ne_zero e (qE_ne P hp)]
    rw [this]
    exact isUnit_redP P ⟨hw0, hw1, hw2⟩
  have hspec : IsUnit (redP P (a / (qOf P : E) ^ vP P (qOf P) a)) := Classical.epsilon_spec hex
  unfold locChar
  refine mul_ne_zero (zpow_ne_zero _ hcq) ?_
  unfold unitV
  rw [dif_pos hspec]
  exact Units.ne_zero _

theorem omStep_of (hJ : JLawP) (hM : MuNeP) : OmStepP := by
  intro E K _ _ _ _ P hp hq sq cq hsq hcq ξ k₀ r c' n' c n kj h1 h2 h3 h4 h5 g₀ h ρ κ hκ
  obtain ⟨lam, hlam, hlaw⟩ := hJ E K P hp hq ξ k₀ r c' n' c n kj h1 h2 h3 h4 h5 κ hκ
  have hdet : ∀ f : (Fin (n + c) → E) ≃ₗ[E] (Fin (n + c) → E), locChar (qOf P) cq ξ⁻¹ (LinearEquiv.det f : E) ≠ 0 :=
    fun f => hM E K P hp hq cq ξ⁻¹ hcq _ (Units.ne_zero _)
  refine ⟨(locChar (qOf P) cq ξ⁻¹ (LinearEquiv.det (ρ * h * κ) : E))⁻¹ * sq ^ (vP P (qOf P) (LinearEquiv.det (ρ * h * κ) : E) * ((n' + c' : ℕ) : ℤ)) * lam /
      ((locChar (qOf P) cq ξ⁻¹ (LinearEquiv.det h : E))⁻¹ * sq ^ (vP P (qOf P) (LinearEquiv.det h : E) * ((n' + c' : ℕ) : ℤ))), ?_, fun x => ?_⟩
  · have := hdet (ρ * h * κ)
    have := hdet h
    refine div_ne_zero (mul_ne_zero (mul_ne_zero (inv_ne_zero ‹_›) (zpow_ne_zero _ hsq)) hlam)
      (mul_ne_zero (inv_ne_zero ‹_›) (zpow_ne_zero _ hsq))
  · have ey : (ρ * h * κ).symm.toLinearMap ∘ₗ x ∘ₗ g₀.toLinearMap =
        κ.symm.toLinearMap ∘ₗ (h.symm.toLinearMap ∘ₗ ((ρ⁻¹).toLinearMap ∘ₗ x) ∘ₗ g₀.toLinearMap) := by
      apply LinearMap.ext
      intro v
      simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
      rw [LinearEquiv.symm_apply_eq]
      show _ = ρ (h (κ (κ.symm _)))
      rw [LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
      show _ = (ρ * ρ⁻¹) _
      rw [mul_inv_cancel]
      rfl
    unfold om
    rw [ey, hlaw]
    have a1 := hdet (ρ * h * κ)
    have a0 := hdet h
    have s0 : sq ^ (vP P (qOf P) (LinearEquiv.det h : E) * ((n' + c' : ℕ) : ℤ)) ≠ 0 := zpow_ne_zero _ hsq
    field_simp

end PI.TwistedEisensteinNonvanishing.W
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.TwistedEisensteinCoset.TwistedEisensteinOfHypotheses
section
open NumberField IsDedekindDomain Module

noncomputable section

namespace PI.TwistedEisensteinNonvanishing.W

open Loc LocE

theorem psi_ne {E K : Type} [Field E] [NumberField E] [StarRing E] [Field K] {D : ℕ}
    {P : HeightOneSpectrum (𝓞 E)} {psi : E → K} (hpsi : PsiOk D P psi) (z : E) : psi z ≠ 0 := by
  obtain ⟨hmul, hint, hout⟩ := hpsi
  by_cases hz : IntAt P ((qOf P : E) ^ D * z)
  · have hz' : IntAt P ((qOf P : E) ^ D * (-z)) := by
      obtain ⟨r, s, hs, hrs⟩ := hz
      exact ⟨-r, s, hs, by rw [mul_neg, mul_neg, hrs, map_neg]⟩
    have h0 : IntAt P 0 := ⟨0, 1, (Ideal.ne_top_iff_one _).mp P.isPrime.ne_top, by simp⟩
    have h := hmul z (-z) hz hz'
    rw [add_neg_cancel, hint 0 h0] at h
    intro hz0
    rw [hz0, zero_mul] at h
    exact one_ne_zero h
  · rw [hout z hz]
    exact one_ne_zero

private lemma intAt_add_twisted_eisenstein_coset {E : Type} [Field E] [NumberField E] {P : HeightOneSpectrum (𝓞 E)} {a b : E}
    (ha : IntAt P a) (hb : IntAt P b) : IntAt P (a + b) := by
  obtain ⟨r1, s1, hs1, h1⟩ := ha
  obtain ⟨r2, s2, hs2, h2⟩ := hb
  refine ⟨r1 * s2 + r2 * s1, s1 * s2, fun h => ?_, ?_⟩
  · rcases P.isPrime.mem_or_mem h with h' | h'
    · exact hs1 h'
    · exact hs2 h'
  · rw [map_mul, map_add, map_mul, map_mul, ← h1, ← h2]
    ring

private lemma intAt_neg_twisted_eisenstein_coset {E : Type} [Field E] [NumberField E] {P : HeightOneSpectrum (𝓞 E)} {a : E}
    (h : IntAt P a) : IntAt P (-a) := by
  obtain ⟨r, s, hs, hr⟩ := h
  exact ⟨-r, s, hs, by rw [mul_neg, hr, map_neg]⟩

private lemma intAt_qOf_pow_mul {E : Type} [Field E] [NumberField E] {P : HeightOneSpectrum (𝓞 E)} (k : ℕ) {a : E}
    (h : IntAt P a) : IntAt P ((qOf P : E) ^ k * a) := by
  obtain ⟨r, s, hs, hr⟩ := h
  refine ⟨(qOf P : 𝓞 E) ^ k * r, s, hs, ?_⟩
  rw [map_mul, map_pow, map_natCast, ← hr]
  ring

theorem key_pt {E K : Type} [Field E] [NumberField E] [StarRing E] [Field K] {D j : ℕ} (hjD : j ≤ D)
    {P : HeightOneSpectrum (𝓞 E)} {psi : E → K} (hpsi : PsiOk D P psi) {C gx gy : K} (hC : C ≠ 0)
    {cx cy c0 : E} (hg : gx = C * gy) (hc : cy = cx + c0)
    (hbx : gx ≠ 0 → IntAt P ((qOf P : E) ^ j * cx)) (hby : gy ≠ 0 → IntAt P ((qOf P : E) ^ j * cy)) :
    gx * psi (-cx) = (C * psi c0) * (gy * psi (-cy)) := by
  by_cases hgy : gy = 0
  · rw [hg, hgy]
    ring
  · have hgx : gx ≠ 0 := by
      rw [hg]
      exact mul_ne_zero hC hgy
    have ix := hbx hgx
    have iy := hby hgy
    have lift : ∀ t : E, IntAt P ((qOf P : E) ^ j * t) → IntAt P ((qOf P : E) ^ D * t) := by
      intro t ht
      have h := intAt_qOf_pow_mul (D - j) ht
      rwa [← mul_assoc, ← pow_add, Nat.sub_add_cancel hjD] at h
    have i_cx := lift cx ix
    have i_cy := lift cy iy
    have i_c0 : IntAt P ((qOf P : E) ^ D * c0) := by
      have e : (qOf P : E) ^ D * c0 = (qOf P : E) ^ D * cy + -((qOf P : E) ^ D * cx) := by
        rw [hc]
        ring
      rw [e]
      exact intAt_add_twisted_eisenstein_coset i_cy (intAt_neg_twisted_eisenstein_coset i_cx)
    have i_ncy : IntAt P ((qOf P : E) ^ D * (-cy)) := by
      rw [mul_neg]
      exact intAt_neg_twisted_eisenstein_coset i_cy
    have hsplit := hpsi.1 (-cy) c0 i_ncy i_c0
    have e : -cy + c0 = -cx := by
      rw [hc]
      ring
    rw [e] at hsplit
    rw [hsplit, hg]
    ring

theorem RS_mul {E K : Type} [Field E] [NumberField E] [Field K] (P : HeightOneSpectrum (𝓞 E)) {ι : Type}
    [Fintype ι] [DecidableEq ι] (A B : ℕ) (C : K) (H : (ι → E) → K) :
    RS P A B (fun t => C * H t) = C * RS P A B H := by
  simp only [RS, ← Finset.mul_sum]
  ring

theorem core {E K : Type} [Field E] [NumberField E] [StarRing E] [Field K] (P : HeightOneSpectrum (𝓞 E))
    (hp : (Ideal.absNorm P.asIdeal).Prime) (hq : ((Ideal.absNorm P.asIdeal : ℕ) : 𝓞 E) ∉ P.asIdeal ^ 2)
    (hq0 : ((qOf P : ℕ) : K) ≠ 0) (hStab : StabP) (hCoV : CoVP) (hXX : XXP) (hTA : TrAffP)
    (hRX : ResXSurjP) (hCA : ChArgP) (hCB : ChArgBddP)
    {n' c' n c D j : ℕ} (hjD : j ≤ D) {psi : E → K} (hpsi : PsiOk D P psi)
    (G G' : SF E K (n' + c') (n + c)) (ρ : (Fin (n + c) → E) ≃ₗ[E] (Fin (n + c) → E)) (hρ : ρ ∈ R1 E n c)
    (C : K) (hC : C ≠ 0) (hCeq : ∀ x, G' x = C * G (ρ.toLinearMap ∘ₗ x))
    (hS : ∀ x, G x ≠ 0 → ∀ (s : ℕ) (l : Fin (n + c)), IntAt P ((qOf P : E) ^ j * x (eN E (n' + c') s) l))
    (hS' : ∀ x, G' x ≠ 0 → ∀ (s : ℕ) (l : Fin (n + c)), IntAt P ((qOf P : E) ^ j * x (eN E (n' + c') s) l))
    (hH : ∀ y : (Fin n' → E) →ₗ[E] (Fin n → E),
      Good P j j (fun t : FC n' c' n c → E => G (xx1 y t) * psi (-chArg (xx1 y t))))
    (hne : ∃ A0 B0 : ℕ, ∀ A' B', A0 ≤ A' → B0 ≤ B' →
      (fun xj : (Fin n' → E) →ₗ[E] (Fin n → E) =>
        RS P A' B' (fun t : FC n' c' n c → E => G (xx1 xj t) * psi (-chArg (xx1 xj t)))) ≠ 0) :
    ∃ A0 B0 : ℕ, ∀ A' B', A0 ≤ A' → B0 ≤ B' →
      (fun xj : (Fin n' → E) →ₗ[E] (Fin n → E) =>
        RS P A' B' (fun t : FC n' c' n c → E => G' (xx1 xj t) * psi (-chArg (xx1 xj t)))) ≠ 0 := by
  obtain ⟨L, hL⟩ := hTA E n' c' n c ρ hρ
  obtain ⟨cT, hcT, hcov⟩ := hCoV E K P hp hq hq0 (FC n' c' n c) L (Tr ρ 0)
  obtain ⟨a', b', hab⟩ := hcov j j
  have key : ∀ (xj : (Fin n' → E) →ₗ[E] (Fin n → E)) (t : FC n' c' n c → E),
      G' (xx1 xj t) * psi (-chArg (xx1 xj t)) =
        (C * psi (chArg (ρ.toLinearMap ∘ₗ xx1 (0 : (Fin n' → E) →ₗ[E] (Fin n → E)) (0 : FC n' c' n c → E)))) *
          (G (xx1 (resX ρ ∘ₗ xj) (L t + Tr ρ 0)) * psi (-chArg (xx1 (resX ρ ∘ₗ xj) (L t + Tr ρ 0)))) := by
    intro xj t
    have e1 : ρ.toLinearMap ∘ₗ xx1 xj t = xx1 (resX ρ ∘ₗ xj) (L t + Tr ρ 0) := by
      rw [hXX E n' c' n c ρ hρ xj t, hL t]
    rw [← e1]
    exact key_pt hjD hpsi hC (hCeq _) (hCA E n' c' n c ρ hρ xj t)
      (fun h0 => hCB E P n' c' n c j _ (hS' _ h0)) (fun h0 => hCB E P n' c' n c j _ (hS _ h0))
  obtain ⟨A0, B0, hAB⟩ := hne
  obtain ⟨y, hy⟩ : ∃ y : (Fin n' → E) →ₗ[E] (Fin n → E),
      RS P j j (fun t : FC n' c' n c → E => G (xx1 y t) * psi (-chArg (xx1 y t))) ≠ 0 := by
    obtain ⟨y, hy⟩ := Function.ne_iff.1 (hAB (max A0 j) (max B0 j) (le_max_left _ _) (le_max_left _ _))
    refine ⟨y, ?_⟩
    simp only [Pi.zero_apply] at hy
    rwa [← hStab E K P hp hq hq0 _ j j _ (hH y) _ _ (le_max_right _ _) (le_max_right _ _)]
  obtain ⟨xj, rfl⟩ := hRX E n' n c ρ hρ y
  obtain ⟨hg, heq⟩ := hab _ (hH (resX ρ ∘ₗ xj))
  refine ⟨a', b', fun A' B' hA' hB' hz => ?_⟩
  have h1 := congrFun hz xj
  simp only [Pi.zero_apply] at h1
  rw [show (fun t : FC n' c' n c → E => G' (xx1 xj t) * psi (-chArg (xx1 xj t))) = fun t =>
      (C * psi (chArg (ρ.toLinearMap ∘ₗ xx1 (0 : (Fin n' → E) →ₗ[E] (Fin n → E)) (0 : FC n' c' n c → E)))) *
        (G (xx1 (resX ρ ∘ₗ xj) (L t + Tr ρ 0)) * psi (-chArg (xx1 (resX ρ ∘ₗ xj) (L t + Tr ρ 0))))
      from funext (key xj), RS_mul, hStab E K P hp hq hq0 _ a' b' _ hg A' B' hA' hB', heq] at h1
  exact mul_ne_zero (mul_ne_zero hC (psi_ne hpsi _)) (mul_ne_zero hcT hy) h1

theorem twisted_eisenstein_of_hypotheses (hStab : StabP) (hCoV : CoVP) (hOm : OmStepP) (hPS : PhiSuppP) (hPP : PhiPerP)
    (hBE : BddEntP) (hGS : GSuppP) (hGP : GPerP) (hHG : HGoodP) (hCB : ChArgBddP) (hXX : XXP)
    (hTA : TrAffP) (hRX : ResXSurjP) (hCA : ChArgP) : PI.TwistedEisensteinNonvanishing.TwistedEisensteinNonvanishing := by
  intro E K _ _ _ _ R P hp hq psi sq cq ξ hpsi hsq hcq i hi hal h h' hbal hbh hbh' hdc hne
  obtain ⟨r, hr, κ, hκ, rfl⟩ := hdc
  have m1 : i ≤ i * (R.t + 1) := Nat.le_mul_of_pos_right i (Nat.succ_pos _)
  have m2 : i + 1 ≤ (i + 1) * (R.t + 1) := Nat.le_mul_of_pos_right _ (Nat.succ_pos _)
  have hk := R.m_add_three_le_k
  have s1 : R.r = (R.k + (i + 1)) + cOf R (i + 1) := by
    unfold Ranks.r cOf
    omega
  have s3 : R.k + (i + 1) ≤ R.N (i + 1) := by
    unfold Ranks.N
    omega
  have s4 : R.r ≤ R.N i + cOf R i := by
    unfold Ranks.r Ranks.N cOf
    omega
  have s5 : R.k ≤ R.N i := by
    unfold Ranks.N
    omega
  have s6 : R.k ≤ R.N (i + 1) := by
    unfold Ranks.N
    omega
  have s7 : cOf R (i + 1) < cOf R i := by
    unfold cOf
    omega
  by_cases hq0 : ((qOf P : ℕ) : K) = 0
  · exfalso
    have hFC : Nonempty (FC (R.N i) (cOf R i) (R.N (i + 1)) (cOf R (i + 1))) :=
      ⟨⟨(⟨0, by omega⟩, ⟨R.N i + cOf R (i + 1), by omega⟩), by
        show IsFree (R.N i) (R.N (i + 1)) (cOf R (i + 1)) 0 (R.N i + cOf R (i + 1))
        unfold IsFree
        omega⟩⟩
    obtain ⟨A0, B0, hAB⟩ := hne
    refine hAB A0 (B0 + 1) le_rfl (Nat.le_succ _) ?_
    funext xj
    show (((qOf P : K) ^ (B0 + 1))⁻¹) ^ Fintype.card (FC (R.N i) (cOf R i) (R.N (i + 1)) (cOf R (i + 1))) * _ = 0
    rw [hq0, zero_pow (Nat.succ_ne_zero _), inv_zero, zero_pow Fintype.card_ne_zero, zero_mul]
  have hρ : r⁻¹ ∈ R1 E (R.N (i + 1)) (cOf R (i + 1)) := inv_mem hr
  obtain ⟨C, hC, hCeq⟩ := hOm E K P hp hq sq cq hsq hcq ξ R.k R.r (cOf R i) (R.N i) (cOf R (i + 1)) (R.N (i + 1))
    (R.k + (i + 1)) s1 (Nat.le_add_right _ _) s3 s4 s5 hal h r κ hκ
  obtain ⟨bh1, bh2⟩ := hBE E P R (i + 1) h hbh
  obtain ⟨bh1', -⟩ := hBE E P R (i + 1) (r * h * κ) hbh'
  obtain ⟨ba1, ba2⟩ := hBE E P R i hal hbal
  have hPhiS := hPS E K P (qOf P) ξ R.k R.r (cOf R i) (R.N i) (cOf R (i + 1)) (R.N (i + 1)) s6 s5
  have hPhiP := hPP E K P hp hq ξ R.k R.r (cOf R i) (R.N i) (cOf R (i + 1)) (R.N (i + 1))
  have gS := hGS E K P hp _ _ (locChar (qOf P) cq ξ⁻¹) (vP P (qOf P)) sq hal h _ (i + 1) hPhiS ba2 bh1
  have gS' := hGS E K P hp _ _ (locChar (qOf P) cq ξ⁻¹) (vP P (qOf P)) sq hal (r * h * κ) _ (i + 1) hPhiS ba2 bh1'
  have gP := hGP E K P hp _ _ (locChar (qOf P) cq ξ⁻¹) (vP P (qOf P)) sq hal h _ i hPhiP ba1 bh2
  have hHg := hHG E K P hp (R.N i) (cOf R i) (R.N (i + 1)) (cOf R (i + 1)) (2 * R.m) (i + 1) (by omega) psi hpsi _ gS gP
  exact core P hp hq hq0 hStab hCoV hXX hTA hRX hCA hCB (D := 2 * R.m) (j := i + 1) (by omega) hpsi _ _ r⁻¹ hρ
    C hC hCeq gS gS' hHg hne

end PI.TwistedEisensteinNonvanishing.W
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.TwistedEisensteinCoset.UnfoldingMatrixFreeCoordinate
section
open NumberField IsDedekindDomain Module

noncomputable section

namespace PI.TwistedEisensteinNonvanishing.W

open Loc LocE

section Vec

variable {E : Type} [Field E]

theorem gh_eN_lt {N s : ℕ} (h : s < N) : eN E N s = Pi.single (⟨s, h⟩ : Fin N) 1 := by
  funext l
  simp [eN, Pi.single_apply, Fin.ext_iff]

theorem gh_eN_ge {N s : ℕ} (h : N ≤ s) : eN E N s = 0 := by
  funext l
  have := l.2
  simp only [eN, Pi.zero_apply]
  rw [if_neg (by omega)]

theorem gh_decomp {N : ℕ} (v : Fin N → E) : v = ∑ m : Fin N, v m • eN E N m.1 := by
  funext l
  simp [eN, Finset.sum_apply, Fin.val_inj]

theorem gh_apply {M N : ℕ} (f : (Fin M → E) →ₗ[E] (Fin N → E)) (v : Fin M → E) (l : Fin N) :
    f v l = ∑ m : Fin M, v m * f (eN E M m.1) l := by
  conv_lhs => rw [gh_decomp v]
  simp [map_sum, Finset.sum_apply, mul_comm]

theorem gh_atN_add {N : ℕ} (v w : Fin N → E) (i : ℕ) : atN (v + w) i = atN v i + atN w i := by
  unfold atN
  split_ifs <;> simp

theorem gh_chArg_add {n' c' n c : ℕ} (x z : (Fin (n' + c') → E) →ₗ[E] (Fin (n + c) → E)) :
    chArg (n := n) (c := c) (x + z) = chArg (n := n) (c := c) x + chArg (n := n) (c := c) z := by
  unfold chArg
  simp [LinearMap.add_apply, gh_atN_add, Finset.sum_add_distrib]

theorem unfolding_matrix_free_coordinate {n' c' n c : ℕ} (y : (Fin n' → E) →ₗ[E] (Fin n → E)) (t : FC n' c' n c → E) (p : FC n' c' n c) :
    xx1 y t (eN E (n' + c') p.1.2.1) p.1.1 = t p := by
  have he : eN E (n' + c') p.1.2.1 = Pi.single p.1.2 1 := gh_eN_lt p.1.2.2
  rw [he]
  unfold xx1
  rw [Matrix.toLin'_apply, Matrix.mulVec_single_one]
  exact dif_pos p.2

private theorem xx1_eN_apply {n' c' n c : ℕ} (y : (Fin n' → E) →ₗ[E] (Fin n → E))
    (t : FC n' c' n c → E) {s : ℕ} (hs : s < n' + c') (l : Fin (n + c)) :
    xx1 y t (eN E (n' + c') s) l =
      if hf : IsFree n' n c l.1 s then t ⟨(l, ⟨s, hs⟩), hf⟩
      else if hs' : s < n' then (if hl : l.1 < n then LinearMap.toMatrix' y ⟨l.1, hl⟩ ⟨s, hs'⟩ else 0)
      else if l.1 = n + (s - n') then 1 else 0 := by
  rw [gh_eN_lt hs]
  unfold xx1
  rw [Matrix.toLin'_apply, Matrix.mulVec_single_one]
  rfl

theorem unfolding_matrix_sub {n' c' n c : ℕ} (y : (Fin n' → E) →ₗ[E] (Fin n → E)) (t t' : FC n' c' n c → E) (s : ℕ) (l : Fin (n + c)) :
    (xx1 y t - xx1 y t') (eN E (n' + c') s) l =
      if hs : s < n' + c' then (if hf : IsFree n' n c l.1 s then t ⟨(l, ⟨s, hs⟩), hf⟩ - t' ⟨(l, ⟨s, hs⟩), hf⟩ else 0) else 0 := by
  by_cases hs : s < n' + c'
  · rw [dif_pos hs, LinearMap.sub_apply, Pi.sub_apply, xx1_eN_apply y t hs, xx1_eN_apply y t' hs]
    split_ifs <;> first | rfl | exact sub_self _
  · rw [dif_neg hs, gh_eN_ge (not_lt.mp hs)]
    simp

end Vec

section Bd

variable {E : Type} [Field E] [NumberField E] (P : HeightOneSpectrum (𝓞 E))

end Bd

theorem character_argument_bounded : ChArgBddP := by
  intro E _ _ P n' c' n c j x hx
  unfold chArg
  rw [Finset.mul_sum]
  apply ia_sum (P := P)
  intro i _
  unfold atN
  split_ifs with h
  · exact hx _ _
  · rw [mul_zero]; exact ia_zero (P := P)

theorem translated_function_support : GSuppP := by
  intro E K _ _ _ P hp a b mu v sq g₀ h Φ j hΦ hg hh x hx s l
  set y := h.symm.toLinearMap ∘ₗ x ∘ₗ g₀.toLinearMap with hy
  have hy0 : Φ y ≠ 0 := by
    intro h0; apply hx; simp only [om]; rw [← hy, h0, mul_zero]
  have hyI := hΦ y hy0
  set w := y (g₀.symm (eN E a s)) with hw
  have e1 : x (eN E a s) l = h w l := by simp [hw, hy]
  have e2 := gh_apply h.toLinearMap w l
  simp only [LinearEquiv.coe_coe] at e2
  rw [e1, e2, Finset.mul_sum]
  apply ia_sum (P := P)
  intro m _
  rw [mul_left_comm]
  refine ia_mul (P := P) ?_ (hh m.1 l)
  have e3 := gh_apply y (g₀.symm (eN E a s)) m
  rw [← hw] at e3
  rw [e3]
  apply ia_sum (P := P)
  intro k _
  exact ia_mul (P := P) (hg s k) (hyI k.1 m)

theorem translated_function_invariance : GPerP := by
  intro E K _ _ _ P hp a b mu v sq g₀ h Φ e hΦ hg hh x δ hδ
  have hq : (qOf P : E) ≠ 0 := qE_ne (P := P) hp
  simp only [om]
  congr 1
  rw [LinearMap.add_comp, LinearMap.comp_add]
  apply hΦ
  intro s l
  have e1 := gh_apply h.symm.toLinearMap (δ (g₀ (eN E a s))) l
  simp only [LinearEquiv.coe_coe] at e1
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
  rw [e1, Finset.sum_div]
  apply ia_sum (P := P)
  intro k _
  rw [gh_apply δ (g₀ (eN E a s)) k, Finset.sum_mul, Finset.sum_div]
  apply ia_sum (P := P)
  intro m _
  have e3 : g₀ (eN E a s) m * δ (eN E a m.1) k * h.symm (eN E b k.1) l / (qOf P : E)
      = ((qOf P : E) ^ e * g₀ (eN E a s) m) * (δ (eN E a m.1) k / (qOf P : E) ^ (e + 1))
        * h.symm (eN E b k.1) l := by
    field_simp
    ring
  rw [e3]
  exact ia_mul (P := P) (ia_mul (P := P) (hg s m) (hδ m.1 k)) (hh k.1 l)

theorem unfolding_integrand_good : HGoodP := by
  intro E K _ _ _ _ P hp n' c' n c D j hjD psi hpsi G hGs hGp y
  have hq : (qOf P : E) ≠ 0 := qE_ne (P := P) hp
  refine ⟨?_, ?_⟩
  · intro t ht l
    have hGne : G (xx1 y t) ≠ 0 := by
      intro h0; apply ht; simp only [h0, zero_mul]
    rw [← unfolding_matrix_free_coordinate y t l]
    exact hGs _ hGne _ _
  · intro t δ hδ
    set X := xx1 y t with hX
    set Dm := xx1 y (t + δ) - X with hDm
    have hsplit : xx1 y (t + δ) = X + Dm := by rw [hDm]; abel
    have hD : ∀ (s : ℕ) (l : Fin (n + c)), IntAt P (Dm (eN E (n' + c') s) l / (qOf P : E) ^ j) := by
      intro s l
      rw [hDm, hX, unfolding_matrix_sub]
      split_ifs with hs hf
      · simp only [Pi.add_apply, add_sub_cancel_left]; exact hδ _
      · rw [zero_div]; exact ia_zero (P := P)
      · rw [zero_div]; exact ia_zero (P := P)
    have hDint : ∀ (s : ℕ) (l : Fin (n + c)), IntAt P (Dm (eN E (n' + c') s) l) := by
      intro s l
      have e : Dm (eN E (n' + c') s) l
          = (qOf P : E) ^ j * (Dm (eN E (n' + c') s) l / (qOf P : E) ^ j) := by
        field_simp
      rw [e]; exact ia_mul (P := P) (ia_qpow (P := P) j) (hD s l)
    have hGeq : G (X + Dm) = G X := hGp X Dm hD
    simp only
    rw [hsplit, hGeq]
    by_cases hG : G X = 0
    · rw [hG, zero_mul, zero_mul]
    · have hB : IntAt P (chArg (n := n) (c := c) Dm) := by
        have := character_argument_bounded E P n' c' n c 0 Dm (fun s l => by rw [pow_zero, one_mul]; exact hDint s l)
        rwa [pow_zero, one_mul] at this
      have hA : IntAt P ((qOf P : E) ^ j * chArg (n := n) (c := c) X) :=
        character_argument_bounded E P n' c' n c j X (hGs X hG)
      have hA' : IntAt P ((qOf P : E) ^ D * -chArg (n := n) (c := c) X) :=
        ia_up (P := P) hjD (by rw [mul_neg]; exact ia_neg (P := P) hA)
      have hB' : IntAt P ((qOf P : E) ^ D * -chArg (n := n) (c := c) Dm) :=
        ia_mul (P := P) (ia_qpow (P := P) D) (ia_neg (P := P) hB)
      rw [gh_chArg_add, neg_add, hpsi.1 _ _ hA' hB', hpsi.2.1 _ (ia_neg (P := P) hB), mul_one]

end PI.TwistedEisensteinNonvanishing.W
end
end

