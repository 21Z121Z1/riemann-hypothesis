import Formalism.LocalToGlobal.Columns.Bundle0058
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.KerHypAll
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.ThDistC

-- bundled from Formalism.LocalToGlobal.Columns.ExistsNeZeroOfFirstUnfoldingNeZero
section
open NumberField IsDedekindDomain Module

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV

section TwE1J

variable {E K : Type} [Field E] [NumberField E] [StarRing E] [Field K] {P : HeightOneSpectrum (𝓞 E)}

theorem isUnit_reduction_mul_iff₂ {u y : E} (hu0 : u ≠ 0) (hu : IntAt P u) (hu' : IntAt P u⁻¹) :
    IsUnit (redP P (y * u)) ↔ IsUnit (redP P y) := by
  have hru : IsUnit (redP P u) := by
    have h1 : redP P u * redP P u⁻¹ = 1 := by rw [← reduction_mul hu hu', mul_inv_cancel₀ hu0, redP_one]
    exact isUnit_iff_exists_inv.2 ⟨_, h1⟩
  by_cases hy : IntAt P y
  · rw [reduction_mul hy hu, IsUnit.mul_iff]
    exact ⟨fun h => h.1, fun h => ⟨h, hru⟩⟩
  · have hyu : ¬ IntAt P (y * u) := fun h => hy (by
      have e : y = (y * u) * u⁻¹ := by field_simp
      rw [e]; exact h.mul hu')
    rw [reduction_eq_zero_of_not_integral P hy, reduction_eq_zero_of_not_integral P hyu]

theorem valuationAt_mul_unit (q : ℕ) {a u : E} (hu0 : u ≠ 0) (hu : IntAt P u) (hu' : IntAt P u⁻¹) : LocE.vP P q (a * u) = LocE.vP P q a := by
  unfold LocE.vP
  congr 1
  funext z
  have e : a * u / (q : E) ^ z = a / (q : E) ^ z * u := by ring
  rw [e, isUnit_reduction_mul_iff₂ hu0 hu hu']

theorem twLocChar_mul_unit (q : ℕ) (cq : K) (χ : (𝓞 E ⧸ P.asIdeal)ˣ →* Kˣ) {a u : E} (hu0 : u ≠ 0) (hu : IntAt P u) (hu' : IntAt P u⁻¹)
    (ha : LocE.locChar (P := P) q cq χ a ≠ 0) : LocE.locChar (P := P) q cq χ (a * u) ≠ 0 := by
  unfold LocE.locChar at ha ⊢
  rw [valuationAt_mul_unit q hu0 hu hu']
  have h1 := left_ne_zero_of_mul ha
  have h2 := right_ne_zero_of_mul ha
  refine mul_ne_zero h1 ?_
  have hU : IsUnit (redP P (a / (q : E) ^ LocE.vP P q a)) := by
    by_contra hn
    unfold LocE.unitV at h2
    rw [dif_neg hn] at h2
    exact h2 rfl
  have hU' : IsUnit (redP P (a * u / (q : E) ^ LocE.vP P q a)) := by
    have e : a * u / (q : E) ^ LocE.vP P q a = a / (q : E) ^ LocE.vP P q a * u := by ring
    rw [e, isUnit_reduction_mul_iff₂ hu0 hu hu']
    exact hU
  unfold LocE.unitV
  rw [dif_pos hU']
  exact Units.ne_zero _

theorem firstUnfolding_const_mul {n' c' n c : ℕ} (psi : E → K) (vals : Finset E) (wt C : K) (Φ : Loc.SF E K (n' + c') (n + c))
    (xj : (Fin n' → E) →ₗ[E] (Fin n → E)) :
    Loc.E1 (n' := n') (c' := c') (n := n) (c := c) psi vals wt (fun x => C * Φ x) xj = C * Loc.E1 psi vals wt Φ xj := by
  unfold Loc.E1
  simp only [Finset.mul_sum]
  exact Finset.sum_congr rfl fun t _ => by ring

theorem exists_ne_zero_of_firstUnfolding_ne_zero {n' c' n c : ℕ} (psi : E → K) (vals : Finset E) (wt : K) (Φ : Loc.SF E K (n' + c') (n + c))
    (xj : (Fin n' → E) →ₗ[E] (Fin n → E)) (h : Loc.E1 (n' := n') (c' := c') (n := n) (c := c) psi vals wt Φ xj ≠ 0) : ∃ x, Φ x ≠ 0 := by
  by_contra hn
  push Not at hn
  apply h
  unfold Loc.E1
  simp [hn]

end TwE1J

section TwE1JMain

variable {X : Fields} {Pr : Primes X} {R : Ranks} {Ch : Chars X Pr R.m}
  {sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)} {S : Set ℕ}
  {mu : Tup X.F X.E X.K S} {cst : LocCst X (rowSG Pr sel mu)}

theorem twPhiAt_Q (sharp : Bool) (i : ℕ) {P : HeightOneSpectrum (𝓞 X.E)} (hP : P ∉ Pr.vGs) :
    PhiAt (Pr := Pr) (R := R) Ch mu sharp i P = LocE.PhiQ (qOf P) (resChar (mu : Chr X.F X.E X.K) P) R.k R.r (cOf R i) (R.N i)
      (cOf R (i + 1)) (R.N (i + 1)) := by
  unfold PhiAt
  rw [if_neg hP]

def twOmS (c : LocCst X (rowSG Pr sel mu)) (i : ℕ) (P : rowSG Pr sel mu) (hal : AutY X R i) (g : AutY X R (i + 1)) : X.K :=
  muAt Ch sel mu c i P (LinearEquiv.det hal : X.Eˣ) * (muAt Ch sel mu c i P (LinearEquiv.det g : X.Eˣ))⁻¹ *
    c.sq P ^ (-(LocE.vP P.1 (qOf P.1) (LinearEquiv.det hal : X.Eˣ)) * ((R.N (i + 1) + cOf R (i + 1) : ℕ) : ℤ)) *
    c.sq P ^ (LocE.vP P.1 (qOf P.1) (LinearEquiv.det g : X.Eˣ) * ((R.N i + cOf R i : ℕ) : ℤ))

theorem twOmPhi_eq (c : LocCst X (rowSG Pr sel mu)) (i : ℕ) (P : rowSG Pr sel mu) (hal : AutY X R i) (g : AutY X R (i + 1))
    (x : HomE X.E (R.N i + cOf R i) (R.N (i + 1) + cOf R (i + 1))) :
    omPhi Ch sel mu c i P hal g x = twOmS (Ch := Ch) c i P hal g * PhiAt Ch mu c.sharp i P.1 (g.symm.toLinearMap ∘ₗ x ∘ₗ hal.toLinearMap) :=
  rfl

theorem firstUnfoldingNe_mul_parahoric {i : ℕ} (hi : i + 2 ≤ R.m) {P : rowSG Pr sel mu} (hP : P.1 ∉ Pr.vGs) (hd : TwDegOne X P.1) (hsq : cst.sq P ≠ 0)
    {hal : AutY X R i} {h κ : AutY X R (i + 1)} (hκ : κ ∈ Jat (Pr := Pr) cst.sharp (i + 1) P.1)
    (H : FiniteSumNonzeroLargeDepth Ch sel mu cst i P hal h) : FiniteSumNonzeroLargeDepth Ch sel mu cst i P hal (h * κ) := by
  have hJ : κ ∈ LocE.JQ P.1 (qOf P.1) (R.k + (i + 1)) (R.N (i + 1)) (cOf R (i + 1)) := by
    rw [← twJat_Q cst.sharp (i + 1) hP]; exact hκ
  have hr := R.two_le_m

  have hlaw : ∀ g : AutY X R (i + 1), g ∈ LocE.JQ P.1 (qOf P.1) (R.k + (i + 1)) (R.N (i + 1)) (cOf R (i + 1)) →
      ∀ y, PhiAt Ch mu cst.sharp i P.1 (g.toLinearMap ∘ₗ y) =
        ((LocE.unitV (resChar (mu : Chr X.F X.E X.K) P.1) ((LinearEquiv.det g : X.Eˣ) : X.E) *
          LocE.lamQB (resChar (mu : Chr X.F X.E X.K) P.1) (R.k + (i + 1)) (R.N (i + 1)) g.toLinearMap) *
        (LocE.unitV (resChar (mu : Chr X.F X.E X.K) P.1) ((LinearEquiv.det (1 : AutY X R i) : X.Eˣ) : X.E) *
          LocE.lamQB (resChar (mu : Chr X.F X.E X.K) P.1) (R.k + i) (R.N i) (1 : AutY X R i).toLinearMap)) *
        PhiAt Ch mu cst.sharp i P.1 y := by
    intro g hg y
    rw [twPhiAt_Q cst.sharp i hP]
    have e1 : g.toLinearMap ∘ₗ y = g.toLinearMap ∘ₗ y ∘ₗ (1 : AutY X R i).toLinearMap := LinearMap.ext fun _ => rfl
    rw [e1]
    refine Formalism.L2.Ker.phiQ_law_lam (ciQ_mem P.1) hd.2 _ R.k R.r (cOf R i) (R.N i) (cOf R (i + 1)) (R.N (i + 1)) (R.k + i) (R.k + (i + 1))
      (by omega) (by omega) ?_ ?_ ?_ ?_ (Subgroup.one_mem _) hg y
    · unfold Ranks.N; have := Nat.le_mul_of_pos_right i (show 0 < R.t + 1 by omega); omega
    · unfold Ranks.N; have := Nat.le_mul_of_pos_right (i + 1) (show 0 < R.t + 1 by omega); omega
    · unfold cOf Ranks.r; omega
    · unfold cOf Ranks.r; omega
  obtain ⟨A₀, B₀, hH⟩ := H
  refine ⟨A₀, B₀, fun A' B' hA hB hz => ?_⟩
  have hne := hH A' B' hA hB
  obtain ⟨xj, hxj⟩ := Function.ne_iff.1 hne
  set c' : LocCst X (rowSG Pr sel mu) := { cst with A := A', B := B' } with hc'

  set Ψ : Loc.SF X.E X.K (R.N i + cOf R i) (R.N (i + 1) + cOf R (i + 1)) :=
    fun x => PhiAt Ch mu cst.sharp i P.1 (h.symm.toLinearMap ∘ₗ x ∘ₗ hal.toLinearMap) with hΨ
  have hOm0 : omPhi Ch sel mu c' i P hal h = fun x => twOmS (Ch := Ch) c' i P hal h * Ψ x := funext fun x => twOmPhi_eq c' i P hal h x
  set F : X.K := (LocE.unitV (resChar (mu : Chr X.F X.E X.K) P.1) ((LinearEquiv.det κ⁻¹ : X.Eˣ) : X.E) *
          LocE.lamQB (resChar (mu : Chr X.F X.E X.K) P.1) (R.k + (i + 1)) (R.N (i + 1)) κ⁻¹.toLinearMap) *
        (LocE.unitV (resChar (mu : Chr X.F X.E X.K) P.1) ((LinearEquiv.det (1 : AutY X R i) : X.Eˣ) : X.E) *
          LocE.lamQB (resChar (mu : Chr X.F X.E X.K) P.1) (R.k + i) (R.N i) (1 : AutY X R i).toLinearMap) with hFdef
  have hOm1 : omPhi Ch sel mu c' i P hal (h * κ) = fun x => (twOmS (Ch := Ch) c' i P hal (h * κ) * F) * Ψ x := by
    funext x
    rw [twOmPhi_eq c' i P hal (h * κ) x, mul_assoc]
    congr 1
    have e2 : (h * κ).symm.toLinearMap ∘ₗ x ∘ₗ hal.toLinearMap = κ⁻¹.toLinearMap ∘ₗ (h.symm.toLinearMap ∘ₗ x ∘ₗ hal.toLinearMap) :=
      LinearMap.ext fun _ => rfl
    rw [e2]
    exact hlaw κ⁻¹ (inv_mem hJ) _
  have hE0 : E1at Ch sel mu c' i P hal h xj = twOmS (Ch := Ch) c' i P hal h * Loc.E1 (c'.psi P) (LocE.valsQ X.E (qOf P.1) c'.A c'.B)
      (((qOf P.1 : X.K) ^ c'.B)⁻¹) Ψ xj := by
    unfold E1at
    rw [hOm0, firstUnfolding_const_mul]
  have hE1 : E1at Ch sel mu c' i P hal (h * κ) xj = (twOmS (Ch := Ch) c' i P hal (h * κ) * F) * Loc.E1 (c'.psi P) (LocE.valsQ X.E (qOf P.1) c'.A c'.B)
      (((qOf P.1 : X.K) ^ c'.B)⁻¹) Ψ xj := by
    unfold E1at
    rw [hOm1, firstUnfolding_const_mul]
  have h0 := hE0 ▸ hxj
  have hS := right_ne_zero_of_mul h0
  have hM := left_ne_zero_of_mul h0

  obtain ⟨x0, hx0⟩ := exists_ne_zero_of_firstUnfolding_ne_zero _ _ _ Ψ xj hS
  have hF : F ≠ 0 := by
    intro hF0
    apply hx0
    have e3 : h.symm.toLinearMap ∘ₗ x0 ∘ₗ hal.toLinearMap = κ.toLinearMap ∘ₗ (κ⁻¹.toLinearMap ∘ₗ (h.symm.toLinearMap ∘ₗ x0 ∘ₗ hal.toLinearMap)) :=
      LinearMap.ext fun v => by simp
    show PhiAt Ch mu cst.sharp i P.1 (h.symm.toLinearMap ∘ₗ x0 ∘ₗ hal.toLinearMap) = 0
    rw [e3, hlaw κ hJ, hlaw κ⁻¹ (inv_mem hJ), ← hFdef, hF0, zero_mul, mul_zero]

  have hMk : twOmS (Ch := Ch) c' i P hal (h * κ) ≠ 0 := by
    unfold twOmS at hM ⊢
    have hA1 := left_ne_zero_of_mul (left_ne_zero_of_mul (left_ne_zero_of_mul hM))
    have hA2 := right_ne_zero_of_mul (left_ne_zero_of_mul (left_ne_zero_of_mul hM))
    have hA3 := right_ne_zero_of_mul (left_ne_zero_of_mul hM)
    have hκG : κ ∈ GLint X.E (R.N (i + 1) + cOf R (i + 1)) P.1 := hJ.1
    have hmu : muAt Ch sel mu c' i P (LinearEquiv.det (h * κ) : X.Eˣ) ≠ 0 := by
      have e4 : ((LinearEquiv.det (h * κ) : X.Eˣ) : X.E) = ((LinearEquiv.det h : X.Eˣ) : X.E) * ((LinearEquiv.det κ : X.Eˣ) : X.E) := by
        rw [map_mul, Units.val_mul]
      rw [e4]
      exact twLocChar_mul_unit _ _ _ (Units.ne_zero _) (Formalism.L2.Ker.intAt_det κ hκG) (Formalism.L2.Ker.intAt_det_inv κ hκG) (fun h0 => hA2 (by unfold muAt; rw [h0, inv_zero]))
    refine mul_ne_zero (mul_ne_zero (mul_ne_zero hA1 (inv_ne_zero hmu)) hA3) (zpow_ne_zero _ hsq)
  have hz' := congrFun hz xj
  rw [hE1] at hz'
  exact mul_ne_zero (mul_ne_zero hMk hF) hS hz'

variable (Ch sel mu cst) in

def UnfoldingNonvanishingLeftCoset (m2 : ℕ) : Prop :=
  ∀ i, i < m2 → ∀ P : rowSG Pr sel mu, P.1 ∉ Pr.vGs → TwDegOne X P.1 → ∀ (hal : AutY X R i) (h r : AutY X R (i + 1)),
    r ∈ Loc.R1 X.E (R.N (i + 1)) (cOf R (i + 1)) → TwBdd (Pr := Pr) i P.1 hal → TwBdd (Pr := Pr) (i + 1) P.1 h →
      TwBdd (Pr := Pr) (i + 1) P.1 (r * h) → FiniteSumNonzeroLargeDepth Ch sel mu cst i P hal h → FiniteSumNonzeroLargeDepth Ch sel mu cst i P hal (r * h)

theorem doubleCoset_of_leftR1 {m2 : ℕ} (hm : R.m = m2 + 2) (hsq : ∀ P : rowSG Pr sel mu, P.1 ∉ Pr.vGs → cst.sq P ≠ 0)
    (HL : UnfoldingNonvanishingLeftCoset Ch sel mu cst m2) : UnfoldingNonvanishingDoubleCoset Ch sel mu cst m2 := by
  intro i hi P hP hd hal h h' hbal hb hb' hs hne
  obtain ⟨r, hr, κ, hκ, rfl⟩ := hs
  have hJ : κ ∈ LocE.JQ P.1 (qOf P.1) (R.k + (i + 1)) (R.N (i + 1)) (cOf R (i + 1)) := by
    rw [← twJat_Q cst.sharp (i + 1) hP]; exact hκ

  have hstd : ∀ (g : AutY X R (i + 1)), g ∈ stabL X.E _ (stdAt X.E (R.N (i + 1) + cOf R (i + 1)) P.1) →
      ∀ x, x ∈ lamYat (Pr := Pr) (R := R) (i + 1) P.1 → g x ∈ lamYat (Pr := Pr) (R := R) (i + 1) P.1 := fun g hg x hx => by
    rw [twLamQ_mem hP] at hx ⊢
    exact (twStd_mem _).1 ((hg x).2 ((twStd_mem _).2 hx))
  have hbrh : TwBdd (Pr := Pr) (i + 1) P.1 (r * h) := by
    intro x hx
    have e : r * h = (r * h * κ) * κ⁻¹ := by rw [mul_assoc, mul_inv_cancel, mul_one]
    rw [e]
    refine ⟨?_, ?_⟩
    · show κ ((r * h * κ)⁻¹ x) ∈ _
      exact hstd κ hJ.1 _ (hb' x hx).1
    · show ((qOf P.1 : X.E) ^ (i + 1)) • (r * h * κ) (κ⁻¹ x) ∈ _
      exact (hb' _ (hstd κ⁻¹ (inv_mem hJ.1) x hx)).2
  have h1 := HL i hi P hP hd hal h r hr hbal hb hbrh hne
  exact firstUnfoldingNe_mul_parahoric (by omega) hP hd (hsq P hP) hκ h1

end TwE1JMain

end Formalism.L2.Col
end
end

-- bundled from Formalism.LocalToGlobal.Columns.QthPrincInv
section
open NumberField IsDedekindDomain

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV

section Ext

variable {E : Type} [Field E] [NumberField E] [StarRing E] (P : HeightOneSpectrum (𝓞 E)) {n c : ℕ}

theorem qth_ext_close (g : Sp E n ≃ₗ[E] Sp E n) (N : ℕ) (hg : lqPrinc P N g) (i l : Fin (n + c)) :
    P.valuation E ((((toGLm E (n + c) (twZrExt (c := c) g) : GL (Fin (n + c)) E) : Matrix (Fin (n + c)) (Fin (n + c)) E) - 1) i l) ≤
      WithZero.exp (-(N : ℤ)) := by
  have hcoe : ∀ W : Sp E (n + c) ≃ₗ[E] Sp E (n + c),
      ((toGLm E (n + c) W : GL (Fin (n + c)) E) : Matrix (Fin (n + c)) (Fin (n + c)) E) =
        LinearMap.toMatrix' (W : Sp E (n + c) →ₗ[E] Sp E (n + c)) := by
    intro W
    simp only [toGLm, Matrix.GeneralLinearGroup.toLin, LinearMap.GeneralLinearGroup.generalLinearEquiv,
      MulEquiv.trans_apply, MulEquiv.symm_symm, MulEquiv.symm_mk, MulEquiv.coe_mk, Equiv.coe_fn_symm_mk,
      Units.coe_map, MonoidHom.coe_coe]
    rfl
  set u : Fin (n + c) → E := Pi.single l 1 with hu0
  have hpi : ∀ y : Fin n → E, (Loc.inX E n c y) i = if h : (i : ℕ) < n then y ⟨i, h⟩ else 0 := by
    intro y
    simp only [Loc.inX, LinearMap.pi_apply]
    split_ifs <;> rfl
  have hval : ((twZrExt (c := c) g) u) i =
      Loc.inX E n c (g (LinearMap.funLeft E E (Fin.castAdd c) u)) i +
        (u i - Loc.inX E n c (LinearMap.funLeft E E (Fin.castAdd c) u) i) := by
    rw [twZrExt_apply]
    rfl
  rw [hcoe, Matrix.sub_apply, LinearMap.toMatrix'_apply, LinearEquiv.coe_coe, ← hu0, hval, hpi, hpi]
  by_cases hi : (i : ℕ) < n
  · rw [dif_pos hi, dif_pos hi]
    have hu : (LinearMap.funLeft E E (Fin.castAdd c)) u ⟨i, hi⟩ = u i := rfl
    rw [hu, sub_self, add_zero]
    by_cases hl : (l : ℕ) < n
    · have hu' : LinearMap.funLeft E E (Fin.castAdd c) u = Pi.single (⟨l, hl⟩ : Fin n) 1 := by
        ext j
        simp [hu0, LinearMap.funLeft_apply, Pi.single_apply, Fin.ext_iff]
      rw [hu']
      have h1 : (1 : Matrix (Fin (n + c)) (Fin (n + c)) E) i l =
          (1 : Matrix (Fin n) (Fin n) E) ⟨i, hi⟩ ⟨l, hl⟩ := by
        simp [Matrix.one_apply, Fin.ext_iff]
      rw [h1]
      have h2 := hg ⟨i, hi⟩ ⟨l, hl⟩
      rw [Matrix.sub_apply, LinearMap.toMatrix'_apply, LinearEquiv.coe_coe] at h2
      exact h2
    · have hu' : LinearMap.funLeft E E (Fin.castAdd c) u = 0 := by
        ext j
        simp only [hu0, LinearMap.funLeft_apply, Pi.single_apply, Pi.zero_apply, Function.comp_apply]
        rw [if_neg]
        intro h
        apply hl
        rw [← h]
        exact j.isLt
      have h1 : (1 : Matrix (Fin (n + c)) (Fin (n + c)) E) i l = 0 := by
        rw [Matrix.one_apply_ne]
        intro h
        apply hl
        rw [← h]
        exact hi
      rw [hu', map_zero, Pi.zero_apply, h1, sub_zero, map_zero]
      exact zero_le'
  · rw [dif_neg hi, dif_neg hi, zero_add, sub_zero]
    have h3 : u i - (1 : Matrix (Fin (n + c)) (Fin (n + c)) E) i l = 0 := by
      simp [hu0, Pi.single_apply, Matrix.one_apply]
    rw [h3, map_zero]
    exact zero_le'

theorem qth_princ_inv {N : ℕ} (g : ↥(GLint E n P)) (hg : lqPrinc P N (g : Sp E n ≃ₗ[E] Sp E n)) :
    lqPrinc P N ((g⁻¹ : ↥(GLint E n P)) : Sp E n ≃ₗ[E] Sp E n) := by
  unfold lqPrinc at hg ⊢
  intro i j
  set A := LinearMap.toMatrix' ((g : Sp E n ≃ₗ[E] Sp E n) : Sp E n →ₗ[E] Sp E n) with hA
  set B := LinearMap.toMatrix'
    ((((g⁻¹ : GLint E n P)) : Sp E n ≃ₗ[E] Sp E n) : Sp E n →ₗ[E] Sp E n) with hB
  have hBA : B * A = 1 := by
    rw [hA, hB, ← LinearMap.toMatrix'_comp]
    have hc : ((((g⁻¹ : GLint E n P)) : Sp E n ≃ₗ[E] Sp E n) : Sp E n →ₗ[E] Sp E n).comp
        ((g : Sp E n ≃ₗ[E] Sp E n) : Sp E n →ₗ[E] Sp E n) = LinearMap.id := by
      refine LinearMap.ext fun x => ?_
      have hx : ((((g⁻¹ * g : GLint E n P)) : Sp E n ≃ₗ[E] Sp E n)) x = x := by
        rw [inv_mul_cancel]
        rfl
      exact hx
    rw [hc, LinearMap.toMatrix'_id]
  have hBle : ∀ a k, P.valuation E (B a k) ≤ 1 := by
    intro a k
    rw [hB, LinearMap.toMatrix'_apply, LinearEquiv.coe_coe]
    have hs : (Pi.single k (1 : E) : Sp E n) ∈ stdAt E n P := by
      show _ ∈ localization₂ P.asIdeal (stdLat E n)
      rw [mem_localization_standardLattice]
      intro t
      rw [qth_intAt_iff]
      by_cases h : t = k
      · subst h
        simp
      · simp [Pi.single_apply, h]
    have hmem : ((g⁻¹ : GLint E n P) : Sp E n ≃ₗ[E] Sp E n) ∈ stabL E n (stdAt E n P) :=
      (g⁻¹ : GLint E n P).2
    have h2 := ((ChainCounts.mem_stabL_iff.1 hmem) _).2 hs
    have h3 := (mem_localization_standardLattice P _).1 h2 a
    rw [qth_intAt_iff] at h3
    exact h3
  have hBm : B - 1 = -(B * (A - 1)) := by
    rw [Matrix.mul_sub, hBA, Matrix.mul_one, neg_sub]
  rw [hBm, Matrix.neg_apply, Valuation.map_neg, Matrix.mul_apply]
  refine Valuation.map_sum_le _ (fun k _ => ?_)
  rw [map_mul]
  calc _ ≤ 1 * P.valuation E ((A - 1) k j) := mul_le_mul' (hBle i k) le_rfl
    _ ≤ _ := by rw [one_mul]; exact hg k j

end Ext

end Formalism.L2.Col
end
end

