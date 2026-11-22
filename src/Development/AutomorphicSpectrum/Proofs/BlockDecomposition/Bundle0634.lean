import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.VerticalStrips.UnramifiedEulerProductIntegral
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.RealDescent.RealLeviDescent.Bundle0002
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CliffordHighestWeightVector
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0595
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0607
import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.ThetaIdempotents.HeckeEta

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NewformTorusVanishing
section
noncomputable section

open Matrix GroundTheory.LocalField GroundTheory.Automorphic
open GroundTheory.Automorphic.GLnLocal (integralGL)
open scoped ValuativeRel

namespace GlobalTheory.CompanionTheory.RankinTorusVanishing

open Ad3 Ad3.R

section Mat

variable {R : Type*} [CommRing R]

theorem diagonal_mul_unipotent (a : Rˣ) (y : R) :
    (dg2 a 1 * uni2 y : GL (Fin 2) R) = uni2 ((a : R) * y) * dg2 a 1 := by
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [dg2, uni2, Matrix.mul_apply, Fin.sum_univ_two]

theorem diagonal_mul_diagonal_alt (a b c d : Rˣ) :
    (dg2 a b * dg2 c d : GL (Fin 2) R) = dg2 (a * c) (b * d) := by
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [dg2, Matrix.mul_apply, Fin.sum_univ_two]

theorem scalar_diagonal_one_one : (dg2 1 1 : GL (Fin 2) R) = 1 := by
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [dg2]

end Mat

section Loc

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]

theorem unipotent_integral_mem_compact {y : F} (hy : y ∈ 𝒪[F]) : uni2 y ∈ integralGL F 2 := by
  rw [GLnLocal.mem_integralGL_iff]
  have hn : -y ∈ 𝒪[F] := neg_mem hy
  constructor <;> intro i j <;> fin_cases i <;> fin_cases j <;>
    simp [uni2, hy, hn, zero_mem, one_mem]

theorem mem_of_ord_nonneg {a : Fˣ} (h : 0 ≤ ord (a : F)) : (a : F) ∈ 𝒪[F] :=
  mem_valBall_zero_iff.1 ((mem_valBall_iff_le_ord a.ne_zero).2 h)

theorem scalar_diagonal_mem_level_zero {u : Fˣ} (hu : ord (u : F) = 0) : dg2 u 1 ∈ integralGL F 2 := by
  rw [GLnLocal.mem_integralGL_iff]
  have h1 : (u : F) ∈ 𝒪[F] := mem_of_ord_nonneg hu.ge
  have h2 : ((u⁻¹ : Fˣ) : F) ∈ 𝒪[F] := mem_of_ord_nonneg (by rw [ord_units_inv, hu]; simp)
  have h2' : (u : F)⁻¹ ∈ 𝒪[F] := by simpa using h2
  constructor <;> intro i j <;> fin_cases i <;> fin_cases j <;>
    simp [dg2, h1, h2', zero_mem, one_mem]

theorem exists_iwasawa2 (g : GL (Fin 2) F) :
    ∃ (x : F) (a d : Fˣ), ∃ k ∈ integralGL F 2, g = uni2 x * dg2 a d * k := by
  obtain ⟨b, hb, k, hk, rfl⟩ := Iwasawa.exists_borel_mul_integralGL F 2 g
  have h10 : b 1 0 = 0 := hb (by simp)
  have h0 : b 0 0 ≠ 0 := Iwasawa.apply_self_ne_zero_of_mem_borel F 2 hb 0
  have h1 : b 1 1 ≠ 0 := Iwasawa.apply_self_ne_zero_of_mem_borel F 2 hb 1
  refine ⟨b 0 1 / b 1 1, Units.mk0 _ h0, Units.mk0 _ h1, k, hk, ?_⟩
  congr 1
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [dg2, uni2, Matrix.mul_apply, Fin.sum_univ_two, h10, h1]

end Loc

section Main

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [MeasurableSpace F] [BorelSpace F]
  {ψ : AddChar F Circle} {ω : Fˣ →* ℂˣ} {lam : ℂ} {W : GL (Fin 2) F → ℂ}

theorem psi_integral (hψ : IsStd ψ) {x : F} (hx : x ∈ 𝒪[F]) : ψ x = 1 := by
  have h := isTrivialOn_addCharConductor hψ.1 hψ.2.1
  rw [hψ.2.2] at h
  exact h x (mem_valBall_zero_iff.2 hx)

theorem torus_mul_unit (hT : TypeT lam W) (a : Fˣ) {u : Fˣ} (hu : ord (u : F) = 0) :
    W (dg2 (a * u) 1) = W (dg2 a 1) := by
  have h : (dg2 (a * u) 1 : GL (Fin 2) F) = dg2 a 1 * dg2 u 1 := by
    rw [diagonal_mul_diagonal_alt, one_mul]
  rw [h, hT.1 _ (scalar_diagonal_mem_level_zero hu)]

theorem torus_eq_zero_of_ord_neg (hψ : IsStd ψ) (hL : Law ψ ω W) (hT : TypeT lam W) {a : Fˣ}
    (ha : ord (a : F) < 0) : W (dg2 a 1) = 0 := by
  have hnt := not_isTrivialOn_addCharConductor_sub_one hψ.1 hψ.2.1
  rw [hψ.2.2] at hnt
  simp only [IsTrivialOn, not_forall] at hnt
  obtain ⟨x, hx, hne⟩ := hnt
  have hx' : x ∈ valBall F (ord (a : F)) := valBall_antitone (by omega) hx
  obtain ⟨y, rfl⟩ := exists_mul_of_mem_valBall a.ne_zero hx'
  have h1 := hT.1 (uni2 (y : F)) (unipotent_integral_mem_compact y.2) (dg2 a 1)
  rw [diagonal_mul_unipotent, hL.1] at h1
  have h2 : ((ψ ((a : F) * y) : ℂ) - 1) * W (dg2 a 1) = 0 := by
    rw [sub_mul, h1]; ring
  rcases mul_eq_zero.1 h2 with h | h
  · exact absurd (Circle.coe_eq_one.1 (sub_eq_zero.1 h)) hne
  · exact h

theorem torus_hecke (hψ : IsStd ψ) (hL : Law ψ ω W) (hT : TypeT lam W) {ϖ : Fˣ} {B : Finset F}
    (hR : Reps ϖ B) {a : Fˣ} (ha : 0 ≤ ord (a : F)) :
    (B.card : ℂ) * W (dg2 (a * ϖ) 1) + ((ω ϖ : ℂˣ) : ℂ) * W (dg2 (a * ϖ⁻¹) 1) =
      lam * W (dg2 a 1) := by
  have h := hT.2 ϖ B hR (dg2 a 1)
  have h1 : ∀ b ∈ B, W (dg2 a 1 * upm ϖ b) = W (dg2 (a * ϖ) 1) := by
    intro b hb
    have hab : (a : F) * b ∈ 𝒪[F] := mul_mem (mem_of_ord_nonneg ha) (hR.2.1 b hb)
    rw [upm, ← mul_assoc, diagonal_mul_unipotent, mul_assoc, diagonal_mul_diagonal_alt, hL.1, psi_integral hψ hab]
    simp
  have h2 : W (dg2 a 1 * dg2 1 ϖ) = ((ω ϖ : ℂˣ) : ℂ) * W (dg2 (a * ϖ⁻¹) 1) := by
    have h3 : (dg2 a 1 * dg2 1 ϖ : GL (Fin 2) F) = dg2 ϖ ϖ * dg2 (a * ϖ⁻¹) 1 := by
      rw [diagonal_mul_diagonal_alt, diagonal_mul_diagonal_alt, mul_one, one_mul, mul_one, mul_left_comm, mul_inv_cancel,
        mul_one]
    rw [h3, hL.2]
  rw [Finset.sum_congr rfl h1, h2] at h
  simpa [Finset.sum_const, nsmul_eq_mul] using h

theorem card_ne_zero {ϖ : Fˣ} {B : Finset F} (hR : Reps ϖ B) : (B.card : ℂ) ≠ 0 := by
  obtain ⟨b, ⟨hb, -⟩, -⟩ := hR.2.2 0 (zero_mem _)
  exact Nat.cast_ne_zero.2 (Finset.card_ne_zero_of_mem hb)

theorem torus_pow_eq_zero (hψ : IsStd ψ) (hL : Law ψ ω W) (hT : TypeT lam W) {ϖ : Fˣ}
    {B : Finset F} (hR : Reps ϖ B) (h1 : W 1 = 0) (n : ℕ) :
    W (dg2 (ϖ ^ (n : ℤ)) 1) = 0 ∧ W (dg2 (ϖ ^ ((n : ℤ) - 1)) 1) = 0 := by
  induction n with
  | zero =>
    refine ⟨by simpa [scalar_diagonal_one_one] using h1, torus_eq_zero_of_ord_neg hψ hL hT ?_⟩
    rw [ord_units_zpow, hR.1]
    simp
  | succ n ih =>
    have hn : 0 ≤ ord ((ϖ ^ (n : ℤ) : Fˣ) : F) := by
      rw [ord_units_zpow, hR.1]
      simp
    have h := torus_hecke hψ hL hT hR hn
    rw [← _root_.zpow_add_one, ← _root_.zpow_sub_one, ih.1, ih.2, mul_zero, mul_zero, add_zero] at h
    push_cast
    refine ⟨(mul_eq_zero.1 h).resolve_left (card_ne_zero hR), ?_⟩
    simpa using ih.1

theorem torus_eq_zero (hψ : IsStd ψ) (hL : Law ψ ω W) (hT : TypeT lam W) {ϖ : Fˣ}
    {B : Finset F} (hR : Reps ϖ B) (h1 : W 1 = 0) (a : Fˣ) : W (dg2 a 1) = 0 := by
  by_cases h : ord (a : F) < 0
  · exact torus_eq_zero_of_ord_neg hψ hL hT h
  obtain ⟨n, hn⟩ := Int.eq_ofNat_of_zero_le (not_lt.1 h)
  have hu : ord ((a * (ϖ ^ (n : ℤ))⁻¹ : Fˣ) : F) = 0 := by
    rw [ord_units_mul, ord_units_inv, ord_units_zpow, hR.1, hn]
    simp
  have ha : a = ϖ ^ (n : ℤ) * (a * (ϖ ^ (n : ℤ))⁻¹) := by
    rw [mul_left_comm, mul_inv_cancel, mul_one]
  rw [ha, torus_mul_unit hT _ hu]
  exact (torus_pow_eq_zero hψ hL hT hR h1 n).1

end Main

theorem spherical_whittaker_eq_zero : Ad3.R.C1 → Ad3.R.U0 := by
  intro hC F _ _ _ _ _ _ ψ hψ ω lam W hL hT h1
  obtain ⟨⟨ϖ, B, hR⟩, -, -⟩ := hC F ψ hψ
  funext g
  obtain ⟨x, a, d, k, hk, rfl⟩ := exists_iwasawa2 g
  have h : (dg2 a d : GL (Fin 2) F) = dg2 d d * dg2 (a * d⁻¹) 1 := by
    rw [diagonal_mul_diagonal_alt, mul_one, mul_left_comm, mul_inv_cancel, mul_one]
  rw [hT.1 k hk, hL.1, h, hL.2, torus_eq_zero hψ hL hT hR h1]
  simp

end GlobalTheory.CompanionTheory.RankinTorusVanishing

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NormSqLeDominantRearrangement
section
noncomputable section

open Matrix Finset
open scoped InnerProductSpace

namespace GlobalTheory.CompanionTheory.DiracKType0

open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD GlobalTheory.CompanionTheory.RealCount GlobalTheory.CompanionTheory.RealCount.InjHw GlobalTheory.CompanionTheory.DiracK

variable {n : ℕ}

theorem norm_sq_le_dominant_rearrangement (a : Fin n → ℝ) (π : Equiv.Perm (Fin n)) :
    Formalism.REAL.nsq (a + rhoV n ∘ π) ≤ nsq (domC a + rhoV n) := by
  set s : Equiv.Perm (Fin n) := Tuple.sort (fun i => -a i) with hs
  have hanti : Antitone (a ∘ s) := by
    intro i j hij
    have := Tuple.monotone_sort (fun i => -a i) hij
    simpa [Function.comp] using this
  have hρ : Antitone (rhoV n) := by
    intro i j hij
    simp only [rhoV]
    have : ((i : ℕ) : ℝ) ≤ (j : ℕ) := by exact_mod_cast hij
    linarith
  have hmv : Monovary (a ∘ s) (rhoV n) := hanti.monovary hρ
  have hr := hmv.sum_mul_comp_perm_le_sum_mul (σ := s.trans π)
  have e1 : ∑ i, a i ^ 2 = ∑ i, (a ∘ s) i ^ 2 := (Equiv.sum_comp s (fun i => a i ^ 2)).symm
  have e2 : ∑ i, rhoV n (π i) ^ 2 = ∑ i, rhoV n i ^ 2 := Equiv.sum_comp π (fun i => rhoV n i ^ 2)
  have e3 : ∑ i, a i * rhoV n (π i) = ∑ i, (a ∘ s) i * rhoV n ((s.trans π) i) :=
    (Equiv.sum_comp s (fun i => a i * rhoV n (π i))).symm
  have l : Formalism.REAL.nsq (a + rhoV n ∘ π) =
      ∑ i, a i ^ 2 + 2 * ∑ i, a i * rhoV n (π i) + ∑ i, rhoV n (π i) ^ 2 := by
    simp only [Formalism.REAL.nsq, Formalism.REAL.dot, Pi.add_apply, Function.comp, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  have r : nsq (domC a + rhoV n) =
      ∑ i, (a ∘ s) i ^ 2 + 2 * ∑ i, (a ∘ s) i * rhoV n i + ∑ i, rhoV n i ^ 2 := by
    simp only [nsq, domC, Pi.add_apply, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by
      simp only [hs, Function.comp]
      ring
  rw [l, r, e1, e2, e3]
  linarith

theorem dirac_ineq0 : ∀ {n : ℕ} (lam : Fin n → ℤ) (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (E1 E2 : Fin n → Fin n → Module.End ℂ V) (σ : Matrix.unitaryGroup (Fin n) ℂ →* (V →ₗ[ℂ] V)),
    IsCoreMod0 (infOf lam) E1 E2 σ → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (c : Fin n → Fin n → Matrix ι ι ℂ),
      IsCliff c → ∀ (τ : Fin n → ℝ) (x : ι → V), x ≠ 0 → Formalism.REAL.KHighest (fun _ => true) (yF (kF E1 E2) c) τ x →
        ∑ a, (m0 lam a) ^ 2 ≤ ∑ a, (τ a + rhoV n a) ^ 2 := by
  intro n lam V _ _ E1 E2 σ h ι _ _ c hc τ x hx hK
  obtain ⟨hc1, hc2⟩ := hc
  have hcl : IsCliff c := ⟨hc1, hc2⟩
  have hp := h.pair

  set L := lft (V := V) ι with hL
  set Rr := rgt (ι := ι) V with hRr
  set p : Fin n → Fin n → Module.End ℂ (ι → V) := fun a b => L (pF E1 E2 a b) with hpdef
  set k : Fin n → Fin n → Module.End ℂ (ι → V) := fun a b => L (kF E1 E2 a b) with hkdef
  set g : Fin n → Fin n → Module.End ℂ (ι → V) := fun a b => Rr (c a b) with hgdef
  set s : Fin n → Fin n → Module.End ℂ (ι → V) := fun a b => Rr (spinM c a b) with hsdef
  set D := dirac (pF E1 E2) c with hD
  have hDe : D = ∑ a, ∑ b, p a b * g b a := rfl
  have hks : ∀ a b c' d, k a b * s c' d = s c' d * k a b := fun a b c' d => lft_mul_rgt _ _
  have hglK : Formalism.REAL.GlRel (kF E1 E2) := glRel_add E1 E2 hp.gl1 hp.gl2 hp.comm
  have hGk : Formalism.REAL.GlRel k := glRel_map L.toRingHom hglK
  have hGs : Formalism.REAL.GlRel s := glRel_map Rr.toRingHom (spinM_glRel c hcl)
  have hYe : yF (kF E1 E2) c = fun a b => k a b + s a b := by
    funext a b
    exact yF_eq _ _ a b
  have hGY : Formalism.REAL.GlRel (yF (kF E1 E2) c) := by
    rw [hYe]
    exact glRel_add k s hGk hGs hks
  have hCY := Formalism.REAL.compactCasimirOnHighestWeight_holds (ι → V) n (fun _ => true) _ τ x hGY hK
  have hCK : Formalism.REAL.CasK (fun _ : Fin n => true) (yF (kF E1 E2) c) = Formalism.REAL.Cas (yF (kF E1 E2) c) := by
    simp [Formalism.REAL.CasK, Formalism.REAL.Cas]
  rw [hCK, rhoC_true] at hCY

  have hg : ∀ a b d e, g a b * g d e + g d e * g a b = if a = e ∧ b = d then (2 : ℂ) • (1 : Module.End ℂ (ι → V)) else 0 := by
    intro a b d e
    have h1 := congrArg Rr (cliff_hg hcl a b d e)
    simp only [map_add, map_mul] at h1
    rw [show g a b * g d e + g d e * g a b = Rr (c a b) * Rr (c d e) + Rr (c d e) * Rr (c a b) from rfl, h1]
    split_ifs
    · rw [map_smul, map_one]
    · exact map_zero Rr
  have hpp : ∀ a b c' d, p a b * p c' d - p c' d * p a b =
      (if b = c' then k a d else 0) - (if d = a then k c' b else 0) := by
    intro a b c' d
    have h1 := congrArg L (bracket_p E1 E2 hp.gl1 hp.gl2 hp.comm a b c' d)
    simp only [map_sub, map_mul] at h1
    have h2 : p a b * p c' d - p c' d * p a b = L (E1 a b - E2 a b) * L (E1 c' d - E2 c' d) -
        L (E1 c' d - E2 c' d) * L (E1 a b - E2 a b) := rfl
    rw [h2]
    simp only [map_sub]
    rw [h1]
    by_cases h5 : b = c' <;> by_cases h6 : d = a <;> simp [h5, h6, hkdef, kF]
  have hsq := dirac_sq_ring p k g hg hpp (fun a b c' d => lft_mul_rgt _ _)
  have hsE : ∀ d a, ((1 / 2 : ℂ) • ∑ e, g d e * g e a - if d = a then ((n : ℂ) / 2) • (1 : Module.End ℂ (ι → V)) else 0) =
      s d a := by
    intro d a
    have : s d a = Rr (spinM c d a) := rfl
    rw [this]
    unfold spinM
    by_cases h1 : d = a <;> simp [h1, map_sub, map_smul, map_sum, map_mul, hgdef]
  simp only [hsE] at hsq
  rw [← hDe] at hsq
  have hCasY := cas_add k s hks
  rw [← hYe] at hCasY
  have hCasP : (∑ a, ∑ b, p a b * p b a) + Formalism.REAL.Cas k =
      L (Formalism.REAL.Cas E1 + Formalism.REAL.Cas E1 + (Formalism.REAL.Cas E2 + Formalism.REAL.Cas E2)) := by
    have h1 := congrArg L (cas_p_add_k E1 E2)
    simp only [two_mul] at h1
    rw [← h1]
    simp [Formalism.REAL.Cas, map_add, map_sum, map_mul, hpdef, hkdef, pF, kF]
  have hCasS : Formalism.REAL.Cas s = (((n : ℂ) ^ 3 - n) / 4) • (1 : Module.End ℂ (ι → V)) := by
    have h1 := congrArg Rr (spinM_cas c hcl)
    simp only [map_smul, map_one] at h1
    rw [← h1]
    simp [Formalism.REAL.Cas, map_sum, map_mul, hsdef]
  have hTot : D * D + Formalism.REAL.Cas (yF (kF E1 E2) c) =
      L (Formalism.REAL.Cas E1 + Formalism.REAL.Cas E1 + (Formalism.REAL.Cas E2 + Formalism.REAL.Cas E2)) +
        (((n : ℂ) ^ 3 - n) / 4) • (1 : Module.End ℂ (ι → V)) := by
    rw [← hCasP, ← hCasS, hsq, hCasY]
    abel

  set R : ℝ := ∑ a, (rhoV n a) ^ 2 with hR
  set S : ℝ := (∑ a, (m0 lam a) ^ 2) / 4 with hS
  have hv : ∀ b : Bool, GlobalTheory.Dec.gelfVal (infOf lam b) 2 = ((S - R : ℝ) : ℂ) := by
    intro b
    rw [gelfVal_two_eq, infOf_sq, Complex.ofReal_sub, hS, hR]
    push_cast
    rfl
  have hC1 : ∀ v : V, Formalism.REAL.Cas E1 v = ((S - R : ℝ) : ℂ) • v := by
    intro v
    rw [← gelA_two, h.ch1 2 v, hv]
  have hC2 : ∀ v : V, Formalism.REAL.Cas E2 v = ((S - R : ℝ) : ℂ) • v := by
    intro v
    rw [← gelA_bar_two, h.ch2 2 v, hv]
  have hn : (((n : ℂ) ^ 3 - n) / 4) = ((3 * R : ℝ) : ℂ) := by
    rw [hR, sum_rhoV_sq]
    push_cast
    ring
  set T : ℝ := Formalism.REAL.nsq (τ + rhoV n) - Formalism.REAL.nsq (rhoV n) with hT
  have hDD : D (D x) = ((4 * (S - R) + 3 * R - T : ℝ) : ℂ) • x := by
    have h1 := congrArg (fun f : Module.End ℂ (ι → V) => f x) hTot
    simp only [LinearMap.add_apply, Module.End.mul_apply, LinearMap.smul_apply, Module.End.one_apply] at h1
    rw [hCY] at h1
    have h2 : L (Formalism.REAL.Cas E1 + Formalism.REAL.Cas E1 + (Formalism.REAL.Cas E2 + Formalism.REAL.Cas E2)) x =
        ((4 * (S - R) : ℝ) : ℂ) • x := by
      funext i
      simp only [hL, lft_apply, LinearMap.add_apply, hC1, hC2, Pi.smul_apply]
      push_cast
      module
    rw [h2, hn] at h1
    rw [eq_sub_of_add_eq h1]
    push_cast
    module

  have hsk := dirac_skew (pF E1 E2) c hp.unitP hc2 x (D x)
  have hN : 0 < ∑ i, ‖x i‖ ^ 2 := by
    obtain ⟨i, hi⟩ := Function.ne_iff.mp hx
    exact Finset.sum_pos' (fun _ _ => by positivity) ⟨i, Finset.mem_univ _, by
      have : x i ≠ 0 := hi
      positivity⟩
  have hM : 0 ≤ ∑ i, ‖D x i‖ ^ 2 := Finset.sum_nonneg fun _ _ => by positivity
  have hEq : ((∑ i, ‖D x i‖ ^ 2 : ℝ) : ℂ) = -(((4 * (S - R) + 3 * R - T) * ∑ i, ‖x i‖ ^ 2 : ℝ) : ℂ) := by
    have e1 : ∑ i, ⟪dirac (pF E1 E2) c x i, D x i⟫_ℂ = ((∑ i, ‖D x i‖ ^ 2 : ℝ) : ℂ) := by
      push_cast
      exact Finset.sum_congr rfl fun i _ => by
        rw [inner_self_eq_norm_sq_to_K]
        rfl
    have e2 : ∑ i, ⟪x i, dirac (pF E1 E2) c (D x) i⟫_ℂ =
        (((4 * (S - R) + 3 * R - T) * ∑ i, ‖x i‖ ^ 2 : ℝ) : ℂ) := by
      have : dirac (pF E1 E2) c (D x) = ((4 * (S - R) + 3 * R - T : ℝ) : ℂ) • x := hDD
      rw [this]
      push_cast
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by
        rw [Pi.smul_apply, inner_smul_right, inner_self_eq_norm_sq_to_K]
        push_cast
        rfl
    rw [← e1, hsk, e2]
  have hEq' : (∑ i, ‖D x i‖ ^ 2) = -((4 * (S - R) + 3 * R - T) * ∑ i, ‖x i‖ ^ 2) := by
    exact_mod_cast hEq
  have hle : 4 * (S - R) + 3 * R - T ≤ 0 := by
    by_contra hcon
    push_neg at hcon
    have := mul_pos hcon hN
    linarith
  have hT' : T = ∑ a, (τ a + rhoV n a) ^ 2 - R := by
    rw [hT, hR]
    simp only [Formalism.REAL.nsq, Formalism.REAL.dot, Pi.add_apply, pow_two]
  rw [hT'] at hle
  have : ∑ a, (m0 lam a) ^ 2 = 4 * S := by
    rw [hS]
    ring
  rw [this]
  linarith

theorem dirac_inequality_k_types : DiracInequalityWithoutSplitComponent := by
  intro n lam _ V _ _ E1 E2 σ hc ν hν
  obtain ⟨x, hxh, hx⟩ := (Submodule.ne_bot_iff _).1 hν
  obtain ⟨S, hfd, hvS, -, hKS, -⟩ := hc.der.2 x
  have hGl : Formalism.REAL.GlRel (kF E1 E2) := GlobalTheory.CompanionTheory.RealMult.DiracProof.kF_gl hc.pair
  have hK : Formalism.REAL.KHighest (fun _ => true) (kF E1 E2) ν x := hxh
  have hint : ∀ a, ∃ m : ℤ, ν a = m := fun a =>
    GlobalTheory.CompanionTheory.RealMult.DiracProof.weight_int hc.der a (ν a) hx (hK.1 a)
  choose m hm using hint
  have hνm : wtR m = ν := by
    funext a
    exact (hm a).symm
  obtain ⟨ι, i1, i2, c, hcl, hconds⟩ := GlobalTheory.T.parthasarathy_rao_varadarajan n
  have hK' : Formalism.REAL.KHighest (fun _ => true) (kF E1 E2) (wtR m) x := by rwa [hνm]
  obtain ⟨w, -, y, hy, hyh⟩ := hconds V (kF E1 E2) S m x hGl hc.pair.unitK hfd hKS hvS hx hK'
  have hn := dirac_ineq0 lam V E1 E2 σ hc ι c hcl _ y hy hyh
  rw [hνm] at hn
  have e1 : LSq lam = ∑ a, (m0 lam a) ^ 2 := by
    simp only [LSq, nsq, m0, rhoV]
    exact Finset.sum_congr rfl fun a _ => by ring
  have e2 : Formalism.REAL.nsq (ν - rhoV n + rhoV n ∘ w.symm) = ∑ a, (ν (w a) - rhoV n (w a) + rhoV n a) ^ 2 := by
    simp only [Formalism.REAL.nsq, Formalism.REAL.dot]
    rw [← Equiv.sum_comp w]
    refine Finset.sum_congr rfl fun a _ => ?_
    simp only [Pi.add_apply, Pi.sub_apply, Function.comp, Equiv.symm_apply_apply]
    ring
  rw [e1]
  have h3 := norm_sq_le_dominant_rearrangement (ν - rhoV n) w.symm
  rw [e2] at h3
  exact hn.trans h3

end GlobalTheory.CompanionTheory.DiracKType0
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PairFiniteDimensional
section
noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec GlobalTheory.CompanionTheory.CTFin PositivityTheory.Rg.Rs
open PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation

namespace GlobalTheory.CompanionTheory.EGlue

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {a b : ℕ}

theorem exists_fd_slices (U₁ : Submodule ℂ (Sm E a)) (U₂ : Submodule ℂ (Sm E b)) (F : H E a b → ℂ)
    (hF : F ∈ pairSpace U₁ U₂) :
    ∃ (A : Submodule ℂ (Sm E a)) (B : Submodule ℂ (Sm E b)), FiniteDimensional ℂ A ∧ FiniteDimensional ℂ B ∧
      (∀ m₂ : GA E b, ∃ φ ∈ A, φ.1 = fun x => F (x, m₂)) ∧ (∀ m₁ : GA E a, ∃ φ ∈ B, φ.1 = fun x => F (m₁, x)) := by
  induction hF using Submodule.span_induction with
  | mem F h =>
    obtain ⟨φ₁, -, φ₂, -, rfl⟩ := h
    refine ⟨Submodule.span ℂ {φ₁}, Submodule.span ℂ {φ₂}, inferInstance, inferInstance, fun m₂ => ?_, fun m₁ => ?_⟩
    · refine ⟨φ₂.1 m₂ • φ₁, Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _), ?_⟩
      funext x
      simp [mul_comm]
    · refine ⟨φ₁.1 m₁ • φ₂, Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _), ?_⟩
      funext x
      simp
  | zero =>
    refine ⟨⊥, ⊥, inferInstance, inferInstance, fun m₂ => ⟨0, Submodule.zero_mem _, ?_⟩,
      fun m₁ => ⟨0, Submodule.zero_mem _, ?_⟩⟩
    · funext x
      simp
    · funext x
      simp
  | add F G _ _ hF hG =>
    obtain ⟨A, B, hA, hB, h₁, h₂⟩ := hF
    obtain ⟨A', B', hA', hB', h₁', h₂'⟩ := hG
    refine ⟨A ⊔ A', B ⊔ B', inferInstance, inferInstance, fun m₂ => ?_, fun m₁ => ?_⟩
    · obtain ⟨φ, hφ, e⟩ := h₁ m₂
      obtain ⟨φ', hφ', e'⟩ := h₁' m₂
      refine ⟨φ + φ', Submodule.add_mem_sup hφ hφ', ?_⟩
      funext x
      simp [e, e']
    · obtain ⟨φ, hφ, e⟩ := h₂ m₁
      obtain ⟨φ', hφ', e'⟩ := h₂' m₁
      refine ⟨φ + φ', Submodule.add_mem_sup hφ hφ', ?_⟩
      funext x
      simp [e, e']
  | smul c F _ hF =>
    obtain ⟨A, B, hA, hB, h₁, h₂⟩ := hF
    refine ⟨A, B, hA, hB, fun m₂ => ?_, fun m₁ => ?_⟩
    · obtain ⟨φ, hφ, e⟩ := h₁ m₂
      refine ⟨c • φ, A.smul_mem c hφ, ?_⟩
      funext x
      simp [e]
    · obtain ⟨φ, hφ, e⟩ := h₂ m₁
      refine ⟨c • φ, B.smul_mem c hφ, ?_⟩
      funext x
      simp [e]

theorem pairFD_holds : PairFD := by
  intro E _ _ _ a b ι _ U₁ U₂ f hf
  choose A B hA hB h₁ h₂ using fun i => exists_fd_slices U₁ U₂ (f i) (hf i)
  have hA' : FiniteDimensional ℂ (⨆ i, A i : Submodule ℂ (Sm E a)) := Submodule.finiteDimensional_iSup A
  have hB' : FiniteDimensional ℂ (⨆ i, B i : Submodule ℂ (Sm E b)) := Submodule.finiteDimensional_iSup B
  constructor
  · refine Submodule.finiteDimensional_of_le (S₂ := ⨆ i, A i) (Submodule.span_le.2 ?_)
    rintro φ ⟨i, m₂, e⟩
    obtain ⟨ψ, hψ, e'⟩ := h₁ i m₂
    have : φ = ψ := Subtype.ext (e.trans e'.symm)
    rw [this]
    exact Submodule.mem_iSup_of_mem i hψ
  · refine Submodule.finiteDimensional_of_le (S₂ := ⨆ i, B i) (Submodule.span_le.2 ?_)
    rintro φ ⟨i, m₁, e⟩
    obtain ⟨ψ, hψ, e'⟩ := h₂ i m₁
    have : φ = ψ := Subtype.ext (e.trans e'.symm)
    rw [this]
    exact Submodule.mem_iSup_of_mem i hψ

end GlobalTheory.CompanionTheory.EGlue

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RightIdentityStatementStatement
section
open PositivityTheory.Rg.Rsw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.right_identity_statement : RightId := by
  first | exact @GlobalTheory.CompanionTheory.Dblock.rightId | exact GlobalTheory.CompanionTheory.Dblock.rightId | (intros; apply GlobalTheory.CompanionTheory.Dblock.rightId <;> assumption)
end

