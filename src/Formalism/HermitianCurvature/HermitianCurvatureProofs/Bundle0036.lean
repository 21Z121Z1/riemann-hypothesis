import Formalism.HermitianCurvature.BigCellVanishingOfCommute
import Formalism.HermitianCurvature.CompositeFormulaLevelZero
import Formalism.HermitianCurvature.StatementJF
import Formalism.HermitianCurvature.HermitianCurvatureProofs.DilationUnipotentWeylMeasure
import Formalism.HermitianCurvature.HermitianCurvatureProofs.RegularisedPairingViaPhase
import Formalism.HermitianCurvature.HermitianCurvatureProofs.NormDiagonalEntryDilationGeneratorLeOne
import Formalism.HermitianCurvature.HermitianCurvatureProofs.OrbitalIntegralAeConvergenceContinuity

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.FibreExpansionZeroFails
section
open Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P

theorem fibre_chain_expansion : C6.FibChainExp := by
  intro r i a _ hai; nlinarith

theorem fibre_expansion_identity : C6.FibExpText := by
  intro r i hi; nlinarith

theorem fibre_expansion_zero_fails : C6.FibExpZeroFails := by
  intro h; have := h 0 0; norm_num at this

theorem c6_budgetArith_proof : C6.BudgetArith := by
  intro Cb CV hCb
  refine ⟨Cb ^ 2 + 3 * Cb + 6 * CV + 1, ?_⟩
  intro r n N o κ As A₀ hr hn h1 h2 ho hκ hA
  unfold C6.AV C6.mmV
  push_cast
  have hx : (1:ℝ) ≤ r := by exact_mod_cast hr
  have hxy : 2 * (r:ℝ) + 2 ≤ n := by exact_mod_cast hn
  have h1' : (N:ℝ) * (n:ℝ) ^ 2 ≤ As := by exact_mod_cast h1
  have h2' : (n:ℝ) ^ 3 ≤ As := by exact_mod_cast h2
  have hV : (0:ℝ) ≤ CV := by positivity
  have hN : (0:ℝ) ≤ N := by positivity
  have hy : (1:ℝ) ≤ n := by linarith
  have hn2 : (n:ℝ) ^ 2 ≤ As := le_trans (by nlinarith) h2'
  have hn1 : (n:ℝ) ≤ As := le_trans (by nlinarith) hn2
  have hR3 : ((r:ℝ) + 1) ^ 3 ≤ As := le_trans (pow_le_pow_left₀ (by positivity) (by linarith) 3) h2'
  have hr3 : (r:ℝ) ^ 3 ≤ As := le_trans (pow_le_pow_left₀ (by positivity) (by linarith) 3) hR3
  have hNn : (N:ℝ) * n ≤ As := le_trans (mul_le_mul_of_nonneg_left (by nlinarith) hN) h1'
  have ho' : (o:ℝ) ≤ Cb * As := by
    calc (o:ℝ) ≤ Cb * N * n := ho
      _ = Cb * (N * n) := by ring
      _ ≤ Cb * As := mul_le_mul_of_nonneg_left hNn hCb
  have hAs0 : (0:ℝ) ≤ As := le_trans (by positivity) hn1
  set P : ℝ := ((r:ℝ) + 1) ^ 4 * As with hP
  have hR4 : (1:ℝ) ≤ ((r:ℝ) + 1) ^ 4 := one_le_pow₀ (by linarith)
  have hP1 : (As:ℝ) ≤ P := by nlinarith
  have hRR : (r:ℝ) + 1 ≤ ((r:ℝ) + 1) ^ 4 := by
    calc (r:ℝ) + 1 = ((r:ℝ) + 1) ^ 1 := (pow_one _).symm
      _ ≤ _ := pow_le_pow_right₀ (by linarith) (by norm_num)
  have hP2 : ((r:ℝ) + 1) * As ≤ P := mul_le_mul_of_nonneg_right hRR hAs0
  have hx4 : (r:ℝ) ^ 4 ≤ ((r:ℝ) + 1) ^ 4 := pow_le_pow_left₀ (by positivity) (by linarith) 4
  have hP3 : (r:ℝ) ^ 4 * n ≤ P := mul_le_mul hx4 hn1 (by positivity) (by positivity)
  have hP4 : (r:ℝ) * n ^ 2 ≤ P := mul_le_mul (by linarith) hn2 (by positivity) (by positivity)
  have hx2 : (r:ℝ) ^ 2 ≤ ((r:ℝ) + 1) ^ 4 := by
    calc (r:ℝ) ^ 2 ≤ ((r:ℝ) + 1) ^ 2 := pow_le_pow_left₀ (by positivity) (by linarith) 2
      _ ≤ _ := pow_le_pow_right₀ (by linarith) (by norm_num)
  have hP5 : (r:ℝ) ^ 5 ≤ P := by
    have : (r:ℝ) ^ 5 = (r:ℝ) ^ 2 * (r:ℝ) ^ 3 := by ring
    rw [this]; exact mul_le_mul hx2 hr3 (by positivity) (by positivity)
  have hP6 : ((r:ℝ) + 1) * ((r:ℝ) ^ 2 + 1) ≤ P := by
    have : ((r:ℝ) + 1) * ((r:ℝ) ^ 2 + 1) ≤ ((r:ℝ) + 1) ^ 3 := by nlinarith
    linarith
  have hκ' : (κ:ℝ) ≤ Cb ^ 2 * P := by
    have a1 : (κ:ℝ) ≤ Cb * ((r:ℝ) + 1) * (Cb * As) :=
      le_trans hκ (mul_le_mul_of_nonneg_left ho' (by positivity))
    have a2 : Cb * ((r:ℝ) + 1) * (Cb * As) = Cb ^ 2 * (((r:ℝ) + 1) * As) := by ring
    rw [a2] at a1
    exact le_trans a1 (mul_le_mul_of_nonneg_left hP2 (by positivity))
  have hoR : ((r:ℝ) + 1) * o ≤ Cb * P := by
    calc ((r:ℝ) + 1) * o ≤ ((r:ℝ) + 1) * (Cb * As) := mul_le_mul_of_nonneg_left ho' (by positivity)
      _ = Cb * (((r:ℝ) + 1) * As) := by ring
      _ ≤ Cb * P := mul_le_mul_of_nonneg_left hP2 hCb
  have hP0 : 0 ≤ P := by positivity
  have e1 : (r:ℝ) * (CV * ((r:ℝ) ^ 3 * n + (n:ℝ) ^ 2 + (r:ℝ) ^ 4)) =
      CV * ((r:ℝ) ^ 4 * n) + CV * ((r:ℝ) * n ^ 2) + CV * (r:ℝ) ^ 5 := by ring
  have e2 : 3 * ((r:ℝ) + 1) * (CV * ((r:ℝ) ^ 2 + 1) + o) =
      3 * CV * (((r:ℝ) + 1) * ((r:ℝ) ^ 2 + 1)) + 3 * (((r:ℝ) + 1) * o) := by ring
  rw [e1, e2]
  have := mul_le_mul_of_nonneg_left hP3 hV
  have := mul_le_mul_of_nonneg_left hP4 hV
  have := mul_le_mul_of_nonneg_left hP5 hV
  have := mul_le_mul_of_nonneg_left hP6 (by positivity : (0:ℝ) ≤ 3 * CV)
  nlinarith

theorem big_cell_threshold : C6.BigCellVanishingThreshold := by
  intro c₃ Cb hc hCb
  refine ⟨c₃ * Cb + 2 * c₃ + 3 * Cb + 4, ?_⟩
  intro r n N o As A₀ hr hn h1 h2 ho hA
  have hx : (1:ℝ) ≤ r := by exact_mod_cast hr
  have hxy : 2 * (r:ℝ) + 2 ≤ n := by exact_mod_cast hn
  have h1' : (N:ℝ) * (n:ℝ) ^ 2 ≤ As := by exact_mod_cast h1
  have h2' : (n:ℝ) ^ 3 ≤ As := by exact_mod_cast h2
  have hN : (0:ℝ) ≤ N := by positivity
  have hy : (1:ℝ) ≤ n := by linarith
  have hn2 : (n:ℝ) ^ 2 ≤ As := le_trans (by nlinarith) h2'
  have hn1 : (n:ℝ) ≤ As := le_trans (by nlinarith) hn2
  have hA1 : (1:ℝ) ≤ As := le_trans hy hn1
  have hNn : (N:ℝ) * n ≤ As := le_trans (mul_le_mul_of_nonneg_left (by nlinarith) hN) h1'
  have ho' : (o:ℝ) ≤ Cb * As := by
    calc (o:ℝ) ≤ Cb * N * n := ho
      _ = Cb * (N * n) := by ring
      _ ≤ Cb * As := mul_le_mul_of_nonneg_left hNn hCb
  set P : ℝ := ((r:ℝ) + 1) ^ 4 * As with hP
  have hAs0 : (0:ℝ) ≤ As := by linarith
  have q2 : ((r:ℝ) + 1) ^ 2 ≤ ((r:ℝ) + 1) ^ 4 := pow_le_pow_right₀ (by linarith) (by norm_num)
  have q3 : ((r:ℝ) + 1) ^ 3 ≤ ((r:ℝ) + 1) ^ 4 := pow_le_pow_right₀ (by linarith) (by norm_num)
  have q1 : ((r:ℝ) + 1) ≤ ((r:ℝ) + 1) ^ 4 := by
    calc (r:ℝ) + 1 = ((r:ℝ) + 1) ^ 1 := (pow_one _).symm
      _ ≤ _ := pow_le_pow_right₀ (by linarith) (by norm_num)
  have hR4 : (1:ℝ) ≤ ((r:ℝ) + 1) ^ 4 := one_le_pow₀ (by linarith)

  have p1 : ((r:ℝ) + 1) ^ 2 * o ≤ Cb * P := by
    calc ((r:ℝ) + 1) ^ 2 * o ≤ ((r:ℝ) + 1) ^ 4 * (Cb * As) := mul_le_mul q2 ho' (by positivity) (by positivity)
      _ = Cb * P := by rw [hP]; ring
  have p2 : ((r:ℝ) + 1) ^ 2 * ((r:ℝ) * n) ≤ P := by
    have : (r:ℝ) * n ≤ ((r:ℝ) + 1) * As := mul_le_mul (by linarith) hn1 (by positivity) (by positivity)
    calc ((r:ℝ) + 1) ^ 2 * ((r:ℝ) * n) ≤ ((r:ℝ) + 1) ^ 2 * (((r:ℝ) + 1) * As) :=
          mul_le_mul_of_nonneg_left this (by positivity)
      _ = ((r:ℝ) + 1) ^ 3 * As := by ring
      _ ≤ P := mul_le_mul_of_nonneg_right q3 hAs0
  have p3 : ((r:ℝ) + 1) ^ 2 ≤ P := by
    calc ((r:ℝ) + 1) ^ 2 = ((r:ℝ) + 1) ^ 2 * 1 := by ring
      _ ≤ ((r:ℝ) + 1) ^ 4 * As := mul_le_mul q2 hA1 (by norm_num) (by positivity)
  have p4 : ((r:ℝ) + 1) * o ≤ Cb * P := by
    calc ((r:ℝ) + 1) * o ≤ ((r:ℝ) + 1) ^ 4 * (Cb * As) := mul_le_mul q1 ho' (by positivity) (by positivity)
      _ = Cb * P := by rw [hP]; ring
  have p5 : ((r:ℝ) + 1) ≤ P := by
    calc ((r:ℝ) + 1) = ((r:ℝ) + 1) * 1 := by ring
      _ ≤ ((r:ℝ) + 1) ^ 4 * As := mul_le_mul q1 hA1 (by norm_num) (by positivity)
  have hP0 : 0 ≤ P := by positivity
  have e : c₃ * ((r:ℝ) + 1) ^ 2 * ((o:ℝ) + r * n + 1) =
      c₃ * (((r:ℝ) + 1) ^ 2 * o) + c₃ * (((r:ℝ) + 1) ^ 2 * ((r:ℝ) * n)) + c₃ * ((r:ℝ) + 1) ^ 2 := by ring
  have e' : 3 * ((r:ℝ) + 1) * ((o:ℝ) + 1) = 3 * (((r:ℝ) + 1) * o) + 3 * ((r:ℝ) + 1) := by ring
  rw [e, e']
  have := mul_le_mul_of_nonneg_left p1 hc
  have := mul_le_mul_of_nonneg_left p2 hc
  have := mul_le_mul_of_nonneg_left p3 hc
  nlinarith

end Formalism.FourierDecayAlt.P
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.FsvMulFsvNeg
section
open scoped ComplexConjugate ContDiff
open Filter Topology

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

noncomputable section

namespace Formalism.FourierDecayAlt.P5

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Wd

theorem fsv_mul_fsv_neg (s t : ℂ) : fsv s t * fsv (-s) t = 1 := by
  rw [fsv, fsv, ← Complex.exp_add]
  convert Complex.exp_zero using 2
  simp only [map_neg]
  ring

theorem fsv_neg_mul_fsv (s t : ℂ) : fsv (-s) t * fsv s t = 1 := by
  rw [mul_comm]
  exact fsv_mul_fsv_neg s t

theorem hasFDerivAt_fsv {m : ℕ} (t : ℂ) (l : Fin m) (c : Fin m → ℂ) :
    ∃ D : (Fin m → ℂ) →L[ℝ] ℂ, HasFDerivAt (fun c' : Fin m → ℂ => fsv t (c' l)) D c ∧
      D (Pi.single l 1) = (t - conj t) * fsv t (c l) ∧
      D (Pi.single l Complex.I) = Complex.I * (t + conj t) * fsv t (c l) := by
  classical
  let L : (Fin m → ℂ) →L[ℝ] ℂ := t • (ContinuousLinearMap.proj l : (Fin m → ℂ) →L[ℝ] ℂ) -
    (conj t) • (Complex.conjCLE.toContinuousLinearMap.comp (ContinuousLinearMap.proj l : (Fin m → ℂ) →L[ℝ] ℂ))
  have hL : ∀ c' : Fin m → ℂ, L c' = t * c' l - conj t * conj (c' l) := by
    intro c'
    simp [L]
  refine ⟨fsv t (c l) • L, ?_, ?_, ?_⟩
  · have h2 := (L.hasFDerivAt (x := c)).cexp
    have he : (fun c' : Fin m → ℂ => fsv t (c' l)) = fun c' => Complex.exp (L c') := by
      funext c'
      rw [hL]
      rfl
    have hc : Complex.exp (L c) = fsv t (c l) := by
      rw [hL]
      rfl
    rw [he, ← hc]
    exact h2
  · simp only [ContinuousLinearMap.smul_apply, hL, Pi.single_eq_same, map_one, smul_eq_mul]
    ring
  · simp only [ContinuousLinearMap.smul_apply, hL, Pi.single_eq_same, Complex.conj_I, smul_eq_mul]
    ring

section Leibniz

variable {m : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem wirt_fsv_smul (t : ℂ) (l : Fin m) (φ : (Fin m → ℂ) → E) (c : Fin m → ℂ)
    (hφ : DifferentiableAt ℝ φ c) :
    wirt l (fun c' => fsv t (c' l) • φ c') c = fsv t (c l) • wirt l φ c + (t * fsv t (c l)) • φ c ∧
    wirtBar l (fun c' => fsv t (c' l) • φ c') c =
      fsv t (c l) • wirtBar l φ c + (-(conj t) * fsv t (c l)) • φ c := by
  obtain ⟨D, hD, h1, hI⟩ := hasFDerivAt_fsv t l c
  have hP : HasFDerivAt (fun c' => fsv t (c' l) • φ c') (fsv t (c l) • fderiv ℝ φ c + D.smulRight (φ c)) c :=
    hD.smul hφ.hasFDerivAt
  unfold wirt wirtBar
  rw [hP.fderiv]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.smulRight_apply, h1, hI, smul_add, smul_sub, smul_smul, ← mul_assoc, Complex.I_mul_I]
  constructor <;> module

theorem pOp_fsv_smul (t : ℂ) (l : Fin m) (φ : (Fin m → ℂ) → E) (c : Fin m → ℂ)
    (hd : c ∈ OmX m → DifferentiableAt ℝ φ c) (h0 : c ∉ OmX m → φ c = 0) :
    pOp l (fun c' => fsv t (c' l) • φ c') c =
      fsv t (c l) • pOp l φ c + t • fsv t (c l) • (c l • φ c) := by
  unfold pOp
  by_cases h : c ∈ OmX m
  · rw [if_pos h, if_pos h, (wirt_fsv_smul t l φ c (hd h)).1]
    module
  · rw [if_neg h, if_neg h, h0 h]
    simp

theorem pbOp_fsv_smul (t : ℂ) (l : Fin m) (φ : (Fin m → ℂ) → E) (c : Fin m → ℂ)
    (hd : c ∈ OmX m → DifferentiableAt ℝ φ c) (h0 : c ∉ OmX m → φ c = 0) :
    pbOp l (fun c' => fsv (-t) (c' l) • φ c') c =
      fsv (-t) (c l) • pbOp l φ c + conj t • fsv (-t) (c l) • (star (c l) • φ c) := by
  unfold pbOp
  by_cases h : c ∈ OmX m
  · rw [if_pos h, if_pos h, (wirt_fsv_smul (-t) l φ c (hd h)).2]
    simp only [map_neg, neg_neg, Complex.star_def]
    module
  · rw [if_neg h, if_neg h, h0 h]
    simp

end Leibniz

section Reg

variable {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {Wp Wq : Type} [NormedAddCommGroup Wp] [NormedSpace ℂ Wp]
  [NormedAddCommGroup Wq] [NormedSpace ℂ Wq] {π : Mx k r → (Wp →L[ℂ] Wp)} {π' : Mx k r → (Wq →L[ℂ] Wq)}

theorem radSp_regular (Φ : RadSp k r z z' π π') (g : Mx k r) (c : Fin r → ℂ) :
    (c ∈ OmX r → DifferentiableAt ℝ (fun c' => (Φ : Fn k r (Wq →L[ℂ] Wp)) c' g) c) ∧
      (c ∉ OmX r → (Φ : Fn k r (Wq →L[ℂ] Wp)) c g = 0) := by
  have hΦm : (Φ : Fn k r (Wq →L[ℂ] Wp)) ∈ RadSp k r z z' π π' := Φ.2
  obtain ⟨h0, hs, -⟩ := hΦm
  refine ⟨fun hc => ?_, fun hc => h0 (c, g) (fun hx => hc (by
    simp only [DomR, Set.mem_setOf_eq] at hx
    exact hx.1))⟩
  by_cases hg : g ∈ Glev k r (Fin.last r) ∧ 0 < GGl k r z z' g
  · obtain ⟨U, F, hU, hxU, hF, hΦ⟩ := hs (c, g) (by
      simp only [DomR, Set.mem_setOf_eq]
      exact ⟨hc, hg.1, hg.2⟩)
    have hcont : Continuous (fun c' : Fin r → ℂ => (c', g)) := by fun_prop
    have hev : ∀ᶠ c' in nhds c, (Φ : Fn k r (Wq →L[ℂ] Wp)) c' g = F (c', g) := by
      have hU' : ∀ᶠ c' in nhds c, (c', g) ∈ U := hcont.continuousAt.preimage_mem_nhds (hU.mem_nhds hxU)
      filter_upwards [hU'] with c' hc'
      exact hΦ (c', g) hc' hg.1
    have hFd : DifferentiableAt ℝ F (c, g) := (hF.contDiffAt (hU.mem_nhds hxU)).differentiableAt (by simp)
    have hpair : DifferentiableAt ℝ (fun c' : Fin r → ℂ => (c', g)) c := by fun_prop
    have hcomp : DifferentiableAt ℝ (fun c' => F (c', g)) c := hFd.comp c hpair
    exact hcomp.congr_of_eventuallyEq hev
  · have hz : (fun c' => (Φ : Fn k r (Wq →L[ℂ] Wp)) c' g) = fun _ => 0 := by
      funext c'
      refine h0 (c', g) (fun hx => hg ?_)
      simp only [DomR, Set.mem_setOf_eq] at hx
      exact ⟨hx.2.1, hx.2.2⟩
    rw [hz]
    exact differentiableAt_const 0

end Reg

section PairLemmas

variable {V : Type*} [AddCommGroup V] [Module ℂ V]

theorem pr_ext {a b : Pr V} (h1 : a.1 = b.1) (h2 : a.2.unop = b.2.unop) : a = b :=
  Prod.ext h1 (MulOpposite.unop_injective h2)

@[simp] theorem mkPair_fst' (X Xs : Module.End ℂ V) : (mkP X Xs : Pr V).1 = X := rfl
@[simp] theorem mkPair_snd' (X Xs : Module.End ℂ V) : (mkP X Xs : Pr V).2.unop = Xs := rfl
@[simp] theorem pr_mul_fst (a b : Pr V) : (a * b).1 = a.1 * b.1 := rfl
@[simp] theorem pr_mul_snd (a b : Pr V) : (a * b).2.unop = b.2.unop * a.2.unop := rfl
@[simp] theorem pr_add_fst (a b : Pr V) : (a + b).1 = a.1 + b.1 := rfl
@[simp] theorem pr_add_snd (a b : Pr V) : (a + b).2.unop = a.2.unop + b.2.unop := rfl
@[simp] theorem pr_one_fst : (1 : Pr V).1 = 1 := rfl
@[simp] theorem pr_one_snd : (1 : Pr V).2.unop = 1 := rfl
@[simp] theorem pr_alg_fst (w : ℂ) : (algebraMap ℂ (Pr V) w).1 = algebraMap ℂ (Module.End ℂ V) w := rfl
@[simp] theorem pr_alg_snd (w : ℂ) :
    (algebraMap ℂ (Pr V) w).2.unop = algebraMap ℂ (Module.End ℂ V) (conj w) := rfl

end PairLemmas

theorem waveSiteAll : WaveSiteAll := by
  intro Wp Wq _ _ _ _ P z z' π π' X L hL l s Wv Wv' hW hW'
  obtain ⟨hp, -, hc, hci, -⟩ := hL
  have hW1 : ∀ (Φ : RadSp P.k P.r z z' π π') c g, (Wv Φ : Fn P.k P.r (Wq →L[ℂ] Wp)) c g =
      fsv s (c l) • (Φ : Fn P.k P.r (Wq →L[ℂ] Wp)) c g := hW
  have hW2 : ∀ (Φ : RadSp P.k P.r z z' π π') c g, (Wv' Φ : Fn P.k P.r (Wq →L[ℂ] Wp)) c g =
      fsv (-s) (c l) • (Φ : Fn P.k P.r (Wq →L[ℂ] Wp)) c g := hW'
  have hop : ∀ i (Φ : RadSp P.k P.r z z' π π'),
      (X.op l i Φ : Fn P.k P.r (Wq →L[ℂ] Wp)) = crd (opL l i) (Φ : Fn P.k P.r (Wq →L[ℂ] Wp)) :=
    fun i Φ => X.op_apply l i Φ
  have hWW' : Wv * Wv' = 1 := by
    apply LinearMap.ext; intro Φ; apply Subtype.ext; funext c g
    simp only [Module.End.mul_apply, Module.End.one_apply, hW1, hW2, smul_smul, fsv_mul_fsv_neg, one_smul]
  have hW'W : Wv' * Wv = 1 := by
    apply LinearMap.ext; intro Φ; apply Subtype.ext; funext c g
    simp only [Module.End.mul_apply, Module.End.one_apply, hW1, hW2, smul_smul, fsv_neg_mul_fsv, one_smul]

  have hcomm : ∀ (W : Module.End ℂ (RadSp P.k P.r z z' π π')) (u : ℂ → ℂ),
      (∀ (Φ : RadSp P.k P.r z z' π π') c g, (W Φ : Fn P.k P.r (Wq →L[ℂ] Wp)) c g =
        u (c l) • (Φ : Fn P.k P.r (Wq →L[ℂ] Wp)) c g) →
      ∀ i : Fin 6, (i = 1 ∨ i = 2 ∨ i = 4 ∨ i = 5) → W * X.op l i = X.op l i * W := by
    intro W u hWu i hi
    apply LinearMap.ext; intro Φ; apply Subtype.ext; funext c g
    simp only [Module.End.mul_apply, hWu, hop, crd]
    rcases hi with rfl | rfl | rfl | rfl <;>
      simp only [opL, cOp, ciOp, cbOp, cbiOp] <;> exact smul_comm _ _ _
  have hsite : ∀ f : Pr (RadSp P.k P.r z z' π π'), (site L l).p = L.p l ∧ (site L l).c = L.c l ∧
      (site L l).ci = L.ci l := fun _ => ⟨rfl, rfl, rfl⟩
  obtain ⟨hsp, hsc, hsci⟩ := hsite 0
  rw [hsp, hsc, hsci, hp l, hc l, hci l]
  refine ⟨⟨pr_ext ?_ ?_, pr_ext ?_ ?_, rfl⟩, pr_ext ?_ ?_, pr_ext ?_ ?_, pr_ext ?_ ?_⟩
  · simpa using hWW'
  · simpa using hWW'
  · simpa using hW'W
  · simpa using hW'W
  · simpa using hcomm Wv _ hW1 1 (by decide)
  · simpa using (hcomm Wv' _ hW2 4 (by decide)).symm
  · simpa using hcomm Wv _ hW1 2 (by decide)
  · simpa using (hcomm Wv' _ hW2 5 (by decide)).symm
  · simp only [mkPair_fst', pr_mul_fst, pr_add_fst, pr_alg_fst]
    apply LinearMap.ext; intro Φ; apply Subtype.ext; funext c g
    obtain ⟨hd, h0⟩ := radSp_regular Φ g c
    simp only [Module.End.mul_apply, LinearMap.add_apply, Module.algebraMap_end_apply, Submodule.coe_add,
      Submodule.coe_smul, Pi.add_apply, Pi.smul_apply, hop, crd, hW1, opL]
    rw [pOp_fsv_smul s l _ c hd h0]
    simp only [cOp]
  · simp only [mkPair_snd', pr_mul_snd, pr_add_snd, pr_alg_snd]
    apply LinearMap.ext; intro Φ; apply Subtype.ext; funext c g
    obtain ⟨hd, h0⟩ := radSp_regular Φ g c
    simp only [Module.End.mul_apply, LinearMap.add_apply, LinearMap.neg_apply, Module.algebraMap_end_apply,
      Submodule.coe_add, Submodule.coe_neg, Submodule.coe_smul, Pi.add_apply, Pi.neg_apply, Pi.smul_apply, hop,
      crd, hW2, opL]
    rw [pbOp_fsv_smul s l _ c hd h0]
    simp only [cbOp]
    module

end Formalism.FourierDecayAlt.P5
end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.JDomBoundOfNnMaj
section
open Matrix MeasureTheory Filter

noncomputable section

namespace Formalism.FourierDecayAlt.P.JFxDs2

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.JF

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

def NNMaj : Prop :=
  ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] (D : B.RealPlaceData k r Wp Wq) (A : ℝ) (m : ℕ),
    TransportedAlt k r A m →
    ∀ K : Set (B.Mat k r), IsCompact K → K ⊆ Om k r D.z D.z' →
      ∃ b : B.SS k r → ℝ, Integrable b D.μSS ∧
        ∀ u v : List (B.Mat k r), (∀ X ∈ u, B.unitLie k r X) → (∀ X ∈ v, B.unitLie k r X) →
          u.length + v.length ≤ m → ∀ g ∈ K, ∀ᵐ p ∂D.μSS,
            (u.map fun X => ‖AdL p X‖).prod * (v.map fun X => ‖AdR p X‖).prod * B.gN (B.sgs p g) ^ (-A) ≤ b p

def JDomBound : Prop :=
  ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (D : B.RealPlaceData k r Wp Wq) (A : ℝ)
    (m : ℕ) (F : B.Mat k r → (Wq →L[ℂ] Wp)),
    TransportedAlt k r A m → B.InCC A m F →
    ∀ K : Set (B.Mat k r), IsCompact K → K ⊆ Om k r D.z D.z' →
      ∃ b : B.SS k r → ℝ, Integrable b D.μSS ∧
        ∀ u v : List (B.Mat k r), (∀ X ∈ u, B.unitLie k r X) → (∀ X ∈ v, B.unitLie k r X) →
          u.length + v.length ≤ m → ∀ g ∈ K, ∀ᵐ p ∂D.μSS,
            ‖B.rho D p (B.dLR (u.map (AdL p)) (v.map (AdR p)) F) g‖ ≤ b p

def JDomMeas : Prop :=
  ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (D : B.RealPlaceData k r Wp Wq) (A : ℝ)
    (m : ℕ) (F : B.Mat k r → (Wq →L[ℂ] Wp)),
    TransportedAlt k r A m → B.InCC A m F →
    ∀ u v : List (B.Mat k r), (∀ X ∈ u, B.unitLie k r X) → (∀ X ∈ v, B.unitLie k r X) → u.length + v.length ≤ m →
      ∀ g ∈ Om k r D.z D.z',
        AEStronglyMeasurable (fun p => B.rho D p (B.dLR (u.map (AdL p)) (v.map (AdR p)) F) g) D.μSS

theorem jDom_of_parts : JDomMeas → JDomBound → Formalism.FourierDecayAlt.JF.JDom := fun hM hB k r Wp Wq _ _ _ _ _ _ D A m F hT hC =>
  ⟨hM k r Wp Wq D A m F hT hC, hB k r Wp Wq D A m F hT hC⟩

variable {k r : ℕ}

private theorem gv_mul_lemma (a b : Mat k r) (ha : a ∈ GV k r) (hb : b ∈ GV k r) : a * b ∈ GV k r := by
  have ha' : aᴴ * Hpk k r * a = Hpk k r := ha
  have hb' : bᴴ * Hpk k r * b = Hpk k r := hb
  show (a * b)ᴴ * Hpk k r * (a * b) = Hpk k r
  rw [Matrix.conjTranspose_mul]
  calc bᴴ * aᴴ * Hpk k r * (a * b) = bᴴ * (aᴴ * Hpk k r * a) * b := by simp only [mul_assoc]
    _ = Hpk k r := by rw [ha', hb']

lemma sL_mem {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] {D : RealPlaceData k r Wp Wq} {p : SS k r} (hp : D.inSS p) : sL p ∈ GV k r := by
  unfold RealPlaceData.inSS at hp
  unfold UWset QuantumDeterminants.Nset at hp
  obtain ⟨⟨h11, -⟩, ⟨h12, -⟩, -, -⟩ := hp
  unfold sL
  exact gv_mul_lemma _ _ h12 h11

lemma sR_mem {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] {D : RealPlaceData k r Wp Wq} {p : SS k r} (hp : D.inSS p) : sR p ∈ GV k r := by
  unfold RealPlaceData.inSS at hp
  unfold UWset QuantumDeterminants.Nset at hp
  obtain ⟨-, -, ⟨h21, -⟩, ⟨h22, -⟩⟩ := hp
  unfold sR
  exact gv_mul_lemma _ _ h22 h21

lemma pn_lr (p : SS k r) (u v : List (Mat k r)) :
    B4.pn (B4.lr (u.map (AdL p)) (v.map (AdR p))) =
      (u.map fun X => ‖AdL p X‖).prod * (v.map fun X => ‖AdR p X‖).prod := by
  simp [B4.pn, B4.lr, List.map_append, List.prod_append, List.map_map, Function.comp_def]

private theorem inLie_inv_mul_mul_of_mem_gv {y X : Mat k r} (hy : y ∈ GV k r) (hX : inLie k r X) : inLie k r (y⁻¹ * X * y) := by
  have hHH : Hpk k r * Hpk k r = 1 := Formalism.QuantumDeterminants.GBasic.Hpk_sq k r
  have hHH' : ∀ A : Mat k r, Hpk k r * (Hpk k r * A) = A := fun A => by rw [← mul_assoc, hHH, one_mul]
  have hX' : Xᴴ * Hpk k r + Hpk k r * X = 0 := hX
  have hy' : yᴴ * Hpk k r * y = Hpk k r := hy
  have hinv : y⁻¹ = Hpk k r * yᴴ * Hpk k r := by
    apply Matrix.inv_eq_left_inv
    simp only [mul_assoc] at hy' ⊢
    rw [hy', hHH]
  have e1 : (y⁻¹ * X * y)ᴴ * Hpk k r = yᴴ * (Xᴴ * Hpk k r) * y := by
    rw [hinv]
    simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Formalism.QuantumDeterminants.GBasic.Hpk_herm, mul_assoc,
      hHH, mul_one]
  have e2 : Hpk k r * (y⁻¹ * X * y) = yᴴ * (Hpk k r * X) * y := by
    rw [hinv]
    simp only [mul_assoc, hHH']
  show (y⁻¹ * X * y)ᴴ * Hpk k r + Hpk k r * (y⁻¹ * X * y) = 0
  rw [e1, e2, ← add_mul, ← mul_add, hX', mul_zero, zero_mul]

lemma allLie_ad {p : SS k r} (hL : sL p ∈ GV k r) (hR : sR p ∈ GV k r) {u v : List (Mat k r)}
    (hu : ∀ X ∈ u, unitLie k r X) (hv : ∀ X ∈ v, unitLie k r X) :
    B4.AllLie (B4.lr (u.map (AdL p)) (v.map (AdR p))) := by
  unfold B4.AllLie B4.lr AdL AdR
  intro x hx
  simp only [List.mem_append, List.mem_map] at hx
  rcases hx with ⟨_, ⟨X, hX, rfl⟩, rfl⟩ | ⟨_, ⟨X, hX, rfl⟩, rfl⟩
  · exact inLie_inv_mul_mul_of_mem_gv hL (hu X hX).1
  · exact inLie_inv_mul_mul_of_mem_gv hR (hv X hX).1

theorem jDomBound_of_nnMaj : NNMaj → JDomBound := by
  intro hNN k r Wp Wq _ _ _ _ _ _ D A m F hThr hCC K hK hKsub
  obtain ⟨c, hc⟩ := hCC
  obtain ⟨b, hbI, hb⟩ := hNN k r Wp Wq D A m hThr K hK hKsub
  refine ⟨fun p => c * b p, hbI.const_mul c, ?_⟩
  intro u v hu hv hl g hg
  filter_upwards [hb u v hu hv hl g hg, B7.ae_inSS D] with p hp hin
  have hgG : g ∈ GV k r := (hKsub hg).1
  have hsG : sgs p g ∈ GV k r := B7.sgs_mem D hin hgG
  have hN : 0 < gN (sgs p g) := B6.gN_pos hsG
  have hgA : 0 < gN (sgs p g) ^ A := Real.rpow_pos_of_pos hN A
  have hc0 : 0 ≤ c := by
    have h0 := hc.2 [] [] (by simp) (by simp) (by simp) g hgG
    exact le_trans (mul_nonneg (Real.rpow_pos_of_pos (B6.gN_pos hgG) A).le (norm_nonneg _)) h0
  have hall := allLie_ad (sL_mem hin) (sR_mem hin) hu hv
  have hlen : (B4.lr (u.map (AdL p)) (v.map (AdR p))).length ≤ m := by
    rw [B4.length_lr, List.length_map, List.length_map]; exact hl
  have hbd := B4.bound_scaled hc _ (B4.lrt_lr _ _) hall hlen _ hsG
  rw [← B4.dLR_eq, pn_lr] at hbd
  refine (B7.norm_rho_le D hin _ g).trans ?_
  have h1 : ‖dLR (u.map (AdL p)) (v.map (AdR p)) F (sgs p g)‖ ≤
      ((u.map fun X => ‖AdL p X‖).prod * (v.map fun X => ‖AdR p X‖).prod * c) / gN (sgs p g) ^ A := by
    rw [le_div_iff₀ hgA]
    linarith [hbd]
  refine h1.trans (le_of_eq_of_le ?_ (mul_le_mul_of_nonneg_left hp hc0))
  rw [Real.rpow_neg hN.le]
  field_simp

end Formalism.FourierDecayAlt.P.JFxDs2
end
end

