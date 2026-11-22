import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0200
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0059
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0073
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0047
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0075
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0193
import Formalism.HermitianCurvature.HermitianCurvatureProofs.RegularisedPairingViaPhase
import Formalism.HermitianCurvature.HermitianCurvatureProofs.OrbitalIntegralAeConvergenceContinuity
import Formalism.HermitianCurvature.HermitianCurvatureProofs.HaarUniquenessConjugation
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0043
import Formalism.HermitianCurvature.HermitianCurvatureProofs.AdjointLeibnizExpansion
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0202
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0187

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutERCapAdjAsm
section
namespace Formalism.FourierDecayAlt.P.CutMP.ER

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants MeasureTheory Filter Topology
open scoped ComplexConjugate ContDiff

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

noncomputable section

section clm

variable {k r : ℕ} {E E' : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup E']
  [NormedSpace ℂ E']

theorem contDiff_clm_comp (Λ : E →L[ℂ] E') {ψ : B.Mat k r → E} (hψ : ContDiff ℝ ∞ ψ) :
    ContDiff ℝ ∞ (fun g => Λ (ψ g)) :=
  (Λ.restrictScalars ℝ).contDiff.comp hψ

theorem rdV_clm (Λ : E →L[ℂ] E') {ψ : B.Mat k r → E} (hψ : ContDiff ℝ ∞ ψ) (X : B.Mat k r) :
    RdV X (fun g => Λ (ψ g)) = fun g => Λ (RdV X ψ g) := by
  rw [rdV_global (contDiff_clm_comp Λ hψ) X, rdV_global hψ X]
  funext g
  have hd : HasFDerivAt ψ (fderiv ℝ ψ g) g := ((hψ.differentiable (by simp)) g).hasFDerivAt
  have h := (Λ.restrictScalars ℝ).hasFDerivAt.comp g hd
  exact (DFunLike.congr_fun h.fderiv (g * X)).trans rfl

theorem rw_clm' (Λ : E →L[ℂ] E') {ψ : B.Mat k r → E} (hψ : ContDiff ℝ ∞ ψ) :
    ∀ w : List (B.Mat k r), B.Rw w (fun g => Λ (ψ g)) = fun g => Λ (B.Rw w ψ g)
  | [] => rfl
  | X :: w => by
    show RdV X (B.Rw w (fun g => Λ (ψ g))) = fun g => Λ (RdV X (B.Rw w ψ) g)
    rw [rw_clm' Λ hψ w, rdV_clm Λ (rw_contDiff hψ w) X]

end clm

section comps

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

def lam (i : Fin (Module.finrank ℂ Wq)) (j : Fin (Module.finrank ℂ Wp)) : (Wq →L[ℂ] Wp) →L[ℂ] ℂ :=
  (innerSL ℂ (stdOrthonormalBasis ℂ Wp j)).comp (ContinuousLinearMap.apply ℂ Wp (stdOrthonormalBasis ℂ Wq i))

theorem lam_apply (i j) (A : Wq →L[ℂ] Wp) :
    lam i j A = inner ℂ (stdOrthonormalBasis ℂ Wp j) (A (stdOrthonormalBasis ℂ Wq i)) := rfl

theorem hsInner_eq_sum (A C : Wq →L[ℂ] Wp) :
    B.hsInner A C = ∑ i, ∑ j, lam i j A * star (lam i j C) := by
  unfold B.hsInner B.hsVec
  rw [PiLp.inner_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [PiLp.toLp_apply]
  rw [← (stdOrthonormalBasis ℂ Wp).sum_inner_mul_inner]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [lam_apply, lam_apply, mul_comm]
  congr 1
  rw [← inner_conj_symm]
  rfl

end comps

section terms

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

theorem lam_opAdj_tail (i j) (s : ℂ) {ψ : B.Mat k r → (Wq →L[ℂ] Wp)} (hψ : ContDiff ℝ ∞ ψ) :
    ∀ (L : List (ℂ × List (B.Mat k r))), (∀ cw ∈ L, ∀ X ∈ cw.2, B.inLie k r X) → ∀ g,
    lam i j (((L.map fun cw => TLB.cTerm (Wp := Wp) (Wq := Wq) (s * cw.1) cw.2).map
        (fun T => ((-1 : ℂ) ^ T.word.length) • B.Rw T.word.reverse (fun x => T.coefAdj x (ψ x)) g)).sum) =
      conj s * (L.map fun cw => conj cw.1 * (-1 : ℂ) ^ cw.2.length *
        B.Rw cw.2.reverse (fun x => lam i j (ψ x)) g).sum
  | [], _, g => by simp
  | cw :: L, hL, g => by
    simp only [List.map_cons, List.sum_cons, map_add, mul_add]
    rw [lam_opAdj_tail i j s hψ L (fun cw' h => hL cw' (List.mem_cons_of_mem _ h)) g]
    congr 1
    rw [TLB.cTerm_word (hL cw List.mem_cons_self)]
    have e : (fun x => (TLB.cTerm (Wp := Wp) (Wq := Wq) (s * cw.1) cw.2).coefAdj x (ψ x)) =
        conj (s * cw.1) • ψ := by
      funext x; simp [TLB.cTerm]
    rw [e, Formalism.FourierDecayAlt.P.PositiveOrbitOpen.rw_smul, map_smul, Pi.smul_apply, map_smul]
    have e2 := congrFun (rw_clm' (lam i j) hψ cw.2.reverse) g
    rw [← e2, smul_eq_mul, smul_eq_mul, map_mul]
    ring

theorem lam_wordSum (i j) {ψ : B.Mat k r → (Wq →L[ℂ] Wp)} (hψ : ContDiff ℝ ∞ ψ) :
    ∀ (L : List (ℂ × List (B.Mat k r))) (g : B.Mat k r),
    lam i j ((L.map fun cw => cw.1 • B.Rw cw.2 ψ g).sum) =
      (L.map fun cw => cw.1 • B.Rw cw.2 (fun x => lam i j (ψ x)) g).sum
  | [], _ => by simp
  | cw :: L, g => by
    simp only [List.map_cons, List.sum_cons, map_add, map_smul]
    rw [lam_wordSum i j hψ L g, congrFun (rw_clm' (lam i j) hψ cw.2) g]

theorem wsAdj_contDiff (L : List (ℂ × List (B.Mat k r))) {b : B.Mat k r → ℂ} (hb : ContDiff ℝ ∞ b) :
    ContDiff ℝ ∞ (wsAdj L b) := by
  unfold wsAdj
  exact contDiff_listSum (fun (cw : ℂ × List (B.Mat k r)) x => conj cw.1 * (-1 : ℂ) ^ cw.2.length * B.Rw cw.2.reverse b x) L
    fun cw _ => contDiff_const.mul (rw_contDiff hb _)

end terms

theorem capacity_adjoint_integral_scalar : CapAdjIntOfScalar := by
  intro hS k r Wp Wq _ _ _ _ _ _ s Y μ hμ φ ψ hφ hφc hψ hψc
  haveI : IsFiniteMeasureOnCompacts μ := ⟨hμ.finite_compact⟩
  have hLw := (Classical.choose_spec (Formalism.FourierDecayAlt.P.capelli_word_sum k r Y)).1
  obtain ⟨L', hL', hCV'⟩ := Formalism.FourierDecayAlt.P.capelli_word_sum k r (conj Y)
  set a : Fin (Module.finrank ℂ Wq) → Fin (Module.finrank ℂ Wp) → B.Mat k r → ℂ :=
    fun i j g => lam i j (φ g) with ha
  set b : Fin (Module.finrank ℂ Wq) → Fin (Module.finrank ℂ Wp) → B.Mat k r → ℂ :=
    fun i j g => lam i j (ψ g) with hb
  have ha_s : ∀ i j, ContDiff ℝ ∞ (a i j) := fun i j => contDiff_clm_comp (lam i j) hφ
  have hb_s : ∀ i j, ContDiff ℝ ∞ (b i j) := fun i j => contDiff_clm_comp (lam i j) hψ
  have ha_c : ∀ i j, HasCompactSupport (a i j) := fun i j => hφc.comp_left (map_zero (lam i j))
  have hb_c : ∀ i j, HasCompactSupport (b i j) := fun i j => hψc.comp_left (map_zero (lam i j))

  have hAdj : ∀ i j g, lam i j (B.opAdj (capTh k r Wp Wq s Y) ψ g) = conj s * wsAdj (capLw k r Y) (b i j) g := by
    intro i j g
    unfold B.opAdj
    rw [capTh, TLB.capOp, List.map_cons, List.sum_cons, map_add]
    have h0 : (fun x => (TLB.cTerm (Wp := Wp) (Wq := Wq) 0
        (List.replicate (2 * r + k + 1) (0 : B.Mat k r))).coefAdj x (ψ x)) = (0 : ℂ) • ψ := by
      funext x; simp [TLB.cTerm]
    rw [h0, Formalism.FourierDecayAlt.P.PositiveOrbitOpen.rw_smul, zero_smul]
    rw [lam_opAdj_tail i j s hψ (capLw k r Y) (fun cw h X hX => ((hLw cw h).1 X hX).1) g]
    simp [wsAdj, b]

  have hCVc : ∀ i j, ∀ g ∈ B.GV k r, lam i j (Q.CV k r (conj Y) ψ g) = Q.CV k r (conj Y) (b i j) g := by
    intro i j g hg
    rw [hCV' _ (B.GV k r) ψ (ckOn_of_contDiff hψ _ _) g hg hg,
      hCV' _ (B.GV k r) (b i j) (ckOn_of_contDiff (hb_s i j) _ _) g hg hg]
    exact lam_wordSum i j hψ L' g

  have hP1 : ∀ x : Mt k r, B.hsInner (φ (Matrix.of x)) (B.opAdj (capTh k r Wp Wq s Y) ψ (Matrix.of x)) =
      ∑ i, ∑ j, s * (a i j (Matrix.of x) * star (wsAdj (capLw k r Y) (b i j) (Matrix.of x))) := by
    intro x
    rw [hsInner_eq_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [hAdj, star_mul', Complex.star_def, Complex.conj_conj]
    simp only [ha]; ring
  have hP2 : ∀ᵐ x ∂μ, B.hsInner (φ (Matrix.of x)) (conj s • Q.CV k r (conj Y) ψ (Matrix.of x)) =
      ∑ i, ∑ j, s * (a i j (Matrix.of x) * star (Q.CV k r (conj Y) (b i j) (Matrix.of x))) := by
    filter_upwards [Formalism.FourierDecayAlt.P.HaarUniquenessConjugation.ae_mem hμ] with x hx
    rw [hsInner_eq_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [map_smul, hCVc i j _ hx, smul_eq_mul, star_mul', Complex.star_def, Complex.conj_conj]
    simp only [ha]; ring

  have hI1 : ∀ i j, Integrable (fun x : Mt k r => s * (a i j (Matrix.of x) *
      star (wsAdj (capLw k r Y) (b i j) (Matrix.of x)))) μ := by
    intro i j
    have hc : Continuous (fun x : Mt k r => a i j (Matrix.of x) * star (wsAdj (capLw k r Y) (b i j) (Matrix.of x))) :=
      (ha_s i j).continuous.mul (continuous_star.comp (wsAdj_contDiff _ (hb_s i j)).continuous)
    have hcs : HasCompactSupport
        (fun x : Mt k r => a i j (Matrix.of x) * star (wsAdj (capLw k r Y) (b i j) (Matrix.of x))) :=
      (ha_c i j).mul_right
    exact (hc.integrable_of_hasCompactSupport (μ := μ) hcs).const_mul s
  have hI2 : ∀ i j, Integrable (fun x : Mt k r => s * (a i j (Matrix.of x) *
      star (Q.CV k r (conj Y) (b i j) (Matrix.of x)))) μ := by
    intro i j
    have hS' : ContDiff ℝ ∞ (fun g => (L'.map fun cw => cw.1 • B.Rw cw.2 (b i j) g).sum) :=
      contDiff_listSum (fun cw g => cw.1 • B.Rw cw.2 (b i j) g) L' fun cw _ =>
        (rw_contDiff (hb_s i j) _).const_smul _
    have hc : Continuous (fun x : Mt k r => a i j (Matrix.of x) *
        star ((L'.map fun cw => cw.1 • B.Rw cw.2 (b i j) (Matrix.of x)).sum)) :=
      (ha_s i j).continuous.mul (continuous_star.comp hS'.continuous)
    have hcs : HasCompactSupport (fun x : Mt k r => a i j (Matrix.of x) *
        star ((L'.map fun cw => cw.1 • B.Rw cw.2 (b i j) (Matrix.of x)).sum)) :=
      (ha_c i j).mul_right
    refine ((hc.integrable_of_hasCompactSupport (μ := μ) hcs).const_mul s).congr ?_
    filter_upwards [Formalism.FourierDecayAlt.P.HaarUniquenessConjugation.ae_mem hμ] with x hx
    rw [hCV' _ (B.GV k r) (b i j) (ckOn_of_contDiff (hb_s i j) _ _) _ hx hx]
  rw [integral_congr_ae (Eventually.of_forall hP1), integral_congr_ae hP2,
    integral_finset_sum _ (fun i _ => integrable_finset_sum _ fun j _ => hI1 i j),
    integral_finset_sum _ (fun i _ => integrable_finset_sum _ fun j _ => hI2 i j)]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [integral_finset_sum _ (fun j _ => hI1 i j), integral_finset_sum _ (fun j _ => hI2 i j)]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [integral_const_mul, integral_const_mul,
    hS k r Y μ hμ (a i j) (b i j) (ha_s i j) (ha_c i j) (hb_s i j) (hb_c i j)]

theorem capAdjInt_of_scalar (hS : CapAdjScalar) : CapAdjInt := capacity_adjoint_integral_scalar hS

end

end Formalism.FourierDecayAlt.P.CutMP.ER
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutERCapAdjS
section
namespace Formalism.FourierDecayAlt.P.CutMP.ER

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants MeasureTheory Filter Topology
open scoped ComplexConjugate ContDiff

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

noncomputable section

namespace CAS

variable {k r : ℕ}

def TF (a : B.Mat k r → ℂ) : Prop := ContDiff ℝ ∞ a ∧ HasCompactSupport a

theorem tsupport_rdV {ψ : B.Mat k r → ℂ} (hψ : ContDiff ℝ ∞ ψ) (X : B.Mat k r) :
    tsupport (RdV X ψ) ⊆ tsupport ψ := by
  apply closure_minimal _ (isClosed_tsupport ψ)
  intro g hg
  by_contra hgs
  apply hg
  have hopen : IsOpen (tsupport ψ)ᶜ := (isClosed_tsupport ψ).isOpen_compl
  have hcont : Continuous (fun t : ℝ => g * NormedSpace.exp ((t : ℂ) • X)) :=
    continuous_const.mul (Formalism.REAL.continuous_exp_real_smul X)
  have hmem : (fun t : ℝ => g * NormedSpace.exp ((t : ℂ) • X)) ⁻¹' (tsupport ψ)ᶜ ∈ 𝓝 (0 : ℝ) := by
    apply hcont.continuousAt.preimage_mem_nhds
    apply hopen.mem_nhds
    simpa using hgs
  have hev : (fun t : ℝ => ψ (g * NormedSpace.exp ((t : ℂ) • X))) =ᶠ[𝓝 0] fun _ => 0 := by
    filter_upwards [hmem] with t ht
    exact image_eq_zero_of_notMem_tsupport ht
  show deriv _ 0 = 0
  rw [hev.deriv_eq]
  simp

theorem tf_rdV {a : B.Mat k r → ℂ} (ha : TF a) (X : B.Mat k r) : TF (RdV X a) := by
  exact ⟨rdV_contDiff ha.1 X, ha.2.mono' ((subset_tsupport _).trans (tsupport_rdV ha.1 X))⟩

theorem tf_rw {a : B.Mat k r → ℂ} (ha : TF a) : ∀ w : List (B.Mat k r), TF (B.Rw w a)
  | [] => ha
  | X :: w => tf_rdV (tf_rw ha w) X

theorem level_zero_set_eq_group : Q.Glev k r 0 = B.GV k r := by
  ext g
  simp only [Q.Glev, Set.mem_setOf_eq, B.GV, Fin.val_zero, Nat.not_lt_zero, IsEmpty.forall_iff, implies_true,
    and_true]

theorem haar0 {μ : Measure (Mt k r)} (h : B.IsHaarOn (B.GV k r) μ) : B.IsHaarOn (Q.Glev k r 0) μ := by
  rw [level_zero_set_eq_group]
  exact h

theorem lie0 {X : B.Mat k r} (hX : B.inLie k r X) : Q.inLieLev k r 0 X := by
  exact ⟨hX, fun a ha => absurd ha (Nat.not_lt_zero _)⟩

theorem smooth0 {a : B.Mat k r → ℂ} (ha : ContDiff ℝ ∞ a) : Q.SmoothLev k r 0 Set.univ a := by
  exact fun g₀ _ => ⟨Set.univ, a, isOpen_univ, trivial, ha.contDiffOn, fun _ _ _ => rfl⟩

theorem cpt0 {a : B.Mat k r → ℂ} (ha : HasCompactSupport a) : Q.CptOn k r 0 a := by
  exact ⟨tsupport a, ha, fun g _ hg => image_eq_zero_of_notMem_tsupport hg⟩

theorem word_adj_scalar {μ : Measure (Mt k r)} (h : B.IsHaarOn (B.GV k r) μ) :
    ∀ (w : List (B.Mat k r)), (∀ X ∈ w, B.inLie k r X) → ∀ {a b : B.Mat k r → ℂ}, TF a → TF b →
      (∫ x : Mt k r, B.Rw w a (Matrix.of x) * star (b (Matrix.of x)) ∂μ) =
        (-1 : ℂ) ^ w.length * ∫ x : Mt k r, a (Matrix.of x) * star (B.Rw w.reverse b (Matrix.of x)) ∂μ
  | [], _, a, b, _, _ => by simp [B.Rw]
  | X :: w, hw, a, b, ha, hb => by
    have hX : B.inLie k r X := hw X (by simp)
    have hw' : ∀ Z ∈ w, B.inLie k r Z := fun Z hZ => hw Z (by simp [hZ])
    have e1 : B.Rw (X :: w) a = RdV X (B.Rw w a) := rfl
    have e2 : B.Rw (X :: w).reverse b = B.Rw w.reverse (RdV X b) := by
      simp only [B.Rw, List.reverse_cons, List.foldr_append, List.foldr_cons, List.foldr_nil]
    have hra := tf_rw ha w
    have sk := Formalism.FourierDecayAlt.P.right_differential_skew k r 0 μ (haar0 h) X (B.Rw w a) b (lie0 hX) (smooth0 hra.1)
      (smooth0 hb.1) (cpt0 hra.2) (cpt0 hb.2)
    rw [e1, sk, word_adj_scalar h w hw' ha (tf_rdV hb X), e2, List.length_cons, pow_succ]
    ring

end CAS

open CAS in
theorem capacity_adjoint_scalar : CapAdjScalar := by
  intro k r Y μ h a b ha hac hb hbc
  have ta : TF a := ⟨ha, hac⟩
  have tb : TF b := ⟨hb, hbc⟩
  have : IsFiniteMeasureOnCompacts μ := ⟨h.finite_compact⟩
  obtain ⟨hLw, hCV⟩ := Classical.choose_spec (Formalism.FourierDecayAlt.P.capelli_word_sum k r Y)
  have hLie : ∀ cw ∈ capLw k r Y, ∀ X ∈ cw.2, B.inLie k r X := fun cw hc X hX => ((hLw cw hc).1 X hX).1

  have hintA : ∀ v : B.Mat k r → ℂ, Continuous v →
      Integrable (fun x : Mt k r => a (Matrix.of x) * star (v (Matrix.of x))) μ := by
    intro v hv
    have hc : Continuous (fun x : Mt k r => a (Matrix.of x) * star (v (Matrix.of x))) :=
      ha.continuous.mul (continuous_star.comp hv)
    have hs : HasCompactSupport (fun x : Mt k r => a (Matrix.of x) * star (v (Matrix.of x))) :=
      hac.mono fun x hx h0 => hx (by show a x * _ = 0; rw [h0, zero_mul])
    exact hc.integrable_of_hasCompactSupport hs
  have hintB : ∀ v : B.Mat k r → ℂ, Continuous v →
      Integrable (fun x : Mt k r => v (Matrix.of x) * star (b (Matrix.of x))) μ := by
    intro v hv
    have hc : Continuous (fun x : Mt k r => v (Matrix.of x) * star (b (Matrix.of x))) :=
      hv.mul (continuous_star.comp hb.continuous)
    have hs : HasCompactSupport (fun x : Mt k r => v (Matrix.of x) * star (b (Matrix.of x))) :=
      hbc.mono fun x hx h0 => hx (by show _ * star (b x) = 0; rw [h0, star_zero, mul_zero])
    exact hc.integrable_of_hasCompactSupport hs

  have hH := Formalism.FourierDecayAlt.P.hermitian_haar_invariance k r 0 0 0 μ (haar0 h) (fun _ _ => rfl) (fun _ _ => rfl) a b
    (smooth0 ha) (smooth0 hb) (cpt0 hac) (cpt0 hbc) Y 0 0
  have eT : ∀ (Y' : ℂ), Q.tL k r (E := ℂ) 0 0 0 Y' 0 0 = Q.CV k r Y' := fun _ => rfl
  have eS : star Y = conj Y := rfl
  rw [eT, eT, eS] at hH
  rw [← hH]

  have e2 : (∫ x : Mt k r, Q.CV k r Y a (Matrix.of x) * star (b (Matrix.of x)) ∂μ) =
      ∫ x : Mt k r, ((capLw k r Y).map fun cw =>
        cw.1 * (B.Rw cw.2 a (Matrix.of x) * star (b (Matrix.of x)))).sum ∂μ := by
    refine integral_congr_ae ?_
    filter_upwards [Formalism.FourierDecayAlt.P.B5.haar_ae h] with x hx
    have := hCV ℂ (B.GV k r) a (ckOn_of_contDiff ha _ _) (Matrix.of x) hx hx
    rw [this, ← List.sum_map_mul_right]
    refine congrArg List.sum (List.map_congr_left fun cw _ => ?_)
    rw [smul_eq_mul, mul_assoc]

  have e1 : (∫ x : Mt k r, a (Matrix.of x) * star (wsAdj (capLw k r Y) b (Matrix.of x)) ∂μ) =
      ∫ x : Mt k r, ((capLw k r Y).map fun cw =>
        cw.1 * ((-1 : ℂ) ^ cw.2.length * (a (Matrix.of x) * star (B.Rw cw.2.reverse b (Matrix.of x))))).sum ∂μ := by
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only [wsAdj, Complex.star_def, map_list_sum, List.map_map, ← List.sum_map_mul_left]
    refine congrArg List.sum (List.map_congr_left fun cw _ => ?_)
    simp only [Function.comp_apply, map_mul, map_pow, map_neg, map_one, Complex.conj_conj]
    ring
  rw [e1, e2,
    (Formalism.FourierDecayAlt.P.B5.integral_listSum μ _ _ fun cw _ =>
      ((hintA _ (tf_rw tb _).1.continuous).const_mul _).const_mul _).2,
    (Formalism.FourierDecayAlt.P.B5.integral_listSum μ _ _ fun cw _ => (hintB _ (tf_rw ta _).1.continuous).const_mul _).2]
  refine congrArg List.sum (List.map_congr_left fun cw hcw => ?_)
  rw [integral_const_mul, integral_const_mul, integral_const_mul,
    word_adj_scalar h cw.2 (hLie cw hcw) ta tb]

end

end Formalism.FourierDecayAlt.P.CutMP.ER
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJAFFStableAdjFund
section
namespace Formalism.FourierDecayAlt.P.CutMP.JA.FFS

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants MeasureTheory Filter Topology
open scoped ComplexConjugate ContDiff

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

noncomputable section

theorem fundG_hs_sub_left {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] (A A' C : Wq →L[ℂ] Wp) :
    B.hsInner (A - A') C = B.hsInner A C - B.hsInner A' C := by
  unfold B.hsInner
  simp only [← Formalism.FourierDecayAlt.P.B5.hsL_apply, map_sub, inner_sub_right]

theorem fundamental_domain_group : FundG := by
  intro k r Wp Wq _ _ _ _ _ _ D A A' hA hA' hI g₀ hg₀
  have hμ := D.haarG
  have : IsFiniteMeasureOnCompacts D.μG := ⟨hμ.finite_compact⟩
  have hg₀G : g₀ ∈ B.GV k r := hg₀.1
  have hG0 : 0 < Gf k r D.z D.z' g₀ := hg₀.2
  by_contra hne
  set C : Wq →L[ℂ] Wp := A g₀ - A' g₀ with hC
  have hC0 : C ≠ 0 := sub_ne_zero.2 hne
  have hvC : B.hsVec C ≠ 0 := fun h0 => hC0 (Formalism.FourierDecayAlt.P.JFxI.hsVec_injective (h0.trans (by
      rw [← Formalism.FourierDecayAlt.P.B5.hsL_apply, map_zero])))
  set u : B.Mat k r → ℝ := fun x => (B.hsInner (A x) C - B.hsInner (A' x) C).re with hu
  have hu0 : u g₀ = ‖B.hsVec C‖ ^ 2 := by
    show (B.hsInner (A g₀) C - B.hsInner (A' g₀) C).re = _
    rw [← fundG_hs_sub_left]
    unfold B.hsInner
    rw [inner_self_eq_norm_sq_to_K]
    norm_cast
  have hpos0 : 0 < u g₀ := by rw [hu0]; positivity
  have huc : ContinuousOn u (B.GV k r) := by
    have hhs := Formalism.FourierDecayAlt.P.B5.hs_continuous (Wp := Wp) (Wq := Wq)
    have h1 : ContinuousOn (fun x => B.hsInner (A x) C) (B.GV k r) :=
      hhs.comp_continuousOn (f := fun x => (A x, C)) (hA.prodMk continuousOn_const)
    have h2 : ContinuousOn (fun x => B.hsInner (A' x) C) (B.GV k r) :=
      hhs.comp_continuousOn (f := fun x => (A' x, C)) (hA'.prodMk continuousOn_const)
    exact Complex.continuous_re.comp_continuousOn (h1.sub h2)

  have hgf := Formalism.FourierDecayAlt.P.DifferentialOperatorClasses.gf_cont k r D.z D.z'
  obtain ⟨ε1, hε1, h1⟩ := Metric.continuousOn_iff.1 huc g₀ hg₀G (u g₀ / 2) (by positivity)
  obtain ⟨ε2, hε2, h2⟩ := Metric.continuous_iff.1 hgf g₀ (Gf k r D.z D.z' g₀ / 2) (by positivity)
  set ε := min ε1 ε2 with hε
  have hεpos : 0 < ε := lt_min hε1 hε2
  have hgood : ∀ x ∈ B.GV k r, dist x g₀ < ε → 0 < u x ∧ x ∈ B.GPos D := by
    intro x hx hd
    have hd1 := h1 x hx (lt_of_lt_of_le hd (min_le_left _ _))
    have hd2 := h2 x (lt_of_lt_of_le hd (min_le_right _ _))
    rw [Real.dist_eq] at hd1 hd2
    refine ⟨by linarith [(abs_lt.1 hd1).1], hx, ?_⟩
    show 0 < Gf k r D.z D.z' x
    linarith [(abs_lt.1 hd2).1]

  obtain ⟨β, hβin, hβout⟩ : ∃ β : ContDiffBump g₀, β.rIn = ε / 4 ∧ β.rOut = ε / 2 :=
    ⟨⟨ε / 4, ε / 2, by positivity, by linarith⟩, rfl, rfl⟩
  have hβd : ∀ x : B.Mat k r, β x ≠ 0 → dist x g₀ < ε / 2 := by
    intro x hx
    by_contra hc
    push Not at hc
    exact hx (β.zero_of_le_dist (by rw [hβout]; exact hc))
  set φ : B.Mat k r → (Wq →L[ℂ] Wp) := fun g => ((β g : ℝ) : ℂ) • C with hφ
  have hφs : ContDiff ℝ ∞ φ := (Complex.ofRealCLM.contDiff.comp β.contDiff).smul contDiff_const
  have hφc : HasCompactSupport φ := (β.hasCompactSupport.comp_left Complex.ofReal_zero).smul_right
  have hφsupp : B.SuppIn (B.GPos D) φ := by
    intro x hx
    have hsub : {g | g ∈ B.GV k r ∧ φ g ≠ 0} ⊆ Metric.closedBall g₀ (ε / 2) ∩ B.GV k r := by
      rintro g ⟨hgG, hg⟩
      refine ⟨?_, hgG⟩
      have hβ0 : β g ≠ 0 := fun h0 => hg (by simp [hφ, h0])
      exact Metric.mem_closedBall.2 (le_of_lt (hβd g hβ0))
    have hGc : IsClosed (B.GV k r) := Formalism.FourierDecayAlt.P.B7.isClosed_GV
    have hcl : IsClosed (Metric.closedBall g₀ (ε / 2) ∩ B.GV k r) := Metric.isClosed_closedBall.inter hGc
    have hx' := closure_minimal hsub hcl hx
    exact (hgood x hx'.2 (lt_of_le_of_lt (Metric.mem_closedBall.1 hx'.1) (by linarith))).2
  have hEq := hI φ (Formalism.FourierDecayAlt.P.CutMP.ER.ckOn_of_contDiff hφs ⊤ _) hφc hφsupp

  have hGc' : IsClosed {x : Mt k r | Matrix.of x ∈ B.GV k r} := Formalism.FourierDecayAlt.P.B7.isClosed_GV
  have hK : IsCompact ({x : Mt k r | Matrix.of x ∈ B.GV k r} ∩ tsupport φ) := hφc.isCompact.inter_left hGc'
  have hint : ∀ A₁ : B.Mat k r → (Wq →L[ℂ] Wp), ContinuousOn A₁ (B.GV k r) →
      Integrable (fun x : Mt k r => B.hsInner (A₁ (Matrix.of x)) (φ (Matrix.of x))) D.μG := by
    intro A₁ hA₁
    have hof : Continuous (fun x : Mt k r => (Matrix.of x : B.Mat k r)) := continuous_id
    have hc : ContinuousOn (fun x : Mt k r => B.hsInner (A₁ (Matrix.of x)) (φ (Matrix.of x)))
        ({x : Mt k r | Matrix.of x ∈ B.GV k r} ∩ tsupport φ) :=
      (Formalism.FourierDecayAlt.P.B5.hs_continuous (Wp := Wp) (Wq := Wq)).comp_continuousOn
        (f := fun x : Mt k r => (A₁ (Matrix.of x), φ (Matrix.of x)))
        ((hA₁.comp hof.continuousOn (fun x hx => hx.1)).prodMk (hφs.continuous.comp hof).continuousOn)
    refine (hc.integrableOn_compact hK).integrable_of_ae_notMem_eq_zero ?_
    filter_upwards [Formalism.FourierDecayAlt.P.HaarUniquenessConjugation.ae_mem hμ] with x hxG hxK
    have hx : x ∉ tsupport φ := fun h => hxK ⟨hxG, h⟩
    show B.hsInner (A₁ (Matrix.of x)) (φ (Matrix.of x)) = 0
    have hz : φ (Matrix.of x) = 0 := image_eq_zero_of_notMem_tsupport hx
    rw [hz]
    exact Formalism.FourierDecayAlt.P.B5.hs_zero_right _
  have i1 := hint A hA
  have i2 := hint A' hA'

  set h : Mt k r → ℝ := fun x => β (Matrix.of x) * u (Matrix.of x) with hh
  have hpt : ∀ x : Mt k r, (B.hsInner (A (Matrix.of x)) (φ (Matrix.of x)) -
      B.hsInner (A' (Matrix.of x)) (φ (Matrix.of x))).re = h x := by
    intro x
    simp only [hh, hu, hφ, Formalism.FourierDecayAlt.P.B5.hs_smul_right, Complex.conj_ofReal, ← mul_sub, Complex.re_ofReal_mul]
  have hintR : Integrable h D.μG :=
    (i1.sub i2).re.congr (Eventually.of_forall fun x => by rw [← hpt x]; rfl)
  have hzero : ∫ x, h x ∂D.μG = 0 := by
    have e := integral_re (i1.sub i2)
    simp only [Pi.sub_apply] at e
    rw [integral_sub i1 i2, hEq, sub_self, map_zero] at e
    rw [← e]
    exact integral_congr_ae (Eventually.of_forall fun x => by rw [← hpt x]; rfl)
  have hnn : 0 ≤ᵐ[D.μG] h := by
    filter_upwards [Formalism.FourierDecayAlt.P.HaarUniquenessConjugation.ae_mem hμ] with x hxG
    show 0 ≤ β (Matrix.of x) * u (Matrix.of x)
    by_cases hb : β (Matrix.of x) = 0
    · rw [hb, zero_mul]
    · exact mul_nonneg β.nonneg (hgood _ hxG (by linarith [hβd _ hb])).1.le
  have hae : h =ᵐ[D.μG] 0 := (integral_eq_zero_iff_of_nonneg_ae hnn hintR).1 hzero

  have hO : IsOpen {x : Mt k r | 0 < β (Matrix.of x)} := isOpen_lt continuous_const β.continuous
  have hg₀O : (g₀ : Mt k r) ∈ {x : Mt k r | 0 < β (Matrix.of x)} := by
    show 0 < β g₀
    rw [β.one_of_mem_closedBall (Metric.mem_closedBall_self β.rIn_pos.le)]
    exact one_pos
  apply Formalism.FourierDecayAlt.P.CutMP.ER.haar_open_pos hμ hO (g₀ := g₀) hg₀G hg₀O
  rw [measure_eq_zero_iff_ae_notMem]
  filter_upwards [hae, Formalism.FourierDecayAlt.P.HaarUniquenessConjugation.ae_mem hμ] with x hx0 hxG hxO
  have hb : 0 < β (Matrix.of x) := hxO
  have hpos : 0 < h x := mul_pos hb (hgood _ hxG (by linarith [hβd _ hb.ne'])).1
  rw [hx0] at hpos
  exact lt_irrefl _ hpos

end

end Formalism.FourierDecayAlt.P.CutMP.JA.FFS
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJDQQAsm
section
namespace Formalism.FourierDecayAlt.P.CutMP

theorem jDecayTrQQ_of_open (h2 : JDHatOpQQ) : JDecayTrQQ := jDecayTrQQd_of_open h2

end Formalism.FourierDecayAlt.P.CutMP
end

