import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0152
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0149

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.LocalNablaHolds
section
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Polynomial

namespace Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.LNab

noncomputable section

open Formalism.FourierDecayAlt.P.CutMP.Gauge.GC

section ring

variable {P : M.Par} {A : Type} [Ring A] [StarRing A] [Algebra ℂ A]

private theorem natDegree_prod_X_add_C_le_card (S : Finset ℕ) (a : ℕ → ℂ) :
    (∏ i ∈ S, (X + C (a i))).natDegree ≤ S.card := by
  refine (Polynomial.natDegree_prod_le _ _).trans ?_
  refine (Finset.sum_le_sum (fun i _ => (Polynomial.natDegree_X_add_C (a i)).le)).trans ?_
  simp

private theorem xpol_natDegree_le (P : M.Par) (ρ : M.Ty P) : (xpol P ρ).natDegree ≤ P.k - 1 := by
  have h2 := natDegree_prod_X_add_C_le_card (Finset.Icc 1 (P.k - 1)) (fun i => ((M.rho P ρ i : ℝ) : ℂ))
  beta_reduce at h2
  have h3 : (Finset.Icc 1 (P.k - 1)).card = P.k - 1 := by rw [Nat.card_Icc]; omega
  unfold xpol
  omega

theorem xpol_half_deg (P : M.Par) (hk : 1 ≤ P.k) (ρ : M.Ty P) (s : ℂ) :
    ((xpol P ρ) * (X + C s)).natDegree ≤ P.k := by
  refine Polynomial.natDegree_mul_le.trans ?_
  rw [Polynomial.natDegree_X_add_C]
  have := xpol_natDegree_le P ρ
  omega

theorem xpol_halfm_deg (P : M.Par) (hk : 1 ≤ P.k) (ρ : M.Ty P) (s : ℂ) :
    ((xpol P ρ) * (X - C s)).natDegree ≤ P.k := by
  refine Polynomial.natDegree_mul_le.trans ?_
  rw [Polynomial.natDegree_X_sub_C]
  have := xpol_natDegree_le P ρ
  omega

theorem xpol_deg (P : M.Par) (ρ : M.Ty P) : (xpol P ρ).natDegree ≤ P.k := by
  have := xpol_natDegree_le P ρ
  omega

private theorem xepol_natDegree_le (P : M.Par) {l : ℕ} (hl : l ∈ Finset.Icc 1 (P.k - 1)) (ρ : M.Ty P) :
    (xepol P l ρ).natDegree ≤ P.k - 2 := by
  have h2 := natDegree_prod_X_add_C_le_card (Finset.Icc 1 (P.k - 1) \ {l}) (fun i => ((M.rho P ρ i : ℝ) : ℂ))
  beta_reduce at h2
  have h3 : (Finset.Icc 1 (P.k - 1) \ {l}).card = P.k - 2 := by
    rw [Finset.sdiff_singleton_eq_erase, Finset.card_erase_of_mem hl, Nat.card_Icc]; omega
  unfold xepol
  omega

theorem xepol_deg (P : M.Par) {l : ℕ} (hl : l ∈ Finset.Icc 1 (P.k - 1)) (ρ : M.Ty P) (c : ℂ) :
    (C c * xepol P l ρ).natDegree ≤ P.k := by
  have := xepol_natDegree_le P hl ρ
  exact (Polynomial.natDegree_C_mul_le c _).trans (by omega)

theorem xepol_coeff (P : M.Par) (hk : 2 ≤ P.k) {l : ℕ} (hl : l ∈ Finset.Icc 1 (P.k - 1)) (ρ : M.Ty P) (c : ℂ) :
    (C c * xepol P l ρ).coeff (P.k - 1) = 0 := by
  have := xepol_natDegree_le P hl ρ
  exact Polynomial.coeff_eq_zero_of_natDegree_lt
    (lt_of_le_of_lt (Polynomial.natDegree_C_mul_le c _) (by omega))

theorem nab_eq (d : Q.NFData P A) (hR : d.Rel) (hk : 2 ≤ P.k) :
    ∃ (lam : Fin (P.k + 1) → ℂ) (e : M.Ty P → ℂ),
      d.L.nab = ∑ ρ, d.L.GGi * (-(∑ j : Fin (P.k + 1), lam j • (d.κ (dl ρ) * d.QQ ((j : ℕ) : ℂ) 1 0)) -
        e ρ • (d.κ (dl ρ) * d.L.ζb)) := by
  classical
  obtain ⟨lam, hlam⟩ := lag_weights P.k
  refine ⟨lam, fun ρ => ((xpol P ρ) * (X + C (1 / 2 : ℂ))).coeff (P.k - 1), ?_⟩
  have key : ∀ ρ, ∑ j : Fin (P.k + 1), lam j • (d.κ (dl ρ) * d.QQ ((j : ℕ) : ℂ) 1 0) =
      -(d.L.GG * d.κ (dl ρ) * d.L.nab) +
        ((xpol P ρ) * (X + C (1 / 2 : ℂ))).coeff (P.k - 1) • (-(d.κ (dl ρ) * d.L.ζb)) := by
    intro ρ
    simp_rw [e10 d hR ρ, smul_add, Finset.sum_add_distrib, Finset.smul_sum]
    rw [comb hlam _ (xpol_deg P ρ), comb hlam _ (xpol_half_deg P (by omega) ρ _), xpol_coeff, one_smul]
    have h3 : ∑ j : Fin (P.k + 1), ∑ l ∈ Finset.Icc 1 (P.k - 1), ∑ ρ0,
        lam j • ((C (fl P l ρ ρ0) * xepol P l ρ0).eval ((j : ℕ) : ℂ) • (d.SS l * d.κ (dl ρ0))) = 0 := by
      rw [Finset.sum_comm]
      refine Finset.sum_eq_zero fun l hl => ?_
      rw [Finset.sum_comm]
      refine Finset.sum_eq_zero fun ρ0 _ => ?_
      rw [comb hlam _ (xepol_deg P hl ρ0 _), xepol_coeff P hk hl, zero_smul]
    rw [h3, add_zero]
  have hρ : ∀ ρ, d.κ (dl ρ) * d.L.nab = d.L.GGi * (-(∑ j : Fin (P.k + 1), lam j • (d.κ (dl ρ) *
      d.QQ ((j : ℕ) : ℂ) 1 0)) - ((xpol P ρ) * (X + C (1 / 2 : ℂ))).coeff (P.k - 1) • (d.κ (dl ρ) * d.L.ζb)) := by
    intro ρ
    rw [key ρ, smul_neg, neg_add, neg_neg, neg_neg, add_sub_cancel_right, ← mul_assoc, ← mul_assoc,
      d.L.GGi_GG, one_mul]
  calc d.L.nab = (∑ ρ, d.κ (dl ρ)) * d.L.nab := by rw [sum_dl, one_mul]
    _ = _ := by rw [Finset.sum_mul]; exact Finset.sum_congr rfl fun ρ _ => hρ ρ

theorem nabs_eq (d : Q.NFData P A) (hR : d.Rel) (hk : 2 ≤ P.k) :
    ∃ (lam : Fin (P.k + 1) → ℂ) (e : M.Ty P → ℂ),
      d.L.nabs = ∑ ρ, d.L.GGi * (-(∑ j : Fin (P.k + 1), lam j • (d.κ (dl ρ) * d.QQ ((j : ℕ) : ℂ) 0 1)) -
        e ρ • (d.κ (dl ρ) * d.L.ζ)) := by
  classical
  obtain ⟨lam, hlam⟩ := lag_weights P.k
  refine ⟨lam, fun ρ => ((xpol P ρ) * (X - C (1 / 2 : ℂ))).coeff (P.k - 1), ?_⟩
  have key : ∀ ρ, ∑ j : Fin (P.k + 1), lam j • (d.κ (dl ρ) * d.QQ ((j : ℕ) : ℂ) 0 1) =
      -(d.L.GG * d.κ (dl ρ) * d.L.nabs) +
        ((xpol P ρ) * (X - C (1 / 2 : ℂ))).coeff (P.k - 1) • (-(d.κ (dl ρ) * d.L.ζ)) := by
    intro ρ
    simp_rw [e01 d hR ρ, smul_add, Finset.sum_add_distrib, Finset.smul_sum]
    rw [comb hlam _ (xpol_deg P ρ), comb hlam _ (xpol_halfm_deg P (by omega) ρ _), xpol_coeff, one_smul]
    have h3 : ∑ j : Fin (P.k + 1), ∑ l ∈ Finset.Icc 1 (P.k - 1),
        lam j • ((xepol P l ρ).eval ((j : ℕ) : ℂ) • (d.κ (dl ρ) * star (d.SS l))) = 0 := by
      rw [Finset.sum_comm]
      refine Finset.sum_eq_zero fun l hl => ?_
      have hd : (xepol P l ρ).natDegree ≤ P.k := by rw [xepol_natDegree P hl]; omega
      rw [comb hlam _ hd, Polynomial.coeff_eq_zero_of_natDegree_lt (by rw [xepol_natDegree P hl]; omega),
        zero_smul]
    rw [h3, add_zero]
  have hρ : ∀ ρ, d.κ (dl ρ) * d.L.nabs = d.L.GGi * (-(∑ j : Fin (P.k + 1), lam j • (d.κ (dl ρ) *
      d.QQ ((j : ℕ) : ℂ) 0 1)) - ((xpol P ρ) * (X - C (1 / 2 : ℂ))).coeff (P.k - 1) • (d.κ (dl ρ) * d.L.ζ)) := by
    intro ρ
    rw [key ρ, smul_neg, neg_add, neg_neg, neg_neg, add_sub_cancel_right, ← mul_assoc, ← mul_assoc,
      d.L.GGi_GG, one_mul]
  calc d.L.nabs = (∑ ρ, d.κ (dl ρ)) * d.L.nabs := by rw [sum_dl, one_mul]
    _ = _ := by rw [Finset.sum_mul]; exact Finset.sum_congr rfl fun ρ _ => hρ ρ

end ring

section fst

variable {V : Type*} [AddCommGroup V] [Module ℂ V]

theorem fst_mul' (a b : Q.Pr V) : (a * b).1 = a.1 * b.1 := rfl
theorem fst_add' (a b : Q.Pr V) : (a + b).1 = a.1 + b.1 := rfl
theorem fst_neg' (a : Q.Pr V) : (-a).1 = -a.1 := rfl
theorem fst_sub' (a b : Q.Pr V) : (a - b).1 = a.1 - b.1 := rfl
theorem fst_zero' : (0 : Q.Pr V).1 = 0 := rfl
theorem fst_smul' (c : ℂ) (a : Q.Pr V) : (c • a).1 = c • a.1 := by
  first
  | rfl
  | exact Prod.smul_fst _ _
theorem fst_sum' {ι : Type*} (s : Finset ι) (f : ι → Q.Pr V) : (∑ i ∈ s, f i).1 = ∑ i ∈ s, (f i).1 := by
  first
  | exact Prod.fst_sum
  | exact map_sum (AddMonoidHom.fst (Module.End ℂ V) (Module.End ℂ V)ᵐᵒᵖ) f s

end fst

section main

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] [FiniteDimensional ℂ Wp]

theorem radDZ_expr (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq)
    (X : Q.ActualOps P.k P.r Bs.z Bs.z' Bs.π Bs.π') (d : Q.NFData P (Q.Pr (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π')))
    (hH : GTHyp P Bs X d) (hT : ∀ (Y : ℂ) (a b : Fin 2), RadDZ P Bs (X.t Y a b))
    (e : M.Ty P → ℂ → (Wq →L[ℂ] Wp)) (he : IsFrameB P Bs e) (hk : KapF P Bs d e)
    (lam : Fin (P.k + 1) → ℂ) (c : ℂ) (j0 : Fin 6) (hj0 : j0 = 0 ∨ j0 = 2) (a b : Fin 2) (ρ : M.Ty P) :
    RadDZ P Bs (X.fn 5 * (-(∑ j : Fin (P.k + 1), lam j • ((d.κ (dl ρ)).1 * X.t ((j : ℕ) : ℂ) a b)) -
      c • ((d.κ (dl ρ)).1 * X.fn j0))) := by
  have hpl := hH.1
  refine radDZ_fn_left P Bs hpl X 5 (Or.inr (Or.inr rfl)) ?_
  rw [sub_eq_add_neg]
  refine radDZ_add (radDZ_neg (radDZ_sum _ _ fun j _ => radDZ_smul ?_ _)) (radDZ_neg (radDZ_smul ?_ _))
  · exact radDZ_kap_left P Bs X d hH e he hk ρ (hT _ a b)
  · refine radDZ_kap_left P Bs X d hH e he hk ρ ?_
    have := radDZ_fn_left P Bs hpl X j0 (hj0.elim Or.inl fun h => Or.inr (Or.inl h)) (radDZ_one P Bs)
    rwa [mul_one] at this

theorem local_nabla_holds : GTCLNab := by
  intro Wp Wq _ _ _ _ _ _ P Bs X d hH hT e he hk
  have hpl := hH.1
  have hk2 := hH.2.1
  have hL := hH.2.2.2.1
  have hR := hH.2.2.2.2.2.1
  have hQ := hH.2.2.2.2.2.2
  have hQt : ∀ (Y : ℂ) (a b : Fin 2), (d.QQ Y a b).1 = X.t Y a b := by
    intro Y a b
    rw [← hQ Y]
    rfl
  have hGGi : d.L.GGi.1 = X.fn 5 := by rw [hL.2.2.2.2.2.2.2.2.2.2.2.1]; rfl
  have hζb : d.L.ζb.1 = X.fn 2 := by rw [hL.2.2.2.2.2.2.2.2.1]; rfl
  have hζ : d.L.ζ.1 = X.fn 0 := by rw [hL.2.2.2.2.2.2.1]; rfl
  obtain ⟨lam, c, hn⟩ := nab_eq d hR hk2
  obtain ⟨lam', c', hns⟩ := nabs_eq d hR hk2
  constructor
  · rw [hn, fst_sum']
    refine radDZ_sum _ _ fun ρ _ => ?_
    rw [fst_mul', fst_sub', fst_neg', fst_sum', fst_smul', fst_mul', hGGi, hζb]
    have hs : ∀ j : Fin (P.k + 1), (lam j • (d.κ (dl ρ) * d.QQ ((j : ℕ) : ℂ) 1 0)).1 =
        lam j • ((d.κ (dl ρ)).1 * X.t ((j : ℕ) : ℂ) 1 0) := by
      intro j; rw [fst_smul', fst_mul', hQt]
    simp_rw [hs]
    exact radDZ_expr P Bs X d hH hT e he hk lam (c ρ) 2 (Or.inr rfl) 1 0 ρ
  · rw [hns, fst_sum']
    refine radDZ_sum _ _ fun ρ _ => ?_
    rw [fst_mul', fst_sub', fst_neg', fst_sum', fst_smul', fst_mul', hGGi, hζ]
    have hs : ∀ j : Fin (P.k + 1), (lam' j • (d.κ (dl ρ) * d.QQ ((j : ℕ) : ℂ) 0 1)).1 =
        lam' j • ((d.κ (dl ρ)).1 * X.t ((j : ℕ) : ℂ) 0 1) := by
      intro j; rw [fst_smul', fst_mul', hQt]
    simp_rw [hs]
    exact radDZ_expr P Bs X d hH hT e he hk lam' (c' ρ) 0 (Or.inl rfl) 0 1 ρ

end main

end

end Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.LNab

namespace Formalism.FourierDecayAlt.P.CutMP.Gauge.GC

theorem local_nabla_holds : GTCLNab := LNab.local_nabla_holds

end Formalism.FourierDecayAlt.P.CutMP.Gauge.GC
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.MeasurableEnormComposition
section
noncomputable section

open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal NNReal

namespace Formalism.FourierDecayAlt.P.S3dx4

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData

variable {k r : ℕ}

def abelian₂ (e0 : Mx k r → ℂ) (γ : Mx k r) (μp μq : Measure (Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r))
    (x y : Formalism.QuantumDeterminants.Mt k r) : ℝ≥0∞ :=
  ∫⁻ p, ∫⁻ q, ‖e0 ((Matrix.of x)⁻¹ * (Matrix.of p.1 * Matrix.of p.2) * γ * (Matrix.of q.1 * Matrix.of q.2)⁻¹ *
    Matrix.of y)‖ₑ ∂μq ∂μp

def Lam1 (e0 : Mx k r → ℂ) (μp : Measure (Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r)) (x y : Formalism.QuantumDeterminants.Mt k r) :
    ℝ≥0∞ :=
  ∫⁻ p, ‖e0 ((Matrix.of x)⁻¹ * (Matrix.of p.1 * Matrix.of p.2) * Matrix.of y)‖ₑ ∂μp

theorem meas_inv {α : Type*} [MeasurableSpace α] {f : α → Formalism.QuantumDeterminants.Mt k r} (hf : Measurable f) :
    Measurable (fun t => (fun i j => ((Matrix.of (f t))⁻¹ : Mx k r) i j : Formalism.QuantumDeterminants.Mt k r)) :=
  (B2x1.invM_meas (k := k) (r := r)).comp hf

theorem measurable_enorm_composition {e0 : Mx k r → ℂ} (he0 : Continuous e0) {α : Type*} [MeasurableSpace α]
    {f : α → Formalism.QuantumDeterminants.Mt k r} (hf : Measurable f) : Measurable (fun t => ‖e0 (Matrix.of (f t))‖ₑ) :=
  ((he0.comp mt_cont).measurable.comp hf).enorm

theorem meas_hn {α : Type*} [MeasurableSpace α] {f : α → Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r}
    (hf : Measurable f) :
    Measurable (fun t => (fun i j => (Matrix.of (f t).1 * Matrix.of (f t).2) i j : Formalism.QuantumDeterminants.Mt k r)) :=
  meas_matmul hf.fst hf.snd

theorem meas_lam_int {e0 : Mx k r → ℂ} (he0 : Continuous e0) (γ : Mx k r) {α : Type*} [MeasurableSpace α]
    {X Y : α → Formalism.QuantumDeterminants.Mt k r} {P Q : α → Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r}
    (hX : Measurable X) (hY : Measurable Y) (hP : Measurable P) (hQ : Measurable Q) :
    Measurable (fun t => ‖e0 ((Matrix.of (X t))⁻¹ * (Matrix.of (P t).1 * Matrix.of (P t).2) * γ *
      (Matrix.of (Q t).1 * Matrix.of (Q t).2)⁻¹ * Matrix.of (Y t))‖ₑ) := by
  have mγ : Measurable (fun _ : α => (Matrix.of.symm γ : Formalism.QuantumDeterminants.Mt k r)) := measurable_const
  have M := meas_matmul (meas_matmul (meas_matmul (meas_matmul (meas_inv hX) (meas_hn hP)) mγ)
    (meas_inv (meas_hn hQ))) hY
  exact measurable_enorm_composition he0 M

theorem measurable_lambda_integrand {e0 : Mx k r → ℂ} (he0 : Continuous e0) {α : Type*} [MeasurableSpace α]
    {X Y : α → Formalism.QuantumDeterminants.Mt k r} {P : α → Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r}
    (hX : Measurable X) (hY : Measurable Y) (hP : Measurable P) :
    Measurable (fun t => ‖e0 ((Matrix.of (X t))⁻¹ * (Matrix.of (P t).1 * Matrix.of (P t).2) *
      Matrix.of (Y t))‖ₑ) := by
  have M := meas_matmul (meas_matmul (meas_inv hX) (meas_hn hP)) hY
  exact measurable_enorm_composition he0 M

theorem meas_lam {e0 : Mx k r → ℂ} (he0 : Continuous e0) (γ : Mx k r)
    (μp μq : Measure (Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r)) [SFinite μp] [SFinite μq] :
    Measurable (fun t : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r => abelian₂ e0 γ μp μq t.1 t.2) := by
  unfold abelian₂
  have m4 := meas_lam_int he0 γ (α := ((Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r) × (Formalism.QuantumDeterminants.Mt k r ×
      Formalism.QuantumDeterminants.Mt k r)) × (Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r))
    (measurable_fst.fst.fst) (measurable_fst.fst.snd) measurable_fst.snd measurable_snd
  have m3 := m4.lintegral_prod_right' (ν := μq)
  exact m3.lintegral_prod_right' (ν := μp)

theorem measurable_lambda_integral {e0 : Mx k r → ℂ} (he0 : Continuous e0)
    (μp : Measure (Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r)) [SFinite μp] :
    Measurable (fun t : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r => Lam1 e0 μp t.1 t.2) := by
  unfold Lam1
  have m3 := measurable_lambda_integrand he0 (α := (Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r) × (Formalism.QuantumDeterminants.Mt k r ×
      Formalism.QuantumDeterminants.Mt k r)) (measurable_fst.fst) (measurable_fst.snd) measurable_snd
  exact m3.lintegral_prod_right' (ν := μp)

theorem meas_const_mt (c : Formalism.QuantumDeterminants.Mt k r) {α : Type*} [MeasurableSpace α] :
    Measurable (fun _ : α => c) := measurable_const

theorem lam_left {e0 : Mx k r → ℂ} (he0 : Continuous e0) (γ : Mx k r) {z : Fin (2 * r + k + 1) → ℂ}
    {μW μN : Measure (Formalism.QuantumDeterminants.Mt k r)} (hW : PI.BesselPeriodGGP.IsHaarOn (Formalism.QuantumDeterminants.UWset k r z) μW)
    (hN : PI.BesselPeriodGGP.IsHaarOn (Formalism.QuantumDeterminants.Nset k r) μN) [SigmaFinite μW] [SigmaFinite μN]
    (hz : Formalism.QuantumDeterminants.inWb k r z) (μq : Measure (Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r)) [SFinite μq]
    {h0 n0 : Mx k r} (hh0 : h0 ∈ Formalism.QuantumDeterminants.UWset k r z) (hn0 : n0 ∈ Formalism.QuantumDeterminants.Nset k r) (x y : Formalism.QuantumDeterminants.Mt k r) :
    abelian₂ e0 γ (μW.prod μN) μq (fun i j => (h0 * n0 * Matrix.of x) i j) y = abelian₂ e0 γ (μW.prod μN) μq x y := by
  have hS : h0 * n0 ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r) := DDSmoothness.uh_mul hh0.1 hn0.1
  obtain ⟨-, -, hSS⟩ := MatrixMultiplicationContinuity.uh_inv hS
  set x' : Formalism.QuantumDeterminants.Mt k r := fun i j => (h0 * n0 * Matrix.of x) i j with hx'
  set F : Formalism.QuantumDeterminants.Mt k r → ℝ≥0∞ := fun m => ∫⁻ q, ‖e0 ((Matrix.of x')⁻¹ * Matrix.of m * γ *
    (Matrix.of q.1 * Matrix.of q.2)⁻¹ * Matrix.of y)‖ₑ ∂μq with hF
  have hFm : Measurable F := by
    have mγ : Measurable (fun _ : Formalism.QuantumDeterminants.Mt k r × (Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r) =>
        (Matrix.of.symm γ : Formalism.QuantumDeterminants.Mt k r)) := measurable_const
    have M := meas_matmul (meas_matmul (meas_matmul (meas_matmul (meas_inv (meas_const_mt x'))
      measurable_fst) mγ) (meas_inv (meas_hn measurable_snd))) (meas_const_mt y)
    exact (measurable_enorm_composition he0 M).lintegral_prod_right'
  have hpl := param_left hW hN hz hh0 hn0 hFm
  unfold abelian₂
  calc ∫⁻ p, ∫⁻ q, ‖e0 ((Matrix.of x')⁻¹ * (Matrix.of p.1 * Matrix.of p.2) * γ *
        (Matrix.of q.1 * Matrix.of q.2)⁻¹ * Matrix.of y)‖ₑ ∂μq ∂(μW.prod μN)
      = ∫⁻ p, F (fun i j => (Matrix.of p.1 * Matrix.of p.2) i j) ∂(μW.prod μN) := rfl
    _ = ∫⁻ p, F (fun i j => (h0 * n0 * (Matrix.of p.1 * Matrix.of p.2)) i j) ∂(μW.prod μN) := hpl.symm
    _ = _ := by
        have hmat : ∀ P : Mx k r, (Matrix.of x')⁻¹ * Matrix.of (fun i j => (h0 * n0 * P) i j : Formalism.QuantumDeterminants.Mt k r) =
            (Matrix.of x)⁻¹ * P := by
          intro P
          show (h0 * n0 * Matrix.of x)⁻¹ * (h0 * n0 * P) = (Matrix.of x)⁻¹ * P
          rw [Matrix.mul_inv_rev, Matrix.mul_assoc, ← Matrix.mul_assoc (h0 * n0)⁻¹, hSS, Matrix.one_mul]
        simp only [hF, hmat]

theorem lam_right {e0 : Mx k r → ℂ} (he0 : Continuous e0) (γ : Mx k r) {z : Fin (2 * r + k + 1) → ℂ}
    {μW μN : Measure (Formalism.QuantumDeterminants.Mt k r)} (hW : PI.BesselPeriodGGP.IsHaarOn (Formalism.QuantumDeterminants.UWset k r z) μW)
    (hN : PI.BesselPeriodGGP.IsHaarOn (Formalism.QuantumDeterminants.Nset k r) μN) [SigmaFinite μW] [SigmaFinite μN]
    (hz : Formalism.QuantumDeterminants.inWb k r z) (μp : Measure (Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r))
    {h0 n0 : Mx k r} (hh0 : h0 ∈ Formalism.QuantumDeterminants.UWset k r z) (hn0 : n0 ∈ Formalism.QuantumDeterminants.Nset k r) (x y : Formalism.QuantumDeterminants.Mt k r) :
    abelian₂ e0 γ μp (μW.prod μN) x (fun i j => (h0 * n0 * Matrix.of y) i j) = abelian₂ e0 γ μp (μW.prod μN) x y := by
  have hS : h0 * n0 ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r) := DDSmoothness.uh_mul hh0.1 hn0.1
  obtain ⟨-, hSS, -⟩ := MatrixMultiplicationContinuity.uh_inv hS
  unfold abelian₂
  apply lintegral_congr
  intro p
  set y' : Formalism.QuantumDeterminants.Mt k r := fun i j => (h0 * n0 * Matrix.of y) i j with hy'
  set F : Formalism.QuantumDeterminants.Mt k r → ℝ≥0∞ := fun m => ‖e0 ((Matrix.of x)⁻¹ * (Matrix.of p.1 * Matrix.of p.2) * γ *
    (Matrix.of m)⁻¹ * Matrix.of y')‖ₑ with hF
  have hFm : Measurable F := by
    have mc : Measurable (fun _ : Formalism.QuantumDeterminants.Mt k r =>
        (fun i j => ((Matrix.of x)⁻¹ * (Matrix.of p.1 * Matrix.of p.2) * γ) i j : Formalism.QuantumDeterminants.Mt k r)) :=
      measurable_const
    have M := meas_matmul (meas_matmul mc (meas_inv measurable_id)) (meas_const_mt y')
    exact measurable_enorm_composition he0 M
  have hpl := param_left hW hN hz hh0 hn0 hFm
  calc ∫⁻ q, ‖e0 ((Matrix.of x)⁻¹ * (Matrix.of p.1 * Matrix.of p.2) * γ *
        (Matrix.of q.1 * Matrix.of q.2)⁻¹ * Matrix.of y')‖ₑ ∂(μW.prod μN)
      = ∫⁻ q, F (fun i j => (Matrix.of q.1 * Matrix.of q.2) i j) ∂(μW.prod μN) := rfl
    _ = ∫⁻ q, F (fun i j => (h0 * n0 * (Matrix.of q.1 * Matrix.of q.2)) i j) ∂(μW.prod μN) := hpl.symm
    _ = _ := by
        have hSS' := (MatrixMultiplicationContinuity.uh_inv hS).2.2
        have hmat : ∀ (Z Q : Mx k r), Z * (Matrix.of (fun i j => (h0 * n0 * Q) i j : Formalism.QuantumDeterminants.Mt k r))⁻¹ *
            Matrix.of y' = Z * Q⁻¹ * Matrix.of y := by
          intro Z Q
          show Z * (h0 * n0 * Q)⁻¹ * (h0 * n0 * Matrix.of y) = Z * Q⁻¹ * Matrix.of y
          rw [Matrix.mul_inv_rev, Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc (h0 * n0)⁻¹, hSS',
            Matrix.one_mul, ← Matrix.mul_assoc]
        simp only [hF, hmat]

theorem lambda_left_translation {e0 : Mx k r → ℂ} (he0 : Continuous e0) {z : Fin (2 * r + k + 1) → ℂ}
    {μW μN : Measure (Formalism.QuantumDeterminants.Mt k r)} (hW : PI.BesselPeriodGGP.IsHaarOn (Formalism.QuantumDeterminants.UWset k r z) μW)
    (hN : PI.BesselPeriodGGP.IsHaarOn (Formalism.QuantumDeterminants.Nset k r) μN) [SigmaFinite μW] [SigmaFinite μN]
    (hz : Formalism.QuantumDeterminants.inWb k r z)
    {h0 n0 : Mx k r} (hh0 : h0 ∈ Formalism.QuantumDeterminants.UWset k r z) (hn0 : n0 ∈ Formalism.QuantumDeterminants.Nset k r) (x y : Formalism.QuantumDeterminants.Mt k r) :
    Lam1 e0 (μW.prod μN) (fun i j => (h0 * n0 * Matrix.of x) i j) y = Lam1 e0 (μW.prod μN) x y := by
  have hS : h0 * n0 ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r) := DDSmoothness.uh_mul hh0.1 hn0.1
  obtain ⟨-, -, hSS⟩ := MatrixMultiplicationContinuity.uh_inv hS
  set x' : Formalism.QuantumDeterminants.Mt k r := fun i j => (h0 * n0 * Matrix.of x) i j with hx'
  set F : Formalism.QuantumDeterminants.Mt k r → ℝ≥0∞ := fun m => ‖e0 ((Matrix.of x')⁻¹ * Matrix.of m * Matrix.of y)‖ₑ with hF
  have hFm : Measurable F :=
    measurable_enorm_composition he0 (meas_matmul (meas_matmul (meas_inv (meas_const_mt x')) measurable_id) (meas_const_mt y))
  have hpl := param_left hW hN hz hh0 hn0 hFm
  unfold Lam1
  calc ∫⁻ p, ‖e0 ((Matrix.of x')⁻¹ * (Matrix.of p.1 * Matrix.of p.2) * Matrix.of y)‖ₑ ∂(μW.prod μN)
      = ∫⁻ p, F (fun i j => (Matrix.of p.1 * Matrix.of p.2) i j) ∂(μW.prod μN) := rfl
    _ = ∫⁻ p, F (fun i j => (h0 * n0 * (Matrix.of p.1 * Matrix.of p.2)) i j) ∂(μW.prod μN) := hpl.symm
    _ = _ := by
        have hmat : ∀ P : Mx k r, (Matrix.of x')⁻¹ * Matrix.of (fun i j => (h0 * n0 * P) i j : Formalism.QuantumDeterminants.Mt k r) =
            (Matrix.of x)⁻¹ * P := by
          intro P
          show (h0 * n0 * Matrix.of x)⁻¹ * (h0 * n0 * P) = (Matrix.of x)⁻¹ * P
          rw [Matrix.mul_inv_rev, Matrix.mul_assoc, ← Matrix.mul_assoc (h0 * n0)⁻¹, hSS, Matrix.one_mul]
        simp only [hF, hmat]

theorem lambda_right_translation {e0 : Mx k r → ℂ} (he0 : Continuous e0) {z : Fin (2 * r + k + 1) → ℂ}
    {μW μN : Measure (Formalism.QuantumDeterminants.Mt k r)} (hW : B.IsHaarOn (Formalism.QuantumDeterminants.UWset k r z) μW)
    (hN : B.IsHaarOn (Formalism.QuantumDeterminants.Nset k r) μN) [SigmaFinite μW] [SigmaFinite μN]
    (hz : Formalism.QuantumDeterminants.inWb k r z) (hT : 0 < Formalism.QuantumDeterminants.Tz k r z)
    {h0 n0 : Mx k r} (hh0 : h0 ∈ Formalism.QuantumDeterminants.UWset k r z) (hn0 : n0 ∈ Formalism.QuantumDeterminants.Nset k r) (x y : Formalism.QuantumDeterminants.Mt k r) :
    Lam1 e0 (μW.prod μN) x (fun i j => (h0 * n0 * Matrix.of y) i j) = Lam1 e0 (μW.prod μN) x y := by
  set F : Formalism.QuantumDeterminants.Mt k r → ℝ≥0∞ := fun m => ‖e0 ((Matrix.of x)⁻¹ * Matrix.of m * Matrix.of y)‖ₑ with hF
  have hFm : Measurable F :=
    measurable_enorm_composition he0 (meas_matmul (meas_matmul (meas_inv (meas_const_mt x)) measurable_id) (meas_const_mt y))
  have hpr := param_right hW hN hz hT hh0 hn0 hFm
  unfold Lam1
  calc ∫⁻ p, ‖e0 ((Matrix.of x)⁻¹ * (Matrix.of p.1 * Matrix.of p.2) *
        Matrix.of (fun i j => (h0 * n0 * Matrix.of y) i j : Formalism.QuantumDeterminants.Mt k r))‖ₑ ∂(μW.prod μN)
      = ∫⁻ p, F (fun i j => (Matrix.of p.1 * Matrix.of p.2 * (h0 * n0)) i j) ∂(μW.prod μN) := by
        have hmat : ∀ P : Mx k r, (Matrix.of x)⁻¹ * P *
            Matrix.of (fun i j => (h0 * n0 * Matrix.of y) i j : Formalism.QuantumDeterminants.Mt k r) =
            (Matrix.of x)⁻¹ * Matrix.of (fun i j => (P * (h0 * n0)) i j : Formalism.QuantumDeterminants.Mt k r) * Matrix.of y := by
          intro P
          show (Matrix.of x)⁻¹ * P * (h0 * n0 * Matrix.of y) = (Matrix.of x)⁻¹ * (P * (h0 * n0)) * Matrix.of y
          simp only [Matrix.mul_assoc]
        simp only [hF, hmat]
    _ = ∫⁻ p, F (fun i j => (Matrix.of p.1 * Matrix.of p.2) i j) ∂(μW.prod μN) := hpr
    _ = _ := rfl

end Formalism.FourierDecayAlt.P.S3dx4
end
end

