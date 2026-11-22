import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGaugeVLem
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0138
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0131
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0132
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0073
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0137

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGaugeGVTr
section
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP.Gauge.VLem

open Formalism.FourierDecayAlt.P.CutMP.Gauge

noncomputable section

def Vp (P : M.Par) (Y : ℂ) (i : ℕ) : Wd.M2 (MA.A P (MA.DQ P)) :=
  (((List.finRange P.r).take i).reverse.map fun l => Wd.Ts (MA.siteA P (MA.DQ P) l) Y).prod

theorem Vp_zero (P : M.Par) (Y : ℂ) : Vp P Y 0 = 1 := by
  simp [Vp]

theorem Vp_succ (P : M.Par) (Y : ℂ) (i : ℕ) (h : i < P.r) :
    Vp P Y (i + 1) = Wd.Ts (MA.siteA P (MA.DQ P) ⟨i, h⟩) Y * Vp P Y i := by
  simp [Vp, List.take_add_one, h]

theorem sitesCommonSpace_v0_eq_Vp (P : M.Par) (Y : ℂ) : Wd.v0 (MA.sites P (MA.DQ P)) Y = fun b => Vp P Y P.r b 0 := by
  funext b
  simp [Wd.v0, MA.sites, Vp, List.ofFn_eq_map, List.map_reverse, List.take_of_length_le, Function.comp_def]

theorem Ts_mul_0 (P : M.Par) (σ : Wd.Site (MA.A P (MA.DQ P))) (Y : ℂ) (V : Wd.M2 (MA.A P (MA.DQ P))) :
    (Wd.Ts σ Y * V) 0 0 = (algebraMap ℂ (MA.A P (MA.DQ P)) Y + σ.p) * V 0 0 + -σ.c * V 1 0 := by
  simp [Wd.Ts, Formalism.YangianSpanCharacter.T.Tm, Matrix.mul_apply, Fin.sum_univ_two]

theorem Ts_mul_1 (P : M.Par) (σ : Wd.Site (MA.A P (MA.DQ P))) (Y : ℂ) (V : Wd.M2 (MA.A P (MA.DQ P))) :
    (Wd.Ts σ Y * V) 1 0 = σ.ci * V 0 0 := by
  simp [Wd.Ts, Formalism.YangianSpanCharacter.T.Tm, Matrix.mul_apply, Fin.sum_univ_two]

section ind

theorem actA_p (P : M.Par) (l : Fin P.r) (f : M.Ty P → MA.SmQ P.r P.TT) :
    MA.actA P (MA.siteA P (MA.DQ P) l).p f = fun ρ => MA.eulerQ (TT := P.TT) (M.vc l) (f ρ) :=
  actA_sc P _ f

theorem actA_c (P : M.Par) (l : Fin P.r) (f : M.Ty P → MA.SmQ P.r P.TT) :
    MA.actA P (MA.siteA P (MA.DQ P) l).c f = fun ρ => MA.coordQ (TT := P.TT) (M.vc l) * f ρ :=
  actA_sc P _ f

theorem actA_ci (P : M.Par) (l : Fin P.r) (f : M.Ty P → MA.SmQ P.r P.TT) :
    MA.actA P (MA.siteA P (MA.DQ P) l).ci f = fun ρ => Ring.inverse (MA.coordQ (TT := P.TT) (M.vc l)) * f ρ :=
  actA_sc P _ f

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]
  {P : M.Par} {Bs : B.RealPlaceData P.k P.r Wp Wq} {e : M.Ty P → ℂ → (Wq →L[ℂ] Wp)}

theorem vab_ind (hpl : Q.IsPlace P Bs.z Bs.z' Bs.π Bs.π') (hk : 2 ≤ P.k) (he : IsFrameB P Bs e) (Y : ℝ) :
    ∀ i : ℕ, i ≤ P.r → ∀ (Dc : (Fin P.r → ℂ) → Set (Q.Mx P.k P.r)) (Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)),
      FamR P Bs Dc Φ →
      (FamR P Bs Dc (Q.crd (Q.cmp (Q.vAB P.r (Y : ℂ) i) 0) Φ) ∧
        trR P Bs.μsec e (Q.crd (Q.cmp (Q.vAB P.r (Y : ℂ) i) 0) Φ) =
          MA.actA P (Vp P Y i 0 0) (trR P Bs.μsec e Φ)) ∧
      (FamR P Bs Dc (Q.crd (Q.cmp (Q.vAB P.r (Y : ℂ) i) 1) Φ) ∧
        trR P Bs.μsec e (Q.crd (Q.cmp (Q.vAB P.r (Y : ℂ) i) 1) Φ) =
          MA.actA P (Vp P Y i 1 0) (trR P Bs.μsec e Φ)) := by
  intro i
  induction i with
  | zero =>
    intro _ Dc Φ hΦ
    have h0 : Q.crd (Q.cmp (Q.vAB P.r (Y : ℂ) 0) 0) Φ = Φ := rfl
    have h1 : Q.crd (Q.cmp (Q.vAB P.r (Y : ℂ) 0) 1) Φ = 0 := rfl
    have v0 : Vp P Y 0 0 0 = 1 := by simp [Vp_zero]
    have v1 : Vp P Y 0 1 0 = 0 := by simp [Vp_zero]
    rw [h0, h1, v0, v1, actA_one, actA_zero, trR_zero]
    refine ⟨⟨hΦ, rfl⟩, ⟨?_, rfl⟩⟩
    have := famR_smul hΦ 0
    rwa [zero_smul] at this
  | succ i ih =>
    intro hi Dc Φ hΦ
    have h : i < P.r := hi
    obtain ⟨⟨hA, tA⟩, ⟨hB, tB⟩⟩ := ih (Nat.le_of_lt h) Dc Φ hΦ
    set ΦA := Q.crd (Q.cmp (Q.vAB P.r (Y : ℂ) i) 0) Φ with hΦA
    set ΦB := Q.crd (Q.cmp (Q.vAB P.r (Y : ℂ) i) 1) Φ with hΦB
    have hv : Q.vAB (E := Wq →L[ℂ] Wp) P.r (Y : ℂ) (i + 1) =
        (fun f => (Y : ℂ) • (Q.vAB P.r (Y : ℂ) i).1 f + pOp ⟨i, h⟩ ((Q.vAB P.r (Y : ℂ) i).1 f) -
          cOp ⟨i, h⟩ ((Q.vAB P.r (Y : ℂ) i).2 f), fun f => ciOp ⟨i, h⟩ ((Q.vAB P.r (Y : ℂ) i).1 f)) := by
      simp only [Q.vAB, dif_pos h]
    have e0 : Q.crd (Q.cmp (Q.vAB P.r (Y : ℂ) (i + 1)) 0) Φ =
        (Y : ℂ) • ΦA + Q.crd (pOp ⟨i, h⟩) ΦA - Q.crd (cOp ⟨i, h⟩) ΦB := by
      rw [hv]; rfl
    have e1 : Q.crd (Q.cmp (Q.vAB P.r (Y : ℂ) (i + 1)) 1) Φ = Q.crd (ciOp ⟨i, h⟩) ΦA := by
      rw [hv]; rfl
    have hpA : FamR P Bs Dc (Q.crd (pOp ⟨i, h⟩) ΦA) := famR_opL hA ⟨i, h⟩ 0
    have hcB : FamR P Bs Dc (Q.crd (cOp ⟨i, h⟩) ΦB) := famR_opL hB ⟨i, h⟩ 1
    have hciA : FamR P Bs Dc (Q.crd (ciOp ⟨i, h⟩) ΦA) := famR_opL hA ⟨i, h⟩ 2
    have hsum : FamR P Bs Dc ((Y : ℂ) • ΦA + Q.crd (pOp ⟨i, h⟩) ΦA) := famR_add (famR_smul hA _) hpA
    have tc : trR P Bs.μsec e (Q.crd (cOp ⟨i, h⟩) ΦB) =
        fun ρ => MA.coordQ (TT := P.TT) (M.vc ⟨i, h⟩) * trR P Bs.μsec e ΦB ρ :=
      trR_mul hpl hk he hB _ hcB (fun c => c ⟨i, h⟩) (fun _ _ => rfl) _ (fun q => coordE_vc _ _)
    have tci : trR P Bs.μsec e (Q.crd (ciOp ⟨i, h⟩) ΦA) =
        fun ρ => Ring.inverse (MA.coordQ (TT := P.TT) (M.vc ⟨i, h⟩)) * trR P Bs.μsec e ΦA ρ :=
      trR_mul hpl hk he hA _ hciA (fun c => (c ⟨i, h⟩)⁻¹) (fun _ _ => rfl) _ (fun q => by
        rw [inv_coordQ_apply _ (fun x hx => by rw [coordE_vc]; exact hx.1 _), coordE_vc])
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
    · rw [e0]; exact famR_sub hsum hcB
    · rw [e0, trR_sub _ _ _ _ (fun ρ => smR hpl hk he hsum ρ) (fun ρ => smR hpl hk he hcB ρ),
        trR_add _ _ _ _ (fun ρ => smR hpl hk he (famR_smul hA _) ρ) (fun ρ => smR hpl hk he hpA ρ), trR_smul,
        trR_p hpl hk he hA, tc, tA, tB, Vp_succ P Y i h, Ts_mul_0, actA_add, actA_mul, actA_mul,
        actA_neg, actA_add, actA_algebraMap, actA_p, actA_c, sub_eq_add_neg]
    · rw [e1]; exact hciA
    · rw [e1, tci, tA, Vp_succ P Y i h, Ts_mul_1, actA_mul, actA_ci]

end ind

end

end Formalism.FourierDecayAlt.P.CutMP.Gauge.VLem

namespace Formalism.FourierDecayAlt.P.CutMP.Gauge

open VLem

theorem gauge_vector_transition_holds : GVTr := by
  intro Wp Wq _ _ _ _ _ _ P Bs hpl hk e he Dc Φ hΦ Y b
  have h := vab_ind hpl hk he Y P.r le_rfl Dc Φ hΦ
  rw [sitesCommonSpace_v0_eq_Vp]
  fin_cases b
  · exact ⟨h.1.1, fun ρ => congrFun h.1.2 ρ⟩
  · exact ⟨h.2.1, fun ρ => congrFun h.2.2 ρ⟩

end Formalism.FourierDecayAlt.P.CutMP.Gauge
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJAPRCPDecompDec
section
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q NumberField
open scoped ComplexConjugate Matrix

namespace Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep.Core.TC.PR.CP.Dc

open Formalism.FourierDecayAlt.P.B2x3 Formalism.FourierDecayAlt.P.SettingConstruction Formalism.FourierDecayAlt.P.TheSec Formalism.FourierDecayAlt.B2

noncomputable section

variable {k : ℕ}

section ann

variable {T T' : ℝ}

lemma kap_ne (hT : 0 < T) (hT' : 0 < T') : kap T T' ≠ 0 := by
  unfold kap
  exact_mod_cast (mul_pos (Real.sqrt_pos.2 hT) (Real.sqrt_pos.2 hT')).ne'

lemma kap_sq (hT : 0 < T) (hT' : 0 < T') : kap T T' * kap T T' = ((T * T' : ℝ) : ℂ) := by
  unfold kap
  rw [← Complex.ofReal_mul, mul_mul_mul_comm, Real.mul_self_sqrt hT.le, Real.mul_self_sqrt hT'.le]

lemma wZ_eq (ζ : ℂ) : wZ T T' ζ = -(kap T T')⁻¹ * ζ := rfl

lemma wZ_star (ζ : ℂ) : star (wZ T T' ζ) = -(kap T T')⁻¹ * conj ζ := by
  rw [wZ_eq, star_mul', star_neg, star_inv₀, kap_star]
  rfl

lemma zeta_ne (hT : 0 < T) (hT' : 0 < T') {ζ : ℂ} (hζ : T * T' < Complex.normSq ζ) : ζ ≠ 0 := by
  intro h
  rw [h, map_zero] at hζ
  exact absurd hζ (not_lt.2 (mul_pos hT hT').le)

lemma ws_rel (hT : 0 < T) (hT' : 0 < T') {ζ : ℂ} (hζ : T * T' < Complex.normSq ζ) :
    wZ T T' ζ * star (wZ T T' ζ) - sZ T T' ζ * sZ T T' ζ = 1 := by
  have hk := kap_ne hT hT'
  have h1 := sig_sq hζ
  have h2 := kap_sq hT hT'
  have h3 : gg (T * T') ζ = ζ * conj ζ - ((T * T' : ℝ) : ℂ) := by
    rw [Complex.mul_conj]; unfold gg; push_cast; ring
  rw [wZ_star, wZ_eq, sZ_eq T T' hT hT' ζ hζ]
  have h4 : ζ * conj ζ - sig (T * T') ζ * sig (T * T') ζ = kap T T' * kap T T' := by rw [h1, h3, h2]; ring
  field_simp
  linear_combination h4

lemma nuI_eq (ζ : ℂ) : nuI k T T' ζ = nuG k (wZ T T' ζ) (-sZ T T' ζ) (star (wZ T T' ζ)) := by
  unfold nuI
  rw [nu_eq, star_star]

lemma nuI_mul (h0 : (0 : Fin (k + 1)) ≠ Fin.last k) (hT : 0 < T) (hT' : 0 < T') {ζ : ℂ}
    (hζ : T * T' < Complex.normSq ζ) : nuI k T T' ζ * nu k (wZ T T' ζ) (sZ T T' ζ) = 1 := by
  rw [nuI_eq, nu_eq]
  have h := nuG_mul h0 (wZ T T' ζ) (-sZ T T' ζ) (star (wZ T T' ζ)) (by linear_combination ws_rel hT hT' hζ)
  rwa [neg_neg] at h

end ann

def PSL (k : ℕ) (TT : ℝ) (C : ℂ → Mb k) : Prop := (∀ i j, PS TT (fun ζ => C ζ i j)) ∧ ∀ ζ, InL k (C ζ)

lemma psl_smul {TT : ℝ} {f : ℂ → ℂ} (hf : PS TT f) {A : Mb k} (hA : InL k A) : PSL k TT (fun ζ => f ζ • A) := by
  refine ⟨fun i j => ?_, fun ζ i => ⟨?_, ?_⟩⟩
  · exact ps_mul hf (ps_const (A i j))
  · show f ζ * A i (Fin.last k) = 0
    rw [(hA i).1, mul_zero]
  · show f ζ * A (Fin.last k) i = 0
    rw [(hA i).2, mul_zero]

lemma psl_add {TT : ℝ} {C D : ℂ → Mb k} (hC : PSL k TT C) (hD : PSL k TT D) : PSL k TT (fun ζ => C ζ + D ζ) := by
  refine ⟨fun i j => ps_add (hC.1 i j) (hD.1 i j), fun ζ i => ⟨?_, ?_⟩⟩
  · show C ζ i (Fin.last k) + D ζ i (Fin.last k) = 0
    rw [(hC.2 ζ i).1, (hD.2 ζ i).1, add_zero]
  · show C ζ (Fin.last k) i + D ζ (Fin.last k) i = 0
    rw [(hC.2 ζ i).2, (hD.2 ζ i).2, add_zero]

lemma psl_csmul {TT : ℝ} (c : ℂ) {C : ℂ → Mb k} (hC : PSL k TT C) : PSL k TT (fun ζ => c • C ζ) := by
  refine ⟨fun i j => ps_mul (ps_const c) (hC.1 i j), fun ζ i => ⟨?_, ?_⟩⟩
  · show c * C ζ i (Fin.last k) = 0
    rw [(hC.2 ζ i).1, mul_zero]
  · show c * C ζ (Fin.last k) i = 0
    rw [(hC.2 ζ i).2, mul_zero]

def Dec (k : ℕ) (T T' : ℝ) (M : Mb k) : Prop :=
  ∃ (C₁ C₂ : ℂ → Mb k) (β₁ β₂ : ℂ → ℂ), PSL k (T * T') C₁ ∧ PSL k (T * T') C₂ ∧ PS (T * T') β₁ ∧ PS (T * T') β₂ ∧
    ∀ ζ : ℂ, T * T' < Complex.normSq ζ →
      M = C₁ ζ + nuI k T T' ζ * C₂ ζ * nu k (wZ T T' ζ) (sZ T T' ζ) + β₁ ζ • H1 k T T' ζ + β₂ ζ • H2 k T T' ζ

variable {T T' : ℝ}

lemma dec_mk (M : Mb k) (f₁ f₂ β₁ β₂ : ℂ → ℂ) (A₁ A₂ : Mb k) (hA₁ : InL k A₁) (hA₂ : InL k A₂) (h1 : PS (T * T') f₁)
    (h2 : PS (T * T') f₂) (h3 : PS (T * T') β₁) (h4 : PS (T * T') β₂)
    (h : ∀ ζ : ℂ, T * T' < Complex.normSq ζ →
      M = f₁ ζ • A₁ + nuI k T T' ζ * (f₂ ζ • A₂) * nu k (wZ T T' ζ) (sZ T T' ζ) + β₁ ζ • H1 k T T' ζ +
        β₂ ζ • H2 k T T' ζ) : Dec k T T' M :=
  ⟨_, _, β₁, β₂, psl_smul h1 hA₁, psl_smul h2 hA₂, h3, h4, h⟩

lemma dec_add {M N : Mb k} (hM : Dec k T T' M) (hN : Dec k T T' N) : Dec k T T' (M + N) := by
  obtain ⟨C₁, C₂, β₁, β₂, a1, a2, a3, a4, a5⟩ := hM
  obtain ⟨D₁, D₂, γ₁, γ₂, b1, b2, b3, b4, b5⟩ := hN
  refine ⟨_, _, _, _, psl_add a1 b1, psl_add a2 b2, ps_add a3 b3, ps_add a4 b4, fun ζ hζ => ?_⟩
  conv_lhs => rw [a5 ζ hζ, b5 ζ hζ]
  rw [Matrix.mul_add, Matrix.add_mul, add_smul, add_smul]
  abel

lemma dec_smul (c : ℂ) {M : Mb k} (hM : Dec k T T' M) : Dec k T T' (c • M) := by
  obtain ⟨C₁, C₂, β₁, β₂, a1, a2, a3, a4, a5⟩ := hM
  refine ⟨_, _, _, _, psl_csmul c a1, psl_csmul c a2, ps_mul (ps_const c) a3, ps_mul (ps_const c) a4, fun ζ hζ => ?_⟩
  conv_lhs => rw [a5 ζ hζ]
  rw [Matrix.mul_smul, Matrix.smul_mul, smul_add, smul_add, smul_add, smul_smul, smul_smul]

lemma inL_Su {a b : Fin (k + 1)} (ha : a ≠ Fin.last k) (hb : b ≠ Fin.last k) : InL k (Su k a b) := by
  intro i
  unfold Su
  constructor
  · rw [Matrix.single_apply, if_neg (fun h => hb h.2)]
  · rw [Matrix.single_apply, if_neg (fun h => ha h.1)]

lemma inL_zero : InL k (0 : Mb k) := fun _ => ⟨rfl, rfl⟩

lemma ps_zero {TT : ℝ} : PS TT (fun _ => (0 : ℂ)) := ps_const 0

lemma dec_LL {a b : Fin (k + 1)} (ha : a ≠ Fin.last k) (hb : b ≠ Fin.last k) : Dec k T T' (Su k a b) :=
  dec_mk _ (fun _ => 1) (fun _ => 0) (fun _ => 0) (fun _ => 0) (Su k a b) 0 (inL_Su ha hb) inL_zero (ps_const 1) ps_zero
    ps_zero ps_zero (fun ζ _ => by simp)

lemma dec_lm (h0 : (0 : Fin (k + 1)) ≠ Fin.last k) (hT : 0 < T) (hT' : 0 < T') (m : Fin (k + 1)) (hm0 : m ≠ 0)
    (hml : m ≠ Fin.last k) : Dec k T T' (Su k (Fin.last k) m) := by
  refine dec_mk _ (fun ζ => (-1 : ℂ) * (ζ * (sig (T * T') ζ)⁻¹)) (fun ζ => (-kap T T') * (sig (T * T') ζ)⁻¹) (fun _ => 0)
    (fun _ => 0) (Su k 0 m) (Su k 0 m) (inL_Su h0 hml) (inL_Su h0 hml) (ps_mul (ps_const _) (ps_mul ps_id ps_sigInv))
    (ps_mul (ps_const _) ps_sigInv) ps_zero ps_zero (fun ζ hζ => ?_)
  have hk := kap_ne hT hT'
  have hs := sig_ne hζ
  rw [Matrix.mul_smul, Matrix.smul_mul, nuI_eq, nu_eq, conj0m h0 _ _ _ m hm0 hml, sZ_eq T T' hT hT' ζ hζ, wZ_eq]
  match_scalars <;> field_simp <;> ring

lemma dec_ml (h0 : (0 : Fin (k + 1)) ≠ Fin.last k) (hT : 0 < T) (hT' : 0 < T') (m : Fin (k + 1)) (hm0 : m ≠ 0)
    (hml : m ≠ Fin.last k) : Dec k T T' (Su k m (Fin.last k)) := by
  refine dec_mk _ (fun ζ => conj ζ * (sig (T * T') ζ)⁻¹) (fun ζ => kap T T' * (sig (T * T') ζ)⁻¹) (fun _ => 0)
    (fun _ => 0) (Su k m 0) (Su k m 0) (inL_Su hml h0) (inL_Su hml h0) (ps_mul ps_conj ps_sigInv)
    (ps_mul (ps_const _) ps_sigInv) ps_zero ps_zero (fun ζ hζ => ?_)
  have hk := kap_ne hT hT'
  have hs := sig_ne hζ
  rw [Matrix.mul_smul, Matrix.smul_mul, nuI_eq, nu_eq, conjm0 h0 _ _ _ m hm0 hml, sZ_eq T T' hT hT' ζ hζ, wZ_star]
  match_scalars <;> field_simp <;> ring

section plane

variable (h0 : (0 : Fin (k + 1)) ≠ Fin.last k) (hT : 0 < T) (hT' : 0 < T')
include h0 hT hT'

lemma plane_facts {ζ : ℂ} (hζ : T * T' < Complex.normSq ζ) :
    sZ T T' ζ ≠ 0 ∧ (kap T T')⁻¹ ≠ 0 ∧ star (wZ T T' ζ) ≠ 0 ∧
      2 * sZ T T' ζ * ((2 * kap T T')⁻¹ * conj ζ * (sig (T * T') ζ)⁻¹) = -(kap T T')⁻¹ * star (wZ T T' ζ) ∧
      2 * sZ T T' ζ * ((2 * kap T T')⁻¹ * ζ * (sig (T * T') ζ)⁻¹) = -(kap T T')⁻¹ * wZ T T' ζ := by
  have hk := kap_ne hT hT'
  have hs := sig_ne hζ
  have hz := zeta_ne hT hT' hζ
  have hzc : conj ζ ≠ 0 := by simpa using hz
  refine ⟨?_, inv_ne_zero hk, ?_, ?_, ?_⟩
  · rw [sZ_eq T T' hT hT' ζ hζ]; exact mul_ne_zero (inv_ne_zero hk) hs
  · rw [wZ_star]; exact mul_ne_zero (neg_ne_zero.2 (inv_ne_zero hk)) hzc
  · rw [sZ_eq T T' hT hT' ζ hζ, wZ_star]; field_simp
  · rw [sZ_eq T T' hT hT' ζ hζ, wZ_eq]; field_simp

lemma dec_0l : Dec k T T' (Su k 0 (Fin.last k)) := by
  refine dec_mk _ (fun ζ => (2⁻¹ : ℂ) * (conj ζ * (sig (T * T') ζ)⁻¹)) (fun ζ => (-2⁻¹ : ℂ) * (conj ζ * (sig (T * T') ζ)⁻¹))
    (fun ζ => (-1 : ℂ) * sig (T * T') ζ) (fun _ => 0) (Su k 0 0) (Su k 0 0) (inL_Su h0 h0) (inL_Su h0 h0)
    (ps_mul (ps_const _) (ps_mul ps_conj ps_sigInv)) (ps_mul (ps_const _) (ps_mul ps_conj ps_sigInv))
    (ps_mul (ps_const _) ps_sig) ps_zero (fun ζ hζ => ?_)
  obtain ⟨f1, f2, f3, f4, f5⟩ := plane_facts h0 hT hT' hζ
  have hk := kap_ne hT hT'
  have hs := sig_ne hζ
  have key := unit0l h0 _ _ _ _ _ f1 f2 f3 (ws_rel hT hT' hζ) f4
  have e1 : -(star (wZ T T' ζ) / (2 * sZ T T' ζ)) = (2⁻¹ : ℂ) * (conj ζ * (sig (T * T') ζ)⁻¹) := by
    rw [sZ_eq T T' hT hT' ζ hζ, wZ_star]; field_simp
  have e2 : star (wZ T T' ζ) / (2 * sZ T T' ζ) = (-2⁻¹ : ℂ) * (conj ζ * (sig (T * T') ζ)⁻¹) := by
    rw [sZ_eq T T' hT hT' ζ hζ, wZ_star]; field_simp
  have e3 : -(sZ T T' ζ / (kap T T')⁻¹) = (-1 : ℂ) * sig (T * T') ζ := by
    rw [sZ_eq T T' hT hT' ζ hζ]; field_simp
  rw [e1, e2, e3, ← nuI_eq, ← nu_eq] at key
  rw [zero_smul, add_zero]
  exact key

lemma decomposition_lower_corner_unit : Dec k T T' (Su k (Fin.last k) 0) := by
  refine dec_mk _ (fun ζ => (-2⁻¹ : ℂ) * (ζ * (sig (T * T') ζ)⁻¹)) (fun ζ => (2⁻¹ : ℂ) * (ζ * (sig (T * T') ζ)⁻¹))
    (fun _ => 0) (fun ζ => (-1 : ℂ) * sig (T * T') ζ) (Su k 0 0) (Su k 0 0) (inL_Su h0 h0) (inL_Su h0 h0)
    (ps_mul (ps_const _) (ps_mul ps_id ps_sigInv)) (ps_mul (ps_const _) (ps_mul ps_id ps_sigInv))
    ps_zero (ps_mul (ps_const _) ps_sig) (fun ζ hζ => ?_)
  obtain ⟨f1, f2, f3, f4, f5⟩ := plane_facts h0 hT hT' hζ
  have hk := kap_ne hT hT'
  have hs := sig_ne hζ
  have key := unitl0 h0 _ _ _ _ _ f1 f2 f3 (ws_rel hT hT' hζ) f5
  have e1 : wZ T T' ζ / (2 * sZ T T' ζ) = (-2⁻¹ : ℂ) * (ζ * (sig (T * T') ζ)⁻¹) := by
    rw [sZ_eq T T' hT hT' ζ hζ, wZ_eq]; field_simp
  have e2 : -(wZ T T' ζ / (2 * sZ T T' ζ)) = (2⁻¹ : ℂ) * (ζ * (sig (T * T') ζ)⁻¹) := by
    rw [sZ_eq T T' hT hT' ζ hζ, wZ_eq]; field_simp
  have e3 : -(sZ T T' ζ / (kap T T')⁻¹) = (-1 : ℂ) * sig (T * T') ζ := by
    rw [sZ_eq T T' hT hT' ζ hζ]; field_simp
  rw [e2, e1, e3, ← nuI_eq, ← nu_eq] at key
  rw [zero_smul, add_zero]
  exact key

lemma dec_ll : Dec k T T' (Su k (Fin.last k) (Fin.last k)) := by
  refine dec_mk _ (fun _ => 0) (fun _ => 1) (fun ζ => ζ) (fun ζ => (-1 : ℂ) * conj ζ) (Su k 0 0) (Su k 0 0)
    (inL_Su h0 h0) (inL_Su h0 h0) ps_zero (ps_const 1) ps_id (ps_mul (ps_const _) ps_conj) (fun ζ hζ => ?_)
  obtain ⟨f1, f2, f3, f4, f5⟩ := plane_facts h0 hT hT' hζ
  have hk := kap_ne hT hT'
  have key := unitll h0 _ _ _ _ _ _ f1 f2 f3 (ws_rel hT hT' hζ) f4 f5
  have e1 : -(wZ T T' ζ / (kap T T')⁻¹) = ζ := by rw [wZ_eq]; field_simp
  have e2 : star (wZ T T' ζ) / (kap T T')⁻¹ = (-1 : ℂ) * conj ζ := by rw [wZ_star]; field_simp
  rw [e1, e2, ← nuI_eq, ← nu_eq] at key
  rw [zero_smul, zero_add, one_smul]
  exact key

lemma dec_unit (a b : Fin (k + 1)) : Dec k T T' (Su k a b) := by
  by_cases ha : a = Fin.last k
  · subst ha
    by_cases hb : b = Fin.last k
    · subst hb; exact dec_ll h0 hT hT'
    · by_cases hb0 : b = 0
      · subst hb0; exact decomposition_lower_corner_unit h0 hT hT'
      · exact dec_lm h0 hT hT' b hb0 hb
  · by_cases hb : b = Fin.last k
    · subst hb
      by_cases ha0 : a = 0
      · subst ha0; exact dec_0l h0 hT hT'
      · exact dec_ml h0 hT hT' a ha0 ha
    · exact dec_LL ha hb

lemma dec_all (M : Mb k) : Dec k T T' M := by
  have hz : Dec k T T' (0 : Mb k) := by
    have := dec_smul (T := T) (T' := T') 0 (dec_LL (k := k) h0 h0)
    rwa [zero_smul] at this
  rw [Matrix.matrix_eq_sum_single M]
  refine Finset.sum_induction _ _ (fun _ _ => dec_add) hz fun i _ => ?_
  refine Finset.sum_induction _ _ (fun _ _ => dec_add) hz fun j _ => ?_
  have : Matrix.single i j (M i j) = M i j • Su k i j := by
    unfold Su; rw [Matrix.smul_single, smul_eq_mul, mul_one]
  rw [this]
  exact dec_smul _ (dec_unit h0 hT hT' i j)

end plane

end

end Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep.Core.TC.PR.CP.Dc
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.FdegOfSchur
section
noncomputable section

open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal

namespace Formalism.FourierDecayAlt.P.S3dx6

open Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData

variable {k r : ℕ}

theorem one_mem_uh : (1 : Mx k r) ∈ UH (Hpk k r) := by
  simp [UH]

theorem mem_DD {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] (σ : Mx k r → (H →L[ℂ] H)) (w0 : H)
    {t : Mx k r} (ht : t ∈ UH (Hpk k r)) : σ t w0 ∈ DDsp σ w0 := Submodule.subset_span ⟨t, ht, rfl⟩

theorem fdeg_of_schur {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {σ : Mx k r → (H →L[ℂ] H)}
    {μG : Measure (Mt k r)} {w0 : H} (hw : w0 ≠ 0) {d : ℝ} (hd : 0 < d)
    (hS : ∫ x, ⟪w0, σ (Matrix.of x) w0⟫_ℂ * star ⟪w0, σ (Matrix.of x) w0⟫_ℂ ∂μG =
      ⟪w0, w0⟫_ℂ * ⟪w0, w0⟫_ℂ / (d : ℂ)) :
    PI.BesselPeriodGGP.fdegH μG σ w0 = d := by

  have hpt : ∀ x, ⟪w0, σ (Matrix.of x) w0⟫_ℂ * star ⟪w0, σ (Matrix.of x) w0⟫_ℂ =
      ((‖⟪w0, σ (Matrix.of x) w0⟫_ℂ‖ ^ 2 : ℝ) : ℂ) := by
    intro x
    rw [show star ⟪w0, σ (Matrix.of x) w0⟫_ℂ = (starRingEnd ℂ) ⟪w0, σ (Matrix.of x) w0⟫_ℂ from rfl,
      RCLike.mul_conj]
    norm_cast
  simp_rw [hpt] at hS
  rw [integral_complex_ofReal, inner_self_eq_norm_sq_to_K] at hS
  have hI : (∫ x, ‖⟪w0, σ (Matrix.of x) w0⟫_ℂ‖ ^ 2 ∂μG) = ‖w0‖ ^ 4 / d := by
    have h2 : ((‖w0‖ ^ 4 / d : ℝ) : ℂ) = (‖w0‖ : ℂ) ^ 2 * (‖w0‖ : ℂ) ^ 2 / (d : ℂ) := by
      push_cast; ring
    exact_mod_cast hS.trans h2.symm
  have hw' : ‖w0‖ ≠ 0 := norm_ne_zero_iff.2 hw
  simp only [PI.BesselPeriodGGP.fdegH]
  rw [hI]
  field_simp

end Formalism.FourierDecayAlt.P.S3dx6
end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.HeadVectorOfParts
section
noncomputable section

open Matrix MeasureTheory Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt
open scoped ComplexConjugate

namespace Formalism.FourierDecayAlt.P.PBI

def Exh : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq) (F)
    (w : List C.Letter)
    (X : Q.ActualOps (JC.parLev P P.r).k (JC.parLev P P.r).r (p.T.bs P.r).z (p.T.bs P.r).z' (p.T.bs P.r).π (p.T.bs P.r).π')
    (μ : Measure (Mt P.k (P.r - P.r)))
    (L : R.LevelData (Q.Pr (Q.RadSp (JC.parLev P P.r).k (JC.parLev P P.r).r (p.T.bs P.r).z (p.T.bs P.r).z'
      (p.T.bs P.r).π (p.T.bs P.r).π')) (JC.parLev P P.r).r)
    (st : Fr.Start (Q.Pr (Q.RadSp (JC.parLev P P.r).k (JC.parLev P P.r).r (p.T.bs P.r).z (p.T.bs P.r).z'
      (p.T.bs P.r).π (p.T.bs P.r).π'))) (Cb : ℝ),
    P5.IsData (JC.parLev P P.r) (p.T.bs P.r).z (p.T.bs P.r).z' (p.T.bs P.r).π (p.T.bs P.r).π' X μ L st p.l0 →
    KB.InDDplus2 P p.l0 p.T.base Cb p.Θ → KB.CptCoef p.T.base F → KB.CutWord P p.l0 w →
    ∀ (e : Wd.Ix (Fin w.length)) (h : C.LPt) (hh : D.IsLocPt h P.r),
      ∃ F₂ : B.Mat P.k P.r → (Wq →L[ℂ] Wp), KB.CptCoef p.T.base F₂ ∧
      (∀ ζ : ℂ, p.V (p.Θ.Θ w e F) (h ++ [(1, ζ)]) = p.V F₂ (h ++ [(1, ζ)])) ∧
      ∀ (Φ : Wd.Ix (Fin w.length) → Q.RadSp (JC.parLev P P.r).k (JC.parLev P P.r).r (p.T.bs P.r).z (p.T.bs P.r).z'
          (p.T.bs P.r).π (p.T.bs P.r).π'),
        (∀ e', Top.IsRadOf (JC.parLev P P.r) (p.T.bs P.r) (Φ e') (KB.slv p.T F P.r le_rfl w h hh.2 e')) →
        ∀ (c : Fin (JC.parLev P P.r).r → ℂ) (γ : B.Mat P.k (P.r - P.r)), γ ∈ B.GV P.k (P.r - P.r) →
          0 < Q.GGl P.k (P.r - P.r) (p.T.bs P.r).z (p.T.bs P.r).z' γ →
          B.JF (p.T.bs P.r) (D.castF (by simp [hh.2]) (D.sliceAt P.k P.r p.T.base.z p.T.base.z' F₂ h)) γ =
            (P5.act (Fr.ofWord L st (D.positionted w)).F Φ e :
              Q.Fn (JC.parLev P P.r).k (JC.parLev P P.r).r (Wq →L[ℂ] Wp)) c γ

def HeadVecOfParts : Prop := HighestUnipotentIntegral → Exh → HeadVec

end Formalism.FourierDecayAlt.P.PBI

namespace Formalism.FourierDecayAlt.P

theorem head_vector_of_parts : PBI.HeadVecOfParts := by
  intro hU5 hExh Wp Wq _ _ _ _ _ _ P p F w X μ L st Cb ν'r m₀r hD hdd hF hcut hLev x hx γ₀ hγG hζ hγF h hh Φ hΦ e
  obtain ⟨F₂, hF₂, hV, hJ⟩ := hExh Wp Wq P p F w X μ L st Cb hD hdd hF hcut e h hh
  set ζ := Q.zetaL P.k (P.r - P.r) (p.T.bs P.r).z (p.T.bs P.r).z' (Fin.last _) x.2 with hζdef
  have hr : P.r - P.r = 0 := by omega
  have hGx : 0 < Complex.normSq ζ - Tz P.k (P.r - P.r) (p.T.bs P.r).z * Tz P.k (P.r - P.r) (p.T.bs P.r).z' :=
    hx.2.2
  have hζ0 : ζ ≠ 0 := by
    intro h0
    rw [h0, map_zero] at hGx
    nlinarith [mul_pos (p.T.bs P.r).T_pos (p.T.bs P.r).T'_pos]
  have hZ : Zhat P.k (P.r - P.r) (p.T.bs P.r).z (p.T.bs P.r).z' γ₀ = D.ptMatN [(1, ζ)] (P.r - P.r + 1) := by
    ext a b
    have ha : a = Fin.last _ := Fin.ext (by have := a.isLt; simp only [Fin.val_last]; omega)
    have hb : b = Fin.last _ := Fin.ext (by have := b.isLt; simp only [Fin.val_last]; omega)
    subst ha hb
    rw [← PBI.zetaL_eq_zhat, hζ]
    simp [D.ptMatN, D.ptEntry, hr]
  have hγGG : 0 < Q.GGl P.k (P.r - P.r) (p.T.bs P.r).z (p.T.bs P.r).z' γ₀ := by
    show 0 < Complex.normSq (Q.zetaL P.k (P.r - P.r) (p.T.bs P.r).z (p.T.bs P.r).z' (Fin.last _) γ₀) -
      Tz P.k (P.r - P.r) (p.T.bs P.r).z * Tz P.k (P.r - P.r) (p.T.bs P.r).z'
    rw [hζ]; exact hGx
  show p.V (p.Θ.Θ w e F) (h ++ [(1, ζ)]) = _
  rw [hV, hU5 Wp Wq P p F₂ h ζ hh ν'r m₀r hF₂ hζ0 hLev.1 hLev.2.1,
    PBM.vector_level_zero_eq_jacquet hr (p.T.bs P.r) ν'r m₀r hLev.2.2 _ ζ (by linarith) γ₀ hγG hZ hγF]
  exact hJ Φ hΦ x.1 γ₀ hγG hγGG

end Formalism.FourierDecayAlt.P
end
end

