import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2068
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0026
import Formalism.LocalToGlobal.IndefiniteReal.FWExist
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0028
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0027
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0011
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RightTranslationLiftEqLevelMoveUnitConst
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ActLevMemCuspA
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1697
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1527
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1359
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinearModelCompactConjugateExists
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1116
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2048
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2076
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2058
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinearModelUnitaryConjugate
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2077
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalIntertwinerUniqueScalar
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0229

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LambdaPrimeAllPoints
section
set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.ExpTie

namespace GlobalTheory.LiftWeightForced

open Formalism.IndefR.IndefiniteWeightData

def wd (D : D7) (j : Fin D.R.m) (τ : D.what₂.Tau) : WeightData where
  k := D.R.k
  m := D.R.m
  t := D.R.t
  j := (j : ℕ) + 1
  e := ((D.hc τ).e_int j).choose
  v := fun n => if h : 2 ≤ n ∧ n - 2 < D.R.k - 1 then ((D.hc τ).v_int ⟨n - 2, h.2⟩).choose else 0
  b := fun n => if h : 1 ≤ n ∧ n - 1 < D.R.m then ((D.hc τ).b_int ⟨n - 1, h.2⟩).choose else 0

variable (D : D7) (j : Fin D.R.m) (τ : D.what₂.Tau)

theorem wd_e : ((wd D j τ).e : ℚ) = (D.hc τ).e j := ((D.hc τ).e_int j).choose_spec.symm

theorem wd_v (n : ℕ) (h : 2 ≤ n ∧ n - 2 < D.R.k - 1) : ((wd D j τ).v n : ℚ) = (D.hc τ).v ⟨n - 2, h.2⟩ := by
  show (((if h : 2 ≤ n ∧ n - 2 < D.R.k - 1 then ((D.hc τ).v_int ⟨n - 2, h.2⟩).choose else 0 : ℤ)) : ℚ) = _
  rw [dif_pos h]
  exact ((D.hc τ).v_int _).choose_spec.symm

theorem wd_b (n : ℕ) (h : 1 ≤ n ∧ n - 1 < D.R.m) : ((wd D j τ).b n : ℚ) = (D.hc τ).b ⟨n - 1, h.2⟩ := by
  show (((if h : 1 ≤ n ∧ n - 1 < D.R.m then ((D.hc τ).b_int ⟨n - 1, h.2⟩).choose else 0 : ℤ)) : ℚ) = _
  rw [dif_pos h]
  exact ((D.hc τ).b_int _).choose_spec.symm

end GlobalTheory.LiftWeightForced

namespace GlobalTheory.LiftWeightForced

open Formalism.IndefR.IndefiniteWeightData

variable (D : D7) (j : Fin D.R.m) (τ : D.what₂.Tau)

theorem wd_lam_lo (i : ℕ) (h1 : 1 ≤ i) (h2 : i ≤ D.R.k - 1) :
    ((wd D j τ).lam i : ℚ) = (D.hc τ).v ⟨i - 1, by omega⟩ := by
  have hk : (wd D j τ).k = D.R.k := rfl
  unfold WeightData.lam
  rw [if_pos (by rw [hk]; exact h2), wd_v D j τ (i + 1) ⟨by omega, by omega⟩]
  exact congrArg _ (Fin.ext (by simp))

theorem wd_lam_hi (i : ℕ) (h1 : D.R.k - 1 < i) (h2 : i - (D.R.k - 1) - 1 < D.R.m) :
    ((wd D j τ).lam i : ℚ) = -(D.hc τ).b ⟨i - (D.R.k - 1) - 1, h2⟩ := by
  have hk : (wd D j τ).k = D.R.k := rfl
  unfold WeightData.lam
  rw [if_neg (by rw [hk]; omega)]
  push_cast
  rw [hk, wd_b D j τ _ ⟨by omega, h2⟩]

theorem wd_hyp : (wd D j τ).Hyp := by
  have hR := D.R.m_add_three_le_k
  have hm2 := D.R.two_le_m
  have hjm := j.2
  have ht : (0 : ℚ) ≤ D.R.t := by positivity
  set P := D.hc τ with hP
  have hu : ∀ a b : Fin D.R.k, a.1 = b.1 → P.u a = P.u b := fun a b h => congrArg _ (Fin.ext h)
  have hb : ∀ a b : Fin D.R.m, a.1 = b.1 → P.b a = P.b b := fun a b h => congrArg _ (Fin.ext h)
  refine ⟨show 1 ≤ D.R.k by omega, show 1 ≤ (j : ℕ) + 1 by omega, show (j : ℕ) + 1 ≤ D.R.m by omega, ?_, D.R.t_odd, ?_, ?_, ?_⟩
  · show Odd (D.R.k + D.R.m - 1)
    exact Nat.Even.sub_odd (by omega) (D.R.k_even.add D.R.m_even) odd_one
  · intro i hi1 hi2
    have hi2' : i < D.R.k + D.R.m - 1 := hi2
    suffices ((wd D j τ).lam (i + 1) : ℚ) < (wd D j τ).lam i by exact_mod_cast this
    rcases lt_trichotomy (i + 1) (D.R.k) with h | h | h
    · rw [wd_lam_lo D j τ (i + 1) (by omega) (by omega), wd_lam_lo D j τ i hi1 (by omega)]
      have h1 := P.u_gt_v ⟨i, by omega⟩
      have h2 := P.v_gt_u ⟨i - 1, by omega⟩
      rw [hu ⟨i - 1 + 1, _⟩ ⟨i, by omega⟩ (by simp; omega)] at h2
      have e1 : (⟨i + 1 - 1, by omega⟩ : Fin (D.R.k - 1)) = ⟨i, by omega⟩ := Fin.ext (by simp)
      rw [e1]
      exact h1.trans h2
    · rw [wd_lam_hi D j τ (i + 1) (by omega) (by omega), wd_lam_lo D j τ i hi1 (by omega)]
      have h1 := P.u_last_gt (by omega) (by omega)
      have h2 := P.v_gt_u ⟨i - 1, by omega⟩
      rw [hu ⟨i - 1 + 1, _⟩ ⟨D.R.k - 1, by omega⟩ (by simp; omega)] at h2
      rw [hb ⟨i + 1 - (D.R.k - 1) - 1, _⟩ ⟨0, by omega⟩ (by simp; omega)]
      exact h1.trans h2
    · rw [wd_lam_hi D j τ (i + 1) (by omega) (by omega), wd_lam_hi D j τ i (by omega) (by omega)]
      have h1 := P.gap_be ⟨i - (D.R.k - 1) - 1, by omega⟩
      have h2 := P.gap_eb ⟨i - (D.R.k - 1) - 1, by omega⟩ (by simp; omega)
      rw [hb ⟨i - (D.R.k - 1) - 1 + 1, _⟩ ⟨i + 1 - (D.R.k - 1) - 1, by omega⟩ (by simp; omega)] at h2
      linarith
  · show (((wd D j τ).b ((j : ℕ) + 1)) : ℤ) < (wd D j τ).e
    suffices ((wd D j τ).b ((j : ℕ) + 1) : ℚ) < (wd D j τ).e by exact_mod_cast this
    rw [wd_b D j τ _ ⟨by omega, by omega⟩, wd_e, hb _ j (by simp)]
    have := P.gap_be j
    linarith
  · intro hj'
    have hj'' : (j : ℕ) + 1 < D.R.m := hj'
    show ((wd D j τ).e : ℤ) < (wd D j τ).b ((j : ℕ) + 1 + 1)
    suffices ((wd D j τ).e : ℚ) < (wd D j τ).b ((j : ℕ) + 1 + 1) by exact_mod_cast this
    rw [wd_b D j τ _ ⟨by omega, by omega⟩, wd_e, hb _ ⟨(j : ℕ) + 1, hj''⟩ (by simp)]
    have := P.gap_eb j hj''
    linarith

theorem wd_gap : (wd D j τ).GapHyp := by
  have hjm := j.2
  set P := D.hc τ with hP
  have hb : ∀ a b : Fin D.R.m, a.1 = b.1 → P.b a = P.b b := fun a b h => congrArg _ (Fin.ext h)
  refine ⟨?_, ?_⟩
  · show ((D.R.t : ℚ) + 3) / 2 ≤ ((wd D j τ).e : ℚ) - (wd D j τ).b ((j : ℕ) + 1)
    rw [wd_b D j τ _ ⟨by omega, by omega⟩, wd_e, hb _ j (by simp)]
    exact P.gap_be j
  · intro hj'
    have hj'' : (j : ℕ) + 1 < D.R.m := hj'
    show ((D.R.t : ℚ) + 3) / 2 ≤ ((wd D j τ).b ((j : ℕ) + 1 + 1) : ℚ) - (wd D j τ).e
    rw [wd_b D j τ _ ⟨by omega, by omega⟩, wd_e, hb _ ⟨(j : ℕ) + 1, hj''⟩ (by simp)]
    exact P.gap_eb j hj''

end GlobalTheory.LiftWeightForced

namespace GlobalTheory.LiftWeightForced

open Formalism.IndefR.IndefiniteWeightData

variable (D : D7) (j : Fin D.R.m) (τ : D.what₂.Tau)

theorem exists_isLamPrime :
    ∃ lam : DomWeight (Vc D j).rank, Formalism.IndefR.Bridge.IsLamPrime (D := D) lam ((j : ℕ) + 1) τ := by
  have hjm := j.2
  have hC := GlobalTheory.LowestKType.thetaSide (wd D j τ) (wd_hyp D j τ) (wd_gap D j τ)
  have hint := hC.2.2.2.1
  have hdom := hC.2.2.2.2.1
  have hN : (Vc D j).rank = (wd D j τ).nV := D.sp.V_rank _ (by omega) (by omega)

  have hmono : ∀ d a : ℕ, 1 ≤ a → a + d ≤ (wd D j τ).nV →
      (wd D j τ).lamPrime (a + d) ≤ (wd D j τ).lamPrime a := by
    intro d
    induction d with
    | zero => intro a _ _; simp
    | succ d ih =>
      intro a ha had
      have := hdom (a + d) (by omega) (by omega)
      rw [← add_assoc]
      exact this.trans (ih a ha (by omega))
  let w : Fin (Vc D j).rank → ℤ := fun i => (hint (i.1 + 1) (by omega) (by have := i.2; omega)).choose
  have hw : ∀ i, (w i : ℚ) = (wd D j τ).lamPrime (i.1 + 1) := fun i =>
    (hint (i.1 + 1) (by omega) (by have := i.2; omega)).choose_spec.symm
  have hanti : Antitone w := by
    intro a b hab
    have hab' : a.1 ≤ b.1 := hab
    have := hmono (b.1 - a.1) (a.1 + 1) (by omega) (by have := b.2; omega)
    rw [show a.1 + 1 + (b.1 - a.1) = b.1 + 1 by omega] at this
    have h' : (w b : ℚ) ≤ w a := by rw [hw, hw]; exact this
    exact_mod_cast h'
  refine ⟨⟨w, hanti⟩, ⟨by omega, by omega⟩, wd D j τ, rfl, rfl, rfl, rfl, ?_, ?_, ?_, ?_⟩
  · rw [wd_e]
    exact congrArg _ (Fin.ext (by simp))
  · intro a
    rw [wd_v D j τ _ ⟨by omega, by have := a.2; omega⟩]
    exact congrArg _ (Fin.ext (by simp))
  · intro a
    rw [wd_b D j τ _ ⟨by omega, by have := a.2; omega⟩]
    exact congrArg _ (Fin.ext (by simp))
  · intro i
    exact hw i

theorem isLamPrime_lamLdef :
    Formalism.IndefR.Bridge.IsLamPrime (D := D)
      (Formalism.IndefR.Bridge.lamLdef (D := D) (Vc D j).rank ((j : ℕ) + 1) τ) ((j : ℕ) + 1) τ := by
  have hex := exists_isLamPrime D j τ
  unfold Formalism.IndefR.Bridge.lamLdef
  rw [dif_pos hex]
  exact hex.choose_spec

end GlobalTheory.LiftWeightForced

theorem GlobalTheory.LiftWeightForced.atPts : GlobalTheory.BigOn.AtPts fun Fm x _ i _ => ∀ (j : Fin (Fm.D x i).R.m) τ,
    Formalism.IndefR.Bridge.IsLamPrime (D := Fm.D x i)
      (Formalism.IndefR.Bridge.lamLdef (D := Fm.D x i) (Formalism.IndefR.Links.Vc (Fm.D x i) j).rank ((j : ℕ) + 1) τ) ((j : ℕ) + 1) τ :=
  ⟨1, one_pos, fun _ _ _ => ⟨⟨0, fun _ => 0, fun _ => 0, fun _ => 0⟩, fun Fm _ _ _ =>
    EvPt.of_forall fun x _ i _ _ _ j τ => GlobalTheory.LiftWeightForced.isLamPrime_lamLdef (Fm.D x i) j τ⟩⟩
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelMoveStabiliserCharacterDet
section
noncomputable section

namespace GlobalTheory.StabMove

section Adelic

open NumberField IsDedekindDomain AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
  Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj GlobalTheory.LevelCusp GlobalTheory.DictMove
open GlobalTheory.Dict (castFr)
open scoped TensorProduct Matrix

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E} {Dw : Datum H}

set_option maxHeartbeats 1000000 in

theorem exists_carries {V W : HSp D} (hV : V = W) {l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H} {Xo : Moduli Dw l}
    {c : Coeff l} {σ : c.F →+* ℂ} {r : ℕ} (hr : V.rank = r) (hr' : W.rank = r) {U : Unf Xo c σ r}
    {dict : GA D V → Σ k, Frame (U.X k).Ψ r} (io : Dw.La →ₗ[𝓞 D.host.E] (Fin r → D.host.E)) {g : ℕ}
    {e : Fin g ≃ Σ τ : D.host.E →+* ℂ, Fin (Dw.mult τ)}
    {F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (fun j => relab c σ (e j).1)}
    {ik : U.Comp → Fin F.n} {φ : ∀ k, (F.Di (ik k)).La ≃ₗ[𝓞 D.host.E] (U.X k).Λ}
    {th : ∀ k, (U.X k).Ψ → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)}
    {x₀ : (D.host.E →+* ℂ) → Matrix (Fin r) (Fin r) ℂ}
    (hU : IsUnf U) (hW : ∀ k, ModelW V hr (U.X k))
    (hL : DictLat U V hr dict (LinearMap.funLeft (𝓞 D.host.E) D.host.E (Fin.cast hr) ∘ₗ io) e F ik φ th x₀)
    (hth : ∀ k τ, Formalism.MainNotions.StandardLattice.IsInfEmb τ.1 (th k τ)) (hdom : ∀ h, (dict h).2 ∈ (U.X (dict h).1).dom)
    {s : Dw.La →ₗ[𝓞 D.host.E] Dw.La} {κ : GA D W}
    (hκ : Induces W l (LinearMap.funLeft (𝓞 D.host.E) D.host.E (Fin.cast hr') ∘ₗ io) s κ) (h : GA D W) :
    (Formalism.IndefR.FWT.castDict hV dict h).2 ∈ (U.X (Formalism.IndefR.FWT.castDict hV dict h).1).dom ∧
      ∃ δ, ∃ hc : Carries φ s (Formalism.IndefR.FWT.castDict hV dict h).1 (Formalism.IndefR.FWT.castDict hV dict (h * κ)).1 δ,
        (Formalism.IndefR.FWT.castDict hV dict (h * κ)).2 =
          lact δ (castFr hc.mt.psi (Formalism.IndefR.FWT.castDict hV dict h).2) := by
  subst hV
  subst hr
  change DictLat U V rfl dict io e F ik φ th x₀ at hL
  change Induces V l io s κ at hκ
  refine ⟨hdom h, ?_⟩
  change ∃ δ, ∃ hc : Carries φ s (dict h).1 (dict (h * κ)).1 δ,
      (dict (h * κ)).2 = lact δ (castFr hc.mt.psi (dict h).2)
  have hG : ∀ k, (U.X k).Gm = -V.gramᵀ := fun k => (hW k).1
  have hxi : ∀ k k', (U.X k).ξ0 = (U.X k').ξ0 := fun k k' => (hW k).2.trans (hW k').2.symm
  obtain ⟨θ, hθ⟩ := (GlobalTheory.Member.infiniteAdele_bijective D).1
  obtain ⟨hAr, -, -⟩ := GlobalTheory.T.archimedeanMatrix_unitary_continuous_multiplicative D V θ hθ
  obtain ⟨γ₁, hγ₁, hΛ₁, hm₁, hf₁⟩ := hL.2 h
  obtain ⟨γ₂, hγ₂, hΛ₂, hm₂, hf₂⟩ := hL.2 (h * κ)
  have e₀ : γ₂ * (h * κ) = γ₂ * γ₁⁻¹ * (γ₁ * h) * κ := by group
  obtain ⟨δ, hδu, hδf, hδa⟩ := GlobalTheory.MarkCoset.rational_matrix V (γ₂ * γ₁⁻¹) (mul_mem hγ₂ (inv_mem hγ₁))
  obtain ⟨gam, e₁, t₁, hgam⟩ := GlobalTheory.TwistTie.marked_isometry_half V l io (U.X (dict h).1) (U.X (dict (h * κ)).1) _ _
    (φ _) (φ _) (F.t _) (F.t _) s (γ₁ * h) (γ₂ * γ₁⁻¹) κ (hW _) (hW _) (hL.1.1 _) (hL.1.1 _) δ hδu hδf hκ.2.1 hκ.2.2
    ⟨hΛ₁, hm₁⟩ (by rw [← e₀]; exact ⟨hΛ₂, hm₂⟩)
  have hmt : IsMatch (U.X (dict h).1) (U.X (dict (h * κ)).1) δ := by
    refine ⟨Finset.ext fun τ => ((hU.2.1 _).2 τ).trans ((hU.2.1 _).2 τ).symm, (hU.2.1 _).1.trans (hU.2.1 _).1.symm,
      hxi _ _, fun u v => by rw [hG, hG]; exact hδu u v, fun v => ⟨fun hv => ?_, fun hv => ?_⟩⟩
    · obtain ⟨a, ha⟩ := (φ _).surjective ⟨v, hv⟩
      rw [show v = (φ (dict h).1 a : Fin V.rank → D.host.E) by rw [ha], ← hgam]
      exact (φ _ _).2
    · obtain ⟨a, ha⟩ := (φ _).surjective ⟨_, hv⟩
      obtain ⟨b, rfl⟩ := gam.surjective a
      have h1 := congrArg (fun u => (δ⁻¹).1 *ᵥ u) ((hgam b).symm.trans (congrArg Subtype.val ha))
      simp only [Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec] at h1
      rw [← h1]
      exact (φ _ _).2
  refine ⟨δ, ⟨hmt, by rw [hG, hG], gam, e₁, t₁, hgam⟩, funext fun τ => ?_⟩
  change mat (dict (h * κ)).2 τ = δ.1.map τ.1 * mat (dict h).2 ⟨τ.1, hmt.mem τ⟩
  rw [hf₁, hf₂, GlobalTheory.LettersCheck.isInfEmb_unique τ.1 _ _ (hth _ τ) (hθ τ.1),
    GlobalTheory.LettersCheck.isInfEmb_unique τ.1 _ _ (hth _ ⟨τ.1, hmt.mem τ⟩) (hθ τ.1), e₀, (hAr τ.1).2.1, (hAr τ.1).2.1,
    (hAr τ.1).2.2.1 κ hκ.1, hδa τ.1 _ (hθ τ.1), Matrix.mul_one, ← Matrix.mul_assoc]
  rfl

set_option maxHeartbeats 1000000 in

theorem rdU_eq_of_carries_self (T : CoreJ D) (hT : LawsJ T) {j : ℕ} (hj : InR D j) {σ : T.Q.c.F →+* ℂ}
    (hσ : GoodEmb T.Q.c σ) {g : ℕ} {e : Fin g ≃ Σ τ : D.host.E →+* ℂ, Fin ((T.Q.Dw j).mult τ)}
    {F : FamilyUnif (T.Q.Xo j) (σ.comp (IntermediateField.inclusion T.Q.c.le).toRingHom)
      (fun i => relab T.Q.c σ (e i).1)}
    {ik : (T.U j σ).Comp → Fin F.n} {φ : ∀ k, (F.Di (ik k)).La ≃ₗ[𝓞 D.host.E] ((T.U j σ).X k).Λ}
    (hP : HasPeriods φ) {G : Type} [Group G]
    {lev : G → ((T.Q.Dw j).La →ₗ[𝓞 D.host.E] (T.Q.Dw j).La) × ((T.Q.Dw j).La →ₗ[𝓞 D.host.E] (T.Q.Dw j).La)}
    (hact : ActLev (Xo := T.Q.Xo j) T.Q.c lev) (a : G) {w : (D.host.E →+* ℂ) × ℕ → ℕ} {n : ℕ} (hD : Dom w n)
    {f : Rul (T.Q.Xo j) T.Q.c} (hf : f ∈ sec (T.Q.Xo j) T.Q.c w n)
    (p q : Σ k, Frame ((T.U j σ).X k).Ψ D.R.r) (hp : p.2 ∈ ((T.U j σ).X p.1).dom) {δ : GL (Fin D.R.r) D.host.E}
    (hc : Carries φ (lev a).1 p.1 q.1 δ) (hq : q.2 = lact δ (castFr hc.mt.psi p.2)) (hpq : q.1 = p.1) :
    rdU (T.U j σ) (actLev T.Q.c lev a f) p.1 p.2 = rdU (T.U j σ) f q.1 q.2 := by
  obtain ⟨k, x⟩ := p
  obtain ⟨k', x'⟩ := q
  dsimp only at hp hc hq hpq ⊢
  subst hpq
  rw [hq]
  obtain ⟨-, hA, -, -, -, -, hnum⟩ := GlobalTheory.PinNum.numerics_of_pins D T.Q hT.pins
  have hU := hT.unf _ hj σ hσ
  have hr := hU.1 ▸ (show 1 ≤ D.R.r from (hnum _ hj).2.1)
  obtain ⟨hneg, φD, h1, h2, h3⟩ := GlobalTheory.GeoLevel.model_space_of_lawsJ D T hT j hj σ hσ k'
  obtain ⟨h4, hdet⟩ := GlobalTheory.GeoLevel.four_dvd_finrank_and_det_eq_pm_one D
  obtain ⟨ρ, ν, hρ, hν, -⟩ := mvPt_spec hact.total a ((T.U j σ).un k' ⟨x, hp⟩)
  refine GlobalTheory.T.movedSection_reading_eq_movedFrame_reading D.host.E T.Q.H (T.Q.Dw j) T.Q.l (T.Q.Xo j) T.Q.c σ D.R.r (Formalism.L2.PjFree.Unf.ofPj (T.U j σ)) hσ hU
    k' φD h1 h2 h3 hneg δ hc.mt ((hdet _ _ δ hc.mt).imp_right fun h => ⟨h, h4⟩) ρ ν hν.1
    (fun z y' hm => move_eq hσ hr hA hP hc hν z hm) w n hD f hf _
    (actL_mem _ _ _ _ hact.total hact.nat hact.bor _ a hf) (fun y y' hm => ?_) x hp
  have m1 := mvPt_spec hact.total a y
  have m2 : levActR (Xo := T.Q.Xo j) (c := T.Q.c) lev a y y' := ⟨ρ, ν, hρ, hν, hm⟩
  exact (evalAt_actL hact (hT.evalWD _ hj) frMap_trans_id a hf.1 y).trans
    (evalAt_congr_id (hT.evalWD _ hj) frMap_trans_id hf.1 (hact.func a _ y _ _ m1 m2) (hact.func a _ y _ _ m2 m1))

end Adelic

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in

theorem phiAt_actLev_of_comp_eq : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec) (O : ∀ i, OMDat T.toCore R i Unit (fun _ => A.μ0)), R.toLevCh.Is A.μ0 → TieIn T R κ v₀ → T.pb = R.C.P.pb → (∀ i, OMPins T R κ v₀ O i) → ∀ (i : Fin D.R.m) (σ : T.Q.c.F →+* ℂ), GoodEmb T.Q.c σ → ∀ hV : T.V ((i : ℕ) + 1) σ = Wc D i, ∀ g k, Lev.IsLevelLift (Wc D i) (R.βW i) (R.datWp i R.triv) (R.eG g) k → ∀ y : T.Q.c.F, D.what₂.embLL (algebraMap T.Q.c.F D.what₂.LL y) = ((chiC R i g : ℂˣ) : ℂ) → ∀ h, (castDict hV (T.dict ((i : ℕ) + 1) σ) (h * k)).1 = (castDict hV (T.dict ((i : ℕ) + 1) σ) h).1 → ∀ f ∈ T.cuspA ((i : ℕ) + 1) (wtA (κ i)) (κ i).n, phiAt T i σ hV (fun _ => 1) (actLev T.Q.c (O i).lev2 g f) h = σ y * phiAt T i σ hV (fun _ => 1) f (h * k) := by
  intro D G _ _ Pl0 T0 A T _ R κ v₀ O hR ht hpb hO i σ hσ hV g k hk y hy p hp f hf
  have hj : InR D ((i : ℕ) + 1) := ⟨Nat.le_add_left _ _, i.2⟩
  have h := ht.laws
  obtain ⟨_, _, -, hd⟩ := h.dictU _ hj σ hσ
  obtain ⟨hr, g₀, e, F, ik, φ, th, hio, -, hth, hL⟩ := h.adPin _ hj σ hσ
  obtain ⟨_, hW⟩ := h.modelW _ hj σ hσ
  have hU := h.unf _ hj σ hσ
  have hK := h.levelK _ hj σ hσ
  rw [← h.pins.2.1.1] at hK
  obtain ⟨hio', hK'⟩ := GlobalTheory.DictMove.cast_level hV hK (T.iota _) hr (rank_Wc i) hio
  obtain ⟨k₀, hk₀, hs⟩ := (hO i).2.lift.lev g
  have hI := GlobalTheory.DictMove.induces_of_lift hio' (hR.βW i)
    (fun k hk => hK' k ((GlobalTheory.LiftLevel.isLift_one_iff_mem_level T R κ v₀ hR ht hpb i σ hσ hV k).1 hk)) hk₀ hk hs
  obtain ⟨hdom, δ, hc, hq⟩ := exists_carries hV hr (rank_Wc i) (T.iota _) hU hW hL hth hd.2.2.2.1 hI p
  have key := rdU_eq_of_carries_self T h hj hσ hL.1.2 (hO i).2.act.1 g (dom_wtA (κ i))
    ((mem_cusp _ _ _ _ _ _).1 hf).1 _ _ hdom hc hq hp
  obtain ⟨y', hy', hy1⟩ := GlobalTheory.GeoLevel.mu_lift hR ht hpb i hσ hV hk
  obtain rfl : y = y' := (algebraMap T.Q.c.F D.what₂.LL).injective (D.what₂.embLL.injective (hy.trans hy'.symm))
  have hmu := h.muUnit _ hj σ hσ
  rw [GlobalTheory.GeoLevel.phiAt_eq, GlobalTheory.GeoLevel.phiAt_eq, GlobalTheory.GeoLevel.castDict_mu_mul hmu.1, ← mul_assoc,
    mul_left_comm (σ y), hy1, mul_one]
  unfold GlobalTheory.GeoLevel.frameRead
  rw [key]

end GlobalTheory.StabMove
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinearModelCompactConjugateExistsStatement
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.KSplit
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.linear_model_compact_conjugate_exists : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ)
    (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' →
    ∀ (v : Pl F) (t : E →ₐ[F] Fv F v) (b : GL (Fin n) (Fv F v)) (c : GL (Fin d) (Fv F v)), ∀ ι, M.IsLinW B.ψ t b c ι →
    ∃ κ : UA σ X.J → ℂ, ∀ g ∈ UAt σ X (evFin F v), ∀ φ ∈ SB (Fin n × Fin d → Fv F v), ∀ φ₁ ∈ SB (Fin n × Fin d → Fv F v),
      Acts (evFin F v) (om (g, 1)) φ φ₁ → ι φ₁ = κ g • fun Y => ι φ (((locMat t b g)⁻¹ : GL (Fin n) (Fv F v)).val * Y) := by
  first | exact @GlobalTheory.ShapeUXBas.shapeX | exact GlobalTheory.ShapeUXBas.shapeX | (intros; apply GlobalTheory.ShapeUXBas.shapeX <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinearModelCompactEquivarianceStatement
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.KSplit
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.linear_model_compact_equivariance : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ)
    (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' →
    ∀ (v : Pl F) (t : E →ₐ[F] Fv F v) (b : GL (Fin n) (Fv F v)) (c : GL (Fin d) (Fv F v)), ∀ ι, M.IsLinW B.ψ t b c ι →
    ∀ κ : UA σ W.J → ℂ, (∀ h ∈ UAt σ W (evFin F v), ∀ φ ∈ SB (Fin n × Fin d → Fv F v), ∀ φ₁ ∈ SB (Fin n × Fin d → Fv F v),
      Acts (evFin F v) (om (1, h)) φ φ₁ → ι φ₁ = κ h • fun Y => ι φ (Y * (GlobalTheory.SplitFlip.invT (locMat t c h)).val)) →
    ∀ (dd : GlobalTheory.DblScal.DblCo σ X W) (omd : GlobalTheory.DblScal.DblRep σ (n := n) W),
      IsDblCoord (cA σ) (-1) (incM F X.J) (incM F W.J) M.co dd →
      IsUSplitting (adeleClass F) B.ψ dd (actB (cA σ)) omd →
      (∀ (g : UA σ W.J) (gd : GlobalTheory.DblScal.UD σ W.J),
        ((gd : GL (Fin d ⊕ Fin d) (AE F E)) : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) (AE F E)) =
          Matrix.fromBlocks (mat g) 0 0 1 →
        ∀ φ₁ ∈ schA F (Fin n × Fin d), ∀ φ₂ ∈ schA F (Fin n × Fin d), omd gd (boxFun φ₁ φ₂) = boxFun (om (1, g) φ₁) φ₂) →
      GlobalTheory.DblScal.LocOps omd v →
      ∀ ιd, GlobalTheory.DblScal.IsLinD B.ψ dd t b c ιd →
      (∀ φ₁ ∈ SB (Fin n × Fin d → Fv F v), ∀ φ₂ ∈ SB (Fin n × Fin d → Fv F v),
        ιd (boxFun φ₁ φ₂) = fun Y => ι φ₁ (Y.submatrix id Sum.inl) *
          starRingEnd ℂ (ι (fun x => starRingEnd ℂ (φ₂ x)) (Y.submatrix id Sum.inr))) →
      ∀ cd, GlobalTheory.DblScal.IsShapeD omd t c ιd cd →
      ∀ h ∈ UAt σ W (evFin F v), ∀ gd : GlobalTheory.DblScal.UD σ W.J,
        ((gd : GL (Fin d ⊕ Fin d) (AE F E)) : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) (AE F E)) =
          Matrix.fromBlocks (mat h) 0 0 1 → κ h = cd gd := by
  first | exact @GlobalTheory.DblScalBox.scal_diag_one | exact GlobalTheory.DblScalBox.scal_diag_one | (intros; apply GlobalTheory.DblScalBox.scal_diag_one <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinearModelDoubleSplittingStatement
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.KSplit
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.linear_model_double_splitting : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ)
    (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' →
    ∀ (v : Pl F) (t : E →ₐ[F] Fv F v) (b : GL (Fin n) (Fv F v)) (c : GL (Fin d) (Fv F v)), ∀ ι, M.IsLinW B.ψ t b c ι →
    ∀ dd : GlobalTheory.DblScal.DblCo σ X W, IsDblCoord (cA σ) (-1) (incM F X.J) (incM F W.J) M.co dd →
    ∃ ιd, GlobalTheory.DblScal.IsLinD B.ψ dd t b c ιd ∧
      ∀ φ₁ ∈ SB (Fin n × Fin d → Fv F v), ∀ φ₂ ∈ SB (Fin n × Fin d → Fv F v),
        ιd (boxFun φ₁ φ₂) = fun Y => ι φ₁ (Y.submatrix id Sum.inl) *
          starRingEnd ℂ (ι (fun x => starRingEnd ℂ (φ₂ x)) (Y.submatrix id Sum.inr)) := by
  first | exact @GlobalTheory.DblLin.dblLin | exact GlobalTheory.DblLin.dblLin | (intros; apply GlobalTheory.DblLin.dblLin <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinearModelUnitaryConjugateStatement
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.KSplit
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.linear_model_unitary_conjugate : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ)
    (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' →
    ∀ (v : Pl F) (t : E →ₐ[F] Fv F v) (b : GL (Fin n) (Fv F v)) (c : GL (Fin d) (Fv F v)), ∀ ι, M.IsLinW B.ψ t b c ι →
    ∃ κ : UA σ W.J → ℂ, ∀ h ∈ UAt σ W (evFin F v), ∀ φ ∈ SB (Fin n × Fin d → Fv F v), ∀ φ₁ ∈ SB (Fin n × Fin d → Fv F v),
      Acts (evFin F v) (om (1, h)) φ φ₁ → ι φ₁ = κ h • fun Y => ι φ (Y * (GlobalTheory.SplitFlip.invT (locMat t c h)).val) := by
  first | exact @GlobalTheory.LinWShape.shape_right | exact GlobalTheory.LinWShape.shape_right | (intros; apply GlobalTheory.LinWShape.shape_right <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinearModelUnitaryIntertwinesStatement
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.KSplit
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.linear_model_unitary_intertwines : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ)
    (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' →
    ∀ (v : Pl F) (t : E →ₐ[F] Fv F v) (b : GL (Fin n) (Fv F v)) (c : GL (Fin d) (Fv F v)), ∀ ι, M.IsLinW B.ψ t b c ι →
    ∀ κ : UA σ X.J → ℂ, (∀ g ∈ UAt σ X (evFin F v), ∀ φ ∈ SB (Fin n × Fin d → Fv F v), ∀ φ₁ ∈ SB (Fin n × Fin d → Fv F v),
      Acts (evFin F v) (om (g, 1)) φ φ₁ → ι φ₁ = κ g • fun Y => ι φ (((locMat t b g)⁻¹ : GL (Fin n) (Fv F v)).val * Y)) →
    ∀ g ∈ UAt σ X (evFin F v), κ g = (chrW χW t (GlobalTheory.SplitFlip.gdet (locMat t b g)) : ℂ) *
      GlobalTheory.SplitFlip.apow (GlobalTheory.SplitFlip.gdet (locMat t b g)) (-(d : ℂ) / 2) := by
  first | exact @GlobalTheory.SplitScalX.scalar_left | exact GlobalTheory.SplitScalX.scalar_left | (intros; apply GlobalTheory.SplitScalX.scalar_left <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalIntertwinerUniqueScalarStatement
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.WeilTr MeasureTheory
open scoped Matrix ENNReal

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_intertwiner_unique_scalar : ∀ (F : Type) [Field F] [NumberField F] (v : Pl F) [Invertible (2 : Fv F v)] (κ : Type) [Fintype κ]
    (ψv : AddChar (Fv F v) ℂ), Continuous ψv → ψv ≠ 1 →
    ∀ (T : ((κ → Fv F v) → ℂ) →ₗ[ℂ] (κ → Fv F v) → ℂ) (A : (κ → Fv F v) × (κ → Fv F v) → (κ → Fv F v) × (κ → Fv F v)),
      (∀ φ ∈ SB (κ → Fv F v), T φ ∈ SB (κ → Fv F v)) →
      (∀ w, ∀ φ ∈ SB (κ → Fv F v), T (schr ψv w φ) = schr ψv (A w) (T φ)) →
      ∃ c : ℝ, 0 ≤ c ∧ ∀ μ : @Measure (κ → Fv F v) (borel _), @Measure.IsAddHaarMeasure _ _ _ (borel _) μ →
        ∀ φ ∈ SB (κ → Fv F v), ∀ φ' ∈ SB (κ → Fv F v),
          @integral _ ℂ _ _ (borel _) μ (fun x => T φ x * starRingEnd ℂ (T φ' x)) =
            (c : ℂ) * @integral _ ℂ _ _ (borel _) μ (fun x => φ x * starRingEnd ℂ (φ' x)) := by
  first | exact @GlobalTheory.CompactOpenLattice.inner_eq_const_mul | exact GlobalTheory.CompactOpenLattice.inner_eq_const_mul | (intros; apply GlobalTheory.CompactOpenLattice.inner_eq_const_mul <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalMatrixMapInjectiveStatement
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.KSplit
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.DblScal
open scoped Matrix

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_matrix_map_injective : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
    IsCMExt F E σ → ∀ (d : ℕ) (J : Matrix (Fin d) (Fin d) E), J.det ≠ 0 →
    ∀ (v : Pl F) (t : E →ₐ[F] Fv F v) (c : GL (Fin d) (Fv F v)),
    Set.InjOn (locMatD (σ := σ) (J := J) t c) (UDAt σ J (evFin F v)) := by
  first | exact @GlobalTheory.DblScal.locMatD_injOn | exact GlobalTheory.DblScal.locMatD_injOn | (intros; apply GlobalTheory.DblScal.locMatD_injOn <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalMatrixMapSurjectiveStatement
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.KSplit
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.DblScal
open scoped Matrix

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_matrix_map_surjective : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
    IsCMExt F E σ → ∀ (d : ℕ) (J : Matrix (Fin d) (Fin d) E), J.det ≠ 0 → (∀ i j, σ (J j i) = -J i j) →
    ∀ (v : Pl F) (t : E →ₐ[F] Fv F v) (c : GL (Fin d) (Fv F v)),
    Set.SurjOn (locMatD (σ := σ) (J := J) t c) (UDAt σ J (evFin F v)) Set.univ := by
  first | exact @GlobalTheory.DblScal.locMatD_surjOn | exact GlobalTheory.DblScal.locMatD_surjOn | (intros; apply GlobalTheory.DblScal.locMatD_surjOn <;> assumption)
end

