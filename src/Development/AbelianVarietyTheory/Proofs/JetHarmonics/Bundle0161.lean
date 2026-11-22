import Mathlib
import Formalism.HermitianCurvature.Bundle0007
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0208
import Formalism.HermitianCurvature.HermitianCurvatureProofs.OpApplyContinuousOn
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0160
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0115
import Formalism.LocalToGlobal.ProjectiveLattices.ThShort
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import Development.AbelianVarietyTheory.Definitions.Jets.Bundle0002
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0214
import Development.AbelianVarietyTheory.Definitions.Jets.Bundle0003
import Formalism.HermitianCurvature.Bundle0004

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.CutoffCompactApproximantsConvergeDecayClass
section
open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants Filter Topology MeasureTheory

namespace GlobalTheory

theorem cutF_approximants_ccle :
    ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (Bs : B.RealPlaceData k r Wp Wq) (χ : ℝ → ℝ) (f : B.Mat k r → (Wq →L[ℂ] Wp)) (A₀ ε A : ℝ) (mm : ℕ), C6.IsCut0 χ → 0 < ε → B.CkOn ⊤ (B.GV k r) f → (∀ m : ℕ, B.InCC A₀ m f) → A + 1 + 2 * ((r : ℝ) + 1) * (mm : ℝ) ≤ A₀ → ∃ K : ℝ, 0 ≤ K ∧ B.CCle A mm (D.cutF Bs χ f ε) K ∧ ∀ n : ℕ, B.CCle A mm ((fun g : B.Mat k r => ((Real.smoothTransition ((4 - ∑ i, ∑ j, Complex.normSq ((((n : ℝ) + 1)⁻¹ • g) i j)) / 3) : ℝ) : ℂ) • D.cutF Bs χ f ε g)) K ∧ B.CCle A mm ((fun g : B.Mat k r => ((Real.smoothTransition ((4 - ∑ i, ∑ j, Complex.normSq ((((n : ℝ) + 1)⁻¹ • g) i j)) / 3) : ℝ) : ℂ) • D.cutF Bs χ f ε g) - (D.cutF Bs χ f ε)) (K / ((n : ℝ) + 1)) := by
  intro k r Wp Wq _ _ _ _ _ _ Bs χ f A₀ ε A mm hχ hε _ hfA hA
  obtain ⟨b, hb⟩ := Formalism.FourierDecayAlt.P.PBE.cutF_inCC Bs hχ hfA hε (A + 1) mm hA
  generalize D.cutF Bs χ f ε = H at hb ⊢
  have hb0 : 0 ≤ b := Formalism.FourierDecayAlt.P.JCx2.pd_ccle_nonneg hb
  have hb' : B.CCle A mm H b := Formalism.FourierDecayAlt.P.BetaSesquilinearity.CCle_mono_A (by linarith) hb
  obtain ⟨Kp, hKp0, hKp⟩ := Formalism.FourierDecayAlt.P.JCx2.pd_cut_ccle (k := k) (r := r) (E := Wq →L[ℂ] Wp) mm
  have hψ : ∀ n : ℕ, B.CCle A mm (fun g => Formalism.FourierDecayAlt.P.JCx2.pdPsi ((n : ℝ) + 1) g • H g)
      (Kp * b / ((n : ℝ) + 1)) := fun n => by
    have h := hKp ((n : ℝ) + 1) (by positivity) (A + 1) H b hb
    rwa [add_sub_cancel_right] at h
  have hc : ∀ (n : ℕ) (g : B.Mat k r), ((Real.smoothTransition
      ((4 - ∑ i, ∑ j, Complex.normSq ((((n : ℝ) + 1)⁻¹ • g) i j)) / 3) : ℝ) : ℂ)
        = 1 - Formalism.FourierDecayAlt.P.JCx2.pdPsi ((n : ℝ) + 1) g := fun n g =>
    Formalism.FourierDecayAlt.P.PBE.cut_eq (fun (n : ℕ) (g : B.Mat k r) => ((Real.smoothTransition
      ((4 - ∑ i, ∑ j, Complex.normSq ((((n : ℝ) + 1)⁻¹ • g) i j)) / 3) : ℝ) : ℂ)) (fun _ _ => rfl) n g
  have hKb : 0 ≤ Kp * b := mul_nonneg hKp0 hb0
  refine ⟨b + Kp * b, by positivity, Formalism.FourierDecayAlt.P.JCx2.pd_ccle_mono_c hb' (by linarith), fun n => ⟨?_, ?_⟩⟩
  · have e : (fun g : B.Mat k r => ((Real.smoothTransition
        ((4 - ∑ i, ∑ j, Complex.normSq ((((n : ℝ) + 1)⁻¹ • g) i j)) / 3) : ℝ) : ℂ) • H g)
          = fun g => H g + (-1 : ℂ) • (Formalism.FourierDecayAlt.P.JCx2.pdPsi ((n : ℝ) + 1) g • H g) := by
      funext g
      rw [hc n g, sub_smul, one_smul, neg_one_smul, sub_eq_add_neg]
    rw [e]
    refine Formalism.FourierDecayAlt.P.JCx2.pd_ccle_mono_c
      (Formalism.FourierDecayAlt.P.BetaSesquilinearity.CCle_add hb' (Formalism.FourierDecayAlt.P.BetaSesquilinearity.CCle_smul (-1) (hψ n))) ?_
    have h1 : Kp * b / ((n : ℝ) + 1) ≤ Kp * b := div_le_self hKb (by
      have : (0 : ℝ) ≤ n := Nat.cast_nonneg n; linarith)
    simp only [norm_neg, norm_one, one_mul]
    linarith
  · have e : ((fun g : B.Mat k r => ((Real.smoothTransition
        ((4 - ∑ i, ∑ j, Complex.normSq ((((n : ℝ) + 1)⁻¹ • g) i j)) / 3) : ℝ) : ℂ) • H g) - H)
          = fun g => (-1 : ℂ) • (Formalism.FourierDecayAlt.P.JCx2.pdPsi ((n : ℝ) + 1) g • H g) := by
      funext g
      rw [Pi.sub_apply, hc n g, sub_smul, one_smul, neg_one_smul, sub_sub_cancel_left]
    rw [e]
    refine Formalism.FourierDecayAlt.P.JCx2.pd_ccle_mono_c (Formalism.FourierDecayAlt.P.BetaSesquilinearity.CCle_smul (-1) (hψ n)) ?_
    simp only [norm_neg, norm_one, one_mul]
    exact div_le_div_of_nonneg_right (by linarith) (by positivity)

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.MarkedLatticeIsometryDoubleCosetMoveStatement
section
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi
open scoped TensorProduct
open GlobalTheory.ShortMove
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.markedLattice_isometry_double_coset_move : ∀ (D : D7) (V : HSp D) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (r : ℕ) (hr : V.rank = r) (io : Dw.La →ₗ[𝓞 D.host.E] (Fin V.rank → D.host.E)) (X X' : Data D.host.E r) (A A' : Datum H) (φ : A.La ≃ₗ[𝓞 D.host.E] X.Λ) (φ' : A'.La ≃ₗ[𝓞 D.host.E] X'.Λ) (t : Dw.La →ₗ[𝓞 D.host.E] A.La) (t' : Dw.La →ₗ[𝓞 D.host.E] A'.La) (s : Dw.La →ₗ[𝓞 D.host.E] Dw.La) (h γ κ : GA D V), ModelW V hr X → ModelW V hr X' → (∀ a b, ((A.EF a b : ℤ) : ℚ) = Algebra.trace ℚ D.host.E (-X.ξ0 * herm X.Gm (φ a : Fin r → D.host.E) (φ b))) → (∀ a b, ((A'.EF a b : ℤ) : ℚ) = Algebra.trace ℚ D.host.E (-X'.ξ0 * herm X'.Gm (φ' a : Fin r → D.host.E) (φ' b))) → γ ∈ GQ V → latGHat V κ = latGHat V 1 → (∀ a, ∃ w ∈ latGHat V 1, (finHom V κ).1.mulVec (finVec V (io a)) = finVec V (io (s a)) + l.M • w) → Marked V hr io l X.Λ (fun a => (φ (t a) : Fin r → D.host.E)) h → Marked V hr io l X'.Λ (fun a => (φ' (t' a) : Fin r → D.host.E)) (γ * h * κ) → ∃ gam : A.La ≃ₗ[𝓞 D.host.E] A'.La, (∀ a b, A'.EF (gam a) (gam b) = A.EF a b) ∧ ∀ a ∈ Mfr l • (⊤ : Submodule (𝓞 D.host.E) Dw.La), ∃ x, gam (t (s a)) = t' a + l.M • x := by
  first | exact @GlobalTheory.ShortMoveIso.marked_isometry | exact GlobalTheory.ShortMoveIso.marked_isometry | (intros; apply GlobalTheory.ShortMoveIso.marked_isometry <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.PointwiseBoundedRadialOpsClosureAndFunctions
section
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr Formalism.REAL Formalism.QuantumDeterminants MeasureTheory GlobalTheory.HatNF

namespace GlobalTheory.HatNF.PtBBasic

open Formalism.FourierDecayAlt.P.TLB

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

theorem nv_of_mulAt {P : M.Par} {Bs : B.RealPlaceData P.k P.r Wp Wq} {x : (Fin P.r → ℂ) × Q.Mx P.k P.r}
    {T : Module.End ℂ (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π')} {s : ℂ} (h : MulAt x T s)
    (Φ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') : nv (T Φ) x = ‖s‖ * nv Φ x := by
  unfold nv
  rw [h Φ, ← norm_smul]
  rfl

theorem nv_nonneg {P : M.Par} {Bs : B.RealPlaceData P.k P.r Wp Wq} (Φ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π')
    (x : (Fin P.r → ℂ) × Q.Mx P.k P.r) : 0 ≤ nv Φ x := norm_nonneg _

theorem ptB_of_mulAt {P : M.Par} {Bs : B.RealPlaceData P.k P.r Wp Wq} (b : RA P Bs) (C : ℝ) (hC : 0 ≤ C)
    (h : ∀ x ∈ Q.DomR P.k P.r Bs.z Bs.z', ∃ s : ℂ, MulAt x b.1 s ∧ ‖s‖ ≤ C) : PtB P Bs b := by
  refine ⟨C, hC, fun Φ x hx => ?_⟩
  obtain ⟨s, hs, hle⟩ := h x hx
  rw [nv_of_mulAt hs]
  exact mul_le_mul_of_nonneg_right hle (nv_nonneg Φ x)

theorem ptB_mul {P : M.Par} {Bs : B.RealPlaceData P.k P.r Wp Wq} (a b : RA P Bs) (ha : PtB P Bs a) (hb : PtB P Bs b) :
    PtB P Bs (a * b) := by
  obtain ⟨C, hC, ha⟩ := ha
  obtain ⟨C', hC', hb⟩ := hb
  refine ⟨C * C', mul_nonneg hC hC', fun Φ x hx => ?_⟩
  rw [pr_mul_fst, Module.End.mul_apply, mul_assoc]
  exact (ha _ x hx).trans (mul_le_mul_of_nonneg_left (hb Φ x hx) hC)

theorem norm_ratio_le (a b : ℂ) (h : ‖a‖ = ‖b‖) : ‖a * b⁻¹‖ ≤ 1 := by
  rw [norm_mul, norm_inv, h]
  exact mul_inv_le_one

theorem sqrt_lt_zeta {P : M.Par} (Bs : B.RealPlaceData P.k P.r Wp Wq) {x : (Fin P.r → ℂ) × Q.Mx P.k P.r}
    (hx : x ∈ Q.DomR P.k P.r Bs.z Bs.z') :
    Real.sqrt (Tz P.k P.r Bs.z * Tz P.k P.r Bs.z') < ‖Q.zetaL P.k P.r Bs.z Bs.z' (Fin.last P.r) x.2‖ := by
  have h := hx.2.2
  unfold Q.GGl at h
  rw [Complex.normSq_eq_norm_sq] at h
  have hn := norm_nonneg (Q.zetaL P.k P.r Bs.z Bs.z' (Fin.last P.r) x.2)
  rw [← Real.sqrt_sq hn]
  exact Real.sqrt_lt_sqrt (mul_pos Bs.T_pos Bs.T'_pos).le (by linarith)

end GlobalTheory.HatNF.PtBBasic

namespace GlobalTheory.HatNF

open Formalism.FourierDecayAlt.P.TLB PtBBasic

theorem ptB_basic : ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq) (X : Q.ActualOps P.k P.r Bs.z Bs.z' Bs.π Bs.π') (μ : Measure (Mt P.k P.r)) (L : LevelData (RA P Bs) P.r) (st : Start (RA P Bs)) (l0 : ℕ) (d : Q.NFData P (RA P Bs)), P5.IsData P Bs.z Bs.z' Bs.π Bs.π' X μ L st l0 → IsNF X d → (PtB P Bs 1 ∧ (∀ a b, PtB P Bs a → PtB P Bs b → PtB P Bs (a * b))) ∧ PtB P Bs d.L.ζi ∧ PtB P Bs d.L.ζbi ∧ PtB P Bs (d.L.D * d.L.Dbi) ∧ PtB P Bs (d.L.Db * d.L.Di) ∧ PtB P Bs (d.L.Drb * d.L.Dri) ∧ PtB P Bs (d.L.Dr * d.L.Drbi) ∧ ∀ (Φ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π'), ∀ x ∈ Q.DomR P.k P.r Bs.z Bs.z', 0 < dR P Bs x.1 x.2 ∧ 0 < gR P Bs x.1 x.2 ∧ nv (d.L.Di.1 Φ) x = (dR P Bs x.1 x.2)⁻¹ * nv Φ x ∧ nv ((TL.gI d.L).1 Φ) x = (gR P Bs x.1 x.2)⁻¹ * nv Φ x := by
  intro Wp Wq _ _ _ _ _ _ Pa Bs X μ L0 st l0 d _ hd
  have hL := hd.1
  set L := d.L with hLdef
  have hDr : ∀ x, MulAt x L.Dr.1 (∏ a, x.1 a) := fun x =>
    mulAt_ofFn L.c _ fun l => act_c X L hL x l
  have hDri : ∀ x, MulAt x L.Dri.1 (∏ a, x.1 a)⁻¹ := fun x => by
    rw [← Finset.prod_inv_distrib]
    exact mulAt_ofFn L.ci _ fun l => act_ci X L hL x l
  have hDrb : ∀ x, MulAt x L.Drb.1 (star (∏ a, x.1 a)) := fun x => by
    rw [star_prod]
    exact mulAt_ofFn L.cb _ fun l => act_cb X L hL x l
  have hDrbi : ∀ x, MulAt x L.Drbi.1 (star (∏ a, x.1 a))⁻¹ := fun x => by
    rw [star_prod, ← Finset.prod_inv_distrib]
    exact mulAt_ofFn L.cbi _ fun l => act_cbi X L hL x l
  have hz : ∀ x ∈ Q.DomR Pa.k Pa.r Bs.z Bs.z', MulAt x L.ζ.1 (Q.zetaL Pa.k Pa.r Bs.z Bs.z' (Fin.last Pa.r) x.2) := by
    intro x hx; rw [hL.2.2.2.2.2.2.1]; exact act_fn X x hx 0
  have hzi : ∀ x ∈ Q.DomR Pa.k Pa.r Bs.z Bs.z',
      MulAt x L.ζi.1 (Q.zetaL Pa.k Pa.r Bs.z Bs.z' (Fin.last Pa.r) x.2)⁻¹ := by
    intro x hx; rw [hL.2.2.2.2.2.2.2.1]; exact act_fn X x hx 1
  have hzb : ∀ x ∈ Q.DomR Pa.k Pa.r Bs.z Bs.z',
      MulAt x L.ζb.1 (star (Q.zetaL Pa.k Pa.r Bs.z Bs.z' (Fin.last Pa.r) x.2)) := by
    intro x hx; rw [hL.2.2.2.2.2.2.2.2.1]; exact act_fn X x hx 2
  have hzbi : ∀ x ∈ Q.DomR Pa.k Pa.r Bs.z Bs.z',
      MulAt x L.ζbi.1 (star (Q.zetaL Pa.k Pa.r Bs.z Bs.z' (Fin.last Pa.r) x.2))⁻¹ := by
    intro x hx; rw [hL.2.2.2.2.2.2.2.2.2.1]; exact act_fn X x hx 3
  have hGGi : ∀ x ∈ Q.DomR Pa.k Pa.r Bs.z Bs.z',
      MulAt x L.GGi.1 ((Q.GGl Pa.k Pa.r Bs.z Bs.z' x.2 : ℂ))⁻¹ := by
    intro x hx; rw [hL.2.2.2.2.2.2.2.2.2.2.2.1]; exact act_fn X x hx 5
  have hD : ∀ x ∈ Q.DomR Pa.k Pa.r Bs.z Bs.z',
      MulAt x L.D.1 ((∏ a, x.1 a) * Q.zetaL Pa.k Pa.r Bs.z Bs.z' (Fin.last Pa.r) x.2) :=
    fun x hx => mulAt_mul (hDr x) (hz x hx)
  have hDb : ∀ x ∈ Q.DomR Pa.k Pa.r Bs.z Bs.z',
      MulAt x L.Db.1 (star ((∏ a, x.1 a) * Q.zetaL Pa.k Pa.r Bs.z Bs.z' (Fin.last Pa.r) x.2)) := by
    intro x hx
    rw [star_mul']
    exact mulAt_mul (hDrb x) (hzb x hx)
  have hDi : ∀ x ∈ Q.DomR Pa.k Pa.r Bs.z Bs.z',
      MulAt x L.Di.1 ((∏ a, x.1 a) * Q.zetaL Pa.k Pa.r Bs.z Bs.z' (Fin.last Pa.r) x.2)⁻¹ := by
    intro x hx
    rw [mul_inv, mul_comm]
    exact mulAt_mul (hzi x hx) (hDri x)
  have hDbi : ∀ x ∈ Q.DomR Pa.k Pa.r Bs.z Bs.z',
      MulAt x L.Dbi.1 (star ((∏ a, x.1 a) * Q.zetaL Pa.k Pa.r Bs.z Bs.z' (Fin.last Pa.r) x.2))⁻¹ := by
    intro x hx
    rw [star_mul', mul_inv, mul_comm]
    exact mulAt_mul (hzbi x hx) (hDrbi x)
  have hsq : 0 < Real.sqrt (Tz Pa.k Pa.r Bs.z * Tz Pa.k Pa.r Bs.z') :=
    Real.sqrt_pos.2 (mul_pos Bs.T_pos Bs.T'_pos)
  refine ⟨⟨?_, ptB_mul⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact ptB_of_mulAt _ 1 zero_le_one fun x _ => ⟨1, mulAt_one x, by simp⟩
  · refine ptB_of_mulAt _ _ (inv_pos.2 hsq).le fun x hx => ⟨_, hzi x hx, ?_⟩
    rw [norm_inv]
    exact inv_anti₀ hsq (sqrt_lt_zeta Bs hx).le
  · refine ptB_of_mulAt _ _ (inv_pos.2 hsq).le fun x hx => ⟨_, hzbi x hx, ?_⟩
    rw [norm_inv, norm_star]
    exact inv_anti₀ hsq (sqrt_lt_zeta Bs hx).le
  · exact ptB_of_mulAt _ 1 zero_le_one fun x hx =>
      ⟨_, mulAt_mul (hD x hx) (hDbi x hx), norm_ratio_le _ _ (norm_star _).symm⟩
  · exact ptB_of_mulAt _ 1 zero_le_one fun x hx =>
      ⟨_, mulAt_mul (hDb x hx) (hDi x hx), norm_ratio_le _ _ (norm_star _)⟩
  · exact ptB_of_mulAt _ 1 zero_le_one fun x _ =>
      ⟨_, mulAt_mul (hDrb x) (hDri x), norm_ratio_le _ _ (norm_star _)⟩
  · exact ptB_of_mulAt _ 1 zero_le_one fun x _ =>
      ⟨_, mulAt_mul (hDr x) (hDrbi x), norm_ratio_le _ _ (norm_star _).symm⟩
  · intro Φ x hx
    have hc : (∏ a, x.1 a) ≠ 0 := Finset.prod_ne_zero_iff.2 fun a _ => hx.1 a
    have hζ : Q.zetaL Pa.k Pa.r Bs.z Bs.z' (Fin.last Pa.r) x.2 ≠ 0 :=
      norm_pos_iff.1 (hsq.trans (sqrt_lt_zeta Bs hx))
    have hG := hx.2.2
    refine ⟨norm_pos_iff.2 (mul_ne_zero hc hζ), mul_pos (Complex.normSq_pos.2 hc) hG, ?_, ?_⟩
    · rw [nv_of_mulAt (hDi x hx), norm_inv]
      rfl
    · have h : MulAt x (TL.gI L).1 _ := mulAt_mul (mulAt_mul (hDri x) (hDrbi x)) (hGGi x hx)
      rw [nv_of_mulAt h]
      congr 1
      unfold gR
      rw [norm_mul, norm_mul, norm_inv, norm_inv, norm_inv, norm_star, Complex.norm_real, Real.norm_of_nonneg hG.le,
        Complex.normSq_eq_norm_sq, sq, mul_inv, mul_inv]

end GlobalTheory.HatNF
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.RadialPictureSmulCutoffGMultiplierStatement
section
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr Formalism.REAL Formalism.QuantumDeterminants MeasureTheory GlobalTheory.HatNF
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.radial_picture_smul_cutoff_G_multiplier : ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq), ∀ (φ : ℝ → ℝ) (f : B.Mat P.k P.r → (Wq →L[ℂ] Wp)), (ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ → LE.SmoothLog φ ∧ (KB.CptCoef Bs f → KB.CptCoef Bs (mulG Bs φ f))) ∧ ∀ (W : ℕ → Module.End ℂ (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π')) (Φ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π'), IsMulG P Bs φ W → Top.IsRadOf P Bs Φ f → Top.IsRadOf P Bs (W 0 Φ) (mulG Bs φ f) := by
  first | exact @GlobalTheory.HatNF.radial_mulG | exact GlobalTheory.HatNF.radial_mulG | (intros; apply GlobalTheory.HatNF.radial_mulG <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.TopVectorAddSmulCompactCoefficientsStatement
section
open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.TopVec Filter Topology MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.topVector_add_smul_compactCoefficients : ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq) (Cb : ℝ) (a : ℂ) (H₁ H₂ : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (w : List C.Letter) (c : Fin (P.r + 1) → ℂ), KB.InDDplus2 P p.l0 p.T.base Cb p.Θ → KB.CutWord P p.l0 w → KB.CptCoef p.T.base H₁ → KB.CptCoef p.T.base H₂ → tv p (H₁ + a • H₂) w c = tv p H₁ w c + a • tv p H₂ w c := by
  first | exact @GlobalTheory.TopVec.tv_add_smul | exact GlobalTheory.TopVec.tv_add_smul | (intros; apply GlobalTheory.TopVec.tv_add_smul <;> assumption)
end

