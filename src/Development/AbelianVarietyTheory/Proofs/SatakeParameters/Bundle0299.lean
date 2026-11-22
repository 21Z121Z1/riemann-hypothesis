import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0025
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ChartBaseRepresentativePenultimateStep
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.FirstCoupledKernelEquivariantCosets
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0294
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0280
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.Bundle0002
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0176
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousOfCongSet
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0093
import Formalism.LocalToGlobal.Divisibility.DivisibilityProofs.TuplesP
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1162
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0295
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0099
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0094
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0063
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0272
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0036
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0296
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0278
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SmulCompSmul
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ChartPointRightTranslateByLevelCoupledStep
import Formalism.LocalToGlobal.KernelLattices.FirstKernelLawReading
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.FormsAre
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0297
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0139
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0266
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.XiAtCongInvariant
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0269
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0030
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0019
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0026
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0008
import Formalism.LocalToGlobal.GroupLattices.Joint0
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0014
import Formalism.LocalToGlobal.KernelLattices.TopPin
import Formalism.LocalToGlobal.KernelLattices.Bundle0001
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0027
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.TypePrimeFramesRightTranslateDifferIntegralGL

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.FirstCoupledStepDatumRationalUnitaryEquivariant
section
open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.UG Formalism.MainNotions Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV Formalism.L2.PairingIndexBounds.F Formalism.MainNotions.G.KAat Formalism.L2.Forms Formalism.MainNotions.G GlobalTheory.TwU GlobalTheory.TwV

noncomputable section

namespace GlobalTheory.CplRat

section Gen

variable {X : Fields} {Pr : Primes X} {R : Ranks}
  {sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)} {S : Set ℕ} {mu : Tup X.F X.E X.K S}
  {cst : LocCst X (rowSG Pr sel mu)} {u : Pr.Word} {j : ℕ}

open Classical in

theorem exists_pass_rat (p : ChPt (R := R) sel mu u j) (g : UF X.E (R.N j)) :
    ∃ κ : GLQ X.E (R.N j) (rowSG Pr sel mu),
      (∀ P, frsF sel mu (((g, 1, 1) : UF X.E (R.N j) × GLG X.E (R.N j) Pr.vGs × GLQ X.E (R.N j) (QE sel (mu : Chr X.F X.E X.K))) • p) P =
        g.1 * (frsF sel mu p P * ((κ P)⁻¹).1)) ∧
      (∀ P : rowSG Pr sel mu, GlobalTheory.TopStep.redGL (R.N j) P.1 (κ P) = 1) ∧ (∀ P : rowSG Pr sel mu, P.1 ∉ Pr.vGs → κ P = 1) := by
  have h : ∀ P : rowSG Pr sel mu, ∃ k : GLint X.E (R.N j) P.1,
      frsF sel mu (((g, 1, 1) : UF X.E (R.N j) × GLG X.E (R.N j) Pr.vGs × GLQ X.E (R.N j) (QE sel (mu : Chr X.F X.E X.K))) • p) P =
        g.1 * (frsF sel mu p P * (k⁻¹).1) ∧ GlobalTheory.TopStep.redGL (R.N j) P.1 k = 1 ∧ (P.1 ∉ Pr.vGs → k = 1) := by
    intro P
    by_cases hP : P.1 ∈ Pr.vGs
    · obtain ⟨κ0, h1, h2⟩ := liftFr_smul p.deco ((g, 1) : UF X.E (R.N j) × GLG X.E (R.N j) Pr.vGs) ⟨P.1, hP⟩
      have hr : GlobalTheory.TopStep.redGL (R.N j) P.1 κ0 = 1 := GlobalTheory.TopStep.redGL_eq κ0 fun x hx => by
        rw [h2 x hx]
        simp
      refine ⟨κ0⁻¹, ?_, by rw [map_inv, hr, inv_one], fun h => absurd hP h⟩
      unfold frsF
      rw [dif_pos hP, dif_pos hP, inv_inv]
      exact h1.trans (mul_assoc _ _ _)
    · refine ⟨1, ?_, map_one _, fun _ => rfl⟩
      unfold frsF
      rw [dif_neg hP, dif_neg hP]
      show g.1 * _ * (((1 : GLQ X.E (R.N j) (QE sel (mu : Chr X.F X.E X.K))) _)⁻¹).1 = _
      simp [mul_assoc]
      rfl
  choose κ hκ using h
  exact ⟨κ, fun P => (hκ P).1, fun P => (hκ P).2.1, fun P => (hκ P).2.2⟩

theorem levAt_one {n : ℕ} (Λ : LevFam X.E X.K n Pr.vGs) (Θ : LevQFam X.E X.K n (QE sel (mu : Chr X.F X.E X.K))) (P : rowSG Pr sel mu)
    (k : GLint X.E n P.1) (hr : GlobalTheory.TopStep.redGL n P.1 k = 1) (h1 : P.1 ∉ Pr.vGs → k = 1) : GlobalTheory.TopLaw.LevAt Λ Θ P k 1 := by
  refine ⟨fun hP => ?_, fun hQ hP => ?_⟩
  · have hm : GlobalTheory.TopStep.redGL n P.1 k ∈ (Λ ⟨P.1, hP⟩).H := by rw [hr]; exact one_mem _
    refine ⟨hm, ?_⟩
    rw [show (⟨_, hm⟩ : (Λ ⟨P.1, hP⟩).H) = 1 from Subtype.ext hr, map_one]
  · obtain rfl := h1 hP
    exact ⟨one_mem _, (map_one _).symm⟩

end Gen

section Cos

variable {X : Fields} {Pr : Primes X} {R : Ranks}
  {sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)} {S : Set ℕ} {mu : Tup X.F X.E X.K S}
  {cst : LocCst X (rowSG Pr sel mu)} {u : Pr.Word} {j : ℕ}

open Classical in

theorem sameCoset_pass (hX : X.Ok) (hPr : Pr.Ok) {n : ℕ} (P : rowSG Pr sel mu) (k : GLint X.E n P.1)
    (hr : GlobalTheory.TopStep.redGL n P.1 k = 1) (h1 : P.1 ∉ Pr.vGs → k = 1) (y0 : Sp X.E n)
    (hy0 : P.1 ∈ Pr.vGs → ∀ l, IntAt P.1 ((qOf P.1 : X.E) ^ 1 * y0 l)) (v : Sp X.E n) :
    SameCoset sel mu cst P (k.1 v) y0 ↔ SameCoset sel mu cst P v y0 := by
  by_cases hP : P.1 ∈ Pr.vGs
  · unfold SameCoset
    simp only [if_pos hP]
    have hk : k⁻¹ ∈ GlobalTheory.TopStep.prinCong n P.1 1 :=
      GlobalTheory.CplCosetPt.mem_prinCong_one_of_redGL (GlobalTheory.TopStep.qOf_notMem_sq hX hPr hP) _ (by rw [map_inv, hr, inv_one])
    exact GlobalTheory.CplCosetPt.sameCoset_loc P.1 0 1 1 k.1 1 k⁻¹ k.2 (one_mem _) hk (by simp) (by omega) y0 (hy0 hP)
      (fun l => by simpa using GlobalTheory.TopStep.intAt_zero) v
  · obtain rfl := h1 hP
    exact Iff.rfl

open Classical in

theorem coset_image (hX : X.Ok) (hPr : Pr.Ok) {n : ℕ} (fp fq : rowSG Pr sel mu → (Sp X.E n ≃ₗ[X.E] Sp X.E n))
    (g : Sp X.E n ≃ₗ[X.E] Sp X.E n) (κ : GLQ X.E n (rowSG Pr sel mu)) (hκ : ∀ P, fq P = g * (fp P * ((κ P)⁻¹).1))
    (hr : ∀ P : rowSG Pr sel mu, GlobalTheory.TopStep.redGL n P.1 (κ P) = 1) (h1 : ∀ P : rowSG Pr sel mu, P.1 ∉ Pr.vGs → κ P = 1)
    (y0 : rowSG Pr sel mu → Sp X.E n) (hy0 : ∀ P : rowSG Pr sel mu, P.1 ∈ Pr.vGs → ∀ l, IntAt P.1 ((qOf P.1 : X.E) ^ 1 * y0 P l)) :
    {y | ∀ P, SameCoset sel mu cst P ((fq P).symm y) (y0 P)} =
      (fun v => g v) '' {y | ∀ P, SameCoset sel mu cst P ((fp P).symm y) (y0 P)} := by
  have e : ∀ P y, (fq P).symm y = (κ P).1 ((fp P).symm (g.symm y)) := by
    intro P y
    apply (fq P).injective
    rw [LinearEquiv.apply_symm_apply, hκ P]
    show y = g (fp P (((κ P)⁻¹).1 ((κ P).1 ((fp P).symm (g.symm y)))))
    rw [Subgroup.coe_inv]
    show y = g (fp P ((κ P).1.symm ((κ P).1 ((fp P).symm (g.symm y)))))
    simp
  ext y
  simp only [Set.mem_setOf_eq, Set.mem_image, e]
  constructor
  · intro h
    refine ⟨g.symm y, fun P => (sameCoset_pass hX hPr P (κ P) (hr P) (h1 P) (y0 P) (hy0 P) _).1 (h P), by simp⟩
  · rintro ⟨z, hz, rfl⟩ P
    rw [LinearEquiv.symm_apply_apply]
    exact (sameCoset_pass hX hPr P (κ P) (hr P) (h1 P) (y0 P) (hy0 P) _).2 (hz P)

open Classical in

theorem coset_mem_ybSet (p : ChPt (R := R) sel mu u j) (y0 : rowSG Pr sel mu → Sp X.E (R.N j))
    (hy0 : ∀ (P : rowSG Pr sel mu) l, IntAt P.1 ((qOf P.1 : X.E) ^ (if P.1 ∈ Pr.vGs then 1 else cst.M) * y0 P l)) :
    {y | ∀ P, SameCoset sel mu cst P ((frsF sel mu p P).symm y) (y0 P)} ∈ ybSet sel mu cst p.deco.1.N := by
  obtain ⟨y, hy⟩ := GlobalTheory.CplCosetPt.exists_sameCoset_frames sel mu cst (frsF sel mu p) y0
  refine ⟨y, ?_, ?_⟩
  · rw [mem_locLat]
    intro P
    have hq0 : ((qOf P.1 : ℕ) : X.E) ≠ 0 := by
      have : qOf P.1 ≠ 0 := fun h0 => P.1.ne_bot (Ideal.absNorm_eq_zero_iff.1 h0)
      exact_mod_cast this
    have hqI : IntAt P.1 ((qOf P.1 : ℕ) : X.E) := by simpa using IntAt.coe P.1 ((qOf P.1 : ℕ) : 𝓞 X.E)
    rw [← (frsF sel mu p P).apply_symm_apply (_ • y), GlobalTheory.TwV.Model.frsF_mem, GlobalTheory.TopStep.mem_stdAt]
    intro l
    rw [map_smul, Pi.smul_apply, smul_eq_mul]
    have hs := hy P l
    have h0 := hy0 P l
    by_cases hP : P.1 ∈ Pr.vGs
    · simp only [if_pos hP, pow_zero, inv_one, one_mul, pow_one] at hs h0 ⊢
      simp only [_root_.zpow_neg, zpow_one, inv_inv]
      have e : ((qOf P.1 : ℕ) : X.E) * (frsF sel mu p P).symm y l =
          ((qOf P.1 : ℕ) : X.E) * ((frsF sel mu p P).symm y - y0 P) l + ((qOf P.1 : ℕ) : X.E) * y0 P l := by
        simp only [Pi.sub_apply]; ring
      rw [e]
      exact (hqI.mul hs).add h0
    · simp only [if_neg hP] at hs h0 ⊢
      simp only [_root_.zpow_neg, zpow_natCast, inv_inv]
      have e : ((qOf P.1 : ℕ) : X.E) ^ cst.M * (frsF sel mu p P).symm y l =
          (((qOf P.1 : ℕ) : X.E) ^ cst.M * ((qOf P.1 : ℕ) : X.E) ^ cst.M) *
            ((((qOf P.1 : ℕ) : X.E) ^ cst.M)⁻¹ * ((frsF sel mu p P).symm y - y0 P) l) + ((qOf P.1 : ℕ) : X.E) ^ cst.M * y0 P l := by
        simp only [Pi.sub_apply]
        field_simp
        ring
      rw [e]
      exact (((GlobalTheory.TopStep.intAt_pow hqI _).mul (GlobalTheory.TopStep.intAt_pow hqI _)).mul hs).add h0
  · ext z
    rw [Set.mem_setOf_eq, Set.mem_setOf_eq, mem_locLat]
    refine forall_congr' fun P => ?_
    rw [← GlobalTheory.TwV.Model.sameCoset_iff sel mu cst p P z y]
    exact ⟨fun h => GlobalTheory.TwV.Model.sameCoset_trans _ _ _ h (GlobalTheory.TwV.Model.sameCoset_symm _ _ _ (hy P)),
      fun h => GlobalTheory.TwV.Model.sameCoset_trans _ _ _ h (hy P)⟩

end Cos

section Main

theorem unitV_det_one {E K : Type} [Field E] [NumberField E] [StarRing E] [Field K] {n : ℕ} {P : HeightOneSpectrum (𝓞 E)}
    (χ : (𝓞 E ⧸ P.asIdeal)ˣ →* Kˣ) (k : GLint E n P) (hr : GlobalTheory.TopStep.redGL n P k = 1) :
    LocE.unitV χ ((LinearEquiv.det k.1 : Eˣ) : E) = 1 := by
  rw [GlobalTheory.TopStep.unitV_congr χ (b := 1) ?_, GlobalTheory.Mem.Col2.IdxEx.Cong.unitV_one]
  rw [(GlobalTheory.TopStep.det_glint k).2, GlobalTheory.TopStep.reduction_one₂, ← GlobalTheory.TopStep.redGL_val, hr]
  simp

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem xiPt_cpl_smul : UnderTie (fun {D L hT Gi Gl Kc Y cX ex t u μ St} A dtU a =>
    ∀ i (hi : i + 1 ≤ D.R.m), i = t.m2 → ∀ β β' (x : UA D i (Nat.le_of_succ_le hi)) (x' : UA D (i + 1) hi) p p',
      IsPtAd A a i (Nat.le_of_succ_le hi) β x p → IsPtAd A a (i + 1) hi β' x' p' →
      ∀ (g : UF t.X.E (D.R.N i)) (g' : UF t.X.E (D.R.N (i + 1))) (w : HomE t.X.E (D.R.N i) (D.R.N (i + 1))),
      xiPt A i hi β β' (((g, 1, 1) : UF t.X.E (D.R.N i) × GLG t.X.E (D.R.N i) t.Pr.vGs × GLQ t.X.E (D.R.N i) (QE t.sel (t.tup μ : Chr t.X.F t.X.E t.X.K))) • p)
        (((g', 1, 1) : UF t.X.E (D.R.N (i + 1)) × GLG t.X.E (D.R.N (i + 1)) t.Pr.vGs × GLQ t.X.E (D.R.N (i + 1)) (QE t.sel (t.tup μ : Chr t.X.F t.X.E t.X.K))) • p')
        (g'.1.toLinearMap ∘ₗ w ∘ₗ g.1.symm.toLinearMap) = xiPt A i hi β β' p p' w) := by
  intro D L hT Gi Gl Kc Y cX ex t u μ St A dtU a hPins hTie i hi hm β β' x x' p p' _ _ g g' w
  classical
  subst hm
  have hX : t.X.Ok := hPins.fields.ok
  have hPr := t.pr_ok
  have hL := t.idx_ok μ
  obtain ⟨κ, hκ, hr, h1⟩ := exists_pass_rat (R := D.R) p g
  obtain ⟨κ', hκ', hr', h1'⟩ := exists_pass_rat (R := D.R) p' g'
  have hy0 : ∀ (P : SB t μ) l, IntAt P.1 ((qOf P.1 : t.X.E) ^ (if P.1 ∈ t.Pr.vGs then 1 else (t.cst μ).M) *
      y0At A (t.m2 + 1) hi β' P l) := by
    intro P l
    have e : y0At A (t.m2 + 1) hi β' P = A.y0 β' P := by
      unfold y0At
      rw [dif_pos rfl]
    rw [e]
    exact GlobalTheory.TwU.BaseCosetInt.baseCosetRep_integral_after_scaling_at_bad_prime D L hT Gi Gl Kc Y cX ex t u μ St A dtU a hPins hTie β' P l
  have hY : cosetOf A (t.m2 + 1) hi β' p' ∈ ybSet t.sel (t.tup μ) (t.cst μ) p'.deco.1.N := coset_mem_ybSet p' _ hy0
  have hC : cosetOf A (t.m2 + 1) hi β' (((g', 1, 1) : UF t.X.E (D.R.N (t.m2 + 1)) × GLG t.X.E (D.R.N (t.m2 + 1)) t.Pr.vGs ×
      GLQ t.X.E (D.R.N (t.m2 + 1)) (QE t.sel (t.tup μ : Chr t.X.F t.X.E t.X.K))) • p') =
      (fun v => g'.1 v) '' cosetOf A (t.m2 + 1) hi β' p' :=
    coset_image hX hPr _ _ g'.1 κ' hκ' hr' h1' _ (fun P hP l => by simpa [hP] using hy0 P l)
  have hY2 : (fun v => g'.1 v) '' cosetOf A (t.m2 + 1) hi β' p' ∈ ybSet t.sel (t.tup μ) (t.cst μ)
      ((((g', 1, 1) : UF t.X.E (D.R.N (t.m2 + 1)) × GLG t.X.E (D.R.N (t.m2 + 1)) t.Pr.vGs ×
        GLQ t.X.E (D.R.N (t.m2 + 1)) (QE t.sel (t.tup μ : Chr t.X.F t.X.E t.X.K))) • p').deco.1.N) :=
    (ybSet_gmap t.sel (t.tup μ) (t.cst μ) _ g'.1 _).2 hY
  have law := GlobalTheory.CoupledLaw.xiCpl1_law (Ch := t.Ch) (L := t.idx μ) (al := A.ib t.m2 hi β)
    (b := A.ib (t.m2 + 1) (cpl_lt t μ) β') hX hPr hL hY hY2 hκ hκ' (a := fun _ => 1) (a' := fun _ => 1)
    (fun P => levAt_one _ _ P _ (hr P) (h1 P)) (fun P => levAt_one _ _ P _ (hr' P) (h1' P)) w
    (Formalism.L2.Ker.phiT_smul t.X.K p.deco p'.deco g 1 g' 1 w)
  have hprod : ∀ P : SB t μ, rhoS t.Ch t.sel (t.tup μ) t.m2 P ((LinearEquiv.det (κ⁻¹ P).1 : t.X.Eˣ) : t.X.E) *
      rhoT t.Ch t.sel (t.tup μ) t.m2 P ((LinearEquiv.det (κ'⁻¹ P).1 : t.X.Eˣ) : t.X.E) = 1 := by
    intro P
    unfold rhoS rhoT
    rw [Pi.inv_apply, Pi.inv_apply, unitV_det_one _ _ (by rw [map_inv, hr P, inv_one]),
      unitV_det_one _ _ (by rw [map_inv, hr' P, inv_one]), mul_one]
  rw [Finset.prod_eq_one fun P _ => hprod P, mul_one] at law
  simp only [Finset.prod_const_one, inv_one, mul_one, Units.val_one, one_mul] at law
  unfold xiPt
  rw [dif_neg (lt_irrefl _), if_pos rfl, dif_neg (lt_irrefl _), if_pos rfl, hC]
  exact law

end Main

end GlobalTheory.CplRat
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.KernelStepCharacterEqOneIntegralUnitary
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV GlobalTheory.TwU GlobalTheory.TwV Formalism.L2.Forms
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.TieUnr

set_option maxHeartbeats 4000000 in

theorem mt_eq_one_of_intUnit : UnderTie (fun {D L hT Gi Gl Kc Y cX ex t u μ St} A dtU a => ∀ i < D.R.m, ∀ y : (letI := D.host.cmStar; Formalism.L2.Herm.unitaryOneFiniteAdeles D.sp.cm), Matrix.GeneralLinearGroup.det y.1 ∈ intU D.host.F D.host.E → (∀ v, UnderSB t μ v → Formalism.UG.prV (E := D.host.E) v ((Matrix.GeneralLinearGroup.det y.1 : (AfE D.host.F D.host.E)ˣ) : AfE D.host.F D.host.E) = 1) → (t.O u μ).mt (i + 1) (dtU y) = 1) := by
  intro D L hT Gi Gl Kc Y cX ex t u μ St A dtU a H T i hi y hint hsupp
  classical
  letI := D.host.cmStar
  have hzU : Matrix.GeneralLinearGroup.det y.1 ∈ U1 (sigD D) := det_in_unitary_one D.host.F D.host.E (sigD D) 1 1 (by simp) y.1 y.2
  obtain ⟨x', hx'int, hx'h90, hx'supp⟩ := GlobalTheory.T.integral_h90_preimage_trivial_at_places_over_trivial D.host.F D.host.E (sigD D) (GlobalTheory.T.cmData_conj_isConjOf _ _ D.sp.cm)
    (GlobalTheory.HeckeAdjoint.unramified_host D) _ hzU hint
  set x : (AfE t.X.F t.X.E)ˣ := Units.map A.iA.symm.toRingHom.toMonoidHom x' with hxdef
  have hxx : Units.map A.iA.toRingHom.toMonoidHom x = x' := by
    ext
    simp [x]
  have hq : A.q x = dtU y := H.q_dt x y (by rw [hxx, hx'h90])
  have hcoe : ∀ w : AfE t.X.F t.X.E, A.iA w ∈ RInt D.host.F D.host.E ↔ w ∈ RInt t.X.F t.X.E := H.iA_int
  have hxint : x ∈ intU t.X.F t.X.E := by
    refine ⟨(hcoe _).1 ?_, (hcoe _).1 ?_⟩
    · simpa [x] using hx'int.1
    · simpa [x] using hx'int.2

  have hsub : ∀ {K : Type} [Field K] [NumberField K] (w : FiniteAdeleRing (𝓞 K) K) (P : HeightOneSpectrum (𝓞 K)),
      (w - 1) P = w P - 1 := fun _ _ => rfl
  have hsuppX : ∀ Q : HeightOneSpectrum (𝓞 t.X.E), (∃ P ∈ SB t μ, P.under (𝓞 t.X.F) = Q.under (𝓞 t.X.F)) →
      GlobalTheory.Mem.Col2.afIso t.X.F t.X.E (x : AfE t.X.F t.X.E) Q = 1 := by
    rintro Q ⟨P, hP, hPQ⟩
    have hxm1 : (x : AfE t.X.F t.X.E) - 1 ∈ RInt t.X.F t.X.E := sub_mem hxint.1 (one_mem _)
    have key := GlobalTheory.T.afIso_ringEquiv_eq_zero_iff t.X.F t.X.E D.host.F D.host.E t.seam.iE A.iA H.iA_rat H.iA_int _ hxm1 Q
    have e1 : A.iA ((x : AfE t.X.F t.X.E) - 1) = (x' : AfE D.host.F D.host.E) - 1 := by
      rw [map_sub, map_one]
      simp [x]
    rw [e1] at key
    have hA : GlobalTheory.Mem.Col2.afIso t.X.F t.X.E ((x : AfE t.X.F t.X.E) - 1) Q =
        GlobalTheory.Mem.Col2.afIso t.X.F t.X.E (x : AfE t.X.F t.X.E) Q - 1 := by
      rw [map_sub, map_one]; rfl
    have hB : GlobalTheory.Mem.Col2.afIso D.host.F D.host.E ((x' : AfE D.host.F D.host.E) - 1) (seamP t.seam Q) =
        GlobalTheory.Mem.Col2.afIso D.host.F D.host.E (x' : AfE D.host.F D.host.E) (seamP t.seam Q) - 1 := by
      rw [map_sub, map_one]; rfl
    rw [← sub_eq_zero, ← hA]
    refine key.1 ?_
    show GlobalTheory.Mem.Col2.afIso D.host.F D.host.E ((x' : AfE D.host.F D.host.E) - 1) (seamP t.seam Q) = 0
    rw [hB, sub_eq_zero]
    refine hx'supp _ fun R hR => ?_
    have hv : UnderSB t μ ((seamP t.seam Q).under (𝓞 D.host.F)) := by
      refine ⟨P, hP, ?_⟩
      show ((seamP t.seam Q).under (𝓞 D.host.F)).asIdeal = ((seamP t.seam P).under (𝓞 D.host.F)).asIdeal
      rw [GlobalTheory.T.columnPrimeToBasePrime_preserves_common_place D t.X t.seam t.seam_ok H.fields.ok P Q hPQ]
    exact (GlobalTheory.T.placeComponent_eq_one_iff_components_over_eq_one _ _ _ _).1 (hsupp _ hv) R hR
  have hvG : ∀ P : HeightOneSpectrum (𝓞 t.X.E), (∃ k, ((t.Pr.g k : ℕ) : 𝓞 t.X.E) ∈ P.asIdeal) →
      GlobalTheory.Mem.Col2.afIso t.X.F t.X.E (x : AfE t.X.F t.X.E) P = 1 := by
    rintro P ⟨k, hk⟩
    obtain ⟨P', hP', hu⟩ := GlobalTheory.T.exists_typePrime_under_eq t.X t.Pr H.fields.ok t.pr_ok k P hk
    refine hsuppX P ⟨P', Finset.mem_union_left _ ?_, hu⟩
    fin_cases k
    · exact Finset.mem_union_left _ hP'
    · exact Finset.mem_union_right _ hP'
  have hiso : IsAdIso (GlobalTheory.Mem.Col2.afIso t.X.F t.X.E) :=
    ⟨GlobalTheory.Mem.Col2.afIso_tmul_one _ _, GlobalTheory.Mem.Col2.mem_rInt_iff _ _⟩
  have hmu : ∀ j : Fin D.R.m, D.muTil (j.1 + 1) (A.q x) = 1 := by
    intro j
    rw [H.muTil _ hiso j (GlobalTheory.Mem.ReadEx.toIdl t.X.F t.X.E x) x (fun w => rfl) (GlobalTheory.Mem.ReadEx.toIdl_snd x).symm]
    refine Units.ext ?_
    have h1 := GlobalTheory.Mem.ReadEx.map_toIdl_eq_one (H.mu0 j).tame hxint (fun P hP => ?_)
    · rw [h1]
    · have hg : ∃ k, ((t.Pr.g k : ℕ) : 𝓞 t.X.E) ∈ P.asIdeal := by
        by_contra hc
        push_neg at hc
        exact hP ((H.mu0 j).unr P hc)
      have h2 := hvG P hg
      show Valued.v (GlobalTheory.Mem.Col2.afIso t.X.F t.X.E ((x : AfE t.X.F t.X.E) - 1) P) ≤ _
      rw [map_sub, map_one, hsub, h2, sub_self, map_zero]
      exact zero_le'
  have hxi : (t.tup μ : Chr t.X.F t.X.E t.X.K) x = 1 := by
    have hmem := (t.tup μ).2
    simp only [tupGrp, finChar, Subgroup.mem_inf] at hmem
    refine GlobalTheory.T.openCharacter_eq_one_of_integralUnit_one_at_ramified t.X.F t.X.E t.X.K t.seam.σ₀ _ hmem.1.1.1.1.2 hmem.1.1.1.1.1 x hxint fun P hP => hsuppX P ?_
    refine ⟨t.sel (P.under (𝓞 t.X.F)), Finset.mem_union_right _ ?_, ?_⟩
    · have hs : (t.sel (P.under (𝓞 t.X.F))).under (𝓞 t.X.F) = P.under (𝓞 t.X.F) :=
        GlobalTheory.TwistPlaces.under_eq_iff.2 (H.sel _)
      refine (GlobalTheory.TwistPlaces.mem_QE_iff H.sel (t.tup μ)).2 ⟨?_, ?_⟩
      · rw [hs]; exact hP
      · rw [hs]
    · exact GlobalTheory.TwistPlaces.under_eq_iff.2 (H.sel _)
  rw [← hq]
  by_cases hμ : μ = D.what₂.mu0
  · rw [(H.ref hμ).2]
    exact hmu ⟨i, hi⟩
  · obtain ⟨ξ, hξ, hmt⟩ := H.tw μ hμ rfl
    rw [hmt u, twMt, if_pos ⟨by omega, by omega⟩, MonoidHom.mul_apply, hmu ⟨i, hi⟩, one_mul, hξ x, hxi, map_one]

end GlobalTheory.TieUnr
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LastStepLocalFactorSourceLawCoupledLevelStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.DIV Formalism.L2.Col Formalism.MainNotions Formalism.L2.Ker GlobalTheory.TwU GlobalTheory.TwV GlobalTheory.TwTop GlobalTheory.TopStep
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.last_step_local_factor_source_law_coupled_level : ∀ {X : Fields} {Pr : Primes X} {R : Ranks} {Ch : Chars X Pr R.m} {sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)}
  {S : Set ℕ} {mu : Tup X.F X.E X.K S} {cst : LocCst X (rowSG Pr sel mu)} {L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K))}
  {G : ChGlob X R.m} {m2 : ℕ}, X.Ok → Pr.Ok → IsSel X sel → L.Ok Ch sel mu cst G m2 → ∀ (b : L.β (m2 + 1)) (P : rowSG Pr sel mu), P.1 ∈ Pr.vGs →
  ∀ (g : Sp X.E (R.N (m2 + 1)) ≃ₗ[X.E] Sp X.E (R.N (m2 + 1))) (z : X.K), MidLev Ch sel mu cst (m2 + 1) P (L.h (m2 + 1) b P) g z →
  ∃ Gg : GLint X.E (R.N (m2 + 1)) P.1, Gg.1 = g ∧ ∀ (k : GLint X.E (R.N (m2 + 1)) P.1), redGL _ P.1 k = redGL _ P.1 Gg →
  ∀ (y : HomE X.E (R.N (m2 + 1)) (R.N (m2 + 1 + 1))) (y' y'' : Sp X.E (R.N (m2 + 1))),
    (∀ i, IntAt P.1 ((qOf P.1 : X.E) * y' i)) → k.1 y'' - y' ∈ stdAt X.E _ P.1 →
    (PhiTopG Ch mu cst.sharp (m2 + 1) (m2 + 1 + 1) (R.N (m2 + 1 + 1)) P.1
        (prXpG X.E (R.N (m2 + 1 + 1)) ∘ₗ (y ∘ₗ k.1.toLinearMap) ∘ₗ LinearMap.funLeft X.E X.E (Fin.castAdd (cOf R (m2 + 1)))) *
      ftY sel mu cst P (atNL X.E (R.N (m2 + 1 + 1)) (R.N (m2 + 1 + 1) - 1) ∘ₗ (y ∘ₗ k.1.toLinearMap)) y'') * rhoS Ch sel mu (m2 + 1) P ((LinearEquiv.det g : X.Eˣ) : X.E) =
      z * (PhiTopG Ch mu cst.sharp (m2 + 1) (m2 + 1 + 1) (R.N (m2 + 1 + 1)) P.1
        (prXpG X.E (R.N (m2 + 1 + 1)) ∘ₗ y ∘ₗ LinearMap.funLeft X.E X.E (Fin.castAdd (cOf R (m2 + 1)))) *
      ftY sel mu cst P (atNL X.E (R.N (m2 + 1 + 1)) (R.N (m2 + 1 + 1) - 1) ∘ₗ y) y') := by
  first | exact @GlobalTheory.TopLawG.locTopG_source | exact GlobalTheory.TopLawG.locTopG_source | (intros; apply GlobalTheory.TopLawG.locTopG_source <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LastStepLocalFactorTargetLawTopLevelStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.DIV Formalism.L2.Col Formalism.MainNotions Formalism.L2.Ker GlobalTheory.TwU GlobalTheory.TwV GlobalTheory.TwTop GlobalTheory.TopStep
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.last_step_local_factor_target_law_top_level : ∀ {X : Fields} {Pr : Primes X} {R : Ranks} {Ch : Chars X Pr R.m} {sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)}
  {S : Set ℕ} {mu : Tup X.F X.E X.K S} {cst : LocCst X (rowSG Pr sel mu)} {L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K))}
  {G : ChGlob X R.m} {m2 : ℕ}, X.Ok → Pr.Ok → IsSel X sel → L.Ok Ch sel mu cst G m2 → ∀ (P : rowSG Pr sel mu), P.1 ∈ Pr.vGs →
  ∀ (g : Sp X.E (R.N (m2 + 1 + 1)) ≃ₗ[X.E] Sp X.E (R.N (m2 + 1 + 1))) (z : X.K), TopLev Ch sel mu cst (m2 + 1 + 1) P g z →
  ∃ Gg : GLint X.E (R.N (m2 + 1 + 1)) P.1, Gg.1 = g ∧ ∀ (k : GLint X.E (R.N (m2 + 1 + 1)) P.1), redGL _ P.1 k = redGL _ P.1 Gg →
  ∀ (y : HomE X.E (R.N (m2 + 1)) (R.N (m2 + 1 + 1))) (y' : Sp X.E (R.N (m2 + 1))),
    (∀ i, IntAt P.1 ((qOf P.1 : X.E) * y' i)) →
    z * (PhiTopG Ch mu cst.sharp (m2 + 1) (m2 + 1 + 1) (R.N (m2 + 1 + 1)) P.1
        (prXpG X.E (R.N (m2 + 1 + 1)) ∘ₗ ((k⁻¹).1.toLinearMap ∘ₗ y) ∘ₗ LinearMap.funLeft X.E X.E (Fin.castAdd (cOf R (m2 + 1)))) *
      ftY sel mu cst P (atNL X.E (R.N (m2 + 1 + 1)) (R.N (m2 + 1 + 1) - 1) ∘ₗ ((k⁻¹).1.toLinearMap ∘ₗ y)) y') * rhoT Ch sel mu (m2 + 1) P ((LinearEquiv.det g : X.Eˣ) : X.E) =
      (PhiTopG Ch mu cst.sharp (m2 + 1) (m2 + 1 + 1) (R.N (m2 + 1 + 1)) P.1
        (prXpG X.E (R.N (m2 + 1 + 1)) ∘ₗ y ∘ₗ LinearMap.funLeft X.E X.E (Fin.castAdd (cOf R (m2 + 1)))) *
      ftY sel mu cst P (atNL X.E (R.N (m2 + 1 + 1)) (R.N (m2 + 1 + 1) - 1) ∘ₗ y) y') := by
  first | exact @GlobalTheory.TwTop.topF_target_vG | exact GlobalTheory.TwTop.topF_target_vG | (intros; apply GlobalTheory.TwTop.topF_target_vG <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.PairKernelLawOfFiniteDatumLawStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker Formalism.L2.Forms Formalism.L2.Col Formalism.L2.DIV Formalism.HermitianLatticesTheory GlobalTheory.KerJ NumberField IsDedekindDomain Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pairKernelLaw_of_finiteDatumLaw : ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : G.Inst D L) (Gl : G.LatInst D) (K : G.Consts) (Y : DivX D) (cX : ExtraC) (ex : Extra D L hT Gi Gl K Y cX) (t : KerEntTied ex), t.X.Ok → IsSel t.X t.sel → (∀ i, t.Pr.g i ∈ t.S) → (∀ v, t.Pr.T v ∈ t.S) → (∀ l ∈ D.host.small, l ∈ t.S) → D.host.q ∈ t.S → (∃ eta, t.Ch.Tied t.glob.σ₀ (fun j τ => (D.hc (t.seam.iT τ)).e j) t.glob.mu0 eta) → ∀ u μ i, i < D.R.m → ∀ (c : (D.chTw u μ).cls i) (c' : (D.chTw u μ).cls (i + 1)) (γ : UF t.X.E (D.R.N (i + 1))) (k : t.X.K), gmap γ.1 ((t.rd u μ).N (i + 1) c') = (t.rd u μ).N (i + 1) c' → (∀ x, ∀ z ∈ mulLat (t.rd u μ).lev (homAt (t.rd u μ).SS ((t.rd u μ).N i c) ((t.rd u μ).N (i + 1) c')), (t.rd u μ).Xi i c c' (x + z) = (t.rd u μ).Xi i c c' x) → (∀ x, (t.rd u μ).Xi i c c' (γ.1.toLinearMap ∘ₗ x) * t.seam.σ₀ (∏ P : rowSG t.Pr t.sel (t.tup μ), muAt t.Ch t.sel (t.tup μ) (t.cst μ) i P ((LinearEquiv.det γ.1 : t.X.Eˣ) : t.X.E)) = t.seam.σ₀ k * (t.rd u μ).Xi i c c' x) → TermLaw (t.O u μ) i c c' (matE t.seam γ.1, t.seam.σ₀ k) := by
  first | exact @GlobalTheory.KFiDat.termLaw_of_xi | exact GlobalTheory.KFiDat.termLaw_of_xi | (intros; apply GlobalTheory.KFiDat.termLaw_of_xi <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.PrincipalCongruenceSubgroupMemLevelTwistPrimeStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV GlobalTheory.TwU GlobalTheory.TwV
open scoped TensorProduct
open GlobalTheory.TopStep
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.principal_congruence_subgroup_mem_level_twist_prime : ∀ {X : Fields} {Pr : Primes X} {R : Ranks} {Ch : Chars X Pr R.m}
    {sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)} {S : Set ℕ} {mu : Tup X.F X.E X.K S}
    {cst : LocCst X (rowSG Pr sel mu)} {L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K))} {G : ChGlob X R.m} {m2 : ℕ},
    X.Ok → Pr.Ok → L.Ok Ch sel mu cst G m2 → ∀ {j : ℕ}, j ≤ m2 → ∀ (b : L.β j) (P : rowSG Pr sel mu), P.1 ∉ Pr.vGs →
    ∀ C : GLint X.E (R.N j) P.1, C ∈ GlobalTheory.TopStep.prinCong (R.N j) P.1 (cst.D P) →
    ∃ r ∈ Loc.Cbe (Jat (Pr := Pr) cst.sharp j P.1) (L.h j b P),
      (∀ x, r (Loc.inX X.E (R.N j) (cOf R j) x) = Loc.inX X.E (R.N j) (cOf R j) (C.1 x)) ∧
        chiInv Ch sel mu cst j P (L.h j b P) r = 1 := by
  first | exact @GlobalTheory.TwistCong.cong_mem_prCat_twist | exact GlobalTheory.TwistCong.cong_mem_prCat_twist | (intros; apply GlobalTheory.TwistCong.cong_mem_prCat_twist <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.RowFormsMatchPeriodMapOfFurtherPropertiesStatement
section
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rowFormsMatchPeriodMap_of_furtherProperties : ∀ (K : Ctx) (B : GlobalTheory.Mem.Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T) (Z : w.Lt) (Wt : Set B.places.Pl) (p0 : BaseLevelRowSide (w.D Z)) (t : RowsT K w Z Wt p0), RX K B f T w Z Wt p0 t → ∀ a, GlobalTheory.AtG.RowPin w.I w.ok w.l Z a := by
  first | exact @GlobalTheory.AtG.RX.rowPin_of_rx | exact GlobalTheory.AtG.RX.rowPin_of_rx | (intros; apply GlobalTheory.AtG.RX.rowPin_of_rx <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.TrueColumnTupleKernelsRationalStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix GlobalTheory.TwU GlobalTheory.TwU.AtTrue
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.trueColumnTupleKernels_rational : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (l0 : I.Law0 l) (Tw : TwForms (I.rec7 l Z)), ColIn.JetsIn I → Tw = I.tw l l0 Z → ∀ (u : B.Word) (a : I.ι) j, j < B.R.m → (Tw.fm u a).KRat j := by
  first | exact @GlobalTheory.TwU.AtTrue.tuple_kernels_rational | exact GlobalTheory.TwU.AtTrue.tuple_kernels_rational | (intros; apply GlobalTheory.TwU.AtTrue.tuple_kernels_rational <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.TrueKernelJetsMulDetCharactersMemCoefficientFielStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.trueKernelJets_mul_detCharacters_mem_coefficientField : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ColIn.JetsIn I → ∀ (u : B.Word) (a : I.ι) (i : ℕ), i < B.R.m → ∀ (c : (I.stp u a i).Cl) (c' : (I.stp u a (i + 1)).Cl) (e : DVar B.fields.Tau (B.R.N i) (B.R.N (i + 1)) →₀ ℕ), (∀ τ, (monoDeg e τ : ℤ) = nuDeg B u i τ) → ∃ k : B.LL, B.embLL k = (I.rho u a i c.1 ((I.stp u a i).rep c) * I.rho' u a i c'.1 ((I.stp u a (i + 1)).rep c')) * jetC I.J.cD (I.th u a i c.1 c'.1 ((I.stp u a i).rep c) ((I.stp u a (i + 1)).rep c')) e := by
  first | exact @GlobalTheory.Mem.Col2.TC.rho_jet_mem | exact GlobalTheory.Mem.Col2.TC.rho_jet_mem | (intros; apply GlobalTheory.Mem.Col2.TC.rho_jet_mem <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.TuplesLocalModelsOfOtherDivisionLatticesHeights
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Ker Formalism.L2.Forms GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Fc GlobalTheory.Svd NumberField IsDedekindDomain

namespace GlobalTheory.Svd

set_option maxHeartbeats 800000 in

theorem modelsAt_tr : ∀ (D : D7) (O : Obj D) (N : ∀ u, Submodule (𝓞 D.what₂.LL) (D.div.Nu u).V) (h : D.what₂.Word → ℝ),
    ModelsAt D O → ModelsAt (setDiv D N h) (O.tr N h) := by
  intro D O N h H hT hk
  obtain ⟨h0, LC, hLC⟩ := H hT hk
  refine ⟨h0, LC, fun μ hμ u w hg hq => ?_⟩
  obtain ⟨c1, c2⟩ := hLC μ hμ u w hg hq
  exact ⟨GlobalTheory.T.latticeChainComparison_indep_divisionLattices D N h _ _ u μ w hg _ _ _ c1, GlobalTheory.T.siteAdmissible_indep_divisionLattices D N h u w hg _ _ _ c2⟩

end GlobalTheory.Svd
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.TypePrimeFramesRightTranslateDifferIntegralGLStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.DIV Formalism.L2.Col Formalism.MainNotions Formalism.L2.Ker GlobalTheory.TwU GlobalTheory.TwV GlobalTheory.TwTop GlobalTheory.TopStep
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.type_prime_frames_right_translate_differ_integral_GL : UnderTie (fun {D L hT Gi Gl Kc Y cX ex t u μ St} A dtU a =>
  ∀ (i : ℕ) (hi : i ≤ D.R.m) (β : (St i hi).Ch) (x x₁ : UA D i hi) (κ : ((St i hi).K β).lev.U),
    x₁.1 = x.1 * κ.1 → ∀ p p₁, IsPtAd A a i hi β x p → IsPtAd A a i hi β x₁ p₁ →
    ∀ (P : SB t μ), P.1 ∈ t.Pr.vGs → ∀ (dep : SB t μ → ℕ), dep P = 1 → ∀ (Gg : GLint t.X.E (D.R.N i) P.1),
      InFrame t.seam (A.fb i hi β) dep P κ.1 Gg.1 →
      ∃ k : GLint t.X.E (D.R.N i) P.1, frsF t.sel (t.tup μ) p₁ P = frsF t.sel (t.tup μ) p P * k.1 ∧
        redGL _ P.1 k = redGL _ P.1 Gg) := by
  first | exact @GlobalTheory.LevFrame.frame_lev | exact GlobalTheory.LevFrame.frame_lev | (intros; apply GlobalTheory.LevFrame.frame_lev <;> assumption)
end

