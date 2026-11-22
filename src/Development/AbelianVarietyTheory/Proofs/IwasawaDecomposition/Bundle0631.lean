import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FlagComponentFramedPointFrame
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0024
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0010
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0568
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0596
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0605
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0604
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0576
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0592
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0594
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0609
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.KeyFamOne
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.Bundle0003
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle0025
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle0008
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle0037
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle0046
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0109
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0094
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0051
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0114
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0058
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.LawsFieldsSeparately
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0029
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AffineOpenChartCompStructureEqSpMap
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0607
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsPullbackOfNormalFlatProj
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0617
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0601

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsKeySectionUnif
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj GlobalTheory.ShFam GlobalTheory.LamT
open GlobalTheory.FrameUnif GlobalTheory.Reg
open scoped Matrix TensorProduct

namespace GlobalTheory.KeyFourth

theorem exists_eq_smul_pow {K : Type} [Field K] [Algebra K ℂ] {A : Type} [CommRing A] [Algebra K A]
    [Algebra.Smooth K A] [IsDomain (ℂ ⊗[K] A)] {n : ℕ} (hn : 0 < n) (u : Aˣ) {C : ℂ} (hC : C ≠ 0)
    (ρ : (A →ₐ[K] ℂ) → ℂ)
    (hρ : ∀ (m : ℕ) (V : Set (Fin m → ℂ)) (s : (Fin m → ℂ) → (A →ₐ[K] ℂ)), IsOpen V →
      (∀ a : A, DifferentiableOn ℂ (fun p => s p a) V) → ContinuousOn (fun p => ρ (s p)) V)
    (hu : ∀ ψ : A →ₐ[K] ℂ, ρ ψ ^ n = C * ψ (u : A)) : ∃ (a : K) (b : A), a ≠ 0 ∧ (u : A) = a • b ^ n := by
  haveI : Nontrivial A := by
    by_contra h
    rw [not_nontrivial_iff_subsingleton] at h
    exact not_subsingleton (ℂ ⊗[K] A) inferInstance
  let res : (ℂ ⊗[K] A →ₐ[ℂ] ℂ) → (A →ₐ[K] ℂ) := fun χ =>
    (χ.restrictScalars K).comp Algebra.TensorProduct.includeRight
  let u' : (ℂ ⊗[K] A)ˣ := Units.map (algebraMap ℂ (ℂ ⊗[K] A) : ℂ →* _) (Units.mk0 C hC) *
    Units.map ((Algebra.TensorProduct.includeRight : A →ₐ[K] ℂ ⊗[K] A) : A →* _) u
  have hu' : (u' : ℂ ⊗[K] A) = C ⊗ₜ[K] (u : A) := by
    simp [u', Algebra.TensorProduct.algebraMap_apply]
  obtain ⟨w, hw⟩ := GlobalTheory.T.exists_pow_eq_unit_of_continuous_complex_root (ℂ ⊗[K] A) n u' (fun χ => ρ (res χ)) hn
    (fun m V s hV hs => hρ m V (fun p => res (s p)) hV fun a => hs _) (fun χ => by
      rw [hu, hu']
      have : C ⊗ₜ[K] (u : A) = C • ((1 : ℂ) ⊗ₜ[K] (u : A)) := by
        rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      rw [this, map_smul, smul_eq_mul]
      rfl)
  exact GlobalTheory.T.exists_base_field_multiple_of_nth_root_complexification K A n w C u hn hC u.ne_zero (hw.trans hu')

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H} {Xo : Moduli Dw l} {c : Coeff l}

theorem keySec_of_generic (h : GenFrEx Xo c) (b : ∀ Z : Comp Xo c, Om Z) (hb0 : ∀ Z, b Z ≠ 0)
    (hb : ∀ C : FChart h, ((kch C.t : (Om C.Z)ˣ) : Om C.Z) * b C.Z ∈ C.R ∧
      (((kch C.t : (Om C.Z)ˣ) : Om C.Z) * b C.Z)⁻¹ ∈ C.R) : Nonempty (KeySec Xo c) := by
  obtain ⟨hL, -, -, hA⟩ := evLaws_genFr_atlas E H Dw l Xo c
  obtain ⟨f, hf, hfb⟩ := GlobalTheory.T.exists_integer_exponent_section_of_chart_regular E H Dw l Xo c h (keyEx Dw) b fun C => (hb C).1
  obtain ⟨f', hf', hfb'⟩ := GlobalTheory.T.exists_integer_exponent_section_of_chart_regular E H Dw l Xo c h (-keyEx Dw) (fun Z => (b Z)⁻¹) fun C => by
    have := (hb C).2
    rw [mul_inv, ← Units.val_inv_eq_inv_val] at this
    simpa only [kch, Pi.neg_apply, zpow_neg, Finset.prod_inv_distrib] using this
  have h0 : GlobalTheory.AllWt.secZ Xo c 0 = sec Xo c 0 0 := by
    rw [← GlobalTheory.AllWt.secZ_nat]
    congr 1
    funext i
    cases i <;> rfl
  have hm := GlobalTheory.AllWt.mul_mem_secZ hf hf'
  rw [add_neg_cancel, h0] at hm
  have h1 := GlobalTheory.AllWt.one_mem_secZ (Xo := Xo) (c := c)
  rw [h0] at h1
  have hff : f * f' = 1 := by
    refine sub_eq_zero.1 (sec_eq_zero_of_generic_values E H Dw l Xo c hL h (hA h) 0 0 _ (sub_mem hm h1) fun Z => ?_)
    have e₁ : evC h Z (f * f') = evC h Z f * evC h Z f' := by simp only [evC, evR, evalAt_mul]
    have e₂ : evC h Z (1 : Rul Xo c) = 1 := evalAt_one _ _ _ (hL.test _ _)
    have e₃ := (evalL (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) (genFr h Z)).map_sub
      (f * f') 1
    refine e₃.trans ?_
    change evC h Z (f * f') - evC h Z 1 = 0
    rw [e₁, e₂, hfb, hfb', mul_inv_cancel₀ (hb0 Z), sub_self]
  exact ⟨⟨⟨f, f', hff, (mul_comm _ _).trans hff⟩, hf⟩⟩

theorem exists_chart_units {κ : GlobalTheory.KeyCl.Rule} (h₁ : GlobalTheory.KeyCl.Homog (fun _ => 1) κ) (h₂ : GlobalTheory.KeyCl.Funct κ)
    (h₃ : GlobalTheory.KeyCl.FamUnit κ) {g : ℕ} (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ)) (hpq : 1 ≤ Dw.p + Dw.q)
    (h : GenFrEx Xo c) : ∃ v : ∀ Z : Comp Xo c, (Om Z)ˣ, ∀ C : FChart h,
      ∃ (Φ : FibKey Xo C.R C.y.x) (u : (C.R)ˣ), Tied e C.y.s C.y.u Φ ∧ GlobalTheory.KeyCl.IsValue κ Φ.key (u : C.R) ∧
        ((u : C.R) : Om C.Z) = ((kch C.t ^ 4 * v C.Z : (Om C.Z)ˣ) : Om C.Z) := by
  have hc : ∀ Z : Comp Xo c, CharZero (Om Z) := fun Z =>
    charZero_of_injective_algebraMap (algebraMap c.F (Om Z)).injective
  choose Ψ hΨ using fun Z : Comp Xo c => GlobalTheory.T.exists_universalTripleFibre_at_framedPoint E H Dw l Xo c g e (Om Z) (genFr h Z) hpq
  refine ⟨fun Z => κ (Om Z) (Ψ Z).key, fun C => ?_⟩
  haveI := C.sm
  haveI : IsIntegrallyClosed C.R := isIntegrallyClosed_of_smooth c.F C.R
  haveI : IsNoetherianRing C.R := Algebra.FiniteType.isNoetherianRing c.F C.R
  haveI : CharZero C.R := charZero_of_injective_algebraMap (algebraMap c.F C.R).injective
  obtain ⟨Φ, hΦ⟩ := GlobalTheory.T.exists_universalTripleFibre_at_framedPoint E H Dw l Xo c g e C.R C.y hpq
  obtain ⟨Φ', hΦ'⟩ := GlobalTheory.T.exists_universalTripleFibre_at_framedPoint E H Dw l Xo c g e (Om C.Z) C.yg hpq
  obtain ⟨u, hu⟩ := h₃ C.R Φ.key
  refine ⟨Φ, u, hΦ, hu, ?_⟩
  rw [← GlobalTheory.T.theta_key_rule_triangular_frame_change_fourth_power κ h₁ h₂ E H Dw l Xo c g e (Om C.Z) C.t _ _ (Ψ C.Z) Φ' C.bor (hΨ _) hΦ']
  exact (hu (Om C.Z) _ _ (GlobalTheory.T.universal_triple_fibres_base_change_key_data E H Dw l Xo c g e _ _ C.R.val C.y C.yg Φ Φ' C.gen hΦ hΦ')).symm

theorem rule_eq_of_rootVal {κ : GlobalTheory.KeyCl.Rule} (h₁ : GlobalTheory.KeyCl.Homog (fun _ => 1) κ) (h₂ : GlobalTheory.KeyCl.Funct κ)
    (h₃ : GlobalTheory.KeyCl.ThetaOne κ) {σ : c.F →+* ℂ} {g : ℕ} {e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ)}
    {F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom)
      (fun j => Formalism.L2.PjFree.relab c σ (e j).1)} {r : ℕ} {M : ModelsOf F r} (T : ∀ k, ThetaData e F M k)
    {un : ∀ k, (M.X k).dom → FrPt Xo c (CAt σ)} (hun : ∀ k, IsNormUn (T k) (un k)) (hpq : 1 ≤ Dw.p + Dw.q)
    {N : ℂ} (hN : N ≠ 0) (hNk : ∀ k, (normConst (fun j => Formalism.L2.PjFree.relab c σ (e j).1) (M.X k).ξ0 : ℂ) = N)
    {y : FrPt Xo c (CAt σ)} {v : ℂ} (hv : RootVal (unfOf e F M un) y v) (Φ : FibKey Xo ℂ y.x)
    (hΦ : Tied (S := ℂ) e y.s y.u Φ) :
    v ^ 4 = (N / (2 * Real.pi * Complex.I) ^ g) ^ 4 * (κ ℂ Φ.key : ℂ) := by
  obtain ⟨k, x, t, ht, rfl⟩ : ∃ (k : Fin F.n) (x : (M.X k).dom) (t : Ix Dw → (CAt σ)ˣ), FrBor t (un k x) y ∧
    v = Formalism.L2.PjFree.toC ((kch t : (CAt σ)ˣ) : CAt σ) := hv
  obtain ⟨Ψ, hΨ⟩ : ∃ Ψ : FibKey Xo ℂ (un k x).x, Tied (S := ℂ) e (un k x).s (un k x).u Ψ :=
    @GlobalTheory.T.exists_universalTripleFibre_at_framedPoint E _ _ _ H Dw l Xo c g e ℂ _ _ σ.toAlgebra (un k x) hpq
  have e₁ : κ ℂ Φ.key = kch (S := ℂ) t ^ 4 * κ ℂ Ψ.key :=
    @GlobalTheory.T.theta_key_rule_triangular_frame_change_fourth_power κ h₁ h₂ E _ _ _ H Dw l Xo c g e ℂ _ _ σ.toAlgebra t (un k x) y Ψ Φ ht hΨ hΦ
  obtain ⟨a, ha, hy⟩ := hun k x
  have hb : (T k).co.symm x.1 ∈ (T k).co ⁻¹' (M.X k).dom := by
    show (T k).co ((T k).co.symm x.1) ∈ (M.X k).dom
    rw [(T k).co.apply_symm_apply]; exact x.2
  have d1 := ((T k).norm _ hb).1.ne_zero
  rw [hNk] at ha
  have a0 : a ≠ 0 := fun h0 => mul_ne_zero hN d1 (by rw [← ha, h0]; simp)
  have e₂ := GlobalTheory.T.theta_key_rule_value_at_theta_point κ h₁ h₃ E H Dw l Xo c σ g e F r M k (T k) _ hb a (un k x) Ψ a0 hy hΨ
  have e₃ : N ^ 4 * (κ ℂ Ψ.key : ℂ) = ((2 * Real.pi * Complex.I) ^ g) ^ 4 := by
    refine mul_right_cancel₀ (pow_ne_zero 4 d1) ?_
    rw [show a ^ 8 = (a ^ 2) ^ 4 by ring, ha] at e₂
    linear_combination e₂
  have hπ : ((2 * Real.pi * Complex.I : ℂ) ^ g) ^ 4 ≠ 0 :=
    pow_ne_zero _ (pow_ne_zero _ Complex.two_pi_I_ne_zero)
  have e₄ : (κ ℂ Φ.key : ℂ) = Formalism.L2.PjFree.toC ((kch t : (CAt σ)ˣ) : CAt σ) ^ 4 * (κ ℂ Ψ.key : ℂ) := by
    rw [e₁]
    rfl
  rw [e₄, div_pow, mul_left_comm, div_mul_eq_mul_div, e₃, div_self hπ, mul_one]

set_option maxHeartbeats 1000000 in

theorem nonempty_keySec : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (N : ℕ) (U : Formalism.L2.PjFree.Unf Xo c σ N), Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf U → (∀ k, (U.X k).dom.Nonempty) → (∀ k la γ, (U.X k).χ la γ = 1) → FnAlgClosed Xo c → 2 ≤ N → 2 < Module.finrank ℚ E / 2 → Nonempty (KeySec Xo c) := by
  intro E _ _ _ H Dw l Xo c σ N U hσ hU _ _ hF hN _
  obtain ⟨hr, -, -, -, -, g, e, F, -⟩ := hU
  have hpq : 1 ≤ Dw.p + Dw.q := by omega
  have hB : Out.SecBaseChangeSt := GlobalTheory.lawsFieldsSeparately.2.1
  have hT : Out.SecTwistSt := GlobalTheory.abelianSchemeLaws_all.2.secTwist
  obtain ⟨ξ₀, hcc, hne, him⟩ := GlobalTheory.IsUnfEx.exists_xi H
  have hcc' : cc (-ξ₀) = -(-ξ₀) := by
    unfold cc at hcc ⊢
    rw [map_neg, hcc]
  obtain ⟨Gm, φ, hφ⟩ := GlobalTheory.exists_herm_coord_of_datum E H Dw (-ξ₀) hcc' (neg_ne_zero.2 hne) (Dw.p + Dw.q) rfl
  obtain ⟨M, hM, hξ, hMG⟩ := GlobalTheory.ModelsExist.exists_modelsOf GlobalTheory.QNorm.hasseNormSt E H Dw l Xo _ _ _ F _ ξ₀ Gm φ
    hcc him hφ
  have T : ∀ k, ThetaData e F M k := fun k => (GlobalTheory.T.nonempty_thetaData_flagDomainModels E H Dw l Xo c σ g e F _ M hσ hM hξ k).some
  choose un hun using fun k => GlobalTheory.T.exists_normalisedFramedPoint_on_each_component hT E H Dw l Xo c σ g e F _ M k (T k)
  have hok : FramesOK e F M un :=
    ⟨fun k => GlobalTheory.T.normalised_points_satisfy_single_frame hT E H Dw l Xo c σ g e F _ M k (T k) (un k) hσ hM hξ (hun k),
      fun k => GlobalTheory.T.normalisedFramedPoint_triangularFrame_weightRule hT E H Dw l Xo c σ g e F _ M un k (T k) hσ hM hξ (hun k),
      fun k => GlobalTheory.T.normalisedFramedPoint_arithmeticGroup_invariant_sign hT E H Dw l Xo c σ g e F _ M un k (T k) hσ hM hξ (hun k),
      fun a n han f hf k => GlobalTheory.T.differentiableOn_readings_normalised_theta_points hB hT E H Dw l Xo c σ g e F _ M un k (T k) (hun k) a n han f hf⟩
  have hU₀ := isUnf_built hB E H Dw l Xo c σ g e F _ M un hσ hM hξ hok
  have hC : (normConst (fun j => Formalism.L2.PjFree.relab c σ (e j).1) ξ₀ : ℂ) ≠ 0 := by
    rw [Complex.ofReal_ne_zero]
    refine (Real.sqrt_pos.2 (div_pos (by positivity) (Finset.prod_pos fun j _ => ?_))).ne'
    have : Formalism.L2.PjFree.relab c σ (e j).1 ξ₀ ≠ 0 := (map_ne_zero _).2 hne
    positivity
  obtain ⟨κ, k₁, k₂, -, k₃, -, k₄, -⟩ := GlobalTheory.KeyFamClosing.keyFam_one
  obtain ⟨hL, -, h, hA⟩ := evLaws_genFr_atlas E H Dw l Xo c
  obtain ⟨v, hv⟩ := exists_chart_units k₁ k₂ k₄ e hpq h
  have hroot : ∀ C : FChart h, ∃ (a : c.F) (b : C.R), a ≠ 0 ∧
      ((kch C.t ^ 4 * v C.Z : (Om C.Z)ˣ) : Om C.Z) = a • (b : Om C.Z) ^ 4 := by
    intro C
    obtain ⟨Φ, u, hΦ, hu, huv⟩ := hv C
    letI : Algebra c.F ℂ := σ.toAlgebra
    haveI := C.sm
    haveI := GlobalTheory.GeomConn.isDomain_tensor C.R.val Subtype.val_injective (hF C.Z) ℂ
    choose z hz using fun ψ : C.R →ₐ[c.F] CAt σ => hL.bc _ _ ψ C.y
    have hex : ∀ ψ, ∃ w, RootVal (unfOf e F M un) (z ψ) w := fun ψ => by
      obtain ⟨k, x, t, ht⟩ := hU₀.2.2.1 (z ψ)
      exact ⟨_, k, x, t, ht, rfl⟩
    choose ρ hρ using hex
    obtain ⟨a, b, ha, hab⟩ := exists_eq_smul_pow (K := c.F) (A := C.R) (n := 4) (by norm_num) u
      (pow_ne_zero 4 (div_ne_zero hC (pow_ne_zero g Complex.two_pi_I_ne_zero))) ρ
      (fun m V s hV hs => GlobalTheory.T.continuousOn_keySection_complexValue E H Dw l Xo c σ g e F _ M T un hσ hM hξ hun hok C.R C.y m V s
        (fun p => z (s p)) (fun p => ρ (s p)) hV hs (fun p _ => hz _) fun p _ => hρ _)
      (fun ψ => by
        obtain ⟨Ψ, hΨ⟩ : ∃ Ψ : FibKey Xo ℂ (z ψ).x, Tied (S := ℂ) e (z ψ).s (z ψ).u Ψ :=
          @GlobalTheory.T.exists_universalTripleFibre_at_framedPoint E _ _ _ H Dw l Xo c g e ℂ _ _ σ.toAlgebra (z ψ) hpq
        exact (rule_eq_of_rootVal k₁ k₂ k₃ T hun hpq hC (fun k => by rw [(hMG k).2]) (hρ ψ) Ψ hΨ).trans
          (congrArg _ (hu ℂ _ _
            (@GlobalTheory.T.universal_triple_fibres_base_change_key_data E _ _ _ H Dw l Xo c g e _ ℂ _ _ _ _ σ.toAlgebra ψ C.y (z ψ) Φ Ψ (hz ψ) hΦ hΨ))))
    exact ⟨a, b, ha, by rw [← huv, hab]; rfl⟩
  have hgen : ∀ Z : Comp Xo c, ∃ (a : c.F) (b : Om Z), a ≠ 0 ∧ (v Z : Om Z) = a • b ^ 4 := by
    intro Z
    obtain ⟨C, ψ, z, t, h1, h2⟩ := hA h (Om Z) (genFr h Z)
    obtain rfl := GlobalTheory.Reg.SecGlue.chart_comp Z C ψ z t h1 h2
    obtain ⟨a, b, ha, hab⟩ := hroot C
    refine ⟨a, b / ((kch C.t : (Om C.Z)ˣ) : Om C.Z), ha, ?_⟩
    rw [div_pow, ← smul_div_assoc, ← hab, Units.val_mul, Units.val_pow_eq_pow_val,
      mul_div_cancel_left₀ _ (pow_ne_zero 4 (kch C.t).ne_zero)]
  choose a b ha hab using hgen
  have hb0 : ∀ Z, b Z ≠ 0 := fun Z h0 => (v Z).ne_zero (by rw [hab, h0]; simp)
  refine keySec_of_generic h b hb0 fun C => ?_
  obtain ⟨-, u, -, -, huv⟩ := hv C
  haveI := C.sm
  haveI : IsIntegrallyClosed C.R := isIntegrallyClosed_of_smooth c.F C.R
  haveI := GlobalTheory.SupGeneric.isFractionRing_chart C
  have hint : ∀ (x : Om C.Z) (y : C.R), x ^ 4 = y → x ∈ C.R := fun x y hxy => by
    have hi : IsIntegral C.R (x ^ 4) := hxy ▸ isIntegral_algebraMap (R := C.R) (x := y)
    obtain ⟨w, hw⟩ := IsIntegrallyClosed.exists_algebraMap_eq_of_isIntegral_pow (by norm_num : 0 < 4) hi
    exact hw ▸ w.2
  have hc : ∀ (x : c.F) (y : C.R), ((algebraMap c.F C.R x * y : C.R) : Om C.Z) = x • (y : Om C.Z) := fun x y => by
    rw [Algebra.smul_def]
    rfl
  have e₁ : (((kch C.t : (Om C.Z)ˣ) : Om C.Z) * b C.Z) ^ 4 = (a C.Z)⁻¹ • ((u : C.R) : Om C.Z) := by
    rw [huv, Units.val_mul, Units.val_pow_eq_pow_val, hab, mul_smul_comm, smul_smul,
      inv_mul_cancel₀ (ha _), one_smul, mul_pow]
  refine ⟨hint _ _ (e₁.trans (hc _ _).symm),
    hint _ (algebraMap c.F C.R (a C.Z) * ((u⁻¹ : (C.R)ˣ) : C.R)) ?_⟩
  rw [inv_pow, e₁, hc]
  refine inv_eq_of_mul_eq_one_right ?_
  rw [smul_mul_smul_comm, inv_mul_cancel₀ (ha _), one_smul, ← Subalgebra.coe_mul, Units.mul_inv]
  rfl

end GlobalTheory.KeyFourth
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsModelOfAtlas
section
open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LocM GlobalTheory.LieMet GlobalTheory.DRFlag
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.FlagMod (ev tau tau_le spMap_ev ev_res ev_spMap le_preimage_inf le_preimage_map le_preimage_mono le_preimage_comp tanPull initSpan mem_initSpan)

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.DRFlag.ToMdl

theorem exists_chart_iso {X' Y : Scheme.{0}} {R : Type} [CommRing R] (χ : Sp R ⟶ Y) [IsOpenImmersion χ]
    (g : Y ⟶ X') [IsIso g] : ∃ θ : R ≃+* Γ(X', (χ ≫ g).opensRange),
      spMap θ.toRingHom ≫ χ ≫ g = (isAffineOpen_opensRange (χ ≫ g)).fromSpec := by
  let hU := isAffineOpen_opensRange (χ ≫ g)
  let k := IsOpenImmersion.isoOfRangeEq hU.fromSpec (χ ≫ g) (by rw [hU.range_fromSpec]; simp)
  have hg : Spec.map (Spec.preimage k.hom) = k.hom := Spec.map_preimage _
  have hi : IsIso (Spec.map (Spec.preimage k.hom)) := by rw [hg]; infer_instance
  have hi' : IsIso (Spec.preimage k.hom) := by
    have : IsIso (Scheme.Spec.map (Spec.preimage k.hom).op) := hi
    have := isIso_of_reflects_iso (Spec.preimage k.hom).op Scheme.Spec
    exact isIso_of_op _
  refine ⟨(asIso (Spec.preimage k.hom)).commRingCatIsoToRingEquiv, ?_⟩
  change Spec.map (Spec.preimage k.hom) ≫ _ = _
  rw [hg]
  exact IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _

theorem range_comp_inv {X X' T : Scheme.{0}} (e : X' ≅ X) (f : T ⟶ X) :
    Set.range (f ≫ e.inv) = e.hom ⁻¹' Set.range f := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    exact ⟨y, by rw [← Scheme.Hom.comp_apply, Category.assoc, e.inv_hom_id, Category.comp_id]⟩
  · rintro ⟨y, hy⟩
    refine ⟨y, ?_⟩
    rw [Scheme.Hom.comp_apply, hy, ← Scheme.Hom.comp_apply, e.hom_inv_id]
    rfl

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {Xo : ∀ l : Level H, Moduli Dw l} {p : ℕ} {W : ValuationSubring ℂ} {Y : LocalSystem Xo p W} {i : Idx H p}
  {X : Scheme.{0}} {π : X ⟶ (Y i).X} {ty : (E →+* ℂ) → Finset ℕ} (A : Atlas (Y i) π ty)

def chartNum : A.ch.ι ≃ Fin (Nat.card A.ch.ι) := Finite.equivFin _

def chartOpen {X' : Scheme.{0}} (e : X' ≅ X) (a : A.ch.ι) : X'.affineOpens :=
  ⟨(A.ch.χ a ≫ e.inv).opensRange, isAffineOpen_opensRange _⟩

def chartEquiv {X' : Scheme.{0}} (e : X' ≅ X) (a : A.ch.ι) : A.ch.R a ≃+* Γ(X', (chartOpen A e a).1) :=
  (exists_chart_iso (A.ch.χ a) e.inv).choose

theorem fromSpec_hom {X' : Scheme.{0}} (e : X' ≅ X) (a : A.ch.ι) :
    (chartOpen A e a).2.fromSpec ≫ e.hom = spMap (chartEquiv A e a).toRingHom ≫ A.ch.χ a := by
  have h := congrArg (· ≫ e.hom) (exists_chart_iso (A.ch.χ a) e.inv).choose_spec
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id] at h
  exact h.symm

variable (i₀ : Idx H p) (hl : i₀.l.Dvd i.l) (hc : i₀.c.F ≤ i.c.F) {n : ℕ} (I : (PSpace (i.c.V W) n).IdealSheafData)
  (e : I.subscheme ≅ X)

def pre : Pre Y i₀ where
  i := i
  dvd := hl
  le := hc
  n := n
  I := I
  π := e.hom ≫ π
  ty := ty
  m := Nat.card A.ch.ι
  U b := chartOpen A e ((chartNum A).symm b)
  alg b := (chartEquiv A e ((chartNum A).symm b)).toRingHom.comp (A.alg ((chartNum A).symm b))
  fr b := (A.fr ((chartNum A).symm b)).bc (chartEquiv A e ((chartNum A).symm b)).toRingHom

theorem pre_flagAt_iff {k : Type} [Field k] (w : Sp k ⟶ I.subscheme) (u : Vecs Dw (Y i).t k) :
    (pre A i₀ hl hc I e).FlagAt w u ↔ A.FlagAt (w ≫ e.hom) u := by
  change (∃ (b : Fin (Nat.card A.ch.ι)) (φ : Γ(I.subscheme, (chartOpen A e ((chartNum A).symm b)).1) →+* k),
      spMap φ ≫ (chartOpen A e ((chartNum A).symm b)).2.fromSpec = w ∧
      IsFrame (Y i).t (φ.comp ((chartEquiv A e ((chartNum A).symm b)).toRingHom.comp (A.alg ((chartNum A).symm b)))) (w ≫ e.hom ≫ π) u ∧
      SameFlag ty (Y i).t (w ≫ e.hom ≫ π) (((A.fr ((chartNum A).symm b)).bc (chartEquiv A e ((chartNum A).symm b)).toRingHom).bc φ) u) ↔
    ∃ (a : A.ch.ι) (φ : A.ch.R a →+* k), spMap φ ≫ A.ch.χ a = w ≫ e.hom ∧
      IsFrame (Y i).t (φ.comp (A.alg a)) ((w ≫ e.hom) ≫ π) u ∧ SameFlag ty (Y i).t ((w ≫ e.hom) ≫ π) ((A.fr a).bc φ) u
  constructor
  · rintro ⟨b, φ, h1, h2, h3⟩
    refine ⟨_, φ.comp (chartEquiv A e ((chartNum A).symm b)).toRingHom, ?_, ?_, ?_⟩
    · rw [← h1, Category.assoc, fromSpec_hom, ← Category.assoc, GlobalTheory.LocM.Recode.spMap_comp_eq]
    · rw [Category.assoc, RingHom.comp_assoc]; exact h2
    · rw [Category.assoc, ← GlobalTheory.LocM.Recode.bc_bc]; exact h3
  · rintro ⟨a, φ, h1, h2, h3⟩
    obtain ⟨b, rfl⟩ := (chartNum A).symm.surjective a
    have hφ : (φ.comp (chartEquiv A e ((chartNum A).symm b)).symm.toRingHom).comp (chartEquiv A e ((chartNum A).symm b)).toRingHom = φ := by
      ext x; simp
    refine ⟨b, φ.comp (chartEquiv A e ((chartNum A).symm b)).symm.toRingHom, ?_, ?_, ?_⟩
    · rw [← cancel_mono e.hom, Category.assoc, fromSpec_hom, ← Category.assoc, GlobalTheory.LocM.Recode.spMap_comp_eq, hφ, h1]
    · rw [← RingHom.comp_assoc, hφ, ← Category.assoc]; exact h2
    · rw [GlobalTheory.LocM.Recode.bc_bc, hφ, ← Category.assoc]; exact h3

end GlobalTheory.DRFlag.ToMdl

namespace GlobalTheory.DRFlag.ToMdl

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {Xo : ∀ l : Level H, Moduli Dw l} {p : ℕ} {W : ValuationSubring ℂ} {Y : LocalSystem Xo p W} {i : Idx H p}
  {X : Scheme.{0}} {π : X ⟶ (Y i).X} {ty : (E →+* ℂ) → Finset ℕ} (A : Atlas (Y i) π ty)
  (i₀ : Idx H p) (hl : i₀.l.Dvd i.l) (hc : i₀.c.F ≤ i.c.F) {n : ℕ} (I : (PSpace (i.c.V W) n).IdealSheafData)
  (e : I.subscheme ≅ X)

def mdl (hs : e.hom ≫ π ≫ (Y i).s = I.subschemeι ≫ PSpace.str _ n) (g : Geo (Y i) π) : Mdl Y i₀ where
  toPre := pre A i₀ hl hc I e
  π_s := by
    change (e.hom ≫ π) ≫ (Y i).s = I.subschemeι ≫ PSpace.str _ n
    rw [Category.assoc, hs]
  normal := by
    have hn₀ : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme I.subscheme := by
      intro x
      obtain ⟨h1, h2⟩ := g.normal (e.hom x)
      let φ := (asIso (e.hom.stalkMap x)).commRingCatIsoToRingEquiv
      exact ⟨φ.symm.toMulEquiv.isDomain _, IsIntegrallyClosed.of_equiv φ⟩
    exact GlobalTheory.IsNormalScheme.of_pred hn₀
  flat := by
    change Flat (I.subschemeι ≫ PSpace.str _ n)
    rw [← hs]
    have := g.flat
    infer_instance
  dense := by
    change Dense ((e.hom ≫ π) ⁻¹' Set.range (Y i).j)
    exact g.dense.preimage (f := ⇑e.hom) e.hom.isOpenEmbedding.isOpenMap
  cover := by
    change ⋃ b, (((A.ch.χ ((chartNum A).symm b) ≫ e.inv).opensRange : I.subscheme.Opens) : Set I.subscheme) =
      (e.hom ≫ π) ⁻¹' Set.range (Y i).j
    simp only [Scheme.Hom.coe_opensRange, range_comp_inv]
    rw [(chartNum A).symm.surjective.iUnion_comp (fun a => e.hom ⁻¹' Set.range (A.ch.χ a)), ← Set.preimage_iUnion]
    change e.hom ⁻¹' A.ch.carrier = _
    rw [A.cover]
    rfl
  alg_s b := by
    change (chartOpen A e _).2.fromSpec ≫ I.subschemeι ≫ PSpace.str _ n = _
    rw [← hs, ← Category.assoc, fromSpec_hom, Category.assoc, A.alg_s, GlobalTheory.LocM.Recode.spMap_comp_eq]
    rfl
  smooth b := by
    change Smooth ((chartOpen A e _).2.fromSpec ≫ e.hom ≫ π)
    rw [← Category.assoc, fromSpec_hom, Category.assoc]
    have := A.smooth ((chartNum A).symm b)
    have : IsIso (spMap (chartEquiv A e ((chartNum A).symm b)).toRingHom) := by
      have : IsIso (CommRingCat.ofHom (chartEquiv A e ((chartNum A).symm b)).toRingHom) :=
        (chartEquiv A e ((chartNum A).symm b)).toCommRingCatIso.isIso_hom
      infer_instance
    infer_instance
  frame b := by
    change IsFrame (Y i).t ((chartEquiv A e ((chartNum A).symm b)).toRingHom.comp (A.alg _))
      ((chartOpen A e _).2.fromSpec ≫ e.hom ≫ π) ((A.fr _).bc (chartEquiv A e ((chartNum A).symm b)).toRingHom)
    rw [← Category.assoc, fromSpec_hom, Category.assoc]
    exact GlobalTheory.LocM.isFrame_bc _ _ _ _ _ _ _ _ _ _ _ _ _ (A.frame _)
  glue k _ := by
    change ∀ (b b' : Fin (Nat.card A.ch.ι)) (φ : Γ(I.subscheme, (chartOpen A e ((chartNum A).symm b)).1) →+* k)
      (φ' : Γ(I.subscheme, (chartOpen A e ((chartNum A).symm b')).1) →+* k),
      spMap φ ≫ (chartOpen A e ((chartNum A).symm b)).2.fromSpec = spMap φ' ≫ (chartOpen A e ((chartNum A).symm b')).2.fromSpec →
      SameFlag ty (Y i).t (spMap φ ≫ (chartOpen A e ((chartNum A).symm b)).2.fromSpec ≫ e.hom ≫ π)
        (((A.fr _).bc (chartEquiv A e ((chartNum A).symm b)).toRingHom).bc φ) (((A.fr _).bc (chartEquiv A e ((chartNum A).symm b')).toRingHom).bc φ')
    intro b b' φ φ' h
    have h' : spMap (φ.comp (chartEquiv A e ((chartNum A).symm b)).toRingHom) ≫ A.ch.χ ((chartNum A).symm b) =
        spMap (φ'.comp (chartEquiv A e ((chartNum A).symm b')).toRingHom) ≫ A.ch.χ ((chartNum A).symm b') := by
      rw [← GlobalTheory.LocM.Recode.spMap_comp_eq, ← GlobalTheory.LocM.Recode.spMap_comp_eq, Category.assoc, Category.assoc,
        ← fromSpec_hom, ← fromSpec_hom, ← Category.assoc, ← Category.assoc, h]
    have hp : spMap φ ≫ (chartOpen A e ((chartNum A).symm b)).2.fromSpec ≫ e.hom ≫ π =
        spMap (φ.comp (chartEquiv A e ((chartNum A).symm b)).toRingHom) ≫ A.ch.χ ((chartNum A).symm b) ≫ π := by
      rw [← GlobalTheory.LocM.Recode.spMap_comp_eq]
      simp only [Category.assoc]
      rw [← Category.assoc (spMap (chartEquiv A e ((chartNum A).symm b)).toRingHom) (A.ch.χ _) π, ← fromSpec_hom]
      simp only [Category.assoc]
    rw [GlobalTheory.LocM.Recode.bc_bc, GlobalTheory.LocM.Recode.bc_bc, hp]
    exact A.glue k _ _ _ _ h'
  bij k _ := by
    change ∀ (f : i.c.F →+* k) (y : Sp k ⟶ (Xo i.l).XF i.c), y ≫ pullback.snd _ _ = spMap f →
      ∀ u, IsFrame (Y i).t f (y ≫ (Y i).j) u →
        ∃! w : Sp k ⟶ I.subscheme, w ≫ e.hom ≫ π = y ≫ (Y i).j ∧ (pre A i₀ hl hc I e).FlagAt w u
    intro f y hy u hu
    obtain ⟨w, ⟨hw1, hw2⟩, hw3⟩ := A.bij k f y hy u hu
    refine ⟨w ≫ e.inv, ⟨?_, ?_⟩, fun w' ⟨h1, h2⟩ => ?_⟩
    · rw [Category.assoc, Iso.inv_hom_id_assoc]; exact hw1
    · refine (pre_flagAt_iff A i₀ hl hc I e _ u).2 ?_
      rw [Category.assoc, Iso.inv_hom_id, Category.comp_id]
      exact hw2
    · have := hw3 (w' ≫ e.hom) ⟨by rw [Category.assoc, h1], (pre_flagAt_iff A i₀ hl hc I e w' u).1 h2⟩
      rw [← this, Category.assoc, Iso.hom_inv_id, Category.comp_id]

end GlobalTheory.DRFlag.ToMdl

namespace GlobalTheory.DRFlag

namespace ToMdl

theorem comp_hom_comp {X' X X₂ T Z : Scheme.{0}} (w : T ⟶ X') (e : X' ≅ X) (f : X ⟶ X₂) (π₂ : X₂ ⟶ Z) (π : X ⟶ Z)
    (hf : f ≫ π₂ = π) : (w ≫ e.hom ≫ f) ≫ π₂ = w ≫ (e.hom ≫ π) ≫ 𝟙 Z := by
  simp [hf]

theorem of_assoc {X' X X₂ T : Scheme.{0}} (w : T ⟶ X') (e : X' ≅ X) (f : X ⟶ X₂) (P : (T ⟶ X₂) → Prop)
    (h : P ((w ≫ e.hom) ≫ f)) : P (w ≫ e.hom ≫ f) := by
  rwa [Category.assoc] at h

end ToMdl

theorem exists_mdl_of_atlas : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (Xo : ∀ l : Level H, Moduli Dw l) (p : ℕ) (W : ValuationSubring ℂ) (Y : LocalSystem Xo p W) (i₀ : Idx H p) (i : Idx H p) (X : Scheme.{0}) (π : X ⟶ (Y i).X) (ty : (E →+* ℂ) → Finset ℕ) (A : Atlas (Y i) π ty), i₀.l.Dvd i.l → i₀.c.F ≤ i.c.F → Geo (Y i) π → ∃ (Z' : Mdl Y i₀) (e : Z'.X ≅ X), Z'.i = i ∧ Z'.ty = ty ∧ (∀ (Z₁ : Mdl Y i₀) (g : Z₁.X ⟶ X), MapsTo Z₁ A g → MapsTo Z₁ (atlasOf Z') (g ≫ e.inv)) ∧ (∀ (X₂ : Scheme.{0}) (π₂ : X₂ ⟶ (Y i).X) (ty₂ : (E →+* ℂ) → Finset ℕ) (A₂ : Atlas (Y i) π₂ ty₂) (f : X ⟶ X₂), f ≫ π₂ = π → (∀ (K : Type) [Field K] (w : Sp K ⟶ X) (u : Vecs Dw (Y i).t K), A.FlagAt w u → A₂.FlagAt (w ≫ f) u) → MapsTo Z' A₂ (e.hom ≫ f)) ∧ ∀ σ k, IntStep A σ k → IntStep (atlasOf Z') σ k := by
  intro E _ _ _ H Dw Xo p W Y i₀ i X π ty A hl hc g
  obtain ⟨n, ι, hι, hs⟩ := g.proj
  have hiso : IsIso ι.toImage := inferInstance
  let e : ι.ker.subscheme ≅ X := (asIso ι.toImage).symm
  have he : e.inv ≫ ι.ker.subschemeι = ι := ι.toImage_imageι
  have hs' : e.hom ≫ π ≫ (Y i).s = ι.ker.subschemeι ≫ PSpace.str _ n := by
    calc e.hom ≫ π ≫ (Y i).s = e.hom ≫ ι ≫ PSpace.str _ n := by rw [hs]
      _ = e.hom ≫ (e.inv ≫ ι.ker.subschemeι) ≫ PSpace.str _ n := by rw [he]
      _ = _ := by simp
  refine ⟨ToMdl.mdl A i₀ hl hc ι.ker e hs' g, e, rfl, rfl, ?_, ?_, ?_⟩
  · intro Z₁ f hf k _ w hw
    obtain ⟨τ, mu, u, h1, h2, h3, h4⟩ := hf k w hw
    refine ⟨τ, mu, u, h1, ?_, h3, ?_⟩
    · have h5 : (w ≫ f ≫ e.inv) ≫ e.hom ≫ π = (w ≫ f) ≫ π := by
        simp only [Category.assoc, Iso.inv_hom_id_assoc]
      exact h5.trans h2
    · refine (ToMdl.pre_flagAt_iff A i₀ hl hc ι.ker e (w ≫ f ≫ e.inv) _).2 ?_
      simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
      exact h4
  · intro X₂ π₂ ty₂ A₂ f hf hfl k _ w hw
    obtain ⟨mu, hmu, ht⟩ := exists_isTrans_id (Y := Y) i
    have hw' : (w ≫ e.hom) (IsLocalRing.closedPoint k) ∈ A.ch.carrier := by
      rw [A.cover]
      exact hw ⟨_, rfl⟩
    obtain ⟨a, φ, ha⟩ := A.ch.exists_fac (w ≫ e.hom) hw'
    refine ⟨𝟙 _, mu, (A.fr a).bc φ, ht, ?_, ?_, ?_⟩
    · exact ToMdl.comp_hom_comp w e f π₂ π hf
    · exact (ToMdl.pre_flagAt_iff A i₀ hl hc ι.ker e w _).2 (A.flagAt_fr ha)
    · have h5 : (fun σ j => (A.fr a).bc φ σ j ≫ mu.φ) = (A.fr a).bc φ := by
        funext σ j
        rw [hmu]
        exact Category.comp_id _
      exact (congrArg (A₂.FlagAt (w ≫ e.hom ≫ f)) h5).mpr
        (ToMdl.of_assoc w e f (fun v => A₂.FlagAt v ((A.fr a).bc φ)) (hfl k (w ≫ e.hom) _ (A.flagAt_fr ha)))
  · intro σ k h
    exact GlobalTheory.T.atlas_pullback_preserves_step E H Dw i.l (Xo i.l) i.c (i.c.V W) (Y i) X π ty A σ k _ e.hom ty (atlasOf (ToMdl.mdl A i₀ hl hc ι.ker e hs' g))
      (fun K _ w u hw => (ToMdl.pre_flagAt_iff A i₀ hl hc ι.ker e w u).1 hw) h

end GlobalTheory.DRFlag
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FromModelNegStatement
section
open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.LocM GlobalTheory.TrueGeo GlobalTheory.Cartier GlobalTheory.ProjVar
open Formalism.MainNotions.DIV.Cons (intO)
open GlobalTheory.LineNorm MonObj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fromModel_neg' : ∀ (F : Type) [Field F] [NumberField F] (Y : Var F) (Δ : Y.Dv) (t : Y.X → Y.Fnˣ) (φ : PtFn Y), (∀ y, Δ.IsEqn y (t y)) → FromModel Y Δ t φ → FromModel Y (-Δ) (fun y => (t y)⁻¹) (fun v e y => -φ v e y) := by
  first | exact @GlobalTheory.LineNorm.Neg.fromModel_neg | exact GlobalTheory.LineNorm.Neg.fromModel_neg | (intros; apply GlobalTheory.LineNorm.Neg.fromModel_neg <;> assumption)
end

