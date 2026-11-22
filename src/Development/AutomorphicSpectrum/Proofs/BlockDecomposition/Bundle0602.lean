import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.GaugeTopology.SSmoothW
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1369
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1414
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DetGramRatOneNeZero
import Development.WeilBound.CoreStatements.AutomorphicKernels.IsobaricBaseChange.IntegralCoefficientBaseChange.UnitaryBaseChangeCharacters.UnitaryBaseChangeLemmas.ToComplBijective
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0576
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsSmoothHermCombLine
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterRed
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1002
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0577
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0500
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MixedPointLengthFormula
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0578
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.StripEstimates.FaceMapCompSuccAboveCastSucc
import Formalism.RealPlaceAnalysis.Bundle0004
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0011
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.T2SpaceAdelicGeneralLinearGroupNumberField
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0009
import Development.AutomorphicSpectrum.PublishedTheorems.PublishedGlobalResults.HasInfCharOfIsRegAlg
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle0005
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DiscreteSpectrumGLTwoOfCuspidalSpectrum
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ClozelPurity.EopV

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalFunctionalWhittakerCharacter
section
open MeasureTheory Matrix GroundTheory.LocalField GroundTheory.Automorphic
open scoped ValuativeRel

noncomputable section

namespace GlobalTheory.CompanionTheory.LFPsi

open Ad3 Ad3.LFS

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [MeasurableSpace F] [BorelSpace F]

def tv (a y z : F) (x : Fin 2 → F) : Fin 2 → F := ![y + x 0 - a * (z + x 1), z + x 1]

theorem blk_mul_uni (a y z : F) (x : Fin 2 → F) :
    blk x * ((uni a y z : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
      ((uni2 a : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) * blk (tv a y z x) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [blk, uni, uni2, tv, Matrix.mul_apply, Fin.sum_univ_two, Fin.sum_univ_three] <;> ring

def tvEquiv (a y z : F) : (Fin 2 → F) ≃ᵐ (Fin 2 → F) where
  toFun := tv a y z
  invFun x := ![x 0 + a * x 1 - y, x 1 - z]
  left_inv x := by
    ext i; fin_cases i <;> simp [tv]
  right_inv x := by
    ext i; fin_cases i <;> simp [tv]
  measurable_toFun := by
    refine measurable_pi_iff.2 fun i => ?_
    fin_cases i
    · simp only [tv]
      exact (Continuous.measurable (by fun_prop) : Measurable fun x : Fin 2 → F => y + x 0 - a * (z + x 1))
    · simp only [tv]
      exact (Continuous.measurable (by fun_prop) : Measurable fun x : Fin 2 → F => z + x 1)
  measurable_invFun := by
    refine measurable_pi_iff.2 fun i => ?_
    fin_cases i
    · exact (Continuous.measurable (by fun_prop) : Measurable fun x : Fin 2 → F => x 0 + a * x 1 - y)
    · exact (Continuous.measurable (by fun_prop) : Measurable fun x : Fin 2 → F => x 1 - z)

theorem mp_tv (ψ : AddChar F Circle) (a y z : F) :
    MeasurePreserving (tv a y z) (vol2 ψ) (vol2 ψ) := by
  set μ := selfDualMeasure ψ with hμ
  have e : MeasurePreserving (MeasurableEquiv.piFinTwo fun _ : Fin 2 => F) (vol2 ψ) (μ.prod μ) :=
    measurePreserving_piFinTwo (fun _ => μ)
  have Q : MeasurePreserving (fun p : F × F => (z + p.1, y + p.2 - a * (z + p.1)))
      (μ.prod μ) (μ.prod μ) := by
    refine MeasurePreserving.skew_product (f := fun t => z + t)
      (g := fun t s => y + s - a * (z + t)) (measurePreserving_add_left μ z) ?_ ?_
    · exact Continuous.measurable (by unfold Function.uncurry; fun_prop)
    · refine Filter.Eventually.of_forall fun t => ?_
      have : (fun s => y + s - a * (z + t)) = fun s => s + (y - a * (z + t)) := by
        ext s; ring
      rw [this]
      exact (measurePreserving_add_right μ _).map_eq
  have sw : MeasurePreserving (Prod.swap : F × F → F × F) (μ.prod μ) (μ.prod μ) :=
    Measure.measurePreserving_swap
  have all := (MeasurePreserving.symm _ e).comp (sw.comp (Q.comp (sw.comp e)))
  convert all using 1
  ext x i
  fin_cases i <;> simp [tv, MeasurableEquiv.piFinTwo]

theorem inn_uni (ψ : AddChar F Circle) (Φ : Matrix (Fin 2) (Fin 3) F → ℂ) (h : GL (Fin 2) F)
    (a y z : F) (g : GL (Fin 3) F) :
    inn ψ Φ h (uni a y z * g) = (ψ z : ℂ) * inn ψ Φ (h * uni2 a) g := by
  unfold inn
  rw [← (mp_tv ψ a y z).integral_comp (tvEquiv a y z).measurableEmbedding
      (fun x => Φ (((h * uni2 a : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) * blk x *
        (g : Matrix (Fin 3) (Fin 3) F)) * (ψ (-x 1) : ℂ)),
    ← MeasureTheory.integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  have hm : ((h : Matrix (Fin 2) (Fin 2) F)) * blk x *
        (((uni a y z * g : GL (Fin 3) F)) : Matrix (Fin 3) (Fin 3) F) =
      (((h * uni2 a : GL (Fin 2) F)) : Matrix (Fin 2) (Fin 2) F) * blk (tv a y z x) *
        (g : Matrix (Fin 3) (Fin 3) F) := by
    rw [Units.val_mul, Units.val_mul, Matrix.mul_assoc (h : Matrix (Fin 2) (Fin 2) F) (blk x),
      ← Matrix.mul_assoc (blk x), blk_mul_uni]
    simp only [Matrix.mul_assoc]
  have hc : (ψ (-x 1) : ℂ) = (ψ z : ℂ) * (ψ (-(tv a y z x 1)) : ℂ) := by
    have : -x 1 = z + -(tv a y z x 1) := by simp [tv]
    rw [this, AddChar.map_add_eq_mul, Circle.coe_mul]
  beta_reduce
  rw [hm, hc]
  ring

theorem det_uni (a y z : F) : GeneralLinearGroup.det (uni a y z : GL (Fin 3) F) = 1 := by
  ext
  simp [uni, Matrix.det_fin_three]

theorem det_unipotent_adele (a : F) : GeneralLinearGroup.det (uni2 a : GL (Fin 2) F) = 1 := by
  ext
  simp [uni2, Matrix.det_fin_two]

theorem unipotent_inv_eq_neg (a : F) : (uni2 a : GL (Fin 2) F)⁻¹ = uni2 (-a) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [uni2]

theorem wp_uni (ψ : AddChar F Circle) (W' : GL (Fin 2) F → ℂ) (Φ : Matrix (Fin 2) (Fin 3) F → ℂ)
    (hpsi : ∀ x g, W' (uni2 x * g) = (ψ x : ℂ) * W' g) (a y z : F) (g : GL (Fin 3) F) :
    Wp ψ W' Φ (uni a y z * g) = (ψ (a + z) : ℂ) * Wp ψ W' Φ g := by
  unfold Wp
  have hd : GeneralLinearGroup.det (uni a y z * g) = GeneralLinearGroup.det g := by
    rw [map_mul, det_uni, one_mul]
  set G : GL (Fin 2) F → ℂ := fun h =>
    W' h⁻¹ * mp (GeneralLinearGroup.det h) (3 / 2) * inn ψ Φ h g with hG'
  have hi : ∀ h : GL (Fin 2) F,
      W' h⁻¹ * mp (GeneralLinearGroup.det h) (3 / 2) * inn ψ Φ h (uni a y z * g) =
        ((ψ a : ℂ) * (ψ z : ℂ)) * G (h * uni2 a) := by
    intro h
    have h1 : W' (h * uni2 a)⁻¹ = (ψ (-a) : ℂ) * W' h⁻¹ := by
      rw [_root_.mul_inv_rev, unipotent_inv_eq_neg, hpsi]
    have h2 : (ψ a : ℂ) * (ψ (-a) : ℂ) = 1 := by
      rw [← Circle.coe_mul, ← AddChar.map_add_eq_mul]
      simp
    have h3 : GeneralLinearGroup.det (h * uni2 a) = GeneralLinearGroup.det h := by
      rw [map_mul, det_unipotent_adele, mul_one]
    simp only [hG', h1, h3, inn_uni]
    linear_combination (-(W' h⁻¹ * mp (GeneralLinearGroup.det h) (3 / 2) * (ψ z : ℂ) *
      inn ψ Φ (h * uni2 a) g)) * h2
  haveI : (hG ψ).IsMulRightInvariant := by
    unfold hG
    infer_instance
  simp only [hi, hd]
  rw [MeasureTheory.integral_const_mul, integral_mul_right_eq_self G (uni2 a),
    AddChar.map_add_eq_mul, Circle.coe_mul]
  ring

theorem sPsiW : SPsiW := by
  intro F _ _ _ _ _ _ ψ ν W' Φ hyp x y z g
  obtain ⟨-, -, ⟨V', hV, hW⟩, -⟩ := hyp
  exact wp_uni ψ W' Φ (hV.psi W' hW) x y z g

end GlobalTheory.CompanionTheory.LFPsi
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalFunctionalWhittakerSmooth
section
noncomputable section

open MeasureTheory Matrix GroundTheory.LocalField GroundTheory.Automorphic Ad3 Ad3.LFS
open scoped ValuativeRel

namespace GlobalTheory.CompanionTheory.LFSmooth

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]

theorem modulus_det_eq_one {u : GL (Fin 3) F} (hu : u ∈ GLnLocal.integralGL F 3) :
    modulus ((GeneralLinearGroup.det u : Fˣ) : F) = 1 := by
  have key : ∀ w ∈ GLnLocal.integralGL F 3,
      modulus ((GeneralLinearGroup.det w : Fˣ) : F) ≤ 1 := by
    rintro _ ⟨v, rfl⟩
    rw [modulus_le_one_iff]
    have h : ((GeneralLinearGroup.det (GLnLocal.integralGLHom F 3 v) : Fˣ) : F) =
        (𝒪[F]).subtype (v : Matrix (Fin 3) (Fin 3) 𝒪[F]).det := by
      rw [RingHom.map_det]
      rfl
    rw [h]
    exact Subtype.property _
  have h1 := key u hu
  have h2 := key u⁻¹ (inv_mem hu)
  rw [map_inv, Units.val_inv_eq_inv_val, modulus_inv] at h2
  exact le_antisymm h1 ((inv_le_one₀ (modulus_pos (Units.ne_zero _))).1 h2)

theorem exists_openSubgroup_invariant {Φ : Matrix (Fin 2) (Fin 3) F → ℂ}
    (hl : IsLocallyConstant Φ) (hc : HasCompactSupport Φ) :
    ∃ U : OpenSubgroup (GL (Fin 3) F), (∀ u ∈ U, u ∈ GLnLocal.integralGL F 3) ∧
      ∀ u ∈ U, ∀ X : Matrix (Fin 2) (Fin 3) F,
        Φ (X * (u : Matrix (Fin 3) (Fin 3) F)) = Φ X := by
  have hcont : Continuous fun p : Matrix (Fin 2) (Fin 3) F × GL (Fin 3) F =>
      p.1 * (p.2 : Matrix (Fin 3) (Fin 3) F) :=
    continuous_fst.matrix_mul (Units.continuous_val.comp continuous_snd)
  have hlc : IsLocallyConstant fun p : Matrix (Fin 2) (Fin 3) F × GL (Fin 3) F =>
      Φ (p.1 * (p.2 : Matrix (Fin 3) (Fin 3) F)) - Φ p.1 :=
    (hl.comp_continuous hcont).sub (hl.comp_continuous continuous_fst)
  have hopen := hlc.isOpen_fiber 0
  have hsub : tsupport Φ ×ˢ ({1} : Set (GL (Fin 3) F)) ⊆
      (fun p : Matrix (Fin 2) (Fin 3) F × GL (Fin 3) F =>
        Φ (p.1 * (p.2 : Matrix (Fin 3) (Fin 3) F)) - Φ p.1) ⁻¹' {0} := by
    rintro ⟨X, u⟩ ⟨-, hu⟩
    obtain rfl : u = 1 := hu
    simp
  obtain ⟨A, B, -, hB, hA, h1, hAB⟩ :=
    generalized_tube_lemma hc isCompact_singleton hopen hsub
  obtain ⟨m, -, hm⟩ :=
    (GLnLocal.hasBasis_nhds_one F 3).mem_iff.1 (hB.mem_nhds (h1 rfl))
  have hfix : ∀ u ∈ GLnLocal.congruenceSubgroup F 3 m, ∀ X, Φ X ≠ 0 →
      Φ (X * (u : Matrix (Fin 3) (Fin 3) F)) = Φ X := by
    intro u hu X hX
    have : (X, u) ∈ A ×ˢ B := ⟨hA (subset_tsupport _ hX), hm hu⟩
    exact sub_eq_zero.1 (hAB this)
  refine ⟨⟨GLnLocal.congruenceSubgroup F 3 m, GLnLocal.isOpen_congruenceSubgroup F 3 m⟩,
    fun u hu => GLnLocal.congruenceSubgroup_le F 3 m hu, fun u hu X => ?_⟩
  have hu' : u ∈ GLnLocal.congruenceSubgroup F 3 m := hu
  by_cases hX : Φ X = 0
  · by_cases hY : Φ (X * (u : Matrix (Fin 3) (Fin 3) F)) = 0
    · rw [hX, hY]
    · have h := hfix u⁻¹ (inv_mem hu') _ hY
      rw [Matrix.mul_assoc, Units.mul_inv_of_eq rfl, Matrix.mul_one] at h
      exact h.symm
  · exact hfix u hu' X hX

theorem smoothW : Ad3.LFS.SSmoothW := by
  intro F _ _ _ _ _ _ ψ ν W' Φ h
  obtain ⟨hl, hc⟩ := h.2.2.2
  obtain ⟨U, hUK, hU⟩ := exists_openSubgroup_invariant hl hc
  refine ⟨U, fun g u hu => ?_⟩
  have hinn : ∀ k, inn ψ Φ k (g * u) = inn ψ Φ k g := by
    intro k
    simp only [inn, Units.val_mul, ← Matrix.mul_assoc, hU u hu]
  have hdet : mp (GeneralLinearGroup.det (g * u)) 1 = mp (GeneralLinearGroup.det g) 1 := by
    simp only [mp, map_mul, Units.val_mul, modulus_mul, modulus_det_eq_one (hUK u hu), mul_one]
  simp only [Wp, hinn, hdet]

end GlobalTheory.CompanionTheory.LFSmooth
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalHermitianClassSecond
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.UnitaryClasses
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.IndefiniteRowSideFullHecke.SelfReciprocalLocalField PositivityTheory.BCUSide.HermitianLocalForms

noncomputable section

namespace GlobalTheory.CompanionTheory.LocPhiUnit

section Fixed

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (Q : SelfRecip E r)
  (k : Type) [CommRing k] [Algebra (maximalRealSubfield E) k]

theorem exists_inclPlus_half (z : k ⊗[maximalRealSubfield E] Fld Q) :
    ∃ a : k ⊗[maximalRealSubfield E] plus Q,
      inclPlus Q k a = ((1 : k) ⊗ₜ[maximalRealSubfield E] (2⁻¹ : Fld Q)) * (z + involBase Q k z) := by
  induction z using TensorProduct.induction_on with
  | zero => exact ⟨0, by simp⟩
  | tmul s y =>
    refine ⟨s ⊗ₜ ⟨(y + invol Q y) / 2, ?_⟩, ?_⟩
    · change invol Q _ = _
      simp only [map_div₀, map_add, invol_invol, map_ofNat, AlgHom.id_apply, add_comm]
    · change s ⊗ₜ[maximalRealSubfield E] ((y + invol Q y) / 2) = _ * (s ⊗ₜ y + s ⊗ₜ invol Q y)
      rw [← TensorProduct.tmul_add, Algebra.TensorProduct.tmul_mul_tmul, one_mul, div_eq_inv_mul]
  | add x y hx hy =>
    obtain ⟨a, ha⟩ := hx
    obtain ⟨b, hb⟩ := hy
    refine ⟨a + b, ?_⟩
    rw [map_add, ha, hb, map_add]
    ring

theorem exists_inclPlus_of_fixed {z : k ⊗[maximalRealSubfield E] Fld Q} (hz : involBase Q k z = z) :
    ∃ a : k ⊗[maximalRealSubfield E] plus Q, inclPlus Q k a = z := by
  obtain ⟨a, ha⟩ := exists_inclPlus_half Q k z
  refine ⟨a, ?_⟩
  have h2 : (2 : k ⊗[maximalRealSubfield E] Fld Q) = (1 : k) ⊗ₜ[maximalRealSubfield E] (2 : Fld Q) :=
    (map_ofNat (Algebra.TensorProduct.includeRight :
      Fld Q →ₐ[maximalRealSubfield E] k ⊗[maximalRealSubfield E] Fld Q) 2).symm
  rw [ha, hz, ← two_mul, ← mul_assoc, h2, Algebra.TensorProduct.tmul_mul_tmul, mul_one,
    inv_mul_cancel₀ two_ne_zero, ← Algebra.TensorProduct.one_def, one_mul]

theorem inclPlus_injective : Function.Injective (inclPlus Q k) :=
  Module.Flat.lTensor_preserves_injective_linearMap (M := k) (plus Q).val.toLinearMap
    Subtype.val_injective

theorem exists_unit_of_fixed {y : k ⊗[maximalRealSubfield E] Fld Q} (hu : IsUnit y)
    (hy : involBase Q k y = y) :
    ∃ x : (k ⊗[maximalRealSubfield E] plus Q)ˣ,
      inclPlus Q k (x : k ⊗[maximalRealSubfield E] plus Q) = y := by
  obtain ⟨u, rfl⟩ := hu
  have hinv : involBase Q k ((u⁻¹ : (k ⊗[maximalRealSubfield E] Fld Q)ˣ) :
      k ⊗[maximalRealSubfield E] Fld Q) = (u⁻¹ : (k ⊗[maximalRealSubfield E] Fld Q)ˣ) := by
    have h1 : (u : k ⊗[maximalRealSubfield E] Fld Q) * involBase Q k
        ((u⁻¹ : (k ⊗[maximalRealSubfield E] Fld Q)ˣ) : k ⊗[maximalRealSubfield E] Fld Q) = 1 := by
      conv_lhs => rw [← hy]
      rw [← map_mul, Units.mul_inv, map_one]
    calc _ = ((u⁻¹ : (k ⊗[maximalRealSubfield E] Fld Q)ˣ) : k ⊗[maximalRealSubfield E] Fld Q) *
          ((u : k ⊗[maximalRealSubfield E] Fld Q) * involBase Q k
            ((u⁻¹ : (k ⊗[maximalRealSubfield E] Fld Q)ˣ) : k ⊗[maximalRealSubfield E] Fld Q)) := by
          rw [Units.inv_mul_cancel_left]
      _ = _ := by rw [h1, mul_one]
  obtain ⟨a, ha⟩ := exists_inclPlus_of_fixed Q k hy
  obtain ⟨b, hb⟩ := exists_inclPlus_of_fixed Q k hinv
  have hab : a * b = 1 := inclPlus_injective Q k (by rw [map_mul, ha, hb, Units.mul_inv, map_one])
  exact ⟨⟨a, b, hab, by rw [mul_comm]; exact hab⟩, ha⟩

end Fixed

section Matrix

theorem aeval_mul_of_intertwine {K : Type} [Field K] {n : ℕ} {B C H : Matrix (Fin n) (Fin n) K}
    (h : B * H = H * C) (g : K[X]) : aeval B g * H = H * aeval C g := by
  induction g using Polynomial.induction_on' with
  | add p q hp hq => rw [map_add, map_add, add_mul, mul_add, hp, hq]
  | monomial d a =>
    have e : B ^ d * H = H * C ^ d :=
      (((show SemiconjBy H C B from h.symm).pow_right d).eq).symm
    rw [aeval_monomial, aeval_monomial]
    simp only [Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul, mul_smul_comm, mul_assoc, e]

theorem cT_mul {K : Type} [Field K] (s : K →+* K) {n : ℕ} (B C : Matrix (Fin n) (Fin n) K) :
    cT s (B * C) = cT s C * cT s B := by
  simp [cT, Matrix.map_mul, Matrix.transpose_mul]

end Matrix

section Local

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem involBase_locPhi (hU : Unr E) (w : Pl E) (hw : ¬ IsSplitAt w)
    (v : HeightOneSpectrum (𝓞 (maximalRealSubfield E))) (hv : w.under (𝓞 (maximalRealSubfield E)) = v)
    {r : ℕ} (Q : SelfRecip E r) {r₀ : E[X]} (hr : AdjoinRoot.mk Q.1 (X * r₀ - 1) = 0)
    (f : (w.adicCompletion E)[X]) :
    involBase Q (v.adicCompletion (maximalRealSubfield E)) (locPhi hU w hw v hv Q f) =
      locPhi hU w hw v hv Q ((f.map (cj w)).comp (atPl w r₀)) := by
  set k := v.adicCompletion (maximalRealSubfield E)
  let ι : w.adicCompletion E →+* k ⊗[maximalRealSubfield E] Fld Q :=
    (inclBase Q k).toRingHom.comp (locJ hU w hw v hv).toRingHom
  have hιc : ∀ y, involBase Q k (ι y) = ι (cj w y) := by
    intro y
    change involBase Q k (inclBase Q k (locJ hU w hw v hv y)) =
      inclBase Q k (locJ hU w hw v hv (cj w y))
    rw [locJ_cj]
    generalize locJ hU w hw v hv y = t
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul a e => simp [inclBase, involBase, invol_algebraMap]
    | add a b ha hb => simp only [map_add, ha, hb]
  let ib : k ⊗[maximalRealSubfield E] Fld Q →+* k ⊗[maximalRealSubfield E] Fld Q :=
    (involBase Q k).toRingHom
  have hR : locPhi hU w hw v hv Q (atPl w r₀) = (1 : k) ⊗ₜ (alpha Q)⁻¹ := by
    rw [locPhi_atPl]
    congr 1
    rw [map_sub, map_mul, AdjoinRoot.mk_X, map_one, sub_eq_zero] at hr
    exact eq_inv_of_mul_eq_one_right hr
  have e1 : ib.comp ι = ι.comp (cj w) := RingHom.ext fun y => hιc y
  have e2 : ib ((1 : k) ⊗ₜ alpha Q) = (1 : k) ⊗ₜ (alpha Q)⁻¹ := by
    change (1 : k) ⊗ₜ invol Q (alpha Q) = _
    rw [invol_alpha]
  change ib (eval₂ ι _ f) = eval₂ ι _ _
  rw [Polynomial.hom_eval₂, e1, e2, eval₂_comp, eval₂_map]
  exact congrArg (fun x => eval₂ (ι.comp (cj w)) x f) hR.symm

end Local

theorem locPhi_mem_units_plus : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (hU : Unr E) (w : Pl E) (hw : ¬ IsSplitAt w) (v : HeightOneSpectrum (𝓞 (maximalRealSubfield E))) (hv : w.under (𝓞 (maximalRealSubfield E)) = v), ∀ (n : ℕ) (γ₀ : GL (Fin n) E), γ₀.val.charpoly ∈ Ell E n → ∀ H₀ : Matrix (Fin n) (Fin n) E, IsHerm (IsCMField.complexConj E).toRingEquiv.toRingHom H₀ → H₀.det ≠ 0 → cT (IsCMField.complexConj E).toRingEquiv.toRingHom γ₀.val * H₀ * γ₀.val = H₀ → ∀ m : (w.adicCompletion E)[X], IsHerm (cj w) ((H₀.map (algebraMap E (w.adicCompletion E))) * aeval (γ₀.val.map (algebraMap E (w.adicCompletion E))) m) → ((H₀.map (algebraMap E (w.adicCompletion E))) * aeval (γ₀.val.map (algebraMap E (w.adicCompletion E))) m).det ≠ 0 → ∀ (r : ℕ) (Q : SelfRecip E r), Q.1 ∣ γ₀.val.charpoly → ∃ x : ((v.adicCompletion (maximalRealSubfield E)) ⊗[(maximalRealSubfield E)] plus Q)ˣ, inclPlus Q (v.adicCompletion (maximalRealSubfield E)) (x : (v.adicCompletion (maximalRealSubfield E)) ⊗[(maximalRealSubfield E)] plus Q) = locPhi hU w hw v hv Q m := by
  intro E _ _ _ hU w hw v hv n γ₀ hell H₀ hH hdet h3 m hM hMdet r Q hQ
  have hsep : γ₀.val.charpoly.Separable := hell.2.2.1
  obtain ⟨r₀, hr₀⟩ := GlobalTheory.BCT.ClsFin.exists_aeval_of_comm γ₀.val (γ₀⁻¹).val hsep
    (by rw [Units.mul_inv, Units.inv_mul])
  have hPr : γ₀.val.charpoly ∣ X * r₀ - 1 := by
    refine GlobalTheory.ClassParam.charpoly_dvd_of_aeval γ₀.val hsep _ ?_
    rw [map_sub, map_mul, aeval_X, ← hr₀, Units.mul_inv, map_one, sub_self]
  have hr : AdjoinRoot.mk Q.1 (X * r₀ - 1) = 0 := AdjoinRoot.mk_eq_zero.2 (hQ.trans hPr)
  obtain ⟨A, hA⟩ : ∃ A, A = γ₀.val.map (algebraMap E (w.adicCompletion E)) := ⟨_, rfl⟩
  obtain ⟨H, hHd⟩ : ∃ H, H = H₀.map (algebraMap E (w.adicCompletion E)) := ⟨_, rfl⟩
  rw [← hA, ← hHd] at hM hMdet
  obtain ⟨M, hMd⟩ : ∃ M, M = aeval A m := ⟨_, rfl⟩
  rw [← hMd] at hM hMdet
  have hAsep : A.charpoly.Separable := by rw [hA, Matrix.charpoly_map]; exact hsep.map
  have hAP : A.charpoly = atPl w γ₀.val.charpoly := by rw [hA]; exact Matrix.charpoly_map _ _
  have hAi : A * aeval A (atPl w r₀) = 1 := by
    rw [hA, aeval_map_mat, ← hr₀, ← Matrix.map_mul, Units.mul_inv,
      Matrix.map_one _ (map_zero _) (map_one _)]
  have hHh : cT (cj w) H = H := by
    rw [hHd, ← cT_map hU w hw]
    exact congrArg (Matrix.map · (algebraMap E (w.adicCompletion E))) hH
  have hcA : cT (cj w) A * H * A = H := by
    have := congrArg (Matrix.map · (algebraMap E (w.adicCompletion E))) h3
    simp only [Matrix.map_mul, cT_map hU w hw] at this
    rw [hA, hHd]
    exact this
  have hint : cT (cj w) A * H = H * aeval A (atPl w r₀) := by
    calc cT (cj w) A * H = cT (cj w) A * H * (A * aeval A (atPl w r₀)) := by rw [hAi, Matrix.mul_one]
      _ = H * aeval A (atPl w r₀) := by rw [← Matrix.mul_assoc, hcA]
  have hH0 : IsUnit H := by
    rw [Matrix.isUnit_iff_isUnit_det, Matrix.det_mul] at *
    exact (left_ne_zero_of_mul hMdet).isUnit
  have hM0 : IsUnit M := by
    rw [Matrix.isUnit_iff_isUnit_det]
    rw [Matrix.det_mul] at hMdet
    exact (right_ne_zero_of_mul hMdet).isUnit
  have hfix : M = aeval A ((m.map (cj w)).comp (atPl w r₀)) := by
    have h1 : cT (cj w) M * H = H * M := by
      have := hM
      rw [IsHerm, cT_mul, hHh] at this
      exact this
    rw [hMd, GlobalTheory.NormInert.cT_aeval, aeval_mul_of_intertwine hint, ← aeval_comp, ← hMd] at h1
    exact (hH0.mul_left_cancel h1).symm
  have hdiv : A.charpoly ∣ (m.map (cj w)).comp (atPl w r₀) - m :=
    GlobalTheory.ClassParam.charpoly_dvd_of_aeval A hAsep _ (by rw [map_sub, ← hfix, ← hMd, sub_self])
  have hΦ0 : locPhi hU w hw v hv Q A.charpoly = 0 := by
    rw [hAP, locPhi_atPl]
    exact (congrArg _ (AdjoinRoot.mk_eq_zero.2 hQ)).trans (TensorProduct.tmul_zero _ _)
  have hy : involBase Q (v.adicCompletion (maximalRealSubfield E)) (locPhi hU w hw v hv Q m) =
      locPhi hU w hw v hv Q m := by
    obtain ⟨t, ht⟩ := hdiv
    rw [involBase_locPhi hU w hw v hv Q hr, ← sub_eq_zero, ← map_sub, ht, map_mul, hΦ0, zero_mul]
  obtain ⟨u, hu⟩ := hM0
  have hcomm : Commute A (u : Matrix (Fin n) (Fin n) (w.adicCompletion E)) := by
    rw [hu, hMd]
    have := congrArg (aeval A) (mul_comm (X : (w.adicCompletion E)[X]) m)
    rw [map_mul, map_mul, aeval_X] at this
    exact this
  obtain ⟨g, hg⟩ := GlobalTheory.BCT.ClsFin.exists_aeval_of_comm A
    ((u⁻¹ : (Matrix (Fin n) (Fin n) (w.adicCompletion E))ˣ) : Matrix (Fin n) (Fin n) (w.adicCompletion E))
    hAsep hcomm.units_inv_right.eq
  have hdiv2 : A.charpoly ∣ m * g - 1 :=
    GlobalTheory.ClassParam.charpoly_dvd_of_aeval A hAsep _ (by
      rw [map_sub, map_mul, ← hg, ← hMd, ← hu, Units.mul_inv, map_one, sub_self])
  have hone : locPhi hU w hw v hv Q m * locPhi hU w hw v hv Q g = 1 := by
    obtain ⟨t, ht⟩ := hdiv2
    rw [← map_mul, ← sub_eq_zero, ← map_one (locPhi hU w hw v hv Q), ← map_sub, ht, map_mul, hΦ0,
      zero_mul]
  exact exists_unit_of_fixed Q _ (isUnit_iff_exists_inv.2 ⟨_, hone⟩) hy

end GlobalTheory.CompanionTheory.LocPhiUnit

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LogNormContinuousOffDivisorStatement
section
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry Limits TopologicalSpace MvPolynomial MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.ProjSpace GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.Points GlobalTheory.ChartGlue
open GroundTheory.Arith.SchemeCoh GroundTheory.Arith.SchemeCoh.ProjSpace
open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open GlobalTheory.CompanionTheory.MPDict GlobalTheory.CompanionTheory.MixZ
open ReciprocityTheory.ChartRestriction.G.Geo (mcPts IsMultiHomog SameOrbit)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.log_norm_continuous_off_divisor : ∀ {k : Type} [CommRing k] {X : Scheme.{0}} [IsIntegral X] {q : X ⟶ Sp k} {σ : k →+* ℂ}
    {L : LB X} (ψ : GlobalTheory.Weight q σ L), ψ.IsCInf → ∀ {r : L.ι → X.functionFieldˣ} (hr : IsRatSec L r),
    ContinuousOn (GlobalTheory.Cartier.logNorm ψ r) (offSupp q σ (divOfRatSec ψ.isLB hr)) := by
  first | exact @GlobalTheory.CompanionTheory.MixZ.ArchInt.continuousOn_logNorm_offSupp | exact GlobalTheory.CompanionTheory.MixZ.ArchInt.continuousOn_logNorm_offSupp | (intros; apply GlobalTheory.CompanionTheory.MixZ.ArchInt.continuousOn_logNorm_offSupp <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MirabolicPairingConductorBoundStatement
section
open Matrix MeasureTheory GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.BZSeg GlobalTheory.BZMir GlobalTheory.SplitWeil GlobalTheory.CompanionTheory.MirFourier GlobalTheory.CompanionTheory.BZOnto.PerpSmall ValuativeRel Zc
open scoped Topology
open GlobalTheory.CompanionTheory.MirPair

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mirabolic_pairing_conductor_bound : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (ν : Measure k) [ν.IsAddHaarMeasure] (ψ : AddChar k Circle) (c : kˣ) {n : ℕ} {V V' : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V'] (T : Representation ℂ (Mir k (n + 1)) V) (T' : Representation ℂ (Mir k (n + 1)) V') (B : V →ₗ[ℂ] V' →ₗ[ℂ] ℂ) (s : ℕ), Continuous ψ → HasConductor ψ c → IsSmooth T → IsSmooth T' → TwInv T T' B s → ∀ (g : GL (Fin (n + 1)) k) (v : V) (v' : V'), ∃ r : kˣ, ∀ t : kˣ, valuation k ((c * t⁻¹ : kˣ) : k) ≤ valuation k (r : k) → ∀ t' : kˣ, (∀ x ∈ box (n + 1) t, (g : Matrix (Fin (n + 1)) (Fin (n + 1)) k) *ᵥ x ∈ box (n + 1) t') → JJ ν ψ T B {x | (g : Matrix (Fin (n + 1)) (Fin (n + 1)) k) *ᵥ x ∈ box (n + 1) t'} v v' = JJ ν ψ T B (box (n + 1) t : Set (Fin (n + 1) → k)) v v' := by
  first | exact @GlobalTheory.CompanionTheory.MirPair.JJ_preimage_box_eq_JJ_box | exact GlobalTheory.CompanionTheory.MirPair.JJ_preimage_box_eq_JJ_box | (intros; apply GlobalTheory.CompanionTheory.MirPair.JJ_preimage_box_eq_JJ_box <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MixedPointLengthFormulaStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mixed_point_length_formula : GlobalTheory.CompanionTheory.MixZ.PtLen := by
  first | exact @GlobalTheory.CompanionTheory.MixZ.PtLenProof.ptLen | exact GlobalTheory.CompanionTheory.MixZ.PtLenProof.ptLen | (intros; apply GlobalTheory.CompanionTheory.MixZ.PtLenProof.ptLen <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MixedPolarizationIdentityStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mixed_polarization_identity : GlobalTheory.CompanionTheory.MixZ.Polar := by
  first | exact @GlobalTheory.CompanionTheory.MixZ.PolarProof.polar | exact GlobalTheory.CompanionTheory.MixZ.PolarProof.polar | (intros; apply GlobalTheory.CompanionTheory.MixZ.PolarProof.polar <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NormSquareCoefficientLeDivisorBoundStatement
section
open Ad3 Ad3.S
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.norm_square_coefficient_le_divisor_bound : ∀ (k N : ℕ) (χ : DirichletCharacter ℂ N) (a : ℕ → ℂ), IsEig k N χ a → E2a → (∀ p : ℕ, p.Prime → ¬ p ∣ N → ∃ α β : ℂ, α + β = a p ∧ α * β = χ p * (p : ℂ) ^ (k - 1) ∧ ‖α‖ = ‖β‖) → ∀ n : ℕ, Nat.Coprime n N → ‖a (n ^ 2)‖ ≤ (((n ^ 2).divisors.card : ℕ) : ℝ) * (n : ℝ) ^ (k - 1) := by
  first | exact @GlobalTheory.CompanionTheory.HeckeSq.norm_sq_le | exact GlobalTheory.CompanionTheory.HeckeSq.norm_sq_le | (intros; apply GlobalTheory.CompanionTheory.HeckeSq.norm_sq_le <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NormalisedCuspFormL2BoundedStatement
section
open NumberField GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL MeasureTheory PositivityTheory.S2.Clozel
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.normalised_cusp_form_L2_bounded : GlobalTheory.Published.CuspFormsBoundedGL → ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (μ : Measure (GA E a)) [μ.IsHaarMeasure] [μ.IsMulRightInvariant] (π : CuspSub E a), GlobalTheory.DiscSpec.IsNormalised π → ∀ φ ∈ π.V, GlobalTheory.AutomorphicL2Unitary.MemL2Quotient (GlobalTheory.UnitaryBC.latticeGL E a) μ φ.1 ∧ ∃ C : ℝ, ∀ g, ‖φ.1 g‖ ≤ C := by
  first | exact @GlobalTheory.CompanionTheory.CuspForms.memL2_and_bounded_of_normalised | exact GlobalTheory.CompanionTheory.CuspForms.memL2_and_bounded_of_normalised | (intros; apply GlobalTheory.CompanionTheory.CuspForms.memL2_and_bounded_of_normalised <;> assumption)
end

