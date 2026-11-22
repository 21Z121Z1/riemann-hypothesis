import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemHatIffOfSelfDual
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0261
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0013
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0176
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1598
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1026
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilLatticeIntertwinerCoefficientAtPlace
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0182
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsFinWeil

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemHatGlueLatIffDual
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Lev Formalism.IndefR.Links
open Formalism.IndefR.Datum (IsSelfDualC)
open scoped TensorProduct nonZeroDivisors

namespace GlobalTheory.AdIsom

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open GlobalTheory.IndefiniteRowSideFullHecke.FlatSpaceComponents
open GlobalTheory.StdFrames hiding OA
open GlobalTheory.IdemSupport (cP cO)
open GlobalTheory.NormSum.AdLattice (lat)

variable {D : D7}

section Flat

variable {Y X : HSp D} {ι : X.V →ₗ[D.host.E] Y.V} {z : Y.V} {u : D.what₂.Word}

theorem vA_surj (V : HSp D) (x : Fin V.rank → D.host.E) : ∃ y : V.V, vA V y = fun i => inc D (x i) :=
  ⟨(Formalism.L2.Herm.crd V).symm x, funext fun i => by simp [vA]⟩

theorem eq_sum_vA_frame (x : Fin X.rank → EAf D) : x = ∑ i, x i • vA X (X.frame i) := by
  funext k
  have : ∀ i, vA X (X.frame i) k = if i = k then 1 else 0 := fun i => by
    change inc D (X.frame.repr (X.frame i) k) = _
    rw [Module.Basis.repr_self, Finsupp.single_apply]
    split_ifs
    · exact map_one _
    · exact map_zero _
  simp [Finset.sum_apply, this]

theorem adelic_induction {p : (Fin X.rank → EAf D) → Prop} (h1 : ∀ x : X.V, p (vA X x)) (h0 : p 0)
    (hadd : ∀ x y, p x → p y → p (x + y)) (hsm : ∀ (a : EAf D) x, p x → p (a • x)) (x : Fin X.rank → EAf D) : p x := by
  rw [eq_sum_vA_frame x]
  exact Finset.sum_induction _ p hadd h0 fun i _ => hsm _ _ (h1 _)

theorem hA_zero_left (V : HSp D) (y : Fin V.rank → EAf D) : hA V 0 y = 0 := by simp [hA, Formalism.UG.hform]

theorem hA_zero_right (V : HSp D) (y : Fin V.rank → EAf D) : hA V y 0 = 0 := by simp [hA, Formalism.UG.hform]

theorem hA_mA_mA (h : HSpace.IsIsomEmb X Y ι) (x x' : Fin X.rank → EAf D) :
    hA Y (mA Y X ι *ᵥ x) (mA Y X ι *ᵥ x') = hA X x x' := by
  induction x using adelic_induction with
  | h1 x =>
    induction x' using adelic_induction with
    | h1 x' => rw [mA_mulVec_vA, mA_mulVec_vA, hA_vA, hA_vA, HSpace.hD, HSpace.hD, h]
    | h0 => rw [mulVec_zero, hA_zero_right, hA_zero_right]
    | hadd a b ha hb => rw [mulVec_add, hA_add_right, hA_add_right, ha, hb]
    | hsm c a ha => rw [mulVec_smul, hA_smul_right, hA_smul_right, ha]
  | h0 => rw [mulVec_zero, hA_zero_left, hA_zero_left]
  | hadd a b ha hb => rw [mulVec_add, hA_add_left, hA_add_left, ha, hb]
  | hsm c a ha => rw [mulVec_smul, hA_smul_left, hA_smul_left, ha]

theorem hA_mA_vA (h : IsLine Y X ι z u) (x : Fin X.rank → EAf D) : hA Y (mA Y X ι *ᵥ x) (vA Y z) = 0 := by
  induction x using adelic_induction with
  | h1 x => rw [mA_mulVec_vA, hA_vA, h.2.1, RingHom.map_zero]
  | h0 => rw [mulVec_zero, hA_zero_left]
  | hadd a b ha hb => rw [mulVec_add, hA_add_left, ha, hb, add_zero]
  | hsm c a ha => rw [mulVec_smul, hA_smul_left, ha, mul_zero]

theorem hA_flat (h : IsLine Y X ι z u) (x x' : Fin X.rank → EAf D) (a a' : EAf D) :
    hA Y (mA Y X ι *ᵥ x + a • vA Y z) (mA Y X ι *ᵥ x' + a' • vA Y z) = hA X x x' - a * cjA D a' * inc D (Tu D u) := by
  have h1 : hA Y (vA Y z) (mA Y X ι *ᵥ x') = 0 := by rw [← cjA_hA, hA_mA_vA h, RingHom.map_zero]
  rw [hA_add_left, hA_add_right, hA_add_right, hA_smul_left, hA_smul_left, hA_smul_right, hA_smul_right,
    hA_mA_mA h.1, hA_mA_vA h, h1, hA_vA, h.2.2, RingHom.map_neg]
  ring

theorem inc_inv_mul (u : D.what₂.Word) : inc D (Tu D u)⁻¹ * inc D (Tu D u) = 1 := by
  rw [← RingHom.map_mul, inv_mul_cancel₀ (Tu_ne_zero u), RingHom.map_one]

theorem cjA_inc_Tu (u : D.what₂.Word) : cjA D (inc D (Tu D u)) = inc D (Tu D u) := by rw [cjA_inc, star_natCast]

theorem cjA_inc_inv (u : D.what₂.Word) : cjA D (inc D (Tu D u)⁻¹) = inc D (Tu D u)⁻¹ := by
  rw [cjA_inc, star_inv₀, star_natCast]

theorem inc_Tu_mem (u : D.what₂.Word) : inc D (Tu D u) ∈ OA D := by
  rw [map_natCast]; exact natCast_mem _ _

theorem eq_zero_of_hA {V : HSp D} {x : Fin V.rank → EAf D} (h : ∀ y, hA V x y = 0) : x = 0 := by
  have h1 : V.gram.map (inc D) *ᵥ x = 0 := funext fun i => by
    rw [← Formalism.UG.P.sf_single (cjA D)]; exact h _
  exact Matrix.mulVec_injective_of_isUnit (isUnit_gram V) (h1.trans (mulVec_zero _).symm)

theorem flat_inj (h : IsLine Y X ι z u) {x x' : Fin X.rank → EAf D} {a a' : EAf D}
    (e : mA Y X ι *ᵥ x + a • vA Y z = mA Y X ι *ᵥ x' + a' • vA Y z) : x = x' ∧ a = a' := by
  constructor
  · rw [← sub_eq_zero]
    refine eq_zero_of_hA fun y => ?_
    have h1 := hA_flat h x y a 0
    rw [e, hA_flat h] at h1
    rw [hA_sub_left]
    simp only [RingHom.map_zero, mul_zero, zero_mul, sub_zero] at h1
    rw [h1, sub_self]
  · have h1 := hA_flat h x 0 a (inc D (Tu D u)⁻¹)
    rw [e, hA_flat h, hA_zero_right, hA_zero_right, cjA_inc_inv, mul_assoc, mul_assoc, inc_inv_mul] at h1
    linear_combination h1

theorem mem_glueLat {L₀ : Lat X} {x₀ : X.V} (y : Y.V) : y ∈ glueLat Y X ι z u L₀ x₀ ↔
    ∃ x : X.V, Formalism.L2.Herm.crd X x ∈ L₀ ∧ ∃ a : 𝓞 D.host.E, y = ι x + (a : D.host.E) • ((Tu D u)⁻¹ • z + ι x₀) := by
  rw [glueLat, Submodule.mem_sup]
  constructor
  · rintro ⟨_, ⟨x, hx, rfl⟩, b, hb, rfl⟩
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.1 hb
    exact ⟨x, hx, a, by rw [← algebraMap_smul D.host.E a]; rfl⟩
  · rintro ⟨x, hx, a, rfl⟩
    exact ⟨_, ⟨x, hx, rfl⟩, _, Submodule.mem_span_singleton.2 ⟨a, rfl⟩, by rw [← algebraMap_smul D.host.E a]; rfl⟩

set_option maxHeartbeats 1600000 in

theorem mem_hat_glueLat {L₀ : Lat X} {x₀ : X.V} (y : Fin Y.rank → EAf D) :
    y ∈ hat (Formalism.L2.Herm.crdLat Y (glueLat Y X ι z u L₀ x₀)) ↔ ∃ x ∈ hat L₀, ∃ a ∈ OA D,
      y = mA Y X ι *ᵥ (x + a • vA X x₀) + (a * inc D (Tu D u)⁻¹) • vA Y z := by
  constructor
  · intro hy
    refine hat_induction (p := fun y => ∃ x ∈ hat L₀, ∃ a ∈ OA D,
      y = mA Y X ι *ᵥ (x + a • vA X x₀) + (a * inc D (Tu D u)⁻¹) • vA Y z) ?_ ?_ ?_ ?_ hy
    · rintro _ ⟨y, hy, rfl⟩
      obtain ⟨x, hx, a, rfl⟩ := (mem_glueLat y).1 hy
      refine ⟨vA X x, inc_mem_hat hx, inc D a, (inc_mem_iff _).2 ⟨a, rfl⟩, ?_⟩
      change vA Y _ = _
      rw [vA_add, vA_smul, vA_add, vA_smul, mulVec_add, mulVec_smul, mA_mulVec_vA, mA_mulVec_vA, smul_add, smul_smul]
      abel
    · exact ⟨0, zero_mem_hat, 0, zero_mem _, by rw [zero_smul, add_zero, mulVec_zero, zero_mul, zero_smul, add_zero]⟩
    · rintro _ _ ⟨x, hx, a, ha, rfl⟩ ⟨x', hx', a', ha', rfl⟩
      refine ⟨x + x', add_mem_hat hx hx', a + a', add_mem ha ha', ?_⟩
      rw [add_smul, add_mul, add_smul, add_add_add_comm x, mulVec_add _ (x + _)]
      abel
    · rintro c hc _ ⟨x, hx, a, ha, rfl⟩
      refine ⟨c • x, smul_mem_hat hc hx, c * a, mul_mem hc ha, ?_⟩
      rw [smul_add, ← mulVec_smul, smul_add, smul_smul, smul_smul, mul_assoc]
  · rintro ⟨x, hx, a, ha, rfl⟩
    have h1 : mA Y X ι *ᵥ x ∈ hat (Formalism.L2.Herm.crdLat Y (glueLat Y X ι z u L₀ x₀)) := by
      refine hat_induction (p := fun x => mA Y X ι *ᵥ x ∈ hat (Formalism.L2.Herm.crdLat Y (glueLat Y X ι z u L₀ x₀)))
        ?_ ?_ ?_ ?_ hx
      · intro x hx
        obtain ⟨x, rfl⟩ := (Formalism.L2.Herm.crd X).surjective x
        change mA Y X ι *ᵥ vA X x ∈ _
        rw [mA_mulVec_vA]
        exact vA_mem_hat Y ((mem_glueLat _).2 ⟨x, hx, 0, by simp⟩)
      · rw [mulVec_zero]; exact zero_mem_hat
      · intro a b ha hb; rw [mulVec_add]; exact add_mem_hat ha hb
      · intro c hc a ha; rw [mulVec_smul]; exact smul_mem_hat hc ha
    have h2 := smul_mem_hat ha (vA_mem_hat Y ((mem_glueLat (ι := ι) (z := z) (u := u) (L₀ := L₀) (x₀ := x₀)
      ((Tu D u)⁻¹ • z + ι x₀)).2 ⟨0, by simp, 1, by simp⟩))
    convert add_mem_hat h1 h2 using 1
    rw [vA_add, vA_smul, mulVec_add, mulVec_smul, mA_mulVec_vA, smul_add, smul_smul]
    abel

theorem IsGlueVec.congr {L₀ : Lat X} {f f' : Fin X.rank → EAf D} (h : IsGlueVec X u L₀ f) (hf : f - f' ∈ hat L₀) :
    IsGlueVec X u L₀ f' := by
  obtain ⟨d, rfl⟩ : ∃ d, f' = f - d := ⟨f - f', (sub_sub_cancel _ _).symm⟩
  rw [sub_sub_cancel] at hf
  refine ⟨?_, h.int, fun y hy => ?_, ?_, fun y hy => ?_⟩
  · rw [smul_sub]; exact sub_mem_hat h.mul_mem (smul_mem_hat (inc_Tu_mem u) hf)
  · rw [hA_sub_left]; exact sub_mem (h.pair y hy) (h.int d hf y hy)
  · have h1 : hA X d f ∈ OA D := by rw [← cjA_hA]; exact cjA_mem (h.pair d hf)
    have := sub_mem (sub_mem h.norm (h.pair d hf)) (sub_mem h1 (h.int d hf d hf))
    rw [hA_sub_left, hA_sub_right, hA_sub_right]
    convert this using 1
    ring
  · obtain ⟨a, ha, H⟩ := h.dual y hy
    refine ⟨a, ha, ?_⟩
    convert add_mem_hat H (smul_mem_hat ha hf) using 1
    rw [smul_sub]; abel

set_option maxHeartbeats 1600000 in

theorem mem_hat_glueLat_iff_dual (h : IsLine Y X ι z u) {L₀ : Lat X} {x₀ : X.V} (hg : IsGlueVec X u L₀ (vA X x₀))
    (x : Fin X.rank → EAf D) (a : EAf D) :
    mA Y X ι *ᵥ x + a • vA Y z ∈ hat (Formalism.L2.Herm.crdLat Y (glueLat Y X ι z u L₀ x₀)) ↔
      ∀ y ∈ hat (Formalism.L2.Herm.crdLat Y (glueLat Y X ι z u L₀ x₀)), hA Y y (mA Y X ι *ᵥ x + a • vA Y z) ∈ OA D := by
  simp only [mem_hat_glueLat]
  generalize vA X x₀ = f at hg
  have t := inc_inv_mul u
  constructor
  · rintro ⟨x₁, hx₁, a₁, ha₁, e⟩ _ ⟨x₂, hx₂, a₂, ha₂, rfl⟩
    have h1 : hA X x₂ f ∈ OA D := by rw [← cjA_hA]; exact cjA_mem (hg.pair _ hx₂)
    have := add_mem (add_mem (hg.int _ hx₂ _ hx₁) (mul_mem (cjA_mem ha₁) h1))
      (add_mem (mul_mem ha₂ (hg.pair _ hx₁)) (mul_mem (mul_mem ha₂ (cjA_mem ha₁)) hg.norm))
    rw [e, hA_flat h, hA_add_left, hA_add_right, hA_add_right, hA_smul_left, hA_smul_left, hA_smul_right, hA_smul_right,
      RingHom.map_mul, cjA_inc_inv]
    convert this using 1
    linear_combination (-(a₂ * cjA D a₁ * inc D (Tu D u)⁻¹)) * t
  · intro H
    obtain ⟨b, hb, hx⟩ := hg.dual x fun x' hx' => by
      have := H _ ⟨x', hx', 0, zero_mem _, rfl⟩
      rwa [hA_flat h, zero_smul, add_zero, zero_mul, zero_mul, zero_mul, sub_zero] at this
    have h1 := H _ ⟨0, zero_mem_hat, 1, one_mem _, rfl⟩
    rw [hA_flat h, zero_add, one_smul, one_mul] at h1
    have h2 := hg.pair _ hx
    rw [hA_sub_right, hA_smul_right] at h2
    have h3 : cjA D (a - b * inc D (Tu D u)⁻¹) ∈ OA D := by
      have := sub_mem (add_mem h2 (mul_mem (cjA_mem hb) hg.norm)) h1
      rw [RingHom.map_sub, RingHom.map_mul, cjA_inc_inv]
      convert this using 1
      linear_combination (-(cjA D a)) * t
    rw [cjA_mem_iff] at h3
    refine ⟨x - b • f - (a - b * inc D (Tu D u)⁻¹) • inc D (Tu D u) • f, sub_mem_hat hx (smul_mem_hat h3 hg.mul_mem),
      a * inc D (Tu D u), ?_, ?_⟩
    · convert add_mem (mul_mem h3 (inc_Tu_mem u)) hb using 1
      linear_combination b * t
    · congr 2
      · rw [smul_smul, sub_mul, mul_assoc b, t, mul_one, sub_smul]
        abel
      · linear_combination (-a) * t

end Flat

end GlobalTheory.AdIsom

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.OneParameterOperatorUnique
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped Classical

noncomputable section

namespace GlobalTheory.ArchimedeanUnitaryL2

open scoped ENNReal
open GlobalTheory.WeilAdm.HaarSplit

private theorem opensMeasurableSpace_pi_mixedSpace (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] :
    OpensMeasurableSpace (κ → mixedEmbedding.mixedSpace F) := by
  haveI : SecondCountableTopology (mixedEmbedding.mixedSpace F) := inferInstance
  haveI : BorelSpace (mixedEmbedding.mixedSpace F) := inferInstance
  infer_instance

theorem exists_haar (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ]
    (μ : Measure (κ → mixedEmbedding.mixedSpace F)) [μ.IsAddHaarMeasure]
    (g : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ) (hg : g ∈ GlobalTheory.WeilM.SB (κ → FiniteAdeleRing (𝓞 F) F)) (hg0 : g 0 ≠ 0) :
    ∃ μA : @Measure (κ → AdeleRing (𝓞 F) F) (borel _), @Measure.IsAddHaarMeasure _ _ _ (borel _) μA ∧
      ∃ c : ℝ≥0∞, c ≠ 0 ∧ c ≠ ⊤ ∧ ∀ f : SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ,
        ∫⁻ x, ‖GlobalTheory.WeilM.pureA F f g x‖ₑ ^ 2 ∂μA = c * ∫⁻ z, ‖f z‖ₑ ^ 2 ∂μ := by
  classical
  haveI := opensMeasurableSpace_pi_mixedSpace F κ
  letI : LocallyCompactSpace (FiniteAdeleRing (𝓞 F) F) := GlobalTheory.AdelicUnitaryTop.locallyCompact_finiteAdele F
  haveI : SecondCountableTopology (FiniteAdeleRing (𝓞 F) F) := GlobalTheory.AdelicUnitaryTop.secondCountable_finiteAdele F
  haveI : T2Space (FiniteAdeleRing (𝓞 F) F) := GlobalTheory.AdelicUnitaryTop.t2Space_finiteAdeleRing_of_numberField F
  letI : MeasurableSpace (FiniteAdeleRing (𝓞 F) F) := borel _
  haveI : BorelSpace (FiniteAdeleRing (𝓞 F) F) := ⟨rfl⟩
  letI mA : MeasurableSpace (κ → AdeleRing (𝓞 F) F) := borel _
  haveI : BorelSpace (κ → AdeleRing (𝓞 F) F) := ⟨rfl⟩
  obtain ⟨ν, hν⟩ : ∃ ν : Measure (κ → FiniteAdeleRing (𝓞 F) F), ν = Measure.addHaar := ⟨_, rfl⟩
  haveI : ν.IsAddHaarMeasure := by rw [hν]; infer_instance
  haveI : SFinite ν := by rw [hν]; infer_instance
  haveI : SFinite μ := inferInstance
  haveI : MeasurableAdd (κ → FiniteAdeleRing (𝓞 F) F) := inferInstance
  haveI : MeasurableAdd (κ → mixedEmbedding.mixedSpace F) := inferInstance
  let h : ((κ → mixedEmbedding.mixedSpace F) × (κ → FiniteAdeleRing (𝓞 F) F)) ≃ₜ (κ → AdeleRing (𝓞 F) F) :=
    { toEquiv := (splitE F κ).toEquiv
      continuous_toFun := continuous_splitE F κ
      continuous_invFun := continuous_splitE_symm F κ }
  let m := h.toMeasurableEquiv
  have hm : (m : _ → _) = splitE F κ := rfl
  have hgc : Continuous g := hg.1.continuous
  refine ⟨(μ.prod ν).map m, ?_, ∫⁻ y, ‖g y‖ₑ ^ 2 ∂ν, ?_, ?_, ?_⟩
  · rw [hm]
    exact AddEquiv.isAddHaarMeasure_map (μ.prod ν) (splitE F κ) (continuous_splitE F κ) (continuous_splitE_symm F κ)
  · apply ne_of_gt
    have hU : IsOpen {y | g y = g 0} := hg.1.isOpen_fiber _
    have hpos : 0 < ν {y | g y = g 0} := hU.measure_pos ν ⟨0, rfl⟩
    calc (0 : ℝ≥0∞) < ‖g 0‖ₑ ^ 2 * ν {y | g y = g 0} :=
          ENNReal.mul_pos (pow_ne_zero _ (enorm_ne_zero.2 hg0)) hpos.ne'
      _ = ∫⁻ y, {y | g y = g 0}.indicator (fun _ => ‖g 0‖ₑ ^ 2) y ∂ν :=
          (lintegral_indicator_const hU.measurableSet _).symm
      _ ≤ ∫⁻ y, ‖g y‖ₑ ^ 2 ∂ν := by
          refine lintegral_mono fun y => ?_
          by_cases hy : g y = g 0
          · simp [Set.indicator, hy]
          · simp [Set.indicator, hy]
  · have hs : HasCompactSupport fun y => ‖g y‖ ^ 2 := hg.2.comp_left (g := fun z : ℂ => ‖z‖ ^ 2) (by simp)
    have hint : Integrable (fun y => ‖g y‖ ^ 2) ν := (hgc.norm.pow 2).integrable_of_hasCompactSupport hs
    have h2 := hint.2
    unfold HasFiniteIntegral at h2
    refine ne_of_lt (lt_of_le_of_lt (le_of_eq ?_) h2)
    refine lintegral_congr fun y => ?_
    rw [enorm_pow, enorm_norm]
  · intro f
    rw [lintegral_map_equiv, hm]
    have hpt : ∀ p : (κ → mixedEmbedding.mixedSpace F) × (κ → FiniteAdeleRing (𝓞 F) F),
        ‖GlobalTheory.WeilM.pureA F f g (splitE F κ p)‖ₑ ^ 2 = ‖f p.1‖ₑ ^ 2 * ‖g p.2‖ₑ ^ 2 := by
      intro p
      rw [pureA_splitE, enorm_mul, mul_pow]
    simp_rw [hpt]
    rw [mul_comm]
    exact lintegral_prod_mul (μ := μ) (ν := ν) (f := fun z => ‖f z‖ₑ ^ 2) (g := fun y => ‖g y‖ₑ ^ 2)
      (f.continuous.measurable.enorm.pow_const 2).aemeasurable (hgc.measurable.enorm.pow_const 2).aemeasurable

theorem integral_sq_eq {V : Type} [TopologicalSpace V] [MeasurableSpace V] [OpensMeasurableSpace V] (μ : Measure V)
    {f : V → ℂ} (hf : Continuous f) : ∫ x, ‖f x‖ ^ 2 ∂μ = (∫⁻ x, ‖f x‖ₑ ^ 2 ∂μ).toReal := by
  have hc : Continuous fun x => ‖f x‖ ^ 2 := hf.norm.pow 2
  rw [integral_eq_lintegral_of_nonneg_ae (f := fun x => ‖f x‖ ^ 2)
    (Filter.Eventually.of_forall fun x => by positivity) hc.aestronglyMeasurable]
  congr 1
  refine lintegral_congr fun x => ?_
  rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm_eq_enorm]

theorem opensMeasurable (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] :
    OpensMeasurableSpace (κ → mixedEmbedding.mixedSpace F) := opensMeasurableSpace_pi_mixedSpace F κ

theorem snd_eq_zero {F : Type} [Field F] [NumberField F] {κ : Type} {z : κ → AF F} (hz : At (evI F) z) (i : κ) :
    (z i).2 = 0 := by
  have h := hz (((0 : InfiniteAdeleRing F), (1 : FiniteAdeleRing (𝓞 F) F)) : AdeleRing (𝓞 F) F) (by
    show InfiniteAdeleRing.ringEquiv_mixedSpace F 0 = 0
    exact map_zero _)
  have h2 : (((0 : InfiniteAdeleRing F), (1 : FiniteAdeleRing (𝓞 F) F)) * ((z i).1, (z i).2)).2 =
      (0 : InfiniteAdeleRing F × FiniteAdeleRing (𝓞 F) F).2 := congrArg Prod.snd (congrFun h i)
  simpa using h2

theorem integral_norm_sq_eq : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    {a a' : ℕ} (B : Base F E) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W),
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple B G X om om' → ∀ γ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Lines σ G.W,
    ∀ T : ℝ → SInf F (Fin a × Fin (a + a')) →ₗ[ℂ] SInf F (Fin a × Fin (a + a')),
    (∀ (t : ℝ) (f : SInf F (Fin a × Fin (a + a'))), Acts (evI F) (om (1, γ (Multiplicative.ofAdd t))) f (T t f)) →
    ∀ (μ : Measure (Fin a × Fin (a + a') → mixedEmbedding.mixedSpace F)), μ.IsAddHaarMeasure →
    ∀ (t : ℝ) (f : SInf F (Fin a × Fin (a + a'))), ∫ x, ‖T t f x‖ ^ 2 ∂μ = ∫ x, ‖f x‖ ^ 2 ∂μ := by
  intro F E _ _ _ _ _ σ a a' B G X om om' hT γ _ T hAct μ hμ t f
  classical
  haveI := hμ
  haveI := opensMeasurable F (Fin a × Fin (a + a'))
  set g : (Fin a × Fin (a + a') → FiniteAdeleRing (𝓞 F) F) → ℂ :=
    (GlobalTheory.SchANonzero.intPts F (Fin a × Fin (a + a'))).indicator 1 with hgdef
  have hgSB : g ∈ GlobalTheory.WeilM.SB _ := GlobalTheory.SchANonzero.indicator_intPts_mem_SB F _
  have h0mem : (0 : Fin a × Fin (a + a') → FiniteAdeleRing (𝓞 F) F) ∈ GlobalTheory.SchANonzero.intPts F _ := by
    intro i _ v
    simp
  have hg0 : g 0 ≠ 0 := by
    rw [hgdef, Set.indicator_of_mem h0mem]
    simp
  obtain ⟨μA, hμA, c, hc0, hctop, hc⟩ := exists_haar F (Fin a × Fin (a + a')) μ g hgSB hg0
  have hU := (GlobalTheory.WeilM.IsUWeilPair.isUSplitting hT.weil).unit
  let r : (Fin a × Fin (a + a') → AF F) → ℂ := fun x => g (fun i => (x i).2)
  have htens : ∀ φ : SInf F (Fin a × Fin (a + a')), tens (evI F) (φ : _ → ℂ) r = GlobalTheory.WeilM.pureA F φ g :=
    fun φ => rfl
  have hRest : Rest (evI F) (f : _ → ℂ) r := by
    refine ⟨fun x z hz => ?_, ?_⟩
    · show g _ = g _
      congr 1
      funext i
      show (x i).2 + (z i).2 = (x i).2
      rw [snd_eq_zero hz i, add_zero]
    · rw [htens]
      exact Submodule.subset_span ⟨f, g, hgSB, rfl⟩
  have hA := hAct t f r hRest
  rw [htens, htens] at hA
  have hmem : GlobalTheory.WeilM.pureA F f g ∈ GlobalTheory.WeilM.schA F (Fin a × Fin (a + a')) :=
    Submodule.subset_span ⟨f, g, hgSB, rfl⟩
  have hu := hU μA hμA (1, γ (Multiplicative.ofAdd t)) _ hmem
  rw [hA, hc, hc] at hu
  have hl := (ENNReal.mul_right_inj hc0 hctop).1 hu
  rw [integral_sq_eq μ (T t f).continuous, integral_sq_eq μ f.continuous, hl]

end GlobalTheory.ArchimedeanUnitaryL2

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SelfDualLatticeImageAdelicUnitary
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH NumberField IsDedekindDomain Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Lev Formalism.IndefR.Links Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice
open Formalism.IndefR.Datum (IsSelfDualC)
open GlobalTheory.IndefiniteRowSideFullHecke.FlatSpaceComponents GlobalTheory.AdIsom
open scoped TensorProduct

namespace GlobalTheory.AdIsomImage

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open GlobalTheory.NormSum.AdLattice (lat)

section Ring

variable {A : Type} [CommRing A] {n : ℕ}

theorem inv_mul_mulVec (g β : GL (Fin n) A) (y : Fin n → A) :
    ((g * β)⁻¹).val *ᵥ y = (β⁻¹).val *ᵥ ((g⁻¹).val *ᵥ y) := by
  rw [_root_.mul_inv_rev, Units.val_mul, Matrix.mulVec_mulVec]

theorem gram_mul (σ : A →+* A) (J : Matrix (Fin n) (Fin n) A) (g β : GL (Fin n) A)
    (h : Formalism.UG.cT σ g.val * J * g.val = J) :
    Formalism.UG.cT σ (g * β).val * J * (g * β).val = Formalism.UG.cT σ β.val * J * β.val := by
  have hc : Formalism.UG.cT σ (g * β).val = Formalism.UG.cT σ β.val * Formalism.UG.cT σ g.val := by
    rw [Units.val_mul]
    exact GlobalTheory.StdFrames.cT_mul' σ _ _
  calc Formalism.UG.cT σ (g * β).val * J * (g * β).val
      = Formalism.UG.cT σ β.val * (Formalism.UG.cT σ g.val * J * g.val) * β.val := by
        rw [hc, Units.val_mul]
        simp only [Matrix.mul_assoc]
    _ = Formalism.UG.cT σ β.val * J * β.val := by rw [h]

end Ring

variable {D : D7}

theorem fin_cA (z : Formalism.L2.Theta.AE D) :
    ((swapAE D).comp (finPart D)) (cA D z) = cjA D (((swapAE D).comp (finPart D)) z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul a e =>
    simp [cA, cjA, finPart, swapAE, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR, Formalism.UG.sigR]
  | add x y hx hy => simp only [map_add, hx, hy]

theorem finE_unitary (V : HSp D) (g : GA D V) :
    Formalism.UG.cT (cjA D) (finE V g).val * V.gram.map (inc D) * (finE V g).val = V.gram.map (inc D) := by
  have hg : Formalism.UG.cT (cA D) (g.1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)) * V.gram.map (incA D) *
      (g.1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)) = V.gram.map (incA D) := g.2
  have key := congrArg ((swapAE D).comp (finPart D)).mapMatrix hg
  simp only [RingHom.mapMatrix_apply, Matrix.map_mul] at key
  have hcT : ∀ M : Matrix (Fin V.rank) (Fin V.rank) (AE D),
      (Formalism.UG.cT (cA D) M).map ((swapAE D).comp (finPart D)) =
        Formalism.UG.cT (cjA D) (M.map ((swapAE D).comp (finPart D))) := by
    intro M
    ext i j
    simp only [Formalism.UG.cT, Matrix.map_apply, Matrix.transpose_apply]
    exact fin_cA (M j i)
  have hJ : (V.gram.map (incA D)).map ((swapAE D).comp (finPart D)) = V.gram.map (inc D) := by
    rw [Matrix.map_map]
    congr 1
  have hfin : ((finE V g).val : Matrix (Fin V.rank) (Fin V.rank) (EAf D)) =
      (g.1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)).map ((swapAE D).comp (finPart D)) := rfl
  rw [hcT, hJ] at key
  rw [hfin]
  exact key

theorem carries_iff {n : ℕ} (g : GL (Fin n) (EAf D)) (Λ Λ' : Submodule (𝓞 D.host.E) (Fin n → D.host.E)) :
    Formalism.L2.Herm.Carries g Λ Λ' ↔ ∀ y, y ∈ hat Λ' ↔ (g⁻¹).val *ᵥ y ∈ hat (D := D) Λ := by
  unfold Formalism.L2.Herm.Carries
  exact forall_congr' fun y => Iff.rfl

theorem imageSt (D : D7) : ImageSt D := by
  intro V Λ hΛ d _hd
  obtain ⟨β, rfl, hβ⟩ := exists_orth hΛ
  have hcar : Formalism.L2.Herm.Carries (finE V d) (lat β) (lat (finE V d * β)) := by
    rw [carries_iff]
    intro y
    rw [mem_hat_lat, mem_hat_lat, inv_mul_mulVec]
  have hgram : GlobalTheory.StdFrames.gramOf V (finE V d * β) = 1 :=
    (gram_mul (cjA D) (V.gram.map (inc D)) (finE V d) β (finE_unitary V d)).trans hβ
  refine ⟨⟨lat (finE V d * β), GlobalTheory.NormSum.AdLattice.lat_isLattice _, hcar⟩, fun Λ' hΛ' hc => ?_⟩
  have heq : Λ' = lat (finE V d * β) := by
    ext x
    rw [← inc_mem_hat_iff hΛ' x, ← inc_mem_hat_iff (GlobalTheory.NormSum.AdLattice.lat_isLattice (finE V d * β)) x]
    rw [carries_iff] at hc hcar
    rw [hc, hcar]
  rw [heq]
  exact isSelfDualC_lat (by rw [hgram]; exact unimod_one)

end GlobalTheory.AdIsomImage

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilLatticeIntertwinerCoefficientAtPlaceStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep GlobalTheory.FinZeta GlobalTheory.AdelicScalar GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.LiftRows
open Formalism.IndefR.Lev (levG levChi IsBaseFrame)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke dosetInd IsCommensurated)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LGrp (IsUnitarisable IsIrrSmooth bcParam)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weil_latticeIntertwiner_coefficient_at_place : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (hψ : IsStdChar D ψ (-1)) (lam : ℕ →* ℂ) (w₀ : 𝓞 D.host.E) (Om : GA D S × GA D T →* Module.End ℂ (GlobalTheory.FinWeilO.thetaSub ψ S T)), GlobalTheory.FinWeilO.IsLatRep hψ.1 (frameLat S) (frameLat T) w₀ lam Om → ∀ (μ : Measure (WO S T)) (𝓕 : Set (WO S T)), IsCovolOne (ratL T S) μ 𝓕 → ∀ (v : HeightOneSpectrum (𝓞 D.host.F)) (a : Gv T v) (f₁ f₂ : GlobalTheory.FinWeilO.thetaSub ψ S T), VacFin ψ S T v f₁ → VacFin ψ S T v f₂ → l2 μ 𝓕 (Om (1, embV T v a) f₁ : WO S T → ℂ) f₂ = (lam (GlobalTheory.FinWeil.idx (GlobalTheory.FinWeilO.latF S T (frameLat S) (frameLat T)) ((GlobalTheory.FinWeilO.latF S T (frameLat S) (frameLat T)).map (GlobalTheory.FinWeilO.rhoF S T (1, embV T v a)))))⁻¹ * l2 μ 𝓕 (f₁ : WO S T → ℂ) f₂ := by
  first | exact @GlobalTheory.LatCoef.latCoef | exact GlobalTheory.LatCoef.latCoef | (intros; apply GlobalTheory.LatCoef.latCoef <;> assumption)
end

