import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LevelMatchIff
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0013
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0335
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0355
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0004
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0118
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0356
import Formalism.FormalDegreeBessel.FormalDegreeRatio.Bundle0002
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ConvolutionSmoothL2
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.Bundle0001
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.DiscreteSpectrumKFiniteDecomposition
import Formalism.HarderNarasimhan.ShiftInvariance
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CovolumeIntegralUnipotentStabilizerOfTerm
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0011
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MeasurePreservingReindex
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0240
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0278
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TruncatedLeastLatticeSizeLipschitzProperties
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.DiscreteSeriesSUIff
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.Bundle0001
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0314
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0275
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0008
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsExactGramFrameInTermClass
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.NGData
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.TermLoc
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.Bundle0001
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Vanish
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0012
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.PlacesOf

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.AdelicColumnsLatticeDivisibleByLevelAwayChosen
section
open MeasureTheory NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ColDict GlobalTheory.St GlobalTheory.St.G
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.St.G.FrameFull

variable {D : D7}

theorem mL_div (I : Formalism.MainNotions.S.AutInst) (m : ℕ) :
    ∀ v ∈ mL I m, ∃ z ∈ I.Lf, v = (m : I.E ⊗[I.F] Af I.F) • z := by
  intro v hv
  induction hv using Submodule.span_induction with
  | mem x hx => exact hx
  | zero => exact ⟨0, I.Lf.zero_mem, (smul_zero _).symm⟩
  | add x y _ _ hx hy =>
    obtain ⟨a, ha, rfl⟩ := hx
    obtain ⟨b, hb, rfl⟩ := hy
    exact ⟨a + b, I.Lf.add_mem ha hb, (smul_add _ _ _).symm⟩
  | smul c x _ hx =>
    obtain ⟨a, ha, rfl⟩ := hx
    exact ⟨c • a, I.Lf.smul_mem c ha, smul_comm _ _ _⟩

theorem embA_smul (X : HidaSetting D) (wt : (VS D).V ≃ₗ[D.host.E] (VS D).V)
    (ιA : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F ≃+* D.host.E ⊗[D.host.F] Ad D.host.F)
    (c : D.host.E ⊗[D.host.F] Ad D.host.F) (x : Fin (D.R.N 0) → D.host.E ⊗[D.host.F] Ad D.host.F) :
    embA X wt ιA (c • x) = ιA.symm c • embA X wt ιA x := by
  simp only [embA, Pi.smul_apply, smul_eq_mul, map_mul, mul_smul, Finset.smul_sum]

theorem embA_zero (X : HidaSetting D) (wt : (VS D).V ≃ₗ[D.host.E] (VS D).V)
    (ιA : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F ≃+* D.host.E ⊗[D.host.F] Ad D.host.F) :
    embA X wt ιA 0 = 0 := by
  simp [embA]

theorem step (X : HidaSetting D) (wt : (VS D).V ≃ₗ[D.host.E] (VS D).V)
    (ιA : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F ≃+* D.host.E ⊗[D.host.F] Ad D.host.F)
    (hmem : ∀ x, x ∈ hat D.host.F (Mq wt) ↔ embA X wt ιA x ∈ X.B.I.Lf)
    (hinj : Function.Injective (embA X wt ιA))
    (c : D.host.E ⊗[D.host.F] Ad D.host.F) (y : Fin (D.R.N 0) → D.host.E ⊗[D.host.F] Ad D.host.F)
    (m : ℕ) (w : VA X.B.I) (hw : w ∈ X.B.I.Lf)
    (hwe : embA X wt ιA (c • y) = (m : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • w) :
    ∃ z ∈ hat D.host.F (Mq wt), c • y = (m : D.host.E ⊗[D.host.F] Ad D.host.F) • z := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · refine ⟨0, Submodule.zero_mem _, ?_⟩
    rw [smul_zero]
    apply hinj
    rw [hwe, embA_zero, Nat.cast_zero, zero_smul]
  · have hF : IsUnit ((m : D.host.F)) := (Nat.cast_ne_zero.mpr hm.ne').isUnit
    have hR : IsUnit ((m : D.host.E ⊗[D.host.F] Ad D.host.F)) := by
      simpa using hF.map (algebraMap D.host.F (D.host.E ⊗[D.host.F] Ad D.host.F))
    obtain ⟨t, ht⟩ := hR.exists_right_inv
    refine ⟨t • (c • y), ?_, ?_⟩
    · rw [hmem, embA_smul, hwe, smul_smul, ← map_natCast ιA.symm m, ← map_mul, mul_comm, ht, map_one, one_smul]
      exact hw
    · rw [smul_smul, ht, one_smul]

theorem symm_unit (X : HidaSetting D)
    (ιA : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F ≃+* D.host.E ⊗[D.host.F] Ad D.host.F) (hI : IsAdeleIso X ιA) :
    ιA.symm (1 - ιA X.ew - Formalism.UG.sigR (Formalism.L2.Forms.sigD D) (Ad D.host.F) (ιA X.ew)) =
      1 - X.ew - sigA X.B.I X.ew := by
  have h := GlobalTheory.St.G.IotaSigmaCompatibility.iotaA_sigA D X ιA hI X.ew
  apply ιA.injective
  rw [RingEquiv.apply_symm_apply, map_sub, map_sub, map_one]
  exact congrArg (fun t => 1 - ιA X.ew - t) h.symm

theorem emb_mem (X : HidaSetting D) (wt : (VS D).V ≃ₗ[D.host.E] (VS D).V)
    (ιA : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F ≃+* D.host.E ⊗[D.host.F] Ad D.host.F) (hI : IsAdeleIso X ιA)
    (y : Fin (D.R.N 0) → D.host.E ⊗[D.host.F] Ad D.host.F) (hy : embA X wt ιA y ∈ X.B.I.Lf) :
    ∃ w ∈ X.B.I.Lf, embA X wt ιA
      ((1 - ιA X.ew - Formalism.UG.sigR (Formalism.L2.Forms.sigD D) (Ad D.host.F) (ιA X.ew)) • y) =
      ((D.host.g 0 * D.host.g 1 : ℕ) : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • w := by
  rw [embA_smul, symm_unit X ιA hI]
  obtain ⟨w, hw, hw'⟩ := mL_div X.B.I X.B.g _ (X.ew_full _ hy)
  exact ⟨w, hw, by rw [hw', X.g_eq]⟩

theorem eps_full : ∀ (D : D7) (X : HidaSetting D) (u : D.what₂.Word) (wt : (VS D).V ≃ₗ[D.host.E] (VS D).V) (ιA : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F ≃+* D.host.E ⊗[D.host.F] Ad D.host.F), WittX X u wt → IsAdeleIso X ιA → ∀ y ∈ hat D.host.F (Mq wt), ∃ z ∈ hat D.host.F (Mq wt), (1 - ιA X.ew - Formalism.UG.sigR (Formalism.L2.Forms.sigD D) (Ad D.host.F) (ιA X.ew)) • y = ((D.host.g 0 * D.host.g 1 : ℕ) : D.host.E ⊗[D.host.F] Ad D.host.F) • z := by
  intro D X u wt ιA hW hI y hy
  obtain ⟨hmem, -, hinj, -⟩ := GlobalTheory.T.adelicColumnLattice_eq_spanPart_transportedFrame D X u wt ιA hW hI
  obtain ⟨w, hw, hwe⟩ := emb_mem X wt ιA hI y ((hmem y).1 hy)
  exact step X wt ιA hmem hinj _ y _ w hw hwe

end GlobalTheory.St.G.FrameFull
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.AdelicEmbeddingBasisLiesInModule
section
open MeasureTheory NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ColDict GlobalTheory.St GlobalTheory.St.G
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.St.G.TransportCong

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1600000 in

theorem inModL_of_inMod_embA : ∀ (D : D7) (X : HidaSetting D) (u : D.what₂.Word) (wt : (VS D).V ≃ₗ[D.host.E] (VS D).V) (ιA : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F ≃+* D.host.E ⊗[D.host.F] Ad D.host.F), WittX X u wt → IsAdeleIso X ιA → ∀ (b bd : Fin D.R.k → Fin (D.R.N 0) → D.host.E ⊗[D.host.F] Ad D.host.F) (y : Fin (D.R.N 0) → D.host.E ⊗[D.host.F] Ad D.host.F), InMod X.B.I X.B.g (Set.range (fun i => embA X wt ιA (b i)) ∪ Set.range (fun i => embA X wt ιA (bd i))) (embA X wt ιA y) → InModL (hat D.host.F (Mq wt)) (D.host.g 0 * D.host.g 1) (Set.range b ∪ Set.range bd) y := by
  intro D X u wt ιA hW hA b bd y hy
  obtain ⟨h1, -, hinj, -⟩ := GlobalTheory.T.adelicColumnLattice_eq_spanPart_transportedFrame D X u wt ιA hW hA
  have hadd : ∀ x x', embA X wt ιA (x + x') = embA X wt ιA x + embA X wt ιA x' := by
    intro x x'; simp only [embA, Pi.add_apply, map_add, add_smul, Finset.sum_add_distrib]
  have hsmul : ∀ (c : D.host.E ⊗[D.host.F] Ad D.host.F) x,
      embA X wt ιA (c • x) = ιA.symm c • embA X wt ιA x := by
    intro c x; simp only [embA, Pi.smul_apply, smul_eq_mul, map_mul, mul_smul, Finset.smul_sum]
  have hzero : embA X wt ιA 0 = 0 := by simp [embA]
  have hsub : ∀ x x', embA X wt ιA (x - x') = embA X wt ιA x - embA X wt ιA x' := by
    intro x x'
    have := hadd (x - x') x'
    rw [sub_add_cancel] at this
    rw [this, add_sub_cancel_right]
  have hS : (Set.range (fun i => embA X wt ιA (b i)) ∪ Set.range (fun i => embA X wt ιA (bd i))) =
      embA X wt ιA '' (Set.range b ∪ Set.range bd) := by
    rw [Set.image_union, ← Set.range_comp, ← Set.range_comp]; rfl
  have hspan : ∀ s ∈ Submodule.span (IntAf X.B.I.F X.B.I.E) (embA X wt ιA '' (Set.range b ∪ Set.range bd)),
      ∃ s' ∈ Submodule.span (OAd D.host.F D.host.E) (Set.range b ∪ Set.range bd), embA X wt ιA s' = s := by
    intro s hs
    induction hs using Submodule.span_induction with
    | mem x hx => obtain ⟨t, ht, rfl⟩ := hx; exact ⟨t, Submodule.subset_span ht, rfl⟩
    | zero => exact ⟨0, Submodule.zero_mem _, hzero⟩
    | add x x' _ _ ihx ihx' =>
      obtain ⟨s1, hs1, rfl⟩ := ihx
      obtain ⟨s2, hs2, rfl⟩ := ihx'
      exact ⟨s1 + s2, Submodule.add_mem _ hs1 hs2, hadd _ _⟩
    | smul a x _ ihx =>
      obtain ⟨s1, hs1, rfl⟩ := ihx
      have ha : ιA (a : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) ∈ OAd D.host.F D.host.E := (hA.2 a).1 a.2
      refine ⟨(⟨_, ha⟩ : OAd D.host.F D.host.E) • s1, Submodule.smul_mem _ _ hs1, ?_⟩
      rw [Subring.smul_def, hsmul, RingEquiv.symm_apply_apply, Subring.smul_def]
  have hmL : ∀ w ∈ mL X.B.I X.B.g, ∃ x ∈ X.B.I.Lf,
      w = ((X.B.g : ℕ) : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • x := by
    intro w hw
    induction hw using Submodule.span_induction with
    | mem x hx => obtain ⟨x', hx', rfl⟩ := hx; exact ⟨x', hx', rfl⟩
    | zero => exact ⟨0, Submodule.zero_mem _, (smul_zero _).symm⟩
    | add x x' _ _ ihx ihx' =>
      obtain ⟨a1, h1, rfl⟩ := ihx
      obtain ⟨a2, h2, rfl⟩ := ihx'
      exact ⟨a1 + a2, Submodule.add_mem _ h1 h2, (smul_add _ _ _).symm⟩
    | smul a x _ ihx =>
      obtain ⟨a1, h1, rfl⟩ := ihx
      refine ⟨a • a1, Submodule.smul_mem _ _ h1, ?_⟩
      simp only [Subring.smul_def, smul_smul, mul_comm]
  unfold InMod at hy
  rw [hS] at hy
  obtain ⟨s, hs, w, hw, hsw⟩ := Submodule.mem_sup.mp hy
  obtain ⟨s', hs', rfl⟩ := hspan s hs
  obtain ⟨x, hx, rfl⟩ := hmL w hw
  rw [X.g_eq] at hsw
  rcases Nat.eq_zero_or_pos (D.host.g 0 * D.host.g 1) with h0 | hpos
  · refine ⟨s', hs', 0, Submodule.zero_mem _, ?_⟩
    rw [smul_zero, add_zero]
    apply hinj
    rw [← hsw, h0, Nat.cast_zero, zero_smul, add_zero]
  · have hu : IsUnit (((D.host.g 0 * D.host.g 1 : ℕ)) : D.host.E ⊗[D.host.F] Ad D.host.F) := by
      rw [← map_natCast (algebraMap D.host.F (D.host.E ⊗[D.host.F] Ad D.host.F))]
      exact (IsUnit.mk0 _ (Nat.cast_ne_zero.mpr hpos.ne')).map _
    obtain ⟨c, hc⟩ := hu
    refine ⟨s', hs', ((c⁻¹ : (D.host.E ⊗[D.host.F] Ad D.host.F)ˣ) : D.host.E ⊗[D.host.F] Ad D.host.F) • (y - s'), ?_, ?_⟩
    · rw [h1, hsmul, hsub, ← hsw, add_sub_cancel_left, smul_smul, ← map_natCast ιA.symm, ← hc,
        ← map_mul, Units.inv_mul, map_one, one_smul]
      exact hx
    · rw [smul_smul, ← hc, Units.mul_inv, one_smul, add_sub_cancel]

end GlobalTheory.St.G.TransportCong
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.BesselFunctionEqScalarSqNormalisedBesselTorusCon
section
open Formalism.FourierDecayAlt GlobalTheory.ThA MeasureTheory Formalism.QuantumDeterminants Matrix
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.ThA

private lemma inv_mul_comm_of_mul_comm {n : Type*} [Fintype n] [DecidableEq n] (a h : Matrix n n ℂ)
    (hah : a * h = h * a) : h⁻¹ * a = a * h⁻¹ := by
  by_cases hh : IsUnit h.det
  · calc h⁻¹ * a = h⁻¹ * (a * h) * h⁻¹ := by
          rw [Matrix.mul_assoc, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hh, Matrix.mul_one]
      _ = h⁻¹ * (h * a) * h⁻¹ := by rw [hah]
      _ = a * h⁻¹ := by rw [← Matrix.mul_assoc h⁻¹ h a, Matrix.nonsing_inv_mul _ hh, Matrix.one_mul]
  · rw [Matrix.nonsing_inv_apply_not_isUnit _ hh, Matrix.zero_mul, Matrix.mul_zero]

private lemma inv_mul_conj_mul_conj_eq_conj_of_commute {n : Type*} [Fintype n] [DecidableEq n] (a H M g M' H' : Matrix n n ℂ)
    (ha : IsUnit a.det) (c1 : a * H = H * a) (c2 : a * H' = H' * a) :
    H⁻¹ * (a * M * a⁻¹)⁻¹ * g * (a * M' * a⁻¹) * H' =
      a * (H⁻¹ * M⁻¹ * (a⁻¹ * g * a) * M' * H') * a⁻¹ := by
  have e1 : (a * M * a⁻¹)⁻¹ = a * M⁻¹ * a⁻¹ := by
    rw [Matrix.mul_inv_rev, Matrix.mul_inv_rev, Matrix.nonsing_inv_nonsing_inv _ ha, Matrix.mul_assoc]
  have d1 : H⁻¹ * a = a * H⁻¹ := inv_mul_comm_of_mul_comm a H c1
  have d2 : a⁻¹ * H' = H' * a⁻¹ := inv_mul_comm_of_mul_comm H' a c2.symm
  rw [e1]
  simp only [Matrix.mul_assoc]
  rw [d2, ← Matrix.mul_assoc H⁻¹ a, d1, Matrix.mul_assoc]

theorem besselJ_conj {Wp Wq : Type} [NormedAddCommGroup Wp] [NormedSpace ℂ Wp] [NormedAddCommGroup Wq]
    [NormedSpace ℂ Wq] (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (c c' : ℂ)
    (π : B.Mat k r → (Wp →L[ℂ] Wp)) (π' : B.Mat k r → (Wq →L[ℂ] Wq))
    (μW μN μW' : Measure (Mt k r)) [SFinite μW] [SFinite μN] [SFinite μW']
    (hW : μW (UWset k r z)ᶜ = 0) (hN : μN (Nset k r)ᶜ = 0) (hW' : μW' (UWset k r z')ᶜ = 0)
    (a : B.Mat k r) (ha : IsUnit a.det)
    (hc : ∀ h ∈ UWset k r z, a * h = h * a) (hc' : ∀ h ∈ UWset k r z', a * h = h * a)
    (hp : ∀ n ∈ Nset k r, psi k r z c (a * n * a⁻¹) = psi k r z c' n)
    (hp' : ∀ n ∈ Nset k r, psi k r z' c (a * n * a⁻¹) = psi k r z' c' n)
    (F : B.Mat k r → (Wq →L[ℂ] Wp)) (g : B.Mat k r) :
    besselJ k r z z' c π π' μW (μN.map (conjM a)) μW' F g =
      besselJ k r z z' c' π π' μW μN μW' (fun x => F (a * x * a⁻¹)) (a⁻¹ * g * a) := by
  have hm : Measurable (conjM (k := k) (r := r) a) := (BesselUnitaryEquiv.conjE (k := k) (r := r) a ha).measurable
  let E : Mt k r ≃ᵐ Mt k r := BesselUnitaryEquiv.conjE (k := k) (r := r) a ha
  let Φ : (Mt k r × Mt k r) × (Mt k r × Mt k r) ≃ᵐ (Mt k r × Mt k r) × (Mt k r × Mt k r) :=
    ((MeasurableEquiv.refl (Mt k r)).prodCongr E).prodCongr ((MeasurableEquiv.refl (Mt k r)).prodCongr E)
  have hpm : ∀ (ν : Measure (Mt k r)) [SFinite ν],
      (ν.prod μN).map (Prod.map id (conjM a)) = ν.prod (μN.map (conjM a)) := by
    intro ν _
    rw [← Measure.map_prod_map _ _ measurable_id hm, Measure.map_id]
  have hμ : (μW.prod (μN.map (conjM a))).prod (μW'.prod (μN.map (conjM a))) =
      ((μW.prod μN).prod (μW'.prod μN)).map Φ := by
    rw [← hpm μW, ← hpm μW', Measure.map_prod_map _ _ (measurable_id.prodMap hm) (measurable_id.prodMap hm)]
    rfl
  have aW : ∀ᵐ x ∂μW, x ∈ UWset k r z := ae_iff.2 hW
  have aN : ∀ᵐ x ∂μN, x ∈ Nset k r := ae_iff.2 hN
  have aW' : ∀ᵐ x ∂μW', x ∈ UWset k r z' := ae_iff.2 hW'
  have q1 : ∀ᵐ p ∂((μW.prod μN).prod (μW'.prod μN)), p.1.1 ∈ UWset k r z :=
    (Measure.quasiMeasurePreserving_fst (μ := μW.prod μN) (ν := μW'.prod μN)).ae
      ((Measure.quasiMeasurePreserving_fst (μ := μW) (ν := μN)).ae aW)
  have q2 : ∀ᵐ p ∂((μW.prod μN).prod (μW'.prod μN)), p.1.2 ∈ Nset k r :=
    (Measure.quasiMeasurePreserving_fst (μ := μW.prod μN) (ν := μW'.prod μN)).ae
      ((Measure.quasiMeasurePreserving_snd (μ := μW) (ν := μN)).ae aN)
  have q3 : ∀ᵐ p ∂((μW.prod μN).prod (μW'.prod μN)), p.2.1 ∈ UWset k r z' :=
    (Measure.quasiMeasurePreserving_snd (μ := μW.prod μN) (ν := μW'.prod μN)).ae
      ((Measure.quasiMeasurePreserving_fst (μ := μW') (ν := μN)).ae aW')
  have q4 : ∀ᵐ p ∂((μW.prod μN).prod (μW'.prod μN)), p.2.2 ∈ Nset k r :=
    (Measure.quasiMeasurePreserving_snd (μ := μW.prod μN) (ν := μW'.prod μN)).ae
      ((Measure.quasiMeasurePreserving_snd (μ := μW') (ν := μN)).ae aN)
  unfold besselJ
  rw [hμ, integral_map_equiv]
  refine integral_congr_ae ?_
  filter_upwards [q1, q2, q3, q4] with p h1 h2 h3 h4
  have hΦ : Φ p = ((p.1.1, conjM a p.1.2), (p.2.1, conjM a p.2.2)) := rfl
  have e2 : Matrix.of (conjM a p.1.2) = a * Matrix.of p.1.2 * a⁻¹ := rfl
  have e4 : Matrix.of (conjM a p.2.2) = a * Matrix.of p.2.2 * a⁻¹ := rfl
  rw [hΦ]
  dsimp only
  rw [e2, e4, hp (Matrix.of p.1.2) h2, hp' (Matrix.of p.2.2) h4,
    inv_mul_conj_mul_conj_eq_conj_of_commute a (Matrix.of p.1.1) (Matrix.of p.1.2) g (Matrix.of p.2.2) (Matrix.of p.2.1) ha
      (hc (Matrix.of p.1.1) h1) (hc' (Matrix.of p.2.1) h3)]

theorem besselJ_smul {Wp Wq : Type} [NormedAddCommGroup Wp] [NormedSpace ℂ Wp] [NormedAddCommGroup Wq]
    [NormedSpace ℂ Wq] (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (c : ℂ)
    (π : B.Mat k r → (Wp →L[ℂ] Wp)) (π' : B.Mat k r → (Wq →L[ℂ] Wq))
    (μW μN μW' : Measure (Mt k r)) [SFinite μW] [SFinite μN] [SFinite μW'] (t : ℝ≥0∞)
    (F : B.Mat k r → (Wq →L[ℂ] Wp)) (g : B.Mat k r) :
    besselJ k r z z' c π π' μW (t • μN) μW' F g =
      ((t.toReal ^ 2 : ℝ) : ℂ) • besselJ k r z z' c π π' μW μN μW' F g := by
  unfold besselJ
  rw [Measure.prod_smul_right, Measure.prod_smul_right, Measure.prod_smul_left,
    Measure.prod_smul_right, smul_smul,
    integral_smul_measure, ENNReal.toReal_mul, ← pow_two, Complex.coe_smul]

theorem besselJ_changeFrame : ∀ (k r : ℕ) (L : Formalism.MainNotions.S.LocBessel k r) (μsec : ℂ → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) (Bs : B.RealPlaceData k r L.Wp L.Wq) (cN : ℝ) (F : B.Mat k r → (L.Wq →L[ℂ] L.Wp)), IsStdOf L μsec Bs → IsRatioN k r cN → L.c ≠ 0 → L.κN ≠ 0 → L.κN ≠ ⊤ → ∀ g : B.Mat k r, L.J F g = ((lamN L cN ^ 2 : ℝ) : ℂ) • B.JF Bs (conjF (cStd / L.c) F) ((aT k r (cStd / L.c))⁻¹ * g * aT k r (cStd / L.c)) := by
  intro k r L μsec Bs cN F hstd hR hc hκ0 hκT g
  obtain ⟨hz, hz', hπ, hπ', hμW, hμW', hμN, -⟩ := hstd
  have hα : cStd / L.c ≠ 0 := div_ne_zero (by simp [cStd]) hc
  have hcα : L.c * (cStd / L.c) = cStd := by field_simp
  set α := cStd / L.c with hαdef
  obtain ⟨-, hT, -, -⟩ := GlobalTheory.T.besselTorusElement_properties k r α hα
  obtain ⟨hcz, hnz⟩ := hT L.z L.hz.1
  obtain ⟨hcz', hnz'⟩ := hT L.z' L.hz'.1
  have hmap := GlobalTheory.T.lebesgue_rootCoordinates_map_besselTorus_conj k r α hα
  have ha : IsUnit (aT k r α).det := by
    rw [aT, Matrix.det_diagonal]
    refine isUnit_iff_ne_zero.mpr (Finset.prod_ne_zero_iff.mpr fun i _ => ?_)
    split_ifs
    · exact pow_ne_zero _ hα
    · exact one_ne_zero
    · exact inv_ne_zero (pow_ne_zero _ (star_ne_zero.mpr hα))
  have hp : ∀ w : Fin (2 * r + k + 1) → ℂ,
      (∀ n ∈ Nset k r, ell k r w (aT k r α * n * (aT k r α)⁻¹) = α * ell k r w n) →
      ∀ n ∈ Nset k r, psi k r w L.c (aT k r α * n * (aT k r α)⁻¹) = psi k r w cStd n := by
    intro w hw n hn
    simp only [psi, hw n hn, ← mul_assoc, hcα]
  haveI : IsFiniteMeasure L.μW := ⟨by rw [L.hμW.2]; exact ENNReal.one_lt_top⟩
  haveI : IsFiniteMeasure L.μW' := ⟨by rw [L.hμW'.2]; exact ENNReal.one_lt_top⟩
  have hNc : (D.muN k r) (Nset k r)ᶜ = 0 := by rw [← hμN]; exact Bs.haarN.conc
  haveI : IsFiniteMeasureOnCompacts (D.muN k r) :=
    ⟨fun K hK => by rw [← hμN]; exact Bs.haarN.finite_compact K hK⟩
  have hW : L.μW (UWset k r L.z)ᶜ = 0 := L.hμW.1.2.2.1
  have hW' : L.μW' (UWset k r L.z')ᶜ = 0 := L.hμW'.1.2.2.1
  have hx : 0 < ‖α‖ ^ B.kap k r := pow_pos (norm_pos_iff.mpr hα) _
  have hone : ENNReal.ofReal (‖α‖ ^ B.kap k r) * ENNReal.ofReal ((‖α‖ ^ B.kap k r)⁻¹) = 1 := by
    rw [← ENNReal.ofReal_mul hx.le, mul_inv_cancel₀ hx.ne', ENNReal.ofReal_one]
  have hLμN : L.μN = (L.κN * ENNReal.ofReal cN * ENNReal.ofReal (‖α‖ ^ B.kap k r)) •
      (D.muN k r).map (conjM (aT k r α)) := by
    rw [hmap, smul_smul, mul_assoc (L.κN * ENNReal.ofReal cN), hone, mul_one, mul_smul, ← hR.2]
    simp only [Formalism.MainNotions.S.LocBessel.μN, Formalism.MainNotions.S.haarLie, one_smul]
  have ht : (L.κN * ENNReal.ofReal cN * ENNReal.ofReal (‖α‖ ^ B.kap k r)).toReal = lamN L cN := by
    rw [ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_ofReal hR.1.le, ENNReal.toReal_ofReal hx.le]
    rfl
  have step : L.J F g = ((lamN L cN ^ 2 : ℝ) : ℂ) •
      besselJ k r L.z L.z' L.c L.π L.π' L.μW ((D.muN k r).map (conjM (aT k r α))) L.μW' F g := by
    rw [← ht]
    show besselJ k r L.z L.z' L.c L.π L.π' L.μW L.μN L.μW' F g = _
    rw [hLμN]
    exact besselJ_smul k r L.z L.z' L.c L.π L.π' L.μW _ L.μW' _ F g
  rw [step, besselJ_conj k r L.z L.z' L.c cStd L.π L.π' L.μW (D.muN k r) L.μW' hW hNc hW' (aT k r α) ha
    hcz hcz' (hp L.z fun n hn => (hnz n hn).2.2) (hp L.z' fun n hn => (hnz' n hn).2.2) F g,
    Formalism.FourierDecayAlt.B.JF, hz, hz', hπ, hπ', hμW, hμW', hμN]
  rfl

end GlobalTheory.ThA
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ColumnDictionaryIntoStepZeroFormsStatement
section
open MeasureTheory NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ColDict GlobalTheory.St
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.columnDictionary_into_stepZeroForms : ∀ (D : D7) (X : HidaSetting D) (u : D.what₂.Word) (F : Formalism.L2.Forms.Forms0 D u) (Tr : Transport X u F) (hK : X.LevelSubgroupCharacter), (∀ a, Tr.ιA (sigA X.B.I a) = Formalism.UG.sigR (Formalism.L2.Forms.sigD D) (FiniteAdeleRing (𝓞 D.host.F) D.host.F) (Tr.ιA a)) → LevelMatch X Tr hK → ColDictInto X Tr hK := by
  first | exact @GlobalTheory.St.colDictInto_of_levelMatch | exact GlobalTheory.St.colDictInto_of_levelMatch | (intros; apply GlobalTheory.St.colDictInto_of_levelMatch <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ConvolutionSmoothL2Statement
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec
open scoped InnerProductSpace ComplexOrder ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.convolutionSmoothL2_of_def : ConvolutionSmoothL2 := by
  first | exact @GlobalTheory.SmoothGrowth.convolutionSmoothL2 | exact GlobalTheory.SmoothGrowth.convolutionSmoothL2 | (intros; apply GlobalTheory.SmoothGrowth.convolutionSmoothL2 <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.CovolumeIntegralUnipotentStabilizerOfTermStatement
section
open NumberField Module Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.Cnt GlobalTheory.LoopC
open scoped ENNReal Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.covolume_integralUnipotentStabilizer_of_term : ∀ Cg cb Cu cT CT C0 A : ℝ, ∃ C : ℝ, 1 ≤ C ∧ ∀ (D : D7) (large₂ : SizeData₂ D) (u u' : D.what₂.Word) (C' Cl : ℝ), 1 ≤ Cl → Hyp D large₂ u u' C' Cl Cg cb Cu cT CT C0 A → ∀ (F0 : Fb D u) (Λ : LatV D), IsBase D u F0 → IsRowLat D F0 Λ → ∀ F' : FlagU D u', IsTermF D Λ (lf D F0) F' → ∀ (p : Point D.host.E (D.R.rS + 1)) (L U : GramM D), IsLoUni L → IsUpUni U → ZhatOM (ZhatL (lf D F0) F') = L * ptMat p * U → ∃ Ω : Set (D.what₂.Tau → GlobalTheory.LoopV.roots (ptMat p) → ℂ), MeasurableSet Ω ∧ MeasureTheory.volume Ω * ENNReal.ofReal (D.host.rdE ^ (2 * D.R.f * (D.R.rS + 1) ^ 3)) ≤ ENNReal.ofReal (HHZ D large₂.sc.b C (ZhatL (lf D F0) F') ^ (C * (D.R.rS : ℝ) ^ 2)) ∧ ∀ c : D.what₂.Tau → GlobalTheory.LoopV.roots (ptMat p) → ℂ, ∃ n ∈ NLam Λ (lf D F0) ∩ NLam Λ F', ∃ a : GramM D, (∀ j : Fin (D.R.rS + 1), n (frame F' j) = ∑ i : Fin (D.R.rS + 1), ((-1) ^ (i.val + j.val) * a i j) • frame F' i) ∧ (fun τ (q : GlobalTheory.LoopV.roots (ptMat p)) => ((U * a * U⁻¹).map (embS D τ) * GlobalTheory.LoopV.ofRoots (GlobalTheory.LoopV.roots (ptMat p)) (c τ) : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) ℂ) q.1.1 q.1.2) ∈ Ω := by
  first | exact @GlobalTheory.LoopC.CovTerm.covolume_term | exact GlobalTheory.LoopC.CovTerm.covolume_term | (intros; apply GlobalTheory.LoopC.CovTerm.covolume_term <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.DerivativeClosedClassBoundedByInverseLeastSizeStatement
section
open MeasureTheory NumberField Matrix Formalism.MainNotions.S
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.derivativeClosedClass_bounded_by_inverseLeastSize : ∀ (B : RowsAut), 1 ≤ B.I.n → 1 ≤ B.g → ∃ m : ℕ, ∀ W : Set (B.I.GA → ℂ), (∀ f ∈ W, (∃ F, GlobalTheory.Dec.IsContRep B F f) ∧ (∀ k ∈ B.I.Kg B.g, ∀ y, f (y * (1, k)) = f y) ∧ ∀ (v : InfinitePlace B.I.F) (E : GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalPlaceBasis.gLie (B.I.ε v)), ∃ f' ∈ W, ∀ y, HasDerivAt (fun t : ℝ => f (y * GlobalTheory.SobolevBound.onePar B (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalPlaceBasis.atPlace B v E) t)) (f' y) 0) → ∀ f ∈ W, ∃ C : ℝ, ∀ y, ‖f y‖ ≤ C * (GlobalTheory.Count.tau1 B.I y)⁻¹ ^ m := by
  first | exact @GlobalTheory.SobolevBound.derivative_closed_class_bound | exact GlobalTheory.SobolevBound.derivative_closed_class_bound | (intros; apply GlobalTheory.SobolevBound.derivative_closed_class_bound <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.DiscreteSeriesClassification
section
open GlobalTheory.DSSU

namespace GlobalTheory.DSSU.FromSU

theorem classS_of_discreteSeriesSU (h : GlobalTheory.Published.DiscreteSeriesSU) (n : ℕ) (hn : 1 ≤ n) (ε : Fin n → Bool) : ClassS ε := by
  rcases Nat.lt_or_ge n 2 with h2 | h2
  · obtain rfl : n = 1 := by omega
    exact GlobalTheory.T.classification_rank_one.1 ε
  · exact (GlobalTheory.Published.discreteSeriesSU_iff.mp h) n h2 ε

theorem discreteSeriesClassification_of_SU :
    GlobalTheory.Published.DiscreteSeriesSU → GlobalTheory.Published.DiscreteSeriesClassification := by
  intro h
  rw [GlobalTheory.Published.discreteSeriesClassification_iff, dsClass_iff]
  intro n
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact GlobalTheory.T.classification_rank_one.2
  · exact GlobalTheory.T.classification_unitary_of_full n (fun ε => GlobalTheory.T.classification_of_special_unitary n hn ε (classS_of_discreteSeriesSU h n hn ε))

end GlobalTheory.DSSU.FromSU
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsContinuousRowRepresentativesLowestKTypeStatement
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec GlobalTheory.Deep
open scoped InnerProductSpace ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_continuousRowRepresentatives_lowestKType : ∀ (B : RowsAut) (d : InfinitePlace B.I.F → ℝ), IsDSData B d → (∀ v, Formalism.MainNotions.S.IsKTypeOf (B.I.ε v) (B.σ v) (Formalism.QuantumDeterminants.lowK (B.I.ε v) (B.lam v)) (Formalism.MainNotions.S.lowKSub (B.I.ε v) (B.lam v) (B.σ v))) → 1 ≤ B.g → ∀ T ∈ B.I.HomS B.σs B.μf B.fund B.R, (∀ u, ∀ k ∈ B.I.Kg B.g, B.R (1, k) (T u) = T u) → ∃ Fr, IsReps B T Fr := by
  first | exact @GlobalTheory.SmoothRepsType.repsExist | exact GlobalTheory.SmoothRepsType.repsExist | (intros; apply GlobalTheory.SmoothRepsType.repsExist <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsExactGramFrameInTermClassStatement
section
open NumberField Module Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.Cnt GlobalTheory.LoopC
open scoped ENNReal Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_exactGram_frame_in_termClass : ∀ (D : D7) (u u' : D.what₂.Word) (F0 : Fb D u) (Λ : LatV D), Stand D u u' → IsBase D u F0 → IsRowLat D F0 Λ → ∀ (P : LatW D) (Z : GramM D), ∀ F' ∈ FrSet D Λ (lf D F0) ((Tu D u' : ℕ) : D.host.E) Z P, ∃ F'' ∈ ExSet D Λ (lf D F0) ((Tu D u' : ℕ) : D.host.E) Z P, TEqv D Λ (lf D F0) F' F'' := by
  first | exact @GlobalTheory.LoopC.FrameMove.exists_exact_frame | exact GlobalTheory.LoopC.FrameMove.exists_exact_frame | (intros; apply GlobalTheory.LoopC.FrameMove.exists_exact_frame <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsLatticeRepresentativeNormalisedStatement
section
open scoped Classical ENNReal
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.Unfold
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_lattice_representative_normalised : ∀ (D : D7) (T : D.host.E) (F0 : FlagG (VS D) D.R.rS T) (Λ : LV D), IsRowLat D F0 Λ → ∃ σ ∈ Lrep Λ (lf D F0), (VS D).hT σ F0.z = 1 := by
  first | exact @GlobalTheory.RowPartner.exists_partner_rowLat | exact GlobalTheory.RowPartner.exists_partner_rowLat | (intros; apply GlobalTheory.RowPartner.exists_partner_rowLat <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsScaleNormalisedLocalReadingStatement
section
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.HL GlobalTheory.LocOver
open scoped Pointwise ENNReal Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_scale_normalised_localReading : ∀ (D : D7) (X : HidaSetting D) (u u' : D.what₂.Word), ∃ s : X.B.I.Ginf → NNReal, (∀ γ, Formalism.L2.SG.RealObj.RegX X u u' γ → s γ = 1) ∧ (∀ γ, 0 < s γ) ∧ (∀ γ, s γ ≤ 1) ∧ ∀ w : Point D.host.E (D.R.rS + 1), (∃ g, Formalism.L2.SG.RealObj.IsPtRep X u u' w g) → (s (Formalism.L2.SG.RealObj.gamW X u u' w) : ℝ) = (((X.B.g : ℝ) ^ (D.R.f * Fintype.card (Formalism.L2.SG.RealObj.FreeE w)))⁻¹) := by
  first | exact @GlobalTheory.PinScale.scale_pin | exact GlobalTheory.PinScale.scale_pin | (intros; apply GlobalTheory.PinScale.scale_pin <;> assumption)
end

