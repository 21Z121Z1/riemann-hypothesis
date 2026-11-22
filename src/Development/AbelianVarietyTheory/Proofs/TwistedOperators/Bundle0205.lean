import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.MeasurePreservingRmulQuotMeas
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HasOrbIntTensorOfHasOrbInt
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0178
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0182
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0191
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0176
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0933
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.MemLatOIffExistsActO
import Formalism.SatakeDualWeyl.KpqSubgroupCompact
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0142
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0103
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0192
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0165
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0193
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0123
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0003
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.HalfLinearCocycle
import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.LocalIntegralGL
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilVacuumEqResidueCharDetSmul
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0129

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.QuotientMeasureFibration
section
open MeasureTheory Set GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary
open scoped ENNReal NNReal

noncomputable section

namespace GlobalTheory.Orb.FubiniQuot

theorem exists_bruhat_nnreal {A : Type} [Group A] [TopologicalSpace A] [IsTopologicalGroup A]
    [SecondCountableTopology A] [LocallyCompactSpace A] [T2Space A] [MeasurableSpace A] [BorelSpace A]
    {TA : Subgroup A} (hA : IsClosed (TA : Set A)) (ds : Measure TA) [ds.IsHaarMeasure] [ds.IsMulRightInvariant] :
    ∃ b : A → ℝ≥0, Measurable b ∧ ∀ a, ∫⁻ s : TA, (b (s * a) : ℝ≥0∞) ∂ds = 1 := by
  obtain ⟨b, hb, h1⟩ := exists_bruhat hA ds
  have hm : ∀ x, Measurable fun t : TA => b (t * x) := fun x => hb.comp (measurable_subtype_coe.mul_const _)
  have hlt : ∀ x, ∀ᵐ t : TA ∂ds, b (t * x) < ∞ := fun x => ae_lt_top (hm x) (by simp [h1])
  refine ⟨fun x => (b x).toNNReal, hb.ennreal_toNNReal, fun x => ?_⟩
  rw [← h1 x]
  exact lintegral_congr_ae ((hlt x).mono fun t ht => ENNReal.coe_toNNReal ht.ne)

section Prod

variable {A B : Type} [Group A] [TopologicalSpace A] [IsTopologicalGroup A] [SecondCountableTopology A]
  [LocallyCompactSpace A] [T2Space A] [MeasurableSpace A] [BorelSpace A]
  [Group B] [TopologicalSpace B] [IsTopologicalGroup B] [SecondCountableTopology B]
  [LocallyCompactSpace B] [T2Space B] [MeasurableSpace B] [BorelSpace B]

theorem quotInt_prod_eq_zero {TA : Subgroup A} {TB : Subgroup B} {U : Subgroup (A × B)}
    (hU : ∀ x, x ∈ U ↔ x.1 ∈ TA ∧ x.2 ∈ TB) (hA : IsClosed (TA : Set A)) (hB : IsClosed (TB : Set B))
    (da : Measure A) [da.IsHaarMeasure] (db : Measure B) [db.IsHaarMeasure]
    (ds : Measure TA) [ds.IsHaarMeasure] [ds.IsMulRightInvariant]
    (dr : Measure TB) [dr.IsHaarMeasure] [dr.IsMulRightInvariant]
    (φ : A × B → ℂ) (hi : LeftInv U φ)
    (hint : Integrable (descend U φ) (quotMeas U ((ds.prod dr).map (prodSub hU)) (da.prod db)))
    (h0 : ∀ b, quotInt TA ds da (fun a => φ (a, b)) = 0) :
    quotInt U ((ds.prod dr).map (prodSub hU)) (da.prod db) φ = 0 := by
  haveI : LocallyCompactSpace TA := hA.locallyCompactSpace
  haveI : LocallyCompactSpace TB := hB.locallyCompactSpace
  have hUc : IsClosed (U : Set (A × B)) := by
    rw [show (U : Set (A × B)) = (TA : Set A) ×ˢ (TB : Set B) from Set.ext hU]
    exact hA.prod hB
  set dt := (ds.prod dr).map (prodSub hU) with hdt
  haveI : dt.IsHaarMeasure := ContinuousMulEquiv.isHaarMeasure_map _ _
  haveI : dt.IsMulRightInvariant := isMulRightInvariant_map (prodSub hU) _
  obtain ⟨bA, mA, hA1⟩ := exists_bruhat_nnreal hA ds
  obtain ⟨bB, mB, hB1⟩ := exists_bruhat_nnreal hB dr
  set β : A × B → ℝ≥0 := fun x => bA x.1 * bB x.2 with hβ
  have mβ : Measurable β := (mA.comp measurable_fst).mul (mB.comp measurable_snd)
  have hβ1 : ∀ x, ∫⁻ t : U, (β (t * x) : ℝ≥0∞) ∂dt = 1 := fun x => by
    rw [hdt, lintegral_map (f := fun t : U => (β (t * x) : ℝ≥0∞))
      (mβ.coe_nnreal_ennreal.comp (measurable_subtype_coe.mul_const _)) (map_continuous _).measurable]
    show ∫⁻ p : TA × TB, ((bA (p.1 * x.1) * bB (p.2 * x.2) : ℝ≥0) : ℝ≥0∞) ∂(ds.prod dr) = 1
    simp only [ENNReal.coe_mul]
    rw [lintegral_prod_mul (f := fun s : TA => (bA (s * x.1) : ℝ≥0∞)) (g := fun s : TB => (bB (s * x.2) : ℝ≥0∞))
      (mA.coe_nnreal_ennreal.comp (measurable_subtype_coe.mul_const _)).aemeasurable
      (mB.coe_nnreal_ennreal.comp (measurable_subtype_coe.mul_const _)).aemeasurable, hA1, hB1, one_mul]
  have hν := (isQuotMeasure_quotMeas dt (da.prod db) hUc).eq_map (b := fun x => (β x : ℝ≥0∞))
    mβ.coe_nnreal_ennreal hβ1
  have hq : quotInt U dt (da.prod db) φ = ∫ x, β x • φ x ∂(da.prod db) := by
    rw [quotInt, hν, integral_map measurable_mk.aemeasurable (hν ▸ hint.1),
      ← integral_withDensity_eq_integral_smul mβ]
    simp only [hi.descend_mk]
  have hF : Integrable (fun x => β x • φ x) (da.prod db) := by
    have h2 := hint
    rw [hν] at h2
    replace h2 := h2.comp_measurable measurable_mk
    rwa [show descend U φ ∘ mk U = φ from hi.lift_descend, integrable_withDensity_iff_integrable_smul mβ] at h2
  have hAr : ∀ a, ∫ s : TA, (bA (s * a) : ℝ) ∂ds = 1 := fun a => by
    have hm : Measurable fun s : TA => (bA (s * a) : ℝ≥0∞) :=
      mA.coe_nnreal_ennreal.comp (measurable_subtype_coe.mul_const _)
    have := integral_toReal (μ := ds) hm.aemeasurable (.of_forall fun _ => ENNReal.coe_lt_top)
    rw [hA1 a, ENNReal.toReal_one] at this
    simpa only [ENNReal.coe_toReal] using this
  rw [hq, integral_prod_symm _ hF]
  refine integral_eq_zero_of_ae ?_
  filter_upwards [hF.prod_left_ae] with b hb
  by_cases hb0 : bB b = 0
  · simp [hβ, hb0]
  have hG : Integrable (fun a => bA a • φ (a, b)) da := by
    have hb0' : (bB b : ℝ) ≠ 0 := by exact_mod_cast hb0
    refine (hb.smul ((bB b : ℝ)⁻¹)).congr (.of_forall fun a => ?_)
    simp only [hβ, NNReal.smul_def, NNReal.coe_mul, smul_smul, Pi.smul_apply]
    rw [mul_comm (bA a : ℝ), ← mul_assoc, inv_mul_cancel₀ hb0', one_mul]
  have hw := (weil_integral (dt := ds) hA hG).2
  have e1 : (fun a => ∫ s : TA, bA (s * a) • φ ((s : A) * a, b) ∂ds) = fun a => φ (a, b) := funext fun a => by
    have hs : ∀ s : TA, φ ((s : A) * a, b) = φ (a, b) := fun s => by
      simpa only [Prod.mk_mul_mk, one_mul] using hi ((s : A), 1) ((hU _).2 ⟨s.2, TB.one_mem⟩) (a, b)
    simp only [hs, NNReal.smul_def]
    rw [integral_smul_const, hAr a, one_smul]
  rw [e1] at hw
  have e2 : ∫ a, β (a, b) • φ (a, b) ∂da = bB b • ∫ a, bA a • φ (a, b) ∂da := by
    rw [NNReal.smul_def, ← integral_smul]
    refine integral_congr_ae (.of_forall fun a => ?_)
    simp only [hβ, NNReal.smul_def, NNReal.coe_mul, smul_smul, mul_comm]
  show ∫ a, β (a, b) • φ (a, b) ∂da = 0
  rw [e2, ← hw.2, h0 b, smul_zero]

end Prod

theorem quotInt_eq_zero_of_fiber (A : Type) [Group A] [TopologicalSpace A] [IsTopologicalGroup A]
    [SecondCountableTopology A] [LocallyCompactSpace A] [T2Space A] [MeasurableSpace A] [BorelSpace A] (B : Type)
    [Group B] [TopologicalSpace B] [IsTopologicalGroup B] [SecondCountableTopology B] [LocallyCompactSpace B]
    [T2Space B] [MeasurableSpace B] [BorelSpace B] (H : Type) [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [SecondCountableTopology H] [LocallyCompactSpace H] [T2Space H] [MeasurableSpace H] [BorelSpace H]
    (e : A × B ≃ₜ* H) (TA : Subgroup A) (TB : Subgroup B) (T : Subgroup H)
    (hmem : ∀ a b, e (a, b) ∈ T ↔ a ∈ TA ∧ b ∈ TB) (hT : IsClosed (T : Set H)) (hcomm : IsMulCommutative T)
    (dh : Measure H) [dh.IsHaarMeasure] (dt : Measure T) [dt.IsHaarMeasure] (da : Measure A) [da.IsHaarMeasure]
    (ds : Measure TA) [ds.IsHaarMeasure] (φ : H → ℂ) (hi : LeftInv T φ)
    (hint : Integrable (descend T φ) (quotMeas T dt dh))
    (h0 : ∀ b, quotInt TA ds da (fun a => φ (e (a, b))) = 0) : quotInt T dt dh φ = 0 := by
  let U : Subgroup (A × B) := T.comap (e : A × B →* H)
  have hU : ∀ x, x ∈ U ↔ x.1 ∈ TA ∧ x.2 ∈ TB := fun x => hmem x.1 x.2
  have h' : ∀ x, e x ∈ T ↔ x ∈ U := fun x => Iff.rfl
  have hA : IsClosed (TA : Set A) := by
    have : (TA : Set A) = (fun a => e (a, 1)) ⁻¹' (T : Set H) := Set.ext fun a => by simp [hmem]
    rw [this]
    exact hT.preimage (by fun_prop)
  have hB : IsClosed (TB : Set B) := by
    have : (TB : Set B) = (fun b => e (1, b)) ⁻¹' (T : Set H) := Set.ext fun b => by simp [hmem]
    rw [this]
    exact hT.preimage (by fun_prop)
  have hUc : IsClosed (U : Set (A × B)) := hT.preimage e.continuous
  haveI : LocallyCompactSpace TA := hA.locallyCompactSpace
  haveI : LocallyCompactSpace TB := hB.locallyCompactSpace
  haveI : LocallyCompactSpace T := hT.locallyCompactSpace
  have hc : ∀ x y : T, x * y = y * x := fun x y => hcomm.is_comm.comm x y
  have hcA : ∀ s s' : TA, s * s' = s' * s := fun s s' => by
    have := congrArg Subtype.val (hc ⟨e ((s : A), 1), (hmem _ _).2 ⟨s.2, TB.one_mem⟩⟩
      ⟨e ((s' : A), 1), (hmem _ _).2 ⟨s'.2, TB.one_mem⟩⟩)
    simp only [Subgroup.coe_mul, ← map_mul, Prod.mk_mul_mk, mul_one] at this
    exact Subtype.ext (congrArg Prod.fst (e.injective this))
  have hcB : ∀ s s' : TB, s * s' = s' * s := fun s s' => by
    have := congrArg Subtype.val (hc ⟨e (1, (s : B)), (hmem _ _).2 ⟨TA.one_mem, s.2⟩⟩
      ⟨e (1, (s' : B)), (hmem _ _).2 ⟨TA.one_mem, s'.2⟩⟩)
    simp only [Subgroup.coe_mul, ← map_mul, Prod.mk_mul_mk, mul_one] at this
    exact Subtype.ext (congrArg Prod.snd (e.injective this))
  haveI : ds.IsMulRightInvariant := ⟨fun g => by
    rw [show (fun x : TA => x * g) = (fun x => g * x) from funext fun x => hcA x g]
    exact map_mul_left_eq_self ds g⟩
  let dr : Measure TB := Measure.haar
  haveI : dr.IsMulRightInvariant := ⟨fun g => by
    rw [show (fun x : TB => x * g) = (fun x => g * x) from funext fun x => hcB x g]
    exact map_mul_left_eq_self dr g⟩
  haveI : dt.IsMulRightInvariant := ⟨fun g => by
    rw [show (fun x : T => x * g) = (fun x => g * x) from funext fun x => hc x g]
    exact map_mul_left_eq_self dt g⟩
  let dtU : Measure U := (ds.prod dr).map (prodSub hU)
  haveI : dtU.IsHaarMeasure := ContinuousMulEquiv.isHaarMeasure_map _ _
  haveI : dtU.IsMulRightInvariant := isMulRightInvariant_map (prodSub hU) _
  let dt' : Measure T := dtU.map (subEquiv e h')
  haveI : dt'.IsHaarMeasure := ContinuousMulEquiv.isHaarMeasure_map _ _
  haveI : dt'.IsMulRightInvariant := isMulRightInvariant_map (subEquiv e h') _

  let db : Measure B := Measure.haar
  let dh' : Measure H := (da.prod db).map e
  haveI : dh'.IsHaarMeasure := ContinuousMulEquiv.isHaarMeasure_map _ _
  have hiU : LeftInv U (φ ∘ e) := fun γ hγ g => by
    simp only [Function.comp, map_mul]
    exact hi _ hγ _
  have ht := hasQuotInt_map (e := e) (h := h') (hT := hUc) (dt := dtU) (dh := da.prod db) hi
    (quotInt T dt' dh' φ)
  have hk : Measure.haarScalarFactor dt dt' ≠ 0 := fun h => NeZero.ne dt (by
    rw [Measure.isMulLeftInvariant_eq_smul dt dt', h, zero_smul])
  have hc0 : Measure.haarScalarFactor dh dh' ≠ 0 := fun h => NeZero.ne dh (by
    rw [Measure.isMulLeftInvariant_eq_smul dh dh', h, zero_smul])
  obtain ⟨k, hk0, edt⟩ : ∃ k : ℝ≥0, k ≠ 0 ∧ dt = k • dt' := ⟨_, hk, Measure.isMulLeftInvariant_eq_smul dt dt'⟩
  obtain ⟨c, hc1, edh⟩ : ∃ c : ℝ≥0, c ≠ 0 ∧ dh = c • dh' := ⟨_, hc0, Measure.isMulLeftInvariant_eq_smul dh dh'⟩
  subst edt edh
  have e1 : quotMeas T (k • dt') (c • dh') = ((k⁻¹ * c : ℝ≥0) : ℝ≥0∞) • quotMeas T dt' dh' := by
    rw [quotMeas_smul_right hT hk0, show c • dh' = (c : ℝ≥0∞) • dh' from rfl, quotMeas_smul_left hT,
      show ∀ (r : ℝ≥0) (μ : Measure (Quot T)), r • μ = (r : ℝ≥0∞) • μ from fun _ _ => rfl, smul_smul,
      ENNReal.coe_mul]
  have hr0 : ((k⁻¹ * c : ℝ≥0) : ℝ≥0∞) ≠ 0 := by simp [hk0, hc1]
  rw [e1] at hint
  have hint' := (integrable_smul_measure hr0 ENNReal.coe_ne_top).1 hint
  have hI := (ht.1.1 ⟨hint', rfl⟩).1
  have h00 := quotInt_prod_eq_zero hU hA hB da db ds dr (φ ∘ e) hiU hI h0
  have hz : quotInt T dt' dh' φ = 0 := ht.2.trans h00
  rw [quotInt, e1, integral_smul_measure]
  rw [quotInt] at hz
  rw [hz, smul_zero]

end GlobalTheory.Orb.FubiniQuot
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RedMFrMapAdjZero
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.LiftLevel

variable {D : D7}

def liftI (Pg Q : Finset (Formalism.L2.DIV.Pl D.host.E)) : Ideal (𝓞 D.host.E) :=
  ∏ PP ∈ Pg ∪ Q, conjI PP.asIdeal

theorem frMapAdj_zero (S T : HSp D) (βS : GL (Fin S.rank) (EAf D)) (βT : GL (Fin T.rank) (EAf D)) :
    frMapAdj S T βS βT 0 = 0 := by
  unfold frMapAdj
  simp

theorem isIntM_zero {b a : ℕ} : IsIntM (0 : Matrix (Fin b) (Fin a) (EAf D)) := fun _ _ => zero_mem _

theorem redM_frMapAdj_zero (S T : HSp D) (βS : GL (Fin S.rank) (EAf D)) (βT : GL (Fin T.rank) (EAf D))
    (PP : Formalism.L2.DIV.Pl D.host.E) : redM PP (frMapAdj S T βS βT 0) = 0 := by
  have h0 : IsIntM (frMapAdj S T βS βT 0) := by rw [frMapAdj_zero]; exact isIntM_zero
  have h := (GlobalTheory.FrameAdjAdd.frMapAdj_add_isIntM_redM S T βS βT 0 0 h0 h0).2 PP
  rw [add_zero] at h
  exact (left_eq_add.mp h)

def liftL (S T : HSp D) (βS : GL (Fin S.rank) (EAf D)) (βT : GL (Fin T.rank) (EAf D))
    (Pg Q : Finset (Formalism.L2.DIV.Pl D.host.E)) (e : AE D) : AddSubgroup (WO S T) where
  carrier := {x | IsHalf (cA D e) x ∧ IsIntM (frMapAdj S T βS βT x) ∧
    ∀ PP ∈ Pg ∪ Q, redM PP (frMapAdj S T βS βT x) = 0}
  zero_mem' := by
    refine ⟨fun i j => by simp, ?_, fun PP _ => ?_⟩
    · rw [frMapAdj_zero]; exact isIntM_zero
    · exact redM_frMapAdj_zero S T βS βT PP
  add_mem' := by
    rintro x y ⟨hx1, hx2, hx3⟩ ⟨hy1, hy2, hy3⟩
    obtain ⟨h1, h2⟩ := GlobalTheory.FrameAdjAdd.frMapAdj_add_isIntM_redM S T βS βT x y hx2 hy2
    refine ⟨fun i j => ?_, h1, fun PP hPP => ?_⟩
    · simp only [Matrix.add_apply, mul_add, hx1 i j, hy1 i j]
    · rw [h2, hx3 PP hPP, hy3 PP hPP, add_zero]
  neg_mem' := by
    rintro x ⟨hx1, hx2, hx3⟩
    have hneg : frMapAdj S T βS βT (-x) = -frMapAdj S T βS βT x := by
      unfold frMapAdj
      simp [Matrix.map_neg, Matrix.transpose_neg, Matrix.mul_neg, Matrix.neg_mul]
    have hI : IsIntM (frMapAdj S T βS βT (-x)) := fun i j => by
      rw [hneg, Matrix.neg_apply]; exact neg_mem (hx2 i j)
    obtain ⟨-, h2⟩ := GlobalTheory.FrameAdjAdd.frMapAdj_add_isIntM_redM S T βS βT x (-x) hx2 hI
    refine ⟨fun i j => ?_, hI, fun PP hPP => ?_⟩
    · simp only [Matrix.neg_apply, mul_neg, hx1 i j]
    · have := h2 PP
      rw [add_neg_cancel, redM_frMapAdj_zero, hx3 PP hPP, zero_add] at this
      exact this.symm

def adjA (S T : HSp D) (βS : GL (Fin S.rank) (EAf D)) (βT : GL (Fin T.rank) (EAf D)) (a : AE D) (x : WO S T) :
    Matrix (Fin S.rank) (Fin T.rank) (EAf D) :=
  toEAf D a • HMul.hMul βS.val (frMapAdj S T βS βT x)

def IsMover (S T : HSp D) (βS : GL (Fin S.rank) (EAf D)) (βT : GL (Fin T.rank) (EAf D)) (e a : AE D)
    (k₀ : GA D S) : Prop :=
  k₀ ∈ GfC S ∧ (∀ x : WO S T, IsHalf (1 - e - cA D e) x → actO S T k₀ 1 x = x) ∧
    ∀ x : WO S T, IsHalf (cA D e) x →
      frMapAdj S T βS βT (actO S T k₀ 1 x) = adjA S T βS βT a x

def IsGen {S T : HSp D} (C : Ctx S T) (βS : GL (Fin S.rank) (EAf D)) (βT : GL (Fin T.rank) (EAf D))
    (Pg Q : Finset (Formalism.L2.DIV.Pl D.host.E)) (e a : AE D) : Prop :=
  ∀ x : WO S T, IsHalf (cA D e) x →
    (IsIntM (adjA S T βS βT a x) ↔
      x ∈ hatA S T (tens (stdL D.host.E S.rank) C.X.Λ)) ∧
    ((IsIntM (adjA S T βS βT a x) ∧
      ∀ PP ∈ Pg ∪ Q, redM PP (adjA S T βS βT a x) = 0) ↔
      x ∈ hatA S T (tens (stdL D.host.E S.rank) (liftI Pg Q • C.X.Λ)))

end GlobalTheory.LiftLevel

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SchwartzIsometryInnerProductEqStatement
section
open MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.schwartz_isometry_inner_product_eq : ∀ {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] (μ : Measure V) [μ.IsAddHaarMeasure] (T : SchwartzMap V ℂ →ₗ[ℂ] SchwartzMap V ℂ),
    (∀ f, ∫ x, ‖T f x‖ ^ 2 ∂μ = ∫ x, ‖f x‖ ^ 2 ∂μ) →
    ∀ f g : SchwartzMap V ℂ, ∫ x, T f x * starRingEnd ℂ (T g x) ∂μ = ∫ x, f x * starRingEnd ℂ (g x) ∂μ := by
  first | exact @GlobalTheory.schwartz_L2_isometry_preserves_inner | exact GlobalTheory.schwartz_L2_isometry_preserves_inner | (intros; apply GlobalTheory.schwartz_L2_isometry_preserves_inner <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SelfDualFrameConjIntegralSmulOfIntegral
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep GlobalTheory.FinZeta GlobalTheory.AdelicScalar GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.LiftRows
open Formalism.IndefR.Lev (levG levChi IsBaseFrame)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke dosetInd IsCommensurated)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LGrp (IsUnitarisable IsIrrSmooth bcParam)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ConjIntegral

theorem mul_int {R : Type} [CommRing R] (S : Subring R) {n : ℕ} {A B : Matrix (Fin n) (Fin n) R}
    (hA : ∀ i j, A i j ∈ S) (hB : ∀ i j, B i j ∈ S) (i j : Fin n) : (A * B) i j ∈ S := by
  rw [Matrix.mul_apply]
  exact S.sum_mem fun k _ => S.mul_mem (hA i k) (hB k j)

theorem conj_int {R : Type} [CommRing R] (S : Subring R) (σ : R →+* R) (hσ : ∀ s ∈ S, σ s ∈ S) {n : ℕ}
    (G Gi γ γi : Matrix (Fin n) (Fin n) R) (hG : ∀ i j, G i j ∈ S) (hGi : ∀ i j, Gi i j ∈ S) (hGG : Gi * G = 1)
    (hγ : γ * γi = 1) (hu : (γ.map σ)ᵀ * G * γ = G) (a : R) (ha : ∀ i j, (a • γ) i j ∈ S) :
    ∀ i j, (σ a • γi) i j ∈ S := by
  have e1 : γi = Gi * (γ.map σ)ᵀ * G := by
    calc γi = Gi * G * γi := by rw [hGG, Matrix.one_mul]
      _ = Gi * ((γ.map σ)ᵀ * G * γ) * γi := by rw [hu]
      _ = Gi * (γ.map σ)ᵀ * G * (γ * γi) := by simp only [Matrix.mul_assoc]
      _ = Gi * (γ.map σ)ᵀ * G := by rw [hγ, Matrix.mul_one]
  have e2 : σ a • γi = Gi * ((a • γ).map σ)ᵀ * G := by
    have : (a • γ).map σ = σ a • γ.map σ := by
      ext i j; simp [Matrix.map_apply, Matrix.smul_apply, map_mul]
    rw [this, Matrix.transpose_smul, Matrix.mul_smul, Matrix.smul_mul, e1]
  have hc : ∀ i j, ((a • γ).map σ)ᵀ i j ∈ S := fun i j => hσ _ (ha j i)
  rw [e2]
  exact mul_int S (mul_int S hGi hc) hG

theorem conj_int_both {R : Type} [CommRing R] (S : Subring R) (σ : R →+* R) (hσ : ∀ s ∈ S, σ s ∈ S) {n : ℕ}
    (G Gi γ γi : Matrix (Fin n) (Fin n) R) (hG : ∀ i j, G i j ∈ S) (hGi : ∀ i j, Gi i j ∈ S) (hGG : Gi * G = 1)
    (hγ : γ * γi = 1) (hγ' : γi * γ = 1) (hu : (γ.map σ)ᵀ * G * γ = G) (a : R)
    (ha : ∀ i j, (a • γ) i j ∈ S) (ha' : ∀ i j, (a • γi) i j ∈ S) :
    (∀ i j, (σ a • γ) i j ∈ S) ∧ (∀ i j, (σ a • γi) i j ∈ S) := by
  have hu' : (γi.map σ)ᵀ * G * γi = G := by
    have h1 : (γi.map σ)ᵀ * (γ.map σ)ᵀ = 1 := by
      rw [← Matrix.transpose_mul, ← Matrix.map_mul, hγ, Matrix.map_one σ (map_zero σ) (map_one σ), Matrix.transpose_one]
    calc (γi.map σ)ᵀ * G * γi = (γi.map σ)ᵀ * ((γ.map σ)ᵀ * G * γ) * γi := by rw [hu]
      _ = ((γi.map σ)ᵀ * (γ.map σ)ᵀ) * G * (γ * γi) := by simp only [Matrix.mul_assoc]
      _ = G := by rw [h1, hγ, Matrix.one_mul, Matrix.mul_one]
  exact ⟨conj_int S σ hσ G Gi γi γ hG hGi hGG hγ' hu' a ha', conj_int S σ hσ G Gi γ γi hG hGi hGG hγ hu a ha⟩

theorem unit_conj {R : Type} [CommRing R] (σ : R →+* R) {n : ℕ} (B Bi H J : Matrix (Fin n) (Fin n) R)
    (hB : Bi * B = 1) (hB' : B * Bi = 1) (hH : Formalism.UG.cT σ H * J * H = J) :
    ((Bi * H * B).map σ)ᵀ * (Formalism.UG.cT σ B * J * B) * (Bi * H * B) = Formalism.UG.cT σ B * J * B := by
  have hcT : ∀ A C : Matrix (Fin n) (Fin n) R, Formalism.UG.cT σ (A * C) = Formalism.UG.cT σ C * Formalism.UG.cT σ A := by
    intro A C; simp only [Formalism.UG.cT, Matrix.map_mul, Matrix.transpose_mul]
  have e : Formalism.UG.cT σ Bi * Formalism.UG.cT σ B = 1 := by
    rw [← hcT, hB']
    simp only [Formalism.UG.cT, Matrix.map_one _ (map_zero _) (map_one _), Matrix.transpose_one]
  change Formalism.UG.cT σ (Bi * H * B) * _ * _ = _
  rw [hcT, hcT]
  calc Formalism.UG.cT σ B * (Formalism.UG.cT σ H * Formalism.UG.cT σ Bi) * (Formalism.UG.cT σ B * J * B) * (Bi * H * B)
      = Formalism.UG.cT σ B * (Formalism.UG.cT σ H * (Formalism.UG.cT σ Bi * Formalism.UG.cT σ B) * J * (B * Bi) * H) * B := by
        simp only [Matrix.mul_assoc]
    _ = Formalism.UG.cT σ B * J * B := by rw [e, hB', Matrix.mul_one, Matrix.mul_one, hH]

end GlobalTheory.ConjIntegral

namespace GlobalTheory.ConjIntegral

set_option maxHeartbeats 800000 in

theorem conj_smul_isIntM : ∀ {D : D7} (T : HSp D) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)) (βT : GL (Fin T.rank) (EAf D)), IsSelfDualC T ΛT → IsFrame βT ΛT → ∀ (h : GL (Fin T.rank) (EAf D)), h ∈ UA D.sp.cm T.gram → ∀ (γ : GL (Fin T.rank) (EAf D)), γ = βT⁻¹ * h * βT → ∀ (a : AE D), IsIntM (toEAf D a • γ.1) → IsIntM (toEAf D a • (γ⁻¹ : GL (Fin T.rank) (EAf D)).1) → IsIntM (toEAf D (cA D a) • γ.1) ∧ IsIntM (toEAf D (cA D a) • (γ⁻¹ : GL (Fin T.rank) (EAf D)).1) := by
  intro D T ΛT βT hsd hβ h hh γ hγ a h1 h2
  obtain ⟨m, s, s', hs, hd⟩ := GlobalTheory.LatVacDual.dualFamily D T ΛT hsd
  obtain ⟨G, hG⟩ := GlobalTheory.FrameGram.exists_unit_adelic star (Formalism.UG.sigR D.sp.cm.sig (Formalism.L2.Herm.Af D.host.F))
    (fun _ => GlobalTheory.LevSplit.sigR_int) (fun _ => rfl) T.gram βT ΛT hβ (fun y hy => (hsd.2 y).1 hy) s s' hs hd
  have hσ : ∀ x ∈ Formalism.L2.Herm.intAf D.host.F D.host.E,
      Formalism.UG.sigR D.sp.cm.sig (Formalism.L2.Herm.Af D.host.F) x ∈ Formalism.L2.Herm.intAf D.host.F D.host.E :=
    fun _ hx => GlobalTheory.LevSplit.sigR_int hx
  have hGm : ∀ i j, (intGL D.host.F D.host.E T.rank G).1 i j ∈ Formalism.L2.Herm.intAf D.host.F D.host.E :=
    fun i j => (G.1 i j).2
  have hGi : ∀ i j, (intGL D.host.F D.host.E T.rank G⁻¹).1 i j ∈ Formalism.L2.Herm.intAf D.host.F D.host.E :=
    fun i j => ((G⁻¹).1 i j).2
  have hGG : (intGL D.host.F D.host.E T.rank G⁻¹).1 * (intGL D.host.F D.host.E T.rank G).1 = 1 := by
    rw [← Units.val_mul, ← map_mul, inv_mul_cancel, map_one, Units.val_one]

  have hhu : Formalism.UG.cT (Formalism.UG.sigR D.sp.cm.sig (Formalism.L2.Herm.Af D.host.F)) h.1 * T.gram.map (Formalism.UG.inclE (Formalism.L2.Herm.Af D.host.F)) * h.1 =
      T.gram.map (Formalism.UG.inclE (Formalism.L2.Herm.Af D.host.F)) := hh
  have hγ1 : γ.1 = (βT⁻¹).1 * h.1 * βT.1 := by rw [hγ]; rfl
  have hu := unit_conj (Formalism.UG.sigR D.sp.cm.sig (Formalism.L2.Herm.Af D.host.F)) βT.1 (βT⁻¹).1 h.1 _
    (Units.inv_mul βT) (Units.mul_inv βT) hhu
  rw [← hγ1, ← hG] at hu
  have key := conj_int_both _ _ hσ _ _ γ.1 (γ⁻¹).1 hGm hGi hGG (Units.mul_inv γ) (Units.inv_mul γ) hu (toEAf D a) h1 h2
  rw [GlobalTheory.AdelicLatMove.toEAf_cA a]
  exact key

end GlobalTheory.ConjIntegral
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SmulMemHermitianLatticeAdelicCompletionOfSmulLeStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.smul_mem_hermitianLatticeAdelicCompletion_of_smul_le : ∀ (D : D7) {k : ℕ} (L L' : Lt D.host.E k) (c : D.host.E), (∀ x ∈ L, c • x ∈ L') → ∀ u ∈ hatV L, ((1 : Af D.host.F) ⊗ₜ[D.host.F] c) • u ∈ hatV L' := by
  first | exact @GlobalTheory.LevkSmul.smul_mem_hatV | exact GlobalTheory.LevkSmul.smul_mem_hatV | (intros; apply GlobalTheory.LevkSmul.smul_mem_hatV <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SphericalZetaKernelGLRightInvariantIntegral
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep GlobalTheory.FinZeta GlobalTheory.AdelicScalar GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.LiftRows
open Formalism.IndefR.Lev (levG levChi IsBaseFrame)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke dosetInd IsCommensurated)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LGrp (IsUnitarisable IsIrrSmooth bcParam)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ZetaGL

theorem kerGL_mul_right_KGL : ∀ (E : Type) [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) (r N : ℕ) (z : ℂˣ) (φ : GL (Fin r) (w.adicCompletion E) → ℂ), KerGL w N z φ → ∀ g k : GL (Fin r) (w.adicCompletion E), k ∈ KGL w r → φ (g * k) = φ g := by
  intro E _ _ w r N z φ hφ g k hk
  obtain ⟨ϖ, hϖ⟩ := exists_isUnifV w
  have hm := mem_Ov_of_isUnifV hϖ
  obtain ⟨a, -, k₁, hk₁, k₂, hk₂, e⟩ := Formalism.UG.Final.CartanDecomp E w r ϖ hm hϖ g
  obtain ⟨t, ht⟩ : ∃ t : GL (Fin r) (w.adicCompletion E), t = k₁⁻¹ * g * k₂⁻¹ := ⟨_, rfl⟩
  have hg : g = k₁ * t * k₂ := by rw [ht]; group
  have htv : t.1 = Matrix.diagonal fun i => ϖ ^ a i := by
    calc t.1 = ((k₁⁻¹ : GL (Fin r) (w.adicCompletion E)).1 * k₁.1) * Formalism.UG.diagPow E w ϖ a *
          (k₂.1 * (k₂⁻¹ : GL (Fin r) (w.adicCompletion E)).1) := by
          rw [ht, Units.val_mul, Units.val_mul, e]; simp only [Matrix.mul_assoc]
      _ = _ := by rw [Units.inv_mul, Units.mul_inv, Matrix.one_mul, Matrix.mul_one]; rfl
  rw [hg, mul_assoc (k₁ * t) k₂ k, hφ ϖ hϖ a t htv k₁ hk₁ (k₂ * k) (mul_mem hk₂ hk), hφ ϖ hϖ a t htv k₁ hk₁ k₂ hk₂]

end GlobalTheory.ZetaGL
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SplitPlaceColumnMemCompletedLatticeIffFrameIntegStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting GlobalTheory.PlaceTensor
open scoped TensorProduct ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.splitPlace_column_mem_completedLattice_iff_frame_integral : ∀ (D : D7) (V : HSp D) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) (β : GL (Fin V.rank) (EAf D)), IsSelfDualC V Λ → Formalism.L2.DIV.IsFrame β Λ → ∀ (v : FinPl D) (φ : SplitProj D v) (e : AE D), IsIdemOf φ e → ∀ y : Fin V.rank → AE D, (fun i => finPart D (e * y i)) ∈ Formalism.MainNotions.StandardLattice.latHat D.host.F D.host.E (Λ : Set (Fin V.rank → D.host.E)) ↔ ∀ i, Valued.v ((((frCo φ β)⁻¹ : GL (Fin V.rank) (Fv D.host.F v)).1 *ᵥ fun k => rdA φ (y k)) i) ≤ 1 := by
  first | exact @GlobalTheory.SplitFrameColumn.frame_column | exact GlobalTheory.SplitFrameColumn.frame_column | (intros; apply GlobalTheory.SplitFrameColumn.frame_column <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SymplecticFormOnHomsReframeHomMatrixStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open GlobalTheory.AdSpan.ReVec
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.symplecticFormOnHoms_reframeHomMatrix : ∀ (D : D7) (S T : HSp D) (b : Module.Basis (Fin S.rank) D.host.E S.V) (x y : WO (reS S b) T), symplO (reS S b) T x y = symplO S T (reW S T b x) (reW S T b y) := by
  first | exact @GlobalTheory.AdSpan.ReVec.Sympl.symplO_reW | exact GlobalTheory.AdSpan.ReVec.Sympl.symplO_reW | (intros; apply GlobalTheory.AdSpan.ReVec.Sympl.symplO_reW <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaKernelFiniteVectorNeZeroStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.theta_kernel_finite_vector_ne_zero : ∀ (D : D7) (S T : HSp D) (C : Ctx S T), T.rank ≤ S.rank → ∀ (B : C.Bas), C.IsB B → ∀ ΛT : Lt D.host.E T.rank, IsSelfDualC T ΛT → ∀ (βS : GL (Fin S.rank) (Lev.EAf D)) (βT : GL (Fin T.rank) (Lev.EAf D)), Formalism.L2.DIV.IsFrame βS (stdL D.host.E S.rank) → Formalism.L2.DIV.IsFrame βT ΛT → ∀ (Pg Q : Finset (Formalism.L2.DIV.Pl D.host.E)) (ξ : ∀ PP : Formalism.L2.DIV.Pl D.host.E, (Formalism.L2.DIV.kP PP)ˣ →* ℂˣ) (f₀ f : WO S T → ℂ), IsThPVecOf C.ψ C.θ S T (fun _ => 1) (C.sB B) (stdL D.host.E S.rank : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) βS βT Pg Q ξ f₀ f → f ≠ 0 := by
  first | exact @GlobalTheory.ThPVecNe.thPVec_ne_zero | exact GlobalTheory.ThPVecNe.thPVec_ne_zero | (intros; apply GlobalTheory.ThPVecNe.thPVec_ne_zero <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ToEAfOrientedHermitianFormEqTraceFramesStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.LiftRows
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.AdelicScalar
open Formalism.L2.DIV (kP Pl LevelP)
open Classical

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.toEAf_orientedHermitianForm_eq_trace_frames : ∀ {D : D7} (S T : HSp D) (βS : GL (Fin S.rank) (Datum.EAf D)) (βT : GL (Fin T.rank) (Datum.EAf D)) (k y : WO S T), toEAf D (hO S T y k) = Matrix.trace (frMapAdj S T βS βT k * frMapO S T βS βT y) := by
  first | exact @GlobalTheory.TraceFrames.toEAf_hO_eq_trace_frames | exact GlobalTheory.TraceFrames.toEAf_hO_eq_trace_frames | (intros; apply GlobalTheory.TraceFrames.toEAf_hO_eq_trace_frames <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilVacuumEqResidueCharDetSmulStatement
section
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR GlobalTheory.WeilParts GlobalTheory.StepLaw
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weil_vacuum_eq_residueChar_det_smul : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)) (θ : InfFam D) (sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)) (βS : GL (Fin S.rank) (Lev.EAf D)) (βT : GL (Fin T.rank) (Lev.EAf D)) (e : AE D) (P : Finset (Pl D.host.E)) (cS cT : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (f : WO S T → ℂ), IsWeilDatumO ψ S T χS χT om → IsInfFam θ → S.SigOK → T.SigOK → (∀ τ, IsCartanInv (gramAt D S τ) (sS τ)) → (∀ τ, IsCartanInv (gramAt D T τ) (sT τ)) → IsSelfDualC S ΛS → IsSelfDualC T ΛT → IsFrame βS ΛS → IsFrame βT ΛT → IsIdemSum e P → TameOn χS e P cS → TameOn χT e P cT → (∀ v ε, NonSplitAt D v ε → UnramAt ε χS → UnramAt ε χT → FixesVacAt ψ S T ΛS ΛT om v ε) → IsVacO ψ θ S T sS sT ΛS ΛT f → ∀ g ∈ GfC S, ∀ h ∈ GfC T, finE S g ∈ St βS → finE T h ∈ St βT → ∀ v ε, IsPlaceIdem D v ε → SuppPl ε S g → SuppPl ε T h → om (g, h) f = vacScal βS βT P cS cT g h • f := by
  first | exact @GlobalTheory.VacLoc.om_vacuum_eq_vacScal_smul | exact GlobalTheory.VacLoc.om_vacuum_eq_vacScal_smul | (intros; apply GlobalTheory.VacLoc.om_vacuum_eq_vacScal_smul <;> assumption)
end

