import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0023
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0021
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0053

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.SplitsPullbackSndOfSplitsDiagonalComplement
section
open CategoryTheory Limits AlgebraicGeometry

noncomputable section
namespace GlobalTheory.EtC.Tr

theorem splits_pullbackSnd_of_splits_diagComplHom {Z X V : Scheme.{0}} (f : Z ⟶ X) [IsFinite f] [Etale f]
    (v : V ⟶ Z) (h : Splits (diagComplHom f) v) : Splits (pullback.snd f f) v := by
  obtain ⟨m, s, hs, hiso⟩ := h
  have hδs : pullback.diagonal f ≫ pullback.snd f f = 𝟙 Z := pullback.diagonal_snd f
  let t : Fin (m + 1) → (V ⟶ pullback f f) :=
    Fin.cons (α := fun _ => V ⟶ pullback f f) (v ≫ pullback.diagonal f) (fun j => s j ≫ (diagCompl f).ι)
  have ht0 : t 0 = v ≫ pullback.diagonal f := rfl
  have hts : ∀ k : Fin m, t k.succ = s k ≫ (diagCompl f).ι := fun k => rfl
  have ht : ∀ j, t j ≫ pullback.snd f f = v := by
    intro j
    induction j using Fin.cases with
    | zero => rw [ht0, Category.assoc, hδs, Category.comp_id]
    | succ k => rw [hts, Category.assoc]; exact hs k
  refine ⟨m + 1, t, ht, ?_⟩
  let d : Fin m → (V ⟶ pullback (diagComplHom f) v) :=
    fun j => pullback.lift (s j) (𝟙 V) (by rw [hs j, Category.id_comp])
  let Φ : ∐ (fun _ : Fin m => V) ⟶ pullback (diagComplHom f) v := Sigma.desc d
  have hΦ : IsIso Φ := hiso
  have hdΦ : ∀ k, d k = Sigma.ι (fun _ : Fin m => V) k ≫ Φ := fun k => (Sigma.ι_desc _ _).symm
  let eU : pullback (diagComplHom f) v ⟶ pullback (pullback.snd f f) v :=
    pullback.map (diagComplHom f) v (pullback.snd f f) v (diagCompl f).ι (𝟙 V) (𝟙 Z)
      (by simp [diagComplHom]) (by simp)
  let eD : pullback (pullback.diagonal f ≫ pullback.snd f f) v ⟶ pullback (pullback.snd f f) v :=
    pullback.map _ v (pullback.snd f f) v (pullback.diagonal f) (𝟙 V) (𝟙 Z) (by simp) (by simp)
  let l : V ⟶ pullback (pullback.diagonal f ≫ pullback.snd f f) v :=
    pullback.lift v (𝟙 V) (by rw [hδs]; simp)
  have hl : IsIso l := by
    have h1 : IsIso (pullback.diagonal f ≫ pullback.snd f f) := by rw [hδs]; infer_instance
    have h2 : l ≫ pullback.snd _ _ = 𝟙 V := pullback.lift_snd _ _ _
    have h3 : IsIso (l ≫ pullback.snd (pullback.diagonal f ≫ pullback.snd f f) v) := by
      rw [h2]; infer_instance
    exact IsIso.of_isIso_comp_right l (pullback.snd _ _)
  let g : Fin (m + 1) → (V ⟶ pullback (pullback.snd f f) v) :=
    Fin.cons (α := fun _ => V ⟶ pullback (pullback.snd f f) v) (l ≫ eD) (fun k => d k ≫ eU)
  have hg : (Sigma.desc (fun j => pullback.lift (t j) (𝟙 V) (by rw [ht j, Category.id_comp])) :
      ∐ (fun _ : Fin (m + 1) => V) ⟶ pullback (pullback.snd f f) v) = Sigma.desc g := by
    refine Sigma.hom_ext _ _ (fun j => ?_)
    rw [Sigma.ι_desc, Sigma.ι_desc]
    induction j using Fin.cases with
    | zero =>
      apply pullback.hom_ext
      · rw [pullback.lift_fst]
        show t 0 = (l ≫ eD) ≫ _
        rw [Category.assoc, pullback.lift_fst, ← Category.assoc, pullback.lift_fst, ht0]
      · rw [pullback.lift_snd]
        show 𝟙 V = (l ≫ eD) ≫ _
        rw [Category.assoc, pullback.lift_snd, ← Category.assoc, pullback.lift_snd, Category.id_comp]
    | succ k =>
      apply pullback.hom_ext
      · rw [pullback.lift_fst]
        show t k.succ = (d k ≫ eU) ≫ _
        rw [Category.assoc, pullback.lift_fst, ← Category.assoc, pullback.lift_fst, hts]
      · rw [pullback.lift_snd]
        show 𝟙 V = (d k ≫ eU) ≫ _
        rw [Category.assoc, pullback.lift_snd, ← Category.assoc, pullback.lift_snd, Category.id_comp]
  rw [hg]
  have hΦi : IsOpenImmersion Φ := inferInstance
  have hι : ∀ k, IsOpenImmersion (Sigma.ι (fun _ : Fin m => V) k) := fun k => inferInstance
  have hδo : IsOpenImmersion (pullback.diagonal f) := inferInstance
  have hUo : IsOpenImmersion eU := inferInstance
  have hDo : IsOpenImmersion eD := inferInstance
  have hgo : ∀ j, IsOpenImmersion (g j) := by
    intro j
    induction j using Fin.cases with
    | zero => show IsOpenImmersion (l ≫ eD); infer_instance
    | succ k => show IsOpenImmersion (d k ≫ eU); rw [hdΦ]; infer_instance
  have hgπ' : ∀ j, g j ≫ pullback.fst (pullback.snd f f) v = t j := by
    intro j
    induction j using Fin.cases with
    | zero =>
      show (l ≫ eD) ≫ _ = t 0
      rw [Category.assoc, pullback.lift_fst, ← Category.assoc, pullback.lift_fst, ht0]
    | succ k =>
      show (d k ≫ eU) ≫ _ = t k.succ
      rw [Category.assoc, pullback.lift_fst, ← Category.assoc, pullback.lift_fst, hts]
  have hgπ : ∀ j y, pullback.fst (pullback.snd f f) v (g j y) = t j y := by
    intro j y
    rw [← Scheme.Hom.comp_apply, hgπ']
  have hsep : ∀ a b, pullback.diagonal f a ≠ (diagCompl f).ι b := by
    intro a b hab
    have hb : (diagCompl f).ι b ∈ Set.range (diagCompl f).ι := ⟨b, rfl⟩
    rw [Scheme.Opens.range_ι] at hb
    exact hb ⟨a, hab⟩
  rw [isIso_iff_isOpenImmersion_and_surjective]
  refine ⟨isOpenImmersion_sigmaDesc _ g ?_, ⟨fun p => ?_⟩⟩
  · intro i j hij
    rw [Function.onFun, Set.disjoint_left]
    rintro _ ⟨x, rfl⟩ ⟨y, hy⟩
    have hπ := congrArg (pullback.fst (pullback.snd f f) v) hy
    rw [hgπ, hgπ] at hπ
    induction i using Fin.cases with
    | zero =>
      induction j using Fin.cases with
      | zero => exact hij rfl
      | succ k =>
        rw [ht0, hts, Scheme.Hom.comp_apply, Scheme.Hom.comp_apply] at hπ
        exact hsep _ _ hπ.symm
    | succ k =>
      induction j using Fin.cases with
      | zero =>
        rw [ht0, hts, Scheme.Hom.comp_apply, Scheme.Hom.comp_apply] at hπ
        exact hsep _ _ hπ
      | succ k' =>
        have h1 : d k' y = d k x := by
          apply eU.isOpenEmbedding.injective
          have hy' : (d k' ≫ eU) y = (d k ≫ eU) x := hy
          rwa [Scheme.Hom.comp_apply, Scheme.Hom.comp_apply] at hy'
        rw [hdΦ, hdΦ, Scheme.Hom.comp_apply, Scheme.Hom.comp_apply] at h1
        have h2 := (sigmaι_eq_iff _ _ _ _ _).mp (Φ.isOpenEmbedding.injective h1)
        exact hij (by rw [(Sigma.mk.inj_iff.mp h2).1])
  · by_cases hp : pullback.fst (pullback.snd f f) v p ∈ Set.range (pullback.diagonal f)
    · have hpD : p ∈ Set.range eD := by
        rw [Scheme.Pullback.range_map]
        exact ⟨hp, ⟨pullback.snd (pullback.snd f f) v p, rfl⟩⟩
      obtain ⟨q, rfl⟩ := hpD
      refine ⟨Sigma.ι (fun _ : Fin (m + 1) => V) 0 (inv l q), ?_⟩
      rw [← Scheme.Hom.comp_apply, Sigma.ι_desc]
      show (l ≫ eD) (inv l q) = eD q
      rw [Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply (inv l), IsIso.inv_hom_id]
      rfl
    · have hpU : p ∈ Set.range eU := by
        rw [Scheme.Pullback.range_map]
        refine ⟨?_, ⟨pullback.snd (pullback.snd f f) v p, rfl⟩⟩
        rw [Set.mem_preimage, Scheme.Opens.range_ι]
        exact hp
      obtain ⟨q, rfl⟩ := hpU
      obtain ⟨⟨k, x⟩, hkx⟩ := (sigmaMk (fun _ : Fin m => V)).surjective (inv Φ q)
      rw [sigmaMk_mk] at hkx
      refine ⟨Sigma.ι (fun _ : Fin (m + 1) => V) k.succ x, ?_⟩
      rw [← Scheme.Hom.comp_apply, Sigma.ι_desc]
      show (d k ≫ eU) x = eU q
      rw [hdΦ, Scheme.Hom.comp_apply, Scheme.Hom.comp_apply, hkx, ← Scheme.Hom.comp_apply (inv Φ),
        IsIso.inv_hom_id]
      rfl

end GlobalTheory.EtC.Tr
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThetaIntegralIntegrable
section
open MeasureTheory GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.GodementJacquet Matrix

namespace GlobalTheory.GodementJacquet

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem eMat_leftInv (r t : ℕ) :
    (Matrix.of fun (i : Fin r) (j : Fin (r + t)) => if (j : ℕ) = i then (1 : k) else 0) * eMat k r t = 1 := by
  ext i j
  rw [Matrix.mul_apply, Finset.sum_eq_single (Fin.castAdd t i)]
  · simp [eMat, Matrix.one_apply, Fin.ext_iff]
  · intro b _ hb
    rw [Matrix.of_apply, if_neg, zero_mul]
    intro hh; exact hb (Fin.ext (by simpa using hh))
  · simp

theorem isLocallyConstant_char_det {n : Type} [Fintype n] [DecidableEq n] {μ : kˣ →* ℂˣ}
    (hμ : IsSmoothChar μ) :
    IsLocallyConstant fun g : GL n k => ((μ (GeneralLinearGroup.det g) : ℂˣ) : ℂ) := by
  set χ : GL n k →* ℂˣ := μ.comp GeneralLinearGroup.det with hχd
  have hχ : IsOpen (χ.ker : Set (GL n k)) := hμ.preimage GeneralLinearGroup.continuous_det
  refine (IsLocallyConstant.iff_eventually_eq _).mpr fun g0 => ?_
  have hn : (fun g => g0⁻¹ * g) ⁻¹' (χ.ker : Set (GL n k)) ∈ nhds g0 :=
    (hχ.preimage (continuous_const.mul continuous_id)).mem_nhds (by simp)
  filter_upwards [hn] with g hg
  have hg' : χ (g0⁻¹ * g) = 1 := hg
  have e : χ g = χ g0 := by
    have := congrArg (χ g0 * ·) hg'
    simp only [← map_mul, mul_inv_cancel_left, mul_one] at this
    exact this
  exact congrArg (fun u : ℂˣ => (u : ℂ)) e

theorem integrable_om_eMat : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    [MeasurableSpace k] [BorelSpace k] (ν : Measure k) [ν.IsAddHaarMeasure] (r t : ℕ) (μ : kˣ →* ℂˣ),
    r ≤ t → IsSmoothChar μ → IsUnitaryChar μ → ∀ (h : GL (Fin (r + t)) k)
      (Φ : Matrix (Fin (r + t)) (Fin r) k → ℂ), Φ ∈ SB (Matrix (Fin (r + t)) (Fin r) k) →
      Integrable (fun g : GL (Fin r) k => om μ g h Φ (eMat k r t)) (volGL ν (Fin r)) := by
  intro k _ _ _ _ _ _ ν _ r t μ hrt hμs hμu h Φ hΦ
  have hu : ∀ x : kˣ, ‖((μ x : ℂˣ) : ℂ)‖ = 1 := hμu
  set Φ' : Matrix (Fin r) (Fin r) k → ℂ := fun x => Φ ((h⁻¹ : GL (Fin (r + t)) k).val * eMat k r t * x)
    with hΦ'
  set P : Matrix (Fin r) (Fin (r + t)) k := Matrix.of fun i j => if (j : ℕ) = i then 1 else 0 with hP
  obtain ⟨hl, hK⟩ : IsLocallyConstant Φ ∧ HasCompactSupport Φ := hΦ
  have hcont : Continuous fun x : Matrix (Fin r) (Fin r) k =>
      (h⁻¹ : GL (Fin (r + t)) k).val * eMat k r t * x :=
    continuous_const.matrix_mul continuous_id
  have hl' : IsLocallyConstant Φ' := hl.comp_continuous hcont
  have hK' : HasCompactSupport Φ' := by
    refine HasCompactSupport.intro (hK.image (f := fun y => P * h.val * y)
      (continuous_const.matrix_mul continuous_id)) fun x hx => ?_
    by_contra h0
    apply hx
    refine ⟨_, subset_tsupport _ h0, ?_⟩
    show P * h.val * ((h⁻¹ : GL _ k).val * eMat k r t * x) = x
    simp only [← Matrix.mul_assoc]
    rw [Matrix.mul_assoc P, Units.mul_inv, Matrix.mul_one, hP, eMat_leftInv, Matrix.one_mul]
  obtain ⟨B, hB⟩ := GlobalTheory.ZetaConvergence.exists_nabs_le (IsCompact.image hK'
    (f := fun x : Matrix (Fin r) (Fin r) k => x.det) continuous_id.matrix_det)
  have := GlobalTheory.SplitWeil.secondCountable k
  have := GlobalTheory.SplitWeil.t2Space k
  have : BorelSpace (Matrix (Fin r) (Fin r) k) := inferInstanceAs (BorelSpace (Fin r → Fin r → k))
  have : (volM ν (Fin r) (Fin r)).IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _
  have : BorelSpace (GL (Fin r) k) := SplitFlip.borel_GL
  have : SecondCountableTopology (GL (Fin r) k) := SplitFlip.secondCountable_GL
  have hE := GlobalTheory.SplitWeil.Model.measurableEmbedding_val (k := k) (Fin r)
  have hd := continuous_density_volGL (k := k) (n := Fin r)
  have hn : IsLocallyConstant fun g : GL (Fin r) k => nabs k (GeneralLinearGroup.det g) :=
    (isLocallyConstant_nabs k).comp_continuous GeneralLinearGroup.continuous_det
  have hI : Integrable (fun g : GL (Fin r) k => Φ' g.val)
      ((volM ν (Fin r) (Fin r)).comap fun g : GL (Fin r) k => g.val) := by
    have h1 : Integrable Φ' (volM ν (Fin r) (Fin r)) := hl'.continuous.integrable_of_hasCompactSupport hK'
    refine (hE.integrable_map_iff (g := Φ')).1 ?_
    rw [hE.map_comap]
    exact h1.restrict
  have hloc : IsLocallyConstant fun g : GL (Fin r) k => om μ g h Φ (eMat k r t) := by
    unfold om
    refine ((((isLocallyConstant_char_det hμs).mul (IsLocallyConstant.const _)).mul
      (hn.comp fun a => ((a ^ ((Fintype.card (Fin (r + t)) : ℝ) / 2) : ℝ) : ℂ))).mul
      (IsLocallyConstant.const _)).mul ?_
    exact hl'.comp_continuous Units.continuous_val
  set c : ℝ := nabs k (GeneralLinearGroup.det h) ^ (-(Fintype.card (Fin r) : ℝ) / 2) with hc
  unfold volGL
  rw [integrable_withDensity_iff_integrable_smul' hd.measurable
    (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  refine (hI.norm.mul_const (c * B ^ (((t : ℝ) - r) / 2))).mono'
    (hd.measurable.ennreal_toReal.aestronglyMeasurable.smul hloc.continuous.aestronglyMeasurable)
    (Filter.Eventually.of_forall fun g => ?_)
  have hp := nabs_pos' k (GeneralLinearGroup.det g)
  have hq := nabs_pos' k (GeneralLinearGroup.det h)
  by_cases h0 : Φ' g.val = 0
  · have : om μ g h Φ (eMat k r t) = 0 := by
      simp only [om]
      rw [show Φ ((h⁻¹ : GL (Fin (r + t)) k).val * eMat k r t * g.val) = 0 from h0, mul_zero]
    simp [this, h0]
  have h1 : nabs k (GeneralLinearGroup.det g) ≤ B := hB _ ⟨g.val, subset_tsupport _ h0, rfl⟩
  set a := nabs k (GeneralLinearGroup.det g) with ha
  have e1 : ‖om μ g h Φ (eMat k r t)‖ = a ^ (((r : ℝ) + t) / 2) * c * ‖Φ' g.val‖ := by
    simp only [om, norm_mul, Units.val_inv_eq_inv_val, norm_inv, hu, Complex.norm_real,
      Real.norm_of_nonneg (Real.rpow_nonneg hp.le _), Real.norm_of_nonneg (Real.rpow_nonneg hq.le _),
      Fintype.card_fin, Nat.cast_add, hc, ha, hΦ']
    rw [Real.norm_of_nonneg (Real.rpow_nonneg (nabs_pos' k _).le _)]
    ring
  rw [norm_smul, ENNReal.toReal_ofReal (Real.rpow_nonneg hp.le _), Real.norm_of_nonneg (Real.rpow_nonneg hp.le _),
    e1, Fintype.card_fin]
  have hc0 : 0 ≤ c := Real.rpow_nonneg hq.le _
  have h2 : a ^ (((t : ℝ) - r) / 2) ≤ B ^ (((t : ℝ) - r) / 2) :=
    Real.rpow_le_rpow hp.le h1 (div_nonneg (sub_nonneg.2 (by exact_mod_cast hrt)) (by norm_num))
  calc a ^ (-(r : ℝ)) * (a ^ (((r : ℝ) + t) / 2) * c * ‖Φ' g.val‖)
      = ‖Φ' g.val‖ * (c * a ^ (((t : ℝ) - r) / 2)) := by
        rw [show ((t : ℝ) - r) / 2 = -(r : ℝ) + ((r : ℝ) + t) / 2 by ring, Real.rpow_add hp]; ring
    _ ≤ ‖Φ' g.val‖ * (c * B ^ (((t : ℝ) - r) / 2)) := by gcongr
end GlobalTheory.GodementJacquet
end

