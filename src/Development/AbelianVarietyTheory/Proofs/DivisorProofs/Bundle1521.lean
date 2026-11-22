import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0056
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.WeightFunctionOnFrames
import Development.AbelianVarietyTheory.BlockTheory.ExistenceTori.UnitaryHaarVolume
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle0028
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.Bundle0023
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1498
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1041
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1371
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1446
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1444
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1479
import Development.AbelianVarietyTheory.Definitions.KeyFormula.GeomIntSelf
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0141
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1499
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0045
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1392
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1462
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0022
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeviBlockSizesSum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WittRankLeSkewSignature
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0331
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1387
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0282
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1504
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1115
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0108

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CovolumeEqOfRealUnitaryConj
section
open NumberField MeasureTheory ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates
open scoped ENNReal Matrix

namespace GlobalTheory.CovolConj

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem mass_le (X : Data E r) {x0 x1 : Frame X.Ψ r} (h0 : IsOrth X x0) (h1 : IsOrth X x1)
    {F0 F1 : Set (V (nd X))} (hF0 : IsFundSet X x0 F0) (hF1 : IsFundSet X x1 F1) :
    muF X x0 F0 ≤ muF X x1 F1 := by
  classical
  have := FundSetPf.countable_GL (E := E) (r := r)
  have hM : MeasInvStatement (E := E) := measInv_holds
  have hle := GlobalTheory.Unfold.lintegral_fundSet_inter_le hM r X x0 x1 h0 h1 F0 hF0 (fun _ => 1)
    measurable_const (fun _ _ _ _ _ _ => rfl) F1 hF1.1 hF1.2.1
  simp only [setLIntegral_one] at hle
  refine le_trans (le_of_eq ?_) hle
  let S : Set (Frame X.Ψ r) :=
    ⋃ γ : X.Γ, (fun x => lact (γ.1)⁻¹ x) ⁻¹' GlobalTheory.Unfold.satFrames X x1 F1
  have hS : MeasurableSet S := MeasurableSet.iUnion fun γ =>
    (GlobalTheory.Unfold.continuous_lact X _).measurable (GlobalTheory.Unfold.measurableSet_satFrames X h1 hF1.1 hF1.2.1)
  have hSiff : ∀ x, x ∈ S ↔ ∃ y ∈ F1, ∃ γ ∈ X.Γ, ∃ b ∈ Bor X.Ψ r,
      x = lact γ (rmul (cpt X x1 y) b) := by
    intro x
    simp only [S, Set.mem_iUnion, Set.mem_preimage]
    constructor
    · rintro ⟨γ, y, hy, b, hb, h⟩
      refine ⟨y, hy, γ.1, γ.2, b, hb, ?_⟩
      rw [← h, ← FundSetPf.lact_mul, mul_inv_cancel, FundSetPf.lact_one]
    · rintro ⟨y, hy, γ, hγ, b, hb, h⟩
      exact ⟨⟨γ, hγ⟩, y, hy, b, hb, by rw [h, FundSetPf.lact_inv]⟩
  have hSB : ∀ x, ∀ b ∈ Bor X.Ψ r, rmul x b ∈ S ↔ x ∈ S := by
    intro x b hb
    simp only [S, Set.mem_iUnion, Set.mem_preimage, FundSetPf.lact_rmul,
      GlobalTheory.Unfold.rmul_mem_satFrames_iff X x1 F1 _ hb]
  have hI := hM r X x0 x1 h0 h1 (Sᶜ.indicator fun _ => 1) (measurable_const.indicator hS.compl)
    (fun x _ b hb => by simp only [Set.indicator, Set.mem_compl_iff, hSB x b hb])
  have hc : ∀ x : Frame X.Ψ r, ∫⁻ z, (Sᶜ.indicator fun _ => (1 : ℝ≥0∞)) (cpt X x z) ∂muF X x =
      muF X x (cpt X x ⁻¹' Sᶜ) := by
    intro x
    rw [← lintegral_indicator_one ((FundSetPf.cont_cpt X x).measurable hS.compl)]
    rfl
  rw [hc, hc] at hI
  have hz1 : muF X x1 (cpt X x1 ⁻¹' Sᶜ) = 0 := by
    have : ∀ᵐ z ∂muF X x1, cpt X x1 z ∈ S := by
      filter_upwards [hF1.2.2.2] with z hz using (hSiff _).2 hz
    exact this
  have hz0 : ∀ᵐ z ∂muF X x0, cpt X x0 z ∈ S := hI.trans hz1
  refine measure_congr ?_
  filter_upwards [hz0] with z hz
  exact propext ⟨fun h => ⟨h, (hSiff _).1 hz⟩, fun h => h.1⟩

theorem mass_eq (X : Data E r) {x0 x1 : Frame X.Ψ r} (h0 : IsOrth X x0) (h1 : IsOrth X x1)
    {F0 F1 : Set (V (nd X))} (hF0 : IsFundSet X x0 F0) (hF1 : IsFundSet X x1 F1) :
    muF X x0 F0 = muF X x1 F1 :=
  le_antisymm (mass_le X h0 h1 hF0 hF1) (mass_le X h1 h0 hF1 hF0)

omit [IsCMField E] [NumberField E] in
theorem gram_eq (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) (x : Matrix (Fin r) (Fin r) ℂ) :
    gram τ G x = xᵀ * G.map τ * x.map (starRingEnd ℂ) := by
  ext a b
  simp only [gram, hermC, col, Matrix.of_apply, Matrix.mul_apply, Matrix.transpose_apply,
    Matrix.map_apply, Finset.sum_mul]
  rw [Finset.sum_comm]

omit [IsCMField E] [NumberField E] in
theorem gram_mul {τ : E →+* ℂ} {G : Matrix (Fin r) (Fin r) E} {u : Matrix (Fin r) (Fin r) ℂ}
    (hu : gram τ G u = G.map τ) (x : Matrix (Fin r) (Fin r) ℂ) : gram τ G (u * x) = gram τ G x := by
  rw [gram_eq] at hu
  rw [gram_eq, gram_eq, Matrix.transpose_mul, Matrix.map_mul]
  conv_rhs => rw [← hu]
  simp only [Matrix.mul_assoc]

omit [IsCMField E] [NumberField E] in
theorem det_ne {τ : E →+* ℂ} {G : Matrix (Fin r) (Fin r) E} (hG : G.det ≠ 0)
    {u : Matrix (Fin r) (Fin r) ℂ} (hu : gram τ G u = G.map τ) : u.det ≠ 0 := by
  intro h
  rw [gram_eq] at hu
  have h2 := congrArg Matrix.det hu
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, h, zero_mul, zero_mul] at h2
  have h3 : τ G.det = (G.map τ).det := RingHom.map_det τ G
  exact hG ((map_eq_zero τ).1 (h3.trans h2.symm))

noncomputable def umul {Ψ : Finset (E →+* ℂ)} (u : (E →+* ℂ) → Matrix (Fin r) (Fin r) ℂ)
    (x : Frame Ψ r) : Frame Ψ r :=
  fun τ => (u τ.1 * mat x τ : Matrix (Fin r) (Fin r) ℂ)

section

variable (X : Data E r) {u : (E →+* ℂ) → Matrix (Fin r) (Fin r) ℂ}

omit [IsCMField E] [NumberField E] in
theorem umul_rmul {Ψ : Finset (E →+* ℂ)} (x b : Frame Ψ r) :
    umul u (rmul x b) = rmul (umul u x) b := by
  funext τ
  exact (Matrix.mul_assoc (u τ.1) (mat x τ) (mat b τ)).symm

theorem cpt_umul (x0 : Frame X.Ψ r) (z : V (nd X)) :
    cpt X (umul u x0) z = umul u (cpt X x0 z) := (umul_rmul _ _).symm

theorem gram_umul (hu : ∀ τ ∈ X.Ψ, gram τ X.Gm (u τ) = X.Gm.map τ) (x : Frame X.Ψ r) (τ : X.Ψ) :
    gram τ.1 X.Gm (mat (umul u x) τ) = gram τ.1 X.Gm (mat x τ) :=
  gram_mul (hu τ.1 τ.2) _

theorem umul_mem_dom (hu : ∀ τ ∈ X.Ψ, gram τ X.Gm (u τ) = X.Gm.map τ) (x : Frame X.Ψ r) :
    umul u x ∈ X.dom ↔ x ∈ X.dom := by
  refine forall_congr' fun τ => and_congr ?_ ?_
  · have : mat (umul u x) τ = u τ.1 * mat x τ := rfl
    rw [this, Matrix.det_mul]
    exact ⟨right_ne_zero_of_mul, mul_ne_zero (det_ne X.Gm_det (hu τ.1 τ.2))⟩
  · simp only [dmin, gram_umul X hu]

theorem umul_inj (hu : ∀ τ ∈ X.Ψ, gram τ X.Gm (u τ) = X.Gm.map τ) {x y : Frame X.Ψ r}
    (h : umul u x = umul u y) : x = y := by
  funext τ
  have h1 : u τ.1 * mat x τ = u τ.1 * mat y τ := congrFun h τ
  have hd : IsUnit (u τ.1).det := isUnit_iff_ne_zero.mpr (det_ne X.Gm_det (hu τ.1 τ.2))
  have := congrArg (fun M => (u τ.1)⁻¹ * M) h1
  simp only [Matrix.nonsing_inv_mul_cancel_left _ _ hd] at this
  exact this

theorem umul_lact {γ γ' : GL (Fin r) E}
    (h : ∀ τ ∈ X.Ψ, u τ * (γ : Matrix (Fin r) (Fin r) E).map τ =
      (γ' : Matrix (Fin r) (Fin r) E).map τ * u τ) (x : Frame X.Ψ r) :
    umul u (lact γ x) = lact γ' (umul u x) := by
  funext τ
  show u τ.1 * ((γ : Matrix (Fin r) (Fin r) E).map τ.1 * mat x τ) =
    (γ' : Matrix (Fin r) (Fin r) E).map τ.1 * (u τ.1 * mat x τ)
  rw [← Matrix.mul_assoc, h τ.1 τ.2, Matrix.mul_assoc]

theorem isOrth_umul (hu : ∀ τ ∈ X.Ψ, gram τ X.Gm (u τ) = X.Gm.map τ) {x0 : Frame X.Ψ r}
    (ho : IsOrth X x0) : IsOrth X (umul u x0) := fun τ => by
  rw [gram_umul X hu]; exact ho τ

theorem OmF_umul (hu : ∀ τ ∈ X.Ψ, gram τ X.Gm (u τ) = X.Gm.map τ) (x0 : Frame X.Ψ r) :
    OmF X (umul u x0) = OmF X x0 := by
  ext z
  show cpt X (umul u x0) z ∈ X.dom ↔ cpt X x0 z ∈ X.dom
  rw [cpt_umul, umul_mem_dom X hu]

theorem muF_umul (hu : ∀ τ ∈ X.Ψ, gram τ X.Gm (u τ) = X.Gm.map τ) (x0 : Frame X.Ψ r) :
    muF X (umul u x0) = muF X x0 := by
  have h2 : densF X (umul u x0) = densF X x0 := by
    funext z
    simp only [densF, dmin, cpt_umul, gram_umul X hu]
  simp only [muF, OmF_umul X hu, h2]

theorem fundSet_umul (hu : ∀ τ ∈ X.Ψ, gram τ X.Gm (u τ) = X.Gm.map τ)
    (Γ' : Subgroup (GL (Fin r) E))
    (h1 : ∀ γ ∈ X.Γ, ∃ γ' ∈ Γ', ∀ τ ∈ X.Ψ, u τ * (γ : Matrix (Fin r) (Fin r) E).map τ =
      (γ' : Matrix (Fin r) (Fin r) E).map τ * u τ)
    (h2 : ∀ γ' ∈ Γ', ∃ γ ∈ X.Γ, ∀ τ ∈ X.Ψ, u τ * (γ : Matrix (Fin r) (Fin r) E).map τ =
      (γ' : Matrix (Fin r) (Fin r) E).map τ * u τ)
    {x0 : Frame X.Ψ r} {FF : Set (V (nd X))} (hF : IsFundSet X x0 FF) :
    MeasurableSet FF ∧ FF ⊆ OmF X (umul u x0) ∧
    (∀ z ∈ FF, ∀ z' ∈ FF, ∀ γ ∈ Γ', ∀ b ∈ Bor X.Ψ r,
      cpt X (umul u x0) z' = lact γ (rmul (cpt X (umul u x0) z) b) → z = z') ∧
    ∀ᵐ z ∂muF X (umul u x0), ∃ z' ∈ FF, ∃ γ ∈ Γ', ∃ b ∈ Bor X.Ψ r,
      cpt X (umul u x0) z = lact γ (rmul (cpt X (umul u x0) z') b) := by
  refine ⟨hF.1, by rw [OmF_umul X hu]; exact hF.2.1, ?_, ?_⟩
  · intro z hz z' hz' γ' hγ' b hb h
    obtain ⟨γ, hγ, hc⟩ := h2 γ' hγ'
    rw [cpt_umul, cpt_umul, ← umul_rmul, ← umul_lact X hc] at h
    exact hF.2.2.1 z hz z' hz' γ hγ b hb (umul_inj X hu h)
  · rw [muF_umul X hu]
    filter_upwards [hF.2.2.2] with z hz
    obtain ⟨z', hz', γ, hγ, b, hb, h⟩ := hz
    obtain ⟨γ', hγ', hc⟩ := h1 γ hγ
    refine ⟨z', hz', γ', hγ', b, hb, ?_⟩
    rw [cpt_umul, cpt_umul, ← umul_rmul, ← umul_lact X hc, h]

end

theorem muF_eq_of_conj : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X X' : Data E r) (hΨ : X'.Ψ = X.Ψ) (u : (E →+* ℂ) → Matrix (Fin r) (Fin r) ℂ) (x0 : Frame X.Ψ r) (x0' : Frame X'.Ψ r) (FF : Set (V (nd X))) (FF' : Set (V (nd X'))), X'.Gm = X.Gm → X'.p0 = X.p0 → (∀ τ ∈ X.Ψ, gram τ X.Gm (u τ) = X.Gm.map τ) → (∀ γ ∈ X.Γ, ∃ γ' ∈ X'.Γ, ∀ τ ∈ X.Ψ, u τ * (γ : Matrix (Fin r) (Fin r) E).map τ = (γ' : Matrix (Fin r) (Fin r) E).map τ * u τ) → (∀ γ' ∈ X'.Γ, ∃ γ ∈ X.Γ, ∀ τ ∈ X.Ψ, u τ * (γ : Matrix (Fin r) (Fin r) E).map τ = (γ' : Matrix (Fin r) (Fin r) E).map τ * u τ) → IsOrth X x0 → IsOrth X' x0' → IsFundSet X x0 FF → IsFundSet X' x0' FF' → muF X x0 FF = muF X' x0' FF' := by
  intro E _ _ _ r X X' hΨ u x0 x0' FF FF' hG hp hu h1 h2 ho ho' hF hF'
  have k1 := isOrth_umul X hu ho
  have k2 := fundSet_umul X hu X'.Γ h1 h2 hF
  rw [← muF_umul X hu x0]
  have k3 := fun (y : Frame X'.Ψ r) (F : Set (V (nd X'))) (hy : IsOrth X' y) (hF0 : IsFundSet X' y F) =>
    mass_eq X' hy ho' hF0 hF'
  cases X
  cases X'
  dsimp only at hΨ hG hp
  subst hΨ hG hp
  exact k3 (umul u x0) FF k1 k2

end GlobalTheory.CovolConj
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoubledSpaceSplittingConstantHalfRealPlacesStatement
section
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix Classical
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift GlobalTheory.RealLift.Dbl

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.doubledSpace_splitting_constant_half_realPlaces : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (α β κ : Type) [Fintype α]
    [DecidableEq α] [Fintype β] [DecidableEq β] [Fintype κ] (P Q R S : ℕ) (ψ : AddChar (AF F) ℂ)
    (τ : ∀ w : InfinitePlace F, EmbOver E w) (JA : Matrix α α (AE F E)) (JB : Matrix β β (AE F E))
    (dd : Darboux (symp (R := AF F) (cA σ) (-1) JA (dbl JB)) (κ ⊕ κ)) (a b : ℂ) (A : InfinitePlace F → Matrix α (Ix P Q) ℂ)
    (C : InfinitePlace F → Matrix β (Ix R S) ℂ) (Φd : Tens F P Q (R + S) (S + R) →ₗ[ℂ] SInf F (κ ⊕ κ))
    (omd : UG (cA σ) (dbl JB) →* Module.End ℂ ((κ ⊕ κ → AF F) → ℂ)) (χ : Chr F E) (m : InfinitePlace F → ℤ)
    (cd : InfinitePlace F → ℂ),
    IsCMExt F E σ → IsStd ψ → Framed τ JA JB a b A C →
    IsUWeilSplit (cA σ) (adeleClass F) ψ (-1) JA (dbl JB) dd χ (diagCols β) omd → HasExp τ χ m →
    ActsBy τ (fun w => dblM (C w)) omd Φd (fockAct2 P Q (R + S) (S + R)) cd →
    (∃ l ∈ (adeleClass F).adm (κ ⊕ κ), (∀ z : Matrix α β (AE F E), ∀ φ ∈ (adeleClass F).sp (κ ⊕ κ),
      l (dd.rho ψ (z * (diagCols β : Matrix (β ⊕ β) β (AE F E))ᵀ) φ) = l φ) ∧
      ∃ g ∈ SB (κ ⊕ κ → Af F), ∀ f : SInf F (κ ⊕ κ),
        l (pureA F f g) = ∫ x : κ → mixedEmbedding.mixedSpace F, f (Sum.elim x x)) →
    (∫ x : κ → mixedEmbedding.mixedSpace F, Φd (PiTensorProduct.tprod ℂ fun _ => 1) (Sum.elim x x)) ≠ 0 →
    0 < R + S → ∀ w, cd w = m w / 2 := by
  first | exact @GlobalTheory.RealLift.DConst.cd_eq_half_exp | exact GlobalTheory.RealLift.DConst.cd_eq_half_exp | (intros; apply GlobalTheory.RealLift.DConst.cd_eq_half_exp <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EisensteinSettingHeightContinuousStatement
section
open scoped TensorProduct NNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.EisRes
open GlobalTheory.Doubling (absE)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eisenstein_setting_height_continuous : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ)
    (J : Matrix (Fin n) (Fin n) E) (r : ℕ) (X Y : Matrix (Fin n) (Fin (r + 1)) E) (L : Submodule (𝓞 E) (Fin n → E))
    (a : GL (Fin n) (AF F ⊗[F] E)) (h : GAd σ J → ℝ), HidaSetting σ J X Y L a h → Continuous h := by
  first | exact @GlobalTheory.EisRes.HtCont.continuous_iwaHt | exact GlobalTheory.EisRes.HtCont.continuous_iwaHt | (intros; apply GlobalTheory.EisRes.HtCont.continuous_iwaHt <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAppellHumbertUnimodularRiemannForm
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.ZM GlobalTheory.KeyFam

namespace GlobalTheory.PolUnif

theorem hermForm_self_im {g : ℕ} {Hm : Matrix (Fin g) (Fin g) ℂ} (hH : Hm.IsHermitian) (x : Fin g → ℂ) :
    (hermForm Hm x x).im = 0 := by
  have h := hH.im_star_dotProduct_mulVec_self (star x)
  rw [star_star] at h
  exact h

theorem exists_unif_riemannForm : ∀ (h : ℕ) (P : Out.PolAV (Sp ℂ)), P.g = h → ∃ (u : HolUnif P.A P.L h) (Hm : Matrix (Fin h) (Fin h) ℂ) (χ : u.Λ → ℂ) (Ef : LinearMap.BilinForm ℤ u.Λ), u.IsAH Hm χ ∧ (∀ x y : u.Λ, (Ef x y : ℝ) = (hermForm Hm x y).im) ∧ Function.Bijective Ef ∧ (∀ x, Ef x x = 0) ∧ Module.Free ℤ u.Λ ∧ Module.Finite ℤ u.Λ ∧ Module.finrank ℤ u.Λ = 2 * h ∧ ∀ (n : ℕ) (x y : u.Λ) (e : ℂˣ), 0 < n → (e : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * (Ef x y : ℂ) / n) → Out.WeilIs P.A P.L n (u.ex ((n : ℂ)⁻¹ • (x : Fin h → ℂ))) (u.ex ((n : ℂ)⁻¹ • (y : Fin h → ℂ))) (unitOn e) := by
  intro h P hg
  subst hg
  obtain ⟨rig, hrig⟩ := P.rigid
  obtain ⟨u, Hm, χ, Ef, hAH, -, -, -, -, -, hE, hbij, hW⟩ := GlobalTheory.thetaUnifAV_all P rig hrig
  haveI : DiscreteTopology u.Λ := u.discrete
  haveI : IsZLattice ℝ u.Λ := ⟨u.full⟩
  refine ⟨u, Hm, χ, Ef, hAH, hE, hbij, fun x => ?_, ZLattice.module_free ℝ u.Λ, ZLattice.module_finite ℝ u.Λ, ?_, hW⟩
  · have h1 := hE x x
    rw [hermForm_self_im hAH.1] at h1
    exact_mod_cast h1
  · rw [ZLattice.rank ℝ u.Λ, Module.finrank_pi_fintype]
    simp [mul_comm]

end GlobalTheory.PolUnif
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsArchimedeanPhaseSpaceComplexStructureSignaStatement
section
open scoped TensorProduct Matrix GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Classical
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift GlobalTheory.VacLn
open GlobalTheory.HoweD
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_archimedeanPhaseSpace_complexStructure_signatures : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (α β κ : Type) [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] [Fintype κ] (P Q R S : InfinitePlace F → ℕ)
    (τ : ∀ w : InfinitePlace F, EmbOver E w) (JA : Matrix α α (AE F E)) (JB : Matrix β β (AE F E))
    (d : Darboux (symp (R := AF F) (cA σ) (-1) JA JB) κ) (a b : ℂ) (A : ∀ w : InfinitePlace F, Matrix α (Ix (P w) (Q w)) ℂ)
    (C : ∀ w : InfinitePlace F, Matrix β (Ix (R w) (S w)) ℂ) (ε : InfinitePlace F → ℤˣ), IsCMExt F E σ → FramedD τ JA JB a b A C →
    ∃ (J e : ((κ → mixedEmbedding.mixedSpace F) × (κ → mixedEmbedding.mixedSpace F)) →ₗ[ℝ]
        ((κ → mixedEmbedding.mixedSpace F) × (κ → mixedEmbedding.mixedSpace F)))
      (e' : (κ → mixedEmbedding.mixedSpace F) →ₗ[ℝ] (κ → mixedEmbedding.mixedSpace F)),
      (∀ y, J (J y) = -y) ∧ (∀ y, e (e y) = e y) ∧ (∀ y, J (e y) = e (J y)) ∧ (∀ y, (e y).1 = e' y.1) ∧
      (∀ y x, trPair F κ x (e y).2 = trPair F κ (e' x) y.2) ∧
      ∀ y, ∃ (u u' u₁ : Matrix α β (AE F E)) (c : ∀ w : InfinitePlace F, Matrix (Ix (P w) (Q w)) (Ix (R w) (S w)) ℂ),
        At (evI F) u ∧ At (evI F) u' ∧ At (evI F) u₁ ∧ (∀ w, u.map (piInf (τ w)) = A w * c w * (C w)ᵀ) ∧
        (∀ w, u'.map (piInf (τ w)) = A w * ((((ε w : ℤ) : ℂ) * Complex.I) • (Jm (P w) (Q w) * c w * Jm (R w) (S w))) * (C w)ᵀ) ∧
        (∀ w, u₁.map (piInf (τ w)) = A w * (Complex.I • (Jm (P w) (Q w) * c w * Jm (R w) (S w))) * (C w)ᵀ) ∧
        coord d u = y ∧ coord d u' = J (y - (2 : ℝ) • e y) ∧ coord d u₁ = J y := by
  first | exact @GlobalTheory.HoweD.exists_bridgeD | exact GlobalTheory.HoweD.exists_bridgeD | (intros; apply GlobalTheory.HoweD.exists_bridgeD <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBlockEmb
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SmGL GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.LeviBlockExponent GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
  GlobalTheory.UAut GlobalTheory.SiegelSet GlobalTheory.ThK.SquareIntegrability GlobalTheory.CuspBlock GlobalTheory.LFun.SplitTie
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section
open scoped TensorProduct
open Matrix
open Formalism.UG (cT)

namespace GlobalTheory.BlockFormsEmb

section Alg
variable {R : Type} [CommRing R] {n d : ℕ}

theorem cT_add' (s : R →+* R) {m p : Type} (A B : Matrix m p R) : cT s (A + B) = cT s A + cT s B :=
  Matrix.ext fun i j => by simp [cT]

theorem cT_sub' (s : R →+* R) {m p : Type} (A B : Matrix m p R) : cT s (A - B) = cT s A - cT s B :=
  Matrix.ext fun i j => by simp [cT]

def blk (a b : Matrix (Fin n) (Fin d) R) (α β : Matrix (Fin d) (Fin n) R) (H K : Matrix (Fin d) (Fin d) R) :
    Matrix (Fin n) (Fin n) R := 1 + a * (H - 1) * α + b * (K - 1) * β

variable {a b : Matrix (Fin n) (Fin d) R} {α β : Matrix (Fin d) (Fin n) R}

theorem blk_one : blk a b α β 1 1 = 1 := by simp [blk]

theorem blk_mul (hαa : α * a = 1) (hβb : β * b = 1) (hαb : α * b = 0) (hβa : β * a = 0)
    (H K H' K' : Matrix (Fin d) (Fin d) R) :
    blk a b α β H K * blk a b α β H' K' = blk a b α β (H * H') (K * K') := by
  first
  | exact @_root_.GlobalTheory.SquareDistanceExpansion.main
  | exact _root_.GlobalTheory.SquareDistanceExpansion.main
  | (apply _root_.GlobalTheory.SquareDistanceExpansion.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.SquareDistanceExpansion.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.SquareDistanceExpansion.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.SquareDistanceExpansion.main ..)

theorem blk_unitary (s : R →+* R) (Jm : Matrix (Fin n) (Fin n) R)
    (hαa : α * a = 1) (hβb : β * b = 1) (hαb : α * b = 0) (hβa : β * a = 0)
    (hα : cT s α = Jm * b) (hβ : cT s β = Jm * a) (ha : cT s a * Jm = β) (hb : cT s b * Jm = α)
    (H K : Matrix (Fin d) (Fin d) R) (h1 : cT s K * H = 1) (h2 : cT s H * K = 1) :
    cT s (blk a b α β H K) * Jm * blk a b α β H K = Jm := by
  have key : cT s (blk a b α β H K) * Jm = Jm * blk a b α β (cT s K) (cT s H) := by
    unfold blk
    rw [cT_add', cT_add', Formalism.UG.cT_one, Formalism.UG.cT_mul, Formalism.UG.cT_mul, Formalism.UG.cT_mul, Formalism.UG.cT_mul, cT_sub', cT_sub',
      Formalism.UG.cT_one, hα, hβ]
    simp only [Matrix.add_mul, Matrix.mul_add, Matrix.mul_one, Matrix.one_mul, Matrix.mul_assoc, ha, hb]
    abel
  rw [key, Matrix.mul_assoc, blk_mul hαa hβb hαb hβa, h1, h2, blk_one, Matrix.mul_one]

end Alg

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.BlockForms

section Main

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem sigR_inclR (σ : E →ₐ[F] E) (x : E) :
    sigR (AF F) σ (inclR (F := F) (AF F) x) = inclR (F := F) (AF F) (σ x) := by
  simp [sigR, inclR]

theorem cT_adMat (σ : E →ₐ[F] E) {m p : Type} (Z : Matrix m p E) :
    cT (sigR (AF F) σ) (adMat F Z) = adMat F (cT (σ : E →+* E) Z) :=
  Matrix.ext fun i j => by simp only [cT, adMat, Matrix.transpose_apply, Matrix.map_apply, sigR_inclR]; rfl

theorem adMat_mul' {m p q : Type} [Fintype p] (A : Matrix m p E) (B : Matrix p q E) :
    adMat F (A * B) = adMat F A * adMat F B := Matrix.map_mul

theorem adMat_one' {m : Type} [Fintype m] [DecidableEq m] : adMat F (1 : Matrix m m E) = 1 :=
  Matrix.map_one _ (map_zero _) (map_one _)

theorem adMat_zero' {m p : Type} : adMat F (0 : Matrix m p E) = 0 := Matrix.map_zero _ (map_zero _)

theorem sigR_sigR' (σ : E →ₐ[F] E) (hσ : ∀ x, σ (σ x) = x) (z : AF F ⊗[F] E) :
    sigR (AF F) σ (sigR (AF F) σ z) = z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a x => simp [sigR, hσ]
  | add x y hx hy => rw [map_add, map_add, hx, hy]

theorem blkCols_gram {n r l d : ℕ} (h : l + d ≤ r) (σ : E →ₐ[F] E) (J : Matrix (Fin n) (Fin n) E)
    (Z W : Matrix (Fin n) (Fin r) E) :
    cT (σ : E →+* E) (blkCols h Z) * J * blkCols h W =
      (cT (σ : E →+* E) Z * J * W).submatrix (fun j : Fin d => (⟨l + j.val, by omega⟩ : Fin r))
        (fun j : Fin d => (⟨l + j.val, by omega⟩ : Fin r)) := by
  first
  | rfl
  | (ext i j; simp [Matrix.mul_apply, blkCols, cT])

def embMat (σ : E →ₐ[F] E) (Φ : AF F ⊗[F] E ≃+* AdeleRing (𝓞 E) E) {n d : ℕ}
    (a b : Matrix (Fin n) (Fin d) (AF F ⊗[F] E)) (α β : Matrix (Fin d) (Fin n) (AF F ⊗[F] E))
    (g : GlobalTheory.CuspRep.GA E d) : Matrix (Fin n) (Fin n) (AF F ⊗[F] E) :=
  blk a b α β (g.1.map Φ.symm) (cT (sigR (AF F) σ) ((g⁻¹).1.map Φ.symm))

variable (σ : E →ₐ[F] E) (Φ : AF F ⊗[F] E ≃+* AdeleRing (𝓞 E) E) {n d : ℕ}
  {a b : Matrix (Fin n) (Fin d) (AF F ⊗[F] E)} {α β : Matrix (Fin d) (Fin n) (AF F ⊗[F] E)}

theorem map_symm_mul (A B : Matrix (Fin d) (Fin d) (AdeleRing (𝓞 E) E)) :
    (A * B).map Φ.symm = A.map Φ.symm * B.map Φ.symm := Matrix.map_mul (f := Φ.symm.toRingHom)

theorem map_symm_one : (1 : Matrix (Fin d) (Fin d) (AdeleRing (𝓞 E) E)).map Φ.symm = 1 :=
  Matrix.map_one _ (map_zero _) (map_one _)

theorem embMat_one : embMat σ Φ a b α β 1 = 1 := by
  simp only [embMat, inv_one, Units.val_one, map_symm_one, Formalism.UG.cT_one, blk_one]

theorem embMat_mul (hαa : α * a = 1) (hβb : β * b = 1) (hαb : α * b = 0) (hβa : β * a = 0)
    (g g' : GlobalTheory.CuspRep.GA E d) : embMat σ Φ a b α β (g * g') = embMat σ Φ a b α β g * embMat σ Φ a b α β g' := by
  unfold embMat
  rw [blk_mul hαa hβb hαb hβa, Units.val_mul, _root_.mul_inv_rev, Units.val_mul, map_symm_mul, map_symm_mul, Formalism.UG.cT_mul]

theorem embMat_unitary (hσ : ∀ x, σ (σ x) = x) (Jm : Matrix (Fin n) (Fin n) (AF F ⊗[F] E))
    (hαa : α * a = 1) (hβb : β * b = 1) (hαb : α * b = 0) (hβa : β * a = 0)
    (hα : cT (sigR (AF F) σ) α = Jm * b) (hβ : cT (sigR (AF F) σ) β = Jm * a)
    (ha : cT (sigR (AF F) σ) a * Jm = β) (hb : cT (sigR (AF F) σ) b * Jm = α) (g : GlobalTheory.CuspRep.GA E d) :
    cT (sigR (AF F) σ) (embMat σ Φ a b α β g) * Jm * embMat σ Φ a b α β g = Jm := by
  have hcc : ∀ A : Matrix (Fin d) (Fin d) (AF F ⊗[F] E), cT (sigR (AF F) σ) (cT (sigR (AF F) σ) A) = A :=
    fun A => Matrix.ext fun i j => by simp only [cT, Matrix.transpose_apply, Matrix.map_apply]; exact sigR_sigR' σ hσ _
  have hgg : (g⁻¹).1.map Φ.symm * g.1.map Φ.symm = 1 := by
    rw [← map_symm_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, map_symm_one]
  unfold embMat
  refine blk_unitary _ Jm hαa hβb hαb hβa hα hβ ha hb _ _ ?_ ?_
  · rw [hcc, hgg]
  · rw [← Formalism.UG.cT_mul, hgg, Formalism.UG.cT_one]

end Main

theorem exists_blockEmb : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [IsTotallyComplex E] [Algebra F E]
    (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J →
    ∀ (r : ℕ) (Xf Yf : Matrix (Fin n) (Fin r) E), IsWittFrame σ J Xf Yf → ∀ (l d : ℕ) (h : l + d ≤ r), ∃ ι : GlobalTheory.CuspRep.GA E d →* GAd σ J, GlobalTheory.BlockForms.IsBlockEmb σ J Xf Yf h ι := by
  intro F E _ _ _ _ _ _ σ hcm n J hJ r Xf Yf hW l d h
  obtain ⟨Φ, j, hc1, hc2, hj, hΦ⟩ := GlobalTheory.HeckeBridge.exists_tensor_adele_equiv F E σ hcm
  have hσ : ∀ x, σ (σ x) = x := fun x => by
    obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
    exact τ.injective (by rw [hcm.2.2.2, hcm.2.2.2, star_star])
  have hJT : cT (σ : E →+* E) J = J := Matrix.ext fun i j => hJ.1 i j
  have hcc : ∀ {m p : Type} (Z : Matrix m p E), cT (σ : E →+* E) (cT (σ : E →+* E) Z) = Z :=
    fun Z => Matrix.ext fun _ _ => hσ _
  have hyx : cT (σ : E →+* E) Yf * J * Xf = 1 := by
    have := congrArg (cT (σ : E →+* E)) hW.xy
    rwa [Formalism.UG.cT_mul, Formalism.UG.cT_mul, hcc, hJT, Formalism.UG.cT_one, ← Matrix.mul_assoc] at this
  have he : Function.Injective (fun j : Fin d => (⟨l + j.val, by omega⟩ : Fin r)) := fun i k e =>
    Fin.ext (by have := congrArg Fin.val e; simp only at this; omega)
  have q1 : cT (σ : E →+* E) (blkCols h Yf) * J * blkCols h Xf = 1 := by
    rw [blkCols_gram, hyx, Matrix.submatrix_one _ he]
  have q2 : cT (σ : E →+* E) (blkCols h Xf) * J * blkCols h Yf = 1 := by
    rw [blkCols_gram, hW.xy, Matrix.submatrix_one _ he]
  have q3 : cT (σ : E →+* E) (blkCols h Yf) * J * blkCols h Yf = 0 := by
    rw [blkCols_gram, hW.yy, Matrix.submatrix_zero]; rfl
  have q4 : cT (σ : E →+* E) (blkCols h Xf) * J * blkCols h Xf = 0 := by
    rw [blkCols_gram, hW.xx, Matrix.submatrix_zero]; rfl
  have hαa : adMat F (cT (σ : E →+* E) (blkCols h Yf) * J) * adMat F (blkCols h Xf) = 1 := by
    rw [← adMat_mul', q1, adMat_one']
  have hβb : adMat F (cT (σ : E →+* E) (blkCols h Xf) * J) * adMat F (blkCols h Yf) = 1 := by
    rw [← adMat_mul', q2, adMat_one']
  have hαb : adMat F (cT (σ : E →+* E) (blkCols h Yf) * J) * adMat F (blkCols h Yf) = 0 := by
    rw [← adMat_mul', q3, adMat_zero']
  have hβa : adMat F (cT (σ : E →+* E) (blkCols h Xf) * J) * adMat F (blkCols h Xf) = 0 := by
    rw [← adMat_mul', q4, adMat_zero']
  have hα : cT (sigR (AF F) σ) (adMat F (cT (σ : E →+* E) (blkCols h Yf) * J)) = adMat F J * adMat F (blkCols h Yf) := by
    rw [cT_adMat, Formalism.UG.cT_mul, hcc, hJT, adMat_mul']
  have hβ : cT (sigR (AF F) σ) (adMat F (cT (σ : E →+* E) (blkCols h Xf) * J)) = adMat F J * adMat F (blkCols h Xf) := by
    rw [cT_adMat, Formalism.UG.cT_mul, hcc, hJT, adMat_mul']
  have ha : cT (sigR (AF F) σ) (adMat F (blkCols h Xf)) * adMat F J = adMat F (cT (σ : E →+* E) (blkCols h Xf) * J) := by
    rw [cT_adMat, ← adMat_mul']
  have hb : cT (sigR (AF F) σ) (adMat F (blkCols h Yf)) * adMat F J = adMat F (cT (σ : E →+* E) (blkCols h Yf) * J) := by
    rw [cT_adMat, ← adMat_mul']
  let M := embMat σ Φ (adMat F (blkCols h Xf)) (adMat F (blkCols h Yf))
    (adMat F (cT (σ : E →+* E) (blkCols h Yf) * J)) (adMat F (cT (σ : E →+* E) (blkCols h Xf) * J))
  have hMmul : ∀ g g', M (g * g') = M g * M g' := embMat_mul σ Φ hαa hβb hαb hβa
  have hMone : M 1 = 1 := embMat_one σ Φ
  have hMu : ∀ g, cT (sigR (AF F) σ) (M g) * JR (AF F) J * M g = JR (AF F) J :=
    embMat_unitary σ Φ hσ (adMat F J) hαa hβb hαb hβa hα hβ ha hb
  let U : GlobalTheory.CuspRep.GA E d → GL (Fin n) (AF F ⊗[F] E) := fun g =>
    ⟨M g, M g⁻¹, by rw [← hMmul, mul_inv_cancel, hMone], by rw [← hMmul, inv_mul_cancel, hMone]⟩
  let ι : GlobalTheory.CuspRep.GA E d →* GAd σ J :=
    { toFun := fun g => (⟨U g, hMu g⟩ : HR (AF F) σ J)
      map_one' := Subtype.ext (Units.ext hMone)
      map_mul' := fun g g' => Subtype.ext (Units.ext (hMmul g g')) }
  exact ⟨ι, Φ, j, hc1, hc2, hj, hΦ, fun g => rfl⟩

end GlobalTheory.BlockFormsEmb
end
end

