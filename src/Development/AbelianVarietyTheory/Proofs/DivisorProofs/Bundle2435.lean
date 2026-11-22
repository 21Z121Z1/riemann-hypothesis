import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0032
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0029
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2364
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2310
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2357
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0073
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0030
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0060
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2248
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TangentHaarRealSUOfMap
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.NonemptyCompactDualHaar
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2349
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0042
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0006
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0012
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0827
import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.FiniteCohPushforwardIffOfIsClosedImmersion
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.CechModulesFunctorShortExactOfIsAffineOpen
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0252
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1194
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2356
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2358
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2304
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2359
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0033

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RepresentsAdditiveLineBundleFamiliesCompare
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

namespace GlobalTheory.Pinch

variable {S : Scheme.{0}}

theorem isPullback_fst_whiskerRight {X Y : Over S} (f : X ⟶ Y) (W : Over S) :
    IsPullback (fst X W) (f ▷ W) f (fst Y W) := by
  refine ⟨⟨by simp⟩, ⟨PullbackCone.IsLimit.mk _ (fun s => lift s.fst (s.snd ≫ snd _ _)) (fun s => by simp)
    (fun s => ?_) fun s l h1 h2 => ?_⟩⟩
  · ext1
    · simp [s.condition]
    · simp
  · ext1
    · simp [← h1]
    · simp [← h2]

theorem isPullback_snd_whiskerLeft (W : Over S) {X Y : Over S} (f : X ⟶ Y) :
    IsPullback (snd W X) (W ◁ f) f (snd W Y) := by
  refine ⟨⟨by simp⟩, ⟨PullbackCone.IsLimit.mk _ (fun s => lift (s.snd ≫ fst _ _) s.fst) (fun s => by simp)
    (fun s => ?_) fun s l h1 h2 => ?_⟩⟩
  · ext1
    · simp
    · simp [s.condition]
  · ext1
    · simp [← h2]
    · simp [← h1]

theorem rep_cmp (S : Scheme.{0}) (A B' S' C Z : Over S) [GrpObj A] (b' : B' ⟶ S') (P' : LB (A ⊗ B').left)
    (e : C ⟶ Z) (Q : LB (A ⊗ C).left) (h₁ : Rep A b' P') (h₂ : Rep A e Q) :
    ∃ q : B' ⊗ Z ⟶ C, q ≫ e = snd B' Z ∧ IsPullback q.left (fst B' Z ≫ b').left C.hom S'.hom ∧
      Same A P' Q (fst B' Z) q := by
  have r₁ := Rep.baseChange S A B' S' (S' ⊗ Z) (B' ⊗ Z) b' P' (fst S' Z) (fst B' Z) (b' ▷ Z) h₁
    (isPullback_fst_whiskerRight b' Z)
  have r₂ := Rep.baseChange S A C Z (S' ⊗ Z) (S' ⊗ C) e Q (snd S' Z) (snd S' C) (S' ◁ e) h₂
    (isPullback_snd_whiskerLeft S' e)
  obtain ⟨ε, hε, hs⟩ := rep_unique S A (B' ⊗ Z) (S' ⊗ C) (S' ⊗ Z) (b' ▷ Z) _ (S' ◁ e) _ r₁ r₂
  have hf : ε.hom.left ≫ (fst S' C).left = (fst B' Z ≫ b').left := by
    rw [← Over.comp_left, ← whiskerLeft_fst S' e, reassoc_of% hε, whiskerRight_fst]
  refine ⟨ε.hom ≫ snd S' C, ?_, ?_, ?_⟩
  · rw [Category.assoc, ← whiskerLeft_snd, reassoc_of% hε, whiskerRight_snd]
  · have hpb : IsPullback (snd S' C).left (fst S' C).left C.hom S'.hom :=
      (IsPullback.of_hasPullback S'.hom C.hom).flip
    have : IsIso ε.hom.left := ⟨⟨ε.inv.left, by rw [← Over.comp_left, ε.hom_inv_id, Over.id_left],
      by rw [← Over.comp_left, ε.inv_hom_id, Over.id_left]⟩⟩
    have hiso : IsPullback ε.hom.left (fst B' Z ≫ b').left (fst S' C).left (𝟙 S'.left) :=
      IsPullback.of_horiz_isIso ⟨by rw [hf, Category.comp_id]⟩
    have := hiso.paste_horiz hpb
    rwa [Category.id_comp, ← Over.comp_left] at this
  · rw [same_iff h₁.fam.isLB h₂.fam.isLB]
    rw [same_iff r₁.fam.isLB r₂.fam.isLB, evc_ev h₁.fam.isLB, evc_ev h₂.fam.isLB] at hs
    simpa [lift_fst, lift_snd_assoc] using hs

end GlobalTheory.Pinch
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RescaleDegDataTrivialisationsPsiEvenOfSqrt
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.PolDeg

theorem rescale_psiEven : ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (h eta : D.X → (FractionRing R)ˣ),
    EvenDefect D h → (∀ a b, eta (a + b) = eta a * eta b) → (∀ a, eta a ^ 2 = h a) → (rescale D eta).PsiEven := by
  intro R _ _ D h eta hD hadd hsq
  have h0 : eta 0 = 1 := by
    have e := hadd 0 0
    rw [add_zero] at e
    exact mul_eq_left.1 e.symm
  have key : ∀ χ : D.X, eta (-χ) * h χ = eta χ := fun χ => by
    rw [← hsq, pow_two, ← _root_.mul_assoc, ← hadd, neg_add_cancel, h0, _root_.one_mul]
  have hu : ∀ a b : (FractionRing R)ˣ, unitOn (a * b) = unitOn a * unitOn b := fun a b => map_mul _ a b
  refine fun (χ : D.X) => corr_of_val D.P.isLB fun y J hJ => ?_
  show val (LB.mulGen D.P.L _ _ _ _ (GlobalTheory.UU.scaleGen (unitOn (eta (-χ))) (D.psi (-χ)))
      (LB.pullGen D.P.L _ _ D.sym (D.xK χ))) (𝟙 _) y J = val (GlobalTheory.UU.scaleGen (unitOn (eta χ)) (D.psi χ)) (𝟙 _) y J
  refine (val_mul hJ _ _ _).trans ?_
  refine (congrArg₂ (· * ·) (GlobalTheory.UU.val_scaleGen _ _ _ hJ)
    ((val_pull hJ _ _ _).trans (congrArg (fun r => val D.sym r y J) (Category.id_comp _)))).trans ?_
  refine (_root_.mul_assoc _ _ _).trans ((congrArg (_ * ·) (hD χ y J hJ)).trans ?_)
  refine (_root_.mul_assoc _ _ _).symm.trans ((congrArg (· * _) ((map_mul _ _ _).symm.trans
    (congrArg (gm _ y ⊤) ((hu _ _).symm.trans (congrArg unitOn (key χ)))))).trans (GlobalTheory.UU.val_scaleGen _ _ _ hJ).symm)

end GlobalTheory.PolDeg
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RiemannianHaarFrameBallLowerBound
section
open NumberField IsDedekindDomain MeasureTheory Matrix GlobalTheory.AdLat GlobalTheory.UCls GlobalTheory.SUVol ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.CovTop.VolUp
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.StandardLattice Formalism.IndefR.Lev Formalism.IndefR.Datum GlobalTheory.AdelicScalar
open scoped ENNReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CovTop.VolUp.LowBall

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem exists_lam (Ψ : Finset (E →+* ℂ)) (G : Matrix (Fin r) (Fin r) E) (x : Frame Ψ r)
    (hx : ∀ τ, (mat x τ).det ≠ 0) :
    ∃ lam : Measure (realLie Ψ G), lam.IsAddHaarMeasure ∧ lam.map Subtype.val = riemLie Ψ G x := by
  set W := (realLie Ψ G).comap (fromFrame x)
  let Φ : W →ₗ[ℝ] realLie Ψ G :=
    ((fromFrame x).comp W.subtype).codRestrict (realLie Ψ G) (fun v => v.2)
  have key2 : ∀ τ (A : Matrix (Fin r) (Fin r) ℂ),
      mat x τ * ((mat x τ)⁻¹ * A * mat x τ) * (mat x τ)⁻¹ = A := fun τ A => by
    rw [Matrix.mul_assoc, Matrix.mul_nonsing_inv_cancel_right _ _ (hx τ).isUnit,
      Matrix.mul_nonsing_inv_cancel_left _ _ (hx τ).isUnit]
  have hsurj : Function.Surjective Φ := by
    intro X
    let Y : EuclideanSpace ℂ (Ψ × Fin r × Fin r) := WithLp.toLp 2 (fun p : Ψ × Fin r × Fin r =>
      ((mat x p.1)⁻¹ * Matrix.of (X.1 p.1) * mat x p.1) p.2.1 p.2.2)
    have hY : fromFrame x Y = X.1 := by
      funext τ
      have e : Matrix.of (fun a b => Y (τ, a, b)) = (mat x τ)⁻¹ * Matrix.of (X.1 τ) * mat x τ := by
        ext a b; simp [Y]
      change (mat x τ * Matrix.of _ * (mat x τ)⁻¹ : Matrix (Fin r) (Fin r) ℂ) = X.1 τ
      rw [e, key2]; rfl
    exact ⟨⟨Y, show fromFrame x Y ∈ realLie Ψ G by rw [hY]; exact X.2⟩, Subtype.ext hY⟩
  have key1 : ∀ τ (A : Matrix (Fin r) (Fin r) ℂ),
      (mat x τ)⁻¹ * (mat x τ * A * (mat x τ)⁻¹) * mat x τ = A := fun τ A => by
    rw [Matrix.mul_assoc, Matrix.nonsing_inv_mul_cancel_right _ _ (hx τ).isUnit,
      Matrix.nonsing_inv_mul_cancel_left _ _ (hx τ).isUnit]
  have hinj : Function.Injective Φ := by
    intro Y Z h
    have h' : fromFrame x Y.1 = fromFrame x Z.1 := congrArg Subtype.val h
    have hτ : ∀ τ, Matrix.of (fun a b => Y.1 (τ, a, b)) = Matrix.of (fun a b => Z.1 (τ, a, b)) := by
      intro τ
      have h1 : mat x τ * Matrix.of (fun a b => Y.1 (τ, a, b)) * (mat x τ)⁻¹ =
          mat x τ * Matrix.of (fun a b => Z.1 (τ, a, b)) * (mat x τ)⁻¹ := congrFun h' τ
      rw [← key1 τ (Matrix.of (fun a b => Y.1 (τ, a, b))), h1, key1]
    refine Subtype.ext (PiLp.ext fun p => ?_)
    obtain ⟨τ, a, b⟩ := p
    exact congrFun (congrFun (hτ τ) a) b
  let φ : W ≃L[ℝ] realLie Ψ G := (LinearEquiv.ofBijective Φ ⟨hinj, hsurj⟩).toContinuousLinearEquiv
  refine ⟨(stdOrthonormalBasis ℝ W).toBasis.addHaar.map φ, φ.isAddHaarMeasure_map _, ?_⟩
  rw [Measure.map_map measurable_subtype_coe φ.continuous.measurable]
  rfl

theorem exists_conj_bound (Ψ : Finset (E →+* ℂ)) (x : Frame Ψ r) (hx : ∀ τ, (mat x τ).det ≠ 0) :
    ∃ C : ℝ, 0 < C ∧ ∀ (t : ℝ) (X : Ψ → Fin r → Fin r → ℂ), 0 ≤ t →
      (∀ τ a b, ‖((mat x τ)⁻¹ * Matrix.of (X τ) * mat x τ) a b‖ ≤ t) → ‖X‖ ≤ C * t := by
  let L : (Ψ → Fin r → Fin r → ℂ) →ₗ[ℝ] (Ψ → Fin r → Fin r → ℂ) :=
    { toFun := fun Y τ => (mat x τ * Matrix.of (Y τ) * (mat x τ)⁻¹ : Matrix (Fin r) (Fin r) ℂ)
      map_add' := fun Y Z => by
        funext τ
        change mat x τ * (Matrix.of (Y τ) + Matrix.of (Z τ)) * (mat x τ)⁻¹ = _
        rw [Matrix.mul_add, Matrix.add_mul]; rfl
      map_smul' := fun c Y => by
        funext τ
        change mat x τ * ((c : ℂ) • Matrix.of (Y τ)) * (mat x τ)⁻¹ = _
        rw [Matrix.mul_smul, Matrix.smul_mul]; rfl }
  let Lc := LinearMap.toContinuousLinearMap L
  refine ⟨‖Lc‖ + 1, by positivity, fun t X ht hX => ?_⟩
  let Y : Ψ → Fin r → Fin r → ℂ := fun τ => ((mat x τ)⁻¹ * Matrix.of (X τ) * mat x τ : Matrix (Fin r) (Fin r) ℂ)
  have hLY : Lc Y = X := by
    funext τ
    change mat x τ * ((mat x τ)⁻¹ * Matrix.of (X τ) * mat x τ) * (mat x τ)⁻¹ = Matrix.of (X τ)
    rw [Matrix.mul_assoc, Matrix.mul_nonsing_inv_cancel_right _ _ (hx τ).isUnit,
      Matrix.mul_nonsing_inv_cancel_left _ _ (hx τ).isUnit]
  have hY : ‖Y‖ ≤ t := by
    refine (pi_norm_le_iff_of_nonneg ht).2 fun τ => (pi_norm_le_iff_of_nonneg ht).2 fun a =>
      (pi_norm_le_iff_of_nonneg ht).2 fun b => hX τ a b
  calc ‖X‖ = ‖Lc Y‖ := by rw [hLY]
    _ ≤ ‖Lc‖ * ‖Y‖ := Lc.le_opNorm Y
    _ ≤ ‖Lc‖ * t := by gcongr
    _ ≤ (‖Lc‖ + 1) * t := by nlinarith

section Exp

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem exists_exp_bound (n : Type) [Fintype n] [DecidableEq n] :
    ∃ δ : ℝ, 0 < δ ∧ ∀ Y : Matrix n n ℂ, ‖Y‖ < δ → ‖NormedSpace.exp Y - 1‖ ≤ 2 * ‖Y‖ := by
  have h := (hasFDerivAt_iff_isLittleO_nhds_zero.1
    (GlobalTheory.CompactDualExists.exp_strict (n := n)).hasFDerivAt).def (zero_lt_one' ℝ)
  obtain ⟨δ, hδ, hh⟩ := Metric.eventually_nhds_iff.1 h
  refine ⟨δ, hδ, fun Y hY => ?_⟩
  have := hh (y := Y) (by rwa [dist_zero_right])
  simp only [zero_add, NormedSpace.exp_zero, one_mul] at this
  have this : ‖NormedSpace.exp Y - 1 - Y‖ ≤ ‖Y‖ := this
  calc ‖NormedSpace.exp Y - 1‖ = ‖Y + (NormedSpace.exp Y - 1 - Y)‖ := by congr 1; abel
    _ ≤ ‖Y‖ + ‖NormedSpace.exp Y - 1 - Y‖ := norm_add_le _ _
    _ ≤ 2 * ‖Y‖ := by linarith

theorem exists_exp_entry (n : Type) [Fintype n] [DecidableEq n] :
    ∃ δ : ℝ, 0 < δ ∧ ∀ (ε : ℝ) (Y : Matrix n n ℂ), 0 < ε → ε < δ → (∀ a b, ‖Y a b‖ < ε / 2) →
      ∀ a b, ‖(NormedSpace.exp Y - 1) a b‖ < ε := by
  obtain ⟨δ, hδ, h⟩ := exists_exp_bound n
  refine ⟨δ, hδ, fun ε Y hε hεδ hY a b => ?_⟩
  have hYn : ‖Y‖ < ε / 2 := (Matrix.norm_lt_iff (by positivity)).2 hY
  calc ‖(NormedSpace.exp Y - 1) a b‖ ≤ ‖NormedSpace.exp Y - 1‖ := Matrix.norm_entry_le_entrywise_sup_norm _
    _ ≤ 2 * ‖Y‖ := h Y (by linarith)
    _ < ε := by linarith

end Exp

theorem riemHaar_frBall_ge : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (Ψ : Finset (E →+* ℂ))
    (G : Matrix (Fin r) (Fin r) E) (x : Frame Ψ r), 1 ≤ r → G.det ≠ 0 → (∀ τ, (mat x τ).det ≠ 0) →
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ →
      ENNReal.ofReal ((ε / (2 * ((Ψ.card : ℝ) * (r : ℝ) ^ 2))) ^ (Ψ.card * (r ^ 2 - 1)) / 2) ≤
        riemHaar Ψ G x (frBall Ψ G x ε) := by
  intro E _ _ _ r Ψ G x hr hG hx
  obtain ⟨lam, hlam, hmap⟩ := exists_lam Ψ G x hx
  obtain ⟨δ, hδ, hlow⟩ := GlobalTheory.T.lieHaar_le_two_mul_tangentNormalizedHaar E r Ψ G hG lam
  obtain ⟨C, hC, hconj⟩ := exists_conj_bound Ψ x hx
  obtain ⟨δ', hδ', hexp⟩ := exists_exp_entry (Fin r)
  refine ⟨min 2 (min δ' (δ / C)), lt_min two_pos (lt_min hδ' (div_pos hδ hC)), fun ε hε hε₀ => ?_⟩
  have hε2 : ε < 2 := lt_of_lt_of_le hε₀ (min_le_left _ _)
  have hεδ' : ε < δ' := lt_of_lt_of_le hε₀ ((min_le_right _ _).trans (min_le_left _ _))
  have hεC : ε < δ / C := lt_of_lt_of_le hε₀ ((min_le_right _ _).trans (min_le_right _ _))
  set S : Set (Ψ → Fin r → Fin r → ℂ) :=
    {X | ∀ τ a b, ‖((mat x τ)⁻¹ * Matrix.of (X τ) * mat x τ) a b‖ < ε / 2} with hS
  have hcont : ∀ τ a b, Continuous (fun X : Ψ → Fin r → Fin r → ℂ =>
      ((mat x τ)⁻¹ * Matrix.of (X τ) * mat x τ) a b) := by
    intro τ a b
    exact ((continuous_const.matrix_mul (continuous_apply τ)).matrix_mul continuous_const).matrix_elem a b
  have hSm : MeasurableSet S := by
    simp only [hS, Set.setOf_forall]
    exact MeasurableSet.iInter fun τ => MeasurableSet.iInter fun a => MeasurableSet.iInter fun b =>
      measurableSet_lt (hcont τ a b).norm.measurable measurable_const
  set s : Set (realLie Ψ G) := Subtype.val ⁻¹' S with hs
  have hsm : MeasurableSet s := measurable_subtype_coe hSm
  have h1 : ENNReal.ofReal ((ε / 2 / ((Ψ.card : ℝ) * (r : ℝ) ^ 2)) ^ (Ψ.card * (r ^ 2 - 1))) ≤ lam s := by
    have := GlobalTheory.T.riemannianLieMeasure_frameBox_ge E r Ψ G x hr hG hx (ε / 2) (by positivity) (by linarith)
    rw [← hmap, Measure.map_apply measurable_subtype_coe hSm] at this
    exact this
  have hball : s ⊆ Metric.ball 0 δ := by
    intro X hX
    rw [mem_ball_zero_iff]
    have h := hconj (ε / 2) X.1 (by positivity) fun τ a b => (hX τ a b).le
    have hCε : C * ε < δ := by rw [lt_div_iff₀ hC] at hεC; linarith
    calc ‖X‖ = ‖X.1‖ := rfl
      _ ≤ C * (ε / 2) := h
      _ < δ := by nlinarith
  have himg : GlobalTheory.SUVol.DensOne.chartExp Ψ G hG '' s ⊆ frBall Ψ G x ε := by
    rintro _ ⟨X, hX, rfl⟩ τ a b
    change ‖((mat x τ)⁻¹ * NormedSpace.exp (Matrix.of (X.1 τ)) * mat x τ - 1) a b‖ < ε
    rw [← Matrix.exp_conj' _ _ ((Matrix.isUnit_iff_isUnit_det _).2 (hx τ).isUnit)]
    exact hexp ε _ hε hεδ' (hX τ) a b
  have h2 := hlow s hsm hball
  have h3 : tangentHaar (realSU Ψ G) (lam.map Subtype.val) (GlobalTheory.SUVol.DensOne.chartExp Ψ G hG '' s) ≤
      riemHaar Ψ G x (frBall Ψ G x ε) := by
    rw [hmap]; exact measure_mono himg
  have e : ε / (2 * ((Ψ.card : ℝ) * (r : ℝ) ^ 2)) = ε / 2 / ((Ψ.card : ℝ) * (r : ℝ) ^ 2) := by rw [div_div]
  rw [e, ENNReal.ofReal_div_of_pos two_pos, ENNReal.ofReal_ofNat]
  refine ENNReal.div_le_of_le_mul ?_
  calc _ ≤ lam s := h1
    _ ≤ 2 * tangentHaar (realSU Ψ G) (lam.map Subtype.val) (GlobalTheory.SUVol.DensOne.chartExp Ψ G hG '' s) := h2
    _ ≤ 2 * riemHaar Ψ G x (frBall Ψ G x ε) := by gcongr
    _ = riemHaar Ψ G x (frBall Ψ G x ε) * 2 := mul_comm _ _

end GlobalTheory.CovTop.VolUp.LowBall
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RootOfMonomialQuotientIntegral
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.LogDR GlobalTheory.LogPair

namespace GlobalTheory.EtRoot

open MvPolynomial

theorem not_X_dvd_X {K : Type} [Field K] {n : ℕ} {i k : Fin n} (hik : i ≠ k) :
    ¬ (X i : MvPolynomial (Fin n) K) ∣ X k := by
  rintro ⟨q, hq⟩
  have := congrArg (MvPolynomial.eval (fun j => if j = i then (0 : K) else 1)) hq
  simp [hik.symm] at this

theorem prod_X_dvd_of_dvd_X_mul {K : Type} [Field K] {n : ℕ} (k : Fin n) :
    ∀ (S : Finset (Fin n)), k ∉ S → ∀ h : MvPolynomial (Fin n) K,
      (∏ j ∈ S, X j) ∣ X k * h → (∏ j ∈ S, X j) ∣ h := by
  intro S
  induction S using Finset.induction_on with
  | empty => intros; simp
  | insert i S hi ih =>
    intro hk h hd
    rw [Finset.prod_insert hi] at hd ⊢
    have hik : i ≠ k := fun e => hk (e ▸ Finset.mem_insert_self _ _)
    have hXi : (X i : MvPolynomial (Fin n) K) ∣ h := by
      rcases (X_prime (R := K) (i := i)).dvd_or_dvd (dvd_trans (dvd_mul_right _ _) hd) with h1 | h1
      · exact absurd h1 (not_X_dvd_X hik)
      · exact h1
    obtain ⟨h', rfl⟩ := hXi
    have hd' : X i * (∏ j ∈ S, X j) ∣ X i * (X k * h') := by
      rw [mul_left_comm (X i) (X k) h']; exact hd
    have h2 := (mul_dvd_mul_iff_left (X_ne_zero (R := K) i)).1 hd'
    exact mul_dvd_mul_left _ (ih (fun h => hk (Finset.mem_insert_of_mem h)) h' h2)

theorem prod_X_dvd_of_dvd_X_pow_mul {K : Type} [Field K] {n : ℕ} (k : Fin n)
    (S : Finset (Fin n)) (hk : k ∉ S) :
    ∀ (e : ℕ) (h : MvPolynomial (Fin n) K), (∏ j ∈ S, X j) ∣ X k ^ e * h → (∏ j ∈ S, X j) ∣ h := by
  intro e
  induction e with
  | zero => intro h hd; simpa using hd
  | succ e ih =>
    intro h hd
    apply ih
    apply prod_X_dvd_of_dvd_X_mul k S hk
    rwa [pow_succ, mul_comm _ (X k), mul_assoc] at hd

theorem prod_X_dvd_of_dvd_pow {K : Type} [Field K] {n : ℕ} :
    ∀ (S : Finset (Fin n)) (f : MvPolynomial (Fin n) K) (m : ℕ),
      (∏ j ∈ S, X j) ∣ f ^ m → (∏ j ∈ S, X j) ∣ f := by
  intro S
  induction S using Finset.induction_on with
  | empty => intros; simp
  | insert k S hk ih =>
    intro f m hd
    rw [Finset.prod_insert hk] at hd ⊢
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · rw [pow_zero] at hd
      exact dvd_trans hd (one_dvd _)
    have hXk : (X k : MvPolynomial (Fin n) K) ∣ f :=
      (X_prime (R := K) (i := k)).dvd_of_dvd_pow (dvd_trans (dvd_mul_right _ _) hd)
    obtain ⟨f', rfl⟩ := hXk
    have h1 : (∏ j ∈ S, X j) ∣ X k ^ m * f' ^ m := by
      rw [← mul_pow]; exact dvd_trans (dvd_mul_left _ _) hd
    exact mul_dvd_mul_left _ (ih f' m (prod_X_dvd_of_dvd_X_pow_mul k S hk m _ h1))

theorem isRadical_span_prod_X {K : Type} [Field K] {n : ℕ} (S : Finset (Fin n)) :
    (Ideal.span {∏ j ∈ S, (X j : MvPolynomial (Fin n) K)}).IsRadical := by
  intro y hy
  obtain ⟨e, he⟩ := (Ideal.mem_radical_iff).1 hy
  rw [Ideal.mem_span_singleton] at he ⊢
  exact prod_X_dvd_of_dvd_pow S y e he

end GlobalTheory.EtRoot

namespace GlobalTheory.EtRoot

open MvPolynomial

theorem dvd_of_dvd_pow_prod_coords (p : ℕ) [Fact p.Prime] (A : Type) [CommRing A]
    [Algebra (ZMod p) A] {n : ℕ} (t : Fin n → A)
    (he : (MvPolynomial.aeval (R := ZMod p) t).toRingHom.Etale) (S : Finset (Fin n))
    (z : A) (k : ℕ) (hz : (∏ j ∈ S, t j) ∣ z ^ k) : (∏ j ∈ S, t j) ∣ z := by
  letI : Algebra (MvPolynomial (Fin n) (ZMod p)) A := (MvPolynomial.aeval t).toRingHom.toAlgebra
  haveI : Algebra.Etale (MvPolynomial (Fin n) (ZMod p)) A := he
  have h1 := GlobalTheory.EtaleReducedEq.isRadical_map_of_etale (C := A)
    (Ideal.span {∏ j ∈ S, (X j : MvPolynomial (Fin n) (ZMod p))}) (isRadical_span_prod_X S)
  rw [Ideal.map_span, Set.image_singleton] at h1
  have h2 : algebraMap (MvPolynomial (Fin n) (ZMod p)) A (∏ j ∈ S, X j) = ∏ j ∈ S, t j := by
    rw [RingHom.algebraMap_toAlgebra, map_prod]
    simp
  rw [h2] at h1
  have hmem : z ∈ (Ideal.span {∏ j ∈ S, t j}).radical :=
    (Ideal.mem_radical_iff).2 ⟨k, Ideal.mem_span_singleton.2 hz⟩
  exact Ideal.mem_span_singleton.1 (h1 hmem)

theorem mem_local_of_pow_mem (p : ℕ) [Fact p.Prime] (A : Type) [CommRing A] [IsDomain A]
    [Algebra (ZMod p) A] {n : ℕ} (t : Fin n → A)
    (he : (MvPolynomial.aeval (R := ZMod p) t).toRingHom.Etale) (P : Ideal A) [P.IsPrime]
    (L : Type) [Field L] [Algebra A L] [IsFractionRing A L] (x : L) (m : ℕ) (hm : 0 < m)
    (hx : ∃ a b : A, b ∉ P ∧ x ^ m * algebraMap A L b = algebraMap A L a) :
    ∃ a b : A, b ∉ P ∧ x * algebraMap A L b = algebraMap A L a := by
  let Q := MvPolynomial (Fin n) (ZMod p)
  letI : Algebra Q A := (MvPolynomial.aeval t).toRingHom.toAlgebra
  haveI : Algebra.Etale Q A := he
  let T := Localization.AtPrime P
  haveI : Algebra.FormallyEtale Q T := inferInstance
  haveI : Algebra.EssFiniteType A T := Algebra.EssFiniteType.of_isLocalization T P.primeCompl
  haveI : Algebra.EssFiniteType Q T := Algebra.EssFiniteType.comp Q A T
  haveI : IsIntegrallyClosed Q := isIntegrallyClosed_mvPolynomial_fin (ZMod p) n
  obtain ⟨_, hT⟩ := GlobalTheory.EtNormal.isDomain_and_isIntegrallyClosed_of_formallyEtale Q T
  have hunit : ∀ y : P.primeCompl, IsUnit (algebraMap A L y) := fun y => by
    have hy : (y : A) ≠ 0 := fun h => y.2 (h ▸ P.zero_mem)
    exact isUnit_iff_ne_zero.2 ((map_ne_zero_iff _ (IsFractionRing.injective A L)).2 hy)
  letI : Algebra T L := (IsLocalization.lift (M := P.primeCompl) (S := T) hunit).toAlgebra
  haveI : IsScalarTower A T L := IsScalarTower.of_algebraMap_eq
    (fun y => (IsLocalization.lift_eq (M := P.primeCompl) (S := T) hunit y).symm)
  haveI : IsFractionRing T L :=
    IsFractionRing.isFractionRing_of_isDomain_of_isLocalization P.primeCompl T L
  have hmk : ∀ (a : A) (b : P.primeCompl),
      algebraMap T L (IsLocalization.mk' T a b) * algebraMap A L b = algebraMap A L a := by
    intro a b
    rw [IsScalarTower.algebraMap_apply A T L b, ← map_mul, IsLocalization.mk'_spec,
      ← IsScalarTower.algebraMap_apply]
  obtain ⟨a, b, hb, hab⟩ := hx
  have hbL : algebraMap A L b ≠ 0 := (hunit ⟨b, hb⟩).ne_zero
  have hxm : x ^ m = algebraMap T L (IsLocalization.mk' T a (⟨b, hb⟩ : P.primeCompl)) := by
    apply mul_right_cancel₀ hbL
    rw [hab]; exact (hmk a ⟨b, hb⟩).symm
  have hint : IsIntegral T x := by
    apply IsIntegral.of_pow hm
    rw [hxm]; exact isIntegral_algebraMap
  obtain ⟨u, hu⟩ := (IsIntegrallyClosed.isIntegral_iff (R := T) (K := L)).1 hint
  obtain ⟨⟨c, s⟩, rfl⟩ := IsLocalization.mk'_surjective P.primeCompl u
  refine ⟨c, s, s.2, ?_⟩
  rw [← hu]; exact hmk c s

theorem div_prod_coords_mem_of_pow : ∀ (p : ℕ) [Fact p.Prime] (A : Type) [CommRing A] [IsDomain A] [Algebra (ZMod p) A] {n : ℕ} (t : Fin n → A), (MvPolynomial.aeval (R := ZMod p) t).toRingHom.Etale → ∀ (P : Ideal A) [P.IsPrime] (L : Type) [Field L] [Algebra A L] [IsFractionRing A L] (S : Finset (Fin n)) (g : L) (m : ℕ), 0 < m → (∃ a b : A, b ∉ P ∧ g ^ m / algebraMap A L (∏ j ∈ S, t j) * algebraMap A L b = algebraMap A L a) → ∃ a b : A, b ∉ P ∧ g / algebraMap A L (∏ j ∈ S, t j) * algebraMap A L b = algebraMap A L a := by
  intro p _ A _ _ _ n t he P _ L _ _ _ S g m hm ⟨a, b, hb, hab⟩
  have h1P : (1 : A) ∉ P := (Ideal.ne_top_iff_one P).1 (Ideal.IsPrime.ne_top ‹_›)
  by_cases h0 : (∏ j ∈ S, t j) = 0
  · exact ⟨0, 1, h1P, by simp [h0]⟩
  have hπL : algebraMap A L (∏ j ∈ S, t j) ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective A L)).2 h0
  have h1 : ∃ a' b' : A, b' ∉ P ∧ g ^ m * algebraMap A L b' = algebraMap A L a' :=
    ⟨a * ∏ j ∈ S, t j, b, hb, by
      rw [map_mul, ← hab, div_mul_eq_mul_div, div_mul_cancel₀ _ hπL]⟩
  obtain ⟨x, s, hs, hxs⟩ := mem_local_of_pow_mem p A t he P L g m hm h1
  have hbs : s * b ∉ P := fun h => ((‹P.IsPrime›).mem_or_mem h).elim hs hb
  have h2 : x ^ m * b = a * (∏ j ∈ S, t j) * s ^ m := by
    apply IsFractionRing.injective A L
    simp only [map_mul, map_pow]
    rw [← hxs, ← hab]
    field_simp
    ring
  have h3 : (∏ j ∈ S, t j) ∣ (x * b) ^ m := by
    obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
    refine ⟨a * s ^ (k + 1) * b ^ k, ?_⟩
    calc (x * b) ^ (k + 1) = (x ^ (k + 1) * b) * b ^ k := by ring
      _ = _ := by rw [h2]; ring
  obtain ⟨y, hy⟩ := dvd_of_dvd_pow_prod_coords p A t he S (x * b) m h3
  refine ⟨y, s * b, hbs, ?_⟩
  have h4 : algebraMap A L (x * b) = algebraMap A L (∏ j ∈ S, t j) * algebraMap A L y := by
    rw [hy, map_mul]
  rw [map_mul, ← hxs] at h4
  rw [map_mul, div_mul_eq_mul_div, div_eq_iff hπL]
  linear_combination h4

end GlobalTheory.EtRoot
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SameRigidifiedFamilyAbelianSchemeOfLocalStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sameRigidifiedFamily_abelianScheme_of_local : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (A : Over (Sp R)) [GrpObj A], IsAbelianScheme A → ∀ (U T : Over (Sp R)) (M : LB (A ⊗ U).left) (N : LB (A ⊗ T).left) (hM : M.IsLB) (hN : N.IsLB), (∀ (Y : Over (Sp R)) (u : Y ⟶ U), evc hM (1 : Y ⟶ A) u = 0) → (∀ (Y : Over (Sp R)) (t : Y ⟶ T), evc hN (1 : Y ⟶ A) t = 0) → ∀ (Y : Over (Sp R)) (u : Y ⟶ U) (t : Y ⟶ T), (∀ y : Y.left, ∃ W : Y.left.Opens, y ∈ W ∧ Same A M N (Over.homMk W.ι rfl ≫ u : Over.mk (W.ι ≫ Y.hom) ⟶ U) (Over.homMk W.ι rfl ≫ t)) → Same A M N u t := by
  first | exact @GlobalTheory.DualCon.SameLocal.same_of_local | exact GlobalTheory.DualCon.SameLocal.same_of_local | (intros; apply GlobalTheory.DualCon.SameLocal.same_of_local <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SectionValueLinCombChangeOfChartsStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.MBModel GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MBLow.TanGauge
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sectionValue_linComb_change_of_charts : ∀ {X Y : Scheme.{0}} (L : LB X) {K : Type} [Fintype K] (φ : K → (Y ⟶ X)) (ε : K → ℤ)
    (s : LB.Sec (LB.LinComb L φ ε)) {A : Type} [CommRing A] (y : Sp A ⟶ Y) (j j' : K → L.ι),
    ⊤ ≤ y ⁻¹ᵁ LB.wchart L φ j → ⊤ ≤ y ⁻¹ᵁ LB.wchart L φ j' →
    valR y (LB.wchart L φ j) (s.f j) =
      (∏ k, trV L (y ≫ φ k) (j k) (j' k) (ε k)) * valR y (LB.wchart L φ j') (s.f j') := by
  first | exact @GlobalTheory.MBLow.TanGauge.valR_linComb_sec | exact GlobalTheory.MBLow.TanGauge.valR_linComb_sec | (intros; apply GlobalTheory.MBLow.TanGauge.valR_linComb_sec <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothExistsPointLiftSquareZeroLocalRingStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon GlobalTheory.DualOpen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.smooth_exists_point_lift_squareZero_localRing : ∀ (U S : Scheme.{0}) (p : U ⟶ S) [Smooth p] (C : Type) [CommRing C] [IsLocalRing C] (I : Ideal C), I ^ 2 = ⊥ → ∀ (s : Sp C ⟶ S) (u₀ : Sp (C ⧸ I) ⟶ U), u₀ ≫ p = spMap (Ideal.Quotient.mk I) ≫ s → ∃ u : Sp C ⟶ U, spMap (Ideal.Quotient.mk I) ≫ u = u₀ ∧ u ≫ p = s := by
  first | exact @GlobalTheory.SmoothPtLift.exists_lift | exact GlobalTheory.SmoothPtLift.exists_lift | (intros; apply GlobalTheory.SmoothPtLift.exists_lift <;> assumption)
end

