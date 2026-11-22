import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TripleLinearWittModelNonvanishing
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0044
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Development.AbelianVarietyTheory.Definitions.Divisors.RankEqCardIffExistsFrameMatrixFirstColumnBlock
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2083
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0068
import Development.AbelianVarietyTheory.BlockTheory.PoincareCuspForms.SmallUnipotentElements
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2075
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2084
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2085
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle0038
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0465
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1326
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RightTranslationLiftEqLevelMoveUnitConst
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1361
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2068
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2081

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TripleLinearWittModelNonvanishingStatement
section
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun MeasureTheory Topology
open scoped Matrix
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.triple_linear_witt_model_nonvanishing : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ v, X.Good v → ∀ (t : E →ₐ[F] Fv F v)
    (ι : ((Fin a × Fin (a + a') → Fv F v) → ℂ) →ₗ[ℂ] (Matrix (Fin a) (Fin (a + a')) (Fv F v) → ℂ)), G.M.IsLinW B.ψ t 1 1 ι →
    ∀ φ ∈ SB (Fin a × Fin (a + a') → Fv F v), ∀ φ₁ ∈ SB (Fin a × Fin (a + a') → Fv F v),
    (∀ μ : @Measure (Fin a × Fin (a + a') → Fv F v) (borel _), @Measure.IsAddHaarMeasure _ _ _ (borel _) μ →
      ∫⁻ x, ‖φ₁ x‖ₑ ^ 2 ∂μ = ∫⁻ x, ‖φ x‖ₑ ^ 2 ∂μ) →
    ∀ ν : @Measure (Matrix (Fin a) (Fin (a + a')) (Fv F v)) (borel _), @Measure.IsAddHaarMeasure _ _ _ (borel _) ν →
      ∫⁻ Y, ‖ι φ₁ Y‖ₑ ^ 2 ∂ν = ∫⁻ Y, ‖ι φ Y‖ₑ ^ 2 ∂ν := by
  first | exact @GlobalTheory.LinearModelL2.linIso_lintegral_eq | exact GlobalTheory.LinearModelL2.linIso_lintegral_eq | (intros; apply GlobalTheory.LinearModelL2.linIso_lintegral_eq <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TripleLocalGlEmbeddingIntegralStatement
section
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open scoped Matrix
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.triple_local_gl_embedding_integral : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ v, X.Good v → ∀ (t : E →ₐ[F] Fv F v)
    (K : GL (Fin a') (Fv F v) →* UA σ G.V'.J), (∀ g, K g ∈ UAt σ G.V' (evFin F v) ∧
      (mat (K g)).map (piW t) = g.val ∧
      (mat (K g)).map (piW (t.comp σ)) = (G.V'.J.map t)⁻¹ * ((g⁻¹ : GL _ _).val)ᵀ * G.V'.J.map t) →
    ∀ (S : GL (Fin a') (Fv F v) → (((Fin a' × Fin (a + a')) → Fv F v) → ℂ) → ((Fin a' × Fin (a + a')) → Fv F v) → ℂ),
    (∀ g, ∀ φ ∈ SB ((Fin a' × Fin (a + a')) → Fv F v), S g φ ∈ SB _ ∧ Acts (evFin F v) (om' (K g, 1)) φ (S g φ)) →
    ∀ (ν α : (Fv F v)ˣ →* ℂˣ) (ι : (((Fin a' × Fin (a + a')) → Fv F v) → ℂ) →ₗ[ℂ] (Matrix (Fin a') (Fin (a + a')) (Fv F v) → ℂ)),
    G.M'.IsLinBar B.ψ t 1 1 ι → (∀ g, ∀ φ ∈ SB ((Fin a' × Fin (a + a')) → Fv F v), ι (S g φ) = GlobalTheory.SplitFlip.omB ν α g 1 (ι φ)) →
    ∀ (d' : Darboux (symp (cA σ) (-1) (incM F G.W.J) (incM F G.V'.J)) (Fin a' × Fin (a + a'))),
    (∀ x : Matrix (Fin a') (Fin (a + a')) (AE F E), d'.e xᵀ = G.M'.co.e x) →
    ∀ (dd : Darboux (symp (cA σ) (-1) (incM F G.W.J) (dbl (incM F G.V'.J))) ((Fin a' × Fin (a + a')) ⊕ (Fin a' × Fin (a + a')))),
    IsDblCoord (cA σ) (-1) (incM F G.W.J) (incM F G.V'.J) d' dd →
    ∀ (omd : UG (cA σ) (dbl (incM F G.V'.J)) →* Module.End ℂ (((Fin a' × Fin (a + a')) ⊕ (Fin a' × Fin (a + a')) → AF F) → ℂ)),
    IsUSplitting (adeleClass F) B.ψ dd (actB (cA σ)) omd →
    (∀ (g : UA σ G.V'.J) (gd : UG (cA σ) (dbl (incM F G.V'.J))),
      ((gd : GL (Fin a' ⊕ Fin a') (AE F E)) : Matrix (Fin a' ⊕ Fin a') (Fin a' ⊕ Fin a') (AE F E)) =
        Matrix.fromBlocks (mat g) 0 0 1 →
      ∀ φ₁ ∈ schA F (Fin a' × Fin (a + a')), ∀ φ₂ ∈ schA F (Fin a' × Fin (a + a')), omd gd (boxFun φ₁ φ₂) = boxFun (om' (g, 1) φ₁) φ₂) →
    ∀ (g : GL (Fin a') (Fv F v)) (p : UG (cA σ) (dbl (incM F G.V'.J))),
      ((p : GL (Fin a' ⊕ Fin a') (AE F E)) : Matrix (Fin a' ⊕ Fin a') (Fin a' ⊕ Fin a') (AE F E)) =
        Matrix.fromBlocks (mat (K g)) 0 0 (mat (K g)) →
    ∀ φ₁ ∈ SB ((Fin a' × Fin (a + a')) → Fv F v), ∀ φ₂ ∈ SB ((Fin a' × Fin (a + a')) → Fv F v), ∀ φ'' ∈ SB ((Fin a' × Fin (a + a')) ⊕ (Fin a' × Fin (a + a')) → Fv F v),
      Acts (evFin F v) (omd p) (boxFun φ₁ φ₂) φ'' →
    ∀ μ : @MeasureTheory.Measure ((Fin a' × Fin (a + a')) → Fv F v) (borel _), @MeasureTheory.Measure.IsAddHaarMeasure _ _ _ (borel _) μ →
      ∫ x, φ'' (Sum.elim x x) ∂μ =
        ((ν (GlobalTheory.SplitFlip.gdet g) : ℂ) / starRingEnd ℂ (ν (GlobalTheory.SplitFlip.gdet g) : ℂ)) * ∫ x, φ₁ x * φ₂ x ∂μ := by
  first | exact @GlobalTheory.DblDiag.diag_integral | exact GlobalTheory.DblDiag.diag_integral | (intros; apply GlobalTheory.DblDiag.diag_integral <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedPullbackPolynomialRightActionOfCocycle
section
open NumberField Module ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.IndefiniteRowSideFullHecke.FrameWeightGapBounds GlobalTheory.ShareOn GlobalTheory.CuspEmb

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CuspEmb

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} {U C : Type} [Group U] [MulAction U C]

theorem pbA_comp (M : TwoLevels E r U C) (u v : U) (f : HA M) :
    pbA M v (pbA M u f) = pbA M (u * v) f := by
  apply Subtype.ext
  funext c x
  show f.1 (u • v • c) ⟨lact (M.tr u (v • c)) (lact (M.tr v c) x.1), _⟩ =
    f.1 ((u * v) • c) ⟨lact (M.tr (u * v) c) x.1, _⟩
  rw [show u • v • c = (u * v) • c from (mul_smul u v c).symm]
  have hγ := M.tr_mul u v c
  have hy : lact (M.tr u (v • c) * M.tr v c) x.1 ∈ M.dom := by
    rw [ReciprocityTheory.ChartRestriction.G.AR.Up.FundSetPf.lact_mul]
    exact lact_tr_mem M u _ (lact_tr_mem M v c x.2)
  have e : lact (M.tr (u * v) c * (M.tr u (v • c) * M.tr v c)⁻¹) (lact (M.tr u (v • c) * M.tr v c) x.1) =
      lact (M.tr (u * v) c) x.1 := by
    rw [← ReciprocityTheory.ChartRestriction.G.AR.Up.FundSetPf.lact_mul, inv_mul_cancel_right]
  have hz : lact (M.tr (u * v) c * (M.tr u (v • c) * M.tr v c)⁻¹)
      (⟨lact (M.tr u (v • c) * M.tr v c) x.1, hy⟩ : M.dom).1 ∈ M.dom := by
    show lact _ (lact _ x.1) ∈ M.dom
    rw [e]; exact lact_tr_mem M (u * v) c x.2
  have key := f.2.2 ((u * v) • c) _ hγ ⟨lact (M.tr u (v • c) * M.tr v c) x.1, hy⟩ hz
  rw [show (⟨lact (M.tr (u * v) c) x.1, lact_tr_mem M (u * v) c x.2⟩ : M.dom) =
      ⟨lact (M.tr (u * v) c * (M.tr u (v • c) * M.tr v c)⁻¹) (lact (M.tr u (v • c) * M.tr v c) x.1), hz⟩
      from Subtype.ext e.symm, key]
  exact congrArg (f.1 _) (Subtype.ext (ReciprocityTheory.ChartRestriction.G.AR.Up.FundSetPf.lact_mul _ _ _).symm)

theorem pbA_one (M : TwoLevels E r U C) (f : HA M) : pbA M 1 f = f := by
  apply Subtype.ext
  funext c x
  show f.1 ((1 : U) • c) ⟨lact (M.tr 1 c) x.1, _⟩ = f.1 c x
  have hγ := M.tr_mul 1 1 c
  simp only [mul_one, one_smul] at hγ
  rw [mul_inv_rev, mul_inv_cancel_left] at hγ
  have hz : lact (M.tr 1 c)⁻¹ (lact (M.tr 1 c) x.1) ∈ M.dom := by
    rw [← ReciprocityTheory.ChartRestriction.G.AR.Up.FundSetPf.lact_mul, inv_mul_cancel, ReciprocityTheory.ChartRestriction.G.AR.Up.FundSetPf.lact_one]
    exact x.2
  have key := f.2.2 c _ hγ ⟨lact (M.tr 1 c) x.1, lact_tr_mem M 1 c x.2⟩ hz
  simp only [one_smul]
  rw [← key]
  refine congrArg (f.1 c) (Subtype.ext ?_)
  show lact (M.tr 1 c)⁻¹ (lact (M.tr 1 c) x.1) = x.1
  rw [← ReciprocityTheory.ChartRestriction.G.AR.Up.FundSetPf.lact_mul, inv_mul_cancel, ReciprocityTheory.ChartRestriction.G.AR.Up.FundSetPf.lact_one]

theorem tw_law (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (U C : Type) [Group U] [MulAction U C]
    (M : TwoLevels E r U C) (a : U → C → ℂˣ) (ha : ∀ (g h : U) (c : C), a (h * g) c = a g c * a h (g • c)) :
    tw M (fun c => (a 1 c : ℂ)) 1 = AlgHom.id ℂ _ ∧
      ∀ u v : U, (tw M (fun c => (a v c : ℂ)) v).comp (tw M (fun c => (a u c : ℂ)) u) =
        tw M (fun c => (a (u * v) c : ℂ)) (u * v) := by
  refine ⟨?_, fun u v => ?_⟩
  · apply AlgHom.coe_ringHom_injective
    apply Polynomial.ringHom_ext
    · intro f
      show tw M _ 1 (Polynomial.C f) = Polynomial.C f
      rw [tw_C, pbA_one]
    · show tw M _ 1 Polynomial.X = Polynomial.X
      rw [tw_X]
      have h1 : cst M (fun c => (a 1 c : ℂ)) = 1 := by
        apply Subtype.ext
        funext c x
        show (a 1 c : ℂ) = 1
        have h := ha 1 1 c
        rw [one_mul, one_smul] at h
        have h' : a 1 c = 1 := by
          have := congrArg (fun t => (a 1 c)⁻¹ * t) h
          simpa using this.symm
        rw [h', Units.val_one]
      rw [h1, map_one, one_mul]
  · apply AlgHom.coe_ringHom_injective
    apply Polynomial.ringHom_ext
    · intro f
      show tw M _ v (tw M _ u (Polynomial.C f)) = tw M _ (u * v) (Polynomial.C f)
      rw [tw_C, tw_C, tw_C, pbA_comp]
    · show tw M _ v (tw M _ u Polynomial.X) = tw M _ (u * v) Polynomial.X
      rw [tw_X, map_mul, tw_C, tw_X, tw_X, ← mul_assoc, ← Polynomial.C_mul]
      congr 2
      apply Subtype.ext
      funext c x
      show (a u (v • c) : ℂ) * (a v c : ℂ) = (a (u * v) c : ℂ)
      rw [ha v u c, Units.val_mul, mul_comm]

end GlobalTheory.CuspEmb

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwoBinomialRatioBoundsStatement
section
open NumberField Module ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.IndefiniteRowSideFullHecke.FrameWeightGapBounds GlobalTheory.ShareOn
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.two_binomial_ratio_bounds : ∀ T n : ℕ, 2 ≤ n → 11 * n ^ 2 ≤ T → (T + 3 * n + 10).choose n ≤ 2 * (T + n).choose n ∧ (1 - (n : ℝ) * (n + 6) / T) * ((T + 2 * n + 6).choose n : ℕ) ≤ ((T + n).choose n : ℕ) := by
  first | exact @GlobalTheory.BinomRatio.two_binom_ratios | exact GlobalTheory.BinomRatio.two_binom_ratios | (intros; apply GlobalTheory.BinomRatio.two_binom_ratios <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwoLevelCuspFiniteOfComponentsStatement
section
open NumberField Module ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.IndefiniteRowSideFullHecke.FrameWeightGapBounds GlobalTheory.ShareOn
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twoLevelCusp_finite_of_components : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (U C : Type) [Group U] [Finite C] [MulAction U C] (M : TwoLevels E r U C) (ka : Wt M.Ψ r), (∀ c : C, FiniteDimensional ℂ (Submodule.span ℂ ((fun f : Frame (M.comp c).Ψ r → ℂ => fun x : (M.comp c).dom => f x) '' (M.comp c).SS (castWt (M.comp_Ψ c) ka)))) → Module.Finite ℂ (M.cusp ka) := by
  first | exact @GlobalTheory.cusp_finite_of_comp | exact GlobalTheory.cusp_finite_of_comp | (intros; apply GlobalTheory.cusp_finite_of_comp <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwoLevelCuspFormsDirectSumComponentsStatement
section
open NumberField Module ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.IndefiniteRowSideFullHecke.FrameWeightGapBounds GlobalTheory.ShareOn
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twoLevelCuspForms_directSum_components : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (U C : Type) [Group U] [Finite C] [DecidableEq C] [MulAction U C] (M : TwoLevels E r U C) (ka : Wt M.Ψ r) (ρ : Representation ℂ U (M.cusp ka)), IsPullRep M ka ρ → ∃ A : C → Submodule ℂ (M.cusp ka), DirectSum.IsInternal A ∧ ∀ (h : U) (c : C), ∀ v ∈ A c, ρ h v ∈ A (h • c) := by
  first | exact @GlobalTheory.ShareOn.cusp_decomp | exact GlobalTheory.ShareOn.cusp_decomp | (intros; apply GlobalTheory.ShareOn.cusp_decomp <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwoLevelCuspFormsMulMemAddWeight
section
open NumberField Module ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.IndefiniteRowSideFullHecke.FrameWeightGapBounds GlobalTheory.ShareOn GlobalTheory.CuspEmb

namespace GlobalTheory.CuspEmb

theorem twoLevels_mul_mem_SS : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (U C : Type) [Group U] [MulAction U C] (M : TwoLevels E r U C) (la mu : Wt M.Ψ r) (F G : C → Frame M.Ψ r → ℂ), F ∈ M.SS la → G ∈ M.SS mu → F * G ∈ M.SS (la + mu) := by
  intro E _ _ _ r U C _ _ M la mu F G hF hG c
  have hP := hF c
  have hQ := (hG c).1
  have h := ReciprocityTheory.ChartRestriction.G.AR.Up.ss_mul_pow (M.comp c).toData hP hQ 1
  have hw : castWt (M.comp_Ψ c) (la + mu) =
      castWt (M.comp_Ψ c) la + 1 • castWt (M.comp_Ψ c) mu := by
    rw [one_smul]; funext τ; rfl
  rw [hw]
  rw [pow_one] at h
  exact h

end GlobalTheory.CuspEmb
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwoLevelCuspFormsPullMem
section
set_option autoImplicit false

noncomputable section

open NumberField Module ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.IndefiniteRowSideFullHecke.FrameWeightGapBounds GlobalTheory.ShareOn GlobalTheory.CuspEmb

namespace GlobalTheory.CuspEmb

theorem pull_mem_SS : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (U C : Type) [Group U] [MulAction U C]
    (M : TwoLevels E r U C) (la : Wt M.Ψ r) (F : C → Frame M.Ψ r → ℂ) (h : U), F ∈ M.SS la → M.pull h F ∈ M.SS la := by
  intro E _ _ _ r U C _ _ M la F h hF c
  have hm : GlobalTheory.LevelCusp.IsMatch (M.comp c).toData (M.comp (h • c)).toData (M.tr h c) :=
    { psi := (M.comp_Ψ c).trans (M.comp_Ψ (h • c)).symm
      p0 := (M.comp_basePoint c).trans (M.comp_basePoint (h • c)).symm
      xi := (M.comp_ξ0 c).trans (M.comp_ξ0 (h • c)).symm
      iso := fun u v => by
        show herm (M.comp (h • c)).Gm _ _ = herm (M.comp c).Gm u v
        rw [M.comp_Gm, M.comp_Gm]
        exact M.tr_herm h c u v
      lat := fun v => M.tr_Λ h c v }
  exact GlobalTheory.LevelCusp.mem_SS_of_isMatch E r _ _ (M.tr h c) hm (castWt (M.comp_Ψ c) la)
    (castWt (M.comp_Ψ (h • c)) la) (fun τ i => rfl) _ (fun y => F (h • c) (castFrame (M.comp_Ψ (h • c)) y)) 1
    (GlobalTheory.PullBdd.pull_isBddSec E r U C M la F hF h c).1 (hF (h • c)) (fun x _ => by rw [one_mul]; rfl)

end GlobalTheory.CuspEmb

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwoLevelCuspFormsRestrictHolInvariant
section
open NumberField Module ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.IndefiniteRowSideFullHecke.FrameWeightGapBounds GlobalTheory.ShareOn GlobalTheory.CuspEmb

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CuspEmb

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem isSec_cast (X : Data E r) (Ψ : Finset (E →+* ℂ)) (Gm : Matrix (Fin r) (Fin r) E) (p0 : ℕ)
    (h1 : X.Ψ = Ψ) (h2 : X.Gm = Gm) (h3 : X.p0 = p0) (la : Wt Ψ r) (G : Frame Ψ r → ℂ)
    (hG : X.IsSec (castWt h1 la) (fun x => G (castFrame h1 x))) :
    DifferentiableOn ℂ G (GG Ψ Gm p0) ∧
      ∀ γ ∈ X.Γ, ∀ x ∈ GG Ψ Gm p0, G (lact γ x) = X.χ (castWt h1 la) γ * G x := by
  subst h1 h2 h3
  exact ⟨hG.1, hG.2.2⟩

theorem res_mem_HA (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (U C : Type) [Group U] [MulAction U C]
    (M : TwoLevels E r U C) (la : Wt M.Ψ r) (F : C → Frame M.Ψ r → ℂ) (hF : F ∈ M.SS la) : M.res F ∈ HA M := by
  have key := fun c => isSec_cast (M.comp c).toData M.Ψ M.Gm M.p0 (M.comp_Ψ c) (M.comp_Gm c) (M.comp_basePoint c) la (F c)
    (hF c).1.1
  refine ⟨fun c => ⟨F c, (key c).1, fun x => rfl⟩, fun c γ hγ x hx => ?_⟩
  show F c (lact γ x.1) = F c x.1
  rw [(key c).2 γ hγ x.1 x.2, M.χ_one c _ γ hγ, one_mul]

end GlobalTheory.CuspEmb

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformFamilyComponentIndex
section
open NumberField AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj GlobalTheory.GeoLevel GlobalTheory.LevelCusp GlobalTheory.FrameUnif
open GlobalTheory.Dict (castFr)
open GlobalTheory.FrameNorm (IsUnitFr)
open scoped Matrix

namespace GlobalTheory.GeoLevel

set_option maxHeartbeats 1000000 in

theorem moveMatch_of_markRel : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (r : ℕ) (U : Formalism.L2.PjFree.Unf Xo c σ r) (g : ℕ) (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ)) (F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (fun j => Formalism.L2.PjFree.relab c σ (e j).1)) (ik : U.Comp → Fin F.n) (φ : ∀ k, (F.Di (ik k)).La ≃ₗ[𝓞 E] (U.X k).Λ), Formalism.L2.PjFree.GoodEmb c σ → 1 ≤ Dw.p + Dw.q → l.A = 1 → Pinned U e F ik φ → ∀ (k k' : U.Comp) (δ : GL (Fin r) E) (h : IsMatch (U.X k) (U.X k') δ) (γ : Dw.La →ₗ[𝓞 E] Dw.La) (ρ : Xo.X ⟶ Xo.X) (ν : SABMap Xo.univ.t Xo.univ.t ρ), MarkRel l (φ k) (φ k') (F.t (ik k)) (F.t (ik k')) γ δ → IsLevMove ρ ν γ LinearMap.id → MoveMatch U U k k' h ρ ν := by
  intro E _ _ _ H Dw l Xo c σ r U g e F ik φ hσ hr hA hP k k' δ h γ ρ ν hM hν x y' hm
  obtain ⟨gam, hgam, t₁⟩ := hM
  have e₁ : ∀ a b, (F.Di (ik k')).EF (gam a) (gam b) = (F.Di (ik k)).EF a b := fun a b => by
    apply Int.cast_injective (α := ℚ)
    rw [hP.1, hP.1, hgam, hgam, h.iso, h.xi]
  obtain ⟨P, hPe, p, hy, hd⟩ := hP.2 k x
  obtain ⟨P', hPe', p', hy', hd'⟩ := hP.2 k' ⟨_, h.mem_dom x.2⟩
  obtain ⟨k₁, k₂⟩ := GlobalTheory.DictMove.exp_of_levMove F hr hσ ((GlobalTheory.Relab.relab_good _ H l c σ hσ).2.2.2 Dw g e) hA hν p p'
    gam e₁ t₁ fun v => funext fun j => by
      rw [hPe, hPe', hgam]
      exact GlobalTheory.GeoLevel.perFr_lact_of_isMatch E r _ _ δ h x.1 _ _ _
  refine ⟨by rw [hm.1, hy, hy']; exact k₁, funext fun τ => funext fun i => ?_⟩
  have d0 := GlobalTheory.FibreDeriv.isDerivAt0_comp (hd τ i) ν.φ
  simp only [← k₂] at d0
  rw [hm.2.1]
  exact ((GlobalTheory.isDerivAt0_ex_isTanAt E H Dw l Xo _ g _ F _ P' p').2.1 _).unique d0 (hd' τ i)

end GlobalTheory.GeoLevel
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisationRowCoreFormsOfGeometricAction
section
open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR GlobalTheory.HolDict
open scoped TensorProduct InnerProductSpace ContDiff
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.HolDict

theorem lUnif_topR_of_geoAct : GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Mem.Vol.FiniteVolume₂ → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec), R.toLevCh.Is A.μ0 → R.IsModels → TieIn T R κ v₀ → T.pb = R.C.P.pb → (∀ i, (κ i).LastPos) → 8 * D.R.f * D.R.r + 4 ≤ D.R.nV → GeoAct T R κ v₀ → (topR T R κ v₀).LUnif := by
  intro hC hV D G _ _ Pl0 T0 A T _ R κ v₀ hI hM hT hpb hκ hn hg
  exact lUnif_topN T R κ v₀ (nTop T κ) (hasB_nTop T hT.laws κ) hM.HW
    (GlobalTheory.T.cuspFormReadings_independent_spanning_all_embeddings hC hV D G Pl0 T0 A T R κ v₀ hI hM hT hpb hκ hn) hg

end GlobalTheory.HolDict
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnipotentModIdealOfTrivialModHalf
section
open NumberField IsDedekindDomain Module ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.IndefiniteRowSideFullHecke.FrameWeightGapBounds
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.CovTop Formalism.L2.Pj GlobalTheory.FormTies GlobalTheory.Shares GlobalTheory.ShareOn

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.UnipModHalf

theorem zpow_sub_one_eq_mul {R A : Type*} [CommRing R] [AddCommGroup A] [Module R A]
    (ℓ : A ≃ₗ[R] A) (n : ℤ) :
    ∃ X : Module.End R A, Commute ((ℓ : Module.End R A) - 1) X ∧
      ((ℓ ^ n : A ≃ₗ[R] A) : Module.End R A) - 1 = ((ℓ : Module.End R A) - 1) * X := by
  have h1 : (ℓ.symm : Module.End R A) * (ℓ : Module.End R A) = 1 := by
    ext y; simp
  have h2 : (ℓ : Module.End R A) * (ℓ.symm : Module.End R A) = 1 := by
    ext y; simp
  have hDℓ : Commute ((ℓ : Module.End R A) - 1) (ℓ : Module.End R A) :=
    (Commute.refl _).sub_left (Commute.one_left _)
  have hDs : Commute ((ℓ : Module.End R A) - 1) (ℓ.symm : Module.End R A) := by
    show _ = _
    rw [sub_mul, mul_sub, h2, h1, one_mul, mul_one]
  induction n using Int.induction_on with
  | zero => exact ⟨0, Commute.zero_right _, by ext y; simp⟩
  | succ k ih =>
    obtain ⟨X, hc, hX⟩ := ih
    refine ⟨(ℓ : Module.End R A) * X + 1, (hDℓ.mul_right hc).add_right (Commute.one_right _), ?_⟩
    have e : ((ℓ ^ ((k : ℤ) + 1) : A ≃ₗ[R] A) : Module.End R A)
        = (ℓ : Module.End R A) * ((ℓ ^ (k : ℤ) : A ≃ₗ[R] A) : Module.End R A) := by
      ext y; rw [add_comm, zpow_add, zpow_one]; rfl
    rw [e, eq_add_of_sub_eq hX]
    noncomm_ring
  | pred k ih =>
    obtain ⟨X, hc, hX⟩ := ih
    refine ⟨(ℓ.symm : Module.End R A) * X - (ℓ.symm : Module.End R A),
      (hDs.mul_right hc).sub_right hDs, ?_⟩
    have e : ((ℓ ^ (-(k : ℤ) - 1) : A ≃ₗ[R] A) : Module.End R A)
        = (ℓ.symm : Module.End R A) * ((ℓ ^ (-(k : ℤ)) : A ≃ₗ[R] A) : Module.End R A) := by
      ext y; rw [sub_eq_neg_add, zpow_add, zpow_neg_one]; rfl
    rw [e, eq_add_of_sub_eq hX]
    set s : Module.End R A := (ℓ.symm : Module.End R A)
    set l : Module.End R A := (ℓ : Module.End R A)
    have : s * ((l - 1) * X + 1) - 1 = (l - 1) * (s * X - s) + (s * l - 1) * X
        - (l * s - 1) * X + (l * s - 1) := by noncomm_ring
    rw [this, h1, h2]; simp

end GlobalTheory.UnipModHalf

namespace GlobalTheory.UnipModHalf

open Matrix

theorem unip_mod_half : ∀ {E : Type} [Field E] [NumberField E] {r : ℕ} (L' : Submodule (𝓞 E) (Fin r → E)) (Mb P : Ideal (𝓞 E)), Mb ≤ P →
    ∀ {A : Type} [AddCommGroup A] [Module (𝓞 E) A] (φ : A ≃ₗ[𝓞 E] (L' ⧸ (Mb • (⊤ : Submodule (𝓞 E) L'))))
      (ℓ : A ≃ₗ[𝓞 E] A) (n : ℤ),
    (∀ x : A, ((ℓ.toLinearMap - LinearMap.id : Module.End (𝓞 E) A) ^ r) x ∈ P • (⊤ : Submodule (𝓞 E) A)) →
    ∀ γ t : Matrix (Fin r) (Fin r) E, (∀ w ∈ L', Matrix.mulVec γ w ∈ L') → (∀ w ∈ L', Matrix.mulVec γ w - w ∈ Mb • L') →
    (∀ w : L', ∃ hw : Matrix.mulVec t w ∈ L',
      Submodule.Quotient.mk (p := Mb • (⊤ : Submodule (𝓞 E) L')) ⟨_, hw⟩ = φ ((ℓ ^ n) (φ.symm (Submodule.Quotient.mk w)))) →
    ∀ w ∈ L', Matrix.mulVec ((γ * t - 1) ^ r) w ∈ P • L' := by
  intro E _ _ r L' Mb P hMP A _ _ φ ℓ n hℓ γ t hγ hγ1 ht w hw

  let tL : (Fin r → E) →ₗ[𝓞 E] (Fin r → E) := (Matrix.mulVecLin t).restrictScalars (𝓞 E)
  let gL : (Fin r → E) →ₗ[𝓞 E] (Fin r → E) := (Matrix.mulVecLin γ).restrictScalars (𝓞 E)
  let T : Module.End (𝓞 E) L' := tL.restrict (fun x hx => (ht ⟨x, hx⟩).1)
  let G : Module.End (𝓞 E) L' := gL.restrict (fun x hx => hγ x hx)
  let U : Module.End (𝓞 E) L' := G * T - 1
  have hU : ∀ x : L', ((U x : L') : Fin r → E) = γ *ᵥ (t *ᵥ (x : Fin r → E)) - x := by
    intro x; rfl
  have hpow : ∀ k : ℕ, ∀ x : L', ((γ * t - 1) ^ k) *ᵥ (x : Fin r → E) = (((U ^ k) x : L') : Fin r → E) := by
    intro k
    induction k with
    | zero => intro x; simp
    | succ k ih =>
      intro x
      rw [pow_succ', ← Matrix.mulVec_mulVec, ih, pow_succ', Module.End.mul_apply, hU,
        Matrix.sub_mulVec, Matrix.one_mulVec, ← Matrix.mulVec_mulVec]

  have hsub : ∀ (I : Ideal (𝓞 E)) (z : L'), (z : Fin r → E) ∈ I • L' → z ∈ I • (⊤ : Submodule (𝓞 E) L') := by
    intro I z hz
    have e : I • L' = (I • (⊤ : Submodule (𝓞 E) L')).map L'.subtype := by
      rw [Submodule.map_smul'', Submodule.map_subtype_top]
    rw [e] at hz
    obtain ⟨u, hu, huz⟩ := hz
    have : u = z := Subtype.ext huz
    exact this ▸ hu
  set ℓn : Module.End (𝓞 E) A := ((ℓ ^ n : A ≃ₗ[𝓞 E] A) : Module.End (𝓞 E) A)
  have hπU : ∀ x : L', (Mb • (⊤ : Submodule (𝓞 E) L')).mkQ (U x) = φ ((ℓn - 1) (φ.symm ((Mb • (⊤ : Submodule (𝓞 E) L')).mkQ x))) := by
    intro x
    have hG : (Mb • (⊤ : Submodule (𝓞 E) L')).mkQ (G (T x)) = (Mb • (⊤ : Submodule (𝓞 E) L')).mkQ (T x) := by
      rw [Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq]
      exact hsub Mb _ (hγ1 _ (T x).2)
    have hT : (Mb • (⊤ : Submodule (𝓞 E) L')).mkQ (T x) = φ ((ℓ ^ n) (φ.symm ((Mb • (⊤ : Submodule (𝓞 E) L')).mkQ x))) := (ht x).2
    simp only [U, LinearMap.sub_apply, Module.End.mul_apply, Module.End.one_apply, map_sub, hG, hT]
    simp [ℓn]
  have hπUk : ∀ k : ℕ, ∀ x : L', (Mb • (⊤ : Submodule (𝓞 E) L')).mkQ ((U ^ k) x) = φ (((ℓn - 1) ^ k) (φ.symm ((Mb • (⊤ : Submodule (𝓞 E) L')).mkQ x))) := by
    intro k
    induction k with
    | zero => intro x; simp
    | succ k ih =>
      intro x
      rw [pow_succ', Module.End.mul_apply, hπU, ih, LinearEquiv.symm_apply_apply, pow_succ',
        Module.End.mul_apply]

  obtain ⟨X, hc, hX⟩ := zpow_sub_one_eq_mul ℓ n
  have hℓ' : ∀ y : A, ((ℓn - 1) ^ r) y ∈ P • (⊤ : Submodule (𝓞 E) A) := by
    intro y
    rw [show ℓn - 1 = ((ℓ : Module.End (𝓞 E) A) - 1) * X from hX, hc.mul_pow, Module.End.mul_apply]
    have := hℓ ((X ^ r) y)
    rwa [← Module.End.one_eq_id] at this

  have hQ : (Mb • (⊤ : Submodule (𝓞 E) L')).mkQ ((U ^ r) ⟨w, hw⟩) ∈ P • (⊤ : Submodule (𝓞 E) (L' ⧸ (Mb • (⊤ : Submodule (𝓞 E) L')))) := by
    rw [hπUk]
    have hm : ((P • (⊤ : Submodule (𝓞 E) A)).map (φ : A →ₗ[𝓞 E] (L' ⧸ (Mb • (⊤ : Submodule (𝓞 E) L'))))) ≤ P • ⊤ := by
      rw [Submodule.map_smul'']; exact Submodule.smul_mono le_rfl le_top
    exact hm (Submodule.mem_map_of_mem (hℓ' _))
  have hL : (U ^ r) ⟨w, hw⟩ ∈ P • (⊤ : Submodule (𝓞 E) L') := by
    have e : P • (⊤ : Submodule (𝓞 E) (L' ⧸ (Mb • (⊤ : Submodule (𝓞 E) L')))) = (P • (⊤ : Submodule (𝓞 E) L')).map (Mb • (⊤ : Submodule (𝓞 E) L')).mkQ := by
      rw [Submodule.map_smul'', Submodule.map_top, Submodule.range_mkQ]
    rw [e] at hQ
    have hQ' := Submodule.mem_comap.mpr hQ
    rw [Submodule.comap_map_mkQ] at hQ'
    have hle : Mb • (⊤ : Submodule (𝓞 E) L') ≤ P • (⊤ : Submodule (𝓞 E) L') := Submodule.smul_mono_left hMP
    exact (sup_le hle le_rfl) hQ'
  have key := hpow r ⟨w, hw⟩
  simp only at key
  rw [key]
  have e : P • L' = (P • (⊤ : Submodule (𝓞 E) L')).map L'.subtype := by
    rw [Submodule.map_smul'', Submodule.map_subtype_top]
  rw [e]
  exact Submodule.mem_map_of_mem hL

end GlobalTheory.UnipModHalf
end

