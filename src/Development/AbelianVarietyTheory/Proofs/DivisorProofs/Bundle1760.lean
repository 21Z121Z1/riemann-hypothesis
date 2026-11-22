import Mathlib
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.UnifMetricScalar
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0075
import Formalism.LocalToGlobal.ProjectiveLattices.RosatiLatticeNorms.LinkFD
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsRankOneNonproperPowerSeries
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0149
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0147
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1728
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousAtPlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1727
import Development.AbelianVarietyTheory.Definitions.Divisors.KernelNormConstantSpec
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1687
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1155
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0322
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0074
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0020
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0017
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsAdelicUnitaryTranslateStandardLattice
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TateUnramifiedOfTorsionUnramified
import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverMorphismRestrictOfRelAmple
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.TwistingSheafOneChartEqPreimageStandardChart
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsRegularFnIffOfIsAffineOpen
import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.BijectiveSmulChartSec
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMetricOfIsOrtho
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.LamCM Formalism.L2.Pj
open scoped ComplexOrder
open GlobalTheory GlobalTheory.CM GlobalTheory.Frames GlobalTheory.LamT GlobalTheory.OrthoMetric

namespace GlobalTheory.SupFull

theorem hm_eq_diagonal : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (r : ℕ) (U : Unf Xo c σ r), GoodEmb c σ → IsUnf U → ∀ (k : U.Comp) (x : (U.X k).dom) (W : PullbackSections.UnfAt U k x) (Wu : PullbackSections.UnitAt W), (U.X k).IsOrtho x.1 → Wu.Hm = Matrix.diagonal fun j => ((2 * ‖relab c σ (W.e j).1 (U.X k).ξ0‖ : ℝ) : ℂ) := by
  intro E _ _ _ H Dw l Xo c σ r U hσ hU k x W Wu hx
  obtain ⟨hbij, hrt, -, -⟩ := GlobalTheory.Relab.relab_good E H l c σ hσ
  obtain ⟨hp0, hty⟩ := hU.2.1 k
  obtain ⟨f, hf⟩ := GlobalTheory.FrameUnif.exists_letter_equiv (U.X k).Ψ (U.X k).cmType Dw.p Dw.q r hU.1 (relab c σ) hbij
    Dw.mult
    (fun τ h => by unfold Datum.mult; rw [if_pos ((hrt τ).1 ((hty _).1 h))])
    (fun τ h => by unfold Datum.mult; rw [if_neg (fun h' => h ((hty _).2 ((hrt τ).2 h')))])
  have hper : ∀ (v : Fin r → E) j, perFr (U.X k) x.1 v (relab c σ (W.e j).1) (W.e j).2 =
      if (((W.e.trans f) j).2 : ℕ) < (U.X k).p0 then
        FD.hermC ((W.e.trans f) j).1.1 (U.X k).Gm
          (FD.col (FD.mat x.1 ((W.e.trans f) j).1) ((W.e.trans f) j).2) (FD.Data.emb ((W.e.trans f) j).1.1 v)
      else ((FD.mat x.1 ((W.e.trans f) j).1)⁻¹.mulVec (FD.Data.emb ((W.e.trans f) j).1.1 v))
        ((W.e.trans f) j).2 := by
    intro v j
    have h := hf (W.e j)
    rw [Equiv.trans_apply]
    generalize f (W.e j) = t at h ⊢
    obtain ⟨⟨τ, hτ⟩, ⟨n, hn⟩⟩ := t
    generalize ((W.e j).2 : ℕ) = i at h ⊢
    dsimp only at h ⊢
    rw [← hp0] at h
    rcases h with ⟨a, rfl, rfl⟩ | ⟨a, rfl, rfl, d⟩
    · rw [if_neg (by omega)]
      unfold perFr
      rw [dif_pos a, dif_pos hn]
    · rw [if_pos (by omega)]
      unfold perFr
      rw [dif_neg a, dif_pos (show conjEmb (relab c σ (W.e j).1) ∈ (U.X k).Ψ from hτ), dif_pos hn]
      rfl
  have hcc : FD.cc (-(U.X k).ξ0) = -(-(U.X k).ξ0) := by
    have h := (U.X k).ξ0_im
    unfold FD.cc at h ⊢
    rw [map_neg, h]
  have key : Wu.Hm = Matrix.diagonal fun j => ((2 * (((W.e.trans f) j).1.1 (-(U.X k).ξ0)).im : ℝ) : ℂ) := by
    refine PullbackSections.UH.herm_eq_of_im W.Pm W.per.2.2.2.1 _ _ fun a b => ?_
    rw [Wu.c1, OrthoHerm.im_diag_eq_trace (U.X k).p0 _ (U.X k).Gm (U.X k).Ψ (U.X k).cmType (W.e.trans f) hcc x.1 hx
      (W.φ k a) (W.φ k b) _ _ (fun j => (W.pm_eq a j).trans (hper _ j)) (fun j => (W.pm_eq b j).trans (hper _ j)),
      ← W.isom, Rat.cast_intCast]
  have hd : ∀ j, (((W.e.trans f) j).1.1 (-(U.X k).ξ0)).im = ‖relab c σ (W.e j).1 (U.X k).ξ0‖ := by
    intro j
    have hn : ‖relab c σ (W.e j).1 (U.X k).ξ0‖ = ‖((W.e.trans f) j).1.1 (U.X k).ξ0‖ := by
      rcases hf (W.e j) with ⟨-, h, -⟩ | ⟨-, h, -⟩
      · rw [Equiv.trans_apply, h]
      · rw [Equiv.trans_apply, h]
        exact (Complex.norm_conj _).symm
    rw [hn]
    clear hn
    have hpos := Wu.pos (Pi.single j 1) (by simp)
    rw [key, hermForm, single_dotProduct, Matrix.mulVec_diagonal, Pi.star_apply, Pi.single_eq_same, star_one,
      _root_.one_mul, _root_.mul_one, Complex.ofReal_re] at hpos
    generalize ((W.e.trans f) j).1.1 = τ at hpos ⊢
    have hre : (τ (-(U.X k).ξ0)).re = 0 := by
      have h := congrArg τ hcc
      rw [FD.cc, IsCMField.complexEmbedding_complexConj, map_neg τ (-(U.X k).ξ0)] at h
      have := congrArg Complex.re h
      simp only [Complex.conj_re, Complex.neg_re] at this
      linarith
    have hp : 0 < (τ (-(U.X k).ξ0)).im := by linarith
    rw [← norm_neg, ← map_neg, ← Complex.abs_im_eq_norm.mpr hre, abs_of_pos hp]
  rw [key]
  simp only [hd]

theorem isMetric_of_isOrtho : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (r : ℕ) (U : Unf Xo c σ r), GoodEmb c σ → IsUnf U → 1 ≤ Dw.p + Dw.q → ∀ (k : U.Comp) (x : (U.X k).dom), (U.X k).IsOrtho x.1 → IsMetric (U.un k x) 1 (fun b => ((2 * Real.pi * ‖relab c σ b (U.X k).ξ0‖ : ℝ) : ℂ) • 1) := by
  intro E _ _ _ H Dw l Xo c σ r U hσ hU hpq k x hx
  obtain ⟨W⟩ := PullbackSections.nonempty_unfAt hU k x
  obtain ⟨Wu⟩ := PullbackSections.nonempty_unitAt W (PullbackSections.PfSupAtUnit.dmin_ortho _ hx)
  have hH := hm_eq_diagonal E H Dw l Xo c σ r U hσ hU k x W Wu hx
  obtain ⟨Φ₀⟩ := nonempty_fibKey E H Dw l Xo ℂ (U.un k x).x hpq
  obtain ⟨-, h₁, h₂⟩ := SecTieEx.secTie_exists_unique E H Dw l Xo ℂ (U.un k x).x Φ₀.T.t Φ₀.m
  obtain ⟨th, ht⟩ := h₁ (U.un k x).s
  have hne := (h₂ th _ ht).2.1 (secNZ_of_secGen lawsFieldsSeparately.2.1 E H Dw l Xo ℂ _ _ (U.un k x).gen)
  let Φ : FibKey Xo ℂ (U.un k x).x := { Φ₀ with th := th, th_ne := hne }
  obtain ⟨u, χ, hΛ, hA, hR, hF, hg, hD⟩ := exists_unif W.F (W.ik k) W.per W.pt Φ ht Wu.herm Wu.pos Wu.c2 Wu.c3 Wu.c4
    Wu.c5 Wu.c6 Wu.c7
  choose w hw using fun τ i => hD _ _ ((U.un k x).tan τ i) (W.der τ i)
  have hFd : IsAddFundamentalDomain u.Λ Wu.Fd volume := hΛ ▸ Wu.c8
  have hN := Wu.c9.symm
  have hG : ∀ (b : E →+* ℂ) (i j : Fin (Dw.mult b)),
      (((2 * Real.pi * ‖relab c σ b (U.X k).ξ0‖ : ℝ) : ℂ) • (1 : Matrix (Fin (Dw.mult b)) (Fin (Dw.mult b)) ℂ)) i j =
        Real.pi * hermForm Wu.Hm (Pi.single (W.e.symm ⟨b, j⟩) 1) (Pi.single (W.e.symm ⟨b, i⟩) 1) := by
    intro b i j
    rw [hH]
    simp [hermForm, Matrix.mulVec_diagonal, Pi.single_apply, Matrix.one_apply]
    split_ifs <;> simp_all <;> ring
  exact isMetricAt_of Φ hg u Wu.Hm χ Wu.θ Wu.Fd w (fun b i => Pi.single (W.e.symm ⟨b, i⟩) 1)
    ⟨ht, hA, hR, hF, hFd, hN, hw, hG⟩

theorem isBddSec_of_isUnf : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (r : ℕ) (U U' : Unf Xo c σ r), GoodEmb c σ → IsUnf U → IsUnf U' → 1 ≤ Dw.p + Dw.q → ∀ (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ), Dom a n → ∀ f ∈ sec Xo c a n, (∀ k, (U.X k).IsBddSec (laU U a n k) (rdU U f k)) → ∀ k, (U'.X k).IsBddSec (laU U' a n k) (rdU U' f k) := by
  intro E _ _ _ H Dw l Xo c σ r U U' hσ hU hU' hpq a n hd f hf hb k'
  have hB : Out.SecBaseChangeSt := GlobalTheory.lawsFieldsSeparately.2.1
  obtain ⟨-, -, -, -, -, -, hwt⟩ := GlobalTheory.Frames.algebraic_laws hB E H Dw l Xo c
  have hs' := hU'.2.2.2.2.1 a n hd f hf k'
  choose C hC using fun k => (hb k).2
  have hpos : ∀ (X : FD.Data E r) (b : E →+* ℂ), 0 < 2 * Real.pi * ‖relab c σ b X.ξ0‖ := fun X b =>
    mul_pos (by positivity) (norm_pos_iff.2 ((map_ne_zero _).2 X.ξ0_ne))
  let κ : U.Comp → (E →+* ℂ) → ℝ := fun k b =>
    2 * Real.pi * ‖relab c σ b (U.X k).ξ0‖ / (2 * Real.pi * ‖relab c σ b (U'.X k').ξ0‖)
  let B : U.Comp → ℝ := fun k =>
    (∏ p : Σ τ : E →+* ℂ, Fin (Dw.mult τ), (Real.sqrt (κ k p.1))⁻¹ ^ a (p.1, p.2)) * |C k|
  refine ⟨hs', ∑ k, B k, fun x₁ hx₁ => ?_⟩
  obtain ⟨b, hbB, ho⟩ := (FD.orthonormalFlagTranslate_holds r (U'.X k')).1 x₁ hx₁
  have hx' := FD.OrthogonalFrameDomain.rmul_mem_dom (U'.X k') hx₁ hbB
  rw [← (FD.orthonormalFlagTranslate_holds r (U'.X k')).2.1 _ _ hs'.2.1 x₁ hx₁ b hbB,
    PullbackSections.PfSupAtUnit.pnorm_unit _ _ _ (PullbackSections.PfSupAtUnit.dmin_ortho _ ho)]
  have hN := isMetric_of_isOrtho E H Dw l Xo c σ r U' hσ hU' hpq k' ⟨_, hx'⟩ ho
  have hrd' : ‖rdU U' f k' (FD.rmul x₁ b)‖ = cabs (evR Xo c f (U'.un k' ⟨_, hx'⟩)) := by
    have e : rdU U' f k' (FD.rmul x₁ b) = toC (evR Xo c f (U'.un k' ⟨_, hx'⟩)) := dif_pos hx'
    rw [e]; rfl
  rw [hrd']
  generalize U'.un k' ⟨_, hx'⟩ = y at hN ⊢
  obtain ⟨k, x, t, hx, ht⟩ := GlobalTheory.T.exists_orthonormalFrame_borelChange_complexFramedPoint E H Dw l Xo c σ r U hU y
  obtain ⟨g, hg0, hgd, hchg⟩ :=
    ((GlobalTheory.Frames.frBor_calculus E H Dw l Xo c (CAt σ) (U.un k x) y y).1 t).1 ht
  have hm0 := isMetric_of_isOrtho E H Dw l Xo c σ r U hσ hU hpq k x hx
  have hm1 := GlobalTheory.T.metric_change_of_frame E H Dw l Xo c σ (U.un k x) y 1 _
    (fun b => Matrix.transpose (show Matrix (Fin (Dw.mult b)) (Fin (Dw.mult b)) ℂ from g b))
    (show ℂ from (t none : CAt σ)) (Units.ne_zero (M₀ := ℂ) (t none)) hchg hm0
  obtain ⟨hNN, hG⟩ := GlobalTheory.T.metric_data_unique E H Dw l Xo c σ y _ _ _ _ hN hm1
  have hnone : cabs (t none : CAt σ) = 1 := by
    rw [_root_.mul_one] at hNN
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).1 hNN.symm
  have hsome : ∀ p : Σ τ : E →+* ℂ, Fin (Dw.mult τ), cabs (t (some p) : CAt σ) = (Real.sqrt (κ k p.1))⁻¹ := by
    rintro ⟨τ, i⟩
    rw [← hgd τ i]
    refine OrthoBound.norm_diag_of_triangular
      (Matrix.transpose (show Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) ℂ from g τ)) _
      (div_pos (hpos _ _) (hpos _ _)) (fun i j hij => hg0 τ j i hij) ?_ i
    have h1 := (congrFun hG τ).symm
    have h2 : ((2 * Real.pi * ‖relab c σ τ (U'.X k').ξ0‖ : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (hpos _ _).ne'
    dsimp only at h1
    rw [Complex.ofReal_div, div_eq_inv_mul, mul_smul, Matrix.mul_smul, Matrix.smul_mul, h1, smul_smul,
      inv_mul_cancel₀ h2, one_smul]
  have hev := hwt (CAt σ) (GlobalTheory.FrameNorm.Comparison₂.isReduced_cAt σ) a n f hf t _ _ ht
  have hw : cabs (wchar (ex Dw a n) t) =
      ∏ p : Σ τ : E →+* ℂ, Fin (Dw.mult τ), (Real.sqrt (κ k p.1))⁻¹ ^ a (p.1, p.2) := by
    rw [GlobalTheory.FrameNorm.Comparison₂.cabs_wchar, Fintype.prod_option, hnone, one_pow, _root_.one_mul]
    exact Finset.prod_congr rfl fun p _ => by rw [hsome p]; rfl
  have hrd : ‖rdU U f k x.1‖ = cabs (evR Xo c f (U.un k x)) := by
    have e : rdU U f k x.1 = toC (evR Xo c f (U.un k x)) := dif_pos x.2
    rw [e]; rfl
  have hle := hC k x.1 x.2
  rw [PullbackSections.PfSupAtUnit.pnorm_unit _ _ _ (PullbackSections.PfSupAtUnit.dmin_ortho _ hx), hrd] at hle
  have hB0 : ∀ k, 0 ≤ B k := fun k => mul_nonneg (Finset.prod_nonneg fun p _ => by positivity) (abs_nonneg _)
  rw [hev, GlobalTheory.FrameNorm.Comparison₂.cabs_mul, hw]
  exact (mul_le_mul_of_nonneg_left (hle.trans (le_abs_self _)) (Finset.prod_nonneg fun p _ => by positivity)).trans
    (Finset.single_le_sum (f := B) (fun k _ => hB0 k) (Finset.mem_univ k))

end GlobalTheory.SupFull
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSemiAbelianAndSpecialFibre
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.SplitMultiplicative

open IsLocalRing

section Curve

open ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.WeierstrassCurve GlobalTheory.MultiplicativeReduction

variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]

theorem isUnit_one_sub {a : V} (ha : a ∈ maximalIdeal V) : IsUnit (1 - 64 * a) :=
  isUnit_one_sub_self_of_mem_nonunits _ (Ideal.mul_mem_left (maximalIdeal V) 64 ha)

theorem isElliptic_generic {a : V} (ha : a ∈ maximalIdeal V) (ha0 : a ≠ 0) :
    ((⟨1, 0, 0, a, 0⟩ : WeierstrassCurve V).map (algebraMap _ (FractionRing V))).IsElliptic := by
  refine ⟨?_⟩
  rw [WeierstrassCurve.map_Δ, isUnit_iff_ne_zero, map_ne_zero_iff _ (IsFractionRing.injective _ _)]
  have : (⟨1, 0, 0, a, 0⟩ : WeierstrassCurve V).Δ = a ^ 2 * (1 - 64 * a) := by
    simp only [WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.b₈]
    ring
  rw [this]
  exact mul_ne_zero (pow_ne_zero _ ha0) (isUnit_one_sub ha).ne_zero

theorem isSemiAbelian_and_specialFibre {a : V} (ha : a ∈ maximalIdeal V) : ∀ (W : WeierstrassCurve V), W = ⟨1, 0, 0, a, 0⟩ → ∀ (U : (GlobalTheory.WeierstrassCurve.scheme W).Opens), (∀ (k : Type) [Field k] (ρ : V →+* k) (P : Fin 3 → k) (h : GlobalTheory.WeierstrassCurve.IsUnimodularSol (W.map ρ) P), ⊤ ≤ GlobalTheory.WeierstrassCurve.ptHom W ρ P h ⁻¹ᵁ U ↔ (W.map ρ).toProjective.Nonsingular P) → Smooth (U.ι ≫ GlobalTheory.WeierstrassCurve.toSpec W) → GeometricallyIntegral (U.ι ≫ GlobalTheory.WeierstrassCurve.toSpec W) → QuasiCompact (U.ι ≫ GlobalTheory.WeierstrassCurve.toSpec W) → ∀ [GrpObj (Over.mk (U.ι ≫ GlobalTheory.WeierstrassCurve.toSpec W))] [IsCommMonObj (Over.mk (U.ι ≫ GlobalTheory.WeierstrassCurve.toSpec W))], (∀ (k : Type) [Field k] (ρ : V →+* k) (x y : Over.mk (Spec.map (CommRingCat.ofHom ρ)) ⟶ (Over.mk (U.ι ≫ GlobalTheory.WeierstrassCurve.toSpec W))) (P Q : Fin 3 → k) (hP : GlobalTheory.WeierstrassCurve.IsUnimodularSol (W.map ρ) P) (hQ : GlobalTheory.WeierstrassCurve.IsUnimodularSol (W.map ρ) Q), x.left ≫ U.ι = GlobalTheory.WeierstrassCurve.ptHom W ρ P hP → y.left ≫ U.ι = GlobalTheory.WeierstrassCurve.ptHom W ρ Q hQ → ∃ h : GlobalTheory.WeierstrassCurve.IsUnimodularSol (W.map ρ) ((W.map ρ).toProjective.add P Q), (lift x y ≫ μ[(Over.mk (U.ι ≫ GlobalTheory.WeierstrassCurve.toSpec W))]).left ≫ U.ι = GlobalTheory.WeierstrassCurve.ptHom W ρ _ h) → IsSemiAbelian (Over.mk (U.ι ≫ GlobalTheory.WeierstrassCurve.toSpec W)) ∧ ∃ i : splitTorus (Spec (CommRingCat.of (IsLocalRing.ResidueField V))) ℤ ≅ (Over.pullback (Spec.map (CommRingCat.ofHom (IsLocalRing.residue V)))).obj (Over.mk (U.ι ≫ GlobalTheory.WeierstrassCurve.toSpec W)), IsMonHom i.hom := by
  intro W hW U hU hsm hgi hqc _ _ hmul
  have hgc : GeometricallyConnected (U.ι ≫ toSpec W) := by
    refine ⟨fun K _ y Z fst snd h ↦ ?_⟩
    have : IsIntegral Z := GeometricallyIntegral.geometrically_isIntegral y fst snd h
    exact inferInstanceAs (ConnectedSpace Z)
  have htor : ∀ (K : Type) [Field K] (f : V →+* K), f a = 0 →
      ∃ i : splitTorus (Spec (CommRingCat.of K)) ℤ ≅
        (Over.pullback (Spec.map (CommRingCat.ofHom f))).obj (Over.mk (U.ι ≫ toSpec W)),
        IsMonHom i.hom := by
    intro K _ f hf
    obtain ⟨U', _, e, he, -, hU', hmul'⟩ :=
      GlobalTheory.SmoothLocusBaseChange.main _ K f W U hU hsm hgi hmul
    have hl : U'.ι ≫ toSpec (W.map f) =
        e.hom.left ≫ pullback.snd (U.ι ≫ toSpec W) (Spec.map (CommRingCat.ofHom f)) :=
      (Over.w e.hom).symm
    have : IsIso e.hom.left := inferInstanceAs (IsIso ((Over.forget _).map e.hom))
    obtain ⟨i, hi⟩ := GlobalTheory.NodalCubic.exists_splitTorus_iso K (W.map f)
      (by subst hW; ext <;> simp [hf]) U' hU' (by rw [hl]; infer_instance)
      (by
        rw [hl]
        exact MorphismProperty.of_isPullback (P := @GeometricallyIntegral)
          (IsPullback.of_horiz_isIso (fst := e.hom.left) (g := 𝟙 _) ⟨(Category.comp_id _).symm⟩)
          (inferInstanceAs (GeometricallyIntegral
            (pullback.snd (U.ι ≫ toSpec W) (Spec.map (CommRingCat.ofHom f)))))) hmul'
    exact ⟨i ≪≫ e, by rw [Iso.trans_hom]; infer_instance⟩
  refine ⟨⟨inferInstance, hsm, inferInstanceAs (IsSeparated (U.ι ≫ toSpec W)), hqc,
    hgc, fun Ω _ _ p => ?_⟩,
    htor _ _ ?_⟩
  · obtain ⟨g, rfl⟩ := Spec.map_surjective p
    obtain ⟨f, rfl⟩ : ∃ f : V →+* Ω, g = CommRingCat.ofHom f := ⟨g.hom, rfl⟩
    by_cases hf : f a = 0
    · obtain ⟨i, hi⟩ := htor Ω f hf
      obtain ⟨T⟩ := nonempty_torusExtension_splitTorus Ω
      exact ⟨Geo.Tor.torusExtOfIso i T⟩
    · have hΔ : W.Δ = a ^ 2 * (1 - 64 * a) := by
        subst hW
        simp only [WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
          WeierstrassCurve.b₆, WeierstrassCurve.b₈]
        ring
      have hu : IsUnit (1 - 64 * a : V) := isUnit_one_sub ha
      have hΔ' : f W.Δ ≠ 0 := by
        rw [hΔ, map_mul, map_pow]
        exact mul_ne_zero (pow_ne_zero _ hf) (hu.map f).ne_zero
      refine ⟨GlobalTheory.torusExtensionOfAbelian _ ⟨inferInstance, ?_, ?_, ?_⟩⟩
      · exact inferInstanceAs (Smooth (pullback.snd (U.ι ≫ toSpec W) _))
      · exact isProper_pullback_snd W U hU f hΔ'
      · exact inferInstanceAs (GeometricallyConnected (pullback.snd (U.ι ≫ toSpec W) _))
  · exact (IsLocalRing.residue_eq_zero_iff a).2 ha

theorem exists_semiAbelian_polarised {a : V} (ha : a ∈ maximalIdeal V) (ha0 : a ≠ 0) : ∃ (G : Over (Spec (CommRingCat.of V))) (_ : GrpObj G) (_ : IsCommMonObj G) (A : PolAV (Spec (CommRingCat.of (FractionRing V)))) (eA : (Over.pullback (jK V)).obj G ≅ A.A) (i : splitTorus (Spec (CommRingCat.of (IsLocalRing.ResidueField V))) ℤ ≅ (Over.pullback (Spec.map (CommRingCat.ofHom (IsLocalRing.residue V)))).obj G), IsSemiAbelian G ∧ IsMonHom eA.hom ∧ IsMonHom i.hom ∧ A.g = 1 ∧ ∃ (LG : RigLB G) (_c : CubicalStr G LG) (s : LB.Gen (LB.LinComb LG.L (K := Fin 2) ![(ι[G]).left, 𝟙 G.left] ![1, -1])), s.IsGen ∧ LB.Gen.Corr LG.L _ _ _ _ (LB.pullGen LG.L _ _ s (eSec G)) (LB.oneGen LG.L) ∧ (∃ w : LB.Iso (A.L.pull eA.hom.left) (LG.L.pull (pullback.fst G.hom (jK V))), w.IsGen) ∧ ∃ θ : H0 LG.L 1, ∀ x : G.left, G.hom x = IsLocalRing.closedPoint V → x ∈ nonzeroLocus θ := by
  have hL := GlobalTheory.allSixLaws.1
  obtain ⟨W, hW⟩ : ∃ W : WeierstrassCurve V, W = ⟨1, 0, 0, a, 0⟩ := ⟨_, rfl⟩
  obtain ⟨U, hU, hsm, hqc, hgi⟩ := exists_smoothLocus _ W
  have hs : Smooth (U.ι ≫ toSpec W) := SmoothOfRelativeDimension.smooth 1 _
  obtain ⟨_, _, hη, hmul⟩ := GlobalTheory.exists_grpObj_smoothLocus _ W U hU hs hgi
  obtain ⟨hG, i, hi⟩ := isSemiAbelian_and_specialFibre ha W hW U hU hs hgi hqc hmul
  let f := algebraMap V (FractionRing V)
  have : (W.map f).IsElliptic := hW ▸ isElliptic_generic ha ha0
  obtain ⟨φ, hφ⟩ := exists_iso_schemeOver f W U hU
  let G := Over.mk (U.ι ≫ toSpec W)
  let j := pullback.fst G.hom (jK V)
  have hη' : (η[(Over.pullback (jK V)).obj G]).left ≫ j ≫ U.ι = jK _ ≫ zero W := by
    rw [← hη, ← Category.assoc, ← Category.assoc]
    exact congrArg (· ≫ U.ι) (one_pullback_fst _ G)
  have hP : IsUnimodularSol (W.map f) ![0, 0, 1] := hW ▸ isUnimodularSol_twoPt _ _
  have hX : f a ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective _ _)).2 ha0
  have hPU := (hU _ f _ hP).2 (hW ▸ (nonsingular_twoPt _ f).2 hX)
  have hr : Set.range (ptHom W f _ hP) ⊆ Set.range U.ι := by
    rintro _ ⟨y, rfl⟩
    rw [Scheme.Opens.range_ι]
    exact hPU (Set.mem_univ y)
  have hb := IsOpenImmersion.lift_fac U.ι (ptHom W f _ hP) hr
  have hb' : IsOpenImmersion.lift U.ι (ptHom W f _ hP) hr ≫ U.ι ≫ toSpec W = jK _ := by
    rw [← Category.assoc, hb, ptHom_toSpec]
  let b : Over.mk (jK V) ⟶ G := Over.homMk _ hb'
  let x : 𝟙_ _ ⟶ (Over.pullback (jK V)).obj G :=
    Over.homMk (pullback.lift b.left (𝟙 _) (hb'.trans (Category.id_comp _).symm)) (pullback.lift_snd _ _ _)
  have hxa : x.left ≫ j = b.left := pullback.lift_fst _ _ _
  have hx : x * x = 1 := by
    have h₁ : (1 : 𝟙_ _ ⟶ (Over.pullback (jK V)).obj G) = η[_] := by rw [Hom.one_def]; simp
    rw [h₁]
    refine Over.OverMorphism.ext (pullback.hom_ext ?_ ((Over.w _).trans (Over.w _).symm))
    have h₂ := SmoothLocusBaseChange.lift_mul_pullback_fst (jK V) G x x (𝟙 _) b b
      (hxa.symm.trans (Category.id_comp _).symm) (hxa.symm.trans (Category.id_comp _).symm)
    obtain ⟨h, h₃⟩ := hmul _ f b b _ _ hP hP hb hb
    refine (cancel_mono U.ι).1 ?_
    refine Eq.trans ?_ (hη'.symm.trans (Category.assoc _ _ _).symm)
    refine (congrArg (· ≫ U.ι) (h₂.trans (Category.id_comp _))).symm.trans (h₃.trans ?_)
    rw [SpecMap_zero, ptHom_eq_ptHom_iff_minors]
    obtain ⟨h₄, h₅⟩ := add_twoPt a f
    rw [← hW] at h₄ h₅
    intro m l
    fin_cases m <;> fin_cases l <;> simp [h₄, h₅]
  have hz : (η[(Over.pullback (jK V)).obj G]).left ≫ φ.hom.left = zero (W.map f) := by
    apply (isPullback_mapHom W f rfl).hom_ext
    · exact (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) hφ).trans (hη'.trans (zero_mapHom W f rfl).symm))
    · exact (Over.w (η[(Over.pullback (jK V)).obj G] ≫ φ.hom)).trans (zero_toSpec _).symm
  obtain ⟨A, eA, θ, heA, hg, hθ⟩ := exists_pol_twoTorsion hL (W.map f) _ φ hz x hx
  obtain ⟨LG, c, s, hs₁, hs₂, w, hw⟩ := PolExtension.exists_cubical_symmetric_extension hL _ G hG A eA heA
  refine ⟨G, inferInstance, inferInstance, A, eA, i, hG, heA, hi, hg, LG, c, s, hs₁, hs₂, ⟨w, hw⟩, ?_⟩
  obtain ⟨t, ht⟩ := exists_sec_of_iso A.isLB (pull_isLB LG.isLB j) eA.hom.left ⟨w, hw⟩ θ
  have ht' : ∀ z, z ∈ nonzeroLocus t ↔ z ∉ Set.range x.left := fun z => (ht z).trans (hθ z)
  refine exists_sec_generates_specialFibre _ G hG LG.L LG.isLB t
    ⟨(η[(Over.pullback (jK V)).obj G]).left (IsLocalRing.closedPoint _), (ht' _).2 ?_⟩ ?_
  · rintro ⟨p, hp⟩
    have h₁ : ptHom W f _ hP p ∈ coordOpen W 2 := (ptHom_preimage_coordOpen W f _ hP 2).ge
      (PrimeSpectrum.basicOpen_one.ge (Set.mem_univ p))
    have h₂ : ptHom W f _ hP p = zero W (jK _ (IsLocalRing.closedPoint _)) :=
      (congrArg (fun q => q p) ((congrArg (· ≫ U.ι) hxa).trans hb)).symm.trans
        ((congrArg (j ≫ U.ι) hp).trans (congrArg (fun q => q (IsLocalRing.closedPoint _)) hη'))
    rw [h₂] at h₁
    exact (zero_preimage_coordOpen_two W).le h₁
  · have e : j '' {z | z ∉ nonzeroLocus t} = Set.range b.left := by
      rw [← hxa]
      ext y
      constructor
      · rintro ⟨z, hz, rfl⟩
        obtain ⟨p, rfl⟩ := not_not.1 (mt (ht' z).2 hz)
        exact ⟨p, rfl⟩
      · rintro ⟨p, rfl⟩
        exact ⟨x.left p, fun h => (ht' _).1 h ⟨p, rfl⟩, rfl⟩
    exact e ▸ isClosed_twoPt ha W hW U hU b.left hP hb

end Curve

open GlobalTheory.UU GlobalTheory.MultiplicativeTorusSetting GlobalTheory.TateUnif

theorem not_isProper_torus_of_infinite (k : Type) [Field k] [Infinite k] :
    ¬ IsProper (splitTorus (Spec (CommRingCat.of k)) ℤ).hom := fun h => by
  let e : k ≃+* Γ(Spec (CommRingCat.of k), ⊤) := (Scheme.ΓSpecIso (CommRingCat.of k)).symm.commRingCatIsoToRingEquiv
  obtain ⟨p, hp, h0⟩ := isIntegral_appTop_of_universallyClosed (splitTorus (Spec (CommRingCat.of k)) ℤ).hom
    (charUnit (Spec (CommRingCat.of k)) ℤ 1).val
  have root : ∀ a : kˣ, (p.map e.symm.toRingHom).IsRoot a.val := fun a => by
    let t : 𝟙_ (Over (Spec (CommRingCat.of k))) ⟶ splitTorus (Spec (CommRingCat.of k)) ℤ :=
      (splitTorusPointsEquiv _ ℤ _).symm (zpowersHom _ (Units.map e.toMonoidHom a))
    have h₁ : t.left.appTop.hom (charUnit (Spec (CommRingCat.of k)) ℤ 1).val = e a.val := by
      rw [← chV_val, chV, MulEquiv.apply_symm_apply]
      exact congrArg Units.val (zpow_one (Units.map e.toMonoidHom a))
    have h₂ : t.left.appTop.hom.comp (splitTorus (Spec (CommRingCat.of k)) ℤ).hom.appTop.hom = RingHom.id _ := by
      rw [← CommRingCat.hom_comp, ← Scheme.Hom.comp_appTop, Over.w]
      exact congrArg CommRingCat.Hom.hom Scheme.Hom.id_appTop
    have h₃ := congrArg t.left.appTop.hom h0
    rw [Polynomial.hom_eval₂, h₂, h₁, map_zero] at h₃
    have h₄ := congrArg e.symm.toRingHom h₃
    rw [Polynomial.hom_eval₂, map_zero] at h₄
    rw [Polynomial.IsRoot, Polynomial.eval_map]
    simpa using h₄
  have inf : Set.Infinite {x | (p.map e.symm.toRingHom).IsRoot x} :=
    (Set.finite_singleton (0 : k)).infinite_compl.mono fun x hx => root (Units.mk0 x hx)
  exact (hp.map _).ne_zero (Polynomial.eq_zero_of_infinite_isRoot _ inf)

theorem not_isProper_torus (k : Type) [Field k] :
    ¬ IsProper (splitTorus (Spec (CommRingCat.of k)) ℤ).hom := fun h =>
  not_isProper_torus_of_infinite (AlgebraicClosure k) (MorphismProperty.of_isPullback (P := @IsProper)
    (SplitTorus.isGrpPullback_bcMap (spMap (algebraMap k (AlgebraicClosure k))) ℤ).1 h)

variable {V : Type} [CommRing V] [IsDomain V] [IsLocalRing V]

theorem exists_setting (hV : CDVR V) : ∃ (A : PolAV (Spec (CommRingCat.of (FractionRing V)))) (G : Over (Spec (CommRingCat.of V))) (_ : GrpObj G) (_ : IsCommMonObj G) (s : HidaSetting V A G), A.g = 1 ∧ Module.finrank ℤ s.X = 1 ∧ ¬ IsProper (thickObj V (IsLocalRing.maximalIdeal V) 0 G).hom := by
  obtain ⟨laws, laws₂, -⟩ := GlobalTheory.allSixLaws
  have := hV.1
  obtain ⟨a, ha'⟩ := IsDiscreteValuationRing.exists_irreducible V
  obtain ⟨G, _, _, A, eA, i, hG, hA, hi, hg, L, -, -, -, -, hw, θ, hθ⟩ :=
    exists_semiAbelian_polarised (a := a) ha'.not_isUnit ha'.ne_zero
  obtain ⟨P, rfl⟩ := CubicalPackage.exists_package laws _ hV A G hG eA hA L hw
  have := hG.smooth
  have : IsMonHom eA.symm.hom := inferInstanceAs (IsMonHom eA.inv)
  have gp : IsGrpPullback A.A G (jK _) (eA.inv.left ≫ pullback.fst G.hom (jK _)) :=
    ((isGrpPullback_of_iso eA.symm).comp (isGrpPullback_pullback G (jK _))).congr (Category.id_comp _) rfl
  have hinv : eA.inv.left ≫ eA.hom.left = 𝟙 _ := by rw [← Over.comp_left, eA.inv_hom_id, Over.id_left]
  obtain ⟨s, hs⟩ := exists_even_sec laws₂.secTwist A gp P
    (LBIso.chartPull (chartPullSec A.L _ eA.inv.left hinv) (chartPullSame P.L.L _ _ _ eA.inv.left fun _ => rfl) hw) θ
    (hθ _ (congrArg (fun q => q (IsLocalRing.closedPoint V)) (Over.w η[G])))
  obtain ⟨r, hr⟩ := thick_zero_factor V
  obtain ⟨i₀, hi₀, -⟩ := grpPullback_iso
    (((SplitTorus.isGrpPullback_bcMap r ℤ).comp ((isGrpPullback_of_iso i).comp (isGrpPullback_pullback G _))).congr
      ((congrArg (r ≫ ·) (Category.id_comp _)).trans hr.symm) rfl)
    (isGrpPullback_pullback G (thick _ (IsLocalRing.maximalIdeal V) 0))
  obtain ⟨P₀, w₀, h₀⟩ := exists_isLevelCP (IsLocalRing.maximalIdeal V) 0 P
  have hm : (IsLocalRing.maximalIdeal V ^ (0 + 1)).IsMaximal := by
    rw [zero_add, pow_one]; infer_instance
  let _ : Field (V ⧸ IsLocalRing.maximalIdeal V ^ (0 + 1)) := Ideal.Quotient.field _
  obtain ⟨wA, hwA⟩ := hw
  refine ⟨A, G, inferInstance, inferInstance, ⟨hV, hG, eA, hA, P, wA, hwA, ℤ, tqOfIso i₀, P₀, ⟨w₀, h₀⟩,
    exists_even_cubTriv i₀ h₀ s (fun y J hJ => (hs _ _ y J hJ).1 (hθ _ ?_)) fun Z r z J hJ => (hs Z r z J hJ).2⟩,
    hg, Module.finrank_self ℤ, fun h => not_isProper_torus
      (V ⧸ IsLocalRing.maximalIdeal V ^ (0 + 1)) ?_⟩
  · exact (congrArg (fun q => q y) (pullback.condition.trans (congrArg (_ ≫ ·) hr))).trans
      (IsLocalRing.PrimeSpectrum.comap_residue _ (r (pullback.snd G.hom _ y)))
  · have : IsIso i₀.hom.left := inferInstanceAs (IsIso ((Over.forget _).map i₀.hom))
    rw [← Over.w i₀.hom]
    infer_instance

theorem exists_unif_rank_one (hV : CDVR V) : ∃ (A : PolAV (Spec (CommRingCat.of (FractionRing V)))) (G : Over (Spec (CommRingCat.of V))) (_ : GrpObj G) (_ : IsCommMonObj G) (D : DegData V (IsLocalRing.maximalIdeal V)) (_ : Unif (IsLocalRing.maximalIdeal V) D A G), IsSemiAbelian G ∧ A.g = 1 ∧ Module.finrank ℤ D.toPre.X = 1 ∧ D.toPre.P.g = 0 := by
  obtain ⟨A, G, _, _, s, hA, -, hnp⟩ := exists_setting hV
  obtain ⟨D, U, -⟩ := GlobalTheory.UU.exists_degData_unif_unconditional V A G s
  have hR : AdmBase V (IsLocalRing.maximalIdeal V) :=
    have := hV.1
    ⟨inferInstance, inferInstance, inferInstance, hV.2.1⟩
  have h := rank_add_dim hR s.semi U
  have h0 : Module.finrank ℤ D.toPre.X ≠ 0 := fun h0 => by
    have : Subsingleton D.toPre.X := Module.finrank_zero_iff.1 h0
    exact hnp (isProper_of_subsingleton (U.gt 0))
  exact ⟨A, G, inferInstance, inferInstance, D, U, s.semi, hA, by omega, by omega⟩

end GlobalTheory.SplitMultiplicative

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSymp
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped GlobalTheory.VacAny

noncomputable section

namespace GlobalTheory.SympChange

variable {F : Type} [Field F] {κ : Type} [Fintype κ] [DecidableEq κ]

def spAct {R : Type} [CommRing R] [Algebra F R] (G : Matrix (κ ⊕ κ) (κ ⊕ κ) F) (w : (κ → R) × (κ → R)) :
    (κ → R) × (κ → R) :=
  (fun k => (G.map (algebraMap F R) *ᵥ Sum.elim w.1 w.2) (Sum.inl k),
    fun k => (G.map (algebraMap F R) *ᵥ Sum.elim w.1 w.2) (Sum.inr k))

def weylM : Matrix (κ ⊕ κ) (κ ⊕ κ) F := Matrix.fromBlocks 0 1 (-1) 0

def leviM (A : Matrix κ κ F) : Matrix (κ ⊕ κ) (κ ⊕ κ) F := Matrix.fromBlocks A 0 0 A⁻¹ᵀ

def unipM (S : Matrix κ κ F) : Matrix (κ ⊕ κ) (κ ⊕ κ) F := Matrix.fromBlocks 1 0 S 1

def IsSymp (G : Matrix (κ ⊕ κ) (κ ⊕ κ) F) : Prop := G.transpose * weylM * G = weylM

def gens : Set (Matrix (κ ⊕ κ) (κ ⊕ κ) F) :=
  {G | ∃ A : Matrix κ κ F, IsUnit A.det ∧ G = leviM A} ∪ {G | ∃ S : Matrix κ κ F, S.transpose = S ∧ G = unipM S} ∪ {weylM}

variable [NumberField F]

def indO (v : Pl F) : (κ → Fv F v) → ℂ := Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1

def HasOp (ψ : AddChar (AF F) ℂ) (G : Matrix (κ ⊕ κ) (κ ⊕ κ) F) : Prop :=
  ∃ (e : ((κ → AF F) → ℂ) →ₗ[ℂ] (κ → AF F) → ℂ) (ei : SInf F κ →L[ℂ] SInf F κ)
    (ev : ∀ v : Pl F, ((κ → Fv F v) → ℂ) →ₗ[ℂ] (κ → Fv F v) → ℂ),
    Function.Surjective ei ∧ (∀ Φ ∈ schA F κ, e Φ ∈ schA F κ) ∧
    (∀ w, ∀ Φ ∈ schA F κ, e (schr ψ w Φ) = schr ψ (spAct G w) (e Φ)) ∧
    (∀ v, (SB _).map (ev v) = SB _) ∧ (∀ v, ∀ φ ∈ SB (κ → Fv F v), ev v φ = 0 → φ = 0) ∧
    (∀ v w, ∀ φ ∈ SB (κ → Fv F v),
      ev v (schr (GlobalTheory.LatVac.psiAt ψ v) w φ) = schr (GlobalTheory.LatVac.psiAt ψ v) (spAct G w) (ev v φ)) ∧
    (∀ᶠ v in cofinite, ev v (indO v) = indO v) ∧
    ∀ f φ, (∀ v, φ v ∈ SB _) → (∀ᶠ v in cofinite, φ v = indO v) → e (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ) = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (ei f) fun v => ev v (φ v)

end GlobalTheory.SympChange
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsUnitaryAdelicMatrixConjOrthonormalFrameStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField Matrix MvPolynomial
open scoped TensorProduct nonZeroDivisors
open GlobalTheory.SignedHC GlobalTheory.ChiGrid Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.FunObj
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isUnitaryAdelicMatrix_conj_orthonormalFrame : ∀ (D : D7) (V : HSp D) (fr : GL (Fin V.rank) D.host.E) (g : Matrix (Fin V.rank) (Fin V.rank) (GlobalTheory.AdLat.RA D.host.F D.host.E)),
    Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) fr.1 * V.gram * fr.1 = 1 → GlobalTheory.UnRep.IsUnA (GlobalTheory.Member.cF D) 1 g →
    GlobalTheory.UnRep.IsUnA (GlobalTheory.Member.cF D) V.gramᵀ (GlobalTheory.UnRep.fm D.host.F fr.1 * g * GlobalTheory.UnRep.fm D.host.F (fr⁻¹).1) := by
  first | exact @GlobalTheory.UnitConjFrame.isUnA_frame_conj | exact GlobalTheory.UnitConjFrame.isUnA_frame_conj | (intros; apply GlobalTheory.UnitConjFrame.isUnA_frame_conj <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsVeryAmpleBySectionsOfLinearSpanCombinationStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isVeryAmpleBySections_of_linear_span_combination : ∀ (R : Type) [CommRing R] (X : Scheme.{0}) (f : X ⟶ Spec (CommRingCat.of R)) (H : LB X) (m N : ℕ) (s : Fin (m + 1) → LB.Sec H) (t : Fin (N + 1) → LB.Sec H) (a : Matrix (Fin (m + 1)) (Fin (N + 1)) R), H.IsLB → GlobalTheory.AbLaw.VeryAmpleBy f H s → (∀ i, s i = ∑ j, GlobalTheory.AbLaw.cst f ⊤ (a i j) • t j) → GlobalTheory.AbLaw.VeryAmpleBy f H t := by
  first | exact @GlobalTheory.veryAmpleBy_of_span | exact GlobalTheory.veryAmpleBy_of_span | (intros; apply GlobalTheory.veryAmpleBy_of_span <;> assumption)
end

