import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1462
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0022
import Development.AbelianVarietyTheory.Definitions.Divisors.IsSquareIntegrableIffMemL2
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1473
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1478
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0062
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1501
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeviBlockSizesSum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WittRankLeSkewSignature
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0331
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1387
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0282
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1504
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1506
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1455
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1308
import Development.AbelianVarietyTheory.Definitions.CMLattices.IsDiffOf
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0033
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0042
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0141
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0056
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.WeightFunctionOnFrames
import Development.AbelianVarietyTheory.BlockTheory.ExistenceTori.UnitaryHaarVolume
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.Bundle0020
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle0028
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1465
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1468
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1038
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1406
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.LtChar
import Development.AbelianVarietyTheory.Statements.WeilDeligneCrystalline.Bundle0001
import Development.AbelianVarietyTheory.Statements.WeilDeligneCrystalline.EqNegOneOfJumpAt
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemRangeOfHasSumZero
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0317
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0570
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0594
import Development.AbelianVarietyTheory.CrystallinePeriods.RingIface
import Development.AbelianVarietyTheory.CrystallinePeriods.Bundle0001
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1507
import Development.AbelianVarietyTheory.Definitions.Divisors.DiagHermitianTrivialOfSumFourSquares
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1508
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1445
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1469
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModerateEisensteinHolomorphicBall
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1446
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1444

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsotropicColumnsExtendWitt
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.ThK.SquareIntegrability
noncomputable section

namespace GlobalTheory.WittExt

open Matrix
open Formalism.UG (cT)

theorem exists_isWittFrame_initCols : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
    ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (r : ℕ) (C : Matrix (Fin n) (Fin (r + 1)) E),
      LinearIndependent E C.transpose → Formalism.UG.cT (σ : E →+* E) C * J * C = 0 →
        ∃ (m : ℕ) (hm : r < m) (X Y : Matrix (Fin n) (Fin m) E), IsWittFrame σ J X Y ∧ GlobalTheory.StdPar.initCols X ⟨r, hm⟩ = C := by
  first
  | exact @_root_.GlobalTheory.AdjugateAppendColumn.exists_wittFrame_initCols
  | exact _root_.GlobalTheory.AdjugateAppendColumn.exists_wittFrame_initCols
  | (apply _root_.GlobalTheory.AdjugateAppendColumn.exists_wittFrame_initCols <;> assumption)
  | (intros; apply _root_.GlobalTheory.AdjugateAppendColumn.exists_wittFrame_initCols <;> assumption)
  | (intros; apply @_root_.GlobalTheory.AdjugateAppendColumn.exists_wittFrame_initCols <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.AdjugateAppendColumn.exists_wittFrame_initCols ..)

end GlobalTheory.WittExt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KinfFinite
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SmGL GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.LeviBlockExponent GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
  GlobalTheory.UAut GlobalTheory.SiegelSet GlobalTheory.ThK.SquareIntegrability GlobalTheory.CuspBlock GlobalTheory.LFun.SplitTie
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.CuspKinfFin

theorem kinf_finite : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [IsTotallyComplex E] [Algebra F E]
    (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J →
    ∀ (r : ℕ) (Xf Yf : Matrix (Fin n) (Fin r) E), IsWittFrame σ J Xf Yf → ∀ (K : Subgroup (GAd σ J)), IsMaxCpt σ J K →
    ∀ (S : Finset (Fin r)) (l d : ℕ) (h : l + d ≤ r) (ι : GlobalTheory.CuspRep.GA E d →* GAd σ J), GlobalTheory.BlockForms.IsBlockEmb σ J Xf Yf h ι →
      1 ≤ d → (∀ j : Fin r, l ≤ j.val → j.val + 1 < l + d → j ∉ S) → (∃ k ∈ S, k.val + 1 = l + d) →
      (l = 0 ∨ ∃ p ∈ S, p.val + 1 = l) →
      ∀ (ψ : GAd σ J → ℂ), GlobalTheory.StdPar.IsCuspOn σ J Xf Yf S K ψ → ∀ g₀ : GAd σ J,
        (∀ k : GlobalTheory.CuspRep.Kinf E d, g₀⁻¹ * ι (GlobalTheory.CuspRep.infGL E d (Unitary.toUnits k)) * g₀ ∈ K) →
        FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun k : GlobalTheory.CuspRep.Kinf E d => fun g : GlobalTheory.CuspRep.GA E d => ψ (ι (g * GlobalTheory.CuspRep.infGL E d (Unitary.toUnits k)) * g₀))) := by
  intro F E _ _ _ _ _ _ σ _ n J _ r Xf Yf _ K _ S l d h ι _ _ _ _ _ ψ hψ g₀ hK
  classical
  let T : (GAd σ J → ℂ) →ₗ[ℂ] (GlobalTheory.CuspRep.GA E d → ℂ) :=
    { toFun := fun φ g => φ (ι g * g₀)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hV := hψ.1.kfin
  refine Submodule.finiteDimensional_of_le (S₂ := (Submodule.span ℂ (Set.range fun k : K => fun g => ψ (g * k))).map T) ?_
  rw [Submodule.span_le]
  rintro _ ⟨k, rfl⟩
  refine ⟨fun x => ψ (x * (g₀⁻¹ * ι (GlobalTheory.CuspRep.infGL E d (Unitary.toUnits k)) * g₀)), Submodule.subset_span ⟨⟨_, hK k⟩, rfl⟩, ?_⟩
  funext g
  show ψ (ι g * g₀ * (g₀⁻¹ * ι (GlobalTheory.CuspRep.infGL E d (Unitary.toUnits k)) * g₀)) = _
  simp only [map_mul, mul_assoc, mul_inv_cancel_left]

end GlobalTheory.CuspKinfFin
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeviElementInfinitePointsStatement
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)
open GlobalTheory.UAut GlobalTheory.SiegelSet GlobalTheory.ThK.SquareIntegrability GlobalTheory.ThKCtFin GlobalTheory.TorFin

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.levi_element_infinite_points : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E), IsCMExt F E σ → ∀ (d r s : ℕ) (W : Spc F E d), W.IsSkew σ B r s → ∀ (hσ : ∀ x, σ (σ x) = x) (c : E) (hc : c ≠ 0), σ c = -c → ∀ (d₁ : ℕ) (W₁ : Spc F E d₁) (H' : Plane E d d₁) (i₀ i₁ : ℕ), H'.IsAdapted σ B W W₁ i₀ i₁ → ∀ a ∈ idelesInf F E, toGAd hσ W.J hc (leviElt σ W W₁ H' a) ∈ infPts σ (c • W.J.map σ) ∧ ∀ (w : InfinitePlace F) (τ : EmbOver E w), ∃ z : ℂ, z ≠ 0 ∧ GlobalTheory.Orb.archMat σ (c • W.J.map σ) τ (projArch σ (c • W.J.map σ) w (toGAd hσ W.J hc (leviElt σ W W₁ H' a))) = torMat ((c • W.J.map σ).map τ.1) (fun i => τ.1 (H'.x i)) (fun i => τ.1 (c⁻¹ * H'.y i)) z := by
  first | exact @GlobalTheory.LeviArch.leviElt_arch | exact GlobalTheory.LeviArch.leviElt_arch | (intros; apply GlobalTheory.LeviArch.leviElt_arch <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LieAlgebraMetricConjEmbeddingEqConj
section
open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.GeometryOfNumbersTheory GlobalTheory GlobalTheory.CM GlobalTheory.ArchMetricCompare

attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.CM.LieMetricConj

variable {K : Type} [Field K]

theorem form_conj_of_single {g : ℕ} (h : HermFam K (Fin g → K)) (s : K →+* ℂ)
    (e : ∀ i j, h.form ((starRingEnd ℂ).comp s) (Pi.single i 1) (Pi.single j 1) =
      starRingEnd ℂ (h.form s (Pi.single i 1) (Pi.single j 1)))
    (a b : Fin g → K) : h.form ((starRingEnd ℂ).comp s) a b = starRingEnd ℂ (h.form s a b) := by
  have key : ∀ t : K →+* ℂ, h.form t a b =
      ∑ j, t (b j) * starRingEnd ℂ (∑ i, t (a i) * h.form t (Pi.single j 1) (Pi.single i 1)) := by
    intro t
    rw [LieMetric.form_sum_right h t a b]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← h.conj_symm t (Pi.single j 1) a, LieMetric.form_sum_right h t (Pi.single j 1) a]
  rw [key ((starRingEnd ℂ).comp s), key s]
  simp only [map_sum, map_mul, RingHom.comp_apply, e, Complex.conj_conj]

end GlobalTheory.CM.LieMetricConj

namespace GlobalTheory.CM.LieMetricConj

open GlobalTheory.ConjUnif

variable {K : Type} [Field K] [NumberField K]

theorem conj_conj_comp (s : K →+* ℂ) : (starRingEnd ℂ).comp ((starRingEnd ℂ).comp s) = s :=
  RingHom.ext fun x => by simp

theorem single_conj (hU : ThetaUnifAV) {P : Out.PolAV (Sp (𝓞 K))} (F : GenFib P) (h : HermFam K (Fin F.P₀.g → K))
    (H : F.IsHerm h) (s : K →+* ℂ) (i j : Fin F.P₀.g) :
    h.form ((starRingEnd ℂ).comp s) (Pi.single i 1) (Pi.single j 1) =
      starRingEnd ℂ (h.form s (Pi.single i 1) (Pi.single j 1)) := by
  obtain ⟨Q, ψ, v, u, Hm, χ, W, a, b, c, d⟩ := H s
  obtain ⟨Q', ψ', v', u', Hm', χ', W', a', b', c', d'⟩ := H ((starRingEnd ℂ).comp s)
  obtain ⟨A'', _, ψc, hc⟩ : ∃ (A'' : Over (Sp ℂ)) (_ : GrpObj A'') (ψc : A''.left ⟶ Q'.A.left),
      IsGrpPullback A'' Q'.A cj ψc :=
    ⟨_, _, _, isGrpPullback_pullback Q'.A cj⟩
  let Q'' : Out.PolAV (Sp ℂ) := pullPol Q' hc
  have hQ : IsPolFibre (starRingEnd ℂ) Q' Q'' ψc := ⟨rfl, hc, ⟨idIso _, idIso_isGen (pull_isLB Q'.isLB ψc)⟩⟩
  have a'' : IsPolFibre s F.P₀ Q'' (ψc ≫ ψ') := by
    rw [← conj_conj_comp s]
    exact PolFibre.comp a' hQ
  choose v'' hv'' using fun k => (existsUnique_isVecOver hc.1 (v' k)).exists
  have ht : ∀ k, IsTangent (v' k) := fun k => (c' k).1.isTangent a'.2.1 (F.basis.1 k)
  have c'' : ∀ k, IsVecOver s (ψc ≫ ψ') (F.v k) (v'' k) ∧ (conjPull hc u').IsDiff (star (W' k)) (v'' k) := by
    intro k
    refine ⟨?_, cj_isDiff hc (pullId u') (ht k) (hv'' k) (c' k).2⟩
    rw [← conj_conj_comp s]
    exact (PolFibre.vec_iff a'.2.1.1 hc.1.w (c' k).1).1 (hv'' k)
  have e := LieMetric.hermForm_eq hU a a'' b (conjPull_isAH hc u' b') F.basis.1 c c'' j i
  rw [d, d', e]
  unfold hermForm
  rw [map_mul, Complex.conj_ofReal, star_star]
  congr 1
  simp [dotProduct, Matrix.mulVec, map_sum, Complex.star_def]

theorem form_conj : ∀ (K : Type) [Field K] [NumberField K] (P : ReciprocityTheory.ChartRestriction.G.Out.PolAV (Sp (𝓞 K)))
    (F : GlobalTheory.CM.GenFib P) (h : ReciprocityTheory.GeometryOfNumbersTheory.HermFam K (Fin F.P₀.g → K)), F.IsHerm h → ∀ (σ : K →+* ℂ)
    (a b : Fin F.P₀.g → K), h.form ((starRingEnd ℂ).comp σ) a b = starRingEnd ℂ (h.form σ a b) :=
  fun _ _ _ _ F h H σ a b => form_conj_of_single h σ (single_conj thetaUnifAV_all F h H σ) a b

end GlobalTheory.CM.LieMetricConj
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LintegralInvariantChartSetLeMulFundamentalSet
section
open NumberField MeasureTheory ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates GlobalTheory.LevGeo
open scoped ENNReal

namespace GlobalTheory.Unfold

theorem lintegral_chart_le_mul_fundSet : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (x0 x : Frame X.Ψ r) (FF A : Set (V (nd X))) (m : ℝ≥0∞) (Φ : Frame X.Ψ r → ℝ≥0∞), IsOrth X x0 → IsOrth X x → IsFundSet X x0 FF → MeasurableSet A → A ⊆ OmF X x → Measurable Φ → (∀ γ ∈ X.Γ, ∀ x ∈ X.dom, Φ (lact γ x) = Φ x) → (∀ b ∈ Bor X.Ψ r, ∀ x ∈ X.dom, Φ (rmul x b) = Φ x) → (({γ : GL (Fin r) E | γ ∈ X.Γ ∧ ∃ z ∈ A, ∃ z' ∈ A, ∃ b ∈ Bor X.Ψ r, lact γ (cpt X x z) = rmul (cpt X x z') b}.encard : ℝ≥0∞) ≤ m) → ∫⁻ z in A, Φ (cpt X x z) ∂(muF X x) ≤ m * ∫⁻ z in FF, Φ (cpt X x0 z) ∂(muF X x0) := by
  intro E _ _ _ r X x0 x FF A m Φ ho0 ho hF hA hAO hΦ hΓ hB hm
  classical
  have := FundSetPf.countable_GL (E := E) (r := r)
  have hM := ReciprocityTheory.ChartRestriction.G.AR.Up.measInv_holds (E := E)
  have hc : Measurable (cpt X x0) := (FundSetPf.cont_cpt X x0).measurable
  let ψ : Frame X.Ψ r → ℝ≥0∞ := (satFrames X x A).indicator Φ
  have hψ : Measurable ψ := hΦ.indicator (measurableSet_satFrames X ho hA hAO)
  have hψB : ∀ y ∈ X.dom, ∀ b ∈ Bor X.Ψ r, ψ (rmul y b) = ψ y := by
    intro y hy b hb
    simp only [ψ, Set.indicator, rmul_mem_satFrames_iff X x A _ hb, hB b hb y hy]
  have h1 : ∫⁻ z in A, Φ (cpt X x z) ∂muF X x = ∫⁻ z, ψ (cpt X x z) ∂muF X x := by
    rw [← lintegral_indicator hA]
    refine lintegral_congr fun z => ?_
    simp only [ψ, Set.indicator, cpt_mem_satFrames_iff X ho]
  rw [h1, ← hM r X x0 x ho0 ho ψ hψ hψB, lintegral_unfold hM r X x0 ho0 FF hF ψ hψ hψB,
    ← lintegral_const_mul m (f := fun z => Φ (cpt X x0 z)) (hΦ.comp hc)]
  refine setLIntegral_mono ((hΦ.comp hc).const_mul m) fun z hz => ?_
  set y := cpt X x0 z with hy_def
  have hy : y ∈ X.dom := hF.2.1 hz
  let S : Set (GL (Fin r) E) := {γ : GL (Fin r) E | γ ∈ X.Γ ∧ ∃ z ∈ A, ∃ z' ∈ A, ∃ b ∈ Bor X.Ψ r,
    lact γ (cpt X x z) = rmul (cpt X x z') b}
  let T : Set X.Γ := {γ | lact γ.1 y ∈ satFrames X x A}
  by_cases hT : T.Nonempty
  swap
  · have h0 : ∀ γ : X.Γ, ψ (lact γ.1 y) = 0 := fun γ =>
      Set.indicator_of_notMem (s := satFrames X x A) (fun h => hT ⟨γ, h⟩) Φ
    simp [h0]
  obtain ⟨γ0, hγ0⟩ := hT
  obtain ⟨z0, hz0, b0, hb0, e0⟩ := hγ0
  have hpt : ∀ γ : X.Γ, ψ (lact γ.1 y) ≤ T.indicator (fun _ => Φ y) γ := by
    intro γ
    by_cases hγ : γ ∈ T
    · rw [Set.indicator_of_mem hγ]
      show (satFrames X x A).indicator Φ _ ≤ _
      rw [Set.indicator_of_mem (s := satFrames X x A) hγ Φ, hΓ γ.1 γ.2 y hy]
    · rw [Set.indicator_of_notMem hγ]
      exact le_of_eq (Set.indicator_of_notMem (s := satFrames X x A) hγ Φ)
  have hTS : T.encard ≤ S.encard := by
    let f : X.Γ → GL (Fin r) E := fun γ => γ.1 * γ0.1⁻¹
    have hinj : Set.InjOn f T := fun a _ b _ h => Subtype.ext (mul_right_cancel h)
    rw [← hinj.encard_image]
    refine Set.encard_le_encard ?_
    rintro _ ⟨γ, ⟨z1, hz1, b1, hb1, e1⟩, rfl⟩
    refine ⟨X.Γ.mul_mem γ.2 (X.Γ.inv_mem γ0.2), z0, hz0, z1, hz1,
      rmul b1 (ExtFPf.invF X b0), ExtFPf.mul_mem X hb1 (ExtFPf.invF_mem X hb0), ?_⟩
    have e0' : cpt X x z0 = rmul (lact γ0.1 y) (ExtFPf.invF X b0) := by
      rw [e0, ExtFPf.rmul_assoc, ExtFPf.rmul_invF X hb0, ExtFPf.rmul_oneF]
    show lact (γ.1 * γ0.1⁻¹) (cpt X x z0) = _
    rw [e0', FundSetPf.lact_rmul, FundSetPf.lact_mul, FundSetPf.lact_inv, e1, ExtFPf.rmul_assoc]
  calc ∑' γ : X.Γ, ψ (lact γ.1 y) ≤ ∑' γ : X.Γ, T.indicator (fun _ => Φ y) γ := ENNReal.tsum_le_tsum hpt
    _ = (T.encard : ℝ≥0∞) * Φ y := by rw [← tsum_subtype, ENNReal.tsum_set_const]
    _ ≤ m * Φ y := by
      gcongr
      exact le_trans (by exact_mod_cast hTS) hm

end GlobalTheory.Unfold
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LintegralUnitCubeTranslatesSlabPeriodicLeStatement
section
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped TensorProduct NNReal Matrix ENNReal
open scoped Classical
open GlobalTheory.ArchDecay

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lintegral_unitCube_translates_slabPeriodic_le : ∀ {G : Type} [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G] [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsAddLeftInvariant] {N : ℕ} (ι : (Fin N → ℝ) →+ G) (π : G →+ (Fin N → ℝ)), Continuous ι → Continuous π → (∀ t, π (ι t) = t) → ∀ (U : Set G), MeasurableSet {w | w - ι (π w) ∈ U} → (∀ A : Set (Fin N → ℝ), IsCompact A → μ (π ⁻¹' A ∩ {w | w - ι (π w) ∈ U}) ≠ ⊤) → ∀ (φ : G → ℝ≥0∞), Measurable φ → (∀ w, ∀ u ∈ U, φ (w + u) = φ w) → ∀ y : G, μ (π ⁻¹' cube N ∩ {w | w - ι (π w) ∈ U}) * ∫⁻ t in cube N, φ (y + ι t) ≤ ∫⁻ w, φ w ∂μ := by
  first | exact @GlobalTheory.ArchDecay.lintegral_cube_slab_le | exact GlobalTheory.ArchDecay.lintegral_cube_slab_le | (intros; apply GlobalTheory.ArchDecay.lintegral_cube_slab_le <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalThetaIntegralAtInertPlaceStatement
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.KFinLoc
open scoped TensorProduct Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_theta_integral_at_inert_place : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl F) (w : HeightOneSpectrum (𝓞 E)), Formalism.UG.IsInertAt F E v w → v ∉ X.T →
    ∀ t : GL (Fin (a + a')) (AE F E), (At (evFin F v) ((t : Matrix (Fin (a + a')) (Fin (a + a')) (AE F E)) - 1) ∧
      ∀ z ∈ GlobalTheory.InertSph.latAt G.W v, (t : Matrix (Fin (a + a')) (Fin (a + a')) (AE F E)) *ᵥ z ∈ GlobalTheory.InertSph.latAt G.W v ∧
        ((t⁻¹ : GL (Fin (a + a')) (AE F E)) : Matrix (Fin (a + a')) (Fin (a + a')) (AE F E)) *ᵥ z ∈ GlobalTheory.InertSph.latAt G.W v) →
      (adeleClass F).modu (Units.map (Algebra.norm (AF F) : AE F E →* AF F) (Matrix.GeneralLinearGroup.det t)) = 1 := by
  first | exact @GlobalTheory.IntegralDetModule.modu_norm_det_triple | exact GlobalTheory.IntegralDetModule.modu_norm_det_triple | (intros; apply GlobalTheory.IntegralDetModule.modu_norm_det_triple <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LpDimLocParT
section
noncomputable section

open NumberField IsDedekindDomain ValuativeRel Matrix Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.SatakeFlip GlobalTheory.CuspRep
  GlobalTheory.CuspRep.ParLawsT
open GlobalTheory.Mem.Chr hiding HChar

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.CuspRep.ParLawsT

theorem lpDim_locParT (hT : UpperTheory.Zero.LLC.RecTExists) (E Ω : Type) [Field E] [NumberField E] [IsTotallyComplex E]
    [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (a : ℕ)
    (π : CG E a) (h : IsPlaceOver A w) : (locParT hT π h).lpDim = a := by
  obtain ⟨_, _, H⟩ := isRecT_locRecT hT h
  exact H.dim _

end GlobalTheory.CuspRep.ParLawsT

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapAlgebraMap
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations
open GlobalTheory.HeckeGal GlobalTheory.Pst GlobalTheory.TripleGal GlobalTheory.LocLanglands GlobalTheory.WeilDeligne TensorProduct CompanionTheory.PRW.ACWD GlobalTheory.PZ GlobalTheory.PMC
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.PMC.BrChar

theorem map_algebraMap {l : ℕ} [Fact l.Prime] (K : FinExt l) (τ : ↥K.1 →+* Om l)
    (hτ : ∀ y : ↥K.1, ‖(y : Om l)‖ ≤ 1 → ‖τ y‖ ≤ 1) (q : ℚ_[l]) :
    τ (algebraMap ℚ_[l] ↥K.1 q) = algebraMap ℚ_[l] (Om l) q := by
  let f : ℚ_[l] →+* Om l := τ.comp (algebraMap ℚ_[l] ↥K.1)
  have hf : ∀ x : ℚ_[l], ‖x‖ ≤ 1 → ‖f x‖ ≤ 1 := fun x hx => hτ _ (by
    show ‖algebraMap ℚ_[l] (Om l) x‖ ≤ 1
    rwa [norm_algebraMap'])
  have hl0 : (l : ℚ_[l]) ≠ 0 := by exact_mod_cast (Fact.out : l.Prime).ne_zero
  have hl1 : ‖(l : ℚ_[l])‖ < 1 := Padic.norm_p_lt_one
  have hlO : ‖(l : Om l)‖ = ‖(l : ℚ_[l])‖ := by
    rw [← map_natCast (algebraMap ℚ_[l] (Om l)), norm_algebraMap']
  have hc : Continuous f := by
    refine continuous_of_continuousAt_zero f (Metric.continuousAt_iff.2 fun ε hε => ?_)
    obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hε hl1
    have hp : 0 < ‖(l : ℚ_[l])‖ ^ n := pow_pos (norm_pos_iff.2 hl0) n
    refine ⟨_, hp, fun x hx => ?_⟩
    rw [dist_zero_right] at hx
    rw [map_zero, dist_zero_right]
    have h1 := hf (x / (l : ℚ_[l]) ^ n) (by rw [norm_div, norm_pow, div_le_one hp]; exact hx.le)
    rw [map_div₀, map_pow, map_natCast, norm_div, norm_pow, hlO, div_le_one hp] at h1
    exact h1.trans_lt hn
  exact congrFun ((Padic.denseRange_ratCast l).equalizer hc (continuous_algebraMap ℚ_[l] (Om l))
    (funext fun r => by simp)) q

theorem main : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (l : ℕ) [Fact l.Prime]
    (w : HeightOneSpectrum (𝓞 E)) (A : ValuationSubring Ω) (h : IsPlaceOver A w)
    (O : Type) [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l E Ω (Dec (F := E) A) O),
    GlobalTheory.Pst.Induces Bw → ∀ (a : Weil h →* (w.adicCompletion E)ˣ), IsLocalArtin h a →
    ∀ (π : (w.adicCompletion E)ˣ), IsUnifAt w π →
    ∀ (j₀ : {j : w.adicCompletion E →+* Qbar l // Continuous j}) (LL : FinExt l)
      (ψ : ↥(Dec (F := E) A) →* GL (Fin 1) ↥LL.1), Continuous (ent ψ) →
      (∀ σ : Weil h, ent ψ ⟨σ, Weil_le_Dec h σ.2⟩ = j₀.1 (((a σ : (w.adicCompletion E)ˣ) : w.adicCompletion E) * ((π : w.adicCompletion E) ^ deg σ))) →
      ∃ (τ₀ : ↥Bw.Kw.1 →ₐ[ℚ_[l]] ↥LL.1) (χ : ↥(GK Bw.Kw) →* (↥Bw.Kw.1)ˣ) (π' : ↥(OL Bw.Kw)) (z : ℕ → Om l),
        (∀ x : E, j₀.1 (algebraMap E (w.adicCompletion E) x) = ((τ₀ ⟨Bw.j (algebraMap E Ω x), Bw.j_E x⟩ : ↥LL.1) : Qbar l)) ∧
        LTData Bw.Kw χ π' z ∧ ((τ₀ (π' : ↥Bw.Kw.1) : ↥LL.1) : Qbar l) = j₀.1 (π : w.adicCompletion E) ∧
        ∀ g : ↥(Dec (F := E) A), ent ψ g = ((τ₀ ((χ (Bw.e g) : (↥Bw.Kw.1)ˣ) : ↥Bw.Kw.1) : ↥LL.1) : Qbar l) := by
  intro E Ω _ _ _ _ _ l _ w A h O _ _ _ Bw hB a ha π hπ j₀ LL ψ hψc hψ

  have hmem : ∀ g, ent ψ g ∈ LL.1 := fun g => Subtype.property _
  have hv : Valued.v ((1 : w.adicCompletion E) + π) = 1 := by
    apply Valuation.map_one_add_of_lt
    unfold IsUnifAt at hπ
    rw [hπ, ← WithZero.exp_zero, WithZero.exp_lt_exp]
    norm_num
  have hπL : j₀.1 (π : w.adicCompletion E) ∈ LL.1 := by
    have h0 : (1 : w.adicCompletion E) + π ≠ 0 := fun h0 => by simp [h0] at hv
    obtain ⟨σ, hσ⟩ := ha.surj (Units.mk0 _ h0)
    have hd : deg σ = 0 := by
      have := ha.ord_eq σ
      rw [hσ, GlobalTheory.PY.LTInh.ord_unit (x := Units.mk0 _ h0) hv] at this
      omega
    have := hmem ⟨σ, Weil_le_Dec h σ.2⟩
    rw [hψ, hd, hσ] at this
    simp only [zpow_zero, mul_one, Units.val_mk0, map_add, map_one] at this
    simpa using LL.1.sub_mem this LL.1.one_mem
  have hall : ∀ x : w.adicCompletion E, j₀.1 x ∈ LL.1 := fun x => by
    rcases eq_or_ne x 0 with rfl | hx
    · rw [map_zero]; exact LL.1.zero_mem
    obtain ⟨σ, hσ⟩ := ha.surj (Units.mk0 x hx)
    have h1 := hmem ⟨σ, Weil_le_Dec h σ.2⟩
    rw [hψ, map_mul, map_zpow₀, hσ, Units.val_mk0] at h1
    have h2 := LL.1.mul_mem h1 (LL.1.inv_mem (LL.1.toSubfield.zpow_mem hπL (deg σ)))
    have h3 : j₀.1 (π : w.adicCompletion E) ^ deg σ ≠ 0 := zpow_ne_zero _ (by simp)
    rwa [mul_inv_cancel_right₀ h3] at h2

  obtain ⟨⟨j, hj, hjE⟩, H⟩ := GlobalTheory.LTTateC.main E Ω l w A h O Bw hB a ha
  obtain ⟨-, H2, H3⟩ := H j hj hjE
  obtain ⟨k, hk⟩ := GlobalTheory.LTTateC.exists_ringEquiv_Kw Bw j hj hjE
  obtain ⟨π', hπ', hππ⟩ := H2 π hπ
  obtain ⟨⟨c, hc, hcW⟩, H4⟩ := H3 π' hπ' π hππ

  let τ : ↥Bw.Kw.1 →+* Om l := j₀.1.comp (k.symm : ↥Bw.Kw.1 →+* w.adicCompletion E)
  have hτk : ∀ x, τ (k x) = j₀.1 x := fun x => congrArg j₀.1 (k.symm_apply_apply x)
  have hτ : ∀ y : ↥Bw.Kw.1, ‖(y : Om l)‖ ≤ 1 → ‖τ y‖ ≤ 1 := fun y hy => by
    obtain ⟨x, rfl⟩ := k.surjective y
    rw [hk, GlobalTheory.LTTateC.norm_le_one_iff j hj] at hy
    rw [hτk]
    exact (GlobalTheory.LTTateC.norm_le_one_iff j₀.1 j₀.2 x).2 hy
  let τ₀ : ↥Bw.Kw.1 →ₐ[ℚ_[l]] ↥LL.1 :=
    { τ.codRestrict LL.1 (fun y => hall _) with
      commutes' := fun q => Subtype.ext (map_algebraMap Bw.Kw τ hτ q) }
  have hτ₀ : ∀ x, ((τ₀ (k x) : ↥LL.1) : Qbar l) = j₀.1 x := hτk

  let χ : ↥(GK Bw.Kw) →* (↥Bw.Kw.1)ˣ :=
    (Units.map (k : w.adicCompletion E →+* ↥Bw.Kw.1).toMonoidHom).comp (c.comp Bw.e.symm.toMonoidHom)
  have hχ : ∀ g, ((χ g : (↥Bw.Kw.1)ˣ) : ↥Bw.Kw.1) = k (c (Bw.e.symm g) : (w.adicCompletion E)ˣ) := fun _ => rfl
  obtain ⟨χ₁, z, hz⟩ := exists_ltData_of_irreducible l Bw.Kw π' hπ'
  obtain ⟨_, hF, v, hvz, hS, hv0, -, -⟩ := ltData_tilt_hyps l Bw.Kw χ₁ π' z hz
  obtain ⟨-, hz0, hz1, hzr, -⟩ := hz
  obtain ⟨_, hiff⟩ := GlobalTheory.PZ.isLTEndo_iff_eq_lubinTateHom l Bw.Kw π' hπ'
  refine ⟨τ₀, χ, π', z, fun x => ?_, ⟨hπ', hz0, hz1, hzr, fun g => ?_⟩, ?_, fun g => ?_⟩
  · rw [← hτ₀]
    congr 2
    exact Subtype.ext ((hk _).trans (hjE x))
  · obtain ⟨⟨u, -, hu⟩, H5⟩ := H4 c hc hcW g
    refine ⟨u, Subtype.ext (by rw [hχ, hk]; exact hu), _, (hiff u _).2 rfl, fun n => ?_⟩
    have h6 := H5 u hu _ hF v hS hv0 n
    have hind : Topology.IsInducing (algebraMap (Om l) ℂ_[l]) :=
      (AddMonoidHomClass.isometry_of_norm (algebraMap (Om l) ℂ_[l])
        fun y => PadicComplex.norm_extends l y).isEmbedding.isInducing
    rw [← hind.hasSum_iff]
    have e2 : ((Formalism.Per.σO (g : GQ l) (v n) : Formalism.Per.OC l) : ℂ_[l]) =
        algebraMap (Om l) ℂ_[l] ((g : GQ l) (z n)) := by
      refine (GlobalTheory.RingIface.sigO_coe l (g : GQ l) (v n)).trans ?_
      rw [hvz]
      exact GlobalTheory.RingBasics.σC_coe _ _
    rw [e2] at h6
    refine (congrArg (HasSum · _) (funext fun i => ?_)).mp h6
    push_cast
    rw [hvz, Function.comp_apply, map_mul, map_pow]
    rfl
  · rw [← hτ₀]
    congr 2
    exact Subtype.ext (hππ.symm.trans (hk _).symm)
  · rw [hχ, hτ₀, MulEquiv.symm_apply_apply]
    have hd := (GlobalTheory.LTExt.ext_profinite h (B := Unit) 1 continuous_const).1
    refine congrFun (hd.equalizer hψc (j₀.2.comp hc) (funext fun σ => ?_)) g
    show ent ψ ⟨σ, Weil_le_Dec h σ.2⟩ = j₀.1 (c ⟨σ, Weil_le_Dec h σ.2⟩ : (w.adicCompletion E)ˣ)
    rw [hψ, hcW, Units.val_mul, Units.val_zpow_eq_zpow_val]

end GlobalTheory.PMC.BrChar

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MarkedFieldPairsEquivDefiniteFieldPairsOddStatement
section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKDef GlobalTheory.LKCount
open scoped TensorProduct Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.markedFieldPairs_equiv_definiteFieldPairs_odd : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p), G.a = 1 → Odd G.n → ∀ (sel : Polynomial G.F → ℂ), IsSel G sel → ∃ e : {q : Cls G // Irreducible (Quot.out q).pol ∧ (Quot.out q).Mark (sel (Quot.out q).pol)} ≃ {q : DCls G // Irreducible (Quot.out q).pol}, ∀ q, (Quot.out (e q).1).pol = (Quot.out q.1).pol ∧ ∀ (Kf : Subgroup G.GAf) (f : G.GAf → ℂ) (r : ℕ) (K : Subgroup (Gr G r)) (φ : Gr G r → ℂ), 0 < r → (∀ k ∈ Kf, ∀ g, f (k⁻¹ * g * k) = f g) → (∀ k ∈ K, ∀ g, φ (k⁻¹ * g * sigG G r k) = φ g) → (Quot.out (e q).1).term Kf f r K φ = (Quot.out q.1).term Kf f r K φ := by
  first | (exact @GlobalTheory.LKDef.cls_equiv_dcls_irr) | (exact GlobalTheory.LKDef.cls_equiv_dcls_irr) | (intros; apply GlobalTheory.LKDef.cls_equiv_dcls_irr <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MeasurablePeriodicArchRestrictionStatement
section
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThetaDecay
open scoped TensorProduct NNReal Matrix
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.measurable_periodic_arch_restriction : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ], ∃ (μ : @Measure (κ → AF F) (borel _)), @Measure.IsAddHaarMeasure _ _ _ (borel _) μ ∧ ∃ (a : ℕ) (C : ℝ), ∀ m : ℕ, 1 ≤ m → ∀ f : (κ → AF F) → ENNReal, (∀ x a' : κ → AF F, (∀ i, evI F (a' i) = 0 ∧ ∀ v, evFin F v (a' i) ∈ v.adicCompletionIntegers F) → f (x + (m : AF F) • a') = f x) → ∀ x : κ → AF F, Measurable (fun y : κ → mixedEmbedding.mixedSpace F => f (x + GlobalTheory.SobClass.archInc F y)) → ∫⁻ y : κ → mixedEmbedding.mixedSpace F, f (x + GlobalTheory.SobClass.archInc F y) ≤ ENNReal.ofReal (C * (m : ℝ) ^ a) * ∫⁻ z, f z ∂μ := by
  first | exact @GlobalTheory.SobClass.ClassMeas.class_meas | exact GlobalTheory.SobClass.ClassMeas.class_meas | (intros; apply GlobalTheory.SobClass.ClassMeas.class_meas <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModerateEisensteinHolomorphicBallStatement
section
open scoped TensorProduct NNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.EisRes
open GlobalTheory.Doubling (absE)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.moderate_eisenstein_holomorphic_ball : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
    ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (H₀ : ℂ → GAd σ J → ℂ) (s₀ : ℂ) (r : ℝ) (V : Set ℂ),
    IsOpen V → 0 < r → Metric.closedBall s₀ r ⊆ V → (∀ s ∈ V, IsSmoothModerate σ J (H₀ s)) →
    (∀ μ, GlobalTheory.EisLine.IsModerateForm σ J μ → DifferentiableOn ℂ (fun s => μ (H₀ s)) V) → ∀ j : ℤ,
    GlobalTheory.UAut.IsSm σ J fun g => circleIntegral (fun z => (z - s₀) ^ j * H₀ z g) s₀ r := by
  first | exact @GlobalTheory.CircleSmooth.isSm_circleIntegral | exact GlobalTheory.CircleSmooth.isSm_circleIntegral | (intros; apply GlobalTheory.CircleSmooth.isSm_circleIntegral <;> assumption)
end

