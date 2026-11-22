import Mathlib
import Development.AbelianVarietyTheory.Definitions.RegularCharts.MatrixTwoByTwoCongr
import Formalism.LocalToGlobal.ProjectiveLattices.FrameCharts
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0021
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle0016
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle0021
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle0015
import Development.AbelianVarietyTheory.Definitions.RegularCharts.Reframe
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PullCub
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.CubePullbacks.CubePull
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle0022
import Development.AbelianVarietyTheory.Definitions.RegularCharts.SCharts
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0010
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.CuspStatementPf
import Development.AbelianVarietyTheory.Definitions.RegularCharts.BaseNorm
import Development.AbelianVarietyTheory.Definitions.RegularCharts.ModelAt
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0017
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0016
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0013
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.MaxBoundPf
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle0010
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.ExistsContinuousOnEmbeddings
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0014
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0026
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0027
import Formalism.LocalToGlobal.ProjectiveLattices.IsGenFrGenFr
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.TriangularReframeCompBaseChangeBorel
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0025

-- bundled from Development.AbelianVarietyTheory.Proofs.GenericRegularity.FinrankEqOfExistsUniqueComb
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Reg
open scoped CategoryTheory.Obj

namespace GlobalTheory.Reg

theorem finrank_eq_of_existsUnique_comb {L V : Type} [Field L] [AddCommGroup V] [Module L V] (N : Submodule L V)
    {m : ℕ} (cv : Fin m → V) (hcv : ∀ i, cv i ∈ N) (h : ∀ v ∈ N, ∃! a : Fin m → L, ∑ i, a i • cv i = v) :
    Module.finrank L N = m := by
  have hli : LinearIndependent L cv := by
    rw [Fintype.linearIndependent_iff]
    intro g hg i
    have := (h 0 N.zero_mem).unique hg (y₂ := 0) (by simp)
    rw [this]; rfl
  have hN : N = Submodule.span L (Set.range cv) := by
    apply le_antisymm
    · intro v hv
      obtain ⟨a, rfl, -⟩ := h v hv
      exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
    · rw [Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      exact hcv i
  rw [hN, finrank_span_eq_card hli, Fintype.card_fin]

theorem finrank_chart_eig : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), ∀ (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (M : MChart Y), ∀ (L : Type) [Field L] [Algebra c.F L] (f : Γ(Y.X, M.U) →+* L) (x : Sp L ⟶ Xo.X) (Λ : M.Lift f x) (τ : E →+* ℂ) (N : Submodule L (Fin M.n → L)), (∀ cv, cv ∈ N ↔ M.Eig f τ cv) → Module.finrank L N = Dw.mult τ := by
  intro E _ _ _ H Dw l Xo c O _ β Y M L _ _ f x Λ τ N hN
  classical
  have hx0 : x ≫ Xo.s = sOf c L := by
    rw [← Λ.xF_fst, Category.assoc, pullback.condition, ← Category.assoc, Λ.xF_snd]
    show Spec.map _ ≫ Spec.map _ = Spec.map _
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  have hs : Smooth ((Over.pullback x).obj Xo.univ.t.G).hom := by
    have := Xo.univ.t.semi.smooth
    show Smooth (pullback.snd Xo.univ.t.G.hom x)
    infer_instance
  obtain ⟨n, xc, hx⟩ := ReciprocityTheory.ChartRestriction.G.Chart.univChartLoc ((Over.pullback x).obj Xo.univ.t.G)
  obtain ⟨d, hd, hdW⟩ : ∃ d : Fin (Dw.mult τ) → Fin n → L,
      LinearIndependent L d ∧ ∀ i, d i ∈ gfpEig (c := c) hx τ := by
    obtain ⟨B⟩ : Nonempty (Module.Basis (Fin (Dw.mult τ)) L (gfpEig (c := c) hx τ)) :=
      ⟨Module.finBasisOfFinrankEq L _ (gfp_finrank hx0 hx τ)⟩
    exact ⟨(gfpEig (c := c) hx τ).subtype ∘ B,
      B.linearIndependent.map' (gfpEig (c := c) hx τ).subtype (Submodule.ker_subtype _), fun i => by simp⟩
  obtain ⟨hex, htan, hco⟩ := GlobalTheory.Reg.vec_bijective E H Dw l Xo c O β Y M L f x Λ
  have hcomb := GlobalTheory.Reg.VecComb.isCombAt_iff_vec E H Dw l Xo c O β Y M L f x Λ
  have heig := GlobalTheory.Reg.isEigAt_iff_eig E H Dw l Xo c O β Y M L f x Λ τ
  choose cv hcv using fun i => (hco _ (gfp_tan hx (d i))).exists
  refine finrank_eq_of_existsUnique_comb N cv
    (fun i => (hN _).2 ((heig _ _ (hcv i)).1 ((gfp_eig_iff hx τ _).2 (hdW i)))) fun v hv => ?_
  obtain ⟨w, hw⟩ := (hex v).exists
  have hwt := htan v w hw
  have hb := gfp_basis hx0 hx τ d hd hdW w hwt ((heig v w hw).2 ((hN v).1 hv))
  refine (existsUnique_congr fun a => ?_).1 hb
  rw [hcomb _ cv _ a w hcv]
  exact ⟨fun h => (hco w hwt).unique h hw, fun h => h ▸ hw⟩

end GlobalTheory.Reg
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GenericRegularity.FrameBorelGroupoidPropertiesStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Reg
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.frameBorel_groupoid_properties : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), ∀ (S : Type) [CommRing S] [Algebra c.F S], (∀ y : FrPt Xo c S, FrBor 1 y y) ∧ (∀ (t t' : Ix Dw → Sˣ) (y y' y'' : FrPt Xo c S), FrBor t y y' → FrBor t' y' y'' → FrBor (t * t') y y'') ∧ (∀ (t : Ix Dw → Sˣ) (y y' : FrPt Xo c S), FrBor t y y' → FrBor t⁻¹ y' y) ∧ ∀ (t t' : Ix Dw → Sˣ) (y y' : FrPt Xo c S), FrBor t y y' → FrBor t' y y' → t = t' := by
  first | exact @GlobalTheory.Reg.BorelGroupoid.frBor_groupoid | exact GlobalTheory.Reg.BorelGroupoid.frBor_groupoid | (intros; apply GlobalTheory.Reg.BorelGroupoid.frBor_groupoid <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GenericRegularity.FramedPointIntegralIntegralCellAnyModel
section
noncomputable section

namespace GlobalTheory.Reg

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Reg

theorem tie_integral_of_any_model : ReciprocityTheory.ChartRestriction.G.Out.SecTwistSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), ∀ (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (M : MChart Y), ∀ (T : CDVR) (io : c.F →+* T.Fr) (f₀ : Γ(Y.X, M.U) →+* T.V) (ix : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) ↪ Fin M.n) (u₀ : ∀ τ : E →+* ℂ, Matrix (Fin M.n) (Fin (Dw.mult τ)) T.V), (∀ τ, InCell (ix τ) (u₀ τ)) → letI := io.toAlgebra; ∀ z : FrPt Xo c T.Fr, M.Comparison₂ ((algebraMap T.V T.Fr).comp f₀) (fun τ => (u₀ τ).map (algebraMap T.V T.Fr)) z → Integral T io z := by
  intro hS E _ _ _ H Dw l Xo c O _ β Y M T io f₀ ix u₀ hu
  letI := io.toAlgebra
  intro z ⟨Λ, hL, hT⟩
  obtain ⟨_, _, _, _, _, m, -⟩ := sabPull Out.CubePf.cubePull (spMap f₀ ≫ M.hU.fromSpec) Y.t
  have e : spMap ((algebraMap T.V T.Fr).comp f₀) ≫ M.hU.fromSpec =
      spMap (algebraMap T.V T.Fr) ≫ spMap f₀ ≫ M.hU.fromSpec := by
    rw [← Category.assoc]
    congr 1
    simp only [spMap, ← Spec.map_comp]
    rfl
  have key : ∀ (g : Sp T.Fr ⟶ Y.X) (n : SABMap Λ.t' Y.t g),
      g = spMap (algebraMap T.V T.Fr) ≫ spMap f₀ ≫ M.hU.fromSpec →
      ∃ m2 : SABMap Λ.t' _ (spMap (algebraMap T.V T.Fr)), m2.φ ≫ m.φ = n.φ := by
    intro g n hg
    subst hg
    obtain ⟨m2, h⟩ := sabCancel pullCubCancel E H _ _ _ _ _ _ _ _ m n
    exact ⟨m2, h.symm⟩
  obtain ⟨m2, h2⟩ := key _ Λ.m2 e
  exact ⟨_, Λ.t', Λ.m1, m2,
    tie_vectors_integral E H Dw l Xo c O β Y M T io f₀ ix u₀ hu z Λ hL _ m m2 h2,
    GlobalTheory.T.exists_integralGenerator_chartPoint_noInvert hS E H Dw l Xo c O β Y M T io f₀ z.x z.s Λ hT _ m m2 h2⟩

end GlobalTheory.Reg
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GenericRegularity.IsCombAtIffCoordinateCombinationStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Reg
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isCombAt_iff_coordinate_combination : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), ∀ (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (M : MChart Y), ∀ (R : Type) [CommRing R] [Algebra c.F R] (f : Γ(Y.X, M.U) →+* R) (x : Sp R ⟶ Xo.X) (Λ : M.Lift f x), ∀ (m : ℕ) (cv : Fin m → Fin M.n → R) (w : Fin m → (Sp (DualNumber R) ⟶ Xo.univ.t.G.left)) (a : Fin m → R) (w' : Sp (DualNumber R) ⟶ Xo.univ.t.G.left), (∀ i, Λ.Vec (cv i) (w i)) → (IsCombAt x w a w' ↔ Λ.Vec (∑ i, a i • cv i) w') := by
  first | exact @GlobalTheory.Reg.VecComb.isCombAt_iff_vec | exact GlobalTheory.Reg.VecComb.isCombAt_iff_vec | (intros; apply GlobalTheory.Reg.VecComb.isCombAt_iff_vec <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GenericRegularity.IsCuspFormOfIntegralOverDominantWeightStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Reg
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isCuspForm_of_integral_over_dominantWeight : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), AllTest Xo c → ∀ (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Formalism.L2.PjFree.Unf Xo c σ r), (∀ σ, Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf (U σ)) → ∀ (a : (E →+* ℂ) × ℕ → ℕ) (n N : ℕ) (w : Fin N → Rul Xo c), Dom a n → (∀ i, w i ∈ Formalism.L2.PjFree.cusp Xo c U a n) → ∀ (k m : ℕ) (cf : ℕ → MvPolynomial (Fin N) c.F), 0 < k → (∀ i < m, (cf i).IsHomogeneous ((m - i) * k)) → ∀ g ∈ sec Xo c (k • a) (k * n), g * g ^ m + ∑ i ∈ Finset.range m, (g * MvPolynomial.aeval w (cf i)) * g ^ i = 0 → g ∈ Formalism.L2.PjFree.cusp Xo c U (k • a) (k * n) := by
  first | exact @GlobalTheory.cusp_of_integral_of_dom | exact GlobalTheory.cusp_of_integral_of_dom | (intros; apply GlobalTheory.cusp_of_integral_of_dom <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GenericRegularity.IsTriangularReframeExistsAndUniqueStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Reg
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isTriangularReframe_exists_and_unique : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), ∀ (S : Type) [CommRing S] [Algebra c.F S] (y : FrPt Xo c S), (∀ g : ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) S, (∀ τ, IsUnit (g τ).det) → ∃ y', Reframe g y y') ∧ ∀ y' : FrPt Xo c S, y'.x = y.x → ∃! g : ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) S, (∀ τ, IsUnit (g τ).det) ∧ Reframe g y y' := by
  first | exact @GlobalTheory.Reg.ReframeEx.reframe_exists_unique | exact GlobalTheory.Reg.ReframeEx.reframe_exists_unique | (intros; apply GlobalTheory.Reg.ReframeEx.reframe_exists_unique <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GenericRegularity.KapDivFinStLocDataOf
section
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.FrameNorm GlobalTheory.Reg

namespace GlobalTheory.Reg

theorem kap_divFin_stLoc_dataOf : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), ∀ [Fintype (Comp Xo c)] (h : GenFrEx Xo c) (δ : ∀ Z : Comp Xo c, AddValuation (Om Z) (WithTop ℤ) → Ix Dw → ℤ) (fn : ∀ σ : c.F →+* ℂ, FrPt Xo c (CAt σ) → Ix Dw → ℝ) (yP : ∀ Z : Comp Xo c, ∀ P : Om Z →+* ℂ, FrPt Xo c (CAt (sgOf P))) (Dd N T i g0 : ℕ) (cc : ℝ) (uL uF uka ude uet uta1 uta2 : WtR E) (wR : Fin (N + 1) → Rul Xo c) (jc : Comp Xo c → Fin (N + 1)) (np : ℕ) (thpR : Fin np → Rul Xo c) (n0 : ℕ) (th0R : Fin n0 → Rul Xo c) (uF0 : WtR E) (nk : ℕ) (thkR : Fin nk → Rul Xo c) (MR : Set (Rul Xo c)) (etR ta1R ta2R : Rul Xo c) (nu : HeightOneSpectrum (𝓞 c.F) → ℝ) (ip : (c.F →+* ℂ) → (∀ Z : Comp Xo c, AC Z) → (∀ Z : Comp Xo c, AC Z) → ℂ) (wsize : WTZ E → ℝ) (DF PN PQ tableDegreeThreeBase PP0' Pd Gc PI4 Pet tableLineDegreeFive tableLineDegreeTwo Prw PO f r : ℝ), 1 ≤ Dd → Dd = Dw.dim + Nat.card (FlagVar Dw) → (∀ Z, evC h Z (wR (jc Z)) ≠ 0) → A1Bigness (dataOf h δ fn yP Dd N T i g0 cc uL uF uka ude uet uta1 uta2 wR jc np thpR n0 th0R uF0 nk thkR MR etR ta1R ta2R nu ip wsize DF PN PQ tableDegreeThreeBase PP0' Pd Gc PI4 Pet tableLineDegreeFive tableLineDegreeTwo Prw PO f r) → KapFG Xo c ∧ KapTrdeg Xo c Dw.dim ∧ DivFin (dataOf h δ fn yP Dd N T i g0 cc uL uF uka ude uet uta1 uta2 wR jc np thpR n0 th0R uF0 nk thkR MR etR ta1R ta2R nu ip wsize DF PN PQ tableDegreeThreeBase PP0' Pd Gc PI4 Pet tableLineDegreeFive tableLineDegreeTwo Prw PO f r) ∧ STLoc h Dd N uL wR jc := by
  intro E _ _ _ H Dw l Xo c _ h δ fn yP Dd N T i g0 cc uL uF uka ude uet uta1 uta2 wR jc np thpR n0 th0R uF0 nk thkR MR etR ta1R ta2R nu ip wsize DF PN PQ tableDegreeThreeBase PP0' Pd Gc PI4 Pet tableLineDegreeFive tableLineDegreeTwo Prw PO f r hD hDd hjc hA
  obtain ⟨hfg, htr⟩ := kap_fg_trdeg E H Dw l Xo c
  have hFG : FnFG Xo c := fnFG_of Xo c hfg
  have hTr : FnTrdeg Xo c Dd := hDd ▸ fnTrdeg_of Xo c Dw.dim htr
  have hw : ∀ Z, (dataOf h δ fn yP Dd N T i g0 cc uL uF uka ude uet uta1 uta2 wR jc np thpR n0 th0R uF0 nk thkR MR etR ta1R ta2R nu ip wsize DF PN PQ tableDegreeThreeBase PP0' Pd Gc PI4 Pet tableLineDegreeFive tableLineDegreeTwo Prw PO f r).w ((dataOf h δ fn yP Dd N T i g0 cc uL uF uka ude uet uta1 uta2 wR jc np thpR n0 th0R uF0 nk thkR MR etR ta1R ta2R nu ip wsize DF PN PQ tableDegreeThreeBase PP0' Pd Gc PI4 Pet tableLineDegreeFive tableLineDegreeTwo Prw PO f r).jc Z) Z ≠ 0 := fun Z => valC_ne_zero (hjc Z)
  have hT : ∀ Z, ReciprocityTheory.ChartRestriction.G.AR.Up.TrdegD (dataOf h δ fn yP Dd N T i g0 cc uL uF uka ude uet uta1 uta2 wR jc np thpR n0 th0R uF0 nk thkR MR etR ta1R ta2R nu ip wsize DF PN PQ tableDegreeThreeBase PP0' Pd Gc PI4 Pet tableLineDegreeFive tableLineDegreeTwo Prw PO f r) Z := fun Z =>
    ((GlobalTheory.differentials_iff_trdegD_and_genericSection _ _ _ _ _ (fun _ _ => ⊥) _ Z (hFG Z) (hTr Z) (hw Z)).1).1 (hA Z)
  refine ⟨hfg, htr, ?_, ?_⟩
  · exact divFin_of_trdeg E H Dw l Xo c _ hD hDd (fun Z j => valC_mem h uL.1 uL.2 (wR j) Z) hw hT
  · refine stLoc_of_trdeg E H Dw l Xo c h Dd N uL wR jc hFG hTr hjc (fun Z => ?_)
    have hZ := hT Z
    unfold ReciprocityTheory.ChartRestriction.G.AR.Up.TrdegD at hZ
    have key : (fun j => ReciprocityTheory.ChartRestriction.G.T0.ratio (Ω := Om Z) ((dataOf h δ fn yP Dd N T i g0 cc uL uF uka ude uet uta1 uta2 wR jc np thpR n0 th0R uF0 nk thkR MR etR ta1R ta2R nu ip wsize DF PN PQ tableDegreeThreeBase PP0' Pd Gc PI4 Pet tableLineDegreeFive tableLineDegreeTwo Prw PO f r).w j Z) ((dataOf h δ fn yP Dd N T i g0 cc uL uF uka ude uet uta1 uta2 wR jc np thpR n0 th0R uF0 nk thkR MR etR ta1R ta2R nu ip wsize DF PN PQ tableDegreeThreeBase PP0' Pd Gc PI4 Pet tableLineDegreeFive tableLineDegreeTwo Prw PO f r).w ((dataOf h δ fn yP Dd N T i g0 cc uL uF uka ude uet uta1 uta2 wR jc np thpR n0 th0R uF0 nk thkR MR etR ta1R ta2R nu ip wsize DF PN PQ tableDegreeThreeBase PP0' Pd Gc PI4 Pet tableLineDegreeFive tableLineDegreeTwo Prw PO f r).jc Z) Z)) =
        fun j => evC h Z (wR j) / evC h Z (wR (jc Z)) := by
      funext j
      refine ReciprocityTheory.ChartRestriction.G.T0.ValuationResidueLemmas.ratio_eq (valC_ne_zero (hjc Z)) ?_
      unfold dataOf valG valC
      simp [div_mul_cancel₀ _ (hjc Z)]
    rw [key] at hZ
    exact hZ

end GlobalTheory.Reg
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GenericRegularity.NumericalConsequencesOfPinsStatement
section
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.numerical_consequences_of_pins : ∀ (D : D7) (Q : Par D), Q.Pins → (∀ p : ℕ, p.Prime → Q.l.GoodAt p) ∧ Q.l.A = 1 ∧ Q.l.M' = Q.l.M ∧ 0 < xiR D ∧ xiR D ≤ 1 ∧ Module.finrank ℚ D.host.E = 2 * D.R.f ∧ ∀ j, InR D j → (Q.Dw j).p + (Q.Dw j).q = D.R.r ∧ 1 ≤ D.R.r ∧ (Q.Dw j).dim + Nat.card (FlagVar (Q.Dw j)) = WeightFamilies.dimY D j := by
  first | exact @GlobalTheory.PinNum.numerics_of_pins | exact GlobalTheory.PinNum.numerics_of_pins | (intros; apply GlobalTheory.PinNum.numerics_of_pins <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GenericRegularity.TriangularReframeCompBaseChangeBorelStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Reg
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.triangularReframe_comp_baseChange_borel : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), ∀ (S : Type) [CommRing S] [Algebra c.F S], (∀ (g g' : ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) S) (y y' y'' : FrPt Xo c S), Reframe g y y' → Reframe g' y' y'' → Reframe (fun τ => g τ * g' τ) y y'') ∧ (∀ (T : Type) [CommRing T] [Algebra c.F T] (φ : S →ₐ[c.F] T) (g : ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) S) (y y' : FrPt Xo c S) (z z' : FrPt Xo c T), Reframe g y y' → FrMap φ y z → FrMap φ y' z' → Reframe (fun τ => (g τ).map φ) z z') ∧ ∀ y y' : FrPt Xo c S, (∃ t : Ix Dw → Sˣ, FrBor t y y') ↔ ∃ b : ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) S, (∀ τ, (b τ).BlockTriangular id ∧ ∀ i, IsUnit (b τ i i)) ∧ Reframe b y y' := by
  first | exact @GlobalTheory.Reg.reframe_calculus | exact GlobalTheory.Reg.reframe_calculus | (intros; apply GlobalTheory.Reg.reframe_calculus <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GenericRegularity.ValuesEqOfCommonPoint
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Reg

namespace GlobalTheory.Reg.ChartCompat

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l}

def liftF {S : Type} [CommRing S] [Algebra c.F S] (y : FrPt Xo c S) : Sp S ⟶ Xo.XF c :=
  pullback.lift y.x (spMap (algebraMap c.F S)) (by
    rw [y.x_over, spMap_comp_ring]; rfl)

theorem liftF_fst {S : Type} [CommRing S] [Algebra c.F S] (y : FrPt Xo c S) :
    liftF y ≫ pullback.fst _ _ = y.x := pullback.lift_fst _ _ _

theorem liftF_snd {S : Type} [CommRing S] [Algebra c.F S] (y : FrPt Xo c S) :
    liftF y ≫ pullback.snd _ _ = spMap (algebraMap c.F S) := pullback.lift_snd _ _ _

theorem liftF_map {S T : Type} [CommRing S] [Algebra c.F S] [CommRing T] [Algebra c.F T] {φ : S →ₐ[c.F] T}
    {y : FrPt Xo c S} {z : FrPt Xo c T} (h : FrMap φ y z) : liftF z = spMap φ.toRingHom ≫ liftF y := by
  apply pullback.hom_ext
  · rw [Category.assoc, liftF_fst, liftF_fst, h.1]
  · rw [Category.assoc, liftF_snd, liftF_snd, spMap_comp_ring]
    congr 1
    ext a
    simp

theorem liftF_bor {S : Type} [CommRing S] [Algebra c.F S] {t : Ix Dw → Sˣ}
    {y z : FrPt Xo c S} (h : FrBor t y z) : liftF z = liftF y := by
  apply pullback.hom_ext
  · rw [liftF_fst, liftF_fst, h.1]
  · rw [liftF_snd, liftF_snd]

theorem liftF_gen (h : GenFrEx Xo c) (Z : Comp Xo c) :
    liftF (genFr h Z) = spMap (algebraMap (kap Z) (Om Z)) ≫ genSp Z := by
  apply pullback.hom_ext
  · rw [Category.assoc, liftF_fst, (isGenFr_genFr h Z).1]; rfl
  · rw [Category.assoc, liftF_snd, IsScalarTower.algebraMap_eq c.F (kap Z) (Om Z), ← spMap_comp_ring]
    congr 1
    exact Spec.map_preimage (genSp Z ≫ strK)

theorem liftF_gen_apply (h : GenFrEx Xo c) (Z : Comp Xo c) (p : Sp (Om Z)) :
    (liftF (genFr h Z)) p = genPt Z := by
  rw [liftF_gen, Scheme.Hom.comp_apply]
  exact Scheme.fromSpecResidueField_apply _ _

theorem closure_genPt' (Z : Comp Xo c) : closure {genPt Z} = (Z : Set (Xo.XF c)) :=
  (IsIrreducible.genericPoint_closure_eq (Z.2.1 : IsIrreducible (Z : Set (Xo.XF c)))).trans
    (isClosed_of_mem_irreducibleComponents _ Z.2).closure_eq

theorem chart_mem {h : GenFrEx Xo c} (C : FChart h) (p : Sp C.R) : (liftF C.y) p ∈ (C.Z : Set (Xo.XF c)) := by
  have hcl : IsClosed ((liftF C.y) ⁻¹' (C.Z : Set (Xo.XF c))) :=
    (isClosed_of_mem_irreducibleComponents _ C.Z.2).preimage (liftF C.y).continuous
  let q : Sp (Om C.Z) := (⊥ : PrimeSpectrum (Om C.Z))
  have h1 : (liftF C.y) (spMap C.R.val.toRingHom q) = genPt C.Z := by
    rw [← Scheme.Hom.comp_apply, ← liftF_map C.gen, liftF_bor C.bor, liftF_gen_apply]
  have h2 : spMap C.R.val.toRingHom q ∈ (liftF C.y) ⁻¹' (C.Z : Set (Xo.XF c)) := by
    show (liftF C.y) (spMap C.R.val.toRingHom q) ∈ (C.Z : Set (Xo.XF c))
    rw [h1, ← closure_genPt']
    exact subset_closure rfl
  have h3 : spMap C.R.val.toRingHom q ⤳ p := by
    refine (PrimeSpectrum.le_iff_specializes _ _).1 ?_
    intro a ha
    have ha' : C.R.val a = 0 := ha
    have : a = 0 := Subtype.ext ha'
    rw [this]
    exact Ideal.zero_mem _
  exact h3.mem_closed hcl h2

theorem comp_eq {h : GenFrEx Xo c} (C C' : FChart h) (ψ : C'.R →ₐ[c.F] Om C.Z) (z : FrPt Xo c (Om C.Z))
    (t : Ix Dw → (Om C.Z)ˣ) (hz : FrMap ψ C'.y z) (hb : FrBor t z C.yg) : C.Z = C'.Z := by
  let q : Sp (Om C.Z) := (⊥ : PrimeSpectrum (Om C.Z))
  have h1 : genPt C.Z ∈ (C'.Z : Set (Xo.XF c)) := by
    rw [← liftF_gen_apply h C.Z q, ← liftF_bor C.bor, liftF_bor hb, liftF_map hz, Scheme.Hom.comp_apply]
    exact chart_mem C' _
  have h2 : (C.Z : Set (Xo.XF c)) ⊆ (C'.Z : Set (Xo.XF c)) := by
    rw [← closure_genPt']
    exact closure_minimal (Set.singleton_subset_iff.2 h1) (isClosed_of_mem_irreducibleComponents _ C'.Z.2)
  exact Subtype.ext (Set.Subset.antisymm h2 (C.Z.2.2 C'.Z.2.1 h2))

theorem wchar_mul {J S : Type} [Fintype J] [CommRing S] (e : J → ℕ) (t t' : J → Sˣ) :
    wchar e (t * t') = wchar e t * wchar e t' := by
  simp [wchar, mul_pow, Finset.prod_mul_distrib]

theorem wchar_map {J K S T : Type} [Fintype J] [Field K] [CommRing S] [CommRing T] [Algebra K S] [Algebra K T]
    (φ : S →ₐ[K] T) (e : J → ℕ) (t : J → Sˣ) :
    wchar e (fun i => Units.map (φ : S →* T) (t i)) = φ (wchar e t) := by
  simp [wchar]

theorem away_lift {K R T : Type} [Field K] [CommRing R] [Algebra K R] [Field T] [Algebra K T] (g : R)
    (φ : R →ₐ[K] T) (hφ : φ g ≠ 0) :
    ∃ m : Localization.Away g →ₐ[K] T, m.comp (IsScalarTower.toAlgHom K R (Localization.Away g)) = φ := by
  have hu : ∀ m : Submonoid.powers g, IsUnit (φ m) := by
    rintro ⟨_, n, rfl⟩
    simpa using Ne.isUnit (pow_ne_zero n hφ)
  refine ⟨IsLocalization.liftAlgHom (M := Submonoid.powers g) hu, ?_⟩
  ext a
  simp

theorem away_inj {K R T : Type} [Field K] [CommRing R] [Algebra K R] [CommRing T] [Algebra K T] (g : R)
    (m : Localization.Away g →ₐ[K] T)
    (h : Function.Injective (m.comp (IsScalarTower.toAlgHom K R (Localization.Away g)))) : Function.Injective m := by
  rw [injective_iff_map_eq_zero]
  intro s hs
  obtain ⟨⟨a, n⟩, hm⟩ := IsLocalization.surj (Submonoid.powers g) s
  have h1 : m (algebraMap R _ a) = 0 := by
    rw [← hm, map_mul, hs, zero_mul]
  have h3 : a = 0 := (injective_iff_map_eq_zero _).1 h a h1
  dsimp only at hm
  rw [h3, map_zero] at hm
  exact (IsLocalization.map_units _ n).mul_left_eq_zero.1 hm

end GlobalTheory.Reg.ChartCompat

namespace GlobalTheory.Reg
open ChartCompat

set_option maxHeartbeats 1000000 in
theorem FChart.compat : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), EvLaws Xo c → ∀ h : GenFrEx Xo c, ∀ (C C' : FChart h) (L : Type) [Field L] [Algebra c.F L] (ψ : C.R →ₐ[c.F] L) (ψ' : C'.R →ₐ[c.F] L) (z z' : FrPt Xo c L) (t : Ix Dw → Lˣ), FrMap ψ C.y z → FrMap ψ' C'.y z' → FrBor t z z' → C.Z = C'.Z ∧ ∀ (e : Ix Dw → ℕ) (b : ∀ Z : Comp Xo c, Om Z) (hb : wchar e C.t * b C.Z ∈ C.R) (hb' : wchar e C'.t * b C'.Z ∈ C'.R), ψ' ⟨_, hb'⟩ = wchar e t * ψ ⟨_, hb⟩ := by
  intro E _ _ _ H Dw l Xo c hev h C C' L _ _ ψ ψ' z z' t hz hz' hbor
  have G := GlobalTheory.Reg.BorelGroupoid.frBor_groupoid E H Dw l Xo c
  have U := GlobalTheory.Frames.frMap_unique_refl_iff E H Dw l Xo c
  obtain ⟨g, hg, hopn⟩ := C'.opn C.R L ψ C.y z hz ⟨ψ', z', t⁻¹, hz', (G L).2.2.1 t z z' hbor⟩
  have hg0 : g ≠ 0 := fun e => hg (by rw [e, map_zero])
  have hg1 : C.R.val g ≠ 0 := fun e => hg0 (Subtype.ext e)
  have hZ : C.Z = C'.Z := by
    obtain ⟨ψ0, z0, t0, h1, h2⟩ := hopn (Om C.Z) C.R.val (Ne.isUnit hg1) C.yg C.gen
    exact comp_eq C C' ψ0 z0 t0 h1 h2
  refine ⟨hZ, ?_⟩
  obtain ⟨Z, R, sm, frac, y, yg, tC, gen, bor, mono, opn⟩ := C
  obtain ⟨Z', R', sm', frac', y', yg', tC', gen', bor', mono', opn'⟩ := C'
  dsimp only at *
  subst hZ
  intro e b hb hb'
  let S := Localization.Away g
  let lam : R →ₐ[c.F] S := IsScalarTower.toAlgHom c.F R S
  have hlam : IsUnit (lam g) := IsLocalization.Away.algebraMap_isUnit g
  obtain ⟨mu, hmu⟩ : ∃ m : S →ₐ[c.F] Om Z, m.comp lam = R.val := away_lift g R.val hg1
  obtain ⟨nu, hnu⟩ : ∃ m : S →ₐ[c.F] L, m.comp lam = ψ := away_lift g ψ hg
  have hinj : Function.Injective mu := away_inj g mu (by rw [hmu]; exact Subtype.val_injective)
  obtain ⟨w, hw⟩ := hev.bc R S lam y
  obtain ⟨φ, v, s, hv, hs⟩ := hopn S lam hlam w hw

  obtain ⟨vmu, hvmu⟩ := hev.bc S (Om Z) mu v
  have m1 : FrMap mu w yg := frMap_cancel _ _ _ lam mu y w yg hw (by rw [hmu]; exact gen)
  have b1 := frBorBC _ _ mu s v w vmu yg hs hvmu m1
  have m2 : FrMap (mu.comp φ) y' vmu := frMap_trans _ _ _ φ mu y' v vmu hv hvmu
  have b2 := (G _).2.1 _ _ _ _ _ b1 ((G _).2.1 _ _ _ _ _ ((G _).2.2.1 _ _ _ bor) bor')
  have e1 : mu.comp φ = R'.val := mono' _ _ _ _ _ _ m2 gen' b2
  have e2 : vmu = yg' := (U _ _ R'.val y').1 _ _ (e1 ▸ m2) gen'
  subst e2
  have e3 : tC = tC' * fun i => Units.map (mu : S →* Om Z) (s i) :=
    (G _).2.2.2 _ _ _ _ bor ((G _).2.1 _ _ _ _ _ bor' b1)

  obtain ⟨vnu, hvnu⟩ := hev.bc S L nu v
  have m3 : FrMap nu w z := frMap_cancel _ _ _ lam nu y w z hw (by rw [hnu]; exact hz)
  have b3 := frBorBC _ _ nu s v w vnu z hs hvnu m3
  have m4 : FrMap (nu.comp φ) y' vnu := frMap_trans _ _ _ φ nu y' v vnu hv hvnu
  have b4 := (G _).2.1 _ _ _ _ _ b3 hbor
  have e4 : nu.comp φ = ψ' := mono' _ _ _ _ _ _ m4 hz' b4
  have e5 : vnu = z' := (U _ _ ψ' y').1 _ _ (e4 ▸ m4) hz'
  subst e5
  have e6 : (fun i => Units.map (nu : S →* L) (s i)) * t = 1 :=
    (G _).2.2.2 _ _ _ _ b4 ((G _).1 _)
  have e7 : lam ⟨_, hb⟩ = wchar e s * φ ⟨_, hb'⟩ := by
    apply hinj
    have a1 : mu (lam ⟨_, hb⟩) = wchar e tC * b Z := DFunLike.congr_fun hmu ⟨_, hb⟩
    have a2 : mu (φ ⟨_, hb'⟩) = wchar e tC' * b Z := DFunLike.congr_fun e1 ⟨_, hb'⟩
    have a0 : wchar e tC = wchar e tC' * mu (wchar e s) :=
      (congrArg (wchar e) e3).trans ((wchar_mul _ _ _).trans (congrArg _ (wchar_map mu e s)))
    rw [map_mul, a1, a2]
    linear_combination (b Z) * a0
  have a3 : ψ ⟨_, hb⟩ = nu (wchar e s) * ψ' ⟨_, hb'⟩ := by
    rw [← hnu, ← e4, AlgHom.comp_apply, AlgHom.comp_apply, e7, map_mul]
  have a4 : nu (wchar e s) * wchar e t = 1 := by
    rw [← wchar_map, ← wchar_mul, e6]
    simp [wchar]
  linear_combination (-(wchar e t)) * a3 - (ψ' ⟨_, hb'⟩) * a4

end GlobalTheory.Reg
end
end

