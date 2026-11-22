import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0096
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.FBIdSy
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ThetaSwapFirstTwo
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.FrRatio
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0140
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.EmbedsGeneric
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.GoodOrigin
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0131
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.BdryChart
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsFlatAnIffIsConstMul
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0005
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Bundle0004
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
import Development.AutomorphicSpectrum.PublishedTheorems.Geometry₂.GagaSections
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0004
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0034
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0031
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.Bundle0007
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0139
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0014
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle0059
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0141
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
import Development.AutomorphicSpectrum.Statements.GeometryStatements.Bundle0009
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.AddJFintype
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.GlueApplyOfNotInFibre
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0010
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0142
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.CoordsCompatibleAlongMap
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsPeriodAtRestrict
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.PotentialsBoundedRegSettingEqReference
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0023

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.AdjointRelationGeneratorCorr
section
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Flat.FrGauge.WAxis

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Conj Formalism.L2.Pj
open Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.GermD Formalism.MainNotions.ModuliIntegralCharts.H1.GermFun Formalism.MainNotions.ModuliIntegralCharts.H1.FBIdSy Formalism.MainNotions.ModuliIntegralCharts.H1.FBIdJet
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS Pt ev pt comp1)
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

section Alg

variable {S : Type} [CommRing S] {d : ℕ}

theorem aeval_psIn_zero (m : ℕ) (i : Fin 2) (ψ : Fin 2 × Fin d → MvPolynomial (Fin 1 × Fin d) S)
    (h : ∀ l, ψ (i, l) = 0) (f : PS S 1 d) (hf : MvPowerSeries.constantCoeff f = 0) :
    MvPolynomial.aeval ψ (psIn d m ![i] f) = 0 := by
  have e : (ψ ∘ fun p : Fin 1 × Fin d => ((![i] : Fin 1 → Fin 2) p.1, p.2)) = 0 := by
    funext p
    obtain ⟨k, l⟩ := p
    simpa using h l
  rw [psIn, MvPolynomial.aeval_rename, e, MvPolynomial.aeval_zero, FBIdPh.cc_psTrunc, hf, map_zero]

theorem aeval_psIn_X (m : ℕ) (i : Fin 2) (ψ : Fin 2 × Fin d → MvPolynomial (Fin 1 × Fin d) S)
    (h : ∀ l, ψ (i, l) = MvPolynomial.X ((0 : Fin 1), l)) (f : PS S 1 d) :
    MvPolynomial.aeval ψ (psIn d m ![i] f) = psTrunc m f := by
  have e : (ψ ∘ fun p : Fin 1 × Fin d => ((![i] : Fin 1 → Fin 2) p.1, p.2)) = MvPolynomial.X := by
    funext p
    obtain ⟨k, l⟩ := p
    have hk : k = 0 := Subsingleton.elim _ _
    subst hk
    simpa using h l
  rw [psIn, MvPolynomial.aeval_rename, e, MvPolynomial.aeval_X_left_apply]

abbrev axP (d : ℕ) (S : Type) [CommRing S] (b : Bool) : Fin 2 × Fin d → MvPolynomial (Fin 1 × Fin d) S :=
  fun p => (if b then ![fun _ => 0, fun j => MvPolynomial.X ((0 : Fin 1), j)]
    else ![fun j => MvPolynomial.X ((0 : Fin 1), j), fun _ => 0] :
      Fin 2 → Fin d → MvPolynomial (Fin 1 × Fin d) S) p.1 p.2

theorem constantCoeff₂ (b : Bool) (p : Fin 2 × Fin d) : MvPolynomial.constantCoeff (axP d S b p) = 0 := by
  obtain ⟨k, j⟩ := p
  cases b <;> fin_cases k <;> simp [axP]

abbrev fstP (f : Fin d → PS S 1 d) (m : ℕ) : Fin 2 × Fin d → MvPolynomial (Fin 2 × Fin d) S :=
  fun p => (![fun j => psIn d m ![0] (f j), fun j => MvPolynomial.X ((1 : Fin 2), j)] :
    Fin 2 → Fin d → MvPolynomial (Fin 2 × Fin d) S) p.1 p.2

abbrev sndP (f : Fin d → PS S 1 d) (m : ℕ) : Fin 2 × Fin d → MvPolynomial (Fin 2 × Fin d) S :=
  fun p => (![fun j => MvPolynomial.X ((0 : Fin 2), j), fun j => psIn d m ![1] (f j)] :
    Fin 2 → Fin d → MvPolynomial (Fin 2 × Fin d) S) p.1 p.2

abbrev actJ (f : Fin d → PS S 1 d) (m : ℕ) : Jet S (Fin 1 × Fin d) m →ₐ[S] Jet S (Fin 1 × Fin d) m :=
  jetSubstP m fun p : Fin 1 × Fin d => psTrunc m (f p.2)

theorem fstP_cc (f : Fin d → PS S 1 d) (hf : ∀ j, MvPowerSeries.constantCoeff (f j) = 0) (m : ℕ)
    (p : Fin 2 × Fin d) : MvPolynomial.constantCoeff (fstP f m p) = 0 := by
  obtain ⟨k, j⟩ := p
  fin_cases k
  · simpa [fstP] using (FBIdPh.cc_psIn d m ![0] (f j)).trans (hf j)
  · simp [fstP]

theorem sndP_cc (f : Fin d → PS S 1 d) (hf : ∀ j, MvPowerSeries.constantCoeff (f j) = 0) (m : ℕ)
    (p : Fin 2 × Fin d) : MvPolynomial.constantCoeff (sndP f m p) = 0 := by
  obtain ⟨k, j⟩ := p
  fin_cases k
  · simp [sndP]
  · simpa [sndP] using (FBIdPh.cc_psIn d m ![1] (f j)).trans (hf j)

theorem trunc_cc (f : Fin d → PS S 1 d) (hf : ∀ j, MvPowerSeries.constantCoeff (f j) = 0) (m : ℕ)
    (p : Fin 1 × Fin d) : MvPolynomial.constantCoeff (psTrunc m (f p.2)) = 0 :=
  (FBIdPh.cc_psTrunc m _).trans (hf _)

theorem ax_fst_true (f : Fin d → PS S 1 d) (hf : ∀ j, MvPowerSeries.constantCoeff (f j) = 0) (m : ℕ) :
    (axJ (S := S) d m true).comp (jetSubstP m (fstP f m)) = axJ d m true := by
  refine (FBIdPh.jetSubstP_comp m (fstP f m) (axP d S true) (fstP_cc f hf m) (constantCoeff₂ true)).trans ?_
  congr 1
  funext p
  obtain ⟨k, j⟩ := p
  fin_cases k
  · exact aeval_psIn_zero m 0 _ (fun _ => rfl) _ (hf j)
  · simp [fstP, axP]

theorem ax_snd_true (f : Fin d → PS S 1 d) (hf : ∀ j, MvPowerSeries.constantCoeff (f j) = 0) (m : ℕ) :
    (axJ (S := S) d m true).comp (jetSubstP m (sndP f m)) = (actJ f m).comp (axJ d m true) := by
  refine (FBIdPh.jetSubstP_comp m (sndP f m) (axP d S true) (sndP_cc f hf m) (constantCoeff₂ true)).trans ?_
  refine Eq.trans ?_ (FBIdPh.jetSubstP_comp m (axP d S true) _ (constantCoeff₂ true) (trunc_cc f hf m)).symm
  congr 1
  funext p
  obtain ⟨k, j⟩ := p
  fin_cases k
  · simp [sndP, axP]
  · refine (aeval_psIn_X m 1 _ (fun _ => rfl) _).trans ?_
    simp [axP]

theorem ax_fst_false (f : Fin d → PS S 1 d) (hf : ∀ j, MvPowerSeries.constantCoeff (f j) = 0) (m : ℕ) :
    (axJ (S := S) d m false).comp (jetSubstP m (fstP f m)) = (actJ f m).comp (axJ d m false) := by
  refine (FBIdPh.jetSubstP_comp m (fstP f m) (axP d S false) (fstP_cc f hf m) (constantCoeff₂ false)).trans ?_
  refine Eq.trans ?_ (FBIdPh.jetSubstP_comp m (axP d S false) _ (constantCoeff₂ false) (trunc_cc f hf m)).symm
  congr 1
  funext p
  obtain ⟨k, j⟩ := p
  fin_cases k
  · refine (aeval_psIn_X m 0 _ (fun _ => rfl) _).trans ?_
    simp [axP]
  · simp [fstP, axP]

theorem ax_snd_false (f : Fin d → PS S 1 d) (hf : ∀ j, MvPowerSeries.constantCoeff (f j) = 0) (m : ℕ) :
    (axJ (S := S) d m false).comp (jetSubstP m (sndP f m)) = axJ d m false := by
  refine (FBIdPh.jetSubstP_comp m (sndP f m) (axP d S false) (sndP_cc f hf m) (constantCoeff₂ false)).trans ?_
  congr 1
  funext p
  obtain ⟨k, j⟩ := p
  fin_cases k
  · simp [sndP, axP]
  · exact aeval_psIn_zero m 1 _ (fun _ => rfl) _ (hf j)

theorem ax_copy_zero (m : ℕ) (b : Bool) (i : Fin 2) (hi : (i = 1) ≠ b) :
    (axJ (S := S) d m b).comp (jetCopy d m i) =
      (Algebra.ofId S (Jet S (Fin 1 × Fin d) m)).comp jetAug := by
  refine jet_hom_ext fun p => ?_
  obtain ⟨k, j⟩ := p
  have h0 : (jetAug : Jet S (Fin 1 × Fin d) m →ₐ[S] S) (Ideal.Quotient.mk _ (MvPolynomial.X (k, j))) = 0 := by
    simp [jetAug, liftJet]
  rw [AlgHom.comp_apply, AlgHom.comp_apply, h0, map_zero, jetCopy, jetMap_mk, MvPolynomial.aeval_X, axJ_X]
  simp [axV, hi]

theorem ax_copy_id (m : ℕ) (b : Bool) (i : Fin 2) (hi : (i = 1) = b) :
    (axJ (S := S) d m b).comp (jetCopy d m i) = AlgHom.id S _ := by
  refine jet_hom_ext fun p => ?_
  obtain ⟨k, j⟩ := p
  have hk : k = 0 := Subsingleton.elim _ _
  subst hk
  rw [AlgHom.comp_apply, jetCopy, jetMap_mk, MvPolynomial.aeval_X, axJ_X, AlgHom.id_apply]
  simp [axV, hi]

end Alg

section Frame

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X0 : Scheme.{0}} (t : SAB H X0)
  {S : Type} [CommRing S] (x0 : Sp S ⟶ X0) (d : ℕ) (x : ∀ m, jOG x0 d m 1 ⟶ t.G)

theorem pt_killed (hz : ∀ m, homAt x0 (jetAug : Jet S (Fin 1 × Fin d) m →ₐ[S] S) ≫ x m = 1) (m : ℕ) (b : Bool)
    (i : Fin 2) (hi : (i = 1) ≠ b) : homAt x0 (axJ (S := S) d m b) ≫ jptG t x0 d x m i = 1 := by
  rw [jptG, ← Category.assoc, homAt_comp, ax_copy_zero m b i hi, ← homAt_comp, Category.assoc, hz m]
  exact MonObj.comp_one _

theorem pt_kept (m : ℕ) (b : Bool) (i : Fin 2) (hi : (i = 1) = b) :
    homAt x0 (axJ (S := S) d m b) ≫ jptG t x0 d x m i = x m := by
  rw [jptG, ← Category.assoc, homAt_comp, ax_copy_id m b i hi, homAt_id, Category.id_comp]

theorem val_axis (act : 𝓞 E → Fin d → MvPowerSeries (Fin 1 × Fin d) S) (ad : 𝓞 E → MvPowerSeries (Fin 2 × Fin d) S)
    (e : ∀ m, FrTyG t x0 d x m) (hax : FrAxes t x0 d x e) (a : 𝓞 E) (wL : FrGauge.AdTy t a)
    (hrel : FrGauge.AdRel t x0 d x act ad e a wL) (m : ℕ) (b : Bool)
    (hb : ev (n := 1) (if b then ![0, pt S d 0] else ![pt S d 0, 0]) (ad a) = 1)
    (r₁ r₂ : (jOG x0 d m 1).left ⟶ (jOG x0 d m 1).left)
    (h₁ : (homAt x0 (axJ (S := S) d m b)).left ≫ (homAt x0 (jetSubstP m (fstP (act a) m))).left =
      r₁ ≫ (homAt x0 (axJ (S := S) d m b)).left)
    (h₂ : (homAt x0 (axJ (S := S) d m b)).left ≫ (homAt x0 (jetSubstP m (sndP (act (H.bar a)) m))).left =
      r₂ ≫ (homAt x0 (axJ (S := S) d m b)).left)
    (y : (jOG x0 d m 1).left) (J : ((jOG x0 d m 1).left ⟶ t.G.left) → t.PP.L.ι) (hJ : Good t.PP.L y J) :
    val wL ((homAt x0 (axJ (S := S) d m b)).left ≫
      (lift (jptG t x0 d x m (0 : Fin 2)) (jptG t x0 d x m (1 : Fin 2))).left) y J = 1 := by
  obtain ⟨u, hu, hc⟩ := hrel m
  have hA : LB.Gen.Corr t.PP.L _ _ _ _
      (LB.pullGen t.PP.L (cφG t ![jptG t x0 d x m (0 : Fin 2), jptG t x0 d x m (1 : Fin 2)]) (cε 2) (e m)
        (homAt x0 (axJ (S := S) d m b)).left) (LB.oneGen t.PP.L) := by
    cases b
    · exact (hax m).2
    · exact (hax m).1
  have hv : ∀ r : (jOG x0 d m 1).left ⟶ (jOG x0 d m 1).left,
      val (e m) (r ≫ (homAt x0 (axJ (S := S) d m b)).left) y J = 1 := fun r =>
    (val_pull hJ _ _ _).symm.trans ((val_corr hJ hA r).trans (val_one _))
  have E := val_corr hJ hc (homAt x0 (axJ (S := S) d m b)).left
  rw [val_mul hJ, val_pull hJ, GermB.val_scale t _ _ _ _ _ y J hJ] at E
  have p₁ : val (peG t x0 d x e m ![fun j => psIn d m ![0] (act a j), fun j => MvPolynomial.X ((1 : Fin 2), j)])
      (homAt x0 (axJ (S := S) d m b)).left y J = 1 :=
    (val_pull hJ _ _ _).trans ((congrArg (fun r => val (e m) r y J) h₁).trans (hv r₁))
  have p₂ : val (peG t x0 d x e m ![fun j => MvPolynomial.X ((0 : Fin 2), j), fun j => psIn d m ![1] (act (H.bar a) j)])
      (homAt x0 (axJ (S := S) d m b)).left y J = 1 :=
    (val_pull hJ _ _ _).trans ((congrArg (fun r => val (e m) r y J) h₂).trans (hv r₂))
  have hU : Units.map ((axJ (S := S) d m b : _ →ₐ[S] _) : Jet S (Fin 2 × Fin d) m →* Jet S (Fin 1 × Fin d) m) u = 1 :=
    Units.ext (by
      rw [Units.coe_map, hu]
      exact (psJet_ev_ax d m (ad a) b).symm.trans ((congrArg (psJet m) hb).trans (psJet_one m)))
  have p₃ : gm (homAt x0 (axJ (S := S) d m b)).left y ⊤ (unitΓ u) = 1 := by
    rw [FrRatio.gm_map, hU, unitΓ_one, map_one]
  rw [p₁, p₂, p₃, _root_.mul_one, _root_.mul_one] at E
  exact E

theorem lift_true (hz : ∀ m, homAt x0 (jetAug : Jet S (Fin 1 × Fin d) m →ₐ[S] S) ≫ x m = 1) (m : ℕ) :
    (homAt x0 (axJ (S := S) d m true)).left ≫
        (lift (jptG t x0 d x m (0 : Fin 2)) (jptG t x0 d x m (1 : Fin 2))).left =
      (lift (1 : jOG x0 d m 1 ⟶ t.G) (x m)).left := by
  rw [← Over.comp_left, comp_lift, pt_killed t x0 d x hz m true 0 (by simp),
    pt_kept t x0 d x m true 1 (by simp)]

theorem lift_false (hz : ∀ m, homAt x0 (jetAug : Jet S (Fin 1 × Fin d) m →ₐ[S] S) ≫ x m = 1) (m : ℕ) :
    (homAt x0 (axJ (S := S) d m false)).left ≫
        (lift (jptG t x0 d x m (0 : Fin 2)) (jptG t x0 d x m (1 : Fin 2))).left =
      (lift (x m) (1 : jOG x0 d m 1 ⟶ t.G)).left := by
  rw [← Over.comp_left, comp_lift, pt_kept t x0 d x m false 0 (by simp),
    pt_killed t x0 d x hz m false 1 (by simp)]

end Frame

theorem adAxes : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)],
    (∀ a : 𝓞 E, star a = H.bar a) → ∀ (X : Scheme.{0}) (t : SAB H X) (S : Type) [CommRing S] (x : Sp S ⟶ X) (d : ℕ)
    (g : GermAt t x d) (a : 𝓞 E) (wL : FrGauge.AdTy t a), wL.IsGen →
    FrGauge.AdRel t x d g.x g.B.A.act g.B.ad g.e a wL → ∀ m,
    LB.Gen.Corr t.PP.L _ _ _ _ (LB.pullGen t.PP.L _ _ wL (lift (1 : jOG x d m 1 ⟶ t.G) (g.x m)).left)
      (LB.oneGen t.PP.L) ∧
    LB.Gen.Corr t.PP.L _ _ _ _ (LB.pullGen t.PP.L _ _ wL (lift (g.x m) (1 : jOG x d m 1 ⟶ t.G)).left)
      (LB.oneGen t.PP.L) := by
  intro E _ _ _ H _ _ X t S _ x d g a wL _ hrel m
  have hL := t.PP.isLB
  have hc : ∀ c j, MvPowerSeries.constantCoeff (g.B.A.act c j) = 0 := g.B.A.const
  refine ⟨corr_of_val hL fun y J hJ => ?_, corr_of_val hL fun y J hJ => ?_⟩
  · rw [val_pull hJ, val_one, Category.id_comp, ← lift_true t x d g.x g.chart.zero m]
    refine val_axis t x d g.x g.B.A.act g.B.ad g.e g.axes a wL hrel m true (g.B.adjoint_zero_fst a) (𝟙 _)
      (homAt x (actJ (g.B.A.act (H.bar a)) m)).left ?_ ?_ y J hJ
    · rw [← Over.comp_left, homAt_comp, ax_fst_true _ (hc a) m, Category.id_comp]
    · rw [← Over.comp_left, homAt_comp, ax_snd_true _ (hc _) m, ← homAt_comp, Over.comp_left]
  · rw [val_pull hJ, val_one, Category.id_comp, ← lift_false t x d g.x g.chart.zero m]
    refine val_axis t x d g.x g.B.A.act g.B.ad g.e g.axes a wL hrel m false (g.B.adjoint_zero_snd a)
      (homAt x (actJ (g.B.A.act a) m)).left (𝟙 _) ?_ ?_ y J hJ
    · rw [← Over.comp_left, homAt_comp, ax_fst_false _ (hc _) m, ← homAt_comp, Over.comp_left]
    · rw [← Over.comp_left, homAt_comp, ax_snd_false _ (hc _) m, Category.id_comp]

end GlobalTheory.CompanionTheory.Ar.Flat.FrGauge.WAxis
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.AmpleOfSingleCoordBlockStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ample_of_single_coord_block : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] [CharZero Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (k₀ : K) (a : K → ℤ), CoordTie ℤ ξ (fun c' : (k : K) → J k => ∏ k, y ⟨k, c' k⟩) → EmbedsGeneric ξ (fun i : J k₀ => y ⟨k₀, i⟩) → a k₀ = 1 → (∀ k, k ≠ k₀ → a k = 0) → Ht.AmpleQ y a := by
  first | exact @GlobalTheory.CompanionTheory.Ar.AmpleBlock.ampleQ_of_embeds | exact GlobalTheory.CompanionTheory.Ar.AmpleBlock.ampleQ_of_embeds | (intros; apply GlobalTheory.CompanionTheory.Ar.AmpleBlock.ampleQ_of_embeds <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.AnalyticChartUnitSectionStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat Filter Topology Metric
open ReciprocityTheory.ChartRestriction.G.TB.ValAt ReciprocityTheory.ChartRestriction.G.PullbackSections
open GlobalTheory.CompanionTheory.Ar.Flat.GagaC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.analytic_chart_unit_section : ∀ (X : Scheme.{0}) (s : X ⟶ Sp ℂ) (Ω : Type) [Field Ω] (ξ : Sp Ω ⟶ X) (W U N : X.Opens) (F : (Sp ℂ ⟶ X) → ℂ) (T t : Ω) (v : Γ(X, N)) (d : ℕ) (B : Set (Fin d → ℂ)) (Y : (Fin d → ℂ) → (Sp ℂ ⟶ X)) (b₁ : Fin d → ℂ), IsCptGen ξ → IsChart s B Y → b₁ ∈ B → (∀ b ∈ B, centre (Y b) ∈ N ∧ genPt ξ ⤳ centre (Y b)) → N ≤ U → (∀ O : Set (Fin d → ℂ), IsOpen O → O ⊆ B → O.Nonempty → ∃ b ∈ O, centre (Y b) ∈ W) → IsUnit v → (∀ (q : X) (hq : genPt ξ ⤳ q) (h : q ∈ N), genMap ξ ⟨q, hq⟩ (X.presheaf.germ N q h v) = t / T) → T ≠ 0 → ExtendsUnitAt s (RingHom.id ℂ) ξ W F t (Y b₁) → ∃ (B₂ : Set (Fin d → ℂ)) (H : (Fin d → ℂ) → ℂ), b₁ ∈ B₂ ∧ HChart s ξ W U F T B₂ Y H := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.GagaC.exists_hChart_of_extendsUnitAt | exact GlobalTheory.CompanionTheory.Ar.Flat.GagaC.exists_hChart_of_extendsUnitAt | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.GagaC.exists_hChart_of_extendsUnitAt <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.AnalyticChartVanishingSectionStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat Filter Topology Metric
open ReciprocityTheory.ChartRestriction.G.TB.ValAt ReciprocityTheory.ChartRestriction.G.PullbackSections
open GlobalTheory.CompanionTheory.Ar.Flat.GagaC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.analytic_chart_vanishing_section : (∀ (A : Type) [CommRing A] [IsDomain A] [Algebra ℂ A] (D : ℕ) [Algebra.IsStandardSmoothOfRelativeDimension D ℂ A] (O : Set (Fin D → ℂ)) (Ψ : (Fin D → ℂ) → (A →+* ℂ)) (f : Fin D → A) (a : A), IsOpen O → O.Nonempty → (∀ b ∈ O, (Ψ b).comp (algebraMap ℂ A) = RingHom.id ℂ ∧ ∀ i, Ψ b (f i) = b i) → (∀ b ∈ O, Ψ b a = 0) → a = 0) → ∀ (X : Scheme.{0}) (s : X ⟶ Sp ℂ) (Ω : Type) [Field Ω] (ξ : Sp Ω ⟶ X) (W N : X.Opens) (x : Sp ℂ ⟶ X), Smooth s → IsCptGen ξ → genPt ξ ∈ W → x ≫ s = 𝟙 _ → genPt ξ ⤳ centre x → centre x ∈ N → ∃ (d : ℕ) (B : Set (Fin d → ℂ)) (Y : (Fin d → ℂ) → (Sp ℂ ⟶ X)) (b₁ : Fin d → ℂ), IsChart s B Y ∧ b₁ ∈ B ∧ Y b₁ = x ∧ (∀ b ∈ B, centre (Y b) ∈ N ∧ genPt ξ ⤳ centre (Y b)) ∧ ∀ O : Set (Fin d → ℂ), IsOpen O → O ⊆ B → O.Nonempty → ∃ b ∈ O, centre (Y b) ∈ W := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.GagaC.ChartAt.exists_chart | exact GlobalTheory.CompanionTheory.Ar.Flat.GagaC.ChartAt.exists_chart | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.GagaC.ChartAt.exists_chart <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ArtinSchreierCocycleRoot
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem GlobalTheory.CompanionTheory.Ar.CechP.coboundary_of_pow_coboundary : ∀ (Z : Scheme.{0}) [IsIntegral Z] (p : ℕ) [Fact p.Prime] [CharP Z.functionField p], ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme Z → ∀ (J : Type) (U : J → Z.Opens) (n : ∀ a b, Γ(Z, U a ⊓ U b)) (h : ∀ a, Γ(Z, U a)) (a₀ : J) [Nonempty (U a₀)], (∀ a b, n a b ^ p = (Z.presheaf.map (homOfLE (inf_le_left : U a ⊓ U b ≤ U a)).op).hom (h a) - (Z.presheaf.map (homOfLE (inf_le_right : U a ⊓ U b ≤ U b)).op).hom (h b)) → (∃ r : Z.functionField, r ^ p = (Z.germToFunctionField (U a₀)).hom (h a₀)) → ∃ s : ∀ a, Γ(Z, U a), ∀ a b, n a b = (Z.presheaf.map (homOfLE (inf_le_left : U a ⊓ U b ≤ U a)).op).hom (s a) - (Z.presheaf.map (homOfLE (inf_le_right : U a ⊓ U b ≤ U b)).op).hom (s b) := by
  intro Z _ p _ _ hN J U n h a₀ _ hn ⟨r, hr⟩
  have hg : genericPoint Z ∈ U a₀ := ((genericPoint_spec Z).mem_open_set_iff (U a₀).isOpen).mpr (by
    obtain ⟨⟨z, hz⟩⟩ := ‹Nonempty (U a₀)›
    exact ⟨z, trivial, hz⟩)
  haveI : Nonempty (⊤ : Z.Opens) := ⟨⟨genericPoint Z, trivial⟩⟩
  have hp : (p : Γ(Z, ⊤)) = 0 := by
    apply Z.germToFunctionField_injective ⊤
    rw [map_natCast, map_zero]
    exact CharP.cast_eq_zero _ p
  obtain ⟨s, hs⟩ := GlobalTheory.CechRoot.exists_root Z (fun b => (hN b).2) p hp J U h n
    (fun a b => (hn a b).symm) a₀ (genericPoint Z) hg (algebraMap Z.functionField _ r)
    (by rw [← map_pow, hr])
  exact ⟨s, fun a b => (hs a b).symm⟩
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ComplexCoordsAddedStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.FlagStep
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.complex_coords_added : ∀ (X X' : Scheme.{0}) (Ω₀ Ω : Type) [Field Ω₀] [Field Ω] [Algebra Ω₀ Ω]
    (ξ : Spec (CommRingCat.of Ω₀) ⟶ X) (ξ' : Spec (CommRingCat.of Ω) ⟶ X') (f : X' ⟶ X)
    (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω₀) (N : ℕ) (x' : Fin (N + 1) → Ω)
    (z : Spec (CommRingCat.of ℂ) ⟶ X') (w : (Σ k, addJ J N k) → ℂ),
    (∀ q : X, genPt ξ ⤳ q) → CoordTie ℤ ξ (fun c' : (k : K) → J k => ∏ k, y ⟨k, c' k⟩) → IsCptGen ξ' →
    (∀ q : X', genPt ξ' ⤳ q) → GlobalTheory.CompanionTheory.Ar.Dominates ξ' ξ f (algebraMap Ω₀ Ω) →
    CoordsAt ξ' (addY y x') z w → CoordsAt ξ y (z ≫ f) (fun p => w (addV J N p)) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.FlagStep.CoordsRestrict.coordsAt_restrict | exact GlobalTheory.CompanionTheory.Ar.FlagStep.CoordsRestrict.coordsAt_restrict | (intros; apply GlobalTheory.CompanionTheory.Ar.FlagStep.CoordsRestrict.coordsAt_restrict <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ComplexCoordsReindexedStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.complex_coords_reindexed : ∀ (X X' : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (ξ' : Spec (CommRingCat.of Ω) ⟶ X') (g : X' ⟶ X) (K : Type) (J : K → Type) (y : (Σ k, J k) → Ω) (K' : Type) (J' : K' → Type) (y' : (Σ k, J' k) → Ω) (bk : K → K') (bx : ∀ k, J k ≃ J' (bk k)) (z : Spec (CommRingCat.of ℂ) ⟶ X') (w : (Σ k, J' k) → ℂ), (∀ q : X, genPt ξ ⤳ q) → (∀ q : X', genPt ξ' ⤳ q) → IsCptGen ξ' → ξ' ≫ g = ξ → (∀ k a, y' ⟨bk k, bx k a⟩ = y ⟨k, a⟩) → (∀ q' : Cpt ξ', (∀ r : ℕ, r.Prime → ¬ InFibre ξ' r q') → ∀ h : genPt ξ ⤳ g q'.1, regAt ξ' q' = regAt ξ ⟨g q'.1, h⟩) → CoordsAt ξ' y' z w → CoordsAt ξ y (z ≫ g) (fun p : (Σ k, J k) => w ⟨bk p.1, bx p.1 p.2⟩) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.CoordsDown.coordsAt_down | exact GlobalTheory.CompanionTheory.Ar.CoordsDown.coordsAt_down | (intros; apply GlobalTheory.CompanionTheory.Ar.CoordsDown.coordsAt_down <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ComponentGenericCharZeroStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.component_generic_char_zero : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Tor.Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (Ω₀ : Type) [Field Ω₀] (ξ₀ : Spec (CommRingCat.of Ω₀) ⟶ Y.X), IsCptGen ξ₀ → CharZero Ω₀ := by
  first | exact @GlobalTheory.CompanionTheory.Ar.CharZeroModel.charZero_function_field | exact GlobalTheory.CompanionTheory.Ar.CharZeroModel.charZero_function_field | (intros; apply GlobalTheory.CompanionTheory.Ar.CharZeroModel.charZero_function_field <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ComponentGenericIsGenericPointStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.component_generic_is_generic_point : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Tor.Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (Ω₀ : Type) [Field Ω₀] (ξ₀ : Spec (CommRingCat.of Ω₀) ⟶ Y.X), IsCptGen ξ₀ → GlobalTheory.CompanionTheory.Ar.genPt ξ₀ ∈ genericPoints Y.X := by
  first | exact @GlobalTheory.CompanionTheory.Ar.GenPtModel.genPt_mem_genericPoints | exact GlobalTheory.CompanionTheory.Ar.GenPtModel.genPt_mem_genericPoints | (intros; apply GlobalTheory.CompanionTheory.Ar.GenPtModel.genPt_mem_genericPoints <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.CoordsAddedProjectiveStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.FlagStep
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.coords_added_projective : ∀ (X X' : Scheme.{0}) (Ω₀ Ω : Type) [Field Ω₀] [Field Ω] [Algebra Ω₀ Ω]
    (ξ : Spec (CommRingCat.of Ω₀) ⟶ X) (ξ' : Spec (CommRingCat.of Ω) ⟶ X') (f : X' ⟶ X)
    (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω₀) (N : ℕ) (x' : Fin (N + 1) → Ω),
    (∀ q : X, genPt ξ ⤳ q) → CoordTie ℤ ξ (fun c' : (k : K) → J k => ∏ k, y ⟨k, c' k⟩) → CoordTie ℤ ξ' x' →
    GlobalTheory.CompanionTheory.Ar.Dominates ξ' ξ f (algebraMap Ω₀ Ω) →
    CoordTie ℤ ξ' (fun c' : (k : Unit ⊕ K) → addJ J N k => ∏ k, addY y x' ⟨k, c' k⟩) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.FlagStep.TieBlocks.tie_blocks | exact GlobalTheory.CompanionTheory.Ar.FlagStep.TieBlocks.tie_blocks | (intros; apply GlobalTheory.CompanionTheory.Ar.FlagStep.TieBlocks.tie_blocks <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.CoordsCompatibleAlongMapStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.smoothGenericFibre_of_dominates : ∀ (Ω : Type) [Field Ω] [CharZero Ω] (K₁ : Type) [Fintype K₁] (J₁ : K₁ → Type) [∀ k, Fintype (J₁ k)] (y₁ : (Σ k, J₁ k) → Ω) (K₂ : Type) [Fintype K₂] (J₂ : K₂ → Type) [∀ k, Fintype (J₂ k)] (y₂ : (Σ k, J₂ k) → Ω) (X₁ X₂ : Scheme.{0}) (ξ₁ : Spec (CommRingCat.of Ω) ⟶ X₁) (ξ₂ : Spec (CommRingCat.of Ω) ⟶ X₂) (g : X₂ ⟶ X₁), (∀ q : X₁, GlobalTheory.CompanionTheory.Ar.genPt ξ₁ ⤳ q) → (∀ q : X₂, GlobalTheory.CompanionTheory.Ar.genPt ξ₂ ⤳ q) → CoordTie ℤ ξ₁ (fun c' : (k : K₁) → J₁ k => ∏ k, y₁ ⟨k, c' k⟩) → CoordTie ℤ ξ₂ (fun c' : (k : K₂) → J₂ k => ∏ k, y₂ ⟨k, c' k⟩) → GlobalTheory.CompanionTheory.Ar.Dominates ξ₂ ξ₁ g (RingHom.id Ω) → SmoothGenericFibreM y₁ → (∀ q ∈ genFib ξ₁, IsoAt ξ₂ g (RingHom.id Ω) q) → SmoothGenericFibreM y₂ := by
  first | exact @GlobalTheory.CompanionTheory.Ar.SmoothChange.smoothGenericFibreM_of_isoAt | exact GlobalTheory.CompanionTheory.Ar.SmoothChange.smoothGenericFibreM_of_isoAt | (intros; apply GlobalTheory.CompanionTheory.Ar.SmoothChange.smoothGenericFibreM_of_isoAt <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.DenseOpenGenericFibreStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.SncBase GlobalTheory.CompanionTheory.Ar.GeoModel
open GroundTheory.Heights₂.Heights.LowerBoundFree
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dense_open_generic_fibre : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Tor.Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (Ω : Type) [Field Ω] (κ : Type) [Finite κ] (x : κ → Ω) (M : PModel ℤ x) (f : M.X ⟶ Y.X) (y₀ : Sp Ω ⟶ Xo.XF c), M.ξ ≫ f = y₀ ≫ Y.j → ∃ U : (pullback (f ≫ Y.s) (spMap (algebraMap (𝓞 c.F) c.F))).Opens, Dense (U : Set ((pullback (f ≫ Y.s) (spMap (algebraMap (𝓞 c.F) c.F)) : Scheme.{0}))) ∧ pullback.fst (f ≫ Y.s) (spMap (algebraMap (𝓞 c.F) c.F)) ⁻¹' (f ⁻¹' abLocus Y.t.G) = U := by
  first | exact @GlobalTheory.CompanionTheory.Ar.GeoModel.OpenLocus.exists_dense_open | exact GlobalTheory.CompanionTheory.Ar.GeoModel.OpenLocus.exists_dense_open | (intros; apply GlobalTheory.CompanionTheory.Ar.GeoModel.OpenLocus.exists_dense_open <;> assumption)
end

