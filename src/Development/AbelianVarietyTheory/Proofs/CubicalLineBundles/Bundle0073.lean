import Mathlib
import Formalism.LocalToGlobal.CMDeterminantIdeals.LambdaLowerBound
import ReciprocityTheory.SemistableReduction.Bundle0009
import Development.AbelianVarietyTheory.Statements.FundamentalDomains.KeyFormulaPowOfKeyFormula
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0020
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0072
import Development.AbelianVarietyTheory.Definitions.CMLattices.IntegralOf
import Development.AbelianVarietyTheory.Statements.PrincipalLattices.ExistsPrincipalLattice
import Development.AbelianVarietyTheory.Definitions.RegularCharts.BaseNorm
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0026
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0024
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.NonemptyUnitAt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0010
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0007
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0011
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0025
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0048
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0045

-- bundled from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.CmPointLowerBoundFree
section
open NumberField IsDedekindDomain MeasureTheory IsLocalRing Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.LamCM
open scoped nonZeroDivisors ComplexOrder

namespace GlobalTheory

theorem cmPoint_lowerBound_free :
    ∀ (K : Type) [Field K] [NumberField K] (x : KeyIn K) (T abelian₂ : MLine K) (B : Type) [Fintype B] [DecidableEq B] (m : B → ℕ) (e : (Σ b, Fin (m b)) ≃ Fin x.P.g) (ℓ : Fin x.P.g → MLine K) (U : Matrix (Fin x.P.g) (Fin x.P.g) K) (G : MvPolynomial (FrVar m) K) (a : ∀ b, Fin (m b) → ℕ) (n r : ℕ) (La logOm : ℝ) (S : (K →+* ℂ) → ℝ), T.Good → abelian₂.Good → (∀ p, KeyLocAt x T abelian₂ p) → (∀ σ, KeyArchAt x T abelian₂ σ) → (∀ j, (ℓ j).Good) → (∀ j, (ℓ j).ndeg = logOm / 2) → U.det ≠ 0 → G ≠ 0 → 1 ≤ La → 1 ≤ r → (∀ b, m b ≤ r) → (∀ σ, 0 < S σ) → (∀ p, Step5Loc e T.dual abelian₂ ℓ U G n p) → (∀ σ, Step5Arch e T.dual abelian₂ ℓ U G a n La (S σ) σ) → - ((pDeg logOm + (1 / 2) * Real.log La) * (((∑ b, ∑ i, a b i : ℕ) : ℝ) + (x.P.g : ℝ) * n)) - ((∑ b, ∑ i, a b i : ℕ) : ℝ) * Real.log ((r : ℝ) * La) ≤ (∑ σ : K →+* ℂ, Real.log (S σ)) / (Module.finrank ℚ K : ℝ) :=
  GlobalTheory.T.cmPoint_lower_bound_of_coefficient_bound GlobalTheory.T.thetaLine_degree_and_heightLowerBound.2 ReciprocityTheory.MultiplicativeHeights.lemmaH_holds

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsGoodCmPointOfIntegralCmObjectStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.LamCM Formalism.L2.Pj
open scoped ComplexOrder
open GlobalTheory GlobalTheory.CM GlobalTheory.Frames GlobalTheory.LamT

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_good_cm_point_of_integral_cm_object : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)], (∀ a : 𝓞 E, star a = H.bar a) → ∀ (K : Type) [Field K] [NumberField K] [Algebra c.F K] (ρ : 𝓞 K) (σ : K →+* ℂ) (X : CMObj H K ρ σ Dw.p Dw.q) (La : ℝ) (x : Sp K ⟶ Xo.X) (Φ : FibKey Xo K x) (_ : SABMap Φ.T.t X.B.t (spMap (algebraMap (𝓞 K) K))), (∀ τ, τ ∈ LamF.psiSet H ↔ LamF.labK c K τ (H.rt : E) = (ρ : K)) → (∀ j (τ : E →+* ℂ), ‖τ (X.hh j : E)‖ ≤ La ^ 2) → x ≫ Xo.s = sOf c K → ∀ (S : Type) [CommRing S] [Algebra c.F S] (σ₁ : K →ₐ[c.F] S), ∃ (z : CMPt Xo c) (σ' : z.K →ₐ[c.F] S), z.Good (Module.finrank ℚ E / 2) La ∧ spMap σ'.toRingHom ≫ z.y.x = spMap σ₁.toRingHom ≫ x := by
  first | exact @GlobalTheory.LamT.exists_cmPt_good_of_cmObj | exact GlobalTheory.LamT.exists_cmPt_good_of_cmObj | (intros; apply GlobalTheory.LamT.exists_cmPt_good_of_cmObj <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IntegralGeneratorAssociatedLocalGeneratorCMLineStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.LamCM Formalism.L2.Pj
open scoped ComplexOrder
open GlobalTheory GlobalTheory.CM GlobalTheory.Frames GlobalTheory.LamT

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integralGenerator_associated_localGenerator_CM_line : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)] (z : CMPt Xo c) (f : ℕ) (La : ℝ), z.Good f La → ∀ (p : HeightOneSpectrum (𝓞 z.K)) (T : CDVR) (iK : z.K →+* T.Fr) (M : LocMod z T iK), (∀ y : z.K, iK y ∈ Set.range (algebraMap T.V T.Fr) ↔ p.valuation z.K y ≤ 1) → letI := (iK.comp (algebraMap c.F z.K)).toAlgebra; ∀ (φ : z.K →ₐ[c.F] T.Fr) (yT y' : FrPt Xo c T.Fr) (g : (∀ b : E →+* ℂ, Matrix (Fin (Dw.mult b)) (Fin (Dw.mult b)) T.Fr)) (a : T.Fr), φ.toRingHom = iK → FrMap φ z.y yT → FrChg g a yT y' → SecInt T M.m1 M.m2 y'.s → ∀ ca : z.K, IsLocGen p ca z.Tl.I → ∃ u : T.Vˣ, a = iK ca * algebraMap T.V T.Fr u := by
  first | exact @GlobalTheory.LamT.LocGen.integral_generator_unit | exact GlobalTheory.LamT.LocGen.integral_generator_unit | (intros; apply GlobalTheory.LamT.LocGen.integral_generator_unit <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.MetricDataUnique
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.LamCM Formalism.L2.Pj
open scoped ComplexOrder
open GlobalTheory GlobalTheory.CM GlobalTheory.Frames GlobalTheory.LamT

namespace GlobalTheory.LamT.MetUniq

theorem uniq_cast (x : KeyIn ℂ) (g : ℕ) (hg : x.P.g = g) (u : HolUnif x.P.A x.P.L g) (Hm : Matrix (Fin g) (Fin g) ℂ)
    (χ : u.Λ → ℂ) (θ : (Fin g → ℂ) → ℂ) (Fd : Set (Fin g → ℂ)) (u' : HolUnif x.P.A x.P.L x.P.g)
    (Hm' : Matrix (Fin x.P.g) (Fin x.P.g) ℂ) (χ' : u'.Λ → ℂ) (θ' : (Fin x.P.g → ℂ) → ℂ) (Fd' : Set (Fin x.P.g → ℂ))
    (h : u.IsAH Hm χ ∧ u.IsRig x.rig ∧ u.IsFn x.th θ ∧ IsAddFundamentalDomain u.Λ Fd volume)
    (h' : u'.IsAH Hm' χ' ∧ u'.IsRig x.rig ∧ u'.IsFn x.th θ' ∧ IsAddFundamentalDomain u'.Λ Fd' volume) :
    (∫ z in Fd, ‖θ z‖ ^ 2 * Real.exp (-Real.pi * (hermForm Hm z z).re)) / (volume Fd).toReal =
      (∫ z in Fd', ‖θ' z‖ ^ 2 * Real.exp (-Real.pi * (hermForm Hm' z z).re)) / (volume Fd').toReal ∧
    ∀ (v w : epsR ℂ ⟶ x.P.A) (V W : Fin g → ℂ) (V' W' : Fin x.P.g → ℂ), IsTangent v → IsTangent w → u.IsDiff V v →
      u.IsDiff W w → u'.IsDiff V' v → u'.IsDiff W' w → hermForm Hm V W = hermForm Hm' V' W' := by
  subst hg
  exact GlobalTheory.T.thetaSection_norm_and_hermitianForm_indep_uniformisation x u Hm χ θ Fd u' Hm' χ' θ' Fd' h h'

theorem spMap_dualMap_id (S : Type) [CommRing S] :
    spMap (Formalism.L2.Pj.dualMap (RingHom.id S)) = 𝟙 (Sp (DualNumber S)) := by
  have : Formalism.L2.Pj.dualMap (RingHom.id S) = RingHom.id _ := by
    refine RingHom.ext fun r => ?_
    ext <;> simp [Formalism.L2.Pj.dualMap]
  rw [this]
  exact Spec.map_id _

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l}

theorem isMetricAt_unique (x : Sp ℂ ⟶ Xo.X) (s : LB.Sec (PPx x))
    (uu : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → (Sp (DualNumber ℂ) ⟶ Xo.univ.t.G.left)) (ht : ∀ τ i, IsTanAt x (uu τ i))
    (N N' : ℝ) (Gr Gr' : ∀ b : E →+* ℂ, Matrix (Fin (Dw.mult b)) (Fin (Dw.mult b)) ℂ)
    (h : IsMetricAt x s uu N Gr) (h' : IsMetricAt x s uu N' Gr') : N = N' ∧ Gr = Gr' := by
  obtain ⟨Φ, u, Hm, χ, θ, Fd, w, W, tie, a1, a2, a3, a4, hN, hw, hG⟩ := h
  obtain ⟨Φ', u', Hm', χ', θ', Fd', w', W', tie', b1, b2, b3, b4, hN', hw', hG'⟩ := h'
  have hx : x = spMap (RingHom.id ℂ) ≫ x := by
    have : spMap (RingHom.id ℂ) = 𝟙 (Sp ℂ) := Spec.map_id _
    rw [this, Category.id_comp]
  have sc := GlobalTheory.Frames.SecCalc.sec_calc E H Dw l Xo ℂ ℂ ℂ (RingHom.id ℂ) (RingHom.id ℂ) x x x hx hx
  have hbc : SecBC (RingHom.id ℂ) 1 x x s s := (sc.2.1 1 s s).2 fun i => by
    rw [(sc.2.2.2 1 1 i).2.2, _root_.one_mul]
  obtain ⟨hg, v', hv', kp, hv⟩ := GlobalTheory.T.universalTripleFibreKeyData_baseChange_keyPullback E H Dw l Xo ℂ ℂ (RingHom.id ℂ) x x Φ Φ' s s hx tie tie' hbc
  simp only [spMap_dualMap_id, Category.id_comp] at hv
  obtain ⟨u₁, χ₁, θ₁, Fd₁, c1, c2, c3, c4, hN₁, hD⟩ := GlobalTheory.T.exists_appellHumbert_uniformisation_of_keyDatumIso Φ.key _ kp hg _ u Hm χ θ Fd ⟨a1, a2, a3, a4⟩
  have hm : Hm.map (RingHom.id ℂ) = Hm := rfl
  rw [hm] at c1 hN₁
  obtain ⟨e1, e2⟩ := uniq_cast ({ Φ' with v := v', basis := hv' } : FibKey Xo ℂ x).key _ hg u₁ Hm χ₁ θ₁ Fd₁
    u' Hm' χ' θ' Fd' ⟨c1, c2, c3, c4⟩ ⟨b1, b2, b3, b4⟩
  have tan : ∀ b i, IsTangent (G := Φ.T.t.G) (w b i) := fun b i =>
    (Chart.tan_push Φ.m.cart _).2 (((congrArg (_ ≫ ·) (hw b i).1)).trans (ht b i).2)
  have tan' : ∀ b i, IsTangent (G := Φ'.T.t.G) (w' b i) := fun b i =>
    (Chart.tan_push Φ'.m.cart _).2 (((congrArg (_ ≫ ·) (hw' b i).1)).trans (ht b i).2)
  have key : ∀ b i, u₁.IsDiff (W b i) (w' b i) := fun b i => by
    obtain ⟨cf, hcf, -⟩ := Φ.basis.2 (w b i) (tan b i)
    refine hD cf (w b i) (w' b i) (W b i) hcf ?_ (hw b i).2
    obtain ⟨p, hp, hq⟩ := (Chart.comb_push Φ.m.cart _ _ _).1 hcf
    refine (Chart.comb_push Φ'.m.cart _ v' (w' b i)).2 ⟨fun j => p (j.cast hg), fun j => ?_, ?_⟩
    · exact (hp _).trans (congrArg (_ ≫ ·) (hv j).symm)
    · have : List.ofFn (fun j : Fin Φ'.T.g => p (j.cast hg)) = List.ofFn p := (List.ofFn_congr hg.symm p).symm
      exact (congrArg (fun L => (List.prod L).left) this).trans (hq.trans ((hw b i).1.trans (hw' b i).1.symm))
  refine ⟨hN.trans (hN₁.symm.trans (e1.trans hN'.symm)), ?_⟩
  funext b
  ext i k
  rw [hG, hG', e2 (w' b k) (w' b i) _ _ _ _ (tan' b k) (tan' b i) (key b k) (key b i) (hw' b k).2 (hw' b i).2]

theorem isMetric_unique : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (y : FrPt Xo c (CAt σ)) (N N' : ℝ) (Gr Gr' : (∀ b : E →+* ℂ, Matrix (Fin (Dw.mult b)) (Fin (Dw.mult b)) ℂ)), IsMetric y N Gr → IsMetric y N' Gr' → N = N' ∧ Gr = Gr' :=
  fun _ _ _ _ _ _ _ _ _ _ y N N' Gr Gr' h h' => isMetricAt_unique y.x y.s y.u y.tan N N' Gr Gr' h h'

end GlobalTheory.LamT.MetUniq
end

