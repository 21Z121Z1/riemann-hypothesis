import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0665
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedRationalOfOneMapOverL
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0014
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StableIffCarrierEq
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0013
import Formalism.LocalToGlobal.UnitaryNorms.Bundle0006
import Formalism.LocalRingCardinality.Bundle0004
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0032
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0036
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0041
import Formalism.LocalToGlobal.ProjectiveLattices.ExistsParameterConditions
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0006
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DsExistsOfDiscreteSeriesExists
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0670
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0601
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0659
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0671
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.IsPrincipalMapOfAlgHom
import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.NonemptyAlgHomOfIsRayOfDvd
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.PublishedTheorems.WeberRayClassFields.WeberRayFieldSt
import Formalism.SharpRestriction.GlobalSchurBounds.ThickPlacesCorollaryOfAnyTranslate
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0043
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0030
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0405
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0466
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PushInvertibleModelOfIso
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsThetaL2NormSquared
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.SiegelFamilyNearbyPeriodsSameComponent
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsSiegelFamilyOverNumberField
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0046
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0040
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0042
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.NotInjOnOfFderivEqZero
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ThetaFrameValueIndependentNormalForm
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0014
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0002
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0015
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.EqZeroOfSemicharacterMultiplier
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsEqCexpQuadraticOfEquivalentFactors
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0141
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsLinearOfIsMonHom
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0651
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0643
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0669
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0674
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NonnegSumSmulIntBilinFormToRealMemPsdCone
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0673
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0677
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0090
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0213
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.CoefficientFieldIntegersDedekindFractionField
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0672

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GeometricExistenceCoreFormsAnalyticPhaseOne
section
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.Pj Formalism.IndefR.FWT ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.RealGeo
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.R3.GeoExProof

set_option maxHeartbeats 2000000 in

theorem geoExV_of_top : GlobalTheory.Published.CuspRapidDecay → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T0 : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T0 D.R.m) (C : CoreJ D) [Algebra C.Q.c.F D.what₂.LL] (F : Face D A3.A), VolTieG D → LawsJ C → LawsCore C.toCore → AlgTie C → Finite T0 → (∀ i, VStd D i) → 8 * D.R.f * D.R.r + 4 ≤ D.R.nV → GlobalTheory.Mem.R3.GeoExV A3 C F := by
  intro hRD D G _ _ Pl0 I0 T0 A3 C _ F hVol hL hLC hA hT hVS hn R cG hVal hPre _hlev hpb hK
  obtain ⟨dict, mu, chiW, x₀, cE, nW, FW, B, -, -, hFired, -, -, hPre', hchi, hU, -, -⟩ :=
    GlobalTheory.T.exists_geometricHalf_phase_one_over_lawful_core hRD D G Pl0 T0 A3.A C R hVol hL hLC hA hpb hPre hK.valKs hK.frameKs hVal hT hK.guard hVS hn
  refine ⟨dict, mu, chiW, x₀, cE, nW, FW, hchi, ⟨B⟩, fun i x => ?_⟩
  have hHW := hPre'.models.HW
  obtain ⟨m, a, f, hf⟩ := (hFired.1 i).2.2 x
  have hm : (1 : ℂ) • ((updFW R nW FW).HW i (sg0 D A3.A)).e (R.thG i A3.A.μ0 (jVx (updFW R nW FW) i A3.A.μ0 x)) ∈
      (updFW R nW FW).Wall i (sg0 D A3.A) :=
    ((updFW R nW FW).Wall i (sg0 D A3.A)).smul_mem 1 ((hHW i _).2.1.le (LinearMap.mem_range_self _ _))
  obtain ⟨y, hy⟩ := GlobalTheory.TwistedClassSum.exists_adForm B.fw hHW hU (B.O i).hV hm a f 1 fun q =>
    (hf q.out).trans (one_mul _).symm
  rw [one_smul, one_smul] at hy
  exact ⟨y, (hHW i _).1 hy.symm⟩

end GlobalTheory.Mem.R3.GeoExProof
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HermFormImRealCombinationEqDotProductStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor GlobalTheory.ShFam.Hor.LogCh
open scoped Matrix CategoryTheory.Obj Topology
attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermForm_im_real_combination_eq_dotProduct : ∀ (g r : ℕ) (x : Fin r → Fin g → ℂ) (M : Matrix (Fin r) (Fin r) ℝ) (Hm : Matrix (Fin g) (Fin g) ℂ), (∀ i j, (hermForm Hm (x i) (x j)).im = M i j) → ∀ u v : Fin r → ℝ, (hermForm Hm (∑ m, (u m : ℂ) • x m) (∑ m, (v m : ℂ) • x m)).im = u ⬝ᵥ M *ᵥ v := by
  first | exact @GlobalTheory.hermForm_im_real_comb | exact GlobalTheory.hermForm_im_real_comb | (intros; apply GlobalTheory.hermForm_im_real_comb <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HermFormPeriodsAlternatingNondegRankEqTwoMulStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor GlobalTheory.ShFam.Hor.LogCh
open scoped Matrix CategoryTheory.Obj Topology
attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermForm_periods_alternating_nondeg_rank_eq_two_mul : ∀ (g r : ℕ) (x : Fin r → Fin g → ℂ) (M : Matrix (Fin r) (Fin r) ℝ) (Hm : Matrix (Fin g) (Fin g) ℂ), LinearIndependent ℝ x → Submodule.span ℝ (Set.range x) = ⊤ → Hm.IsHermitian → (∀ z : Fin g → ℂ, z ≠ 0 → 0 < (hermForm Hm z z).re) → (∀ i j, (hermForm Hm (x i) (x j)).im = M i j) → Mᵀ = -M ∧ M.det ≠ 0 ∧ r = 2 * g := by
  first | exact @GlobalTheory.hermForm_periods_alternating_nondeg | exact GlobalTheory.hermForm_periods_alternating_nondeg | (intros; apply GlobalTheory.hermForm_periods_alternating_nondeg <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HostPlacesRayField
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.Top.Bl

theorem hostPins_wpt : GlobalTheory.NT.RayField → ∀ (𝒮 : Slots) (K : Ctx) (q : WPt 𝒮 K), GlobalTheory.Mem.HD.HostPins (q.w.D q.Z) q.O.ex.nch := by
  intro hR 𝒮 K q
  obtain ⟨B, f, T, w, Z, O, x⟩ := q
  have hmu := x.what₂.mu
  have key := GlobalTheory.Mem.Top.TupTieW.tupTied_of_muIsW (w.st Z) f T x.Wt w.I.xi hmu
  have hδ : w.δ.ray ≤ B.KsC := w.exact.lower.1
  have hQ : ∀ v ∈ x.Wt, O.ex.nch.Q v = T.Q v := fun v hv => (x.n.Q v hv).1
  refine ⟨fun u i => (w.D Z).T_ne_g u i, ?_, fun v hv v' hv' u => ?_, B.galLL, GlobalTheory.Mem.HD.exists_hilbert_le_O hR B w.δ hδ⟩
  · exact key.2.1.subset fun v hv => (key.1 v).1 hv
  · have hvW := (key.1 v).1 hv
    rw [hQ v hvW] at hv'
    have e : ((w.D Z).mem u).A.T = B.T u := (w.st Z).C.A_T u
    have hp : (B.T u).Prime := e ▸ ((w.D Z).mem u).A.T_prime
    rw [e]
    exact GlobalTheory.Mem.HD.twistConductor_not_over_levelPrimes B T v hv' u hp

end GlobalTheory.Mem.Top.Bl
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ImHermFormPer
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.KeyPow GlobalTheory.KeyFam GlobalTheory.ZM GlobalTheory.AbLaw GlobalTheory.KeyCl GlobalTheory.LocM
open Filter Topology Matrix

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.WeilStd

open ReciprocityTheory.PTheta Matrix in

theorem im_hermForm_per {g : ℕ} {τ : Matrix (Fin g) (Fin g) ℂ} (hτ : τ ∈ SiegelH (Fin g))
    (k k' : Fin g → ℤ) {Hm : Matrix (Fin g) (Fin g) ℂ} (hH : Hm.IsHermitian)
    (F : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)) (ρ : (Fin g → ℂ) → ℂ) (hρd : Differentiable ℂ ρ) (hρ0 : ∀ z, ρ z ≠ 0)
    (χ : (Fin g ⊕ Fin g → ℤ) → ℂ) (hχ : ∀ r, χ r ≠ 0)
    (h : ∀ r z, ρ (z + per τ r) * (χ r * Complex.exp (Real.pi * hermForm Hm (F z) (F (per τ r)) +
        Real.pi / 2 * hermForm Hm (F (per τ r)) (F (per τ r)))) * theta (Key.halfVec k) (Key.halfVec k') z τ =
      ρ z * theta (Key.halfVec k) (Key.halfVec k') (z + per τ r) τ)
    (p q : Fin g ⊕ Fin g → ℤ) :
    (hermForm Hm (F (per τ p)) (F (per τ q))).im = omegaStd p q := by

  classical
  have hper : ∀ r : Fin g ⊕ Fin g → ℤ, per τ r =
      τ *ᵥ ofIntVec (fun i => r (Sum.inl i)) + ofIntVec (fun i => r (Sum.inr i)) := fun r => rfl
  have qp : ∀ r z, theta (Key.halfVec k) (Key.halfVec k') (z + per τ r) τ =
      autFactor (Key.halfVec k) (Key.halfVec k') τ (fun i => r (Sum.inl i)) (fun i => r (Sum.inr i)) z *
        theta (Key.halfVec k) (Key.halfVec k') z τ := fun r z => by
    rw [hper, ← add_assoc]
    exact thetaQuasiPeriod_holds (Fin g) _ _ z τ _ _ hτ.1
  choose c₁ hc₁ using fun r : Fin g ⊕ Fin g → ℤ =>
    NormalUnique.autFactor_eq_exp (Key.halfVec k) (Key.halfVec k') τ (fun i => r (Sum.inl i)) (fun i => r (Sum.inr i))
  let lin₁ : (Fin g ⊕ Fin g → ℤ) → (Fin g → ℂ) →ₗ[ℂ] ℂ := fun r =>
    { toFun := fun v => -(2 * Real.pi * Complex.I) * (ofIntVec (fun i => r (Sum.inl i)) ⬝ᵥ v)
      map_add' := fun v w => by simp only [dotProduct_add]; ring
      map_smul' := fun s v => by simp only [dotProduct_smul, smul_eq_mul, RingHom.id_apply]; ring }
  let lin₂ : (Fin g ⊕ Fin g → ℤ) → (Fin g → ℂ) →ₗ[ℂ] ℂ := fun r =>
    { toFun := fun v => (Real.pi : ℂ) * hermForm Hm (F v) (F (per τ r))
      map_add' := fun v w => by simp only [map_add, hermForm, add_dotProduct]; ring
      map_smul' := fun s v => by simp only [map_smul, hermForm, smul_dotProduct, smul_eq_mul, RingHom.id_apply]; ring }
  let c₂ : (Fin g ⊕ Fin g → ℤ) → ℂ := fun r =>
    Complex.log (χ r) + Real.pi / 2 * hermForm Hm (F (per τ r)) (F (per τ r))
  have e1 : ∀ r v, Complex.exp (lin₁ r v + c₁ r) =
      autFactor (Key.halfVec k) (Key.halfVec k') τ (fun i => r (Sum.inl i)) (fun i => r (Sum.inr i)) v := fun r v => by
    rw [hc₁]; rfl
  have e2 : ∀ r v, Complex.exp (lin₂ r v + c₂ r) = χ r * Complex.exp (Real.pi * hermForm Hm (F v) (F (per τ r)) +
      Real.pi / 2 * hermForm Hm (F (per τ r)) (F (per τ r))) := fun r v => by
    rw [show lin₂ r v + c₂ r = Complex.log (χ r) + (Real.pi * hermForm Hm (F v) (F (per τ r)) +
      Real.pi / 2 * hermForm Hm (F (per τ r)) (F (per τ r))) from by
        show (Real.pi : ℂ) * hermForm Hm (F v) (F (per τ r)) + (Complex.log (χ r) +
          Real.pi / 2 * hermForm Hm (F (per τ r)) (F (per τ r))) = _
        ring, Complex.exp_add, Complex.exp_log (hχ r)]
  have hfac : ∀ r v, Complex.exp (lin₁ r v + c₁ r) * ρ v = Complex.exp (lin₂ r v + c₂ r) * ρ (v + per τ r) := by
    intro r v
    have d₁ : Differentiable ℂ fun z => Complex.exp (lin₁ r z + c₁ r) * ρ z -
        Complex.exp (lin₂ r z + c₂ r) * ρ (z + per τ r) :=
      ((((LinearMap.toContinuousLinearMap (lin₁ r)).differentiable.add_const (c₁ r)).cexp).mul hρd).sub
        ((((LinearMap.toContinuousLinearMap (lin₂ r)).differentiable.add_const (c₂ r)).cexp).mul
          (hρd.comp (differentiable_id.add_const _)))
    rcases entire_eq_zero_or_eq_zero_of_mul_eq_zero _ (fun z => theta (Key.halfVec k) (Key.halfVec k') z τ) d₁
      (differentiable_theta hτ _ _) (fun z => by
        simp only [e1, e2]
        have h1 := h r z
        have h2 := qp r z
        linear_combination (-ρ z) * h2 - h1) with h0 | h0
    · exact sub_eq_zero.1 (h0 v)
    · exact absurd (funext h0) (theta_ne_zero hτ _ _)
  have key := alternating_eq_of_equivalent_factors (per τ) lin₁ lin₂ c₁ c₂ hρd.continuous hρ0 hfac p q
  set X := hermForm Hm (F (per τ p)) (F (per τ q)) with hX
  have k2 : -(2 * Real.pi * Complex.I) * (ofIntVec (fun i => p (Sum.inl i)) ⬝ᵥ per τ q) -
      -(2 * Real.pi * Complex.I) * (ofIntVec (fun i => q (Sum.inl i)) ⬝ᵥ per τ p) =
      (Real.pi : ℂ) * hermForm Hm (F (per τ q)) (F (per τ p)) - (Real.pi : ℂ) * X := key
  rw [hermForm_conj_symm_of_isHermitian Hm hH, ← hX, hper, hper, dotProduct_add, dotProduct_add] at k2
  have sym : ofIntVec (fun i => p (Sum.inl i)) ⬝ᵥ τ *ᵥ ofIntVec (fun i => q (Sum.inl i)) =
      ofIntVec (fun i => q (Sum.inl i)) ⬝ᵥ τ *ᵥ ofIntVec (fun i => p (Sum.inl i)) := by
    rw [dotProduct_mulVec, ← mulVec_transpose, hτ.1.eq, dotProduct_comm]
  have sc : X - star X = 2 * (X.im : ℂ) * Complex.I := by
    have := Complex.sub_conj X
    push_cast at this
    exact this
  have om : ((omegaStd p q : ℤ) : ℂ) = ofIntVec (fun i => p (Sum.inl i)) ⬝ᵥ ofIntVec (fun i => q (Sum.inr i)) -
      ofIntVec (fun i => q (Sum.inl i)) ⬝ᵥ ofIntVec (fun i => p (Sum.inr i)) := by
    simp only [omegaStd, ofIntVec, dotProduct, ← Finset.sum_sub_distrib]
    push_cast
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  have G : (2 * Real.pi * Complex.I) * (((omegaStd p q : ℤ) : ℂ) - (X.im : ℂ)) = 0 := by
    rw [om]
    linear_combination -k2 - (2 * Real.pi * Complex.I) * sym + (Real.pi : ℂ) * sc
  rcases mul_eq_zero.1 G with h0 | h0
  · exact absurd h0 Complex.two_pi_I_ne_zero
  · exact_mod_cast (sub_eq_zero.1 h0).symm

end GlobalTheory.WeilStd

namespace GlobalTheory.WeilStd

open GlobalTheory.NormalUnique in

theorem weilIs_per : ∀ (x : KeyIn ℂ) (g : ℕ) (u : HolUnif x.P.A x.P.L g) (τ : Matrix (Fin g) (Fin g) ℂ) (a b : Fin g → ℂ) (c : ℂ),
    x.P.g = g → τ.IsSymm → (τ.map Complex.im).PosDef → charHalf g a b → c ≠ 0 →
    (∀ z, z ∈ u.Λ ↔ ∃ m n : Fin g → ℤ, z = (fun i => (m i : ℂ)) + τ.mulVec (fun i => (n i : ℂ))) →
    u.IsFn x.th (fun z => c * thetaChar τ a b z) →
    ∀ (n : ℕ) (p q : Fin g ⊕ Fin g → ℤ) (e : ℂˣ), 0 < n →
      (e : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * (omegaStd p q : ℂ) / n) →
      Out.WeilIs x.P.A x.P.L n (u.ex ((n : ℂ)⁻¹ • per τ p)) (u.ex ((n : ℂ)⁻¹ • per τ q)) (unitOn e) := by
  intro x g u τ a b c hg hτs hτp hab hc hΛ hfn n p q e hn he
  subst hg
  obtain ⟨u₁, Hm, χ, Ef, hA, -, h1, h2, -, -, hE, -, hW⟩ := thetaUnifAV_all x.P x.rig x.rig_gen
  obtain ⟨F, hF, hFl, -, -⟩ := HomLinear.exists_linear_of_isMonHom x.P.A x.P.A x.P.isAb x.P.isAb x.P.L x.P.L
    x.P.g x.P.g u u₁ h1 h2 (𝟙 x.P.A) inferInstance
  simp only [Category.comp_id] at hF
  obtain ⟨ρ, hρd, hρ0, -, hρ⟩ := NormalUnique.exists_frame_ratio x.P.isLB u₁ u F hF
  obtain ⟨θ₁, hθ₁⟩ := exists_isFn x.P.isLB u₁ x.th
  have hT := (isThetaFn_and_ne_zero_of_isFn x u₁ Hm χ θ₁ hA hθ₁).1
  have hrel : ∀ z, c * thetaChar τ a b z = ρ z * θ₁ (F z) := hρ x.th θ₁ _ hθ₁ hfn
  have hmem : ∀ r, F (per τ r) ∈ u₁.Λ := fun r => hFl _ ((hΛ _).2
    ⟨fun i => r (Sum.inr i), fun i => r (Sum.inl i), by simp only [per]; rw [add_comm]⟩)
  obtain ⟨k, rfl⟩ : ∃ k : Fin x.P.g → ℤ, a = fun i => (k i : ℂ) / 2 :=
    ⟨fun i => if a i = 0 then 0 else 1, funext fun i => by rcases hab.1 i with h | h <;> simp [h]⟩
  obtain ⟨k', rfl⟩ : ∃ k : Fin x.P.g → ℤ, b = fun i => (k i : ℂ) / 2 :=
    ⟨fun i => if b i = 0 then 0 else 1, funext fun i => by rcases hab.2 i with h | h <;> simp [h]⟩
  simp only [SpMove.thetaChar_half] at hrel
  have hχ : ∀ l, χ l ≠ 0 := fun l => norm_ne_zero_iff.1 (by rw [hA.2.2.1]; exact one_ne_zero)
  have key := WeilStd.im_hermForm_per (τ := τ) ⟨hτs, hτp⟩ k k' hA.1 F ρ hρd hρ0 (fun r => χ ⟨_, hmem r⟩)
    (fun r => hχ _) (fun r z => by
      have eA := hrel (z + per τ r)
      have eB := hT.2 ⟨_, hmem r⟩ (F z)
      have eC := hrel z
      rw [pow_one] at eB
      rw [map_add] at eA
      apply mul_left_cancel₀ hc
      linear_combination (ρ (z + per τ r) * (χ ⟨_, hmem r⟩ * Complex.exp (Real.pi * hermForm Hm (F z) (F (per τ r)) +
        Real.pi / 2 * hermForm Hm (F (per τ r)) (F (per τ r))))) * eC - ρ z * eA - ρ z * ρ (z + per τ r) * eB) p q
  have hEf : Ef ⟨_, hmem p⟩ ⟨_, hmem q⟩ = omegaStd p q := by
    have := hE ⟨_, hmem p⟩ ⟨_, hmem q⟩
    rw [key] at this
    exact_mod_cast this
  have hw := hW n ⟨_, hmem p⟩ ⟨_, hmem q⟩ e hn (by rw [he, hEf])
  have e1 : u.ex ((n : ℂ)⁻¹ • per τ p) = u₁.ex ((n : ℂ)⁻¹ • F (per τ p)) := by rw [← map_smul, hF]
  have e2 : u.ex ((n : ℂ)⁻¹ • per τ q) = u₁.ex ((n : ℂ)⁻¹ • F (per τ q)) := by rw [← map_smul, hF]
  rw [e1, e2]
  exact hw

end GlobalTheory.WeilStd
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InConeOfMonomialMultipleStatement
section
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.TorRef

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.inCone_of_monomial_multiple : ∀ {R : Type} [CommRing R] [IsDomain R] (Dg : DegPre R) {m : ℕ} (t : Fin m → R) (γ δ : Fin m → LinearMap.BilinForm ℤ Dg.X) (N : ℕ), 0 < N → (∀ i, γ i = (N : ℤ) • δ i) → (∀ i y z, δ i y z = δ i z y) → (∀ i, δ i ≠ 0) → IsMonomial Dg t γ → InCone Dg δ := by
  first | exact @GlobalTheory.GenFan.inCone_of_isMonomial_smul | exact GlobalTheory.GenFan.inCone_of_isMonomial_smul | (intros; apply GlobalTheory.GenFan.inCone_of_isMonomial_smul <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InRealConeSelf
section
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.TorRef

noncomputable section

namespace GlobalTheory.ChartMono

section Mono

variable {R : Type} [CommRing R] [IsDomain R]

def TraitMono (Dg : DegPre R) (ℓ : LinearMap.BilinForm ℤ Dg.X →ₗ[ℤ] ℤ) (h : R) : Prop :=
  ∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W], CDvr W → ∀ ϖ : W, Irreducible ϖ → ∀ (f : R →+* W)
    (be : LinearMap.BilinForm ℤ Dg.X), (∀ y z, be y z = be z y) → FormAt Dg f ϖ be →
    ∀ k : ℕ, (k : ℤ) = ℓ be → Associated (f h) (ϖ ^ k)

theorem TraitMono.mul {Dg : DegPre R} {ℓ ℓ' : LinearMap.BilinForm ℤ Dg.X →ₗ[ℤ] ℤ} {h h' : R}
    (H : TraitMono Dg ℓ h) (H' : TraitMono Dg ℓ' h') (hn : ∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W],
      CDvr W → ∀ ϖ : W, Irreducible ϖ → ∀ (f : R →+* W) (be : LinearMap.BilinForm ℤ Dg.X), (∀ y z, be y z = be z y) →
      FormAt Dg f ϖ be → 0 ≤ ℓ be ∧ 0 ≤ ℓ' be) : TraitMono Dg (ℓ + ℓ') (h * h') := by
  intro W _ _ _ hW ϖ hϖ f be hs hf k hk
  obtain ⟨h1, h2⟩ := hn W hW ϖ hϖ f be hs hf
  obtain ⟨a, ha⟩ := Int.eq_ofNat_of_zero_le h1
  obtain ⟨b, hb⟩ := Int.eq_ofNat_of_zero_le h2
  have hk' : k = a + b := by
    have : (k : ℤ) = a + b := by rw [hk, LinearMap.add_apply, ha, hb]
    exact_mod_cast this
  rw [map_mul, hk', pow_add]
  exact (H W hW ϖ hϖ f be hs hf a ha.symm).mul_mul (H' W hW ϖ hϖ f be hs hf b hb.symm)

end Mono

section Cone

variable {X : Type} [AddCommGroup X]

def InRealCone {k : ℕ} (γ : Fin k → LinearMap.BilinForm ℤ X) (β : LinearMap.BilinForm ℤ X) : Prop :=
  ∃ c : Fin k → ℝ, (∀ i, 0 ≤ c i) ∧ toReal β = ∑ i, c i • toReal (γ i)

end Cone

end GlobalTheory.ChartMono
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IntBilinFormToRealMemBalancedPsdCone
section
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan

namespace GlobalTheory.PolFan

theorem toReal_mem_psdCone_of_nonneg : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X : Type)
    [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X] [Module.Projective (𝓞 E) X]
    (β : LinearMap.BilinForm ℤ X), β ∈ balForms H.bar X → (∀ y, 0 ≤ β y y) → toReal β ∈ psdCone H.bar X := by
  intro E _ _ _ H X _ _ _ _ β hβ hp
  have h := ConeSub.sum_smul_toReal_mem_psdCone (𝓞 E) H.bar X 1 (fun _ => β) (fun _ => 1)
    (fun _ => hβ) (fun _ y => hp y) (fun _ => zero_le_one)
  simpa using h

end GlobalTheory.PolFan
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsBilRatio
section
set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.L2.Pj GlobalTheory.RayEv GlobalTheory.RayHoriz
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.RayRos

section Series

variable {S : Type} [CommRing S] {ρ κ : Type}

def bil [Fintype ρ] (A : ρ → ρ → S) : MvPowerSeries (Fin 2 × ρ) S :=
  ∑ r, ∑ s, MvPowerSeries.C (A r s) * MvPowerSeries.X ((0 : Fin 2), r) * MvPowerSeries.X ((1 : Fin 2), s)

def quad [Fintype ρ] (B : ρ → ρ → S) : MvPowerSeries ρ S :=
  ∑ r, ∑ s, MvPowerSeries.C (B r s) * MvPowerSeries.X r * MvPowerSeries.X s

def qexp [Algebra ℚ S] (q : MvPowerSeries κ S) : MvPowerSeries κ S :=
  PowerSeries.subst q (PowerSeries.exp S)

end Series

section Ratio

variable {X : Scheme.{0}} {G : Over X} [GrpObj G] [IsCommMonObj G] {S : Type} [CommRing S] (x0 : Sp S ⟶ X)
  {ρ : Type} [Fintype ρ] [DecidableEq ρ] (L : LB G.left) {O : Type} [CommRing O]

def ratio6 (bar : O → O) (ch : ρ → O →+* S) {x : ∀ m, overAt x0 (Jet S ρ m) ⟶ G} (e : Fr x0 L x) (c : O) (m : ℕ)
    (y : (overAt x0 (Jet S (Fin 2 × ρ) m)).left)
    (J : ((overAt x0 (Jet S (Fin 2 × ρ) m)).left ⟶ G.left) → L.ι) :
    ((overAt x0 (Jet S (Fin 2 × ρ) m)).left.presheaf.stalk y)ˣ :=
  ev x0 L e ![fun r => ch r c, fun _ => 1] m y J * (ev x0 L e ![fun r => ch r c, fun _ => 0] m y J)⁻¹ *
    (ev x0 L e ![fun _ => 0, fun _ => 1] m y J)⁻¹ * (ev x0 L e ![fun _ => 1, fun r => ch r (bar c)] m y J)⁻¹ *
    ev x0 L e ![fun _ => 1, fun _ => 0] m y J * ev x0 L e ![fun _ => 0, fun r => ch r (bar c)] m y J

def IsBilRatio [Algebra ℚ S] (a : OAct O G) (bar : O → O) (ch : ρ → O →+* S) (x : ∀ m, overAt x0 (Jet S ρ m) ⟶ G)
    (e : Fr x0 L x) (c : O) (A : ρ → ρ → S)
    (w : LB.Gen (LB.LinComb L (rosatiφ G (a.act c) (a.act (bar c))) rosatiε)) : Prop :=
  w.IsGen ∧ (∀ y J, Good L y J → val w (zero2 G) y J = 1) ∧
    ∀ m y J, Good L y J → (val w (pt2 x0 x m).left y J).val * gs (𝟙 _) y ⊤ (toΓ _ (psJet m (qexp (bil A)))) =
      (ratio6 x0 L bar ch e c m y J).val

end Ratio

end GlobalTheory.RayRos
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsOpenAbelianLocus
section
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.TorRef GlobalTheory.Cartier
open MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AbLocusOpenGlobal

theorem exists_unit (S : Scheme.{0}) (s : S) :
    ∃ n : ℕ, 2 ≤ n ∧ s ∈ S.basicOpen (n : Γ(S, ⊤)) := by
  rcases IsLocalRing.isUnit_or_isUnit_of_isUnit_add (R := S.presheaf.stalk s) (a := (3 : S.presheaf.stalk s)) (b := -2)
      (by norm_num) with h | h
  · refine ⟨3, by norm_num, (S.mem_basicOpen_top _ s).2 ?_⟩
    rw [map_natCast]; exact_mod_cast h
  · refine ⟨2, le_rfl, (S.mem_basicOpen_top _ s).2 ?_⟩
    rw [map_natCast]; exact_mod_cast (IsUnit.neg_iff _).1 h

theorem isOpen_connectedComponent_of_noetherian {X : Type} [TopologicalSpace X] [NoetherianSpace X] (x : X) :
    IsOpen (connectedComponent x) := by
  rw [← isClosed_compl_iff, show (connectedComponent x)ᶜ = ⋃ Z ∈ {Z ∈ irreducibleComponents X | ¬ Z ⊆ connectedComponent x}, Z from
    Set.ext fun y => ⟨fun h => Set.mem_biUnion ⟨irreducibleComponent_mem_irreducibleComponents y, fun k => h (k mem_irreducibleComponent)⟩
      mem_irreducibleComponent, fun h k => by
      obtain ⟨Z, ⟨a, b⟩, c⟩ := Set.mem_iUnion₂.1 h
      exact b ((a.1.isConnected.isPreconnected.subset_connectedComponent c).trans (connectedComponent_eq k).ge)⟩]
  exact (NoetherianSpace.finite_irreducibleComponents.subset fun _ h => h.1).isClosed_biUnion fun Z h =>
    isClosed_of_mem_irreducibleComponents Z h.1

theorem exists_connected_open {S : Scheme.{0}} [IsLocallyNoetherian S] (N : S.Opens) (s : S) (hs : s ∈ N) :
    ∃ (V : Scheme.{0}) (w : V ⟶ S), IsOpenImmersion w ∧ ConnectedSpace V ∧ s ∈ Set.range w ∧
      Set.range w ⊆ (N : Set S) := by
  obtain ⟨U, hU, hsU, hUN⟩ := exists_isAffineOpen_mem_and_subset (X := S) (U := N) (x := s) hs
  have : IsAffine U := hU
  have : IsNoetherian U.toScheme := {}
  have : NoetherianSpace U.toScheme := inferInstance
  let V : U.toScheme.Opens := ⟨_, isOpen_connectedComponent_of_noetherian (X := U.toScheme) ⟨s, hsU⟩⟩
  have : ConnectedSpace V.toScheme := isConnected_iff_connectedSpace.1 isConnected_connectedComponent
  refine ⟨V.toScheme, V.ι ≫ U.ι, inferInstance, this, ⟨⟨⟨s, hsU⟩, mem_connectedComponent⟩, rfl⟩, ?_⟩
  rintro _ ⟨v, rfl⟩
  exact hUN (V.ι v).2

theorem isOpen_abLocus_of_locallyNoetherian {S : Scheme.{0}} [IsLocallyNoetherian S] (G : Over S) [GrpObj G]
    (hG : IsSemiAbelian G) : IsOpen (abLocus G) := by
  refine isOpen_iff_forall_mem_open.2 fun s hs => ?_
  obtain ⟨n, h2, hn⟩ := exists_unit S s
  obtain ⟨V, w, hw, hV, ⟨v, rfl⟩, hle⟩ := exists_connected_open _ s hn
  have hG' : IsSemiAbelian ((Over.pullback w).obj G) := IsSemiAbelian.pullback w G hG
  have := hG'.smooth
  have := hG'.geomConnected
  have : ConnectedSpace ((Over.pullback w).obj G).left := GeometricallyConnected.connectedSpace ((Over.pullback w).obj G).hom ((Over.pullback w).obj G).hom.isOpenMap
  obtain ⟨x₀⟩ : Nonempty ((Over.pullback w).obj G).left := inferInstance
  obtain ⟨g, hg⟩ := exists_dim_of_preconnected ((Over.pullback w).obj G).hom x₀
  have hu : IsUnit ((n : ℕ) : Γ(V, ⊤)) := by
    have h₀ := RingedSpace.isUnit_res_basicOpen S.toRingedSpace ((n : ℕ) : Γ(S, ⊤))
    have h₁ : (⊤ : V.Opens) ≤ w ⁻¹ᵁ S.basicOpen ((n : ℕ) : Γ(S, ⊤)) := fun y _ => hle ⟨y, rfl⟩
    have h₀' : IsUnit ((n : ℕ) : Γ(S, S.basicOpen ((n : ℕ) : Γ(S, ⊤)))) := by
      simp only [map_natCast] at h₀
      exact h₀
    have := h₀'.map (w.appLE _ ⊤ h₁).hom
    rwa [map_natCast] at this
  have hU := AbLocusOpen.isOpen_abLocus ((Over.pullback w).obj G) hG' hg h2 hu
  have key : ∀ y : V, w y ∈ abLocus G ↔ y ∈ abLocus ((Over.pullback w).obj G) := fun y =>
    abLocus_pullback abLocusOne hG (isGrpPullback_pullback G w).1 y
  refine ⟨w '' abLocus ((Over.pullback w).obj G), ?_, w.isOpenEmbedding.isOpenMap _ hU, ⟨v, (key v).1 hs, rfl⟩⟩
  rintro _ ⟨y, hy, rfl⟩
  exact (key y).2 hy

end GlobalTheory.AbLocusOpenGlobal

theorem GlobalTheory.AbLocusOpenGlobal.isOpen_abLocus_gmod : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H} {Xo : Moduli D l} {c : Coeff l} (Z : GMod Xo c), IsOpen (abLocus Z.t.G) := by
  intro E _ _ _ H D l Xo c Z
  have : IsLocallyNoetherian Z.X := (GlobalTheory.ModelRelCompare.densePart Z (GlobalTheory.CoeffRings.coeff_isDedFrac E H l c).1).1
  exact GlobalTheory.AbLocusOpenGlobal.isOpen_abLocus_of_locallyNoetherian Z.t.G Z.t.semi
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsProperOfCompleteDVRLiftGenericPointStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.L2.Pj GlobalTheory.RayEv
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isProper_of_completeDVR_lift_genericPoint : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (X : Scheme.{0}) [IsIntegral X] (f : X ⟶ Sp R) [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f], (∀ (V K : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [IsAdicComplete (IsLocalRing.maximalIdeal V) V] [Field K] [Algebra V K] [IsFractionRing V K] (x : Sp K ⟶ X) (y : Sp V ⟶ Sp R), Set.range x ⊆ {genericPoint X} → x ≫ f = spMap (algebraMap V K) ≫ y → ∃ x' : Sp V ⟶ X, spMap (algebraMap V K) ≫ x' = x) → IsProper f := by
  first | exact @GlobalTheory.TraitProper.isProper_of_lift_genericPoint | exact GlobalTheory.TraitProper.isProper_of_lift_genericPoint | (intros; apply GlobalTheory.TraitProper.isProper_of_lift_genericPoint <;> assumption)
end

