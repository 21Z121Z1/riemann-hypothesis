import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0014
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeIsometrySignFirst
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0042
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0006
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1055
import Development.AbelianVarietyTheory.Definitions.Divisors.IsTorsionFreeOfForallExists
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1058
import Development.AbelianVarietyTheory.Definitions.Divisors.DatumOfIsIntegersLattice
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.MulStableIntegral
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsDiscreteValuationRingValuationSubringAtPrime
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.AddMonoidHomEqZeroOfEventually
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0901
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
import GroundTheory.AutomorphicForms.MultiplicityOne.Bundle0001
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0933
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1022
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1036
import CompanionTheory.HarishChandraModules.LowKTypeMultiplicity.EigenspaceCyclicDensity.LowKMultOneP
import CompanionTheory.HarishChandraModules.LowKTypeMultiplicity.DiscreteSeriesCharacters.DiscreteSeriesInfinitesimalCharacter
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HolomorphicDiscreteSeries
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1020
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1042

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.VPEqSumHeisCore
section
noncomputable section

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

namespace GlobalTheory.DatumFourierCore

open NumberField Matrix Complex MeasureTheory IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.DatumFourier
open scoped TensorProduct Classical ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1600000 in

theorem thetaVector_eq_sum_heisenberg_core : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : Formalism.L2.DIV.FamIn D.what₂.LL G Pl0 T0 D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Hk3.Core R F → ∀ (i : Fin D.R.m), VStd D i → ∀ (H : Geo.Tor.Host D.host.E) (Dw : Datum H) (ι : Dw.La →ₗ[𝓞 D.host.E] (Fin (Wc D i).rank → D.host.E)), LatEmb (Wc D i) ι → LatIsom (Wc D i) Dw.EF ι → ∃ δ : ℤˣ, ∀ (t : T0) (l₂ : Geo.Tor.Level H) (φ : (Fin (Vc D i).rank → LevQc Dw l₂) → ℂ), PhiIs R i (RingHom.id ℂ) t ι (Mfr l₂ • ⊤) φ → (∀ PP, PP ∈ R.Pg ∨ PP ∈ R.Q t → l₂.Mb ≤ PP.asIdeal ∧ ((D.host.QS * D.host.q * Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal) → ∀ e : AE D, IsIdemSum e (R.Pg ∪ R.Q t) → R.vP i t = ((Nat.card (Fin (Vc D i).rank → LevQ Dw l₂) : ℂ))⁻¹ • ∑ᶠ q : Fin (Vc D i).rank → LevQ Dw l₂, hatC l₂ φ q • heisO R.ψ (Vc D i) (Wc D i) (Matrix.of fun a b => e * incA D (((δ : ℤ) : D.host.E) * ι (cSep l₂ • levRep (q b)) a / (l₂.M : D.host.E))) (R.vacP i) := by
  intro D G _ _ Pl0 T0 A Ks _ _ _ R F hR i hV H Dw ι hι hI
  obtain ⟨ε, hε⟩ := hI
  refine ⟨ε, fun t l φ hφ hP e he => ?_⟩
  obtain ⟨hvac, e₁, he₁, hθ⟩ := hR.thP.vP i t
  obtain ⟨e₂, he₂, hφ⟩ := hφ
  obtain rfl := idemSum_unique (Vc D i) he₁ he
  obtain rfl := idemSum_unique (Vc D i) he₂ he
  have hβV := hR.lev.βV i
  have hβW := hR.lev.βW i
  have hS := GlobalTheory.SDFrameLattice.isSelfDualC_of_isSDFrame D _ _ _ _ hβV
  have hT := GlobalTheory.SDFrameLattice.isSelfDualC_of_isSDFrame D _ _ _ _ hβW
  have hstd : R.ΛV i = Submodule.pi Set.univ fun _ => (1 : Submodule (𝓞 D.host.E) D.host.E) := by
    rw [GlobalTheory.PrincInLevel.eq_latC hβV, ← GlobalTheory.SplitReps.hLat_one, hV.2]
  have hlat := mem_latRat_iff hV.1 hstd hβW
  have hM : l.M ≠ 0 := by have := l.three_le; omega
  have hM' : (l.M : D.host.E) ≠ 0 := Nat.cast_ne_zero.2 hM
  have hsurj : ∀ M ∈ GlobalTheory.LatVac.latRat (Vc D i) (Wc D i) (R.ΛV i : Set (Fin (Vc D i).rank → D.host.E))
      (R.ΛW i : Set (Fin (Wc D i).rank → D.host.E)), ∃ x : Fin (Vc D i).rank → Dw.La, M = Matrix.of fun a b => ι (x b) a := by
    intro M hM
    choose x hx using fun b => hι.2.ge ((hlat M).1 hM b)
    exact ⟨x, Matrix.ext fun a b => (congrFun (hx b) a).symm⟩
  have hint : ∀ u ∈ latO (Vc D i) (Wc D i) (R.ΛV i : Set (Fin (Vc D i).rank → D.host.E))
      (R.ΛW i : Set (Fin (Wc D i).rank → D.host.E)) (fun _ => True),
      IsIntM (frMapAdj (Vc D i) (Wc D i) (R.βV i) (R.βW i) (cA D e • u)) := fun u hu =>
    int_of_mem_latO (fun M hM => by
      obtain ⟨x, rfl⟩ := hsurj M hM
      exact (hφ x).1) hu
  have : Finite (LevQ Dw l) := GlobalTheory.LevelPairing.finite_LevQ
  have := Fintype.ofFinite (Fin (Vc D i).rank → LevQ Dw l)
  rw [finsum_eq_sum_of_fintype, Finset.smul_sum]
  simp only [smul_smul]
  refine thetaAt_eq_sum _ _ hθ (fun q a b => ?_) fun w => ?_
  · rw [GlobalTheory.LatVac.cA_cA, Matrix.of_apply, ← mul_assoc, GlobalTheory.PlaceVec.idemSum_mul_self he]
  by_cases hw : w ∈ latO (Vc D i) (Wc D i) (R.ΛV i : Set (Fin (Vc D i).rank → D.host.E))
      (R.ΛW i : Set (Fin (Wc D i).rank → D.host.E)) (fun _ => True) ∧ IsHalf (cA D e) w
  swap
  · rw [halfInd, if_neg hw, zero_mul, if_neg]
    rintro ⟨h1, h2⟩
    have hN : ∀ PP ∈ R.Pg ∪ R.Q t, ((Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal := fun PP hPP h =>
      (hP PP (Finset.mem_union.1 hPP)).2 (by rw [Nat.cast_mul]; exact Ideal.mul_mem_left _ _ h)
    exact hw ⟨mem_latO_of_int hS hT hβV.choose_spec.1 hβW.choose_spec.1 he (Ideal.absNorm_eq_zero_iff.not.2 D.host.ccK_ne_bot)
      (ReciprocityTheory.ChartRestriction.G.PullbackSections.PfModelLatA.normCc_mem_AA D) hN h1 h2, h1⟩
  have hw' : cA D e • w = w := Matrix.ext hw.2
  obtain ⟨M, hM0, u, hu, hwM⟩ := approx_mod (Nat.pos_of_ne_zero hM) hw.1
  obtain ⟨x, rfl⟩ := hsurj M hM0
  have hfr : frMapAdj (Vc D i) (Wc D i) (R.βV i) (R.βW i) w =
      uMat (Vc D i) (Wc D i) (R.βV i) (R.βW i) e (fun b => ι (x b)) +
        l.M • frMapAdj (Vc D i) (Wc D i) (R.βV i) (R.βW i) (cA D e • u) := by
    rw [← hw', hwM, smul_add, GlobalTheory.PlaceVec.frMapAdj_add, frMapAdj_half, smul_comm]
    congr 1
    · exact one_smul _ _
    · exact (AddMonoidHom.mk' _ (GlobalTheory.PlaceVec.frMapAdj_add _ _ (R.βV i) (R.βW i))).map_nsmul _ _
  have hred : ∀ PP, PP ∈ R.Pg ∨ PP ∈ R.Q t → redM PP (frMapAdj (Vc D i) (Wc D i) (R.βV i) (R.βW i) w) =
      redM PP (uMat (Vc D i) (Wc D i) (R.βV i) (R.βW i) e (fun b => ι (x b))) := fun PP hPP => by
    rw [hfr]
    have : Ideal.span {(l.M : 𝓞 D.host.E)} ≤ l.Mb := l.prod ▸ Ideal.mul_le_left
    exact GlobalTheory.PlaceVec.redM_add_nsmul PP ((hP PP hPP).1 (this (Ideal.subset_span rfl))) (hφ x).1 (hint u hu)
  rw [halfInd, if_pos hw, one_mul, if_pos ⟨hw.2, hw' ▸ hint w hw.1⟩,
    GlobalTheory.PlaceVec.omegaK_congr _ fun PP h => hred PP (Or.inl h),
    GlobalTheory.PlaceVec.omegaQ_congr _ _ _ _ fun PP h => hred PP (Or.inr h), ← (hφ x).2, RingHom.id_apply, ← inversion l φ x]
  refine Finset.sum_congr rfl fun q _ => congrArg _ ?_
  have hY : (Matrix.of fun a b => ((ε : ℤ) : D.host.E) * ι (cSep l • levRep (q b)) a / (l.M : D.host.E)) =
      Matrix.of fun a b => (((ε : ℤ) : D.host.E) / (l.M : D.host.E)) * ι (cSep l • levRep (q b)) a :=
    Matrix.ext fun a b => by simp only [Matrix.of_apply]; ring
  refine Eq.trans ?_ (char_eq (Y := Matrix.of fun a b => ((ε : ℤ) : D.host.E) * ι (cSep l • levRep (q b)) a / (l.M : D.host.E))
    hvac.1 hS hT (GlobalTheory.PlaceVec.idemSum_infPart he) hw.2 hu hwM ((hlat _).2 fun b => ?_)).symm
  · rw [hY, hRat_std hV.1 _ _ _ (by rw [star_div₀, star_intCast, star_natCast]), ← Complex.exp_int_mul]
    congr 1
    have h1 : ∀ c : ℚ, ∀ z : D.host.E, Algebra.trace ℚ D.host.E (D.host.xi0 * ((c : D.host.E) * z)) =
        c * Algebra.trace ℚ D.host.E (D.host.xi0 * z) := fun c z => by
      rw [mul_left_comm, ← Rat.smul_def, map_smul, smul_eq_mul]
    have h2 : ∀ y z, Dw.EF y z = -Dw.EF z y := fun y z => (LinearMap.IsAlt.neg Dw.alt z y).symm
    have h3 : ((pairL (l := l) x (fun b => levRep (q b)) : ℤ) : ℚ) = -(((ε : ℤ) : ℚ) * Algebra.trace ℚ D.host.E (D.host.xi0 *
        ∑ b, (Wc D i).hT ((Wc D i).frame.equivFun.symm (ι (cSep l • levRep (q b)))) ((Wc D i).frame.equivFun.symm (ι (x b))))) := by
      rw [pairL, Int.cast_sum, Finset.mul_sum, map_sum, Finset.mul_sum, ← Finset.sum_neg_distrib]
      exact Finset.sum_congr rfl fun b _ => by rw [h2, Int.cast_neg, hε]
    have h4 := congrArg (fun z : ℚ => (z : ℂ)) h3
    rw [show (((ε : ℤ) : D.host.E) / (l.M : D.host.E)) = ((((ε : ℤ) : ℚ) / (l.M : ℚ) : ℚ) : D.host.E) by push_cast; rfl, h1]
    push_cast at h4 ⊢
    rw [h4]
    ring
  · have h1 := hι.2.le (LinearMap.mem_range_self ι ((ε : ℤ) • cSep l • levRep (q b)))
    convert h1 using 1
    funext a
    rw [map_zsmul, Matrix.smul_apply, Matrix.of_apply, nsmul_eq_mul, mul_div_cancel₀ _ hM', Pi.smul_apply, zsmul_eq_mul]

end GlobalTheory.DatumFourierCore

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.VecFockCore
section
open NumberField Matrix Complex MeasureTheory IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct Classical ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.AdTh.VecFockCore
open GlobalTheory.AdTh.VecFock

open scoped ComplexOrder

theorem vec_fock_core : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : Formalism.L2.DIV.FamIn D.what₂.LL G Pl0 T0 D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Hk3.Core R F → ∀ (i : Fin D.R.m) (t : T0), VStd D i → IsThetaFunO R.ψ (Vc D i) (Wc D i) (R.vP i t) ∧ (∀ τ, IsFockVacAt (heisO R.ψ (Vc D i) (Wc D i)) R.θ τ (cplxO 1 (cart (R.MW i (sg0 D A)) τ)) (R.vP i t)) ∧ (∀ τ, IsCartanInv (gramAt D (Wc D i) τ) (cart (R.MW i (sg0 D A)) τ)) ∧ (∀ τ, IsCartanInv (gramAt D (Vc D i) τ) 1) ∧ ∀ τ, IsONBasis (gramAt D (Wc D i) τ) (cart (R.MW i (sg0 D A)) τ) (onb (R.MW i (sg0 D A)) τ) ((Wc D i).sig (tauE D τ)).1 := by
  intro D G _ _ Pl0 T0 A Ks _ _ _ R F h i t hV
  have hθ : IsThetaFunO R.ψ (Vc D i) (Wc D i) (R.vP i t) := by
    have := h.thP.pt_theta i t 1
    unfold RealDat.ptP pureTensorO at this
    rwa [pureTensorL_one] at this
  refine ⟨hθ, GlobalTheory.DatumFock.isFockVacAt_thPVec _ _ _ _ (fun _ => 1) _ _ _ _ _ _ _ _ _ _ (h.thP.vP i t) hθ,
    isCartanInv_cart _, fun τ => ?_, fun τ => isONBasis_onb _ τ _ (h.models.order i τ)⟩
  have : gramAt D (Vc D i) τ = 1 := by
    unfold gramAt
    rw [hV.1]
    exact Matrix.map_one _ (map_zero _) (map_one _)
  rw [this]
  exact ⟨by simp, by simp, by simpa using Matrix.PosDef.one⟩

end GlobalTheory.AdTh.VecFockCore
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.VectorBundleOfFreeStalks
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.VB

namespace GlobalTheory.VB

theorem nonempty_basis_of_localizedModule {R M N ι : Type*} (B : Type*) [CommRing R] [CommRing B]
    [Algebra R B] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N] [Module B N]
    [IsScalarTower R B N] (S : Submonoid R) [IsLocalization S B] (f : M →ₗ[R] N)
    [IsLocalizedModule S f] (b : Module.Basis ι (Localization S) (LocalizedModule S M)) :
    Nonempty (Module.Basis ι B N) := by
  let e : Localization S ≃ₐ[R] B := IsLocalization.algEquiv S _ _
  let : Module (Localization S) N := Module.compHom N e.toRingEquiv.toRingHom
  have hs (a : Localization S) (n : N) : a • n = e a • n := rfl
  have : IsScalarTower R (Localization S) N := ⟨fun r a n => by
    rw [hs, hs, map_smul, smul_assoc]⟩
  let φ := (IsLocalizedModule.iso S f).extendScalarsOfIsLocalization S (Localization S)
  exact ⟨(b.map φ).mapCoeffs e.toRingEquiv fun _ _ => rfl⟩

theorem isFrame_of_basis_affine {X : Scheme.{0}} {F : X.Modules} [F.IsQuasicoherent]
    {U : X.Opens} (hU : IsAffineOpen U) {ι : Type} [Fintype ι]
    (b : Module.Basis ι Γ(X, U) Γ(F, U)) : IsFrame (F := F) (U := U) b := by
  refine isFrame_of_forall_exists fun V h y hy => ?_
  obtain ⟨W, hW, hyW, hle⟩ := QCoh.exists_affine_mem_le y hy
  refine ⟨W, hle, hyW, ?_⟩
  let := QCoh.resAlgebra (hle.trans h)
  let := QCoh.resModule F (hle.trans h)
  have := QCoh.res_isScalarTower F (hle.trans h)
  let c := (QCoh.isBaseChange_resLinear F hU hW (hle.trans h)).basis b
  have hc (i : ι) : c i = Twist.resM F (hle.trans h) (b i) := by
    rw [IsBaseChange.basis_apply]
    rfl
  have : Fintype.linearCombination Γ(X, W) (fun i => Twist.resM F (hle.trans h) (b i)) =
      c.equivFun.symm.toLinearMap := by
    ext a : 1
    simp [Fintype.linearCombination_apply, hc]
  rw [this]
  exact c.equivFun.symm.bijective

theorem isVB_of_basis_stalk (X : Scheme.{0}) [IsLocallyNoetherian X] (F : X.Modules)
    [GlobalTheory.QCoh.IsFiniteQC F] (r : ℕ)
    (h : ∀ x : X, Nonempty (Module.Basis (Fin r) (X.presheaf.stalk x) (F.presheaf.stalk x :))) :
    IsVB F r := by
  intro x
  obtain ⟨U, hU, hx, -⟩ := QCoh.exists_affine_mem_le (U := ⊤) x trivial
  obtain ⟨y, rfl⟩ : ∃ y : U, y.1 = x := ⟨⟨x, hx⟩, rfl⟩
  obtain ⟨b⟩ := h y
  have := QCoh.finite_sections F hU
  have : IsNoetherianRing Γ(X, U) := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
  have : Module.FinitePresentation Γ(X, U) Γ(F, U) := Module.finitePresentation_of_finite _ _
  have := QCoh.isLocalizedModule_germLinear F hU y
  have := hU.isLocalization_stalk y
  obtain ⟨f, hf, b', -⟩ := Module.FinitePresentation.exists_basis_localizedModule_powers
    (hU.primeIdealOf y).asIdeal.primeCompl (QCoh.germLinear F y) (X.presheaf.stalk (y : X)) b
  have := hU.isLocalization_basicOpen f
  have := QCoh.isLocalizedModule_resBasicOpen F hU f
  obtain ⟨c⟩ := nonempty_basis_of_localizedModule Γ(X, X.basicOpen f) (.powers f)
    (QCoh.resBasicOpen F f) b'
  exact ⟨X.basicOpen f, c, (QCoh.mem_primeCompl_primeIdealOf_iff hU y f).1 hf,
    isFrame_of_basis_affine (hU.basicOpen f) c⟩

end GlobalTheory.VB
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeierstrassModelUnitDiscriminantAwayFromPStatement
section
open NumberField IsDedekindDomain WeierstrassCurve GlobalTheory GlobalTheory.Published GlobalTheory.CMModel Formalism.L2.Th1.F
open scoped IntermediateField BigOperators Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weierstrassModel_unit_discriminant_away_from_p : ∀ (p : ℕ) (F : IntermediateField ℚ ℂ) (L : PeriodPair) (t : ℂ), p.Prime → p % 4 = 3 → 3 < p → Datum p F L t → sqProd p L t ∈ F → ∀ V : ValuationSubring ℂ, V.valuation (p : ℂ) = 1 → ModelAt V F (latticeCurve L) 1 := by
  first | exact @GlobalTheory.CMModel.modelAt_one_of_sqProd_mem | exact GlobalTheory.CMModel.modelAt_one_of_sqProd_mem | (intros; apply GlobalTheory.CMModel.modelAt_one_of_sqProd_mem <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WhittakerRelationPassesToSemiLocalSpan
section
noncomputable section

open NumberField IsDedekindDomain GlobalTheory.CuspRep Formalism.UG GlobalTheory.LFun Matrix MeasureTheory

namespace GlobalTheory.JSW.MirSemi

open GlobalTheory.JSW

theorem whit_rt_apply {E : Type} [Field E] [NumberField E] {a : ℕ} (F : GA E a → ℂ) (h g : GA E a) :
    whit (fun x => F (x * h)) g = whit F (g * h) := by
  simp only [whit, GroundTheory.Automorphic.FourierWhittaker.whittaker, mul_assoc]

theorem whit_zero_apply {E : Type} [Field E] [NumberField E] {a : ℕ} (g : GA E a) :
    whit (0 : GA E a → ℂ) g = 0 := by
  simp [whit, GroundTheory.Automorphic.FourierWhittaker.whittaker]

theorem mul_mem_supS' {E : Type} [Field E] [NumberField E] {a : ℕ} {S : Finset (HeightOneSpectrum (𝓞 E))}
    {x h : GA E a} (hx : x ∈ supS E a S) (hh : h ∈ supS E a S) : x * h ∈ supS E a S := by
  intro w hw
  rw [map_mul, hx w hw, hh w hw, one_mul]

theorem infGL_mem_supS' {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ} (S : Finset (HeightOneSpectrum (𝓞 E)))
    (y : GL (Fin a) (Cinf E)) : infGL E a y ∈ supS E a S := by
  intro w _
  have h1 : GeneralLinearGroup.map ((pLoc E w).comp (pFin E)) (infGL E a y) =
      GeneralLinearGroup.map (pLoc E w) (GeneralLinearGroup.map (pFin E) (infGL E a y)) := by
    ext i j; rfl
  rw [h1, pFin_infGL, map_one]

theorem whit_rel_locSpan : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (S : Finset (HeightOneSpectrum (𝓞 E))) (π : CuspSub E a) (φ : Sm E a), φ ∈ π.V → ∀ (t : GA E a) (c : ℂ), GeneralLinearGroup.map (pInf E) t = 1 → (∀ w ∈ S, GeneralLinearGroup.map ((pLoc E w).comp (pFin E)) t = 1) → (∀ x ∈ GlobalTheory.JSW.supS E a S, GlobalTheory.JSW.whit φ.1 (x * t) = c * GlobalTheory.JSW.whit φ.1 x) → ∀ F ∈ GlobalTheory.JSW.MirSemi.locSpan S φ.1, ∀ x ∈ GlobalTheory.JSW.supS E a S, GlobalTheory.JSW.whit F (x * t) = c * GlobalTheory.JSW.whit F x := by
  intro E _ _ _ a S π φ hφ t c htInf htS hrel
  have hreg := GlobalTheory.T.cusp_form_moderate_growth_compact E a S π φ hφ
  have hlin : ∀ F ∈ locSpan S φ.1, ∀ G ∈ locSpan S φ.1, ∀ (c' : ℂ) (g : GA E a),
      whit (fun x => F x + c' * G x) g = whit F g + c' * whit G g := fun F hF G hG =>
    (GlobalTheory.T.globalWhittakerCoefficient_linear_archimedeanKernel E a F G (hreg F hF).1 (hreg G hG).1 (hreg F hF).2 (hreg G hG).2).1
  let V : Submodule ℂ (GA E a → ℂ) :=
    { carrier := {F | F ∈ locSpan S φ.1 ∧ ∀ x ∈ supS E a S, whit F (x * t) = c * whit F x}
      add_mem' := by
        rintro F G ⟨hF, hF'⟩ ⟨hG, hG'⟩
        refine ⟨add_mem hF hG, fun x hx => ?_⟩
        have e : (F + G) = fun y => F y + 1 * G y := by funext y; simp
        rw [e, hlin F hF G hG, hlin F hF G hG, hF' x hx, hG' x hx]; ring
      zero_mem' := ⟨zero_mem _, fun x _ => by rw [whit_zero_apply, whit_zero_apply, mul_zero]⟩
      smul_mem' := by
        rintro c' F ⟨hF, hF'⟩
        refine ⟨Submodule.smul_mem _ c' hF, fun x hx => ?_⟩
        have e : (c' • F) = fun y => (0 : GA E a → ℂ) y + c' * F y := by funext y; simp
        rw [e, hlin 0 (zero_mem _) F hF, hlin 0 (zero_mem _) F hF, whit_zero_apply, whit_zero_apply, hF' x hx]
        ring }
  have hV : locSpan S φ.1 ≤ V := by
    refine locSpan_le ⟨self_mem_locSpan, hrel⟩ ?_ ?_
    · rintro F ⟨hF, hF'⟩ h hh
      refine ⟨rt_mem_locSpan hF hh, fun x hx => ?_⟩
      rw [whit_rt_apply, whit_rt_apply, mul_assoc, ← GlobalTheory.T.adelicGL_complementary_supports_commute E a S h t hh htInf htS, ← mul_assoc]
      exact hF' (x * h) (mul_mem_supS' hx hh)
    · rintro F ⟨hF, hF'⟩ X _ ν _ k γ hk
      refine ⟨kerInf_mem_locSpan hF ν hk, fun x hx => ?_⟩
      have hker := (GlobalTheory.T.globalWhittakerCoefficient_linear_archimedeanKernel E a F F (hreg F hF).1 (hreg F hF).1 (hreg F hF).2 (hreg F hF).2).2 X ν k γ hk
      rw [hker, hker, ← integral_const_mul]
      congr 1
      funext y
      have hc := GlobalTheory.T.adelicGL_complementary_supports_commute E a S (infGL E a (γ y)) t (infGL_mem_supS' S (γ y)) htInf htS
      rw [mul_assoc x t, ← hc, ← mul_assoc, hF' _ (mul_mem_supS' hx (infGL_mem_supS' S (γ y)))]
      ring
  intro F hF x hx
  exact (hV hF).2 x hx

end GlobalTheory.JSW.MirSemi
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WordReachingIrreducibleKModuleReachesHighestWeig
section
open Matrix GlobalTheory.HolDS
open Formalism.REAL (GlRel IsUnitary IsWeight KHighest root Jm inG)
open Formalism.QuantumDeterminants (lowK IsHCParam)
open Formalism.MainNotions.S (IsURepOn IsIrredOn UJset IsKFin IsKTypeOf IsKStableOn IsDS lowKSub vNormSq)
open CompanionTheory.D.DSIC (KRel KUnit KStab IsSmMod)
open CompanionTheory.D.LK (IsKMod IsMin)
open scoped InnerProductSpace

namespace GlobalTheory.HdStep

theorem proj_comm {n : ℕ} {ε : Fin n → Bool} {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    {E : Fin n → Fin n → Module.End ℂ V} (hU : KUnit ε E) (L : Submodule ℂ V) [L.HasOrthogonalProjection]
    (hL : KStab ε E L) (a b : Fin n) (hab : ε a = ε b) (y : V) :
    L.starProjection (E a b y) = E a b (L.starProjection y) := by
  apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero
  · exact hL a b hab _ (L.starProjection_apply_mem y)
  · intro z hz
    rw [← map_sub, hU a b hab]
    exact Submodule.starProjection_inner_eq_zero y _ (hL b a hab.symm z hz)

theorem main : ∀ (n : ℕ) (ε : Fin n → Bool) (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] (E : Fin n → Fin n → Module.End ℂ V), GlRel E → KUnit ε E → ∀ L : Submodule ℂ V, FiniteDimensional ℂ L → KStab ε E L → ∀ Λ : Fin n → ℝ, (∀ ν : Fin n → ℝ, ∀ x ∈ L, x ≠ 0 → KHighest ε E ν x → ν = Λ) → ∀ (μ : Fin n → ℝ) (w : V), KHighest ε E μ w → ∀ (s t : Bool) (l : List (Fin n × Fin n)), (∀ p ∈ l, ε p.1 = s ∧ ε p.2 = t) → ∀ x ∈ L, ⟪x, (l.map fun p : Fin n × Fin n => E p.1 p.2).prod w⟫_ℂ ≠ 0 → ∃ l' : List (Fin n × Fin n), l'.length = l.length ∧ (∀ p ∈ l', ε p.1 = s ∧ ε p.2 = t) ∧ μ + (l'.map fun p : Fin n × Fin n => root p.1 p.2).sum = Λ := by
  intro n ε V _ _ E hG hU L hfd hL Λ hΛ μ w hw s t l hl x hx hxl
  haveI : FiniteDimensional ℂ L := hfd
  let word : List (Fin n × Fin n) → V := fun l => (l.map fun p : Fin n × Fin n => E p.1 p.2).prod w
  let ht : List (Fin n × Fin n) → ℤ := fun l => (l.map fun p : Fin n × Fin n => ((p.2 : ℕ) : ℤ) - ((p.1 : ℕ) : ℤ)).sum
  let S : Set (List (Fin n × Fin n)) :=
    {l' | l'.length = l.length ∧ (∀ p ∈ l', ε p.1 = s ∧ ε p.2 = t) ∧ L.starProjection (word l') ≠ 0}
  have hSfin : S.Finite := (List.finite_length_eq (Fin n × Fin n) l.length).subset (fun l' h => h.1)
  have hlS : l ∈ S := by
    refine ⟨rfl, hl, fun h0 => hxl ?_⟩
    have hPx : L.starProjection x = x := Submodule.starProjection_eq_self_iff.mpr hx
    rw [← hPx, Submodule.inner_starProjection_left_eq_right]
    change ⟪x, L.starProjection (word l)⟫_ℂ = 0
    rw [h0, inner_zero_right]
  obtain ⟨l', hl'S, hmax⟩ := Set.exists_max_image S ht hSfin ⟨l, hlS⟩
  refine ⟨l', hl'S.1, hl'S.2.1, ?_⟩
  set u := L.starProjection (word l') with hu
  have huL : u ∈ L := L.starProjection_apply_mem _
  have hwt := GlobalTheory.T.isWeight_word_apply_weightVector n V E hG μ w hw.1 l'
  refine hΛ _ u huL hl'S.2.2 ⟨?_, ?_⟩
  · intro a
    rw [hu, ← proj_comm hU L hL a a rfl, hwt a, map_smul]
  · intro c d hcd hcd'
    rw [hu, ← proj_comm hU L hL c d hcd']
    have hspan := GlobalTheory.T.compactRaising_word_mem_span_higherWords n ε V E hG w c d hcd hcd' (hw.2 c d hcd hcd') s t l' hl'S.2.1
    have hle : Submodule.span ℂ {y : V | ∃ l'' : List (Fin n × Fin n), l''.length = l'.length ∧
        (∀ p ∈ l'', ε p.1 = s ∧ ε p.2 = t) ∧
        (l'.map fun p : Fin n × Fin n => ((p.2 : ℕ) : ℤ) - ((p.1 : ℕ) : ℤ)).sum <
          (l''.map fun p : Fin n × Fin n => ((p.2 : ℕ) : ℤ) - ((p.1 : ℕ) : ℤ)).sum ∧
        y = (l''.map fun p : Fin n × Fin n => E p.1 p.2).prod w} ≤
        LinearMap.ker (L.starProjection : V →ₗ[ℂ] V) := by
      rw [Submodule.span_le]
      rintro y ⟨l'', hlen, htyp, hlt, rfl⟩
      simp only [SetLike.mem_coe, LinearMap.mem_ker, ContinuousLinearMap.coe_coe]
      by_contra hne
      have hS'' : l'' ∈ S := ⟨hlen.trans hl'S.1, htyp, hne⟩
      exact absurd (hmax l'' hS'') (not_le.mpr hlt)
    exact LinearMap.mem_ker.mp (hle hspan)

end GlobalTheory.HdStep
end

