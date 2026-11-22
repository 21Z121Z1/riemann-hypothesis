import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0777
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0278
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0239
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.VacuumTranslateConjugateJetBound
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ConjugateCurveDatumLatticeIsCurveLattice
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CmThetaComplexConjugationCompatible
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0296
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaTaylorCoeffsAlgebraicAtComplexMultiplicatio
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0326
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0251
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0076
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0080
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0215
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0045
import Formalism.LocalToGlobal.GlobalTheory.GL5.FamilyMassVolumeIdentityOfClassDecomp
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsClosedImmersionGenericPoint
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0858
import Development.AbelianVarietyTheory.Definitions.Divisors.AevalEqZeroOfMemConeIdeal
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.ExistsAlgebraicIndependentGenericPoint
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ProjPointIdealMemProjComponentsOfIsProjPureDim
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsFormDegreeLeHilbertDegreeEvalNeZero
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0040
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0963
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0032
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
import GroundTheory.AutomorphicForms.MultiplicityOne.Bundle0001
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0958
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0127
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Bundle0008

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAlgebraicNumbersExtensionConjVacuumNormSq
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker GlobalTheory.IndefiniteRowSideFullHecke.PlaceLogThetaBounds GlobalTheory.ColNorms
open scoped ComplexOrder

namespace GlobalTheory.ConjVacuumNorm

theorem area_lamConj_pos (D : D7) (cc : Ideal (𝓞 D.host.K)) (dl : ℂ) (hc : StandardLatticesGL3.Crv D cc dl)
    (M : IntermediateField ℚ ℂ) (ρ : M →ₐ[ℚ] ℂ) (hD : TaylorLogMetric.DataIn D (TaylorLogMetric.tor0 D cc dl) M) :
    0 < TaylorLogMetric.area (TaylorLogMetric.lamConj M ρ (TaylorLogMetric.lamOf D cc dl)) := by
  have g1 := (GlobalTheory.InducedType.induced_type D).1
  obtain ⟨hK | hK, hT, -⟩ := GlobalTheory.ThetaConj.useBar_holds D cc dl hc M ρ hD
  · obtain ⟨cc', δ', hc', -, hl⟩ :=
      GlobalTheory.ConjCurve.galCurve_holds D cc dl hc M ρ hK hD.2.1 hD.2.2 1 one_pos
    rw [hl]
    exact GlobalTheory.ConjJet.area_pos D g1 cc' δ' hc'
  · obtain ⟨cc', δ', hc', -, hl⟩ :=
      GlobalTheory.ConjCurve.galCurve_holds D cc dl hc M _ hK hD.2.1 hD.2.2 1 one_pos
    have hL : TaylorLogMetric.lamConj M (StandardLatticesGL3.rhoBar M ρ) (TaylorLogMetric.lamOf D cc dl) =
        (TaylorLogMetric.lamConj M ρ (TaylorLogMetric.lamOf D cc dl)).map (starRingEnd ℂ).toAddMonoidHom :=
      congrArg TaylorLogMetric.Tor.abelian₂ hT
    rw [← GlobalTheory.ConjJet.area_conj, ← hL, hl]
    exact GlobalTheory.ConjJet.area_pos D g1 cc' δ' hc'

theorem exists_extension_normSq_eq : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (dl : ℂ) (t0 : ℂ), StandardLatticesGL3.Crv D cc dl → GL3Theta.IsTwoTorsionPointUnkilled D (TaylorLogMetric.lamOf D cc dl) t0 → ∀ (M : IntermediateField ℚ ℂ) [FiniteDimensional ℚ M] (ρ : M →ₐ[ℚ] ℂ), TaylorLogMetric.DataIn D (TaylorLogMetric.tor0 D cc dl) M → ∃ ρ' : TaylorLogMetric.Qbar →ₐ[ℚ] ℂ, (∀ x ∈ M, x ∈ TaylorLogMetric.Qbar ∧ StandardLatticesGL3.cj TaylorLogMetric.Qbar ρ' x = StandardLatticesGL3.cj M ρ x) ∧ TaylorLogMetric.lamConj TaylorLogMetric.Qbar ρ' (TaylorLogMetric.lamOf D cc dl) = TaylorLogMetric.lamConj M ρ (TaylorLogMetric.lamOf D cc dl) ∧ 0 < TaylorLogMetric.area (TaylorLogMetric.lamConj M ρ (TaylorLogMetric.lamOf D cc dl)) ∧ ∀ (a b : ℕ) (L : Submodule (𝓞 D.host.E) (Fin a → D.host.E)) (L' : Submodule (𝓞 D.host.E) (Fin b → D.host.E)) (L₀ : Submodule (𝓞 D.host.E) (Fin a → D.host.E)) (L₀' : Submodule (𝓞 D.host.E) (Fin b → D.host.E)), StandardLatticesGL3.SD D L → StandardLatticesGL3.SD D L' → StandardLatticesGL3.SD D L₀ → StandardLatticesGL3.SD D L₀' → Even (a * b) → ∀ F F₀ : TaylorLogMetric.VC D a b → ℂ, StandardLatticesGL3.ThetaVectorUpToUnits D (TaylorLogMetric.tor0 D cc dl) t0 L L' F → StandardLatticesGL3.ThetaVectorUpToUnits D (TaylorLogMetric.tor0 D cc dl) t0 L₀ L₀' F₀ → TaylorLogMetric.CoefIn D F₀ M → TaylorLogMetric.normSq D (TaylorLogMetric.torConj D (TaylorLogMetric.tor0 D cc dl) TaylorLogMetric.Qbar ρ') (TaylorLogMetric.La D (TaylorLogMetric.torConj D (TaylorLogMetric.tor0 D cc dl) TaylorLogMetric.Qbar ρ') L L') (TaylorLogMetric.fnConj D TaylorLogMetric.Qbar ρ' F) = TaylorLogMetric.normSq D (TaylorLogMetric.torConj D (TaylorLogMetric.tor0 D cc dl) M ρ) (TaylorLogMetric.La D (TaylorLogMetric.torConj D (TaylorLogMetric.tor0 D cc dl) M ρ) L₀ L₀') (TaylorLogMetric.fnConj D M ρ F₀) := by
  intro D cc dl t0 hc ht M _ ρ hD
  have g1 := (GlobalTheory.InducedType.induced_type D).1
  obtain ⟨ρ', hρ'⟩ := GlobalTheory.ThetaConj.exists_cj_Qbar_eq M ρ
  have hle : ∀ x ∈ M, x ∈ TaylorLogMetric.Qbar := fun x hx =>
    mem_algebraicClosure_iff.mpr
      ((Algebra.IsAlgebraic.isAlgebraic (R := ℚ) (⟨x, hx⟩ : M)).algHom M.val)
  have he : ∀ x ∈ M, ρ' (TaylorLogMetric.liftM TaylorLogMetric.Qbar x) = ρ (TaylorLogMetric.liftM M x) := fun x hx =>
    (hρ' x (hle x hx) hx).symm
  have hl : TaylorLogMetric.lamConj TaylorLogMetric.Qbar ρ' (TaylorLogMetric.lamOf D cc dl) = TaylorLogMetric.lamConj M ρ (TaylorLogMetric.lamOf D cc dl) := by
    unfold TaylorLogMetric.lamConj
    rw [he (TaylorLogMetric.g2 (TaylorLogMetric.lamOf D cc dl)) hD.2.1, he (TaylorLogMetric.g3 (TaylorLogMetric.lamOf D cc dl)) hD.2.2]
  refine ⟨ρ', fun x hx => ⟨hle x hx, he x hx⟩, hl, area_lamConj_pos D cc dl hc M ρ hD, ?_⟩
  intro a b L L' L₀ L₀' h1 h2 h3 h4 hev F F₀ hF hF₀ hC
  obtain ⟨hQ, -⟩ := (GlobalTheory.CurveAlgebraic.integral_j_and_algebraic_data D g1).2 cc dl hc
  obtain ⟨hA, -⟩ := GlobalTheory.ThetaAlgebraic.taylor_algebraic D cc dl hc t0 ht a b L L' h1 h2 hev F hF
  obtain ⟨t', ht'⟩ := (GlobalTheory.TwoTorsionPt.exists_point D cc dl hc).2 M ρ hD.2.1 hD.2.2
  obtain ⟨n1, -⟩ := GlobalTheory.ConjNorm.useNorm_all D cc dl hc t0 ht a b L L' h1 h2 hev F hF
    TaylorLogMetric.Qbar ρ' hQ hA t' (hl ▸ ht')
  obtain ⟨n2, -⟩ := GlobalTheory.ConjNorm.useNorm_all D cc dl hc t0 ht a b L₀ L₀' h3 h4 hev F₀ hF₀
    M ρ hD hC t' ht'
  rw [n1, n2, hl]

end GlobalTheory.ConjVacuumNorm
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsArchimedeanLiftUnitaryGroupProduct
section
open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR GlobalTheory.HolDict
open scoped TensorProduct InnerProductSpace ContDiff
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped Classical

noncomputable section

namespace GlobalTheory.RealLift

open GlobalTheory.PointAtPlaceHom

variable {D : D7}

def prodAt (θ : InfFam D) (V : HSp D) (l : List D.what₂.Tau) (u : D.what₂.Tau → Mt V.rank) : GA D V :=
  (l.map fun τ => atTau θ V τ (u τ)).prod

theorem prodAt_mem (θ : InfFam D) (V : HSp D) (l : List D.what₂.Tau) (u : D.what₂.Tau → Mt V.rank) :
    prodAt θ V l u ∈ GinfC V := by
  refine Subgroup.list_prod_mem _ fun x hx => ?_
  obtain ⟨τ, -, rfl⟩ := List.mem_map.1 hx
  exact atTau_mem V τ _

theorem infMat_prodAt {θ : InfFam D} (hθ : IsInfFam θ) (V : HSp D) {u : D.what₂.Tau → Mt V.rank}
    (hu : u ∈ UG (gramAt D V)) (ρ : D.what₂.Tau) (l : List D.what₂.Tau) (hl : l.Nodup) :
    infMat D.sp.cm.sig V.gram (θ ρ) (prodAt θ V l u) = if ρ ∈ l then u ρ else 1 := by
  induction l with
  | nil => rw [if_neg List.not_mem_nil]; exact infMat_one V _
  | cons τ l ih =>
    have e : prodAt θ V (τ :: l) u = atTau θ V τ (u τ) * prodAt θ V l u := List.prod_cons
    have hs := atTau_spec hθ V τ (hu τ)
    rw [List.nodup_cons] at hl
    rw [e, infMat_mul, ih hl.2]
    by_cases c : ρ = τ
    · subst c
      rw [hs.2.1, if_neg hl.1, if_pos List.mem_cons_self, Matrix.mul_one]
    · rw [hs.2.2 ρ c, Matrix.one_mul]
      simp only [List.mem_cons, c, false_or]

theorem continuousOn_prodAt {θ : InfFam D} (hθ : IsInfFam θ) (V : HSp D) (l : List D.what₂.Tau) :
    ContinuousOn (prodAt θ V l) (UG (gramAt D V)) := by
  induction l with
  | nil => exact continuousOn_const
  | cons τ l ih =>
    have e : prodAt θ V (τ :: l) = fun u => atTau θ V τ (u τ) * prodAt θ V l u := funext fun _ => List.prod_cons
    have : IsTopologicalGroup (GA D V) := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA _ _
    have c : ContinuousOn (fun u : D.what₂.Tau → Mt V.rank => atTau θ V τ (u τ)) (UG (gramAt D V)) :=
      (continuousOn_atTau hθ V τ).comp (continuous_apply τ).continuousOn fun u hu => hu τ
    rw [e]
    exact c.mul ih

theorem archM_mem {θ : InfFam D} (hθ : IsInfFam θ) (V : HSp D) (g : GA D V) (τ : D.what₂.Tau) :
    archM V (θ τ) g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ) := by
  obtain ⟨θ₀, h₀⟩ := (GlobalTheory.Member.infiniteAdele_bijective D).1
  have e : θ = fun ρ => θ₀ (tauE D ρ) := (GlobalTheory.SmoothForms.RealPts.realPoints D).1 _ _ hθ fun ρ => h₀ _
  subst e
  exact (GlobalTheory.Member.Arch.unit_iff _ _ _).1 (((GlobalTheory.Member.Arch.archM_spec D V θ₀ h₀).1 _).2.2.2.2 g)

theorem exists_real_lift : ∀ (D : D7) (θ : InfFam D) (V : HSp D), IsInfFam θ → ∃ L : (D.what₂.Tau → Mt V.rank) → GA D V, (∀ u ∈ UG (gramAt D V), L u ∈ GinfC V ∧ ∀ τ, archM V (θ τ) (L u) = u τ) ∧ (∀ u ∈ UG (gramAt D V), ∀ u' ∈ UG (gramAt D V), L (u * u') = L u * L u') ∧ ContinuousOn L (UG (gramAt D V)) ∧ (∀ g, (fun τ => archM V (θ τ) g) ∈ UG (gramAt D V)) ∧ (∀ u ∈ GinfC V, L (fun τ => archM V (θ τ) u) = u) ∧ (∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ), atTau θ V τ g = L (Pi.mulSingle τ g)) ∧ (∀ g, ∃ a ∈ GfC V, ∃ u ∈ GinfC V, g = a * u) ∧ (∀ a ∈ GfC V, ∀ u ∈ GinfC V, a * u = u * a) ∧ ∀ τ, (gramAt D V τ).IsHermitian ∧ (gramAt D V τ).det ≠ 0 := by
  intro D θ V hθ
  obtain ⟨r1, -, r3, r4, -, r6, r7, -⟩ := (GlobalTheory.SmoothForms.RealPts.realPoints D).2 θ hθ V
  let L : (D.what₂.Tau → Mt V.rank) → GA D V := prodAt θ V Finset.univ.toList
  have hm : ∀ u, L u ∈ GinfC V := prodAt_mem θ V _
  have hL : ∀ u ∈ UG (gramAt D V), ∀ τ, infMat D.sp.cm.sig V.gram (θ τ) (L u) = u τ := fun u hu τ => by
    rw [infMat_prodAt hθ V hu τ _ (Finset.nodup_toList _), if_pos (Finset.mem_toList.2 (Finset.mem_univ _))]
  refine ⟨L, fun u hu => ⟨hm u, hL u hu⟩, fun u hu u' hu' => ?_, continuousOn_prodAt hθ V _,
    fun g τ => archM_mem hθ V g τ, fun u hu => ?_, fun τ g hg => ?_, r7, fun a ha u hu => (r6 u hu a ha).symm,
    fun τ => ⟨(r1 τ).1, (r1 τ).2.ne_zero⟩⟩
  · refine r3 _ (hm _) _ (mul_mem (hm _) (hm _)) fun τ => ?_
    rw [r4, hL u hu, hL u' hu', hL (u * u') fun ρ => mul_mem_UH (hu ρ) (hu' ρ)]
    rfl
  · exact r3 _ (hm _) _ hu fun τ => hL _ (fun ρ => archM_mem hθ V u ρ) τ
  · have hs := atTau_spec hθ V τ hg
    have hu : (Pi.mulSingle τ g : D.what₂.Tau → Mt V.rank) ∈ UG (gramAt D V) := fun ρ => by
      by_cases c : ρ = τ
      · subst c
        rwa [Pi.mulSingle_eq_same]
      · rw [Pi.mulSingle_eq_of_ne c]
        exact one_mem_UH _
    refine r3 _ hs.1 _ (hm _) fun ρ => ?_
    rw [hL _ hu]
    by_cases c : ρ = τ
    · subst c
      rw [Pi.mulSingle_eq_same, hs.2.1]
    · rw [Pi.mulSingle_eq_of_ne c, hs.2.2 ρ c]

end GlobalTheory.RealLift

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBasicOpenEtaleCoordinatesFiniteFreeEtaleCo
section
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.Points

set_option autoImplicit false

namespace GlobalTheory.CoverDeg

theorem exists_goodCover_of_coords_of_cover : ∀ {k : Type} [CommRing k] {X Y : Scheme.{0}} (p : X ⟶ Sp k) (π : Y ⟶ X) (D δ : ℕ) (x : X) (U₁ U₂ : X.Opens), IsAffineOpen U₁ → x ∈ U₁ → (∃ t : Fin D → Γ(X, U₁), (MvPolynomial.eval₂Hom (ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.algX p U₁) t).Etale) → IsAffineOpen U₂ → x ∈ U₂ → IsAffineOpen (π ⁻¹ᵁ U₂) → (π.app U₂).hom.Etale → (π.app U₂).hom.Finite → (letI := (π.app U₂).hom.toAlgebra; Module.Free Γ(X, U₂) Γ(Y, π ⁻¹ᵁ U₂) ∧ Module.finrank Γ(X, U₂) Γ(Y, π ⁻¹ᵁ U₂) = δ) → ∃ U : X.Opens, x ∈ U ∧ GlobalTheory.CoverDeg.GoodCover p π D δ U := by
  intro k _ X Y p π D δ x U₁ U₂ hU₁ hx₁ ⟨t, ht⟩ hU₂ hx₂ hV₂ he hf hfr
  obtain ⟨f, g, hfg, hxf⟩ := exists_basicOpen_le_affine_inter hU₁ hU₂ x ⟨hx₁, hx₂⟩
  have hxU : x ∈ X.basicOpen g := hfg ▸ hxf
  refine ⟨X.basicOpen g, hxU, ?_⟩
  have hUU₁ : X.basicOpen g ≤ U₁ := hfg ▸ X.basicOpen_le f
  have hUU₂ : X.basicOpen g ≤ U₂ := X.basicOpen_le g
  have hUa : IsAffineOpen (X.basicOpen g) := hU₂.basicOpen g
  have hpre : π ⁻¹ᵁ X.basicOpen g = Y.basicOpen (π.app U₂ g) := Scheme.preimage_basicOpen π g
  have hVa : IsAffineOpen (π ⁻¹ᵁ X.basicOpen g) := hpre ▸ hV₂.basicOpen _
  have hVV₂ : π ⁻¹ᵁ X.basicOpen g ≤ π ⁻¹ᵁ U₂ := fun _ h => hUU₂ h
  refine ⟨hUa, hVa, ?_, ?_⟩
  · refine ⟨fun i => resG X hUU₁ (t i), ?_⟩
    have e : MvPolynomial.eval₂Hom (ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.algX p (X.basicOpen g)) (fun i => resG X hUU₁ (t i)) =
        (resG X hUU₁).comp (MvPolynomial.eval₂Hom (ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.algX p U₁) t) := by
      rw [MvPolynomial.comp_eval₂Hom, GlobalTheory.TopForm.resG_comp_algX]
    rw [e]
    have hR : (resG X hUU₁).Etale := by
      letI : Algebra Γ(X, U₁) Γ(X, X.basicOpen g) := (resG X hUU₁).toAlgebra
      haveI : IsLocalization.Away f Γ(X, X.basicOpen g) :=
        hU₁.isLocalization_of_eq_basicOpen f (homOfLE hUU₁) hfg.symm
      exact RingHom.etale_algebraMap.2 (Algebra.Etale.of_isLocalizationAway f)
    exact RingHom.Etale.stableUnderComposition _ _ ht hR
  · letI i1 : Algebra Γ(X, U₂) Γ(Y, π ⁻¹ᵁ U₂) := (π.app U₂).hom.toAlgebra
    letI i2 : Algebra Γ(X, U₂) Γ(X, X.basicOpen g) := (resG X hUU₂).toAlgebra
    letI i3 : Algebra Γ(Y, π ⁻¹ᵁ U₂) Γ(Y, π ⁻¹ᵁ X.basicOpen g) := (resG Y hVV₂).toAlgebra
    letI i4 : Algebra Γ(X, X.basicOpen g) Γ(Y, π ⁻¹ᵁ X.basicOpen g) := (π.app (X.basicOpen g)).hom.toAlgebra
    letI i5 : Algebra Γ(X, U₂) Γ(Y, π ⁻¹ᵁ X.basicOpen g) :=
      ((π.app (X.basicOpen g)).hom.comp (resG X hUU₂)).toAlgebra
    have hnat : (π.app (X.basicOpen g)).hom.comp (resG X hUU₂) = (resG Y hVV₂).comp (π.app U₂).hom := by
      ext a
      exact congr($(π.naturality (homOfLE hUU₂).op) a)
    haveI : IsScalarTower Γ(X, U₂) Γ(X, X.basicOpen g) Γ(Y, π ⁻¹ᵁ X.basicOpen g) :=
      IsScalarTower.of_algebraMap_eq' rfl
    haveI : IsScalarTower Γ(X, U₂) Γ(Y, π ⁻¹ᵁ U₂) Γ(Y, π ⁻¹ᵁ X.basicOpen g) :=
      IsScalarTower.of_algebraMap_eq' hnat
    haveI : IsLocalization.Away g Γ(X, X.basicOpen g) :=
      hU₂.isLocalization_of_eq_basicOpen g (homOfLE hUU₂) rfl
    haveI : IsLocalization (Algebra.algebraMapSubmonoid Γ(Y, π ⁻¹ᵁ U₂) (Submonoid.powers g))
        Γ(Y, π ⁻¹ᵁ X.basicOpen g) := by
      rw [Algebra.algebraMapSubmonoid, Submonoid.map_powers]
      exact hV₂.isLocalization_of_eq_basicOpen (π.app U₂ g) (homOfLE hVV₂) hpre
    haveI hpo : Algebra.IsPushout Γ(X, U₂) Γ(Y, π ⁻¹ᵁ U₂) Γ(X, X.basicOpen g) Γ(Y, π ⁻¹ᵁ X.basicOpen g) :=
      Algebra.isPushout_of_isLocalization (Submonoid.powers g) Γ(X, X.basicOpen g) Γ(Y, π ⁻¹ᵁ U₂)
        Γ(Y, π ⁻¹ᵁ X.basicOpen g)
    have het : (algebraMap Γ(X, X.basicOpen g) Γ(Y, π ⁻¹ᵁ X.basicOpen g)).Etale :=
      RingHom.Etale.isStableUnderBaseChange _ _ _ _ he
    haveI : Module.Finite Γ(X, U₂) Γ(Y, π ⁻¹ᵁ U₂) := hf
    haveI hfin : Module.Finite Γ(X, X.basicOpen g) Γ(Y, π ⁻¹ᵁ X.basicOpen g) :=
      Module.Finite.of_isLocalization Γ(X, U₂) Γ(Y, π ⁻¹ᵁ U₂) (Submonoid.powers g)
    refine ⟨het, hfin, ?_⟩
    obtain ⟨hfree, hrk⟩ := hfr
    haveI : Nontrivial Γ(X, X.basicOpen g) := (X.presheaf.germ _ x hxU).hom.domain_nontrivial
    haveI : Nontrivial Γ(X, U₂) := (X.presheaf.germ _ x hx₂).hom.domain_nontrivial
    let b := Module.Free.chooseBasis Γ(X, U₂) Γ(Y, π ⁻¹ᵁ U₂)
    let b' := hpo.symm.out.basis b
    refine ⟨Module.Free.of_basis b', ?_⟩
    rw [Module.finrank_eq_card_basis b', ← hrk, Module.finrank_eq_card_basis b]

end GlobalTheory.CoverDeg
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsChowFormGenericHyperplaneSection
section
set_option autoImplicit false

noncomputable section

open MvPolynomial GlobalTheory.ChowHt GlobalTheory.CompHt Filter
open scoped ENNReal

namespace GlobalTheory.ChowSpec

attribute [local instance] MvPolynomial.gradedAlgebra MvPolynomial.algebraMvPolynomial

def lastSubst {A : Type} [CommRing A] {N : ℕ} (D : ℕ) (t : Fin N → A) :
    Fin (D + 1) × Fin N → MvPolynomial (Fin D × Fin N) A :=
  fun v => Fin.lastCases (motive := fun _ => MvPolynomial (Fin D × Fin N) A)
    (C (t v.2)) (fun i => X (i, v.2)) v.1

set_option autoImplicit false in
open MvPolynomial Filter in
open scoped ENNReal in
attribute [local instance] MvPolynomial.gradedAlgebra MvPolynomial.algebraMvPolynomial in
@[simp] theorem _root_.GlobalTheory.ChowSpec.lastSubst_last {A : Type} [CommRing A] {N : ℕ} (D : ℕ)
    (t : Fin N → A) (j : Fin N) : _root_.GlobalTheory.ChowSpec.lastSubst D t (Fin.last D, j) = C (t j) := by
  simp [_root_.GlobalTheory.ChowSpec.lastSubst]

set_option autoImplicit false in
open MvPolynomial Filter in
open scoped ENNReal in
attribute [local instance] MvPolynomial.gradedAlgebra MvPolynomial.algebraMvPolynomial in
@[simp] theorem _root_.GlobalTheory.ChowSpec.lastSubst_castSucc {A : Type} [CommRing A] {N : ℕ} (D : ℕ)
    (t : Fin N → A) (i : Fin D) (j : Fin N) :
    _root_.GlobalTheory.ChowSpec.lastSubst D t (i.castSucc, j) = X (i, j) := by
  simp [_root_.GlobalTheory.ChowSpec.lastSubst]

def lastEquiv (K : Type) [CommRing K] (N D : ℕ) :
    MvPolynomial (Fin (D + 1) × Fin N) K ≃+* MvPolynomial (Fin D × Fin N) (MvPolynomial (Fin N) K) :=
  RingEquiv.ofRingHom
    (aeval (R := K) (lastSubst D (X : Fin N → MvPolynomial (Fin N) K))).toRingHom
    (eval₂Hom (aeval (R := K) (fun j => X (Fin.last D, j))).toRingHom
      (fun v => X (v.1.castSucc, v.2)))
    (by
      refine MvPolynomial.ringHom_ext' (MvPolynomial.ringHom_ext (fun r => ?_) (fun j => ?_))
        (fun v => ?_) <;> simp)
    (by
      refine MvPolynomial.ringHom_ext (fun r => by simp) ?_
      rintro ⟨i, j⟩
      refine Fin.lastCases ?_ (fun i => ?_) i <;> simp)

set_option autoImplicit false in
open MvPolynomial Filter in
open scoped ENNReal in
attribute [local instance] MvPolynomial.gradedAlgebra MvPolynomial.algebraMvPolynomial in
private theorem isWeightedHomogeneous_aeval_of_forall {R S σ τ Γ Δ : Type} [CommSemiring R]
    [CommSemiring S] [Algebra R S] [AddCommMonoid Γ] [AddCommMonoid Δ] {w : σ → Γ}
    {w' : τ → Δ} (g : Γ →+ Δ) {p : MvPolynomial σ R} {m : Γ}
    (hp : IsWeightedHomogeneous w p m) (φ : σ → MvPolynomial τ S)
    (hφ : ∀ v, IsWeightedHomogeneous w' (φ v) (g (w v))) :
    IsWeightedHomogeneous w' (aeval φ p) (g m) := by
  rw [p.as_sum, map_sum, ← mem_weightedHomogeneousSubmodule]
  refine Submodule.sum_mem _ fun s hs => ?_
  rw [mem_weightedHomogeneousSubmodule, aeval_monomial, Finsupp.prod]
  have hw : Finsupp.weight w s = m := hp (mem_support_iff.mp hs)
  have hm : g m = 0 + ∑ v ∈ s.support, s v • g (w v) := by
    rw [zero_add, ← hw, Finsupp.weight_apply, Finsupp.sum, map_sum]
    simp [map_nsmul]
  rw [hm, MvPolynomial.algebraMap_apply]
  exact (isWeightedHomogeneous_C w' _).mul
    (IsWeightedHomogeneous.prod _ _ _ fun v _ => (hφ v).pow _)

set_option autoImplicit false in
open MvPolynomial Filter in
open scoped ENNReal in
attribute [local instance] MvPolynomial.gradedAlgebra MvPolynomial.algebraMvPolynomial in

theorem _root_.GlobalTheory.ChowSpec.exists_isChowFormInt_generic_section : ∀ (K L : Type) [Field K] [Field L] (N : ℕ) [Algebra K L] [Algebra (MvPolynomial (Fin N) K) L] [IsScalarTower K (MvPolynomial (Fin N) K) L] [IsFractionRing (MvPolynomial (Fin N) K) L] (P : Ideal (MvPolynomial (Fin N) K)) (D δ : ℕ) (f : MvPolynomial (Fin (D + 1 + 1) × Fin N) K), (∀ g ∈ P, ∀ n : ℕ, homogeneousComponent n g ∈ P) → _root_.GlobalTheory.ChowHt.IsChowFormInt P (D + 1) δ f → ∃ f' : MvPolynomial (Fin (D + 1) × Fin N) L, _root_.GlobalTheory.ChowHt.IsChowFormInt (P.map (MvPolynomial.map (algebraMap K L) : MvPolynomial (Fin N) K →+* MvPolynomial (Fin N) L) ⊔ Ideal.span {(∑ j : Fin N, C (algebraMap (MvPolynomial (Fin N) K) L (X j)) * X j : MvPolynomial (Fin N) L)}) D δ f' := by
  intro K L _ _ N _ _ _ _ P D δ f hP hf
  set t : Fin N → L := fun j => algebraMap (MvPolynomial (Fin N) K) L (X j) with ht
  set φ := _root_.GlobalTheory.ChowSpec.lastSubst (D + 1) t with hφ
  set f' : MvPolynomial (Fin (D + 1) × Fin N) L := aeval (R := K) φ f with hf'
  have hfhom : _root_.GlobalTheory.Chow.IsBlockHomogeneous f (fun _ => δ) :=
    _root_.GlobalTheory.ChowHt.isMultiHomogeneous_iff_block.1 hf.homog
  have hf'hom : _root_.GlobalTheory.Chow.IsBlockHomogeneous f' (fun _ => δ) := by
    unfold _root_.GlobalTheory.Chow.IsBlockHomogeneous at hfhom ⊢
    let g : (Fin (D + 1 + 1) → ℕ) →+ (Fin (D + 1) → ℕ) :=
      { toFun := fun a i => a i.castSucc, map_zero' := rfl, map_add' := fun _ _ => rfl }
    refine isWeightedHomogeneous_aeval_of_forall (S := L) g hfhom φ ?_
    rintro ⟨i, j⟩
    induction i using Fin.lastCases with
    | last =>
      have hg : g (_root_.GlobalTheory.Chow.blockWeight (Fin.last (D + 1), j)) = 0 := by
        funext i
        simp [g, _root_.GlobalTheory.Chow.blockWeight, Pi.single_apply, Fin.castSucc_ne_last]
      rw [hφ, _root_.GlobalTheory.ChowSpec.lastSubst_last, hg]
      exact isWeightedHomogeneous_C _ _
    | cast i =>
      have hg : g (_root_.GlobalTheory.Chow.blockWeight (i.castSucc, j)) = _root_.GlobalTheory.Chow.blockWeight (i, j) := by
        funext i'
        simp [g, _root_.GlobalTheory.Chow.blockWeight, Pi.single_apply]
      rw [hφ, _root_.GlobalTheory.ChowSpec.lastSubst_castSucc, hg]
      exact isWeightedHomogeneous_X _ _ _
  refine ⟨f', _root_.GlobalTheory.ChowHt.isMultiHomogeneous_iff_block.2 hf'hom, ?_, ?_⟩
  · have hkey : MvPolynomial.map (algebraMap (MvPolynomial (Fin N) K) L)
        (_root_.GlobalTheory.ChowSpec.lastEquiv K N (D + 1) f) = f' := by
      rw [hf']
      change ((MvPolynomial.map (algebraMap (MvPolynomial (Fin N) K) L)).comp
        (_root_.GlobalTheory.ChowSpec.lastEquiv K N (D + 1)).toRingHom) f = (aeval φ).toRingHom f
      congr 1
      refine MvPolynomial.ringHom_ext (fun r => ?_) (fun v => ?_)
      · simp [_root_.GlobalTheory.ChowSpec.lastEquiv, MvPolynomial.algebraMap_apply,
          IsScalarTower.algebraMap_apply K (MvPolynomial (Fin N) K) L]
      · rcases v with ⟨i, j⟩
        induction i using Fin.lastCases <;> simp [_root_.GlobalTheory.ChowSpec.lastEquiv, hφ, ht]
    set F := _root_.GlobalTheory.ChowSpec.lastEquiv K N (D + 1) f with hF
    have hFirr : Irreducible F :=
      (MulEquiv.irreducible_iff (_root_.GlobalTheory.ChowSpec.lastEquiv K N (D + 1))).2
        hf.irred
    have hF0 : F ≠ 0 := hFirr.ne_zero
    have hFprime : Prime F := UniqueFactorizationMonoid.irreducible_iff_prime.1 hFirr
    have hδ : 0 < δ := by
      rcases Nat.eq_zero_or_pos δ with h | h
      · exfalso
        subst h
        have hh := hfhom.isHomogeneous
        simp only [Finset.sum_const_zero] at hh
        have hf0 := hf.ne_zero
        have hC : f = C (coeff 0 f) :=
          (totalDegree_eq_zero_iff_eq_C).1 (by simpa using hh.totalDegree hf0)
        have hc : coeff 0 f ≠ 0 := fun h0 => hf0 (by rw [hC, h0, C_0])
        apply hf.irred.not_isUnit
        rw [hC]
        exact hc.isUnit.map C
      · exact h
    have hf'0 : f' ≠ 0 := by
      rw [← hkey]
      exact fun h => hF0 ((map_eq_zero_iff _
        (MvPolynomial.map_injective _ (IsFractionRing.injective (MvPolynomial (Fin N) K) L))).1 h)
    have hnotunit : ¬ IsUnit f' := by
      intro hu
      obtain ⟨r, hr, hfr⟩ := (MvPolynomial.isUnit_iff_eq_C_of_isReduced).1 hu
      have hh := hf'hom.isHomogeneous
      rw [hfr] at hh
      have h0 := hh (show coeff 0 (C r) ≠ 0 by simpa using hr.ne_zero)
      simp at h0
      omega
    have hdisj : Disjoint ((Submonoid.map (C : MvPolynomial (Fin N) K →+*
        MvPolynomial (Fin (D + 1) × Fin N) (MvPolynomial (Fin N) K))
          (nonZeroDivisors (MvPolynomial (Fin N) K))) :
            Set (MvPolynomial (Fin (D + 1) × Fin N) (MvPolynomial (Fin N) K)))
        (↑(Ideal.span {F}) : Set (MvPolynomial (Fin (D + 1) × Fin N) (MvPolynomial (Fin N) K))) := by
      rw [Set.disjoint_left]
      rintro _ ⟨s, hs, rfl⟩ hmem
      obtain ⟨g, hg⟩ := Ideal.mem_span_singleton'.1 hmem
      apply hnotunit
      have hs0 : algebraMap (MvPolynomial (Fin N) K) L s ≠ 0 :=
        IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hs
      have hmapped := congrArg (MvPolynomial.map (algebraMap (MvPolynomial (Fin N) K) L)) hg
      rw [map_mul, hkey, map_C] at hmapped
      exact isUnit_of_mul_isUnit_right (hmapped ▸ hs0.isUnit.map C)
    have hprime := IsLocalization.isPrime_of_isPrime_disjoint
      (Submonoid.map (C : MvPolynomial (Fin N) K →+*
        MvPolynomial (Fin (D + 1) × Fin N) (MvPolynomial (Fin N) K))
          (nonZeroDivisors (MvPolynomial (Fin N) K)))
      (MvPolynomial (Fin (D + 1) × Fin N) L) (Ideal.span {F})
      ((Ideal.span_singleton_prime hF0).2 hFprime) hdisj
    rw [Ideal.map_span, Set.image_singleton] at hprime
    have hF' : algebraMap (MvPolynomial (Fin (D + 1) × Fin N) (MvPolynomial (Fin N) K))
        (MvPolynomial (Fin (D + 1) × Fin N) L) F = f' := hkey
    rw [hF'] at hprime
    exact ((Ideal.span_singleton_prime hf'0).1 hprime).irreducible
  · intro u
    set ũ : Fin (D + 1 + 1) × Fin N → AlgebraicClosure L := fun v =>
      Fin.lastCases (motive := fun _ => AlgebraicClosure L) (algebraMap L (AlgebraicClosure L) (t v.2))
        (fun i => u (i, v.2)) v.1 with hũ
    have hev : aeval u f' = aeval ũ f := by
      rw [hf']
      change ((aeval u).restrictScalars K) (aeval φ f) = aeval ũ f
      rw [← AlgHom.comp_apply, comp_aeval]
      refine congrArg (fun x => (aeval x) f) (funext fun v => ?_)
      rcases v with ⟨i, j⟩
      induction i using Fin.lastCases <;> simp [hφ, hũ]
    have hPhom : Ideal.IsHomogeneous (homogeneousSubmodule (Fin N) K) P := by
      intro i r hr
      convert hP r hr i using 1
      conv_lhs => rw [← sum_homogeneousComponent r]
      rw [DirectSum.decompose_sum, DFinsupp.finset_sum_apply, AddSubmonoidClass.coe_finset_sum,
        Finset.sum_eq_single i]
      · exact DirectSum.decompose_of_mem_same _ (homogeneousComponent_mem i r)
      · intro b _ hb
        exact DirectSum.decompose_of_mem_ne _ (homogeneousComponent_mem b r) hb
      · intro hi
        have h0 : homogeneousComponent i r = 0 :=
          homogeneousComponent_eq_zero i r (by simp at hi; omega)
        rw [h0, DirectSum.decompose_zero]
        rfl
    have hideal : ∀ y : Fin N → AlgebraicClosure L,
        (∀ g ∈ P.map (MvPolynomial.map (algebraMap K L) : MvPolynomial (Fin N) K →+* MvPolynomial (Fin N) L) ⊔
          Ideal.span {(∑ j : Fin N, C (t j) * X j : MvPolynomial (Fin N) L)}, aeval y g = 0) ↔
        (∀ g ∈ P, aeval y g = 0) ∧ ∑ j, ũ (Fin.last (D + 1), j) * y j = 0 := by
      intro y
      have hmap : ∀ g : MvPolynomial (Fin N) K,
          aeval y (MvPolynomial.map (algebraMap K L) g) = aeval y g := fun g => aeval_map_algebraMap L y g
      have hlin : aeval y (∑ j : Fin N, C (t j) * X j : MvPolynomial (Fin N) L) =
          ∑ j, ũ (Fin.last (D + 1), j) * y j := by
        simp [hũ]
      constructor
      · intro H
        refine ⟨fun g hg => ?_, ?_⟩
        · rw [← hmap]
          exact H _ (Ideal.mem_sup_left (Ideal.mem_map_of_mem _ hg))
        · rw [← hlin]
          exact H _ (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _))
      · rintro ⟨H1, H2⟩ g hg
        have hle : P.map (MvPolynomial.map (algebraMap K L) : MvPolynomial (Fin N) K →+* MvPolynomial (Fin N) L) ⊔
            Ideal.span {(∑ j : Fin N, C (t j) * X j : MvPolynomial (Fin N) L)} ≤
            RingHom.ker (aeval y : MvPolynomial (Fin N) L →ₐ[L] AlgebraicClosure L) := by
          refine sup_le (Ideal.map_le_iff_le_comap.2 fun g hg => ?_) ((Ideal.span_singleton_le_iff_mem _).2 ?_)
          · simpa [RingHom.mem_ker, hmap] using H1 g hg
          · simpa [RingHom.mem_ker, hlin] using H2
        exact RingHom.mem_ker.1 (hle hg)
    rw [hev, hf.zero_iff_of_isAlgClosed hPhom ũ]
    constructor
    · rintro ⟨y, hy0, hyP, hyu⟩
      rw [Fin.forall_fin_succ'] at hyu
      exact ⟨y, hy0, (hideal y).2 ⟨hyP, hyu.2⟩, fun i => by simpa [hũ] using hyu.1 i⟩
    · rintro ⟨y, hy0, hyI, hyu⟩
      obtain ⟨hyP, hyh⟩ := (hideal y).1 hyI
      exact ⟨y, hy0, hyP, Fin.forall_fin_succ'.2 ⟨fun i => by simpa [hũ] using hyu i, hyh⟩⟩

end GlobalTheory.ChowSpec
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDerivationEqIteratePrimeCharP
section
open GlobalTheory GlobalTheory.LogDR

namespace GlobalTheory

theorem derivation_iterate_leibniz {R : Type} [CommRing R] (D : Derivation ℤ R R) (a b : R) (n : ℕ) :
    (⇑D)^[n] (a * b) =
      ∑ ij ∈ Finset.HasAntidiagonal.antidiagonal n, (n.choose ij.1 : R) * ((⇑D)^[ij.1] a * (⇑D)^[ij.2] b) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_antidiagonal_choose_succ_mul (fun i j => (⇑D)^[i] a * (⇑D)^[j] b) n,
      Function.iterate_succ_apply', ih, map_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun ij hij => ?_
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hij
    have hc : (n.choose ij.2 : R) = (n.choose ij.1 : R) := by
      rw [← hij, Nat.choose_symm_add]
    rw [hc, Derivation.leibniz, Derivation.leibniz, Derivation.map_natCast, smul_zero, add_zero,
      Function.iterate_succ_apply', Function.iterate_succ_apply']
    simp only [smul_eq_mul]
    ring

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteAdelicGLAgreeOutsideTrivialOnFinsetStatement
section
open NumberField IsDedekindDomain GlobalTheory.CuspRep Formalism.UG GlobalTheory.LFun Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_finiteAdelicGL_agree_outside_trivial_on_finset : ∀ (E : Type) [Field E] [NumberField E] (a : ℕ) (S : Finset (HeightOneSpectrum (𝓞 E))) (k : GL (Fin a) (Af E)), ∃ k' : GL (Fin a) (Af E), (∀ w ∉ S, GeneralLinearGroup.map (pLoc E w) k' = GeneralLinearGroup.map (pLoc E w) k) ∧ ∀ w ∈ S, GeneralLinearGroup.map (pLoc E w) k' = 1 := by
  first | exact @GlobalTheory.outsideS_elt | exact GlobalTheory.outsideS_elt | (intros; apply GlobalTheory.outsideS_elt <;> assumption)
end

