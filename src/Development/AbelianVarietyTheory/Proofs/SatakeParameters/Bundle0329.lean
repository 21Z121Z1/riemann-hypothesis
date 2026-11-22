import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0324
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0025
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.FirstCoupledKernelEquivariantCosets
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0325
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0278
import Formalism.LocalToGlobal.Columns.XtPhiTopGCongr
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.TopLawQ
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.RegPolOfRepOf
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.ArthurClozel
import Formalism.SharpRestriction.LevelLetterCocycles.SumRepresentations
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsMonomialOfCountZero
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsPotCrysAtOfMono0
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteDimensionalAdjoinRange
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIrreducibleFixed
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1320
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1406
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0433
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0424
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0875
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0046
import CompanionTheory.AutomorphicTheory.ProductFormulaTheory.GrothendieckRingPolynomial.GrothendieckRingPolynomialOfSeg
import CompanionTheory.RealGroups.GeneralUnitaryRepresentations.ArchimedeanJacquetSegments.SegmentSubquotients.SegmentRepresentation
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaMod
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ExistsUniqueVec
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsWildInertiaCyclotomicElement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0235
import Formalism.SharpRestriction.LevelLetterCocycles.ExistsInertiaCharpolyFactorOfTameType
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0006
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TendstoOneOfSummable
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SplitPlaceHeckeOperatorScalarOnSpherical
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0362
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0240
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0239
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0327
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0313
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0009
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0025
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0020
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0903
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0767
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NontrivialTwJacquetOfSurjective
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0178
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0190
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0326
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0019
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0104
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0008
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.ValidForConstructedPointClassesEventuallyWorking
import Formalism.SharpRestriction.Bundle0001
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.GoodIdempotentFixesOfOnlySeriesOfLabelActs

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ChartPointsFramesCongrAwayFromBadPrimesStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV GlobalTheory.TwU GlobalTheory.TwV Formalism.UG

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chartPoints_frames_congr_away_from_badPrimes : UnderTie (fun {D L hT Gi Gl Kc Y cX ex t u μ St} A dtU a => ∀ j (hj : j ≤ D.R.m) β x x₁ p p₁,
    IsPtAd A a j hj β x p → IsPtAd A a j hj β x₁ p₁ →
    (∀ v ∈ plUnder D.host.F (ssRec t u μ), bc (prV (E := D.host.E) v) x₁.1 = bc (prV (E := D.host.E) v) x.1) →
    ∀ P : SB t μ, ∃ k : GLint t.X.E (D.R.N j) P.1, frsF t.sel (t.tup μ) p₁ P = frsF t.sel (t.tup μ) p P * k.1 ∧
      ∀ s l, IntAt P.1 ((((qOf P.1 : ℕ) : t.X.E) ^ ((t.cst μ).D P))⁻¹ * (k.1 (Pi.single s 1) l - (Pi.single s 1 : Sp t.X.E (D.R.N j)) l))) := by
  first | exact @GlobalTheory.AwayFr.frames_away | exact GlobalTheory.AwayFr.frames_away | (intros; apply GlobalTheory.AwayFr.frames_away <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.CompanionLatticeAdelicLatticeLocalizationEqStatement
section
open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.UG Formalism.L2.Col Formalism.L2.PairingIndexBounds.F Formalism.MainNotions.G.KAat Formalism.L2.Forms Formalism.L2.Ker Formalism.MainNotions Formalism.L2.DIV Formalism.MainNotions.G GlobalTheory.TwU GlobalTheory.TwV
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.companionLattice_adelicLattice_localization_eq : ∀ {R : Ranks} {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] (sp : Spaces R F E) {N : ℕ} (σ : E →ₐ[F] E), (σ : E →+* E) = sp.cm.sig → ∀ (J : Matrix (Fin N) (Fin N) E), IsUnit J.det → ∀ (a : 𝓞 E) (x : GL (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)), x ∈ UPts σ J (FiniteAdeleRing (𝓞 F) F) → ∀ (Lb : Submodule (𝓞 E) (Fin N → E)), Lb.FG → Submodule.span E (Lb : Set (Fin N → E)) = ⊤ → ∀ (P : HeightOneSpectrum (𝓞 E)), Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (compan (sp := sp) J a (latAd x Lb)) = Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (latAd x (compan (sp := sp) J a Lb)) := by
  first | exact @GlobalTheory.CompanLatAd.locP_companion_latAd | exact GlobalTheory.CompanLatAd.locP_companion_latAd | (intros; apply GlobalTheory.CompanLatAd.locP_companion_latAd <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.CouplingCosetRepresentativesCongrAtTwistPrimeStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.DIV Formalism.L2.Col Formalism.MainNotions Formalism.L2.Ker GlobalTheory.TwU GlobalTheory.TwV GlobalTheory.TwTop
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.couplingCoset_representatives_congr_at_twistPrime : UnderTie (fun {D L hT Gi Gl Kc Y cX ex t u μ St} A dtU a =>
  ∀ (hi : t.m2 + 1 ≤ D.R.m) (β : (St (t.m2 + 1) hi).Ch) (P : SB t μ), P.1 ∉ t.Pr.vGs →
  ∀ (p p₁ : ChPt (R := D.R) t.sel (t.tup μ) (t.word u) (t.m2 + 1)) (g k : Sp t.X.E (D.R.N (t.m2 + 1)) ≃ₗ[t.X.E] Sp t.X.E (D.R.N (t.m2 + 1))),
    g ∈ GLint t.X.E (D.R.N (t.m2 + 1)) P.1 →
    SameCoset t.sel (t.tup μ) (t.cst μ) P (g (y0At A (t.m2 + 1) hi β P)) (y0At A (t.m2 + 1) hi β P) →
    k ∈ GLint t.X.E (D.R.N (t.m2 + 1)) P.1 →
    (∀ w ∈ stdAt t.X.E (D.R.N (t.m2 + 1)) P.1, ((qOf P.1 : t.X.E) ^ (t.cst μ).D P)⁻¹ • (k w - w) ∈ stdAt t.X.E (D.R.N (t.m2 + 1)) P.1) →
    (∀ w, frsF t.sel (t.tup μ) p₁ P w = frsF t.sel (t.tup μ) p P (g (k w))) →
    ((qOf P.1 : t.X.E) ^ (t.cst μ).M) • (frsF t.sel (t.tup μ) p P).symm (repY (cosetOf A (t.m2 + 1) hi β p)) ∈ stdAt t.X.E (D.R.N (t.m2 + 1)) P.1 ∧
    ((qOf P.1 : t.X.E) ^ (t.cst μ).M) • (frsF t.sel (t.tup μ) p₁ P).symm (repY (cosetOf A (t.m2 + 1) hi β p₁)) ∈ stdAt t.X.E (D.R.N (t.m2 + 1)) P.1 ∧
    ((qOf P.1 : t.X.E) ^ (t.cst μ).M)⁻¹ • ((frsF t.sel (t.tup μ) p P).symm (repY (cosetOf A (t.m2 + 1) hi β p₁)) -
      (frsF t.sel (t.tup μ) p P).symm (repY (cosetOf A (t.m2 + 1) hi β p))) ∈ stdAt t.X.E (D.R.N (t.m2 + 1)) P.1) := by
  first | exact @GlobalTheory.LocQCoset.coset_agree | exact GlobalTheory.LocQCoset.coset_agree | (intros; apply GlobalTheory.LocQCoset.coset_agree <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.FixedIwahoriNeBotOfTwist
section
noncomputable section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.AboveL

namespace GlobalTheory.AboveL.IwaFix

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL

theorem fixed_iwahori_ne_bot_of_twist {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] {n : ℕ} {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    {ρ : Representation ℂ (GL (Fin n) k) V} {ρ' : Representation ℂ (GL (Fin n) k) W} (s : ℂ)
    (T : (twist ρ (detChar (Fin n) (absPow k s))).Equiv ρ') (h : fixed ρ' (iwahori k (Fin n)) ≠ ⊥) :
    fixed ρ (iwahori k (Fin n)) ≠ ⊥ := by
  obtain ⟨y, hy, h0⟩ := (Submodule.ne_bot_iff _).1 h
  obtain ⟨x, rfl⟩ := T.toLinearEquiv.surjective y
  refine (Submodule.ne_bot_iff _).2 ⟨x, GlobalTheory.Parabolic.mem_fixed.2 fun g hg => ?_, fun hx => h0 (by simp [hx])⟩
  have e := T.toIntertwiningMap.isIntertwining _ _ g x
  have hd : absPow k s (Matrix.GeneralLinearGroup.det g) = 1 := by
    have h1 := GlobalTheory.SmGL.LeviInt.nabs_det_eq_one (iwahori_le_KO k (Fin n) hg)
    ext; simp [absPow, h1]
  rw [twist_apply, detChar_apply, hd, Units.val_one, one_smul] at e
  have hy' := GlobalTheory.Parabolic.mem_fixed.1 hy g hg
  exact T.toLinearEquiv.injective (e.trans hy')

end GlobalTheory.AboveL.IwaFix
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.FormAtEachLocation
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.FormAllLevels

theorem main_of (pet : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (a : NG.AlgWt L n) (β : a.W →ₗ⋆[ℂ] a.W →ₗ[ℂ] ℂ), GlobalTheory.CoefDuty.IsInvForm a β → ∃ B, GlobalTheory.CoefDuty.IsPetersson a B ∧ ∀ (J : Subgroup (GAf L n)) (χ : J →* ℂˣ) (T : Finset (GAf L n)), GlobalTheory.CoefDuty.IsBounded J → (∃ N : ℕ, 0 < N ∧ ∀ κ, NG.Cong L n N κ → ∃ h : κ ∈ J, χ ⟨κ, h⟩ = 1) → GlobalTheory.CoefDuty.IsClassReps J T → ∃ c : ℝ, 0 < c ∧ ∀ f ∈ NG.TypeSp a.ρ J χ, ∀ f' ∈ NG.TypeSp a.ρ J χ, GlobalTheory.CoefDuty.classSum a β J T f f' = (c : ℂ) * B f f') (cls : ∀ (hL : GlobalTheory.Published.LocalLanglandsGL) (D : D7) (P : Pin hL D) (X : GlobalTheory.NJoin.RealAt D P.cf P.C P.tp), GlobalTheory.NJoin.Agree X P.M P.rep → ∀ i, ∃ (J : Subgroup (GAf D.host.E D.R.nV)) (χ : J →* ℂˣ) (T : Finset (GAf D.host.E D.R.nV)) (β : (P.M.loc i).wt.W →ₗ⋆[ℂ] (P.M.loc i).wt.W →ₗ[ℂ] ℂ) (c : ℝ), GlobalTheory.CoefDuty.IsInvForm (P.M.loc i).wt β ∧ GlobalTheory.CoefDuty.IsBounded J ∧ (∃ N : ℕ, 0 < N ∧ ∀ κ, NG.Cong D.host.E D.R.nV N κ → ∃ h : κ ∈ J, χ ⟨κ, h⟩ = 1) ∧ GlobalTheory.CoefDuty.IsClassReps J T ∧ 0 < c ∧ (∀ x, (P.M.loc i).real x ∈ NG.TypeSp (P.M.loc i).wt.ρ J χ) ∧ ∀ x y, inner ℂ x y = (c : ℂ) * GlobalTheory.CoefDuty.classSum (P.M.loc i).wt β J T ((P.M.loc i).real x) ((P.M.loc i).real y)) : ∀ (hL : GlobalTheory.Published.LocalLanglandsGL) (D : D7) (P : Pin hL D), ∀ (X : GlobalTheory.NJoin.RealAt D P.cf P.C P.tp) (_ : GlobalTheory.NJoin.Agree X P.M P.rep), ∀ i, MtForm D P.M i := by
  intro hL D P X hA i
  obtain ⟨J, χ, T, β, c, hβ, hJb, hJo, hT, hc, hmem, hin⟩ := cls hL D P X hA i
  obtain ⟨B, hB, hcs⟩ := pet D.host.E D.R.nV (P.M.loc i).wt β hβ
  obtain ⟨c', hc', hcs'⟩ := hcs J χ T hJb hJo hT
  have hpos : (0 : ℝ) < c * c' := mul_pos hc hc'
  refine ⟨((c * c' : ℝ) : ℂ) • B, ?_, ?_⟩
  · intro f hf f' hf'
    obtain ⟨h1, h2, h3⟩ := hB f hf f' hf'
    refine ⟨?_, ?_, ?_⟩
    · simp only [LinearMap.smul_apply, smul_eq_mul, map_mul, Complex.conj_ofReal]
      rw [h1]
    · intro hne
      simp only [LinearMap.smul_apply, smul_eq_mul, Complex.re_ofReal_mul]
      exact mul_pos hpos (h2 hne)
    · intro h
      simp only [LinearMap.smul_apply, h3 h]
  · intro x y
    rw [hin x y, hcs' _ (hmem x) _ (hmem y)]
    simp only [LinearMap.smul_apply, smul_eq_mul]
    push_cast
    ring

theorem main : ∀ (hL : GlobalTheory.Published.LocalLanglandsGL) (D : D7) (P : Pin hL D), ∀ (X : GlobalTheory.NJoin.RealAt D P.cf P.C P.tp) (_ : GlobalTheory.NJoin.Agree X P.M P.rep), ∀ i, MtForm D P.M i :=
  main_of GlobalTheory.T.exists_pos_classSum_eq_mul_invariantForm GlobalTheory.T.invariant_form_bounded_congruence

end GlobalTheory.FormAllLevels
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.GoodPlaceHeckeEigenMatch
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.SummandEig

theorem irrScalar : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (a : Formalism.L2.NG.AlgWt L n) (S : Submodule ℂ (Formalism.AUTREP.GAf L n → a.W)), Formalism.L2.NG.IsIrrRep a.ρ S → ∀ (s : SplitPlace L) (α : Formalism.AUTREP.GAf L n), TrivOutside {s.v} α → ∀ (ι : Type) (R : Finset ι) (r : ι → Formalism.AUTREP.GAf L n), (∀ γ ∈ R, ∃ k₁ ∈ GlobalTheory.HeckeScalarSph.locK n s.v, ∃ k₂ ∈ GlobalTheory.HeckeScalarSph.locK n s.v, r γ = k₁ * α * k₂) → (∀ x, (∃ k₁ ∈ GlobalTheory.HeckeScalarSph.locK n s.v, ∃ k₂ ∈ GlobalTheory.HeckeScalarSph.locK n s.v, x = k₁ * α * k₂) → ∃! γ, γ ∈ R ∧ (r γ)⁻¹ * x ∈ Umax L n) → ∃ c : ℂ, ∀ f ∈ S, (∀ κ ∈ Umax L n, TrivOutside {s.v} κ → Formalism.L2.NG.rt L n κ f = f) → ∑ γ ∈ R, Formalism.L2.NG.rt L n (r γ) f = c • f := GlobalTheory.T.sphericalDoubleCosetSum_scalar_irreducible_fixed

theorem isoScalar : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (a : Formalism.L2.NG.AlgWt L n) (S : Submodule ℂ (Formalism.AUTREP.GAf L n → a.W)), Formalism.L2.NG.IsIrrRep a.ρ S → ∀ (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) (ι : Type) (R : Finset ι) (r : ι → Formalism.AUTREP.GAf L n) (c : ℂ), (∀ f ∈ S, (∀ κ ∈ Umax L n, TrivOutside {v} κ → Formalism.L2.NG.rt L n κ f = f) → ∑ γ ∈ R, Formalism.L2.NG.rt L n (r γ) f = c • f) → ∀ f ∈ Formalism.L2.NG.isoTyp a.ρ S, (∀ κ ∈ Umax L n, TrivOutside {v} κ → Formalism.L2.NG.rt L n κ f = f) → ∑ γ ∈ R, Formalism.L2.NG.rt L n (r γ) f = c • f := GlobalTheory.T.rightTranslationSum_scalar_isotypic

theorem frameReps : ∀ (D : D7) (V : Formalism.BasicNotions.TH.HSp D) (n : ℕ) (hF : D.host.F = maximalRealSubfield D.host.E) (Ψ : Formalism.IndefR.principalLevelFrame.RowPsi V n), GlobalTheory.NJoin.StdFrame hF Ψ → ∀ (Pp : HeightOneSpectrum (𝓞 D.host.E)), Formalism.MainNotions.SchurIrreducible.IsSplit (E := D.host.E) (Pp.under (𝓞 D.host.F)) → ∀ d, GlobalTheory.Hk3.IsLab V Pp d → ∃ (s : SplitPlace D.host.E) (α : Formalism.AUTREP.GAf D.host.E n), Formalism.L2.NG.OverPl Pp s.v ∧ TrivOutside {s.v} α ∧ (∀ γ ∈ GlobalTheory.Hk3.rep V Pp d, ∃ k₁ ∈ GlobalTheory.HeckeScalarSph.locK n s.v, ∃ k₂ ∈ GlobalTheory.HeckeScalarSph.locK n s.v, Formalism.IndefR.principalLevelFrame.pre Ψ γ = k₁ * α * k₂) ∧ ∀ x, (∃ k₁ ∈ GlobalTheory.HeckeScalarSph.locK n s.v, ∃ k₂ ∈ GlobalTheory.HeckeScalarSph.locK n s.v, x = k₁ * α * k₂) → ∃! γ, γ ∈ GlobalTheory.Hk3.rep V Pp d ∧ (Formalism.IndefR.principalLevelFrame.pre Ψ γ)⁻¹ * x ∈ Umax D.host.E n := GlobalTheory.T.standardFrame_sphericalDoubleCoset_reps_local

theorem offBad : ∀ (hL : GlobalTheory.Published.LocalLanglandsGL) (D : D7) (P : Pin hL D) (X : GlobalTheory.NJoin.RealAt D P.cf P.C P.tp) (i : D.nd.Loc), Formalism.IndefR.RecTie.Used0 D (D.nd.mu i) → ∀ Pp, GlobalTheory.Hk3.Good X.R (X.tupT (D.nd.mu i)) Pp → ∀ v : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)), Formalism.L2.NG.OverPl Pp v → v ∉ Formalism.L2.badPl D i := GlobalTheory.T.good_place_not_bad_below

theorem rep_mem {D : D7} (V : Formalism.BasicNotions.TH.HSp D) (Pp : HeightOneSpectrum (𝓞 D.host.E)) (d : List ℤ)
    {γ : Formalism.L2.Theta.GA D V} (hγ : γ ∈ GlobalTheory.Hk3.rep V Pp d) : γ ∈ Formalism.L2.Theta.GfC V := by
  unfold GlobalTheory.Hk3.rep at hγ
  split_ifs at hγ with hl
  · obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, hR⟩ := hl.choose_spec
    exact (hR.1 γ hγ).1
  · simp at hγ

theorem cast_sum {D : D7} (M : MtFam D) (μ : D.what₂.Tup) {j k : ℕ} (e : j = k) (h1 : 1 ≤ k) (h2 : k ≤ D.R.m)
    (h1' : 1 ≤ j) (h2' : j ≤ D.R.m) (f' : D.what₂.Mt μ j) {ι : Type} (R : Finset ι) (r : ι → Formalism.AUTREP.GAf D.host.E D.R.nV)
    (c : ℂ) (h : ∑ γ ∈ R, Formalism.L2.NG.rt D.host.E D.R.nV (r γ) ((M μ k h1 h2).real (e ▸ f')) = c • (M μ k h1 h2).real (e ▸ f')) :
    ∑ γ ∈ R, Formalism.L2.NG.rt D.host.E D.R.nV (r γ) ((M μ j h1' h2').real f') = c • (M μ j h1' h2').real f' := by
  subst e
  exact h

theorem extV_inf {D : D7} {cf : CharFrame D} {nch : NChoice D} {tp : TupTied D cf nch} (X : GlobalTheory.NJoin.RealAt D cf nch tp)
    (j : Fin D.R.m) (t : X.T) (y : (X.R.HV j t).H) {a b : Formalism.L2.Theta.GA D (Formalism.IndefR.Links.Vc D j)}
    (ha : a ∈ Formalism.L2.Theta.GinfC (Formalism.IndefR.Links.Vc D j)) (hb : b ∈ Formalism.L2.Theta.GfC (Formalism.IndefR.Links.Vc D j)) :
    X.R.extV j t y (a * b) = (X.R.cV j).ρ a⁻¹ (X.R.extV j t y b) := by
  have hcv := (X.given.core.models.cV j).1
  have e0 : ∀ g, X.R.extV j t y g = (X.R.cV j).ρ g⁻¹ ((X.R.HV j t).e y ((Formalism.L2.Theta.finHom (Formalism.IndefR.Links.Vc D j)).rangeRestrict g)) := fun g => rfl
  have e1 : (Formalism.L2.Theta.finHom (Formalism.IndefR.Links.Vc D j)).rangeRestrict a = 1 := by
    apply Subtype.ext
    exact (MonoidHom.mem_ker (f := Formalism.L2.Theta.finHom (Formalism.IndefR.Links.Vc D j))).1 ha
  refine (e0 (a * b)).trans (Eq.trans ?_ (congrArg ((X.R.cV j).ρ a⁻¹) (e0 b)).symm)
  have e2 : (Formalism.L2.Theta.finHom (Formalism.IndefR.Links.Vc D j)).rangeRestrict (a * b) = (Formalism.L2.Theta.finHom (Formalism.IndefR.Links.Vc D j)).rangeRestrict b := by
    rw [map_mul, e1, one_mul]
  have e3 : (X.R.cV j).ρ (a * b)⁻¹ = (X.R.cV j).ρ a⁻¹ := by
    rw [mul_inv_rev, map_mul, hcv _ (inv_mem hb), one_mul]
  have e4 : (X.R.cV j).ρ b⁻¹ = 1 := hcv _ (inv_mem hb)
  have e5 : ∀ x, (X.R.cV j).ρ b⁻¹ x = x := fun x => by rw [e4]; rfl
  have e6 := congr (congrArg DFunLike.coe e3) (congrArg ((X.R.HV j t).e y) e2)
  exact e6.trans (congrArg ((X.R.cV j).ρ a⁻¹) (e5 _)).symm

theorem main : GlobalTheory.Published.AutomorphicFormsFiniteGL → ∀ (hL : GlobalTheory.Published.LocalLanglandsGL) (D : D7) (P : Pin hL D), ∀ (X : GlobalTheory.NJoin.RealAt D P.cf P.C P.tp) (_ : GlobalTheory.NJoin.Agree X P.M P.rep), Formalism.MainNotions.SumRepresentations.Conclusion41 D → Formalism.MainNotions.SumRepresentations.adm7 D → Formalism.MainNotions.SumRepresentations.tieLab D → ∀ (i : D.nd.Loc) (hμ : Formalism.IndefR.RecTie.Used0 D (D.nd.mu i)) (j : Fin D.R.m) (hj : j.1 + 1 = D.nd.j i), ∀ (Q : D.naut.AV i), ∀ Pp, GlobalTheory.Hk3.Good X.R (X.tupT (D.nd.mu i)) Pp → Formalism.MainNotions.SchurIrreducible.IsSplit (E := D.host.E) (Pp.under (𝓞 D.host.F)) → ∀ d, GlobalTheory.Hk3.IsLab (Formalism.IndefR.Links.Vc D j) Pp d → ∃ c : ℂ, ∀ f' : D.what₂.Mt (D.nd.mu i) (j.1 + 1), (hj ▸ f' : D.what₂.Mt (D.nd.mu i) (D.nd.j i)) ∈ D.naut.typeV i Q → ∀ g, ∑ γ ∈ GlobalTheory.Hk3.rep (Formalism.IndefR.Links.Vc D j) Pp d, X.fn hμ j f' (g * γ) = c • X.fn hμ j f' g := by
  intro hAF hL D P X hAg h41 h7 hTie i hμ j hj Q Pp hG hS d hd
  obtain ⟨s, α, hov, hα, hR1, hR2⟩ := frameReps D (Formalism.IndefR.Links.Vc D j) D.R.nV hAg.hF (hAg.PV j) (hAg.stdV j) Pp hS d hd
  obtain ⟨c, hc1⟩ := irrScalar D.host.E D.R.nV (P.M.loc i).wt (P.H.av.S i Q) (P.H.av.irr i Q) s α hα _ _ _ hR1 hR2
  have hc := isoScalar D.host.E D.R.nV (P.M.loc i).wt (P.H.av.S i Q) (P.H.av.irr i Q) s.v _ _ _ c hc1
  have hsB : s.v ∉ Formalism.L2.badPl D i := offBad hL D P X i hμ Pp hG s.v hov
  refine ⟨c, fun f' hf' g => ?_⟩

  have hFI : (P.M.loc i).real (hj ▸ f') ∈ Formalism.L2.NG.isoTyp (P.M.loc i).wt.ρ (P.H.av.S i Q) := by
    have h := hf'
    rw [P.H.av.typeV i Q] at h
    exact h
  have hFT : (P.M.loc i).real (hj ▸ f') ∈ Formalism.L2.NG.TypeSp (P.M.loc i).wt.ρ (P.M.loc i).J (P.M.loc i).χ := by
    rw [← (P.M.loc i).real_range]
    exact ⟨_, rfl⟩
  have hfix : ∀ κ ∈ Umax D.host.E D.R.nV, TrivOutside {s.v} κ →
      Formalism.L2.NG.rt D.host.E D.R.nV κ ((P.M.loc i).real (hj ▸ f')) = (P.M.loc i).real (hj ▸ f') := by
    intro κ hκ ht
    have ht' : TrivOutside (Formalism.L2.badPl D i)ᶜ κ := fun v hv => ht v fun h => hv (by
      rw [Set.mem_singleton_iff.1 h]
      exact hsB)
    obtain ⟨h1, h2⟩ := P.H.hecke.J_hyp i κ ht'
    have hJ : κ ∈ (P.M.loc i).J := h1.2 hκ
    have e := hFT.2 ⟨κ, hJ⟩
    rw [h2 hJ] at e
    simpa using e
  have hkey := cast_sum P.M (D.nd.mu i) hj _ _ (by omega) (by omega) f' _ _ c (hc _ hFI hfix)
  have hreal : ∀ w, hAg.eW (D.nd.mu i) hμ j (X.fn hμ j f' ((hAg.PV j).ψ w)) =
      (P.M (D.nd.mu i) (j.1 + 1) (by omega) (by omega)).real f' (hAg.a j * w) := by
    intro w
    rw [hAg.real (D.nd.mu i) hμ j f' (hAg.a j * w), inv_mul_cancel_left]
  have hfin : ∀ w, ∑ γ ∈ GlobalTheory.Hk3.rep (Formalism.IndefR.Links.Vc D j) Pp d, X.fn hμ j f' ((hAg.PV j).ψ w * γ) =
      c • X.fn hμ j f' ((hAg.PV j).ψ w) := by
    intro w
    apply (hAg.eW (D.nd.mu i) hμ j).injective
    rw [map_sum, map_smul, hreal]
    have e1 : ∀ γ ∈ GlobalTheory.Hk3.rep (Formalism.IndefR.Links.Vc D j) Pp d, hAg.eW (D.nd.mu i) hμ j (X.fn hμ j f' ((hAg.PV j).ψ w * γ)) =
        Formalism.L2.NG.rt D.host.E D.R.nV (Formalism.IndefR.principalLevelFrame.pre (hAg.PV j) γ)
          ((P.M (D.nd.mu i) (j.1 + 1) (by omega) (by omega)).real f') (hAg.a j * w) := by
      intro γ hγ
      have e2 : (hAg.PV j).ψ w * γ = (hAg.PV j).ψ (w * Formalism.IndefR.principalLevelFrame.pre (hAg.PV j) γ) := by
        rw [map_mul, Formalism.IndefR.principalLevelFrame.pre_spec (hAg.PV j) (rep_mem _ Pp d hγ)]
      rw [e2, hreal]
      show _ = (P.M (D.nd.mu i) (j.1 + 1) (by omega) (by omega)).real f' (hAg.a j * w * Formalism.IndefR.principalLevelFrame.pre (hAg.PV j) γ)
      rw [mul_assoc]
    rw [Finset.sum_congr rfl e1, ← Finset.sum_apply, hkey]
    rfl
  obtain ⟨a₀, ha₀, k, hk, rfl⟩ := (GlobalTheory.T.adelicUnitary_real_mul_finite_decomposition D (Formalism.IndefR.Links.Vc D j)).1 g
  obtain ⟨w, rfl⟩ := (hAg.PV j).onto k hk
  obtain ⟨y, hy, -⟩ := X.existsUnique_vec hμ j f'
  have hw := hfin w
  rw [← hy] at hw ⊢
  have e1 : ∀ γ ∈ GlobalTheory.Hk3.rep (Formalism.IndefR.Links.Vc D j) Pp d,
      X.R.extV j (X.tupT (D.nd.mu i)) y (a₀ * (hAg.PV j).ψ w * γ) =
        (X.R.cV j).ρ a₀⁻¹ (X.R.extV j (X.tupT (D.nd.mu i)) y ((hAg.PV j).ψ w * γ)) := fun γ hγ =>
    (congrArg (X.R.extV j (X.tupT (D.nd.mu i)) y) (mul_assoc _ _ _)).trans
      (extV_inf X j _ y ha₀ (mul_mem ((hAg.PV j).into w) (rep_mem _ Pp d hγ)))
  calc ∑ γ ∈ GlobalTheory.Hk3.rep (Formalism.IndefR.Links.Vc D j) Pp d, X.R.extV j (X.tupT (D.nd.mu i)) y (a₀ * (hAg.PV j).ψ w * γ)
      = ∑ γ ∈ GlobalTheory.Hk3.rep (Formalism.IndefR.Links.Vc D j) Pp d,
          (X.R.cV j).ρ a₀⁻¹ (X.R.extV j (X.tupT (D.nd.mu i)) y ((hAg.PV j).ψ w * γ)) := Finset.sum_congr rfl e1
    _ = (X.R.cV j).ρ a₀⁻¹ (∑ γ ∈ GlobalTheory.Hk3.rep (Formalism.IndefR.Links.Vc D j) Pp d,
          X.R.extV j (X.tupT (D.nd.mu i)) y ((hAg.PV j).ψ w * γ)) := (map_sum _ _ _).symm
    _ = (X.R.cV j).ρ a₀⁻¹ (c • X.R.extV j (X.tupT (D.nd.mu i)) y ((hAg.PV j).ψ w)) := congrArg _ hw
    _ = c • (X.R.cV j).ρ a₀⁻¹ (X.R.extV j (X.tupT (D.nd.mu i)) y ((hAg.PV j).ψ w)) := map_smul _ _ _
    _ = c • X.R.extV j (X.tupT (D.nd.mu i)) y (a₀ * (hAg.PV j).ψ w) :=
      congrArg _ (extV_inf X j _ y ha₀ ((hAg.PV j).into w)).symm

end GlobalTheory.SummandEig
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LpTwOneNe
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.GalOfCusp GlobalTheory.TheRec
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory

theorem WeilDeligne.WD.lpTw_one_ne {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω]
    [IsAlgClosure E Ω] {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}
    (x : WD h) : 0 < x.lpDim → x.lpTw 1 ≠ x := by
  obtain ⟨n, a, rfl⟩ := WD.exists_rep x
  intro hn heq
  rw [WD.lpTw_mk, WD.mk_eq_mk] at heq
  obtain ⟨e, he, -⟩ := heq
  rw [WD.lpDim_mk, Module.finrank_fin_fun] at hn
  set σ := frob h
  set T := (a.tw 1).ρ σ
  set B := a.ρ σ
  have hconj : (e : (Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ)) ∘ₗ T ∘ₗ (e.symm : (Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ)) = B := by
    refine LinearMap.ext fun v => ?_
    show e ((a.tw 1).ρ σ (e.symm v)) = a.ρ σ v
    rw [he, LinearEquiv.apply_symm_apply]
  have hdet : LinearMap.det T = LinearMap.det B := by
    rw [← hconj, LinearMap.det_conj]
  have hT : T = ((normV w : ℕ) : ℂ) • B := by
    show (a.tw 1).ρ σ = _
    rw [WDRep.tw_ρ, deg_frob]
    simp only [Complex.ofReal_one, Complex.cpow_one, zpow_one]
    rfl
  rw [hT, LinearMap.det_smul, Module.finrank_fin_fun] at hdet
  have hB : LinearMap.det B ≠ 0 := by
    intro h0
    have h1 : B * a.ρ σ⁻¹ = 1 := by
      show a.ρ σ * a.ρ σ⁻¹ = 1
      rw [← map_mul, mul_inv_cancel, map_one]
    have := congrArg LinearMap.det h1
    rw [map_mul, h0, zero_mul, map_one] at this
    exact zero_ne_one this
  have hq : ((normV w : ℕ) : ℂ) ^ n = 1 := by
    have := mul_right_cancel₀ hB (hdet.trans (one_mul _).symm)
    exact this
  have hq' : (normV w : ℕ) ^ n = 1 := by exact_mod_cast hq
  have h1q := one_lt_normV w
  have : 1 < (normV w : ℕ) ^ n := Nat.one_lt_pow hn.ne' h1q
  omega

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.NEqZeroOfSumList
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.GalOfCusp GlobalTheory.TheRec
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.WeilDeligne.NoTwHom

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}

def IsTw {V V' : Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    [AddCommGroup V'] [Module ℂ V'] [FiniteDimensional ℂ V'] (a : WDRep h V) (b : WDRep h V')
    (f : V →ₗ[ℂ] V') : Prop :=
  ∀ (σ : Weil h) (v : V), f ((((normV w : ℕ) : ℂ) ^ deg σ) • a.ρ σ v) = b.ρ σ (f v)

def NoTw (X Y : WD h) : Prop :=
  ∀ (V V' : Type) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    [AddCommGroup V'] [Module ℂ V'] [FiniteDimensional ℂ V'] (a : WDRep h V) (b : WDRep h V'),
    WD.mk a = X → WD.mk b = Y → ∀ f : V →ₗ[ℂ] V', IsTw a b f → f = 0

section
variable {V V' W W' : Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
  [AddCommGroup V'] [Module ℂ V'] [FiniteDimensional ℂ V']
  [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
  [AddCommGroup W'] [Module ℂ W'] [FiniteDimensional ℂ W']

theorem IsTw.inl {V2 : Type} [AddCommGroup V2] [Module ℂ V2] [FiniteDimensional ℂ V2]
    {a1 : WDRep h V} {a2 : WDRep h V2} {b : WDRep h V'} {g : V × V2 →ₗ[ℂ] V'}
    (hg : IsTw (a1.sum a2) b g) : IsTw a1 b (g ∘ₗ LinearMap.inl ℂ V V2) := by
  intro σ v
  have : LinearMap.inl ℂ V V2 ((((normV w : ℕ) : ℂ) ^ deg σ) • a1.ρ σ v) =
      (((normV w : ℕ) : ℂ) ^ deg σ) • (a1.sum a2).ρ σ (LinearMap.inl ℂ V V2 v) := by
    ext <;> simp
  rw [LinearMap.comp_apply, this, hg]; rfl

theorem IsTw.inr {V2 : Type} [AddCommGroup V2] [Module ℂ V2] [FiniteDimensional ℂ V2]
    {a1 : WDRep h V} {a2 : WDRep h V2} {b : WDRep h V'} {g : V × V2 →ₗ[ℂ] V'}
    (hg : IsTw (a1.sum a2) b g) : IsTw a2 b (g ∘ₗ LinearMap.inr ℂ V V2) := by
  intro σ v
  have : LinearMap.inr ℂ V V2 ((((normV w : ℕ) : ℂ) ^ deg σ) • a2.ρ σ v) =
      (((normV w : ℕ) : ℂ) ^ deg σ) • (a1.sum a2).ρ σ (LinearMap.inr ℂ V V2 v) := by
    ext <;> simp
  rw [LinearMap.comp_apply, this, hg]; rfl

theorem IsTw.fst {V2 : Type} [AddCommGroup V2] [Module ℂ V2] [FiniteDimensional ℂ V2]
    {a : WDRep h W} {b1 : WDRep h V} {b2 : WDRep h V2} {g : W →ₗ[ℂ] V × V2}
    (hg : IsTw a (b1.sum b2) g) : IsTw a b1 (LinearMap.fst ℂ V V2 ∘ₗ g) := by
  intro σ v
  rw [LinearMap.comp_apply, hg]; rfl

theorem IsTw.snd {V2 : Type} [AddCommGroup V2] [Module ℂ V2] [FiniteDimensional ℂ V2]
    {a : WDRep h W} {b1 : WDRep h V} {b2 : WDRep h V2} {g : W →ₗ[ℂ] V × V2}
    (hg : IsTw a (b1.sum b2) g) : IsTw a b2 (LinearMap.snd ℂ V V2 ∘ₗ g) := by
  intro σ v
  rw [LinearMap.comp_apply, hg]; rfl

end

end GlobalTheory.WeilDeligne.NoTwHom
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.NotMono0LpCharLpSp
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.GalOfCusp GlobalTheory.TheRec
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section
open scoped TensorProduct

namespace GlobalTheory.SegLen

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}

theorem tmul_ne_zero_of_ne {X Y : Type} [AddCommGroup X] [Module ℂ X] [AddCommGroup Y] [Module ℂ Y] {x : X} {y : Y}
    (hx : x ≠ 0) (hy : y ≠ 0) : x ⊗ₜ[ℂ] y ≠ 0 := by
  obtain ⟨φ, hφ⟩ : ∃ φ : Module.Dual ℂ Y, φ y ≠ 0 := by
    by_contra hc
    push_neg at hc
    exact hy ((Module.forall_dual_apply_eq_zero_iff ℂ y).1 hc)
  intro h0
  have := congrArg ((TensorProduct.rid ℂ X).toLinearMap ∘ₗ LinearMap.lTensor X φ) h0
  simp only [LinearMap.comp_apply, LinearMap.lTensor_tmul, LinearEquiv.coe_coe, TensorProduct.rid_tmul,
    map_zero] at this
  exact hx ((smul_eq_zero.1 this).resolve_left hφ)

theorem lpChar_lpSp_one' (x : WD h) : x.lpChar (WD.lpSp h 1) = x := by
  have h1 : WD.lpSp h 1 = WD.lpOfChar h (WeilDeligne.unrChar h (qPow w 0)) (isSmooth_unrChar h _) := by
    refine WD.sound ⟨.refl _ _, fun σ v => ?_, fun v => ?_⟩
    · funext i
      simp [WDRep.spEig]
    · funext i
      simp [shiftEnd_apply]
  rw [h1, lpChar_lpOfChar]
  exact WD.lpTw_zero x

theorem not_mono0_lpChar_lpSp {x : WD h} (hx : IsIrrWD x) {n : ℕ} (hn : 2 ≤ n) :
    ¬ (x.lpChar (WD.lpSp h n)).mono0 := by
  have h0 := TemperedRec.monodromy_zero_of_irreducible_weilDeligne E Ω A w h x hx
  obtain ⟨m, b, rfl, hirr⟩ := hx
  have : Nontrivial (Fin m → ℂ) := Model.nontrivial_of_isIrreducible hirr
  obtain ⟨v, hv⟩ := exists_ne (0 : Fin m → ℂ)
  rw [WD.monodromyZero_ofWeilDeligneRepClass_iff] at h0
  rw [WD.lpSp, WD.lpChar_mk, WD.monodromyZero_ofWeilDeligneRepClass_iff, WDRep.tensor_N, h0, WDRep.sp_N, LinearMap.rTensor_zero, zero_add]
  intro hN
  obtain ⟨u, hu⟩ : ∃ u, shiftEnd n u ≠ 0 := by
    by_contra hc
    push_neg at hc
    exact shiftEnd_ne_zero hn (LinearMap.ext hc)
  have := LinearMap.congr_fun hN (v ⊗ₜ u)
  rw [LinearMap.lTensor_tmul, LinearMap.zero_apply] at this
  exact tmul_ne_zero_of_ne hv hu this

end GlobalTheory.SegLen
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.PeriodRelationsTrueColumnsAtTupleStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.AtG
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.periodRelations_trueColumns_at_tuple : ∀ {B : GlobalTheory.Mem.Base} {X : GlobalTheory.Mem.PreX B.toPre} (I : GlobalTheory.Mem.Col2.TC B X) (h : I.Ok) (l : I.Laws) (Z : GlobalTheory.Mem.Col2.TC.Later B (I.cols l)) (l0 : I.Law0 l), GlobalTheory.Mem.Col2.ColIn.JetsIn I → ∀ (EX : ErrX (I.rec7 l Z)) (Dx : DivX (I.rec7 l Z)) (a : I.ι), EX.piG = X.piG → EX.piT = X.piT → I.QpIs Dx.Qp → RowPin I h l Z a → TiesAt (I.rec7 l Z) EX Dx a := by
  first | exact @GlobalTheory.TiesTrue.tiesAt_true | exact GlobalTheory.TiesTrue.tiesAt_true | (intros; apply GlobalTheory.TiesTrue.tiesAt_true <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.RationalUnitaryOrthonormalCoordsIsColumnIsometryStatement
section
open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.UG Formalism.MainNotions Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV Formalism.L2.PairingIndexBounds.F Formalism.MainNotions.G.KAat Formalism.L2.Forms Formalism.MainNotions.G GlobalTheory.TwU GlobalTheory.TwV
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rationalUnitary_orthonormalCoords_isColumnIsometry : UnderTie (fun {D L hT Gi Gl Kc Y cX ex t u μ St} A dtU a =>
    ∀ i (hi : i ≤ D.R.m) (γ : GL (Fin (D.R.N i)) D.host.E), γ ∈ UJ (sigD D : D.host.E →+* D.host.E) (gramN D i hi) →
      ∃ g : UF t.X.E (D.R.N i), seamGL t.seam g.1 = A.crd i hi * γ * (A.crd i hi)⁻¹) := by
  first | exact @GlobalTheory.TwRat.ratUnitCol | exact GlobalTheory.TwRat.ratUnitCol | (intros; apply GlobalTheory.TwRat.ratUnitCol <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.RowsBAndLocalLiftsStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rows_b_and_local_lifts : GlobalTheory.NRows.Hypotheses₂ → ∀ (hL : GlobalTheory.Published.LocalLanglandsGL) (D : D7) (P : Pin hL D), Join P → GlobalTheory.NRows.RowsA D → Formalism.MainNotions.SumRepresentations.adm1 D → (∀ i : D.nd.Loc, GlobalTheory.RowCopy.LamPos D (D.nd.mu i) (D.nd.j i)) → GlobalTheory.NRows.RowsB D ∧ ∀ i, PairLift D.nd D.naut i ∧ SplitBC D.nd D.naut i ∧ RepOfLoc D.nd D.naut i := by
  first | exact @GlobalTheory.RowsBClosing.main | exact GlobalTheory.RowsBClosing.main | (intros; apply GlobalTheory.RowsBClosing.main <;> assumption)
end

