import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1791
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1777
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsNotRelZero
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.UnitaryConjugation
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1674
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1702
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousAtPlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1738
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1728
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0102
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1783
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0045
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0481
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1181
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0956
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0356
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1196
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1638
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1383
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1038
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1387
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1397
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1425
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InertPlaceLocalFieldDataExists
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsUniqueIsConjAt
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RamificationIdxEqOneOfIsSquare
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1793
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1778
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0005
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueIsFunForm
import Formalism.SharpRestriction.Divisibility.PrimeDegreeVariant
import Formalism.PieriBlockIdeals.Bundle0004
import Formalism.MirabolicMackeyTheory.MirabolicMackeyProofs.Bundle0003
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.FormulaAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1054
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.StatementWithTransposeOfBranching
import Formalism.LocalToGlobal.Divisibility.Bundle0002
import Formalism.LocalToGlobal.Columns.Bundle0014
import Formalism.QuotientMetricDivisors.HermitianTwistDivisors.Bundle0002
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0253
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0004
import Development.AbelianVarietyTheory.Statements.CuspidalUnitaryTwists.ExistsSmallSpherical
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0356
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1802
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1790
import Development.AbelianVarietyTheory.Definitions.Divisors.PointShiftSt
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0062

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbsNormGridModulusLeExpDepthLogNormSum
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.TestLat GlobalTheory.SumSize GlobalTheory.RowClaim GlobalTheory.ClassCount

noncomputable section

namespace GlobalTheory.ModulNorm

open GlobalTheory.SumSize

theorem absNorm_map_of_finrank_two {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (h2 : Module.finrank F E = 2) (I : Ideal (𝓞 F)) :
    Ideal.absNorm (Ideal.map (algebraMap (𝓞 F) (𝓞 E)) I) = Ideal.absNorm I ^ 2 := by
  rw [Ideal.absNorm_algebraMap, ← h2]
  congr 1
  exact (IsFractionRing.finrank_eq (𝓞 F) F (𝓞 E) E).symm

theorem absNorm_le_sq_of_under {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (h2 : Module.finrank F E = 2) (P : HeightOneSpectrum (𝓞 E)) :
    Ideal.absNorm P.asIdeal ≤ Ideal.absNorm (P.under (𝓞 F)).asIdeal ^ 2 := by
  have hle : Ideal.map (algebraMap (𝓞 F) (𝓞 E)) (P.under (𝓞 F)).asIdeal ≤ P.asIdeal :=
    Ideal.map_le_iff_le_comap.2 le_rfl
  have hd := Ideal.absNorm_dvd_absNorm_of_le hle
  rw [absNorm_map_of_finrank_two h2] at hd
  refine Nat.le_of_dvd (pow_pos (Nat.pos_of_ne_zero ?_) 2) hd
  rw [Ne, Ideal.absNorm_eq_zero_iff]
  exact (P.under (𝓞 F)).ne_bot

theorem absNorm_modul_le : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc), D.host.F = maximalRealSubfield D.host.E → (Ideal.absNorm G.modul : ℝ) ≤ Real.exp (2 * sig G) := by
  intro D T L sc G hF
  have h2 : Module.finrank D.host.F D.host.E = 2 := by
    rw [hF]; exact Algebra.IsQuadraticExtension.finrank_eq_two _ _
  have hmod : G.modul = ∏ v ∈ G.pl.S0, (G.pl.w v).asIdeal ^ G.pl.depth sc v := rfl
  rw [hmod, map_prod, Nat.cast_prod, sig, Finset.mul_sum, Real.exp_sum]
  refine Finset.prod_le_prod (fun v _ => by positivity) fun v hv => ?_
  have hw : Ideal.absNorm (G.pl.w v).asIdeal ≤ Ideal.absNorm v.asIdeal ^ 2 := by
    have := absNorm_le_sq_of_under h2 (G.pl.w v)
    rwa [G.pl.under_w hv] at this
  have hpos : (0 : ℝ) < Ideal.absNorm v.asIdeal := by
    have : Ideal.absNorm v.asIdeal ≠ 0 := by rw [Ne, Ideal.absNorm_eq_zero_iff]; exact v.ne_bot
    exact_mod_cast Nat.pos_of_ne_zero this
  rw [map_pow, Nat.cast_pow]
  calc ((Ideal.absNorm (G.pl.w v).asIdeal : ℕ) : ℝ) ^ G.pl.depth sc v
      ≤ ((Ideal.absNorm v.asIdeal : ℝ) ^ 2) ^ G.pl.depth sc v := by
        gcongr
        exact_mod_cast hw
    _ = Real.exp (2 * ((G.pl.depth sc v : ℝ) * Real.log (Ideal.absNorm v.asIdeal))) := by
        rw [← pow_mul, ← Real.rpow_natCast, Real.rpow_def_of_pos hpos]
        congr 1
        push_cast
        ring

end GlobalTheory.ModulNorm
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AddCharHalfTraceTensorLatticeHeisenbergCocycleStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open Classical
open scoped TensorProduct ComplexConjugate GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ alpha beta Num skewGram blk conjU)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model HasExp SplitsFully Chars)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open scoped GlobalTheory.VacAny

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.addChar_halfTrace_tensorLattice_heisenbergCocycle : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    (B : Base F E), B.IsGood σ → ∀ {n d : ℕ} (X : Spc F E n) (Y : Spc F E d) (r s r' s' : ℕ),
    X.IsHerm σ B r s → Y.IsSkew σ B r' s' → ∀ θ : 𝓞 E, (θ : E) + σ θ = 1 → ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F,
    ∀ γ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.latAtV X Y v, ∀ γ' ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.latAtV X Y v,
      B.ψ (⅟(2 : AF F) * GlobalTheory.WeilM.symp (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA σ) (inclR (F := F) (AF F) (θ : E))
          (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F X.J) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F Y.J) (γ + γ') (γ + γ')) =
        B.ψ (⅟(2 : AF F) * GlobalTheory.WeilM.symp (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA σ) (inclR (F := F) (AF F) (θ : E))
            (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F X.J) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F Y.J) γ γ) *
          B.ψ (⅟(2 : AF F) * GlobalTheory.WeilM.symp (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA σ) (inclR (F := F) (AF F) (θ : E))
            (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F X.J) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F Y.J) γ' γ') *
          B.ψ (-(⅟(2 : AF F) * GlobalTheory.WeilM.symp (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA σ) (-1)
            (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F X.J) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F Y.J) γ γ')) := by
  first | exact @GlobalTheory.VacCocycle.psi_half_symp_add | exact GlobalTheory.VacCocycle.psi_half_symp_add | (intros; apply GlobalTheory.VacCocycle.psi_half_symp_add <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicAddCharEqArchimedeanMulFinprodLocalStatement
section
open scoped Matrix GlobalTheory.VacAny
open NumberField IsDedekindDomain MeasureTheory Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RatWeilOp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adelicAddChar_eq_archimedean_mul_finprod_local : ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), Continuous ψ → ∀ x : AF F,
    (Function.mulSupport fun v : Pl F => GlobalTheory.LatVac.psiAt ψ v (evFin F v x)).Finite ∧
    ψ x = ψ (pairA F (fstA F x) 0) * ∏ᶠ v : Pl F, GlobalTheory.LatVac.psiAt ψ v (evFin F v x) := by
  first | exact @GlobalTheory.PsiProd.psi_prod | exact GlobalTheory.PsiProd.psi_prod | (intros; apply GlobalTheory.PsiProd.psi_prod <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicHeisenbergActsByLocalSchrodinger
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open Classical
open scoped TensorProduct ComplexConjugate GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ alpha beta Num skewGram blk conjU)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model HasExp SplitsFully Chars)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

open scoped GlobalTheory.VacAny

noncomputable section

namespace GlobalTheory.VacBridge

theorem rho_acts_locCo : ∀ {F : Type} [Field F] [NumberField F] {W : Type} [AddCommGroup W] [Module (AF F) W]
    {B : W → W → AF F} {κ : Type} [Fintype κ] (co : GlobalTheory.WeilM.Darboux B κ) (ψ : AddChar (AF F) ℂ)
    (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F) (γ : W), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.AdelicU.evFin F v) γ →
    ∀ φ : (κ → Fv F v) → ℂ, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Acts (GlobalTheory.AdelicU.evFin F v) (co.rho ψ γ) φ
      (GlobalTheory.WeilM.schr (GlobalTheory.LatVac.psiAt ψ v) (GlobalTheory.LatVac.locCo co v γ) φ) := by
  intro F _ _ W _ _ B κ _ co ψ v γ hγ φ r hr
  funext x
  set w := co.e γ with hw
  have hcomp : ∀ u : AF F, GlobalTheory.AdelicU.evFin F v u = 0 → u • w = 0 := fun u hu => by
    rw [hw, ← LinearEquiv.map_smul, hγ u hu, map_zero]
  have ha1 : ∀ k, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.AdelicU.evFin F v) (w.1 k) := fun k u hu => by
    have := congrArg (fun z => z.1 k) (hcomp u hu)
    simpa using this
  have ha2 : ∀ k, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.AdelicU.evFin F v) (w.2 k) := fun k u hu => by
    have := congrArg (fun z => z.2 k) (hcomp u hu)
    simpa using this
  have hshift : r (x + w.1) = r x := hr.1 x w.1 (GlobalTheory.VacAny.at_pi ha1)
  simp only [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens, GlobalTheory.WeilM.Darboux.rho, GlobalTheory.WeilM.schr, ← hw, hshift]
  have hat : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.AdelicU.evFin F v) (x ⬝ᵥ w.2 + ⅟(2 : AF F) * (w.1 ⬝ᵥ w.2)) :=
    GlobalTheory.VacAny.at_add (GlobalTheory.VacAny.at_sum _ fun k _ => GlobalTheory.VacAny.at_mul_left _ (ha2 k))
      (GlobalTheory.VacAny.at_mul_left _ (GlobalTheory.VacAny.at_sum _ fun k _ => GlobalTheory.VacAny.at_mul_left _ (ha2 k)))
  rw [GlobalTheory.StdVacuum.psi_eq_psiLoc ψ v _ hat, ← GlobalTheory.LatVac.psiAt_apply]
  have e1 : GlobalTheory.AdelicU.evFin F v (x ⬝ᵥ w.2 + ⅟(2 : AF F) * (w.1 ⬝ᵥ w.2)) =
      (fun i => GlobalTheory.AdelicU.evFin F v (x i)) ⬝ᵥ (GlobalTheory.LatVac.locCo co v γ).2 +
        ⅟(2 : Fv F v) * ((GlobalTheory.LatVac.locCo co v γ).1 ⬝ᵥ (GlobalTheory.LatVac.locCo co v γ).2) := by
    simp only [dotProduct, map_add, map_sum, map_mul, GlobalTheory.VacAny.evFin_invOf_two, hw]
    rfl
  have e2 : (fun i => GlobalTheory.AdelicU.evFin F v ((x + w.1) i)) =
      (fun i => GlobalTheory.AdelicU.evFin F v (x i)) + (GlobalTheory.LatVac.locCo co v γ).1 := by
    funext i
    simp only [Pi.add_apply, map_add, hw]
    rfl
  rw [e1, e2, mul_assoc]

end GlobalTheory.VacBridge
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicLiftMemCuspFormMultiplicitySpace
section
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.AdelicScalar GlobalTheory.LiftRows GlobalTheory.LowRow

namespace GlobalTheory.LowRow.CuspLift

theorem liftIsCuspC : GlobalTheory.Published.CuspRapidDecay → ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type}
    {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks)
    (F : Face D A), LiftIsCuspC R F := by
  intro hP D G _ _ Pl0 T A Ks _ _ _ R F
  intro i t σ s P cμ cη m ω BW f₀ f c io hd ν 𝓕 hν φ hφ
  obtain ⟨hcore, -, hemb, -, -, hom, -, -, hpt, hc, hio⟩ := id hd
  have h5 := GlobalTheory.Core5.of_core hcore
  have hm := h5.models
  have hpos : ∀ τ, (gramAt D (Vc D i) τ).PosDef := fun τ => by
    have := D.sp.V_sig ((i : ℕ) + 1) (tauE D τ)
    rw [hm.vpos i] at this
    exact GlobalTheory.DefiniteQuotient.posDef_of_signature this
  obtain ⟨hM, w, hw⟩ := GlobalTheory.T.liftModel_holomorphic_overReflexField R F h5 i σ s hemb
  have : IsTopologicalGroup (GA D (Vc D i)) := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA _ _
  have hF := GlobalTheory.ThetaIntegrand.form_continuous (finHom (Vc D i)).rangeRestrict (GQ (Vc D i)) c.ρ hc.2.2.1
    (eventually_grpOf (Vc D i) (R.βV i) (datV i R.Pg (R.Q t) P m)) hφ
  have key := GlobalTheory.DefLift.ThetaMap.exists_member hP hom hm.inf hpos hM hw hc
    (pureTensorO R.ψ R.θ (Vc D i) (Wc D i) (fun _ => 1) (cart (R.MW i σ)) (R.BV i) BW f) hpt hio
    (GlobalTheory.T.lowering_part_kills_fock_product_minors R F i t σ s P cμ cη m ω BW f₀ f c io hd)
    (J := levS _ (R.βW i) (R.datWp i R.triv)) (fun _ hk => hk.1) (GlobalTheory.DefLift.ThetaMap.level_open _ _ _)
    (fun k hk Q => GlobalTheory.PrincipalLevelFock.levW_fix_ptAt R F i t σ s P cμ cη m ω BW f₀ f c io hd Q k hk)
    (GlobalTheory.IndefiniteRowSideFullHecke.VectorLevelCharacters.principalLevelCharacter_eq_one R i)
    (fun Q h g ξ hξ => GlobalTheory.T.levelFockVector_heisenbergAverage_isotropic_eq_zero R F i t σ s P cμ cη m ω BW f₀ f c io hd Q h g ξ hξ)
    hF (GlobalTheory.ThetaIntegrand.ext_invariant c hφ) hν.1.1 hν.2
  obtain ⟨Θ, hΘ, hΘv⟩ := key
  refine ⟨Θ, Submodule.subset_span hΘ, fun v g => ?_⟩
  rw [hΘv v]
  rfl

end GlobalTheory.LowRow.CuspLift

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicMatrixGluedAtInertPlaceProperties
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.KFinLoc
open scoped TensorProduct Matrix

noncomputable section
namespace GlobalTheory.InertBigCell

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {v : Pl F} {w : HeightOneSpectrum (𝓞 E)}

theorem gl_iotaW_apply (hw : Formalism.UG.IsInertAt F E v w) (x : w.adicCompletion E) :
    iotaW hw x = GlobalTheory.InertLocField.liftT E v ((InertChart.complEquiv hw (under_eq_of_isInertAt hw)).symm x) := rfl

theorem gl_iotaW_mul (hw : Formalism.UG.IsInertAt F E v w) (x y : w.adicCompletion E) :
    iotaW hw (x * y) = iotaW hw x * iotaW hw y := by
  rw [gl_iotaW_apply, gl_iotaW_apply, gl_iotaW_apply, map_mul, GlobalTheory.InertLocField.liftT_mul]

theorem gl_iotaW_injective (hw : Formalism.UG.IsInertAt F E v w) : Function.Injective (iotaW hw) := fun x y hxy =>
  (InertChart.complEquiv hw (under_eq_of_isInertAt hw)).symm.injective (GlobalTheory.InertLocField.liftT_injective v hxy)

theorem gl_idem_mul_iotaW (hw : Formalism.UG.IsInertAt F E v w) (x : w.adicCompletion E) :
    algebraMap (AF F) (AE F E) (GlobalTheory.LatVac.liftV v 1) * iotaW hw x = iotaW hw x := by
  rw [← Algebra.smul_def, GlobalTheory.InertLocField.liftV_one_smul, gl_iotaW_apply, GlobalTheory.InertLocField.evT_liftT]

theorem gl_iotaW_one (hw : Formalism.UG.IsInertAt F E v w) :
    iotaW hw 1 = algebraMap (AF F) (AE F E) (GlobalTheory.LatVac.liftV v 1) := by
  have h := GlobalTheory.InertLocField.liftV_one_smul (E := E) v 1
  rw [Algebra.smul_def, mul_one, _root_.map_one (GlobalTheory.InertLocField.evT E v)] at h
  rw [gl_iotaW_apply, _root_.map_one]
  exact h.symm

theorem gl_compl_mul_iotaW (hw : Formalism.UG.IsInertAt F E v w) (x : w.adicCompletion E) :
    (1 - algebraMap (AF F) (AE F E) (GlobalTheory.LatVac.liftV v 1)) * iotaW hw x = 0 := by
  rw [sub_mul, one_mul, gl_idem_mul_iotaW, sub_self]

theorem gl_compl_idem (hw : Formalism.UG.IsInertAt F E v w) :
    (1 - algebraMap (AF F) (AE F E) (GlobalTheory.LatVac.liftV v 1)) * (1 - algebraMap (AF F) (AE F E) (GlobalTheory.LatVac.liftV v 1)) =
      1 - algebraMap (AF F) (AE F E) (GlobalTheory.LatVac.liftV v 1) := by
  have h := gl_idem_mul_iotaW hw 1
  rw [gl_iotaW_one] at h
  rw [mul_sub, mul_one, sub_mul, one_mul, h, sub_self, sub_zero]

variable {ι : Type} [Fintype ι] [DecidableEq ι]

theorem gl_compl_smul_map (hw : Formalism.UG.IsInertAt F E v w) (P : Matrix ι ι (w.adicCompletion E)) :
    (1 - algebraMap (AF F) (AE F E) (GlobalTheory.LatVac.liftV v 1)) • P.map (iotaW hw) = 0 := by
  ext i j
  rw [Matrix.smul_apply, Matrix.map_apply, smul_eq_mul, gl_compl_mul_iotaW, Matrix.zero_apply]

theorem gl_map_mul_map (hw : Formalism.UG.IsInertAt F E v w) (P Q : Matrix ι ι (w.adicCompletion E)) :
    P.map (iotaW hw) * Q.map (iotaW hw) = (P * Q).map (iotaW hw) := by
  ext i k
  rw [Matrix.mul_apply, Matrix.map_apply, Matrix.mul_apply, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Matrix.map_apply, Matrix.map_apply, gl_iotaW_mul]

theorem gl_map_one_eq (hw : Formalism.UG.IsInertAt F E v w) :
    (1 : Matrix ι ι (w.adicCompletion E)).map (iotaW hw) =
      algebraMap (AF F) (AE F E) (GlobalTheory.LatVac.liftV v 1) • (1 : Matrix ι ι (AE F E)) := by
  ext i j
  rw [Matrix.map_apply, Matrix.smul_apply, Matrix.one_apply, Matrix.one_apply]
  split_ifs
  · rw [gl_iotaW_one, smul_eq_mul, mul_one]
  · rw [map_zero, smul_zero]

theorem gl_glueW_sub_one (hw : Formalism.UG.IsInertAt F E v w) (P : Matrix ι ι (w.adicCompletion E)) :
    glueW hw P - 1 = (P - 1).map (iotaW hw) := by
  rw [Matrix.map_sub _ (map_sub (iotaW hw)), gl_map_one_eq, glueW, sub_smul, one_smul]
  abel

theorem glueW_props : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {v : Pl F}
    {w : HeightOneSpectrum (𝓞 E)} (hw : Formalism.UG.IsInertAt F E v w) {ι : Type} [Fintype ι] [DecidableEq ι],
  (∀ P Q : Matrix ι ι (w.adicCompletion E), GlobalTheory.InertBigCell.glueW hw (P * Q) = GlobalTheory.InertBigCell.glueW hw P * GlobalTheory.InertBigCell.glueW hw Q) ∧
  GlobalTheory.InertBigCell.glueW hw (1 : Matrix ι ι (w.adicCompletion E)) = 1 ∧
  Function.Injective (GlobalTheory.InertBigCell.glueW hw (ι := ι)) ∧
  (∀ P : Matrix ι ι (w.adicCompletion E), At (evFin F v) (GlobalTheory.InertBigCell.glueW hw P - 1)) ∧
  (∀ M : Matrix ι ι (AE F E), At (evFin F v) (M - 1) → ∃ P, GlobalTheory.InertBigCell.glueW hw P = M) ∧
  (∀ (P : Matrix ι ι (w.adicCompletion E)) (u : ι → w.adicCompletion E),
    GlobalTheory.InertBigCell.glueW hw P *ᵥ (fun i => GlobalTheory.InertBigCell.iotaW hw (u i)) = fun i => GlobalTheory.InertBigCell.iotaW hw ((P *ᵥ u) i)) := by
  intro F E _ _ _ _ _ v w hw ι _ _
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro P Q
    have h1 : ∀ B : Matrix ι ι (AE F E), ((1 - algebraMap (AF F) (AE F E) (GlobalTheory.LatVac.liftV v 1)) • (1 : Matrix ι ι (AE F E))) * B =
        (1 - algebraMap (AF F) (AE F E) (GlobalTheory.LatVac.liftV v 1)) • B := fun B => by
      rw [Matrix.smul_mul, Matrix.one_mul]
    have h2 : ∀ A : Matrix ι ι (AE F E), A * ((1 - algebraMap (AF F) (AE F E) (GlobalTheory.LatVac.liftV v 1)) • (1 : Matrix ι ι (AE F E))) =
        (1 - algebraMap (AF F) (AE F E) (GlobalTheory.LatVac.liftV v 1)) • A := fun A => by
      rw [Matrix.mul_smul, Matrix.mul_one]
    rw [glueW, glueW, glueW, add_mul, mul_add, mul_add, h1, h1, h2, smul_smul, gl_compl_idem hw, gl_compl_smul_map,
      gl_compl_smul_map, gl_map_mul_map, add_zero, zero_add]
  · rw [glueW, gl_map_one_eq, ← add_smul, sub_add_cancel, one_smul]
  · intro P Q hPQ
    have h : P.map (iotaW hw) = Q.map (iotaW hw) := add_left_cancel hPQ
    exact Matrix.ext fun i j => gl_iotaW_injective hw (congrFun (congrFun h i) j)
  · intro P u hu
    rw [gl_glueW_sub_one]
    ext i j
    rw [Matrix.smul_apply, Matrix.map_apply, Matrix.zero_apply, gl_iotaW_apply]
    exact GlobalTheory.InertLocField.at_liftT v _ u hu
  · intro M hM
    have hent : ∀ i j, ∃ y, GlobalTheory.InertLocField.liftT E v y = (M - 1) i j := fun i j =>
      (GlobalTheory.InertLocField.at_iff v _).1 (fun u hu => by
        have := congrFun (congrFun (hM u hu) i) j
        rwa [Matrix.smul_apply] at this)
    choose y hy using hent
    refine ⟨1 + Matrix.of fun i j => InertChart.complEquiv hw (under_eq_of_isInertAt hw) (y i j), ?_⟩
    have hX : (Matrix.of fun i j => InertChart.complEquiv hw (under_eq_of_isInertAt hw) (y i j)).map (iotaW hw) = M - 1 := by
      ext i j
      rw [Matrix.map_apply, Matrix.of_apply, gl_iotaW_apply, RingEquiv.symm_apply_apply, hy]
    have h := gl_glueW_sub_one hw (1 + Matrix.of fun i j => InertChart.complEquiv hw (under_eq_of_isInertAt hw) (y i j))
    rw [add_sub_cancel_left, hX] at h
    exact sub_left_inj.mp h
  · intro P u
    have hd : ∀ x : ι → AE F E, ((1 - algebraMap (AF F) (AE F E) (GlobalTheory.LatVac.liftV v 1)) • (1 : Matrix ι ι (AE F E))) *ᵥ x =
        (1 - algebraMap (AF F) (AE F E) (GlobalTheory.LatVac.liftV v 1)) • x := fun x => by
      funext i
      simp [Matrix.mulVec, dotProduct, Matrix.one_apply]
    funext i
    rw [glueW, Matrix.add_mulVec, hd, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
      gl_compl_mul_iotaW, zero_add, Matrix.mulVec, dotProduct, Matrix.mulVec, dotProduct, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Matrix.map_apply, gl_iotaW_mul]

end GlobalTheory.InertBigCell
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicPoissonSummationAnyHaarStatement
section
open scoped Matrix GlobalTheory.VacAny
open NumberField IsDedekindDomain MeasureTheory Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RatWeilOp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adelicPoisson_summation_anyHaar : ∀ (F : Type) [Field F] [NumberField F], IsTotallyReal F → ∀ (ψ : AddChar (AF F) ℂ), IsStd ψ → ∀ (κ : Type) [Fintype κ]
    [MeasurableSpace (κ → AF F)] [BorelSpace (κ → AF F)] (μ : Measure (κ → AF F)) [μ.IsAddHaarMeasure],
    ∃ c : ℂ, c ≠ 0 ∧ ∀ Φ ∈ schA F κ, (fun y : κ → AF F => ∫ x, Φ x * ψ (x ⬝ᵥ y) ∂μ) ∈ schA F κ →
      thetaSum F (fun y : κ → AF F => ∫ x, Φ x * ψ (x ⬝ᵥ y) ∂μ) = c * thetaSum F Φ := by
  first | exact @GlobalTheory.PoissonReindex.poisson_any | exact GlobalTheory.PoissonReindex.poisson_any | (intros; apply GlobalTheory.PoissonReindex.poisson_any <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdjugateSubstLinearEquivSymmMemNabla
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim GlobalTheory.TestLat GlobalTheory.SumSize
open Formalism.DivisionValues (vw lw)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory

theorem funEquiv_symm_mem_nabAt_of_nabAtr : ∀ {E K ι : Type} [Field E] [NumberField E] [Field K] [NumberField K] [Fintype ι]
    (emb : ι → E →+* K) {n : ℕ} (σ : ι → DomWeight n) (M : Submodule (𝓞 E) (Fin n → E)),
    Submodule.IsLattice E M → ∀ (v : VV K fun τ => (σ τ).dual),
    v ∈ nabAtr emb (fun τ => (σ τ).dual) M → (GlobalTheory.FunObj.funEquiv σ).symm v ∈ nabAt emb σ M := by
  intro E K ι _ _ _ _ _ emb n σ M hM v hv
  have hA : ∀ τ, (tauLat emb τ M).FG := fun τ =>
    (Formalism.L2.DIV.tauLatLattice E K ι n emb τ M hM).fg
  change ((GlobalTheory.FunObj.funEquiv σ).symm v).1 ∈ nabP σ (fun τ => tauLat emb τ M)
  simp only [nabP, transLat, Submodule.mem_iInf, Submodule.mem_comap]
  intro w B hB
  have hB' : ∀ τ, IsBasisAt w (dualFr (tauLat emb τ M)) (invTrK B τ) := fun τ =>
    GlobalTheory.DualWeylDual.isBasisAt_dualFr w (hA τ) (hB τ)
  have h1 : v.1 ∈ nabP (fun τ => (σ τ).dual) (fun τ => dualFr (tauLat emb τ M)) := hv
  simp only [nabP, transLat, Submodule.mem_iInf, Submodule.mem_comap] at h1
  have h2 := h1 w (invTrK B) hB'
  rw [← map_inv] at h2
  obtain ⟨s, hs, hsv⟩ := (Formalism.L2.DIV.lc_mem_locP w _ _).1 h2
  refine (Formalism.L2.DIV.lc_mem_locP w _ _).2 ⟨s, hs, ?_⟩
  set F := (GlobalTheory.FunObj.funEquiv σ).symm v with hF
  have e2 : GlobalTheory.FunObj.funEquiv σ (s • rhoK σ B⁻¹ F) = s • rhoK (fun τ => (σ τ).dual) (invTrK B⁻¹) v := by
    rw [LinearMapClass.map_smul_of_tower, GlobalTheory.FunObj.funEquiv_rhoK, hF, LinearEquiv.apply_symm_apply]
  have h3 : (s • rhoK σ B⁻¹ F).1 ∈ nabStd K σ := by
    rw [GlobalTheory.FunObj.funEquiv_mem_nabStd, e2]
    exact hsv
  exact h3

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchimedeanBoundBottomPairsNormsGrid
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.IndefR Formalism.IndefR.Links IsDedekindDomain NumberField
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.SqTop GlobalTheory.NormSum Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts

namespace GlobalTheory.ArchGrid

theorem level_pos {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ t0 : ℂ} {Q : ℕ} (P : Pair D cc δ t0 Q) : 0 < Q := by
  rcases Nat.eq_zero_or_pos Q with rfl | h
  · have h1 := P.idx_le
    rw [zero_pow (by positivity)] at h1
    exact absurd (Nat.le_zero.1 h1) P.idx_ne
  · exact h

theorem arch_grid : GlobalTheory.SqTop.GBig fun {D} _ _ {sc} G μ₀ C _ b => ∀ (zA zA' : Fin D.R.m × Fin D.R.m → D.what₂.LL), (∃ δ t0 : ℂ, ∀ ij : Fin D.R.m × Fin D.R.m, ∃ P P' : Pair D ⊤ δ t0 (levQ G.pl), IsBottom G μ₀ ij.1 ij.2 (SqNum.condE G.pl) P P' ∧ D.what₂.embLL (zA ij) = (P.norm : ℂ) ∧ D.what₂.embLL (zA' ij) = (P'.norm : ℂ)) → ArchimedeanHeightBound zA zA' (C * D.R.f * (2 * (bigN D : ℝ)) * (maxWt D sc.cGap : ℝ) * (Real.log b + Real.log ((maxWt D sc.cGap : ℝ) * (2 * (bigN D : ℝ)))) + C * D.R.f * (bigN D : ℝ) ^ 2 * (Real.log b + Real.log ((D.R.f : ℝ) * (2 * (bigN D : ℝ)) * (maxWt D sc.cGap : ℝ))) + C * (bigN D : ℝ) ^ 2 * Real.log (levQ G.pl)) := by
  obtain ⟨C0, -, hA⟩ := GlobalTheory.ArchFree.st.archSt
  refine ⟨0, fun ε CF _ => ⟨C0, 0, fun C hC D large₂ _ _ hR T Lc μ₀ hμ G => ?_⟩⟩
  rintro zA zA' ⟨δ, t0, h⟩
  choose P P' hB hz hz' using h
  haveI := D.tcLL
  obtain ⟨-, -, hf4, hm44, -, -, -, -, -, hrd1, hrd2, -⟩ := hR.size
  have hLpos : 0 < large₂.sc.L := Real.rpow_pos_of_pos (by linarith [large₂.sc.one_lt_alt]) _
  have hL1 : (1 : ℝ) ≤ large₂.sc.L := Real.one_le_rpow large₂.sc.one_lt_alt.le large₂.sc.eps_pos.le
  have hlb : Real.log large₂.sc.b = large₂.sc.L := by unfold Scale.b; exact Real.log_exp _
  have hN : 1 ≤ bigN D := by have := D.R.m_add_three_le_k; unfold bigN; omega
  have hB1 : (1 : ℝ) ≤ (maxWt D 1 : ℝ) := by exact_mod_cast le_max_left _ _
  have hrd : Real.log D.host.rdE ≤ Real.log large₂.sc.b := by rw [hlb]; linarith
  have hdl : |TaylorLogMetric.logDerivativeAtOne D| ≤ Real.log large₂.sc.b := by
    rw [hlb]
    have e : TaylorLogMetric.logDerivativeAtOne D = large₂.logDerivativeAtOne := by rw [large₂.logDerivative_at_one_eq]; rfl
    rw [e]; exact hR.dlog
  intro ij
  have hQ : 0 < levQ G.pl := level_pos (P ij)
  have key := hA D ⊤ δ t0 (levQ G.pl) (P ij).crv (P ij).pt0 hQ D.what₂.LL D.what₂.embLL (Fin D.R.m × Fin D.R.m) (bigN D)
    (maxWt D 1 : ℝ) (Real.log large₂.sc.b) P P' zA zA' hN hB1 (by rw [hlb]; exact hL1) hrd hdl
    (fun k => GlobalTheory.T.squareBottomPairs_small_reference_tuple hμ G δ t0 _ (P k) (P' k) k.1 k.2 _ (hB k)) (fun k => ⟨hz k, hz' k⟩) ij
  have hf : (1 : ℝ) ≤ (D.R.f : ℝ) := by
    have : 1 ≤ D.R.f := le_trans (Nat.one_le_pow _ _ (by omega)) hf4
    exact_mod_cast this
  have hN' : (1 : ℝ) ≤ (bigN D : ℝ) := by exact_mod_cast hN
  have hX : 0 ≤ (D.R.f : ℝ) * (2 * (bigN D : ℝ)) * (maxWt D 1 : ℝ) *
      (Real.log large₂.sc.b + Real.log ((maxWt D 1 : ℝ) * (2 * (bigN D : ℝ)))) +
      (D.R.f : ℝ) * (bigN D : ℝ) ^ 2 * (Real.log large₂.sc.b + Real.log ((D.R.f : ℝ) * (2 * (bigN D : ℝ)) * (maxWt D 1 : ℝ))) +
      (bigN D : ℝ) ^ 2 * Real.log (levQ G.pl : ℝ) := by
    have h1 : 0 ≤ Real.log ((maxWt D 1 : ℝ) * (2 * (bigN D : ℝ))) := Real.log_nonneg (by nlinarith)
    have h2 : 0 ≤ Real.log ((D.R.f : ℝ) * (2 * (bigN D : ℝ)) * (maxWt D 1 : ℝ)) := by
      apply Real.log_nonneg
      have : 1 ≤ (D.R.f : ℝ) * (2 * (bigN D : ℝ)) := by nlinarith
      nlinarith
    have h3 : 0 ≤ Real.log (levQ G.pl : ℝ) := Real.log_natCast_nonneg _
    have hl : 0 ≤ Real.log large₂.sc.b := by rw [hlb]; linarith
    positivity
  have hle : ∀ c : ℝ, c * (D.R.f : ℝ) * (2 * (bigN D : ℝ)) * (maxWt D 1 : ℝ) *
      (Real.log large₂.sc.b + Real.log ((maxWt D 1 : ℝ) * (2 * (bigN D : ℝ)))) +
      c * (D.R.f : ℝ) * (bigN D : ℝ) ^ 2 * (Real.log large₂.sc.b + Real.log ((D.R.f : ℝ) * (2 * (bigN D : ℝ)) * (maxWt D 1 : ℝ))) +
      c * (bigN D : ℝ) ^ 2 * Real.log (levQ G.pl : ℝ) = c * ((D.R.f : ℝ) * (2 * (bigN D : ℝ)) * (maxWt D 1 : ℝ) *
      (Real.log large₂.sc.b + Real.log ((maxWt D 1 : ℝ) * (2 * (bigN D : ℝ)))) +
      (D.R.f : ℝ) * (bigN D : ℝ) ^ 2 * (Real.log large₂.sc.b + Real.log ((D.R.f : ℝ) * (2 * (bigN D : ℝ)) * (maxWt D 1 : ℝ))) +
      (bigN D : ℝ) ^ 2 * Real.log (levQ G.pl : ℝ)) := fun c => by ring
  have hmono := mul_le_mul_of_nonneg_right hC hX
  show _ ∧ _
  constructor
  · refine le_trans key.1 (le_of_eq_of_le ?_ (le_of_le_of_eq hmono ?_))
    · exact (hle C0).symm ▸ rfl
    · exact (hle C).symm
  · refine le_trans key.2 (le_of_eq_of_le ?_ (le_of_le_of_eq hmono ?_))
    · exact (hle C0).symm ▸ rfl
    · exact (hle C).symm

end GlobalTheory.ArchGrid
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsWeilPairingEqCmIntegerOfPureTypeStatement
section
open AlgebraicGeometry CategoryTheory NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory GlobalTheory GlobalTheory.CM GlobalTheory.FlatCM
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_weil_pairing_eq_cm_integer_of_pure_type : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (A B : PAT H (Sp ℂ)) (p q : ℕ), p + q = 1 → (∀ τ : 𝓞 E →+* ℂ, (τ H.rt = H.rt0 → LieMult A.t.act (𝟙 (Sp ℂ)) τ p) ∧ (τ H.rt ≠ H.rt0 → LieMult A.t.act (𝟙 (Sp ℂ)) τ q)) → ∀ (f₁ f₂ : A.t.G ⟶ B.t.G), Serre.IsLinearHom A.t.act B.t.act f₁ → Serre.IsLinearHom A.t.act B.t.act f₂ → ∃ g : 𝓞 E, WeilEq B.t.PP.L f₁ f₂ A.t.PP.L (A.t.act.act g) (𝟙 _) (𝟙 (Sp ℂ)) := by
  first | exact @GlobalTheory.CM.PureHom.exists_weilEq_smul_of_pure | exact GlobalTheory.CM.PureHom.exists_weilEq_smul_of_pure | (intros; apply GlobalTheory.CM.PureHom.exists_weilEq_smul_of_pure <;> assumption)
end

