import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0045
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0014
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMapOfOfExtends
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0042
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0028
import Formalism.LocalToGlobal.IndefiniteReal.FWExist
import Development.AbelianVarietyTheory.Definitions.Divisors.IsDeltaDelAtOwnAt
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0505
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2029
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2020
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2087
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0083
import Formalism.MirabolicMackeyTheory.MirabolicMackeyProofs.Bundle0003
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OscillatorModelValuesThird
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0053
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsPowEqSpan
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SplitPlaceSupportLevelStandardCoordinates
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SupportedSubgroupSplitCommutePrimeIdempotents
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsPrimeIdemOfInert
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2098
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2095
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2079
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1744
import Development.AbelianVarietyTheory.Definitions.Divisors.RankEqCardIffExistsFrameMatrixFirstColumnBlock
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianAdaptedPlaneSeesaw
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2086
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1145
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0056
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.WeightFunctionOnFrames
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.MeanLogSupNormLowerBoundCmFrameNonvanishingStatement
import Development.AbelianVarietyTheory.Definitions.RegularCharts.BaseNorm
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0027
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TamagawaSpecialUnitary
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2094
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0871
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1133
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2096
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2068
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0011
import Formalism.LocalToGlobal.IndefiniteReal.BaseLiftsPackageOfPrimitiveLinks
import Development.AbelianVarietyTheory.Definitions.Divisors.RealisedChainTorusEq

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIntegralAbsNormPowMulOnId
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.Indef Formalism.L2.Indef.Tree
open Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.IndefR.Datum Formalism.IndefR.Lev
open GlobalTheory.FormTies GlobalTheory.OnTies GlobalTheory.TraceClassRank
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.OnCmp GlobalTheory.BigOn GlobalTheory.RealIndexBound
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff)

noncomputable section

namespace GlobalTheory.TameHeckeIntegral

open Formalism.L2.Host GlobalTheory.IndefiniteRowSideFullHecke.CentralInvolutionRing GlobalTheory.ChiUnit

theorem unitOff_onId (E : Type) [Field E] [NumberField E] (ψ : HChar E) (I : Type) [Fintype I] (φs : I → E →+* ℂ)
    (n : I → ℤ) (hinf : ψ.HasInf φs n) (ht : ∀ v, ψ.TameAt v) (b : ℕ) (hb : b ≠ 0)
    (hu : ∀ v : HeightOneSpectrum (𝓞 E), (b : 𝓞 E) ∉ v.asIdeal → ψ.UnrAt v) (cc : Ideal (𝓞 E)) (hcc : cc ≠ ⊥)
    (hcop : cc ⊔ Ideal.span {(b : 𝓞 E)} = ⊤) :
    UnitOff (Ideal.absNorm cc) ((ψ.onId (cc : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) : ℂˣ) : ℂ) := by
  classical
  have hb0 : (b : 𝓞 E) ≠ 0 := Nat.cast_ne_zero.2 hb
  have hfin : {w | ¬ ψ.UnrAt w}.Finite := by
    refine (Ideal.finite_factors (I := Ideal.span {(b : 𝓞 E)}) (by simpa using hb0)).subset fun w hw => ?_
    have hbw : (b : 𝓞 E) ∈ w.asIdeal := by
      by_contra h
      exact hw (hu w h)
    show w.asIdeal ∣ Ideal.span {(b : 𝓞 E)}
    rw [Ideal.dvd_iff_le, Ideal.span_singleton_le_iff_mem]
    exact hbw
  have hcc0 : cc ≠ 0 := hcc
  unfold HChar.onId
  refine finprod_induction (fun u : ℂˣ => UnitOff (Ideal.absNorm cc) (u : ℂ)) (by simpa using unitOff_one _)
    (fun x y hx hy => by simpa [Units.val_mul] using unitOff_mul hx hy) fun v => ?_
  show UnitOff _ (((ψ.val v ^ FractionalIdeal.count E v (cc : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) : ℂˣ)) : ℂ)
  rw [Units.val_zpow_eq_zpow_val]
  by_cases hdv : v.asIdeal ∣ cc
  · have hle : cc ≤ v.asIdeal := Ideal.le_of_dvd hdv
    have hbv : (b : 𝓞 E) ∉ v.asIdeal := fun h => v.isPrime.ne_top (by
      rw [eq_top_iff, ← hcop]
      exact sup_le hle (by rw [Ideal.span_singleton_le_iff_mem]; exact h))
    have hq : ((Ideal.absNorm cc : ℕ) : 𝓞 E) ∈ v.asIdeal := hle (Ideal.absNorm_mem cc)
    exact unitOff_zpow (GlobalTheory.ValUnit.unitOff_val E ψ I φs n v _ hinf hfin ht (hu v hbv) hq) _
  · have h0 : FractionalIdeal.count E v (cc : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) = 0 := by
      rw [FractionalIdeal.count_coe E v hcc0, Nat.cast_eq_zero]
      by_contra h
      exact hdv ((Associates.count_ne_zero_iff_dvd hcc0 (HeightOneSpectrum.prime v).irreducible).1 h)
    rw [h0, zpow_zero]
    exact unitOff_one _

theorem isIntegral_absNorm_pow_mul_onId : ∀ (E : Type) [Field E] [NumberField E] (ψ : Formalism.L2.Host.HChar E) (I : Type) [Fintype I] (φs : I → E →+* ℂ) (n : I → ℤ), ψ.HasInf φs n → (∀ v, ψ.TameAt v) → ∀ b : ℕ, b ≠ 0 → (∀ v : HeightOneSpectrum (𝓞 E), (b : 𝓞 E) ∉ v.asIdeal → ψ.UnrAt v) → ∀ cc : Ideal (𝓞 E), cc ≠ ⊥ → cc ⊔ Ideal.span {(b : 𝓞 E)} = ⊤ → ∃ K : ℕ, IsIntegral ℤ (((Ideal.absNorm cc : ℕ) : ℂ) ^ K * ((ψ.onId (cc : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) : ℂˣ) : ℂ)) := by
  intro E _ _ ψ I _ φs n hinf ht b hb hu cc hcc hcop
  obtain ⟨_, K, hK, _⟩ := unitOff_onId E ψ I φs n hinf ht b hb hu cc hcc hcop
  exact ⟨K, hK⟩

end GlobalTheory.TameHeckeIntegral
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLocalAtPlaceConjProduct
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.L2.Pj GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.ExpFrame GlobalTheory.ExpTie GlobalTheory.FrameOf
open scoped TensorProduct
open Formalism.IndefR.Mult Formalism.L2.Theta
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FrameProdLoc

theorem mem_locGrp_of_isLocEnv {D : D7} (V : Formalism.BasicNotions.TH.HSp D) {Pl0 : Type} (pl : Pl0 → Pl D.host.E) (ok : Set Pl0)
    (i : ok × ℕ) (x : Bridge.Gf V) (h : isLocEnv V pl ok i x) :
    x ∈ GlobalTheory.HeckeRowsCompare.locGrp V ((pl i.1).under (𝓞 D.host.F)) := by
  rw [GlobalTheory.HeckeRowsCompare.mem_locGrp]
  exact GlobalTheory.Mem.R3.LiftInertChi.locAt_of_isLocElt V _ x ((GlobalTheory.Hk3Split.isLabElt_of_isTEnv V pl ok i x).2.1 h)

theorem isLocEnv_of_mem {D : D7} (V : Formalism.BasicNotions.TH.HSp D) {Pl0 : Type} (pl : Pl0 → Pl D.host.E) (ok : Set Pl0)
    (i : ok × ℕ) (x : Bridge.Gf V) (e : Formalism.L2.Theta.AE D) (he : Formalism.L2.NTheta.IsIdemAt e (pl i.1))
    (h : x ∈ GlobalTheory.HeckeRowsCompare.locGrp V ((pl i.1).under (𝓞 D.host.F))) : isLocEnv V pl ok i x := by
  obtain ⟨α, hα, hfin⟩ := GlobalTheory.HeckeRowsCompare.fin_lift V x
  have hI : IsPrimeIdem (pl i.1) e (e + cA D e) := Or.inl ⟨he, rfl⟩
  obtain ⟨Φ, hΦ⟩ := GlobalTheory.IdemSupport.exists_comp D
  obtain ⟨-, ε, hε, hf⟩ := GlobalTheory.IdemSupport.of_isPrimeIdem hΦ hI
  refine ⟨e, α, he, hα, ?_, ?_⟩
  · show SuppF V (e + cA D e) α
    rw [hf, GlobalTheory.HeckeRowsCompare.suppF_iff V hε hα, hfin]
    exact h
  · rw [← hfin]
    rfl

theorem isLocEnv_prod : ∀ {D : D7} (V : Formalism.BasicNotions.TH.HSp D) {Pl0 : Type} (pl : Pl0 → Pl D.host.E) (ok : Set Pl0)
    (i i' : ok × ℕ) (a b c d : Bridge.Gf V), (pl i.1).under (𝓞 D.host.F) = (pl i'.1).under (𝓞 D.host.F) →
    isLocEnv V pl ok i a → isLocEnv V pl ok i' b → isLocEnv V pl ok i' c → isLocEnv V pl ok i d →
    isLocEnv V pl ok i ((c * d)⁻¹ * (a * b)) := by
  intro D V Pl0 pl ok i i' a b c d hv ha hb hc hd
  obtain ⟨e, -, he, -⟩ := id ha
  apply isLocEnv_of_mem V pl ok i _ e he
  have ha' := mem_locGrp_of_isLocEnv V pl ok i a ha
  have hd' := mem_locGrp_of_isLocEnv V pl ok i d hd
  have hb' := mem_locGrp_of_isLocEnv V pl ok i' b hb
  have hc' := mem_locGrp_of_isLocEnv V pl ok i' c hc
  rw [← hv] at hb' hc'
  exact Subgroup.mul_mem _ (Subgroup.inv_mem _ (Subgroup.mul_mem _ hc' hd')) (Subgroup.mul_mem _ ha' hb')

end GlobalTheory.FrameProdLoc
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTransp
section
set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain Module ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.IndefiniteRowSideFullHecke.FrameWeightGapBounds
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.CovTop Formalism.L2.Pj GlobalTheory.FormTies GlobalTheory.Shares
open ReciprocityTheory.ChartRestriction.G.PullbackSections.PfModelLatA GlobalTheory.ShareOn

namespace GlobalTheory.ShareOn

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ}

def mvLev {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    {Dw : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum H} {l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H} (Xo : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Moduli Dw l)
    (c : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff l) (γ : LaMod Dw l ≃ₗ[𝓞 E] LaMod Dw l)
    {S : Type} [CommRing S] [Algebra c.F S] (y : FrPt Xo c S) : FrPt Xo c S :=
  mvPt (K := c.F) (fun S _ _ => FrPt Xo c S)
    (fun {S : Type} [CommRing S] [Algebra c.F S] (g' : LaMod Dw l ≃ₗ[𝓞 E] LaMod Dw l) (y y' : FrPt Xo c S) =>
      levActR (Xo := Xo) (c := c) (levFull Dw l) g' y y') γ y

abbrev latQ (p : PtAt ex Csz) (r : TwoRuns p.T p.P.Gp) (i : Fin D.R.m) (v : HeightOneSpectrum (𝓞 D.what₂.LL))
    (k : (uAt r v i).Comp) : Type :=
  lattice₂ D ((uAt r v i).X k).Λ ⧸ (p.T.Q.l.Mb • (⊤ : Submodule (𝓞 D.host.E) (lattice₂ D ((uAt r v i).X k).Λ)))

def IsTransp (p : PtAt ex Csz) (r : TwoRuns p.T p.P.Gp) (i : Fin D.R.m) (v : HeightOneSpectrum (𝓞 D.what₂.LL))
    (ψ : ∀ k : (uAt r v i).Comp, LaMod (p.T.Q.Dw ((i : ℕ) + 1)) p.T.Q.l ≃ₗ[𝓞 D.host.E] latQ p r i v k)
    (γ : LaMod (p.T.Q.Dw ((i : ℕ) + 1)) p.T.Q.l ≃ₗ[𝓞 D.host.E] LaMod (p.T.Q.Dw ((i : ℕ) + 1)) p.T.Q.l)
    (k k' : (uAt r v i).Comp) (a : GL (Fin D.R.r) D.host.E) : Prop :=
  ∃ hm : GlobalTheory.LevelCusp.IsMatch ((uAt r v i).X k) ((uAt r v i).X k') a,
    (∀ (x : Frame ((uAt r v i).X k).Ψ D.R.r) (hx : x ∈ ((uAt r v i).X k).dom),
      ∃ (hy : castFrame hm.psi (lact a x) ∈ ((uAt r v i).X k').dom) (t : _),
        FrBor t ((uAt r v i).un k' ⟨castFrame hm.psi (lact a x), hy⟩) (mvLev ((r.used v).full.Q.Xo ((i : ℕ) + 1)) (r.used v).full.Q.c γ ((uAt r v i).un k ⟨x, hx⟩))) ∧
    ∀ w : lattice₂ D ((uAt r v i).X k).Λ,
      ∃ hw : Matrix.mulVec (a : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E) (w : Fin D.R.r → D.host.E) ∈
          lattice₂ D ((uAt r v i).X k').Λ,
        Submodule.Quotient.mk (p := p.T.Q.l.Mb • (⊤ : Submodule (𝓞 D.host.E) (lattice₂ D ((uAt r v i).X k').Λ))) ⟨_, hw⟩ =
          ψ k' (γ.symm ((ψ k).symm (Submodule.Quotient.mk w)))

theorem IsTransp.eq_of_eq {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D}
    {Kc : Formalism.MainNotions.G.Consts} {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ} {p : PtAt ex Csz}
    {r : TwoRuns p.T p.P.Gp} {i : Fin D.R.m} {v : HeightOneSpectrum (𝓞 D.what₂.LL)}
    {ψ : ∀ k : (uAt r v i).Comp, LaMod (p.T.Q.Dw ((i : ℕ) + 1)) p.T.Q.l ≃ₗ[𝓞 D.host.E] latQ p r i v k}
    {γ γ' : LaMod (p.T.Q.Dw ((i : ℕ) + 1)) p.T.Q.l ≃ₗ[𝓞 D.host.E] LaMod (p.T.Q.Dw ((i : ℕ) + 1)) p.T.Q.l}
    {k k' : (uAt r v i).Comp} {a : GL (Fin D.R.r) D.host.E}
    (h₁ : IsTransp p r i v ψ γ k k' a) (h₂ : IsTransp p r i v ψ γ' k k' a) : γ = γ' := by
  obtain ⟨-, -, m₁⟩ := h₁
  obtain ⟨-, -, m₂⟩ := h₂
  have hs : γ.symm = γ'.symm := by
    ext u
    obtain ⟨w, hw⟩ := Submodule.Quotient.mk_surjective _ (ψ k u)
    obtain ⟨hw₁, e₁⟩ := m₁ w
    obtain ⟨hw₂, e₂⟩ := m₂ w
    have := e₁.symm.trans e₂
    simp only [hw, LinearEquiv.symm_apply_apply] at this
    exact (ψ k').injective this
  have := congrArg LinearEquiv.symm hs
  simpa using this

end GlobalTheory.ShareOn

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsUnitAwayFromLevelProdNormalisedMatrixGaussSumStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR
open Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.ConjTwist GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.OnTies GlobalTheory.OnCmp GlobalTheory.BaseCmp
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Classical
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isUnitAwayFromLevel_prod_normalised_matrixGaussSum : ∀ (D : D7) [∀ PP : Pl D.host.E, Fintype (kP PP)] (Q : Finset (Pl D.host.E)) (n r : ℕ), r ≤ n → ∀ (ψP : ∀ PP : Pl D.host.E, AddChar (kP PP) ℂ) (ξ : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ), (∀ PP ∈ Q, (ψP PP).IsPrimitive) → (∀ PP ∈ Q, ξ PP ≠ 1) → ∀ N : ℕ, N ≠ 0 → (∀ PP ∈ Q, (N : 𝓞 D.host.E) ∈ PP.asIdeal) → UnitOff N (∏ PP ∈ Q.attach, ((Nat.card (kP PP.1) : ℂ) ^ (n * r))⁻¹ * ∑ g : GL (Fin r) (kP PP.1), (((ξ PP.1 (Matrix.GeneralLinearGroup.det g))⁻¹ : ℂˣ) : ℂ) * ψP PP.1 (Matrix.trace (g : Matrix (Fin r) (Fin r) (kP PP.1)))) := by
  first | exact @GlobalTheory.GaussUnit.unitOff_prod_gaussSum | exact GlobalTheory.GaussUnit.unitOff_prod_gaussSum | (intros; apply GlobalTheory.GaussUnit.unitOff_prod_gaussSum <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsotropicIntegralInvariantHeisenbergFirstVarsStatement
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels MeasureTheory GlobalTheory.LatVac GlobalTheory.InertVacLag GlobalTheory.InertLagChar
open scoped TensorProduct Matrix GlobalTheory.VacAny
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isotropicIntegral_invariant_heisenberg_first_vars : ∀ (F : Type) [Field F] [NumberField F] (v : Pl F) (κ : Type) [Fintype κ] (ψ : AddChar (Fv F v) ℂ) (μ : @Measure (κ → Fv F v) (borel _)), @Measure.IsAddHaarMeasure _ _ _ (borel _) μ →
    ∀ (N : ℕ) (ν : @Measure (Fin N → Fv F v) (borel _)), @Measure.IsAddHaarMeasure _ _ _ (borel _) ν →
    ∀ j : (Fin N → Fv F v) →ₗ[Fv F v] (κ → Fv F v) × (κ → Fv F v), (∀ y y', (j y).1 ⬝ᵥ (j y').2 = (j y').1 ⬝ᵥ (j y).2) →
    ∀ (y₀ : Fin N → Fv F v) (φ₁ φ₂ : (κ → Fv F v) → ℂ),
      lagInt ψ μ ν j (boxFun (schr ψ (j y₀) φ₁) φ₂) = lagInt ψ μ ν j (boxFun φ₁ φ₂) := by
  first | exact @GlobalTheory.LagIntTransl.main | exact GlobalTheory.LagIntTransl.main | (intros; apply GlobalTheory.LagIntTransl.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.JointRowWeightAntitoneOfMaxPotential
section
set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Pj GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.ExpTie GlobalTheory.ExpFrame Formalism.CohomologicalDescent.DepthNonnegative Formalism.CohomologicalDescent.LogSmallConstantBounds Formalism.CohomologicalDescent.ShortWeightBounds Formalism.CohomologicalDescent.LD Formalism.RankGapBounds.FormsTensorLocalization
open MvPolynomial

namespace GlobalTheory.HighWt

def permMat {O : Type} [CommRing O] {N : ℕ} (σ : Equiv.Perm (Fin N)) : Matrix (Fin N) (Fin N) O :=
  Matrix.of fun i j => if σ i = j then 1 else 0

theorem permMat_mul {O : Type} [CommRing O] {N : ℕ} (σ ρ : Equiv.Perm (Fin N)) :
    (permMat σ : Matrix (Fin N) (Fin N) O) * permMat ρ = permMat (σ.trans ρ) := by
  ext i k
  simp only [permMat, Matrix.mul_apply, Matrix.of_apply, Equiv.trans_apply]
  rw [Finset.sum_eq_single (σ i)]
  · by_cases h : ρ (σ i) = k <;> simp [h]
  · intro j _ hj
    simp [Ne.symm hj]
  · simp

theorem permMat_refl {O : Type} [CommRing O] {N : ℕ} :
    (permMat (Equiv.refl (Fin N)) : Matrix (Fin N) (Fin N) O) = 1 := by
  ext i k
  by_cases h : i = k <;> simp [permMat, Matrix.one_apply, h]

def permGL {O : Type} [CommRing O] {N : ℕ} (σ : Equiv.Perm (Fin N)) : GL (Fin N) O :=
  ⟨permMat σ, permMat σ.symm, by rw [permMat_mul, Equiv.self_trans_symm, permMat_refl],
    by rw [permMat_mul, Equiv.symm_trans_self, permMat_refl]⟩

theorem rowAct_permMat {O : Type} [CommRing O] {N : ℕ} (σ : Equiv.Perm (Fin N)) (f : MvPolynomial (Fin N × Fin N) O) :
    Formalism.GradedWeylDivisibility.rowAct O (n := N) (permMat σ) f = rename (fun v : Fin N × Fin N => (σ v.1, v.2)) f := by
  have : Formalism.GradedWeylDivisibility.rowAct O (n := N) (permMat σ) = rename (fun v : Fin N × Fin N => (σ v.1, v.2)) := by
    apply MvPolynomial.algHom_ext
    intro v
    simp [Formalism.GradedWeylDivisibility.rowAct, permMat, rename_X]
  rw [this]

theorem weight_mapDomain_perm {N : ℕ} (σ : Equiv.Perm (Fin N)) (d : Fin N × Fin N →₀ ℕ) (a : Fin N) :
    Finsupp.weight (Formalism.GradedWeylDivisibility.rowW N N) (d.mapDomain (fun v : Fin N × Fin N => (σ v.1, v.2))) (σ a) =
      Finsupp.weight (Formalism.GradedWeylDivisibility.rowW N N) d a := by
  induction d using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg => rw [Finsupp.mapDomain_add, map_add, map_add, Pi.add_apply, Pi.add_apply, hf, hg]
  | single v c =>
    rw [Finsupp.mapDomain_single, Finsupp.weight_single, Finsupp.weight_single]
    simp only [Pi.smul_apply, Formalism.GradedWeylDivisibility.rowW, Pi.single_apply, σ.injective.eq_iff]

end GlobalTheory.HighWt

namespace GlobalTheory.HighWt

theorem rowComp_rename_perm {O : Type} [CommRing O] {N : ℕ} (σ : Equiv.Perm (Fin N)) (u : Fin N → ℕ)
    (f : MvPolynomial (Fin N × Fin N) O) :
    weightedHomogeneousComponent (Formalism.GradedWeylDivisibility.rowW N N) u (rename (fun v : Fin N × Fin N => (σ v.1, v.2)) f) =
      rename (fun v : Fin N × Fin N => (σ v.1, v.2)) (weightedHomogeneousComponent (Formalism.GradedWeylDivisibility.rowW N N) (u ∘ σ) f) := by
  classical
  induction f using MvPolynomial.induction_on' with
  | monomial d c =>
    rw [rename_monomial]
    have key : Finsupp.weight (Formalism.GradedWeylDivisibility.rowW N N) (d.mapDomain (fun v : Fin N × Fin N => (σ v.1, v.2))) = u ↔
        Finsupp.weight (Formalism.GradedWeylDivisibility.rowW N N) d = u ∘ σ := by
      constructor
      · intro h
        funext a
        rw [Function.comp_apply, ← h, weight_mapDomain_perm]
      · intro h
        funext b
        obtain ⟨a, rfl⟩ := σ.surjective b
        rw [weight_mapDomain_perm, h, Function.comp_apply]
    rw [weightedHomogeneousComponent_of_mem (isWeightedHomogeneous_monomial _ _ _ rfl),
      weightedHomogeneousComponent_of_mem (isWeightedHomogeneous_monomial _ _ _ rfl)]
    by_cases h : Finsupp.weight (Formalism.GradedWeylDivisibility.rowW N N) d = u ∘ σ
    · rw [if_pos (Eq.symm (key.2 h)), if_pos h.symm, rename_monomial]
    · rw [if_neg (fun h' => h (key.1 h'.symm)), if_neg (fun h' => h h'.symm), map_zero]
  | add p q hp hq => rw [map_add, map_add, hp, hq, map_add, map_add]

variable (O : Type) [CommRing O] (N : ℕ) {ι : Type} [DecidableEq ι] (lam : ι → ℕ → ℕ)

theorem grp_tprod (g : ι → GL (Fin N) O) (x : ∀ τ, Formalism.GradedWeylDivisibility.dualWeyl O N N (res N (lam τ))) :
    grp O N lam g (PiTensorProduct.tprod O x) =
      PiTensorProduct.tprod O (fun τ => Formalism.UG.dualWeylRep O N N (res N (lam τ)) (g τ) (x τ)) := by
  simp only [grp, Formalism.CohomologicalDescent.RealLocalDeltaNabla.nablaRep, MonoidHom.coe_comp, Function.comp_apply]
  rw [PiTensorProduct.mapMonoidHom_apply, PiTensorProduct.map_tprod]
  rfl

theorem grp_inv_mul (g : ι → GL (Fin N) O) : grp O N lam g⁻¹ * grp O N lam g = 1 := by
  simp only [grp]
  rw [← map_mul, inv_mul_cancel, map_one]

theorem dualWeylRep_mul_inv (ν : Fin N → ℕ) (h : GL (Fin N) O) (v : Formalism.GradedWeylDivisibility.dualWeyl O N N ν) :
    Formalism.UG.dualWeylRep O N N ν h (Formalism.UG.dualWeylRep O N N ν h⁻¹ v) = v := by
  rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]

theorem isProj_conj (g : ι → GL (Fin N) O) (τ' : ι) (u u' : Fin N → ℕ)
    (h : ∀ f, weightedHomogeneousComponent (Formalism.GradedWeylDivisibility.rowW N N) u (Formalism.UG.dwAct O N N (g τ')⁻¹ f) =
      Formalism.UG.dwAct O N N (g τ')⁻¹ (weightedHomogeneousComponent (Formalism.GradedWeylDivisibility.rowW N N) u' f))
    (b : Module.End O (NablaT O N lam)) (hb : IsProj O N lam τ' u b) :
    IsProj O N lam τ' u' (grp O N lam g * b * grp O N lam g⁻¹) := by
  intro x y hy
  set x'' : ∀ τ, Formalism.GradedWeylDivisibility.dualWeyl O N N (res N (lam τ)) := fun τ => Formalism.UG.dualWeylRep O N N (res N (lam τ)) (g τ)⁻¹ (x τ) with hx''
  have h1 : grp O N lam g⁻¹ (PiTensorProduct.tprod O x) = PiTensorProduct.tprod O x'' := by
    rw [grp_tprod]; rfl
  have hy'' : ((Formalism.UG.dualWeylRep O N N (res N (lam τ')) (g τ')⁻¹ y : Formalism.GradedWeylDivisibility.dualWeyl O N N (res N (lam τ'))) :
      MvPolynomial (Fin N × Fin N) O) = weightedHomogeneousComponent (Formalism.GradedWeylDivisibility.rowW N N) u (x'' τ' : MvPolynomial (Fin N × Fin N) O) := by
    rw [Formalism.UG.dualWeylRep_apply, hy, ← h, hx'', Formalism.UG.dualWeylRep_apply]
  have h2 := hb x'' _ hy''
  rw [Module.End.mul_apply, Module.End.mul_apply, h1, h2, grp_tprod]
  congr 1
  funext i
  by_cases hi : i = τ'
  · subst hi
    rw [Function.update_self, Function.update_self, dualWeylRep_mul_inv]
  · rw [Function.update_of_ne hi, Function.update_of_ne hi, hx'', dualWeylRep_mul_inv]

end GlobalTheory.HighWt

namespace GlobalTheory.HighWt

theorem grpA_inv_mul (O : Type) [CommRing O] (N : ℕ) {ι : Type} [DecidableEq ι] (lam : ι → ℕ → ℕ) (g : ι → GL (Fin N) O) :
    grpA O N lam g⁻¹ * grpA O N lam g = 1 :=
  Subtype.ext (grp_inv_mul O N lam g)

theorem jointWt_perm (O : Type) [CommRing O] (N : ℕ) {ι : Type} [Fintype ι] [DecidableEq ι] (lam : ι → ℕ → ℕ)
    (Gm : Type) [AddCommGroup Gm] [Module (alg O N lam) Gm] (w : ι → Fin N → ℕ) (hw : JointWt O N lam Gm w)
    (τ : ι) (σ : Equiv.Perm (Fin N)) : JointWt O N lam Gm (Function.update w τ (w τ ∘ σ)) := by
  obtain ⟨z, hz0, hz⟩ := hw
  set g : ι → GL (Fin N) O := Pi.mulSingle τ (permGL σ) with hg
  refine ⟨grpA O N lam g • z, ?_, ?_⟩
  · intro h0
    apply hz0
    have := congrArg (fun t => grpA O N lam g⁻¹ • t) h0
    simp only [smul_smul, grpA_inv_mul, one_smul, smul_zero] at this
    exact this
  · intro τ' a ha
    obtain ⟨b0, hb0, -⟩ := GlobalTheory.ExpFrame.exists_unique_isProj O N ι lam τ' (w τ')
    obtain ⟨c, -, huniq⟩ := GlobalTheory.ExpFrame.exists_unique_isProj O N ι lam τ' (Function.update w τ (w τ ∘ σ) τ')
    have hconj : IsProj O N lam τ' (Function.update w τ (w τ ∘ σ) τ') (grp O N lam g * b0 * grp O N lam g⁻¹) := by
      apply isProj_conj O N lam g τ' (w τ') _ _ b0 hb0
      intro f
      by_cases hτ : τ' = τ
      · subst hτ
        have hgt : g τ' = permGL σ := by rw [hg, Pi.mulSingle_eq_same]
        rw [hgt, Function.update_self]
        simp only [Formalism.UG.dwAct, inv_inv]
        show weightedHomogeneousComponent (Formalism.GradedWeylDivisibility.rowW N N) (w τ') (Formalism.GradedWeylDivisibility.rowAct O (n := N) (permMat σ) f) =
          Formalism.GradedWeylDivisibility.rowAct O (n := N) (permMat σ) (weightedHomogeneousComponent (Formalism.GradedWeylDivisibility.rowW N N) (w τ' ∘ σ) f)
        rw [rowAct_permMat, rowAct_permMat, rowComp_rename_perm]
      · have hgt : g τ' = 1 := by rw [hg, Pi.mulSingle_eq_of_ne hτ]
        rw [hgt, Function.update_of_ne hτ, inv_one, (Formalism.UG.P.dual_weyl_action_mul O N N 1 1).2]
        rfl
    have haeq : (a : Module.End O (NablaT O N lam)) = grp O N lam g * b0 * grp O N lam g⁻¹ :=
      (huniq _ ha).trans (huniq _ hconj).symm
    set b : alg O N lam := ⟨b0, Algebra.subset_adjoin (Or.inr ⟨τ', w τ', hb0⟩)⟩ with hbdef
    have haeq' : a = grpA O N lam g * b * grpA O N lam g⁻¹ := Subtype.ext haeq
    rw [haeq', smul_smul, mul_assoc, grpA_inv_mul, mul_one, mul_smul, hz τ' b hb0]

theorem sum_lt_swap {N : ℕ} (v : Fin N → ℕ) (a b : Fin N) (hab : (b : ℕ) = a + 1) (h : v a < v b) :
    ∑ c : Fin N, (N - (c : ℕ)) * v c < ∑ c : Fin N, (N - (c : ℕ)) * (v ∘ Equiv.swap a b) c := by
  classical
  have hne : a ≠ b := fun e => by rw [e] at hab; omega
  rw [← Finset.sum_add_sum_compl {a, b}, ← Finset.sum_add_sum_compl {a, b} (fun c : Fin N => (N - (c : ℕ)) * (v ∘ Equiv.swap a b) c)]
  have hrest : ∑ c ∈ ({a, b} : Finset (Fin N))ᶜ, (N - (c : ℕ)) * v c =
      ∑ c ∈ ({a, b} : Finset (Fin N))ᶜ, (N - (c : ℕ)) * (v ∘ Equiv.swap a b) c := by
    apply Finset.sum_congr rfl
    intro c hc
    simp only [Finset.mem_compl, Finset.mem_insert, Finset.mem_singleton, not_or] at hc
    rw [Function.comp_apply, Equiv.swap_apply_of_ne_of_ne hc.1 hc.2]
  rw [hrest, Finset.sum_pair hne, Finset.sum_pair hne]
  simp only [Function.comp_apply, Equiv.swap_apply_left, Equiv.swap_apply_right]
  have hb : (b : ℕ) < N := b.isLt
  have hk : N - (a : ℕ) = (N - (b : ℕ)) + 1 := by omega
  rw [hk]
  have : (N - (b : ℕ) + 1) * v a + (N - b) * v b < (N - (b : ℕ) + 1) * v b + (N - b) * v a := by nlinarith
  omega

theorem pot_lt_swap {N : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι] (w : ι → Fin N → ℕ) (τ : ι) (a b : Fin N)
    (hab : (b : ℕ) = a + 1) (h : w τ a < w τ b) : pot N w < pot N (Function.update w τ (w τ ∘ Equiv.swap a b)) := by
  unfold pot
  apply Finset.sum_lt_sum
  · intro i _
    by_cases hi : i = τ
    · subst hi
      rw [Function.update_self]
      exact (sum_lt_swap _ a b hab h).le
    · rw [Function.update_of_ne hi]
  · exact ⟨τ, Finset.mem_univ _, by rw [Function.update_self]; exact sum_lt_swap _ a b hab h⟩

theorem antitone_of_adj {N : ℕ} (v : Fin N → ℕ) (h : ∀ a b : Fin N, (b : ℕ) = a + 1 → v b ≤ v a) : Antitone v := by
  cases N with
  | zero => intro a; exact a.elim0
  | succ n => exact Fin.antitone_iff_succ_le.2 fun i => h i.castSucc i.succ (by simp)

theorem antitone_of_pot_max : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O] (N : ℕ) (ι : Type) [Fintype ι]
    [DecidableEq ι] (lam : ι → ℕ → ℕ) (Gm : Type) [AddCommGroup Gm] [Module (alg O N lam) Gm] (w : ι → Fin N → ℕ),
    GlobalTheory.HighWt.JointWt O N lam Gm w → (∀ w' : ι → Fin N → ℕ, GlobalTheory.HighWt.JointWt O N lam Gm w' → GlobalTheory.HighWt.pot N w' ≤ GlobalTheory.HighWt.pot N w) →
    ∀ τ, Antitone (w τ) := by
  intro O _ _ _ _ N ι _ _ lam Gm _ _ w hw hmax τ
  apply antitone_of_adj
  intro a b hab
  by_contra hlt
  push_neg at hlt
  have h1 := hmax _ (jointWt_perm O N lam Gm w hw τ (Equiv.swap a b))
  have h2 := pot_lt_swap w τ a b hab hlt
  omega

end GlobalTheory.HighWt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KroneckerCharacterFrameThird
section
open NumberField MeasureTheory Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.L2.Theta Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.AllWt GlobalTheory.LevGeo
open scoped ENNReal

namespace GlobalTheory

theorem mumaxTop : GlobalTheory.Published.TamagawaSpecialUnitary → ∀ (D : D7) (j : ℕ) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ D.R.r) (dict : ∀ σ : c.F →+* ℂ, GA D (D.sp.W j) → Σ k, Frame ((U σ).X k).Ψ D.R.r), Laws D j Xo c U dict → ∀ [NeZero H.d] (χ : DirichletCharacter ℂ H.d), GlobalTheory.IsKroneckerChar χ → ∀ (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ), Dom a n → GoodW U (xiR D) (fun _ => D.sp.W j) dict (wtZ a n) → latW U (wtZ a n) ≠ ⊥ → slopeMax_sq (normW U (xiR D) (fun _ => D.sp.W j) dict (wtZ a n)) (latW U (wtZ a n)) ≤ 2 * lamSup D.host.E D.R.r Dw.q D.host.d l.M (GlobalTheory.CM.logOm D.host.E χ).re ((absA Dw a : ℕ) : ℝ) ((fdeg D.host.E * D.R.r * n : ℕ) : ℝ) + 2 * Real.log (supConst D.host.E D.R.r D.host.d l.M (((absA Dw a : ℕ) : ℝ) + ((fdeg D.host.E * D.R.r * n : ℕ) : ℝ) + 1)) + Real.log |(discr c.F : ℝ)| / (Module.finrank ℚ c.F : ℝ) := fun hT =>
  GlobalTheory.T.kronecker_character_frame_second (GlobalTheory.T.mass_bound_of_tamagawa_unitary hT) GlobalTheory.T.normOneTorusClassNumberBound_proof

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LambdaPrimeAllPointsStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.ExpTie
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lambda_prime_all_points : GlobalTheory.BigOn.AtPts fun Fm x _ i _ => ∀ (j : Fin (Fm.D x i).R.m) τ, Formalism.IndefR.Bridge.IsLamPrime (D := Fm.D x i) (Formalism.IndefR.Bridge.lamLdef (D := Fm.D x i) (Formalism.IndefR.Links.Vc (Fm.D x i) j).rank ((j : ℕ) + 1) τ) ((j : ℕ) + 1) τ := by
  first | exact @GlobalTheory.LiftWeightForced.atPts | exact GlobalTheory.LiftWeightForced.atPts | (intros; apply GlobalTheory.LiftWeightForced.atPts <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelCharacterFiniteOrderDefiniteFormsStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.levelCharacter_finiteOrder_definite_forms : GlobalTheory.BaseCmp.LevLamRoot := by
  first | exact @GlobalTheory.BaseCmp.levLamRoot | exact GlobalTheory.BaseCmp.levLamRoot | (intros; apply GlobalTheory.BaseCmp.levLamRoot <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelMoveStabiliserCharacterDetStatement
section
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.levelMove_stabiliser_character_det : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec) (O : ∀ i, OMDat T.toCore R i Unit (fun _ => A.μ0)), R.toLevCh.Is A.μ0 → TieIn T R κ v₀ → T.pb = R.C.P.pb → (∀ i, OMPins T R κ v₀ O i) → ∀ (i : Fin D.R.m) (σ : T.Q.c.F →+* ℂ), GoodEmb T.Q.c σ → ∀ hV : T.V ((i : ℕ) + 1) σ = Wc D i, ∀ g k, Lev.IsLevelLift (Wc D i) (R.βW i) (R.datWp i R.triv) (R.eG g) k → ∀ y : T.Q.c.F, D.what₂.embLL (algebraMap T.Q.c.F D.what₂.LL y) = ((chiC R i g : ℂˣ) : ℂ) → ∀ h, (castDict hV (T.dict ((i : ℕ) + 1) σ) (h * k)).1 = (castDict hV (T.dict ((i : ℕ) + 1) σ) h).1 → ∀ f ∈ T.cuspA ((i : ℕ) + 1) (wtA (κ i)) (κ i).n, phiAt T i σ hV (fun _ => 1) (actLev T.Q.c (O i).lev2 g f) h = σ y * phiAt T i σ hV (fun _ => 1) f (h * k) := by
  first | exact @GlobalTheory.StabMove.phiAt_actLev_of_comp_eq | exact GlobalTheory.StabMove.phiAt_actLev_of_comp_eq | (intros; apply GlobalTheory.StabMove.phiAt_actLev_of_comp_eq <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftEigenvalueLowerBoundOfWeakCharacterisationStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.AdelicScalar GlobalTheory.LiftRows GlobalTheory.LowRow
open Formalism.IndefR.Cx GlobalTheory.BigOn
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.liftEigenvalueLowerBound_of_weakCharacterisation : ConjRatLift5 → ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T0 : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T0 D.R.m} (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat3 D A3 T.Q.c.F) (F : Face3 D A3) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.toRealDat.MW i σ).Vec) (O : ∀ i, OMDat T.toCore R.toRealDat i Unit (fun _ => A3.A.μ0)) (s : ℕ) (b C CH : ℝ), A3.fam3.Ok3 s → A3.fam3.TypesSep3 → R.WeakCharacterisation F → R.toRealDat.ExAt → PrimRows3 R F → (∀ i, R.phs i = 1) → IsStdChar D R.ψ (-1) → ∀ fw : FWTie T R.toRealDat κ v₀, BarTie fw → IoExt R.toRealDat → (∀ i, OMPins T R.toRealDat κ v₀ O i) → (∀ i, OneMapRow0 T R.toRealDat κ v₀ O i) → (∀ i, R.toRealDat.LUnif → PhaseTie T R.toRealDat κ v₀ O (fun i => cj (twAt D.what₂.embLL A3.A.v0) (R.phs i)) i) → (∀ j, Sizes D j b) → (∀ j, (F.Zsc (R.toCx3 F).zs).l6m j ≤ lowB D j b) → (∀ j, (R.num F C CH).l6 j ≤ (F.Zsc (R.toCx3 F).zs).l6m j) → AdelC R.toRealDat F.lv2 → PrimeToHost R.toRealDat A3.A.μ0 → ((R.toCx3 F).data F.cr true).L6 (R.num F C CH) := by
  first | exact @GlobalTheory.LowRow.lamLow_of_weak | exact GlobalTheory.LowRow.lamLow_of_weak | (intros; apply GlobalTheory.LowRow.lamLow_of_weak <;> assumption)
end

