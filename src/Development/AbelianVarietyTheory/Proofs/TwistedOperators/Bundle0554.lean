import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0513
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0019
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FiniteDimensionalModel
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DiscreteSeriesModelOfDualParameter
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0138
import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsAllTiedNotStable
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0216
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqZeroOfInnerSmooth
import Development.AbelianVarietyTheory.Definitions.Divisors.LeastSplitAuxiliaryPrimeThetaChainSpec
import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.Bundle0007
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0217
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaGrowthOfThetaSquareIntegrable
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0008
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CuspAlongOfPairLifts
import Development.AbelianVarietyTheory.Proofs.HeightProofs.TypeAtOfDiscreteSeries
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0010
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.SqNormIntegralFundamentalDomainEqL2NormSq
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContDiffDerivSnoc
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0523
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0404
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0027
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0214
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0005
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0304
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NormDwLeSobNorm
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0542
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.TwistPlacesOffPrimeQZero
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0533
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0004
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0006
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ToricSymbols
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0030
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0240
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0020
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0238
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0006
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LintegralNormSqEqToL2
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0421
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.HermitianOrthogonalExtensionData
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0141
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0080
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0510
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0528
import Formalism.LocalToGlobal.GlobalTheory.GL5.FamilyMassVolumeIdentityOfClassDecomp
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemClosureUnitary
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0521
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0547

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.CuspidalListedTopForms
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.EndCusp

open Formalism.IndefR.Mult Matrix

variable {D : D7}

theorem isTypeAt_of_finSum (θ : InfFam D) (V : HSp D) (τ : D.what₂.Tau) {S : SPar}
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {σ : Matrix (Fin V.rank) (Fin V.rank) ℂ → (H →L[ℂ] H)} {lam : Fin V.rank → ℝ} {ε : Fin V.rank → Bool}
    {P : Matrix (Fin V.rank) (Fin V.rank) ℂ}
    (hE : IsEnum S lam ε) (hD : Formalism.MainNotions.S.IsDS ε lam σ) (hP : IsUnit P) (hJ : Pᴴ * Formalism.REAL.Jm ε * P = gramAt D V τ)
    (φ : GA D V → ℂ)
    (h : ∀ x, ∃ (n : ℕ) (L : Fin n → (H →L[ℂ] ℂ)) (v : Fin n → H),
      (∀ i, SmoothVec (lieAt V τ) (fun g => σ (P * g * P⁻¹)) (v i)) ∧
      ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ), φ (x * atTau θ V τ g) = ∑ i, L i (σ (P * g * P⁻¹) (v i))) :
    IsTypeAt θ V τ S φ := by
  refine ⟨H, _, _, σ, lam, ε, P, hE, hD, hP, hJ, fun x => ?_⟩
  obtain ⟨n, L, v, hv, hφ⟩ := h x
  let vv : ℕ → H := fun i => if hi : i < n then v ⟨i, hi⟩ else 0
  let ll : ℕ → (H →ₗ[ℂ] ℂ) := fun i => if hi : i < n then ((L ⟨i, hi⟩ : H →L[ℂ] ℂ) : H →ₗ[ℂ] ℂ) else 0
  let CC : ℕ → ℝ := fun i => if hi : i < n then ‖L ⟨i, hi⟩‖ else 0
  have hb : ∀ i w, ‖ll i w‖ ≤ CC i * ‖w‖ := fun i w => by
    by_cases hi : i < n
    · simp only [ll, CC, dif_pos hi]
      exact (L ⟨i, hi⟩).le_opNorm w
    · simp [ll, CC, dif_neg hi]
  refine ⟨vv, fun i => ?_, ll, fun i => ⟨[[]], CC i, by simp, fun w _ => by simpa using hb i w⟩,
    ⟨[[]], CC, by simp, fun i w _ => by simpa using hb i w, fun S' _ => ?_, fun _ => 1, continuous_const,
      fun g hg w _ => ?_⟩, fun g hg => ?_⟩
  · by_cases hi : i < n
    · simp only [vv, dif_pos hi]
      exact hv _
    · simp only [vv, dif_neg hi]
      intro k Xs _
      simpa using contDiff_const
  · refine summable_of_ne_finset_zero (s := Finset.range n) fun i hi => ?_
    have : ¬ i < n := by simpa using hi
    simp [CC, dif_neg this]
  · simp [hD.2.2.1.2.1 _ (GlobalTheory.TypeAtCompare.conj_mem hP hJ hg) w]
  · rw [hφ g hg]
    convert hasSum_sum_of_ne_finset_zero (s := Finset.range n)
      (f := fun i => ll i (σ (P * g * P⁻¹) (vv i))) (fun i hi => by
        have : ¬ i < n := by simpa using hi
        simp [ll, dif_neg this]) using 1
    · rw [Finset.sum_range]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp [ll, vv, i.2]
    · infer_instance

def conjFun {H H' : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [NormedAddCommGroup H']
    [InnerProductSpace ℂ H'] (c : H' ≃ₗᵢ⋆[ℂ] H) (ℓ : H →L[ℂ] ℂ) : H' →L[ℂ] ℂ :=
  LinearMap.mkContinuous
    { toFun := fun w => star (ℓ (c w))
      map_add' := fun a b => by simp
      map_smul' := fun a w => by
        simp only [LinearIsometryEquiv.map_smulₛₗ, map_smul, smul_eq_mul, map_mul, Complex.conj_conj, RingHom.id_apply]
        rw [star_mul', Complex.star_def, Complex.conj_conj] }
    ‖ℓ‖ (fun w => by simpa using ℓ.le_opNorm (c w))

theorem conjFun_apply {H H' : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [NormedAddCommGroup H']
    [InnerProductSpace ℂ H'] (c : H' ≃ₗᵢ⋆[ℂ] H) (ℓ : H →L[ℂ] ℂ) (w : H') : conjFun c ℓ w = star (ℓ (c w)) := rfl

end GlobalTheory.EndCusp

namespace GlobalTheory.EndCusp

open Formalism.IndefR.Mult Matrix

variable {D : D7}

theorem conj_finSum {V : HSp D} {S S' : D.what₂.Tau → SPar} {θ : InfFam D} (M : DSModel V S) (M' : DSModel V S')
    (τ : D.what₂.Tau) [FiniteDimensional ℂ (M.H τ)] (c : M'.H τ ≃ₗᵢ⋆[ℂ] M.H τ)
    (hc : ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ), ∀ w, c (M'.rep τ g w) = M.rep τ g (c w))
    (hsm : ∀ w : M'.H τ, w ∈ M'.sm τ ↔ c w ∈ M.sm τ)
    {J : Set (GA D V)} {χ : GA D V → ℂ} {T : MMap M} (hT : IsMultMap θ M J χ T) (x : GA D V) (z : SmT M) :
    ∃ (n : ℕ) (L : Fin n → (M'.H τ →L[ℂ] ℂ)) (v : Fin n → M'.H τ),
      (∀ i, SmoothVec (lieAt V τ) (fun g => M'.σ τ (M'.fr τ * g * (M'.fr τ)⁻¹)) (v i)) ∧
      ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ), star (PiTensorProduct.lift T z (x * atTau θ V τ g)) =
        ∑ i, L i (M'.σ τ (M'.fr τ * g * (M'.fr τ)⁻¹) (v i)) := by
  induction z using PiTensorProduct.induction_on with
  | smul_tprod r f =>
    obtain ⟨ℓ, -, hℓ⟩ := GlobalTheory.DefiniteEnd.exists_sobCont M τ T f x
    have hw : c.symm (f τ) ∈ M'.sm τ := (hsm _).2 (by simp)
    have hsv : SmoothVec (lieAt V τ) (fun g => M'.σ τ (M'.fr τ * g * (M'.fr τ)⁻¹)) (c.symm (f τ)) := by
      rw [GlobalTheory.SmVec.sm_eq M' τ] at hw
      exact hw
    refine ⟨1, fun _ => star r • conjFun c (LinearMap.toContinuousLinearMap ℓ), fun _ => c.symm (f τ), fun _ => hsv,
      fun g hg => ?_⟩
    have e1 := congrFun (hT.equiv τ g hg f ⟨M.rep τ g (f τ), GlobalTheory.ConjMult.rep_mem_sm M τ hg (f τ).2⟩ rfl) x
    have e3 : T f (x * atTau θ V τ g) = ℓ (M.rep τ g (f τ)) := by
      rw [hℓ ⟨M.rep τ g (f τ), GlobalTheory.ConjMult.rep_mem_sm M τ hg (f τ).2⟩]
      exact e1.symm
    have e2 : M.rep τ g (f τ) = c (M'.rep τ g (c.symm (f τ))) := by
      rw [hc g hg, LinearIsometryEquiv.apply_symm_apply]
    rw [Fin.sum_univ_one, map_smul, PiTensorProduct.lift.tprod, Pi.smul_apply, ContinuousLinearMap.smul_apply, conjFun_apply,
      smul_eq_mul, smul_eq_mul, star_mul', e3, LinearMap.coe_toContinuousLinearMap', e2]
    rfl
  | add a b ha hb =>
    obtain ⟨n₁, L₁, v₁, hv₁, h₁⟩ := ha
    obtain ⟨n₂, L₂, v₂, hv₂, h₂⟩ := hb
    refine ⟨n₁ + n₂, Fin.append L₁ L₂, Fin.append v₁ v₂, fun i => ?_, fun g hg => ?_⟩
    · refine Fin.addCases (fun i => ?_) (fun i => ?_) i
      · simpa using hv₁ i
      · simpa using hv₂ i
    · rw [Fin.sum_univ_add, map_add, Pi.add_apply, star_add, h₁ g hg, h₂ g hg]
      simp

end GlobalTheory.EndCusp

namespace GlobalTheory.EndCusp

open Formalism.IndefR.Mult Matrix

variable {D : D7}

theorem isAutFunSm_lift {V : HSp D} {S : D.what₂.Tau → SPar} {θ : InfFam D} {M : DSModel V S} {J : Set (GA D V)}
    {χ : GA D V → ℂ} {T : MMap M} (hT : IsMultMap θ M J χ T) (z : SmT M) :
    IsAutFunSm θ V (PiTensorProduct.lift T z) := by
  induction z using PiTensorProduct.induction_on with
  | smul_tprod r f =>
    rw [map_smul, PiTensorProduct.lift.tprod]
    exact GlobalTheory.Mem.AutSpace.isAutFunSm_smul r (hT.aut f)
  | add a b ha hb =>
    rw [map_add]
    exact GlobalTheory.Mem.AutSpace.isAutFunSm_add ha hb

variable {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

set_option maxHeartbeats 1000000 in

theorem formX_props (R : RealDat D A Ks) (hθ : R.models_inf) (hc : R.models_cX) (hpr : R.models_prX) (hH : R.models_HX)
    (d : ChainVec R) (t : T) (y : (R.HX t).H) :
    IsAutFunSm R.θ D.sp.X' (d.formX t y) ∧ IsCuspFun D.sp.X' (d.formX t y) ∧
      ∀ τ, IsTypeAt R.θ D.sp.X' τ ((Ptw D).Dpar D.R.m τ) fun g => star (d.formX t y g) := by
  have hx := (hH t).2.1.le (LinearMap.mem_range_self (R.HX t).e y)
  have hT := GlobalTheory.DefiniteEnd.isMultMap_toMap hθ D.sp.X'_sig (GlobalTheory.DefiniteEnd.end_definite D) R.MX hc hpr hx
  have e : d.formX t y =
      PiTensorProduct.lift (PiTensorProduct.lift.symm (R.cX.toMap R.prX ((R.HX t).e y))) d.v := by
    rw [LinearEquiv.apply_symm_apply]; rfl
  rw [e]
  refine ⟨isAutFunSm_lift hT _, GlobalTheory.DefiniteEnd.isCuspFun_of_definite D.sp.X'_sig (GlobalTheory.DefiniteEnd.end_definite D) _,
    fun τ => ?_⟩
  haveI := GlobalTheory.DefiniteEnd.finiteDimensional_model D.sp.X'_sig (GlobalTheory.DefiniteEnd.end_definite D) R.MX τ
  obtain ⟨M', c, hc'⟩ := @GlobalTheory.ConjDS.exists_conjModel D D.sp.X' (parB (Ptw D) D.R.m) R.MX
  have hsm := (GlobalTheory.ConjMult.conj_mult R.θ R.MX M' c hc').1 τ
  have hE := M'.enum τ
  simp only [parB, dualPar_dualPar] at hE
  exact isTypeAt_of_finSum R.θ D.sp.X' τ hE (M'.ds τ) (M'.fr_unit τ) (M'.fr_gram τ) _
    fun x => conj_finSum R.MX M' τ (c τ) (hc' τ) hsm hT x d.v

theorem props_cast (θ : InfFam D) (S : D.what₂.Tau → SPar) {Λ : Submodule (𝓞 D.host.E) (Fin D.sp.X'.rank → D.host.E)}
    (X : LSp D) (h : X = ⟨D.sp.X', Λ⟩) (φ : GA D D.sp.X' → ℂ) (h1 : IsAutFunSm θ D.sp.X' φ) (h2 : IsCuspFun D.sp.X' φ)
    (h3 : ∀ τ, IsTypeAt θ D.sp.X' τ (S τ) fun g => star (φ g)) :
    IsAutFunSm θ X.sp (fun g => φ (cast (congrArg (fun X : LSp D => GA D X.sp) h) g)) ∧
      IsCuspFun X.sp (fun g => φ (cast (congrArg (fun X : LSp D => GA D X.sp) h) g)) ∧
      ∀ τ, IsTypeAt θ X.sp τ (S τ) fun g => star (φ (cast (congrArg (fun X : LSp D => GA D X.sp) h) g)) := by
  subst h
  exact ⟨h1, h2, h3⟩

end GlobalTheory.EndCusp

namespace GlobalTheory.EndCusp

theorem formTop_isCuspListed : GlobalTheory.FunPr.Hypotheses₂ → GlobalTheory.RowClaim.Big fun {D} _ _ _ _ {T} _ _ _ _ _ {R} ch => ∀ (t : T) (y : (R.HX t).H), GlobalTheory.FlipRun.IsCuspListed ch.W.θ (.grid 0 D.R.m) (GlobalTheory.RowClaim.formTop ch t y) := by
  intro _
  refine ⟨0, fun ε CF _ => ⟨0, fun D large₂ _ _ Γ _ _ Pl0 T A Ks _ _ _ R F hS ch hch _ => ?_⟩⟩
  intro t y
  have hm := hS.core.models
  obtain ⟨h1, h2, h3⟩ := formX_props R hm.inf hm.cX hm.prX hm.HX ch.cv t y
  have hθ : ch.W.θ = R.θ := hch.toIsBase.weil.θ
  obtain ⟨k1, k2, k3⟩ := props_cast R.θ (fun τ => Node.par D ch.sc.cGap (.grid 0 D.R.m) τ) (columnBlock R.toLevCh D.R.m)
    (colY_m R.toLevCh) (ch.cv.formX t y) h1 h2 (fun τ => by
      rw [show Node.par D ch.sc.cGap (.grid 0 D.R.m) τ = (Ptw D).Dpar D.R.m τ from parV_zero D _ le_rfl τ]
      exact h3 τ)
  rw [hθ]
  exact ⟨k1, k2, k3⟩

end GlobalTheory.EndCusp
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.DecompAtZero
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.Grow GlobalTheory.Size

noncomputable section

namespace GlobalTheory.KFinDecomp

variable {D : D7}

def Cls (θ : InfFam D) (N : GlobalTheory.Grid.Node D) (U : Subgroup (GA D N.V)) : Set (GA D N.V → ℂ) :=
  {f | GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.IsCuspOfType θ N f ∧ ∀ k ∈ U, k ∈ GfC N.V → ∀ g, f (g * k) = f g}

structure IsOpAt (θ : InfFam D) (N : GlobalTheory.Grid.Node D) (𝒞 : Set (GA D N.V → ℂ))
    (Ty : D.what₂.Tau → (GA D N.V → ℂ) → Prop) (τ : D.what₂.Tau) (A : (GA D N.V → ℂ) → (GA D N.V → ℂ)) : Prop where

  cont : ∀ f, Continuous f → Continuous (A f)

  add : ∀ f f', Continuous f → Continuous f' → A (f + f') = A f + A f'

  smul : ∀ (c : ℂ) f, Continuous f → A (c • f) = c • A f

  maps : ∀ f ∈ 𝒞, A f ∈ 𝒞

  keep : ∀ τ', τ' ≠ τ → ∀ f ∈ 𝒞, Ty τ' f → Ty τ' (A f)

  tr : ∀ τ', τ' ≠ τ → ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D N.V τ'), ∀ f ∈ 𝒞,
    A (rTr N.V (atTau θ N.V τ' g) f) = rTr N.V (atTau θ N.V τ' g) (A f)

  lie : ∀ τ', τ' ≠ τ → ∀ X ∈ lieAt N.V τ', ∀ f ∈ 𝒞, A (Rder θ N.V τ' X f) = Rder θ N.V τ' X (A f)

def DecompAt (θ : InfFam D) (N : GlobalTheory.Grid.Node D) (𝒞 : Set (GA D N.V → ℂ))
    (Ty : D.what₂.Tau → (GA D N.V → ℂ) → Prop) (τ : D.what₂.Tau) : Prop :=
  ∃ (m : ℕ) (a : Fin m → GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.kFin N.M τ)
    (A : Fin m → GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.kFin N.M τ → (GA D N.V → ℂ) → (GA D N.V → ℂ)),
    (∀ j u, IsOpAt θ N 𝒞 Ty τ (A j u)) ∧
    (∀ j, ∀ f ∈ 𝒞, (∀ u u', A j (u + u') f = A j u f + A j u' f) ∧ (∀ (c : ℂ) u, A j (c • u) f = c • A j u f) ∧
      (∀ k ∈ GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.maxCpt N.M τ, ∀ u w : GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.kFin N.M τ,
        (w : N.M.H τ) = N.M.rep τ k u → A j w f = rTr N.V (atTau θ N.V τ k) (A j u f)) ∧
      (∀ X ∈ lieAt N.V τ, ∀ u w : GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.kFin N.M τ,
        (w : N.M.H τ) = dRep (N.M.rep τ) X u → A j w f = Rder θ N.V τ X (A j u f))) ∧
    ∀ f ∈ 𝒞, Ty τ f → f = ∑ j, A j (a j) f

theorem isOpAt_id (θ : InfFam D) (N : GlobalTheory.Grid.Node D) (𝒞 : Set (GA D N.V → ℂ))
    (Ty : D.what₂.Tau → (GA D N.V → ℂ) → Prop) (τ : D.what₂.Tau) : IsOpAt θ N 𝒞 Ty τ id :=
  ⟨fun _ h => h, fun _ _ _ _ => rfl, fun _ _ _ => rfl, fun _ h => h, fun _ _ _ _ h => h, fun _ _ _ _ _ _ => rfl,
    fun _ _ _ _ _ _ => rfl⟩

end GlobalTheory.KFinDecomp

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.DefiniteBottomWeilActionFockPureTensorSubstituti
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx MeasureTheory

noncomputable section

namespace GlobalTheory.BottomAct

open GlobalTheory.Grid (neg sgn ofSgn)

theorem conj_invT_of_unitary {n : ℕ} {M : Matrix (Fin n) (Fin n) ℂ} (h : Matrix.conjTranspose M * M = 1) :
    ((M⁻¹).transpose).map (starRingEnd ℂ) = M := by
  rw [Matrix.inv_eq_left_inv h]
  ext a b
  simp only [Matrix.map_apply, Matrix.transpose_apply, Matrix.conjTranspose_apply, RCLike.star_def, Complex.conj_conj]

theorem conj_invT_compAt {D : D7} {θ : InfFam D} (hθ : IsInfFam θ) {V : HSp D} (hV : V.gram = 1) (g : GA D V)
    (τ : D.what₂.Tau) :
    (((compAt θ τ (Formalism.L2.Theta.mt V g))⁻¹).transpose).map (starRingEnd ℂ) = compAt θ τ (Formalism.L2.Theta.mt V g) := by
  have h1 := GlobalTheory.StdUnn.CartanMove.compAt_isom hθ V g τ
  have hg : gramAt D V τ = 1 := by
    unfold gramAt
    rw [hV]
    exact Matrix.map_one _ (map_zero _) (map_one _)
  rw [hg, Matrix.mul_one] at h1
  exact conj_invT_of_unitary h1

theorem om_pureTensorO_bottom : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {i j : Fin D.R.m} {A A' WW : HSp D} {X : Tri T A A' WW}, IsBottomTri W i j X → ∀ (t : T) (g : GA D A) (P : MvPolynomial (FVar D WW.rank A.rank) ℂ), (X.ω t).toSgn true ((GlobalTheory.Grid.ofSgn true A).symm g, 1) (pureTensorO W.ψ W.θ (GlobalTheory.Grid.neg A) WW (fun τ => -X.rA.s τ) X.rW.s X.rA.B X.rW.B (X.f t) P) = pureTensorO W.ψ W.θ (GlobalTheory.Grid.neg A) WW (fun τ => -X.rA.s τ) X.rW.s X.rA.B X.rW.B ((X.ω t).toSgn true ((GlobalTheory.Grid.ofSgn true A).symm g, 1) (X.f t)) (GlobalTheory.CompactHowe.substF (fun _ => (1 : Matrix (Fin WW.rank) (Fin WW.rank) ℂ)) (fun τ => compAt W.θ τ (Formalism.L2.Theta.mt A g)) P) := by
  intro D T L sc G W i j A A' WW X hX t g P
  have hI := hX.is
  have hθ : IsInfFam W.θ := hI.isVac.2.inf
  have hψ : IsStdChar D W.ψ (-1) := hI.isVac.1
  have hom := hI.weil t
  have hsA : ∀ τ, X.rA.s τ = 1 := fun τ => (hX.std.2.2 τ).1
  have hsW : ∀ τ, X.rW.s τ = 1 := fun τ => (hX.stdW.2.2 τ).1
  have hBA : ∀ τ, X.rA.B τ = 1 := fun τ => (hX.std.2.2 τ).2
  have hf : IsThetaFunO W.ψ (neg A) WW (X.f t) := (GlobalTheory.ConstRatio.theta_f hI t).1
  have hmt : Formalism.L2.Theta.mt (neg A) ((ofSgn true A).symm g) = Formalism.L2.Theta.mt A g := by
    rw [← GlobalTheory.Grid.mt_ofSgn, MulEquiv.apply_symm_apply]
  set u : D.what₂.Tau → Matrix (Fin A.rank) (Fin A.rank) ℂ := fun τ => compAt W.θ τ (Formalism.L2.Theta.mt A g) with hu
  have one : ∀ τ, compAt W.θ τ (Formalism.L2.Theta.mt WW 1) = 1 := fun τ => GlobalTheory.StdUnn.CartanMove.compAt_mt_one W.θ τ WW
  have hop := GlobalTheory.OrientedHeis.om_pureTensorO D W.ψ W.θ (neg A) WW _ _ ((X.ω t).toSgn true) hom hθ
    (fun τ => -X.rA.s τ) (fun τ => -X.rA.s τ) X.rA.B (fun τ => X.rA.B τ * u τ) X.rW.s X.rW.s X.rW.B
    (fun τ => X.rW.B τ * 1) ((ofSgn true A).symm g) 1
    (fun τ => by rw [hmt, hsA, Matrix.neg_mul, Matrix.mul_neg, Matrix.one_mul, Matrix.mul_one])
    (fun τ => by rw [one, Matrix.mul_one, Matrix.one_mul])
    (fun τ => by rw [hmt, hBA, Matrix.mul_one, Matrix.one_mul])
    (fun τ => by rw [one, Matrix.one_mul, Matrix.mul_one]) (X.f t) hf P
  rw [hop.2]
  have hf' : IsThetaFunO W.ψ (neg A) WW ((X.ω t).toSgn true ((ofSgn true A).symm g, 1) (X.f t)) :=
    hom.om_pres _ _ hf
  have e1 : (fun τ => -X.rA.s τ) = fun _ => (-1 : Matrix (Fin A.rank) (Fin A.rank) ℂ) := funext fun τ => by rw [hsA]
  have e2 : X.rW.s = fun _ => (1 : Matrix (Fin WW.rank) (Fin WW.rank) ℂ) := funext hsW
  have key := GlobalTheory.FockNegSubst.pureTensorO_negSp_subst D W.ψ W.θ A WW hψ hθ X.rA.B u X.rW.B (fun _ => 1) _ hf' P
  have hunit : ∀ τ, (((u τ)⁻¹).transpose).map (starRingEnd ℂ) = u τ := fun τ => conj_invT_compAt hθ hX.std.1 g τ
  have hv : (fun _ : D.what₂.Tau => (1 : Matrix (Fin WW.rank) (Fin WW.rank) ℂ).map (starRingEnd ℂ)) = fun _ => 1 :=
    funext fun _ => Matrix.map_one _ (map_zero _) (map_one _)
  rw [funext hunit, hv] at key
  rw [e1, e2]
  exact key

end GlobalTheory.BottomAct

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.DenseUnitaryRealPointsAlgebraicEntries
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx MeasureTheory

noncomputable section

namespace GlobalTheory.RealAlgDense

theorem dense_alg : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ V : HSp D, Dense {g : GinfC V | ∀ τ a b, IsAlgebraic ℚ (compAt θ τ (Formalism.L2.Theta.mt V g.1) a b)} := by
  intro D θ hθ V
  obtain ⟨e, he⟩ := GlobalTheory.Mem.VolSplit.exists_adelic_split D.host.F D.host.E D.sp.cm.sig V.rank V.gram
  have hfin : ∀ h : GA D V, h ∈ GinfC V ↔ (e h).2 = 1 := fun h =>
    ⟨fun H => Subtype.ext (Units.ext ((he h).1.trans (congrArg Units.val (MonoidHom.mem_ker.1 H)))),
      fun H => MonoidHom.mem_ker.2 (Units.ext ((he h).1.symm.trans (by rw [H]; rfl)))⟩
  have hne : ∃ z, D.sp.cm.sig z ≠ z := by
    by_contra h
    push Not at h
    have hs : Function.Surjective (algebraMap D.host.F D.host.E) := fun z => (D.sp.cm.fixed z).1 (h z)
    have h1 : Module.finrank D.host.F D.host.E = 1 :=
      Algebra.finrank_eq_one_iff_bijective_algebraMap.2 ⟨(algebraMap D.host.F D.host.E).injective, hs⟩
    have h2 := D.sp.cm.deg2
    omega
  have hd := GlobalTheory.RealApprox.dense_inf D.host.F D.host.E D.sp.cm.sig (fun x => star_star x) hne V.gram
    (GlobalTheory.AutFunCounterexample.gram_herm V) (GlobalTheory.AutFunCounterexample.gram_det_ne V)
  let Φ : HA (Ainf D.host.F) D.sp.cm.sig V.gram → GinfC V := fun x =>
    ⟨e.symm (x, 1), (hfin _).2 (by rw [e.apply_symm_apply])⟩
  have hΦc : Continuous Φ :=
    Continuous.subtype_mk (e.symm.continuous.comp (continuous_id.prodMk continuous_const)) _
  have hΦs : Function.Surjective Φ := by
    intro g
    refine ⟨(e g.1).1, Subtype.ext ?_⟩
    change e.symm ((e g.1).1, 1) = g.1
    rw [← (hfin g.1).1 g.2]
    exact e.symm_apply_apply g.1
  refine Dense.mono ?_ (hΦs.denseRange.dense_image hΦc hd)
  rintro _ ⟨x, ⟨γ₀, hγ₀, hx⟩, rfl⟩ τ a b
  have hm := (he (e.symm (x, 1))).2
  rw [e.apply_symm_apply] at hm
  have key : compAt θ τ (Formalism.L2.Theta.mt V (Φ x).1) a b = tauE D τ (γ₀.1 a b) := by
    change infMat D.sp.cm.sig V.gram (θ τ) (e.symm (x, 1)) a b = _
    unfold infMat
    rw [← hm, ← hx]
    exact (hθ τ).1 _
  rw [key]
  have h0 : IsAlgebraic ℚ (γ₀.1 a b) := Algebra.IsAlgebraic.isAlgebraic (R := ℚ) (γ₀.1 a b)
  first
    | exact h0.algHom (tauE D τ).toRatAlgHom
    | exact IsAlgebraic.map (tauE D τ).toRatAlgHom h0
    | exact (isAlgebraic_algHom_iff (tauE D τ).toRatAlgHom (tauE D τ).injective).2 h0

end GlobalTheory.RealAlgDense
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.DifferentiableIntertwiningPair
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3

open scoped TensorProduct
open GlobalTheory.MovedDict Formalism.L2.Ker GlobalTheory.SignedHC

open scoped TensorProduct
open GlobalTheory.MovedDict Formalism.L2.Ker GlobalTheory.SignedHC

namespace GlobalTheory.MovedDict.Entire

theorem differentiable_U' {D : D7} {T : Tor D} {N N' : ℕ} (x : VC D N N') {G : VC D N N' → ℂ}
    (hG : Differentiable ℂ G) : Differentiable ℂ (U D T x G) := by
  have h : Differentiable ℂ (fun z : VC D N N' => Hf D T z x) := by
    unfold Hf
    fun_prop
  unfold U
  fun_prop

theorem differentiable_Iop' {D : D7} {T : Tor D} {N N' : ℕ} (A B : AddSubgroup (VC D N N'))
    {G : VC D N N' → ℂ} (hG : Differentiable ℂ G) : Differentiable ℂ (Iop D T A B G) := by
  unfold Iop
  by_cases h : (A.addSubgroupOf B).index = 0
  · simp [h]
  · haveI : Finite (B ⧸ A.addSubgroupOf B) := Nat.finite_of_card_ne_zero h
    haveI := Fintype.ofFinite (B ⧸ A.addSubgroupOf B)
    simp only [finsum_eq_sum_of_fintype]
    exact (Differentiable.fun_sum fun q _ => (differentiable_U' _ hG).const_mul _).const_mul _

theorem differentiable_intertwining_moved : GlobalTheory.FunPr.Hypotheses₂ → (∀ D, GlobalTheory.NormSum.Inp D) → ∀ {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type}
    {A : FamIn D.what₂.LL Γ Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks}
    (ch : Choice R), ch.Is → ∀ (p : Pair T), DefPair D.R.m p → ∀ (x : FinPt ch.G p.small) (y : FinPt ch.G p.big),
    Differentiable ℂ (Iop D (tor0 D D.host.ccK ch.S.Z.δ) (La0 D (tor0 D D.host.ccK ch.S.Z.δ) _ _) (Formalism.MainNotions.TaylorLogMetric.La D (tor0 D D.host.ccK ch.S.Z.δ) (GlobalTheory.MovedDict.srcLat ch.S.toGridChoice p x y) (GlobalTheory.MovedDict.tgtLat ch.S.toGridChoice p x y)) (ch.S.Z.e0 p)) := by
  intro _ _ D Γ _ _ Pl0 T A Ks _ _ _ R ch _ p hp x y
  exact differentiable_Iop' _ _ (ch.S.Z.e0_is p hp).1.1

end GlobalTheory.MovedDict.Entire
end

