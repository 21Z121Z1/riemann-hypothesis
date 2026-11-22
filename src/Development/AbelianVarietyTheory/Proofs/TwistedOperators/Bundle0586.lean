import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0567
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0003
import Formalism.LocalToGlobal.IndefiniteReal.NormalDecomposition.PairingCommutesLiftOperators
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0017
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0336
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0217
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0566
import Formalism.LocalToGlobal.IndefiniteReal.BaseLiftsPackageOfPrimitiveLinks
import Formalism.LocalToGlobal.IndefiniteReal.NormalDecomposition.LiftHeckeOperators
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0897
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0513
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0019
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsAllTiedNotStable
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.DiscreteSeriesHermitianUniqueOfClassification
import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.Bundle0007
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0091
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0372
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0364
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1897
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNatMulIntegralOfIsCompact
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0544
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.TwistPlacesOffPrimeQZero
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0492
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0458
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0407
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0061
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NonzeroPlacesOverPrimesLifts
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnitVacuumEntireFactorIsThetaMovedLattices
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0943
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0521
import Formalism.SharpRestriction.GlobalSchurBounds.StandardLatticesGL3
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1876
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1714
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0547
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumOKEx

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaKernelGridRationalLeftInvariant
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.IndefiniteRowSideFullHecke.MinorOrderedEntries

namespace GlobalTheory.RowReal

variable {D : D7}

theorem GQ_negGA_mem (V : HSp D) {γ : GA D V} (hγ : γ ∈ GQ V) : negGA V γ ∈ GQ (negSp V) := by
  obtain ⟨x, hx, e⟩ := Subgroup.mem_map.1 (Subgroup.mem_subgroupOf.1 hγ)
  refine Subgroup.mem_subgroupOf.2 (Subgroup.mem_map.2 ⟨x, ?_, e⟩)
  have hx' : Formalism.UG.cT _ (x : Matrix _ _ _) * V.gram * (x : Matrix _ _ _) = V.gram := hx
  show Formalism.UG.cT _ (x : Matrix _ _ _) * (-V.gram) * (x : Matrix _ _ _) = -V.gram
  rw [Matrix.mul_neg, Matrix.neg_mul, hx']

variable {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc}

theorem toPair_GQ (p : Pair T) {γ : GA D (G.V p.small)} {γ' : GA D (G.V p.big)} (hγ : γ ∈ GQ (G.V p.small))
    (hγ' : γ' ∈ GQ (G.V p.big)) : (G.toPair p γ γ').1 ∈ GQ (G.pS p) ∧ (G.toPair p γ γ').2 ∈ GQ (G.pT p) := by
  cases p with
  | chi i j => exact ⟨GQ_negGA_mem _ hγ', hγ⟩
  | mu t i j => exact ⟨hγ, hγ'⟩
  | core i => exact ⟨GQ_negGA_mem _ hγ', hγ⟩
  | top t j => exact ⟨hγ, hγ'⟩

theorem ker_rat_left : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (W : G.Weil) (p : Pair T),
    p.InRange D.R.m →
    ∀ f : WO (G.pS p) (G.pT p) → ℂ, IsThetaFunO W.ψ (G.pS p) (G.pT p) f → ∀ γ ∈ GQ (G.V p.small), ∀ γ' ∈ GQ (G.V p.big),
    ∀ g h, W.ker p f (γ * g) (γ' * h) = W.ker p f g h := by
  intro D T L sc G W p hp f hf γ hγ γ' hγ' g h
  have hw := W.om_is p hp
  obtain ⟨h1, h2⟩ := toPair_GQ p hγ hγ'
  have e : W.ker p f (γ * g) (γ' * h) =
      W.om p (G.toPair p γ γ') (W.om p (G.toPair p g h) f) 0 := by
    simp only [GridData.Weil.ker, thetaKO, toPair_mul, Prod.mk.eta, map_mul, Module.End.mul_apply]
  rw [e]
  have := hw.om_aut _ h1 _ h2 (W.om p (G.toPair p g h) f) (hw.om_pres (G.toPair p g h) f hf)
  rw [Prod.mk.eta] at this
  rw [this]
  simp only [GridData.Weil.ker, thetaKO, Prod.mk.eta]

end GlobalTheory.RowReal
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaLiftOntoOfInjectiveEigenspaces
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.LiftRows

namespace GlobalTheory.LiftOntoRed

theorem onto_red : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) {s : ℕ}, A3.fam3.Ok3 s → R.WeakCharacterisation F → R.toRealDat.ExAt → LiftInj R.toRealDat → UpInjW R.toRealDat → (∀ j t, (A3.A.fam.L j t).OkH ∧ (A3.liftI j t).InertRationalAdjoint) → R.PGEquiv F → R.toRealDat.LUnif → ∀ hW, HeckeIntertwiningLifts A3 (R.toCx3 F) hW → U2.OntoC A3 (R.toCx3 F) F.P0 F.ψ0 F.P1 F.ψ1 hW := by
  intro D G _ _ Pl0 I0 T A3 Ks _ _ _ R F s hok hC hEx hLI hUI hH hPG hLU hW hTh j
  exact GlobalTheory.OntoLinAlg.ontoParts_of _ (fun i x => hTh.intw j _ i x)
    (U2.adjoint_closed_lift_operators hH (RealDat3.kFormL_of hC.base.models) (RealDat3.jIsoL_of hC.base.models) j)
    (GlobalTheory.T.good_forms_le_range_theta_adjoint_base_tuple R F hok hC hEx hUI hH hPG hLU j) (GlobalTheory.T.kernelProjection_preserves_good_forms_base_level R F hok hC hEx hH hPG j)
    (GlobalTheory.T.thetaLift_injective_goodPart_jointEigenspace R F hok hC hEx hLI hH hPG j)

end GlobalTheory.LiftOntoRed
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaLiftVerticalCuspidalTypeStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.theta_lift_vertical_cuspidal_type : GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.LiftsCuspidal → GlobalTheory.FunPr.Hypotheses₂ → ∀ (D : D7), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.Sizes D → ∀ (G₀ : Type) [Group G₀] [Fintype G₀] (Pl0 T : Type) (A : FamIn D.what₂.LL G₀ Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (G : GlobalTheory.Grid.GridPre R), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.RowBase R → G.Is → ∀ t i j, i < D.R.m → j ≤ D.R.m → ∀ Φ, IsThetaFunO R.ψ (GlobalTheory.Grid.neg (G.V (i + 1) j).V) (G.V i j).V Φ → ∀ F : (G.V i j).Maps, F ∈ (G.V i j).Cusp R.θ → ∀ v : SmT (G.V i j).M, (∀ h, IntegrableOn (fun g => thetaKO (G.X i j).ω h g Φ * F v g) (G.meas t i j).fd (G.meas t i j).ν) → ∀ C : Set (GA D (G.V (i + 1) j).V), IsCompact C → ∀ ε : ℝ, 0 < ε → ∃ (n : ℕ) (f : Fin n → (WO (G.V (i + 1) j).V (G.V i j).V → ℂ)) (p : Fin n → GlobalTheory.Grid.Pol (G.V (i + 1) j) (G.V i j)), (∀ l, GlobalTheory.Grid.IsFinVec R.ψ R.θ true (G.V (i + 1) j) (G.V i j) (f l)) ∧ ∀ h ∈ C, ‖(∫ g in (G.meas t i j).fd, thetaKO (G.X i j).ω h g Φ * F v g ∂(G.meas t i j).ν) - ∑ l, ∫ g in (G.meas t i j).fd, thetaKO (G.X i j).ω h g (GlobalTheory.Grid.fock R.ψ R.θ true (G.V (i + 1) j) (G.V i j) (f l) (p l)) * F v g ∂(G.meas t i j).ν‖ < ε := by
  first | exact @GlobalTheory.ThetaApproxX.approx | exact GlobalTheory.ThetaApproxX.approx | (intros; apply GlobalTheory.ThetaApproxX.approx <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaTransformDarbouxModelLinearInjective
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct ComplexConjugate

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

noncomputable section

namespace GlobalTheory.ThetaTransformInj

theorem linear_injective : ∀ (D : D7) {m k d : ℕ} {Y : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc D.host.F D.host.E m} {Z : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc D.host.F D.host.E k}
    (Mo : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model D.sp.cm.sig Y Z) (ψ : AddChar (AF D.host.F) ℂ) (G : Matrix (Fin m) (Fin m) D.host.E)
    (e : Fin k ≃ Fin d), Mo.IsGood ψ → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsStd ψ → Y.J.det ≠ 0 → Z.J.det ≠ 0 → G.det ≠ 0 →
    ∃ T : ((Fin m × Fin k → AF D.host.F) → ℂ) →ₗ[ℂ] (Matrix (Fin d) (Fin m) (AE D) → ℂ),
      (∀ Φ ∈ GlobalTheory.WeilM.schA D.host.F (Fin m × Fin k), T Φ = GlobalTheory.TripleRead.thO Mo ψ G e Φ) ∧
      ∀ Φ ∈ GlobalTheory.WeilM.schA D.host.F (Fin m × Fin k), T Φ = 0 → Φ = 0 := by
  intro D m k d Y Z Mo ψ G e _ hψ _ _ hG
  have hGG : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM G * GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM G⁻¹ = 1 := by
    simp only [GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM]
    rw [← Matrix.map_mul, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hG), Matrix.map_one _ (map_zero _) (map_one _)]
  have hsur : ∀ u, ∃ x, GlobalTheory.TripleRead.ptO G e x = u := by
    intro u
    refine ⟨(HMul.hMul (u.submatrix id e.symm)ᵀ (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM G) : Matrix (Fin d) (Fin m) (AE D)), ?_⟩
    simp only [GlobalTheory.TripleRead.ptO, Matrix.mul_assoc, hGG, Matrix.mul_one, Matrix.transpose_transpose]
    ext i j
    simp
  have hadd : ∀ (u : Matrix (Fin m) (Fin k) (AE D)) (Φ Ψ : (Fin m × Fin k → AF D.host.F) → ℂ),
      Mo.co.rho ψ u (Φ + Ψ) = Mo.co.rho ψ u Φ + Mo.co.rho ψ u Ψ := by
    intro u Φ Ψ
    funext y
    simp [GlobalTheory.WeilM.Darboux.rho, GlobalTheory.WeilM.schr, mul_add]
  have hsmul : ∀ (u : Matrix (Fin m) (Fin k) (AE D)) (c : ℂ) (Φ : (Fin m × Fin k → AF D.host.F) → ℂ),
      Mo.co.rho ψ u (c • Φ) = c • Mo.co.rho ψ u Φ := by
    intro u c Φ
    funext y
    simp only [GlobalTheory.WeilM.Darboux.rho, GlobalTheory.WeilM.schr, Pi.smul_apply, smul_eq_mul]
    ring
  let f : GlobalTheory.WeilM.schA D.host.F (Fin m × Fin k) →ₗ[ℂ] (Matrix (Fin d) (Fin m) (AE D) → ℂ) :=
    { toFun := fun Φ => GlobalTheory.TripleRead.thO Mo ψ G e Φ.1
      map_add' := fun Φ Ψ => by
        funext x
        simp only [GlobalTheory.TripleRead.thO, Submodule.coe_add, Pi.add_apply, hadd]
        exact GlobalTheory.WeilM.thetaSum_add _ (GlobalTheory.HeisSchA.rho_mem_schA Mo ψ hψ _ _ Φ.2)
          (GlobalTheory.HeisSchA.rho_mem_schA Mo ψ hψ _ _ Ψ.2)
      map_smul' := fun c Φ => by
        funext x
        simp only [GlobalTheory.TripleRead.thO, Submodule.coe_smul, Pi.smul_apply, hsmul, smul_eq_mul, RingHom.id_apply]
        exact GlobalTheory.WeilM.thetaSum_smul _ c _ }
  obtain ⟨T, hT⟩ := LinearMap.exists_extend f
  have hTf : ∀ Φ ∈ GlobalTheory.WeilM.schA D.host.F (Fin m × Fin k), T Φ = GlobalTheory.TripleRead.thO Mo ψ G e Φ := by
    intro Φ hΦ
    exact LinearMap.congr_fun hT ⟨Φ, hΦ⟩
  refine ⟨T, hTf, fun Φ hΦ h0 => ?_⟩
  rw [hTf Φ hΦ] at h0
  refine GlobalTheory.ThetaInj.theta_inj Mo ψ hψ (fun u => u) Φ 0 (fun _ => 0) ⟨hΦ, fun u => ?_⟩
    ⟨Submodule.zero_mem _, fun u => ?_⟩
  · obtain ⟨x, rfl⟩ := hsur u
    exact congrFun h0 x
  · simp [GlobalTheory.WeilM.thetaSum, GlobalTheory.WeilM.Darboux.rho, GlobalTheory.WeilM.schr]

end GlobalTheory.ThetaTransformInj
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.TotalTensorThetaLiftEqOfSchwartzEqStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open scoped Pointwise

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.totalTensorThetaLift_eq_of_schwartz_eq : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {μ₀ : T}, L.Is μ₀ → ∀ {W : G.Weil} (M : Vol G) (ρ : RealMatch W) (t : T) {e : AE D}, IsIdemSum e (locPl G t) → GlobalTheory.FlipRun.CuspStep W M ρ t → ∀ {X Y : Node} (p : Path T X Y), GlobalTheory.FlipRun.OnGrid D.R.m t p → ∀ (τ₁ τ₂ : TotT G p) (φ₁ φ₂ : PureT G p → PureT G p), (∀ d ∈ τ₁.support, GlobalTheory.FlipRun.VecAll ρ e p (φ₁ d) d) → (∀ d ∈ τ₂.support, GlobalTheory.FlipRun.VecAll ρ e p (φ₂ d) d) → (∀ x : GlobalTheory.FlipRun.ArgT G p, GlobalTheory.FlipRun.HalfAll e p x → (τ₁.sum fun d c => c * GlobalTheory.FlipRun.famProd p (φ₁ d) x) = τ₂.sum fun d c => c * GlobalTheory.FlipRun.famProd p (φ₂ d) x) → ∀ F : Fn G X, GlobalTheory.FlipRun.IsCuspListed W.θ X F → ∀ Q : GlobalTheory.FlipRun.PolE G →₀ ℂ, liftT W M p (GlobalTheory.FlipRun.tensE W p Q τ₁) F = liftT W M p (GlobalTheory.FlipRun.tensE W p Q τ₂) F := by
  first | exact @GlobalTheory.FlipRun.liftT_tensE_eq_of_famProd | exact GlobalTheory.FlipRun.liftT_tensE_eq_of_famProd | (intros; apply GlobalTheory.FlipRun.liftT_tensE_eq_of_famProd <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.TwistedDataOffBaseLevel
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH NumberField IsDedekindDomain Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.Col2 GlobalTheory.Mem.R3

namespace GlobalTheory.RowEx.DatTw

open Formalism.L2.Host

theorem not_two_primes {R : Type*} [CommRing R] (P : Ideal R) [hP : P.IsPrime] {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hne : p ≠ q) (h1 : (p : R) ∈ P) (h2 : (q : R) ∈ P) : False := by
  obtain ⟨u, v, huv⟩ : IsCoprime (p : ℤ) (q : ℤ) := Nat.isCoprime_iff_coprime.2 ((Nat.coprime_primes hp hq).2 hne)
  apply hP.ne_top
  rw [Ideal.eq_top_iff_one]
  have e := congrArg (Int.cast : ℤ → R) huv
  push_cast at e
  rw [← e]
  exact P.add_mem (P.mul_mem_left _ h1) (P.mul_mem_left _ h2)

theorem unrAt_mul {L : Type} [Field L] [NumberField L] {χ χ' : HChar L} {v : HeightOneSpectrum (𝓞 L)} (h : χ.UnrAt v)
    (h' : χ'.UnrAt v) : (χ * χ').UnrAt v := fun x hx => by
  rw [HChar.loc_mul, h x hx, h' x hx, one_mul]

theorem unrAt_one {L : Type} [Field L] [NumberField L] (v : HeightOneSpectrum (𝓞 L)) : (1 : HChar L).UnrAt v := fun _ _ => rfl

variable {R : Ranks} (H : Host R)

theorem unrAt_of_isTwist {S : Set ℕ} (hS : GlobalTheory.EX.DC.q0H H ∈ S) {ψ : HChar H.E} (hψ : Chr.IsTwist H S ψ)
    {v : HeightOneSpectrum (𝓞 H.E)} (hv : ((GlobalTheory.EX.DC.q0H H : ℕ) : 𝓞 H.E) ∈ v.asIdeal) : ψ.UnrAt v := by
  by_contra h
  obtain ⟨-, hpr, -, hnot⟩ := hψ.2.2.2 v h
  by_cases e : Ideal.absNorm v.asIdeal = GlobalTheory.EX.DC.q0H H
  · exact hnot (e ▸ hS)
  · exact not_two_primes v.asIdeal hpr (GlobalTheory.EX.DC.globalTwisting_spec_fact H).1 e (Ideal.absNorm_mem _) hv

theorem not_overP_pde {v : HeightOneSpectrum (𝓞 H.E)} (hv : ((GlobalTheory.EX.DC.q0H H : ℕ) : 𝓞 H.E) ∈ v.asIdeal) :
    ¬ OverP H H.pde v ∧ ¬ OverP H H.pde' v :=
  ⟨fun h => not_two_primes v.asIdeal H.pde_prime (GlobalTheory.EX.DC.globalTwisting_spec_fact H).1 (GlobalTheory.EX.DC.q0H_ne_pde_and_ne_pde' H).1.symm h hv,
    fun h => not_two_primes v.asIdeal H.pde'_prime (GlobalTheory.EX.DC.globalTwisting_spec_fact H).1 (GlobalTheory.EX.DC.q0H_ne_pde_and_ne_pde' H).2.symm h hv⟩

theorem unrAt_of_mem_set {B : Base} {f : Fr B.toPre} {T : TwDat B} {ξ : HChar B.host.E} (h : ξ ∈ T.set f)
    {v : HeightOneSpectrum (𝓞 B.host.E)} (hv : ((GlobalTheory.EX.DC.q0H B.host : ℕ) : 𝓞 B.host.E) ∈ v.asIdeal) : ξ.UnrAt v := by
  have hd := not_overP_pde B.host hv
  have hdel : f.del.UnrAt v := f.isDel.unr v hd.1
  have hdel' : f.del'.UnrAt v := f.isDel'.unr v hd.2
  simp only [TwDat.set, Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_range] at h
  rcases h with (rfl | rfl | rfl) | ⟨w, rfl⟩
  · exact unrAt_one v
  · exact hdel
  · exact hdel'
  · unfold TwDat.xiTw
    refine unrAt_mul ?_ (unrAt_of_isTwist B.host ?_ (T.psi_tw w) hv)
    · split_ifs
      · exact hdel'
      · exact hdel
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))

end GlobalTheory.RowEx.DatTw

theorem GlobalTheory.RowEx.twisted_data_off_base_level : ∀ (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T) (Z : w.Lt) (hX : B.fields.Ok)
    (Wt : Set B.places.Pl) (z : Dat (w.st Z) w.I hX T Wt), GlobalTheory.RowEx.TwistPlacesOffPrimeQZero z.R.toLevCh ∧ z.R.C = Fr.at (w.st Z) f ∧
      (T.set f).Finite ∧ ∀ t, z.R.xiH t ∈ T.set f := by
  intro B f T w Z hX Wt z
  have hmem : ∀ t, z.R.xiH t ∈ T.set f := fun t => by
    rw [z.lev.xiH t, ← w.xi_range]
    exact ⟨_, rfl⟩
  refine ⟨fun t PP hPP hq => ?_, ?_, ?_, hmem⟩
  · exact (z.lev.is.Q_ram t PP).2 (Or.inl hPP) (GlobalTheory.RowEx.DatTw.unrAt_of_mem_set (hmem t) hq)
  · rw [z.lev.C, w.C_eq]
  · rw [← w.xi_range]
    exact Set.finite_range _
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnitVacuumEntireFactorIsThetaMovedLatticesStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField Matrix MvPolynomial
open GlobalTheory.SignedHC GlobalTheory.ChiGrid Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.FunObj
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitVacuumEntireFactor_isTheta_movedLattices : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (frS : GL (Fin S.rank) D.host.E) (frT : GL (Fin T.rank) D.host.E), Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) frS.1 * S.gram * frS.1 = 1 → Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) frT.1 * T.gram * frT.1 = 1 → ∀ δ : ℂ, Formalism.MainNotions.StandardLatticesGL3.Crv D D.host.ccK δ → δ ≠ 0 → ∀ (Ls : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (Lt : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)), Formalism.MainNotions.StandardLatticesGL3.SD D Ls → Formalism.MainNotions.StandardLatticesGL3.SD D Lt → ∀ f : WO S T → ℂ, IsVacO ψ θ S T (fun _ => 1) (fun _ => 1) (GlobalTheory.MovedDict.inV frS Ls) (GlobalTheory.MovedDict.inV frT Lt) f → ∀ Φ : Formalism.MainNotions.TaylorLogMetric.VC D S.rank T.rank → ℂ, Differentiable ℂ Φ → (∀ w : WO S T, w.map (finPart D) = 0 → f w = GlobalTheory.FockPos.gaussO θ frS frT w * Φ (GlobalTheory.FockPos.zCo θ frS frT w)) → (fun Y => Φ (δ⁻¹ • Y)) ∈ Formalism.MainNotions.TaylorLogMetric.Th D (Formalism.MainNotions.TaylorLogMetric.tor0 D D.host.ccK δ) Ls Lt := by
  first | exact @GlobalTheory.ThetaLawMoved.theta_of_vacuum_moved | exact GlobalTheory.ThetaLawMoved.theta_of_vacuum_moved | (intros; apply GlobalTheory.ThetaLawMoved.theta_of_vacuum_moved <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.VacuumFixedOfFixesPureTensorsVacuaOutside
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct ComplexConjugate

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

open scoped Classical

theorem GlobalTheory.TripleAssembly.vac_fixed_of_pure_fixed : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    {n d : ℕ} {Y : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E n} {Wd : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E d} (M : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model σ Y Wd)
    (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ Y Wd) (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F) (k : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA σ Wd.J)
    (S : Finset (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F)), M.vac v ∈ GlobalTheory.WeilM.SB (Fin n × Fin d → Fv F v) →
    (∀ w ∉ S, M.vac w = Set.indicator {x | ∀ i, x i ∈ w.adicCompletionIntegers F} 1) →
    (∀ (f : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin n × Fin d)) (φ : ∀ w : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F, (Fin n × Fin d → Fv F w) → ℂ),
      (∀ w, φ w ∈ GlobalTheory.WeilM.SB (Fin n × Fin d → Fv F w)) → (∀ w ∉ S, φ w = M.vac w) →
      om (1, k) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ) = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ) →
    ∀ ψ : (Fin n × Fin d → Fv F v) → ℂ, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Acts (GlobalTheory.AdelicU.evFin F v) (om (1, k)) (M.vac v) ψ → ψ = M.vac v := by
  intro F E _ _ _ _ _ σ n d Y Wd M om v k S hvac hstd hfix ψ hψ
  let ind : ∀ w : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F, (Fin n × Fin d → Fv F w) → ℂ :=
    fun w => Set.indicator {x | ∀ i, x i ∈ w.adicCompletionIntegers F} 1

  let φ := Function.update ind v (M.vac v)
  have hφv : φ v = M.vac v := by simp [φ]
  have hφw : ∀ w, w ≠ v → φ w = ind w := fun w h => by simp [φ, h]
  have hφev : ∀ᶠ w in Filter.cofinite,
      φ w = Set.indicator {x | ∀ i, x i ∈ w.adicCompletionIntegers F} 1 := by
    rw [Filter.eventually_cofinite]
    refine (Set.finite_singleton v).subset fun w hw => ?_
    by_contra hne
    exact hw (hφw w hne)
  have hSB : ∀ w, φ w ∈ GlobalTheory.WeilM.SB (Fin n × Fin d → Fv F w) := by
    intro w
    by_cases h : w = v
    · subst h; rw [hφv]; exact hvac
    · rw [hφw w h]; exact GlobalTheory.StdVacuum.indicator_mem_SB w
  obtain ⟨f, hf⟩ := GlobalTheory.TensUniq.exists_sInf_ne_zero F (Fin n × Fin d)
  obtain ⟨r, hrinv, hrt⟩ := GlobalTheory.PureFactor.exists_rest_factor v f φ hφev
  have hupd : ∀ ψ₀, Function.update φ v ψ₀ = Function.update ind v ψ₀ :=
    fun ψ₀ => Function.update_idem _ _ _

  have hfixφ : om (1, k) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ) = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ := by
    refine hfix f φ hSB fun w hw => ?_
    by_cases h : w = v
    · subst h; exact hφv
    · rw [hφw w h, hstd w hw]
  have hpv : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens (GlobalTheory.AdelicU.evFin F v) (M.vac v) r = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ := by
    rw [hrt, hupd]
  have hRest : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rest (GlobalTheory.AdelicU.evFin F v) (M.vac v) r := by
    unfold GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rest
    refine ⟨hrinv, ?_⟩
    rw [hpv]
    exact GlobalTheory.TensUniq.pure_mem_schA f φ hSB hφev
  have key : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens (GlobalTheory.AdelicU.evFin F v) ψ r = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens (GlobalTheory.AdelicU.evFin F v) (M.vac v) r := by
    rw [← hψ r hRest, hpv, hfixφ]

  have hr0 : r 0 ≠ 0 := by
    have h1 := congrFun (hrt (fun _ => 1)) 0
    simp only [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens, one_mul] at h1
    rw [h1, hupd]
    unfold GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure
    have e1 : (fun i : Fin n × Fin d => GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F ((0 : Fin n × Fin d → AF F) i)) = 0 := by
      funext i
      show InfiniteAdeleRing.ringEquiv_mixedSpace F ((0 : Fin n × Fin d → AF F) i).1 = 0
      exact map_zero _
    have e2 : ∀ w : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F, Function.update ind v (fun _ => 1) w
        (fun i => GlobalTheory.AdelicU.evFin F w ((0 : Fin n × Fin d → AF F) i)) = 1 := by
      intro w
      by_cases h : w = v
      · subst h; simp
      · rw [Function.update_of_ne h]
        show Set.indicator {x : Fin n × Fin d → Fv F w | ∀ i, x i ∈ w.adicCompletionIntegers F} 1
          (fun i => GlobalTheory.AdelicU.evFin F w ((0 : Fin n × Fin d → AF F) i)) = 1
        rw [Set.indicator_of_mem]
        · rfl
        · simp only [Set.mem_setOf_eq, Pi.zero_apply, map_zero]
          exact fun _ => zero_mem _
    rw [e1, finprod_congr e2, finprod_one, mul_one]
    exact hf
  funext y
  have hz : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.AdelicU.evFin F v) (fun i => GlobalTheory.EmbChart.atPlace v (y i)) := by
    intro u hu
    funext i
    simp only [Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
    rw [mul_comm, GlobalTheory.EmbChart.atPlace_mul_right, hu, mul_zero, map_zero]
  have hrz : r (fun i => GlobalTheory.EmbChart.atPlace v (y i)) = r 0 := by
    simpa using hrinv 0 _ hz
  have h2 := congrFun key (fun i => GlobalTheory.EmbChart.atPlace v (y i))
  simp only [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens, GlobalTheory.EmbChart.evFin_atPlace, hrz] at h2
  exact mul_right_cancel₀ hr0 h2
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ValuationGdetKapAt
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix ValuativeRel GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.ExpansionInvariance GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.RootEx
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.TopLevelInv

section Local

variable {k : Type} [Field k]

def colMove {G : Grid k} (j : ℕ) (κ : GL (Fin (topRank G (j + 1))) k) (x : ColArgs G) : ColArgs G :=
  Function.update (Function.update x j ((κ⁻¹).val * x j)) (j + 1) (x (j + 1) * κ.val)

open Classical in

def stepVol [MeasurableSpace k] (ν : Measure k) (n : Type) [Fintype n] (c : ℕ) (n' : Type) [Fintype n'] :
    Measure (StepVar n c n' → k) := Measure.pi fun _ => ν

theorem varsVol_eq [MeasurableSpace k] (G : Grid k) (ν : Measure k) :
    varsVol G ν = Measure.pi fun j : Fin (G.m - 1) => stepVol ν (Fin (topRank G (j + 1))) (G.m - 2 - j) (Fin (topRank G j)) := rfl

variable {n : Type} [Fintype n] [DecidableEq n] {c : ℕ}

theorem gdet_of_mem_N {p : ℕ} {g : GL (n ⊕ Fin c) k} (hg : g ∈ N k n c p) : gdet g = 1 := by
  refine (show N k n c p ≤ (Matrix.GeneralLinearGroup.det (n := n ⊕ Fin c) (R := k)).ker from
    (Subgroup.closure_le _).2 fun g hg => ?_) hg
  apply Units.ext
  change g.val.det = 1
  rw [(GlobalTheory.RootEx.Model.inN_tri hg).det]
  refine Finset.prod_eq_one fun a _ => ?_
  have : g.val.toSquareBlock (lev p) a = 1 := by
    ext ⟨i, hi⟩ ⟨j, hj⟩
    simp only [Matrix.toSquareBlock_def, Matrix.of_apply]
    rw [hg i j (by rw [hi, hj]), Matrix.one_apply, Matrix.one_apply]
    simp [Subtype.ext_iff]
  rw [this, det_one]

theorem gdet_of_mem_symN {g : GL (n ⊕ Fin c) k} (hg : g ∈ symN k n c) : gdet g = 1 :=
  (show symN k n c ≤ (Matrix.GeneralLinearGroup.det (n := n ⊕ Fin c) (R := k)).ker from
    sup_le (fun _ h => gdet_of_mem_N h) fun _ h => gdet_of_mem_N h) hg

theorem gdet_embX (g : GL n k) : gdet (embX c g) = gdet g :=
  Units.ext (by
    change (fromBlocks g.val 0 0 (1 : Matrix (Fin c) (Fin c) k)).det = g.val.det
    rw [det_fromBlocks_zero₂₁, det_one, mul_one])

theorem gdet_toFrame {G : Grid k} (hs : 1 ≤ G.s) {j : ℕ} (hj : j < G.m) (g : GL (Fin (G.rank (G.m, j))) k) :
    gdet (toFrame hs hj g) = gdet g :=
  Units.ext (det_submatrix_equiv_self _ _)

theorem exists_of_mem_symPr {G : Grid k} (hs : 1 ≤ G.s) {J : G.Level} {g : G.VertexGroup} {j : ℕ} (hj : j < G.m)
    {κ : GL (Fin (topRank G j)) k} (hκ : κ ∈ symPr (conjLevel hs J g hj)) :
    ∃ u ∈ J (G.m, j), ∃ v ∈ symN k (Fin (topRank G j)) (G.m - 1 - j),
      toFrame hs hj (g (G.m, j) * u * (g (G.m, j))⁻¹) = v * embX _ κ ∧ gdet κ = gdet u := by
  obtain ⟨v, hv, _, ⟨u, hu, rfl⟩, h⟩ := hκ
  refine ⟨u, hu, v, hv, h, ?_⟩
  have := congrArg gdet h
  rw [gdet_mul, gdet_of_mem_symN hv, one_mul, gdet_embX] at this
  rw [← this]
  change gdet (toFrame hs hj (g (G.m, j) * u * (g (G.m, j))⁻¹)) = _
  rw [gdet_toFrame, gdet_mul, gdet_mul, mul_right_comm, ← gdet_mul, mul_inv_cancel]
  simp

end Local

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T}

def movedPt (t : T) (j : ℕ) (hj : j + 1 < D.R.m) (g : FinPt G (.top (j + 1)))
    (x : ∀ j' : Fin D.R.m, WO (G.pS (.top t j' : Pair T)) (G.pT (.top t j' : Pair T))) :
    ∀ j' : Fin D.R.m, WO (G.pS (.top t j' : Pair T)) (G.pT (.top t j' : Pair T)) :=
  Function.update (Function.update x ⟨j, by omega⟩ (actO _ _ 1⁻¹ (g : GA D (G.V (.top (j + 1))))⁻¹ (x ⟨j, by omega⟩)))
    ⟨j + 1, hj⟩ (actO _ _ (g : GA D (G.V (.top (j + 1))))⁻¹ 1⁻¹ (x ⟨j + 1, hj⟩))

theorem movedFn_apply (S : GridChoice W U) {t : T} (d : PureDat G t) (j : ℕ) (hj : j + 1 < D.R.m) (g : FinPt G (.top (j + 1)))
    (x : ∀ j' : Fin D.R.m, WO (G.pS (.top t j' : Pair T)) (G.pT (.top t j' : Pair T))) (j' : Fin D.R.m) :
    movedFn S d j hj g j' (x j') = (d.1 j').fn (movedPt t j hj g x j') := by
  rcases eq_or_ne j' ⟨j + 1, hj⟩ with rfl | h1
  · simp only [movedFn, movedPt, Function.update_self]
  rcases eq_or_ne j' ⟨j, by omega⟩ with rfl | h2
  · simp only [movedFn, movedPt, Function.update_of_ne h1, Function.update_self]
  · simp only [movedFn, movedPt, Function.update_of_ne h1, Function.update_of_ne h2]

def kapAt (S : GridChoice W U) (t : T) (j : ℕ) (hj : j + 1 < D.R.m) (k : FinPt G (.top (j + 1))) (w : Pl D.host.E) :
    GL (Fin (topRank (locGrid G t w) (j + 1))) (Kw w) :=
  inBasis (topRank_eq G t w hj.le) (S.βp (j + 1)) w (finG (G.V (.top (j + 1))) k)

theorem kapAt_mem (S : GridChoice W U) {t : T} {Φ : G.Datum} {β : CosFam G t} {j : ℕ} (hj : j + 1 < D.R.m)
    {k : FinPt G (.top (j + 1))} (hk : finG (G.V (.top (j + 1))) k ∈ S.levTop t Φ β (j + 1) hj) (w : locPl G t) :
    kapAt S t j hj k w ∈ (S.term t Φ β w).pr (j + 1) j.succ_pos hj :=
  Subgroup.mem_iInf.1 (Subgroup.mem_inf.1 hk).1 w

theorem givenLevel_col (t : T) (w : Pl D.host.E) (j : ℕ) : givenLevel G t w (D.R.m, j + 1) = KO (Kw w) _ := by
  have key : ∀ i, 0 < i → givenLevel G t w (i, j + 1) = KO (Kw w) _ := by
    rintro (_ | i) h
    · omega
    · rfl
  exact key _ (by have := D.R.two_le_m; omega)

theorem valuation_gdet_kapAt (S : GridChoice W U) {t : T} {Φ : G.Datum} {β : CosFam G t} {j : ℕ} (hj : j + 1 < D.R.m)
    {k : FinPt G (.top (j + 1))} (hk : finG (G.V (.top (j + 1))) k ∈ S.levTop t Φ β (j + 1) hj) (w : locPl G t) :
    valuation (Kw w.1) (gdet (kapAt S t j hj k w) : Kw w.1) = 1 := by
  obtain ⟨u, hu, -, -, -, h⟩ := exists_of_mem_symPr (G := locGrid G t w) one_le_sLen hj (kapAt_mem S hj hk w)
  rw [h]
  exact valuation_gdet_of_mem_KO (givenLevel_col t w.1 j ▸ hu)

end GlobalTheory.TopLevelInv

end
end

