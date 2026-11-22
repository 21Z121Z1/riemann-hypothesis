import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsCoreLat
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0017
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0008
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0012
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.WeilSiegelFormulaUnitary
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitaryConvergent
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0005
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0003
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0398
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0399
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0513
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0170
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0100
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0083
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SmulEqZeroOfInf
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0549
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0026
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0405
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0523
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0406
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0409
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0423
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0790
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0747
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0615
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.TwistPlacesOffPrimeQZero
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0533
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0004
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0006
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0019
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ToricSymbols
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0570
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0182
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsRealFam
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCombAt
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0296
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RepresentationAtEveryPlace
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0791
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0521
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0547
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0006
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.EpsVEqOne
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0123
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0003
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.HalfLinearCocycle
import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.LocalIntegralGL
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHeightLeTwoMulQuotHeight
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0010
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CuspAlongOfPairLifts
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0606

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsCosetFockVacuumDatum
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.SepRows GlobalTheory.CoreOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Chain (IsVacVec ptOf)
open GlobalTheory.PairLift (adjO)
open scoped ComplexConjugate

noncomputable section

namespace GlobalTheory.CosDatum

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem cA_cA₀ {D : D7} (z : AE D) : cA D (cA D z) = z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a x => show a ⊗ₜ[D.host.F] star (star x) = _; rw [star_star]
  | add x y hx hy => rw [map_add, map_add, hx, hy]

theorem latO_le_true {D : D7} (S T : HSp D) (LS : Set (Fin S.rank → D.host.E)) (LT : Set (Fin T.rank → D.host.E))
    (P : HeightOneSpectrum (𝓞 D.host.F) → Prop) : latO S T LS LT P ≤ latO S T LS LT fun _ => True := by
  apply AddSubgroup.closure_mono
  rintro w ⟨α, hα, -, rest⟩
  exact ⟨α, hα, fun v h => (h trivial).elim, rest⟩

theorem isLatVac_mono {D : D7} {m n : ℕ} {hs : Mx D m n → (Mx D m n → ℂ) → (Mx D m n → ℂ)} {Λ Λ' : AddSubgroup (Mx D m n)}
    (h : Λ' ≤ Λ) {f : Mx D m n → ℂ} (hf : IsLatVac hs Λ f) : IsLatVac hs Λ' f :=
  ⟨fun u hu => hf.1 u (h hu), fun e he u hu hh => hf.2 e he u (h hu) hh⟩

theorem addChar_ne_zero {A : Type} [AddGroup A] (ψ : AddChar A ℂ) (a : A) : ψ a ≠ 0 := fun h => by
  have := ψ.map_add_eq_mul a (-a)
  rw [add_neg_cancel, ψ.map_zero_eq_one, h, zero_mul] at this
  exact one_ne_zero this

end GlobalTheory.CosDatum

namespace GlobalTheory.CoreOnto

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open GlobalTheory.CosDatum in

theorem datumEx : DatumEx := by
  intro D hq T L μ0 hL sc G W M hM i hi r r' hr hr' S S' MM MM' x₀ hx₀
  have hψ : IsStdChar D W.ψ (-1) := W.ψ_std
  have hθ : IsInfFam W.θ := W.θ_is
  have hEx : ExchLaw D := GlobalTheory.T.adjointExchange_laws_thetaHeisenberg D
  have hLE : LatExch := GlobalTheory.T.coreChain_adjoint_latticeExchange
  have hadj := GlobalTheory.AdjLawPf.adjLaw D W.ψ hψ (G.V (.core i)) (G.V (.core (i + 1)))
  obtain ⟨e, he, -⟩ := W.cosVec_is
  obtain ⟨f₀, hf₀⟩ := GlobalTheory.T.thetaChain_unitVacuum_otherLattices_exists D hq T L μ0 hL sc G W M hM i hi r r' S S' MM MM'
  obtain ⟨R, hR1, hR2, hR3, hR4⟩ := GlobalTheory.T.exists_representatives_half_quotient_pairing_trivial_depthLattice D hq T L μ0 hL sc G W M hM i hi e he
  have hxi := GlobalTheory.T.corePair_integralPoint_pairs_trivially_half D hq T L μ0 hL sc G W M hM i hi e he x₀ hx₀
  have hhalf : ∀ z ∈ R, IsHalf e (adjO (G.V (.core i)) (G.V (.core (i + 1))) z) := fun z hz => by
    have := hadj.half _ z (hR1 z hz).1
    rwa [cA_cA₀] at this
  have hfin : ∀ z ∈ R, (adjO (G.V (.core i)) (G.V (.core (i + 1))) z).map (infPart D) = 0 := fun z hz =>
    GlobalTheory.T.infinitePart_eq_zero_of_isHalf_idempotentSum _ e he _ (Or.inl (hhalf z hz))
  let c : WO (G.pS (.core i)) (G.pT (.core i)) → ℂ :=
    fun z => W.ψ (-symplO (G.pS (.core i)) (G.pT (.core i)) (e • x₀.map (incA D)) z)
  let f : WO r.sp r'.sp → ℂ :=
    ∑ z ∈ R, c z • heisO W.ψ r.sp r'.sp (adjO (G.V (.core i)) (G.V (.core (i + 1))) z) f₀
  have hexs : ∀ g : WO r.sp r'.sp → ℂ,
      exch (G.V (.core i)) (G.V (.core (i + 1)))
        (∑ z ∈ R, c z • heisO W.ψ r.sp r'.sp (adjO (G.V (.core i)) (G.V (.core (i + 1))) z) g) =
      ∑ z ∈ R, c z • heisO W.ψ (G.pS (.core i)) (G.pT (.core i)) z (exch (G.V (.core i)) (G.V (.core (i + 1))) g) := by
    intro g
    funext x
    have h2 := fun z : WO (G.pS (.core i)) (G.pT (.core i)) =>
      congrFun ((hEx W.ψ (G.V (.core i)) (G.V (.core (i + 1))) hψ).2.1 z g) x
    show (∑ z ∈ R, c z • heisO W.ψ r.sp r'.sp (adjO (G.V (.core i)) (G.V (.core (i + 1))) z) g)
      (adjO (G.V (.core i)) (G.V (.core (i + 1))) x) = _
    rw [Finset.sum_apply, Finset.sum_apply]
    refine Finset.sum_congr rfl fun z _ => ?_
    rw [Pi.smul_apply, Pi.smul_apply, h2 z]
    rfl
  have hf₀th : IsThetaFunO W.ψ r.sp r'.sp f₀ := hf₀.2.theta
  have hcomb := GlobalTheory.T.isThetaFunction_finiteHeisenbergCombination W.ψ W.θ r.sp r'.sp hψ hθ f₀ hf₀th R c _ hfin
  have hex0 : exch (G.V (.core i)) (G.V (.core (i + 1))) f₀ ≠ 0 := by
    intro h0
    apply GlobalTheory.SeeSaw.Inh.vac_ne_zero hf₀
    funext y
    obtain ⟨x, rfl⟩ := (hEx W.ψ _ _ hψ).2.2.2.1.2 y
    exact congrFun h0 x
  have hRne : ∃ z ∈ R, c z ≠ 0 := by
    obtain ⟨y', hy', -⟩ := hR2 0 (fun _ _ => mul_zero _) (fun u _ => by
      have h00 : symplO (G.pS (.core i)) (G.pT (.core i)) u 0 = 0 := by unfold symplO hO; simp
      rw [h00, AddChar.map_zero_eq_one])
    exact ⟨y', hy', addChar_ne_zero _ _⟩
  refine ⟨f, ⟨hcomb.1, ?_, fun τ => GlobalTheory.T.isFockVacuumAt_finiteHeisenbergCombination W.ψ W.θ r.sp r'.sp hψ hθ _ τ f₀ hf₀th (hf₀.2.fock τ) R c _ hfin⟩,
    ?_, fun φ => ?_⟩
  · intro h0
    have h2 : exch (G.V (.core i)) (G.V (.core (i + 1))) f = 0 := by rw [h0]; rfl
    refine GlobalTheory.T.sum_heisenbergTranslates_latticeVacuum_ne_zero W.ψ (G.pS (.core i)) (G.pT (.core i)) (G.latS (.core i)) (G.latT (.core i)) G.pl.W0 e he R hR4
      _ (GlobalTheory.T.adjointExchange_isLatticeVacuum_coreChain D hq T L μ0 hL sc G W M hM hEx hLE i hi r r' hr hr' f₀ hf₀.2.lat) hex0 c hRne ?_
    rw [← hexs f₀]
    exact h2
  · show IsLatVac _ _ _
    refine GlobalTheory.T.isLatticeVacuum_sum_heisenbergTranslates W.ψ r.sp r'.sp _ f₀ (isLatVac_mono (latO_le_true _ _ _ _ _) hf₀.2.lat) R c _ ?_
    intro z hz u hu
    rw [GlobalTheory.T.half_vector_symplectic_orthogonal D hq T L μ0 hL sc G W M hM e he r.sp r'.sp _ _ u hu _ (hhalf z hz), AddChar.map_zero_eq_one]
  · have hpt : ptOf W.ψ W.θ MM MM' f φ = ∑ z ∈ R, c z • heisO W.ψ r.sp r'.sp
        (adjO (G.V (.core i)) (G.V (.core (i + 1))) z) (ptOf W.ψ W.θ MM MM' f₀ φ) :=
      hcomb.2 (cart MM) (onb MM) (cart MM') (onb MM') φ
    have hfl := GlobalTheory.T.isTheta_isLatticeVacuum_fockPureTensor W.ψ W.θ r.sp r'.sp hψ hθ _ _ _ f₀ hf₀th hf₀.2.lat (cart MM) (onb MM) (cart MM') (onb MM') φ
    have hgl := GlobalTheory.T.adjointExchange_isLatticeVacuum_coreChain D hq T L μ0 hL sc G W M hM hEx hLE i hi r r' hr hr' _ hfl.2
    have hth : IsThetaFunO W.ψ r.sp r'.sp (ptOf W.ψ W.θ MM MM' f φ) := by
      rw [hpt]; exact (GlobalTheory.T.isThetaFunction_finiteHeisenbergCombination W.ψ W.θ r.sp r'.sp hψ hθ _ hfl.1 R c _ hfin).1
    have hth' := (((GlobalTheory.T.selfDualLattice_changeOfLattice_laws D).2.2 W.ψ (G.V (.core i)) (G.V (.core (i + 1))) r r').1 _).1 hth
    have hΦth := ((hEx W.ψ (G.V (.core i)) (G.V (.core (i + 1))) hψ).1 _).1 hth'
    have hΦ := hexs (ptOf W.ψ W.θ MM MM' f₀ φ)
    rw [← hpt] at hΦ
    rw [hΦ] at hΦth ⊢
    refine ⟨⟨hΦth, GlobalTheory.T.isLatticeVacuum_sum_heisenbergTranslates W.ψ _ _ _ _ (isLatVac_mono (Λ' := depLat G (.core i)) (fun u hu => hu.1) hgl) R c (fun z => z)
      (fun z hz => (hR1 z hz).2)⟩, ?_⟩
    intro e' he' y hy hyd
    obtain rfl := GlobalTheory.T.idempotentSum_over_finite_places_unique _ _ _ he he'
    exact GlobalTheory.T.cosetSum_heisenberg_isEigenvector W.ψ _ _ (G.latS (.core i)) (G.latT (.core i)) G.pl.W0 e he (depLat G (.core i)) R _ hR1 hR2 hR3 hxi
      _ hgl y hy hyd

end GlobalTheory.CoreOnto

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsDegreeBoundFourierLifted
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx MeasureTheory

noncomputable section

theorem GlobalTheory.RealProj.avg_monomial : ∀ {D : D7} {T : Type} [Finite T] {L : LevCh D T} {μ₀ : T} {sc : Consts} {G : GridData L sc} {W : G.Weil}
    {i j : Fin D.R.m} {A A' WW : HSp D} {X : Tri T A A' WW}, GlobalTheory.FunPr.Hypotheses₂ → (∀ D, GlobalTheory.NormSum.Inp D) → L.Is μ₀ →
    IsBottomTri W i j X →
    ∃ n : D.what₂.Tau → ℕ, ∀ (κ : Measure (GinfC A')), κ.IsMulLeftInvariant → IsProbabilityMeasure κ →
      ∀ (t : T), ∀ x ∈ GfC A', ∀ h ∈ GfC WW, ∀ k : FVar D WW.rank A'.rank →₀ ℕ,
        ∃ (m : ℕ) (r : Fin m → ℂ) (U : Fin m → GlobalTheory.NormSum.Tup D A'.rank WW.rank n), (∀ p, IsAlgebraic ℚ (r p)) ∧
          ∫ g, X.ker' W.ψ W.θ t (MvPolynomial.monomial k 1) h (x * (g : GA D A')) ∂κ =
            ∑ p, r p * X.ker' W.ψ W.θ t (GlobalTheory.NormSum.minorPol D (U p)) h x := by
  intro D T _ L μ₀ sc G W i j A A' WW X hPr hInp hL hB
  obtain ⟨m, ρ, hρm, hρs, hact⟩ := GlobalTheory.T.exists_archimedean_unitary_weights hPr hInp hL hB
  obtain ⟨n, hn⟩ := GlobalTheory.T.average_det_char_monomial_eq_sum_prod_minors (ι := D.what₂.Tau) A'.rank WW.rank m
  refine ⟨n, fun κ hκ hκp t x hx h hh k => ?_⟩
  let Λ : GlobalTheory.MinorFrame.Pol D.what₂.Tau WW.rank A'.rank →ₗ[ℂ] ℂ :=
    (LinearMap.proj (R := ℂ) (φ := fun _ : WO A' WW => ℂ) 0).comp
      ((X.ω' t (x, h)).comp (pureTensorO W.ψ W.θ A' WW X.rA'.s X.rW.s X.rA'.B X.rW.B (X.f' t)))
  have hΛ : ∀ P, Λ P = X.ker' W.ψ W.θ t P h x := fun P => rfl
  obtain ⟨M, r, U, hr, hI⟩ := hn κ hκp hκ ρ hρm hρs Λ k
  refine ⟨M, r, U, hr, ?_⟩
  have e : (fun g : GinfC A' => X.ker' W.ψ W.θ t (MvPolynomial.monomial k 1) h (x * (g : GA D A'))) =
      fun g => (∏ τ, (ρ g τ : Matrix (Fin A'.rank) (Fin A'.rank) ℂ).det ^ (m τ)) *
        Λ (GlobalTheory.MinorFrame.colSub (fun τ => (ρ g τ : Matrix (Fin A'.rank) (Fin A'.rank) ℂ)) (MvPolynomial.monomial k 1)) := by
    funext g; rw [hact t x hx h hh g, hΛ]
  rw [e, hI]
  rfl

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsPeriodGroupPointLiftingRowGroupLocalElemen
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section

namespace GlobalTheory.RowLift
open GlobalTheory.RowRep
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

variable {D : D7}

theorem suppAt_conj {V : HSp D} {e : AE D} {y : GA D V} (h : SuppAt e V y) (δ : GA D V) : SuppAt e V (δ * y * δ⁻¹) := by
  have hs : (e + cA D e) • (mt V y - 1) = mt V y - 1 := Matrix.ext fun i j => h i j
  have hδ : mt V δ * mt V δ⁻¹ = 1 := by rw [← GlobalTheory.MixModel.mt_mul, mul_inv_cancel, GlobalTheory.MixModel.mt_one]
  have key : mt V (δ * y * δ⁻¹) - 1 = mt V δ * (mt V y - 1) * mt V δ⁻¹ := by
    rw [GlobalTheory.MixModel.mt_mul, GlobalTheory.MixModel.mt_mul, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, hδ]
  have h2 : (e + cA D e) • (mt V δ * (mt V y - 1) * mt V δ⁻¹) = mt V δ * (mt V y - 1) * mt V δ⁻¹ := by
    rw [← Matrix.smul_mul, ← Matrix.mul_smul, hs]
  intro i j
  rw [key]
  exact congrFun (congrFun h2 i) j

variable {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc}

theorem hasLoc_conj (B : Frames G) (t : T) {j : ℕ} (hj : j ≤ D.R.m) {y : GA D (G.V (.grid D.R.m j))}
    {g : ∀ w : locPl G t, GL (Fin ((locGrid G t w.1).rank (D.R.m, j))) (Kw w.1)} (h : HasLoc t B hj y g)
    (δ : GA D (G.V (.grid D.R.m j))) :
    HasLoc t B hj (δ * y * δ⁻¹) (fun w => locAt B t w.1 j hj δ * g w * (locAt B t w.1 j hj δ)⁻¹) := by
  obtain ⟨e, he, hs, hl⟩ := h
  refine ⟨e, he, suppAt_conj hs δ, fun w => ?_⟩
  change locAt B t w.1 j hj (δ * y * δ⁻¹) = _
  rw [map_mul, map_mul, map_inv]
  exact congrArg (fun z => locAt B t w.1 j hj δ * z * (locAt B t w.1 j hj δ)⁻¹) (hl w)

theorem conj_rowR' {k : Type} [Field k] {Γ : GlobalTheory.SplitFlip.Grid k} (hs : 1 ≤ Γ.s) {j : ℕ} (hj : j < Γ.m)
    {x y : GL (Fin (Γ.rank (Γ.m, j))) k} (hy : ∃ f, (toFrame hs hj y).val = diagonal f) (hx : x ∈ rowR hs hj) :
    y * x * y⁻¹ ∈ rowR hs hj := by
  obtain ⟨f, hf⟩ := hy
  have hy' : ∃ f, (toFrame hs hj y⁻¹).val = diagonal f :=
    ⟨Ring.inverse f, by rw [map_inv, Matrix.coe_units_inv, hf, Matrix.inv_diagonal]⟩
  have := conj_rowR hs hj (g := fun _ => 1) hy' hx
  have e1 : GlobalTheory.SplitFlip.diagGL (fun _ => (1 : kˣ)) = (1 : GL (Fin (Γ.rank (Γ.m, j))) k) :=
    Units.ext (by rw [GlobalTheory.SplitFlip.diagGL_val]; exact diagonal_one)
  rwa [e1, mul_one, inv_inv] at this

theorem sgn_diag {k : Type} [Field k] {Γ : GlobalTheory.SplitFlip.Grid k} (hs : 1 ≤ Γ.s) {j : ℕ} (hj : j < Γ.m)
    (c : Fin (Γ.rank (Γ.m, j)) → kˣ) : ∃ f, (toFrame hs hj (GlobalTheory.SplitFlip.diagGL c)).val = diagonal f := by
  have h : topRank Γ j + (Γ.m - 1 - j) = Γ.rank (Γ.m, j) := by have := topRank_add hs j; omega
  exact ⟨_, submatrix_diagonal_equiv (fun i => (c i : k)) (frame h)⟩

end GlobalTheory.RowLift

open GlobalTheory.RowLift GlobalTheory.RowRep in

theorem GlobalTheory.RowLift.lift_rowR : Big fun {D} _ _ _ _ _ _ _ _ _ _ _ ch => ∀ (s : ℤˣ) t, ∀ j ∈ idx D, ∀ (hj : j ≤ D.R.m) (hj' : j < D.R.m)
    (δ : GA D (ch.G.V (.grid D.R.m j))), IsTilt ch.G j δ →
    ∀ l : ∀ w : locPl ch.G t, GL (Fin ((locGrid ch.G t w.1).rank (D.R.m, j))) (Kw w.1),
      (∀ w, l w ∈ rowR (G := locGrid ch.G t w.1) one_le_sLen (j := j) hj') →
      ∃ y, HasLoc t ch.S.B hj y (fun w => sgnAt ch.G t s w.1 j * l w * (sgnAt ch.G t s w.1 j)⁻¹) ∧
        δ * y * δ⁻¹ ∈ rowGrp ch.G j := by
  obtain ⟨C1, hJ⟩ := GlobalTheory.T.mem_fourierJacobiGroup_of_local_lattice_matrices
  obtain ⟨C2, hB⟩ := GlobalTheory.T.mem_besselGroup_of_local_lattice_matrices
  refine ⟨max C1 C2, fun ε CF hCF => ?_⟩
  obtain ⟨x1, hx1⟩ := hJ ε CF (le_trans (le_max_left _ _) hCF)
  obtain ⟨x2, hx2⟩ := hB ε CF (le_trans (le_max_right _ _) hCF)
  refine ⟨max x1 x2, fun D large₂ hε hx Γ _ _ Pl0 T A Ks _ _ _ R F hS ch hch hsc => ?_⟩
  intro s t j hjI hj hj' δ hδ l hl
  obtain ⟨y, hy⟩ := exists_hasLoc hS.core.lev ch.S.B t hj (fun w => sgnAt ch.G t s w.1 j * l w * (sgnAt ch.G t s w.1 j)⁻¹)
  refine ⟨y, hy, ?_⟩
  have hc := hasLoc_conj ch.S.B t hj hy δ
  have hm : ∀ w : locPl ch.G t, locAt ch.S.B t w.1 j hj δ * (sgnAt ch.G t s w.1 j * l w * (sgnAt ch.G t s w.1 j)⁻¹) *
      (locAt ch.S.B t w.1 j hj δ)⁻¹ ∈ rowR (G := locGrid ch.G t w.1) one_le_sLen (j := j) hj' := fun w =>
    conj_rowR' one_le_sLen hj' (locAt_tilt ch.S.toGridChoice (Set.mem_univ t) w.2 hj hj' hδ)
      (conj_rowR' one_le_sLen hj' (sgn_diag one_le_sLen hj' _) (hl w))
  unfold rowGrp
  split_ifs with h1 h2
  · exact hx1 D large₂ hε (le_trans (le_max_left _ _) hx) Γ Pl0 T A Ks R F hS ch hch hsc t j _ hjI hj hj' _
      (by have := (idx_le hjI); omega) _ _ hc hm
  · exact hx2 D large₂ hε (le_trans (le_max_right _ _) hx) Γ Pl0 T A Ks R F hS ch hch hsc t j _ hjI hj hj' h2 _ _ hc hm
  · exfalso; have := idx_le hjI; omega
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsUnitModulusLocalFactorStatement
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

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_unit_modulus_local_factor : GlobalTheory.FunPr.Hypotheses₂ → (∀ D, GlobalTheory.NormSum.Inp D) → ∀ {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type}
    {A : FamIn D.what₂.LL Γ Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks}
    (ch : Choice R), ch.Is → ∀ (p : Pair T), DefPair D.R.m p → ∀ (x : FinPt ch.G p.small) (y : FinPt ch.G p.big),
    ∃ κ : ℂ, Mod1All κ ∧
    (∀ (q : ℕ) [Fact q.Prime], EqAt D q (GlobalTheory.SumSize.latAt ch.S.toGridChoice p.small x) (stdL D _) →
      EqAt D q (GlobalTheory.SumSize.latAt ch.S.toGridChoice p.big y) (stdL D _) → ∀ lam : Qbar →+* ℂ_[q], ‖lamC lam κ‖ = 1) ∧
    ∀ k : FVar D (ch.G.pT p).rank (ch.G.pS p).rank →₀ ℕ,
      fockIn ch.W ch.S.N.frC p (ch.W.om p (ch.G.toPair p ((x * ch.S.N.u p.small : FinPt ch.G p.small) : Formalism.L2.Theta.GA D (ch.G.V p.small)) ((y * ch.S.N.u p.big : FinPt ch.G p.big) : Formalism.L2.Theta.GA D (ch.G.V p.big))) (ch.S.Z.vac p))
        (MvPolynomial.monomial k 1) 0 = ch.S.Z.c0 p * opp p ((k.prod fun v e => period ch.S.Z.δ v.1 ^ e) *
          Formalism.MainNotions.GL3Theta.applyAt0 D (MvPolynomial.monomial k 1) fun z => κ * Iop D (tor0 D D.host.ccK ch.S.Z.δ) (La0 D (tor0 D D.host.ccK ch.S.Z.δ) _ _) (Formalism.MainNotions.TaylorLogMetric.La D (tor0 D D.host.ccK ch.S.Z.δ) (GlobalTheory.MovedDict.srcLat ch.S.toGridChoice p x y) (GlobalTheory.MovedDict.tgtLat ch.S.toGridChoice p x y)) (ch.S.Z.e0 p) z) := by
  first | exact @GlobalTheory.MovedDict.movedVacuum_kappa | exact GlobalTheory.MovedDict.movedVacuum_kappa | (intros; apply GlobalTheory.MovedDict.movedVacuum_kappa <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FourierJacobiStepPiecesAdmissibleSplitsStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fourierJacobi_step_pieces_admissible_splits : OnStd fun {D} _ _ {sc} {G} W F => ∀ σ (h : 2 * (σ + 1) + 2 ≤ D.R.m) (h' : 2 * σ + 2 ≤ D.R.m), (pcFB W F σ h h').Is (F.dJ (σ + 1) h) (F.dB σ h') (xFB F σ h') W.ψ ∧ Splits (F.dJ (σ + 1) h) (F.dB σ h') (pcFB W F σ h h') (xFB F σ h') 0 W.ψ (latRow G (2 * σ + 2)) := by
  first | exact @GlobalTheory.AscFin.piecesFB_is_and_splits | exact GlobalTheory.AscFin.piecesFB_is_and_splits | (intros; apply GlobalTheory.AscFin.piecesFB_is_and_splits <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FrameLatticePointsEqIntegralMatricesLargeDepthStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.FlatPlace GlobalTheory.LocMod GlobalTheory.SplitWeil

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.frameLattice_points_eq_integralMatrices_largeDepth : Big fun ch => LatP ch := by
  first | exact @GlobalTheory.FlatPlace.big_latP | exact GlobalTheory.FlatPlace.big_latP | (intros; apply GlobalTheory.FlatPlace.big_latP <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HalfLatticeIffFrameAdjointIsIntegralMatrixStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.LiftRows
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.AdelicScalar
open Formalism.L2.DIV (kP Pl LevelP)
open Classical

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.halfLattice_iff_frameAdjoint_isIntegralMatrix : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.PlaceModels D → ∀ i t σ s P cμ cη m ω BW f₀ f c io, GlobalTheory.LiftRows.IsLiftDataC R F i t σ s P cμ cη m ω BW f₀ f c io → ∀ e : AE D, IsIdemSum e (R.Pg ∪ R.Q t) → ∀ x : WO (Vc D i) (Wc D i), IsHalf (cA D e) x →
  (x ∈ latO (Vc D i) (Wc D i) (R.ΛV i) (R.ΛW i) (fun _ => True) ↔ IsIntM (frMapAdj (Vc D i) (Wc D i) (R.βV i) (R.βW i) x)) := by
  first | exact @GlobalTheory.HalfLatFrames.halfLat_iff_isIntM | exact GlobalTheory.HalfLatFrames.halfLat_iff_isIntM | (intros; apply GlobalTheory.HalfLatFrames.halfLat_iff_isIntM <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegrableOnQuotHeightPowMulNorm
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.CuspFormApprox

variable {D : D7} {V : HSp D} {μ : Measure (GA D V)} {𝓕 : Set (GA D V)}

theorem integrableOn_one (hμ : μ.IsHaarMeasure) (h𝓕 : IsFundamentalDomain (GQ V) 𝓕 μ) :
    IntegrableOn (fun _ => (1 : ℝ)) 𝓕 μ := by
  simpa using GlobalTheory.Size.integrableOn_inv_quotHeight_pow (V := V) 0 hμ h𝓕

theorem integrableOn_of_le (hμ : μ.IsHaarMeasure) (h𝓕 : IsFundamentalDomain (GQ V) 𝓕 μ) {f : GA D V → ℝ}
    (hf : Continuous f) (h0 : ∀ g, 0 ≤ f g) {C : ℝ} (hC : ∀ g, f g ≤ C) :
    IntegrableOn f 𝓕 μ ∧ ∫ g in 𝓕, f g ∂μ ≤ C * ∫ _g in 𝓕, (1 : ℝ) ∂μ := by
  have h1 := integrableOn_one hμ h𝓕
  have hC' : IntegrableOn (fun _ => C * (1 : ℝ)) 𝓕 μ := h1.const_mul C
  have hi : IntegrableOn f 𝓕 μ := by
    refine Integrable.mono' hC' hf.aestronglyMeasurable (.of_forall fun g => ?_)
    rw [Real.norm_of_nonneg (h0 g), mul_one]
    exact hC g
  refine ⟨hi, ?_⟩
  rw [← integral_const_mul]
  exact integral_mono_of_nonneg (.of_forall fun g => h0 g) hC' (.of_forall fun g => by simpa using hC g)

theorem integrableOn_quotHeight_pow_mul_norm (hP : GlobalTheory.Published.CuspRapidDecay) {θ : InfFam D} (hθ : IsInfFam θ)
    {N : GlobalTheory.Grid.Node D} {μ : Measure (GA D N.V)} {𝓕 : Set (GA D N.V)} (hμ : μ.IsHaarMeasure)
    (h𝓕 : IsFundamentalDomain (GQ N.V) 𝓕 μ) {φ : GA D N.V → ℂ} (hφ : GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.IsCuspOfType θ N φ) (b : ℕ) :
    IntegrableOn (fun g => GlobalTheory.Grow.quotHeight N.V g ^ b * ‖φ g‖) 𝓕 μ := by
  have hr := (GlobalTheory.Size.rapidDecSm_of_cuspForm hP hθ hφ.1 hφ.2.1).rapidDec
  obtain ⟨C, hC⟩ := hr.decay b
  refine (integrableOn_of_le hμ h𝓕 (((GlobalTheory.Grow.continuous_quotHeight N.V).pow b).mul hr.continuous.norm)
    (fun g => mul_nonneg (pow_nonneg (GlobalTheory.Grow.quotHeight_pos N.V g).le b) (norm_nonneg _)) (C := C)
    (fun g => by rw [mul_comm]; exact hC g)).1

theorem weighted_uniform_approx_cusp_forms {θ : InfFam D} {N : GlobalTheory.Grid.Node D} {μ : Measure (GA D N.V)} {𝓕 : Set (GA D N.V)}
    (hμ : μ.IsHaarMeasure) (h𝓕 : IsFundamentalDomain (GQ N.V) 𝓕 μ) {φ : GA D N.V → ℂ} (hc : Continuous φ) (b : ℕ)
    (hu : ∀ ε : ℝ, 0 < ε → ∃ (n : ℕ) (F : Fin n → N.Maps) (v : Fin n → SmT N.M), (∀ l, F l ∈ N.Cusp θ) ∧
      ∀ g, ‖φ g - ∑ l, F l (v l) g‖ * GlobalTheory.Grow.quotHeight N.V g ^ b ≤ ε) :
    ∀ ε : ℝ, 0 < ε → ∃ (n : ℕ) (Fs : Fin n → N.Maps) (vs : Fin n → SmT N.M), (∀ k, Fs k ∈ N.Cusp θ) ∧
      IntegrableOn (fun g => GlobalTheory.Grow.quotHeight N.V g ^ b * ‖(∑ k, Fs k (vs k) g) - φ g‖) 𝓕 μ ∧
      ∫ g in 𝓕, GlobalTheory.Grow.quotHeight N.V g ^ b * ‖(∑ k, Fs k (vs k) g) - φ g‖ ∂μ ≤ ε := by
  intro ε hε
  set I := ∫ _g in 𝓕, (1 : ℝ) ∂μ
  have hI : 0 ≤ I := integral_nonneg fun _ => zero_le_one
  obtain ⟨n, F, v, hF, h⟩ := hu (ε / (I + 1)) (div_pos hε (by linarith))
  have hcs : Continuous fun g => ∑ l, F l (v l) g := by
    have := continuous_finset_sum Finset.univ fun l _ =>
      GlobalTheory.BaseChain.multT_apply_continuous θ N.M ∅ 1 (F l) (hF l) (v l)
    simpa using this
  have hcf : Continuous fun g => GlobalTheory.Grow.quotHeight N.V g ^ b * ‖(∑ l, F l (v l) g) - φ g‖ :=
    ((GlobalTheory.Grow.continuous_quotHeight N.V).pow b).mul (hcs.sub hc).norm
  obtain ⟨hi, hle⟩ := integrableOn_of_le hμ h𝓕 hcf
    (fun g => mul_nonneg (pow_nonneg (GlobalTheory.Grow.quotHeight_pos N.V g).le b) (norm_nonneg _)) (C := ε / (I + 1))
    (fun g => by rw [mul_comm, norm_sub_rev]; exact h g)
  refine ⟨n, F, v, hF, hi, hle.trans ?_⟩
  rw [div_mul_eq_mul_div, div_le_iff₀ (by linarith)]
  nlinarith

end GlobalTheory.CuspFormApprox

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LastRowLatticesGoodPositionLargeDepthStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lastRowLatticesGoodPosition_large_depth : Big fun ch => ShapeAt ch := by
  first | exact @GlobalTheory.RowShape.shapeAt_big | exact GlobalTheory.RowShape.shapeAt_big | (intros; apply GlobalTheory.RowShape.shapeAt_big <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LastRowUnfoldingBasicHypothesesStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lastRow_unfolding_basicHypotheses : Big fun ch => BasicAt ch := by
  first | exact @GlobalTheory.RowBasic.basicAt | exact GlobalTheory.RowBasic.basicAt | (intros; apply GlobalTheory.RowBasic.basicAt <;> assumption)
end

