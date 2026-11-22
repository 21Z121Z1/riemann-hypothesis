import Mathlib
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
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0558
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0078
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1516
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0916
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0964
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0129
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0310
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0028
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ChainParSucc
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DiscreteSeriesHarishChandraModuleAdmissible
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0165
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0168
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0017
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0018
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
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0567
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0570
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0421
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0042
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0053
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0013
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0026
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0001
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0028
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.StandardMaximalParabolic
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CentralizerTensorForms
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1889
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SandwichedFlipRouteThroughSmallEqInvConstRouteBi
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0544

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RealPointActsOnVacuumByAlgebraicScalar
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx MeasureTheory

noncomputable section

namespace GlobalTheory.RealScalarAlg

open Matrix
open scoped Kronecker ComplexOrder

open GlobalTheory.Grid (neg sgn ofSgn)

variable {D : D7}

def EIn {m n : Type} (M : Matrix m n ℂ) : Prop := ∀ i j, M i j ∈ algebraicClosure ℚ ℂ

section Entries

variable {ι κ ι' κ' : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

theorem EIn.add {M N : Matrix ι κ ℂ} (hM : EIn M) (hN : EIn N) : EIn (M + N) := fun i j => add_mem (hM i j) (hN i j)

theorem EIn.sub {M N : Matrix ι κ ℂ} (hM : EIn M) (hN : EIn N) : EIn (M - N) := fun i j => sub_mem (hM i j) (hN i j)

theorem EIn.neg {M : Matrix ι κ ℂ} (hM : EIn M) : EIn (-M) := fun i j => neg_mem (hM i j)

theorem EIn.smul {c : ℂ} (hc : c ∈ algebraicClosure ℚ ℂ) {M : Matrix ι κ ℂ} (hM : EIn M) : EIn (c • M) :=
  fun i j => mul_mem hc (hM i j)

theorem EIn.one : EIn (1 : Matrix ι ι ℂ) := fun i j => by
  rw [Matrix.one_apply]; split_ifs
  · exact one_mem _
  · exact zero_mem _

theorem EIn.mul {M : Matrix ι κ ℂ} {N : Matrix κ ι' ℂ} (hM : EIn M) (hN : EIn N) : EIn (M * N) := fun i j => by
  rw [Matrix.mul_apply]; exact sum_mem fun k _ => mul_mem (hM i k) (hN k j)

theorem EIn.transpose {M : Matrix ι κ ℂ} (hM : EIn M) : EIn Mᵀ := fun i j => hM j i

theorem EIn.kron {M : Matrix ι κ ℂ} {N : Matrix ι' κ' ℂ} (hM : EIn M) (hN : EIn N) :
    EIn (Matrix.kroneckerMap (· * ·) M N) := fun i j => by
  rw [Matrix.kroneckerMap_apply]; exact mul_mem (hM _ _) (hN _ _)

theorem EIn.det {M : Matrix ι ι ℂ} (hM : EIn M) : M.det ∈ algebraicClosure ℚ ℂ := by
  let M' : Matrix ι ι (algebraicClosure ℚ ℂ) := fun i j => ⟨M i j, hM i j⟩
  have e : M = (algebraicClosure ℚ ℂ).val.toRingHom.mapMatrix M' := by ext i j; rfl
  rw [e, ← RingHom.map_det]
  exact (M'.det).2

end Entries

theorem half_mem : (1 / 2 : ℂ) ∈ algebraicClosure ℚ ℂ := div_mem (one_mem _) (ofNat_mem _ 2)

theorem detPlus_mem {m n : ℕ} {sS : Matrix (Fin n) (Fin n) ℂ} {sT : Matrix (Fin m) (Fin m) ℂ}
    {a' : Matrix (Fin n) (Fin n) ℂ} {b : Matrix (Fin m) (Fin m) ℂ} (hS : EIn sS) (hT : EIn sT) (ha : EIn a') (hb : EIn b) :
    GlobalTheory.WeilParts.detPlus sS sT a' b ∈ algebraicClosure ℚ ℂ := by
  unfold GlobalTheory.WeilParts.detPlus
  have k1 : EIn (sT ⊗ₖ sSᵀ) := hT.kron hS.transpose
  have k2 : EIn (b ⊗ₖ a'ᵀ) := hb.kron ha.transpose
  have k3 : EIn ((1 + sT ⊗ₖ sSᵀ) * (b ⊗ₖ a'ᵀ)) := (EIn.one.add k1).mul k2
  have k4 : EIn ((1 / 2 : ℂ) • ((1 + sT ⊗ₖ sSᵀ) * (b ⊗ₖ a'ᵀ))) := k3.smul half_mem
  have k5 : EIn ((1 / 2 : ℂ) • (1 - sT ⊗ₖ sSᵀ)) := (EIn.one.sub k1).smul half_mem
  exact (k4.add k5).det

theorem compAt_mt_mul (θ : InfFam D) (τ : D.what₂.Tau) (V : HSp D) (g h : GA D V) :
    compAt θ τ (Formalism.L2.Theta.mt V (g * h)) = compAt θ τ (Formalism.L2.Theta.mt V g) * compAt θ τ (Formalism.L2.Theta.mt V h) := by
  have e : Formalism.L2.Theta.mt V (g * h) = Formalism.L2.Theta.mt V g * Formalism.L2.Theta.mt V h := by
    unfold Formalism.L2.Theta.mt; rw [map_mul, Units.val_mul]
  rw [e]
  exact Matrix.map_mul (f := (θ τ).comp (infPart D))

theorem compAt_mt_fin (θ : InfFam D) (τ : D.what₂.Tau) (V : HSp D) (g : GA D V) (hg : g ∈ GfC V) :
    compAt θ τ (Formalism.L2.Theta.mt V g) = 1 := by
  have h1 : infHom V g = 1 := hg
  have e : compAt θ τ (Formalism.L2.Theta.mt V g) = (Units.val (infHom V g)).map (θ τ) := rfl
  rw [e, h1, Units.val_one]
  exact Matrix.map_one _ (map_zero _) (map_one _)

theorem eIn_rat {θ : InfFam D} (hθ : IsInfFam θ) (τ : D.what₂.Tau) (V : HSp D) (γ : GA D V) (hγ : γ ∈ GQ V) :
    EIn (compAt θ τ (Formalism.L2.Theta.mt V γ)) := by
  obtain ⟨x, -, e⟩ := hγ
  have hm : Formalism.L2.Theta.mt V γ = (x : Matrix (Fin V.rank) (Fin V.rank) D.host.E).map (incA D) := by
    exact (congrArg Units.val e).symm
  intro i j
  rw [hm]
  show θ τ (infPart D (incA D (x i j))) ∈ _
  have e2 : infPart D (incA D (x i j)) = (1 : Ainf D.host.F) ⊗ₜ[D.host.F] (x i j : D.host.E) := by
    simp [infPart, incA, inclR, Algebra.TensorProduct.map_tmul]
  rw [e2, (hθ τ).1, mem_algebraicClosure_iff]
  exact ((Algebra.IsAlgebraic.isAlgebraic (R := ℚ) (x i j : D.host.E))).algHom (tauE D τ).toRatAlgHom

theorem eIn_real {θ : InfFam D} (hθ : IsInfFam θ) (τ : D.what₂.Tau) (V : HSp D) (γ : GA D V) (hγ : γ ∈ GQ V) (a : GA D V)
    (h : γ * a ∈ GfC V) : EIn (compAt θ τ (Formalism.L2.Theta.mt V a)) ∧ EIn (compAt θ τ (Formalism.L2.Theta.mt V a⁻¹)) := by
  constructor
  · have e : a = γ⁻¹ * (γ * a) := by group
    rw [e, compAt_mt_mul, compAt_mt_fin θ τ V _ h, Matrix.mul_one]
    exact eIn_rat hθ τ V _ (inv_mem hγ)
  · have e : a⁻¹ = (γ * a)⁻¹ * γ := by group
    rw [e, compAt_mt_mul, compAt_mt_fin θ τ V _ (inv_mem h), Matrix.one_mul]
    exact eIn_rat hθ τ V _ hγ

theorem exists_root_alg {θ : InfFam D} (hθ : IsInfFam θ) (V : HSp D) (hV : ∀ τ, (gramAt D V τ).det ≠ 0)
    (g : GA D V) (hg : g ∈ GinfC V) (hA : ∀ τ, (compAt θ τ (Formalism.L2.Theta.mt V g)).det ∈ algebraicClosure ℚ ℂ) :
    ∃ x, IsDetRoot V g x ∧ ∀ ν : (AE D)ˣ →* Circle, (∀ τ, ∃ a, HasInfExp D ν τ a) →
      ((ν x : Circle) : ℂ) ∈ algebraicClosure ℚ ℂ := by
  classical
  have hu : ∀ τ, ‖(compAt θ τ (Formalism.L2.Theta.mt V g)).det‖ = 1 := fun τ => by
    have h : (compAt θ τ (Formalism.L2.Theta.mt V g))ᴴ * gramAt D V τ * compAt θ τ (Formalism.L2.Theta.mt V g) = gramAt D V τ :=
      GlobalTheory.FockCompare.RealAction.infMat_mem_UH hθ V g τ
    have h2 := congrArg (fun M => ‖Matrix.det M‖) h
    simp only [Matrix.det_mul, Matrix.det_conjTranspose, norm_mul, norm_star] at h2
    have h3 : ‖(gramAt D V τ).det‖ ≠ 0 := norm_ne_zero_iff.2 (hV τ)
    have h4 : ‖(compAt θ τ (Formalism.L2.Theta.mt V g)).det‖ ^ 2 = 1 := by
      apply mul_left_cancel₀ h3; linear_combination h2
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).1 h4
  have hw : ∀ τ, ∃ w : ℂ, w ^ 2 = (compAt θ τ (Formalism.L2.Theta.mt V g)).det ∧ ‖w‖ = 1 := fun τ => by
    obtain ⟨w, hw⟩ := IsAlgClosed.exists_pow_nat_eq (compAt θ τ (Formalism.L2.Theta.mt V g)).det two_pos
    refine ⟨w, hw, (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).1 ?_⟩
    rw [← norm_pow, hw, hu]
  choose w hw1 hw2 using hw
  have hw0 : ∀ τ, w τ ≠ 0 := fun τ h => by simpa [h] using hw2 τ
  have hwA : ∀ τ, w τ ∈ algebraicClosure ℚ ℂ := fun τ => by
    have := hA τ
    rw [← hw1, mem_algebraicClosure_iff] at this
    exact mem_algebraicClosure_iff.2 (IsAlgebraic.of_pow two_pos this)
  choose x hx1 hx2 using fun τ => GlobalTheory.VacuumCharacter.exists_idele_at hθ τ (w τ) (hw0 τ)
  have hf : finPart D ((∏ τ, x τ : (AE D)ˣ) : AE D) = 1 := by
    rw [Units.coe_prod, map_prod]; exact Finset.prod_eq_one fun τ _ => hx1 τ
  have hi : ∀ τ, θ τ (infPart D ((∏ τ, x τ : (AE D)ˣ) : AE D)) = w τ := fun τ => by
    rw [Units.coe_prod, map_prod, map_prod]
    simp [hx2]
  refine ⟨∏ τ, x τ, ?_, fun ν hc => ?_⟩
  · refine GlobalTheory.VacuumCharacter.adele_ext hθ ?_ fun τ => ?_
    · have hd : finPart D (Formalism.L2.Theta.mt V g).det = 1 := by
        have hg' : finHom V g = 1 := hg
        have : (Formalism.L2.Theta.mt V g).map (finPart D) = 1 := congrArg Units.val hg'
        rw [RingHom.map_det]
        exact (congrArg Matrix.det this).trans Matrix.det_one
      rw [map_mul, hf]
      exact ((congrArg₂ (· * ·) hd (GlobalTheory.VacuumCharacter.finPart_cA _ hf)).trans (one_mul 1)).symm
    · rw [map_mul, map_mul, hi]
      have e1 := GlobalTheory.FockCompare.comp_cA hθ τ ((∏ τ, x τ : (AE D)ˣ) : AE D)
      have e2 := GlobalTheory.VacuumCharacter.det_compAt θ τ (Formalism.L2.Theta.mt V g)
      rw [hi] at e1
      refine Eq.trans ?_ (congrArg₂ (· * ·) e2 e1.symm)
      have : w τ * starRingEnd ℂ (w τ) = 1 := by rw [Complex.mul_conj', hw2]; simp
      rw [← hw1]; linear_combination (-w τ) * this
  · rw [map_prod]
    rw [show ((∏ τ, ν (x τ) : Circle) : ℂ) = ∏ τ, (ν (x τ) : ℂ) from map_prod Circle.coeHom _ _]
    refine prod_mem fun τ _ => ?_
    obtain ⟨a, n, -, -, h⟩ := hc τ
    rw [h θ hθ (x τ) (hx1 τ) (fun τ' h' => by rw [hx2, if_neg h']), hx2, if_pos rfl, hw2]
    simp only [Complex.ofReal_one, div_one]
    exact zpow_mem (hwA τ) n

theorem realScalar : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil}
    {i j : Fin D.R.m} {A A' WW : HSp D} {X : Tri T A A' WW},
    IsBottomTri W i j X → ∀ (t : T), ∀ γ ∈ Formalism.L2.Theta.GQ A, ∀ a ∈ GinfC A, ∀ γ' ∈ Formalism.L2.Theta.GQ WW, ∀ a' ∈ GinfC WW,
      γ * a ∈ GfC A → γ' * a' ∈ GfC WW →
      ∃ C : ℂ, IsAlgebraic ℚ C ∧ X.ω t (a, a') X.vac = C • X.vac := by
  intro D T L sc G W i j A A' WW X hX t γ hγ a ha γ' hγ' a' ha' hγa hγa'
  classical
  have hI := hX.is
  have hθ : IsInfFam W.θ := hI.isVac.2.inf
  have hψ : IsStdChar D W.ψ (-1) := hI.isVac.1
  set om' := (X.ω t).toSgn true with hom'
  have hom := hI.weil t
  have hsA : ∀ τ, X.rA.s τ = 1 := fun τ => (hX.std.2.2 τ).1
  have hsW : ∀ τ, X.rW.s τ = 1 := fun τ => (hX.stdW.2.2 τ).1
  set g : GA D (neg A) := (ofSgn true A).symm a with hgdef
  have hga : ofSgn true A g = a := MulEquiv.apply_symm_apply _ _
  have hg : g ∈ GinfC (neg A) := (GlobalTheory.SgnIdent.mem_GinfC_sgn true A g).2 (by rw [hga]; exact ha)
  have cS : ∀ τ, IsCartanInv (gramAt D (neg A) τ) (-X.rA.s τ) := fun τ => GlobalTheory.Grid.isCartanInv_sgn true A τ (hI.rigA.2.2 τ).1
  have cT : ∀ τ, IsCartanInv (gramAt D WW τ) (X.rW.s τ) := fun τ => (hI.rigW.2.2 τ).1
  have hdet : ∀ τ, (gramAt D (neg A) τ).det ≠ 0 := fun τ h0 => by
    have := (cS τ).2.2.det_pos.ne'
    rw [Matrix.det_mul, h0, zero_mul] at this
    exact this rfl
  have hdetW : ∀ τ, (gramAt D WW τ).det ≠ 0 := fun τ h0 => by
    have := (cT τ).2.2.det_pos.ne'
    rw [Matrix.det_mul, h0, zero_mul] at this
    exact this rfl
  have mg : ∀ τ, compAt W.θ τ (Formalism.L2.Theta.mt (neg A) g) = compAt W.θ τ (Formalism.L2.Theta.mt A a) := fun τ => by
    have e := GlobalTheory.Grid.mt_ofSgn true A g
    rw [hga] at e
    rw [e]
  have mgi : ∀ τ, compAt W.θ τ (Formalism.L2.Theta.mt (neg A) g⁻¹) = compAt W.θ τ (Formalism.L2.Theta.mt A a⁻¹) := fun τ => by
    have e := GlobalTheory.Grid.mt_ofSgn true A g⁻¹
    rw [map_inv, hga] at e
    rw [e]
  have eA := fun τ => eIn_real hθ τ A γ hγ a hγa
  have eW := fun τ => eIn_real hθ τ WW γ' hγ' a' hγa'
  obtain ⟨x, hx, hxν⟩ := exists_root_alg hθ (neg A) hdet g hg fun τ => by rw [mg]; exact (eA τ).1.det
  obtain ⟨y, hy, hyν⟩ := exists_root_alg hθ WW hdetW a' ha' fun τ => (eW τ).1.det
  obtain ⟨η, hη⟩ := GlobalTheory.WeilParts.exists_isEtaTilde_unramified D
  have hC := GlobalTheory.WeilVacChar.vacuum_character D W.ψ hψ (neg A) WW W.θ hθ _ _ om' η hη hom (fun τ => -X.rA.s τ) X.rW.s cS cT
    g hg a' ha' (fun τ => by rw [hsA]; simp) (fun τ => by rw [hsW]; simp) x y hx hy X.vac hI.isVac.2.theta hI.isVac.2.fock
  have hexp : ∀ (χ : (AE D)ˣ →* Circle) (n : ℕ), IsHeckeChar D χ → ResEta D χ n → ∀ k : ℕ,
      ∀ τ, ∃ b, HasInfExp D (χ * (η ^ k)⁻¹) τ b := fun χ n h1 h2 k τ => by
    obtain ⟨b, hb⟩ := GlobalTheory.SplitCharExp.exists_hasInfExp D W.θ χ n τ hθ h1 h2
    exact ⟨_, GlobalTheory.VacuumCharacter.hasInfExp_twist hb (hη.2.2.2 τ) k⟩
  have key : X.ω t (a, a') X.vac = om' (g, a') X.vac := by
    show _ = X.ω t (ofSgn true A g, a') X.vac
    rw [hga]
  rw [key, hC]
  refine ⟨_, ?_, rfl⟩
  · rw [← mem_algebraicClosure_iff, Circle.coe_mul, Circle.coe_inv]
    refine mul_mem (mul_mem (inv_mem (hxν _ (hexp _ _ hom.hecT hom.resT _))) (hyν _ (hexp _ _ hom.hecS hom.resS _)))
      (prod_mem fun τ _ => ?_)
    rw [mgi]
    have hs1 : EIn (-X.rA.s τ) := by rw [hsA]; exact EIn.one.neg
    have hs2 : EIn (X.rW.s τ) := by rw [hsW]; exact EIn.one
    exact detPlus_mem hs1 hs2 (eA τ).2 (eW τ).1

end GlobalTheory.RealScalarAlg

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RealThetaCorrespondenceUpwardPairBothDirections
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.EvenOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section

namespace GlobalTheory.EvenOnto

theorem upPair_down {D : D7} {X : ProvA} (h : GlobalTheory.ArchRec.Good D X) (h1 : Formalism.MainNotions.SchurIrreducible.ArchimedeanRallisFirst X) (h3 : Formalism.MainNotions.SchurIrreducible.ArchimedeanRallisUpDownLine X)
    {t : ℕ} {S S' : SPar} {aS aT : ℚ} (hp : UpPair t S S' aS aT) (τ : D.what₂.Tau) (V W : HSp D) :
    GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction.ForAllAt τ V W aS aT S S' fun MS MT A B pt =>
      GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction.LiftLaw MT τ B pt MS A ∧ ∀ ip, GlobalTheory.ArchRec.IsIp V W ip → GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction.ZetaLaw MT τ B pt MS A ip := by
  obtain ⟨al, be, ga, de, hd, -, rfl, rfl⟩ := hp
  intro ψ θ χS χT ω hω hS hT PS PT MS MT p1 p2 BS BT f hf
  obtain ⟨hm, e, u, hk⟩ := GlobalTheory.ArchRec.tie_small h hd.1 MS τ true false p1
  obtain ⟨e', u', hk'⟩ := GlobalTheory.ArchRec.tie_large h hd.1 MT τ false true p2
  obtain ⟨κ, hR⟩ := GlobalTheory.ArchRec.exists_real hω hS hT (GlobalTheory.ArchRec.isFrameOf_model MS τ) (GlobalTheory.ArchRec.isFrameOf_model MT τ) hf
    hk.ord.1 hk'.ord.1
  exact GlobalTheory.ArchRec.lift_down h h1 h3 hd hm hk hk' hR

theorem pairPar_of_upPair {t : ℕ} {S S' : SPar} {aS aT : ℚ} (hp : UpPair t S S' aS aT) :
    GlobalTheory.PairLift.PairPar S S' aS aT ∧ GlobalTheory.PairLift.PairPar S' S aT aS := by
  obtain ⟨al, be, ga, de, hd, hfar, rfl, rfl⟩ := hp
  have hT : GlobalTheory.PairLift.ThetaPar t (GlobalTheory.Chain.signed (al ++ be) (ga ++ de) aT) (GlobalTheory.Chain.signed (al ++ block t ++ de) (ga ++ be) aS) aT aS :=
    ⟨al, be, ga, de, rfl, Or.inl ⟨hd, rfl⟩⟩
  have hF : GlobalTheory.SignedHC.FarFrom aT (((t : ℚ) + 3) / 2) (GlobalTheory.Chain.signed (al ++ be) (ga ++ de) aT) := by
    intro x hx
    obtain ⟨s, hs⟩ := GlobalTheory.SignedHC.mem_entries.1 hx
    have : ∃ y ∈ al ++ be ++ ga ++ de, x = y + aT := by
      rcases Finset.mem_union.1 hs with h | h
      · obtain ⟨y, hy, hy'⟩ := List.mem_map.1 (List.mem_toFinset.1 h)
        exact ⟨y, by simp only [List.mem_append] at hy ⊢; tauto, (congrArg Prod.fst hy').symm⟩
      · obtain ⟨y, hy, hy'⟩ := List.mem_map.1 (List.mem_toFinset.1 h)
        exact ⟨y, by simp only [List.mem_append] at hy ⊢; tauto, (congrArg Prod.fst hy').symm⟩
    obtain ⟨y, hy, rfl⟩ := this
    rw [add_sub_cancel_right]
    exact hfar y hy
  exact ⟨⟨t, _, _, rfl, rfl, Or.inl ⟨hT, hF⟩⟩, ⟨t, _, _, rfl, rfl, Or.inr hT⟩⟩

theorem upPair_arch : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → ∀ (D : D7) (t : ℕ) (S S' : SPar) (aS aT : ℚ),
    UpPair t S S' aS aT → (∀ (τ : D.what₂.Tau) (V W : HSp D), GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction.ToSource τ V W aS aT S S' ∧
      GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction.ZetaSource τ V W aS aT S S') ∧ ∀ X : ProvA, Formalism.MainNotions.SchurIrreducible.ArchimedeanRallisUpDownLine X → Formalism.MainNotions.SchurIrreducible.ArchimedeanRallisFourth X →
      Formalism.MainNotions.SchurIrreducible.ArchimedeanRallisFifth X → GlobalTheory.PairLift.RulePar X S S' aS aT ∧ GlobalTheory.PairLift.RulePar X S' S aT aS := by
  intro hDS hHC D t S S' aS aT hp
  refine ⟨fun τ V W => ?_, fun X h3 h4 h5 => ?_⟩
  · obtain ⟨X, hX, h1, -, h3, -, -⟩ := GlobalTheory.RealPlaceTheta.exists_record_theta_all hDS hHC
    have h : GlobalTheory.ArchRec.Good D X :=
      ⟨hX, GlobalTheory.CoverDS.admissibleDiscreteSeries_of_hasParam hDS X hX, hHC.admQ5_of_harishChandraModules X, GlobalTheory.T.thetaModels_are_coverDiscreteSeries_of_harishChandra hDS hHC D⟩
    have down := upPair_down h h1 h3 hp τ V W
    exact ⟨fun ψ θ χS χT ω hω hS hT PS PT MS MT p1 p2 BS BT f hf =>
        (down ψ θ χS χT ω hω hS hT PS PT MS MT p1 p2 BS BT f hf).1,
      fun ψ θ χS χT ω hω hS hT PS PT MS MT p1 p2 BS BT f hf μ 𝓕 m1 m2 =>
        (down ψ θ χS χT ω hω hS hT PS PT MS MT p1 p2 BS BT f hf).2 _ ⟨μ, 𝓕, m1, m2, rfl⟩⟩
  · obtain ⟨q1, q2⟩ := pairPar_of_upPair hp
    exact ⟨GlobalTheory.StepRule.rulePar_of_pairPar h3 h4 h5 q1, GlobalTheory.StepRule.rulePar_of_pairPar h3 h4 h5 q2⟩

end GlobalTheory.EvenOnto

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RealUnitaryFockColumnActionSurjective
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx MeasureTheory
noncomputable section
open scoped Matrix

namespace GlobalTheory.RealColAct

theorem compAt_eq_infMat {D : D7} (θ : InfFam D) (V : HSp D) (τ : D.what₂.Tau) (h : GA D V) :
    compAt θ τ (Formalism.L2.Theta.mt V h) = infMat D.sp.cm.sig V.gram (θ τ) h := rfl

theorem realCol_surjective {D : D7} {θ : InfFam D} (hθ : IsInfFam θ) (V : HSp D) (hV : HSpace.gram V = 1) :
    Function.Surjective (GlobalTheory.RealColAct.realCol θ hθ V hV) := by
  classical
  intro u
  have hex : ∀ τ, ∃ h : GA D V, IsAtTau θ V τ ((u τ : Matrix (Fin V.rank) (Fin V.rank) ℂ)ᵀ) h := fun τ => by
    refine (GlobalTheory.PointAtPlace.existsUnique_isAtTau V τ θ hθ _ ?_).exists
    have hu := transpose_mem_unitary (u τ).2
    rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose] at hu
    show _ * _ * _ = _
    rw [gramAt_of_gram_one hV, Matrix.mul_one, hu]
  choose hτ hhτ using hex
  have key : ∀ (L : List D.what₂.Tau), L.Nodup → ∀ ρ,
      compAt θ ρ (Formalism.L2.Theta.mt V (L.map hτ).prod) =
        if ρ ∈ L then ((u ρ : Matrix (Fin V.rank) (Fin V.rank) ℂ)ᵀ) else 1 := by
    intro L
    induction L with
    | nil => intro _ ρ; simp only [List.map_nil, List.prod_nil, List.not_mem_nil, if_false]; exact GlobalTheory.StdUnn.CartanMove.compAt_mt_one θ ρ V
    | cons a L ih =>
      intro hL ρ
      rw [List.nodup_cons] at hL
      rw [List.map_cons, List.prod_cons, GlobalTheory.StdUnn.CartanMove.compAt_mt_mul, ih hL.2 ρ, compAt_eq_infMat]
      by_cases c : ρ = a
      · subst c
        rw [(hhτ ρ).2.1, if_neg hL.1, if_pos List.mem_cons_self, Matrix.mul_one]
      · rw [(hhτ a).2.2 ρ c, Matrix.one_mul]
        by_cases d : ρ ∈ L
        · rw [if_pos d, if_pos (List.mem_cons_of_mem a d)]
        · rw [if_neg d, if_neg (by simp [c, d])]
  let L := (Finset.univ : Finset D.what₂.Tau).toList
  have hmem : (L.map hτ).prod ∈ GinfC V := by
    apply Subgroup.list_prod_mem
    intro x hx
    obtain ⟨τ, -, rfl⟩ := List.mem_map.1 hx
    exact (hhτ τ).1
  refine ⟨(⟨(L.map hτ).prod, hmem⟩ : GinfC V)⁻¹, ?_⟩
  funext ρ
  apply Subtype.ext
  rw [realCol_apply]
  simp only [InvMemClass.coe_inv, inv_inv]
  rw [key L (Finset.nodup_toList _) ρ, if_pos (Finset.mem_toList.2 (Finset.mem_univ ρ)), Matrix.transpose_transpose]

end GlobalTheory.RealColAct
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RegularSemisimpleRationalClassKernelIntegrals
section
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Chamber GlobalTheory.TruncKer GlobalTheory.Cusp

noncomputable section

namespace GlobalTheory.RegClass

open GlobalTheory.IndefiniteRowSideFullHecke.NonFieldTypeVanishingAlt

variable {D : D7} {V : HSp D}

theorem rat_mem (g : GF V) : rat V g ∈ GQ V := by
  rw [show GQ V = (rat V).range from (range_ratEmb ..).symm]; exact ⟨g, rfl⟩

def classEquiv (γ : GF V) : {δ : GF V | IsConj γ δ} ≃ ratClass (GQ V) (rat V γ) :=
  Equiv.ofBijective (fun δ => ⟨rat V δ, by
      obtain ⟨c, hc⟩ := isConj_iff.1 δ.2
      refine ⟨rat V c⁻¹, rat_mem _, ?_⟩
      rw [← hc]; simp only [map_mul, map_inv, inv_inv]⟩)
    ⟨fun a b h => Subtype.ext (ratEmb_injective _ _ (congrArg Subtype.val h)), fun δ => by
      obtain ⟨δ, g, hg, rfl⟩ := δ
      rw [show GQ V = (rat V).range from (range_ratEmb ..).symm] at hg
      obtain ⟨c, rfl⟩ := hg
      refine ⟨⟨c⁻¹ * γ * c, isConj_iff.2 ⟨c⁻¹, by group⟩⟩, Subtype.ext ?_⟩
      simp only [map_mul, map_inv]⟩

theorem classKernel_eq (γ : GF V) (f : GA D V → ℂ) (x : GA D V) :
    classKernel (GQ V) (rat V γ) f x = ∑' δ : {δ : GF V | IsConj γ δ}, f (x⁻¹ * rat V δ * x) :=
  ((classEquiv γ).tsum_eq fun δ : ratClass (GQ V) (rat V γ) => f (x⁻¹ * δ * x)).symm

theorem summable_class {f : GA D V → ℂ} (hf : HasCompactSupport f) {γ : GA D V} (hγ : γ ∈ GQ V) (x : GA D V) :
    Summable fun δ : ratClass (GQ V) γ => f (x⁻¹ * δ * x) := by
  have hmem : ∀ δ : ratClass (GQ V) γ, (δ : GA D V) ∈ GQ V := fun ⟨δ, k, hk, e⟩ => e ▸ mul_mem (mul_mem (inv_mem hk) hγ) hk
  let ι : ratClass (GQ V) γ → GQ V := fun δ => ⟨δ, hmem δ⟩
  have hι : Function.Injective ι := fun a b e => Subtype.ext (congrArg (fun z : GQ V => (z : GA D V)) e)
  apply summable_of_hasFiniteSupport
  refine ((GlobalTheory.AutomorphicL2Unitary.finite_support_kernel (Γ := GQ V) hf x x).preimage hι.injOn).subset ?_
  intro δ hδ
  exact hδ

theorem fd_iff {μ : Measure (GA D V)} [μ.IsHaarMeasure] {𝓕 : Set (GA D V)} (h𝓕 : IsFundamentalDomain (GQ V) 𝓕 μ)
    {φ : GA D V → ℂ} (hφ : GlobalTheory.AutomorphicL2Unitary.LeftInv (GQ V) φ) :
    (IntegrableOn φ 𝓕 μ ↔ Integrable (descend (GQ V) φ) (autMeasure V μ)) ∧
      ∫ x in 𝓕, φ x ∂μ = ∫ q, descend (GQ V) φ q ∂autMeasure V μ := by
  refine ⟨?_, ?_⟩
  · have := (GlobalTheory.AutomorphicL2Unitary.memLp_quotMeasure_iff h𝓕 (F := descend (GQ V) φ) (p := 1))
    rw [hφ.lift_descend, memLp_one_iff_integrable, memLp_one_iff_integrable] at this
    exact this.symm
  · rw [GlobalTheory.AutomorphicL2Unitary.integral_quotMeasure h𝓕]
    exact congrArg (fun F => ∫ x in 𝓕, F x ∂μ) hφ.lift_descend.symm

theorem regClass : ∀ (D : D7) (V : HSp D) (γ : GF V), IsRegSS γ.1.1 → IsSSClass {δ | IsConj γ δ} ∧
    ∀ (f : GA D V → ℂ), (∀ x, GlobalTheory.IndefiniteRowSideFullHecke.NonFieldTypeVanishingAlt.classKernel (GQ V) (rat V γ) f x =
      ∑' δ : {δ : GF V | IsConj γ δ}, f (x⁻¹ * rat V δ * x)) ∧
    (Continuous f → HasCompactSupport f → ∀ (μ : Measure (GA D V)) [μ.IsHaarMeasure] (c : ℂ),
      ((∀ 𝓕, IsFundamentalDomain (GQ V) 𝓕 μ → GlobalTheory.IndefiniteRowSideFullHecke.NonFieldTypeVanishingAlt.HasClassInt (GQ V) μ 𝓕 (rat V γ) f c) ↔
        Integrable (descend (GQ V) (GlobalTheory.IndefiniteRowSideFullHecke.NonFieldTypeVanishingAlt.classKernel (GQ V) (rat V γ) f)) (autMeasure V μ) ∧
          ∫ q, descend (GQ V) (GlobalTheory.IndefiniteRowSideFullHecke.NonFieldTypeVanishingAlt.classKernel (GQ V) (rat V γ) f) q ∂autMeasure V μ = c)) := by
  intro D V γ hγ
  refine ⟨GlobalTheory.regSS_conjClass_isSSClass γ hγ, fun f => ⟨classKernel_eq γ f, fun _ hcs μ _ c => ?_⟩⟩
  have hinv : GlobalTheory.AutomorphicL2Unitary.LeftInv (GQ V) (classKernel (GQ V) (rat V γ) f) :=
    fun δ hδ x => classKernel_mul _ _ hδ x
  constructor
  · intro H
    have h𝓕 := GlobalTheory.AutomorphicL2Unitary.isFundamentalDomain_stdDom (GQ V) μ
    obtain ⟨-, hi, hv⟩ := H _ h𝓕
    obtain ⟨e1, e2⟩ := fd_iff h𝓕 hinv
    exact ⟨e1.1 hi, e2 ▸ hv⟩
  · rintro ⟨hi, hv⟩ 𝓕 h𝓕
    obtain ⟨e1, e2⟩ := fd_iff h𝓕 hinv
    exact ⟨summable_class hcs (rat_mem γ), e1.2 hi, e2.trans hv⟩

theorem main : ∀ (D : D7) (V : HSp D) (γ : GF V), IsRegSS γ.1.1 → IsSSClass {δ | IsConj γ δ} ∧ ∀ (f : GA D V → ℂ), (∀ x, GlobalTheory.IndefiniteRowSideFullHecke.NonFieldTypeVanishingAlt.classKernel (GQ V) (rat V γ) f x = ∑' δ : {δ : GF V | IsConj γ δ}, f (x⁻¹ * rat V δ * x)) ∧ (Continuous f → HasCompactSupport f → ∀ (μ : Measure (GA D V)) [μ.IsHaarMeasure] (c : ℂ), ((∀ 𝓕, IsFundamentalDomain (GQ V) 𝓕 μ → GlobalTheory.IndefiniteRowSideFullHecke.NonFieldTypeVanishingAlt.HasClassInt (GQ V) μ 𝓕 (rat V γ) f c) ↔ Integrable (descend (GQ V) (GlobalTheory.IndefiniteRowSideFullHecke.NonFieldTypeVanishingAlt.classKernel (GQ V) (rat V γ) f)) (autMeasure V μ) ∧ ∫ q, descend (GQ V) (GlobalTheory.IndefiniteRowSideFullHecke.NonFieldTypeVanishingAlt.classKernel (GQ V) (rat V γ) f) q ∂autMeasure V μ = c)) := regClass

end GlobalTheory.RegClass
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SandwichedFlipRouteThroughSmallEqInvConstRouteBiStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open scoped Pointwise

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sandwichedFlip_routeThroughSmall_eq_inv_const_routeBig : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} (M : Vol G) (B : Frames G) (ρ : RealMatch W) (t : T) (i j : ℕ) (hi : i < D.R.m) (hj : j < D.R.m) (c : ℂ), c ≠ 0 → CommutesWith W B ρ t ⟨i, hi⟩ ⟨j, hj⟩ c → M.Is t → GlobalTheory.FlipRun.CuspStep W M ρ t → ∀ (A : Path T (.grid 0 D.R.m) (.grid i (j + 1))) (Bp : Path T (.grid (i + 1) j) (.grid D.R.m 0)), GlobalTheory.FlipRun.OnGrid D.R.m t A → GlobalTheory.FlipRun.OnGrid D.R.m t Bp → ∀ (e : AE D), IsIdemSum e (locPl G t) → ∀ (α : PureT G A) (β : PureT G Bp) (φA : PureT G A) (φB : PureT G Bp), GlobalTheory.FlipRun.VecAll ρ e A φA α → GlobalTheory.FlipRun.VecAll ρ e Bp φB β → ∀ (σs : TotT G (routeSmall t i j)) (σb : TotT G (routeBig t i j)) (Φ : ∀ w, Matrix (Fin ((locGrid G t w).rank (i, j))) ((locGrid G t w).Cols i j) (Kw w) → ℂ), (∀ w ∈ locPl G t, GlobalTheory.SplitFlip.IsNatDatum (unifAt w) (depthAt G w) (Φ w)) → HasFlip B t ρ ⟨i, hi⟩ ⟨j, hj⟩ (depthAt G) Φ σb σs → ∀ F : Fn G (.grid 0 D.R.m), GlobalTheory.FlipRun.IsCuspListed W.θ _ F → ∀ Q : GlobalTheory.FlipRun.PolE G →₀ ℂ, liftT W M _ (GlobalTheory.FlipRun.tensE W _ Q (((σs).sum fun d c => Finsupp.single (((α).append d).append (β)) c) : TotT G ((A.comp (routeSmall t i j)).comp Bp))) F = c⁻¹ • liftT W M _ (GlobalTheory.FlipRun.tensE W _ (GlobalTheory.FlipRun.flipPolE ρ i j Q) (((σb).sum fun d c => Finsupp.single (((α).append d).append (β)) c) : TotT G ((A.comp (routeBig t i j)).comp Bp))) F := by
  first | exact @GlobalTheory.FlipRun.oneFlip_sandwich | exact GlobalTheory.FlipRun.oneFlip_sandwich | (intros; apply GlobalTheory.FlipRun.oneFlip_sandwich <;> assumption)
end

