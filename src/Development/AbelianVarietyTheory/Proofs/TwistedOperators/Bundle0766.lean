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
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0947
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0941
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0140
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1719
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1852
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.NormSqMulGaussianLatticeTranslateEqShifted
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0841
import Formalism.LocalToGlobal.Columns.CoefficientsModP.LatticeBasisExistsHolds
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FiniteHeisenbergTranslateSelfDualVacuumFockJets
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IdempotentMulEqZeroOfOrthogonal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1708
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0964
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0006
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0755
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0746
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0760
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0734
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0320
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0585
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ComplexEmbeddingHermitianQuadrupleSum
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0207
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0761
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0565
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0547
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0261
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0273
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0013
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle0002
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsFullRankSubMem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1116
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocalGLEmbeddingUnitary
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1418
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2048
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2007
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2244
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2032
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1511
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0762
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0526
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0393

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FrameGramUnitaryIdentity
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx MeasureTheory

noncomputable section

namespace GlobalTheory.FinTransJet

theorem inV_stdL_eq_colLat {D : D7} {n : ℕ} (B : GL (Fin n) D.host.E) :
    GlobalTheory.MovedDict.inV B (Formalism.MainNotions.StandardLatticesGL3.stdL D n) = (Formalism.L2.DIV.colLat B : Set (Fin n → D.host.E)) := by
  have hc := GlobalTheory.ColStd.colLat_comap_eq_stdLat B
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    have hy' : y ∈ Formalism.L2.Pj.stdLat D.host.E n := hy
    rw [← hc] at hy'
    exact hy'
  · intro hx
    refine ⟨(B⁻¹ : GL (Fin n) D.host.E).1.mulVec x, ?_, ?_⟩
    · show _ ∈ Formalism.L2.Pj.stdLat D.host.E n
      rw [← hc, Submodule.mem_comap]
      simp only [LinearMap.restrictScalars_apply, Matrix.mulVecLin_apply, Matrix.mulVec_mulVec]
      rw [show (B.1 * (B⁻¹).1) = 1 from B.mul_inv, Matrix.one_mulVec]
      exact hx
    · simp only [Matrix.mulVec_mulVec]
      rw [show (B.1 * (B⁻¹).1) = 1 from B.mul_inv, Matrix.one_mulVec]

end GlobalTheory.FinTransJet

namespace GlobalTheory.FinTransJet

theorem fock_jets_heisO_fin : GlobalTheory.FunPr.Hypotheses₂ → (∀ D, GlobalTheory.NormSum.Inp D) →
    ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D)
    (sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ)
    (frS : GL (Fin S.rank) D.host.E) (frT : GL (Fin T.rank) D.host.E),
    Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) frS.1 * S.gram * frS.1 = 1 →
    Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) frT.1 * T.gram * frT.1 = 1 →
    (∀ τ, IsCartanInv (gramAt D S τ) (sS τ)) → (∀ τ, IsCartanInv (gramAt D T τ) (sT τ)) →
    ∀ (δ t0 : ℂ), StandardLatticesGL3.Crv D D.host.ccK δ → δ ≠ 0 → GL3Theta.IsTwoTorsionPointUnkilled D (TaylorLogMetric.lamOf D D.host.ccK δ) t0 →
    ∀ e0 : TaylorLogMetric.VC D S.rank T.rank → ℂ, StandardLatticesGL3.oddE0 D D.host.ccK δ t0 S.rank T.rank e0 →
    ∀ f, IsVacO ψ θ S T sS sT (colLat frS : Set _) (colLat frT : Set _) f → ∀ c : ℂ,
    (∀ k : FVar D T.rank S.rank →₀ ℕ, pureTensorO ψ θ S T sS sT (fun τ => frS.1.map (tauE D τ)) (fun τ => frT.1.map (tauE D τ)) f
        (MvPolynomial.monomial k 1) 0 = c * ((k.prod fun v n => GlobalTheory.FunObj.period δ v.1 ^ n) * GL3Theta.applyAt0 D (MvPolynomial.monomial k 1) e0)) →
    ∀ u : WO S T, u.map (infPart D) = 0 →
    ∃ (m : ℕ) (a : Fin m → ℂ) (s : Fin m → TaylorLogMetric.VC D S.rank T.rank),
      (∀ l, IsAlgebraic ℚ (a l)) ∧ (∀ l, StandardLatticesGL3.LaQ D (TaylorLogMetric.tor0 D D.host.ccK δ) (StandardLatticesGL3.stdL D S.rank) (StandardLatticesGL3.stdL D T.rank) (s l)) ∧
      ∀ k : FVar D T.rank S.rank →₀ ℕ, pureTensorO ψ θ S T sS sT (fun τ => frS.1.map (tauE D τ)) (fun τ => frT.1.map (tauE D τ))
        (heisO ψ S T u f) (MvPolynomial.monomial k 1) 0 =
        c * ((k.prod fun v n => GlobalTheory.FunObj.period δ v.1 ^ n) * GL3Theta.applyAt0 D (MvPolynomial.monomial k 1)
          (StandardLatticesGL3.comb D (TaylorLogMetric.tor0 D D.host.ccK δ) a s e0)) := by
  intro _hP _hI D ψ θ S T sS sT frS frT hS hT hcS hcT δ t0 _hC hδ _ht0 e0 he0 f hf c hjets u hu
  have hlS : Submodule.IsLattice D.host.E (Formalism.L2.DIV.colLat frS) := GlobalTheory.FunObj.VecEx.isLattice_colLat frS
  have hlT : Submodule.IsLattice D.host.E (Formalism.L2.DIV.colLat frT) := GlobalTheory.FunObj.VecEx.isLattice_colLat frT
  obtain ⟨n, hn, hnu⟩ := GlobalTheory.PlaceDatum.exists_nsmul_mem_latO' hlS hlT u hu
  rw [← inV_stdL_eq_colLat frS, ← inV_stdL_eq_colLat frT] at hf hnu
  have he0d : Differentiable ℂ e0 := he0.1.1
  obtain ⟨ζ, s, ⟨m, hm, hζ⟩, hs, hk⟩ := GlobalTheory.HeisTrans.core ψ θ S T sS sT frS frT hS hT hcS hcT
    (Formalism.MainNotions.StandardLatticesGL3.stdL D S.rank) (Formalism.MainNotions.StandardLatticesGL3.stdL D T.rank) (GlobalTheory.NormSum.VacInt.sd_std D S.rank)
    (GlobalTheory.NormSum.VacInt.sd_std D T.rank) δ hδ e0 he0d c f hf hjets n hn u hnu
  have hζalg : IsAlgebraic ℚ ζ := by
    have hint : IsIntegral ℚ ζ := ⟨Polynomial.X ^ m - 1, Polynomial.monic_X_pow_sub_C 1 hm.ne', by simp [hζ]⟩
    exact hint.isAlgebraic
  refine ⟨1, ![ζ], ![s], fun l => ?_, fun l => ?_, fun k => ?_⟩
  · fin_cases l; exact hζalg
  · fin_cases l; exact ⟨n, hn, hs⟩
  · refine Eq.trans (hk k) ?_
    congr 3
    funext z
    simp [Formalism.MainNotions.StandardLatticesGL3.comb]

end GlobalTheory.FinTransJet
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeisenbergCommutantPermutesFirstRowCosetVectors
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

namespace GlobalTheory.CosPerm

variable {D : D7}

theorem heisO_smul_fun (ψ : AddChar (AF D.host.F) ℂ) {S T : HSp D} (w : WO S T) (c : ℂ) (f : WO S T → ℂ) :
    heisO ψ S T w (c • f) = c • heisO ψ S T w f := by
  funext x; simp only [heisO, Pi.smul_apply, smul_eq_mul]; ring

theorem heisO_star {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) (S T : HSp D) (w : WO S T) (f : WO S T → ℂ) :
    heisO ψ S T w (star f) = star (heisO ψ (negSp S) T w f) := by
  have h := GlobalTheory.CjNeg.heis_negS hψ S T w (star f)
  have hc : GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj id (star f) = f := by
    funext y; simp [GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj]
  rw [hc] at h
  rw [h]; funext y; simp [GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj]

theorem symplO_negSp (S T : HSp D) (x y : WO S T) : symplO (negSp S) T x y = -symplO S T x y := by
  rw [GlobalTheory.ThetaSquare.symplO_eq, GlobalTheory.ThetaSquare.symplO_eq, GlobalTheory.CjNeg.symplOH_negS]; ring

theorem mem_ann_negSp {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {Γ : AddSubgroup (WO S T)} {w : WO S T}
    (hw : w ∈ Ann ψ S T Γ) : w ∈ Ann ψ (negSp S) T Γ := by
  have key : ∀ a b : WO S T, ψ (symplO S T a b) = 1 → ψ (symplO (negSp S) T a b) = 1 := fun a b h => by
    rw [symplO_negSp, AddChar.map_neg_eq_inv, h, inv_one]
  exact ⟨fun u hu => key _ _ (hw.1 u hu), fun e he u hu hh => key _ _ (hw.2 e he u hu hh)⟩

end GlobalTheory.CosPerm

open GlobalTheory.CosPerm in

theorem GlobalTheory.CosPerm.cosVec_perm : All fun {D} _ _ _ {G} W _ => ∀ i, i < D.R.m → ∀ κ, W.cosVec i κ ≠ 0 ∧ (∀ τ, IsFockVacAt (heisO W.ψ (G.pS (.chi i 0)) (G.pT (.chi i 0))) W.θ τ (cplxO (G.cartS W.cart (.chi i 0) τ) (G.onT W.cart (.chi i 0) τ)) (W.cosVec i κ)) ∧ VacG W.ψ _ _ (latRow G i) (star (W.cosVec i κ)) ∧ ∀ w ∈ Ann W.ψ _ _ (latRow G i), w.map (infPart D) = 0 → heisO W.ψ (G.V (.grid (i + 1) 0)) (G.V (.grid i 0)) w (star (W.cosVec i κ)) ∈ Submodule.span ℂ (Set.range fun κ' => (star (W.cosVec i κ') : WO (G.V (.grid (i + 1) 0)) (G.V (.grid i 0)) → ℂ)) := by
  intro D hD T L μ0 hL sc G W M hM i hi κ
  obtain ⟨h1, hdep, hfock⟩ := GlobalTheory.T.coset_vectors_nonzero_depth_fock_vacua D hD T L μ0 hL sc G W M hM i hi κ
  have hψ : IsStdChar D W.ψ (-1) := W.ψ_std
  have hth := (GlobalTheory.CjNeg.theta_heis_neg D W.ψ hψ (G.V (.grid (i + 1) 0)) (G.V (.grid i 0))).1 (star (W.cosVec i κ))
  have hcj : GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj id (star (W.cosVec i κ)) = W.cosVec i κ := by
    funext y; simp [GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj]
  rw [hcj] at hth
  refine ⟨h1, hfock, ⟨hth.2.1 hdep.1, fun u hu => ?_, fun e he u hu hh => ?_⟩, ?_⟩
  · rw [heisO_star hψ]; exact congrArg star (hdep.2.1 u hu)
  · rw [heisO_star hψ]; exact congrArg star (hdep.2.2 e he u hu hh)
  intro w hw hfin
  have hw' : w ∈ Ann W.ψ (G.pS (.chi i 0)) (G.pT (.chi i 0)) (depLat G (.chi i 0)) := mem_ann_negSp hw
  obtain ⟨e, he, hthe⟩ := W.cosVec_is
  have hthi := fun κ => hthe i hi κ
  obtain ⟨c₀, hc₀⟩ := GlobalTheory.T.heisenberg_offPart_vacuumCommutant_acts_by_scalar D hD T L μ0 hL sc G W M hM i hi e he w hw' hfin
  obtain ⟨c₃, h₃⟩ := GlobalTheory.T.heisenbergOperator_eigen_of_thetaVector_at_place D W.ψ (G.pS (.chi i 0)) (G.pT (.chi i 0)) e
    (latO (G.pS (.chi i 0)) (G.pT (.chi i 0)) (G.latS (.chi i 0) : Set _) (G.latT (.chi i 0) : Set _) fun _ => True)
    (W.vac i) (cosInd e κ) (W.cosVec i κ) ((1 - e - cA D e) • w) c₀ (hthi κ)
    (fun x hx => GlobalTheory.T.symplecticForm_offIdempotentPart_orthogonal_half D (G.pS (.chi i 0)) (G.pT (.chi i 0)) G.pl.W0 e he w x (Or.inl hx))
    (fun y hy => GlobalTheory.T.symplecticForm_offIdempotentPart_orthogonal_half D (G.pS (.chi i 0)) (G.pT (.chi i 0)) G.pl.W0 e he w y (Or.inr hy)) hc₀
  obtain ⟨c₂, h₂⟩ := GlobalTheory.T.conjugateHalfCommutant_acts_on_cosetVector_by_scalar D hD T L μ0 hL sc G W M hM i hi e he hthi w hw' hfin κ
  obtain ⟨κ', h₁⟩ := GlobalTheory.T.commutant_depth_lattice_permutes_coset_vectors D hD T L μ0 hL sc G W M hM i hi e he hthi w hw' hfin κ
  have hdec : w = e • w + (cA D e • w + (1 - e - cA D e) • w) := by
    rw [← add_smul, ← add_smul, show e + (cA D e + (1 - e - cA D e)) = 1 by ring, one_smul]
  have hne : ∀ a, W.ψ a ≠ 0 := fun a h => by
    have := AddChar.map_add_eq_mul W.ψ a (-a)
    rw [add_neg_cancel, AddChar.map_zero_eq_one, h, zero_mul] at this
    exact one_ne_zero this
  have e1 := GlobalTheory.OrientedHeis.heisO_heisO (ψ := W.ψ) (S := G.pS (.chi i 0)) (T := G.pT (.chi i 0))
    (cA D e • w) ((1 - e - cA D e) • w) (W.cosVec i κ)
  rw [h₃, heisO_smul_fun, h₂, smul_smul] at e1
  have e1' : heisO W.ψ (G.pS (.chi i 0)) (G.pT (.chi i 0)) (cA D e • w + (1 - e - cA D e) • w) (W.cosVec i κ) =
      (W.ψ (symplOH (G.pS (.chi i 0)) (G.pT (.chi i 0)) (cA D e • w) ((1 - e - cA D e) • w)))⁻¹ • ((c₃ * c₂) • W.cosVec i κ) := by
    rw [e1, inv_smul_smul₀ (hne _)]
  have e2 := GlobalTheory.OrientedHeis.heisO_heisO (ψ := W.ψ) (S := G.pS (.chi i 0)) (T := G.pT (.chi i 0))
    (e • w) (cA D e • w + (1 - e - cA D e) • w) (W.cosVec i κ)
  rw [← hdec, e1', heisO_smul_fun, heisO_smul_fun, h₁] at e2
  have hC : heisO W.ψ (G.pS (.chi i 0)) (G.pT (.chi i 0)) w (W.cosVec i κ) =
      ((W.ψ (symplOH (G.pS (.chi i 0)) (G.pT (.chi i 0)) (e • w) (cA D e • w + (1 - e - cA D e) • w)))⁻¹ *
        ((W.ψ (symplOH (G.pS (.chi i 0)) (G.pT (.chi i 0)) (cA D e • w) ((1 - e - cA D e) • w)))⁻¹ * (c₃ * c₂))) • W.cosVec i κ' := by
    rw [← smul_smul, ← smul_smul, e2, inv_smul_smul₀ (hne _)]
  rw [heisO_star hψ]
  change star (heisO W.ψ (G.pS (.chi i 0)) (G.pT (.chi i 0)) w (W.cosVec i κ)) ∈ _
  rw [hC, star_smul]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨κ', rfl⟩)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.JetScalarRationalTranslateStatement
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
theorem _root_.GlobalTheory.T.jet_scalar_rational_translate : GlobalTheory.FunPr.Hypotheses₂ → (∀ D, GlobalTheory.NormSum.Inp D) → ∀ {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type}
    {A : FamIn D.what₂.LL Γ Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks}
    (ch : Choice R), ch.Is → ∀ (p : Pair T), DefPair D.R.m p → ∀ (x : FinPt ch.G p.small) (y : FinPt ch.G p.big) (κ : ℂ), GlobalTheory.MovedKappaEx.JetKap ch p x y κ →
    ∀ (r : FinPt ch.G p.small) (r' : FinPt ch.G p.big), GlobalTheory.MovedKappaEx.RatFin _ r → GlobalTheory.MovedKappaEx.RatFin _ r' →
    ∃ c : ℂ, Mod1All c ∧ (∀ (q : ℕ) [Fact q.Prime],
        EqAt D q (GlobalTheory.SumSize.latAt ch.S.toGridChoice p.small x) (stdL D _) → EqAt D q (GlobalTheory.SumSize.latAt ch.S.toGridChoice p.big y) (stdL D _) →
        EqAt D q (GlobalTheory.SumSize.latAt ch.S.toGridChoice p.small (r * x)) (stdL D _) → EqAt D q (GlobalTheory.SumSize.latAt ch.S.toGridChoice p.big (r' * y)) (stdL D _) →
        GlobalTheory.MovedKappaEx.UnitAt q c) ∧
      GlobalTheory.MovedKappaEx.JetKap ch p (r * x) (r' * y) (c * κ) := by
  first | exact @GlobalTheory.RatMoveJets.exists_rat_move | exact GlobalTheory.RatMoveJets.exists_rat_move | (intros; apply GlobalTheory.RatMoveJets.exists_rat_move <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LocalVectorDownEdgeBoundaryStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_vector_down_edge_boundary : GlobalTheory.FunPr.Hypotheses₂ → GlobalTheory.RowClaim.Big fun {D} _ _ _ _ {T} _ _ _ _ _ {R} ch => ∀ (t : T) (j : Fin D.R.m) (g : Sch ch.G (.down t 0 j)), (j : ℕ) + 1 = D.R.m → HEq g (R.vX t) → ∃ c : ℂˣ, c ∈ xiVals R.toLevCh t ∧ ∀ e : AE D, IsIdemSum e (locPl ch.G t) → ∀ Φ : ch.G.Datum, IsLocVec ch.W (.mu t 0 j) e (ch.rm.vT 0 j) ((c : ℂ) • GlobalTheory.FlipStart.givenFn ch.S.B t Φ e (.down t 0 j)) g := by
  first | exact @GlobalTheory.FlipStart.topVec | exact GlobalTheory.FlipStart.topVec | (intros; apply GlobalTheory.FlipStart.topVec <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.MatchedMapsGaussianSum
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.KSplit
open scoped Matrix

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.HoweSplitSmall

section Local

open GlobalTheory.SplitFlip

theorem eq_coinv_or_eq_top (HB : GlobalTheory.Published.BernsteinUnitaryProductIrreducible)
    {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n d : ℕ}
    (hnd : 2 * n ≤ d + 1) {ν β : kˣ →* ℂˣ} (hν : IsSmU ν) (hβ : IsSmU β)
    (C N : Submodule ℂ (Matrix (Fin n) (Fin d) k → ℂ))
    (hC : C = Submodule.span ℂ {z | ∃ (g : GL (Fin n) k) (Ψ : Matrix (Fin n) (Fin d) k → ℂ),
        Ψ ∈ SB (Matrix (Fin n) (Fin d) k) ∧ z = omA ν β g 1 Ψ - Ψ})
    (hCN : C ≤ N) (hN : N ≤ SB (Matrix (Fin n) (Fin d) k))
    (hst : ∀ (h : GL (Fin d) k), ∀ Ψ ∈ N, omA ν β 1 h Ψ ∈ N) :
    N ≤ C ∨ SB (Matrix (Fin n) (Fin d) k) ≤ N := by
  obtain ⟨ϖ, hϖ⟩ := exists_isUnif (k := k)
  have dec : ∀ Ψ ∈ SB (Matrix (Fin n) (Fin d) k), ∃ Ψ₀ ∈ SB (Matrix (Fin n) (Fin d) k),
      (∀ Y : Matrix (Fin n) (Fin d) k, Y.rank ≠ n → Ψ₀ Y = 0) ∧ Ψ - Ψ₀ ∈ C := by
    intro Ψ hΨ
    obtain ⟨Ψ₀, h1, h2, h3⟩ := GlobalTheory.SmallRankCoinv.exists_fullRank_sub_mem k n d ν ϖ hϖ (hν.2 ϖ) hnd Ψ hΨ
    refine ⟨Ψ₀, h1, h2, ?_⟩
    rw [hC]
    refine Submodule.span_mono ?_ h3
    rintro _ ⟨g, Ψ', hΨ', rfl⟩
    refine ⟨invT g, Ψ', hΨ', ?_⟩
    congr 1
    funext Y
    simp only [omA, omB, map_one, Units.val_one, Matrix.mul_one, mul_one, apow_one, invT_inv_val, gdet_invT, map_inv,
      inv_inv, apow_inv, neg_div, neg_neg]
  rcases GlobalTheory.T.span_character_translates_coinvariant HB k n d (by omega) ν β hν.1 hν.2 hβ.1 hβ.2 N (hC ▸ hCN) hN hst with h | h
  · left
    intro Ψ hΨ
    obtain ⟨Ψ₀, -, h2, h3⟩ := dec Ψ (hN hΨ)
    have h4 : Ψ₀ ∈ N := by simpa using N.sub_mem hΨ (hCN h3)
    have h5 : Ψ₀ ∈ C := hC ▸ h Ψ₀ h4 h2
    simpa using C.add_mem h3 h5
  · right
    intro Ψ hΨ
    obtain ⟨Ψ₀, h1, h2, h3⟩ := dec Ψ hΨ
    simpa using N.add_mem (hCN h3) (h Ψ₀ h1 h2)

theorem isSmU_inv {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {ν : kˣ →* ℂˣ} (h : IsSmU ν) : IsSmU ν⁻¹ := by
  refine ⟨Subgroup.isOpen_mono (H₁ := ν.ker) (fun x hx => ?_) h.1, fun x => ?_⟩
  · rw [MonoidHom.mem_ker, MonoidHom.inv_apply, hx, inv_one]
  · rw [MonoidHom.inv_apply, Units.val_inv_eq_inv_val, norm_inv, h.2, inv_one]

end Local

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

omit [NumberField E] in

theorem one_mem_UAt {n : ℕ} (Y : Spc F E n) (v : Pl F) : (1 : UA σ Y.J) ∈ UAt σ Y (evFin F v) := fun u _ => by
  rw [show mat (1 : UA σ Y.J) = 1 from rfl, sub_self, smul_zero]

theorem surj_herm {B : Base F E} {n r s : ℕ} {X : Spc F E n} (hB : B.IsGood σ) (hX : X.IsHerm σ B r s) {v : Pl F}
    (t : E →ₐ[F] Fv F v) (g : GL (Fin n) (Fv F v)) : ∃ x ∈ UAt σ X (evFin F v), locMat t 1 x = g := by
  have hJ : IsUnit (X.J.map t).det := by
    obtain ⟨φ⟩ : Nonempty (F →+* ℂ) := inferInstance
    have h0 := GlobalTheory.LeviAtPlace.det_ne_zero_of_sig (hX.sig (InfinitePlace.mk φ))
    have h1 : X.J.det ≠ 0 := fun e => h0 (by
      rw [show X.J.map _ = RingHom.mapMatrix _ X.J from rfl, ← RingHom.map_det, e, map_zero])
    rw [show X.J.map t = (t : E →+* Fv F v).mapMatrix X.J from rfl, ← RingHom.map_det]
    exact isUnit_iff_ne_zero.2 ((map_ne_zero _).2 h1)
  refine ⟨GlobalTheory.LeviAtPlace.leviHom hB.cm t X.J hJ hX.herm g, GlobalTheory.LeviAtPlace.lift_sub_one_at v _, Units.ext ?_⟩
  rw [locMat_val, GlobalTheory.LeviAtPlace.leviHom_map_piW, GlobalTheory.LeviAtPlace.locMat, GlobalTheory.LeviAtPlace.pairMat_fst]
  simp

theorem thetaSub_eq (hP : GlobalTheory.FunPr.Hypotheses₂) {B : Base F E} {n d : ℕ} {X : Spc F E n} {W : Spc F E d} {M : Model σ X W}
    {χX χW : Chr F E} {om : Rep σ X W} {r s r' s' : ℕ} (P : IsPair B M χX χW om r s r' s') (hnd : 2 * n ≤ d + 1)
    {v : Pl F} (t : E →ₐ[F] Fv F v) {N : Submodule ℂ ((Fin n × Fin d → Fv F v) → ℂ)} (hN : GlobalTheory.Published.ThetaSub om v N) :
    N = augAt om v ∨ N = SB _ := by
  obtain ⟨ι, hι⟩ := GlobalTheory.T.exists_linear_witt_model_local hP F E σ B n d X W M χX χW om r s r' s' P v t 1 1
  have act := GlobalTheory.T.linear_witt_model_unitary_action hP F E σ B n d X W M χX χW om r s r' s' P v t 1 1 ι hι
  have hex := (GlobalTheory.T.theta_action_exists hP F E σ B n d X W M χX χW om r s r' s' P v).1
  have hb := Model.IsLin.bij hι
  have hν := isSmU_inv (GlobalTheory.T.splitPlaceCharacterComponent_smooth_unitary_conductor F E χW P.hW v t).1
  have hβ := (GlobalTheory.T.splitPlaceCharacterComponent_smooth_unitary_conductor F E χX P.hX v t).1
  have haug : augAt om v ≤ SB _ := hN.1.trans hN.2.1
  have pull : ∀ Q : Submodule ℂ ((Fin n × Fin d → Fv F v) → ℂ), Q ≤ SB _ → ∀ φ ∈ SB (Fin n × Fin d → Fv F v),
      ι φ ∈ Q.map ι → φ ∈ Q := by
    rintro Q hQ φ hφ ⟨ψ, hψ, e⟩
    rw [← hb.injOn (hQ hψ) hφ e]
    exact hψ
  have hC : Submodule.span ℂ {z | ∃ (g : GL (Fin n) (Fv F v)) (Ψ : Matrix (Fin n) (Fin d) (Fv F v) → ℂ),
      Ψ ∈ SB (Matrix (Fin n) (Fin d) (Fv F v)) ∧
        z = GlobalTheory.SplitFlip.omA (chrW χW t)⁻¹ (chrW χX t) g 1 Ψ - Ψ} ≤ (augAt om v).map ι := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨g, Ψ, hΨ, rfl⟩
    obtain ⟨φ, hφ, rfl⟩ := hb.surjOn hΨ
    obtain ⟨x, hx, rfl⟩ := surj_herm P.base P.herm t g
    obtain ⟨φ₁, ⟨h1, H⟩, -⟩ := hex x hx 1 (one_mem_UAt _ v) φ hφ
    refine ⟨φ₁ - φ, Submodule.subset_span ⟨x, hx, φ, hφ, φ₁, h1, H, rfl⟩, ?_⟩
    rw [map_sub, act x hx 1 (one_mem_UAt _ v) φ hφ φ₁ h1 H, map_one]
  rcases eq_coinv_or_eq_top hP.bernsteinUnitaryProductIrreducible hnd hν hβ _ (N.map ι) rfl
    (hC.trans (Submodule.map_mono hN.1)) (by rintro _ ⟨φ, hφ, rfl⟩; exact hb.mapsTo (hN.2.1 hφ)) (by
      rintro h _ ⟨φ, hφ, rfl⟩
      obtain ⟨x, hx, rfl⟩ := GlobalTheory.T.local_unitary_matrix_surjective F E σ B d W r' s' P.base P.skew v t 1 h
      obtain ⟨φ₁, ⟨h1, H⟩, -⟩ := hex 1 (one_mem_UAt _ v) x hx φ (hN.2.1 hφ)
      refine ⟨φ₁, hN.2.2 x hx φ hφ φ₁ h1 H, ?_⟩
      rw [act 1 (one_mem_UAt _ v) x hx φ (hN.2.1 hφ) φ₁ h1 H, map_one]) with h | h
  · exact Or.inl (le_antisymm (fun φ hφ => pull _ haug φ (hN.2.1 hφ) (hC (h ⟨φ, hφ, rfl⟩))) hN.1)
  · exact Or.inr (le_antisymm hN.2.1 fun φ hφ => pull _ hN.2.1 φ hφ (h (hb.mapsTo hφ)))

theorem isHecke_div {χ₁ χ₂ : Chr F E} (h₁ : IsHecke F E χ₁) (h₂ : IsHecke F E χ₂) : IsHecke F E (χ₁ / χ₂) := by
  refine ⟨?_, fun x => ?_⟩
  · show Continuous fun x => χ₁ x / χ₂ x
    exact h₁.1.div' h₂.1
  · rw [MonoidHom.div_apply, h₁.2 x, h₂.2 x, div_one]

theorem resEtaPow_div {K : Subgroup (AF F)ˣ} {χ χ' : Chr F E}
    {m m' : ℕ} (h : ResEtaPow K χ m) (h' : ResEtaPow K χ' m') : ResEtaPow K (χ / χ') (m + m') := by
  intro u
  rw [MonoidHom.div_apply, Circle.coe_div, h u, h' u]
  split_ifs
  · simp
  · rw [div_eq_mul_inv, ← inv_pow, inv_neg_one, ← pow_add]

theorem isPair_small {a a' : ℕ} {B : Base F E} {G : Geo σ a a'} {X : Chars F E} {om : Rep σ G.V G.W}
    {om' : Rep σ G.V' G.W} (h : IsTriple B G X om om') :
    IsPair B G.M' X.α (X.α / X.β) om' G.q (a' - G.q) (a + a' - (G.p + G.q)) (G.p + G.q) :=
  ⟨h.base, h.geo.hV', h.geo.hW, h.geo.hM', h.chars.heckeα, isHecke_div h.chars.heckeα h.chars.heckeβ, h.chars.resα,
    add_comm a' a ▸ resEtaPow_div h.chars.resα h.chars.resβ, h.weil'⟩

theorem howe_split_ker_small : GlobalTheory.FunPr.Hypotheses₂ → GlobalTheory.Published.MinguezThetaGL →
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (a a' : ℕ) (G : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo σ a a') (Xc : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars F E)
    (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V G.W) (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V' G.W)
    (R : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.RealMaps F a a') (Rf : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.FinMaps F a a'),
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsMatched Bs G Xc om om' R Rf →
    ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F, Nonempty (E →ₐ[F] Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) →
      (∃ L : ℕ, ∀ (m : ℕ) (N : Fin m → Submodule ℂ ((Fin a' × Fin (a + a') → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) → ℂ)),
        StrictMono N → (∀ i, GlobalTheory.Published.ThetaSub om' v (N i)) → m ≤ L) ∧
      ∀ N : Submodule ℂ ((Fin a' × Fin (a + a') → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) → ℂ), GlobalTheory.Published.ThetaSub om' v N →
        N ≠ GlobalTheory.WeilM.SB _ → ∀ φ ∈ N, Rf.p' v φ = 0 := by
  intro hP _ F E _ _ _ _ _ σ Bs a a' G Xc om om' R Rf hM v ⟨t⟩
  have hlt := hM.triple.geo.lt
  have key := fun N hN => thetaSub_eq (N := N) hP (isPair_small hM.triple) (by omega) t hN
  refine ⟨⟨2, fun m N hmono hN => ?_⟩, fun N hN hne φ hφ => ?_⟩
  · by_contra hm
    have h01 : N ⟨0, by omega⟩ < N ⟨1, by omega⟩ := hmono (by simp [Fin.lt_def])
    have h12 : N ⟨1, by omega⟩ < N ⟨2, by omega⟩ := hmono (by simp [Fin.lt_def])
    rcases key _ (hN ⟨1, by omega⟩) with h | h
    · exact absurd (h ▸ (hN _).1.trans_lt h01 : augAt om' v < augAt om' v) (lt_irrefl _)
    · exact absurd (h12.trans_le (hN _).2.1) (h ▸ lt_irrefl _)
  · rcases key N hN with h | h
    · exact hM.fin.inv' v (h ▸ hφ)
    · exact absurd h hne

end GlobalTheory.HoweSplitSmall

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SeesawUnfoldingLimitStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.seesaw_unfolding_limit : GlobalTheory.FunPr.Hypotheses₂ → ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (W W₁ X : HSp D) (A : Fr W) (A₁ : Fr W₁)
    (B : Fr X) (α β : (AE D)ˣ →* Circle) (ν : Measure (GA D W)) (𝓕 : Set (GA D W)) (ν₁ : Measure (GA D W₁))
    (𝓕₁ : Set (GA D W₁)) (ωA : WRep W X) (ωB : WRep W₁ X) (e : Fin X.rank ≃ Fin (W.rank + W₁.rank))
    (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo D.sp.cm.sig W.rank W₁.rank)
    (Xc : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars D.host.F D.host.E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V Γ.W)
    (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V' Γ.W) (cA : Matrix (Fin W.rank) (Fin (W.rank + W₁.rank)) (AE D) ≃+ WO W X)
    (cB : Matrix (Fin W₁.rank) (Fin (W.rank + W₁.rank)) (AE D) ≃+ WO W₁ X),
    IsInfFam θ → IsTriple W W₁ X α β → IsOver ψ θ A A₁ B α β ν 𝓕 ν₁ 𝓕₁ ωA ωB e Bs Γ Xc om om' cA cB →
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple Bs Γ Xc om om' →
    ∀ Pi rf rl p p', IsMatch ψ θ A A₁ B α β ωA ωB Pi rf rl p p' →
    ∀ k ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.KInf D.sp.cm.sig Γ.W Bs.emb, ∀ Φ ∈ kerPD ψ θ A₁ B Bs Γ cB p', om' (1, k) Φ ∈ kerPD ψ θ A₁ B Bs Γ cB p' := by
  first | exact @GlobalTheory.SquareAgree.KerStabCpt.stabCpt_mem_kerPD | exact GlobalTheory.SquareAgree.KerStabCpt.stabCpt_mem_kerPD | (intros; apply GlobalTheory.SquareAgree.KerStabCpt.stabCpt_mem_kerPD <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SplitLocalFrameOddLevelStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin
open ValuativeRel
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.split_local_frame_odd_level : OnStd fun {D} _ _ {sc} {G} W F => ∀ σ (h : 2 * (σ + 1) + 2 ≤ D.R.m), ∀ v ∈ G.pl.S0,
  ∃ (k : Type) (_ : Field k) (_ : ValuativeRel k) (_ : TopologicalSpace k) (_ : IsNonarchimedeanLocalField k)
    (p : GlobalTheory.FinPl.SplitPt D k) (β : GlobalTheory.FinPl.Frame p (G.V (.grid (2 * (σ + 1) + 1) 0)) (Fin (G.V (.grid (2 * (σ + 1) + 1) 0)).rank))
    (ι ι' : Fin (σ + 1) → Fin (G.V (.grid (2 * (σ + 1) + 1) 0)).rank) (s t : Fin (σ + 1) → k),
  p.v = v ∧ Formalism.L2.NTheta.IsIdemAt p.e (G.pl.w v) ∧
  β.IsLat (G.Λ (.grid (2 * (σ + 1) + 1) 0)) (Submodule.pi Set.univ fun _ => (1 : Submodule 𝒪[k] k)) ∧
  Function.Injective ι ∧ Function.Injective ι' ∧ (∀ a b, ι' b ≠ ι a) ∧
  (∀ q, s q • (β.b' *ᵥ fun i => p.pr (xZero (F.dJ (σ + 1) h) i q)) = Pi.single (ι q) 1) ∧
  (∀ q, t q • ((fun i => p.pr (cA D (xZero (F.dJ (σ + 1) h) i q))) ᵥ*
    ((G.V (.grid (2 * (σ + 1) + 1) 0)).gram.map (fun c => p.pr (incA D c)) * β.b)) = Pi.single (ι' q) 1) ∧
  ∀ a ∈ (pcBF W F (σ + 1) h).A₁,
    (∀ q i, ∃ z ∈ IsLocalRing.maximalIdeal 𝒪[k] ^ G.pl.depth sc v, (z : k) = s q * (β.b' *ᵥ fun j => p.pr (a j q)) i) ∧
    (∀ q i, ∃ z ∈ IsLocalRing.maximalIdeal 𝒪[k] ^ G.pl.depth sc v, (z : k) = t q * ((fun j => p.pr (cA D (a j q))) ᵥ*
      ((G.V (.grid (2 * (σ + 1) + 1) 0)).gram.map (fun c => p.pr (incA D c)) * β.b)) i) := by
  first | exact @GlobalTheory.AscFin.FrameBF.frame_bf | exact GlobalTheory.AscFin.FrameBF.frame_bf | (intros; apply GlobalTheory.AscFin.FrameBF.frame_bf <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.StarAdjointMemHatLatticeStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.star_adjoint_mem_hat_lattice : OnStd fun {D} _ _ {sc} {G} W F => ∀ (h : 2 * 0 + 2 ≤ D.R.m), ∀ u ∈ (pcBF W F 0 h).Γ₀, ∀ e : AE D, IsIdemSum e G.pl.W0 → e • (incA D D.host.xi0⁻¹ • GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.starAdj _ _ (((F.oB 0 h).resS (G.V (.core (2 * 0 + 1))) u).2)) ∈ hatMx (G.modul • homLat (G.Λ (.core (2 * 0 + 1))) (Submodule.span (𝓞 D.host.E) {F.ζ 0})) := by
  first | exact @GlobalTheory.AscFin.BoxBF.lineAdj_zero_dep | exact GlobalTheory.AscFin.BoxBF.lineAdj_zero_dep | (intros; apply GlobalTheory.AscFin.BoxBF.lineAdj_zero_dep <;> assumption)
end

