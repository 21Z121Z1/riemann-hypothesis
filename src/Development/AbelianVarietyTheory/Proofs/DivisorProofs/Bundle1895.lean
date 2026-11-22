import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1816
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1833
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HighestWeightBelow
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0258
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0354
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.LatticeUnitNormSqNonneg
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0278
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1063
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaVacuaConjugatesCmPoints
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1852
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0296
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0841
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1869
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0014
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1800
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsRepsOfFiniteIndex
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0119
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0026
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContDiffDerivSnoc
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0880
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0871
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0976
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0974
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1864
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsINeZeroKind
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1036
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1865
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OrientedHermitianFormQuadSumEqTrace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TranslationInvariantFormConstL2
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0004
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0533
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0142
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0013
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1317
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1090
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1871
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1765
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1777
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1453
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RamificationIdxEqOneOfIsSquare
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0201
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0331
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.CentralInvolutionRing
import Development.AbelianVarietyTheory.Definitions.Divisors.FinitePrimesUnder
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1679
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1681
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsSelfDualPairGaloisConjugateHomLattice
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1870
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1689
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilDatumTwistByHeckeCharactersTrivialBase
import Formalism.LocalToGlobal.IndefiniteReal.DatumF
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.VacuumUnderAdelicPairModulusOne
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaSpanRationalTranslatesVacuum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1721
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1708
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0264

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaCombinationJetsAlgebraicConjEqConjSeries
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim GlobalTheory.TestLat
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.SumSize GlobalTheory.KerConjMean
open GlobalTheory.ThetaConj

namespace GlobalTheory.ConjJetComb

theorem applyAt0_mono (D : D7) {N N' : ℕ} (α : Mono D N N') (G : VC D N N' → ℂ) :
    GL3Theta.applyAt0 D (MvPolynomial.monomial α 1) G
      = ((α.prod fun _ n => n.factorial : ℕ) : ℂ) * Formalism.MainNotions.TaylorLogMetric.taylor D G α := by
  classical
  unfold Formalism.MainNotions.GL3Theta.applyAt0
  rw [MvPolynomial.support_monomial, if_neg one_ne_zero, Finset.sum_singleton, MvPolynomial.coeff_monomial,
    if_pos rfl, one_mul]
  simp [Finsupp.prod]

theorem jet_of_cjF {D : D7} {N N' : ℕ} {ρ : Qbar →ₐ[ℚ] ℂ} {F F' : VC D N N' → ℂ} (h : CjF D Qbar ρ F F')
    (α : Mono D N N') :
    GL3Theta.applyAt0 D (MvPolynomial.monomial α 1) F ∈ Qbar ∧
      Formalism.MainNotions.StandardLatticesGL3.cj Qbar ρ (GL3Theta.applyAt0 D (MvPolynomial.monomial α 1) F) =
        GL3Theta.applyAt0 D (MvPolynomial.monomial α 1) (fnConj D Qbar ρ F) := by
  rw [h.fnConj_eq, applyAt0_mono, applyAt0_mono]
  set n : ℕ := α.prod fun _ n => n.factorial
  have hn : (n : ℂ) ∈ Qbar := natCast_mem _ n
  refine ⟨mul_mem hn (h.2.2 α).1, ?_⟩
  rw [cj_mul ρ hn (h.2.2 α).1, (h.2.2 α).2, cj_mem ρ hn]
  have : (⟨(n : ℂ), hn⟩ : Qbar) = (n : Qbar) := rfl
  rw [this, map_natCast]

theorem conj_jet : ∀ (D : D7), GlobalTheory.NormSum.Inp D → ∀ (δ t0 : ℂ), Crv D D.host.ccK δ → GL3Theta.IsTwoTorsionPointUnkilled D (lamOf D D.host.ccK δ) t0 →
    ∀ (a b : ℕ), Even (a * b) → ∀ (e0 : VC D a b → ℂ), oddE0 D D.host.ccK δ t0 a b e0 →
    ∀ (Ls : Submodule (𝓞 D.host.E) (Fin a → D.host.E)) (Lt : Submodule (𝓞 D.host.E) (Fin b → D.host.E)), SD D Ls → SD D Lt →
    ∀ (κ : ℂ), Mod1All κ → ∀ (k n : ℕ), 0 < k → ∀ (r : Fin n → Qbar) (s : Fin n → VC D a b),
    (∀ i, k • s i ∈ La D (tor0 D D.host.ccK δ) Ls Lt) → ∀ (ρ' : Qbar →ₐ[ℚ] ℂ) (m : Formalism.L2.Ker.DVar D.what₂.Tau a b →₀ ℕ),
      GL3Theta.applyAt0 D (MvPolynomial.monomial m 1) (fun z => κ * ∑ i, (r i : ℂ) * U D (tor0 D D.host.ccK δ) (s i)
              (Iop D (tor0 D D.host.ccK δ) (La0 D (tor0 D D.host.ccK δ) _ _) (La D (tor0 D D.host.ccK δ) Ls Lt) e0) z) ∈ Qbar ∧
      Formalism.MainNotions.StandardLatticesGL3.cj Qbar ρ' (GL3Theta.applyAt0 D (MvPolynomial.monomial m 1) (fun z => κ * ∑ i, (r i : ℂ) * U D (tor0 D D.host.ccK δ) (s i)
                (Iop D (tor0 D D.host.ccK δ) (La0 D (tor0 D D.host.ccK δ) _ _) (La D (tor0 D D.host.ccK δ) Ls Lt) e0) z)) =
        GL3Theta.applyAt0 D (MvPolynomial.monomial m 1) (fnConj D Qbar ρ' fun z => κ * ∑ i, (r i : ℂ) * U D (tor0 D D.host.ccK δ) (s i)
          (Iop D (tor0 D D.host.ccK δ) (La0 D (tor0 D D.host.ccK δ) _ _) (La D (tor0 D D.host.ccK δ) Ls Lt) e0) z) := by
  intro D _ δ t0 hc ht0 N N' _ e0 he Ls Lt hL₁ hL₁' κ hκ k₀ n hk₀ r s hs ρ m
  have hG := (GlobalTheory.T.inducedType_thetaGenusOne_permutes D).1
  have hL := GlobalTheory.MovedVacuum.sd_stdL D N
  have hL' := GlobalTheory.MovedVacuum.sd_stdL D N'
  have hGth := he.1
  obtain ⟨b, κ₀, hb, hκ₀, rfl⟩ := he.2.2.2.1
  obtain ⟨k, hk, hC⟩ := GlobalTheory.T.exists_homLattice_commensurable_orthonormal D N N' _ b _ _ hb hL hL'
  have kB : KLat D (tor0 D D.host.ccK δ) (LaB D (tor0 D D.host.ccK δ) b) := Or.inl ⟨_, b, hb, rfl⟩
  have kL : KLat D (tor0 D D.host.ccK δ) (La D (tor0 D D.host.ccK δ) _ _) := Or.inr ⟨_, _, hL, hL', rfl⟩
  obtain ⟨-, -, c1, c2, -⟩ := GlobalTheory.T.coords_along_orthonormal_realSubfield_basis D hG D.host.ccK δ N N' _ b hb
  obtain ⟨d1, d2⟩ := GlobalTheory.T.halfPeriodTheta_differentiable_and_signedTranslate_invariant D hG D.host.ccK δ hc t0 ht0
  have hth0 := GlobalTheory.T.orthoProductTheta_mem_thetaSpace_of_lattice D (tor0 D D.host.ccK δ) N N' _ b _ c1 c2 d1 d2
  have hCb : Comm D b k (Set.range b) := by simpa using (comm_range D b).mul k
  obtain ⟨m1, -⟩ := conj_iop hc ρ hb (GlobalTheory.T.pullB_th0_mem_tr D _ δ hc t0 ht0 N N' _ b hb) hk
    hCb hC (LaB_eq D _ b ▸ kB) kL (LaB_eq D _ b ▸ hth0)
  rw [← LaB_eq, ← La_eq] at m1
  have hGm := Submodule.smul_mem _ (⟨κ₀, hκ₀.1⟩ : Qbar) m1
  obtain ⟨k₁, hk₁, hC₁⟩ := GlobalTheory.T.exists_homLattice_commensurable_orthonormal D N N' _ b Ls Lt hb hL₁ hL₁'
  have hC₂ := hC₁.mul k
  rw [mul_comm k k₁] at hC₂
  obtain ⟨m2, -⟩ := conj_iop hc ρ hb hGm (Nat.mul_pos hk₁ hk) (hC.mul k₁) hC₂ kL
      (Or.inr ⟨Ls, Lt, hL₁, hL₁', rfl⟩) hGth
  have hsB : ∀ i, (k₀ * k₁) • s i ∈ LaB D (tor0 D D.host.ccK δ) b := fun i => by
    rw [mul_nsmul]
    exact nsmul_mem_LaB (isTraceCompatibleTorusEmbedding_standardTorus D hG _ δ) (GlobalTheory.T.idealPeriodLattice_of_curveDatum D hG _ δ hc).2.2.2.2 hC₁ (hs i)
  have m3 := fun i => GlobalTheory.T.torsionTranslate_mem_thetaPullbackSpan D _ δ hc N N' _ b hb _ m2 (s i) _ (Nat.mul_pos hk₀ hk₁) (hsB i)
  choose F' hF' using fun i => galRel_all hc ρ hb (m3 i) one_pos
  exact jet_of_cjF ((CjF.sum Finset.univ fun i _ => (hF' i).1.mul (r i).2).mul hκ.1) m

end GlobalTheory.ConjJetComb
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaKernelContinuousFunctionalStatement
section
open scoped TensorProduct NNReal Matrix ENNReal
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.theta_kernel_continuous_functional : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W)
    (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' → ∀ φ ∈ SB (Fin n × Fin d → Af F), ∀ (g : UA σ X.J) (h : UA σ W.J),
    ∃ T : SInf F (Fin n × Fin d) →L[ℂ] ℂ, ∀ f : SInf F (Fin n × Fin d), theta om (pureA F f φ) g h = T f := by
  first | exact @GlobalTheory.ThetaKernelCont.theta_pureA_clm | exact GlobalTheory.ThetaKernelCont.theta_pureA_clm | (intros; apply GlobalTheory.ThetaKernelCont.theta_pureA_clm <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaKernelFinitePointMemSpanRationalFormLiftsStatement
section
open NumberField Matrix IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaKernel_finitePoint_mem_span_rationalFormLifts : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : Formalism.L2.DIV.FamIn D.what₂.LL G Pl0 T0 D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Hk3.Core R F → ∀ (i : Fin D.R.m) (t : T0), VStd D i → ∀ h ∈ GfC (Vc D i), ∀ (w : (R.cV i).W) (u : ∀ ρ, lowT (R.MW i (sg0 D A)) ρ), (fun g : GA D (Wc D i) => thetaKO (R.ωP i t) h g (R.ptP i t (R.ioP i (PiTensorProduct.tprod ℂ u) w))) ∈ Submodule.span ℂ (Set.range fun x₀ : A.fam.amb.FL i t => (R.thF i t (jVx R i t x₀) (fun ρ => u ρ) : GA D (Wc D i) → ℂ)) := by
  first | exact @GlobalTheory.KernelSpanCore.kernel_mem_span_core | exact GlobalTheory.KernelSpanCore.kernel_mem_span_core | (intros; apply GlobalTheory.KernelSpanCore.kernel_mem_span_core <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaLiftMemMultiplicitySpaceBaseLevel
section
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ThetaLevelP

set_option maxHeartbeats 1000000 in

theorem thF_mem_conj {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (hIs : R.toLevCh.Is A.μ0)
    (hMod : R.IsModels) (hTh : R.IsThP) (i : Fin D.R.m) (t : T) (P : LevelP R.Pg D.R.r ℂ) (y : (R.HV i t).H)
    (hy : R.extV i t y ∈ RecTie.levSubV (Vc D i) (R.cV i).W (levS _ (R.βV i) (RecTie.datVP R i t P))
      (levChi _ (R.βV i) (RecTie.datVP R i t P))) :
    R.thF i t y ∈ Mult R.θ (R.MW i (sg0 D A)) (levS _ (R.βW i) (R.datWp i P.conj))
      (levChi _ (R.βW i) (R.datWp i P.conj)) := by
  have hW := (GlobalTheory.MultMem.mem_mult_iff _ _ _ _ _ _ _ _).1 (hTh.thF_mem i t y)
  refine (GlobalTheory.MultMem.mem_mult_iff _ _ _ _ _ _ _ _).2 ⟨hW.aut, hW.cusp, fun v k' hk' g => ?_, hW.equiv, hW.cont⟩
  obtain ⟨g0, hl', hc'⟩ := GlobalTheory.LevelRankR.exists_lift_of_mem_level R i P.conj k' hk'
  have hL := (GlobalTheory.StepLifts.lifts_exist R hIs i).1 t
  have hx := hL g0
  clear hL
  rcases hx with ⟨κ, hl⟩
  have h1 := GlobalTheory.T.lift_mem_levelOfDatum_flagCharacter R i t P
  let g1 : P.H := ⟨g0.1, g0.2⟩
  have h3 := h1 g1 κ hl
  clear h1
  have hf0 : levChi (Vc D i) (R.βV i) (flagL (R.datVt i t)) κ ≠ 0 := Units.ne_zero _
  have hy' : ∀ k ∈ levS (Vc D i) (R.βV i) (RecTie.datVP R i t P), ∀ h,
      R.extV i t y (h * k) = levChi (Vc D i) (R.βV i) (RecTie.datVP R i t P) k • R.extV i t y h := hy
  have e1 := hy' κ h3.1
  have e2 := h3.2
  clear hy' hy h3
  have hnum : (((P.chi g1 : ℂˣ) : ℂ))⁻¹ = (levChi (Vc D i) (R.βV i) (flagL (R.datVt i t)) κ)⁻¹ *
      levChi (Vc D i) (R.βV i) (RecTie.datVP R i t P) κ := by
    rw [e2]
    field_simp
  have hsh : ∀ h, R.extV i t ((((P.chi g1 : ℂˣ) : ℂ))⁻¹ • y) h =
      (levChi (Vc D i) (R.βV i) (flagL (R.datVt i t)) κ)⁻¹ • R.extV i t y (h * κ) := by
    intro h
    have e3 : R.extV i t ((((P.chi g1 : ℂˣ) : ℂ))⁻¹ • y) h = (((P.chi g1 : ℂˣ) : ℂ))⁻¹ • R.extV i t y h :=
      congrFun ((R.extV i t).map_smul _ y) h
    refine e3.trans ?_
    refine Eq.trans ?_ (congrArg (fun w => (levChi (Vc D i) (R.βV i) (flagL (R.datVt i t)) κ)⁻¹ • w) (e1 h).symm)
    refine (congrArg (fun a : ℂ => a • R.extV i t y h) hnum).trans ?_
    exact mul_smul _ _ _
  have key := GlobalTheory.T.thetaLift_intertwines_lifts_smoothVectors R hIs hMod hTh i t g0.1 κ k' hl hl' y _ hsh v g
  have hcc : levChi (Wc D i) (R.βW i) (R.datWp i P.conj) k' = (((P.chi g1 : ℂˣ) : ℂ))⁻¹ := by
    rw [hc']
    change (((P.chi⁻¹) g1 : ℂˣ) : ℂ) = _
    rw [MonoidHom.inv_apply, Units.val_inv_eq_inv_val]
  have e4 : R.thF i t ((((P.chi g1 : ℂˣ) : ℂ))⁻¹ • y) v g = (((P.chi g1 : ℂˣ) : ℂ))⁻¹ * R.thF i t y v g := by
    have e5 := congrFun (congrArg (fun T : MMap (R.MW i (sg0 D A)) => T v) ((R.thF i t).map_smul (((P.chi g1 : ℂˣ) : ℂ))⁻¹ y)) g
    exact e5
  exact key.symm.trans (e4.trans (congrArg (· * R.thF i t y v g) hcc.symm))

set_option maxHeartbeats 1000000 in

theorem thF_mem_level : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks), ∀ F : Face D A, R.toLevCh.Is A.μ0 → R.IsModels → R.IsThP → A.v0 = InfinitePlace.mk D.what₂.embLL → ∀ (b : Bool) (i : Fin D.R.m) (t : T) (y : (R.HV i t).H), R.extV i t y ∈ RecTie.levSubV (Vc D i) (R.cV i).W (levS _ (R.βV i) (RecTie.datVP R i t (R.levR F b))) (levChi _ (R.βV i) (RecTie.datVP R i t (R.levR F b))) → R.thF i t y ∈ Mult R.θ (R.MW i (sg0 D A)) (levS _ (R.βW i) (R.datWp i (R.levL F b (sg0 D A)))) (levChi _ (R.βW i) (R.datWp i (R.levL F b (sg0 D A)))) := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F hIs hMod hTh hv b i t y hy
  rw [GlobalTheory.Proof.LevelCharacterConjugate.liftLevel_fixedEmbedding_eq_conj_rowLevel R F b hv]
  exact thF_mem_conj R hIs hMod hTh i t (R.levR F b) y hy

end GlobalTheory.ThetaLevelP
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraceSecondPos
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames GlobalTheory.BigNZ GlobalTheory.AdelicU
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ Num IsTripleOf IsDatumA skewGram blkU conjU UB)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chars Rep IsTriple UAt ratU mat Acts SInf)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.RouteCoordsW

open GlobalTheory.RouteCoords GlobalTheory.WeilM GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation

theorem trace_second_pos {A : Type} [CommRing A] (c : A →+* A) {n b : ℕ} (hc : ∀ z, c (c z) = z) (ξ : A) (hξ : c ξ = -ξ)
    (g : Matrix (Fin n) (Fin n) A) (p pi : Matrix (Fin b) (Fin b) A) (hg : (g.map c)ᵀ = g) (hp : (p.map c)ᵀ = p)
    (hpi : pi * p = 1) (Z Z' : Matrix (Fin n) (Fin b) A) :
    c (ξ * (pi * ((-(Z'.map c * p)).map c)ᵀ * g * (-(Z.map c * p))).trace) =
      -(ξ * (Z * pᵀ * (Z'.map c)ᵀ * gᵀ).trace) := by
  rw [← trace_second c hc ξ hξ g p pi hg hp hpi Z Z', ← map_neg, ← mul_neg, ← trace_neg]
  congr 3
  simp only [Matrix.neg_mul, neg_neg]

attribute [local instance] Formalism.BasicNotions.Host.cmStar

end GlobalTheory.RouteCoordsW
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TranslationInvariantFormConstL2Statement
section
open MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.translation_invariant_form_const_l2 : ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (μ : @MeasureTheory.Measure V (borel V)), @MeasureTheory.Measure.IsAddHaarMeasure V _ _ (borel V) μ →
    ∀ (T : SchwartzMap V ℂ →L[ℂ] SchwartzMap V ℂ),
    (∀ (a : V) (f f' g g' : SchwartzMap V ℂ), (∀ x, f' x = f (x + a)) → (∀ x, g' x = g (x + a)) →
      @MeasureTheory.integral V ℂ _ _ (borel V) μ (fun x => T f' x * starRingEnd ℂ (T g' x)) =
        @MeasureTheory.integral V ℂ _ _ (borel V) μ (fun x => T f x * starRingEnd ℂ (T g x))) →
    (∀ (m f f' g g' : SchwartzMap V ℂ), (∀ x, f' x = m x * f x) → (∀ x, g' x = starRingEnd ℂ (m x) * g x) →
      @MeasureTheory.integral V ℂ _ _ (borel V) μ (fun x => T f' x * starRingEnd ℂ (T g x)) =
        @MeasureTheory.integral V ℂ _ _ (borel V) μ (fun x => T f x * starRingEnd ℂ (T g' x))) →
    ∃ c : ℂ, ∀ f g : SchwartzMap V ℂ,
      @MeasureTheory.integral V ℂ _ _ (borel V) μ (fun x => T f x * starRingEnd ℂ (T g x)) =
        c * @MeasureTheory.integral V ℂ _ _ (borel V) μ (fun x => f x * starRingEnd ℂ (g x)) := by
  first | exact @GlobalTheory.TransConstForm.eq_const_mul_l2_of_translation_invariant | exact GlobalTheory.TransConstForm.eq_const_mul_l2_of_translation_invariant | (intros; apply GlobalTheory.TransConstForm.eq_const_mul_l2_of_translation_invariant <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TripleMatchExistence
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest GlobalTheory.SqTop GlobalTheory.SquareComm
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.TripleWeilTransfer

variable {D : D7}

theorem isThetaFunO_of_mem_algF {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} (hψ : IsStdChar D ψ (-1))
    (hθ : IsInfFam θ) (ε : Bool) {M X : HSp D} (A : GlobalTheory.ChainFr.Fr M) (B : GlobalTheory.ChainFr.Fr X) {Φ : WO M X → ℂ}
    (hΦ : Φ ∈ algF ψ θ ε A B) : IsThetaFunO ψ (GlobalTheory.Grid.sgn ε M) X Φ := by
  induction hΦ using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨f, P, hf, rfl⟩ := hx
    exact GlobalTheory.GalLift.Vec.theta_pureTensorO hψ hθ _ _ _ _ hf.1 P
  | zero => exact GlobalTheory.OrientedHeis.theta_zero
  | add x y _ _ hx hy => exact GlobalTheory.OrientedHeis.theta_add hx hy
  | smul c x _ hx => exact GlobalTheory.OrientedHeis.theta_smul c hx

theorem eq_on_theta {ψ : AddChar (AF D.host.F) ℂ} (ε : Bool) {M X : HSp D} {χ χ' : (AE D)ˣ →* Circle}
    {ω ω' : GlobalTheory.Grid.WRep M X} (h : GlobalTheory.Grid.IsWeil ψ ε M X χ χ' ω) (h' : GlobalTheory.Grid.IsWeil ψ ε M X χ χ' ω')
    (p : GA D M × GA D X) (f : WO M X → ℂ) (hf : IsThetaFunO ψ (GlobalTheory.Grid.sgn ε M) X f) : ω p f = ω' p f := by
  have e := GlobalTheory.WeilUniq.weilDatum_unique D ψ h.std _ X χ χ' _ _ h h' ((GlobalTheory.Grid.ofSgn ε M).symm p.1, p.2) f hf
  simpa [GlobalTheory.Grid.WRep.toSgn] using e

theorem isCoinvMap_congr {θ : InfFam D} {M X : HSp D} {ω ω' : GlobalTheory.Grid.WRep M X} {S : Submodule ℂ (WO M X → ℂ)}
    {Pi : ModuleCat.{0} ℂ} {rf : GA D X → Module.End ℂ Pi}
    {rl : D.what₂.Tau → Matrix (Fin X.rank) (Fin X.rank) ℂ → Module.End ℂ Pi} {p : (WO M X → ℂ) →ₗ[ℂ] Pi}
    (he : ∀ q, ∀ Φ ∈ S, ω q Φ = ω' q Φ) (h : GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints.IsCoinvMap θ ω S Pi rf rl p) : GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints.IsCoinvMap θ ω' S Pi rf rl p := by
  obtain ⟨⟨sM1, sM2⟩, ⟨sX1, sX2⟩, onto, invf, invl, eqf, eql⟩ := h
  refine ⟨⟨fun g hg Φ hΦ => ?_, fun τ Y hY Φ hΦ => ?_⟩, ⟨fun g hg Φ hΦ => ?_, fun τ Y hY Φ hΦ => ?_⟩, onto,
    fun g hg Φ hΦ => ?_, fun τ Y hY Φ hΦ Φ' hΦ' hd => ?_, fun g hg Φ hΦ => ?_, fun τ Y hY Φ hΦ Φ' hΦ' hd => ?_⟩
  · rw [← he _ Φ hΦ]; exact sM1 g hg Φ hΦ
  · obtain ⟨Φ', h1, h2⟩ := sM2 τ Y hY Φ hΦ
    refine ⟨Φ', h1, fun z => ?_⟩
    simpa only [he _ Φ hΦ] using h2 z
  · rw [← he _ Φ hΦ]; exact sX1 g hg Φ hΦ
  · obtain ⟨Φ', h1, h2⟩ := sX2 τ Y hY Φ hΦ
    refine ⟨Φ', h1, fun z => ?_⟩
    simpa only [he _ Φ hΦ] using h2 z
  · rw [← he _ Φ hΦ]; exact invf g hg Φ hΦ
  · exact invl τ Y hY Φ hΦ Φ' hΦ' (fun z => by simpa only [he _ Φ hΦ] using hd z)
  · rw [← he _ Φ hΦ]; exact eqf g hg Φ hΦ
  · exact eql τ Y hY Φ hΦ Φ' hΦ' (fun z => by simpa only [he _ Φ hΦ] using hd z)

theorem exists_isMatch : GlobalTheory.Published.HoweDualityReal → GlobalTheory.FunPr.Hypotheses₂ → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching → ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D), IsStdChar D ψ (-1) → IsInfFam θ → ∀ (W W₁ X : HSp D) (A : GlobalTheory.ChainFr.Fr W) (A₁ : GlobalTheory.ChainFr.Fr W₁) (B : GlobalTheory.ChainFr.Fr X) (α β : (AE D)ˣ →* Circle), IsTriple W W₁ X α β → (∃ ωA ωB Pi rf rl p p', IsMatch ψ θ A A₁ B α β ωA ωB Pi rf rl p p') → ∀ (ωA : GlobalTheory.Grid.WRep W X) (ωB : GlobalTheory.Grid.WRep W₁ X), GlobalTheory.Grid.IsWeil ψ true W X β (β / α) ωA → GlobalTheory.Grid.IsWeil ψ false W₁ X α (α / β) ωB → ∃ Pi rf rl p p', IsMatch ψ θ A A₁ B α β ωA ωB Pi rf rl p p' := by
  intro _ _ _ _ D ψ θ hψ hθ W W₁ X A A₁ B α β _ ⟨ωA₀, ωB₀, Pi, rf, rl, p, p', hm⟩ ωA ωB hA hB
  refine ⟨Pi, rf, rl, p, p', hA, hB, hm.irred, ?_, ?_⟩
  · exact isCoinvMap_congr (fun q Φ hΦ => eq_on_theta true hm.weilA hA q Φ (isThetaFunO_of_mem_algF hψ hθ true A B hΦ))
      hm.mapA
  · exact isCoinvMap_congr (fun q Φ hΦ => eq_on_theta false hm.weilB hB q Φ (isThetaFunO_of_mem_algF hψ hθ false A₁ B hΦ))
      hm.mapB

end GlobalTheory.TripleWeilTransfer

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistPlaceStepCharacterConductorExponentOneStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.DivisionValues (vw)
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.CMVal (IsHeckeL)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.SqTop
open GlobalTheory.ConstRatio (NegIdx Factor)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Chars Base stepFac chrW eps idealVal gauss unifAt PsiUnr)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twistPlace_stepCharacter_conductorExponent_one : ∀ {D : D7} {T : Type} {Lc : LevCh D T} {sc : Consts} (G : GridData Lc sc) {μ₀ : T}, Lc.Is μ₀ →
    ∀ (i j : Fin D.R.m) (t : T) {v : HeightOneSpectrum (𝓞 D.host.F)} (τ : D.host.E →ₐ[D.host.F] Fv D.host.F v),
      (Lc.C.mu0 j).UnrAt (GlobalTheory.AdelicU.splitPrime τ) → (G.ch.chiH (D.R.m - i)).UnrAt (GlobalTheory.AdelicU.splitPrime τ) →
      GlobalTheory.AdelicU.splitPrime τ ∈ Lc.Q t → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.condExp (chrW (GlobalTheory.SqStep.chs G i j t).ν τ) = 1 := by
  first | exact @GlobalTheory.TwistCond.condExp_twist_eq_one | exact GlobalTheory.TwistCond.condExp_twist_eq_one | (intros; apply GlobalTheory.TwistCond.condExp_twist_eq_one <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilActionCosetVectorFixedPrincipalCongruence
section
open scoped Pointwise
open Formalism.BasicNotions Formalism.IndefR.Links IsDedekindDomain NumberField
open Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.LeafRestExamples GlobalTheory.FunObj.SqNum GlobalTheory.NormSum
open GlobalTheory.Mem.Col2.SplitChar (finIdl)

open GlobalTheory.FunObj.StdDatum

namespace GlobalTheory.BotPairSmall.CvFix

theorem om_cvec_of_congOne : ∀ (D : D7) (δ t0 : ℂ) (hc : Crv D ⊤ δ) (ht : GL3Theta.IsTwoTorsionPointUnkilled D (lamOf D ⊤ δ) t0) (a d : ℕ) (hd : Even d) (e0 : VC D a d → ℂ) (hv : oddE0 D ⊤ δ t0 a d e0) (W : WeilO D ⊤ δ a d e0) (hep : W.ep = 1) (hep' : W.ep' = 1) (𝔪 : Ideal (𝓞 D.host.E)) (hm : 𝔪 ≠ ⊥) (hcop : 𝔪 ⊔ D.host.conj • 𝔪 = ⊤) (hcond : ∀ u : (AE D)ˣ, IntU D u → (u : AE D) - 1 ∈ hatId D (𝔪 * D.host.conj • 𝔪) → W.chV'.f u = 1) (o : ℕ) (ho : o + a = d), ∀ k ∈ intG D a, CongOne D (D.host.conj • 𝔪) k → W.Om k 1 (GlobalTheory.BotPairSmall.cvec D δ (D.host.conj • 𝔪) o a d e0) = GlobalTheory.BotPairSmall.cvec D δ (D.host.conj • 𝔪) o a d e0 := by
  intro D δ t0 hc ht a d hd e0 hv W hep hep' 𝔪 hm hcop hcond o ho k hk hkc
  have hcc : D.host.conj • D.host.conj • 𝔪 = 𝔪 := by
    rw [smul_smul, GlobalTheory.GaloisTwist.conj_mul_conj, one_smul]
  have h := GlobalTheory.T.weil_fixes_cosetVector_congruent_one_mod_ideal D δ t0 hc e0 hv W (D.host.conj • 𝔪) (GlobalTheory.BotPairSmall.conj_smul_ne_bot D hm) ?_ ?_ o (by omega) k hk hkc
  · exact h
  · rw [hcc, Ideal.isCoprime_iff_sup_eq, sup_comm]; exact hcop
  · intro u hu hu1
    apply hcond u hu
    rwa [hcc, mul_comm] at hu1

end GlobalTheory.BotPairSmall.CvFix
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilDatumAdjointNegSourceKernelsAgreeStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV GlobalTheory.RouteSeesaw

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weilDatum_adjoint_negSource_kernels_agree : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S B : HSp D) (χS χT : (AE D)ˣ →* Circle)
    (ω₂ : GA D B × GA D S →* Module.End ℂ (WO B S → ℂ)), IsWeilDatumO ψ B S χS χT ω₂ →
    ∃ (ω : GA D (negSp S) × GA D B →* Module.End ℂ (WO (negSp S) B → ℂ)) (χ χ' : (AE D)ˣ →* Circle),
      IsWeilDatumO ψ (negSp S) B χ χ' ω ∧ ∀ f : WO B S → ℂ, IsThetaFunO ψ B S f →
        IsThetaFunO ψ (negSp S) B (fun y => f (adjM S B y)) ∧
        ∀ g₁ u, thetaKO ω (negGA S u) g₁ (fun y => f (adjM S B y)) = thetaKO ω₂ g₁ u f := by
  first | exact @GlobalTheory.AdjSwap.weil_adjoint_negSource | exact GlobalTheory.AdjSwap.weil_adjoint_negSource | (intros; apply GlobalTheory.AdjSwap.weil_adjoint_negSource <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilDatumTwistByHeckeCharactersTrivialBaseStatement
section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weil_datum_twist_by_hecke_characters_trivial_base : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    B.IsGood σ → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ →
      ∀ (χS χT νS νT : (AF F ⊗[F] E)ˣ →* Circle) ω,
        IsWeilDatumOF σ JS JT (fun w : InfinitePlace F => (B.emb w).1) ξ₀ B.ψ χS χT ω →
        IsHeckeCharF νS → IsHeckeCharF νT → ResEtaF νS 0 → ResEtaF νT 0 →
        ∃ ω', IsWeilDatumOF σ JS JT (fun w : InfinitePlace F => (B.emb w).1) ξ₀ B.ψ (χS * νS) (χT * νT) ω' := by
  first | exact @GlobalTheory.WeilTwistF.exists_weilDatumOF_twist | exact GlobalTheory.WeilTwistF.exists_weilDatumOF_twist | (intros; apply GlobalTheory.WeilTwistF.exists_weilDatumOF_twist <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilOperatorFixesConjCosetVector
section
open Formalism.BasicNotions Formalism.IndefR.Links IsDedekindDomain NumberField Polynomial
open scoped Pointwise nonZeroDivisors
open Formalism.L2.Host (HChar embTau)
open GlobalTheory.ChiGrid GlobalTheory.LeafRestExamples
open Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.FunObj GlobalTheory.FunObj.SqNum

namespace GlobalTheory.FunObj.NormUniq

theorem conj_smul_conj_smul {D : D7} (I : Ideal (𝓞 D.host.E)) : D.host.conj • D.host.conj • I = I := by
  have h : D.host.conj * D.host.conj = 1 := AlgEquiv.ext fun x => GlobalTheory.NormSum.VacMove.conj_conj D x
  rw [smul_smul, h, one_smul]

end GlobalTheory.FunObj.NormUniq
end

