import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0160
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.LocalLanglandsGL
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0051
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0017
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsNormalisedThetaSub
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0009
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0010
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0012
import Formalism.LocalRingCardinality.CoeNeZeroOfNotMem
import Formalism.LocalRingCardinality.HostCls
import Formalism.LocalToGlobal.InertKernelTheory.Bundle0012
import Formalism.LocalToGlobal.InertKernelTheory.GenusOneModelExistsLattice
import Formalism.LocalToGlobal.InertKernelTheory.Bundle0007
import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.Bundle0001
import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.GlobalOrthonormalBasisFour
import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.IntWAPlaces
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0001
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ContinuousMapPFin
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsSubquotientDetRepParInd
import Formalism.LocalToGlobal.KernelLattices.FirstKernelLawReading
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0161
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0149
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0142
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0132
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HasSupportOfIsSubquotientProdIrr
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivMultiProdOne
import Formalism.LocalToGlobal.IndefiniteReal.ZeroPartEigenvalueConvention
import Development.AbelianVarietyTheory.BlockTheory.ThetaLiftGeometry.Bundle0009
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsPrimeIdemOfInert
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0015
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0006
import Formalism.SharpRestriction.LevelLetterCocycles.SumRepresentations
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.WeightRegularOfExt
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.Bundle0012
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0156
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0005
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.IrreducibleWdEigenEqualNormStatement
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.irreducible_wd_eigen_equal_norm : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w) (x : WD h), IsIrrWD x → ∀ φ : Weil h, deg φ = 1 → ∀ α ∈ x.eig φ, ∀ β ∈ x.eig φ, ‖α‖ = ‖β‖ := by
  first | exact @GlobalTheory.IrrWeilAbs.irrWD_eig_norm_eq | exact GlobalTheory.IrrWeilAbs.irrWD_eig_norm_eq | (intros; apply GlobalTheory.IrrWeilAbs.irrWD_eig_norm_eq <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsConjSelfDualOfInvTransposeIsoCmConjStatement
section
open NumberField Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.ContraPair
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isConjSelfDual_of_invTranspose_iso_cmConj : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (a : ℕ) (π : CuspSub L a) (S : π.V ≃ₗ[ℂ] π.V), (∀ o φ, S (π.op (invTOp o) φ) = π.op (conjOp o) (S φ)) → π.IsCsd := by
  first | exact @GlobalTheory.CsdFromConj.isCsd_of_invT_conj | exact GlobalTheory.CsdFromConj.isCsd_of_invT_conj | (intros; apply GlobalTheory.CsdFromConj.isCsd_of_invT_conj <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.JacobiOfClass
section
noncomputable section

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.TaylorLogMetric GlobalTheory.KerStd Classical
open Formalism.L2.Th1.CM (MaximalUnramifiedExtension)
open Formalism.L2.Th1.D (F1 F2 OwOK TrDual phFF)
open Formalism.InvariantFactorPaths.G7 (UnrOK IsLawOfLog cob)

namespace GlobalTheory.KerStd.HostInert

open Formalism.InvariantFactorPaths.G7 (lgF at1) in
open Formalism.L2.G.Pend (k0ToC wittFractionAlgebraCp) in

theorem inParamK_eq {l : ℕ} [Fact l.Prime] {ι : Type} (f : MvPowerSeries ι ℂ_[l]) :
    @Formalism.MainNotions.FormalGroupSystem.inParamK l _ ι ℂ_[l] _ (wittFractionAlgebraCp l) f = MvPowerSeries.subst (fun i => at1 i (lgF ℂ_[l] l)) f := by
  unfold Formalism.MainNotions.FormalGroupSystem.inParamK
  have hlog : PowerSeries.map (k0ToC l) (Formalism.MainNotions.FormalGroupSystem.logF l) = lgF ℂ_[l] l := by
    ext n
    rw [PowerSeries.coeff_map]
    simp only [Formalism.MainNotions.FormalGroupSystem.logF, lgF, PowerSeries.coeff_mk, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [pow_mul]
    split_ifs <;> simp
  congr 1
  funext i
  rw [show @algebraMap (Formalism.MainNotions.FormalGroupSystem.K0 l) ℂ_[l] _ _ (wittFractionAlgebraCp l) = k0ToC l from rfl, hlog]
  rfl

theorem jacobi_of_class (D : D7) (p : ℕ) [Fact p.Prime] (h : IsResidueClassZero D p ∨ IsSg D p) :
    jacobiSym (-(D.host.d : ℤ)) p = -1 := by
  have hp : p.Prime := Fact.out
  have hd : D.host.d.Prime := D.host.hyp.2.1
  have key : p ≠ D.host.d ∧ jacobiSym (-(D.host.d : ℤ)) p ≠ 1 := by
    have h' : D.host.cls p = PrimeClass.inertClass ∨
        D.host.cls p = PrimeClass.signal := h
    rcases h' with h' | h'
    · obtain ⟨-, -, h3, h4, -⟩ := (primeClass_eq_inert_iff _).1 h'
      exact ⟨h3, h4⟩
    · obtain ⟨-, -, h3, h4, -⟩ := (primeClass_eq_signal_iff _).1 h'
      exact ⟨h3, h4⟩
  haveI : NeZero p := ⟨hp.ne_zero⟩
  rcases jacobiSym.trichotomy (-(D.host.d : ℤ)) p with h0 | h1 | h1
  · exfalso
    rw [jacobiSym.eq_zero_iff_not_coprime] at h0
    apply h0
    have : Nat.Coprime D.host.d p := (Nat.coprime_primes hd hp).2 key.1.symm
    simpa [Int.gcd_neg, Int.gcd_natCast_natCast] using this
  · exact absurd h1 key.2
  · exact h1

theorem hostAt_inert : Formalism.L2.KerInert.GenusOneModelExistsLattice → Formalism.L2.KerInert.Rep.CurveDict → Formalism.L2.KerInert.IntInert → ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Formalism.L2.Ker.Base D cc δ) (χ : IdE D → ℂ), IsCurveIdeal D cc → IsDiscriminantTwelfthRootOfIdealLattice D cc δ → IsChi D χ → ∀ (p : ℕ) [Fact p.Prime] (lam : Qbar →+* ℂ_[p]), 5 ≤ p → (IsResidueClassZero D p ∨ IsSg D p) → HostAt B χ p lam := by
  intro h1 h2 h3 D cc δ B χ hc hδ hχ p _ lam h5 hcl
  have hin := jacobi_of_class D p hcl
  obtain ⟨cc', δ', g, -, -, hL, hlam, hAt, hM, hLT⟩ := h1 D cc δ hc hδ p h5 hin lam
  obtain ⟨g2, g3, ε, s2, -, -, -, -, hn, ⟨a1, a2, a3, a4, a5, -, F, hF, -⟩, hD⟩ := h2 D cc' δ' p g hLT hAt h5 hin hM
  obtain ⟨σ, hσ, -⟩ := Formalism.L2.Th1.D.fieldDataCM p h5
  refine ⟨_, g2, g3, s2, ε, σ, F, hn, ⟨h5, a1, a2, a3, a4, hσ, hF, a5 σ hσ⟩, ?_⟩
  intro N N' L L' hA
  obtain ⟨r, b, hb, ho⟩ := Formalism.L2.KerInert.orthBasisExists_of Formalism.L2.KerInert.global_orthonormal_basis_four
    Formalism.L2.KerInert.weakApprox_of_approx_and_separation D p h5 hin N N' L L' hA
  refine ⟨r, b, hb, ho, fun G hG => ?_⟩
  obtain ⟨C, wq, hC, hw, hd⟩ := hD D
  have hΛ : g.abelian₂ = B.tor.abelian₂ := hAt.2.2.2.1.trans hL
  subst hlam
  rw [hΛ] at hC hw hd
  have := hd N N' r b G (h3 D cc δ B hc hδ χ hχ p h5 hin g.lam N N' L L' hA G hG C wq r b hC hw hb ho)
  rw [HostLog.iff_phSum]
  rw [inParamK_eq] at this
  exact this

end GlobalTheory.KerStd.HostInert
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.JacquetModuleCoinvariantsSubsingletonOfCharConjStatement
section
open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC GlobalTheory.DefU Formalism.BasicNotions Formalism.ConjugateSelfDual GlobalTheory.Cong
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.jacquetModuleCoinvariants_subsingleton_of_char_conj : ∀ (G V : Type) [Group G] [AddCommGroup V] [Module ℂ V] (π : Representation ℂ G V), π.IsIrreducible → ∀ (N H : Subgroup G) (χ : H →* ℂˣ) (v : V), v ≠ 0 → (∀ h : H, π h v = (χ h : ℂ) • v) → (∀ g : G, ∃ h : H, g * h * g⁻¹ ∈ N ∧ χ h ≠ 1) → Subsingleton (Jacquet π N) := by
  first | exact @GlobalTheory.jacquet_subsingleton_of_char_nontrivial_on_conj | exact GlobalTheory.jacquet_subsingleton_of_char_nontrivial_on_conj | (intros; apply GlobalTheory.jacquet_subsingleton_of_char_nontrivial_on_conj <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LastStepDataIntegralAwayFromLevelsStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker Formalism.L2.Col Formalism.HermitianLatticesTheory Formalism.L2.DIV Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lastStep_data_integralAwayFrom_levels : ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : G.Inst D L) (Gl : G.LatInst D) (K : G.Consts) (Y : DivX D) (cX : ExtraC) (ex : Extra D L hT Gi Gl K Y cX) (t : KerEntTied ex), ∀ u μ p Yb d x, Yb ∈ ybSet t.sel (t.tup μ) (t.cst μ) p.deco.1.N → IntOff (t.O u μ).S (t.seam.σ₀ (XiCpl2 (R := D.R) (u := t.word u) t.Ch t.sel (t.tup μ) (t.cst μ) t.m2 p Yb d x)) := by
  first | exact @GlobalTheory.CplTwoInt.xiCpl2_intOff_tied | exact GlobalTheory.CplTwoInt.xiCpl2_intOff_tied | (intros; apply GlobalTheory.CplTwoInt.xiCpl2_intOff_tied <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LatticeKernelLeOfMatrixLatticeIndexEqStatement
section
open Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.latticeKernel_le_of_matrixLatticeIndex_eq : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (ϖ : L) (σ : L →+* L) (q : ℕ),
    Formalism.UG.IsUnramInv ϖ σ q → ∀ (n n' : ℕ) (x y : Matrix (Fin n') (Fin n) L),
    (∀ u : Fin n → L, (∀ i, u i ∈ Formalism.UG.intL L) → (∀ i, (x *ᵥ u) i ∈ Formalism.UG.intL L) → ∀ i, (y *ᵥ u) i ∈ Formalism.UG.intL L) →
    GlobalTheory.Hk3.HoweDuality.latIdx y = GlobalTheory.Hk3.HoweDuality.latIdx x →
    ∀ u : Fin n → L, (∀ i, u i ∈ Formalism.UG.intL L) → (∀ i, (y *ᵥ u) i ∈ Formalism.UG.intL L) → ∀ i, (x *ᵥ u) i ∈ Formalism.UG.intL L := by
  first | exact @GlobalTheory.Hk3.HoweDuality.ker_le_of_latIdx_eq | exact GlobalTheory.Hk3.HoweDuality.ker_le_of_latIdx_eq | (intros; apply GlobalTheory.Hk3.HoweDuality.ker_le_of_latIdx_eq <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LexSumSplitFirstBlockStrictMonoStatement
section
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel Matrix
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lexSum_splitFirstBlock_strictMono : ∀ (s : ℕ) (t : Fin (s + 1) → ℕ), StrictMono fun c : Fin (t 0) ⊕ₗ (Σₗ i : Fin s, Fin (t i.succ)) => (Sum.elim (fun j => toLex (⟨0, j⟩ : Σ a, Fin (t a))) (fun x => toLex (⟨(ofLex x).1.succ, (ofLex x).2⟩ : Σ a, Fin (t a))) (ofLex c) : Σₗ a, Fin (t a)) := by
  first | exact @GlobalTheory.lexSumSplit_strictMono | exact GlobalTheory.lexSumSplit_strictMono | (intros; apply GlobalTheory.lexSumSplit_strictMono <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LocAtOfIsLocElt
section
open Formalism.BasicNotions IsDedekindDomain NumberField

noncomputable section

namespace GlobalTheory.LocEltLocal

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem locAt_of_isLocElt {D : Formalism.BasicNotions.D7} (V : Formalism.BasicNotions.TH.HSp D) (P : Formalism.L2.DIV.Pl D.host.E)
    (x : Formalism.IndefR.Bridge.Gf V) (_hP : GlobalTheory.IndefiniteRowSideFullHecke.HeckeIntertwinersInert.IsInertPl P) (h : Formalism.IndefR.Links.IsLocElt V P x) :
    GlobalTheory.IndefiniteRowSideFullHecke.HeckeIntertwinersInert.LocAt V (GlobalTheory.IndefiniteRowSideFullHecke.HeckeIntertwinersInert.plF P) x := by
  obtain ⟨e, f, g, hpi, hg, hx, hs⟩ := h
  obtain ⟨Φ, hΦ⟩ := GlobalTheory.IdemSupport.exists_comp D
  obtain ⟨-, ε, hε, rfl⟩ := GlobalTheory.IdemSupport.of_isPrimeIdem hΦ hpi
  have h1 := (GlobalTheory.HeckeRowsCompare.suppF_iff V hε hg).1 hs
  rw [GlobalTheory.HeckeRowsCompare.mem_locGrp] at h1
  have h2 : GlobalTheory.HeckeRowsCompare.fin V g = x := Subtype.ext hx.symm
  rw [h2] at h1
  exact (GlobalTheory.HeckeRowsCompare.locAt_iff V _ x).2 h1

theorem main : ∀ {D : Formalism.BasicNotions.D7} (V : Formalism.BasicNotions.TH.HSp D) (P : Formalism.L2.DIV.Pl D.host.E) (x : Formalism.IndefR.Bridge.Gf V),
    GlobalTheory.IndefiniteRowSideFullHecke.HeckeIntertwinersInert.IsInertPl P → Formalism.IndefR.Links.IsLocElt V P x →
      GlobalTheory.IndefiniteRowSideFullHecke.HeckeIntertwinersInert.LocAt V (GlobalTheory.IndefiniteRowSideFullHecke.HeckeIntertwinersInert.plF P) x :=
  fun V P x hP h => locAt_of_isLocElt V P x hP h

end GlobalTheory.LocEltLocal
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LocalInvariantsMatchSemisimple
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.RowTie GlobalTheory.SplitRead

noncomputable section

namespace GlobalTheory.TwistLG

open Formalism.MainNotions.SumRepresentations.At

section Rep

variable {Γ : Type} [Group Γ] {k : Type} [Field k] {a : ℕ}

theorem twGL_val (ρ : Γ →* GL (Fin a) k) (χ : Γ →* kˣ) (g : Γ) :
    ((twGL ρ χ g : GL (Fin a) k) : Matrix (Fin a) (Fin a) k) =
      ((χ g : kˣ) : k) • (ρ g : Matrix (Fin a) (Fin a) k) := by
  rw [Algebra.smul_def]
  rfl

theorem isInv_twGL_iff (ρ : Γ →* GL (Fin a) k) (χ : Γ →* kˣ) (W : Submodule k (Fin a → k)) :
    IsInv (twGL ρ χ) W ↔ IsInv ρ W := by
  constructor
  · intro h g v hv
    have h1 := W.smul_mem (((χ g)⁻¹ : kˣ) : k) (h g v hv)
    rw [twGL_val, Matrix.smul_mulVec, smul_smul, ← Units.val_mul, inv_mul_cancel, Units.val_one,
      one_smul] at h1
    exact h1
  · intro h g v hv
    rw [twGL_val, Matrix.smul_mulVec]
    exact W.smul_mem _ (h g v hv)

theorem isSSRep_twGL (ρ : Γ →* GL (Fin a) k) (χ : Γ →* kˣ) (h : IsSSRep ρ) : IsSSRep (twGL ρ χ) := by
  intro W hW
  obtain ⟨W', h1, h2⟩ := h W ((isInv_twGL_iff ρ χ W).1 hW)
  exact ⟨W', (isInv_twGL_iff ρ χ W').2 h1, h2⟩

theorem cont_twGL [TopologicalSpace Γ] [TopologicalSpace k] [IsTopologicalRing k]
    (ρ : Γ →* GL (Fin a) k) (χ : Γ →* GL (Fin 1) k)
    (hρ : Continuous fun g => ((ρ g : GL (Fin a) k) : Matrix (Fin a) (Fin a) k))
    (hχ : Continuous fun g => ((χ g : GL (Fin 1) k) : Matrix (Fin 1) (Fin 1) k)) :
    Continuous fun g => ((twGL ρ (Matrix.GeneralLinearGroup.det.comp χ) g : GL (Fin a) k) :
      Matrix (Fin a) (Fin a) k) := by
  simp only [twGL_val]
  refine Continuous.smul (M := k) ?_ hρ
  have e : ∀ g, (((Matrix.GeneralLinearGroup.det.comp χ) g : kˣ) : k) =
      (χ g : Matrix (Fin 1) (Fin 1) k).det := fun g => rfl
  simp only [e]
  exact hχ.matrix_det

theorem charpoly_eq_of_dense [TopologicalSpace Γ] [TopologicalSpace k] [IsTopologicalRing k] [T2Space k]
    [Infinite k] (ρ₁ ρ₂ : Γ →* GL (Fin a) k)
    (h1 : Continuous fun g => ((ρ₁ g : GL (Fin a) k) : Matrix (Fin a) (Fin a) k))
    (h2 : Continuous fun g => ((ρ₂ g : GL (Fin a) k) : Matrix (Fin a) (Fin a) k))
    (S : Set Γ) (hS : closure S = Set.univ)
    (hE : ∀ g ∈ S, ((ρ₁ g : GL (Fin a) k) : Matrix (Fin a) (Fin a) k).charpoly =
      ((ρ₂ g : GL (Fin a) k) : Matrix (Fin a) (Fin a) k).charpoly) (g : Γ) :
    ((ρ₁ g : GL (Fin a) k) : Matrix (Fin a) (Fin a) k).charpoly =
      ((ρ₂ g : GL (Fin a) k) : Matrix (Fin a) (Fin a) k).charpoly := by
  apply Polynomial.funext
  intro t
  rw [Matrix.eval_charpoly, Matrix.eval_charpoly]
  have hc : IsClosed {g : Γ | (Matrix.scalar (Fin a) t - ((ρ₁ g : GL (Fin a) k) : Matrix (Fin a) (Fin a) k)).det =
      (Matrix.scalar (Fin a) t - ((ρ₂ g : GL (Fin a) k) : Matrix (Fin a) (Fin a) k)).det} :=
    isClosed_eq (continuous_const.sub h1).matrix_det (continuous_const.sub h2).matrix_det
  have hsub : closure S ⊆ _ := hc.closure_subset_iff.mpr fun g hg => by
    show _ = _
    rw [← Matrix.eval_charpoly, ← Matrix.eval_charpoly, hE g hg]
  rw [hS] at hsub
  exact hsub (Set.mem_univ g)

end Rep

section Glob

variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂) (A : NAut N)

theorem etaT_char_etaTinv (w : PlE H) :
    A.lpChar (A.locG A.etaT w) (A.locG A.etaTinv w) = A.lpUnr w {1} := by
  have u1 := A.etaT_unr w
  obtain ⟨u2, f2⟩ := A.etaTinv_def w
  have d2 : A.lpDim (A.locG A.etaTinv w) = 1 := A.locG_dim _ w
  obtain ⟨b, hb⟩ : ∃ b, A.frobEig (A.locG A.etaT w) = {b} :=
    Multiset.card_eq_one.mp (by rw [A.frobEig_card _ u1, A.locG_dim])
  have hb0 : b ≠ 0 := by
    intro h0
    apply A.frobEig_ne_zero _ u1
    rw [hb, h0]
    exact Multiset.mem_singleton_self 0
  rw [hb, Multiset.map_singleton] at f2
  have hu := A.unr_char _ _ d2 u1 u2
  have hf := A.frobEig_char _ _ b⁻¹ u1 u2 d2 f2
  rw [hb, Multiset.map_singleton, mul_inv_cancel₀ hb0] at hf
  rw [A.unr_eq_lpUnr _ hu, hf]

theorem param_twist (hLP : TieLP N A) {a : ℕ} (π : A.CG a) (w : PlE H) (u s : ℝ) :
    A.lpChar (A.lpTw (A.locG (A.tw π A.etaT) w) u) (A.lpTw (A.locG A.etaTinv w) s) =
      A.lpTw (A.locG π w) (s + u) := by
  have d1 : A.lpDim (A.locG A.etaT w) = 1 := A.locG_dim _ w
  have d2 : A.lpDim (A.locG A.etaTinv w) = 1 := A.locG_dim _ w
  have c3 := (hLP w (A.lpTw (A.locG (A.tw π A.etaT) w) u) (A.lpZero w) (A.locG A.etaTinv w)
    (A.locG A.etaTinv w) s d2 d2).2.2.1
  have c2 := (hLP w (A.locG (A.tw π A.etaT) w) (A.lpZero w) (A.locG A.etaTinv w) (A.locG A.etaTinv w) u
    d2 d2).2.1
  have c4 := (hLP w (A.locG π w) (A.lpZero w) (A.locG A.etaT w) (A.locG A.etaTinv w) 0 d1 d2).2.2.2.1
  have c5 := (hLP w (A.locG π w) (A.lpZero w) (A.locG A.etaT w) (A.locG A.etaTinv w) 0 d1 d2).2.2.2.2.1
  rw [c3, c2, A.lpTw_add, A.locG_tw, c4, etaT_char_etaTinv N A w, c5, add_comm]

theorem isSSRep_iotaOQ (i : N.Loc) {a : ℕ} (ρ : G H.E N.Om →* GL (Fin a) (N.O i))
    (h : IsSSRep (mapRep (algebraMap (N.O i) (Kf N i)) ρ)) : IsSSRep (mapRep (iotaOQ N A i) ρ) := by
  let _ : Algebra (Kf N i) (Qbar (N.l i)) := (A.iotaQ i).toAlgebra
  have : CharZero (Kf N i) := RingHom.charZero (A.iotaQ i)
  have e : mapRep (iotaOQ N A i) ρ =
      mapRep (algebraMap (Kf N i) (Qbar (N.l i))) (mapRep (algebraMap (N.O i) (Kf N i)) ρ) := by
    ext g p q
    rfl
  rw [e]
  exact ssAscent (Kf N i) (Qbar (N.l i)) (G H.E N.Om) a _ h

theorem placesOver_finite (i : N.Loc) : (placesOver H.E (N.l i)).Finite := by
  have hne : Ideal.span {((N.l i : ℕ) : 𝓞 H.E)} ≠ ⊥ := by
    rw [Ne, Ideal.span_singleton_eq_bot]
    exact_mod_cast (Fact.out : (N.l i).Prime).ne_zero
  refine (Ideal.finite_factors hne).subset fun v hv => ?_
  exact Ideal.dvd_span_singleton.mpr hv

end Glob

section Main

variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂) (A : NAut N)

theorem localGlobal_twist_at (hLP : TieLP N A) (hAut : TieAut N A) (hGal : TieGal N A) (hG : exists_galois_rep_local_global_compatible N A)
    (hAN : JacquetShalikaStrongMultOne N A) (i : N.Loc) (a : ℕ) (ha : 1 ≤ a) (π : A.CG a) (s : ℝ)
    (hcsd : A.csd (A.tw π A.etaT)) (hralg : A.ralg (A.tw π A.etaT)) (hs : ∃ m : ℤ, s = (m : ℝ) + 1 / 2)
    (ρ : G H.E N.Om →* GL (Fin a) (N.O i)) (hρ : GlobalTheory.LocalInv.Cont N i ρ)
    (hss : IsSSRep (mapRep (algebraMap (N.O i) (Kf N i)) ρ))
    (hM : GlobalTheory.LocalInv.Matches N A i ρ π (s + (1 - (a : ℝ)) / 2)) (w : PlE H) :
    GlobalTheory.LocalInv.wd N A i ρ w = A.lpTw (A.locG π w) (s + (1 - (a : ℝ)) / 2) ∧
      (w ∈ placesOver H.E (N.l i) → GlobalTheory.LocalInv.DeRham N A i ρ w) := by

  obtain ⟨ρ1, c1, ss1, away1, above1⟩ := (hG i).1 a ha _ hcsd hralg

  have hint : ∀ τ : H.E →+* ℂ, ∀ z ∈ A.infG A.etaTinv τ, ∃ k : ℤ, z + (s : ℂ) = (k : ℂ) := by
    intro τ z hz
    obtain ⟨m, rfl⟩ := hs
    obtain ⟨h1, h2⟩ := hAut.2.1 τ
    rw [h2] at hz
    rcases h1 with h1 | h1
    · rw [h1] at hz
      simp at hz
      subst hz
      exact ⟨m, by push_cast; ring⟩
    · rw [h1] at hz
      simp at hz
      subst hz
      exact ⟨m + 1, by push_cast; ring⟩
  obtain ⟨χ1, cχ, awayχ, aboveχ⟩ := (hG i).2.2 A.etaTinv s hint
  obtain ⟨-, hconj, -, htw⟩ := hGal.2.2.2 i
  have ok1 : ∀ w, WDok N A i ρ1 w := fun w => by
    by_cases hw : w ∈ placesOver H.E (N.l i)
    · exact Or.inr (above1 w hw).1
    · exact Or.inl hw
  have okχ : ∀ w, WDok N A i χ1 w := fun w => by
    by_cases hw : w ∈ placesOver H.E (N.l i)
    · exact Or.inr (aboveχ w hw).1
    · exact Or.inl hw
  have wd1 : ∀ w, A.wdOf i ρ1 w = A.lpTw (A.locG (A.tw π A.etaT) w) ((1 - (a : ℝ)) / 2) := fun w => by
    by_cases hw : w ∈ placesOver H.E (N.l i)
    · exact (above1 w hw).2.2
    · exact (away1 w hw).1
  have wdχ : ∀ w, A.wdOf i χ1 w = A.lpTw (A.locG A.etaTinv w) s := fun w => by
    by_cases hw : w ∈ placesOver H.E (N.l i)
    · exact (aboveχ w hw).2.1
    · exact awayχ w hw

  let ρ0 := twGL ρ1 (Matrix.GeneralLinearGroup.det.comp χ1)
  have c0 : ContQ N i ρ0 := cont_twGL ρ1 χ1 c1 cχ
  have wd0 : ∀ w, A.wdOf i ρ0 w = A.lpTw (A.locG π w) (s + (1 - (a : ℝ)) / 2) := fun w => by
    rw [(htw a ρ1 χ1 c1 cχ).2.1 w (ok1 w) (okχ w), wd1, wdχ, param_twist N A hLP]
  have dR0 : ∀ w ∈ placesOver H.E (N.l i), A.IsdRW i ρ0 w := fun w hw =>
    ((htw a ρ1 χ1 c1 cχ).1 w hw (aboveχ w hw).1).2 (above1 w hw).1
  have ok0 : ∀ w, WDok N A i ρ0 w := fun w => by
    by_cases hw : w ∈ placesOver H.E (N.l i)
    · exact Or.inr (dR0 w hw)
    · exact Or.inl hw

  let ρQ := mapRep (iotaOQ N A i) ρ
  have cQ : ContQ N i ρQ := GlobalTheory.LocalInv.cont_mapRep_iotaOQ N A i ρ hρ
  have ssQ : IsSSRep ρQ := isSSRep_iotaOQ N A i ρ hss
  have ss0 : IsSSRep ρ0 := isSSRep_twGL _ _ ss1

  have hcp : ∀ g, ((ρ0 g : GL (Fin a) (Qbar (N.l i))) : Matrix (Fin a) (Fin a) (Qbar (N.l i))).charpoly =
      ((ρQ g : GL (Fin a) (Qbar (N.l i))) : Matrix (Fin a) (Fin a) (Qbar (N.l i))).charpoly := by
    have hMf := Filter.eventually_cofinite.mp hM
    have hUf := Filter.eventually_cofinite.mp (A.locG_unr_ae π)
    refine charpoly_eq_of_dense ρ0 ρQ c0 cQ _
      (hAN.2.2.1 _ (((placesOver_finite N i).union hMf).union hUf)) ?_
    rintro g ⟨v, hv, hsp, B, hB, hg⟩
    simp only [Set.mem_union, not_or] at hv
    obtain ⟨⟨hvl, hvM⟩, hvU⟩ := hv
    have hvM' := not_not.mp hvM
    have hvU' := not_not.mp hvU
    apply Polynomial.map_injective (A.iotaQC i).toRingHom (A.iotaQC i).injective
    have hu0 : A.unr (A.wdOf i ρ0 v) := by
      rw [wd0]
      exact (A.unr_tw _ _).2 hvU'
    rw [A.wdOf_frob i ρ0 v hvl c0 hu0 B g hB hg, wd0]
    have e := hvM' hsp B g hB hg
    have e2 : ((ρQ g : GL (Fin a) (Qbar (N.l i))) : Matrix (Fin a) (Fin a) (Qbar (N.l i))).charpoly.map
        (A.iotaQC i).toRingHom =
        ((ρ g : GL (Fin a) (N.O i)) : Matrix (Fin a) (Fin a) (N.O i)).charpoly.map (iotaO N A i) := by
      show ((((ρ g : GL (Fin a) (N.O i)) : Matrix (Fin a) (Fin a) (N.O i)).map (iotaOQ N A i)).charpoly).map _ = _
      rw [Matrix.charpoly_map, Polynomial.map_map]
      rfl
    rw [e2, e]
    rfl

  obtain ⟨Pm, hPm⟩ := hAN.2.2.2 (Qbar (N.l i)) a ρ0 ρQ ss0 ssQ hcp
  obtain ⟨hdR, hwd, -⟩ := hconj a ρ0 ρQ c0 Pm hPm
  refine ⟨?_, fun hw => ?_⟩
  · show A.wdOf i ρQ w = _
    rw [hwd w (ok0 w), wd0]
  · show A.IsdRW i ρQ w
    exact (hdR w hw).2 (dR0 w hw)

end Main

theorem localGlobal_twist : ∀ D : D7, Formalism.MainNotions.SumRepresentations.tie0 D → Formalism.MainNotions.SumRepresentations.adm2 D → Formalism.MainNotions.SumRepresentations.adm5 D →
    ∀ (i : D.nd.Loc) (a : ℕ), 1 ≤ a → ∀ (π : D.naut.CG a) (s : ℝ), D.naut.csd (D.naut.tw π D.naut.etaT) →
    D.naut.ralg (D.naut.tw π D.naut.etaT) → (∃ m : ℤ, s = (m : ℝ) + 1 / 2) →
    ∀ ρ : G D.host.E D.nd.Om →* GL (Fin a) (D.nd.O i), GlobalTheory.LocalInv.Cont D.nd i ρ →
    IsSSRep (mapRep (algebraMap (D.nd.O i) (Kf D.nd i)) ρ) →
    GlobalTheory.LocalInv.Matches D.nd D.naut i ρ π (s + (1 - (a : ℝ)) / 2) →
    ∀ w, GlobalTheory.LocalInv.wd D.nd D.naut i ρ w = D.naut.lpTw (D.naut.locG π w) (s + (1 - (a : ℝ)) / 2) ∧
      (w ∈ placesOver D.host.E (D.nd.l i) → GlobalTheory.LocalInv.DeRham D.nd D.naut i ρ w) := by
  intro D ht h2 h5 i a ha π s hcsd hralg hs ρ hρ hss hM w
  exact localGlobal_twist_at D.nd D.naut ht.1 ht.2.1 ht.2.2 h2 h5 i a ha π s hcsd hralg hs ρ hρ hss hM w

end GlobalTheory.TwistLG
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LpCharacterEigenProductStatement
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lp_character_eigen_product : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w) (x : WD h) (l : ℕ) (σ : Weil h), ((x.lpChar (WD.lpSp h l)).eig σ).prod = ((x.eig σ).prod) ^ l := by
  first | exact @GlobalTheory.WeilDeligne.prod_eig_lpChar_lpSp | exact GlobalTheory.WeilDeligne.prod_eig_lpChar_lpSp | (intros; apply GlobalTheory.WeilDeligne.prod_eig_lpChar_lpSp <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.MemISupTypePartsOfGoodBaseForms
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.Hk3
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwParts

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type}
  {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks]
  [Algebra Ks D.what₂.LL]

theorem mk_bC_mem_range (R : RealDat3 D A3 Ks) (F : Face3 D A3) (j : Fin D.R.m)
    (k : Fin ((R.toCx3 F).dW false j)) :
    Tw.mk (twAt D.what₂.embLL A3.A.v0) (R.toRealDat.bC F.lv2 false j (sg0 D A3.A) k) ∈
      LinearMap.range ((R.toCx3 F).w0C false j) := by
  have hpos : (0 : ℝ) < Real.sqrt (RealDat.nP F.lv2 false) := Real.sqrt_pos.mpr (RealDat.nP_pos (F := F.lv2) false)
  refine ⟨Pi.single k ((((Real.sqrt (RealDat.nP F.lv2 false))⁻¹ : ℝ) : ℂ)), ?_⟩
  simp only [CxData.w0C, CxData.wC, lin, LinearMap.comp_apply, Fintype.linearCombination_apply_single]
  rw [LinearMap.map_smul]
  show Tw.out (s := twAt D.what₂.embLL A3.A.v0) (E := (R.HW j (sg0 D A3.A)).H) (_ • _) = Tw.out (s := twAt D.what₂.embLL A3.A.v0) (E := (R.HW j (sg0 D A3.A)).H) (Tw.mk _ _)
  erw [Tw.out_smul, cj_ofReal]
  show ((((Real.sqrt (RealDat.nP F.lv2 false))⁻¹ : ℝ) : ℂ)) • ((((Real.sqrt (RealDat.nP F.lv2 false)) : ℝ) : ℂ) • R.toRealDat.bC F.lv2 false j (sg0 D A3.A) k) = R.toRealDat.bC F.lv2 false j (sg0 D A3.A) k
  rw [smul_smul, ← Complex.ofReal_mul, inv_mul_cancel₀ hpos.ne', Complex.ofReal_one, one_smul]

end GlobalTheory.TwParts

open GlobalTheory.TwParts in
theorem GlobalTheory.TwParts.mem_iSup_Wp3_of_mem_WS : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3), (R.toCx3 F).PartsW false → ∀ j (w : (R.HW j (sg0 D A3.A)).H), w ∈ R.toRealDat.WS F.lv2 false j (sg0 D A3.A) → w ∈ ⨆ p, R.Wp3 j p := by
  intro D G _ _ Pl0 I0 T A3 Ks _ _ _ R F hP j w hw
  obtain ⟨-, hsup⟩ := hP j
  refine Submodule.span_le.mpr ?_ hw
  rintro _ ⟨k, rfl⟩
  have hk := mk_bC_mem_range R F j k
  rw [← hsup] at hk
  have hk' : Tw.mk (twAt D.what₂.embLL A3.A.v0) (R.toRealDat.bC F.lv2 false j (sg0 D A3.A) k) ∈
      ⨆ p, (R.toCx3 F).Wp j p := by
    have hle : (⨆ p, (R.toCx3 F).Wp j p ⊓ LinearMap.range ((R.toCx3 F).w0C false j)) ≤ ⨆ p, (R.toCx3 F).Wp j p :=
      iSup_mono fun p => inf_le_left
    exact hle hk
  refine Submodule.iSup_induction (fun p => (R.toCx3 F).Wp j p) (motive := fun x => Tw.out (s := twAt D.what₂.embLL A3.A.v0) (E := (R.HW j (sg0 D A3.A)).H) x ∈ ⨆ p, R.Wp3 j p) hk' ?_ ?_ ?_
  · intro p x hx
    exact Submodule.mem_iSup_of_mem p hx
  · exact Submodule.zero_mem _
  · intro x y hx hy
    exact Submodule.add_mem _ hx hy
end

