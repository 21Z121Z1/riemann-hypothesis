import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0017
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.GaussianBinomialClosedForm
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsUniqueIsConjAt
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RamificationIdxEqOneOfIsSquare
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0019
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0081
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0167
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0154
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0090
import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0018
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0149
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0170
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0189
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0024
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0019
import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0005
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0179
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0011
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0024
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IwasawaDoubledHermitianSpaceRealPlace
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0174
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0021
import Development.AbelianVarietyTheory.Definitions.Foundations.EventuallyEqOfIsPreconnected

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnramifiedDoublingIntegralInertAdelic
section
open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP

namespace GlobalTheory.LocZetaInertAd

theorem domain_of_bound {q : ℕ} (hq : 2 ≤ q) {n : ℕ} (α : Fin (n / 2) → ℂˣ) {ε : ℂ} (hε : ‖ε‖ = 1) {s : ℂ}
    (hs : (n : ℝ) < s.re) (hα : ∀ i, ‖((α i : ℂˣ) : ℂ)‖ ≤ ((q ^ 2 : ℕ) : ℝ) ^ ((n : ℝ) / 2) ∧
      ‖(((α i)⁻¹ : ℂˣ) : ℂ)‖ ≤ ((q ^ 2 : ℕ) : ℝ) ^ ((n : ℝ) / 2)) :
    GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables.Domain (GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables.varY q ε s) α := by
  have hq0 : (0 : ℝ) < q := by exact_mod_cast (by omega : 0 < q)
  have hq1 : (1 : ℝ) < q := by exact_mod_cast (by omega : 1 < q)
  have hy : ‖GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables.varY q ε s‖ = (q : ℝ) ^ (-(2 * s.re + 1)) := by
    rw [GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables.varY, norm_mul, hε, one_mul, Complex.norm_natCast_cpow_of_pos (by omega)]
    congr 1
    simp
  have hQ : ((q ^ 2 : ℕ) : ℝ) ^ ((n : ℝ) / 2) = (q : ℝ) ^ (n : ℝ) := by
    rw [Nat.cast_pow, ← Real.rpow_natCast (q : ℝ) 2, ← Real.rpow_mul hq0.le]
    congr 1; push_cast; ring
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have key : (q : ℝ) ^ (-(2 * s.re + 1)) * (q : ℝ) ^ (n : ℝ) < 1 := by
    rw [← Real.rpow_add hq0]
    exact Real.rpow_lt_one_of_one_lt_of_neg hq1 (by linarith)
  have hpos : (0 : ℝ) ≤ (q : ℝ) ^ (-(2 * s.re + 1)) := (Real.rpow_pos_of_pos hq0 _).le
  refine ⟨?_, fun i => ⟨?_, ?_⟩⟩
  · rw [hy]
    exact Real.rpow_lt_one_of_one_lt_of_neg hq1 (by linarith)
  · rw [hy]
    exact lt_of_le_of_lt (mul_le_mul_of_nonneg_left ((hα i).1.trans hQ.le) hpos) key
  · rw [hy]
    have := (hα i).2
    rw [Units.val_inv_eq_inv_val, norm_inv] at this
    exact lt_of_le_of_lt (mul_le_mul_of_nonneg_left (this.trans hQ.le) hpos) key

end GlobalTheory.LocZetaInertAd

namespace GlobalTheory.LocZetaInertAd

set_option maxHeartbeats 400000 in
theorem localZetaOn_inert : GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables.UnramDoublingInert → ∀ D : D7, ParamBoundOn D (fun v => ¬ Formalism.MainNotions.SchurIrreducible.IsSplit (E := D.host.E) v) → LocalZetaOn D fun v => ¬ Formalism.MainNotions.SchurIrreducible.IsSplit (E := D.host.E) v := by
  intro hU D hPB A L hL χ b hχ hRes v hv hunr μ hμ hμK s hs φ hφ par c hc
  classical
  have hcm := isCMExt_host D
  have h2 : Module.finrank D.host.F D.host.E = 2 := hcm.2.2.1
  obtain ⟨w, h⟩ : ∃ w : HeightOneSpectrum (𝓞 D.host.E), w.under (𝓞 D.host.F) = v := by
    have := v.isMaximal
    obtain ⟨Q, hQ, hl⟩ := Ideal.exists_maximal_ideal_liesOver_of_isIntegral (S := 𝓞 D.host.E) v.asIdeal
    exact ⟨⟨Q, hQ.isPrime, Ideal.ne_bot_of_liesOver_of_ne_bot v.ne_bot Q⟩, HeightOneSpectrum.ext hl.over.symm⟩
  have hc' := hc
  obtain ⟨-, V, _, _, ρ, x, ℓ, hpar, hℓ, hcx⟩ := hc'
  have hfix := (hpar w h).mem_fixed
  rcases hpar w h with ⟨hsplit, -⟩ | ⟨hw, c', ϖ0, e, α, hUI, he, hsat, hBw⟩
  · exact absurd hsplit hv
  have hϖ0 : ϖ0 ≠ 0 := by
    intro h0
    have := hUI.2.2.2.1
    rw [h0, map_zero] at this
    exact WithZero.zero_ne_coe this
  let ϖ : (w.adicCompletion D.host.E)ˣ := Units.mk0 ϖ0 hϖ0
  obtain ⟨hUnr, hχϖ, hχϖb, Φ, hΦ, hφΦ⟩ := GlobalTheory.KerInert.sphSec_inert D A L hL χ b hRes v w h hw (hunr w h) s φ hφ c' ϖ e hUI he
  let ρ' : Representation ℂ (Formalism.UG.GU c' A.rank) V := ρ.comp e.symm.toMonoidHom
  have hℓ' : ∀ k ∈ Formalism.UG.KU c' A.rank, ∀ g, ℓ (ρ' (k * g) x) = ℓ (ρ' g x) := by
    intro k hk g
    have hk' : e.symm k ∈ stabLoc D.sp.cm.sig A.gram L v := (he.2.2 _).2 (by simpa using hk)
    have := hℓ _ hk' (e.symm g)
    simpa [ρ'] using this
  have hdom : ℓ x ≠ 0 → GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables.Domain
      (GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables.varY (Formalism.UG.qV D.host.F v) (GlobalTheory.LFun.locChar χ⁻¹ w ϖ) s) α := by
    intro hx0
    have hc1 : c 1 ≠ 0 := by rw [hcx, map_one, Module.End.one_apply]; exact hx0
    obtain ⟨-, hbd⟩ := hPB A L hL v hv par c hc hc1 w h
    have hN : Ideal.absNorm w.asIdeal = Formalism.UG.qV D.host.F v ^ 2 := GlobalTheory.LFun.InertChart.absNorm_eq h2 hw
    have hq : 2 ≤ Formalism.UG.qV D.host.F v := hUI.2.2.2.2.2.1
    refine GlobalTheory.LocZetaInertAd.domain_of_bound hq α (GlobalTheory.LFun.norm_locChar _ _ _) (by exact_mod_cast hs) fun i => ?_
    have h1 := hbd (α i) (by rw [hBw]; simp [GlobalTheory.LGrp.bcParam])
    have h3 := hbd (α i)⁻¹ (by rw [hBw]; simp [GlobalTheory.LGrp.bcParam])
    rw [hN] at h1 h3
    exact ⟨h1, h3⟩
  obtain ⟨hΦK, hsum⟩ := GlobalTheory.DoublingSumU.hasSum_doubling_inert hU (w.adicCompletion D.host.E) ϖ c' (Formalism.UG.qV D.host.F v) A.rank hUI
    (GlobalTheory.LFun.locChar χ⁻¹ w) hUnr b hχϖb s Φ hΦ V ρ' x α hsat ℓ hℓ' hdom
  have hsum' : HasSum (fun a : Gv A v ⧸ stabLoc D.sp.cm.sig A.gram L v =>
      φ (ioAt A v a.out) * c a.out)
      (GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables.stdL (Formalism.UG.qV D.host.F v) A.rank α (GlobalTheory.LFun.locChar χ⁻¹ w ϖ) (s + 1 / 2) /
        GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables.dFac (Formalism.UG.qV D.host.F v) A.rank b s * ℓ x) := by
    refine GlobalTheory.T.hasSum_quotient_of_hasSum_mulEquiv_quotient _ _ e _ _ he.2.2 (fun g => φ (ioAt A v g) * c g) ?_ _ ?_
    · intro g k hk
      show φ (ioAt A v (g * k)) * c (g * k) = φ (ioAt A v g) * c g
      rw [hφΦ, hφΦ, map_mul, hΦK _ _ ((he.2.2 k).1 hk), hcx, hcx, map_mul, Module.End.mul_apply,
        GlobalTheory.LGrp.mem_fixed.1 hfix k hk]
    · have hfun : ∀ a : Formalism.UG.GU c' A.rank ⧸ Formalism.UG.KU c' A.rank, φ (ioAt A v (e.symm a.out)) * c (e.symm a.out) =
          Φ (GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables.io1 c' A.rank a.out) * ℓ (ρ' a.out x) := fun a => by
        rw [hφΦ, hcx, MulEquiv.apply_symm_apply]; rfl
      simp only [hfun]
      exact hsum
  haveI := hL.1
  obtain ⟨hint, hval⟩ := GlobalTheory.T.integral_right_invariant_eq_sum_open_subgroup_cosets (Gv A v) μ (stabLoc D.sp.cm.sig A.gram L v) (isOpen_stabLoc _ _ _ v) hμK
    (fun g => φ (ioAt A v g) * c g) _ (fun g k hk => by
      show φ (ioAt A v (g * k)) * c (g * k) = φ (ioAt A v g) * c g
      rw [hφΦ, hφΦ, map_mul, hΦK _ _ ((he.2.2 k).1 hk), hcx, hcx, map_mul, Module.End.mul_apply,
        GlobalTheory.LGrp.mem_fixed.1 hfix k hk]) hsum'
  refine ⟨hint, ?_⟩
  rw [hval, GlobalTheory.LFun.LvTw_div_dv_inert_eq_stdL _ _ par (GlobalTheory.LFun.val χ) v w A.rank b α s h2 hw (GlobalTheory.LFun.isUnram_of_isInertAt hw) hBw, ← hχϖ,
    hcx 1, map_one, Module.End.one_apply]

end GlobalTheory.LocZetaInertAd
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnramifiedHeckeVacuumLargerEqSmaller
section
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep
open GlobalTheory.FinZeta (Gv embV Kv VacFin IsLocKer KerU)
open GlobalTheory.SphTheta (IsStd CayleyRule intMat liftPar)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke IsCommensurated Tj SatU ordL Ov)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.LFun (heckeVec)

namespace GlobalTheory.ChainOnto

open Formalism.UG GlobalTheory.Hk3 GlobalTheory.SphTheta in

theorem heckeVec_howe : GlobalTheory.Hk3.HoweUnram → ∀ (L : Type) [Field L] [CharZero L] [Valued L (WithZero (Multiplicative ℤ))] [CompleteSpace L] (ϖ : L) (σ : L →+* L) (q : ℕ) (δ : L) (ψ : AddChar L ℂ) (n n' : ℕ) (M : Type) [AddCommGroup M] [Module ℂ M] (ρ : Matrix (Fin n') (Fin n) L → Module.End ℂ M) (ω : GU σ n × GU σ n' →* Module.End ℂ M) (s : M), IsStd ϖ σ q δ ψ ρ ω s → ∀ h' ∈ Hecke ℂ (KU σ n'), ∃ h ∈ Hecke ℂ (KU σ n), heckeVec (ω.comp (MonoidHom.inl _ _)) (KU σ n) h s = heckeVec (ω.comp (MonoidHom.inr _ _)) (KU σ n') h' s := by
  intro hH L _ _ _ _ ϖ σ q δ ψ n n' M _ _ ρ ω s hS h' hh'
  have hU := hS.1.unr
  obtain ⟨-, hw2⟩ := hH L ϖ σ q δ n n' (antiG L n) (antiG L n') ψ M ρ ω hS.1 s hS.2.1 hS.2.2.1 hS.2.2.2
  have hK := P.isCommensurated_integral_unitary_of_unramified hU n
  have hK' := P.isCommensurated_integral_unitary_of_unramified hU n'
  have f1 : ∀ k ∈ KU σ n, ω (k, 1) s = s := fun k hk => hS.1.fix k 1 (mem_KU_iff.1 hk) (one_mem _) s hS.2.2.1
  have f2 : ∀ k ∈ KU σ n', ω (1, k) s = s := fun k hk => hS.1.fix 1 k (one_mem _) (mem_KU_iff.1 hk) s hS.2.2.1
  set w := heckeVec (ω.comp (MonoidHom.inr _ _)) (KU σ n') h' s with hw
  have w1 : ∀ k ∈ KU σ n, ω (k, 1) w = w := fun k hk => by
    rw [hw, GlobalTheory.LFun.map_heckeVec hK' hh' (ρ' := ω.comp (MonoidHom.inr _ _)) (ω (k, 1)) (fun g y => by
      show (ω (k, 1) * ω (1, g)) y = (ω (1, g) * ω (k, 1)) y
      rw [← map_mul, ← map_mul]
      simp), f1 k hk]
  have w2 : ∀ k ∈ KU σ n', ω (1, k) w = w := fun k hk => by
    have hs : s ∈ GlobalTheory.PRep.fixed (ω.comp (MonoidHom.inr _ _)) (KU σ n') := GlobalTheory.LGrp.mem_fixed.2 f2
    let e : GU σ n' ⧸ KU σ n' ≃ GU σ n' ⧸ KU σ n' := MulAction.toPerm k
    conv_rhs => rw [hw, GlobalTheory.LFun.heckeVec_eq_of_section hh'.1 hs (fun c => k * (e.symm c).out) (fun c => by
      rw [← smul_eq_mul, ← MulAction.Quotient.smul_mk, QuotientGroup.out_eq']
      exact e.apply_symm_apply c), ← finsum_comp_equiv e]
    rw [hw]
    refine ((ω (1, k)).toAddMonoidHom.map_finsum (GlobalTheory.LFun.finite_heckeVec hK' hh' _ s)).trans (finsum_congr fun c => ?_)
    have := hh'.1 ⟨k, hk⟩ 1 c.out
    simp only [OneMemClass.coe_one, mul_one] at this
    simp only [Equiv.symm_apply_apply, this, map_mul, LinearMap.toAddMonoidHom_coe, map_smul]
    rfl
  obtain ⟨h, hh, e⟩ := GlobalTheory.T.exists_hecke_translate_of_mem_span_fixed_translates _ (KU σ n) hK M (ω.comp (MonoidHom.inl _ _)) s w f1 w1
    (hw2 w fun g hg => w2 g (mem_KU_iff.2 hg))
  exact ⟨h, hh, e⟩

end GlobalTheory.ChainOnto

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UpInjWOfAForm
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift GlobalTheory.Core.Rk.Exh

namespace GlobalTheory.Core.Rk.UpInjWProof

theorem upInjW_of_aForm : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Hk3.Core R F → GlobalTheory.Hk3.SchurAll R → (∀ χ ∈ A.X, IsAbsIrrChar χ) → ∀ SF, GlobalTheory.Hk3.IsSF R SF → GlobalTheory.LiftRows.AForm R SF → GlobalTheory.LiftRows.UpInjW R := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F hC hS hIrr SF hSF hA
  obtain ⟨a, ha, hAF⟩ := hA
  intro i t x hx h0
  obtain ⟨h, -, -, -, hspan, -⟩ := GlobalTheory.SphOpsModel.sphericalOperators_forms_on_rank_space_normal_alt R F hC hS hIrr SF hSF i

  have hpart : ∀ c, GlobalTheory.Hk3.Wcc R SF i c ≤ LinearMap.range (R.thG i t) := by
    intro c y hy
    by_cases hc : GlobalTheory.Hk3.Wcc R SF i c = ⊥
    · rw [hc] at hy
      rw [(Submodule.mem_bot ℂ).1 hy]
      exact Submodule.zero_mem _
    · obtain ⟨z, hz, hS'⟩ := hAF i t c hc
      obtain ⟨B, -, -, hzpos, -⟩ := hz
      have hne : ((a i * z : ℝ) : ℂ) ≠ 0 := by
        exact_mod_cast (mul_pos (ha i) hzpos).ne'
      refine ⟨((a i * z : ℝ) : ℂ)⁻¹ • LinearMap.adjoint (R.thG i t) y, ?_⟩
      rw [map_smul, hS' y hy, smul_smul, inv_mul_cancel₀ hne, one_smul]
  have hxr : x ∈ LinearMap.range (R.thG i t) := by
    have : x ∈ LinearMap.range (GlobalTheory.Hk3.eH R i) := ⟨x, hx⟩
    rw [← hspan] at this
    exact (iSup_le hpart) this
  obtain ⟨v, rfl⟩ := hxr
  have h1 : ⟪R.thG i t v, R.thG i t v⟫_ℂ = 0 := by
    rw [← LinearMap.adjoint_inner_right, h0, inner_zero_right]
  exact inner_self_eq_zero.1 h1

end GlobalTheory.Core.Rk.UpInjWProof
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilRepPreservesFockDegreeOfCommuteCartanStatement
section
open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weilRep_preserves_fockDegree_of_commute_cartan : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : WRep S T) (sS : RealMat S) (sT : RealMat T), IsWeilDatumO ψ S T χS χT om → IsInfFam θ → ∀ k : GA D S, (∀ τ, compAt θ τ (Formalism.L2.Theta.mt S k) * sS τ = sS τ * compAt θ τ (Formalism.L2.Theta.mt S k)) → ∀ (N : ℕ) (f : WO S T → ℂ), IsThetaFunO ψ S T f → (∀ l : List (D.what₂.Tau × Matrix (Fin T.rank) (Fin S.rank) ℂ), l.length = N → l.foldr (fun p f => annih (heisO ψ S T) θ p.1 (cplxO (sS p.1) (sT p.1)) p.2 f) f = 0) → ∀ l : List (D.what₂.Tau × Matrix (Fin T.rank) (Fin S.rank) ℂ), l.length = N → l.foldr (fun p f => annih (heisO ψ S T) θ p.1 (cplxO (sS p.1) (sT p.1)) p.2 f) (om (k, 1) f) = 0 := by
  first | exact @GlobalTheory.CartanFockDeg.om_keeps_fockDeg | exact GlobalTheory.CartanFockDeg.om_keeps_fockDeg | (intros; apply GlobalTheory.CartanFockDeg.om_keeps_fockDeg <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WittHyperbolicIsotropicColumnsAtRealPlace
section
open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec)
open GlobalTheory.Mem.Th (CptF)
open GlobalTheory.Core.Rk.IP
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.Exh GlobalTheory.RegSW
open GlobalTheory.AdelicU Formalism.UG

namespace GlobalTheory.IsoColReal

theorem compInf_incA {D : D7} (w : InfinitePlace D.host.F) (x : D.host.E) :
    compInf D.host.F D.host.E w (incA D x) = inclR (F := D.host.F) w.Completion x := by
  simp [compInf, incA, inclR, Algebra.TensorProduct.includeRight_apply, Algebra.TensorProduct.map_tmul]

theorem sigR_inclR_real {D : D7} (w : InfinitePlace D.host.F) (x : D.host.E) :
    Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR w.Completion D.sp.cm.sig (inclR (F := D.host.F) w.Completion x) = inclR (F := D.host.F) w.Completion (star x) := by
  simp [Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR, inclR, Algebra.TensorProduct.includeRight_apply, Algebra.TensorProduct.map_tmul]
  rfl

theorem isotropic_at_real : ∀ {D : D7} {T T₀ : HSp D} {r : ℕ} (d : HypDec T T₀ r) (w : InfinitePlace D.host.F), (Formalism.UG.cT (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR w.Completion D.sp.cm.sig) (Matrix.map d.jX (compInf D.host.F D.host.E w)) * Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.JR w.Completion T.gram : Matrix (Fin r) (Fin T.rank) (TensorProduct D.host.F w.Completion D.host.E)) * Matrix.map d.jX (compInf D.host.F D.host.E w) = 0 := by
  intro D T T₀ r d w
  have hm : Matrix.map d.jX (compInf D.host.F D.host.E w) = d.e.map (inclR (F := D.host.F) w.Completion) := by
    ext i j
    simp [HypDec.jX, rat, compInf_incA]
  have hc : Formalism.UG.cT (sigR w.Completion D.sp.cm.sig) (d.e.map (inclR (F := D.host.F) w.Completion)) =
      (d.eᴴ).map (inclR (F := D.host.F) w.Completion) := by
    ext i j
    simp [Formalism.UG.cT, Matrix.conjTranspose_apply, sigR_inclR_real]
  have hJ : JR w.Completion T.gram = T.gram.map (inclR (F := D.host.F) w.Completion) := rfl
  rw [hm, hc, hJ]
  have h0 := congrArg (fun M => M.map (inclR (F := D.host.F) w.Completion)) d.ee
  simp only [Matrix.map_mul, Matrix.map_zero, map_zero] at h0
  exact h0

end GlobalTheory.IsoColReal
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ZetaResidueNeZeroOfSimplePoleLiftLFunction
section
open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec)
open GlobalTheory.Mem.Th (CptF)
open GlobalTheory.Core.Rk.IP
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.Exh GlobalTheory.RegSW

noncomputable section

namespace GlobalTheory.Core.Rk.Exh

open Filter Topology

theorem residue_ne_zero_of_simplePole : GlobalTheory.IndefiniteRowSideFullHecke.SimplePoleTwistedLift.SimplePole → ∀ (D : D7) (S : Finset (FinPl D)) (r t : ℕ) (c par : GlobalTheory.LFun.Fam D.host.E) (χ : (AE D)ˣ →* Circle), GlobalTheory.IndefiniteRowSideFullHecke.SimplePoleTwistedLift.Hyp (S : Set (FinPl D)) r t c par (GlobalTheory.LFun.val (F := D.host.F) χ) (GlobalTheory.LFun.val (F := D.host.F) χ) → ∀ (a b : ℕ) (Z : ℂ → ℂ) (C z : ℂ), C ≠ 0 → EqRight Z (fun s => GlobalTheory.LFun.LSD D S par χ (s + 1 / 2) / GlobalTheory.LFun.dSfun D.host.E (S : Set (FinPl D)) a b s * C) → CoeffAt Z ((t : ℂ) / 2) (-1) z → z ≠ 0 := by
  intro hSP D S r t c par χ hH a b Z C z hC hZ hz
  obtain ⟨-, -, ⟨Z0, hZ0⟩, h4⟩ := hSP D.host.F D.host.E (S : Set (FinPl D)) r t c par
    (GlobalTheory.LFun.val (F := D.host.F) χ) (GlobalTheory.LFun.val (F := D.host.F) χ) hH
  obtain ⟨hmer, -, heq, -, -, ρ, hρ, hlim⟩ := h4 Z0 hZ0
  set R := GlobalTheory.IndefiniteRowSideFullHecke.SimplePoleTwistedLift.rhs (S : Set (FinPl D)) c (GlobalTheory.LFun.val (F := D.host.F) χ) t Z0 with hR
  set d := GlobalTheory.LFun.dSfun (F := D.host.F) D.host.E (S : Set (FinPl D)) a b with hd
  obtain ⟨hdan, hdne⟩ := dSfun_analytic_ne_zero D (S : Set (FinPl D)) a b
  have ht : (r : ℝ) + 5 ≤ t := by exact_mod_cast hH.2.1
  have hr0 : (0 : ℝ) ≤ (r : ℝ) / 2 := by positivity
  have htr : (r : ℝ) / 2 < ((t : ℂ) / 2).re := by
    have : ((t : ℂ) / 2).re = (t : ℝ) / 2 := by simp
    rw [this]; linarith
  have hext : IsExtAt (fun s => GlobalTheory.LFun.LSD D S par χ (s + 1 / 2) / d s * C) ((t : ℂ) / 2)
      (fun s => R (s + 1 / 2) / d s * C) := by
    refine ⟨rightOf ((r : ℝ) / 2), htr, isRightDomain_rightOf _, fun s hs => ?_, (t : ℝ) / 2, fun s hs => ?_⟩
    · have hs0 : (r : ℝ) / 2 < s.re := hs
      have hs' : ((r : ℝ) + 1) / 2 < (s + 1 / 2).re := by
        have : (s + 1 / 2).re = s.re + 1 / 2 := by simp
        rw [this]; linarith
      have h1 : MeromorphicAt (fun s => R (s + 1 / 2)) s :=
        MeromorphicAt.comp_analyticAt (g := (· + 1 / 2)) (hmer _ hs') (by fun_prop)
      have h2 : MeromorphicAt d s := (hdan s (show (0 : ℝ) < s.re by linarith)).meromorphicAt
      exact (h1.div h2).mul (MeromorphicAt.const C s)
    · have hs0 : (t : ℝ) / 2 < s.re := hs
      have hs' : ((t : ℝ) + 1) / 2 < (s + 1 / 2).re := by
        have : (s + 1 / 2).re = s.re + 1 / 2 := by simp
        rw [this]; linarith
      show R (s + 1 / 2) / d s * C = GlobalTheory.LFun.LSD D S par χ (s + 1 / 2) / d s * C
      rw [heq _ hs']
  have hext' : IsExtAt Z ((t : ℂ) / 2) (fun s => R (s + 1 / 2) / d s * C) := hext.congr hZ.symm
  have hpos : (0 : ℝ) < ((t : ℂ) / 2).re := lt_of_le_of_lt hr0 htr
  have hd0 : d ((t : ℂ) / 2) ≠ 0 := (hdne _ hpos).1
  have hshift : Tendsto (fun s : ℂ => s + 1 / 2) (𝓝[≠] ((t : ℂ) / 2)) (𝓝[≠] ((1 + (t : ℂ)) / 2)) := by
    have h := (Homeomorph.addRight (1 / 2 : ℂ)).map_punctured_nhds_eq ((t : ℂ) / 2)
    have e : (t : ℂ) / 2 + 1 / 2 = (1 + (t : ℂ)) / 2 := by ring
    have h' : map (fun x : ℂ => x + 1 / 2) (𝓝[≠] ((t : ℂ) / 2)) = 𝓝[≠] ((t : ℂ) / 2 + 1 / 2) := h
    rw [e] at h'
    exact h'.le
  have h2 : Tendsto d (𝓝[≠] ((t : ℂ) / 2)) (𝓝 (d ((t : ℂ) / 2))) :=
    (hdan _ hpos).continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have hlim' : Tendsto (fun s => (s - (t : ℂ) / 2) ^ (1 : ℕ) * (R (s + 1 / 2) / d s * C)) (𝓝[≠] ((t : ℂ) / 2))
      (𝓝 (ρ / d ((t : ℂ) / 2) * C)) := by
    refine (((hlim.comp hshift).div h2 hd0).mul_const C).congr fun s => ?_
    simp only [Pi.div_apply, Function.comp_apply, pow_one]
    ring
  have hc := hext'.coeffAt_of_tendsto hlim'
  have e := hz.unique (by simpa using hc)
  rw [e]
  exact mul_ne_zero (div_ne_zero hρ hd0) hC

end GlobalTheory.Core.Rk.Exh

end
end

