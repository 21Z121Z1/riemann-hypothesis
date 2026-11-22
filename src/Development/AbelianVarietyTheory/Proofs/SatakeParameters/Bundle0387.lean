import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0019
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Imports
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0006
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0008
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle0004
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.HeckeLAdicCharacterAboveIff
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle0009
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsPolarizedTwistAbsPow
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0222
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0295
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0954
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0386
import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0027
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.JointCmpEmbeddingY
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0302
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0477
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.RealAt
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0031
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.EquivFrameBTheta
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0349
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0345
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0376
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0381
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0382
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0379
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0359
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0378
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0367
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0356
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1322
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle0035
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.ThetaSatakeParametersInverse
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle0034
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0101
import GroundTheory.GlobalFields.NormResidueSymbol.FunctorialFinite
import GroundTheory.GlobalFields.NormResidueSymbol.Bundle0001
import CompanionTheory.AutomorphicTheory.UnitriangularMeasure.AdeleCoordinateMeasure.EllipticTorusNorm

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsGoodConjSelfDualTwistSplitUnramified
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.Published

noncomputable section
namespace GlobalTheory.GoodCsdTwist

open GlobalTheory.ContraPair

theorem unrAt_mul {K : Type} [Field K] [NumberField K] {χ χ' : HChar K} {v : HeightOneSpectrum (𝓞 K)}
    (h : χ.UnrAt v) (h' : χ'.UnrAt v) : (χ * χ').UnrAt v := fun x hx => by
  change χ.loc v x * χ'.loc v x = 1
  rw [h x hx, h' x hx, mul_one]

theorem unrAt_inv {K : Type} [Field K] [NumberField K] {χ : HChar K} {v : HeightOneSpectrum (𝓞 K)}
    (h : χ.UnrAt v) : (χ⁻¹).UnrAt v := fun x hx => by
  change (χ.loc v x)⁻¹ = 1
  rw [h x hx, inv_one]

theorem unrAt_pow {K : Type} [Field K] [NumberField K] {χ : HChar K} {v : HeightOneSpectrum (𝓞 K)}
    (h : χ.UnrAt v) : ∀ k : ℕ, (χ ^ k).UnrAt v
  | 0 => fun _ _ => rfl
  | k + 1 => by rw [pow_succ]; exact unrAt_mul (unrAt_pow h k) h

theorem isAlgPos_mul {F : Type} [Field F] [NumberField F] {χ χ' : HChar F} {n n' : (F →+* ℂ) → ℤ}
    (h : IsAlgPos χ n) (h' : IsAlgPos χ' n') : IsAlgPos (χ * χ') (n + n') := fun k hk => by
  have e : (χ * χ').inf k = χ.inf k * χ'.inf k := rfl
  rw [e, Units.val_mul, h k hk, h' k hk, ← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun φ _ => (zpow_add₀ ((map_ne_zero φ).2 k.ne_zero) _ _).symm

theorem regAlg_twist {K : Type} [Field K] [NumberField K] [IsTotallyComplex K] {n : ℕ} {P : CuspSub K n}
    (h : (CG.mk P).IsRegAlg) {κ : HChar K} {m : (K →+* ℂ) → ℤ} (hκ : κ.IsAlg m) : (CG.mk (P.twist κ)).IsRegAlg := (GlobalTheory.CuspRep.CG.isRegAlg_iff _).2 fun τ => by
  have e := ((ParLaws.hasInfChar_infChar (CG.mk P) τ).twist κ).infChar_eq
  rw [CG.twist_mk] at e
  rw [e, (InfType.expo_of_infType K κ).1 m hκ τ]
  refine ⟨(h τ).1.map (add_left_injective _), fun z hz => ?_⟩
  obtain ⟨y, hy, rfl⟩ := Multiset.mem_map.1 hz
  obtain ⟨k, rfl⟩ := (h τ).2 y hy
  exact ⟨k + m τ, by push_cast; ring⟩

theorem neg_one_zpow_natAbs (z : ℤ) : ((-1 : ℂˣ) ^ z.natAbs) = (-1 : ℂˣ) ^ (-z) := by
  rcases Int.even_or_odd z with h | h
  · rw [h.neg.neg_one_zpow, (Int.natAbs_even.2 h).neg_one_pow]
  · rw [h.neg.neg_one_zpow, (Int.natAbs_odd.2 h).neg_one_pow]

theorem exists_goodCsd_twist : AutomorphicFormsFiniteGL → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (l a : ℕ), 1 ≤ a →
    ∀ (π : CuspSub E a) (χ : HChar (maximalRealSubfield E)), InScope .good l π χ → ∀ w₀ : HeightOneSpectrum (𝓞 E),
    GlobalTheory.UnitaryBC.IsSplitAt w₀ → ∃ (κ : HChar E) (m : (E →+* ℂ) → ℤ), κ.IsAlg m ∧ κ.UnrAt w₀ ∧
    InScope .csd l (π.twist κ) (quadChar E ^ a) := by
  intro _ E _ _ _ l a ha π χ ⟨hreg, hpol, hgood⟩ w₀ hw₀
  obtain ⟨n, hn⟩ := GlobalTheory.RegAlgCharAlg.isAlgPos_of_polarizedPair E a ha π χ hreg hpol
  obtain ⟨φ₀⟩ : Nonempty (maximalRealSubfield E →+* ℂ) := inferInstance
  have hb : IsAlgPos χ (fun _ => n φ₀) := by
    rw [show (fun _ => n φ₀) = n from funext fun φ => UpperTheory.heckeChar_parallel_weight _ χ n hn φ₀ φ]
    exact hn
  have hinv : IsAlgPos χ⁻¹ (fun _ => -n φ₀) := fun k hk => by
    rw [HChar.inf_inv, Units.val_inv_eq_inv_val, hb k hk, ← Finset.prod_inv_distrib]
    exact Finset.prod_congr rfl fun φ _ => (zpow_neg _ _).symm
  have ho : (quadChar E ^ (a + (n φ₀).natAbs)).OrderDvd 2 := by
    unfold HChar.OrderDvd
    rw [← pow_mul, mul_comm, pow_mul]
    have : (quadChar E) ^ 2 = 1 := by
      refine Subtype.ext (MonoidHom.ext fun x => ?_)
      change (Units.map (Int.castRingHom ℂ).toMonoidHom (GlobalTheory.IdeleNormChar.normSign E x)) ^ 2 = 1
      rw [← map_pow, Int.units_sq, map_one]
    rw [this, one_pow]
  have hpos := isAlgPos_mul hinv (isAlgPos_zero_of_orderDvd two_pos ho)
  rw [add_zero] at hpos
  have hsign : ∀ v, (χ⁻¹ * quadChar E ^ (a + (n φ₀).natAbs)).locInf v (-1) = (-1) ^ (-n φ₀) := fun v => by
    rw [HChar.locInf_mul, locInf_pow, quadChar_locInf]
    change (χ.locInf v (-1))⁻¹ * _ = _
    rw [hpol.sign v, pow_add, inv_mul_cancel_left, neg_one_zpow_natAbs]
  have halg := UpperTheory.heckeChar_algebraic_of_sign _ _ (-n φ₀) hpos hsign
  have hunr : ∀ w : HeightOneSpectrum (𝓞 E), ¬ GlobalTheory.UnitaryBC.IsSplitAt w →
      Algebra.IsUnramifiedAt (𝓞 (maximalRealSubfield E)) w.asIdeal ∧
      (χ⁻¹ * quadChar E ^ (a + (n φ₀).natAbs)).UnrAt (w.under (𝓞 (maximalRealSubfield E))) := fun w hw => by
    obtain ⟨-, hu, hsat⟩ := hgood.2.2 w hw
    have h1 := GlobalTheory.T.heckeChar_unrAt_of_spherical_and_twist_spherical E a ha π _ w hsat (GlobalTheory.T.isSpherical_twist_of_contragredient_conjugate E a ha π _ hpol.dual w hw hsat)
    replace h1 := unrAt_inv h1
    rw [inv_inv] at h1
    exact ⟨hu, unrAt_mul (unrAt_inv (GlobalTheory.T.heckeChar_unrAt_under_of_compNorm_unramified E χ w hw hu h1)) (unrAt_pow (GlobalTheory.T.quadraticHeckeChar_unramified_of_isUnramifiedAt E w hu) _)⟩
  obtain ⟨κ, m, hκ, hres, hκ0, hκu⟩ := GlobalTheory.T.exists_algebraic_hecke_char_split E _ (-n φ₀) halg hunr w₀ hw₀
  refine ⟨κ, m, hκ, hκ0, regAlg_twist hreg hκ, ⟨fun v => ?_, ?_⟩, ⟨hgood.1, hgood.2.1, fun w hw => ?_⟩, rfl⟩
  · rw [locInf_pow, quadChar_locInf]
  · rw [map_pow, compNorm_quadChar, one_pow, dualIsConjBy_one]
    exact UpperTheory.V.Af.Cq.csdTwist E a π _ κ hpol.dual
      (by rw [hres, map_mul, map_inv, map_pow, compNorm_quadChar, one_pow, mul_one])
  · obtain ⟨h1, h2, B, hB⟩ := hgood.2.2 w hw
    refine ⟨h1, h2, B.map (· * κ.val w), ?_⟩
    rw [CG.hasSat_mk] at hB ⊢
    exact GlobalTheory.SphGal.hasSatGL_twist E a π κ w B (hκu w hw) hB

end GlobalTheory.GoodCsdTwist
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.JointsAtAllStd
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Ker Formalism.L2.Forms GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Fc GlobalTheory.Svd NumberField IsDedekindDomain

set_option maxHeartbeats 1000000

theorem GlobalTheory.Svd.jointsAt_all_std : ∀ (B : GlobalTheory.Mem.Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T) (Z : w.Lt) (O : Obj (w.D Z)), Part w Z (ofObj O) → G.LatTied O.gatT O.Gx O.Gy → (∃ t : KerEntTied O.ex, ∀ μ, GlobalTheory.TwV.JointsAt t μ) ∧ ∀ u, O.ex.tw.e0 u (w.D Z).what₂.mu0 = O.ex.tw.eMu0 u 0 (Nat.zero_le _) := by
  intro B f T w Z O P hL
  obtain ⟨htw, -, hpiT, -, t, hstd, -, -⟩ := GlobalTheory.Svd.Part.kerTie B f T w Z O P
  have hchi := (GlobalTheory.Mem.ChiDVal.chiD_values_and_cc_top B f T w Z).1
  obtain ⟨L, gatT, Gx, Gy, K, X, cX, ex⟩ := O
  obtain ⟨pin, col, errX, tp, xi, qp, ker0, ker_eq, ker⟩ := P
  simp only [ofObj, extraObj] at ker_eq
  have h1 := congrArg Sigma.fst ker_eq
  simp only at h1
  subst h1
  have h2 := eq_of_heq (Sigma.mk.inj ker_eq).2
  have h3 := congrArg Sigma.fst h2
  simp only at h3
  obtain ⟨lev, th, th_io, cmp, lat, tw, exker⟩ := ex
  simp only at h3
  subst h3
  exact GlobalTheory.T.kernel_relation_true_columns_joints_all_tuples w.I w.ok w.pins w.l w.l0 Z L col.Gt Gx Gy K X cX _ t col.C col.full col.g _ tp xi
    pin.isTw pin.jets htw hpiT hstd col.std col.stdLv col.stdDt col.herm_eq col.forms_eq hchi hL
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.KernelSiteFrameValuesAllStepsLtM
section
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelProjection Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.KerInert.SecondKernelInstances Formalism.L2.KerInert.SecondKernelSeries GlobalTheory.TwV GlobalTheory.TwV.DelB GlobalTheory.TwV.DelA

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwV.DelA

theorem tieDel_all_steps : AllSites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S => J.Dict std → S.Pair → S.Pos → S.Law → ∀ j < D.R.m, S.Del j) := by
  intro D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X _ std t J S hDict hPair hPos hLaw j hj ι hι
  letI := wittFractionAlgebraCp (D.what₂.places.resChar w)
  letI := algKfC S.E.toCEmb
  have hj1 : j + 1 ≤ D.R.m := hj
  by_cases hne : Nonempty (Lv.comp j) ∧ Nonempty (Lv.comp (j + 1))
  swap
  · refine ⟨1, norm_one, ?_⟩
    intro La _ x c' L' _
    exact absurd ⟨⟨La.1⟩, ⟨c'⟩⟩ hne
  obtain ⟨⟨a⟩, ⟨a'⟩⟩ := hne
  obtain ⟨hn1, -, hsame⟩ := GlobalTheory.T.stepDeterminantConstant_unit_independent S hPos ι hι j hj1 a a'
  set cK := cKs S ι j hj1 a a' with hcK
  refine ⟨cK, hn1, ?_⟩
  obtain ⟨-, -, hrk, hRT⟩ := GlobalTheory.TwV.DelB.sysS_ranks S
  have hN := hRT j
  have h1 : ((sysS H X std).Pj (j + 1)).m + 1 = D.R.N (j + 1) := hrk (j + 1)
  obtain ⟨d0⟩ := GlobalTheory.T.exists_adelic_latticeTuple_decomposition S hDict
  intro La hLa x c' L' hL'

  have hQ : K2.SharpQ t ex.tw u μ j x (K2.qOf t ex.tw u μ j x) := by
    have hex := J.sharp j hj x
    unfold K2.qOf
    rw [dif_pos hex]
    exact Classical.choose_spec hex
  set cc := clsAt X H j La.1 La.2 with hcc
  set κ := clsAt X H (j + 1) c' L' with hκ
  set Q := K2.qOf t ex.tw u μ j x with hQdef
  set P : MvPolynomial (GL3Theta.FrV D (D.R.N (j + 1))) ℂ :=
    ((((GL3Theta.rhoOf D (t.O u μ).mt j ((t.O u μ).dt j cc) : ℂˣ) : ℂ) *
          ((GL3Theta.rhoOf' D (t.O u μ).mt j ((t.O u μ).dt (j + 1) κ) : ℂˣ) : ℂ)) •
          framePol D (t.O u μ).dgen (Q cc) ((t.rd u μ).Th t.seam t.amb j cc κ)) with hP
  have hPw : P ∈ WtPol ℂ (extNu (D.R.N (j + 1)) (Formalism.L2.Ker.nuT D u j)) :=
    Submodule.smul_mem _ _ ((wt_polDY_framePol D (rk_le _ D hN) (t.O u μ).dgen _ (Q cc) (hQ.1 cc)).2 _)
  set φ := K2.entRec t ex.tw u μ j cc x with hφ
  have hφκ : ∀ y, φ κ y = (∏ τ, (D.chTw u μ).de (j + 1) y τ ^ (D.chTw u μ).sDiv j τ)⁻¹ * frPoly (t.O u μ) (j + 1) P y := by
    intro y
    have e := (GlobalTheory.T.operatorOnFrame_and_classSummand_polynomial).2 D L hT Gi Gl Kc Dx cX ex t u μ j cc (Q cc) κ y
    have e2 : φ κ y = entQ t u μ j cc (Q cc) κ y := rfl
    rw [e2, e, hP, map_smul, Pi.smul_apply, smul_eq_mul]
    ring

  have hR : ∀ d : Dec J std, ∃ V : XR ((sysS H X std).Pj (j + 1)) ℂ, RealAt d (j + 1) hj1 h1 (c', L') φ V ∧
      MvPolynomial.map ι V = cK • S.Y.DelF j ((kaAt X H hT).cmp j x La.1 La.2) (srOf S.Y j La (c', L')) := by
    intro d
    obtain ⟨V, hV, hmap⟩ := GlobalTheory.T.transportedFramePolynomial_complex_values_at_point S hPos ι hι d j hj1 h1 (c', L') φ P hPw hφκ
    refine ⟨V, hV, ?_⟩
    rw [hmap]
    obtain ⟨hMove, hOp, hDeg⟩ := GlobalTheory.T.movedForms_operator_degrees_at_kernelSource S hDict hPos ι hι d j hj ⟨a'⟩ hN
    have hEq := GlobalTheory.FrameB.equiv_frame_b S.Y d.fd2 (ltC S.g S.hLT) (GlobalTheory.FrameB.ltC_ne S.hLT)
      ((GlobalTheory.TwV.DelB.frames_invertible S).2 d) j
    have hsc : ∀ (La : (sysS H X std).Lt j) (La' : (sysS H X std).Lt (j + 1)), ((sysS H X std).Pj j).IsLatTup La.2 →
        ((sysS H X std).Pj (j + 1)).IsLatTup La'.2 →
        cK * (Formalism.L2.G.Pend.cA (sysS H X std) ℂ_[D.what₂.places.resChar w] j (BOf d.fd2 j La) * sO d ι j La) *
          ι (d.uS S j La) * ι (d.uT S j La') = scT d S ι j La'.1 La'.2 := by
      intro La La' _ _
      have e := GlobalTheory.T.unit_mul_sourceScalar_eq_nextLevelScalar S hPos ι hι d j hj1 La La'
      rw [hsame] at e
      exact e
    have hDel := GlobalTheory.T.kernelSite_contractionIdentity_operatorHalf S hDict hPair hPos hLaw d ι hι (fun j => phi0 (sysS H X std) D (hT.gat_pos u w hg) ι j)
      (fun j c' L' => GlobalTheory.FrameB.tauV ℂ_[D.what₂.places.resChar w] d.fd2 (ltC S.g S.hLT) j (c', L'))
      (fun j c' L' => scT d S ι j c' L') (sO d ι) (gmS d) j hj cK hN hMove hOp hDeg hEq hsc
    have := hDel La hLa x Q hQ c' L' hL'
    exact this
  obtain ⟨V0, hV0, hm0⟩ := hR d0
  have hall : ∀ d : Dec J std, RealAt d (j + 1) hj1 h1 (c', L') φ V0 := by
    intro d
    obtain ⟨V, hV, hm⟩ := hR d
    have : V = V0 := MvPolynomial.map_injective ι ι.injective (hm.trans hm0.symm)
    exact this ▸ hV
  have hrd := GlobalTheory.T.latticeTupleReading_eq_of_realising_polynomial S hDict ι j hj1 h1 (c', L') hL' φ V0 hall
  exact hrd.trans hm0

end GlobalTheory.TwV.DelA
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.PolarizedPairBaseChangePolarizedSameWeight
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.Published

noncomputable section

namespace GlobalTheory.LiftPolar

theorem conj_algebraMap {E M : Type} [Field E] [NumberField E] [IsCMField E] [Field M] [NumberField M] [IsCMField M]
    [Algebra E M] (x : E) :
    IsCMField.complexConj M (algebraMap E M x) = algebraMap E M (IsCMField.complexConj E x) := by
  obtain ⟨j⟩ : Nonempty (M →+* ℂ) := inferInstance
  apply j.injective
  rw [IsCMField.complexEmbedding_complexConj M j]
  exact (IsCMField.complexEmbedding_complexConj E (j.comp (algebraMap E M)) x).symm

theorem cPl_asIdeal {E : Type} [Field E] [NumberField E] [IsCMField E] (w : HeightOneSpectrum (𝓞 E)) :
    (UpperTheory.V.Af.Bc.cPl w).asIdeal =
      w.asIdeal.comap (RingOfIntegers.mapRingEquiv (IsCMField.complexConj E).toRingEquiv : 𝓞 E →+* 𝓞 E) :=
  (GlobalTheory.Mem.Chr.conjPl_iff_comap _ _ _).1 (conjPl_conjSrc _ w)

theorem cPl_under {E M : Type} [Field E] [NumberField E] [IsCMField E] [Field M] [NumberField M] [IsCMField M]
    [Algebra E M] (w : HeightOneSpectrum (𝓞 M)) :
    (UpperTheory.V.Af.Bc.cPl w).under (𝓞 E) = UpperTheory.V.Af.Bc.cPl (w.under (𝓞 E)) := by
  apply HeightOneSpectrum.ext
  rw [cPl_asIdeal]
  change (UpperTheory.V.Af.Bc.cPl w).asIdeal.comap (algebraMap (𝓞 E) (𝓞 M)) = (w.asIdeal.comap (algebraMap (𝓞 E) (𝓞 M))).comap _
  rw [cPl_asIdeal, Ideal.comap_comap, Ideal.comap_comap]
  congr 1
  ext x
  exact conj_algebraMap (x : E)

theorem normV_cPl {E : Type} [Field E] [NumberField E] [IsCMField E] (w : HeightOneSpectrum (𝓞 E)) :
    normV (UpperTheory.V.Af.Bc.cPl w) = normV w := by
  show Nat.card (𝓞 E ⧸ (UpperTheory.V.Af.Bc.cPl w).asIdeal) = Nat.card (𝓞 E ⧸ w.asIdeal)
  refine Nat.card_congr (Ideal.quotientEquiv _ _
    (RingOfIntegers.mapRingEquiv (IsCMField.complexConj E).toRingEquiv) ?_).toEquiv
  rw [cPl_asIdeal]
  exact (Ideal.map_comap_of_surjective
    (RingOfIntegers.mapRingEquiv (IsCMField.complexConj E).toRingEquiv : 𝓞 E →+* 𝓞 E)
    (RingOfIntegers.mapRingEquiv _).surjective w.asIdeal).symm

theorem tendsto_under {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] :
    Filter.Tendsto (fun w : HeightOneSpectrum (𝓞 L) => w.under (𝓞 K)) Filter.cofinite Filter.cofinite := by
  refine Filter.Tendsto.cofinite_of_finite_preimage_singleton fun v => ?_
  have h0 : Ideal.map (algebraMap (𝓞 K) (𝓞 L)) v.asIdeal ≠ 0 :=
    fun h => v.ne_bot ((Ideal.map_eq_bot_iff_of_injective (FaithfulSMul.algebraMap_injective _ _)).1 h)
  refine (Ideal.finite_factors h0).subset fun w hw => ?_
  have e : w.under (𝓞 K) = v := hw
  show w.asIdeal ∣ _
  rw [Ideal.dvd_iff_le, Ideal.map_le_iff_le_comap, ← e]
  exact le_rfl

theorem normV_under {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (w : HeightOneSpectrum (𝓞 L)) : normV w = normV (w.under (𝓞 K)) ^ w.asIdeal.inertiaDeg (𝓞 K) := by
  have : w.asIdeal.LiesOver (w.under (𝓞 K)).asIdeal := ⟨rfl⟩
  have := w.isMaximal
  have := (w.under (𝓞 K)).isMaximal
  show Ideal.absNorm w.asIdeal = Ideal.absNorm (w.under (𝓞 K)).asIdeal ^ w.asIdeal.inertiaDeg (𝓞 K)
  rw [← Ideal.absNorm_relNorm (𝓞 K) (𝓞 L) w.asIdeal,
    Ideal.relNorm_eq_pow_of_isMaximal w.asIdeal (w.under (𝓞 K)).asIdeal, map_pow]

theorem val_of_norm {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L]
    (v : HeightOneSpectrum (𝓞 K)) (w : HeightOneSpectrum (𝓞 L)) (y : (v.adicCompletion K)ˣ) (x : (w.adicCompletion L)ˣ)
    (h : ‖(y : v.adicCompletion K)‖ = ‖(x : w.adicCompletion L)‖) (f : ℕ) (hf : normV w = normV v ^ f) :
    Valued.v (y : v.adicCompletion K) = Valued.v (x : w.adicCompletion L) ^ f := by
  have hf' : Ideal.absNorm w.asIdeal = Ideal.absNorm v.asIdeal ^ f := hf
  have hy : Valued.v (y : v.adicCompletion K) ≠ 0 := (Valuation.ne_zero_iff _).2 y.ne_zero
  have hx : Valued.v (x : w.adicCompletion L) ≠ 0 := (Valuation.ne_zero_iff _).2 x.ne_zero
  rw [FinitePlace.norm_def, FinitePlace.norm_def] at h
  rw [WithZeroMulInt.toNNReal_neg_apply _ hy, WithZeroMulInt.toNNReal_neg_apply _ hx, NNReal.coe_inj, hf',
    Nat.cast_pow, ← zpow_natCast, ← zpow_mul] at h
  have h1 := HeightOneSpectrum.one_lt_absNorm_nnreal v
  have h2 := zpow_right_injective₀ (zero_lt_one.trans h1) h1.ne' h
  rw [← WithZero.coe_unzero hy, ← WithZero.coe_unzero hx, ← WithZero.coe_pow]
  refine congrArg _ (Multiplicative.toAdd.injective ?_)
  rw [h2, toAdd_pow, nsmul_eq_mul]

def normChar {K : Type} (L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] (χ : HChar K) :
    HChar L :=
  ⟨χ.1.comp (GroundTheory.Global.ideleNorm K L), χ.2.1.comp GroundTheory.Global.continuous_ideleNorm, fun k =>
    (congrArg χ.1 (GroundTheory.Global.ideleNorm_diagonal (K := K) k)).trans (χ.2.2 _)⟩

theorem normChar_loc {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (χ : HChar K) (w : HeightOneSpectrum (𝓞 L)) (f : ℕ) (hf : normV w = normV (w.under (𝓞 K)) ^ f)
    (x : (w.adicCompletion L)ˣ) : ∃ y : ((w.under (𝓞 K)).adicCompletion K)ˣ,
      (normChar L χ).loc w x = χ.loc (w.under (𝓞 K)) y ∧
      Valued.v (y : (w.under (𝓞 K)).adicCompletion K) = Valued.v (x : w.adicCompletion L) ^ f := by
  have h := GroundTheory.Global.ideleNorm_finiteEmbedding (K := K) w x
  have hm := GroundTheory.Automorphic.EllipticTorus.ideleModule_ideleNorm (K := K)
    (GroundTheory.Global.IdeleGroup.finiteEmbedding w x)
  rw [h] at hm
  have hm' := congrArg Subtype.val hm
  rw [GroundTheory.Global.IdeleGroup.ideleModule_finiteEmbedding, GroundTheory.Global.IdeleGroup.ideleModule_finiteEmbedding] at hm'
  exact ⟨_, congrArg χ.1 h, val_of_norm _ w _ x hm' f hf⟩

theorem normChar_val {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (χ : HChar K) (w : HeightOneSpectrum (𝓞 L)) (f : ℕ) (hf : normV w = normV (w.under (𝓞 K)) ^ f)
    (hχ : χ.UnrAt (w.under (𝓞 K))) : (normChar L χ).UnrAt w ∧ (normChar L χ).val w = χ.val (w.under (𝓞 K)) ^ f := by
  refine ⟨fun x hx => ?_, ?_⟩
  · obtain ⟨y, hy, hv⟩ := normChar_loc χ w f hf x
    rw [hy]
    apply hχ
    unfold IsUnitAt at *
    rw [hv, hx, one_pow]
  · obtain ⟨y, hy, hv⟩ := normChar_loc χ w f hf (atFin w (unif w))
    have h1 := unif_spec w
    have h2 := unif_spec (w.under (𝓞 K))
    have hu : IsUnitAt (w.under (𝓞 K)) (y * ((atFin _ (unif (w.under (𝓞 K)))) ^ f)⁻¹) := by
      unfold IsUnitAt IsUnifAt at *
      rw [Units.val_mul, Units.val_inv_eq_inv_val, Units.val_pow_eq_pow_val, map_mul, map_inv₀, map_pow, hv, h1, h2]
      exact mul_inv_cancel₀ (pow_ne_zero _ WithZero.exp_ne_zero)
    have h3 := hχ _ hu
    rw [map_mul, map_inv, mul_inv_eq_one, map_pow] at h3
    exact hy.trans h3

theorem infIdele_eq {K : Type} [Field K] [NumberField K] (w : InfinitePlace K) (x : (w.Completion)ˣ) :
    ReciprocityTheory.Neutral.Bridge.HCFR.infIdele K w x = GroundTheory.Global.IdeleGroup.infiniteEmbedding w x := by
  classical
  refine Units.ext (Prod.ext (funext fun u => ?_) rfl)
  change Pi.mulSingle w (x : w.Completion) u = GroundTheory.Global.IdeleGroup.infiniteAdeleSingle w (x : w.Completion) u
  rw [GroundTheory.Global.IdeleGroup.infiniteAdeleSingle_apply]

theorem normChar_locInf {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (χ : HChar K) (u : InfinitePlace L) (hu : u.IsReal) :
    (normChar L χ).locInf u (-1) = χ.locInf (u.comap (algebraMap K L)) (-1) := by
  have hv := hu.comap (algebraMap K L)
  show χ.1 (GroundTheory.Global.ideleNorm K L (ReciprocityTheory.Neutral.Bridge.HCFR.infIdele L u (-1))) =
    χ.1 (ReciprocityTheory.Neutral.Bridge.HCFR.infIdele K (u.comap (algebraMap K L)) (-1))
  rw [infIdele_eq, infIdele_eq, GroundTheory.Global.ideleNorm_infiniteEmbedding]
  congr 2
  apply Units.ext
  apply (InfinitePlace.Completion.extensionEmbeddingOfIsReal hv).injective
  have := GroundTheory.Global.extensionEmbeddingOfIsReal_normUnits (K := K) u hu (-1)
  rw [this]
  simp

theorem normCharGen : ∀ (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] (χ : HChar K) (s : ℂˣ), (∀ v : InfinitePlace K, v.IsReal → χ.locInf v (-1) = s) → ∃ χ' : HChar L, (∀ u : InfinitePlace L, u.IsReal → χ'.locInf u (-1) = s) ∧ ∀ u : HeightOneSpectrum (𝓞 L), χ.UnrAt (u.under (𝓞 K)) → χ'.UnrAt u ∧ ∀ f : ℕ, normV u = normV (u.under (𝓞 K)) ^ f → χ'.val u = χ.val (u.under (𝓞 K)) ^ f := by
  intro K L _ _ _ _ _ χ s hs
  refine ⟨normChar L χ, fun u hu => (normChar_locInf χ u hu).trans (hs _ (hu.comap _)), fun u hu => ?_⟩
  refine ⟨(normChar_val χ u _ (normV_under u) hu).1, fun f hf => (normChar_val χ u f hf hu).2⟩

theorem one_lt_normV {K : Type} [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K)) : 1 < normV v := by
  have h := HeightOneSpectrum.one_lt_absNorm_nnreal v
  show 1 < Ideal.absNorm v.asIdeal
  exact_mod_cast h

theorem algebraMap_mem_real {E M : Type} [Field E] [NumberField E] [IsCMField E] [Field M] [NumberField M] [IsCMField M]
    [Algebra E M] (x : maximalRealSubfield E) : algebraMap E M x ∈ maximalRealSubfield M := by
  refine (IsCMField.complexConj_eq_self_iff M _).1 ?_
  rw [conj_algebraMap, (IsCMField.complexConj_eq_self_iff E _).2 x.2]

def realHom (E M : Type) [Field E] [NumberField E] [IsCMField E] [Field M] [NumberField M] [IsCMField M]
    [Algebra E M] : maximalRealSubfield E →+* maximalRealSubfield M :=
  ((algebraMap E M).comp (maximalRealSubfield E).subtype).codRestrict _ algebraMap_mem_real

theorem charLift : ∀ (E M : Type) [Field E] [NumberField E] [IsCMField E] [Field M] [NumberField M] [IsCMField M] [Algebra E M] (a : ℕ) (χ : HChar (maximalRealSubfield E)), (∀ v : InfinitePlace (maximalRealSubfield E), χ.locInf v (-1) = (-1) ^ a) → ∃ χ' : HChar (maximalRealSubfield M), (∀ u : InfinitePlace (maximalRealSubfield M), χ'.locInf u (-1) = (-1) ^ a) ∧ ∀ᶠ w : HeightOneSpectrum (𝓞 M) in Filter.cofinite, (compNorm M χ').UnrAt w ∧ ∀ f : ℕ, normV w = normV (w.under (𝓞 E)) ^ f → (compNorm M χ').val w = (compNorm E χ).val (w.under (𝓞 E)) ^ f := by
  intro E M _ _ _ _ _ _ _ a χ hsign
  letI : Algebra (maximalRealSubfield E) (maximalRealSubfield M) := (realHom E M).toAlgebra
  obtain ⟨χ', hs, hv⟩ := normCharGen (maximalRealSubfield E) (maximalRealSubfield M) χ ((-1) ^ a) (fun v _ => hsign v)
  refine ⟨χ', fun u => hs u (IsTotallyReal.isReal u), ?_⟩
  have hNV := UpperTheory.ideleNorm_valuation_of_local_compatibility UpperTheory.ideleNorm_local_compatibility
  have hfin : ∀ᶠ w : HeightOneSpectrum (𝓞 M) in Filter.cofinite,
      χ.UnrAt ((w.under (𝓞 E)).under (𝓞 (maximalRealSubfield E))) :=
    (tendsto_under (K := E) (L := M)).eventually ((tendsto_under (K := maximalRealSubfield E) (L := E)).eventually
      (Filter.eventually_cofinite.2 (GlobalTheory.Mem.UnrAe.finite_ramified χ)))
  filter_upwards [hfin] with w hw
  have key : (w.under (𝓞 (maximalRealSubfield M))).under (𝓞 (maximalRealSubfield E)) =
      (w.under (𝓞 E)).under (𝓞 (maximalRealSubfield E)) := by
    apply HeightOneSpectrum.ext
    change (w.asIdeal.comap _).comap _ = (w.asIdeal.comap _).comap _
    rw [Ideal.comap_comap, Ideal.comap_comap]
    congr 1
  obtain ⟨hu1, hu2⟩ := hv (w.under (𝓞 (maximalRealSubfield M))) (by rw [key]; exact hw)
  obtain ⟨hw1, hw2⟩ := hNV M χ' w _ (normV_under w) hu1
  obtain ⟨-, hv2⟩ := hNV E χ (w.under (𝓞 E)) _ (normV_under _) hw
  refine ⟨hw1, fun f hf => ?_⟩
  rw [hw2, hu2 _ (normV_under _), hv2, key, ← pow_mul, ← pow_mul]
  congr 1
  refine Nat.pow_right_injective (one_lt_normV ((w.under (𝓞 E)).under (𝓞 (maximalRealSubfield E)))) ?_
  simp only
  rw [pow_mul, pow_mul, ← key, ← normV_under, ← normV_under, key, ← normV_under, ← hf]

theorem main : AutomorphicFormsFiniteGL → JacquetShalikaRigidity → GelfandKazhdanDual → ∀ (E M : Type) [Field E] [NumberField E] [IsCMField E] [Field M] [NumberField M] [IsCMField M] [Algebra E M] (l a : ℕ), 1 ≤ a → ∀ (π : CuspSub E a) (χ : HChar (maximalRealSubfield E)) (P : CuspSub M a), IsLift π P → InScope .all l π χ → (∃ χ' : HChar (maximalRealSubfield M), InScope .all l P χ') ∧ ∀ wt : ℤ, IsWeight π wt → IsWeight P wt := by
  intro hF hJ hG E M _ _ _ _ _ _ _ l a ha π χ P hL hS
  obtain ⟨hreg, hpol, -⟩ := hS
  refine ⟨?_, fun wt hw τ => ?_⟩
  · obtain ⟨χ', hsign, hev⟩ := charLift E M a χ hpol.sign
    refine ⟨χ', (GlobalTheory.CuspRep.CG.isRegAlg_iff _).2 fun τ => ?_, ⟨hsign, ?_⟩, trivial⟩
    · rw [hL.inf τ]
      exact (GlobalTheory.CuspRep.CG.isRegAlg_iff _).1 hreg _
    refine UpperTheory.polOfSat_of_thetaSat UpperTheory.theta_satake_parameters_inverse hJ hG M a ha P (compNorm M χ') ?_
    have hsd := GlobalTheory.T.polarizedPair_satakeParameter_conjugatePlace hF E a π χ hpol
    have hun := GlobalTheory.CuspRep.UnrSat.eventually_hasSatGL_locRep hF E a π
    filter_upwards [hev, (tendsto_under (K := E) (L := M)).eventually (hsd.and hun)] with w ⟨hu, hval⟩ ⟨hs, B, hB⟩
    have e1 := cPl_under (E := E) w
    have e2 := normV_cPl w
    have e3 := normV_cPl (w.under (𝓞 E))
    have hf := normV_under (K := E) w
    set f := w.asIdeal.inertiaDeg (𝓞 E)
    have hB0 : (CG.mk π).HasSat (w.under (𝓞 E)) B := (CG.hasSat_mk _ _ _).2 hB
    have h1 := hL.sat w f B hf hB0
    have h2 := hL.sat (UpperTheory.V.Af.Bc.cPl w) f _ (by rw [e1, e2, e3]; exact hf) (e1 ▸ hs B hB0)
    refine ⟨hu, _, _, h1, h2, ?_⟩
    rw [hval f hf]
    simp only [Multiset.map_map, Function.comp_def, mul_pow, inv_pow, mul_inv, inv_inv]
  · rw [hL.inf, hL.inf]
    have e : (τ.comp (IsCMField.complexConj M).toRingEquiv.toRingHom).comp (algebraMap E M) =
        (τ.comp (algebraMap E M)).comp (IsCMField.complexConj E).toRingEquiv.toRingHom :=
      RingHom.ext fun x => congrArg τ (conj_algebraMap x)
    rw [e]
    exact hw _

end GlobalTheory.LiftPolar

end
end

