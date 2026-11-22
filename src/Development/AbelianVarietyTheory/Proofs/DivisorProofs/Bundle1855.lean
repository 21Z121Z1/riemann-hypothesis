import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1816
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1833
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.VacuumTranslateConjugateJetBound
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0256
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0266
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsLatticeOfAdelicPoint
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1824
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0164
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1825
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BlockMatrixTwoByTwoFinTranspose
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0887
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0890
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0129
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1826
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1778
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0005
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueIsFunForm
import Formalism.SharpRestriction.Divisibility.PrimeDegreeVariant
import Formalism.PieriBlockIdeals.Bundle0004
import Formalism.MirabolicMackeyTheory.MirabolicMackeyProofs.Bundle0003
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.FormulaAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1116
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Development.AbelianVarietyTheory.Definitions.Foundations.GLintEqKOAndPrincEqKOne
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsDualFamilyOfIsLattice
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorLatticeInertPlaceSelfDual
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1781
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0007

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaussianGrowthConjTorsionTranslatesVacuum
section
namespace GlobalTheory.ConjGrowth

section SlopeTestRemainingChoices

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.ConjJet
open scoped BigOperators

theorem fnConj_sum (D : D7) {N N' n : ℕ} (M : IntermediateField ℚ ℂ) (ρ : M →ₐ[ℚ] ℂ) (c : Fin n → M)
    (F : Fin n → VC D N N' → ℂ) (hF : ∀ i, Differentiable ℂ (F i)) (hM : ∀ i, CoefIn D (F i) M)
    (hd : ∀ i, Differentiable ℂ (fnConj D M ρ (F i))) (h0 : ∀ i, fnConj D M ρ (F i) ≠ 0) :
    fnConj D M ρ (fun z => ∑ i, (c i : ℂ) * F i z) = fun z => ∑ i, ρ (c i) * fnConj D M ρ (F i) z := by
  funext z
  have ht : ∀ α, TaylorLogMetric.taylor D (fun z => ∑ i, (c i : ℂ) * F i z) α =
      ((∑ i, c i * ⟨_, hM i α⟩ : M) : ℂ) := by
    intro α
    rw [GlobalTheory.ConjSeries.taylor_eq_coeff, taylorDir_sum _ _ fun i _ =>
      GlobalTheory.ProdThetaConj.an0 ((hF i).const_mul (c i : ℂ)), map_sum]
    push_cast
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← GlobalTheory.ConjSeries.taylor_eq_coeff, GlobalTheory.ProdThetaConj.taylor_const_mul (hF i)]
  have hcj : ∀ x : M, cj M ρ x = ρ x := fun x => by simp [cj, TaylorLogMetric.liftM]
  have hs : HasSum (fun α => ∑ i, ρ (c i) * (TaylorLogMetric.taylor D (fnConj D M ρ (F i)) α * mono D α z))
      (∑ i, ρ (c i) * fnConj D M ρ (F i) z) :=
    hasSum_sum fun i _ => (GlobalTheory.EntireTaylor.hasSum_taylor_mono D N N' _ (hd i) z).mul_left _
  rw [← hs.tsum_eq]
  refine tsum_congr fun α => ?_
  change cj M ρ _ * _ = _
  rw [ht, hcj, map_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [(GlobalTheory.ConjSeries.taylor_fnConj D N N' M ρ (F i) (hd i) (h0 i)).1 α, map_mul, mul_assoc, ← hcj ⟨_, hM i α⟩]

theorem vBar_vBar (D : D7) {N N' : ℕ} (z : VC D N N') : vBar D (vBar D z) = z := by
  funext τ i j
  simp [vBar]

theorem cBar_cBar (D : D7) {N N' : ℕ} (G : VC D N N' → ℂ) : cBar D (cBar D G) = G := by
  funext z
  simp [cBar, vBar_vBar]

def Facts (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) {a d : ℕ}
    (L : Submodule (𝓞 D.host.E) (Fin a → D.host.E)) (L' : Submodule (𝓞 D.host.E) (Fin d → D.host.E))
    (G : VC D a d → ℂ) (ρ : Qbar →ₐ[ℚ] ℂ) : Prop :=
  0 < area (lamConj Qbar ρ (lamOf D cc δ)) ∧ fnConj D Qbar ρ G ≠ 0 ∧
    (∀ y, LaQ D (tor0 D cc δ) L L' y → ∃ y', fnConj D Qbar ρ (U D (tor0 D cc δ) y G) =
      U D (torConj D (tor0 D cc δ) Qbar ρ) y' (fnConj D Qbar ρ G)) ∧
    ∀ x z, ‖U D (torConj D (tor0 D cc δ) Qbar ρ) x (fnConj D Qbar ρ G) z‖ ^ 2 ≤
      3 * (2 * ((fF D * a * d : ℕ) : ℝ) * D.host.rdE + 1) ^ (fF D * a * d) *
        normSq D (torConj D (tor0 D cc δ) Qbar ρ) (La D (torConj D (tor0 D cc δ) Qbar ρ) L L')
          (fnConj D Qbar ρ G) *
        Real.exp (Real.pi * (∑ τ, ∑ i, ∑ j, ‖z τ i j‖ ^ 2) / area (lamConj Qbar ρ (lamOf D cc δ)))

theorem facts_fix (D : D7) (hI : Inp D) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (t0 : ℂ)
    (hc : Crv D cc δ) (ht : GL3Theta.IsTwoTorsionPointUnkilled D (lamOf D cc δ) t0) (a d : ℕ) (L L')
    (h1 : SD D L) (h2 : SD D L') (hev : Even (a * d)) (G : VC D a d → ℂ)
    (hG : ThetaVectorUpToUnits D (tor0 D cc δ) t0 L L' G) (ρ : Qbar →ₐ[ℚ] ℂ) (hρ : FixK D Qbar ρ) :
    Facts D cc δ L L' G ρ := by
  have hGT := vacuum_mem_thetaSpace_pair D hI cc δ t0 hc ht a d L L' h1 h2 G hG
  obtain ⟨hdata, htors⟩ := (GlobalTheory.CurveAlgebraic.integral_j_and_algebraic_data D hI.g1).2 cc δ hc
  obtain ⟨hA, hAU, -⟩ := hI.alg cc δ hc t0 ht a d L L' h1 h2 hev G hG
  obtain ⟨hTh, -⟩ := hI.conj cc δ hc t0 ht a d L L' h1 h2 hev G hG Qbar ρ hdata hA
  obtain ⟨t', ht'⟩ := (hI.t0Ex cc δ hc).2 Qbar ρ hdata.2.1 hdata.2.2
  obtain ⟨hN, -⟩ := hI.nrm cc δ hc t0 ht a d L L' h1 h2 hev G hG Qbar ρ hdata hA t' ht'
  obtain ⟨cc', δ', hc', -, hΛ⟩ := hI.curve cc δ hc Qbar ρ hρ hdata.2.1 hdata.2.2 1 one_pos
  obtain ⟨π, hπ⟩ := hI.perm Qbar ρ hρ hdata.1
  refine ⟨by rw [hΛ]; exact area_pos D hI.g1 cc' δ' hc', ?_, fun y hy => ?_, fun x z => ?_⟩
  · intro h
    rw [h, hΛ] at hN
    rw [hΛ] at ht'
    refine pow_ne_zero _ (thetaZeroNormSq_ne_zero_cmLattice D hI.g1 cc' δ' t' hc' ht') (hN.symm.trans ?_)
    simp [normSq]
  · obtain ⟨m, hm, hmy⟩ := id hy
    obtain ⟨y', hy', -⟩ := hI.galEx cc δ hc Qbar ρ hρ hdata htors a d L L' h1 h2 y (2 * m) hy
      (by omega)
    have hgal := (hI.gal cc δ hc Qbar ρ hρ hdata a d L L' h1 h2 1 (fun _ => 1) (fun _ => 0) G y y' m
      hGT hm hmy (fun _ => by simp) hy' (by rw [comb_one]; exact hA)
      (by rw [comb_one]; exact hAU y hy)).1
    rw [comb_one] at hgal
    exact ⟨y', hgal⟩
  · have := sup_perm D hI.g1 cc' δ' hc' (torConj D (tor0 D cc δ) Qbar ρ) π hΛ hπ a d L L' h1 h2 _
      hTh x z
    rw [Hf_re, ← mul_div_assoc] at this
    exact this

theorem facts_all (D : D7) (hI : Inp D) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (t0 : ℂ)
    (hc : Crv D cc δ) (ht : GL3Theta.IsTwoTorsionPointUnkilled D (lamOf D cc δ) t0) (a d : ℕ) (L L')
    (h1 : SD D L) (h2 : SD D L') (hev : Even (a * d)) (G : VC D a d → ℂ)
    (hG : ThetaVectorUpToUnits D (tor0 D cc δ) t0 L L' G) (ρ : Qbar →ₐ[ℚ] ℂ) :
    Facts D cc δ L L' G ρ := by
  obtain ⟨hdata, -⟩ := (GlobalTheory.CurveAlgebraic.integral_j_and_algebraic_data D hI.g1).2 cc δ hc
  obtain ⟨hA, -⟩ := hI.alg cc δ hc t0 ht a d L L' h1 h2 hev G hG
  obtain ⟨hfix | hfix, htor, hbar⟩ := hI.bar cc δ hc Qbar ρ hdata
  · exact facts_fix D hI cc δ t0 hc ht a d L L' h1 h2 hev G hG ρ hfix
  obtain ⟨k1, k2, k3, k4⟩ := facts_fix D hI cc δ t0 hc ht a d L L' h1 h2 hev G hG _ hfix
  obtain ⟨hTh, -⟩ := hI.conj cc δ hc t0 ht a d L L' h1 h2 hev G hG Qbar ρ hdata hA
  have hn2 := ((hbar a d L L' (fnConj D Qbar ρ G)).2.2 hTh).2 h1 h2 0
  rw [U_zero] at hn2
  have hL : lamConj Qbar (rhoBar Qbar ρ) (lamOf D cc δ) =
      (lamConj Qbar ρ (lamOf D cc δ)).map (starRingEnd ℂ).toAddMonoidHom :=
    congrArg Tor.abelian₂ htor
  rw [hL, area_conj] at k1 k4
  rw [(hbar a d L L' G).1] at k2 k3 k4
  rw [htor] at k3 k4
  rw [hn2] at k4
  have hU := (hbar a d L L' (fnConj D Qbar ρ G)).2.1
  refine ⟨k1, fun h => k2 ?_, fun y hy => ?_, fun x z => ?_⟩
  · rw [h]
    funext z
    simp [cBar]
  · obtain ⟨y', hy'⟩ := k3 y hy
    refine ⟨vBar D y', ?_⟩
    rw [(hbar a d L L' _).1, ← vBar_vBar D y', ← hU] at hy'
    have := congrArg (cBar D) hy'
    rwa [cBar_cBar, cBar_cBar] at this
  · have := k4 (vBar D x) (vBar D z)
    rw [← hU] at this
    simpa only [cBar, vBar_vBar, vBar, RCLike.norm_conj, Complex.conj_conj] using this

end SlopeTestRemainingChoices

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim GlobalTheory.TestLat
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.SumSize GlobalTheory.KerConjMean

theorem conj_growth : ∀ (D : D7), GlobalTheory.NormSum.Inp D → ∀ (cc : Ideal (𝓞 D.host.K)) (δ t0 : ℂ), Crv D cc δ → GL3Theta.IsTwoTorsionPointUnkilled D (lamOf D cc δ) t0 →
  ∀ (a b : ℕ) (e0 : VC D a b → ℂ), Even (a * b) → oddE0 D cc δ t0 a b e0 →
  ∀ (Ls : Submodule (𝓞 D.host.E) (Fin a → D.host.E)) (Lt : Submodule (𝓞 D.host.E) (Fin b → D.host.E)), SD D Ls → SD D Lt →
  ∀ (κ : ℂ), Mod1All κ → ∀ (k n : ℕ) (r : Fin n → Qbar) (s : Fin n → VC D a b), 0 < k →
  (∀ i, k • s i ∈ La D (tor0 D cc δ) Ls Lt) → (∀ ρ₁ : Qbar →+* ℂ, ∑ i, ‖ρ₁ (r i)‖ ≤ 1) →
  ∀ (ρ : Qbar →ₐ[ℚ] ℂ) (t' : ℂ), GL3Theta.IsTwoTorsionPointUnkilled D (lamConj Qbar ρ (lamOf D cc δ)) t' →
    0 < area (lamConj Qbar ρ (lamOf D cc δ)) ∧
    CoefIn D (fun z => κ * ∑ i, (r i : ℂ) * U D (tor0 D cc δ) (s i)
      (Iop D (tor0 D cc δ) (La0 D (tor0 D cc δ) a b) (La D (tor0 D cc δ) Ls Lt) e0) z) Qbar ∧
    Differentiable ℂ (fnConj D Qbar ρ fun z => κ * ∑ i, (r i : ℂ) * U D (tor0 D cc δ) (s i)
      (Iop D (tor0 D cc δ) (La0 D (tor0 D cc δ) a b) (La D (tor0 D cc δ) Ls Lt) e0) z) ∧
    ∀ z, ‖fnConj D Qbar ρ (fun z => κ * ∑ i, (r i : ℂ) * U D (tor0 D cc δ) (s i)
      (Iop D (tor0 D cc δ) (La0 D (tor0 D cc δ) a b) (La D (tor0 D cc δ) Ls Lt) e0) z) z‖ ^ 2 ≤
      3 * (2 * ((fF D * a * b : ℕ) : ℝ) * D.host.rdE + 1) ^ (fF D * a * b) *
        nrm1Sq (lamConj Qbar ρ (lamOf D cc δ)) (GL3Theta.th0 (lamConj Qbar ρ (lamOf D cc δ)) t') ^ (fF D * a * b) *
        Real.exp (Real.pi * (∑ τ, ∑ i, ∑ j, ‖z τ i j‖ ^ 2) / area (lamConj Qbar ρ (lamOf D cc δ))) := by
  intro D hI cc δ t0 hc ht a b e0 hev he Ls Lt h1 h2 κ hκ k n r s hk hs hr ρ t' ht'
  have hsd : ∀ N, SD D (stdL D N) := fun N => by
    obtain ⟨Lt, h, h1, -⟩ := GlobalTheory.NormSum.exists_lattice_of_adelic_point D N
    exact h1 ▸ (h 1).2
  have hG := GlobalTheory.VacuumMove.isVacuum_thetaIntertwiner_selfDual D hI cc δ t0 hc ht a b _ _ Ls Lt (hsd a) (hsd b) h1 h2 e0 he.2.2.2.1
  change ThetaVectorUpToUnits D (tor0 D cc δ) t0 Ls Lt
    (Iop D (tor0 D cc δ) (La0 D (tor0 D cc δ) a b) (La D (tor0 D cc δ) Ls Lt) e0) at hG
  generalize Iop D (tor0 D cc δ) (La0 D (tor0 D cc δ) a b) (La D (tor0 D cc δ) Ls Lt) e0 = G at hG ⊢
  have hGT := GlobalTheory.ConjJet.vacuum_mem_thetaSpace_pair D hI cc δ t0 hc ht a b Ls Lt h1 h2 G hG
  obtain ⟨hdata, -⟩ := (GlobalTheory.CurveAlgebraic.integral_j_and_algebraic_data D hI.g1).2 cc δ hc
  obtain ⟨hA, hAU, hAC, -⟩ := hI.alg cc δ hc t0 ht a b Ls Lt h1 h2 hev G hG
  obtain ⟨hTh, -⟩ := hI.conj cc δ hc t0 ht a b Ls Lt h1 h2 hev G hG Qbar ρ hdata hA
  obtain ⟨hN, -⟩ := hI.nrm cc δ hc t0 ht a b Ls Lt h1 h2 hev G hG Qbar ρ hdata hA t' ht'
  obtain ⟨k1, k2, k3, k4⟩ := facts_all D hI cc δ t0 hc ht a b Ls Lt h1 h2 hev G hG ρ
  rw [hN] at k4
  obtain ⟨hκ1, hκ2⟩ := hκ
  have hq : ∀ i, LaQ D (tor0 D cc δ) Ls Lt (s i) := fun i => ⟨k, hk, hs i⟩
  choose y hy using fun i => k3 (s i) (hq i)
  have he' : (fun z => κ * ∑ i, (r i : ℂ) * U D (tor0 D cc δ) (s i) G z) =
      fun z => ∑ i, ((⟨κ, hκ1⟩ * r i : Qbar) : ℂ) * U D (tor0 D cc δ) (s i) G z := by
    funext z
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← mul_assoc]
    rfl
  have hd : ∀ i, Differentiable ℂ (fnConj D Qbar ρ (U D (tor0 D cc δ) (s i) G)) := fun i => by
    rw [hy]; exact GlobalTheory.ConjJet.U_diff D _ _ _ hTh.1
  rw [he', fnConj_sum D Qbar ρ _ _ (fun i => GlobalTheory.ConjJet.U_diff D _ _ _ hGT.1) (fun i => hAU _ (hq i)) hd
    (fun i => by rw [hy]; exact GlobalTheory.ConjJet.U_ne_zero D _ _ _ k2)]
  refine ⟨k1, hAC n _ s (fun i => (⟨κ, hκ1⟩ * r i : Qbar).2) hq,
    Differentiable.fun_sum fun i _ => (hd i).const_mul _, fun z => ?_⟩
  have hb := fun i => k4 (y i) z
  have h0 := (sq_nonneg _).trans (k4 0 z)
  generalize (3 * (2 * ((fF D * a * b : ℕ) : ℝ) * D.host.rdE + 1) ^ (fF D * a * b) * _ * _ : ℝ) = B at hb h0 ⊢
  have hb' : ∀ i, ‖fnConj D Qbar ρ (U D (tor0 D cc δ) (s i) G) z‖ ≤ √B := fun i => by
    rw [hy]; exact Real.le_sqrt_of_sq_le (hb i)
  rw [← Real.le_sqrt (norm_nonneg _) h0]
  calc _ ≤ ∑ i, ‖ρ (r i)‖ * √B := by
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
        have h3 : ‖ρ ⟨κ, hκ1⟩‖ = 1 := hκ2 ρ.toRingHom
        rw [norm_mul, map_mul, norm_mul, h3, one_mul]
        exact mul_le_mul_of_nonneg_left (hb' i) (norm_nonneg _)
    _ ≤ 1 * √B := by
        rw [← Finset.sum_mul]
        exact mul_le_mul_of_nonneg_right (hr ρ.toRingHom) (Real.sqrt_nonneg _)
    _ = √B := one_mul _

end GlobalTheory.ConjGrowth
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GridLocalTensorPlacesSplitIdempotentSum
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.VacAny
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames GlobalTheory.BigNZ GlobalTheory.AdelicU GlobalTheory.WeilM
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ Num IsTripleOf IsDatumA skewGram mulG colV adjV₁)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chars Rep IsTriple Acts SInf At latAtV realAd evI)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.BigDat

namespace GlobalTheory.IdemAtPl

theorem eq_atPl_of_isIdemAt {D : D7} {e : AE D} {P : Pl D.host.E} (h : Formalism.L2.NTheta.IsIdemAt e P) : e = atPl P 1 := by
  classical
  refine ae_ext ?_ fun Q => ?_
  · rw [GlobalTheory.SplitScalar.infPart_splitIdem h.1, (atPl_spec P 1).1]
  · rw [(atPl_spec P 1).2]
    by_cases hQ : Q = P
    · subst hQ
      rw [(cpt_of_isIdemAt h).1, Pi.single_eq_same]
    · rw [(cpt_of_isIdemAt h).2 Q hQ, Pi.single_eq_of_ne hQ]

theorem eq_liftV_of_isPlaceIdem {D : D7} {v : HeightOneSpectrum (𝓞 D.host.F)} {ε : AF D.host.F}
    (h : IsPlaceIdem D v ε) : ε = GlobalTheory.LatVac.liftV v 1 := by
  obtain ⟨α, rfl, h1, h0⟩ := h
  have hα : α = GlobalTheory.AdelicU.singleFin v 1 := GlobalTheory.AdelicU.af_ext fun u => by
    by_cases hu : u = v
    · subst hu
      rw [h1, GlobalTheory.AdelicU.evalV_singleFin_self]
    · rw [h0 u hu, GlobalTheory.AdelicU.evalV_singleFin_ne hu]
  subst hα
  rfl

theorem main : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {μ₀ : T}, L.Is μ₀ → ∀ t : T,
    (∀ w ∈ locPl G t, IsSplitIdem D (atPl w 1) ∧ atPl w 1 + cA D (atPl w 1) =
      algebraMap (AF D.host.F) (AE D) (GlobalTheory.LatVac.liftV (w.under (𝓞 D.host.F)) 1)) ∧
    ∀ ε, IsIdemSum ε (locPl G t) → ε = ∑ w ∈ locPl G t, atPl w 1 ∧ ∀ w ∈ locPl G t, ε * atPl w 1 = atPl w 1 := by
  intro D T L sc G μ₀ hL t
  classical
  obtain ⟨_, ⟨es, hes, -⟩, -⟩ := GlobalTheory.FunObj.LocTensor.exists_idemSum_locPl hL G t
  refine ⟨fun w hw => ?_, fun ε hε => ?_⟩
  · have h := hes w hw
    rw [← eq_atPl_of_isIdemAt h]
    obtain ⟨v, ε, hε, he⟩ := h.1.2.2
    refine ⟨h.1, ?_⟩
    rw [he, eq_liftV_of_isPlaceIdem hε, GlobalTheory.IdemUnder.under_eq_of_isIdemAt D _ w v ε h hε he]
  · obtain ⟨⟨fs, hfs, rfl⟩, -⟩ := hε
    have hf : ∀ PP ∈ locPl G t, fs PP = atPl PP 1 := fun PP hPP => eq_atPl_of_isIdemAt (hfs PP hPP)
    refine ⟨Finset.sum_congr rfl hf, fun w hw => ?_⟩
    rw [Finset.sum_congr rfl hf]
    refine ae_ext ?_ fun Q => ?_
    · rw [map_mul, (atPl_spec w 1).1, mul_zero]
    · rw [map_mul, map_mul, (atPl_spec w 1).2, map_sum, map_sum]
      by_cases hQ : Q = w
      · subst hQ
        rw [Pi.single_eq_same, mul_one, Finset.sum_eq_single Q (fun b _ hb => by
          rw [(atPl_spec b 1).2, Pi.single_eq_of_ne (Ne.symm hb)]) (fun h => absurd hw h),
          (atPl_spec Q 1).2, Pi.single_eq_same]
      · rw [Pi.single_eq_of_ne hQ, mul_zero]

end GlobalTheory.IdemAtPl
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HaarAverageFundamentalDomainDescentStatement
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Doubling GlobalTheory.MixModel GlobalTheory.SWLit
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (UA incM ratU)
open GlobalTheory.WeilM (Darboux symp schA thetaSum UG)
open GlobalTheory.SiegelFormula (coord)
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SWLink

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.haar_average_fundamental_domain_descent : ∀ (D : D7) (V : HSp D) (ι : UD D (-V.gram) ≃ₜ* GA D V), (∀ h, h ∈ ratU D.sp.cm.sig (-V.gram) ↔ ι h ∈ GQ V) → ∀ ν : Measure (GA D V), ν.IsHaarMeasure → ∃ (ν' : Measure (UD D (-V.gram))) (𝓕 : Set (UD D (-V.gram))), ν'.IsHaarMeasure ∧ IsFundamentalDomain (ratU D.sp.cm.sig (-V.gram)) 𝓕 ν' ∧ ∀ f : GA D V → ℂ, LeftInv (GQ V) f → ⨍ h in 𝓕, f (ι h) ∂ν' = ⨍ q, descend (GQ V) f q ∂autMeasure V ν := by
  first | exact @GlobalTheory.SWLink.exists_fundDom_mean | exact GlobalTheory.SWLink.exists_fundDom_mean | (intros; apply GlobalTheory.SWLink.exists_fundDom_mean <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasDerivAtThetaTransformHeisenbergRealLine
section
noncomputable section

namespace GlobalTheory.ThetaLineDeriv

section SlopeTestRemainingChoices

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.SWQ GlobalTheory.WeilM
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (realAd)
open scoped Matrix Classical

variable {F : Type} [Field F] [NumberField F]

theorem comp_mem_schA {κ κ' : Type} [Fintype κ] [Fintype κ'] (σ : κ ≃ κ')
    {Φ : (κ → AF F) → ℂ} (hΦ : Φ ∈ schA F κ) : (fun x : κ' → AF F => Φ (x ∘ σ)) ∈ schA F κ' := by
  induction hΦ using Submodule.span_induction with
  | mem Φ h =>
    obtain ⟨f, g, hg, rfl⟩ := h
    let A : (κ' → mixedEmbedding.mixedSpace F) ≃L[ℝ] (κ → mixedEmbedding.mixedSpace F) :=
      (LinearEquiv.funCongrLeft ℝ (mixedEmbedding.mixedSpace F) σ).toContinuousLinearEquiv
    let B : (κ' → Af F) ≃ₜ (κ → Af F) := (Homeomorph.piCongrLeft (Y := fun _ => Af F) σ).symm
    refine Submodule.subset_span ⟨SchwartzMap.compCLMOfContinuousLinearEquiv ℂ A f, g ∘ B,
      ⟨hg.1.comp_continuous B.continuous, hg.2.comp_homeomorph B⟩, ?_⟩
    rfl
  | zero => exact Submodule.zero_mem _
  | add Φ Ψ _ _ h1 h2 => exact Submodule.add_mem _ h1 h2
  | smul c Φ _ h => exact Submodule.smul_mem _ c h

theorem decay_majorant {N : ℕ} (hF : IsTotallyReal F)
    {Φ : (Fin N → AF F) → ℂ} (hΦ : Decay Φ) (ω : Set (Fin N → AF F)) (hω : IsCompact ω) :
    ∃ c : (Fin N → F) → ℝ, Summable c ∧ ∀ ξ, ∀ y ∈ ω, ‖Φ (rat ξ + y)‖ ≤ c ξ := by
  obtain ⟨-, ⟨K, hK, hKz⟩, hdec⟩ := hΦ
  obtain ⟨k, hk⟩ := GlobalTheory.SumMaj.summable_majorant F N hF K hK
  obtain ⟨C, hC⟩ := hdec k
  have hC0 : 0 ≤ C :=
    le_trans (mul_nonneg (norm_nonneg _) (pow_nonneg (by linarith [GlobalTheory.SumMaj.sz_nonneg (0 : Fin N → AF F)]) k))
      (hC 0)
  obtain ⟨c, hcs, hc0, hcb⟩ := hk ω hω
  refine ⟨fun ξ => C * c ξ, hcs.mul_left C, fun ξ y hy => ?_⟩
  by_cases hmem : fin (rat ξ + y) ∈ K
  · have h1 := hcb ξ y hy hmem
    have h2 := hC (rat ξ + y)
    calc ‖Φ (rat ξ + y)‖ = ‖Φ (rat ξ + y)‖ * 1 := (mul_one _).symm
      _ ≤ ‖Φ (rat ξ + y)‖ * (c ξ * (1 + sz (rat ξ + y)) ^ k) :=
        mul_le_mul_of_nonneg_left h1 (norm_nonneg _)
      _ = c ξ * (‖Φ (rat ξ + y)‖ * (1 + sz (rat ξ + y)) ^ k) := by ring
      _ ≤ c ξ * C := mul_le_mul_of_nonneg_left h2 (hc0 ξ)
      _ = C * c ξ := mul_comm _ _
  · rw [hKz _ hmem, norm_zero]
    exact mul_nonneg hC0 (hc0 ξ)

theorem schA_majorant {κ : Type} [Fintype κ] (hF : IsTotallyReal F)
    {Φ : (κ → AF F) → ℂ} (hΦ : Φ ∈ schA F κ) (ω : Set (κ → AF F)) (hω : IsCompact ω) :
    ∃ c : (κ → F) → ℝ, Summable c ∧
      ∀ ξ : κ → F, ∀ y ∈ ω, ‖Φ ((fun i => algebraMap F (AF F) (ξ i)) + y)‖ ≤ c ξ := by
  let σ := Fintype.equivFin κ
  have hc : Continuous fun y : κ → AF F => y ∘ σ.symm := continuous_pi fun i => continuous_apply _
  obtain ⟨c, hcs, hcb⟩ := decay_majorant hF
    (GlobalTheory.SchwartzDecay.decay_of_mem_schA F _ _ (comp_mem_schA σ hΦ)) _ (hω.image hc)
  refine ⟨fun ξ => c (ξ ∘ σ.symm), (Equiv.arrowCongr σ (Equiv.refl F)).summable_iff.2 hcs, fun ξ y hy => ?_⟩
  have h := hcb (ξ ∘ σ.symm) _ ⟨y, hy, rfl⟩
  have e : (rat (ξ ∘ σ.symm) + y ∘ σ.symm) ∘ σ = (fun i => algebraMap F (AF F) (ξ i)) + y := by
    funext i
    simp [rat]
  rwa [e] at h

theorem continuous_ofMixed : Continuous (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm := by
  refine continuous_pi fun v => ?_
  rcases v.isReal_or_isComplex with hv | hv
  · rw [(InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal hv).isEmbedding.continuous_iff]
    exact ((continuous_apply _).comp continuous_fst).congr fun y =>
      (congrFun (congrArg Prod.fst ((InfiniteAdeleRing.ringEquiv_mixedSpace F).apply_symm_apply y)) ⟨v, hv⟩).symm
  · rw [(InfinitePlace.Completion.isometry_extensionEmbedding v).isEmbedding.continuous_iff]
    exact ((continuous_apply _).comp continuous_snd).congr fun y =>
      (congrFun (congrArg Prod.snd ((InfiniteAdeleRing.ringEquiv_mixedSpace F).apply_symm_apply y)) ⟨v, hv⟩).symm

theorem continuous_realAd : Continuous (realAd F) :=
  Continuous.prodMk (continuous_ofMixed.comp (continuous_algebraMap ℝ _)) continuous_const

theorem realAd_add (s t : ℝ) : realAd F (s + t) = realAd F s + realAd F t := by
  simp only [realAd, map_add]
  rfl

theorem realAd_zero : realAd F 0 = 0 := by
  simp only [realAd, map_zero]
  rfl

theorem schr_smul_add {R : Type} [CommRing R] [Invertible (2 : R)] (ψ : AddChar R ℂ) {κ : Type} [Fintype κ]
    (v : (κ → R) × (κ → R)) (a b : R) (Φ : (κ → R) → ℂ) (z : κ → R) :
    schr ψ ((a + b) • v) Φ z = schr ψ (a • v) (schr ψ (b • v) Φ) z := by
  simp only [schr, Prod.smul_fst, Prod.smul_snd, ← mul_assoc, ← AddChar.map_add_eq_mul, add_smul, add_assoc]
  congr 2
  simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, add_dotProduct, dotProduct_add, smul_dotProduct, dotProduct_smul, smul_eq_mul]
  first
    | linear_combination (a * b * (v.1 ⬝ᵥ v.2)) * invOf_mul_self (2 : R)
    | linear_combination (-(a * b * (v.1 ⬝ᵥ v.2))) * invOf_mul_self (2 : R)

variable [Invertible (2 : AF F)] {κ : Type} [Fintype κ]

theorem hasDerivAt_schr (ψ : AddChar (AF F) ℂ) (v : (κ → AF F) × (κ → AF F))
    {Φ Φ' : (κ → AF F) → ℂ} (hd : ∀ z, HasDerivAt (fun s : ℝ => schr ψ (realAd F s • v) Φ z) (Φ' z) 0)
    (z : κ → AF F) (t : ℝ) :
    HasDerivAt (fun s : ℝ => schr ψ (realAd F s • v) Φ z) (schr ψ (realAd F t • v) Φ' z) t := by
  have h1 : HasDerivAt (fun h : ℝ => schr ψ (realAd F (t + h) • v) Φ z) (schr ψ (realAd F t • v) Φ' z) (t - t) := by
    have e : (fun h : ℝ => schr ψ (realAd F (t + h) • v) Φ z) = fun h =>
        ψ (z ⬝ᵥ (realAd F t • v).2 + ⅟(2 : AF F) * ((realAd F t • v).1 ⬝ᵥ (realAd F t • v).2)) *
          schr ψ (realAd F h • v) Φ (z + (realAd F t • v).1) := by
      funext h
      rw [realAd_add, schr_smul_add]
      rfl
    rw [e, sub_self]
    exact (hd _).const_mul _
  have h2 := h1.comp_sub_const t t
  simpa only [add_sub_cancel] using h2

theorem hasDerivAt_thetaSum_schr (ψ : AddChar (AF F) ℂ) (hF : IsTotallyReal F) (hψ : IsCharAF F ψ)
    (v : (κ → AF F) × (κ → AF F)) {Φ Φ' : (κ → AF F) → ℂ} (hΦ : Φ ∈ schA F κ) (hΦ' : Φ' ∈ schA F κ)
    (hd : ∀ z, HasDerivAt (fun s : ℝ => schr ψ (realAd F s • v) Φ z) (Φ' z) 0) (w : (κ → AF F) × (κ → AF F)) :
    HasDerivAt (fun t : ℝ => thetaSum F (schr ψ w (schr ψ (realAd F t • v) Φ))) (thetaSum F (schr ψ w Φ')) 0 := by
  have hnorm : ∀ x, ‖ψ x‖ = 1 := hψ.2.1
  have hM0 : realAd F 0 • v = 0 := by rw [realAd_zero, zero_smul]
  set ω : Set (κ → AF F) := (fun s : ℝ => w.1 + (realAd F s • v).1) '' Set.Icc (-1) 1 with hω
  have hωc : IsCompact ω := isCompact_Icc.image
    (continuous_const.add (continuous_pi fun i => continuous_realAd.mul (continuous_const (y := v.1 i))))
  obtain ⟨c, hcs, hcb⟩ := schA_majorant hF hΦ' ω hωc
  obtain ⟨c₀, hcs₀, hcb₀⟩ := schA_majorant hF hΦ {w.1} isCompact_singleton
  set r : (κ → F) → (κ → AF F) := fun ξ i => algebraMap F (AF F) (ξ i) with hr
  set ph : (κ → F) → ℂ := fun ξ => ψ (r ξ ⬝ᵥ w.2 + ⅟(2 : AF F) * (w.1 ⬝ᵥ w.2)) with hph
  have e : (fun t : ℝ => thetaSum F (schr ψ w (schr ψ (realAd F t • v) Φ))) =
      fun t => ∑' ξ : κ → F, ph ξ * schr ψ (realAd F t • v) Φ (r ξ + w.1) := rfl
  have h0 : ∀ Ψ : (κ → AF F) → ℂ, schr ψ (realAd F 0 • v) Ψ = Ψ := fun Ψ => by
    rw [hM0]
    funext z
    simp [schr]
  have hv : thetaSum F (schr ψ w Φ') = ∑' ξ : κ → F, ph ξ * schr ψ (realAd F 0 • v) Φ' (r ξ + w.1) := by
    rw [h0]
    rfl
  rw [e, hv]
  have hmem : (0 : ℝ) ∈ Set.Ioo (-1 : ℝ) 1 := ⟨by norm_num, by norm_num⟩
  refine hasDerivAt_tsum_of_isPreconnected hcs isOpen_Ioo isPreconnected_Ioo
    (fun ξ t _ => (hasDerivAt_schr ψ v hd (r ξ + w.1) t).const_mul (ph ξ)) (fun ξ t ht => ?_) hmem ?_ hmem
  · have hy : w.1 + (realAd F t • v).1 ∈ ω := ⟨t, ⟨ht.1.le, ht.2.le⟩, rfl⟩
    have := hcb ξ _ hy
    simp only [ph, schr, norm_mul, hnorm, one_mul, add_assoc]
    exact this
  · refine Summable.of_norm_bounded hcs₀ fun ξ => ?_
    have := hcb₀ ξ w.1 rfl
    simp only [h0, ph, norm_mul, hnorm, one_mul]
    exact this

end SlopeTestRemainingChoices

end GlobalTheory.ThetaLineDeriv

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.VacAny
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames GlobalTheory.BigNZ GlobalTheory.AdelicU GlobalTheory.WeilM
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ Num IsTripleOf IsDatumA skewGram mulG colV adjV₁)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chars Rep IsTriple Acts SInf At latAtV realAd evI)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.BigDat

theorem GlobalTheory.ThetaLineDeriv.hasDerivAt_thetaSum_rho : ∀ {F : Type} [Field F] [NumberField F] {U : Type} [AddCommGroup U] [Module (AF F) U] {B : U → U → AF F} {κ : Type} [Fintype κ]
    (co : Darboux B κ) (ψ : AddChar (AF F) ℂ), IsTotallyReal F → IsCharAF F ψ → ∀ (u : U), ∀ Φ ∈ schA F κ, ∀ Φ' ∈ schA F κ,
    (∀ x, HasDerivAt (fun t : ℝ => co.rho ψ (realAd F t • u) Φ x) (Φ' x) 0) →
    ∀ w : U, HasDerivAt (fun t : ℝ => thetaSum F (co.rho ψ w (co.rho ψ (realAd F t • u) Φ))) (thetaSum F (co.rho ψ w Φ')) 0 := by
  intro F _ _ U _ _ B κ _ co ψ hF hψ u Φ hΦ Φ' hΦ' hd w
  simp only [Darboux.rho, map_smul] at hd ⊢
  exact GlobalTheory.ThetaLineDeriv.hasDerivAt_thetaSum_schr ψ hF hψ (co.e u) hΦ hΦ' hd (co.e w)

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianFockNormAdjugateSubstSymmLeStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim GlobalTheory.TestLat GlobalTheory.SumSize
open Formalism.DivisionValues (vw lw)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermitianFockNorm_adjugateSubst_symm_le : ∀ {ι : Type} [Fintype ι] {n : ℕ} (σ : ι → DomWeight n) (w : VV ℂ fun τ => (σ τ).dual),
    (pairK σ (fun _ => (1 : Matrix (Fin n) (Fin n) ℂ)) ((GlobalTheory.FunObj.funEquiv σ).symm w) ((GlobalTheory.FunObj.funEquiv σ).symm w)).re ≤
      (pairK (fun τ => (σ τ).dual) (fun _ => (1 : Matrix (Fin n) (Fin n) ℂ)) w w).re := by
  first | exact @GlobalTheory.FunIsom.pairK_funEquiv_symm_le | exact GlobalTheory.FunIsom.pairK_funEquiv_symm_le | (intros; apply GlobalTheory.FunIsom.pairK_funEquiv_symm_le <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdealMapSmulIsLatticeOfNeBotStatement
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.KSplit
open scoped Matrix TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ideal_map_smul_isLattice_of_ne_bot : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (n : ℕ) (L : Submodule (𝓞 E) (Fin n → E)) (I : Ideal (𝓞 F)), I ≠ ⊥ → Submodule.IsLattice E L → Submodule.IsLattice E (I.map (algebraMap (𝓞 F) (𝓞 E)) • L) := by
  first | exact @GlobalTheory.ideal_map_smul_isLattice | exact GlobalTheory.ideal_map_smul_isLattice | (intros; apply GlobalTheory.ideal_map_smul_isLattice <;> assumption)
end

