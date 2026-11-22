import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.FinitePrimesUnder
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.VacuumUnderAdelicPairModulusOne
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaSpanRationalTranslatesVacuum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1679
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1771
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsMovesOfSelfDual
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1776
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0028
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0015
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0025
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0008
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0014
import Formalism.LocalToGlobal.KernelLattices.TopPin
import Formalism.LocalToGlobal.KernelLattices.Bundle0001
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1681
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1736
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1747
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1705
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1749
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WordActionSquareIntegrableBound
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1465

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.VlLeOfMemHatId
section
open Formalism.BasicNotions Formalism.IndefR.Links IsDedekindDomain NumberField Polynomial
open scoped Pointwise nonZeroDivisors
open Formalism.L2.Host (HChar embTau)
open GlobalTheory.ChiGrid GlobalTheory.LeafRestExamples
open Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.FunObj GlobalTheory.FunObj.SqNum

noncomputable section

namespace GlobalTheory.NuTrivSq
variable {D : D7}
open GlobalTheory.Mem.Col2.SplitChar in

theorem vl_le_of_mem_hatId' {I : Ideal (𝓞 D.host.E)} {PP : HeightOneSpectrum (𝓞 D.host.E)} {n : ℕ}
    (hI : I ≤ PP.asIdeal ^ n) {x : AE D} (hx : x ∈ hatId D I) : vl D PP x ≤ WithZero.exp (-(n : ℤ)) := by
  induction hx using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨b, hb, s, hs, rfl⟩ := hy
    rw [map_mul, vl_inc]
    refine (mul_le_of_le_one_right' (vl_le hs PP)).trans ?_
    rw [HeightOneSpectrum.valuation_of_algebraMap]
    exact (HeightOneSpectrum.intValuation_le_pow_iff_mem PP b n).2 (hI hb)
  | zero => simp
  | add a b _ _ ha hb => exact (Valuation.map_add _ _ _).trans (max_le ha hb)
  | neg a _ ha => rwa [Valuation.map_neg]

open GlobalTheory.Mem.Col2.SplitChar in

theorem sgA_mem_hatId' {I : Ideal (𝓞 D.host.E)} {x : AE D} (hx : x ∈ hatId D I) :
    sgA D x ∈ hatId D (D.host.conj • I) := by
  induction hx using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨b, hb, s, hs, rfl⟩ := hy
    refine AddSubgroup.subset_closure ⟨D.host.conj • b, Ideal.smul_mem_pointwise_smul _ _ _ hb, sgA D s,
      GlobalTheory.NormSum.UnramHecke.sgA_mem D hs, ?_⟩
    rw [map_mul, GlobalTheory.Mem.Col2.SplitChar.sgA_inc]
    rfl
  | zero => simp
  | add a b _ _ ha hb => rw [map_add]; exact add_mem ha hb
  | neg a _ ha => rw [map_neg]; exact neg_mem ha

theorem conj_conj_smul (𝔪 : Ideal (𝓞 D.host.E)) : D.host.conj • D.host.conj • 𝔪 = 𝔪 := by
  have h : D.host.conj * D.host.conj = 1 := AlgEquiv.ext fun z => GlobalTheory.NormSum.UnramHecke.conj_conj D z
  rw [smul_smul, h, one_smul]

open GlobalTheory.Mem.Col2.SplitChar in

theorem vl_sub_le' {T : Type} {L : LevCh D T} (P : Places L) {y : AE D}
    (h1 : y ∈ hatId D (condE P)) (h2 : y ∈ hatId D (D.host.conj • condE P))
    {PP : HeightOneSpectrum (𝓞 D.host.E)} (hv : PP.under (𝓞 D.host.F) ∈ P.S0) :
    vl D PP y ≤ WithZero.exp (-(condExp P (PP.under (𝓞 D.host.F)) : ℤ)) := by
  obtain ⟨c, hc, hcm, -⟩ := GlobalTheory.Mem.HostCM.host_cm D.R D.host
  set v := PP.under (𝓞 D.host.F) with hvdef
  have hw : (P.w v).under (𝓞 D.host.F) = v := P.under_w hv
  have hle : condE P ≤ (P.w v).asIdeal ^ condExp P v := Ideal.le_of_dvd (Finset.dvd_prod_of_mem _ hv)
  rcases (GlobalTheory.Mem.Chr.under_eq_iff_conjPl c hcm.rank hcm.ne (P.w v) PP).1 (by rw [hw]) with e | h
  · rw [e]
    exact vl_le_of_mem_hatId' (e ▸ hle) h1
  · have e : c.toRingEquiv = D.host.conj.toRingEquiv := RingEquiv.ext hc
    rw [e] at h
    rw [← GlobalTheory.NormSum.UnramHecke.sgA_sgA D y, vl_sgA h]
    have h3 := sgA_mem_hatId' h2
    rw [conj_conj_smul] at h3
    exact vl_le_of_mem_hatId' hle h3

end GlobalTheory.NuTrivSq

open GlobalTheory.Mem.Col2.SplitChar Formalism.L2.Host GlobalTheory.NuTrivSq in

theorem GlobalTheory.NuTrivSq.nuH_finIdl_eq_one : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc) (i j : Fin D.R.m) {μ₀ : T},
    L.Is μ₀ → ∀ x : (AE D)ˣ, IntU D x → (x : AE D) - 1 ∈ hatId D (condE G.pl) →
      (x : AE D) - 1 ∈ hatId D (D.host.conj • condE G.pl) →
      (nuH G μ₀ i j).1 (GlobalTheory.Mem.Col2.SplitChar.finIdl D x) = 1 := by
  intro D T L sc G i j μ₀ hL u hu hc1 hc2
  refine GlobalTheory.Mem.LocTriv.eq_one_of_local D.host.E _ (nuH G μ₀ i j).2.1 (finIdl D u) (finIdl_unit hu)
    (fun w => by rw [finIdl_fst]; rfl) fun PP x hx => ?_
  have hunit : IsUnitAt PP x := by
    unfold IsUnitAt
    rw [hx]
    exact finIdl_unit hu PP
  have hsub : Valued.v ((x : PP.adicCompletion D.host.E) - 1) = vl D PP ((u : AE D) - 1) := by
    rw [hx, vl_sub_one]
  have hμ : (L.C.mu0 j).loc PP x = 1 := by
    by_cases hg : ∃ k, OverP D.host (D.host.g k) PP
    · obtain ⟨k, hk⟩ := hg
      have hS : PP.under (𝓞 D.host.F) ∈ G.pl.S0 := by
        refine G.pl.mem_S0_of_sum_eq.2 (Or.inr ((S1_mem_OmF D).2 ?_))
        have : ((D.host.g k : ℕ) : 𝓞 D.host.F) ∈ (PP.under (𝓞 D.host.F)).asIdeal := by
          change _ ∈ PP.asIdeal.comap (algebraMap (𝓞 D.host.F) (𝓞 D.host.E))
          rw [Ideal.mem_comap, map_natCast]
          exact hk
        fin_cases k
        · exact Or.inl this
        · exact Or.inr (Or.inl this)
      refine (L.C.isMu0 j).tame PP x hunit ?_
      rw [hsub]
      refine (vl_sub_le' G.pl hc1 hc2 hS).trans ?_
      have : 1 ≤ condExp G.pl (PP.under (𝓞 D.host.F)) := by unfold condExp; split_ifs <;> omega
      exact WithZero.exp_le_exp.2 (by omega)
    · push_neg at hg
      exact (L.C.isMu0 j).unr PP hg x hunit
  have hχ : (G.ch.chiH (D.R.m - i)).loc PP x = 1 := by
    have h1 : 1 ≤ D.R.m - (i : ℕ) := by omega
    have h2 : D.R.m - (i : ℕ) ≤ D.R.m := by omega
    by_cases hS : PP.under (𝓞 D.host.F) ∈ G.pl.S0
    · have hb := vl_sub_le' G.pl hc1 hc2 hS
      rw [← hsub] at hb
      rcases G.pl.mem_S0_of_sum_eq.1 hS with h0 | h1'
      · rw [condExp, if_pos h0] at hb
        exact (G.ch.lev0 _ h1 h2 PP h0).1 x hunit (by simpa using hb)
      · have hne : PP.under (𝓞 D.host.F) ≠ G.pl.v0 := fun e => G.ch.basePlace_not_mem_chiGridBadPlaces (e ▸ h1')
        rw [condExp, if_neg hne] at hb
        exact (G.ch.lev1 _ h1 h2 PP h1').1 x hunit (by simpa using hb)
    · exact G.ch.unr _ h1 h2 PP hS x hunit
  show (nuH G μ₀ i j).loc PP x = 1
  rw [nuH, hL.xi_base, mul_one, div_eq_mul_inv, HChar.loc_mul, HChar.loc_inv, hμ, hχ]
  simp

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightCompatibilityStandardKernelDataTrueColumnsStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weightCompatibility_standardKernelData_trueColumns : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (L : SizeData₂ (I.rec7 l Z)) (hT : GatTies (I.rec7 l Z)) (Gi : G.Inst (I.rec7 l Z) L) (Gl : G.LatInst (I.rec7 l Z)) (K : G.Consts) (Y : DivX (I.rec7 l Z)) (cX : ExtraC) (ex : Extra (I.rec7 l Z) L hT Gi Gl K Y cX) (t : KerEntTied ex) (W : Formalism.L2.Col.Wts t.X t.Pr.Word (I.rec7 l Z).R) (Del h0 : ℕ), I.StdKer l Z t → HEq W B.wts → (I.rec7 l Z).s.Del = (Del : ℚ) → L.etaSz = ((I.rec7 l Z).R.m : ℝ) * (h0 : ℝ) → ∃ pl : RPl (I.rec7 l Z).R ≃ t.X.Tau, ∀ u, GlobalTheory.IndefiniteRowSideFullHecke.PlaceLogThetaBounds.WeightTie (ofRecord (I.rec7 l Z) L Del h0) W pl (t.word u) (letterOf (I.rec7 l Z) L Del h0 u) := by
  first | exact @GlobalTheory.ColRows.weightTie_of_stdKer | exact GlobalTheory.ColRows.weightTie_of_stdKer | (intros; apply GlobalTheory.ColRows.weightTie_of_stdKer <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilActionCosetVectorEqTranslateUnitVector
section
open scoped Pointwise
open Formalism.BasicNotions Formalism.IndefR.Links IsDedekindDomain NumberField
open Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.LeafRestExamples GlobalTheory.FunObj.SqNum GlobalTheory.NormSum GlobalTheory.FunObj.StdDatum
open GlobalTheory.Mem.Col2.SplitChar (finIdl)

noncomputable section

namespace GlobalTheory.FunObj.StdDatum.LiftCoset

theorem globalIntegralMatrix_mem_stdThetaLattice (D : D7) (δ : ℂ) {a d : ℕ} (x : Matrix (Fin d) (Fin a) D.host.E)
    (hx : ∀ i j, ∃ b : 𝓞 D.host.E, x i j = (b : D.host.E)) :
    pt D (tor0 D ⊤ δ) δ x ∈ La0 D (tor0 D ⊤ δ) a d := by
  refine AddSubgroup.subset_closure ⟨δ, AddSubgroup.subset_closure ⟨1, trivial, by simp⟩, _, ?_, rfl⟩
  refine Submodule.subset_span ⟨1, ?_, _, Submodule.subset_span fun v hv i _ => ?_, (one_smul _ _).symm⟩
  · refine FractionalIdeal.one_mem_inv_coe_ideal fun h => ?_
    have h2 := D.host.𝔟_spec.2
    rw [h, Ideal.smul_bot, sup_bot_eq] at h2
    exact bot_ne_top h2
  · have : ∑ j, x i j * v j ∈ (1 : Submodule (𝓞 D.host.E) D.host.E) := sum_mem fun j _ => by
      obtain ⟨b, hb⟩ := hx i j
      have h1 := (1 : Submodule (𝓞 D.host.E) D.host.E).smul_mem b (hv j trivial)
      rw [hb]
      simpa [Algebra.smul_def] using h1
    exact this

end GlobalTheory.FunObj.StdDatum.LiftCoset

namespace GlobalTheory.FunObj.StdDatum.LiftCoset

theorem unitBlock_mul_int (D : D7) {a d : ℕ} (r : GA D a) (hr : r ∈ intG D a) (i : Fin d) (j : Fin a) :
    ((unitBlock D 0 a d).map (inc D) * (((r⁻¹ : GA D a) : GL (Fin a) (AE D)) : Matrix (Fin a) (Fin a) (AE D))) i j ∈
      OhE D := by
  rw [Matrix.mul_apply]
  refine sum_mem fun l _ => mul_mem ?_ ?_
  · rw [Matrix.map_apply]
    by_cases h : i.1 = 0 + l.1
    · simp only [unitBlock, Matrix.of_apply, h, if_true, map_one]; exact one_mem _
    · simp only [unitBlock, Matrix.of_apply, h, if_false, map_zero]; exact zero_mem _
  · rw [Subgroup.coe_inv]
    exact ((mem_intG r).1 hr l j).2

theorem om_cosetV_eq : ∀ (D : D7) (δ : ℂ), Crv D ⊤ δ → ∀ {a d : ℕ} (e0 : VC D a d → ℂ), e0 ∈ Th D (tor0 D ⊤ δ) (stdL D a) (stdL D d) → ∀ (W : WeilO D ⊤ δ a d e0) (𝔪 : Ideal (𝓞 D.host.E)), 𝔪 ≠ ⊥ → ∀ (r : GA D a), r ∈ intG D a → ∃ x : Matrix (Fin d) (Fin a) D.host.E, pt D (tor0 D ⊤ δ) δ x ∈ (La0 D (tor0 D ⊤ δ) a d) ∧ (∀ i j, (x.map (inc D) - (unitBlock D 0 a d).map (inc D) * (((r⁻¹ : GA D a) : GL (Fin a) (AE D)) : Matrix (Fin a) (Fin a) (AE D))) i j ∈ hatId D 𝔪) ∧ W.Om r 1 (cosetV D δ 𝔪 0 a d e0) = ((Real.sqrt ((Ideal.absNorm 𝔪 : ℝ) ^ (a * d)) : ℂ))⁻¹ • Wd D (tor0 D ⊤ δ) (pt D (tor0 D ⊤ δ) δ x) (W.Om r 1 (Iop D (tor0 D ⊤ δ) (La0 D (tor0 D ⊤ δ) a d) (La D (tor0 D ⊤ δ) (stdL D a) (skewLat D 𝔪 d)) e0)) := by
  intro D δ hc a d e0 he W 𝔪 h𝔪 r hr
  set T := tor0 D ⊤ δ
  set G := Iop D T (La0 D T a d) (La D T (stdL D a) (skewLat D 𝔪 d)) e0 with hGdef
  set x₀ := unitBlock D 0 a d with hx₀
  have hT := GlobalTheory.ThetaLevels.levels_closed D ⊤ δ hc a d
  have he' : e0 ∈ TT D T a d := hT.1 _ _ (GlobalTheory.FunObj.CosetTT.sd_stdL a) (GlobalTheory.FunObj.CosetTT.sd_stdL d) e0 he
  obtain ⟨M, hM, hMx⟩ := GlobalTheory.FunObj.CosetTT.la_skew_nsmul (D := D) ⊤ δ 𝔪 a d
  have hG : G ∈ TT D T a d :=
    GlobalTheory.FunObj.CosetTT.iop_mem_TT hc _ (fun y hy => ⟨M, hM, hMx y hy⟩) he'
  have hF : Wd D T (pt D T δ x₀) G ∈ TT D T a d := hT.2.1 _ _ hG
  obtain ⟨m, hm, hlift⟩ := W.lift r 1 x₀ G hG
  have hN : 0 < Ideal.absNorm 𝔪 := Nat.pos_of_ne_zero (by simpa [Ideal.absNorm_eq_zero_iff] using h𝔪)
  set R : Matrix (Fin a) (Fin a) (AE D) := (((r⁻¹ : GA D a) : GL (Fin a) (AE D)) : Matrix (Fin a) (Fin a) (AE D)) with hR
  set Tm : Matrix (Fin d) (Fin a) (AE D) := x₀.map (inc D) * R with hTm
  have hTint : ∀ i j, Tm i j ∈ OhE D := fun i j => unitBlock_mul_int D r hr i j
  choose b w hw hbw using fun i j =>
    GlobalTheory.CongApprox.exists_int_approx D (m * Ideal.absNorm 𝔪) (Nat.mul_pos hm hN) (Tm i j) (hTint i j)
  set x : Matrix (Fin d) (Fin a) D.host.E := Matrix.of fun i j => (b i j : D.host.E) with hxdef
  have hdiff : ∀ i j, (x.map (inc D) - Tm) i j = -(((m * Ideal.absNorm 𝔪 : ℕ) : AE D) * w i j) := by
    intro i j
    rw [Matrix.sub_apply, Matrix.map_apply, hbw i j]
    simp [hxdef]
  have hnat : ∀ k : ℕ, ((k : ℕ) : AE D) ∈ OhE D := fun k => natCast_mem _ k
  refine ⟨x, LiftCoset.globalIntegralMatrix_mem_stdThetaLattice D δ x (fun i j => ⟨b i j, rfl⟩), fun i j => ?_, ?_⟩
  · rw [hdiff i j, Nat.cast_mul, mul_comm ((m : ℕ) : AE D), mul_assoc]
    exact neg_mem (GlobalTheory.BotPairSmall.BlockIdx.absNorm_mul_mem_hatId D 𝔪 (mul_mem (hnat m) (hw i j)))
  · have hclose : CloseTo D ⊤ m (r : GL (Fin a) (AE D)) ((1 : GA D d) : GL (Fin d) (AE D)) x₀ x := by
      intro i j
      refine ⟨-(((Ideal.absNorm 𝔪 : ℕ) : AE D) * w i j),
        GlobalTheory.CongApprox.OhE_le_IhE_top D _ (neg_mem (mul_mem (hnat _) (hw i j))), ?_⟩
      have e1 : (((1 : GA D d) : GL (Fin d) (AE D)) : Matrix (Fin d) (Fin d) (AE D)) = 1 := by simp
      have e2 : (((r : GL (Fin a) (AE D))⁻¹ : GL (Fin a) (AE D)) : Matrix (Fin a) (Fin a) (AE D)) = R := by
        rw [hR, Subgroup.coe_inv]
      rw [e1, Matrix.one_mul, e2, ← hTm, hdiff i j, Nat.cast_mul]
      ring
    have hl := hlift x hclose
    show W.Om r 1 (((Real.sqrt ((Ideal.absNorm 𝔪 : ℝ) ^ (a * d)) : ℂ))⁻¹ • Wd D T (pt D T δ x₀) G) = _
    rw [W.smul r 1 _ _ hF, hl]

end GlobalTheory.FunObj.StdDatum.LiftCoset

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilIntegralPointSkewLatticeUnitVectorSameEigen
section
open scoped Pointwise nonZeroDivisors
open Formalism.BasicNotions Formalism.IndefR.Links IsDedekindDomain NumberField
open Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.LeafRestExamples GlobalTheory.FunObj.SqNum GlobalTheory.NormSum GlobalTheory.FunObj.StdDatum
open GlobalTheory.Mem.Col2.SplitChar (finIdl)

noncomputable section
namespace GlobalTheory.FunObj.EigUnit

theorem conj_smul_smul (D : D7) (I : Ideal (𝓞 D.host.E)) : D.host.conj • D.host.conj • I = I := by
  have h2 : D.host.conj * D.host.conj = 1 := AlgEquiv.ext fun x => VacMove.conj_conj D x
  rw [smul_smul, h2, one_smul]

theorem conj_smul_mul (D : D7) (I J : Ideal (𝓞 D.host.E)) :
    D.host.conj • (I * J) = D.host.conj • I * D.host.conj • J := by
  simp only [Ideal.pointwise_smul_def, Ideal.map_mul]

theorem conj_smul_mono (D : D7) {I J : Ideal (𝓞 D.host.E)} (h : I ≤ J) : D.host.conj • I ≤ D.host.conj • J := by
  simp only [Ideal.pointwise_smul_def]; exact Ideal.map_mono h

theorem coprime_rep (D : D7) (𝔪 : Ideal (𝓞 D.host.E)) (h𝔪 : 𝔪 ≠ ⊥) :
    ∃ 𝔫 : Ideal (𝓞 D.host.E), 𝔫 ≠ ⊥ ∧ IsCoprime 𝔫 (D.host.conj • 𝔫) ∧
      𝔪 * D.host.conj • 𝔫 = 𝔫 * D.host.conj • 𝔪 := by
  induction 𝔪 using UniqueFactorizationMonoid.induction_on_prime with
  | h₁ => exact absurd rfl h𝔪
  | h₂ x hx =>
    rw [Ideal.isUnit_iff] at hx
    subst hx
    exact ⟨⊤, top_ne_bot, by rw [Ideal.isCoprime_iff_sup_eq]; exact top_sup_eq _, rfl⟩
  | h₃ x p hx hp ih =>
    obtain ⟨n, hn, hcop, hxn⟩ := ih hx
    have hpb : p ≠ ⊥ := hp.ne_zero
    have hpP : p.IsPrime := Ideal.isPrime_of_prime hp
    have hpM : p.IsMaximal := hpP.isMaximal hpb
    have hsb : D.host.conj • p ≠ ⊥ := GlobalTheory.BotPairSmall.conj_smul_ne_bot D hpb
    have hsM : (D.host.conj • p).IsMaximal := (Ideal.IsPrime.smul D.host.conj).isMaximal hsb
    by_cases hfix : D.host.conj • p = p
    · refine ⟨n, hn, hcop, ?_⟩
      rw [conj_smul_mul, hfix, mul_assoc, hxn]
      ring
    by_cases hdiv : n ≤ D.host.conj • p
    · obtain ⟨n', rfl⟩ := Ideal.dvd_iff_le.2 hdiv
      refine ⟨n', fun h0 => hn (by rw [h0, Ideal.mul_bot]), ?_, ?_⟩
      · rw [conj_smul_mul] at hcop
        exact (hcop.of_mul_left_right).of_mul_right_right
      · simp only [conj_smul_mul, conj_smul_smul] at hxn ⊢
        calc p * x * D.host.conj • n' = x * p * D.host.conj • n' := by ring
          _ = D.host.conj • p * n' * D.host.conj • x := by rw [mul_assoc, hxn]
          _ = n' * (D.host.conj • p * D.host.conj • x) := by ring
    · refine ⟨p * n, mul_ne_zero hpb hn, ?_, ?_⟩
      · have hnot : ¬ D.host.conj • n ≤ p := fun h => hdiv (by
          have := conj_smul_mono D h
          rwa [conj_smul_smul] at this)
        have c1 : IsCoprime p (D.host.conj • p) := by
          rw [Ideal.isCoprime_iff_sup_eq]
          by_contra hne
          have h3 : p = p ⊔ D.host.conj • p := hpM.eq_of_le hne le_sup_left
          exact hfix (hsM.eq_of_le hpM.ne_top (le_sup_right.trans h3.ge))
        have c2 : IsCoprime p (D.host.conj • n) := by
          rw [Ideal.isCoprime_iff_sup_eq]
          by_contra hne
          have h3 : p = p ⊔ D.host.conj • n := hpM.eq_of_le hne le_sup_left
          exact hnot (le_sup_right.trans h3.ge)
        have c3 : IsCoprime n (D.host.conj • p) := by
          rw [Ideal.isCoprime_iff_sup_eq, sup_comm]
          by_contra hne
          have h3 : D.host.conj • p = D.host.conj • p ⊔ n := hsM.eq_of_le hne le_sup_left
          exact hdiv (le_sup_right.trans h3.ge)
        rw [conj_smul_mul]
        exact IsCoprime.mul_left (IsCoprime.mul_right c1 c2) (IsCoprime.mul_right c3 hcop)
      · rw [conj_smul_mul, conj_smul_mul]
        calc p * x * (D.host.conj • p * D.host.conj • n) = p * D.host.conj • p * (x * D.host.conj • n) := by ring
          _ = p * D.host.conj • p * (n * D.host.conj • x) := by rw [hxn]
          _ = p * n * (D.host.conj • p * D.host.conj • x) := by ring

theorem zeroAt_zero' (D : D7) (q : ℕ) : ZeroAt D q 0 :=
  fun _ => ⟨1, one_pos, Nat.coprime_one_left q, 0, zero_mem _, by simp⟩

theorem suppSplit_one' (D : D7) (N : ℕ) : SuppSplit D ((1 : GA D N) : GL (Fin N) (AE D)) :=
  fun q _ _ i j => by rw [OneMemClass.coe_one, Units.val_one, sub_self]; exact zeroAt_zero' D q

theorem skewLat_eq (D : D7) {𝔪 𝔫 : Ideal (𝓞 D.host.E)} (h𝔪 : 𝔪 ≠ ⊥) (h𝔫 : 𝔫 ≠ ⊥)
    (h : 𝔪 * D.host.conj • 𝔫 = 𝔫 * D.host.conj • 𝔪) (N : ℕ) : skewLat D 𝔪 N = skewLat D 𝔫 N := by
  have e : ((𝔪 : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) /
      ((D.host.conj • 𝔪 : Ideal (𝓞 D.host.E)) : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E)) =
      ((𝔫 : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) /
      ((D.host.conj • 𝔫 : Ideal (𝓞 D.host.E)) : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E)) := by
    rw [div_eq_div_iff (FractionalIdeal.coeIdeal_ne_zero.2 (GlobalTheory.BotPairSmall.conj_smul_ne_bot D h𝔪))
      (FractionalIdeal.coeIdeal_ne_zero.2 (GlobalTheory.BotPairSmall.conj_smul_ne_bot D h𝔫)), ← FractionalIdeal.coeIdeal_mul,
      ← FractionalIdeal.coeIdeal_mul, h]
  unfold skewLat
  rw [e]

theorem eig_unit : ∀ (D : D7) (δ : ℂ), Crv D ⊤ δ → ∀ {a d : ℕ} (e0 : VC D a d → ℂ), e0 ∈ Th D (tor0 D ⊤ δ) (stdL D a) (stdL D d) → ∀ (W : WeilO D ⊤ δ a d e0) (𝔪 : Ideal (𝓞 D.host.E)), 𝔪 ≠ ⊥ → ∀ (r : GA D a), r ∈ intG D a → ∀ c : ℂ, W.Om r 1 e0 = c • e0 → W.Om r 1 (Iop D (tor0 D ⊤ δ) (La0 D (tor0 D ⊤ δ) a d) (La D (tor0 D ⊤ δ) (stdL D a) (skewLat D 𝔪 d)) e0) = c • Iop D (tor0 D ⊤ δ) (La0 D (tor0 D ⊤ δ) a d) (La D (tor0 D ⊤ δ) (stdL D a) (skewLat D 𝔪 d)) e0 := by
  intro D δ hc a d e0 he W 𝔪 h𝔪 r hr c hrc
  have h1 := (GlobalTheory.InducedType.induced_type D).1
  have hT := VacMove.vac_TT h1 hc he
  obtain ⟨𝔫, h𝔫, hcop, hmn⟩ := coprime_rep D 𝔪 h𝔪
  rw [skewLat_eq D h𝔪 h𝔫 hmn d]
  obtain ⟨g', x', hg's, hg'm, hx'q, hx'd⟩ := GlobalTheory.T.exists_splitSupported_unitary_moving_to_selfDualSkewLattice D 𝔫 h𝔫 hcop d
  have hJ : W.Om 1 g' e0 = ((W.chV.f x' ^ W.ep * W.chV'.f 1 ^ W.ep' : ℂˣ) : ℂ) •
      Iop D (tor0 D ⊤ δ) (La0 D (tor0 D ⊤ δ) a d) (La D (tor0 D ⊤ δ) (stdL D a) (skewLat D 𝔫 d)) e0 := by
    rw [W.split 1 g' 1 x' (stdL D a) (skewLat D 𝔫 d) (suppSplit_one' D a) hg's
      (fun q hq hi => ⟨by simpa using zeroAt_zero' D q, hx'q q hq hi⟩) (by simp) hx'd (VacMove.moves_one D a) hg'm]
    rfl
  have hc0 : ((W.chV.f x' ^ W.ep * W.chV'.f 1 ^ W.ep' : ℂˣ) : ℂ) ≠ 0 := Units.ne_zero _
  have hJe : Iop D (tor0 D ⊤ δ) (La0 D (tor0 D ⊤ δ) a d) (La D (tor0 D ⊤ δ) (stdL D a) (skewLat D 𝔫 d)) e0 =
      ((W.chV.f x' ^ W.ep * W.chV'.f 1 ^ W.ep' : ℂˣ) : ℂ)⁻¹ • W.Om 1 g' e0 := by
    rw [hJ, smul_smul, inv_mul_cancel₀ hc0, one_smul]
  have e1 := W.mul r 1 1 g' e0 hT
  have e2 := W.mul 1 r g' 1 e0 hT
  rw [mul_one, one_mul] at e1
  rw [one_mul, mul_one, hrc, W.smul _ _ _ _ hT] at e2
  rw [hJe, W.smul _ _ _ _ (W.maps 1 g' e0 hT), ← e1, e2, smul_comm]

end GlobalTheory.FunObj.EigUnit
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WordActionSquareIntegrableBoundStatement
section
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped TensorProduct NNReal Matrix
open scoped Classical
open GlobalTheory.ArchDecay
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.word_action_square_integrable_bound : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' → ∀ Φ ∈ schA F (Fin n × Fin d), ∀ (μ : @Measure (Fin n × Fin d → AF F) (borel _)), @Measure.IsAddHaarMeasure _ _ _ (borel _) μ → ∀ p : ℕ, ∃ (C : ℝ) (k : ℕ), ∀ g h (w : List (Op F (Fin n × Fin d))), w.length ≤ p → (∀ o ∈ w, size F o ≤ 1) → ∫⁻ x, ‖word F w (om (g, h) Φ) x‖ₑ ^ 2 ∂μ ≤ ENNReal.ofReal (C * ((ht g : ℝ) * ht h) ^ k) := by
  first | exact @GlobalTheory.ArchDecay.word_action_square_integrable | exact GlobalTheory.ArchDecay.word_action_square_integrable | (intros; apply GlobalTheory.ArchDecay.word_action_square_integrable <;> assumption)
end

