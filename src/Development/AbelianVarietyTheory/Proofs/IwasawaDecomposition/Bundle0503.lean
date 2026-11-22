import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0471
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0487
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MemPrinCongOfSm
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StepZeroTwistReferenceTupleEqId
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsClosedNFlag
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0214
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0036
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMulRightInvariantHaarAdelicUnitaryGroupHermiti
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0488
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0472
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0447
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0453
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0449
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RowsRestWordColumnUnitBaseTupleAlt
import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsHermPosChainRealEndSpaceTuple
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RowFiniteTypesIsotypicPartsSpanOrthogonal
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0492
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0027
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0494
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0021
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NVNeZero
import Formalism.LocalToGlobal.IndefiniteReal.BridgeColPts
import Formalism.LocalToGlobal.Columns.Bundle0017
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0495
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0014
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0027
import Formalism.LocalToGlobal.KernelLattices.TopPin
import Formalism.LocalToGlobal.KernelLattices.Bundle0001
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0008
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0475
import Formalism.LocalToGlobal.KernelLattices.ColumnData.DiagramFitsSourceRank
import Formalism.UnipotentAdelicQuotients.Bundle0002
import Formalism.LocalToGlobal.Divisibility.NumbersLemmas
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0496
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0028
import Formalism.SharpRestriction.GlobalSchurBounds.ThickPlacesCorollaryOfAnyTranslate
import Formalism.LocalToGlobal.GroupLattices.ComparisonMaps.ComparisonZeroEmbedding
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0483
import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.UnitTraceSumBounds.Bundle0007
import Formalism.LocalRingCardinality.FactDelDualNabla
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0456
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StepLevelContainsDeepCongruenceAtBadPrime
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LevelElementAtBadPrimesIntegralAndNear
import Formalism.LocalToGlobal.Columns.Bundle0016
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0497
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0035

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RationalAutomorphismsNearSameAdelicCongruent
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.AdT Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.Col2.AdT.AdTieNear

theorem entries_le_of_add_mul {K : Type} [Field K] (v : Valuation K (WithZero (Multiplicative ℤ))) {n : ℕ}
    (A D : Matrix (Fin n) (Fin n) K) (c : WithZero (Multiplicative ℤ)) (hA : ∀ r s, v (A r s) < 1)
    (h : ∀ r s, v ((D + A * D) r s) ≤ c) (r s : Fin n) : v (D r s) ≤ c := by
  obtain ⟨p, -, hmax⟩ := Finset.exists_max_image (Finset.univ : Finset (Fin n × Fin n))
    (fun p => v (D p.1 p.2)) ⟨(r, s), Finset.mem_univ _⟩
  refine (hmax (r, s) (Finset.mem_univ _)).trans ?_
  by_cases hμ : v (D p.1 p.2) = 0
  · rw [hμ]; exact zero_le'
  have hlt : v ((A * D) p.1 p.2) < v (D p.1 p.2) := by
    rw [Matrix.mul_apply]
    refine Valuation.map_sum_lt _ hμ fun k _ => ?_
    rw [map_mul]
    calc v (A p.1 k) * v (D k p.2) ≤ v (A p.1 k) * v (D p.1 p.2) :=
          mul_le_mul_right (hmax (k, p.2) (Finset.mem_univ _)) _
      _ < 1 * v (D p.1 p.2) := mul_lt_mul_of_pos_right (hA p.1 k) (zero_lt_iff.2 hμ)
      _ = v (D p.1 p.2) := one_mul _
  have e := Valuation.map_add_eq_of_lt_left v hlt
  rw [← e, ← Matrix.add_apply]
  exact h p.1 p.2

section Gen

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [StarRing E]

theorem adAt_ratA {n : ℕ} (P : HeightOneSpectrum (𝓞 E)) (G : GL (Fin n) E) (r s : Fin n) :
    adAt F P ((GlobalTheory.TwU.ratA F G : GL (Fin n) (AfE F E)) r s) = algebraMap E (P.adicCompletion E) ((G : Matrix (Fin n) (Fin n) E) r s) := by
  exact adAt_inclE F P _

theorem congE_of_near (P : HeightOneSpectrum (𝓞 E)) {n : ℕ} (d d' : ℕ) (hd' : 1 ≤ d') (hdd : d' ≤ d)
    (x : GL (Fin n) (AfE F E)) (g g' : Sp E n ≃ₗ[E] Sp E n) (G G' : GL (Fin n) E)
    (hG : ∀ w, (G : Matrix (Fin n) (Fin n) E) *ᵥ w = g w) (hG' : ∀ w, (G' : Matrix (Fin n) (Fin n) E) *ᵥ w = g' w)
    (hg : g ∈ Formalism.L2.Col.GLint E n P)
    (hq : Valued.v ((qOf P : ℕ) : P.adicCompletion E) = WithZero.exp (-1 : ℤ))
    (hy : ∀ r s, Valued.v (adAt F P (((x⁻¹ * GlobalTheory.TwU.ratA F G : GL (Fin n) (AfE F E)) : Matrix (Fin n) (Fin n) (AfE F E)) r s)
      - (1 : Matrix (Fin n) (Fin n) (P.adicCompletion E)) r s) ≤ WithZero.exp (-(d : ℤ)))
    (hy' : ∀ r s, Valued.v (adAt F P (((x⁻¹ * GlobalTheory.TwU.ratA F G' : GL (Fin n) (AfE F E)) : Matrix (Fin n) (Fin n) (AfE F E)) r s)
      - (1 : Matrix (Fin n) (Fin n) (P.adicCompletion E)) r s) ≤ WithZero.exp (-(d' : ℤ))) :
    CongE P d' g' g := by
  set φ := adAt F P
  set y := x⁻¹ * GlobalTheory.TwU.ratA F G
  set y' := x⁻¹ * GlobalTheory.TwU.ratA F G'
  set H : GL (Fin n) E := G⁻¹ * G'
  have hyH : y * GlobalTheory.TwU.ratA F H = y' := by
    simp only [y, y', H, map_mul, map_inv, mul_assoc, mul_inv_cancel_left]
  set Y : Matrix (Fin n) (Fin n) (P.adicCompletion E) := (y : Matrix (Fin n) (Fin n) (AfE F E)).map φ
  set Y' : Matrix (Fin n) (Fin n) (P.adicCompletion E) := (y' : Matrix (Fin n) (Fin n) (AfE F E)).map φ
  set R : Matrix (Fin n) (Fin n) (P.adicCompletion E) := ((GlobalTheory.TwU.ratA F H : GL (Fin n) (AfE F E)) : Matrix (Fin n) (Fin n) (AfE F E)).map φ
  have hYR : Y * R = Y' := by
    simp only [Y, Y', R, ← Matrix.map_mul, ← Units.val_mul, hyH]
  have hdA : ∀ r s, Valued.v ((Y - 1) r s) < 1 := fun r s => by
    refine lt_of_le_of_lt (hy r s) ?_
    rw [← WithZero.exp_zero, WithZero.exp_lt_exp]
    omega
  have hsum : ∀ r s, Valued.v (((R - 1) + (Y - 1) * (R - 1)) r s) ≤ WithZero.exp (-(d' : ℤ)) := fun r s => by
    have e : (R - 1) + (Y - 1) * (R - 1) = (Y' - 1) - (Y - 1) := by
      rw [← hYR]; noncomm_ring
    rw [e, Matrix.sub_apply]
    refine Valuation.map_sub_le _ (hy' r s) ((hy r s).trans ?_)
    rw [WithZero.exp_le_exp]; omega
  have hD := entries_le_of_add_mul Valued.v (Y - 1) (R - 1) _ hdA hsum

  have hH : ∀ r s, Valued.v (algebraMap E (P.adicCompletion E) (((H : Matrix (Fin n) (Fin n) E) - 1) r s)) ≤ WithZero.exp (-(d' : ℤ)) := by
    intro r s
    have e : (R - 1) r s = algebraMap E (P.adicCompletion E) (((H : Matrix (Fin n) (Fin n) E) - 1) r s) := by
      rw [Matrix.sub_apply, Matrix.sub_apply, map_sub]
      simp only [R, Matrix.map_apply, φ, adAt_ratA]
      rw [Matrix.one_apply, Matrix.one_apply]
      split_ifs <;> simp
    rw [← e]; exact hD r s
  intro w hw
  have hHw : g ((H : Matrix (Fin n) (Fin n) E) *ᵥ w) = g' w := by
    rw [← hG, Matrix.mulVec_mulVec, ← Units.val_mul, ← hG']
    simp only [H, mul_inv_cancel_left]
  have e : (((qOf P : ℕ) : E) ^ d')⁻¹ • (g' w - g w) =
      g ((((qOf P : ℕ) : E) ^ d')⁻¹ • (((H : Matrix (Fin n) (Fin n) E) - 1) *ᵥ w)) := by
    rw [map_smul, Matrix.sub_mulVec, Matrix.one_mulVec, map_sub, hHw]
  rw [e]
  refine (hg _).2 ?_
  rw [GlobalTheory.Mem.ColAd.mem_stdAt_val] at hw ⊢
  intro l
  have hs : Valued.v (algebraMap E (P.adicCompletion E) ((((H : Matrix (Fin n) (Fin n) E) - 1) *ᵥ w) l)) ≤ WithZero.exp (-(d' : ℤ)) := by
    simp only [Matrix.mulVec, dotProduct, map_sum]
    refine Valuation.map_sum_le _ fun k _ => ?_
    rw [map_mul, map_mul]
    calc _ ≤ WithZero.exp (-(d' : ℤ)) * 1 := mul_le_mul' (hH l k) (hw k)
      _ = _ := mul_one _
  rw [Pi.smul_apply, smul_eq_mul, map_mul, map_mul, map_inv₀, map_inv₀, map_pow, map_pow, map_natCast, hq]
  calc _ ≤ (WithZero.exp (-1 : ℤ) ^ d')⁻¹ * WithZero.exp (-(d' : ℤ)) := mul_le_mul_right hs _
    _ = 1 := by
      rw [← WithZero.exp_nsmul, ← WithZero.exp_neg, ← WithZero.exp_add]
      simp

end Gen

end GlobalTheory.Mem.Col2.AdT.AdTieNear

namespace GlobalTheory.Mem.Col2.AdT.AdTieNear

set_option maxHeartbeats 800000 in

theorem main : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (a : I.ι) (i : ℕ) (fb : SBof I a → GL (Fin ((I.rec7 l Z).R.N i)) (I.rec7 l Z).host.E) (dep dep' : SBof I a → ℕ) (P : SBof I a) (κ : GL (Fin ((I.rec7 l Z).R.N i)) (AfE (I.rec7 l Z).host.F (I.rec7 l Z).host.E)) (g g' : Sp B.fields.E (B.R.N i) ≃ₗ[B.fields.E] Sp B.fields.E (B.R.N i)), g ∈ Formalism.L2.Col.GLint B.fields.E (B.R.N i) P.1 → 1 ≤ dep' P → dep' P ≤ dep P → GlobalTheory.TwU.InFrame (i := i) (sm I l Z) fb dep P κ g → GlobalTheory.TwU.InFrame (i := i) (sm I l Z) fb dep' P κ g' → CongE P.1 (dep' P) g' g := by
  intro B X I hOk l Z a i fb dep dep' P κ g g' hg h1 hdd hF hF'
  unfold GlobalTheory.TwU.InFrame GlobalTheory.TwU.NearAt at hF hF'
  have hq := (GlobalTheory.T.adelicMatrixCongruenceBadPrime_iff_completion I hOk l Z a ((I.rec7 l Z).R.N i) 0 P 1).2.1
  have hy := (GlobalTheory.T.adelicMatrixCongruenceBadPrime_iff_completion I hOk l Z a _ (dep P) P _).2.2.1 hF
  have hy' := (GlobalTheory.T.adelicMatrixCongruenceBadPrime_iff_completion I hOk l Z a _ (dep' P) P _).2.2.1 hF'
  exact congE_of_near (F := B.host.F) P.1 (dep P) (dep' P) h1 hdd _ g g'
    (GlobalTheory.TwU.seamGL (sm I l Z) g) (GlobalTheory.TwU.seamGL (sm I l Z) g')
    (fun w => GlobalTheory.TwU.seamGL_mulVec (sm I l Z) g w) (fun w => GlobalTheory.TwU.seamGL_mulVec (sm I l Z) g' w)
    hg hq hy hy'

end GlobalTheory.Mem.Col2.AdT.AdTieNear
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RedGLEqOneOfLqPrinc
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.TopStep Matrix
open Formalism.L2.Theta GlobalTheory.Mem.Th Filter Topology MeasureTheory
open GlobalTheory.Mem.ColAd GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2.TC
open Formalism.MainNotions Formalism.L2.Ker Formalism.UG GlobalTheory.Mem.Col2.TopCh
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.TopStepPrimes

open IsDedekindDomain.HeightOneSpectrum GlobalTheory.TopStep

theorem reduction_eq_zero_of_valuation_le {E : Type} [Field E] [NumberField E] {P : HeightOneSpectrum (𝓞 E)} {x : E}
    (h : P.valuation E x ≤ WithZero.coe (Multiplicative.ofAdd (-((1 : ℕ) : ℤ)))) : redP P x = 0 := by
  have hlt : P.valuation E x < 1 := h.trans_lt (by decide)
  obtain ⟨n, d, hnd⟩ := P.exists_primeCompl_mul_eq_of_integer x hlt.le
  have hd : (d : 𝓞 E) ∉ P.asIdeal := d.2
  have hdv : P.valuation E (algebraMap (𝓞 E) E d) = 1 := by
    rw [valuation_of_algebraMap]
    exact le_antisymm (P.intValuation_le_one _) (not_lt.1 fun hc => hd ((P.intValuation_lt_one_iff_mem _).1 hc))
  have hn : n ∈ P.asIdeal := by
    rw [← P.valuation_lt_one_iff_mem (K := E)]
    change P.valuation E (algebraMap (𝓞 E) E n) < 1
    rw [← hnd, map_mul, hdv, mul_one]
    exact hlt
  have hs := reduction_spec P hd (a := x) (r := n) (by rw [mul_comm]; exact hnd)
  rw [Ideal.Quotient.eq_zero_iff_mem.2 hn] at hs
  exact (mul_eq_zero.1 hs).resolve_left (mk_ne_zero hd)

theorem redGL_eq_one_of_lqPrinc {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ} {P : HeightOneSpectrum (𝓞 E)}
    (g : GLint E n P) (hg : lqPrinc P 1 (g : Sp E n ≃ₗ[E] Sp E n)) : redGL n P g = 1 := by
  apply Units.ext
  rw [redGL_val]
  ext i j
  have h2 : LinearMap.toMatrix' ((g : Sp E n ≃ₗ[E] Sp E n) : Sp E n →ₗ[E] Sp E n) i j = g.1 (Pi.single j 1) i := by
    rw [LinearMap.toMatrix'_apply]
    rfl
  have hv := hg i j
  rw [Matrix.sub_apply, h2] at hv
  have hx := glint_entry g i j
  have hδ : IntAt P ((1 : Matrix (Fin n) (Fin n) E) i j) := by
    by_cases hij : i = j
    · simpa [Matrix.one_apply, hij] using intAt_one
    · simpa [Matrix.one_apply, hij] using intAt_zero
  have hr : redP P ((1 : Matrix (Fin n) (Fin n) E) i j) = (1 : Matrix (Fin n) (Fin n) (𝓞 E ⧸ P.asIdeal)) i j := by
    by_cases hij : i = j
    · simpa [Matrix.one_apply, hij] using reduction_one₂
    · simpa [Matrix.one_apply, hij] using reduction_zero
  have e : g.1 (Pi.single j 1) i = (g.1 (Pi.single j 1) i - (1 : Matrix (Fin n) (Fin n) E) i j) +
      (1 : Matrix (Fin n) (Fin n) E) i j := by ring
  show redP P (g.1 (Pi.single j 1) i) = _
  rw [e, reduction_add (intAt_sub hx hδ) hδ, reduction_eq_zero_of_valuation_le hv, zero_add, hr]
  rfl

end GlobalTheory.TopStepPrimes

open GlobalTheory.TopStepPrimes in

theorem GlobalTheory.TopStepPrimes.primes_top_ok : ∀ {B : Base} {X : PreX B.toPre} {I : TC B X}, I.Ok → ∀ (u : B.Word) (a : I.ι), Disjoint (B.primes X).vGs (I.Q a) ∧ (∀ P ∈ uSG ∅ (uSG (B.primes X).vGs (I.Q a)), conjPrime₂ P ∉ uSG ∅ (uSG (B.primes X).vGs (I.Q a))) ∧ ∀ (P : I.Q a) (g : ↥(GLint B.fields.E (B.R.N B.R.m - 1) P.1)), lqPrinc P.1 1 (g : Sp B.fields.E (B.R.N B.R.m - 1) ≃ₗ[B.fields.E] Sp B.fields.E (B.R.N B.R.m - 1)) → ∃ h : g ∈ (levQX B.R I.sel (I.tup a) P).H, (levQX B.R I.sel (I.tup a) P).lam ⟨g, h⟩ = 1 := by
  intro B X I h u a
  obtain ⟨hX, hPr, -⟩ := base_fields_primes_ok B X
  refine ⟨?_, ?_, ?_⟩
  · exact (GlobalTheory.Mem.LevTwist.levOk_twists B X I h).2.1.mono_right (I.Q_subset_SQ a)
  · intro P hP
    have h1 := GlobalTheory.ThetaMove.BadPrimes.bad_primes B.fields (B.primes X) I.sel I.S (I.tup a) u hX hPr h.sel_ok (h.T_mem u) h.g_mem
    unfold Sall at h1
    simp only [Finset.mem_union] at h1 hP ⊢
    rcases hP with h0 | hP
    · exact absurd h0 (Finset.notMem_empty _)
    · rintro (hc | hc)
      · exact Finset.notMem_empty _ hc
      · exact (h1 P (Or.inr hP)).1 (Or.inr hc)
  · intro P g hg
    have e := redGL_eq_one_of_lqPrinc g hg
    refine ⟨(mem_levQX _ _ _ _).2 (e ▸ Subgroup.one_mem _), ?_⟩
    rw [levQX_lam]
    have key : ∀ {G M : Type} [Group G] [Monoid M] (H : Subgroup G) (f : H →* M) (y : G) (hy : y ∈ H), y = 1 → f ⟨y, hy⟩ = 1 := by
      rintro G M _ _ H f y hy rfl
      exact map_one f
    exact key _ _ _ _ e
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RowFiniteTypePartsSpanAndOrthogonal
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw

noncomputable section

namespace GlobalTheory.Mem.R3.Rw.TypesRows

theorem parts_span_orth : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd), Inputs D → Pins R F cG → Holds R F → ∀ (y : Hd R.toRealDat) (Φ : Type) (rep : Φ → Formalism.L2.NG.FinTyp D.host.E D.R.r), Reps y F.lv2 rep → ∀ b : Bool, (⨆ π, y.prtE F.lv2 b (rep π)) = (y.C F.lv2).EEc b ∧ ∀ π π', π ≠ π' → ∀ x ∈ y.prtE F.lv2 b (rep π), ∀ x' ∈ y.prtE F.lv2 b (rep π'), (y.C F.lv2).ipE b x x' = 0 := by
  intro D G _ _ Pl0 I0 T A3 Ks _ _ _ R F cG hI hP hH y Φ rep hR b
  have hB := hP.char.base
  have h0 := hB.models.ν0
  have hs := GlobalTheory.HilbertLevels.scaled (inv_pos.2 (GlobalTheory.HilbertLevels.nP_pos F.lv2 b)) h0.1.1 h0.2
  obtain ⟨s, c, hsG, he⟩ : ∃ (s : Finset (GA D (Yc D 0))) (c : GA D (Yc D 0) → ℂ), (∀ g ∈ s, g ∈ GfC (Yc D 0)) ∧
      R.e0 = ∑ g ∈ s, c g • principalLevelFrame.rtA g :=
    GlobalTheory.Mem.R3.IsotIndep.gaL_finSum (Yc D 0) (R.βY 0) (R.dat0 R.triv) R.eG _
  have key := GlobalTheory.FinTypesRows.isotL_span_orth D (Yc D 0) _ R.θ (R.MY 0) y.PY y.hF (R.βY 0) (R.dat0 (R.levR F.lv2 b)) R.e0
    (ENNReal.ofReal (RealDat.nP F.lv2 b)⁻¹ • R.ν0) R.fd0 hI (D.sp.Y_sig _) hB.models.inf y.stdPsi.1 hs.1 hs.2 ⟨s, c, hsG, he⟩

  set J := levS _ (R.βY 0) (R.dat0 (R.levR F.lv2 b)) with hJ
  set χ := levChi _ (R.βY 0) (R.dat0 (R.levR F.lv2 b)) with hχ

  have hcc : ∀ ρ : Formalism.L2.NG.FinTyp D.host.E D.R.r, (principalLevelFrame.FinTyp.conjT (principalLevelFrame.FinTyp.conjT ρ)).Iso ρ := by
    intro ρ
    unfold Formalism.L2.NG.FinTyp.Iso
    rw [principalLevelFrame.conjT_S, principalLevelFrame.conjT_S, principalLevelFrame.conjSub_conjSub]
    exact Formalism.L2.NG.IsoRep.refl _
  have hspan : (⨆ π, principalLevelFrame.isotE R.θ y.PY (R.MY 0) J χ R.e0 (rep π)) = Mult.goodPart R.θ (R.MY 0) J χ R.e0 := by
    refine le_antisymm (iSup_le fun π => inf_le_left) ?_
    rw [← key.1]
    refine iSup_le fun ρ => ?_
    by_cases h0 : principalLevelFrame.isotL R.θ y.PY (R.MY 0) J χ R.e0 ρ = ⊥
    · rw [h0]
      exact bot_le
    · have he1 : principalLevelFrame.isotE R.θ y.PY (R.MY 0) J χ R.e0 (principalLevelFrame.FinTyp.conjT ρ) = principalLevelFrame.isotL R.θ y.PY (R.MY 0) J χ R.e0 ρ :=
        principalLevelFrame.isotL_iso R.θ y.PY (R.MY 0) J χ R.e0 (hcc ρ)
      have hocc : principalLevelFrame.FinTyp.conjT ρ ∈ y.occ F.lv2 := ⟨b, by rw [he1]; exact h0⟩
      obtain ⟨π, hπ⟩ := hR.all _ hocc
      have he2 : principalLevelFrame.isotE R.θ y.PY (R.MY 0) J χ R.e0 (rep π) = principalLevelFrame.isotL R.θ y.PY (R.MY 0) J χ R.e0 ρ := by
        rw [← he1]
        exact principalLevelFrame.isotL_iso R.θ y.PY (R.MY 0) J χ R.e0 (principalLevelFrame.conjT_iso hπ)
      exact le_iSup_of_le π (le_of_eq he2.symm)
  refine ⟨?_, ?_⟩
  · unfold Hd.prtE
    show (⨆ π, (principalLevelFrame.isotE R.θ y.PY (R.MY 0) J χ R.e0 (rep π)).map
        (PiTensorProduct.lift : Mult.MMap (R.MY 0) ≃ₗ[ℂ] _).toLinearMap) =
      (Mult.goodPart R.θ (R.MY 0) J χ R.e0).map (PiTensorProduct.lift : Mult.MMap (R.MY 0) ≃ₗ[ℂ] _).toLinearMap
    rw [← hspan, Submodule.map_iSup]
  · intro π π' hne x hx x' hx'
    obtain ⟨u, hu, rfl⟩ := hx
    obtain ⟨u', hu', rfl⟩ := hx'
    have hni : ¬ (principalLevelFrame.FinTyp.conjT (rep π)).Iso (principalLevelFrame.FinTyp.conjT (rep π')) :=
      principalLevelFrame.not_iso_conjT fun h => hne (hR.inj π π' h)
    have := key.2 _ _ hni u hu u' hu'
    show ipMT (R.MY 0) (ENNReal.ofReal (RealDat.nP F.lv2 b)⁻¹ • R.ν0) R.fd0 _ _ = 0
    unfold ipMT
    convert this using 2 <;> exact LinearEquiv.symm_apply_apply _ _

end GlobalTheory.Mem.R3.Rw.TypesRows
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RowFormLevelPrimesIsSplitSetStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.Col2
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rowFormLevelPrimes_isSplitSet : ∀ (X : Stages) (px : PreX X.B.toPre) (I : Col2.ColIn X.B px) (U : Set I.ι)
    (L : Formalism.IndefR.Links.LevCh X.toD7 (TupU I U)), I.Ok → LevOf X I U L →
    ∀ t : TupU I U, Formalism.L2.DIV.IsSplitSet (LiftBrg.sgL X I U t) := by
  first | exact @GlobalTheory.Mem.R3.LiftBrg.isSplitSet_sgL | exact GlobalTheory.Mem.R3.LiftBrg.isSplitSet_sgL | (intros; apply GlobalTheory.Mem.R3.LiftBrg.isSplitSet_sgL <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SectionPolynomialEqOfFunctionEqCoefficientStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sectionPolynomial_eq_of_function_eq_coefficient : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (Qp : I.ι → Finset ℕ) (O : ∀ u a, GL3Theta.LiftObj (I.rec7 l Z) ((I.rec7 l Z).chTw u a)), I.StdO l Z Qp O → ∀ (u : B.Word) (μ : I.ι) (i : ℕ), i < (I.rec7 l Z).R.m → ∀ (z : VV B.LL (lamT (B.hcW u) (i + 1))) (v' : ValQ O u μ (i + 1)), evC O u μ (i + 1) v' = evV B.fields.emb (1 : Matrix (Fin (B.R.N (i + 1))) (Fin (B.R.N (i + 1))) B.fields.E) (lamT (B.hcW u) (i + 1)) B.embLL z → ((secC O u μ (i + 1) v' : MvPolynomial (GL3Theta.FrV (I.rec7 l Z) ((I.rec7 l Z).R.N (i + 1))) (I.rec7 l Z).what₂.LL)) = (show MvPolynomial (GL3Theta.FrV (I.rec7 l Z) ((I.rec7 l Z).R.N (i + 1))) (I.rec7 l Z).what₂.LL from z.1) := by
  first | exact @GlobalTheory.Mem.Col2.PolyId.secC_eq_of_evC_eq_evV | exact GlobalTheory.Mem.Col2.PolyId.secC_eq_of_evC_eq_evV | (intros; apply GlobalTheory.Mem.Col2.PolyId.secC_eq_of_evC_eq_evV <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SplitPlaceEmbeddingAtOrbitPositionEqInducedStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.splitPlace_embedding_at_orbitPosition_eq_induced_alt : ∀ {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} (w : ColW B f T), K.Over B.toPre → Forced K B T → Pinned K B f T w →
    ∀ (Z : w.Lt) (t : ColumnDataSplitPrimes K w Z) (Wt : Set B.places.Pl) (nch : NChoice (w.D Z)) (_ : NchT w Z Wt nch) (Y : DivX (w.D Z)),
    V4.MuIsW (w.st Z) f T Wt w.I.xi → TC.QpIs w.I Y.Qp →
    ∀ (O : ∀ u a, GL3Theta.LiftObj (w.D Z) ((w.D Z).chTw u a)), TC.StdO w.I w.l Z Y.Qp O →
    (∀ u a i, i < B.R.m → Formalism.L2.Ker.UnfIsAll (O u a) i) → ∀ (E : KerEnt (w.D Z) Y (w.tw Z)), TC.EntOk E O →
    ∀ u (v : (w.D Z).what₂.places.Pl) (hg : GIdx (w.D Z).host ((w.D Z).mem u).A.T ((w.D Z).what₂.places.resChar v)),
      haveI : Fact ((w.D Z).what₂.places.resChar v).Prime := ⟨(w.D Z).what₂.places.resChar_prime v⟩
      ∀ (q : Fin ((w.D Z).gat u v hg).P.nV) (s : Fin (((w.D Z).gat u v hg).P.n' q)) (x : (w.D Z).host.E),
        ((w.D Z).gat u v hg).P.ι q ((((w.D Z).gat u v hg).P.σ q ^ s.val) (GlobalTheory.Mem.Top.KerOne.iw0 t.full.1.g u v hg q x)) =
          t.cmp.embW u v hg (tauLL (w.D Z) (t.Gt.gat_pos u v hg ⟨q, s⟩) (if s.val % 2 = 1 then (w.D Z).host.conj x else x)) := by
  first | exact @GlobalTheory.Mem.Top.KerOne.splitPlace_embedding_at_orbitPosition_eq_induced | exact GlobalTheory.Mem.Top.KerOne.splitPlace_embedding_at_orbitPosition_eq_induced | (intros; apply GlobalTheory.Mem.Top.KerOne.splitPlace_embedding_at_orbitPosition_eq_induced <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SupportDegreeEqOfMemWeightPolynomialsStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix Formalism.MainNotions.G Formalism.MainNotions.TaylorLogMetric
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.support_degree_eq_of_mem_weightPolynomials : ∀ {K : Type} [Field K] [CharZero K] {ι : Type} [Fintype ι] {n : ℕ} (ν : ι → Fin n → ℕ)
    (Q : MvPolynomial (ι × Fin n × Fin n) K) (hQ : Q ∈ WtPol K ν), ∀ e ∈ Q.support, ∀ τ, ∑ α, ∑ s, e (τ, α, s) = ∑ r, ν τ r := by
  first | exact @GlobalTheory.Mem.WtHomog.deg_eq_of_mem_wtPol | exact GlobalTheory.Mem.WtHomog.deg_eq_of_mem_wtPol | (intros; apply GlobalTheory.Mem.WtHomog.deg_eq_of_mem_wtPol <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SupportedUnitaryAdelicIntegralWithInverse
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.AdT Matrix
open scoped TensorProduct
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.Col2.AdT.IntSplit

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [StarRing E] {n : ℕ}

theorem val_entry_le {P : HeightOneSpectrum (𝓞 E)} {G : Sp E n ≃ₗ[E] Sp E n} (hG : G ∈ Formalism.L2.Col.GLint E n P) (i j : Fin n) :
    Valued.v (algebraMap E (P.adicCompletion E) (LinearMap.toMatrix' G.toLinearMap i j)) ≤ 1 := by
  have he : (Pi.single j 1 : Sp E n) ∈ Formalism.L2.Col.stdAt E n P := by
    refine Formalism.L2.Col.le_locP P _ ((mem_stdLat _).2 fun l => ?_)
    rw [Pi.single_apply]
    split_ifs
    exacts [⟨1, map_one _⟩, ⟨0, map_zero _⟩]
  have hGe : G (Pi.single j 1) ∈ Formalism.L2.Col.stdAt E n P := (hG (Pi.single j 1)).2 he
  have hint : Formalism.L2.Col.IntAt P (G (Pi.single j 1) i) := by
    obtain ⟨s, hs, hsx⟩ := (Formalism.L2.Col.mem_locP P _ _).1 hGe
    obtain ⟨r, hr⟩ := (mem_stdLat _).1 hsx i
    refine ⟨r, s, hs, ?_⟩
    rw [hr]
    simp [Algebra.smul_def]
  have e : LinearMap.toMatrix' G.toLinearMap i j = G (Pi.single j 1) i := by
    rw [LinearMap.toMatrix'_apply]
    congr 2
  rw [e]
  exact LevRead.hasRes_le (ReadBad.hasRes_redP hint)

theorem val_away {u : GL (Fin n) (AfE F E)} {v : HeightOneSpectrum (𝓞 F)}
    (hu : ∀ v', v' ≠ v → bc (prV (E := E) v') u = 1) {Q : HeightOneSpectrum (𝓞 E)} (hQ : ¬ Formalism.L2.Col.IsOver v Q) (i j : Fin n) :
    Valued.v (adAt F Q ((u : Matrix (Fin n) (Fin n) (AfE F E)) i j)) ≤ 1 := by
  have hne : Q.under (𝓞 F) ≠ v := fun e => hQ (e ▸ (rfl : Formalism.L2.Col.IsOver (Q.under (𝓞 F)) Q))
  have h1 : bc (prV (E := E) (Q.under (𝓞 F))) u = bc (prV (E := E) (Q.under (𝓞 F))) (1 : GL (Fin n) (AfE F E)) := by
    rw [map_one]; exact hu _ hne
  have h2 : adAt F Q ((u : Matrix (Fin n) (Fin n) (AfE F E)) i j) =
      adAt F Q (((1 : GL (Fin n) (AfE F E)) : Matrix (Fin n) (Fin n) (AfE F E)) i j) := by
    apply ChTwRead.adAt_congr_prV
    exact congrArg (fun g => g.1 i j) h1
  rw [h2, Units.val_one, Matrix.one_apply]
  split_ifs <;> simp

theorem inv_entry (hc : CMData F E) {u : GL (Fin n) (AfE F E)} (hu : u ∈ Formalism.L2.Herm.UstdAf hc n) (i j : Fin n) :
    ((u⁻¹ : GL (Fin n) (AfE F E)) : Matrix (Fin n) (Fin n) (AfE F E)) j i =
      sigR hc.sig (FiniteAdeleRing (𝓞 F) F) ((u : Matrix (Fin n) (Fin n) (AfE F E)) i j) := by
  have h := Opn.inv_eq_cT hc.sig (u := u) hu
  have h' := congrFun (congrFun h j) i
  refine h'.trans ?_
  unfold cT
  rw [Matrix.map_sub _ (map_sub _), Matrix.map_one _ (map_zero _) (map_one _), Matrix.transpose_sub, Matrix.transpose_one,
    add_sub_cancel]
  rfl

theorem adAt_inv {u : GL (Fin n) (AfE F E)} {P : HeightOneSpectrum (𝓞 E)} {g : Sp E n ≃ₗ[E] Sp E n}
    (h : ∀ r s, adAt F P ((u : Matrix (Fin n) (Fin n) (AfE F E)) r s) =
      algebraMap E (P.adicCompletion E) (LinearMap.toMatrix' g.toLinearMap r s)) (r s : Fin n) :
    adAt F P (((u⁻¹ : GL (Fin n) (AfE F E)) : Matrix (Fin n) (Fin n) (AfE F E)) r s) =
      algebraMap E (P.adicCompletion E) (LinearMap.toMatrix' (g⁻¹).toLinearMap r s) := by
  have e1 : (adAt F P).mapMatrix (u : Matrix (Fin n) (Fin n) (AfE F E)) =
      (algebraMap E (P.adicCompletion E)).mapMatrix (LinearMap.toMatrix' g.toLinearMap) := by
    exact Matrix.ext fun r s => h r s
  have e2 : (adAt F P).mapMatrix ((u⁻¹ : GL (Fin n) (AfE F E)) : Matrix (Fin n) (Fin n) (AfE F E)) *
      (adAt F P).mapMatrix (u : Matrix (Fin n) (Fin n) (AfE F E)) = 1 := by
    rw [← map_mul, Units.inv_mul, map_one]
  have e3 : (algebraMap E (P.adicCompletion E)).mapMatrix (LinearMap.toMatrix' g.toLinearMap) *
      (algebraMap E (P.adicCompletion E)).mapMatrix (LinearMap.toMatrix' (g⁻¹).toLinearMap) = 1 := by
    rw [← map_mul, ← LinearMap.toMatrix'_comp]
    have : g.toLinearMap ∘ₗ (g⁻¹).toLinearMap = LinearMap.id := by
      exact LinearMap.ext fun y => g.apply_symm_apply y
    rw [this, LinearMap.toMatrix'_id, map_one]
  rw [e1] at e2
  have e4 := left_inv_eq_right_inv e2 e3
  exact congrFun (congrFun e4 r) s

theorem int_of_supported : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [StarRing E] (hc : CMData F E) {n : ℕ} (u : GL (Fin n) (AfE F E)), u ∈ Formalism.L2.Herm.UstdAf hc n → ∀ (v : HeightOneSpectrum (𝓞 F)) (P : HeightOneSpectrum (𝓞 E)), Formalism.L2.Col.IsOver v P → (∀ v', v' ≠ v → bc (prV (E := E) v') u = 1) → ∀ g ∈ Formalism.L2.Col.GLint E n P, (∀ r s, adAt F P ((u : Matrix (Fin n) (Fin n) (AfE F E)) r s) = algebraMap E (P.adicCompletion E) (LinearMap.toMatrix' g.toLinearMap r s)) → ∀ i j, (u : Matrix (Fin n) (Fin n) (AfE F E)) i j ∈ RInt F E ∧ ((u⁻¹ : GL (Fin n) (AfE F E)) : Matrix (Fin n) (Fin n) (AfE F E)) i j ∈ RInt F E := by
  intro F E _ _ _ _ _ _ hc n u hu v P hv hsup g hg hcomp i j
  have hsup' : ∀ v', v' ≠ v → bc (prV (E := E) v') u⁻¹ = 1 := fun v' h => by rw [map_inv, hsup v' h, inv_one]
  have a1 : ∀ r s, Valued.v (adAt F P ((u : Matrix (Fin n) (Fin n) (AfE F E)) r s)) ≤ 1 := fun r s => by
    rw [hcomp]; exact val_entry_le hg r s
  have a2 : ∀ r s, Valued.v (adAt F P (((u⁻¹ : GL (Fin n) (AfE F E)) : Matrix (Fin n) (Fin n) (AfE F E)) r s)) ≤ 1 := fun r s => by
    rw [adAt_inv hcomp]; exact val_entry_le (inv_mem hg) r s
  refine ⟨(mem_rInt_iff F E _).2 fun Q => ?_, (mem_rInt_iff F E _).2 fun Q => ?_⟩
  · show Valued.v (adAt F Q _) ≤ 1
    by_cases hQ : Formalism.L2.Col.IsOver v Q
    · rcases rll_over_cases hc hv hQ with rfl | rfl
      · exact a1 i j
      · rw [← valued_sigR hc, ← inv_entry hc hu]
        exact a2 j i
    · exact val_away hsup hQ i j
  · show Valued.v (adAt F Q _) ≤ 1
    by_cases hQ : Formalism.L2.Col.IsOver v Q
    · rcases rll_over_cases hc hv hQ with rfl | rfl
      · exact a2 i j
      · rw [← valued_sigR hc, ← inv_entry hc (inv_mem hu), inv_inv]
        exact a1 j i
    · exact val_away hsup' hQ i j

end GlobalTheory.Mem.Col2.AdT.IntSplit

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WeylLatticeDualInvariantUnitIffStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weyl_lattice_dual_invariant_unit_iff : ∀ (p : ℕ) [Fact p.Prime] (T : Type) [Fintype T] (N : ℕ) (ν : T → Fin N → ℕ) (g : T → Matrix (Fin N) (Fin N) ℂ_[p]) (c : ℂ_[p]), (∀ τ a b, ‖g τ a b‖ ≤ 1) → (∀ τ, ‖(g τ).det‖ = 1) → ‖c‖ = 1 → ∀ F : (T → Matrix (Fin N) (Fin N) ℂ_[p]) → ℂ_[p], F ∈ WeylLatticeDuality.DelW p T N ν ↔ (fun y => c * F (fun τ => g τ * y τ)) ∈ WeylLatticeDuality.DelW p T N ν := by
  first | exact @GlobalTheory.DelWSub.delW_rowSub | exact GlobalTheory.DelWSub.delW_rowSub | (intros; apply GlobalTheory.DelWSub.delW_rowSub <;> assumption)
end

