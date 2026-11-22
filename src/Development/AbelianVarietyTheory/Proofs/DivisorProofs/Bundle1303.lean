import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1286
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1217
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1275
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1267
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0049
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1236
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0024
import Development.AbelianVarietyTheory.Definitions.Divisors.SmallFam
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0014
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0016
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NontrivialIsomClassInt
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0043
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0013
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1268
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnitLemmaGroup
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0116
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0148
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0002
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0020
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsSmoothModerateOfIsAutFunSm
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0015
import Development.AbelianVarietyTheory.Proofs.HeightProofs.MemberDatumOfFlagTie
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsGloballyGeneratedIffGeneratingSections
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.EventuallySubsingletonCohTwistZOfIsProjOver
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsFiniteLengthOfIsArtinianRingAnnihilator
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.EventuallyExistsFiniteSubsetNonzeroLocus
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsLinearMapMultilinearMapBaseChange
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0229
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SupportPushforwardSubschemeSubset
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0317
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPowLeGlobalSectionsDimLineBundlePow
import Development.AbelianVarietyTheory.Definitions.Divisors.ToRingActOpOfRingAct
import Development.AbelianVarietyTheory.Definitions.Divisors.NonemptyHomFixRepTrivial
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VecMulMapEqZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1269
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1174

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HaarIntegralNormalizedOpenCompactEqFiniteLevelSu
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.BCT.HintLevel

theorem finsum_prod_fst {A T : Type} [Finite T] [Nonempty T] (f : A → ℂ) :
    ∑ᶠ x : A × T, f x.1 = (Nat.card T : ℂ) * ∑ᶠ a : A, f a := by
  by_cases hf : (Function.support f).Finite
  · have hg : (Function.support fun x : A × T => f x.1).Finite := by
      refine (hf.prod (Set.finite_univ (α := T))).subset ?_
      intro x hx
      exact ⟨hx, Set.mem_univ _⟩
    rw [finsum_curry _ hg, mul_finsum]
    refine finsum_congr fun a => ?_
    haveI := Fintype.ofFinite T
    rw [finsum_eq_sum_of_fintype]
    show ∑ _i : T, f a = _
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Nat.card_eq_fintype_card]
  · have hg : ¬ (Function.support fun x : A × T => f x.1).Finite := by
      intro hg
      apply hf
      refine (hg.image Prod.fst).subset ?_
      intro a ha
      exact ⟨(a, Classical.arbitrary T), ha, rfl⟩
    rw [finsum_of_infinite_support hg, finsum_of_infinite_support hf, mul_zero]

theorem sum_level (H : Type) [Group H] (S L : Subgroup H) (u : H → ℂ) (hLS : L ≤ S) (hS : S ≤ rStab u)
    (hfin : L.relIndex S ≠ 0) :
    ∑ᶠ q : H ⧸ L, u q.out = ((L.relIndex S : ℕ) : ℂ) * ∑ᶠ p : H ⧸ S, u p.out := by
  have hinv : ∀ g : H, u ((QuotientGroup.mk g : H ⧸ S).out) = u g := by
    intro g
    obtain ⟨k, hk⟩ := QuotientGroup.mk_out_eq_mul S g
    rw [hk]
    exact hS k.2 g
  have hfst : ∀ q : H ⧸ L, u q.out = u ((Subgroup.quotientEquivProdOfLE hLS q).1.out) := by
    intro q
    have : (Subgroup.quotientEquivProdOfLE hLS q).1 = (QuotientGroup.mk q.out : H ⧸ S) := by
      simp only [Subgroup.quotientEquivProdOfLE, Subgroup.quotientEquivProdOfLE']
      conv_lhs => rw [← QuotientGroup.out_eq' q]
      rfl
    rw [this, hinv]
  haveI : Finite (S ⧸ L.subgroupOf S) := Subgroup.index_ne_zero_iff_finite.1 hfin
  rw [finsum_congr hfst, finsum_comp_equiv (Subgroup.quotientEquivProdOfLE hLS)
    (f := fun x : (H ⧸ S) × (S ⧸ L.subgroupOf S) => u x.1.out)]
  exact finsum_prod_fst (fun p : H ⧸ S => u p.out)

theorem hint_level : ∀ (H : Type) [Group H] (K L : Subgroup H) (u : H → ℂ), L ≤ K → L ≤ rStab u →
    L.relIndex K ≠ 0 → hint K u = ((L.relIndex K : ℕ) : ℂ)⁻¹ * ∑ᶠ q : H ⧸ L, u q.out := by
  intro H _ K L u hLK hLu hne
  have hLS : L ≤ rStab u ⊓ K := le_inf hLu hLK
  have hmul := Subgroup.relIndex_mul_relIndex L (rStab u ⊓ K) K hLS inf_le_right
  have h1 : L.relIndex (rStab u ⊓ K) ≠ 0 := by
    intro h0; apply hne; rw [← hmul, h0, zero_mul]
  have h2 : (rStab u ⊓ K).relIndex K ≠ 0 := by
    intro h0; apply hne; rw [← hmul, h0, mul_zero]
  rw [sum_level H (rStab u ⊓ K) L u hLS inf_le_left h1, hint, ← hmul]
  push_cast
  have h1' : ((L.relIndex (rStab u ⊓ K) : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.2 h1
  field_simp

end GlobalTheory.BCT.HintLevel
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasSumSu21RankOneSeriesDifferences
section
open MeasureTheory GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.SatakeBound GlobalTheory.WeylCell Formalism.UG GlobalTheory.WeylCell.WeylUnipotentShell

namespace GlobalTheory.SURankOneSeries

theorem term_even (q z : ℂ) (hq : q ≠ 0) (i : ℕ) :
    (z / q ^ 2) ^ (2 * i) * q ^ (2 * i + 2 * (2 * i / 2)) = (z ^ 2) ^ i := by
  have h : 2 * i / 2 = i := by omega
  rw [h, div_pow, ← pow_mul, show 2 * i + 2 * i = 2 * (2 * i) by ring, ← pow_mul]
  field_simp

theorem term_odd (q z : ℂ) (hq : q ≠ 0) (i : ℕ) :
    (z / q ^ 2) ^ (2 * i + 1) * q ^ (2 * i + 1 + 2 * ((2 * i + 1) / 2)) = z / q * (z ^ 2) ^ i := by
  have h : (2 * i + 1) / 2 = i := by omega
  rw [h]
  have h4 : 2 * i + 1 + 2 * i = 2 * (2 * i) + 1 := by ring
  rw [h4]
  simp only [div_pow, ← pow_mul]
  rw [show 2 * (2 * i + 1) = (2 * (2 * i) + 1) + 1 by ring, pow_succ q (2 * (2 * i) + 1)]
  field_simp
  ring

theorem hasSum_weighted (q z : ℂ) (hq : q ≠ 0) (hz : ‖z‖ < 1) :
    HasSum (fun j : ℕ => (z / q ^ 2) ^ j * q ^ (j + 2 * (j / 2))) ((1 + q⁻¹ * z) / (1 - z ^ 2)) := by
  have hz2 : ‖z ^ 2‖ < 1 := by
    rw [norm_pow]; nlinarith [norm_nonneg z]
  have hg := hasSum_geometric_of_norm_lt_one hz2
  have he : HasSum (fun k : ℕ => (z / q ^ 2) ^ (2 * k) * q ^ (2 * k + 2 * (2 * k / 2))) (1 - z ^ 2)⁻¹ := by
    have : (fun k : ℕ => (z / q ^ 2) ^ (2 * k) * q ^ (2 * k + 2 * (2 * k / 2))) = fun k => (z ^ 2) ^ k :=
      funext fun k => term_even q z hq k
    rw [this]; exact hg
  have ho : HasSum (fun k : ℕ => (z / q ^ 2) ^ (2 * k + 1) * q ^ (2 * k + 1 + 2 * ((2 * k + 1) / 2)))
      (z / q * (1 - z ^ 2)⁻¹) := by
    have : (fun k : ℕ => (z / q ^ 2) ^ (2 * k + 1) * q ^ (2 * k + 1 + 2 * ((2 * k + 1) / 2))) =
        fun k => z / q * (z ^ 2) ^ k := funext fun k => term_odd q z hq k
    rw [this]; exact hg.mul_left _
  have h1 : (1 : ℂ) - z ^ 2 ≠ 0 := by
    intro h
    have : z ^ 2 = 1 := by linear_combination -h
    have : ‖z ^ 2‖ = 1 := by rw [this, norm_one]
    linarith
  have e : (1 - z ^ 2)⁻¹ + z / q * (1 - z ^ 2)⁻¹ = (1 + q⁻¹ * z) / (1 - z ^ 2) := by
    field_simp
  rw [← e]
  exact HasSum.even_add_odd (f := fun j : ℕ => (z / q ^ 2) ^ j * q ^ (j + 2 * (j / 2))) he ho

theorem hasSum_series : ∀ (q : ℕ), 2 ≤ q → ∀ z : ℂ, ‖z‖ < 1 →
    HasSum (fun j : ℕ => (z / (q : ℂ) ^ 2) ^ j *
      ((q : ℂ) ^ (j + 2 * (j / 2)) - (if j = 0 then 0 else (q : ℂ) ^ (j - 1 + 2 * ((j - 1) / 2))))) (cSU q z) := by
  intro q hq z hz
  have hq0 : (q : ℂ) ≠ 0 := by exact_mod_cast (by omega : q ≠ 0)
  have hA := hasSum_weighted (q : ℂ) z hq0 hz
  set w : ℂ := z / (q : ℂ) ^ 2 with hw
  set S : ℂ := (1 + (q : ℂ)⁻¹ * z) / (1 - z ^ 2) with hS
  set a : ℕ → ℂ := fun j => w ^ j * (q : ℂ) ^ (j + 2 * (j / 2)) with ha
  set b : ℕ → ℂ := fun j => if j = 0 then 0 else w * a (j - 1) with hb
  have hB : HasSum b (w * S) := by
    refine (hasSum_nat_add_iff' 1).mp ?_
    have e : (fun n => b (n + 1)) = fun n => w * a n := by
      funext n; simp [hb]
    rw [e]
    simpa [hb] using hA.mul_left w
  have hfun : (fun j : ℕ => w ^ j *
      ((q : ℂ) ^ (j + 2 * (j / 2)) - (if j = 0 then 0 else (q : ℂ) ^ (j - 1 + 2 * ((j - 1) / 2))))) =
      fun j => a j - b j := by
    funext j
    rcases j with _ | n
    · simp [ha, hb]
    · simp only [ha, hb, Nat.succ_ne_zero, if_false, Nat.add_sub_cancel]
      rw [pow_succ]; ring
  rw [hfun]
  have h1 : (1 : ℂ) - z ^ 2 ≠ 0 := by
    intro h
    have : z ^ 2 = 1 := by linear_combination -h
    have : ‖z ^ 2‖ = 1 := by rw [this, norm_one]
    rw [norm_pow] at this
    nlinarith [norm_nonneg z]
  have e : cSU (q : ℂ) z = S - w * S := by
    rw [cSU, hS, hw]
    field_simp
  rw [e]
  exact hA.sub hB

end GlobalTheory.SURankOneSeries
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeCharCMEtaLocalEqNegOnePowValInertStatement
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heckeCharCM_eta_local_eq_neg_one_pow_val_inert : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ μ : HChar E,
    (∀ x, μ.1 (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.ideleMap (maximalRealSubfield E) E x) = (GlobalTheory.GalOfCusp.quadChar E).1 x) →
    (∀ (w : HeightOneSpectrum (𝓞 E)) (u : (w.adicCompletion E)ˣ), ¬ IsSplitAt w → Valued.v (u : w.adicCompletion E) = 1 →
      μ.1 (Neutral.B1.localIdele E w u) = 1) →
    ∀ w : Pl E, ¬ IsSplitAt w → μ.loc w = GlobalTheory.SmGL.unrChar (w.adicCompletion E) (-1) := by
  first | exact @GlobalTheory.MuInert.loc_eq_unrChar_neg_one | exact GlobalTheory.MuInert.loc_eq_unrChar_neg_one | (intros; apply GlobalTheory.MuInert.loc_eq_unrChar_neg_one <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermLBLeBySmallSectionTensorIsometricTransShift
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef GlobalTheory.CechPic GlobalTheory.Points GlobalTheory.ChartGlue

namespace GlobalTheory.HSNef

variable {k : Type} [CommRing k] {X : Scheme.{0}} [IsIntegral X] {p : X ⟶ Sp k}

theorem norm_mul_exp_neg_log_normSq {u : ℂ} (hu : u ≠ 0) :
    ‖u‖ * Real.exp (-Real.log (‖u‖ ^ 2) / 2) = 1 := by
  have h : 0 < ‖u‖ := norm_pos_iff.2 hu
  rw [Real.log_pow, show -((2 : ℕ) * Real.log ‖u‖) / 2 = -Real.log ‖u‖ by push_cast; ring,
    Real.exp_neg, Real.exp_log h, mul_inv_cancel₀ h.ne']

theorem ratSec_div_eq {L : LB X} {r : L.ι → X.functionFieldˣ} (hr : IsRatSec L r) {i j : L.ι}
    (h : genericPoint X ∈ L.U i ⊓ L.U j) :
    (r i : X.functionField) / (r j : X.functionField) = fnOf _ h (L.g i j : Γ(X, L.U i ⊓ L.U j)) := by
  rw [hr i j h, mul_div_cancel_right₀ _ (r j).ne_zero]

theorem regAt_ratSec_div {L : LB X} {r : L.ι → X.functionFieldˣ} (hr : IsRatSec L r) {i j : L.ι} {x : X}
    (hi : x ∈ L.U i) (hj : x ∈ L.U j) : RegAt x ((r i : X.functionField) / (r j : X.functionField)) := by
  rw [ratSec_div_eq hr (gen_mem (memInf hi hj))]
  exact regAt_fnOf (memInf hi hj) _ _

theorem ratVal_ratSec_div {σ : k →+* ℂ} {L : LB X} {r : L.ι → X.functionFieldˣ} (hr : IsRatSec L r) {i j : L.ι}
    {y : CxPts p σ} (hi : y ∈ ptsIn p σ (L.U i)) (hj : y ∈ ptsIn p σ (L.U j)) :
    ratVal ((r i : X.functionField) / (r j : X.functionField)) y = gv p σ L i j y := by
  have hy := mem_ptsIn_inf.2 ⟨hi, hj⟩
  rw [ratSec_div_eq hr (gen_mem (mem_ptsIn.1 hy)), ratVal_fnOf hy]
  rfl

theorem norm_ratSec_div {σ : k →+* ℂ} {L : LB X} (φ : Weight p σ L) {r : L.ι → X.functionFieldˣ} (hr : IsRatSec L r)
    {i j : L.ι} {y : CxPts p σ} (hi : y ∈ ptsIn p σ (L.U i)) (hj : y ∈ ptsIn p σ (L.U j)) :
    ‖ratVal ((r i : X.functionField) / (r j : X.functionField)) y‖ * Real.exp (-(φ.φ i y - φ.φ j y) / 2) = 1 := by
  rw [ratVal_ratSec_div hr hi hj, φ.trans i j y hi hj, sub_sub_cancel]
  exact norm_mul_exp_neg_log_normSq (gv_ne_zero hi hj)

end GlobalTheory.HSNef

namespace GlobalTheory.HSNef

variable {k : Type} [CommRing k] {X : Scheme.{0}} [IsIntegral X] {p : X ⟶ Sp k}

theorem Le.shift {A B : HermLB p} (t : ℝ) (h : Le B A) :
    Le (B.shift (fun _ => t) fun _ => rfl) (A.shift (fun _ => t) fun _ => rfl) := by
  obtain ⟨r, r', hr, hr', hreg, hn⟩ := (GlobalTheory.T.hermLBLeBySmallSection_iff_localQuotients k X p A B).1 h
  refine (GlobalTheory.T.hermLBLeBySmallSection_iff_localQuotients k X p _ _).2 ⟨r, r', hr, hr', hreg, fun σ y i j hi hj => ?_⟩
  have e : ((A.shift (fun _ => t) fun _ => rfl).φ σ).φ i y - ((B.shift (fun _ => t) fun _ => rfl).φ σ).φ j y =
      (A.φ σ).φ i y - (B.φ σ).φ j y := by
    simp only [HermLB.shift, Weight.addFn]; ring
  rw [e]
  exact hn σ y i j hi hj

theorem Le.trans {A B M : HermLB p} (h₁ : Le B A) (h₂ : Le A M) : Le B M := by
  obtain ⟨r₁, r₁', hr₁, hr₁', hreg₁, hn₁⟩ := (GlobalTheory.T.hermLBLeBySmallSection_iff_localQuotients k X p A B).1 h₁
  obtain ⟨r₂, r₂', hr₂, hr₂', hreg₂, hn₂⟩ := (GlobalTheory.T.hermLBLeBySmallSection_iff_localQuotients k X p M A).1 h₂
  obtain ⟨a₀, h₀⟩ := exists_chart A.isLB (genericPoint X)
  let c : X.functionFieldˣ := r₂' a₀ / r₁ a₀
  have hs : IsRatSec B.B fun j => r₁' j * c := fun i j h => by
    simp only [Units.val_mul]
    rw [hr₁' i j h, mul_assoc]
  have key (a : A.B.ι) (ha : genericPoint X ∈ A.B.U a) (i : M.B.ι) (j : B.B.ι) :
      (r₂ i : X.functionField) / ((r₁' j * c : X.functionFieldˣ) : X.functionField) =
        (r₂ i : X.functionField) / (r₂' a : X.functionField) * ((r₁ a : X.functionField) / (r₁' j : X.functionField)) := by
    have e₁ := hr₁ a a₀ (memInf ha h₀)
    have e₂ := hr₂' a a₀ (memInf ha h₀)
    have n₁ := (r₁ a₀).ne_zero
    have n₂ := (r₂' a₀).ne_zero
    have n₃ := (r₂' a).ne_zero
    have n₄ := (r₁' j).ne_zero
    simp only [c, Units.val_mul, Units.val_div_eq_div_val]
    rw [div_mul_div_comm, div_eq_div_iff (mul_ne_zero n₄ (div_ne_zero n₂ n₁)) (mul_ne_zero n₃ n₄), e₁, e₂]
    field_simp
  refine (GlobalTheory.T.hermLBLeBySmallSection_iff_localQuotients k X p M B).2 ⟨r₂, _, hr₂, hs, fun x i j hi hj => ?_, fun σ y i j hi hj => ?_⟩
  · obtain ⟨a, ha⟩ := exists_chart A.isLB x
    rw [key a (gen_mem ha)]
    exact (hreg₂ x i a hi ha).mul (hreg₁ x a j ha hj)
  · have ha := mem_pick (A.φ σ).isLB y
    set a := pick (A.φ σ).isLB y
    have hx := mem_ptsIn.1 ha
    rw [key a (gen_mem hx), ratVal_mul (hreg₂ _ i a (mem_ptsIn.1 hi) hx) (hreg₁ _ a j hx (mem_ptsIn.1 hj)), norm_mul]
    have e : -((M.φ σ).φ i y - (B.φ σ).φ j y) / 2 =
        -((M.φ σ).φ i y - (A.φ σ).φ a y) / 2 + -((A.φ σ).φ a y - (B.φ σ).φ j y) / 2 := by ring
    rw [e, Real.exp_add]
    calc _ = (‖ratVal ((r₂ i : X.functionField) / (r₂' a : X.functionField)) y‖ *
          Real.exp (-((M.φ σ).φ i y - (A.φ σ).φ a y) / 2)) *
        (‖ratVal ((r₁ a : X.functionField) / (r₁' j : X.functionField)) y‖ *
          Real.exp (-((A.φ σ).φ a y - (B.φ σ).φ j y) / 2)) := by ring
      _ ≤ 1 := mul_le_one₀ (hn₂ σ y i a hi ha) (by positivity) (hn₁ σ y a j ha hj)

end GlobalTheory.HSNef

namespace GlobalTheory.HSNef

variable {k : Type} [CommRing k] {X : Scheme.{0}} [IsIntegral X] {p : X ⟶ Sp k}

theorem Le.tens {A B : HermLB p} (M : HermLB p) (h : Le B A) : Le (M.tens B) (M.tens A) := by
  obtain ⟨r, r', hr, hr', hreg, hn⟩ := (GlobalTheory.T.hermLBLeBySmallSection_iff_localQuotients k X p A B).1 h
  obtain ⟨ρ, hρ⟩ := exists_isRatSec M.isLB
  have hs := ((presents_divOfRatSec M.isLB hρ).tens (presents_divOfRatSec A.isLB hr)).isRatSec
  have hs' := ((presents_divOfRatSec M.isLB hρ).tens (presents_divOfRatSec B.isLB hr')).isRatSec
  have key (c : M.B.ι × A.B.ι) (d : M.B.ι × B.B.ι) :
      ((ρ c.1 * r c.2 : X.functionFieldˣ) : X.functionField) / ((ρ d.1 * r' d.2 : X.functionFieldˣ) : X.functionField) =
        (ρ c.1 : X.functionField) / (ρ d.1 : X.functionField) * ((r c.2 : X.functionField) / (r' d.2 : X.functionField)) := by
    rw [Units.val_mul, Units.val_mul, mul_div_mul_comm]
  refine (GlobalTheory.T.hermLBLeBySmallSection_iff_localQuotients k X p (M.tens A) (M.tens B)).2 ⟨fun c => ρ c.1 * r c.2, fun d => ρ d.1 * r' d.2, hs, hs',
    fun x c d hc hd => ?_, fun σ y c d hc hd => ?_⟩
  · beta_reduce
    erw [key c d]
    exact (regAt_ratSec_div hρ hc.1 hd.1).mul (hreg x c.2 d.2 hc.2 hd.2)
  · have hc' := mem_ptsIn_inf.1 hc
    have hd' := mem_ptsIn_inf.1 hd
    beta_reduce
    erw [key c d]
    rw [ratVal_mul (regAt_ratSec_div hρ (mem_ptsIn.1 hc'.1) (mem_ptsIn.1 hd'.1))
      (hreg _ c.2 d.2 (mem_ptsIn.1 hc'.2) (mem_ptsIn.1 hd'.2)), norm_mul]
    have e : -(((M.tens A).φ σ).φ c y - ((M.tens B).φ σ).φ d y) / 2 =
        -((M.φ σ).φ c.1 y - (M.φ σ).φ d.1 y) / 2 + -((A.φ σ).φ c.2 y - (B.φ σ).φ d.2 y) / 2 := by
      simp only [HermLB.tens, Weight.tens]; ring
    rw [e, Real.exp_add]
    calc _ = (‖ratVal ((ρ c.1 : X.functionField) / (ρ d.1 : X.functionField)) y‖ *
          Real.exp (-((M.φ σ).φ c.1 y - (M.φ σ).φ d.1 y) / 2)) *
        (‖ratVal ((r c.2 : X.functionField) / (r' d.2 : X.functionField)) y‖ *
          Real.exp (-((A.φ σ).φ c.2 y - (B.φ σ).φ d.2 y) / 2)) := by ring
      _ ≤ 1 := by
        rw [norm_ratSec_div (M.φ σ) hρ hc'.1 hd'.1, one_mul]
        exact hn σ y c.2 d.2 hc'.2 hd'.2

end GlobalTheory.HSNef

namespace GlobalTheory.HSNef

variable {k : Type} [CommRing k] {X : Scheme.{0}} [IsIntegral X] {p : X ⟶ Sp k}

theorem le_of_isometric {A B : HermLB p} (hi : B.Isometric A) : Le B A := by
  classical
  obtain ⟨w, hw, h⟩ := hi.exists_units
  obtain ⟨r, hr⟩ := exists_isRatSec B.isLB
  obtain ⟨b₀, h₀⟩ := exists_chart B.isLB (genericPoint X)
  let F (U : X.Opens) (u : Γ(X, U)ˣ) : X.functionFieldˣ := gm (𝟙 X) (genericPoint X) U u
  have hF (U : X.Opens) (u : Γ(X, U)ˣ) (hU : genericPoint X ∈ U) : (F U u : X.functionField) = fnOf U hU u.val :=
    gm_val (𝟙 X) _ U hU u
  have hw' (a a' b b') (h₁ : genericPoint X ∈ A.B.U a) (h₂ : genericPoint X ∈ A.B.U a')
      (h₃ : genericPoint X ∈ B.B.U b) (h₄ : genericPoint X ∈ B.B.U b') :
      F _ (w a b) = F _ (A.B.g a a') * (F _ (B.B.g b b'))⁻¹ * F _ (w a' b') :=
    hw _ (𝟙 X) _ a a' b b' h₁ h₂ h₃ h₄
  have hM (a) (h₁ : genericPoint X ∈ A.B.U a) : F _ (A.B.g a a) = 1 := gm_self A.isLB (𝟙 X) _ h₁
  have hL : F _ (B.B.g b₀ b₀) = 1 := gm_self B.isLB (𝟙 X) _ h₀
  have hr' : IsRatSec A.B fun a => F _ (w a b₀) * r b₀ := fun a a' h' => by
    beta_reduce
    rw [← hF, ← Units.val_mul, hw' a a' b₀ b₀ h'.1 h'.2 h₀ h₀, hL, inv_one, mul_one, mul_assoc]
  have key (a b) (h' : genericPoint X ∈ A.B.U a ⊓ B.B.U b) :
      ((F _ (w a b₀) * r b₀ : X.functionFieldˣ) : X.functionField) / (r b : X.functionField) = fnOf _ h' (w a b).val := by
    rw [div_eq_iff (r b).ne_zero, ← hF, hr b b₀ (memInf h'.2 h₀), ← hF _ (B.B.g b b₀), ← Units.val_mul, ← Units.val_mul,
      hw' a a b b₀ h'.1 h'.1 h'.2 h₀, hM a h'.1, one_mul, mul_comm (F _ (B.B.g b b₀))⁻¹, mul_assoc,
      inv_mul_cancel_left]
  refine (GlobalTheory.T.hermLBLeBySmallSection_iff_localQuotients k X p A B).2 ⟨_, r, hr', hr, fun x a b ha hb => ?_, fun σ y a b ha hb => ?_⟩
  · beta_reduce
    rw [key a b (gen_mem (memInf ha hb))]
    exact regAt_fnOf (memInf ha hb) _ _
  · have hab := mem_ptsIn_inf.2 ⟨ha, hb⟩
    beta_reduce
    rw [key a b (gen_mem (mem_ptsIn.1 hab)), ratVal_fnOf hab, h σ a b y ha hb, add_sub_cancel_left, logSq,
      norm_mul_exp_neg_log_normSq (ev_ne_zero hab (Units.isUnit _))]

theorem le_tens_isometric_trans_shift : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k),
    ∀ A B M : HermLB p, (Le B A → Le (M.tens B) (M.tens A)) ∧ (B.Isometric A → Le B A) ∧ (Le B A → Le A M → Le B M) ∧
      ∀ t : ℝ, Le B A → Le (B.shift (fun _ => t) fun _ => rfl) (A.shift (fun _ => t) fun _ => rfl) :=
  fun _ _ _ _ _ _ _ _ => ⟨Le.tens _, le_of_isometric, Le.trans, fun t => Le.shift t⟩

end GlobalTheory.HSNef
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermPairPowSectionMemAndNormPowStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermPair_pow_section_mem_and_norm_pow : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (P : Pair p), ∀ (a b : ℤ) (f : X.functionField), f ∈ P.H a b → ∀ n : ℕ, f ^ n ∈ P.H (n * a) (n * b) ∧ ∀ (σ : k →+* ℂ) (y : CxPts p σ), P.nu (n * a) (n * b) σ y (f ^ n) = P.nu a b σ y f ^ n := by
  first | exact @GlobalTheory.VolBr.NuPow.pow_mem_H_and_nu_pow | exact GlobalTheory.VolBr.NuPow.pow_mem_H_and_nu_pow | (intros; apply GlobalTheory.VolBr.NuPow.pow_mem_H_and_nu_pow <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianFormDetUnitAndTwistStatement
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermitian_form_det_unit_and_twist : ∀ (K : GlobalTheory.UnitLemma.UQ) (B : GlobalTheory.UnitLemma.InvAlg K) (L : Type) [Field L] (e : K.E ≃+* L) (c : L →+* L), (∀ x, e (K.c x) = c (e x)) → (∀ x, c (c x) = x) → ∀ (a : ℕ) (Q : L[X]), B.P = Q.map e.symm.toRingHom → Q.Separable → Q.natDegree = a → ∀ β : B.Aˣ, B.σ (β : B.A) = β * ((-1) ^ (a - 1) * B.g) → ∀ b : Module.Basis (Fin a) K.E B.A, IsUnit (Matrix.of fun i j => e (B.herm β (b i) (b j))).det ∧ ∀ δ : GL (Fin a) L, ((δ.val * GlobalTheory.Tw.Phi a L)⁻¹)ᵀ = (Matrix.of fun i j => e (B.herm β (b i) (b j))) → (δ * thetaGL a c δ).val.charpoly = Q := by
  first | exact @GlobalTheory.GramTwistNorm.gram_twisted_norm_charpoly | exact GlobalTheory.GramTwistNorm.gram_twisted_norm_charpoly | (intros; apply GlobalTheory.GramTwistNorm.gram_twisted_norm_charpoly <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianWittFrameColumnsLeWittIndex
section
open scoped Matrix NNReal ENNReal TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.WittIdxBound

theorem witt_frame_le_wittIdx : ∀ (D : D7) (V : HSp D) (r : ℕ) (X Y : Matrix (Fin V.rank) (Fin r) D.host.E),
    GlobalTheory.SiegelSet.IsWittFrame D.sp.cm.sig V.gram X Y → r ≤ Formalism.MainNotions.SchurIrreducible.wittIdx V := by
  intro D V r X Y h
  obtain ⟨ev, hev⟩ := GlobalTheory.BesselCompare.eMat_surj V X
  obtain ⟨ev', hev'⟩ := GlobalTheory.BesselCompare.eMat_surj V Y
  have hiso : ∀ a b, V.hT (ev a) (ev b) = 0 := fun a b => by
    rw [← GlobalTheory.BesselCompare.cT_mul, hev]
    exact congrFun (congrFun h.xx a) b
  have hpair : ∀ i j, V.hT (ev i) (ev' j) = if i = j then 1 else 0 := fun i j => by
    rw [← GlobalTheory.BesselCompare.cT_mul, hev, hev', h.xy]
    simp [Matrix.one_apply]
  have hli : LinearIndependent D.host.E ev := by
    rw [Fintype.linearIndependent_iff]
    intro c hc j
    have h1 := congrArg (fun v => V.hT v (ev' j)) hc
    simp only [map_sum, LinearMap.sum_apply, LinearMap.map_smulₛₗ, LinearMap.smul_apply, hpair, smul_eq_mul,
      mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true, map_zero, LinearMap.zero_apply] at h1
    simpa using h1
  have hmem : ∀ x ∈ Submodule.span D.host.E (Set.range ev), ∃ c : Fin r → D.host.E, ∑ i, c i • ev i = x :=
    fun x hx => (Submodule.mem_span_range_iff_exists_fun D.host.E).1 hx
  unfold Formalism.MainNotions.SchurIrreducible.wittIdx
  apply le_csSup
  · refine ⟨Module.finrank D.host.E V.V, ?_⟩
    rintro k ⟨W, rfl, -⟩
    exact Submodule.finrank_le W
  · refine ⟨Submodule.span D.host.E (Set.range ev), ?_, ?_⟩
    · rw [finrank_span_eq_card hli, Fintype.card_fin]
    · intro x hx y hy
      obtain ⟨c, rfl⟩ := hmem x hx
      obtain ⟨d, rfl⟩ := hmem y hy
      simp [map_sum, LinearMap.sum_apply, LinearMap.map_smulₛₗ, LinearMap.smul_apply, hiso]

end GlobalTheory.WittIdxBound
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HigherCohomologyTwistBoundOfRegularSectionStatement
section
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter Asymptotics
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Twist
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.higherCohomology_twist_bound_of_regular_section : ∀ (k : Type) [Field k] [Infinite k] (X : Scheme.{0}) [Algebra k Γ(X, ⊤)], IsProjOver (strHom k X) → ∀ (d : ℕ) (L : LB X) (hL : L.IsLB), (∀ (E : X.Modules) [IsFiniteQC E], suppDim E ≤ (d : ℕ) → ∀ j, 0 < j → (∃ C : ℕ, ∀ m : ℕ, hdim k (twist E (lbPow L m)) j ≤ C * (d * (m + 1) ^ (d - 1)))) → ∀ (F : X.Modules) [IsFiniteQC F], suppDim F ≤ (d + 1 : ℕ) → ∀ p : ℕ, 1 ≤ p → ∀ s : (lbPow L p).Sec, Mono (cutHom F (isLB_lbPow hL p) s) → ∀ i, 0 < i → (∃ C : ℕ, ∀ m : ℕ, hdim k (twist F (lbPow L m)) i ≤ C * ((d + 1) * (m + 1) ^ d)) := by
  first | exact @GlobalTheory.hdim_twist_pow_le_of_regular_section | exact GlobalTheory.hdim_twist_pow_le_of_regular_section | (intros; apply GlobalTheory.hdim_twist_pow_le_of_regular_section <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HigherCohomologyTwistBoundOfTwoCutsStatement
section
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter Asymptotics
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Twist
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.higherCohomology_twist_bound_of_two_cuts : ∀ (k : Type) [Field k] [Infinite k] (X : Scheme.{0}) [Algebra k Γ(X, ⊤)], IsProjOver (strHom k X) → ∀ (d : ℕ) (L : LB X), L.IsLB → (∀ (E : X.Modules) [IsFiniteQC E], suppDim E ≤ (d : ℕ) → ∀ j, 0 < j → (∃ C : ℕ, ∀ m : ℕ, hdim k (twist E (lbPow L m)) j ≤ C * (d * (m + 1) ^ (d - 1)))) → ∀ (F : X.Modules) [IsFiniteQC F], suppDim F ≤ (d + 1 : ℕ) → ∀ i, 2 ≤ i → (∃ C : ℕ, ∀ m : ℕ, hdim k (twist F (lbPow L m)) i ≤ C * ((d + 1) * (m + 1) ^ d)) := by
  first | exact @GlobalTheory.hdim_twist_lbPow_le_of_two_le | exact GlobalTheory.hdim_twist_lbPow_le_of_two_le | (intros; apply GlobalTheory.hdim_twist_lbPow_le_of_two_le <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HomFixedPullbackRepresentableGlueOpenCoverStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.homFixedPullbackRepresentable_glue_openCover : ∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (A B : Over S) [GrpObj A] [IsCommMonObj A] [GrpObj B] [IsCommMonObj B] (L : LB A.left) (M : LB B.left), IsAbelianScheme A → IsAbelianScheme B → L.IsLB → M.IsLB → Out.Rigidified A L → Out.Rigidified B M → ∀ (J : Type) (U : J → S.Opens), (∀ p : S, ∃ i, p ∈ U i) → (∀ i, ∃ (AU : Over (U i).toScheme) (_ : GrpObj AU) (BU : Over (U i).toScheme) (_ : GrpObj BU) (φA : AU.left ⟶ A.left) (φB : BU.left ⟶ B.left), IsGrpPullback AU A (U i).ι φA ∧ IsGrpPullback BU B (U i).ι φB ∧ ∃ R : HomFixRep AU BU (L.pull φA) (M.pull φB), QuasiCompact R.π ∧ IsSeparated R.π ∧ LocallyOfFiniteType R.π) → ∃ R : HomFixRep A B L M, QuasiCompact R.π ∧ IsSeparated R.π ∧ LocallyOfFiniteType R.π := by
  first | exact @GlobalTheory.homFixRep_glue_opens | exact GlobalTheory.homFixRep_glue_opens | (intros; apply GlobalTheory.homFixRep_glue_opens <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdealCountUnderExtensionStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.CM GlobalTheory.FlatDegreeCompare
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ideal_count_under_extension : ∀ (E : Type) [Field E] [NumberField E] (k k' : Type) [Field k] [NumberField k] [Field k'] [NumberField k'] (i : k →+* k') (τ : E →+* k) (𝔞 : Ideal (𝓞 E)) (𝔭 : HeightOneSpectrum (𝓞 k)) (𝔓 : HeightOneSpectrum (𝓞 k')) (ε : ℕ), (∀ z : k, 𝔓.valuation k' (i z) = 𝔭.valuation k z ^ ε) → FractionalIdeal.count k' 𝔓 ((𝔞.map (RingOfIntegers.mapRingHom (i.comp τ)) : Ideal (𝓞 k')) : FractionalIdeal (nonZeroDivisors (𝓞 k')) k') = ε * FractionalIdeal.count k 𝔭 ((𝔞.map (RingOfIntegers.mapRingHom τ) : Ideal (𝓞 k)) : FractionalIdeal (nonZeroDivisors (𝓞 k)) k) := by
  first | exact @GlobalTheory.count_map_comp_ideal_eq_mul_of_valuation_pow | exact GlobalTheory.count_map_comp_ideal_eq_mul_of_valuation_pow | (intros; apply GlobalTheory.count_map_comp_ideal_eq_mul_of_valuation_pow <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InertPlaceKernelSignEqEtaGramDetStatement
section
open NumberField GlobalTheory.UnitaryBC IsDedekindDomain Matrix Polynomial GlobalTheory.CuspRep Formalism.UG GlobalTheory.BCT GlobalTheory.KapLat
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.inertPlace_kernelSign_eq_eta_gramDet : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (w : Pl E), ¬ IsSplitAt w → ∀ (K : GlobalTheory.UnitLemma.UQ) (e : K.E ≃+* w.adicCompletion E), Bridge w K e → ∀ (n : ℕ) (Q₁ Q₂ : (w.adicCompletion E)[X]) (B₁ B₂ : GlobalTheory.UnitLemma.InvAlg K) (u₁ : B₁.A) (u₂ : B₂.A), (Q₁ * Q₂).Separable → Fits w e B₁ Q₁ u₁ → Fits w e B₂ Q₂ u₂ → ∀ (x : (B₁.prod B₂).A) (γ : GLw n w), IsModel w e (B₁.prod B₂) ((u₁, u₂) : B₁.A × B₂.A) x γ → kapSign n w Q₁ γ = ((K.eta (B₁.gramDet x.1) : ℚ) : ℂ) := by
  first | exact @GlobalTheory.KapLat.kapSign_eq_eta_gramDet | exact GlobalTheory.KapLat.kapSign_eq_eta_gramDet | (intros; apply GlobalTheory.KapLat.kapSign_eq_eta_gramDet <;> assumption)
end

