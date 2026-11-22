import Mathlib
import Formalism.LocalToGlobal.KernelLattices.FirstKernelLawReading
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThetaDistributionUnfolded
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.FormsAre
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0081
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0102
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0103
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Bundle0002
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0104
import Formalism.LocalToGlobal.Columns.BaseLemmas
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.CharacterValueAtT
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsUnitaryCarries
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.MemZmuOfPowPred
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0091

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.PairKernelTermTargetStabiliserLaw
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker Formalism.L2.Forms Formalism.L2.Col Formalism.L2.DIV Formalism.HermitianLatticesTheory GlobalTheory.KerJ NumberField IsDedekindDomain Classical

namespace GlobalTheory.KerJ

open GlobalTheory.KerWt

theorem applyAt0_const_mul (D : D7) {N N' : ℕ} (P : MvPolynomial (GL3Theta.Idx D N N') ℂ) (k : ℂ) (G : TaylorLogMetric.VC D N N' → ℂ)
    (hG : Differentiable ℂ G) : GL3Theta.applyAt0 D P (fun z => k * G z) = k * GL3Theta.applyAt0 D P G := by
  exact (GlobalTheory.NormSum.applyAt0_minorPol_linear D N N' (fun _ => 0) G hG).2.2.1 k P

theorem applyAt0_polD_eigen (D : D7) (N N' : ℕ) (s : D.what₂.Tau → ℂ) (Q : MvPolynomial (GL3Theta.FrV D N) ℂ)
    (y' γ : D.what₂.Tau → Matrix (Fin N') (Fin N') ℂ) (G : TaylorLogMetric.VC D N N' → ℂ) (k : ℂ) (hγ : ∀ τ, (γ τ).det ≠ 0)
    (hG : Differentiable ℂ G) (hk : ∀ z : TaylorLogMetric.VC D N N', G (fun τ => (γ τ * Matrix.of (z τ) : Matrix _ _ ℂ)) = k * G z) :
    GL3Theta.applyAt0 D (GL3Theta.polD D s Q (fun τ => γ τ * y' τ)) G = k * GL3Theta.applyAt0 D (GL3Theta.polD D s Q y') G := by
  have h := GlobalTheory.ClassSumEquiv.applyAt0_polD_equivariant D N N' s Q y' γ (fun _ => 1) (fun z => k * G z) hγ (hG.const_mul k)
  have e1 : (fun z : TaylorLogMetric.VC D N N' => k * G (fun τ => ((γ τ)⁻¹ * Matrix.of (z τ) * (1 : Matrix (Fin N) (Fin N) ℂ) : Matrix (Fin N') (Fin N) ℂ))) = G := by
    funext z
    refine (hk _).symm.trans (congrArg G (funext fun τ => ?_))
    have : (γ τ * ((γ τ)⁻¹ * Matrix.of (z τ) * (1 : Matrix (Fin N) (Fin N) ℂ)) : Matrix (Fin N') (Fin N) ℂ) = Matrix.of (z τ) := by
      rw [Matrix.mul_one, Matrix.mul_nonsing_inv_cancel_left _ _ (hγ τ).isUnit]
    exact this
  have e2 : (MvPolynomial.aeval (fun k : GL3Theta.FrV D N => ∑ a : Fin N, MvPolynomial.C ((1 : Matrix (Fin N) (Fin N) ℂ) k.2.1 a) *
      (MvPolynomial.X (k.1, a, k.2.2) : MvPolynomial (GL3Theta.FrV D N) ℂ)) Q) = Q := by
    have : (fun k : GL3Theta.FrV D N => ∑ a : Fin N, MvPolynomial.C ((1 : Matrix (Fin N) (Fin N) ℂ) k.2.1 a) *
      (MvPolynomial.X (k.1, a, k.2.2) : MvPolynomial (GL3Theta.FrV D N) ℂ)) = MvPolynomial.X := by
      funext k
      rw [Finset.sum_eq_single k.2.1]
      · simp
      · intro b _ hb
        simp [Matrix.one_apply_ne hb.symm]
      · simp
    rw [this, MvPolynomial.aeval_X_left_apply]
  beta_reduce at h
  rw [e1, e2, applyAt0_const_mul D _ k G hG] at h
  exact h

theorem lawAt_Kmap : ∀ (D : D7) (u : D.what₂.Word) (C : ColumnChain D.R D.what₂.Tau (D.hcW u)) (A : ColumnsAtT D.R C) (Pm : PeriodMap D.R C) (M : MemberForms D.what₂.LL D.what₂.embLL D.what₂.places D.what₂.Tau (D.hcW u) C A Pm) (O : GL3Theta.LiftObj D C) (i : ℕ), i < D.R.m → UnfIs O i (nuT D u i) → ∀ (c : C.cls i) (c' : C.cls (i + 1)), Differentiable ℂ (O.Th i c c') → ∀ g, TermLaw O i c c' g → ∀ f, IsVal (O.frm i) (lamTG M i) (RingHom.id ℂ) f → LawAt O (i + 1) g (C.Kmap i c c' f) := by
  intro D u C A Pm M O i hi h c c' hd g ⟨hdet, k, hk, hg⟩ f ⟨P, hP, hf⟩ y y' hy
  obtain ⟨n, hw, hn, -, -⟩ := GlobalTheory.T.trueWeight_consecutive_steps_partition D u C A Pm M i hi
  have hs : C.sharp i f = frPoly O i (MvPolynomial.map (RingHom.id ℂ) P * ∏ τ, frDet ℂ (D.R.N i) τ ^ n τ) := by
    have h1 := mulFun_evG (fr := O.frm i) (fun y => (O.frm_range i hi.le _).1 ⟨y, rfl⟩) (RingHom.id ℂ) _ (C.sSharp i) n hn P
    have e1 : (fun y => ∏ τ, (O.frm i y τ).det ^ C.sSharp i τ) = fun y => ∏ τ, (C.de i y τ) ^ (C.sSharp i τ) := by
      funext y; simp only [O.frm_de i hi.le]
    rw [e1] at h1
    rw [hf]
    exact h1
  have hQ : MvPolynomial.map (RingHom.id ℂ) P * ∏ τ, frDet ℂ (D.R.N i) τ ^ n τ ∈ WtPol ℂ (nuT D u i) := by
    have h2 := vv_in_weight ℂ D.what₂.Tau _ (lamTG M i) n (MvPolynomial.map (RingHom.id ℂ) P) (map_mem_VV _ _ P hP)
    have e : (fun τ r => (lamTG M i τ).natW r + n τ) = nuT D u i := by funext τ r; exact hw τ r
    rwa [e] at h2
  generalize MvPolynomial.map (RingHom.id ℂ) P * ∏ τ, frDet ℂ (D.R.N i) τ ^ n τ = Q at hs hQ
  have hu : ∀ x : C.Y (i + 1), C.unf i c c' (C.sharp i f) x =
      GL3Theta.applyAt0 D (GL3Theta.polD D O.dgen Q (O.frm (i + 1) x)) (O.Th i c c') := fun x => by
    rw [hs]
    exact (unfolding_iff_alt D u C O i hi.le _).1 h c c' Q hQ x
  have hK : ∀ x : C.Y (i + 1), C.Kmap i c c' f x = (C.rhoDet i c * C.rhoDet' i c') *
      ((∏ τ, (O.frm (i + 1) x τ).det ^ C.sDiv i τ)⁻¹ *
        GL3Theta.applyAt0 D (GL3Theta.polD D O.dgen Q (O.frm (i + 1) x)) (O.Th i c c')) := fun x => by
    rw [← hu x]
    simp only [← O.frm_de (i + 1) hi]
    rfl
  have hdm : ∀ τ, (g.1.map (TaylorLogMetric.embT D τ)).det = TaylorLogMetric.embT D τ g.1.det := fun τ => ((TaylorLogMetric.embT D τ).map_det g.1).symm
  have hne : ∀ τ, (g.1.map (TaylorLogMetric.embT D τ)).det ≠ 0 := fun τ => by
    rw [hdm]; exact (map_ne_zero _).2 hdet
  have hy' : O.frm (i + 1) y = fun τ => g.1.map (TaylorLogMetric.embT D τ) * O.frm (i + 1) y' τ := funext hy
  rw [hK, hK, hy', applyAt0_polD_eigen D _ _ _ Q _ _ _ k hne hd hk, hg]
  simp only [Matrix.det_mul, hdm, mul_zpow, Finset.prod_mul_distrib, zpow_neg, Finset.prod_inv_distrib, mul_inv]
  ring

end GlobalTheory.KerJ
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.SplitChartUniformiserAndResidueCard
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.NTheta Formalism.IndefR.Datum IsDedekindDomain NumberField Matrix GlobalTheory.SplitHecke
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SplitUnif

section General

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (v : HeightOneSpectrum (𝓞 F)) (φ : E →+* v.adicCompletion F)

omit [NumberField E] [Algebra F E] in

theorem map_mem (x : 𝓞 E) : φ x ∈ v.adicCompletionIntegers F := by
  have h2 : IsIntegral (v.adicCompletionIntegers F) (φ x) :=
    IsIntegral.map_of_comp_eq (Int.castRingHom _) φ (RingHom.ext_int _ _) x.isIntegral_coe
  obtain ⟨y, hy⟩ := (IsIntegrallyClosed.isIntegral_iff (R := v.adicCompletionIntegers F)
    (K := v.adicCompletion F)).1 h2
  rw [← hy]
  exact y.2

theorem lt_one_iff (x : WithZero (Multiplicative ℤ)) : x < 1 ↔ x ≤ WithZero.exp (-1) := by
  rcases eq_or_ne x 0 with rfl | h
  · simp
  · rw [← WithZero.exp_log h, ← WithZero.exp_zero, WithZero.exp_lt_exp, WithZero.exp_le_exp]
    omega

theorem mem_max (x : v.adicCompletionIntegers F) :
    x ∈ IsLocalRing.maximalIdeal (v.adicCompletionIntegers F) ↔ Valued.v (x : v.adicCompletion F) < 1 :=
  Valuation.mem_maximalIdeal_iff (v := (Valued.v : Valuation (v.adicCompletion F) (WithZero (Multiplicative ℤ))))

theorem irreducible_of_valued (p : v.adicCompletionIntegers F)
    (hp : Valued.v (p : v.adicCompletion F) = WithZero.exp (-1)) : Irreducible p := by
  have hp0 : (p : v.adicCompletion F) ≠ 0 := by
    intro h
    rw [h, map_zero] at hp
    exact WithZero.exp_ne_zero hp.symm
  rw [IsDiscreteValuationRing.irreducible_iff_uniformizer]
  ext x
  rw [mem_max, lt_one_iff, Ideal.mem_span_singleton', ← hp]
  constructor
  · intro h
    refine ⟨⟨(x : v.adicCompletion F) / p, ?_⟩, Subtype.ext (div_mul_cancel₀ _ hp0)⟩
    show Valued.v ((x : v.adicCompletion F) / p) ≤ 1
    rw [map_div₀]
    exact div_le_one_of_le₀ h zero_le
  · rintro ⟨a, rfl⟩
    show Valued.v ((a : v.adicCompletion F) * p) ≤ _
    rw [map_mul]
    exact mul_le_of_le_one_left' a.2

variable (P : HeightOneSpectrum (𝓞 E))
  (hφ : ∀ t : F, φ (algebraMap F E t) = algebraMap F (v.adicCompletion F) t)
  (hP : ∀ x : 𝓞 E, x ∈ P.asIdeal ↔ Valued.v (φ x) < 1)

include hφ hP in
theorem valued_unif (ϖ : 𝓞 E) (h1 : ϖ ∈ P.asIdeal) (h2 : ϖ ∉ P.asIdeal ^ 2) :
    Valued.v (φ ϖ) = WithZero.exp (-1) := by
  refine le_antisymm ((lt_one_iff _).1 ((hP ϖ).1 h1)) ?_
  obtain ⟨t, ht⟩ := v.intValuation_exists_uniformizer
  let s : 𝓞 E := algebraMap (𝓞 F) (𝓞 E) t
  have hs : Valued.v (φ s) = WithZero.exp (-1) := by
    have e1 : (s : E) = algebraMap F E (algebraMap (𝓞 F) F t) := rfl
    have e2 : Valued.v (algebraMap F (v.adicCompletion F) (algebraMap (𝓞 F) F t)) =
        v.valuation F (algebraMap (𝓞 F) F t) := v.valuedAdicCompletion_eq_valuation' _
    rw [e1, hφ, e2, HeightOneSpectrum.valuation_of_algebraMap, ht]
  have hsP : s ∈ P.asIdeal := by rw [hP, lt_one_iff, hs]
  have hϖ0 : (ϖ : E) ≠ 0 := by
    intro h
    apply h2
    rw [show ϖ = 0 from Subtype.ext h]
    exact zero_mem _
  have hle : P.intValuation s ≤ P.intValuation ϖ := by
    have a1 := (P.intValuation_le_pow_iff_mem s 1).2 (by simpa using hsP)
    have a2 := mt (P.intValuation_le_pow_iff_mem ϖ 2).1 h2
    have a3 : P.intValuation ϖ ≠ 0 := P.intValuation_ne_zero ϖ (fun h => hϖ0 (by rw [h]; rfl))
    refine a1.trans ?_
    rw [← WithZero.exp_log a3, WithZero.exp_le_exp] at a2 ⊢
    push_cast at a2 ⊢
    omega
  have hx : P.valuation E ((s : E) / ϖ) ≤ 1 := by
    rw [map_div₀]
    refine div_le_one_of_le₀ ?_ zero_le
    rw [HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.valuation_of_algebraMap]
    exact hle
  obtain ⟨n, d, h⟩ := P.exists_primeCompl_mul_eq_of_integer _ hx
  have hd : Valued.v (φ ((d : 𝓞 E) : E)) = 1 :=
    le_antisymm (map_mem v φ d) (not_lt.1 (mt (hP d).2 d.2))
  have h3 : (s : E) * ((d : 𝓞 E) : E) = (n : E) * ϖ := by
    have h' : (s : E) / ϖ * ((d : 𝓞 E) : E) = (n : E) := h
    rw [← h']
    field_simp
  have h4 := congrArg (fun z => Valued.v (φ z)) h3
  simp only [map_mul] at h4
  rw [hd, mul_one, hs] at h4
  rw [h4]
  exact mul_le_of_le_one_left' (map_mem v φ n)

include hφ hP in
theorem card_residueField :
    Nat.card (IsLocalRing.ResidueField (v.adicCompletionIntegers F)) = Ideal.absNorm P.asIdeal := by
  let ψ : 𝓞 E →+* v.adicCompletionIntegers F :=
    (φ.comp (algebraMap (𝓞 E) E)).codRestrict _ (map_mem v φ)
  let χ : 𝓞 E →+* IsLocalRing.ResidueField (v.adicCompletionIntegers F) :=
    (IsLocalRing.residue _).comp ψ
  have hker : RingHom.ker χ = P.asIdeal := by
    ext x
    rw [RingHom.mem_ker, hP]
    show IsLocalRing.residue _ (ψ x) = 0 ↔ _
    rw [IsLocalRing.residue_eq_zero_iff, mem_max]
    rfl
  have hsurj : Function.Surjective χ := by
    intro y
    obtain ⟨x, rfl⟩ := IsLocalRing.residue_surjective y
    obtain ⟨r, hr⟩ := Formalism.UG.P.glint_exists_approx v x
    refine ⟨algebraMap (𝓞 F) (𝓞 E) r, ?_⟩
    show IsLocalRing.residue _ (ψ _) = _
    rw [eq_comm, ← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff, mem_max]
    have e1 : ((ψ (algebraMap (𝓞 F) (𝓞 E) r) : v.adicCompletionIntegers F) : v.adicCompletion F) =
        algebraMap (𝓞 F) (v.adicCompletion F) r := by
      rw [IsScalarTower.algebraMap_apply (𝓞 F) F (v.adicCompletion F), ← hφ]
      rfl
    rw [AddSubgroupClass.coe_sub, e1]
    exact hr
  rw [Ideal.absNorm_apply, Submodule.cardQuot_apply, ← hker]
  exact (Nat.card_congr (RingHom.quotientKerEquivOfSurjective hsurj).toEquiv).symm

end General

theorem unif_chart : ∀ {D : D7} (e : AE D) (P : HeightOneSpectrum (𝓞 D.host.E)) (v : HeightOneSpectrum (𝓞 D.host.F)) (π : AE D →+* Fv D.host.F v), IsIdemAt e P → Chart e v π → ∀ ϖ : 𝓞 D.host.E, ϖ ∈ P.asIdeal → ϖ ∉ P.asIdeal ^ 2 → (∃ p : Ov D v, algebraMap (Ov D v) (Fv D.host.F v) p = π (incA D (ϖ : D.host.E)) ∧ Irreducible p) ∧ Nat.card (IsLocalRing.ResidueField (Ov D v)) = Ideal.absNorm P.asIdeal := by
  intro D e P v π he hc ϖ h1 h2
  let φ : D.host.E →+* v.adicCompletion D.host.F := π.comp (incA D)
  have hφ : ∀ t : D.host.F, φ (algebraMap D.host.F D.host.E t) =
      algebraMap D.host.F (v.adicCompletion D.host.F) t := by
    intro t
    have e1 : incA D (algebraMap D.host.F D.host.E t) =
        algebraMap (AF D.host.F) (AE D) (algebraMap D.host.F (AF D.host.F) t) := by
      rw [← IsScalarTower.algebraMap_apply]
      exact (Algebra.TensorProduct.includeRight (R := D.host.F) (A := AF D.host.F) (B := D.host.E)).commutes t
    show π (incA D _) = _
    rw [e1, hc.2.2.1, AlgHom.commutes, AlgHom.commutes]
  have hP : ∀ x : 𝓞 D.host.E, x ∈ P.asIdeal ↔ Valued.v (φ x) < 1 := by
    intro x
    rcases eq_or_ne x 0 with rfl | hx
    · simp
    · have hx0 : Valued.v (φ x) ≠ 0 := by
        rw [Valuation.ne_zero_iff, map_ne_zero]
        exact fun h => hx (Subtype.ext h)
      rw [he.2 x hx, hc.2.2.2, isInt_Ov]
      show ¬ Valued.v (φ (x : D.host.E)⁻¹) ≤ 1 ↔ _
      rw [map_inv₀, map_inv₀, not_le, one_lt_inv₀ (zero_lt_iff.2 hx0)]
  exact ⟨⟨⟨φ ϖ, map_mem v φ ϖ⟩, rfl, irreducible_of_valued v _ (valued_unif v φ P hφ hP ϖ h1 h2)⟩,
    card_residueField v φ P hφ hP⟩

end GlobalTheory.SplitUnif

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.SubHalfRankInt
section
namespace GlobalTheory.ColPeriod

open Formalism.L2.Col Formalism.BasicNotions Formalism.L2.Ker
open GlobalTheory.IndefiniteRowSideFullHecke.SubstitutionAdjoint (WtCompat)

theorem sub_half_rank_int (R : Ranks) (z : ℤ) (j : ℕ) : ∃ a : ℤ, (z : ℚ) - (R.N j : ℚ) / 2 = a := by
  obtain ⟨a, ha⟩ := R.k_even
  obtain ⟨c, hc⟩ := R.t_odd
  unfold Ranks.N
  rw [ha, hc]
  exact ⟨z - a - (j : ℤ) * (c + 1), by push_cast; ring⟩

theorem chainWeights : ChainWeights := by
  intro X Pr R W u j hj
  have hs : ∀ τ : X.Tau, ∃ a : ℤ, sExp R ((W.hc u τ).e ⟨j, hj⟩) (j + 1) = a := by
    intro τ
    obtain ⟨z, hz⟩ := (W.hc u τ).e_int ⟨j, hj⟩
    rw [hz]
    exact sub_half_rank_int R z _
  have hs' : ∀ τ : X.Tau, ∃ a : ℤ, sExp' R ((W.hc u τ).e ⟨j, hj⟩) (j + 1) = a := by
    intro τ
    obtain ⟨z, hz⟩ := (W.hc u τ).e_int ⟨j, hj⟩
    rw [hz]
    exact sub_half_rank_int R z _
  choose s hs using hs
  choose s' hs' using hs'
  have hlt := N_lt_succ R j
  have h1 : ∀ τ (i : Fin (R.N j)),
      (W.lamTrue u (j + 1) τ).w (Fin.castLE hlt.le i) + s τ = (W.lamTrue u j τ).w i + s' τ := by
    intro τ i
    have h := W.lamTrue_old u hj τ (Fin.castLE hlt.le i) i.2
    rw [hs, hs'] at h
    have h' : (((W.lamTrue u (j + 1) τ).w (Fin.castLE hlt.le i) + s τ : ℤ) : ℚ) =
        (((W.lamTrue u j τ).w i + s' τ : ℤ) : ℚ) := by
      push_cast
      rw [h]
      simp
    exact_mod_cast h'
  have h2 : ∀ τ (i : Fin (R.N (j + 1))), R.N j ≤ (i : ℕ) → (W.lamTrue u (j + 1) τ).w i = -s τ := by
    intro τ i hi
    have h := W.lamTrue_new u hj τ i (by omega)
    rw [hs] at h
    exact_mod_cast h
  have h3 : ∀ (τ : X.Tau) (a : Fin (R.N j)), (W.lamTrue u j τ).w a + s' τ = (W.nuW u (j + 1) τ).w a := by
    intro τ a
    have h := W.nuW_eq_true u hj τ a
    rw [hs'] at h
    exact_mod_cast h.symm
  refine ⟨s, s', ⟨h1, h2, fun τ => ?_⟩, h3⟩
  have hpos : 0 < R.N j := R.N_pos j
  have e1 : (W.lamTrue u j τ).detShift = (W.lamTrue u j τ).w ⟨R.N j - 1, by omega⟩ := by
    unfold DomWeight.detShift
    rw [dif_pos hpos]
  have e2 : (W.nuW u (j + 1) τ).detShift = (W.nuW u (j + 1) τ).w (⟨R.N j - 1, by omega⟩ : Fin (R.N j)) := by
    unfold DomWeight.detShift
    exact dif_pos hpos
  have hge : 0 ≤ (W.lamTrue u j τ).w ⟨R.N j - 1, by omega⟩ + s' τ := by
    rw [← h1]
    have ha := (W.lamTrue u (j + 1) τ).anti
      (show Fin.castLE hlt.le (⟨R.N j - 1, by omega⟩ : Fin (R.N j)) ≤ ⟨R.N j, hlt⟩ from by
        rw [Fin.le_def]; simp)
    have hb := h2 τ ⟨R.N j, hlt⟩ le_rfl
    omega
  unfold nuLast
  rw [e1, e2, ← h3, Int.toNat_of_nonneg hge]

end GlobalTheory.ColPeriod
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ValLocCharUnit
section
noncomputable section

namespace GlobalTheory.ColPeriod.Scal

open NumberField IsDedekindDomain Formalism.L2.Col Formalism.HermitianLatticesTheory Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Ker
open GlobalTheory.IndefiniteRowSideFullHecke.CharacterValuation (StdOver IsFrames)

variable {X : Fields} {Pr : Primes X}

theorem g_mem_of_vG (hPr : Pr.Ok) {i : Fin 2} {P : HeightOneSpectrum (𝓞 X.E)} (h : P ∈ Pr.vG i) :
    ((Pr.g i : ℕ) : 𝓞 X.E) ∈ P.asIdeal := by
  rw [← hPr.piG_norm i]
  exact P.asIdeal.mul_mem_left _ (GlobalTheory.ColPeriod.mem_divs h)

theorem g_notMem_of_vGs (hPr : Pr.Ok) {i : Fin 2} {P : HeightOneSpectrum (𝓞 X.E)} (h : P ∈ Pr.vGs) (h' : P ∉ Pr.vG i) :
    ((Pr.g i : ℕ) : 𝓞 X.E) ∉ P.asIdeal := by
  classical
  have h2 : ∃ k, P ∈ Pr.vG k := by
    rcases Finset.mem_union.1 h with h2 | h2
    exacts [⟨0, h2⟩, ⟨1, h2⟩]
  obtain ⟨k, hk⟩ := h2
  have hne : Pr.g i ≠ Pr.g k := by
    have h0 := hPr.g_ne
    fin_cases i <;> fin_cases k
    · exact absurd hk h'
    · exact h0
    · exact h0.symm
    · exact absurd hk h'
  exact natCast_notMem_of_ne (hPr.g_prime i) (hPr.g_prime k) hne P (g_mem_of_vG hPr hk)

theorem under_conjP (hX : X.Ok) (Q : HeightOneSpectrum (𝓞 X.E)) :
    (conjPrime₂ Q).asIdeal.under (𝓞 X.F) = Q.asIdeal.under (𝓞 X.F) := by
  ext r
  have e : cO X.E (algebraMap (𝓞 X.F) (𝓞 X.E) r) = algebraMap (𝓞 X.F) (𝓞 X.E) r :=
    RingOfIntegers.ext (hX.star_F (r : X.F))
  rw [Ideal.under_def, Ideal.under_def, Ideal.mem_comap, Ideal.mem_comap, mem_conjP, e]

variable {sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)} {S : Set ℕ} {mu : Tup X.F X.E X.K S}

theorem g_notMem_sel (hX : X.Ok) (hPr : Pr.Ok) (hsel : IsSel X sel) {v : HeightOneSpectrum (𝓞 X.F)}
    (hv : ¬ ∃ P ∈ rowSG Pr sel mu, P.asIdeal.under (𝓞 X.F) = v.asIdeal) (k : Fin 2) :
    ((Pr.g k : ℕ) : 𝓞 X.E) ∉ (sel v).asIdeal := by
  classical
  intro h
  have hsub : ∀ Q, Q ∈ Pr.vG k → Q ∈ rowSG Pr sel mu := fun Q hQ => Finset.mem_union_left _ (by
    unfold Primes.vGs
    rw [Finset.mem_union]
    fin_cases k
    exacts [Or.inl hQ, Or.inr hQ])
  have h0 : X.conjO (Pr.piG k) ≠ 0 := by
    refine right_ne_zero_of_mul (a := Pr.piG k) ?_
    rw [hPr.piG_norm k]
    exact_mod_cast (hPr.g_prime k).ne_zero
  rw [← hPr.piG_norm k] at h
  rcases (sel v).isPrime.mem_or_mem h with h | h
  · refine hv ⟨conjPrime₂ (sel v), hsub _ ((Formalism.L2.Col.mem_divs h0 _).2 ?_), by rw [under_conjP hX, hsel v]⟩
    rw [mem_conjP]
    exact (cO_cO (Pr.piG k)).symm ▸ h
  · exact hv ⟨sel v, hsub _ ((Formalism.L2.Col.mem_divs h0 _).2 h), hsel v⟩

theorem val_locChar_unit {E K : Type} [Field E] [NumberField E] [Field K] [NumberField K] (w : HeightOneSpectrum (𝓞 K))
    (P : HeightOneSpectrum (𝓞 E)) (cq : K) (ψ : (𝓞 E ⧸ P.asIdeal)ˣ →* Kˣ) {a : E} (ha : P.valuation E a = 1) :
    w.valuation K (LocE.locChar (qOf P) cq ψ a) = 1 := by
  have hu := GlobalTheory.LocCharVal.isUnit_redP P _ ha
  have : Finite (𝓞 E ⧸ P.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot _ P.ne_bot
  rw [GlobalTheory.LastSteps.locChar_unit _ _ hu, LocE.unitV, dif_pos hu]
  exact GlobalTheory.CharVal.unit_of_finOrder (MonoidHom.isOfFinOrder ψ (isOfFinOrder_of_finite _))

theorem val_locChar {E K : Type} [Field E] [NumberField E] [Field K] [NumberField K] (w : HeightOneSpectrum (𝓞 K))
    (P : HeightOneSpectrum (𝓞 E)) {cq : K} (ψ : (𝓞 E ⧸ P.asIdeal)ˣ →* Kˣ) (hq : ((qOf P : ℕ) : 𝓞 E) ∉ P.asIdeal ^ 2)
    (hc : w.valuation K cq = 1) {a : E} (ha : a ≠ 0) : w.valuation K (LocE.locChar (qOf P) cq ψ a) = 1 := by
  obtain ⟨z, ζ, hζ, e⟩ := GlobalTheory.LocCharVal.locChar_eq_zpow_mul E K P (qOf P) cq ψ a
    (GlobalTheory.CharVal.val_natCast_of_notMem_sq (Ideal.absNorm_mem _) hq) ha
  rw [e, map_mul, map_zpow₀, hc, GlobalTheory.CharVal.unit_of_finOrder hζ, one_zpow, one_mul]

end GlobalTheory.ColPeriod.Scal

namespace GlobalTheory.ColPeriod

open NumberField IsDedekindDomain Formalism.L2.Col Formalism.HermitianLatticesTheory Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Ker Scal

theorem scalarUnit_of (hL : LevelPrimes) (hH : HeckeUnit) (hT : TwistUnit) : ScalarUnit := by
  intro X Pr R Ch sel S mu cst L G m2 e eta hX hPr hsel hS ht hOk i w hw j hj
  have hH' := hH X Pr R.m Ch G.σ₀ (e ⟨j, hj⟩) ⟨j, hj⟩ (G.mu0 ⟨j, hj⟩) hX hPr (ht.mu0 _) (Pr.g i) w
  have hval : ∀ P : HeightOneSpectrum (𝓞 X.E), (∀ k, ((Pr.g k : ℕ) : 𝓞 X.E) ∉ P.asIdeal) →
      w.valuation X.K (Ch.muVal ⟨j, hj⟩ P : X.K) = 1 := fun P hP =>
    hH' P (hPr.g_prime i) hw (hP i) (Formalism.L2.Host.unif P) _ (ht.muVal _ P hP)
  have h1 : ∀ P : rowSG Pr sel mu, P.1 ∉ Pr.vG i → w.valuation X.K (cst.muq (j + 1) P) = 1 := by
    intro P hPi
    have hq := (hT X.F X.E X.K S mu P.1 w).2
    obtain ⟨hd, hn⟩ := hL X Pr sel S mu hX hPr hsel P
    by_cases hP : P.1 ∈ Pr.vGs
    · have h1 := hOk.muqG j hj P hP (Units.mk0 _ (Proof.NormalFormAtPrime.qOf_ne_zero P.1)) rfl
      have h2 : G.σ₀ ((cst.muq (j + 1) P * ((qValC (mu : Chr X.F X.E X.K) P.1 : X.Kˣ) : X.K))⁻¹) =
          (((G.mu0 ⟨j, hj⟩).locK P.1 (Units.mk0 _ (Proof.NormalFormAtPrime.qOf_ne_zero P.1)) : ℂˣ) : ℂ) := by
        rw [map_inv₀, map_mul, h1, mul_assoc, ← map_mul, Units.inv_mul, map_one, mul_one, inv_inv]
      have h3 := hH' P.1 (hPr.g_prime i) hw (g_notMem_of_vGs hPr hP hPi) _ _ h2
      rwa [map_inv₀, map_mul, hq, mul_one, inv_eq_one] at h3
    · have hg : ∀ k, ((Pr.g k : ℕ) : 𝓞 X.E) ∉ P.1.asIdeal := fun k =>
        natCast_notMem_of_ne (hPr.g_prime k) hd.1 (fun h => hn hP (h ▸ hS k)) P.1 (Ideal.absNorm_mem _)
      rw [hOk.muqQ j hj P hP, Units.val_mul, Units.val_inv_eq_inv_val, Units.val_inv_eq_inv_val, map_mul, map_inv₀, map_inv₀,
        hq, hval _ hg]
      simp
  refine ⟨h1, fun n N fr _ hN hfr => ?_⟩
  have h2 : w.valuation X.K (muOff sel (rowSG Pr sel mu) (mUof Ch mu j) N) = 1 := by
    unfold muOff
    refine finprod_induction (fun x => w.valuation X.K x = 1) (map_one _)
      (fun x y hx hy => by rw [map_mul, hx, hy, one_mul]) fun v => ?_
    split_ifs with hv
    · exact map_one _
    · rw [Units.val_zpow_eq_zpow_val, map_zpow₀, mUof, dif_pos hj, Units.val_mul, Units.val_inv_eq_inv_val,
        Units.val_inv_eq_inv_val, map_mul, map_inv₀, map_inv₀, hval _ (g_notMem_sel hX hPr hsel hv),
        (hT X.F X.E X.K S mu _ w).1]
      simp
  rw [muInvDet, map_mul, h2, one_mul, map_prod]
  refine Finset.prod_eq_one fun P _ => ?_
  unfold muAt
  by_cases hP : P.1 ∈ Pr.vG i
  · refine val_locChar_unit w P.1 _ _ ?_
    rw [LinearEquiv.coe_det]
    refine GlobalTheory.StdReps.val_det_eq fun x => ?_
    rw [← hfr P x, hN P.1 (g_mem_of_vG hPr hP)]
  · exact val_locChar w P.1 _ (hL X Pr sel S mu hX hPr hsel P).1.2 (h1 P hP) (Units.ne_zero _)

end GlobalTheory.ColPeriod
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ValuationFinOrderApply
section
open NumberField IsDedekindDomain Formalism.L2.Col Formalism.HermitianLatticesTheory Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Ker

noncomputable section

namespace GlobalTheory.ColPeriod

theorem valuation_finOrder_apply {G K : Type} [Group G] [Field K] [NumberField K] (ξ : G →* Kˣ) (hξ : IsOfFinOrder ξ)
    (w : HeightOneSpectrum (𝓞 K)) (y : G) : w.valuation K ((ξ y : Kˣ) : K) = 1 := by
  obtain ⟨n, hn, h⟩ := isOfFinOrder_iff_pow_eq_one.1 hξ
  have h1 : (ξ y) ^ n = 1 := by
    have := congrArg (fun φ : G →* Kˣ => φ y) h
    simpa using this
  have h2 : (w.valuation K ((ξ y : Kˣ) : K)) ^ n = 1 := by
    rw [← map_pow, ← Units.val_pow_eq_pow_val, h1, Units.val_one, map_one]
  exact (pow_eq_one_iff_of_nonneg zero_le hn.ne').1 h2

theorem twistUnit : TwistUnit := by
  intro F E K _ _ _ _ _ _ _ S mu P w
  have hfin : IsOfFinOrder (mu : Chr F E K) := mu.2.1.1.1.2
  let v : HeightOneSpectrum (𝓞 F) := P.under (𝓞 F)
  have hv : P.asIdeal.under (𝓞 F) = v.asIdeal := rfl
  constructor
  · unfold unifVal
    split_ifs with h
    · obtain ⟨b, hb, hb2⟩ : ∃ b ∈ P.asIdeal, b ∉ P.asIdeal ^ 2 := by
        have := Ideal.exists_mem_pow_notMem_pow_succ P.asIdeal P.ne_bot P.isPrime.ne_top 1
        simpa using this
      obtain ⟨y, y₀, h1, h2, h3, h4⟩ := GlobalTheory.SuppIdele.exists_supported_idele F E P v b hv
      rw [← h.choose_spec v hv y y₀ b h1 hb hb2 h2 h3 h4]
      exact valuation_finOrder_apply _ hfin w y
    · simp
  · unfold qValC
    split_ifs with h
    · obtain ⟨y, y₀, h1, h2, h3, h4⟩ :=
        GlobalTheory.SuppIdele.exists_supported_idele F E P v ((Ideal.absNorm P.asIdeal : ℕ) : 𝓞 E) hv
      rw [← h.choose_spec v hv y y₀ h1 h2 h3 h4]
      exact valuation_finOrder_apply _ hfin w y
    · simp

end GlobalTheory.ColPeriod
end
end

