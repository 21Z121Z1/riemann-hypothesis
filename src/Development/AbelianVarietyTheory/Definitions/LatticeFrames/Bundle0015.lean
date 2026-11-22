import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0012
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.SqNormIntegralFundamentalDomainEqL2NormSq
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0006
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0002
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0103
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0055
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0166
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0252
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0216
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IdempotentMulEqZeroOfOrthogonal
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0072
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0083
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0045
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsContinuousPadic
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0070
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0076
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0206
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0112
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowsJoinPinned
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0032
import Formalism.LocalToGlobal.IndefiniteReal.LinksLemmas
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0011
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0013

-- bundled from Development.AbelianVarietyTheory.Definitions.LatticeFrames.RealSizeNonneg
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped ENNReal

namespace GlobalTheory.Unf

variable {D : D7}

def realSize (θ : InfFam D) {m n : ℕ} (x : Mx D m n) : ℝ := ∑ τ, ∑ i, ∑ j, ‖compAt θ τ x i j‖

def InBox {m n : ℕ} (K : Set (Mx D m n)) (x : Mx D m n) : Prop := ∃ k ∈ K, (x - k).map (finPart D) = 0

open Classical in

def maj (θ : InfFam D) {m n : ℕ} (K : Set (Mx D m n)) (N : ℕ) (x : Mx D m n) : ℝ :=
  if InBox K x then ((1 + realSize θ x) ^ N)⁻¹ else 0

def supSob (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) {S T : HSp D} (d : ℕ) (f : WO S T → ℂ) : ℝ≥0∞ :=
  GlobalTheory.Size.wordSum (GlobalTheory.Size.heisDer ψ θ) (fun φ : WO S T → ℂ => ⨆ w, ‖φ w‖ₑ) d f

structure IsSobForm (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (ℓ : (WO S T → ℂ) → ℂ) : Prop where
  add : ∀ f g, IsThetaFunO ψ S T f → IsThetaFunO ψ S T g → ℓ (f + g) = ℓ f + ℓ g
  smul : ∀ (c : ℂ) f, IsThetaFunO ψ S T f → ℓ (c • f) = c * ℓ f
  bound : ∀ U : AddSubgroup (WO S T), IsOpen (U : Set (WO S T)) → ∃ (d : ℕ) (C : NNReal),
    ∀ f ∈ GlobalTheory.Size.thetaLevel ψ S T U, ‖ℓ f‖ₑ ≤ C * supSob ψ θ d f

theorem realSize_nonneg (θ : InfFam D) {m n : ℕ} (x : Mx D m n) : 0 ≤ realSize θ x :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _

theorem maj_nonneg (θ : InfFam D) {m n : ℕ} (K : Set (Mx D m n)) (N : ℕ) (x : Mx D m n) : 0 ≤ maj θ K N x := by
  unfold maj
  split_ifs
  · have := realSize_nonneg θ x; positivity
  · exact le_rfl

theorem isSobForm_eval (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) : IsSobForm ψ θ S T fun f => f 0 where
  add _ _ _ _ := rfl
  smul _ _ _ := rfl
  bound _ _ := ⟨0, 1, fun f _ => by
    rw [ENNReal.coe_one, one_mul]
    exact le_trans (le_iSup (fun w => ‖f w‖ₑ) 0)
      (GlobalTheory.Size.le_wordSum (A := GlobalTheory.Size.heisDer ψ θ) (p := fun φ : WO S T → ℂ => ⨆ w, ‖φ w‖ₑ) (l := []) le_rfl f)⟩

end GlobalTheory.Unf

end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.LatticeFrames.RecHeightSWith
section
noncomputable section

namespace GlobalTheory.CoreHt

open NumberField Formalism.BasicNotions Formalism.MainNotions

def HtRowsS {D : D7} (L : SizeData₂ D) (CY : ℝ) : Prop :=
  Nonempty (ParameterChoice' D L) ∧
  (Real.log D.host.rdE ≤ L.sc.L ∧ |L.logDerivativeAtOne| ≤ L.sc.L ∧ Real.log (4 * L.sc.x) ≤ L.sc.L) ∧
  (∀ i, Real.log (D.host.g i) ≤ CY * L.sc.L + 1) ∧
  (4 * (D.R.N D.R.m : ℝ) ^ 3 ≤ L.etaSz ∧ (D.R.t : ℝ) ≤ L.etaSz ∧
    (D.R.m : ℝ) * ((D.R.t : ℝ) + 1) * L.etaSz ≤ L.sc.w'' D.R.n ∧ (D.R.k : ℝ) * L.Sc ≤ L.sc.w'' D.R.n ∧
    ∀ t, (L.bT t : ℝ) ≤ 2 * L.sc.b') ∧
  DelNat D ∧ ThickUp L

def hRecS {D : D7} (L : SizeData₂ D) (u : D.what₂.Word) (c : ℝ) : ℝ :=
  DV.SZbP D L c u + (∑ j ∈ SizeData₂.lifts D, DV.kernelPlaceMeanBound D L c u j) +
    c * (((D.host.TT.card : ℝ) * L.sc.b' +
      (D.R.f : ℝ) * (L.Sc + (D.R.m : ℝ) * L.etaSz + (D.R.N D.R.m : ℝ)) +
      (D.R.f : ℝ) * (D.R.m : ℝ) ^ 3 * (D.R.N D.R.m : ℝ) ^ 2) * Real.log ((D.mem u).A.T : ℝ))

def RecHeightSWith (CY c : ℝ) : Prop :=
  ∀ (D : D7) (L : SizeData₂ D) (u : D.what₂.Word), OverTC D L.sc.a → HtRowsS L CY → (∀ v, IsUnit ((D.div.Nu u).X v).det) →
    GlobalTheory.Core.HtLe (D.div.Nu u) (GlobalTheory.Core.Rk.Pt D u) (GlobalTheory.Core.Rk.Psi D u) (hRecS L u c)

def RecHeightS : Prop := ∀ CY : ℝ, ∃ c : ℝ, 0 ≤ c ∧ RecHeightSWith CY c

end GlobalTheory.CoreHt
end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.LatticeFrames.ReflectionBoostMatrixConjTransposeMulSelf
section
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil ValuativeRel
open scoped TensorProduct Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.SplitHalf

section Gen
variable {X : Type} [AddCommGroup X] [TopologicalSpace X] [IsTopologicalAddGroup X]

theorem exists_inv (Φ : SB X) (A : AddSubgroup X) (hA : IsCompact (A : Set X)) :
    ∃ N : ℕ, 0 < N ∧ ∀ a ∈ A, ∀ x, Φ.1 (x + N • a) = Φ.1 x := by
  let V : AddSubgroup X :=
    { carrier := {v | ∀ x, Φ.1 (x + v) = Φ.1 x}
      zero_mem' := fun x => by rw [add_zero]
      add_mem' := fun {a b} ha hb x => by rw [← add_assoc, hb, ha]
      neg_mem' := fun {a} ha x => by rw [← ha (x + -a), neg_add_cancel_right] }
  have key : ∀ᶠ v in 𝓝 (0 : X), ∀ x ∈ tsupport Φ.1, Φ.1 (x + v) = Φ.1 x := by
    refine IsCompact.eventually_forall_of_forall_eventually Φ.2.2 fun x _ => ?_
    have h1 : IsLocallyConstant fun p : X × X => (Φ.1 (p.2 + p.1), Φ.1 p.2) :=
      (Φ.2.1.comp_continuous (continuous_snd.add continuous_fst)).prodMk (Φ.2.1.comp_continuous continuous_snd)
    filter_upwards [h1.eventually_eq (0, x)] with p hp
    rw [Prod.mk.injEq, add_zero] at hp
    rw [hp.1, hp.2]
  have key' : ∀ᶠ v in 𝓝 (0 : X), ∀ x ∈ tsupport Φ.1, Φ.1 (x + -v) = Φ.1 x :=
    (continuous_neg.tendsto' (0 : X) 0 neg_zero).eventually key
  have hV : IsOpen (V : Set X) := by
    refine V.isOpen_of_mem_nhds (g := 0) ?_
    filter_upwards [key, key'] with v h1 h2 x
    by_cases hx : x ∈ tsupport Φ.1
    · exact h1 x hx
    · by_cases hv : x + v ∈ tsupport Φ.1
      · rw [← h2 _ hv, add_neg_cancel_right]
      · rw [image_eq_zero_of_notMem_tsupport hx, image_eq_zero_of_notMem_tsupport hv]
  haveI : DiscreteTopology (X ⧸ V) := QuotientAddGroup.discreteTopology hV
  have hfin : ((A.map (QuotientAddGroup.mk' V) : AddSubgroup (X ⧸ V)) : Set (X ⧸ V)).Finite := by
    rw [AddSubgroup.coe_map]
    exact (hA.image QuotientAddGroup.continuous_mk).finite_of_discrete
  haveI : Finite (A.map (QuotientAddGroup.mk' V)) := hfin
  refine ⟨Nat.card (A.map (QuotientAddGroup.mk' V)), Nat.card_pos, fun a ha => ?_⟩
  have h := card_nsmul_eq_zero' (x := (⟨QuotientAddGroup.mk' V a, a, ha, rfl⟩ : A.map (QuotientAddGroup.mk' V)))
  have h2 := congrArg Subtype.val h
  simp only [AddSubgroup.coe_nsmul, ZeroMemClass.coe_zero, ← map_nsmul] at h2
  exact (QuotientAddGroup.eq_zero_iff _).1 h2

theorem exists_supp {K : Set X} (hK : IsCompact K) (A : AddSubgroup X) (hA : IsOpen (A : Set X))
    (h : ∀ x, ∃ n : ℕ, 0 < n ∧ n • x ∈ A) : ∃ N : ℕ, 0 < N ∧ ∀ x ∈ K, N • x ∈ A := by
  obtain ⟨s, hs⟩ := hK.elim_finite_subcover (fun n : ℕ+ => {x | (n : ℕ) • x ∈ A})
    (fun n => hA.preimage (continuous_nsmul _)) fun x _ => by
      obtain ⟨n, hn, hx⟩ := h x
      exact Set.mem_iUnion.2 ⟨⟨n, hn⟩, hx⟩
  refine ⟨∏ n ∈ s, (n : ℕ), Finset.prod_pos fun n _ => n.pos, fun x hx => ?_⟩
  obtain ⟨n, hn, hx⟩ := Set.mem_iUnion₂.1 (hs hx)
  obtain ⟨m, hm⟩ := Finset.dvd_prod_of_mem (fun n : ℕ+ => (n : ℕ)) hn
  rw [hm, mul_nsmul]
  exact nsmul_mem hx _

end Gen

variable {D : D7}

theorem chart_one {e : AE D} (h1 : e * e = e) {v : HeightOneSpectrum (𝓞 D.host.F)}
    {π : AE D →+* Fv D.host.F v} (hπ : GlobalTheory.SplitHecke.Chart e v π) : π e = 1 := by
  have : π (e - 1) = 0 := (hπ.2.1 _).2 (by rw [mul_sub, h1, mul_one, sub_self])
  rwa [RingHom.map_sub, RingHom.map_one, sub_eq_zero] at this

theorem chart_cont {e : AE D} (he : IsSplitIdem D e) {v : HeightOneSpectrum (𝓞 D.host.F)}
    {π : AE D →+* Fv D.host.F v} (hπ : GlobalTheory.SplitHecke.Chart e v π) : Continuous π := by
  obtain ⟨h1, h2, -⟩ := he
  have tA : ∀ z : AE D, algebraMap (AF D.host.F) (AE D) (Algebra.trace (AF D.host.F) (AE D) z) = z + cA D z :=
    GlobalTheory.FockCompare.SymplVal.trace_tensor D.sp.cm.deg2 D.sp.cm.sig (fun e => star_star e)
    (fun e he => (D.sp.cm.fixed e).1 he) (AF D.host.F)
  have ht : Continuous (Algebra.trace (AF D.host.F) (AE D)) := IsModuleTopology.continuous_of_linearMap _
  have hc : Continuous fun x : AE D => Algebra.trace (AF D.host.F) (AE D) (e * x) :=
    ht.comp (continuous_const.mul continuous_id)
  have hev : Continuous fun y : AF D.host.F => evalV D.host.F v (sndA D.host.F y) :=
    (RestrictedProduct.continuous_eval v).comp continuous_snd
  refine (hev.comp hc).congr fun x => ?_
  have h4 : π (cA D (e * x)) = 0 := (hπ.2.1 _).2 (by rw [RingHom.map_mul, ← mul_assoc, h2, zero_mul])
  have h5 := hπ.2.2.1 (Algebra.trace (AF D.host.F) (AE D) (e * x))
  rw [tA, RingHom.map_add, h4, add_zero, RingHom.map_mul, chart_one h1 hπ, one_mul] at h5
  exact h5.symm

theorem single_add {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) (a b : Fv F v) :
    singleV F v (a + b) = singleV F v a + singleV F v b := by
  refine RestrictedProduct.ext _ _ fun w => ?_
  change evalV F w (singleV F v (a + b)) = evalV F w (singleV F v a + singleV F v b)
  by_cases hw : w = v
  · subst hw
    rw [map_add, GlobalTheory.SplitCoord.evalV_single, GlobalTheory.SplitCoord.evalV_single, GlobalTheory.SplitCoord.evalV_single]
  · rw [map_add, GlobalTheory.SplitCoord.evalV_single_ne hw, GlobalTheory.SplitCoord.evalV_single_ne hw,
      GlobalTheory.SplitCoord.evalV_single_ne hw, add_zero]

def sec (e : AE D) (v : HeightOneSpectrum (𝓞 D.host.F)) : Fv D.host.F v →+ AE D :=
  AddMonoidHom.mk' (fun a => e * algebraMap (AF D.host.F) _ (pairA D.host.F 0 (singleV D.host.F v a))) fun a b => by
    rw [← mul_add, ← RingHom.map_add, single_add]
    congr 2
    exact Prod.ext (add_zero _).symm rfl

theorem sec_cont (e : AE D) (v : HeightOneSpectrum (𝓞 D.host.F)) : Continuous (sec e v) := by
  have ha : Continuous (Algebra.linearMap (AF D.host.F) (AE D)) := IsModuleTopology.continuous_of_linearMap _
  have hb : Continuous fun a => pairA D.host.F 0 (singleV D.host.F v a) :=
    Continuous.prodMk continuous_const (GlobalTheory.LocalComponentChar.continuous_singleV D.host.F v)
  exact continuous_const.mul (ha.comp hb)

theorem chart_sec {e : AE D} (h1 : e * e = e) {v : HeightOneSpectrum (𝓞 D.host.F)}
    {π : AE D →+* Fv D.host.F v} (hπ : GlobalTheory.SplitHecke.Chart e v π) (a) : π (sec e v a) = a := by
  change π (e * algebraMap (AF D.host.F) _ (pairA D.host.F 0 (singleV D.host.F v a))) = a
  rw [RingHom.map_mul, chart_one h1 hπ, one_mul, hπ.2.2.1]
  exact GlobalTheory.SplitCoord.evalV_single v a

theorem sec_chart {e : AE D} (h1 : e * e = e) {v : HeightOneSpectrum (𝓞 D.host.F)}
    {π : AE D →+* Fv D.host.F v} (hπ : GlobalTheory.SplitHecke.Chart e v π) (x) : sec e v (π x) = e * x := by
  have := (hπ.2.1 (sec e v (π x) - x)).1 (by rw [RingHom.map_sub, chart_sec h1 hπ, sub_self])
  rw [mul_sub, sub_eq_zero] at this
  rw [← this]
  change e * _ = e * (e * _)
  rw [← mul_assoc, h1]

theorem exists_idem (D : D7) : ∃ e, IsSplitIdem D e := by
  have h2 : ¬ IsUnit (2 : 𝓞 D.host.F) := by
    intro hu
    have hn := hu.map (Algebra.norm ℤ (S := 𝓞 D.host.F))
    rw [show (2 : 𝓞 D.host.F) = algebraMap ℤ (𝓞 D.host.F) 2 by simp, Algebra.norm_algebraMap,
      isUnit_pow_iff Module.finrank_pos.ne'] at hn
    rcases Int.isUnit_iff.mp hn with h | h <;> omega
  obtain ⟨M, hM, h2M⟩ := Ideal.exists_le_maximal (Ideal.span {(2 : 𝓞 D.host.F)})
    (by rwa [Ne, Ideal.span_singleton_eq_top])
  have hm : (2 : 𝓞 D.host.F) ∈ M := h2M (Ideal.mem_span_singleton_self 2)
  have hM0 : M ≠ ⊥ := by
    rintro rfl
    exact two_ne_zero ((Submodule.mem_bot _).mp hm)
  obtain ⟨e, a, b, c, -⟩ := GlobalTheory.SplitIdem.exists_split_idempotent D ⟨M, hM.isPrime, hM0⟩ hm
  exact ⟨e, a, b, _, _, ⟨_, rfl, GlobalTheory.SplitCoord.evalV_single _ 1, fun w hw => GlobalTheory.SplitCoord.evalV_single_ne hw 1⟩, c⟩

theorem isCompact_half {e : AE D} (he : IsSplitIdem D e) {S T : HSp D}
    {ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)} {ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)}
    (hS : IsSelfDualC S ΛS) (hT : IsSelfDualC T ΛT) :
    IsCompact {t : WO S T | t ∈ (latO S T ΛS ΛT fun _ => True) ∧ IsHalf e t} := by
  obtain ⟨v, π, hπ⟩ := GlobalTheory.SplitChart.exists_chart e he
  have h := (GlobalTheory.PlaceCoord.isOpen_isCompact_map (S := S) (T := T) hS.1 hT.1 hπ he.1 (chart_one he.1 hπ)
    (GlobalTheory.PlaceCoord.infPart_split he)).2
  have hc : Continuous fun y : Matrix (Fin T.rank) (Fin S.rank) (Fv D.host.F v) => (y.map (sec e v) : WO S T) :=
    continuous_id.matrix_map (sec_cont e v)
  have h2 := h.image hc
  rw [Set.image_image] at h2
  convert h2 using 1
  refine (Set.EqOn.image_eq_self fun t ht => ?_).symm
  ext i j
  exact (sec_chart he.1 hπ _).trans (ht.2 i j)

variable {S : HSp D}

theorem units_mul_relation_rearrange_commRing {R : Type} [CommRing R] {n : ℕ} (e e' f : R) (G Gi a a' b b' : Matrix (Fin n) (Fin n) R) (h1 : e * e = e)
    (h1' : e' * e' = e') (h2 : e * e' = 0) (hf : f = 1 - e - e') (hba : b * a = e • (1 : Matrix (Fin n) (Fin n) R))
    (hab' : a' * b' = e' • (1 : Matrix (Fin n) (Fin n) R)) (g1 : ∀ x : Matrix (Fin n) (Fin n) R, Gi * (G * x) = x)
    (g2 : ∀ x : Matrix (Fin n) (Fin n) R, G * (Gi * x) = x) :
    (e' • a' + e • (G * b * Gi) + f • 1) * (G * (e • a + e' • (Gi * (b' * G)) + f • 1)) = G := by
  have z1 : e' * e = 0 := by rw [mul_comm, h2]
  have z2 : e' * f = 0 := by rw [hf]; linear_combination -h1' - h2
  have z3 : e * f = 0 := by rw [hf]; linear_combination -h1 - h2
  have z4 : f * e = 0 := by rw [mul_comm, z3]
  have z5 : f * e' = 0 := by rw [mul_comm, z2]
  have z6 : f * f = f := by rw [hf]; linear_combination h1 + h1' + 2 * h2
  simp only [Matrix.add_mul, Matrix.mul_add,
    Matrix.smul_mul, Matrix.mul_smul, smul_smul, z1, z2, z3, z4, z5, z6, h1, h1', h2, zero_smul, add_zero, zero_add,
    Matrix.mul_assoc, g1, g2, Matrix.one_mul, Matrix.mul_one, hba, smul_add]
  rw [← Matrix.mul_assoc, hab', Matrix.smul_mul, smul_smul, h1', Matrix.one_mul, ← add_smul, ← add_smul,
    show e + e' + f = 1 by rw [hf]; ring, one_smul]

theorem reflectionBoost_matrix_conjTranspose_mul_self (e e' f : AE D) (a b : Mx D S.rank S.rank) (h1 : e * e = e) (h2 : e * e' = 0) (c1 : cA D e = e')
    (hf : f = 1 - e - e') (hba : b * a = e • (1 : Mx D S.rank S.rank)) :
    adj (e • a + e' • (giA S * (adj b * gA S)) + f • 1) * (gA S * (e • a + e' • (giA S * (adj b * gA S)) + f • 1)) = gA S := by
  have h1' : e' * e' = e' := by rw [← c1, ← RingHom.map_mul, h1]
  have hab' : adj a * adj b = e' • (1 : Mx D S.rank S.rank) := by rw [← adj_mul, hba, adj_smul, adj_one, c1]
  have hcc : cA D e' = e := by rw [← c1]; exact GlobalTheory.DualPairCheck.cA_cA _
  have cf : cA D f = f := by rw [hf, RingHom.map_sub, RingHom.map_sub, RingHom.map_one, hcc, c1]; exact sub_right_comm _ _ _
  have q : adj (giA S * (adj b * gA S)) = gA S * b * giA S := by
    rw [adj_mul (giA S), adj_mul (adj b), adj_adj, adj_gA, adj_giA]
  have q2 : adj (e • a + e' • (giA S * (adj b * gA S)) + f • (1 : Mx D S.rank S.rank)) =
      e' • adj a + e • (gA S * b * giA S) + f • (1 : Mx D S.rank S.rank) := by
    rw [adj_add, adj_add, adj_smul e, adj_smul e', adj_smul f, q, hcc, cf, c1, adj_one (n := S.rank)]
  rw [q2]
  exact units_mul_relation_rearrange_commRing e e' f _ _ a _ b _ h1 h1' h2 hf hba hab' (giA_gA_cancel S) (gA_giA_cancel S)

end GlobalTheory.SplitHalf
end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.LatticeFrames.ThetaIdentityOfMapsAll
section
set_option genSizeOfSpec false
set_option genInjectivity false

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation
open Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk
open scoped TensorProduct InnerProductSpace

namespace GlobalTheory.Core.Mi

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

section Dense

variable {V W : HSp D} {S S' : D.what₂.Tau → SPar}

open Classical in

def SepCont (M : DSModel V S) (Λ : SmT M →ₗ[ℂ] ℂ) : Prop :=
  ∀ τ (v : M.Vec), ∃ ℓ : M.H τ →ₗ[ℂ] ℂ, Sobolev₂ (lieAt V τ) (M.rep τ) ℓ ∧
    ∀ w : M.sm τ, ℓ w = Λ (PiTensorProduct.tprod ℂ (Function.update v τ w))

def KVecP (M : DSModel V S) (v : M.Vec) : Prop := ∀ τ, IsKFin (M.ε τ) (M.σ τ) (v τ : M.H τ)

def PolStable (θ : InfFam D) (M : DSModel V S) (ω : Om V W) (pt : PolF D W.rank V.rank → (WO V W → ℂ)) : Prop :=
  ∀ τ, (∀ X ∈ lieAt V τ, ∀ P, ∃ P', ∀ z, HasDerivAt (fun t : ℝ => ω (oneP θ V τ X t, 1) (pt P) z) (pt P' z) 0) ∧
    ∃ deg : ℕ → Submodule ℂ (PolF D W.rank V.rank), (∀ n, FiniteDimensional ℂ (deg n)) ∧ (∀ P, ∃ n, P ∈ deg n) ∧
      ∀ k ∈ Formalism.REAL.Kset (M.ε τ), ∀ n, ∀ P ∈ deg n, ∃ P' ∈ deg n,
        pt P' = ω (atTau θ V τ ((M.fr τ)⁻¹ * k * M.fr τ), 1) (pt P)

def ItSpans (M : DSModel V S) (M' : DSModel W S') (It : PolF D W.rank V.rank →ₗ[ℂ] SmT M' →ₗ[ℂ] SmT M) : Prop :=
  ∀ v : M.Vec, KVecP M v → PiTensorProduct.tprod ℂ v ∈
    Submodule.span ℂ {x | ∃ (P : PolF D W.rank V.rank) (y : M'.Vec), KVecP M' y ∧ x = It P (PiTensorProduct.tprod ℂ y)}

end Dense

def PropTo {I : Type} (f τ : I → ℂ) : Prop := ∃ a : ℂ, ∀ i, f i = a * τ i

def DenseExt (D : D7) : Prop :=
  ∀ (θ : InfFam D) (ψ : AddChar (AF D.host.F) ℂ) (ρ : ℕ) (B : BesLev D ρ) (S : D.what₂.Tau → SPar) (M : DSModel B.V S)
    (J : Set (GA D B.V)) (χ : GA D B.V → ℂ) (t : GA D B.V) (I : Type) (τ : I → ℂ) (φ : I → GA D B.A → ℂ)
    (T : I → SmT M →ₗ[ℂ] (GA D B.V → ℂ)), IsInfFam θ → IsStdChar D ψ (-1) → (∀ i, IsContAut B.A (φ i)) →
    (∀ i, T i ∈ MultT θ M J χ) →
    (∀ v : M.Vec, KVecP M v → PropTo (fun i => B.per ψ (φ i) (rTrans t (T i (PiTensorProduct.tprod ℂ v)))) τ) →
    ∀ x : SmT M, PropTo (fun i => B.per ψ (φ i) (rTrans t (T i x))) τ

def TowerSpans (W : Tower D) : Prop :=
  (∀ k, k + 1 < D.R.m → ItSpans (W.MY k) (W.MY (k + 1)) (W.ItY k)) ∧ ItSpans (W.MY (D.R.m - 1)) W.MX W.ItX

section Model

variable (X : HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D)

def IdE : Prop := ∀ x : X.B.I.E, HEq (X.ιE x) x

def rowJ : Set (GA D (D.sp.Y 0)) := iotaX X h ⁻¹' {x : X.B.I.GA | x.1 = 1 ∧ x.2 ∈ X.K2}

def rowChi (k : GA D (D.sp.Y 0)) : ℂ := star (X.chi2 (iotaX X h k).2)

def Matches (J : Set (GA D (D.sp.Y 0))) (χ : GA D (D.sp.Y 0) → ℂ) (t : GA D (D.sp.Y 0)) : Prop :=
  t ∈ GfC (D.sp.Y 0) ∧ ConjLevel t⁻¹ J χ (rowJ X h) (rowChi X h)

def evS (t : GA D (D.sp.Y 0)) (F : GA D (D.sp.Y 0) → ℂ) : X.B.I.GA → ℂ := fun x => F ((iotaX X h).symm x * t)

def ConjVec (θ : InfFam D) {S : D.what₂.Tau → SPar} (M : DSModel (D.sp.Y 0) S) (v₀ : M.Vec) : Prop :=
  ∃ c : ∀ τ, M.H τ ≃ₗᵢ⋆[ℂ] X.B.H (X.pl.symm τ),
    (∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D (D.sp.Y 0) τ), ∀ w, c τ (M.rep τ g w) =
      X.B.σ (X.pl.symm τ) (uMat ((iotaX X h (atTau θ (D.sp.Y 0) τ g)).1 (X.pl.symm τ))) (c τ w)) ∧
    ∀ τ, c τ (v₀ τ : M.H τ) = X.B.w (X.pl.symm τ)

def RealSplit (θ : InfFam D) : Prop :=
  (∀ k : GA D (D.sp.Y 0), k ∈ GfC (D.sp.Y 0) ↔ (iotaX X h k).1 = 1) ∧
  (∀ k : GA D (D.sp.Y 0), k ∈ GinfC (D.sp.Y 0) ↔ (iotaX X h k).2 = 1) ∧
  (∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D (D.sp.Y 0) τ), (iotaX X h (atTau θ (D.sp.Y 0) τ g)).2 = 1 ∧
    (∀ v, v ≠ X.pl.symm τ → (iotaX X h (atTau θ (D.sp.Y 0) τ g)).1 v = 1) ∧
    HEq (uMat ((iotaX X h (atTau θ (D.sp.Y 0) τ g)).1 (X.pl.symm τ)))
      ((fun Pm : Matrix (Fin (D.sp.Y 0).rank) (Fin (D.sp.Y 0).rank) ℂ => Pm⁻¹ * g * Pm)
        ((Formalism.L2.SG.InstExistsPf.instOf D).P (Formalism.L2.Host.tauPl D τ)))) ∧
  ∀ τ (y : Formalism.REAL.UJ (X.B.I.ε (X.pl.symm τ))), ∃ g ∈ Formalism.QuantumDeterminants.UH (gramAt D (D.sp.Y 0) τ),
    (iotaX X h (atTau θ (D.sp.Y 0) τ g)).1 (X.pl.symm τ) = y

def EvalAll (θ : InfFam D) {S : D.what₂.Tau → SPar} (M : DSModel (D.sp.Y 0) S) (J : Set (GA D (D.sp.Y 0)))
    (χ : GA D (D.sp.Y 0) → ℂ) (t : GA D (D.sp.Y 0)) (v₀ : M.Vec) : Prop :=
  ∃ j : MultT θ M J χ →ₗ⋆[ℂ] HHX X, Function.Bijective j ∧ ∀ T : MultT θ M J χ,
    (((j T : HHX X) : L2X X) : X.B.I.GA → ℂ) =ᵐ[muX X] fun x => star (evS X h t (T.1 (PiTensorProduct.tprod ℂ v₀)) x)

structure RowFun (f : X.B.I.GA → ℂ) : Prop where
  cont : Continuous f
  bdd : ∃ C : ℝ, ∀ x, ‖f x‖ ≤ C
  left : ∀ γ ∈ X.B.I.GFset, ∀ x, f (γ * x) = f x
  right : ∀ k ∈ X.K2, ∀ x, f (x * (1, k)) = star (X.chi2 k) * f x

structure SBes (u : D.what₂.Word) (ψ : AddChar (AF D.host.F) ℂ) (A : HSp D) where
  V₀ : HSp D
  L : HSp D
  d : HypDec (D.sp.Y 0) V₀ D.R.rS
  o : OrthDec V₀ A L
  ζ : Fin L.rank → D.host.E
  line : IsLineVec L ζ
  cpt : CoCpt A
  vA : Vol A
  vN : VolN d
  tieN : ∀ n, n ∈ flagN d ↔ (iotaX X h n).1 ∈ X.NinfU u ∧ (iotaX X h n).2 ∈ X.NfinU u
  tieH : ∀ g, g ∈ (embA d o).range ↔ (iotaX X h g).1 ∈ Hinf X u ∧ (iotaX X h g).2 ∈ Hfin X u
  tieψ : ∀ n ∈ flagN d, star (psiBes ψ d 1 (vecB o ζ) n) = X.psiInfU u (iotaX X h n).1 * X.psiFinU u (iotaX X h n).2

namespace SBes

variable {X h} {u : D.what₂.Word} {ψ : AddChar (AF D.host.F) ℂ} {A : HSp D} (B : SBes X h u ψ A)

abbrev lev : BesLev D D.R.rS := ⟨D.sp.Y 0, B.V₀, A, B.L, B.d, B.o, B.ζ, B.line, B.cpt, B.vA, B.vN⟩

def toH (a : GA D A) : Hinf X u × Hfin X u :=
  (⟨(iotaX X h (embA B.d B.o a)).1, ((B.tieH _).1 ⟨a, rfl⟩).1⟩, ⟨(iotaX X h (embA B.d B.o a)).2, ((B.tieH _).1 ⟨a, rfl⟩).2⟩)

def colForm (T : X.Vpi u →ₗ[ℂ] (Hinf X u × Hfin X u → ℂ)) (ξ : X.Vpi u) : GA D A → ℂ := fun a => T ξ (B.toH a)

def PerLaw (Y : Formalism.L2.SG.Full.Full X) : Prop :=
  ∃ c : ℂ, ∀ (T : Cu X u Y.hK) (f : X.B.I.GA → ℂ) (φ : L2X X), RowFun X f → (φ : X.B.I.GA → ℂ) =ᵐ[muX X] f →
    ⟪star φ, PuFun X u Y.hK (Y.Dt u) T⟫_ℂ =
      c * ∫ y, B.lev.per ψ (B.colForm T.1 (X.Wu u y)) (fun g => f (iotaX X h g * (y, X.xu u))) ∂(X.nuQ u)

end SBes

theorem rank_eq (X : HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) : (D.sp.Y 0).rank = X.B.I.n := by
  rw [h]; rfl

def SBes.Adapted {X : HidaSetting D} {h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D} {u : D.what₂.Word}
    {ψ : AddChar (AF D.host.F) ℂ} (B : SBes X h u ψ (D.sp.X 0)) (wt : (VS D).V ≃ₗ[D.host.E] (VS D).V) : Prop :=
  ∀ k j, (B.d.i₀ * B.o.iA) k j = X.ιE (X.crd (Formalism.L2.SG.ColDict.qFr wt
    (Fin.cast (Formalism.L2.Forms.rankN D 0 (Nat.zero_le _)) j)) (Fin.cast (rank_eq X h) k))

end Model

section MI

variable {F₀ : ∀ u, Formalism.L2.Forms.Forms0 D u} (S : STrue D F₀) (u : D.what₂.Word) (W : Tower D) (L : Link D u W)

def colOf (x : D.s.Cu u) : Cu S.X u S.Y.hK := (S.hI S.hF).eCu u x

def shift (t : GA D (D.sp.Y 0)) : GA D (D.sp.Y 0) := (iotaX S.X S.inst).symm (1, S.X.xu u) * t

def ThetaIdentityOfMapsAt (t : GA D (D.sp.Y 0)) {A : HSp D} (B : SBes S.X S.inst u W.ψ A) : Prop :=
  ∃ U : (D.mem u).A.Mram →ₗ[ℂ] D.s.Cu u, Function.Injective U ∧
    ∀ (ξ : S.X.Vpi u) (x : SmT (W.MY 0)), ∃ a : ℂ,
      ∀ (φ : (D.mem u).A.Mram) (F : (D.mem u).P.Mt) (T₀ : SmT (W.MY 0) →ₗ[ℂ] (GA D (Yc D 0) → ℂ)), W.IsDn (L.eT F) T₀ →
        B.lev.per W.ψ (B.colForm (colOf S u (U φ)).1 ξ) (rTrans (shift S u t) (T₀ x)) =
          a * PhiC (D.mem u).C (D.mem u).A (D.mem u).P φ F

def ThetaVectorCompatibility (v₀ : (W.MY 0).Vec) (t : GA D (D.sp.Y 0)) : Prop :=
  L.RowPinAt S.toSTies S.hF v₀ t ∧
    Matches S.X S.inst (levS (Yc D 0) (W.βY 0) (W.datYt () 0 L.P)) (levChi (Yc D 0) (W.βY 0) (W.datYt () 0 L.P)) t

end MI

open GlobalTheory.Mem GlobalTheory.Mem.Col2 in

def ThetaIdentityOfMapsAll {Bs : Base} {Xp : PreX Bs.toPre} {I : TC Bs Xp} {l : I.Laws} {Z : TC.Later Bs (I.cols l)} (w : World I l Z)
    (u : (I.rec7 l Z).what₂.Word) : Prop :=
  ∃ (W : Tower (I.rec7 l Z)) (L : Link (I.rec7 l Z) u W) (v₀ : (W.MY 0).Vec) (t : GA (I.rec7 l Z) ((I.rec7 l Z).sp.Y 0))
    (B : SBes w.S.X w.S.inst u W.ψ ((I.rec7 l Z).sp.X 0)),
    W.Is ∧ L.TopPin (w.C.forms u) ∧ ThetaVectorCompatibility w.S u W L v₀ t ∧ B.Adapted (w.S.tr u).wt ∧ ThetaIdentityOfMapsAt w.S u W L t B

example {I : Type} (τ : I → ℂ) : PropTo (fun _ => 0) τ := ⟨0, fun _ => by simp⟩

example : ¬ PropTo (fun _ : Unit => (1 : ℂ)) (fun _ => 0) := fun ⟨a, h⟩ => by simpa using h ()

end GlobalTheory.Core.Mi

end
end

