import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0012
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0015
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0008
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0024
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.TransvectionAction
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0009
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.CovolOneIntegralAdd
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0146
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0119
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0027
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0310
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0078
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0068
import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsTopologicalRingAE
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0221
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0149

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TsumAdelicMatrixSchwartzMajorantRationalNeTop
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf
open scoped ComplexOrder ENNReal NNReal ContDiff Pointwise

noncomputable section

namespace GlobalTheory.MajSum

variable {D : D7}

theorem realSize_add_le (θ : InfFam D) {m n : ℕ} (x y : Mx D m n) :
    realSize θ (x + y) ≤ realSize θ x + realSize θ y := by
  unfold realSize
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun τ _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun i _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun j _ => ?_
  have : Formalism.IndefR.Datum.compAt θ τ (x + y) i j =
      Formalism.IndefR.Datum.compAt θ τ x i j + Formalism.IndefR.Datum.compAt θ τ y i j := by
    show θ τ (infPart D (x i j + y i j)) = θ τ (infPart D (x i j)) + θ τ (infPart D (y i j))
    rw [RingHom.map_add (infPart D), RingHom.map_add (θ τ)]
  rw [this]
  exact norm_add_le _ _

theorem maj_le_shift (θ : InfFam D) {m n : ℕ} (K C : Set (Mx D m n)) (N : ℕ) (γ w : Mx D m n)
    (hwC : w ∈ C) (hw : realSize θ w ≤ 1) :
    maj θ K N γ ≤ 2 ^ N * maj θ (K + C) N (γ + w) := by
  unfold maj
  by_cases hγ : InBox K γ
  · have hbox : InBox (K + C) (γ + w) := by
      obtain ⟨k, hk, hk0⟩ := hγ
      refine ⟨k + w, Set.add_mem_add hk hwC, ?_⟩
      have : γ + w - (k + w) = γ - k := by abel
      rw [this]; exact hk0
    rw [if_pos hγ, if_pos hbox]
    have h0 := realSize_nonneg θ γ
    have h1 := realSize_nonneg θ (γ + w)
    have h2 : 1 + realSize θ (γ + w) ≤ 2 * (1 + realSize θ γ) := by
      have := realSize_add_le θ γ w; linarith
    have hp : (0:ℝ) < (1 + realSize θ (γ + w)) ^ N := by positivity
    have hq : (0:ℝ) < (1 + realSize θ γ) ^ N := by positivity
    rw [← div_eq_mul_inv, inv_eq_one_div, div_le_div_iff₀ hq hp, one_mul]
    calc (1 + realSize θ (γ + w)) ^ N ≤ (2 * (1 + realSize θ γ)) ^ N := by gcongr
      _ = 2 ^ N * (1 + realSize θ γ) ^ N := by rw [mul_pow]
  · rw [if_neg hγ]
    have := maj_nonneg θ (K + C) N (γ + w)
    unfold maj at this
    positivity

end GlobalTheory.MajSum

namespace GlobalTheory.MajSum

theorem realSize_zero {D : D7} (θ : InfFam D) {m n : ℕ} : realSize θ (0 : Mx D m n) = 0 := by
  have h : ∀ τ (i : Fin m) (j : Fin n), Formalism.IndefR.Datum.compAt θ τ (0 : Mx D m n) i j = 0 := by
    intro τ i j
    show θ τ (infPart D 0) = 0
    rw [RingHom.map_zero (infPart D), RingHom.map_zero (θ τ)]
  unfold realSize
  simp only [h, norm_zero, Finset.sum_const_zero]

set_option synthInstance.maxHeartbeats 400000 in

theorem tsum_maj_ne_top : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ m n : ℕ, ∃ N : ℕ, ∀ K : Set (Mx D m n), IsCompact K →
    (∑' y : ratMx D m n, ENNReal.ofReal (maj θ K N y)) ≠ ⊤ := by
  intro D θ hθ m n
  obtain ⟨i1, i2, i3, i4, i5, -⟩ := lattice_Mx D m n
  haveI : BorelSpace (Mx D m n) := ⟨rfl⟩
  haveI : Countable (ratMx D m n) := TopologicalSpace.separableSpace_iff_countable.1 inferInstance
  let μ : Measure (Mx D m n) := Measure.addHaar
  have hcont : Continuous (realSize θ : Mx D m n → ℝ) :=
    ((GlobalTheory.T.adelicMatrixSchwartzMajorant_measurable_rationalShift D θ hθ).1 m n ∅ isCompact_empty).2.1
  obtain ⟨N, hN⟩ := GlobalTheory.T.integrable_majorant_coordinate_coset_measure D θ hθ m n (fun _ _ => True) 0 μ inferInstance
    (Filter.Eventually.of_forall fun x i j h => (h trivial).elim)
    (fun t _ => by
      have e : (fun x : Mx D m n => x + t) = fun x => t + x := funext fun x => add_comm x t
      rw [e]; exact map_add_left_eq_self μ t)
  refine ⟨N, fun K hK => ?_⟩

  obtain ⟨U, hUo, hU⟩ : ∃ U : Set (Mx D m n), IsOpen U ∧ ∀ γ ∈ ratMx D m n, γ ∈ U ↔ γ = 0 := by
    have h0 : IsOpen ({0} : Set (ratMx D m n)) := @isOpen_discrete (ratMx D m n) _ i5 _
    obtain ⟨U, hUo, hUe⟩ := isOpen_induced_iff.mp h0
    refine ⟨U, hUo, fun γ hγ => ?_⟩
    have := Set.ext_iff.mp hUe ⟨γ, hγ⟩
    simp only [Set.mem_preimage, Set.mem_singleton_iff] at this
    rw [this]
    exact ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩
  have h0U : (0 : Mx D m n) ∈ U := (hU 0 (zero_mem _)).2 rfl
  have hsub : {p : Mx D m n × Mx D m n | p.1 - p.2 ∈ U} ∈ nhds ((0 : Mx D m n), (0 : Mx D m n)) := by
    have hc : Continuous fun p : Mx D m n × Mx D m n => p.1 - p.2 := continuous_fst.sub continuous_snd
    refine hc.continuousAt.preimage_mem_nhds ?_
    simpa using hUo.mem_nhds h0U
  obtain ⟨A, hA, B, hB, hAB⟩ := mem_nhds_prod_iff.mp hsub
  obtain ⟨C, hCc, hC⟩ := exists_compact_mem_nhds (0 : Mx D m n)
  have hR : {w : Mx D m n | realSize θ w < 1} ∈ nhds (0 : Mx D m n) := by
    refine (isOpen_lt hcont continuous_const).mem_nhds ?_
    show realSize θ (0 : Mx D m n) < 1
    rw [realSize_zero]; exact one_pos
  set W := interior (A ∩ B ∩ C ∩ {w : Mx D m n | realSize θ w < 1}) with hWdef
  have hW0 : (0 : Mx D m n) ∈ W :=
    mem_interior_iff_mem_nhds.2 (Filter.inter_mem (Filter.inter_mem (Filter.inter_mem hA hB) hC) hR)
  have hμW : μ W ≠ 0 := (isOpen_interior.measure_pos μ ⟨0, hW0⟩).ne'

  let s : ratMx D m n → Set (Mx D m n) := fun γ => (fun x => -(γ : Mx D m n) + x) ⁻¹' W
  have hs : ∀ γ, MeasurableSet (s γ) := fun γ =>
    (isOpen_interior.preimage (continuous_const.add continuous_id)).measurableSet
  have hdisj : Pairwise (Function.onFun Disjoint s) := by
    intro γ γ' hne
    refine Set.disjoint_left.2 fun x hx hx' => hne ?_
    have hxA : -(γ : Mx D m n) + x ∈ A := (interior_subset hx).1.1.1
    have hxB : -(γ' : Mx D m n) + x ∈ B := (interior_subset hx').1.1.2
    have hmem : (-(γ : Mx D m n) + x, -(γ' : Mx D m n) + x) ∈ {p : Mx D m n × Mx D m n | p.1 - p.2 ∈ U} :=
      hAB ⟨hxA, hxB⟩
    simp only [Set.mem_setOf_eq] at hmem
    have e : -(γ : Mx D m n) + x - (-(γ' : Mx D m n) + x) = (γ' : Mx D m n) - γ := by abel
    rw [e] at hmem
    have := (hU _ (sub_mem γ'.2 γ.2)).1 hmem
    exact Subtype.ext (sub_eq_zero.1 this).symm
  set K' := K + C
  have hK' : IsCompact K' := hK.add hCc
  have hfin : ∫⁻ x, ENNReal.ofReal (maj θ K' N x) ∂μ < ⊤ := (hN K' hK').lintegral_lt_top
  have key : ∀ γ : ratMx D m n, ENNReal.ofReal (maj θ K N γ) * μ W ≤
      2 ^ N * ∫⁻ x in s γ, ENNReal.ofReal (maj θ K' N x) ∂μ := by
    intro γ
    calc ENNReal.ofReal (maj θ K N γ) * μ W = ∫⁻ _x in s γ, ENNReal.ofReal (maj θ K N γ) ∂μ := by
          rw [setLIntegral_const]
          congr 1
          exact (measure_preimage_add μ (-(γ : Mx D m n)) W).symm
      _ ≤ ∫⁻ x in s γ, 2 ^ N * ENNReal.ofReal (maj θ K' N x) ∂μ := by
          refine setLIntegral_mono' (hs γ) fun x hx => ?_
          have hw := interior_subset hx
          have h1 := maj_le_shift θ K C N (γ : Mx D m n) (-(γ : Mx D m n) + x) hw.1.2 (le_of_lt hw.2)
          rw [add_neg_cancel_left] at h1
          calc ENNReal.ofReal (maj θ K N γ) ≤ ENNReal.ofReal (2 ^ N * maj θ K' N x) :=
                ENNReal.ofReal_le_ofReal h1
            _ = 2 ^ N * ENNReal.ofReal (maj θ K' N x) := by
                rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_pow (by norm_num), ENNReal.ofReal_ofNat]
      _ = 2 ^ N * ∫⁻ x in s γ, ENNReal.ofReal (maj θ K' N x) ∂μ :=
          lintegral_const_mul' _ _ (ENNReal.pow_ne_top ENNReal.ofNat_ne_top)
  have hsum : (∑' γ : ratMx D m n, ENNReal.ofReal (maj θ K N γ)) * μ W ≤
      2 ^ N * ∫⁻ x, ENNReal.ofReal (maj θ K' N x) ∂μ := by
    rw [← ENNReal.tsum_mul_right]
    calc _ ≤ ∑' γ : ratMx D m n, 2 ^ N * ∫⁻ x in s γ, ENNReal.ofReal (maj θ K' N x) ∂μ :=
          ENNReal.tsum_le_tsum key
      _ = 2 ^ N * ∑' γ : ratMx D m n, ∫⁻ x in s γ, ENNReal.ofReal (maj θ K' N x) ∂μ := ENNReal.tsum_mul_left
      _ = 2 ^ N * ∫⁻ x in ⋃ γ, s γ, ENNReal.ofReal (maj θ K' N x) ∂μ := by rw [lintegral_iUnion hs hdisj]
      _ ≤ 2 ^ N * ∫⁻ x, ENNReal.ofReal (maj θ K' N x) ∂μ := by
          gcongr; exact Measure.restrict_le_self
  intro htop
  rw [htop, ENNReal.top_mul hμW] at hsum
  exact (ENNReal.mul_lt_top (ENNReal.pow_lt_top ENNReal.ofNat_lt_top) hfin).ne (top_le_iff.1 hsum)

end GlobalTheory.MajSum
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilOperatorOrthSummandSlicesSobolevBounded
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf
open scoped ENNReal NNReal

namespace GlobalTheory.SliceForm

open GlobalTheory.Size GlobalTheory.OrientedHeis GlobalTheory.FockCompare

variable {D : D7} {S A B T : HSp D}

def slA (o : OrthDec S A B) (f : WO S T → ℂ) : WO A T → ℂ := fun u => f ((o.resS T).symm (u, 0))

def extA (o : OrthDec S A B) (T : HSp D) : WO A T →+ WO S T :=
  (o.resS T).symm.toAddMonoidHom.comp (AddMonoidHom.inl _ _)

theorem extA_apply (o : OrthDec S A B) (u : WO A T) : extA o T u = (o.resS T).symm (u, 0) := rfl

theorem symm_left (o : OrthDec S A B) (u : WO A T) : (o.resS T).symm (u, 0) = u ⬝ o.pA := by
  rw [o.resS_symm_apply, Matrix.zero_mul, add_zero]

theorem symm_swap (o : OrthDec S A B) (v : WO B T) : (o.symm.resS T).symm (v, 0) = (o.resS T).symm (0, v) := by
  rw [OrthDec.resS_symm_apply, OrthDec.resS_symm_apply]
  exact add_comm _ _

theorem compAt_pA {θ : InfFam D} (hθ : IsInfFam θ) (o : OrthDec S A B) (τ : D.what₂.Tau) :
    compAt θ τ o.pA = o.qA.map (tauE D τ) := by
  unfold compAt OrthDec.pA GlobalTheory.MixModel.rat
  rw [Matrix.map_map]
  congr 1
  funext e
  exact GlobalTheory.FockCompare.comp_incA hθ τ e

theorem lineAt_slice {θ : InfFam D} (hθ : IsInfFam θ) (o : OrthDec S A B) (τ : D.what₂.Tau)
    (z : Matrix (Fin T.rank) (Fin A.rank) ℂ) (t : ℝ) :
    (o.resS T).symm (lineAt θ τ z t, 0) = lineAt θ τ (z * o.qA.map (tauE D τ)) t := by
  have hL := GlobalTheory.OrientedHeis.isLineAt_lineAt hθ τ z
  let L : ℝ →+ WO S T := (extA o T).comp (lineAt θ τ z)
  have hL' : IsLineAt θ τ (z * o.qA.map (tauE D τ)) L := by
    refine ⟨(o.continuous_resS_symm T).comp (hL.1.prodMk continuous_const), fun t => ?_, fun t τ' => ?_⟩
    · show ((o.resS T).symm (lineAt θ τ z t, 0)).map (finPart D) = 0
      rw [symm_left, Matrix.map_mul, hL.2.1, Matrix.zero_mul]
    · show compAt θ τ' ((o.resS T).symm (lineAt θ τ z t, 0)) = _
      rw [symm_left, GlobalTheory.OrientedHeis.compAt_mul, hL.2.2, compAt_pA hθ]
      split_ifs with h
      · subst h
        rw [Matrix.smul_mul]
      · rw [Matrix.zero_mul]
  rw [GlobalTheory.RealLineAt.lineAt_unique D θ hθ _ _ τ _ _ _ (GlobalTheory.OrientedHeis.isLineAt_lineAt hθ τ _) hL']
  rfl

theorem heisO_slice (ψ : AddChar (AF D.host.F) ℂ) (o : OrthDec S A B) (u : WO A T) (g : WO S T → ℂ) :
    heisO ψ A T u (slA o g) = slA o (heisO ψ S T ((o.resS T).symm (u, 0)) g) := by
  funext w
  simp only [slA, heisO]
  rw [o.symplOH_resS T, ← map_add, Prod.mk_add_mk, add_zero]
  simp only [AddEquiv.apply_symm_apply, symplOH_zero_left, add_zero]

theorem dRho_slice (ψ : AddChar (AF D.host.F) ℂ) {θ : InfFam D} (hθ : IsInfFam θ) (o : OrthDec S A B)
    (τ : D.what₂.Tau) (z : Matrix (Fin T.rank) (Fin A.rank) ℂ) (g : WO S T → ℂ) :
    Formalism.IndefR.Datum.dRho (heisO ψ A T) θ τ z (slA o g) =
      slA o (Formalism.IndefR.Datum.dRho (heisO ψ S T) θ τ (z * o.qA.map (tauE D τ)) g) := by
  funext w
  simp only [Formalism.IndefR.Datum.dRho, heisO_slice, lineAt_slice hθ]
  rfl

end GlobalTheory.SliceForm

namespace GlobalTheory.SliceForm

open GlobalTheory.Size GlobalTheory.OrientedHeis GlobalTheory.FockCompare

variable {D : D7} {S A B T : HSp D}

def dirA (o : OrthDec S A B) (a : D.what₂.Tau × Fin T.rank × Fin A.rank × Bool) : Matrix (Fin T.rank) (Fin S.rank) ℂ :=
  Matrix.single a.2.1 a.2.2.1 (if a.2.2.2 then Complex.I else 1) * o.qA.map (tauE D a.1)

def opA (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (o : OrthDec S A B)
    (a : D.what₂.Tau × Fin T.rank × Fin A.rank × Bool) (g : WO S T → ℂ) : WO S T → ℂ :=
  Formalism.IndefR.Datum.dRho (heisO ψ S T) θ a.1 (dirA o a) g

theorem word_slice (ψ : AddChar (AF D.host.F) ℂ) {θ : InfFam D} (hθ : IsInfFam θ) (o : OrthDec S A B)
    (l : List (D.what₂.Tau × Fin T.rank × Fin A.rank × Bool)) (g : WO S T → ℂ) :
    wordAct (heisDer ψ θ) l (slA o g) = slA o (wordAct (opA ψ θ o) l g) := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    rw [wordAct_cons, wordAct_cons, ih]
    exact dRho_slice ψ hθ o a.1 _ _

abbrev supN (φ : WO S T → ℂ) : ℝ≥0∞ := ⨆ w, ‖φ w‖ₑ

theorem word_bound {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) {θ : InfFam D} (hθ : IsInfFam θ)
    (o : OrthDec S A B) (l : List (D.what₂.Tau × Fin T.rank × Fin A.rank × Bool)) :
    ∃ c : ℝ≥0, ∀ g, IsThetaFunO ψ S T g → ∀ k,
      wordSum (heisDer ψ θ) supN k (wordAct (opA ψ θ o) l g) ≤ c * wordSum (heisDer ψ θ) supN (k + l.length) g := by
  induction l with
  | nil => exact ⟨1, fun g _ k => by simp⟩
  | cons a l ih =>
    obtain ⟨c, hc⟩ := ih
    refine ⟨Real.toNNReal (∑ i, ∑ j, (|(dirA o a i j).re| + |(dirA o a i j).im|)) * c, fun g hg k => ?_⟩
    have hg' : IsThetaFunO ψ S T (wordAct (opA ψ θ o) l g) :=
      wordAct_rel (B := opA ψ θ o) (R := fun x _ => IsThetaFunO ψ S T x) l
        (fun a _ _ _ h => theta_dRho hθ hψ a.1 _ h) (y := g) hg
    rw [wordAct_cons]
    calc _ ≤ ENNReal.ofReal (∑ i, ∑ j, (|(dirA o a i j).re| + |(dirA o a i j).im|)) *
          wordSum (heisDer ψ θ) supN (k + 1) (wordAct (opA ψ θ o) l g) :=
          GlobalTheory.Size.SupWord.ws_dRho_le hψ hθ GlobalTheory.Size.SupWord.supN_add_le GlobalTheory.Size.SupWord.supN_smul hg' a.1 _ k
      _ ≤ ENNReal.ofReal (∑ i, ∑ j, (|(dirA o a i j).re| + |(dirA o a i j).im|)) *
          (c * wordSum (heisDer ψ θ) supN (k + 1 + l.length) g) := by gcongr; exact hc g hg (k + 1)
      _ = _ := by
        rw [List.length_cons, show k + (l.length + 1) = k + 1 + l.length by omega, ← mul_assoc, ENNReal.ofReal,
          ENNReal.coe_mul]

theorem l2O_le_supN_of_measure_eq_one {μ : Measure (WO S T)} {𝓕 : Set (WO S T)} (h1 : μ 𝓕 = 1) (φ : WO S T → ℂ) :
    l2O μ 𝓕 φ ≤ supN φ := by
  have h : l2O μ 𝓕 φ ^ 2 ≤ supN φ ^ 2 := by
    rw [l2O_sq_eq_lintegral]
    calc ∫⁻ w in 𝓕, ‖φ w‖ₑ ^ 2 ∂μ ≤ ∫⁻ _ in 𝓕, supN φ ^ 2 ∂μ :=
          lintegral_mono fun w => by gcongr; exact le_iSup (fun w => ‖φ w‖ₑ) w
      _ = supN φ ^ 2 := by rw [setLIntegral_const, h1, mul_one]
  exact (ENNReal.pow_le_pow_left_iff two_ne_zero).1 h

theorem supN_slice (o : OrthDec S A B) (φ : WO S T → ℂ) : supN (slA o φ) ≤ supN φ :=
  iSup_le fun _ => le_iSup (fun w => ‖φ w‖ₑ) _

end GlobalTheory.SliceForm

namespace GlobalTheory.SliceForm

open GlobalTheory.Size GlobalTheory.OrientedHeis GlobalTheory.FockCompare

variable {D : D7} {S A B T : HSp D}

theorem sobO_slice_le {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) {θ : InfFam D} (hθ : IsInfFam θ)
    (o : OrthDec S A B) (d : ℕ) : ∃ K : ℝ≥0, ∀ (μ : Measure (WO A T)) (𝓕 : Set (WO A T)), μ 𝓕 = 1 →
      ∀ f, IsThetaFunO ψ S T f → sobO ψ θ μ 𝓕 d (slA o f) ≤ K * supSob ψ θ d f := by
  choose c hc using word_bound (T := T) hψ hθ o
  refine ⟨∑ k ∈ Finset.range (d + 1), ∑ a : Fin k → D.what₂.Tau × Fin T.rank × Fin A.rank × Bool, c (List.ofFn a),
    fun μ 𝓕 h1 f hf => ?_⟩
  unfold sobO supSob wordSum
  push_cast
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun k hk => ?_
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun a _ => ?_
  have hkd : k ≤ d := Nat.lt_succ_iff.1 (Finset.mem_range.1 hk)
  rw [word_slice ψ hθ o]
  calc l2O μ 𝓕 (slA o (wordAct (opA ψ θ o) (List.ofFn a) f)) ≤ supN (wordAct (opA ψ θ o) (List.ofFn a) f) :=
        (l2O_le_supN_of_measure_eq_one h1 _).trans (supN_slice o _)
    _ = wordSum (heisDer ψ θ) supN 0 (wordAct (opA ψ θ o) (List.ofFn a) f) := (wordSum_zero _ _ _).symm
    _ ≤ c (List.ofFn a) * wordSum (heisDer ψ θ) supN (0 + (List.ofFn a).length) f := hc _ f hf 0
    _ ≤ c (List.ofFn a) * wordSum (heisDer ψ θ) supN d f := by
        gcongr
        exact wordSum_mono (by rw [List.length_ofFn]; omega) f
    _ = _ := rfl

theorem isSobForm_slice {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} (hθ : IsInfFam θ) (o : OrthDec S A B)
    {χ χ' : (AE D)ˣ →* Circle} {om : Om A T} (hom : IsWeilDatumO ψ A T χ χ' om) (p : GA D A × GA D T) :
    IsSobForm ψ θ S T fun f => om p (fun u => f ((o.resS T).symm (u, 0))) 0 where
  add f g _ _ := by
    show om p (slA o f + slA o g) 0 = _
    rw [map_add]; rfl
  smul c f _ := by
    show om p (c • slA o f) 0 = _
    rw [map_smul]; rfl
  bound U hU := by
    have hψ := hom.std
    let U' : AddSubgroup (WO A T) := U.comap (extA o T)
    have hU' : IsOpen (U' : Set (WO A T)) :=
      hU.preimage ((o.continuous_resS_symm T).comp (continuous_id.prodMk continuous_const))
    obtain ⟨e, d, hK⟩ := GlobalTheory.KernelSeminorm.thetaGrowth_onObjects D A.rank T.rank
    obtain ⟨C, hC⟩ := hK A T rfl rfl ψ θ hθ U' hU'
    obtain ⟨μ, 𝓕, hμ⟩ := exists_isCovolOne A T
    obtain ⟨K, hKs⟩ := sobO_slice_le (T := T) hψ hθ o d
    refine ⟨d, C * (ENNReal.ofReal ((height A p.1 * height T p.2) ^ e)).toNNReal * K, fun f hf => ?_⟩
    have hsl : slA o f ∈ thetaLevel ψ A T U' := by
      refine ⟨((GlobalTheory.T.thetaFunction_products_slices_orthogonalDecomposition D ψ hψ S A B T o).2.2.2 f hf.1).1 0, fun u hu h0 => ?_⟩
      rw [heisO_slice, ← extA_apply, hf.2 _ hu]
      rw [extA_apply, symm_left, Matrix.map_mul, h0, Matrix.zero_mul]
    have h := hC χ χ' om hom μ 𝓕 hμ (slA o f) hsl p.1 p.2
    have h2 := hKs μ 𝓕 hμ.2.2 f hf.1
    have hfin : ENNReal.ofReal ((height A p.1 * height T p.2) ^ e) ≠ ⊤ := ENNReal.ofReal_ne_top
    calc ‖om p (fun u => f ((o.resS T).symm (u, 0))) 0‖ₑ = ‖thetaKO om p.1 p.2 (slA o f)‖ₑ := rfl
      _ ≤ C * sobO ψ θ μ 𝓕 d (slA o f) * ENNReal.ofReal ((height A p.1 * height T p.2) ^ e) := h
      _ ≤ C * (K * supSob ψ θ d f) * ENNReal.ofReal ((height A p.1 * height T p.2) ^ e) := by gcongr
      _ = _ := by
        rw [ENNReal.coe_mul, ENNReal.coe_mul, ENNReal.coe_toNNReal hfin]
        ring

theorem weil_slice_isSobForm : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D), IsInfFam θ →
    ∀ (S A B T : HSp D) (o : OrthDec S A B),
      (∀ (χ χ' : (AE D)ˣ →* Circle) (om : Om A T), IsWeilDatumO ψ A T χ χ' om →
        ∀ p, IsSobForm ψ θ S T fun f => om p (fun u => f ((o.resS T).symm (u, 0))) 0) ∧
      ∀ (χ χ' : (AE D)ˣ →* Circle) (om : Om B T), IsWeilDatumO ψ B T χ χ' om →
        ∀ p, IsSobForm ψ θ S T fun f => om p (fun v => f ((o.resS T).symm (0, v))) 0 := by
  intro D ψ θ hθ S A B T o
  refine ⟨fun χ χ' om hom p => isSobForm_slice hθ o hom p, fun χ χ' om hom p => ?_⟩
  have e : (fun f : WO S T → ℂ => om p (fun v => f ((o.resS T).symm (0, v))) 0) =
      fun f => om p (fun v => f ((o.symm.resS T).symm (v, 0))) 0 := by
    funext f
    simp only [symm_swap]
  rw [e]
  exact isSobForm_slice hθ o.symm hom p

end GlobalTheory.SliceForm
end
end

