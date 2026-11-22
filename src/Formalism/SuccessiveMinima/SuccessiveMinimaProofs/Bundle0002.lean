import Formalism.SuccessiveMinima.Bundle0002
import Formalism.SuccessiveMinima.SuccessiveMinimaProofs.NewtonSlope

-- bundled from Formalism.SuccessiveMinima.SuccessiveMinimaProofs.MinkCore
section
open MeasureTheory Module Metric Set
open scoped Pointwise ENNReal

noncomputable section

namespace Formalism.FN

theorem partialBoxVolumeTopLeOne : GjTop := by
  intro n A
  unfold Gj
  calc volume (boxJ n n ∩ (A + latJ n n)) ≤ volume (boxJ n n) :=
        measure_mono Set.inter_subset_left
    _ ≤ volume (Set.univ.pi fun _ : Fin n => Set.Ico (0 : ℝ) 1) := by
        apply measure_mono
        intro u hu i _
        exact hu i i.2
    _ = 1 := by
        rw [Real.volume_pi_Ico]
        simp

theorem gjZero (n : ℕ) (A : Set (Fin n → ℝ)) : Gj n 0 A = volume A := by
  unfold Gj
  have h1 : boxJ n 0 = Set.univ := by
    ext u
    simp [boxJ]
  have h2 : latJ n 0 = {0} := by
    ext k
    simp only [latJ, Set.mem_setOf_eq, Set.mem_singleton_iff]
    constructor
    · rintro ⟨_, hk⟩
      funext i
      exact hk i (Nat.zero_le _)
    · rintro rfl
      exact ⟨fun _ => ⟨0, by simp⟩, fun _ _ => rfl⟩
  rw [h1, h2, Set.univ_inter]
  simp

theorem minkCore_of (h3 : GjLevel) (h4 : GjScale) : MinkCore := by
  intro n C lam hCo hCc hCs hCb hpos hmono hsep
  have hsmulC : ∀ k : Fin n, IsOpen (lam k • C) := fun k => hCo.smul₀ (hpos k).ne'
  have hlev : ∀ k : Fin n, Gj n k (lam k • C) ≤ Gj n (k + 1) (lam k • C) := by
    intro k
    apply h3 n k (lam k • C) k.2 (hsmulC k)
    intro x hx y hy hxy i hi
    exact hsep k x hx y hy hxy i (Fin.le_def.mpr hi)
  have hbase : ∀ hk : 0 < n, ENNReal.ofReal (∏ i, min (lam i) (lam ⟨0, hk⟩)) * volume C
      ≤ Gj n 0 (lam ⟨0, hk⟩ • C) := by
    intro hk
    rw [gjZero, Measure.addHaar_smul, Module.finrank_fin_fun, abs_of_pos (pow_pos (hpos _) n)]
    have e : ∏ i, min (lam i) (lam ⟨0, hk⟩) = lam ⟨0, hk⟩ ^ n := by
      rw [Finset.prod_congr rfl
        (fun i _ => min_eq_right (hmono (show (⟨0, hk⟩ : Fin n) ≤ i from
          Fin.le_def.mpr (Nat.zero_le (i : ℕ)))))]
      simp
    rw [e]
  have hstep : ∀ k (hk0 : k < n) (hk : k + 1 < n),
      ∏ i, min (lam i) (lam ⟨k + 1, hk⟩) =
        (lam ⟨k + 1, hk⟩ / lam ⟨k, hk0⟩) ^ (n - (k + 1)) * ∏ i, min (lam i) (lam ⟨k, hk0⟩) := by
    intro k hk0 hk
    have hab : lam ⟨k, hk0⟩ ≤ lam ⟨k + 1, hk⟩ := hmono (Fin.mk_le_mk.mpr (by omega))
    have ha0 : 0 < lam ⟨k, hk0⟩ := hpos _
    have hfac : ∀ i : Fin n, min (lam i) (lam ⟨k + 1, hk⟩) =
        (if k < (i : ℕ) then lam ⟨k + 1, hk⟩ / lam ⟨k, hk0⟩ else 1) * min (lam i) (lam ⟨k, hk0⟩) := by
      intro i
      split_ifs with h
      · have h1 : lam ⟨k + 1, hk⟩ ≤ lam i := hmono (Fin.le_def.mpr (show k + 1 ≤ (i : ℕ) by omega))
        rw [min_eq_right h1, min_eq_right (hab.trans h1), div_mul_cancel₀ _ ha0.ne']
      · have h1 : lam i ≤ lam ⟨k, hk0⟩ := hmono (Fin.le_def.mpr (show (i : ℕ) ≤ k by omega))
        rw [min_eq_left (h1.trans hab), min_eq_left h1, one_mul]
    have hcard : (Finset.univ.filter fun i : Fin n => k < (i : ℕ)).card = n - (k + 1) := by
      have e : (Finset.univ.filter fun i : Fin n => k < (i : ℕ)) = Finset.Ioi ⟨k, hk0⟩ := by
        ext i
        simp [Fin.lt_def]
      rw [e, Fin.card_Ioi]
      simp only
      omega
    rw [Finset.prod_congr rfl (fun i _ => hfac i), Finset.prod_mul_distrib, Finset.prod_ite,
      Finset.prod_const, Finset.prod_const_one, mul_one, hcard]
  have claim : ∀ k (hk : k < n), ENNReal.ofReal (∏ i, min (lam i) (lam ⟨k, hk⟩)) * volume C
      ≤ Gj n k (lam ⟨k, hk⟩ • C) := by
    intro k
    induction k with
    | zero => exact hbase
    | succ k ih =>
      intro hk
      have hk0 : k < n := by omega
      have hr : 0 ≤ (lam ⟨k + 1, hk⟩ / lam ⟨k, hk0⟩) ^ (n - (k + 1)) := by
        have := hpos ⟨k + 1, hk⟩
        have := hpos ⟨k, hk0⟩
        positivity
      rw [hstep k hk0 hk, ENNReal.ofReal_mul hr, mul_assoc]
      calc ENNReal.ofReal ((lam ⟨k + 1, hk⟩ / lam ⟨k, hk0⟩) ^ (n - (k + 1))) *
            (ENNReal.ofReal (∏ i, min (lam i) (lam ⟨k, hk0⟩)) * volume C)
          ≤ ENNReal.ofReal ((lam ⟨k + 1, hk⟩ / lam ⟨k, hk0⟩) ^ (n - (k + 1))) *
            Gj n (k + 1) (lam ⟨k, hk0⟩ • C) := by
            gcongr
            exact (ih hk0).trans (hlev ⟨k, hk0⟩)
        _ ≤ Gj n (k + 1) (lam ⟨k + 1, hk⟩ • C) :=
            h4 n (k + 1) C (lam ⟨k, hk0⟩) (lam ⟨k + 1, hk⟩) hk.le hCo hCc hCs hCb (hpos _)
              (hmono (Fin.mk_le_mk.mpr (by omega)))
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    have h0 := partialBoxVolumeTopLeOne 0 C
    rw [gjZero] at h0
    simp only [Fin.prod_univ_zero, mul_one]
    exact ENNReal.toReal_le_of_le_ofReal zero_le_one (by simpa using h0)
  · have hn1 : n - 1 < n := by omega
    have hlast := (claim (n - 1) hn1).trans (hlev ⟨n - 1, hn1⟩)
    have htop := partialBoxVolumeTopLeOne n (lam ⟨n - 1, hn1⟩ • C)
    have e : ((⟨n - 1, hn1⟩ : Fin n) : ℕ) + 1 = n := by
      show n - 1 + 1 = n
      omega
    rw [e] at hlast
    have hprod : ∏ i, min (lam i) (lam ⟨n - 1, hn1⟩) = ∏ i, lam i :=
      Finset.prod_congr rfl fun i _ =>
        min_eq_left (hmono (Fin.le_def.mpr (show (i : ℕ) ≤ n - 1 by omega)))
    rw [hprod] at hlast
    have hP : 0 ≤ ∏ i, lam i := Finset.prod_nonneg fun i _ => (hpos i).le
    have hfin : ENNReal.ofReal (∏ i, lam i) * volume C ≤ 1 := hlast.trans htop
    rw [mul_comm, ← ENNReal.toReal_ofReal hP, ← ENNReal.toReal_mul]
    exact ENNReal.toReal_le_of_le_ofReal zero_le_one (by simpa using hfin)

end Formalism.FN
end
end

-- bundled from Formalism.SuccessiveMinima.SuccessiveMinimaProofs.MinkowskiIILowerOf
section
open MeasureTheory Module Metric Set ZSpan
open scoped Pointwise ENNReal

noncomputable section

namespace Formalism.FN.LowerVolumeBound

lemma cross_mem {E : Type*} [AddCommGroup E] [Module ℝ E] {K : Set E} (hK : Convex ℝ K)
    (hs : ∀ x ∈ K, -x ∈ K) (h0 : (0 : E) ∈ K) {n : ℕ} (w : Fin n → E) (hw : ∀ i, w i ∈ K)
    (c : Fin n → ℝ) (hc : ∑ i, |c i| ≤ 1) : ∑ i, c i • w i ∈ K := by
  classical
  set s := ∑ i, |c i| with hsdef
  let p : Fin n → E := fun i => if 0 ≤ c i then w i else -w i
  have hp : ∀ i, p i ∈ K := fun i => by
    dsimp only [p]; split_ifs
    · exact hw i
    · exact hs _ (hw i)
  have hcp : ∀ i, c i • w i = |c i| • p i := fun i => by
    dsimp only [p]; split_ifs with h
    · rw [abs_of_nonneg h]
    · rw [abs_of_neg (not_le.mp h), neg_smul, smul_neg, neg_neg]
  have hs_nonneg : 0 ≤ s := Finset.sum_nonneg (fun i _ => abs_nonneg (c i))
  rcases hs_nonneg.eq_or_lt with hs0 | hs0
  · have hz : ∀ i, c i = 0 := fun i => abs_eq_zero.mp (le_antisymm
      ((Finset.single_le_sum (fun j _ => abs_nonneg (c j)) (Finset.mem_univ i)).trans hs0.symm.le)
      (abs_nonneg _))
    simpa [hz] using h0
  · have hx : ∑ i, (|c i| / s) • p i ∈ K :=
      hK.sum_mem (fun i _ => div_nonneg (abs_nonneg _) hs0.le)
        (by rw [← Finset.sum_div, div_self hs0.ne']) (fun i _ => hp i)
    have h2 := hK.smul_mem_of_zero_mem h0 hx ⟨hs0.le, hc⟩
    convert h2 using 1
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [smul_smul, mul_div_cancel₀ _ hs0.ne', hcp]

lemma covol_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [μ.IsAddHaarMeasure]
    (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]
    (bv : Basis (Fin (finrank ℝ E)) ℝ E) (hv : ∀ i, bv i ∈ L) :
    ZLattice.covolume L μ ≤ μ.real (parallelepiped bv) := by
  classical
  have hcard : Fintype.card (Free.ChooseBasisIndex ℤ L) = Fintype.card (Fin (finrank ℝ E)) := by
    rw [← finrank_eq_card_chooseBasisIndex, ZLattice.rank ℝ L, Fintype.card_fin]
  let bz : Basis (Fin (finrank ℝ E)) ℤ L :=
    (Free.chooseBasis ℤ L).reindex (Fintype.equivOfCardEq hcard)
  let b' : Basis (Fin (finrank ℝ E)) ℝ E := bz.ofZLatticeBasis ℝ L
  have hb' : ((↑) : L → E) ∘ bz = ⇑b' := by
    funext i; simp [b']
  have hk : ∃ k : ℤ, b'.det bv = k := by
    refine ⟨(Matrix.of fun i j => bz.repr ⟨bv j, hv j⟩ i).det, ?_⟩
    rw [Basis.det_apply, Int.cast_det]
    congr 1
    ext i j
    rw [Basis.toMatrix_apply, Matrix.map_apply, Matrix.of_apply]
    exact bz.ofZLatticeBasis_repr_apply ℝ L ⟨bv j, hv j⟩ i
  obtain ⟨k, hk⟩ := hk
  have hprod : bv.det b' * b'.det bv = 1 := by
    rw [Basis.det_mul_det, Basis.det_self]
  have hk0 : k ≠ 0 := by
    rintro rfl; simp [hk] at hprod
  have hdet : |bv.det b'| ≤ 1 := by
    have h1 : (1 : ℝ) ≤ |(k : ℝ)| := by
      rw [← Int.cast_abs]; exact_mod_cast Int.one_le_abs hk0
    have h2 : |bv.det b'| * |(k : ℝ)| = 1 := by rw [← abs_mul, ← hk, hprod, abs_one]
    nlinarith [abs_nonneg (bv.det b')]
  rw [ZLattice.covolume_eq_det_mul_measureReal L μ bz bv, hb',
    measureReal_congr (fundamentalDomain_ae_parallelepiped bv μ)]
  calc |bv.det b'| * μ.real (parallelepiped bv) ≤ 1 * μ.real (parallelepiped bv) := by
        gcongr
    _ = μ.real (parallelepiped bv) := one_mul _

end Formalism.FN.LowerVolumeBound
end
end

-- bundled from Formalism.SuccessiveMinima.SuccessiveMinimaProofs.NPUnit
section
namespace Formalism.FN
open Filter Topology

lemma unit_eps {K : Type*} [NormedField K] (b : ℕ → K) (r : ℝ) (hr : 0 < r) (hc : ConvOn b r)
    (hb : b ≠ 0) (hw : wdeg b r = 0) :
    ‖b 0‖ = gNorm b r ∧ 0 < gNorm b r ∧
    ∃ ε : ℝ, 0 ≤ ε ∧ ε < 1 ∧ ∀ k, 1 ≤ k → ‖b k‖ * r ^ k ≤ ε * gNorm b r := by
  obtain ⟨h0, hM⟩ := wdeg_spec b r hr hc hb
  rw [hw, pow_zero, mul_one] at h0
  refine ⟨h0, hM, ?_⟩
  have hle : ∀ k, ‖b k‖ * r ^ k ≤ gNorm b r := fun k => le_ciSup (gNorm_bdd_of_conv b r hc) k
  obtain ⟨k0, hk0⟩ := eventually_atTop.1
    ((hc : Tendsto (fun k : ℕ => ‖b k‖ * r ^ k) atTop (𝓝 0)).eventually
      (gt_mem_nhds (half_pos hM)))
  have hlt : ∀ k, 1 ≤ k → ‖b k‖ * r ^ k < gNorm b r := by
    intro k hk
    rcases (hle k).lt_or_eq with h | h
    · exact h
    · exfalso
      have hB : BddAbove {k : ℕ | ‖b k‖ * r ^ k = gNorm b r} := by
        refine ⟨k0, fun j hj => ?_⟩
        by_contra hc'
        push Not at hc'
        have h1 := hk0 j hc'.le
        have e : ‖b j‖ * r ^ j = gNorm b r := hj
        linarith
      have h2 : k ≤ wdeg b r := le_csSup hB h
      omega
  obtain ⟨j, -, hj⟩ := Finset.exists_max_image (Finset.range (k0 + 1))
    (fun k => ‖b (k + 1)‖ * r ^ (k + 1)) ⟨0, by simp⟩
  refine ⟨max (1 / 2) (‖b (j + 1)‖ * r ^ (j + 1) / gNorm b r), le_max_of_le_left (by norm_num),
    max_lt (by norm_num) ((div_lt_one hM).2 (hlt _ (by omega))), ?_⟩
  intro k hk
  rw [max_mul_of_nonneg _ _ hM.le]
  by_cases hkk : k ≤ k0 + 1
  · apply le_max_of_le_right
    rw [div_mul_cancel₀ _ hM.ne']
    obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    exact hj k' (by simp; omega)
  · apply le_max_of_le_left
    have := hk0 k (by omega)
    linarith

lemma unit_norm {K : Type} [NontriviallyNormedField K] [CompleteSpace K] [IsUltrametricDist K]
    (b : ℕ → K) (r : ℝ) (hr : 0 < r) (hc : ConvOn b r) (hb : b ≠ 0) (hw : wdeg b r = 0)
    (x : K) (hx : ‖x‖ ≤ r) : ‖evalS b x‖ = gNorm b r := by
  obtain ⟨h0, hM, ε, hε0, hε1, hε⟩ := unit_eps b r hr hc hb hw
  have hterm : ∀ k, ‖b k * x ^ k‖ ≤ ‖b k‖ * r ^ k := fun k => by
    rw [norm_mul, norm_pow]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hx k) (norm_nonneg _)
  have hsum : Summable (fun k => b k * x ^ k) := by
    apply NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero
    rw [Nat.cofinite_eq_atTop, tendsto_zero_iff_norm_tendsto_zero]
    exact squeeze_zero (fun k => norm_nonneg _) hterm hc
  have htail : ‖∑' k, b (k + 1) * x ^ (k + 1)‖ ≤ ε * gNorm b r :=
    IsUltrametricDist.norm_tsum_le_of_forall_le_of_nonneg (by positivity)
      (fun k => (hterm (k + 1)).trans (hε (k + 1) (by omega)))
  have hlt : ε * gNorm b r < gNorm b r := mul_lt_of_lt_one_left hM hε1
  unfold evalS
  rw [hsum.tsum_eq_zero_add, pow_zero, mul_one]
  rw [IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm, h0]
  · exact max_eq_left (htail.trans hlt.le)
  · rw [h0]; exact ne_of_gt (htail.trans_lt hlt)

lemma unit_inv {K : Type} [NontriviallyNormedField K] [IsUltrametricDist K]
    (b : ℕ → K) (r : ℝ) (hr : 0 < r) (hc : ConvOn b r) (hb : b ≠ 0) (hw : wdeg b r = 0) :
    ∃ u : ℕ → K, ConvOn u r ∧ cmul b u = fun n => if n = 0 then 1 else 0 := by
  obtain ⟨h0, hM, ε, hε0, hε1, hε⟩ := unit_eps b r hr hc hb hw
  have hb0 : b 0 ≠ 0 := by
    intro h; rw [h, norm_zero] at h0; linarith
  set M := gNorm b r with hMdef
  set B : PowerSeries K := PowerSeries.mk b with hB
  set u : ℕ → K := fun n => PowerSeries.coeff n B⁻¹ with hu
  have hmul : cmul b u = fun n => if n = 0 then 1 else 0 := by
    funext n
    have h := congrArg (PowerSeries.coeff n)
      (PowerSeries.mul_inv_cancel B (by rw [hB, PowerSeries.constantCoeff_mk]; exact hb0))
    rw [PowerSeries.coeff_mul, PowerSeries.coeff_one,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ
        (fun i j => PowerSeries.coeff i B * PowerSeries.coeff j B⁻¹)] at h
    simpa [cmul, u, B, PowerSeries.coeff_mk] using h
  refine ⟨u, ?_, hmul⟩

  have key : ∀ n, 1 ≤ n → ∀ C : ℝ, 0 ≤ C →
      (∀ i < n, (‖b (i + 1)‖ * r ^ (i + 1)) * (‖u (n - (i + 1))‖ * r ^ (n - (i + 1))) ≤ C) →
      M * (‖u n‖ * r ^ n) ≤ C := by
    intro n hn C hC h
    have hrec : b 0 * u n = -∑ i ∈ Finset.range n, b (i + 1) * u (n - (i + 1)) := by
      have e := congrFun hmul n
      simp only [cmul, if_neg (show n ≠ 0 by omega)] at e
      rw [Finset.sum_range_succ', Nat.sub_zero] at e
      linear_combination e
    have hrn : 0 < r ^ n := pow_pos hr n
    have hs : ‖∑ i ∈ Finset.range n, b (i + 1) * u (n - (i + 1))‖ ≤ C / r ^ n := by
      apply IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (div_nonneg hC hrn.le)
      intro i hi
      have hi' := Finset.mem_range.1 hi
      rw [le_div_iff₀ hrn, norm_mul]
      have e : r ^ n = r ^ (i + 1) * r ^ (n - (i + 1)) := by
        rw [← pow_add]; congr 1; omega
      rw [e]
      calc ‖b (i + 1)‖ * ‖u (n - (i + 1))‖ * (r ^ (i + 1) * r ^ (n - (i + 1)))
          = (‖b (i + 1)‖ * r ^ (i + 1)) * (‖u (n - (i + 1))‖ * r ^ (n - (i + 1))) := by ring
        _ ≤ C := h i hi'
    have h3 : M * ‖u n‖ ≤ C / r ^ n := by
      rw [← h0, ← norm_mul, hrec, norm_neg]; exact hs
    rw [le_div_iff₀ hrn] at h3
    calc M * (‖u n‖ * r ^ n) = M * ‖u n‖ * r ^ n := by ring
      _ ≤ C := h3
  have hu0 : M * (‖u 0‖ * r ^ 0) = 1 := by
    have e : b 0 * u 0 = 1 := by simpa [cmul] using congrFun hmul 0
    rw [pow_zero, mul_one, ← h0, ← norm_mul, e, norm_one]

  have decay : ∀ δ : ℝ, 0 ≤ δ → δ ≤ 1 → ∀ k0 : ℕ, 1 ≤ k0 →
      (∀ k, k0 ≤ k → ‖b k‖ * r ^ k ≤ δ * M) →
      ∀ n, M * (‖u n‖ * r ^ n) ≤ max δ (ε ^ (n / k0)) := by
    intro δ hδ0 hδ1 k0 hk0 hbk n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · rw [hu0]; simp
    apply key n hn _ (le_max_of_le_left hδ0)
    intro i hi
    have hv : 0 ≤ ‖u (n - (i + 1))‖ * r ^ (n - (i + 1)) := by positivity
    have hIH := ih (n - (i + 1)) (by omega)
    by_cases hik : k0 ≤ i + 1
    · have hX1 : max δ (ε ^ ((n - (i + 1)) / k0)) ≤ 1 :=
        max_le hδ1 (pow_le_one₀ hε0 hε1.le)
      calc (‖b (i + 1)‖ * r ^ (i + 1)) * (‖u (n - (i + 1))‖ * r ^ (n - (i + 1)))
          ≤ (δ * M) * (‖u (n - (i + 1))‖ * r ^ (n - (i + 1))) :=
            mul_le_mul_of_nonneg_right (hbk _ hik) hv
        _ = δ * (M * (‖u (n - (i + 1))‖ * r ^ (n - (i + 1)))) := by ring
        _ ≤ δ * 1 := mul_le_mul_of_nonneg_left (hIH.trans hX1) hδ0
        _ = δ := mul_one _
        _ ≤ _ := le_max_left _ _
    · have hm : n / k0 ≤ (n - (i + 1)) / k0 + 1 := by
        rw [← Nat.add_div_right _ (by omega : 0 < k0)]
        exact Nat.div_le_div_right (by omega)
      calc (‖b (i + 1)‖ * r ^ (i + 1)) * (‖u (n - (i + 1))‖ * r ^ (n - (i + 1)))
          ≤ (ε * M) * (‖u (n - (i + 1))‖ * r ^ (n - (i + 1))) :=
            mul_le_mul_of_nonneg_right (hε _ (by omega)) hv
        _ = ε * (M * (‖u (n - (i + 1))‖ * r ^ (n - (i + 1)))) := by ring
        _ ≤ ε * max δ (ε ^ ((n - (i + 1)) / k0)) := mul_le_mul_of_nonneg_left hIH hε0
        _ = max (ε * δ) (ε ^ ((n - (i + 1)) / k0 + 1)) := by
            rw [mul_max_of_nonneg _ _ hε0, pow_succ']
        _ ≤ max δ (ε ^ (n / k0)) :=
            max_le_max (mul_le_of_le_one_left hδ0 hε1.le) (pow_le_pow_of_le_one hε0 hε1.le hm)

  show Tendsto (fun k : ℕ => ‖u k‖ * r ^ k) atTop (𝓝 0)
  rw [Metric.tendsto_atTop]
  intro η hη
  have hηM : 0 < η * M / 2 := by positivity
  set δ := min 1 (η * M / 2) with hδ
  have hδ0 : 0 < δ := lt_min one_pos hηM
  obtain ⟨K1, hK1⟩ := eventually_atTop.1
    ((hc : Tendsto (fun k : ℕ => ‖b k‖ * r ^ k) atTop (𝓝 0)).eventually
      (gt_mem_nhds (mul_pos hδ0 hM)))
  set k0 := max K1 1 with hk0
  obtain ⟨m, hm⟩ := exists_pow_lt_of_lt_one hηM hε1
  refine ⟨m * k0, fun n hn => ?_⟩
  have hD := decay δ hδ0.le (min_le_left _ _) k0 (le_max_right _ _)
    (fun k hk => (hK1 k (le_trans (le_max_left _ _) hk)).le) n
  have hmn : m ≤ n / k0 := (Nat.le_div_iff_mul_le (by omega)).2 hn
  have hpow : ε ^ (n / k0) ≤ ε ^ m := pow_le_pow_of_le_one hε0 hε1.le hmn
  have hv : 0 ≤ ‖u n‖ * r ^ n := by positivity
  rw [Real.dist_eq, sub_zero, abs_of_nonneg hv]
  have hbound : M * (‖u n‖ * r ^ n) < η * M := by
    calc M * (‖u n‖ * r ^ n) ≤ max δ (ε ^ (n / k0)) := hD
      _ ≤ max (η * M / 2) (ε ^ m) := max_le_max (min_le_right _ _) hpow
      _ < η * M := max_lt (by linarith) (by linarith)
  nlinarith

end Formalism.FN
end

-- bundled from Formalism.SuccessiveMinima.SuccessiveMinimaProofs.NPWDivision
section
open Filter Topology Polynomial

noncomputable section

namespace Formalism.FN.WDiv

section General
variable {K : Type} [NontriviallyNormedField K] [IsUltrametricDist K]

lemma term_eq (a b : ℕ → K) (r : ℝ) {n i : ℕ} (hi : i ≤ n) :
    ‖a i * b (n - i)‖ * r ^ n = (‖a i‖ * r ^ i) * (‖b (n - i)‖ * r ^ (n - i)) := by
  rw [norm_mul]
  have : r ^ n = r ^ i * r ^ (n - i) := by rw [← pow_add, Nat.add_sub_cancel' hi]
  rw [this]; ring

lemma series_bound (u : ℕ → ℕ → K) {r : ℝ} (hr : 0 < r) (j : ℕ) {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ i, ‖u i j‖ * r ^ j ≤ C) : ‖∑' i, u i j‖ * r ^ j ≤ C := by
  rw [← le_div_iff₀ (pow_pos hr j)]
  exact IsUltrametricDist.norm_tsum_le_of_forall_le_of_nonneg (by positivity)
    fun i => (le_div_iff₀ (pow_pos hr j)).2 (h i)

variable [CompleteSpace K]

end General

end Formalism.FN.WDiv

namespace Formalism.FN.WDiv

section PolyDiv
variable {K : Type} [NontriviallyNormedField K] [IsUltrametricDist K]

def cN (G : K[X]) (N : ℕ) (P : K[X]) : K := P.coeff N / G.coeff N

def QR (G : K[X]) (N : ℕ) : ℕ → K[X] × K[X]
  | 0 => (C (cN G N 1), 1 - C (cN G N 1) * G)
  | m + 1 => (X * (QR G N m).1 + C (cN G N (X * (QR G N m).2)),
      X * (QR G N m).2 - C (cN G N (X * (QR G N m).2)) * G)

variable (G : K[X]) (N : ℕ) {r M : ℝ} (hr : 0 < r) (hM : 0 < M)
  (hGN : ‖G.coeff N‖ * r ^ N = M) (hGle : ∀ j, ‖G.coeff j‖ * r ^ j ≤ M)
  (hGhi : ∀ j, N < j → G.coeff j = 0)
include hr hM hGN hGle hGhi

end PolyDiv

end Formalism.FN.WDiv

namespace Formalism.FN.WDiv

section SeriesDiv
variable {K : Type} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]

def Dq (G : K[X]) (N : ℕ) (f : ℕ → K) (j : ℕ) : K := ∑' m, f m * (QR G N m).1.coeff j

def DR (G : K[X]) (N : ℕ) (f : ℕ → K) (j : ℕ) : K := ∑' m, f m * (QR G N m).2.coeff j

variable (G : K[X]) (N : ℕ) {r M : ℝ} (hr : 0 < r) (hM : 0 < M)
  (hGN : ‖G.coeff N‖ * r ^ N = M) (hGle : ∀ j, ‖G.coeff j‖ * r ^ j ≤ M)
  (hGhi : ∀ j, N < j → G.coeff j = 0)
include hr hM hGN hGle hGhi

end SeriesDiv

section Main
variable {K : Type} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]

def iterF (G : K[X]) (N : ℕ) (H f : ℕ → K) : ℕ → ℕ → K
  | 0 => f
  | i + 1 => fun n => -(cmul (Dq G N (iterF G N H f i)) H n)

omit [CompleteSpace K] in
lemma exists_eps (g : ℕ → K) (r : ℝ) (hr : 0 < r) (hg : ConvOn g r) (hne : g ≠ 0) :
    ∃ ε : ℝ, 0 ≤ ε ∧ ε < 1 ∧ ∀ k, wdeg g r < k → ‖g k‖ * r ^ k ≤ ε * gNorm g r := by
  obtain ⟨-, hM⟩ := wdeg_spec g r hr hg hne
  have hle : ∀ k, ‖g k‖ * r ^ k ≤ gNorm g r := fun k => le_ciSup (gNorm_bdd_of_conv g r hg) k
  obtain ⟨K0, hK0⟩ := eventually_atTop.1
    ((hg : Tendsto _ atTop _).eventually (eventually_le_nhds (half_pos hM)))
  have hbdd : BddAbove {k : ℕ | ‖g k‖ * r ^ k = gNorm g r} := ⟨K0, fun k hk => by
    simp only [Set.mem_ofPred_eq] at hk
    by_contra h; push Not at h
    have := hK0 k h.le
    rw [hk] at this; linarith⟩
  have hlt : ∀ k, wdeg g r < k → ‖g k‖ * r ^ k < gNorm g r := by
    intro k hk
    refine lt_of_le_of_ne (hle k) fun h => ?_
    have : k ≤ wdeg g r := le_csSup hbdd h
    omega
  obtain ⟨k1, hk1T, hk1⟩ := Finset.exists_max_image (Finset.Icc (wdeg g r + 1) (max K0 (wdeg g r + 1)))
    (fun k => ‖g k‖ * r ^ k) ⟨wdeg g r + 1, by simp⟩
  have hk1lt : ‖g k1‖ * r ^ k1 < gNorm g r := hlt k1 (by simp at hk1T; omega)
  refine ⟨max (‖g k1‖ * r ^ k1 / gNorm g r) (1 / 2), le_max_of_le_right (by norm_num),
    max_lt ((div_lt_one hM).2 hk1lt) (by norm_num), fun k hk => ?_⟩
  rw [max_mul_of_nonneg _ _ hM.le]
  by_cases hkK : k ≤ max K0 (wdeg g r + 1)
  · have := hk1 k (by simp; omega)
    exact le_max_of_le_left (by rw [div_mul_cancel₀ _ hM.ne']; exact this)
  · exact le_max_of_le_right (by have := hK0 k (by omega); linarith)

end Main

end Formalism.FN.WDiv

namespace Formalism.FN

end Formalism.FN
end
end

