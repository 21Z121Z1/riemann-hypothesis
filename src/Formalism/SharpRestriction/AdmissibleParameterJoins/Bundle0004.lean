import Formalism.LocalRingCardinality.Bundle0006
import Formalism.SharpRestriction.SmoothDesignExistence.DGamSmooth
import Formalism.SharpRestriction.CuspSpanNormBounds.CongruenceAtSplitFrobeniusHolds
import Formalism.SharpRestriction.CuspSpanNormBounds.NonGenericAndKTwoTheorems
import Formalism.SharpRestriction.Divisibility.ZetaProductPairs
import Formalism.SharpRestriction.Divisibility.LocalQuadraticParts
import Formalism.SharpRestriction.GlobalSchurBounds.CMFieldLemmas
import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.Bundle0001
import Formalism.FrobeniusOrbits.HostCorollaries
import Formalism.SharpRestriction.GlobalSchurBounds.ProductFirstZerothParts
import Formalism.SharpRestriction.GlobalSchurBounds.TaylorLogMetric
import Formalism.LocalRingCardinality.Lemmas
import Formalism.SharpRestriction.AdmissibleParameterJoins.SumLogPrimeFactorsLe
import Formalism.SharpRestriction.GlobalSchurBounds.StandardLattice
import Formalism.SharpRestriction.GlobalSchurBounds.Joints
import Formalism.SharpRestriction.Bundle0001

-- bundled from Formalism.SharpRestriction.AdmissibleParameterJoins.DGamMink
section
namespace Formalism.MainNotions.J

open Formalism.BasicNotions

private lemma prime_le_succ_of_dvd_minkM' {n p : ℕ} (hp : p.Prime) (h : p ∣ minkM n) : p ≤ n + 1 := by
  have h' : p ∣ ∏ q ∈ (Finset.range (n + 2)).filter Nat.Prime, q ^ Formalism.HermitianLatticeCounting.S6.minkowskiExp n q := h
  rcases (Prime.dvd_finset_prod_iff hp.prime _).1 h' with ⟨q, hq, hdvd⟩
  rw [Finset.mem_filter, Finset.mem_range] at hq
  have hpq := (Nat.prime_dvd_prime_iff_eq hp hq.2).1 (hp.dvd_of_dvd_pow hdvd)
  omega

theorem dGamSmooth_of_dvd {eps : ℝ} (Fm : FamP eps)
    (h : ∃ x0 : ℝ, ∀ x ≥ x0, ∀ (i : Fm.Ix x) u,
      ((Fm.D x i).mem u).C.DGam ∣ minkM (2 * (Fm.D x i).R.f * (Fm.D x i).R.N (Fm.D x i).R.m)) :
    Pk.DGamSmooth Fm := by
  obtain ⟨x0, hx0⟩ := h
  exact ⟨x0, fun x hx i u p hp hpd => prime_le_succ_of_dvd_minkM' hp (dvd_trans hpd (hx0 x hx i u))⟩

end Formalism.MainNotions.J
end

-- bundled from Formalism.SharpRestriction.AdmissibleParameterJoins.DIVfromGLc
section
noncomputable section

namespace Formalism.MainNotions.J

open Formalism.BasicNotions Formalism.FrobeniusOrbits Formalism.MainNotions.GlobalTheoryTheory

theorem orbits_and_orders_hold : LocalQuadraticParts.HostOrbitConditions := by
  exact ⟨Formalism.FrobeniusOrbits.hostOrbits, Formalism.FrobeniusOrbits.hostOrbitsPlaces, Formalism.FrobeniusOrbits.hostOrbitsFin.2.2.1, Formalism.FrobeniusOrbits.hostOrders⟩

theorem lemma_on_tops_holds : LocalQuadraticParts.TopsChoiceLemma := by
  exact Formalism.FrobeniusOrbits.Final.host_places.2.2.1

theorem ord_hclP (e l : ℕ) (hl : l.Prime) (h2 : l ≠ 2) :
    orderOf (LocalQuadraticParts.hclP e l) = ordH (hOf e l) := by
  rw [← Formalism.MainNotions.UnusedSlot33.SlopeTestRemainingChoices.ordH_eq]
  congr 1
  unfold LocalQuadraticParts.hclP hOf
  have hc2 : l.Coprime 2 := (Nat.coprime_primes hl Nat.prime_two).2 h2
  have hc : l.Coprime (2 ^ (e + 2)) := Nat.Coprime.pow_right _ hc2
  rw [dif_pos hc, dif_pos hc2]

theorem dyadic_order_consequences (D : D7) (C : ℝ) (h : UnusedSlot33.Conclusion4 D C) : LocalQuadraticParts.OrderConsequences D C := by
  obtain ⟨-, h2, h3, h4⟩ := h
  have hc : ((2 ^ D.R.e : ℕ) : ℝ) = (2 : ℝ) ^ D.R.e := by norm_num
  refine ⟨fun J l hJ hl hl2 ho => ?_, fun J S hJ hS => ?_, fun J Y S hJ hY hS => ?_⟩
  · have h5 := h2 J (by exact_mod_cast hJ) l hl hl2 (by rw [← ord_hclP _ l hl hl2]; exact_mod_cast ho)
    rw [hc] at h5
    exact h5
  · have h5 := h3 J (by exact_mod_cast hJ) S (fun l hlS => ⟨(hS l hlS).1, (hS l hlS).2.1, by
      rw [← ord_hclP _ l (hS l hlS).1 (hS l hlS).2.1]; exact_mod_cast (hS l hlS).2.2⟩)
    rw [hc] at h5
    exact h5
  · have hsub : S ⊆ (Finset.range (⌊Y⌋₊ + 1)).filter
        (fun l => l.Prime ∧ l ≠ 2 ∧ (ordH (hOf D.R.e l) : ℝ) ≤ J) := by
      intro l hlS
      obtain ⟨hl, hl2, hlY, ho⟩ := hS l hlS
      rw [Finset.mem_filter, Finset.mem_range]
      refine ⟨Nat.lt_succ_of_le (Nat.le_floor hlY), hl, hl2, ?_⟩
      rw [← ord_hclP _ l hl hl2]
      exact_mod_cast ho
    have h5 := h4 J (by exact_mod_cast hJ) Y
    rw [hc] at h5
    refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg hsub fun l _ _ => ?_) h5
    exact div_nonneg (Real.log_natCast_nonneg l) (Nat.cast_nonneg l)

theorem family_dyadic_order_consequences {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) (C : ℝ)
    (h : ∀ x (i : Fm.Ix x), UnusedSlot33.Conclusion4 (Fm.D x i) C) : LocalQuadraticParts.SmallOrderPrimeBoundsFamily Fm := by
  exact ⟨C, fun x i => dyadic_order_consequences _ C (h x i)⟩

theorem full_rank_family_of_eventually_nuFull {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps)
    (h : ∃ x0 : ℝ, ∀ x ≥ x0, ∀ i : Fm.Ix x, (Fm.D x i).NuFull) : LocalQuadraticParts.FullRankFamily Fm := by
  obtain ⟨x0, hx0⟩ := h
  refine ⟨x0, fun x hx hx1 i => ⟨⟨Fm.nprimeDef x hx1 i, Fm.nuDef x hx1 i, fun p hp => Fm.drop_iff x hx1 i p hp,
    fun w => Fm.fills x hx1 i w⟩, hx0 x hx i⟩⟩

end Formalism.MainNotions.J
end
end

-- bundled from Formalism.SharpRestriction.AdmissibleParameterJoins.DIVfromGLd
section
noncomputable section

namespace Formalism.MainNotions.J

open Formalism.BasicNotions

def LevelPrimeBasicClauses (D : D7) : Prop :=
  ∀ u,
    ((D.mem u).A.du : ℝ) = (1 - 1 / (((D.mem u).A.T : ℝ) - 1)) ^ D.R.f * (D.duS u : ℝ) ∧
    (LocalQuadraticParts.MuH D u).mu = ((D.fm u).lat 0).mu -
      (D.R.f : ℝ) * Real.log (((D.mem u).A.T : ℝ) - 1) / (((D.mem u).A.T : ℝ) - 2) ∧
    (LocalQuadraticParts.MuH D u).muMax ≤ ((D.fm u).lat 0).muMax

theorem levelPrimeClauses_of_second (D : D7) (h : ∀ u, product_first_zeroth_parts.Conclusion2 D u) : LevelPrimeBasicClauses D := by
  intro u
  obtain ⟨h1, h2, h3, -⟩ := h u
  obtain ⟨s1, s2, -⟩ := D.ram_slopes u
  refine ⟨?_, ?_, ?_⟩
  · have h1' := congrArg (fun q : ℚ => (q : ℝ)) h1
    push_cast at h1'
    rw [h1']
    ring
  · rw [show (LocalQuadraticParts.MuH D u).mu = (D.fm u).ramLat.mu from s1]
    exact h2
  · rw [show (LocalQuadraticParts.MuH D u).muMax = (D.fm u).ramLat.muMax from s2]
    exact h3

theorem sum_lwP_e_le (D : D7) (p : ℕ) (hp : p.Prime) (S : Finset D.what₂.places.Pl)
    (hS : ∀ w ∈ S, D.what₂.places.resChar w = p) :
    ∑ w ∈ S, SizeData₂.lwP w * (D.what₂.places.ramIdx w : ℝ) ≤ Real.log p := by
  classical
  obtain ⟨T, hT⟩ := finite_places_over (K := D.what₂.LL) p hp
  have h1 : ∑ w ∈ S, SizeData₂.lwP w * (D.what₂.places.ramIdx w : ℝ) =
      ∑ v ∈ S.map D.plEq.toEmbedding, lw D.what₂.LL v * (eWL D.what₂.LL v : ℝ) := by
    rw [Finset.sum_map]
    refine Finset.sum_congr rfl (fun w _ => ?_)
    rw [D.ram_eq w]; rfl
  have hsub : S.map D.plEq.toEmbedding ⊆ T := by
    intro v hv
    obtain ⟨w, hw, rfl⟩ := Finset.mem_map.1 hv
    rw [hT]
    have := resChar_mem D w
    rw [hS w hw] at this
    exact this
  rw [h1, ← sum_lw_e p hp T hT]
  exact Finset.sum_le_sum_of_subset_of_nonneg hsub
    (fun v _ _ => mul_nonneg (lw_nonneg v) (Nat.cast_nonneg _))

def LenAtT (D : D7) (L : SizeData₂ D) : Prop :=
  ∀ u w, D.what₂.places.resChar w = (D.mem u).A.T →
    DV.lenLoc (D.plEq w) (L.NuLat u) (DV.MramL D u) =
      product_first_zeroth_parts.len D u w (product_first_zeroth_parts.Sram D u w) (product_first_zeroth_parts.Nlam D u w)

def LocSpan (D : D7) : Prop :=
  ∀ u w, ∀ y ∈ (D.fm u).S 0 w, InLoc (D.plEq w) ((D.fm u).lat 0).L y

def LevelPrimeSizeBounds (D : D7) (L : SizeData₂ D) (C1 : ℝ) : Prop :=
  ∀ u w, product_first_zeroth_parts.OverT D u w → ∑ v ∈ product_first_zeroth_parts.VV D u w,
      ((product_first_zeroth_parts.amax D u : ℝ) / D.R.k + 2 * product_first_zeroth_parts.Wt D u ((D.fm u).tauOf w v) + D.R.k +
        (D.fm u).bTop ((D.fm u).tauOf w v)) ≤
    C1 * LocalQuadraticParts.nTT D * (L.sc.a / D.R.k + L.sc.b')

theorem levelPrime_summary_of_fifth (D : D7) (L : SizeData₂ D) (C C1 : ℝ) (h2 : ∀ u, product_first_zeroth_parts.Conclusion2 D u)
    (h5 : ∀ u, product_first_zeroth_parts.Conclusion5 D u C) (hNu : DV.NuDef D L) (hAtT : NuAtTDef D L) (hLoc : LocSpan D)
    (hLen : LenAtT D L) (hS : LevelPrimeSizeBounds D L C1)
    (hSet : ∀ u, product_first_zeroth_parts.HidaSetting D u) (hC1 : 0 ≤ C1) : LocalQuadraticParts.adm26 L (4 * C1) := by
  classical
  intro u
  obtain ⟨c1, c2, c3⟩ := levelPrimeClauses_of_second D h2 u
  refine ⟨c1, c2, c3, ?_, ?_⟩
  · intro w hw x hx
    have h1 : InLoc (D.plEq w) (L.NuLat u) x :=
      ⟨1, fun h => (D.plEq w).isPrime.ne_top ((Ideal.eq_top_iff_one _).mpr h), by rwa [one_smul]⟩
    have h2 : D.nuIn u x ∈ product_first_zeroth_parts.Nlam D u w := (hAtT u w hw x).mp h1
    have h3 : D.nuIn u x ∈ (D.fm u).S 0 w := ((h5 u w hw).1 h2).1
    obtain ⟨s, hs, hsx⟩ := hLoc u w _ h3
    refine ⟨s, hs, ?_⟩
    rw [pow_zero, Ideal.one_eq_top, Submodule.top_smul]
    show (D.nuIn u).restrictScalars (NumberField.RingOfIntegers D.what₂.LL) (s • x) ∈ ((D.fm u).lat 0).L
    rw [map_smul]
    exact hsx
  · intro F hFT
    have hx0 : 0 < L.sc.x := lt_trans zero_lt_one L.sc.one_lt_alt
    have ha : 0 < L.sc.a := mul_pos hx0 (Real.exp_pos _)
    have hb' : 0 < L.sc.b' := div_pos ha (Real.exp_pos _)
    have hk : (0 : ℝ) ≤ D.R.k := Nat.cast_nonneg _
    have hm : (0 : ℝ) ≤ D.R.m := Nat.cast_nonneg _
    have hd : (0 : ℝ) ≤ D.duS u := Nat.cast_nonneg _
    have hTT : (0 : ℝ) ≤ LocalQuadraticParts.nTT D := Nat.cast_nonneg _
    have hlT : 0 ≤ Real.log ((D.mem u).A.T : ℝ) := Real.log_natCast_nonneg _
    set B : ℝ := C1 * LocalQuadraticParts.nTT D * (L.sc.a / D.R.k + L.sc.b') with hB
    have hB0 : 0 ≤ B := by positivity
    have hterm : ∀ w ∈ F, SizeData₂.sz w (L.lenMN u w) ≤
        (SizeData₂.lwP w * (D.what₂.places.ramIdx w : ℝ)) * (2 * (D.R.m * D.duS u * B)) := by
      intro w hw
      have hwT : D.what₂.places.resChar w = (D.mem u).A.T := hFT w hw
      obtain ⟨-, -, n, hn, hle⟩ := h5 u w hwT
      have hl := hNu.2.2 u w n (by rw [hLen u w hwT, hn])
      have hlw := logWeight_nonneg w
      have he : (0 : ℝ) ≤ D.what₂.places.ramIdx w := Nat.cast_nonneg _
      have hSw := hS u w hwT
      have h1 : (n : ℝ) ≤ (D.what₂.places.ramIdx w : ℝ) * (D.R.m * D.duS u * B) :=
        le_trans hle (by gcongr)
      unfold SizeData₂.sz
      calc 2 * SizeData₂.lwP w * ((D.what₂.places.ramIdx w : ℝ) * (L.lenMN u w : ℝ))
          = 2 * SizeData₂.lwP w * (n : ℝ) := by rw [hl]; ring
        _ ≤ 2 * SizeData₂.lwP w * ((D.what₂.places.ramIdx w : ℝ) * (D.R.m * D.duS u * B)) := by gcongr
        _ = _ := by ring
    have hsum : ∑ w ∈ F, SizeData₂.sz w (L.lenMN u w) ≤
        Real.log ((D.mem u).A.T : ℝ) * (2 * (D.R.m * D.duS u * B)) := by
      refine le_trans (Finset.sum_le_sum hterm) ?_
      rw [← Finset.sum_mul]
      exact mul_le_mul_of_nonneg_right
        (sum_lwP_e_le D _ (D.mem u).A.T_prime F hFT) (by positivity)

    have hN1 : 1 ≤ D.R.N D.R.m := by have := D.R.m_add_three_le_k; unfold Ranks.N; omega
    have hTf : 2 * D.R.f + 1 < (D.mem u).A.T := by
      have h := (hSet u).1
      have : 2 * D.R.f ≤ 2 * D.R.f * D.R.N D.R.m := Nat.le_mul_of_pos_right _ hN1
      omega
    have hTfR : 2 * (D.R.f : ℝ) + 1 < (D.mem u).A.T := by exact_mod_cast hTf
    have hf : (0 : ℝ) ≤ D.R.f := Nat.cast_nonneg _
    have hT1 : 0 < ((D.mem u).A.T : ℝ) - 1 := by linarith
    have hT2 : (2 : ℝ) ≤ (D.mem u).A.T := by exact_mod_cast (D.mem u).A.T_prime.two_le
    have hr : (1 / 2 : ℝ) ≤ (1 - 1 / (((D.mem u).A.T : ℝ) - 1)) ^ D.R.f := by
      have hb := one_add_mul_le_pow (a := -(1 / (((D.mem u).A.T : ℝ) - 1))) (by
        have : 1 / (((D.mem u).A.T : ℝ) - 1) ≤ 1 := by
          rw [div_le_one hT1]; linarith
        linarith) D.R.f
      have h3 : (D.R.f : ℝ) * (1 / (((D.mem u).A.T : ℝ) - 1)) ≤ 1 / 2 := by
        rw [mul_one_div, div_le_iff₀ hT1]; linarith
      have h4 : (1 + -(1 / (((D.mem u).A.T : ℝ) - 1))) = 1 - 1 / (((D.mem u).A.T : ℝ) - 1) := by ring
      rw [h4] at hb
      linarith
    have hgoal : (4 * C1) * LocalQuadraticParts.nTT D * D.R.m * (L.sc.a / D.R.k + L.sc.b') *
        Real.log ((D.mem u).A.T : ℝ) = 4 * (D.R.m * B * Real.log ((D.mem u).A.T : ℝ)) := by
      rw [hB]; ring
    rw [hgoal]
    rcases eq_or_lt_of_le hd with h0 | h0
    · rw [c1, ← h0, mul_zero, div_zero]; positivity
    · have hdu : 0 < ((D.mem u).A.du : ℝ) := by rw [c1]; positivity
      rw [div_le_iff₀ hdu]
      refine le_trans hsum ?_
      rw [c1]
      have : (D.duS u : ℝ) * (1 / 2) ≤ (1 - 1 / (((D.mem u).A.T : ℝ) - 1)) ^ D.R.f * (D.duS u : ℝ) := by
        rw [mul_comm]; gcongr
      have hP : 0 ≤ D.R.m * B * Real.log ((D.mem u).A.T : ℝ) := by positivity
      nlinarith

theorem family_levelPrime_summary {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) (C C1 : ℝ) (hC1 : 0 ≤ C1)
    (hE : ∃ x0 : ℝ, ∀ x ≥ x0, ∀ i : Fm.Ix x,
      (∀ u, product_first_zeroth_parts.Conclusion2 (Fm.D x i) u) ∧ (∀ u, product_first_zeroth_parts.Conclusion5 (Fm.D x i) u C) ∧ LocSpan (Fm.D x i) ∧
      LenAtT (Fm.D x i) (Fm.L x i) ∧
      LevelPrimeSizeBounds (Fm.D x i) (Fm.L x i) C1 ∧ ∀ u, product_first_zeroth_parts.HidaSetting (Fm.D x i) u) :
    LocalQuadraticParts.LevelTFamily Fm := by
  obtain ⟨x0, hx0⟩ := hE
  refine ⟨4 * C1, max x0 (Fm.x1 + 1), fun x hx i => ?_⟩
  have hxx0 : x0 ≤ x := le_trans (le_max_left _ _) hx
  have hx1 : Fm.x1 < x := by
    have := le_trans (le_max_right x0 (Fm.x1 + 1)) hx
    linarith
  obtain ⟨h2, h5, hLoc, hLen, hS, hSet⟩ := hx0 x hxx0 i
  exact levelPrime_summary_of_fifth (Fm.D x i) (Fm.L x i) C C1 h2 h5 (Fm.nuDef x hx1 i) (Fm.ex x hx1 i).lat.atT hLoc hLen hS
    hSet hC1

end Formalism.MainNotions.J
end
end

-- bundled from Formalism.SharpRestriction.AdmissibleParameterJoins.DIVfromGLe
section
noncomputable section

namespace Formalism.MainNotions.J

open Formalism.BasicNotions Formalism.BasicNotions.DV

def RankHyp (D : D7) : Prop :=
  StandardLattice.GBig D ∧ (∀ i, StandardLattice.SplitsF D (D.host.g i)) ∧
    ∀ u : D.what₂.Word, StandardLattice.SplitsF D (D.mem u).A.T ∧ StandardLattice.Mu0Tie D u

def CountTie (D : D7) : Prop :=
  (∀ u, ((D.mem u).A.duStar : ℝ) = StandardLattice.duStarU D u) ∧ D.what₂.Dstar = StandardLattice.DstarD D

theorem exp_logXuD (D : D7) (hT : CountTie D) (u : D.what₂.Word) :
    Real.exp (StandardLattice.logXuD D u) = (D.mem u).A.Xu := by
  obtain ⟨hT1, hT2⟩ := hT
  have hpos : 0 < (D.mem u).A.Dstar / ((D.mem u).A.duStar : ℝ) :=
    div_pos (D.mem u).A.Dstar_pos (by exact_mod_cast (D.mem u).A.duStar_pos)
  unfold StandardLattice.logXuD StandardLattice.logXu
  rw [← hT1 u, ← hT2, ← D.Dstar_eq u]
  unfold Formalism.BasicNotions.ColumnsAtT.Xu
  rw [Real.rpow_def_of_pos hpos, mul_comm]

theorem rank_count_bound_of_data (D : D7) (L : SizeData₂ D) (Lv : LevelData D) (C0 C : ℝ) (Δ : ℝ)
    (h4 : StandardLattice.Conclusion4f D Lv) (h5c : StandardLattice.TorusPairsWithVariant D L.sc C0 C) (h5v : StandardLattice.VandermondeVariationBound D L.sc C0 C)
    (hB : StandardLattice.DataB D L.sc C0 Δ (fun j ρ => wSz D (j + 1) ρ))
    (hR : RankHyp D) (hT : CountTie D) (hWs : Formalism.MainNotions.SizeWords L) :
    LocalQuadraticParts.HerrExtensionClause L (max C (Real.exp C)) := by
  obtain ⟨hT1, hT2⟩ := hT
  obtain ⟨hG, hSp, hU⟩ := hR
  have hL : 0 < L.sc.L := by
    obtain ⟨hv, hlv, -⟩ := hB
    have hv1 : 1 < D.host.v := lt_of_lt_of_le (by linarith [Real.pi_gt_three]) hv
    linarith [Real.log_pos hv1]
  have hk : 5 ≤ D.R.k := by
    have := D.R.two_le_m
    have := D.R.m_add_three_le_k
    omega
  have hCC : C ≤ max C (Real.exp C) := le_max_left _ _
  have hCe : Real.exp C ≤ max C (Real.exp C) := le_max_right _ _
  have hCpos : 0 < max C (Real.exp C) := lt_of_lt_of_le (Real.exp_pos C) hCe
  have hXu : ∀ u, Real.log (D.mem u).A.Xu = StandardLattice.logXuD D u := by
    intro u
    rw [← exp_logXuD D ⟨hT1, hT2⟩ u, Real.log_exp]
  unfold LocalQuadraticParts.HerrExtensionClause
  refine ⟨fun u => ?_, fun u u' => ?_, ?_⟩
  · have hΓ : 1 ≤ (D.mem u).A.GamP := le_of_lt (D.mem u).A.one_lt_gammaP
    have hGpos : 0 < (D.mem u).A.GamP := by linarith
    have hwin := D.T_win u
    have hlo : Real.exp (StandardLattice.logXuD D u) * (D.mem u).A.GamP ^ (-(2 : ℝ) / (D.R.f * D.R.k)) ≤
        ((D.mem u).A.T : ℝ) := by
      rw [exp_logXuD D ⟨hT1, hT2⟩ u]
      exact hwin.1
    have hhi : ((D.mem u).A.T : ℝ) ≤ Real.exp (StandardLattice.logXuD D u) *
        (D.mem u).A.GamP ^ (-(2 : ℝ) / (D.R.f * D.R.k)) * (1 + 1 / ((D.R.f : ℝ) * D.R.k)) := by
      rw [exp_logXuD D ⟨hT1, hT2⟩ u, mul_comm _ (1 + _)]
      exact hwin.2
    obtain ⟨h1, h2, h3⟩ := h5c Δ _ hB _ hΓ u hlo hhi
    have hrank : ((D.duS u : ℕ) : ℝ) =
        StandardLattice.duStarU D u * (((D.mem u).A.T : ℝ) ^ D.R.k - 1) ^ D.R.f :=
      h4 hG hSp u (hU u).1 (hU u).2
    have hTge : (2 : ℝ) ≤ (D.mem u).A.T := by exact_mod_cast (D.mem u).A.T_prime.two_le
    have hTk : 0 < ((D.mem u).A.T : ℝ) ^ D.R.k - 1 := by
      have : 1 < ((D.mem u).A.T : ℝ) ^ D.R.k := one_lt_pow₀ (by linarith) (by omega)
      linarith
    have hdu : 0 < StandardLattice.duStarU D u := by
      rw [← hT1 u]
      exact_mod_cast (D.mem u).A.duStar_pos
    have hDs : (D.mem u).A.Dstar = StandardLattice.DstarD D := by rw [D.Dstar_eq u, hT2]
    have hDpos : 0 < StandardLattice.DstarD D := by
      rw [← hDs]
      exact (D.mem u).A.Dstar_pos
    have hQ : (D.duS u : ℝ) * (D.mem u).A.GamP ^ 2 / (D.mem u).A.Dstar =
        StandardLattice.duStarU D u * (((D.mem u).A.T : ℝ) ^ D.R.k - 1) ^ D.R.f /
          (StandardLattice.DstarD D * (D.mem u).A.GamP ^ (-(2 : ℝ))) := by
      rw [hrank, hDs, Real.rpow_neg hGpos.le, Real.rpow_two]
      field_simp
    have hQpos : 0 < StandardLattice.duStarU D u * (((D.mem u).A.T : ℝ) ^ D.R.k - 1) ^ D.R.f /
        (StandardLattice.DstarD D * (D.mem u).A.GamP ^ (-(2 : ℝ))) :=
      div_pos (mul_pos hdu (pow_pos hTk _)) (mul_pos hDpos (Real.rpow_pos_of_pos hGpos _))
    rw [abs_le] at h1
    have hQlo : Real.exp (-C) ≤ StandardLattice.duStarU D u * (((D.mem u).A.T : ℝ) ^ D.R.k - 1) ^ D.R.f /
        (StandardLattice.DstarD D * (D.mem u).A.GamP ^ (-(2 : ℝ))) := by
      rw [← Real.exp_log hQpos]
      exact Real.exp_le_exp.mpr h1.1
    have hQhi : StandardLattice.duStarU D u * (((D.mem u).A.T : ℝ) ^ D.R.k - 1) ^ D.R.f /
        (StandardLattice.DstarD D * (D.mem u).A.GamP ^ (-(2 : ℝ))) ≤ Real.exp C := by
      rw [← Real.exp_log hQpos]
      exact Real.exp_le_exp.mpr h1.2
    have hS : (∑ j ∈ SizeData₂.lifts D, (1 / (D.R.f : ℝ)) *
          ∑ ρ : D.what₂.Tau, Real.log (wSz D j ρ * D.host.v / Real.pi)) =
        ∑ j ∈ Finset.range D.R.m, (1 / (D.R.f : ℝ)) *
          ∑ ρ : D.what₂.Tau, Real.log (wSz D (j + 1) ρ * D.host.v / Real.pi) := by
      have himg : SizeData₂.lifts D = (Finset.range D.R.m).image (· + 1) := by
        ext j
        simp only [SizeData₂.lifts, Finset.mem_Icc, Finset.mem_image, Finset.mem_range]
        constructor
        · rintro ⟨hj1, hj2⟩
          exact ⟨j - 1, by omega, by omega⟩
        · rintro ⟨a, ha, rfl⟩
          omega
      rw [himg, Finset.sum_image (fun a _ b _ h => by simpa using h)]
    have hg : (∑ g ∈ L.gTypes, Real.log (g : ℝ)) ≤ ∑ i : Fin 2, Real.log (D.host.g i : ℝ) := by
      rw [Fin.sum_univ_two]
      unfold SizeData₂.gTypes
      by_cases h : D.host.g 0 = D.host.g 1
      · rw [h]
        simp only [Finset.mem_singleton, Finset.insert_eq_of_mem, Finset.sum_singleton]
        linarith [Real.log_natCast_nonneg (D.host.g 1)]
      · rw [Finset.sum_pair h]
    have hX : 0 ≤ L.sc.L + (D.R.m : ℝ) ^ 2 * L.sc.L / D.R.k := by positivity
    have hm : (0 : ℝ) ≤ D.R.m := Nat.cast_nonneg _
    refine ⟨?_, ?_, ?_, ?_⟩
    · calc (max C (Real.exp C))⁻¹ ≤ (Real.exp C)⁻¹ := (inv_le_inv₀ hCpos (Real.exp_pos C)).mpr hCe
        _ = Real.exp (-C) := (Real.exp_neg C).symm
        _ ≤ _ := by rw [hQ]; exact hQlo
    · rw [hQ]
      exact le_trans hQhi hCe
    · calc Real.log ((D.mem u).A.T : ℝ) ≤ C * D.R.m * L.sc.L := h2
        _ ≤ max C (Real.exp C) * D.R.m * L.sc.L :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hCC hm) hL.le
    · unfold StandardLattice.lowB at h3
      rw [hS]
      nlinarith [mul_le_mul_of_nonneg_right hCC hX, mul_le_mul_of_nonneg_left hg hm]
  · rw [hXu, hXu]
    exact le_trans ((h5v Δ _ hB).2 u u')
      (mul_le_mul_of_nonneg_right hCC (Real.log_natCast_nonneg _))
  · have hW : Fintype.card D.what₂.Word ≤ 2 ^ (D.R.k - 3) := hWs
    exact le_trans hW (Nat.pow_le_pow_right (by norm_num) (by omega))

theorem family_rank_count_bound {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) (C0 : ℝ)
    (h4 : ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x), StandardLattice.Conclusion4f (Fm.D x i) (Fm.ex x hx i).lev)
    (h5 : StandardLattice.PartFiveFamilyBounds Fm)
    (hE : ∃ x0 : ℝ, ∀ x ≥ x0, ∀ i : Fm.Ix x, Formalism.MainNotions.SizeWords (Fm.L x i) ∧ RankHyp (Fm.D x i) ∧
      ∃ Δ : ℝ, StandardLattice.DataB (Fm.D x i) (Fm.L x i).sc C0 Δ (fun j ρ => wSz (Fm.D x i) (j + 1) ρ)) :
    LocalQuadraticParts.CountFamily Fm := by
  obtain ⟨C, x5, hP⟩ := h5 C0
  obtain ⟨x0, hE⟩ := hE
  unfold LocalQuadraticParts.CountFamily
  refine ⟨max C (Real.exp C), max (max x0 x5) (Fm.x1 + 1), fun x hx i => ?_⟩
  have hx0 : x0 ≤ x := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hx
  have hx5 : x5 ≤ x := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hx
  have hx1 : Fm.x1 < x := by
    have := le_trans (le_max_right _ _) hx
    linarith
  obtain ⟨hWs, hR, Δ, hB⟩ := hE x hx0 i
  obtain ⟨-, h5c, h5v⟩ := hP x hx5 hx1 i
  exact rank_count_bound_of_data (Fm.D x i) (Fm.L x i) (Fm.ex x hx1 i).lev C0 C Δ (h4 x hx1 i) h5c h5v hB hR
    ⟨(Fm.ex x hx1 i).duStar_def, (Fm.ex x hx1 i).Dstar_def⟩ hWs

end Formalism.MainNotions.J
end
end

-- bundled from Formalism.SharpRestriction.AdmissibleParameterJoins.DIVfromGLf
section
noncomputable section

namespace Formalism.MainNotions.J

open Formalism.BasicNotions Formalism.BasicNotions.DV

theorem logDerivative_and_regulator_bound (D : D7) (L : SizeData₂ D) (hdl : |L.logDerivativeAtOne| ≤ L.sc.x ^ L.sc.eps)
    (hrd : 1 ≤ D.host.rdE) (hx : 16 ≤ L.sc.x) :
    LocalQuadraticParts.adm23 L := by
  have : NeZero D.host.d := ⟨D.host.hyp.2.1.ne_zero⟩
  have : Fact D.host.d.Prime := ⟨D.host.hyp.2.1⟩
  refine ⟨⟨chiK D, ?_, ?_⟩, ?_⟩
  · intro n
    rw [← jacobiSym.legendreSym.to_jacobiSym]
    simp [chiK, MulChar.ringHomComp_apply, legendreSym]
  · have him := GlobalTheoryTheory.log_deriv_L_one_real_im_eq_zero (chiK D) (GlobalTheoryTheory.jnt_chiK_ne_one D) (GlobalTheoryTheory.jnt_chiK_real D)
    rw [L.logDerivative_at_one_eq]
    apply Complex.ext
    · simp [dlogL]
    · simpa [GlobalTheoryTheory.logDerivativeAtOne] using him.symm
  · have hx0 : 0 < L.sc.x := by linarith
    have hv : D.host.v = D.host.rdE / 2 := rfl
    have hrd0 : 0 < D.host.rdE := by linarith
    have hlrd : 0 ≤ Real.log D.host.rdE := Real.log_nonneg hrd
    have h1 : Real.log (Real.pi / D.host.v) = Real.log (2 * Real.pi) - Real.log D.host.rdE := by
      rw [hv, ← Real.log_div (by positivity) hrd0.ne']
      congr 1
      field_simp
    have h2 : Real.log (2 * Real.pi) ≤ 3 * Real.log 2 := by
      have : Real.log (2 * Real.pi) ≤ Real.log ((2 : ℝ) ^ 3) :=
        Real.log_le_log (by positivity) (by nlinarith [Real.pi_le_four])
      rwa [Real.log_pow] at this
    have h2' : 0 ≤ Real.log (2 * Real.pi) := Real.log_nonneg (by nlinarith [Real.pi_gt_three])
    have h3 : 4 * Real.log 2 ≤ Real.log L.sc.x := by
      have : Real.log ((2 : ℝ) ^ 4) ≤ Real.log L.sc.x := Real.log_le_log (by positivity) (by linarith)
      rwa [Real.log_pow] at this
    have h4 : L.La = Real.log L.sc.x + L.sc.L + Real.log D.host.rdE := by
      unfold SizeData₂.La Scale.a Scale.b
      rw [Real.log_mul (by positivity) hrd0.ne', Real.log_mul hx0.ne' (Real.exp_pos _).ne', Real.log_exp]
    have h5 : |L.logDerivativeAtOne| ≤ L.sc.L := hdl
    have hg := Real.eulerMascheroniConstant_lt_two_thirds
    have hg0 : 0 < Real.eulerMascheroniConstant := by
      have := Real.one_half_lt_eulerMascheroniConstant; linarith
    have hl2 := Real.log_two_gt_d9
    obtain ⟨h5a, h5b⟩ := abs_le.mp h5
    unfold SizeData₂.logOm
    rw [h1, h4, abs_le]
    constructor <;> linarith

theorem family_logDerivative_regulator_bound {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps)
    (hE : ∃ x0 : ℝ, ∀ x ≥ x0, ∀ i : Fm.Ix x,
      |(Fm.L x i).logDerivativeAtOne| ≤ (Fm.L x i).sc.x ^ (Fm.L x i).sc.eps ∧ 1 ≤ (Fm.D x i).host.rdE) :
    LocalQuadraticParts.PeriodFamily' Fm := by
  obtain ⟨xE, hE⟩ := hE
  refine ⟨max xE (max 16 (Fm.x1 + 1)), fun x hx i => ?_⟩
  have hxE : xE ≤ x := le_trans (le_max_left _ _) hx
  have hx16 : 16 ≤ x := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hx
  have hx1 : Fm.x1 < x :=
    lt_of_lt_of_le (by linarith) (le_trans (le_trans (le_max_right 16 _) (le_max_right _ _)) hx)
  have hsx : (Fm.L x i).sc.x = x := Fm.L_x x i hx1
  exact logDerivative_and_regulator_bound _ _ (hE x hxE i).1 (hE x hxE i).2 (by rw [hsx]; exact hx16)

end Formalism.MainNotions.J
end
end

