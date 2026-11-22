import Mathlib
import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.Bundle0004
import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.Bundle0001
import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.Bundle0003
import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0008
import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.Objects

-- bundled from GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.PBoundingKaehler
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.AnalyticLimit

open ReciprocityTheory.AnForm (levi levi_zero levi_add_smul)
open ReciprocityTheory.AnForm.M (FinHolAtlas LocPot IsPotential IsPosPot)

noncomputable section

variable {D : ℕ} {X : Type} [TopologicalSpace X]

theorem levi_rsmul_chart (A : FinHolAtlas D X) (P : LocPot X) (hP : IsPotential A P) (a : ℝ)
    (x : X) (k : Fin A.n) (y : Fin D → ℂ)
    (hy : y ∈ (A.chart k).target ∩ (A.chart k).symm ⁻¹' P.U x) (w : Fin D → ℂ) :
    levi ((P.rsmul a).φ x ∘ (A.chart k).symm) y w = a * levi (P.φ x ∘ (A.chart k).symm) y w := by
  have hs : ContDiffAt ℝ 2 (P.φ x ∘ (A.chart k).symm) y :=
    ((hP.1 x k).of_le two_le_smooth_kb).contDiffAt
      (((A.chart k).continuousOn_symm.isOpen_inter_preimage (A.chart k).open_target
        (P.isOpen_U x)).mem_nhds hy)
  have h := levi_add_smul a (contDiffAt_const (c := (0 : ℝ))) hs w
  have he : (P.rsmul a).φ x ∘ (A.chart k).symm =
      fun z => (0 : ℝ) + a * (P.φ x ∘ (A.chart k).symm) z := by
    funext z
    simp [LocPot.rsmul]
  rw [he, h, levi_const, zero_add]

theorem BoundingKaehler.proof : BoundingKaehler.Statement := by
  intro X _ _ _ D A om m th hth
  have hX : IsCompact (Set.univ : Set X) := isCompact_univ
  choose M hM0 hM using fun i => levi_abs_le_global A hX (th i) om.pot (hth i) om.isPot om.pos
  set K : ℝ := 1 + ∑ i, M i with hKdef
  have hsum : 0 ≤ ∑ i, M i := Finset.sum_nonneg fun i _ => hM0 i
  have hK : 0 < K := by linarith
  have hMK : ∀ i, M i ≤ K := fun i => by
    have := Finset.single_le_sum (fun j (_ : j ∈ Finset.univ) => hM0 j) (Finset.mem_univ i)
    linarith
  have hnn : ∀ x k, ∀ y ∈ (A.chart k).target ∩ (A.chart k).symm ⁻¹' om.pot.U x, ∀ w : Fin D → ℂ,
      0 ≤ levi (om.pot.φ x ∘ (A.chart k).symm) y w := by
    intro x k y hy w
    rcases eq_or_ne w 0 with h0 | h0
    · rw [h0, levi_zero]
    · exact (om.pos x k y hy w h0).le
  refine ⟨⟨om.pot.rsmul K, ReciprocityTheory.AnForm.M.isPotentialRsmul A K om.pot om.isPot,
    fun x k y hy w hw => ?_⟩, fun i => ⟨?_, ?_⟩⟩
  · rw [levi_rsmul_chart A om.pot om.isPot K x k y hy w]
    exact mul_pos hK (om.pos x k y hy w hw)
  · intro x k y hy w
    have hyo : y ∈ (A.chart k).target ∩ (A.chart k).symm ⁻¹' om.pot.U x := ⟨hy.1, hy.2.2⟩
    have hyb : y ∈ (A.chart k).target ∩ (A.chart k).symm ⁻¹' ((th i).U x ∩ om.pot.U x) :=
      ⟨hy.1, hy.2.1.2, hy.2.2⟩
    rw [levi_rsmul_chart A om.pot om.isPot K x k y hyo w]
    have h1 := abs_le.mp (hM i x k y hyb w)
    have h2 := hnn x k y hyo w
    have h3 := hMK i
    nlinarith
  · intro x k y hy w
    have hyo : y ∈ (A.chart k).target ∩ (A.chart k).symm ⁻¹' om.pot.U x := ⟨hy.1, hy.2.1.2⟩
    have hyb : y ∈ (A.chart k).target ∩ (A.chart k).symm ⁻¹' ((th i).U x ∩ om.pot.U x) :=
      ⟨hy.1, hy.2.2, hy.2.1.2⟩
    rw [levi_rsmul_chart A om.pot om.isPot K x k y hyo w]
    have h1 := abs_le.mp (hM i x k y hyb w)
    have h2 := hnn x k y hyo w
    have h3 := hMK i
    nlinarith

end

end GroundTheory.Heights₂.Heights.AnalyticLimit
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.PGluedLocal
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.AnalyticLimit

open Filter Topology Metric
open ReciprocityTheory.AnForm.A (regMax regMax_update)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Regular (RegChartData RegCharts errorWithLinear)

noncomputable section

theorem regMax_eq_of_agree_dominated {ι : Type*} [Fintype ι] [Nonempty ι] [DecidableEq ι]
    {e : ℝ} (he : 0 ≤ e) (J : Finset ι) (u v : ι → ℝ)
    (hJ : ∀ j ∈ J, u j = v j)
    (hu : ∀ j ∉ J, ∃ k ∈ J, u j + e ≤ u k)
    (hv : ∀ j ∉ J, ∃ k ∈ J, v j + e ≤ v k) :
    regMax e u = regMax e v := by
  have key : ∀ S : Finset ι, (∀ i ∈ S, i ∉ J) →
      regMax e (fun i => if i ∈ S then v i else u i) = regMax e u := by
    intro S
    induction S using Finset.induction_on with
    | empty => intro _; simp
    | insert j S hjS ih =>
      intro hS
      have hjJ : j ∉ J := hS j (Finset.mem_insert_self j S)
      have ih' := ih (fun i hi => hS i (Finset.mem_insert_of_mem hi))
      set w : ι → ℝ := fun i => if i ∈ S then v i else u i with hw
      have hwJ : ∀ k ∈ J, w k = u k := by
        intro k hk
        have : k ∉ S := fun h => hS k (Finset.mem_insert_of_mem h) hk
        simp [hw, this]
      have hwj : w j = u j := by simp [hw, hjS]
      obtain ⟨k1, hk1J, hk1⟩ := hu j hjJ
      obtain ⟨k2, hk2J, hk2⟩ := hv j hjJ
      have hk1j : k1 ≠ j := fun h => hjJ (h ▸ hk1J)
      have hk2j : k2 ≠ j := fun h => hjJ (h ▸ hk2J)
      have e1 : regMax e (Function.update w j (min (u j) (v j))) = regMax e w := by
        apply regMax_update he w j k1 _ hk1j
        · rw [hwj, hwJ k1 hk1J]; exact hk1
        · rw [hwJ k1 hk1J]; linarith [min_le_left (u j) (v j)]
      have e2 : regMax e (Function.update (Function.update w j (min (u j) (v j))) j (v j)) =
          regMax e (Function.update w j (min (u j) (v j))) := by
        apply regMax_update he _ j k2 _ hk2j
        · rw [Function.update_self, Function.update_of_ne hk2j, hwJ k2 hk2J]
          linarith [min_le_right (u j) (v j), hJ k2 hk2J]
        · rw [Function.update_of_ne hk2j, hwJ k2 hk2J, hJ k2 hk2J]; exact hk2
      have hfun : (fun i => if i ∈ insert j S then v i else u i) =
          Function.update (Function.update w j (min (u j) (v j))) j (v j) := by
        funext i
        rw [Function.update_idem]
        by_cases hi : i = j
        · subst hi; simp
        · rw [Function.update_of_ne hi]; simp [hw, Finset.mem_insert, hi]
      rw [hfun, e2, e1, ih']
  have hall := key (Finset.univ.filter (fun i => i ∉ J)) (fun i hi => (Finset.mem_filter.1 hi).2)
  rw [← hall]
  congr 1
  funext i
  by_cases hi : i ∈ J
  · simp [hi, hJ i hi]
  · simp [hi]

theorem GluedLocal.proof : GluedLocal.Statement := by
  intro X _ _ D A R ρ Cη η hη x₀
  classical
  have hV''V' : ∀ j x, x ∈ R.V'' j → x ∈ R.V' j := fun j x hx =>
    ⟨hx.1, R.closure_W''_subset j (subset_closure hx.2)⟩
  have hV'open : ∀ j, IsOpen (R.V' j) := fun j => (R.ψ j).isOpen_inter_preimage (R.isOpen_alt j)
  set c : Fin R.n := (R.cover x₀).choose with hc
  have hc0 : x₀ ∈ R.V'' c := (R.cover x₀).choose_spec
  have hK : ∀ j, ∃ K : Set (Fin D → ℂ), IsCompact K ∧ K ⊆ R.W' j ∧
      ∀ x ∈ R.V' j, R.ψ j x ∉ K → η j x = -1 := fun j => (hη j).2.2.2.1
  choose K hKc hKW hKη using hK
  have hKt : ∀ j, K j ⊆ (R.ψ j).target := fun j k hk =>
    R.W_subset j (R.closure_W'_subset j (subset_closure (hKW j hk)))
  set Z : Fin R.n → Set X := fun j => (R.ψ j).symm '' K j with hZ
  have hZclosed : ∀ j, IsClosed (Z j) := fun j =>
    ((hKc j).image_of_continuousOn ((R.ψ j).continuousOn_symm.mono (hKt j))).isClosed
  have memZ : ∀ j x, x ∈ R.V' j → R.ψ j x ∈ K j → x ∈ Z j := fun j x hx hk =>
    ⟨R.ψ j x, hk, (R.ψ j).left_inv hx.1⟩
  set J : Finset (Fin R.n) := Finset.univ.filter (fun j => x₀ ∈ R.V' j ∧ R.ψ j x₀ ∈ K j) with hJ
  have hx0Z : ∀ j ∉ J, x₀ ∉ Z j := by
    rintro j hj ⟨k, hk, hkx⟩
    apply hj
    have ht := hKt j hk
    have hs : x₀ ∈ (R.ψ j).source := by rw [← hkx]; exact (R.ψ j).map_target ht
    have he : R.ψ j x₀ = k := by rw [← hkx]; exact (R.ψ j).right_inv ht
    refine Finset.mem_filter.2 ⟨Finset.mem_univ _, ⟨hs, ?_⟩, ?_⟩
    · show R.ψ j x₀ ∈ R.W' j
      rw [he]; exact hKW j hk
    · rw [he]; exact hk
  set N : Set X := R.V'' c ∩ ⋂ j, (if j ∈ J then R.V' j else (Z j)ᶜ) with hN
  have hNJ : ∀ x ∈ N, ∀ j ∈ J, x ∈ R.V' j := fun x hx j hj => by
    have := Set.mem_iInter.1 hx.2 j
    rwa [if_pos hj] at this
  have hNZ : ∀ x ∈ N, ∀ j ∉ J, x ∉ Z j := fun x hx j hj => by
    have := Set.mem_iInter.1 hx.2 j
    rwa [if_neg hj] at this
  have hNopen : IsOpen N := by
    refine ((R.ψ c).isOpen_inter_preimage (R.isOpen_alt_alt c)).inter (isOpen_iInter_of_finite fun j => ?_)
    split_ifs
    · exact hV'open j
    · exact (hZclosed j).isOpen_compl
  have hx0N : x₀ ∈ N := by
    refine ⟨hc0, Set.mem_iInter.2 fun j => ?_⟩
    split_ifs with hj
    · exact (Finset.mem_filter.1 hj).2.1
    · exact hx0Z j hj

  have inner_mem : ∀ x ∈ N, ∀ j, x ∈ R.V'' j → j ∈ J := by
    intro x hx j hxj
    by_contra hj
    have h1 : η j x = -1 :=
      hKη j x (hV''V' j x hxj) (fun hk => hNZ x hx j hj (memZ j x (hV''V' j x hxj) hk))
    have h0 : η j x = 0 := (hη j).2.2.1 x hxj
    rw [h1] at h0
    norm_num at h0
  have hcJ : c ∈ J := inner_mem x₀ hx0N c hc0
  refine ⟨N, J, c, hNopen, hx0N, hcJ, fun j hj x hx => hNJ x hx j hj, fun x hx => hx.1, ?_⟩
  intro C t he hcomp x hx
  have : Nonempty (Fin R.n) := ⟨c⟩
  have hcx : x ∈ R.V'' (R.cover x).choose := (R.cover x).choose_spec
  have hcxJ : (R.cover x).choose ∈ J := inner_mem x hx _ hcx
  rw [RegCharts.glued]
  congr 1
  refine regMax_eq_of_agree_dominated he.le J _ _ ?_ ?_ ?_
  · intro j hj
    rw [if_pos (hNJ x hx j hj), if_pos hj]
  · intro j hj
    refine ⟨(R.cover x).choose, hcxJ, ?_⟩
    rw [if_pos (hNJ x hx _ hcxJ)]
    by_cases hxj : x ∈ R.V' j
    · rw [if_pos hxj]
      have h1 : η j x = -1 := hKη j x hxj (fun hk => hNZ x hx j hj (memZ j x hxj hk))
      have h0 : η (R.cover x).choose x = 0 := (hη _).2.2.1 x hcx
      have hcmp := (abs_le.1 (hcomp j (R.cover x).choose x hxj (hV''V' _ x hcx))).2
      simp only [RegCharts.regArg, h1, h0]
      linarith
    · rw [if_neg hxj]
      linarith
  · intro j hj
    refine ⟨c, hcJ, ?_⟩
    rw [if_neg hj, if_pos hcJ]
    linarith

end

end GroundTheory.Heights₂.Heights.AnalyticLimit
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.PPolynomialInWeights
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.AnalyticLimit

open MeasureTheory
open ReciprocityTheory.AnForm (hessC maDens mdisc)
open ReciprocityTheory.AnForm.M (FinHolAtlas LocPot IsPotential mInt ChartPartition locDens integralWith
  MIntegrable)

noncomputable section

section Expansion

variable {D : ℕ} {X : Type} [TopologicalSpace X] {ι : Type} [Fintype ι]

theorem locDens_expand (A : FinHolAtlas D X) (Φ : Fin D → LocPot X) (B : Fin D → ι → LocPot X)
    (hB : ∀ k o, IsPotential A (B k o)) (x : ι → ℝ)
    (hΦ : ∀ k b z, (Φ k).φ b z = ∑ o, x o * (B k o).φ b z) (j : Fin A.n) {y : Fin D → ℂ}
    (hy : y ∈ (A.chart j).target) :
    locDens A Φ j y = ∑ σ : Fin D → ι, (∏ k, x (σ k)) * locDens A (fun k => B k (σ k)) j y := by
  let f : Fin D → ι → (Fin D → ℂ) → ℝ := fun k o y' =>
    (B k o).φ ((A.chart j).symm y) ((A.chart j).symm y')
  have hS : ∀ k, hessC (fun y' => (Φ k).φ ((A.chart j).symm y) ((A.chart j).symm y')) y =
      ∑ o, (x o : ℂ) • hessC (f k o) y := fun k => by
    simp_rw [hΦ]
    exact hessC_finset_sum _ _ (f k) y fun o _ =>
      ReciprocityTheory.AnForm.M.potential_contDiffAt A (B k o) (hB k o) j hy
  obtain ⟨M, hM⟩ := ReciprocityTheory.AnForm.A.exists_multilinearMap_eq_mdisc (D := D)
  have hL : locDens A Φ j y =
      (D.factorial : ℝ) * (2 / Real.pi) ^ D * (M fun k => ∑ o, (x o : ℂ) • hessC (f k o) y).re := by
    simp only [locDens, maDens, hS, hM]
  have hR : ∀ σ : Fin D → ι, locDens A (fun k => B k (σ k)) j y =
      (D.factorial : ℝ) * (2 / Real.pi) ^ D * (M fun k => hessC (f k (σ k)) y).re := fun σ => by
    rw [hM]
    rfl
  rw [hL, MultilinearMap.map_sum, Complex.re_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [MultilinearMap.map_smul_univ, hR, smul_eq_mul, ← Complex.ofReal_prod, Complex.re_ofReal_mul]
  ring

theorem mIntegrable_of_continuousOn (A : FinHolAtlas D X) (Φ : Fin D → LocPot X)
    (hΦ : ∀ k, IsPotential A (Φ k)) (w : X → ℝ)
    (hw : ∀ j, ContinuousOn (fun y => w ((A.chart j).symm y)) (A.chart j).target) :
    MIntegrable A Φ w := by
  intro j K hKt hK
  exact (((hw j).mul (ReciprocityTheory.AnForm.M.locDensCont A Φ hΦ j)).mono hKt).integrableOn_compact hK

theorem mInt_expand [CompactSpace X] [T2Space X] (A : FinHolAtlas D X) (Φ : Fin D → LocPot X)
    (B : Fin D → ι → LocPot X) (hB : ∀ k o, IsPotential A (B k o)) (x : ι → ℝ)
    (hΦ : ∀ k b z, (Φ k).φ b z = ∑ o, x o * (B k o).φ b z) (g : X → ℝ) (w : ι → X → ℝ)
    (hw : ∀ o j, ContinuousOn (fun y => w o ((A.chart j).symm y)) (A.chart j).target)
    (hg : ∀ p, g p = ∑ o, x o * w o p) :
    mInt A Φ g =
      ∑ o, ∑ σ : Fin D → ι, (x o * ∏ k, x (σ k)) * mInt A (fun k => B k (σ k)) (w o) := by
  unfold mInt
  split_ifs with h
  · unfold integralWith
    have hI : ∀ (o : ι) (σ : Fin D → ι) (j : Fin A.n), IntegrableOn (fun y =>
        h.some.χ j ((A.chart j).symm y) * w o ((A.chart j).symm y) *
          locDens A (fun k => B k (σ k)) j y) (A.chart j).target := fun o σ j =>
      ReciprocityTheory.AnForm.M.integrableOn_weight A h.some _ _
        (mIntegrable_of_continuousOn A _ (fun k => hB k (σ k)) _ (hw o)) j
    have hj : ∀ j, ∫ y in (A.chart j).target,
        h.some.χ j ((A.chart j).symm y) * g ((A.chart j).symm y) * locDens A Φ j y =
        ∑ o, ∑ σ : Fin D → ι, (x o * ∏ k, x (σ k)) * ∫ y in (A.chart j).target,
          h.some.χ j ((A.chart j).symm y) * w o ((A.chart j).symm y) *
            locDens A (fun k => B k (σ k)) j y := by
      intro j
      calc ∫ y in (A.chart j).target,
            h.some.χ j ((A.chart j).symm y) * g ((A.chart j).symm y) * locDens A Φ j y
          = ∫ y in (A.chart j).target, ∑ o, ∑ σ : Fin D → ι, (x o * ∏ k, x (σ k)) *
              (h.some.χ j ((A.chart j).symm y) * w o ((A.chart j).symm y) *
                locDens A (fun k => B k (σ k)) j y) := by
            refine setIntegral_congr_fun (A.chart j).open_target.measurableSet fun y hy => ?_
            rw [hg, locDens_expand A Φ B hB x hΦ j hy, mul_assoc, Finset.sum_mul, Finset.mul_sum]
            refine Finset.sum_congr rfl fun o _ => ?_
            rw [Finset.mul_sum, Finset.mul_sum]
            refine Finset.sum_congr rfl fun σ _ => ?_
            ring
        _ = _ := by
            rw [integral_finsetSum _ fun o _ =>
              integrable_finsetSum _ fun σ _ => (hI o σ j).const_mul _]
            refine Finset.sum_congr rfl fun o _ => ?_
            rw [integral_finsetSum _ fun σ _ => (hI o σ j).const_mul _]
            refine Finset.sum_congr rfl fun σ _ => ?_
            exact integral_const_mul _ _
    rw [Finset.sum_congr rfl fun j _ => hj j, Finset.sum_comm]
    refine Finset.sum_congr rfl fun o _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [Finset.mul_sum]
  · simp

theorem totalDegree_C_mul_X_mul_prod_le {κ : Type} (c : ℝ) (o : κ) (σ : Fin D → κ) :
    (MvPolynomial.C c * (MvPolynomial.X o * ∏ i, MvPolynomial.X (σ i)) :
      MvPolynomial κ ℝ).totalDegree ≤ D + 1 := by
  refine (MvPolynomial.totalDegree_mul _ _).trans ?_
  rw [MvPolynomial.totalDegree_C, zero_add]
  refine (MvPolynomial.totalDegree_mul _ _).trans ?_
  rw [MvPolynomial.totalDegree_X, add_comm]
  refine Nat.add_le_add_right ((MvPolynomial.totalDegree_finsetProd _ _).trans ?_) 1
  simp [MvPolynomial.totalDegree_X]

end Expansion

theorem PolynomialInWeights.proof : PolynomialInWeights.Statement := by
  intro X _ _ _ D A F a ha t ht
  classical
  let P : Option (Fin F.m) → LocPot X := fun o =>
    o.elim a fun i => (F.R i).θ + LocPot.ofFun ((F.sys i).ph t)
  let Q : Option (Fin F.m) → LocPot X := fun o => o.elim a fun i => (F.R i).θ
  let w : Option (Fin F.m) → X → ℝ := fun o => o.elim (fun _ => 0) fun i => (F.sys i).ph t
  let B : ℕ → Fin D → Option (Fin F.m) → LocPot X := fun k i => if (i : ℕ) < k then P else Q
  have hsm : ∀ i, A.Smooth ((F.sys i).ph t) := fun i => (F.sys i).smooth t ht.1 (ht.2 i)
  have hP : ∀ o, IsPotential A (P o) := by
    rintro (_ | i)
    · exact ha
    · exact ReciprocityTheory.AnForm.M.isPotentialAdd A _ _ (F.R i).θ_pot
        (ReciprocityTheory.AnForm.M.isPotential_ofFun A _ (hsm i))
  have hQ : ∀ o, IsPotential A (Q o) := by
    rintro (_ | i)
    · exact ha
    · exact (F.R i).θ_pot
  have hB : ∀ k i o, IsPotential A (B k i o) := by
    intro k i o
    by_cases hik : (i : ℕ) < k
    · simp only [B, if_pos hik]; exact hP o
    · simp only [B, if_neg hik]; exact hQ o
  have hw : ∀ o j, ContinuousOn (fun y => w o ((A.chart j).symm y)) (A.chart j).target := by
    rintro (_ | i) j
    · exact continuousOn_const
    · have := ((hsm i) j).continuousOn
      rw [Set.preimage_univ, Set.inter_univ] at this
      exact this
  have hPφ : ∀ x b z, (F.coefForm a x t).φ b z = ∑ o, x o * (P o).φ b z := by
    intro x b z
    show (F.chernForm (fun i => x (some i)) t).φ b z + x none * a.φ b z = _
    rw [Family.chernForm, lincomb_φ, Fintype.sum_option, add_comm]
    rfl
  have hQφ : ∀ x b z, (F.coefRefForm a x).φ b z = ∑ o, x o * (Q o).φ b z := by
    intro x b z
    show (lincomb F.m (fun i => x (some i)) (fun i => (F.R i).θ)).φ b z + x none * a.φ b z = _
    rw [lincomb_φ, Fintype.sum_option, add_comm]
    rfl
  refine ⟨∑ k ∈ Finset.range (D + 1), ∑ o, ∑ σ : Fin D → Option (Fin F.m),
    MvPolynomial.C (mInt A (fun i => B k i (σ i)) (w o)) *
      (MvPolynomial.X o * ∏ i, MvPolynomial.X (σ i)), ?_, ?_⟩
  · exact MvPolynomial.totalDegree_finsetSum_le fun k _ =>
      MvPolynomial.totalDegree_finsetSum_le fun o _ =>
        MvPolynomial.totalDegree_finsetSum_le fun σ _ => totalDegree_C_mul_X_mul_prod_le _ _ _
  · intro x
    simp only [map_sum, map_mul, map_prod, MvPolynomial.eval_C, MvPolynomial.eval_X]
    unfold Family.weightEnergy
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [mInt_expand A _ (B k) (hB k) x ?_ _ w hw ?_]
    · refine Finset.sum_congr rfl fun o _ => Finset.sum_congr rfl fun σ _ => ?_
      ring
    · intro i b z
      by_cases hik : (i : ℕ) < k
      · simp only [B, if_pos hik]; exact hPφ x b z
      · simp only [B, if_neg hik]; exact hQφ x b z
    · intro p
      simp [Family.coefWeight, Fintype.sum_option, w]

end

end GroundTheory.Heights₂.Heights.AnalyticLimit
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.StListTailLog
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.AnalyticLimit

open ReciprocityTheory.AnForm.M (FinHolAtlas LocPot)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Regular (RegChartData)

def ListTailLog.Statement : Prop :=
  ∀ {X : Type} [TopologicalSpace X] [CompactSpace X] [T2Space X] (D : ℕ) (A : FinHolAtlas D X)
    (R : RegChartData A), (∀ x ∈ R.Yo, Real.exp 1 ≤ R.r x) → ∀ (Om : KaehlerForm A) (C₁ : ℝ),
    ∃ CE : ℝ, ∀ (th : Fin D → LocPot X) (u : Fin D → X → ℝ),
      (∀ j, IsBoundedPotForm A R.Yo R.r Om C₁ (th j) (u j)) →
      TailLogBound A R.Yo R.r (fun j => potForm (th j) (u j)) CE

section Inhabitants

open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Regular (projLineChartData)

end Inhabitants

end GroundTheory.Heights₂.Heights.AnalyticLimit
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.UniformIntegrability
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.AnalyticLimit

open ReciprocityTheory.AnForm.M (mInt)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Regular (ell errE)

noncomputable section

theorem mixedForms_all {W : Type} [TopologicalSpace W] {D : ℕ} (Om : ReciprocityTheory.AnForm.M.LocPot W)
    (T : Fin (D + 1) → ReciprocityTheory.AnForm.M.LocPot W) : mixedForms Om T (D + 1) = T :=
  funext fun i => if_pos i.isLt

theorem UniformIntegrability.proof (h₀ : GreenMassZero.Statement) (h₁ : GreenMassStep.Statement)
    (h₂ : GreenMassReplace.Statement) (h₃ : GreenMassError.Statement) :
    UniformIntegrability.Statement := by
  intro D W _ _ _ S
  have key : ∀ a, a ≤ D + 1 → ∀ η, 0 < η → ∃ ε₀, 0 < ε₀ ∧ ∃ t₁, 0 < t₁ ∧ ∀ ε t, 0 < ε →
      ε ≤ ε₀ → 0 < t → t ≤ t₁ → S.ell₀ ≤ ell t → S.J a ε t ≤ η := by
    intro a
    induction a with
    | zero =>
      intro _ η hη
      obtain ⟨ε₀, hε₀, h⟩ := h₀ S η hη
      exact ⟨ε₀, hε₀, 1, one_pos, fun ε t hε hεle _ _ _ => h ε hε hεle t⟩
    | succ a ih =>
      intro haD η hη
      have ha : a < D + 1 := haD
      obtain ⟨Cκ, hCκ, hR⟩ := h₂ S
      have hδ : 0 < η / (2 * (Cκ + 2)) := by positivity
      obtain ⟨τ, hτ, hE⟩ := h₃ S a ha _ hδ

      have ht₀ : 0 < min τ (Real.exp (-S.ell₀)) := lt_min hτ (Real.exp_pos _)
      have hell : S.ell₀ ≤ ell (min τ (Real.exp (-S.ell₀))) := by
        have h : Real.log (min τ (Real.exp (-S.ell₀))) ≤ -S.ell₀ :=
          (Real.log_le_iff_le_exp ht₀).2 (min_le_right _ _)
        show S.ell₀ ≤ Real.log (min τ (Real.exp (-S.ell₀)))⁻¹
        rw [Real.log_inv]
        linarith
      obtain ⟨K, hK, hRK⟩ := hR a ha _ ht₀ hell
      obtain ⟨ε₁, hε₁, t₂, ht₂, hih⟩ := ih (Nat.le_of_succ_le haD) (η / (2 * (K + 1)))
        (by positivity)
      refine ⟨min ε₁ 1, lt_min hε₁ one_pos, min t₂ (min τ (Real.exp (-S.ell₀))),
        lt_min ht₂ ht₀, ?_⟩
      intro ε t hε hεle ht htle htell
      have hJ := hih ε t hε (hεle.trans (min_le_left _ _)) ht (htle.trans (min_le_left _ _)) htell
      have hPL := h₁ S a ha ε t hε ht htell
      have hRep := hRK ε t hε (hεle.trans (min_le_right _ _)) ht (htle.trans (min_le_right _ _))
      obtain ⟨hW, hD⟩ := hE _ t ht (htle.trans (min_le_right _ _)) (min_le_left _ _) hell
      have e1 : (1 + K) * S.J a ε t ≤ η / 2 := by
        calc (1 + K) * S.J a ε t ≤ (1 + K) * (η / (2 * (K + 1))) :=
              mul_le_mul_of_nonneg_left hJ (by linarith)
          _ = η / 2 := by field_simp; ring
      have e2 : Cκ * S.errW a ha (min τ (Real.exp (-S.ell₀))) t +
          2 * S.errDiv a ha (min τ (Real.exp (-S.ell₀))) t ≤ η / 2 := by
        have := mul_le_mul_of_nonneg_left hW hCκ
        calc _ ≤ Cκ * (η / (2 * (Cκ + 2))) + 2 * (η / (2 * (Cκ + 2))) := by linarith
          _ = η / 2 := by field_simp
      linarith
  intro η hη
  obtain ⟨ε₀, hε₀, t₁, ht₁, h⟩ := key (D + 1) le_rfl η hη
  refine ⟨ε₀, hε₀, t₁, ht₁, fun ε t hε hεle ht htle htell => ?_⟩
  have := h ε t hε hεle ht htle htell
  rwa [UIData.J, UIData.T, mixedForms_all] at this

end

end GroundTheory.Heights₂.Heights.AnalyticLimit
end

