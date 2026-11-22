import Mathlib
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0023
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0003
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0027
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0029
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0028
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0011
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsSegreClosureNumber
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0026

-- bundled from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PFlagBundleSectionDiv
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

namespace FlagBundleSectionDivProof

theorem eq_of_lt_of_le_of_mem_minimalPrimes {A : Type*} [CommRing A] [IsNoetherianRing A]
    {P Q W : Ideal A} [P.IsPrime] [Q.IsPrime] {x : A}
    (hW : W ∈ (P ⊔ Ideal.span {x}).minimalPrimes) (hPQ : P < Q) (hQW : Q ≤ W) : Q = W := by
  by_contra hne
  have hQW' : Q < W := lt_of_le_of_ne hQW hne
  have : W.IsPrime := hW.1.1
  let f := Ideal.Quotient.mk P
  have hf : Function.Surjective f := Ideal.Quotient.mk_surjective
  have hPW : P ≤ W := hPQ.le.trans hQW
  have hker : RingHom.ker f = P := Ideal.mk_ker
  have : (W.map f).IsPrime := Ideal.map_isPrime_of_surjective hf (by rw [hker]; exact hPW)
  have : (Q.map f).IsPrime := Ideal.map_isPrime_of_surjective hf (by rw [hker]; exact hPQ.le)
  have h1 : (W.map f).height ≤ 1 := Ideal.map_height_le_one_of_mem_minimalPrimes hW
  have hlt : Q.map f < W.map f := by
    refine (Ideal.map_mono hQW).lt_of_not_ge fun e => hQW'.not_ge ?_
    have := Ideal.comap_mono (f := f) e
    rwa [Ideal.comap_map_of_surjective f hf, Ideal.comap_map_of_surjective f hf,
      ← RingHom.ker_eq_comap_bot, hker, sup_eq_left.mpr hPW, sup_eq_left.mpr hPQ.le] at this
  have : (W.map f).FiniteHeight := ⟨Or.inr (h1.trans_lt (WithTop.coe_lt_top 1)).ne⟩
  have h2 := (Ideal.height_strict_mono_of_isPrime_of_isPrime hlt).trans_le h1
  rw [Order.lt_one_iff, Ideal.height_eq_zero_iff_eq_bot] at h2
  refine hPQ.not_ge fun q hq => ?_
  have h3 : f q ∈ Q.map f := Ideal.mem_map_of_mem f hq
  rw [h2, Ideal.mem_bot, Ideal.Quotient.eq_zero_iff_mem] at h3
  exact h3

theorem divCycle_eq_zero_of_not_mem {K : Type*} {ι : K → Type*} {R : Type*} [CommRing R]
    {P W : Ideal (MRing ι R)} {x : MRing ι R} (hx : x ∉ W) : divCycle P x W = 0 := by
  unfold divCycle
  rw [dif_neg]
  rintro ⟨h, -⟩
  exact hx (h.1.2 (Ideal.mem_sup_right (Ideal.mem_span_singleton_self x)))

theorem divCycle_congr {K : Type*} {ι : K → Type*} {R : Type*} [CommRing R]
    {P : Ideal (MRing ι R)} {x x' : MRing ι R} (h : x - x' ∈ P) : divCycle P x = divCycle P x' := by
  have hJ : P ⊔ Ideal.span {x} = P ⊔ Ideal.span {x'} := by
    apply le_antisymm
    · refine sup_le le_sup_left ?_
      rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe]
      have := Ideal.add_mem _ (Ideal.mem_sup_left h : x - x' ∈ P ⊔ Ideal.span {x'})
        (Ideal.mem_sup_right (Ideal.mem_span_singleton_self x') : x' ∈ P ⊔ Ideal.span {x'})
      rwa [sub_add_cancel] at this
    · refine sup_le le_sup_left ?_
      rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe]
      have := Ideal.sub_mem _ (Ideal.mem_sup_right (Ideal.mem_span_singleton_self x) : x ∈ P ⊔ Ideal.span {x})
        (Ideal.mem_sup_left h : x - x' ∈ P ⊔ Ideal.span {x})
      rwa [sub_sub_cancel] at this
  funext W
  unfold divCycle
  split_ifs with h1 h2 h2
  · simp only [hJ]
  · exact absurd (hJ ▸ h1) h2
  · exact absurd (hJ.symm ▸ h2) h1
  · rfl

end FlagBundleSectionDivProof

open FlagBundleSectionDivProof in

theorem FlagBundleSectionDiv.proof (hDim : FlagBundleDim.Statement)
    (hSat : MultAtOfSaturated.Statement.{0}) (hForm : ProjIdealFormValue.Statement)
    (hTrunc : TruncSpecialize.Statement) (hChart : FlagBundleChartSection.Statement) :
    FlagBundleSectionDiv.Statement := by
  intro F _ Ω _ _ K _ _ ι _ y e hV hdim N E _ _ B w b hB M a φ hφ Φ _ _ t ht i hi bf bg f g hf hg
    hdeg hgP hval W
  classical
  have hQ : IsMultiProjPrime (projIdeal F y w φ (truncCoord t i)) :=
    (hDim F Ω K ι y e hV hdim N E B w b hB M a φ hφ Φ t ht i hi i.2.le).1
  have hP : IsMultiProjPrime (projIdeal F y w φ (truncCoord t ((i : ℕ) + 1))) :=
    (hDim F Ω K ι y e hV hdim N E B w b hB M a φ hφ Φ t ht ((i : ℕ) + 1) (by omega) i.2).1
  have := hP.isPrime
  have := hQ.isPrime
  obtain ⟨hPQ, hspec⟩ := hTrunc F Ω K ι y N E w M φ Φ t ht i
  have hti : t i ≠ 0 := ht.ne_zero i
  have hval0 := fun (d : Option K → ℕ) (x : MRing (bundleIdx ι M) F) (hx : IsMultiHomog x d) =>
    hForm F Ω K ι y N E w M φ Φ (truncCoord t ((i : ℕ) + 1)) d x hx
  have hgv := fun h => hgP ((hval0 _ _ hg).mpr h)
  have hfP : f ∉ projIdeal F y w φ (truncCoord t ((i : ℕ) + 1)) := fun h =>
    mul_ne_zero hti hgv (hval ▸ (hval0 _ _ hf).mp h)
  by_cases hW : W.IsPrime ∧ IsRelevant W ∧ projIdeal F y w φ (truncCoord t ((i : ℕ) + 1)) ≤ W
  · obtain ⟨hWp, hWrel, hPW⟩ := hW
    choose c hc using fun k => hWrel (some k)
    have hy : segreVec y c ≠ 0 := by
      unfold segreVec
      rw [Finset.prod_ne_zero_iff]
      intro k _ hk
      apply hc k (hPW ?_)
      rw [hval0 _ _ (isWeightedHomogeneous_X F _ _), eval₂_X]
      simp [projCoord, hk]
    obtain ⟨dl, dm, l, μ, m, hμ, hl, hμh, hdl, hlv, hsat⟩ :=
      hChart F Ω K ι y N E B w b hB M a φ hφ Φ t ht i c hy
    have hsW : ∀ n : ℕ, (∏ k, (X ⟨some k, c k⟩ : MRing (bundleIdx ι M) F)) ^ n ∉ W := by
      intro n h
      obtain ⟨k, -, hk⟩ := (Ideal.IsPrime.prod_mem_iff (hp := hWp)).mp (hWp.mem_of_pow_mem n h)
      exact hc k hk
    have hμW : μ ∉ W := by
      rw [hμ]
      intro h
      obtain ⟨k, -, hk⟩ := (Ideal.IsPrime.prod_mem_iff (hp := hWp)).mp h
      exact hc k (hWp.mem_of_pow_mem _ hk)
    have hμP : μ ∉ projIdeal F y w φ (truncCoord t ((i : ℕ) + 1)) := fun h => hμW (hPW h)
    have hμv := fun h => hμP ((hval0 _ _ hμh).mpr h)
    have hlP : l ∉ projIdeal F y w φ (truncCoord t ((i : ℕ) + 1)) := fun h =>
      mul_ne_zero hti hμv (hlv ▸ (hval0 _ _ hl).mp h)
    have hdeg' : bf + dm = dl + bg := by
      funext o
      have h1 := congrFun hdeg o
      have h2 := congrFun hdl o
      simp only [Pi.add_apply] at h1 h2 ⊢
      omega
    have hdiff : f * μ - l * g ∈ projIdeal F y w φ (truncCoord t ((i : ℕ) + 1)) := by
      have h2 := hl.mul hg
      rw [← hdeg'] at h2
      have h1 : IsMultiHomog (f * μ - l * g) (bf + dm) :=
        (mem_weightedHomogeneousSubmodule _ _ _ _).mp (Submodule.sub_mem _
          ((mem_weightedHomogeneousSubmodule _ _ _ _).mpr (hf.mul hμh))
          ((mem_weightedHomogeneousSubmodule _ _ _ _).mpr h2))
      rw [hval0 _ _ h1, eval₂_sub, eval₂_mul, eval₂_mul, hval, hlv]
      ring
    have hrat : ratDiv (projIdeal F y w φ (truncCoord t ((i : ℕ) + 1))) f g W =
        divCycle (projIdeal F y w φ (truncCoord t ((i : ℕ) + 1))) l W := by
      have h1 := congrFun (divCycle_congr hdiff) W
      rw [DivCycleMul.proof.{0} F (Option K) (bundleIdx ι M) _ f μ hP.isPrime hfP hμP,
        DivCycleMul.proof.{0} F (Option K) (bundleIdx ι M) _ l g hP.isPrime hlP hgP] at h1
      simp only [Pi.add_apply, divCycle_eq_zero_of_not_mem hμW] at h1
      unfold ratDiv
      omega
    rw [hrat]
    have hlQ : l ∈ projIdeal F y w φ (truncCoord t i) :=
      (hForm F Ω K ι y N E w M φ Φ (truncCoord t i) dl l hl).mpr (hspec l μ hlv)
    split_ifs with hWQ
    · subst hWQ
      obtain ⟨hmin, hmult⟩ := hSat F (Option K) (bundleIdx ι M) _ _
        (sup_le hPQ ((Ideal.span_singleton_le_iff_mem _).mpr hlQ))
        (fun q hq => by
          obtain ⟨n, hn⟩ := hsat q hq
          exact ⟨_, hsW n, hn⟩)
      unfold divCycle
      rw [dif_pos ⟨hmin, hQ.relevant⟩, hmult]
      rfl
    · by_contra hne
      have hmin : W ∈ (projIdeal F y w φ (truncCoord t ((i : ℕ) + 1)) ⊔ Ideal.span {l}).minimalPrimes := by
        unfold divCycle at hne
        split_ifs at hne with h
        · exact h.1
        · exact absurd rfl hne
      have hQW : projIdeal F y w φ (truncCoord t i) ≤ W := fun q hq => by
        obtain ⟨n, hn⟩ := hsat q hq
        exact (hWp.mem_or_mem (hmin.1.2 hn)).resolve_left (hsW n)
      have hPQ' : projIdeal F y w φ (truncCoord t ((i : ℕ) + 1)) < projIdeal F y w φ (truncCoord t i) :=
        lt_of_le_of_ne hPQ (fun h => hlP (by rw [h]; exact hlQ))
      exact hWQ (eq_of_lt_of_le_of_mem_minimalPrimes hmin hPQ' hQW).symm
  · have h0 : ∀ x, divCycle (projIdeal F y w φ (truncCoord t ((i : ℕ) + 1))) x W = 0 := fun x => by
      unfold divCycle
      rw [dif_neg]
      rintro ⟨h, hr⟩
      exact hW ⟨h.1.1, hr, le_sup_left.trans h.1.2⟩
    have hWQ : W ≠ projIdeal F y w φ (truncCoord t i) := by
      rintro rfl
      exact hW ⟨hQ.isPrime, hQ.relevant, hPQ⟩
    simp [ratDiv, h0, hWQ]

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PFlagLineSectionSplit
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

set_option linter.unusedSectionVars false

namespace FlagLineSectionProof

variable {K : Type*} [Fintype K] [DecidableEq K] {ι : K → Type} {Ω : Type*} [Field Ω] {F : Type*} [Field F]
  [Algebra F Ω] {N : ℕ} {E : Type*} [AddCommGroup E] [Module Ω E]

theorem exists_adapted (y : (Σ k, ι k) → Ω) (B : ChartBundle F (segreVec y) N E)
    (w : Module.Basis (Fin N) Ω E) (b : Fin N → K → ℤ) (hB : IsFlagFrame y B w b) (c : ∀ k, ι k)
    (hc : segreVec y c ≠ 0) (i : Fin N) :
    ∃ v ∈ B.lat c, (∀ j, i < j → w.repr v j = 0) ∧ w.repr v i = chartZ y c (b i) := by
  have h : chartZ y c (b i) ∈ degLat F y (b i) c := ⟨1, one_mem _, by simp [chartZ]⟩
  rw [← hB.graded c hc i] at h
  obtain ⟨v, hv, h1, h2⟩ := h
  exact ⟨v, hv, h1, h2⟩

theorem exists_dual_first (y : (Σ k, ι k) → Ω) (B : ChartBundle F (segreVec y) N E)
    (w : Module.Basis (Fin N) Ω E) (b : Fin N → K → ℤ) (hB : IsFlagFrame y B w b) (c : ∀ k, ι k)
    (hc : segreVec y c ≠ 0) (h0 : 0 < N) :
    ∃ ψ : Module.Dual Ω E, (∀ v ∈ B.lat c, ψ v ∈ chartRing F (segreVec y) c) ∧
      ψ (w ⟨0, h0⟩) * chartZ y c (b ⟨0, h0⟩) = 1 := by
  have hlive := live_of_segreVec_ne_zero hc
  choose e he hup hdiag using exists_adapted y B w b hB c hc
  have hm : ∀ i, chartZ y c (b i) ≠ 0 := fun i => chartZ_ne_zero hlive _
  have hspan : ∀ n : ℕ, ∀ i : Fin N, (i : ℕ) = n → w i ∈ Submodule.span Ω (Set.range e) := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro i hi
      have hsum := w.sum_repr (e i)
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i)] at hsum
      have hrest : ∑ j ∈ Finset.univ.erase i, w.repr (e i) j • w j ∈
          Submodule.span Ω (Set.range e) := by
        refine Submodule.sum_mem _ fun j hj => ?_
        rcases lt_or_gt_of_ne (Finset.ne_of_mem_erase hj) with hlt | hgt
        · exact Submodule.smul_mem _ _ (ih j (by rw [← hi]; exact hlt) j rfl)
        · rw [hup i j hgt, zero_smul]
          exact Submodule.zero_mem _
      have hei : e i ∈ Submodule.span Ω (Set.range e) := Submodule.subset_span ⟨i, rfl⟩
      have h1 : w.repr (e i) i • w i ∈ Submodule.span Ω (Set.range e) := by
        rw [eq_sub_of_add_eq hsum]
        exact Submodule.sub_mem _ hei hrest
      rw [hdiag] at h1
      have h2 := Submodule.smul_mem _ (chartZ y c (b i))⁻¹ h1
      rwa [smul_smul, inv_mul_cancel₀ (hm i), one_smul] at h2
  have htop : ⊤ ≤ Submodule.span Ω (Set.range e) := by
    rw [← w.span_eq, Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    exact hspan i i rfl
  have hcard : Fintype.card (Fin N) = Module.finrank Ω E := by
    rw [Module.finrank_eq_card_basis w]
  set eb := basisOfTopLeSpanOfCardEqFinrank e htop hcard with heb_def
  have heb : ∀ i, eb i = e i := fun i => by
    rw [heb_def, coe_basisOfTopLeSpanOfCardEqFinrank]
  set ψ : Module.Dual Ω E := eb.coord ⟨0, h0⟩ with hψ_def
  have hψe : ∀ i, ψ (e i) ∈ chartRing F (segreVec y) c := by
    intro i
    rw [← heb, hψ_def, Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_apply]
    split_ifs
    · exact one_mem _
    · exact zero_mem _
  have hint : ∀ n : ℕ, n ≤ N → ∀ v ∈ B.lat c, (∀ j : Fin N, n ≤ (j : ℕ) → w.repr v j = 0) →
      ψ v ∈ chartRing F (segreVec y) c := by
    intro n
    induction n with
    | zero =>
      intro _ v _ hv
      have : v = 0 := w.repr.injective (by ext j; simp [hv j (Nat.zero_le _)])
      simp [this]
    | succ n ih =>
      intro hn v hvB hv
      set i : Fin N := ⟨n, hn⟩ with hi_def
      have hmem : w.repr v i ∈ degLat F y (b i) c := by
        rw [← hB.graded c hc i]
        refine ⟨v, hvB, fun j hj => hv j ?_, rfl⟩
        rw [Fin.lt_def] at hj
        simp only [hi_def] at hj
        omega
      obtain ⟨α, hα, hαv⟩ := hmem
      have hv' : v - α • e i ∈ B.lat c := (B.lat c).sub_mem hvB (B.stable c α hα _ (he i))
      have hrec := ih (by omega) _ hv' (fun j hj => by
        rw [map_sub, map_smul, Finsupp.sub_apply, Finsupp.smul_apply, smul_eq_mul]
        rcases Nat.lt_or_ge n (j : ℕ) with hlt | hge
        · rw [hv j (by omega), hup i j (by rw [Fin.lt_def]; exact hlt), mul_zero, sub_zero]
        · have hji : j = i := Fin.ext (by simp only [hi_def]; omega)
          rw [hji, hdiag, hαv]
          simp [chartZ])
      have hsplit : ψ v = ψ (v - α • e i) + α * ψ (e i) := by
        simp [map_sub, smul_eq_mul]
      rw [hsplit]
      exact add_mem hrec (mul_mem hα (hψe i))
  refine ⟨ψ, fun v hv => hint N le_rfl v hv (fun j hj => absurd j.isLt (by omega)), ?_⟩
  have he0 : e ⟨0, h0⟩ = chartZ y c (b ⟨0, h0⟩) • w ⟨0, h0⟩ := by
    conv_lhs => rw [← w.sum_repr (e ⟨0, h0⟩)]
    rw [Finset.sum_eq_single ⟨0, h0⟩]
    · rw [hdiag]
    · intro j _ hj
      rw [hup _ j (by rw [Fin.lt_def]; exact Nat.pos_of_ne_zero (fun h => hj (Fin.ext h))), zero_smul]
    · simp
  have h1 : ψ (e ⟨0, h0⟩) = 1 := by
    rw [← heb, hψ_def, Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_eq_same]
  rw [he0, map_smul, smul_eq_mul] at h1
  rw [mul_comm]
  exact h1

theorem chart_data (y : (Σ k, ι k) → Ω) (B : ChartBundle F (segreVec y) N E)
    (w : Module.Basis (Fin N) Ω E) (b : Fin N → K → ℤ) (hB : IsFlagFrame y B w b) {M : ℕ}
    (a : K → ℤ) (φ : Fin M → Module.Dual Ω E) (hφ : IsTwistedDualGens y B a φ) (c : ∀ k, ι k)
    (hc : segreVec y c ≠ 0) (h0 : 0 < N) :
    (∀ l, φ l (w ⟨0, h0⟩) * chartZ y c (b ⟨0, h0⟩ - a) ∈ chartRing F (segreVec y) c) ∧
      ∃ v : Fin M → Ω, (∀ l, v l ∈ chartRing F (segreVec y) c) ∧
        ∑ l, v l * (φ l (w ⟨0, h0⟩) * chartZ y c (b ⟨0, h0⟩ - a)) = 1 := by
  have hlive := live_of_segreVec_ne_zero hc
  have hsplit : chartZ y c (b ⟨0, h0⟩ - a) = chartZ y c (b ⟨0, h0⟩) * chartZ y c (-a) := by
    rw [sub_eq_add_neg, chartZ_add hlive]
  have hinv : chartZ y c a * chartZ y c (-a) = 1 := by
    rw [← chartZ_add hlive, add_neg_cancel]
    simp [chartZ]
  refine ⟨fun l => ?_, ?_⟩
  · obtain ⟨v0, hv0, hup, hdiag⟩ := exists_adapted y B w b hB c hc ⟨0, h0⟩
    have hv0eq : v0 = chartZ y c (b ⟨0, h0⟩) • w ⟨0, h0⟩ := by
      conv_lhs => rw [← w.sum_repr v0]
      rw [Finset.sum_eq_single ⟨0, h0⟩]
      · rw [hdiag]
      · intro j _ hj
        rw [hup j (by rw [Fin.lt_def]; exact Nat.pos_of_ne_zero (fun h => hj (Fin.ext h))), zero_smul]
      · simp
    obtain ⟨α, hα, hαe⟩ := hφ.sections c hc l v0 hv0
    rw [hv0eq, map_smul, smul_eq_mul] at hαe
    have hαe' : chartZ y c (b ⟨0, h0⟩) * φ l (w ⟨0, h0⟩) = α * chartZ y c a := hαe
    have : φ l (w ⟨0, h0⟩) * chartZ y c (b ⟨0, h0⟩ - a) = α := by
      rw [hsplit]
      linear_combination chartZ y c (-a) * hαe' + α * hinv
    rw [this]
    exact hα
  · obtain ⟨ψ, hψ, hψ1⟩ := exists_dual_first y B w b hB c hc h0
    obtain ⟨u, hu, hψeq⟩ := hφ.generate c hc ψ hψ
    refine ⟨u, hu, ?_⟩
    have h := LinearMap.congr_fun hψeq (w ⟨0, h0⟩)
    rw [LinearMap.sum_apply] at h
    simp only [LinearMap.smul_apply, smul_eq_mul] at h
    rw [← hψ1, h, Finset.sum_mul]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [hsplit]
    simp only [chartZ, Pi.neg_apply]
    ring

end FlagLineSectionProof

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PHsymmPairFlagIndependence
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

noncomputable section

theorem HsymmPairFlagIndependence.proof (hExp : PairNumberExpansionIndependence.Statement)
    (hClos : GenericProjClosureModel.Statement) (hSeg : SegreClosureNumber.Statement) :
    HsymmPairFlagIndependence.Statement := by
  intro O _ _ _ ϖ hϖ Ω _ _ K _ _ ι _ y d hV N E _ _ B B' hBB' w w' v v' x x' u u' f g f₂ g₂
    hF1 hF2 n z z' fz gz hz a r R hR As Bs hAs hBs Q hQ
  classical
  have hA : (hsymmTimes N n a R).IsHomogeneous (a + r) :=
    (isHomogeneous_hsymm N a).rename_isHomogeneous.mul hR.rename_isHomogeneous
  rcases Nat.eq_zero_or_pos N with rfl | hN
  ·
    obtain rfl : x = u := funext fun i => i.elim0
    obtain rfl : x' = u' := funext fun i => i.elim0
    obtain rfl : f = f₂ := funext fun i => i.elim0
    obtain rfl : g = g₂ := funext fun i => i.elim0
    refine hExp O ϖ hϖ K ι (pointIdeal O y) d hV (0 + n) _ _ _ _ (fun i => ?_) (a + r) _ hA As Bs
      hAs hBs Q hQ
    refine Fin.addCases (fun i => i.elim0) (fun j => ?_) i
    simp only [Fin.append_right]
    exact hz j
  ·
    let Φ := FractionRing (MvPolynomial (Fin N) Ω)
    let t : Fin N → Φ := fun i => algebraMap (MvPolynomial (Fin N) Ω) Φ (X i)
    have ht : AlgebraicIndependent Ω t :=
      (MvPolynomial.algebraicIndependent_X (Fin N) Ω).map'
        (f := IsScalarTower.toAlgHom Ω (MvPolynomial (Fin N) Ω) Φ)
        (IsFractionRing.injective (MvPolynomial (Fin N) Ω) Φ)
    obtain ⟨M, M', a₀, a₀', φ, φ', hφ, hφ', hZ, f₀, g₀, hD₀, hD₀gen⟩ :=
      hClos O ϖ hϖ Ω K ι y d hV N hN E B B' hBB' Φ w t ht
    have hC : (zetaPowTimes n (N - 1 + a) R).IsHomogeneous (N - 1 + a + r) := by
      have h := ((isHomogeneous_X ℤ (Fin.castAdd n (0 : Fin 1))).pow (N - 1 + a)).mul
        (hR.rename_isHomogeneous (f := (Fin.natAdd 1 : Fin n → Fin (1 + n))))
      rwa [one_mul] at h
    obtain ⟨Cs, hCs⟩ := exists_isPairExpansion hC
    rw [hSeg O ϖ hϖ Ω K ι y d hV N hN E B B' hBB' w w' x x' f g hF1 M M' a₀ a₀' φ φ' hφ hφ' Φ w t ht
        hZ f₀ g₀ hD₀ hD₀gen n z z' fz gz hz a r R hR As hAs Cs hCs Q hQ,
      hSeg O ϖ hϖ Ω K ι y d hV N hN E B B' hBB' v v' u u' f₂ g₂ hF2 M M' a₀ a₀' φ φ' hφ hφ' Φ w t ht
        hZ f₀ g₀ hD₀ hD₀gen n z z' fz gz hz a r R hR Bs hBs Cs hCs Q hQ]

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PLocalCoeffRing
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

universe u

private theorem mem_minimalPrimes_of_locCycle_ne_zero {S : Type*} [CommRing S] {J W : Ideal S}
    (h : locCycle J W ≠ 0) : W ∈ J.minimalPrimes := by
  by_contra hc
  exact h (by unfold locCycle; rw [dif_neg hc])

theorem LocalCoeffRing.proof (h₁ : LocalQuotRing.Statement.{u}) (h₂ : LocalQuotPrimes.Statement.{u})
    (h₃ : LocCycleLocalQuot.Statement.{u}) (h₄ : LocalQuotColon.Statement.{u})
    (h₅ : LocalQuotFinsum.Statement.{u}) (h₆ : LocalCoeffLocal.Statement.{u}) :
    LocalCoeffRing.Statement.{u} := by
  intro R _ _ P U hP hU hPU hchain f g s u v hf hg hs hu huv hno
  have := hU
  obtain ⟨hdom, hloc, hunit, hker⟩ := h₁ R P U hP hPU
  have := hdom
  have := hloc
  obtain ⟨hup, hdown⟩ := h₂ R P U hPU
  have hmin := fun {J W : Ideal R} (h : locCycle J W ≠ 0) => mem_minimalPrimes_of_locCycle_ne_zero h
  have hmin' := fun {J W : Ideal (localQuot P U)} (h : locCycle J W ≠ 0) =>
    mem_minimalPrimes_of_locCycle_ne_zero h

  have hm : IsLocalRing.maximalIdeal (localQuot P U) = U.map (localQuotMap P U) := by
    ext y
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, hunit, not_not]
  have hUc : (U.map (localQuotMap P U)).comap (localQuotMap P U) = U := (hup U hU hPU le_rfl).2
  have hPbot : P.map (localQuotMap P U) = ⊥ :=
    (Ideal.map_eq_bot_iff_le_ker _).mpr fun y hy => RingHom.mem_ker.mpr ((hker y).2 hy)
  have hmapx : ∀ x : R, (P ⊔ Ideal.span {x}).map (localQuotMap P U) =
      Ideal.span {localQuotMap P U x} := by
    intro x
    rw [Ideal.map_sup, Ideal.map_span, Set.image_singleton, hPbot, bot_sup_eq]

  have hchain' : ∀ Q₁ Q₂ : Ideal (localQuot P U), Q₁.IsPrime → Q₂.IsPrime → ⊥ < Q₁ → Q₁ < Q₂ →
      Q₂ < IsLocalRing.maximalIdeal (localQuot P U) → False := by
    intro Q₁ Q₂ hQ₁ hQ₂ h0 h12 h2m
    obtain ⟨hP1, -, he1⟩ := hdown Q₁ hQ₁
    obtain ⟨-, hU2, he2⟩ := hdown Q₂ hQ₂
    exact hchain _ _ (Ideal.comap_isPrime _ _) (Ideal.comap_isPrime _ _)
      (lt_of_le_of_ne hP1 fun h => h0.ne (by rw [← he1, ← h, hPbot]))
      (lt_of_le_of_ne (Ideal.comap_mono h12.le) fun h => h12.ne (by rw [← he1, ← he2, h]))
      (lt_of_le_of_ne hU2 fun h => h2m.ne (by rw [← he2, h, hm]))
  have hne : ∀ x : R, x ∉ P → localQuotMap P U x ≠ 0 := fun x hx h => hx ((hker x).1 h)
  have hloc' := h₆ (localQuot P U) hchain' (localQuotMap P U f) (localQuotMap P U g)
    (localQuotMap P U s) (localQuotMap P U u) (localQuotMap P U v) (hne f hf) (hne g hg) (hne s hs)
    ((hunit _).2 fun h => hu (hUc ▸ Ideal.mem_comap.mpr h))
    (by rw [← sub_eq_zero, ← map_mul, ← map_mul, ← map_sub]; exact (hker _).2 huv) ?_
  swap
  ·
    intro W hW
    have hWm := hmin' hW
    have := hWm.1.1
    obtain ⟨hPW, hWU, hWe⟩ := hdown W hWm.1.1
    have h := hno (W.comap (localQuotMap P U)) hWU
    rw [h₃ R P U _ _ le_sup_left inferInstance hPW hWU, h₃ R P U (P ⊔ Ideal.span {f}) _ le_sup_left
      inferInstance hPW hWU, h₃ R P U (P ⊔ Ideal.span {g}) _ le_sup_left inferInstance hPW hWU,
      hmapx, hmapx, hmapx, hWe] at h
    exact h hW
  rw [hm] at hloc'
  convert hloc' using 1
  ·
    apply h₅ R P U hPU
    · intro G hG
      have hGU : G ≤ U := le_sup_left.trans (hmin (right_ne_zero_of_mul hG)).1.2
      have h2 := left_ne_zero_of_mul hG
      by_cases h : locCycle (P ⊔ Ideal.span {f}) G = 0
      · rw [h, zero_sub, neg_ne_zero] at h2
        exact ⟨(hmin h2).1.1, le_sup_left.trans (hmin h2).1.2, hGU⟩
      · exact ⟨(hmin h).1.1, le_sup_left.trans (hmin h).1.2, hGU⟩
    · intro p hp
      have h2 := left_ne_zero_of_mul hp
      by_cases h : locCycle (Ideal.span {localQuotMap P U f}) p = 0
      · rw [h, zero_sub, neg_ne_zero] at h2
        exact (hmin' h2).1.1
      · exact (hmin' h).1.1
    · intro G hG hPG hGU
      rw [h₃ R P U _ G le_sup_left hG hPG hGU, h₃ R P U (P ⊔ Ideal.span {g}) G le_sup_left hG hPG hGU,
        h₃ R P U (G ⊔ Ideal.span {s}) U (le_sup_of_le_left hPG) hU hPU le_rfl, hmapx, hmapx,
        Ideal.map_sup, Ideal.map_span, Set.image_singleton]
  ·
    apply h₅ R P U hPU
    · intro W hW
      have h1 := hmin (left_ne_zero_of_mul hW)
      have h2 := hmin (right_ne_zero_of_mul hW)
      exact ⟨h1.1.1, le_sup_left.trans h1.1.2, le_sup_left.trans h2.1.2⟩
    · intro p hp
      exact (hmin' (left_ne_zero_of_mul hp)).1.1
    · intro W hW hPW hWU
      rw [h₃ R P U _ W le_sup_left hW hPW hWU, h₃ R P U (W ⊔ _) U (le_sup_of_le_left hPW) hU hPU le_rfl,
        hmapx, Ideal.map_sup, h₄ R P U f g]

end GroundTheory.Heights₂.Heights.NumbersDVR
end

