import Mathlib
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.Statements
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.SectionInjectivityHypothesesProjectiveLine
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.Bundle0005
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.PointHeightDegreeHypotheses
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.Bundle0012
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.Bundle0001
import GroundTheory.HeightsAndTheta.Heights.HeightComparison.GeoNum
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.CycDim
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.Bundle0009

-- bundled from GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.ChartRingDescriptionAltHolds
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Close

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Geo (chartRingZ)

noncomputable section

variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ}

omit [Fintype ι] in

theorem genPt_ne_zero_of_isLive {P : ArithVariety n} {c : (k : ι) → Fin (n k + 1)}
    (hc : IsLive P c) (k : ι) : genPt P ⟨k, c k⟩ ≠ 0 := by
  intro h
  have h1 : Ideal.Quotient.mk P.ideal (X ⟨k, c k⟩) = 0 :=
    IsFractionRing.injective (CoordRing P) (FunField P) (h.trans (map_zero _).symm)
  exact hc k (Ideal.Quotient.eq_zero_iff_mem.mp h1)

theorem chartPow_ne_zero_of_isLive {P : ArithVariety n} {c : (k : ι) → Fin (n k + 1)}
    (hc : IsLive P c) (a : ι → ℤ) : chartPow P c a ≠ 0 :=
  Finset.prod_ne_zero_iff.mpr fun k _ ↦ zpow_ne_zero _ (genPt_ne_zero_of_isLive hc k)

namespace AddBlockData

variable {P : ArithVariety n} (D : AddBlockData P)

theorem ξ_div_ξ_eq {c : (k : ι) → Fin (n k + 1)} (hc : IsLive P c) (i j : Fin (D.m + 1)) :
    D.ξ c i / D.ξ c j = D.x i / D.x j :=
  mul_div_mul_right _ _ (chartPow_ne_zero_of_isLive hc _)

theorem chartRingZ_chartPlus_eq {c : (k : ι) → Fin (n k + 1)} (hc : IsLive P c)
    (j : Fin (D.m + 1)) :
    chartRingZ D.yPlus (D.chartPlus c j) =
      Algebra.adjoin ℤ ((chartRing P c : Set (FunField P)) ∪
        Set.range fun i ↦ D.ξ c i / D.ξ c j) := by
  have hrange : (Set.range fun p : Coord D.dims ↦ D.yPlus p / D.yPlus ⟨p.1, D.chartPlus c j p.1⟩) =
      (Set.range fun v : Coord n ↦ genPt P v / genPt P ⟨v.1, c v.1⟩) ∪
        Set.range fun i ↦ D.ξ c i / D.ξ c j := by
    ext x
    constructor
    · rintro ⟨⟨_ | k, i⟩, rfl⟩
      · exact Or.inr ⟨i, D.ξ_div_ξ_eq hc i j⟩
      · exact Or.inl ⟨⟨k, i⟩, rfl⟩
    · rintro (⟨v, rfl⟩ | ⟨i, rfl⟩)
      · exact ⟨⟨some v.1, v.2⟩, rfl⟩
      · exact ⟨⟨none, i⟩, (D.ξ_div_ξ_eq hc i j).symm⟩
  rw [chartRingZ, hrange]
  apply le_antisymm
  · refine Algebra.adjoin_mono (Set.union_subset_union_left _ fun x hx ↦ ?_)
    exact Algebra.subset_adjoin hx
  · rw [Algebra.adjoin_le_iff]
    refine Set.union_subset (fun x hx ↦ ?_) fun x hx ↦ Algebra.subset_adjoin (Or.inr hx)
    exact Algebra.adjoin_mono Set.subset_union_left hx

theorem adjoin_ξ_div_eq_adjoin_inv {c : (k : ι) → Fin (n k + 1)} (hc : IsLive P c)
    (j : Fin (D.m + 1)) :
    Algebra.adjoin ℤ ((chartRing P c : Set (FunField P)) ∪ Set.range fun i ↦ D.ξ c i / D.ξ c j) =
      Algebra.adjoin ℤ ((chartRing P c : Set (FunField P)) ∪ {(D.ξ c j)⁻¹}) := by
  set S := Algebra.adjoin ℤ ((chartRing P c : Set (FunField P)) ∪ {(D.ξ c j)⁻¹})
  set T := Algebra.adjoin ℤ ((chartRing P c : Set (FunField P)) ∪
    Set.range fun i ↦ D.ξ c i / D.ξ c j)
  have hAS : (chartRing P c : Set (FunField P)) ⊆ S := fun x hx ↦ Algebra.subset_adjoin (Or.inl hx)
  have hAT : (chartRing P c : Set (FunField P)) ⊆ T := fun x hx ↦ Algebra.subset_adjoin (Or.inl hx)
  apply le_antisymm
  · rw [Algebra.adjoin_le_iff]
    rintro x (hx | ⟨i, rfl⟩)
    · exact hAS hx
    · show D.ξ c i / D.ξ c j ∈ S
      rw [div_eq_mul_inv]
      exact S.mul_mem (hAS (D.chart c hc i)) (Algebra.subset_adjoin (Or.inr rfl))
  · rw [Algebra.adjoin_le_iff]
    rintro x (hx | hx)
    · exact hAT hx
    · rw [Set.mem_singleton_iff] at hx
      subst hx
      obtain ⟨u, hu, hsum⟩ := D.unit c hc
      have h : (D.ξ c j)⁻¹ = ∑ i, u i * (D.ξ c i / D.ξ c j) := by
        rw [← one_mul (D.ξ c j)⁻¹, ← hsum, Finset.sum_mul]
        refine Finset.sum_congr rfl fun i _ ↦ ?_
        simp only [ξ]
        ring
      rw [h]
      exact T.sum_mem fun i _ ↦ T.mul_mem (hAT (hu i)) (Algebra.subset_adjoin (Or.inr ⟨i, rfl⟩))

end AddBlockData

theorem ChartRingDescription.chartRingDescription_alt_holds : ChartRingDescription.Statement := by
  intro ι _ _ n P D c hc j
  exact ⟨D.chartRingZ_chartPlus_eq hc j,
    (D.chartRingZ_chartPlus_eq hc j).trans (D.adjoin_ξ_div_eq_adjoin_inv hc j)⟩

theorem ChartRingDescription.equiv :
    GroundTheory.Heights₂.Heights.ChartRingDescription.Statement ↔
      GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Close.ChartRingDescription.Statement :=
  iff_of_true GroundTheory.Heights₂.Heights.ChartRingDescription.proof ChartRingDescription.chartRingDescription_alt_holds

end

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Close
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.ExistsOneBlockLinMonomial
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Close

open MvPolynomial NumberField
open ReciprocityTheory.ChartRestriction.G.Geo (IsMultiHomog IsArithVar mCoordIdeal secM MRing MRingOver)

noncomputable section

theorem isMultiHomog_unit_iff {R : Type*} [CommRing R] {ι : Unit → Type*} [∀ k, Fintype (ι k)]
    (f : MvPolynomial (Σ k, ι k) R) (N : ℕ) :
    IsMultiHomog (R := R) (ι := ι) f (fun _ ↦ N) ↔ f.IsHomogeneous N := by
  have hdeg : ∀ m : (Σ k, ι k) →₀ ℕ, ∑ i, m ⟨(), i⟩ = Finsupp.weight 1 m := by
    intro m
    have h1 : m.degree = Finsupp.weight 1 m := by
      rw [Finsupp.degree_eq_weight_one]
      rfl
    rw [← h1, Finsupp.degree_eq_sum, Fintype.sum_sigma]
    exact (Fintype.sum_unique (fun u : Unit ↦ ∑ y : ι u, m ⟨u, y⟩)).symm
  simp only [IsMultiHomog, IsHomogeneous, IsWeightedHomogeneous, mem_support_iff]
  constructor
  · intro h d hd
    rw [← hdeg]
    exact h d hd ()
  · intro h m hm k
    cases k
    rw [hdeg]
    exact h hm

theorem isArithVar_comap_rename {ι ι' : Unit → Type*} [∀ k, Fintype (ι k)] [∀ k, Fintype (ι' k)]
    (e : (Σ k, ι k) ≃ (Σ k, ι' k)) {P : Ideal (MRing ι)} {d : ℕ} (hP : IsArithVar P d) :
    IsArithVar (P.comap (rename e.symm : MRing ι' →ₐ[ℤ] MRing ι)) d := by
  obtain ⟨hne, ⟨hprime, ⟨S, hS, hPS⟩, hrel⟩, hhor, hdim⟩ := hP
  let E : MRing ι ≃+* MRing ι' := (renameEquiv ℤ e).toRingEquiv
  have hQ : P.comap (rename e.symm : MRing ι' →ₐ[ℤ] MRing ι) = P.map E := by
    rw [← Ideal.comap_symm]
    rfl
  refine ⟨hne, ⟨?_, ⟨E '' S, ?_, ?_⟩, ?_⟩, ?_, ?_⟩
  · have := hprime
    exact Ideal.comap_isPrime _ _
  · rintro _ ⟨g, hg, rfl⟩
    obtain ⟨a, ha⟩ := hS g hg
    have ha' : a = fun _ ↦ a () := funext fun k ↦ by cases k; rfl
    rw [ha', isMultiHomog_unit_iff] at ha
    refine ⟨fun _ ↦ a (), ?_⟩
    rw [isMultiHomog_unit_iff]
    exact ha.rename_isHomogeneous
  · rw [hQ, hPS, Ideal.map_span]
  · intro k
    cases k
    obtain ⟨i, hi⟩ := hrel ()
    rcases hp : e ⟨(), i⟩ with ⟨⟨⟩, j⟩
    refine ⟨j, fun hj ↦ hi ?_⟩
    have hs : e.symm ⟨(), j⟩ = ⟨(), i⟩ := (Equiv.symm_apply_eq e).mpr hp.symm
    rw [Ideal.mem_comap, rename_X, hs] at hj
    exact hj
  · have h : Ideal.comap (C : ℤ →+* MRing ι') (P.comap (rename e.symm : MRing ι' →ₐ[ℤ] MRing ι)) =
        Ideal.comap (C : ℤ →+* MRing ι) P := by
      ext x
      simp only [Ideal.mem_comap, rename_C]
    unfold ReciprocityTheory.ChartRestriction.G.Geo.IsHorizontal
    rw [h]
    exact hhor
  · rw [← hdim]
    exact (ringKrullDim_eq_of_ringEquiv (Ideal.quotientEquiv P _ E hQ)).symm

section Values

variable {K : Type} [Field K] {d : ℕ} (om : Module.Basis (Fin d) ℤ (𝓞 K)) (i : ℕ)

def oneBlockLin : MvPolynomial (Σ _ : Unit, Fin d × Fin (i + 1)) ℤ →+* MvPolynomial (Fin (i + 1)) (𝓞 K) :=
  eval₂Hom (Int.castRingHom _) fun p ↦ C (om p.2.1) * X p.2.2

def affEval : MvPolynomial (Fin (i + 1)) (𝓞 K) →+* FractionRing (MvPolynomial (Fin i) K) :=
  eval₂Hom ((algebraMap K (FractionRing (MvPolynomial (Fin i) K))).comp (algebraMap (𝓞 K) K)) (affGen K i)

theorem eval₂_oneBlockPt [NumberField K] (g : MvPolynomial (Σ _ : Unit, Fin d × Fin (i + 1)) ℤ) :
    eval₂ (Int.castRingHom _) (oneBlockPt om i) g = affEval i (oneBlockLin om i g) := by
  induction g using MvPolynomial.induction_on with
  | C a => simp only [eval₂_C, oneBlockLin, eval₂Hom_C, Int.coe_castRingHom, map_intCast]
  | add p q hp hq => simp only [eval₂_add, map_add, hp, hq]
  | mul_X p v hp =>
    simp only [eval₂_mul, map_mul, hp, eval₂_X]
    congr 1
    simp [oneBlockLin, affEval, oneBlockPt]

theorem oneBlockLin_isHomogeneous {g : MvPolynomial (Σ _ : Unit, Fin d × Fin (i + 1)) ℤ} {N : ℕ}
    (hg : g.IsHomogeneous N) : (oneBlockLin om i g).IsHomogeneous N := by
  have h : (eval₂ (Int.castRingHom (MvPolynomial (Fin (i + 1)) (𝓞 K))) (fun p ↦ C (om p.2.1) * X p.2.2)
      g).IsHomogeneous (1 * N) := hg.eval₂ _ _ (fun r ↦ ?_) (fun p ↦ ?_)
  · rw [one_mul] at h
    exact h
  · show ((r : MvPolynomial (Fin (i + 1)) (𝓞 K))).IsHomogeneous 0
    rw [← map_intCast (C : 𝓞 K →+* MvPolynomial (Fin (i + 1)) (𝓞 K)) r]
    exact isHomogeneous_C _ _
  · simpa using (isHomogeneous_C (Fin (i + 1)) (om p.2.1)).mul (isHomogeneous_X (𝓞 K) p.2.2)

def linForm (c : 𝓞 K) (j : Fin (i + 1)) : MvPolynomial (Σ _ : Unit, Fin d × Fin (i + 1)) ℤ :=
  ∑ a, C (om.repr c a) * X ⟨(), (a, j)⟩

theorem linForm_isHomogeneous (c : 𝓞 K) (j : Fin (i + 1)) : (linForm om i c j).IsHomogeneous 1 := by
  refine IsHomogeneous.sum _ _ _ fun a _ ↦ ?_
  simpa using (isHomogeneous_C _ (om.repr c a)).mul (isHomogeneous_X ℤ (⟨(), (a, j)⟩ : Σ _ : Unit, Fin d × Fin (i + 1)))

theorem oneBlockLin_linForm (c : 𝓞 K) (j : Fin (i + 1)) :
    oneBlockLin om i (linForm om i c j) = C c * X j := by
  conv_rhs => rw [← om.sum_repr c]
  simp only [linForm, oneBlockLin, map_sum, map_mul, eval₂Hom_C, eval₂Hom_X', Int.coe_castRingHom,
    Finset.sum_mul]
  refine Finset.sum_congr rfl fun a _ ↦ ?_
  rw [zsmul_eq_mul, map_mul, map_intCast, mul_assoc]

def powForm (β : Fin (i + 1) →₀ ℕ) : MvPolynomial (Σ _ : Unit, Fin d × Fin (i + 1)) ℤ :=
  β.prod fun j n ↦ linForm om i 1 j ^ n

theorem powForm_isHomogeneous (β : Fin (i + 1) →₀ ℕ) : (powForm om i β).IsHomogeneous β.degree := by
  have h := IsHomogeneous.prod β.support (fun j ↦ linForm om i 1 j ^ β j) (fun j ↦ 1 * β j)
    (fun j _ ↦ (linForm_isHomogeneous om i 1 j).pow (β j))
  simp only [one_mul] at h
  exact h

theorem oneBlockLin_powForm (β : Fin (i + 1) →₀ ℕ) : oneBlockLin om i (powForm om i β) = monomial β 1 := by
  rw [powForm, map_finsuppProd]
  simp only [map_pow, oneBlockLin_linForm, map_one, one_mul]
  exact prod_X_pow_eq_monomial

theorem exists_oneBlockLin_monomial (α : Fin (i + 1) →₀ ℕ) (hα : α ≠ 0) (c : 𝓞 K) :
    ∃ g, g.IsHomogeneous α.degree ∧ oneBlockLin om i g = monomial α c := by
  obtain ⟨j, hj⟩ : ∃ j, α j ≠ 0 := by
    by_contra h
    push Not at h
    exact hα (Finsupp.ext h)
  have hle : Finsupp.single j 1 ≤ α := Finsupp.single_le_iff.mpr (Nat.one_le_iff_ne_zero.mpr hj)
  have hsplit : α = Finsupp.single j 1 + (α - Finsupp.single j 1) := (add_tsub_cancel_of_le hle).symm
  refine ⟨linForm om i c j * powForm om i (α - Finsupp.single j 1), ?_, ?_⟩
  · have h := (linForm_isHomogeneous om i c j).mul (powForm_isHomogeneous om i (α - Finsupp.single j 1))
    convert h using 1
    conv_lhs => rw [hsplit]
    rw [map_add, Finsupp.degree_single]
  · rw [map_mul, oneBlockLin_linForm, oneBlockLin_powForm, C_mul_X_eq_monomial, monomial_mul, mul_one,
      ← hsplit]

theorem mem_secM_oneBlockPt_iff [NumberField K] (N : ℕ) (hN : 1 ≤ N) (s : FractionRing (MvPolynomial (Fin i) K)) :
    s ∈ secM (oneBlockPt om i) (fun _ ↦ N) ↔
      ∃ F : MvPolynomial (Fin (i + 1)) (𝓞 K), F.IsHomogeneous N ∧
        s = eval₂ ((algebraMap K (FractionRing (MvPolynomial (Fin i) K))).comp
          (algebraMap (𝓞 K) K)) (affGen K i) F := by
  have hev : ∀ F : MvPolynomial (Fin (i + 1)) (𝓞 K),
      eval₂ ((algebraMap K (FractionRing (MvPolynomial (Fin i) K))).comp (algebraMap (𝓞 K) K))
        (affGen K i) F = affEval i F := fun _ ↦ rfl
  simp only [hev]
  rw [secM, Submodule.mem_toAddSubgroup]
  constructor
  · intro hs
    induction hs using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨g, hg, rfl⟩ := hx
      rw [isMultiHomog_unit_iff] at hg
      refine ⟨oneBlockLin om i g, oneBlockLin_isHomogeneous om i hg, ?_⟩
      exact eval₂_oneBlockPt om i g
    | zero => exact ⟨0, isHomogeneous_zero _ _ _, (map_zero (affEval i)).symm⟩
    | add x y _ _ hx hy =>
      obtain ⟨F, hF, rfl⟩ := hx
      obtain ⟨G, hG, rfl⟩ := hy
      exact ⟨F + G, hF.add hG, (map_add (affEval i) F G).symm⟩
    | smul n x _ hx =>
      obtain ⟨F, hF, rfl⟩ := hx
      refine ⟨n • F, ?_, (map_zsmul (affEval i) n F).symm⟩
      rw [zsmul_eq_mul, ← map_intCast (C : 𝓞 K →+* MvPolynomial (Fin (i + 1)) (𝓞 K)) n]
      simpa using hF.C_mul (n : 𝓞 K)
  · rintro ⟨F, hF, rfl⟩
    rw [F.as_sum, map_sum]
    refine Submodule.sum_mem _ fun α hα ↦ ?_
    have hdeg : α.degree = N := by
      have h := hF (mem_support_iff.mp hα)
      rw [← h, Finsupp.degree_eq_weight_one]
      rfl
    have hα0 : α ≠ 0 := by
      rintro rfl
      simp at hdeg
      omega
    obtain ⟨g, hg, hgα⟩ := exists_oneBlockLin_monomial om i α hα0 (coeff α F)
    rw [hdeg] at hg
    refine Submodule.subset_span ⟨g, (isMultiHomog_unit_iff g N).mpr hg, ?_⟩
    rw [← hgα]
    exact eval₂_oneBlockPt om i g

end Values

def oneBlockReindexEquiv (e r : ℕ) :
    Coord (oneBlockSizes e r) ≃ (Σ _ : Unit, Fin (e + 1) × Fin (r + 1)) where
  toFun := oneBlockReindex e r
  invFun := oneBlockReindexInv e r
  left_inv v := by rcases v with ⟨⟨⟩, q⟩; simp [oneBlockReindex, oneBlockReindexInv]
  right_inv p := by rcases p with ⟨⟨⟩, q⟩; simp [oneBlockReindex, oneBlockReindexInv]

theorem OneBlockModel.imp (hA : Heights.OneBlockModel.Statement) : OneBlockModel.Statement := by
  intro K _ _ d om i
  refine ⟨?_, fun N hN s ↦ mem_secM_oneBlockPt_iff om i N hN s⟩
  cases d with
  | zero => exact ((om.index_nonempty).elim fun x ↦ x.elim0)
  | succ e =>
    obtain ⟨hstd, hideal, -⟩ := Heights.OneBlockStandard.proof K e i om
    have h := (hA K i (oneBlockSize e i) (HermLattice.standard K (i + 1)) (oneBlockForms om) hstd).2.2.1
    rw [hideal] at h
    rw [mCoordIdeal_eq_comap om]
    exact isArithVar_comap_rename (oneBlockReindexEquiv e i) h

end

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Close
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.Imports
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial ReciprocityTheory.ChartRestriction.G

theorem GeometricArithmeticNumbers.proof (hF : WeightedDegree.Statement) (hZ : FibreCompDimZ.Statement) :
    GeometricArithmeticNumbers.Statement := by
  intro ι _ _ n P D hdim a p hp
  rw [hF ι n P D hdim a p, NumbersDVR.cycEval, finsum_mem_def]
  refine finsum_congr fun W ↦ ?_
  by_cases hW : W ∈ Geo.divSupp (ι := blockIdx n) P.ideal (C (p : ℤ))
  · rw [Set.indicator_of_mem hW]
    have hW' : W ∈ (P.ideal ⊔ Ideal.span {C (p : ℤ)}).minimalPrimes ∧ NumbersDVR.IsRelevant W := hW
    have hWp : W.IsPrime := hW.1.1.1
    have hpW : (C (p : ℤ) : MvPolynomial (Coord n) ℤ) ∈ W :=
      hW.1.1.2 (Ideal.mem_sup_right (Ideal.subset_span rfl))
    have hC : Geo.IsMultiHomog (ι := blockIdx n) (C (p : ℤ) : MvPolynomial (Coord n) ℤ) 0 := by
      intro m hm k
      have h0 := MvPolynomial.mem_support_iff.mp hm
      rw [coeff_C] at h0
      split_ifs at h0 with h
      · subst h
        simp
      · exact absurd rfl h0
    have hMP : Geo.IsMultiProjPrime (ι := blockIdx n) W :=
      ⟨hWp, ReciprocityTheory.ChartRestriction.G.AI.I1.cyc_isMultiHomogIdeal_of_mem_minimalPrimes
        P.isMultiProjPrime.2.1 hC hW.1, hW.2⟩
    have hdimW : ringKrullDim (Geo.MRing (blockIdx n) ⧸ W) =
        ((D + Fintype.card ι : ℕ) : WithBot ℕ∞) := by
      refine hZ (Coord n) P.ideal P.isPrime P.isHorizontal (D + Fintype.card ι) p hp.out ?_ W hW.1
      rw [show D + Fintype.card ι + 1 = D + 1 + Fintype.card ι by omega]
      exact hdim
    have hm : Geo.multAt (ι := blockIdx n) (P.ideal ⊔ Ideal.span {C (p : ℤ)}) W =
        (NumbersDVR.multAt (P.ideal ⊔ Ideal.span {C (p : ℤ)}) W).toNat := by
      rw [Geo.multAt, dif_pos hWp]
      rfl
    rw [NumbersDVR.divCycle, dif_pos hW', hm,
      Bridge.intNum_map_eq_geoNum p D W hMP hpW hdimW a]
  · have hW' : ¬(W ∈ (P.ideal ⊔ Ideal.span {C (p : ℤ)}).minimalPrimes ∧ NumbersDVR.IsRelevant W) := hW
    rw [Set.indicator_of_notMem hW, NumbersDVR.divCycle, dif_neg hW', zero_mul]

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.LatticePointPairForms
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Close

open NumberField Matrix TensorProduct ComplexAt
open scoped ComplexOrder

noncomputable section

variable {K : Type} [Field K] [NumberField K]

def stdLatticeWith (K : Type) [Field K] [NumberField K] (i : ℕ) (H : (K →+* ℂ) → Matrix (Fin i) (Fin i) ℂ)
    (hH : ∀ σ, (H σ).PosDef) (hc : ∀ σ, H (ComplexEmbedding.conjugate σ) = (H σ).map (starRingEnd ℂ)) :
    HermLattice K i where
  lattice := (HermLattice.standard K i).lattice
  fg := (HermLattice.standard K i).fg
  span_eq := (HermLattice.standard K i).span_eq
  metric := H
  posDef := hH
  conj := hc

def pairForms {d i N : ℕ} (om : Module.Basis (Fin d) ℤ (𝓞 K)) (e : Fin d × Fin i ≃ Fin (N + 1)) :
    Fin (N + 1) → Fin i → K :=
  fun b ↦ Pi.single (e.symm b).2 (om (e.symm b).1 : K)

omit [NumberField K] in

theorem latticePoint_pairForms {R : Type*} [CommRing R] {d i N : ℕ} (om : Module.Basis (Fin d) ℤ (𝓞 K))
    (e : Fin d × Fin i ≃ Fin (N + 1)) (σ : K →+* R) (w : Fin i → R) :
    latticePoint (pairForms om e) σ w = fun _ t ↦ σ (om (e.symm t).1 : K) * w (e.symm t).2 := by
  funext _ t
  simp only [latticePoint, pairForms]
  rw [Finset.sum_eq_single (e.symm t).2 (fun j _ hj ↦ by simp [hj]) (by simp)]
  simp

theorem isDualBasis_pairForms {e' r N : ℕ} (om : Module.Basis (Fin (e' + 1)) ℤ (𝓞 K))
    (e : Fin (e' + 1) × Fin (r + 1) ≃ Fin (N + 1)) :
    IsDualBasis (HermLattice.standard K (r + 1)).lattice (pairForms om e) := by
  obtain ⟨h, -, -⟩ := GroundTheory.Heights₂.Heights.OneBlockStandard.proof K e' r om
  let g : Fin (N + 1) ≃ Fin (oneBlockSize e' r + 1) := e.symm.trans (oneBlockIndex e' r).symm
  have hφ : pairForms om e = oneBlockForms om ∘ g := by
    funext b
    simp [pairForms, oneBlockForms, g]
  rw [hφ]
  exact ⟨h.independent.comp g g.injective, by rw [g.surjective.range_comp]; exact h.span_eq⟩

theorem PointHeightDegree.forward (hL : LineDegreeBundle.Statement) :
    GroundTheory.Heights₂.Heights.PointHeightDegree.Statement → PointHeightDegree.Statement := by
  intro hA K _ _ d om i N e H hH hc A hdeg hmet K' _ _ _ E φ hE ψ v hv
  obtain _ | r := i
  · exact absurd (funext fun j ↦ j.elim0) hv
  obtain _ | e' := d
  · exact absurd (om.repr.injective (Subsingleton.elim _ _) : (1 : 𝓞 K) = 0) one_ne_zero
  let F := stdLatticeWith K (r + 1) H hH hc
  have hv' : (fun j ↦ (v j : K')) ≠ 0 := fun h ↦ hv (funext fun j ↦ by
    simpa using congrFun h j)
  have h := (hA K r N F (pairForms om e) (isDualBasis_pairForms om e)).2 A (funext hdeg)
    (fun σ w hw ↦ by rw [latticePoint_pairForms]; exact hmet σ w hw) K' (fun j ↦ (v j : K')) hv' ψ
  rw [latticePoint_pairForms] at h
  rw [hL K (r + 1) F rfl K' E φ hE v hv]
  have hpt : (fun (_ : Unit) (t : Fin (N + 1)) ↦ (ψ.comp (algebraMap K K')) (om (e.symm t).1 : K) *
      ψ (v (e.symm t).2 : K')) =
      fun _ t ↦ ψ (algebraMap K K' (om (e.symm t).1 : K) * (v (e.symm t).2 : K')) := by
    funext _ t
    simp
  rw [hpt] at h
  linarith

end

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Close
end

