import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1462
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0022
import Development.AbelianVarietyTheory.Definitions.Divisors.IsSquareIntegrableIffMemL2
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1473
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1478
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0296
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1409
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1406
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1474
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1057
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1448
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1468
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0075
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1475
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0019
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1446
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1444
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1479
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1465
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1466
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1397
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1368

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagUnipotentRadicalLeStandardParabolicUnipotent
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.ThK.SquareIntegrability
open Formalism.UG (cT)
open Matrix

noncomputable section

namespace GlobalTheory.FlagRad

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

omit [NumberField E] in

theorem mulVec_initCols_mem {n r : ℕ} (X : Matrix (Fin n) (Fin r) E) (m : Fin r) (A : Set (Fin r))
    (a : Fin (m.val + 1) → AF F ⊗[F] E) (ha : ∀ l, a l ≠ 0 → Fin.castLE m.2 l ∈ A) :
    adMat F (GlobalTheory.StdPar.initCols X m) *ᵥ a ∈ GlobalTheory.StdPar.colSpan F X A := by
  rw [Matrix.mulVec_eq_sum]
  refine sum_mem fun l _ => ?_
  by_cases h : a l = 0
  · simp [h]
  · rw [op_smul_eq_smul]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, ha l h, rfl⟩)

theorem exists_of_card_lt {r : ℕ} (S : Finset (Fin r)) {a b : ℕ}
    (h : (S.filter fun k => k.val < a).card < (S.filter fun k => k.val < b).card) :
    ∃ k ∈ S, a ≤ k.val ∧ k.val < b := by
  by_contra hc
  push_neg at hc
  refine absurd h (not_lt.2 (Finset.card_le_card fun k hk => ?_))
  simp only [Finset.mem_filter] at hk ⊢
  exact ⟨hk.1, not_le.1 fun h' => absurd hk.2 (not_lt.2 (hc k hk.1 h'))⟩

open GlobalTheory.StdPar in

theorem unipFlag_le_unip (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (h : IsCMExt F E σ) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (hJ : IsHermND σ J) (r : ℕ)
    (X Y : Matrix (Fin n) (Fin r) E) (hW : IsWittFrame σ J X Y) (S : Finset (Fin r)) (m : Fin r) (hmS : m ∈ S)
    (hm : ∀ k ∈ S, k ≤ m) :
    GlobalTheory.UAut.unipFlag σ J (GlobalTheory.StdPar.initCols X m) (fun i => (S.filter fun k => k.val < i.val).card) ≤
      GlobalTheory.StdPar.unip σ J X S := by
  set C := initCols X m with hCdef
  set d : Fin (m.val + 1) → ℕ := fun i => (S.filter fun k => k.val < i.val).card with hd
  have hσ : ∀ x, σ (σ x) = x := GlobalTheory.SiegelSet.sigma_sigma h
  have hC : IsIsoCols σ J C := isIsoCols_of_isWittFrame hW hσ hJ m.2
  have memS : ∀ g ∈ unipFlag σ J C d, g ∈ unipSet σ J C d := fun g hg => (mem_unipFlag hJ hσ hC d).1 hg

  have stab : ∀ g ∈ unipSet σ J C d, ∀ A : Set (Fin r), (∀ i ∈ A, i.val ≤ m.val) →
      (∀ l l' : Fin (m.val + 1), Fin.castLE m.2 l ∈ A → d l' < d l → Fin.castLE m.2 l' ∈ A) →
      ∀ y ∈ colSpan F X A, (matHom _ σ J g).1 *ᵥ y ∈ colSpan F X A := by
    intro g hg A hA1 hA2 y hy
    have hle : colSpan F X A ≤ (colSpan F X A).comap (matHom _ σ J g).1.mulVecLin := by
      refine Submodule.span_le.2 ?_
      rintro _ ⟨i, hi, rfl⟩
      obtain ⟨a, ha0, ha⟩ := hg.1 ⟨i.val, Nat.lt_succ_of_le (hA1 i hi)⟩
      have ha' : ((matHom _ σ J g).1 - 1) *ᵥ (adMat F X)ᵀ i = adMat F C *ᵥ a := ha
      have e : (matHom _ σ J g).1 *ᵥ (adMat F X)ᵀ i = (adMat F X)ᵀ i + ((matHom _ σ J g).1 - 1) *ᵥ (adMat F X)ᵀ i := by
        rw [Matrix.sub_mulVec, Matrix.one_mulVec, add_sub_cancel]
      show (matHom _ σ J g).1 *ᵥ (adMat F X)ᵀ i ∈ colSpan F X A
      rw [e, ha']
      refine add_mem (Submodule.subset_span ⟨i, hi, rfl⟩) (GlobalTheory.FlagRad.mulVec_initCols_mem X m A a fun l' hl' => ?_)
      exact hA2 ⟨i.val, Nat.lt_succ_of_le (hA1 i hi)⟩ l' hi (not_le.1 fun h' => hl' (ha0 l' h'))
    exact hle hy
  have inv_app : ∀ (g : GAd σ J) y, (matHom _ σ J g⁻¹).1 *ᵥ (matHom _ σ J g).1 *ᵥ y = y := fun g y => by
    rw [mulVec_mulVec, ← Units.val_mul, ← map_mul, inv_mul_cancel, map_one, Units.val_one, one_mulVec]
  intro g hg
  have hg1 := memS g hg
  have hg2 := memS g⁻¹ (inv_mem hg)
  have iffPart : ∀ A : Set (Fin r), (∀ i ∈ A, i.val ≤ m.val) →
      (∀ l l' : Fin (m.val + 1), Fin.castLE m.2 l ∈ A → d l' < d l → Fin.castLE m.2 l' ∈ A) →
      ∀ y, y ∈ colSpan F X A ↔ (matHom _ σ J g).1 *ᵥ y ∈ colSpan F X A := fun A hA1 hA2 y =>
    ⟨stab g hg1 A hA1 hA2 y, fun hy => by
      have := stab g⁻¹ hg2 A hA1 hA2 _ hy
      rwa [inv_app] at this⟩
  have e1 : {i | ∃ k ∈ S, i ≤ k} = {i | i ≤ m} :=
    Set.ext fun i => ⟨fun ⟨k, hk, hik⟩ => hik.trans (hm k hk), fun hi => ⟨m, hmS, hi⟩⟩
  have hB1 : ∀ i ∈ {i : Fin r | i ≤ m}, i.val ≤ m.val := fun i hi => hi
  have hB2 : ∀ l l' : Fin (m.val + 1), Fin.castLE m.2 l ∈ {i : Fin r | i ≤ m} → d l' < d l →
      Fin.castLE m.2 l' ∈ {i : Fin r | i ≤ m} := fun l l' _ _ => Nat.le_of_lt_succ l'.2
  have sub_app : ∀ y, (matHom _ σ J g).1 *ᵥ y - y = ((matHom _ σ J g).1 - 1) *ᵥ y := fun y => by
    simp [Matrix.sub_mulVec]
  refine ⟨Subgroup.mem_iInf.2 fun j => ⟨iffPart _ ?_ ?_, fun y hy => ?_⟩, ?_⟩
  · rintro i ⟨k, hk, hik, -⟩
    exact hik.trans (hm k hk)
  · rintro l l' ⟨k, hk, hlk, hkj⟩ hdl
    obtain ⟨k', hk', h1, h2⟩ := GlobalTheory.FlagRad.exists_of_card_lt S hdl
    refine ⟨k', hk', h1, ?_⟩
    rw [Fin.le_def] at hlk
    rw [Fin.lt_def] at hkj ⊢
    simp only [Fin.coe_castLE] at hlk
    omega
  ·
    have hle : colSpan F X {j} ≤ (colSpan F X {i | ∃ k ∈ S, i ≤ k ∧ k < j}).comap
        ((matHom _ σ J g).1 - 1).mulVecLin := by
      refine Submodule.span_le.2 ?_
      rintro _ ⟨i, hi', rfl⟩
      have hij : i = j := hi'
      simp only [SetLike.mem_coe, Submodule.mem_comap, Matrix.mulVecLin_apply]
      by_cases hi : i.val ≤ m.val
      · obtain ⟨a, ha0, ha⟩ := hg1.1 ⟨i.val, Nat.lt_succ_of_le hi⟩
        have e : ((matHom _ σ J g).1 - 1) *ᵥ (adMat F X)ᵀ i = adMat F C *ᵥ a := ha
        rw [e]
        refine GlobalTheory.FlagRad.mulVec_initCols_mem X m _ a fun l' hl' => ?_
        obtain ⟨k, hk, h1, h2⟩ := GlobalTheory.FlagRad.exists_of_card_lt S (not_le.1 fun h' => hl' (ha0 l' h'))
        refine ⟨k, hk, h1, ?_⟩
        rw [Fin.lt_def, ← hij]
        exact h2
      · have hx : (cT (σ : E →+* E) C * J) *ᵥ (fun k => X k i) = 0 :=
          funext fun l => congrFun (congrFun hW.xx (l.castLE m.2)) i
        obtain ⟨a, ha⟩ := hg1.2 _ hx
        have e : ((matHom _ σ J g).1 - 1) *ᵥ (adMat F X)ᵀ i = adMat F C *ᵥ a := ha
        rw [e]
        refine GlobalTheory.FlagRad.mulVec_initCols_mem X m _ a fun l' _ => ⟨m, hmS, Nat.le_of_lt_succ l'.2, ?_⟩
        rw [Fin.lt_def, ← hij]
        omega
    rw [sub_app]
    exact hle hy
  · rw [e1]
    refine ⟨iffPart _ hB1 hB2, fun y hy => ?_⟩
    set T := cT (σ : E →+* E) (initCols X m) * J
    have hT : T * initCols Y m = 1 := Matrix.ext fun i j =>
      (congrFun (congrFun hW.xy (i.castLE m.2)) (j.castLE m.2)).trans (by simp [Matrix.one_apply])
    have hQ : T * (1 - initCols Y m * T) = 0 := by
      rw [Matrix.mul_sub, ← Matrix.mul_assoc, hT, Matrix.one_mul, Matrix.mul_one, sub_self]
    have hy' : y = adMat F (1 - initCols Y m * T) *ᵥ y := by
      rw [adMat, Matrix.map_sub _ (map_sub _), Matrix.map_one _ (map_zero _) (map_one _), Matrix.map_mul, sub_mulVec,
        one_mulVec, ← mulVec_mulVec, mem_colPerp_iff.1 hy, mulVec_zero, sub_zero]
    have : (matHom _ σ J g).1 *ᵥ y - y = ((matHom _ σ J g).1 - 1).mulVecLin y := by simp [sub_mulVec]
    rw [this, hy', mulVec_eq_sum, map_sum]
    refine sum_mem fun j _ => ?_
    rw [op_smul_eq_smul, map_smul]
    obtain ⟨a, ha⟩ := hg1.2 (fun i => (1 - initCols Y m * T : Matrix (Fin n) (Fin n) E) i j)
      (funext fun i => congrFun (congrFun hQ i) j)
    exact Submodule.smul_mem _ _ (mem_colSpan_iff.2 ⟨a, ha.symm⟩)

end GlobalTheory.FlagRad
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FullRankCoinvariantInducedIso
section
noncomputable section

open MeasureTheory GlobalTheory.SplitFlip
open scoped Topology Matrix

namespace GlobalTheory.FullRankCoinv

theorem sb_right_invariant : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (n d : ℕ) (Ψ : Matrix (Fin n) (Fin d) k → ℂ), Ψ ∈ GlobalTheory.WeilM.SB (Matrix (Fin n) (Fin d) k) →
    ∃ U ∈ nhds (1 : GL (Fin d) k), ∀ u ∈ U, ∀ X : Matrix (Fin n) (Fin d) k, Ψ (X * u.val) = Ψ X := by
  intro k _ _ _ _ n d Ψ hΨ
  have h1 : ∀ᶠ u in 𝓝 (1 : GL (Fin d) k), ∀ X ∈ tsupport Ψ, Ψ (X * u.val) = Ψ X := by
    refine IsCompact.eventually_forall_of_forall_eventually hΨ.2 fun y _ => ?_
    have h2 : IsLocallyConstant fun q : GL (Fin d) k × Matrix (Fin n) (Fin d) k => (Ψ (q.2 * q.1.val), Ψ q.2) :=
      (hΨ.1.comp_continuous (by fun_prop)).prodMk (hΨ.1.comp_continuous continuous_snd)
    filter_upwards [h2.eventually_eq (1, y)] with q hq
    simp only [Prod.mk.injEq, Units.val_one, Matrix.mul_one] at hq
    rw [hq.1, hq.2]
  have h3 : ∀ᶠ u in 𝓝 (1 : GL (Fin d) k), ∀ X ∈ tsupport Ψ, Ψ (X * (u⁻¹).val) = Ψ X := by
    have ht : Filter.Tendsto (fun u : GL (Fin d) k => u⁻¹) (𝓝 1) (𝓝 1) := by
      simpa using (continuous_inv.tendsto (1 : GL (Fin d) k))
    exact ht.eventually h1
  refine ⟨_, h1.and h3, fun u hu X => ?_⟩
  by_cases hX : X ∈ tsupport Ψ
  · exact hu.1 X hX
  by_cases hX' : X * u.val ∈ tsupport Ψ
  · have := hu.2 _ hX'
    rw [Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.mul_one] at this
    exact this.symm
  · rw [image_eq_zero_of_notMem_tsupport hX, image_eq_zero_of_notMem_tsupport hX']

theorem fibre_coinvariants : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (n d : ℕ) (ν : kˣ →* ℂˣ), n ≤ d → GlobalTheory.SmGL.IsSmoothChar ν →
    ∃ Z : (Matrix (Fin n) (Fin d) k → ℂ) →ₗ[ℂ] (GL (Fin d) k → ℂ),
      (∀ Ψ ∈ GlobalTheory.FullRankCoinv.fullRk k n d, Z Ψ ∈ GlobalTheory.FullRankCoinv.indSp k n d ν) ∧
      (∀ f ∈ GlobalTheory.FullRankCoinv.indSp k n d ν, ∃ Ψ ∈ GlobalTheory.FullRankCoinv.fullRk k n d, Z Ψ = f) ∧
      (∀ Ψ ∈ GlobalTheory.FullRankCoinv.fullRk k n d, Z Ψ = 0 → Ψ ∈ GlobalTheory.FullRankCoinv.augRk n d ν) ∧
      ∀ Ψ ∈ GlobalTheory.FullRankCoinv.fullRk k n d, ∀ h₀ : GL (Fin d) k,
        Z (fun Y => Ψ (Y * h₀.1)) = fun h => Z Ψ (h * h₀) := by
  intro k _ _ _ _ n d ν hnd hν
  letI : MeasurableSpace k := borel k
  haveI : BorelSpace k := ⟨rfl⟩
  let Z₀ : fullRk k n d →ₗ[ℂ] (GL (Fin d) k → ℂ) :=
    { toFun := fun Ψ h => smallF (haarVol (GlobalTheory.SplitWeil.KO k (Fin n))) ν Ψ.1 (Y0 k n d * h.val)
      map_add' := fun Ψ Φ => by
        funext h
        simp only [smallF, Submodule.coe_add, Pi.add_apply]
        rw [← integral_add (GlobalTheory.T.integrable_full_rank_zeta k n d ν hν Ψ.1 Ψ.2 _) (GlobalTheory.T.integrable_full_rank_zeta k n d ν hν Φ.1 Φ.2 _)]
        congr 1; funext g; ring
      map_smul' := fun c Ψ => by
        funext h
        simp only [smallF, SetLike.val_smul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
        rw [← integral_const_mul]
        congr 1; funext g; ring }
  obtain ⟨Z, hZ⟩ := LinearMap.exists_extend Z₀
  have hZΨ : ∀ Ψ (hΨ : Ψ ∈ fullRk k n d),
      Z Ψ = fun h => smallF (haarVol (GlobalTheory.SplitWeil.KO k (Fin n))) ν Ψ (Y0 k n d * h.val) :=
    fun Ψ hΨ => LinearMap.congr_fun hZ ⟨Ψ, hΨ⟩
  refine ⟨Z, fun Ψ hΨ => ?_, fun f hf => ?_, fun Ψ hΨ h0 => ?_, fun Ψ hΨ h₀ => ?_⟩
  · rw [hZΨ Ψ hΨ]
    refine ⟨?_, fun b h D hD => ?_⟩
    · obtain ⟨U, hU, hinv⟩ := sb_right_invariant k n d Ψ hΨ.1
      refine ⟨U, hU, fun h u hu => ?_⟩
      simp only [smallF]
      congr 1; funext g
      rw [Units.val_mul, ← Matrix.mul_assoc, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hinv u hu, Matrix.mul_assoc]
    · have e1 : Y0 k n d * (b * h).val = D.val * (Y0 k n d * h.val) := by
        rw [Units.val_mul, ← Matrix.mul_assoc, hD, Matrix.mul_assoc]
      have key := smallF_mul_left (haarVol (GlobalTheory.SplitWeil.KO k (Fin n))) ν Ψ D (Y0 k n d * h.val)
      simp only [Fintype.card_fin] at key
      show smallF _ ν Ψ (Y0 k n d * (b * h).val) = _
      rw [e1]
      beta_reduce
      rw [← key, Units.val_inv_eq_inv_val, neg_div, apow_neg]
      have h1 : (ν (gdet D) : ℂ) ≠ 0 := Units.ne_zero _
      have h2 := apow_ne_zero (gdet D) ((d : ℂ) / 2)
      field_simp
  · obtain ⟨Ψ, hΨ, hf'⟩ := GlobalTheory.T.full_rank_zeta_surjective k n d ν hnd hν f hf
    exact ⟨Ψ, hΨ, by rw [hZΨ Ψ hΨ]; funext h; exact hf' h⟩
  · refine GlobalTheory.T.full_rank_zeta_kernel k n d ν hnd hν Ψ hΨ fun h => ?_
    have := congrFun h0 h
    rwa [hZΨ Ψ hΨ] at this
  · have hmem : (fun Y => Ψ (Y * h₀.1)) ∈ fullRk k n d := by
      let e : Matrix (Fin n) (Fin d) k ≃ₜ Matrix (Fin n) (Fin d) k :=
        { toFun := fun X => X * h₀.1
          invFun := fun X => X * (h₀⁻¹).1
          left_inv := fun X => by simp [Matrix.mul_assoc]
          right_inv := fun X => by simp [Matrix.mul_assoc]
          continuous_toFun := by fun_prop
          continuous_invFun := by fun_prop }
      refine ⟨⟨hΨ.1.1.comp_continuous e.continuous, hΨ.1.2.comp_homeomorph e⟩, fun Y hY => hΨ.2 _ ?_⟩
      rwa [Matrix.rank_mul_eq_left_of_isUnit_det _ _ (Matrix.isUnits_det_units h₀)]
    rw [hZΨ _ hmem, hZΨ _ hΨ]
    funext h
    simp only [smallF, Units.val_mul, Matrix.mul_assoc]

end GlobalTheory.FullRankCoinv
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HaarScalingMultiplicative
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

namespace GlobalTheory.AdeleUnitModule

open scoped Pointwise ENNReal

theorem map_smul_eq_inv_smul {G A : Type} [Group G] [AddCommGroup A] [DistribMulAction G A] [TopologicalSpace A]
    [IsTopologicalAddGroup A] [LocallyCompactSpace A] [SecondCountableTopology A] [T2Space A]
    [ContinuousConstSMul G A] [MeasurableSpace A] [BorelSpace A] (μ : Measure A) [μ.IsAddHaarMeasure] (g : G) :
    μ.map (fun x => g • x) = ((distribHaarChar A g : ℝ≥0∞))⁻¹ • μ := by
  have h1 : DomMulAct.mk g⁻¹ • μ = μ.map (fun x => g • x) := by
    ext s hs
    rw [Measure.domSMul_apply, Measure.map_apply (measurable_const_smul g) hs, Set.preimage_smul]
    simp
  have h2 := Measure.isAddLeftInvariant_eq_smul (DomMulAct.mk g⁻¹ • μ) μ
  rw [addHaarScalarFactor_smul_eq_distribHaarChar μ g⁻¹, map_inv (distribHaarChar A)] at h2
  rw [← h1, h2, ENNReal.smul_def, ENNReal.coe_inv (distribHaarChar_pos).ne']

open GroundTheory.Global GroundTheory.Global.AdeleBaseChange

theorem distribHaarChar_eq_absE (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    [IsTopologicalRing (AE F E)] [LocallyCompactSpace (AE F E)] [SecondCountableTopology (AE F E)] [T2Space (AE F E)]
    (t : (AE F E)ˣ) : distribHaarChar (AE F E) t = absE F E t := by
  have : IsModuleTopology (AF F) (AE F E) := ⟨rfl⟩
  have := IsModuleTopology.toContinuousSMul (AF F) (AE F E)
  have : IsModuleTopology (AF F) (AdeleRing (𝓞 E) E) := isModuleTopology_adeleRing
  let φ : AE F E ≃ₜ+ AdeleRing (𝓞 E) E :=
    { (adeleTensorAlgEquivLeft F E).toAddEquiv with
      continuous_toFun := IsModuleTopology.continuous_of_linearMap (adeleTensorAlgEquivLeft F E).toLinearMap
      continuous_invFun := IsModuleTopology.continuous_of_linearMap (adeleTensorAlgEquivLeft F E).symm.toLinearMap }
  haveI : SecondCountableTopology (AdeleRing (𝓞 E) E) := φ.symm.toHomeomorph.secondCountableTopology
  haveI : T2Space (AdeleRing (𝓞 E) E) := φ.symm.toHomeomorph.isEmbedding.t2Space
  have h1 : distribHaarChar (AdeleRing (𝓞 E) E) (GlobalTheory.IdeleLogHom.toE F E t) = distribHaarChar (AE F E) t :=
    GlobalTheory.JR.ModuleNorm.distribHaarChar_transport φ t (GlobalTheory.IdeleLogHom.toE F E t) (fun x => by
      change adeleTensorAlgEquivLeft F E ((t : AE F E) * x) = _
      rw [map_mul]
      rfl)
  apply NNReal.eq
  rw [← h1, GlobalTheory.ModuAdele.distribHaarChar_adeleRing, GlobalTheory.IdeleLogHom.absE_eq_ideleModule]

theorem map_mul_eq_absE_inv_smul : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
  ∀ [MeasurableSpace (AE F E)] [BorelSpace (AE F E)] (ν : Measure (AE F E)), ν.IsAddHaarMeasure →
  ∀ t : (AE F E)ˣ, ν.map (fun x => (t : AE F E) * x) = ((absE F E t : ENNReal))⁻¹ • ν := by
  intro F E _ _ _ _ _ σ _ _ _ ν _ t
  haveI : IsTopologicalRing (AE F E) := IsModuleTopology.isTopologicalRing (AF F) _
  haveI := GlobalTheory.AdelicUnitaryTop.secondCountable_adele F
  haveI := GlobalTheory.AdelicUnitaryTop.t2Space_adeleRing_numberField F
  haveI : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E
  obtain ⟨e⟩ := GlobalTheory.AdelicUnitaryTop.nonempty_homeomorph (F := F) (E := E) (AF F)
  haveI : LocallyCompactSpace (AE F E) := e.isClosedEmbedding.locallyCompactSpace
  haveI : SecondCountableTopology (AE F E) := e.secondCountableTopology
  haveI : T2Space (AE F E) := e.isEmbedding.t2Space
  have h := map_smul_eq_inv_smul ν t
  rw [distribHaarChar_eq_absE] at h
  exact h

end GlobalTheory.AdeleUnitModule
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasGlobalOneFormFrameOfSmoothGroupSchemeStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hasGlobalOneFormFrame_of_smooth_groupScheme : ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A], Smooth A.hom → HasFrame (OAff A.hom) := by
  first | exact @GlobalTheory.AbCoh.hasFrame_of_smooth_grpObj | exact GlobalTheory.AbCoh.hasFrame_of_smooth_grpObj | (intros; apply GlobalTheory.AbCoh.hasFrame_of_smooth_grpObj <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeightInvariantUnderStabilizer
section
open scoped TensorProduct NNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.EisRes
open GlobalTheory.Doubling (absE)

namespace GlobalTheory.EisCT

theorem exists_col0_ne_zero_of_witt {F E : Type} [Field F] [Field E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ}
    {J : Matrix (Fin n) (Fin n) E} {r : ℕ} {X Y : Matrix (Fin n) (Fin (r + 1)) E} (hW : IsWittFrame σ J X Y) :
    ∃ i, X i 0 ≠ 0 := by
  by_contra hc
  push_neg at hc
  have h1 := congrArg (fun M => M 0 0) hW.xy
  simp only [Matrix.one_apply_eq] at h1
  rw [Matrix.mul_apply] at h1
  simp [Matrix.mul_apply, Formalism.UG.cT, hc] at h1

theorem iwaHt_mul_rat_stabL : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ)
    (J : Matrix (Fin n) (Fin n) E) (r : ℕ) (X Y : Matrix (Fin n) (Fin (r + 1)) E) (L : Submodule (𝓞 E) (Fin n → E))
    (a : GL (Fin n) (AF F ⊗[F] E)) (h : GAd σ J → ℝ), HidaSetting σ J X Y L a h →
    ∀ p ∈ ratPts σ J, GlobalTheory.EisCT.StabL σ J (col0 X) p → ∀ v, h (p * v) = h v := by
  intro F E _ _ _ _ _ σ n J r X Y L a h hS p hp hst v
  obtain ⟨-, -, -, -, hW, -, hI1, hI2⟩ := hS
  obtain ⟨lp, hlp⟩ := hst
  have key : absE F E lp = 1 := by
    rw [← range_ratEmb] at hp
    obtain ⟨γ, rfl⟩ := hp
    obtain ⟨i, hi⟩ := exists_col0_ne_zero_of_witt hW
    have hmat : (matHom _ σ J (ratEmb σ J γ)).1 = (γ.1.1 : Matrix (Fin n) (Fin n) E).map (inclR (F := F) (AF F)) := by
      ext s t; rfl
    rw [hmat] at hlp
    have hent := congrArg (fun M => M i 0) hlp
    simp only [adMat] at hent
    rw [← RingHom.map_matrix_mul] at hent
    simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul] at hent
    have hx : col0 X i 0 = X i 0 := rfl
    rw [hx] at hent
    set e : E := ((γ.1.1 : Matrix (Fin n) (Fin n) E) * col0 X) i 0 / X i 0 with he_def
    have he : inclR (F := F) (AF F) e * inclR (F := F) (AF F) (X i 0) =
        inclR (F := F) (AF F) (((γ.1.1 : Matrix (Fin n) (Fin n) E) * col0 X) i 0) := by
      rw [← map_mul, he_def, div_mul_cancel₀ _ hi]
    have hu : IsUnit (inclR (F := F) (AF F) (X i 0)) := (isUnit_iff_ne_zero.2 hi).map _
    have hl : lp.1 = inclR (F := F) (AF F) e := by
      rw [← he] at hent
      exact (hu.mul_left_inj.1 hent).symm
    by_cases he0 : e = 0
    · rw [he0, map_zero] at hl
      have : Subsingleton (AF F ⊗[F] E) := by
        have h01 := lp.mul_inv
        rw [hl, zero_mul] at h01
        exact subsingleton_of_zero_eq_one h01
      rw [Subsingleton.elim lp 1, map_one]
    · have := GlobalTheory.Doubling.absE_inclR (F := F) (E := E) (Units.mk0 e he0)
      rwa [show (Units.map (inclR (F := F) (AF F)).toMonoidHom (Units.mk0 e he0)) = lp from
        Units.ext (by simp [hl])] at this
  obtain ⟨q, lq, hq, k, hk, rfl⟩ := hI1 v
  have e1 : h (q * k) = absE F E lq := hI2 q lq hq k hk
  have hpq : (matHom _ σ J (p * q)).1 * adMat F (col0 X) = (lp * lq).1 • adMat F (col0 X) := by
    rw [map_mul, Units.val_mul, Matrix.mul_assoc, hq, Matrix.mul_smul, hlp, smul_smul, Units.val_mul, mul_comm]
  have e2 : h (p * q * k) = absE F E (lp * lq) := hI2 (p * q) (lp * lq) hpq k hk
  rw [← mul_assoc, e2, e1, map_mul, key, one_mul]

end GlobalTheory.EisCT
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeisenbergDerivArchimedeanWeilRepIntertwine
section
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped TensorProduct NNReal Matrix
open scoped Classical
open GlobalTheory.ArchDecay

noncomputable section

namespace GlobalTheory.ArchDecay.HeisWeil

variable {R : Type} [CommRing R] [Invertible (2 : R)] {V : Type} [AddCommGroup V] [Module R V] {Bf : V → V → R}
  {κ : Type} [Fintype κ]

theorem rho_add (dc : Darboux Bf κ) (ψ : AddChar R ℂ) (w : V) (f g : (κ → R) → ℂ) :
    dc.rho ψ w (f + g) = dc.rho ψ w f + dc.rho ψ w g := by
  funext x
  simp [Darboux.rho, schr, mul_add]

theorem rho_smul (dc : Darboux Bf κ) (ψ : AddChar R ℂ) (w : V) (c : ℂ) (f : (κ → R) → ℂ) :
    dc.rho ψ w (c • f) = c • dc.rho ψ w f := by
  funext x
  simp only [Darboux.rho, schr, Pi.smul_apply, smul_eq_mul]
  ring

theorem rho_zero (dc : Darboux Bf κ) (ψ : AddChar R ℂ) (w : V) : dc.rho ψ w (0 : (κ → R) → ℂ) = 0 := by
  funext x
  simp [Darboux.rho, schr]

end GlobalTheory.ArchDecay.HeisWeil

open GlobalTheory.ArchDecay.HeisWeil

theorem GlobalTheory.ArchDecay.HeisWeil.exists_hasDerivAt_adm {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] {σ : E →ₐ[F] E} {α β κ : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] [Fintype κ]
    (ψ : AddChar (AF F) ℂ) {JA : Matrix α α (AE F E)} {JB : Matrix β β (AE F E)}
    (dc : Darboux (symp (R := AF F) (cA σ) (-1) JA JB) κ) (hψ : IsStd ψ) (u : Matrix α β (AE F E))
    (hu : At (evI F) u) (f : (κ → AF F) → ℂ) (hf : f ∈ schA F κ) :
    ∃ Df : (κ → AF F) → ℂ, ∀ l ∈ (adeleClass F).adm κ,
      HasDerivAt (fun t : ℝ => l (dc.rho ψ (realAd F t • u) f)) (l Df) 0 := by
  obtain ⟨D, hD⟩ := GlobalTheory.T.archHeisenbergDerivatives_exist F E σ α β κ ψ JA JB dc hψ
  induction hf using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨f₀, g, hg, rfl⟩ := hx
    exact ⟨pureA F (D u f₀) g, fun l hl => (hD u hu f₀).1 g hg l hl⟩
  | zero =>
    refine ⟨0, fun l _ => ?_⟩
    simp only [rho_zero, map_zero]
    exact hasDerivAt_const _ _
  | add x y _ _ hx hy =>
    obtain ⟨Dx, hDx⟩ := hx
    obtain ⟨Dy, hDy⟩ := hy
    refine ⟨Dx + Dy, fun l hl => ?_⟩
    simp only [rho_add, map_add]
    exact (hDx l hl).add (hDy l hl)
  | smul c x _ hx =>
    obtain ⟨Dx, hDx⟩ := hx
    refine ⟨c • Dx, fun l hl => ?_⟩
    simp only [rho_smul, map_smul, smul_eq_mul]
    exact (hDx l hl).const_mul c

theorem GlobalTheory.ArchDecay.HeisWeil.heisD_weil : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' → ∀ (p : UA σ X.J × UA σ W.J) (u : Matrix (Fin n) (Fin d) (AE F E)), At (evI F) u → ∀ f ∈ schA F (Fin n × Fin d), heisD M B.ψ u (om p f) = om p (heisD M B.ψ (actAB (cA σ) p⁻¹ u) f) := by
  intro F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hP p u hu f hf
  have hψ : IsStd B.ψ := hP.base.std
  have hS := IsUWeilPair.isUSplitting hP.weil
  set u' := actAB (cA σ) p⁻¹ u with hu'def
  have hu' : At (evI F) u' := fun a ha => by
    rw [hu'def, actAB, ← Matrix.smul_mul, ← Matrix.mul_smul, hu a ha, Matrix.mul_zero, Matrix.zero_mul]
  have hact : ∀ t : ℝ, actAB (cA σ) p (realAd F t • u') = realAd F t • u := fun t => by
    simp only [hu'def, actAB]
    rw [Matrix.mul_smul, Matrix.smul_mul]
    congr 1
    simp only [Prod.fst_inv, Prod.snd_inv, Subgroup.coe_inv, Matrix.mul_assoc]
    rw [← Matrix.transpose_mul, Units.mul_inv, Matrix.transpose_one, Matrix.mul_one, ← Matrix.mul_assoc,
      Units.mul_inv, Matrix.one_mul]
  obtain ⟨Df, hDf⟩ := exists_hasDerivAt_adm B.ψ M.co hψ u' hu' f hf
  have hDfx : Df = heisD M B.ψ u' f := by
    funext x
    exact ((hDf _ (GlobalTheory.RealLift.eval_mem_adm x)).deriv).symm
  funext x
  have hl := hS.adm p _ (GlobalTheory.RealLift.eval_mem_adm x)
  have h1 := hDf _ hl
  have e : (fun t : ℝ => M.heisLine B.ψ u t (om p f) x) =
      fun t : ℝ => ((LinearMap.proj x : ((Fin n × Fin d → AF F) → ℂ) →ₗ[ℂ] ℂ) ∘ₗ om p)
        (M.co.rho B.ψ (realAd F t • u') f) := by
    funext t
    rw [LinearMap.comp_apply, hS.impl p _ f hf, hact t]
    rfl
  show deriv (fun t : ℝ => M.heisLine B.ψ u t (om p f) x) 0 = _
  rw [e, h1.deriv, ← hDfx]
  rfl
end
end

