import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ResBound
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0414
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0411
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0193
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0132
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0135
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0413
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0005
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0015
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0011
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0406
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0417
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsRhoPtOfSplitting
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0154
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0412
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0014
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemSpanRingCornerIdealModuleIff
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsMapEntriesHaarUnitriangularEqSmulPi
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdelicUnitriangularMulMemUnipotentTimesIntegral

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsFrobeniusGenDegreeHomToZl
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc

namespace GlobalTheory.UnramGen

theorem exists_normalised {l : ℕ} [Fact l.Prime] {G : Type} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] (I : Subgroup G) (F : G)
    (hF : (Subgroup.zpowers F ⊔ I).topologicalClosure = ⊤) (z : G → ℤ_[l]) (hc : Continuous z)
    (hadd : ∀ σ τ, z (σ * τ) = z σ + z τ) (hI : ∀ σ ∈ I, z σ = 0) (h0 : ∃ σ, z σ ≠ 0) :
    ∃ ν : G →* Multiplicative ℤ_[l], Continuous ν ∧ (∀ σ ∈ I, ν σ = 1) ∧
      ν F = Multiplicative.ofAdd 1 := by
  have h1 : z 1 = 0 := by simpa using hadd 1 1
  have hinv : ∀ σ, z σ⁻¹ = - z σ := by
    intro σ
    have h := hadd σ σ⁻¹
    rw [mul_inv_cancel, h1] at h
    linear_combination -h

  let H : Subgroup G :=
    { carrier := {σ | ‖z σ‖ ≤ ‖z F‖}
      mul_mem' := fun {a b} ha hb => by
        show ‖z (a * b)‖ ≤ ‖z F‖
        rw [hadd]
        exact (PadicInt.nonarchimedean _ _).trans (max_le ha hb)
      one_mem' := by
        show ‖z 1‖ ≤ ‖z F‖
        rw [h1, norm_zero]
        exact norm_nonneg _
      inv_mem' := fun {a} ha => by
        show ‖z a⁻¹‖ ≤ ‖z F‖
        rw [hinv, norm_neg]
        exact ha }
  have hHc : IsClosed (H : Set G) := isClosed_le (continuous_norm.comp hc) continuous_const
  have hsup : Subgroup.zpowers F ⊔ I ≤ H := by
    refine sup_le ((Subgroup.zpowers_le (H := H)).2 (show ‖z F‖ ≤ ‖z F‖ from le_rfl)) ?_
    intro σ hσ
    show ‖z σ‖ ≤ ‖z F‖
    rw [hI σ hσ, norm_zero]
    exact norm_nonneg _
  have hbound : ∀ σ, ‖z σ‖ ≤ ‖z F‖ := by
    intro σ
    have hle := Subgroup.topologicalClosure_minimal _ hsup hHc
    rw [hF] at hle
    exact hle (Subgroup.mem_top σ)
  have hF0 : z F ≠ 0 := by
    intro h
    obtain ⟨σ, hσ⟩ := h0
    apply hσ
    have := hbound σ
    rw [h, norm_zero] at this
    exact norm_le_zero_iff.mp this
  have hF0' : (z F : ℚ_[l]) ≠ 0 := fun h => hF0 (Subtype.ext (h.trans PadicInt.coe_zero.symm))

  let w : G → ℤ_[l] := fun σ => ⟨(z σ : ℚ_[l]) / (z F : ℚ_[l]), by
    rw [norm_div, PadicInt.padic_norm_e_of_padicInt, PadicInt.padic_norm_e_of_padicInt,
      div_le_one (norm_pos_iff.mpr hF0)]
    exact hbound σ⟩
  have hw : ∀ σ, (w σ : ℚ_[l]) = (z σ : ℚ_[l]) / (z F : ℚ_[l]) := fun _ => rfl
  have hwadd : ∀ σ τ, w (σ * τ) = w σ + w τ := by
    intro σ τ
    apply Subtype.ext
    show (w (σ * τ) : ℚ_[l]) = ((w σ + w τ : ℤ_[l]) : ℚ_[l])
    rw [PadicInt.coe_add, hw, hw, hw, hadd, PadicInt.coe_add, add_div]
  have hwc : Continuous w :=
    Continuous.subtype_mk ((continuous_subtype_val.comp hc).div_const _) _
  let ν : G →* Multiplicative ℤ_[l] :=
    MonoidHom.mk' (fun σ => Multiplicative.ofAdd (w σ)) (fun σ τ => by
      rw [hwadd]
      rfl)
  refine ⟨ν, continuous_ofAdd.comp hwc, ?_, ?_⟩
  · intro σ hσ
    show Multiplicative.ofAdd (w σ) = 1
    rw [ofAdd_eq_one]
    apply Subtype.ext
    show (w σ : ℚ_[l]) = ((0 : ℤ_[l]) : ℚ_[l])
    rw [hw, hI σ hσ]
    simp
  · show Multiplicative.ofAdd (w F) = Multiplicative.ofAdd 1
    congr 1
    apply Subtype.ext
    show (w F : ℚ_[l]) = ((1 : ℤ_[l]) : ℚ_[l])
    rw [hw, div_self hF0', PadicInt.coe_one]

private theorem norm_prime_lt_one_algClosure {l : ℕ} [Fact l.Prime] : ‖(l : Om l)‖ < 1 := by
  have h : (l : Om l) = algebraMap ℚ_[l] (Om l) (l : ℚ_[l]) := by simp
  rw [h, PadicAlgCl.norm_extends]
  exact Padic.norm_p_lt_one

private theorem norm_pow_sub_pow_le_norm_sub {E : Type} [NormedField E] [IsUltrametricDist E] {x y : E}
    (hx : ‖x‖ ≤ 1) (hy : ‖y‖ ≤ 1) (i : ℕ) : ‖y ^ i - x ^ i‖ ≤ ‖y - x‖ := by
  rw [← geom_sum₂_mul, norm_mul]
  refine mul_le_of_le_one_left (norm_nonneg _) ?_
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one ?_
  intro j _
  rw [norm_mul, norm_pow, norm_pow]
  exact mul_le_one₀ (pow_le_one₀ (norm_nonneg _) hy) (by positivity) (pow_le_one₀ (norm_nonneg _) hx)

private theorem fixes_root_of_unity_of_inertia_like {l : ℕ} [Fact l.Prime] (σ : GQ l)
    (hσ : ∀ x : Om l, ‖x‖ ≤ 1 → ‖σ x - x‖ < 1) (n : ℕ) (hn : 0 < n) (x : Om l)
    (hx : x ^ l ^ n = x) : σ x = x := by
  have hl1 : 1 < l := (Fact.out : l.Prime).one_lt
  have hq : 1 < l ^ n := Nat.one_lt_pow hn.ne' hl1
  by_cases hx0 : x = 0
  · rw [hx0, map_zero]
  have hxq : x ^ (l ^ n - 1) = 1 := by
    have h : x ^ (l ^ n - 1) * x = 1 * x := by
      rw [← pow_succ, Nat.sub_add_cancel hq.le, one_mul, hx]
    exact mul_right_cancel₀ hx0 h
  have hnx : ‖x‖ = 1 := by
    have h := congrArg norm hxq
    rw [norm_pow, norm_one] at h
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg x) (by omega)).mp h
  have hy : σ x ^ l ^ n = σ x := by rw [← map_pow, hx]
  have hε : ‖σ x - x‖ < 1 := hσ x hnx.le
  have hny : ‖σ x‖ ≤ 1 := by
    have h := IsUltrametricDist.norm_add_le_max (σ x - x) x
    rw [sub_add_cancel, hnx] at h
    exact h.trans (max_le hε.le le_rfl)
  by_contra hne
  have hne' : σ x - x ≠ 0 := sub_ne_zero.mpr hne
  set S := ∑ i ∈ Finset.range (l ^ n), σ x ^ i * x ^ (l ^ n - 1 - i) with hSdef

  have hS : S = 1 := by
    have h := geom_sum₂_mul (σ x) x (l ^ n)
    rw [hy, hx] at h
    exact mul_right_cancel₀ hne' (h.trans (one_mul _).symm)

  have hterm : ∀ i ∈ Finset.range (l ^ n),
      ‖σ x ^ i * x ^ (l ^ n - 1 - i) - 1‖ ≤ ‖σ x - x‖ := by
    intro i hi
    have hi' : i ≤ l ^ n - 1 := by
      have := Finset.mem_range.mp hi
      omega
    have h1 : (1 : Om l) = x ^ i * x ^ (l ^ n - 1 - i) := by
      rw [← pow_add, Nat.add_sub_cancel' hi', hxq]
    rw [h1, ← sub_mul, norm_mul, norm_pow, hnx, one_pow, mul_one]
    exact norm_pow_sub_pow_le_norm_sub hnx.le hny i
  have hsum : ‖S - ((l ^ n : ℕ) : Om l)‖ ≤ ‖σ x - x‖ := by
    have h : ((l ^ n : ℕ) : Om l) = ∑ i ∈ Finset.range (l ^ n), (1 : Om l) := by simp
    rw [h, hSdef, ← Finset.sum_sub_distrib]
    exact IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (norm_nonneg _) hterm
  have hlq : ‖((l ^ n : ℕ) : Om l)‖ < 1 := by
    rw [Nat.cast_pow, norm_pow]
    exact pow_lt_one₀ (norm_nonneg _) norm_prime_lt_one_algClosure hn.ne'
  have hq1 : ‖((l ^ n : ℕ) : Om l) - 1‖ = 1 := by
    rw [sub_eq_add_neg, IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm
      (by rw [norm_neg, norm_one]; exact hlq.ne), norm_neg, norm_one]
    exact max_eq_right hlq.le
  have key : ‖S - 1‖ = 1 := by
    have e : S - 1 = (((l ^ n : ℕ) : Om l) - 1) + (S - ((l ^ n : ℕ) : Om l)) := by ring
    rw [e, IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm
      (by rw [hq1]; exact (hsum.trans_lt hε).ne'), hq1]
    exact max_eq_left (hsum.trans hε.le)
  rw [hS, sub_self, norm_zero] at key
  exact zero_ne_one key

theorem exists_gen_degree : ∀ {l : ℕ} [Fact l.Prime] (K : FinExt l),
    ∃ (F : ↥(GK K)) (ν : ↥(GK K) →* Multiplicative ℤ_[l]), Continuous ν ∧ (∀ σ ∈ IK K, ν σ = 1) ∧
      ν F = Multiplicative.ofAdd 1 ∧
      (Subgroup.closure (insert F (IK K : Set ↥(GK K)))).topologicalClosure = ⊤ := by
  intro l _ K

  obtain ⟨φ, hφ⟩ := (GlobalTheory.Cyc.exists_frobenius_and_exponent_modEq l).1
  obtain ⟨z, hzc, hzadd, hzval⟩ := GlobalTheory.UnramifiedDegree.exists_degree l
    (fun n hn σ => GlobalTheory.InertiaEigenvalues.FrobPow.exists_gal_eq_pow l n hn σ)
    (GlobalTheory.Cyc.exists_frobenius_and_exponent_modEq l).2
  have hz1 : z 1 = 0 := by simpa using hzadd 1 1
  have hzφ : z φ = 1 := by
    have h := hzval φ 1 (fun n hn x hx => by rw [pow_one]; exact hφ n hn x hx)
    simpa using h
  have hzpow : ∀ m : ℕ, z (φ ^ m) = m := by
    intro m
    induction m with
    | zero => simp [hz1]
    | succ m ih =>
      rw [pow_succ, hzadd, ih, hzφ]
      push_cast
      ring

  have hfix : ∀ σ : GQ l, (∀ x : Om l, ‖x‖ ≤ 1 → ‖σ x - x‖ < 1) → z σ = 0 := by
    intro σ hσ
    have h := hzval σ 0 (fun n hn x hx => by
      rw [pow_zero, pow_one]
      exact fixes_root_of_unity_of_inertia_like σ hσ n hn x hx)
    simpa using h

  obtain ⟨N, hN, hmem⟩ : ∃ N : ℕ, 0 < N ∧ φ ^ N ∈ GK K := by
    have : FiniteDimensional ℚ_[l] (K : IntermediateField ℚ_[l] (Om l)) := K.2
    let g : ℕ → ((K : IntermediateField ℚ_[l] (Om l)) →ₐ[ℚ_[l]] Om l) := fun m =>
      ((φ ^ m : GQ l) : Om l →ₐ[ℚ_[l]] Om l).comp (K : IntermediateField ℚ_[l] (Om l)).val
    have claim : ∀ i j, i < j → g i = g j → φ ^ (j - i) ∈ GK K := by
      intro i j hij hg
      show φ ^ (j - i) ∈ (K : IntermediateField ℚ_[l] (Om l)).fixingSubgroup
      rw [IntermediateField.mem_fixingSubgroup_iff]
      intro x hx
      have h1 : (φ ^ i) x = (φ ^ j) x := DFunLike.congr_fun hg ⟨x, hx⟩
      have h2 : φ ^ j = φ ^ i * φ ^ (j - i) := by
        rw [← pow_add, Nat.add_sub_cancel' hij.le]
      rw [h2, AlgEquiv.mul_apply] at h1
      exact ((φ ^ i).injective h1).symm
    obtain ⟨i, j, hij, hg⟩ := Finite.exists_ne_map_eq_of_infinite g
    rcases Nat.lt_or_gt_of_ne hij with h | h
    · exact ⟨j - i, by omega, claim i j h hg⟩
    · exact ⟨i - j, by omega, claim j i h hg.symm⟩

  let z' : ↥(GK K) → ℤ_[l] := fun σ => z σ
  have hz'c : Continuous z' := hzc.comp continuous_subtype_val
  have hz'add : ∀ σ τ, z' (σ * τ) = z' σ + z' τ := fun σ τ => hzadd σ τ
  let f : ↥(GK K) →* Multiplicative ℤ_[l] :=
    MonoidHom.mk' (fun σ => Multiplicative.ofAdd (z' σ)) (fun σ τ => by rw [hz'add]; rfl)
  have hIK : IK K ≤ f.ker := by
    unfold IK
    rw [Subgroup.closure_le]
    intro σ hσ
    rw [SetLike.mem_coe, MonoidHom.mem_ker]
    show Multiplicative.ofAdd (z σ) = 1
    rw [hfix σ hσ, ofAdd_zero]
  have hz'I : ∀ σ ∈ IK K, z' σ = 0 := by
    intro σ hσ
    have h := hIK hσ
    rw [MonoidHom.mem_ker] at h
    change Multiplicative.ofAdd (z' σ) = 1 at h
    exact ofAdd_eq_one.mp h
  have h0 : ∃ σ, z' σ ≠ 0 := ⟨⟨φ ^ N, hmem⟩, by
    show z (φ ^ N) ≠ 0
    rw [hzpow]
    exact Nat.cast_ne_zero.mpr hN.ne'⟩
  obtain ⟨F, hF⟩ := GlobalTheory.exists_topologicalClosure_zpowers_sup_inertia l K
  obtain ⟨ν, hνc, hνI, hνF⟩ := exists_normalised (IK K) F hF z' hz'c hz'add hz'I h0
  refine ⟨F, ν, hνc, hνI, hνF, ?_⟩
  rw [eq_top_iff, ← hF]
  refine Subgroup.topologicalClosure_mono (sup_le ?_ ?_)
  · exact Subgroup.zpowers_le.mpr (Subgroup.subset_closure (Set.mem_insert F _))
  · intro σ hσ
    exact Subgroup.subset_closure (Set.mem_insert_of_mem F hσ)

end GlobalTheory.UnramGen
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsGaussNormAinfDiscStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_gaussNorm_ainf_disc : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (ρ : ℝ≥0), 0 < ρ → ρ < 1 → ∃ N : Ainf l → ℝ, (∀ x y, N (x * y) = N x * N y) ∧ (∀ x y, N (x + y) ≤ max (N x) (N y)) ∧ N (l : Ainf l) = (l : ℝ)⁻¹ ∧ (∀ x, N x ≤ ‖toDisc l (bk.ev X) ρ x‖) ∧ ∀ x, (ρ : ℝ) * ‖toDisc l (bk.ev X) ρ x‖ ≤ N x := by
  first | exact @GlobalTheory.DiscGauss.exists_gauss_disc | exact GlobalTheory.DiscGauss.exists_gauss_disc | (intros; apply GlobalTheory.DiscGauss.exists_gauss_disc <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsHodgeBasisDeRhamLattice
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

noncomputable section

namespace GlobalTheory.HodgeEx

theorem exists_hodge : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (P : LocPrime l) (AI : LocAinf l P) (T : LocTied l P AI) (C : Core l), Fits T C → ∀ (ξ : Ainf l), Ideal.span {ξ} = RingHom.ker (Per.θ l) → ∀ (d : ℕ) (ρ : ↥(GK K) →* GL (Fin d) ℤ_[l]), Formalism.MainNotions.N.IsDR (P.PD K) (qRep ρ) → ∃ H : Hodge C ξ (fun g => (ρ g).val.map (zOm l)) K, ∀ N : ℕ, (DdR (P.PD K) (qRep ρ) ≤ FilV (P.PD K) (LL := ℚ_[l]) (V := Fin d → ℚ_[l]) (-(N : ℤ)) ∧ DdR (P.PD K) (qRep ρ) ⊓ FilV (P.PD K) (LL := ℚ_[l]) (V := Fin d → ℚ_[l]) ((N : ℤ) + 1) = ⊥) → ∀ i, |(H.p i : ℤ) - H.q| ≤ N := by
  intro l _ K P AI T C hC ξ hξ d ρ hDR
  set M : ↥(GK K) → Matrix (Fin d) (Fin d) P.R.BdR :=
    fun g => (ρ g).val.map (fun z : ℤ_[l] => algebraMap ℚ_[l] P.R.BdR (z : ℚ_[l])) with hM
  have hKact : ∀ (g : ↥(GK K)) (k : ↥K.1) (v : P.R.BdR),
      P.actQdR (g : GQ l) (algebraMap ↥K.1 P.R.BdR k * v) = algebraMap ↥K.1 P.R.BdR k * P.actQdR (g : GQ l) v := by
    intro g k v
    rw [← P.PD_actdR, ← P.PD_actdR, map_mul, AlgEquiv.commutes]
  let Iv : Submodule ↥K.1 (Fin d → P.R.BdR) :=
    { carrier := {c | ∀ g : ↥(GK K), M g *ᵥ (fun i => P.actQdR (g : GQ l) (c i)) = c}
      add_mem' := by
        intro u v hu hv g
        simp only [Set.mem_setOf_eq] at hu hv ⊢
        have : (fun i => P.actQdR (g : GQ l) ((u + v) i)) =
            (fun i => P.actQdR (g : GQ l) (u i)) + (fun i => P.actQdR (g : GQ l) (v i)) := by
          funext i; simp
        rw [this, Matrix.mulVec_add, hu g, hv g]
      zero_mem' := by
        intro g
        simp only [Set.mem_setOf_eq, Pi.zero_apply, map_zero]
        exact Matrix.mulVec_zero _
      smul_mem' := by
        intro k u hu g
        simp only [Set.mem_setOf_eq] at hu ⊢
        have : (fun i => P.actQdR (g : GQ l) ((k • u) i)) = k • (fun i => P.actQdR (g : GQ l) (u i)) := by
          funext i; simp only [Pi.smul_apply, Algebra.smul_def, hKact]
        rw [this, Matrix.mulVec_smul, hu g] }
  have hmemIv : ∀ c, c ∈ Iv ↔ ∀ g : ↥(GK K), M g *ᵥ (fun i => P.actQdR (g : GQ l) (c i)) = c := fun c => Iff.rfl
  obtain ⟨x, hxli, hxinv, hxspan⟩ := GlobalTheory.T.exists_invariant_basis_of_isDeRham_lattice l P AI T K d ρ hDR
  set D : Submodule ↥K.1 (Fin d → P.R.BdR) := Submodule.span ↥K.1 (Set.range x) with hD
  have hDIv : D ≤ Iv := Submodule.span_le.2 (by rintro _ ⟨j, rfl⟩; exact (hmemIv _).2 (hxinv j))
  have hIvD : ∀ c, c ∈ Iv → c ∈ D := fun c hc => hxspan c hc
  haveI : FiniteDimensional ↥K.1 D := FiniteDimensional.span_of_finite ↥K.1 (Set.finite_range x)
  have hfr : Module.finrank ↥K.1 D = d := by
    rw [hD, finrank_span_eq_card hxli, Fintype.card_fin]
  let F : ℤ → Submodule ↥K.1 (Fin d → P.R.BdR) := fun a => Submodule.pi Set.univ (fun _ => (P.PD K).Fil a)
  have hmemF : ∀ a v, v ∈ F a ↔ ∀ i, v i ∈ (P.PD K).Fil a := fun a v => by
    simp [F, Submodule.mem_pi]
  have hFil : Antitone (P.PD K).Fil := antitone_int_of_succ_le (P.PD K).Fil_anti
  have hF : Antitone F := fun a b hab v hv => (hmemF _ _).2 fun i => hFil hab ((hmemF _ _).1 hv i)
  have hex : ∀ v ∈ D, ∃ a, v ∈ F a := by
    intro v _
    choose a ha using fun i => (P.PD K).Fil_exh (v i)
    refine ⟨-∑ i, |a i|, (hmemF _ _).2 fun i => hFil ?_ (ha i)⟩
    have h1 : |a i| ≤ ∑ j, |a j| := Finset.single_le_sum (f := fun j => |a j|) (fun j _ => abs_nonneg _) (Finset.mem_univ i)
    have h2 := neg_abs_le (a i)
    linarith
  have hsep : ∀ v ∈ D, (∀ a, v ∈ F a) → v = 0 := fun v _ hv =>
    funext fun i => (P.PD K).Fil_sep (v i) fun a => (hmemF a v).1 (hv a) i
  obtain ⟨b0, h0, hbF0, hbrep0⟩ := GlobalTheory.T.exists_filtration_adapted_basis_of_subspace D F hF hex hsep
  set e := finCongr hfr
  set b := b0.reindex e with hb
  set h : Fin d → ℤ := fun j => h0 (e.symm j) with hh
  have hbF : ∀ j, (b j : Fin d → P.R.BdR) ∈ F (h j) ∧ (b j : Fin d → P.R.BdR) ∉ F (h j + 1) := fun j => by
    rw [hb, Module.Basis.reindex_apply]; exact hbF0 _
  have hbrep : ∀ (a : ℤ) (v : D), (v : Fin d → P.R.BdR) ∈ F a → ∀ j, b.repr v j ≠ 0 → a ≤ h j := by
    intro a v hv j hj
    rw [hb, Module.Basis.repr_reindex_apply] at hj
    exact hbrep0 a v hv _ hj
  have hbinv : ∀ j (g : ↥(GK K)), M g *ᵥ (fun i => P.actQdR (g : GQ l) ((b j : Fin d → P.R.BdR) i)) = (b j : Fin d → P.R.BdR) :=
    fun j => (hmemIv _).1 (hDIv (b j).2)
  have hspan : ∀ y : Fin d → P.R.BdR, (∀ i, y i ∈ (P.PD K).Fil 0) →
      ∃ c : Fin d → P.R.BdR, (∀ j, c j ∈ (P.PD K).Fil (-h j)) ∧ y = ∑ j, c j • (b j : Fin d → P.R.BdR) := by
    intro y hy
    obtain ⟨m, k, bb, z, hz, rfl⟩ := GlobalTheory.T.deRham_filtered_comparison_coordinates l P AI T K d ρ hDR 0 y hy
    have hzD : ∀ r, z r ∈ D := fun r => hIvD _ ((hmemIv _).2 (hz r).1)
    let cf : Fin m → Fin d → ↥K.1 := fun r j => b.repr ⟨z r, hzD r⟩ j
    refine ⟨fun j => ∑ r, cf r j • bb r, fun j => ?_, ?_⟩
    · refine Submodule.sum_mem _ fun r _ => ?_
      by_cases hc : cf r j = 0
      · rw [hc, zero_smul]; exact zero_mem _
      · have hkr := hbrep (k r) ⟨z r, hzD r⟩ ((hmemF _ _).2 (hz r).2.1) j hc
        refine Submodule.smul_mem _ _ (hFil ?_ (hz r).2.2)
        linarith
    · have hexp : ∀ r, z r = ∑ j, cf r j • (b j : Fin d → P.R.BdR) := fun r => by
        have := congrArg Subtype.val (b.sum_repr ⟨z r, hzD r⟩)
        rw [Submodule.coe_sum] at this
        simp only [Submodule.coe_smul] at this
        exact this.symm
      funext i
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      conv_lhs => enter [2, r]; rw [hexp r]
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, Finset.sum_mul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun r _ => ?_
      simp only [Algebra.smul_def]
      ring
  obtain ⟨H, hH⟩ := GlobalTheory.T.hodge_structure_of_adapted_invariant_family l K P AI T C hC ξ hξ d ρ (fun j => (b j : Fin d → P.R.BdR)) h hbinv
    (fun j i => (hmemF _ _).1 (hbF j).1 i) hspan
  refine ⟨H, fun N ⟨h1, h2⟩ i => ?_⟩
  rw [hH i]
  have hne : (b i : Fin d → P.R.BdR) ≠ 0 := fun h0' => b.ne_zero i (Subtype.ext h0')
  obtain ⟨hlo, hhi⟩ := GlobalTheory.T.deRham_filtration_bounds_invariant_coordinates l P K d ρ N h1 h2 _ (hbinv i) hne
  rw [abs_le]
  constructor
  · by_contra hlt
    push_neg at hlt
    exact (hbF i).2 (hF (show h i + 1 ≤ -(N : ℤ) by omega) ((hmemF _ _).2 hlo))
  · by_contra hlt
    push_neg at hlt
    exact hhi ((hmemF _ _).1 (hF (show (N : ℤ) + 1 ≤ h i by omega) (hbF i).1))

end GlobalTheory.HodgeEx
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsInertiaCycZEq
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.PtCore

namespace GlobalTheory.Cyc

theorem isCyc_map_cycZ (l : ℕ) [Fact l.Prime] :
    IsCyc ((Units.map (PadicInt.Coe.ringHom (p := l)).toMonoidHom).comp
      (cycZ (F := ℚ_[l]) (Ω := Om l) l)) := by
  intro g m ζ hζ
  haveI : ∀ i : ℕ, NeZero ((l ^ i : ℕ) : Om l) := fun i =>
    ⟨by exact_mod_cast pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
  refine ⟨_, ?_, cyclotomicCharacter.spec l (n := m)
    (MulSemiringAction.toRingAut (GQ l) (Om l) g) ζ hζ⟩
  set z : ℤ_[l] := ((cycZ (F := ℚ_[l]) (Ω := Om l) l g : ℤ_[l]ˣ) : ℤ_[l]) with hz
  change ‖(z : ℚ_[l]) - (((PadicInt.toZModPow m z).val : ℕ) : ℚ_[l])‖ ≤ _
  have h : z - (((PadicInt.toZModPow m z).val : ℕ) : ℤ_[l]) ∈
      Ideal.span {(l : ℤ_[l]) ^ m} := by
    haveI : NeZero (l ^ m) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
    rw [← PadicInt.ker_toZModPow, RingHom.mem_ker, map_sub, map_natCast, ZMod.natCast_zmod_val,
      sub_self]
  have := (PadicInt.norm_le_pow_iff_mem_span_pow _ m).2 h
  rwa [PadicInt.norm_def, PadicInt.coe_sub, PadicInt.coe_natCast] at this

theorem exists_inertia_cycZ_eq : ∀ (l : ℕ) [Fact l.Prime] (u : ℤ_[l]ˣ), ∃ σ : GQ l, (∀ x ∈ MaximalUnramifiedExtension l, σ x = x) ∧ cycZ (F := ℚ_[l]) (Ω := Om l) l σ = u := by
  intro l _ u
  have hχ := isCyc_map_cycZ l
  set χ := (Units.map (PadicInt.Coe.ringHom (p := l)).toMonoidHom).comp
      (cycZ (F := ℚ_[l]) (Ω := Om l) l) with hχdef
  have hu1 : ‖((u : ℤ_[l]) : ℚ_[l])‖ = 1 := PadicInt.norm_units u
  have hs : IsClosed {g : GQ l | (χ g : ℚ_[l]) = ((u : ℤ_[l]) : ℚ_[l])} :=
    isClosed_eq hχ.continuous continuous_const
  have key := hs.isCompact.inter_iInter_nonempty
    (fun x : MaximalUnramifiedExtension l => ((IntermediateField.adjoin ℚ_[l] {(x : Om l)}).fixingSubgroup : Set (GQ l)))
    (fun x => by
      haveI := IntermediateField.adjoin.finiteDimensional
        (Algebra.IsIntegral.isIntegral (R := ℚ_[l]) (x : Om l))
      exact IntermediateField.fixingSubgroup_isClosed _)
    (fun t => by
      let S : Set (Om l) := (fun x : MaximalUnramifiedExtension l => (x : Om l)) '' (t : Set (MaximalUnramifiedExtension l))
      haveI : Finite S := (t.finite_toSet.image _).to_subtype
      let K : FinExt l := ⟨IntermediateField.adjoin ℚ_[l] S,
        IntermediateField.finiteDimensional_adjoin
          (fun x _ => Algebra.IsIntegral.isIntegral x)⟩
      obtain ⟨g, hg, hgu⟩ := exists_chi_eq K χ hχ _ hu1
      refine ⟨g, hgu, Set.mem_iInter₂.2 fun x hx => ?_⟩
      refine (mem_fixingSubgroup_adjoin_iff _ g).2 ?_
      rintro y rfl
      exact (IntermediateField.mem_fixingSubgroup_iff _ _).1 hg _
        ⟨IntermediateField.subset_adjoin _ _ ⟨x, hx, rfl⟩, x.2⟩)
  obtain ⟨g, hgu, hg⟩ := key
  refine ⟨g, fun x hx => ?_, Units.ext (Subtype.ext hgu)⟩
  exact (mem_fixingSubgroup_adjoin_iff _ g).1 (Set.mem_iInter.1 hg ⟨x, hx⟩) x rfl

end GlobalTheory.Cyc
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsInjectiveMapIntegersClToWittQuotientStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_injective_map_integers_Cl_to_wittQuotient : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (O : Type) [CommRing O] [IsDomain O] [ValuationRing O] [CharP O l] [PerfectRing O l] (ψ : OCb l →+* O), ψ bk.flat ≠ 0 → ¬ IsUnit (ψ bk.flat) → IsAdicComplete (Ideal.span {ψ bk.flat}) O → ∃ θ' : OC l →+* (WittVector l O ⧸ Ideal.span {WittVector.map ψ (bk.ev bk.E)}), (∀ a : Ainf l, θ' (Per.θ l a) = Ideal.Quotient.mk _ (WittVector.map ψ a)) ∧ Function.Injective θ' ∧ IsDomain (WittVector l O ⧸ Ideal.span {WittVector.map ψ (bk.ev bk.E)}) ∧ ∀ a : WittVector l O, ((l : ℕ) : WittVector l O ⧸ Ideal.span {WittVector.map ψ (bk.ev bk.E)}) ∣ Ideal.Quotient.mk _ a → ψ bk.flat ^ bk.Ep.natDegree ∣ a.coeff 0 := by
  first | exact @GlobalTheory.BSP.exists_untilt_map | exact GlobalTheory.BSP.exists_untilt_map | (intros; apply GlobalTheory.BSP.exists_untilt_map <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsInjectiveRootsOfNcardRootSetStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices GlobalTheory.SpanRing
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_injective_roots_of_ncard_rootSet' : ∀ {A O : Type} [CommRing A] [IsDomain A] [CommRing O] [IsDomain O] [IsIntegrallyClosed O] [Algebra A O] (t : ℕ) (P : Polynomial A) (α : Fin t → FractionRing O), Function.Injective (algebraMap A O) → ((P.map (toFr A)).rootSet (AlgebraicClosure (FractionRing A))).ncard = t → P.map ((toFr O).comp (algebraMap A O)) = ∏ c, (Polynomial.X - Polynomial.C (α c)) → ∃ β : Fin t → O, Function.Injective β ∧ P.map (algebraMap A O) = ∏ c, (Polynomial.X - Polynomial.C (β c)) := by
  first | exact @GlobalTheory.exists_injective_roots_of_ncard_rootSet | exact GlobalTheory.exists_injective_roots_of_ncard_rootSet | (intros; apply GlobalTheory.exists_injective_roots_of_ncard_rootSet <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsInvertibleInvariantPeriodMatrixBcrisStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_invertible_invariant_periodMatrix_bcris : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ (d : ℕ) (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) (ℤ_[l])), (∀ j : Fin d, ∃ (m : ℕ) (c : Fin m → Per.Bcris l) (v : Fin m → Fin d → Per.Bcris l), (∀ i (g : ↥(GK K)), ((ρ g).map (Per.zB l)).mulVec (fun r => Per.σB (g : GQ l) (v i r)) = v i) ∧ (Pi.single j 1 : Fin d → Per.Bcris l) = ∑ i, c i • v i) → ∃ U U' : Matrix (Fin d) (Fin d) (Per.Bcris l), U * U' = 1 ∧ (∀ g : ↥(GK K), (ρ g).map (Per.zB l) * U.map (Per.σB (g : GQ l)) = U) := by
  first | exact @GlobalTheory.Per.PerMat.exists_invertible_invariant | exact GlobalTheory.Per.PerMat.exists_invertible_invariant | (intros; apply GlobalTheory.Per.PerMat.exists_invertible_invariant <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsMapEntriesHaarUnitriangularEqSmulPiStatement
section
open NumberField IsDedekindDomain Matrix Formalism.UG GlobalTheory.CuspRep MeasureTheory
open scoped ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_map_entries_haar_unitriangular_eq_smul_pi : ∀ (R : Type) [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] [LocallyCompactSpace R]
    [SecondCountableTopology R] [T2Space R] [MeasurableSpace R] [BorelSpace R] (n : ℕ)
    [MeasurableSpace (GL (Fin n) R)] [BorelSpace (GL (Fin n) R)] (μR : Measure R) [μR.IsAddHaarMeasure]
    (ν : Measure (GlobalTheory.SmGL.unipB R (Fin n))) [ν.IsHaarMeasure],
    ∃ c : ℝ≥0∞, Measure.map (fun (u : GlobalTheory.SmGL.unipB R (Fin n)) (p : {p : Fin n × Fin n // p.1 < p.2}) =>
        ((u : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) p.1.1 p.1.2) ν = c • Measure.pi (fun _ => μR) := by
  first | exact @GlobalTheory.UnipCoord.map_coords_haar | exact GlobalTheory.UnipCoord.map_coords_haar | (intros; apply GlobalTheory.UnipCoord.map_coords_haar <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsMemSubmoduleAllCharpolySeparableStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices GlobalTheory.SpanRing
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_mem_submodule_all_charpoly_separable : ∀ {O K X : Type} [CommRing O] [IsDomain O] [Infinite O] [Field K] [Algebra O K] [IsFractionRing O K] [Finite X] (t : ℕ) (M : Submodule O (X → Matrix (Fin t) (Fin t) K)) (a : X → Matrix (Fin t) (Fin t) K), (∀ x, (a x).charpoly.Separable ∨ ∃ s ∈ M, ∃ c : K, c ≠ 0 ∧ (c • s x).charpoly.Separable) → ∃ s ∈ M, ∀ x, (a x + s x).charpoly.Separable := by
  first | exact @GlobalTheory.SepGeneric.exists_separable | exact GlobalTheory.SepGeneric.exists_separable | (intros; apply GlobalTheory.SepGeneric.exists_separable <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsRepMatrixCombinationKillingCharactersStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices GlobalTheory.SpanRing
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_repMatrix_combination_killing_characters : ∀ {Γ A : Type} [Group Γ] [CommRing A] {r : ℕ} (ρ : Γ →* GL (Fin r) A) (χ : ℕ → (Γ →* Aˣ)), 2 ≤ r → Submodule.span A (Set.range (mat ρ)) = ⊤ → ∀ P : Matrix (Fin r) (Fin r) A, ∃ (m : ℕ) (f : Fin m → A) (h : Fin m → Γ), ∑ k, f k • mat ρ (h k) = P ∧ ∀ c : ℕ, ∑ k, f k * ((χ c (h k) : Aˣ) : A) = 0 := by
  first | exact @GlobalTheory.MatCorner.exists_comb_kills_chars | exact GlobalTheory.MatCorner.exists_comb_kills_chars | (intros; apply GlobalTheory.MatCorner.exists_comb_kills_chars <;> assumption)
end

