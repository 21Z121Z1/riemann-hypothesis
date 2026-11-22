import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0009
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.PseudoCoefficientSeparation
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Formalism.RealPlaceAnalysis.Bundle0003
import Formalism.RealPlaceAnalysis.Bundle0002
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0080
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0339
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0338
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0259
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0299
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0253
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0015
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0016
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.Bundle0001
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsSmoothModerateOfIsAutFunSm
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0214
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.SqNormIntegralFundamentalDomainEqL2NormSq
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaGrowthOfThetaSquareIntegrable
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0005

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnitaryFactorKernel
section
open MeasureTheory Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.FlagMeas GlobalTheory.GKModule GlobalTheory.RealInd GlobalTheory.OpTrace
open GlobalTheory.SmoothGlob (lieSet)
open GlobalTheory.Dec (IsHaarSub HasInfChar UEquiv gelfVal)
open GlobalTheory.Orb (IsPseudoCoeff ujMat ujRep)
open scoped InnerProductSpace

noncomputable section
open Filter Topology

namespace GlobalTheory.UnitaryBound

theorem re_le_of_chamber {n a : ℕ} (j : Fin a → ℕ) (hj : ∀ i, 1 ≤ j i) (s : Fin a → ℂ) (h : 0 < a)
    (hx : ∀ x : Fin a → ℝ, InChamber x → 0 ≤ (pairing j (rho n j - s) x).re) :
    (s ⟨0, h⟩).re ≤ (n : ℝ) - 1 := by
  set i0 : Fin a := ⟨0, h⟩ with hi0
  have hre : ∀ x : Fin a → ℝ, (pairing j (rho n j - s) x).re =
      ∑ i, (j i : ℝ) * ((rho n j i).re - (s i).re) * x i := by
    intro x; simp [pairing, Complex.re_sum, Complex.mul_re]
  have hI : Finset.Iio i0 = ∅ :=
    Finset.eq_empty_of_forall_notMem fun l hl => by simp [hi0, Fin.lt_def] at hl
  have hrho : (rho n j i0).re = n - j i0 := by simp [rho, hI]
  set A := (j i0 : ℝ) * ((rho n j i0).re - (s i0).re) with hA
  set B := ∑ i, (j i : ℝ) * ((rho n j i).re - (s i).re) * ((a : ℝ) - ((i : ℕ) : ℝ)) with hB
  have key : ∀ δ : ℝ, 0 < δ → 0 ≤ A + δ * B := by
    intro δ hδ
    have hc : InChamber (fun i : Fin a => (if i = i0 then (1 : ℝ) else 0) + δ * ((a : ℝ) - ((i : ℕ) : ℝ))) := by
      refine ⟨fun i l hil => ?_, fun i => ?_⟩
      · have hl : l ≠ i0 := fun e => by
          have : (i : ℕ) < l := hil
          rw [e] at this; simp [hi0] at this
        have hil' : ((i : ℕ) : ℝ) < ((l : ℕ) : ℝ) := by exact_mod_cast hil
        simp only [hl, if_false]
        have : (0 : ℝ) ≤ if i = i0 then 1 else 0 := by split_ifs <;> norm_num
        nlinarith
      · have : ((i : ℕ) : ℝ) < a := by exact_mod_cast i.2
        have : (0 : ℝ) ≤ if i = i0 then 1 else 0 := by split_ifs <;> norm_num
        nlinarith
    have := hx _ hc
    rw [hre] at this
    convert this using 1
    simp only [mul_add, Finset.sum_add_distrib, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ,
      if_true, hA, hB, Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun i _ => by ring
  have hA0 : 0 ≤ A := by
    have ht : Tendsto (fun δ : ℝ => A + δ * B) (𝓝[>] 0) (𝓝 (A + 0 * B)) :=
      ((continuous_const.add (continuous_id.mul continuous_const)).tendsto 0).mono_left nhdsWithin_le_nhds
    have := ge_of_tendsto ht (eventually_nhdsWithin_of_forall fun δ hδ => key δ hδ)
    simpa using this
  have hj0 : (1 : ℝ) ≤ j i0 := by exact_mod_cast hj i0
  rw [hA, hrho] at hA0
  have : 0 ≤ (n : ℝ) - j i0 - (s i0).re := by
    by_contra hneg
    push_neg at hneg
    nlinarith
  linarith

theorem re_nonneg_of_tendsto {p L : ℂ} {F : ℝ → ℂ} {B : ℝ} (hB : ∀ r, ‖F r‖ ≤ B) (hL : L ≠ 0)
    (hF : Tendsto (fun r : ℝ => Complex.exp (r * p) * F r) atTop (𝓝 L)) : 0 ≤ p.re := by
  by_contra hp
  push_neg at hp
  have h0 : Tendsto (fun r : ℝ => Complex.exp (r * p) * F r) atTop (𝓝 0) := by
    refine squeeze_zero_norm (a := fun r : ℝ => Real.exp (r * p.re) * B) (fun r => ?_) ?_
    · rw [norm_mul, Complex.norm_exp, Complex.re_ofReal_mul]
      exact mul_le_mul_of_nonneg_left (hB r) (Real.exp_pos _).le
    · have : Tendsto (fun r : ℝ => r * p.re) atTop atBot := tendsto_id.atTop_mul_const_of_neg hp
      simpa using (Real.tendsto_exp_atBot.comp this).mul_const B
  exact hL (tendsto_nhds_unique hF h0)

theorem inner_ι {n : ℕ} {ε : Fin n → Bool} (I : IndModule ε) (f g : I.fns) :
    ⟪I.ι g, I.ι f⟫_ℂ = ∫ k : KG ε, ⟪g.1 k, f.1 k⟫_ℂ ∂muK ε := by
  have hcont : ∀ u : I.fns, Continuous fun k : KG ε => u.1 k := fun u =>
    (mem_indFun_top.1 u.2).1.comp continuous_subtype_val
  have int : ∀ u : I.fns, Integrable (fun k : KG ε => ((‖u.1 k‖ : ℂ)) ^ 2) (muK ε) := fun u =>
    ((Complex.continuous_ofReal.comp (hcont u).norm).pow 2).integrable_of_hasCompactSupport
      (isClosed_tsupport _).isCompact
  have key : ∀ u : I.fns, ((‖I.ι u‖ : ℂ)) ^ 2 = ∫ k : KG ε, ((‖u.1 k‖ : ℂ)) ^ 2 ∂muK ε := fun u => by
    have := I.model.norm_sq u
    rw [← Complex.ofReal_pow, this, ← integral_complex_ofReal]
    push_cast; rfl
  have key' : ∀ u : I.fns, (RCLike.ofReal ‖I.ι u‖ : ℂ) ^ 2 = ∫ k : KG ε, ((‖u.1 k‖ : ℂ)) ^ 2 ∂muK ε := key
  rw [inner_eq_sum_norm_sq_div_four (𝕜 := ℂ), ← map_add, ← map_sub, ← map_smul, ← map_sub, ← map_add,
    key', key', key', key']
  have e : (fun k : KG ε => ⟪g.1 k, f.1 k⟫_ℂ) = fun k : KG ε =>
      (((‖(g + f).1 k‖ : ℂ)) ^ 2 - ((‖(g - f).1 k‖ : ℂ)) ^ 2 +
        (((‖(g - (RCLike.I : ℂ) • f).1 k‖ : ℂ)) ^ 2 - ((‖(g + (RCLike.I : ℂ) • f).1 k‖ : ℂ)) ^ 2) * RCLike.I) / 4 := by
    funext k
    rw [inner_eq_sum_norm_sq_div_four (𝕜 := ℂ)]
    rfl
  rw [e, integral_div]
  congr 1
  have i12 : Integrable (fun k : KG ε => ((‖(g + f).1 k‖ : ℂ)) ^ 2 - ((‖(g - f).1 k‖ : ℂ)) ^ 2) (muK ε) :=
    (int _).sub (int _)
  have i34 : Integrable (fun k : KG ε => (((‖(g - (RCLike.I : ℂ) • f).1 k‖ : ℂ)) ^ 2 -
      ((‖(g + (RCLike.I : ℂ) • f).1 k‖ : ℂ)) ^ 2) * RCLike.I) (muK ε) := ((int _).sub (int _)).mul_const _
  rw [integral_add i12 i34, integral_sub (int _) (int _), integral_mul_const, integral_sub (int _) (int _)]

theorem isKFinFun_mul {n : ℕ} {ε : Fin n → Bool} {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    {φ : UJ ε → V} (hφ : IsKFinFun φ) {k : UJ ε} (hk : k ∈ KG ε) : IsKFinFun fun g => φ (g * k) := by
  unfold IsKFinFun at *
  have hle : Submodule.span ℂ {ψ : UJ ε → V | ∃ k' ∈ KG ε, ψ = fun g => (fun g => φ (g * k)) (g * k')} ≤
      Submodule.span ℂ {ψ : UJ ε → V | ∃ k' ∈ KG ε, ψ = fun g => φ (g * k')} := by
    refine Submodule.span_mono ?_
    rintro ψ ⟨k', hk', rfl⟩
    exact ⟨k' * k, mul_mem hk' hk, by funext g; simp [mul_assoc]⟩
  exact Submodule.finiteDimensional_of_le hle

theorem unitary_bound : GlobalTheory.Published.HarishChandraAnalyticity → GlobalTheory.Published.LanglandsClassification → ∀ (n : ℕ) (ε : Fin n → Bool) (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V] (π : Matrix (Fin n) (Fin n) ℂ → (V →L[ℂ] V)), IsIrrAdm ε π → IsURepOn (UJset ε) π → ∀ I : IndModule ε, I.Positive → ∀ Z, IsFactor ε I.ρ Z (kFinVec ε I.ρ) π → (∀ ν : Measure (UJ ε), IsHaarSub I.Nbar ν → (Z : Set I.H) = I.intKer ν) → ∀ h : 0 < I.a, (I.s ⟨0, h⟩).re ≤ (n : ℝ) - 1 := by
  intro hHC hL n ε V _ _ _ π hπ hπu I hI Z hZ hZker h0
  have hL' := hL
  obtain ⟨hInd, hQuot, -, hLim, -⟩ := hL'
  obtain ⟨hadm, -, hgk, hkfin, -, -⟩ := hInd n ε I
  obtain ⟨ν, hν⟩ := GlobalTheory.Published.Langlands.exists_isHaarSub_nbar I.toDatum
  obtain ⟨hZgk, -, -, T, hTY, hTker, hTK, hTX⟩ := hZ
  have hZne : Z ≠ kFinVec ε I.ρ := by
    obtain ⟨-, -, Z', hZ', -, hne, -⟩ := hQuot n ε I hI ν hν
    have : Z = Z' := SetLike.coe_injective ((hZker ν hν).trans hZ'.symm)
    rw [this]; exact hne
  obtain ⟨a₀, ha₀, ha₀K, ha₀Z⟩ := GlobalTheory.T.k_finite_orthogonal_complement n ε I.H I.ρ hadm Z (fun v hv => hZgk.kFin v hv)
    hZgk.kStable hZne
  obtain ⟨φ₀, hφ₀K, rfl⟩ := (hkfin a₀).1 ha₀K
  have hφ₀ : φ₀.1 ≠ 0 := fun e => ha₀ (by rw [show φ₀ = 0 from Subtype.ext e, map_zero])
  obtain ⟨k, hk, hφk⟩ := (GlobalTheory.T.induced_k_finite_restriction n ε I.toDatum φ₀.1 φ₀.2 hφ₀K).2.2 hφ₀
  set φ : I.fns := ⟨fun g => φ₀.1 (g * k), indFun_mul_right φ₀.2 trivial⟩ with hφdef
  have hφK : IsKFinFun φ.1 := isKFinFun_mul hφ₀K hk
  have hφ1 : φ.1 1 ≠ 0 := by simpa [hφdef] using hφk
  have haρ : I.ι φ = I.ρ (uMat k) (I.ι φ₀) := (I.model.transl k trivial φ₀ φ fun g => rfl).symm
  have haK : IsKFin ε I.ρ (I.ι φ) := (hkfin _).2 ⟨φ, hφK, rfl⟩

  have hiso : ∀ v w : I.H, ⟪I.ρ (uMat k) v, I.ρ (uMat k) w⟫_ℂ = ⟪v, w⟫_ℂ := fun v w =>
    (⟨(I.ρ (uMat k)).toLinearMap, fun v => hadm.2.2.1 _ hk v⟩ : I.H →ₗᵢ[ℂ] I.H).inner_map_map v w
  have hinv : ∀ z, I.ρ (uMat k) (I.ρ (uMat k⁻¹) z) = z := fun z => by
    rw [← ContinuousLinearMap.comp_apply, ← hadm.1.2 _ k.2 _ k⁻¹.2, RealIwasawa.uMat_mul_inv, hadm.1.1]; rfl
  have haZ : ∀ z ∈ Z, ⟪I.ι φ, z⟫_ℂ = 0 := fun z hz => by
    rw [haρ, ← hinv z, hiso]
    exact ha₀Z _ (hZgk.kStable _ (inv_mem hk) z hz)

  obtain ⟨w, hwK, hw⟩ := (GlobalTheory.T.intertwiner_of_k_finite_vectors n ε I.H I.ρ V π hadm hπ.2.1 T hTY (fun k hk y hy => hTK k hk y hy)).1
    (I.ι φ) haK fun y hy hTy => haZ y ((hTker y hy).1 hTy)
  have hTfin : ∀ y, IsKFin ε I.ρ y → IsKFin ε π (T y) := fun y hy => by
    have : T y ∈ (kFinVec ε I.ρ).map T := Submodule.mem_map_of_mem hy
    rw [hTY] at this; exact this
  have hcoef := GlobalTheory.T.smooth_intertwiner_extension hHC n ε I.H I.ρ V π hadm hπ.2.1 hgk
    (fun v hv => (GlobalTheory.T.irreducible_K_stable_finite_subspace n ε V π hπu hπ.2.2).2 v hv) T hTfin (fun k hk y hy => hTK k hk y hy)
    (fun X hX y hy => hTX X hX y hy) (I.ι φ) w haK hwK hw

  obtain ⟨f, hf, hfK, hh, -, hint, hne⟩ := GlobalTheory.T.induced_intertwining_integral_nonzero hHC hL n ε I hI ν hν (φ.1 1) hφ1
  obtain ⟨⟨f', hf', hf'K, hf'φ⟩, hφM, -⟩ := GlobalTheory.T.induced_k_finite_restriction n ε I.toDatum φ.1 φ.2 hφK
  obtain ⟨c, hc, -, hlim⟩ := hLim n ε I.toDatum hI ν hν
  have hf'1 : f' 1 = φ.1 1 := hf'φ 1 (one_mem _)
  have hL0 : (c : ℂ) * ∫ u, ⟪f' 1, f u⟫_ℂ ∂ν ≠ 0 := by
    refine mul_ne_zero (by exact_mod_cast hc.ne') ?_
    have := (hint 1 (φ.1 1) hφM).2
    simp only [mul_one] at this
    rw [hf'1, ← this]; exact hne
  have hιf : IsKFin ε I.ρ (I.ι ⟨f, hf⟩) := (hkfin _).2 ⟨⟨f, hf⟩, hfK, rfl⟩
  refine re_le_of_chamber I.j I.pos I.s h0 fun x hx => ?_
  choose t ht using fun r : ℝ => exists_isSplit I.flag (r • x)
  refine re_nonneg_of_tendsto (B := ‖w‖ * ‖T (I.ι ⟨f, hf⟩)‖) (fun r => ?_) hL0
    ((hlim f hf hfK f' hf' hf'K x hx t fun r => (ht r).1).2)
  have e1 : ∫ k : KG ε, ⟪f' k, f (k * t r)⟫_ℂ ∂muK ε = ⟪I.ι φ, I.ρ (uMat (t r)) (I.ι ⟨f, hf⟩)⟫_ℂ := by
    rw [I.model.transl (t r) trivial ⟨f, hf⟩ ⟨_, indFun_mul_right hf trivial⟩ fun g => rfl, inner_ι]
    refine integral_congr_ae (Eventually.of_forall fun k => ?_)
    simp only
    rw [hf'φ k k.2]
  rw [e1, hcoef _ hιf _ (t r).2]
  refine (norm_inner_le_norm _ _).trans ?_
  rw [hπu.2.1 _ (t r).2]

end GlobalTheory.UnitaryBound
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnitaryIrreducibleSmoothAdmissible
section
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes IsDedekindDomain NumberField Filter GlobalTheory.AutomorphicL2Unitary GlobalTheory.OpTrace GlobalTheory.AdelicU GlobalTheory.AutMult
open GlobalTheory.PRep (IsAdmissible fixed)

noncomputable section

open scoped InnerProductSpace

namespace GlobalTheory.SmoothUnitary

open GlobalTheory.PRep

section

variable {G H : Type} [Group G] [NormedAddCommGroup H] [InnerProductSpace ℂ H]

def stab (π : G →* (H →L[ℂ] H)) (v : H) : Subgroup G := GlobalTheory.DoubleCosetSetoid.clmStabilizer π v

theorem inner_map_map_of_norm {π : G →* (H →L[ℂ] H)} (hπ : ∀ g x, ‖π g x‖ = ‖x‖) (g : G) (x y : H) :
    ⟪π g x, π g y⟫_ℂ = ⟪x, y⟫_ℂ :=
  (⟨(π g : H →ₗ[ℂ] H), hπ g⟩ : H →ₗᵢ[ℂ] H).inner_map_map x y

theorem exists_mean (π : G →* (H →L[ℂ] H)) (hπ : ∀ g x, ‖π g x‖ = ‖x‖) (K : Subgroup G) (w : H)
    (hf : (Set.range fun k : K => π (k : G) w).Finite) :
    ∃ m ∈ Submodule.span ℂ (Set.range fun k : K => π (k : G) w), (∀ k ∈ K, π k m = m) ∧
      ∀ u : H, (∀ k ∈ K, π k u = u) → ⟪u, m⟫_ℂ = ⟪u, w⟫_ℂ := by
  classical
  set O := hf.toFinset with hO
  have hmem : ∀ z, z ∈ O ↔ ∃ k : K, π (k : G) w = z := fun z => by simp [O]
  have hw : w ∈ O := (hmem w).2 ⟨1, by simp⟩
  have hc : (O.card : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (Finset.card_ne_zero.2 ⟨w, hw⟩)
  refine ⟨(O.card : ℂ)⁻¹ • ∑ z ∈ O, z, ?_, fun k hk => ?_, fun u hu => ?_⟩
  · refine Submodule.smul_mem _ _ (Submodule.sum_mem _ fun z hz => Submodule.subset_span ?_)
    obtain ⟨k, rfl⟩ := (hmem z).1 hz
    exact ⟨k, rfl⟩
  · rw [map_smul, map_sum]
    congr 1
    refine Finset.sum_nbij' (fun z => π k z) (fun z => π k⁻¹ z) (fun z hz => ?_) (fun z hz => ?_)
      (fun z _ => ?_) (fun z _ => ?_) (fun z _ => rfl)
    · obtain ⟨k', rfl⟩ := (hmem z).1 hz
      exact (hmem _).2 ⟨⟨k, hk⟩ * k', by simp⟩
    · obtain ⟨k', rfl⟩ := (hmem z).1 hz
      exact (hmem _).2 ⟨⟨k, hk⟩⁻¹ * k', by simp⟩
    · simp [← ContinuousLinearMap.mul_apply, ← map_mul]
    · simp [← ContinuousLinearMap.mul_apply, ← map_mul]
  · have h1 : ∀ z ∈ O, ⟪u, z⟫_ℂ = ⟪u, w⟫_ℂ := fun z hz => by
      obtain ⟨k, rfl⟩ := (hmem z).1 hz
      rw [← inner_map_map_of_norm hπ k u w, hu k k.2]
    rw [inner_smul_right, inner_sum, Finset.sum_congr rfl h1, Finset.sum_const, nsmul_eq_mul, ← mul_assoc,
      inv_mul_cancel₀ hc, one_mul]

variable [TopologicalSpace G] [IsTopologicalGroup G]

theorem exists_compactOpen_subset [NonarchimedeanGroup G] [LocallyCompactSpace G] {U : Set G}
    (hU : U ∈ nhds (1 : G)) : ∃ K : Subgroup G, IsOpen (K : Set G) ∧ IsCompact (K : Set G) ∧ (K : Set G) ⊆ U := by
  obtain ⟨C, hC, hCU, hCc⟩ := local_compact_nhds hU
  obtain ⟨V, hV⟩ := NonarchimedeanGroup.is_nonarchimedean C hC
  exact ⟨V.toSubgroup, V.isOpen, hCc.of_isClosed_subset V.isClosed hV, hV.trans hCU⟩

theorem finite_orbit (π : G →* (H →L[ℂ] H)) {K : Subgroup G} (hK : IsCompact (K : Set G)) {w : H}
    (hw : IsOpen (stab π w : Set G)) : (Set.range fun k : K => π (k : G) w).Finite := by
  haveI : CompactSpace K := isCompact_iff_compactSpace.1 hK
  haveI := Subgroup.quotient_finite_of_isOpen ((stab π w).subgroupOf K) (hw.preimage continuous_subtype_val)
  refine (Set.finite_range (fun q : K ⧸ (stab π w).subgroupOf K => π ((q.out : K) : G) w)).subset ?_
  rintro _ ⟨k, rfl⟩
  refine ⟨QuotientGroup.mk k, ?_⟩
  obtain ⟨s, hs⟩ := QuotientGroup.mk_out_eq_mul ((stab π w).subgroupOf K) k
  have h2 : π ((s : K) : G) w = w := Subgroup.mem_subgroupOf.1 s.2
  simp only [hs, Subgroup.coe_mul, map_mul, ContinuousLinearMap.mul_apply, h2]

end

theorem exists_fixed_ne_zero : ∀ (G : Type) [Group G] (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (π : G →* (H →L[ℂ] H)), (∀ g x, ‖π g x‖ = ‖x‖) → ∀ (K : Subgroup G) (x : H), x ≠ 0 →
      (∀ k ∈ K, ‖π k x - x‖ ≤ ‖x‖ / 2) → ∃ y : H, y ≠ 0 ∧ ∀ k ∈ K, π k y = y := by
  intro G _ H _ _ _ π hπ K x hx hK
  letI : InnerProductSpace ℝ H := InnerProductSpace.rclikeToReal ℂ H
  set O : Set H := Set.range fun k : K => π (k : G) x
  set C : Set H := closure (convexHull ℝ O)
  have hconv : Convex ℝ C := (convex_convexHull ℝ O).closure
  have hxC : x ∈ C := subset_closure (subset_convexHull ℝ O ⟨1, by simp⟩)
  have hball : C ⊆ Metric.closedBall x (‖x‖ / 2) := by
    refine closure_minimal (convexHull_min ?_ (convex_closedBall _ _)) Metric.isClosed_closedBall
    rintro _ ⟨k, rfl⟩
    rw [Metric.mem_closedBall, dist_eq_norm]
    exact hK k k.2
  have hinv : ∀ k ∈ K, ∀ z ∈ C, π k z ∈ C := by
    intro k hk z hz
    let T : H →L[ℝ] H := (π k).restrictScalars ℝ
    have hO : T '' O ⊆ O := by
      rintro _ ⟨_, ⟨k', rfl⟩, rfl⟩
      exact ⟨⟨k, hk⟩ * k', by simp [T]⟩
    have h1 : T '' convexHull ℝ O ⊆ convexHull ℝ O := by
      have e := (T : H →ₗ[ℝ] H).image_convexHull O
      change (T : H →ₗ[ℝ] H) '' convexHull ℝ O ⊆ _
      rw [e]
      exact convexHull_min ((show (T : H →ₗ[ℝ] H) '' O ⊆ O from hO).trans (subset_convexHull ℝ O)) (convex_convexHull ℝ O)
    have h2 : T '' C ⊆ C := (image_closure_subset_closure_image T.continuous).trans (closure_mono h1)
    exact h2 ⟨z, hz, rfl⟩
  obtain ⟨y, hyC, hy⟩ := exists_norm_eq_iInf_of_complete_convex ⟨x, hxC⟩ isClosed_closure.isComplete hconv 0
  have hmin : ∀ z ∈ C, ‖y‖ ≤ ‖z‖ := fun z hz => by
    have := ciInf_le (f := fun w : C => ‖(0 : H) - (w : H)‖) ⟨0, by rintro _ ⟨w, rfl⟩; exact norm_nonneg _⟩ (⟨z, hz⟩ : C)
    simp only [zero_sub, norm_neg] at hy this
    rw [← hy] at this
    exact this
  refine ⟨y, fun h0 => ?_, fun k hk => ?_⟩
  · have h1 := hball (h0 ▸ hyC)
    rw [Metric.mem_closedBall, dist_eq_norm, zero_sub, norm_neg] at h1
    have := norm_pos_iff.2 hx
    linarith
  · set z := π k y
    have hz : z ∈ C := hinv k hk y hyC
    have hzn : ‖z‖ = ‖y‖ := hπ k y
    have hmid : (1 / 2 : ℝ) • y + (1 / 2 : ℝ) • z ∈ C := hconv hyC hz (by norm_num) (by norm_num) (by norm_num)
    have h3 := hmin _ hmid
    have h4 : (1 / 2 : ℝ) • y + (1 / 2 : ℝ) • z = (1 / 2 : ℝ) • (y + z) := by rw [smul_add]
    rw [h4, norm_smul, Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)] at h3
    have hp := parallelogram_law_with_norm ℂ y z
    rw [hzn] at hp
    have h5 : ‖y - z‖ * ‖y - z‖ ≤ 0 := by nlinarith [norm_nonneg (y + z), norm_nonneg y]
    have h6 : ‖y - z‖ = 0 := by nlinarith [norm_nonneg (y - z)]
    exact (sub_eq_zero.1 (norm_eq_zero.1 h6)).symm

open GlobalTheory.AutomorphicL2Unitary GlobalTheory.OpTrace GlobalTheory.AutMult in

theorem isIrreducible_isAdmissible_smRep : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [NonarchimedeanGroup G] [LocallyCompactSpace G] (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (π : G →* (H →L[ℂ] H)), IsIrrUnitary π →
    (∀ K : Subgroup G, IsOpen (K : Set G) → IsCompact (K : Set G) → FiniteDimensional ℂ (fixed (toRep π) K)) →
      (smRep π).IsIrreducible ∧ IsAdmissible (smRep π) := by
  intro G _ _ _ _ _ H _ _ π hπ hfin
  have hc := hπ.complete
  have hu := hπ.unitary
  have memF : ∀ (K : Subgroup G) (u : H), u ∈ fixed (toRep π) K ↔ ∀ k ∈ K, π k u = u := fun K u => by
    change (∀ k : K, toRep π k u = ((1 : K →* ℂˣ) k : ℂ) • u) ↔ _
    simp
  have memV : ∀ v : H, v ∈ smoothPart (toRep π) ↔ IsOpen (stab π v : Set G) := fun v => Iff.rfl
  refine ⟨?_, isSmooth_smoothRep (toRep π), fun K hKo hKc => ?_⟩
  swap
  · haveI := hfin K hKo hKc
    let f : fixed (smRep π) K →ₗ[ℂ] fixed (toRep π) K :=
      { toFun := fun v => ⟨(v : smoothPart (toRep π)).1, (memF K _).2 fun k hk => by
            have h : smRep π k (v : smoothPart (toRep π)) = v := by simpa using v.2 ⟨k, hk⟩
            exact congrArg Subtype.val h⟩
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl }
    exact Module.Finite.of_injective f fun a b e => by
      have := congrArg Subtype.val e
      exact Subtype.ext (Subtype.ext this)
  have hex : ∃ y : H, y ≠ 0 ∧ y ∈ smoothPart (toRep π) := by
    have := hπ.irred.1
    obtain ⟨x, hx⟩ := exists_ne (0 : H)
    have hx2 : 0 < ‖x‖ / 2 := by have := norm_pos_iff.2 hx; positivity
    have hU : {g : G | ‖π g x - x‖ < ‖x‖ / 2} ∈ nhds (1 : G) := by
      have hcont : Continuous fun g => ‖π g x - x‖ := ((hu.continuous_apply x).sub continuous_const).norm
      exact (isOpen_lt hcont continuous_const).mem_nhds (by simpa using hx2)
    obtain ⟨K, hKo, -, hKU⟩ := exists_compactOpen_subset hU
    obtain ⟨y, hy, hyK⟩ := exists_fixed_ne_zero G H π hu.norm_apply K x hx (fun k hk => (hKU hk).le)
    exact ⟨y, hy, (memV y).2 (Subgroup.isOpen_mono (H₁ := K) (fun k hk => hyK k hk) hKo)⟩
  obtain ⟨y, hy0, hy⟩ := hex
  refine { exists_pair_ne := ⟨⊥, ⊤, fun e => hy0 (congrArg Subtype.val ((Submodule.mem_bot ℂ).1
    (show (⟨y, hy⟩ : smoothPart (toRep π)) ∈ (⊥ : Subrepresentation (smRep π)).toSubmodule from
      e ▸ Submodule.mem_top)))⟩, eq_bot_or_eq_top := fun S => ?_ }
  by_cases hS : S = ⊥
  · exact Or.inl hS
  right
  let V := smoothPart (toRep π)
  let W' : Submodule ℂ H := S.toSubmodule.map V.subtype
  have hWst : ∀ g, ∀ w ∈ W', π g w ∈ W' := by
    rintro g _ ⟨w, hw, rfl⟩
    exact ⟨smRep π g w, S.apply_mem_toSubmodule g hw, rfl⟩
  have hWV : ∀ w ∈ W', w ∈ V := by
    rintro _ ⟨w, -, rfl⟩
    exact w.2
  have hcl : W'.topologicalClosure = ⊤ := by
    refine (hπ.irred.2 _ ⟨W'.isClosed_topologicalClosure, fun g v hv => ?_⟩).resolve_left ?_
    · exact Submodule.topologicalClosure_minimal W' (t := W'.topologicalClosure.comap (π g : H →ₗ[ℂ] H))
        (fun w hw => W'.le_topologicalClosure (hWst g w hw))
        (W'.isClosed_topologicalClosure.preimage (π g).continuous) hv
    · intro e
      have hS' : S.toSubmodule ≠ ⊥ := fun e' => hS (Subrepresentation.ext e')
      obtain ⟨w, hw, hw0⟩ := (Submodule.ne_bot_iff _).1 hS'
      have h1 : (w : H) ∈ W'.topologicalClosure := W'.le_topologicalClosure ⟨w, hw, rfl⟩
      rw [e, Submodule.mem_bot] at h1
      exact hw0 (Subtype.ext h1)
  have key : ∀ v ∈ V, v ∈ W' := by
    intro v hv
    obtain ⟨K, hKo, hKc, hKv⟩ := exists_compactOpen_subset (((memV v).1 hv).mem_nhds (one_mem (stab π v)))
    haveI := hfin K hKo hKc
    let M : Submodule ℂ H := W' ⊓ fixed (toRep π) K
    haveI : FiniteDimensional ℂ M := Submodule.finiteDimensional_of_le inf_le_right
    have hvF : v ∈ fixed (toRep π) K := (memF K v).2 fun k hk => hKv hk
    have huF : v - M.starProjection v ∈ fixed (toRep π) K :=
      Submodule.sub_mem _ hvF (Submodule.mem_inf.1 (M.starProjection_apply_mem v)).2
    have huM := M.sub_starProjection_mem_orthogonal v
    have horth : ∀ w ∈ W', ⟪v - M.starProjection v, w⟫_ℂ = 0 := by
      intro w hw
      obtain ⟨m, hm, hmK, hmu⟩ := exists_mean π hu.norm_apply K w (finite_orbit π hKc ((memV w).1 (hWV w hw)))
      have hmW : m ∈ W' := Submodule.span_le.2 (by rintro _ ⟨k, rfl⟩; exact hWst k w hw) hm
      rw [← hmu _ ((memF K _).1 huF)]
      exact (Submodule.mem_orthogonal' _ _).1 huM m ⟨hmW, (memF K m).2 hmK⟩
    have hu0 : v - M.starProjection v = 0 := by
      have hle : W'.topologicalClosure ≤ LinearMap.ker (innerₛₗ ℂ (v - M.starProjection v)) :=
        Submodule.topologicalClosure_minimal _ (fun w hw => horth w hw)
          (ContinuousLinearMap.isClosed_ker (innerSL ℂ (v - M.starProjection v)))
      have h1 := hle (hcl ▸ Submodule.mem_top : v - M.starProjection v ∈ W'.topologicalClosure)
      exact inner_self_eq_zero.1 h1
    have hvM : v ∈ M := (sub_eq_zero.1 hu0).symm ▸ M.starProjection_apply_mem v
    exact hvM.1
  refine Subrepresentation.ext (eq_top_iff.2 fun v _ => ?_)
  obtain ⟨w, hw, e⟩ := key v.1 v.2
  exact (Subtype.ext e : w = v) ▸ hw

end GlobalTheory.SmoothUnitary
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilThetaLevelPolynomialInHeight
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct ENNReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm
open scoped Pointwise

noncomputable section

namespace GlobalTheory.LevelGrowth

theorem level_poly : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (hθ : IsInfFam θ) (ε : Bool) (M X : HSp D)
    (χ χ' : (AE D)ˣ →* Circle) (ω : WRep M X) (hω : IsWeil ψ ε M X χ χ' ω) (Φ : WO M X → ℂ) (hΦ : IsThetaFunO ψ (sgn ε M) X Φ)
    (C₁ : Set (GA D M)) (hC₁ : IsCompact C₁),
    ∃ K₀ : Set (WO M X), K₀ ∈ nhds (0 : WO M X) ∧ IsCompact K₀ ∧ ∃ (m : ℝ) (e : ℕ), ∀ y ∈ C₁, ∀ h : GA D X,
      ∃ n : ℕ, 0 < n ∧ (n : ℝ) ≤ m * (GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.height θ X h : ℝ) ^ e ∧
        ∀ u ∈ K₀, u.map (infPart D) = 0 → heisO ψ (sgn ε M) X (n • u) (ω (y, h) Φ) = ω (y, h) Φ := by
  intro D ψ θ hθ ε M X χ χ' ω hω Φ hΦ C₁ hC₁
  obtain ⟨U, hU, hΦU⟩ := GlobalTheory.Size.isTheta_iff_level.1 hΦ
  obtain ⟨K₀, h0, hK₀, m, hlev⟩ := GlobalTheory.KernelSeminorm.exists_level_multiple (S := sgn ε M) (T := X) hU
  obtain ⟨B, hB⟩ := hC₁.bddAbove_image
    ((GlobalTheory.Grow.continuous_height (sgn ε M)).comp (continuous_ofSgn_symm ε M)).continuousOn
  obtain ⟨C, hC, hcmp⟩ := GlobalTheory.Grow.height_comparison X hθ
  refine ⟨K₀, h0, hK₀, m * max B 0 * C, 1, fun y hy h => ?_⟩
  set g := (ofSgn ε M).symm y with hg
  obtain ⟨n, hn, hnle, hmem⟩ := hlev g h
  refine ⟨n, hn, ?_, fun u hu hinf => ?_⟩
  · have hgB : GlobalTheory.Grow.height (sgn ε M) g ≤ max B 0 := (hB ⟨y, hy, rfl⟩).trans (le_max_left _ _)
    have hhC : GlobalTheory.Grow.height X h ≤ C * (GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.height θ X h : ℝ) := (hcmp h).2
    have hm0 : (0 : ℝ) ≤ m := m.cast_nonneg
    have hg0 := (GlobalTheory.Grow.height_pos (sgn ε M) g).le
    have hh0 := (GlobalTheory.Grow.height_pos X h).le
    calc (n : ℝ) ≤ m * (GlobalTheory.Grow.height (sgn ε M) g * GlobalTheory.Grow.height X h) := hnle
      _ ≤ m * (max B 0 * (C * (GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.height θ X h : ℝ))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul hgB hhC hh0 (le_max_right _ _)) hm0
      _ = m * max B 0 * C * (GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.height θ X h : ℝ) ^ 1 := by ring
  · have hv : (actO (sgn ε M) X g⁻¹ h⁻¹ (n • u)).map (infPart D) = 0 := by
      have : (n • u).map (infPart D) = 0 := by
        ext i j
        have h3 : infPart D (u i j) = 0 := congrFun (congrFun hinf i) j
        exact (map_nsmul (infPart D) n (u i j)).trans ((congrArg (n • ·) h3).trans (nsmul_zero n))
      unfold actO
      rw [Matrix.map_mul, Matrix.map_mul, this, Matrix.mul_zero, Matrix.zero_mul]
    have hfix := hΦU.2 _ (hmem u hu hinf) hv
    have e := hω.om_heis g h (actO (sgn ε M) X g⁻¹ h⁻¹ (n • u)) Φ hΦ
    rw [hfix, GlobalTheory.ThetaGrowth.actO_mul, mul_inv_cancel, mul_inv_cancel, GlobalTheory.ThetaGrowth.actO_one] at e
    have e2 : (WRep.toSgn ε ω) (g, h) = ω (y, h) := by
      simp [WRep.toSgn, hg]
    rw [e2] at e
    exact e.symm

end GlobalTheory.LevelGrowth
end
end

