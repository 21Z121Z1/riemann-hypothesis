import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HeckeTateFunctionalEquationCM
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0006
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1113
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0046
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1097
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0040
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1094
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0887
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1117
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1086
import Development.AbelianVarietyTheory.Definitions.Divisors.IsDominantOfSection
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1095
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0045
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1122
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TamagawaSpecialUnitary

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbsNormDifferentEqProd
section
noncomputable section

open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.CompletedLStripBounds GlobalTheory.HeckeEps
open Formalism.L2.Host (unif atFin unif_spec IsUnitAt)

namespace GlobalTheory.HeckeEpsAbs

variable {E : Type} [Field E] [NumberField E]

theorem norm_gaussSumAt_sq (χ : HChar E) (w : HeightOneSpectrum (𝓞 E)) (a : ℕ) (c : Eˣ) (ha : a ≠ 0) (hχ : ExpAt χ w a)
    (hu : IsUnitary χ) (hc : w.valuation E (c : E) = WithZero.exp (-((a + diffExp w : ℕ) : ℤ))) :
    ‖gaussSumAt χ w a c‖ ^ 2 = (Ideal.absNorm w.asIdeal : ℝ) ^ a := GlobalTheory.T.heckeLocalGaussSum_norm_sq_eq_absNorm_pow χ w a c ha hχ hu hc

theorem norm_locK {χ : HChar E} (hu : IsUnitary χ) (w : HeightOneSpectrum (𝓞 E)) (x : Eˣ) :
    ‖((χ.locK w x : ℂˣ) : ℂ)‖ = 1 := hu _

theorem absNorm_pos (w : HeightOneSpectrum (𝓞 E)) : 0 < Ideal.absNorm w.asIdeal :=
  Nat.pos_of_ne_zero fun h => w.ne_bot (Ideal.absNorm_eq_zero_iff.1 h)

theorem natCast_pow_cpow {N : ℕ} (hN : (N : ℂ) ≠ 0) (k : ℕ) (t : ℂ) :
    (((N ^ k : ℕ) : ℂ)) ^ t = (N : ℂ) ^ ((k : ℂ) * t) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, Nat.cast_mul, Complex.natCast_mul_natCast_cpow, ih, ← Complex.cpow_add _ _ hN]
    congr 1; push_cast; ring

theorem prod_natCast_cpow {ι : Type} (S : Finset ι) (f : ι → ℕ) (t : ℂ) :
    ∏ i ∈ S, ((f i : ℕ) : ℂ) ^ t = (((∏ i ∈ S, f i : ℕ)) : ℂ) ^ t := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | insert i S hi ih => rw [Finset.prod_insert hi, Finset.prod_insert hi, ih, Nat.cast_mul, Complex.natCast_mul_natCast_cpow]

theorem locEps_eq_mul (χ : HChar E) (w : HeightOneSpectrum (𝓞 E)) (k : ℕ) (s : ℂ) :
    locEps χ w k s = locEps χ w k (1 / 2) * (((Ideal.absNorm w.asIdeal ^ (k + diffExp w) : ℕ) : ℂ) ^ (1 / 2 - s)) := by
  have hN : ((Ideal.absNorm w.asIdeal : ℕ) : ℂ) ≠ 0 := by exact_mod_cast (absNorm_pos w).ne'
  rw [natCast_pow_cpow hN]
  simp only [locEps]
  have e : ((Ideal.absNorm w.asIdeal : ℕ) : ℂ) ^ (-s * ((k + diffExp w : ℕ) : ℂ)) =
      ((Ideal.absNorm w.asIdeal : ℕ) : ℂ) ^ (-(1 / 2) * ((k + diffExp w : ℕ) : ℂ)) *
        ((Ideal.absNorm w.asIdeal : ℕ) : ℂ) ^ (((k + diffExp w : ℕ) : ℂ) * (1 / 2 - s)) := by
    rw [← Complex.cpow_add _ _ hN]; congr 1; ring
  rw [e]; ring

theorem norm_locEps_half {χ : HChar E} (hu : IsUnitary χ) {w : HeightOneSpectrum (𝓞 E)} {k : ℕ} (hk : ExpAt χ w k) :
    ‖locEps χ w k (1 / 2)‖ = 1 := by
  have hNpos : (0 : ℝ) < ((Ideal.absNorm w.asIdeal : ℕ) : ℝ) := by exact_mod_cast absNorm_pos w
  have hG : ‖(if k = 0 then (1 : ℂ) else gaussSumAt χ w k (unif w ^ (k + diffExp w)))‖ =
      ((Ideal.absNorm w.asIdeal : ℕ) : ℝ) ^ ((k : ℝ) / 2) := by
    split_ifs with h
    · simp [h]
    · have := norm_gaussSumAt_sq χ w k _ h hk hu (valuation_unif_pow w _)
      rw [← Real.sqrt_sq (norm_nonneg _), this, Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul hNpos.le]
      ring_nf
  rw [locEps, norm_mul, norm_mul, norm_mul, norm_locK hu, hG, Complex.norm_natCast_cpow_of_pos (absNorm_pos w),
    Complex.norm_natCast_cpow_of_pos (absNorm_pos w), one_mul, ← Real.rpow_add hNpos, ← Real.rpow_add hNpos]
  convert Real.rpow_zero _ using 2
  simp
  ring

theorem absNorm_different_eq_prod (S : Finset (HeightOneSpectrum (𝓞 E))) (hS : ∀ w, w ∉ S → diffExp w = 0) :
    Ideal.absNorm (differentIdeal ℤ (𝓞 E)) = ∏ w ∈ S, Ideal.absNorm w.asIdeal ^ diffExp w := by
  have hD : differentIdeal ℤ (𝓞 E) ≠ ⊥ := differentIdeal_ne_bot
  have hm : ∀ w : HeightOneSpectrum (𝓞 E), w.maxPowDividing (differentIdeal ℤ (𝓞 E)) = w.asIdeal ^ diffExp w := by
    intro w
    rw [w.maxPowDividing_eq_pow_multiset_count hD, diffExp, HeightOneSpectrum.count_normalizedFactors_eq_multiplicity hD]
  have h := Ideal.finprod_heightOneSpectrum_factorization hD
  rw [finprod_eq_prod_of_mulSupport_subset _ (s := S) ?_] at h
  · conv_lhs => rw [← h]
    rw [map_prod]
    simp only [hm, map_pow]
  · intro w hw
    by_contra h'
    apply hw
    show w.maxPowDividing _ = 1
    rw [hm, hS w h', pow_zero]

theorem finEps_eq (χ : HChar E) (a : HeightOneSpectrum (𝓞 E) →₀ ℕ) (s : ℂ) :
    finEps χ a s = finEps χ a (1 / 2) *
      ((((discr E).natAbs * a.prod fun v k => Ideal.absNorm v.asIdeal ^ k : ℕ) : ℂ) ^ (1 / 2 - s)) := by
  classical
  have hD : differentIdeal ℤ (𝓞 E) ≠ ⊥ := differentIdeal_ne_bot
  set S : Finset (HeightOneSpectrum (𝓞 E)) := ((Ideal.finite_factors hD).union a.support.finite_toSet).toFinset with hSdef
  have hS : ∀ w, w ∉ S → diffExp w = 0 ∧ a w = 0 := by
    intro w hw
    simp only [hSdef, Set.Finite.mem_toFinset, Set.mem_union, Set.mem_setOf_eq, Finset.mem_coe, Finsupp.mem_support_iff,
      not_or, not_not] at hw
    exact ⟨multiplicity_eq_zero.2 hw.1, hw.2⟩
  have hsub : ∀ f : HeightOneSpectrum (𝓞 E) → ℂ, (∀ w, diffExp w = 0 → a w = 0 → f w = 1) → Function.mulSupport f ⊆ S := by
    intro f hf w hw
    by_contra h
    exact hw (hf w (hS w h).1 (hS w h).2)
  have e1 : ∀ z, finEps χ a z = ∏ w ∈ S, locEps χ w (a w) z := fun z =>
    finprod_eq_prod_of_mulSupport_subset _ (hsub _ fun w h0 h1 => by rw [h1]; exact locEps_eq_one χ h0 z)
  have e3 : (((discr E).natAbs * a.prod fun v k => Ideal.absNorm v.asIdeal ^ k : ℕ)) =
      ∏ w ∈ S, Ideal.absNorm w.asIdeal ^ (a w + diffExp w) := by
    rw [← absNorm_differentIdeal E (𝓞 E), absNorm_different_eq_prod S fun w hw => (hS w hw).1, Finsupp.prod,
      Finset.prod_subset (s₁ := a.support) (s₂ := S) ?_ ?_, ← Finset.prod_mul_distrib]
    · refine Finset.prod_congr rfl fun w _ => ?_
      rw [← pow_add, add_comm]
    · intro w hw
      simp only [hSdef, Set.Finite.mem_toFinset, Set.mem_union, Finset.mem_coe]
      exact Or.inr hw
    · intro w _ hw
      rw [Finsupp.notMem_support_iff.1 hw, pow_zero]
  rw [e1, e1, e3, ← prod_natCast_cpow, ← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun w _ => locEps_eq_mul χ w (a w) s

theorem norm_finEps_half {χ : HChar E} (hu : IsUnitary χ) {a : HeightOneSpectrum (𝓞 E) →₀ ℕ} (ha : ∀ w, ExpAt χ w (a w)) :
    ‖finEps χ a (1 / 2)‖ = 1 := by
  have hf := finite_mulSupport_locEps χ a (1 / 2)
  rw [finEps, finprod_eq_prod_of_mulSupport_subset _ hf.coe_toFinset.ge, norm_prod]
  exact Finset.prod_eq_one fun w _ => norm_locEps_half hu (ha w)

theorem norm_archEps {I : Type} [Fintype I] (n : I → ℤ) : ‖archEps n‖ = 1 := by
  simp [archEps]

end GlobalTheory.HeckeEpsAbs

namespace GlobalTheory.Published

open GlobalTheory.HeckeEpsAbs

theorem HeckeTateFunctionalEquation.abs (h : HeckeTateFunctionalEquation) : HeckeFunctionalEquationAbs := by
  intro E _ _ _ I _ φ hφ χ n a Λ Λ' hu hi hn ha hΛ hΛ'
  obtain ⟨Λ₀, Λ₀', h1, h2, h3⟩ := h E I φ hφ χ n a hu hi hn ha
  obtain rfl := hΛ.unique h1
  obtain rfl := hΛ'.unique h2
  refine ⟨archEps n * finEps χ a (1 / 2), ?_, fun s => ?_⟩
  · rw [norm_mul, norm_archEps, norm_finEps_half hu ha, one_mul]
  · rw [h3 s, finEps_eq χ a s]
    ring

end GlobalTheory.Published
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdaptedFrameEventuallyNearComplexPoint
section
open MeasureTheory Filter Topology GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.GoodTop
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff Matrix

set_option autoImplicit false

namespace GlobalTheory.GoodTop

theorem frame_eventually {F : Type} [Field F] {σ : F →+* ℂ} {X : Var F} {m : ℕ}
    (E : Fr (ratOf X) (fun _ : Unit => m) 0) {y : CxPts X.str σ} {A : Mat (fun _ : Unit => m) X.Fn}
    (hA : A ∈ E.S (under y)) : ∀ᶠ z in 𝓝 y, A ∈ E.S (under z) := by
  obtain ⟨U, B, hU, hB, hS⟩ := E.loc (under y)
  have hP := (hS _ hU A).1 hA
  have hreg : ∀ g : X.Fn, RegAt (under y) g → ∀ᶠ z in 𝓝 y, RegAt (under z) g := by
    intro g hg
    obtain ⟨W, hW, a, rfl⟩ := hg.exists_fnOf
    filter_upwards [(isOpen_ptsIn W).mem_nhds (mem_ptsIn.2 hW)] with z hz
    exact regAt_fnOf (mem_ptsIn.1 hz) _ a
  have hU' : ∀ᶠ z in 𝓝 y, under z ∈ U := by
    filter_upwards [(isOpen_ptsIn U).mem_nhds (mem_ptsIn.2 hU)] with z hz
    exact mem_ptsIn.1 hz
  have h1 : ∀ᶠ z in 𝓝 y, ∀ τ, (∀ i j, RegAt (under z) ((A * B⁻¹) τ i j)) ∧ RegAt (under z) ((A * B⁻¹) τ).det⁻¹ :=
    Filter.eventually_all.2 fun τ => (Filter.eventually_all.2 fun i => Filter.eventually_all.2 fun j =>
      hreg _ (mem_O_ratOf.1 ((hP τ).1 i j))).and (hreg _ (mem_O_ratOf.1 (hP τ).2.2.1))
  filter_upwards [hU', h1] with z hz hz1
  exact (hS _ hz A).2 fun τ => ⟨fun i j => mem_O_ratOf.2 ((hz1 τ).1 i j), (hP τ).2.1, mem_O_ratOf.2 (hz1 τ).2,
    fun i j hi => absurd hi (by simp)⟩

end GlobalTheory.GoodTop
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdeleQuotientCompactRepresentatives
section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.UnipDom

namespace GlobalTheory.AdeleCocompactExt

theorem exists_compact_adele_ext : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E], ∃ C : Set (AE F E), IsCompact C ∧ ∀ a : AE F E, ∃ α : E, a - inclR (F := F) (AF F) α ∈ C := by
  intro F E _ _ _ _ _
  classical
  haveI : IsModuleTopology (AF F) (AE F E) := GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.modTop
  haveI : ContinuousAdd (AE F E) := IsModuleTopology.toContinuousAdd (AF F) (AE F E)
  haveI : ContinuousSMul (AF F) (AE F E) := IsModuleTopology.toContinuousSMul (AF F) (AE F E)
  obtain ⟨K, hK, hK'⟩ := GlobalTheory.AdeleCocompact.exists_compact_adele F
  let b := Module.finBasis F E
  let B : Module.Basis (Fin (Module.finrank F E)) (AF F) (AE F E) := Algebra.TensorProduct.basis (AF F) b
  let φ : (Fin (Module.finrank F E) → AF F) → AE F E := fun c => ∑ i, c i • B i
  have hφ : Continuous φ := continuous_finset_sum _ fun i _ => (continuous_apply i).smul continuous_const
  refine ⟨φ '' Set.univ.pi (fun _ => K), (isCompact_univ_pi fun _ => hK).image hφ, fun a => ?_⟩
  choose x hx using fun i => hK' (B.repr a i)
  refine ⟨∑ i, x i • b i, fun i => B.repr a i - algebraMap F (AF F) (x i), fun i _ => hx i, ?_⟩
  have hB : ∀ i, B i = (1 : AF F) ⊗ₜ[F] b i := fun i => Algebra.TensorProduct.basis_apply _ _
  have hincl : inclR (F := F) (AF F) (∑ i, x i • b i) = ∑ i, algebraMap F (AF F) (x i) • B i := by
    simp only [inclR, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, map_sum, map_smul,
      Algebra.TensorProduct.includeRight_apply, hB, algebraMap_smul]
  simp only [φ, sub_smul, Finset.sum_sub_distrib, hincl]
  rw [B.sum_repr a]

end GlobalTheory.AdeleCocompactExt
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicSchwartzFixedBySchroedingerOpenFiniteSubgrStatement
section
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.SWQ GlobalTheory.ThetaTransform
open scoped Matrix Classical

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adelicSchwartz_fixed_by_schroedinger_open_finite_subgroup : ∀ (F : Type) [Field F] [NumberField F] (N : ℕ) [Invertible (2 : AF F)] (ψ : AddChar (AF F) ℂ), IsTotallyReal F → IsCharAF F ψ → ∀ Φ ∈ GlobalTheory.WeilM.schA F (Fin N), ∃ U : AddSubgroup (VA F N), IsOpen (U : Set (VA F N)) ∧ ∀ u ∈ U, inf u.1 = 0 → inf u.2 = 0 → GlobalTheory.WeilM.schr ψ u Φ = Φ := by
  first | exact @GlobalTheory.WeilLevel.schA_level | exact GlobalTheory.WeilLevel.schA_level | (intros; apply GlobalTheory.WeilLevel.schA_level <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicSymplecticTraceFormAlternatingSwap
section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF

namespace GlobalTheory.SymplSkew

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem herm_inv {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} (hJ : IsHermND σ J) (a b : Fin n) :
    σ (J⁻¹ b a) = J⁻¹ a b := by
  have hmap : J.map σ = Jᵀ := by ext i j; simp [Matrix.transpose_apply, hJ.1 j i]
  have hu : IsUnit J.det := isUnit_iff_ne_zero.mpr hJ.2
  have h1 : (J⁻¹).map σ * J.map σ = 1 := by
    rw [← Matrix.map_mul, Matrix.nonsing_inv_mul _ hu]; simp
  have h2 : (J⁻¹).map σ = (J⁻¹)ᵀ := by
    rw [Matrix.transpose_nonsing_inv, ← hmap]; exact (Matrix.inv_eq_left_inv h1).symm
  have := congrFun (congrFun h2 b) a
  rw [Matrix.map_apply] at this
  rw [this, Matrix.transpose_apply]

noncomputable def cEquiv (σ : E →ₐ[F] E) (hσ : ∀ e, σ (σ e) = e) : AEF F E ≃ₐ[AF F] AEF F E :=
  Algebra.TensorProduct.congr (AlgEquiv.refl) (AlgEquiv.ofAlgHom σ σ (AlgHom.ext fun e => hσ e) (AlgHom.ext fun e => hσ e))

theorem cEquiv_apply (σ : E →ₐ[F] E) (hσ : ∀ e, σ (σ e) = e) (z : AEF F E) : cEquiv σ hσ z = cAF σ z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a e => rfl
  | add x y hx hy => rw [map_add, map_add, hx, hy]

theorem cAF_cAF (σ : E →ₐ[F] E) (hσ : ∀ e, σ (σ e) = e) (z : AEF F E) : cAF σ (cAF σ z) = z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a e =>
    show (Algebra.TensorProduct.map (AlgHom.id F (AF F)) σ) ((Algebra.TensorProduct.map (AlgHom.id F (AF F)) σ) (a ⊗ₜ e)) = a ⊗ₜ e
    simp [hσ]
  | add x y hx hy => rw [map_add, map_add, hx, hy]

theorem cAF_incAF (σ : E →ₐ[F] E) (e : E) : cAF σ (incAF F E e) = incAF F E (σ e) := by
  show (Algebra.TensorProduct.map (AlgHom.id F (AF F)) σ) ((1 : AF F) ⊗ₜ e) = (1 : AF F) ⊗ₜ σ e
  simp

theorem cAF_hOF (σ : E →ₐ[F] E) (hσ : ∀ e, σ (σ e) = e) {nS nT : ℕ} {JS : Matrix (Fin nS) (Fin nS) E}
    {JT : Matrix (Fin nT) (Fin nT) E} (hS : IsHermND σ JS) (hT : IsHermND σ JT) (x y : WOF F E nS nT) :
    cAF σ (hOF σ JS JT x y) = hOF σ JS JT y x := by
  unfold hOF
  simp only [map_sum, map_mul, cAF_incAF, cAF_cAF σ hσ, herm_inv hS, hT.1]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun d _ => Finset.sum_congr rfl fun c _ => ?_
  ring

theorem symplOF_swap : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
    (∀ e, σ (σ e) = e) → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E),
    IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, σ ξ₀ = -ξ₀ → ∀ x y : WOF F E nS nT,
      symplOF σ JS JT ξ₀ y x = -symplOF σ JS JT ξ₀ x y := by
  intro F E _ _ _ _ _ σ hσ nS nT JS JT hS hT ξ₀ hξ x y
  unfold symplOF
  have hx : incAF F E ξ₀ = cAF σ (incAF F E (-ξ₀)) := by rw [cAF_incAF, ← hξ, hσ]
  rw [← cAF_hOF σ hσ hS hT x y]
  have key : incAF F E ξ₀ * cAF σ (hOF σ JS JT x y) = cEquiv σ hσ (incAF F E (-ξ₀) * hOF σ JS JT x y) := by
    rw [cEquiv_apply, map_mul, ← hx]
  rw [key, Algebra.trace_eq_of_algEquiv, map_neg, neg_mul, map_neg]

end GlobalTheory.SymplSkew
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicUnitaryLocallyCompactHausdorff
section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.UnipDom

namespace GlobalTheory.AdelicUnitaryTop

theorem lcsc_UA : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E),
    LocallyCompactSpace (UA σ J) ∧ SecondCountableTopology (UA σ J) ∧ T2Space (UA σ J) := by
  intro F E _ _ _ _ _ σ n J
  haveI := locallyCompact_adele F
  haveI := secondCountable_adele F
  haveI := t2Space_adeleRing_numberField F
  haveI : IsModuleTopology (AF F) (AE F E) := ⟨rfl⟩
  haveI : IsTopologicalRing (AE F E) := IsModuleTopology.isTopologicalRing (AF F) _
  obtain ⟨e⟩ := nonempty_homeomorph (F := F) (E := E) (AF F)
  haveI : LocallyCompactSpace (AE F E) := e.isClosedEmbedding.locallyCompactSpace
  haveI : SecondCountableTopology (AE F E) := e.secondCountableTopology
  haveI : T2Space (AE F E) := e.isEmbedding.t2Space
  haveI : LocallyCompactSpace (Matrix (Fin n) (Fin n) (AE F E)) :=
    inferInstanceAs (LocallyCompactSpace (Fin n → Fin n → AE F E))
  haveI : LocallyCompactSpace (Matrix (Fin n) (Fin n) (AE F E))ᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.isClosedEmbedding.locallyCompactSpace
  haveI : LocallyCompactSpace (GL (Fin n) (AE F E)) :=
    Units.isClosedEmbedding_embedProduct.locallyCompactSpace
  haveI : SecondCountableTopology (Matrix (Fin n) (Fin n) (AE F E)) :=
    inferInstanceAs (SecondCountableTopology (Fin n → Fin n → AE F E))
  haveI : SecondCountableTopology (Matrix (Fin n) (Fin n) (AE F E))ᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.isEmbedding.secondCountableTopology
  haveI : SecondCountableTopology (GL (Fin n) (AE F E)) :=
    Units.isEmbedding_embedProduct.secondCountableTopology
  haveI : T2Space (GL (Fin n) (AE F E)) := Units.isEmbedding_embedProduct.t2Space
  have hσ : Continuous (cA σ) := IsModuleTopology.continuous_of_linearMap (cA σ).toLinearMap
  have hc : IsClosed (UG (cA σ) (incM F J) : Set (GL (Fin n) (AE F E))) := by
    have hv : Continuous fun g : GL (Fin n) (AE F E) => (g : Matrix (Fin n) (Fin n) (AE F E)) :=
      Units.continuous_val
    exact isClosed_eq ((hv.matrix_transpose.matrix_mul continuous_const).matrix_mul
      (hv.matrix_map hσ)) continuous_const
  exact ⟨hc.isClosedEmbedding_subtypeVal.locallyCompactSpace,
    hc.isClosedEmbedding_subtypeVal.isEmbedding.secondCountableTopology,
    inferInstanceAs (T2Space (UG (cA σ) (incM F J)))⟩

end GlobalTheory.AdelicUnitaryTop
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdjointBlockOrthogonalityStatement
section
open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.FockAlg GlobalTheory.SteepMult
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adjoint_block_orthogonality : ∀ (R S : ℕ) (z w : NC R S), ∑ a : Ix R S, ∑ b : Ix R S, (if sameBlock a b then ∑ y : NC R S, (starRingEnd ℂ) (adP (Eab b a) y z) * adP (Eab b a) y w else 0) = if z = w then ((R + S : ℕ) : ℂ) else 0 := by
  first | exact @GlobalTheory.SteepMult.AdPCasimir.sum_adP_mul_adP | exact GlobalTheory.SteepMult.AdPCasimir.sum_adP_mul_adP | (intros; apply GlobalTheory.SteepMult.AdPCasimir.sum_adP_mul_adP <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AemeasurableChartOfLocallyContinuousDensity
section
open MeasureTheory Filter Topology GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.GoodTop
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff Matrix

namespace GlobalTheory.GoodTop

theorem aemeasurable_chart_of_locally_continuous {n : ℕ} {Y : Type} [TopologicalSpace Y]
    (e : OpenPartialHomeomorph Y (V n)) {S : Set Y} {d : Y → ℝ} (hS : IsOpen S)
    (h : ∀ y ∈ S, y ∈ e.source →
      ∃ g : V n → ℝ, ContinuousAt g (e y) ∧ ∀ᶠ z in 𝓝 y, d z = g (e z)) :
    AEMeasurable (fun v => d (e.symm v)) (volume.restrict (e.target ∩ e.symm ⁻¹' S)) := by
  have hO : IsOpen (e.target ∩ e.symm ⁻¹' S) := e.isOpen_inter_preimage_symm hS
  refine ContinuousOn.aemeasurable (fun v hv => ContinuousAt.continuousWithinAt ?_) hO.measurableSet
  obtain ⟨hvt, hvS⟩ := hv
  obtain ⟨g, hg, hev⟩ := h _ hvS (e.map_target hvt)
  rw [e.right_inv hvt] at hg
  refine hg.congr ?_
  have h1 := (e.continuousAt_symm hvt).eventually hev
  filter_upwards [h1, e.open_target.mem_nhds hvt] with w hw hwt
  rw [hw, e.right_inv hwt]

end GlobalTheory.GoodTop
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlmostLowerTriangularDiagMinorIsUnit
section
open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZH GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.FlagPush
open Classical

namespace GlobalTheory.FlagPush.AlmostLowUnits

theorem det_almost {K : Type} [Field K] {n : ℕ} (A : Matrix (Fin n) (Fin n) K) (a b : Fin n)
    (hb : (b : ℕ) = a + 1) (hab : A a b ≠ 0)
    (hl : ∀ i j : Fin n, i < j → ¬ (i = a ∧ j = b) → A i j = 0) :
    A.det = (A a a * A b b - A a b * A b a) * ∏ i ∈ (Finset.univ.erase a).erase b, A i i := by
  have hne : a ≠ b := fun h => by rw [h] at hb; omega
  have hlt : a < b := by rw [Fin.lt_iff_val_lt_val]; omega
  set c := A a a / A a b with hc
  set U := A.updateCol a (fun k => A k a + (-c) • A k b) with hU
  set N := U.submatrix id (Equiv.swap a b) with hN
  have hdetU : U.det = A.det := Matrix.det_updateCol_add_smul_self A hne (-c)
  have hdetN : N.det = - A.det := by
    rw [hN, Matrix.det_permute', Equiv.Perm.sign_swap hne, hdetU]; simp
  have hUapp : ∀ i j, U i j = if j = a then A i a - c * A i b else A i j := by
    intro i j
    rw [hU, Matrix.updateCol_apply]
    split_ifs <;> simp [sub_eq_add_neg]
  have hNapp : ∀ i j, N i j = U i (Equiv.swap a b j) := fun _ _ => rfl
  have htri : N.BlockTriangular OrderDual.toDual := by
    intro i j hij
    have hij' : i < j := OrderDual.toDual_lt_toDual.1 hij
    rw [hNapp]
    by_cases hja : j = a
    · rw [hja, Equiv.swap_apply_left, hUapp, if_neg hne.symm]
      rw [hja] at hij'
      exact hl i b (lt_trans hij' hlt) (fun h => (ne_of_lt hij') h.1)
    · by_cases hjb : j = b
      · rw [hjb, Equiv.swap_apply_right, hUapp, if_pos rfl]
        rw [hjb] at hij'
        by_cases hia : i = a
        · rw [hia, hc, div_mul_cancel₀ _ hab, sub_self]
        · have hia' : i < a := by
            have h1 : (i : ℕ) < b := hij'
            have h2 : (i : ℕ) ≠ a := fun h => hia (Fin.ext h)
            rw [Fin.lt_iff_val_lt_val]; omega
          rw [hl i a hia' (fun h => hia h.1), hl i b (lt_trans hia' hlt) (fun h => hia h.1)]; ring
      · rw [Equiv.swap_apply_of_ne_of_ne hja hjb, hUapp, if_neg hja]
        exact hl i j hij' (fun h => hjb h.2)
  have hprod := Matrix.det_of_lowerTriangular N htri
  have hmb : b ∈ Finset.univ.erase a := Finset.mem_erase.2 ⟨hne.symm, Finset.mem_univ _⟩
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ a), ← Finset.mul_prod_erase _ _ hmb] at hprod
  have hNa : N a a = A a b := by rw [hNapp, Equiv.swap_apply_left, hUapp, if_neg hne.symm]
  have hNb : N b b = A b a - c * A b b := by rw [hNapp, Equiv.swap_apply_right, hUapp, if_pos rfl]
  have hrest : ∏ i ∈ (Finset.univ.erase a).erase b, N i i = ∏ i ∈ (Finset.univ.erase a).erase b, A i i := by
    refine Finset.prod_congr rfl fun i hi => ?_
    have hib := (Finset.mem_erase.1 hi).1
    have hia := (Finset.mem_erase.1 (Finset.mem_erase.1 hi).2).1
    rw [hNapp, Equiv.swap_apply_of_ne_of_ne hia hib, hUapp, if_neg hia]
  rw [hNa, hNb, hrest, hdetN] at hprod
  have e : A a b * (A b a - c * A b b) = A a b * A b a - A a a * A b b := by
    rw [hc]; field_simp
  rw [← mul_assoc, e] at hprod
  linear_combination (-1 : K) * hprod

theorem units_of_det {K α : Type} [Field K] [DecidableEq α] (O : Subring K) {s : Finset α} (x : α → K) (y d : K)
    (hd : d = y * ∏ i ∈ s, x i) (hd0 : d ≠ 0) (hdi : d⁻¹ ∈ O) (hy : y ∈ O) (hx : ∀ i ∈ s, x i ∈ O) :
    (y ≠ 0 ∧ y⁻¹ ∈ O) ∧ ∀ i ∈ s, x i ≠ 0 ∧ (x i)⁻¹ ∈ O := by
  have hP : ∏ i ∈ s, x i ∈ O := O.prod_mem hx
  rw [hd] at hd0
  refine ⟨⟨left_ne_zero_of_mul hd0, ?_⟩, fun i hi => ?_⟩
  · have e : y⁻¹ = d⁻¹ * ∏ i ∈ s, x i := by
      rw [hd, mul_inv, mul_assoc, inv_mul_cancel₀ (right_ne_zero_of_mul hd0), mul_one]
    rw [e]; exact O.mul_mem hdi hP
  · have e : d = x i * (y * ∏ j ∈ s.erase i, x j) := by
      rw [hd, ← Finset.mul_prod_erase s x hi]; ring
    have h0 : x i * (y * ∏ j ∈ s.erase i, x j) ≠ 0 := by rw [← e, hd]; exact hd0
    refine ⟨left_ne_zero_of_mul h0, ?_⟩
    have e' : (x i)⁻¹ = d⁻¹ * (y * ∏ j ∈ s.erase i, x j) := by
      rw [e, mul_inv, mul_assoc, inv_mul_cancel₀ (right_ne_zero_of_mul h0), mul_one]
    rw [e']
    exact O.mul_mem hdi (O.mul_mem hy (O.prod_mem fun j hj => hx j (Finset.mem_of_mem_erase hj)))

end GlobalTheory.FlagPush.AlmostLowUnits

open GlobalTheory.FlagPush.AlmostLowUnits in

theorem GlobalTheory.FlagPush.almostLow_units : ∀ (ι : Type) (m : ι → ℕ) (τ : ι) (a b : Fin (m τ)), (b : ℕ) = a + 1 →
    ∀ (K : Type) [Field K] (O : Subring K) (g : Mat m K), AlmostLow τ a b g → Par 0 O g →
    (∀ x : Root m, x ≠ ⟨τ, a⟩ → x ≠ ⟨τ, b⟩ → g x.1 x.2 x.2 ≠ 0 ∧ (g x.1 x.2 x.2)⁻¹ ∈ O) ∧
      minor τ a b g ≠ 0 ∧ (minor τ a b g)⁻¹ ∈ O := by
  intro ι m τ a b hb K _ O g hg hp
  have hlτ : ∀ i j : Fin (m τ), i < j → ¬ (i = a ∧ j = b) → g τ i j = 0 := fun i j hij h =>
    hg.2.2 τ i j hij (fun h' => h ⟨eq_of_heq (Sigma.mk.inj h'.1).2, eq_of_heq (Sigma.mk.inj h'.2).2⟩)
  have hdetτ := det_almost (g τ) a b hb hg.2.1 hlτ
  have hmO : minor τ a b g ∈ O :=
    O.sub_mem (O.mul_mem ((hp τ).1 a a) ((hp τ).1 b b)) (O.mul_mem ((hp τ).1 a b) ((hp τ).1 b a))
  have hτ := units_of_det O (fun i => g τ i i) (minor τ a b g) ((g τ).det) hdetτ (hp τ).2.1 (hp τ).2.2.1 hmO
    (fun i _ => (hp τ).1 i i)
  refine ⟨?_, hτ.1⟩
  rintro ⟨σ, i⟩ h1 h2
  by_cases hσ : σ = τ
  · subst hσ
    have hia : i ≠ a := fun e => h1 (by rw [e])
    have hib : i ≠ b := fun e => h2 (by rw [e])
    exact hτ.2 i (Finset.mem_erase.2 ⟨hib, Finset.mem_erase.2 ⟨hia, Finset.mem_univ _⟩⟩)
  · have htri : (g σ).BlockTriangular OrderDual.toDual := fun i j hij =>
      hg.2.2 σ i j (OrderDual.toDual_lt_toDual.1 hij) (fun h' => hσ (congrArg Sigma.fst h'.1))
    have hdet := Matrix.det_of_lowerTriangular (g σ) htri
    have h := units_of_det O (s := Finset.univ) (fun j => g σ j j) 1 ((g σ).det) (by rw [one_mul]; exact hdet)
      (hp σ).2.1 (hp σ).2.2.1 O.one_mem (fun j _ => (hp σ).1 j j)
    exact h.2 i (Finset.mem_univ _)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BlockCasimirEigenvalueDropsOffBlockStatement
section
open scoped TensorProduct
open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.RealLift GlobalTheory.HoweR
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.blockCasimir_eigenvalue_drops_offBlock : ∀ (ι M : Type) [Fintype ι] [DecidableEq ι] [AddCommGroup M] [Module ℂ M] (s : ι → Bool) (F : ι → ι → Module.End ℂ M), ∀ (α β x ω : ℂ) (y : ι → M), IsGl F → (∀ a b, qop F α β a b = 0) → (∀ a, s a = false → y a = 0) → (∀ a, s a = true → ∑ b, F a b (y b) = x • y a) → (∀ a, cas s F (y a) = ω • y a) → ∀ j, s j = false → cas s F (∑ b, F j b (y b)) = (ω - 4 * x + 2 * α + ((Finset.univ.filter fun a => s a = true).card : ℂ) - ((Finset.univ.filter fun a => s a = false).card : ℂ)) • ∑ b, F j b (y b) := by
  first | exact @GlobalTheory.HoweR.cas_drop | exact GlobalTheory.HoweR.cas_drop | (intros; apply GlobalTheory.HoweR.cas_drop <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BlockCasimirEqRealCasimirStatement
section
open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.FockAlg GlobalTheory.SteepMult
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.block_casimir_eq_real_casimir : ∀ (R S : ℕ) (μ : Ix R S → ℚ), GlobalTheory.BlockReps.casVal μ = GlobalTheory.RealLift.casK μ := by
  first | exact @GlobalTheory.CasimirCoord.casVal_eq_casK | exact GlobalTheory.CasimirCoord.casVal_eq_casK | (intros; apply GlobalTheory.CasimirCoord.casVal_eq_casK <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MassBoundOfTamagawaUnitaryStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mass_bound_of_tamagawa_unitary : GlobalTheory.Published.TamagawaSpecialUnitary → GlobalTheory.UCls.MassBound := by
  first | exact @GlobalTheory.UCls.massBound_of_tamagawa | exact GlobalTheory.UCls.massBound_of_tamagawa | (intros; apply GlobalTheory.UCls.massBound_of_tamagawa <;> assumption)
end

