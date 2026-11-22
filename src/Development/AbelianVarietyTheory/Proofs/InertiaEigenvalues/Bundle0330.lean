import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0011
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0317
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0129
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0312
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0316
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0321
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0311
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0136
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormEqZpowOfMemMaxUnramifiedSubfield
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0154
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0004
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PeriodDiscExtensionTateElement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0325
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0012
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0011
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0006
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoeffZeroEqZeroIff
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PowMulMemLatIff
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0250
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0313
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsCyclotomicKernelFixedBasisWittTensorLattic

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContinuousCochainOfDeRhamCoboundary
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N GlobalTheory.Pst GlobalTheory.PMon TensorProduct Module
open scoped Formalism.Per

noncomputable section

open Formalism Formalism.MainNotions.LocalSituation GlobalTheory.Cyc GlobalTheory.ExpImage GlobalTheory.FundCont Filter Topology

namespace GlobalTheory.ContDR

theorem cont_dR : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (T : LocTied l P AI) (K : FinExt l) (V : Type) [AddCommGroup V] [Module ℚ_[l] V] [FiniteDimensional ℚ_[l] V] [TopologicalSpace V] [IsModuleTopology ℚ_[l] V] (ρ : Representation ℚ_[l] ↥(GK K) V), (∀ v : V, Continuous fun g => ρ g v) → ∀ (k : ℕ) (x : Fin k → V ⊗[ℚ_[l]] P.R.BdR) (β : Fin k → ↥(GK K) → ℚ_[l]), (∀ i, Continuous (β i)) → ∀ (x' : V ⊗[ℚ_[l]] P.R.BdR) (f : ↥(GK K) → V), (∀ g, f g ⊗ₜ[ℚ_[l]] (1 : P.R.BdR) = ∑ i, β i g • x i + (actVdR (P.PD K) ρ g x' - x')) → Continuous f := by
  intro l _ P AI T K V _ _ _ _ _ ρ hρ k x β hβ x' f hf
  have hV : ∀ φ : V →ₗ[ℚ_[l]] ℚ_[l], Continuous φ := fun φ =>
    IsModuleTopology.continuous_of_linearMap φ
  have key : ∀ φ : V →ₗ[ℚ_[l]] ℚ_[l], Continuous fun g => φ (f g) := by
    intro φ
    let Φ : V ⊗[ℚ_[l]] P.R.BdR →ₗ[ℚ_[l]] P.R.BdR :=
      (TensorProduct.lid ℚ_[l] P.R.BdR).toLinearMap ∘ₗ TensorProduct.map φ LinearMap.id
    have hΦ : ∀ v b, Φ (v ⊗ₜ b) = qB P (φ v) * b := by
      intro v b
      simp [Φ, Algebra.smul_def]
    have h1 : ∀ (y : V ⊗[ℚ_[l]] P.R.BdR) (i : Fin k), LatCont AI fun g => Φ (β i g • y) := by
      intro y i
      induction y using TensorProduct.induction_on with
      | zero => simpa using latCont_const AI 0
      | tmul v b =>
        simp only [TensorProduct.smul_tmul', hΦ]
        simpa using latCont_orbit AI T b ((hV φ).comp ((hβ i).smul continuous_const))
          (γ := fun _ => 1) continuous_const
      | add y y' ih ih' =>
        simp only [smul_add, map_add]
        exact ih.add AI ih'
    have h2 : ∀ y : V ⊗[ℚ_[l]] P.R.BdR, LatCont AI fun g => Φ (actVdR (P.PD K) ρ g y) := by
      intro y
      induction y using TensorProduct.induction_on with
      | zero => simpa using latCont_const AI 0
      | tmul v b =>
        have e : ∀ g : ↥(GK K), Φ (actVdR (P.PD K) ρ g (v ⊗ₜ b)) =
            qB P (φ (ρ g v)) * P.actQdR (g : GQ l) b := by
          intro g
          rw [← P.PD_actdR K g b, ← hΦ]
          rfl
        simp only [e]
        exact latCont_orbit AI T b ((hV φ).comp (hρ v)) continuous_subtype_val
      | add y y' ih ih' =>
        simp only [map_add]
        exact ih.add AI ih'
    apply continuous_of_latCont AI T
    have e : ∀ g, qB P (φ (f g)) =
        ∑ i, Φ (β i g • x i) + (Φ (actVdR (P.PD K) ρ g x') + -Φ x') := by
      intro g
      have := congrArg Φ (hf g)
      rwa [hΦ, mul_one, map_add, map_sum, map_sub, sub_eq_add_neg] at this
    simp only [e]
    exact (LatCont.sum AI _ _ fun i => h1 (x i) i).add AI ((h2 x').add AI (latCont_const AI _))
  let b := Module.finBasis ℚ_[l] V
  have : f = fun g => ∑ j, b.coord j (f g) • b j := by
    funext g
    simp [b.sum_repr]
  rw [this]
  haveI : ContinuousAdd V := IsModuleTopology.toContinuousAdd ℚ_[l] V
  haveI : ContinuousSMul ℚ_[l] V := IsModuleTopology.toContinuousSMul ℚ_[l] V
  exact continuous_finset_sum _ fun j _ => (key (b.coord j)).smul continuous_const

end GlobalTheory.ContDR
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContinuousGaloisCharacterFiltrationOne
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon TensorProduct
open scoped Formalism.Per

namespace GlobalTheory.LTChar

theorem char_cont : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (T : LocTied l P AI) (K : FinExt l) (x : P.R.B), P.ιB x ∈ Fil P 1 → P.ιB x ∉ Fil P 2 → ∀ (c : ↥(GK K) → ↥(MaximalUnramifiedExtension l)), (∀ g : ↥(GK K), P.actQ (g : GQ l) x = algebraMap ↥(MaximalUnramifiedExtension l) P.R.B (c g) * x) → Continuous fun g => ((c g : ↥(MaximalUnramifiedExtension l)) : Om l) := by
  intro l _ P AI T K x h1 h2 c hc
  obtain ⟨-, -, hsh, -, -, -, -, hact, -⟩ := GlobalTheory.PMon.bdR_tied l P AI T
  obtain ⟨S, θ, hS, -, hker, hOm, hθ⟩ := GlobalTheory.PMon.exists_theta_deRhamFilZero_surjective_alt l P AI T
  have hu0 : tz P (-1) * P.ιB x ∈ Fil P 0 := by
    have := (hsh 1 (-1) _).1 h1
    simpa using this
  have hu1 : tz P (-1) * P.ιB x ∉ Fil P 1 := by
    intro h
    apply h2
    rw [hsh 2 (-1)]
    simpa using h
  set u : S := ⟨tz P (-1) * P.ιB x, (hS _).2 hu0⟩ with hu
  have hy : θ u ≠ 0 := fun h => hu1 ((hker u).1 h)
  have key : ∀ g : ↥(GK K), (((c g : ↥(MaximalUnramifiedExtension l)) : Om l) : ℂ_[l]) =
      algebraMap ℚ_[l] ℂ_[l] ((P.χQ (g : GQ l) : ℚ_[l]ˣ) : ℚ_[l]) * Formalism.Per.σC (g : GQ l) (θ u) / θ u := by
    intro g
    obtain ⟨hg, hg'⟩ := hθ g u
    obtain ⟨ha, ha'⟩ := hOm (algebraMap ℚ_[l] (Om l) ((P.χQ (g : GQ l) : ℚ_[l]ˣ) : ℚ_[l]))
    obtain ⟨hb, hb'⟩ := hOm ((c g : ↥(MaximalUnramifiedExtension l)) : Om l)
    have e : (⟨_, ha⟩ : S) * ⟨_, hg⟩ = ⟨_, hb⟩ * u := by
      apply Subtype.ext
      show algebraMap (Om l) P.R.BdR _ * P.actQdR g (tz P (-1) * P.ιB x) = kd P (c g) * (tz P (-1) * P.ιB x)
      rw [map_mul, hact, ← iota_act, hc, map_mul, iota_kur, ← IsScalarTower.algebraMap_apply, ← mul_assoc, ← mul_assoc, ← mul_assoc,
        ← map_mul, ← Units.val_mul]
      simp only [zpow_neg, zpow_one, mul_inv_cancel, Units.val_one, map_one]
      ring
    have e' := congrArg θ e
    rw [map_mul θ, map_mul θ, ha', hb', hg'] at e'
    rw [eq_div_iff hy, ← e']
    rfl
  have hemb : Topology.IsEmbedding (fun y : Om l => (y : ℂ_[l])) :=
    UniformSpace.Completion.coe_isometry.isEmbedding
  refine hemb.continuous_iff.2 ?_
  have : ((fun y : Om l => (y : ℂ_[l])) ∘ fun g => ((c g : ↥(MaximalUnramifiedExtension l)) : Om l)) = _ := funext key
  rw [this]
  refine Continuous.div_const (Continuous.mul ?_ ?_) _
  · exact (continuous_algebraMap ℚ_[l] ℂ_[l]).comp
      ((GlobalTheory.Cyc.IsCyc.continuous P.χQ_cyc).comp continuous_subtype_val)
  · exact (orbit_cont (θ u)).comp continuous_subtype_val

end GlobalTheory.LTChar
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CyclotomicIntegersEqWittZetaSubOne
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct GlobalTheory.HWL GlobalTheory.Prism GlobalTheory.PrismS Polynomial
open scoped IntermediateField

namespace GlobalTheory.PrismS.Poly

variable {l : ℕ} [Fact l.Prime]

theorem mem_OL_of_norm_le (K : FinExt l) (y : ↥K.1) (h : ‖(y : Om l)‖ ≤ 1) : y ∈ OL K := by
  have hi : IsIntegral ℚ_[l] (y : Om l) := Algebra.IsIntegral.isIntegral _
  rw [← PadicAlgCl.spectralNorm_eq, spectralNorm, spectralValue_le_one_iff (minpoly.monic hi)] at h
  have hl : minpoly ℚ_[l] (y : Om l) ∈ Polynomial.lifts (algebraMap ℤ_[l] ℚ_[l]) := by
    rw [lifts_iff_coeff_lifts]
    exact fun n => ⟨⟨_, h n⟩, rfl⟩
  obtain ⟨q, hq, -, hm⟩ := lifts_and_degree_eq_and_monic hl (minpoly.monic hi)
  have h1 : IsIntegral ℤ_[l] (y : Om l) := ⟨q, hm, by
    rw [← aeval_def, ← aeval_map_algebraMap ℚ_[l], hq, minpoly.aeval]⟩
  exact (isIntegral_algHom_iff (K.1.val.restrictScalars ℤ_[l]) K.1.val.toRingHom.injective).1 h1

theorem norm_coeff_le (K : FinExt l) (N : ℕ) (π : Om l)
    (hπ : ‖π‖ = (l : ℝ) ^ (-(1 : ℝ) / (N : ℝ))) (p : (↥(K0 K))[X])
    (hd : p.natDegree < N) (h1 : ‖aeval π p‖ ≤ 1) (j : ℕ) :
    ‖((p.coeff j : ↥(K0 K)) : Om l)‖ ≤ 1 := by
  have hl1 : (1 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).one_lt
  have hl0 : (0 : ℝ) < l := by linarith
  have hN : (0 : ℝ) < N := by exact_mod_cast (Nat.zero_le _).trans_lt hd
  have key : ∀ i ∈ p.support, ∃ n : ℤ, ‖((p.coeff i : ↥(K0 K)) : Om l)‖ = (l : ℝ) ^ n ∧
      ‖p.coeff i • π ^ i‖ = (l : ℝ) ^ ((n : ℝ) - (i : ℝ) / N) := by
    intro i hi
    have h0 : ((p.coeff i : ↥(K0 K)) : Om l) ≠ 0 := by
      have := mem_support_iff.1 hi
      exact fun h => this (Subtype.ext h)
    obtain ⟨n, hn⟩ := GlobalTheory.UnramValue.norm_of_mem_unramified_subfield l K _ (p.coeff i).2 h0
    refine ⟨n, hn, ?_⟩
    change ‖((p.coeff i : ↥(K0 K)) : Om l) * π ^ i‖ = _
    rw [norm_mul, norm_pow, hn, hπ, ← Real.rpow_natCast, ← Real.rpow_mul hl0.le,
      ← Real.rpow_intCast, ← Real.rpow_add hl0]
    congr 1
    ring
  have hpw : Set.Pairwise (p.support : Set ℕ)
      (fun i k => ‖p.coeff i • π ^ i‖₊ ≠ ‖p.coeff k • π ^ k‖₊) := by
    intro i hi k hk hik h
    obtain ⟨n, -, hn⟩ := key i hi
    obtain ⟨m, -, hm⟩ := key k hk
    have h' : ‖p.coeff i • π ^ i‖ = ‖p.coeff k • π ^ k‖ := congrArg NNReal.toReal h
    rw [hn, hm] at h'
    have h2 := (Real.rpow_right_inj hl0 hl1.ne').1 h'
    have h3 : ((n - m) * N : ℝ) = i - k := by
      field_simp at h2
      linarith
    have h4 : ((n - m) * N : ℤ) = i - k := by exact_mod_cast h3
    have hi' : i < N := (le_natDegree_of_mem_supp i hi).trans_lt hd
    have hk' : k < N := (le_natDegree_of_mem_supp k hk).trans_lt hd
    have h5 : (i : ℤ) - k = 0 := by
      apply Int.eq_zero_of_abs_lt_dvd (m := N) ⟨n - m, by rw [← h4]; ring⟩
      rw [abs_lt]; constructor <;> omega
    omega
  by_cases hj : j ∈ p.support
  swap
  · rw [notMem_support_iff.1 hj]; simp
  have hs : ∑ i ∈ p.support, p.coeff i • π ^ i = aeval π p := by
    rw [aeval_eq_sum_range' (Nat.lt_succ_self _)]
    apply Finset.sum_subset supp_subset_range_natDegree_succ
    intro i _ hi
    rw [notMem_support_iff.1 hi, zero_smul]
  have h6 := IsUltrametricDist.nnnorm_sum_eq_sup_of_pairwise_ne hpw
  rw [hs] at h6
  have h7 := Finset.le_sup (f := fun i => ‖p.coeff i • π ^ i‖₊) hj
  rw [← h6] at h7
  obtain ⟨n, hn, hn'⟩ := key _ hj
  have h8 : ‖p.coeff j • π ^ j‖ ≤ ‖aeval π p‖ := h7
  replace h8 := (h8.trans h1).trans (Real.rpow_zero (l : ℝ)).ge
  rw [hn', Real.rpow_le_rpow_left_iff hl1] at h8
  have hj' : (j : ℝ) < N := by exact_mod_cast (le_natDegree_of_mem_supp j hj).trans_lt hd
  have h9 : (j : ℝ) / N < 1 := (div_lt_one hN).2 hj'
  have h10 : n < 1 := by
    have : (n : ℝ) < 1 := by linarith
    exact_mod_cast this
  rw [hn]
  exact zpow_le_one_of_nonpos₀ hl1.le (by omega)

theorem coe_eval₂ (K : FinExt l) (π : Om l) (t : OC l) (ht : (t : ℂ_[l]) = (π : ℂ_[l]))
    (r : (WK K)[X]) : ((r.eval₂ (intToOC (unr K)) t : OC l) : ℂ_[l]) =
      algebraMap (Om l) ℂ_[l] (aeval π (r.map ((OL (unr K)).val.toRingHom : WK K →+* ↥(K0 K)))) := by
  induction r using Polynomial.induction_on' with
  | add p q hp hq =>
    rw [eval₂_add, Polynomial.map_add, map_add, map_add, ← hp, ← hq]; rfl
  | monomial n a =>
    rw [eval₂_monomial, Polynomial.map_monomial, aeval_monomial, map_mul, map_pow]
    push_cast
    rw [ht]
    rfl

theorem exists_poly (K : FinExt l) (s : ℕ) (hs : 1 ≤ s) (ζ : Om l) (hζ : IsPrimitiveRoot ζ (l ^ s))
    (x : Om l) (hx : x ∈ Ks K s) :
    ∃ p : (↥(K0 K))[X], p.natDegree < l ^ (s - 1) * (l - 1) ∧ aeval (ζ - 1) p = x := by
  have hlp : l.Prime := Fact.out
  have hint : IsIntegral ↥(K0 K) ζ := Algebra.IsIntegral.isIntegral ζ
  rw [GlobalTheory.Cyc.Ks_eq_restrictScalars K s ζ hζ] at hx
  have hx' : x ∈ ((↥(K0 K))⟮ζ⟯).toSubalgebra := hx
  rw [IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic hint.isAlgebraic,
    Algebra.adjoin_singleton_eq_range_aeval] at hx'
  obtain ⟨q, rfl⟩ := hx'
  refine ⟨taylor 1 (q %ₘ minpoly ↥(K0 K) ζ), ?_, ?_⟩
  · rw [natDegree_taylor, ← Nat.totient_prime_pow hlp hs,
      ← natDegree_cyclotomic (l ^ s) ↥(K0 K), ← GlobalTheory.Cyc.minpoly_unramifiedSubfield_eq_cyclotomic K s hs ζ hζ]
    exact natDegree_modByMonic_lt _ (minpoly.monic hint) (minpoly.ne_one _ _)
  · rw [taylor_apply, aeval_comp]
    simp only [map_add, aeval_X, aeval_C, map_one, sub_add_cancel]
    exact aeval_modByMonic_eq_self_of_root (minpoly.aeval _ _)

theorem main : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ), 1 ≤ s → ∀ ζ : Om l, IsPrimitiveRoot ζ (l ^ s) → ∀ t : OC l, (t : ℂ_[l]) = ((ζ - 1 : Om l) : ℂ_[l]) → (∀ r : Polynomial (WK K), r.natDegree < l ^ (s - 1) * (l - 1) → r.eval₂ (intToOC (unr K)) t = 0 → r = 0) ∧ (K.1 ≤ Ks K s → ∀ x : ↥(OL K), ∃ r : Polynomial (WK K), r.eval₂ (intToOC (unr K)) t = intToOC K x) := by
  intro l _ K s hs ζ hζ t ht
  have hlp : l.Prime := Fact.out
  have hnorm : ‖ζ - 1‖ = (l : ℝ) ^ (-(1 : ℝ) / ((l ^ (s - 1) * (l - 1) : ℕ) : ℝ)) := by
    have h1 := GlobalTheory.Cyc.norm_primitiveRoot_sub_one l s hs (ζ : PadicComplex l)
      (hζ.map_of_injective (f := algebraMap (Om l) (PadicComplex l)) (RingHom.injective _))
    push_cast [Nat.cast_sub hlp.one_le]
    rw [← h1, ← PadicComplex.norm_extends]
    congr 1
    exact (map_sub (algebraMap (Om l) (PadicComplex l)) ζ 1).trans (by rw [map_one]; rfl)
  have hinj : Function.Injective ((OL (unr K)).val.toRingHom : WK K →+* ↥(K0 K)) :=
    Subtype.val_injective
  refine ⟨fun r hr h0 => ?_, fun hK x => ?_⟩
  · by_contra hne
    have h1 := coe_eval₂ K (ζ - 1) t ht r
    rw [h0] at h1
    refine GlobalTheory.Cyc.aeval_ne_zero_of_norm_eq K _ (ζ - 1) hnorm _
      ((Polynomial.map_ne_zero_iff hinj).2 hne) (natDegree_map_le.trans_lt hr) ?_
    exact (algebraMap (Om l) ℂ_[l]).injective (h1.symm.trans (map_zero _).symm)
  · obtain ⟨p, hp, hpx⟩ := exists_poly K s hs ζ hζ _ (hK (x : ↥K.1).2)
    have hc := norm_coeff_le K _ _ hnorm p hp (hpx ▸ norm_le_one_of_mem_OL K x)
    have hl : p ∈ Polynomial.lifts ((OL (unr K)).val.toRingHom : WK K →+* ↥(K0 K)) := by
      rw [lifts_iff_coeff_lifts]
      exact fun n => ⟨⟨_, mem_OL_of_norm_le (unr K) _ (hc n)⟩, rfl⟩
    obtain ⟨r, rfl⟩ := (mem_lifts _).1 hl
    refine ⟨r, Subtype.ext ?_⟩
    rw [coe_eval₂ K (ζ - 1) t ht r, hpx]
    rfl

end GlobalTheory.PrismS.Poly
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CyclotomicPowerSeriesDataLevIsExpansionAtZetaStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct GlobalTheory.HWL GlobalTheory.HWL.Cmp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cyclotomicPowerSeriesData_lev_isExpansionAtZeta : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K : FinExt l) (s : ℕ) (LL : FinExt l) (Γ : GamS P K s LL) (R : WSer Γ), ∀ (i : ZMod (Module.finrank ℚ_[l] ↥(K0 K))) (ζ : ↥LL.1), (∃ j : ℕ, IsPrimitiveRoot ζ (l ^ j)) → ∀ a : LetA ↥(OL LL) (Module.finrank ℚ_[l] ↥(K0 K)), IsExp ζ (toLL a i) (R.lev i ζ a) := by
  first | exact @GlobalTheory.HWL.LevExp.lev_isExp | exact GlobalTheory.HWL.LevExp.lev_isExp | (intros; apply GlobalTheory.HWL.LevExp.lev_isExp <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DeRhamPeriodRingFieldTPowFiltrationUnitsStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon TensorProduct
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.deRhamPeriodRing_field_tPow_filtration_units : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (T : LocTied l P AI), IsField P.R.BdR ∧ Function.Injective P.ιB ∧ (∀ (a b : ℤ) (x : P.R.BdR), x ∈ Fil P a ↔ tz P b * x ∈ Fil P (a + b)) ∧ (∀ x ∈ Fil P 0, x ∉ Fil P 1 → ∃ y ∈ Fil P 0, x * y = 1) ∧ (∀ x : P.R.BdR, x ≠ 0 → ∃ a : ℤ, x ∈ Fil P a ∧ x ∉ Fil P (a + 1)) ∧ (∀ (a b : ℤ) (x y : P.R.BdR), x ∈ Fil P a → y ∈ Fil P b → x * y ∈ Fil P (a + b)) ∧ (∀ (a : ℤ) (g : GQ l) (x : P.R.BdR), x ∈ Fil P a → P.actQdR g x ∈ Fil P a) ∧ (∀ (a : ℤ) (g : GQ l), P.actQdR g (tz P a) = algebraMap ℚ_[l] P.R.BdR ((P.χQ g ^ a : ℚ_[l]ˣ) : ℚ_[l]) * tz P a) ∧ (∀ a b : ℤ, tz P (a + b) = tz P a * tz P b) ∧ tz P 0 = 1 ∧ tz P 1 = P.ιB P.tB := by
  first | exact @GlobalTheory.PMon.bdR_tied | exact GlobalTheory.PMon.bdR_tied | (intros; apply GlobalTheory.PMon.bdR_tied <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DeRhamTrivialRationalCocycleRestrictionScalars
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon TensorProduct
open scoped Formalism.Per

noncomputable section

open Matrix

namespace GlobalTheory.PMon.DRvec

theorem blockDiag_mulVec {R : Type*} [CommRing R] {n o : Type} [Fintype n] [Fintype o] [DecidableEq o]
    (M : o → Matrix n n R) (v : n × o → R) (i : n) (m : o) :
    (Matrix.blockDiagonal M *ᵥ v) (i, m) = (M m *ᵥ fun j => v (j, m)) i := by
  simp [Matrix.mulVec, dotProduct, Matrix.blockDiagonal_apply, Fintype.sum_prod_type, ite_mul, Finset.sum_ite_eq]

theorem kd_q {l : ℕ} [Fact l.Prime] (P : LocPrime l) (q : ℚ_[l]) :
    kd P (algebraMap ℚ_[l] ↥(MaximalUnramifiedExtension l) q) = algebraMap ℚ_[l] P.R.BdR q := by
  show algebraMap (Om l) P.R.BdR (algebraMap ↥(MaximalUnramifiedExtension l) (Om l) (algebraMap ℚ_[l] ↥(MaximalUnramifiedExtension l) q)) = _
  rw [← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply]

theorem ratCocycle_trivial : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (n : Type) [Fintype n] [DecidableEq n] (K : FinExt l) (r : ℕ)
    (σ : ↥(GK K) →* GL n ↥(MaximalUnramifiedExtension l)) (ρ₀ : ↥(GK K) →* GL (n × Fin r) ℚ_[l]) (p : GL (n × Fin r) ↥(MaximalUnramifiedExtension l))
    (c : ↥(GK K) → n → ↥(MaximalUnramifiedExtension l)) (c₀ : ↥(GK K) → n × Fin r → ℚ_[l]),
    (∀ i j, (((p : Matrix (n × Fin r) (n × Fin r) ↥(MaximalUnramifiedExtension l)) i j : ↥(MaximalUnramifiedExtension l)) : Om l) ∈ K.1) →
    (∀ g, (p : Matrix (n × Fin r) (n × Fin r) ↥(MaximalUnramifiedExtension l)) *
          (ρ₀ g : Matrix (n × Fin r) (n × Fin r) ℚ_[l]).map (algebraMap ℚ_[l] ↥(MaximalUnramifiedExtension l)) =
        Matrix.blockDiagonal (fun m : Fin r => (σ g : Matrix n n ↥(MaximalUnramifiedExtension l)).map (fr l m)) *
          (p : Matrix (n × Fin r) (n × Fin r) ↥(MaximalUnramifiedExtension l))) →
    (∀ g, (p : Matrix (n × Fin r) (n × Fin r) ↥(MaximalUnramifiedExtension l)).mulVec (fun x => algebraMap ℚ_[l] ↥(MaximalUnramifiedExtension l) (c₀ g x)) =
            fun x => fr l x.2 (c g x.1)) →
    (∀ m : ℕ, ∃ b : n → P.R.BdR, ∀ g : ↥(GK K), (fun i => kd P (fr l m (c g i))) =
      (matD P σ m g).mulVec (fun i => P.actQdR (g : GQ l) (b i)) - b) →
    ∃ β : n × Fin r → P.R.BdR, ∀ g : ↥(GK K), (fun x => algebraMap ℚ_[l] P.R.BdR (c₀ g x)) =
      ((ρ₀ g : Matrix (n × Fin r) (n × Fin r) ℚ_[l]).map (algebraMap ℚ_[l] P.R.BdR)).mulVec
        (fun x => P.actQdR (g : GQ l) (β x)) - β := by
  intro l _ P n _ _ K r σ ρ₀ p c c₀ hp hconj hpc hdr
  choose b hb using hdr
  let pG : GL (n × Fin r) P.R.BdR := Matrix.GeneralLinearGroup.map (kd P) p
  let β' : n × Fin r → P.R.BdR := fun x => b x.2 x.1
  have hinvmul : ((pG⁻¹ : GL (n × Fin r) P.R.BdR) : Matrix (n × Fin r) (n × Fin r) P.R.BdR) *
      (pG : Matrix (n × Fin r) (n × Fin r) P.R.BdR) = 1 := pG.inv_mul
  have hmulinv : (pG : Matrix (n × Fin r) (n × Fin r) P.R.BdR) *
      ((pG⁻¹ : GL (n × Fin r) P.R.BdR) : Matrix (n × Fin r) (n × Fin r) P.R.BdR) = 1 := pG.mul_inv
  have hpG : ∀ i j, (pG : Matrix (n × Fin r) (n × Fin r) P.R.BdR) i j =
      kd P ((p : Matrix (n × Fin r) (n × Fin r) ↥(MaximalUnramifiedExtension l)) i j) := fun i j => rfl
  refine ⟨((pG⁻¹ : GL (n × Fin r) P.R.BdR) : Matrix (n × Fin r) (n × Fin r) P.R.BdR) *ᵥ β', fun g => ?_⟩
  set pinv := ((pG⁻¹ : GL (n × Fin r) P.R.BdR) : Matrix (n × Fin r) (n × Fin r) P.R.BdR) with hpinv
  set pM := (pG : Matrix (n × Fin r) (n × Fin r) P.R.BdR) with hpM
  set BD := Matrix.blockDiagonal (fun m : Fin r => matD P σ m g) with hBD
  set R0 := (ρ₀ g : Matrix (n × Fin r) (n × Fin r) ℚ_[l]).map (algebraMap ℚ_[l] P.R.BdR) with hR0

  have hfix : ∀ i j, P.actQdR (g : GQ l) (pinv i j) = pinv i j := by
    let φ : P.R.BdR →+* P.R.BdR := (P.actQdR (g : GQ l)).toAlgHom.toRingHom
    have h1 : Matrix.GeneralLinearGroup.map φ pG = pG := by
      ext i j
      show φ (kd P _) = kd P _
      exact act_kd P g (hp i j)
    have h2 : Matrix.GeneralLinearGroup.map φ pG⁻¹ = pG⁻¹ := by rw [map_inv, h1]
    intro i j
    exact congrArg (fun A : GL (n × Fin r) P.R.BdR => (A : Matrix (n × Fin r) (n × Fin r) P.R.BdR) i j) h2
  have hactv : (fun x => P.actQdR (g : GQ l) ((pinv *ᵥ β') x)) = pinv *ᵥ (fun x => P.actQdR (g : GQ l) (β' x)) := by
    funext x
    simp only [Matrix.mulVec, dotProduct, map_sum, map_mul, hfix]

  have hd : pM * R0 = BD * pM := by
    have h1 : pM = (p : Matrix (n × Fin r) (n × Fin r) ↥(MaximalUnramifiedExtension l)).map (kd P) := rfl
    have h2 : R0 = ((ρ₀ g : Matrix (n × Fin r) (n × Fin r) ℚ_[l]).map (algebraMap ℚ_[l] ↥(MaximalUnramifiedExtension l))).map (kd P) := by
      ext i j; simp [hR0, kd_q]
    have h3 : BD = (Matrix.blockDiagonal fun m : Fin r => (σ g : Matrix n n ↥(MaximalUnramifiedExtension l)).map (fr l m)).map (kd P) := by
      rw [hBD, Matrix.blockDiagonal_map _ _ (map_zero (kd P))]
      rfl
    rw [h1, h2, h3, ← Matrix.map_mul, ← Matrix.map_mul, hconj g]
  have hR : R0 * pinv = pinv * BD := by
    calc R0 * pinv = pinv * (pM * R0) * pinv := by rw [← Matrix.mul_assoc, hinvmul, Matrix.one_mul]
    _ = pinv * (BD * pM) * pinv := by rw [hd]
    _ = pinv * BD := by rw [Matrix.mul_assoc, Matrix.mul_assoc, hmulinv, Matrix.mul_one]
  have hvec : (fun x : n × Fin r => kd P (fr l x.2 (c g x.1))) = pM *ᵥ fun x => algebraMap ℚ_[l] P.R.BdR (c₀ g x) := by
    funext x
    have h := congrArg (fun v => kd P (v x)) (hpc g)
    simp only [Matrix.mulVec, dotProduct] at h ⊢
    rw [← h, map_sum]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [map_mul, kd_q, hpG]
  have hbt : (fun x : n × Fin r => kd P (fr l x.2 (c g x.1))) = BD *ᵥ (fun x => P.actQdR (g : GQ l) (β' x)) - β' := by
    funext ⟨i, m⟩
    rw [Pi.sub_apply, hBD, blockDiag_mulVec]
    exact congrFun (hb m g) i
  rw [hactv, Matrix.mulVec_mulVec, hR, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_sub, ← hbt, hvec, Matrix.mulVec_mulVec,
    hinvmul, Matrix.one_mulVec]

end GlobalTheory.PMon.DRvec

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DoublingArithStep
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc ValuativeRel GroundTheory.LocalField GlobalTheory.PMon.Ram

namespace GlobalTheory.PMon.Ram

theorem doublingArith_step (V : ℕ → ℕ → ℕ) (E k : ℕ) (hE : 0 < E)
    (h1 : ∀ j, 1 ≤ j → j + 1 ≤ 8 → min (2 * V k (k + j)) (V k (k + j) + E) ≤ V k (k + j + 1))
    (h2 : V k (k + 8) ≤ 6 * E)
    (h3 : V k (k + 3) ≤ V k (k + 2) + V (k + 2) (k + 3)) :
    V k (k + 1) < E ∧ 2 * V k (k + 1) ≤ V (k + 2) (k + 3) := by
  have e1 := h1 1 le_rfl (by norm_num)
  have e2 := h1 2 (by norm_num) (by norm_num)
  have e3 := h1 3 (by norm_num) (by norm_num)
  have e4 := h1 4 (by norm_num) (by norm_num)
  have e5 := h1 5 (by norm_num) (by norm_num)
  have e6 := h1 6 (by norm_num) (by norm_num)
  have e7 := h1 7 (by norm_num) (by norm_num)
  rw [show k + 1 + 1 = k + 2 by ring] at e1
  rw [show k + 2 + 1 = k + 3 by ring] at e2
  rw [show k + 3 + 1 = k + 4 by ring] at e3
  rw [show k + 4 + 1 = k + 5 by ring] at e4
  rw [show k + 5 + 1 = k + 6 by ring] at e5
  rw [show k + 6 + 1 = k + 7 by ring] at e6
  rw [show k + 7 + 1 = k + 8 by ring] at e7
  rw [min_le_iff] at e1 e2 e3 e4 e5 e6 e7
  omega

theorem doublingArith : ∀ (V : ℕ → ℕ → ℕ) (E T g : ℕ), 0 < E →
    (∀ k ≤ 2 * T, ∀ j, 1 ≤ j → j + 1 ≤ 8 → min (2 * V k (k + j)) (V k (k + j) + E) ≤ V k (k + j + 1)) →
    (∀ k ≤ 2 * T, V k (k + 8) ≤ 6 * E) →
    (∀ k, V k (k + 3) ≤ V k (k + 2) + V (k + 2) (k + 3)) → g ≤ V 0 1 → 2 ^ T * g < E := by
  intro V E T g hE h1 h2 h3 hg
  have step : ∀ k, k ≤ 2 * T → V k (k + 1) < E ∧ 2 * V k (k + 1) ≤ V (k + 2) (k + 3) :=
    fun k hk => doublingArith_step V E k hE (h1 k hk) (h2 k hk) (h3 k)
  have ind : ∀ i, i ≤ T → 2 ^ i * g ≤ V (2 * i) (2 * i + 1) := by
    intro i
    induction i with
    | zero => intro _; simpa using hg
    | succ n ih =>
      intro hn
      have hs := (step (2 * n) (by omega)).2
      have ih' := ih (by omega)
      rw [show 2 * (n + 1) = 2 * n + 2 by ring, show 2 * n + 2 + 1 = 2 * n + 3 by ring, pow_succ]
      calc 2 ^ n * 2 * g = 2 * (2 ^ n * g) := by ring
        _ ≤ 2 * V (2 * n) (2 * n + 1) := Nat.mul_le_mul_left 2 ih'
        _ ≤ V (2 * n + 2) (2 * n + 3) := hs
  exact lt_of_le_of_lt (ind T le_rfl) (step (2 * T) le_rfl).1

end GlobalTheory.PMon.Ram
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EtaleComparisonPiAdicFiltrationModEllStatement
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc GlobalTheory.Decompl
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.etaleComparison_piAdic_filtration_mod_ell : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL) (W : Wach P K LL) (E : EtSit P AI K s LL h W), (∀ (m : ℕ) (e : W.EE), NearPi AI LL s m (E.tie.ioE e) → ∃ (a : LetA ↥(OL LL) (Module.finrank ℚ_[l] ↥(K0 K))) (e' : W.EE), e = algebraMap (LetA ↥(OL LL) (Module.finrank ℚ_[l] ↥(K0 K))) W.EE (letπ ^ m * a) + (l : W.EE) * e') ∧ ∀ (e : W.EE) (r : RW LL), E.tie.ioE e = (l : RW LL) * r → ∃ e' : W.EE, e = (l : W.EE) * e' := by
  first | exact @GlobalTheory.Decompl.near_ioE | exact GlobalTheory.Decompl.near_ioE | (intros; apply GlobalTheory.Decompl.near_ioE <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsCoeffTensorAcrisWithFrobeniusGaloisStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct GlobalTheory.HWL
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_coeffTensorAcris_with_frobenius_galois : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ (LL : FinExt l) (β : RA LL →+* ↥LL.1 ⊗[ℚ_[l]] P.R.B), IsBeta AI β → ∃ (A : Type) (_ : CommRing A) (b : RA LL →+* A) (κ : A →+* ↥LL.1 ⊗[ℚ_[l]] P.R.B) (φ : A →+* A) (γ : GQ l → (A →+* A)) (t : A), GlobalTheory.Decompl.LAdic.Good l A ∧ ((∀ y, κ (b y) = β y) ∧ (∀ o w, φ (b (o ⊗ₜ[ℤ_[l]] w)) = b (o ⊗ₜ[ℤ_[l]] WittVector.frobenius w)) ∧ (∀ x, κ (φ x) = Algebra.TensorProduct.map (AlgHom.id ℚ_[l] ↥LL.1) P.φB (κ x)) ∧ (∀ g o w, γ g (b (o ⊗ₜ[ℤ_[l]] w)) = b (o ⊗ₜ[ℤ_[l]] AI.actW g w)) ∧ (∀ g x, κ (γ g x) = Algebra.TensorProduct.map (AlgHom.id ℚ_[l] ↥LL.1) (P.actQ g).toAlgHom (κ x)) ∧ κ t = (1 : ↥LL.1) ⊗ₜ[ℚ_[l]] P.tB) ∧ (∀ s : ℕ, ∃ d : ℕ, 0 < d ∧ (l : A) ∣ b ((1 : ↥(OL LL)) ⊗ₜ[ℤ_[l]] (WittVector.teichmuller l (AI.εroot s) - 1)) ^ d) ∧ (∀ r : ℕ, ∃ N : ℕ, ∀ n ≥ N, ∃ u z : A, ((n.factorial : ℕ) : A) * u = ∑ k ∈ Finset.range n, (-1) ^ k * ((n.factorial / (k + 1) : ℕ) : A) * b ((1 : ↥(OL LL)) ⊗ₜ[ℤ_[l]] AI.μ) ^ (k + 1) ∧ t - u = (l : A) ^ r * z) ∧ ∀ (ι : ↥LL.1 →ₐ[ℚ_[l]] P.R.BdR) (m : ℕ), ∃ C : ℕ, ∀ y : A, (l : P.R.BdR) ^ C * Algebra.TensorProduct.productMap ι P.ιB (κ y) ∈ GlobalTheory.ExpImage.Lat AI m 0 := by
  first | exact @GlobalTheory.HWLCris.exists_tensor_acris | exact GlobalTheory.HWLCris.exists_tensor_acris | (intros; apply GlobalTheory.HWLCris.exists_tensor_acris <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsCongruenceFiltrationGaloisRepStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_congruenceFiltration_galoisRep : ∀ (l : ℕ) [Fact l.Prime] (n : Type) [Fintype n] [DecidableEq n] (K : FinExt l) (ρ : ↥(GK K) →* GL n ℚ_[l]), (∀ i j, Continuous fun g => (ρ g : Matrix n n ℚ_[l]) i j) → ∃ N : ℕ → Subgroup ↥(GK K), (∀ k g, g ∈ N k ↔ ∀ i j, ‖((ρ g : Matrix n n ℚ_[l]) - 1) i j‖ ≤ (l : ℝ) ^ (-((k : ℤ) + 2))) ∧ Antitone N ∧ (∀ k, IsOpen (N k : Set ↥(GK K))) ∧ (∀ k g, g ∈ N k → g ^ l ∈ N (k + 1)) ∧ (∀ k g, g ∈ N 0 → g ^ l ∈ N (k + 1) → g ∈ N k) ∧ ∀ g, (∀ k, g ∈ N k) → ρ g = 1 := by
  first | exact @GlobalTheory.congrFiltration | exact GlobalTheory.congrFiltration | (intros; apply GlobalTheory.congrFiltration <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsCyclotomicFrobeniusTwistedValueEqPowMulStatement
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc GlobalTheory.ExpImage
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_cyclotomicFrobeniusTwistedValue_eq_pow_mul : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K : FinExt l) (s e : ℕ), 1 ≤ s → ∀ α : Om l, α ∈ Ks K s → ‖α‖ ≤ 1 → ∃ (lam : ℕ → ↥(K0 K)) (d : ↥(K0 K)), (∀ a, ‖(lam a : Om l)‖ ≤ 1) ∧ ‖(d : Om l)‖ ≤ 1 ∧ d - (l : ↥(K0 K)) ^ e * frK P K d = (frK P K ^ s) (∑ a ∈ primeTo l s, lam a) ∧ cycVal P K s e lam d = (l : Om l) ^ ((e + 1) * (s - 1)) * α := by
  first | exact @GlobalTheory.ExpImage.exists_cycVal_eq_pow_mul | exact GlobalTheory.ExpImage.exists_cycVal_eq_pow_mul | (intros; apply GlobalTheory.ExpImage.exists_cycVal_eq_pow_mul <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsCyclotomicKernelFixedBasisWittTensorLatticStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct GlobalTheory.HWL
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_cyclotomicKernelFixedBasis_wittTensorLattice : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), FaithH AI → ∀ (K LL : FinExt l) (T : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)), ∃ e : Module.Basis (Fin (Module.finrank ↥(OL LL) ↥T.L.T)) (RW LL) (TW (RW LL) T), FixBasis AI T e := by
  first | exact @GlobalTheory.HWL.FixedBasis.main | exact GlobalTheory.HWL.FixedBasis.main | (intros; apply GlobalTheory.HWL.FixedBasis.main <;> assumption)
end

