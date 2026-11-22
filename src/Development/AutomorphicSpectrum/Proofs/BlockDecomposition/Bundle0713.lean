import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0699
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0515
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0915
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0522
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0539
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0026
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0058
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0580
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle0042
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0701
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0700
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0702
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0703
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0705
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0704
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0694
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0508
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.LocalComparisonSplitting.EulerFactorLevels.LocCompareSplit
import Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinContinuation.DictInf
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalHypothesesHold
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0689
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.Bundle0005

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteKTypeDecomposition
section
noncomputable section

namespace GlobalTheory.CompanionTheory.SiegelRep

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl PositivityTheory.RgEis GlobalTheory.CompanionTheory.SiegelFrame

section Rep

variable {G : Type} [Group G] {K : Subgroup G} {V : Submodule ℂ (G → ℂ)}

def rt (hV : ∀ v ∈ V, ∀ k : K, (fun x => v (x * (k : G))) ∈ V) : K →* Module.End ℂ V where
  toFun k :=
    { toFun := fun v => ⟨fun x => v.1 (x * (k : G)), hV v.1 v.2 k⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  map_one' := by
    apply LinearMap.ext
    intro v
    apply Subtype.ext
    funext x
    simp
  map_mul' a b := by
    apply LinearMap.ext
    intro v
    apply Subtype.ext
    funext x
    simp [mul_assoc]

theorem rt_apply (hV : ∀ v ∈ V, ∀ k : K, (fun x => v (x * (k : G))) ∈ V) (k : K) (v : V) (x : G) :
    (rt hV k v).1 x = v.1 (x * (k : G)) := rfl

variable [FiniteDimensional ℂ V]

def mat (hV : ∀ v ∈ V, ∀ k : K, (fun x => v (x * (k : G))) ∈ V) (k : K) :
    Matrix (Fin (Module.finrank ℂ V)) (Fin (Module.finrank ℂ V)) ℂ :=
  LinearMap.toMatrix (Module.finBasis ℂ V) (Module.finBasis ℂ V) (rt hV k)

theorem mat_mul (hV : ∀ v ∈ V, ∀ k : K, (fun x => v (x * (k : G))) ∈ V) (a b : K) :
    mat hV (a * b) = mat hV a * mat hV b := by
  simp only [mat, map_mul]
  exact LinearMap.toMatrix_mul _ _ _

theorem mat_one (hV : ∀ v ∈ V, ∀ k : K, (fun x => v (x * (k : G))) ∈ V) : mat hV 1 = 1 := by
  simp only [mat, map_one]
  exact LinearMap.toMatrix_one _

def rho (hV : ∀ v ∈ V, ∀ k : K, (fun x => v (x * (k : G))) ∈ V) :
    K →* ((Fin (Module.finrank ℂ V) → ℂ) →L[ℂ] (Fin (Module.finrank ℂ V) → ℂ)) where
  toFun k := LinearMap.toContinuousLinearMap (Matrix.toLin' (mat hV k⁻¹)ᵀ)
  map_one' := by
    apply ContinuousLinearMap.ext
    intro a
    simp [mat_one]
  map_mul' a b := by
    apply ContinuousLinearMap.ext
    intro x
    simp [mul_inv_rev, mat_mul, Matrix.transpose_mul, Matrix.mulVec_mulVec]

theorem rho_apply (hV : ∀ v ∈ V, ∀ k : K, (fun x => v (x * (k : G))) ∈ V) (k : K)
    (a : Fin (Module.finrank ℂ V) → ℂ) (i : Fin (Module.finrank ℂ V)) :
    rho hV k a i = ∑ j, (Module.finBasis ℂ V).repr (rt hV k⁻¹ (Module.finBasis ℂ V i)) j * a j := by
  change ((mat hV k⁻¹)ᵀ *ᵥ a) i = _
  simp [Matrix.mulVec, dotProduct, mat, LinearMap.toMatrix_apply]

theorem sum_repr_apply (z : V) (x : G) :
    ∑ j, (Module.finBasis ℂ V).repr z j * (Module.finBasis ℂ V j).1 x = z.1 x := by
  have h := congrArg (fun y : V => y.1 x) ((Module.finBasis ℂ V).sum_repr z)
  simp only [AddSubmonoidClass.coe_finset_sum, Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply,
    smul_eq_mul] at h
  exact h

def w₀ (V : Submodule ℂ (G → ℂ)) [FiniteDimensional ℂ V] : Fin (Module.finrank ℂ V) → ℂ :=
  fun j => (Module.finBasis ℂ V j).1 1

theorem rho_w₀ (hV : ∀ v ∈ V, ∀ k : K, (fun x => v (x * (k : G))) ∈ V) (k : K)
    (i : Fin (Module.finrank ℂ V)) : rho hV k (w₀ V) i = (Module.finBasis ℂ V i).1 ((k : G)⁻¹) := by
  rw [rho_apply]
  simp only [w₀]
  rw [sum_repr_apply, rt_apply]
  simp

end Rep

section Cont

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] {K : Subgroup G}
  {V : Submodule ℂ (G → ℂ)} [FiniteDimensional ℂ V]

def evl (V : Submodule ℂ (G → ℂ)) (x : G) : Module.Dual ℂ V := (LinearMap.proj x).comp V.subtype

theorem span_evl : Submodule.span ℂ (Set.range (evl V)) = ⊤ := by
  have h : (Submodule.span ℂ (Set.range (evl V))).dualCoannihilator = ⊥ := by
    rw [eq_bot_iff]
    intro v hv
    rw [Submodule.mem_dualCoannihilator] at hv
    have : v = 0 := by
      apply Subtype.ext
      funext x
      exact hv _ (Submodule.subset_span ⟨x, rfl⟩)
    simp [this]
  have h2 := Subspace.dualCoannihilator_dualAnnihilator_eq
    (W := Submodule.span ℂ (Set.range (evl V)))
  rw [h] at h2
  simpa using h2.symm

theorem cont_coef (hV : ∀ v ∈ V, ∀ k : K, (fun x => v (x * (k : G))) ∈ V)
    (hc : ∀ v ∈ V, Continuous v) (ℓ : Module.Dual ℂ V) (v : V) :
    Continuous fun k : K => ℓ (rt hV k⁻¹ v) := by
  have hℓ : ℓ ∈ Submodule.span ℂ (Set.range (evl V)) := by
    rw [span_evl]
    trivial
  induction hℓ using Submodule.span_induction with
  | mem ℓ h =>
    obtain ⟨x, rfl⟩ := h
    have h1 : Continuous fun k : K => x * (((k⁻¹ : K)) : G) :=
      continuous_const.mul (continuous_subtype_val.comp continuous_inv)
    exact (hc v.1 v.2).comp h1
  | zero => simpa using continuous_const
  | add a b _ _ ha hb => exact ha.add hb
  | smul a ℓ _ h => exact continuous_const.mul h

theorem rho_cont (hV : ∀ v ∈ V, ∀ k : K, (fun x => v (x * (k : G))) ∈ V)
    (hc : ∀ v ∈ V, Continuous v) : Continuous (rho hV) := by
  rw [continuous_clm_apply]
  intro a
  refine continuous_pi fun i => ?_
  simp only [rho_apply]
  refine continuous_finset_sum _ fun j _ => ?_
  exact (cont_coef hV hc ((Module.finBasis ℂ V).coord j) _).mul continuous_const

end Cont

theorem ch_one {G : Type} [Group G] [TopologicalSpace G] {Γ P : Subgroup G} {c : G → ℂ}
    (h : IsCh Γ P c) : c 1 = 1 := by
  have h1 := h.mul 1 P.one_mem 1 P.one_mem
  have h2 := h.norm 1 P.one_mem
  have h0 : c 1 ≠ 0 := by
    intro h0
    simp [h0] at h2
  rw [mul_one] at h1
  exact mul_left_cancel₀ h0 (by rw [mul_one]; exact h1.symm)

theorem exists_rep : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (Γ K P : Subgroup G) (c : G → ℂ) (η : G → ℝ), IsCh Γ P c → (∀ r ∈ P, r ∈ K → η r = 0) → (∀ p ∈ P, ∀ q ∈ P, η (p * q) = η p + η q) → ∀ (f : G → ℂ) (u : ℂ), Continuous f → (∀ p ∈ P, ∀ x, f (p * x) = c p * Complex.exp (u * η p) * f x) → FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun k : K => fun x => f (x * (k : G)))) → ∃ (d : ℕ) (ρ : K →* ((Fin d → ℂ) →L[ℂ] (Fin d → ℂ))) (w : Fin d → ℂ) (e : (Fin d → ℂ) →L[ℂ] ℂ), Continuous ρ ∧ w ∈ secSp K P c ρ ∧ ∀ k : K, e (ρ k⁻¹ w) = f k := by
  intro G _ _ _ Γ K P c η hch hηK _ f u hf hlaw hfd
  obtain ⟨V, hVdef⟩ : ∃ V : Submodule ℂ (G → ℂ),
      V = Submodule.span ℂ (Set.range fun k : K => fun x => f (x * (k : G))) := ⟨_, rfl⟩
  rw [← hVdef] at hfd
  have hV : ∀ v ∈ V, ∀ k : K, (fun x => v (x * (k : G))) ∈ V := by
    intro v hv k
    rw [hVdef] at hv ⊢
    induction hv using Submodule.span_induction with
    | mem v hv =>
      obtain ⟨k', rfl⟩ := hv
      exact Submodule.subset_span ⟨k * k', by funext x; simp [mul_assoc]⟩
    | zero => exact Submodule.zero_mem _
    | add a b _ _ ha hb => exact Submodule.add_mem _ ha hb
    | smul a v _ hv => exact Submodule.smul_mem _ a hv
  have hcont : ∀ v ∈ V, Continuous v := by
    intro v hv
    rw [hVdef] at hv
    induction hv using Submodule.span_induction with
    | mem v hv =>
      obtain ⟨k', rfl⟩ := hv
      exact hf.comp (continuous_id.mul continuous_const)
    | zero => exact continuous_const
    | add a b _ _ ha hb => exact ha.add hb
    | smul a v _ hv => exact continuous_const.smul hv
  have hl : ∀ v ∈ V, ∀ p ∈ P, ∀ x, v (p * x) = c p * Complex.exp (u * η p) * v x := by
    intro v hv p hp x
    rw [hVdef] at hv
    induction hv using Submodule.span_induction generalizing x with
    | mem v hv =>
      obtain ⟨k', rfl⟩ := hv
      change f (p * x * (k' : G)) = c p * Complex.exp (u * η p) * f (x * (k' : G))
      rw [mul_assoc, hlaw p hp]
    | zero => simp
    | add a b _ _ ha hb => simp only [Pi.add_apply, ha, hb]; ring
    | smul a v _ hv => simp only [Pi.smul_apply, hv, smul_eq_mul]; ring
  have hfV : f ∈ V := by
    rw [hVdef]
    exact Submodule.subset_span ⟨1, by funext x; simp⟩
  refine ⟨Module.finrank ℂ V, rho hV, w₀ V,
    ∑ i, (Module.finBasis ℂ V).repr ⟨f, hfV⟩ i •
      (ContinuousLinearMap.proj i : (Fin (Module.finrank ℂ V) → ℂ) →L[ℂ] ℂ),
    rho_cont hV hcont, ?_, ?_⟩
  · intro r hr
    funext i
    have hri : ((r : G))⁻¹ ∈ P := P.inv_mem hr
    have hrK : ((r : G))⁻¹ ∈ K := K.inv_mem r.2
    have h1 := hl _ (Module.finBasis ℂ V i).2 _ hri 1
    have h2 : c r * c ((r : G))⁻¹ = 1 := by
      rw [← hch.mul _ hr _ hri, mul_inv_cancel, ch_one hch]
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [rho_w₀]
    rw [mul_one, hηK _ hri hrK] at h1
    rw [h1]
    simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero, mul_one]
    rw [← mul_assoc, h2, one_mul]
    rfl
  · intro k
    have h := sum_repr_apply (V := V) ⟨f, hfV⟩ (k : G)
    simp only [ContinuousLinearMap.coe_sum', Finset.sum_apply, ContinuousLinearMap.coe_smul',
      Pi.smul_apply, ContinuousLinearMap.proj_apply, smul_eq_mul]
    simp only [rho_w₀]
    simpa using h

end GlobalTheory.CompanionTheory.SiegelRep
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteLocalOrbitalIntegralBounded
section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC GlobalTheory.CompanionTheory.SiegelND
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.CompanionTheory.SiegelND.Integ GlobalTheory.CompanionTheory.SiegelND.Integ.Hua
open NumberField

namespace GlobalTheory.CompanionTheory.SiegelND.Integ.Weyl
open GlobalTheory.CompanionTheory.SW.Core GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Coef.Dec

set_option maxHeartbeats 1000000 in
theorem finite_bound : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
    IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J →
    ∀ (n : ℕ) (ψ : AddChar (AF F) ℂ), IsCharAF F ψ →
    ∀ μ : Measure (Fin n → Fin M → Af F ⊗[F] E), μ.IsAddHaarMeasure →
    ∀ Q : (Fin n → Fin M → Af F ⊗[F] E) → ℂ, IsSB Q →
    ∃ (C : ℝ) (t : F), t ≠ 0 ∧ ∀ c : hermE σ n,
      ‖starLoc (Af F) σ J (psiFin F ψ) μ Q (hermIn (Af F) σ n c)‖ ≤
        C * (delta (t • c).1 : ℝ) ^ (-((M : ℝ) / 2)) := by
  intro F E _ _ _ _ _ σ hCM M J hJ n ψ hψ μ hμ Q hQ
  classical
  obtain ⟨hA1, hA2, hA3, -⟩ := GlobalTheory.T.mem_Oh_iff_and_nat_mul_properties F
  haveI : LocallyCompactSpace (Af F) := hA1
  haveI : SecondCountableTopology (Af F) := hA2
  haveI : T2Space (Af F) := hA3
  obtain ⟨hT1, hT2, hT3, hT4, -, -, -, hT8, -⟩ := GlobalTheory.T.tensor_locally_compact_ring F E σ hCM (Af F)
  haveI : IsTopologicalRing (Af F ⊗[F] E) := hT1
  haveI : SecondCountableTopology (Af F ⊗[F] E) := hT3
  haveI : T2Space (Af F ⊗[F] E) := hT4
  haveI : BorelSpace (Fin n → Fin M → Af F ⊗[F] E) := hT8 n M
  haveI : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E
  obtain ⟨d, ⟨b⟩⟩ : ∃ d : ℕ, Nonempty (Module.Basis (Fin d) F E) :=
    ⟨_, ⟨Module.finBasis F E⟩⟩
  obtain ⟨N, hN, hNU⟩ := GlobalTheory.T.lattice_levels_neighbourhood_basis F E σ hCM d b n M _ (invariant_mem_nhds hQ.1 hQ.2)
  obtain ⟨hLo, hLc⟩ := GlobalTheory.T.lattice_level_open_compact F E σ hCM d b n M N hN
  set L := latN b n M N with hL
  obtain ⟨s, hs⟩ := eq_sum_cosets hQ.2 L hLo (fun x l hl => hNU hl x)
  obtain ⟨D, hD, hDc⟩ := GlobalTheory.T.trace_dual_denominator_bounded F
  obtain ⟨t₁, ht₁, htest⟩ := GlobalTheory.T.rational_character_kernel_scaling F E σ hCM d b ψ hψ N hN D hD hDc
  obtain ⟨s₂, hs₂, hrat⟩ := GlobalTheory.T.rational_tuple_in_lattice_level F E d b M J n N hN
  have hs₂F : ((s₂ : ℕ) : F) ≠ 0 := Nat.cast_ne_zero.2 hs₂.ne'
  refine ⟨(∑ a ∈ s, ‖Q a‖) * (μ (L : Set _)).toReal, t₁ * (s₂ : F), mul_ne_zero ht₁ hs₂F, fun c => ?_⟩
  set t : F := t₁ * (s₂ : F) with ht
  set bc := hermIn (Af F) σ n c with hbc
  obtain ⟨hp1, hp2, hp3⟩ := GlobalTheory.T.phase_continuous_unitary F E σ hCM M J n ψ hψ bc
  obtain ⟨hq1, hq2⟩ := GlobalTheory.T.pairing_biadditive F E σ M J n ψ bc
  set q := phaseB σ J (psiFin F ψ) bc with hq
  set B := pairB σ J (psiFin F ψ) bc with hB
  set S : Set (Fin n → Fin M → Af F ⊗[F] E) := {y | y ∈ L ∧ ∀ l ∈ L, B l y = 1} with hS
  have hLfin : μ (L : Set _) ≠ ⊤ := hLc.measure_lt_top.ne
  have hSL : S ⊆ L := fun y hy => hy.1
  have hSfin : μ S ≠ ⊤ := ne_top_of_le_ne_top hLfin (measure_mono hSL)

  have hbd : ‖starLoc (Af F) σ J (psiFin F ψ) μ Q bc‖ ≤
      (∑ a ∈ s, ‖Q a‖) * √((μ (L : Set _)).toReal * (μ S).toReal) := by
    have hw := GlobalTheory.T.gauss_sum_quadratic_character_bound _ μ L hLc hLo q B hp1 hp2 (GlobalTheory.T.phase_cocycle_bimultiplicative F E σ hCM M J hJ n ψ hψ bc) hq1 hq2
    exact GlobalTheory.T.gauss_sum_finite_average_bound _ μ L hLc hLo q hp1 hp2 _ hw Q s hs

  have hSm : MeasurableSet S := by
    have e : S = (L : Set _) ∩ ⋂ l ∈ L, (B l) ⁻¹' {1} := by
      ext y
      simp [hS]
    have hcl : IsClosed S := by
      rw [e]
      have hLcl : IsClosed (L : Set (Fin n → Fin M → Af F ⊗[F] E)) := hLc.isClosed
      exact hLcl.inter (isClosed_biInter fun l _ => isClosed_singleton.preimage (hp3 l))
    exact hcl.measurableSet

  have hdiff : ∀ u ∈ S, ∀ v ∈ S, ∀ l ∈ L, B l (v - u) = 1 := by
    intro u hu v hv l hl
    have h := hq2 l u (v - u)
    rw [add_sub_cancel, hv.2 l hl, hu.2 l hl, one_mul] at h
    exact h.symm
  set c' : Matrix (Fin n) (Fin n) E := ((t • c).1).map σ with hc'
  have hδ : delta c' = delta (t • c).1 := GlobalTheory.T.delta_conj_invariant F E σ n _
  have hδ0 : delta c' ≠ 0 := GlobalTheory.T.delta_ne_zero' E n c'
  haveI hfin : Finite ((Fin n → 𝓞 E) ⧸ Kc c') := Nat.finite_of_card_ne_zero hδ0
  haveI := Fintype.ofFinite ((Fin n → 𝓞 E) ⧸ Kc c')

  have hcount : ((delta c' ^ M : ℕ) : ℝ≥0∞) * μ S ≤ μ (L : Set _) := by
    have h := GlobalTheory.T.disjoint_translates_volume_bound _ μ L S hSm hSL (Fin M → (Fin n → 𝓞 E) ⧸ Kc c')
      (fun φ => ratTuple J s₂ fun i => (φ i).out) (fun φ => hrat _) ?_
    · have hc : Fintype.card (Fin M → (Fin n → 𝓞 E) ⧸ Kc c') = delta c' ^ M := by
        rw [Fintype.card_fun, Fintype.card_fin, ← Nat.card_eq_fintype_card]
        rfl
      rwa [hc] at h
    · intro φ φ' u v hu hv huv
      funext i₀
      have hρ : ratTuple (F := F) J s₂ (fun i => (φ i).out - (φ' i).out) = ratTuple J s₂ (fun i => (φ i).out) - ratTuple J s₂ (fun i => (φ' i).out) := by
        funext a j
        simp only [ratTuple, Pi.sub_apply, map_sub]
        rw [show (fun i => algebraMap (𝓞 E) E ((φ i).out a) - algebraMap (𝓞 E) E ((φ' i).out a)) =
          (fun i => algebraMap (𝓞 E) E ((φ i).out a)) - (fun i => algebraMap (𝓞 E) E ((φ' i).out a)) from rfl,
          Matrix.mulVec_sub]
        simp [mul_sub]
      have hmem : ∀ l ∈ L, B l (ratTuple J s₂ fun i => (φ i).out - (φ' i).out) = 1 := by
        intro l hl
        have : ratTuple (F := F) J s₂ (fun i => (φ i).out - (φ' i).out) = v - u := by
          rw [hρ, sub_eq_sub_iff_add_eq_add, add_comm v]
          exact huv
        rw [this]
        exact hdiff u hu v hv l hl
      have hK : (φ i₀).out - (φ' i₀).out ∈ Kc c' := by
        intro c₀
        have hx := htest ((s₂ : E) * ∑ a, c.1 a c₀ *
          algebraMap (𝓞 E) E (((φ i₀).out - (φ' i₀).out) a)) (fun x hx => by
            have h1 := hmem (fun a i => if a = c₀ ∧ i = i₀ then x else 0) (by
              intro a i
              by_cases h : a = c₀ ∧ i = i₀
              · simpa [h] using hx
              · simp only [h, if_false]
                exact (latN b n M N).zero_mem a i)
            rw [hB, hbc, GlobalTheory.T.pairing_on_rational_tuple_formula F E σ M J hJ n (psiFin F ψ) c c₀ i₀ x s₂ _] at h1
            exact h1)
        obtain ⟨o, ho⟩ := hx
        refine ⟨o, ?_⟩
        rw [ho]
        simp only [Matrix.mulVec, dotProduct, hc', Matrix.map_apply, Finset.smul_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun a _ => ?_
        have h3 : σ (c.1 c₀ a) = c.1 a c₀ := c.2 a c₀
        rw [show σ ((t • c).1 c₀ a) = t • c.1 a c₀ from by
          show σ (t • c.1 c₀ a) = _
          rw [Algebra.smul_def, map_mul, AlgHom.commutes, h3, ← Algebra.smul_def]]
        simp only [ht, Algebra.smul_def, map_mul, map_natCast]
        ring
      have h5 : (QuotientAddGroup.mk (φ' i₀).out : (Fin n → 𝓞 E) ⧸ Kc c') = QuotientAddGroup.mk (φ i₀).out :=
        QuotientAddGroup.eq.2 (by rw [neg_add_eq_sub]; exact hK)
      rw [QuotientAddGroup.out_eq', QuotientAddGroup.out_eq'] at h5
      exact h5.symm

  have hδpos : (0 : ℝ) < (delta c' : ℝ) := Nat.cast_pos.2 (Nat.pos_of_ne_zero hδ0)
  have hreal : (delta c' : ℝ) ^ M * (μ S).toReal ≤ (μ (L : Set _)).toReal := by
    have h := ENNReal.toReal_mono hLfin hcount
    rw [ENNReal.toReal_mul] at h
    simpa using h
  rw [← hδ]
  set A := (μ (L : Set _)).toReal with hA
  set Sr := (μ S).toReal with hSr
  have hA0 : 0 ≤ A := ENNReal.toReal_nonneg
  have hS0 : 0 ≤ Sr := ENNReal.toReal_nonneg
  set w : ℝ := (delta c' : ℝ) ^ (-((M : ℝ) / 2)) with hw
  have hw0 : 0 ≤ w := Real.rpow_nonneg hδpos.le _
  have hw2 : w ^ 2 * (delta c' : ℝ) ^ M = 1 := by
    rw [hw, ← Real.rpow_natCast _ 2, ← Real.rpow_mul hδpos.le, ← Real.rpow_natCast _ M, ← Real.rpow_add hδpos]
    have : -((M : ℝ) / 2) * ((2 : ℕ) : ℝ) + (M : ℝ) = 0 := by push_cast; ring
    rw [this, Real.rpow_zero]
  have hsq : √(A * Sr) ≤ A * w := by
    refine Real.sqrt_le_iff.2 ⟨mul_nonneg hA0 hw0, ?_⟩
    have h1 : Sr = w ^ 2 * ((delta c' : ℝ) ^ M * Sr) := by rw [← mul_assoc, hw2, one_mul]
    have h2 : Sr ≤ w ^ 2 * A := by
      rw [h1]
      exact mul_le_mul_of_nonneg_left hreal (sq_nonneg _)
    calc A * Sr ≤ A * (w ^ 2 * A) := mul_le_mul_of_nonneg_left h2 hA0
      _ = (A * w) ^ 2 := by ring
  calc _ ≤ (∑ a ∈ s, ‖Q a‖) * √(A * Sr) := hbd
    _ ≤ (∑ a ∈ s, ‖Q a‖) * (A * w) :=
        mul_le_mul_of_nonneg_left hsq (Finset.sum_nonneg fun _ _ => norm_nonneg _)
    _ = _ := by ring

end GlobalTheory.CompanionTheory.SiegelND.Integ.Weyl
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HypothesesPreservedByLinearPullback
section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CompanionTheory.WeilSiegel.Deg

variable {D : D7}

def rightMulEquiv {m r : ℕ} (a : Matrix (Fin r) (Fin r) D.host.E) (ha : a.det ≠ 0) :
    Matrix (Fin m) (Fin r) D.host.E ≃ Matrix (Fin m) (Fin r) D.host.E where
  toFun ξ := ξ * a
  invFun ξ := ξ * a⁻¹
  left_inv ξ := by
    have hu : IsUnit a.det := isUnit_iff_ne_zero.mpr ha
    simp [Matrix.mul_assoc, Matrix.mul_nonsing_inv a hu]
  right_inv ξ := by
    have hu : IsUnit a.det := isUnit_iff_ne_zero.mpr ha
    simp [Matrix.mul_assoc, Matrix.nonsing_inv_mul a hu]

theorem invPt_mul (V : HSp D) {r : ℕ} (h : GA D V) (ξ : Matrix (Fin V.rank) (Fin r) D.host.E)
    (a : Matrix (Fin r) (Fin r) D.host.E) :
    GlobalTheory.SiegelFormula.invPt V h (ξ * a) =
      HMul.hMul (GlobalTheory.SiegelFormula.invPt V h ξ) (a.map (incA D)) := by
  unfold GlobalTheory.SiegelFormula.invPt
  rw [Matrix.map_mul, Matrix.mul_assoc]

theorem absTheta_pull (V : HSp D) {r : ℕ} (φ : Mx D V.rank r → ℂ)
    (a : Matrix (Fin r) (Fin r) D.host.E) (ha : a.det ≠ 0) (h : GA D V) :
    GlobalTheory.SiegelFormula.absTheta V (pull a φ) h = GlobalTheory.SiegelFormula.absTheta V φ h := by
  unfold GlobalTheory.SiegelFormula.absTheta
  rw [← (rightMulEquiv (m := V.rank) a ha).tsum_eq
    (fun ξ => ‖φ (GlobalTheory.SiegelFormula.invPt V h ξ)‖ₑ)]
  refine tsum_congr fun ξ => ?_
  show ‖φ _‖ₑ = ‖φ (GlobalTheory.SiegelFormula.invPt V h (ξ * a))‖ₑ
  rw [invPt_mul]

theorem absThetaInt_pull (V : HSp D) (ν : Measure (GA D V)) {r : ℕ} (φ : Mx D V.rank r → ℂ)
    (a : Matrix (Fin r) (Fin r) D.host.E) (ha : a.det ≠ 0) :
    GlobalTheory.SiegelFormula.absThetaInt V ν (pull a φ) = GlobalTheory.SiegelFormula.absThetaInt V ν φ := by
  unfold GlobalTheory.SiegelFormula.absThetaInt
  have : GlobalTheory.SiegelFormula.absTheta V (pull a φ) = GlobalTheory.SiegelFormula.absTheta V φ :=
    funext (absTheta_pull V φ a ha)
  rw [this]

theorem hyp_pull : ∀ (D : D7) (r : ℕ) (V : HSp D) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D)
    (μ : Measure (Mx D V.rank r)) (lam : Measure (hermA D r)) (ν : Measure (GA D V))
    (φ : Mx D V.rank r → ℂ) (a : Matrix (Fin r) (Fin r) D.host.E), a.det ≠ 0 →
    Hyp D r V ψ θ μ lam ν φ → Hyp D r V ψ θ μ lam ν (pull a φ) := by
  intro D r V ψ θ μ lam ν φ a ha ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩
  have hli : LinearIndependent D.host.E a :=
    Matrix.linearIndependent_rows_of_isUnit ((Matrix.isUnit_iff_isUnit_det a).mpr (isUnit_iff_ne_zero.mpr ha))
  refine ⟨h1, h2, h3, h4, h5, h6, GlobalTheory.T.pullback_schwartz_linear_independent D θ h3 _ _ _ a hli φ h7, ?_⟩
  rw [absThetaInt_pull V ν φ a ha]
  exact h8

end GlobalTheory.CompanionTheory.WeilSiegel.Deg
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalComparisonSplitStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_comparison_split : PositivityTheory.Rg.BcB.G8.Fin.LocCompareSplit := by
  first | exact @GlobalTheory.CompanionTheory.LcSplit.locCompareSplit | exact GlobalTheory.CompanionTheory.LcSplit.locCompareSplit | (intros; apply GlobalTheory.CompanionTheory.LcSplit.locCompareSplit <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalGlobalDictionaryStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_global_dictionary : PositivityTheory.RgEis.Dict := by
  first | exact @GlobalTheory.CompanionTheory.EisDict.dict | exact GlobalTheory.CompanionTheory.EisDict.dict | (intros; apply GlobalTheory.CompanionTheory.EisDict.dict <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalHypothesesHoldStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_hypotheses_hold : PositivityTheory.Rg.BcB.G8.Fin.LocHyp := by
  first | exact @GlobalTheory.CompanionTheory.LocHypProof.locHyp | exact GlobalTheory.CompanionTheory.LocHypProof.locHyp | (intros; apply GlobalTheory.CompanionTheory.LocHypProof.locHyp <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ModulusHalfBlockValueStatement
section
open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.BCT GlobalTheory.LFun Formalism.L2.Host
open PositivityTheory.Rg.Rs PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.F.RS GlobalTheory.CompanionTheory.CtS
open scoped Classical

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.modulus_half_block_value : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a b : ℕ) (w : Pl E) (i j : ℕ) (m : GLw a w × GLw b w), ordL m.1.val.det = (i : ℤ) → ordL m.2.val.det = (j : ℤ) → absHalf w (m.1.val.det ^ b / m.2.val.det ^ a) = (qV E w : ℂ) ^ (-((i : ℂ) * b - (j : ℂ) * a) / 2) := by
  first | exact @GlobalTheory.CompanionTheory.CtS.absHalf_blockDet_value | exact GlobalTheory.CompanionTheory.CtS.absHalf_blockDet_value | (intros; apply GlobalTheory.CompanionTheory.CtS.absHalf_blockDet_value <;> assumption)
end

