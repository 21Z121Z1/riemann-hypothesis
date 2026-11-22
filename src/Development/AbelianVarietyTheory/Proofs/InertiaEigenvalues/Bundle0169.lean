import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0085
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0156
import GroundTheory.LocalFields.UnramifiedNormSurj
import GroundTheory.LocalFields.UnramifiedGalois
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0054
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0148
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0149
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0067
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MonodromyZeroOfWeilDeligneRepClassIff
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0051
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0053

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnramifiedQuadraticExistsIntegersUniformiser
section
open GlobalTheory.JR GlobalTheory.JR.WeilQuad Matrix MeasureTheory Filter Topology

noncomputable section

namespace GlobalTheory.JR.UnramInt
open ValuativeRel GroundTheory.LocalField

theorem alg_main : ∀ (F E K L : Type) [NontriviallyNormedField F] [IsUltrametricDist F] [CompleteSpace F]
    [LocallyCompactSpace F] [NontriviallyNormedField E] [NormedAlgebra F E] [IsUltrametricDist E]
    [LocallyCompactSpace E] [Field K] [Field L] [Algebra F K] [Algebra F L] [Algebra K L] [Algebra E L]
    [IsScalarTower F K L] [IsScalarTower F E L] [FiniteDimensional F K] [FiniteDimensional F E]
    [FiniteDimensional K L],
    (∀ y : E, ∃ x : F, ‖y‖ = ‖x‖) → Module.finrank K L = 2 →
    Algebra.adjoin K (Set.range (algebraMap E L)) = ⊤ →
    ∃ (ϖ : Kˣ) (O : Subring L), (O : Set L) = {y | spectralNorm F L y ≤ 1} ∧
      (¬ ∃ y : L, Algebra.norm K y = (ϖ : K)) ∧ algebraMap K L (ϖ : K) ∈ O ∧
      (¬ ∃ z ∈ O, algebraMap K L (ϖ : K) * z = 1) ∧
      (∀ y ∈ O, (∃ z ∈ O, y = algebraMap K L (ϖ : K) * z) ∨ ∃ z ∈ O, y * z = 1) ∧
      (∀ s : K, algebraMap K L s ∈ O → ∃ z ∈ O, Algebra.trace K L z = s) ∧
      (∀ s : K, algebraMap K L s ∈ O → (∃ r ∈ O, algebraMap K L s * r = 1) → ∃ w ∈ O, Algebra.norm K w = s) ∧
      (∀ r : ℝ, 0 < r → ∃ n : ℕ, ∀ z ∈ O, spectralNorm F L (algebraMap K L ((ϖ : K) ^ n) * z) < r) ∧
      ∀ y : L, ∃ n : ℕ, algebraMap K L ((ϖ : K) ^ n) * y ∈ O := by
  intro F E K L _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hunr h2 hgen
  haveI : FiniteDimensional F L := Module.Finite.trans K L
  have nmulL : ∀ x y : L, spectralNorm F L (x * y) = spectralNorm F L x * spectralNorm F L y :=
    fun x y => map_mul (spectralMulAlgNorm F L) x y
  have npowK : ∀ (x : K) (n : ℕ), spectralNorm F K (x ^ n) = spectralNorm F K x ^ n :=
    fun x n => map_pow (spectralMulAlgNorm F K) x n
  have ntow : ∀ a : K, spectralNorm F L (algebraMap K L a) = spectralNorm F K a :=
    fun a => (spectralNorm.eq_of_tower a).symm
  obtain ⟨vF, hFloc, hFv⟩ := NormSign.exists_valuativeRel_of_normed F
  obtain ⟨vE, hEloc, hEv⟩ := NormSign.exists_valuativeRel_of_normed E
  obtain ⟨vK, tK, hKloc, hKv⟩ := GlobalTheory.T.exists_localField_structure_spectralNorm F K
  obtain ⟨vL, tL, hLloc, hLv⟩ := GlobalTheory.T.exists_localField_structure_spectralNorm F L
  haveI : ValuativeExtension F E := ⟨fun a b => by rw [hEv, hFv, norm_algebraMap', norm_algebraMap']⟩
  haveI : ValuativeExtension F K := ⟨fun a b => by
    rw [hKv, hFv, spectralNorm_extends, spectralNorm_extends]⟩
  haveI : ValuativeExtension K L := ⟨fun a b => by rw [hLv, hKv, ntow, ntow]⟩
  have heF : ramificationIndex F E = 1 := by
    obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[E]
    obtain ⟨x, hx⟩ := hunr (ϖ : E)
    have h1 : (ϖ : E) ≤ᵥ algebraMap F E x := by rw [hEv, norm_algebraMap', hx]
    have h2 : algebraMap F E x ≤ᵥ (ϖ : E) := by rw [hEv, norm_algebraMap', hx]
    have hv : valuation E (ϖ : E) = valuation E (algebraMap F E x) :=
      le_antisymm ((Valuation.Compatible.vle_iff_le _ _).1 h1) ((Valuation.Compatible.vle_iff_le _ _).1 h2)
    have hord : ord (ϖ : E) = ord (algebraMap F E x) := by
      simp only [ord]
      rw [(normalizedValuation_eq_iff (K := E)).2 hv]
    rw [ord_uniformizer hϖ, ord_algebraMap] at hord
    have hd : ((ramificationIndex F E : ℕ) : ℤ) ∣ 1 := ⟨ord x, hord⟩
    exact_mod_cast Int.eq_one_of_dvd_one (by positivity) hd
  have heKL := GlobalTheory.T.ramificationIndex_eq_one_of_adjoin_range_eq_top_alt F E K L heF hgen
  obtain ⟨ϖ, hϖ0, hϖ1, hϖ1', hN, hunif, htr, hnrm⟩ := GlobalTheory.T.unramified_quadratic_norm_trace_surjective K L heKL h2
  have hleL : ∀ y : L, y ≤ᵥ 1 ↔ spectralNorm F L y ≤ 1 := fun y => by rw [hLv, spectralNorm_one]
  have hleK : ∀ s : K, s ≤ᵥ 1 ↔ spectralNorm F K s ≤ 1 := fun s => by rw [hKv, spectralNorm_one]
  have hgeK : ∀ s : K, (1 : K) ≤ᵥ s ↔ 1 ≤ spectralNorm F K s := fun s => by rw [hKv, spectralNorm_one]
  have hϖlt : spectralNorm F K ϖ < 1 := lt_of_not_ge fun h => hϖ1' ((hgeK ϖ).2 h)
  let O : Subring L :=
    { carrier := {y | spectralNorm F L y ≤ 1}
      mul_mem' := fun {a b} ha hb => by
        simp only [Set.mem_setOf_eq] at *
        rw [nmulL]
        exact mul_le_one₀ ha (spectralNorm_nonneg _) hb
      one_mem' := by simp [spectralNorm_one]
      add_mem' := fun {a b} ha hb => (isNonarchimedean_spectralNorm a b).trans (max_le ha hb)
      zero_mem' := by simp [spectralNorm_zero]
      neg_mem' := fun {a} ha => by
        simp only [Set.mem_setOf_eq] at *
        rwa [spectralNorm_neg (Algebra.IsAlgebraic.isAlgebraic a)] }
  have hmem : ∀ y : L, y ∈ O ↔ y ≤ᵥ 1 := fun y => (hleL y).symm
  refine ⟨Units.mk0 ϖ hϖ0, O, rfl, hN, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · show spectralNorm F L _ ≤ 1
    rw [Units.val_mk0, ntow]
    exact hϖlt.le
  · rintro ⟨z, hz, hz1⟩
    have h := congrArg (spectralNorm F L) hz1
    rw [nmulL, spectralNorm_one, Units.val_mk0, ntow] at h
    have hz' : spectralNorm F L z ≤ 1 := hz
    have : spectralNorm F K ϖ * spectralNorm F L z < 1 :=
      lt_of_le_of_lt (mul_le_of_le_one_right (spectralNorm_nonneg _) hz') hϖlt
    linarith
  · intro y hy
    rcases hunif y ((hmem y).1 hy) with ⟨z, hz, hyz⟩ | ⟨z, hz, hyz⟩
    · exact Or.inl ⟨z, (hmem z).2 hz, by rw [Units.val_mk0]; exact hyz⟩
    · exact Or.inr ⟨z, (hmem z).2 hz, hyz⟩
  · intro s hs
    have hs' : s ≤ᵥ 1 := by
      rw [hleK, ← ntow]
      exact hs
    obtain ⟨z, hz, hzs⟩ := htr s hs'
    exact ⟨z, (hmem z).2 hz, hzs⟩
  · rintro s hs ⟨r, hr, hsr⟩
    have hs1 : spectralNorm F K s ≤ 1 := by rw [← ntow]; exact hs
    have hr1 : spectralNorm F L r ≤ 1 := hr
    have h := congrArg (spectralNorm F L) hsr
    rw [nmulL, spectralNorm_one, ntow] at h
    have hge : 1 ≤ spectralNorm F K s := by
      nlinarith [spectralNorm_nonneg (K := F) s, spectralNorm_nonneg (K := F) r]
    obtain ⟨w, hw, hws⟩ := hnrm s ((hleK s).2 hs1) ((hgeK s).2 hge)
    exact ⟨w, (hmem w).2 hw, hws⟩
  · intro r hr
    obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hr hϖlt
    refine ⟨n, fun z hz => ?_⟩
    have hz' : spectralNorm F L z ≤ 1 := hz
    rw [nmulL, ntow, Units.val_mk0, npowK]
    exact lt_of_le_of_lt (mul_le_of_le_one_right (pow_nonneg (spectralNorm_nonneg _) _) hz') hn
  · intro y
    by_cases hy : spectralNorm F L y ≤ 1
    · refine ⟨0, ?_⟩
      show spectralNorm F L _ ≤ 1
      simpa using hy
    · have hpos : 0 < spectralNorm F L y := lt_of_lt_of_le one_pos (le_of_not_ge hy)
      obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one (inv_pos.2 hpos) hϖlt
      refine ⟨n, ?_⟩
      show spectralNorm F L _ ≤ 1
      rw [nmulL, ntow, Units.val_mk0, npowK]
      calc spectralNorm F K ϖ ^ n * spectralNorm F L y ≤ (spectralNorm F L y)⁻¹ * spectralNorm F L y :=
            mul_le_mul_of_nonneg_right hn.le (spectralNorm_nonneg _)
        _ = 1 := inv_mul_cancel₀ hpos.ne'

end GlobalTheory.JR.UnramInt

namespace GlobalTheory.JR.UnramInt

theorem main : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E), IsField A.K → IsField A.L → ∃ (ϖ : A.Kˣ) (O : Subring A.L), IsOpen (O : Set A.L) ∧ IsCompact (O : Set A.L) ∧ (∀ y ∈ O, star y ∈ O) ∧ (¬ ∃ y, A.NL y = (ϖ : A.K)) ∧ algebraMap A.K A.L (ϖ : A.K) ∈ O ∧ (¬ ∃ z ∈ O, algebraMap A.K A.L (ϖ : A.K) * z = 1) ∧ (∀ y ∈ O, (∃ z ∈ O, y = algebraMap A.K A.L (ϖ : A.K) * z) ∨ ∃ z ∈ O, y * z = 1) ∧ (∀ s : A.K, algebraMap A.K A.L s ∈ O → ∃ z ∈ O, Algebra.trace A.K A.L z = s) ∧ (∀ s : A.K, algebraMap A.K A.L s ∈ O → (∃ r ∈ O, algebraMap A.K A.L s * r = 1) → ∃ w ∈ O, A.NL w = s) ∧ (∀ U ∈ 𝓝 (0 : A.L), ∃ n : ℕ, ∀ z ∈ O, algebraMap A.K A.L ((ϖ : A.K) ^ n) * z ∈ U) ∧ ∀ y : A.L, ∃ n : ℕ, algebraMap A.K A.L ((ϖ : A.K) ^ n) * y ∈ O := by
  intro F E _ _ _ _ U A hK hL
  letI : Field A.K := hK.toField
  letI : Field A.L := hL.toField
  haveI := U.ultraF
  haveI := U.ultraE
  haveI := U.lcF
  haveI := U.lcE
  haveI : ProperSpace F := .of_nontriviallyNormedField_of_weaklyLocallyCompactSpace F
  haveI : CompleteSpace F := complete_of_proper
  haveI : FiniteDimensional F E := Module.finite_of_finrank_eq_succ U.finrank_eq
  have hKL : Module.finrank A.K A.L = 2 := by
    haveI := A.push.symm
    rw [← (Algebra.IsPushout.equiv F A.K E A.L).toLinearEquiv.finrank_eq, Module.finrank_baseChange,
      U.finrank_eq]
  haveI : FiniteDimensional A.K A.L := Module.finite_of_finrank_eq_succ hKL
  haveI : FiniteDimensional F A.L := Module.Finite.trans A.K A.L
  have hgen : Algebra.adjoin A.K (Set.range (algebraMap E A.L)) = ⊤ := by
    haveI := A.push.symm
    rw [eq_top_iff]
    intro y _
    obtain ⟨t, rfl⟩ := (Algebra.IsPushout.equiv F A.K E A.L).surjective y
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul k e =>
      rw [Algebra.IsPushout.equiv_tmul]
      exact Subalgebra.mul_mem _ (Subalgebra.algebraMap_mem _ k) (Algebra.subset_adjoin ⟨e, rfl⟩)
    | add a b ha hb =>
      rw [map_add]
      exact Subalgebra.add_mem _ (ha trivial) (hb trivial)
  obtain ⟨ϖ, O, hO, hN, hϖO, hϖu, hunif, htr, hnrm, hsmall, hbig⟩ :=
    alg_main F E A.K A.L (fun y => U.unram y) hKL hgen
  obtain ⟨hop, hcp, hball⟩ := GlobalTheory.T.spectralNorm_closedBall_isOpen_isCompact_nhds F A.L
  have hmem : ∀ y : A.L, y ∈ O ↔ spectralNorm F A.L y ≤ 1 := fun y => by
    rw [← SetLike.mem_coe, hO]
    rfl
  refine ⟨ϖ, O, by rw [hO]; exact hop, by rw [hO]; exact hcp, ?_, hN, hϖO, hϖu, hunif, htr, hnrm, ?_, hbig⟩
  · intro y hy
    have hσ : ∀ x : F, starRingAut (algebraMap F A.L x) = algebraMap F A.L x := fun x => by
      rw [starRingAut_apply, IsScalarTower.algebraMap_apply F A.K A.L, A.star_K]
    let σ : A.L ≃ₐ[F] A.L := AlgEquiv.ofRingEquiv (f := starRingAut) hσ
    have h := spectralNorm_eq_of_equiv σ y
    rw [hmem] at hy ⊢
    have hs : σ y = star y := rfl
    rw [hs] at h
    rw [← h]
    exact hy
  · intro V hV
    obtain ⟨r, hr, hrV⟩ := hball V hV
    obtain ⟨n, hn⟩ := hsmall r hr
    exact ⟨n, fun z hz => hrV _ (hn z hz)⟩

end GlobalTheory.JR.UnramInt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WeilDeligneInductionPrinciple
section
noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial Module

namespace GlobalTheory.WeilDeligne

section Reduction

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}

def WDRep.resZero {V : Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (a : WDRep h V) (U : Submodule ℂ V) (hU : ∀ σ, ∀ v ∈ U, a.ρ σ v ∈ U) : WDRep h U where
  ρ := { toFun := fun σ => (a.ρ σ).restrict (hU σ)
         map_one' := by ext; simp
         map_mul' := fun σ τ => by ext; simp }
  N := 0
  smooth := a.smooth.of_le fun σ hσ => by ext; simp [hσ]
  semisimple σ := End.IsSemisimple.restrict (hU σ) (a.semisimple σ)
  nilpotent := IsNilpotent.zero
  comm σ := by simp

theorem WDRep.charpoly_eq_mul_of_isCompl {V : Type} [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] (a : WDRep h V) (U U' : Submodule ℂ V)
    (hU : ∀ σ, ∀ v ∈ U, a.ρ σ v ∈ U) (hU' : ∀ σ, ∀ v ∈ U', a.ρ σ v ∈ U') (hc : IsCompl U U')
    (σ : Weil h) :
    (a.ρ σ).charpoly = ((a.resZero U hU).ρ σ).charpoly * ((a.resZero U' hU').ρ σ).charpoly := by
  rw [← LinearMap.charpoly_prodMap, ← LinearEquiv.charpoly_conj (Submodule.prodEquivOfIsCompl U U' hc)]
  congr 1
  refine LinearMap.ext fun v => ?_
  obtain ⟨x, rfl⟩ := (Submodule.prodEquivOfIsCompl U U' hc).surjective v
  rw [LinearEquiv.conj_apply_apply, LinearEquiv.symm_apply_apply]
  simp [Submodule.coe_prodEquivOfIsCompl', WDRep.resZero]

theorem finite_range_of_frob_pow_eq_one {V : Type} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ (Weil h) V) (hρ : IsSmooth ρ) {m : ℕ} (hm : 0 < m)
    (h1 : ρ (frob h) ^ m = 1) : (Set.range ρ).Finite := by
  refine (Set.Finite.image2 (· * ·) (Set.finite_range fun j : Fin m => ρ (frob h) ^ (j : ℕ))
    hρ.finite_range).subset ?_
  rintro _ ⟨σ, rfl⟩
  obtain ⟨τ, hτ⟩ := exists_eq_zpow_mul (h := h) deg_frob σ
  have hker : frob h ^ m ∈ ρ.ker := by rw [MonoidHom.mem_ker, map_pow, h1]
  set k := deg σ
  have hk : frob h ^ k = frob h ^ ((k % m).toNat) * (frob h ^ m) ^ (k / m) := by
    rw [← zpow_natCast (frob h) m, ← zpow_mul, ← zpow_natCast (frob h) ((k % m).toNat),
      ← zpow_add, Int.toNat_of_nonneg (Int.emod_nonneg _ (by exact_mod_cast hm.ne')),
      add_comm, Int.mul_ediv_add_emod]
  have hlt : (k % m).toNat < m := by
    have := Int.emod_lt_of_pos k (by exact_mod_cast hm : (0 : ℤ) < m)
    omega
  refine ⟨ρ (frob h) ^ ((k % m).toNat), ⟨⟨_, hlt⟩, rfl⟩, ρ (ineIncl h τ), ⟨τ, rfl⟩, ?_⟩
  have h2 : ρ ((frob h ^ m) ^ (k / m)) = 1 := (ρ.ker.zpow_mem hker _)
  show _ = ρ σ
  rw [hτ, hk, map_mul, map_mul, h2, mul_one, map_pow]

theorem exists_of_lpSum_twist_finite (S : WD h → Prop)
    (hsum : ∀ x y, S x → S y → S (x.lpSum y))
    (hfin : ∀ (n : ℕ) (a : WDRep h (Fin n → ℂ)) (μ : Weil h →* ℂˣ) (hμ : IsSmooth μ),
      (Set.range a.ρ).Finite → S (WD.mk (a.twist μ hμ))) :
    ∀ (d : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V],
      finrank ℂ V = d → ∀ (ρ : Representation ℂ (Weil h) V), IsSmooth ρ →
      (∀ σ, End.IsSemisimple (ρ σ)) → ∃ y : WD h, S y ∧ ∀ σ, y.charPol σ = (ρ σ).charpoly := by
  intro d
  induction d using Nat.strong_induction_on with
  | _ d ih =>
  intro V _ _ _ hd ρ hρ hs
  let a0 : WDRep h V := ⟨ρ, 0, hρ, hs, IsNilpotent.zero, by simp⟩
  obtain ⟨m, hm, hcomm⟩ := exists_pow_frob_commute ρ hρ
  have hsm : ρ (frob h) ^ m = ρ (frob h ^ m) := (map_pow _ _ _).symm
  by_cases hsc : ∃ c : ℂ, c ≠ 0 ∧ ρ (frob h) ^ m = c • (1 : Module.End ℂ V)
  · obtain ⟨c, hc0, hsc⟩ := hsc
    obtain ⟨c', hc'⟩ := IsAlgClosed.exists_pow_nat_eq c hm
    have hc'0 : c' ≠ 0 := by rintro rfl; exact hc0 (by rw [← hc', zero_pow hm.ne'])
    set u : ℂˣ := Units.mk0 c' hc'0
    let b : WDRep h V := a0.twist (unrChar h u⁻¹) (isSmooth_unrChar h _)
    have hb1 : b.ρ (frob h) ^ m = 1 := by
      show ((((unrChar h u⁻¹) (frob h) : ℂˣ) : ℂ) • ρ (frob h)) ^ m = 1
      rw [_root_.smul_pow, hsc, smul_smul, unrChar_apply, deg_frob, zpow_one, ← Units.val_pow_eq_pow_val,
        inv_pow]
      have : u ^ m = Units.mk0 c hc0 := Units.ext (by simp [u, hc'])
      rw [this]
      simp [hc0]
    have hfinb := finite_range_of_frob_pow_eq_one b.ρ b.smooth hm hb1
    have hfins : (Set.range (WD.std b).2.ρ).Finite :=
      (hfinb.image ((finBasis ℂ V).equivFun.conjAlgEquiv ℂ)).subset (by rintro _ ⟨σ, rfl⟩; exact ⟨_, ⟨σ, rfl⟩, rfl⟩)
    refine ⟨WD.mk ((WD.std b).2.twist (unrChar h u) (isSmooth_unrChar h _)),
      hfin _ _ _ _ hfins, fun σ => ?_⟩
    rw [← WD.sound ((WD.iso_std b).twist _ _), WD.charPol_mk]
    show ((((unrChar h u) σ : ℂˣ) : ℂ) • ((((unrChar h u⁻¹) σ : ℂˣ) : ℂ) • ρ σ)).charpoly = _
    rw [smul_smul, ← Units.val_mul, unrChar_apply, unrChar_apply, ← mul_zpow, mul_inv_cancel,
      one_zpow, Units.val_one, one_smul]
  · have hnt : Nontrivial V := by
      by_contra hn
      rw [not_nontrivial_iff_subsingleton] at hn
      exact hsc ⟨1, one_ne_zero, LinearMap.ext fun v => Subsingleton.elim _ _⟩
    set s := ρ (frob h) ^ m with hs_def
    have hss : End.IsSemisimple s := by rw [hsm]; exact hs _
    obtain ⟨c, hc⟩ := Module.End.exists_eigenvalue s
    have hinv : ∀ σ α, ∀ v ∈ End.eigenspace s α, ρ σ v ∈ End.eigenspace s α := by
      intro σ α v hv
      rw [Module.End.mem_eigenspace_iff] at hv ⊢
      rw [← Module.End.mul_apply, (hcomm σ).eq, Module.End.mul_apply, hv, map_smul]
    set U := End.eigenspace s c
    set U' := ⨆ α ∈ ({c}ᶜ : Set ℂ), End.eigenspace s α
    have hU : ∀ σ, ∀ v ∈ U, ρ σ v ∈ U := fun σ => hinv σ c
    have hU' : ∀ σ, ∀ v ∈ U', ρ σ v ∈ U' := by
      intro σ v hv
      have : U' ≤ U'.comap (ρ σ) := iSup₂_le fun α hα w hw =>
        (le_iSup₂_of_le α hα le_rfl : End.eigenspace s α ≤ U') (hinv σ α w hw)
      exact this hv
    have hcompl : IsCompl U U' := by
      refine ⟨(Module.End.eigenspaces_iSupIndep s).disjoint_biSup (by simp), ?_⟩
      rw [codisjoint_iff, eq_top_iff, ← hss.iSup_eigenspace_eq_top]
      refine iSup_le fun α => ?_
      by_cases hα : α = c
      · subst hα; exact le_sup_left
      · exact le_sup_of_le_right (le_iSup₂_of_le α hα le_rfl)
    have hc0 : c ≠ 0 := by
      rintro rfl
      obtain ⟨v, hv, hv0⟩ := hc.exists_hasEigenvector
      apply hv0
      have h1 := Module.End.mem_eigenspace_iff.mp hv
      rw [zero_smul] at h1
      have h1' : ρ (frob h ^ m) v = 0 := by rw [← hsm]; exact h1
      have := congrArg (ρ (frob h ^ m)⁻¹) h1'
      rwa [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply,
        map_zero] at this
    have hUb : U ≠ ⊥ := hc
    have hU'b : U' ≠ ⊥ := by
      intro hb
      apply hsc
      refine ⟨c, hc0, LinearMap.ext fun v => ?_⟩
      have hv : v ∈ U := by
        have := hcompl.sup_eq_top
        rw [hb, sup_bot_eq] at this
        rw [this]; trivial
      rw [Module.End.mem_eigenspace_iff.mp hv]
      simp
    have hrk := Submodule.finrank_add_eq_of_isCompl hcompl
    have h1 : 0 < finrank ℂ U := Module.finrank_pos_iff.mpr (Submodule.nontrivial_iff_ne_bot.mpr hUb)
    have h2 : 0 < finrank ℂ U' :=
      Module.finrank_pos_iff.mpr (Submodule.nontrivial_iff_ne_bot.mpr hU'b)
    obtain ⟨y1, hS1, hy1⟩ := ih (finrank ℂ U) (by omega) U rfl (a0.resZero U hU).ρ
      (a0.resZero U hU).smooth (a0.resZero U hU).semisimple
    obtain ⟨y2, hS2, hy2⟩ := ih (finrank ℂ U') (by omega) U' rfl (a0.resZero U' hU').ρ
      (a0.resZero U' hU').smooth (a0.resZero U' hU').semisimple
    refine ⟨y1.lpSum y2, hsum _ _ hS1 hS2, fun σ => ?_⟩
    rw [WD.charPol_lpSum, hy1, hy2]
    exact (a0.charpoly_eq_mul_of_isCompl U U' hU hU' hcompl σ).symm

end Reduction

theorem WD.induction_lpSum_twist_finite : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w) (S : WD h → Prop), (∀ x y, S x → S y → S (x.lpSum y)) → (∀ x y, (∀ σ, x.charPol σ = y.charPol σ) → S x → S y) → (∀ (n : ℕ) (a : WDRep h (Fin n → ℂ)) (μ : Weil h →* ℂˣ) (hμ : IsSmooth μ), (Set.range a.ρ).Finite → S (WD.mk (a.twist μ hμ))) → ∀ x, S x := by
  intro E Ω _ _ _ _ _ A w h S hsum hchar hfin x
  induction x using WD.ind with
  | hP n a =>
  obtain ⟨y, hy, hyc⟩ := exists_of_lpSum_twist_finite S hsum hfin _ (Fin n → ℂ) rfl a.ρ a.smooth
    a.semisimple
  exact hchar y _ (fun σ => by rw [hyc, WD.charPol_mk]) hy

end GlobalTheory.WeilDeligne
end
end

