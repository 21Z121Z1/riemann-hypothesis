import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0003
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0011
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0408
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0311
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0417
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0401
import Formalism.SharpRestriction.LevelLetterCocycles.SumRepresentations
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SemisimpleOfInjective
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0418
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0005
import Formalism.SharpRestriction.LevelLetterCocycles.ArithmeticCylinders
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0006
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0238
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0564
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdelicUnitriangularMulMemUnipotentTimesIntegral
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsWildInertiaCyclotomicElement
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0009
import Formalism.LocalToGlobal.NormalizedHeckeFactors.CoverStd
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SplitExEveryDatum
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0007
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0008
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0014
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0015
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FinrankFiniteLeExponentialCocycles
section
noncomputable section

namespace GlobalTheory.HyodoFE

open Formalism Formalism.WeaklyAdmissibleFiltrations GlobalTheory.HyodoDef TensorProduct Module

section Generic

variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)
    {LL : Type} [Field LL] [Algebra Qp LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    (ρ : Representation LL G V)

theorem mem_Dcris_iff (x : V ⊗[Qp] B) : x ∈ Dcris PD ρ ↔ ∀ g, actVB PD ρ g x = x := by
  simp only [Dcris, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
    LinearMap.id_apply, sub_eq_zero]

theorem φVB_mem_Dcris {x : V ⊗[Qp] B} (hx : x ∈ Dcris PD ρ) :
    φVB PD (LL := LL) (V := V) x ∈ Dcris PD ρ := by
  rw [mem_Dcris_iff] at hx ⊢
  intro g
  rw [← GlobalTheory.CobCrisLift.φVB_act, hx g]

def oneSubφ : Dcris PD ρ →ₗ[LL] Dcris PD ρ :=
  (LinearMap.id - φVB PD (LL := LL) (V := V)).restrict (p := Dcris PD ρ) (q := Dcris PD ρ)
    (fun x hx => (Dcris PD ρ).sub_mem hx (φVB_mem_Dcris PD ρ hx))

variable [TopologicalSpace G] [TopologicalSpace V] [ContinuousAdd V] [ContinuousConstSMul LL V]

def pairs : Submodule LL ((G → V) × (V ⊗[Qp] B)) where
  carrier := {p | p.1 ∈ continuousCocycles ρ ∧ ∀ g, p.1 g ⊗ₜ[Qp] (1 : B) = actVB PD ρ g p.2 - p.2}
  zero_mem' := ⟨(continuousCocycles ρ).zero_mem, fun g => by simp⟩
  add_mem' := by
    rintro a b ⟨ha, hx⟩ ⟨hb, hy⟩
    refine ⟨(continuousCocycles ρ).add_mem ha hb, fun g => ?_⟩
    simp only [Prod.fst_add, Prod.snd_add, Pi.add_apply, add_tmul, hx, hy, map_add]
    abel
  smul_mem' := by
    rintro c a ⟨ha, hx⟩
    refine ⟨(continuousCocycles ρ).smul_mem c ha, fun g => ?_⟩
    simp only [Prod.smul_fst, Prod.smul_snd, Pi.smul_apply, map_smul, ← smul_sub, ← hx]
    rfl

def projZ : pairs PD ρ →ₗ[LL] finiteCocycles PD ρ :=
  LinearMap.codRestrict (finiteCocycles PD ρ) ((LinearMap.fst LL (G → V) (V ⊗[Qp] B)).comp (pairs PD ρ).subtype)
    (fun p => ⟨p.2.1, p.1.2, p.2.2⟩)

theorem projZ_surjective : Function.Surjective (projZ PD ρ) := by
  rintro ⟨c, hc, x, hx⟩
  exact ⟨⟨(c, x), hc, hx⟩, rfl⟩

def toDcris : pairs PD ρ →ₗ[LL] Dcris PD ρ :=
  LinearMap.codRestrict (Dcris PD ρ)
    (((LinearMap.id - φVB PD (LL := LL) (V := V)).comp (LinearMap.snd LL (G → V) (V ⊗[Qp] B))).comp
      (pairs PD ρ).subtype)
    (fun p => GlobalTheory.CobCrisLift.sub_φ_mem_Dcris PD ρ p.1.1 p.1.2 p.2.2)

theorem fst_mem_exponential_cocycles (p : pairs PD ρ) (hp : toDcris PD ρ p ∈ LinearMap.range (oneSubφ PD ρ)) :
    (p : (G → V) × (V ⊗[Qp] B)).1 ∈ crystallineCocycles PD ρ := by
  obtain ⟨e, he⟩ := hp
  have he' : (e : V ⊗[Qp] B) - φVB PD (LL := LL) (V := V) e
      = p.1.2 - φVB PD (LL := LL) (V := V) p.1.2 := congrArg Subtype.val he
  refine ⟨p.2.1, p.1.2 - e, ?_, fun g => ?_⟩
  · rw [map_sub]
    calc φVB PD (LL := LL) (V := V) p.1.2 - φVB PD (LL := LL) (V := V) e
        = (p.1.2 - (e : V ⊗[Qp] B)) + (((e : V ⊗[Qp] B) - φVB PD (LL := LL) (V := V) e)
          - (p.1.2 - φVB PD (LL := LL) (V := V) p.1.2)) := by abel
      _ = p.1.2 - e := by rw [he', sub_self, add_zero]
  · have hg := (mem_Dcris_iff PD ρ e).1 e.2 g
    rw [p.2.2 g, map_sub, hg]
    abel

theorem finrank_finite_cocycles_le [Module.Finite LL (Dcris PD ρ)] :
    finrank LL (finiteCocycles PD ρ) ≤ finrank LL (crystallineCocycles PD ρ) +
      finrank LL ↥(Dcris PD ρ ⊓ LinearMap.ker (φVB PD (LL := LL) (V := V) - LinearMap.id)) := by
  by_cases hf : Module.Finite LL (finiteCocycles PD ρ)
  swap
  · rw [Module.finrank_of_not_finite hf]; exact Nat.zero_le _
  obtain ⟨s, hs⟩ := (projZ PD ρ).exists_rightInverse_of_surjective
    (LinearMap.range_eq_top.2 (projZ_surjective PD ρ))
  set N := LinearMap.range (oneSubφ PD ρ) with hN
  let T : finiteCocycles PD ρ →ₗ[LL] (Dcris PD ρ ⧸ N) := N.mkQ ∘ₗ toDcris PD ρ ∘ₗ s
  have hle : crystallineCocycles PD ρ ≤ finiteCocycles PD ρ := fun c ⟨hc, x, _, hx⟩ => ⟨hc, x, hx⟩
  haveI : Module.Finite LL (crystallineCocycles PD ρ) :=
    Module.Finite.of_injective (Submodule.inclusion hle) (Submodule.inclusion_injective hle)
  have hmem : ∀ k : LinearMap.ker T, ((k : finiteCocycles PD ρ) : G → V) ∈ crystallineCocycles PD ρ := by
    intro k
    have hk : T k = 0 := LinearMap.mem_ker.1 k.2
    have h := fst_mem_exponential_cocycles PD ρ (s k) ((Submodule.Quotient.mk_eq_zero N).1 hk)
    have hsk : projZ PD ρ (s k) = k := LinearMap.congr_fun hs k
    have hv : ((s k : pairs PD ρ) : (G → V) × (V ⊗[Qp] B)).1 = ((k : finiteCocycles PD ρ) : G → V) :=
      congrArg Subtype.val hsk
    rwa [hv] at h
  have h1 : finrank LL (LinearMap.ker T) ≤ finrank LL (crystallineCocycles PD ρ) := by
    let j : LinearMap.ker T →ₗ[LL] crystallineCocycles PD ρ :=
      LinearMap.codRestrict (crystallineCocycles PD ρ) ((finiteCocycles PD ρ).subtype ∘ₗ (LinearMap.ker T).subtype) hmem
    have hj : Function.Injective j := by
      intro a b hab
      have h := congrArg Subtype.val hab
      simp only [j, LinearMap.codRestrict_apply, LinearMap.comp_apply, Submodule.subtype_apply] at h
      exact Subtype.ext (Subtype.ext h)
    exact LinearMap.finrank_le_finrank_of_injective hj
  have h2 : finrank LL (LinearMap.range T) ≤ finrank LL (Dcris PD ρ ⧸ N) := Submodule.finrank_le _
  have h3 := Submodule.finrank_quotient_add_finrank N
  have h4 := LinearMap.finrank_range_add_finrank_ker (oneSubφ PD ρ)
  have h5 := LinearMap.finrank_range_add_finrank_ker T
  set W := Dcris PD ρ ⊓ LinearMap.ker (φVB PD (LL := LL) (V := V) - LinearMap.id) with hW
  haveI : Module.Finite LL W :=
    Module.Finite.of_injective (Submodule.inclusion (inf_le_left : W ≤ Dcris PD ρ))
      (Submodule.inclusion_injective _)
  have hmemW : ∀ k : LinearMap.ker (oneSubφ PD ρ), ((k : Dcris PD ρ) : V ⊗[Qp] B) ∈ W := by
    intro k
    have hk : oneSubφ PD ρ k = 0 := LinearMap.mem_ker.1 k.2
    have hk' : ((k : Dcris PD ρ) : V ⊗[Qp] B) - φVB PD (LL := LL) (V := V) (k : Dcris PD ρ) = 0 :=
      congrArg Subtype.val hk
    refine Submodule.mem_inf.2 ⟨(k : Dcris PD ρ).2, ?_⟩
    rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply]
    rw [sub_eq_zero] at hk' ⊢
    exact hk'.symm
  have h6 : finrank LL (LinearMap.ker (oneSubφ PD ρ)) ≤ finrank LL W := by
    let j : LinearMap.ker (oneSubφ PD ρ) →ₗ[LL] W :=
      LinearMap.codRestrict W ((Dcris PD ρ).subtype ∘ₗ (LinearMap.ker (oneSubφ PD ρ)).subtype) hmemW
    have hj : Function.Injective j := by
      intro a b hab
      have h := congrArg Subtype.val hab
      simp only [j, LinearMap.codRestrict_apply, LinearMap.comp_apply, Submodule.subtype_apply] at h
      exact Subtype.ext (Subtype.ext h)
    exact LinearMap.finrank_le_finrank_of_injective hj
  have h7 : finrank LL N = finrank LL (LinearMap.range (oneSubφ PD ρ)) := rfl
  omega

end Generic

end GlobalTheory.HyodoFE

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N GlobalTheory.HyodoDef GlobalTheory.Pst TensorProduct Module

theorem GlobalTheory.HyodoFE.finrank_finite_le_exponential_add : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ (K : FinExt l) (V : Type) [AddCommGroup V] [Module ℚ_[l] V] [FiniteDimensional ℚ_[l] V] [TopologicalSpace V] [IsModuleTopology ℚ_[l] V] [ContinuousAdd V] [ContinuousConstSMul ℚ_[l] V] (ρ : Representation ℚ_[l] ↥(GK K) V), (∀ v, Continuous fun g => ρ g v) → IsDR (P.PD K) ρ → finrank ℚ_[l] ↥(finiteCocycles (P.PD K) ρ) ≤ finrank ℚ_[l] ↥(crystallineCocycles (P.PD K) ρ) + finrank ℚ_[l] ↥(Dcris (P.PD K) ρ ⊓ LinearMap.ker (φVB (P.PD K) (LL := ℚ_[l]) (V := V) - LinearMap.id)) := by
  intro l _ P AI _ K V _ _ _ _ _ _ _ ρ _ hdR
  haveI := GlobalTheory.DcrisFin.dcris_finite_of_isDR l P K V ρ hdR
  exact GlobalTheory.HyodoFE.finrank_finite_cocycles_le (P.PD K) ρ
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GaloisRepTupleRelationMemPowSpanStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.galoisRepTuple_relation_mem_pow_span : ∀ (l : ℕ) [Fact l.Prime] (Γ : Type) [Group Γ] (a : ℕ) (r : Γ →* GL (Fin a) (Om l)) (m : ℕ) (ρs : Fin m → (Γ →* GL (Fin a) (Om l))) (c N : ℕ) (cs : Fin m → Om l), (∀ (n : ℕ) (f : Γ →₀ ℤ_[l]), (∀ g, ‖((f.sum fun h c => zOm l c • ((r h : GL (Fin a) (Om l)) : Matrix (Fin a) (Fin a) (Om l))) * ((r g : GL (Fin a) (Om l)) : Matrix (Fin a) (Fin a) (Om l))).trace‖ ≤ ((l : ℝ)⁻¹) ^ (n + c)) → ∃ f' : Γ →₀ ℤ_[l], (f.sum fun h c => zOm l c • ((r h : GL (Fin a) (Om l)) : Matrix (Fin a) (Fin a) (Om l))) = (l : Om l) ^ n • (f'.sum fun h c => zOm l c • ((r h : GL (Fin a) (Om l)) : Matrix (Fin a) (Fin a) (Om l)))) → (∀ g, ‖trc r g - ∑ k, cs k * trc (ρs k) g‖ ≤ ((l : ℝ)⁻¹) ^ (N + c)) → ∀ G : Γ →₀ ℤ_[l], (G.sum fun g c => zOm l c • GlobalTheory.TraceConjugationCover.tup ρs g) = 0 → ∃ f' : Γ →₀ ℤ_[l], (G.sum fun h c => zOm l c • ((r h : GL (Fin a) (Om l)) : Matrix (Fin a) (Fin a) (Om l))) = (l : Om l) ^ N • (f'.sum fun h c => zOm l c • ((r h : GL (Fin a) (Om l)) : Matrix (Fin a) (Fin a) (Om l))) := by
  first | (exact @GlobalTheory.CovKer.kerB) | (exact GlobalTheory.CovKer.kerB) | (intros; apply GlobalTheory.CovKer.kerB  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GaloisRepTupleSpanSaturationBoundStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.galoisRepTuple_span_saturation_bound : ∀ (l : ℕ) [Fact l.Prime] (Γ : Type) [Group Γ] (a m : ℕ) (ρs : Fin m → (Γ →* GL (Fin a) (Om l))) (t : Fin m → Finset (Matrix (Fin a) (Fin a) (Om l))), (∀ k, ∃ c' : Matrix (Fin a) (Fin a) (Om l) → ℤ_[l], ∑ y ∈ t k, zOm l (c' y) • y = 1) → (∀ k g, ∀ x ∈ t k, ∃ c' : Matrix (Fin a) (Fin a) (Om l) → ℤ_[l], ((ρs k g : GL (Fin a) (Om l)) : Matrix (Fin a) (Fin a) (Om l)) * x = ∑ y ∈ t k, zOm l (c' y) • y) → ∃ u : ℕ, ∀ N M : ℕ, N + u ≤ M → ∀ H : Γ →₀ ℤ_[l], (H.sum fun g c => zOm l c • GlobalTheory.TraceConjugationCover.tup ρs g) ∈ GlobalTheory.TraceConjugationCover.latL t M → ∃ H' : Γ →₀ ℤ_[l], (H.sum fun g c => zOm l c • GlobalTheory.TraceConjugationCover.tup ρs g) = (l : Om l) ^ N • (H'.sum fun g c => zOm l c • GlobalTheory.TraceConjugationCover.tup ρs g) := by
  first | (exact @GlobalTheory.CovSat.satA) | (exact GlobalTheory.CovSat.satA) | (intros; apply GlobalTheory.CovSat.satA  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GaloisRepsCuspidal
section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Module

noncomputable section

namespace GlobalTheory.GaloisFromAdm

theorem placesOver_finite (D : D7) (l : ℕ) (hl : l ≠ 0) : (placesOver D.host.E l).Finite := by
  have h0 : Ideal.span {((l : ℕ) : 𝓞 D.host.E)} ≠ 0 := by
    simpa using hl
  exact (Ideal.finite_factors h0).subset fun v hv => Ideal.dvd_span_singleton.2 hv

theorem main : ∀ D : D7, SumRepresentations.adm2 D → GlobalTheory.BlockComplement.GaloisRepsCusp D := by
  intro D h i a ha π hc hr
  obtain ⟨ρ, hcont, hss, haway, -⟩ := (h i).1 a ha π hc hr
  refine ⟨ρ, hcont, hss, ?_⟩
  have hfin := placesOver_finite D (D.nd.l i) (Fact.out : (D.nd.l i).Prime).ne_zero
  filter_upwards [D.naut.locG_unr_ae π, hfin.eventually_cofinite_notMem] with w hu hw B φ hB hφ
  rw [D.naut.wdOf_frob i ρ w hw hcont (by rw [(haway w hw).1]; exact (D.naut.unr_tw _ _).2 hu) B φ hB hφ,
    (haway w hw).1]
  rfl

end GlobalTheory.GaloisFromAdm

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GaloisTransitiveOnPrimePowerRootSystemsStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.galois_transitive_on_prime_power_root_systems : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (π : ↥(OL K)), Prime π → ∀ y z : ℕ → Om l, y 0 = ((π : ↥K.1) : Om l) → z 0 = ((π : ↥K.1) : Om l) → (∀ n, y (n + 1) ^ l = y n) → (∀ n, z (n + 1) ^ l = z n) → ∃ g : ↥(GK K), ∀ n, (g : GQ l) (y n) = z n := by
  first | exact @GlobalTheory.galois_transitive_on_root_systems_of_prime | exact GlobalTheory.galois_transitive_on_root_systems_of_prime | (intros; apply GlobalTheory.galois_transitive_on_root_systems_of_prime <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GelfandGraevCharacterGLnNormAndReciprocity
section
open GlobalTheory.GLq Formalism.MainNotions.ArithmeticCylinders Polynomial
open scoped Classical

noncomputable section

namespace GlobalTheory.GLq.GGNorm

variable {g : ℕ} [Fact g.Prime]

theorem wh_formula (ψ : AddChar (ZMod g) ℂ) {n : ℕ} (χ : Gn g n → ℂ) :
    wh ψ χ = ((Finset.univ.filter fun u : Gn g n => IsUniUp (u : Mt g n)).card : ℂ)⁻¹ *
      ∑ u : Gn g n, (if IsUniUp (u : Mt g n) then
        (ψ (∑ i ∈ Finset.range (n - 1), entN (u : Mt g n) i (i + 1)))⁻¹ else 0) * χ u := by
  unfold wh tr eU eDat
  simp only [MonoidAlgebra.coeff_smul, MonoidAlgebra.coeff_sum, MonoidAlgebra.coeff_single, Finsupp.smul_apply,
    Finsupp.finsetSum_apply, Finsupp.single_apply, smul_eq_mul]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [mul_assoc]
  congr 2
  rw [Finset.sum_ite_eq']
  simp

theorem gg_term_inv (ψ : AddChar (ZMod g) ℂ) {n : ℕ} (u : Gn g n) :
    (if IsUniUp ((u⁻¹ : Gn g n) : Mt g n) then
        ψ (∑ i ∈ Finset.range (n - 1), entN ((u⁻¹ : Gn g n) : Mt g n) i (i + 1)) else 0) =
      if IsUniUp (u : Mt g n) then (ψ (∑ i ∈ Finset.range (n - 1), entN (u : Mt g n) i (i + 1)))⁻¹ else 0 := by
  by_cases hu : IsUniUp (u : Mt g n)
  · have hi := GlobalTheory.BadCount.Inh.isUniUp_inv u hu
    rw [if_pos hi, if_pos hu]
    have h := GlobalTheory.BadCount.Inh.sd_mul hi hu
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one, GlobalTheory.BadCount.Inh.sd_one] at h
    have e : (∑ i ∈ Finset.range (n - 1), entN ((u⁻¹ : Gn g n) : Mt g n) i (i + 1)) =
        -(∑ i ∈ Finset.range (n - 1), entN (u : Mt g n) i (i + 1)) :=
      eq_neg_of_add_eq_zero_left h.symm
    rw [e, AddChar.map_neg_eq_inv]
  · have hi : ¬ IsUniUp ((u⁻¹ : Gn g n) : Mt g n) := fun h =>
      hu (by simpa using GlobalTheory.BadCount.Inh.isUniUp_inv u⁻¹ h)
    rw [if_neg hi, if_neg hu]

theorem ip_gg (ψ : AddChar (ZMod g) ℂ) (n : ℕ) (χ : Gn g n → ℂ) (hχ : IsClass χ) :
    ip χ (gg ψ n) = wh ψ χ := by
  set c : ℂ := ((Finset.univ.filter fun u : Gn g n => IsUniUp (u : Mt g n)).card : ℂ)⁻¹ with hc
  set F : Gn g n → ℂ := fun z => if IsUniUp (z : Mt g n) then
    ψ (∑ i ∈ Finset.range (n - 1), entN (z : Mt g n) i (i + 1)) else 0 with hF
  have hgg : ∀ x, gg ψ n x = c * ∑ y : Gn g n, F (y⁻¹ * x * y) := fun x => rfl
  have hinner : ∀ y : Gn g n, ∑ x : Gn g n, χ x * F (y⁻¹ * x⁻¹ * y) = ∑ u : Gn g n, χ u * F u⁻¹ := by
    intro y
    let e : Gn g n ≃ Gn g n :=
      ⟨fun x => y⁻¹ * x * y, fun u => y * u * y⁻¹, fun x => by group, fun u => by group⟩
    refine Fintype.sum_equiv e _ _ fun x => ?_
    have h1 : χ (y⁻¹ * x * y) = χ x := by
      have := hχ x y⁻¹
      rwa [inv_inv] at this
    have h2 : y⁻¹ * x⁻¹ * y = (y⁻¹ * x * y)⁻¹ := by group
    change χ x * F (y⁻¹ * x⁻¹ * y) = χ (y⁻¹ * x * y) * F (y⁻¹ * x * y)⁻¹
    rw [h1, h2]
  have hG : (Fintype.card (Gn g n) : ℂ) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  have e1 : ∑ x : Gn g n, χ x * gg ψ n x⁻¹ = c * ∑ y : Gn g n, ∑ x : Gn g n, χ x * F (y⁻¹ * x⁻¹ * y) := by
    simp only [hgg, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun y _ => Finset.sum_congr rfl fun x _ => by ring
  have e2 : wh ψ χ = c * ∑ u : Gn g n, χ u * F u⁻¹ := by
    rw [wh_formula]
    congr 1
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [mul_comm]
    congr 1
    exact (gg_term_inv ψ u).symm
  unfold ip
  rw [e1, e2, Finset.sum_congr rfl fun y _ => hinner y, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [mul_left_comm, ← mul_assoc, ← mul_assoc, mul_assoc c, inv_mul_cancel₀ hG, mul_one]

theorem wh_gg (ψ : AddChar (ZMod g) ℂ) (hψ : ψ ≠ 1) (n : ℕ) (hn : 0 < n) :
    wh ψ (gg ψ n) = (g : ℂ) ^ n - (g : ℂ) ^ (n - 1) := by
  have h1 := GlobalTheory.GLm.GGSum.sum_wh_gg g ψ hψ n
  have h2 := GlobalTheory.GLm.GGSum.sum_wh_gg g ψ hψ (n - 1)
  rw [Nat.sub_add_cancel hn] at h2
  rw [Finset.sum_range_succ, h2] at h1
  linear_combination h1

theorem gg_norm : ∀ (g : ℕ) [Fact g.Prime] (ψ : AddChar (ZMod g) ℂ), ψ ≠ 1 → ∀ n : ℕ, 0 < n →
    wh ψ (gg ψ n) = (g : ℂ) ^ n - (g : ℂ) ^ (n - 1) ∧
      ∀ χ : Gn g n → ℂ, IsClass χ → ip χ (gg ψ n) = wh ψ χ :=
  fun _ _ ψ hψ n hn => ⟨wh_gg ψ hψ n hn, fun χ hχ => ip_gg ψ n χ hχ⟩

end GlobalTheory.GLq.GGNorm
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HasSumUnfoldingOfComplexInvariantIntegrableStatement
section
open NumberField IsDedekindDomain Matrix Formalism.UG GlobalTheory.CuspRep MeasureTheory
open scoped ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hasSum_unfolding_of_complex_invariant_integrable : ∀ {α ι : Type} [MeasurableSpace α] [Countable ι] (μ : Measure α) (𝓕 A : Set α) (c : ι → ℝ), (∀ i, 0 < c i) →
    ∀ (T : ι → α → α), (∀ i, Measurable (T i)) → ∀ (H : Set (α → α)),
    (∀ f : α → ℝ≥0∞, Measurable f → (∀ h ∈ H, ∀ x, f (h x) = f x) →
      ∫⁻ x in 𝓕, f x ∂μ = ∑' i, ENNReal.ofReal (c i) * ∫⁻ x in A, f (T i x) ∂μ) →
    ∀ B : α → ℂ, Measurable B → Integrable B (μ.restrict 𝓕) → (∀ h ∈ H, ∀ x, B (h x) = B x) →
      (∀ i, Integrable (fun x => B (T i x)) (μ.restrict A)) ∧
        HasSum (fun i => (c i : ℂ) * ∫ x in A, B (T i x) ∂μ) (∫ x in 𝓕, B x ∂μ) := by
  first | exact @GlobalTheory.UnfoldCplx.hasSum_complex | exact GlobalTheory.UnfoldCplx.hasSum_complex | (intros; apply GlobalTheory.UnfoldCplx.hasSum_complex <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HeckeEigenvalueSystemSetFinite
section
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 NumberField IsDedekindDomain Polynomial GlobalTheory.EtaJoin GlobalTheory.CoefDuty

namespace GlobalTheory.EigFinite

theorem eigSet_finite : HeckeStdPlain → ∀ (D : D7) (μ : D.what₂.Tup) (j : ℕ) (X : MtReal D μ j) (l : ℕ) (Q : Finset (PlE D.host)) (B : Set (HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)))), NG.HypOutside X.J X.χ B → (∀ v k (s : SplitPlace D.host.E), GenAt D l Q v k → IsConjPl D.host v s.w → s.v ∉ B) → (EigSet X l Q).Finite := by
  intro hP D μ j X l Q B hB hBv
  classical
  have hex := GlobalTheory.SplitConjPlace.splitEx_all D
  let ι := {p : PlE D.host × ℕ // GenAt D l Q p.1 p.2}
  have hch : ∀ i : ι, ∃ (s : SplitPlace D.host.E) (ϖ : s.v.adicCompletion (maximalRealSubfield D.host.E)),
      IsConjPl D.host i.1.1 s.w ∧ IsUnif D.host.E s.v ϖ := fun i => hex i.1.1 i.2.1
  choose s ϖ hs hϖ using hch
  have hfact := fun i : ι => hP D.host.E D.R.nV X.wt X.J X.χ B X.J_open hB (s i) (ϖ i) i.1.2
    (hBv _ _ _ i.2 (hs i)) (hϖ i) i.2.2.2.2.2.1 i.2.2.2.2.2.2
  have hTS : ∀ y, X.real y ∈ NG.TypeSp X.wt.ρ X.J X.χ := fun y => X.real_range ▸ LinearMap.mem_range_self X.real y
  have hmem : ∀ (i : ι) (y : D.what₂.Mt μ j), ∃ y', X.real y' = NG.tN X.J (s i) (ϖ i) i.1.2 (X.real y) := fun i y => by
    have h := (hfact i).1 _ (hTS y)
    rw [← X.real_range] at h
    exact h
  choose g hg using hmem
  have h0 : ∀ i : ι, NG.tN X.J (s i) (ϖ i) i.1.2 0 = 0 := fun i => by
    have h := (hfact i).2.1 0 (Submodule.zero_mem _) 0 (Submodule.zero_mem _) 1
    simp only [one_smul, add_zero] at h
    simpa using h
  let op : ι → Module.End ℂ (D.what₂.Mt μ j) := fun i =>
    { toFun := g i
      map_add' := fun y y' => X.real_inj (by
        rw [hg, map_add, map_add, hg, hg]
        have h := (hfact i).2.1 _ (hTS y) _ (hTS y') 1
        simpa using h)
      map_smul' := fun c y => X.real_inj (by
        rw [hg, map_smul, map_smul, hg]
        have h := (hfact i).2.1 _ (hTS y) 0 (Submodule.zero_mem _) c
        simpa [h0] using h) }
  have hop : ∀ i y, X.real (op i y) = NG.tN X.J (s i) (ϖ i) i.1.2 (X.real y) := fun i y => hg i y
  have hcomm : ∀ i i' : ι, Commute (op i) (op i') := fun i i' => by
    ext y
    apply X.real_inj
    show X.real (op i (op i' y)) = X.real (op i' (op i y))
    rw [hop, hop, hop, hop]
    exact (hfact i).2.2.1 (s i') (ϖ i') i'.1.2 (hBv _ _ _ i'.2 (hs i')) (hϖ i') i'.2.2.2.2.2.1 i'.2.2.2.2.2.2 _ (hTS y)
  have hind := Module.End.independent_iInf_maxGenEigenspace_of_forall_mapsTo op
    (fun i i' φ => Module.End.mapsTo_maxGenEigenspace_of_comm (hcomm i' i) φ)
  have hfin : {χ : ι → ℂ | ⨅ i, (op i).maxGenEigenspace (χ i) ≠ ⊥}.Finite :=
    Set.finite_coe_iff.mp (@Finite.of_fintype _ hind.fintypeNeBotOfFiniteDimensional)
  let Φ : (PlE D.host → ℕ → ℂ) → (ι → ℂ) := fun c i => c i.1.1 i.1.2
  apply Set.Finite.of_finite_image (f := Φ)
  · apply hfin.subset
    rintro _ ⟨c, ⟨-, y, hy0, hy⟩, rfl⟩
    show ⨅ i, (op i).maxGenEigenspace (c i.1.1 i.1.2) ≠ ⊥
    intro hbot
    apply hy0
    have hyin : y ∈ ⨅ i, (op i).maxGenEigenspace (c i.1.1 i.1.2) := by
      rw [Submodule.mem_iInf]
      intro i
      apply Module.End.eigenspace_le_maxGenEigenspace
      rw [Module.End.mem_eigenspace_iff]
      apply X.real_inj
      rw [hop, map_smul]
      exact hy i.1.1 i.1.2 (s i) (ϖ i) i.2 (hs i) (hϖ i)
    rw [hbot] at hyin
    exact (Submodule.mem_bot ℂ).1 hyin
  · rintro c ⟨hc, -⟩ c' ⟨hc', -⟩ hcc
    funext v k
    by_cases h : GenAt D l Q v k
    · exact congrFun hcc ⟨(v, k), h⟩
    · rw [hc v k h, hc' v k h]

end GlobalTheory.EigFinite
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HeckeStableLocalLatticeOfIntegral
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 NumberField IsDedekindDomain Polynomial GlobalTheory.EtaJoin GlobalTheory.CoefDuty

noncomputable section

namespace GlobalTheory.LatStab

theorem jMt_injective (D : D7) (μ : D.what₂.Tup) (j : ℕ) : Function.Injective (D.what₂.jMt μ j) := by
  classical
  let b := Module.Free.chooseBasis D.what₂.LL (D.what₂.MtL μ j)
  have hli := (D.what₂.jMt_basis μ j b).1
  refine (injective_iff_map_eq_zero _).2 fun x hx => ?_
  have hx' : x = ∑ i ∈ (b.repr x).support, b.repr x i • b i := by
    conv_lhs => rw [← b.linearCombination_repr x]
    rw [Finsupp.linearCombination_apply]; rfl
  rw [hx', map_sum] at hx
  simp only [map_smulₛₗ] at hx
  have h0 := linearIndependent_iff'.1 hli _ _ hx
  apply b.repr.injective
  ext i
  by_cases hi : i ∈ (b.repr x).support
  · simpa using h0 i hi
  · simpa using Finsupp.notMem_support_iff.1 hi

theorem latStable_of_latInt : ∀ (D : D7) (M : MtFam D) (B : NLocBase D M) (j : ℕ) (h1 : 1 ≤ j) (h2 : j ≤ D.R.m)
    (w : D.what₂.places.Pl), LatInt D M (B.Qc j w) j h1 h2 w → LatStable B j w := by
  intro D M B j h1 h2 w hI v k hvk x hx
  classical
  obtain ⟨s, ϖ, hcj, hu⟩ := GlobalTheory.SplitConjPlace.splitEx_all D v hvk.1
  have hinj := jMt_injective D (D.what₂.muTw w) j
  let f : D.what₂.Mt (D.what₂.muTw w) j → D.what₂.MtL (D.what₂.muTw w) j := fun g =>
    if h : g ∈ Set.range (D.what₂.jMt (D.what₂.muTw w) j) then h.choose else 0
  have hf : ∀ g ∈ (D.what₂.MtLat (D.what₂.muTw w) j).gen, D.what₂.jMt (D.what₂.muTw w) j (f g) = g := by
    intro g hg
    have h := hI.1 g hg
    simp only [f, dif_pos h]
    exact h.choose_spec
  have key : ∀ y ∈ genSet D (D.what₂.muTw w) j, B.hK j w v k (B.iV j w y) ∈ latLoc B j w := by
    intro y hy
    obtain ⟨c, hc0, hcE⟩ := hI.2 v k s ϖ hvk hcj hu _ hy
    have e1 := B.hL_def j w h1 h2 v k s ϖ hvk hcj hu y
    rw [hcE] at e1
    have e2 := (M (D.what₂.muTw w) j h1 h2).real_inj e1
    have e3 : B.hL j w v k y = ∑ g ∈ (D.what₂.MtLat (D.what₂.muTw w) j).gen, c g • f g := by
      apply hinj
      rw [e2, map_sum]
      refine Finset.sum_congr rfl fun g hg => ?_
      rw [map_smulₛₗ, hf g hg]
    rw [B.hK_def, e3, map_sum]
    refine Submodule.sum_mem _ fun g hg => ?_
    rw [map_smulₛₗ]
    obtain ⟨o, ho⟩ := (B.ec_w j w (c g)).1 (hc0 g)
    rw [← ho, algebraMap_smul]
    refine Submodule.smul_mem _ _ (Submodule.subset_span ⟨f g, ?_, rfl⟩)
    show D.what₂.jMt (D.what₂.muTw w) j (f g) ∈ (D.what₂.MtLat (D.what₂.muTw w) j).gen
    rw [hf g hg]; exact hg
  have hle : latLoc B j w ≤ (latLoc B j w).comap ((B.hK j w v k).restrictScalars (B.Oc j w)) := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨y, hy, rfl⟩
    exact key y hy
  exact hle hx

end GlobalTheory.LatStab

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HkFrobOfAttachedStatement
section
open GlobalTheory.TripleGal Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hkFrob_of_attached : ∀ (D : D7) (bkP : BlochKatoReduction.BK D) (i : D.ntw.Tw) (s : D.ntw.Sig i), TripleAtt D.naut bkP i s → HkFrob i s := by
  first | exact @GlobalTheory.TripleGal.HkFrobProof.hkFrob_of_tripleAtt | exact GlobalTheory.TripleGal.HkFrobProof.hkFrob_of_tripleAtt | (intros; apply GlobalTheory.TripleGal.HkFrobProof.hkFrob_of_tripleAtt <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HodgeAdaptedBasisGaloisActionBdRPlusStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hodgeAdaptedBasis_galois_action_bdRPlus : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (C : Core l) (d : ℕ) (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) ℤ_[l]) (H : Hodge C (bk.ev bk.E) (fun g => (ρ g).map (zOm l)) K) (g : ↥(GK K)) (w : Ainf l), Per.σA (g : GQ l) (bk.ev bk.E) = bk.ev bk.E * w → (ρ g).map ((aDp l).comp (Per.zA l)) * H.V.map (Per.σDp (g : GQ l)) * Matrix.diagonal (fun j => aDp l w ^ H.p j) = aDp l w ^ H.q • H.V := by
  first | (exact @GlobalTheory.BKLim.GalAdapted.gal_V) | (exact GlobalTheory.BKLim.GalAdapted.gal_V) | (intros; apply GlobalTheory.BKLim.GalAdapted.gal_V  <;> assumption)
end

