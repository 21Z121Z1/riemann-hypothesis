import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1308
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0012
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0004
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0003
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0207
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle0004
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0009
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0006
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.CuspRapidDecaySiegelGL
import Development.AbelianVarietyTheory.Definitions.Divisors.LineOppositeParabolicUnitaryLeviSectionEq
import Development.AbelianVarietyTheory.Definitions.Foundations.IsSatVecUOfIsSphericalU
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsConstAlongSingleton
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1150
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.IsTemperedGLOfIsUnitaryLSeg
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle0005
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0004
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0009
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteUnitary
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0005
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.HeckeLAdicCharacterAboveIff
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0732
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0003
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0012
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsPolarizedTwistAbsPow
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0129
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.LocalLanglandsGL
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0002
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0051
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1305
import Development.AbelianVarietyTheory.Definitions.Divisors.IsSquareIntegrableIffMemL2
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0052
import Formalism.HarderNarasimhan.StatementPl
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0951
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemNonzeroLocusFormMap
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1200
import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.Bundle0001
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.RingKrullDimQuotientEqOfMemMinimalPrimes
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1306
import Development.AbelianVarietyTheory.Definitions.Divisors.DiagHermitianTrivialOfSumFourSquares
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
import Development.AbelianVarietyTheory.Definitions.Divisors.PrimitiveCrystalHodgeLiftClasses
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsNoetherianRingDualNumber
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1307
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0020
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsSmoothModerateOfIsAutFunSm
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0015

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralModuleFiniteQuotient
section
open Matrix GlobalTheory.TorFin
open scoped ContDiff

namespace GlobalTheory.TorFin

theorem pow_mul_mem_of_mul_mem {A : Type} [Ring A] [Algebra ℂ A] {I : Submodule ℂ A} {H : A}
    (hH : ∀ i ∈ I, H * i ∈ I) (m : ℕ) {x : A} (hx : x ∈ I) : H ^ m * x ∈ I := by
  induction m with
  | zero => simpa using hx
  | succ m ih => rw [pow_succ', mul_assoc]; exact hH _ ih

theorem finiteDimensional_span_pow_mul_pow :
    ∀ (A U W : Type) [Ring A] [Algebra ℂ A] [AddCommGroup U] [Module ℂ U] [AddCommGroup W] [Module ℂ W]
      (Z : Subalgebra ℂ A) (I : Submodule ℂ A) (H H' : A) (κ : A →ₗ[ℂ] U) (Λ : A →ₗ[ℂ] W), Commute H H' →
      (∀ i ∈ I, H * i ∈ I) → (∀ i ∈ I, H' * i ∈ I) → (∀ i ∈ I, ∀ z ∈ Z, i * z ∈ I) → (∀ i ∈ I, Λ i = 0) →
      IsIntMod Z I H → IsIntMod Z I H' → FiniteDimensional ℂ ((Subalgebra.toSubmodule Z).map κ) →
      (∀ z ∈ Z, κ z = 0 → ∀ T, Λ (T * z) = 0) →
      FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun p : ℕ × ℕ => Λ (H ^ p.1 * H' ^ p.2))) := by
  intro A U W _ _ _ _ _ _ Z I H H' κ Λ hc hHI hH'I hIZ hΛ ⟨N, hN⟩ ⟨N', hN'⟩ hfin hker
  set K : Submodule ℂ A := Subalgebra.toSubmodule Z with hK
  let κK : K →ₗ[ℂ] U := κ ∘ₗ K.subtype
  let f : ℕ × ℕ → K →ₗ[ℂ] W := fun p => Λ ∘ₗ LinearMap.mulLeft ℂ (H ^ p.1 * H' ^ p.2) ∘ₗ K.subtype
  have hle : ∀ p, LinearMap.ker κK ≤ LinearMap.ker (f p) := by
    intro p z hz
    simp only [LinearMap.mem_ker] at hz ⊢
    exact hker z.1 z.2 hz _
  have hQ : Module.Finite ℂ (K ⧸ LinearMap.ker κK) := by
    have hr : LinearMap.range κK = K.map κ := by
      simp [κK, LinearMap.range_comp, Submodule.range_subtype]
    haveI : Module.Finite ℂ (LinearMap.range κK) := by rw [hr]; exact hfin
    exact Module.Finite.equiv (κK.quotKerEquivRange).symm
  have hfp : ∀ p, Module.Finite ℂ (LinearMap.range (f p)) := by
    intro p
    rw [← Submodule.range_liftQ _ (f p) (hle p)]
    exact Module.Finite.range _
  let V : Submodule ℂ W := ⨆ p : Fin N × Fin N', LinearMap.range (f (p.1.1, p.2.1))
  haveI : Module.Finite ℂ V := by
    haveI := fun p : Fin N × Fin N' => hfp (p.1.1, p.2.1)
    infer_instance
  have hbase : ∀ i j, i < N → j < N' → ∀ z ∈ Z, Λ (H ^ i * H' ^ j * z) ∈ V := by
    intro i j hi hj z hz
    refine Submodule.mem_iSup_of_mem (⟨i, hi⟩, ⟨j, hj⟩) ⟨⟨z, hz⟩, ?_⟩
    simp [f, mul_assoc]
  have main : ∀ n i j, i + j ≤ n → ∀ z ∈ Z, Λ (H ^ i * H' ^ j * z) ∈ V := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
    intro i j hij z hz
    by_cases hi : N ≤ i
    · obtain ⟨ι, hι, s, hs, hsum⟩ := Submodule.mem_sup.1 hN
      have e : H ^ i * H' ^ j * z = H ^ (i - N) * (H' ^ j * (ι * z)) + H ^ (i - N) * H' ^ j * s * z := by
        rw [← pow_sub_mul_pow H hi, mul_assoc (H ^ (i - N)), (hc.pow_pow N j).eq, ← hsum]
        simp only [mul_add, add_mul, mul_assoc]
      rw [e, map_add, hΛ _ (pow_mul_mem_of_mul_mem hHI _ (pow_mul_mem_of_mul_mem hH'I _ (hIZ _ hι _ hz))), zero_add]
      clear e hsum
      induction hs using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨k, hk, zk, hzk, rfl⟩ := hx
        have e2 : H ^ (i - N) * H' ^ j * (H ^ k * zk) * z = H ^ (i - N + k) * H' ^ j * (zk * z) := by
          calc H ^ (i - N) * H' ^ j * (H ^ k * zk) * z = H ^ (i - N) * (H' ^ j * H ^ k) * (zk * z) := by
                simp only [mul_assoc]
            _ = H ^ (i - N) * (H ^ k * H' ^ j) * (zk * z) := by rw [(hc.pow_pow k j).eq]
            _ = _ := by rw [pow_add]; simp only [mul_assoc]
        rw [e2]
        exact ih (i - N + k + j) (by omega) _ _ le_rfl _ (Z.mul_mem hzk hz)
      | zero => simp
      | add x y _ _ hx hy => rw [mul_add, add_mul, map_add]; exact V.add_mem hx hy
      | smul c x _ hx => rw [mul_smul_comm, smul_mul_assoc, map_smul]; exact V.smul_mem c hx
    by_cases hj : N' ≤ j
    · obtain ⟨ι, hι, s, hs, hsum⟩ := Submodule.mem_sup.1 hN'
      have e : H ^ i * H' ^ j * z = H ^ i * (H' ^ (j - N') * (ι * z)) + H ^ i * H' ^ (j - N') * s * z := by
        rw [← pow_sub_mul_pow H' hj, ← hsum]
        simp only [mul_add, add_mul, mul_assoc]
      rw [e, map_add, hΛ _ (pow_mul_mem_of_mul_mem hHI _ (pow_mul_mem_of_mul_mem hH'I _ (hIZ _ hι _ hz))), zero_add]
      clear e hsum
      induction hs using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨k, hk, zk, hzk, rfl⟩ := hx
        have e2 : H ^ i * H' ^ (j - N') * (H' ^ k * zk) * z = H ^ i * H' ^ (j - N' + k) * (zk * z) := by
          rw [pow_add]; simp only [mul_assoc]
        rw [e2]
        exact ih (i + (j - N' + k)) (by omega) _ _ le_rfl _ (Z.mul_mem hzk hz)
      | zero => simp
      | add x y _ _ hx hy => rw [mul_add, add_mul, map_add]; exact V.add_mem hx hy
      | smul c x _ hx => rw [mul_smul_comm, smul_mul_assoc, map_smul]; exact V.smul_mem c hx
    exact hbase i j (by omega) (by omega) z hz
  apply Submodule.finiteDimensional_of_le (S₂ := V)
  rw [Submodule.span_le]
  rintro _ ⟨⟨i, j⟩, rfl⟩
  simpa using main (i + j) i j le_rfl 1 Z.one_mem

example : ∀ (A U W : Type) [Ring A] [Algebra ℂ A] [AddCommGroup U] [Module ℂ U] [AddCommGroup W] [Module ℂ W] (Z : Subalgebra ℂ A) (I : Submodule ℂ A) (H H' : A) (κ : A →ₗ[ℂ] U) (Λ : A →ₗ[ℂ] W), Commute H H' → (∀ i ∈ I, H * i ∈ I) → (∀ i ∈ I, H' * i ∈ I) → (∀ i ∈ I, ∀ z ∈ Z, i * z ∈ I) → (∀ i ∈ I, Λ i = 0) → IsIntMod Z I H → IsIntMod Z I H' → FiniteDimensional ℂ ((Subalgebra.toSubmodule Z).map κ) → (∀ z ∈ Z, κ z = 0 → ∀ T, Λ (T * z) = 0) → FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun p : ℕ × ℕ => Λ (H ^ p.1 * H' ^ p.2))) :=
  finiteDimensional_span_pow_mul_pow

end GlobalTheory.TorFin
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCosocleComp
section
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.LocLanglands GlobalTheory.JHMult

noncomputable section

namespace GlobalTheory.CosocleComp

variable {G H V W : Type} [Group G] [Group H] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

def subrepOfComp (ρ : Representation ℂ G V) (s : H →* G) (hs : Function.Surjective s) :
    Subrepresentation (ρ.comp s : Representation ℂ H V) ≃o Subrepresentation ρ where
  toFun S := ⟨S.toSubmodule, fun g v hv => by
    obtain ⟨h, rfl⟩ := hs g
    exact S.apply_mem_toSubmodule h hv⟩
  invFun S := ⟨S.toSubmodule, fun h _ hv => S.apply_mem_toSubmodule (s h) hv⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_rel_iff' := Iff.rfl

theorem isIrreducible_comp {ρ : Representation ℂ G V} {s : H →* G} (hs : Function.Surjective s)
    (h : ρ.IsIrreducible) : Representation.IsIrreducible (ρ.comp s : Representation ℂ H V) :=
  (subrepOfComp ρ s hs).isSimpleOrder_iff.2 h

theorem isCosocle_comp : ∀ (G H V W : Type) [Group G] [Group H] [AddCommGroup V] [Module ℂ V] [AddCommGroup W]
    [Module ℂ W] (σ : Representation ℂ G W) (π : Representation ℂ G V) (s : H →* G), Function.Surjective s →
    IsCosocle σ π → IsCosocle (σ.comp s) (π.comp s) := by
  intro G H V W _ _ _ _ _ _ σ π s hs h
  obtain ⟨hi, f, hf, hS⟩ := h
  let f' : Representation.IntertwiningMap (π.comp s : Representation ℂ H V) (σ.comp s : Representation ℂ H W) := ⟨f.toLinearMap, fun g => f.isIntertwining' (s g)⟩
  refine ⟨isIrreducible_comp hs hi, f', hf, fun S hS' => ?_⟩
  have h1 := hS (subrepOfComp π s hs S) ((OrderIso.isCoatom_iff (subrepOfComp π s hs) S).2 hS')
  have h2 := congrArg Subrepresentation.toSubmodule h1
  have inj : Function.Injective (Subrepresentation.toSubmodule (ρ := (π.comp s : Representation ℂ H V))) := by
    rintro ⟨a, _⟩ ⟨b, _⟩ rfl; rfl
  exact inj h2

end GlobalTheory.CosocleComp
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCuspFormOfConjPointwise
section
open NumberField IsDedekindDomain Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.ContraPair

noncomputable section

namespace GlobalTheory

theorem isCuspForm_of_conj_pointwise : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (C : Sm E a ≃ₗ⋆[ℂ] Sm E a), (∀ φ g, (C φ).1 g = starRingEnd ℂ (φ.1 g)) → (∀ o φ, act o (C φ) = C (act o φ)) → (∀ z ∈ Zalg E a, ∃ z' ∈ Zalg E a, ∀ φ, z (C φ) = C (z' φ)) → ∀ φ : Sm E a, IsCuspForm φ → IsCuspForm (C φ) := by
  intro E _ _ _ a C hC hact hZ φ hφ
  obtain ⟨h, hc⟩ := hφ
  refine ⟨⟨?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · intro γ g
    rw [hC, hC, h.left]
  · convert h.level using 1
    ext k
    change act (.fin k) (C φ) = C φ ↔ act (.fin k) φ = φ
    rw [hact]
    exact C.injective.eq_iff
  · have := h.kfin
    refine Submodule.finiteDimensional_of_le (S₂ := (Submodule.span ℂ (Set.range fun k => cptRep E a k φ)).map
      C.toLinearMap) (Submodule.span_le.2 ?_)
    rintro _ ⟨k, rfl⟩
    exact ⟨_, Submodule.subset_span ⟨k, rfl⟩, (hact (.cpt k) φ).symm⟩
  · have := h.zfin
    refine Submodule.finiteDimensional_of_le (S₂ := (Submodule.span ℂ ((fun z : Module.End ℂ (Sm E a) => z φ) ''
      Zalg E a)).map C.toLinearMap) (Submodule.span_le.2 ?_)
    rintro _ ⟨z, hz, rfl⟩
    obtain ⟨z', h1, h2⟩ := hZ z hz
    exact ⟨_, Submodule.subset_span ⟨z', h1, rfl⟩, (h2 φ).symm⟩
  · intro g
    obtain ⟨K, N, h1⟩ := h.growth g
    refine ⟨K, N, fun y => ?_⟩
    rw [hC, RCLike.norm_conj]
    exact h1 y
  · intro r hr0 hra _ _ μ 𝓕 hμ h𝓕 g
    have := hc r hr0 hra μ 𝓕 hμ h𝓕 g
    simp_rw [hC]
    rw [integral_conj, this, map_zero]

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIdTorusEltOne
section
noncomputable section

open NumberField Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.StdPar
open GlobalTheory.Doubling (absE conjUnit)
open scoped TensorProduct

namespace GlobalTheory.IdTorus

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) {r : ℕ} (X Y : Matrix (Fin n) (Fin r) E)

def IsIdTorusElt (l : Fin r → (AF F ⊗[F] E)ˣ) (a : GAd σ J) : Prop :=
  (matHom _ σ J a).1 * adMat F X = adMat F X * diagonal (fun k => ((l k : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E)) ∧
  (matHom _ σ J a).1 * adMat F Y = adMat F Y * diagonal (fun k => (((conjUnit σ (l k))⁻¹ : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E)) ∧
  ∀ z ∈ colPerp σ J X Set.univ ⊓ colPerp σ J Y Set.univ, (matHom _ σ J a).1 *ᵥ z = z

variable (F E) in

def archUnitF (c : ℝ) : (AF F)ˣ where
  val := ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (fun _ => Real.exp c, fun _ => (Real.exp c : ℂ)), 1)
  inv := ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (fun _ => Real.exp (-c), fun _ => (Real.exp (-c) : ℂ)), 1)
  val_inv := by
    refine Prod.ext ?_ (mul_one _)
    change _ * _ = (1 : InfiniteAdeleRing F)
    rw [← map_mul, ← (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm.map_one]
    congr 1
    refine Prod.ext (funext fun _ => ?_) (funext fun _ => ?_)
    · simp [← Real.exp_add]
    · simp [← Complex.exp_add]
  inv_val := by
    refine Prod.ext ?_ (mul_one _)
    change _ * _ = (1 : InfiniteAdeleRing F)
    rw [← map_mul, ← (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm.map_one]
    congr 1
    refine Prod.ext (funext fun _ => ?_) (funext fun _ => ?_)
    · simp [← Real.exp_add]
    · simp [← Complex.exp_add]

variable (F E) in

def archUnit (c : ℝ) : (AF F ⊗[F] E)ˣ := Units.map (algebraMap (AF F) (AF F ⊗[F] E)).toMonoidHom (archUnitF F c)

def torTrans (S : Finset (Fin r)) (φ : GAd σ J → ℂ) : Set (GAd σ J → ℂ) :=
  {f | ∃ l a, (∀ k ∉ S, l k = 1) ∧ IsIdTorusElt σ J X Y l a ∧ f = fun g => φ (a * g)}

theorem isIdTorusElt_one : IsIdTorusElt σ J X Y 1 1 := by
  refine ⟨?_, ?_, fun z _ => ?_⟩ <;> simp

@[simp] theorem archUnit_zero : archUnit F E 0 = 1 := by
  have : archUnitF F 0 = 1 := Units.ext (Prod.ext (by
    change (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm _ = 1
    rw [← (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm.map_one]
    congr 1
    refine Prod.ext (funext fun _ => ?_) (funext fun _ => ?_) <;> simp) rfl)
  rw [archUnit, this, map_one]

end GlobalTheory.IdTorus
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSphericalTwistAbsDetPowGL
section
open NumberField IsDedekindDomain
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.CuspRep GlobalTheory.SmGL GlobalTheory.DefiniteBC
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.TwistSph

theorem isSpherical_twist_absPow : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a : ℕ) (w : HeightOneSpectrum (𝓞 E))
    (σ : SmIrr (GL (Fin a) (w.adicCompletion E))) (s : ℝ), GlobalTheory.LGrp.IsSpherical σ.ρ (GlobalTheory.LFun.KGL w a) →
    GlobalTheory.SmGL.IsSpherical (σ.twist (CuspSub.locDet a (GlobalTheory.HeckeGal.Model.absPow E s) w)
      (CuspSub.isOpen_ker_locDet _ w)).ρ := by
  intro E _ _ _ a w σ s h
  have hK : GlobalTheory.SplitWeil.KO (w.adicCompletion E) (Fin a) = GlobalTheory.LFun.KGL w a :=
    GlobalTheory.SmGL.SphCompletion.KO_completion w a
  obtain ⟨v, hv, hv0⟩ := (Submodule.ne_bot_iff _).1 h
  rw [← hK] at hv
  refine (Submodule.ne_bot_iff _).2 ⟨v, fun g => ?_, hv0⟩
  have h1 : CuspSub.locDet a (GlobalTheory.HeckeGal.Model.absPow E s) w g.1 = 1 := by
    show (GlobalTheory.HeckeGal.Model.absPow E s).loc w (Matrix.GeneralLinearGroup.det g.1) = 1
    rw [GlobalTheory.HeightCounting.Blocks.loc_of_isAbsPow (GlobalTheory.HeckeGal.Model.absPow_isAbsPow E s) w]
    refine isUnram_absPow _ _ _ ?_
    obtain ⟨u, hu⟩ := g.2
    rw [← hu]
    have h2 : ((Matrix.GeneralLinearGroup.det (Matrix.GeneralLinearGroup.map
        (algebraMap (ValuativeRel.valuation (w.adicCompletion E)).integer (w.adicCompletion E)) u) :
          (w.adicCompletion E)ˣ) : w.adicCompletion E) =
        algebraMap (ValuativeRel.valuation (w.adicCompletion E)).integer (w.adicCompletion E) u.val.det := by
      rw [RingHom.map_det]; rfl
    rw [h2]
    exact (Valuation.Integers.isUnit_iff_valuation_eq_one (Valuation.integer.integers _)).1
      ((Matrix.isUnit_iff_isUnit_det _).1 u.isUnit)
  have h3 := hv g
  show ((CuspSub.locDet a (GlobalTheory.HeckeGal.Model.absPow E s) w g.1 : ℂˣ) : ℂ) • σ.ρ g.1 v = _
  rw [h1, Units.val_one, one_smul]
  exact h3

end GlobalTheory.TwistSph
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsotropicFlagStabilizerNotLowerWeightStatement
section
open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut
open scoped TensorProduct
open GlobalTheory.Mem.UnipCocompact
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isotropicFlagStabilizer_not_lower_weight : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (r : ℕ) (X Y : Matrix (Fin n) (Fin r) E) (d : Fin r → ℕ) (M : ℕ), (∀ j, d j < M) → Formalism.UG.cT (σ : E →+* E) X * J * X = 0 → Formalism.UG.cT (σ : E →+* E) Y * J * Y = 0 → Formalism.UG.cT (σ : E →+* E) X * J * Y = 1 → ∀ p ∈ parFlag σ J X d, ∀ a b, wt d M a < wt d M b → fam (adjA σ J) (idemA X (Formalism.UG.cT (σ : E →+* E) Y * J)) a * (matHom (AF F) σ J p).1 * fam (adjA σ J) (idemA X (Formalism.UG.cT (σ : E →+* E) Y * J)) b = 0 := by
  first | exact @GlobalTheory.UAut.NoLower.parFlag_no_lower | exact GlobalTheory.UAut.NoLower.parFlag_no_lower | (intros; apply GlobalTheory.UAut.NoLower.parFlag_no_lower <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KawamataViehwegVanishingNumberFieldTwist
section
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.HermTools GlobalTheory.Vanishing GlobalTheory.Adelic GlobalTheory.HilbertSamuel GlobalTheory.ChowHt GlobalTheory.TangentOrigin
open GlobalTheory.IndefiniteRowSideFullHecke.RadicalPowers
open GlobalTheory.HSCore GlobalTheory.QCoh
open GlobalTheory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HSCore.VanishNumberField

open GlobalTheory.AbLaw

theorem subsingleton_of_tensor {k E V : Type} [Field k] [Field E] [Algebra k E] [AddCommGroup V] [Module k V]
    (h : Subsingleton (TensorProduct k E V)) : Subsingleton V := by
  by_contra hV
  rw [not_subsingleton_iff_nontrivial] at hV
  exact not_nontrivial_iff_subsingleton.2 h (Module.FaithfullyFlat.lTensor_nontrivial k E V)

theorem subsingleton_coh_of_pull {k E : Type} [Field k] [Field E] [Algebra k E] {X X' : Scheme.{0}}
    {f : X ⟶ Spec (CommRingCat.of k)} {f' : X' ⟶ Spec (CommRingCat.of E)} {π : X' ⟶ X} [QuasiCompact f] [IsSeparated f]
    (H : IsPullback π f' f (Spec.map (CommRingCat.ofHom (algebraMap k E)))) {M : LB X} (hM : M.IsLB) (n : ℕ)
    (h : Subsingleton (coh (twist (structureModule X') (M.pull π)) n)) :
    Subsingleton (coh (twist (structureModule X) M) n) := by
  letI := algebraΓOfHom f
  letI := algebraΓOfHom f'
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  have := isAffineHom_diagonal_of_isSeparated f
  obtain ⟨m, D, hD, hc⟩ := exists_fin_affine_cover (X := X) (V := ⊤) isCompact_univ
  have hD' := isAffineOpen_finset_biInf hD
  obtain ⟨e₁⟩ := FieldChangeInter.nonempty_coh_equiv f hM hc hD' n
  obtain ⟨e₂⟩ := FieldChangeInter.nonempty_coh_equiv f' (LB.isLB_pull hM π) (D := fun i => π ⁻¹ᵁ D i)
    (by rw [← Scheme.Hom.preimage_iSup, hc]; rfl) (fun s hs => isAffineOpen_biInf_preimage H (hD' s hs)) n
  obtain ⟨e₃⟩ := FieldChangeInter.nonempty_homology_equiv E (cechLB f M D) n
  have e₄ := ((HomologicalComplex.homologyFunctor _ _ n).mapIso (cechLBBaseChangeIso hM H hD')).toLinearEquiv
  have h₁ : Subsingleton (TensorProduct k E ((cechLB f M D).homology n)) :=
    (e₃.symm.toEquiv.trans (e₄.toEquiv.trans e₂.toEquiv)).subsingleton_congr.2 h
  exact e₁.symm.toEquiv.subsingleton_congr.2 (subsingleton_of_tensor h₁)

theorem topologicalKrullDim_eq_of_smooth {k : Type} [Field k] {Y : Scheme.{0}} [Nonempty Y] (p : Y ⟶ Sp k) (D : ℕ)
    (h : SmoothOfRelativeDimension D p) : topologicalKrullDim Y = D := by
  have key : topologicalKrullDim (Set.univ : Set Y) = D := by
    refine topologicalKrullDim_eq_of_forall_exists_isOpen Set.univ_nonempty fun x _ => ?_
    obtain ⟨U, hU, hx, -⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.1 Y.isBasis_affineOpens
      (TopologicalSpace.Opens.mem_top x)
    replace hU : IsAffineOpen (X := Y) U := hU
    refine ⟨U, U.isOpen, hx, ?_⟩
    rw [Set.inter_univ, topologicalKrullDim_eq_of_isEmbedding hU.fromSpec.isOpenEmbedding.isEmbedding hU.range_fromSpec]
    exact (PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim (R := Γ(Y, U))).trans
      (SmoothDim.ringKrullDim_affineOpen k _ p _ h U hU ⟨x, hx⟩)
  rw [← key]
  exact (topologicalKrullDim_eq_of_isEmbedding (e := (id : Y → Y)) Topology.IsEmbedding.id Set.range_id).symm

theorem vanishFrom_adj : Quoted → ∀ (K : Type) [Field K] [NumberField K] (G : Geo K), IsNef K G.LA → IsBig K G.LA →
    VanishFrom G.L (GlobalTheory.LB.toMod (tens G.K.bundle G.LA)) 0 := by
  intro Q K _ _ G hnef hbig j hj q hq
  lift j to ℕ using hj
  let Ω := AlgebraicClosure K
  let S := G.toLinSys
  have hV : S.IsVariety := G.geom.alg.variety
  have hV' := hV.baseChange Ω
  have hH := S.isPullback_baseChange Ω
  haveI : IsIntegral (S.baseChange Ω).Y := hV'.isIntegral
  haveI : SmoothOfRelativeDimension G.D (S.baseChange Ω).str := hV'.smooth
  obtain ⟨hprop, A₀, hA₀⟩ := (isProjOver_iff_isProper_and_exists_isAmpleLB _).1 hV.proj
  haveI := hprop
  have hstr : strHom K G.Y = G.str := strHom_eq fun _ => rfl
  have hproj : IsProjOver (strHom K G.Y) := hstr ▸ hV.proj
  haveI : IsProper (strHom K G.Y) := hstr ▸ hprop

  have hLnef : IsNef K G.L := IsGenerated.isNef_of_isProjOver (L := G.L) ⟨G.N, G.b, G.geom.alg.bpf⟩ hV.proj
  have hLj : IsNef K (lbPow G.L j) := hLnef.pow hA₀ j
  have hNnef : IsNef K (tens G.LA (lbPow G.L j)) := hnef.tens_of_isProjOver hLj hV.proj
  have hNbig : IsBig K (tens G.LA (lbPow G.L j)) := hbig.tens_nef Q.nef hproj hnef hLj

  haveI : IsIntegralHom (spMap (algebraMap K Ω)) :=
    IsIntegralHom.SpecMap_iff.2 fun x => Algebra.IsIntegral.isIntegral x
  haveI : IsIntegralHom (S.bcFst Ω) := MorphismProperty.of_isPullback (P := @IsIntegralHom) hH.flip ‹_›
  let π := S.bcFst Ω

  have hN'nef : IsNef Ω ((tens G.LA (lbPow G.L j)).pull π) :=
    PosBaseChange.isNef_pull hNnef hA₀ (hA₀.pull_of_isAffineHom π) π π.isClosedMap
  have hN'big : IsBig Ω ((tens G.LA (lbPow G.L j)).pull π) := by
    obtain ⟨D₀, hD₀, c, hc, hm⟩ := hNbig.3
    have hD : topologicalKrullDim G.Y = G.D := topologicalKrullDim_eq_of_smooth G.str G.D hV.smooth
    obtain rfl : D₀ = G.D := by exact_mod_cast hD₀.symm.trans hD
    have hL := LB.isLB_pull hNbig.1 π
    refine (isBig_iff (f := (S.baseChange Ω).str) (fun _ => rfl) hV'.proj
      (topologicalKrullDim_eq_of_smooth _ G.D hV'.smooth)).2 ⟨hL, c, hc, hm.mono fun m hm => hm.trans_eq (congrArg _ ?_)⟩
    rw [lineBundleGlobalSectionsDim_congr_picardClass (isLB_lbPow hL m) (LB.isLB_pull (isLB_lbPow hNbig.1 m) π)
      (by rw [cls_lbPow hL, cls_pull hNbig.1, cls_pull (isLB_lbPow hNbig.1 m), cls_lbPow hNbig.1, map_nsmul])]
    exact (FieldChangeInter.hdim_pull hH (isLB_lbPow hNbig.1 m) 0).symm

  have hM' := LB.isLB_pull (G.isLB_adj j) π
  have hKV : Subsingleton (coh (twist (structureModule (S.baseChange Ω).Y) ((G.adj j).pull π)) q) :=
    Q.kv.twist (k := Ω) (p := (S.baseChange Ω).str) (fun _ => rfl) hV'.proj (G.K.baseChange hH) hN'nef hN'big hM'
      (by
        rw [cls_pull (G.isLB_adj j) π]
        erw [cls_pull G.K.isLB π, cls_pull hNnef.isLB π]
        rw [← map_add]
        congr 1
        erw [cls_tens (isLB_tens G.K.isLB G.isLBA) (Twist.isLB_lbZPow G.isLB j), cls_tens G.K.isLB G.isLBA,
          cls_tens G.isLBA (isLB_lbPow G.isLB j)]
        exact add_assoc _ _ _) hq

  have hY : Subsingleton (coh (twist (structureModule G.Y) (G.adj j)) q) :=
    subsingleton_coh_of_pull (f := G.str) (f' := (S.baseChange Ω).str) hH (G.isLB_adj j) q hKV
  have hB : (tens G.K.bundle G.LA).IsLB := isLB_tens G.K.isLB G.isLBA
  obtain ⟨i⟩ := nonempty_twist_twist_iso_of_cls_eq (structureModule G.Y) hB (Twist.isLB_lbZPow G.isLB j)
    (G.isLB_adj j) rfl
  exact (cohOn.mapIso Γ(G.Y, ⊤) ⊤ q
    ((twistFunctor (lbZPow G.L j)).mapIso (Twist.unitTwistIso (tens G.K.bundle G.LA)).symm ≪≫ i)).toEquiv.subsingleton_congr.2 hY

end GlobalTheory.HSCore.VanishNumberField
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KottwitzTermEqDefinitePairOfLocalIsometryStatement
section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKDef GlobalTheory.LKCount
open scoped TensorProduct Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kottwitzTerm_eq_definitePair_of_local_isometry : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (P : Pair G) (Q : DPair G), P.γ = Q.γ → P.c = Q.c → (∃ u : (AfP p ⊗[ℚ] G.C)ˣ, (u : AfP p ⊗[ℚ] G.C) * inC G (AfP p) (Q.γ : G.C) = inC G (AfP p) (Q.γ : G.C) * u ∧ (u : AfP p ⊗[ℚ] G.C) * inC G (AfP p) (Q.β : G.C) * (starT G.star (AfP p) u).unop = inC G (AfP p) (P.β : G.C)) → ∀ (Kf : Subgroup G.GAf) (f : G.GAf → ℂ) (r : ℕ) (K : Subgroup (Gr G r)) (φ : Gr G r → ℂ), 0 < r → (∀ k ∈ Kf, ∀ g, f (k⁻¹ * g * k) = f g) → (∀ k ∈ K, ∀ g, φ (k⁻¹ * g * sigG G r k) = φ g) → P.term Kf f r K φ = Q.term Kf f r K φ := by
  first | exact @GlobalTheory.LKDefTerm.term_eq_of_local_isom | exact GlobalTheory.LKDefTerm.term_eq_of_local_isom | (intros; apply GlobalTheory.LKDefTerm.term_eq_of_local_isom <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.L2MatrixCoeffBoundedHolomorphicFormEqExtremalVecStatement
section
open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR GlobalTheory.HolDict
open scoped TensorProduct InnerProductSpace ContDiff
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.inner_rho_eq_normSq_mul_prod_of_holForm : ∀ (D : D7) (θ : InfFam D) (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (w : D.what₂.Tau → Fin V.rank → ℤ) (v : M.Vec), IsInfFam θ → HolShape M → WtIs M w → IsExtVec M v → ∀ (μ : Measure (GA D V)) (𝓕 : Set (GA D V)) (ρ : GA D V →* (Lp ℂ 2 (nuQ V μ 𝓕) →L[ℂ] Lp ℂ 2 (nuQ V μ 𝓕))), FinPair V μ 𝓕 → IsReg V μ 𝓕 ρ → ∀ (J : Set (GA D V)) (χ φ : GA D V → ℂ) F, HolForm θ M w J χ φ → Repr V μ 𝓕 F φ → ∀ u ∈ GinfC V, ⟪F, ρ u F⟫_ℂ = ((‖F‖ ^ 2 : ℝ) : ℂ) * ∏ τ, ⟪(v τ : M.H τ), M.rep τ (archM V (θ τ) u) (v τ : M.H τ)⟫_ℂ := by
  first | exact @GlobalTheory.HolDict.inner_reg_eq_coef_extremal | exact GlobalTheory.HolDict.inner_reg_eq_coef_extremal | (intros; apply GlobalTheory.HolDict.inner_reg_eq_coef_extremal <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftHomExistsOfNoetherianStatement
section
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj DividedPowers
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.SqLift GlobalTheory.Published GlobalTheory.Published.GrothendieckMessing

attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.liftHom_exists_of_noetherian_alt : AbelianDeRham → (∀ (R : Type) [CommRing R] [IsNoetherianRing R] (I : Ideal R) (hI : I ^ 2 = 0) (R₀ : Type) [CommRing R₀] (π : R →+* R₀),
    Function.Surjective π → RingHom.ker π = I → LiftObj (divided₂ hI) π ∧ LiftHom (divided₂ hI) π) →
  ∀ (R : Type) [CommRing R] (I : Ideal R) (h : I ^ 2 = 0) (R₀ : Type) [CommRing R₀] (π : R →+* R₀),
    Function.Surjective π → RingHom.ker π = I →
  ∀ (g : ℕ) (A₀ : Over (Sp R₀)) [GrpObj A₀] (A : Over (Sp R)) [GrpObj A] (i : A₀.left ⟶ A.left)
    (hA : IsGrpPullback A₀ A (spMap π) i), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom →
  ∀ (g' : ℕ) (B₀ : Over (Sp R₀)) [GrpObj B₀] (B : Over (Sp R)) [GrpObj B] (j : B₀.left ⟶ B.left)
    (hB : IsGrpPullback B₀ B (spMap π) j), IsAbelianScheme B → SmoothOfRelativeDimension g' B.hom →
  ∀ (f₀ : A₀ ⟶ B₀) [IsMonHom f₀], (∀ d ∈ liftFil (divided₂ h) hA, push (divided₂ h) (spMap π) f₀ d ∈ liftFil (divided₂ h) hB) →
    ∃ f : A ⟶ B, i ≫ f.left = f₀.left ≫ j := by
  first | exact @GlobalTheory.liftHom_exists_of_noetherian | exact GlobalTheory.liftHom_exists_of_noetherian | (intros; apply GlobalTheory.liftHom_exists_of_noetherian <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LintegralSiegelTorusConeModulusLtTopStatement
section
open scoped Matrix NNReal ENNReal TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lintegral_siegelTorusCone_modulus_lt_top : ∀ (F : Type) [Field F] [NumberField F] (m r n : ℕ) (c : ℝ), 0 < c → (r = 0 ∨ n + r < m) → ∫⁻ t in GlobalTheory.SiegelSet.cone r c, ENNReal.ofReal (∏ i, t i ^ (Module.finrank ℚ F * (2 * n))) * ENNReal.ofReal ((GlobalTheory.SiegelSet.modulus F m t * ∏ i, t i)⁻¹) < ⊤ := by
  first | exact @GlobalTheory.SiegelSet.lintegral_cone_modulus_lt_top_of_witt | exact GlobalTheory.SiegelSet.lintegral_cone_modulus_lt_top_of_witt | (intros; apply GlobalTheory.SiegelSet.lintegral_cone_modulus_lt_top_of_witt <;> assumption)
end

