import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0699
import Mathlib
import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.LocalBaseChange.ExponentSeparationLemma.ExponentSeparation
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SupercuspidalSupportUniqueGL
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle0048
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle0044
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle0063
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0163
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0056
import GroundTheory.AutomorphicForms.Satake
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0701
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0020
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsSmoothModerateOfIsAutFunSm
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0272
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0321
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1523
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0066
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0037
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0698
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0702
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0706
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.UnramifiedWhittaker.Bundle0003
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0707

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.StandardCompactFrameEquiv
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl PositivityTheory.RgEis GlobalTheory.CompanionTheory.SiegelFrame

noncomputable section

namespace GlobalTheory.CompanionTheory.SiegelFrame.StdCompact

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ} {Y : Spc F E n}

theorem conj_unit_iff {ι : Type} [Fintype ι] [DecidableEq ι] (U : Matrix ι ι ℂ) :
    U.map (starRingEnd ℂ) * (U.map (starRingEnd ℂ))ᴴ = 1 ↔ U * Uᴴ = 1 := by
  have e : U.map (starRingEnd ℂ) * (U.map (starRingEnd ℂ))ᴴ = (U * Uᴴ).map (starRingEnd ℂ) := by
    rw [Matrix.map_mul]
    congr 1
  constructor
  · intro h
    rw [e] at h
    have h2 : ((U * Uᴴ).map (starRingEnd ℂ)).map (starRingEnd ℂ) = (1 : Matrix ι ι ℂ).map (starRingEnd ℂ) := by rw [h]
    have e2 : ((U * Uᴴ).map (starRingEnd ℂ)).map (starRingEnd ℂ) = U * Uᴴ := by
      ext i j
      simp only [Matrix.map_apply, Complex.conj_conj]
    rw [e2, Matrix.map_one _ (map_zero _) (map_one _)] at h2
    exact h2
  · intro h
    rw [e, h]
    exact Matrix.map_one _ (map_zero _) (map_one _)

theorem inFrame_eq (χ : Chr F E) (ε : ℤˣ) (b : GL (Fin n ⊕ Fin n) E)
    (hb : b.1ᵀ * dbl Y.J * b.1.map σ = Matrix.fromBlocks 0 1 (((ε : ℤ) : E) • 1) 0) (x : G2 σ Y) :
    inFrame b x = (((frameEquiv χ ε b hb x).1 : GL (Fin n ⊕ Fin n) (AE F E)) :
      Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (AE F E)) := by
  have hinv : (bA (F := F) b)⁻¹ = bA (F := F) b⁻¹ :=
    (map_inv (Matrix.GeneralLinearGroup.map (n := Fin n ⊕ Fin n) (inclR (F := F) (E := E) (AF F))) b).symm
  rw [frameEquiv_val, hinv]
  rfl

theorem mem_O_iff (hD : Dict) (χ : Chr F E) (y : AE F E) :
    y ∈ (adCM σ χ).O ↔ finOne F • y ∈ intHat F E :=
  (hD F E).2.2.2.1 y

theorem unit_iff (hI : DictInf) (hcm : IsCMExt F E σ) (χ : Chr F E) (B : Base F E)
    (M : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (AE F E)) :
    (∀ w, M.map (piInf (B.emb w)) * (M.map (piInf (B.emb w)))ᴴ = 1) ↔
      ∀ w, M.map ((adCM σ χ).φ w) ∈ Matrix.unitaryGroup (Fin n ⊕ Fin n) ℂ := by
  have key : ∀ (τ : AE F E →+* ℂ) (w' : InfinitePlace E),
      ((∀ z, τ z = (adStd E).φ w' (eqv F E z)) ∨ ∀ z, τ z = starRingEnd ℂ ((adStd E).φ w' (eqv F E z))) →
      (M.map τ * (M.map τ)ᴴ = 1 ↔ M.map ((adCM σ χ).φ w') ∈ Matrix.unitaryGroup (Fin n ⊕ Fin n) ℂ) := by
    intro τ w' h
    rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose]
    rcases h with h | h
    · have e : M.map τ = M.map ((adCM σ χ).φ w') := by
        ext i j
        exact h _
      rw [e]
    · have e : M.map τ = (M.map ((adCM σ χ).φ w')).map (starRingEnd ℂ) := by
        ext i j
        exact h _
      rw [e]
      exact conj_unit_iff _
  obtain ⟨h1, h2⟩ := (hI F E σ hcm).2 B.emb
  constructor
  · intro h w'
    obtain ⟨w, hw⟩ := h2 w'
    exact (key _ w' hw).1 (h w)
  · intro h w
    obtain ⟨w', hw⟩ := h1 w
    exact (key _ w' hw).2 (h w')

theorem mem_isStdK_iff : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (Y : Spc F E n), Dict → DictInf → IsCMExt F E σ → ∀ (χ : Chr F E) (ε : ℤˣ) (b : GL (Fin n ⊕ Fin n) E) (hb : b.1ᵀ * dbl Y.J * b.1.map σ = Matrix.fromBlocks 0 1 (((ε : ℤ) : E) • 1) 0) (B : Base F E) (K : Subgroup (G2 σ Y)), IsStdK (σ := σ) (Y := Y) B b K → ∀ x : G2 σ Y, x ∈ K ↔ frameEquiv χ ε b hb x ∈ (adCM σ χ).uK ε (Fin n) := by
  intro F E _ _ _ _ _ σ n Y hD hI hcm χ ε b hb B K hK x
  have hinv : inFrame b x⁻¹ = ((((frameEquiv χ ε b hb x).1)⁻¹ : GL (Fin n ⊕ Fin n) (AE F E)) :
      Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (AE F E)) := by
    rw [inFrame_eq χ ε b hb x⁻¹, map_inv]
    rfl
  have hx := inFrame_eq χ ε b hb x
  rw [hK x]
  show _ ↔ (frameEquiv χ ε b hb x).1 ∈ (adCM σ χ).kGL (Fin n ⊕ Fin n)
  show _ ↔ (∀ r c, (((frameEquiv χ ε b hb x).1 : GL (Fin n ⊕ Fin n) (AE F E)) :
        Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (AE F E)) r c ∈ (adCM σ χ).O ∧
      (((((frameEquiv χ ε b hb x).1)⁻¹ : GL (Fin n ⊕ Fin n) (AE F E))) :
        Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (AE F E)) r c ∈ (adCM σ χ).O) ∧
      ∀ w, (((frameEquiv χ ε b hb x).1 : GL (Fin n ⊕ Fin n) (AE F E)) :
        Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (AE F E)).map ((adCM σ χ).φ w) ∈ Matrix.unitaryGroup (Fin n ⊕ Fin n) ℂ
  rw [← hinv, ← hx, ← unit_iff hI hcm χ B, and_comm]
  refine and_congr ?_ Iff.rfl
  simp only [mem_O_iff (σ := σ) hD χ]
  constructor
  · intro h r c
    exact ⟨h x (by simp) r c, h x⁻¹ (by simp) r c⟩
  · intro h k' hk' r c
    rcases hk' with rfl | hk'
    · exact (h r c).1
    · rw [Set.mem_singleton_iff] at hk'
      subst hk'
      exact (h r c).2

end GlobalTheory.CompanionTheory.SiegelFrame.StdCompact
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SubquotientPrincipalSeriesBound
section
noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.Published GlobalTheory.SplitWeil
open GroundTheory.Automorphic.Spherical

namespace GlobalTheory.CompanionTheory.HeckeSub

theorem isSatakeParameter_subquotient : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (α : Fin n → ℂˣ) (X V : Type) [AddCommGroup X] [Module ℂ X] [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (GL (Fin n) k) X), IsSmooth ρ → ∀ (ι : ρ.IntertwiningMap (principalSeries k n (paramChar k α))), Function.Injective ι → ∀ (π : Representation ℂ (GL (Fin n) k) V), IsSubquotient π ρ → ∀ [MeasurableSpace (GL (Fin n) k)] [BorelSpace (GL (Fin n) k)] (μ : MeasureTheory.Measure (GL (Fin n) k)) [μ.IsHaarMeasure], IsSatakeParameter π μ α := by
  intro k _ _ _ _ n α X V _ _ _ _ ρ hρ ι hι π hπ _ _ μ _ h v hv
  obtain ⟨S, f, hf⟩ := hπ
  have hS : IsSmooth S.toRepresentation :=
    IsSubquotient.isSmooth (ρ := ρ) ⟨S, .id _, Function.surjective_id⟩ hρ
  obtain ⟨u, rfl⟩ := hf v
  have hfix : ∀ g ∈ GroundTheory.Automorphic.GLnLocal.integralGL k n, π g (f u) = f u := fun g hg =>
    GroundTheory.Automorphic.mem_fixedVectors.1 hv g hg
  obtain ⟨w, hw, hfw⟩ := IwahoriOnto.exists_fixed_map_eq hS
    (GroundTheory.Automorphic.GLnLocal.isCompact_integralGL k n) f.toLinearMap u fun g hg => by
      show f (S.toRepresentation g u) = f u
      rw [f.isIntertwining]
      exact hfix g hg
  have hfw' : f w = f u := hfw
  have hw' : w ∈ GroundTheory.Automorphic.fixedVectors S.toRepresentation
      (GroundTheory.Automorphic.GLnLocal.integralGL k n) := by
    simpa [fixed, eig, GroundTheory.Automorphic.fixedVectors] using hw
  let T : S.toRepresentation.IntertwiningMap (principalSeries k n (paramChar k α)) :=
    ⟨ι.toLinearMap ∘ₗ S.toSubmodule.subtype, fun g => by
      refine LinearMap.ext fun x => ?_
      exact ι.isIntertwining _ _ g x⟩
  have hT : Function.Injective T := fun a b e => Subtype.ext (hι e)
  have hTw : T w ∈ GroundTheory.Automorphic.fixedVectors (principalSeries k n (paramChar k α))
      (GroundTheory.Automorphic.GLnLocal.integralGL k n) :=
    GroundTheory.Automorphic.mem_fixedVectors.2 fun g hg => by
      rw [← T.isIntertwining, GroundTheory.Automorphic.mem_fixedVectors.1 hw' g hg]
  have hmem := (h : GroundTheory.Automorphic.HeckeAlgebra μ).mem
  set c := GroundTheory.Automorphic.Spherical.evalAt α (satakeTransform μ h) with hc
  have hPS := isSatakeParameter_principalSeries (F := k) (μ := μ) α h (T w) hTw
  have hact : GroundTheory.Automorphic.heckeAct μ S.toRepresentation (h : GroundTheory.Automorphic.HeckeAlgebra μ) w = c • w := by
    apply hT
    rw [GroundTheory.Automorphic.map_heckeAct T hmem (hS w), hPS, map_smul]
  rw [← hfw', ← GroundTheory.Automorphic.map_heckeAct f hmem (hS w), hact, map_smul]

end GlobalTheory.CompanionTheory.HeckeSub
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SurjectiveIntertwinerQuotientEquiv
section
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.BZRes Topology
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.BZRes.KerQuot

theorem exists_subQuot_top_ker_equiv {G V W : Type} [Group G] [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W] (ρ : Representation ℂ G V) (τ : Representation ℂ G W)
    (R : ρ.IntertwiningMap τ) (hR : Function.Surjective R) :
    ∃ S : Subrepresentation ρ, S.toSubmodule = LinearMap.ker R.toLinearMap ∧
      Nonempty ((subQuot ⊤ S).Equiv τ) := by
  refine ⟨Representation.IntertwiningMap.ker ρ τ R, rfl, ?_⟩
  let T : Subrepresentation ρ := ⊤
  let f : T.toSubmodule →ₗ[ℂ] W := R.toLinearMap ∘ₗ T.toSubmodule.subtype
  have hf : Function.Surjective f := by
    intro w
    obtain ⟨v, rfl⟩ := hR w
    exact ⟨⟨v, by first | exact Submodule.mem_top | trivial | simp [T]⟩, rfl⟩
  have hker : Submodule.comap T.toSubmodule.subtype
      (Representation.IntertwiningMap.ker ρ τ R).toSubmodule = LinearMap.ker f :=
    (LinearMap.ker_comp T.toSubmodule.subtype R.toLinearMap).symm
  let e := (Submodule.quotEquivOfEq _ _ hker).trans (f.quotKerEquivOfSurjective hf)
  refine ⟨⟨⟨e.toLinearMap, fun g => ?_⟩, e.symm, e.left_inv, e.right_inv⟩⟩
  apply Submodule.linearMap_qext
  apply LinearMap.ext
  intro x
  first
    | exact Representation.IntertwiningMap.isIntertwining ρ τ R g x.1
    | exact R.isIntertwining g x.1
    | simp [e, f, T, GlobalTheory.SmGL.subQuot, Representation.quotient_apply,
        Subrepresentation.toRepresentation, Representation.IntertwiningMap.isIntertwining]

end GlobalTheory.CompanionTheory.BZRes.KerQuot
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ThetaRapidDecaySiegelSet
section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.SiegelFormula
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CompanionTheory.WeilCount
open NumberField IsDedekindDomain Matrix

theorem lattice_sum {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {I : Type} [Fintype I] (τ : I → (E →+* ℂ)) (hτ : Function.Surjective fun i => InfinitePlace.mk (τ i))
    {n : ℕ} {ι : Type} [Fintype ι] (R : Matrix ι (Fin n) E) (R' : Matrix (Fin n) ι E) (hR : R' * R = 1)
    (L : Set (Matrix (Fin n) (Fin 1) (Af F ⊗[F] E))) (hL : IsCompact L) :
    ∃ K : ℝ, 0 < K ∧ ∀ (s : ι → ℝ), (∀ i, 0 < s i) → ∀ (U : Matrix (Fin n) (Fin 1) E → ℝ), (∀ ξ, 0 ≤ U ξ) →
      (∀ ξ, ξ.map (fun x => (1 : Af F) ⊗ₜ[F] x) ∈ L → ∀ ρ i, ‖τ ρ ((R * ξ) i 0)‖ ≤ s i * U ξ) →
      ∀ N, 2 * (Fintype.card ι * Module.finrank ℚ E) ≤ N →
      ∑' ξ : Matrix (Fin n) (Fin 1) E, ENNReal.ofReal (((1 + U ξ) ^ N)⁻¹ *
          Set.indicator L (fun _ => (1 : ℝ)) (ξ.map (fun x => (1 : Af F) ⊗ₜ[F] x))) ≤
        ENNReal.ofReal (∏ i, (1 + K * s i) ^ Module.finrank ℚ E) := by
  classical
  have hev : ∀ j : Fin n, Continuous fun M : Matrix (Fin n) (Fin 1) (Af F ⊗[F] E) => M j 0 := fun j =>
    (continuous_apply 0).comp (continuous_apply j)
  have hC : IsCompact ((⋃ j, (fun M : Matrix (Fin n) (Fin 1) (Af F ⊗[F] E) => M j 0) '' L) ∪
      Set.range fun p : ι × Fin n => (1 : Af F) ⊗ₜ[F] R p.1 p.2) :=
    (isCompact_iUnion fun j => hL.image (hev j)).union (Set.finite_range _).isCompact
  obtain ⟨d, hd, hden⟩ := GlobalTheory.T.compact_adelic_denominator F E _ hC
  obtain ⟨K₀, hK₀, hco⟩ := GlobalTheory.T.integer_coordinates_bound τ hτ
  have hint : ∀ ξ : Matrix (Fin n) (Fin 1) E, ξ.map (fun x => (1 : Af F) ⊗ₜ[F] x) ∈ L → ∀ i,
      ∃ y : 𝓞 E, ((d * d : ℕ) : E) * (R * ξ) i 0 = y := by
    intro ξ hξ i
    choose y₁ hy₁ using fun j => hden (R i j) (Or.inr ⟨(i, j), rfl⟩)
    choose y₂ hy₂ using fun j => hden (ξ j 0) (Or.inl (Set.mem_iUnion.2 ⟨j, _, hξ, rfl⟩))
    refine ⟨∑ j, y₁ j * y₂ j, ?_⟩
    rw [Matrix.mul_apply, Finset.mul_sum, RingOfIntegers.coe_eq_algebraMap, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_mul, ← RingOfIntegers.coe_eq_algebraMap, ← RingOfIntegers.coe_eq_algebraMap, ← hy₁ j, ← hy₂ j]
    push_cast
    ring
  have hdd : (0 : ℝ) < ((d * d : ℕ) : ℝ) := by exact_mod_cast Nat.mul_pos hd hd
  have hddE : ((d * d : ℕ) : E) ≠ 0 := by exact_mod_cast (Nat.mul_pos hd hd).ne'
  set D₀ : ℝ := ((d * d : ℕ) : ℝ) with hD₀
  refine ⟨2 * (K₀ * D₀), by positivity, fun s hs U hU hb N hN => ?_⟩
  let e : Matrix (Fin n) (Fin 1) E → ι → 𝓞 E := fun ξ i =>
    if h : ∃ y : 𝓞 E, ((d * d : ℕ) : E) * (R * ξ) i 0 = y then h.choose else 0
  have he : ∀ ξ : Matrix (Fin n) (Fin 1) E, ξ.map (fun x => (1 : Af F) ⊗ₜ[F] x) ∈ L → ∀ i,
      ((e ξ i : 𝓞 E) : E) = ((d * d : ℕ) : E) * (R * ξ) i 0 := fun ξ hξ i => by
    have h := hint ξ hξ i
    simp only [e, dif_pos h]
    exact h.choose_spec.symm
  let κ := Module.Free.ChooseBasisIndex ℤ (𝓞 E)
  let m : Matrix (Fin n) (Fin 1) E → ι × κ → ℤ := fun ξ p => (RingOfIntegers.basis E).repr (e ξ p.1) p.2
  let b : ι × κ → ℝ := fun p => K₀ * D₀ * s p.1
  have hbp : ∀ p, 0 < b p := fun p => mul_pos (by positivity) (hs p.1)
  let h : Matrix (Fin n) (Fin 1) E → ℝ≥0∞ := fun ξ => ENNReal.ofReal (((1 + U ξ) ^ N)⁻¹ *
    Set.indicator L (fun _ => (1 : ℝ)) (ξ.map (fun x => (1 : Af F) ⊗ₜ[F] x)))
  have hsupp : ∀ ξ, h ξ ≠ 0 → ξ.map (fun x => (1 : Af F) ⊗ₜ[F] x) ∈ L := fun ξ h0 => by
    by_contra hn
    exact h0 (by simp [h, Set.indicator_of_notMem hn])
  have hinj : Set.InjOn m {ξ | h ξ ≠ 0} := by
    intro ξ hξ ξ' hξ' hm
    have hξ1 := hsupp ξ hξ
    have hξ2 := hsupp ξ' hξ'
    have h1 : ∀ i, e ξ i = e ξ' i := fun i =>
      (RingOfIntegers.basis E).ext_elem fun k => congrFun hm (i, k)
    have h2 : R * ξ = R * ξ' := by
      ext i j
      obtain rfl : j = 0 := Subsingleton.elim _ _
      have := congrArg (fun y : 𝓞 E => (y : E)) (h1 i)
      simp only [he ξ hξ1 i, he ξ' hξ2 i] at this
      exact mul_left_cancel₀ hddE this
    calc ξ = R' * (R * ξ) := by rw [← Matrix.mul_assoc, hR, Matrix.one_mul]
      _ = R' * (R * ξ') := by rw [h2]
      _ = ξ' := by rw [← Matrix.mul_assoc, hR, Matrix.one_mul]
  have hh : ∀ ξ, h ξ ≤ ∏ p, ENNReal.ofReal (((1 + |(m ξ p : ℝ)| / b p) ^ 2)⁻¹) := by
    intro ξ
    by_cases hξ : ξ.map (fun x => (1 : Af F) ⊗ₜ[F] x) ∈ L
    · rw [← ENNReal.ofReal_prod_of_nonneg fun p _ => by positivity]
      refine ENNReal.ofReal_le_ofReal ?_
      rw [Set.indicator_of_mem hξ, mul_one]
      have h1 : ∀ p, ((1 + U ξ) ^ 2)⁻¹ ≤ ((1 + |(m ξ p : ℝ)| / b p) ^ 2)⁻¹ := fun p => by
        have hUp := hU ξ
        have h2 : |(m ξ p : ℝ)| ≤ K₀ * (D₀ * (s p.1 * U ξ)) := by
          refine hco (e ξ p.1) _ (fun ρ => ?_) p.2
          rw [he ξ hξ p.1, map_mul, norm_mul, map_natCast, Complex.norm_natCast]
          exact mul_le_mul_of_nonneg_left (hb ξ hξ ρ p.1) hdd.le
        have h3 : |(m ξ p : ℝ)| / b p ≤ U ξ := by
          rw [div_le_iff₀ (hbp p)]
          calc |(m ξ p : ℝ)| ≤ K₀ * (D₀ * (s p.1 * U ξ)) := h2
            _ = U ξ * b p := by simp only [b]; ring
        have h4 : 0 ≤ |(m ξ p : ℝ)| / b p := div_nonneg (abs_nonneg _) (hbp p).le
        refine inv_anti₀ (by positivity) (pow_le_pow_left₀ (by positivity) (by linarith) 2)
      have hcard : Fintype.card (ι × κ) = Fintype.card ι * Module.finrank ℚ E := by
        rw [Fintype.card_prod, ← RingOfIntegers.rank, Module.finrank_eq_card_chooseBasisIndex]
      have h5 : ((1 + U ξ) ^ N)⁻¹ ≤ ∏ _p : ι × κ, ((1 + U ξ) ^ 2)⁻¹ := by
        have hUp := hU ξ
        rw [Finset.prod_const, Finset.card_univ, hcard, inv_pow, ← pow_mul]
        refine inv_anti₀ (by positivity) (pow_le_pow_right₀ (by linarith) ?_)
        exact hN
      exact h5.trans (Finset.prod_le_prod (fun _ _ => by positivity) fun p _ => h1 p)
    · simp [h, Set.indicator_of_notMem hξ]
  refine (GlobalTheory.T.lattice_sum_decay_bound m b hbp h hinj hh).trans (le_of_eq ?_)
  rw [← ENNReal.ofReal_prod_of_nonneg fun p _ => by have := hbp p; positivity]
  congr 1
  rw [Fintype.prod_prod_type]
  refine Finset.prod_congr rfl fun i _ => ?_
  have hc : ∀ y : κ, 1 + 2 * b (i, y) = 1 + 2 * (K₀ * D₀) * s i := fun y => by simp only [b]; ring
  simp only [hc, Finset.prod_const, Finset.card_univ]
  rw [← RingOfIntegers.rank, Module.finrank_eq_card_chooseBasisIndex]

theorem count_main : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (V : HSp D) {r : ℕ} (Xf Yf : Matrix (Fin V.rank) (Fin r) D.host.E), GlobalTheory.SiegelSet.IsWittFrame D.sp.cm.sig V.gram Xf Yf → ∀ {c : ℝ}, 0 < c → ∀ (L : Set (Matrix (Fin V.rank) (Fin 1) (Af D.host.F ⊗[D.host.F] D.host.E))), IsCompact L → ∃ N₀ : ℕ, ∀ N, N₀ ≤ N → ∃ C : ℝ, ∀ t ∈ GlobalTheory.SiegelSet.cone r c, ∀ a : GA D V, GlobalTheory.SiegelSet.IsTorusElt D.sp.cm.sig V.gram Xf Yf t a → ∑' ξ : Matrix (Fin V.rank) (Fin 1) D.host.E, ENNReal.ofReal (((1 + ‖fun τ i => compAt θ τ (invPt V a ξ) i 0‖) ^ N)⁻¹ * Set.indicator L (fun _ => (1 : ℝ)) ((invPt V a ξ).map (finPart D))) ≤ ENNReal.ofReal (C * ∏ i, t i ^ (2 * Module.finrank ℚ D.host.F)) := by
  intro D θ hθ V r Xf Yf hW c hc L hL
  have hCM := GlobalTheory.AdelicU.isCMExt_host D
  have hf2 : Module.finrank ℚ D.host.E = 2 * Module.finrank ℚ D.host.F := by
    haveI : Module.Finite D.host.F D.host.E := Module.Finite.of_restrictScalars_finite ℚ _ _
    rw [← Module.finrank_mul_finrank ℚ D.host.F D.host.E, hCM.2.2.1, mul_comm]
  set Rx := Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) Xf * V.gram with hRx
  set Ry := Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) Yf * V.gram with hRy
  set Q := 1 - Xf * Ry - Yf * Rx with hQ
  let R : Matrix (Fin r ⊕ Fin r ⊕ Fin V.rank) (Fin V.rank) D.host.E := Matrix.fromRows Ry (Matrix.fromRows Rx Q)
  let R' : Matrix (Fin V.rank) (Fin r ⊕ Fin r ⊕ Fin V.rank) D.host.E := Matrix.fromCols Xf (Matrix.fromCols Yf 1)
  have hR : R' * R = 1 := by
    simp only [R, R', Matrix.fromCols_mul_fromRows, hQ, Matrix.one_mul]
    abel
  obtain ⟨K, hK, hsum⟩ := lattice_sum (F := D.host.F) (tauE D) (GlobalTheory.CMTypePlaces.mk_tauE_bijective D).2 R R' hR L hL
  set Cn : ℝ := 1 + ∑ ρ, ∑ i, ∑ j, ‖tauE D ρ (R i j)‖ with hCn
  have hCn1 : 1 ≤ Cn := by
    have : 0 ≤ ∑ ρ, ∑ i, ∑ j, ‖tauE D ρ (R i j)‖ := by positivity
    linarith
  have hCn0 : 0 < Cn := by linarith
  have hrow : ∀ ρ i, ∑ j, ‖tauE D ρ (R i j)‖ ≤ Cn := fun ρ i => by
    have h1 : ∑ j, ‖tauE D ρ (R i j)‖ ≤ ∑ i, ∑ j, ‖tauE D ρ (R i j)‖ :=
      Finset.single_le_sum (f := fun i => ∑ j, ‖tauE D ρ (R i j)‖) (fun _ _ => by positivity) (Finset.mem_univ i)
    have h2 : ∑ i, ∑ j, ‖tauE D ρ (R i j)‖ ≤ ∑ ρ, ∑ i, ∑ j, ‖tauE D ρ (R i j)‖ :=
      Finset.single_le_sum (f := fun ρ => ∑ i, ∑ j, ‖tauE D ρ (R i j)‖) (fun _ _ => by positivity) (Finset.mem_univ ρ)
    linarith
  refine ⟨2 * (Fintype.card (Fin r ⊕ Fin r ⊕ Fin V.rank) * Module.finrank ℚ D.host.E), fun N hN => ?_⟩
  set c₀ : ℝ := min 1 c ^ r with hc₀
  have hc₀p : 0 < c₀ := pow_pos (lt_min one_pos hc) _
  set A₁ : ℝ := c₀⁻¹ + K * Cn with hA₁
  set A₂ : ℝ := 1 + K * Cn * c₀⁻¹ with hA₂
  set A₃ : ℝ := 1 + K * Cn with hA₃
  have hA₁p : 0 < A₁ := by positivity
  have hA₂p : 0 < A₂ := by positivity
  have hA₃p : 0 < A₃ := by positivity
  set f := Module.finrank ℚ D.host.E with hf
  refine ⟨(∏ _i : Fin r, A₁ ^ f) * (∏ _i : Fin r, A₂ ^ f) * ∏ _j : Fin V.rank, A₃ ^ f, fun t ht a ha => ?_⟩
  have ht0 : ∀ i, 0 < t i := ht.1
  have htc : ∀ i, c₀ ≤ t i := GlobalTheory.SiegelHt.cone_low hc ht
  let U : Matrix (Fin V.rank) (Fin 1) D.host.E → ℝ := fun ξ => ‖fun τ i => compAt θ τ (invPt V a ξ) i 0‖
  let s : Fin r ⊕ Fin r ⊕ Fin V.rank → ℝ := Sum.elim (fun i => Cn * t i) (Sum.elim (fun i => Cn * (t i)⁻¹) fun _ => Cn)
  have hs : ∀ i, 0 < s i := by
    rintro (i | i | i)
    · exact mul_pos hCn0 (ht0 i)
    · exact mul_pos hCn0 (inv_pos.2 (ht0 i))
    · exact hCn0
  have hU : ∀ ξ, 0 ≤ U ξ := fun ξ => norm_nonneg _
  have hcoord := GlobalTheory.T.inverse_point_torus_scaling D θ hθ V Xf Yf hW t ht0 a ha
  have hent : ∀ ξ ρ j, ‖compAt θ ρ (invPt V a ξ) j 0‖ ≤ U ξ := fun ξ ρ j =>
    (norm_le_pi_norm (fun i => compAt θ ρ (invPt V a ξ) i 0) j).trans
      (norm_le_pi_norm (fun τ i => compAt θ τ (invPt V a ξ) i 0) ρ)
  have hmul : ∀ ξ ρ i, ‖((R.map (tauE D ρ)) * compAt θ ρ (invPt V a ξ)) i 0‖ ≤ Cn * U ξ := fun ξ ρ i => by
    rw [Matrix.mul_apply]
    refine (norm_sum_le _ _).trans ?_
    calc ∑ j, ‖(R.map (tauE D ρ)) i j * compAt θ ρ (invPt V a ξ) j 0‖
        ≤ ∑ j, ‖tauE D ρ (R i j)‖ * U ξ := Finset.sum_le_sum fun j _ => by
          rw [norm_mul, Matrix.map_apply]
          exact mul_le_mul_of_nonneg_left (hent ξ ρ j) (norm_nonneg _)
      _ = (∑ j, ‖tauE D ρ (R i j)‖) * U ξ := (Finset.sum_mul _ _ _).symm
      _ ≤ Cn * U ξ := mul_le_mul_of_nonneg_right (hrow ρ i) (hU ξ)
  have hb : ∀ ξ, ξ.map (fun x => (1 : Af D.host.F) ⊗ₜ[D.host.F] x) ∈ L → ∀ ρ i, ‖tauE D ρ ((R * ξ) i 0)‖ ≤ s i * U ξ := by
    intro ξ _ ρ i
    obtain ⟨-, h⟩ := hcoord ξ
    obtain ⟨h1, h2, h3⟩ := h ρ
    rcases i with i | i | i
    · have e := congrFun (congrFun h1 i) 0
      have e2 : (R.map (tauE D ρ) * compAt θ ρ (invPt V a ξ)) (Sum.inl i) 0 = (Ry.map (tauE D ρ) * compAt θ ρ (invPt V a ξ)) i 0 := rfl
      have e3 : (R * ξ) (Sum.inl i) 0 = (Ry * ξ) i 0 := rfl
      have h4 := hmul ξ ρ (Sum.inl i)
      rw [e2, e, Matrix.diagonal_mul, Matrix.map_apply, norm_mul, norm_inv, Complex.norm_real,
        Real.norm_of_nonneg (ht0 i).le] at h4
      rw [e3]
      show _ ≤ Cn * t i * U ξ
      have := ht0 i
      rw [inv_mul_le_iff₀ this] at h4
      linarith
    · have e := congrFun (congrFun h2 i) 0
      have e2 : (R.map (tauE D ρ) * compAt θ ρ (invPt V a ξ)) (Sum.inr (Sum.inl i)) 0 = (Rx.map (tauE D ρ) * compAt θ ρ (invPt V a ξ)) i 0 := rfl
      have e3 : (R * ξ) (Sum.inr (Sum.inl i)) 0 = (Rx * ξ) i 0 := rfl
      have h4 := hmul ξ ρ (Sum.inr (Sum.inl i))
      rw [e2, e, Matrix.diagonal_mul, Matrix.map_apply, norm_mul, Complex.norm_real,
        Real.norm_of_nonneg (ht0 i).le] at h4
      rw [e3]
      show _ ≤ Cn * (t i)⁻¹ * U ξ
      have := ht0 i
      rw [mul_comm Cn, mul_assoc, inv_mul_eq_div, le_div_iff₀ this, mul_comm]
      exact h4
    · have e := congrFun (congrFun h3 i) 0
      have e2 : (R.map (tauE D ρ) * compAt θ ρ (invPt V a ξ)) (Sum.inr (Sum.inr i)) 0 = (Q.map (tauE D ρ) * compAt θ ρ (invPt V a ξ)) i 0 := rfl
      have e3 : (R * ξ) (Sum.inr (Sum.inr i)) 0 = (Q * ξ) i 0 := rfl
      have h4 := hmul ξ ρ (Sum.inr (Sum.inr i))
      rw [e2, e, Matrix.map_apply] at h4
      rw [e3]
      exact h4
  have main := hsum s hs U hU hb N hN
  have hsame : ∀ ξ : Matrix (Fin V.rank) (Fin 1) D.host.E, (invPt V a ξ).map (finPart D) = ξ.map (fun x => (1 : Af D.host.F) ⊗ₜ[D.host.F] x) := fun ξ => (hcoord ξ).1
  simp only [hsame]
  refine main.trans (ENNReal.ofReal_le_ofReal ?_)
  rw [← hf2, Fintype.prod_sum_type, Fintype.prod_sum_type]
  simp only [s, Sum.elim_inl, Sum.elim_inr]
  have h1 : ∀ i, (1 + K * (Cn * t i)) ^ f ≤ A₁ ^ f * t i ^ f := fun i => by
    rw [← mul_pow]
    refine pow_le_pow_left₀ (by have := ht0 i; positivity) ?_ _
    have : 1 ≤ c₀⁻¹ * t i := by
      rw [inv_mul_eq_div, one_le_div hc₀p]; exact htc i
    rw [hA₁]; nlinarith
  have h2 : ∀ i, (1 + K * (Cn * (t i)⁻¹)) ^ f ≤ A₂ ^ f := fun i => by
    refine pow_le_pow_left₀ (by have := ht0 i; positivity) ?_ _
    have : (t i)⁻¹ ≤ c₀⁻¹ := inv_anti₀ hc₀p (htc i)
    have hKC : 0 < K * Cn := by positivity
    rw [hA₂]; nlinarith
  calc (∏ i, (1 + K * (Cn * t i)) ^ f) * ((∏ i, (1 + K * (Cn * (t i)⁻¹)) ^ f) * ∏ _j : Fin V.rank, (1 + K * Cn) ^ f)
      ≤ (∏ i, A₁ ^ f * t i ^ f) * ((∏ _i : Fin r, A₂ ^ f) * ∏ _j : Fin V.rank, A₃ ^ f) := by
        refine mul_le_mul (Finset.prod_le_prod (fun i _ => by have := ht0 i; positivity) fun i _ => h1 i) ?_ (by
          refine mul_nonneg (Finset.prod_nonneg fun i _ => by have := ht0 i; positivity) (Finset.prod_nonneg fun i _ => by positivity)) (Finset.prod_nonneg fun i _ => by have := ht0 i; positivity)
        refine mul_le_mul_of_nonneg_right (Finset.prod_le_prod (fun i _ => by have := ht0 i; positivity) fun i _ => h2 i) (Finset.prod_nonneg fun i _ => by positivity)
    _ = (∏ _i : Fin r, A₁ ^ f) * (∏ _i : Fin r, A₂ ^ f) * (∏ _j : Fin V.rank, A₃ ^ f) * ∏ i, t i ^ f := by
        rw [Finset.prod_mul_distrib]; ring

end GlobalTheory.CompanionTheory.WeilCount

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnramifiedQuadraticConditionOneStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unramified_quadratic_condition_one : PositivityTheory.SiegelWeilFormula.Gunr.Q1 := by
  first | exact @GlobalTheory.CompanionTheory.ResidueInvolution.q1 | exact GlobalTheory.CompanionTheory.ResidueInvolution.q1 | (intros; apply GlobalTheory.CompanionTheory.ResidueInvolution.q1 <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnramifiedQuadraticConditionThreeStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unramified_quadratic_condition_three : PositivityTheory.SiegelWeilFormula.Gunr.Q3 := by
  first | exact @GlobalTheory.CompanionTheory.GunrResCard.q3 | exact GlobalTheory.CompanionTheory.GunrResCard.q3 | (intros; apply GlobalTheory.CompanionTheory.GunrResCard.q3 <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnramifiedQuadraticConditionTwoStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unramified_quadratic_condition_two : PositivityTheory.SiegelWeilFormula.Gunr.Q2 := by
  first | exact @GlobalTheory.CompanionTheory.ValuationCompleteness.q2 | exact GlobalTheory.CompanionTheory.ValuationCompleteness.q2 | (intros; apply GlobalTheory.CompanionTheory.ValuationCompleteness.q2 <;> assumption)
end

