import Mathlib
import Development.WeilBound.ThetaLifts.LatticeBasics.Bundle0008
import Development.WeilBound.ThetaLifts.LatticeBasics.Bundle0015
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0462
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0485
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.CuspRapidDecaySiegelGL
import GroundTheory.AutomorphicForms.CuspidalDiscreteness.CuspFormsHeight
import GroundTheory.AutomorphicForms.CuspidalDiscreteness.DecayUniform
import GroundTheory.AutomorphicForms.AutomorphicFormSpaces.GKStable
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0471
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0470
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0423
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0442
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1307
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0017
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0472
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0009
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0446
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0429
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0473
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0447
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.RealDescent.RealLeviDescent.Bundle0001
import CompanionTheory.RealGroups.DiscreteSeries.DiscreteSeriesClassification.DiscreteSeriesExhaustion.FarRegularity.LKTExists
import CompanionTheory.HarishChandraModules.LowKTypeMultiplicity.EigenspaceCyclicDensity.CreationOperators.DifferentialBoundedSupport
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0457

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IntegersBoundedEmbeddingsCount
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl
open GlobalTheory.Doubling (absE)
open GlobalTheory.CompanionTheory.GodementH

namespace GlobalTheory.CompanionTheory.IntegerCount

theorem card_bounded_conjugates_le :
    ∀ (E : Type) [Field E] [NumberField E], ∃ C : ℝ, 0 < C ∧ ∀ R : ℝ, 1 ≤ R →
    {β : 𝓞 E | ∀ τ : E →+* ℂ, ‖τ (β : E)‖ ≤ R}.Finite ∧
    (Set.ncard {β : 𝓞 E | ∀ τ : E →+* ℂ, ‖τ (β : E)‖ ≤ R} : ℝ) ≤ C * R ^ Module.finrank ℚ E := by
  intro E _ _
  classical
  let ι := Module.Free.ChooseBasisIndex ℤ (𝓞 E)
  let b : Module.Basis ι ℤ (𝓞 E) := RingOfIntegers.basis E
  let B := canonicalEmbedding.latticeBasis E

  let L : ι → (((E →+* ℂ) → ℂ) →L[ℂ] ℂ) := fun i => LinearMap.toContinuousLinearMap (B.coord i)
  let C₀ : ℝ := ∑ i, ‖L i‖
  have hC₀ : 0 ≤ C₀ := Finset.sum_nonneg fun _ _ => norm_nonneg _
  have hcoord : ∀ (β : 𝓞 E) (i : ι), L i (canonicalEmbedding E (β : E)) = ((b.repr β i : ℤ) : ℂ) := by
    intro β i
    have hx : canonicalEmbedding E (β : E) = ∑ j, ((b.repr β j : ℤ) : ℂ) • B j := by
      have h0 : (β : E) = ∑ j, ((b.repr β j : ℤ) : E) * ((b j : 𝓞 E) : E) := by
        conv_lhs => rw [← b.sum_repr β]
        simp [map_sum, zsmul_eq_mul]
      rw [h0, map_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      ext τ
      simp [B, b, canonicalEmbedding.latticeBasis_apply, integralBasis_apply]
    change B.coord i _ = _
    rw [hx, map_sum]
    simp [Module.Basis.coord_apply, Finsupp.single_apply]
  have hbound : ∀ (R : ℝ), 1 ≤ R → ∀ β : 𝓞 E, (∀ τ : E →+* ℂ, ‖τ (β : E)‖ ≤ R) →
      ∀ i, |((b.repr β i : ℤ) : ℝ)| ≤ C₀ * R := by
    intro R hR β hβ i
    have hx : ‖canonicalEmbedding E (β : E)‖ ≤ R :=
      (pi_norm_le_iff_of_nonneg (by linarith)).2 fun τ => by simpa using hβ τ
    have h1 : ‖L i (canonicalEmbedding E (β : E))‖ ≤ ‖L i‖ * R :=
      ((L i).le_opNorm _).trans (mul_le_mul_of_nonneg_left hx (norm_nonneg _))
    rw [hcoord, Complex.norm_intCast] at h1
    refine h1.trans (mul_le_mul_of_nonneg_right ?_ (by linarith))
    exact Finset.single_le_sum (f := fun i => ‖L i‖) (fun _ _ => norm_nonneg _) (Finset.mem_univ i)
  have hcard : Fintype.card ι = Module.finrank ℚ E := by
    rw [← RingOfIntegers.rank E]
    exact (Module.finrank_eq_card_chooseBasisIndex ℤ (𝓞 E)).symm
  refine ⟨(2 * C₀ + 1) ^ Module.finrank ℚ E, by positivity, fun R hR => ?_⟩
  set S : Set (𝓞 E) := {β : 𝓞 E | ∀ τ : E →+* ℂ, ‖τ (β : E)‖ ≤ R} with hS
  let N : ℤ := ⌊C₀ * R⌋
  have hN0 : 0 ≤ N := Int.floor_nonneg.2 (by nlinarith)
  let box : Finset (ι → ℤ) := Fintype.piFinset fun _ => Finset.Icc (-N) N
  let f : 𝓞 E → (ι → ℤ) := fun β i => b.repr β i
  have hf : Function.Injective f := by
    intro x y hxy
    apply b.repr.injective
    ext i
    exact congrFun hxy i
  have hmaps : Set.MapsTo f S (box : Set (ι → ℤ)) := by
    intro β hβ
    simp only [box, Finset.mem_coe, Fintype.mem_piFinset, Finset.mem_Icc]
    intro i
    have h := abs_le.1 (hbound R hR β hβ i)
    constructor
    · have h2 : -(b.repr β i) ≤ N := Int.le_floor.2 (by push_cast; linarith [h.1])
      change -N ≤ b.repr β i
      omega
    · exact Int.le_floor.2 h.2
  have hfin : S.Finite := Set.Finite.of_injOn hmaps hf.injOn box.finite_toSet
  refine ⟨hfin, ?_⟩
  have hle : S.ncard ≤ box.card := by
    have h := Set.ncard_le_ncard_of_injOn f hmaps hf.injOn box.finite_toSet
    rwa [Set.ncard_coe_finset] at h
  have hboxcard : (box.card : ℝ) = (2 * (N : ℝ) + 1) ^ Module.finrank ℚ E := by
    have h1 : ((Finset.Icc (-N) N).card : ℤ) = 2 * N + 1 := by
      rw [Int.card_Icc]
      omega
    have h2 : ((Finset.Icc (-N) N).card : ℝ) = 2 * (N : ℝ) + 1 := by
      exact_mod_cast h1
    simp only [box, Fintype.card_piFinset, Finset.prod_const, Finset.card_univ, hcard]
    push_cast
    rw [h2]
  have hNle : (N : ℝ) ≤ C₀ * R := Int.floor_le _
  calc (S.ncard : ℝ) ≤ box.card := by exact_mod_cast hle
    _ = (2 * (N : ℝ) + 1) ^ Module.finrank ℚ E := hboxcard
    _ ≤ ((2 * C₀ + 1) * R) ^ Module.finrank ℚ E := by
        have hN0' : (0 : ℝ) ≤ N := by exact_mod_cast hN0
        exact pow_le_pow_left₀ (by positivity) (by nlinarith) _
    _ = (2 * C₀ + 1) ^ Module.finrank ℚ E * R ^ Module.finrank ℚ E := mul_pow _ _ _

end GlobalTheory.CompanionTheory.IntegerCount
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IrreducibleSubquotientOfExtension
section
noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.CompanionTheory.BZNuPair

namespace GlobalTheory.CompanionTheory.SubquotExt

theorem isSubquotient_sub_or_quot :
    ∀ (G V W : Type) [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] (ρ : Representation ℂ G V) (σ : Representation ℂ G W)
    (A B : Subrepresentation ρ), A ≤ B → σ.IsIrreducible → IsSubquotient σ B.toRepresentation →
    IsSubquotient σ A.toRepresentation ∨ IsSubquotient σ (subQuot B A) := by
  intro G V W _ _ _ _ _ ρ σ A B hAB hσ hB
  haveI : IsSimpleOrder (Subrepresentation σ) := hσ
  unfold GlobalTheory.SmGL.IsSubquotient at hB ⊢
  obtain ⟨S, f, hf⟩ := hB
  let P : Submodule ℂ S.toSubmodule :=
    (A.toSubmodule.comap B.toSubmodule.subtype).comap S.toSubmodule.subtype
  have hNinv : ∀ (g : G) ⦃w : W⦄, w ∈ P.map f.toLinearMap → σ g w ∈ P.map f.toLinearMap := by
    intro g w hw
    rw [Submodule.mem_map] at hw ⊢
    obtain ⟨s, hs, rfl⟩ := hw
    have hs' : ((s : B.toSubmodule) : V) ∈ A.toSubmodule := hs
    refine ⟨S.toRepresentation g s, A.apply_mem_toSubmodule g hs', ?_⟩
    exact f.isIntertwining _ _ g s
  let N : Subrepresentation σ := ⟨P.map f.toLinearMap, hNinv⟩
  let Z : Subrepresentation σ := ⟨⊥, by
    intro g w hw
    rw [Submodule.mem_bot] at hw ⊢
    rw [hw, map_zero]⟩
  let Fu : Subrepresentation σ := ⟨⊤, by
    intro g w _
    exact Submodule.mem_top⟩
  rcases IsSimpleOrder.eq_bot_or_eq_top N with hN | hN
  · right
    have hle : N ≤ Z := by
      rw [hN]
      exact bot_le
    have hfP : P ≤ LinearMap.ker f.toLinearMap := by
      intro s hs
      have h0 : f.toLinearMap s ∈ (⊥ : Submodule ℂ W) := hle (Submodule.mem_map_of_mem hs)
      exact LinearMap.mem_ker.2 ((Submodule.mem_bot ℂ).1 h0)
    let A' : Submodule ℂ B.toSubmodule := A.toSubmodule.comap B.toSubmodule.subtype
    have hQ : ∀ (g : G) (b : B.toSubmodule), GlobalTheory.SmGL.subQuot B A g (A'.mkQ b) =
        A'.mkQ (B.toRepresentation g b) := by
      intro g b
      first
      | rfl
      | (unfold GlobalTheory.SmGL.subQuot
         rw [Representation.quotient_apply]
         rfl)
    have hSinv : ∀ (g : G) ⦃x : B.toSubmodule ⧸ A'⦄, x ∈ S.toSubmodule.map A'.mkQ →
        GlobalTheory.SmGL.subQuot B A g x ∈ S.toSubmodule.map A'.mkQ := by
      intro g x hx
      rw [Submodule.mem_map] at hx ⊢
      obtain ⟨b, hb, rfl⟩ := hx
      exact ⟨B.toRepresentation g b, S.apply_mem_toSubmodule g hb, (hQ g b).symm⟩
    let S'' : Subrepresentation (GlobalTheory.SmGL.subQuot B A) := ⟨S.toSubmodule.map A'.mkQ, hSinv⟩
    let ψ0 : S.toSubmodule →ₗ[ℂ] (S.toSubmodule.map A'.mkQ) :=
      LinearMap.codRestrict _ (A'.mkQ ∘ₗ S.toSubmodule.subtype) (fun s => Submodule.mem_map_of_mem s.2)
    have hPker : P ≤ LinearMap.ker ψ0 := by
      intro s hs
      have hs' : (s : B.toSubmodule) ∈ A' := hs
      rw [LinearMap.mem_ker]
      exact Subtype.ext ((Submodule.Quotient.mk_eq_zero A').2 hs')
    have hkerP : LinearMap.ker ψ0 ≤ P := by
      intro s hs
      rw [LinearMap.mem_ker] at hs
      have h2 : (Submodule.Quotient.mk (s : B.toSubmodule) : B.toSubmodule ⧸ A') = 0 := congrArg Subtype.val hs
      exact (Submodule.Quotient.mk_eq_zero A').1 h2
    have hinj : Function.Injective (P.liftQ ψ0 hPker) :=
      LinearMap.ker_eq_bot.1 (Submodule.ker_liftQ_eq_bot P ψ0 hPker hkerP)
    have hsurj : Function.Surjective (P.liftQ ψ0 hPker) := by
      intro x
      obtain ⟨y, hy⟩ := x
      rw [Submodule.mem_map] at hy
      obtain ⟨b, hb, rfl⟩ := hy
      exact ⟨Submodule.Quotient.mk ⟨b, hb⟩, rfl⟩
    let e := LinearEquiv.ofBijective (P.liftQ ψ0 hPker) ⟨hinj, hsurj⟩
    let F'' : (S.toSubmodule.map A'.mkQ) →ₗ[ℂ] W := P.liftQ f.toLinearMap hfP ∘ₗ e.symm.toLinearMap
    have key : ∀ s, F'' (ψ0 s) = f s := by
      intro s
      have he : ψ0 s = e (Submodule.Quotient.mk s) := rfl
      show P.liftQ f.toLinearMap hfP (e.symm (ψ0 s)) = f s
      rw [he, LinearEquiv.symm_apply_apply]
      rfl
    have hrep : ∀ (g : G) (s : S.toSubmodule), S''.toRepresentation g (ψ0 s) = ψ0 (S.toRepresentation g s) :=
      fun g s => Subtype.ext (hQ g s)
    have hψ0 : ∀ x : S.toSubmodule.map A'.mkQ, ∃ s, ψ0 s = x := by
      intro x
      obtain ⟨y, rfl⟩ := hsurj x
      obtain ⟨s, rfl⟩ := Submodule.mkQ_surjective P y
      exact ⟨s, rfl⟩
    let f'' : S''.toRepresentation.IntertwiningMap σ := ⟨F'', fun g => LinearMap.ext fun x => by
      obtain ⟨s, rfl⟩ := hψ0 x
      show F'' (S''.toRepresentation g (ψ0 s)) = σ g (F'' (ψ0 s))
      rw [hrep, key, key]
      exact f.isIntertwining _ _ g s⟩
    refine ⟨S'', f'', fun w => ?_⟩
    obtain ⟨s, rfl⟩ := hf w
    exact ⟨ψ0 s, key s⟩
  · left
    have hge : Fu ≤ N := by
      rw [hN]
      exact le_top
    have hAB' : A.toSubmodule ≤ B.toSubmodule := fun x hx => hAB hx
    have hS'inv : ∀ (g : G) ⦃a : A.toSubmodule⦄, a ∈ S.toSubmodule.comap (Submodule.inclusion hAB') →
        A.toRepresentation g a ∈ S.toSubmodule.comap (Submodule.inclusion hAB') := by
      intro g a ha
      exact S.apply_mem_toSubmodule g ha
    let S' : Subrepresentation A.toRepresentation := ⟨S.toSubmodule.comap (Submodule.inclusion hAB'), hS'inv⟩
    let r : (S.toSubmodule.comap (Submodule.inclusion hAB')) →ₗ[ℂ] S.toSubmodule :=
      (Submodule.inclusion hAB').restrict (fun a ha => ha)
    let f' : S'.toRepresentation.IntertwiningMap σ := ⟨f.toLinearMap ∘ₗ r, fun g => LinearMap.ext fun x => by
      show f.toLinearMap (r (S'.toRepresentation g x)) = σ g (f.toLinearMap (r x))
      exact f.isIntertwining _ _ g (r x)⟩
    refine ⟨S', f', fun w => ?_⟩
    have hw : w ∈ P.map f.toLinearMap := hge (Submodule.mem_top : w ∈ (⊤ : Submodule ℂ W))
    rw [Submodule.mem_map] at hw
    obtain ⟨s, hs, rfl⟩ := hw
    have hs' : ((s : B.toSubmodule) : V) ∈ A.toSubmodule := hs
    have ha : (⟨((s : B.toSubmodule) : V), hs'⟩ : A.toSubmodule) ∈ S.toSubmodule.comap (Submodule.inclusion hAB') := by
      first
      | exact s.2
      | simpa using s.2
    exact ⟨⟨⟨((s : B.toSubmodule) : V), hs'⟩, ha⟩, rfl⟩

end GlobalTheory.CompanionTheory.SubquotExt

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsAddHaarMeasureUnipMeasure
section
noncomputable section

open NumberField MeasureTheory GlobalTheory.CuspRep GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.Reduction
open scoped NumberField.AdeleRing

namespace GlobalTheory.CompanionTheory.CuspBridge

theorem unipGL_eq_unip {R : Type} [CommRing R] {a r : ℕ} (X : AutomorphicForm.UPos a r → R) :
    AutomorphicForm.unipGL X = unip X := by
  apply Units.ext
  rfl

theorem isAddHaarMeasure_unipMeasure (E : Type) [Field E] [NumberField E] (a r : ℕ) :
    (AutomorphicForm.unipMeasure E a r).IsAddHaarMeasure := by
  infer_instance

theorem isCuspidal_of_isCuspForm : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (φ : Sm E a),
    IsCuspForm φ → AutomorphicForm.IsCuspidal φ.1 := by
  intro E _ _ _ a φ h r h0 h1 g
  have h2 := h.2 r h0 h1 (AutomorphicForm.unipMeasure E a r) (AutomorphicForm.unipFundamentalDomain E a r)
    (isAddHaarMeasure_unipMeasure E a r) AutomorphicForm.isAddFundamentalDomain_unipFundamentalDomain g
  simpa only [AutomorphicForm.constantTerm, unipGL_eq_unip] using h2

end GlobalTheory.CompanionTheory.CuspBridge

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsCompactStandardMaximalStatement
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl
open GlobalTheory.Doubling (absE)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isCompact_standard_maximal : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n : ℕ) (Y : Spc F E n) (r s : ℕ), B.IsGood σ → 1 ≤ n → (Y.IsHerm σ B r s ∨ Y.IsSkew σ B r s) → ∀ (b : GL (Fin n ⊕ Fin n) E) (K : Subgroup (G2 σ Y)) (a : G2 σ Y → ℝ), IsFrame2 σ Y b → IsStdK (σ := σ) (Y := Y) B b K → IsHgt K a → IsCompact (K : Set (G2 σ Y)) := by
  first | exact @GlobalTheory.CompanionTheory.StdK.isCompact_K | exact GlobalTheory.CompanionTheory.StdK.isCompact_K | (intros; apply GlobalTheory.CompanionTheory.StdK.isCompact_K <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsLeftInvariantOfIsAutForm
section
open NumberField GlobalTheory.CuspRep GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.Reduction
open scoped NumberField.AdeleRing

namespace GlobalTheory.CompanionTheory.LeftInv

theorem ratGL_eq_diagonal (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ)
    (γ : GL (Fin a) E) : ratGL E a γ = AdelicGLn.diagonal E a γ :=
  Units.ext (Matrix.ext fun _ _ => rfl)

theorem isLeftInvariant_of_isAutForm : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E]
    (a : ℕ) (φ : Sm E a), IsAutForm φ → AutomorphicForm.IsLeftInvariant φ.1 := by
  intro E _ _ _ a φ h γ g
  rw [← ratGL_eq_diagonal]
  exact h.left γ g

end GlobalTheory.CompanionTheory.LeftInv
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsOpenRightInvarianceOrbitCoefficientStatement
section
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.BZPhiPG
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isOpen_right_invariance_orbit_coefficient : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (i t : ℕ) (ψ : AddChar k Circle) (τ : MRep k (i + 1)) (σ : GRep k (t + 1)) (f : XS τ σ),
  IsOpen {g : Mir k (i + (t + 1)) | ∀ m, eO ψ f (m * g) = eO ψ f m} := by
  first | exact @GlobalTheory.CompanionTheory.BZPhiPG.isOpen_eO_rightPeriods | exact GlobalTheory.CompanionTheory.BZPhiPG.isOpen_eO_rightPeriods | (intros; apply GlobalTheory.CompanionTheory.BZPhiPG.isOpen_eO_rightPeriods <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IwahoriDoubleCosetTorusNilpotent
section
noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL Matrix ValuativeRel GlobalTheory.CompanionTheory.IwJac
open scoped Classical

namespace GlobalTheory.CompanionTheory.IwJac.DCoset

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}

theorem tor_inv (ϖ : kˣ) (x : Fin n → ℤ) : (tor ϖ x)⁻¹ = tor ϖ (fun i => - x i) := by
  unfold tor
  rw [← map_inv]
  congr 1
  funext i
  simp [_root_.zpow_neg]

theorem conj_apply (ϖ : kˣ) (x : Fin n → ℤ) (l : GL (Fin n) k) (i j : Fin n) :
    (((tor ϖ x)⁻¹ * l * tor ϖ x : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) i j =
      ((ϖ ^ (x j - x i) : kˣ) : k) * (l : Matrix (Fin n) (Fin n) k) i j := by
  rw [tor_inv, Units.val_mul, Units.val_mul]
  unfold tor
  rw [val_diagT, val_diagT, Matrix.mul_diagonal, Matrix.diagonal_mul, sub_eq_add_neg, add_comm (x j),
    _root_.zpow_add, Units.val_mul]
  ring

theorem val_zpow_lt_one {ϖ : kˣ} (hϖ : ord k ϖ = 1) {m : ℤ} (hm : 0 < m) :
    valuation k ((ϖ ^ m : kˣ) : k) < 1 := by
  have h := GlobalTheory.OrdShellInt.val_le_iff_ord (k := k) 1 (ϖ ^ m)
  rw [GlobalTheory.OrdShellInt.ord_zpow, hϖ, ord_eq_zero (by simp)] at h
  rw [Units.val_one, map_one] at h
  exact not_le.1 fun h' => absurd (h.1 h') (by omega)

theorem conj_entries {ϖ : kˣ} (hϖ : ord k ϖ = 1) {x : Fin n → ℤ} (hx : StrictAnti x) {l : GL (Fin n) k}
    (hl : l ∈ iwahori k (Fin n) ⊓ unipBLower k (Fin n)) (i j : Fin n) :
    valuation k ((((tor ϖ x)⁻¹ * l * tor ϖ x : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) i j) ≤ 1 ∧
      (j < i → valuation k ((((tor ϖ x)⁻¹ * l * tor ϖ x : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) i j) < 1) := by
  obtain ⟨h0, h1⟩ := GlobalTheory.IwahoriTraceProof.mem_unipBLower.1 hl.2
  have hint : valuation k ((l : Matrix (Fin n) (Fin n) k) i j) ≤ 1 :=
    (Valuation.mem_integer_iff _ _).1 (((GlobalTheory.SplitFlip.mem_KO_iff l).1 (iwahori_le_KO k (Fin n) hl.1)).1 i j)
  rw [conj_apply]
  rcases lt_trichotomy i j with h | rfl | h
  · rw [h0 i j h, mul_zero, map_zero]
    exact ⟨zero_le', fun h' => absurd h' h.not_gt⟩
  · rw [h1, sub_self]
    simp
  · have hlt : valuation k (((ϖ ^ (x j - x i) : kˣ) : k) * (l : Matrix (Fin n) (Fin n) k) i j) < 1 := by
      rw [map_mul]
      refine lt_of_le_of_lt (mul_le_mul' le_rfl hint) ?_
      rw [mul_one]
      exact val_zpow_lt_one hϖ (sub_pos.2 (hx h))
    exact ⟨hlt.le, fun _ => hlt⟩

theorem conj_mem_iwahori {ϖ : kˣ} (hϖ : ord k ϖ = 1) {x : Fin n → ℤ} (hx : StrictAnti x) {l : GL (Fin n) k}
    (hl : l ∈ iwahori k (Fin n) ⊓ unipBLower k (Fin n)) :
    (tor ϖ x)⁻¹ * l * tor ϖ x ∈ iwahori k (Fin n) := by
  refine mem_iwahori.2 ⟨(GlobalTheory.SplitFlip.mem_KO_iff _).2 ⟨fun i j => ?_, fun i j => ?_⟩,
    fun i j hij => (conj_entries hϖ hx hl i j).2 hij⟩
  · exact (Valuation.mem_integer_iff _ _).2 (conj_entries hϖ hx hl i j).1
  · have e : ((tor ϖ x)⁻¹ * l * tor ϖ x)⁻¹ = (tor ϖ x)⁻¹ * l⁻¹ * tor ϖ x := by group
    rw [e]
    exact (Valuation.mem_integer_iff _ _).2 (conj_entries hϖ hx (inv_mem hl) i j).1

theorem diagT_conj_tor (ϖ : kˣ) (x : Fin n → ℤ) (s : Fin n → kˣ) :
    tor ϖ x * diagT k (Fin n) s * (tor ϖ x)⁻¹ = diagT k (Fin n) s := by
  have e : tor ϖ x * diagT k (Fin n) s = diagT k (Fin n) s * tor ϖ x := by
    unfold tor
    rw [← map_mul, ← map_mul, mul_comm]
  rw [e]
  group

end GlobalTheory.CompanionTheory.IwJac.DCoset

namespace GlobalTheory.CompanionTheory.IwJac

theorem iwahori_mul_tor_mul_iwahori : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (n : ℕ) (ϖ : kˣ), ord k ϖ = 1 → ∀ x : Fin n → ℤ, StrictAnti x →
    ∀ a ∈ iwahori k (Fin n), ∀ b ∈ iwahori k (Fin n), ∃ m ∈ nO k n, ∃ c ∈ iwahori k (Fin n),
      a * tor ϖ x * b = m * tor ϖ x * c := by
  intro k _ _ _ _ n ϖ hϖ x hx a ha b hb
  obtain ⟨c, hc, τ, hτ, l, hl, rfl⟩ := GlobalTheory.CompanionTheory.IwahoriDatumGL.fact_up' k n ha
  refine ⟨c, hc, τ * ((tor ϖ x)⁻¹ * l * tor ϖ x) * b,
    mul_mem (mul_mem hτ.1 (DCoset.conj_mem_iwahori hϖ hx hl)) hb, ?_⟩
  obtain ⟨s, rfl⟩ := hτ.2
  calc c * diagT k (Fin n) s * l * tor ϖ x * b
      = c * (tor ϖ x * diagT k (Fin n) s * (tor ϖ x)⁻¹) * l * tor ϖ x * b := by
        rw [DCoset.diagT_conj_tor]
    _ = c * tor ϖ x * (diagT k (Fin n) s * ((tor ϖ x)⁻¹ * l * tor ϖ x) * b) := by group

end GlobalTheory.CompanionTheory.IwJac

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.L2ConvolutionLocallyCompactMemStatement
section
open MeasureTheory GlobalTheory.AutomorphicL2Unitary GlobalTheory.OpTrace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.l2_convolution_locally_compact_mem : ∀ {G L : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [SecondCountableTopology G] [T2Space G] [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G] (Γ : Subgroup G) [DiscreteTopology Γ] (μ : Measure G) [μ.IsMulLeftInvariant] [μ.IsMulRightInvariant] [IsFiniteMeasureOnCompacts μ] [Group L] [TopologicalSpace L] [IsTopologicalGroup L] [SecondCountableTopology L] [T2Space L] [LocallyCompactSpace L] [MeasurableSpace L] [BorelSpace L] (ν : Measure L) [IsFiniteMeasureOnCompacts ν] (j : L →* G), Continuous j → ∀ D : L → ℂ, Continuous D → HasCompactSupport D → ∀ φ ψ : G → ℂ, Continuous φ → ∀ h : MemL2Quotient Γ μ φ, (∀ g, ψ g = ∫ y, φ (g * j y) * D y ∂ν) → ∃ h' : MemL2Quotient Γ μ ψ, ∀ W : Submodule ℂ (L2 Γ μ), IsSubrep (R Γ μ) W → h.toL2 ∈ W → h'.toL2 ∈ W := by
  first | exact @GlobalTheory.CompanionTheory.AutomorphicL2Convolution.memL2_convolution_mem | exact GlobalTheory.CompanionTheory.AutomorphicL2Convolution.memL2_convolution_mem | (intros; apply GlobalTheory.CompanionTheory.AutomorphicL2Convolution.memL2_convolution_mem <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LastRowUpdateNhdsGenerationStatement
section
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.BZPhiPG GlobalTheory.CompanionTheory.BZPhiPG.OntoO Topology
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.last_row_update_nhds_generation : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (S : Subgroup (GL (Fin (n + 1)) k))
    (hS : ∀ (r : Fin (n + 1) → k), r (Fin.last n) ≠ 0 → ∀ g : GL (Fin (n + 1)) k,
      (g : Matrix (Fin (n + 1)) (Fin (n + 1)) k) = (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) k).updateRow (Fin.last n) r → g ∈ S)
    (O : Set (Mir k n)) (hO : O ∈ 𝓝 (1 : Mir k n)),
    ∃ N ∈ 𝓝 (1 : GL (Fin (n + 1)) k), ∀ p ∈ S, ∀ x ∈ N, ∀ m : Mir k n, (m : GL (Fin (n + 1)) k) = p * x →
      ∃ a : Mir k n, (a : GL (Fin (n + 1)) k) ∈ S ∧ ∃ x' ∈ O, m = a * x' := by
  first | exact @GlobalTheory.CompanionTheory.BZPhiPG.OntoO.RowRep.row_replacement | exact GlobalTheory.CompanionTheory.BZPhiPG.OntoO.RowRep.row_replacement | (intros; apply GlobalTheory.CompanionTheory.BZPhiPG.OntoO.RowRep.row_replacement <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LatticeMaxEvenAlmostAllStatement
section
open NumberField IsDedekindDomain Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet PositivityTheory.ThKR GlobalTheory.CompanionTheory.KFin
open Formalism.UG (cT)
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lattice_max_even_almost_all : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {r : ℕ} {X Y : Matrix (Fin n) (Fin r) E}, IsCMExt F E σ → IsHermND σ J → IsWittFrame σ J X Y → ∃ (L : Submodule (𝓞 E) (Fin n → E)) (_ : Submodule.IsLattice E L), ∀ᶠ v in Filter.cofinite, IsMaxEven (sigR (Fv F v) σ) (intLoc F E v) (hR (Fv F v) σ J) (latLoc F L v) ∧ IsAdapted (intLoc F E v) (hR (Fv F v) σ J) (colV v X) (colV v Y) (latLoc F L v) := by
  first | exact @GlobalTheory.CompanionTheory.KFin.AE.exists_lattice_maxEven_adapted | exact GlobalTheory.CompanionTheory.KFin.AE.exists_lattice_maxEven_adapted | (intros; apply GlobalTheory.CompanionTheory.KFin.AE.exists_lattice_maxEven_adapted <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LeftInvertibleExistsNonzeroMinor
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl
open GlobalTheory.Doubling (absE)
open GlobalTheory.CompanionTheory.GodementH

namespace GlobalTheory.CompanionTheory.GodementH

theorem det_mul_eq_sum_mnr {R : Type} [CommRing R] {ι : Type} [Fintype ι] [DecidableEq ι] {n : ℕ}
    (M : Matrix ι (Fin n) R) (L : Matrix (Fin n) ι R) :
    (L * M).det = ∑ g : Fin n → ι, (∏ i, L i (g i)) * mnr M g := by
  have h1 : (L * M).det =
      (Matrix.detRowAlternating (R := R) (n := Fin n)).toMultilinearMap
        (fun i => ∑ j, L i j • M j) := by
    have : (L * M) = Matrix.of (fun i => ∑ j, L i j • M j) := by
      ext i k
      simp [Matrix.mul_apply, Finset.sum_apply]
    rw [this]
    rfl
  rw [h1, MultilinearMap.map_sum]
  refine Finset.sum_congr rfl fun g _ => ?_
  rw [MultilinearMap.map_smul_univ]
  rfl

theorem exists_mnr_ne_zero_of_left_inverse :
    ∀ (R : Type) [CommRing R] [Nontrivial R] (ι : Type) [Fintype ι] [DecidableEq ι] (n : ℕ)
      (M : Matrix ι (Fin n) R) (L : Matrix (Fin n) ι R),
      L * M = 1 → ∃ f, mnr M f ≠ 0 := by
  intro R _ _ ι _ _ n M L h
  by_contra hc
  push_neg at hc
  have key := det_mul_eq_sum_mnr M L
  rw [h, Matrix.det_one] at key
  simp [hc] at key

end GlobalTheory.CompanionTheory.GodementH
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LeviAdjointOnChainsStatement
section
open Finset PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD GlobalTheory.CompanionTheory.LvChain
open CompanionTheory.D.LK (Pos)
open scoped InnerProductSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.levi_adjoint_on_chains : ∀ (n : ℕ) (lev : Fin n → ℕ) (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] (E1 E2 : Fin n → Fin n → Module.End ℂ V),
    (∀ a b (x y : V), ⟪kA E1 E2 a b x, y⟫_ℂ = ⟪x, kA E1 E2 b a y⟫_ℂ) → ∀ p q : Fin n, lev p = lev q → ∀ x z : Cq n V,
      ∑ A, ⟪Lv lev E1 E2 p q x A, z A⟫_ℂ = ∑ A, ⟪x A, Lv lev E1 E2 q p z A⟫_ℂ := by
  first | exact @GlobalTheory.CompanionTheory.LvChainAdj.Lv_adjoint | exact GlobalTheory.CompanionTheory.LvChainAdj.Lv_adjoint | (intros; apply GlobalTheory.CompanionTheory.LvChainAdj.Lv_adjoint <;> assumption)
end

