import Mathlib
import Formalism.LocalToGlobal.BesselHermitianTheta.Bundle0001
import Formalism.LocalToGlobal.BesselHermitianTheta.Bundle0002
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.Bundle0007
import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.IsotypicSignedParameters
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0022
import Formalism.LocalToGlobal.LatticeGeometry.Bundle0001
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0068
import Development.AbelianVarietyTheory.Counterexamples.LevelGroupExamples.Bundle0004
import Formalism.LocalToGlobal.BesselHermitianTheta.TiedWeil
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0067
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0040
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0001
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0039
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0005
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsFramedPointChangedByLetters
import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.Bundle0005
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsUniqueConstantTangentVectorsAlongArc
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.PmapsOfGenRelR
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0041
import Development.AbelianVarietyTheory.Proofs.HeightProofs.UnitaryLieGeneratorsRep

-- bundled from Development.AbelianVarietyTheory.Proofs.HeightProofs.AtPlaceIffEqAtTau
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.RealPar Matrix MeasureTheory
open scoped TensorProduct

namespace GlobalTheory.PointAtPlace

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice NumberField

variable {D : D7}

theorem tauE_injective : Function.Injective (tauE D) := fun _ _ h =>
  D.eTau.injective (Subtype.ext ((factEmb D.R D.host).1.1 h))

theorem tauE_cm (σ : D.host.E →+* ℂ) :
    (∃ ρ, tauE D ρ = σ) ↔ ¬ ∃ ρ, tauE D ρ = ComplexEmbedding.conjugate σ := by
  obtain ⟨g, rfl⟩ := (factEmb D.R D.host).1.2 σ
  have hc : ComplexEmbedding.conjugate (D.host.emb g) = D.host.emb (g * D.R.cc) := by
    rw [Formalism.L2.Geo.emb_mul_cc_comp]
    refine RingHom.ext fun x => ?_
    letI := D.host.cmStar
    haveI : IsCMField D.host.E := D.host.isCMField_hostE
    have h1 : star x = D.host.conj x := bridge_star_holds D.R D.host x
    have h2 : D.host.emb g (star x) = starRingEnd ℂ (D.host.emb g x) :=
      IsCMField.complexEmbedding_complexConj D.host.E (D.host.emb g) x
    rw [h1] at h2
    exact h2.symm
  have key : ∀ g', (∃ ρ, tauE D ρ = D.host.emb g') ↔ g' ∈ D.R.Psi := fun g' => by
    rw [← Formalism.L2.Geo.exists_tauEmb_iff D g']
    exact exists_congr fun ρ => eq_comm
  rw [hc, key, key]
  exact Formalism.L2.Geo.mem_Psi_iff_mul_cc_notMem g

theorem infMat_eq (V : HSp D) (θ : Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ) (h : GA D V) :
    letI := D.host.cmStar
    infMat D.sp.cm.sig V.gram θ h = Formalism.L2.Pj.archM V θ h := rfl

theorem archM_mul (V : HSp D) (θ : Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ) (a b : GA D V) :
    Formalism.L2.Pj.archM V θ (a * b) = Formalism.L2.Pj.archM V θ a * Formalism.L2.Pj.archM V θ b := by
  unfold Formalism.L2.Pj.archM
  rw [map_mul, Units.val_mul, Matrix.map_mul]

theorem archM_one (V : HSp D) (θ : Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ) :
    Formalism.L2.Pj.archM V θ 1 = 1 := by
  unfold Formalism.L2.Pj.archM
  rw [map_one, Units.val_one, Matrix.map_one _ (map_zero _) (map_one _)]

theorem eq_one_of_mem (V : HSp D) (k : GA D V) (h1 : k ∈ GfC V) (h2 : k ∈ GinfC V) : k = 1 := by
  obtain ⟨e, he, -⟩ := GlobalTheory.AdSplit.exists_adele_equiv D.host.F D.host.E
  have a1 : (infHom V k).1 = (infHom V 1).1 := by rw [map_one]; exact congrArg Units.val h1
  have a2 : (finHom V k).1 = (finHom V 1).1 := by rw [map_one]; exact congrArg Units.val h2
  refine Subtype.ext (Units.ext (Matrix.ext fun a b => e.injective (Prod.ext ?_ ?_)))
  · rw [(he _).1, (he _).1]; exact congrFun (congrFun a1 a) b
  · rw [(he _).2, (he _).2]; exact congrFun (congrFun a2 a) b

theorem existsUnique_isAtTau (V : HSp D) (τ : D.what₂.Tau)
    (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (hθ : IsInfFam θ)
    (g : Matrix (Fin V.rank) (Fin V.rank) ℂ) (hg : g ∈ Formalism.QuantumDeterminants.UH (Formalism.BasicNotions.TH.gramAt D V τ)) :
    ∃! h : GA D V, IsAtTau θ V τ g h := by
  classical
  let Ψ : Finset (D.host.E →+* ℂ) := Finset.univ.filter fun σ => ∃ ρ, tauE D ρ = σ
  have hmem : ∀ σ, σ ∈ Ψ ↔ ∃ ρ, tauE D ρ = σ := fun σ => by simp [Ψ]
  choose r hr using fun σ : Ψ => (hmem σ.1).1 σ.2
  have hsurj : ∀ ρ, r ⟨tauE D ρ, (hmem _).2 ⟨ρ, rfl⟩⟩ = ρ := fun ρ => tauE_injective (hr _)
  obtain ⟨h1, -, -, h2⟩ := (GlobalTheory.UnitaryGlue.adelic_glue D V).2 Ψ (fun σ => θ (r σ))
    (fun σ => by rw [hmem, hmem]; exact tauE_cm σ) (fun σ => by rw [← hr σ]; exact hθ _)
  obtain ⟨h, hh, hu⟩ := h2 (fun σ => if r σ = τ then g else 1) (fun σ => by
    by_cases c : r σ = τ
    · rw [if_pos c, ← hr σ, c]
      exact hg
    · rw [if_neg c, Matrix.map_one _ (map_zero _) (map_one _), Matrix.transpose_one, Matrix.one_mul,
        Matrix.mul_one])
  have hu' : ∀ ρ, Formalism.L2.Pj.archM V (θ ρ) h = if ρ = τ then g else 1 := fun ρ => by
    have := hu ⟨tauE D ρ, (hmem _).2 ⟨ρ, rfl⟩⟩
    simp only [hsurj] at this
    exact this
  refine ⟨h, ⟨hh, (hu' τ).trans (if_pos rfl), fun ρ c => (hu' ρ).trans (if_neg c)⟩, fun h' hh' => ?_⟩
  have e : ∀ ρ, Formalism.L2.Pj.archM V (θ ρ) h' = Formalism.L2.Pj.archM V (θ ρ) h := fun ρ => by
    rw [hu']
    by_cases c : ρ = τ
    · rw [if_pos c, c]; exact hh'.2.1
    · rw [if_neg c]; exact hh'.2.2 ρ c
  refine mul_inv_eq_one.1 (eq_one_of_mem V _ (h1 _ fun σ => ?_) (mul_mem hh'.1 (inv_mem hh)))
  rw [archM_mul, e, ← archM_mul, mul_inv_cancel, archM_one]

end GlobalTheory.PointAtPlace
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.HeightProofs.CocompactTensor
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta MeasureTheory NumberField IsDedekindDomain
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.AdelicMatrixLattice

section Tensor

variable {F E : Type} [Field F] [Field E] [Algebra F E] [FiniteDimensional F E]
  (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [IsTopologicalRing R]

theorem exists_coords : ∃ (n : ℕ) (e : R ⊗[F] E ≃ₜ (Fin n → R)) (b : E ≃ₗ[F] (Fin n → F)),
    (∀ x y, e (x + y) = e x + e y) ∧ ∀ x i, e (inclR R x) i = algebraMap F R (b x i) := by
  have : IsModuleTopology R (R ⊗[F] E) := ⟨rfl⟩
  have : IsTopologicalRing (R ⊗[F] E) := IsModuleTopology.isTopologicalRing R _
  let e := (Algebra.TensorProduct.basis R (Module.finBasis F E)).equivFun
  refine ⟨Module.finrank F E, { e.toEquiv with
    continuous_toFun := IsModuleTopology.continuous_of_linearMap e.toLinearMap
    continuous_invFun := IsModuleTopology.continuous_of_linearMap e.symm.toLinearMap },
    (Module.finBasis F E).equivFun, fun x y => e.map_add x y, fun x i => ?_⟩
  change (Algebra.TensorProduct.basis R (Module.finBasis F E)).repr ((1 : R) ⊗ₜ[F] x) i = _
  rw [Algebra.TensorProduct.basis_repr_tmul]
  simp

theorem discrete_tensor (h : ∃ U ∈ nhds (0 : R), ∀ x : F, algebraMap F R x ∈ U → x = 0) :
    ∃ U ∈ nhds (0 : R ⊗[F] E), ∀ x : E, inclR R x ∈ U → x = 0 := by
  obtain ⟨U, hU, hx⟩ := h
  obtain ⟨n, e, b, hadd, hb⟩ := exists_coords (F := F) (E := E) R
  have h0 : e 0 = 0 := by
    have := hadd 0 0
    rw [add_zero] at this
    exact left_eq_add.1 this
  refine ⟨e ⁻¹' (Set.univ.pi fun _ => U), ?_, fun x hxU => ?_⟩
  · refine e.continuous.continuousAt.preimage_mem_nhds ?_
    rw [h0]
    exact set_pi_mem_nhds Set.finite_univ fun _ _ => hU
  · refine b.injective ?_
    rw [map_zero]
    funext i
    refine hx _ ?_
    rw [← hb]
    exact hxU i (Set.mem_univ i)

theorem cocompact_tensor
    (h : ∃ K : Set R, IsCompact K ∧ ∀ a : R, ∃ x : F, a - algebraMap F R x ∈ K) :
    ∃ K : Set (R ⊗[F] E), IsCompact K ∧ ∀ a : R ⊗[F] E, ∃ x : E, inclR R x + a ∈ K := by
  obtain ⟨K, hK, hx⟩ := h
  obtain ⟨n, e, b, hadd, hb⟩ := exists_coords (F := F) (E := E) R
  refine ⟨e ⁻¹' (Set.univ.pi fun _ => K), e.isCompact_preimage.2 (isCompact_univ_pi fun _ => hK),
    fun a => ?_⟩
  choose c hc using hx
  refine ⟨b.symm fun i => - c (e a i), fun i _ => ?_⟩
  rw [hadd, Pi.add_apply, hb, b.apply_symm_apply, map_neg, neg_add_eq_sub]
  exact hc _

end Tensor

theorem lattice : ∀ (D : D7) (V W : HSp D), IsTopologicalAddGroup (WA V W) ∧ LocallyCompactSpace (WA V W) ∧ SecondCountableTopology (WA V W) ∧ T2Space (WA V W) ∧ DiscreteTopology (ratL V W) ∧ ∃ K : Set (WA V W), IsCompact K ∧ ∀ x : WA V W, ∃ γ ∈ ratL V W, γ + x ∈ K := by
  intro D V W
  have : LocallyCompactSpace (AF D.host.F) := GlobalTheory.AdelicUnitaryTop.locallyCompact_adele _
  have : SecondCountableTopology (AF D.host.F) := GlobalTheory.AdelicUnitaryTop.secondCountable_adele _
  have : T2Space (AF D.host.F) := GlobalTheory.AdelicUnitaryTop.t2Space_adeleRing_numberField _
  have : IsModuleTopology (AF D.host.F) (AE D) := ⟨rfl⟩
  have : IsTopologicalRing (AE D) := IsModuleTopology.isTopologicalRing (AF D.host.F) _
  obtain ⟨e⟩ := GlobalTheory.AdelicUnitaryTop.nonempty_homeomorph (F := D.host.F) (E := D.host.E)
    (AF D.host.F)
  have : LocallyCompactSpace (AE D) := e.isClosedEmbedding.locallyCompactSpace
  have : SecondCountableTopology (AE D) := e.secondCountableTopology
  have : T2Space (AE D) := e.isEmbedding.t2Space
  have hg : IsTopologicalAddGroup (WA V W) :=
    inferInstanceAs (IsTopologicalAddGroup (Fin V.rank → Fin W.rank → AE D))
  refine ⟨hg, inferInstanceAs (LocallyCompactSpace (Fin V.rank → Fin W.rank → AE D)),
    inferInstanceAs (SecondCountableTopology (Fin V.rank → Fin W.rank → AE D)),
    inferInstanceAs (T2Space (Fin V.rank → Fin W.rank → AE D)), ?_, ?_⟩
  · obtain ⟨U, hU, hx⟩ := discrete_tensor (F := D.host.F) (E := D.host.E) (AF D.host.F)
      (GlobalTheory.AdeleDiscrete.exists_nhds_zero_principal_eq_zero D.host.F)
    have hN : (Set.univ.pi fun _ : Fin V.rank => Set.univ.pi fun _ : Fin W.rank => U) ∈
        nhds (0 : WA V W) :=
      set_pi_mem_nhds Set.finite_univ fun _ _ => set_pi_mem_nhds Set.finite_univ fun _ _ => hU
    refine discreteTopology_of_isOpen_singleton_zero ?_
    rw [isOpen_singleton_iff_nhds_eq_pure]
    refine le_antisymm (Filter.le_pure_iff.2 ?_) (pure_le_nhds _)
    have hc : ContinuousAt (fun x : ratL V W => (x : WA V W)) 0 :=
      continuous_subtype_val.continuousAt
    refine Filter.mem_of_superset (hc.preimage_mem_nhds hN) ?_
    rintro ⟨_, y, rfl⟩ hy
    have hy0 : y = 0 := by
      funext i j
      exact hx _ (hy i (Set.mem_univ i) j (Set.mem_univ j))
    subst hy0
    exact Subtype.ext (map_zero _)
  · obtain ⟨K, hK, hx⟩ := cocompact_tensor (F := D.host.F) (E := D.host.E) (AF D.host.F)
      (GlobalTheory.AdeleCocompact.exists_compact_adele D.host.F)
    choose c hc using hx
    refine ⟨Set.univ.pi fun _ : Fin V.rank => Set.univ.pi fun _ : Fin W.rank => K,
      isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => hK, fun x => ?_⟩
    exact ⟨_, ⟨Matrix.of fun i j => c (x i j), rfl⟩, fun i _ j _ => hc (x i j)⟩

end GlobalTheory.AdelicMatrixLattice
end

-- bundled from Development.AbelianVarietyTheory.Proofs.HeightProofs.EnvelopingMapSurjectiveStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.SmoothForms Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance 100] LieRing.ofAssociativeRing
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.enveloping_map_surjective : ∀ (D : D7) (V : HSp D) (τ : D.what₂.Tau), Function.Surjective (GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.envOf V τ) := by
  first | exact @GlobalTheory.EnvWords.envOf_surjective | exact GlobalTheory.EnvWords.envOf_surjective | (intros; apply GlobalTheory.EnvWords.envOf_surjective <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsCompactAdeleRingModNumberFieldStatement
section
open NumberField IsDedekindDomain MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_compact_adeleRing_mod_numberField : ∀ (F : Type) [Field F] [NumberField F], ∃ K : Set (AdeleRing (𝓞 F) F), IsCompact K ∧ ∀ a : AdeleRing (𝓞 F) F, ∃ x : F, a - algebraMap F (AdeleRing (𝓞 F) F) x ∈ K := by
  first | exact @GlobalTheory.AdeleCocompact.exists_compact_adele | exact GlobalTheory.AdeleCocompact.exists_compact_adele | (intros; apply GlobalTheory.AdeleCocompact.exists_compact_adele <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsEnvelopingAlgHomUnitaryLieAlgebraStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.SmoothForms Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance 100] LieRing.ofAssociativeRing
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_envelopingAlgHom_unitaryLieAlgebra : ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) ℂ) (A : Type) [Ring A] [Algebra ℂ A] (ρ : GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.lieU J → A), (∀ X Y, ρ (X + Y) = ρ X + ρ Y) → (∀ (c : ℝ) X, ρ (c • X) = (c : ℂ) • ρ X) → (∀ X Y Z : GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.lieU J, Z.1 = X.1 * Y.1 - Y.1 * X.1 → ρ Z = ρ X * ρ Y - ρ Y * ρ X) → ∃ π : UniversalEnvelopingAlgebra ℂ (ℂ ⊗[ℝ] GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.lieU J) →ₐ[ℂ] A, ∀ X, π (UniversalEnvelopingAlgebra.ι ℂ ((1 : ℂ) ⊗ₜ[ℝ] X)) = ρ X := by
  first | exact @GlobalTheory.EnvelopingExtension.exists_algHom_unitary | exact GlobalTheory.EnvelopingExtension.exists_algHom_unitary | (intros; apply GlobalTheory.EnvelopingExtension.exists_algHom_unitary <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsFiniteCosetsAdelicUnitaryBoundedDenominato
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.SmoothForms Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance 100] LieRing.ofAssociativeRing

namespace GlobalTheory.SmoothForms.Cover

open NumberField IsDedekindDomain Topology

theorem exists_finset_of_compact {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (H : Subgroup G) (U : Subgroup H) (hU : IsOpen (U : Set H)) (K : Set G) (hK : IsCompact K)
    (Ω : Set H) (hΩ : ∀ k ∈ Ω, (k : G) ∈ K) :
    ∃ S : Finset H, (∀ x ∈ S, x ∈ Ω) ∧ ∀ k ∈ Ω, ∃ x ∈ S, x⁻¹ * k ∈ U := by
  classical
  obtain ⟨W, hW, hWU⟩ := isOpen_induced_iff.1 hU
  have h1 : (1 : G) ∈ W := by
    have : (1 : H) ∈ (U : Set H) := U.one_mem
    rw [← hWU] at this
    exact this
  have hc : Continuous fun p : G × G => p.1⁻¹ * p.2 := by fun_prop
  have h2 : (fun p : G × G => p.1⁻¹ * p.2) ⁻¹' W ∈ 𝓝 ((1, 1) : G × G) :=
    (hW.preimage hc).mem_nhds (by simpa using h1)
  obtain ⟨A, hA, B, hB, hAB⟩ := mem_nhds_prod_iff.1 h2
  obtain ⟨t, -, ht⟩ := hK.elim_nhds_subcover (fun x => (fun y => x⁻¹ * y) ⁻¹' (A ∩ B)) (fun x _ => by
    have : Continuous fun y : G => x⁻¹ * y := by fun_prop
    exact this.continuousAt.preimage_mem_nhds (by simpa using ⟨hA, hB⟩))
  have hch : ∀ x : G, (∃ s ∈ Ω, x⁻¹ * (s : G) ∈ A ∩ B) → ∃ s ∈ Ω, x⁻¹ * (s : G) ∈ A ∩ B := fun _ h => h
  choose f hf hf' using hch
  refine ⟨(t.filter fun x => ∃ s ∈ Ω, x⁻¹ * (s : G) ∈ A ∩ B).attach.image
    fun x => f x.1 (by have h := x.2; rw [Finset.mem_filter] at h; exact h.2), ?_, ?_⟩
  · intro x hx
    obtain ⟨y, -, rfl⟩ := Finset.mem_image.1 hx
    exact hf _ _
  · intro k hk
    obtain ⟨x, hx, hxk⟩ := Set.mem_iUnion₂.1 (ht (hΩ k hk))
    have hex : ∃ s ∈ Ω, x⁻¹ * (s : G) ∈ A ∩ B := ⟨k, hk, hxk⟩
    refine ⟨f x hex, Finset.mem_image.2 ⟨⟨x, Finset.mem_filter.2 ⟨hx, hex⟩⟩, Finset.mem_attach _ _, rfl⟩, ?_⟩
    have h3 := hAB (Set.mk_mem_prod (hf' x hex).1 hxk.2)
    have h4 : (x⁻¹ * (f x hex : G))⁻¹ * (x⁻¹ * (k : G)) = (((f x hex)⁻¹ * k : H) : G) := by
      push_cast; group
    change _ ∈ (U : Set H)
    rw [← hWU]
    change _ ∈ W
    rw [← h4]
    exact h3

theorem isCompact_GL {A : Type} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [T2Space A] {n : ℕ}
    (C : Fin n → Fin n → Set A) (hC : ∀ i j, IsCompact (C i j)) :
    IsCompact {g : GL (Fin n) A | ∀ i j, g.1 i j ∈ C i j ∧ (g⁻¹).1 i j ∈ C i j} := by
  have h1 : IsCompact {m : Matrix (Fin n) (Fin n) A | ∀ i j, m i j ∈ C i j} :=
    isCompact_pi_infinite fun i => isCompact_pi_infinite (hC i)
  have h2 := (Units.isClosedEmbedding_embedProduct (α := Matrix (Fin n) (Fin n) A)).isCompact_preimage
    (h1.prod (h1.image MulOpposite.continuous_op))
  convert h2 using 1
  ext g
  simp only [Set.mem_setOf_eq, Set.mem_preimage, Units.embedProduct_apply, Set.mem_prod, Set.mem_image,
    MulOpposite.op_inj, exists_eq_right, forall_and]

theorem exists_compact_denom (D : D7) (d : ℕ) (hd : 0 < d) :
    ∃ C : Set (Af D.host.F ⊗[D.host.F] D.host.E), IsCompact C ∧ ∀ y, d • y ∈ intAE D → y ∈ C := by
  classical
  haveI : IsModuleTopology (Af D.host.F) (Af D.host.F ⊗[D.host.F] D.host.E) := ⟨rfl⟩
  haveI : Module.Finite D.host.F D.host.E := Module.Finite.of_restrictScalars_finite ℚ _ _
  haveI : IsTopologicalRing (Af D.host.F ⊗[D.host.F] D.host.E) :=
    IsModuleTopology.isTopologicalRing (Af D.host.F) _
  let b := RingOfIntegers.basis D.host.E
  let O : AddSubgroup (Af D.host.F) :=
    { carrier := {a | ∀ v, a v ∈ v.adicCompletionIntegers D.host.F}
      zero_mem' := fun v => zero_mem _
      add_mem' := fun ha hb v => add_mem (ha v) (hb v)
      neg_mem' := fun ha v => neg_mem (ha v) }
  let φ : (Module.Free.ChooseBasisIndex ℤ (𝓞 D.host.E) → Af D.host.F) →+
      Af D.host.F ⊗[D.host.F] D.host.E :=
    { toFun := fun a => ∑ i, a i • ((1 : Af D.host.F) ⊗ₜ[D.host.F] (b i : D.host.E))
      map_zero' := by simp
      map_add' := fun x y => by simp [add_smul, Finset.sum_add_distrib] }
  have hφ : Continuous φ :=
    continuous_finset_sum _ fun i _ => (continuous_apply i).fun_smul continuous_const
  have hle : intAE D ≤ (AddSubgroup.pi Set.univ fun _ => O).map φ := by
    refine (AddSubgroup.closure_le _).2 ?_
    rintro y ⟨a, ha, x, rfl⟩
    refine ⟨fun i => b.repr x i • a, fun i _ => zsmul_mem (show a ∈ O from ha) _, ?_⟩
    change ∑ i, (b.repr x i • a) • ((1 : Af D.host.F) ⊗ₜ[D.host.F] (b i : D.host.E)) = _
    conv_rhs => rw [← b.sum_repr x]
    change _ = a ⊗ₜ[D.host.F] (algebraMap (𝓞 D.host.E) D.host.E _)
    rw [map_sum, TensorProduct.tmul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_zsmul, smul_assoc, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    exact (map_zsmul (TensorProduct.mk D.host.F (Af D.host.F) D.host.E a) _ _).symm
  have hO : IsCompact (Set.pi Set.univ fun _ : Module.Free.ChooseBasisIndex ℤ (𝓞 D.host.E) =>
      (O : Set (Af D.host.F))) :=
    isCompact_univ_pi fun _ => GlobalTheory.AdeleCocompact.isCompact_integral D.host.F
  let c : Af D.host.F := algebraMap D.host.F (Af D.host.F) (d : D.host.F)⁻¹
  have hcs : Continuous fun y : Af D.host.F ⊗[D.host.F] D.host.E => c • y :=
    (continuous_const (y := c)).fun_smul continuous_id
  refine ⟨(fun y => c • y) '' (φ '' _), (hO.image hφ).image hcs, fun y hy => ?_⟩
  refine ⟨d • y, hle hy, ?_⟩
  have : (d : D.host.F) ≠ 0 := Nat.cast_ne_zero.mpr hd.ne'
  change c • d • y = y
  rw [← Nat.cast_smul_eq_nsmul (Af D.host.F), smul_smul,
    ← map_natCast (algebraMap D.host.F (Af D.host.F)) d, ← map_mul, inv_mul_cancel₀ this, map_one, one_smul]

theorem exists_finset_cover : ∀ (D : D7) (V : HSp D) (U : Subgroup (GA D V)), IsOpen (U : Set (GA D V)) → ∀ d : ℕ, 0 < d → ∃ S : Finset (GA D V), ∀ k ∈ GfC V, BddDen V d k → ∃ x ∈ S, x⁻¹ * k ∈ U ∧ x⁻¹ * k ∈ GfC V := by
  intro D V U hU d hd
  haveI : IsModuleTopology (AF D.host.F) (AE D) := ⟨rfl⟩
  haveI : Module.Finite D.host.F D.host.E := Module.Finite.of_restrictScalars_finite ℚ _ _
  haveI : IsTopologicalRing (AE D) := IsModuleTopology.isTopologicalRing (AF D.host.F) _
  haveI := GlobalTheory.AdelicUnitaryTop.t2Space_adeleRing_numberField D.host.F
  obtain ⟨e0⟩ := GlobalTheory.AdelicUnitaryTop.nonempty_homeomorph (F := D.host.F) (E := D.host.E) (AF D.host.F)
  haveI : T2Space (AE D) := e0.isEmbedding.t2Space
  obtain ⟨C, hC, hCd⟩ := exists_compact_denom D d hd
  obtain ⟨e, he, -, hc⟩ := GlobalTheory.AdSplit.exists_adele_equiv D.host.F D.host.E
  let C' : Fin V.rank → Fin V.rank → Set (AE D) := fun i j =>
    e.symm '' ({(1 : Matrix (Fin V.rank) (Fin V.rank) (Ainf D.host.F ⊗[D.host.F] D.host.E)) i j} ×ˢ C)
  have hC' : ∀ i j, IsCompact (C' i j) := fun i j => (isCompact_singleton.prod hC).image hc
  have key : ∀ k ∈ GfC V, (∀ i j, d • finMat D.sp.cm.sig V.gram k i j ∈ intAE D) →
      ∀ i j, (matHom V k).1 i j ∈ C' i j := by
    intro k hk h i j
    refine ⟨e ((matHom V k).1 i j), ⟨?_, ?_⟩, e.symm_apply_apply _⟩
    · rw [(he _).1]
      have h1 : (infHom V k).1 i j = _ := congrArg (fun g => g.1 i j) (MonoidHom.mem_ker.1 hk)
      exact h1
    · rw [(he _).2]
      exact hCd _ (h i j)
  obtain ⟨S, hS, hS'⟩ := exists_finset_of_compact (HR (AF D.host.F) D.sp.cm.sig V.gram) U hU _
    (isCompact_GL C' hC') {k : GA D V | k ∈ GfC V ∧ BddDen V d k} (fun k hk i j =>
      ⟨key k hk.1 (fun i j => (hk.2 i j).1) i j, key k⁻¹ (inv_mem hk.1) (fun i j => (hk.2 i j).2) i j⟩)
  refine ⟨S, fun k hk hb => ?_⟩
  obtain ⟨x, hx, hxk⟩ := hS' k ⟨hk, hb⟩
  exact ⟨x, hx, hxk, mul_mem (inv_mem (hS x hx).1) hk⟩

end GlobalTheory.SmoothForms.Cover
end

-- bundled from Development.AbelianVarietyTheory.Proofs.HeightProofs.LieIdentityArcWitnessIff
section
noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField CartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.ArcQ

namespace GlobalTheory.LieIdImg

open ReciprocityTheory.ChartRestriction.G.Chart (dualMapR)

theorem genRelR_iff_genThrough {A : Type} [CommRing A] [IsLocalRing A] {B B₀ Y : Scheme.{0}} {M : LB B} {M₀ : LB B₀}
    {φ : B ⟶ B₀} {w : LB.Iso M (M₀.pull φ)} (hw : w.IsGen) (hM : M.IsLB) (hM₀ : M₀.IsLB) {K : Type} [Fintype K]
    {ε : K → ℤ} {pt : K → (Sp A ⟶ B)} {pt₀ : K → (Y ⟶ B₀)} {t : LB.Gen (LB.LinComb M pt ε)}
    {t₀ : LB.Gen (LB.LinComb M₀ pt₀ ε)} (ht : t.IsGen) (ht₀ : t₀.IsGen) (h : Sp A ⟶ Y) :
    GenRelR w t (LB.pullGen _ _ _ t₀ h) ↔ GlobalTheory.IndefiniteRowSideFullHecke.SectionsThroughEpsilonPoints.GenThrough w ε t t₀ h := by
  constructor
  · intro H
    refine ⟨H.1, fun Z r z p q hp hq => ?_⟩
    have e := ConstGrp.pmaps_of_genRelR ((isGen_iff w).1 hw) hM hM₀ ht (DVR.pullGen_isGen _ _ _ _ ht₀ h) H
      Z r z p q hp hq
    rwa [gm_pullGen', Category.comp_id] at e
  · rintro ⟨h₁, h₂⟩
    refine (genRelR_iff w t _).2 ⟨h₁, fun j j₀ hj₀ hj => ?_⟩
    have e := h₂ _ (𝟙 _) (cpt A) j₀ j hj₀ hj
    simp only [Category.id_comp] at e
    rw [gm_pullGen', Category.id_comp, e]

theorem dualMap_inl {R R' : Type} [CommRing R] [CommRing R'] (f : R →+* R') (r : R) :
    dualMap f (TrivSqZeroExt.inl r) = TrivSqZeroExt.inl (f r) := by
  ext <;> simp [dualMap]

theorem dualMap_eps {R R' : Type} [CommRing R] [CommRing R'] (f : R →+* R') :
    dualMap f DualNumber.eps = DualNumber.eps := by
  ext <;> simp [dualMap]

theorem eq_dualMap {R R' : Type} [CommRing R] [CommRing R'] (f : R →+* R') (ρ : DualNumber R →+* DualNumber R')
    (h : ∀ r, ρ (TrivSqZeroExt.inl r) = TrivSqZeroExt.inl (f r)) (h' : ρ DualNumber.eps = DualNumber.eps) :
    ρ = dualMap f :=
  (ConstTan.eq_dualMapR f ρ h h').trans (ConstTan.eq_dualMapR f _ (dualMap_inl f) (dualMap_eps f)).symm

theorem lieId_iff : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (A : Type) [CommRing A] [IsDomain A] [IsLocalRing A] (b : O →+* A) (a : ArcIn Dw l β A b) (χ : Sp (PowerSeries A) ⟶ Y.X) (W : Wit Y a χ) (ν : Out.GtPt a.D₀ (epsR A)) (v : epsR (PowerSeries A) ⟶ W.t.G), GlobalTheory.IndefiniteRowSideFullHecke.SectionsThroughEpsilonPoints.LieId W ν v ↔ (GlobalTheory.IndefiniteRowSideFullHecke.SectionsThroughEpsilonPoints.IsTanGt ν ∧ LieImg W ν v) := by
  intro E _ _ _ H Dw l Xo c O _ β Y A _ _ _ b a χ W ν v
  refine and_congr_right fun _ => ?_
  let I : Ideal (PowerSeries A) := Ideal.span {PowerSeries.X}
  have hloc : ∀ n, IsLocalRing (DualNumber (PowerSeries A ⧸ I ^ (n + 1))) := fun n =>
    have : IsLocalRing (PowerSeries A ⧸ I ^ (n + 1)) :=
      isLocalRing_quotient_pow (ConstLie.span_X_ne_top (A := A)) n
    ConstTan.isLocalRing_dual _
  have hs : ∀ n, spMap (algebraMap (PowerSeries A ⧸ I ^ (n + 1)) (DualNumber (PowerSeries A ⧸ I ^ (n + 1)))) ≫
      Out.thick (PowerSeries A) I n =
      spMap (dualMap (Ideal.Quotient.mk (I ^ (n + 1)))) ≫ (epsR (PowerSeries A)).hom := fun n =>
    (ConstLie.spMap_comp' _ _).trans ((congrArg spMap
      (RingHom.ext fun r => (dualMap_inl (Ideal.Quotient.mk (I ^ (n + 1))) r).symm)).trans
        (ConstLie.spMap_comp' _ _).symm)
  constructor
  · intro h n ρ κ vn h₁ h₂ h₃ h₄ _ h₆ x
    have := hloc n
    obtain ⟨vn', k₁, -, k₃⟩ := h n
    obtain rfl := eq_dualMap _ ρ h₁ h₂
    obtain rfl := eq_dualMap ((Ideal.Quotient.mk _).comp (PowerSeries.C (R := A))) κ h₃ h₄
    have := thick_mono (PowerSeries A) I n
    have hm : Mono (pullback.fst W.t.G.hom (Out.thick (PowerSeries A) I n)) := inferInstance
    obtain rfl : vn = vn' := hm.right_cancellation _ _ (h₆.trans k₁.symm)
    exact (genRelR_iff_genThrough W.spec.2.1 W.P.D.toPre.P.isLB a.D₀.P.isLB
      (DVR.pullGen_isGen _ _ _ _ ((W.P.U.gt n).t_gen _) vn) (ν.isGen x) _).2 (k₃ x)
  · intro h n
    have := hloc n
    let vn : Sp (DualNumber (PowerSeries A ⧸ I ^ (n + 1))) ⟶ (Out.thickObj (PowerSeries A) I n W.t.G).left :=
      pullback.lift (spMap (dualMap (Ideal.Quotient.mk (I ^ (n + 1)))) ≫ v.left) (spMap (algebraMap _ _))
        (by rw [Category.assoc, Over.w v, hs])
    have h' := h n _ _ vn (dualMap_inl _) (dualMap_eps _)
      (dualMap_inl ((Ideal.Quotient.mk _).comp (PowerSeries.C (R := A)))) (dualMap_eps _)
      (pullback.lift_snd _ _ _) (pullback.lift_fst _ _ _)
    refine ⟨vn, pullback.lift_fst _ _ _, (Category.assoc _ _ _).symm.trans ((h' 0).1 2), fun x => ?_⟩
    exact (genRelR_iff_genThrough W.spec.2.1 W.P.D.toPre.P.isLB a.D₀.P.isLB
      (DVR.pullGen_isGen _ _ _ _ ((W.P.U.gt n).t_gen _) vn) (ν.isGen x) _).1 (h' x)

end GlobalTheory.LieIdImg
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.HeightProofs.NormInfSubmultiplicativeLeAdelicHeightStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.SmoothForms Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance 100] LieRing.ofAssociativeRing
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.normInf_submultiplicative_le_adelicHeight : ∀ (D : D7) (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (V : HSp D), (∀ g h : GA D V, normInf θ V (g * h) ≤ normInf θ V g * normInf θ V h) ∧ ∃ C : ℝ, ∀ g : GA D V, normInf θ V g ≤ C * (GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.height θ V g : ℝ) := by
  first | exact @GlobalTheory.SmoothForms.normInf_mul_le_and_le_height | exact GlobalTheory.SmoothForms.normInf_mul_le_and_le_height | (intros; apply GlobalTheory.SmoothForms.normInf_mul_le_and_le_height <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.HeightProofs.UnitaryAdelicHeightCosetLeNormInfPowStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.SmoothForms Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance 100] LieRing.ofAssociativeRing
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitaryAdelicHeight_coset_le_normInf_pow : ∀ (D : D7) (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (V : HSp D), ∃ M : ℕ, ∀ x : GA D V, ∃ C : ℝ, ∀ g ∈ GinfC V, (GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.height θ V (x * g) : ℝ) ≤ C * normInf θ V g ^ M := by
  first | exact @GlobalTheory.SmoothForms.HeightCoset.height_le_normInf_pow | exact GlobalTheory.SmoothForms.HeightCoset.height_le_normInf_pow | (intros; apply GlobalTheory.SmoothForms.HeightCoset.height_le_normInf_pow <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.HeightProofs.UnitaryLieGeneratorsRepStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.SmoothForms Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance 100] LieRing.ofAssociativeRing
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitary_lie_generators_rep : ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) ℂ), Jᴴ = J → IsUnit J.det → ∃ P Q : Fin n → Fin n → GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.lieU J, (∀ a b, (P a b).1 = (1 / 2 : ℂ) • (Matrix.single a b 1 + -(J⁻¹ * (Matrix.single a b (1 : ℂ))ᴴ * J)) ∧ (Q a b).1 = (1 / (2 * Complex.I)) • (Matrix.single a b 1 - -(J⁻¹ * (Matrix.single a b (1 : ℂ))ᴴ * J))) ∧ ∀ (A : Type) [Ring A] [Algebra ℂ A] (ρ : GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.lieU J → A), (∀ X Y, ρ (X + Y) = ρ X + ρ Y) → (∀ (c : ℝ) X, ρ (c • X) = (c : ℂ) • ρ X) → (∀ X Y Z : GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.lieU J, Z.1 = X.1 * Y.1 - Y.1 * X.1 → ρ Z = ρ X * ρ Y - ρ Y * ρ X) → Formalism.REAL.GlRel (fun a b => ρ (P a b) + Complex.I • ρ (Q a b)) ∧ ∀ X, ρ X ∈ Submodule.span ℂ (Set.range fun p : Fin n × Fin n => ρ (P p.1 p.2) + Complex.I • ρ (Q p.1 p.2)) := by
  first | exact @GlobalTheory.UnitaryLieComplexification.glRel_and_span | exact GlobalTheory.UnitaryLieComplexification.glRel_and_span | (intros; apply GlobalTheory.UnitaryLieComplexification.glRel_and_span <;> assumption)
end

