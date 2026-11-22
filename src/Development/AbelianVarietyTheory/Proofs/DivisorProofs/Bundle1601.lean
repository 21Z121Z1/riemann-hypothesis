import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0025
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SecondChernDegreeVanishesTrueSurfaces
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1583
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1568
import Development.AbelianVarietyTheory.Definitions.Divisors.IsSquareIntegrableIffMemL2
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0332
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1552
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0597
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0033
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0038
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TateUnramifiedOfTorsionUnramified
import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1569
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0032
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
import GroundTheory.AutomorphicForms.MultiplicityOne.Bundle0001
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsFlagModelHermSum
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0056
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0037
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0166
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.Bundle0031
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0129
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SiegelFamilyTangentDimensionBound
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsPointPrimitiveBundleEqTranslatePpav
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1579
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1574
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0173
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0009
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsAbelianSchemeAndExtendOfGenericHoms
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0052
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteAffineNeighbourhoodExists
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1536
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1570
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1537

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRegularCoverOfAlteration
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.RegCoverExists

set_option autoImplicit false in
open CategoryTheory AlgebraicGeometry in
private theorem isSeparated_spMap {R R' : Type} [CommRing R] [CommRing R'] (c : R →+* R') :
    IsSeparated (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap c) := by
  have : IsAffine (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp R) := by
    show IsAffine (Spec (CommRingCat.of R)); infer_instance
  have : IsAffine (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp R') := by
    show IsAffine (Spec (CommRingCat.of R')); infer_instance
  infer_instance

set_option autoImplicit false in
open CategoryTheory AlgebraicGeometry in

theorem _root_.GlobalTheory.RegCoverExists.isProjOver_of_comp_spMap {R R' : Type} [CommRing R] [CommRing R'] (c : R →+* R')
    {Y : Scheme.{0}} {f : Y ⟶ _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp R'} (h : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsProjOver (f ≫ _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap c)) : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsProjOver f := by
  obtain ⟨N, i, hi, hif⟩ := h
  have hP := _root_.GlobalTheory.ProjSpace.isPullback_baseChange N c
  haveI := isSeparated_spMap c
  haveI : IsSeparated (_root_.GlobalTheory.ProjSpace.baseChange N c) :=
    MorphismProperty.of_isPullback (P := @IsSeparated) hP.flip inferInstance
  refine ⟨N, hP.lift i f hif, ?_, hP.lift_snd _ _ _⟩
  haveI : IsClosedImmersion (hP.lift i f hif ≫ _root_.GlobalTheory.ProjSpace.baseChange N c) := by
    rw [hP.lift_fst]; exact hi
  exact IsClosedImmersion.of_comp _ (_root_.GlobalTheory.ProjSpace.baseChange N c)

theorem isArithVar_of_toSpZ {k : Type} [CommRing k] (hd : IsDomain k) (hf : Module.Finite ℤ k) {Y : Scheme.{0}}
    (f : Y ⟶ Sp k) {s : Y ⟶ Sp ℤ} {D : ℕ} (h : IsArithVar s D) : IsArithVar f D :=
  ⟨hd, hf, h.isIntegral,
    isProjOver_of_comp_spMap (Int.castRingHom k)
      (specZIsTerminal.hom_ext s (f ≫ spMap (Int.castRingHom k)) ▸ h.isProjOver),
    specZIsTerminal.hom_ext (s ≫ spMap (Int.castRingHom ℤ)) (f ≫ spMap (Int.castRingHom k)) ▸ h.flat, h.dim_eq⟩

theorem nonempty_regCover : Published.RegularAlteration → ∀ (k : Type) [CommRing k] (Y : Scheme.{0}) (q : Y ⟶ Sp k)
    [IsIntegral Y], IsArithVar q 1 → Nonempty (RegCover q) := by
  intro H k _ Y q _ h
  obtain ⟨Z, _, ρ, hZ, hr, hg, hd⟩ := H Y _ 1 (ShFam.Pad.isArithVar_toSpZ h)
  exact ⟨⟨Z, ρ, ⟨isArithVar_of_toSpZ h.isDomain h.finite _ hZ, hr⟩, hg, hd⟩⟩

end GlobalTheory.RegCoverExists

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsShortExactOfComposition
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.HermFrame GlobalTheory.CurveDens GlobalTheory.Cartier
open scoped ComplexOrder

namespace GlobalTheory.ThirdIso

open CategoryTheory.Limits

theorem abelian {C : Type*} [Category C] [Abelian C] {A M B L Q V : C}
    (f : A ⟶ M) (g : M ⟶ B) (u : A ⟶ B) (q₀ : M ⟶ L) (q₁ : B ⟶ Q) (q₂ : B ⟶ V)
    (w₀ : f ≫ q₀ = 0) (w₁ : g ≫ q₁ = 0) (w₂ : u ≫ q₂ = 0)
    (hS₀ : (ShortComplex.mk f q₀ w₀).ShortExact)
    (hS₁ : (ShortComplex.mk g q₁ w₁).ShortExact)
    (hS₂ : (ShortComplex.mk u q₂ w₂).ShortExact) (hfg : f ≫ g = u) :
    ∃ (l : L ⟶ V) (m : V ⟶ Q) (w₃ : l ≫ m = 0), (ShortComplex.mk l m w₃).ShortExact ∧
      q₀ ≫ l = g ≫ q₂ ∧ q₂ ≫ m = q₁ := by
  have e₀ : Epi q₀ := hS₀.epi_g
  have e₁ : Epi q₁ := hS₁.epi_g
  have e₂ : Epi q₂ := hS₂.epi_g
  have mg : Mono g := hS₁.mono_f
  have c₀ := hS₀.exact.gIsCokernel
  have c₂ := hS₂.exact.gIsCokernel
  have a₀ : f ≫ g ≫ q₂ = 0 := by rw [← Category.assoc, hfg, w₂]
  have a₂ : u ≫ q₁ = 0 := by rw [← hfg, Category.assoc, w₁, comp_zero]
  obtain ⟨l, hl⟩ : ∃ l : L ⟶ V, q₀ ≫ l = g ≫ q₂ :=
    ⟨c₀.desc (CokernelCofork.ofπ _ a₀), c₀.fac (CokernelCofork.ofπ _ a₀) WalkingParallelPair.one⟩
  obtain ⟨m, hm⟩ : ∃ m : V ⟶ Q, q₂ ≫ m = q₁ :=
    ⟨c₂.desc (CokernelCofork.ofπ _ a₂), c₂.fac (CokernelCofork.ofπ _ a₂) WalkingParallelPair.one⟩
  have w₃ : l ≫ m = 0 := by
    rw [← cancel_epi q₀, comp_zero, ← Category.assoc, hl, Category.assoc, hm, w₁]
  refine ⟨l, m, w₃, ?_, hl, hm⟩
  have em : Epi m := by
    subst hm
    exact epi_of_epi q₂ m
  have ml : Mono l := by
    refine Preadditive.mono_of_cancel_zero _ ?_
    intro T x hx
    obtain ⟨T₁, p₁, _, y, hy⟩ := surjective_up_to_refinements_of_epi q₀ x
    have hy0 : (y ≫ g) ≫ q₂ = 0 := by
      rw [Category.assoc, ← hl, ← Category.assoc, ← hy, Category.assoc, hx, comp_zero]
    obtain ⟨T₂, p₂, _, z, hz⟩ :=
      (ShortComplex.exact_iff_exact_up_to_refinements _).1 hS₂.exact (y ≫ g) hy0
    dsimp at hz
    have hz' : p₂ ≫ y = z ≫ f := by
      rw [← cancel_mono g, Category.assoc, Category.assoc, hfg, hz]
    rw [← cancel_epi (p₂ ≫ p₁), comp_zero, Category.assoc, hy, ← Category.assoc, hz',
      Category.assoc, w₀, comp_zero]
  have ex : (ShortComplex.mk l m w₃).Exact := by
    rw [ShortComplex.exact_iff_exact_up_to_refinements]
    intro T x hx
    dsimp at x hx
    obtain ⟨T₁, p₁, _, y, hy⟩ := surjective_up_to_refinements_of_epi q₂ x
    have hy0 : y ≫ q₁ = 0 := by
      rw [← hm, ← Category.assoc, ← hy, Category.assoc, hx, comp_zero]
    obtain ⟨T₂, p₂, _, z, hz⟩ :=
      (ShortComplex.exact_iff_exact_up_to_refinements _).1 hS₁.exact y hy0
    dsimp at hz
    refine ⟨T₂, p₂ ≫ p₁, inferInstance, z ≫ q₀, ?_⟩
    dsimp
    rw [Category.assoc, hy, ← Category.assoc, hz, Category.assoc, Category.assoc, hl]
  exact { exact := ex, mono_f := ml, epi_g := em }

end GlobalTheory.ThirdIso

theorem GlobalTheory.ThirdIso.modules : ∀ (X : Scheme.{0}) (A M B L Q V : X.Modules) (f : A ⟶ M) (g : M ⟶ B) (u : A ⟶ B) (q₀ : M ⟶ L) (q₁ : B ⟶ Q) (q₂ : B ⟶ V) (w₀ : f ≫ q₀ = 0) (w₁ : g ≫ q₁ = 0) (w₂ : u ≫ q₂ = 0) (hS₀ : (ShortComplex.mk f q₀ w₀).ShortExact) (hS₁ : (ShortComplex.mk g q₁ w₁).ShortExact) (hS₂ : (ShortComplex.mk u q₂ w₂).ShortExact), f ≫ g = u → ∃ (l : L ⟶ V) (m : V ⟶ Q) (w₃ : l ≫ m = 0), (ShortComplex.mk l m w₃).ShortExact ∧ q₀ ≫ l = g ≫ q₂ ∧ q₂ ≫ m = q₁ := by
  intro X A M B L Q V f g u q₀ q₁ q₂ w₀ w₁ w₂ hS₀ hS₁ hS₂ hfg
  exact GlobalTheory.ThirdIso.abelian f g u q₀ q₁ q₂ w₀ w₁ w₂ hS₀ hS₁ hS₂ hfg
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSignatureDiagonalisingBasisStatement
section
open scoped TensorProduct Matrix
open NumberField Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_signature_diagonalising_basis : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
    ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ K' : Subgroup (GAd σ J), GlobalTheory.UAut.IsMaxCpt σ J K' →
      ∀ (k : GAd σ J) (w : InfinitePlace F) (τ : EmbOver E w), ∃ (C : GL (Fin n) ℂ) (ε : Fin n → Bool),
        C.1ᴴ * J.map τ.1 * C.1 = Matrix.diagonal (fun i => if ε i then 1 else -1) ∧
        ∀ y : GArch σ J w, ((C⁻¹).1 * GlobalTheory.Orb.archMat σ J τ y * C.1)ᴴ * ((C⁻¹).1 * GlobalTheory.Orb.archMat σ J τ y * C.1) = 1 →
          k⁻¹ * embArch σ J w y * k ∈ K' := by
  first | exact @GlobalTheory.ArchFrameConj.exists_frame_mem_conj | exact GlobalTheory.ArchFrameConj.exists_frame_mem_conj | (intros; apply GlobalTheory.ArchFrameConj.exists_frame_mem_conj <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSmulMemSpanOrbitOfNumberFieldLattice
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory
open scoped Matrix

namespace GlobalTheory.CyclicLattice

theorem exists_linearIndependent_mulVec_pow {R : Type} [CommRing R] [IsDomain R] {r : ℕ}
    (g : Matrix (Fin r) (Fin r) R) (hg : LinearIndependent R (fun i : Fin r => g ^ (i : ℕ))) :
    ∃ v : Fin r → R, LinearIndependent R (fun i : Fin r => (g ^ (i : ℕ)) *ᵥ v) := by
  classical
  let K := FractionRing R
  let f := algebraMap R K
  have hf : Function.Injective f := IsFractionRing.injective R K
  let gK := g.map f
  let Φ : Matrix (Fin r) (Fin r) R →ₗ[R] Matrix (Fin r) (Fin r) K :=
    (Algebra.linearMap R K).mapMatrix
  have hΦ : Function.Injective Φ := fun a a' h => by
    ext i j
    exact hf (congrFun (congrFun h i) j)
  have hgK : LinearIndependent K (fun i : Fin r => gK ^ (i : ℕ)) := by
    have h1 := hg.map' Φ (LinearMap.ker_eq_bot.2 hΦ)
    have h2 : (Φ ∘ fun i : Fin r => g ^ (i : ℕ)) = fun i : Fin r => gK ^ (i : ℕ) := by
      funext i
      simp only [Function.comp_apply, gK, ← Matrix.map_pow]
      rfl
    rw [h2] at h1
    exact (LinearIndependent.iff_fractionRing R K).mp h1
  obtain ⟨w, hw⟩ :=
    GlobalTheory.CyclicVector.exists_linearIndependent_iterates_of_linearIndependent_pow gK hgK
  obtain ⟨s, hs⟩ := IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors R) w
  choose u hu using hs
  refine ⟨u, ?_⟩
  let Ψ : (Fin r → R) →ₗ[R] (Fin r → K) :=
    LinearMap.pi (fun i => (Algebra.linearMap R K).comp (LinearMap.proj i))
  have hΨ : Function.Injective Ψ := fun a a' h => funext fun i => hf (congrFun h i)
  have hfu : (f ∘ u) = (f s) • w := funext fun j => by
    simpa [Algebra.smul_def] using hu j
  have key : (Ψ ∘ fun i : Fin r => g ^ (i : ℕ) *ᵥ u) =
      fun i : Fin r => (f s) • (gK ^ (i : ℕ) *ᵥ w) := by
    funext i
    ext k
    have e1 := RingHom.map_mulVec f (g ^ (i : ℕ)) u k
    simp only [Function.comp_apply]
    change f ((g ^ (i : ℕ) *ᵥ u) k) = _
    rw [e1, Matrix.map_pow, hfu, Matrix.mulVec_smul]
  have hsK : f s ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors s.2
  have h3 : LinearIndependent K (fun i : Fin r => (f s) • (gK ^ (i : ℕ) *ᵥ w)) := by
    have := hw.units_smul (fun _ => Units.mk0 (f s) hsK)
    have e : (fun i : Fin r => (f s) • (gK ^ (i : ℕ) *ᵥ w)) =
        (fun _ : Fin r => Units.mk0 (f s) hsK) • (fun i : Fin r => gK ^ (i : ℕ) *ᵥ w) := by
      funext i
      simp [Units.smul_def]
    rw [e]
    exact this
  have h4 := (LinearIndependent.iff_fractionRing R K).mpr h3
  rw [← key] at h4
  exact h4.of_comp

theorem exists_smul_mem_span_of_linearIndependent {R M : Type} [CommRing R] [IsDomain R]
    [AddCommGroup M] [Module R M] {r : ℕ} (b : Module.Basis (Fin r) R M) (w : Fin r → M)
    (hw : LinearIndependent R w) :
    ∃ c : R, c ≠ 0 ∧ ∀ t : M, c • t ∈ Submodule.span R (Set.range w) := by
  classical
  let N : Matrix (Fin r) (Fin r) R := b.toMatrix w
  have hsum : ∀ z : Fin r → R, b.equivFun (∑ j, z j • w j) = N *ᵥ z := by
    intro z
    ext i
    simp [N, Module.Basis.toMatrix_apply, Matrix.mulVec, dotProduct, mul_comm]
  have hdet : N.det ≠ 0 := by
    intro h0
    obtain ⟨z, hz0, hz⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h0
    apply hz0
    have : ∑ j, z j • w j = 0 := b.equivFun.injective (by rw [hsum, hz, map_zero])
    funext j
    exact Fintype.linearIndependent_iff.1 hw z this j
  refine ⟨N.det, hdet, fun t => ?_⟩
  have : N.det • t = ∑ j, (N.adjugate *ᵥ b.equivFun t) j • w j := by
    apply b.equivFun.injective
    rw [hsum, map_smul, Matrix.mulVec_mulVec, Matrix.mul_adjugate, Matrix.smul_mulVec,
      Matrix.one_mulVec]
  rw [this]
  exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)

theorem exists_smul_mem_span_orbit : ∀ (l : ℕ) [Fact l.Prime] (T : Type) [AddCommGroup T] [Module ℤ_[l] T] [Module.Free ℤ_[l] T] [Module.Finite ℤ_[l] T] (O F : Type) [CommRing O] [Field F] [NumberField F] [Algebra O F] [IsFractionRing O F] (ρ : O →+* Module.End ℤ_[l] T), Module.finrank ℤ_[l] T = Module.finrank ℚ F → (∀ (n : ℕ) (a : Fin n → O), LinearIndependent ℚ (fun i => algebraMap O F (a i)) → LinearIndependent ℤ_[l] (fun i => ρ (a i))) → ∃ (v : T) (c : ℤ_[l]), c ≠ 0 ∧ ∀ t : T, c • t ∈ Submodule.span ℤ_[l] (Set.range fun a => ρ a v) := by
  intro l _ T _ _ _ _ O F _ _ _ _ _ ρ hrank hind
  obtain ⟨α, hα⟩ := GlobalTheory.exists_pow_linearIndependent_of_isFractionRing O F
  set n := Module.finrank ℚ F with hn
  let b : Module.Basis (Fin n) ℤ_[l] T := Module.finBasisOfFinrankEq ℤ_[l] T hrank
  set φ := ρ α with hφdef
  set g := LinearMap.toMatrix b b φ with hgdef
  have hpow : ∀ i : ℕ, LinearMap.toMatrix b b (φ ^ i) = g ^ i := fun i => by
    induction i with
    | zero => simp [LinearMap.toMatrix_one]
    | succ k ih => rw [pow_succ, LinearMap.toMatrix_mul, ih, pow_succ]
  have hφ : LinearIndependent ℤ_[l] (fun i : Fin n => φ ^ (i : ℕ)) := by
    have := hind n (fun i => α ^ (i : ℕ)) hα
    simpa [φ, map_pow] using this
  have hg : LinearIndependent ℤ_[l] (fun i : Fin n => g ^ (i : ℕ)) := by
    have := hφ.map' (LinearMap.toMatrix b b).toLinearMap (LinearMap.toMatrix b b).ker
    simpa [Function.comp_def, hpow] using this
  obtain ⟨u, hu⟩ := exists_linearIndependent_mulVec_pow g hg
  set v : T := b.equivFun.symm u with hv
  have hw : ∀ i : ℕ, b.equivFun ((φ ^ i) v) = g ^ i *ᵥ u := by
    intro i
    have hu' : u = ⇑(b.repr v) := by
      rw [hv, ← Module.Basis.equivFun_apply, LinearEquiv.apply_symm_apply]
    rw [← hpow, hu', LinearMap.toMatrix_mulVec_repr, Module.Basis.equivFun_apply]
  have hli : LinearIndependent ℤ_[l] (fun i : Fin n => (φ ^ (i : ℕ)) v) := by
    have hfun : (fun i : Fin n => (φ ^ (i : ℕ)) v) =
        b.equivFun.symm.toLinearMap ∘ (fun i : Fin n => g ^ (i : ℕ) *ᵥ u) := by
      funext i
      apply b.equivFun.injective
      simp only [Function.comp_apply, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply, hw]
    rw [hfun]
    exact hu.map' _ b.equivFun.symm.ker
  obtain ⟨c, hc, hct⟩ := exists_smul_mem_span_of_linearIndependent b _ hli
  refine ⟨v, c, hc, fun t => Submodule.span_mono ?_ (hct t)⟩
  rintro _ ⟨i, rfl⟩
  exact ⟨α ^ (i : ℕ), by simp [φ, map_pow]⟩

end GlobalTheory.CyclicLattice
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSphericalCuspFormWhittakerNeZeroStatement
section
open NumberField IsDedekindDomain GlobalTheory.CuspRep Formalism.UG GlobalTheory.LFun Matrix
open scoped ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_spherical_cuspForm_whittaker_ne_zero : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (m : ℕ) (S : Finset (HeightOneSpectrum (𝓞 E))), (∀ w ∉ S, ∀ x : w.adicCompletion E, (∀ y ∈ Ov E w, GlobalTheory.JSW.psiLoc w (x * y) = 1) ↔ x ∈ Ov E w) → ∀ (π : CuspSub E (m + 1)) (α : HeightOneSpectrum (𝓞 E) → Fin (m + 1) → ℂˣ), (∀ w ∉ S, HasSatGL w (π.locRep w) (Finset.univ.val.map (α w))) → ∃ φ ∈ π.V, (∀ w ∉ S, ∀ k ∈ KGL w (m + 1), act (.fin (locGL E (m + 1) w k)) φ = φ) ∧ ∃ x ∈ GlobalTheory.JSW.supS E (m + 1) S, GlobalTheory.JSW.whit φ.1 x ≠ 0 := by
  first | exact @GlobalTheory.JSW.NzSph.exists_sph_whit_ne_zero | exact GlobalTheory.JSW.NzSph.exists_sph_whit_ne_zero | (intros; apply GlobalTheory.JSW.NzSph.exists_sph_whit_ne_zero <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSymTranslate
section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CxPts GlobalTheory.VB

open MonoidalCategory CartesianMonoidalCategory MonObj Limits
open scoped CategoryTheory.Obj
open GlobalTheory.CechPic (Pic cls lam)
noncomputable section
namespace GlobalTheory.RiemannExists

theorem exists_sym_translate : ∀ (K : Type) [Field K] [IsAlgClosed K] (B : Over (Sp K)) [GrpObj B], IsAbelianScheme B → ∀ (L : LB B.left) (hL : L.IsLB), Out.RelAmple B L → Out.KTriv B L → ∃ (L' : LB B.left) (hL' : L'.IsLB), Out.Rigidified B L' ∧ Out.Sym B L' ∧ Out.RelAmple B L' ∧ Out.KTriv B L' ∧ lam (cls L' hL') (fst B B) (snd B B) = lam (cls L hL) (fst B B) (snd B B) := by
  intro K _ _ B _ hB L hL ha hk
  have := hB.comm
  obtain ⟨c, hc⟩ := exists_gen_theta_of_isAbelianScheme K B hB L hL
  have hΘ : ∃ t : LB.Gen (Theta B L), t.IsGen := ⟨c, hc⟩
  obtain ⟨O, hO, eO⟩ := CechPic.cls_surj (CechPic.pull (GrpObj.inv : B ⟶ B).left (cls L hL) - cls L hL)
  have hlam : lam (cls O hO) (fst B B) (snd B B) = 0 := by
    rw [eO, PrimitiveOverField.lam_sub, CechPic.lam_pull, ← Hom.inv_def, ← Hom.inv_def,
      FormPoly.lam_inv_left hL hΘ, FormPoly.lam_inv_right hL hΘ, neg_neg, sub_self]
  obtain ⟨b, hb⟩ := GlobalTheory.T.exists_point_picardClass_eq_translate_of_trivial_lambda K B hB L hL hk O hO hlam
  obtain ⟨a, hab⟩ := SS.SemiDivisible.pow_surj_abelian K B hB (n := 2) (by norm_num) b
  have hL' : (RigidTranslate.rigTransl L a).IsLB := DVR.linComb_isLB _ hL _ _
  refine ⟨_, hL', RigidTranslate.rigidified_rigTransl hL, GlobalTheory.T.symmetric_rigidTranslateLineBundle_of_square_defect K B L hL hΘ a (by rw [← eO, hb, hab]),
    GlobalTheory.T.relAmple_rigidTranslateLineBundle_rationalPoint K B hB L hL a ha, GlobalTheory.T.kernelTrivial_rigidTranslateLineBundle _ B L hL a hk, ?_⟩
  have e := (CechPic.cls_eq_iff (LB.isLB_linComb hL' _ _) (pull_isLB (LB.isLB_linComb hL _ _) _)).2
    (RigidTranslate.lam_rigTransl (t := a) hL c hc)
  rw [CechPic.cls_pull (LB.isLB_linComb hL _ _), CechPic.pull_id] at e
  exact (CechPic.cls_cube_two hL' _ _ _).symm.trans (e.trans (CechPic.cls_cube_two hL _ _ _))

theorem nonempty_riemannData : ∀ (S : Scheme.{0}) (P : PPAS S) (y : Sp ℂ ⟶ S), Nonempty (P.RiemannData y) := by
  intro S P y
  have h := isGrpPullback_pullback P.A y
  obtain ⟨L, hL, ha, hk, hc⟩ := P.isPol.2.2 ℂ y
  have hB : IsAbelianScheme ((Over.pullback y).obj P.A) := PolPull.isAbelianScheme_of_isGrpPullback P.isAb h
  obtain ⟨L', hL', hr, hs, ha', hk', hl⟩ := exists_sym_translate ℂ _ hB L hL ha hk
  let Q' : Out.PolAV (Sp ℂ) := ⟨(Over.pullback y).obj P.A, hB, P.g,
    (smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback h.1 P.smoothDim, L', hL', hr, hs, ha', hk'⟩
  obtain ⟨rig, hrg⟩ := Q'.rigid
  obtain ⟨u, H, χ, -, hH, -⟩ := thetaUnifAV_all Q' rig hrg
  exact ⟨⟨(Over.pullback y).obj P.A, _, h, L', hL', hc.trans hl.symm, u, H, χ, hH⟩⟩

end GlobalTheory.RiemannExists
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueHomExtensionAbelianDvr
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AbHomExtDvr

theorem existsUnique_hom_extension_abelian_dvr :
    ∀ (W L : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field L] [Algebra W L] [IsFractionRing W L] (G G' : Over (Sp W)) [GrpObj G] [GrpObj G'], IsAbelianScheme G → IsAbelianScheme G' → ∀ f : (Over.pullback (spMap (algebraMap W L))).obj G ⟶ (Over.pullback (spMap (algebraMap W L))).obj G', IsMonHom f → ∃! F : G ⟶ G', (Over.pullback (spMap (algebraMap W L))).map F = f := by
  intro W L _ _ _ _ _ _ G G' _ _ hG hG' f hf
  have hsm : GlobalTheory.SS.SmConn G := ⟨hG.comm, hG.smooth, by have := hG.proper; infer_instance,
    by have := hG.proper; infer_instance, hG.geomConnected⟩
  obtain ⟨F, ⟨-, hF⟩, -⟩ := GlobalTheory.existsUnique_hom_extension_smConn_semiAbelian_dvr W L G G' hsm
    (GlobalTheory.isSemiAbelian_of_isAbelianScheme G' hG') f hf
  have := hG.smooth
  have := hG'.proper
  have : Flat G.hom := inferInstance
  refine ⟨F, hF, fun F' hF' => ?_⟩
  exact GlobalTheory.KernelNoTorsion.eq_of_generic W L (hF'.trans hF.symm)

end GlobalTheory.AbHomExtDvr
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExplicitArithmeticHilbertSamuelBoundStatement
section
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.HermTools GlobalTheory.Vanishing GlobalTheory.Adelic GlobalTheory.HilbertSamuel GlobalTheory.ChowHt GlobalTheory.TangentOrigin
open GlobalTheory.IndefiniteRowSideFullHecke.RadicalPowers
open GlobalTheory.HSCore GlobalTheory.QCoh
open GlobalTheory
open GlobalTheory.HSShort GlobalTheory.HSChoice MvPolynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.explicit_arithmetic_hilbertSamuel_bound : Quoted → BertiniNF → HeightTie → SlopeBound → GeoBound := by
  first | exact @GlobalTheory.HSShortTop.geoBound_of_abstract | exact GlobalTheory.HSShortTop.geoBound_of_abstract | (intros; apply GlobalTheory.HSShortTop.geoBound_of_abstract <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExtTraceSubmatrixSumMap
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.HermFrame GlobalTheory.CurveDens GlobalTheory.Cartier
open scoped ComplexOrder

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.HermFrame.Renumber
open Matrix

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E]
variable {m l m' l' : Type} [Fintype m] [Fintype l] [Fintype m'] [Fintype l'] [DecidableEq m]
  [DecidableEq l] [DecidableEq m'] [DecidableEq l']

theorem mdbar_submatrix {a b a' b' : Type} (A : E → Matrix a b ℂ) (e : a' → a) (f : b' → b) (z η : E) :
    mdbar (fun x => (A x).submatrix e f) z η = (mdbar A z η).submatrix e f := by
  ext i j; simp [mdbar]

theorem subGram_submatrix (e : m' ≃ m) (f : l' ≃ l) (H : Matrix (m ⊕ l) (m ⊕ l) ℂ) :
    subGram (H.submatrix (Sum.map e f) (Sum.map e f)) = (subGram H).submatrix e e := by
  ext i j; simp [subGram, toBlocks₁₁]

theorem quotGram_submatrix (e : m' ≃ m) (f : l' ≃ l) (H : Matrix (m ⊕ l) (m ⊕ l) ℂ) :
    quotGram (H.submatrix (Sum.map e f) (Sum.map e f)) = (quotGram H).submatrix f f := by
  have h11 : (H.submatrix (Sum.map e f) (Sum.map e f)).toBlocks₁₁ = H.toBlocks₁₁.submatrix e e := by
    ext i j; simp [toBlocks₁₁]
  have h12 : (H.submatrix (Sum.map e f) (Sum.map e f)).toBlocks₁₂ = H.toBlocks₁₂.submatrix e f := by
    ext i j; simp [toBlocks₁₂]
  have h21 : (H.submatrix (Sum.map e f) (Sum.map e f)).toBlocks₂₁ = H.toBlocks₂₁.submatrix f e := by
    ext i j; simp [toBlocks₂₁]
  have h22 : (H.submatrix (Sum.map e f) (Sum.map e f)).toBlocks₂₂ = H.toBlocks₂₂.submatrix f f := by
    ext i j; simp [toBlocks₂₂]
  rw [quotGram, quotGram, h11, h12, h21, h22, inv_submatrix_equiv, submatrix_mul_equiv,
    submatrix_mul_equiv]; rfl

theorem orthCoeff_submatrix (e : m' ≃ m) (f : l' ≃ l) (H : Matrix (m ⊕ l) (m ⊕ l) ℂ) :
    orthCoeff (H.submatrix (Sum.map e f) (Sum.map e f)) = (orthCoeff H).submatrix e f := by
  have h11 : (H.submatrix (Sum.map e f) (Sum.map e f)).toBlocks₁₁ = H.toBlocks₁₁.submatrix e e := by
    ext i j; simp [toBlocks₁₁]
  have h21 : (H.submatrix (Sum.map e f) (Sum.map e f)).toBlocks₂₁ = H.toBlocks₂₁.submatrix f e := by
    ext i j; simp [toBlocks₂₁]
  rw [orthCoeff, orthCoeff, h11, h21, transpose_submatrix, transpose_submatrix, inv_submatrix_equiv,
    submatrix_mul_equiv]

theorem adj_submatrix {a b a' b' : Type} [Fintype a] [Fintype b] [Fintype a'] [Fintype b']
    [DecidableEq a] [DecidableEq a'] (e : a' ≃ a) (f : b' ≃ b)
    (H : Matrix a a ℂ) (K : Matrix b b ℂ) (T : Matrix b a ℂ) :
    adj (H.submatrix e e) (K.submatrix f f) (T.submatrix f e) = (adj H K T).submatrix e f := by
  rw [adj, adj, transpose_submatrix, transpose_submatrix, conjTranspose_submatrix,
    inv_submatrix_equiv, submatrix_mul_equiv, submatrix_mul_equiv]

theorem extForm_submatrix (e : m' ≃ m) (f : l' ≃ l) (K : E → Matrix (m ⊕ l) (m ⊕ l) ℂ) (z η : E) :
    extForm (fun x => (K x).submatrix (Sum.map e f) (Sum.map e f)) z η =
      (extForm K z η).submatrix e f := by
  rw [extForm_eq_neg_mdbar, extForm_eq_neg_mdbar]
  simp_rw [orthCoeff_submatrix]
  rw [mdbar_submatrix]; rfl

theorem extFormAdj_submatrix (e : m' ≃ m) (f : l' ≃ l) (K : E → Matrix (m ⊕ l) (m ⊕ l) ℂ) (z ξ : E) :
    extFormAdj (fun x => (K x).submatrix (Sum.map e f) (Sum.map e f)) z ξ =
      (extFormAdj K z ξ).submatrix f e := by
  rw [extFormAdj, extFormAdj, extForm_submatrix, quotGram_submatrix, subGram_submatrix, adj_submatrix]

end GlobalTheory.HermFrame.Renumber

open Matrix in

theorem GlobalTheory.HermFrame.extTrace_submatrix_sumMap : ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E] (m l m' l' : Type) [Fintype m] [Fintype l] [Fintype m'] [Fintype l'] [DecidableEq m] [DecidableEq l] [DecidableEq m'] [DecidableEq l'] (e : m' ≃ m) (f : l' ≃ l) (K : E → Matrix (m ⊕ l) (m ⊕ l) ℂ) (z : E), extTrace (fun x => (K x).submatrix (Sum.map e f) (Sum.map e f)) z = extTrace K z := by
  intro E _ _ _ _ m l m' l' _ _ _ _ _ _ _ _ e f K z
  funext ξ η
  rw [extTrace, extTrace, Renumber.extFormAdj_submatrix, Renumber.extForm_submatrix,
    submatrix_mul_equiv]
  congr 1
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.submatrix_apply]
  exact Equiv.sum_comp f (fun i => (extFormAdj K z ξ * extForm K z η) i i)
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteAffineNeighbourhoodExistsStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CxPts GlobalTheory.VB
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_affine_neighbourhood_exists : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k) [IsIntegral X] (Y : Scheme.{0}) [IsIntegral Y] (q : Y ⟶ Sp k), IsArithVar p 1 → IsArithVar q 1 → ∀ (π : Y ⟶ X), π ≫ p = q → π (genericPoint Y) = genericPoint X → π.residueDegree (genericPoint Y) ≠ 0 → ∀ U₀ : X.Opens, genericPoint X ∈ U₀ → ∃ U : X.Opens, U ≤ U₀ ∧ IsAffineOpen U ∧ genericPoint X ∈ U ∧ IsAffineOpen (π ⁻¹ᵁ U) ∧ (π.app U).hom.Finite ∧ (π.app U).hom.Etale ∧ (letI := (π.app U).hom.toAlgebra; Module.finrank Γ(X, U) Γ(Y, π ⁻¹ᵁ U)) = π.residueDegree (genericPoint Y) := by
  first | exact @GlobalTheory.GenFiniteEtale.exists_finite_etale | exact GlobalTheory.GenFiniteEtale.exists_finite_etale | (intros; apply GlobalTheory.GenFiniteEtale.exists_finite_etale <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GelfandGeneratorMemQuantumDetStatement
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.DescB GlobalTheory.ThK.FlagCT GlobalTheory.ThK.FlagPar
open GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.LeviHC

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gelfand_generator_mem_quantum_det : ∀ (A : Type) [Ring A] [Algebra ℂ A] (n : ℕ) (X : Fin n → Fin n → A), Formalism.REAL.GlRel X →
    ∀ k : ℕ, GlobalTheory.SmoothForms.gelfA X k ∈ Algebra.adjoin ℂ (Set.range (Formalism.REAL.qdet X)) := by
  first | exact @GlobalTheory.CapelliGelfand.gelfA_mem_adjoin_qdet | exact GlobalTheory.CapelliGelfand.gelfA_mem_adjoin_qdet | (intros; apply GlobalTheory.CapelliGelfand.gelfA_mem_adjoin_qdet <;> assumption)
end

