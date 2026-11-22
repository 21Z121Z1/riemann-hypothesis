import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Clauses
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.AlWellDefSt
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.MemRangeCompIffOfIsClosedImmersion
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.Bundle0017
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.Bundle0013
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.Bundle0005
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.Bundle0014
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.Bundle0007
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.ExistsMvPolynomialOfPolyBoundOffHypersurface
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.Bundle0008
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0006
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.KodairaSpencerClassCohomologousAlongEndomorphism
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle0001
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0085

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsUniqueTorsionPointFrobeniusLocal
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Pdiv GlobalTheory.AbLaw
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory.TorsionTheta

theorem ptMap_comp_ptMap {O : Type} [CommRing O] {A B C : Type} [CommRing A] [Algebra O A]
    [CommRing B] [Algebra O B] [CommRing C] [Algebra O C] (φ : A →ₐ[O] B) (ψ : B →ₐ[O] C) :
    ptMap ψ ≫ ptMap φ = ptMap (ψ.comp φ) := by
  unfold ptMap
  ext1
  simp only [Over.comp_left, Over.homMk_left]
  rw [← Spec.map_comp]
  rfl

theorem tmul_one_ne_zero {O : Type} [CommRing O] [IsLocalRing O] {H : Type} [CommRing H]
    [Algebra O H] [Module.Finite O H] [Module.Free O H] (l : H)
    (hl : l ∉ (IsLocalRing.maximalIdeal O).map (algebraMap O H))
    (K : Type) [Field K] [Algebra O K] : l ⊗ₜ[O] (1 : K) ≠ 0 := by
  classical
  intro h0
  let b := Module.Free.chooseBasis O H
  have hex : ∃ i, IsUnit (b.repr l i) := by
    by_contra hne
    push Not at hne
    apply hl
    rw [← b.sum_repr l]
    refine Ideal.sum_mem _ (fun i _ => ?_)
    rw [Algebra.smul_def]
    exact Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ ((IsLocalRing.mem_maximalIdeal _).2 (hne i)))
  obtain ⟨i, hi⟩ := hex
  have h1 := congrArg (fun x => TensorProduct.lid O K (TensorProduct.map (b.coord i) LinearMap.id x)) h0
  simp only [TensorProduct.map_tmul, TensorProduct.lid_tmul, LinearMap.id_apply, map_zero,
    Module.Basis.coord_apply] at h1
  rw [Algebra.smul_def, _root_.mul_one] at h1
  exact (hi.map (algebraMap O K)).ne_zero h1

private lemma ptMap_comp_comp {O : Type} [CommRing O] {A B C : Type} [CommRing A] [Algebra O A]
    [CommRing B] [Algebra O B] [CommRing C] [Algebra O C] {X : Over (Sp O)} (φ : A →ₐ[O] B)
    (ψ : B →ₐ[O] C) (f : specO O A ⟶ X) : ptMap (ψ.comp φ) ≫ f = ptMap ψ ≫ ptMap φ ≫ f := by
  rw [← ptMap_comp_ptMap, Category.assoc]

theorem exists_theta : ∀ (O : Type) [CommRing O] [IsLocalRing O] (G : Over (Sp O)) [GrpObj G] [IsCommMonObj G] (n : ℕ) (H : Type) [CommRing H] [Algebra O H] [Module.Finite O H] [Module.Free O H] (y : specO O H ⟶ G), y ^ n = 1 → (∀ (S : Type) [CommRing S] [Algebra O S] (z : specO O S ⟶ G), z ^ n = 1 → ∃! φ : H →ₐ[O] S, ptMap φ ≫ y = z) → ∀ (ε : H →ₐ[O] O) (l : H) (c : O), ptMap ε ≫ y = 1 → (∀ h, ε h = 0 → h * l = 0) → ε l = c → l ∉ (IsLocalRing.maximalIdeal O).map (algebraMap O H) → ∃ Θ : H ⊗[O] H, (∀ h : H, (h ⊗ₜ[O] (1 : H)) * Θ = ((1 : H) ⊗ₜ[O] h) * Θ) ∧ Algebra.TensorProduct.lmul' O Θ = algebraMap O H c ∧ ∀ (K : Type) [Field K] [IsAlgClosed K] [Algebra O K], (∀ a ∈ IsLocalRing.maximalIdeal O, algebraMap O K a = 0) → ∀ ga : H →ₐ[O] K, Algebra.TensorProduct.map (AlgHom.id O H) ga Θ ≠ 0 := by
  intro O _ _ G _ _ n H _ _ _ _ y hy hU ε l c hε hann hεl hlm
  have tors : ∀ (S : Type) [CommRing S] [Algebra O S] (f : specO O S ⟶ specO O H), (f ≫ y) ^ n = 1 := by
    intro S _ _ f
    rw [← comp_pow, hy, comp_one]
  have uniq : ∀ (S : Type) [CommRing S] [Algebra O S] (φ₁ φ₂ : H →ₐ[O] S),
      ptMap φ₁ ≫ y = ptMap φ₂ ≫ y → φ₁ = φ₂ := by
    intro S _ _ φ₁ φ₂ h
    obtain ⟨φ, -, hφ⟩ := hU S (ptMap φ₂ ≫ y) (tors S _)
    exact (hφ φ₁ h).trans (hφ φ₂ rfl).symm
  let iL : H →ₐ[O] H ⊗[O] H := Algebra.TensorProduct.includeLeft
  let iR : H →ₐ[O] H ⊗[O] H := Algebra.TensorProduct.includeRight
  obtain ⟨d, hd, -⟩ := hU (H ⊗[O] H) (ptMap iL ≫ y * (ptMap iR ≫ y)⁻¹)
    (by rw [mul_pow, inv_pow, tors, tors, inv_one, _root_.mul_one])
  obtain ⟨m, hm, -⟩ := hU (H ⊗[O] H) (ptMap iL ≫ y * ptMap iR ≫ y)
    (by rw [mul_pow, tors, tors, _root_.mul_one])
  let eH : H →ₐ[O] H := (Algebra.ofId O H).comp ε
  have heH : ptMap eH ≫ y = 1 := by
    rw [ptMap_comp_comp, hε, comp_one]

  have hmd : (Algebra.TensorProduct.lmul' O : H ⊗[O] H →ₐ[O] H).comp d = eH := by
    apply uniq
    rw [ptMap_comp_comp, hd, comp_mul, GrpObj.comp_inv, ← ptMap_comp_comp, ← ptMap_comp_comp, heH]
    have h1 : (Algebra.TensorProduct.lmul' O : H ⊗[O] H →ₐ[O] H).comp iL = AlgHom.id O H := by
      ext x; simp [iL]
    have h2 : (Algebra.TensorProduct.lmul' O : H ⊗[O] H →ₐ[O] H).comp iR = AlgHom.id O H := by
      ext x; simp [iR]
    rw [h1, h2, mul_inv_cancel]
  refine ⟨d l, ?_, ?_, ?_⟩
  ·
    have hl' : ∀ a : H, a * l = algebraMap O H (ε a) * l := by
      intro a
      have := hann (a - algebraMap O H (ε a)) (by simp)
      rwa [sub_mul, sub_eq_zero] at this
    let e2 : H ⊗[O] H →ₐ[O] H := Algebra.TensorProduct.lift eH (AlgHom.id O H) (fun _ _ => Commute.all _ _)
    have hkey : ∀ x : H ⊗[O] H, x * (l ⊗ₜ[O] (1 : H)) = (l ⊗ₜ[O] (1 : H)) * ((1 : H) ⊗ₜ[O] e2 x) := by
      intro x
      induction x using TensorProduct.induction_on with
      | zero => simp
      | tmul a b =>
        simp only [e2, eH, Algebra.TensorProduct.lift_tmul, Algebra.TensorProduct.tmul_mul_tmul, _root_.mul_one,
          _root_.one_mul, hl' a, AlgHom.comp_apply, Algebra.ofId_apply, AlgHom.id_apply]
        rw [← Algebra.smul_def, ← Algebra.smul_def, TensorProduct.smul_tmul]
      | add x x' hx hx' => rw [add_mul, hx, hx', map_add, TensorProduct.tmul_add, mul_add]
    let ψ : H ⊗[O] H →ₐ[O] H ⊗[O] H := Algebra.TensorProduct.lift d iR (fun _ _ => Commute.all _ _)
    have hψL : ψ.comp iL = d := by ext x; simp [ψ, iL]
    have hψR : ψ.comp iR = iR := by ext x; simp [ψ, iR]
    have he2L : e2.comp iL = eH := by ext x; simp [e2, iL]
    have he2R : e2.comp iR = AlgHom.id O H := by ext x; simp [e2, iR]
    have he2m : e2.comp m = AlgHom.id O H := by
      apply uniq
      rw [ptMap_comp_comp, hm, comp_mul, ← ptMap_comp_comp, ← ptMap_comp_comp, he2L, he2R, heH, _root_.one_mul]
    have hψm : ψ.comp m = iL := by
      apply uniq
      rw [ptMap_comp_comp, hm, comp_mul, ← ptMap_comp_comp, ← ptMap_comp_comp, hψL, hψR, hd,
        inv_mul_cancel_right]
    intro h
    have a1 : h ⊗ₜ[O] (1 : H) = ψ (m h) := by
      rw [← AlgHom.comp_apply, hψm]; rfl
    have a2 : d l = ψ (l ⊗ₜ[O] (1 : H)) := by simp [ψ]
    have a3 : (1 : H) ⊗ₜ[O] h = ψ ((1 : H) ⊗ₜ[O] h) := by simp [ψ, iR]
    have a4 : e2 (m h) = h := by rw [← AlgHom.comp_apply, he2m]; rfl
    rw [a1, a2, ← map_mul, hkey, a4, map_mul, ← a3, ← a2, _root_.mul_comm]
  · have := DFunLike.congr_fun hmd l
    rw [AlgHom.comp_apply] at this
    rw [this]
    simp [eH, hεl]
  · intro K _ _ _ _ ga
    let jL : H →ₐ[O] H ⊗[O] K := Algebra.TensorProduct.includeLeft
    let jR : K →ₐ[O] H ⊗[O] K := Algebra.TensorProduct.includeRight
    let κ : H ⊗[O] H →ₐ[O] H ⊗[O] K := Algebra.TensorProduct.map (AlgHom.id O H) ga
    let Sg : H →ₐ[O] H ⊗[O] K := κ.comp m
    let MainNotions : H ⊗[O] K →ₐ[O] H ⊗[O] K := Algebra.TensorProduct.lift Sg jR (fun _ _ => Commute.all _ _)
    have hκL : κ.comp iL = jL := by ext x; simp [κ, iL, jL]
    have hκR : κ.comp iR = jR.comp ga := by ext x; simp [κ, iR, jR]
    have hSL : (MainNotions.comp κ).comp iL = Sg := by ext x; simp [MainNotions, κ, iL]
    have hSR : (MainNotions.comp κ).comp iR = jR.comp ga := by ext x; simp [MainNotions, κ, iR, jR]
    have hSg : ptMap Sg ≫ y = ptMap jL ≫ y * ptMap (jR.comp ga) ≫ y := by
      rw [ptMap_comp_comp, hm, comp_mul, ← ptMap_comp_comp, ← ptMap_comp_comp, hκL, hκR]
    have hback : (MainNotions.comp κ).comp d = jL := by
      apply uniq
      rw [ptMap_comp_comp, hd, comp_mul, GrpObj.comp_inv, ← ptMap_comp_comp, ← ptMap_comp_comp, hSL, hSR, hSg,
        mul_inv_cancel_right]
    intro h0
    apply tmul_one_ne_zero l hlm K
    have := DFunLike.congr_fun hback l
    simp only [AlgHom.comp_apply] at this
    change MainNotions (κ (d l)) = l ⊗ₜ[O] (1 : K) at this
    rw [← this]
    change MainNotions (Algebra.TensorProduct.map (AlgHom.id O H) ga (d l)) = 0
    rw [h0, map_zero]

end GlobalTheory.TorsionTheta
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.FiniteImageOfLocallyConstantOnHolomorphicFamilie
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open Topology Filter

namespace GlobalTheory.FiniteClasses

open GlobalTheory.Points

theorem preconnectedSpace_pts (A : Type) [CommRing A] [IsDomain A] [Algebra ℂ A]
    [Algebra.FiniteType ℂ A] : PreconnectedSpace (Pts (spMap (algebraMap ℂ A))) := by
  have hc := isConnected_basicOpen_complexPoints_of_dense
    (exists_isConnected_principalOpen noetherNormalization_primitive
      (isConnected_unramified_cover_of_irreducible isConnected_and_dense_compl_hypersurface
        exists_mvPolynomial_of_poly_bound_off_hypersurface))
    (principalOpen_dense_complexPoints noetherNormalization_primitive
      isConnected_and_dense_compl_hypersurface) A 1 one_ne_zero
  have he := isEmbedding_ptsOverEquivAlgHom (C := ℂ) A (id_eq_spMap_algebraMap ℂ)
  refine ⟨he.isInducing.isPreconnected_image.1 ?_⟩
  convert hc.isPreconnected using 1
  ext x
  constructor
  · rintro ⟨y, -, rfl⟩
    exact ⟨_, rfl, by simp⟩
  · rintro ⟨φ, rfl, -⟩
    exact ⟨(ptsOverEquivAlgHom A (id_eq_spMap_algebraMap ℂ)).symm φ, trivial, by simp⟩

theorem finite_range_affine (A : Type) [CommRing A] [Algebra ℂ A] [Algebra.FiniteType ℂ A] {I : Type*}
    (c : Pts (spMap (algebraMap ℂ A)) → I) (hc : IsLocallyConstant c) : (Set.range c).Finite := by
  have : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing ℂ A
  have hcomp : ∀ P : Ideal A, spMap (Ideal.Quotient.mk P) ≫ spMap (algebraMap ℂ A) =
      spMap (algebraMap ℂ (A ⧸ P)) := fun P => by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  have hfin : (⋃ P ∈ minimalPrimes A,
      Set.range (c ∘ PtsOver.map (spMap (Ideal.Quotient.mk P)) (hcomp P) (𝟙 _))).Finite := by
    refine (minimalPrimes.finite_of_isNoetherianRing A).biUnion fun P hP => ?_
    have : P.IsPrime := hP.1.1
    have := preconnectedSpace_pts (A ⧸ P)
    exact Set.Subsingleton.finite (by
      rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
      exact (hc.comp_continuous (PtsOver.continuous_map _ _ _)).apply_eq_of_preconnectedSpace a b)
  refine hfin.subset ?_
  rintro _ ⟨x, rfl⟩
  obtain ⟨φ, rfl⟩ := (ptsEquivAlgHom A).symm.surjective x
  have : (RingHom.ker φ.toRingHom).IsPrime := RingHom.ker_isPrime _
  obtain ⟨P, hP, hle⟩ := Ideal.exists_minimalPrimes_le (I := (⊥ : Ideal A))
    (J := RingHom.ker φ.toRingHom) bot_le
  refine Set.mem_biUnion (x := P) hP ⟨(ptsEquivAlgHom (A ⧸ P)).symm
    (Ideal.Quotient.liftₐ P φ fun a ha => hle ha), congrArg c (Subtype.ext ?_)⟩
  simp only [PtsOver.map_val, ptsOverEquivAlgHom_symm_val]
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  rfl

theorem finite_range {Y : Scheme.{0}} (p : Y ⟶ Sp ℂ) [LocallyOfFiniteType p] [QuasiCompact p] {I : Type*}
    (c : Pts p → I) (hc : IsLocallyConstant c) : (Set.range c).Finite := by
  have : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace p
  let 𝒰 := Y.affineOpenCover
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover (X := Y)
    (fun i => ((𝒰.f i).opensRange : Set Y)) (fun i => (𝒰.f i).opensRange.isOpen)
    (fun y _ => Set.mem_iUnion.2 ⟨𝒰.idx y, 𝒰.covers y⟩)
  have key : ∀ {R : CommRingCat.{0}} (j : Spec R ⟶ Y) [IsOpenImmersion j],
      (Set.range (c ∘ PtsOver.map j rfl (𝟙 _))).Finite := by
    intro R j _
    have hl : IsLocallyConstant (c ∘ PtsOver.map j rfl (𝟙 _)) :=
      hc.comp_continuous (PtsOver.continuous_map _ _ _)
    have hft : LocallyOfFiniteType (j ≫ p) := inferInstance
    generalize c ∘ PtsOver.map j rfl (𝟙 _) = c' at hl
    generalize j ≫ p = q at c' hl hft
    obtain ⟨φ, rfl⟩ := Spec.map_surjective q
    let _ := φ.hom.toAlgebra
    have : Algebra.FiniteType ℂ R := (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).1 hft
    exact finite_range_affine R c' hl
  refine (t.finite_toSet.biUnion fun i _ => key (𝒰.f i)).subset ?_
  rintro _ ⟨x, rfl⟩
  obtain ⟨i, hi, hx⟩ := Set.mem_iUnion₂.1 (ht (Set.mem_univ (x.1 (IsLocalRing.closedPoint ℂ))))
  have hx' : x ∈ Set.range (PtsOver.map (𝒰.f i) rfl (𝟙 _)) := by
    rw [PtsOver.range_map, range_comp_of_isOpenImmersion]
    exact (le_preimage_iff x.1 _).2 hx
  obtain ⟨z, rfl⟩ := hx'
  exact Set.mem_biUnion hi ⟨z, rfl⟩

theorem isLocallyConstant_of_hol {Y : Scheme.{0}} (p : Y ⟶ Sp ℂ) (d : ℕ)
    (hp : SmoothOfRelativeDimension d p) {I : Type*} (c : Pts p → I)
    (H : ∀ (B : Set (Fin d → ℂ)) (y : (Fin d → ℂ) → Pts p), IsOpen B → IsHolTo B (fun b => (y b).1) →
      ∀ b₀ ∈ B, ∀ᶠ b in 𝓝 b₀, c (y b) = c (y b₀)) : IsLocallyConstant c := by
  rw [IsLocallyConstant.iff_eventually_eq]
  intro x
  let h := overHomeomorph (C := ℂ) (Over.mk p)
  obtain ⟨W, σ, U, t, hW, h0, hσ, -, hhol, hco, hop, -⟩ := HolChart.exists_holomorphic_chart valAt'_rules
    existsUnique_point_of_ringHom exists_holomorphic_section_of_etale (Over.mk p) d hp (h.symm x)
  have hop' : IsOpen (σ '' W) := by
    refine TopologicalSpace.le_def.1 (le_generateFrom ?_) _ hop
    rintro _ ⟨V, f, O, hO, rfl⟩
    exact (isOpen_basicSet (C := ℂ) V f hO).preimage (isEmbedding_left (Over.mk p)).continuous
  have hx : h (σ 0) = x := by rw [hσ, Homeomorph.apply_symm_apply]
  have hev := H W (fun b => h (σ b)) hW hhol 0 h0
  have hxU : ⊤ ≤ x.1 ⁻¹ᵁ U := by rw [← hx]; exact (hco 0 h0).1
  have hT : Tendsto (fun (z : Pts p) (i : Fin d) => valR z.1 U (t i)) (𝓝 x) (𝓝 0) := by
    refine tendsto_pi_nhds.2 fun i => ?_
    have h1 := ((continuousAt_valR (t i) hxU).comp continuous_subtype_val.continuousAt).tendsto
    have h2 : valR x.1 U (t i) = (0 : Fin d → ℂ) i := by rw [← hx]; exact (hco 0 h0).2 i
    rw [← h2]
    exact h1
  have hN : h '' (σ '' W) ∈ 𝓝 x := (h.isOpenMap _ hop').mem_nhds ⟨_, ⟨0, h0, rfl⟩, hx⟩
  filter_upwards [hN, hT.eventually hev] with z hz hz'
  obtain ⟨_, ⟨w, hw, rfl⟩, rfl⟩ := hz
  have : (fun i => valR (h (σ w)).1 U (t i)) = w := funext (hco w hw).2
  rw [this, hx] at hz'
  exact hz'

theorem finite_image_of_locally_constant_on_holomorphic_families :
    (∀ (k : Type) [Field k] (σ : k →+* ℂ) (X : Scheme.{0}) (s : X ⟶ Sp k) (d : ℕ) (y₀ : Sp ℂ ⟶ X), SmoothOfRelativeDimension d s → y₀ ≫ s = spMap σ → ∃ (B : Set (Fin d → ℂ)) (y : (Fin d → ℂ) → (Sp ℂ ⟶ X)) (U : X.Opens) (f : Fin d → Γ(X, U)) (n : ℕ) (r : Fin n → Γ(X, U)), IsOpen B ∧ (0 : Fin d → ℂ) ∈ B ∧ y 0 = y₀ ∧ (∀ b ∈ B, y b ≫ s = spMap σ) ∧ IsHolTo B y ∧ Set.InjOn y B ∧ ⊤ ≤ y₀ ⁻¹ᵁ U ∧ ∃ ε : ℝ, 0 < ε ∧ ∀ x : Sp ℂ ⟶ X, x ≫ s = spMap σ → ⊤ ≤ x ⁻¹ᵁ U → (∀ i, ‖valAt' x U (r i) - valAt' y₀ U (r i)‖ < ε) → x ∈ y '' B) → ∀ (k : Type) [Field k] (σ : k →+* ℂ) (X : Scheme.{0}) (s : X ⟶ Sp k) (d : ℕ) (I : Type 1) (cls : (Sp ℂ ⟶ X) → I), SmoothOfRelativeDimension d s → QuasiCompact s → (∀ (B : Set (Fin d → ℂ)) (y : (Fin d → ℂ) → (Sp ℂ ⟶ X)), IsOpen B → (∀ b ∈ B, y b ≫ s = spMap σ) → IsHolTo B y → ∀ b₀ ∈ B, ∀ᶠ b in nhds b₀, cls (y b) = cls (y b₀)) → (cls '' {x | x ≫ s = spMap σ}).Finite := by
  intro _ k _ σ X s d I cls hs hq H
  let p := pullback.snd s (spMap σ)
  let q := pullback.fst s (spMap σ)
  have hp : SmoothOfRelativeDimension d p :=
    (smoothOfRelativeDimension_isStableUnderBaseChange d).of_isPullback
      (IsPullback.of_hasPullback s (spMap σ)) hs
  have : Smooth p := SmoothOfRelativeDimension.smooth d p
  have hover : ∀ z : Pts p, (z.1 ≫ q) ≫ s = spMap σ := fun z => by
    rw [Category.assoc, pullback.condition, ← Category.assoc, z.2, Category.id_comp]
  have hl : IsLocallyConstant fun z : Pts p => cls (z.1 ≫ q) := by
    refine isLocallyConstant_of_hol p d hp _ fun B y hB hy => ?_
    refine H B (fun b => (y b).1 ≫ q) hB (fun b _ => hover _) fun U f => ?_
    simp only [valAt'_eq_valR, valR_comp]
    exact hy (q ⁻¹ᵁ U) ((q.app U).hom f)
  refine (finite_range p _ hl).subset ?_
  rintro _ ⟨x, hx, rfl⟩
  refine ⟨⟨pullback.lift x (𝟙 _) (by rw [Category.id_comp]; exact hx), pullback.lift_snd _ _ _⟩, ?_⟩
  exact congrArg cls (pullback.lift_fst _ _ _)

end GlobalTheory.FiniteClasses
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.FlatOfIsFiniteOfFinitePresentationOfFlatGeometri
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Pdiv GlobalTheory.AbLaw
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory

namespace FinitePresFibreFlat

open TensorProduct IsLocalRing FiniteFibreFlat

section Algebra

theorem free_of_flat_reduction {R A M : Type*} [CommRing R] [CommRing A] [Algebra R A]
    [IsLocalRing A]
    [AddCommGroup M] [Module R M] [Module A M] [IsScalarTower R A M] [Module.Flat R M]
    [Module.FinitePresentation A M] (p : Ideal R) (hp : p.map (algebraMap R A) ≤ maximalIdeal A)
    [Module.Flat (A ⧸ p.map (algebraMap R A)) ((A ⧸ p.map (algebraMap R A)) ⊗[A] M)] :
    Module.Free A M := by
  set I := p.map (algebraMap R A) with hI
  have hrel : LocalFlat.RelationsLift I M :=
    LocalFlat.relationsLift_of_flat (C := A ⧸ I) Ideal.Quotient.mk_surjective Ideal.mk_ker
      (TensorProduct.mk A (A ⧸ I) M 1) (TensorProduct.mk_surjective A M (A ⧸ I)
        Ideal.Quotient.mk_surjective) (LinearMap.ker_tensorProductMk M)
  apply Module.free_of_maximalIdeal_rTensor_injective
  rw [← LinearMap.lTensor_inj_iff_rTensor_inj, injective_iff_map_eq_zero]
  intro x hx
  obtain ⟨y, rfl⟩ := hrel (maximalIdeal A) (maximalIdeal A).subtype x (by rw [hx]; simp)
  let e := Submodule.comapSubtypeEquivOfLe hp
  have hy : I.subtype.lTensor M (e.toLinearMap.lTensor M y) = 0 := by
    rw [← hx, ← LinearMap.lTensor_comp_apply, ← LinearMap.lTensor_comp_apply]
    rfl
  rw [map_eq_zero_iff _ (lTensor_map_injective p)] at hy
  have : y = 0 := (LinearEquiv.lTensor M e).injective (hy.trans (map_zero _).symm)
  rw [this, map_zero]

theorem flat_of_flat_fibres {R A B : Type} [CommRing R] [CommRing A] [CommRing B] [Algebra R A]
    [Algebra R B] [Algebra A B] [IsScalarTower R A B] [Module.FinitePresentation A B]
    [Module.Flat R B]
    (H : ∀ (k C : Type) [Field k] [CommRing C] [Algebra A C] (t : R →+* k) (h : k →+* C),
      (algebraMap A C).comp (algebraMap R A) = h.comp t → Module.Flat C (C ⊗[A] B)) :
    Module.Flat A B := by
  refine Module.flat_of_isLocalized_maximal A B (fun P _ => Localization.AtPrime P ⊗[A] B)
    (fun P _ => TensorProduct.mk A (Localization.AtPrime P) B 1) fun P _ => ?_
  let A' := Localization.AtPrime P
  let p : Ideal R := (maximalIdeal A').comap (algebraMap R A')
  let I := p.map (algebraMap R A')
  have h1 : Module.Flat R (B ⊗[A] A') := Module.Flat.trans R B (B ⊗[A] A')
  have h2 : Module.Flat R (A' ⊗[A] B) :=
    Module.Flat.of_linearEquiv
      ((Algebra.TensorProduct.comm A A' B).restrictScalars R).toLinearEquiv
  have h3 : Module.Flat (A' ⧸ I) ((A' ⧸ I) ⊗[A] B) := by
    let ψ : R →+* A' ⧸ I := (Ideal.Quotient.mk I).comp (algebraMap R A')
    have hψ₁ : p ≤ RingHom.ker ψ := fun r hr =>
      Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_map_of_mem _ hr)
    have hψ₂ : p.primeCompl ≤ (IsUnit.submonoid (A' ⧸ I)).comap ψ := by
      intro r hr
      have : IsUnit (algebraMap R A' r) := by
        by_contra h
        exact hr h
      exact this.map (Ideal.Quotient.mk I)
    refine H p.ResidueField (A' ⧸ I) (algebraMap R _) (Ideal.ResidueField.lift p ψ hψ₁ hψ₂) ?_
    ext r
    exact (Ideal.ResidueField.lift_algebraMap p ψ hψ₁ hψ₂ r).symm
  have h4 : Module.Flat (A' ⧸ I) ((A' ⧸ I) ⊗[A'] (A' ⊗[A] B)) :=
    Module.Flat.of_linearEquiv
      (AlgebraTensorModule.cancelBaseChange A A' (A' ⧸ I) (A' ⧸ I) B)
  have h5 : Module.Free A' (A' ⊗[A] B) :=
    free_of_flat_reduction p Ideal.map_comap_le
  have h6 : Module.Flat A' (A' ⊗[A] B) := Module.Flat.of_free
  exact Module.Flat.trans A A' (A' ⊗[A] B)

end Algebra

open FibreFlat

set_option backward.isDefEq.respectTransparency false in
theorem flat_of_flatOver_fields {X Y S : Scheme.{0}} (f : X ⟶ Y) (g : Y ⟶ S)
    (hY : LocallyOfFinitePresentation g) (h0 : LocallyOfFinitePresentation (f ≫ g))
    (h1 : Flat (f ≫ g)) (h2 : IsFinite f)
    (H : ∀ (k : Type) [Field k] (t : Spec (CommRingCat.of k) ⟶ S), FlatOver f g t) :
    Flat f := by
  wlog hS : ∃ R, S = Spec R generalizing X Y S
  · refine IsZariskiLocalAtTarget.of_openCover (S.affineCover.pullback₁ g) fun i => ?_
    let u := S.affineCover.f i
    have sq := IsPullback.of_hasPullback f (pullback.fst g u)
    have sq' := IsPullback.of_hasPullback g u
    refine this (pullback.snd f (pullback.fst g u)) (pullback.snd g u)
      inferInstance (MorphismProperty.of_isPullback (sq.paste_vert sq') h0)
      (MorphismProperty.of_isPullback (sq.paste_vert sq') h1) inferInstance
      (fun k _ t => flatOver_of_comp_base (u := u) ?_) ⟨_, rfl⟩
    rw [← pullback.condition]
    exact (H k _).target sq
  obtain ⟨R, rfl⟩ := hS
  wlog hA : ∃ A, Y = Spec A generalizing X Y
  · refine IsZariskiLocalAtTarget.of_openCover Y.affineCover fun i => ?_
    have sq := IsPullback.of_hasPullback f (Y.affineCover.f i)
    have e : pullback.snd f (Y.affineCover.f i) ≫ Y.affineCover.f i ≫ g =
        pullback.fst f (Y.affineCover.f i) ≫ f ≫ g := by
      rw [← Category.assoc, ← sq.w, Category.assoc]
    exact this (pullback.snd f (Y.affineCover.f i)) inferInstance (Y.affineCover.f i ≫ g)
      inferInstance (by rw [e]; infer_instance) (by rw [e]; infer_instance)
      (fun k _ t => (H k t).target sq) ⟨_, rfl⟩
  obtain ⟨A, rfl⟩ := hA
  wlog hX : ∃ B, X = Spec B generalizing X
  · haveI hX' : IsAffine X := isAffine_of_isAffineHom f
    rw [← MorphismProperty.cancel_left_of_respectsIso @Flat X.isoSpec.inv]
    exact this (X.isoSpec.inv ≫ f) inferInstance (by rw [Category.assoc]; infer_instance)
      (by rw [Category.assoc]; infer_instance)
      (fun k _ t => (H k t).source _) ⟨_, rfl⟩
  obtain ⟨B, rfl⟩ := hX
  obtain ⟨f, rfl⟩ := Spec.map_surjective f
  obtain ⟨g, rfl⟩ := Spec.map_surjective g
  rw [← Spec.map_comp] at h1 h0
  rw [Flat.SpecMap_iff] at h1 ⊢
  rw [IsFinite.SpecMap_iff] at h2
  rw [HasRingHomProperty.Spec_iff (P := @LocallyOfFinitePresentation)] at hY h0
  letI : Algebra R A := g.hom.toAlgebra
  letI : Algebra A B := f.hom.toAlgebra
  letI : Algebra R B := (g ≫ f).hom.toAlgebra
  haveI : IsScalarTower R A B := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : Module.Flat R B := h1
  haveI : Module.Finite A B := h2
  haveI : Algebra.FinitePresentation R A := hY
  haveI : Algebra.FinitePresentation R B := h0
  haveI : Algebra.FinitePresentation A B :=
    Algebra.FinitePresentation.of_restrict_scalars_finitePresentation R A B
  haveI : Module.FinitePresentation A B :=
    Module.FinitePresentation.of_finite_of_finitePresentation A B
  refine flat_of_flat_fibres (R := R) (A := A) (B := B) fun k C _ _ _ t h e => ?_
  have sq := isPullback_SpecMap_of_isPushout _ _ _ _ (CommRingCat.isPushout_tensorProduct A C B)
  have := H k (Spec.map (CommRingCat.ofHom t)) _ _ _ (Spec.map (CommRingCat.ofHom h)) sq.flip
    (by
      rw [← Spec.map_comp, ← Spec.map_comp]
      congr 1
      ext1
      exact e)
  rw [Flat.SpecMap_iff] at this
  exact RingHom.flat_algebraMap_iff.mp this

end FinitePresFibreFlat

theorem flat_of_isFinite_of_finitePresentation_of_flat_geometric_fibres :
    ∀ (S : Scheme.{0}) (X Y : Over S) (f : X ⟶ Y), Flat X.hom → LocallyOfFinitePresentation X.hom → LocallyOfFinitePresentation Y.hom → IsFinite f.left → (∀ (K : Type) [Field K] [IsAlgClosed K] (t : Sp K ⟶ S), Flat ((Over.pullback t).map f).left) → Flat f.left := by
  intro S X Y f h1 h0 h2 h3 H
  refine FinitePresFibreFlat.flat_of_flatOver_fields f.left Y.hom h2 (by rwa [Over.w])
    (by rwa [Over.w]) h3 fun k _ t => ?_
  exact FiniteFibreFlat.flatOver_descend
    (Spec.map (CommRingCat.ofHom (algebraMap k (AlgebraicClosure k))))
    (FibreFlat.flatOver_of_pullback f _ (H _ _))

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.KodairaSpencerClassCohomologousAlongEndomorphismStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.KS
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kodairaSpencerClass_cohomologous_along_endomorphism : ∀ (K : Type) [Field K] (A₀ : Over (Sp K)) [GrpObj A₀] (g : ℕ) (v : Fin g → (epsR K ⟶ A₀)) (dd : Fin g → ∀ O : A₀.left.Opens, Γ(A₀.left, O) → Γ(A₀.left, O)), Smooth A₀.hom → IsLieBasis v → (∀ a, IsInvDer (v a) (dd a)) → ∀ (R : Type) [CommRing R] (x₀ : R →+* K) (X : Scheme.{0}) (p : X ⟶ Sp R) (m : A₀.left ⟶ X), IsPullback m A₀.hom p (spMap x₀) → ∀ (I : Type) (W : I → X.Opens) (D : R → K) d θ (f : X ⟶ X) (f₀ : A₀ ⟶ A₀) (F : Matrix (Fin g) (Fin g) K), KSCoc A₀.hom p m D W dd d θ → IsMonHom f₀ → f ≫ p = p → f₀.left ≫ m = m ≫ f → (∀ j, IsLieComb (fun i => F i j) v (v j ≫ f₀)) → ∀ x, Cohom f₀.left _ (lc A₀.hom (F x) θ) (θ x) := by
  first | exact @GlobalTheory.KS.cohom_ksCoc_of_endomorphism | exact GlobalTheory.KS.cohom_ksCoc_of_endomorphism | (intros; apply GlobalTheory.KS.cohom_ksCoc_of_endomorphism <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.LbPowDescendsOfIsotropicOfLaws
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory

theorem lbPow_descends_of_isotropic_of_laws : Out.Laws → ∀ (k : Type) [Field k] [IsAlgClosed k] (P : Out.PolAV (Sp k)) (n : ℕ) (C : Subgroup (𝟙_ (Over (Sp k)) ⟶ P.A)) (B : Over (Sp k)) [GrpObj B] (ψ : P.A ⟶ B), 0 < n → (n : k) ≠ 0 → (∀ x ∈ C, x ^ n = 1) → (∀ x ∈ C, ∀ y ∈ C, Out.WeilIs P.A P.L n x y 1) → IsMonHom ψ → IsFinite ψ.left → Etale ψ.left → Surjective ψ.left → (∀ x : 𝟙_ (Over (Sp k)) ⟶ P.A, x ≫ ψ = 1 ↔ x ∈ C) → ∃ M : LB B.left, M.IsLB ∧ LBIso (lbPow P.L n) (M.pull ψ.left) :=
  LinDescent.lbPow_descends

end GlobalTheory
end
end

