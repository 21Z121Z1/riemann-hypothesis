import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2202
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1457
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2853
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1541
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1802
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsLeadOfUnif
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle0002
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FamMod
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0001
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2799
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2839
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2855
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusHomOfIff
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0141
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0142
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.CrossRelationGivesConvolutionRelation
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0048
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0023
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0020
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0081
import Development.AbelianVarietyTheory.Definitions.Divisors.SmallFam
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0014
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0016
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0057
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0082
import Development.AbelianVarietyTheory.Statements.TorsionEndomorphisms.EndDeterminedOnTorsion
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0007
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0098
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsLineBundleGeneratorExtendingDensePart
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2687
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0060
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0028
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1582
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.EssFiniteTypeOfFiniteDimensional
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1701
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FromPullbackPiMapStalkLift
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2160
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2827
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2675
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1319
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1284
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1155
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SemiabelianTorusAfterSeparable
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0046
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0026
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0084
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0076
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2761
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2624
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2210
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsAbelianSchemeAndExtendOfGenericHoms
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0077
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2665
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2856
import Development.AbelianVarietyTheory.Definitions.Divisors.IsActIffIsDiagEnd
import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle0001
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2858
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0021

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzOrbitDecay
section
noncomputable section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThKSoDecay

namespace GlobalTheory.ThKSoDecay

theorem soDecayUnif (hP : KP) : SoDecayUnif := by
  intro F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hPair φ hφ hφS N
  obtain ⟨q, x, y, hxy, Cc, c, C0, A, hCc, hc, hcov⟩ :=
    GlobalTheory.T.exists_siegel_domain_reduction hP.siegelSetUnitary F E σ B n X r s hPair.base hPair.herm
  obtain ⟨C1, k, hC1⟩ := GlobalTheory.T.schwartz_siegel_domain_decay hP F E σ B n d X W M χX χW om r s r' s' hPair q x y hxy Cc hCc c hc φ hφ hφS (A * N)
  have hB := GlobalTheory.T.theta_basic_properties hP.base F E σ B n d X W M χX χW om r s r' s' hPair
  refine ⟨max C0 0 ^ N * C1, k, fun f g h => ?_⟩
  obtain ⟨γ, hγ, t, a, κ, ht', ha, hκ, hg, hht⟩ := hcov g
  have hΦ : pureA F f φ ∈ schA F (Fin n × Fin d) := Submodule.subset_span ⟨f, φ, hφ, rfl⟩
  have e : theta om (pureA F f φ) g h = theta om (pureA F f φ) (a * κ) h := by
    rw [← hg]
    have := (hB.1 _ hΦ).2.1 γ hγ 1 (one_mem _) g h
    rw [one_mul] at this
    exact this.symm
  have hP0 : (0 : ℝ) ≤ 1 + ∏ i, t i :=
    add_nonneg zero_le_one (Finset.prod_nonneg fun i _ => hc.le.trans (ht' i))
  have hq : (qht g : ℝ) ≤ max C0 0 * (1 + ∏ i, t i) ^ A := by
    have h1 : qht g ≤ ht (a * κ) := by
      rw [← hg]
      exact ciInf_le (OrderBot.bddBelow _) (⟨γ, hγ⟩ : ratU σ X.J)
    exact (NNReal.coe_le_coe.2 h1).trans (hht.trans
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (pow_nonneg hP0 A)))
  have hC0 : (0 : ℝ) ≤ max C0 0 := le_max_right _ _
  calc ‖theta om (pureA F f φ) g h‖ * (qht g : ℝ) ^ N
      ≤ ‖theta om (pureA F f φ) (a * κ) h‖ * (max C0 0 * (1 + ∏ i, t i) ^ A) ^ N := by
        rw [e]
        exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (NNReal.coe_nonneg _) hq N) (norm_nonneg _)
    _ = max C0 0 ^ N * (‖theta om (pureA F f φ) (a * κ) h‖ * (1 + ∏ i, t i) ^ (A * N)) := by
        rw [mul_pow, pow_mul]; ring
    _ ≤ max C0 0 ^ N * (C1 * semK (Fin n × Fin d) k f * (ht h : ℝ) ^ k) :=
        mul_le_mul_of_nonneg_left (hC1 f t a κ h ht' ha hκ) (pow_nonneg hC0 N)
    _ = max C0 0 ^ N * C1 * semK (Fin n × Fin d) k f * (ht h : ℝ) ^ k := by ring

theorem soDecay (hP : KP) : SoDecay := GlobalTheory.T.soDecay_of_prints_of_soDecayUnif hP.base (soDecayUnif hP)

end GlobalTheory.ThKSoDecay
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SecKRatioTraitDescendsToFractionField
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum.RatioDesc

open ReciprocityTheory.ChartRestriction.G.DVR.TG

theorem pull_fst_app_injective {K L : Type} [Field K] [Field L] (ψ : K →+* L) {X : Scheme.{0}} (h : X ⟶ Sp K)
    (U : X.Opens) : Function.Injective ((pullback.fst h (spMap ψ)).app U).hom := by
  have : Flat (spMap ψ) := by
    rw [HasRingHomProperty.Spec_iff (P := @Flat)]
    letI := ψ.toAlgebra
    exact (RingHom.flat_algebraMap_iff).2 inferInstance
  have : Surjective (spMap ψ) := by
    constructor
    intro x
    exact ⟨IsLocalRing.closedPoint L, Subsingleton.elim _ _⟩
  exact app_injective_of_flat_surj _ U

variable {A : Type} [CommRing A] {X Y Z : Scheme.{0}}

theorem scal_mul' (p : Y ⟶ Sp A) (a b : A) : scal p (a * b) = scal p a * scal p b := by
  unfold scal; rw [map_mul, map_mul]

theorem scal_one' (p : Y ⟶ Sp A) : scal p 1 = 1 := by
  unfold scal; rw [map_one, map_one]

theorem scal_comp' (f : Z ⟶ Y) (p : Y ⟶ Sp A) (r : A) : scal (f ≫ p) r = f.appTop.hom (scal p r) := by
  unfold scal; rw [Scheme.Hom.comp_appTop]; rfl

theorem scal_spMap {B : Type} [CommRing B] (g : Y ⟶ Sp B) (ψ : A →+* B) (r : A) :
    scal (g ≫ Spec.map (CommRingCat.ofHom ψ)) r = scal g (ψ r) := by
  rw [scal_comp']
  unfold scal
  congr 1
  have := Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom ψ)
  exact (congrArg (fun f => f.hom r) this).symm

theorem gs_top' (f : Z ⟶ Y) (z : Z) (a : Γ(Y, ⊤)) : gs f z ⊤ a = gs (𝟙 Z) z ⊤ (f.appTop.hom a) := by
  have := gs_pull (𝟙 Z) f z ⊤ trivial a
  rw [Category.id_comp] at this
  exact this.symm

theorem gs_zero'' (f : Z ⟶ Y) (z : Z) (U : Y.Opens) : gs f z U 0 = 0 := by
  unfold gs; split_ifs <;> simp

abbrev sg (g : Z ⟶ Sp A) (z : Z) (a : A) : Z.presheaf.stalk z := gs (𝟙 Z) z ⊤ (scal g a)

theorem sg_mul (g : Z ⟶ Sp A) (z : Z) (a b : A) : sg g z (a * b) = sg g z a * sg g z b := by
  unfold sg; rw [scal_mul', gs_mul _ z ⊤ trivial]

theorem sg_one (g : Z ⟶ Sp A) (z : Z) : sg g z 1 = 1 := by
  unfold sg; rw [scal_one', gs_eq _ z ⊤ trivial, map_one, map_one]

theorem sg_isUnit {F : Type} [Field F] (g : Z ⟶ Sp F) (z : Z) {a : F} (ha : a ≠ 0) : IsUnit (sg g z a) :=
  have h1 : sg g z a * sg g z a⁻¹ = 1 := by rw [← sg_mul, mul_inv_cancel₀ ha, sg_one]
  ⟨⟨_, _, h1, by rw [mul_comm]; exact h1⟩, rfl⟩

end GlobalTheory.Mum.RatioDesc

namespace GlobalTheory.Mum

open GlobalTheory.Mum.RatioDesc

theorem secK_ratio_descends : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (C : LabCover D) (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W] (T : Trait C W) (k : ℕ) (s₁ s₂ : SecK C.P.L.L C.α k) (c d : W), c ≠ 0 → d ≠ 0 → (∀ (Z : Scheme.{0}) (p : Z ⟶ T.G.left) (p' : Z ⟶ C.A.A.left), p ≫ T.β = p' ≫ C.α → ∀ (z : Z) (J : (Z ⟶ C.G.left) → C.P.L.L.ι), Good C.P.L.L z J → gs p z ⊤ (scal T.G.hom c) * sval s₁ p' z J = gs p z ⊤ (scal T.G.hom d) * sval s₂ p' z J) → ∃ r t : R, r ≠ 0 ∧ t ≠ 0 ∧ ∀ (Z : Scheme.{0}) (p' : Z ⟶ C.A.A.left) (z : Z) (J : (Z ⟶ C.G.left) → C.P.L.L.ι), Good C.P.L.L z J → gs p' z ⊤ (scal C.A.A.hom (algebraMap R (FractionRing R) t)) * sval s₁ p' z J = gs p' z ⊤ (scal C.A.A.hom (algebraMap R (FractionRing R) r)) * sval s₂ p' z J := by
  intro R _ _ _ _ D C W _ _ _ T k s₁ s₂ c d hc hd H
  obtain ⟨ψ, hψR, hψ⟩ := GlobalTheory.T.exists_genericPoint_factor_of_injective_base_map R C.toModif W T.φ T.inj T.ξ T.ξ_π
  let Y : Scheme.{0} := pullback C.A.A.hom (spMap ψ)
  let q : Y ⟶ C.A.A.left := pullback.fst C.A.A.hom (spMap ψ)
  let g : Y ⟶ Sp (FractionRing W) := pullback.snd C.A.A.hom (spMap ψ)
  have hw : (q ≫ C.α) ≫ C.G.hom = (g ≫ jK W) ≫ T.ξ := by
    simp only [Category.assoc]
    rw [C.α_cart.1.w, ← Category.assoc q, pullback.condition, Category.assoc]
    exact congrArg (g ≫ ·) hψ
  let p := T.cart.1.lift (q ≫ C.α) (g ≫ jK W) hw
  have hp : p ≫ T.β = q ≫ C.α := T.cart.1.lift_fst _ _ _
  have hpG : p ≫ T.G.hom = g ≫ jK W := T.cart.1.lift_snd _ _ _
  have hsc : ∀ (y : Y) (w : W),
      gs p y ⊤ (scal T.G.hom w) = sg g y (algebraMap W (FractionRing W) w) := by
    intro y w
    rw [gs_top', ← scal_comp', hpG, scal_spMap]

  set c' := algebraMap W (FractionRing W) c with hc'
  set d' := algebraMap W (FractionRing W) d with hd'
  have hc0 : c' ≠ 0 := fun h => hc (IsFractionRing.injective W (FractionRing W) (h.trans (map_zero _).symm))
  have hd0 : d' ≠ 0 := fun h => hd (IsFractionRing.injective W (FractionRing W) (h.trans (map_zero _).symm))
  let Uc : (Fin 1 → C.P.L.L.ι) → C.A.A.left.Opens := fun j => LB.wchart C.P.L.L (fun _ : Fin 1 => C.α) j
  have G0 : ∀ (j : Fin 1 → C.P.L.L.ι) (y : Y), q y ∈ Uc j →
      sg g y c' * gs q y (Uc j) (s₁.f j) = sg g y d' * gs q y (Uc j) (s₂.f j) := by
    intro j y hy
    obtain ⟨J, hJ, hJj⟩ := exists_good C.P.L.L C.P.L.isLB y (fun _ : Unit => q ≫ C.α) (fun _ => j 0)
      (fun _ _ _ => rfl) (fun _ => by simpa using Set.mem_iInter.1 hy 0)
    have e := H Y p q hp y J hJ
    have hj : ∀ i : Fin 1, J (q ≫ C.α) = j i := fun i => by rw [Subsingleton.elim i 0]; exact hJj ()
    rw [hsc, hsc, sval_of s₁ q y J j hj, sval_of s₂ q y J j hj] at e
    exact e

  have key : ∃ m₀ : FractionRing R, m₀ ≠ 0 ∧ ∀ (j : Fin 1 → C.P.L.L.ι) (y : Y), q y ∈ Uc j →
      gs q y (Uc j) (s₁.f j) = sg g y (ψ m₀) * gs q y (Uc j) (s₂.f j) := by
    by_cases h0 : ∀ j, s₂.f j = 0
    · refine ⟨1, one_ne_zero, fun j y hy => ?_⟩
      have e := G0 j y hy
      have hz : gs q y (Uc j) (s₂.f j) = 0 := by rw [h0 j]; exact gs_zero'' _ _ _
      rw [hz, mul_zero] at e
      rw [hz, mul_zero]
      exact (sg_isUnit g y hc0).mul_left_cancel (e.trans (mul_zero _).symm)
    · push Not at h0
      obtain ⟨j₀, hj₀⟩ := h0
      have e : ((q.app (Uc j₀)).hom (s₁.f j₀)) = (q.app (Uc j₀)).hom (s₂.f j₀) * resTop _ (scal g (d' / c')) := by
        apply fn_ext
        intro y hy
        have hy' : q ((𝟙 Y) y) ∈ Uc j₀ := by simpa using hy
        have e1 := gs_pull (𝟙 Y) q y (Uc j₀) hy' (s₁.f j₀)
        have e2 := gs_pull (𝟙 Y) q y (Uc j₀) hy' (s₂.f j₀)
        rw [Category.id_comp] at e1 e2
        rw [gs_mul _ y _ hy, gs_res _ y le_top hy]
        erw [e1, e2]
        apply (sg_isUnit g y hc0).mul_left_cancel
        have hcd : c' * (d' / c') = d' := by field_simp
        rw [G0 j₀ y hy]
        change _ = sg g y c' * (_ * sg g y (d' / c'))
        rw [mul_comm _ (sg g y (d' / c')), ← _root_.mul_assoc, ← sg_mul, hcd]
      obtain ⟨m₀, hm₀⟩ := GlobalTheory.T.mem_range_of_base_change_ratio_sections ψ C.A.A.hom (Uc j₀) (s₁.f j₀) (s₂.f j₀) (d' / c') hj₀ e
      refine ⟨m₀, fun h => ?_, fun j y hy => ?_⟩
      · rw [h, map_zero] at hm₀
        exact div_ne_zero hd0 hc0 hm₀.symm
      · apply (sg_isUnit g y hc0).mul_left_cancel
        have hcd : c' * (d' / c') = d' := by field_simp
        rw [G0 j y hy, hm₀, ← _root_.mul_assoc, ← sg_mul, hcd]

  obtain ⟨m₀, hm0, hm⟩ := key
  obtain ⟨r, t, ht, hrt⟩ := IsFractionRing.div_surjective (A := R) m₀
  have ht0 : t ≠ 0 := nonZeroDivisors.ne_zero ht
  have ht' : algebraMap R (FractionRing R) t ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors ht
  have hr0 : r ≠ 0 := by
    rintro rfl
    apply hm0
    rw [← hrt, map_zero, zero_div]
  refine ⟨r, t, hr0, ht0, ?_⟩
  have hK : algebraMap R (FractionRing R) t * m₀ = algebraMap R (FractionRing R) r := by
    rw [← hrt]; field_simp
  let F₁ : ∀ j, Γ(C.A.A.left, Uc j) := fun j => s₁.f j
  let F₂ : ∀ j, Γ(C.A.A.left, Uc j) := fun j => s₂.f j
  have sec : ∀ j : Fin 1 → C.P.L.L.ι, resTop (Uc j) (scal C.A.A.hom (algebraMap R (FractionRing R) t)) * F₁ j =
      resTop (Uc j) (scal C.A.A.hom (algebraMap R (FractionRing R) r)) * F₂ j := by
    intro j
    apply pull_fst_app_injective ψ C.A.A.hom (Uc j)
    apply fn_ext
    intro y hy
    have hy' : q ((𝟙 Y) y) ∈ Uc j := by simpa using hy
    have e1 := gs_pull (𝟙 Y) q y (Uc j) hy' (resTop (Uc j) (scal C.A.A.hom (algebraMap R (FractionRing R) t)) * F₁ j)
    have e2 := gs_pull (𝟙 Y) q y (Uc j) hy' (resTop (Uc j) (scal C.A.A.hom (algebraMap R (FractionRing R) r)) * F₂ j)
    rw [Category.id_comp] at e1 e2
    erw [e1, e2]
    rw [gs_mul q y _ hy, gs_mul q y _ hy, gs_res q y le_top hy, gs_res q y le_top hy, gs_top' q, gs_top' q,
      ← scal_comp', ← scal_comp', pullback.condition, scal_spMap, scal_spMap]
    change sg g y _ * _ = sg g y _ * _
    rw [hm j y hy, ← _root_.mul_assoc, ← sg_mul, ← map_mul, hK]
  intro Z p' z J hJ
  have hm' : p' z ∈ Uc (fun _ => J (p' ≫ C.α)) := hJ.mem (fun _ : Fin 1 => C.α) p'
  have e := congrArg (gs p' z (Uc (fun _ => J (p' ≫ C.α)))) (sec (fun _ => J (p' ≫ C.α)))
  rw [gs_mul p' z _ hm', gs_mul p' z _ hm', gs_res p' z le_top hm', gs_res p' z le_top hm'] at e
  exact e

end GlobalTheory.Mum
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SectionValueEqZeroWeightIndependenceLevelStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.Mum GlobalTheory.Mum.Two GlobalTheory.FieldBaseChange
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sectionValue_eq_zero_weightIndependence_level : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D : DegPre R) (e : ℕ) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (g : GtCoord I D e G) (Y : Over (Spec (CommRingCat.of R))) (p : Y ⟶ D.P.A) (X : Scheme.{0}) (N : LB X), N.IsLB → ∀ (ι₀ : D.P.A.left ⟶ X) (π : N.ι → D.P.L.ι), IsPart N D.P.L ι₀ π → ∀ (K : Type) [Fintype K] (φ : D.X → K → (Y.left ⟶ X)) (ε : K → ℤ) (d : ∀ α, LB.Sec (LB.LinComb N (φ α) ε)) (s : Finset D.X), (∀ (Z : Scheme.{0}) (x : Z ⟶ (thickObj R I e G).left) (r : Z ⟶ Y.left), r ≫ p.left = x ≫ g.pG.left → ∀ (z : Z) (J), Good N z J → ∑ α ∈ s, sval (d α) r z J * (val (g.t α) x z (rs ι₀ π J)).val = 0) → ∀ α ∈ s, ∀ (Z : Scheme.{0}) (x : Z ⟶ (thickObj R I e G).left) (r : Z ⟶ Y.left), r ≫ p.left = x ≫ g.pG.left → ∀ (z : Z) (J), Good N z J → sval (d α) r z J = 0 := by
  first | exact @GlobalTheory.sval_eq_zero_of_sum_mul_coord_part | exact GlobalTheory.sval_eq_zero_of_sum_mul_coord_part | (intros; apply GlobalTheory.sval_eq_zero_of_sum_mul_coord_part <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SectionValuesIdentityDescendsToFibreProductStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sectionValues_identity_descends_to_fibreProduct : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (C : LabCover D) (k : ℕ) (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W] (T : Trait C W) (F : Type) [Field F] [Algebra (FractionRing R) F] [Algebra (FractionRing W) F], (∀ r, algebraMap (FractionRing R) F (algebraMap R _ r) = algebraMap (FractionRing W) F (algebraMap W _ (T.φ r))) → ∀ (σ : SecK C.P.L.L T.β k) (s : SecK C.P.L.L C.α k) (w : W), (∀ (Z : Scheme.{0}) (p : Z ⟶ T.G.left) (p' : Z ⟶ (TFK (R := R) F ⊗ C.A.A).left), p ≫ T.β = p' ≫ (snd (TFK (R := R) F) C.A.A).left ≫ C.α → p ≫ T.G.hom = p' ≫ (fst (TFK (R := R) F) C.A.A).left ≫ spMap ((algebraMap (FractionRing W) F).comp (algebraMap W _)) → ∀ z J, Good C.P.L.L z J → sval σ p z J = gs p z ⊤ (scal T.G.hom w) * sval s (p' ≫ (snd (TFK (R := R) F) C.A.A).left) z J) → ∀ (Z : Scheme.{0}) (p : Z ⟶ T.G.left) (p' : Z ⟶ C.A.A.left), p ≫ T.β = p' ≫ C.α → ∀ z J, Good C.P.L.L z J → sval σ p z J = gs p z ⊤ (scal T.G.hom w) * sval s p' z J := by
  first | exact @GlobalTheory.Mum.ValDescent.desc | exact GlobalTheory.Mum.ValDescent.desc | (intros; apply GlobalTheory.Mum.ValDescent.desc <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SelfIntersectionMonoOfHeightNef
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef

namespace GlobalTheory.HSNef

theorem selfInter_mono : GlobalTheory.Published.ArCalc → ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (A B : HermLB p) (α β : ℝ), Le B A → (∀ x y : ℕ, HtNef ((A.pow x).tens (B.pow y)) D) → A.IsSelfInter α → B.IsSelfInter β → β ≤ α := by
  intro hC k _ Y _ p D hX A B α β hle hnef hα hβ
  obtain ⟨Φ, hΦ⟩ := ((hC.arExists k Y p D hX).2 (Fin 2) ![A, B]).1
  have hpos := GlobalTheory.T.mixedArithIntersection_nonneg_of_small_section_diff hC k Y p D hX A B Φ hΦ hle
  have hmono := GlobalTheory.monotone_form_along_segment D Φ fun x y => hpos x y (hnef x y)
  have hd := ((hC.arIso k Y p D hX).2 (Fin 2) _ Φ hΦ).1
  have h0 : Φ (MvPolynomial.X 0 ^ (D + 1)) = α := HermLB.IsSelfInter.unique hX (hd 0) hα
  have h1 : Φ (MvPolynomial.X 1 ^ (D + 1)) = β := HermLB.IsSelfInter.unique hX (hd 1) hβ
  rw [← h0, ← h1]
  exact hmono

end GlobalTheory.HSNef
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemiAbelianBaseChangeNormalDomainGenericFibreStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.semiAbelian_baseChange_normal_domain_generic_fibre : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G], IsSemiAbelian G → ∀ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R] (χ : Sp R ⟶ S), IsLocallyNoetherian (Over.mk χ ⊗ G).left ∧ GlobalTheory.IsNormalScheme (Over.mk χ ⊗ G).left ∧ IsPreimmersion ((Over.homMk (spMap (algebraMap R (FractionRing R))) rfl : Over.mk (spMap (algebraMap R (FractionRing R)) ≫ χ) ⟶ Over.mk χ) ▷ G).left ∧ ∀ W : (Over.mk χ ⊗ G).left.Opens, Function.Injective ((((Over.homMk (spMap (algebraMap R (FractionRing R))) rfl : Over.mk (spMap (algebraMap R (FractionRing R)) ≫ χ) ⟶ Over.mk χ) ▷ G).left.app W).hom) := by
  first | exact @GlobalTheory.SemiAbGenericFibre.baseChange_normal_generic | exact GlobalTheory.SemiAbGenericFibre.baseChange_normal_generic | (intros; apply GlobalTheory.SemiAbGenericFibre.baseChange_normal_generic <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemiAbelianExtensionAbelianOverOpenPartStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.semiAbelianExtension_abelian_over_open_part : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (M : RatModel o Ω) (U₀ : M.Z.Opens) (EE : M.Lat S.J) (FinalForm : ZHOut ρ M U₀ EE), S.Over₀ M U₀ → (U₀ : Set M.Z) ⊆ abLocus FinalForm.G := by
  first | exact @GlobalTheory.ZH.abLocus_of_over₀ | exact GlobalTheory.ZH.abLocus_of_over₀ | (intros; apply GlobalTheory.ZH.abLocus_of_over₀ <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemiAbelianLieSeminegativeOfNeron
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits MonoidalCategory CartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.VB GlobalTheory.LieVB GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.NeronCurve GlobalTheory.Published
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.NeronCurve.LieDescent

theorem semiNeg_of_iso {k : Type} [Field k] {C : Scheme.{0}} [Algebra k Γ(C, ⊤)] {F F' : C.Modules} (e : F ≅ F')
    (h : SemiNeg k F) : SemiNeg k F' := fun W r hW i _ =>
  h W r hW (i ≫ e.inv) (mono_comp i e.inv)

def lieBaseIso {C C' : Scheme.{0}} [IsIntegral C] (π : C' ⟶ C) (G : Over C) [GrpObj G] [IsSemiAbelian G] :
    (Scheme.Modules.pullback π).obj (Lie G) ≅ Lie ((Over.pullback π).obj G) :=
  have h := isGrpPullback_pullback G π
  have hg := (exists_isVB_of_isSemiAbelian G).choose_spec.1
  have := isIso_lieBase h hg
  asIso (lieBase h)

end GlobalTheory.NeronCurve.LieDescent

namespace GlobalTheory.NeronCurve

end GlobalTheory.NeronCurve
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemiAbelianPullbackAbelianOverOpen
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.SiegTh Classical
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.FactorOverOpen

theorem isNormalScheme_opens {S : Scheme.{0}} (h : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme S) (V : S.Opens) :
    ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme V.toScheme := fun x => by
  obtain ⟨h₁, h₂⟩ := h x.1
  have e := (V.stalkIso x).commRingCatIsoToRingEquiv
  exact ⟨e.toMulEquiv.isDomain _, IsIntegrallyClosed.of_equiv e.symm⟩

theorem isNoetherian_opens {S : Scheme.{0}} [AlgebraicGeometry.IsNoetherian S] (V : S.Opens) :
    AlgebraicGeometry.IsNoetherian V.toScheme := by
  have : CompactSpace V.toScheme :=
    isCompact_iff_compactSpace.1 (TopologicalSpace.NoetherianSpace.isCompact (V : Set S))
  exact {}

theorem exists_isGrpPullback_cancel {S S' S'' : Scheme.{0}} {H : Over S} {G : Over S'} {A' : Over S''}
    [GrpObj H] [GrpObj G] [GrpObj A'] {f : S' ⟶ S} {g : S'' ⟶ S'} {φ : A'.left ⟶ H.left} {ψ : G.left ⟶ H.left}
    (hφ : IsGrpPullback A' H (g ≫ f) φ) (hψ : IsGrpPullback G H f ψ) :
    ∃ φ' : A'.left ⟶ G.left, IsGrpPullback A' G g φ' := by
  obtain ⟨i, hi, -⟩ := grpPullback_iso hφ ((isGrpPullback_pullback G g).comp hψ)
  exact ⟨_, ((isGrpPullback_of_iso i).comp (isGrpPullback_pullback G g)).congr (Category.id_comp _) rfl⟩

end GlobalTheory.FactorOverOpen

open GlobalTheory.FactorOverOpen in

theorem GlobalTheory.FactorOverOpen.factor_over_open : ∀ {S X : Scheme.{0}} [IsIntegral S] [AlgebraicGeometry.IsNoetherian S] (hS : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme S) (hX : IsSeparated (toZ X)) (A : Over X) [GrpObj A] (hA : IsAbelianScheme A) (H : Over S) [GrpObj H] (hH : IsSemiAbelian H) (U₀ U : S.Opens) (hU₀ : (U₀ : Set S).Nonempty) (hU : (U : Set S).Nonempty) (u' : U₀.toScheme ⟶ X) (c : U.toScheme ⟶ X) (A₀ : Over U₀.toScheme) [GrpObj A₀] (e₀ : A₀.left ⟶ H.left) (e₁ : A₀.left ⟶ A.left) (h₀ : IsGrpPullback A₀ H U₀.ι e₀) (h₁ : IsGrpPullback A₀ A u' e₁) (K : Type) [Field K] (pt : Sp K ⟶ S) (hpt : Set.range pt = {genericPoint S}) (hgen : ∀ (x : Sp K ⟶ U.toScheme) (y : Sp K ⟶ U₀.toScheme), x ≫ U.ι = pt → y ≫ U₀.ι = pt → x ≫ c = y ≫ u'), ∃ e : pullback A.hom c ⟶ H.left, IsGrpPullback ((Over.pullback c).obj A) H U.ι e := by
  intro S X _ _ hS hX A _ hA H _ hH U₀ U hU₀ hU u' c A₀ _ e₀ e₁ h₀ h₁ K _ pt hpt hgen

  let V : S.Opens := U ⊓ U₀
  have hη : ∀ W : S.Opens, (W : Set S).Nonempty → genericPoint S ∈ W := fun W hW =>
    ((genericPoint_spec S).mem_open_set_iff W.isOpen).2 (by simpa using hW)
  have hηV : genericPoint S ∈ V := ⟨hη U hU, hη U₀ hU₀⟩
  haveI : Nonempty V := ⟨⟨_, hηV⟩⟩
  haveI : Nonempty U := ⟨⟨_, hη U hU⟩⟩
  let jU : V.toScheme ⟶ U.toScheme := S.homOfLE inf_le_left
  let j₀ : V.toScheme ⟶ U₀.toScheme := S.homOfLE inf_le_right
  have hjU : jU ≫ U.ι = V.ι := S.homOfLE_ι _
  have hj₀ : j₀ ≫ U₀.ι = V.ι := S.homOfLE_ι _

  have hrange : Set.range pt ⊆ Set.range V.ι := by
    rw [Scheme.Opens.range_ι, hpt]
    simpa using hηV
  let z : Sp K ⟶ V.toScheme := IsOpenImmersion.lift V.ι pt hrange
  have hz : z ≫ V.ι = pt := IsOpenImmersion.lift_fac _ _ _
  haveI : IsDominant z := by
    refine ⟨?_⟩
    rw [DenseRange, dense_iff_closure_eq,
      V.ι.isOpenEmbedding.isInducing.closure_eq_preimage_closure_image, ← Set.range_comp]
    have : (⇑V.ι ∘ ⇑z) = ⇑pt := by rw [← hz]; rfl
    rw [this, hpt, (genericPoint_spec S).def]
    rfl
  have ha : jU ≫ c = j₀ ≫ u' := by
    refine ext_of_isDominant_of_isSeparated (ReciprocityTheory.ChartRestriction.G.Semi.toZ X)
      (specULiftZIsTerminal.hom_ext _ _) z ?_
    have := hgen (z ≫ jU) (z ≫ j₀) (by rw [Category.assoc, hjU, hz]) (by rw [Category.assoc, hj₀, hz])
    simpa only [Category.assoc] using this

  let G := (Over.pullback U.ι).obj H
  let G' := (Over.pullback c).obj A
  have pH : IsGrpPullback ((Over.pullback j₀).obj A₀) H (jU ≫ U.ι) _ :=
    ((isGrpPullback_pullback A₀ j₀).comp h₀).congr (hj₀.trans hjU.symm) rfl
  have pA : IsGrpPullback ((Over.pullback j₀).obj A₀) A (jU ≫ c) _ :=
    ((isGrpPullback_pullback A₀ j₀).comp h₁).congr ha.symm rfl
  obtain ⟨φ, hφ⟩ := exists_isGrpPullback_cancel pH (isGrpPullback_pullback H U.ι)
  obtain ⟨ψ, hψ⟩ := exists_isGrpPullback_cancel pA (isGrpPullback_pullback A c)

  haveI := isNoetherian_opens U
  haveI : IsDominant jU := ⟨jU.isOpenEmbedding.isOpen_range.dense (Set.range_nonempty _)⟩
  have hG : IsSemiAbelian G := IsSemiAbelian.pullback U.ι H hH
  have hG' : IsSemiAbelian G' := IsSemiAbelian.pullback c A (GlobalTheory.isSemiAbelian_of_isAbelianScheme A hA)
  obtain ⟨E, ⟨hE, -⟩, -⟩ := GlobalTheory.Published.SemiAbelianHomExtension.existsUnique_iso_of_extensions
    GlobalTheory.semiAbelianHomExtension_holds (isNormalScheme_opens hS U) hG' hG hψ hφ
  exact ⟨_, ((isGrpPullback_of_iso E).comp (isGrpPullback_pullback H U.ι)).congr (Category.id_comp _) rfl⟩
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemiAbelianThickeningHomEqOfEqOnOpenStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.semiAbelian_thickening_hom_eq_of_eq_on_open : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ U : Unif (maximalIdeal R) D A G, ∀ (e : ℕ) (x x' : thickObj R (maximalIdeal R) e G ⟶ thickObj R (maximalIdeal R) e G), IsMonHom x → IsMonHom x' → ∀ (W : (thickObj R (maximalIdeal R) e G).left.Opens) (y : (thickObj R (maximalIdeal R) e G).left), y ∈ W → W.ι ≫ x.left = W.ι ≫ x'.left → x = x' := by
  first | exact @GlobalTheory.MumAgree.eq_of_eq_on_open | exact GlobalTheory.MumAgree.eq_of_eq_on_open | (intros; apply GlobalTheory.MumAgree.eq_of_eq_on_open <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemiAbelianUniformisingEighthPowerIsPowerModelStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.semiAbelian_uniformising_eighthPower_isPower_model : ∀ (g n : ℕ) (o : Type) [CommRing o] (ζ : o) (F : SFam g n ζ) (V₁ : Type) [CommRing V₁] [IsDomain V₁] [IsLocalRing V₁], IsCN V₁ → ∀ (D₀ : DegData V₁ (maximalIdeal V₁)) (G₀ : Over (Sp V₁)) [GrpObj G₀] [IsCommMonObj G₀] (A₀ : PolAV (Sp (FractionRing V₁))) (U₀ : Unif (maximalIdeal V₁) D₀ A₀ G₀) (y : Sp (FractionRing V₁) ⟶ F.X) (α : A₀.A.left ⟶ F.univ.A.left), IsSemiAbelian G₀ → IsGrpPullback A₀.A F.univ.A y α → ∀ (P : PolAV (Sp (FractionRing V₁))) (c : SiegPre g n ζ (y ≫ F.s)) (φc : c.A.left ⟶ F.univ.A.left), IsGrpPullback c.A F.univ.A y φc → ∀ pr : Fin 8 → (P.A ⟶ c.A), (∀ a, IsMonHom (pr a)) → (∀ (T' : Over (Sp (FractionRing V₁))) (y' : Fin 8 → (T' ⟶ c.A)), ∃! x : T' ⟶ P.A, ∀ a, x ≫ pr a = y' a) → ∀ (G : Over (Sp V₁)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (D : DegData V₁ (maximalIdeal V₁)) (U : Unif (maximalIdeal V₁) D P G), ∃ q : Fin 8 → (G ⟶ G₀), (∀ u, IsMonHom (q u)) ∧ (∀ (T' : Over (Sp V₁)) (y' : Fin 8 → (T' ⟶ G₀)), ∃! x : T' ⟶ G, ∀ u, x ≫ q u = y' u) ∧ ∀ u, ((Over.pullback (jK V₁)).map (q u) ≫ U₀.gen.hom).left ≫ α = (U.gen.hom ≫ pr u).left ≫ φc := by
  first | exact @GlobalTheory.Poinc.Sep.unif_pow_isPow_model | exact GlobalTheory.Poinc.Sep.unif_pow_isPow_model | (intros; apply GlobalTheory.Poinc.Sep.unif_pow_isPow_model <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SurjectivePiLiftKaehlerCoordinateDerivationsStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.CechDR GlobalTheory.CechPer
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.surjective_pi_liftKaehler_coordinateDerivations : ∀ (A : Over (Sp ℂ)) [GrpObj A] (g : ℕ) (L : LB A.left) (u : HolUnif A L g), IsAbelianScheme A → ∀ (U : A.left.affineOpens) (d : Fin g → Derivation ℂ (Sec (str A) U.1) (Sec (str A) U.1)), (∀ a x, ∀ z ∈ pre u.ex U.1, val u.ex U.1 (d a x) z = fderiv ℂ (val u.ex U.1 x) z (Pi.single a 1)) → Function.Surjective (LinearMap.pi fun a => (d a).liftKaehlerDifferential) := by
  first | exact @GlobalTheory.CechPer.surjective_pi_liftKaehler_coord | exact GlobalTheory.CechPer.surjective_pi_liftKaehler_coord | (intros; apply GlobalTheory.CechPer.surjective_pi_liftKaehler_coord <;> assumption)
end

