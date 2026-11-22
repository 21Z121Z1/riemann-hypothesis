import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsPreDividedPowersOfGenerators
import Development.AbelianVarietyTheory.Definitions.Divisors.RatBasisLinearIndependentInt
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0012
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsCuspidalIffCompositions
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0735
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.ImmersedBy
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0291
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0007
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0736
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0019
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0020
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
import ReciprocityTheory.L2DbarEstimates.Imports
import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.FourSignHolds
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.L2ExtensionLogCanonical
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0004
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0737
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0203
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0235
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0741
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0746
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0732
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0702
import Development.AbelianVarietyTheory.Definitions.Divisors.GalMapMul
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0078
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0026
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RigExtMapRelFrobCompRigOfOmega
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0587

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsPreDividedPowersOfGeneratorsStatement
section
open DividedPowers GlobalTheory.Cris GlobalTheory.PDA
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_isPreDividedPowers_of_generators : ∀ (B ι : Type) [CommRing B] (x : ι → B) (g : ι → ℕ → B), (∀ i, g i 0 = 1) → (∀ i, g i 1 = x i) → (∀ i n, n ≠ 0 → g i n ∈ Ideal.span (Set.range x)) → (∀ i m n, g i m * g i n = ((m + n).choose m : B) * g i (m + n)) → (∀ c : ι →₀ B, (c.sum fun i a ↦ a * x i) = 0 → (c.prod fun i a ↦ PowerSeries.mk fun n ↦ a ^ n * g i n) = 1) → ∃ γ : ℕ → B → B, IsPreDP (Ideal.span (Set.range x)) γ ∧ ∀ i n, γ n (x i) = g i n := by
  first | exact @GlobalTheory.PDA.exists_isPreDividedPowers_of_generators₂ | exact GlobalTheory.PDA.exists_isPreDividedPowers_of_generators₂ | (intros; apply GlobalTheory.PDA.exists_isPreDividedPowers_of_generators₂ <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLeviGeneratedCommutingBlockGL
section
noncomputable section

namespace GlobalTheory.Parabolic.LeviGen

open Formalism.L2.DIV GlobalTheory.FinGL GlobalTheory.Parabolic GlobalTheory.IndefiniteRowSideFullHecke.BlockProductIsomorphism Matrix

variable {F : Type} [Field F] {r d d' : ℕ}

theorem mem_range_blockEnum (b : Fin r → ℕ) (c : ℕ) (h : (block b c).card = d) (i : Fin r) :
    i ∈ Set.range (blockEnum b c h) ↔ b i = c := by
  have e : Set.range (blockEnum b c h) = (block b c : Set (Fin r)) := Finset.range_orderEmbOfFin _ h
  rw [e]
  simp [block]

theorem extendMat_comm (e : Fin d ↪ Fin r) (e' : Fin d' ↪ Fin r) (h : ∀ a a', e a ≠ e' a')
    (M : Matrix (Fin d) (Fin d) F) (N : Matrix (Fin d') (Fin d') F) :
    extendMat e M * extendMat e' N = extendMat e' N * extendMat e M := by
  have h1 : (incl F e)ᵀ * incl F e' = 0 := by
    ext a a'
    simp [incl, Matrix.mul_apply, Matrix.one_apply, h a a']
  have h2 : (incl F e')ᵀ * incl F e = 0 := by
    ext a a'
    simp [incl, Matrix.mul_apply, Matrix.one_apply, (h a' a).symm]
  have h3 : incl F e * (M - 1) * (incl F e)ᵀ * (incl F e' * (N - 1) * (incl F e')ᵀ) = 0 := by
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (incl F e)ᵀ, h1]; simp
  have h4 : incl F e' * (N - 1) * (incl F e')ᵀ * (incl F e * (M - 1) * (incl F e)ᵀ) = 0 := by
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (incl F e')ᵀ, h2]; simp
  simp only [extendMat, MonoidHom.coe_mk, OneHom.coe_mk]
  simp only [add_mul, mul_add, h3, h4, one_mul, mul_one]
  abel

def leviIncl (F : Type) [Field F] (b : Fin r → ℕ) (c : ℕ) (h : (block b c).card = d) :
    GL (Fin d) F →* levi F b :=
  ((blockTri (κ := F) b).subtype.comp (blockHom F b c h)).codRestrict _ fun g => by
    refine mem_levi.2 fun i j hij => ?_
    show extendMat (blockEnum b c h) (g : Matrix (Fin d) (Fin d) F) i j = 0
    rw [extendMat_out, Matrix.one_apply_ne (fun e => hij (congrArg b e))]
    simp only [mem_range_blockEnum]
    omega

theorem leviIncl_val (b : Fin r → ℕ) (c : ℕ) (h : (block b c).card = d) (g : GL (Fin d) F) :
    ((leviIncl F b c h g : GL (Fin r) F) : Matrix (Fin r) (Fin r) F) =
      extendMat (blockEnum b c h) (g : Matrix (Fin d) (Fin d) F) := rfl

def leviRes (F : Type) [Field F] (b : Fin r → ℕ) (c : ℕ) (h : (block b c).card = d) :
    levi F b →* GL (Fin d) F :=
  leviBlock b (blockEnum b c h) (blockEnum b c h).injective fun i j hij => by
    rw [mem_range_blockEnum, ← hij, blockEnum_mem b c h]

theorem leviRes_apply (b : Fin r → ℕ) (c : ℕ) (h : (block b c).card = d) (m : levi F b) (a a' : Fin d) :
    (leviRes F b c h m : Matrix (Fin d) (Fin d) F) a a' =
      ((m : GL (Fin r) F) : Matrix (Fin r) (Fin r) F) (blockEnum b c h a) (blockEnum b c h a') := rfl

theorem leviRes_leviIncl (b : Fin r → ℕ) (c : ℕ) (h : (block b c).card = d) (g : GL (Fin d) F) :
    leviRes F b c h (leviIncl F b c h g) = g := by
  refine Units.ext (Matrix.ext fun a a' => ?_)
  rw [leviRes_apply, leviIncl_val, extendMat_in]

theorem leviRes_leviIncl_ne (b : Fin r → ℕ) {c c' : ℕ} (h : (block b c).card = d) (h' : (block b c').card = d')
    (hc : c' ≠ c) (g : GL (Fin d) F) : leviRes F b c' h' (leviIncl F b c h g) = 1 := by
  refine Units.ext (Matrix.ext fun a a' => ?_)
  rw [leviRes_apply, leviIncl_val, extendMat_out]
  · simp [Matrix.one_apply]
  · left
    rw [mem_range_blockEnum, blockEnum_mem b c' h']
    exact hc

theorem leviIncl_comm (b : Fin r → ℕ) {c c' : ℕ} (h : (block b c).card = d) (h' : (block b c').card = d')
    (hc : c ≠ c') (g : GL (Fin d) F) (g' : GL (Fin d') F) :
    Commute (leviIncl F b c h g) (leviIncl F b c' h' g') := by
  refine Subtype.ext (Units.ext ?_)
  refine extendMat_comm _ _ (fun a a' e => hc ?_) _ _
  rw [← blockEnum_mem b c h a, e, blockEnum_mem b c' h']

theorem iSup_range_leviIncl (b : Fin r → ℕ) (d : Set.range b → ℕ)
    (h : ∀ c : Set.range b, (block b c).card = d c) :
    (⨆ c : Set.range b, (leviIncl F b c (h c)).range) = ⊤ := by
  classical
  have key : ∀ s : Finset (Set.range b), ∀ m : levi F b,
      (∀ c : Set.range b, c ∉ s → leviRes F b c (h c) m = 1) →
        m ∈ ⨆ c : Set.range b, (leviIncl F b c (h c)).range := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      intro m hm
      have : m = 1 := by
        refine Subtype.ext (Units.ext (Matrix.ext fun i j => ?_))
        by_cases hij : b i = b j
        · let c : Set.range b := ⟨b i, i, rfl⟩
          obtain ⟨a, ha⟩ := (mem_range_blockEnum b c (h c) i).2 rfl
          obtain ⟨a', ha'⟩ := (mem_range_blockEnum b c (h c) j).2 hij.symm
          have h1 := leviRes_apply b c (h c) m a a'
          rw [hm c (Finset.notMem_empty _), ha, ha'] at h1
          rw [← h1]
          have : i = j ↔ a = a' := by rw [← (blockEnum b c (h c)).injective.eq_iff, ha, ha']
          simp [Matrix.one_apply, this]
        · rw [m.2 i j hij]
          simp [Matrix.one_apply_ne (fun e => hij (congrArg b e))]
      rw [this]
      exact Subgroup.one_mem _
    | insert c s _ ih =>
      intro m hm
      have e : m = m * leviIncl F b c (h c) (leviRes F b c (h c) m)⁻¹ *
          leviIncl F b c (h c) (leviRes F b c (h c) m) := by simp
      rw [e]
      refine Subgroup.mul_mem _ (ih _ fun c' hc' => ?_) (Subgroup.mem_iSup_of_mem c ⟨_, rfl⟩)
      by_cases hcc : c' = c
      · subst hcc
        rw [map_mul, leviRes_leviIncl, mul_inv_cancel]
      · rw [map_mul, leviRes_leviIncl_ne b _ _ (fun e => hcc (Subtype.ext e)), mul_one]
        exact hm c' (by simp [hcc, hc'])
  have := Fintype.ofFinite (Set.range b)
  exact eq_top_iff.2 fun m _ => key Finset.univ m fun c hc => absurd (Finset.mem_univ c) hc

theorem levi_generated : ∀ (F : Type) [Field F] (r : ℕ) (b : Fin r → ℕ) (d : Set.range b → ℕ)
    (h : ∀ c : Set.range b, (block b c).card = d c), ∃ f : ∀ c : Set.range b, GL (Fin (d c)) F →* levi F b,
    (∀ (c : Set.range b) (g : GL (Fin (d c)) F),
      (f c g : GL (Fin r) F) = (blockHom F b c (h c) g : GL (Fin r) F)) ∧ (⨆ c, (f c).range) = ⊤ ∧
    ∀ c c' : Set.range b, c ≠ c' → ∀ (x : GL (Fin (d c)) F) (y : GL (Fin (d c')) F), Commute (f c x) (f c' y) :=
  fun F _ _ b d h => ⟨fun c => leviIncl F b c (h c), fun _ _ => rfl, iSup_range_leviIncl b d h,
    fun c c' hc x y => leviIncl_comm b (h c) (h c') (fun e => hc (Subtype.ext e)) x y⟩

end GlobalTheory.Parabolic.LeviGen
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLiftAndAugmentationMapStatement
section
open DividedPowers GlobalTheory.Cris GlobalTheory.PDA
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_lift_and_augmentation_map : ∀ (B : Type) [CommRing B] (Q : PDPoly B), (∀ (C : Type) [CommRing C] (f : B →+* C) (c : ℕ → C), c 0 = 1 → (∀ m n, c m * c n = ((m + n).choose m : C) * c (m + n)) → ∃ F : Q.P →+* C, (∀ b, F (algebraMap B Q.P b) = f b) ∧ ∀ n, F (Q.e n) = c n) ∧ ∃ ε : Q.P →ₐ[B] B, ∀ p, p ∈ Q.aug ↔ ε p = 0 := by
  first | exact @GlobalTheory.PDA.PDPoly.exists_lift_and_aug | exact GlobalTheory.PDA.PDPoly.exists_lift_and_aug | (intros; apply GlobalTheory.PDA.PDPoly.exists_lift_and_aug <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLiftOfIsProperOfIsHomId
section
open AlgebraicGeometry CategoryTheory Limits
open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH

namespace GlobalTheory

theorem exists_lift_of_isProper_of_isHom_id :
    ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] (Y M : RatModel o Ω) (q : Y.Z ⟶ M.Z),
      M.IsHom Y (AlgHom.id o Ω) q → IsProper q → ∀ (p : ℕ) [Fact p.Prime] (y : Sp (OO p) ⟶ M.Z),
        ∃ y' : Sp (OO p) ⟶ Y.Z, y' ≫ q = y := by
  intro o Ω _ _ _ Y M q hq hp p _ y
  have hq' : Y.pt ≫ q = spMap (AlgHom.id o Ω).toRingHom ≫ M.pt := by
    first | exact hq | exact hq.1 | exact hq.2
  have hsurj : Function.Surjective q := by
    have hc : IsClosed (Set.range q) := q.isClosedMap.isClosed_range
    have hg : genericPoint M.Z ∈ Set.range q := by
      have w : Sp Ω := IsLocalRing.closedPoint Ω
      refine ⟨Y.pt w, ?_⟩
      have h1 : (Y.pt ≫ q) w = (spMap (AlgHom.id o Ω).toRingHom ≫ M.pt) w := by rw [hq']
      rw [Scheme.Hom.comp_apply, Scheme.Hom.comp_apply, M.pt_apply] at h1
      exact h1
    intro z
    exact (genericPoint_specializes z).mem_closed hc hg
  obtain ⟨K', _, σ, y₁, hσ, hy₁⟩ := exists_finite_ext_point_lift_of_surjective_lft q inferInstance hsurj
    (PadicAlgCl p) (gPt p ≫ y)
  have hbij : Function.Bijective σ := by
    letI := σ.toAlgebra
    haveI : Module.Finite (PadicAlgCl p) K' := hσ
    exact IsAlgClosed.algebraMap_bijective_of_isIntegral (k := PadicAlgCl p) (K := K')
  let e := RingEquiv.ofBijective σ hbij
  have he : e.symm.toRingHom.comp σ = RingHom.id _ := RingHom.ext fun x => e.symm_apply_apply x
  have h2 : (spMap e.symm.toRingHom ≫ y₁) ≫ q = gPt p ≫ y := by
    rw [Category.assoc, hy₁, ← Category.assoc, ← ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap_comp, he]
    have : spMap (RingHom.id (PadicAlgCl p)) = 𝟙 _ := Spec.map_id _
    rw [this, Category.id_comp]
  have hE : ValuativeCriterion.Existence q :=
    (UniversallyClosed.eq_valuativeCriterion ▸ (inferInstance : UniversallyClosed q) :
      (ValuativeCriterion.Existence ⊓ @QuasiCompact) q).1
  obtain ⟨⟨l⟩⟩ := hE
    { R := OO p, K := PadicAlgCl p, i₁ := spMap e.symm.toRingHom ≫ y₁, i₂ := y, commSq := ⟨h2⟩ }
  exact ⟨l.l, l.fac_right⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLiftOfLiftingObstructionEqZeroStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_lift_of_lifting_obstruction_eq_zero : ∀ (R R' R₀ : Type) [CommRing R] [CommRing R'] [CommRing R₀] (t : R) (σ : R →+* R') (σ₀ : R →+* R₀) (X X' X₀ : Scheme.{0}) (s : X ⟶ Sp R) (s' : X' ⟶ Sp R') (s₀ : X₀ ⟶ Sp R₀) (φ : X' ⟶ X) (φ₀ : X₀ ⟶ X) (h : IsPullback φ s' s (spMap σ)) (h₀ : IsPullback φ₀ s₀ s (spMap σ₀)), SmallExt t σ σ₀ → Flat s → ∀ x : HO1 s', Bock h.w h₀.w t x 0 → ∃ y : HO1 s, pullHO1 h.w y = x := by
  first | exact @GlobalTheory.AbCoh.exists_lift_of_bock_zero | exact GlobalTheory.AbCoh.exists_lift_of_bock_zero | (intros; apply GlobalTheory.AbCoh.exists_lift_of_bock_zero <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocalHolomorphicExtensionNearZerosStatement
section
open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_local_holomorphic_extension_near_zeros : ∀ (n : ℕ) (Y : Type) [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] [CompactSpace Y] (ι La : Type) [AddCommGroup La] (A : WeightedAtlas n Y ι La), 1 ≤ n → ∀ (E L : La) (s : Fin n → ι → Y → ℂ), (∀ k, A.IsSec L (s k)) → ∀ hS : (A.zeroSet s).Finite, (∀ P ∈ A.zeroSet s, jacAt A s P ≠ 0) → ∀ (f : Y → ℂ) (δ : ℝ), 0 < δ → ∃ (Ω : Set Y) (h : ι → Y → ℂ) (m : ℝ), (IsOpen Ω ∧ A.IsSecOn (A.kap + E) Ω h ∧ (∀ i y, y ∉ Ω → h i y = 0)) ∧ 0 < m ∧ (∀ y, A.sqn L s y < m → y ∈ Ω) ∧ (∀ P ∈ A.zeroSet s, h (A.pick P) P = f P) ∧ (∀ T : ℝ, 2 ≤ T → ∫⁻ y in {y | -T - 1 ≤ δ * psi A L s y ∧ δ * psi A L s y ≤ -T + 1}, ENNReal.ofReal (A.nsq (A.kap + E) h y * Real.exp (-psi A L s y)) ∂A.mu ≤ ENNReal.ofReal (62 / 30 * (Real.pi ^ n / ((n - 1).factorial : ℝ)) / δ * ∑ P ∈ hS.toFinset, resSq A E L s P (f P))) ∧ ∫⁻ y, ENNReal.ofReal (1 / (1 + (δ * psi A L s y) ^ 2) * A.nsq (A.kap + E) h y * Real.exp (-psi A L s y)) ∂A.mu < ⊤ := by
  first | exact @GlobalTheory.OTY.exists_local_extension | exact GlobalTheory.OTY.exists_local_extension | (intros; apply GlobalTheory.OTY.exists_local_extension <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocalHomToStrictlyHenselianNormalStatement
section
open IsLocalRing Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_local_hom_to_strictly_henselian_normal : ∀ (T : Type) [CommRing T] [IsDomain T] [IsLocalRing T], GlobalTheory.LocAcyc.AbsIntClosed T →
    ∀ (A : Type) [CommRing A] [IsDomain A] [IsLocalRing A] [IsNoetherianRing A] [IsIntegrallyClosed A]
      (i : A →+* T), IsLocalHom i →
    ∃ (A' : Type) (_ : CommRing A') (_ : IsDomain A') (_ : HenselianLocalRing A')
      (_ : IsSepClosed (ResidueField A')) (_ : IsNoetherianRing A') (_ : IsIntegrallyClosed A')
      (ι : A →+* A') (α : A' →+* T), α.comp ι = i ∧ IsLocalHom α := by
  first | (exact @GlobalTheory.exists_strictlyHenselian_normal_between) | (exact GlobalTheory.exists_strictlyHenselian_normal_between) | (intros; apply GlobalTheory.exists_strictlyHenselian_normal_between  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocalHormanderIterationStep
section
open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff

namespace GlobalTheory

theorem hormander_step : ∀ (n : ℕ) (Y : Type) [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] (ι La : Type) [AddCommGroup La] (A : WeightedAtlas n Y ι La), ∀ C : Cover A, ∃ K : ℝ, 0 ≤ K ∧ ∀ (la : La) (t : ℝ), 0 < t → CurvGe C la t → ∀ F0 : ι → Y → ℂ, A.IsSSec (A.kap + la) F0 → ∃ F1 : ι → Y → ℂ, A.IsSSec (A.kap + la) F1 ∧ n0 A la (F0 - F1) ≤ ENNReal.ofReal (K / t) * n1 C la F0 ∧ n1 C la F1 ≤ ENNReal.ofReal (K / t) * n1 C la F0 := by
  intro n Y _ _ _ _ _ ι La _ A C
  obtain ⟨K', hK'0, hK'⟩ := GlobalTheory.T.dbar_energy_glued_section_le n Y ι La A C
  refine ⟨max (C.m : ℝ) K', le_max_of_le_right hK'0, ?_⟩
  intro la t ht hcurv F0 hF0
  have hball : ∀ a : Fin C.m, ∃ F : V n → ℂ, DifferentiableOn ℂ F (ball (C.c a) (C.r a)) ∧
      ∫⁻ v in ball (C.c a) (C.r a), ENNReal.ofReal (‖F0 (C.idx a) ((A.chart (C.idx a)).symm v) - F v‖ ^ 2 *
        Real.exp (-A.ph la (C.idx a) ((A.chart (C.idx a)).symm v))) ≤
      ENNReal.ofReal t⁻¹ * ∫⁻ v in ball (C.c a) (C.r a), ENNReal.ofReal
        ((∑ j, ‖wdb n j (F0 (C.idx a) ∘ (A.chart (C.idx a)).symm) v‖ ^ 2) *
          Real.exp (-A.ph la (C.idx a) ((A.chart (C.idx a)).symm v))) := by
    intro a
    have hsub : ball (C.c a) (C.r a) ⊆ (A.chart (C.idx a)).target :=
      ball_subset_closedBall.trans (C.sub a)
    refine GlobalTheory.T.hormander_estimate_on_ball_const_levi_bound n (C.c a) (C.r a) t (fun w => A.ph la (C.idx a) ((A.chart (C.idx a)).symm w))
      (F0 (C.idx a) ∘ (A.chart (C.idx a)).symm) ht ((A.smooth_ph la (C.idx a)).mono hsub)
      ((hF0.1 (C.idx a)).mono hsub) ?_
    intro v hv ξ
    have h := hcurv a v hv ξ
    unfold WeightedAtlas.leviAt at h
    rwa [(A.chart (C.idx a)).right_inv (hsub hv)] at h
  choose u hu hE using hball
  have hsum := Finset.sum_le_sum (fun a (_ : a ∈ Finset.univ) => hE a)
  rw [← Finset.mul_sum] at hsum
  have hK : ENNReal.ofReal (max (C.m : ℝ) K' / t) =
      ENNReal.ofReal (max (C.m : ℝ) K') * ENNReal.ofReal t⁻¹ := by
    rw [div_eq_mul_inv, ENNReal.ofReal_mul (le_max_of_le_right hK'0)]
  refine ⟨glue C la u, GlobalTheory.T.isSSec_glueSectionByPartition_of_holo n Y ι La A C la u hu, ?_, ?_⟩
  · have hm : (C.m : ℝ≥0∞) ≤ ENNReal.ofReal (max (C.m : ℝ) K') := by
      rw [← ENNReal.ofReal_natCast]; exact ENNReal.ofReal_le_ofReal (le_max_left _ _)
    calc n0 A la (F0 - glue C la u) ≤ _ := GlobalTheory.T.n0_sub_glue_le_card_mul_sum_lintegral n Y ι La A C la F0 u hF0 hu
      _ ≤ (C.m : ℝ≥0∞) * (ENNReal.ofReal t⁻¹ * n1 C la F0) := by gcongr; exact hsum
      _ ≤ ENNReal.ofReal (max (C.m : ℝ) K') * (ENNReal.ofReal t⁻¹ * n1 C la F0) := by gcongr
      _ = _ := by rw [hK, mul_assoc]
  · calc n1 C la (glue C la u) ≤ _ := hK' la F0 u hF0 hu
      _ ≤ ENNReal.ofReal K' * (ENNReal.ofReal t⁻¹ * n1 C la F0) := by gcongr; exact hsum
      _ ≤ ENNReal.ofReal (max (C.m : ℝ) K') * (ENNReal.ofReal t⁻¹ * n1 C la F0) := by
        gcongr; exact le_max_right _ _
      _ = _ := by rw [hK, mul_assoc]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNeZeroCoindIntertwinerOfDoubleCoset
section
open Formalism.L2.DIV GlobalTheory.FinGL GlobalTheory.Parabolic GlobalTheory.IndefiniteRowSideFullHecke.BlockProductIsomorphism

namespace GlobalTheory

theorem exists_ne_zero_intertwiningMap_coind_of_doubleCoset :
    ∀ (G : Type) [Group G] [Finite G] (P P' : Subgroup G) (V V' : Type) [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V'] (σ : Representation ℂ P V) (σ' : Representation ℂ P' V') (x : G) (T : V →ₗ[ℂ] V'), T ≠ 0 → (∀ (p : P) (p' : P'), (p' : G) * x = x * (p : G) → σ' p' ∘ₗ T = T ∘ₗ σ p) → ∃ Φ : Representation.IntertwiningMap (Representation.coind P.subtype σ) (Representation.coind P'.subtype σ'), Φ ≠ 0 := by
  intro G _ _ P P' V V' _ _ _ _ σ σ' x T hT h
  classical
  haveI : Fintype P' := Fintype.ofFinite _
  let L : Representation.coindV P.subtype σ →ₗ[ℂ] Representation.coindV P'.subtype σ' :=
    { toFun := fun f => ⟨fun y => ∑ p' : P', σ' p' (T (f.1 (x⁻¹ * (p' : G)⁻¹ * y))), by
        intro q y
        beta_reduce
        rw [map_sum, ← Equiv.sum_comp (Equiv.mulLeft q)
          (fun p' : P' => σ' p' (T (f.1 (x⁻¹ * (p' : G)⁻¹ * (P'.subtype q * y)))))]
        refine Finset.sum_congr rfl fun p' _ => ?_
        simp [mul_assoc]⟩
      map_add' := fun f g => by
        ext y
        simp [Finset.sum_add_distrib]
      map_smul' := fun c f => by
        ext y
        simp [Finset.smul_sum] }
  have hL : ∀ f y, (L f).1 y = ∑ p' : P', σ' p' (T (f.1 (x⁻¹ * (p' : G)⁻¹ * y))) :=
    fun _ _ => rfl
  refine ⟨⟨L, fun g => ?_⟩, fun h0 => ?_⟩
  · ext f y
    change (L (Representation.coind P.subtype σ g f)).1 y = (L f).1 (y * g)
    rw [hL, hL]
    refine Finset.sum_congr rfl fun p' _ => ?_
    change σ' p' (T (f.1 (x⁻¹ * (p' : G)⁻¹ * y * g))) = _
    rw [mul_assoc _ y g]
  · obtain ⟨v, hv⟩ : ∃ v, T v ≠ 0 := by
      by_contra hc
      push Not at hc
      exact hT (LinearMap.ext hc)
    let δ : Representation.coindV P.subtype σ :=
      ⟨fun y => if hy : y ∈ P then σ ⟨y, hy⟩ v else 0, by
        intro q y
        by_cases hy : y ∈ P
        · have hqy : P.subtype q * y ∈ P := P.mul_mem q.2 hy
          simp only [dif_pos hy, dif_pos hqy]
          rw [← Module.End.mul_apply, ← map_mul]
          rfl
        · have hqy : P.subtype q * y ∉ P := fun hh => hy ((P.mul_mem_cancel_left q.2).1 hh)
          simp only [dif_neg hy, dif_neg hqy, map_zero]⟩
    have hL0 : L = 0 := congrArg Representation.IntertwiningMap.toLinearMap h0
    have h1 : (L δ).1 x = 0 := by rw [hL0]; rfl
    have h2 : ∀ p' : P', σ' p' (T (δ.1 (x⁻¹ * (p' : G)⁻¹ * x))) =
        if x⁻¹ * (p' : G)⁻¹ * x ∈ P then T v else 0 := by
      intro p'
      by_cases hp : x⁻¹ * (p' : G)⁻¹ * x ∈ P
      · have hδ : δ.1 (x⁻¹ * (p' : G)⁻¹ * x) = σ ⟨_, hp⟩ v := dif_pos hp
        have := LinearMap.congr_fun (h ⟨_, hp⟩ p'⁻¹ (by simp [mul_assoc])) v
        simp only [LinearMap.comp_apply] at this
        rw [hδ, if_pos hp, ← this, ← Module.End.mul_apply, ← map_mul]
        simp
      · have hδ : δ.1 (x⁻¹ * (p' : G)⁻¹ * x) = 0 := dif_neg hp
        rw [hδ, if_neg hp]
        simp
    rw [hL, Finset.sum_congr rfl fun p' _ => h2 p', ← Finset.sum_filter, Finset.sum_const,
      ← Nat.cast_smul_eq_nsmul ℂ, smul_eq_zero] at h1
    rcases h1 with h1 | h1
    · have : (1 : P') ∈ Finset.univ.filter fun p' : P' => x⁻¹ * (p' : G)⁻¹ * x ∈ P := by
        simp [P.one_mem]
      exact (Finset.card_pos.2 ⟨_, this⟩).ne' (Nat.cast_eq_zero.1 h1)
    · exact hv h1

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNoetherianShFactor
section
open GlobalTheory.EtC IsLocalRing

namespace GlobalTheory.NoethSHFactor

theorem exists_noetherian_sh_factor : ∀ (R A : Type) [CommRing R] [IsNoetherianRing R] [CommRing A], SH A →
    ∀ b : R →+* A, ∃ (C : Type) (_ : CommRing C), IsNoetherianRing C ∧ SH C ∧
      ∃ (f : R →+* C) (g : C →+* A), g.comp f = b := by
  intro R A _ _ _ hA b
  obtain ⟨hH, hsep⟩ := hA
  let p : Ideal R := (maximalIdeal A).comap b
  haveI : p.IsPrime := Ideal.comap_isPrime _ _
  let Rp := Localization.AtPrime p
  have hunit : ∀ y : p.primeCompl, IsUnit (b y) := by
    intro y
    by_contra h
    exact y.2 ((mem_maximalIdeal _).2 h)
  let b' : Rp →+* A := IsLocalization.lift (M := p.primeCompl) hunit
  have hb' : b'.comp (algebraMap R Rp) = b := IsLocalization.lift_comp hunit
  letI : Algebra Rp A := b'.toAlgebra
  haveI hloc : IsLocalHom (algebraMap Rp A) := by
    refine ⟨fun x hx => ?_⟩
    obtain ⟨⟨r, s⟩, rfl⟩ := IsLocalization.mk'_surjective p.primeCompl x
    rw [IsLocalization.AtPrime.isUnit_mk'_iff]
    intro hr
    have h1 : IsLocalization.mk' Rp r s * algebraMap R Rp s = algebraMap R Rp r :=
      IsLocalization.mk'_spec Rp r s
    have h2 : IsUnit (b r) := by
      rw [← hb', RingHom.comp_apply, ← h1, map_mul]
      exact hx.mul (by rw [← RingHom.comp_apply, hb']; exact hunit s)
    exact (mem_maximalIdeal _).1 hr h2
  obtain ⟨D, _, _, _, c, w, hwc, P, _, φ, hφ, hφc, -⟩ :=
    GlobalTheory.StrictHensFactor.exists_factor_strictHenselisation Rp Rp A (Algebra.ofId Rp A)
  haveI : IsNoetherianRing Rp := IsLocalization.isNoetherianRing p.primeCompl Rp inferInstance
  haveI : IsNoetherianRing (Localization.AtPrime P) :=
    IsLocalization.isNoetherianRing P.primeCompl _ inferInstance
  letI : Algebra (Localization.AtPrime P) D := φ.toAlgebra
  have hD : IsNoetherianRing D :=
    GlobalTheory.StalkNoeth.isNoetherianRing_of_indEt (Localization.AtPrime P) D hφ.2.2.2
  refine ⟨D, inferInstance, hD, ⟨hφ.1, hφ.2.1⟩, (c : Rp →+* D).comp (algebraMap R Rp), (w : D →+* A), ?_⟩
  rw [← RingHom.comp_assoc]
  have : (w : D →+* A).comp (c : Rp →+* D) = b' := by
    ext x
    exact DFunLike.congr_fun hwc x
  rw [this, hb']

end GlobalTheory.NoethSHFactor
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPerfectIdempotentStatement
section
open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_idempotent_nilpotent_complement_of_perfect : ∀ (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] [PerfectRing k p] (G : PDivGroup p k), ∃ e : G ⟶ G, e ≫ e = e ∧ (∀ (n : ℕ) (a : G.A n), IsNilpotent (a - e.app n a)) ∧ ∀ (n : ℕ) (a : G.A n), IsNilpotent (e.app n a) → e.app n a = 0 := by
  first | exact @GlobalTheory.PDivGroup.exists_perfect_idempotent | exact GlobalTheory.PDivGroup.exists_perfect_idempotent | (intros; apply GlobalTheory.PDivGroup.exists_perfect_idempotent <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPermMatrixRepParabolicDoubleCoset
section
open Formalism.L2.DIV GlobalTheory.FinGL GlobalTheory.Parabolic GlobalTheory.IndefiniteRowSideFullHecke.BlockProductIsomorphism

namespace GlobalTheory.FinGL.Bruhat

theorem exists_perm_rep_blockTri : ∀ (F : Type) [Field F] (r : ℕ) (b b' : Fin r → ℕ), Monotone b → Monotone b' → ∀ g : GL (Fin r) F, ∃ (w : Equiv.Perm (Fin r)) (p' : blockTri (κ := F) b') (p : blockTri (κ := F) b), g = (p' : GL (Fin r) F) * permGL F w * (p : GL (Fin r) F) := by
  intro F _ r b b' hb hb' g
  have hle : ∀ (c : Fin r → ℕ), Monotone c → ∀ u ∈ unip F r, u ∈ blockTri (κ := F) c := by
    intro c hc u hu
    rw [mem_blockTri]
    intro i j hij
    exact unip_lower hu (lt_of_not_ge fun h => absurd (hc h) (not_le.2 hij))
  obtain ⟨m, u, hu, u', hu', h⟩ := exists_decomp g
  have hdet : (Matrix.diagonal fun c => (m.2 c : F)).det ≠ 0 := by
    rw [Matrix.det_diagonal]
    exact Finset.prod_ne_zero_iff.2 fun c _ => (m.2 c).ne_zero
  let d : GL (Fin r) F := Matrix.GeneralLinearGroup.mkOfDetNeZero _ hdet
  have hdv : (d : Matrix (Fin r) (Fin r) F) = Matrix.diagonal fun c => (m.2 c : F) := rfl
  have hd : d ∈ blockTri (κ := F) b := by
    rw [mem_blockTri]
    intro i j hij
    rw [hdv]
    exact Matrix.diagonal_apply_ne _ (fun e => by rw [e] at hij; exact lt_irrefl _ hij)
  have hm : mono m = (permGL F m.1 : Matrix (Fin r) (Fin r) F) * (d : Matrix (Fin r) (Fin r) F) := by
    ext a c
    rw [hdv, Matrix.mul_diagonal, permGL_apply]
    by_cases e : a = m.1 c <;> simp [mono, e]
  refine ⟨m.1, ⟨u, hle b' hb' u hu⟩, ⟨d * u', Subgroup.mul_mem _ hd (hle b hb u' hu')⟩, Units.ext ?_⟩
  rw [h, hm]
  simp only [Units.val_mul, Matrix.mul_assoc]

end GlobalTheory.FinGL.Bruhat
end

