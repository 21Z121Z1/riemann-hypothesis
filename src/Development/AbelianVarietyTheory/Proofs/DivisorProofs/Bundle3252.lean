import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3233
import Development.AbelianVarietyTheory.Definitions.Divisors.IsRatioOfWeight
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0005
import Development.AbelianVarietyTheory.Definitions.Divisors.IsCyclotomicExtensionQI
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1005
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3219
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2830
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3238
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2884
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2921
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2890
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2937
import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle0001
import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle0002
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0263
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3225
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2901
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0542
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0030
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3125
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3135
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3224
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2139
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.NonemptyAlgHomOfIsRayOfDvd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3234
import Development.AbelianVarietyTheory.Definitions.Divisors.SubsetSpanBy
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProjOverWeierstrass
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3013
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3228
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3014
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0068
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0072
import Development.AbelianVarietyTheory.Definitions.Divisors.MulSmulIdemMem
import Development.AbelianVarietyTheory.Definitions.Divisors.WedgeNrmLeOfWedgeNormLe
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0057
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2341
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2219
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2281
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2197
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2209
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3222
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2369
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0363
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0062
import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SeriesRatSOf
import Development.AbelianVarietyTheory.Definitions.Divisors.LevelOfOfSameBut
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2083
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle1010
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2165
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2715

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonvanishingLocusAmpleSectionIsAffineModelStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSAmp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.nonvanishingLocus_ample_section_isAffine_model : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (P : Pair p), IsAmpleLB P.L.B → ∀ (e : ℕ) (g : X.functionField), 0 < e → g ∈ P.H e 0 → g ≠ 0 → ∃ (U : X.Opens) (h : genericPoint X ∈ U), (U : Set X) = NV P e 0 g ∧ IsAffineOpen U ∧ (∀ w : X.functionField, (∀ z ∈ U, RegAt z w) ↔ w ∈ (fnOf U h).range) ∧ Algebra.FiniteType ℤ (fnOf U h).range ∧ (∀ w : X.functionField, ∃ a ∈ (fnOf U h).range, ∃ b ∈ (fnOf U h).range, b ≠ 0 ∧ w = a / b) ∧ ∀ φ : (fnOf U h).range →+* ℂ, ∃ (σ : k →+* ℂ) (y : CxPts p σ), under y ∈ U ∧ ∀ w : (fnOf U h).range, ratVal (w : X.functionField) y = φ w := by
  first | exact @GlobalTheory.AffModel.main | exact GlobalTheory.AffModel.main | (intros; apply GlobalTheory.AffModel.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormBasepointFreeSectionsLeOneFubiniStudyStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSAmp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.norm_basepointFree_sections_le_one_fubiniStudy : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (P : Pair p), ∀ (e : ℕ) (x : Fin (D + 1) → X.functionField), Gens P D e x → ∀ (n : ℕ) (u : SmFn p), 1 ≤ n → IsCan P e n x u → (∀ l (σ : k →+* ℂ) (y : CxPts p σ), (upperParabolic P u).nu e 0 σ y (x l) ≤ 1) ∧ (∀ (σ : k →+* ℂ) (y : CxPts p σ), ∃ l, Real.exp (-(Real.log (D + 1) / (2 * n))) ≤ (upperParabolic P u).nu e 0 σ y (x l)) ∧ Gens (upperParabolic P u) D e x ∧ Gens P D (e * n) (fun l => x l ^ n) ∧ IsCan P (e * n) 1 (fun l => x l ^ n) u := by
  first | exact @GlobalTheory.HSAmp.canNorms | exact GlobalTheory.HSAmp.canNorms | (intros; apply GlobalTheory.HSAmp.canNorms <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PadicPointsSimilitudeGLProductBijective
section
open GlobalTheory.LKTrip
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.LKTrip.HTGroup.LocPBij

variable {p : ℕ} [Fact p.Prime] (G : HTGroup p)

theorem starT_starT (x : ℚ_[p] ⊗[ℚ] G.C) :
    (starT G.star ℚ_[p] (starT G.star ℚ_[p] x).unop).unop = x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a c => rw [starT_tmul, starT_tmul, G.star_star]
  | add x y hx hy => simp only [map_add, MulOpposite.unop_add, hx, hy]

theorem starT_algebraMap (a : ℚ_[p]) :
    (starT G.star ℚ_[p] (algebraMap ℚ_[p] (ℚ_[p] ⊗[ℚ] G.C) a)).unop = algebraMap ℚ_[p] (ℚ_[p] ⊗[ℚ] G.C) a := by
  rw [Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply, starT_tmul, map_one,
    MulOpposite.unop_one]

theorem starT_mul (x y : ℚ_[p] ⊗[ℚ] G.C) :
    (starT G.star ℚ_[p] (x * y)).unop = (starT G.star ℚ_[p] y).unop * (starT G.star ℚ_[p] x).unop := by
  rw [map_mul, MulOpposite.unop_mul]

def starL : ℚ_[p] ⊗[ℚ] G.C →ₗ[ℚ_[p]] ℚ_[p] ⊗[ℚ] G.C where
  toFun x := (starT G.star ℚ_[p] x).unop
  map_add' x y := by rw [map_add, MulOpposite.unop_add]
  map_smul' a x := by
    rw [Algebra.smul_def, starT_mul, starT_algebraMap, RingHom.id_apply, Algebra.smul_def]
    exact (Algebra.commutes _ _).symm

def psiL : ℚ_[p] ⊗[ℚ] G.C →ₗ[ℚ_[p]]
    ((i : Fin G.m) → Matrix (Fin G.n) (Fin G.n) (G.Fw i)) × ((i : Fin G.m) → Matrix (Fin G.n) (Fin G.n) (G.Fw i)) :=
  LinearMap.prod (LinearMap.pi fun i => (G.locW i).toLinearMap)
    ((LinearMap.pi fun i => (G.locW i).toLinearMap).comp (starL G))

theorem psiL_injective : Function.Injective (psiL G) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro x hx
  exact GlobalTheory.HTGroupLocInj.locW_inj G x (fun i => congrFun (congrArg Prod.fst hx) i)
    (fun i => congrFun (congrArg Prod.snd hx) i)

theorem finrank_eq : Module.finrank ℚ_[p] (ℚ_[p] ⊗[ℚ] G.C) = Module.finrank ℚ_[p]
    (((i : Fin G.m) → Matrix (Fin G.n) (Fin G.n) (G.Fw i)) × ((i : Fin G.m) → Matrix (Fin G.n) (Fin G.n) (G.Fw i))) := by
  rw [Module.finrank_baseChange, ← Module.finrank_mul_finrank ℚ G.F G.C, G.rankC, Module.finrank_prod,
    Module.finrank_pi_fintype]
  simp only [Module.finrank_matrix, Fintype.card_fin]
  rw [← HTGroup.two_mul_sum_finrank_Fw p G, ← Finset.mul_sum]
  ring

theorem psiL_bijective : Function.Bijective (psiL G) := by
  haveI : ∀ i, FiniteDimensional ℚ_[p] (Matrix (Fin G.n) (Fin G.n) (G.Fw i)) := fun i => inferInstance
  exact ⟨psiL_injective G,
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (finrank_eq G)).1 (psiL_injective G)⟩

end GlobalTheory.LKTrip.HTGroup.LocPBij

theorem GlobalTheory.LKTrip.HTGroup.bijective_locP : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p), Function.Bijective G.localization₂ := by
  intro p _ G
  have key : ∀ d : ℚ_[p] ⊗[ℚ] G.C, (starT G.star ℚ_[p] d).unop = d → (∀ i, G.locW i d = 0) → d = 0 :=
    fun d hd h0 => GlobalTheory.HTGroupLocInj.locW_inj G d h0 (fun i => by rw [hd]; exact h0 i)
  constructor
  · rintro ⟨⟨x, c⟩, hx⟩ ⟨⟨y, d⟩, hy⟩ h
    have hx' : (x : ℚ_[p] ⊗[ℚ] G.C) * (starT G.star ℚ_[p] x).unop = algebraMap ℚ_[p] _ (c : ℚ_[p]) := hx
    have hy' : (y : ℚ_[p] ⊗[ℚ] G.C) * (starT G.star ℚ_[p] y).unop = algebraMap ℚ_[p] _ (d : ℚ_[p]) := hy
    have hc : c = d := congrArg Prod.fst h
    subst hc
    have hu := fun i => congrFun (congrArg Prod.snd h) i
    have sx : (starT G.star ℚ_[p] x).unop = ((x⁻¹ : (ℚ_[p] ⊗[ℚ] G.C)ˣ) : ℚ_[p] ⊗[ℚ] G.C) * algebraMap ℚ_[p] _ (c : ℚ_[p]) := by
      rw [← hx', ← mul_assoc, Units.inv_mul, one_mul]
    have sy : (starT G.star ℚ_[p] y).unop = ((y⁻¹ : (ℚ_[p] ⊗[ℚ] G.C)ˣ) : ℚ_[p] ⊗[ℚ] G.C) * algebraMap ℚ_[p] _ (c : ℚ_[p]) := by
      rw [← hy', ← mul_assoc, Units.inv_mul, one_mul]
    have hw : ∀ i, G.locW i x = G.locW i y := fun i => congrArg Units.val (hu i)
    have hwi : ∀ i, G.locW i ((x⁻¹ : (ℚ_[p] ⊗[ℚ] G.C)ˣ) : ℚ_[p] ⊗[ℚ] G.C) = G.locW i ((y⁻¹ : (ℚ_[p] ⊗[ℚ] G.C)ˣ) : ℚ_[p] ⊗[ℚ] G.C) := by
      intro i
      have := congrArg (fun u => ((u⁻¹ : (Matrix (Fin G.n) (Fin G.n) (G.Fw i))ˣ) : Matrix (Fin G.n) (Fin G.n) (G.Fw i))) (hu i)
      exact this
    have hxy : x = y := by
      apply Units.ext
      apply GlobalTheory.LKTrip.HTGroup.LocPBij.psiL_injective G
      refine Prod.ext (funext hw) (funext fun i => ?_)
      show G.locW i (starT G.star ℚ_[p] x).unop = G.locW i (starT G.star ℚ_[p] y).unop
      rw [sx, sy, map_mul, map_mul, hwi]
    subst hxy
    rfl
  · rintro ⟨c, a⟩
    obtain ⟨x, hx⟩ := (GlobalTheory.LKTrip.HTGroup.LocPBij.psiL_bijective G).2
      (fun i => ((a i : GL (Fin G.n) (G.Fw i)) : Matrix (Fin G.n) (Fin G.n) (G.Fw i)),
       fun i => algebraMap ℚ_[p] (Matrix (Fin G.n) (Fin G.n) (G.Fw i)) (c : ℚ_[p]) *
        (((a i)⁻¹ : GL (Fin G.n) (G.Fw i)) : Matrix (Fin G.n) (Fin G.n) (G.Fw i)))
    have h1 : ∀ i, G.locW i x = a i := fun i => congrFun (congrArg Prod.fst hx) i
    have h2 : ∀ i, G.locW i (starT G.star ℚ_[p] x).unop = algebraMap ℚ_[p] (Matrix (Fin G.n) (Fin G.n) (G.Fw i)) (c : ℚ_[p]) *
        (((a i)⁻¹ : GL (Fin G.n) (G.Fw i)) : Matrix (Fin G.n) (Fin G.n) (G.Fw i)) := fun i => congrFun (congrArg Prod.snd hx) i
    have hyy := GlobalTheory.LKTrip.HTGroup.LocPBij.starT_starT G x
    have hxy : x * (starT G.star ℚ_[p] x).unop = algebraMap ℚ_[p] _ (c : ℚ_[p]) := by
      rw [← sub_eq_zero]
      apply key
      · rw [map_sub, MulOpposite.unop_sub, GlobalTheory.LKTrip.HTGroup.LocPBij.starT_mul, hyy,
          GlobalTheory.LKTrip.HTGroup.LocPBij.starT_algebraMap]
      · intro i
        rw [map_sub, map_mul, h1, h2, AlgHom.commutes, Algebra.left_comm, Units.mul_inv, mul_one, sub_self]
    have hyx : (starT G.star ℚ_[p] x).unop * x = algebraMap ℚ_[p] _ (c : ℚ_[p]) := by
      rw [← sub_eq_zero]
      apply key
      · rw [map_sub, MulOpposite.unop_sub, GlobalTheory.LKTrip.HTGroup.LocPBij.starT_mul, hyy,
          GlobalTheory.LKTrip.HTGroup.LocPBij.starT_algebraMap]
      · intro i
        rw [map_sub, map_mul, h1, h2, AlgHom.commutes, mul_assoc, Units.inv_mul, mul_one, sub_self]
    let u : (ℚ_[p] ⊗[ℚ] G.C)ˣ := ⟨x, algebraMap ℚ_[p] _ ((c⁻¹ : ℚ_[p]ˣ) : ℚ_[p]) * (starT G.star ℚ_[p] x).unop,
      by rw [Algebra.left_comm, hxy, ← map_mul, Units.inv_mul, map_one],
      by rw [mul_assoc, hyx, ← map_mul, Units.inv_mul, map_one]⟩
    refine ⟨⟨(u, c), hxy⟩, Prod.ext rfl (funext fun i => Units.ext (h1 i))⟩
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProductUniformisedGroupsUniformisedBySum
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Mum
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MumFam GlobalTheory.MumProd

namespace GlobalTheory.MumProdUnifSum

theorem main : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D₁ : DegData R (maximalIdeal R)) (A₁ : PolAV (Sp (FractionRing R))) (G₁ : Over (Sp R)) [GrpObj G₁] [IsCommMonObj G₁] (U₁ : Unif (maximalIdeal R) D₁ A₁ G₁) (D₂ : DegData R (maximalIdeal R)) (A₂ : PolAV (Sp (FractionRing R))) (G₂ : Over (Sp R)) [GrpObj G₂] [IsCommMonObj G₂] (U₂ : Unif (maximalIdeal R) D₂ A₂ G₂) (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (p₁ : D.toPre.P.A ⟶ D₁.toPre.P.A) (p₂ : D.toPre.P.A ⟶ D₂.toPre.P.A) (q₁ : D.toPre.X →+ D₁.toPre.X) (q₂ : D.toPre.X →+ D₂.toPre.X) (a₁ : A.A ⟶ A₁.A) (a₂ : A.A ⟶ A₂.A), IsSumDeg D.toPre D₁.toPre D₂.toPre p₁ p₂ q₁ q₂ → IsSumPolAV A A₁ A₂ a₁ a₂ → ∃ U : Unif (maximalIdeal R) D A (G₁ ⊗ G₂), GAdj U₁.LG.L U.LG.L (lift (𝟙 G₁) 1) (fst G₁ G₂) ∧ GAdj U₂.LG.L U.LG.L (lift 1 (𝟙 G₂)) (snd G₁ G₂) ∧ ∀ (i₁ : D₁.toPre.P.A ⟶ D.toPre.P.A) (i₂ : D₂.toPre.P.A ⟶ D.toPre.P.A) (j₁ : D₁.toPre.X →+ D.toPre.X) (j₂ : D₂.toPre.X →+ D.toPre.X), i₁ ≫ p₁ = 𝟙 _ → i₁ ≫ p₂ = toUnit _ ≫ η[D₂.toPre.P.A] → i₂ ≫ p₁ = toUnit _ ≫ η[D₁.toPre.P.A] → i₂ ≫ p₂ = 𝟙 _ → (∀ y, q₁ (j₁ y) = y) → (∀ y, q₂ (j₁ y) = 0) → (∀ y, q₁ (j₂ y) = 0) → (∀ y, q₂ (j₂ y) = y) → LinHom U₁.toUnifPre U.toUnifPre i₁ q₁ (lift (𝟙 G₁) 1) ∧ LinHom U.toUnifPre U₁.toUnifPre p₁ j₁ (fst G₁ G₂) ∧ LinHom U₂.toUnifPre U.toUnifPre i₂ q₂ (lift 1 (𝟙 G₂)) ∧ LinHom U.toUnifPre U₂.toUnifPre p₂ j₂ (snd G₁ G₂) := by
  intro R _ _ _ hB D₁ A₁ G₁ _ _ U₁ D₂ A₂ G₂ _ _ U₂ D A p₁ p₂ q₁ q₂ a₁ a₂ hD hA
  obtain ⟨U, hU⟩ := GlobalTheory.T.uniformisation_product_of_uniformisedGroups R hB D₁ A₁ G₁ U₁ D₂ A₂ G₂ U₂ D A p₁ p₂ q₁ q₂ a₁ a₂ hD hA
  refine ⟨U, GlobalTheory.MumProd.gAdj_prod_fst R _ D₁ A₁ G₁ U₁.toUnifPre D₂ A₂ G₂ U₂.toUnifPre D A U.toUnifPre p₁ p₂ q₁ q₂ a₁ a₂ hU,
    GlobalTheory.MumProd.SndAdj.gAdj_snd_of_isProdUnif R _ D₁ A₁ G₁ U₁.toUnifPre D₂ A₂ G₂ U₂.toUnifPre D A U.toUnifPre p₁ p₂ q₁ q₂ a₁ a₂ hU,
    fun i₁ i₂ j₁ j₂ h1 h2 h3 h4 h5 h6 h7 h8 => ⟨?_, hU.linHom_fst j₁ h5 h6, ?_, hU.linHom_snd j₂ h7 h8⟩⟩
  · exact GlobalTheory.MumProd.IsProdUnif.linHom_inl R _ D₁ A₁ G₁ U₁.toUnifPre D₂ A₂ G₂ U₂.toUnifPre D A U.toUnifPre p₁ p₂ q₁ q₂ a₁ a₂ hD hU i₁ h1 h2
  · exact GlobalTheory.MumProd.linHom_lift_one_id R _ D₁ A₁ G₁ U₁.toUnifPre D₂ A₂ G₂ U₂.toUnifPre D A U.toUnifPre p₁ p₂ q₁ q₂ a₁ a₂ hD hU i₂ h3 h4

end GlobalTheory.MumProdUnifSum
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.QeRingOfFiniteTypeInt
section
open IsLocalRing TensorProduct ReciprocityTheory.AnForm.R

namespace GlobalTheory

theorem qeRing_of_finiteType_int : ∀ (A : Type) [CommRing A] [Algebra.FiniteType ℤ A], FinalTheorems.QERing A := by
  intro A _ _
  have hN : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing ℤ A
  refine ⟨hN, fun P _ => ⟨?_, ?_⟩, fun B _ _ _ => ?_⟩
  · exact AdicCompletion.flat_of_isNoetherian _
  · apply GlobalTheory.T.geomRegFib_of_isRegularRing_tensor_essFiniteType
    intro K _ _ _
    haveI : Algebra.EssFiniteType A (Localization.AtPrime P) :=
      Algebra.EssFiniteType.of_isLocalization _ P.primeCompl
    haveI : Algebra.EssFiniteType ℤ (Localization.AtPrime P) :=
      Algebra.EssFiniteType.comp ℤ A (Localization.AtPrime P)
    have hZ : @Algebra.EssFiniteType ℤ (Localization.AtPrime P) _ _ (Ring.toIntAlgebra _) := by
      convert this
      exact Subsingleton.elim _ _
    exact @GlobalTheory.T.formalFibre_isRegularRing_essFiniteType_int (Localization.AtPrime P) K _ _ hZ _ _ _
  · haveI : Algebra.FiniteType ℤ B := Algebra.FiniteType.trans (inferInstance : Algebra.FiniteType ℤ A) ‹_›
    haveI : IsNoetherianRing B := Algebra.FiniteType.isNoetherianRing ℤ B
    exact GlobalTheory.T.isOpen_regularLocus_of_nagata' B (fun p _ => GlobalTheory.T.exists_regular_quotient_near_prime_finiteType_int B p)

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.QexpansionOnAllComponents
section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
  CartesianMonoidalCategory MonObj TensorProduct NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.RealMult

theorem qExpansionOnAll_of_model (hDP : GlobalTheory.Published.DelignePappasModel) (hQ : GlobalTheory.Published.HilbertQExpansion) :
    QExpansionOnAll := by
  intro F _ _ _ hf e 𝔞 𝔟 k R₀ g a hg ha haR
  obtain ⟨r₀, hr₀, hr₀u⟩ := hQ F hf e 𝔞 𝔟 k R₀ g a hg ha haR
  have hrap : ∀ (R : Type) [CommRing R] [Algebra ℂ R] (X : Obj F (𝔞 * 𝔟⁻¹) (Sp R)), X.IsRapoport := by
    intro R _ _ X
    apply isRapoport_of_isUnit_discr hDP F (𝔞 * 𝔟⁻¹) R
    have h0 : ((NumberField.discr F : ℤ) : R) = algebraMap ℂ R ((NumberField.discr F : ℤ) : ℂ) := by simp
    rw [h0]
    exact (IsUnit.mk0 _ (by exact_mod_cast NumberField.discr_ne_zero F)).map _
  let r₁ : Rule (trivialObjectCondition (𝔞 * 𝔟⁻¹)) ℂ k :=
    { val := fun R _ _ X _ δ ↦ (r₀.extend ℂ).val R X (hrap R X) δ
      homog := fun R _ _ X _ δ δ' c h ↦ (r₀.extend ℂ).homog R X (hrap R X) δ δ' c h
      baseChange := fun R R' _ _ _ _ σ X _ X' _ φ δ δ' h h' ↦
        (r₀.extend ℂ).baseChange R R' σ X (hrap R X) X' (hrap R' X') φ δ δ' h h' }
  obtain ⟨r, hr⟩ := exists_rule_allObj_of_extend hDP F (𝔞 * 𝔟⁻¹) R₀ ℂ Subtype.val_injective k r₀ r₁ (fun R _ _ X hX δ ↦ rfl)
  have hrr : r.HasValues e 𝔞 𝔟 g := by
    intro z hz X _ δ hXz
    rw [hr ℂ X (hrap ℂ X) δ]
    exact hr₀ z hz X (hrap ℂ X) δ hXz
  refine ⟨r, hrr, ?_⟩
  intro s hs
  have hres : ∀ t : Rule (trivialObjectCondition (𝔞 * 𝔟⁻¹)) R₀ k, t.HasValues e 𝔞 𝔟 g →
      (t.restrict (Q' := rapObj (𝔞 * 𝔟⁻¹)) (fun _ _ _ _ ↦ trivial)).HasValues e 𝔞 𝔟 g :=
    fun t ht z hz X _ δ hXz ↦ ht z hz X trivial δ hXz
  have h1 := hr₀u _ (hres s hs)
  have h2 := hr₀u _ (hres r hrr)
  apply rule_eq_of_agree_rapoport hDP F (𝔞 * 𝔟⁻¹) R₀ k s r
  intro R _ _ X hX δ
  exact congrArg (fun t : Rule (rapObj (𝔞 * 𝔟⁻¹)) R₀ k ↦ t.val R X hX δ) (h1.trans h2.symm)

end GlobalTheory.RealMult
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalSeriesOfReciprocityHypothesesStatement
section
open GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.BigOn.Exp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rational_series_of_reciprocity_hypotheses : GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.GlobalArtinReciprocity → GlobalTheory.Published.RayClassFieldSt → GlobalTheory.IndefiniteRowSideFullHecke.RationalRayLevels.SeriesRat → GlobalTheory.BigOn.Exp.SerRef := by
  first | exact @GlobalTheory.SerRefPt.serRef | exact GlobalTheory.SerRefPt.serRef | (intros; apply GlobalTheory.SerRefPt.serRef <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RaynaudLineBundleRelAmpleOfGenericSemiAbelianStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.raynaud_lineBundle_relAmple_of_generic_semiAbelian : ∀ (R : Type) [CommRing R] [IsRegularLocalRing R] [IsDomain R] [CharZero R], IsAdicComplete (maximalIdeal R) R → ∀ (G : Over (Sp R)) [GrpObj G], IsSemiAbelian G → IsAbelianScheme ((Over.pullback (jK R)).obj G) → ∀ L : LB G.left, L.IsLB → RelAmple ((Over.pullback (jK R)).obj G) (L.pull (pullback.fst G.hom (jK R))) → LBIso (L.pull (GrpObj.inv : G ⟶ G).left) L → IsAmpleLB L := by
  first | exact @GlobalTheory.AmpleGenericSemiAb.isAmpleLB_of_generic | exact GlobalTheory.AmpleGenericSemiAb.isAmpleLB_of_generic | (intros; apply GlobalTheory.AmpleGenericSemiAb.isAmpleLB_of_generic <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RecognitionDegDataLabelsAtEveryTrait
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum.Recognition

theorem pullDeg_induces : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (lab : Labels D.toPre A), ∀ n : ℕ, n.Prime → Odd n → IsUnit (n : R) → OneTrait D.toPre A lab → GalEqN n lab → ∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W], GlobalTheory.LN.CDvr W → ∀ (φ : R →+* W), Function.Injective φ → IsLocalHom φ → ∀ (G' : Over (Sp W)) [GrpObj G'] [IsCommMonObj G'] (D' : DegData W (maximalIdeal W)) (A' : PolAV (Sp (FractionRing W))) (U' : Unif (maximalIdeal W) D' A' G') (a : A'.A.left ⟶ A.A.left), IsSemiAbelian G' → IsFib φ A A' a → ∃ hD : IsPullDeg φ D.toPre D'.toPre, ∀ j : ℕ, Induces lab φ U' hD a (n ^ j) := by
  intro R _ _ _ hR D A lab n hn ho hu hOT hGal W _ _ _ hW φ hφ hloc G' _ _ D' A' U' a hG hF
  obtain ⟨hD, C, i1, i2, i3, i4, em, hc, hP⟩ := GlobalTheory.T.galois_equivariant_torsion_values_ultrametric R hR D A lab n hn ho hu hOT hGal
    (GlobalTheory.T.isThetaPoint_of_algebraic_series_one_trait R hR D A lab n hn ho hu hOT) W hW φ hφ hloc G' D' A' U' a hG hF
  exact ⟨hD, fun j => GlobalTheory.T.labels_induced_all_embeddings_of_galois R hR D A lab n hn ho hu hGal W hW φ hφ hloc G' D' A' U' a hG hF hD j
    ⟨C, i1, i2, i3, i4, em, hc, hP j⟩⟩

end GlobalTheory.Mum.Recognition
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ReferenceExponentPrimeBound
section
open GlobalTheory.IndefiniteRowSideFullHecke.DifferentConjugateDefects NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.FlatTw GlobalTheory.SlopeRec GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.RefSum
set_option synthInstance.maxHeartbeats 400000

namespace GlobalTheory.RefSum.WFree

theorem conj_eq_neg {z : ℂ} {d : ℕ} (hd : 0 < d) (h : z ^ 2 = -(d : ℂ)) : (starRingEnd ℂ) z = -z ∧ z ≠ 0 :=
  _root_.GlobalTheory.ClosingLemmaFourth.main hd h

theorem two_mul_sum_mult {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    (Dw : Datum H) : 2 * ∑ τ : E →+* ℂ, Dw.mult τ = Module.finrank ℚ E * (Dw.p + Dw.q) := by
  have key : ∀ τ : E →+* ℂ, Dw.mult τ + Dw.mult (ComplexEmbedding.conjugate τ) = Dw.p + Dw.q := fun τ => by
    have hs : τ (H.rt : E) ^ 2 = -(H.d : ℂ) := by
      have := congrArg (fun a : 𝓞 E => τ (a : E)) H.rt_sq
      simpa using this
    obtain ⟨h1, h2⟩ := conj_eq_neg H.d_prime.pos hs
    have h3 : ComplexEmbedding.conjugate τ (H.rt : E) = -τ (H.rt : E) := h1
    unfold Datum.mult
    rw [h3]
    by_cases h : τ (H.rt : E) = H.rt0
    · rw [if_pos h, if_neg fun e => h2 (by linear_combination (h - e) / 2)]
    · have : -τ (H.rt : E) = H.rt0 := by
        rcases sq_eq_sq_iff_eq_or_eq_neg.1 (hs.trans H.sqrt_neg_disc_sq.symm) with e | e
        · exact absurd e h
        · rw [e, neg_neg]
      rw [if_neg h, if_pos this, add_comm]
  have hinv : Function.Involutive (ComplexEmbedding.conjugate : (E →+* ℂ) → (E →+* ℂ)) := fun τ => star_star τ
  have e := Equiv.sum_comp hinv.toPerm Dw.mult
  rw [two_mul]
  nth_rewrite 2 [← e]
  rw [← Finset.sum_add_distrib]
  refine (Finset.sum_congr rfl fun τ _ => key τ).trans ?_
  rw [Finset.sum_const, Finset.card_univ, Embeddings.card, smul_eq_mul]

theorem one_le_vAdd {K : Type} [Field K] [NumberField K] (w : HeightOneSpectrum (𝓞 K)) {q : ℕ} (hq : q ≠ 0)
    (h : ((q : ℕ) : 𝓞 K) ∈ w.asIdeal) : 1 ≤ vAdd w (q : K) := by
  have h1 : w.valuation K (algebraMap (𝓞 K) K (q : 𝓞 K)) < 1 := (w.valuation_lt_one_iff_mem (K := K) _).2 h
  rw [map_natCast] at h1
  have h0 : w.valuation K (q : K) ≠ 0 := (Valuation.ne_zero_iff _).2 (Nat.cast_ne_zero.2 hq)
  have := WithZero.log_lt_log h0 one_ne_zero |>.2 h1
  rw [WithZero.log_one] at this
  unfold vAdd
  omega

theorem notMem_of_ne {K : Type} [Field K] [NumberField K] (w : HeightOneSpectrum (𝓞 K)) {p q : ℕ} (hp : p.Prime)
    (hq : q.Prime) (hne : p ≠ q) (h : ((q : ℕ) : 𝓞 K) ∈ w.asIdeal) : ((p : ℕ) : 𝓞 K) ∉ w.asIdeal := fun h' => by
  have hc : IsCoprime ((p : ℕ) : 𝓞 K) ((q : ℕ) : 𝓞 K) := ((Nat.coprime_primes hp hq).2 hne).cast
  obtain ⟨a, b, e⟩ := hc
  exact w.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 (e ▸ add_mem (Ideal.mul_mem_left _ _ h') (Ideal.mul_mem_left _ _ h)))

theorem different_vp_eq_zero {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    (l : Level H) {q : ℕ} (hq : q.Prime) (h : q ∉ badPrimes H l) : different_vp E q = 0 := by
  have : ¬ q ∣ (discr E).natAbs := fun hd => h (Nat.mem_primeFactors.2 ⟨hq, (hd.mul_left _).mul_right _,
    mul_ne_zero (mul_ne_zero (mul_ne_zero two_ne_zero H.d_prime.ne_zero) (Int.natAbs_ne_zero.2 (discr_ne_zero E)))
      (Nat.lcm_ne_zero (by have := l.three_le; omega) l.A_pos.ne')⟩)
  rw [different_vp, padicValNat.eq_zero_of_not_dvd this]
  simp

theorem refExp_vp_le_of_laws {E : Type} [Field E] [NumberField E] [IsCMField E] [IsGalois ℚ E]
    {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {r : ℕ}
    {U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r} {x : ℝ} (hL : GlobalTheory.FlatCore.Laws U x) (hN : UnramPts Xo c (badPrimes H l))
    (hF : FlatExists U x) (u : GlobalTheory.AllWt.Weight Dw) (w₀ : Psi H → ℤ) (m : ℕ) (cst : ℝ) {q : ℕ} (hq : q.Prime) {N : ℝ}
    (hs : ∑ τ : E →+* ℂ, (Dw.mult τ : ℝ) = N) :
    refExp_vp U cst (wtOf Dw u 0) q ≤ refExp_vp U cst (wtOf Dw (u + parWt Dw w₀) m) q +
      (((if q ∈ badPrimes H l then (m * N * (different_vp E q : ℝ) + 1) else 0 : ℝ)) : EReal) := by
  obtain ⟨hK, ht⟩ := GlobalTheory.T.exists_keySection_inverseRoot_twistingSection_spread E H Dw l Xo c r U hL.unf x hL.xi hL.geo hL.pos hL.good hN
  have hz : ∀ Z : Comp Xo c, ∃ z : TwSec U x Z (wtOf Dw u 0 - wtOf Dw (u + parWt Dw w₀) m),
      IntOff (badPrimes H l) z.lo ∧ ∀ w, z.hi w - z.lo w ≤
        m * ∑ τ : E →+* ℂ, (Dw.mult τ : ℝ) * (ord_vw w (conjDifferent (embF c τ)) : ℝ) := fun Z => by
    obtain ⟨t, ht1, ht2⟩ := ht Z
    obtain ⟨s, -, -, -, hs1, hs2⟩ := (GlobalTheory.FlatTwisting.twSec_of_flat E H Dw l Xo c r U x _ hK hL.unf hL.pos hN).1 Z (-w₀) _
      (FlatSec.shift (hasPts U hL.pos hL.good hL.unf Z) (fun τ => (hF.nonempty Z τ).some) (-w₀))
      ((Set.finite_iUnion fun τ => finite_flDefect_vw (Dw := Dw) (c := c) τ).subset fun w hw => by
        by_contra hn
        simp only [Set.mem_iUnion, Function.mem_support, not_exists, not_not] at hn
        exact hw (by simp [Finset.sum_apply, hn]))
    exact GlobalTheory.CombTw.exists_twSec_comb E H Dw l Xo c r U hL.unf x _ Z u w₀ m _ s t hs1 hs2 ht1 ht2
  choose z hz1 hz2 using hz
  have key := GlobalTheory.T.baseLocusExponent_twistingSection_mul_le E H Dw l Xo c r U hL.unf x (wtOf Dw (u + parWt Dw w₀) m) _ (even_two_mul (m : ℤ)) cst
    (if q ∈ badPrimes H l then (m * N * (different_vp E q : ℝ) + 1) else 0) q hq z fun Z w hw => by
      have h1 := hz2 Z w
      simp only [fun τ => (GlobalTheory.DifferentGalois.ord_conjDifferent_and_sum E c.F (embF c τ) q w hq hw).1, ← Finset.sum_mul, hs] at h1
      split_ifs with hb
      · have h2 : (1 : ℝ) ≤ (vAdd w (q : c.F) : ℝ) := by exact_mod_cast one_le_vAdd w hq.ne_zero hw
        have h3 := Int.lt_floor_add_one ((z Z).lo w)
        linarith
      · obtain ⟨n, hn⟩ := hz1 Z w fun p hp =>
          notMem_of_ne w (Nat.prime_of_mem_primeFactors hp) hq (fun e => hb (e ▸ hp)) hw
        rw [different_vp_eq_zero l hq hb, hn] at h1
        rw [hn, Int.floor_intCast]
        simpa using h1
  rwa [add_sub_cancel] at key

theorem refExp_vp_le_shift : Hypotheses2 → ∀ (D : D7) (T : CoreJ D) (j : ℕ) (Y : Deep T.toCore j) (e : ℕ) (o : ℝ), LawsJ T → InR D j → Y.Good e o → 1 ≤ (T.Q.Dw j).p → 1 ≤ (T.Q.Dw j).q → FlatExists Y.U (xiR D) → ∀ (u : GlobalTheory.AllWt.Weight (T.Q.Dw j)) (w₀ : Psi T.Q.H → ℤ) (m : ℕ) (cst : ℝ) (q : ℕ), q.Prime → refExp_vp Y.U cst (wtOf (T.Q.Dw j) u 0) q ≤ refExp_vp Y.U cst (wtOf (T.Q.Dw j) (u + parWt (T.Q.Dw j) w₀) m) q + (((if q ∈ badPrimes T.Q.H Y.d.l₂ then (m * (D.R.f * D.R.r) * (different_vp D.host.E q : ℝ) + 1) else 0 : ℝ)) : EReal) := by
  intro hP D T j Y e o hT hj hY _ _ hF u w₀ m cst q hq
  haveI : IsGalois ℚ D.host.E := D.host.hostE_isGalois
  have hL := GlobalTheory.T.complexUniformizationLaws_of_goodDeepCover D T j Y e o hT hj hY
  have hp := hT.pins
  have hr : (T.Q.Dw j).p + (T.Q.Dw j).q = D.R.r := by
    rw [(hp.2.2.2 j hj).1, (hp.2.2.2 j hj).2.1]
    have := hj.1; have := hj.2
    simp only [Ranks.sigW, Ranks.r]; omega
  have h2 := two_mul_sum_mult (T.Q.Dw j)
  rw [StandardLattice.finrank_host D, hr, mul_assoc] at h2
  exact refExp_vp_le_of_laws hL (GlobalTheory.T.hasUnramifiedIntegralFramedPoints_of_goodPlaces hP.q18 hP.q1 hP.p5 _ _ _ _ _ _ hL.pos) hF u w₀ m cst hq
    (by exact_mod_cast Nat.eq_of_mul_eq_mul_left two_pos h2)

end GlobalTheory.RefSum.WFree
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelAmplePrincipalPolarisationEveryFibreOfGeneratStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.relAmple_principal_polarisation_every_fibre_of_generate : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ U : Unif (maximalIdeal R) D A G, ∀ W : (Sp R).Opens, (∀ y, PsiUnitOn D.toPre y W) → ∀ (K : Type) [Field K] (x : Sp K ⟶ Sp R), Set.range x ⊆ (W : Set (Sp R)) → RelAmple ((Over.pullback x).obj G) (U.LG.L.pull (pullback.fst G.hom x)) ∧ KTriv ((Over.pullback x).obj G) (U.LG.L.pull (pullback.fst G.hom x)) := by
  first | exact @GlobalTheory.Mum.PolFibre.relAmple_kTriv_fibre | exact GlobalTheory.Mum.PolFibre.relAmple_kTriv_fibre | (intros; apply GlobalTheory.Mum.PolFibre.relAmple_kTriv_fibre <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RowStatementOfLowWeight
section
set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx
open Formalism.IndefR.FWT GlobalTheory.BigTop GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies GlobalTheory.SeriesTie GlobalTheory.BigOn GlobalTheory.BigOn.Exp

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.BigOn.Exp

theorem rowAt_of : GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.GlobalArtinReciprocity → GlobalTheory.Published.RayClassFieldSt →
    GlobalTheory.SerStd.SeriesRatS → LowAt → TwAdm → RowAt := by
  intro hP hA hR hS hL hT
  refine rowAt_of_ratStep ?_ (GlobalTheory.T.thetaSeries_base_twisted_universal_rational hA hR hS)
  exact AtTw.imp (AtTw.and hL hT) fun Fm x hx i p hp hM w _ j h =>
    GlobalTheory.T.exists_rational_data_realization hP Fm x hx i p hp hM _ j (ratHyp0_at_point Fm x hx i p hp hM _ h.2.2.2 h.1 j)

end GlobalTheory.BigOn.Exp
end
end

