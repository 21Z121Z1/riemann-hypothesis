import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0020
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsSmoothModerateOfIsAutFunSm
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0015
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsSquareIntegrableIffMemL2
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0610
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0049
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1236
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0024
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsRationalUnitaryDeterminantMapRationalUnitaryTo
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0104
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1254
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0705
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0019
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0013
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuasiCompactZeroSec
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1264
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0005
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsLocModelIsPrimeOf
import Development.AbelianVarietyTheory.Definitions.Divisors.NotDominatesTopPlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1263
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0005
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0288
import Development.AbelianVarietyTheory.Definitions.Divisors.DiagValExtTraceNonneg
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1265
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteWeilRepEqLatticeIntertwinerMulCharacter
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1104
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1266
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1241

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsScaledEmbeddingNormBoundHostField
section
open scoped Matrix NNReal ENNReal TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Proof.GNorm

theorem entry_bound {ι κ E : Type} [Fintype κ] [DecidableEq κ] [Ring E] {m n : ℕ}
    (σ : ι → E →+* ℂ) (T : Matrix κ (Fin m) E) (s : κ → ℝ) (hs : ∀ k, 0 < s k)
    (B : ι → Matrix (Fin m) (Fin m) ℂ)
    (hB : ∀ τ, T.map (σ τ) * B τ = Matrix.diagonal (fun k => ((s k : ℝ) : ℂ)⁻¹) * T.map (σ τ))
    (ξ : Matrix (Fin m) (Fin n) E) (τ : ι) (k : κ) (j : Fin n) :
    ‖σ τ ((T * ξ) k j)‖ / s k ≤ ∑ i, ‖T.map (σ τ) k i‖ * ‖(B τ * ξ.map (σ τ)) i j‖ := by
  have hmap : σ τ ((T * ξ) k j) = (T.map (σ τ) * ξ.map (σ τ)) k j := by
    rw [← Matrix.map_mul]; rfl
  have key : ((s k : ℝ) : ℂ)⁻¹ * σ τ ((T * ξ) k j) = (T.map (σ τ) * (B τ * ξ.map (σ τ))) k j := by
    rw [hmap, ← Matrix.mul_assoc, hB τ, Matrix.mul_assoc, Matrix.diagonal_mul]
  have hnorm : ‖σ τ ((T * ξ) k j)‖ / s k = ‖((s k : ℝ) : ℂ)⁻¹ * σ τ ((T * ξ) k j)‖ := by
    rw [norm_mul, norm_inv, Complex.norm_real, Real.norm_of_nonneg (hs k).le, div_eq_inv_mul]
  rw [hnorm, key, Matrix.mul_apply]
  refine (norm_sum_le _ _).trans (le_of_eq ?_)
  exact Finset.sum_congr rfl (fun i _ => norm_mul _ _)

theorem gnorm_gen {ι κ E : Type} [Fintype ι] [Fintype κ] [DecidableEq κ] [Ring E] (m n : ℕ)
    (σ : ι → E →+* ℂ) (T : Matrix κ (Fin m) E) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (s : κ → ℝ), (∀ k, 0 < s k) → ∀ B : ι → Matrix (Fin m) (Fin m) ℂ,
      (∀ τ, T.map (σ τ) * B τ = Matrix.diagonal (fun k => ((s k : ℝ) : ℂ)⁻¹) * T.map (σ τ)) →
      ∀ ξ : Matrix (Fin m) (Fin n) E,
        ∑ p : κ × Fin n, (∑ τ, ‖σ τ ((T * ξ) p.1 p.2)‖) / s p.1 ≤
          C * ∑ τ, ∑ i, ∑ j, ‖(B τ * ξ.map (σ τ)) i j‖ := by
  set c : ℝ := ∑ τ, ∑ k, ∑ i, ‖T.map (σ τ) k i‖ with hc
  have hc0 : 0 ≤ c := by positivity
  have hac : ∀ τ k i, ‖T.map (σ τ) k i‖ ≤ c := by
    intro τ k i
    have h1 : ‖T.map (σ τ) k i‖ ≤ ∑ i', ‖T.map (σ τ) k i'‖ :=
      Finset.single_le_sum (f := fun i' => ‖T.map (σ τ) k i'‖) (fun _ _ => norm_nonneg _) (Finset.mem_univ i)
    have h2 : ∑ i', ‖T.map (σ τ) k i'‖ ≤ ∑ k', ∑ i', ‖T.map (σ τ) k' i'‖ :=
      Finset.single_le_sum (f := fun k' => ∑ i', ‖T.map (σ τ) k' i'‖) (fun _ _ => by positivity) (Finset.mem_univ k)
    have h3 : ∑ k', ∑ i', ‖T.map (σ τ) k' i'‖ ≤ c :=
      Finset.single_le_sum (f := fun τ' => ∑ k', ∑ i', ‖T.map (σ τ') k' i'‖) (fun _ _ => by positivity) (Finset.mem_univ τ)
    linarith
  refine ⟨1 + Fintype.card κ * c, by nlinarith [hc0, (Nat.cast_nonneg (Fintype.card κ) : (0:ℝ) ≤ _)], ?_⟩
  intro s hs B hB ξ
  set b : ι → Fin m → Fin n → ℝ := fun τ i j => ‖(B τ * ξ.map (σ τ)) i j‖ with hb
  have hb0 : ∀ τ i j, 0 ≤ b τ i j := fun _ _ _ => norm_nonneg _
  have S0 : 0 ≤ ∑ τ, ∑ i, ∑ j, b τ i j := by positivity
  calc ∑ p : κ × Fin n, (∑ τ, ‖σ τ ((T * ξ) p.1 p.2)‖) / s p.1
      = ∑ p : κ × Fin n, ∑ τ, ‖σ τ ((T * ξ) p.1 p.2)‖ / s p.1 := by
        simp_rw [Finset.sum_div]
    _ ≤ ∑ p : κ × Fin n, ∑ τ, ∑ i, c * b τ i p.2 := by
        gcongr with p _ τ _
        refine (entry_bound σ T s hs B hB ξ τ p.1 p.2).trans ?_
        gcongr with i _
        exact hac τ p.1 i
    _ = ∑ _k : κ, ∑ j : Fin n, ∑ τ, ∑ i, c * b τ i j := by
        rw [Fintype.sum_prod_type]
    _ = Fintype.card κ * (c * ∑ j, ∑ τ, ∑ i, b τ i j) := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        simp only [Finset.mul_sum]
    _ = Fintype.card κ * c * ∑ τ, ∑ i, ∑ j, b τ i j := by
        rw [mul_assoc]
        congr 2
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl (fun τ _ => ?_)
        rw [Finset.sum_comm]
    _ ≤ (1 + Fintype.card κ * c) * ∑ τ, ∑ i, ∑ j, b τ i j := by nlinarith

end GlobalTheory.Proof.GNorm

namespace GlobalTheory

theorem tGnorm : ∀ (D : D7) (κ : Type) [Fintype κ] [DecidableEq κ] (m n : ℕ) (T : Matrix κ (Fin m) D.host.E), ∃ C : ℝ, 1 ≤ C ∧ ∀ (s : κ → ℝ), (∀ k, 0 < s k) → ∀ B : D.what₂.Tau → Matrix (Fin m) (Fin m) ℂ, (∀ τ, T.map (tauE D τ) * B τ = Matrix.diagonal (fun k => ((s k : ℝ) : ℂ)⁻¹) * T.map (tauE D τ)) → ∀ ξ : Matrix (Fin m) (Fin n) D.host.E, ∑ p : κ × Fin n, (∑ τ, ‖tauE D τ ((T * ξ) p.1 p.2)‖) / s p.1 ≤ C * ∑ τ, ∑ i, ∑ j, ‖(B τ * ξ.map (tauE D τ)) i j‖ := by
  intro D κ _ _ m n T
  exact GlobalTheory.Proof.GNorm.gnorm_gen m n (tauE D) T

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSecondKindCoordinatesUnitaryArchimedeanPla
section
open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut Filter Topology
open scoped TensorProduct ContDiff

namespace GlobalTheory.UAut

theorem exists_coordSecondKind_arch : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J →
    ∀ w : InfinitePlace F, ∃ (d : ℕ) (η : Fin d → ℝ → GAd σ J) (s : GArch σ J w → Fin d → ℝ),
      (∀ i, IsRealLine σ J (η i)) ∧ Tendsto s (𝓝 1) (𝓝 0) ∧
        ∀ᶠ y in 𝓝 1, embArch σ J w y = (List.ofFn fun i => η i (s y i)).prod := by
  intro F E _ _ _ _ _ σ h n J hJ w
  obtain ⟨τ⟩ : Nonempty (EmbOver E w) := inferInstance
  set A : Matrix (Fin n) (Fin n) ℂ := J.map τ.1 with hA
  obtain ⟨d, Z, s₀, hZ, hs, hev⟩ := GlobalTheory.T.coordsSecondKind_formPreservingGroup n A
  have hd : IsUnit A.det := by
    rw [hA, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
    exact (IsUnit.mk0 _ hJ.2).map _

  have hy : ∀ (i : Fin d) (t : ℝ), ∃ y : GArch σ J w, GlobalTheory.Orb.archMat σ J τ y = NormedSpace.exp (t • Z i) := by
    intro i t
    obtain ⟨u, hu⟩ := Matrix.isUnit_exp (t • Z i)
    have h1 := GlobalTheory.SmoothForms.exp_mem_UH (X := t • Z i) hd (by
      rw [conjTranspose_smul, star_trivial, Matrix.smul_mul, Matrix.mul_smul, ← smul_add, hZ i, smul_zero])
    refine ⟨(archEquiv J h τ).symm ⟨u, show _ * _ * _ = _ from hu ▸ h1⟩, ?_⟩
    rw [GlobalTheory.Orb.archMat_eq_archEquiv J h, MulEquiv.apply_symm_apply]
    exact hu
  choose y hy using hy

  have hS : ∀ g : GArch σ J w, GlobalTheory.Orb.archMat σ J τ g ∈ {X : Matrix (Fin n) (Fin n) ℂ | Xᴴ * A * X = A} := by
    intro g
    have := (archEquiv J h τ g).2
    rw [Set.mem_ofPred_eq, GlobalTheory.Orb.archMat_eq_archEquiv J h]
    exact this
  have hc : Tendsto (GlobalTheory.Orb.archMat σ J τ) (𝓝 1) (𝓝[{X : Matrix (Fin n) (Fin n) ℂ | Xᴴ * A * X = A}] 1) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, Eventually.of_forall hS⟩
    simpa using (GlobalTheory.Orb.continuous_archMat σ J τ).tendsto 1
  have hinj : Function.Injective (GlobalTheory.Orb.archMat σ J τ) := fun a b e =>
    (GlobalTheory.Orb.isEmbedding_archMat J h τ).injective (by
      show (fun i j => GlobalTheory.Orb.archMat σ J τ a i j) = fun i j => GlobalTheory.Orb.archMat σ J τ b i j
      rw [e])
  refine ⟨d, fun i t => embArch σ J w (y i t), fun g => s₀ (GlobalTheory.Orb.archMat σ J τ g),
    fun i => ⟨w, τ, Z i, hZ i, fun t => ⟨y i t, rfl, hy i t⟩⟩, hs.comp hc, ?_⟩
  filter_upwards [hc.eventually hev] with g hg
  have e1 : (List.ofFn fun i => embArch σ J w (y i (s₀ (GlobalTheory.Orb.archMat σ J τ g) i))).prod =
      embArch σ J w (List.ofFn fun i => y i (s₀ (GlobalTheory.Orb.archMat σ J τ g) i)).prod := by
    rw [map_list_prod, List.map_ofFn]; rfl
  rw [e1]
  congr 1
  apply hinj
  rw [map_list_prod, List.map_ofFn]
  refine hg.trans ?_
  congr 1
  exact List.ofFn_inj.2 (funext fun i => (hy i _).symm)

end GlobalTheory.UAut
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSplitPlaceBelowCMField
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.SplitPlaceExists

theorem exists_isSplitAt : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E],
    ∃ w : HeightOneSpectrum (𝓞 E), GlobalTheory.UnitaryBC.IsSplitAt w := by
  intro E _ _ _
  obtain ⟨p, hp, hsplit⟩ := GlobalTheory.SplitRealPrime.exists_prime_isSplitAt E

  have hP : (Ideal.span {(p : ℤ)}).IsMaximal :=
    PrincipalIdealRing.isMaximal_of_irreducible (Nat.prime_iff_prime_int.mp hp).irreducible

  obtain ⟨Q, hQmax, hQ⟩ := Ideal.exists_ideal_over_maximal_of_isIntegral (S := 𝓞 E)
    (Ideal.span {(p : ℤ)}) (by
      intro x hx
      rw [RingHom.mem_ker] at hx
      have : x = 0 := (FaithfulSMul.algebraMap_injective ℤ (𝓞 E)) (by rw [hx, map_zero])
      rw [this]
      exact Ideal.zero_mem _)
  have hpQ : ((p : ℕ) : 𝓞 E) ∈ Q := by
    have h1 : ((p : ℤ)) ∈ Q.comap (algebraMap ℤ (𝓞 E)) := by
      rw [hQ]
      exact Ideal.subset_span rfl
    rw [Ideal.mem_comap] at h1
    simpa using h1

  have hQ0 : Q ≠ ⊥ := Ideal.IsMaximal.ne_bot_of_isIntegral_int Q
  exact ⟨⟨Q, hQmax.isPrime, hQ0⟩, hsplit _ hpQ⟩

end GlobalTheory.SplitPlaceExists
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTranslationSqZeroPointsUnitToPoint
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh GlobalTheory.AbTan
attribute [local instance] Over.cartesianMonoidalCategory
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.AbTan.Transl

variable {R : Type} [CommRing R]

abbrev ovT (R : Type) [CommRing R] (B M : Type) [CommRing B] [Algebra R B] [AddCommGroup M] [Module B M]
    [Module Bᵐᵒᵖ M] [IsCentralScalar B M] : Over (Sp R) :=
  Over.mk (spMap ((TrivSqZeroExt.inlHom B M).comp (algebraMap R B)))

abbrev ovB (R : Type) [CommRing R] (B : Type) [CommRing B] [Algebra R B] : Over (Sp R) :=
  Over.mk (spMap (algebraMap R B))

theorem one_left (A : Over (Sp R)) [GrpObj A] (T : Over (Sp R)) : (1 : T ⟶ A).left = T.hom ≫ η[A].left := rfl

theorem inl_w (A : Over (Sp R)) {B M : Type} [CommRing B] [Algebra R B] [AddCommGroup M] [Module B M]
    [Module Bᵐᵒᵖ M] [IsCentralScalar B M] (P : Sp B ⟶ A.left) (hP : P ≫ A.hom = spMap (algebraMap R B)) :
    (spMap (TrivSqZeroExt.inlHom B M) ≫ P) ≫ A.hom = (ovT R B M).hom := by
  rw [Category.assoc, hP]
  exact (GlobalTheory.Cris.spMap_comp _ _).symm

theorem fst_w (B M : Type) [CommRing B] [Algebra R B] [AddCommGroup M] [Module B M]
    [Module Bᵐᵒᵖ M] [IsCentralScalar B M] :
    spMap (TrivSqZeroExt.fstHom B B M).toRingHom ≫ (ovT R B M).hom = (ovB R B).hom := by
  show _ ≫ spMap _ = spMap _
  rw [← GlobalTheory.Cris.spMap_comp]
  congr 1 <;> ext r <;> simp

theorem fst_inl (B M : Type) [CommRing B] [AddCommGroup M] [Module B M]
    [Module Bᵐᵒᵖ M] [IsCentralScalar B M] :
    spMap (TrivSqZeroExt.fstHom B B M).toRingHom ≫ spMap (TrivSqZeroExt.inlHom B M) = 𝟙 (Sp B) := by
  rw [← GlobalTheory.Cris.spMap_comp, ← GlobalTheory.Cris.spMap_id]
  congr 1 <;> ext r <;> simp

def eFst (B M : Type) [CommRing B] [Algebra R B] [AddCommGroup M] [Module B M]
    [Module Bᵐᵒᵖ M] [IsCentralScalar B M] : ovB R B ⟶ ovT R B M :=
  Over.homMk (spMap (TrivSqZeroExt.fstHom B B M).toRingHom) (fst_w B M)

open Classical in

def tau (A : Over (Sp R)) [GrpObj A] (B M : Type) [CommRing B] [Algebra R B] [AddCommGroup M] [Module B M]
    [Module Bᵐᵒᵖ M] [IsCentralScalar B M] (P : Sp B ⟶ A.left) (z : Sp (TrivSqZeroExt B M) ⟶ A.left) :
    Sp (TrivSqZeroExt B M) ⟶ A.left :=
  if h : P ≫ A.hom = spMap (algebraMap R B) ∧ z ≫ A.hom = (ovT R B M).hom then
    ((Over.homMk (U := ovT R B M) (V := A) (spMap (TrivSqZeroExt.inlHom B M) ≫ P) (inl_w A P h.1) *
      Over.homMk (U := ovT R B M) (V := A) z h.2 : ovT R B M ⟶ A)).left
  else z

theorem tau_eq (A : Over (Sp R)) [GrpObj A] {B M : Type} [CommRing B] [Algebra R B] [AddCommGroup M] [Module B M]
    [Module Bᵐᵒᵖ M] [IsCentralScalar B M] (P : Sp B ⟶ A.left) (hP : P ≫ A.hom = spMap (algebraMap R B))
    (z : Sp (TrivSqZeroExt B M) ⟶ A.left) (hz : z ≫ A.hom = (ovT R B M).hom) :
    tau A B M P z = ((Over.homMk (U := ovT R B M) (V := A) (spMap (TrivSqZeroExt.inlHom B M) ≫ P) (inl_w A P hP) *
      Over.homMk (U := ovT R B M) (V := A) z hz : ovT R B M ⟶ A)).left := by
  rw [tau, dif_pos ⟨hP, hz⟩]

theorem red_iff (A : Over (Sp R)) [GrpObj A] {B M : Type} [CommRing B] [Algebra R B] [AddCommGroup M] [Module B M]
    [Module Bᵐᵒᵖ M] [IsCentralScalar B M] (g : ovT R B M ⟶ A) (P : Sp B ⟶ A.left)
    (hP : P ≫ A.hom = spMap (algebraMap R B)) :
    spMap (TrivSqZeroExt.fstHom B B M).toRingHom ≫ g.left = P ↔
      eFst B M ≫ g = Over.homMk (U := ovB R B) (V := A) P hP := by
  constructor
  · intro h; ext; simpa [eFst] using h
  · intro h; have := congrArg CommaMorphism.left h; simpa [eFst] using this

theorem unit_eq (A : Over (Sp R)) [GrpObj A] (B : Type) [CommRing B] [Algebra R B]
    (h : unitPt A B ≫ A.hom = spMap (algebraMap R B)) :
    Over.homMk (U := ovB R B) (V := A) (unitPt A B) h = 1 := by
  ext; rw [one_left]; rfl

end GlobalTheory.AbTan.Transl

namespace GlobalTheory.AbTan.Transl

variable {R : Type} [CommRing R]

theorem unit_w (A : Over (Sp R)) [GrpObj A] (B : Type) [CommRing B] [Algebra R B] :
    unitPt A B ≫ A.hom = spMap (algebraMap R B) := by
  rw [unitPt, Category.assoc, Over.w η[A]]
  exact Category.comp_id _

theorem bijOn_tau (A : Over (Sp R)) [GrpObj A] {B M : Type} [CommRing B] [Algebra R B] [AddCommGroup M]
    [Module B M] [Module Bᵐᵒᵖ M] [IsCentralScalar B M] (P : Sp B ⟶ A.left)
    (hP : P ≫ A.hom = spMap (algebraMap R B)) :
    Set.BijOn (tau A B M P) {z | Lifts A.hom (unitPt A B) z} {z | Lifts A.hom P z} := by
  set Q : ovT R B M ⟶ A := Over.homMk (spMap (TrivSqZeroExt.inlHom B M) ≫ P) (inl_w A P hP) with hQ
  have hU := unit_w A B
  have keyQ : eFst B M ≫ Q = Over.homMk (U := ovB R B) (V := A) P hP := by
    ext
    simp only [eFst, Q, Over.comp_left, Over.homMk_left]
    rw [← Category.assoc, fst_inl]
    exact Category.id_comp _
  refine ⟨?_, ?_, ?_⟩
  · intro z hz
    obtain ⟨h1, h2⟩ := hz
    show Lifts A.hom P (tau A B M P z)
    rw [tau_eq A P hP z h1]
    refine ⟨Over.w _, ?_⟩
    rw [red_iff A _ P hP, MonObj.comp_mul, keyQ,
      (red_iff A (Over.homMk (U := ovT R B M) (V := A) z h1) (unitPt A B) hU).1 h2, unit_eq, _root_.mul_one]
  · intro z1 hz1 z2 hz2 he
    obtain ⟨h11, -⟩ := hz1
    obtain ⟨h21, -⟩ := hz2
    rw [tau_eq A P hP z1 h11, tau_eq A P hP z2 h21] at he
    have := mul_left_cancel (Over.OverMorphism.ext he)
    exact congrArg CommaMorphism.left this
  · intro z' hz'
    obtain ⟨h1, h2⟩ := hz'
    set Z : ovT R B M ⟶ A := Q⁻¹ * Over.homMk (U := ovT R B M) (V := A) z' h1 with hZ
    refine ⟨Z.left, ⟨Over.w Z, ?_⟩, ?_⟩
    · rw [red_iff A Z (unitPt A B) hU, unit_eq, hZ, MonObj.comp_mul, GrpObj.comp_inv, keyQ,
        (red_iff A (Over.homMk (U := ovT R B M) (V := A) z' h1) P hP).1 h2, inv_mul_cancel]
    · show tau A B M P Z.left = z'
      rw [tau_eq A P hP Z.left (Over.w Z)]
      have e : Over.homMk (U := ovT R B M) (V := A) Z.left (Over.w Z) = Z := by ext; rfl
      rw [← hQ, e, hZ, mul_inv_cancel_left]
      rfl

theorem tau_natural (A : Over (Sp R)) [GrpObj A] {B M : Type} [CommRing B] [Algebra R B] [AddCommGroup M]
    [Module B M] [Module Bᵐᵒᵖ M] [IsCentralScalar B M] {B' M' : Type} [CommRing B'] [Algebra R B']
    [AddCommGroup M'] [Module B' M'] [Module B'ᵐᵒᵖ M'] [IsCentralScalar B' M'] (α : B →ₐ[R] B') (f : M → M')
    (β : TrivSqZeroExt B M →+* TrivSqZeroExt B' M') (hβ : IsSum β α f) (P : Sp B ⟶ A.left)
    (hP : P ≫ A.hom = spMap (algebraMap R B)) (z : Sp (TrivSqZeroExt B M) ⟶ A.left)
    (hz : Lifts A.hom (unitPt A B) z) :
    Lifts A.hom (unitPt A B') (spMap β ≫ z) ∧
      tau A B' M' (spMap (α : B →+* B') ≫ P) (spMap β ≫ z) = spMap β ≫ tau A B M P z := by
  obtain ⟨hz1, hz2⟩ := hz
  have hβinl : β.comp (TrivSqZeroExt.inlHom B M) = (TrivSqZeroExt.inlHom B' M').comp (α : B →+* B') :=
    RingHom.ext fun b => hβ.1 b
  have hβT : β.comp ((TrivSqZeroExt.inlHom B M).comp (algebraMap R B)) =
      (TrivSqZeroExt.inlHom B' M').comp (algebraMap R B') := by
    rw [← RingHom.comp_assoc, hβinl, RingHom.comp_assoc, AlgHom.comp_algebraMap]
  have hβfst : (TrivSqZeroExt.fstHom B' B' M').toRingHom.comp β =
      (α : B →+* B').comp (TrivSqZeroExt.fstHom B B M).toRingHom := by
    ext x
    conv_lhs => rw [← TrivSqZeroExt.inl_fst_add_inr_snd_eq x]
    simp [map_add, hβ.1, hβ.2]
  let b : ovT R B' M' ⟶ ovT R B M := Over.homMk (spMap β) (by
    show spMap β ≫ spMap _ = spMap _
    rw [← GlobalTheory.Cris.spMap_comp, hβT])
  set Z : ovT R B M ⟶ A := Over.homMk z hz1 with hZ
  have hz' : (spMap β ≫ z) ≫ A.hom = (ovT R B' M').hom := Over.w (b ≫ Z)
  have hP' : (spMap (α : B →+* B') ≫ P) ≫ A.hom = spMap (algebraMap R B') := by
    rw [Category.assoc, hP, ← GlobalTheory.Cris.spMap_comp, AlgHom.comp_algebraMap]
  refine ⟨⟨hz', ?_⟩, ?_⟩
  · rw [← Category.assoc, ← GlobalTheory.Cris.spMap_comp, hβfst, GlobalTheory.Cris.spMap_comp, Category.assoc, hz2, unitPt,
      unitPt, ← Category.assoc, ← GlobalTheory.Cris.spMap_comp, AlgHom.comp_algebraMap]
  · rw [tau_eq A _ hP' _ hz', tau_eq A P hP z hz1]
    have e1 : b ≫ (Over.homMk (U := ovT R B M) (V := A) (spMap (TrivSqZeroExt.inlHom B M) ≫ P) (inl_w A P hP)) =
        Over.homMk (U := ovT R B' M') (V := A) (spMap (TrivSqZeroExt.inlHom B' M') ≫ spMap (α : B →+* B') ≫ P)
          (inl_w A _ hP') := by
      ext
      simp only [b, Over.comp_left, Over.homMk_left]
      rw [← Category.assoc, ← Category.assoc, ← GlobalTheory.Cris.spMap_comp, ← GlobalTheory.Cris.spMap_comp, hβinl]
    have e2 : b ≫ Z = Over.homMk (U := ovT R B' M') (V := A) (spMap β ≫ z) hz' := by ext; rfl
    show _ = (b ≫ (_ * Z)).left
    rw [MonObj.comp_mul, e1, e2]

end GlobalTheory.AbTan.Transl

open GlobalTheory.AbTan.Transl in

theorem GlobalTheory.AbTan.exists_translation : ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A], ∃ τ : ∀ (B M : Type) [CommRing B] [Algebra R B] [AddCommGroup M] [Module B M] [Module Bᵐᵒᵖ M] [IsCentralScalar B M], (Sp B ⟶ A.left) → (Sp (TrivSqZeroExt B M) ⟶ A.left) → (Sp (TrivSqZeroExt B M) ⟶ A.left), (∀ (B M : Type) [CommRing B] [Algebra R B] [AddCommGroup M] [Module B M] [Module Bᵐᵒᵖ M] [IsCentralScalar B M] (P : Sp B ⟶ A.left), P ≫ A.hom = spMap (algebraMap R B) → Set.BijOn (τ B M P) {z | Lifts A.hom (unitPt A B) z} {z | Lifts A.hom P z}) ∧ ∀ (B M : Type) [CommRing B] [Algebra R B] [AddCommGroup M] [Module B M] [Module Bᵐᵒᵖ M] [IsCentralScalar B M] (B' M' : Type) [CommRing B'] [Algebra R B'] [AddCommGroup M'] [Module B' M'] [Module B'ᵐᵒᵖ M'] [IsCentralScalar B' M'] (α : B →ₐ[R] B') (f : M → M') (β : TrivSqZeroExt B M →+* TrivSqZeroExt B' M'), IsSum β α f → ∀ (P : Sp B ⟶ A.left), P ≫ A.hom = spMap (algebraMap R B) → ∀ z, Lifts A.hom (unitPt A B) z → Lifts A.hom (unitPt A B') (spMap β ≫ z) ∧ τ B' M' (spMap (α : B →+* B') ≫ P) (spMap β ≫ z) = spMap β ≫ τ B M P z := by
  intro R _ A _
  refine ⟨fun B M => tau A B M, ?_, ?_⟩
  · intro B M _ _ _ _ _ _ P hP
    exact bijOn_tau A P hP
  · intro B M _ _ _ _ _ _ B' M' _ _ _ _ _ _ α f β hβ P hP z hz
    exact tau_natural A α f β hβ P hP z hz
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueRingHomOfSqZeroExtPointAffine
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh GlobalTheory.AbTan
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AbTan

theorem range_spMap_fst_eq (B M : Type) [CommRing B] [AddCommGroup M] [Module B M]
    [Module Bᵐᵒᵖ M] [IsCentralScalar B M] :
    Set.range (spMap (TrivSqZeroExt.fstHom B B M).toRingHom) = Set.univ := by
  refine Set.eq_univ_of_forall fun y ↦ ⟨spMap (TrivSqZeroExt.inlHom B M) y, ?_⟩
  change PrimeSpectrum.comap _ (PrimeSpectrum.comap _ y) = y
  apply PrimeSpectrum.ext
  ext x
  change (TrivSqZeroExt.inl x.fst : TrivSqZeroExt B M) ∈ y.asIdeal ↔ x ∈ y.asIdeal
  have hm : (TrivSqZeroExt.inr x.snd : TrivSqZeroExt B M) ∈ y.asIdeal :=
    y.isPrime.mem_of_pow_mem 2 (by rw [pow_two, TrivSqZeroExt.inr_mul_inr]; exact y.asIdeal.zero_mem)
  have hx : x = TrivSqZeroExt.inl x.fst + TrivSqZeroExt.inr x.snd := (TrivSqZeroExt.inl_fst_add_inr_snd_eq x).symm
  constructor
  · intro h; rw [hx]; exact y.asIdeal.add_mem h hm
  · intro h
    have e : (TrivSqZeroExt.inl x.fst : TrivSqZeroExt B M) = x - TrivSqZeroExt.inr x.snd := by
      rw [eq_sub_iff_add_eq]; exact TrivSqZeroExt.inl_fst_add_inr_snd_eq x
    rw [e]; exact y.asIdeal.sub_mem h hm

theorem exists_unique_ringHom_of_sqZero (R : Type) [CommRing R] (X : Scheme.{0}) (s : X ⟶ Sp R)
    (U : X.affineOpens) (B M : Type) [CommRing B] [Algebra R B] [AddCommGroup M] [Module B M]
    [Module Bᵐᵒᵖ M] [IsCentralScalar B M] (ρ : Sec s U.1 →+* B) (z : Sp (TrivSqZeroExt B M) ⟶ X)
    (hz : spMap (TrivSqZeroExt.fstHom B B M).toRingHom ≫ z = spMap ρ ≫ affPt s U) :
    ∃! c : Sec s U.1 →+* TrivSqZeroExt B M, spMap c ≫ affPt s U = z ∧ ∀ b, (c b).fst = ρ b := by
  have hr : Set.range z ⊆ Set.range (affPt s U) := by
    rintro _ ⟨y, rfl⟩
    obtain ⟨x, rfl⟩ : y ∈ Set.range (spMap (TrivSqZeroExt.fstHom B B M).toRingHom) := by
      rw [range_spMap_fst_eq]; trivial
    refine ⟨spMap ρ x, ?_⟩
    change (spMap ρ ≫ affPt s U) x = (spMap (TrivSqZeroExt.fstHom B B M).toRingHom ≫ z) x
    rw [hz]
  haveI : IsOpenImmersion (affPt s U) := IsAffineOpen.isOpenImmersion_fromSpec U.2
  set g := IsOpenImmersion.lift (affPt s U) z hr with hg
  have hgf : g ≫ affPt s U = z := IsOpenImmersion.lift_fac _ _ _
  have hsp : ∀ c c' : Sec s U.1 →+* TrivSqZeroExt B M,
      spMap c ≫ affPt s U = spMap c' ≫ affPt s U → c = c' := fun c c' h ↦ by
    have h' := (cancel_mono (affPt s U)).1 h
    have := Spec.map_injective h'
    exact congrArg CommRingCat.Hom.hom this
  have hsp' : ∀ c c' : Sec s U.1 →+* B,
      spMap c ≫ affPt s U = spMap c' ≫ affPt s U → c = c' := fun c c' h ↦ by
    have h' := (cancel_mono (affPt s U)).1 h
    have := Spec.map_injective h'
    exact congrArg CommRingCat.Hom.hom this
  set c₀ : Sec s U.1 →+* TrivSqZeroExt B M := (Spec.preimage g).hom with hc₀
  have hc : spMap c₀ = g := Spec.map_preimage g
  have h₁ : spMap c₀ ≫ affPt s U = z := by rw [hc, hgf]
  refine ⟨c₀, ⟨h₁, ?_⟩, fun c hc' ↦ hsp _ _ (hc'.1.trans h₁.symm)⟩
  have e : spMap ((TrivSqZeroExt.fstHom B B M).toRingHom.comp c₀) ≫ affPt s U =
      spMap ρ ≫ affPt s U := by
    rw [← hz, ← h₁, ← Category.assoc, ← Spec.map_comp]; rfl
  intro b
  exact congrArg (fun f : Sec s U.1 →+* B ↦ f b) (hsp' _ _ e)

end GlobalTheory.AbTan
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsWeightedMonomialValuationOfParametersStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_weighted_monomial_valuation_of_parameters : ∀ {L : Type} [Field L] (c : ℂ →+* L) (Q : Subring L) (hQ : IsLocModel c Q), letI := hQ.isLocalRing;
  ∀ (r N : ℕ) (z : Fin (r + 1) → Q) (wt : Fin (r + 1) → ℕ),
  IsLocalRing.maximalIdeal Q = Ideal.span (Set.range z) → ringKrullDim Q = r + 1 → wt 0 = 1 → (∀ i, 1 ≤ wt i) →
  (∃ x : Fin N → L, TrBasis c x) →
  ∃ V : Place c, V.Contains Q ∧ (∀ q : Q, IsUnit q → V.ord q = 0) ∧ (∀ i, V.ord (z i) = wt i) ∧
    (∀ (d : ℕ) (q : Q), (q : L) ≠ 0 → q ∈ IsLocalRing.maximalIdeal Q ^ d → (d : ℤ) ≤ V.ord q) ∧
    ∀ y : Fin N → Q, IsFreeGen Q (dForm (c.codRestrict Q hQ.const_mem) y) →
      V.formOrd (dForm c (fun i => (y i : L))) + 1 ≤ ∑ i, (wt i : ℤ) := by
  first | exact @GlobalTheory.MonoVal.monomial_place | exact GlobalTheory.MonoVal.monomial_place | (intros; apply GlobalTheory.MonoVal.monomial_place <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExtTraceNonnegOfPosFrameStatement
section
open Matrix Complex ComplexConjugate Filter Topology
open scoped ComplexOrder ContDiff
open GlobalTheory.HermFrame GlobalTheory.IndefiniteRowSideFullHecke.HermitianCurvatureForms

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ext_trace_nonneg_of_pos_frame : ∀ {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedSpace ℝ V] [IsScalarTower ℝ ℂ V] {m l : Type} [Fintype m] [Fintype l] [DecidableEq m] [DecidableEq l] {U : Set V} {H : V → Matrix (m ⊕ l) (m ⊕ l) ℂ} {z : V} (h : IsPosFrame U H) (hz : z ∈ U), IsNonnegForm (extTrace H z) := by
  first | exact @GlobalTheory.HermFrame.isNonnegForm_extTrace | exact GlobalTheory.HermFrame.isNonnegForm_extTrace | (intros; apply GlobalTheory.HermFrame.isNonnegForm_extTrace <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExtTraceWedgeSelfEqZeroStatement
section
open Matrix Complex ComplexConjugate Filter Topology
open scoped ComplexOrder ContDiff
open GlobalTheory.HermFrame GlobalTheory.IndefiniteRowSideFullHecke.HermitianCurvatureForms

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ext_trace_wedge_self_eq_zero : ∀ {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedSpace ℝ V] [IsScalarTower ℝ ℂ V] {m l : Type} [Fintype m] [Fintype l] [DecidableEq m] [DecidableEq l] {U : Set V} {H : V → Matrix (m ⊕ l) (m ⊕ l) ℂ} {z : V} (h : IsPosFrame U H) (hz : z ∈ U) (hm : Fintype.card m = 1) (hl : Fintype.card l = 1) (ξ₁ η₁ ξ₂ η₂ : V), wedge (extTrace H z) (extTrace H z) ξ₁ η₁ ξ₂ η₂ = 0 := by
  first | exact @GlobalTheory.extTrace_wedge_self_eq_zero_of_line | exact GlobalTheory.extTrace_wedge_self_eq_zero_of_line | (intros; apply GlobalTheory.extTrace_wedge_self_eq_zero_of_line <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteWeilRepEqLatticeIntertwinerMulCharacterStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.WeilParts GlobalTheory.FinWeil GlobalTheory.FinWeilO GlobalTheory.FockCompare GlobalTheory.VacUnique GlobalTheory.RatAut
open scoped TensorProduct Kronecker ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finiteWeilRep_eq_latticeIntertwiner_mul_character : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (hψ : IsStdChar D ψ (-1)) (S T : HSp D) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)), IsSelfDualC S ΛS → IsSelfDualC T ΛT → ∀ (χS χT : (AE D)ˣ →* Circle) (nS nT : ℕ), IsHeckeChar D χS → IsHeckeChar D χT → ResEta D χS nS → ResEta D χT nT → ∀ of : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ), IsFinWeil ψ S T ΛS ΛT χS χT of → ∀ (lam : ℕ →* ℂ), GoodNorm (GlobalTheory.FinWeil.sgO D) lam → (∀ n : ℕ, n ≠ 0 → (∀ q : ℕ, q.Prime → Formalism.MainNotions.StandardLatticesGL3.InertQ D q → ¬ q ∣ n) → lam n = (Real.sqrt n : ℂ)) → ∀ (w : 𝓞 D.host.E) (Om : GA D S × GA D T →* Module.End ℂ (thetaSub ψ S T)), IsLatRep hψ.1 ΛS ΛT w lam Om → ∀ ε, IsHalfIdem D ε → ∀ (g : GA D S) (h : GA D T) (x y : (AE D)ˣ), (x : AE D) = ε * (Formalism.L2.Theta.mt S g).det + (1 - ε) → (y : AE D) = ε * (Formalism.L2.Theta.mt T h).det + (1 - ε) → ∀ f : thetaSub ψ S T, of (g, h) f = ((((χT x)⁻¹ * χS y : Circle) : ℂ)) • (Om (g, h) f : WO S T → ℂ) := by
  first | exact @GlobalTheory.FinWeilForm.finWeil_eq | exact GlobalTheory.FinWeilForm.finWeil_eq | (intros; apply GlobalTheory.FinWeilForm.finWeil_eq <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HaarIntegralNormalizedOpenCompactEqIntegralDivStatement
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.haarIntegralNormalizedOpenCompact_eq_integral_div : ∀ (V : Type) [AddCommGroup V] [TopologicalSpace V] [IsTopologicalAddGroup V] (μ : @MeasureTheory.Measure V (borel V)), @MeasureTheory.Measure.IsAddHaarMeasure V _ _ (borel V) μ → ∀ (Λ : AddSubgroup V), IsOpen (Λ : Set V) → IsCompact (Λ : Set V) → ∀ u : V → ℂ, (∃ U : AddSubgroup V, IsOpen (U : Set V) ∧ ∀ x, ∀ y ∈ U, u (x + y) = u x) → HasCompactSupport u → GlobalTheory.BCT.hint (AddSubgroup.toSubgroup Λ) (fun X : Multiplicative V => u (Multiplicative.toAdd X)) = ((μ (Λ : Set V)).toReal : ℂ)⁻¹ * ∫ x, u x ∂μ := by
  first | exact @GlobalTheory.HaarSum.hint_eq_integral | exact GlobalTheory.HaarSum.hint_eq_integral | (intros; apply GlobalTheory.HaarSum.hint_eq_integral <;> assumption)
end

