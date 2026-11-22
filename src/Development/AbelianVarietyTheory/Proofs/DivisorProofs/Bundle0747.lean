import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Hilbert90IntegralIdelesOfMovedPrimes
import Development.AbelianVarietyTheory.Definitions.Divisors.GalMapMul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0719
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0434
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0574
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0549
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0588
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0729
import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0705
import Development.AbelianVarietyTheory.Definitions.Divisors.SplitDoublingNBlock
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0007
import Development.AbelianVarietyTheory.Definitions.ThetaValues.MemAnalyticAtZeroOfEventuallyDifferentiableAt
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0005
import Development.AbelianVarietyTheory.Definitions.Divisors.IsTaylorExpansionOrderOne
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0004
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0022
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0709
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0008
import Formalism.LocalToGlobal.UnitaryNorms.Bundle0006
import Formalism.LocalToGlobal.Columns.DecoFin
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0106
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0021
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.Bundle0017
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0730

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SuppInertUnitaryAdelicPointComponentAtPrimes
section
open NumberField IsDedekindDomain
open scoped Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.NormSum.PartSupp

open Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum.VacInt

theorem zeroAt_mul_left (D : Formalism.BasicNotions.D7) {q : ℕ} {e z : AE D} (he : e ∈ OhE D) (hz : ZeroAt D q z) :
    ZeroAt D q (e * z) := by
  intro k
  obtain ⟨m, hm, hc, s, hs, h⟩ := hz k
  exact ⟨m, hm, hc, e * s, mul_mem he hs, by linear_combination e * h⟩

theorem trivAt_part_of_trivAt (D : Formalism.BasicNotions.D7) {N : ℕ} (P : ℕ → Prop) (g : GA D N) {q : ℕ}
    (h : TrivAt D q (g : GL (Fin N) (AE D))) : TrivAt D q (part D P g : GL (Fin N) (AE D)) := by
  intro i j
  have := zeroAt_mul_left D (e := eps D.host.E P) (eps_mem P) (h i j)
  convert this using 1
  show cutM _ _ _ i j - _ = _
  rw [cutM_apply]
  ring

theorem suppInert_part_of_suppInert : ∀ {D : Formalism.BasicNotions.D7} {N : ℕ} (P : ℕ → Prop) (y : Formalism.MainNotions.StandardLatticesGL3.GA D N),
    Formalism.MainNotions.StandardLatticesGL3.SuppInert D (y : GL (Fin N) (Formalism.MainNotions.StandardLatticesGL3.AE D)) →
      Formalism.MainNotions.StandardLatticesGL3.SuppInert D (GlobalTheory.NormSum.VacInt.part D P y : GL (Fin N) (Formalism.MainNotions.StandardLatticesGL3.AE D)) :=
  fun {D} {_} P y hy q hq h => trivAt_part_of_trivAt D P y (hy q hq h)

end GlobalTheory.NormSum.PartSupp
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SurjOfStrictHenselisationPolynomial
section
open IsLocalRing Polynomial
open GlobalTheory.EtC

namespace GlobalTheory

theorem surj_of_strictHenselisation_polynomial : ∀ (T : Type) [CommRing T] (A : Type) [CommRing A]
    [Algebra (Polynomial T) A] [Algebra T A] [IsScalarTower T (Polynomial T) A], SH A →
    (∀ a : A, ∃ (E : Type) (_ : CommRing E) (_ : Algebra (Polynomial T) E)
      (_ : Algebra.Etale (Polynomial T) E) (φ : E →ₐ[Polynomial T] A), a ∈ φ.range) →
    ∃ (O : Type) (_ : CommRing O) (_ : Algebra T O) (_ : Algebra (Polynomial T) O)
      (_ : IsScalarTower T (Polynomial T) O) (_ : HenselianLocalRing O)
      (_ : IsSepClosed (IsLocalRing.ResidueField O)) (π : O →ₐ[Polynomial T] A),
      Function.Surjective π ∧ (∃ (ι : Type) (_ : Preorder ι) (_ : IsDirected ι (· ≤ ·))
        (_ : Nonempty ι) (Si : ι → Subalgebra (Polynomial T) O), Monotone Si ∧
        (∀ s : O, ∃ i, s ∈ Si i) ∧ ∀ i, ∃ (E : Type) (_ : CommRing E)
          (_ : Algebra (Polynomial T) E) (_ : Algebra.Etale (Polynomial T) E) (P : Ideal E)
          (_ : P.IsPrime), Nonempty (Localization.AtPrime P ≃ₐ[(Polynomial T)] Si i)) := by
  intro T _ A _ _ _ _ hSH hA
  obtain ⟨hHA, hsepA⟩ := hSH
  let y : Ideal (Polynomial T) := (maximalIdeal A).comap (algebraMap (Polynomial T) A)
  haveI : y.IsPrime := Ideal.comap_isPrime _ _
  obtain ⟨O, _, algRO, _, hloc, hsc, -, -, -, hind⟩ :=
    GlobalTheory.exists_strictHenselisation (Localization.AtPrime y)
      (SeparableClosure (ResidueField (Localization.AtPrime y)))
  letI algPO : Algebra (Polynomial T) O :=
    ((algebraMap (Localization.AtPrime y) O).comp
      (algebraMap (Polynomial T) (Localization.AtPrime y))).toAlgebra
  letI algTO : Algebra T O := ((algebraMap (Polynomial T) O).comp (algebraMap T (Polynomial T))).toAlgebra
  haveI t1 : IsScalarTower T (Polynomial T) O := IsScalarTower.of_algebraMap_eq' rfl
  haveI t2 : IsScalarTower (Polynomial T) (Localization.AtPrime y) O :=
    IsScalarTower.of_algebraMap_eq' rfl
  have hP := GlobalTheory.indEtale_localPieces_trans (Polynomial T) (Localization.AtPrime y) O
    ⟨Unit, inferInstance, inferInstance, inferInstance, fun _ => ⊤, monotone_const,
      fun _ => ⟨(), Algebra.mem_top⟩,
      fun _ => ⟨Polynomial T, inferInstance, inferInstance, inferInstance, y, inferInstance,
        ⟨Subalgebra.topEquiv.symm⟩⟩⟩ hind

  have hRO : (maximalIdeal O).comap (algebraMap (Localization.AtPrime y) O) =
      maximalIdeal (Localization.AtPrime y) := by
    ext x
    simp only [Ideal.mem_comap, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, isUnit_map_iff]
  have hyO : (maximalIdeal O).comap (algebraMap (Polynomial T) O) = y := by
    rw [IsScalarTower.algebraMap_eq (Polynomial T) (Localization.AtPrime y) O, ← Ideal.comap_comap,
      hRO]
    exact Localization.AtPrime.comap_maximalIdeal
  have hkO : ∀ r : Polynomial T, algebraMap (Polynomial T) (ResidueField O) r = 0 ↔ r ∈ y := by
    intro r
    rw [IsScalarTower.algebraMap_apply (Polynomial T) O (ResidueField O), ResidueField.algebraMap_eq,
      residue_eq_zero_iff, ← hyO, Ideal.mem_comap]
  have hkA : ∀ r : Polynomial T, algebraMap (Polynomial T) (ResidueField A) r = 0 ↔ r ∈ y := by
    intro r
    rw [IsScalarTower.algebraMap_apply (Polynomial T) A (ResidueField A), ResidueField.algebraMap_eq,
      residue_eq_zero_iff]
    rfl
  letI algyO : Algebra y.ResidueField (ResidueField O) :=
    (Ideal.ResidueField.lift y (algebraMap (Polynomial T) (ResidueField O)) (fun r hr => (hkO r).2 hr)
      (fun r hr => by
        simp only [Submonoid.mem_comap, IsUnit.mem_submonoid_iff]
        exact isUnit_iff_ne_zero.mpr (fun h => hr ((hkO r).1 h)))).toAlgebra
  haveI : IsScalarTower (Polynomial T) y.ResidueField (ResidueField O) := .of_algebraMap_eq fun r => by
    rw [RingHom.algebraMap_toAlgebra]
    exact (Ideal.ResidueField.lift_algebraMap y _ _ _ r).symm
  letI algyA : Algebra y.ResidueField (ResidueField A) :=
    (Ideal.ResidueField.lift y (algebraMap (Polynomial T) (ResidueField A)) (fun r hr => (hkA r).2 hr)
      (fun r hr => by
        simp only [Submonoid.mem_comap, IsUnit.mem_submonoid_iff]
        exact isUnit_iff_ne_zero.mpr (fun h => hr ((hkA r).1 h)))).toAlgebra
  haveI : IsScalarTower (Polynomial T) y.ResidueField (ResidueField A) := .of_algebraMap_eq fun r => by
    rw [RingHom.algebraMap_toAlgebra]
    exact (Ideal.ResidueField.lift_algebraMap y _ _ _ r).symm

  have hsepO : ∀ s : O, IsSeparable y.ResidueField (algebraMap O (ResidueField O) s) := by
    intro s
    obtain ⟨ι, _, _, _, Si, -, hcov, hpc⟩ := hP
    obtain ⟨i, hi⟩ := hcov s
    obtain ⟨B, _, _, _, q, _, ⟨e⟩⟩ := hpc i
    let F : Localization.AtPrime q →ₐ[Polynomial T] ResidueField O :=
      (IsScalarTower.toAlgHom (Polynomial T) O (ResidueField O)).comp ((Si i).val.comp e.toAlgHom)
    let f : B →ₐ[Polynomial T] ResidueField O :=
      F.comp (IsScalarTower.toAlgHom (Polynomial T) B (Localization.AtPrime q))
    obtain ⟨⟨a, t⟩, hat⟩ := IsLocalization.mk'_surjective q.primeCompl (e.symm ⟨s, hi⟩)
    have hs : algebraMap O (ResidueField O) s = F (IsLocalization.mk' _ a t) := by
      simp only [F, AlgHom.comp_apply, hat]
      simp
    have hft : f t ≠ 0 := by
      have : IsUnit (f t) :=
        (IsLocalization.map_units (Localization.AtPrime q) t).map F
      exact this.ne_zero
    have hmul : F (IsLocalization.mk' _ a t) * f t = f a := by
      simp only [f, AlgHom.comp_apply, IsScalarTower.coe_toAlgHom', ← map_mul,
        IsLocalization.mk'_spec]
    have hx : algebraMap O (ResidueField O) s = f a * (f t)⁻¹ := by
      rw [hs, eq_mul_inv_iff_mul_eq₀ hft, hmul]
    rw [hx, ← mem_separableClosure_iff]
    refine mul_mem ?_ (inv_mem ?_) <;> rw [mem_separableClosure_iff] <;>
      exact GlobalTheory.Specialise.sepEtale (Polynomial T) B y _ f _
  haveI : Algebra.IsSeparable y.ResidueField (ResidueField O) := ⟨fun x => by
    obtain ⟨s, rfl⟩ := residue_surjective x
    have := hsepO s
    rwa [ResidueField.algebraMap_eq] at this⟩
  haveI : IsSepClosure y.ResidueField (ResidueField O) := ⟨hsc, inferInstance⟩
  let L := separableClosure y.ResidueField (ResidueField A)
  let e : ResidueField O ≃ₐ[y.ResidueField] L := IsSepClosure.equiv y.ResidueField (ResidueField O) L
  let ι : ResidueField O →ₐ[y.ResidueField] ResidueField A := L.val.comp e.toAlgHom
  let ψ₀ : O →ₐ[Polynomial T] ResidueField A :=
    (ι.restrictScalars (Polynomial T)).comp (IsScalarTower.toAlgHom (Polynomial T) O (ResidueField O))
  obtain ⟨π, hπ⟩ := (GlobalTheory.IndEtaleHensel.bijective_residue_comp (Polynomial T) O A hP).2 ψ₀
  refine ⟨O, inferInstance, algTO, algPO, t1, inferInstance, hsc, π, ?_, hP⟩
  intro b
  obtain ⟨E, _, _, _, φ, hb⟩ := hA b
  obtain ⟨e0, rfl⟩ := (AlgHom.mem_range φ).1 hb
  let f : E →ₐ[Polynomial T] ResidueField A :=
    (IsScalarTower.toAlgHom (Polynomial T) A (ResidueField A)).comp φ
  have hfL : ∀ x, f x ∈ L := fun x =>
    mem_separableClosure_iff.2 (GlobalTheory.Specialise.sepEtale (Polynomial T) E y (ResidueField A) f x)
  let g : E →ₐ[Polynomial T] ResidueField O :=
    { toRingHom := (e.symm : L →+* ResidueField O).comp (f.toRingHom.codRestrict L hfL)
      commutes' := fun r => by
        apply e.injective
        change e (e.symm ⟨f (algebraMap _ E r), hfL _⟩) = _
        rw [AlgEquiv.apply_symm_apply]
        apply Subtype.ext
        rw [IsScalarTower.algebraMap_apply (Polynomial T) y.ResidueField (ResidueField O),
          AlgEquiv.commutes]
        change f (algebraMap _ E r) = _
        rw [AlgHom.commutes, IsScalarTower.algebraMap_apply (Polynomial T) y.ResidueField (ResidueField A)]
        rfl }
  obtain ⟨ψ, hψ⟩ := (GlobalTheory.EtaleHensel.bijective_residue_comp (Polynomial T) E O).2 g
  have hcomp : π.comp ψ = φ := by
    apply (GlobalTheory.EtaleHensel.bijective_residue_comp (Polynomial T) E A).1
    dsimp only
    ext x
    have h1 := DFunLike.congr_fun hπ (ψ x)
    have h2 := DFunLike.congr_fun hψ x
    simp only [AlgHom.comp_apply] at h1 h2 ⊢
    rw [h1]
    change ι (IsScalarTower.toAlgHom (Polynomial T) O (ResidueField O) (ψ x)) = f x
    rw [h2]
    change ((e (e.symm ⟨f x, hfL x⟩) : L) : ResidueField A) = f x
    rw [AlgEquiv.apply_symm_apply]
  exact ⟨ψ e0, DFunLike.congr_fun hcomp e0⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SurjectiveEvalTmulStatement
section
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat
open TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.surjective_isEval_tmul_of_surjective : ∀ (p : ℕ) (O A B σ τ : Type) [CommRing O] [CommRing A] [CommRing B] [Algebra O A] [Algebra O B] [Fintype σ] [Fintype τ] [IsHausdorff (Ideal.span {(p : A ⊗[O] B)}) (A ⊗[O] B)] (x : σ → A) (y : τ → B) (evA : MvPowerSeries σ O →ₐ[O] A) (evB : MvPowerSeries τ O →ₐ[O] B) (E : MvPowerSeries (σ ⊕ τ) O →ₐ[O] A ⊗[O] B), IsEval p x evA → IsEval p y evB → IsEval p (Sum.elim (fun i => x i ⊗ₜ[O] (1 : B)) fun j => (1 : A) ⊗ₜ[O] y j) E → Function.Surjective evA → Function.Surjective evB → Function.Surjective E := by
  first | exact @GlobalTheory.SurjTens.surjective_eval_tmul | exact GlobalTheory.SurjTens.surjective_eval_tmul | (intros; apply GlobalTheory.SurjTens.surjective_eval_tmul <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SymmetricPositionCharMultiplicityParabolicInductStatement
section
open GlobalTheory.FinGL Formalism.L2.DIV Module
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.symmetricPositionCharMultiplicity_parabolicInduction : ∀ (F : Type) [Field F] [Fintype F] (ψ : AddChar F ℂ), ψ ≠ 1 → ∀ (r : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] (b : Fin r → ℕ) (σ : Representation ℂ (blockTri (κ := F) b) V), IsCuspDatum b σ → ∀ ρ k : ℕ, ρ + k + 1 ≤ r → nPos ψ (parInd b σ) ρ k = ∑ j ∈ Finset.range (k + 1), splitDoublingNBlock b j * gam (Fintype.card F) (k - j) := by
  first | exact @GlobalTheory.FinGL.nPos_parInd | exact GlobalTheory.FinGL.nPos_parInd | (intros; apply GlobalTheory.FinGL.nPos_parInd <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TaylorAddSquareZeroNilpotentStatement
section
open Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.taylor_add_square_zero_nilpotent : ∀ {I : Type} [Fintype I] [DecidableEq I] {D : Type} [CommRing D] [Algebra ℂ D] (N : ℕ) (t : I → D) (n : I → D), (∀ s : Fin (N + 1) → D, (∀ a, s a ∈ Ideal.span (Set.range t ∪ Set.range n)) → ∏ a, s a = 0) → (∀ i j, n i * n j = 0) → ∀ f : (I → ℂ) → ℂ, AnalyticAt ℂ f 0 → GlobalTheory.PeriodFamily.taylor N (fun i ↦ t i + n i) f = GlobalTheory.PeriodFamily.taylor N t f + ∑ i, GlobalTheory.PeriodFamily.taylor N t (fun z ↦ fderiv ℂ f z (Pi.single i 1)) * n i := by
  first | exact @GlobalTheory.PeriodFamily.taylor_add_of_mul_eq_zero | exact GlobalTheory.PeriodFamily.taylor_add_of_mul_eq_zero | (intros; apply GlobalTheory.PeriodFamily.taylor_add_of_mul_eq_zero <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TaylorPolynomialEvalAlgebraMulOfProdEqZeroStatement
section
open Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.taylorPolynomialEvalAlgebra_mul_of_prod_eq_zero : ∀ {I : Type} [Fintype I] [DecidableEq I] {D : Type} [CommRing D] [Algebra ℂ D] (N : ℕ) (t : I → D), (∀ s : Fin (N + 1) → I, ∏ a, t (s a) = 0) → ∀ f g : (I → ℂ) → ℂ, AnalyticAt ℂ f 0 → AnalyticAt ℂ g 0 → GlobalTheory.PeriodFamily.taylor N t (fun z ↦ f z * g z) = GlobalTheory.PeriodFamily.taylor N t f * GlobalTheory.PeriodFamily.taylor N t g := by
  first | exact @GlobalTheory.PeriodFamily.taylor_mul_of_prod_eq_zero | exact GlobalTheory.PeriodFamily.taylor_mul_of_prod_eq_zero | (intros; apply GlobalTheory.PeriodFamily.taylor_mul_of_prod_eq_zero <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TaylorRestrictionSubMemIdealMapStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj Filter Topology TopologicalSpace TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.AnPer GlobalTheory.PeriodFamily
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.taylor_restriction_sub_mem_ideal_map : ∀ {I : Type} [Fintype I] [DecidableEq I] {g : ℕ} {R : Type} [CommRing R] [Algebra ℂ R] (N : ℕ) (t : I → R) (π : R →ₐ[ℂ] ℂ), (∀ i, π (t i) = 0) → ∀ (W : Opens (Tot I g)) (W₀ : Opens (Tot Empty g)), (∀ p ∈ W₀, (((0 : I → ℂ), p.2) : Tot I g) ∈ W) → ∀ ρ : Hol W →+* R ⊗[ℂ] Hol W₀, IsTay N t ρ → ∀ (h : Hol W) (h₀ : Hol W₀), (∀ p ∈ W₀, h₀.fn p = h.fn (0, p.2)) → ρ h - 1 ⊗ₜ[ℂ] h₀ ∈ (RingHom.ker π).map (Algebra.TensorProduct.includeLeft : R →ₐ[ℂ] R ⊗[ℂ] Hol W₀) := by
  first | exact @GlobalTheory.AnPer.taylor_reduces_to_slice | exact GlobalTheory.AnPer.taylor_reduces_to_slice | (intros; apply GlobalTheory.AnPer.taylor_reduces_to_slice <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TaylorSubValueEqSumSqZeroVector
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj Filter Topology TopologicalSpace TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.AnPer GlobalTheory.PeriodFamily
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PeriodFamily

theorem taylor_sub_value_eq_sum_sqZero : ∀ {I : Type} [Fintype I] [DecidableEq I] {g : ℕ} {R : Type} [CommRing R] [Algebra ℂ R] (J : Ideal R) (N : ℕ), (∀ s : Fin (N + 1) → R, (∀ a, s a ∈ J) → ∏ a, s a = 0) → ∀ (r : ℕ) (m : Fin r → I → R), (∀ j i, m j i ∈ J) → (∀ j i i', m j i * m j i' = 0) → ∀ τ : (I → ℂ) → Fin g → ℂ, AnalyticAt ℂ τ 0 → ∃ n : Fin r → Fin g → R, (∀ j a, n j a ∈ J) ∧ (∀ j a b, n j a * n j b = 0) ∧ ∀ a, taylor N (fun i ↦ ∑ j, m j i) (fun z ↦ τ z a) - algebraMap ℂ R (τ 0 a) = ∑ j, n j a := by
  intro I _ _ g R _ _ J N hJ r
  induction r with
  | zero =>
    intro m _ _ τ _
    refine ⟨fun j => Fin.elim0 j, fun j => Fin.elim0 j, fun j => Fin.elim0 j, fun a => ?_⟩
    have h := (taylor_formal_properties N (fun i ↦ ∑ j : Fin 0, m j i)).2.2.2.2.2 (fun z ↦ τ z a)
    simp only [Finset.univ_eq_empty, Finset.sum_empty] at h ⊢
    have : Set.range (fun _ : I => (0 : R)) ⊆ {0} := by
      rintro _ ⟨_, rfl⟩; rfl
    have hb : Ideal.span (Set.range (fun _ : I => (0 : R))) = ⊥ := by
      rw [Ideal.span_eq_bot]; rintro _ ⟨_, rfl⟩; rfl
    rw [hb, Ideal.mem_bot] at h
    exact h
  | succ r ih =>
    intro m hmJ hm τ hτ
    obtain ⟨n', hn'J, hn', hn'eq⟩ := ih (fun j => m (Fin.castSucc j)) (fun j i => hmJ _ i)
      (fun j i i' => hm _ i i') τ hτ
    set t : I → R := fun i => ∑ j : Fin r, m (Fin.castSucc j) i with ht
    set l : I → R := fun i => m (Fin.last r) i with hl
    let v : Fin g → R := fun a => ∑ i, taylor N t (fun z ↦ fderiv ℂ (fun z ↦ τ z a) z (Pi.single i 1)) * l i
    have htJ : ∀ i, t i ∈ J := fun i => J.sum_mem fun j _ => hmJ _ i
    have hlJ : ∀ i, l i ∈ J := fun i => hmJ _ i
    have hspan : Ideal.span (Set.range t ∪ Set.range l) ≤ J := by
      rw [Ideal.span_le]
      rintro _ (⟨i, rfl⟩ | ⟨i, rfl⟩)
      · exact htJ i
      · exact hlJ i
    have hvJ : ∀ a, v a ∈ J := fun a => J.sum_mem fun i _ => J.mul_mem_left _ (hlJ i)
    have hv : ∀ a b, v a * v b = 0 := by
      intro a b
      simp only [v, Finset.sum_mul, Finset.mul_sum]
      refine Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun i' _ => ?_
      have := hm (Fin.last r) i' i
      calc _ = (taylor N t (fun z ↦ fderiv ℂ (fun z ↦ τ z b) z (Pi.single i 1)) *
              taylor N t (fun z ↦ fderiv ℂ (fun z ↦ τ z a) z (Pi.single i' 1))) * (l i' * l i) := by ring
        _ = 0 := by simp only [hl, this, mul_zero]
    refine ⟨Fin.snoc (α := fun _ => Fin g → R) n' v, ?_, ?_, ?_⟩
    · intro j a
      refine Fin.lastCases ?_ (fun j => ?_) j
      · simpa using hvJ a
      · simpa using hn'J j a
    · intro j a b
      refine Fin.lastCases ?_ (fun j => ?_) j
      · simpa using hv a b
      · simpa using hn' j a b
    · intro a
      have hfa : AnalyticAt ℂ (fun z ↦ τ z a) 0 :=
        ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin g => ℂ) a).analyticAt (τ 0)).comp hτ
      have hsum : (fun i ↦ ∑ j : Fin (r + 1), m j i) = fun i => t i + l i := by
        funext i; simp only [ht, hl, Fin.sum_univ_castSucc]
      have hstep := taylor_add_of_mul_eq_zero N t l
        (fun s hs => hJ s fun a => hspan (hs a)) (fun i j => hm (Fin.last r) i j) _ hfa
      rw [hsum, hstep, Fin.sum_univ_castSucc]
      simp only [Fin.snoc_castSucc, Fin.snoc_last]
      rw [← hn'eq a]
      simp only [v, t]
      ring

end GlobalTheory.PeriodFamily
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TaylorSumSubValueEqSumSqZero
section
set_option autoImplicit false

namespace GlobalTheory.PeriodFamily

theorem taylor_sum_sub_value_eq_sum_sqZero : ∀ {I : Type} [Fintype I] [DecidableEq I] {D : Type} [CommRing D] [Algebra ℂ D] (J : Ideal D) (N : ℕ), (∀ s : Fin (N + 1) → D, (∀ a, s a ∈ J) → ∏ a, s a = 0) → ∀ (r : ℕ) (n : Fin r → I → D), (∀ j i, n j i ∈ J) → (∀ j i i', n j i * n j i' = 0) → ∀ {K : Type} (f : K → (I → ℂ) → ℂ), (∀ a, AnalyticAt ℂ (f a) 0) → ∃ n' : Fin r → K → D, (∀ j a, n' j a ∈ J) ∧ (∀ j a b, n' j a * n' j b = 0) ∧ ∀ a, GlobalTheory.PeriodFamily.taylor N (fun i ↦ ∑ j, n j i) (f a) - algebraMap ℂ D (f a 0) = ∑ j, n' j a := by
  intro I _ _ D _ _ J N hJ r
  induction r with
  | zero =>
    intro n _ _ K f _
    refine ⟨fun j ↦ j.elim0, fun j ↦ j.elim0, fun j ↦ j.elim0, fun a ↦ ?_⟩
    have h := taylor_sub_value_mem_span N (fun i ↦ ∑ j, n j i) (f a)
    have h0 : Ideal.span (Set.range (fun i ↦ ∑ j, n j i)) = ⊥ := by
      rw [Ideal.span_eq_bot]
      rintro x ⟨i, rfl⟩
      simp
    rw [h0, Ideal.mem_bot] at h
    rw [h]
    simp
  | succ r ih =>
    intro n hn hsq K f hf
    obtain ⟨n', h1, h2, h3⟩ := ih (fun j ↦ n j.succ) (fun j i ↦ hn _ _) (fun j i i' ↦ hsq _ _ _) f hf
    refine ⟨Fin.cons (fun a ↦ ∑ i, taylor N (fun i ↦ ∑ j : Fin r, n j.succ i)
      (fun z ↦ fderiv ℂ (f a) z (Pi.single i 1)) * n 0 i) n', ?_, ?_, fun a ↦ ?_⟩
    · intro j a
      refine Fin.cases ?_ (fun j ↦ ?_) j
      · simp only [Fin.cons_zero]
        exact Ideal.sum_mem _ fun i _ ↦ Ideal.mul_mem_left _ _ (hn _ _)
      · simpa only [Fin.cons_succ] using h1 j a
    · intro j a b
      refine Fin.cases ?_ (fun j ↦ ?_) j
      · simp only [Fin.cons_zero]
        rw [Finset.sum_mul_sum]
        refine Finset.sum_eq_zero fun i _ ↦ Finset.sum_eq_zero fun i' _ ↦ ?_
        rw [mul_mul_mul_comm, hsq, mul_zero]
      · simpa only [Fin.cons_succ] using h2 j a b
    · have he : (fun i ↦ ∑ j, n j i) = fun i ↦ (∑ j : Fin r, n j.succ i) + n 0 i := by
        funext i
        rw [Fin.sum_univ_succ, add_comm]
      have hle : Ideal.span (Set.range (fun i ↦ ∑ j : Fin r, n j.succ i) ∪ Set.range (n 0)) ≤ J := by
        rw [Ideal.span_le]
        rintro x (⟨i, rfl⟩ | ⟨i, rfl⟩)
        · exact Ideal.sum_mem _ fun j _ ↦ hn _ _
        · exact hn _ _
      rw [he, taylor_add_of_mul_eq_zero N (fun i ↦ ∑ j : Fin r, n j.succ i) (n 0)
        (fun s hs ↦ hJ s fun a ↦ hle (hs a)) (hsq 0) (f a) (hf a), Fin.sum_univ_succ]
      simp only [Fin.cons_zero, Fin.cons_succ]
      rw [← h3 a]
      ring

end GlobalTheory.PeriodFamily
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnderEqOrSmulUnderEq
section
open Formalism.BasicNotions NumberField IsDedekindDomain
open scoped Pointwise

namespace GlobalTheory.ConjOverQuad

theorem under_eq_or_smul_under_eq {L : Type} [Field L] [NumberField L] [IsGalois ℚ L] {p : ℕ} (hp : p.Prime) (b : L)
    (hb : ∀ σ : L ≃ₐ[ℚ] L, σ b = b ∨ σ b = -b) (c : L ≃ₐ[ℚ] L) (hc : c b = -b)
    (v : Ideal (𝓞 L)) [v.IsPrime] (hv : ((p : ℕ) : 𝓞 L) ∈ v)
    (Q : Ideal (𝓞 (IntermediateField.adjoin ℚ {b}))) [Q.IsPrime]
    (hQ : ((p : ℕ) : 𝓞 (IntermediateField.adjoin ℚ {b})) ∈ Q) :
    v.under (𝓞 (IntermediateField.adjoin ℚ {b})) = Q ∨
      (c⁻¹ • v).under (𝓞 (IntermediateField.adjoin ℚ {b})) = Q := by
  obtain ⟨⟨W, hW, hWQ⟩⟩ := (inferInstance : Nonempty (Q.primesOver (𝓞 L)))
  have hpW : ((p : ℕ) : 𝓞 L) ∈ W := by
    rw [hWQ.over, Ideal.mem_under] at hQ
    simpa using hQ
  have := GlobalTheory.Mem.Chr.liesOver_span_of_natCast_mem hp _ hv
  have := GlobalTheory.Mem.Chr.liesOver_span_of_natCast_mem hp _ hpW
  obtain ⟨σ, hσ⟩ := Ideal.exists_smul_eq_of_isGaloisGroup (Ideal.span {(p : ℤ)}) v W (L ≃ₐ[ℚ] L)
  rcases hb σ with h1 | h1
  · left
    rw [hWQ.over, ← hσ, GlobalTheory.Mem.Chr.under_smul_of_fix b σ h1]
  · right
    have h2 : (σ * c) b = b := by
      rw [AlgEquiv.mul_apply, hc, map_neg, h1, neg_neg]
    have h4 : (σ * c) • c⁻¹ • v = W := by rw [mul_smul, smul_inv_smul, hσ]
    rw [hWQ.over, ← h4, GlobalTheory.Mem.Chr.under_smul_of_fix b _ h2]

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem div_or_conj_div : ∀ (D : D7) (P : Formalism.L2.Host.PiBar D.host) (k : Fin 2) (w : HeightOneSpectrum (𝓞 D.host.E)), ((D.host.g k : ℕ) : 𝓞 D.host.E) ∈ w.asIdeal → P.Div k w ∨ ∃ w' : HeightOneSpectrum (𝓞 D.host.E), P.Div k w' ∧ w'.asIdeal = Formalism.HermitianLatticesTheory.conjIdeal (K := D.host.E) w.asIdeal := by
  intro D P k w hw
  have hG : IsGalois ℚ D.host.E := D.host.hostE_isGalois
  have hsq := D.host.sqrtMinusD_sq
  have hc := D.host.conj_sqrtMinusD
  have hb : ∀ σ : D.host.E ≃ₐ[ℚ] D.host.E,
      σ D.host.sqrtMinusD = D.host.sqrtMinusD ∨ σ D.host.sqrtMinusD = -D.host.sqrtMinusD := by
    intro σ
    apply sq_eq_sq_iff_eq_or_eq_neg.1
    rw [← map_pow, hsq, map_neg, map_natCast]
  have := w.isPrime
  have hQ := (P.pb k).isPrime
  rcases @under_eq_or_smul_under_eq _ _ _ _ _ (D.host.g_prime k) D.host.sqrtMinusD hb D.host.conj hc w.asIdeal _ hw
    (P.pb k).asIdeal hQ (P.pb_over k) with h | h
  · exact Or.inl (HeightOneSpectrum.ext h)
  · refine Or.inr ⟨Formalism.L2.Col.conjPrime₂ w, HeightOneSpectrum.ext ?_, (Formalism.L2.Col.conjIdeal_asIdeal w).symm⟩
    have e : (Formalism.L2.Col.conjPrime₂ w).asIdeal = D.host.conj⁻¹ • w.asIdeal := by
      ext y
      rw [Formalism.L2.Col.mem_conjP, Ideal.mem_inv_pointwise_smul_iff]
      have : Formalism.L2.Col.cO D.host.E y = D.host.conj • y :=
        RingOfIntegers.ext (bridge_star_holds D.R D.host (y : D.host.E))
      rw [this]
    show ((Formalism.L2.Col.conjPrime₂ w).asIdeal).under (𝓞 D.host.K) = _
    rw [e]
    exact h

end GlobalTheory.ConjOverQuad
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisedOneFormEvaluationLinearPullback
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.CechDR GlobalTheory.CechPer

attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

namespace GlobalTheory.CechPer

theorem evForm_secPull : ∀ (A : Over (Sp ℂ)) [GrpObj A] (g : ℕ) (L : LB A.left) (u : HolUnif A L g), ∀ (A' : Over (Sp ℂ)) [GrpObj A'] (g' : ℕ) (L' : LB A'.left) (u' : HolUnif A' L' g') (φ : A' ⟶ A) (M : (Fin g' → ℂ) →L[ℂ] (Fin g → ℂ)) (h : φ.left ≫ str A = str A' ≫ spMap (RingHom.id ℂ)), (∀ w, u.ex (M w) = u'.ex w ≫ φ) → ∀ (p : Pair φ.left), ∀ z ∈ pre u'.ex p.1.1.1, M z ∈ pre u.ex p.1.2.1 ∧ (∀ b, val u'.ex p.1.1.1 (secPull (str A) (str A') p b) z = val u.ex p.1.2.1 b (M z)) ∧ ∀ ξ, evForm u'.ex p.1.1.1 z ((semiHom_secPull h p).m1 ξ) = (evForm u.ex p.1.2.1 (M z) ξ).comp M := by
  intro A _ g L u A' _ g' L' u' φ M h hM p z hz
  have hpt : ∀ w, (u.ex (M w)).left = (u'.ex w).left ≫ φ.left := fun w => by rw [hM w]; rfl
  have hval : ∀ w ∈ pre u'.ex p.1.1.1, ∀ b, val u'.ex p.1.1.1 (secPull (str A) (str A') p b) w =
      val u.ex p.1.2.1 b (M w) := by
    intro w hw b
    have k := valAt'_appLE (u'.ex w).left φ.left p.1.2.1 p.1.1.1 p.2 b hw
    rw [← hpt] at k
    exact k
  have hpre : ∀ w ∈ pre u'.ex p.1.1.1, M w ∈ pre u.ex p.1.2.1 := by
    intro w hw
    change ⊤ ≤ (u.ex (M w)).left ⁻¹ᵁ p.1.2.1
    rw [hpt, top_le_preimage_comp]
    exact fun x hx => p.2 (hw hx)
  refine ⟨hpre z hz, hval z hz, ?_⟩
  have hopen : ∀ U, IsOpen (pre u.ex U) := fun U => (u.hol U 0).1
  have hdiff : ∀ U b, DifferentiableOn ℂ (val u.ex U b) (pre u.ex U) := fun U b => (u.hol U b).2
  have hopen' : ∀ U, IsOpen (pre u'.ex U) := fun U => (u'.hol U 0).1
  obtain ⟨-, hsm, hD⟩ := GlobalTheory.T.uniformisedOneFormEvaluation_rules A g L u p.1.2.1 (M z) (hpre z hz)
  obtain ⟨-, hsm', hD'⟩ := GlobalTheory.T.uniformisedOneFormEvaluation_rules A' g' L' u' p.1.1.1 z hz
  intro ξ
  have hξ : ξ ∈ Submodule.span (Sec (str A) p.1.2.1) (Set.range (KaehlerDifferential.D ℂ (Sec (str A) p.1.2.1))) := by
    rw [KaehlerDifferential.span_range_derivation]; trivial
  induction hξ using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨b, rfl⟩ := hx
    rw [SemiHom.m1_D, hD', hD]
    have e : val u'.ex p.1.1.1 (secPull (str A) (str A') p b) =ᶠ[nhds z] (val u.ex p.1.2.1 b) ∘ M :=
      Filter.eventually_of_mem ((hopen' p.1.1.1).mem_nhds hz) fun w hw => hval w hw b
    rw [e.fderiv_eq, fderiv_comp z ((hdiff _ b).differentiableAt ((hopen _).mem_nhds (hpre z hz)))
      M.differentiableAt, M.fderiv]
  | zero => simp
  | add x y _ _ hx hy => rw [map_add, map_add, hx, hy, map_add, ContinuousLinearMap.add_comp]
  | smul a x _ hx => rw [SemiHom.oneFormMap_smul_semilinear, hsm', hsm, hx, hval z hz a, ContinuousLinearMap.smul_comp]

end GlobalTheory.CechPer
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WhittakerSpaceDimParabolicInductionCuspidalEqOneStatement
section
open GlobalTheory.FinGL Formalism.L2.DIV Module
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.whittakerSpaceDim_parabolicInduction_cuspidal_eq_one : ∀ (F : Type) [Field F] [Fintype F] (ψ : AddChar F ℂ), ψ ≠ 1 → ∀ (r : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] (b : Fin r → ℕ) (σ : Representation ℂ (blockTri (κ := F) b) V), IsCuspDatum b σ → whDim ψ (parInd b σ) = 1 := by
  first | exact @GlobalTheory.FinGL.whDim_parInd_eq_one | exact GlobalTheory.FinGL.whDim_parInd_eq_one | (intros; apply GlobalTheory.FinGL.whDim_parInd_eq_one <;> assumption)
end

