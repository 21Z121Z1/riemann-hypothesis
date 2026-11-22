import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IntFormsSubset
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0975
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0921
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsDeltaDatumHigherLevel
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsLevelMulSplit
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle0023
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0238
import Development.AbelianVarietyTheory.Definitions.HeightFunctions.XiValIffXiAt
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.Bundle0001
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LengthPosOfPosDef
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0019
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0024
import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.GaussianBinomialClosedForm
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.SqNormIntegralFundamentalDomainEqL2NormSq
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0927
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0974
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0956
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0976
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ProjectedLiftUnipotentTypeBaseLevelForm
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnivChar
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0016
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0894
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0645
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0020
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0027
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0025
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0032
import Development.AbelianVarietyTheory.Definitions.Divisors.IsAddHaarMeasureVolumeLie
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0872
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.T2SpaceAdelicGeneralLinearGroupNumberField
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdelicUnitriangularMulMemUnipotentTimesIntegral
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
import GroundTheory.AutomorphicForms.MultiplicityOne.Bundle0001
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0895
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.ExistsIsFundamentalDomainAndQuotMeasureEq
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0021
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0949
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0931
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0936
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0905
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0919
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0882
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1888
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0821

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteDimensionalZeta
section
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj GlobalTheory.CoverRead GlobalTheory.Member GlobalTheory.CompRat GlobalTheory.FinalJoin
open scoped TensorProduct Matrix

set_option autoImplicit false

namespace GlobalTheory.CoverExists

theorem exists_ext_of_le {K L : IntermediateField ℚ ℂ} [FiniteDimensional ℚ L] (hle : K ≤ L) (σ : K →+* ℂ) :
    ∃ σ' : L →+* ℂ, σ'.comp (IntermediateField.inclusion hle).toRingHom = σ := by
  letI : Algebra K L := (IntermediateField.inclusion hle).toRingHom.toAlgebra
  letI : Algebra K ℂ := σ.toAlgebra
  haveI : IsScalarTower ℚ K L :=
    IsScalarTower.of_algebraMap_eq (fun x => ((IntermediateField.inclusion hle).commutes x).symm)
  haveI : Module.Finite K L := Module.Finite.of_restrictScalars_finite ℚ K L
  haveI : Algebra.IsAlgebraic K L := Algebra.IsAlgebraic.of_finite K L
  refine ⟨(IsAlgClosed.lift : L →ₐ[K] ℂ).toRingHom, ?_⟩
  ext x
  exact (IsAlgClosed.lift : L →ₐ[K] ℂ).commutes x

end GlobalTheory.CoverExists

namespace GlobalTheory.CoverExists

end GlobalTheory.CoverExists
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FockPolynomialLieDerivativeEquivariantStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fockPolynomial_lieDerivative_equivariant : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.LiftRows.Given R F → R.FullP → ∀ (i : Fin D.R.m) (t : T) (τ : D.what₂.Tau) (Y : Matrix (Fin (Wc D i).rank) (Fin (Wc D i).rank) ℂ), Y ∈ lieAt (Wc D i) τ → ∀ (ψ ψ' : ((R.cV i).W →ₗ[ℂ] PolF D (Wc D i).rank (Vc D i).rank)), (∀ u ∈ GinfC (Vc D i), ∀ w', R.ptP i t (ψ ((R.cV i).ρ u w')) = R.ωP i t (u, 1) (R.ptP i t (ψ w'))) → (∀ w z, HasDerivAt (fun s : ℝ => R.ωP i t (1, oneP R.θ (Wc D i) τ Y s) (R.ptP i t (ψ w)) z) (R.ptP i t (ψ' w) z) 0) → (∀ u ∈ GinfC (Vc D i), ∀ w', R.ptP i t (ψ' ((R.cV i).ρ u w')) = R.ωP i t (u, 1) (R.ptP i t (ψ' w'))) := by
  first | exact @GlobalTheory.LieEquivFock.lie_equivariant | exact GlobalTheory.LieEquivFock.lie_equivariant | (intros; apply GlobalTheory.LieEquivFock.lie_equivariant <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HolomorphicSectionsSpanLeStatement
section
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj GlobalTheory.CoverRead GlobalTheory.Member GlobalTheory.CompRat GlobalTheory.FinalJoin
open scoped TensorProduct Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.holomorphic_sections_span_le : ∀ (D : D7) (T : CoreJ D), LawsJ T → ∀ j, Formalism.L2.Pj.InR D j → ∀ σ : T.Q.c.F →+* ℂ, GoodEmb T.Q.c σ → ∀ w : WeightFamilies.Wt D j, w.LastPos → 0 < w.n → holSub0 (T.U j σ).X (laU (T.U j σ) (wtA w) w.n) ⊓ Submodule.span ℂ (rdU (T.U j σ) '' (sec (T.Q.Xo j) T.Q.c (wtA w) w.n : Set (Rul (T.Q.Xo j) T.Q.c))) ≤ Submodule.span ℂ (rdU (T.U j σ) '' {f | f ∈ sec (T.Q.Xo j) T.Q.c (wtA w) w.n ∧ rdU (T.U j σ) f ∈ holSub0 (T.U j σ).X (laU (T.U j σ) (wtA w) w.n)}) := by
  first | exact @GlobalTheory.CuspDescent.cusp_descends | exact GlobalTheory.CuspDescent.cusp_descends | (intros; apply GlobalTheory.CuspDescent.cusp_descends <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HolomorphicSectionsSpanRestriction
section
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj GlobalTheory.CoverRead GlobalTheory.Member GlobalTheory.CompRat GlobalTheory.FinalJoin
open scoped TensorProduct Matrix

noncomputable section

namespace GlobalTheory.CoverFormDesc

theorem mem_span_of_image_mem_span {K : Type} [Field K] {M : Type} [AddCommGroup M] [Module K M] {W : Type}
    [AddCommGroup W] [Module ℂ W] (σ : K →+* ℂ) (R : M →ₛₗ[σ] W) (S : Submodule K M)
    (hinj : ∀ (m : ℕ) (f : Fin m → M), (∀ i, f i ∈ S) → LinearIndependent K f → LinearIndependent ℂ (fun i => R (f i)))
    {k : ℕ} (g : Fin k → M) (hg : ∀ i, g i ∈ S) (f₂ : M) (hf : f₂ ∈ S)
    (hφ : R f₂ ∈ Submodule.span ℂ (Set.range fun i => R (g i))) : ∃ c : Fin k → K, ∑ i, c i • g i = f₂ := by
  refine (Submodule.mem_span_range_iff_exists_fun K).mp ?_
  by_contra hno
  set G := Submodule.span K (Set.range g) with hG
  haveI : FiniteDimensional K G := FiniteDimensional.span_of_finite _ (Set.finite_range g)
  let b := Module.finBasis K G
  let v : Fin (Module.finrank K G) → M := fun i => (b i : M)
  have hvsp : Submodule.span K (Set.range v) = G := by
    have : Set.range v = G.subtype '' Set.range b := by
      ext x; simp [v]
    rw [this, Submodule.span_image, b.span_eq, Submodule.map_top, Submodule.range_subtype]
  have hli : LinearIndependent K (Fin.cons f₂ v : Fin (Module.finrank K G + 1) → M) := by
    rw [linearIndependent_fin_cons]
    exact ⟨b.linearIndependent.map' G.subtype (Submodule.ker_subtype G), by rwa [hvsp]⟩
  have hsecG : G ≤ S := by
    rw [hG, Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    exact hg i
  have hin : ∀ i, (Fin.cons f₂ v : Fin (Module.finrank K G + 1) → M) i ∈ S := by
    intro i
    refine Fin.cases ?_ (fun i => ?_) i
    · simpa using hf
    · simpa using hsecG (b i).2
  have hC := hinj _ _ hin hli
  have hfun : (fun i => R ((Fin.cons f₂ v : Fin (Module.finrank K G + 1) → M) i)) =
      Fin.cons (R f₂) (fun i => R (v i)) := by
    funext i
    refine Fin.cases ?_ (fun i => ?_) i <;> simp
  rw [hfun, linearIndependent_fin_cons] at hC
  apply hC.2
  have hG' : ∀ x ∈ G, R x ∈ Submodule.span ℂ (Set.range fun i => R (v i)) := by
    intro x hx
    rw [← hvsp] at hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨i, rfl⟩ := hx
      exact Submodule.subset_span ⟨i, rfl⟩
    | zero => rw [map_zero]; exact Submodule.zero_mem _
    | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
    | smul c x _ hx => rw [map_smulₛₗ]; exact Submodule.smul_mem _ _ hx
  refine Submodule.span_le.mpr ?_ hφ
  rintro _ ⟨i, rfl⟩
  exact hG' _ (Submodule.subset_span ⟨i, rfl⟩)

def rdL {D : D7} {T : CoreJ D} {j : ℕ} {σ : T.Q.c.F →+* ℂ} (C : Cover T j σ) (a : (D.host.E →+* ℂ) × ℕ → ℕ) :
    Rul C.d.Xo₂ C.d.c₂ →ₛₗ[C.σ₂] (GA D (T.V j σ) → ℂ) :=
  (lieFac (T.Q.Dw j) (xiR D) a : ℂ) •
    ((adel (T.V j σ) C.dict₂ (muPin (T.V j σ) C.dict₂ (T.mu j σ) C.cc₂)).comp (rdU C.U₂))

theorem rd_eq {D : D7} {T : CoreJ D} {j : ℕ} {σ : T.Q.c.F →+* ℂ} (C : Cover T j σ) (a : (D.host.E →+* ℂ) × ℕ → ℕ)
    (f : Rul C.d.Xo₂ C.d.c₂) : C.rd a f = rdL C a f := rfl

theorem cover_form_desc : ∀ (D : D7) (T : CoreJ D), LawsJ T → ∀ j, Formalism.L2.Pj.InR D j → ∀ σ : T.Q.c.F →+* ℂ, GoodEmb T.Q.c σ → ∀ C : Cover T j σ, C.IsUnif → ∀ (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ), Dom a n → C.IsPinned a n → holSub0 (T.U j σ).X (laU (T.U j σ) a n) ≤ Submodule.span ℂ (rdU (T.U j σ) '' {f | f ∈ sec (T.Q.Xo j) T.Q.c a n ∧ rdU (T.U j σ) f ∈ holSub0 (T.U j σ).X (laU (T.U j σ) a n)}) → (∀ k ∈ T.Kf j σ, ∀ h, T.mu j σ (h * k) = T.mu j σ h) → ∀ φ ∈ C.ratForms a n, (∀ k ∈ T.Kf j σ, ∀ h, φ (h * k) = φ h) → ∃ (m : ℕ) (x : Fin m → C.d.c₂.F) (ψ : Fin m → (GA D (T.V j σ) → ℂ)), (∀ i, ψ i ∈ baseForms T j σ a n) ∧ φ = ∑ i, C.σ₂ (x i) • ψ i := by
  intro D T hL j hj σ hσ C hU a n hD hP hspan hmu φ hφ hφK
  have hsp : φ ∈ Submodule.span ℂ (baseForms T j σ a n) := GlobalTheory.T.coverForm_levelInvariant_mem_span_baseForms D T hL j hj σ hσ C hU a n hD hP hspan hmu φ hφ hφK
  obtain ⟨f₂, ⟨hf₂s, -⟩, rfl⟩ := hφ
  obtain ⟨m, z, ψ, hψ⟩ := Submodule.mem_span_set'.mp hsp
  have hup := (GlobalTheory.T.coreRationalForms_subset_coverForms D T hL j hj σ hσ C hU a n hD hP).1
  choose g hg hgψ using fun i => hup (ψ i).2
  have hinj : ∀ (m : ℕ) (f : Fin m → Rul C.d.Xo₂ C.d.c₂), (∀ i, f i ∈ sec C.d.Xo₂ C.d.c₂ a n) →
      LinearIndependent C.d.c₂.F f → LinearIndependent ℂ (fun i => rdL C a (f i)) :=
    fun m f hf hli => GlobalTheory.T.coverSections_linearIndependent_adelicReadings D T hL j hj σ hσ C hU hP.1 a n hD m f hf hli
  have hmem : rdL C a f₂ ∈ Submodule.span ℂ (Set.range fun i => rdL C a (g i)) := by
    rw [← rd_eq, ← hψ]
    refine Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ ?_
    rw [← hgψ i, rd_eq]
    exact Submodule.subset_span ⟨i, rfl⟩
  obtain ⟨c, hc⟩ := mem_span_of_image_mem_span C.σ₂ (rdL C a) (sec C.d.Xo₂ C.d.c₂ a n) hinj g (fun i => (hg i).1) f₂ hf₂s hmem
  refine ⟨m, c, fun i => (ψ i : GA D (T.V j σ) → ℂ), fun i => (ψ i).2, ?_⟩
  rw [← hc, rd_eq, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smulₛₗ, ← rd_eq, hgψ i]

end GlobalTheory.CoverFormDesc
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HoweDualityCompactPairRealPlacesIrreducibleStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.howeDuality_compactPair_realPlaces_irreducible : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.LiftRows.Given R F → R.FullP → ∀ (i : Fin D.R.m) (t : T) (M : Submodule ℂ ((R.cV i).W →ₗ[ℂ] PolF D (Wc D i).rank (Vc D i).rank)), (∀ ψ ∈ M, (∀ u ∈ GinfC (Vc D i), ∀ w', R.ptP i t (ψ ((R.cV i).ρ u w')) = R.ωP i t (u, 1) (R.ptP i t (ψ w')))) → (∀ ψ ∈ M, ∀ (τ : D.what₂.Tau) (Y : Matrix (Fin (Wc D i).rank) (Fin (Wc D i).rank) ℂ), Y ∈ lieAt (Wc D i) τ → ∀ ψ' : ((R.cV i).W →ₗ[ℂ] PolF D (Wc D i).rank (Vc D i).rank), (∀ w z, HasDerivAt (fun s : ℝ => R.ωP i t (1, oneP R.θ (Wc D i) τ Y s) (R.ptP i t (ψ w)) z) (R.ptP i t (ψ' w) z) 0) → ψ' ∈ M) → M ≠ ⊥ → ∀ φ : ((R.cV i).W →ₗ[ℂ] PolF D (Wc D i).rank (Vc D i).rank), (∀ u ∈ GinfC (Vc D i), ∀ w', R.ptP i t (φ ((R.cV i).ρ u w')) = R.ωP i t (u, 1) (R.ptP i t (φ w'))) → φ ∈ M := by
  first | exact @GlobalTheory.HoweIrrCompact.howe_irr | exact GlobalTheory.HoweIrrCompact.howe_irr | (intros; apply GlobalTheory.HoweIrrCompact.howe_irr <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PolynomialMemSpanLiftedMapsStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.polynomial_mem_span_lifted_maps : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.LiftRows.Given R F → R.FullP → ∀ (i : Fin D.R.m) (t : T), ∀ (P : PolF D (Wc D i).rank (Vc D i).rank), ∃ Q ∈ Submodule.span ℂ {Q : PolF D (Wc D i).rank (Vc D i).rank | ∃ (φ : (R.cV i).W →ₗ[ℂ] PolF D (Wc D i).rank (Vc D i).rank) (w : (R.cV i).W), (∀ u ∈ GinfC (Vc D i), ∀ w', R.ptP i t (φ ((R.cV i).ρ u w')) = R.ωP i t (u, 1) (R.ptP i t (φ w'))) ∧ Q = φ w}, ∃ E : Submodule ℂ (PolF D (Wc D i).rank (Vc D i).rank), FiniteDimensional ℂ E ∧ (∀ u ∈ GinfC (Vc D i), ∀ P₁ ∈ E, ∀ P₂ : PolF D (Wc D i).rank (Vc D i).rank, R.ptP i t P₂ = R.ωP i t (u, 1) (R.ptP i t P₁) → P₂ ∈ E) ∧ (∀ φ : PolF D (Wc D i).rank (Vc D i).rank →ₗ[ℂ] Module.Dual ℂ (R.cV i).W →ₗ[ℂ] ℂ, (∀ u ∈ GinfC (Vc D i), ∀ P₁ ∈ E, ∀ P₂ : PolF D (Wc D i).rank (Vc D i).rank, R.ptP i t P₂ = R.ωP i t (u, 1) (R.ptP i t P₁) → ∀ l, φ P₂ l = φ P₁ (l ∘ₗ (R.cV i).ρ u)) → ∀ P₁ ∈ E, φ P₁ = 0) ∧ P - Q ∈ E := by
  first | exact @GlobalTheory.FockIsotypic.decomp | exact GlobalTheory.FockIsotypic.decomp | (intros; apply GlobalTheory.FockIsotypic.decomp <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ProjectedLiftUnipotentTypeBaseLevelFormStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.TwSys GlobalTheory.TwAll GlobalTheory.SupLaw GlobalTheory.LiftLeaf
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0 FullRk SgJ BasisOf)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1600000
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.projectedLift_unipotentType_baseLevelForm : ∀ (D : D7) (X : RealSide D) (E : IntegralHeckeForms.XD D) (Y : SerSide X E) (i : D.ntw.Tw) (j : Fin D.R.m) (b : Bool) (t : X.T),
    X.R.xi t = (Y.Z.ρ.B i j b).de.chi → X.R.Q t = (Y.Z.ρ.B i j b).de.Q → ∀ y0 : (X.R.HV j t).H,
    (∀ (u : G0g D.nd) (hu : u ∈ D.nexp.U) (κ : GA D (Wc D j)),
        Lev.IsLevelLift (Wc D j) (Y.Z.ρ.B i j b).F.βT (Y.Z.ρ.B i j b).G.levT (Y.Z.ρ.eG i j b u) κ → ∀ g,
        (X.R.HW j (sg0 D X.A3.A)).e (X.R.thG j t y0) (X.geo.v₀ j _) (g * κ) =
          Y.Z.ρ.e i b ((D.nexp.psiU i b ⟨u, hu⟩ : (FractionRing (D.ntw.O i))ˣ) : FractionRing (D.ntw.O i)) *
          (X.R.HW j (sg0 D X.A3.A)).e (X.R.thG j t y0) (X.geo.v₀ j _) g) →
    ∃ y : (X.R.HV j t).H, (∀ (h : Bridge.Gf (Vc D j)) (k : (Y.Z.ρ.B i j b).levJ (Y.Z.ρ.tw i b 0 ∅ 1)),
        (X.R.HV j t).e y (h * (k : Bridge.Gf (Vc D j))) = (((Y.Z.ρ.B i j b).levLam (Y.Z.ρ.tw i b 0 ∅ 1) k : ℂˣ) : ℂ) • (X.R.HV j t).e y h) ∧
      (X.R.HW j (sg0 D X.A3.A)).e (X.R.thG j t y) (X.geo.v₀ j _) = (X.R.HW j (sg0 D X.A3.A)).e (X.R.thG j t y0) (X.geo.v₀ j _) := by
  first | exact @GlobalTheory.AvgLevel.avg_level | exact GlobalTheory.AvgLevel.avg_level | (intros; apply GlobalTheory.AvgLevel.avg_level <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RankinSelbergGLnGLmPartialLEqDivEntire
section
noncomputable section

open NumberField IsDedekindDomain MeasureTheory GlobalTheory.CuspRep GlobalTheory.JSW Formalism.UG GlobalTheory.LFun Formalism.L2.Host
open scoped ENNReal ComplexConjugate ContDiff

namespace GlobalTheory.RSnmUnf

theorem rs_nm_partialL_eq_div : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (n m : ℕ) (σ : CG E n) (σ' : CG E m), 1 ≤ m → m < n → σ.IsUnitary → σ'.IsUnitary → ∀ T : Finset (HeightOneSpectrum (𝓞 E)), (∀ w ∉ T, ∀ x : w.adicCompletion E, (∀ y ∈ Ov E w, GlobalTheory.JSW.psiLoc w (x * y) = 1) ↔ x ∈ Ov E w) → UnrOutside T σ → UnrOutside T σ' → ∃ F H : ℂ → ℂ, Differentiable ℂ F ∧ Differentiable ℂ H ∧ (∀ x : ℝ, 0 < (H x).re ∧ (H x).im = 0) ∧ ∀ x : ℝ, 1 < x → HasProd (fun w : {w : HeightOneSpectrum (𝓞 E) // w ∉ T} => locL (Ideal.absNorm w.1.asIdeal) (sat σ w.1) ((sat σ' w.1).map (Units.map (starRingEnd ℂ).toMonoidHom)) (x : ℂ)) (F x / H x) := by
  intro E _ _ _ n m σ σ' hm hmn hσ hσ' T hψ hT hT'
  obtain ⟨m₀, rfl⟩ : ∃ m₀, m = m₀ + 1 := ⟨m - 1, by omega⟩
  obtain ⟨r, rfl⟩ : ∃ r, n = m₀ + r + 1 + 1 := ⟨n - m₀ - 2, by omega⟩
  obtain ⟨α, _ℓ, _Φ, _J, _η, π, _ω, _φ, hα, hπ, hω, hωc, _h1, _h2, _h3, _h4, _h5, _h6, _h7, hZ⟩ :=
    GlobalTheory.T.unfolded_theta_integral_eq_mul_schur_euler_product E (m₀ + r + 1 + 1) σ (by omega) hσ T hT
  obtain ⟨β, _ℓ', _Φ', _J', _η', π', _ω', _φ', hβ, hπ', hω', hωc', _h1', _h2', _h3', _h4', _h5', _h6', _h7', hZ'⟩ :=
    GlobalTheory.T.unfolded_theta_integral_eq_mul_schur_euler_product E (m₀ + 1) σ' (by omega) hσ' T hT'
  subst hπ hπ'
  have hu : π.IsUnitary := (CG.isUnitary_mk π).1 hσ
  have hu' : π'.IsUnitary := (CG.isUnitary_mk π').1 hσ'
  have hfd : ∀ a : ℕ, ∃ (μ : Measure (GA E a)) (_ : μ.IsHaarMeasure) (𝓕 : Set (GA E a)) (𝓕₀ : Set (GA E a)),
      IsFundamentalDomain (ratGL E a).range 𝓕 μ ∧ IsFundamentalDomain (GlobalTheory.CellDec.NE E a) 𝓕₀ μ := by
    intro a
    haveI := GlobalTheory.CuspRep.CuspidalL2GL.locallyCompactSpace_GA E a
    haveI := GlobalTheory.CuspRep.CuspidalL2GL.t2Space_GA E a
    haveI := GlobalTheory.CuspRep.CuspidalL2GL.secondCountableTopology_GA E a
    haveI : DiscreteTopology (ratGL E a).range := GroundTheory.Automorphic.AdelicGLn.discreteTopology_rationalGL E a
    have hsub : (GlobalTheory.CellDec.NE E a : Set (GA E a)) ⊆ ((ratGL E a).range : Set (GA E a)) := by
      rintro _ ⟨u, -, rfl⟩
      exact ⟨u, rfl⟩
    haveI : DiscreteTopology (GlobalTheory.CellDec.NE E a) :=
      DiscreteTopology.of_subset (inferInstance : DiscreteTopology ((ratGL E a).range : Set (GA E a))) hsub
    obtain ⟨𝓕, -, -, h𝓕⟩ := GlobalTheory.exists_isFundamentalDomain_subgroup (ratGL E a).range
    obtain ⟨𝓕₀, -, -, h𝓕₀⟩ := GlobalTheory.exists_isFundamentalDomain_subgroup (GlobalTheory.CellDec.NE E a)
    exact ⟨Measure.haar, inferInstance, 𝓕, 𝓕₀, h𝓕 _, h𝓕₀ _⟩
  obtain ⟨μ₁, hμ₁, 𝓕₁, -, h𝓕₁, -⟩ := hfd (m₀ + r + 1 + 1)
  obtain ⟨μ, hμ, 𝓕, 𝓕₀, h𝓕, h𝓕₀⟩ := hfd (m₀ + 1)
  have hfin : ∀ x : ℝ, 1 < x → GlobalTheory.RSPole.eulD (fun w : {w : HeightOneSpectrum (𝓞 E) // w ∉ T} => Ideal.absNorm w.1.asIdeal)
      (fun w i => ((α w i : ℂˣ) : ℂ)) x ≠ ⊤ := fun x hx => by
    obtain ⟨H, -, -, h⟩ := hZ μ₁ 𝓕₁ h𝓕₁
    exact (h x hx).2.1
  have hfin' : ∀ x : ℝ, 1 < x → GlobalTheory.RSPole.eulD (fun w : {w : HeightOneSpectrum (𝓞 E) // w ∉ T} => Ideal.absNorm w.1.asIdeal)
      (fun w i => ((β w i : ℂˣ) : ℂ)) x ≠ ⊤ := fun x hx => by
    obtain ⟨H, -, -, h⟩ := hZ' μ 𝓕 h𝓕
    exact (h x hx).2.1
  classical
  let αe : HeightOneSpectrum (𝓞 E) → Fin (m₀ + r + 1 + 1) → ℂˣ := fun w => if h : w ∉ T then α ⟨w, h⟩ else fun _ => 1
  let βe : HeightOneSpectrum (𝓞 E) → Fin (m₀ + 1) → ℂˣ := fun w => if h : w ∉ T then β ⟨w, h⟩ else fun _ => 1
  have hαe : ∀ w : {w : HeightOneSpectrum (𝓞 E) // w ∉ T}, αe w.1 = α w := fun w => dif_pos w.2
  have hβe : ∀ w : {w : HeightOneSpectrum (𝓞 E) // w ∉ T}, βe w.1 = β w := fun w => dif_pos w.2
  have hsatσ : ∀ {a : ℕ} (ρ : CuspSub E a) (w : HeightOneSpectrum (𝓞 E)), (∃ B, (CG.mk ρ).HasSat w B) →
      HasSatGL w (ρ.locRep w) (sat (CG.mk ρ) w) := fun ρ w h => by
    rw [← CG.hasSat_mk, sat, dif_pos h]
    exact h.choose_spec
  have hsat : ∀ w ∉ T, HasSatGL w (π.locRep w) (Finset.univ.val.map (αe w)) := fun w hw => by
    rw [hαe ⟨w, hw⟩, hα ⟨w, hw⟩]; exact hsatσ π w (hT w hw)
  have hsat' : ∀ w ∉ T, HasSatGL w (π'.locRep w) (Finset.univ.val.map (βe w)) := fun w hw => by
    rw [hβe ⟨w, hw⟩, hβ ⟨w, hw⟩]; exact hsatσ π' w (hT' w hw)
  obtain ⟨φ, φ', κ, hφ, hφ', v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12, v13⟩ :=
    GlobalTheory.T.exists_matchedWhittakerVectors_shintaniRelations E m₀ r T hψ π π' hu hu' αe βe hsat hsat'
  obtain ⟨F, hF, hC⟩ := GlobalTheory.T.unfolded_rankinSelberg_cellIntegral_matchedVectors E m₀ r T hψ π π' hu hu' αe βe φ φ' κ hφ hφ' v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13
  obtain ⟨c, hc, hU⟩ := GlobalTheory.T.rankinSelbergGLnGLm_unfolding_to_mirabolic E m₀ r μ
  obtain ⟨f, t, hfm, htm, hf0, hfi, hfpos, hR, hid⟩ := hC μ 𝓕₀ h𝓕₀
  obtain ⟨hdiff, hreal⟩ := GlobalTheory.exp_integral_entire_real_pos (μ.restrict 𝓕₀) f t hfm htm hf0 hfi hR
  have hlt : m₀ + 1 < m₀ + r + 1 + 1 := by omega
  have hent := GlobalTheory.RSnmGood.rsIntegral_entire_good (by omega) hlt
    (GlobalTheory.RSnmGood.mspanR_le_goodFns (by omega) hu hφ) (GlobalTheory.RSnmGood.mspanR_le_goodFns (by omega) hu' hφ') hF μ h𝓕
  refine ⟨fun s => ∫ h in 𝓕, GlobalTheory.RSnm.rsIntegrand (m₀ + 1) hlt.le F φ φ' s h ∂μ,
    fun s => (c : ℂ) * ∫ g in 𝓕₀, (f g : ℂ) * Complex.exp (s * t g) ∂μ, fun s => (hent.2 s).differentiableAt,
    (differentiable_const _).mul hdiff, ?_, ?_⟩
  · intro x
    obtain ⟨him, hre⟩ := hreal x
    have hre' := hre hfpos
    refine ⟨?_, ?_⟩
    · simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
      exact mul_pos hc hre'
    · simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero, him, mul_zero]
  · intro x hx
    have hq : ∀ w : {w : HeightOneSpectrum (𝓞 E) // w ∉ T}, 2 ≤ Ideal.absNorm w.1.asIdeal :=
      fun w => HeightOneSpectrum.one_lt_absNorm w.1
    have e1 : (fun (w : {w : HeightOneSpectrum (𝓞 E) // w ∉ T}) (i : Fin (m₀ + r + 1 + 1)) => ((αe w.1 i : ℂˣ) : ℂ)) =
        fun w i => ((α w i : ℂˣ) : ℂ) := by funext w i; rw [hαe w]
    have e1' : (fun (w : {w : HeightOneSpectrum (𝓞 E) // w ∉ T}) (i : Fin (m₀ + 1)) => ((βe w.1 i : ℂˣ) : ℂ)) =
        fun w i => ((β w i : ℂˣ) : ℂ) := by funext w i; rw [hβe w]
    have hf1 := hfin x hx
    have hf1' := hfin' x hx
    rw [← e1] at hf1
    rw [← e1'] at hf1'
    obtain ⟨dd1, dd2, eq⟩ := hid x hx hf1 hf1'
    obtain ⟨-, eU⟩ := hU π π' hu hu' φ φ' hφ hφ' F hF 𝓕 𝓕₀ h𝓕 h𝓕₀ x dd1 dd2
    rw [e1] at hf1
    rw [e1'] at hf1'
    obtain ⟨P, hP, hS⟩ := GlobalTheory.T.eulerProduct_rankinSelbergGLnGLm_dirichletSeries (fun w : {w : HeightOneSpectrum (𝓞 E) // w ∉ T} => Ideal.absNorm w.1.asIdeal)
      (by omega : m₀ + 1 ≤ m₀ + r + 1 + 1) α β x hx hq hf1 hf1'
    have hsum : (∑' l : {w : HeightOneSpectrum (𝓞 E) // w ∉ T} →₀ (Fin (m₀ + 1) → ℤ),
        l.prod fun w v => GlobalTheory.RSnmUnf.rsTermNM (Ideal.absNorm w.1.asIdeal) (fun i => (αe w.1 i : ℂ))
          (fun i => (βe w.1 i : ℂ)) x v) = P := by
      simp only [hαe, hβe]
      exact hS.tsum_eq
    have hJ : (∫ g in 𝓕₀, (f g : ℂ) * Complex.exp ((x : ℂ) * t g) ∂μ) ≠ 0 := by
      intro h0
      have := (hreal x).2 hfpos
      rw [h0, Complex.zero_re] at this
      exact lt_irrefl _ this
    have hval : (∫ h in 𝓕, GlobalTheory.RSnm.rsIntegrand (m₀ + 1) hlt.le F φ φ' (x : ℂ) h ∂μ) /
        ((c : ℂ) * ∫ g in 𝓕₀, (f g : ℂ) * Complex.exp ((x : ℂ) * t g) ∂μ) = P := by
      rw [eU, eq, hsum]
      have hc0 : (c : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hc.ne'
      field_simp
    have hP' : HasProd (fun w : {w : HeightOneSpectrum (𝓞 E) // w ∉ T} => locL (Ideal.absNorm w.1.asIdeal)
        (sat (CG.mk π) w.1) ((sat (CG.mk π') w.1).map (Units.map (starRingEnd ℂ).toMonoidHom)) (x : ℂ)) P := by
      simp only [← hα, ← hβ]
      exact hP
    simpa only [hval] using hP'

end GlobalTheory.RSnmUnf
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RankinSelbergPartialLPoleAtOneConj
section
open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology GlobalTheory.CuspRep GlobalTheory.UnitaryBC GroundTheory.Global.IdeleGroup
  Formalism.L2.Host GlobalTheory.JSW
open scoped ENNReal nonZeroDivisors ComplexConjugate

noncomputable section

namespace GlobalTheory.RSPole

open GlobalTheory.CuspRep.CuspidalL2GL in

theorem exists_haar_fundamentalDomains : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ),
    ∃ (μ : Measure (GA E a)) (_ : μ.IsHaarMeasure) (𝓕 𝓕' : Set (GA E a)),
      IsFundamentalDomain (ratGL E a).range 𝓕 μ ∧ IsFundamentalDomain (latticeGL E a) 𝓕' μ := by
  intro E _ _ _ a
  haveI := CuspidalL2GL.locallyCompactSpace_GA E a
  haveI := CuspidalL2GL.t2Space_GA E a
  haveI := CuspidalL2GL.secondCountableTopology_GA E a
  haveI : DiscreteTopology (ratGL E a).range := GroundTheory.Automorphic.AdelicGLn.discreteTopology_rationalGL E a
  obtain ⟨𝓕, -, -, h𝓕⟩ := GlobalTheory.exists_isFundamentalDomain_subgroup (ratGL E a).range
  obtain ⟨𝓕', -, -, h𝓕'⟩ := GlobalTheory.exists_isFundamentalDomain_subgroup (latticeGL E a)
  exact ⟨Measure.haar, inferInstance, 𝓕, 𝓕', h𝓕 _, h𝓕' _⟩

open GlobalTheory.Petersson GlobalTheory.AutomorphicL2Unitary GlobalTheory.CuspRep.CuspidalL2GL in

theorem setIntegral_mul_conj_ne_zero_rapid {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ}
    (π₀ : CuspSub E a) (ω : HChar E) (hω : ω.IsUnitary) (hωc : π₀.HasCentChar ω) (φ : Sm E a)
    (hφ : φ ∈ π₀.V ∨ φ.1 ∈ GlobalTheory.JSW.mspanR π₀) (h0 : φ ≠ 0) (μ : Measure (GA E a)) [μ.IsHaarMeasure]
    (𝓕' : Set (GA E a)) (h𝓕 : IsFundamentalDomain (latticeGL E a) 𝓕' μ) :
    ∫ g in 𝓕', φ.1 g * starRingEnd ℂ (φ.1 g) ∂μ ≠ 0 := by
  have hR : φ.1 ∈ GlobalTheory.JSW.rspan π₀ := by
    rcases hφ with h | h
    · exact GlobalTheory.JSW.mem_rspan h
    · rw [GlobalTheory.JSW.rspan_eq_mspanR]; exact h
  have h1 : φ.1 ≠ 0 := fun e => h0 (Subtype.ext e)
  have hb : φ.1 ∈ bddForms E a ω :=
    (GlobalTheory.JSW.rspan_bdd_pet_eq_zero μ hω hωc (ψ := 0) (zero_mem _) (fun _ _ => by simp [pet, descend]) hR).1
  obtain ⟨r, hr, e⟩ := pet_self_pos μ hω hb h1
  rw [← (pet_eq_setIntegral hω hb hb h𝓕).2, e]
  exact_mod_cast hr.ne'

theorem rs_pole_conj : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (π : CG E a), 1 ≤ a → π.IsUnitary → ∀ T : Finset (HeightOneSpectrum (𝓞 E)), UnrOutside T π → ∃ L : ℝ → ℝ, (∀ x : ℝ, 1 < x → HasProd (fun w : {w : HeightOneSpectrum (𝓞 E) // w ∉ T} => locL (Ideal.absNorm w.1.asIdeal) (sat π w.1) ((sat π w.1).map (Units.map (starRingEnd ℂ).toMonoidHom)) (x : ℂ)) (L x : ℂ) ∧ 1 ≤ L x) ∧ ContinuousOn L (Set.Ioi 1) ∧ ∃ c : ℝ, 0 < c ∧ Tendsto (fun x => (x - 1) * L x) (𝓝[>] 1) (𝓝 c) := by
  intro E _ _ _ a π ha hπ T hT
  obtain ⟨α, ℓ, Φ, J, η, π₀, ω, φ, hα, hπ₀, hω, hωc, hφ, hφ0, hΦc, hΦs, hΦr, hΦpos, hΦ0, hZ⟩ := GlobalTheory.T.unfolded_theta_integral_eq_mul_schur_euler_product E a π ha hπ T hT
  set q : {w : HeightOneSpectrum (𝓞 E) // w ∉ T} → ℕ := fun w => Ideal.absNorm w.1.asIdeal with hqdef
  have hq : ∀ w, 2 ≤ q w := fun w => HeightOneSpectrum.one_lt_absNorm w.1
  obtain ⟨μ, hμ, 𝓕, 𝓕', h𝓕, h𝓕'⟩ := exists_haar_fundamentalDomains E a
  obtain ⟨H, hHc, hH1, hZH'⟩ := hZ μ 𝓕 h𝓕
  have hZH : ∀ x : ℝ, 1 < x → _ := fun x hx => (hZH' x hx).2
  have hHpos : ∀ x : ℝ, 1 < x → 0 < H x := fun x hx => (hZH' x hx).1
  set D : ℝ → ℝ := fun x => (eulD q (fun w i => ((α w i : ℂˣ) : ℂ)) x).toReal with hDdef
  obtain ⟨hprod, hcont⟩ := GlobalTheory.T.hasProd_localRankinSelbergFactor_self_of_eulerProduct _ q a α hq fun x hx => (hZH x hx).1
  refine ⟨D, fun x hx => ?_, hcont, ?_⟩
  · have e : (fun w : {w : HeightOneSpectrum (𝓞 E) // w ∉ T} => locL (Ideal.absNorm w.1.asIdeal) (sat π w.1)
        ((sat π w.1).map (Units.map (starRingEnd ℂ).toMonoidHom)) (x : ℂ)) = fun w => locL (q w)
        (Finset.univ.val.map (α w)) ((Finset.univ.val.map (α w)).map (Units.map (starRingEnd ℂ).toMonoidHom)) (x : ℂ) := by
      funext w; rw [hα w]
    rw [e]
    exact hprod x hx
  · obtain ⟨c, hc0, hlim⟩ := GlobalTheory.T.rankinSelberg_theta_integral_pole_rapid_kernel_span E a ℓ Φ hΦc hΦs hΦr J η μ 𝓕 𝓕' h𝓕 h𝓕'
    have hc : c ≠ 0 := hc0 hΦpos hΦ0
    have hT2 := (hlim π₀ π₀ ω hω hωc hωc φ φ hφ hφ).2
    have hP := setIntegral_mul_conj_ne_zero_rapid π₀ ω hω hωc φ hφ hφ0 μ 𝓕' h𝓕'
    set P := ∫ g in 𝓕', φ.1 g * starRingEnd ℂ (φ.1 g) ∂μ
    have hH : Tendsto (fun x : ℝ => ((H x : ℝ) : ℂ)) (𝓝[>] 1) (𝓝 ((H 1 : ℝ) : ℂ)) :=
      (Complex.continuous_ofReal.tendsto _).comp hHc
    have hH0 : ((H 1 : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hH1.ne'
    have hdiv := hT2.div hH hH0
    have hev : ∀ᶠ x in 𝓝[>] (1 : ℝ), ((x - 1 : ℝ) : ℂ) * thetaZ μ 𝓕 ℓ φ.1 φ.1 Φ J η x / ((H x : ℝ) : ℂ) =
        (((x - 1) * D x : ℝ) : ℂ) := by
      filter_upwards [self_mem_nhdsWithin] with x hx
      rw [(hZH x hx).2]
      have : ((H x : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (hHpos x hx).ne'
      simp only [hDdef]
      push_cast
      field_simp
    have hlim2 : Tendsto (fun x : ℝ => (((x - 1) * D x : ℝ) : ℂ)) (𝓝[>] 1) (𝓝 (c * P / ((H 1 : ℝ) : ℂ))) :=
      (hdiv.congr' hev)
    have hre := (Complex.continuous_re.tendsto _).comp hlim2
    have him := (Complex.continuous_im.tendsto _).comp hlim2
    simp only [Function.comp_def, Complex.ofReal_re, Complex.ofReal_im] at hre him
    have him0 : (c * P / ((H 1 : ℝ) : ℂ)).im = 0 := tendsto_nhds_unique tendsto_const_nhds him |>.symm
    have hne : c * P / ((H 1 : ℝ) : ℂ) ≠ 0 := div_ne_zero (mul_ne_zero hc hP) hH0
    have hnn : 0 ≤ (c * P / ((H 1 : ℝ) : ℂ)).re := by
      refine ge_of_tendsto hre ?_
      filter_upwards [self_mem_nhdsWithin] with x hx
      have hx' : (1 : ℝ) < x := hx
      have h1 := (hprod x hx').2
      exact mul_nonneg (by linarith) (by linarith)
    refine ⟨_, lt_of_le_of_ne hnn fun h0 => hne (Complex.ext h0.symm him0), hre⟩

end GlobalTheory.RSPole
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RealRationalPointActsHarmonicSubstitutionStatement
section
open NumberField Matrix Complex IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.SingleDatum GlobalTheory.CoverRead
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
open GlobalTheory.LevelSeries

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.real_rational_point_acts_harmonic_substitution : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (V W : HSp D) (χV χW : (AE D)ˣ →* Circle) (om : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)) (ΛV : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) (ΛW : Submodule (𝓞 D.host.E) (Fin W.rank → D.host.E)) (sW : D.what₂.Tau → Matrix (Fin W.rank) (Fin W.rank) ℂ) (f₀ : WO V W → ℂ), VacPair ψ θ V W χV χW om ΛV ΛW sW f₀ → ∀ (H : Geo.Tor.Host D.host.E) (Dw : Datum H) (BW : D.what₂.Tau → Matrix (Fin W.rank) (Fin W.rank) ℂ) (lt : LtN Dw V.rank ≃ FVar D W.rank V.rank) (wa : (D.host.E →+* ℂ) × ℕ → ℕ), W.rank = Dw.p + Dw.q → (∀ τ : D.host.E →+* ℂ, InPsi H τ ↔ ∃ ρ, τ = tauE D ρ) → (∀ τ, IsONBasis (gramAt D W τ) (sW τ) (BW τ) Dw.p) → IsLetters Dw lt → ∀ l c : ℕ, ∃ c' : ℕ, ∀ (γ a : GA D V) (γ' : GL (Fin V.rank) D.host.E) (O : Subring ℂ), γ ∈ GQ V → GlobalTheory.Member.IsRat V γ γ' → a ∈ GinfC V → γ * a ∈ GfC V → (∀ (τ : D.host.E →+* ℂ) x y, (l : ℂ) ^ c * τ (γ'.val x y) ∈ O ∧ (l : ℂ) ^ c * τ (γ'⁻¹.val x y) ∈ O) → ∀ Q ∈ HHa Dw.mult V.rank ℂ ComplexEmbedding.conjugate (InPsi H) (fun τ i => wa (τ, i)), (∀ mo, Q.coeff mo ∈ O) → ∃ Q' ∈ HHa Dw.mult V.rank ℂ ComplexEmbedding.conjugate (InPsi H) (fun τ i => wa (τ, i)), (∀ mo, Q'.coeff mo ∈ O) ∧ ∀ (M : ℕ) (e : AE D) (O₁ : Subring ℂ), M ≠ 0 → ∀ f ∈ trSp ψ V W ΛV ΛW f₀ e M O₁, ((l : ℂ) ^ c') • om (a, 1) (stdF ψ θ V W sW BW f (MvPolynomial.rename lt Q)) = stdF ψ θ V W sW BW f (MvPolynomial.rename lt Q') := by
  first | exact @GlobalTheory.LevelSeries.ArchAct.real_act_harm | exact GlobalTheory.LevelSeries.ArchAct.real_act_harm | (intros; apply GlobalTheory.LevelSeries.ArchAct.real_act_harm <;> assumption)
end

