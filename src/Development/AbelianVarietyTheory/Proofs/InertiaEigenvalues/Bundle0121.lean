import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0104
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0001
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnitLemmaGroup
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.NatCardAlgHomEqFinrankOfIsReducedOfIsFractionRin
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0087
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0001
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0050
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0091
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0073
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0097
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0096
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0112
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0098
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0002
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0075
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0105
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0086
import ReciprocityTheory.GaloisValuations.Global

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InducedRepresentationCharacterStatement
section
open GlobalTheory.Published
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.induced_representation_character : ∀ (G : Type) [Group G] [Fintype G] (H : Subgroup G) (χ : H →* ℂˣ), ∃ (R : Representation ℂ G (Fin H.index → ℂ)) (v : Fin H.index → ℂ), (∀ σ : H, R σ v = (χ σ : ℂ) • v) ∧ Submodule.span ℂ (Set.range fun g => R g v) = ⊤ ∧ ∀ g, LinearMap.trace ℂ (Fin H.index → ℂ) (R g) = indFun H (fun x => (χ x : ℂ)) g := by
  first | exact @GlobalTheory.InertiaEigenvalues.inducedRep_cyclic_trace | exact GlobalTheory.InertiaEigenvalues.inducedRep_cyclic_trace | (intros; apply GlobalTheory.InertiaEigenvalues.inducedRep_cyclic_trace <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IntegralClosureFgDvrOfSeparableCharpoly
section
open GlobalTheory.UnitLemma Polynomial Module

namespace GlobalTheory.IntClosureSep

theorem isRoot_minpoly_of_isRoot_charpoly {E A L : Type} [Field E] [CommRing A] [Algebra E A]
    [Module.Finite E A] [Field L] [Algebra E L] (g : A) {α : L}
    (hα : ((LinearMap.mulLeft E g).charpoly.map (algebraMap E L)).IsRoot α) :
    ((minpoly E g).map (algebraMap E L)).IsRoot α := by
  classical
  let b := Module.finBasis E A
  set M := Algebra.leftMulMatrix b g with hM
  have hQ : (LinearMap.mulLeft E g).charpoly = M.charpoly := by
    rw [← LinearMap.charpoly_toMatrix (LinearMap.mulLeft E g) b]; rfl
  set M' := M.map (algebraMap E L) with hM'
  have h1 : Module.End.HasEigenvalue (Matrix.toLin' M') α := by
    rw [Module.End.hasEigenvalue_iff_isRoot_charpoly, Matrix.charpoly_toLin', Matrix.charpoly_map,
      ← hQ]
    exact hα
  obtain ⟨v, hv⟩ := h1.exists_hasEigenvector
  have h2 : aeval M (minpoly E g) = 0 := by
    rw [hM, Polynomial.aeval_algHom_apply, minpoly.aeval, map_zero]
  have h3 : aeval M' ((minpoly E g).map (algebraMap E L)) = 0 := by
    rw [aeval_map_algebraMap]
    have : M' = (Algebra.ofId E L).mapMatrix M := rfl
    rw [this, Polynomial.aeval_algHom_apply, h2, map_zero]
  have h4 := Module.End.aeval_apply_of_hasEigenvector (p := (minpoly E g).map (algebraMap E L)) hv
  have h5 : aeval (Matrix.toLin' M') ((minpoly E g).map (algebraMap E L)) = 0 := by
    have : Matrix.toLin' M' = Matrix.toLinAlgEquiv' M' := rfl
    rw [this, Polynomial.aeval_algEquiv, AlgHom.comp_apply, h3, map_zero]
  rw [h5, LinearMap.zero_apply] at h4
  exact (smul_eq_zero.mp h4.symm).resolve_right hv.2

theorem integralClosure_fg_of_separable_charpoly : ∀ (O E A : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field E] [Algebra O E] [IsFractionRing O E] [CommRing A] [Algebra O A] [Algebra E A] [IsScalarTower O E A] [Module.Finite E A] (g : A), (LinearMap.mulLeft E g).charpoly.Separable → (Subalgebra.toSubmodule (integralClosure O A)).FG := by
  intro O E A _ _ _ _ _ _ _ _ _ _ _ g hsep
  classical
  rcases subsingleton_or_nontrivial A with hA | hA
  · rw [Subsingleton.elim (Subalgebra.toSubmodule (integralClosure O A)) ⊥]
    exact Submodule.fg_bot
  let L := AlgebraicClosure E
  set Q := (LinearMap.mulLeft E g).charpoly with hQ
  set n := finrank E A with hn
  have hQdeg : Q.natDegree = n := LinearMap.charpoly_natDegree _
  set R := (Q.map (algebraMap E L)).roots with hR
  have hRnodup : R.Nodup := nodup_roots (hsep.map)
  have hRcard : Multiset.card R = n := by
    rw [hR, IsAlgClosed.card_roots_eq_natDegree, natDegree_map, hQdeg]
  set m := minpoly E g with hm
  have hsub : ∀ α ∈ R, aeval α m = 0 := fun α hα => by
    have := isRoot_minpoly_of_isRoot_charpoly g (isRoot_of_mem_roots hα)
    rwa [IsRoot, eval_map_algebraMap] at this
  have hm_ne : m ≠ 0 := minpoly.ne_zero (Algebra.IsIntegral.isIntegral g)
  have hdeg_ge : n ≤ m.natDegree := by
    have hle : R ≤ (m.map (algebraMap E L)).roots := (Multiset.le_iff_subset hRnodup).mpr
      fun α hα => by
        rw [mem_roots (Polynomial.map_ne_zero hm_ne), IsRoot, eval_map_algebraMap]
        exact hsub α hα
    calc n = Multiset.card R := hRcard.symm
      _ ≤ _ := Multiset.card_le_card hle
      _ ≤ (m.map (algebraMap E L)).natDegree := card_roots' _
      _ = m.natDegree := natDegree_map _
  have hdeg_le : m.natDegree ≤ n := by
    simpa using (linearIndependent_pow (K := E) g).fintype_card_le_finrank
  have hdeg : m.natDegree = n := le_antisymm hdeg_le hdeg_ge
  haveI : Nonempty (Fin m.natDegree) := ⟨⟨0, by rw [hdeg, hn]; exact Module.finrank_pos⟩⟩
  let pb : PowerBasis E A :=
    { gen := g, dim := m.natDegree
      basis := basisOfLinearIndependentOfCardEqFinrank (linearIndependent_pow g) (by simp [hdeg, m, n])
      basis_eq_pow := fun i => by rw [coe_basisOfLinearIndependentOfCardEqFinrank] }
  let ι : Type := ↥R.toFinset
  have hcard : Fintype.card ι = n := by
    rw [Fintype.card_coe, Multiset.toFinset_card_of_nodup hRnodup, hRcard]
  let P : ι → (A →ₐ[E] L) := fun α => pb.lift α.1 (hsub α.1 (Multiset.mem_toFinset.mp α.2))
  have hP : Function.Injective P := fun a b h => Subtype.ext (by
    have h' : (P a) pb.gen = (P b) pb.gen := congrArg (fun f : A →ₐ[E] L => f pb.gen) h
    simpa only [P, PowerBasis.lift_gen] using h')
  let b0 : Basis ι E A := (Module.finBasisOfFinrankEq E A hcard.symm).reindex (Fintype.equivFin ι).symm
  have hex : ∀ i, ∃ c : nonZeroDivisors O, IsIntegral O ((c : O) • b0 i) := fun i =>
    IsIntegral.exists_multiple_integral_of_isLocalization (nonZeroDivisors O) (b0 i)
      (Algebra.IsIntegral.isIntegral (R := E) (b0 i))
  choose c hc using hex
  let e : Basis ι E A := b0.isUnitSMul (w := fun i => algebraMap O E (c i))
    (fun i => (IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors (c i).2).isUnit)
  have he : ∀ i, e i = (c i : O) • b0 i := fun i => by
    simp [e, Basis.isUnitSMul_apply, algebraMap_smul]
  have he_int : ∀ i, IsIntegral O (e i) := fun i => (he i) ▸ hc i
  have hdisc : Algebra.discr E e ≠ 0 := fun h =>
    GlobalTheory.algebraMap_discr_basis_ne_zero e hP (by rw [h, map_zero])
  have hnd : (Algebra.traceForm E A).Nondegenerate := by
    have hT : LinearMap.BilinForm.toMatrix e (Algebra.traceForm E A) = Algebra.traceMatrix E e := by
      ext i j
      rw [Algebra.traceForm_toMatrix, Algebra.traceMatrix_apply, Algebra.traceForm_apply]
    rw [LinearMap.BilinForm.nondegenerate_iff_det_ne_zero e, hT]
    exact hdisc
  have htr : ∀ x : A, IsIntegral O x → ∃ r : O, algebraMap O E r = Algebra.trace E A x := by
    intro x hx
    have h1 : IsIntegral O (algebraMap E L (Algebra.trace E A x)) := by
      rw [GlobalTheory.algebraMap_trace_eq_sum_algHom_of_card hcard hP x]
      refine IsIntegral.sum _ fun j _ => ?_
      exact hx.map ((P j).restrictScalars O)
    have h2 : IsIntegral O (Algebra.trace E A x) :=
      (isIntegral_algHom_iff ((Algebra.ofId E L).restrictScalars O)
        (algebraMap E L).injective).mp h1
    exact IsIntegrallyClosed.isIntegral_iff.mp h2
  set d := (Algebra.traceForm E A).dualBasis hnd e
  have hle : Subalgebra.toSubmodule (integralClosure O A) ≤ Submodule.span O (Set.range d) := by
    intro x hx
    have hx' : IsIntegral O x := hx
    rw [← d.sum_repr x]
    refine Submodule.sum_mem _ fun i _ => ?_
    rw [LinearMap.BilinForm.dualBasis_repr_apply, Algebra.traceForm_apply]
    obtain ⟨r, hr⟩ := htr _ (hx'.mul (he_int i))
    rw [← hr, algebraMap_smul]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  exact Submodule.FG.of_le (Submodule.fg_span (Set.finite_range d)) hle

end GlobalTheory.IntClosureSep
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IntegralClosureFgFiniteEtaleDvrStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integralClosure_fg_finiteEtale_dvr : ∀ (O E A : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field E] [Algebra O E] [IsFractionRing O E] [CommRing A] [Algebra O A] [Algebra E A] [IsScalarTower O E A] [Module.Finite E A] [Algebra.Etale E A], (Subalgebra.toSubmodule (integralClosure O A)).FG := by
  first | exact @GlobalTheory.IntegralClosureFG.integralClosure_fg | exact GlobalTheory.IntegralClosureFG.integralClosure_fg | (intros; apply GlobalTheory.IntegralClosureFG.integralClosure_fg <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IntegralGLSetIsOpenAndIsCompactStatement
section
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integralGLSet_isOpen_and_isCompact : ∀ (F : Type) [NontriviallyNormedField F] [IsUltrametricDist F] [ProperSpace F] (n : ℕ), IsOpen (glO n F) ∧ IsCompact (glO n F) := by
  first | exact @GlobalTheory.JR.GLift.glO_isOpen_isCompact | exact GlobalTheory.JR.GLift.glO_isOpen_isCompact | (intros; apply GlobalTheory.JR.GLift.glO_isOpen_isCompact <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InvariantImageOpenClosedLocalSections
section
open GlobalTheory.JR Matrix MeasureTheory Filter Topology

noncomputable section

namespace GlobalTheory.JR.ImgSec

theorem charpoly_companion_coeff : ∀ (k : Type) [CommRing k] (r : ℕ) (p : Fin r → k) (i : Fin r), (companion p).charpoly.coeff (i : ℕ) = p i := GlobalTheory.T.companionMatrixOfCoeffs_charpoly_coeff_eq
theorem exists_compact_open_nhd : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (r : ℕ) (U : Set (Inv r F)) (a₀ : Inv r F), IsOpen U → a₀ ∈ U → ∃ Ω : Set (Inv r F), IsCompact Ω ∧ IsOpen Ω ∧ a₀ ∈ Ω ∧ Ω ⊆ U := GlobalTheory.T.borderedMatrixInvariantSpace_exists_compact_open_subset
theorem isCompact_orbit : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (r : ℕ) (Ω : Set (Inv r F)) (s : Inv r F → Hn r F E) (h : Inv r F → Matrix (Fin r) (Fin r) E), IsCompact Ω → ContinuousOn s Ω → ContinuousOn h Ω → (∀ a ∈ Ω, IsUnit (h a).det ∧ Bm (s a).toGl = h a) → ∀ C : Set (Hn r F E), IsCompact C → IsCompact {p : Matrix.unitaryGroup (Fin r) E × Inv r F | p.2 ∈ Ω ∧ actU p.1 (s p.2) ∈ C} := GlobalTheory.T.unitaryOrbit_proper_of_invertible_krylovColumns
theorem continuousOn_mkX : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (r : ℕ) (Ω : Set (Inv r F)) (h : Inv r F → Matrix (Fin r) (Fin r) E), ContinuousOn h Ω → (∀ a ∈ Ω, IsUnit (h a).det) → ContinuousOn (fun a => GlobalTheory.JR.ImgSec.mkX a (h a)) Ω := GlobalTheory.T.continuousOn_hermitianBlockMatrixOfInvariants

variable {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E]
  [Unram F E] {r : ℕ}

theorem hasInv_mkX {a : Inv r F} {h : Matrix (Fin r) (Fin r) E} (hh : hᴴ * h = (hankel a).map (algebraMap F E))
    (hd : IsUnit h.det) : HasInv (mkX a h) a := by
  unfold HasInv inv
  refine Prod.ext ?_ (Prod.ext ?_ ?_)
  · funext i
    show ((mkX a h).1.1).charpoly.coeff i = algebraMap F E (a.1 i)
    rw [mkX_fst hh hd]
    let u : (Matrix (Fin r) (Fin r) E)ˣ := Matrix.nonsingInvUnit h hd
    have e : h * (companion a.1).map (algebraMap F E) * h⁻¹ =
        (u : Matrix (Fin r) (Fin r) E) * (companion a.1).map (algebraMap F E) *
          (u : Matrix (Fin r) (Fin r) E)⁻¹ := rfl
    rw [e, Matrix.charpoly_units_conj, Matrix.charpoly_map, Polynomial.coeff_map, charpoly_companion_coeff]
  · funext i; exact mom_mkX hh hd i
  · rfl

end GlobalTheory.JR.ImgSec

open GlobalTheory.JR.ImgSec in

theorem GlobalTheory.JR.image_openClosed_section : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (r : ℕ) (a₀ : Inv r F), Delta a₀ ≠ 0 → ((¬ ∃ X : Hn r F E, HasInv X a₀) → ∀ᶠ a in 𝓝 a₀, ¬ ∃ X : Hn r F E, HasInv X a) ∧ ((∃ X : Hn r F E, HasInv X a₀) → ∃ (Ω : Set (Inv r F)) (s : Inv r F → Hn r F E), IsCompact Ω ∧ IsOpen Ω ∧ a₀ ∈ Ω ∧ ContinuousOn s Ω ∧ (∀ a ∈ Ω, Delta a ≠ 0 ∧ HasInv (s a) a) ∧ ∀ C : Set (Hn r F E), IsCompact C → IsCompact {p : Matrix.unitaryGroup (Fin r) E × Inv r F | p.2 ∈ Ω ∧ actU p.1 (s p.2) ∈ C}) := by
  intro F E _ _ _ _ _ r a₀ hΔ
  haveI := continuousStar (E := E) F
  obtain ⟨-, -, -, hcrit⟩ := GlobalTheory.T.unitary_action_hermitian_invariants_transitive F E r
  obtain ⟨Ω₁, κ, hΩ₁, hH₀, hκ, -, hκeq⟩ := GlobalTheory.T.exists_continuous_congruence_near_symmetric_matrix F E r (hankel a₀) (hankel_isSymm a₀) hΔ
  set φ := algebraMap F E with hφ
  let U : Set (Inv r F) := {a | Delta a ≠ 0} ∩ (fun a => hankel a) ⁻¹' Ω₁
  have hU : IsOpen U := (isOpen_ne_fun continuous_delta continuous_const).inter (hΩ₁.preimage continuous_hankel)
  have ha₀ : a₀ ∈ U := ⟨hΔ, hH₀⟩
  have hK : ∀ a ∈ U, (κ (hankel a))ᵀ * hankel a₀ * κ (hankel a) = hankel a :=
    fun a ha => hκeq _ ha.2 (hankel_isSymm a)
  have hKd : ∀ a ∈ U, IsUnit (κ (hankel a)).det := by
    intro a ha
    refine isUnit_iff_ne_zero.2 fun h0 => ha.1 ?_
    have := congrArg Matrix.det (hK a ha)
    rw [det_mul, det_mul, h0, mul_zero] at this
    exact this.symm
  have hdm : ∀ M : Matrix (Fin r) (Fin r) F, (M.map φ).det = φ M.det := fun M => (RingHom.map_det φ M).symm
  have hKd' : ∀ a ∈ U, IsUnit ((κ (hankel a)).map φ).det := fun a ha => by
    rw [hdm]; exact (hKd a ha).map φ
  have hmapK : ∀ a ∈ U, ((κ (hankel a)).map φ)ᴴ * ((hankel a₀).map φ * (κ (hankel a)).map φ) = (hankel a).map φ := by
    intro a ha
    rw [ImgSec.conjTranspose_map, ← Matrix.map_mul, ← Matrix.map_mul, ← Matrix.mul_assoc, hK a ha]
  have transport : ∀ a ∈ U, (∃ h : Matrix (Fin r) (Fin r) E, hᴴ * h = (hankel a).map φ) →
      ∃ h : Matrix (Fin r) (Fin r) E, hᴴ * h = (hankel a₀).map φ := by
    rintro a ha ⟨h, hh⟩
    set K' := (κ (hankel a)).map φ
    have hu' : IsUnit K'ᴴ.det := by rw [det_conjTranspose]; exact (hKd' a ha).star
    refine ⟨h * K'⁻¹, ?_⟩
    rw [conjTranspose_mul, conjTranspose_nonsing_inv]
    calc K'ᴴ⁻¹ * hᴴ * (h * K'⁻¹) = K'ᴴ⁻¹ * (hᴴ * h) * K'⁻¹ := by simp only [Matrix.mul_assoc]
      _ = K'ᴴ⁻¹ * (K'ᴴ * ((hankel a₀).map φ * K')) * K'⁻¹ := by rw [hh, ← hmapK a ha]
      _ = (hankel a₀).map φ := by
        rw [nonsing_inv_mul_cancel_left _ _ hu', mul_nonsing_inv_cancel_right _ _ (hKd' a ha)]
  refine ⟨fun hno => ?_, fun hex => ?_⟩
  · filter_upwards [hU.mem_nhds ha₀] with a ha
    rintro ⟨X, hX⟩
    apply hno
    rw [hcrit a₀ hΔ]
    exact transport a ha ((hcrit a ha.1).1 ⟨X, hX⟩)
  · obtain ⟨h₀, hh₀⟩ := (hcrit a₀ hΔ).1 hex
    have hd₀ : IsUnit h₀.det := by
      refine isUnit_iff_ne_zero.2 fun h0 => ?_
      have := congrArg Matrix.det hh₀
      rw [det_mul, h0, mul_zero, hdm] at this
      exact hΔ ((map_eq_zero_iff φ φ.injective).1 this.symm)
    obtain ⟨Ω, hΩc, hΩo, ha₀Ω, hΩU⟩ := exists_compact_open_nhd F E r U a₀ hU ha₀
    let hf : Inv r F → Matrix (Fin r) (Fin r) E := fun a => h₀ * (κ (hankel a)).map φ
    have hhf : ∀ a ∈ U, (hf a)ᴴ * hf a = (hankel a).map φ := by
      intro a ha
      simp only [hf]
      rw [conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc h₀ᴴ, hh₀, hmapK a ha]
    have hdf : ∀ a ∈ U, IsUnit (hf a).det := fun a ha => by
      simp only [hf]; rw [det_mul]; exact hd₀.mul (hKd' a ha)
    have hcf : ContinuousOn hf Ω := by
      have h1 : ContinuousOn (fun a => κ (hankel a)) Ω :=
        hκ.comp continuous_hankel.continuousOn fun a ha => (hΩU ha).2
      exact continuousOn_const.mul ((continuous_id.matrix_map (continuous_algebraMap F E)).comp_continuousOn h1)
    have hcs : ContinuousOn (fun a => mkX a (hf a)) Ω :=
      continuousOn_mkX F E r Ω hf hcf fun a ha => hdf a (hΩU ha)
    refine ⟨Ω, fun a => mkX a (hf a), hΩc, hΩo, ha₀Ω, hcs,
      fun a ha => ⟨(hΩU ha).1, hasInv_mkX (hhf a (hΩU ha)) (hdf a (hΩU ha))⟩, ?_⟩
    intro C hC
    exact isCompact_orbit F E r Ω (fun a => mkX a (hf a)) hf hΩc hcs hcf
      (fun a ha => ⟨hdf a (hΩU ha), bm_mkX (hhf a (hΩU ha)) (hdf a (hΩU ha))⟩) C hC
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InvolutionIdempotentDecompositionOfSeparableChar
section
open GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Desc Polynomial Filter Topology

noncomputable section

namespace GlobalTheory.UnitLemma.Desc

open Classical

section Generic

variable {R : Type} [CommRing R]

def FieldIdem (f : R) : Prop :=
  IsIdempotentElem f ∧ f ≠ 0 ∧ ∀ y, f * y ≠ 0 → ∃ z, f * y * z = f

theorem FieldIdem.mul_eq_left {u v : R} (hu : FieldIdem u) (hv : IsIdempotentElem v) (h : u * v ≠ 0) :
    u * v = u := by
  obtain ⟨z, hz⟩ := hu.2.2 v h
  calc u * v = (u * v * z) * v := by rw [hz]
    _ = u * v * z * v := rfl
    _ = u * (v * v) * z := by ring
    _ = u := by rw [hv.eq, hz]

theorem FieldIdem.eq_of_mul_ne_zero {u v : R} (hu : FieldIdem u) (hv : FieldIdem v) (h : u * v ≠ 0) :
    u = v := by
  have h1 : u * v = u := hu.mul_eq_left hv.1 h
  have h2 : v * u = v := hv.mul_eq_left hu.1 (by rwa [mul_comm])
  calc u = u * v := h1.symm
    _ = v * u := mul_comm _ _
    _ = v := h2

theorem FieldIdem.map {u : R} (hu : FieldIdem u) (σ : R ≃+* R) : FieldIdem (σ u) := by
  refine ⟨?_, ?_, ?_⟩
  · show σ u * σ u = σ u
    rw [← map_mul, hu.1.eq]
  · intro h0
    exact hu.2.1 (σ.injective (by rw [h0, map_zero]))
  · intro y hy
    have hy' : u * σ.symm y ≠ 0 := by
      intro h0
      apply hy
      have h1 := congrArg σ h0
      rwa [map_mul, RingEquiv.apply_symm_apply, map_zero] at h1
    obtain ⟨z, hz⟩ := hu.2.2 _ hy'
    refine ⟨σ z, ?_⟩
    have h1 := congrArg σ hz
    rwa [map_mul, map_mul, RingEquiv.apply_symm_apply] at h1

theorem exists_fieldIdem_family [IsReduced R] [IsArtinianRing R] :
    ∃ (M : Type) (_ : Fintype M) (f : M → R), CompleteOrthogonalIdempotents f ∧ ∀ m, FieldIdem (f m) := by

  let φ := IsArtinianRing.equivPi R
  have : Fintype (MaximalSpectrum R) := Fintype.ofFinite _
  have hc : CompleteOrthogonalIdempotents (fun m : MaximalSpectrum R => φ.symm (Pi.single m 1)) :=
    (CompleteOrthogonalIdempotents.single (fun I : MaximalSpectrum R => R ⧸ I.asIdeal)).map
      φ.symm.toRingEquiv.toRingHom
  refine ⟨MaximalSpectrum R, inferInstance, fun m => φ.symm (Pi.single m 1), hc, fun m => ?_⟩
  refine ⟨hc.idem m, ?_, ?_⟩
  · intro h0
    have h1 := congrArg (fun x => φ x m) h0
    simp only [AlgEquiv.apply_symm_apply, map_zero, Pi.single_eq_same, Pi.zero_apply] at h1
    exact one_ne_zero h1
  · intro y hy
    have ha : φ y m ≠ 0 := by
      intro h0
      apply hy
      apply φ.injective
      rw [map_mul, AlgEquiv.apply_symm_apply, map_zero]
      funext j
      rw [Pi.mul_apply, Pi.zero_apply]
      by_cases hj : j = m
      · subst hj
        rw [Pi.single_eq_same, one_mul]
        exact h0
      · simp only [Pi.single_eq_of_ne hj, zero_mul]
    obtain ⟨b, hb⟩ := Ideal.Quotient.exists_inv ha
    refine ⟨φ.symm (Pi.single m b), ?_⟩
    apply φ.injective
    rw [map_mul, map_mul, AlgEquiv.apply_symm_apply, AlgEquiv.apply_symm_apply]
    funext j
    rw [Pi.mul_apply, Pi.mul_apply]
    by_cases hj : j = m
    · subst hj
      rw [Pi.single_eq_same, Pi.single_eq_same, one_mul]
      exact hb
    · simp only [Pi.single_eq_of_ne hj, zero_mul]

end Generic

theorem exists_isPre (K : UQ) (B : InvAlg K) (hP : B.P.Separable) :
    ∃ (ι : Type) (_ : Fintype ι) (e : ι → B.A) (S : Finset ι), IsPre B e S := by
  have := InvAlg.isReduced_of_separable_P K B hP
  have : IsArtinianRing B.A := IsArtinianRing.of_finite K.E B.A
  obtain ⟨M, _, f, hf, hF⟩ := exists_fieldIdem_family (R := B.A)

  have hex : ∀ m, ∃ m', B.σ (f m) = f m' := by
    intro m
    by_contra hcon
    push Not at hcon
    have hσ := (hF m).map B.σ
    have hzero : ∀ m', B.σ (f m) * f m' = 0 := fun m' => by
      by_contra h
      exact hcon m' (hσ.eq_of_mul_ne_zero (hF m') h)
    apply hσ.2.1
    calc B.σ (f m) = B.σ (f m) * 1 := (mul_one _).symm
      _ = ∑ m', B.σ (f m) * f m' := by rw [← hf.complete, Finset.mul_sum]
      _ = 0 := Finset.sum_eq_zero (fun m' _ => hzero m')
  choose τ hτ using hex
  have finj : Function.Injective f := by
    intro a b hab
    by_contra h
    apply (hF a).2.1
    calc f a = f a * f a := (hF a).1.eq.symm
      _ = f a * f b := congrArg (f a * ·) hab
      _ = 0 := hf.ortho h
  have hττ : ∀ m, τ (τ m) = m := by
    intro m
    apply finj
    calc f (τ (τ m)) = B.σ (f (τ m)) := (hτ (τ m)).symm
      _ = B.σ (B.σ (f m)) := by rw [hτ m]
      _ = f m := B.σ_σ _

  obtain ⟨rep, rep_mem, rep_tau⟩ : ∃ rep : M → M, (∀ m, rep m = m ∨ rep m = τ m) ∧
      ∀ m, rep (τ m) = rep m := by
    let enc := Fintype.equivFin M
    refine ⟨fun m => if enc m ≤ enc (τ m) then m else τ m, fun m => ?_, fun m => ?_⟩
    · dsimp only
      split_ifs <;> simp
    · dsimp only
      rw [hττ m]
      by_cases h1 : enc m ≤ enc (τ m) <;> by_cases h2 : enc (τ m) ≤ enc m
      · have h3 : m = τ m := enc.injective (le_antisymm h1 h2)
        rw [if_pos h2, if_pos h1]
        exact h3.symm
      · rw [if_neg h2, if_pos h1]
      · rw [if_pos h2, if_neg h1]
      · exact (le_total (enc m) (enc (τ m))).elim (fun h => absurd h h1) (fun h => absurd h h2)
  have rep_rep : ∀ m, rep (rep m) = rep m := by
    intro m
    rcases rep_mem m with h | h
    · rw [h, h]
    · rw [h, rep_tau, h]
  obtain ⟨g, hg⟩ : ∃ g : M → {m : M // rep m = m}, ∀ m, (g m).1 = rep m :=
    ⟨fun m => ⟨rep m, rep_rep m⟩, fun _ => rfl⟩
  have hfib : ∀ (i : {m : M // rep m = m}) (m : M), g m = i ↔ m = i.1 ∨ m = τ i.1 := by
    intro i m
    rw [Subtype.ext_iff, hg]
    constructor
    · intro h
      rcases rep_mem m with h' | h'
      · exact Or.inl (h'.symm.trans h)
      · right
        have h3 : τ m = i.1 := h'.symm.trans h
        calc m = τ (τ m) := (hττ m).symm
          _ = τ i.1 := by rw [h3]
    · rintro (h | h)
      · rw [h]
        exact i.2
      · rw [h, rep_tau]
        exact i.2
  obtain ⟨e, he⟩ : ∃ e : {m : M // rep m = m} → B.A,
      ∀ i, e i = ∑ m ∈ Finset.univ.filter (fun m => g m = i), f m := ⟨_, fun _ => rfl⟩
  have hsum : ∀ i, e i = if τ i.1 = i.1 then f i.1 else f i.1 + f (τ i.1) := by
    intro i
    have hfil : Finset.univ.filter (fun m => g m = i) = {i.1, τ i.1} := by
      ext m
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
        Finset.mem_singleton]
      exact hfib i m
    rw [he, hfil]
    split_ifs with h
    · simp [h]
    · exact Finset.sum_pair (Ne.symm h)
  refine ⟨{m : M // rep m = m}, inferInstance, e, Finset.univ.filter (fun i => τ i.1 = i.1),
    ⟨⟨fun i => ?_, fun i j hij => ?_⟩, ?_⟩, fun i => ?_⟩
  · rw [he]
    exact hf.1.isIdempotentElem_sum
  · show e i * e j = 0
    rw [he, he, Finset.sum_mul]
    apply Finset.sum_eq_zero
    intro a ha
    apply hf.1.mul_sum_of_notMem
    intro ha'
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha ha'
    exact hij (ha.symm.trans ha')
  · simp_rw [he]
    rw [Finset.sum_fiberwise]
    exact hf.complete
  · refine ⟨f i.1, (hF _).1, (hF _).2.1, (hF _).2.2, fun hi => ?_, fun hi => ?_⟩
    · have hi' : τ i.1 = i.1 := (Finset.mem_filter.mp hi).2
      exact ⟨by rw [hsum i, if_pos hi'], by rw [hτ, hi']⟩
    · have hi' : τ i.1 ≠ i.1 := fun h => hi (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩)
      exact ⟨by rw [hτ]; exact hf.ortho (Ne.symm hi'), by rw [hsum i, if_neg hi', hτ]⟩

theorem isPre_of_separable : ∀ (K : UQ) (B : InvAlg K), B.P.Separable →
    ∃ (ι : Type) (_ : Fintype ι) (e : ι → B.A) (S : Finset ι), IsPre B e S := fun K B hP => exists_isPre K B hP

end GlobalTheory.UnitLemma.Desc
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsClosedEmbeddingDiagOneGeneralLinearEmbeddingStatement
section
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isClosedEmbedding_diagOneGeneralLinearEmbedding : ∀ (F : Type) [NontriviallyNormedField F] (r : ℕ), Topology.IsClosedEmbedding (GlobalTheory.JR.Step.emb r F) := by
  first | exact @GlobalTheory.JR.Step.EmbClosed.isClosedEmbedding_emb | exact GlobalTheory.JR.Step.EmbClosed.isClosedEmbedding_emb | (intros; apply GlobalTheory.JR.Step.EmbClosed.isClosedEmbedding_emb <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsClosedEmbeddingLeftMulMatrixPowerBasisUnitsHomStatement
section
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isClosedEmbedding_leftMulMatrixPowerBasisUnitsHom : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (r : ℕ) (τ : A.K) (p : Fin r → F) (hG : A.IsGen τ p), Topology.IsClosedEmbedding (LinDesc.tm A hG) := by
  first | exact @GlobalTheory.JR.LinDesc.tm_isClosedEmbedding | exact GlobalTheory.JR.LinDesc.tm_isClosedEmbedding | (intros; apply GlobalTheory.JR.LinDesc.tm_isClosedEmbedding <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsFrobFixesRootOfOneModPlaceStatement
section
open NumberField IsDedekindDomain
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isFrob_fixes_root_of_one_mod_place : ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] (M : ℕ) (ζ : F),
    IsPrimitiveRoot ζ M → ∀ v : HeightOneSpectrum (𝓞 F), ((M : ℕ) : 𝓞 F) ∉ v.asIdeal →
    ∀ A : ValuationSubring Ω, Formalism.ConjugateSelfDual.IsPlaceOver A v → ∀ σ : Formalism.ConjugateSelfDual.G F Ω, Formalism.ConjugateSelfDual.IsFrob A (Formalism.ConjugateSelfDual.normV v) σ →
    ∀ x : 𝓞 F, x - 1 ∈ v.asIdeal → ∀ w : Ω, w ^ M = algebraMap F Ω (x : F) → σ w = w := by
  first | exact @GlobalTheory.frob_fixes_root_of_one_mod | exact GlobalTheory.frob_fixes_root_of_one_mod | (intros; apply GlobalTheory.frob_fixes_root_of_one_mod <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsFrobRestrictScalarsOfPrimeAbsNormStatement
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isFrob_restrictScalars_of_prime_absNorm' : ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (Z : IntermediateField F Ω) [NumberField Z] (w : HeightOneSpectrum (𝓞 Z)) (v : HeightOneSpectrum (𝓞 F)), w.asIdeal.LiesOver v.asIdeal → (Ideal.absNorm w.asIdeal).Prime → ∀ B : ValuationSubring Ω, IsPlaceOver (F := Z) B w → ∀ σ : G Z Ω, IsFrob B (normV w) σ → Ideal.absNorm v.asIdeal = Ideal.absNorm w.asIdeal ∧ IsPlaceOver (F := F) B v ∧ IsFrob (F := F) B (normV v) (σ.restrictScalars F) := by
  first | exact @GlobalTheory.isFrob_restrictScalars_of_prime_absNorm | exact GlobalTheory.isFrob_restrictScalars_of_prime_absNorm | (intros; apply GlobalTheory.isFrob_restrictScalars_of_prime_absNorm <;> assumption)
end

