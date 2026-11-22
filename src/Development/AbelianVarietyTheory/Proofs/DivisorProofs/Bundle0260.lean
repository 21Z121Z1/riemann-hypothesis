import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0002
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0200
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0215
import ReciprocityTheory.CommutativeAlgebra.CohenMacaulay.Bundle0001
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0214
import Development.AbelianVarietyTheory.Definitions.Divisors.EllFamNontrivial
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0110
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0189
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0150
import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.IsOpenOfMemIrreducibleComponentsOfFinite
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0086
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteEigenFiltrationPiecesAddValInt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0180
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.OmegaFactorization
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PartialZetaFunctionalEquation
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0167
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0222
import ReciprocityTheory.Chebotarev.Bundle0003
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IrreducibleXSqAddOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0114
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0155
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0216
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankMulPowLeFinrankOfPowerSeries

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniformizerSeparableReduction
section
open scoped TensorProduct nonZeroDivisors
open Polynomial

namespace GlobalTheory.UnramifiedGenerator

open IsLocalRing

theorem charpoly_map_residue {R O : Type} [CommRing R] [IsLocalRing R] [CommRing O] [IsDomain O]
    [IsLocalRing O] [Algebra R O] [Module.Free R O] [Module.Finite R O]
    [IsLocalHom (algebraMap R O)] (ϖ : R) (hϖ : maximalIdeal R = Ideal.span {ϖ})
    (π : O) (hπ0 : π ≠ 0) (hπ : maximalIdeal O = Ideal.span {π}) (e : ℕ) (he : 0 < e) (u : Oˣ)
    (hu : algebraMap R O ϖ = π ^ e * u) (a : O) :
    (LinearMap.charpoly (LinearMap.mulLeft R a)).map (residue R) =
      (LinearMap.charpoly (LinearMap.mulLeft (ResidueField R) (residue O a))) ^ e := by
  set k := ResidueField R
  have hsurj : ∀ x : k ⊗[R] O, ∃ y : O, (1 : k) ⊗ₜ[R] y = x := fun x =>
    TensorProduct.mk_surjective R O k residue_surjective x
  have hker : ∀ y : O, (1 : k) ⊗ₜ[R] y = 0 ↔ ∃ z, y = algebraMap R O ϖ * z := by
    intro y
    have h1 : (1 : k) ⊗ₜ[R] y = 0 ↔
        y ∈ LinearMap.ker (TensorProduct.mk R (R ⧸ maximalIdeal R) O 1) := Iff.rfl
    rw [h1, LinearMap.ker_tensorProductMk, hϖ, Submodule.ideal_span_singleton_smul,
      Submodule.mem_smul_pointwise_iff_exists]
    simp only [Submodule.mem_top, true_and, Algebra.smul_def]
    exact ⟨fun ⟨z, hz⟩ => ⟨z, hz.symm⟩, fun ⟨z, hz⟩ => ⟨z, hz.symm⟩⟩
  let t : Module.End k (k ⊗[R] O) := (LinearMap.mulLeft R π).baseChange k
  let T : Module.End k (k ⊗[R] O) := (LinearMap.mulLeft R a).baseChange k
  have ht : ∀ y, t (1 ⊗ₜ y) = 1 ⊗ₜ (π * y) := fun y => by simp [t]
  have hT : ∀ y, T (1 ⊗ₜ y) = 1 ⊗ₜ (a * y) := fun y => by simp [T]
  have htp : ∀ (n : ℕ) y, (t ^ n) (1 ⊗ₜ y) = 1 ⊗ₜ (π ^ n * y) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih => intro y; rw [pow_succ', Module.End.mul_apply, ih, ht, pow_succ', mul_assoc]
  have hc : Commute t T := by
    refine LinearMap.ext fun x => ?_
    obtain ⟨y, rfl⟩ := hsurj x
    simp only [Module.End.mul_apply, ht, hT, mul_left_comm]
  have hte : t ^ e = 0 := by
    refine LinearMap.ext fun x => ?_
    obtain ⟨y, rfl⟩ := hsurj x
    rw [htp, LinearMap.zero_apply, hker]
    exact ⟨(u⁻¹ : Oˣ) * y, by rw [hu, mul_assoc, Units.mul_inv_cancel_left]⟩
  have hkt : ∀ x, t x = 0 → x ∈ LinearMap.range (t ^ (e - 1)) := by
    intro x hx
    obtain ⟨y, rfl⟩ := hsurj x
    rw [ht, hker] at hx
    obtain ⟨z, hz⟩ := hx
    obtain ⟨n, rfl⟩ : ∃ n, e = n + 1 := ⟨e - 1, by omega⟩
    refine ⟨1 ⊗ₜ (u * z), ?_⟩
    rw [htp, Nat.add_sub_cancel]
    congr 1
    apply mul_left_cancel₀ hπ0
    rw [hz, hu]
    ring
  have hTt : LinearMap.range t ≤ (LinearMap.range t).comap T := by
    rintro _ ⟨x, rfl⟩
    exact ⟨T x, LinearMap.congr_fun hc.eq x⟩
  have key := GlobalTheory.NilpFiltration.charpoly_eq_charpoly_mapQ_pow k (k ⊗[R] O) t T hc e he hte hkt hTt
  have hbc : LinearMap.charpoly T = (LinearMap.charpoly (LinearMap.mulLeft R a)).map (residue R) :=
    LinearMap.charpoly_baseChange _ k
  rw [← hbc, key]
  congr 1
  let φ : k ⊗[R] O →ₗ[k] ResidueField O :=
    (Algebra.TensorProduct.lift (Algebra.ofId k (ResidueField O))
      (IsScalarTower.toAlgHom R O (ResidueField O)) (fun _ _ => Commute.all _ _)).toLinearMap
  have hφ : ∀ y, φ (1 ⊗ₜ y) = residue O y := fun y => by simp [φ]
  have hφs : Function.Surjective φ := fun w => by
    obtain ⟨y, rfl⟩ := residue_surjective w
    exact ⟨_, hφ y⟩
  have hφk : LinearMap.range t = LinearMap.ker φ := by
    ext x
    obtain ⟨y, rfl⟩ := hsurj x
    constructor
    · rintro ⟨x', hx'⟩
      obtain ⟨z, rfl⟩ := hsurj x'
      rw [← hx', ht, LinearMap.mem_ker, hφ, residue_eq_zero_iff, hπ]
      exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)
    · intro hy
      rw [LinearMap.mem_ker, hφ, residue_eq_zero_iff, hπ, Ideal.mem_span_singleton] at hy
      obtain ⟨z, rfl⟩ := hy
      exact ⟨_, ht z⟩
  refine GlobalTheory.NilpFiltration.charpoly_eq_of_intertwine
    ((Submodule.quotEquivOfEq _ _ hφk).trans (φ.quotKerEquivOfSurjective hφs)) _ _ ?_
  intro x
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  obtain ⟨y, rfl⟩ := hsurj x
  change φ (T (1 ⊗ₜ y)) = residue O a * φ (1 ⊗ₜ y)
  rw [hT, hφ, hφ, map_mul]

theorem exists_ramification_and_generator : ∀ (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O],
    ∃ (e : ℕ) (π a : O) (u : Oˣ) (h : ℤ_[l][X]), 0 < e ∧ (l : O) = π ^ e * u ∧ h.Monic ∧
      aeval a h ∈ Ideal.span {π} ∧ e * h.natDegree = Module.finrank ℤ_[l] O ∧
      ∀ (κ : Type) [Field κ] [CharP κ l] (ψ : ℤ_[l] →+* κ), (h.map ψ).Separable ∧
        (LinearMap.charpoly (LinearMap.mulLeft ℤ_[l] a)).map ψ = (h.map ψ) ^ e := by
  intro l hl O _ _ _ _ _ _
  set k := ResidueField ℤ_[l]
  haveI : Finite k := Finite.of_equiv _ (PadicInt.residueField (p := l)).symm.toEquiv
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible O
  have hl0 : (l : ℤ_[l]) ≠ 0 := Nat.cast_ne_zero.2 hl.out.ne_zero
  have hlm : (l : ℤ_[l]) ∈ maximalIdeal ℤ_[l] := by
    rw [PadicInt.maximalIdeal_eq_span_p]; exact Ideal.mem_span_singleton_self _
  have hl1 : algebraMap ℤ_[l] O l ≠ 0 :=
    (map_ne_zero_iff _ (FaithfulSMul.algebraMap_injective ℤ_[l] O)).2 hl0
  obtain ⟨e, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hl1 hπ
  have he : 0 < e := by
    refine Nat.pos_of_ne_zero ?_
    rintro rfl
    have h1 : IsUnit (algebraMap ℤ_[l] O l) := by rw [hu]; simp
    exact hlm (isUnit_of_map_unit _ _ h1)
  rw [mul_comm] at hu
  let pb : PowerBasis k (ResidueField O) := Field.powerBasisOfFiniteOfSeparable k (ResidueField O)
  obtain ⟨a, ha⟩ := residue_surjective pb.gen
  have hm : (minpoly k pb.gen).Monic := minpoly.monic pb.isIntegral_gen
  obtain ⟨h, hh, -, hhm⟩ := lifts_and_natDegree_eq_and_monic (f := residue ℤ_[l])
    ((mem_lifts _).2 (map_surjective _ residue_surjective _)) hm
  have hsep : (h.map (residue ℤ_[l])).Separable := by
    rw [hh]; exact Algebra.IsSeparable.isSeparable k pb.gen
  have hch : (LinearMap.charpoly (LinearMap.mulLeft ℤ_[l] a)).map (residue ℤ_[l]) =
      (h.map (residue ℤ_[l])) ^ e := by
    rw [charpoly_map_residue (l : ℤ_[l]) PadicInt.maximalIdeal_eq_span_p π hπ.ne_zero
      hπ.maximalIdeal_eq e he u hu a, hh, ha, ← charpoly_leftMulMatrix pb,
      ← LinearMap.charpoly_toMatrix _ pb.basis]
    rfl
  refine ⟨e, π, a, u, h, he, by simpa using hu, hhm, ?_, ?_, ?_⟩
  · rw [← hπ.maximalIdeal_eq, ← residue_eq_zero_iff]
    have h1 := minpoly.aeval k pb.gen
    rw [← hh, ← ha] at h1
    rw [← h1]
    exact ((aeval_algebraMap_apply (ResidueField O) a h).symm).trans
      (aeval_map_algebraMap k _ h).symm
  · have h1 := congrArg natDegree hch
    rw [(LinearMap.charpoly_monic _).natDegree_map, LinearMap.charpoly_natDegree,
      natDegree_pow, hhm.natDegree_map] at h1
    exact h1.symm
  · intro κ _ _ ψ
    have hψ : ∀ x ∈ maximalIdeal ℤ_[l], ψ x = 0 := by
      intro x hx
      rw [PadicInt.maximalIdeal_eq_span_p, Ideal.mem_span_singleton] at hx
      obtain ⟨y, rfl⟩ := hx
      simp
    let χ : k →+* κ := Ideal.Quotient.lift _ ψ hψ
    have hχ : ψ = χ.comp (residue ℤ_[l]) := RingHom.ext fun _ => rfl
    rw [hχ, ← Polynomial.map_map, ← Polynomial.map_map, hch, Polynomial.map_pow]
    exact ⟨hsep.map, rfl⟩

end GlobalTheory.UnramifiedGenerator
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FgOfSaturatedIdealPowerIntoImageStatement
section
open IsLocalRing TensorProduct Pointwise
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fg_of_ideal_pow_smul_mem_range_tensor : ∀ (S : Type) [CommRing S] [IsDomain S] [IsNoetherianRing S] (I : Ideal S), (∀ (k : ℕ) (c : FractionRing S), (∀ a ∈ I ^ k, IsLocalization.IsInteger S (a • c)) → IsLocalization.IsInteger S c) → ∀ (M : Type) [AddCommGroup M] [Module S M] [Module.Finite S M] (N : Submodule S (FractionRing S ⊗[S] M)), (∀ z ∈ N, ∃ k : ℕ, ∀ a ∈ I ^ k, a • z ∈ LinearMap.range (TensorProduct.mk S (FractionRing S) M 1)) → N.FG := by
  first | exact @GlobalTheory.fg_of_saturated_ideal_power_into_image | exact GlobalTheory.fg_of_saturated_ideal_power_into_image | (intros; apply GlobalTheory.fg_of_saturated_ideal_power_into_image <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FibreCoordinatePartialDerivationCommStatement
section
open TopologicalSpace CategoryTheory GlobalTheory.CatCoh GlobalTheory.AnPer GlobalTheory.AnPer.Charts
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fibreCoordinatePartialDerivation_comm : ∀ (I : Type) [Fintype I] (g : ℕ) (W : Opens (Tot I g)) (a b : Fin g) (x : Hol W), dw a (dw b x) = dw b (dw a x) := by
  first | exact @GlobalTheory.AnPer.dw_comm | exact GlobalTheory.AnPer.dw_comm | (intros; apply GlobalTheory.AnPer.dw_comm <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteCutOutSubalgebraQuasiCoherentStatement
section
open AlgebraicGeometry CategoryTheory Limits Opposite GlobalTheory.QcSub
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_cut_out_subalgebra_quasiCoherent : ∀ (X : Scheme.{0}), IsNoetherian X → ∀ (F : X.Opensᵒᵖ ⥤ CommRingCat) (α : X.presheaf ⟶ F), ((Scheme.AffineZariskiSite.toOpensFunctor X).op.whiskerLeft α).Coequifibered → (∀ U : X.Opens, IsAffineOpen U → (α.app (op U)).hom.IsIntegral) → ∀ {ι : Type} (V : ι → X.Opens), (∀ j, IsAffineOpen (V j)) → (∀ x : X, ∃ j, x ∈ V j) → ∀ (T : ∀ j, Set (F.obj (op (V j)))), (∀ j, (T j).Finite) → ∀ W : X.Opens, IsAffineOpen W → (subMap F α V T W).Finite := by
  first | exact @GlobalTheory.QcSub.subMap_finite | exact GlobalTheory.QcSub.subMap_finite | (intros; apply GlobalTheory.QcSub.subMap_finite <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteDimensionalFunctionFieldStalkImageGenericP
section
open AlgebraicGeometry CategoryTheory Limits

namespace GlobalTheory.NormSheafDescent

theorem finiteDimensional_functionField : ∀ (Y Z : Scheme.{0}) (π : Y ⟶ Z) [IsFinite π] [IsIntegral Y]
    (hK : IsField (Z.presheaf.stalk (GlobalTheory.NormSheafDescent.genPt π))),
    letI := GlobalTheory.NormSheafDescent.fieldK π hK; letI := GlobalTheory.NormSheafDescent.algKL π
    FiniteDimensional (Z.presheaf.stalk (GlobalTheory.NormSheafDescent.genPt π)) Y.functionField := by
  intro Y Z π _ _ hK
  letI := fieldK π hK
  letI := algKL π
  obtain ⟨U, hU, hζU, -⟩ :=
    exists_isAffineOpen_mem_and_subset (X := Z) (U := ⊤) (x := genPt π) trivial
  have hηU : genericPoint Y ∈ π ⁻¹ᵁ U := hζU
  have hV : IsAffineOpen (π ⁻¹ᵁ U) := hU.preimage π
  haveI : Nonempty (π ⁻¹ᵁ U) := ⟨⟨_, hηU⟩⟩
  let f : Γ(Z, U) →+* Z.presheaf.stalk (genPt π) := (Z.presheaf.germ U (genPt π) hζU).hom
  let φ : Γ(Y, π ⁻¹ᵁ U) →+* Y.functionField :=
    (Y.presheaf.germ (π ⁻¹ᵁ U) (genericPoint Y) hηU).hom
  let g : Γ(Z, U) →+* Γ(Y, π ⁻¹ᵁ U) := (π.app U).hom
  have hsq : ∀ a, algebraMap (Z.presheaf.stalk (genPt π)) Y.functionField (f a) = φ (g a) :=
    fun a => Scheme.Hom.germ_stalkMap_apply π U _ hζU a
  have hfin : g.Finite := IsFinite.finite_app π U hU
  letI : Algebra Γ(Z, U) Γ(Y, π ⁻¹ᵁ U) := g.toAlgebra
  haveI : Module.Finite Γ(Z, U) Γ(Y, π ⁻¹ᵁ U) := hfin
  letI : Algebra Γ(Y, π ⁻¹ᵁ U) Y.functionField := φ.toAlgebra
  haveI : IsFractionRing Γ(Y, π ⁻¹ᵁ U) Y.functionField :=
    functionField_isFractionRing_of_isAffineOpen Y _ hV
  have hint : ∀ b, IsIntegral (Z.presheaf.stalk (genPt π)) (φ b) := by
    intro b
    obtain ⟨p, hp, hpb⟩ := Algebra.IsIntegral.isIntegral (R := Γ(Z, U)) b
    refine ⟨p.map f, hp.map f, ?_⟩
    have e : (algebraMap (Z.presheaf.stalk (genPt π)) Y.functionField).comp f = φ.comp g :=
      RingHom.ext hsq
    have hpb' : p.eval₂ g b = 0 := hpb
    rw [Polynomial.eval₂_map, e, ← Polynomial.hom_eval₂, hpb', map_zero]
  obtain ⟨s, hs⟩ := Module.Finite.fg_top (R := Γ(Z, U)) (M := Γ(Y, π ⁻¹ᵁ U))
  haveI : Finite (φ '' (s : Set Γ(Y, π ⁻¹ᵁ U))) := (s.finite_toSet.image φ).to_subtype
  have hF : FiniteDimensional (Z.presheaf.stalk (genPt π))
      (IntermediateField.adjoin (Z.presheaf.stalk (genPt π)) (φ '' (s : Set Γ(Y, π ⁻¹ᵁ U)))) :=
    IntermediateField.finiteDimensional_adjoin (by
      rintro _ ⟨b, -, rfl⟩
      exact hint b)
  have hmem : ∀ b, φ b ∈ IntermediateField.adjoin (Z.presheaf.stalk (genPt π))
      (φ '' (s : Set Γ(Y, π ⁻¹ᵁ U))) := by
    intro b
    have hb : b ∈ Submodule.span Γ(Z, U) (s : Set Γ(Y, π ⁻¹ᵁ U)) := hs ▸ Submodule.mem_top
    induction hb using Submodule.span_induction with
    | mem x hx => exact IntermediateField.subset_adjoin _ _ ⟨x, hx, rfl⟩
    | zero => rw [map_zero]; exact zero_mem _
    | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
    | smul a x _ hx =>
      have e : φ (a • x) = algebraMap (Z.presheaf.stalk (genPt π)) Y.functionField (f a) * φ x := by
        rw [hsq, Algebra.smul_def, map_mul]; rfl
      rw [e]
      exact mul_mem (IntermediateField.algebraMap_mem _ _) hx
  have htop : IntermediateField.adjoin (Z.presheaf.stalk (genPt π))
      (φ '' (s : Set Γ(Y, π ⁻¹ᵁ U))) = ⊤ := by
    refine eq_top_iff.2 fun x _ => ?_
    obtain ⟨b, c, hc, rfl⟩ := IsFractionRing.div_surjective (A := Γ(Y, π ⁻¹ᵁ U)) x
    exact div_mem (hmem b) (hmem c)
  have h2 : FiniteDimensional (Z.presheaf.stalk (genPt π))
      (⊤ : IntermediateField (Z.presheaf.stalk (genPt π)) Y.functionField) := htop ▸ hF
  exact LinearEquiv.finiteDimensional IntermediateField.topEquiv.toLinearEquiv

end GlobalTheory.NormSheafDescent
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteEigenFiltrationPiecesAddValIntStatement
section
open GlobalTheory.IndefiniteRowSideFullHecke.MultiplicationKernelIdentity GlobalTheory.HermitianPreEigenvalues Polynomial Module
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_eigenFiltration_pieces_addValInt : ∀ (C : Type) [Field C] (v : AddValuation C (WithTop ℝ)) (S : Type) [Fintype S] [DecidableEq S] (a : S → Int0 v), Function.Injective a → ∀ (N : ℕ) (Fil : Submodule (RS a) (Fin N → RS a)), (∀ (c : Int0 v) (x : Fin N → RS a), c ≠ 0 → c • x ∈ Fil → x ∈ Fil) → ∀ τ : S, Module.Finite (Int0 v) (Fil.restrictScalars (Int0 v)) ∧ Module.Finite (Int0 v) (preEig a Fil τ) ∧ Module.Finite (Int0 v) (filKer a Fil τ) ∧ Module.Finite (Int0 v) (eigSub a τ (Fin N → RS a)) ∧ Module.Finite (Int0 v) (eigSub a τ ((Fin N → RS a) ⧸ Fil)) ∧ Module.Finite (Int0 v) (eigSub a τ Fil) ∧ Module.Finite (Int0 v) (kerMul a (cofac a τ) Fil) := by
  first | exact @GlobalTheory.HerbFin.finite_main | exact GlobalTheory.HerbFin.finite_main | (intros; apply GlobalTheory.HerbFin.finite_main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteGaussianExtensionUnitsQuotUnits
section
open NumberField Complex Polynomial
open scoped nonZeroDivisors ContDiff
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.HeckeTwo

noncomputable section

namespace GlobalTheory.GaussExt.UnitIdx

variable (F : Type) [Field F] [NumberField F] [NumberField.IsTotallyReal F]

theorem aeval_neg_ii : aeval (-ii F) (X ^ 2 + 1 : F[X]) = 0 := by
  simp only [map_add, map_pow, aeval_X, map_one, neg_sq, ii_sq F]; ring

def conj : Ext F →ₐ[F] Ext F := AdjoinRoot.liftAlgHom (X ^ 2 + 1 : F[X]) (Algebra.ofId F (Ext F)) (-ii F)
  (by have := aeval_neg_ii F; rwa [aeval_def] at this)

theorem conj_ii : conj F (ii F) = -ii F := by
  simp [conj, ii]

theorem conj_algebraMap (a : F) : conj F (algebraMap F (Ext F) a) = algebraMap F (Ext F) a :=
  (conj F).commutes a

theorem exists_repr (x : Ext F) : ∃ a b : F, x = algebraMap F (Ext F) a + algebraMap F (Ext F) b * ii F := by
  obtain ⟨p, rfl⟩ := AdjoinRoot.mk_surjective x
  have hm : (X ^ 2 + 1 : F[X]).Monic := by monicity!
  have hdeg : (X ^ 2 + 1 : F[X]).natDegree = 2 := by compute_degree!
  set r := p %ₘ (X ^ 2 + 1 : F[X])
  have hr : AdjoinRoot.mk (X ^ 2 + 1 : F[X]) p = AdjoinRoot.mk _ r := by
    rw [AdjoinRoot.mk_eq_mk]
    exact ⟨p /ₘ (X ^ 2 + 1), by have := modByMonic_add_div p (X ^ 2 + 1 : F[X]); linear_combination -this⟩
  have hrd : r.natDegree ≤ 1 := by
    have := natDegree_modByMonic_lt p hm (by intro h; have := congrArg natDegree h; rw [hdeg] at this; simp at this)
    change (p %ₘ (X ^ 2 + 1 : F[X])).natDegree ≤ 1
    omega
  refine ⟨r.coeff 0, r.coeff 1, ?_⟩
  rw [hr, eq_X_add_C_of_natDegree_le_one hrd]
  simp [ii, AdjoinRoot.algebraMap_eq, add_comm]

theorem ii_ne_zero : ii F ≠ 0 := by
  intro h
  have := ii_sq F
  rw [h] at this
  norm_num at this

theorem mem_range_of_conj_eq (x : Ext F) (hx : conj F x = x) : ∃ a : F, algebraMap F (Ext F) a = x := by
  obtain ⟨a, b, rfl⟩ := exists_repr F x
  refine ⟨a, ?_⟩
  simp only [map_add, map_mul, conj_algebraMap, conj_ii] at hx
  have h2 : (2 : Ext F) * algebraMap F (Ext F) b * ii F = 0 := by linear_combination -hx
  have hb : algebraMap F (Ext F) b = 0 := by
    rcases mul_eq_zero.1 h2 with h | h
    · rcases mul_eq_zero.1 h with h | h
      · exact absurd h two_ne_zero
      · exact h
    · exact absurd h (ii_ne_zero F)
  rw [hb]; ring

theorem embedding_conj (φ : Ext F →+* ℂ) (x : Ext F) : φ (conj F x) = starRingEnd ℂ (φ x) := by
  have key : φ.comp (conj F).toRingHom = (starRingEnd ℂ).comp φ := by
    apply AdjoinRoot.ringHom_ext
    · ext a
      have hre := NumberField.IsTotallyReal.complexEmbedding_isReal (φ.comp (algebraMap F (Ext F)))
      have h1 := hre.coe_embedding_apply a
      simp only [RingHom.comp_apply, AdjoinRoot.algebraMap_eq] at h1 ⊢
      have h3 : (conj F).toRingHom (AdjoinRoot.of _ a) = AdjoinRoot.of _ a := by
        rw [← AdjoinRoot.algebraMap_eq]; exact conj_algebraMap F a
      rw [h3, ← h1, Complex.conj_ofReal]
    · have h := congrArg φ (ii_sq F)
      simp only [map_pow, map_neg, map_one] at h
      have hc : (φ (ii F) - I) * (φ (ii F) + I) = 0 := by linear_combination h - I_sq
      simp only [RingHom.comp_apply]
      change φ (conj F (ii F)) = starRingEnd ℂ (φ (ii F))
      rw [conj_ii, map_neg]
      rcases mul_eq_zero.1 hc with h' | h'
      · rw [sub_eq_zero.1 h']; simp
      · rw [eq_neg_of_add_eq_zero_left h']; simp
  exact congrArg (fun f => f x) key

theorem isIntegral_conj {x : Ext F} (hx : IsIntegral ℤ x) : IsIntegral ℤ (conj F x) :=
  hx.map ((conj F).toRingHom.toIntAlgHom)

theorem pow_mem_range (u : (𝓞 (Ext F))ˣ) :
    ∃ m : ℕ, 0 < m ∧ u ^ m ∈ (Units.map (algebraMap (𝓞 F) (𝓞 (Ext F))).toMonoidHom).range := by
  set x : Ext F := ((u : 𝓞 (Ext F)) : Ext F)
  set y : Ext F := (((u⁻¹ : (𝓞 (Ext F))ˣ) : 𝓞 (Ext F)) : Ext F)
  have hxy : x * y = 1 := by
    have := congrArg (fun z : 𝓞 (Ext F) => (z : Ext F)) u.mul_inv
    simpa [x, y] using this
  have hx0 : x ≠ 0 := left_ne_zero_of_mul_eq_one hxy
  have hint : IsIntegral ℤ (x * conj F y) :=
    (RingOfIntegers.isIntegral_coe _).mul (isIntegral_conj F (RingOfIntegers.isIntegral_coe _))
  obtain ⟨m, hm, hpow⟩ := NumberField.Embeddings.pow_eq_one_of_norm_eq_one (Ext F) ℂ hint fun φ => by
    have h1 : φ x * φ y = 1 := by rw [← map_mul, hxy, map_one]
    rw [map_mul, embedding_conj, norm_mul, Complex.norm_conj, ← norm_mul, h1, norm_one]
  refine ⟨m, hm, ?_⟩

  have hcxy : conj F x * conj F y = 1 := by rw [← map_mul, hxy, map_one]
  have hfix : conj F (x ^ m) = x ^ m := by
    have : (x * conj F y) ^ m * (conj F x) ^ m = (conj F x) ^ m := by rw [hpow, one_mul]
    rw [map_pow, ← this, ← mul_pow, mul_assoc, mul_comm (conj F y), hcxy, mul_one]
  obtain ⟨a, ha⟩ := mem_range_of_conj_eq F _ hfix
  have hai : IsIntegral ℤ a := by
    refine (isIntegral_algebraMap_iff (algebraMap F (Ext F)).injective).1 ?_
    rw [ha]; exact (RingOfIntegers.isIntegral_coe _).pow m

  have hfix' : conj F (y ^ m) = y ^ m := by
    have e : y ^ m = (x ^ m)⁻¹ := by rw [← inv_pow, inv_eq_of_mul_eq_one_right hxy]
    rw [e, map_inv₀, hfix]
  obtain ⟨b, hb⟩ := mem_range_of_conj_eq F _ hfix'
  have hbi : IsIntegral ℤ b := by
    refine (isIntegral_algebraMap_iff (algebraMap F (Ext F)).injective).1 ?_
    rw [hb]; exact (RingOfIntegers.isIntegral_coe _).pow m
  have hab : a * b = 1 := by
    apply (algebraMap F (Ext F)).injective
    rw [map_mul, ha, hb, ← mul_pow, hxy, one_pow, map_one]
  let A : 𝓞 F := ⟨a, hai⟩
  let B : 𝓞 F := ⟨b, hbi⟩
  have hAB : A * B = 1 := RingOfIntegers.ext hab
  refine ⟨⟨A, B, hAB, by rw [mul_comm]; exact hAB⟩, ?_⟩
  apply Units.ext
  apply RingOfIntegers.ext
  simp only [RingHom.toMonoidHom_eq_coe, Units.coe_map, MonoidHom.coe_coe, Units.val_pow_eq_pow_val]
  rw [show (((u : 𝓞 (Ext F)) ^ m : 𝓞 (Ext F)) : Ext F) = x ^ m by simp [x], ← ha]
  rfl

theorem finite_quot : Finite ((NumberField.RingOfIntegers (GlobalTheory.GaussExt.Ext F))ˣ ⧸
    (Units.map (algebraMap (NumberField.RingOfIntegers F)
      (NumberField.RingOfIntegers (GlobalTheory.GaussExt.Ext F))).toMonoidHom).range) := by
  haveI : Group.FG (𝓞 (Ext F))ˣ := Group.fg_iff_monoid_fg.2 inferInstance
  refine CommGroup.finite_of_fg_torsion _ fun q => ?_
  obtain ⟨u, rfl⟩ := QuotientGroup.mk_surjective q
  obtain ⟨m, hm, hu⟩ := pow_mem_range F u
  refine isOfFinOrder_iff_pow_eq_one.2 ⟨m, hm, ?_⟩
  rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
  exact hu

end GlobalTheory.GaussExt.UnitIdx

theorem GlobalTheory.GaussExt.finite_units_quot_units : ∀ (F : Type) [Field F] [NumberField F] [NumberField.IsTotallyReal F],
    Finite ((NumberField.RingOfIntegers (GlobalTheory.GaussExt.Ext F))ˣ ⧸
      (Units.map (algebraMap (NumberField.RingOfIntegers F)
        (NumberField.RingOfIntegers (GlobalTheory.GaussExt.Ext F))).toMonoidHom).range) :=
  fun F _ _ _ => GlobalTheory.GaussExt.UnitIdx.finite_quot F
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteOfGaloisTraceRelationStatement
section
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_of_galois_trace_relation : ∀ (A R C : Type) [CommRing A] [CommRing R] [Algebra A R] [IsNoetherianRing R] [CommRing C] [Algebra R C]
    (G : Type) [Group G] [Fintype G] [DecidableEq G] (act : G →* (C ≃ₐ[R] C)) (T : C →ₗ[R] R),
    (∀ c, algebraMap R C (T c) = ∑ g, act g c) →
    ∀ (a : A), a ≠ 0 → ∀ (n : ℕ) (x y : Fin n → C),
      (∀ g, ∑ i, x i * act g (y i) = if g = 1 then algebraMap R C (algebraMap A R a) else 0) →
    GlobalTheory.GoodEtale.TorsionFreeOver A R C → Module.Finite R C := by
  first | (exact @GlobalTheory.GoodEtaleFinite.finite_of_trace_relation) | (exact GlobalTheory.GoodEtaleFinite.finite_of_trace_relation) | (intros; apply GlobalTheory.GoodEtaleFinite.finite_of_trace_relation  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankAddValuationIntegerSubmoduleEqFinrankSpanStatement
section
open GlobalTheory.IndefiniteRowSideFullHecke.MultiplicationKernelIdentity GlobalTheory.HermitianPreEigenvalues Polynomial Module
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finrank_int0_submodule_eq_finrank_span : ∀ (C : Type) [Field C] (v : AddValuation C (WithTop ℝ)) (N : ℕ) (X : Submodule (Int0 v) (Fin N → Int0 v)), Module.Finite (Int0 v) X → finrank (Int0 v) X = finrank C (Submodule.span C ((fun (x : Fin N → Int0 v) (i : Fin N) => (x i : C)) '' (X : Set (Fin N → Int0 v)))) := by
  first | exact @GlobalTheory.finrank_addValuationInteger_submodule_eq_finrank_span | exact GlobalTheory.finrank_addValuationInteger_submodule_eq_finrank_span | (intros; apply GlobalTheory.finrank_addValuationInteger_submodule_eq_finrank_span <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankHomologyModPrimeUniversalCoefficientsStatement
section
open CategoryTheory Limits
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finrank_homology_mod_prime_universal_coefficients : ∀ (C : CochainComplex (ModuleCat.{0} ℤ) ℕ) (p : ℕ) [Fact p.Prime], (∀ (n : ℕ) (x : C.X n), (p : ℤ) • x = 0 → x = 0) → (∀ n, Module.Finite ℤ (C.homology n)) → ∀ n : ℕ, (Module.finrank (ZMod p) ((((ModuleCat.extendScalars (Int.castRingHom (ZMod p))).mapHomologicalComplex (ComplexShape.up ℕ)).obj C).homology n) : ℤ) = Module.finrank (ZMod p) (TensorProduct ℤ (ZMod p) (C.homology n)) + Module.finrank (ZMod p) (TensorProduct ℤ (ZMod p) (C.homology (n + 1))) - Module.finrank ℤ (C.homology (n + 1)) := by
  first | exact @GlobalTheory.uct_mod_p | exact GlobalTheory.uct_mod_p | (intros; apply GlobalTheory.uct_mod_p <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankJointWeightSpaceEqOfCharpolyStatement
section
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finrank_jointWeightSpace_eq_of_charpoly : ∀ (k : Type) [Field k] [IsAlgClosed k] (C : Type) [CommRing C] [Module.Free ℤ C] [Module.Finite ℤ C] (H : Type 1) [AddCommGroup H] [Module k H] [FiniteDimensional k H] (σ : C →+* Module.End k H) (r : ℕ), (∀ c : C, LinearMap.charpoly (σ c) = ((LinearMap.charpoly (LinearMap.mulLeft ℤ c)) ^ r).map (Int.castRingHom k)) → ∀ χ : C →+* k, Module.finrank k ↥(⨅ c : C, (σ c).maxGenEigenspace (χ c)) = r * Module.finrank k ↥(⨅ c : C, (((Algebra.lmul k (k ⊗[ℤ] C)).toRingHom.comp (Algebra.TensorProduct.includeRight : C →ₐ[ℤ] k ⊗[ℤ] C).toRingHom) c).maxGenEigenspace (χ c)) := by
  first | (exact @GlobalTheory.WeightCount.finrank_weight_eq) | (exact GlobalTheory.WeightCount.finrank_weight_eq) | (intros; apply GlobalTheory.WeightCount.finrank_weight_eq <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankMulPowLeFinrankOfPowerSeriesStatement
section
open Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finrank_mul_pow_le_finrank_of_prod_mem : ∀ (D n : ℕ) (A : Type) [CommRing A] [Algebra ℂ A] (φ : Fin n → (A →ₐ[ℂ] MvPowerSeries (Fin D) ℂ)) (x : Fin D → A) (c : Fin D → ℂ), (∀ u : A, (∀ j, φ j u = 0) → u = 0) → (∀ j i, φ j (x i) = MvPowerSeries.X i + MvPowerSeries.C (c i)) → ∀ (F G : Submodule ℂ A) [Module.Finite ℂ F] [Module.Finite ℂ G] (m : ℕ), 0 < m → (∀ (f : Fin m → A) (a : Fin D → ℕ), (∀ l, f l ∈ F) → (∀ i, a i < m) → (∏ l, f l) * ∏ i, x i ^ a i ∈ G) → Module.finrank ℂ F * m ^ D ≤ Module.finrank ℂ G := by
  first | exact @GlobalTheory.finrank_mul_pow_le_finrank_of_powerSeries | exact GlobalTheory.finrank_mul_pow_le_finrank_of_powerSeries | (intros; apply GlobalTheory.finrank_mul_pow_le_finrank_of_powerSeries <;> assumption)
end

