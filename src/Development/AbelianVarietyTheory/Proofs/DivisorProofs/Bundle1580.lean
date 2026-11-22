import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMemChart
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0334
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.MemNonzeroLocusIffPowFn
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemLocalSubringGenericPoint
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0120
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.MemRangeOfForallHeightEqOneOfIsReflexive
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1537
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1555
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0014
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0897
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0035
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0026
import Formalism.LocalToGlobal.IndefiniteReal.BaseLiftsPackageOfPrimitiveLinks
import Formalism.LocalToGlobal.Divisibility.TrivialExtensionSideWellFormed
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1556
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0229

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalDegreeEqOrderSum
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CxPts GlobalTheory.VB

set_option autoImplicit false

namespace GlobalTheory.RatDegZeros

theorem flat_fst {k : Type} [CommRing k] {X : Scheme.{0}} (p : X ⟶ Sp k) : Flat (ratFibre.fst p) := by
  have h2 : Flat (spMap (Int.castRingHom ℚ)) := by
    refine (HasRingHomProperty.Spec_iff (P := @Flat)).mpr ?_
    change Module.Flat ℤ ℚ
    exact IsLocalization.flat ℚ (nonZeroDivisors ℤ)
  exact MorphismProperty.of_isPullback (ratFibre.isPullback p).flip h2

theorem isIso_stalkMap_and_injective : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k), (∀ y : ratFibre p, IsIso ((ratFibre.fst p).stalkMap y)) ∧ Function.Injective (ratFibre.fst p) := by
  intro k _ X p
  have h1 : IsPreimmersion (spMap (Int.castRingHom ℚ)) :=
    IsPreimmersion.of_isLocalization (R := ℤ) (S := ℚ) (nonZeroDivisors ℤ)
  have h3 : IsPreimmersion (ratFibre.fst p) := MorphismProperty.of_isPullback (ratFibre.isPullback p).flip h1
  have h4 := flat_fst p
  exact ⟨fun y => GenSpread.isIso_stalkMap_of_flat _ y, (ratFibre.fst p).isEmbedding.injective⟩

theorem mem_range_fst : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k) (x : X), CharZero (X.residueField x) → x ∈ Set.range (ratFibre.fst p) := by
  intro k _ X p x hx
  let q : Spec (X.residueField x) ⟶ Sp ℚ := Spec.map (CommRingCat.ofHom (algebraMap ℚ (X.residueField x)))
  let y0 := (ratFibre.isPullback p).lift (X.fromSpecResidueField x) q (specZIsTerminal.hom_ext _ _)
  let z : Spec (X.residueField x) := IsLocalRing.closedPoint (X.residueField x)
  refine ⟨y0 z, ?_⟩
  have e : (y0 ≫ ratFibre.fst p) z = X.fromSpecResidueField x z := by
    rw [(ratFibre.isPullback p).lift_fst]
  rw [Scheme.Hom.comp_apply] at e
  exact e.trans (X.fromSpecResidueField_apply x z)

theorem fst_genericPoint : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k) [IsIntegral X] [IsIntegral (ratFibre p)], ratFibre.fst p (genericPoint (ratFibre p)) = genericPoint X := by
  intro k _ X p _ _
  have := flat_fst p
  obtain ⟨z, hz, e⟩ := Flat.generalizingMap (ratFibre.fst p)
    (genericPoint_specializes (ratFibre.fst p (genericPoint (ratFibre p))))
  rw [← e, (hz.antisymm (genericPoint_specializes z)).eq]

theorem exists_finset_zeros : ∀ (K : Type) [Field K] (C : Scheme.{0}) [Algebra K Γ(C, ⊤)] [IsIntegral C], IsProjCurve K C → ∀ (L : LB C) (s : L.Sec), genericPoint C ∈ nonzeroLocus s → ∃ S : Finset C, (∀ y : C, y ∉ nonzeroLocus s → y ∈ S) ∧ ∀ y ∈ S, IsClosed ({y} : Set C) := by
  intro K _ C _ _ hC L s hs
  classical
  have := hC.isNoetherian
  have hZ : IsClosed ((nonzeroLocus s : Set C)ᶜ) := (nonzeroLocus s).isOpen.isClosed_compl
  have hfin := GlobalTheory.ProperCurve.finite_of_isClosed hC.dim_eq hZ (fun h => h hs)
  refine ⟨hfin.toFinset, fun y hy => hfin.mem_toFinset.2 hy, fun y hy => ?_⟩
  refine GlobalTheory.ProperCurve.isClosed_singleton hC.dim_eq ?_
  rintro rfl
  exact (hfin.mem_toFinset.1 hy) hs

theorem nonempty_residueField_equiv : ∀ (X Y : Scheme.{0}) (f : Y ⟶ X) (y : Y), IsIso (f.stalkMap y) → Nonempty (X.residueField (f y) ≃+* Y.residueField y) := by
  intro X Y f y h
  exact ⟨(IsLocalRing.ResidueField.mapEquiv (asIso (f.stalkMap y)).commRingCatIsoToRingEquiv)⟩

theorem residueDegree_eq_card : ∀ (C : Scheme.{0}) [Algebra ℚ Γ(C, ⊤)], IsProjCurve ℚ C → ∀ y : C, IsClosed ({y} : Set C) → Finite (C.residueField y →+* ℂ) ∧ (strHom ℚ C).residueDegree y = Nat.card (C.residueField y →+* ℂ) := by
  intro C _ hC y hy
  have := hC.isProperCurve.isProper
  have : JacobsonSpace C := LocallyOfFiniteType.jacobsonSpace (strHom ℚ C)
  have h₁ : LocallyOfFiniteType (C.fromSpecResidueField y) :=
    isClosed_singleton_iff_locallyOfFiniteType.mp hy
  generalize strHom ℚ C = f at *
  rw [residueDegree_eq_finrank]
  letI := algebraΓOfHom f
  letI := residueFieldAlgebraOver ℚ y
  have : CharZero (C.residueField y) := algebraRat.charZero _
  have hft : Algebra.FiniteType ℚ (C.residueField y) := by
    have e : C.fromSpecResidueField y ≫ f =
        Spec.map (CommRingCat.ofHom (algebraMap ℚ (C.residueField y))) := by
      obtain ⟨φ, hφ⟩ := Spec.map_surjective (C.fromSpecResidueField y ≫ f)
      rw [← hφ]
      congr 1
      ext1
      exact Subsingleton.elim _ _
    have h : LocallyOfFiniteType (C.fromSpecResidueField y ≫ f) :=
      MorphismProperty.comp_mem @LocallyOfFiniteType _ _ h₁ inferInstance
    rw [e] at h
    exact RingHom.finiteType_algebraMap.1 ((HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).mp h)
  have hf : Module.Finite ℚ (C.residueField y) := finite_of_finite_type_of_isJacobsonRing _ _
  have : NumberField (C.residueField y) := { to_finiteDimensional := by convert hf; exact Subsingleton.elim _ _ }
  refine ⟨inferInstance, ?_⟩
  rw [Nat.card_eq_fintype_card, NumberField.Embeddings.card]
  congr!
  exact Subsingleton.elim _ _

theorem isWeaklyRegular_germ : ∀ (Y : Scheme.{0}) [IsIntegral Y] (L : LB Y) (s : L.Sec), genericPoint Y ∈ nonzeroLocus s → ∀ (y : Y) (J : L.ι) (hJ : y ∈ L.U J), RingTheory.Sequence.IsWeaklyRegular ((QCoh.structureModule Y).presheaf.stalk y :) [Y.presheaf.germ _ y hJ (s.f J)] := by
  intro Y _ L s hs y J hJ
  refine ((QCoh.structureModuleStalkEquiv y).isWeaklyRegular_congr _).2 ?_
  rw [RingTheory.Sequence.isWeaklyRegular_singleton_iff]
  have hη : genericPoint Y ∈ L.U J := (genericPoint_specializes y).mem_open (L.U J).isOpen hJ
  have hu := (Y.mem_basicOpen _ _ hη).1 ((Cartier.mem_nonzeroLocus_iff s _ hη).1 hs)
  have h0 : Y.presheaf.germ _ y hJ (s.f J) ≠ 0 := fun h => by
    have : s.f J = 0 := germ_injective_of_isIntegral Y y hJ (h.trans (map_zero _).symm)
    rw [this, map_zero] at hu
    exact not_isUnit_zero hu
  exact (IsRegular.of_ne_zero h0).left.isSMulRegular

theorem length_eq_secOrd : ∀ (X Y : Scheme.{0}) (f : Y ⟶ X) (L : LB X) (hL : L.IsLB) (s : L.Sec) (y : Y), IsIso (f.stalkMap y) → ∀ (J : (L.pull f).ι) (hJ : y ∈ (L.pull f).U J), (Module.length (Y.presheaf.stalk y) (((QCoh.structureModule Y).presheaf.stalk y :) ⧸ (Ideal.ofList [Y.presheaf.germ _ y hJ ((secPull s f).f J)] • ⊤ : Submodule (Y.presheaf.stalk y) ((QCoh.structureModule Y).presheaf.stalk y :)))).toNat = secOrd hL s (f y) := by
  intro X Y f L hL s y h J hJ
  have hi : f y ∈ L.U (J PUnit.unit) := mem_pull.1 hJ
  have e : Y.presheaf.germ _ y hJ ((secPull s f).f J) =
      (asIso (f.stalkMap y)).commRingCatIsoToRingEquiv (X.presheaf.germ _ _ hi (s.f (J PUnit.unit))) :=
    (Y.presheaf.germ_res_apply _ y hJ _).trans (Scheme.Hom.germ_stalkMap_apply f _ y hi _).symm
  rw [secOrd_eq hL s hi, germOrd, ← ord_map_ringEquiv (asIso (f.stalkMap y)).commRingCatIsoToRingEquiv, ← e,
    Ring.ord, (Submodule.Quotient.equiv _ (Ideal.span {Y.presheaf.germ _ y hJ ((secPull s f).f J)})
      (QCoh.structureModuleStalkEquiv y) (by
        rw [Submodule.map_smul'', Submodule.map_top, LinearEquiv.range, smul_eq_mul, Ideal.mul_top,
          Ideal.ofList_singleton])).length_eq]

theorem ratDeg_eq_sum : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k) [IsIntegral X], IsProjCurve ℚ (ratFibre p) → ∀ (L : LB X) (hL : L.IsLB) (s : L.Sec), genericPoint X ∈ nonzeroLocus s → ∃ S : Finset X, (∀ x : X, CharZero (X.residueField x) → x ∉ nonzeroLocus s → x ∈ S) ∧ (∀ x ∈ S, Finite (X.residueField x →+* ℂ)) ∧ ratDeg p L = ∑ x ∈ S, (secOrd hL s x : ℤ) * (Nat.card (X.residueField x →+* ℂ) : ℤ) := by
  intro k _ X p _ hC L hL s hs
  classical
  have := hC.isIntegral
  obtain ⟨hiso, hinj⟩ := isIso_stalkMap_and_injective k X p
  have hL' : (L.pull (ratFibre.fst p)).IsLB := Semi.LB.isLB_pull hL _
  have hnz : ∀ y, y ∈ nonzeroLocus (secPull s (ratFibre.fst p)) ↔ ratFibre.fst p y ∈ nonzeroLocus s :=
    fun y => by rw [nonzeroLocus_secPull]; rfl
  have hs' : genericPoint (ratFibre p) ∈ nonzeroLocus (secPull s (ratFibre.fst p)) :=
    (hnz _).2 (by rw [fst_genericPoint k X p]; exact hs)
  obtain ⟨S', hS'z, hS'c⟩ := exists_finset_zeros ℚ (ratFibre p) hC _ _ hs'
  have hcard : ∀ y ∈ S', Finite (X.residueField (ratFibre.fst p y) →+* ℂ) ∧
      (ratFibre.snd p).residueDegree y = Nat.card (X.residueField (ratFibre.fst p y) →+* ℂ) := by
    intro y hy
    obtain ⟨e⟩ := nonempty_residueField_equiv X (ratFibre p) (ratFibre.fst p) y (hiso y)
    let E : (X.residueField (ratFibre.fst p y) →+* ℂ) ≃ ((ratFibre p).residueField y →+* ℂ) :=
      { toFun := fun g => g.comp e.symm.toRingHom
        invFun := fun g => g.comp e.toRingHom
        left_inv := fun g => by ext a; simp
        right_inv := fun g => by ext a; simp }
    obtain ⟨h₁, h₂⟩ := residueDegree_eq_card (ratFibre p) hC y (hS'c y hy)
    refine ⟨Finite.of_equiv _ E.symm, ?_⟩
    rw [← ratFibre.strHom_eq p, h₂, Nat.card_congr E]
  refine ⟨S'.image (ratFibre.fst p), ?_, ?_, ?_⟩
  · intro x hx hxs
    obtain ⟨y, rfl⟩ := mem_range_fst k X p x hx
    exact Finset.mem_image_of_mem _ (hS'z y ((hnz y).not.2 hxs))
  · intro x hx
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.1 hx
    exact (hcard y hy).1
  · let c : ratFibre p → (L.pull (ratFibre.fst p)).ι := fun y _ => (exists_mem_chart hL (ratFibre.fst p y)).choose
    have hc : ∀ y, y ∈ (L.pull (ratFibre.fst p)).U (c y) := fun y =>
      mem_pull.2 (exists_mem_chart hL (ratFibre.fst p y)).choose_spec
    have hP : IsProjOver (ratFibre.snd p) := by
      have := hC.isProjOver
      rwa [ratFibre.strHom_eq p] at this
    have key := CutDegree.interNum_eq_sum_length (ratFibre.snd p) hP hL' c hc S' hS'c
      [secPull s (ratFibre.fst p)] (QCoh.structureModule (ratFibre p))
      (fun y _ hy => hS'z y (hy _ (List.mem_singleton_self _)))
      (fun y _ => isWeaklyRegular_germ (ratFibre p) _ _ hs' y (c y) (hc y))
    have e1 : (fun _ : Fin [secPull s (ratFibre.fst p)].length => L.pull (ratFibre.fst p)) = ![L.pull (ratFibre.fst p)] :=
      funext fun i => by fin_cases i; rfl
    rw [e1] at key
    rw [ratDeg_eq_degLB hL, hC.degLB_eq_interNum hL', key, Finset.sum_image (fun a _ b _ h => hinj h)]
    push_cast
    refine Finset.sum_congr rfl fun y hy => ?_
    rw [(hcard y hy).2]
    congr 2
    exact length_eq_secOrd X (ratFibre p) (ratFibre.fst p) L hL s y (hiso y) (c y) (hc y)

end GlobalTheory.RatDegZeros
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RealLineIsLineOfPlace
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.DescB GlobalTheory.ThK.FlagCT GlobalTheory.ThK.FlagPar
open GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.LeviHC

namespace GlobalTheory.LeviHC

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra in

theorem isLineOf_of_isRealLine : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
    ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J →
    ∀ (τ : ∀ w : InfinitePlace F, EmbOver E w) (γ : ℝ → GAd σ J), IsRealLine σ J γ →
      ∃ (w : InfinitePlace F) (Z : Matrix (Fin n) (Fin n) ℂ), IsLineOf σ J (τ w) Z γ := by
  intro F E _ _ _ _ _ σ hcm n J _hJ τ γ hγ
  obtain ⟨w, τ', Z', -, hl⟩ := hγ
  choose y hy1 hy2 using hl
  have hinj : Function.Injective (GlobalTheory.Orb.archMat σ J τ') := fun a b e => by
    rw [GlobalTheory.Orb.archMat_eq_archEquiv J hcm, GlobalTheory.Orb.archMat_eq_archEquiv J hcm] at e
    exact (archEquiv J hcm τ').injective (Subtype.ext (Units.ext e))
  have hc : Continuous y := by
    rw [(GlobalTheory.Orb.isEmbedding_archMat J hcm τ').continuous_iff]
    have : (GlobalTheory.Orb.matCoord (GlobalTheory.Orb.archMat σ J τ') ∘ y) = fun t i j => NormedSpace.exp (t • Z') i j := by
      funext t i j
      simp only [Function.comp_apply, GlobalTheory.Orb.matCoord, hy2]
    rw [this]
    have hexp : Continuous fun t : ℝ => NormedSpace.exp (t • Z') :=
      NormedSpace.exp_continuous.comp (continuous_id.smul continuous_const)
    exact continuous_pi fun i => continuous_pi fun j => (continuous_apply_apply i j).comp hexp
  have h0 : y 0 = 1 := hinj (by rw [hy2, map_one, zero_smul, NormedSpace.exp_zero])
  have hm : ∀ s t, y (s + t) = y s * y t := fun s t => hinj (by
    rw [hy2, map_mul, hy2, hy2, add_smul]
    exact NormedSpace.exp_add_of_commute ((Commute.refl Z').smul_left _ |>.smul_right _))
  obtain ⟨Z, hZ⟩ := GlobalTheory.OneParamMatrix.eq_exp_of_continuous_oneParameter
    (fun t => GlobalTheory.Orb.archMat σ J (τ w) (y t)) ((GlobalTheory.Orb.continuous_archMat σ J (τ w)).comp hc)
    (by simp only [h0, map_one]) (fun s t => by simp only [hm, map_mul])
  exact ⟨w, Z, fun t => ⟨y t, hy1 t, hZ t⟩⟩

end GlobalTheory.LeviHC
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelativeCentre
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.DescB GlobalTheory.ThK.FlagCT GlobalTheory.ThK.FlagPar
open GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.LeviHC

noncomputable section

open Matrix GlobalTheory.SmoothForms

namespace GlobalTheory.LeviHC.RelCentre

variable {A : Type} [Ring A] [Algebra ℂ A] {n : ℕ} {X : Fin n → Fin n → A}

def blockOf {m o : Type} (N : Matrix (m × o) (m × o) ℂ) (i : o) : Matrix m m ℂ := Matrix.of fun I K => N (I, i) (K, i)

theorem blockOf_add {m o : Type} (N N' : Matrix (m × o) (m × o) ℂ) (i : o) :
    blockOf (N + N') i = blockOf N i + blockOf N' i := rfl

theorem blockOf_sub {m o : Type} (N N' : Matrix (m × o) (m × o) ℂ) (i : o) :
    blockOf (N - N') i = blockOf N i - blockOf N' i := rfl

theorem blockOf_smul {m o : Type} (c : ℂ) (N : Matrix (m × o) (m × o) ℂ) (i : o) :
    blockOf (c • N) i = c • blockOf N i := rfl

variable {m o : Type} [Fintype m] [DecidableEq m] [Fintype o] [DecidableEq o]

theorem blockOf_blockDiagonal (P : o → Matrix m m ℂ) (i : o) : blockOf (blockDiagonal P) i = P i := by
  ext I K; simp [blockOf]

theorem blockOf_bd_mul (P : o → Matrix m m ℂ) (N : Matrix (m × o) (m × o) ℂ) (i : o) :
    blockOf (blockDiagonal P * N) i = P i * blockOf N i := by
  ext I K
  simp [blockOf, Matrix.mul_apply, Fintype.sum_prod_type, blockDiagonal_apply]

theorem blockOf_mul_bd (P : o → Matrix m m ℂ) (N : Matrix (m × o) (m × o) ℂ) (i : o) :
    blockOf (N * blockDiagonal P) i = blockOf N i * P i := by
  ext I K
  simp [blockOf, Matrix.mul_apply, Fintype.sum_prod_type, blockDiagonal_apply]

variable (X) in

def phi (d : ℕ) {k : ℕ} (b : Fin k → A) :
    Matrix ((Fin d → Fin n) × Fin k) ((Fin d → Fin n) × Fin k) ℂ →ₗ[ℂ] A where
  toFun N := ∑ i, wordMap X d (blockOf N i) * b i
  map_add' N N' := by simp [blockOf_add, add_mul, Finset.sum_add_distrib]
  map_smul' c N := by simp [blockOf_smul, Finset.smul_sum, smul_mul_assoc]

theorem phi_apply (d : ℕ) {k : ℕ} (b : Fin k → A) (N) : phi X d b N = ∑ i, wordMap X d (blockOf N i) * b i := rfl

theorem phi_comm (hX : Formalism.REAL.GlRel X) (d : ℕ) {k : ℕ} (b : Fin k → A) (hb : ∀ i a c, X a c * b i = b i * X a c)
    (N : Matrix ((Fin d → Fin n) × Fin k) ((Fin d → Fin n) × Fin k) ℂ) (a c : Fin n) :
    X a c * phi X d b N - phi X d b N * X a c =
      phi X d b (blockDiagonal (fun _ => polar n d a c) * N - N * blockDiagonal (fun _ => polar n d a c)) := by
  simp only [phi_apply, blockOf_sub, blockOf_bd_mul, blockOf_mul_bd, ← GlobalTheory.T.commutator_glGenerator_tensorWordMapMatrixUnits A n X hX, Finset.mul_sum,
    Finset.sum_mul, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [sub_mul, mul_assoc, mul_assoc, ← hb, ← mul_assoc, ← mul_assoc]

end GlobalTheory.LeviHC.RelCentre

namespace GlobalTheory.LeviHC.RelCentre

variable {A : Type} [Ring A] [Algebra ℂ A] {n : ℕ} {X : Fin n → Fin n → A}

theorem filtB_ad (hX : Formalism.REAL.GlRel X) {B : Subalgebra ℂ A} (hB : ∀ b ∈ B, ∀ i j, X i j * b = b * X i j) (d : ℕ)
    (a c : Fin n) {y : A} (hy : y ∈ filt X d * Subalgebra.toSubmodule B) :
    X a c * y - y * X a c ∈ filt X d * Subalgebra.toSubmodule B := by
  refine Submodule.mul_induction_on hy (fun u hu v hv => ?_) fun x y hx hy => ?_
  · have e : X a c * (u * v) - u * v * X a c = (X a c * u - u * X a c) * v := by
      rw [sub_mul, mul_assoc u v, ← hB v hv, ← mul_assoc, ← mul_assoc]
    rw [e]
    exact Submodule.mul_mem_mul (filt_ad hX d a c hu) hv
  · have e : X a c * (x + y) - (x + y) * X a c = (X a c * x - x * X a c) + (X a c * y - y * X a c) := by
      rw [mul_add, add_mul]; abel
    rw [e]; exact add_mem hx hy

theorem exists_sum {B : Subalgebra ℂ A} {d : ℕ} {u : A}
    (hu : u ∈ LinearMap.range (wordMap X d) * Subalgebra.toSubmodule B) :
    ∃ (k : ℕ) (M : Fin k → Matrix (Fin d → Fin n) (Fin d → Fin n) ℂ) (b : Fin k → A),
      (∀ i, b i ∈ B) ∧ u = ∑ i, wordMap X d (M i) * b i := by
  refine Submodule.mul_induction_on hu (fun x hx v hv => ?_) fun x y hx hy => ?_
  · obtain ⟨M, rfl⟩ := hx
    exact ⟨1, fun _ => M, fun _ => v, fun _ => hv, by simp⟩
  · obtain ⟨k, M, b, hb, rfl⟩ := hx
    obtain ⟨k', M', b', hb', rfl⟩ := hy
    refine ⟨k + k', Fin.append M M', Fin.append b b', fun i => ?_, ?_⟩
    · refine Fin.addCases (fun i => ?_) (fun i => ?_) i
      · simpa using hb i
      · simpa using hb' i
    · rw [Fin.sum_univ_add]; simp

theorem exists_filtB {B : Subalgebra ℂ A} (hB : ∀ b ∈ B, ∀ i j, X i j * b = b * X i j) {z : A}
    (hz : z ∈ Algebra.adjoin ℂ (Set.range fun p : Fin n × Fin n => X p.1 p.2) ⊔ B) :
    ∃ d, z ∈ filt X d * Subalgebra.toSubmodule B := by
  set S := Algebra.adjoin ℂ (Set.range fun p : Fin n × Fin n => X p.1 p.2)
  have hSB : ∀ s ∈ S, ∀ b ∈ B, b * s = s * b := by
    intro s hs b hb
    have : S ≤ Subalgebra.centralizer ℂ {b} := by
      refine Algebra.adjoin_le ?_
      rintro _ ⟨p, rfl⟩ g hg
      rw [Set.mem_singleton_iff.1 hg]
      exact (hB b hb p.1 p.2).symm
    exact this hs b rfl
  set W := Subalgebra.toSubmodule S * Subalgebra.toSubmodule B
  have mono : ∀ {P Q R U : Submodule ℂ A}, P ≤ Q → R ≤ U → P * R ≤ Q * U := fun h h' =>
    Submodule.mul_le.2 fun p hp r hr => Submodule.mul_mem_mul (h hp) (h' hr)
  have oS : (1 : A) ∈ Subalgebra.toSubmodule S := one_mem S
  have oB : (1 : A) ∈ Subalgebra.toSubmodule B := one_mem B
  have hmul : W * W ≤ W := by
    have h1 : Subalgebra.toSubmodule B * Subalgebra.toSubmodule S ≤ W :=
      Submodule.mul_le.2 fun b hb s hs => by rw [hSB s hs b hb]; exact Submodule.mul_mem_mul hs hb
    have h2 : Subalgebra.toSubmodule S * Subalgebra.toSubmodule S ≤ Subalgebra.toSubmodule S :=
      Submodule.mul_le.2 fun s hs t ht => show s * t ∈ S from mul_mem (show s ∈ S from hs) (show t ∈ S from ht)
    have h3 : Subalgebra.toSubmodule B * Subalgebra.toSubmodule B ≤ Subalgebra.toSubmodule B :=
      Submodule.mul_le.2 fun s hs t ht => show s * t ∈ B from mul_mem (show s ∈ B from hs) (show t ∈ B from ht)
    calc W * W = Subalgebra.toSubmodule S * (Subalgebra.toSubmodule B * Subalgebra.toSubmodule S) *
          Subalgebra.toSubmodule B := by simp only [W, mul_assoc]
      _ ≤ Subalgebra.toSubmodule S * W * Subalgebra.toSubmodule B := mono (mono le_rfl h1) le_rfl
      _ = (Subalgebra.toSubmodule S * Subalgebra.toSubmodule S) *
          (Subalgebra.toSubmodule B * Subalgebra.toSubmodule B) := by simp only [W, mul_assoc]
      _ ≤ W := mono h2 h3
  let T : Subalgebra ℂ A := Submodule.toSubalgebra W
    (by simpa using Submodule.mul_mem_mul oS oB)
    (fun x y hx hy => hmul (Submodule.mul_mem_mul hx hy))
  have hT : S ⊔ B ≤ T := by
    refine sup_le (fun s hs => ?_) fun b hb => ?_
    · show s ∈ W
      simpa using Submodule.mul_mem_mul (show s ∈ Subalgebra.toSubmodule S from hs) oB
    · show b ∈ W
      simpa using Submodule.mul_mem_mul oS (show b ∈ Subalgebra.toSubmodule B from hb)
  have hW : W ≤ ⨆ d, filt X d * Subalgebra.toSubmodule B := Submodule.mul_le.2 fun s hs b hb => by
    obtain ⟨d, hd⟩ := exists_filt (E := X) hs
    exact Submodule.mem_iSup_of_mem d (Submodule.mul_mem_mul hd hb)
  have hz' : z ∈ ⨆ d, filt X d * Subalgebra.toSubmodule B := hW (hT hz)
  refine (Submodule.mem_iSup_of_directed _ (Monotone.directed_le fun d d' h => ?_)).1 hz'
  exact Submodule.mul_le.2 fun u hu v hv => Submodule.mul_mem_mul (filt_mono h hu) hv

end GlobalTheory.LeviHC.RelCentre

namespace GlobalTheory.LeviHC.RelCentre

variable {A : Type} [Ring A] [Algebra ℂ A] {n : ℕ} {X : Fin n → Fin n → A}

theorem central_of_filtB (hX : Formalism.REAL.GlRel X) (B : Subalgebra ℂ A) (hB : ∀ b ∈ B, ∀ i j, X i j * b = b * X i j)
    (d : ℕ) : ∀ z ∈ filt X d * Subalgebra.toSubmodule B, (∀ a c, X a c * z = z * X a c) →
      z ∈ Algebra.adjoin ℂ (Set.range (gelfA X)) ⊔ B := by
  induction d with
  | zero =>
    intro z hz _
    have h0 : filt X 0 ≤ ⊥ := iSup₂_le fun k hk => absurd hk (Nat.not_lt_zero k)
    have : filt X 0 * Subalgebra.toSubmodule B ≤ ⊥ :=
      Submodule.mul_le.2 fun u hu v _ => by rw [(Submodule.mem_bot ℂ).1 (h0 hu), zero_mul]; exact zero_mem _
    rw [(Submodule.mem_bot ℂ).1 (this hz)]
    exact zero_mem _
  | succ d ih =>
    intro z hz hc
    have hz' : z ∈ LinearMap.range (wordMap X d) * Subalgebra.toSubmodule B ⊔ filt X d * Subalgebra.toSubmodule B := by
      rw [← Submodule.sup_mul]
      exact (Submodule.mul_le.2 fun u hu v hv => Submodule.mul_mem_mul (filt_succ d hu) hv) hz
    obtain ⟨u, hu, y, hy, rfl⟩ := Submodule.mem_sup.1 hz'
    obtain ⟨k, M, b, hb, rfl⟩ := exists_sum hu
    have hbX : ∀ i a c, X a c * b i = b i * X a c := fun i a c => hB _ (hb i) a c
    set FB := filt X d * Subalgebra.toSubmodule B
    have hM : phi X d b (blockDiagonal M) = ∑ i, wordMap X d (M i) * b i := by
      simp [phi_apply, blockOf_blockDiagonal]
    obtain ⟨M₀, h1, h2⟩ := GlobalTheory.T.commutant_lift_mod_stable_selfAdjoint _
      (Set.range fun p : Fin n × Fin n => blockDiagonal fun _ : Fin k => polar n d p.1 p.2)
      (FB.comap (phi X d b))
      (by
        rintro _ ⟨p, rfl⟩
        exact ⟨(p.2, p.1), by rw [blockDiagonal_conjTranspose]; simp [polar_conjTranspose]⟩)
      (by
        rintro _ ⟨p, rfl⟩ N hN
        rw [Submodule.mem_comap, ← phi_comm hX d b hbX]
        exact filtB_ad hX hB d _ _ hN)
      (blockDiagonal M)
      (by
        rintro _ ⟨p, rfl⟩
        rw [Submodule.mem_comap, ← phi_comm hX d b hbX, hM]
        have h3 := neg_mem (filtB_ad hX hB d p.1 p.2 hy)
        have h4 := hc p.1 p.2
        rw [mul_add, add_mul] at h4
        convert h3 using 1
        rw [neg_sub, sub_eq_sub_iff_add_eq_add, h4, add_comm])
    have h4 : Submodule.span ℂ (Set.range (permMat n d)) ≤
        (Subalgebra.toSubmodule (Algebra.adjoin ℂ (Set.range (gelfA X))) ⊔ filt X d).comap (wordMap X d) := by
      rw [Submodule.span_le]
      rintro _ ⟨π, rfl⟩
      obtain ⟨c, hc1, hc2⟩ := GlobalTheory.T.permutationWord_gelfandPolynomial_mod_shorter A n X hX d π
      exact Submodule.mem_sup.2 ⟨c, hc1, _, hc2, by abel⟩
    have h5 : ∀ i, blockOf M₀ i ∈ Submodule.span ℂ (Set.range (permMat n d)) := fun i => by
      refine GlobalTheory.T.bicommutant_tensorFactorPerm_mem_span n d _ fun T hT => ?_
      have : Algebra.adjoin ℂ (Set.range fun p : Fin n × Fin n => polar n d p.1 p.2) ≤
          Subalgebra.centralizer ℂ {blockOf M₀ i} := by
        refine Algebra.adjoin_le ?_
        rintro _ ⟨p, rfl⟩ g hg
        rw [Set.mem_singleton_iff.1 hg]
        have := congrArg (fun N => blockOf N i) (h2 _ ⟨p, rfl⟩)
        simp only [blockOf_bd_mul, blockOf_mul_bd] at this
        exact this.symm
      exact this (GlobalTheory.T.mem_adjoin_glAction_of_commute_tensorPerm n d T hT) _ rfl
    have h6 : ∀ i, ∃ c ∈ Algebra.adjoin ℂ (Set.range (gelfA X)), ∃ f ∈ filt X d,
        wordMap X d (blockOf M₀ i) = c + f := fun i => by
      obtain ⟨c, hc1, f, hf, e⟩ := Submodule.mem_sup.1 (h4 (h5 i))
      exact ⟨c, hc1, f, hf, e.symm⟩
    choose c hc1 f hf hcf using h6
    have h7 : ∑ i, wordMap X d (M i) * b i + y - ∑ i, c i * b i ∈ FB := by
      have e : ∑ i, wordMap X d (M i) * b i + y - ∑ i, c i * b i =
          phi X d b (blockDiagonal M - M₀) + ∑ i, f i * b i + y := by
        rw [map_sub, hM, phi_apply]
        simp only [hcf, add_mul, Finset.sum_add_distrib]
        abel
      rw [e]
      refine add_mem (add_mem h1 (sum_mem fun i _ => Submodule.mul_mem_mul (hf i) (hb i))) hy
    have hcX : ∀ a a', X a a' * ∑ i, c i * b i = (∑ i, c i * b i) * X a a' := fun a a' => by
      rw [Finset.mul_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← mul_assoc, gelf_adjoin_comm hX (hc1 i), mul_assoc, hbX, mul_assoc]
    have h8 := ih _ h7 fun a a' => by rw [mul_sub, sub_mul, hc, hcX]
    have h9 : ∑ i, c i * b i ∈ Algebra.adjoin ℂ (Set.range (gelfA X)) ⊔ B :=
      sum_mem fun i _ => mul_mem (le_sup_left (a := Algebra.adjoin ℂ (Set.range (gelfA X))) (hc1 i))
        (le_sup_right (b := B) (hb i))
    simpa using add_mem h8 h9

end GlobalTheory.LeviHC.RelCentre

namespace GlobalTheory.LeviHC

theorem relativeCentre : RelativeCentre := by
  intro A _ _ n X hX B hB z hz hc
  obtain ⟨d, hd⟩ := RelCentre.exists_filtB hB hz
  exact RelCentre.central_of_filtB hX B hB d z hd hc

end GlobalTheory.LeviHC
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RowTypeHasSphericalHeckeEigensystemStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Hk3 (Core Good IsSF SchurAll TwoSided FixAll EEc Wcc eH IsLab HoweUnram SphOp hyp)
open GlobalTheory.StdFrame (StdPsi)
attribute [local instance] Formalism.IndefR.principalLevelFrame.instCMHostI
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.row_type_has_spherical_hecke_eigensystem : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A) {s : ℕ}, A.fam.Ok s → Core R F → (∀ χ ∈ A.X, chiIdem χ * lvlIdem F.P0 F.ψ0 ≠ 0) → ∀ SF, IsSF R SF → ∀ {n : ℕ} (hF : D.host.F = maximalRealSubfield D.host.E) (PY : principalLevelFrame.RowPsi (Yc D 0) n) (PW : ∀ i, principalLevelFrame.RowPsi (Wc D i) n), StdPsi hF PY → (∀ i, StdPsi hF (PW i)) → ∀ π, π ∈ principalLevelFrame.OccRows R.θ PY (R.MY 0) (fun b => (levS _ (R.βY 0) (R.dat0 (R.levR F b)))) (fun b => (levChi _ (R.βY 0) (R.dat0 (R.levR F b)))) (fun _ => R.e0) → ∀ i0, ∃ c, principalLevelFrame.IsEigOf (PW i0) (levS _ (R.βW i0) (R.datWp i0 (R.levL F false (sg0 D A)))) (levChi _ (R.βW i0) (R.datWp i0 (R.levL F false (sg0 D A)))) SF π c := by
  first | exact @GlobalTheory.RowEig.row_type_eig | exact GlobalTheory.RowEig.row_type_eig | (intros; apply GlobalTheory.RowEig.row_type_eig <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchrodingerIntertwinerL2ConstantStatement
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.WeilTr MeasureTheory
open scoped Matrix ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.schrodinger_intertwiner_l2_constant : ∀ (F : Type) [Field F] [NumberField F] [Invertible (2 : mixedEmbedding.mixedSpace F)] (κ : Type) [Fintype κ]
    (ψ : AddChar (mixedEmbedding.mixedSpace F) ℂ),
    (∀ a, ψ a = Complex.exp (-(2 * Real.pi * Complex.I) * (Algebra.trace ℝ (mixedEmbedding.mixedSpace F) a : ℝ))) →
    ∀ (T : SInf F κ →L[ℂ] SInf F κ)
      (A : (κ → mixedEmbedding.mixedSpace F) × (κ → mixedEmbedding.mixedSpace F) →
        (κ → mixedEmbedding.mixedSpace F) × (κ → mixedEmbedding.mixedSpace F)),
      (∀ w (f g : SInf F κ), (g : (κ → mixedEmbedding.mixedSpace F) → ℂ) = schr ψ w f →
        (T g : (κ → mixedEmbedding.mixedSpace F) → ℂ) = schr ψ (A w) (T f)) →
      ∃ c : ℝ, 0 ≤ c ∧ ∀ μ : @Measure (κ → mixedEmbedding.mixedSpace F) (borel _),
        @Measure.IsAddHaarMeasure _ _ _ (borel _) μ → ∀ f f' : SInf F κ,
          @integral _ ℂ _ _ (borel _) μ (fun x => T f x * starRingEnd ℂ (T f' x)) =
            (c : ℂ) * @integral _ ℂ _ _ (borel _) μ (fun x => f x * starRingEnd ℂ (f' x)) := by
  first | exact @GlobalTheory.SvNForm.schrodinger_intertwiner_l2_const | exact GlobalTheory.SvNForm.schrodinger_intertwiner_l2_const | (intros; apply GlobalTheory.SvNForm.schrodinger_intertwiner_l2_const <;> assumption)
end

