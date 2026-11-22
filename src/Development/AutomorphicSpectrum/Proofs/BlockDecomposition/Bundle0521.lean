import Mathlib
import GroundTheory.GlobalFields.AnalyticClassNumber.HeckeContinued
import GroundTheory.GlobalFields.TateThesis.RootNumberLocalFinite
import GroundTheory.GlobalFields.IdeleGroups.ClassGroup
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PartialZetaFunctionalEquation
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0513
import GroundTheory.AutomorphicForms.AnisotropicUnitaryHeight
import GroundTheory.AutomorphicForms.ReductionMahler
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0009
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.NotIsFinitePartOfBot
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.CuspRapidDecaySiegelGL
import GroundTheory.AutomorphicForms.CuspidalDiscreteness.CuspFormsHeight
import GroundTheory.AutomorphicForms.CuspidalDiscreteness.DecayUniform
import GroundTheory.AutomorphicForms.AutomorphicFormSpaces.GKStable
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0500
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0491
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0490
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0275
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0381
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0436
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0300
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0301
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0507
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0295
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0298
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HeckeCosetSumCompact
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.Bundle0001
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HeckeOperatorJacquetEigenRight
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.SquareIntegrableTempered.CentredSegments.IrreducibleUnif
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0003
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0508
import Development.WeilBound.ThetaLifts.LatticeBasics.Bundle0008
import Development.WeilBound.ThetaLifts.LatticeBasics.Bundle0015
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0509
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.RealDescent.RealLeviDescent.Bundle0001
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0510
import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.LocalBaseChange.StrictDominanceCasselman.IsStrictlyDominant

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsHeckeCharacterOfClassGroup
section
open NumberField GroundTheory.Global GroundTheory.Global.IdeleGroup
open scoped nonZeroDivisors

namespace GlobalTheory.CompanionTheory.PartialZeta

variable {F : Type} [Field F] [NumberField F]

noncomputable def classCircle (ψ : AddChar (Additive (ClassGroup (𝓞 F))) ℂ) :
    ClassGroup (𝓞 F) →* Circle where
  toFun c := AddChar.circleEquivComplex.symm ψ (Additive.ofMul c)
  map_one' := by
    rw [ofMul_one]
    exact AddChar.map_zero_eq_one _
  map_mul' a b := by
    rw [ofMul_mul]
    exact AddChar.map_add_eq_mul _ _ _

theorem coe_classCircle (ψ : AddChar (Additive (ClassGroup (𝓞 F))) ℂ) (c : ClassGroup (𝓞 F)) :
    (classCircle ψ c : ℂ) = ψ (Additive.ofMul c) := by
  rfl

theorem continuous_comp_toClassGroup (φ : ClassGroup (𝓞 F) →* Circle) :
    Continuous (φ.comp (IdeleClassGroup.toClassGroup (K := F))) := by
  refine continuous_of_continuousAt_one _ ?_
  have hU : IsOpen ((IdeleClassGroup.mk F) '' (standardOpenSubgroup F : Set (IdeleGroup F))) :=
    IdeleClassGroup.isOpenMap_mk (K := F) _ (isOpen_standardOpenSubgroup F)
  have h1 : (1 : IdeleClassGroup F) ∈ (IdeleClassGroup.mk F) '' (standardOpenSubgroup F : Set (IdeleGroup F)) :=
    ⟨1, (standardOpenSubgroup F).one_mem, map_one _⟩
  rw [ContinuousAt, map_one]
  refine tendsto_nhds_of_eventually_eq ?_
  filter_upwards [hU.mem_nhds h1] with y hy
  obtain ⟨x, hx, rfl⟩ := hy
  have hx1 : IdeleGroup.toFractionalIdeal x = 1 := by
    rw [← MonoidHom.mem_ker, IdeleGroup.ker_toFractionalIdeal]
    exact hx
  rw [MonoidHom.comp_apply, IdeleClassGroup.toClassGroup_mk, IdeleGroup.toClassGroup_apply, hx1,
    map_one, map_one]

noncomputable def classHecke (ψ : AddChar (Additive (ClassGroup (𝓞 F))) ℂ) : HeckeCharacter F where
  toMonoidHom := (classCircle ψ).comp IdeleClassGroup.toClassGroup
  continuous_toFun := continuous_comp_toClassGroup _

theorem classHecke_toIdele (ψ : AddChar (Additive (ClassGroup (𝓞 F))) ℂ) (x : IdeleGroup F) :
    (classHecke ψ).toIdele x = classCircle ψ (IdeleGroup.toClassGroup x) :=
  rfl

theorem standardOpenSubgroup_le_ker (ψ : AddChar (Additive (ClassGroup (𝓞 F))) ℂ) :
    standardOpenSubgroup F ≤ (classHecke ψ).toIdele.ker := by
  intro x hx
  have h1 : IdeleGroup.toFractionalIdeal x = 1 := by
    rw [← MonoidHom.mem_ker, IdeleGroup.ker_toFractionalIdeal]
    exact hx
  rw [MonoidHom.mem_ker, classHecke_toIdele, IdeleGroup.toClassGroup_apply, h1, map_one, map_one]

theorem idealLevel_top : idealLevel (⊤ : Ideal (𝓞 F)) = finiteLevel 0 := by
  show finiteLevel (fun v => multiplicity v.asIdeal (⊤ : Ideal (𝓞 F))) = finiteLevel 0
  congr 1
  funext v
  rw [Pi.zero_apply, multiplicity_eq_zero]
  intro h
  exact v.isPrime.ne_top (top_le_iff.mp (Ideal.le_of_dvd h))

theorem conductor_classHecke (ψ : AddChar (Additive (ClassGroup (𝓞 F))) ℂ) :
    (classHecke ψ).conductor = ⊤ := by
  have hne : (⊤ : Ideal (𝓞 F)) ≠ ⊥ := top_ne_bot
  have hle : Subgroup.map ofFinite (idealLevel (⊤ : Ideal (𝓞 F))) ≤ (classHecke ψ).toIdele.ker := by
    rintro _ ⟨z, hz, rfl⟩
    apply standardOpenSubgroup_le_ker ψ
    rw [mem_standardOpenSubgroup_iff_ord]
    intro v
    rw [idealLevel_top] at hz
    apply ord_eq_zero_of_mem_unitsLevel (n := 0)
    rw [← finiteComponent_toFinite, toFinite_ofFinite]
    exact Subgroup.mem_comap.mp (Subgroup.mem_iInf.mp hz v)
  have hd := ((classHecke ψ).map_idealLevel_le_ker_iff hne).mp hle
  exact top_le_iff.mp (Ideal.le_of_dvd hd)

theorem coeff_classHecke (ψ : AddChar (Additive (ClassGroup (𝓞 F))) ℂ)
    (J : Ideal (𝓞 F)) (hJ : J ≠ ⊥) :
    (classHecke ψ).coeff J =
      ψ (Additive.ofMul (ClassGroup.mk0 ⟨J, mem_nonZeroDivisors_of_ne_zero hJ⟩)) := by
  have hprime : ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 F),
      (classHecke ψ).coeff v.asIdeal =
        ψ (Additive.ofMul (ClassGroup.mk0 ⟨v.asIdeal, mem_nonZeroDivisors_of_ne_zero v.ne_bot⟩)) := by
    intro v
    have hv : ¬ v.asIdeal ∣ (classHecke ψ).conductor := by
      rw [conductor_classHecke]
      intro h
      exact v.isPrime.ne_top (top_le_iff.mp (Ideal.le_of_dvd h))
    rw [HeckeCharacter.coeff_asIdeal_of_not_dvd _ hv]
    obtain ⟨x, hx, hxI⟩ := exists_mem_primeToLevel (primeIdealUnit_mem_idealsPrimeTo hv)
    have heq : (primeIdealUnit v : (FractionalIdeal (𝓞 F)⁰ F)ˣ) =
        FractionalIdeal.mk0 F ⟨v.asIdeal, mem_nonZeroDivisors_of_ne_zero v.ne_bot⟩ :=
      Units.ext (by rw [coe_primeIdealUnit, FractionalIdeal.coe_mk0])
    rw [HeckeCharacter.idealCharacter_apply _ hx ⟨primeIdealUnit v, primeIdealUnit_mem_idealsPrimeTo hv⟩ hxI,
      classHecke_toIdele, coe_classCircle, IdeleGroup.toClassGroup_apply, hxI, heq, ClassGroup.mk_mk0]
  refine UniqueFactorizationMonoid.induction_on_prime (P := fun I : Ideal (𝓞 F) => ∀ hI : I ≠ ⊥,
      (classHecke ψ).coeff I =
        ψ (Additive.ofMul (ClassGroup.mk0 ⟨I, mem_nonZeroDivisors_of_ne_zero hI⟩))) J ?_ ?_ ?_ hJ
  · intro h
    exact absurd Ideal.zero_eq_bot h
  · intro x hx hx0
    obtain rfl := Ideal.isUnit_iff.mp hx
    have h1 : (⟨⊤, mem_nonZeroDivisors_of_ne_zero hx0⟩ : (Ideal (𝓞 F))⁰) = 1 :=
      Subtype.ext Ideal.one_eq_top.symm
    rw [HeckeCharacter.coeff_top, h1, map_one, ofMul_one, AddChar.map_zero_eq_one]
  · intro a p ha hp ih hpa
    have ha' : a ≠ ⊥ := by
      rw [← Ideal.zero_eq_bot]
      exact ha
    have hp0 : p ≠ ⊥ := by
      rw [← Ideal.zero_eq_bot]
      exact hp.ne_zero
    have hv := hprime ⟨p, Ideal.isPrime_of_prime hp, hp0⟩
    have hmk : (⟨p * a, mem_nonZeroDivisors_of_ne_zero hpa⟩ : (Ideal (𝓞 F))⁰) =
        ⟨p, mem_nonZeroDivisors_of_ne_zero hp0⟩ * ⟨a, mem_nonZeroDivisors_of_ne_zero ha'⟩ :=
      Subtype.ext rfl
    rw [HeckeCharacter.coeff_mul, ih ha', hmk, map_mul, ofMul_mul, AddChar.map_add_eq_mul]
    congr 1

end GlobalTheory.CompanionTheory.PartialZeta
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsNearMinimalVector
section
noncomputable section
open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet PositivityTheory.ThKR GlobalTheory.CompanionTheory.RedCov
open Formalism.UG (cT)
open scoped TensorProduct NNReal ENNReal

namespace GlobalTheory.CompanionTheory.RedCov

open GroundTheory.Automorphic GroundTheory.Automorphic.Anisotropic GroundTheory.Automorphic.Reduction

section NearMin

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {n : ℕ}

def ratCoords [Algebra.IsQuadraticExtension F E] (u : Fin n → E) :
    Fin (Fintype.card (Fin n × Fin (Module.finrank F E))) → F :=
  resVec (Module.finBasis F E) F (fun i => inclR (F := F) F (u i))

theorem hv_eq_adelicNorm_resVec [Algebra.IsQuadraticExtension F E] (ξ : Fin n → AF F ⊗[F] E) :
    hv (F := F) (E := E) ξ = adelicNorm (resVec (Module.finBasis F E) (AF F) ξ) := rfl

theorem ratCoords_ne_zero [Algebra.IsQuadraticExtension F E] {u : Fin n → E} (hu : u ≠ 0) :
    ratCoords (F := F) u ≠ 0 := by
  intro h0
  apply hu
  have h1 : (fun i => inclR (F := F) F (u i)) = fun _ : Fin n => (0 : F ⊗[F] E) := by
    apply resVec_injective (Module.finBasis F E) F
    rw [show resVec (Module.finBasis F E) F (fun i => inclR (F := F) F (u i)) = 0 from h0]
    funext p
    simp [resVec, coordsVec]
  funext i
  have h2 := congrFun h1 i
  exact Algebra.TensorProduct.includeRight_injective (algebraMap F F).injective
    (h2.trans (map_zero _).symm)

theorem resVec_ratV [Algebra.IsQuadraticExtension F E] (u : Fin n → E) :
    resVec (Module.finBasis F E) (AF F) (ratV F u) = ratVec (ratCoords (F := F) u) := by
  have h := resVec_baseMap (Module.finBasis F E) (Algebra.ofId F (AF F))
    (fun i => inclR (F := F) F (u i))
  have e : (fun i => baseMap (Algebra.ofId F (AF F)) (inclR (F := F) F (u i))) = ratV F u := by
    funext i
    simp [ratV, inclR, baseMap]
  rw [e] at h
  rw [h]
  rfl

variable (σ : E →ₐ[F] E) (J : Matrix (Fin n) (Fin n) E)

theorem exists_pos_le_hgt [Algebra.IsQuadraticExtension F E] (g : GAd σ J) :
    ∃ c : ℝ, 0 < c ∧ ∀ u : Fin n → E, u ≠ 0 → c ≤ hgt σ J g u := by
  set T := trHom (Module.finBasis F E) (AF F) (matHom _ σ J g) with hT
  obtain ⟨P, hP, h⟩ := exists_adelicNorm_vecMul_le_mul (K := F) (C := {T⁻¹}) isCompact_singleton
  refine ⟨1 / P, one_div_pos.2 hP, fun u hu => ?_⟩
  have hx := ratCoords_ne_zero (F := F) hu
  have e2 : hgt σ J g u = adelicNorm (ratVec (ratCoords (F := F) u) ᵥ* (T : Matrix (Fin (Fintype.card (Fin n × Fin (Module.finrank F E))))
      (Fin (Fintype.card (Fin n × Fin (Module.finrank F E)))) (AF F))) := by
    rw [hT, ← resVec_ratV, resVec_vecMul_trHom, ← hv_eq_adelicNorm_resVec, hgt, map_inv]
  have h3 := h T⁻¹ rfl _ ((hasFiniteContent_ratVec hx).vecMul T)
  rw [← e2, Matrix.vecMul_vecMul, ← Units.val_mul, mul_inv_cancel, Units.val_one,
    Matrix.vecMul_one] at h3
  rw [div_le_iff₀ hP, mul_comm]
  exact (one_le_adelicNorm_ratVec hx).trans h3

end NearMin

theorem exists_isotropic_of_isWittFrame {F E : Type} [Field F] [Field E] [Algebra F E]
    {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {r : ℕ}
    {X Y : Matrix (Fin n) (Fin (r + 1)) E} (h : IsWittFrame σ J X Y) :
    ∃ v : Fin n → E, v ≠ 0 ∧ hE σ J v v = 0 := by
  refine ⟨Xᵀ 0, fun h0 => ?_, ?_⟩
  · have h1 := congrFun (congrFun h.xy 0) 0
    have hc : ∀ i, X i 0 = 0 := fun i => congrFun h0 i
    simp [cT, Matrix.mul_apply, hc] at h1
  · have h1 := congrFun (congrFun h.xx 0) 0
    simp only [cT, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, Finset.sum_mul, Matrix.zero_apply] at h1
    rw [Finset.sum_comm] at h1
    simpa [hE, Formalism.UG.hform] using h1

theorem exists_nearMin : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (r : ℕ) (X Y : Matrix (Fin n) (Fin (r + 1)) E), IsWittFrame σ J X Y → ∀ g : GAd σ J, ∃ v, NearMin σ J g v := by
  intro F E _ _ _ _ _ σ hCM n J _ r X Y hW g
  haveI : Algebra.IsQuadraticExtension F E := ⟨hCM.2.2.1⟩
  obtain ⟨c, hc, hlow⟩ := exists_pos_le_hgt σ J g
  obtain ⟨v₀, hv₀, hi₀⟩ := exists_isotropic_of_isWittFrame hW
  let S : Set ℝ := {t | ∃ u : Fin n → E, u ≠ 0 ∧ hE σ J u u = 0 ∧ t = hgt σ J g u}
  have hne : S.Nonempty := ⟨_, v₀, hv₀, hi₀, rfl⟩
  have hbdd : BddBelow S := ⟨c, by rintro _ ⟨u, hu, -, rfl⟩; exact hlow u hu⟩
  have hm : c ≤ sInf S := le_csInf hne (by rintro _ ⟨u, hu, -, rfl⟩; exact hlow u hu)
  have hm0 : 0 < sInf S := hc.trans_le hm
  obtain ⟨_, ⟨v, hv, hi, rfl⟩, hlt⟩ := exists_lt_of_csInf_lt hne (show sInf S < 2 * sInf S by linarith)
  refine ⟨v, hv, hi, fun u hu hiu => ?_⟩
  have : sInf S ≤ hgt σ J g u := csInf_le hbdd ⟨u, hu, hiu, rfl⟩
  linarith

end GlobalTheory.CompanionTheory.RedCov

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteAdelicRestrictionMeasure
section
open NumberField MeasureTheory Topology Matrix GlobalTheory.AutomorphicL2Unitary GlobalTheory.DiscreteSum GlobalTheory.OpTrace GlobalTheory.UnitaryBC GlobalTheory.DiscSpec GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL
open GroundTheory.Automorphic
open scoped ENNReal

namespace GlobalTheory.CompanionTheory.GrowthHaar

theorem isHaarMeasure_map_restrict (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ)
    (μ : Measure (GA E a)) [μ.IsHaarMeasure] [MeasurableSpace (AutomorphicForm.archGroup E a)]
    [BorelSpace (AutomorphicForm.archGroup E a)] (U : Set (AdelicGLn.FiniteAdelicGL E a))
    (hUc : IsCompact U) (hU1 : U ∈ 𝓝 (1 : AdelicGLn.FiniteAdelicGL E a)) :
    ((μ.restrict ((fun h : GA E a => (AdelicGLn.prodEquiv E a h).2) ⁻¹' U)).map
      (fun h : GA E a => AutomorphicForm.archEquiv E a (AdelicGLn.prodEquiv E a h).1)).IsHaarMeasure := by
  haveI : T2Space (AdelicGLn.FiniteAdelicGL E a) := inferInstance
  haveI : T2Space (AutomorphicForm.archGroup E a) := inferInstance
  haveI : BorelSpace (GA E a) := inferInstance
  set q : GA E a → AdelicGLn.FiniteAdelicGL E a := fun h => (AdelicGLn.prodEquiv E a h).2 with hq_def
  set p : GA E a → AutomorphicForm.archGroup E a :=
    fun h => AutomorphicForm.archEquiv E a (AdelicGLn.prodEquiv E a h).1 with hp_def
  have hΦ : Continuous (AdelicGLn.prodEquiv E a) := (AdelicGLn.prodEquiv E a).continuous
  have hq : Continuous q := continuous_snd.comp hΦ
  have hp : Continuous p := (AutomorphicForm.archEquiv E a).continuous.comp (continuous_fst.comp hΦ)
  have hpm : Measurable p := hp.measurable
  have hS : MeasurableSet (q ⁻¹' U) := (hUc.isClosed.preimage hq).measurableSet
  have happly : ∀ B : Set (AutomorphicForm.archGroup E a), MeasurableSet B →
      ((μ.restrict (q ⁻¹' U)).map p) B = μ (p ⁻¹' B ∩ q ⁻¹' U) := fun B hB => by
    rw [Measure.map_apply hpm hB, Measure.restrict_apply (hpm hB)]
  have h1 : IsFiniteMeasureOnCompacts ((μ.restrict (q ⁻¹' U)).map p) := by
    refine ⟨fun K hK => ?_⟩
    rw [happly K hK.isClosed.measurableSet]
    have hK' : IsCompact ((AutomorphicForm.archEquiv E a).symm '' K) :=
      hK.image (AutomorphicForm.archEquiv E a).symm.continuous
    have hc : IsCompact (p ⁻¹' K ∩ q ⁻¹' U) := by
      have : p ⁻¹' K ∩ q ⁻¹' U = (AdelicGLn.prodEquiv E a).symm ''
          (((AutomorphicForm.archEquiv E a).symm '' K) ×ˢ U) := by
        ext h
        constructor
        · rintro ⟨hk, hu⟩
          exact ⟨AdelicGLn.prodEquiv E a h,
            ⟨⟨_, hk, (AutomorphicForm.archEquiv E a).symm_apply_apply _⟩, hu⟩,
            (AdelicGLn.prodEquiv E a).symm_apply_apply h⟩
        · rintro ⟨⟨x, y⟩, ⟨⟨k, hk, rfl⟩, hy⟩, rfl⟩
          refine ⟨?_, ?_⟩
          · simpa [hp_def] using hk
          · simpa [hq_def] using hy
      rw [this]
      exact (hK'.prod hUc).image (AdelicGLn.prodEquiv E a).symm.continuous
    exact hc.measure_lt_top
  have hpL : ∀ (s : AutomorphicForm.archGroup E a) (h : GA E a),
      p (AutomorphicForm.infEmb E a s * h) = s * p h := fun s h => by
    simp [hp_def, AutomorphicForm.prodEquiv_infEmb]
  have hqL : ∀ (s : AutomorphicForm.archGroup E a) (h : GA E a),
      q (AutomorphicForm.infEmb E a s * h) = q h := fun s h => by
    simp [hq_def, AutomorphicForm.prodEquiv_infEmb]
  have h2 : Measure.IsMulLeftInvariant ((μ.restrict (q ⁻¹' U)).map p) := by
    refine ⟨fun s => ?_⟩
    have hms : Measurable fun x : AutomorphicForm.archGroup E a => s * x :=
      (continuous_const.mul continuous_id).measurable
    ext B hB
    rw [Measure.map_apply hms hB, happly _ (hms hB), happly B hB,
      ← measure_preimage_mul μ (AutomorphicForm.infEmb E a s) (p ⁻¹' B ∩ q ⁻¹' U)]
    congr 1
    ext h
    simp only [Set.mem_inter_iff, Set.mem_preimage, hpL, hqL]
  have h3 : Measure.IsOpenPosMeasure ((μ.restrict (q ⁻¹' U)).map p) := by
    refine ⟨fun O hO ⟨s, hs⟩ => ?_⟩
    rw [happly O hO.measurableSet]
    have hV : IsOpen (p ⁻¹' O ∩ q ⁻¹' interior U) :=
      (hO.preimage hp).inter (isOpen_interior.preimage hq)
    have hne : (p ⁻¹' O ∩ q ⁻¹' interior U).Nonempty := by
      refine ⟨AutomorphicForm.infEmb E a s, ?_, ?_⟩
      · simpa [hp_def, AutomorphicForm.prodEquiv_infEmb] using hs
      · simpa [hq_def, AutomorphicForm.prodEquiv_infEmb] using mem_interior_iff_mem_nhds.2 hU1
    refine fun h0 => hV.measure_ne_zero μ hne (measure_mono_null ?_ h0)
    exact Set.inter_subset_inter_right _ (Set.preimage_mono interior_subset)
  exact { toIsFiniteMeasureOnCompacts := h1, toIsMulLeftInvariant := h2, toIsOpenPosMeasure := h3 }

end GlobalTheory.CompanionTheory.GrowthHaar
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FormalAlgebraisationSchemes
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw PositivityTheory.FormalThickening
open GlobalTheory.ProjSpace GlobalTheory.QCoh.Qcqs GlobalTheory.Cartier
open GlobalTheory.CompanionTheory.FormalAlg

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.CompanionTheory.FormalAlg

theorem exists_compatible {R : Type} [CommRing R] (I : Ideal R) {Y : ∀ e : ℕ, Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))}
    {β : ∀ e, (Y e).left ⟶ (Y (e + 1)).left} {N : ∀ e, LB (Y e).left}
    {v : ∀ e, LB.Iso (N e) ((N (e + 1)).pull (β e))} {D : ℤ}
    (step : ∀ (e : ℕ) (σ : LB.Sec (pw (N e) D)), ∃ σ' : LB.Sec (pw (N (e + 1)) D),
      SecMaps (pullPow (v e) D) σ (secPull σ' (β e)))
    {τ : Type} (a₀ : τ → LB.Sec (pw (N 0) D)) :
    ∃ a : ∀ e, τ → LB.Sec (pw (N e) D), a 0 = a₀ ∧
      ∀ e i, SecMaps (pullPow (v e) D) (a e i) (secPull (a (e + 1) i) (β e)) := by
  choose L hL using step
  exact ⟨fun e i => Nat.rec (motive := fun e => LB.Sec (pw (N e) D)) (a₀ i) (fun e x => L e x) e,
    rfl, fun e i => hL e _⟩

theorem tower_sections : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (I : Ideal R) (Y : ∀ e : ℕ, Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) (β : ∀ e, (Y e).left ⟶ (Y (e + 1)).left), (∀ e, IsPullback (β e) (Y e).hom (Y (e + 1)).hom (thickTrans R I e)) → (∀ e, IsProper (Y e).hom) → ∀ (N : ∀ e, LB (Y e).left) (v : ∀ e, LB.Iso (N e) ((N (e + 1)).pull (β e))), (∀ e, (N e).IsLB ∧ (v e).IsGen) → RelAmple (Y 0) (N 0) → ∃ (n p q : ℕ) (a : ∀ e, Fin (p + 1) → LB.Sec (pw (N e) (n : ℤ))) (c : ∀ e, Fin (q + 1) → LB.Sec (pw (N e) ((n : ℤ) + 1))), 1 ≤ n ∧ VeryAmpleBy (Y 0).hom (pw (N 0) (n : ℤ)) (a 0) ∧ VeryAmpleBy (Y 0).hom (pw (N 0) ((n : ℤ) + 1)) (c 0) ∧ (∀ e i, SecMaps (pullPow (v e) (n : ℤ)) (a e i) (secPull (a (e + 1) i) (β e))) ∧ (∀ e i, SecMaps (pullPow (v e) ((n : ℤ) + 1)) (c e i) (secPull (c (e + 1) i) (β e))) := by
  intro R _ _ I Y β hβ hP N v hN hA
  obtain ⟨d, hd, m₁, s, m₂, s', hs, hs'⟩ := GlobalTheory.T.relatively_ample_consecutive_very_ample (R ⧸ I ^ (0 + 1)) (Y 0) (N 0) (hN 0).1 hA
  obtain ⟨t₁, ht₁⟩ := GlobalTheory.T.formal_line_bundle_very_ample_system R I Y β hβ hP N v hN d hd m₁ s hs
  obtain ⟨t₂, ht₂⟩ := GlobalTheory.T.formal_line_bundle_very_ample_system R I Y β hβ hP N v hN (d + 1) (by omega) m₂ s' hs'
  set k := max t₁ t₂ with hk
  set t := 1 + (d + 1) * k with ht
  set t' := 1 + d * k with ht'
  have hkt : k ≤ t := by nlinarith
  have hkt' : k ≤ t' := by nlinarith
  have h1 : t₁ ≤ t := (le_max_left _ _).trans hkt
  have h2 : t₂ ≤ t' := (le_max_right _ _).trans hkt'
  have e₁ : ((d * t : ℕ) : ℤ) = (d : ℤ) * (t : ℕ) := by push_cast; ring
  have e₂ : ((d * t : ℕ) : ℤ) + 1 = ((d + 1 : ℕ) : ℤ) * (t' : ℕ) := by
    simp only [ht, ht']; push_cast; ring
  have hc₁ : 0 < Fintype.card (Fin t → Fin (m₁ + 1)) := Fintype.card_pos
  have hc₂ : 0 < Fintype.card (Fin t' → Fin (m₂ + 1)) := Fintype.card_pos
  obtain ⟨p, hp⟩ : ∃ p, Fintype.card (Fin t → Fin (m₁ + 1)) = p + 1 := ⟨_, (Nat.succ_pred_eq_of_pos hc₁).symm⟩
  obtain ⟨q, hq⟩ : ∃ q, Fintype.card (Fin t' → Fin (m₂ + 1)) = q + 1 := ⟨_, (Nat.succ_pred_eq_of_pos hc₂).symm⟩
  let E₁ : Fin (p + 1) ≃ (Fin t → Fin (m₁ + 1)) := (Fintype.equivFinOfCardEq hp).symm
  let E₂ : Fin (q + 1) ≃ (Fin t' → Fin (m₂ + 1)) := (Fintype.equivFinOfCardEq hq).symm
  have ht1 : 1 ≤ t := by omega
  have ht1' : 1 ≤ t' := by omega
  have va := GlobalTheory.T.very_ample_tensor_power_sections _ (Y 0).hom (N 0) _ _ t e₁.symm m₁ s (hN 0).1 ht1 hs p E₁
  have vc := GlobalTheory.T.very_ample_tensor_power_sections _ (Y 0).hom (N 0) _ _ t' e₂.symm m₂ s' (hN 0).1 ht1' hs' q E₂
  obtain ⟨a, ha0, ha⟩ := exists_compatible I (v := v) (ht₁ t h1 _ e₁) (fun j => secMono e₁.symm s (E₁ j))
  obtain ⟨c, hc0, hc⟩ := exists_compatible I (v := v) (ht₂ t' h2 _ e₂) (fun j => secMono e₂.symm s' (E₂ j))
  refine ⟨d * t, p, q, a, c, Nat.mul_pos hd ht1, ?_, ?_, ha, hc⟩
  · rw [ha0]; exact va
  · rw [hc0]; exact vc

theorem schemes_of_closedProj : GEClosedProj → GlobalTheory.Published.FormalAlgebraisation.Schemes := by
  intro hGE R _ _ I hI Y β hβ hP N hN hv hA
  choose v hvg using hv
  have hNv : ∀ e, (N e).IsLB ∧ (v e).IsGen := fun e => ⟨hN e, hvg e⟩
  obtain ⟨n, p, q, a, c, hn, ha0, hc0, hca, hcc⟩ := tower_sections R I Y β hβ hP N v hNv hA
  set D : ℤ := (n : ℤ) * ((n + 1 : ℕ) : ℤ) with hD
  have h1 : (n : ℤ) * ((n + 1 : ℕ) : ℤ) = D := rfl
  have h2 : ((n : ℤ) + 1) * ((n : ℕ) : ℤ) = D := by rw [hD]; push_cast; ring
  have hcard : ∀ (k r : ℕ), ∃ m, Fintype.card (Fin k → Fin (r + 1)) = m + 1 := fun k r =>
    ⟨_, (Nat.succ_pred_eq_of_pos (Fintype.card_pos (α := Fin k → Fin (r + 1)))).symm⟩
  obtain ⟨m₁, hm₁⟩ := hcard (n + 1) p
  obtain ⟨m₂, hm₂⟩ := hcard n q
  let E₁ : Fin (m₁ + 1) ≃ (Fin (n + 1) → Fin (p + 1)) := (Fintype.equivFinOfCardEq hm₁).symm
  let E₂ : Fin (m₂ + 1) ≃ (Fin n → Fin (q + 1)) := (Fintype.equivFinOfCardEq hm₂).symm
  let m := m₁ + 1 + m₂
  let E : Fin (m + 1) ≃ Fin (m₁ + 1) ⊕ Fin (m₂ + 1) :=
    (finCongr (by omega)).trans finSumFinEquiv.symm
  let z : ∀ e, Fin (m + 1) → LB.Sec (pw (N e) D) := fun e j =>
    Sum.elim (fun i => secMono h1 (a e) (E₁ i)) (fun i => secMono h2 (c e) (E₂ i)) (E j)
  have hz1 : ∀ e w, z e (E.symm (Sum.inl (E₁.symm w))) = secMono h1 (a e) w := fun e w => by
    simp [z]
  have hz2 : ∀ e w, z e (E.symm (Sum.inr (E₂.symm w))) = secMono h2 (c e) w := fun e w => by
    simp [z]
  have hva : VeryAmpleBy (Y 0).hom (pw (N 0) D) (z 0) := by
    have x1 := GlobalTheory.T.very_ample_tensor_power_sections _ (Y 0).hom (N 0) _ _ (n + 1) h1 p (a 0) (hN 0) (by omega) ha0 m₁ E₁
    have x2 := GlobalTheory.T.very_ample_tensor_power_sections _ (Y 0).hom (N 0) _ _ n h2 q (c 0) (hN 0) hn hc0 m₂ E₂
    exact GlobalTheory.T.very_ample_union_sections _ (Y 0).hom _ (isLB_pw (hN 0) D) m₁ m₂ m _ _ E x1 x2
  have hzc : ∀ e j, SecMaps (pullPow (v e) D) (z e j) (secPull (z (e + 1) j) (β e)) := fun e j => by
    simp only [z]
    rcases E j with i | i
    · exact secMaps_secMono (v e) h1 (a e) (a (e + 1)) (hca e) _
    · exact secMaps_secMono (v e) h2 (c e) (c (e + 1)) (hcc e) _
  obtain ⟨X, Q, ζ, b, ω, hQ, hX, hXa, hb, hbc, hω, hωz, hquad, hcov⟩ :=
    GlobalTheory.T.formal_sections_compatible_system hGE R I hI Y β hβ (fun e => pw (N e) D) (fun e => pullPow (v e) D)
      (fun e => ⟨isLB_pw (hN e) D, pullPow_isGen _ _ (hvg e)⟩) m z hzc hva
  let ia : (Fin (n + 1) → Fin (p + 1)) → Fin (m + 1) := fun w => E.symm (Sum.inl (E₁.symm w))
  let ic : (Fin n → Fin (q + 1)) → Fin (m + 1) := fun w => E.symm (Sum.inr (E₂.symm w))
  have hA' : ⨆ i : Fin (p + 1), nonzeroLocus (ζ (ia fun _ => i)) = ⊤ := by
    have := hcov (Set.range fun i : Fin (p + 1) => ia fun _ => i) (by
      rw [iSup_range, ← ha0.1]
      refine iSup_congr fun i => ?_
      rw [hz1, nonzeroLocus_secMono_const h1 _ _ (by omega)])
    rwa [iSup_range] at this
  have hC' : ⨆ i : Fin (q + 1), nonzeroLocus (ζ (ic fun _ => i)) = ⊤ := by
    have := hcov (Set.range fun i : Fin (q + 1) => ic fun _ => i) (by
      rw [iSup_range, ← hc0.1]
      refine iSup_congr fun i => ?_
      rw [hz2, nonzeroLocus_secMono_const h2 _ _ hn])
    rwa [iSup_range] at this
  obtain ⟨A, ωA, hAL, hωA, hAc⟩ := GlobalTheory.T.line_bundle_root_from_relations X.left Q hQ (n + 1) (by omega) (Fin (p + 1)) (fun w => ζ (ia w))
    (fun w₁ w₂ w₃ w₄ hw c' => hquad _ _ _ _ (fun e c'' => by
      simp only [ia, hz1]; exact secMono_mul h1 (a e) w₁ w₂ w₃ w₄ hw c'') c') hA'
  obtain ⟨C, ωC, hCL, hωC, hCc⟩ := GlobalTheory.T.line_bundle_root_from_relations X.left Q hQ n hn (Fin (q + 1)) (fun w => ζ (ic w))
    (fun w₁ w₂ w₃ w₄ hw c' => hquad _ _ _ _ (fun e c'' => by
      simp only [ic, hz2]; exact secMono_mul h2 (c e) w₁ w₂ w₃ w₄ hw c'') c') hC'
  refine ⟨X, tw C A (-1), b, hX, isLB_tw hCL hAL _,
    GlobalTheory.T.relatively_ample_twist_difference R X Q m ζ hQ hXa A C n hn hAL hCL ⟨ωA, hωA⟩ ⟨ωC, hωC⟩, hb, hbc, fun e => ?_⟩
  refine GlobalTheory.T.pullback_twist_iso_difference (b e) A C (N e) n hAL hCL (hN e) ?_ ?_
  · refine hAc _ (b e) (N e) n D h1 (a e) (ω e) (hN e) (hω e) fun w => ?_
    have := hωz e (ia w)
    simp only [ia, hz1] at this
    exact this
  · refine hCc _ (b e) (N e) ((n : ℤ) + 1) D h2 (c e) (ω e) (hN e) (hω e) fun w => ?_
    have := hωz e (ic w)
    simp only [ic, hz2] at this
    exact this

end GlobalTheory.CompanionTheory.FormalAlg
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HeckeCosetSumCompactStatement
section
open NumberField IsDedekindDomain Matrix Polynomial Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT PositivityTheory.Rg.BcN.F2
open scoped Classical TensorProduct

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hecke_coset_sum_compact : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n a b : ℕ) (h : a + b = n) (w : Pl E) (K' : Subgroup (GLw n w)), IsOpen (K' : Set (GLw n w)) → K' ≤ GlobalTheory.LFun.KGL w n → (∀ k ∈ GlobalTheory.LFun.KGL w n, ∀ k' ∈ K', k * k' * k⁻¹ ∈ K') → ∀ X : Finset (GLw n w), (∀ x ∈ X, x ∈ GlobalTheory.LFun.KGL w n) → (∀ k ∈ GlobalTheory.LFun.KGL w n, ∃! x ∈ X, x⁻¹ * k ∈ K') → ∀ φ : GLw n w → ℂ, (∀ g, ∀ k ∈ K', φ (g * k) = φ g) → HasCompactSupport φ → hint (GlobalTheory.LFun.KGL w n) φ = ((X.card : ℂ))⁻¹ * ∑ y ∈ X, hint ((GlobalTheory.LFun.KGL w a).prod (GlobalTheory.LFun.KGL w b)) fun m => hint (intMat a b w) fun Y => φ (blk h w m (Multiplicative.toAdd Y) * y) := by
  first | exact @GlobalTheory.CompanionTheory.IntDec.integral_decomposition | exact GlobalTheory.CompanionTheory.IntDec.integral_decomposition | (intros; apply GlobalTheory.CompanionTheory.IntDec.integral_decomposition <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HeckeOperatorJacquetEigenRightStatement
section
open Filter Topology MeasureTheory GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult ValuativeRel
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hecke_operator_jacquet_eigen_right : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (N : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V), IsSmooth π → ∀ m : ℕ, 1 ≤ m → ∀ (d : Fin 2 → ℕ) (hd : ∑ a, d a = N), 0 < d 0 → 0 < d 1 → ∀ T : Module.End ℂ (fixed π (Zls.Km k N m)), Zls.IsHeckeOp π m (Zls.diagPow k N (Zls.omegaVec N (d 0))) T → ∀ v : fixed π (Zls.Km k N m), (Submodule.Quotient.mk ((T v : fixed π (Zls.Km k N m)) : V) : Jacquet π (unipRad k (stdBlocks d hd))) = Submodule.Quotient.mk (π (Zls.diagPow k N (Zls.omegaVec N (d 0))) (v : V)) := by
  first | exact @GlobalTheory.CompanionTheory.HeckeJacquet.hecke_omega_jacquet | exact GlobalTheory.CompanionTheory.HeckeJacquet.hecke_omega_jacquet | (intros; apply GlobalTheory.CompanionTheory.HeckeJacquet.hecke_omega_jacquet <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HeightContinuousPosStatement
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl
open GlobalTheory.Doubling (absE)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.height_function_continuous_pos' : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n : ℕ) (Y : Spc F E n) (r s : ℕ), B.IsGood σ → 1 ≤ n → (Y.IsHerm σ B r s ∨ Y.IsSkew σ B r s) → ∀ (b : GL (Fin n ⊕ Fin n) E) (K : Subgroup (G2 σ Y)) (a : G2 σ Y → ℝ), IsFrame2 σ Y b → IsStdK (σ := σ) (Y := Y) B b K → IsHgt K a → Continuous a ∧ ∀ x, 0 < a x := by
  first | exact @GlobalTheory.CompanionTheory.Iwasawa.height_continuous_pos | exact GlobalTheory.CompanionTheory.Iwasawa.height_continuous_pos | (intros; apply GlobalTheory.CompanionTheory.Iwasawa.height_continuous_pos <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.InjectiveUnipotentOfRestrictionStatement
section
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.injective_unipotent_of_restriction : PositivityTheory.RgBcC.RealD.InjRL → PositivityTheory.RgBcC.RealD.InjUU := by
  first | exact @GlobalTheory.CompanionTheory.LvChain.injUU_of_injRL | exact GlobalTheory.CompanionTheory.LvChain.injUU_of_injRL | (intros; apply GlobalTheory.CompanionTheory.LvChain.injUU_of_injRL <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JacquetFixedFirstConditionStatement
section
open GlobalTheory.PRep GlobalTheory.SmGL ValuativeRel PositivityTheory.Lbc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.jacquet_fixed_first_condition : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], PositivityTheory.Lbc.C1 k := by
  first | exact @GlobalTheory.CompanionTheory.Lbc.hecke_dominant_mul | exact GlobalTheory.CompanionTheory.Lbc.hecke_dominant_mul | (intros; apply GlobalTheory.CompanionTheory.Lbc.hecke_dominant_mul <;> assumption)
end

