import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0143
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FixedCoefficientFieldInComplex
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0142
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsWildInertiaCyclotomicElement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0144
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InertialOrderFifteenCharAuxiliaryPrimeSpec
import ReciprocityTheory.GaloisValuations.Global
import Formalism.LocalToGlobal.NormalizedHeckeFactors.RingHomOfBaseOrderToFraction
import Formalism.SharpRestriction.LevelLetterCocycles.DataN
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0084
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0135
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0145
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0097
import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.SymplecticTensorMeasures
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0031

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AbsNormModEqOneOfPrincipalRayClassStatement
section
open NumberField IsDedekindDomain Formalism.L2.Host GlobalTheory.NT GlobalTheory.Published GlobalTheory.Mem GlobalTheory.Mem.Fld
open scoped nonZeroDivisors IntermediateField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.absNorm_modEq_one_of_principal_rayClass : ∀ (K : Type) [Field K] [NumberField K] [IsTotallyComplex K] (𝔮 : Ideal (𝓞 K)) (p : ℕ), 𝔮 ≤ Ideal.span {(p : 𝓞 K)} → ∀ (I : Ideal (𝓞 K)) (α β : 𝓞 K), RayPair 𝔮 α β → I * Ideal.span {β} = Ideal.span {α} → Ideal.absNorm I ≡ 1 [MOD p] := by
  first | exact @GlobalTheory.Mem.RayNorm.absNorm_modEq_one | exact GlobalTheory.Mem.RayNorm.absNorm_modEq_one | (intros; apply GlobalTheory.Mem.RayNorm.absNorm_modEq_one <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AlgWtExistsInvFormStatement
section
open NumberField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.algWt_exists_invForm' : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (a : Formalism.L2.NG.AlgWt L n), ∃ β : a.W →ₗ⋆[ℂ] a.W →ₗ[ℂ] ℂ, GlobalTheory.CoefDuty.IsInvForm a β := by
  first | exact @GlobalTheory.algWt_exists_invForm | exact GlobalTheory.algWt_exists_invForm | (intros; apply GlobalTheory.algWt_exists_invForm <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AlgebraicHeckeCharacterValueMemKummerFieldStatement
section
open NumberField IsDedekindDomain Formalism.L2.Host GlobalTheory.NT GlobalTheory.Published GlobalTheory.Mem GlobalTheory.Mem.Fld
open scoped nonZeroDivisors IntermediateField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.algebraicHeckeCharacter_value_mem_kummerField : ∀ (L : Type) [Field L] [NumberField L] [IsGalois ℚ L] [IsTotallyComplex L] (φ₀ : L →+* ℂ) (I : Type) [Fintype I] (φ : I → L →+* ℂ), (Function.Bijective fun i => InfinitePlace.mk (φ i)) → ∀ (χ : HChar L) (n : I → ℤ) (r : ℤ), χ.HasInf φ n → (∀ i, Even (n i - r)) → ∀ (v : HeightOneSpectrum (𝓞 L)) (h : ℕ) (k : Lˣ), FractionalIdeal.spanSingleton (𝓞 L)⁰ (k : L) = (v.asIdeal : FractionalIdeal (𝓞 L)⁰ L) ^ h → χ.inf k * χ.val v ^ h = 1 → χ.valTw ((r : ℝ) / 2) v ∈ kummerField φ₀ h := by
  first | exact @GlobalTheory.Mem.FieldsEx.valTw_mem_kummerField | exact GlobalTheory.Mem.FieldsEx.valTw_mem_kummerField | (intros; apply GlobalTheory.Mem.FieldsEx.valTw_mem_kummerField <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CardPadicAlgClPadicComplexEqComplexStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.L2.NT Formalism.L2.TwC GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial GlobalTheory.GalChar Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR GlobalTheory.HeckeGal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.card_padicAlgCl_padicComplex_eq_complex : ∀ (l : ℕ) [Fact l.Prime], Cardinal.mk (PadicAlgCl l) = Cardinal.mk ℂ ∧ Cardinal.mk ℂ_[l] = Cardinal.mk ℂ := by
  first | exact @GlobalTheory.PadicCard.card_padicAlgCl_padicComplex | exact GlobalTheory.PadicCard.card_padicAlgCl_padicComplex | (intros; apply GlobalTheory.PadicCard.card_padicAlgCl_padicComplex <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CharacterTameQuotientJointPowersTameGeneratorStatement
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.character_tameQuotient_jointPowers_tameGenerator : ∀ {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (γ : G E Ω), TameGenAt A γ → ∀ {O : Type} [CommRing O] [IsLocalRing O] [IsNoetherianRing O] [TopologicalSpace O] [IsTopologicalRing O], IsAdic (IsLocalRing.maximalIdeal O) → ∀ (χ : G E Ω →* Oˣ), Continuous (fun g => ((χ g : Oˣ) : O)) → ∀ (m : ℕ), 0 < m → ¬ A.valuation (m : Ω) < 1 → (∀ σ ∈ Ine (F := E) A, χ σ ^ m = 1) → ∀ (e : E) (π : Ω), π ≠ 0 → π ^ m = algebraMap E Ω e → ∀ σ ∈ Ine (F := E) A, ∃ n : ℕ, χ σ = χ γ ^ n ∧ σ π / π = (γ π / π) ^ n := by
  first | exact @GlobalTheory.TameTau.joint_pow_of_tameGen | exact GlobalTheory.TameTau.joint_pow_of_tameGen | (intros; apply GlobalTheory.TameTau.joint_pow_of_tameGen <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ClassNumberDvdFinrankStatement
section
open NumberField IsDedekindDomain Formalism.L2.Host GlobalTheory.NT GlobalTheory.Published GlobalTheory.Mem GlobalTheory.Mem.Fld
open scoped nonZeroDivisors IntermediateField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.classNumber_dvd_finrank_alt : ∀ (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] (𝔮 : Ideal (𝓞 K)), 𝔮 ≠ ⊥ → IsRayField K L 𝔮 → classNumber K ∣ Module.finrank K L := by
  first | exact @GlobalTheory.Mem.ClassDvd.classNumber_dvd_finrank | exact GlobalTheory.Mem.ClassDvd.classNumber_dvd_finrank | (intros; apply GlobalTheory.Mem.ClassDvd.classNumber_dvd_finrank <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ClosureFrobeniusElementsEqTopStatement
section
open NumberField IsDedekindDomain Formalism.L2.Host GlobalTheory.NT GlobalTheory.Published GlobalTheory.Mem GlobalTheory.Mem.Fld
open scoped nonZeroDivisors IntermediateField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.closure_frobeniusElements_eq_top : ∀ (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L] (S : Set (HeightOneSpectrum (𝓞 K))), S.Finite → (∀ (F : Type) [Field F] [NumberField F] [Algebra K F], (∀ v : HeightOneSpectrum (𝓞 K), v ∉ S → IsFrob F v 1) → ∀ σ : F ≃ₐ[K] F, σ = 1) → Subgroup.closure {σ : L ≃ₐ[K] L | ∃ v : HeightOneSpectrum (𝓞 K), v ∉ S ∧ IsFrob L v σ} = ⊤ := by
  first | exact @GlobalTheory.Mem.FieldsEx.closure_frob_eq_top | exact GlobalTheory.Mem.FieldsEx.closure_frob_eq_top | (intros; apply GlobalTheory.Mem.FieldsEx.closure_frob_eq_top <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ColumnMinorProductsFockReproducingIdentityStatement
section
open MvPolynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.columnMinorProducts_fock_reproducing_identity : ∀ (N : ℕ) (Y : YoungDiagram) (hY : Y.colLen 0 ≤ N) (h : MvPolynomial (Fin N × Fin N) ℚ),
    h ∈ Formalism.GradedWeylDivisibility.dualWeyl ℚ N N (fun r => Y.rowLen r) →
    ∑ J : GlobalTheory.WeylLatDualProof.IncreasingRowChoicePerColumn N Y, Formalism.GradedWeylDivisibility.fockQ h (GlobalTheory.WeylMinorDual.colProd ℚ N Y hY J) • GlobalTheory.WeylMinorDual.colProd ℚ N Y hY J
      = Formalism.GradedWeylDivisibility.fockQ (Formalism.GradedWeylDivisibility.hw ℚ le_rfl (fun r : Fin N => Y.rowLen r)) (Formalism.GradedWeylDivisibility.hw ℚ le_rfl (fun r : Fin N => Y.rowLen r)) • h := by
  first | exact @GlobalTheory.WeylReproducing.reproducing | exact GlobalTheory.WeylReproducing.reproducing | (intros; apply GlobalTheory.WeylReproducing.reproducing <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CombMemIffStatement
section
open MvPolynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.comb_mem_iff_alt : ∀ (p : ℕ) [Fact p.Prime] (Lt T : Type) [Fintype Lt] [DecidableEq Lt] [Fintype T] (e : Lt → T), Function.Bijective e →
    ∀ (N : ℕ) (ν : T → Fin N → ℕ) (ι : Lt → Type) [∀ s, Fintype (ι s)] [∀ s, DecidableEq (ι s)]
    (b g : ∀ s, ι s → MvPolynomial (Fin N × Fin N) ℚ) (Nc : Lt → ℚ), (∀ s, Nc s ≠ 0) →
    (∀ s i k, Formalism.GradedWeylDivisibility.fockQ (b s i) (g s k) = if i = k then Nc s else 0) →
    (∀ s, Submodule.span ℤ (Set.range (g s)) =
      (Formalism.GradedWeylDivisibility.weyl ℤ N N le_rfl (ν (e s))).map (Formalism.GradedWeylDivisibility.intQ N N)) →
    ∀ a : (∀ s, ι s) → ℂ_[p],
      ((fun y : T → Matrix (Fin N) (Fin N) ℂ_[p] => ∑ κ : (∀ s, ι s), a κ *
          ∏ s, MvPolynomial.eval (fun k : Fin N × Fin N => y (e s) k.1 k.2)
            (MvPolynomial.map (algebraMap ℚ ℂ_[p]) (g s (κ s)))) ∈ WeylLatticeDuality.DelW p T N ν ↔
        ∀ κ, ‖a κ‖ ≤ 1) := by
  first | exact @GlobalTheory.WeylCombInt.comb_mem_iff | exact GlobalTheory.WeylCombInt.comb_mem_iff | (intros; apply GlobalTheory.WeylCombInt.comb_mem_iff <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CompletionNormalOfUnramified
section
open IsLocalRing GlobalTheory.Toroidal TensorProduct

namespace GlobalTheory.EtaleCompletionCharZero

theorem completion_isDomain_and_isIntegrallyClosed :
    ∀ (D T : Type) [CommRing D] [IsDomain D] [IsLocalRing D] [IsIntegrallyClosed D] [CharZero D]
      [Algebra.EssFiniteType ℤ D] [CommRing T] [IsLocalRing T] (h : D →+* T),
      IsNoetherianRing T → IsLocalHom h → h.Flat → (maximalIdeal D).map h = maximalIdeal T →
      ((residue T).comp h).Finite → ((residue T).comp h).FormallyUnramified →
      IsDomain (AdicCompletion (maximalIdeal T) T) ∧
        IsIntegrallyClosed (AdicCompletion (maximalIdeal T) T) := by
  intro D T _ _ _ _ _ _ _ _ h hT hloc hflat hm hfin hfu
  let R' := AdicCompletion (maximalIdeal T) T
  let ι : T →+* R' := algebraMap T R'
  have hι : IsLocalHom ι := inferInstance
  have hres : Function.Surjective (ResidueField.map ι) :=
    (AdicCompletion.residueField_map_bijective T).right
  have hcomp : (residue R').comp (ι.comp h) = (ResidueField.map ι).comp ((residue T).comp h) := by
    ext b
    simp
  have hD : IsNoetherianRing D := Algebra.EssFiniteType.isNoetherianRing ℤ D
  obtain ⟨h1, h2⟩ := GlobalTheory.AnalyticNormality.completion_isDomain_and_isIntegrallyClosed D
  refine GlobalTheory.EtaleCompletionNormal.isDomain_and_isIntegrallyClosed D R' (ι.comp h) hD h1 h2
    (GlobalTheory.AdicNoeth.isNoetherianRing_adicCompletion T (maximalIdeal T)) inferInstance
    inferInstance ⟨?_, ?_, ?_⟩ ?_
  · exact RingHom.Flat.comp hflat (RingHom.flat_algebraMap_iff.mpr inferInstance)
  · rw [← Ideal.map_map, hm, AdicCompletion.maximalIdeal_eq_map]
  · rw [hcomp]
    exact RingHom.Finite.comp (RingHom.Finite.of_surjective _ hres) hfin
  · rw [hcomp]
    exact hfu.comp (RingHom.FormallyUnramified.of_surjective hres)

end GlobalTheory.EtaleCompletionCharZero
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CompletionUnramifiedNormalStatement
section
open IsLocalRing
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.completion_unramified_normal : ∀ (D E : Type) [CommRing D] [IsDomain D] [IsLocalRing D] [CommRing E] [IsLocalRing E] (h : D →+* E), IsNoetherianRing D → IsDomain (AdicCompletion (IsLocalRing.maximalIdeal D) D) → IsIntegrallyClosed (AdicCompletion (IsLocalRing.maximalIdeal D) D) → IsNoetherianRing E → IsAdicComplete (IsLocalRing.maximalIdeal E) E → IsLocalHom h → GlobalTheory.Toroidal.IsEtaleCompletion h → ((IsLocalRing.residue E).comp h).FormallyUnramified → IsDomain E ∧ IsIntegrallyClosed E := by
  first | exact @GlobalTheory.EtaleCompletionNormal.isDomain_and_isIntegrallyClosed | exact GlobalTheory.EtaleCompletionNormal.isDomain_and_isIntegrallyClosed | (intros; apply GlobalTheory.EtaleCompletionNormal.isDomain_and_isIntegrallyClosed <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousConjA
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta NumberField Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.SymplecticTensorMeasures (cE cE_cE cA_inc cA_cA ConjIsom conj_map_mem_unitaryGroup)
open GlobalTheory.LocWCompare
open scoped TensorProduct

namespace GlobalTheory.ConjAutProps

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {V : HSp D}

theorem continuous_conjA (D : D7) : Continuous (cA D) := by
  have : IsModuleTopology (AF D.host.F) (AE D) := ⟨rfl⟩
  have : IsTopologicalRing (AE D) := IsModuleTopology.isTopologicalRing (AF D.host.F) (AE D)
  have := IsModuleTopology.continuous_of_linearMap
    (Algebra.TensorProduct.map (AlgHom.id (AF D.host.F) (AF D.host.F)) D.sp.cm.sig).toLinearMap
  exact this

theorem continuous_aut (s : ConjIsom V) : Continuous s.aut := by
  have : IsModuleTopology (AF D.host.F) (AE D) := ⟨rfl⟩
  have : IsTopologicalRing (AE D) := IsModuleTopology.isTopologicalRing (AF D.host.F) (AE D)
  have hm : Continuous (matHom V) := continuous_subtype_val
  have hmap : Continuous fun x : Matrix (Fin V.rank) (Fin V.rank) (AE D) => x.map (cA D) :=
    continuous_id.matrix_map (continuous_conjA D)
  have hc : Continuous (cG D V.rank) :=
    Units.continuous_iff.2 ⟨hmap.comp Units.continuous_val, hmap.comp Units.continuous_coe_inv⟩
  have h : Continuous fun g : GA D V => s.PA * cG D _ (matHom V g) * s.PA⁻¹ :=
    (continuous_const.mul (hc.comp hm)).mul continuous_const
  exact h.subtype_mk fun g => (s.aut g).2

theorem aut_mem_GfC (s : ConjIsom V) {k : GA D V} (hk : k ∈ GfC V) : s.aut k ∈ GfC V := by
  have hk' : Formalism.UG.bc (infPart D) (matHom V k) = 1 := hk
  have h2 : Formalism.UG.bc (infPart D) (cG D _ (matHom V k)) = 1 := by
    apply Units.ext
    have h3 : (mt V k).map (infPart D) = 1 := congrArg Units.val hk'
    have h4 : ((mt V k).map (cA D)).map (infPart D) =
        ((mt V k).map (infPart D)).map (sigR (Ainf D.host.F) D.sp.cm.sig) := by
      funext i j; exact infPart_cA _
    change ((mt V k).map (cA D)).map (infPart D) = 1
    rw [h4, h3, Matrix.map_one _ (map_zero _) (map_one _)]
  change Formalism.UG.bc (infPart D) (matHom V (s.aut k)) = 1
  rw [matHom_aut, map_mul, map_mul, h2, map_inv, mul_one, mul_inv_cancel]

theorem aut_mem_GQ (s : ConjIsom V) {k : GA D V} (hk : k ∈ GQ V) : s.aut k ∈ GQ V := by
  obtain ⟨γ, hγ, e⟩ : ∃ γ ∈ Formalism.UG.UJ (cE D) V.gram, Formalism.UG.bc (incA D) γ = matHom V k := hk
  refine ⟨_, conj_map_mem_unitaryGroup (cE D) V.gram s.P γ s.iso hγ, ?_⟩
  change Formalism.UG.bc (incA D) (s.P * Matrix.GeneralLinearGroup.map (cE D) γ * s.P⁻¹) = matHom V (s.aut k)
  have h1 : Formalism.UG.bc (incA D) s.P = s.PA := Units.ext rfl
  have h2 : Formalism.UG.bc (incA D) (Matrix.GeneralLinearGroup.map (cE D) γ) = cG D _ (Formalism.UG.bc (incA D) γ) := by
    ext i j; exact (cA_inc _).symm
  rw [matHom_aut, map_mul, map_mul, map_inv, h1, h2, e]

theorem inv_aut_aut (s : ConjIsom V) (g : GA D V) : (invIsom s).aut (s.aut g) = g :=
  (autEquiv s).left_inv g

theorem aut_inv_aut (s : ConjIsom V) (g : GA D V) : s.aut ((invIsom s).aut g) = g :=
  (autEquiv s).right_inv g

theorem det_aut (s : ConjIsom V) (g : GA D V) : (mt V (s.aut g)).det = cA D (mt V g).det := by
  have h1 : s.PA.val.det * (s.PA⁻¹).val.det = 1 := by
    rw [← det_mul, s.PA.mul_inv, det_one]
  have h2 : (cM (mt V g)).det = cA D (mt V g).det := ((cA D).map_det _).symm
  rw [s.mt_aut, det_mul, det_mul, h2, mul_right_comm, h1, one_mul]

theorem autProps : ∀ D : D7, GlobalTheory.IndefiniteRowSideFullHecke.SymplecticTensorMeasures.AutProps D := by
  intro D V s
  refine ⟨isHomeomorph_iff_exists_inverse.2 ⟨continuous_aut s, (invIsom s).aut, inv_aut_aut s, aut_inv_aut s,
    continuous_aut _⟩, fun g => ⟨⟨fun h => ?_, aut_mem_GQ s⟩, ⟨fun h => ?_, aut_mem_GfC s⟩,
    ⟨fun h => ?_, aut_mem_GinfC s⟩, det_aut s g⟩⟩
  · exact inv_aut_aut s g ▸ aut_mem_GQ (invIsom s) h
  · exact inv_aut_aut s g ▸ aut_mem_GfC (invIsom s) h
  · exact inv_aut_aut s g ▸ aut_mem_GinfC (invIsom s) h

end GlobalTheory.ConjAutProps

end
end

