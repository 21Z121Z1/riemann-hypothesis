import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1038
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1387
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1397
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1810
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1832
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1503
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1820
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1116
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Development.AbelianVarietyTheory.Definitions.Foundations.GLintEqKOAndPrincEqKOne
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsDualFamilyOfIsLattice
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorLatticeInertPlaceSelfDual
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1781
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1809
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1802
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1801
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSplittingSplitOm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1127
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1126
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1833
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsBinaryEqAdicCompletion
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0058
import Formalism.LocalToGlobal.ProjectiveLattices.HalfOneAddSqrtNegIsIntegral
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0004
import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.Bundle0006
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0088

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocalDictionaryInertPlace
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.KFinLoc
open scoped TensorProduct Matrix

noncomputable section

namespace GlobalTheory.InertLocDict

open GlobalTheory.InertBigCell

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {v : Pl F} {w : HeightOneSpectrum (𝓞 E)}

theorem isConjAt_conjW (σ : E →ₐ[F] E) (hw : Formalism.UG.IsInertAt F E v w) :
    IsConjAt σ (under_eq_of_isInertAt hw) (conjW σ hw) := fun y => by
  show toCompl _ (sigR (Fv F v) σ ((InertChart.complEquiv hw (under_eq_of_isInertAt hw)).symm (toCompl _ y))) = _
  congr 2
  exact (InertChart.complEquiv hw (under_eq_of_isInertAt hw)).symm_apply_apply y

theorem conjW_conjW (σ : E →ₐ[F] E) (hσ : ∀ x, σ (σ x) = x) (hw : Formalism.UG.IsInertAt F E v w)
    (x : w.adicCompletion E) : conjW σ hw (conjW σ hw x) = x := by
  obtain ⟨y, rfl⟩ := InertChart.toCompl_surjective (under_eq_of_isInertAt hw) x
  rw [isConjAt_conjW σ hw, isConjAt_conjW σ hw]
  congr 1
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul a e =>
    simp only [sigR, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Algebra.TensorProduct.map_tmul, AlgHom.id_apply, hσ]
  | add x y hx hy => rw [map_add, map_add, hx, hy]

theorem iotaW_mulVec (hw : Formalism.UG.IsInertAt F E v w) {l m : Type} [Fintype m]
    (M : Matrix l m (w.adicCompletion E)) (y : m → w.adicCompletion E) :
    (fun i => iotaW hw ((M *ᵥ y) i)) = M.map (iotaW hw) *ᵥ fun i => iotaW hw (y i) := by
  funext i
  simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, map_sum, iotaW_mul]

theorem map_iotaW_mul (hw : Formalism.UG.IsInertAt F E v w) {l m p : Type} [Fintype m]
    (M : Matrix l m (w.adicCompletion E)) (N : Matrix m p (w.adicCompletion E)) :
    M.map (iotaW hw) * N.map (iotaW hw) = (M * N).map (iotaW hw) := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.map_apply, map_sum, iotaW_mul]

theorem one_map_iotaW (hw : Formalism.UG.IsInertAt F E v w) (n : ℕ) :
    (1 : Matrix (Fin n) (Fin n) (w.adicCompletion E)).map (iotaW hw) =
      iotaW hw 1 • (1 : Matrix (Fin n) (Fin n) (AE F E)) := by
  ext i j
  simp only [Matrix.map_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
  split_ifs <;> simp

theorem herm_gram {R : Type} [CommRing R] (τ : R →+* R) (hτ : ∀ x, τ (τ x) = x) {n : ℕ}
    (A M : Matrix (Fin n) (Fin n) R) (hM : ∀ i j, τ (M i j) = M j i) (i j : Fin n) :
    τ ((Formalism.UG.cT τ A * M * A) i j) = (Formalism.UG.cT τ A * M * A) j i := by
  simp only [Formalism.UG.cT, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, map_sum, map_mul, hτ, hM,
    Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
  ring

theorem isUnit_of_val_eq_one {t : Formalism.UG.Ov E w} (ht : Valued.v (t : w.adicCompletion E) = 1) : IsUnit t := by
  have h0 : (t : w.adicCompletion E) ≠ 0 := fun h0 => by rw [h0, map_zero] at ht; exact zero_ne_one ht
  have hm : (t : w.adicCompletion E)⁻¹ ∈ Formalism.UG.Ov E w := by
    show _ ∈ w.adicCompletionIntegers E
    rw [HeightOneSpectrum.mem_adicCompletionIntegers, map_inv₀, ht, inv_one]
  exact isUnit_iff_exists_inv.2 ⟨⟨_, hm⟩, Subtype.ext (mul_inv_cancel₀ h0)⟩

end GlobalTheory.InertLocDict

namespace GlobalTheory.InertLocDict

open GlobalTheory.InertBigCell

theorem exists_local_dictionary : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (n r s : ℕ) (X : Spc F E n), B.IsGood σ → X.IsHerm σ B r s →
    ∀ (v : Pl F) (w : HeightOneSpectrum (𝓞 E)), Formalism.UG.IsInertAt F E v w →
    ∃ (O : Type) (_ : CommRing O) (c : O →+* O) (ι : O →ₙ+* AE F E) (P Q : Matrix (Fin n) (Fin n) (AE F E))
      (JL : Matrix (Fin n) (Fin n) O),
      IsLocalRing O ∧ (∀ x, c (c x) = x) ∧ IsUnit (2 : O) ∧ (∃ x : O, IsUnit (c x - x)) ∧
      Function.Injective ι ∧ At (evFin F v) (ι 1) ∧ (∀ y : AE F E, At (evFin F v) y → ι 1 * y = y) ∧
      (∀ x, cA σ (ι x) = ι (c x)) ∧
      P * Q = ι 1 • (1 : Matrix (Fin n) (Fin n) (AE F E)) ∧ Q * P = ι 1 • (1 : Matrix (Fin n) (Fin n) (AE F E)) ∧
      ι 1 • P = P ∧ ι 1 • Q = Q ∧
      (∀ i j, c (JL j i) = JL i j) ∧ IsUnit JL.det ∧ Pᵀ * incM F X.J * P.map (cA σ) = JL.map ι ∧
      ∀ z : Fin n → AE F E, z ∈ GlobalTheory.InertSph.latAt X v ↔ ∃ a : Fin n → O, z = P *ᵥ fun i => ι (a i) := by
  intro F E _ _ _ _ _ σ B n r s X hB hX v w hw
  have h := under_eq_of_isInertAt hw
  have hc : IsConjAt σ h (conjW σ hw) := isConjAt_conjW σ hw
  have hσ : ∀ x, σ (σ x) = x := InertChart.conj_conj hB.cm
  haveI : IsLocalRing (Formalism.UG.Ov E w) := inferInstanceAs (IsLocalRing (w.adicCompletionIntegers E))
  let c : Formalism.UG.Ov E w →+* Formalism.UG.Ov E w :=
    ((conjW σ hw).comp (Formalism.UG.Ov E w).subtype).codRestrict (Formalism.UG.Ov E w)
      (fun x => InertChart.conj_mem hw hc x.2)
  let ι : Formalism.UG.Ov E w →ₙ+* AE F E :=
    { toFun := fun x => iotaW hw (x : w.adicCompletion E)
      map_mul' := fun x y => iotaW_mul hw _ _
      map_zero' := map_zero _
      map_add' := fun x y => map_add _ _ _ }
  have hι : ∀ x, ι x = iotaW hw (x : w.adicCompletion E) := fun _ => rfl
  have hι1 : ι 1 = iotaW hw 1 := rfl
  have hcv : ∀ x, ((c x : Formalism.UG.Ov E w) : w.adicCompletion E) = conjW σ hw x := fun _ => rfl
  obtain ⟨a, ha⟩ := InertChart.exists_isFrameAt (L := X.L) hw hX.lat.fg hX.lat.span_eq_top
  have hJ : (X.Jᵀ).det ≠ 0 := by
    rw [Matrix.det_transpose]; exact GlobalTheory.HermSelfDualLoc.det_ne_zero_of_isHerm σ B hX
  obtain ⟨Bm, ⟨k, hk⟩, eB⟩ := InertChart.exists_gram hw hc hJ
    (GlobalTheory.HermSelfDualLoc.isSelfDualAt_transpose F E σ B n X r s hB hX v) ha
  have hkij : ∀ i j, ((k.1 i j : Formalism.UG.Ov E w) : w.adicCompletion E) = Bm.1 i j := fun i j => by
    rw [← hk]; rfl
  have hBt : Bm.1ᵀ = a.1ᵀ * X.J.map (algebraMap E (w.adicCompletion E)) * a.1.map (conjW σ hw) := by
    rw [eB, Matrix.transpose_mul, Matrix.transpose_mul, Formalism.UG.cT, Matrix.transpose_transpose, Matrix.transpose_map,
      Matrix.transpose_transpose, Matrix.mul_assoc]
  refine ⟨Formalism.UG.Ov E w, inferInstance, c, ι, a.1.map (iotaW hw), (a⁻¹).1.map (iotaW hw), k.1ᵀ, inferInstance,
    fun x => Subtype.ext (conjW_conjW σ hσ hw x), ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  ·
    have h2 : (2 : w.adicCompletion E) ≠ 0 := by
      rw [← map_ofNat (algebraMap E (w.adicCompletion E)) 2]
      exact (map_ne_zero _).2 two_ne_zero
    have hm : (2 : w.adicCompletion E)⁻¹ ∈ Formalism.UG.Ov E w := by
      have := complMap_mem h (GlobalTheory.InertLocField.half_mem v (hB.inert v w hw).1)
      rwa [complMap_algebraMap, map_inv₀, map_inv₀, map_ofNat, map_ofNat] at this
    exact isUnit_iff_exists_inv.2 ⟨⟨_, hm⟩, Subtype.ext (mul_inv_cancel₀ h2)⟩
  ·
    obtain ⟨x, hx⟩ := InertChart.exists_conj_sub_unit hB.cm hw
    have hval : ∀ a : E, Valued.v (algebraMap E (w.adicCompletion E) a) = w.valuation E a := fun a =>
      HeightOneSpectrum.valuedAdicCompletion_eq_valuation' w _
    have hxm : algebraMap E (w.adicCompletion E) (x : E) ∈ Formalism.UG.Ov E w := by
      show _ ∈ w.adicCompletionIntegers E
      rw [HeightOneSpectrum.mem_adicCompletionIntegers, hval]; exact w.valuation_le_one x
    refine ⟨⟨_, hxm⟩, ?_⟩
    refine isUnit_of_val_eq_one ?_
    show Valued.v (conjW σ hw (algebraMap E _ (x : E)) - algebraMap E _ (x : E)) = 1
    rw [InertChart.conj_algebraMap hc, ← map_sub, hval, hx]
  · exact fun x y hxy => Subtype.ext (iotaW_injective hw hxy)
  · rw [hι1, iotaW_apply]; exact GlobalTheory.InertLocField.at_liftT v _
  · intro y hy
    have h1 := hy _ (GlobalTheory.InertLocField.evFin_one_sub v)
    rw [sub_smul, one_smul, sub_eq_zero] at h1
    rw [hι1, iotaW_one, ← Algebra.smul_def]
    exact h1.symm
  · intro x
    rw [hι, hι, hcv, iotaW_conjW]
  · rw [map_iotaW_mul, Units.mul_inv, one_map_iotaW, hι1]
  · rw [map_iotaW_mul, Units.inv_mul, one_map_iotaW, hι1]
  · ext i j
    simp only [Matrix.smul_apply, Matrix.map_apply, smul_eq_mul, hι1, ← iotaW_mul, one_mul]
  · ext i j
    simp only [Matrix.smul_apply, Matrix.map_apply, smul_eq_mul, hι1, ← iotaW_mul, one_mul]
  · intro i j
    apply Subtype.ext
    rw [hcv, Matrix.transpose_apply, Matrix.transpose_apply, hkij, hkij, eB]
    refine herm_gram (conjW σ hw) (conjW_conjW σ hσ hw) a.1 (X.Jᵀ.map (algebraMap E (w.adicCompletion E)))
      (fun p q => ?_) i j
    simp only [Matrix.map_apply, Matrix.transpose_apply, InertChart.conj_algebraMap hc, hX.herm]
  · rw [Matrix.det_transpose]
    exact (Matrix.isUnit_iff_isUnit_det _).1 k.isUnit
  · have e1 : (a.1.map (iotaW hw))ᵀ = (1 - algebraMap (AF F) (AE F E) (GlobalTheory.LatVac.liftV v 1)) • (0 : Matrix (Fin n) (Fin n) (AE F E)) +
        a.1ᵀ.map (iotaW hw) := by
      rw [smul_zero, zero_add, Matrix.transpose_map]
    have e2 : (a.1.map (iotaW hw)).map (cA σ) = (1 - algebraMap (AF F) (AE F E) (GlobalTheory.LatVac.liftV v 1)) • (0 : Matrix (Fin n) (Fin n) (AE F E)) +
        (a.1.map (conjW σ hw)).map (iotaW hw) := by
      rw [smul_zero, zero_add]
      ext i j
      simp only [Matrix.map_apply, iotaW_conjW]
    rw [e1, e2, incM_split hw X.J,
      idem_split_mul _ (iotaW hw) (one_sub_idem v) (one_sub_mul_iotaW hw) (iotaW_mul hw),
      idem_split_mul _ (iotaW hw) (one_sub_idem v) (one_sub_mul_iotaW hw) (iotaW_mul hw),
      Matrix.zero_mul, Matrix.zero_mul, smul_zero, zero_add, ← hBt]
    ext i j
    simp only [Matrix.map_apply, Matrix.transpose_apply, hι, hkij]
  · intro z
    rw [GlobalTheory.InertSphLat.mem_latAt_iff hw X z]
    constructor
    · rintro ⟨u, hu, rfl⟩
      have e : a.1 *ᵥ ((a⁻¹).1 *ᵥ u) = u := by
        rw [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]
      have hint := (ha ((a⁻¹).1 *ᵥ u)).2 (by rw [e]; exact hu)
      refine ⟨fun i => ⟨_, hint i⟩, ?_⟩
      show (fun i => iotaW hw (u i)) = a.1.map (iotaW hw) *ᵥ fun i => iotaW hw (((a⁻¹).1 *ᵥ u) i)
      rw [← iotaW_mulVec, e]
    · rintro ⟨b, rfl⟩
      refine ⟨a.1 *ᵥ fun i => (b i : w.adicCompletion E), (ha _).1 fun i => (b i).2, ?_⟩
      rw [iotaW_mulVec]
      rfl

end GlobalTheory.InertLocDict
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocalGeneratorOfNonzeroIdealStatement
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.KSplit
open scoped Matrix TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_local_generator_of_nonzero_ideal : ∀ (F : Type) [Field F] [NumberField F] (I : Ideal (𝓞 F)) (v : IsDedekindDomain.HeightOneSpectrum (𝓞 F)), I ≠ ⊥ → ∃ z : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v, z ≠ 0 ∧ (¬ I ≤ v.asIdeal → z = 1) ∧ (∀ d ∈ I, Valued.v (algebraMap F (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) (d : F)) ≤ Valued.v z) ∧ ∃ d ∈ I, Valued.v (algebraMap F (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) (d : F)) = Valued.v z := by
  first | exact @GlobalTheory.ideal_localGenerator | exact GlobalTheory.ideal_localGenerator | (intros; apply GlobalTheory.ideal_localGenerator <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocalSchroedingerFamilyAtPlace
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.KFinLoc
open scoped TensorProduct Matrix
open scoped GlobalTheory.VacAny

noncomputable section
namespace GlobalTheory.SchrLocModel

theorem box_mem : ∀ (F : Type) [Field F] [NumberField F] (v : Pl F) (ψ : AddChar (Fv F v) ℂ), (∀ x : Fv F v, (∀ y ∈ v.adicCompletionIntegers F, ψ (x * y) = 1) ↔ x ∈ v.adicCompletionIntegers F) → ∀ (κ : Type) [Fintype κ] (s : (κ → Fv F v) → ℂ), s ∈ SB (κ → Fv F v) → s ≠ 0 → ∃ (x₀ : κ → Fv F v) (N₀ : ℕ), ∀ N ≥ N₀, Set.indicator {x : κ → Fv F v | ∀ i, Valued.v (x i - x₀ i) ≤ WithZero.exp (-(N : ℤ))} (1 : (κ → Fv F v) → ℂ) ∈ Submodule.span ℂ (Set.range fun w : (κ → Fv F v) × (κ → Fv F v) => schr ψ w s) :=
  GlobalTheory.T.schwartzBruhat_span_box_indicator_schrodinger

theorem decomp : ∀ (F : Type) [Field F] [NumberField F] (v : Pl F) (κ : Type) [Fintype κ] (φ : (κ → Fv F v) → ℂ), φ ∈ SB (κ → Fv F v) → ∃ N₀ : ℕ, ∀ N ≥ N₀, φ ∈ Submodule.span ℂ (Set.range fun c : κ → Fv F v => Set.indicator {x : κ → Fv F v | ∀ i, Valued.v (x i - c i) ≤ WithZero.exp (-(N : ℤ))} (1 : (κ → Fv F v) → ℂ)) :=
  GlobalTheory.T.schwartzBruhat_mem_span_coordinateBox_indicators

def rhoSB {F : Type} [Field F] [NumberField F] (v : Pl F) (ψ : AddChar (Fv F v) ℂ) (hψ : Continuous ψ) {κ : Type}
    [Fintype κ] (w : (κ → Fv F v) × (κ → Fv F v)) : Module.End ℂ (SB (κ → Fv F v)) where
  toFun φ := ⟨schr ψ w φ, GlobalTheory.SchrSBFin.schr_mem_SB v ψ hψ w φ φ.2⟩
  map_add' φ φ' := by
    apply Subtype.ext; funext x
    simp only [schr, Submodule.coe_add, Pi.add_apply, mul_add]
  map_smul' c φ := by
    apply Subtype.ext; funext x
    simp only [schr, Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    ring

theorem rhoSB_apply {F : Type} [Field F] [NumberField F] (v : Pl F) (ψ : AddChar (Fv F v) ℂ) (hψ : Continuous ψ)
    {κ : Type} [Fintype κ] (w : (κ → Fv F v) × (κ → Fv F v)) (φ : SB (κ → Fv F v)) :
    ((rhoSB v ψ hψ w φ : SB (κ → Fv F v)) : (κ → Fv F v) → ℂ) = schr ψ w φ := rfl

theorem schr_mem_span {R : Type} [CommRing R] [Invertible (2 : R)] (ψ : AddChar R ℂ) {κ : Type} [Fintype κ]
    (s : (κ → R) → ℂ) (w : (κ → R) × (κ → R)) {f : (κ → R) → ℂ}
    (hf : f ∈ Submodule.span ℂ (Set.range fun w : (κ → R) × (κ → R) => schr ψ w s)) :
    schr ψ w f ∈ Submodule.span ℂ (Set.range fun w : (κ → R) × (κ → R) => schr ψ w s) := by
  let L : ((κ → R) → ℂ) →ₗ[ℂ] ((κ → R) → ℂ) :=
    { toFun := schr ψ w
      map_add' := fun a b => by funext x; simp only [schr, Pi.add_apply, mul_add]
      map_smul' := fun c a => by funext x; simp only [schr, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring }
  have hle : Submodule.span ℂ (Set.range fun w : (κ → R) × (κ → R) => schr ψ w s) ≤
      (Submodule.span ℂ (Set.range fun w : (κ → R) × (κ → R) => schr ψ w s)).comap L := by
    rw [Submodule.span_le]
    rintro _ ⟨w', rfl⟩
    show schr ψ w (schr ψ w' s) ∈ Submodule.span ℂ (Set.range fun w : (κ → R) × (κ → R) => schr ψ w s)
    rw [schr_schr]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨w + w', rfl⟩)
  exact hle hf

theorem schr_fst {R : Type} [CommRing R] [Invertible (2 : R)] (ψ : AddChar R ℂ) {κ : Type} [Fintype κ]
    (a : κ → R) (f : (κ → R) → ℂ) : schr ψ (a, 0) f = fun x => f (x + a) := by
  funext x; simp [schr]

theorem span_schr (F : Type) [Field F] [NumberField F] (v : Pl F) (ψ : AddChar (Fv F v) ℂ)
    (hu : ∀ x : Fv F v, (∀ y ∈ v.adicCompletionIntegers F, ψ (x * y) = 1) ↔ x ∈ v.adicCompletionIntegers F)
    (κ : Type) [Fintype κ] (s : (κ → Fv F v) → ℂ) (hs : s ∈ SB (κ → Fv F v)) (hs0 : s ≠ 0) :
    ∀ φ ∈ SB (κ → Fv F v),
      φ ∈ Submodule.span ℂ (Set.range fun w : (κ → Fv F v) × (κ → Fv F v) => schr ψ w s) := by
  intro φ hφ
  obtain ⟨x₀, N₀, hN₀⟩ := box_mem F v ψ hu κ s hs hs0
  obtain ⟨N₁, hN₁⟩ := decomp F v κ φ hφ
  refine Submodule.span_le.mpr ?_ (hN₁ (max N₀ N₁) (le_max_right _ _))
  rintro _ ⟨c, rfl⟩
  have h := schr_mem_span ψ s (x₀ - c, 0) (hN₀ (max N₀ N₁) (le_max_left _ _))
  rw [schr_fst] at h
  rw [SetLike.mem_coe]
  convert h using 1
  funext x
  have e : ∀ i, x i + (x₀ i - c i) - x₀ i = x i - c i := fun i => by ring
  simp only [Set.indicator_apply, Set.mem_setOf_eq, Pi.add_apply, Pi.sub_apply, e, Pi.one_apply]

end GlobalTheory.SchrLocModel

namespace GlobalTheory.SchrLocModel

theorem locCo_onto {F : Type} [Field F] [NumberField F] (v : Pl F) {Wm : Type} [AddCommGroup Wm] [Module (AF F) Wm]
    {Bf : Wm → Wm → AF F} {κ : Type} [Fintype κ] (co : Darboux Bf κ) {Y : Type} [AddCommGroup Y] (Xm : Y →+ Wm)
    (hX : ∀ z : Wm, At (evFin F v) z ↔ ∃ y, Xm y = z) (w : (κ → Fv F v) × (κ → Fv F v)) :
    ∃ x, GlobalTheory.LatVac.locCo co v (Xm x) = w := by
  set p : (κ → AF F) × (κ → AF F) := (fun k => GlobalTheory.LatVac.liftV v (w.1 k), fun k => GlobalTheory.LatVac.liftV v (w.2 k)) with hp
  have hzat : At (evFin F v) (co.e.symm p) := by
    intro u hu
    have hp0 : u • p = 0 := by
      refine Prod.ext (funext fun k => ?_) (funext fun k => ?_)
      · exact GlobalTheory.LatVac.at_liftV v (w.1 k) u hu
      · exact GlobalTheory.LatVac.at_liftV v (w.2 k) u hu
    rw [← map_smul, hp0, map_zero]
  obtain ⟨x, hx⟩ := (hX _).1 hzat
  refine ⟨x, ?_⟩
  rw [hx]
  refine Prod.ext (funext fun k => ?_) (funext fun k => ?_)
  · show evFin F v ((co.e (co.e.symm p)).1 k) = w.1 k
    rw [LinearEquiv.apply_symm_apply]
    exact GlobalTheory.LatVac.evFin_liftV v (w.1 k)
  · show evFin F v ((co.e (co.e.symm p)).2 k) = w.2 k
    rw [LinearEquiv.apply_symm_apply]
    exact GlobalTheory.LatVac.evFin_liftV v (w.2 k)

theorem exists_locRho : ∀ (F : Type) [Field F] [NumberField F] (v : Pl F) (ψ : AddChar (AF F) ℂ), IsStd ψ → PsiUnr ψ v →
    ∀ {Wm : Type} [AddCommGroup Wm] [Module (AF F) Wm] {Bf : Wm → Wm → AF F} {κ : Type} [Fintype κ] (co : Darboux Bf κ)
      (Y : Type) [AddCommGroup Y] (Xm : Y →+ Wm) (χ : Y → Y → ℂ),
      (∀ z : Wm, At (evFin F v) z ↔ ∃ y, Xm y = z) → (∀ x y, ψ (⅟(2 : AF F) * Bf (Xm x) (Xm y)) = χ x y) →
      ∃ ρ : Y → Module.End ℂ (SB (κ → Fv F v)), ρ 0 = 1 ∧ (∀ x y, ρ x * ρ y = χ x y • ρ (x + y)) ∧
        (∀ x (φ : SB (κ → Fv F v)), Acts (evFin F v) (co.rho ψ (Xm x)) (φ : (κ → Fv F v) → ℂ)
          ((ρ x φ : SB (κ → Fv F v)) : (κ → Fv F v) → ℂ)) ∧
        ∀ s : SB (κ → Fv F v), s ≠ 0 → Submodule.span ℂ (Set.range fun x => ρ x s) = ⊤ := by
  intro F _ _ v ψ hstd hunr Wm _ _ Bf κ _ co Y _ Xm χ hX hχ
  have hc : Continuous (GlobalTheory.LatVac.psiAt ψ v) := by
    have h : Continuous (GlobalTheory.LatVac.liftV v) := by
      change Continuous fun a => ((0 : Ainf F), GlobalTheory.AdelicU.singleFin v a)
      exact continuous_const.prodMk (GlobalTheory.AdelicU.continuous_singleFin v)
    exact hstd.1.comp h
  have hat : ∀ x, At (evFin F v) (Xm x) := fun x => (hX (Xm x)).2 ⟨x, rfl⟩
  refine ⟨fun x => rhoSB v (GlobalTheory.LatVac.psiAt ψ v) hc (GlobalTheory.LatVac.locCo co v (Xm x)), ?_, ?_, ?_, ?_⟩
  · apply LinearMap.ext; intro φ
    apply Subtype.ext; funext z
    simp [rhoSB, schr]
  · intro x y
    apply LinearMap.ext; intro φ
    apply Subtype.ext
    show schr (GlobalTheory.LatVac.psiAt ψ v) (GlobalTheory.LatVac.locCo co v (Xm x))
        (schr (GlobalTheory.LatVac.psiAt ψ v) (GlobalTheory.LatVac.locCo co v (Xm y)) φ) =
      χ x y • schr (GlobalTheory.LatVac.psiAt ψ v) (GlobalTheory.LatVac.locCo co v (Xm (x + y))) φ
    rw [schr_schr, map_add Xm, map_add (GlobalTheory.LatVac.locCo co v), ← hχ]
    congr 1
    rw [GlobalTheory.VacIndic.psi_of_at ψ (GlobalTheory.VacAny.at_mul_left _ (GlobalTheory.LatVac.DualLoc.at_form co v (hat x) (Xm y))),
      map_mul (evFin F v), GlobalTheory.VacAny.evFin_invOf_two, GlobalTheory.LatVac.DualLoc.evFin_form co v]
    rfl
  · intro x φ
    exact GlobalTheory.VacBridge.rho_acts_locCo co ψ v (Xm x) (hat x) φ
  · intro s hs
    rw [eq_top_iff]
    rintro t -
    have key := span_schr F v (GlobalTheory.LatVac.psiAt ψ v) (fun z => hunr z) κ s s.2
      (fun h => hs (Subtype.ext h)) t t.2
    have hmap : Submodule.span ℂ (Set.range fun w : (κ → Fv F v) × (κ → Fv F v) =>
        schr (GlobalTheory.LatVac.psiAt ψ v) w (s : (κ → Fv F v) → ℂ)) =
        (Submodule.span ℂ (Set.range fun x => rhoSB v (GlobalTheory.LatVac.psiAt ψ v) hc
          (GlobalTheory.LatVac.locCo co v (Xm x)) s)).map (SB (κ → Fv F v)).subtype := by
      rw [Submodule.map_span, ← Set.range_comp]
      congr 1
      ext f
      constructor
      · rintro ⟨w, rfl⟩
        obtain ⟨x, hx⟩ := locCo_onto v co Xm hX w
        exact ⟨x, by simp only [Function.comp_apply, Submodule.subtype_apply, rhoSB_apply, hx]⟩
      · rintro ⟨x, rfl⟩
        exact ⟨_, rfl⟩
    rw [hmap] at key
    obtain ⟨u, hu, hut⟩ := key
    rwa [show u = t from Subtype.ext hut] at hu

end GlobalTheory.SchrLocModel
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNormScaleCurveIdeal
section
open NumberField MeasureTheory
open scoped Classical
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum
open Formalism.MainNotions.TaylorLogMetric (VC embT tor0 Hf lamOf area Th U)
open Formalism.MainNotions.StandardLatticesGL3 (WeilO HeckeU TT stdL pt oddE0)
open GlobalTheory.NormSum (Pair Tup minorPol ratG intG Cls gam)
open GlobalTheory.NormDict GlobalTheory.NormExact
open GlobalTheory.BotFormula (IsFinPt)
open GlobalTheory.IndefiniteRowSideFullHecke.ClassFunctionSumIntegral (IsDefiniteSpace IsOpenCompactLevel)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.NormRatio

theorem unram (D : D7) : Algebra.Unramified (𝓞 (maximalRealSubfield D.host.E)) (𝓞 D.host.E) :=
  Formalism.L2.Pj.unramBridge_holds D.host.E fun P hP => by
    obtain ⟨θ, t, e1, e2⟩ := (GlobalTheory.Mem.host_cmData D.R D.host).cmUnram.2.2 P hP
    refine ⟨θ, ?_⟩
    have : RingOfIntegers.mapRingEquiv (IsCMField.complexConj D.host.E : D.host.E ≃+* D.host.E) θ = t :=
      RingOfIntegers.ext e1.symm
    rwa [this]

theorem cc_eq_conj (D : D7) (x : D.host.E) : IsCMField.complexConj D.host.E x = D.host.conj x := by
  apply D.host.φ₀.injective
  rw [IsCMField.complexEmbedding_complexConj]
  exact (Formalism.HC.HostAx.conjE_apply _ _ _).symm

end GlobalTheory.NormRatio

namespace GlobalTheory.NormRatio

open scoped Pointwise nonZeroDivisors

theorem map_mul_bar (D : D7) (hU : Algebra.Unramified (𝓞 (maximalRealSubfield D.host.E)) (𝓞 D.host.E))
    (cc : Ideal (𝓞 D.host.K)) (hc : cc ≠ ⊥) :
    Ideal.map (algebraMap (𝓞 D.host.K) (𝓞 D.host.E)) cc *
      (Ideal.map (algebraMap (𝓞 D.host.K) (𝓞 D.host.E)) cc).map
        ((Formalism.L2.Pj.hostOf D hU).bar : 𝓞 D.host.E →+* 𝓞 D.host.E) =
    Ideal.span {((Ideal.absNorm cc : ℕ) : 𝓞 D.host.E)} := by
  rw [← Formalism.MainNotions.UnusedSlot33.normK_holds D cc hc, Ideal.pointwise_smul_def]
  congr 2
  refine RingHom.ext fun x => RingOfIntegers.ext ?_
  show ((Formalism.L2.Pj.barE D x : 𝓞 D.host.E) : D.host.E) = ((D.host.conj • x : 𝓞 D.host.E) : D.host.E)
  rw [Formalism.L2.Pj.barE_eq_conj]
  exact (Formalism.TwoAdicCyclotomicDecomposition.odd_coe_smul D.host.conj x).symm

theorem absNorm_ne_zero {K : Type*} [Field K] [NumberField K] {I : Ideal (𝓞 K)} (h : I ≠ ⊥) :
    (Ideal.absNorm I : ℕ) ≠ 0 := fun h0 => h (Ideal.absNorm_eq_zero_iff.1 h0)

theorem map_ne_bot (D : D7) (hU : Algebra.Unramified (𝓞 (maximalRealSubfield D.host.E)) (𝓞 D.host.E))
    (cc : Ideal (𝓞 D.host.K)) (hc : cc ≠ ⊥) :
    Ideal.map (algebraMap (𝓞 D.host.K) (𝓞 D.host.E)) cc ≠ ⊥ := by
  intro h0
  have h := map_mul_bar D hU cc hc
  rw [h0, Ideal.bot_mul, eq_comm, Ideal.span_singleton_eq_bot] at h
  exact absNorm_ne_zero hc (by exact_mod_cast h)

theorem exists_mul_conj (D : D7) (cc c0 : Ideal (𝓞 D.host.K)) (hc : cc ≠ ⊥) (h0 : c0 ≠ ⊥) :
    ∃ r : D.host.E, r * D.host.conj r * ((Ideal.absNorm c0 : ℕ) : D.host.E) = ((Ideal.absNorm cc : ℕ) : D.host.E) := by
  have hU := unram D
  set H := Formalism.L2.Pj.hostOf D hU
  set F := maximalRealSubfield D.host.E
  have hn0 : ((Ideal.absNorm c0 : ℕ) : F) ≠ 0 := by exact_mod_cast absNorm_ne_zero h0
  have hn : ((Ideal.absNorm cc : ℕ) : F) ≠ 0 := by exact_mod_cast absNorm_ne_zero hc
  set x : F := ((Ideal.absNorm cc : ℕ) : F) / ((Ideal.absNorm c0 : ℕ) : F) with hxdef
  have hx : x ≠ 0 := div_ne_zero hn hn0
  have hid : FractionalIdeal.spanSingleton (𝓞 D.host.E)⁰ ((x : D.host.E)) *
      ((Ideal.map (algebraMap (𝓞 D.host.K) (𝓞 D.host.E)) c0 *
        (Ideal.map (algebraMap (𝓞 D.host.K) (𝓞 D.host.E)) c0).map (H.bar : 𝓞 D.host.E →+* 𝓞 D.host.E) : Ideal (𝓞 D.host.E)) :
        FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) =
      ((Ideal.map (algebraMap (𝓞 D.host.K) (𝓞 D.host.E)) cc *
        (Ideal.map (algebraMap (𝓞 D.host.K) (𝓞 D.host.E)) cc).map (H.bar : 𝓞 D.host.E →+* 𝓞 D.host.E) : Ideal (𝓞 D.host.E)) :
        FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) := by
    rw [map_mul_bar D hU c0 h0, map_mul_bar D hU cc hc, FractionalIdeal.coeIdeal_span_singleton,
      FractionalIdeal.coeIdeal_span_singleton, FractionalIdeal.spanSingleton_mul_spanSingleton]
    congr 1
    have hn0' : ((Ideal.absNorm c0 : ℕ) : D.host.E) ≠ 0 := by exact_mod_cast absNorm_ne_zero h0
    rw [hxdef]
    push_cast
    field_simp
  have hloc := GlobalTheory.local_norm_of_ideal_norm D.host.E H x hx
    ⟨_, _, map_ne_bot D hU c0 h0, map_ne_bot D hU cc hc, hid⟩
  have hreal : ∀ σ : F →+* ℝ, ∃ a b : ℝ, σ x = a ^ 2 - σ (-(H.d : F)) * b ^ 2 := by
    intro σ
    have hpos : 0 ≤ σ x := by
      rw [hxdef, map_div₀, map_natCast, map_natCast]; positivity
    exact ⟨Real.sqrt (σ x), 0, by rw [Real.sq_sqrt hpos]; ring⟩
  have hd : (-(H.d : F)) ≠ 0 := by
    have : (H.d : F) ≠ 0 := by exact_mod_cast H.d_prime.ne_zero
    exact neg_ne_zero.2 this
  obtain ⟨a, b, hab⟩ := GlobalTheory.QNorm.hasseNormSt F (-(H.d : F)) x hd hx hreal hloc
  refine ⟨(a : D.host.E) + (b : D.host.E) * D.host.sqrtMinusD, ?_⟩
  have ha : D.host.conj (a : D.host.E) = a := by
    rw [← cc_eq_conj]; exact (IsCMField.complexConj_eq_self_iff D.host.E _).2 a.2
  have hb : D.host.conj (b : D.host.E) = b := by
    rw [← cc_eq_conj]; exact (IsCMField.complexConj_eq_self_iff D.host.E _).2 b.2
  have hs : D.host.conj D.host.sqrtMinusD = -D.host.sqrtMinusD := Formalism.MainNotions.UnusedSlot33.PolarisationData.conj_b D
  have hs2 := D.host.sqrtMinusD_sq
  have hxE : (x : D.host.E) = (a : D.host.E) ^ 2 + (D.host.d : D.host.E) * (b : D.host.E) ^ 2 := by
    have := congrArg (fun t : F => (t : D.host.E)) hab
    push_cast at this
    rw [this]
    have hHd : ((H.d : ℕ) : D.host.E) = (D.host.d : D.host.E) := rfl
    rw [hHd]; ring
  have hn0' : ((Ideal.absNorm c0 : ℕ) : D.host.E) ≠ 0 := by exact_mod_cast absNorm_ne_zero h0
  have hxE' : (x : D.host.E) = ((Ideal.absNorm cc : ℕ) : D.host.E) / ((Ideal.absNorm c0 : ℕ) : D.host.E) := by
    rw [hxdef]
    push_cast
    try rfl
  rw [map_add, map_mul, ha, hb, hs]
  have key : ((a : D.host.E) + b * D.host.sqrtMinusD) * (a + b * -D.host.sqrtMinusD) = x := by
    rw [hxE]; linear_combination (-(b : D.host.E) ^ 2) * hs2
  rw [key, hxE']
  field_simp

end GlobalTheory.NormRatio

theorem GlobalTheory.NormRatio.exists_scale : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)), Formalism.MainNotions.TaylorLogMetric.IsCurveIdeal D cc → ∃ r : D.host.E, IsScale D cc r :=
  fun D cc hcc => GlobalTheory.NormRatio.exists_mul_conj D cc D.host.ccK hcc.1 D.host.ccK_ne_bot
end

