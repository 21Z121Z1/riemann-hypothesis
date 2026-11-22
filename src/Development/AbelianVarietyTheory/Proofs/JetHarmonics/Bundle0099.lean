import Mathlib
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0096
import Development.AbelianVarietyTheory.Definitions.Jets.SideFam
import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
import Development.AbelianVarietyTheory.Definitions.Jets.CmLatticeCommutatorPairingPowEqOneOfGoodLift
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0270
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0269
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0006
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ProdExpPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0009
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ProdBox
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TWMain
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBCPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0014
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0004
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.Bundle0002
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0010
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0015
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0014
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0081
import Development.AbelianVarietyTheory.Definitions.Jets.JetsOnCopiesCompatibleFrames
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0095
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0088
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.FrameNStHolds
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0069
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0080
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0013
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0098
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0097
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0088
import Formalism.RealPlaceAnalysis.Bundle0004
import Development.AbelianVarietyTheory.Definitions.Jets.Bundle0001
import Development.AbelianVarietyTheory.Definitions.Jets.WigMap
import Formalism.RealPlaceAnalysis.Bundle0003
import Formalism.RealPlaceAnalysis.Bundle0002
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0016

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.BesselGapIntegrabilityStatement
section
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isBes_bessel_integral_of_gap : Hyps → ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (h : ℝ) (R : Rep k r) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp] (z : Fin (2 * r + k + 1) → ℂ) (π : Mx k r → (Wp →L[ℂ] Wp)) (u : ℕ → ℝ) (μW μN μG νq : Measure (Formalism.QuantumDeterminants.Mt k r)), R.IsDS ε mu → Formalism.QuantumDeterminants.GapAtLeast ε mu h → GapOK k r h → SideG k r z π u μW μN μG νq → ∀ v ∈ R.TK, ∀ ξ : Wp, IsBes R z π (fun w => be z Formalism.QuantumDeterminants.cStd π R.σ μW μN w v ξ) := by
  first | exact @GlobalTheory.be_apply_isBes | exact GlobalTheory.be_apply_isBes | (intros; apply GlobalTheory.be_apply_isBes <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.BesselSettingGapDecayStatement
section
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.bessel_orbital_integral_integrable_and_eq_smul : Hyps → ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (h : ℝ) (R : Rep k r) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp] (Wq : Type) [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [CompleteSpace Wq] [FiniteDimensional ℂ Wq] (D : B.RealPlaceData k r Wp Wq) (l : R.H → Wp) (l' : R.H → Wq), R.IsDS ε mu → Formalism.QuantumDeterminants.GapAtLeast ε mu h → GapOK k r h → IsBeL R D.z D.π D.μW D.μN l → IsBeL R D.z' D.π' D.μW' D.μN l' → ∃ OO : Mx k r → (Wq →L[ℂ] Wp), ∀ F s, IsCoef R l l' F s → ∀ γ ∈ JF.Om k r D.z D.z', Integrable (JF.integrand D F γ) D.μSS ∧ B.JF D F γ = s • OO γ := by
  first | exact @GlobalTheory.BesselOrbital.bessel_integral_eq_smul | exact GlobalTheory.BesselOrbital.bessel_integral_eq_smul | (intros; apply GlobalTheory.BesselOrbital.bessel_integral_eq_smul <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.CpSeriesCoeffNormBoundedRingLaws
section
open PowerSeries GlobalTheory.MomOne
open scoped ComplexConjugate BigOperators Topology

namespace GlobalTheory.MomOne

theorem sup_norm_laws : ∀ (q : ℕ) [Fact q.Prime], (∀ (f g : ℂ_[q]⟦X⟧) (A B : ℝ), Bd A f → Bd B g → Bd (max A B) (f + g) ∧ Bd (A * B) (f * g)) ∧ (∀ (f h : ℂ_[q]⟦X⟧) (A : ℝ), Bd A f → Bd 1 h → constantCoeff h = 0 → Bd A (f.subst h)) ∧ (∀ (f g : ℂ_[q]⟦X⟧), Bd 1 f → ‖constantCoeff f‖ = 1 → f * g = 1 → Bd 1 g) ∧ (∀ (f g : ℂ_[q]⟦X⟧) (B : ℝ), Bdd f → Bdd g → Bd B (f * g) → ∀ i j, ‖coeff i f‖ * ‖coeff j g‖ ≤ B) ∧ (∀ (f g : ℂ_[q]⟦X⟧), Bdd f → Bdd g → f * g = 1 → constantCoeff f = 1 → Bd 1 f ∧ Bd 1 g) ∧ (∀ (f v : ℂ_[q]⟦X⟧) (k : ℕ) (B : ℝ), Bd 1 v → ‖constantCoeff v‖ = 1 → Bd B (X ^ k * v * f) → Bd B f) := by
  intro q _
  have R := GlobalTheory.EvenTheta.SerRing.series_ring_laws q
  have hmul : ∀ (f g : ℂ_[q]⟦X⟧) (A B : ℝ), Bd A f → Bd B g → Bd (A * B) (f * g) :=
    fun f g A B hf hg => R.2.2.2.2.2.2 f g A B hf hg
  have hinv : ∀ f : ℂ_[q]⟦X⟧, Bd 1 f → ‖constantCoeff f‖ = 1 → Bd 1 f⁻¹ :=
    fun f hf h0 => R.2.2.2.2.1 f hf h0
  have hinv' : ∀ (f g : ℂ_[q]⟦X⟧), Bd 1 f → ‖constantCoeff f‖ = 1 → f * g = 1 → Bd 1 g := by
    intro f g hf h0 hfg
    have hc : constantCoeff f ≠ 0 := by
      intro h
      rw [h, norm_zero] at h0
      exact zero_ne_one h0
    have hgf : g = f⁻¹ := by
      rw [PowerSeries.eq_inv_iff_mul_eq_one hc, mul_comm]
      exact hfg
    rw [hgf]
    exact hinv f hf h0
  have hgauss : ∀ (f g : ℂ_[q]⟦X⟧) (B : ℝ), Bdd f → Bdd g → Bd B (f * g) →
      ∀ i j, ‖coeff i f‖ * ‖coeff j g‖ ≤ B :=
    fun f g B hf hg hB => GlobalTheory.EvenTheta.sup_norm_mul_padicComplex q f g B hf hg hB
  refine ⟨fun f g A B hf hg => ⟨fun n => GlobalTheory.EvenTheta.SerRing.norm_coeff_add_le f g A B hf hg n,
    hmul f g A B hf hg⟩, fun f h A hf hh h0 => R.2.2.2.2.2.1 f h A hf hh h0, hinv', hgauss, ?_, ?_⟩
  · intro f g hf hg hfg h1
    have hg0 : constantCoeff g = 1 := by
      have hc := congrArg constantCoeff hfg
      rw [map_mul, h1, one_mul, map_one] at hc
      exact hc
    have hB : Bd 1 (f * g) := by
      rw [hfg]
      intro n
      rw [coeff_one]
      split_ifs <;> simp
    have H := hgauss f g 1 hf hg hB
    refine ⟨fun i => ?_, fun j => ?_⟩
    · have hi := H i 0
      rwa [coeff_zero_eq_constantCoeff_apply, hg0, norm_one, mul_one] at hi
    · have hj := H 0 j
      rwa [coeff_zero_eq_constantCoeff_apply, h1, norm_one, one_mul] at hj
  · intro f v k B hv h0 hB
    have hw : Bd B (v * f) := by
      intro m
      have hm := hB (m + k)
      rwa [mul_assoc, coeff_X_pow_mul] at hm
    have hc : constantCoeff v ≠ 0 := by
      intro h
      rw [h, norm_zero] at h0
      exact zero_ne_one h0
    have hvf := hmul v⁻¹ (v * f) 1 B (hinv v hv h0) hw
    rwa [← mul_assoc, PowerSeries.inv_mul_cancel _ hc, one_mul, one_mul] at hvf

end GlobalTheory.MomOne
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsBoxFamilyPowerDegree
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj

namespace GlobalTheory.IntegralBox

open GlobalTheory.BoxIndep GlobalTheory.FieldBaseChange

theorem span_of_indep_residue {V M M' : Type} [CommRing V] [IsLocalRing V] [AddCommGroup M] [Module V M]
    [AddCommGroup M'] [Module (ResidueField V) M'] (π : M →ₛₗ[residue V] M') {I : Type} [Fintype I]
    (b t : I → M) (hb : ∀ s, ∃ c : I → V, s = ∑ i, c i • b i)
    (ht : ∀ c : I → ResidueField V, ∑ a, c a • π (t a) = 0 → c = 0) (s : M) :
    ∃ c : I → V, s = ∑ a, c a • t a := by
  classical
  choose w hw using fun a => hb (t a)
  let A : Matrix I I V := Matrix.of w
  have hA : IsUnit A.det := by
    rw [← residue_ne_zero_iff_isUnit, RingHom.map_det]
    intro h
    obtain ⟨c, hc, hc'⟩ := Matrix.exists_vecMul_eq_zero_iff.2 h
    refine hc (ht c ?_)
    have e : ∀ i, ∑ a, c a * residue V (w a i) = 0 := fun i => congrFun hc' i
    simp only [hw, map_sum, map_smulₛₗ, Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    exact Finset.sum_eq_zero fun i _ => by rw [← Finset.sum_smul, e, zero_smul]
  obtain ⟨d, rfl⟩ := hb s
  refine ⟨Matrix.vecMul d A⁻¹, ?_⟩
  have e : ∀ i, ∑ a, Matrix.vecMul d A⁻¹ a * w a i = d i := fun i =>
    congrFun (show Matrix.vecMul (Matrix.vecMul d A⁻¹) A = d by
      rw [Matrix.vecMul_vecMul, Matrix.nonsing_inv_mul _ hA, Matrix.vecMul_one]) i
  simp only [hw, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => by rw [← Finset.sum_smul, e]

theorem exists_tensor_pow (F O : Type) [Field F] [CommRing O] [Algebra F O] {m : ℕ} (j : ℕ)
    (β : Fin j → Fin m → O) (hβ : ∀ i, LinearIndependent F (β i)) :
    ∃ (B : Type) (_ : CommRing B) (_ : Algebra F B) (em : Fin j → (O →ₐ[F] B)),
      LinearIndependent F (fun a : Fin j → Fin m => ∏ i, em i (β i (a i))) := by
  induction j with
  | zero =>
    refine ⟨F, inferInstance, inferInstance, fun i => i.elim0, ?_⟩
    rw [linearIndependent_unique_iff]
    simp
  | succ j ih =>
    obtain ⟨B, _, _, em, h⟩ := ih (fun i => β i.succ) (fun i => hβ _)
    refine ⟨TensorProduct F O B, inferInstance, inferInstance,
      Fin.cons Algebra.TensorProduct.includeLeft
        (fun i => (Algebra.TensorProduct.includeRight).comp (em i)), ?_⟩
    have h2 := ((hβ 0).tmul_of_isDomain h).comp (Fin.consEquiv (fun _ : Fin (j+1) => Fin m)).symm
      (Equiv.injective _)
    refine (congrArg (fun v : (Fin (j + 1) → Fin m) → TensorProduct F O B => LinearIndependent F v)
      (funext fun a => ?_)).mpr h2
    simp only [Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ, AlgHom.comp_apply, Function.comp_apply]
    rw [← map_prod, Algebra.TensorProduct.includeLeft_apply, Algebra.TensorProduct.includeRight_apply,
      Algebra.TensorProduct.tmul_mul_tmul, _root_.mul_one, _root_.one_mul]
    rfl

variable {X Y Z : Scheme.{0}}

theorem exists_test {F : Type} [Field F] (p : X ⟶ Spec (CommRingCat.of F)) (x : X) {j : ℕ} {U : Fin j → X.Opens}
    (hx : ∀ i, x ∈ U i) {m : ℕ} (s : ∀ i, Fin m → Γ(X, U i))
    (hs : ∀ i (c : Fin m → F), ∑ l, germOf p x (c l) * gs (𝟙 X) x (U i) (s i l) = 0 → c = 0) :
    ∃ (Z : Scheme.{0}) (q : Z ⟶ Spec (CommRingCat.of F)) (r : Fin j → (Z ⟶ X)), (∀ i, r i ≫ p = q) ∧
      (∀ i z, r i z ∈ U i) ∧ ∀ c : (Fin j → Fin m) → F,
        (∀ z, ∑ a, germOf q z (c a) * ∏ i, gs (r i) z (U i) (s i (a i)) = 0) → c = 0 := by
  let : Algebra F (X.presheaf.stalk x) := (germOf p x).toAlgebra
  have hβ : ∀ i, LinearIndependent F (fun l => gs (𝟙 X) x (U i) (s i l)) := fun i =>
    Fintype.linearIndependent_iff.2 fun c hc => congrFun (hs i c (by simp only [Algebra.smul_def] at hc; exact hc))
  obtain ⟨B, _, _, em, h⟩ := exists_tensor_pow F _ j _ hβ
  refine ⟨Spec (CommRingCat.of B), Spec.map (CommRingCat.ofHom (algebraMap F B)),
    fun i => (Spec.map (CommRingCat.ofHom (em i).toRingHom) : _ ⟶ Spec (X.presheaf.stalk x)) ≫ X.fromSpecStalk x,
    fun i => ?_, fun i z => fromSpecStalk_mem x (hx i) _, fun c hc => ?_⟩
  · rw [Category.assoc, fromSpecStalk_comp]
    refine (Spec.map_comp _ _).symm.trans (congrArg Spec.map ?_)
    ext a
    exact (em i).commutes a
  · funext a
    refine Fintype.linearIndependent_iff.1 h c (eq_zero_of_germOf (B := CommRingCat.of B) _ fun z => ?_) a
    rw [← hc z, map_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Algebra.smul_def, map_mul, map_prod]
    congr 1
    · rw [← Category.id_comp (Spec.map _), germOf_map]; rfl
    · refine Finset.prod_congr rfl fun i _ => ?_
      rw [gs_fromSpecStalk x (hx i)]
      exact (germOf_map (B := X.presheaf.stalk x) (𝟙 _) (CommRingCat.ofHom (em i).toRingHom) z _).symm

theorem eq_zero_of_generic [IsIntegral Y] {R : Type} [CommRing R] (π : Y ⟶ Spec (CommRingCat.of R)) {L : LB X}
    {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ} (s : SecOver π (LB.LinComb L φ ε)) {J}
    (hJ : Good L (genericPoint Y) J) (h : sval s (𝟙 Y) (genericPoint Y) J = 0) : s = 0 := by
  refine SecOps.sec_ext fun jj => fn_ext fun y hy => congrArg _ ?_
  have hy' : genericPoint Y ∈ LB.wchart L φ jj :=
    ((genericPoint_spec _).mem_open_set_iff (TopologicalSpace.Opens.isOpen _)).mpr ⟨y, trivial, hy⟩
  apply germ_injective_of_isIntegral _ _ hy'
  refine (gs_eq (𝟙 _) _ _ hy' _).symm.trans (Eq.trans ?_ (map_zero _).symm)
  exact (sec_trans s (𝟙 _) _ hy' (hJ.mem φ _)).trans ((congrArg _ h).trans (mul_zero _))

theorem sval_comb {R : Type} [CommRing R] (π : Y ⟶ Spec (CommRingCat.of R)) {L : LB X}
    {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ} {I : Type} [Fintype I] (c : I → R)
    (s : I → SecOver π (LB.LinComb L φ ε)) (r : Z ⟶ Y) {z : Z} {J} (hJ : Good L z J) :
    sval (∑ i, c i • s i : SecOver π _) r z J =
      ∑ i, germOf (B := CommRingCat.of R) (r ≫ π) z (c i) * sval (s i) r z J := by
  rw [sval_sum' hJ]
  exact Finset.sum_congr rfl fun i _ => by rw [sval_smul' hJ, germOf_apply]; rfl

section Box

variable {V : Type} [CommRing V] [IsDomain V] {R : Type} [CommRing R] (φ : V →+* R) (D : DegPre V)

theorem isPullback_snd : IsPullback (snd (Over.mk (spMap φ)) D.P.A).left (fst (Over.mk (spMap φ)) D.P.A).left
    D.P.A.hom (spMap φ) := (IsPullback.of_hasPullback (spMap φ) D.P.A.hom).flip

abbrev SecMod (k : ℕ) (α : D.X) : Type := SecOver D.P.A.hom (LB.LinComb D.P.L (D.famφB α) (DegPre.famε k))

abbrev SecModBC (k : ℕ) (α : D.X) : Type :=
  SecOver (R := R) (fst (Over.mk (spMap φ)) D.P.A).left
    (LB.LinComb D.P.L (fun a => (snd (Over.mk (spMap φ)) D.P.A).left ≫ D.famφB α a) (DegPre.famε k))

noncomputable def pullBC (k : ℕ) (α : D.X) : SecMod D k α →ₛₗ[φ] SecModBC φ D k α :=
  pullOver D.P.L (DegPre.famε k) (isPullback_snd φ D).w (fun _ => rfl)

theorem sval_pullBC {k : ℕ} {α : D.X} (s : SecMod D k α) (r : Z ⟶ (Over.mk (spMap φ) ⊗ D.P.A).left) {z : Z} {J}
    (hJ : Good D.P.L z J) :
    sval (pullBC φ D k α s) r z J = sval s (r ≫ (snd (Over.mk (spMap φ)) D.P.A).left) z J :=
  sval_pullOver (isPullback_snd φ D).w (fun _ => rfl) s r hJ

theorem exists_basis [IsLocalRing V] [IsNoetherianRing V] (hT : TwistBaseChangeStatement) {k : ℕ} (hk : 1 ≤ k)
    (α : D.X) : ∃ b : Fin (k ^ D.P.g) → SecMod D k α, (∀ s, ∃ c : Fin (k ^ D.P.g) → V, s = ∑ i, c i • b i) ∧
      ∀ c : Fin (k ^ D.P.g) → R, ∑ i, c i • pullBC φ D k α (b i) = 0 → c = 0 := by
  have hL := D.P.isLB
  obtain ⟨m, b, rfl, hb⟩ := hT V D k hk α
  have H₀ : IsPullback (𝟙 D.P.A.left) D.P.A.hom D.P.A.hom (spMap (RingHom.id V)) := by
    have : spMap (RingHom.id V) = 𝟙 _ := by simp [spMap]
    rw [this]
    exact IsPullback.id_horiz _
  have hψ₀ : ∀ k, D.famφB α k = 𝟙 _ ≫ D.famφB α k := fun k => (Category.id_comp _).symm
  have h0 := ZH.BasisBaseChange.basis_of_isPullback (RingHom.id V) hL (D.famφB α) (DegPre.famε k) b
    (hb V (RingHom.id V) _ fun _ _ => rfl) H₀ hψ₀
  have e0 : ∀ i, pullOver D.P.L (DegPre.famε k) H₀.w hψ₀ (b i) = b i := fun i => sec_ext' hL fun y J hJ =>
    (sval_pullOver H₀.w hψ₀ _ _ hJ).trans (by rw [Category.comp_id])
  simp only [e0] at h0
  have h1 := ZH.BasisBaseChange.basis_of_isPullback φ hL (D.famφB α) (DegPre.famε k) b
    (hb R φ _ fun _ _ => rfl) (isPullback_snd φ D) (fun _ => rfl) (0 : SecModBC φ D k α)
  exact ⟨b, fun s => (h0 s).exists, fun c hc => h1.unique hc.symm
    (Finset.sum_eq_zero fun i _ => zero_smul R _).symm⟩

end Box

theorem box_indep {V : Type} [CommRing V] [IsDomain V] {F : Type} [Field F] (φ : V →+* F) {j : ℕ}
    {D D' : DegPre V} (pD : IsPowDeg D' D j) {k m : ℕ} (b : ∀ α, Fin m → SecMod D k α)
    (hb : ∀ α (c : Fin m → F), ∑ i, c i • pullBC φ D k α (b α i) = 0 → c = 0) (α' : D'.X)
    (c : (Fin j → Fin m) → F)
    (hc : ∑ a, c a • pullBC φ D' k α' (boxFamB pD k (fun i α => b α (a i)) α') = 0) : c = 0 := by
  let T₀ : Over (Spec (CommRingCat.of V)) := Over.mk (spMap φ)
  have := D.P.isAb.smooth
  have := D.P.isAb.geomConnected
  have hg := geometricallyIntegral_of_smooth_of_geometricallyConnected_fibres D.P.A.hom
  have hint : IsIntegral (T₀ ⊗ D.P.A).left := hg.geometrically_isIntegral _ _ _ (isPullback_snd φ D)
  choose J₀ hJ₀ using fun χ : (T₀ ⊗ D.P.A).left ⟶ D.P.A.left =>
    exists_chart D.P.isLB (χ (genericPoint (T₀ ⊗ D.P.A).left))
  have hJ₀ : Good D.P.L _ J₀ := hJ₀
  obtain ⟨Z, q, r, hq, hr, H⟩ := exists_test (F := F) (fst T₀ D.P.A).left _
    (fun i => hJ₀.mem (fun a => (snd T₀ D.P.A).left ≫ D.famφB (pD.xe α' i) a) (𝟙 _))
    (fun i l => (pullBC φ D k (pD.xe α' i) (b _ l)).f _)
    (fun i c hc => hb _ c (eq_zero_of_generic _ _ hJ₀ ((sval_comb _ c _ (𝟙 _) hJ₀).trans (by
      rw [Category.id_comp]; exact hc))))
  let T : Over (Spec (CommRingCat.of V)) := Over.mk (q ≫ T₀.hom)
  let q' : T ⟶ T₀ := Over.homMk q rfl
  let r' : Fin j → (T ⟶ T₀ ⊗ D.P.A) := fun i => Over.homMk (r i) (by
    rw [← Over.w (fst T₀ D.P.A), ← Category.assoc, hq]; rfl)
  let ρ : T ⟶ T₀ ⊗ D'.P.A := lift q' (Fan.IsLimit.lift pD.pw.lim fun i => r' i ≫ snd _ _)
  have hρ : ∀ i, (ρ ≫ snd _ _) ≫ pD.pw.pr i = r' i ≫ snd _ _ := fun i => by
    rw [lift_snd]
    exact Fan.IsLimit.fac pD.pw.lim _ i
  have hρ' : ∀ i, ((ρ.left : Z ⟶ _) ≫ (snd T₀ D'.P.A).left) ≫ (pD.pw.pr i).left =
      r i ≫ (snd T₀ D.P.A).left := fun i => congrArg (fun g => g.left) (hρ i)
  have hρq : (ρ.left : Z ⟶ _) ≫ (fst T₀ D'.P.A).left = q :=
    congrArg (fun g => g.left) (lift_fst q' (Fan.IsLimit.lift pD.pw.lim fun i => r' i ≫ snd _ _))
  refine H c fun z => ?_
  choose J hJ using fun ψ : Z ⟶ D.P.A.left => exists_chart D.P.isLB (ψ z)
  have hJ : Good D.P.L z J := hJ
  choose J' hJ' using fun ψ : Z ⟶ D'.P.A.left => exists_chart D'.P.isLB (ψ z)
  have hJ' : Good D'.P.L z J' := hJ'
  have E := (sval_comb _ c _ (ρ.left : Z ⟶ _) hJ').symm.trans
    ((congrArg (fun s : SecModBC φ D' k α' => sval (Z := Z) s ρ.left z J') hc).trans (sval_zero' hJ' _))
  rw [hρq] at E
  obtain ⟨u, hu⟩ : ∃ u : Z.presheaf.stalk z, ∀ a : Fin j → Fin m,
      u * sval (Z := Z) (pullBC φ D' k α' (boxFamB pD k (fun i α => b α (a i)) α')) ρ.left z J' =
      ∏ i, sval (pullBC φ D k (pD.xe α' i) (b _ (a i))) (r i) z J := by
    refine ⟨(∏ a, bw pD.w (((ρ.left : Z ⟶ _) ≫ (snd T₀ D'.P.A).left) ≫ D'.famφB α' a) z
      (fun i => J ((((ρ.left : Z ⟶ _) ≫ (snd T₀ D'.P.A).left) ≫ D'.famφB α' a) ≫ (pD.pw.pr i).left))
      (J' (((ρ.left : Z ⟶ _) ≫ (snd T₀ D'.P.A).left) ≫ D'.famφB α' a)) ^ DegPre.famε k a).val, fun a => ?_⟩
    obtain ⟨hψ, H'⟩ := isBoxFamB_boxFamB pD k (fun i α => b α (a i)) α'
    refine (congrArg _ (sval_pullBC φ D' _ _ hJ')).trans ((BoxFamScalar.box_sval pD.w hψ _ _ _ H' _ z hJ hJ').trans
      (Finset.prod_congr rfl fun i _ => ?_))
    rw [sval_pullBC φ D _ _ hJ]
    exact congrArg (fun g => sval (b _ (a i)) g z J) (hρ' i)
  obtain ⟨v, hv⟩ : ∃ v : Fin j → Z.presheaf.stalk z, ∀ i l,
      gs (r i) z (LB.wchart D.P.L (fun a => (snd T₀ D.P.A).left ≫ D.famφB (pD.xe α' i) a)
          (fun a => J₀ (𝟙 _ ≫ (snd T₀ D.P.A).left ≫ D.famφB (pD.xe α' i) a)))
        ((pullBC φ D k (pD.xe α' i) (b _ l)).f
          (fun a => J₀ (𝟙 _ ≫ (snd T₀ D.P.A).left ≫ D.famφB (pD.xe α' i) a))) =
      v i * sval (pullBC φ D k (pD.xe α' i) (b _ l)) (r i) z J :=
    ⟨_, fun i l => sec_trans _ (r i) z (hr i z) (hJ.mem _ (r i))⟩
  refine Eq.trans (Finset.sum_congr rfl fun a _ => ?_) ((Finset.mul_sum _ _ ((∏ i, v i) * u)).symm.trans
    ((congrArg _ E).trans (mul_zero _)))
  refine Eq.trans (congrArg _ (((Finset.prod_congr rfl fun i _ => hv i (a i)).trans Finset.prod_mul_distrib).trans
    (congrArg _ (hu a).symm))) ?_
  exact (congrArg _ (_root_.mul_assoc _ _ _).symm).trans (mul_left_comm _ _ _)

theorem main : Laws → Laws2 → Laws4 → TwistBaseChangeStatement → ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [IsAdicComplete (maximalIdeal V) V] (j : ℕ) (D D' : DegPre V) (pD : IsPowDeg D' D j) (k : ℕ), 1 ≤ k → ∀ (α' : D'.X) (β' : D'.SecB k α'), ∃ (l : ℕ) (c : Fin l → V) (f : Fin l → Fin j → ∀ α : D.X, D.SecB k α) (f' : Fin l → ∀ α : D'.X, D'.SecB k α), (∀ a, IsBoxFamB pD k (f' a) (f a)) ∧ ∀ jj, β'.f jj = ∑ a, constFn D'.P.A.hom _ (c a) * (f' a α').f jj := by
  intro _ _ _ hT V _ _ _ _ j D D' pD k hk α' β'
  choose b _ hb using exists_basis (residue V) D hT hk
  obtain ⟨b', hb', -⟩ := exists_basis (residue V) D' hT hk α'
  have hg := (rank_and_g_of_isPowDeg V j D D' pD).2
  let e : Fin (k ^ D'.P.g) ≃ (Fin j → Fin (k ^ D.P.g)) := Fintype.equivOfCardEq (by
    simp [hg, ← pow_mul, mul_comm])
  obtain ⟨c, hc⟩ := span_of_indep_residue (pullBC (residue V) D' k α') b'
    (fun n => boxFamB pD k (fun i α => b α (e n i)) α') hb' (fun c hc => by
      have := box_indep (residue V) pD b hb α' (fun a => c (e.symm a)) (by
        rw [← hc, ← e.sum_comp]
        simp only [Equiv.symm_apply_apply])
      funext n
      simpa using congrFun this (e n)) β'
  exact ⟨_, c, fun n i α => b α (e n i), fun n => boxFamB pD k (fun i α => b α (e n i)),
    fun n => isBoxFamB_boxFamB pD k _, (ZH.BasisBaseChange.isLin_iff D'.P.A.hom _ c β').2 hc⟩

end GlobalTheory.IntegralBox
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsGermLinearMap
section
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.ExpBijectiveUniformisation Formalism.MainNotions.ModuliIntegralCharts.H1.GSt
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
attribute [local instance] Over.cartesianMonoidalCategory
open Formalism.MainNotions.ModuliIntegralCharts.H1.BoxTuple Formalism.MainNotions.ModuliIntegralCharts.H1.BidegreeTwoJet GlobalTheory GlobalTheory.PowGerm
open ReciprocityTheory.ChartRestriction.G.TB (colM dAct)

namespace GlobalTheory.PairingLinear

def linOfComb {F M N : Type} [Field F] [AddCommGroup M] [Module F M] [AddCommGroup N] [Module F N] (f : M → N)
    (h : ∀ (l : ℕ) (c : Fin l → F) (s : Fin l → M), f (∑ i, c i • s i) = ∑ i, c i • f (s i)) : M →ₗ[F] N where
  toFun := f
  map_add' a b := by simpa using h 2 ![1, 1] ![a, b]
  map_smul' c a := by simpa using h 1 ![c] ![a]

theorem exists_germ_linearMap (hL : Laws) (hL2 : Laws2) (hL4 : Laws4) (hT : TwistBaseChangeStatement)
    (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [IsAdicComplete (maximalIdeal V) V]
    (D : DegData V (maximalIdeal V)) (A : PolAV (Spec (CommRingCat.of (FractionRing V)))) (G : Over (Sp V))
    [GrpObj G] [IsCommMonObj G] (U : Unif (maximalIdeal V) D A G) (κ : Type) [Fintype κ] [DecidableEq κ]
    (z : JetPts G κ) (hz : IsUnivJ G κ z) (τ : Frames U.LG.L z) (hτ : τ.Gen) (hτT : τ.Trunc)
    (F : Type) [Field F] [Algebra (FractionRing V) F] [Algebra V F] [IsScalarTower V (FractionRing V) F]
    (q : ℕ) (hq : 1 ≤ q) :
    ∃ gm : Fam D.toPre F q →ₗ[F] MvPowerSeries κ F,
      (∀ t σ' h, U.ExpandsG F q σ' t → GermA U.toUnifPre z τ F q σ' h → h = gm t) ∧
      ∀ t, ∃ σ', U.ExpandsG F q σ' t ∧ GermA U.toUnifPre z τ F q σ' (gm t) := by
  obtain ⟨huniq, hlin, hex⟩ := GlobalTheory.GermBasic.main V D A G U κ z hz τ hτ F q
  have hbij := (GlobalTheory.expandsG_bijective_of_dvr hL hL2 hL4 hT V D A G U F q hq).2
  choose S hS hSu using hbij
  choose Γg hΓ using hex hτT
  have key : ∀ t σ' h, U.ExpandsG F q σ' t → GermA U.toUnifPre z τ F q σ' h → h = Γg (S t) := by
    intro t σ' h he hg
    obtain rfl := hSu t σ' he
    exact huniq _ _ _ hg (hΓ _)
  refine ⟨linOfComb (fun t => Γg (S t)) fun l c s => ?_, key, fun t => ⟨S t, hS t, hΓ _⟩⟩
  let σ' : U.SecGF F q := GlobalTheory.ExpansionLinear.secComb
    (fun i => scal (fst (TFK (R := V) F) ((Over.pullback (jK V)).obj G)).left (c i)) (fun i => S (s i))
  exact (key _ σ' _
    (GlobalTheory.GroupExpansionLinear.expandsG_sum V D A G U F q l c (fun i => S (s i)) s σ' (fun i => hS _) (fun _ => rfl))
    (hlin l c (fun i => S (s i)) _ σ' (fun i => hΓ _) (fun _ => rfl))).symm

theorem main : Laws → Laws2 → Laws4 → TwistBaseChangeStatement → GPairF := by
  intro hL hL2 hL4 hT E _ _ _ H Dw l Xo c n
  letI := H.starRing
  intro T io y _ C hTr P _ g g' hg hg' _ _ _ π π' hπ _ _ _ _ F _ _ _ _ _ _ v ϖ _ _ Q _ D' A' G' _ _ pD pA pG U' PU _
    oD' hx hact p w ζ x hw _ _ _ _ Ppol
  letI := io.toAlgebra
  have hq : 1 ≤ g' * g := Nat.mul_pos hg'.pos hg.pos
  have hw0 : TraceFormTwistIso D'.toPre oD' H.w0 := GlobalTheory.PsiWZeroProd.main T.V n P.D.toPre D'.toPre pD (𝓞 E)
    (fun a x => funext fun i => hx a x i) P.oD oD' hact H.w0 P.w0
  obtain ⟨pl, -, hpl⟩ := PullLin.exists_pull_linearMap hL T.V D' F (𝓞 E) oD' H.w0 hw0 (star π) g g' hg.pos hg'.pos
    (by rw [star_star, _root_.mul_comm]; exact hπ)
  obtain ⟨Φ, hΦ⟩ := phiFun_of hL T.V _ D' F (g' * g) hq p w hw
  obtain ⟨τ, hτ, hτT, hiff⟩ := frameNSt_holds E H T.V C.I.G P _ C.FT C.actT C.ph1T C.ph2T C.syT C.adT C.tgT C.xT C.eT
    C.wPT C.chartT C.frameT C.primT n D' A' G' pD pA pG U' PU
  have hz := GlobalTheory.T.universalJets_power_product T.V C.I.G.G G' n _ pG C.xT (GlobalTheory.T.universal_statement E H Dw l Xo c T io y C)
  obtain ⟨gm, hgm, hgmex⟩ := exists_germ_linearMap hL hL2 hL4 hT T.V D' A' G' U' _ _ hz τ hτ (hτT hTr) F (g' * g) hq
  have hnab := (nabJet T.Fr _ (𝓞 E) C.ch.B F (MvPowerSeries.map (algebraMap T.Fr F) C.ch.h) H.w0 (g' * g) n
    (LtN Dw n) (fun ℓ : LtN Dw n => ℓ.2.2)
    (fun (ℓ : LtN Dw n) i => algebraMap T.Fr F (C.ch.uvec ⟨ℓ.1, ℓ.2.1⟩ i))).2.1 Ppol
  let ν : PS F n (chD C.ch) →ₗ[F] F := linOfComb (fun h => nabValN C.ch.B F
    (MvPowerSeries.map (algebraMap T.Fr F) C.ch.h) H.w0 (g' * g) h (fun ℓ : LtN Dw n => ℓ.2.2)
    (fun (ℓ : LtN Dw n) i => algebraMap T.Fr F (C.ch.uvec ⟨ℓ.1, ℓ.2.1⟩ i)) Ppol)
    fun k a f => hnab (Fin k) a f
  refine ⟨ν ∘ₗ gm ∘ₗ (ζ • Φ) ∘ₗ pl, fun s s₂ t₀ t σ' h h₁ h₂ h₃ h₄ h₅ => ?_, fun s => ?_⟩
  · rw [hgm t σ' h h₄ ((hiff F _ σ' h).1 h₅), (DVR.isSmul_iff _ _ _).1 h₃, (hΦ _ _).1 h₂, (hpl _ _).1 h₁]
    rfl
  · obtain ⟨σ', h₁, h₂⟩ := hgmex (ζ • Φ (pl s))
    exact ⟨pl s, Φ (pl s), _, σ', _, (hpl _ _).2 rfl, (hΦ _ _).2 rfl, (DVR.isSmul_iff _ _ _).2 rfl, h₁,
      (hiff F _ σ' _).2 h₂⟩

end GlobalTheory.PairingLinear
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsWignerContractionChainRaisingStatement
section
open Matrix Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Qr
open Formalism.REAL (qdet GlRel IsHW)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_wignerContraction_chain_raising : ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V] (n r : ℕ) (z : (Fin (2 * r + (n + 1) + 1) → ℂ)) (π : Mx (n + 1) r → (V →L[ℂ] V)) (u : ℕ → ℝ) (β : ℂ) (L : Fin (n + 1) → ℤ) (B : Fin (n + 1) → (Fin (2 * r + (n + 1) + 1) → ℂ)) (l : Fin (n + 1)) (n₀ : ℕ), inWb (n + 1) r z → 0 < Tz (n + 1) r z → IsType (n + 1) r z π u → StrictAnti L → (∀ j : Fin (n + 1), (u ((j : ℕ) + 1) : ℂ) - ((n + 1 : ℕ) : ℂ) / 2 + 1 / 2 = β + (L j : ℂ)) → IsFrameOf (n + 1) r [z] B → (∀ j, j < l → L l + (n₀ : ℤ) < L j) → ∃ (V₂ : Type) (_ : NormedAddCommGroup V₂) (_ : InnerProductSpace ℂ V₂) (_ : FiniteDimensional ℂ V₂) (π₂ : Mx (n + 1) r → (V₂ →L[ℂ] V₂)) (A : (Fin (2 * r + (n + 1) + 1) → ℂ) → (V₂ →L[ℂ] V)), IsType (n + 1) r z π₂ (Function.update u ((l : ℕ) + 1) (u ((l : ℕ) + 1) + (n₀ : ℝ))) ∧ GlobalTheory.WigSh.WigMap (n + 1) r z π₂ π n₀ A ∧ ∀ (M : Fin n → ℤ) (v : V), v ∈ CapSp (subA (EB π B)) (shf β M) → A (B (Fin.last n)) (ContinuousLinearMap.adjoint (A (B (Fin.last n))) v) = ((∏ j ∈ Finset.range n₀, GlobalTheory.WigSh.wP (Function.update L l (L l + (j : ℤ))) M l : ℝ) : ℂ) • v := by
  first | exact @GlobalTheory.WigSh.chain_raise | exact GlobalTheory.WigSh.chain_raise | (intros; apply GlobalTheory.WigSh.chain_raise <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.FamilySetupBesselGrowthStatement
section
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.bessel_functional_l2_bound_and_isometry : Hyps → ∀ (k r : ℕ) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp] (lam : Fin (2 * r + k + 1) → ℝ) (u : ℕ → ℝ) (b bv ga h : ℝ) (q0 : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (π : Mx k r → (Wp →L[ℂ] Wp)) (μW μN μG νq : Measure (Formalism.QuantumDeterminants.Mt k r)) (R : (Fin (2 * r + k + 1) → ℤ) → Rep k r) (l : ∀ ν, (R ν).H → Wp) (dg : (Fin (2 * r + k + 1) → ℤ) → ℝ), Setup lam u b bv ga h q0 z π μW μN μG νq R l dg → ∀ ν, n1 ν ≤ q0 → (∀ w ∈ (R ν).sm, ∫⁻ x, ENNReal.ofReal (1 * (dg ν * ‖l ν ((R ν).σ (Matrix.of x) w)‖ ^ 2)) ∂νq ≤ ENNReal.ofReal (‖w‖ ^ 2)) ∧ (NzOn (R ν) (l ν) → IsIsoB (R ν) z π νq (fun w => ((Real.sqrt (dg ν) : ℝ) : ℂ) • l ν w) ∧ ∀ w ∈ (R ν).sm, ∫⁻ x, ENNReal.ofReal (1 * (dg ν * ‖l ν ((R ν).σ (Matrix.of x) w)‖ ^ 2)) ∂νq = ENNReal.ofReal (‖w‖ ^ 2)) := by
  first | exact @GlobalTheory.MomMass.mom_mass | exact GlobalTheory.MomMass.mom_mass | (intros; apply GlobalTheory.MomMass.mom_mass <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.FamilySetupMomentGrowthStatement
section
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lowering_scalar_sq_mul_degree_ratio_le : Hyps → ∀ (k r : ℕ) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp] (lam : Fin (2 * r + k + 1) → ℝ) (u : ℕ → ℝ) (b bv ga h : ℝ) (q0 : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (π : Mx k r → (Wp →L[ℂ] Wp)) (μW μN μG νq : Measure (Formalism.QuantumDeterminants.Mt k r)) (R : (Fin (2 * r + k + 1) → ℤ) → Rep k r) (l : ∀ ν, (R ν).H → Wp) (dg : (Fin (2 * r + k + 1) → ℤ) → ℝ), Setup lam u b bv ga h q0 z π μW μN μG νq R l dg → ∀ ν, n1 ν + 1 ≤ q0 → ∀ io pr ep, TensH dualM (Formalism.QuantumDeterminants.Hpk k r) (R ν) (fun s => R (ν - Pi.single s 1)) io pr ep → NzOn (R ν) (l ν) → ∀ (s : Fin (2 * r + k + 1)) (κ₀ : ℂ), (∀ v ∈ (R ν).sm, l (ν - Pi.single s 1) (∑ c, pr s c (tm (R ν) (flat k r (Formalism.QuantumDeterminants.fvec k r z 0)) v c)) = κ₀ • l ν v) → ‖κ₀‖ ^ 2 * dg ν / dg (ν - Pi.single s 1) ≤ Formalism.QuantumDeterminants.Tz k r z * b ^ 4 := by
  first | exact @GlobalTheory.DualStepBound.dual_step_bound | exact GlobalTheory.DualStepBound.dual_step_bound | (intros; apply GlobalTheory.DualStepBound.dual_step_bound <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.GermBoxProductEqProdGermsStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.ExpBijectiveUniformisation Formalism.MainNotions.ModuliIntegralCharts.H1.GSt
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
attribute [local instance] Over.cartesianMonoidalCategory
open Formalism.MainNotions.ModuliIntegralCharts.H1.BoxTuple Formalism.MainNotions.ModuliIntegralCharts.H1.BidegreeTwoJet GlobalTheory GlobalTheory.PowGerm
open ReciprocityTheory.ChartRestriction.G.TB (colM dAct)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.germ_boxProduct_eq_prod_germs : Laws → Laws2 → Laws4 → TwistBaseChangeStatement → BoxGermSt := by
  first | exact @GlobalTheory.PowGerm.boxGermSt_holds | exact GlobalTheory.PowGerm.boxGermSt_holds | (intros; apply GlobalTheory.PowGerm.boxGermSt_holds <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ImportsTer
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.ExpBijectiveUniformisation Formalism.MainNotions.ModuliIntegralCharts.H1.GSt
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
attribute [local instance] Over.cartesianMonoidalCategory
open Formalism.MainNotions.ModuliIntegralCharts.H1.BoxTuple Formalism.MainNotions.ModuliIntegralCharts.H1.BidegreeTwoJet GlobalTheory GlobalTheory.PowGerm

namespace GlobalTheory.PowThetaFrame

theorem main : Laws → Laws2 → Laws4 → TwistBaseChangeStatement → ThetaFrameF := by
  intro hL hL2 hL4 hT E _ _ _ H Dw l Xo c n T io y _ C P _ g g' _ hg' _ _ _ π π' _ hπ' _ _ _ F _ _ _ _ _ _ v ϖ hϖ hv
    Q hQ D' A' G' _ _ pD pA pG U' PU _ oD' hx hact
  let _ := H.starRing
  obtain ⟨θ, hν, hθ⟩ := exists_thetaFrame hL hL2 hL4 hT T.V ϖ hϖ D' (sumQ pD.xe Q)
    (QBox.main T.V ϖ hϖ n P.D D' pD Q hQ) F v hv
  have hw : TraceFormTwistIso D'.toPre oD' H.w0 :=
    PsiWZeroProd.main T.V n P.D.toPre D'.toPre pD (𝓞 E) (fun a x => funext (hx a x)) P.oD oD' hact H.w0 P.w0
  obtain ⟨f, -, hf⟩ := PullLin.exists_pull_linearMap hL T.V D' F (𝓞 E) oD' H.w0 hw (star π') g' 1 hg'.one_le le_rfl
    (by rw [star_star, mul_comm]; exact hπ')
  exact ⟨θ, f θ, hν, hθ, (hf _ _).2 rfl⟩

end GlobalTheory.PowThetaFrame
end

