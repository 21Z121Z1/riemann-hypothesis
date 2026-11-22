import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsTestRep
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0163
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0208
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0091
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0943
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0953
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0952
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0143
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0137
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0132
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0116
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0136
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0110
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0193
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0127
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0174
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.BoundAtTwoAndThreeForFamily
import Development.AutomorphicArithmetic.CyclotomicBounds.CyclotomicOrders.NuHost
import Formalism.SharpRestriction.Bundle0002
import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.Bundle0005
import Formalism.SharpRestriction.LevelLetterCocycles.WachCoordinates
import Formalism.SharpRestriction.LevelLetterCocycles.RamifiedCoefficientChains
import Formalism.SharpRestriction.LevelLetterCocycles.ArcLiftingSetup
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0011
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0794
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0914
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0920
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0803
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0322
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0622
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0311
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0650
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2114
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0697

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.JacquetRallisFourierMatchOfWeilRepresentation
section
open GlobalTheory.JR Matrix MeasureTheory Filter Topology

namespace GlobalTheory.JR

theorem fourierMatchAt_of_weil (hW : WeilEt) (hR : RankOne) (hG : GammaOne) {r : ℕ} {F E : Type}
    [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E]
    (M : Meas r F E) (ψ : AddChar F ℂ) (hψ : IsStdChar ψ) (f' : Gl r F → ℂ) (f : Hn r F E → ℂ)
    (hf' : IsTest f') (hf : IsTest f) (hm : Match M f' f) (a : Inv r F) (ha : Delta a ≠ 0)
    (hsep : (companion a.1).charpoly.Separable) :
    MatchAt M (fourG M ψ f') (fourU M ψ f) a := by
  obtain ⟨A, τ, hτ⟩ := GlobalTheory.T.exists_etaleHermitianPair_isGen_companion F E r a.1 hsep
  obtain ⟨hbij, hmom⟩ := GlobalTheory.T.jacquetRallis_invK_regular_iff_isUnit F E A r τ a.1 a.2.2 hτ
  obtain ⟨a₀, ha₀⟩ := hbij.2 a.2.1
  have ha₀' : (fun i : Fin r => Algebra.trace F A.K (τ ^ (i : ℕ) * a₀)) = a.2.1 := ha₀
  have hinv : A.invK τ a.1 a.2.2 a₀ = a := by
    simp only [Et.invK, ha₀']
  have hu₀ : IsUnit a₀ := (hmom a₀).2.mp (by rw [hinv]; exact ha)
  obtain ⟨⟨m⟩, -⟩ := GlobalTheory.T.exists_selfDual_measures_and_absK_scale F E A ψ hψ
  obtain ⟨-, -, -, -, -, -, ⟨S, -, hS⟩, -⟩ := GlobalTheory.T.etaleHermitianPair_structure_facts F E A
  obtain ⟨φ', κ, hφ', hlin⟩ := GlobalTheory.T.jacquetRallis_linear_orbitalIntegral_descent F E A ψ hψ m r M τ a.1 a.2.2 hτ f' hf'
  obtain ⟨-, -, huniq, -⟩ := GlobalTheory.T.unitary_action_hermitian_invariants_transitive F E r
  obtain ⟨-, horbU, -, -⟩ := GlobalTheory.T.jacquetRallisOrbitalIntegrals_invariant_locallyConstant F E r M
  obtain ⟨hL11a, hL11b⟩ := GlobalTheory.T.hermitianBlock_invariants_iff_isometry F E A r τ a.1 a.2.2 hτ
  have key : ∀ x : A.Kˣ, ∃ φx : A.L → ℂ, IsTest φx ∧
      ((∃ j : A.L ≃ₗ[E] (Fin r → E), A.IsIsom (x : A.K) j) →
        ∃ (j : A.L ≃ₗ[E] (Fin r → E)) (Ax : selfAdjoint (Matrix (Fin r) (Fin r) E)), A.IsIsom (x : A.K) j ∧
          (∀ y, HasInv ((Ax, j y, a.2.2) : Hn r F E) (A.invK τ a.1 a.2.2 ((x : A.K) * A.NL y))) ∧
          ∀ y : A.L, IsUnit y → orbU M f (Ax, j y, a.2.2) = A.orbL m.ν φx y ∧
            orbU M (fourU M ψ f) (Ax, j y, a.2.2) = A.orbL m.ν (fourB (m.μL x) (A.kerL ψ x) φx) y) ∧
      ((¬ ∃ j : A.L ≃ₗ[E] (Fin r → E), A.IsIsom (x : A.K) j) → φx = 0) := by
    intro x
    by_cases hx : ∃ j : A.L ≃ₗ[E] (Fin r → E), A.IsIsom (x : A.K) j
    · obtain ⟨j, hj⟩ := hx
      obtain ⟨Ax, hAx, hinvAx⟩ := hL11b (x : A.K) j hj
      obtain ⟨φx, hφx, hrel⟩ := GlobalTheory.T.exists_test_orbU_eq_orbL F E A ψ hψ m r M τ a.1 a.2.2 hτ x j hj Ax hAx f hf
      exact ⟨φx, hφx, fun _ => ⟨j, Ax, hj, hinvAx, hrel⟩, fun h => absurd ⟨j, hj⟩ h⟩
    · exact ⟨0, ⟨IsLocallyConstant.const 0, HasCompactSupport.zero⟩, fun h => absurd h hx, fun _ => rfl⟩
  choose φ hφt hφi hφ0 using key
  choose γ Wr hWr using fun x : A.Kˣ => hW F E A ψ hψ x (m.μL x) (m.sdL x)
  have hunit : ∀ (x : A.Kˣ) (y : A.L), IsUnit y → IsUnit ((x : A.K) * A.NL y) := fun x y hy =>
    x.isUnit.mul (hy.map (Algebra.norm A.K))
  have hyp : ∀ x ∈ S, ∀ y : A.L, IsUnit y → κ * A.orbK m.μK φ' (x * A.NL y) = A.orbL m.ν (φ x) y := by
    intro x _ y hy
    have hb := hunit x y hy
    rw [← (hlin _ hb).1]
    by_cases hx : ∃ j : A.L ≃ₗ[E] (Fin r → E), A.IsIsom (x : A.K) j
    · obtain ⟨j, Ax, -, hinvAx, hrel⟩ := hφi x hx
      rw [← (hrel y hy).1]
      exact (hm _ ((hmom _).2.mpr hb)).1 _ (hinvAx y)
    · rw [hφ0 x hx]
      have h0 : orbG M f' (sec (A.invK τ a.1 a.2.2 ((x : A.K) * A.NL y))) = 0 := by
        apply (hm _ ((hmom _).2.mpr hb)).2
        rintro ⟨X, hX⟩
        obtain ⟨j, hj, -⟩ := hL11a _ X hb hX (x : A.K) y hy rfl
        exact hx ⟨j, hj⟩
      rw [h0]
      simp [Et.orbL]
  have hRk := hR F E A ψ hψ m S hS γ Wr (fun x _ => hWr x) φ' φ κ hφ' (fun x _ => hφt x) hyp
  have hG1 : ∀ (x : A.Kˣ) (j : A.L ≃ₗ[E] (Fin r → E)), A.IsIsom (x : A.K) j → γ x = 1 :=
    fun x j hj => hG F E A ψ hψ x (m.μL x) (m.sdL x) A.etaK (γ x) (Wr x) (hWr x) r j hj
  obtain ⟨x, ⟨hxS, y, hy, hxy⟩, -⟩ := hS hu₀.unit
  have hxy' : a₀ = x * A.NL y := by simpa using hxy
  have hb := hunit x y hy
  have hlhs : orbG M (fourG M ψ f') (sec a) =
      γ x * A.orbL m.ν (fourB (m.μL x) (A.kerL ψ x) (φ x)) y := by
    calc orbG M (fourG M ψ f') (sec a)
        = orbG M (fourG M ψ f') (sec (A.invK τ a.1 a.2.2 ((x : A.K) * A.NL y))) := by rw [← hxy', hinv]
      _ = κ * A.orbK m.μK (A.fourK m.μK ψ φ') ((x : A.K) * A.NL y) := (hlin _ hb).2
      _ = _ := hRk x hxS y hy
  constructor
  · intro X hX
    have hX' : HasInv X (A.invK τ a.1 a.2.2 a₀) := by rw [hinv]; exact hX
    obtain ⟨j₁, hj₁, -⟩ := hL11a a₀ X hu₀ hX' (x : A.K) y hy hxy'
    obtain ⟨j, Ax, hj, hinvAx, hrel⟩ := hφi x ⟨j₁, hj₁⟩
    have hXa : HasInv ((Ax, j y, a.2.2) : Hn r F E) a := by
      have := hinvAx y
      rw [← hxy', hinv] at this
      exact this
    obtain ⟨g, hg, -⟩ := huniq _ X a ha hXa hX
    rw [hlhs, hG1 x j hj, one_mul, ← (hrel y hy).2, ← hg, horbU]
  · intro hno
    have hx : ¬ ∃ j : A.L ≃ₗ[E] (Fin r → E), A.IsIsom (x : A.K) j := by
      intro hx
      obtain ⟨j, Ax, -, hinvAx, -⟩ := hφi x hx
      have := hinvAx y
      rw [← hxy', hinv] at this
      exact hno ⟨_, this⟩
    rw [hlhs, hφ0 x hx]
    simp [fourB, Et.orbL]

theorem fourierMatch_of_weil : WeilEt → RankOne → GammaOne → ∀ r, FourierMatch r := by
  intro hW hR hG r F E _ _ _ _ _ M ψ hψ f' f hf' hf hm
  obtain ⟨h4G, h4U, -⟩ := GlobalTheory.T.partialFourier_preserves_test_fixes_unit F E r M ψ hψ
  exact (GlobalTheory.T.jacquetRallis_match_of_dense_separable F E r M _ _ (h4G f' hf') (h4U f hf)).1
    (fun a ha hsep => fourierMatchAt_of_weil hW hR hG M ψ hψ f' f hf' hf hm a ha hsep)

end GlobalTheory.JR
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.JacquetRallisUnitMatchSucc
section
open GlobalTheory.JR Matrix MeasureTheory Filter Topology

noncomputable section

namespace GlobalTheory.JR.UnitStep

section Basic
variable {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E]

def qU {r : ℕ} (X : Hn r F E) : F := Algebra.trace F E (star X.2.1 ⬝ᵥ X.2.1) / 2

theorem mom_act_zero {r : ℕ} (g : GL (Fin r) F) (Y : Gl r F) : mom (act g Y) 0 = mom Y 0 := by
  simp only [mom, act, pow_zero, one_mulVec]
  rw [dotProduct_mulVec, vecMul_vecMul]
  have : ((g⁻¹ : GL (Fin r) F) : Matrix (Fin r) (Fin r) F) * (g : Matrix (Fin r) (Fin r) F) = 1 := by
    simp
  rw [this, vecMul_one]

theorem qU_actU {r : ℕ} (g : Matrix.unitaryGroup (Fin r) E) (X : Hn r F E) : qU (actU g X) = qU X := by
  simp only [qU, actU]
  congr 2
  rw [Matrix.star_mulVec, dotProduct_mulVec, vecMul_vecMul]
  have : (g.1)ᴴ * g.1 = 1 := by
    rw [← Matrix.star_eq_conjTranspose]; exact (Matrix.mem_unitaryGroup_iff').1 g.2
  rw [this, vecMul_one]

theorem mom_sec_zero {r : ℕ} (a : Inv (r + 1) F) : mom (sec a) 0 = a.2.1 0 := by
  simp [mom, sec, dotProduct]

theorem qU_of_hasInv [Unram F E] {r : ℕ} {X : Hn (r + 1) F E} {a : Inv (r + 1) F} (h : HasInv X a) :
    qU X = mom (sec a) 0 := by
  have h1 := congrArg (fun p => p.2.1 0) h
  simp only [inv, Inv.map, Hn.toGl, mom] at h1
  rw [show ((0 : Fin (r + 1)) : ℕ) = 0 from rfl, pow_zero, one_mulVec] at h1
  rw [mom_sec_zero, qU, h1, Algebra.trace_algebraMap, Unram.finrank_eq]
  haveI := (Unram.charZero (F := F) (E := E))
  rw [nsmul_eq_mul]; push_cast; field_simp

theorem orbG_mul {r : ℕ} (M : Meas r F E) (φ : F → ℂ) (f' : Gl r F → ℂ) (Y : Gl r F) :
    orbG M (fun Y => φ (mom Y 0) * f' Y) Y = φ (mom Y 0) * orbG M f' Y := by
  simp only [orbG, mom_act_zero, mul_assoc]
  exact integral_const_mul _ _

theorem orbU_mul {r : ℕ} (M : Meas r F E) (φ : F → ℂ) (f : Hn r F E → ℂ) (X : Hn r F E) :
    orbU M (fun X => φ (qU X) * f X) X = φ (qU X) * orbU M f X := by
  simp only [orbU, qU_actU]
  exact integral_const_mul _ _

theorem matchAt_mul [Unram F E] {r : ℕ} (M : Meas (r + 1) F E) (φ : F → ℂ) {f' : Gl (r + 1) F → ℂ}
    {f : Hn (r + 1) F E → ℂ} {a : Inv (r + 1) F} (h : MatchAt M f' f a) :
    MatchAt M (fun Y => φ (mom Y 0) * f' Y) (fun X => φ (qU X) * f X) a :=
  ⟨fun X hX => by rw [orbG_mul, orbU_mul, h.1 X hX, qU_of_hasInv hX],
    fun hn => by rw [orbG_mul, h.2 hn, mul_zero]⟩

theorem matchAt_mul_zero [Unram F E] {r : ℕ} (M : Meas (r + 1) F E) (φ : F → ℂ) (f' : Gl (r + 1) F → ℂ)
    (f : Hn (r + 1) F E → ℂ) {a : Inv (r + 1) F} (h0 : φ (mom (sec a) 0) = 0) :
    MatchAt M (fun Y => φ (mom Y 0) * f' Y) (fun X => φ (qU X) * f X) a :=
  ⟨fun X hX => by rw [orbG_mul, orbU_mul, qU_of_hasInv hX, h0, zero_mul, zero_mul],
    fun _ => by rw [orbG_mul, h0, zero_mul]⟩

theorem matchAt_of_mul [Unram F E] {r : ℕ} (M : Meas (r + 1) F E) (φ : F → ℂ) {f' : Gl (r + 1) F → ℂ}
    {f : Hn (r + 1) F E → ℂ} {a : Inv (r + 1) F} (h0 : φ (mom (sec a) 0) ≠ 0)
    (h : MatchAt M (fun Y => φ (mom Y 0) * f' Y) (fun X => φ (qU X) * f X) a) : MatchAt M f' f a := by
  refine ⟨fun X hX => ?_, fun hn => ?_⟩
  · have := h.1 X hX
    rw [orbG_mul, orbU_mul, qU_of_hasInv hX] at this
    exact mul_left_cancel₀ h0 this
  · have := h.2 hn
    rw [orbG_mul] at this
    exact (mul_eq_zero.1 this).resolve_left h0

theorem match_zero {r : ℕ} (M : Meas r F E) : Match M (0 : Gl r F → ℂ) (0 : Hn r F E → ℂ) := by
  intro a _
  refine ⟨fun X _ => ?_, fun _ => ?_⟩ <;> simp [orbG, orbU]

theorem isTest_sub {X : Type} [TopologicalSpace X] {f g : X → ℂ} (hf : IsTest f) (hg : IsTest g) :
    IsTest (f - g) :=
  ⟨hf.1.sub hg.1, hf.2.sub hg.2⟩

theorem wS_inv : (wS F)⁻¹ = wS F * wS F * wS F := by
  refine inv_eq_of_mul_eq_one_right (Subtype.ext ?_)
  simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_one]
  simp [wS, Matrix.mul_fin_two, Matrix.one_fin_two]

theorem nS_inv (t : F) : (nS t)⁻¹ = nS (-t) := by
  refine inv_eq_of_mul_eq_one_right (Subtype.ext ?_)
  show (!![1, t; 0, 1] : Matrix (Fin 2) (Fin 2) F) * !![1, -t; 0, 1] = 1
  simp [Matrix.mul_fin_two, Matrix.one_fin_two]

variable (E) in

theorem submonoid_eq_top [Unram F E] (S : Submonoid (SpecialLinearGroup (Fin 2) F)) (hw : wS F ∈ S)
    (hn : ∀ t : F, (∀ y : F, ‖y‖ < 1 → ‖t * y‖ ≤ 1) → nS t ∈ S) (x : SpecialLinearGroup (Fin 2) F) : x ∈ S := by
  have hgen := GlobalTheory.T.closure_weyl_and_integral_unipotents_eq_univ F E
  have hx : x ∈ Subgroup.closure ({wS F} ∪ {g | ∃ t : F, (∀ y : F, ‖y‖ < 1 → ‖t * y‖ ≤ 1) ∧ g = nS t}) := by
    rw [hgen]; trivial
  rw [← Subgroup.mem_toSubmonoid, Subgroup.closure_toSubmonoid] at hx
  refine (Submonoid.closure_le (S := S)).2 ?_ hx
  rintro g ((hg | ⟨t, ht, rfl⟩) | hg)
  · rw [Set.mem_singleton_iff.1 hg]; exact hw
  · exact hn t ht
  · rcases hg with hg | ⟨t, ht, hg⟩
    · rw [Set.mem_singleton_iff] at hg
      rw [← inv_inv g, hg, wS_inv]; exact S.mul_mem (S.mul_mem hw hw) hw
    · rw [← inv_inv g, hg, nS_inv]
      exact hn (-t) (fun y hy => by rw [neg_mul, norm_neg]; exact ht y hy)

end Basic
end GlobalTheory.JR.UnitStep

namespace GlobalTheory.JR.UnitStep

theorem unitMatch_succ : WeilEt → GammaOne → ∀ r : ℕ, FourierMatch (r + 1) → UnitMatch r → UnitMatch (r + 1) := by
  intro hWe hGo r hF hU F E _ _ _ _ _ M
  obtain ⟨ψ, hψ⟩ := (GlobalTheory.T.unramifiedStandardAddChar_conductor_properties F E).1
  obtain ⟨W1, hW1r, hW1⟩ := GlobalTheory.T.exists_weilRepSL2_glBorderedBlock F E (r + 1) M ψ hψ
  obtain ⟨W2, hW2r, hW2⟩ := GlobalTheory.T.exists_weilRepSL2_hermitianBlock hWe hGo F E (r + 1) M ψ hψ
  obtain ⟨hTG, hTU, htG, htU, hfG, hfU⟩ := GlobalTheory.T.partialFourier_preserves_test_fixes_unit F E (r + 1) M ψ hψ

  have hN1 : ∀ f, IsTest f → ∀ t : F, W1 (nS t) f = fun Y => (fun z => ψ (t * z)) (mom Y 0) * f Y :=
    fun f hf t => funext fun Y => (hW1 f hf).1 t Y
  have hN2 : ∀ f, IsTest f → ∀ t : F, W2 (nS t) f = fun X => (fun z => ψ (t * z)) (qU X) * f X :=
    fun f hf t => funext fun X => by
      rw [(hW2 f hf).1 t X, qU, mul_div_assoc]

  let S : Submonoid (SpecialLinearGroup (Fin 2) F) :=
    { carrier := {g | ∀ f' f, IsTest f' → IsTest f → Match M f' f → Match M (W1 g f') (W2 g f)}
      one_mem' := fun f' f hf' hf hm => by rw [hW1r.2.1 f' hf', hW2r.2.1 f hf]; exact hm
      mul_mem' := fun {g h} hg hh f' f hf' hf hm => by
        rw [hW1r.2.2.1 g h f' hf', hW2r.2.2.1 g h f hf]
        exact hg _ _ (hW1r.1 h f' hf') (hW2r.1 h f hf) (hh f' f hf' hf hm) }
  have hS : ∀ g, g ∈ S := submonoid_eq_top E S
    (fun f' f hf' hf hm => by rw [(hW1 f' hf').2, (hW2 f hf).2]; exact hF F E M ψ hψ f' f hf' hf hm)
    (fun t _ f' f hf' hf hm => by
      rw [hN1 f' hf' t, hN2 f hf t]
      exact fun a ha => matchAt_mul M (fun z => ψ (t * z)) (hm a ha))

  let u' := unitG (r + 1) F
  let u := unitU (r + 1) F E
  let S' : Submonoid (SpecialLinearGroup (Fin 2) F) :=
    { carrier := {g | Match M (W1 g u' - u') (W2 g u - u)}
      one_mem' := by
        show Match M (W1 1 u' - u') (W2 1 u - u)
        rw [hW1r.2.1 u' htG, hW2r.2.1 u htU, sub_self, sub_self]; exact match_zero M
      mul_mem' := fun {g h} hg hh => by
        show Match M (W1 (g * h) u' - u') (W2 (g * h) u - u)
        have e1 : W1 (g * h) u' - u' = W1 g (W1 h u' - u') + (W1 g u' - u') := by
          have hs : W1 h u' - u' = (-1 : ℂ) • u' + W1 h u' := by
            funext Y; simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]; ring
          rw [hW1r.2.2.1 g h u' htG, hs, hW1r.2.2.2 g (-1) u' (W1 h u') htG (hW1r.1 h u' htG)]
          funext Y; simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]; ring
        have e2 : W2 (g * h) u - u = W2 g (W2 h u - u) + (W2 g u - u) := by
          have hs : W2 h u - u = (-1 : ℂ) • u + W2 h u := by
            funext X; simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]; ring
          rw [hW2r.2.2.1 g h u htU, hs, hW2r.2.2.2 g (-1) u (W2 h u) htU (hW2r.1 h u htU)]
          funext X; simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]; ring
        have d1 : IsTest (W1 h u' - u') := isTest_sub (hW1r.1 h u' htG) htG
        have d2 : IsTest (W2 h u - u) := isTest_sub (hW2r.1 h u htU) htU
        rw [e1, e2]
        exact GlobalTheory.T.jacquetRallis_matching_add F E (r + 1) M _ _ _ _ (hW1r.1 g _ d1) (isTest_sub (hW1r.1 g u' htG) htG)
          (hW2r.1 g _ d2) (isTest_sub (hW2r.1 g u htU) htU) (hS g _ _ d1 d2 hh) hg }
  have hD1 : ∀ t : F, W1 (nS t) u' - u' = fun Y => (fun z => ψ (t * z) - 1) (mom Y 0) * u' Y := by
    intro t; rw [hN1 u' htG t]; funext Y; simp only [Pi.sub_apply]; ring
  have hD2 : ∀ t : F, W2 (nS t) u - u = fun X => (fun z => ψ (t * z) - 1) (qU X) * u X := by
    intro t; rw [hN2 u htU t]; funext X; simp only [Pi.sub_apply]; ring
  have hS' : ∀ g, g ∈ S' := submonoid_eq_top E S'
    (by
      show Match M (W1 (wS F) u' - u') (W2 (wS F) u - u)
      rw [(hW1 u' htG).2, (hW2 u htU).2, hfG, hfU, sub_self, sub_self]; exact match_zero M)
    (fun t ht => by
      show Match M (W1 (nS t) u' - u') (W2 (nS t) u - u)
      rw [hD1 t, hD2 t]
      intro a ha
      by_cases h1 : 1 ≤ ‖mom (sec a) 0‖
      · exact matchAt_mul M (fun z => ψ (t * z) - 1) (GlobalTheory.T.jacquetRallisUnitMatch_step_of_one_le_norm r hU F E M a ha h1)
      · refine matchAt_mul_zero M (fun z => ψ (t * z) - 1) u' u ?_
        have : ‖t * mom (sec a) 0‖ ≤ 1 := ht _ (lt_of_not_ge h1)
        simp [hψ.1 _ this])

  refine (GlobalTheory.T.jacquetRallis_match_of_dense_separable F E (r + 1) M u' u htG htU).2 (Nat.succ_pos r) ?_
  intro a ha ha0
  obtain ⟨x, hx, -⟩ := hψ.2
  have hm := hS' (nS (x / mom (sec a) 0))
  change Match M (W1 (nS _) u' - u') (W2 (nS _) u - u) at hm
  rw [hD1, hD2] at hm
  refine matchAt_of_mul M (fun z => ψ (x / mom (sec a) 0 * z) - 1) ?_ (hm a ha)
  simp only [div_mul_cancel₀ x ha0]
  exact sub_ne_zero.2 hx

end GlobalTheory.JR.UnitStep
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PolynomialBoundSetup
section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink

noncomputable section

namespace GlobalTheory.TheoremBQD

open MvPolynomial

def polyB : MvPolynomial (Fin 3) ℕ := 260 * X 0 ^ 2 * X 2 ^ 2 * (X 1 + X 2)

theorem polyB_val (f r t : ℕ) : 260 * f ^ 2 * t ^ 2 * (r + t) ≤ EmbeddingTypeJumps.polyVal polyB f r t := by
  simp [EmbeddingTypeJumps.polyVal, polyB]

theorem exists_good {D : D7} {i : D.nd.Loc} (hi : EmbeddingTypeJumps.AtQD i) : ∃ π, π ∈ D.nd.Zgood i := by
  obtain ⟨π, hπ⟩ := hi.2
  exact ⟨π, (D.Zgood_tie i π).2 hπ⟩

theorem main_of (hc : GlobalTheory.Published.GlobalArtinReciprocity → GlobalTheory.Published.BlochKatoLocal → Formalism.GaloisCohomology.LocalTateDualityK → Formalism.GaloisCohomology.LocalEulerCharK → ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F), ∀ (r : ∀ i : D.nd.Loc, D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (ρ : ∀ i : D.nd.Loc, D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (large₂ : SizeData₂ D) (ep : Bool) (C : ℝ) (Qp : MvPolynomial (Fin 3) ℕ), 2080 ≤ C → (∀ f r t : ℕ, 260 * f ^ 2 * t ^ 2 * (r + t) ≤ EmbeddingTypeJumps.polyVal Qp f r t) → EmbeddingTypeJumps.GlobalIndexAwayFromTypes r ρ → EmbeddingTypeJumps.admG1 r → EmbeddingTypeJumps.admG2 r ρ → EmbeddingTypeJumps.admG3 r ρ → EmbeddingTypeJumps.admG4 r → EmbeddingTypeJumps.admG5 r → EmbeddingTypeJumps.admG6 r → EmbeddingTypeJumps.iwahoriAdmissibleSet r ρ → EmbeddingTypeJumps.KillingTwistedPlaces ρ → EmbeddingTypeJumps.HodgeJumpWindowsAtDistinguishedPrimes r ep large₂ → EmbeddingTypeJumps.FontaineSubOfSumsAtDistinguishedPrimes r ρ → (∀ i : D.nd.Loc, EmbeddingTypeJumps.AtQD i → TruncatedSeriesCountingIdentities.TameGeneratorConditions i) → EmbeddingTypeJumps.ParametersPolynomiallyBounded large₂ → EmbeddingTypeJumps.Conclusion0 D ∧ EmbeddingTypeJumps.Conclusion1 D ∧ EmbeddingTypeJumps.Conclusion2 ρ large₂ C Qp) : ∃ (constantFirstHub : ℝ) (Q : MvPolynomial (Fin 3) ℕ), Hypotheses₂ → ∀ (D : D7) (L : SizeData₂ D) (P : ParameterChoice' D L) (nch : NChoice D) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F) (X : KillingConditions.HubData D) (C₂ : ℝ), Setup L nch HW X C₂ → EmbeddingTypeJumps.Conclusion2 X.ρ L constantFirstHub Q := by
  refine ⟨2080, polyB, ?_⟩
  intro hP D L P nch HW F Cm X C₂ hS
  have hb : (0 : ℝ) ≤ L.sc.b := (Real.exp_pos _).le
  have hX := GlobalTheory.T.split_bound_of_params hP.font hP.fin GlobalTheory.Published.cheb_holds D L HW F (rowC C₂) nch X 120 0 hS.canon P
    (by have := hS.big; linarith) le_rfl (by simpa using hb) (hS.facts.admJ L hS.par) hS.par67 hS.facts.toCore.admA
    hS.facts.Conclusion1.1 hS.facts.Conclusion1.2.2 hS.facts.Conclusion2.1 hS.facts.Conclusion2.2.2 hS.facts.rhoBar hS.facts.large.2.1
    hS.facts.large.2.2 hS.facts.nct hS.facts.trip hS.facts.same hS.facts.block hS.facts.muUnr hS.facts.depthG
  have hSet := GlobalTheory.T.set_point_good hP D L P nch HW F Cm X C₂ hS
  have hpt : ∀ i, EmbeddingTypeJumps.AtQD i → ∀ π ∈ D.nd.Zgood i, SetPt i (X.r i) (X.ρ i) π := fun i hi π hπ =>
    hSet i (GlobalTheory.AtQDTypes.l_not_mem_gset i hi.1.1) π hπ
  obtain ⟨ep, hep⟩ := (GlobalTheory.JumpStatement.holds_all D L (hS.facts.admJ L hS.par)).1
  have hJ := GlobalTheory.T.admJump_setup hP D L P nch HW F Cm X C₂ hS ep hep
  have hSt := GlobalTheory.T.lengthBound_of_rowConditions_and_dualityTheorems hP.artin hP.bk hP.tate hP.euler D (GlobalTheory.DesignUnconditional.main D hS.facts.large.2.2)
  have hN5 : EmbeddingTypeJumps.GlobalIndexAwayFromTypes X.r X.ρ := fun i π dc lenRow e' cB hA =>
    hSt.1 i (X.r i) (X.ρ i) π dc lenRow e' cB (hX.1 i) hA
  have hKill : EmbeddingTypeJumps.KillingTwistedPlaces X.ρ := by
    intro i hl htw _ π hπ
    have hk := hS.kill i htw
    have h2 := UpperTheory.KStar.nuL_eq_zero_of_qd D _ hl
    refine ⟨?_, ?_⟩
    · have := (hk.1 π hπ).2
      simpa [h2, TwistedPlaces.epsL, EmbeddingTypeJumps.epsL, one_div] using this
    · simpa [TwistedPlaces.epsL, EmbeddingTypeJumps.epsL, one_div, EmbeddingTypeJumps.vZeta] using hk.2
  refine (hc hP.artin hP.bk hP.tate hP.euler D HW F Cm X.r X.ρ L ep 2080 polyB le_rfl polyB_val hN5
    (fun i hi => by obtain ⟨π, hπ⟩ := exists_good hi; exact (hpt i hi π hπ).1)
    (fun i hi π hπ => (hpt i hi π hπ).2.1)
    (fun i hi π hπ => (hpt i hi π hπ).2.2.1)
    (fun i hi => by obtain ⟨π, hπ⟩ := exists_good hi; exact (hpt i hi π hπ).2.2.2.1)
    (fun i hi => by obtain ⟨π, hπ⟩ := exists_good hi; exact (hpt i hi π hπ).2.2.2.2.1)
    (fun i hi => by obtain ⟨π, hπ⟩ := exists_good hi; exact (hpt i hi π hπ).2.2.2.2.2.2.1)
    (fun i hi π hπ => by
      obtain ⟨-, -, -, -, -, -, -, -, hc1, hs1, hd1, he1, -⟩ := hpt i hi π hπ
      exact ⟨hc1, hs1, hd1, he1⟩)
    hKill hJ hX.2.2.1
    (fun i hi => by obtain ⟨π, hπ⟩ := exists_good hi; exact (hpt i hi π hπ).2.2.2.2.2.1)
    hS.par67).2.2

theorem main : ∃ (constantFirstHub : ℝ) (Q : MvPolynomial (Fin 3) ℕ), Hypotheses₂ → ∀ (D : D7) (L : SizeData₂ D) (P : ParameterChoice' D L) (nch : NChoice D) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F) (X : KillingConditions.HubData D) (C₂ : ℝ), Setup L nch HW X C₂ → EmbeddingTypeJumps.Conclusion2 X.ρ L constantFirstHub Q :=
  main_of GlobalTheory.T.twistedPlace_selmerLengthBound_of_localDuality

end GlobalTheory.TheoremBQD

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TwLevPow
section
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx
open Formalism.IndefR.FWT GlobalTheory.BigTop GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies GlobalTheory.SeriesTie
open GlobalTheory.BigOn GlobalTheory.BigOn.Exp Formalism.L2.Theta GlobalTheory.ExportSeries GlobalTheory.ConjTwist Formalism.IndefR.Lev
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwLevPow

theorem val_pow {E : Type} [Field E] [NumberField E] (χ : Formalism.L2.Host.HChar E) (a : ℕ) (v) :
    (χ ^ a).val v = χ.val v ^ a :=
  GlobalTheory.ConjExt.locK_pow χ a v _

theorem twLev_pow : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Hk3.Core R F →
    ∀ (χ : Formalism.L2.Host.HChar D.host.E) (xi : (AE D)ˣ →* Circle) (Q : Finset (Pl D.host.E)) (xiR : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ),
      GlobalTheory.BigOn.Exp.TwConj.TwLev R χ xi Q xiR → ∀ a b : ℕ, (χ ^ a) ^ b = χ →
      GlobalTheory.BigOn.Exp.TwConj.TwLev R (χ ^ a) (xi ^ a) Q (fun PP => xiR PP ^ a) := by
  intro D G _ _ Pl0 T0 A Ks _ _ _ R F hC χ xi Q xiR h a b hab

  have hQ0 : ∀ PP, PP ∉ R.Q A.μ0 := fun PP hPP =>
    ((hC.lev.Q_ram A.μ0 PP).2 (Or.inl hPP)) (by rw [hC.lev.xi_base]; intro x _; rfl)
  refine
    { xi := GlobalTheory.ConjExt.chrEq_pow h.xi a
      xi_fin := ?_
      xi_triv := GlobalTheory.ConjExt.trivOn_pow h.xi_triv a
      xi_tame := fun v x h1 h2 => by
        rw [GlobalTheory.ConjExt.loc_pow, h.xi_tame v x h1 h2, one_pow]
      Q_pl := h.Q_pl
      Q_off := h.Q_off
      Q_de := h.Q_de
      Q_ram := fun PP => Iff.trans
        (not_congr ⟨fun hu => hab ▸ GlobalTheory.ConjExt.unrAt_pow hu b, fun hu => GlobalTheory.ConjExt.unrAt_pow hu a⟩) (h.Q_ram PP)
      xiR := fun PP hP c k u h1 h2 => by
        show (xiR PP ^ a) u = (χ ^ a).locK PP k
        rw [GlobalTheory.ConjExt.locK_pow, MonoidHom.pow_apply, h.xiR PP hP c k u h1 h2]
      roots := h.roots
      muVal := ?_
      half := h.half
      guard := h.guard }
  · obtain ⟨n, hn, ho⟩ := h.xi_fin
    refine ⟨n, hn, ?_⟩
    show (χ ^ a) ^ n = 1
    rw [← pow_mul, mul_comm, pow_mul, show χ ^ n = 1 from ho, one_pow]
  · intro i P hP
    obtain ⟨x, hx⟩ := h.muVal i P hP
    have hP0 : Bridge.SplitOff (R.pl P) ((R.Sb : Set (Pl D.host.E)) ∪ (R.Q A.μ0 : Set (Pl D.host.E))) := by
      refine ⟨hP.1, fun hm => ?_, fun Q' hQ' => ?_⟩
      · rcases hm with hm | hm
        · exact hP.2.1 (Or.inl hm)
        · exact hQ0 _ hm
      · rcases hQ' with hQ' | hQ'
        · exact hP.2.2 Q' (Or.inl hQ')
        · exact absurd hQ' (hQ0 _)
    obtain ⟨g, c0R, c0L, ht⟩ := hC.fam.tie
    have hy := hC.fam.muVal i A.μ0 P ((ht.ok A.μ0 P).2 hP0)
    rw [hC.lev.xi_base, mul_one] at hy
    set y : D.what₂.LLˣ := A.muVal i A.μ0 P
    refine ⟨y * (y⁻¹ * x) ^ a, ?_⟩
    rw [Units.val_mul, Units.val_pow_eq_pow_val, Units.val_mul, map_mul, map_pow, map_mul, Units.val_inv_eq_inv_val,
      map_inv₀, hx, hy, Formalism.L2.Host.HChar.val_mul, Formalism.L2.Host.HChar.val_mul, val_pow]
    simp only [Units.val_mul, Units.val_pow_eq_pow_val]
    rw [inv_mul_cancel_left₀ (Units.ne_zero _)]

end GlobalTheory.TwLevPow
end
end

