import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0030
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2813
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2661
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2373
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3016
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2983
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2978
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0083
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1589
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2976
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0946
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.DifferentiableOnOfTendstoLocallyUniformlyOn
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3028
import Development.AbelianVarietyTheory.Definitions.Divisors.NonemptyUWit
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0080
import Development.AbelianVarietyTheory.Definitions.Divisors.DensConst
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0049
import Development.AbelianVarietyTheory.Definitions.Divisors.IsAmbOfIsArithVar
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0005
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2950
import ReciprocityTheory.AnalyticForms.PotentialTheory.ProjectiveLineFubiniStudyFacts
import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.Bundle0005
import ReciprocityTheory.L2DbarEstimates.LeviForms.Bundle0002
import Development.AbelianVarietyTheory.Definitions.Divisors.SmallFam
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0014
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0016

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RuleEqOfAgreeRapoportOfLevel
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.RealMult.QUniq

theorem eq_of_loc_two_three (R : Type) [CommRing R] (x y : R)
    (h2 : algebraMap R (Localization.Away (2 : R)) x = algebraMap R (Localization.Away (2 : R)) y)
    (h3 : algebraMap R (Localization.Away (3 : R)) x = algebraMap R (Localization.Away (3 : R)) y) : x = y := by
  rw [← sub_eq_zero]
  rw [← sub_eq_zero, ← map_sub] at h2 h3
  obtain ⟨⟨_, n, rfl⟩, hn⟩ := (IsLocalization.map_eq_zero_iff (Submonoid.powers (2 : R)) _ _).1 h2
  obtain ⟨⟨_, m, rfl⟩, hm⟩ := (IsLocalization.map_eq_zero_iff (Submonoid.powers (3 : R)) _ _).1 h3
  have hc : IsCoprime ((2 : R) ^ n) ((3 : R) ^ m) := by
    have : IsCoprime (2 : R) 3 := ⟨-1, 1, by norm_num⟩
    exact this.pow
  obtain ⟨a, b, hab⟩ := hc
  simp only at hn hm
  calc x - y = (a * 2 ^ n + b * 3 ^ m) * (x - y) := by rw [hab, _root_.one_mul]
    _ = a * (2 ^ n * (x - y)) + b * (3 ^ m * (x - y)) := by ring
    _ = 0 := by rw [hn, hm]; ring

theorem eq_of_loc_away (R : Type) [CommRing R] (f : PrimeSpectrum R → R) (hf : ∀ p, f p ∉ p.asIdeal)
    (x y : R) (h : ∀ p, algebraMap R (Localization.Away (f p)) x = algebraMap R (Localization.Away (f p)) y) :
    x = y := by
  rw [← sub_eq_zero]
  let I : Ideal R := LinearMap.ker (LinearMap.toSpanSingleton R R (x - y))
  have hI : I = ⊤ := by
    by_contra hI
    obtain ⟨q, hq, hIq⟩ := Ideal.exists_le_maximal I hI
    let p : PrimeSpectrum R := ⟨q, hq.isPrime⟩
    have hp := h p
    rw [← sub_eq_zero, ← map_sub] at hp
    obtain ⟨⟨_, n, rfl⟩, hn⟩ := (IsLocalization.map_eq_zero_iff (Submonoid.powers (f p)) _ _).1 hp
    have hmem : f p ^ n ∈ I := by
      simp only [I, LinearMap.mem_ker, LinearMap.toSpanSingleton_apply, smul_eq_mul]
      exact hn
    exact hf p (hq.isPrime.mem_of_pow_mem n (hIq hmem))
  have h1 : (1 : R) ∈ I := hI ▸ Submodule.mem_top
  simpa [I] using h1

variable {F : Type} [Field F] [NumberField F] {𝔠 : FracId F}

theorem isRapoport_of_range_subset {M : Scheme.{0}} (U : Obj F 𝔠 M) {A : Type} [CommRing A] (c : Sp A ⟶ M)
    (X : Obj F 𝔠 (Sp A)) (φ : X.A.left ⟶ U.A.left) (hX : X.IsPullBy U c φ) (hr : Set.range c ⊆ U.rapLocus) :
    X.IsRapoport := by
  rw [Obj.isRapoport_iff]
  refine Set.eq_univ_of_forall fun s ↦ ?_
  intro K _ t hs Y ψ hY
  obtain ⟨p, rfl⟩ := hs
  exact hr ⟨t p, rfl⟩ K (t ≫ c) ⟨p, rfl⟩ Y (ψ ≫ φ) (hY.comp hX)

theorem agreeAt_on_model : ∀ (F : Type) [Field F] [NumberField F] (𝔠 : FracId F) (N : ℕ) (M : Scheme.{0})
    (sM : M ⟶ Sp (Localization.Away (N : ℤ))) (U : Obj F 𝔠 M) (V : M.Opens), (V : Set M) = U.rapLocus → Flat sM →
    (∀ (K : Type) [Field K] (t : Sp K ⟶ Sp (Localization.Away (N : ℤ))), Geo.Tor.IsNormalScheme (pullback sM t)) →
    (∀ (K : Type) [Field K] (t : Sp K ⟶ Sp (Localization.Away (N : ℤ))) (y : ↥(pullback sM t)),
      pullback.fst sM t y ∉ V → 2 ≤ ringKrullDim ((pullback sM t).presheaf.stalk y)) →
    ∀ (R₀ : Type) [CommRing R₀] (k : ℕ) (r s : Rule (trivialObjectCondition 𝔠) R₀ k),
    (∀ (R : Type) [CommRing R] [Algebra R₀ R] (X : Obj F 𝔠 (Sp R)), X.IsRapoport → r.AgreeAt s X) →
    ∀ (W : M.Opens) (hW : IsAffineOpen W) (X : Obj F 𝔠 (Sp (R₀ ⊗[ℤ] Γ(M, W)))) (φ : X.A.left ⟶ U.A.left),
      X.IsPullBy U (coefSpecMap hW R₀) φ → r.AgreeAt s X := by
  intro F _ _ 𝔠 N M sM U V hV hflat hnorm hcod R₀ _ k r s hrap W hW X φ hX δ
  rw [← sub_eq_zero]
  have key : TensorProduct.comm ℤ R₀ Γ(M, W) (r.val _ X trivial δ - s.val _ X trivial δ) = 0 := by
    refine rTensor_eq_zero_of_restrict_affine_inf N M sM V hflat hnorm hcod W hW R₀ _ fun W' hW' hle ↦ ?_
    let ρ : R₀ ⊗[ℤ] Γ(M, W) →ₐ[R₀] R₀ ⊗[ℤ] Γ(M, W') :=
      Algebra.TensorProduct.map (AlgHom.id R₀ R₀) (M.presheaf.map (homOfLE (hle.trans inf_le_left)).op).hom.toIntAlgHom
    obtain ⟨X', φ', hX'⟩ := Obj.exists_isPullBy X (spMap ρ.toRingHom)
    obtain ⟨δ', hδ', -⟩ := Obj.IsPullBy.existsUnique_detGen (R := R₀ ⊗[ℤ] Γ(M, W)) (R' := R₀ ⊗[ℤ] Γ(M, W')) _ hX' δ
    have hU : X'.IsPullBy U (coefSpecMap hW' R₀) (φ' ≫ φ) := by
      rw [← GlobalTheory.T.coefficient_spec_restriction_compatible M W W' hW hW' (hle.trans inf_le_left) R₀]; exact hX'.comp hX
    have hrng : Set.range (coefSpecMap hW' R₀) ⊆ U.rapLocus := by
      rintro _ ⟨y, rfl⟩
      rw [← hV]
      have : (coefSpecMap hW' R₀) y ∈ Set.range hW'.fromSpec := ⟨_, rfl⟩
      rw [hW'.range_fromSpec] at this
      exact (hle.trans inf_le_right) this
    have hrX' := isRapoport_of_range_subset U _ X' _ hU hrng
    have e := hrap _ X' hrX' δ'
    rw [r.baseChange _ _ ρ X trivial X' trivial φ' δ δ' hX' hδ', s.baseChange _ _ ρ X trivial X' trivial φ' δ δ' hX' hδ',
      ← sub_eq_zero, ← map_sub] at e
    have hcomm : ∀ h, LinearMap.rTensor R₀
        (M.presheaf.map (homOfLE (hle.trans inf_le_left)).op).hom.toAddMonoidHom.toIntLinearMap
        (TensorProduct.comm ℤ R₀ Γ(M, W) h) =
          TensorProduct.comm ℤ R₀ Γ(M, W') (ρ h) := by
      intro h
      induction h using TensorProduct.induction_on with
      | zero => simp
      | tmul a g => rfl
      | add x y hx hy => simp only [map_add, hx, hy]
    rw [hcomm, e, map_zero]
  exact (TensorProduct.comm ℤ R₀ Γ(M, W)).map_eq_zero_iff.1 key

end GlobalTheory.RealMult.QUniq

namespace GlobalTheory.RealMult.QUniq

variable {F : Type} [Field F] [NumberField F] {𝔠 : FracId F} {R₀ : Type} [CommRing R₀] {k : ℕ}

theorem agreeAt_of_one (r s : Rule (trivialObjectCondition 𝔠) R₀ k) {R : Type} [CommRing R] [Algebra R₀ R] (X : Obj F 𝔠 (Sp R))
    (δ₀ : X.DetGen) (h : r.val R X trivial δ₀ = s.val R X trivial δ₀) : r.AgreeAt s X := by
  intro δ
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.1 (δ.2.symm ▸ Submodule.mem_top : δ₀.1 ∈ Submodule.span R {δ.1})
  rw [← r.homog R X trivial δ δ₀ c hc.symm, ← s.homog R X trivial δ δ₀ c hc.symm, h]

theorem agreeAt_of_inj (r s : Rule (trivialObjectCondition 𝔠) R₀ k) {R : Type} [CommRing R] [Algebra R₀ R] (X : Obj F 𝔠 (Sp R))
    {J : Type} (R' : J → Type) [∀ i, CommRing (R' i)] [∀ i, Algebra R₀ (R' i)] (σ : ∀ i, R →ₐ[R₀] R' i)
    (hinj : ∀ x y : R, (∀ i, σ i x = σ i y) → x = y)
    (h : ∀ i (X' : Obj F 𝔠 (Sp (R' i))) (φ : X'.A.left ⟶ X.A.left),
      X'.IsPullBy X (spMap (σ i : R →+* R' i)) φ → r.AgreeAt s X') : r.AgreeAt s X := by
  intro δ
  refine hinj _ _ fun i ↦ ?_
  obtain ⟨X', φ, hX'⟩ := Obj.exists_isPullBy X (spMap (σ i : R →+* R' i))
  obtain ⟨δ', hδ', -⟩ := hX'.existsUnique_detGen (σ i : R →+* R' i) δ
  have e1 := r.baseChange R (R' i) (σ i) X trivial X' trivial φ δ δ' hX' hδ'
  have e2 := s.baseChange R (R' i) (σ i) X trivial X' trivial φ δ δ' hX' hδ'
  change r.val (R' i) X' trivial δ' = (σ i : R →+* R' i) _ at e1
  change s.val (R' i) X' trivial δ' = (σ i : R →+* R' i) _ at e2
  have := h i X' φ hX' δ'
  simpa [e1, e2] using this

end GlobalTheory.RealMult.QUniq

namespace GlobalTheory.RealMult.QUniq

variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F] {𝔠 : FracId F} {R₀ : Type} [CommRing R₀] {k : ℕ}

theorem agreeAt_of_level (hDP : GlobalTheory.Published.DelignePappasModel) (r s : Rule (trivialObjectCondition 𝔠) R₀ k)
    (hrap : ∀ (R : Type) [CommRing R] [Algebra R₀ R] (X : Obj F 𝔠 (Sp R)), X.IsRapoport → r.AgreeAt s X)
    (N : ℕ) (hN : 3 ≤ N) {R : Type} [CommRing R] [Algebra R₀ R] (hu : IsUnit (N : R)) (X : Obj F 𝔠 (Sp R))
    (α : X.Level N) : r.AgreeAt s X := by
  obtain ⟨M, sM, U, αU, hfine, -, -, -, hflat, -, ⟨V, hV, -, -, hcod⟩, hnorm, -⟩ := hDP F 𝔠 N hN
  let t : Sp R ⟶ Sp (Localization.Away (N : ℤ)) :=
    spMap (IsLocalization.Away.lift (S := Localization.Away (N : ℤ)) (N : ℤ) (g := Int.castRingHom R) (by simpa using hu))
  obtain ⟨b, ⟨-, φ, hφ, -⟩, -⟩ := hfine (Sp R) t X α
  have hmod := agreeAt_on_model F 𝔠 N M sM U V hV hflat hnorm hcod R₀ k r s hrap
  choose W hW hmW hgen using fun x : Sp R ↦ GlobalTheory.T.determinant_generator_locally_exists F 𝔠 M U R₀ (b x)
  choose f hf g hg using fun x : Sp R ↦ GlobalTheory.T.local_section_of_coefficient_spec M R₀ R b (W x) (hW x) x (hmW x)
  refine agreeAt_of_inj r s X (fun x : Sp R ↦ Localization.Away (f x)) (fun x ↦ IsScalarTower.toAlgHom R₀ R _)
    (eq_of_loc_away R f hf) fun x X' φ' hX' ↦ ?_
  obtain ⟨UW, φW, hUW⟩ := Obj.exists_isPullBy U (coefSpecMap (hW x) R₀)
  obtain ⟨δW⟩ := hgen x UW φW hUW
  have h1 : X'.IsPullBy U (spMap (g x : _ →+* _) ≫ coefSpecMap (hW x) R₀) (φ' ≫ φ) := by
    rw [hg x]; exact hX'.comp hφ
  obtain ⟨ψ, hψ, -⟩ := h1.cancel hUW
  obtain ⟨δ', hδ', -⟩ := Obj.IsPullBy.existsUnique_detGen (R := R₀ ⊗[ℤ] Γ(M, W x)) (R' := Localization.Away (f x)) _ hψ δW
  refine agreeAt_of_one r s X' δ' ?_
  rw [r.baseChange _ _ (g x) UW trivial X' trivial ψ δW δ' hψ hδ',
    s.baseChange _ _ (g x) UW trivial X' trivial ψ δW δ' hψ hδ', hmod (W x) (hW x) UW φW hUW δW]

theorem agreeAt_of_unit (hDP : GlobalTheory.Published.DelignePappasModel) (hlev : (∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (𝔠 : FracId F) (N : ℕ), 1 ≤ N →
      ∀ (R : Type) [CommRing R], IsUnit (N : R) → ∀ X : Obj F 𝔠 (Sp R),
        ∃ (R' : Type) (_ : CommRing R') (σ : R →+* R') (X' : Obj F 𝔠 (Sp R')) (φ : X'.A.left ⟶ X.A.left),
          σ.FaithfullyFlat ∧ X'.IsPullBy X (spMap σ) φ ∧ Nonempty (X'.Level N))) (r s : Rule (trivialObjectCondition 𝔠) R₀ k)
    (hrap : ∀ (R : Type) [CommRing R] [Algebra R₀ R] (X : Obj F 𝔠 (Sp R)), X.IsRapoport → r.AgreeAt s X)
    (N : ℕ) (hN : 3 ≤ N) {R : Type} [CommRing R] [Algebra R₀ R] (hu : IsUnit (N : R)) (X : Obj F 𝔠 (Sp R)) :
    r.AgreeAt s X := by
  obtain ⟨R', _, σ, X', φ, hff, hX', ⟨α⟩⟩ := hlev F 𝔠 N (by omega) R hu X
  letI : Algebra R₀ R' := (σ.comp (algebraMap R₀ R)).toAlgebra
  let σ' : R →ₐ[R₀] R' := { σ with commutes' := fun _ ↦ rfl }
  refine agreeAt_of_inj r s X (fun _ : Unit ↦ R') (fun _ ↦ σ') (fun x y h ↦ hff.injective (h ()))
    fun _ X'' φ'' hX'' ↦ ?_
  have h2 : X''.IsPullBy X (𝟙 _ ≫ spMap σ) φ'' := by rw [Category.id_comp]; exact hX''
  obtain ⟨ψ, hψ, -⟩ := h2.cancel hX'
  obtain ⟨α'', -⟩ := hψ.exists_level α
  exact agreeAt_of_level hDP r s hrap N hN (by simpa using hu.map σ) X'' α''

theorem agreeAt_all (hDP : GlobalTheory.Published.DelignePappasModel) (hlev : (∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (𝔠 : FracId F) (N : ℕ), 1 ≤ N →
      ∀ (R : Type) [CommRing R], IsUnit (N : R) → ∀ X : Obj F 𝔠 (Sp R),
        ∃ (R' : Type) (_ : CommRing R') (σ : R →+* R') (X' : Obj F 𝔠 (Sp R')) (φ : X'.A.left ⟶ X.A.left),
          σ.FaithfullyFlat ∧ X'.IsPullBy X (spMap σ) φ ∧ Nonempty (X'.Level N))) (r s : Rule (trivialObjectCondition 𝔠) R₀ k)
    (hrap : ∀ (R : Type) [CommRing R] [Algebra R₀ R] (X : Obj F 𝔠 (Sp R)), X.IsRapoport → r.AgreeAt s X)
    {R : Type} [CommRing R] [Algebra R₀ R] (X : Obj F 𝔠 (Sp R)) : r.AgreeAt s X := by
  refine agreeAt_of_inj r s X (fun b : Bool ↦ Localization.Away (if b then (2 : R) else 3))
    (fun b ↦ IsScalarTower.toAlgHom R₀ R _) (fun x y h ↦ eq_of_loc_two_three R x y (h true) (h false)) fun b X' φ' hX' ↦ ?_
  cases b
  · have h3 : IsUnit (algebraMap R (Localization.Away (3 : R)) 3) := IsLocalization.Away.algebraMap_isUnit 3
    have h3' : IsUnit ((3 : ℕ) : Localization.Away (3 : R)) := by
      rw [Nat.cast_ofNat, ← map_ofNat (algebraMap R (Localization.Away (3 : R))) 3]; exact h3
    exact agreeAt_of_unit hDP hlev r s hrap 3 le_rfl h3' X'
  · have h2 : IsUnit (algebraMap R (Localization.Away (2 : R)) 2) := IsLocalization.Away.algebraMap_isUnit 2
    have h4 : ((4 : ℕ) : Localization.Away (2 : R)) = algebraMap R _ 2 * algebraMap R _ 2 := by
      rw [← map_mul, show (2 : R) * 2 = 4 by norm_num, map_ofNat, Nat.cast_ofNat]
    exact agreeAt_of_unit hDP hlev r s hrap 4 (by norm_num) (by rw [h4]; exact h2.mul h2) X'

end GlobalTheory.RealMult.QUniq

theorem GlobalTheory.RealMult.rule_eq_of_agree_rapoport_of_level (hlev : (∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (𝔠 : FracId F) (N : ℕ), 1 ≤ N →
      ∀ (R : Type) [CommRing R], IsUnit (N : R) → ∀ X : Obj F 𝔠 (Sp R),
        ∃ (R' : Type) (_ : CommRing R') (σ : R →+* R') (X' : Obj F 𝔠 (Sp R')) (φ : X'.A.left ⟶ X.A.left),
          σ.FaithfullyFlat ∧ X'.IsPullBy X (spMap σ) φ ∧ Nonempty (X'.Level N))) : GlobalTheory.Published.DelignePappasModel → ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (𝔠 : FracId F) (R₀ : Type) [CommRing R₀]
  (k : ℕ) (r s : Rule (trivialObjectCondition 𝔠) R₀ k),
  (∀ (R : Type) [CommRing R] [Algebra R₀ R] (X : Obj F 𝔠 (Sp R)), X.IsRapoport → ∀ δ : X.DetGen,
    r.val R X trivial δ = s.val R X trivial δ) → r = s := by
  intro hDP F _ _ _ 𝔠 R₀ _ k r s h
  apply Rule.ext
  funext R _ _ X hX δ
  exact QUniq.agreeAt_all hDP hlev r s h X δ
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SecondChernFormPullback
section
set_option autoImplicit false

noncomputable section

open Set Matrix Filter Topology
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory.HermFrame
open GlobalTheory.GoodMetric (coordVec chernPoly curvPoly)
open scoped ContDiff ComplexOrder ComplexConjugate

namespace GlobalTheory.SecondChernPull

section Coordinates

open GlobalTheory.CxForm MvPolynomial

variable {n m : ℕ} {r : Type} [Fintype r] [DecidableEq r]

def subst (L : V n →L[ℂ] V m) : MvPolynomial (Fin m × Fin m) ℂ →ₐ[ℂ] MvPolynomial (Fin n × Fin n) ℂ :=
  aeval fun x : Fin m × Fin m => ∑ a, ∑ b, C (L (coordVec a) x.1 * conj (L (coordVec b) x.2)) * X (a, b)

theorem coe_aeval_sym_subst (L : V n →L[ℂ] V m) (q : MvPolynomial (Fin m × Fin m) ℂ) :
    ((aeval sym (subst L q) : Ev n) : Alt n) = pull L ((aeval sym q : Ev m) : Alt m) := by
  have h : ((Subalgebra.center ℂ (Alt n)).val.comp ((aeval sym).comp (subst L))) =
      (pull L).comp ((Subalgebra.center ℂ (Alt m)).val.comp (aeval sym)) := by
    refine MvPolynomial.algHom_ext fun x => ?_
    simp only [AlgHom.comp_apply, subst, aeval_X, map_sum, map_mul, aeval_C, Subalgebra.coe_val, sym,
      (pull_dz _ _).1, (pull_dz _ _).2, Finset.sum_mul_sum, smul_mul_smul_comm]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    rw [Subalgebra.coe_algebraMap, Subalgebra.coe_algebraMap, ← map_mul, ← Algebra.smul_def]
  exact DFunLike.congr_fun h q

theorem curv_eq_sum_sum {H : V m → Matrix r r ℂ} {y : V m} (h2 : MContDiffAt 2 H y) (hu : IsUnit (H y).det)
    (ξ η : V m) : curv H y ξ η = ∑ c, ∑ d, (ξ c * conj (η d)) • curv H y (coordVec c) (coordVec d) := by
  have e := GlobalTheory.ChernPull.curv_comp (H := H) (φ := fun x => x) (v := y) analyticAt_id h2 hu ξ η
  rw [fderiv_fun_id] at e
  refine e.trans (Finset.sum_congr rfl fun c _ => ?_)
  rw [GlobalTheory.ChernPull.curv_eq_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [smul_smul]; rfl

theorem curvPoly_comp {H : V m → Matrix r r ℂ} {φ : V n → V m} {v : V n} (hφ : AnalyticAt ℂ φ v)
    (h2 : MContDiffAt 2 H (φ v)) (hu : IsUnit (H (φ v)).det) :
    curvPoly (fun x => H (φ x)) v = (curvPoly H (φ v)).map (subst (fderiv ℂ φ v)) := by
  have e (a b : Fin n) := (curv_comp_holo h2 hu hφ.contDiffAt (coordVec a) (coordVec b)).trans
    (curv_eq_sum_sum h2 hu _ _)
  refine Matrix.ext fun i j => ?_
  simp only [curvPoly, Matrix.of_apply, Matrix.map_apply, e, Matrix.sum_apply,
    Matrix.smul_apply, smul_eq_mul, map_sum, map_mul, subst, aeval_X, aeval_C, algebraMap_eq,
    Finset.sum_mul, Finset.mul_sum]
  simp_rw [← Fintype.sum_prod_type']
  let e : Fin n × Fin n × Fin m × Fin m ≃ Fin m × Fin m × Fin n × Fin n :=
    ⟨fun x => (x.2.2.1, x.2.2.2, x.1, x.2.1), fun x => (x.2.2.1, x.2.2.2, x.1, x.2.1), fun _ => rfl, fun _ => rfl⟩
  exact Fintype.sum_equiv e _ _ fun x => by simp only [e, Equiv.coe_fn_mk]; ring

theorem chernAt_comp_holo {H : V m → Matrix r r ℂ} {φ : V n → V m} {v : V n} (hφ : AnalyticAt ℂ φ v)
    (h2 : MContDiffAt 2 H (φ v)) (hu : IsUnit (H (φ v)).det) (j : ℕ) :
    (chernAt (fun w => H (φ w)) v j : Alt n) = pull (fderiv ℂ φ v) (chernAt H (φ v) j : Alt m) := by
  have e : chernPoly (fun x => H (φ x)) v j = subst (fderiv ℂ φ v) (chernPoly H (φ v) j) := by
    unfold chernPoly
    rw [curvPoly_comp hφ h2 hu]
    have hm : -(curvPoly H (φ v)).map (subst (fderiv ℂ φ v)) =
        (-curvPoly H (φ v)).map (subst (fderiv ℂ φ v)).toRingHom := by
      rw [Matrix.map_neg (f := (subst (fderiv ℂ φ v)).toRingHom) (fun a => map_neg _ a)]; rfl
    rw [hm, ← GlobalTheory.ChernPull.charpolyRev_map, Polynomial.coeff_map]
    rfl
  rw [chernAt, chernAt, e, Subalgebra.coe_smul, Subalgebra.coe_smul, map_smul, coe_aeval_sym_subst]

theorem chernAt_reindex {r' : Type} [Fintype r'] [DecidableEq r'] (e : r' ≃ r)
    {G : V n → Matrix r r ℂ} {G' : V n → Matrix r' r' ℂ} {v : V n}
    (he : G' =ᶠ[𝓝 v] fun u => (G u).submatrix e e) (j : ℕ) : chernAt G' v j = chernAt G v j := by
  have e₁ : curvPoly G' v = (curvPoly G v).submatrix e e := by
    ext1 i j
    simp only [curvPoly, Matrix.of_apply, Matrix.submatrix_apply, curv_congr he, curv_submatrix_equiv]
  have e₂ (M : Matrix r r (MvPolynomial (Fin n × Fin n) ℂ)) :
      Matrix.charpolyRev (-M.submatrix e e) = Matrix.charpolyRev (-M) := by
    rw [Matrix.charpolyRev, Matrix.charpolyRev, ← Matrix.det_submatrix_equiv_self e (1 - _)]
    congr 1
    ext1 i j
    simp [Matrix.one_apply]
  rw [chernAt, chernAt, chernPoly, chernPoly, e₁, e₂]

end Coordinates

open CategoryTheory AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxForm GlobalTheory.Points GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.LineForm

variable {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} {D : ℕ}

theorem chern_G_eq (h : IsRegVar p D) {σ : k →+* ℂ} {E : X.Modules} {r : ℕ} {m : Met p σ E r} (H : m.IsCInf)
    (c c' : Chart E r) (x : (h.atlas σ).Pt) (hc : x.pt ∈ ptsIn p σ c.U) (hc' : x.pt ∈ ptsIn p σ c'.U) (j : ℕ) :
    (h.atlas σ).chern (m.G c') j x = (h.atlas σ).chern (m.G c) j x := by
  have e : x.ch.symm x.crd = x.pt := x.ch.left_inv x.2
  refine chernAt_changeFrame _ _ (fun v => c.tr p σ c' (x.ch.symm v)) _
    (((H c _ hc).mContDiffAt x.1.1 x.2).of_le (by norm_cast)) ?_ (fun a b => ?_) ?_ ?_ j
  · erw [e]; exact (isUnit_iff_isUnit_det _).1 (m.posDef c _ hc).isUnit
  · exact GlobalTheory.SCV.analyticAt_of_differentiableOn (AlgChart.holo x.1.1 _ _)
      ((ChartGlue.isOpen_over x.ch (isOpen_ptsIn _)).mem_nhds
        (ChartGlue.mem_over x.ch x.2 (mem_ptsIn_inf.2 ⟨hc', hc⟩)))
  · erw [e]; exact (isUnit_iff_isUnit_det _).1 (c.isUnit_tr c' hc hc')
  · filter_upwards [(ChartGlue.isOpen_over x.ch (isOpen_ptsIn _)).mem_nhds (ChartGlue.mem_over x.ch x.2 hc)] with v hv
    exact m.trans c c' _ hv.2

theorem c2F_eq_chern_of_mem_chart (h : IsRegVar p D) (σ : k →+* ℂ) {E : X.Modules} {m : VMetric p E 2} (H : m.IsCInf)
    (fl : Vert.Flag E 2) (c : Chart E 2) (x : (h.atlas σ).Pt) (hc : x.pt ∈ ptsIn p σ c.U) :
    c2F h σ m fl x = (h.atlas σ).chern ((m.met σ).G c) 2 x := by
  have hS := lineSC_shortExact fl
  have ha := mem_frameAt fl x.pt
  refine Eq.trans ?_ (chern_G_eq h (H σ) c ((frameAt fl x.pt).mid hS) x hc ha 2)
  refine chernAt_reindex (r := Fin 2) (finSumFinEquiv (m := 1) (n := 1)) ?_ 2
  filter_upwards [(ChartGlue.isOpen_over x.ch (isOpen_ptsIn _)).mem_nhds (ChartGlue.mem_over x.ch x.2 ha)] with v hv
  exact Met.gram_frame (S := lineSC fl) (r := 1) (s := 1) (m.met σ) hS _ hv.2

end GlobalTheory.SecondChernPull

end

open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxForm GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.Cartier GlobalTheory.CovTest GlobalTheory.CovTest.SwapLine GlobalTheory.LineForm
open scoped Classical

open scoped ComplexOrder in
open GlobalTheory.Points GlobalTheory.HermFrame Filter Topology in

theorem GlobalTheory.SecondChernPull.c2F_pull_eq_pullF_c2F : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ) (hX : IsRegVar p D) (σ : k →+* ℂ),
    ∀ (Y : Scheme.{0}) (p' : Y ⟶ Sp k) (D' : ℕ) (hY : IsRegVar p' D') (π : Y ⟶ X) (w : π ≫ p = p'),
    ∀ (E : X.Modules) (h : VMetric p E 2) (H : h.IsCInf) (fl : Vert.Flag E 2) (fl' : Vert.Flag ((Scheme.Modules.pullback π).obj E) 2),
    fld _ (c2F hY σ (h.pull π w) fl') = pullF hX hY σ π w (fld _ (c2F hX σ h fl)) := by
  intro k _ X _ p D hX σ Y p' D' hY π w E h H fl fl'
  funext x
  set f : CxPts p' σ → CxPts p σ := PtsOver.map π w _ with hf
  have hm : ∀ z, (f z).1 = z.1 ≫ π := fun _ => rfl
  let x' : (hX.atlas σ).Pt := ⟨(_, f x.pt), ((hX.atlas σ).cover (f x.pt)).choose_spec⟩
  let c : Chart E 2 := (h.met σ).isVB.pick (f x.pt)
  have hc : f x.pt ∈ ptsIn p σ c.U := (h.met σ).isVB.mem_pick _
  change (c2F hY σ (h.pull π w) fl' x : Alt D') =
    pull (fderiv ℂ (x'.ch ∘ f ∘ x.ch.symm) x.crd) (c2F hX σ h fl x' : Alt D)
  rw [SecondChernPull.c2F_eq_chern_of_mem_chart hY σ (H.pull π w) fl' (c.pull (h.met σ).isVB π) x hc,
    SecondChernPull.c2F_eq_chern_of_mem_chart hX σ H fl c x' hc]
  have ho := ChartGlue.isOpen_over x.ch (x'.ch.open_source.preimage (continuous_of_comp hm))
  have hx := ho.mem_nhds (ChartGlue.mem_over x.ch x.2 (show x.pt ∈ f ⁻¹' x'.ch.source from x'.2))
  have hφ : AnalyticAt ℂ (x'.ch ∘ f ∘ x.ch.symm) x.crd :=
    GlobalTheory.SCV.analyticAt_of_differentiableOn (AlgChart.holo_map hm x.1.1 x'.1.1) hx
  have hv : (x'.ch ∘ f ∘ x.ch.symm) x.crd = x'.crd := congrArg (fun z => x'.ch (f z)) (x.ch.left_inv x.2)
  have key := SecondChernPull.chernAt_comp_holo (H := fun v => (h.met σ).G c (x'.ch.symm v)) hφ
    (by rw [hv]; exact ((H σ c _ hc).mContDiffAt x'.1.1 x'.2).of_le (by norm_cast))
    (by rw [hv, x'.ch.left_inv x'.2]; exact (Matrix.isUnit_iff_isUnit_det _).1 ((h.met σ).posDef c _ hc).isUnit) 2
  rw [hv] at key
  refine Eq.trans (congrArg Subtype.val (SecondChernPull.chernAt_reindex (Equiv.refl _) ?_ 2)) key
  filter_upwards [hx, (ChartGlue.isOpen_over x.ch ((isOpen_ptsIn c.U).preimage (continuous_of_comp hm))).mem_nhds
    (ChartGlue.mem_over x.ch x.2 (show x.pt ∈ f ⁻¹' ptsIn p σ c.U from hc))] with v h₁ h₂
  refine ((h.met σ).pull_G π w c h₂.2).trans ?_
  exact congrArg ((h.met σ).G c) (x'.ch.left_inv h₁.2).symm
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemiAbelianActionEqUniversalAtFieldPointsOfThetaStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
open GlobalTheory
attribute [local instance] Over.cartesianMonoidalCategory
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.semiAbelianAction_eq_universal_at_fieldPoints_of_thetaModel : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (C : UCompact Xo c) (X₁ : USetup C) (Y : RatModel X₁.o₁ X₁.Ω₁) (U₀ : Y.Z.Opens) (EE : Y.Lat X₁.S.J) (out : ZHOut X₁.ρ Y U₀ EE) (r : Y.Z ⟶ C.Z), X₁.S.Over₀ Y U₀ → Y.pt ≫ r = X₁.uΩ ≫ C.i → ∀ wi : UWit X₁, ∃ (f : 𝓞 E → (out.G ⟶ out.G)) (ψ : wi.G.left ⟶ out.G.left), (∀ a, IsMonHom (f a)) ∧ IsGrpPullback wi.G out.G Y.pt ψ ∧ (∀ (T : Scheme.{0}) (w : T ⟶ wi.G.left), ∃ x' : T ⟶ pullback X₁.ρ.P.A.hom out.u₀, x' ≫ out.φ = w ≫ ψ ∧ x' ≫ pullback.fst _ _ = w ≫ wi.α) ∧ (∀ (a : 𝓞 E) (e : wi.G ⟶ wi.G), e.left ≫ wi.β = wi.β ≫ (Xo.univ.t.act.act a).left → e.left ≫ ψ = ψ ≫ (f a).left) ∧ ∀ (K : Type) [Field K] (s : Sp K ⟶ Y.Z) (y : Sp K ⟶ Xo.XF c), s ≫ r = y ≫ C.i → ∀ (tK : SAB H (Sp K)), Nonempty (SABMap tK Xo.univ.t (y ≫ pullback.fst _ _)) → ∃ γ : tK.G.left ⟶ out.G.left, IsGrpPullback tK.G out.G s γ ∧ LBIso tK.PP.L (out.L.L.pull γ) ∧ ∀ a, (tK.act.act a).left ≫ γ = γ ≫ (f a).left := by
  first | exact @GlobalTheory.UPoinc.ActField.exists_action_field | exact GlobalTheory.UPoinc.ActField.exists_action_field | (intros; apply GlobalTheory.UPoinc.ActField.exists_action_field <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemiPosAddLogNormSqSectionAddPos
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ChartGlue GlobalTheory.Mix

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Mix.RegLog

variable {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} {σ : k →+* ℂ}

theorem cInfAt_comp {f : CxPts p σ → ℝ} {y : CxPts p σ} (h : CInfAt f y) {G : ℝ → ℝ} {T : Set ℝ}
    (hT : IsOpen T) (hG : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) G T) (hf : ∀ z, f z ∈ T) :
    CInfAt (fun z => G (f z)) y := by
  obtain ⟨W, ι, _, g, F, O, h₁, h₂, h₃, h₄, h₅⟩ := h
  have e : f y = F (fun a => ev p σ W (g a) y) := h₅.eq_of_nhds
  refine ⟨W, ι, inferInstance, g, G ∘ F, O ∩ F ⁻¹' T, h₁, h₄.continuousOn.isOpen_inter_preimage h₂ hT,
    ⟨h₃, show F _ ∈ T from e ▸ hf y⟩, hG.comp (h₄.mono inter_subset_left) fun v hv => hv.2, ?_⟩
  filter_upwards [h₅] with z hz
  simp only [Function.comp_apply, hz]

theorem cInfAt_normSq_ev {W : X.Opens} (g : Γ(X, W)) {y : CxPts p σ} (hy : y ∈ ptsIn p σ W) :
    CInfAt (fun z => ‖ev p σ W g z‖ ^ 2) y :=
  ⟨W, Unit, inferInstance, fun _ => g, fun v => ‖v ()‖ ^ 2, univ, hy, isOpen_univ, trivial,
    ((contDiff_norm_sq ℝ).comp (contDiff_apply ℝ ℂ ())).contDiffOn, EventuallyEq.rfl⟩

theorem cInfAt_nsq {B : LB X} (φ : Weight p σ B) (hφ : φ.IsCInf) (s : B.Sec) (y : CxPts p σ) :
    CInfAt (φ.nsq (secVal p σ s)) y := by
  have hi := mem_pick φ.isLB y
  have h := (cInfAt_normSq_ev (s.f (pick φ.isLB y)) hi).comp₂ (hφ _ y hi)
    (G := fun x => x.1 * Real.exp (-x.2)) (contDiff_fst.mul (Real.contDiff_exp.comp contDiff_snd.neg))
  refine h.congr ?_
  filter_upwards [(isOpen_ptsIn (p := p) (σ := σ) _).mem_nhds hi] with z hz
  exact φ.nsq_eq (secVal_mem s) hz

end GlobalTheory.Mix.RegLog

open GlobalTheory.Mix.RegLog in

theorem GlobalTheory.Mix.semiPosReg_addFn_log_nsq : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k) (σ : k →+* ℂ) (D : ℕ) (N : MLine p σ), N.φ.SemiPosReg D → ∀ (t : N.B.Sec) (δ : ℝ), 0 < δ → (∀ y, CInfAt (fun y => Real.log (N.φ.nsq (secVal p σ t) y + δ)) y) ∧ (N.φ.addFn fun y => Real.log (N.φ.nsq (secVal p σ t) y + δ)).SemiPosReg D := by
  intro k _ X p σ D N hN t δ hδ
  have hC : ∀ y, CInfAt (fun y => Real.log (N.φ.nsq (secVal p σ t) y + δ)) y := fun y =>
    cInfAt_comp ((cInfAt_nsq N.φ N.cInf t y).add (cInfAt_const δ y)) isOpen_compl_singleton
      Real.contDiffOn_log fun z => (add_pos_of_nonneg_of_pos (N.φ.nsq_nonneg _ z) hδ).ne'
  refine ⟨hC, ?_⟩
  intro i c y hy ξ
  have ho := isOpen_over c.e (isOpen_ptsIn (p := p) (σ := σ) (N.B.U i))
  have hm := mem_over c.e hy.1 hy.2
  have hf : ContDiffAt ℂ 2 (ev p σ (N.B.U i) (t.f i) ∘ c.e.symm) (c.e y) :=
    ReciprocityTheory.L2DbarEstimates.Y.contDiffAt_two_of_holo ho (c.holo _ (t.f i)) hm
  have hψ : ContDiffAt ℝ 2 (fun v => N.φ.φ i (c.e.symm v)) (c.e y) := N.cInf.contDiffAt c hy.1 hy.2
  have hψ' : ContDiffAt ℝ 2 (fun v => 1 * N.φ.φ i (c.e.symm v) + Real.log δ) (c.e y) :=
    (contDiffAt_const.mul hψ).add contDiffAt_const
  let w : Fin 2 → ReciprocityTheory.L2DbarEstimates.V D → ℝ := ![fun v => Complex.normSq ((ev p σ (N.B.U i) (t.f i) ∘ c.e.symm) v),
    fun v => Real.exp (1 * N.φ.φ i (c.e.symm v) + Real.log δ)]
  have hu : ∀ j, ContDiffAt ℝ 2 (w j) (c.e y) := by
    intro j; fin_cases j
    · exact ReciprocityTheory.L2DbarEstimates.contDiffAt_normSq_comp hf
    · exact Real.contDiff_exp.contDiffAt.comp _ hψ'
  have hl : ∀ j, ReciprocityTheory.L2DbarEstimates.LogPshAt D (w j) (c.e y) := by
    intro j; fin_cases j
    · exact ReciprocityTheory.L2DbarEstimates.logPshAt_normSq hf
    · refine ReciprocityTheory.L2DbarEstimates.logPshAt_exp hψ' fun ζ => ?_
      rw [ReciprocityTheory.L2DbarEstimates.Y.leviV_const_mul hψ 1 (Real.log δ) ζ, Complex.ofReal_one, one_mul]
      exact hN i c y hy ζ
  have hpos : 0 < ∑ j, w j (c.e y) := by
    simp only [Fin.sum_univ_two, w, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
    exact add_pos_of_nonneg_of_pos (Complex.normSq_nonneg _) (Real.exp_pos _)
  have key := ReciprocityTheory.L2DbarEstimates.leviV_log_sum_nonneg hu hl hpos ξ
  have e : (fun v => (((N.φ.addFn fun y => Real.log (N.φ.nsq (secVal p σ t) y + δ)).φ i (c.e.symm v) : ℝ) : ℂ))
      =ᶠ[𝓝 (c.e y)] fun v => ((Real.log (∑ j, w j v) : ℝ) : ℂ) := by
    filter_upwards [ho.mem_nhds hm] with v hv
    have hz : c.e.symm v ∈ ptsIn p σ (N.B.U i) := hv.2
    congr 1
    simp only [Weight.addFn, N.φ.nsq_eq (secVal_mem t) hz, Fin.sum_univ_two, w, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.head_cons, Function.comp_apply, secVal_apply]
    set a := N.φ.φ i (c.e.symm v)
    set b := ev p σ (N.B.U i) (t.f i) (c.e.symm v)
    have h1 : ‖b‖ ^ 2 * Real.exp (-a) + δ = Real.exp (-a) * (Complex.normSq b + Real.exp (1 * a + Real.log δ)) := by
      rw [Complex.normSq_eq_norm_sq, Real.exp_add, Real.exp_log hδ, one_mul, Real.exp_neg]
      field_simp
    rw [h1, Real.log_mul (Real.exp_pos _).ne' (add_pos_of_nonneg_of_pos (Complex.normSq_nonneg _)
      (Real.exp_pos _)).ne', Real.log_exp]
    ring
  rw [ReciprocityTheory.L2DbarEstimates.leviV_congr e]
  exact key
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemiPositivePullbackGenericallyEtaleStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.semiPositive_pullback_generically_etale : ∀ (k : Type) [CommRing k] (X Y : Scheme.{0}) [IsIntegral X] [IsIntegral Y] (p : X ⟶ Sp k) (q : Y ⟶ Sp k) (D : ℕ), IsArithVar p D → IsArithVar q D → ∀ (π : Y ⟶ X) (hπ : π ≫ p = q) (V : Y.Opens), (V : Set Y).Nonempty → Etale (V.ι ≫ π) → ∀ L : HermLB p, L.SemiPos D → (L.pull π hπ).SemiPos D := by
  first | exact @GlobalTheory.SemiPosUp.semiPos_pull_of_etale | exact GlobalTheory.SemiPosUp.semiPos_pull_of_etale | (intros; apply GlobalTheory.SemiPosUp.semiPos_pull_of_etale <;> assumption)
end

