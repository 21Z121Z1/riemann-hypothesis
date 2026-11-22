import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0030
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2446
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2813
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2810
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0077
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2665
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2809
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0079
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0084
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0076
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0082
import Development.AbelianVarietyTheory.Statements.TorsionEndomorphisms.EndDeterminedOnTorsion
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0007
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsPowerSectionOfChartFunctions
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0105
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0573
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ThetaConstantsIntegralUnitOfClosedFibreNonvanish
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0029
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDatNeZero
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsLeadOfUnif
import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle0002
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FamMod
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2749
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2709
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.TorsionFrameIsUnitAlongSection
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2838
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0046
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UniformisationTrivialisationsCorrespond
import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle0003
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0060
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0208
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ThetaGen
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1726
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2783
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1901
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1949
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1803
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1910
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2621
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2676
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2811
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2727

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRuleUnitObjOfCovers
section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
  TensorProduct NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.RealMult.RuleDescend

theorem exists_square {R R₁ R' : Type} [CommRing R] [CommRing R₁] [CommRing R'] (σ : R →+* R₁)
    (hσ : σ.FaithfullyFlat) (τ : R →+* R') :
    ∃ (T : Type) (_ : CommRing T) (a : R₁ →+* T) (b : R' →+* T), a.comp σ = b.comp τ ∧ Function.Injective b := by
  letI := σ.toAlgebra
  letI := τ.toAlgebra
  haveI : Module.FaithfullyFlat R R₁ := hσ
  refine ⟨R₁ ⊗[R] R', inferInstance, Algebra.TensorProduct.includeLeftRingHom,
    (Algebra.TensorProduct.includeRight : R' →ₐ[R] R₁ ⊗[R] R').toRingHom,
    Algebra.TensorProduct.includeLeftRingHom_comp_algebraMap, ?_⟩
  exact Module.FaithfullyFlat.tensorProduct_mk_injective (A := R) (B := R₁) R'

theorem exists_equaliser {R R₁ : Type} [CommRing R] [CommRing R₁] (σ : R →+* R₁) (hσ : σ.FaithfullyFlat) :
    ∃ (T : Type) (_ : CommRing T) (a b : R₁ →+* T), a.comp σ = b.comp σ ∧ ∀ x, a x = b x → ∃ y, σ y = x := by
  letI := σ.toAlgebra
  haveI : Module.FaithfullyFlat R R₁ := hσ
  refine ⟨R₁ ⊗[R] R₁, inferInstance, Algebra.TensorProduct.includeLeftRingHom,
    (Algebra.TensorProduct.includeRight : R₁ →ₐ[R] R₁ ⊗[R] R₁).toRingHom,
    Algebra.TensorProduct.includeLeftRingHom_comp_algebraMap, fun x hx ↦ ?_⟩
  refine (Algebra.IsEffective.of_faithfullyFlat R R₁ x).1 ?_
  have : x ⊗ₜ[R] (1 : R₁) = (1 : R₁) ⊗ₜ[R] x := hx
  simp [this]

theorem spMap_comp {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap (g.comp f) = spMap g ≫ spMap f := by
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]

theorem dualMapR_comp {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    Chart.dualMapR (g.comp f) = (Chart.dualMapR g).comp (Chart.dualMapR f) := by
  refine RingHom.ext fun r ↦ TrivSqZeroExt.ext ?_ ?_ <;> simp [Chart.dualMapR]

variable {F : Type} [Field F] [NumberField F] {𝔠 : FracId F}
  {R R' R'' : Type} [CommRing R] [CommRing R'] [CommRing R'']

theorem lieCorr_comp {σ : R →+* R'} {τ : R' →+* R''} {X : Obj F 𝔠 (Sp R)} {X' : Obj F 𝔠 (Sp R')}
    {X'' : Obj F 𝔠 (Sp R'')} {φ : X'.A.left ⟶ X.A.left} {ψ : X''.A.left ⟶ X'.A.left}
    {v : X.Lie} {v' : X'.Lie} {v'' : X''.Lie} (h : Obj.LieCorr σ φ v v') (h' : Obj.LieCorr τ ψ v' v'') :
    Obj.LieCorr (τ.comp σ) (ψ ≫ φ) v v'' := by
  unfold Obj.LieCorr at *
  rw [← Category.assoc, h', Category.assoc, h, dualMapR_comp, spMap_comp, Category.assoc]

theorem existsUnique_lieCorr {σ : R →+* R'} {X : Obj F 𝔠 (Sp R)} {X' : Obj F 𝔠 (Sp R')}
    {φ : X'.A.left ⟶ X.A.left} (h : X'.IsPullBy X (spMap σ) φ) (v : X.Lie) : ∃! v', Obj.LieCorr σ φ v v' := by
  letI := σ.toAlgebra
  obtain ⟨e, he, -⟩ := Obj.exists_lieEquiv (R' := R') h
  exact ⟨_, (he v _).2 rfl, fun w hw ↦ (he v w).1 hw⟩

theorem isPullBy_comp {σ : R →+* R'} {τ : R' →+* R''} {X : Obj F 𝔠 (Sp R)} {X' : Obj F 𝔠 (Sp R')}
    {X'' : Obj F 𝔠 (Sp R'')} {φ : X'.A.left ⟶ X.A.left} {ψ : X''.A.left ⟶ X'.A.left}
    (h : X'.IsPullBy X (spMap σ) φ) (h' : X''.IsPullBy X' (spMap τ) ψ) :
    X''.IsPullBy X (spMap (τ.comp σ)) (ψ ≫ φ) := by
  rw [spMap_comp]; exact h'.comp h

theorem detCorr_comp {σ : R →+* R'} {τ : R' →+* R''} {X : Obj F 𝔠 (Sp R)} {X' : Obj F 𝔠 (Sp R')}
    {X'' : Obj F 𝔠 (Sp R'')} {φ : X'.A.left ⟶ X.A.left} {ψ : X''.A.left ⟶ X'.A.left}
    (h : X'.IsPullBy X (spMap σ) φ) (h' : X''.IsPullBy X' (spMap τ) ψ)
    {δ : X.DetOmega} {δ' : X'.DetOmega} {δ'' : X''.DetOmega}
    (hd : Obj.DetCorr σ φ δ δ') (hd' : Obj.DetCorr τ ψ δ' δ'') : Obj.DetCorr (τ.comp σ) (ψ ≫ φ) δ δ'' := by
  intro v v'' hv
  choose v' hv' using fun i ↦ (existsUnique_lieCorr h (v i)).exists
  have : ∀ i, Obj.LieCorr τ ψ (v' i) (v'' i) := fun i ↦ by
    obtain ⟨w, hw⟩ := (existsUnique_lieCorr h' (v' i)).exists
    rwa [(existsUnique_lieCorr (isPullBy_comp h h') (v i)).unique (hv i) (lieCorr_comp (hv' i) hw)]
  rw [hd' v' v'' this, hd v v' hv', RingHom.comp_apply]

theorem isUnit_of_eq_smul {X : Obj F 𝔠 (Sp R)} (δ δ' : X.DetGen) (c : R) (h : δ'.1 = c • δ.1) : IsUnit c := by
  haveI := X.invertible_detOmega
  obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.1 (δ'.2.ge Submodule.mem_top : δ.1 ∈ Submodule.span R {δ'.1})
  refine IsUnit.of_mul_eq_one_right a (eq_of_smul_eq_smul (α := X.DetOmega) fun m ↦ ?_)
  obtain ⟨b, rfl⟩ := Submodule.mem_span_singleton.1 (δ.2.ge Submodule.mem_top : m ∈ Submodule.span R {δ.1})
  rw [smul_comm, mul_smul, ← h, ha, one_smul]

variable {N : ℕ} {R₀ : Type} [CommRing R₀] {k : ℕ}

theorem levObj_of_isPullBy {σ : R →+* R'} {X : Obj F 𝔠 (Sp R)} {X' : Obj F 𝔠 (Sp R')}
    {φ : X'.A.left ⟶ X.A.left} (h : X'.IsPullBy X (spMap σ) φ) (hX : levObj 𝔠 N R X) : levObj 𝔠 N R' X' := by
  obtain ⟨hu, ⟨α⟩⟩ := hX
  obtain ⟨α', -⟩ := h.exists_level α
  exact ⟨by simpa using hu.map σ, ⟨α'⟩⟩

def IsVal (r : Rule (levObj 𝔠 N) R₀ k) [Algebra R₀ R] (X : Obj F 𝔠 (Sp R)) (δ : X.DetGen) (x : R) : Prop :=
  ∀ (R' : Type) [CommRing R'] [Algebra R₀ R'] (σ : R →ₐ[R₀] R') (X' : Obj F 𝔠 (Sp R')) (h' : levObj 𝔠 N R' X')
    (φ : X'.A.left ⟶ X.A.left) (δ' : X'.DetGen), X'.IsPullBy X (spMap (σ : R →+* R')) φ →
    Obj.DetCorr (σ : R →+* R') φ δ.1 δ'.1 → r.val R' X' h' δ' = σ x

theorem val_eq_of_square (r : Rule (levObj 𝔠 N) R₀ k) {R₁ R₂ T : Type} [CommRing R₁] [CommRing R₂] [CommRing T]
    [Algebra R₀ R] [Algebra R₀ R₁] [Algebra R₀ R₂] (σ : R →ₐ[R₀] R₁) (τ : R →ₐ[R₀] R₂)
    (a : R₁ →+* T) (b : R₂ →+* T) (hab : a.comp (σ : R →+* R₁) = b.comp (τ : R →+* R₂))
    {X : Obj F 𝔠 (Sp R)} {X₁ : Obj F 𝔠 (Sp R₁)} {X₂ : Obj F 𝔠 (Sp R₂)}
    {φ₁ : X₁.A.left ⟶ X.A.left} {φ₂ : X₂.A.left ⟶ X.A.left}
    (h₁ : X₁.IsPullBy X (spMap (σ : R →+* R₁)) φ₁) (h₂ : X₂.IsPullBy X (spMap (τ : R →+* R₂)) φ₂)
    (l₁ : levObj 𝔠 N R₁ X₁) (l₂ : levObj 𝔠 N R₂ X₂) {δ : X.DetGen} {δ₁ : X₁.DetGen} {δ₂ : X₂.DetGen}
    (d₁ : Obj.DetCorr (σ : R →+* R₁) φ₁ δ.1 δ₁.1) (d₂ : Obj.DetCorr (τ : R →+* R₂) φ₂ δ.1 δ₂.1) :
    a (r.val R₁ X₁ l₁ δ₁) = b (r.val R₂ X₂ l₂ δ₂) := by
  letI : Algebra R₀ T := (a.comp (algebraMap R₀ R₁)).toAlgebra
  let a' : R₁ →ₐ[R₀] T := { a with commutes' := fun _ ↦ rfl }
  let b' : R₂ →ₐ[R₀] T := { b with
    commutes' := fun x ↦ by
      have := RingHom.congr_fun hab (algebraMap R₀ R x)
      simp only [RingHom.comp_apply, RingHom.coe_coe, AlgHom.commutes] at this
      exact this.symm }
  obtain ⟨Y, ψ₁, k₁⟩ := X₁.exists_isPullBy (spMap a)
  have hY := isPullBy_comp h₁ k₁
  have hY' := hY
  rw [hab, spMap_comp] at hY'
  obtain ⟨ψ₂, k₂, hψ⟩ := hY'.cancel h₂
  obtain ⟨ε₁, e₁⟩ := (k₁.existsUnique_detGen a δ₁).exists
  obtain ⟨ε₂, e₂⟩ := (k₂.existsUnique_detGen b δ₂).exists
  have f₂ := detCorr_comp h₂ k₂ d₂ e₂
  rw [hψ, ← hab] at f₂
  obtain rfl : ε₁ = ε₂ := (hY.existsUnique_detGen _ δ).unique (detCorr_comp h₁ k₁ d₁ e₁) f₂
  have lY := levObj_of_isPullBy k₁ l₁
  exact (r.baseChange R₁ T a' X₁ l₁ Y lY ψ₁ δ₁ ε₁ k₁ e₁).symm.trans (r.baseChange R₂ T b' X₂ l₂ Y lY ψ₂ δ₂ ε₁ k₂ e₂)

variable (𝔠 N) in

def HasLevelCovers : Prop :=
  ∀ (R : Type) [CommRing R], IsUnit (N : R) → ∀ X : Obj F 𝔠 (Sp R),
    ∃ (R' : Type) (_ : CommRing R') (σ : R →+* R') (X' : Obj F 𝔠 (Sp R')) (φ : X'.A.left ⟶ X.A.left),
      σ.FaithfullyFlat ∧ X'.IsPullBy X (spMap σ) φ ∧ Nonempty (X'.Level N)

theorem exists_cover (hN : HasLevelCovers 𝔠 N) [Algebra R₀ R] (hu : IsUnit (N : R)) (X : Obj F 𝔠 (Sp R)) :
    ∃ (R₁ : Type) (_ : CommRing R₁) (_ : Algebra R₀ R₁) (σ : R →ₐ[R₀] R₁) (X₁ : Obj F 𝔠 (Sp R₁))
      (φ : X₁.A.left ⟶ X.A.left), (σ : R →+* R₁).FaithfullyFlat ∧ X₁.IsPullBy X (spMap (σ : R →+* R₁)) φ ∧
      levObj 𝔠 N R₁ X₁ := by
  obtain ⟨R₁, _, σ, X₁, φ, hσ, hp, hl⟩ := hN R hu X
  letI : Algebra R₀ R₁ := (σ.comp (algebraMap R₀ R)).toAlgebra
  exact ⟨R₁, inferInstance, inferInstance, { σ with commutes' := fun _ ↦ rfl }, X₁, φ, hσ, hp,
    by simpa using hu.map σ, hl⟩

theorem existsUnique_isVal (hN : HasLevelCovers 𝔠 N) (r : Rule (levObj 𝔠 N) R₀ k) [Algebra R₀ R]
    (hu : IsUnit (N : R)) (X : Obj F 𝔠 (Sp R)) (δ : X.DetGen) : ∃! x, IsVal r X δ x := by
  obtain ⟨R₁, _, _, σ, X₁, φ, hσ, hp, hl⟩ := exists_cover (R₀ := R₀) hN hu X
  obtain ⟨δ₁, d₁⟩ := (hp.existsUnique_detGen _ δ).exists
  obtain ⟨T, _, a, b, hab, hT⟩ := exists_equaliser _ hσ
  obtain ⟨x, hx⟩ := hT _ (val_eq_of_square r σ σ a b hab hp hp hl hl d₁ d₁)
  refine ⟨x, fun R' _ _ τ X' h' φ' δ' hp' d' ↦ ?_, fun y hy ↦ hσ.injective ?_⟩
  · obtain ⟨T', _, a', b', hab', hb'⟩ := exists_square _ hσ (τ : R →+* R')
    refine hb' ?_
    rw [← val_eq_of_square r σ τ a' b' hab' hp hp' hl h' d₁ d', ← hx]
    exact RingHom.congr_fun hab' x
  · rw [hx]; exact (hy R₁ σ X₁ hl φ δ₁ hp d₁).symm

theorem IsVal.baseChange {r : Rule (levObj 𝔠 N) R₀ k} [Algebra R₀ R] [Algebra R₀ R'] (σ : R →ₐ[R₀] R')
    {X : Obj F 𝔠 (Sp R)} {X' : Obj F 𝔠 (Sp R')} {φ : X'.A.left ⟶ X.A.left} {δ : X.DetGen} {δ' : X'.DetGen}
    (h : X'.IsPullBy X (spMap (σ : R →+* R')) φ) (d : Obj.DetCorr (σ : R →+* R') φ δ.1 δ'.1) {x : R}
    (hx : IsVal r X δ x) : IsVal r X' δ' (σ x) := fun R'' _ _ τ X'' h'' ψ δ'' hp d' ↦
  hx R'' (τ.comp σ) X'' h'' (ψ ≫ φ) δ'' (isPullBy_comp h hp) (detCorr_comp h hp d d')

theorem IsVal.homog {r : Rule (levObj 𝔠 N) R₀ k} [Algebra R₀ R] {X : Obj F 𝔠 (Sp R)} {δ δ' : X.DetGen} {c : R}
    (hc : δ'.1 = c • δ.1) {x : R} (hx : IsVal r X δ' x) : IsVal r X δ (c ^ k * x) := by
  intro R' _ _ σ X' h' φ ε hp d
  have hu : IsUnit (σ c) := (isUnit_of_eq_smul δ δ' c hc).map σ
  let ε' : X'.DetGen := ⟨σ c • ε.1, (Submodule.span_singleton_smul_eq hu _).trans ε.2⟩
  have d' : Obj.DetCorr (σ : R →+* R') φ δ'.1 ε'.1 := fun v v' hv ↦ by
    change σ c • ε.1 v' = _
    rw [d v v' hv, hc]
    simp
  rw [← r.homog R' X' h' ε ε' (σ c) rfl, hx R' σ X' h' φ ε' hp d', map_mul, map_pow]

def descend (hN : HasLevelCovers 𝔠 N) (r : Rule (levObj 𝔠 N) R₀ k) : Rule (unitObj 𝔠 N) R₀ k where
  val _ _ _ X h δ := (existsUnique_isVal hN r h X δ).exists.choose
  homog _ _ _ X h δ δ' _ hc := (existsUnique_isVal hN r h X δ).unique
    ((existsUnique_isVal hN r h X δ').exists.choose_spec.homog hc) (existsUnique_isVal hN r h X δ).exists.choose_spec
  baseChange _ _ _ _ _ _ σ X h X' h' _ δ δ' hp d := (existsUnique_isVal hN r h' X' δ').unique
    (existsUnique_isVal hN r h' X' δ').exists.choose_spec
    ((existsUnique_isVal hN r h X δ).exists.choose_spec.baseChange σ hp d)

theorem descend_val_eq (hN : HasLevelCovers 𝔠 N) (r : Rule (levObj 𝔠 N) R₀ k) [Algebra R₀ R]
    (X : Obj F 𝔠 (Sp R)) (h : IsUnit (N : R)) (δ : X.DetGen) {x : R} (hx : IsVal r X δ x) :
    (descend hN r).val R X h δ = x :=
  (existsUnique_isVal hN r h X δ).unique (existsUnique_isVal hN r h X δ).exists.choose_spec hx

theorem exists_rule_unitObj_of_covers
    (H : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (𝔠 : FracId F) (N : ℕ), 1 ≤ N →
    ∀ (R : Type) [CommRing R], IsUnit (N : R) → ∀ X : Obj F 𝔠 (Sp R),
      ∃ (R' : Type) (_ : CommRing R') (σ : R →+* R') (X' : Obj F 𝔠 (Sp R')) (φ : X'.A.left ⟶ X.A.left),
        σ.FaithfullyFlat ∧ X'.IsPullBy X (spMap σ) φ ∧ Nonempty (X'.Level N)) :
    ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (𝔠 : FracId F) (N : ℕ), 1 ≤ N →
  ∀ (R₀ : Type) [CommRing R₀] (k : ℕ) (r₀ : Rule (rapObj 𝔠) R₀ k) (r : Rule (levObj 𝔠 N) R₀ k),
  (∀ (R : Type) [CommRing R] [Algebra R₀ R] (X : Obj F 𝔠 (Sp R)) (h : levObj 𝔠 N R X)
    (hX : X.IsRapoport) (δ : X.DetGen), r.val R X h δ = r₀.val R X hX δ) →
  ∃ r' : Rule (unitObj 𝔠 N) R₀ k,
    (∀ (R : Type) [CommRing R] [Algebra R₀ R] (X : Obj F 𝔠 (Sp R)) (h : levObj 𝔠 N R X) (δ : X.DetGen),
      r'.val R X h.1 δ = r.val R X h δ) ∧
    ∀ (R : Type) [CommRing R] [Algebra R₀ R] (X : Obj F 𝔠 (Sp R)) (h : IsUnit ((N : ℕ) : R))
      (hX : X.IsRapoport) (δ : X.DetGen), r'.val R X h δ = r₀.val R X hX δ := by
  intro F _ _ _ 𝔠 N hN₁ R₀ _ k r₀ r hr
  have hN : HasLevelCovers 𝔠 N := H F 𝔠 N hN₁
  refine ⟨descend hN r, fun R _ _ X h δ ↦ descend_val_eq hN r X h.1 δ ?_,
    fun R _ _ X h hX δ ↦ descend_val_eq hN r X h δ ?_⟩
  · exact fun R' _ _ σ X' h' φ δ' hp d ↦ r.baseChange R R' σ X h X' h' φ δ δ' hp d
  · intro R' _ _ σ X' h' φ δ' hp d
    have hX' := hp.isRapoport _ hX
    rw [hr R' X' h' hX' δ']
    exact r₀.baseChange R R' σ X hX X' hX' φ δ δ' hp d

end GlobalTheory.RealMult.RuleDescend
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSectionExpansionWeightZeroCoefficientStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_section_expansion_weightZero_coefficient : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R →
    ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G]
      [IsCommMonObj G], IsSemiAbelian G → ∀ U : Unif (maximalIdeal R) D A G, ∀ k : ℕ, 1 ≤ k →
      ∀ σ : D.toPre.SecB k 0, ∃ (s : H0 U.LG.L k) (f : ∀ α : D.toPre.X, D.toPre.SecB k α), f 0 = σ ∧
        (∀ α, α ≠ 0 → ∀ j : Fin 4 → D.toPre.P.L.ι, ((U.gt 0).pG.left.app _).hom ((f α).f j) = 0) ∧
        U.toUnifPre.ExpandsAt 0 k s f := by
  first | exact @GlobalTheory.Mum.LeadZero.exists_expandsAt_lead_zero | exact GlobalTheory.Mum.LeadZero.exists_expandsAt_lead_zero | (intros; apply GlobalTheory.Mum.LeadZero.exists_expandsAt_lead_zero <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSectionNonvanishingOverClosedPointFibreStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_section_nonvanishing_over_closed_point_fibre : ∀ (Y Y' Z' : Scheme.{0}) (k : Y' ⟶ Y), IsFinite k → ∀ (p' : Z' ⟶ Y'), QuasiCompact p' → QuasiSeparated p' → ∀ (V : Y.Opens), IsAffineOpen V → ∀ y ∈ V, (∀ y₁ ∈ V, y ⤳ y₁ → y₁ = y) → ∀ (M : LB Z'), M.IsLB → (∀ x' : Y', k x' = y → ∃ W : Y'.Opens, x' ∈ W ∧ ∃ t : LB.Gen (M.pull (p' ⁻¹ᵁ W).ι), t.IsGen) → ∃ s : LB.Sec (M.pull (p' ⁻¹ᵁ (k ⁻¹ᵁ V)).ι), ∀ z : (p' ⁻¹ᵁ (k ⁻¹ᵁ V)).toScheme, k (p' ((p' ⁻¹ᵁ (k ⁻¹ᵁ V)).ι z)) = y → z ∈ nonzeroLocus s := by
  first | exact @GlobalTheory.Mum.exists_sec_nonzero_on_fibre | exact GlobalTheory.Mum.exists_sec_nonzero_on_fibre | (intros; apply GlobalTheory.Mum.exists_sec_nonzero_on_fibre <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSectionNonzeroUniformisedModelDvr
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Ex.OneGen
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.SiegTh Classical
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.UMin.ModelNZ

theorem exists_sec_nz : ∀ (W : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [CharZero W], IsAdicComplete (IsLocalRing.maximalIdeal W) W → ∀ (D : DegData W (IsLocalRing.maximalIdeal W)) (A : PolAV (Sp (FractionRing W))) (G : Over (Sp W)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (U : Unif (IsLocalRing.maximalIdeal W) D A G), ∃ σ : SecAt G U.LG.L (𝟙 (Sp W)), NZ G U.LG.L (𝟙 (Sp W)) σ := by
  intro R _ _ _ _ _ D A G _ _ hsemi U
  haveI : GeometricallyConnected G.hom := hsemi.geomConnected
  have hLaws := GlobalTheory.abelianSchemeLaws_all

  obtain ⟨th, hth, -⟩ := GlobalTheory.PsiRing.exists_basis_fibNZ hLaws.2.secTwist R D.toPre
  obtain ⟨f₀, hf₀⟩ : ∃ f₀ : D.toPre.SecB 1 0, ∀ (Z : Scheme.{0}) (r : Z ⟶ _) (z : Z) (J), Good D.toPre.P.L z J →
      sval th r z J = sval f₀ (r ≫ (snd (𝟙_ _) D.toPre.P.A).left) z J := by
    refine GlobalTheory.PsiExpansion.exists_sec_of_retract D.toPre.P.isLB _ _
      (GlobalTheory.PsiExpansion.snd_lift_unit D.toPre.P.A) (fun i => ?_) th
    fin_cases i
    · exact congrArg CommaMorphism.left (lift_snd (toUnit D.toPre.P.A) (𝟙 D.toPre.P.A))
    · refine congrArg CommaMorphism.left (show lift (toUnit D.toPre.P.A) (𝟙 D.toPre.P.A) ≫
        padd D.toPre.P.A (snd _ _) (toUnit _ ≫ D.toPre.c 0) = padd D.toPre.P.A (𝟙 _) (toUnit _ ≫ D.toPre.c 0) from ?_)
      simp only [padd, ← Category.assoc, comp_lift, lift_snd, comp_toUnit]
    · refine congrArg CommaMorphism.left
        (show lift (toUnit D.toPre.P.A) (𝟙 D.toPre.P.A) ≫ toUnit _ ≫ D.toPre.c 0 = toUnit _ ≫ D.toPre.c 0 from ?_)
      rw [← Category.assoc, comp_toUnit]
    · refine congrArg CommaMorphism.left
        (show lift (toUnit D.toPre.P.A) (𝟙 D.toPre.P.A) ≫ toUnit _ ≫ η[D.toPre.P.A] = toUnit _ ≫ η[D.toPre.P.A] from ?_)
      rw [← Category.assoc, comp_toUnit]
  obtain ⟨z₀, hz₀, hn₀⟩ := hth (IsLocalRing.closedPoint R)
  have hx : D.toPre.P.A.hom ((snd (𝟙_ (Over (Sp R))) D.toPre.P.A).left z₀) = IsLocalRing.closedPoint R :=
    (congrArg (fun q => q z₀) (Over.w (snd (𝟙_ (Over (Sp R))) D.toPre.P.A))).trans hz₀
  obtain ⟨J, hJ⟩ := GlobalTheory.ConstFam.exists_good' D.toPre.P.isLB z₀
  have hu : IsUnit (sval th (𝟙 _) z₀ J) := (isUnit_sval_iff th (𝟙 _) z₀ hJ).2 hn₀
  rw [hf₀ _ _ z₀ J hJ, Category.id_comp] at hu
  have hxn := (isUnit_sval_iff f₀ _ z₀ hJ).1 hu

  obtain ⟨σ, fam, hfam0, hσ, hmem, -⟩ := GlobalTheory.ThetaUnit.exists_theta hLaws.1.globalFns hLaws.1.secBaseChange
    le_rfl U f₀ ⟨_, hx, hxn⟩
  obtain ⟨g, hg, hn⟩ : ∃ g, G.hom g = IsLocalRing.closedPoint R ∧ g ∈ nonzeroLocus σ :=
    GlobalTheory.ThetaUnit.exists_mem_nonzeroLocus le_rfl U.toUnifPre (hσ 0)
      (by rw [hfam0]; exact ⟨_, hx, hxn⟩) hmem
  refine ⟨GlobalTheory.TorRef.upSec G σ, GlobalTheory.Ex.OnModel.toBase G g, ?_, ?_⟩
  · have a : GlobalTheory.Ex.OnModel.toBase G ≫ (fst (Over.mk (𝟙 (Sp R))) G).left = G.hom := by
      rw [GlobalTheory.Ex.OnModel.toBase, ← Over.comp_left, lift_fst]; rfl
    rw [← Scheme.Hom.comp_apply, a]
    exact hg
  · refine GlobalTheory.Ex.OnModel.mem_nonzeroLocus_pullTo σ _ _ ?_
    rw [← Scheme.Hom.comp_apply, GlobalTheory.Ex.OnModel.toBase_snd]
    exact hn

end GlobalTheory.UMin.ModelNZ
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSectionPointwiseOneCocycleOpenCoverStatement
section
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_section_pointwiseOneCocycle_openCover : ∀ (R : Type) [CommRing R] (X : Over (Sp R)) (K : Type) (W : K → X.left.Opens), ⨆ i, W i = ⊤ → ∀ u : Fn1 X, IsCoc W u → ∀ (D : Type) [CommRing D] [Algebra R D] (x : Pt X D), ∃ σ : ∀ (E : Type) [CommRing E] [Algebra R E], (D →ₐ[R] E) → E, ∀ (E : Type) [CommRing E] [Algebra R E] (E' : Type) [CommRing E'] [Algebra R E'] (ψ : D →ₐ[R] E) (θ : E →ₐ[R] E'), Sm W (spOver ψ ≫ x) → σ E' (θ.comp ψ) - θ (σ E ψ) = u E E' θ (spOver ψ ≫ x) := by
  first | exact @GlobalTheory.PtExt.CocSec.exists_section | exact GlobalTheory.PtExt.CocSec.exists_section | (intros; apply GlobalTheory.PtExt.CocSec.exists_section <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSectionPullbackCommutingEndomorphismGeneraStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_section_pullback_commuting_endomorphism_generator : ∀ {X Y : Scheme.{0}} (L : LB X), L.IsLB → ∀ (β : Y ⟶ X) (g : Y ⟶ Y) (h : X ⟶ X), g ≫ β = β ≫ h →
    ∀ (k k' : ℕ) (u : LB.Gen (LB.LinComb L (K := Fin 2) ![𝟙 X, h] ![(k' : ℤ), -(k : ℤ)])), u.IsGen → ∀ (σ : SecK L β k),
    ∃ σ₂ : SecK L β k', ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (J : (Z ⟶ X) → L.ι), Good L z J →
      sval σ₂ r z J = (val u (r ≫ β) z J).val * sval σ (r ≫ g) z J := by
  first | exact @GlobalTheory.Mum.exists_secK_pullMul_gen | exact GlobalTheory.Mum.exists_secK_pullMul_gen | (intros; apply GlobalTheory.Mum.exists_secK_pullMul_gen <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSectionPullbackTwoTorsionTranslation
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.TwoTorsTr

theorem tr_tr {R : Type} [CommRing R] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (a : 𝟙_ (Over (Sp R)) ⟶ G)
    (ha : a ^ 2 = 1) : ((toUnit G ≫ a) * 𝟙 G) ≫ ((toUnit G ≫ a) * 𝟙 G) = 𝟙 G := by
  rw [MonObj.comp_mul, ← Category.assoc, toUnit_unique (((toUnit G ≫ a) * 𝟙 G) ≫ toUnit G) (toUnit G),
    Category.comp_id, ← _root_.mul_assoc, ← MonObj.comp_mul, ← pow_two, ha, MonObj.comp_one, _root_.one_mul]

end GlobalTheory.TwoTorsTr

namespace GlobalTheory.TwoTorsTr

theorem secPull_invol {X : Scheme.{0}} (L L₂ : LB X) (hL : L.IsLB) (hL₂ : L₂.IsLB) (τ : X ⟶ X) (ττ : τ ≫ τ = 𝟙 X)
    (wL : LB.Iso L₂ (L.pull τ)) (hw : wL.IsGen) (σ : H0 L 1) : ∃ σ₂ : H0 L₂ 1,
    (∀ (Z : Scheme.{0}) (r : Z ⟶ X) (z : Z) (N : (Z ⟶ X) → L.ι) (N' : (Z ⟶ X) → L₂.ι),
      Geo.Tor.Good L z N → Geo.Tor.Good L₂ z N' →
      Geo.Tor.sval σ (r ≫ τ) z N = (Geo.Tor.gw wL r z (N (r ≫ τ)) (N' r)).val * Geo.Tor.sval σ₂ r z N') ∧
    ((∀ j, σ₂.f j = 0) → ∀ j, σ.f j = 0) := by
  have hc : ∀ κ : Fin 1, (fun _ : Fin 1 => 𝟙 X) κ ≫ τ = τ ≫ (fun _ : Fin 1 => 𝟙 X) κ := fun _ => by
    simp only [Category.id_comp, Category.comp_id]
  obtain ⟨σ₂, hσ₂, -⟩ := SecPull.existsUnique_secPull _ _ _ _ L L₂ τ hL hL₂ wL hw (Fin 1)
    (fun _ => 𝟙 X) (fun _ => 𝟙 X) (fun _ => ((1 : ℕ) : ℤ)) τ hc σ
  have key : ∀ (Z : Scheme.{0}) (r : Z ⟶ X) (z : Z) (N : (Z ⟶ X) → L.ι) (N' : (Z ⟶ X) → L₂.ι),
      Geo.Tor.Good L z N → Geo.Tor.Good L₂ z N' →
      Geo.Tor.sval σ (r ≫ τ) z N = (Geo.Tor.gw wL r z (N (r ≫ τ)) (N' r)).val * Geo.Tor.sval σ₂ r z N' := by
    intro Z r z N N' hN hN'
    have := ExpTrans.sec_val wL (fun _ : Fin 1 => 𝟙 X) (fun _ => 𝟙 X) (fun _ => ((1 : ℕ) : ℤ)) τ hc σ σ₂
      r z (hσ₂ Z r z) hN hN'
    rw [this, Fin.prod_univ_one, zpow_natCast, pow_one, ExpTrans.om, Category.comp_id]
  refine ⟨σ₂, key, fun h0 j => ?_⟩
  refine ThetaScalar.eq_zero_of_sval hL σ (fun y J hJ => ?_) j
  choose J' hJ' using fun ψ : X ⟶ X => exists_chart hL₂ (ψ y)
  have e := key X τ y J J' hJ hJ'
  rw [ττ, ThetaScalar.sval_eq_zero σ₂ h0 τ y hJ', MulZeroClass.mul_zero] at e
  exact e

end GlobalTheory.TwoTorsTr

namespace GlobalTheory

theorem twoTors_secPull : ∀ (R : Type) [CommRing R] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (L L₂ : LB G.left), L.IsLB → L₂.IsLB → ∀ a : 𝟙_ (Over (Sp R)) ⟶ G, a ^ 2 = 1 → ∀ wL : LB.Iso L₂ (L.pull ((toUnit G ≫ a) * 𝟙 G).left), wL.IsGen → ∀ σ : H0 L 1, ∃ σ₂ : H0 L₂ 1, (∀ (Z : Scheme.{0}) (r : Z ⟶ G.left) (z : Z) (N : (Z ⟶ G.left) → L.ι) (N' : (Z ⟶ G.left) → L₂.ι), Geo.Tor.Good L z N → Geo.Tor.Good L₂ z N' → Geo.Tor.sval σ (r ≫ ((toUnit G ≫ a) * 𝟙 G).left) z N = (Geo.Tor.gw wL r z (N (r ≫ ((toUnit G ≫ a) * 𝟙 G).left)) (N' r)).val * Geo.Tor.sval σ₂ r z N') ∧ ((∀ j, σ₂.f j = 0) → ∀ j, σ.f j = 0) := by
  intro R _ G _ _ L L₂ hL hL₂ a ha wL hw σ
  exact TwoTorsTr.secPull_invol L L₂ hL hL₂ _
    (by rw [← Over.comp_left, TwoTorsTr.tr_tr G a ha, Over.id_left]) wL hw σ

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSectionQuotientOfExpansionDvdStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_section_quotient_of_expansion_dvd : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegPre R) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (U : GlobalTheory.UU.PreU (maximalIdeal R) D A G) (σ : U.SecGT (𝟙_ _) 1) (f g : ∀ α, GlobalTheory.UU.SecBT D (𝟙_ _) 1 α) (q : R), q ≠ 0 → U.ExpT (𝟙_ _) 1 σ f → (∀ α, ReciprocityTheory.ChartRestriction.G.DVR.SecIsMul (𝟙_ _ ⊗ D.P.A).hom q (f α) (g α)) → ∃ τ : U.SecGT (𝟙_ _) 1, U.ExpT (𝟙_ _) 1 τ g := by
  first | exact @GlobalTheory.SecDiv.exists_expT_of_dvd | exact GlobalTheory.SecDiv.exists_expT_of_dvd | (intros; apply GlobalTheory.SecDiv.exists_expT_of_dvd <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSelfDualLatticeCmHomomorphismsDefinite
section
set_option autoImplicit false

open NumberField

namespace GlobalTheory.FlatCM.HomLat

theorem exists_selfDual_lieSpan : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E),
    GlobalTheory.IndefiniteRowSideFullHecke.EigenvectorLieDegree.IsHostField H → ∀ (K : Type) [Field K] [NumberField K] (ρ : 𝓞 K) (σ₁ : K →+* ℂ) (p : ℕ)
    (X : GlobalTheory.CM.CMObj H K ρ σ₁ p 0) (gP : Matrix (Fin p) (Fin p) (𝓞 E)) (gQ : Matrix (Fin 0) (Fin 0) (𝓞 E)),
    GlobalTheory.FlatCM.IsGram X gP gQ →
    ∃ Λ : Submodule (𝓞 E) (Fin p → E), Λ.FG ∧ (∀ x : Fin p → 𝓞 E, (fun a => (x a : E)) ∈ Λ) ∧
      (∀ barE : E →+* E, (∀ x : 𝓞 E, barE x = ((H.bar x : 𝓞 E) : E)) →
        ∀ d : Fin p → E, d ∈ Λ ↔ ∀ c ∈ Λ, ∃ y : 𝓞 E, (y : E) = ∑ a, ∑ b, c a * (gP a b : E) * barE (d b)) ∧
      ∀ (FP : GlobalTheory.CM.GenFib (X.A true).pol) (FB : GlobalTheory.CM.GenFib X.B.pol)
        (MP : Fin p → ((Fin FP.P₀.g → K) →ₗ[K] (Fin FB.P₀.g → K))),
        (∀ a, FP.IsDiffOf FB (GlobalTheory.FlatCM.phiP X a) (MP a)) →
        ∀ τ : 𝓞 E →+* 𝓞 K, τ H.rt = ρ → ∀ τE : E →+* K, (∀ x : 𝓞 E, τE x = ((τ x : 𝓞 K) : K)) →
          FB.eigLat X.B.t.act τ = Submodule.span (𝓞 K)
            {w | ∃ c ∈ Λ, ∃ e ∈ FP.eigLat (X.A true).t.act τ, w = ∑ a, τE (c a) • MP a e} := by
  intro E _ _ _ H hH K _ _ ρ σ₁ p X gP gQ hG
  refine ⟨GlobalTheory.FlatCM.HomLat.lat X, GlobalTheory.T.cmLinearHomCoordinateLattice_fg E H hH K ρ σ₁ p X, GlobalTheory.FlatCM.HomLat.intl_mem X,
    fun barE hbar d => ⟨fun hd c hc => GlobalTheory.T.cmHomGramForm_integral_coordinateLattice E H hH K ρ σ₁ p X gP gQ hG barE hbar c hc d hd,
      GlobalTheory.T.mem_cmCoordinateLattice_of_integral_gramPairing E H hH K ρ σ₁ p X gP gQ hG barE hbar d⟩, ?_⟩
  intro FP FB MP hMP τ hτ τE hτE
  refine le_antisymm (GlobalTheory.T.lieEigenLattice_le_span_cmHom_images E H hH K ρ σ₁ p X FP FB MP hMP τ hτ τE hτE) ?_
  refine Submodule.span_le.2 ?_
  rintro w ⟨c, hc, e, he, rfl⟩
  induction hc using Submodule.span_induction generalizing e with
  | mem c hc => exact GlobalTheory.T.sum_smul_differential_mem_eigenLattice E H hH K ρ σ₁ p X FP FB MP hMP τ hτ τE hτE c hc e he
  | zero => simp
  | add c d _ _ hc hd =>
    simp only [Pi.add_apply, map_add, add_smul, Finset.sum_add_distrib]
    exact add_mem (hc e he) (hd e he)
  | smul s c _ hc =>
    have h1 : ∑ a, τE ((s • c) a) • MP a e = ∑ a, τE (c a) • MP a ((τ s : K) • e) := by
      refine Finset.sum_congr rfl fun a _ => ?_
      have h2 : τE ((s • c) a) = (τ s : K) * τE (c a) := by
        rw [Pi.smul_apply, Algebra.smul_def, map_mul]
        exact congrArg (· * τE (c a)) (hτE s)
      rw [h2, mul_smul, (MP a).map_smul, smul_comm]
    rw [h1]
    exact hc _ (by simpa [algebraMap_smul] using (FP.eigLat (X.A true).t.act τ).smul_mem (τ s) he)

end GlobalTheory.FlatCM.HomLat
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSelfPullbackDegenerationDataRingAutOverStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_selfPullback_degenerationData_ringAutOver : ∀ (R R' : Type) [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] (ρ : R →+* R'), Function.Injective ρ →
    ∀ (D : DegPre R) (D' : DegPre R') (hD : IsPullDeg ρ D D') (σ : Gal ρ),
      ∃ h : IsPullDeg (Gal.hom σ) D' D', PullOver hD h := by
  first | exact @GlobalTheory.Mum.SelfPull.exists_isPullDeg_self_pullOver | exact GlobalTheory.Mum.SelfPull.exists_isPullDeg_self_pullOver | (intros; apply GlobalTheory.Mum.SelfPull.exists_isPullDeg_self_pullOver <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSemilinearLabelActionOfGaloisDeeperStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_semilinear_label_action_of_galois_deeper : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H), 1 ≤ Dw.p + Dw.q → ∀ (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (cf : Coeff l) (C : UCompact Xo cf), ∀ (X₁ : USetup C) (D : UDeep X₁) (σ : D.X.Ω₁ ≃ₐ[X₁.Ω₁] D.X.Ω₁), ∃ a : D.X.S.Gam ≃+ D.X.S.Gam, D.GalLab σ a ∧ ∀ x, a (D.lab x) = D.lab x := by
  first | exact @GlobalTheory.UPoinc.UGalAct.exists_galLab | exact GlobalTheory.UPoinc.UGalAct.exists_galLab | (intros; apply GlobalTheory.UPoinc.UGalAct.exists_galLab <;> assumption)
end

