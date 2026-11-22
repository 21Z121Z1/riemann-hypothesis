import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0003
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0004
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0026
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0038
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0064
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0062
import Development.AutomorphicSpectrum.Statements.GeometryStatements.Bundle0003
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0010
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.HeckeSectionsIsotropicCommutatorPairingPower
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0016
import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.Bundle0014
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsFlatAnIffIsConstMul
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0013
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsLieModel
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0018
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0063
import Development.AutomorphicSpectrum.Statements.GeometryStatements.IsPolLatticePlane
import Development.AutomorphicSpectrum.Statements.AlgebraStatements.Bundle0003
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.Birational
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.GlueApplyOfNotInFibre
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0007
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.SymplecticPolydiscPeriodBasis
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Bundle0004

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieChartOfSmoothChart
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.ChartDer

open scoped TensorProduct

theorem exists_diffModule {A B : Type} [CommRing A] [CommRing B] (g : B →+* A) (hg : g.Smooth)
    {R : Type} [CommRing R] (f : R) (u : A →+* Localization.Away f) :
    ∃ (P : Type) (_ : AddCommGroup P) (_ : Module R P) (_ : Module (Localization.Away f) P)
      (_ : IsScalarTower R (Localization.Away f) P) (_ : Module.Finite (Localization.Away f) P)
      (_ : Module.Projective (Localization.Away f) P) (d : A → P),
      (∀ a b, d (a + b) = d a + d b) ∧ (∀ a b, d (a * b) = u a • d b + u b • d a) ∧ (∀ b, d (g b) = 0) ∧
      ∀ (C : Type) [CommRing C] [Algebra R C] (κ : Localization.Away f →+* C),
        κ.comp (algebraMap R (Localization.Away f)) = algebraMap R C →
        (∀ (w : P →ₗ[R] C) (r : Localization.Away f) (p : P), w (r • p) = κ r * w p) ∧
        (∀ w w' : P →ₗ[R] C, (∀ a, w (d a) = w' (d a)) → w = w') ∧
        (∀ δ : A → C, (∀ a b, δ (a + b) = δ a + δ b) →
          (∀ a b, δ (a * b) = κ (u a) * δ b + κ (u b) * δ a) → (∀ b, δ (g b) = 0) →
          ∃ w : P →ₗ[R] C, ∀ a, w (d a) = δ a) := by
  letI iB : Algebra B A := g.toAlgebra
  haveI : Algebra.Smooth B A := hg
  letI iA : Algebra A (Localization.Away f) := u.toAlgebra
  haveI tw : IsScalarTower R (Localization.Away f) (Localization.Away f ⊗[A] Ω[A⁄B]) := inferInstance
  have hsmul : ∀ (a : A) (x : Ω[A⁄B]), (1 : Localization.Away f) ⊗ₜ[A] (a • x) =
      u a • ((1 : Localization.Away f) ⊗ₜ[A] x) := fun a x => by
    have e : a • (1 : Localization.Away f) = u a := by
      rw [Algebra.smul_def, _root_.mul_one]; rfl
    rw [← TensorProduct.smul_tmul, e, TensorProduct.smul_tmul', smul_eq_mul, _root_.mul_one]
  refine ⟨Localization.Away f ⊗[A] Ω[A⁄B], inferInstance, inferInstance, inferInstance, tw,
    Module.Finite.base_change A _ _, inferInstance, fun a => 1 ⊗ₜ[A] KaehlerDifferential.D B A a,
    fun a b => by simp [TensorProduct.tmul_add], fun a b => ?_, fun b => ?_, ?_⟩
  · simp only [Derivation.leibniz, TensorProduct.tmul_add, hsmul]
  · have : g b = algebraMap B A b := rfl
    simp [this]
  intro C _ _ κ hκ
  letI aC : Algebra (Localization.Away f) C := κ.toAlgebra
  haveI : IsScalarTower R (Localization.Away f) C := IsScalarTower.of_algebraMap_eq' hκ.symm
  have lin : ∀ (w : (Localization.Away f ⊗[A] Ω[A⁄B]) →ₗ[R] C) (r : Localization.Away f) p,
      w (r • p) = κ r * w p := fun w r p => by
    have h : w (r • p) = r • w p :=
      (w.extendScalarsOfIsLocalization (Submonoid.powers f) (Localization.Away f)).map_smul r p
    rw [h, Algebra.smul_def]
    rfl
  refine ⟨lin, fun w w' h => LinearMap.ext fun p => ?_, fun δ h1 h2 h3 => ?_⟩
  · have hD : ∀ x : Ω[A⁄B], w ((1 : Localization.Away f) ⊗ₜ[A] x) = w' ((1 : Localization.Away f) ⊗ₜ[A] x) := by
      intro x
      have hx : x ∈ Submodule.span A (Set.range (KaehlerDifferential.D B A)) := by
        rw [KaehlerDifferential.span_range_derivation]; trivial
      induction hx using Submodule.span_induction with
      | mem x hx => obtain ⟨a, rfl⟩ := hx; exact h a
      | zero => simp
      | add x y _ _ hx hy => rw [TensorProduct.tmul_add, map_add, map_add, hx, hy]
      | smul a x _ ih => rw [hsmul, lin, lin, ih]
    induction p using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => simp [map_add, hx, hy]
    | tmul r x =>
      have e : r ⊗ₜ[A] x = r • ((1 : Localization.Away f) ⊗ₜ[A] x) := by
        rw [TensorProduct.smul_tmul', smul_eq_mul, _root_.mul_one]
      rw [e, lin, lin, hD]
  · letI aA : Algebra A C := (κ.comp u).toAlgebra
    haveI : IsScalarTower A (Localization.Away f) C := IsScalarTower.of_algebraMap_eq' rfl
    letI aB : Algebra B C := ((κ.comp u).comp g).toAlgebra
    haveI : IsScalarTower B A C := IsScalarTower.of_algebraMap_eq' rfl
    let L : A →ₗ[B] C :=
      { toFun := δ
        map_add' := h1
        map_smul' := fun b a => by
          change δ (g b * a) = κ (u (g b)) * δ a
          rw [h2, h3, mul_zero, add_zero] }
    let Dv : Derivation B A C := Derivation.mk' L fun a b => by
      change δ (a * b) = κ (u a) * δ b + κ (u b) * δ a
      exact h2 a b
    refine ⟨(Dv.liftKaehlerDifferential.liftBaseChange (Localization.Away f)).restrictScalars R, fun a => ?_⟩
    simp only [LinearMap.restrictScalars_apply, LinearMap.liftBaseChange_tmul, one_smul,
      Derivation.liftKaehlerDifferential_comp_D]
    rfl

def dualOf {A C : Type} [CommRing A] [CommRing C] (v : A →+* C) (δ : A → C)
    (h1 : ∀ a b, δ (a + b) = δ a + δ b) (h2 : ∀ a b, δ (a * b) = v a * δ b + v b * δ a) :
    A →+* DualNumber C where
  toFun a := TrivSqZeroExt.inl (v a) + TrivSqZeroExt.inr (δ a)
  map_one' := by
    have h : δ 1 = 0 := by simpa using h2 1 1
    ext <;> simp [h]
  map_mul' a b := by
    ext
    · simp
    · simp [h2, TrivSqZeroExt.snd_mul]
      ring
  map_zero' := by
    have h : δ 0 = 0 := by simpa using h1 0 0
    ext <;> simp [h]
  map_add' a b := by
    ext
    · simp
    · simp [h1]

theorem dualOf_fst {A C : Type} [CommRing A] [CommRing C] (v : A →+* C) (δ : A → C) (h1 h2) (a : A) :
    (dualOf v δ h1 h2 a).fst = v a := by
  simp [dualOf]

theorem dualOf_snd {A C : Type} [CommRing A] [CommRing C] (v : A →+* C) (δ : A → C) (h1 h2) (a : A) :
    (dualOf v δ h1 h2 a).snd = δ a := by
  simp [dualOf]

theorem spMap_comp {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (g : B →+* C) (f : A →+* B) :
    spMap (g.comp f) = spMap g ≫ spMap f := by
  rw [spMap, CommRingCat.ofHom_comp, Spec.map_comp]

theorem one_left {T : Scheme.{0}} {X M : Over T} [GrpObj M] : (1 : X ⟶ M).left = X.hom ≫ η[M].left := by
  rw [Hom.one_def, Over.comp_left, Over.toUnit_left]

theorem exists_lieModel {S : Scheme.{0}} (G : Over S) [GrpObj G] (U : G.left.Opens) (V : S.Opens)
    (hU : IsAffineOpen U) (hV : IsAffineOpen V) (hUV : U ≤ G.hom ⁻¹ᵁ V)
    (C : Type) [CommRing C] (y : Sp C ⟶ S) (v : Γ(G.left, U) →+* C)
    (h1 : (1 : Over.mk y ⟶ G).left = spMap v ≫ hU.fromSpec)
    {E : Type} [AddCommGroup E] [Module C E] (δ : E → Γ(G.left, U) → C)
    (hadd : ∀ e a b, δ e (a + b) = δ e a + δ e b)
    (hmul : ∀ e a b, δ e (a * b) = v a * δ e b + v b * δ e a)
    (hker : ∀ e b, δ e ((G.hom.appLE V U hUV).hom b) = 0)
    (hEadd : ∀ e e' a, δ (e + e') a = δ e a + δ e' a)
    (hEsmul : ∀ (c : C) e a, δ (c • e) a = c * δ e a)
    (hinj : ∀ e e', (∀ a, δ e a = δ e' a) → e = e')
    (hsurj : ∀ δ' : Γ(G.left, U) → C, (∀ a b, δ' (a + b) = δ' a + δ' b) →
      (∀ a b, δ' (a * b) = v a * δ' b + v b * δ' a) →
      (∀ b, δ' ((G.hom.appLE V U hUV).hom b) = 0) → ∃ e, ∀ a, δ e a = δ' a) :
    ∃ M : LieModel G y E, ∀ e, ∃ φ : Γ(G.left, U) →+* DualNumber C,
      (∀ a, (φ a).fst = v a) ∧ (∀ a, (φ a).snd = δ e a) ∧ (M.pt e).left = spMap φ ≫ hU.fromSpec := by
  obtain ⟨c1, c2⟩ := GlobalTheory.T.tangent_vector_of_dual_hom S G U V hU hV hUV C y v h1
  let φ : E → (Γ(G.left, U) →+* DualNumber C) := fun e => dualOf v (δ e) (hadd e) (hmul e)
  have φfst : ∀ e a, (φ e a).fst = v a := fun e a => dualOf_fst ..
  have φsnd : ∀ e a, (φ e a).snd = δ e a := fun e a => dualOf_snd ..
  have ex : ∀ e, ∃ t : epsAt y ⟶ G, IsTanAt G y t ∧ t.left = spMap (φ e) ≫ hU.fromSpec :=
    fun e => c1 (φ e) (φfst e) fun b => by rw [φsnd, hker]
  choose pt ptan pleft using ex
  have spinj : ∀ ψ ψ' : Γ(G.left, U) →+* DualNumber C,
      spMap ψ ≫ hU.fromSpec = spMap ψ' ≫ hU.fromSpec → ψ = ψ' := fun ψ ψ' h => by
    have h2 := Spec.map_injective ((cancel_mono hU.fromSpec).1 h)
    simpa using congrArg CommRingCat.Hom.hom h2
  refine ⟨{ pt := pt, tan := ptan, inj := ?_, onto := ?_, add := ?_, smul := ?_ },
    fun e => ⟨φ e, φfst e, φsnd e, pleft e⟩⟩
  · intro e e' h
    have h2 := spinj _ _ (by rw [← pleft, ← pleft, h] : spMap (φ e) ≫ hU.fromSpec = spMap (φ e') ≫ hU.fromSpec)
    exact hinj _ _ fun a => by rw [← φsnd, h2, φsnd]
  · intro t ht
    obtain ⟨ψ, f1, f2, f3⟩ := c2 t ht
    obtain ⟨e, he⟩ := hsurj (fun a => (ψ a).snd) (fun a b => by simp)
      (fun a b => by
        simp only [map_mul, TrivSqZeroExt.snd_mul, f1]
        simp [mul_comm, add_comm]) f2
    refine ⟨e, Over.OverMorphism.ext ?_⟩
    have h2 : φ e = ψ := RingHom.ext fun a => TrivSqZeroExt.ext (by rw [φfst, f1]) (by rw [φsnd, he])
    rw [pleft, f3, h2]
  · intro e e'
    refine Over.OverMorphism.ext ?_
    rw [GlobalTheory.T.tangent_vector_sum_dual_number S G U hU C y v h1 (pt e) (pt e') (ptan e) (ptan e') (φ e) (φ e') (φ (e + e'))
      (φfst e) (φfst e') (φfst _) (fun a => by rw [φsnd, φsnd, φsnd, hEadd]) (pleft e) (pleft e'), pleft]
  · intro c e
    have h2 : φ (c • e) = (epsMul c).comp (φ e) := RingHom.ext fun a => TrivSqZeroExt.ext
      (by simp [epsMul, φfst]) (by simp [epsMul, φsnd, hEsmul])
    rw [pleft, pleft, h2, spMap_comp, Category.assoc]

theorem lieChart_of_smooth_chart : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] (R : Type) [CommRing R] (x : Sp R ⟶ S) (f : R) (U : G.left.Opens) (V : S.Opens)
  (hU : IsAffineOpen U) (hV : IsAffineOpen V) (hUV : U ≤ G.hom ⁻¹ᵁ V), RingHom.Smooth (G.hom.appLE V U hUV).hom →
  ∀ u : Γ(G.left, U) →+* Localization.Away f,
    (1 : Over.mk (spMap (algebraMap R (Localization.Away f)) ≫ x) ⟶ G).left = spMap u ≫ hU.fromSpec → LieChart G x f := by
  intro S G _ R _ x f U V hU hV hUV hsm u h1
  obtain ⟨P, i1, i2, i3, i4, i5, i6, d, dadd, dmul, dker, hP⟩ :=
    exists_diffModule (G.hom.appLE V U hUV).hom hsm f u
  have hunit : ∀ (C : Type) [CommRing C] [Algebra R C] (κ : Localization.Away f →+* C),
      κ.comp (algebraMap R (Localization.Away f)) = algebraMap R C →
      (1 : Over.mk (spMap (algebraMap R C) ≫ x) ⟶ G).left = spMap (κ.comp u) ≫ hU.fromSpec := by
    intro C _ _ κ hκ
    rw [one_left] at h1 ⊢
    simp only [Over.mk_hom] at h1 ⊢
    have e : spMap (algebraMap R C) = spMap κ ≫ spMap (algebraMap R (Localization.Away f)) := by
      rw [← spMap_comp, hκ]
    have h3 : ((spMap κ ≫ spMap (algebraMap R (Localization.Away f))) ≫ x) ≫ η[G].left =
        spMap κ ≫ (spMap (algebraMap R (Localization.Away f)) ≫ x) ≫ η[G].left := by
      simp only [Category.assoc]
    rw [e, h3, h1, spMap_comp κ u]
    exact (Category.assoc _ _ _).symm
  have key : ∀ (C : Type) [CommRing C] [Algebra R C] (hC : IsUnit (algebraMap R C f)),
      ∃ M : LieModel G (spMap (algebraMap R C) ≫ x) (P →ₗ[R] C), ∀ w,
        ∃ φ : Γ(G.left, U) →+* DualNumber C,
          (∀ a, (φ a).fst = ((IsLocalization.Away.lift f hC).comp u) a) ∧ (∀ a, (φ a).snd = w (d a)) ∧
          (M.pt w).left = spMap φ ≫ hU.fromSpec := by
    intro C _ _ hC
    have hκ := IsLocalization.Away.lift_comp (S := Localization.Away f) f hC
    obtain ⟨l1, l2, l3⟩ := hP C _ hκ
    exact exists_lieModel (E := P →ₗ[R] C) G U V hU hV hUV C _ _ (hunit C _ hκ)
      (fun (w : P →ₗ[R] C) a => w (d a))
      (fun w a b => by simp [dadd]) (fun w a b => by simp only [dmul, map_add, l1, RingHom.comp_apply])
      (fun w b => by simp [dker]) (fun w w' a => rfl) (fun c w a => by simp) l2 l3
  refine ⟨P, i1, i2, i3, i4, i5, i6, fun C _ _ hC => (key C hC).choose, ?_⟩
  intro C C' _ _ _ _ hC hC' c w
  obtain ⟨φ, f1, f2, f3⟩ := (key C hC).choose_spec w
  obtain ⟨φ', g1, g2, g3⟩ := (key C' hC').choose_spec (c.toLinearMap ∘ₗ w)
  have hc : c.toRingHom.comp (IsLocalization.Away.lift (S := Localization.Away f) f hC) =
      IsLocalization.Away.lift (S := Localization.Away f) f hC' := by
    refine IsLocalization.ringHom_ext (Submonoid.powers f) ?_
    rw [RingHom.comp_assoc, IsLocalization.Away.lift_comp, IsLocalization.Away.lift_comp]
    exact c.comp_algebraMap
  have h2 : φ' = (dualMap c.toRingHom).comp φ := RingHom.ext fun a => TrivSqZeroExt.ext
    (by
      simp only [g1, RingHom.comp_apply, dualMap, RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk,
        TrivSqZeroExt.fst_add, TrivSqZeroExt.fst_inl, TrivSqZeroExt.fst_inr, add_zero, f1]
      exact (RingHom.congr_fun hc (u a)).symm)
    (by
      simp only [g2, RingHom.comp_apply, dualMap, RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk,
        TrivSqZeroExt.snd_add, TrivSqZeroExt.snd_inl, TrivSqZeroExt.snd_inr, zero_add, f2]
      rfl)
  rw [g3, f3, h2, spMap_comp, Category.assoc]

end GlobalTheory.CompanionTheory.Ar.ChartDer
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelTwistedComparisonStatement
section
open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lie_model_twisted_comparison : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (g : HostAut H) (Ω : Type) [Field Ω]
    (X X' : Scheme.{0}) (ξ : Sp Ω ⟶ X) (ξ' : Sp Ω ⟶ X') (t : SAB H X) (t' : SAB H X') (tΩ : SAB H (Sp Ω))
    (m : SABMap tΩ t ξ) (m' : SABMap (twistSAB tΩ g) t' ξ') (V V' : Type) [AddCommGroup V] [Module Ω V]
    [AddCommGroup V'] [Module Ω V'] (M : LieModel t.G ξ V) (M' : LieModel t'.G ξ' V')
    (ρ : 𝓞 E →+* Module.End Ω V) (ρ' : 𝓞 E →+* Module.End Ω V') (φ : V ≃ₗ[Ω] V'),
    M.IsActOf t.act.act ρ → M'.IsActOf t'.act.act ρ' →
    (∀ v, ∃ w : epsAt (𝟙 (Sp Ω)) ⟶ tΩ.G, w.left ≫ m.φ = (M.pt v).left ∧ w.left ≫ m'.φ = (M'.pt (φ v)).left) →
    ∀ a v, φ (ρ (g.s a) v) = ρ' a (φ v) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.LieIntertwining.act_intertwine | exact GlobalTheory.CompanionTheory.Ar.LieIntertwining.act_intertwine | (intros; apply GlobalTheory.CompanionTheory.Ar.LieIntertwining.act_intertwine <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.MultihomogComponentQuotient
section
open MvPolynomial

namespace GlobalTheory.CompanionTheory.Ggeo

theorem multihomog_component_relation : ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MvPolynomial (Σ k, ι k) ℤ)), P.IsPrime → GroundTheory.Heights₂.Heights.NumbersDVR.IsMultiHomogIdeal P → ∀ (f g u₀ v₀ : MvPolynomial (Σ k, ι k) ℤ) (bf bg a : K → ℕ), GroundTheory.Heights₂.Heights.NumbersDVR.IsMultiHomog f bf → GroundTheory.Heights₂.Heights.NumbersDVR.IsMultiHomog g bg → f ∉ P → u₀ * f - v₀ * g ∈ P → weightedHomogeneousComponent (GroundTheory.Heights₂.Heights.NumbersDVR.blockWeight ι) a u₀ ∉ P → ∃ (b : K → ℕ) (v : MvPolynomial (Σ k, ι k) ℤ), GroundTheory.Heights₂.Heights.NumbersDVR.IsMultiHomog v b ∧ a + bf = b + bg ∧ (weightedHomogeneousComponent (GroundTheory.Heights₂.Heights.NumbersDVR.blockWeight ι) a u₀) * f - v * g ∈ P :=
  @PositivityTheory.Xgn.homogeneous_pair_component

end GlobalTheory.CompanionTheory.Ggeo
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.MultihomogIdealEquivalenceStatement
section
open MvPolynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isMultiHomogIdeal_transfer : ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MvPolynomial (Σ k, ι k) ℤ)), ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomogIdeal P → GroundTheory.Heights₂.Heights.NumbersDVR.IsMultiHomogIdeal P := by
  first | exact @GlobalTheory.CompanionTheory.Ggeo.CompMem.comp_mem | exact GlobalTheory.CompanionTheory.Ggeo.CompMem.comp_mem | (intros; apply GlobalTheory.CompanionTheory.Ggeo.CompMem.comp_mem <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.MultihomogNonvanishingRatio
section
open MvPolynomial

namespace GlobalTheory.CompanionTheory.Ggeo.TwistLine

theorem forms_off_vanishing_locus : ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MvPolynomial (Σ k, ι k) ℤ)) (bf bg : K → ℕ) (z : ((Σ k, ι k) → ℂ)) (q : MvPolynomial (Σ k, ι k) ℤ), GroundTheory.Heights₂.Heights.NumbersDVR.IsMultiHomogIdeal P → (∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) → q ∈ P → eval z (MvPolynomial.map (Int.castRingHom ℂ) q) ≠ 0 → ∃ (a b : K → ℕ) (u v : MvPolynomial (Σ k, ι k) ℤ), GroundTheory.Heights₂.Heights.NumbersDVR.IsMultiHomog u a ∧ GroundTheory.Heights₂.Heights.NumbersDVR.IsMultiHomog v b ∧ a + bf = b + bg ∧ u ∈ P ∧ v ∈ P ∧ eval z (MvPolynomial.map (Int.castRingHom ℂ) u) ≠ 0 ∧ eval z (MvPolynomial.map (Int.castRingHom ℂ) v) ≠ 0 :=
  @PositivityTheory.Xgn.multihomogeneous_nonvanishing_off

end GlobalTheory.CompanionTheory.Ggeo.TwistLine
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.NonemptyCptOverOfFlatPreimmersion
section
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Flat

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat

theorem isCptGen_comp_of_flat_preimmersion {A X : Scheme.{0}} (j : A ⟶ X) [IsPreimmersion j] [Flat j]
    (hX : ∀ x : X, IsDomain (X.presheaf.stalk x)) (w : A) (hw : ∀ y : A, y ⤳ w → y = w) :
    IsCptGen (Ω := A.residueField w) (A.fromSpecResidueField w ≫ j) := by
  have e : genPt (Ω := A.residueField w) (A.fromSpecResidueField w ≫ j) = j w :=
    congrArg j (A.fromSpecResidueField_apply w _)
  refine isCptGen_of_maximal_of_surjective hX _ ?_ ?_
  · rw [e]
    intro y hy
    obtain ⟨a, ha, rfl⟩ := AlgebraicGeometry.Flat.generalizingMap j hy
    rw [hw a ha]
  · unfold Scheme.stalkClosedPointTo
    rw [CommRingCat.hom_comp, RingHom.coe_comp]
    exact (ConcreteCategory.bijective_of_isIso (stalkClosedPointIso _).hom).2.comp
      ((A.fromSpecResidueField w ≫ j).stalkMap_surjective _)

theorem eq_genericPoint_of_specializes {A : Type*} [TopologicalSpace A] [T0Space A] {U : Set A}
    (hU : U ∈ irreducibleComponents A) {w : A} (hw : IsGenericPoint w U) (y : A) (hy : y ⤳ w) : y = w := by
  have h1 : U ⊆ closure {y} := by
    rw [← hw.def]
    exact closure_minimal (Set.singleton_subset_iff.2 (specializes_iff_mem_closure.1 hy)) isClosed_closure
  have h2 : closure {y} ⊆ U := hU.2 isIrreducible_singleton.closure h1
  have h3 : w ⤳ y := hw.specializes (h2 (subset_closure rfl))
  exact (hy.antisymm h3).eq

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {Xo : Moduli D l} {c : Coeff l}

theorem nonempty_cptOver_of_flat_preimmersion {O : Type} [CommRing O] {β : O →+* c.F} [IsPreimmersion (spMap β)]
    [Flat (spMap β)] (Y : Model Xo c β) (U : Set (Xo.XF c)) (hU : U ∈ irreducibleComponents (Xo.XF c)) :
    Nonempty (CptOver Y U) := by
  have := Y.jQ_open
  have : IsPreimmersion Y.j := by unfold Model.j; infer_instance
  have : Flat Y.j := by unfold Model.j; infer_instance
  obtain ⟨w, hw⟩ := QuasiSober.sober hU.1 (isClosed_of_mem_irreducibleComponents U hU)
  let Ω : Type := (Xo.XF c).residueField w
  let ξ₀ : Sp Ω ⟶ Xo.XF c := (Xo.XF c).fromSpecResidueField w
  have e : genPt ξ₀ = w := (Xo.XF c).fromSpecResidueField_apply w _
  obtain ⟨V, _, _, ⟨M⟩⟩ := lieModel_exists Y.X Y.t.G Ω (ξ₀ ≫ Y.j)
  obtain ⟨ρ, hρ, -⟩ := lieModel_exists_unique_act Y.X Y.t.G Ω (ξ₀ ≫ Y.j) V M (𝓞 E) Y.t.act.act
    Y.t.act.hom Y.t.act.one Y.t.act.mul Y.t.act.add
  exact ⟨{
    Ω := Ω
    ξ₀ := ξ₀
    inc := (Spec.preimage (ξ₀ ≫ pullback.snd _ _)).hom
    over_inc := (Spec.map_preimage _).symm
    gen := isCptGen_comp_of_flat_preimmersion Y.j (fun x => (Y.normal x).1) w
      (eq_genericPoint_of_specializes hU hw)
    closure := fun u => by rw [e]; exact hw.specializes_iff_mem.symm
    V := V
    M := M
    ρ := ρ
    act := hρ }⟩

theorem nonempty_cptOver_of_fraction {O : Type} [CommRing O] {β : O →+* c.F} (hβ : Function.Injective β)
    (hfr : ∀ x : c.F, ∃ a b : O, β b ≠ 0 ∧ x * β b = β a) (Y : Model Xo c β) (U : Set (Xo.XF c))
    (hU : U ∈ irreducibleComponents (Xo.XF c)) : Nonempty (CptOver Y U) := by
  letI : Algebra O c.F := β.toAlgebra
  haveI : IsDomain O := hβ.isDomain β
  haveI : FaithfulSMul O c.F := (faithfulSMul_iff_algebraMap_injective O c.F).2 hβ
  haveI : IsFractionRing O c.F := IsFractionRing.of_field O c.F fun x => by
    obtain ⟨a, b, hb, h⟩ := hfr x
    exact ⟨a, b, (eq_div_iff hb).2 h⟩
  haveI : IsPreimmersion (spMap β) := IsPreimmersion.of_isLocalization (nonZeroDivisors O)
  haveI : Flat (spMap β) := by
    rw [HasRingHomProperty.Spec_iff (P := @Flat)]
    exact IsLocalization.flat c.F (nonZeroDivisors O)
  exact nonempty_cptOver_of_flat_preimmersion Y U hU

end GlobalTheory.CompanionTheory.Ar.Flat
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.NumberFieldIntegersInIntegrallyClosedStatement
section
open CategoryTheory AlgebraicGeometry NumberField MvPolynomial GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.HT ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.number_field_integers_in_integrally_closed : ∀ (A Ω : Type) [CommRing A] [IsDomain A] [Field Ω] [Algebra A Ω] [IsFractionRing A Ω] [IsIntegrallyClosed A] (E : Type) [Field E] [NumberField E] (σ : E →+* Ω) (a : 𝓞 E), σ (a : E) ∈ (algebraMap A Ω).range := by
  first | exact @GlobalTheory.CompanionTheory.Ar.IntEmb.ringOfIntegers_embedding_mem_range | exact GlobalTheory.CompanionTheory.Ar.IntEmb.ringOfIntegers_embedding_mem_range | (intros; apply GlobalTheory.CompanionTheory.Ar.IntEmb.ringOfIntegers_embedding_mem_range <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.PredualVectorBundle
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar

def preDualBasis {Ω : Type} [Field Ω] {V : Type} [AddCommGroup V] [Module Ω V] [FiniteDimensional Ω V] {r : ℕ}
    (B : Module.Basis (Fin r) Ω (Module.Dual Ω V)) : Module.Basis (Fin r) Ω V :=
  B.dualBasis.map (Module.evalEquiv Ω V).symm

theorem apply_preDualBasis {Ω : Type} [Field Ω] {V : Type} [AddCommGroup V] [Module Ω V] [FiniteDimensional Ω V]
    {r : ℕ} (B : Module.Basis (Fin r) Ω (Module.Dual Ω V)) (i j : Fin r) :
    B i (preDualBasis B j) = if i = j then 1 else 0 := by
  have h : ∀ x : Module.Dual Ω (Module.Dual Ω V), B i ((Module.evalEquiv Ω V).symm x) = x (B i) := by
    intro x
    obtain ⟨y, rfl⟩ := (Module.evalEquiv Ω V).surjective x
    rw [LinearEquiv.symm_apply_apply]
    rfl
  rw [preDualBasis, Module.Basis.map_apply, h, Module.Basis.dualBasis_apply_self]

theorem sum_apply_smul_preDualBasis {Ω : Type} [Field Ω] {V : Type} [AddCommGroup V] [Module Ω V]
    [FiniteDimensional Ω V] {r : ℕ} (B : Module.Basis (Fin r) Ω (Module.Dual Ω V)) (v : V) :
    ∑ i, B i v • preDualBasis B i = v := by
  have hc : ∀ i, (preDualBasis B).coord i = B i := by
    intro i
    refine (preDualBasis B).ext (fun j => ?_)
    rw [Module.Basis.coord_apply, Module.Basis.repr_self, apply_preDualBasis, Finsupp.single_apply]
    by_cases h : i = j
    · subst h
      simp
    · rw [if_neg h, if_neg (Ne.symm h)]
  conv_rhs => rw [← (preDualBasis B).sum_repr v]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [← Module.Basis.coord_apply, hc]

theorem Lat.predualIn_isFrameAt {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Sp Ω ⟶ X} {Li : Type} [AddCommGroup Li]
    [Module Ω Li] {L : Lat ξ (Module.Dual Ω Li)} {V : Submodule Ω Li} [FiniteDimensional Ω V] {r : ℕ}
    (B : Module.Basis (Fin r) Ω (Module.Dual Ω V)) {q : Cpt ξ}
    (h : (L.map V.dualRestrict) q = Submodule.span (regAt ξ q) (Set.range B)) :
    (L.predualIn V).IsFrameAt (fun j => (preDualBasis B j : Li)) q := by
  have hB : ∀ i, ∃ w ∈ L q, V.dualRestrict w = B i := by
    intro i
    have hi : B i ∈ (L.map V.dualRestrict) q := by
      rw [h]
      exact Submodule.subset_span (Set.mem_range_self i)
    obtain ⟨w, hw, hwe⟩ := (Submodule.mem_map).mp hi
    exact ⟨w, hw, hwe⟩
  have hw : ∀ w ∈ L q, ∀ j, w (preDualBasis B j : Li) ∈ regAt ξ q := by
    intro w hwL j
    have hm : V.dualRestrict w ∈ (L.map V.dualRestrict) q := Submodule.mem_map_of_mem hwL
    rw [h] at hm
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun _).mp hm
    have hj : (∑ i, c i • B i) (preDualBasis B j) = w (preDualBasis B j : Li) := by
      rw [hc]
      rfl
    have hj' : (∑ i, c i • B i) (preDualBasis B j) = (c j : Ω) := by
      rw [LinearMap.sum_apply]
      simp only [LinearMap.smul_apply, apply_preDualBasis]
      rw [Finset.sum_eq_single j]
      · rw [if_pos rfl, Subring.smul_def, smul_eq_mul, _root_.mul_one]
      · intro b _ hb
        rw [if_neg hb, smul_zero]
      · intro hj0
        exact absurd (Finset.mem_univ j) hj0
    rw [← hj, hj']
    exact (c j).2
  refine ⟨(preDualBasis B).linearIndependent.map' V.subtype (Submodule.ker_subtype V), ?_⟩
  apply le_antisymm
  · intro v hv
    obtain ⟨hvV, hvw⟩ := hv
    have hcoef : ∀ i, B i ⟨v, hvV⟩ ∈ regAt ξ q := by
      intro i
      obtain ⟨w, hwL, hwe⟩ := hB i
      rw [← hwe, Submodule.dualRestrict_apply]
      exact hvw w hwL
    have hv' : v = ∑ i, B i ⟨v, hvV⟩ • (preDualBasis B i : Li) := by
      have hs := congrArg Subtype.val (sum_apply_smul_preDualBasis B ⟨v, hvV⟩)
      rw [Submodule.coe_sum] at hs
      simpa only [Submodule.coe_smul] using hs.symm
    rw [hv']
    refine Submodule.sum_mem _ (fun i _ => ?_)
    have he : B i ⟨v, hvV⟩ • (preDualBasis B i : Li) =
        (⟨B i ⟨v, hvV⟩, hcoef i⟩ : regAt ξ q) • (preDualBasis B i : Li) := rfl
    rw [he]
    exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_range_self i))
  · rw [Submodule.span_le]
    rintro _ ⟨j, rfl⟩
    show (preDualBasis B j : Li) ∈ V ∧ ∀ w ∈ L q, w (preDualBasis B j : Li) ∈ regAt ξ q
    exact ⟨(preDualBasis B j).2, fun w hwL => hw w hwL j⟩

theorem Lat.predualIn_isVBOn : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Sp Ω ⟶ X) (Li : Type) [AddCommGroup Li]
    [Module Ω Li] (L : Lat ξ (Module.Dual Ω Li)) (T : Set (Cpt ξ)) (r : ℕ) (V : Submodule Ω Li)
    [FiniteDimensional Ω V],
    (L.map V.dualRestrict).IsVBOn T r ⊤ → (L.predualIn V).IsVBOn T r V := by
  intro X Ω _ ξ Li _ _ L T r V _ hL p hp
  obtain ⟨U, hpU, b, hbspan, hfr⟩ := hL p hp
  have hli : LinearIndependent Ω b := (hfr p hp hpU).1
  refine ⟨U, hpU, fun j => (preDualBasis (Module.Basis.mk hli hbspan.ge) j : Li), ?_, ?_⟩
  · have he : (fun j => (preDualBasis (Module.Basis.mk hli hbspan.ge) j : Li)) =
        V.subtype ∘ preDualBasis (Module.Basis.mk hli hbspan.ge) := rfl
    rw [he, Set.range_comp, Submodule.span_image, (preDualBasis (Module.Basis.mk hli hbspan.ge)).span_eq,
      Submodule.map_subtype_top]
  · intro q hq hqU
    apply Lat.predualIn_isFrameAt (Module.Basis.mk hli hbspan.ge)
    rw [(hfr q hq hqU).2, Module.Basis.coe_mk]

end GlobalTheory.CompanionTheory.Ar
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.SymplecticPolydiscPeriodBasisStatement
section
open Filter Topology Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.symplectic_polydisc_period_basis : ∀ (n a g : ℕ) (Λ : Type) [AddCommGroup Λ] (L : GlobalTheory.CompanionTheory.Ar.Flat.LogPeriods n a g Λ), ∃ (bas : Module.Basis (Fin g ⊕ Fin g) ℤ Λ) (Q : GroundTheory.Heights₂.Heights.Regular.PeriodPolydisc n a g) (A T0 : (Fin n → ℂ) → Matrix (Fin g) (Fin g) ℂ), (∀ i j, L.E (bas (.inl i)) (bas (.inl j)) = 0 ∧ L.E (bas (.inr i)) (bas (.inr j)) = 0 ∧ L.E (bas (.inl i)) (bas (.inr j)) = if i = j then -1 else 0) ∧ (∀ i j, DifferentiableOn ℂ (fun z => A z i j) (Metric.ball 0 1)) ∧ (A 0).det ≠ 0 ∧ Q.IsTau0Ext T0 ∧ (∀ i, ((Q.B i).map (Int.cast : ℤ → ℝ)).PosSemidef) ∧ (∀ w ∈ GroundTheory.Heights₂.Heights.Regular.logCover L.a_le, ∀ i k, L.P w (bas (.inl i)) k = A (GroundTheory.Heights₂.Heights.Regular.expCover a w) i k) ∧ ∀ w ∈ GroundTheory.Heights₂.Heights.Regular.logCover L.a_le, ∀ j, L.P w (bas (.inr j)) = ∑ k, Q.τ w j k • L.P w (bas (.inl k)) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.exists_markedPeriods_frame | exact GlobalTheory.CompanionTheory.Ar.Flat.exists_markedPeriods_frame | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.exists_markedPeriods_frame <;> assumption)
end

