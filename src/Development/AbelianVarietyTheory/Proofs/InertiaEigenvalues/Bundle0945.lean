import Mathlib
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0192
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ArithmeticCMKnownTheoremsProof
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle0058
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ObjMapUniqueOfIsDominant
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0043
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0940
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0021
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0042
import Development.AbelianVarietyTheory.Definitions.ThetaValues.ExistsRootNotMem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMapOfOfExtends
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0006
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0939
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0249
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0936
import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.FinPartDetAtInvInt
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0122
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsDecompChainSpaceDefiniteAddNormalFrame
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnivChar
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0028
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SubsetTwistExceptionalPlaces
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0716
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0825
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0810
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0829
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0010
import Formalism.LocalToGlobal.Columns.MtAdWt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousCoeffBlockAct
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0938
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AlgWeightContragredientExistsUnique
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0941
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0933
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0822
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0030
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0821

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsObjMapOfCoprime
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory.CoverExp

open GlobalTheory.UnifPoint

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {g : ℕ}

theorem exists_sabMap_types {D D₁ D₂ : Datum H}
    {l : Level H} {b : Base l ℂ} {s : Sp ℂ ⟶ Sp ℂ} (o₁ o₂ : Obj D l b s)
    {ty₁ ty₂ : Fin g → (E →+* ℂ)} {P₁ : D₁.La →+ (Fin g → ℂ)} {P₂ : D₂.La →+ (Fin g → ℂ)} (hP₁ : IsPeriod D₁ ty₁ P₁)
    (hP₂ : IsPeriod D₂ ty₂ P₂) {e₁ : (Fin g → ℂ) → (𝟙_ (Over (Sp ℂ)) ⟶ o₁.t.G)}
    {e₂ : (Fin g → ℂ) → (𝟙_ (Over (Sp ℂ)) ⟶ o₂.t.G)} (a₁ : ∀ z w, e₁ (z + w) = e₁ z * e₁ w)
    (s₁ : Function.Surjective e₁) (s₂ : Function.Surjective e₂)
    (r₁ : ReadsPeriods o₁.t unitOn D₁ ty₁ P₁ e₁) (r₂ : ReadsPeriods o₂.t unitOn D₂ ty₂ P₂ e₂)
    (u₁ : ∀ (g₀ : ℕ) (u : HolUnif o₁.t.G o₁.t.PP.L g₀),
      ∃ h : (Fin g₀ → ℂ) ≃ₗ[ℂ] (Fin g → ℂ), ∀ z, e₁ (h z) = u.ex z)
    (u₂ : ∀ (g₀ : ℕ) (u : HolUnif o₂.t.G o₂.t.PP.L g₀),
      ∃ h : (Fin g₀ → ℂ) ≃ₗ[ℂ] (Fin g → ℂ), ∀ z, e₂ (h z) = u.ex z)
    (gam : D₁.La ≃ₗ[𝓞 E] D₂.La) (h : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ))
    (hEF : ∀ a b, D₂.EF (gam a) (gam b) = D₁.EF a b) (hh : ∀ a, P₂ (gam a) = h (P₁ a)) :
    ∃ m : SABMap o₁.t o₂.t (𝟙 _), ∀ z, (e₁ z).left ≫ m.φ = (e₂ (h z)).left := by
  have hT := GlobalTheory.ArcCM.known_holds.theta
  have hL := GlobalTheory.ArcCM.known_holds.laws
  have hG := hL.globalFns
  have hA : HomAlg := GlobalTheory.exists_isMonHom_of_map_lattice hT hL
  have hD : WeilDet := GlobalTheory.T.lambdaBundleIso_of_primeToP_weilPairings hL
  have p₁ := GlobalTheory.obj_isAbelianScheme_dim_rigidified_sym E H D l _ _ _ _ o₁
  have p₂ := GlobalTheory.obj_isAbelianScheme_dim_rigidified_sym E H D l _ _ _ _ o₂
  obtain ⟨α, hα, hα'⟩ : ∃ α : o₁.t.G ⟶ o₂.t.G, IsMonHom α ∧ ∀ z, e₂ (h z) = e₁ z ≫ α :=
    exists_hom hT hA (objPol o₁ p₁) (objPol o₂ p₂) rfl u₁ u₂ h.toLinearMap fun z hz => by
      obtain ⟨a, rfl⟩ := (r₁.1 z).1 hz
      exact (r₂.1 _).2 ⟨gam a, hh a⟩
  obtain ⟨β, -, hβ'⟩ : ∃ β : o₂.t.G ⟶ o₁.t.G, IsMonHom β ∧ ∀ z, e₁ (h.symm z) = e₂ z ≫ β :=
    exists_hom hT hA (objPol o₂ p₂) (objPol o₁ p₁) rfl u₂ u₁ h.symm.toLinearMap fun z hz => by
      obtain ⟨a, rfl⟩ := (r₂.1 z).1 hz
      refine (r₁.1 _).2 ⟨gam.symm a, h.injective ?_⟩
      rw [← hh, gam.apply_symm_apply]
      exact (h.apply_symm_apply _).symm
  have := p₁.1.smooth
  have := p₂.1.smooth
  have := p₁.1.proper
  have := p₂.1.proper
  have : IsReduced o₁.t.G.left := isReduced_of_smooth_complex _ o₁.t.G.hom inferInstance
  have : IsReduced o₂.t.G.left := isReduced_of_smooth_complex _ o₂.t.G.hom inferInstance
  let ψ : o₁.t.G ≅ o₂.t.G :=
    { hom := α
      inv := β
      hom_inv_id := ComplexPoints.over_hom_ext_of_complexPoints fun x => by
        obtain ⟨z, rfl⟩ := s₁ x
        rw [← Category.assoc, ← hα', ← hβ', h.symm_apply_apply, Category.comp_id]
      inv_hom_id := ComplexPoints.over_hom_ext_of_complexPoints fun x => by
        obtain ⟨z, rfl⟩ := s₂ x
        rw [← Category.assoc, ← hβ', ← hα', h.apply_symm_apply, Category.comp_id] }
  have hcomm : ∀ (a : 𝓞 E) z, h (fun k => ty₁ k (a : E) * z k) = fun k => ty₂ k (a : E) * h z k := fun a z => by
    have k : (h.toLinearMap.restrictScalars ℝ) ∘ₗ LinearMap.mulLeft ℝ (fun k => ty₁ k (a : E)) =
        LinearMap.mulLeft ℝ (fun k => ty₂ k (a : E)) ∘ₗ (h.toLinearMap.restrictScalars ℝ) := by
      refine LinearMap.ext_on_range hP₁.2.2.2.1 fun x => ?_
      show h (fun k => ty₁ k (a : E) * P₁ x k) = fun k => ty₂ k (a : E) * h (P₁ x) k
      rw [← funext (hP₁.1 a x), ← hh, ← hh, map_smul]
      exact funext (hP₂.1 a _)
    exact DFunLike.congr_fun k z
  have hact : ∀ a, o₁.t.act.act a ≫ α = α ≫ o₂.t.act.act a := fun a =>
    ComplexPoints.over_hom_ext_of_complexPoints fun x => by
      obtain ⟨z, rfl⟩ := s₁ x
      rw [← Category.assoc, ← Category.assoc, ← r₁.2.1, ← hα', ← hα', ← r₂.2.1, hcomm]
  have hlam := hD ℂ (objPol o₁ p₁) (objPol o₂ p₂) α 2 1 hα Nat.prime_two inferInstance
    fun k x y c hk _ hx hy hw => by
      obtain ⟨a, rfl⟩ := exists_div_of_pow a₁ s₁ r₁.1 hk hx
      obtain ⟨a', rfl⟩ := exists_div_of_pow a₁ s₁ r₁.1 hk hy
      have w := r₁.2.2 k a a' (Units.mk0 _ (Complex.exp_ne_zero _)) hk rfl
      obtain rfl := weilIs_unique_fieldPoint _ _ _ o₁.t.PP.isLB ℂ (𝟙 _) k _ _ _ _ hw w
      have w' := r₂.2.2 k (gam a) (gam a') (Units.mk0 _ (Complex.exp_ne_zero _)) hk rfl
      rw [hh, hh, ← map_smul h, ← map_smul h, hα', hα', hEF] at w'
      rw [pow_one]
      exact w'
  have : IsMonHom ψ.hom := hα
  exact ⟨⟨CubeMap.ofHom α, isGrpPullback_of_iso ψ, rfl, fun a => congrArg (fun z => z.left) (hact a),
    HeckePoint.isPullCubical_of_iso hG p₁.1 α o₁.t.cub o₂.t.cub (HeckePoint.iso_of_lam o₁.t o₂.t α hact hlam)⟩,
    fun z => congrArg (fun q => q.left) (hα' z).symm⟩

theorem exists_objMap_of_coprime {D : Datum H} {l : Level H} (hA : l.A = 1) {B : Type} [CommRing B] {b : Base l B}
    {S : Scheme.{0}} {s : S ⟶ Sp B} (o₁ o₂ : Obj D l b s) (m : SABMap o₁.t o₂.t (𝟙 S)) (J : Ideal (𝓞 E))
    (hJ : l.Mb ⊔ J = ⊤)
    (h₁ : ∀ a ∈ J • (⊤ : Submodule (𝓞 E) D.La), (o₁.eta a).left ≫ m.φ = (o₂.eta a).left)
    (h₂ : (1 : 𝟙_ (Over S) ⟶ o₁.t.G).left ≫ m.φ = (1 : 𝟙_ (Over S) ⟶ o₂.t.G).left) :
    ∃ n : ObjMap o₁ o₂ (𝟙 S), n.toSABMap.φ = m.φ := by
  refine ⟨⟨m, fun a => ?_, fun a => ?_⟩, rfl⟩
  · have ha : a ∈ l.Mb • (⊤ : Submodule (𝓞 E) D.La) ⊔ J • (⊤ : Submodule (𝓞 E) D.La) := by
      rw [← Submodule.sup_smul, hJ, Submodule.top_smul]
      trivial
    obtain ⟨x, hx, y, hy, rfl⟩ := Submodule.mem_sup.1 ha
    rw [o₁.eta_add, o₂.eta_add, o₁.eta_ker x hx, o₂.eta_ker x hx, _root_.one_mul, _root_.one_mul]
    exact (h₁ y hy).trans (Category.id_comp _).symm
  · have c₁ := o₁.etaA_ker a
    have c₂ := o₂.etaA_ker a
    rw [hA, one_smul] at c₁ c₂
    rw [c₁, c₂]
    exact h₂.trans (Category.id_comp _).symm

theorem phi_eq_of_point_eq {D : Datum H} {l : Level H} {B B' : Type} [CommRing B] [CommRing B'] {b : Base l B}
    {b' : Base l B'} {S : Scheme.{0}} {s : S ⟶ Sp B} {s' : Sp ℂ ⟶ Sp B'}
    {o : Obj D l b s} {o₁ : Obj D l b' s'} {y y' : Sp ℂ ⟶ S} (h : y' = y) (m : ObjMap o₁ o y)
    (m' : ObjMap o₁ o y') : m'.toSABMap.φ = m.toSABMap.φ := by
  subst h
  exact objMap_unique_of_field GlobalTheory.ArcCM.known_holds.laws.serre m' m

theorem isExp_family {D : Datum H} {l : Level H} {Xo : Moduli D l} {σ : KA l →+* ℂ} {ty : Fin g → (E →+* ℂ)}
    (F : FamilyUnif Xo σ ty) (i : Fin F.n) {P : (F.Di i).La →+ (Fin g → ℂ)} (hP : IsPeriod (F.Di i) ty P) :
    GlobalTheory.UnifPoint.IsExp (F.ex i P) :=
  ⟨F.ex_add i P hP, F.ex_onto i P hP, GlobalTheory.ArcCM.isHolTo_exp_of_isPeriod F i P hP, (F.ex_diff i P hP).1,
    (F.ex_diff i P hP).2⟩

theorem pow_of_add {V Q : Type} [AddCommGroup V] [Group Q] {e : V → Q} (he : ∀ z w, e (z + w) = e z * e w) (n : ℕ)
    (z : V) : e (n • z) = e z ^ n := by
  induction n with
  | zero =>
    have := he 0 0
    rw [add_zero] at this
    rw [zero_smul, pow_zero]
    exact left_eq_mul.1 this
  | succ n ih => rw [succ_nsmul, he, ih, pow_succ]

theorem ex_comp_eq {D : Datum H} {l l₂ : Level H} {Xo : Moduli D l} {Xo₂ : Moduli D l₂} {r : Xo₂.X ⟶ Xo.X}
    (m : SABMap Xo₂.univ.t Xo.univ.t r) (pd : ℕ) (hA : l.A = 1) (hM : l₂.M = l.M * pd) (hle : l₂.Mb ≤ l.Mb)
    (heta : ∀ a, (Xo₂.univ.eta a ^ pd).left ≫ m.φ = r ≫ (Xo.univ.eta a).left)
    {σ : KA l →+* ℂ} {σ₂ : KA l₂ →+* ℂ} {ty ty₂ : Fin g → (E →+* ℂ)} (F : FamilyUnif Xo σ ty)
    (F₂ : FamilyUnif Xo₂ σ₂ ty₂) (k : Fin F.n) (k₂ : Fin F₂.n) {P : (F.Di k).La →+ (Fin g → ℂ)}
    {P₂ : (F₂.Di k₂).La →+ (Fin g → ℂ)} (hP : IsPeriod (F.Di k) ty P) (hP₂ : IsPeriod (F₂.Di k₂) ty₂ P₂)
    (hy : (F₂.u k₂ P₂ ≫ r) ≫ Xo.s = spMap σ)
    (gam : (F₂.Di k₂).La ≃ₗ[𝓞 E] (F.Di k).La) (h : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ))
    (hEF : ∀ a b, (F.Di k).EF (gam a) (gam b) = (F₂.Di k₂).EF a b)
    (gM : ∀ a ∈ l₂.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) D.La),
      ∃ x, gam (F₂.t k₂ a) = F.t k a + l.M • x)
    (hh : ∀ a, P (gam a) = h (P₂ a)) :
    F₂.u k₂ P₂ ≫ r = F.u k P ∧ ∀ z, (F₂.ex k₂ P₂ z).left ≫ m.φ = (F.ex k P (h z)).left := by
  have hM0 : 0 < l.M := lt_of_lt_of_le (by norm_num) l.three_le
  have hp0 : pd ≠ 0 := fun h0 => by
    have := l₂.three_le
    rw [hM, h0] at this
    omega
  have hy' := F.over_σ k P hP
  obtain ⟨o₁, ⟨m₁⟩⟩ := GlobalTheory.obj_pull E H D l _ ℂ (baseKA l) (baseOfEmb σ) σ _ _ Xo.s (𝟙 _) (F₂.u k₂ P₂ ≫ r) rfl rfl
    (hy.trans (Category.id_comp _).symm) Xo.univ
  obtain ⟨o₂, ⟨m₂⟩⟩ := GlobalTheory.obj_pull E H D l _ ℂ (baseKA l) (baseOfEmb σ) σ _ _ Xo.s (𝟙 _) (F.u k P) rfl rfl
    (hy'.trans (Category.id_comp _).symm) Xo.univ
  obtain ⟨n, hn⟩ := (GlobalTheory.sabMap_cancel_and_comp_over E H _ _ _ _ _ _ r _ (F₂.u k₂ P₂) m m₁.toSABMap rfl).1
  obtain ⟨e₁, f₁, a₁, s₁, r₁, u₁⟩ := exists_fibre_unif n hP₂ (isExp_family F₂ k₂ hP₂)
    ⟨F₂.ex_ker k₂ P₂ hP₂, F₂.ex_lin k₂ P₂ hP₂, F₂.ex_weil k₂ P₂ hP₂⟩
  obtain ⟨e₂, f₂, a₂, s₂, r₂, u₂⟩ := exists_fibre_unif m₂.toSABMap hP (isExp_family F k hP)
    ⟨F.ex_ker k P hP, F.ex_lin k P hP, F.ex_weil k P hP⟩
  obtain ⟨w, hw⟩ := exists_sabMap_types o₁ o₂ hP₂ hP a₁ s₁ s₂ r₁ r₂ u₁ u₂ gam h hEF hh
  have hmap : l₂.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) ≤ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) := Ideal.map_mono hle
  obtain ⟨q, hq⟩ := exists_objMap_of_coprime hA o₁ o₂ w (l₂.Mb.map (H.bar : 𝓞 E →+* 𝓞 E))
    (eq_top_iff.2 (l₂.coprime.symm.le.trans (sup_le_sup_right hle _)))
    (fun a ha => by
      have j₂ := F.ex_eta k P hP a (Submodule.smul_mono_left hmap ha)
      have j₁ : toUnit _ ≫ Xo₂.univ.eta a ^ pd = F₂.ex k₂ P₂ ((l.M : ℂ)⁻¹ • P₂ (F₂.t k₂ a)) := by
        rw [MonObj.comp_pow, F₂.ex_eta k₂ P₂ hP₂ a ha, ← pow_of_add (F₂.ex_add k₂ P₂ hP₂), hM,
          ← Nat.cast_smul_eq_nsmul ℂ, smul_smul, Nat.cast_mul, mul_inv, mul_left_comm,
          mul_inv_cancel₀ (Nat.cast_ne_zero.2 hp0), _root_.mul_one]
      have c₁ : (o₁.eta a).left = (e₁ ((l.M : ℂ)⁻¹ • P₂ (F₂.t k₂ a))).left := by
        refine m₁.cart.1.hom_ext ?_ ((Over.w _).trans (Over.w _).symm)
        refine (m₁.eta a).trans (Eq.trans ?_ (congrArg (_ ≫ ·) hn))
        rw [← Category.assoc (e₁ _).left, f₁, ← j₁, Category.assoc, ← heta]
        exact (Category.assoc _ _ _).symm
      have c₂ : (o₂.eta a).left = (e₂ ((l.M : ℂ)⁻¹ • P (F.t k a))).left :=
        m₂.cart.1.hom_ext ((m₂.eta a).trans ((congrArg (fun q => q.left) j₂).trans (f₂ _).symm))
          ((Over.w _).trans (Over.w _).symm)
      rw [c₁, c₂, hw, map_smul h, ← hh, (div_eq_iff hP.2.1 a₂ r₂.1 hM0 _ _).2 (gM a ha)])
    (by
      have := hw 0
      rwa [map_zero, (r₁.1 0).2 (zero_mem _), (r₂.1 0).2 (zero_mem _)] at this)
  obtain ⟨q', hq'⟩ := ((GlobalTheory.ObjMaps.id_comp_cancel E H D l _ _ _ _ _ _ _ _ _ _ _ _ Xo.univ o₂ o₁).2 (F.u k P)
    (𝟙 _) m₂).1 q
  have hyy : F₂.u k₂ P₂ ≫ r = 𝟙 _ ≫ F.u k P :=
    (GlobalTheory.moduli_rep_of_base GlobalTheory.ObjMaps.id_comp_cancel E H D l Xo ℂ (baseOfEmb σ) σ _ (𝟙 _) o₁ inferInstance rfl
      rfl).unique ⟨hy.trans (Category.id_comp _).symm, ⟨m₁⟩⟩
      ⟨by rw [Category.id_comp, hy', Category.id_comp], ⟨q'⟩⟩
  have hφ := phi_eq_of_point_eq hyy.symm m₁ q'
  refine ⟨hyy.trans (Category.id_comp _), fun z => ?_⟩
  rw [← f₁, ← f₂, ← hw, Category.assoc, Category.assoc, hn, ← hq, ← hq', hφ]

end GlobalTheory.CoverExp
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GaloisConjClassScalarsAndVolumeStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ConjTwist GlobalTheory.GalTw ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.galoisConj_classScalars_and_volume : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec), GlobalTheory.Hk3.Core R F → Nonempty (FWTie T R κ v₀) → ∀ (i : Fin D.R.m) (Tp : Type) (tup : Tp → T0) (M : OMDat T.toCore R i Tp tup), M.Pins (κ i) (v₀ i (sg0 D A)) (iotaW T i) (T.x₀ ((i : ℕ) + 1) M.s0) → ∀ (τ : ℂ ≃+* ℂ) (ta : M.c'.F ≃+* M.c'.F), (∀ a : M.c'.F, ((ta a : M.c'.F) : ℂ) = τ (a : ℂ)) → FixBase T R i τ → ∀ (a b : Tp) (e : M.Cl' a ≃ M.Cl' b), SameCover M a b e → ConjTup R τ (tup a) (tup b) → ta (M.vol a) = M.vol b ∧ ∀ k, ta (M.ep a k) = M.ep b (e k) := by
  first | exact @GlobalTheory.ConjScalar.conj_vol_ep | exact GlobalTheory.ConjScalar.conj_vol_ep | (intros; apply GlobalTheory.ConjScalar.conj_vol_ep <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HeckeCharacterValueAtConjugatePlacePowStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ConjTwist GlobalTheory.GalTw ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heckeCharacter_value_at_conjugatePlace_pow : ∀ (D : D7) (PP : Pl D.host.E) (e : AE D) (ϖ : 𝓞 D.host.E) (c : (AE D)ˣ →* Circle) (χ : Formalism.L2.Host.HChar D.host.E) (n : ℕ) (y : (AE D)ˣ), Formalism.L2.NTheta.IsIdemAt e PP → ϖ ∈ PP.asIdeal → ϖ ∉ PP.asIdeal ^ 2 → ChrEq c χ → χ.UnrAt (Formalism.L2.DIV.conjPl PP) → (y : AE D) = 1 + cA D e * (incA D (star (ϖ : D.host.E)) ^ n - 1) → ((c y : Circle) : ℂ) = ((χ.val (Formalism.L2.DIV.conjPl PP) : ℂˣ) : ℂ) ^ n := by
  first | exact @GlobalTheory.ConjLocVal.value_at_conj_place | exact GlobalTheory.ConjLocVal.value_at_conj_place | (intros; apply GlobalTheory.ConjLocVal.value_at_conj_place <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsAlgWeightOfContragredientHighestWeight
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.StandardLattice Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2 Formalism.L2.Host Formalism.L2.DIV Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.TwInputs GlobalTheory.SeriesTie GlobalTheory.ExportSeries NumberField IsDedekindDomain
open Formalism.MainNotions.IntegralHeckeForms (TwOK)
open Formalism.AUTREP (GAf)
open GlobalTheory.FormInner (frameEquiv)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

namespace GlobalTheory.AlgWtDualRead

theorem isAlgWeight_of_hwAtF_dual : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (K : Type) [Field K] (e : K →+* ℂ) (c : L →+* L), (∀ x, c x = IsCMField.complexConj L x) → ∀ (W : Type) [AddCommGroup W] [Module K W] [FiniteDimensional K W] (ρ : Representation K (ReciprocityTheory.Aut.GQ L n) W) (κ : Type) [Fintype κ] [DecidableEq κ] (b : Module.Basis κ K W) (ρC : Representation ℂ (ReciprocityTheory.Aut.GQ L n) (κ → ℂ)), (∀ γ, LinearMap.toMatrix' (ρC γ) = (LinearMap.toMatrix b b (ρ γ)).map e) → ∀ (τ : L →+* K) (lam : Fin n → ℤ), NX.HWAtF c ρ.dual τ lam → Formalism.AUTREP.IsAlgWeight L n ρC := by
  intro L _ _ _ n K _ e c hc W _ _ _ ρ κ _ _ b ρC hρC τ lam hw
  obtain ⟨ι, _, _, b', P, hP, -⟩ := hw
  classical
  let bd := b.dualBasis
  let A : Matrix κ ι K := bd.toMatrix b'
  let B : Matrix ι κ K := b'.toMatrix bd
  let f : (L →+* K) × Fin n × Fin n → (L →+* K) × Fin n × Fin n := fun p => (p.1.comp c, p.2.2, p.2.1)
  let Q : κ → κ → MvPolynomial ((L →+* K) × Fin n × Fin n) K := fun i j =>
    ∑ l, ∑ k, MvPolynomial.C (A j k) * MvPolynomial.rename f (P k l) * MvPolynomial.C (B l i)
  have key : ∀ (γ : ReciprocityTheory.Aut.GQ L n) (γ₀ : GL (Fin n) L),
      (((γ : Formalism.AUTREP.GAf L n) : GL (Fin n) (ReciprocityTheory.Aut.AL L)) : Matrix (Fin n) (Fin n) (ReciprocityTheory.Aut.AL L)) =
        (γ₀ : Matrix (Fin n) (Fin n) L).map (Algebra.TensorProduct.includeLeftRingHom) →
      ∀ i j, LinearMap.toMatrix b b (ρ γ) i j =
        MvPolynomial.eval (fun p => p.1 ((γ₀ : Matrix (Fin n) (Fin n) L) p.2.1 p.2.2)) (Q i j) := by
    intro γ γ₀ hm i j
    have hinv := hP γ⁻¹ γ₀⁻¹ (GlobalTheory.WtDual.match_inv γ γ₀ hm)
    have hγ := GlobalTheory.WtDual.mem_rationalUnitaryGroup_of_matrix_match γ γ₀ hm
    have e1 : LinearMap.toMatrix bd bd (ρ.dual γ⁻¹) = Matrix.transpose (LinearMap.toMatrix b b (ρ γ)) := by
      rw [Representation.dual_apply, inv_inv, LinearMap.toMatrix_transpose]
    have e2 : LinearMap.toMatrix bd bd (ρ.dual γ⁻¹) = A * LinearMap.toMatrix b' b' (ρ.dual γ⁻¹) * B :=
      (basis_toMatrix_mul_linearMap_toMatrix_mul_basis_toMatrix bd b' bd b' _).symm
    have e3 : LinearMap.toMatrix b b (ρ γ) i j = LinearMap.toMatrix bd bd (ρ.dual γ⁻¹) j i := by
      rw [e1]; rfl
    rw [e3, e2]
    simp only [Matrix.mul_apply, Finset.sum_mul]
    simp only [hinv]
    simp only [Q, map_sum, map_mul, MvPolynomial.eval_C, MvPolynomial.eval_rename]
    refine Finset.sum_congr rfl fun l _ => ?_
    refine Finset.sum_congr rfl fun k _ => ?_
    congr 2
    refine congrArg (fun g => MvPolynomial.eval g (P k l)) (funext fun p => ?_)
    simp only [Function.comp_apply, f, RingHom.comp_apply]
    rw [GlobalTheory.WtDual.inv_entry γ₀ hγ, hc]
    rfl
  refine ⟨inferInstance, κ, inferInstance, inferInstance, Pi.basisFun ℂ κ,
    fun i j => MvPolynomial.rename (fun p : (L →+* K) × Fin n × Fin n => (e.comp p.1, p.2)) (MvPolynomial.map e (Q i j)), ?_⟩
  intro γ γ₀ hm
  ext i j
  rw [LinearMap.toMatrix_eq_toMatrix', hρC γ, Matrix.map_apply, key γ γ₀ hm i j, MvPolynomial.eval_rename,
    MvPolynomial.eval_map]
  simp only [MvPolynomial.eval, MvPolynomial.coe_eval₂Hom, MvPolynomial.hom_eval₂, RingHom.comp_id]
  rfl

end GlobalTheory.AlgWtDualRead
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LevelCharacterApplyEqLevelFunctionSwap
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ExportSeries GlobalTheory.ConjTwist GlobalTheory.SeriesTie.Scale

set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable section

namespace GlobalTheory.MtLatConj

variable {D : D7}

theorem locC_conj {τ : ℂ ≃+* ℂ} {ν ν' : Twist D Circle} (h : ConjChar τ ν ν') (hν : ν.Good) (hν' : ν'.Good)
    (PP : Pl D.host.E) (u : (kP PP)ˣ) : τ ((ν.locC PP u : ℂˣ) : ℂ) = ((ν'.locC PP u : ℂˣ) : ℂ) := by
  classical
  unfold Twist.locC
  by_cases hP : PP ∈ ν.Q
  · have hP' : PP ∈ ν'.Q := by rw [h.1]; exact hP
    rw [if_pos hP, if_pos hP']
    exact (h.res hν hν' hP u).symm
  · have hP' : PP ∉ ν'.Q := by rw [h.1]; exact hP
    rw [if_neg hP, if_neg hP']
    simp

theorem levPOf_ext1_apply_eq_units_map_inv {r : ℕ} {Pg : Finset (Pl D.host.E)} (P : LevelP Pg r ℂ) {τ : ℂ ≃+* ℂ}
    (hP : ∀ p, τ ((P.chi p : ℂˣ) : ℂ) = ((P.chi p : ℂˣ) : ℂ)) (g : G0 Pg r) :
    τ ((Formalism.L2.DIV.ext1 P.H P.chi g : ℂˣ) : ℂ) = ((Formalism.L2.DIV.ext1 P.H P.chi g : ℂˣ) : ℂ) := by
  unfold Formalism.L2.DIV.ext1
  split_ifs
  · exact hP _
  · simp

theorem levFn_conj {S T : HSp D} {B : Base S T} (hB : B.Good) {τ : ℂ ≃+* ℂ} {ψ ψ' : Twist D Circle} (hψ : ψ.Good)
    (hψ' : ψ'.Good) (hcc : ConjChar τ ψ ψ') (hf : FixDat B τ) (x : GL (Fin S.rank) (Lev.EAf D)) :
    τ ((levFn B.F.βS (B.levS ψ) x : ℂˣ) : ℂ) = ((levFn B.F.βS (B.levS ψ') x : ℂˣ) : ℂ) := by
  simp only [levFn, Base.levS, Units.val_mul, Units.coe_prod, map_mul, map_prod]
  rw [hcc.1]
  congr 1
  congr 1
  · exact levPOf_ext1_apply_eq_units_map_inv B.G.P hf.2.1 _
  · refine Finset.prod_congr rfl fun PP hPP => Finset.prod_congr rfl fun c _ => ?_
    exact hf.2.2 PP hPP _
  · refine Finset.prod_congr rfl fun PP _ => ?_
    rw [MonoidHom.mul_apply, MonoidHom.mul_apply, Units.val_mul, Units.val_mul, map_mul,
      locC_conj hf.conjChar hB.de hB.de, locC_conj hcc hψ hψ']

theorem mem_levJ_of {S T : HSp D} (B : Base S T) {ψ ψ' : Twist D Circle} (hQ : ψ'.Q = ψ.Q) {k : Bridge.Gf S}
    (hk : k ∈ B.levJ ψ') : k ∈ B.levJ ψ := by
  simp only [Base.levJ, Subgroup.mem_comap, Lev.toAfE, mem_lev, mem_parLev, Base.levS] at hk ⊢
  rw [hQ] at hk
  exact hk

set_option maxHeartbeats 800000 in
theorem levelCharacter_apply_eq_levelFunction_swap {S T : HSp D} (B : Base S T) (ψ : Twist D Circle) (k : B.levJ ψ) :
    B.levLam ψ k = levFn B.F.βS (B.levS ψ) (Formalism.UG.bc (Lev.swapAE D) k.1.1) := by
  unfold Base.levLam Lev.levCharAfE
  rfl

theorem levLam_conj {S T : HSp D} {B : Base S T} (hB : B.Good) {τ : ℂ ≃+* ℂ} {ψ ψ' : Twist D Circle} (hψ : ψ.Good)
    (hψ' : ψ'.Good) (hcc : ConjChar τ ψ ψ') (hf : FixDat B τ) (k : B.levJ ψ') :
    ((B.levLam ψ' k : ℂˣ) : ℂ) = τ ((B.levLam ψ ⟨k.1, mem_levJ_of B hcc.1 k.2⟩ : ℂˣ) : ℂ) := by
  rw [levelCharacter_apply_eq_levelFunction_swap, levelCharacter_apply_eq_levelFunction_swap]
  exact (levFn_conj hB hψ hψ' hcc hf _).symm

variable {n : ℕ}

def cmapGL (τ : ℂ ≃+* ℂ) : GLR D n →* GLR D n :=
  MonoidHom.pi fun t => (Units.map (RingHom.mapMatrix (τ : ℂ →+* ℂ) : Matrix (Fin n) (Fin n) ℂ →+* _).toMonoidHom).comp
    (Pi.evalMonoidHom (fun _ : D.what₂.Tau => GL (Fin n) ℂ) t)

theorem cmapGL_val (τ : ℂ ≃+* ℂ) (y : GLR D n) (t : D.what₂.Tau) (a b : Fin n) :
    ((cmapGL τ y t : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) a b = τ (((y t : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) a b) := rfl

theorem coefFn_conj (τ : ℂ ≃+* ℂ) (lam : D.what₂.Tau → DomWeight n) (F : Pol ℂ D.what₂.Tau n) (y : GLR D n) :
    coefFn (RingHom.id ℂ) lam (MvPolynomial.map (τ : ℂ →+* ℂ) F) y = τ (coefFn (RingHom.id ℂ) lam F (cmapGL τ.symm y)) := by
  simp only [coefFn, map_mul]
  congr 1
  · simp only [detFam, MonoidHom.coe_mk, OneHom.coe_mk, Units.coe_prod, map_prod, Units.val_zpow_eq_zpow_val, map_zpow₀,
      GeneralLinearGroup.val_det_apply]
    refine Finset.prod_congr rfl fun t _ => ?_
    congr 1
    have e := RingHom.map_det (τ : ℂ →+* ℂ) (((cmapGL τ.symm y t : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ))
    refine Eq.trans ?_ e.symm
    congr 1
    ext a b
    simp [cmapGL_val]
  · simp only [MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_map]
    have e := MvPolynomial.hom_eval₂ F (RingHom.id ℂ) (τ : ℂ →+* ℂ)
      (fun v : D.what₂.Tau × Fin n × Fin n => ((cmapGL τ.symm y v.1 : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) v.2.1 v.2.2)
    refine Eq.trans ?_ e.symm
    congr 1
    funext v
    simp [cmapGL_val]

theorem cmapGL_embGL (τ : ℂ ≃+* ℂ) (hτ : ∀ (t : D.what₂.Tau) (e : D.host.E), τ (tauE D t e) = tauE D t e)
    (g : GL (Fin n) D.host.E) : cmapGL τ (embGL (tauE D) g) = embGL (tauE D) g := by
  funext t
  refine Units.ext (Matrix.ext fun a b => ?_)
  rw [cmapGL_val]
  exact hτ t _

theorem hasLaw_conj {i : Fin D.R.m} {B : Base (Vc D i) (Wc D i)} (hB : B.Good)
    {Φ : VsV D i ℂ →ₗ[ℂ] PolF D (Wc D i).rank (Vc D i).rank} {κ : ℂ} (hκ0 : κ ≠ 0) (hval : ∀ x, Φ x ∈ B.valSpace)
    (hκ : ∀ x : VsV D i ℂ, harmFn (Wc D i).rank B.w B.F.BS (Φ x) =
      κ • coefFn (RingHom.id ℂ) (lamV D i) (x : Pol ℂ D.what₂.Tau (Vc D i).rank))
    {τ : ℂ ≃+* ℂ} (hτE : ∀ (t : D.what₂.Tau) (e : D.host.E), τ.symm (tauE D t e) = tauE D t e)
    {ψ ψ' : Twist D Circle} (hψ : ψ.Good) (hψ' : ψ'.Good) (hcc : ConjChar τ ψ ψ') (hf : FixDat B τ)
    {x x' : Bridge.Gf (Vc D i) → VsV D i ℂ} (hxx : ∀ h, ConjVec i τ (x h) (x' h))
    (hlaw : B.HasLaw ψ (fun h => Φ (x h))) : B.HasLaw ψ' (fun h => Φ ((τ κ / κ) • x' h)) := by
  intro γ h k
  have hfn : ∀ (w : VsV D i ℂ) z, harmFn (Wc D i).rank B.w B.F.BS (Φ w) z = κ * coefLin (lamV D i) w z :=
    fun w z => congrFun (hκ w) z
  obtain ⟨γE, hγ⟩ : ∃ γE, Bridge.IsRatMat (Vc D i) γ γE := by
    obtain ⟨y, -, hy⟩ := γ.2
    exact ⟨y, hy.symm⟩
  set u := realGL B.F.θ (Vc D i) γ with hu_def
  have hu : u = embGL (tauE D) γE := realGL_rat hB.frame.vac.2.inf hγ
  have hact : ∀ P z, harmFn (Wc D i).rank B.w B.F.BS (B.act γ P) z =
      harmFn (Wc D i).rank B.w B.F.BS P (u⁻¹ * z) := fun P z => harmFn_fockGL _ _ _ _ _
  have hfix : ∀ z, cmapGL τ.symm (u⁻¹ * z) = u⁻¹ * cmapGL τ.symm z := by
    intro z
    rw [map_mul, hu, ← map_inv, cmapGL_embGL τ.symm hτE]
  have hconj : ∀ w z, coefLin (lamV D i) (x' w) z = τ (coefLin (lamV D i) (x w) (cmapGL τ.symm z)) := fun w z => by
    change coefFn (RingHom.id ℂ) (lamV D i) (x' w : Pol ℂ D.what₂.Tau (Vc D i).rank) z =
      τ (coefFn (RingHom.id ℂ) (lamV D i) (x w : Pol ℂ D.what₂.Tau (Vc D i).rank) _)
    rw [hxx w]
    exact coefFn_conj τ _ _ z
  set g := Bridge.ratF (Vc D i) γ * h * (k : Bridge.Gf (Vc D i)) with hg
  set lam : ℂ := ((B.levLam ψ ⟨k.1, mem_levJ_of B hcc.1 k.2⟩ : ℂˣ) : ℂ) with hlam
  have hL : Φ (x g) = lam • B.act γ (Φ (x h)) := hlaw γ h ⟨k.1, mem_levJ_of B hcc.1 k.2⟩
  have E1 : ∀ z, coefLin (lamV D i) (x g) z = lam * coefLin (lamV D i) (x h) (u⁻¹ * z) := by
    intro z
    have e1 : harmFn (Wc D i).rank B.w B.F.BS (Φ (x g)) z =
        lam * harmFn (Wc D i).rank B.w B.F.BS (B.act γ (Φ (x h))) z := by
      rw [hL, map_smul]
      rfl
    rw [hact, hfn, hfn] at e1
    apply mul_left_cancel₀ hκ0
    rw [e1]
    ring
  have hl' : ((B.levLam ψ' k : ℂˣ) : ℂ) = τ lam := levLam_conj hB hψ hψ' hcc hf k
  show Φ ((τ κ / κ) • x' g) = ((B.levLam ψ' k : ℂˣ) : ℂ) • B.act γ (Φ ((τ κ / κ) • x' h))
  rw [hl']
  refine sub_eq_zero.1 (GlobalTheory.T.harmonic_polynomial_eq_zero_of_function D _ _ B.w B.F.BS hB.wt (GlobalTheory.CoefLatConj.pq_le hB) _
    (sub_mem (hval _) (Submodule.smul_mem _ _ (Base.act_mem_valSpace _ (hval _)))) ?_)
  funext z
  have e2 : ∀ (P Q : PolF D (Wc D i).rank (Vc D i).rank) (a : ℂ), harmFn (Wc D i).rank B.w B.F.BS (P - a • Q) z =
      harmFn (Wc D i).rank B.w B.F.BS P z - a * harmFn (Wc D i).rank B.w B.F.BS Q z := fun P Q a => by
    rw [map_sub, map_smul]
    rfl
  rw [e2, hact, hfn, hfn, map_smul, map_smul]
  change κ * ((τ κ / κ) * coefLin (lamV D i) (x' g) z) - τ lam * (κ * ((τ κ / κ) * coefLin (lamV D i) (x' h) (u⁻¹ * z))) = 0
  rw [hconj, hconj, hfix, E1, map_mul]
  ring

theorem mtLat_conj : ∀ (D : D7) (i : Fin D.R.m) (B : Base (Vc D i) (Wc D i)), B.Good → B.w.lam = lamV D i → ∀ (Φ : VsV D i ℂ →ₗ[ℂ] PolF D (Wc D i).rank (Vc D i).rank) (κ : ℂ), κ ≠ 0 → (∀ x, Φ x ∈ B.valSpace) → (∀ x : VsV D i ℂ, harmFn (Wc D i).rank B.w B.F.BS (Φ x) = κ • coefFn (RingHom.id ℂ) (lamV D i) (x : Pol ℂ D.what₂.Tau (Vc D i).rank)) → ∀ (K : Type) [Field K] [NumberField K] (σ : K →+* ℂ) (emb : D.what₂.Tau → (D.host.E →+* K)) (O : Subring ℂ), IsCoefRing σ emb O → ∀ τ : ℂ ≃+* ℂ, (∀ a : K, τ (σ a) = σ a) → ∀ (ψ ψ' : Twist D Circle), ψ.Good → ψ'.Good → ConjChar τ ψ ψ' → FixDat B τ → ∀ f f' : Bridge.Gf (Vc D i) → PolF D (Wc D i).rank (Vc D i).rank, (∀ h, ∃ x x' : VsV D i ℂ, ConjVec i τ x x' ∧ f h = Φ x ∧ f' h = Φ ((τ κ / κ) • x')) → f ∈ B.mtLat σ emb O ψ → f' ∈ B.mtLat σ emb (O.map (τ : ℂ →+* ℂ)) ψ' := by
  intro D i B hB hlam Φ κ hκ0 hval hκ K _ _ σ emb O hc τ hτ ψ ψ' hψ hψ' hcc hf f f' hff hfm
  choose x x' hxx hfx hfx' using hff
  have hτE : ∀ (t : D.what₂.Tau) (e : D.host.E), τ.symm (tauE D t e) = tauE D t e := fun t e => by
    rw [← hc.emb t, RingHom.comp_apply, τ.symm_apply_eq, hτ]
  obtain ⟨hform, hlat⟩ := (Base.mem_mtLat B σ emb O).1 hfm
  have hlaw : B.HasLaw ψ (fun h => Φ (x h)) := by
    have e : f = fun h => Φ (x h) := funext hfx
    rw [← e]
    exact ((Base.mem_formsC B).1 hform).2
  have e' : f' = fun h => Φ ((τ κ / κ) • x' h) := funext hfx'
  refine (Base.mem_mtLat B σ emb (O.map (τ : ℂ →+* ℂ))).2 ⟨(Base.mem_formsC B).2 ⟨fun h => (hfx' h).symm ▸ hval _, ?_⟩, fun h => ?_⟩
  · rw [e']
    exact hasLaw_conj hB hκ0 hval hκ hτE hψ hψ' hcc hf hxx hlaw
  · rw [hfx' h]
    exact (GlobalTheory.CoefLatConj.conj_mem_iff Φ hlam hκ0 hval hκ σ emb O τ hτ h (hxx h)).1 (hfx h ▸ hlat h)

end GlobalTheory.MtLatConj
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormLeOneOfMemLocalUnitBallSideStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.L2.Pj GlobalTheory.GeoTie
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.norm_le_one_of_mem_localUnitBall_side : ∀ (D : D7) (Γ : Type) [Group Γ] [Fintype Γ] (Pl0 I0 T1 : Type) (A3 : FamIn3 D.what₂.LL Γ Pl0 I0 (List ℕ) T1 D.R.m) (T0 : CoreJ D) [Algebra T0.Q.c.F D.what₂.LL] (Rl : RealDat3 D A3 T0.Q.c.F) (cG : Formalism.L2.DIV.G0 Rl.Pg D.R.r ≃* G0g D.nd) (S : NX.RatDat D.ntw) (YS : NX.NExpRealS Rl cG S) (κ : ∀ j : Fin D.R.m, WeightFamilies.Wt D ((j : ℕ) + 1)) (v₀ : ∀ (j : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (Rl.MW j σ).Vec) (fw : FWTie T0 Rl.toRealDat κ v₀) (i : D.ntw.Tw) (iC : FractionRing (D.ntw.O i) →+* ℂ_[D.ntw.l i]), (∀ x, ‖iC x‖ ≤ 1 ↔ x ∈ (algebraMap (D.ntw.O i) (FractionRing (D.ntw.O i))).range) → ∀ (b : Bool) (j : Fin D.R.m), ∀ f ∈ locBall YS fw iC b j, ∀ y : (Rl.FW j).Pt (placeC YS iC b), (Rl.FW j).nrm (placeC YS iC b) y ⟨(YS.fi j).e (show ↥(S.A ((j : ℕ) + 1)).WK from f).1, ((YS.fi j).wk _).1 (show ↥(S.A ((j : ℕ) + 1)).WK from f).2⟩ ≤ 1 := by
  first | exact @GlobalTheory.GeoTie.nrm_le_one_of_mem_locBall_pts | exact GlobalTheory.GeoTie.nrm_le_one_of_mem_locBall_pts | (intros; apply GlobalTheory.GeoTie.nrm_le_one_of_mem_locBall_pts <;> assumption)
end

