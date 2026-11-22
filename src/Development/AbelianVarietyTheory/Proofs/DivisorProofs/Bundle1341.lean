import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1308
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1316
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1265
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0019
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0013
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuasiCompactZeroSec
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1311
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0232
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.T2SpaceFiniteAdeleRing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1284

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusExponentialProjection
section
open Matrix GlobalTheory.TorFin
open scoped ContDiff

noncomputable section

namespace GlobalTheory.TorFin.TorusExp

variable {n : ℕ}

theorem dot_swap {J : Matrix (Fin n) (Fin n) ℂ} (hJ : Jᴴ = J) (u v : Fin n → ℂ) :
    (star u ᵥ* J) ⬝ᵥ v = star ((star v ᵥ* J) ⬝ᵥ u) := by
  rw [← dotProduct_mulVec, star_dotProduct, star_mulVec, hJ]

theorem exp_smul_idem {p : Matrix (Fin n) (Fin n) ℂ} (hp : p * p = p) (a : ℂ) :
    NormedSpace.exp (a • p) = 1 + (Complex.exp a - 1) • p := by
  letI : NormedRing (Matrix (Fin n) (Fin n) ℂ) := Matrix.linftyOpNormedRing
  letI : NormedAlgebra ℂ (Matrix (Fin n) (Fin n) ℂ) := Matrix.linftyOpNormedAlgebra
  letI : NormedAlgebra ℚ (Matrix (Fin n) (Fin n) ℂ) := NormedAlgebra.restrictScalars ℚ ℂ _
  let f : ℂ × ℂ →+* Matrix (Fin n) (Fin n) ℂ :=
    { toFun := fun st => st.1 • p + st.2 • (1 - p)
      map_one' := by simp
      map_mul' := fun s t => by
        simp only [Prod.fst_mul, Prod.snd_mul, add_mul, mul_add, smul_mul_smul_comm, mul_sub, sub_mul, hp,
          mul_one, one_mul, sub_self, smul_zero, add_zero, zero_add, sub_sub_cancel, sub_zero]
      map_zero' := by simp
      map_add' := fun s t => by simp only [Prod.fst_add, Prod.snd_add, add_smul]; abel }
  have hf : Continuous f := by
    show Continuous fun st : ℂ × ℂ => st.1 • p + st.2 • (1 - p)
    fun_prop
  have h1 : f (a, 0) = a • p := by simp [f]
  have h2 := NormedSpace.map_exp f hf (a, 0)
  rw [h1] at h2
  refine Eq.trans h2.symm ?_
  have e1 : (NormedSpace.exp ((a, 0) : ℂ × ℂ)).1 = Complex.exp a := by rw [Prod.fst_exp, Complex.exp_eq_exp_ℂ]
  have e2 : (NormedSpace.exp ((a, 0) : ℂ × ℂ)).2 = 1 := by rw [Prod.snd_exp]; exact NormedSpace.exp_zero
  show (NormedSpace.exp ((a, 0) : ℂ × ℂ)).1 • p + (NormedSpace.exp ((a, 0) : ℂ × ℂ)).2 • (1 - p) = _
  rw [e1, e2, one_smul, sub_smul, one_smul]
  abel

theorem exp_torus (n : ℕ) (J : Matrix (Fin n) (Fin n) ℂ) (hJ : Jᴴ = J) (x y : Fin n → ℂ)
    (hx : (star x ᵥ* J) ⬝ᵥ x = 0) (hy : (star y ᵥ* J) ⬝ᵥ y = 0) (hxy : (star x ᵥ* J) ⬝ᵥ y = 1) (ζ : ℂ) :
    IsSkew J (ζ • projL J x y - star ζ • projL J y x) ∧
      NormedSpace.exp (ζ • projL J x y - star ζ • projL J y x) = torMat J x y (Complex.exp ζ) := by
  have hyx : (star y ᵥ* J) ⬝ᵥ x = 1 := by rw [dot_swap hJ, hxy, star_one]
  have pp : projL J x y * projL J x y = projL J x y := by
    simp only [projL, vecMulVec_mul_vecMulVec, hyx, one_smul]
  have qq : projL J y x * projL J y x = projL J y x := by
    simp only [projL, vecMulVec_mul_vecMulVec, hxy, one_smul]
  have pq : projL J x y * projL J y x = 0 := by
    simp only [projL, vecMulVec_mul_vecMulVec, hy, zero_smul]
    ext i j; simp [vecMulVec]
  have qp : projL J y x * projL J x y = 0 := by
    simp only [projL, vecMulVec_mul_vecMulVec, hx, zero_smul]
    ext i j; simp [vecMulVec]
  have hs : ∀ u v : Fin n → ℂ, (projL J u v)ᴴ * J = J * projL J v u := by
    intro u v
    simp only [projL, conjTranspose_vecMulVec, vecMulVec_mul, mul_vecMulVec, star_vecMul, hJ, star_star]
  refine ⟨?_, ?_⟩
  · unfold IsSkew
    rw [conjTranspose_sub, conjTranspose_smul, conjTranspose_smul, star_star, Matrix.sub_mul, Matrix.smul_mul,
      Matrix.smul_mul, hs, hs, Matrix.mul_sub, Matrix.mul_smul, Matrix.mul_smul]
    abel
  · rw [sub_eq_add_neg, ← neg_smul, Matrix.exp_add_of_commute, exp_smul_idem pp, exp_smul_idem qq]
    · have he : (star (Complex.exp ζ))⁻¹ = Complex.exp (-star ζ) := by
        change (starRingEnd ℂ (Complex.exp ζ))⁻¹ = Complex.exp (-(starRingEnd ℂ ζ))
        rw [← Complex.exp_conj, Complex.exp_neg]
      rw [torMat, he, add_mul, mul_add, mul_add, mul_one, one_mul, smul_mul_smul_comm, pq, smul_zero, add_zero]
      simp only [mul_one]
      abel
    · show Commute _ _
      simp only [Commute, SemiconjBy, smul_mul_smul_comm, pq, qp, smul_zero]

end GlobalTheory.TorFin.TorusExp
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraceDualWeylModuleInvRationalPointEqConjCharAtStatement
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.trace_dualWeylModule_inv_rationalPoint_eq_conj_charAt : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (lam : DomWeight n) (γ : UE E n) (v : InfinitePlace E), LinearMap.trace ℂ _ (GlobalTheory.Branching.sqRep ℂ n lam (GeneralLinearGroup.map v.embedding (γ⁻¹).1)) = starRingEnd ℂ (chAt lam (γ.1.val.charpoly.map v.embedding)) := by
  first | exact @GlobalTheory.ContraChar.trace_sqRep_inv_eq_conj_chAt | exact GlobalTheory.ContraChar.trace_sqRep_inv_eq_conj_chAt | (intros; apply GlobalTheory.ContraChar.trace_sqRep_inv_eq_conj_chAt <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TrivSqZeroExtPinchBasicOpenMorphismUnique
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh GlobalTheory.AbTan
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PinchUniq

section
variable (R : Type) [CommRing R] (B M : Type) [CommRing B] [Algebra R B] [AddCommGroup M] [Module B M]
  [Module Bᵐᵒᵖ M] [IsCentralScalar B M] [Module R M] [IsScalarTower R B M] [Module Rᵐᵒᵖ M] [IsCentralScalar R M]

theorem appTop_joint_inj (β : TrivSqZeroExt R M →+* TrivSqZeroExt B M) (hβ : IsSum β (algebraMap R B) id)
    (c : Γ(Sp (TrivSqZeroExt R M), ⊤))
    (h1 : (spMap (TrivSqZeroExt.fstHom R R M).toRingHom).appTop.hom c = 0)
    (h2 : (spMap β).appTop.hom c = 0) : c = 0 := by
  have n1 := congrArg (fun k => k.hom c)
    (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom (TrivSqZeroExt.fstHom R R M).toRingHom))
  have n2 := congrArg (fun k => k.hom c) (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom β))
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at n1 n2
  have h1' : (Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom R R M).toRingHom)).appTop.hom c = 0 := h1
  have h2' : (Spec.map (CommRingCat.ofHom β)).appTop.hom c = 0 := h2
  rw [h1', map_zero] at n1
  rw [h2', map_zero] at n2
  set c' := (Scheme.ΓSpecIso (CommRingCat.of (TrivSqZeroExt R M))).hom.hom c with hc'
  have e1 : TrivSqZeroExt.fst c' = 0 := n1.symm
  have e2 : TrivSqZeroExt.snd c' = 0 := by
    have : β c' = TrivSqZeroExt.inl (algebraMap R B (TrivSqZeroExt.fst c')) + TrivSqZeroExt.inr (TrivSqZeroExt.snd c') := by
      conv_lhs => rw [← TrivSqZeroExt.inl_fst_add_inr_snd_eq c']
      rw [map_add, hβ.1, hβ.2]; rfl
    have := congrArg TrivSqZeroExt.snd this
    rw [← n2] at this
    simpa using this.symm
  have hc0 : c' = 0 := TrivSqZeroExt.ext e1 e2
  have : c = (Scheme.ΓSpecIso (CommRingCat.of (TrivSqZeroExt R M))).inv.hom c' := by
    rw [hc']; simp
  rw [this, hc0, map_zero]

theorem exists_pow_of_appLE_eq_zero {A : Type} [CommRing A] (s a : Γ(Sp A, ⊤)) (n : ℕ)
    {Y : Scheme.{0}} [IsAffine Y] (f : Y ⟶ Sp A)
    (hf : (f.appLE _ _ le_rfl).hom
      (IsLocalization.mk' Γ(Sp A, (Sp A).basicOpen s) a (⟨s ^ n, n, rfl⟩ : Submonoid.powers s)) = 0) :
    ∃ N : ℕ, f.appTop.hom (s ^ N * a) = 0 := by
  have hspec := IsLocalization.mk'_spec Γ(Sp A, (Sp A).basicOpen s) a (⟨s ^ n, n, rfl⟩ : Submonoid.powers s)
  have h3 : (f.appLE _ _ le_rfl).hom (algebraMap Γ(Sp A, ⊤) Γ(Sp A, (Sp A).basicOpen s) a) = 0 := by
    rw [← hspec, map_mul, hf, zero_mul]
  have h4 : (f.appLE ⊤ (f ⁻¹ᵁ (Sp A).basicOpen s) (by simp)).hom a = 0 := by
    rw [← h3]
    show _ = (((Sp A).presheaf.map (homOfLE le_top).op) ≫ f.appLE _ _ le_rfl).hom a
    rw [Scheme.Hom.map_appLE]
  have hle : Y.basicOpen (f.appTop.hom s) ≤ f ⁻¹ᵁ (Sp A).basicOpen s := (Scheme.preimage_basicOpen_top f s).ge
  have h6 : (f.appLE ⊤ (Y.basicOpen (f.appTop.hom s)) (by simp)).hom a = 0 := by
    rw [← Scheme.Hom.appLE_map (i := (homOfLE hle).op), CommRingCat.comp_apply, h4, map_zero]
    simp
  have h5 : f.appTop.hom a |_ (Y.basicOpen (f.appTop.hom s)) = 0 := h6
  obtain ⟨N, hN⟩ := exists_pow_mul_eq_zero_of_res_basicOpen_eq_zero_of_isAffineOpen Y (isAffineOpen_top Y) _ _ h5
  exact ⟨N, by rw [map_mul, map_pow]; exact hN⟩

theorem appLE_basicOpen_joint_inj (β : TrivSqZeroExt R M →+* TrivSqZeroExt B M) (hβ : IsSum β (algebraMap R B) id)
    (s : Γ(Sp (TrivSqZeroExt R M), ⊤)) (t : Γ(Sp (TrivSqZeroExt R M), (Sp (TrivSqZeroExt R M)).basicOpen s))
    (h1 : ((spMap (TrivSqZeroExt.fstHom R R M).toRingHom).appLE _ _ le_rfl).hom t = 0)
    (h2 : ((spMap β).appLE _ _ le_rfl).hom t = 0) : t = 0 := by
  obtain ⟨⟨a, ⟨_, n, rfl⟩⟩, rfl⟩ := IsLocalization.mk'_surjective (Submonoid.powers s) t
  obtain ⟨N₁, hN₁⟩ := exists_pow_of_appLE_eq_zero s a n _ h1
  obtain ⟨N₂, hN₂⟩ := exists_pow_of_appLE_eq_zero s a n _ h2
  have hc : s ^ (N₁ + N₂) * a = 0 := by
    apply appTop_joint_inj R B M β hβ
    · rw [pow_add, mul_comm (s ^ N₁), _root_.mul_assoc, map_mul, hN₁, mul_zero]
    · rw [pow_add, _root_.mul_assoc, map_mul, hN₂, mul_zero]
  rw [IsLocalization.mk'_eq_zero_iff]
  exact ⟨⟨_, N₁ + N₂, rfl⟩, hc⟩

theorem resLE_appTop_joint_inj (β : TrivSqZeroExt R M →+* TrivSqZeroExt B M) (hβ : IsSum β (algebraMap R B) id)
    (s : Γ(Sp (TrivSqZeroExt R M), ⊤)) (a b : Γ(((Sp (TrivSqZeroExt R M)).basicOpen s).toScheme, ⊤))
    (h1 : ((spMap (TrivSqZeroExt.fstHom R R M).toRingHom).resLE _ _ le_rfl).appTop.hom a =
      ((spMap (TrivSqZeroExt.fstHom R R M).toRingHom).resLE _ _ le_rfl).appTop.hom b)
    (h2 : ((spMap β).resLE _ _ le_rfl).appTop.hom a = ((spMap β).resLE _ _ le_rfl).appTop.hom b) : a = b := by
  have conv : ∀ {Y : Scheme.{0}} (f : Y ⟶ Sp (TrivSqZeroExt R M)) (c : Γ(((Sp (TrivSqZeroExt R M)).basicOpen s).toScheme, ⊤)),
      (f.resLE ((Sp (TrivSqZeroExt R M)).basicOpen s) (f ⁻¹ᵁ (Sp (TrivSqZeroExt R M)).basicOpen s) le_rfl).appTop.hom c =
        (f ⁻¹ᵁ (Sp (TrivSqZeroExt R M)).basicOpen s).topIso.inv.hom
          ((f.appLE _ _ le_rfl).hom (((Sp (TrivSqZeroExt R M)).basicOpen s).topIso.hom.hom c)) := by
    intro Y f c
    rw [Scheme.Hom.appTop, Scheme.Hom.resLE_app_top]
    rfl
  rw [conv, conv] at h1 h2
  replace h1 := congrArg (spMap (TrivSqZeroExt.fstHom R R M).toRingHom ⁻¹ᵁ
    (Sp (TrivSqZeroExt R M)).basicOpen s).topIso.hom.hom h1
  replace h2 := congrArg (spMap β ⁻¹ᵁ (Sp (TrivSqZeroExt R M)).basicOpen s).topIso.hom.hom h2
  simp only [Iso.inv_hom_id_apply] at h1 h2
  have hz := appLE_basicOpen_joint_inj R B M β hβ s
    (((Sp (TrivSqZeroExt R M)).basicOpen s).topIso.hom.hom a - ((Sp (TrivSqZeroExt R M)).basicOpen s).topIso.hom.hom b)
    (by rw [map_sub, h1, sub_self]) (by rw [map_sub, h2, sub_self])
  exact (((Sp (TrivSqZeroExt R M)).basicOpen s).topIso.commRingCatIsoToRingEquiv).injective (sub_eq_zero.mp hz)

end

theorem uniq : ∀ (R : Type) [CommRing R] (B M : Type) [CommRing B] [Algebra R B] [AddCommGroup M] [Module B M] [Module Bᵐᵒᵖ M] [IsCentralScalar B M] [Module R M] [IsScalarTower R B M] [Module Rᵐᵒᵖ M] [IsCentralScalar R M] (β : TrivSqZeroExt R M →+* TrivSqZeroExt B M), IsSum β (algebraMap R B) id → ∀ (X : Scheme.{0}) (x : Sp R ⟶ X) (V : (Sp (TrivSqZeroExt R M)).Opens) (s : Γ((Sp (TrivSqZeroExt R M)), ⊤)), V = (Sp (TrivSqZeroExt R M)).basicOpen s → ∀ (U : X.affineOpens), spMap (TrivSqZeroExt.fstHom R R M).toRingHom ⁻¹ᵁ V ≤ x ⁻¹ᵁ U.1 → ∀ g₁ g₂ : V.toScheme ⟶ X, (spMap (TrivSqZeroExt.fstHom R R M).toRingHom).resLE V _ le_rfl ≫ g₁ = (spMap (TrivSqZeroExt.fstHom R R M).toRingHom ⁻¹ᵁ V).ι ≫ x → (spMap (TrivSqZeroExt.fstHom R R M).toRingHom).resLE V _ le_rfl ≫ g₂ = (spMap (TrivSqZeroExt.fstHom R R M).toRingHom ⁻¹ᵁ V).ι ≫ x → (spMap β).resLE V _ le_rfl ≫ g₁ = (spMap β).resLE V _ le_rfl ≫ g₂ → g₁ = g₂ := by
  intro R _ B M _ _ _ _ _ _ _ _ _ _ β hβ X x V s hV U hU g₁ g₂ h₁ h₂ h₃
  subst hV
  have hrange : ∀ g : ((Sp (TrivSqZeroExt R M)).basicOpen s).toScheme ⟶ X,
      (spMap (TrivSqZeroExt.fstHom R R M).toRingHom).resLE _ _ le_rfl ≫ g =
        (spMap (TrivSqZeroExt.fstHom R R M).toRingHom ⁻¹ᵁ (Sp (TrivSqZeroExt R M)).basicOpen s).ι ≫ x →
      Set.range g ⊆ Set.range U.1.ι := by
    rintro g hg _ ⟨p, rfl⟩
    rw [Scheme.Opens.range_ι]
    obtain ⟨w, hw⟩ := GlobalTheory.Pinch.spMap_fst_surjective R M p.1
    have hwV : w ∈ spMap (TrivSqZeroExt.fstHom R R M).toRingHom ⁻¹ᵁ (Sp (TrivSqZeroExt R M)).basicOpen s := by
      rw [Scheme.Hom.mem_preimage, hw]; exact p.2
    have hp : (spMap (TrivSqZeroExt.fstHom R R M).toRingHom).resLE _ _ le_rfl ⟨w, hwV⟩ = p :=
      Subtype.ext (by rw [Scheme.Hom.coe_resLE_apply]; exact hw)
    rw [← hp]
    change ((spMap (TrivSqZeroExt.fstHom R R M).toRingHom).resLE _ _ le_rfl ≫ g) ⟨w, hwV⟩ ∈ (U.1 : Set X)
    rw [hg]
    exact hU hwV
  haveI : IsAffine U.1.toScheme := U.2
  have f₁ := IsOpenImmersion.lift_fac U.1.ι g₁ (hrange g₁ h₁)
  have f₂ := IsOpenImmersion.lift_fac U.1.ι g₂ (hrange g₂ h₂)
  have ei : (spMap (TrivSqZeroExt.fstHom R R M).toRingHom).resLE _ _ le_rfl ≫ IsOpenImmersion.lift U.1.ι g₁ (hrange g₁ h₁) =
      (spMap (TrivSqZeroExt.fstHom R R M).toRingHom).resLE _ _ le_rfl ≫ IsOpenImmersion.lift U.1.ι g₂ (hrange g₂ h₂) := by
    rw [← cancel_mono U.1.ι, Category.assoc, Category.assoc, f₁, f₂, h₁, h₂]
  have ej : (spMap β).resLE _ _ le_rfl ≫ IsOpenImmersion.lift U.1.ι g₁ (hrange g₁ h₁) =
      (spMap β).resLE _ _ le_rfl ≫ IsOpenImmersion.lift U.1.ι g₂ (hrange g₂ h₂) := by
    rw [← cancel_mono U.1.ι, Category.assoc, Category.assoc, f₁, f₂, h₃]
  have hl : IsOpenImmersion.lift U.1.ι g₁ (hrange g₁ h₁) = IsOpenImmersion.lift U.1.ι g₂ (hrange g₂ h₂) := by
    apply ext_of_isAffine
    ext u
    apply resLE_appTop_joint_inj R B M β hβ s
    · have := congrArg (fun φ => φ.appTop.hom u) ei
      simpa only [Scheme.Hom.comp_appTop, CommRingCat.comp_apply] using this
    · have := congrArg (fun φ => φ.appTop.hom u) ej
      simpa only [Scheme.Hom.comp_appTop, CommRingCat.comp_apply] using this
  rw [← f₁, ← f₂, hl]

end GlobalTheory.PinchUniq
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TrivSqZeroExtPinchExistsExtendBasicOpen
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh GlobalTheory.AbTan
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.Pinch

open TopologicalSpace

theorem appLE_congr_hom {X Y : Scheme.{0}} {φ ψ : X ⟶ Y} (h : φ = ψ) (U : Y.Opens) (V : X.Opens)
    (e : V ≤ φ ⁻¹ᵁ U) (e' : V ≤ ψ ⁻¹ᵁ U) : φ.appLE U V e = ψ.appLE U V e' := by
  subst h; rfl

theorem resLE_comp_of_ringHom {T P X : Scheme.{0}} (V : T.Opens) (hV : IsAffineOpen V) (U : X.affineOpens)
    (ρ : Γ(X, U.1) ⟶ Γ(T, V)) (i : P ⟶ T) (hP : IsAffineOpen (i ⁻¹ᵁ V)) (x : P ⟶ X)
    (hx : i ⁻¹ᵁ V ≤ x ⁻¹ᵁ U.1) (h : ρ ≫ i.appLE V _ le_rfl = x.appLE U.1 _ hx) :
    i.resLE _ _ le_rfl ≫ (hV.isoSpec.hom ≫ Spec.map ρ ≫ U.2.fromSpec) = (i ⁻¹ᵁ V).ι ≫ x := by
  rw [← cancel_epi hP.isoSpec.inv]
  have e1 : hP.isoSpec.inv ≫ i.resLE V _ le_rfl ≫ hV.isoSpec.hom = Spec.map (i.appLE V _ le_rfl) := by
    rw [← cancel_mono hV.isoSpec.inv, ← cancel_mono V.ι]
    simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
    rw [IsAffineOpen.isoSpec_inv_ι, IsAffineOpen.SpecMap_appLE_fromSpec, Scheme.Hom.resLE_comp_ι,
      ← Category.assoc, IsAffineOpen.isoSpec_inv_ι]
  calc hP.isoSpec.inv ≫ i.resLE V _ le_rfl ≫ hV.isoSpec.hom ≫ Spec.map ρ ≫ U.2.fromSpec
      = (hP.isoSpec.inv ≫ i.resLE V _ le_rfl ≫ hV.isoSpec.hom) ≫ Spec.map ρ ≫ U.2.fromSpec := by
        simp only [Category.assoc]
    _ = Spec.map (x.appLE U.1 _ hx) ≫ U.2.fromSpec := by
        rw [e1, ← Category.assoc, ← Spec.map_comp, h]
    _ = hP.isoSpec.inv ≫ (i ⁻¹ᵁ V).ι ≫ x := by
        rw [IsAffineOpen.SpecMap_appLE_fromSpec _ U.2 hP, ← Category.assoc, IsAffineOpen.isoSpec_inv_ι]

theorem exists_glue_of_sections {T P Q X : Scheme.{0}} (i : P ⟶ T) (j : Q ⟶ T)
    (V : T.Opens) (hV : IsAffineOpen V) (hVP : IsAffineOpen (i ⁻¹ᵁ V)) (hVQ : IsAffineOpen (j ⁻¹ᵁ V))
    (U : X.affineOpens) (x : P ⟶ X) (z : Q ⟶ X) (hx : i ⁻¹ᵁ V ≤ x ⁻¹ᵁ U.1) (hz : j ⁻¹ᵁ V ≤ z ⁻¹ᵁ U.1)
    (hinj : ∀ t₁ t₂ : Γ(T, V), i.appLE V (i ⁻¹ᵁ V) le_rfl t₁ = i.appLE V (i ⁻¹ᵁ V) le_rfl t₂ →
      j.appLE V (j ⁻¹ᵁ V) le_rfl t₁ = j.appLE V (j ⁻¹ᵁ V) le_rfl t₂ → t₁ = t₂)
    (hex : ∀ u : Γ(X, U.1), ∃ t : Γ(T, V), i.appLE V (i ⁻¹ᵁ V) le_rfl t = x.appLE U.1 _ hx u ∧
      j.appLE V (j ⁻¹ᵁ V) le_rfl t = z.appLE U.1 _ hz u) :
    ∃ g : V.toScheme ⟶ X, i.resLE _ _ le_rfl ≫ g = (i ⁻¹ᵁ V).ι ≫ x ∧
      j.resLE _ _ le_rfl ≫ g = (j ⁻¹ᵁ V).ι ≫ z := by
  choose ρf hρ using hex
  let ρ : Γ(X, U.1) →+* Γ(T, V) :=
    { toFun := ρf
      map_one' := hinj _ _ (by rw [(hρ 1).1, map_one, map_one]) (by rw [(hρ 1).2, map_one, map_one])
      map_mul' := fun a b => hinj _ _ (by rw [map_mul, (hρ _).1, (hρ _).1, (hρ _).1, map_mul])
        (by rw [map_mul, (hρ _).2, (hρ _).2, (hρ _).2, map_mul])
      map_zero' := hinj _ _ (by rw [(hρ 0).1, map_zero, map_zero]) (by rw [(hρ 0).2, map_zero, map_zero])
      map_add' := fun a b => hinj _ _ (by rw [map_add, (hρ _).1, (hρ _).1, (hρ _).1, map_add])
        (by rw [map_add, (hρ _).2, (hρ _).2, (hρ _).2, map_add]) }
  refine ⟨hV.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom ρ) ≫ U.2.fromSpec, ?_, ?_⟩
  · exact resLE_comp_of_ringHom V hV U _ i hVP x hx (by ext u; exact (hρ u).1)
  · exact resLE_comp_of_ringHom V hV U _ j hVQ z hz (by ext u; exact (hρ u).2)

theorem isLocalization_away_of_eq {Y : Scheme.{0}} [IsAffine Y] (r : Γ(Y, ⊤)) (W : Y.Opens)
    (hW : W = Y.basicOpen r) :
    letI := (Y.presheaf.map (homOfLE le_top : W ⟶ ⊤).op).hom.toAlgebra
    IsLocalization.Away r Γ(Y, W) := by
  subst hW
  exact (isAffineOpen_top Y).isLocalization_basicOpen r

theorem appLE_comp_res {Y Z : Scheme.{0}} (g : Y ⟶ Z) (V : Z.Opens) (W : Y.Opens) (e : W ≤ g ⁻¹ᵁ V) :
    (g.appLE V W e).hom.comp (Z.presheaf.map (homOfLE le_top : V ⟶ ⊤).op).hom =
      (Y.presheaf.map (homOfLE le_top : W ⟶ ⊤).op).hom.comp g.appTop.hom := by
  have h : Z.presheaf.map (homOfLE le_top : V ⟶ ⊤).op ≫ g.appLE V W e =
      g.appTop ≫ Y.presheaf.map (homOfLE le_top : W ⟶ ⊤).op := by
    rw [Scheme.Hom.map_appLE]
    simp only [Scheme.Hom.appLE]
    rfl
  rw [← CommRingCat.hom_comp, ← CommRingCat.hom_comp, h]

theorem appTop_spMap_apply {S S' : Type} [CommRing S] [CommRing S'] (g : S →+* S') (t : Γ(Sp S, ⊤)) :
    (spMap g).appTop.hom t = (Scheme.ΓSpecIso (CommRingCat.of S')).inv.hom
      (g ((Scheme.ΓSpecIso (CommRingCat.of S)).hom.hom t)) := by
  have := congrArg (fun q => q.hom t) (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom g))
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at this
  rw [← this]
  simp

section
variable {R : Type} [CommRing R] {B M : Type} [CommRing B] [Algebra R B] [AddCommGroup M] [Module B M]
  [Module Bᵐᵒᵖ M] [IsCentralScalar B M] [Module R M] [IsScalarTower R B M] [Module Rᵐᵒᵖ M]
  [IsCentralScalar R M] {β : TrivSqZeroExt R M →+* TrivSqZeroExt B M}

theorem sum_apply (hβ : IsSum β (algebraMap R B) id) (a : TrivSqZeroExt R M) :
    β a = TrivSqZeroExt.inl (algebraMap R B a.fst) + TrivSqZeroExt.inr a.snd := by
  conv_lhs => rw [← TrivSqZeroExt.inl_fst_add_inr_snd_eq a]
  rw [map_add, hβ.1, hβ.2]
  rfl

theorem sum_fst (hβ : IsSum β (algebraMap R B) id) (a : TrivSqZeroExt R M) :
    (β a).fst = algebraMap R B a.fst := by
  rw [sum_apply hβ]; simp

theorem sum_snd (hβ : IsSum β (algebraMap R B) id) (a : TrivSqZeroExt R M) :
    (β a).snd = a.snd := by
  rw [sum_apply hβ]; simp

theorem spMap_square (hβ : IsSum β (algebraMap R B) id) :
    spMap (algebraMap R B) ≫ spMap (TrivSqZeroExt.fstHom R R M).toRingHom =
      spMap (TrivSqZeroExt.fstHom B B M).toRingHom ≫ spMap β := by
  simp only [spMap, ← Spec.map_comp]
  congr 1
  ext a
  simp [sum_fst hβ]

end

theorem iso_inv_inj {S S' : CommRingCat.{0}} (e : S ≅ S') {y y' : S'} : e.inv.hom y = e.inv.hom y' ↔ y = y' := by
  constructor
  · intro h
    have := congrArg e.hom.hom h
    simpa using this
  · intro h; rw [h]

theorem exists_extend_basicOpen : ∀ (R : Type) [CommRing R] (B M : Type) [CommRing B] [Algebra R B] [AddCommGroup M] [Module B M] [Module Bᵐᵒᵖ M] [IsCentralScalar B M] [Module R M] [IsScalarTower R B M] [Module Rᵐᵒᵖ M] [IsCentralScalar R M] (β : TrivSqZeroExt R M →+* TrivSqZeroExt B M), IsSum β (algebraMap R B) id → ∀ (X : Scheme.{0}) (x : Sp R ⟶ X) (z : Sp (TrivSqZeroExt B M) ⟶ X), spMap (TrivSqZeroExt.fstHom B B M).toRingHom ≫ z = spMap (algebraMap R B) ≫ x → ∀ (s : Γ((Sp (TrivSqZeroExt R M)), ⊤)) (U : X.affineOpens), spMap (TrivSqZeroExt.fstHom R R M).toRingHom ⁻¹ᵁ (Sp (TrivSqZeroExt R M)).basicOpen s ≤ x ⁻¹ᵁ U.1 → ∃ g : ((Sp (TrivSqZeroExt R M)).basicOpen s).toScheme ⟶ X, (spMap (TrivSqZeroExt.fstHom R R M).toRingHom).resLE _ _ le_rfl ≫ g = (spMap (TrivSqZeroExt.fstHom R R M).toRingHom ⁻¹ᵁ (Sp (TrivSqZeroExt R M)).basicOpen s).ι ≫ x ∧ (spMap β).resLE _ _ le_rfl ≫ g = (spMap β ⁻¹ᵁ (Sp (TrivSqZeroExt R M)).basicOpen s).ι ≫ z := by
  intro R _ B M _ _ _ _ _ _ _ _ _ _ β hβ X x z hxz s U hx
  have hsq := spMap_square hβ
  have hpt : ∀ w : Sp B, (spMap (TrivSqZeroExt.fstHom R R M).toRingHom) ((spMap (algebraMap R B)) w) =
      (spMap β) ((spMap (TrivSqZeroExt.fstHom B B M).toRingHom) w) := fun w => by
    have := congrArg (fun q : Sp B ⟶ Sp (TrivSqZeroExt R M) => q w) hsq
    simpa using this
  have hz : spMap β ⁻¹ᵁ (Sp (TrivSqZeroExt R M)).basicOpen s ≤ z ⁻¹ᵁ U.1 := by
    intro q hq
    obtain ⟨w, rfl⟩ := spMap_fst_surjective B M q
    have h1 : (spMap (algebraMap R B)) w ∈
        spMap (TrivSqZeroExt.fstHom R R M).toRingHom ⁻¹ᵁ (Sp (TrivSqZeroExt R M)).basicOpen s := by
      rw [Scheme.Hom.mem_preimage, hpt]; exact hq
    have h2 := hx h1
    rw [Scheme.Hom.mem_preimage] at h2 ⊢
    have e : z ((spMap (TrivSqZeroExt.fstHom B B M).toRingHom) w) = x ((spMap (algebraMap R B)) w) := by
      have := congrArg (fun q : Sp B ⟶ X => q w) hxz
      simpa using this
    rw [e]; exact h2
  have hW : spMap (algebraMap R B) ⁻¹ᵁ (spMap (TrivSqZeroExt.fstHom R R M).toRingHom ⁻¹ᵁ
      (Sp (TrivSqZeroExt R M)).basicOpen s) ≤
      spMap (TrivSqZeroExt.fstHom B B M).toRingHom ⁻¹ᵁ (spMap β ⁻¹ᵁ (Sp (TrivSqZeroExt R M)).basicOpen s) := by
    intro w hw
    simp only [Scheme.Hom.mem_preimage] at hw ⊢
    rw [← hpt]; exact hw
  have hV : IsAffineOpen ((Sp (TrivSqZeroExt R M)).basicOpen s) := (isAffineOpen_top _).basicOpen s
  have hVP : IsAffineOpen (spMap (TrivSqZeroExt.fstHom R R M).toRingHom ⁻¹ᵁ (Sp (TrivSqZeroExt R M)).basicOpen s) := by
    rw [Scheme.preimage_basicOpen]; exact (isAffineOpen_top _).basicOpen _
  have hVQ : IsAffineOpen (spMap β ⁻¹ᵁ (Sp (TrivSqZeroExt R M)).basicOpen s) := by
    rw [Scheme.preimage_basicOpen]; exact (isAffineOpen_top _).basicOpen _
  have hcomm : (spMap (algebraMap R B)).appTop.hom.comp (spMap (TrivSqZeroExt.fstHom R R M).toRingHom).appTop.hom =
      (spMap (TrivSqZeroExt.fstHom B B M).toRingHom).appTop.hom.comp (spMap β).appTop.hom := by
    rw [← CommRingCat.hom_comp, ← CommRingCat.hom_comp, ← Scheme.Hom.comp_appTop, ← Scheme.Hom.comp_appTop, hsq]
  have hinj0 : ∀ a, (spMap (TrivSqZeroExt.fstHom R R M).toRingHom).appTop.hom a = 0 →
      (spMap β).appTop.hom a = 0 → a = 0 := by
    intro a h1 h2
    rw [appTop_spMap_apply, ← map_zero (Scheme.ΓSpecIso _).inv.hom, iso_inv_inj] at h1 h2
    have e : (Scheme.ΓSpecIso (CommRingCat.of (TrivSqZeroExt R M))).hom.hom a = 0 := by
      ext
      · simpa using h1
      · rw [← sum_snd hβ]
        simpa using congrArg TrivSqZeroExt.snd h2
    have := congrArg (Scheme.ΓSpecIso (CommRingCat.of (TrivSqZeroExt R M))).inv.hom e
    simpa using this
  have hsurj0 : ∀ r c, (spMap (algebraMap R B)).appTop.hom r =
      (spMap (TrivSqZeroExt.fstHom B B M).toRingHom).appTop.hom c →
      ∃ a, (spMap (TrivSqZeroExt.fstHom R R M).toRingHom).appTop.hom a = r ∧ (spMap β).appTop.hom a = c := by
    intro r c h
    rw [appTop_spMap_apply, appTop_spMap_apply, iso_inv_inj] at h
    refine ⟨(Scheme.ΓSpecIso (CommRingCat.of (TrivSqZeroExt R M))).inv.hom
      (TrivSqZeroExt.inl ((Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom r) +
        TrivSqZeroExt.inr ((Scheme.ΓSpecIso (CommRingCat.of (TrivSqZeroExt B M))).hom.hom c).snd : TrivSqZeroExt R M), ?_, ?_⟩
    · rw [appTop_spMap_apply]
      simp
    · rw [appTop_spMap_apply]
      have e : β (TrivSqZeroExt.inl ((Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom r) +
          TrivSqZeroExt.inr ((Scheme.ΓSpecIso (CommRingCat.of (TrivSqZeroExt B M))).hom.hom c).snd) =
          (Scheme.ΓSpecIso (CommRingCat.of (TrivSqZeroExt B M))).hom.hom c := by
        rw [map_add, hβ.1, hβ.2]
        ext
        · simpa using h
        · simp
      simp [e]
  letI : Algebra Γ(Sp R, ⊤) Γ(Sp R, spMap (TrivSqZeroExt.fstHom R R M).toRingHom ⁻¹ᵁ
      (Sp (TrivSqZeroExt R M)).basicOpen s) :=
    ((Sp R).presheaf.map (homOfLE le_top : spMap (TrivSqZeroExt.fstHom R R M).toRingHom ⁻¹ᵁ
      (Sp (TrivSqZeroExt R M)).basicOpen s ⟶ ⊤).op).hom.toAlgebra
  letI : Algebra Γ(Sp (TrivSqZeroExt B M), ⊤) Γ(Sp (TrivSqZeroExt B M), spMap β ⁻¹ᵁ
      (Sp (TrivSqZeroExt R M)).basicOpen s) :=
    ((Sp (TrivSqZeroExt B M)).presheaf.map (homOfLE le_top : spMap β ⁻¹ᵁ
      (Sp (TrivSqZeroExt R M)).basicOpen s ⟶ ⊤).op).hom.toAlgebra
  letI : Algebra Γ(Sp B, ⊤) Γ(Sp B, spMap (algebraMap R B) ⁻¹ᵁ (spMap (TrivSqZeroExt.fstHom R R M).toRingHom ⁻¹ᵁ
      (Sp (TrivSqZeroExt R M)).basicOpen s)) :=
    ((Sp B).presheaf.map (homOfLE le_top : spMap (algebraMap R B) ⁻¹ᵁ (spMap (TrivSqZeroExt.fstHom R R M).toRingHom ⁻¹ᵁ
      (Sp (TrivSqZeroExt R M)).basicOpen s) ⟶ ⊤).op).hom.toAlgebra
  haveI : IsLocalization.Away ((spMap (TrivSqZeroExt.fstHom R R M).toRingHom).appTop.hom s)
      Γ(Sp R, spMap (TrivSqZeroExt.fstHom R R M).toRingHom ⁻¹ᵁ (Sp (TrivSqZeroExt R M)).basicOpen s) :=
    isLocalization_away_of_eq _ _ (Scheme.preimage_basicOpen _ s)
  haveI : IsLocalization.Away ((spMap β).appTop.hom s)
      Γ(Sp (TrivSqZeroExt B M), spMap β ⁻¹ᵁ (Sp (TrivSqZeroExt R M)).basicOpen s) :=
    isLocalization_away_of_eq _ _ (Scheme.preimage_basicOpen _ s)
  haveI : IsLocalization.Away ((spMap (algebraMap R B)).appTop.hom
      ((spMap (TrivSqZeroExt.fstHom R R M).toRingHom).appTop.hom s))
      Γ(Sp B, spMap (algebraMap R B) ⁻¹ᵁ (spMap (TrivSqZeroExt.fstHom R R M).toRingHom ⁻¹ᵁ
      (Sp (TrivSqZeroExt R M)).basicOpen s)) :=
    isLocalization_away_of_eq _ _ (by rw [Scheme.preimage_basicOpen _ s, Scheme.preimage_basicOpen]; rfl)
  haveI : IsLocalization.Away s Γ(Sp (TrivSqZeroExt R M), (Sp (TrivSqZeroExt R M)).basicOpen s) :=
    (isAffineOpen_top _).isLocalization_basicOpen s
  have key := GlobalTheory.T.localization_preserves_ring_pullback_square _ _ _ _ hcomm hinj0 hsurj0 s
    Γ(Sp (TrivSqZeroExt R M), (Sp (TrivSqZeroExt R M)).basicOpen s)
    Γ(Sp R, spMap (TrivSqZeroExt.fstHom R R M).toRingHom ⁻¹ᵁ (Sp (TrivSqZeroExt R M)).basicOpen s)
    Γ(Sp (TrivSqZeroExt B M), spMap β ⁻¹ᵁ (Sp (TrivSqZeroExt R M)).basicOpen s)
    Γ(Sp B, spMap (algebraMap R B) ⁻¹ᵁ (spMap (TrivSqZeroExt.fstHom R R M).toRingHom ⁻¹ᵁ
      (Sp (TrivSqZeroExt R M)).basicOpen s))
    ((spMap (TrivSqZeroExt.fstHom R R M).toRingHom).appLE _ _ le_rfl).hom
    ((spMap β).appLE _ _ le_rfl).hom
    ((spMap (algebraMap R B)).appLE _ _ le_rfl).hom
    ((spMap (TrivSqZeroExt.fstHom B B M).toRingHom).appLE _ _ hW).hom
    (appLE_comp_res _ _ _ _) (appLE_comp_res _ _ _ _) (appLE_comp_res _ _ _ _) (appLE_comp_res _ _ _ _)
  refine exists_glue_of_sections _ _ _ hV hVP hVQ U x z hx hz ?_ ?_
  · intro t₁ t₂ h1 h2
    rw [← sub_eq_zero]
    refine key.1 _ ?_ ?_
    · rw [map_sub, h1, sub_self]
    · rw [map_sub, h2, sub_self]
  · intro u
    refine key.2 _ _ ?_
    have e1 := Scheme.Hom.appLE_comp_appLE (spMap (algebraMap R B)) x U.1 _ _ hx le_rfl
    have e2 := Scheme.Hom.appLE_comp_appLE (spMap (TrivSqZeroExt.fstHom B B M).toRingHom) z U.1 _ _ hz hW
    have e3 := appLE_congr_hom hxz.symm U.1
      (spMap (algebraMap R B) ⁻¹ᵁ (spMap (TrivSqZeroExt.fstHom R R M).toRingHom ⁻¹ᵁ
        (Sp (TrivSqZeroExt R M)).basicOpen s)) (fun w hw => hx hw) (fun w hw => hz (hW hw))
    have := congrArg (fun q => q.hom u) (e1.trans (e3.trans e2.symm))
    simp only [CommRingCat.hom_comp, RingHom.comp_apply] at this
    exact this

end GlobalTheory.Pinch
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedOrbitalIntegralPointTermDoubleCosetInvariStatement
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twistedOrbitalIntegralPointTerm_doubleCoset_invariant : ∀ {G : Type} [Group G] [TopologicalSpace G] (θ : G →* G) (K : Subgroup G) (δ : G) (f : G → ℂ), (∀ a ∈ twCent θ δ, ∀ b ∈ twCent θ δ, a * b = b * a) → (∀ y : G, (rStab fun k : K => f ((y * k)⁻¹ * δ * θ (y * k))).index ≠ 0) → ∀ t ∈ twCent θ δ, ∀ y, ∀ k ∈ K, GlobalTheory.EulerAbs.twTerm θ K δ f (t * y * k) = GlobalTheory.EulerAbs.twTerm θ K δ f y := by
  first | exact @GlobalTheory.EulerAbs.twTerm_inv | exact GlobalTheory.EulerAbs.twTerm_inv | (intros; apply GlobalTheory.EulerAbs.twTerm_inv <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedOrbitalIntegralPointTermOneUnramifiedStatement
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twistedOrbitalIntegralPointTerm_one_unramified : ∀ {G : Type} [Group G] [TopologicalSpace G] (θ : G →* G) (K : Subgroup G) (δ : G), (∀ k ∈ K, θ k ∈ K) → δ ∈ K → cptPart (twCent θ δ) ≤ K → GlobalTheory.EulerAbs.twTerm θ K δ ((K : Set G).indicator 1) 1 = 1 := by
  first | exact @GlobalTheory.EulerAbs.twTerm_one_eq_one | exact GlobalTheory.EulerAbs.twTerm_one_eq_one | (intros; apply GlobalTheory.EulerAbs.twTerm_one_eq_one <;> assumption)
end

