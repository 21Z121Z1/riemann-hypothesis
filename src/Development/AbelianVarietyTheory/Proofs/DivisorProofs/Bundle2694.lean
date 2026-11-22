import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0080
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0130
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0152
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0006
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0003
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2675
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2577
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2656
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TateUnramifiedOfTorsionUnramified
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0029
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0010
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0009
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2513
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2670
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0587
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsLinearOfIsMonHom
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.LatticeDeterminedByInvariants
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0041
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0141
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsWithoutCohomology
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2540
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0079
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0562
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.PsiCoordExistsUniqueUpToUnitLocal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2581

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EighthPowerProjectionsGroupPullback
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

noncomputable section

namespace GlobalTheory.GrpPullPow

theorem isMonHom_of_mul_pts {S : Scheme.{0}} {G H : Over S} [GrpObj G] [GrpObj H] (f : G ⟶ H)
    (h : ∀ (T : Over S) (x y : T ⟶ G), (x * y) ≫ f = (x ≫ f) * (y ≫ f)) : IsMonHom f where
  one_hom := by
    rw [MonObj.one_eq_one, MonObj.one_eq_one]
    exact map_one (MonoidHom.mk' (fun x : 𝟙_ (Over S) ⟶ G ↦ x ≫ f) (h _))
  mul_hom := by
    rw [MonObj.mul_eq_mul, h, MonObj.mul_eq_mul, MonObj.comp_mul]
    simp

theorem pr_pull : ∀ {T T' : Scheme.{0}} {t : T' ⟶ T} {B C : Over T} [GrpObj B] [GrpObj C] {B' C' : Over T'} [GrpObj B'] [GrpObj C'] {φB : B'.left ⟶ B.left} {χ : C'.left ⟶ C.left} (pr : Fin 8 → (B ⟶ C)), IsGrpPullback B' B t φB → IsGrpPullback C' C t χ → (∀ a, IsMonHom (pr a)) → (∀ (T₁ : Over T) (y : Fin 8 → (T₁ ⟶ C)), ∃! x : T₁ ⟶ B, ∀ a, x ≫ pr a = y a) → ∃ pr' : Fin 8 → (B' ⟶ C'), (∀ a, (pr' a).left ≫ χ = φB ≫ (pr a).left) ∧ (∀ a, IsMonHom (pr' a)) ∧ ∀ (T₁ : Over T') (y : Fin 8 → (T₁ ⟶ C')), ∃! x : T₁ ⟶ B', ∀ a, x ≫ pr' a = y a := by
  intro T T' t B C _ _ B' C' _ _ φB χ pr hB hC hpr huniv
  have hw : ∀ a, (φB ≫ (pr a).left) ≫ C.hom = B'.hom ≫ t := fun a => by
    rw [Category.assoc, Over.w (pr a), hB.1.w]
  let pr' : Fin 8 → (B' ⟶ C') := fun a =>
    Over.homMk (hC.1.lift (φB ≫ (pr a).left) B'.hom (hw a)) (hC.1.lift_snd _ _ _)
  have h1 : ∀ a, (pr' a).left ≫ χ = φB ≫ (pr a).left := fun a => hC.1.lift_fst _ _ _
  have hpush : ∀ (T₁ : Over T') (x : T₁ ⟶ B') a,
      pushPt hC.1.w (x ≫ pr' a) = pushPt hB.1.w x ≫ pr a := by
    intro T₁ x a
    apply Over.OverMorphism.ext
    show (x.left ≫ (pr' a).left) ≫ χ = (x.left ≫ φB) ≫ (pr a).left
    rw [Category.assoc, h1, Category.assoc]
  refine ⟨pr', h1, fun a => ?_, fun T₁ y => ?_⟩
  · haveI := hpr a
    refine isMonHom_of_mul_pts _ fun T₁ x y => ?_
    apply Over.OverMorphism.ext
    apply hC.1.hom_ext
    · have e1 := hC.2 T₁ (x ≫ pr' a) (y ≫ pr' a) (pushPt hC.1.w (x ≫ pr' a))
        (pushPt hC.1.w (y ≫ pr' a)) rfl rfl
      have e2 := hB.2 T₁ x y (pushPt hB.1.w x) (pushPt hB.1.w y) rfl rfl
      rw [← e1, hpush, hpush, ← MonObj.mul_comp, Over.comp_left, Over.comp_left, Category.assoc, h1,
        ← Category.assoc, ← e2]
    · rw [Over.w, Over.w]
  · let T₀ : Over T := Over.mk (T₁.hom ≫ t)
    obtain ⟨x₀, hx₀, hu⟩ := huniv T₀ (fun a => pushPt hC.1.w (y a))
    have wx : x₀.left ≫ B.hom = T₁.hom ≫ t := Over.w x₀
    let X : T₁ ⟶ B' := Over.homMk (hB.1.lift x₀.left T₁.hom wx) (hB.1.lift_snd _ _ _)
    have hX : X.left ≫ φB = x₀.left := hB.1.lift_fst _ _ _
    refine ⟨X, fun a => ?_, fun x' hx' => ?_⟩
    · apply Over.OverMorphism.ext
      apply hC.1.hom_ext
      · show (X.left ≫ (pr' a).left) ≫ χ = (y a).left ≫ χ
        rw [Category.assoc, h1, ← Category.assoc, hX]
        exact congrArg (fun q => q.left) (hx₀ a)
      · rw [Over.w, Over.w]
    · have e : pushPt hB.1.w x' = x₀ := hu _ fun a => by
        rw [← hpush, hx' a]
      apply Over.OverMorphism.ext
      apply hB.1.hom_ext
      · rw [hX]; exact congrArg (fun q => q.left) e
      · rw [Over.w, Over.w]

end GlobalTheory.GrpPullPow
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EisensteinRuleOfQExpansion
section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField
  IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.LatJet
open GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds (IsClassZetaVals)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (IsDefSum polydisc defCoord cWt)

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.EisRuleProof

theorem card_emb (F : Type) [Field F] [NumberField F] [IsTotallyReal F] :
    Fintype.card (F →+* ℝ) = Module.finrank ℚ F := by
  rw [← NumberField.Embeddings.card F ℂ]
  refine Fintype.card_of_bijective (f := fun τ : F →+* ℝ ↦ (Complex.ofRealHom.comp τ : F →+* ℂ)) ⟨?_, ?_⟩
  · intro τ τ' hτ
    ext y
    have := DFunLike.congr_fun hτ y
    simpa using this
  · intro φ
    have hr : NumberField.ComplexEmbedding.IsReal φ := IsTotallyReal.complexEmbedding_isReal φ
    exact ⟨hr.embedding, by ext y; simp⟩

theorem isHolForm_mul {F : Type} [Field F] [NumberField F] {𝔞 𝔟 : FracId F} {k : ℕ}
    {g : ((F →+* ℝ) → ℂ) → ℂ} (h : IsHolForm 𝔞 𝔟 k g) (K : ℂ) : IsHolForm 𝔞 𝔟 k (fun z ↦ K * g z) := by
  refine ⟨h.1.const_mul K, fun a b c d hm z hz ↦ ?_⟩
  simp only
  rw [h.2 a b c d hm z hz]; ring

theorem dF_pos (F : Type) [Field F] [NumberField F] : (0 : ℝ) < GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.dF F := by
  unfold GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.dF
  exact abs_pos.2 (by exact_mod_cast NumberField.discr_ne_zero F)

theorem omegaFactor_ne_zero {F : Type} [Field F] [NumberField F] (𝔞 : FracId F) :
    (GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.omegaFactor 𝔞 : ℂ) ≠ 0 := by
  have hn : GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.nrm 𝔞 ≠ 0 := by
    unfold GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.nrm
    exact_mod_cast mt FractionalIdeal.absNorm_eq_zero_iff.1 𝔞.ne_zero
  unfold GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.omegaFactor
  exact_mod_cast mul_ne_zero (Real.rpow_pos_of_pos (dF_pos F) _).ne' hn

theorem cK_ne_zero (F : Type) [Field F] [NumberField F] (k : ℕ) : (GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.cK F k : ℂ) ≠ 0 := by
  have : (0 : ℝ) < GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.cK F k := by
    unfold GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.cK
    exact mul_pos (pow_pos (Nat.cast_pos.2 (Nat.factorial_pos _)) _) (Real.rpow_pos_of_pos (dF_pos F) _)
  exact_mod_cast this.ne'

def smulGen {F : Type} [Field F] [NumberField F] {𝔠 : FracId F} {X : Obj F 𝔠 (Sp ℂ)} (δ : X.DetGen) (c : ℂ)
    (hc : c ≠ 0) : X.DetGen :=
  ⟨c • δ.1, by rw [Submodule.span_singleton_smul_eq (IsUnit.mk0 c hc)]; exact δ.2⟩

theorem sign_pow_even (x : ℤˣ) (s : ℕ) : ((x : ℤ) : ℂ) ^ (2 * s) = 1 := by
  rcases Int.units_eq_one_or x with h | h <;> simp [h, pow_mul]

theorem eisRule_of (hQ : GlobalTheory.RealMult.QExpansionOnAll) (hExp : EisExp) (hMod : EisMod) (hFour : EisFourier)
    (hTor : TorusForm) : EisRule := by
  intro E _ _ _ hf 𝔠 s hs zv hzv R₀ m hm hmz
  have key : ∀ 𝔞 𝔟 𝔠' : FracId (FR E), 𝔠' = 𝔞 * 𝔟⁻¹ → ∃ r : Rule (trivialObjectCondition 𝔠') R₀ (2 * s),
      ∀ (I : Type) [Fintype I] (φ : I → E →+* ℂ) (c : Ideal (OF E)) (y : (Af E)ˣ), IsCMType φ → c ≠ ⊥ →
        IsEisRule φ (lattice c y) m r := by
    intro 𝔞 𝔟 𝔠' h𝔠
    subst h𝔠
    have e : Fin (Module.finrank ℚ (FR E)) ≃ (FR E →+* ℝ) := (Fintype.equivFinOfCardEq (card_emb (FR E))).symm
    obtain ⟨G, hG, hGd, hGexp⟩ := hExp (FR E) hf 𝔞 𝔟 s hs
    have hGmod := hMod (FR E) 𝔞 𝔟 s hs G hG hGd
    obtain ⟨Z, a, hZ, hfo, ha0, hint⟩ := hFour (FR E) 𝔞 𝔟 (2 * s) (by omega) G hGexp
    have hω0 := omegaFactor_ne_zero 𝔞
    have hck0 := cK_ne_zero (FR E) (2 * s)
    set ω : ℂ := (GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.omegaFactor 𝔞 : ℂ) with hω
    set ck : ℂ := (GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.cK (FR E) (2 * s) : ℂ) with hck
    have hcw : (cWt E (2 * s) : ℂ) = ck := rfl
    set gF : ((FR E →+* ℝ) → ℂ) → ℂ := fun z ↦ (m * ck / ω ^ (2 * s)) * G z with hgFdef
    have hgF : IsHolForm 𝔞 𝔟 (2 * s) gF := isHolForm_mul hGmod _
    have hfoF : HasFourier 𝔞 𝔟 gF (fun ξ ↦ m * a ξ) := by
      intro z hz
      have := (hfo z hz).mul_left m
      convert this using 1 <;> first | rfl | (funext ξ; ring) | (simp only [gF]; ring)
    have hcoef : ∀ ξ, m * a ξ ∈ R₀ := by
      intro ξ
      by_cases hξ : ξ = 0
      · subst hξ
        rw [ha0]
        obtain ⟨Z', hZ', hZ'v⟩ := hzv (ClassGroup.mk (FR E) 𝔞)⁻¹
        have hne : (1 - ((2 * s : ℕ) : ℂ)) ∈ ({1}ᶜ : Set ℂ) := by
          have : ((2 * s : ℕ) : ℂ) ≠ 0 := by exact_mod_cast (by omega : 2 * s ≠ 0)
          simpa using this
        have heq := GlobalTheory.IndefiniteRowSideFullHecke.ZetaValueIdeals.IsClassZeta.eqOn (F := FR E) ⟨hZ.1, hZ.2⟩ ⟨hZ'.1, hZ'.2⟩ hne
        rw [heq, hZ'v]
        have h5 : m * ((2 : ℂ)⁻¹ ^ Module.finrank ℚ (FR E) * ((zv (ClassGroup.mk (FR E) 𝔞)⁻¹ : ℚ) : ℂ)) =
            m * (((zv (ClassGroup.mk (FR E) 𝔞)⁻¹ / 2 ^ Module.finrank ℚ (FR E) : ℚ)) : ℂ) := by
          rw [Rat.cast_div, Rat.cast_pow, Rat.cast_ofNat, div_eq_mul_inv, inv_pow]; ring
        rw [h5]; exact hmz _
      · obtain ⟨n, hn⟩ := hint ξ hξ
        rw [hn]
        exact R₀.mul_mem hm (intCast_mem R₀ n)
    obtain ⟨r, hrv, -⟩ := hQ (FR E) hf e 𝔞 𝔟 (2 * s) R₀ gF (fun ξ ↦ m * a ξ) hgF hfoF hcoef
    refine ⟨r, fun I _ φ c y hφ hc ↦ ?_⟩
    intro g hg z hz X U δ C hdet
    obtain ⟨e', τ, lam, he', hτ, hlam, hΛ, htp⟩ := hTor E I 𝔞 𝔟 φ c y hφ hc z hz X U
    have hgz := GlobalTheory.T.polydisc_cm_uniformization E I 𝔞 𝔟 φ c y hφ hc s hs z hz U.e e' τ lam he' hτ hlam
      (fun w ↦ (U.lat w).symm.trans (hΛ w)) G hG g hg
    have hlamp : ∏ j, lam j ≠ 0 := Finset.prod_ne_zero_iff.2 fun j _ ↦ hlam j
    set K : ℂ := ω / ∏ j, lam j with hK
    have hK0 : K ≠ 0 := div_ne_zero hω0 hlamp
    have hval : ∀ δ' : X.DetGen, U.IsDet δ'.1 K → r.val ℂ X trivial δ' = gF τ := by
      intro δ' hδ'
      have htp' := htp δ'.1 hδ'
      let π : Equiv.Perm (Fin (Module.finrank ℚ (FR E))) := e.trans e'.symm
      have hπ : π.trans e' = e := by ext j; simp [π]
      have hA := GlobalTheory.T.torus_point_permutation_sign (FR E) e' π 𝔞 𝔟 τ X δ'.1 htp'
      rw [hπ] at hA
      have hsg : (((Equiv.Perm.sign π : ℤˣ) : ℤ) : ℂ) ≠ 0 := by
        rcases Int.units_eq_one_or (Equiv.Perm.sign π) with h | h <;> simp [h]
      have h1 := hrv τ hτ X trivial (smulGen δ' _ hsg) hA
      have h2 := r.homog ℂ X trivial δ' (smulGen δ' _ hsg) _ rfl
      rw [sign_pow_even, _root_.one_mul] at h2
      rw [← h2, h1]
    by_cases hdeg : ∃ (v : Fin (Module.finrank ℚ (FR E)) → X.Lie)
        (W : Matrix (Fin (Module.finrank ℚ (FR E))) (Fin (Module.finrank ℚ (FR E))) ℂ),
        (∀ j, U.u.IsDiff (W j) (v j).hom) ∧ W.det ≠ 0
    · obtain ⟨v, W, hv, hW⟩ := hdeg
      have hδv := GlobalTheory.T.determinant_nonzero_differentials (FR E) _ X _ U.u δ v W hv hW
      have hC : C ≠ 0 := by
        intro h0; apply hδv; rw [hdet v W hv, h0, zero_mul]
      have hδ' : U.IsDet (smulGen δ (K / C) (div_ne_zero hK0 hC)).1 K := by
        intro v W hv
        show ((K / C) • δ.1) v = K * W.det
        rw [AlternatingMap.smul_apply, hdet v W hv, smul_eq_mul]
        field_simp
      have h1 := hval _ hδ'
      have h2 := r.homog ℂ X trivial δ (smulGen δ (K / C) (div_ne_zero hK0 hC)) (K / C) rfl
      rw [h1] at h2
      have hCK : C ^ (2 * s) * (K / C) ^ (2 * s) = K ^ (2 * s) := by
        rw [← mul_pow]; congr 1; field_simp
      rw [← h2, ← _root_.mul_assoc, hCK, hgz, hcw, hK, hgFdef]
      simp only
      rw [div_pow, inv_pow]
      field_simp
    · push_neg at hdeg
      have hδK : U.IsDet δ.1 K := fun v W hv ↦ by rw [hdet v W hv, hdeg v W hv]; simp
      have hδ2 : U.IsDet (smulGen δ 2 two_ne_zero).1 K := by
        intro v W hv
        show ((2 : ℂ) • δ.1) v = K * W.det
        rw [AlternatingMap.smul_apply, hdet v W hv, hdeg v W hv]; simp
      have h1 := hval _ hδK
      have h2 := hval _ hδ2
      have h3 := r.homog ℂ X trivial δ (smulGen δ 2 two_ne_zero) 2 rfl
      rw [h1, h2] at h3
      have hg0 : gF τ = 0 := by
        have h4 : ((2 : ℂ) ^ (2 * s) - 1) * gF τ = 0 := by rw [sub_mul, h3]; ring
        refine (mul_eq_zero.1 h4).resolve_left ?_
        have : (1 : ℝ) < 2 ^ (2 * s) := one_lt_pow₀ (by norm_num) (by omega)
        intro h5
        have h6 : (2 : ℂ) ^ (2 * s) = 1 := sub_eq_zero.1 h5
        have h7 : ((2 : ℝ) ^ (2 * s) : ℂ) = 1 := by push_cast; exact h6
        have h8 : (2 : ℝ) ^ (2 * s) = 1 := by exact_mod_cast h7
        linarith
      have hmG : m * G τ = 0 := by
        simp only [gF] at hg0
        have := mul_eq_zero.1 hg0
        rcases this with h | h
        · rcases mul_eq_zero.1 (div_eq_zero_iff.1 h |>.resolve_right (pow_ne_zero _ hω0)) with h' | h'
          · rw [h', zero_mul]
          · exact absurd h' hck0
        · rw [h, mul_zero]
      rw [h1, hgz, hg0, mul_zero]
      linear_combination (-(cWt E (2 * s) : ℂ) * ((∏ j, lam j)⁻¹) ^ (2 * s)) * hmG

  exact key 𝔠 1 𝔠 (by simp)

end GlobalTheory.EisRuleProof
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ElementaryMatrixEndomorphismGroupPullbackTranspo
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

noncomputable section
namespace GlobalTheory.MatEndPull

theorem ext_of_pb {T T' : Scheme.{0}} {t : T' ⟶ T} {G : Over T} {G' : Over T'} [GrpObj G] [GrpObj G']
    {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G t φ) {X : Over T'} {x y : X ⟶ G'}
    (e : x.left ≫ φ = y.left ≫ φ) : x = y := by
  apply Over.OverMorphism.ext
  apply h.1.hom_ext e
  rw [Over.w x, Over.w y]

theorem one_left_eq {T : Scheme.{0}} {X M : Over T} [GrpObj M] : (1 : X ⟶ M).left = X.hom ≫ η[M].left := by
  rw [Hom.one_def, Over.comp_left]
  congr 1

theorem mul_comp_lift {T T' : Scheme.{0}} {t : T' ⟶ T} {B : Over T} {B' : Over T'} [GrpObj B] [GrpObj B']
    {φ : B'.left ⟶ B.left} (h : IsGrpPullback B' B t φ) {f : B ⟶ B} [IsMonHom f] {f' : B' ⟶ B'}
    (e : f'.left ≫ φ = φ ≫ f.left) {X : Over T'} (x y : X ⟶ B') :
    (x * y) ≫ f' = (x ≫ f') * (y ≫ f') := by
  apply ext_of_pb h
  have e₁ := h.2 X x y (pushPt h.1.w x) (pushPt h.1.w y) rfl rfl
  have e₂ := h.2 X (x ≫ f') (y ≫ f') (pushPt h.1.w x ≫ f) (pushPt h.1.w y ≫ f)
    (by simp [pushPt, e]) (by simp [pushPt, e])
  rw [← e₂, Over.comp_left, Category.assoc, e, ← Category.assoc, ← e₁, ← Over.comp_left, mul_comp]

theorem isMonHom_lift {T T' : Scheme.{0}} {t : T' ⟶ T} {B : Over T} {B' : Over T'} [GrpObj B] [GrpObj B']
    {φ : B'.left ⟶ B.left} (h : IsGrpPullback B' B t φ) {f : B ⟶ B} [IsMonHom f] {f' : B' ⟶ B'}
    (e : f'.left ≫ φ = φ ≫ f.left) : IsMonHom f' := by
  have h1 : ∀ (X : Over T'), (1 : X ⟶ B') ≫ f' = 1 := fun X => by
    have := mul_comp_lift h e (1 : X ⟶ B') 1
    rw [_root_.mul_one] at this
    exact mul_eq_left.1 this.symm
  refine ⟨?_, ?_⟩
  · have := h1 (𝟙_ _)
    simpa [Hom.one_def] using this
  · have := mul_comp_lift h e (fst B' B') (snd B' B')
    simpa [Hom.mul_def] using this

theorem unit_pull {S S' : Scheme.{0}} {f : S' ⟶ S} {G : Over S} [GrpObj G] {G' : Over S'}
    [GrpObj G'] {φ : G'.left ⟶ G.left} (hG : IsGrpPullback G' G f φ) :
    η[G'].left ≫ φ = f ≫ η[G].left := by
  have h := hG.2 (𝟙_ _) 1 1 (pushPt hG.1.w 1) (pushPt hG.1.w 1) rfl rfl
  rw [_root_.mul_one] at h
  have h3 : pushPt hG.1.w (1 : 𝟙_ (Over S') ⟶ G') * pushPt hG.1.w 1 = pushPt hG.1.w 1 :=
    Over.OverMorphism.ext h
  have h4 : (1 : 𝟙_ (Over S') ⟶ G').left ≫ φ = (1 : Over.mk ((𝟙_ (Over S')).hom ≫ f) ⟶ G).left :=
    congrArg Over.Hom.left (mul_eq_left.1 h3)
  rw [one_left_eq, one_left_eq] at h4
  simpa using h4

theorem matEnd_pull : ∀ {T T' : Scheme.{0}} {t : T' ⟶ T} {B C : Over T} [GrpObj B] [GrpObj C] {B' C' : Over T'} [GrpObj B'] [GrpObj C'] {φB : B'.left ⟶ B.left} {χ : C'.left ⟶ C.left} (pr : Fin 8 → (B ⟶ C)) (pr' : Fin 8 → (B' ⟶ C')) (a b : Fin 8) (f₁ : B ⟶ B) (f₁' : B' ⟶ B'), IsGrpPullback B' B t φB → IsGrpPullback C' C t χ → (∀ w, (pr' w).left ≫ χ = φB ≫ (pr w).left) → f₁'.left ≫ φB = φB ≫ f₁.left → MatEnd pr a b f₁ → MatEnd pr' a b f₁' := by
  intro T T' t B C _ _ B' C' _ _ φB χ pr pr' a b f₁ f₁' hB hC hpr e hf
  obtain ⟨hm, hw⟩ := hf
  haveI := hm
  refine ⟨isMonHom_lift hB e, fun w => ?_⟩
  apply ext_of_pb hC
  have key : (f₁' ≫ pr' w).left ≫ χ = φB ≫ (f₁ ≫ pr w).left := by
    rw [Over.comp_left, Category.assoc, hpr, ← Category.assoc, e, Category.assoc, ← Over.comp_left]
  rw [key, hw w]
  split_ifs
  · exact (hpr b).symm
  · rw [one_left_eq, one_left_eq, ← Category.assoc, hB.1.w, Category.assoc, Category.assoc,
      unit_pull hC]

end GlobalTheory.MatEndPull

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EllipticCurveAbelianSchemeModel
section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.LatJet GlobalTheory.LatModel
open GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds (IsClassZetaVals c_vp cE_vp a0)

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.LatticeFibre

open GlobalTheory.HolUnifScale in

theorem exists_holUnif_rescale {A : Over (Sp ℂ)} [GrpObj A] {Lb : LB A.left} {n : ℕ} (u : HolUnif A Lb n)
    (w₀ : Fin n → ℂ) (hn : n = 1) (v : epsR ℂ ⟶ A) (hw : u.IsDiff w₀ v) (hw0 : w₀ ≠ 0) (Λ : PeriodPair) {c : ℂ}
    (hc : c ≠ 0) (hL : ∀ z : ℂ, z ∈ Λ.lattice ↔ (c⁻¹ * z) • w₀ ∈ u.Λ) :
    ∃ u' : HolUnif A Lb 1, (∀ w, w ∈ u'.Λ ↔ w 0 ∈ Λ.lattice) ∧ u'.IsDiff (fun _ ↦ c) v := by
  subst hn
  have h0 : w₀ 0 ≠ 0 := fun h ↦ hw0 (funext fun j ↦ by rw [Subsingleton.elim j 0]; exact h)
  have h : ∀ j : Fin 1, (fun _ : Fin 1 ↦ w₀ 0 / c) j ≠ 0 := fun _ ↦ div_ne_zero h0 hc
  refine ⟨rescale u _ h, fun w ↦ ?_, ?_⟩
  · refine (mem_latPull u _ h w).trans ?_
    rw [hL, scale_apply]
    have e : (fun j : Fin 1 ↦ w₀ 0 / c * w j) = (c⁻¹ * w 0) • w₀ := by
      funext j
      rw [Subsingleton.elim j 0, Pi.smul_apply, smul_eq_mul]
      ring
    rw [e]
  · have key : ∀ W, (rescale u _ h).IsDiff W v ↔ u.IsDiff (fun j ↦ w₀ 0 / c * W j) v := by
      intro W
      unfold HolUnif.IsDiff
      have hf : ∀ (U : A.left.Opens) (f : Γ(A.left, U)),
          (fun z ↦ valAt' ((rescale u _ h).ex z).left U f) = (fun z ↦ valAt' (u.ex z).left U f) ∘ scale _ h :=
        fun _ _ ↦ rfl
      simp only [hf, ContinuousLinearEquiv.comp_right_fderiv, map_zero]
      rfl
    rw [key]
    have e : (fun _ : Fin 1 ↦ w₀ 0 / c * c) = w₀ := by
      funext j
      rw [Subsingleton.elim j 0, div_mul_cancel₀ _ hc]
    rw [e]
    exact hw

theorem exists_fibre_holUnif : ∀ (R₁ : Subring ℂ) (W : WeierstrassCurve R₁), IsUnit W.Δ → ∀ (Λ : PeriodPair) (c : ℂ), c ≠ 0 →
    ((W.c₄ : R₁) : ℂ) = 12 * c ^ 4 * Λ.g₂ → ((W.c₆ : R₁) : ℂ) = 216 * c ^ 6 * Λ.g₃ →
      ∃ (P : Out.PolAV (Sp R₁)) (A' : Over (Sp ℂ)) (_ : GrpObj A') (φ' : A'.left ⟶ P.A.left) (L' : LB A'.left)
        (u : HolUnif A' L' 1) (v : epsR R₁ ⟶ P.A) (v' : epsR ℂ ⟶ A'),
        IsAbelianScheme A' ∧ SmoothOfRelativeDimension 1 A'.hom ∧ IsGrpPullback A' P.A (spMap R₁.subtype) φ' ∧
        (∀ w, w ∈ u.Λ ↔ w 0 ∈ Λ.lattice) ∧ IsTangent v ∧ IsTangent v' ∧
        v'.left ≫ φ' = spMap (Chart.dualMapR R₁.subtype) ≫ v.left ∧ u.IsDiff (fun _ ↦ c) v' := by
  intro R₁ W hΔ Λ c hc h4 h6
  obtain ⟨P, v, Lf, ⟨hg, hv, -, hs⟩, hinv⟩ :=
    GlobalTheory.exists_polAV_latticeFamily GlobalTheory.thetaUnifAV_all GlobalTheory.polBaseChange_holds R₁ W hΔ
  obtain ⟨P', φ', h⟩ := GlobalTheory.exists_isPolFibre GlobalTheory.polBaseChange_holds R₁.subtype P
  obtain ⟨v', hv', -⟩ := GlobalTheory.existsUnique_isVecOver h.2.1.1 v
  have ht : IsTangent v := hv.1 0
  have ht' : IsTangent v' := hv'.isTangent h.2.1 ht
  obtain ⟨rig, hrig⟩ := P'.rigid
  obtain ⟨u, Hm, χ, -, -, -, hd, -⟩ := GlobalTheory.thetaUnifAV_all P' rig hrig
  obtain ⟨w, hw, -⟩ := hd v' ht'
  obtain ⟨hw0, hL⟩ := hs R₁.subtype P' φ' v' u w h hv' hw
  obtain ⟨e4, e6, -⟩ := hinv R₁.subtype
  have H := GlobalTheory.isHomothetic_scalePeriods Λ c⁻¹ (inv_ne_zero hc)
  have e : (Lf R₁.subtype).lattice = (GlobalTheory.scalePeriods Λ c⁻¹ (inv_ne_zero hc)).lattice := by
    refine GlobalTheory.lattice_eq_of_g₂_eq_of_g₃_eq ?_ ?_
    · refine mul_left_cancel₀ (by norm_num : (12 : ℂ) ≠ 0) ?_
      rw [← e4, H.g₂_eq, inv_pow, inv_inv, ← _root_.mul_assoc]
      exact h4
    · refine mul_left_cancel₀ (by norm_num : (216 : ℂ) ≠ 0) ?_
      rw [← e6, H.g₃_eq, inv_pow, inv_inv, ← _root_.mul_assoc]
      exact h6
  have hg' : P'.g = 1 := h.1.trans hg
  obtain ⟨u', hu', hd'⟩ := exists_holUnif_rescale u w hg' v' hw hw0 Λ hc
    (fun z ↦ by rw [← hL, e]; exact (H z).symm)
  exact ⟨P, P'.A, inferInstance, φ', P'.L, u', v, v', P'.isAb, hg' ▸ P'.smoothDim, h.2.1, hu', ht, ht', hv', hd'⟩

end GlobalTheory.LatticeFibre
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EndCharExistsOfIsMonHom
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
open scoped TensorProduct

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Poinc.Eq8

theorem endChar_exists_of_isMonHom (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (_hB : GlobalTheory.Mum.Base R)
    (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (_hG : IsSemiAbelian G) (D : DegData R (maximalIdeal R))
    (A : PolAV (Sp (FractionRing R))) (U : Unif (maximalIdeal R) D A G) (f : G ⟶ G) (hfm : IsMonHom f) :
    ∃ m, EndChar U f m := by
  have hr : ∀ x ∈ maximalIdeal R ^ (0 + 1), residue R x = 0 := fun x hx =>
    (residue_eq_zero_iff x).2 (Ideal.pow_le_self (Nat.succ_ne_zero 0) hx)
  have hp := isGrpPullback_pullback G (spMap (residue R))
  have e : ((Over.pullback (spMap (residue R))).map f).left ≫ pullback.fst G.hom (spMap (residue R)) =
      pullback.fst G.hom (spMap (residue R)) ≫ f.left := pullback.lift_fst _ _ _
  have hf₁ : IsMonHom ((Over.pullback (spMap (residue R))).map f) :=
    Out.PullGtPf.isMonHom_of_grpPullback hp hp f _ e
  obtain ⟨m, hm⟩ := (GlobalTheory.TorusPart.mono_gtTorus_and_factor (U.gt 0) hr hp).2 _
    (GlobalTheory.TorusPart.gtTorus (U.gt 0) hr hp ≫ (Over.pullback (spMap (residue R))).map f) inferInstance
  refine ⟨m, fun κ _ a ha G₀ _ φ h f₀ hf => ?_⟩
  let σ : ResidueField R →+* κ := Ideal.Quotient.lift _ a fun x hx => ha x (by simpa using hx)
  have ea : a = σ.comp (residue R) := RingHom.ext fun _ => rfl
  have es : spMap a = spMap σ ≫ spMap (residue R) := by rw [← Spec.map_comp]; rfl
  let ψ : G₀.left ⟶ ((Over.pullback (spMap (residue R))).obj G).left :=
    pullback.lift φ (G₀.hom ≫ spMap σ) (by rw [Category.assoc, ← es, h.1.w])
  have hψ : ψ ≫ pullback.fst G.hom (spMap (residue R)) = φ := pullback.lift_fst _ _ _
  have k : IsGrpPullback G₀ ((Over.pullback (spMap (residue R))).obj G) (spMap σ) ψ :=
    hp.cancel (h.congr es hψ.symm) (pullback.lift_snd _ _ _)
  have e₀ : f₀.left ≫ ψ = ψ ≫ ((Over.pullback (spMap (residue R))).map f).left := hp.1.hom_ext
    (by rw [Category.assoc, hψ, hf, Category.assoc, e, ← Category.assoc, hψ])
    (by rw [Category.assoc, k.1.w, ← Category.assoc, Over.w, Category.assoc, Over.w, k.1.w])
  rw [← GlobalTheory.TorusPart.pullTorus_gtTorus (U.gt 0) hr ha hp h k ea hψ.symm,
    ← GlobalTheory.TorusPart.pullTorus_comp k k _ f₀ e₀, hm, GlobalTheory.TorusPart.pullTorus_torusMap_comp]

end GlobalTheory.Poinc.Eq8
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOfCompEqOfConnectedSpacePullbackStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eq_of_comp_eq_of_connectedSpace_pullback' : ∀ (P Q : Scheme.{0}) (b : P ⟶ Q), LocallyQuasiFinite b → ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (ν : Sp Ω ⟶ Q) (ξ₁ ξ₂ : Sp Ω ⟶ P), ξ₁ ≫ b = ν → ξ₂ ≫ b = ν → ConnectedSpace (pullback b ν : Scheme.{0}) → ξ₁ = ξ₂ := by
  first | exact @GlobalTheory.Mum.eq_of_comp_eq_of_connectedSpace_pullback | exact GlobalTheory.Mum.eq_of_comp_eq_of_connectedSpace_pullback | (intros; apply GlobalTheory.Mum.eq_of_comp_eq_of_connectedSpace_pullback <;> assumption)
end

