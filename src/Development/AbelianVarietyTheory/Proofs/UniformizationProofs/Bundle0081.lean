import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0008
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0005
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0006
import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle0002
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.SvalEqZeroOfWeightSum
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0053
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0071
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0002
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsMonHomOfMul
import Development.AbelianVarietyTheory.BlockTheory.UniformisationCharts.SeparatedSymmetricModel
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsTorusAndQuotientHom
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsAbelianSchemeThick
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0016
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0013
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.Bundle0003
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.Bundle0002
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.ThetaMove
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExpansionBijectiveOverFields
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0001
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0013
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0024
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0027
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0013
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0020

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.FourierJacobiExpansionOverFieldInjective
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

namespace GlobalTheory.UU.ExpFUniq

open ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.BoxIndep GlobalTheory.ExpansionSingleValued

theorem split_iff {R F : Type} [CommRing R] [CommRing F] [Algebra R F] {X X₀ : Scheme.{0}}
    (p : X ⟶ Spec (CommRingCat.of R)) [Flat p] {L : LB X₀} (hL : L.IsLB) {K : Type} [Fintype K] {φ : K → (X ⟶ X₀)}
    {ε : K → ℤ} {Λ κ : Type} [Fintype Λ] [Fintype κ] (b : κ → F) (hb : LinearIndependent R b) (a : Λ → κ → R)
    (σ : Λ → LB.Sec (LB.LinComb L φ ε)) (τ : κ → LB.Sec (LB.LinComb L φ ε)) (τ₀ : LB.Sec (LB.LinComb L φ ε))
    (hτ : ∀ l (Z : Scheme.{0}) (r : Z ⟶ X) (z : Z) (J), Good L z J → sval (τ l) r z J =
      ∑ i, gs (r ≫ p) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (a i l)) * sval (σ i) r z J)
    (h₀ : ∀ (Z : Scheme.{0}) (r : Z ⟶ X) (z : Z) (J), Good L z J → sval τ₀ r z J = 0) :
    (∀ l, τ l = τ₀) ↔ ∀ (Z : Scheme.{0}) (q : Z ⟶ Spec (CommRingCat.of F)) (r : Z ⟶ X),
      r ≫ p = q ≫ Spec.map (CommRingCat.ofHom (algebraMap R F)) → ∀ (z : Z) (J), Good L z J →
        ∑ i, germOf q z (∑ l, a i l • b l) * sval (σ i) r z J = 0 := by
  replace hτ : ∀ l (Z : Scheme.{0}) (r : Z ⟶ X) (z : Z) (J), Good L z J → sval (τ l) r z J =
      ∑ i, germOf (r ≫ p) z (a i l) * sval (σ i) r z J := fun l Z r z J hJ =>
    (hτ l Z r z J hJ).trans (Finset.sum_congr rfl fun i _ => congrArg (· * _) (germOf_apply _ _ _).symm)
  constructor
  · intro h Z q r e z J hJ
    simp only [map_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_eq_zero fun l _ => ?_
    have h₁ := (hτ l Z r z J hJ).symm.trans ((congrArg (fun s => sval s r z J) (h l)).trans (h₀ Z r z J hJ))
    refine Eq.trans (Finset.sum_congr rfl fun i _ => ?_) ((Finset.mul_sum _ _ (germOf q z (b l))).symm.trans
      ((congrArg _ h₁).trans (mul_zero _)))
    rw [Algebra.smul_def, map_mul, e, germOf_map, mul_comm (germOf q z _), _root_.mul_assoc]
    rfl
  · intro H l
    refine SecOps.sec_ext (sec_ext_val hL fun y J hJ => ?_)
    rw [h₀ _ _ y J hJ, hτ l _ _ y J hJ, Category.id_comp]
    refine split_relation p y (hJ.mem φ (𝟙 X)) b hb a (fun i => (σ i).f fun k => J (𝟙 X ≫ φ k))
      (fun Z q r e z hz => ?_) l
    obtain ⟨J', hJ'⟩ := exists_good_pt hL z
    have h₁ := congrArg ((trF φ ε r z (fun k => J (𝟙 X ≫ φ k)) (fun k => J' (r ≫ φ k))).val * ·) (H Z q r e z J' hJ')
    simp only [mul_zero, Finset.mul_sum] at h₁
    refine Eq.trans (Finset.sum_congr rfl fun i _ => ?_) h₁
    rw [mul_left_comm]
    exact congrArg _ (sec_trans (σ i) r z hz (hJ'.mem φ r))

theorem expT_unit_iff : AllPre fun {_} _ _ _ {_} {_} {_} _ _ U => ∀ k σ σ' f f',
    U.ExpT (𝟙_ _) k σ f → U.ExpT (𝟙_ _) k σ' f' → (σ = σ' ↔ f = f') := by
  intro V _ _ _ hV D A G _ _ U
  have key : ∀ T, TA V V = T → ∀ k σ σ' f f', U.ExpT T k σ f → U.ExpT T k σ' f' → (σ = σ' ↔ f = f') := by
    rintro _ rfl
    refine GlobalTheory.expT_eq_iff V hV D A G U V ⟨inferInstance, inferInstance, inferInstance, inferInstance, ?_⟩
    rw [Algebra.algebraMap_self, Ideal.map_id]
    exact hV.2.1
  exact key _ (congrArg Over.mk (Spec.map_id _))

set_option maxHeartbeats 400000 in

theorem main : (AllPre fun {V} _ _ _ {_} {_} {_} _ _ U => ∀ (F : Type) [Field F] [Algebra (FractionRing V) F] (k : ℕ) t t' s s', U.ExpF F k t s → U.ExpF F k t' s' → (t = t' ↔ s = s')) := by
  intro V _ _ _ hV D A G _ _ U F _ _ k t t' s s' ⟨n, c, σ, f, hE, hG, hB⟩ ⟨n', c', σ', f', hE', hG', hB'⟩
  classical
  let : Algebra V F := ((algebraMap (FractionRing V) F).comp (algebraMap V (FractionRing V))).toAlgebra
  have : IsScalarTower V (FractionRing V) F := IsScalarTower.of_algebraMap_eq' rfl
  have hj : jFK (R := V) F ≫ jK V = Spec.map (CommRingCat.ofHom (algebraMap V F)) :=
    (Spec.map_comp _ _).symm
  obtain ⟨κ, _, b, a, hb, ha⟩ := exists_indep_coords V F (Fin.append c (-c'))
  have hEE : ∀ i, U.ExpT (𝟙_ _) k (Fin.append σ σ' i) (Fin.append f f' i) := fun i => by
    refine Fin.addCases (fun i => ?_) (fun i => ?_) i
    · simpa only [Fin.append_left] using hE i
    · simpa only [Fin.append_right] using hE' i
  choose τ g hτg hτ hg using fun l => ExpLin.expT_linear V _ D A G U (𝟙_ _) k _
    (fun i => (Scheme.ΓSpecIso (CommRingCat.of V)).inv.hom (a i l)) _ _ hEE
  obtain ⟨τ₀, g₀, h₀, hτ₀, hg₀⟩ := ExpLin.expT_linear V _ D A G U (𝟙_ _) k 0 Fin.elim0 Fin.elim0 Fin.elim0
    (fun i => i.elim0)
  simp only [Finset.univ_eq_empty, Finset.sum_empty] at hτ₀ hg₀
  have := U.semi.smooth
  have := D.P.isAb.smooth
  let pG : (𝟙_ _ ⊗ G).left ⟶ Spec (CommRingCat.of V) := (fst (𝟙_ _) G).left
  let pB : (𝟙_ _ ⊗ D.P.A).left ⟶ Spec (CommRingCat.of V) := (fst (𝟙_ _) D.P.A).left
  have : Flat pG := inferInstanceAs (Flat (pullback.fst _ G.hom))
  have : Flat pB := inferInstanceAs (Flat (pullback.fst _ D.P.A.hom))
  have eG : (snd (𝟙_ _) G).left ≫ G.hom = pG :=
    (Over.w (snd (𝟙_ _) G)).trans ((Over.w (fst (𝟙_ _) G)).symm.trans (Category.comp_id _))
  have eB : (snd (𝟙_ _) D.P.A).left ≫ D.P.A.hom = pB :=
    (Over.w (snd (𝟙_ _) D.P.A)).trans ((Over.w (fst (𝟙_ _) D.P.A)).symm.trans (Category.comp_id _))
  have SG := split_iff pG U.P.L.isLB b hb a (Fin.append σ σ') τ τ₀ hτ hτ₀
  have SB := fun α => split_iff pB D.P.isLB b hb a (fun i => Fin.append f f' i α) (fun l => g l α) (g₀ α)
    (fun l => hg l α) (hg₀ α)
  simp only [← ha] at SG SB
  simp only [gs_scal] at hG hG' hB hB'
  have M : (∀ l, τ l = τ₀) ↔ ∀ α l, g l α = g₀ α := by
    rw [forall_comm]
    exact forall_congr' fun l => (expT_unit_iff V hV D A G U k _ _ _ _ (hτg l) h₀).trans funext_iff
  have NG : t = t' ↔ ∀ l, τ l = τ₀ := by
    rw [SG]
    constructor
    · rintro rfl Z q r e z J hJ
      let y : Z ⟶ pullback G.hom (jK V) := pullback.lift (r ≫ (snd (𝟙_ _) G).left) (q ≫ jFK (R := V) F)
        (by rw [Category.assoc, eG, e, Category.assoc, hj])
      let rA : Z ⟶ (TFK (R := V) F ⊗ A.A).left := pullback.lift q (y ≫ U.gen.hom.left)
        ((pullback.lift_snd _ _ _).symm.trans ((congrArg (y ≫ ·) (Over.w U.gen.hom).symm).trans
          (Category.assoc _ _ _).symm))
      have e₁ : rA ≫ (fst (TFK (R := V) F) A.A).left = q := pullback.lift_fst _ _ _
      obtain ⟨JA, hJA⟩ := exists_good_pt A.isLB z
      have h₁ := hG Z rA y r (pullback.lift_snd _ _ _) (pullback.lift_fst _ _ _).symm z JA J hJA hJ
      have h₂ := hG' Z rA y r (pullback.lift_snd _ _ _) (pullback.lift_fst _ _ _).symm z JA J hJA hJ
      refine (sum_append (germOf q z) c c' σ σ' (fun t => sval t r z J)).trans (sub_eq_zero.2 ?_)
      rw [← e₁]
      exact h₁.symm.trans h₂
    · intro H
      refine SecOps.sec_ext (sec_ext_val (φ := fun _ : Fin 1 => (snd (TFK (R := V) F) A.A).left)
        (ε := fun _ => (k : ℤ)) A.isLB fun z JA hJA => ?_)
      let y : (TFK (R := V) F ⊗ A.A).left ⟶ pullback G.hom (jK V) := (snd (TFK (R := V) F) A.A).left ≫ U.gen.inv.left
      let r : (TFK (R := V) F ⊗ A.A).left ⟶ (𝟙_ _ ⊗ G).left :=
        pullback.lift ((y ≫ pullback.fst G.hom (jK V)) ≫ G.hom) (y ≫ pullback.fst G.hom (jK V)) (Category.comp_id _)
      have e₁ : r ≫ (snd (𝟙_ _) G).left = y ≫ pullback.fst G.hom (jK V) := pullback.lift_snd _ _ _
      have e₂ : 𝟙 _ ≫ (snd (TFK (R := V) F) A.A).left = y ≫ U.gen.hom.left :=
        (Category.id_comp _).trans ((Category.comp_id _).symm.trans ((congrArg (_ ≫ ·)
          (congrArg CommaMorphism.left U.gen.inv_hom_id).symm).trans (Category.assoc _ _ _).symm))
      obtain ⟨J, hJ⟩ := exists_good_pt U.P.L.isLB z
      have h₁ := hG _ (𝟙 _) y r e₂ e₁ z JA J hJA hJ
      have h₂ := hG' _ (𝟙 _) y r e₂ e₁ z JA J hJA hJ
      have e₃ : y ≫ pullback.snd G.hom (jK V) = (𝟙 _ ≫ (fst (TFK (R := V) F) A.A).left) ≫ jFK (R := V) F :=
        (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) (Over.w U.gen.inv)).trans
          ((Over.w (snd (TFK (R := V) F) A.A)).trans ((Over.w (fst (TFK (R := V) F) A.A)).symm.trans
            (congrArg (· ≫ _) (Category.id_comp _).symm))))
      have h₃ := H _ (𝟙 _ ≫ (fst (TFK (R := V) F) A.A).left) r (by
        rw [← eG, ← Category.assoc, e₁, Category.assoc, pullback.condition, ← Category.assoc, e₃, ← hj]
        exact Category.assoc _ _ _) z J hJ
      have h₄ := sub_eq_zero.1 ((sum_append (germOf (B := CommRingCat.of F) (𝟙 _ ≫ (fst (TFK (R := V) F) A.A).left) z)
        c c' σ σ' (fun t => sval t r z J)).symm.trans h₃)
      exact (IsUnit.mul_right_inj ((Units.isUnit _).pow k)).1 (h₁.trans (h₄.trans h₂.symm))
  have NB : s = s' ↔ ∀ α l, g l α = g₀ α := by
    rw [funext_iff]
    refine forall_congr' fun α => ?_
    rw [SB α]
    constructor
    · intro h Z q r e z J hJ
      let rF : Z ⟶ (DegPre.BF D F).left := pullback.lift q (r ≫ (snd (𝟙_ _) D.P.A).left)
        (by rw [Category.assoc, eB, e, ← hj]; rfl)
      have e₁ : rF ≫ (fst (TF (R := V) F) D.P.A).left = q := pullback.lift_fst _ _ _
      have h₁ := hB α Z rF r (pullback.lift_snd _ _ _).symm z J hJ
      have h₂ := hB' α Z rF r (pullback.lift_snd _ _ _).symm z J hJ
      refine (sum_append (germOf q z) c c' f f' (fun t => sval (t α) r z J)).trans (sub_eq_zero.2 ?_)
      rw [← e₁]
      exact h₁.symm.trans ((congrArg (fun u => sval u rF z J) h).trans h₂)
    · intro H
      refine SecOps.sec_ext (sec_ext_val D.P.isLB fun z J hJ => ?_)
      let r : (DegPre.BF D F).left ⟶ (𝟙_ _ ⊗ D.P.A).left :=
        pullback.lift ((DegPre.prB D F).left ≫ D.P.A.hom) (DegPre.prB D F).left (Category.comp_id _)
      have e₁ : r ≫ (snd (𝟙_ _) D.P.A).left = 𝟙 _ ≫ (DegPre.prB D F).left :=
        (pullback.lift_snd _ _ _).trans (Category.id_comp _).symm
      have h₃ := H _ (𝟙 _ ≫ (fst (TF (R := V) F) D.P.A).left) r (by
        rw [← eB, ← Category.assoc, e₁, Category.assoc, Category.assoc, Over.w, ← hj]
        exact congrArg _ (Over.w (fst (TF (R := V) F) D.P.A)).symm) z J hJ
      have h₄ := sub_eq_zero.1 ((sum_append (germOf (B := CommRingCat.of F) (𝟙 _ ≫ (fst (TF (R := V) F) D.P.A).left) z)
        c c' f f' (fun t => sval (t α) r z J)).symm.trans h₃)
      exact (hB α _ (𝟙 _) r e₁ z J hJ).trans (h₄.trans (hB' α _ (𝟙 _) r e₁ z J hJ).symm)
  exact NG.trans (M.trans NB.symm)

end GlobalTheory.UU.ExpFUniq
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.LiftThreeOverMapComp
section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.UnifPreCompare

section General

variable {X₁ X₂ Y Y₁ Y₂ T : Scheme.{0}} {L : LB X₁} {M : LB X₂} {a : Y ⟶ X₁} {b : Y ⟶ X₂}
  {K : Type} [Fintype K]

def wv (w : LB.Iso (L.pull a) (M.pull b)) {Z : Scheme.{0}} (r : Z ⟶ Y) (z : Z) (p : M.ι) (q : L.ι) :
    (Z.presheaf.stalk z)ˣ := gw w r z p (fun _ => q)

def Carries (w : LB.Iso (L.pull a) (M.pull b)) (ψ : K → (T ⟶ Y)) (ε : K → ℤ)
    {φ₁ : K → (Y₁ ⟶ X₁)} (s : LB.Gen (LB.LinComb L φ₁ ε)) (f₁ : T ⟶ Y₁)
    {φ₂ : K → (Y₂ ⟶ X₂)} (t : LB.Gen (LB.LinComb M φ₂ ε)) (f₂ : T ⟶ Y₂) : Prop :=
  ∀ (Z : Scheme.{0}) (r : Z ⟶ T) (z : Z) (p : K → M.ι) (q : K → L.ι), (∀ k, b (ψ k (r z)) ∈ M.U (p k)) →
    (∀ k, a (ψ k (r z)) ∈ L.U (q k)) →
    gm (r ≫ f₂) z (LB.wchart M φ₂ p) (t.s p) =
      (∏ k, wv w (r ≫ ψ k) z (p k) (q k) ^ ε k) * gm (r ≫ f₁) z (LB.wchart L φ₁ q) (s.s q)

variable {w : LB.Iso (L.pull a) (M.pull b)} {ψ : K → (T ⟶ Y)} {ε : K → ℤ}
  {φ₁ : K → (Y₁ ⟶ X₁)} {s : LB.Gen (LB.LinComb L φ₁ ε)} {f₁ : T ⟶ Y₁}
  {φ₂ : K → (Y₂ ⟶ X₂)} {t : LB.Gen (LB.LinComb M φ₂ ε)} {f₂ : T ⟶ Y₂}

theorem Carries.comp (H : Carries w ψ ε s f₁ t f₂) {T' : Scheme.{0}} (h : T' ⟶ T) {ψ' : K → (T' ⟶ Y)}
    {g₁ : T' ⟶ Y₁} {g₂ : T' ⟶ Y₂} (e : ∀ k, ψ' k = h ≫ ψ k) (e₁ : g₁ = h ≫ f₁) (e₂ : g₂ = h ≫ f₂) :
    Carries w ψ' ε s g₁ t g₂ := by
  obtain rfl : ψ' = fun k => h ≫ ψ k := funext e
  subst e₁ e₂
  intro Z r z p q hp hq
  simpa only [Category.assoc] using H Z (r ≫ h) z p q hp hq

theorem Carries.congr {a' : Y ⟶ X₁} {b' : Y ⟶ X₂} {w' : LB.Iso (L.pull a') (M.pull b')} (ha : a = a') (hb : b = b')
    (hw : HEq w w') : Carries w ψ ε s f₁ t f₂ ↔ Carries w' ψ ε s f₁ t f₂ := by
  subst ha hb
  rw [eq_of_heq hw]

end General

section Rigid

variable {X X' T Y : Scheme.{0}} {L : LB X} {L' : LB X'} {F : X' ⟶ X}

theorem exists_ratio {M : LB X} (cov : ∀ x, ∃ j, x ∈ M.U j) {t t' : LB.Gen M} (ht : t.IsGen) (ht' : t'.IsGen) :
    ∃ u : Γ(X, ⊤)ˣ, ∀ (Z : Scheme.{0}) (r : Z ⟶ X) (z : Z) (j : M.ι), r z ∈ M.U j →
      gm r z _ (t.s j) = gm r z ⊤ u * gm r z _ (t'.s j) := by
  obtain ⟨u, hu⟩ := glue_unit ⊤ M.U (fun _ => le_top) (fun x _ => TopologicalSpace.Opens.mem_iSup.2 (cov x))
    (fun j => t.s j * (t'.s j)⁻¹) (fun i j x hx => by
      rw [map_mul, map_mul, map_inv, map_inv, GtCoordCompare.gm_gen ht (𝟙 X) x hx.1 hx.2,
        GtCoordCompare.gm_gen ht' (𝟙 X) x hx.1 hx.2, ← div_eq_mul_inv, ← div_eq_mul_inv, mul_div_mul_left_eq_div])
  refine ⟨u, fun Z r z j hj => ?_⟩
  rw [← gm_res r z (le_top : M.U j ≤ ⊤) hj u, hu, map_mul, map_inv, inv_mul_cancel_right]

theorem exists_rigidified (hL : L.IsLB) (hL' : L'.IsLB) (π : X' ⟶ T) (σ : T ⟶ X') (hσ : σ ≫ π = 𝟙 T)
    (w₀ : LB.Iso L' (L.pull F)) (hw₀ : w₀.IsGen) (ρ' : LB.Gen (L'.pull σ)) (hρ' : ρ'.IsGen) {φ : Y ⟶ X}
    (ρ : LB.Gen (L.pull φ)) (hρ : ρ.IsGen) (h : T ⟶ Y) (e : σ ≫ F = h ≫ φ) :
    ∃ w : LB.Iso L' (L.pull F), w.IsGen ∧ PMaps w (K := PUnit) (fun _ => σ) (fun _ => φ) (fun _ => 1) ρ' ρ h := by
  obtain ⟨t, ht, hv⟩ := exists_up ((isGen_iff w₀).1 hw₀) hL hL' ρ' hρ'
  have ex : ∀ g : T ⟶ X, g = h ≫ φ → ∃ t' : LB.Gen (L.pull g), t'.IsGen ∧ ∀ (Z : Scheme.{0}) (r : Z ⟶ T) (z : Z) p,
      r z ∈ (L.pull g).U p → gm r z _ (t'.s p) = gm (r ≫ h) z ((L.pull φ).U p) (ρ.s p) := by
    rintro _ rfl
    exact ⟨LB.pullGen L _ _ ρ h, DVR.pullGen_isGen _ _ _ _ hρ h, fun Z r z p hp =>
      (gm_res r z _ hp _).trans (gm_pull r h z _ (mem_pull.2 (mem_pull₂.1 hp)) _)⟩
  obtain ⟨t', ht', hv'⟩ := ex _ e
  obtain ⟨u, hu⟩ := exists_ratio (M := L.pull (σ ≫ F)) (fun x => by
    obtain ⟨j, hj⟩ := exists_chart hL (F (σ x))
    exact ⟨fun _ => j, mem_pull₂.2 hj⟩) ht' ht
  let w : LB.Iso L' (L.pull F) := ⟨fun p => res le_top (pullU π ⊤ u) * w₀.s p⟩
  have hw : ∀ (Z : Scheme.{0}) (r : Z ⟶ X') (z : Z) j k, F (r z) ∈ L.U j → r z ∈ L'.U k →
      gw w r z j k = gm (r ≫ π) z ⊤ u * gw w₀ r z j k := fun Z r z j k hj hk =>
    (map_mul _ _ _).trans (congrArg (· * _) (GtCoordCompare.gm_res_pull_top r z π
      (V := (L.pull F).U (fun _ => j) ⊓ L'.U k) ⟨mem_pull.2 hj, hk⟩ _ u))
  refine ⟨w, (isGen_iff w).2 fun Z r z j j' k k' hj hj' hk hk' => ?_, fun Z r z p q hp hq => ?_⟩
  · rw [hw Z r z j k hj hk, hw Z r z j' k' hj' hk', (isGen_iff w₀).1 hw₀ Z r z j j' k k' hj hj' hk hk']
    exact mul_left_comm _ _ _
  · have m : r z ∈ (L.pull (σ ≫ F)).U p := mem_pull₂.2 (hp _)
    refine (hv' Z r z p m).symm.trans ((hu Z r z p m).trans ?_)
    refine (congrArg _ (hv Z r z p q m (Set.mem_iInter.2 hq))).trans ?_
    rw [pw, Fintype.prod_unique, Fintype.prod_unique, zpow_one, zpow_one, hw Z (r ≫ σ) z _ _ (hp _) (hq _),
      Category.assoc, hσ, Category.comp_id, _root_.mul_assoc]

end Rigid

section Cube

open GlobalTheory.IndefiniteRowSideFullHecke.SeparatedSymmetricModel

variable {S S' : Scheme.{0}} (p : S' ⟶ S) {G : Over S} {H T : Over S'}

end Cube

section Clauses

open GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.SeparatedSymmetricModel

variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegPre R}
  {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G] {e : ℕ}

structure GtMatch (g : GtCoord I D e G) (j : CanonicalRigidImages.GtIso D I e G) : Prop where
  q : g.q = j.q
  i : g.i = j.i
  t : ∀ χ, HEq (g.t χ) (j.x χ)

theorem Oφ_eq {g : GtCoord I D e G} {j : CanonicalRigidImages.GtIso D I e G} (h : g.q = j.q) (χ : D.X) :
    D.Oφ g.pG χ = CanonicalRigidImages.oφ D I e j.q χ := by
  rw [← h]
  exact congrArg (fun y => ![y.left, _, _, _]) (_root_.mul_comm g.pG (toUnit _ ≫ D.c χ))

theorem Oinvε_eq : Oinvε = CanonicalRigidImages.oεinv := by decide

variable {LG : RigLB G} {g : GtCoord I D e G} {j : CanonicalRigidImages.GtIso D I e G}
  {w : LB.Iso (LG.L.pull (fstG I e G).left) (D.P.L.pull g.pG.left)}
  {ph : LB.Iso (LG.L.pull (toG I e G).F) (D.P.L.pull (toB j).F)}

end Clauses

section Main

open GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.SeparatedSymmetricModel

variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R}
  {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G]

variable {D : DegData R I} {A : PolAV (Spec (CommRingCat.of (FractionRing R)))} {rA : LB.Gen (A.L.pull (eSec A.A))}

structure Match (u : Out.UnifPre I D A G) (v : SeparatedSymmetricModel.UnifPre R I D A rA G) : Prop where
  gen : v.gen = u.gen.symm
  LG : v.LG = u.LG
  cub : HEq v.cub u.cubG
  sym : HEq v.sym u.symG
  gt : ∀ e, GtMatch (u.gt e) (v.j e)
  w : ∀ e, HEq (u.w e) (v.ph e)

end Main

end GlobalTheory.UnifPreCompare
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.PtEqOfProportional
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.TorsionImage

open FieldBaseChange

theorem translT_translPt {S : Scheme.{0}} {A T : Over S} [GrpObj A] (x y : T ⟶ A) :
    translT A x ≫ translPt A y = translPt A (y * x) := by
  show lift (fst T A) ((fst T A ≫ x) * snd T A) ≫ ((fst T A ≫ y) * snd T A) = (fst T A ≫ (y * x)) * snd T A
  simp only [MonObj.comp_mul, lift_fst_assoc, lift_snd, _root_.mul_assoc]

theorem translPt_one {S : Scheme.{0}} {A : Over S} [GrpObj A] (T : Over S) :
    translPt A (1 : T ⟶ A) = snd T A := by
  show (fst T A ≫ 1) * snd T A = _
  rw [MonObj.comp_one, _root_.one_mul]

theorem translT_inv {S : Scheme.{0}} {A T : Over S} [GrpObj A] (x : T ⟶ A) :
    translT A x⁻¹ ≫ translT A x = 𝟙 _ := by
  apply CartesianMonoidalCategory.hom_ext
  · simp [translT]
  · rw [Category.assoc, Category.id_comp]
    exact (congrArg (_ ≫ ·) (lift_snd _ _)).trans
      ((translT_translPt _ _).trans (by rw [mul_inv_cancel, translPt_one]))

theorem eq_of_gen {S : Scheme.{0}} (P : PolAV S) {F : Type} [CommRing F] (q : Spec (CommRingCat.of F) ⟶ S)
    (x x' : Over.mk q ⟶ P.A)
    (r : LB.Gen (LB.LinComb P.L (K := Fin 2) ![(translPt P.A x).left, (translPt P.A x').left] ![1, -1]))
    (hr : r.IsGen) : x = x' := by
  refine mul_inv_eq_one.1 (P.ktriv F q (x * x'⁻¹) fun p => ⟨⊤, trivial, ?_⟩)
  obtain ⟨w, hw, -⟩ := VVRank.exists_gen_pullTo
    (φ' := ![(translPt P.A (x * x'⁻¹)).left, (snd (Over.mk q) P.A).left]) r hr (translT P.A x'⁻¹).left (fun i => by
      fin_cases i
      · exact congrArg (fun q => q.left) (translT_translPt x'⁻¹ x)
      · exact congrArg (fun q => q.left) ((translT_translPt x'⁻¹ x').trans
          (by rw [mul_inv_cancel, translPt_one])))
  exact exists_isGen_pull (translDiff P.A P.L (x * x'⁻¹)) w hw _

theorem exists_smul_of_phiVal {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {F : Type} [Field F]
    [Algebra (FractionRing R) F] {k : ℕ} (p : QkPt D F k)
    (w w' : LB.Gen (LB.LinComb D.P.L (DegPre.lineφ D F p.g.b) (DegPre.lineε k))) (hw : w.IsGen) (hw' : w'.IsGen) :
    ∃ c : F, c ≠ 0 ∧ ∀ s t t' : Fam D F k, DVR.PhiVal p w s.s t.s → DVR.PhiVal p w' s.s t'.s → t' = c • t := by
  obtain ⟨a, ha⟩ := H1.exists_const D.P.L D.P.isLB (𝟙 _) (fun a => ⟨a, rfl⟩)
    (LB.mulGen D.P.L _ _ _ _ w' (LB.invGen D.P.L _ _ w))
    (DVR.mulGen_isGen _ _ _ _ _ _ _ hw' (DVR.invGen_isGen _ _ _ _ hw)) (fun U _ h => by
      refine (DVR.prod_sum₂ _ (c := ∏ i, h (DegPre.lineφ D F p.g.b i) ^ DegPre.lineε k i) rfl
        (DVR.prod_neg _ _ rfl)).trans ?_
      exact mul_inv_cancel _)
  obtain ⟨c, rfl⟩ := (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of F)).inv).2 a
  refine ⟨c, ?_, fun s t t' h h' => DVR.phi_unique p w' h' fun α β e' T ρ z J hJ => ?_⟩
  · rintro rfl
    let z : (TF (R := R) F).left := (default : PrimeSpectrum F)
    choose J hJ using fun χ : (TF (R := R) F).left ⟶ D.P.A.left => exists_chart D.P.isLB (χ z)
    refine Units.ne_zero _ ((ha _ (𝟙 _) z J hJ).trans ?_)
    exact (congrArg _ (map_zero _)).trans (gs_zero' _ z ⊤ trivial)
  · have e := ha _ (ρ ≫ fst _ _).left z J hJ
    rw [val_mul hJ, val_inv, Category.comp_id] at e
    refine (DVR.sval_smul c t β ρ.left z hJ).trans ?_
    rw [h α β e' T ρ z J hJ, val_mul hJ, val_mul hJ]
    refine (congrArg (· * _) e.symm).trans ?_
    rw [mul_left_comm, ← Units.val_mul]
    congr 2
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv]
    abel

theorem pt_eq_of_proportional (hS : SecBaseChangeSt) {K : Type} [Field K] (P : PolAV (Spec (CommRingCat.of K)))
    {F : Type} [Field F] (q : Spec (CommRingCat.of F) ⟶ Spec (CommRingCat.of K)) {n : ℕ} (hn : 1 ≤ n)
    (θ θ' : ThetaGrp P.A P.L (n : ℤ) (Over.mk q)) (c : Γ((Over.mk q).left, ⊤)ˣ)
    (H : ∀ t u u', IsActOf P.A P.L (n : ℤ) θ t u → IsActOf P.A P.L (n : ℤ) θ' t u' → ∀ y J, Good P.L y J →
      VVRank.sv P.A u' (𝟙 _) y J =
        (gm (𝟙 _ ≫ (fst (Over.mk q) P.A).left) y ⊤ c).val * VVRank.sv P.A u (𝟙 _) y J) : θ.pt = θ'.pt := by
  have hL := P.isLB
  let T := Over.mk q
  have := P.isAb.smooth
  have := P.isAb.geomConnected
  have := grpObj_geometricallyIntegral_of_smooth _ P.A
  have : IsIntegral (T ⊗ P.A).left :=
    pullback_of_geometrically' GeometricallyIntegral.geometrically_isIntegral F _
  have hN : ∀ y : (T ⊗ P.A).left, IsIntegrallyClosed ((T ⊗ P.A).left.presheaf.stalk y) := fun y =>
    ((isReduced_isNormalScheme_isLocallyNoetherian_of_smooth_over_field F _ (fst T P.A).left
      (inferInstanceAs (Smooth (pullback.fst q P.A.hom)))).2.1 y).2
  obtain ⟨b, hb, -⟩ := BoxSpan.exists_basis hS P 1 le_rfl F q
  have : Nontrivial Γ(T.left, ⊤) :=
    (Scheme.ΓSpecIso (CommRingCat.of F)).commRingCatIsoToRingEquiv.toEquiv.nontrivial
  have hne := hb.ne_zero ⟨0, by simp⟩
  let th : LB.Sec (LB.LinComb P.L (K := Fin 1) (fun _ => (snd T P.A).left) (fun _ => ((1 : ℕ) : ℤ))) :=
    SecM.toSec P.A (b ⟨0, by simp⟩)
  have tr : ∀ x : T ⟶ P.A, ∃ s : LB.Sec (LB.LinComb P.L (K := PUnit) (fun _ => (translPt P.A x).left) (fun _ => 1)),
      ∀ (Z : Scheme.{0}) (r : Z ⟶ (T ⊗ P.A).left) (z : Z) (J), Good P.L z J →
        sval s r z J = sval th (r ≫ (translT P.A x).left) z J := fun x => by
    have e : (translT P.A x).left ≫ (snd T P.A).left = (translPt P.A x).left :=
      congrArg (fun q => q.left) (lift_snd _ _ : translT P.A x ≫ snd T P.A = _)
    obtain ⟨s, hs⟩ := exists_sec hL (φ' := fun _ : PUnit => (translPt P.A x).left) (ε' := fun _ => 1)
      (fun U _ h => by simp only [e, Fintype.prod_unique, Nat.cast_one]) (H1.SectionArithmetic.pullSec th (translT P.A x).left)
    exact ⟨s, fun Z r z J hJ => (hs Z r z J hJ).trans (H1.SectionArithmetic.sval_pullSec _ _ r z hJ)⟩
  obtain ⟨s, hs⟩ := tr θ.pt
  obtain ⟨s', hs'⟩ := tr θ'.pt
  obtain ⟨t, ht⟩ := exists_sec hL (φ' := fun _ : Fin 1 => (snd T P.A).left) (ε' := fun _ => (n : ℤ))
    (fun U _ h => by simp) (H1.SectionArithmetic.powSec fun _ : Fin n => th)
  have ht' : ∀ (r : (T ⊗ P.A).left ⟶ (T ⊗ P.A).left) y J, Good P.L y J → sval t r y J = sval th r y J ^ n :=
    fun r y J hJ => by
      rw [ht _ r y J hJ, H1.SectionArithmetic.sval_powSec _ r y hJ, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  obtain ⟨u, hu⟩ : ∃ u, IsActOf P.A P.L (n : ℤ) θ t u := VVRank.exists_isTwistPull P.A hL θ.isGen t
  obtain ⟨u', hu'⟩ : ∃ u, IsActOf P.A P.L (n : ℤ) θ' t u := VVRank.exists_isTwistPull P.A hL θ'.isGen t
  have hc : (constGen P.A P.L c).IsGen := isGen_of_gm _ fun y j j' _ _ => by
    obtain rfl : j = j' := Subsingleton.elim _ _
    rw [trF, Fintype.prod_empty, _root_.one_mul]
  obtain ⟨v, hv, hv'⟩ := exists_gen hL (K' := Fin 2) (φ' := ![(translPt P.A θ'.pt).left, (translPt P.A θ.pt).left])
    (ε' := ![(n : ℤ), -(n : ℤ)]) (fun U _ h => by
      simp [Fintype.prod_sum_type, Fin.prod_univ_two])
    (LB.mulGen P.L _ _ _ _ (LB.invGen P.L ![(snd T P.A).left, (translPt P.A θ'.pt).left] ![(n : ℤ), -(n : ℤ)] θ'.φ)
      (LB.mulGen P.L ![(snd T P.A).left, (translPt P.A θ.pt).left] ![(n : ℤ), -(n : ℤ)] _ _ θ.φ
        (constGen P.A P.L c)))
    (DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.invGen_isGen _ _ _ _ θ'.isGen)
      (DVR.mulGen_isGen _ _ _ _ _ _ _ θ.isGen hc))
  obtain ⟨r, hr, -⟩ := RootUnit.exists_gen_of_pow _ _ hN P.L hL _ _ n hn s' s v hv (by
    by_contra h0
    have h0' : ∀ j, s.f j = 0 := fun j => by_contra fun hj => h0 ⟨j, hj⟩
    refine hne (Subtype.ext (funext fun j => sec_ext_val (s := th) (s' := H1.SectionArithmetic.secZero _) hL
      (fun y J hJ => ?_) j))
    have e := hs _ (translT P.A θ.pt⁻¹).left y J hJ
    rw [← Over.comp_left, translT_inv, Over.id_left] at e
    refine e.symm.trans (Eq.trans ?_ (gs_zero' _ y _ (hJ.mem _ _)).symm)
    exact (congrArg (gs _ y _) (h0' _)).trans (gs_zero' _ y _ (hJ.mem _ _))) (fun y J hJ => by
    have e := H t u u' hu hu' y J hJ
    rw [VVRank.sv_of_isTwistPull P.A hu _ y hJ, VVRank.sv_of_isTwistPull P.A hu' _ y hJ] at e
    have e₁ := (ht' _ y J hJ).trans (congrArg (· ^ n) (hs _ (𝟙 _) y J hJ).symm)
    have e₂ := (ht' _ y J hJ).trans (congrArg (· ^ n) (hs' _ (𝟙 _) y J hJ).symm)
    have e₃ := (congrArg _ e₂).symm.trans (e.trans (congrArg _ (congrArg _ e₁)))
    have e₄ := (hv' _ (𝟙 _) y J hJ).trans ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) (val_inv _ _)
      ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) rfl (H1.val_constGen _ c _ y J)))))
    rw [e₄, Units.val_mul, _root_.mul_assoc, Units.eq_inv_mul_iff_mul_eq, Units.val_mul, _root_.mul_assoc]
    exact e₃.trans (mul_left_comm _ _ _))
  exact (eq_of_gen P q _ _ r hr).symm

theorem qkToAkU_unique : Laws → Laws2 → ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R), AdmBase R I → ∀ (D : DegData R I) (A : PolAV (Spec (CommRingCat.of (FractionRing R)))) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (U : Unif I D A G) (F : Type) [Field F] [Algebra (FractionRing R) F] (n : ℕ), 1 ≤ n → ∀ (p : QkPt D.toPre F n) (x x' : TFK (R := R) F ⟶ A.A), QkToAkU U.toUnifPre F n p x → QkToAkU U.toUnifPre F n p x' → x = x' := by
  intro hL _ R _ _ I _ D A G _ _ _ U F _ _ n hn p x x' hx hx'
  obtain ⟨w₀, hw₀⟩ := U.ext
  obtain ⟨θ, rfl, -⟩ := TorsionTheta.exists_theta_acts hL.kerPow _ A F _ n hn x (hx w₀ hw₀).1
  obtain ⟨θ', rfl, -⟩ := TorsionTheta.exists_theta_acts hL.kerPow _ A F _ n hn x' (hx' w₀ hw₀).1
  obtain ⟨w, hw, h⟩ := (hx w₀ hw₀).2 θ rfl
  obtain ⟨w', hw', h'⟩ := (hx' w₀ hw₀).2 θ' rfl
  obtain ⟨e, he⟩ := exists_linearEquiv_expandsF hL.globalFns U F hn w₀ hw₀
  obtain ⟨c, hc, hcs⟩ := exists_smul_of_phiVal p w w' hw hw'
  refine pt_eq_of_proportional hL.secBaseChange A _ hn θ θ'
    (Units.map (Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom.toMonoidHom (Units.mk0 c hc))
    fun t u u' hu hu' y J hJ => ?_
  have a := hcs _ _ _
    ((DVR.phiRel_iff hL.globalFns p w hw _ _).1 (h t u _ _ ((he _ _).2 rfl) ((he _ _).2 rfl) hu))
    ((DVR.phiRel_iff hL.globalFns p w' hw' _ _).1 (h' t u' _ _ ((he _ _).2 rfl) ((he _ _).2 rfl) hu'))
  obtain rfl := e.injective (a.trans (e.map_smul c u).symm)
  exact (sval_smul' hJ _ c _).trans (congrArg (· * _) (gs_unit _ y ⊤ trivial
    (Units.map (Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom.toMonoidHom (Units.mk0 c hc))))

end GlobalTheory.TorsionImage
end

