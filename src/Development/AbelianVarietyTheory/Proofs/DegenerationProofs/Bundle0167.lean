import Mathlib
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.Bundle0034
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
import Development.AbelianVarietyTheory.Definitions.Degenerations.PlOrdSomeOfAssociated
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.SemistableFin
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0008
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0005
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0006
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0022
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0165
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.CubePullbacks.CubePull
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0017
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0162
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Development.AbelianVarietyTheory.Definitions.Degenerations.RigGen
import Development.AbelianVarietyTheory.Definitions.Uniformization.ExistsInKNeOne
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0097
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0123
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0174
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0062
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigidSys
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBCPf
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0129
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0123
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ThetaCoordinatesExistUniqueSeparatePoints
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle0001
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0166

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.CardTorsionAbelianVarietyLeConstMulPow
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS

namespace GlobalTheory.SS

theorem card_torsion_le : ∀ (k : Type) [Field k] [IsAlgClosed k] (B : Over (Sp k)) [GrpObj B], IsAbelianScheme B → ∀ (L : LB B.left), AmpleCub B L → ∀ a, SmoothOfRelativeDimension a B.hom → ∃ C : ℕ, ∀ n : ℕ, (n : k) ≠ 0 → Finite {x : (𝟙_ (Over (Sp k)) ⟶ B) // x ^ n = 1} ∧ Nat.card {x : (𝟙_ (Over (Sp k)) ⟶ B) // x ^ n = 1} ≤ C * n ^ (2 * a) := by
  intro k _ _ B _ hB L _ a ha
  refine ⟨1, fun n hn => ?_⟩
  have h := GlobalTheory.T.abelianVarietyTorsionCardEqPow k B a n hB ha hn
  have hn0 : n ≠ 0 := by
    rintro rfl
    exact hn Nat.cast_zero
  refine ⟨Nat.finite_of_card_ne_zero ?_, ?_⟩
  · rw [h]
    exact pow_ne_zero _ hn0
  · rw [h, Nat.one_mul]

end GlobalTheory.SS
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsCompatibleSectionsThickeningsLocalRing
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.SecLifts

theorem exists_compatible_sections_local : ∀ (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] (I : Ideal R), I ≠ ⊤ → ∀ (Y : ∀ e : ℕ, Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) (β : ∀ e, (Y e).left ⟶ (Y (e + 1)).left), (∀ e, IsPullback (β e) (Y e).hom (Y (e + 1)).hom (thickTrans R I e)) → (∀ e, Flat (Y e).hom) → (∀ e, IsProjBy (Y e).hom) → ∀ (N : ∀ e, LB (Y e).left) (v : ∀ e, LB.Iso (N e) ((N (e + 1)).pull (β e))), (∀ e, (N e).IsLB ∧ (v e).IsGen) → ∀ (K : Type) [Field K] (g₀ : R ⧸ I ^ (0 + 1) →+* K), Function.Surjective g₀ → ∀ (X₀ : Scheme.{0}) (π : X₀ ⟶ (Y 0).left) (f₀ : X₀ ⟶ Spec (CommRingCat.of K)), IsPullback π f₀ (Y 0).hom (Spec.map (CommRingCat.ofHom g₀)) → ∀ (N₀ : LB X₀) (w₀ : LB.Iso N₀ ((N 0).pull π)), N₀.IsLB → w₀.IsGen → FirstCohomologyVanishes N₀ → ∀ s₀ : LB.Sec (N 0), ∃ s : ∀ e, LB.Sec (N e), s 0 = s₀ ∧ ∀ e, (∀ z (k : (N (e + 1)).ι) (k' : (N e).ι), (β e) z ∈ (N (e + 1)).U k → z ∈ (N e).U k' → gs (β e) z _ ((s (e + 1)).f k) = (Geo.Tor.gw (v e) (𝟙 _) z k k').val * gs (𝟙 _) z _ ((s e).f k')) := by
  intro R _ _ _ I hI Y β hβ hfl hpr N v hN K _ g₀ hg₀ X₀ π f₀ hπ N₀ w₀ hN₀ hw₀ h1 s₀
  have step : ∀ e (s' : LB.Sec (N e)), ∃ s : LB.Sec (N (e + 1)),
      ∀ z (k : (N (e + 1)).ι) (k' : (N e).ι), (β e) z ∈ (N (e + 1)).U k → z ∈ (N e).U k' →
        gs (β e) z _ (s.f k) = (Geo.Tor.gw (v e) (𝟙 _) z k k').val * gs (𝟙 _) z _ (s'.f k') := by
    intro e s'
    obtain ⟨j, hj, w, hw⟩ := exists_closedFibre R I Y β hβ N v hN e
    have g := (isGen_iff _).1 hw
    have g' := (isGen_iff _).1 hw₀
    obtain ⟨w'', T⟩ := exists_comp (hN 0).1 w w₀ g g' (hN (e + 1)).1 hN₀
    have hne : I ^ (e + 1 + 1) ≠ ⊤ := fun h =>
      hI (top_le_iff.1 (h ▸ Ideal.pow_le_self (Nat.succ_ne_zero _)))
    have : Nontrivial (R ⧸ I ^ (e + 1 + 1)) := Ideal.Quotient.nontrivial_iff.2 hne
    have : IsLocalRing (R ⧸ I ^ (e + 1 + 1)) :=
      IsLocalRing.of_surjective' (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective
    have h := hπ.paste_horiz hj
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp] at h
    exact GlobalTheory.T.exists_section_lift_closed_baseChange_of_h1Vanishes (R ⧸ I ^ (e + 1 + 1)) _ (Y (e + 1)).hom (hfl (e + 1)) (hpr (e + 1)) (N (e + 1))
      (hN (e + 1)).1 K _ (hg₀.comp (Ideal.Quotient.factor_surjective _)) X₀ (π ≫ j) f₀ h N₀ w'' hN₀
      ((isGen_iff _).2 (T.pgen_comp (hN 0).1 g g')) h1 _ _ (Ideal.Quotient.factor_surjective _) _ (β e)
      (Y e).hom (hβ e) (N e) (v e) (hN e).1 (hN e).2 s'
  choose L hL using step
  exact ⟨fun e => Nat.rec (motive := fun e => LB.Sec (N e)) s₀ L e, rfl, fun e => hL e _⟩

end GlobalTheory.SecLifts
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsFormCorrectionOfVanishingAfterBaseChange
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.FormCorr

section
open MvPolynomial

variable {X X' Z : Scheme.{0}} {R R' : Type} [CommRing R] [CommRing R']

theorem eval₂_scale {σ A : Type} [CommRing A] (φ : R →+* A) (c : A) (x : σ → A) {F : MvPolynomial σ R}
    {e : ℕ} (hF : F.IsHomogeneous e) : eval₂ φ (fun j => c * x j) F = c ^ e * eval₂ φ x F := by
  rw [eval₂_eq, eval₂_eq, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a ha => ?_
  have hd : ∑ j ∈ a.support, a j = e := by
    have := hF (mem_support_iff.1 ha)
    rw [← this, Finsupp.weight_apply, Finsupp.sum]
    simp
  simp only [mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, hd]
  ring

def gsHom (r : Z ⟶ X) (z : Z) (U : X.Opens) (h : r z ∈ U) : Γ(X, U) →+* Z.presheaf.stalk z :=
  (Z.presheaf.germ (r ⁻¹ᵁ U) z h).hom.comp (r.app U).hom

theorem gsHom_apply (r : Z ⟶ X) (z : Z) (U : X.Opens) (h : r z ∈ U) (a : Γ(X, U)) :
    gsHom r z U h a = gs r z U a := (gs_eq r z U h a).symm

def cstGerm (p : Z ⟶ Spec (CommRingCat.of R)) (z : Z) : R →+* Z.presheaf.stalk z :=
  (gsHom p z ⊤ trivial).comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom

theorem gs_eval {σ : Type} (p : X ⟶ Spec (CommRingCat.of R)) (r : Z ⟶ X) (z : Z) (U : X.Opens) (h : r z ∈ U)
    (x : σ → Γ(X, U)) (F : MvPolynomial σ R) :
    gs r z U (eval₂Hom (AbLaw.cst p U) x F) = eval₂ (cstGerm (r ≫ p) z) (fun j => gs r z U (x j)) F := by
  rw [← gsHom_apply r z U h, coe_eval₂Hom, eval₂_comp_left]
  congr 1
  · ext a
    exact (gsHom_apply r z U h _).trans (((gs_res r z le_top h _).trans (gs_pull r p z ⊤ trivial _)).trans
      (gsHom_apply (r ≫ p) z ⊤ trivial _).symm)
  · ext j
    exact gsHom_apply r z U h _

theorem const_comp (p : X ⟶ Spec (CommRingCat.of R')) (g : R →+* R') (U : X.Opens) :
    AbLaw.cst (p ≫ Spec.map (CommRingCat.ofHom g)) U = (AbLaw.cst p U).comp g := by
  ext a
  have := congrArg (fun q => q.hom a) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom g))
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at this
  simp only [AbLaw.cst, RingHom.comp_apply, Scheme.Hom.comp_appTop, CommRingCat.hom_comp]
  rw [this]

theorem gs_sec {H : LB X} (s : LB.Sec H) (r : Z ⟶ X) (z : Z) {i j : H.ι} (hi : r z ∈ H.U i) (hj : r z ∈ H.U j) :
    gs r z _ (s.f i) = (gm r z _ (H.g i j)).val * gs r z _ (s.f j) := by
  have hm : r z ∈ H.U i ⊓ H.U j := ⟨hi, hj⟩
  have e := congrArg (gs r z _) (s.compat i j)
  rwa [gs_res _ z _ hm, gs_mul _ z _ hm, gs_res _ z _ hm, gs_unit _ z _ hm] at e

def formSec {σ : Type} (p : X ⟶ Spec (CommRingCat.of R)) {H : LB X} (s : σ → LB.Sec H) {F : MvPolynomial σ R}
    {t : ℕ} (hF : F.IsHomogeneous t) : LB.Sec (AbLaw.pw H t) where
  f := fun k => eval₂Hom (AbLaw.cst p (H.U k)) (fun j => (s j).f k) F
  compat := fun i j => fn_ext fun y hy => by
    refine (gs_res _ y _ hy _).trans (Eq.trans ?_ ((gs_mul _ y _ hy _ _).trans (congrArg₂ (· * ·)
      (gs_unit _ y _ hy _) (gs_res _ y _ hy _))).symm)
    refine (gs_eval p (𝟙 X) y (H.U i) hy.1 _ F).trans (Eq.trans ?_ (congrArg₂ (· * ·)
      (congrArg Units.val (map_zpow (gm (𝟙 X) y (H.U i ⊓ H.U j)) (H.g i j) t))
      (gs_eval p (𝟙 X) y (H.U j) hy.2 _ F)).symm)
    rw [zpow_natCast, Units.val_pow_eq_pow_val, ← eval₂_scale _ _ _ hF]
    congr 1
    exact funext fun a => gs_sec (s a) _ y hy.1 hy.2

def pwIso {H : LB X} {H' : LB X'} {β : X' ⟶ X} (w : LB.Iso H' (H.pull β)) (t : ℤ) :
    LB.Iso (AbLaw.pw H' t) ((AbLaw.pw H t).pull β) := ⟨fun p => w.s p ^ t⟩

theorem gw_pwIso {H : LB X} {H' : LB X'} {β : X' ⟶ X} (w : LB.Iso H' (H.pull β)) (t : ℤ) (r : Z ⟶ X') (z : Z)
    (j : H.ι) (k : H'.ι) : gw (pwIso w t) r z j k = gw w r z j k ^ t :=
  map_zpow (gm r z ((H.pull β).U (fun _ => j) ⊓ H'.U k)) (w.s (fun _ => j, k)) t

theorem pgen_pwIso {H : LB X} {H' : LB X'} {β : X' ⟶ X} {w : LB.Iso H' (H.pull β)} (hw : PGen w) (t : ℤ) :
    PGen (pwIso w t) := by
  intro Y f y j j' k k' hj hj' hk hk'
  have e := congrArg (· ^ t) (hw Y f y j j' k k' hj hj' hk hk')
  simp only [mul_zpow, inv_zpow] at e
  refine (gw_pwIso w t f y j k).trans (e.trans (congrArg₂ (· * ·) (congrArg₂ (· * ·) ?_ (congrArg (·⁻¹) ?_))
    (gw_pwIso w t f y j' k').symm))
  · exact (map_zpow _ _ _).symm
  · exact (map_zpow _ _ _).symm

def Rel {H : LB X} {H' : LB X'} (β : X' ⟶ X) (w : LB.Iso H' (H.pull β)) (s : LB.Sec H) (s' : LB.Sec H') : Prop :=
  ∀ z (k : H.ι) (k' : H'.ι), β z ∈ H.U k → z ∈ H'.U k' →
    gs β z _ (s.f k) = (gw w (𝟙 _) z k k').val * gs (𝟙 _) z _ (s'.f k')

theorem Rel.form {σ : Type} {H : LB X} {H' : LB X'} {β : X' ⟶ X} {w : LB.Iso H' (H.pull β)} {s : σ → LB.Sec H}
    {s' : σ → LB.Sec H'} (h : ∀ j, Rel β w (s j) (s' j)) (p : X ⟶ Spec (CommRingCat.of R))
    {F : MvPolynomial σ R} {t : ℕ} (hF : F.IsHomogeneous t) (z : X') (k : H.ι) (k' : H'.ι) (hk : β z ∈ H.U k)
    (hk' : z ∈ H'.U k') :
    gs β z _ (eval₂Hom (AbLaw.cst p (H.U k)) (fun j => (s j).f k) F) = (gw w (𝟙 _) z k k' ^ (t : ℤ)).val *
      gs (𝟙 _) z _ (eval₂Hom (AbLaw.cst (β ≫ p) (H'.U k')) (fun j => (s' j).f k') F) := by
  rw [gs_eval p β z _ hk, gs_eval (β ≫ p) (𝟙 _) z _ hk', Category.id_comp, zpow_natCast, Units.val_pow_eq_pow_val,
    ← eval₂_scale _ _ _ hF]
  congr 1
  exact funext fun j => h j z k k' hk hk'

theorem gs_cst (p : X ⟶ Spec (CommRingCat.of R)) (r : Z ⟶ X) (z : Z) (U : X.Opens) (h : r z ∈ U) (a : R) :
    gs r z U (AbLaw.cst p U a) = cstGerm (r ≫ p) z a := by
  have e := gs_eval (σ := Empty) p r z U h Empty.elim (MvPolynomial.C a)
  rwa [MvPolynomial.eval₂Hom_C, MvPolynomial.eval₂_C] at e

theorem gs_lin {n : ℕ} (p : X ⟶ Spec (CommRingCat.of R)) (r : Z ⟶ X) (z : Z) (U : X.Opens) (h : r z ∈ U)
    (c : Fin n → R) (x : Fin n → Γ(X, U)) :
    gs r z U (∑ i, AbLaw.cst p U (c i) * x i) = ∑ i, cstGerm (r ≫ p) z (c i) * gs r z U (x i) := by
  rw [← gsHom_apply r z _ h, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_mul, gsHom_apply, gsHom_apply, gs_cst p r z _ h]

theorem germ_rel {n : ℕ} {M : LB X} {M' : LB X'} {β : X' ⟶ X} {w : LB.Iso M' (M.pull β)} {σ : LB.Sec M}
    {σ' : LB.Sec M'} {τ : Fin n → LB.Sec M} {τ' : Fin n → LB.Sec M'} (hσ : Rel β w σ σ')
    (hτ : ∀ i, Rel β w (τ i) (τ' i)) (p : X ⟶ Spec (CommRingCat.of R)) (c : Fin n → R) (z : X') (k : M.ι)
    (k' : M'.ι) (hk : β z ∈ M.U k) (hk' : z ∈ M'.U k') :
    gs β z _ (σ.f k) = gs β z _ (∑ i, AbLaw.cst p (M.U k) (c i) * (τ i).f k) ↔
      gs (𝟙 _) z _ (σ'.f k') = gs (𝟙 _) z _ (∑ i, AbLaw.cst (β ≫ p) (M'.U k') (c i) * (τ' i).f k') := by
  have e : gs β z _ (∑ i, AbLaw.cst p (M.U k) (c i) * (τ i).f k) = (gw w (𝟙 _) z k k').val *
      gs (𝟙 _) z _ (∑ i, AbLaw.cst (β ≫ p) (M'.U k') (c i) * (τ' i).f k') := by
    rw [gs_lin p β z _ hk, gs_lin (β ≫ p) (𝟙 _) z _ hk', Category.id_comp, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hτ i z k k' hk hk']
    ring
  rw [e, hσ z k k' hk hk', Units.mul_right_inj]

end

theorem exists_form_correction : ∀ (A : Type) [CommRing A] [IsLocalRing A] [IsNoetherianRing A] (X : Scheme.{0}) (f : X ⟶ Spec (CommRingCat.of A)), Flat f → ∀ (H : LB X) (n : ℕ) (s : Fin (n + 1) → LB.Sec H), H.IsLB → VeryAmpleBy f H s → ∀ (K : Type) [Field K] (g₀ : A →+* K), Function.Surjective g₀ → ∀ (X₀ : Scheme.{0}) (π : X₀ ⟶ X) (f₀ : X₀ ⟶ Spec (CommRingCat.of K)), IsPullback π f₀ f (Spec.map (CommRingCat.ofHom g₀)) → ∀ (H₀ : LB X₀) (w₀ : LB.Iso H₀ (H.pull π)) (s₀ : Fin (n + 1) → LB.Sec H₀), H₀.IsLB → w₀.IsGen → (∀ j, (∀ z (k : (H).ι) (k' : (H₀).ι), (π) z ∈ (H).U k → z ∈ (H₀).U k' → gs (π) z _ ((s j).f k) = (Geo.Tor.gw (w₀) (𝟙 _) z k k').val * gs (𝟙 _) z _ ((s₀ j).f k'))) → ∀ t : ℕ, FirstCohomologyVanishes (pw H₀ t) → (∀ σ : LB.Sec (pw H₀ t), ∃ P : MvPolynomial (Fin (n + 1)) K, P.IsHomogeneous t ∧ ∀ k : H₀.ι, σ.f k = MvPolynomial.eval₂Hom (cst (f₀) ((H₀).U k)) (fun j => (s₀ j).f k) (P)) → ∀ (A' : Type) [CommRing A'] (g : A →+* A') (X' : Scheme.{0}) (β : X' ⟶ X) (f' : X' ⟶ Spec (CommRingCat.of A')), IsPullback β f' f (Spec.map (CommRingCat.ofHom g)) → ∀ (H' : LB X') (w : LB.Iso H' (H.pull β)) (s' : Fin (n + 1) → LB.Sec H'), H'.IsLB → w.IsGen → (∀ j, (∀ z (k : (H).ι) (k' : (H').ι), (β) z ∈ (H).U k → z ∈ (H').U k' → gs (β) z _ ((s j).f k) = (Geo.Tor.gw (w) (𝟙 _) z k k').val * gs (𝟙 _) z _ ((s' j).f k'))) → ∀ F : MvPolynomial (Fin (n + 1)) A, F.IsHomogeneous t → (∀ k : (H').ι, MvPolynomial.eval₂Hom (cst (β ≫ f) ((H').U k)) (fun j => (s' j).f k) (F) = 0) → ∃ G : MvPolynomial (Fin (n + 1)) A, G.IsHomogeneous t ∧ (∀ d, g (MvPolynomial.coeff d G) = 0) ∧ (∀ k : (H).ι, MvPolynomial.eval₂Hom (cst (f) ((H).U k)) (fun j => (s j).f k) (F - G) = 0) := by
  intro A _ _ _ X f hf H n s hH hva K _ g₀ hg₀ X₀ π f₀ hπ H₀ w₀ s₀ hH₀ hw₀ hs₀ t h1 hsurj A' _ g X' β f' hβ H' w s'
    hH' hw hs' F hF hF0
  have hM := isLB_pw hH (t : ℤ)
  have hM' := isLB_pw hH' (t : ℤ)
  obtain ⟨m, τ, hτ⟩ := GlobalTheory.T.exists_sections_basis_baseChange_h1Vanishing A X f hf ⟨H, hH, n, s, hva⟩ (AbLaw.pw H t) hM K g₀ hg₀ X₀ π f₀ hπ
    (AbLaw.pw H₀ t) (pwIso w₀ t) (isLB_pw hH₀ _) ((isGen_iff _).2 (pgen_pwIso ((isGen_iff _).1 hw₀) t)) h1
  choose Q hQ hτQ using fun i => GlobalTheory.T.sections_pow_veryAmple_are_forms_of_closedFibre A X f hf H n s hH hva K g₀ hg₀ X₀ π f₀ hπ H₀ w₀ s₀ hH₀ hw₀ hs₀ t h1
    hsurj (τ i)
  have hL := LB.isLB_pull hM (𝟙 X)
  have hu := CubePf.idIsoL_isGen hL
  choose P hP using fun σ => GlobalTheory.SecPullIso.exists_pull (𝟙 X) (AbLaw.pw H t) _ _ hM hL hu σ
  have hid : IsPullback (𝟙 X) f f (Spec.map (CommRingCat.ofHom (RingHom.id A))) := by
    rw [CommRingCat.ofHom_id, Spec.map_id]
    exact IsPullback.of_horiz_isIso ⟨by simp⟩
  obtain ⟨c, hc, -⟩ := hτ A (RingHom.id A) X (𝟙 X) f hid _ _ (fun i => P (τ i)) hL hu (fun i => hP (τ i))
    (P (formSec f s hF))
  have hc' : ∀ k, (formSec f s hF).f k = ∑ i, AbLaw.cst f ((AbLaw.pw H t).U k) (c i) * (τ i).f k := fun k =>
    fn_ext fun z hz => by
      obtain ⟨k', hk'⟩ := exists_chart hL z
      refine (germ_rel (hP _) (fun i => hP (τ i)) f c z k k' hz hk').2 ?_
      rw [Category.id_comp]
      exact congrArg _ (hc k')
  have hw' := (isGen_iff _).2 (pgen_pwIso ((isGen_iff _).1 hw) (t : ℤ))
  choose τ' hτ' using fun i => GlobalTheory.SecPullIso.exists_pull β (AbLaw.pw H t) _ _ hM hM' hw' (τ i)
  have hrel : Rel β (pwIso w t) (formSec f s hF) (formSec (β ≫ f) s' hF) := fun z k k' hk hk' =>
    (Rel.form hs' f hF z k k' hk hk').trans
      (congrArg (· * _) (congrArg Units.val (gw_pwIso w t (𝟙 _) z k k').symm))
  have hc'' : ∀ k', (formSec (β ≫ f) s' hF).f k' =
      ∑ i, AbLaw.cst f' ((AbLaw.pw H' t).U k') (g (c i)) * (τ' i).f k' := fun k' =>
    Eq.trans (fn_ext fun z hz => by
      obtain ⟨k, hk⟩ := exists_chart hM (β z)
      exact (germ_rel hrel hτ' f c z k k' hk hz).1 (congrArg _ (hc' k))) (by
      rw [hβ.w, const_comp]
      rfl)
  have hgc : (fun i => g (c i)) = 0 :=
    (hτ A' g X' β f' hβ _ _ τ' hM' hw' hτ' (formSec (β ≫ f) s' hF)).unique hc'' fun k' =>
      (hF0 k').trans (Finset.sum_eq_zero fun i _ =>
        (congrArg (· * (τ' i).f k') (map_zero (AbLaw.cst f' ((AbLaw.pw H' t).U k')))).trans (zero_mul _)).symm
  refine ⟨∑ i, MvPolynomial.C (c i) * Q i,
    MvPolynomial.IsHomogeneous.sum _ _ _ fun i _ => (hQ i).C_mul _, fun d => ?_, fun k => ?_⟩
  · rw [MvPolynomial.coeff_sum, map_sum]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [MvPolynomial.coeff_C_mul, map_mul, congrFun hgc i, Pi.zero_apply, zero_mul]
  · rw [map_sub, sub_eq_zero, map_sum]
    refine (hc' k).trans (Finset.sum_congr rfl fun i _ => ?_)
    rw [map_mul, MvPolynomial.eval₂Hom_C, hτQ i k]
    rfl

end GlobalTheory.FormCorr
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsKernelPolarisationTrivialSpreadLocalisatio
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical
open ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.GenSpread

theorem exists_kTriv : GlobalFnsSt → ∀ (R K : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [Field K] [Algebra R K] [IsFractionRing R K] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (A : Over (Sp K)) [GrpObj A] [IsCommMonObj A] (φ : A.left ⟶ G.left) (L : LB G.left) (L₀ : LB A.left), IsAbelianScheme G → IsGrpPullback A G (spMap (algebraMap R K)) φ → L.IsLB → L₀.IsLB → LBIso L₀ (L.pull φ) → GlobalTheory.AbLaw.IsProjBy G.hom → KTriv A L₀ → ∃ a : R, a ≠ 0 ∧ ∀ (R' : Type) [CommRing R'] (g : R →+* R'), IsUnit (g a) → ∀ (G' : Over (Sp R')) [GrpObj G'] [IsCommMonObj G'] (π : G'.left ⟶ G.left) (L' : LB G'.left), IsGrpPullback G' G (spMap g) π → L'.IsLB → LBIso L' (L.pull π) → KTriv G' L' := by
  intro hG R K _ _ _ _ _ _ G _ _ A _ _ φ L L₀ hA h hL hL₀ hw hP hk
  obtain ⟨hO, -, hK⟩ := GlobalTheory.UU.TrivTwist.inK_iff_trivial_twist _ G L hL
  obtain ⟨H, j, hj, hH⟩ := GlobalTheory.UU.TwistKer.exists_closed_twist_kernel hG R G hA hP L _ hL hO
  have hrep : ∀ (T : Over (Sp R)) (x : T ⟶ G), GlobalTheory.UU.InK G L x ↔ ∃ y : T ⟶ H, y ≫ j = x :=
    fun T x => (hK _ rfl T x).trans (hH T x)
  have hm : Mono j := (Over.forget _).mono_of_mono_map (inferInstanceAs (Mono j.left))
  obtain ⟨e, he⟩ := (hrep _ _).1 (GlobalTheory.UU.inK_one hL (𝟙_ _))
  have hprop := hA.proper
  have hH' : IsProper H.hom := by rw [← Over.w j]; infer_instance
  have hsec : e.left ≫ H.hom = 𝟙 (Sp R) := Over.w e
  have hcl : IsClosedImmersion e.left := by
    have : IsClosedImmersion (e.left ≫ H.hom) := by
      rw [hsec]
      exact (inferInstance : IsClosedImmersion (𝟙 (Sp R)))
    exact IsClosedImmersion.of_comp e.left H.hom
  obtain ⟨a, ha, key⟩ := GlobalTheory.T.closed_immersion_generic_unit_locus R K _ _ e.left H.hom hcl inferInstance inferInstance (fun B _ y t hy => by
    have hdi : (y ≫ j.left) ≫ G.hom = t ≫ spMap (algebraMap R K) := by
      rw [Category.assoc, Over.w j, hy]
    let x : Over.mk t ⟶ A := Over.homMk (h.1.lift _ _ hdi) (h.1.lift_snd _ _ _)
    let z : Over.mk (t ≫ spMap (algebraMap R K)) ⟶ H := Over.homMk y hy
    have hz : z ≫ j = pushPt h.1.w x := Over.OverMorphism.ext (h.1.lift_fst _ _ hdi).symm
    have hx : x = 1 := GlobalTheory.UU.InK.eq_one hk (GlobalTheory.UU.inK_of_push h hL hL₀ hw x ((hrep _ _).2 ⟨z, hz⟩))
    have hx' : pushPt h.1.w x = 1 := (congrArg (pushHom h (Over.mk t)) hx).trans (map_one _)
    have h1 : toUnit _ ≫ e = z := by
      rw [← cancel_mono j, hz, hx', Category.assoc, he, MonObj.comp_one]
    exact ⟨(toUnit (Over.mk (t ≫ spMap (algebraMap R K)))).left, congrArg (fun q => q.left) h1⟩)
  refine ⟨a, ha, fun R' _ g hg G' _ _ π L' h' hL' hw' B _ t x hx => ?_⟩
  obtain ⟨z, hz⟩ := (hrep _ _).1 (GlobalTheory.KTrivSpread.memKL_push h' hL hL' hw' t x hx)
  obtain ⟨y, hy⟩ := key R' g hg _ z.left t (Over.w z)
  let u : Over.mk (t ≫ spMap g) ⟶ 𝟙_ (Over (Sp R)) := Over.homMk y (by
    have := Over.w z
    rw [← hy, Category.assoc, hsec] at this
    exact this)
  have hu : u ≫ e = z := Over.OverMorphism.ext hy
  have h1 : pushPt h'.1.w x = pushPt h'.1.w (1 : Over.mk t ⟶ G') := by
    refine Eq.trans ?_ (map_one (pushHom h' (Over.mk t))).symm
    rw [← hz, ← hu, Category.assoc, he, MonObj.comp_one]
  exact Over.OverMorphism.ext (h'.1.hom_ext (congrArg (fun q => q.left) h1) (by rw [Over.w, Over.w]))

end GlobalTheory.GenSpread
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.KTrivOfClosedFibreLocalRingStatement
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kTriv_of_closed_fibre_localRing : Laws → Laws2 → ∀ (A : Type) [CommRing A] [IsLocalRing A] [IsNoetherianRing A] (B : Over (Spec (CommRingCat.of A))) [GrpObj B] [IsCommMonObj B], IsAbelianScheme B → ∀ N : LB B.left, N.IsLB → RelAmple B N → KTriv ((Over.pullback (spMap (IsLocalRing.residue A))).obj B) (N.pull (pullback.fst B.hom (spMap (IsLocalRing.residue A)))) → KTriv B N := by
  first | exact @GlobalTheory.KTrivLocal.kTriv_of_closed_fibre | exact GlobalTheory.KTrivLocal.kTriv_of_closed_fibre | (intros; apply GlobalTheory.KTrivLocal.kTriv_of_closed_fibre <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ModelSeriesEqUnitMulThetaPoint
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex
open GlobalTheory.ModelData

namespace GlobalTheory.ModelTheta

theorem series_eq_unit_mul_theta : Laws → TXSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (C : Type) [NontriviallyNormedField C] [IsUltrametricDist C] [CompleteSpace C] [IsAlgClosed C] [CharZero C] (o : Full D C) (M : Mdl o) (N' : NumD C) (ν' : NumOf M.P.D.toPre C N') (m : ℕ), Odd m → ∀ (p : D.La → QkPt M.P.D.toPre C (m ^ 2)) (q : D.La → N'.QT (m ^ 2)) (v : D.La → C), (∀ x (z : TFK (R := M.W) C ⟶ M.P.A.A), z.left = (o.I.ev (m ^ 2) x).left ≫ M.φ → M.P.ToA C (m ^ 2) (p x) z) → (∀ x, ν'.QPt (p x) (q x)) → o.Theta m v → (∃ c : Cˣ, ∀ x, N'.tx m (q x) = c * v x) ∧ (3 ≤ m → v ≠ 0) := by
  intro hL hTX E _ _ _ H D C _ _ _ _ _ o M N' ν' m hm p q v hpz hq hv
  let x : D.La → (TFK (R := M.W) C ⟶ M.P.A.A) := fun i =>
    Over.homMk ((o.I.ev (m ^ 2) i).left ≫ M.φ) (by
      rw [Category.assoc, M.cart.1.w, ← Category.assoc, Over.w]
      simp)
  have key := hTX M.W (IsLocalRing.maximalIdeal M.W) M.cdv rfl M.P.D M.P.A M.t.G M.t.semi M.P.U C M.ext N' ν' m hm
    D.La p q x (fun i => hpz i (x i) rfl) hq
  have hm0 : (m : C) ≠ 0 := Nat.cast_ne_zero.mpr hm.pos.ne'
  have hmu : IsUnit ((m : ℕ) : Γ(Sp C, ⊤)) := by
    have h1 : ((m : ℕ) : Γ(Sp C, ⊤)) = fnOf (m : C) := (map_natCast _ m).symm
    rw [h1]
    exact (IsUnit.mk0 _ hm0).map _
  have hm2 : 0 < m ^ 2 := pow_pos hm.pos 2
  have htors : ∀ i, o.I.ev (m ^ 2) i ^ (m ^ 2) = 1 := fun i => (o.I.onto (m ^ 2) hm2 _).2 ⟨i, rfl⟩
  have : Subsingleton (TFK (R := M.W) C).left := by
    change Subsingleton (PrimeSpectrum C)
    exact ⟨fun a b => PrimeSpectrum.ext (by
      have := a.isPrime
      have := b.isPrime
      rw [Ideal.eq_bot_of_prime a.asIdeal, Ideal.eq_bot_of_prime b.asIdeal])⟩
  have : Nonempty (TFK (R := M.W) C).left := by
    change Nonempty (PrimeSpectrum C)
    exact ⟨⟨⊥, Ideal.isPrime_bot⟩⟩
  have c1 := (GlobalTheory.CoordSep.isThetaPt_iff (T := TFK (R := M.W) C) hm hmu x _).1 key
  have hτ : 𝟙 (Sp C) ≫ (TFK (R := M.W) C).hom = (baseOver (Sp C)).hom ≫ jFK (R := M.W) C := by simp
  have hβ : 𝟙 (Sp C) ≫ Over.Hom.left (𝟙 (TFK (R := M.W) C)) = 𝟙 (Sp C) := by simp
  have hx : ∀ i, 𝟙 (Sp C) ≫ (x i).left = (o.I.ev (m ^ 2) i).left ≫ M.φ := fun i => Category.id_comp _
  have hz := GlobalTheory.ThetaPtMove.over_one (T := baseOver (Sp C)) (T₀ := TFK (R := M.W) C) M.cart (𝟙 (Sp C)) hτ
  have hg : ∀ th₀, IsGenSec M.P.A.A M.P.A.L 1 th₀ →
      IsGenSec M.P.A.A M.P.A.L 1 (VVRank.pullS M.P.A.A 1 (𝟙 (TFK (R := M.W) C)) th₀) :=
    fun th h => GlobalTheory.ThetaCoord.isGenSec_pullS M.P.A.isLB (𝟙 _) (𝟙 _) (by simp) h
  have hσ : IsIso (𝟙 (Sp C) : (baseOver (Sp C)).left ⟶ (TFK (R := M.W) C).left) := IsIso.id (Sp C)
  have c2 := GlobalTheory.FullExtend.isCoordPt_move (S := Sp (FractionRing M.W)) (S' := Sp C) (f := jFK (R := M.W) C)
    (T := baseOver (Sp C)) (T₀ := TFK (R := M.W) C) (𝟙 (Sp C)) (P₀ := M.P.A) (P := o.P) (φ := M.φ) M.cart M.lb
    (B := TFK (R := M.W) C) (𝟙 (Sp C)) (𝟙 _) hβ hτ hg (k := m) (I := D.La) (x := o.I.ev (m ^ 2)) (x₀ := x) hx htors
    (z := 1) (z₀ := 1) hz (v₀ := fun i => fnOf (N'.tx m (q i))) c1
  have e1 : ∀ y : Γ(Sp C, ⊤), (𝟙 (Sp C) : Sp C ⟶ Sp C).appTop.hom y = y := fun y => by simp
  simp only [e1] at c2
  obtain ⟨-, huniq, hthc, hsep⟩ := GlobalTheory.CoordSep.coord_exists_unique_separate hL C (Sp C) o.P (𝟙 (Sp C)) m hm hm0
    D.La (o.I.ev (m ^ 2)) htors
  have hv1 : IsCoordPt o.P m (o.I.ev (m ^ 2)) 1 (fun i => fnOf (v i)) := (hthc v).1 hv
  obtain ⟨c, hc⟩ := (huniq 1 v (fun i => N'.tx m (q i)) hv1).1 c2
  refine ⟨⟨c, fun i => ?_⟩, fun h3 => ?_⟩
  · have := congrFun hc i
    simpa using this
  · have hall : ∀ y : Over.mk (𝟙 (Sp C)) ⟶ o.P.A, y ^ m ^ 2 = 1 → ∃ i, o.I.ev (m ^ 2) i = y :=
      fun y hy => (o.I.onto (m ^ 2) hm2 y).1 hy
    exact (hsep h3 hall 1 1 v hv1 hv1).2

end GlobalTheory.ModelTheta
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.RelAmpleOfAmpleOnClosedSubschemeLocalBaseStatement
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.relAmple_of_ample_on_closed_subscheme_localBase : ∀ (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] (B : Over (Spec (CommRingCat.of R))) (M : LB B.left), Flat B.hom → IsProjBy B.hom → M.IsLB → ∀ (R₀ : Type) [CommRing R₀] [Nontrivial R₀] (g : R →+* R₀), Function.Surjective g → ∀ (Y₀ : Over (Spec (CommRingCat.of R₀))) (b : Y₀.left ⟶ B.left), IsPullback b Y₀.hom B.hom (Spec.map (CommRingCat.ofHom g)) → ∀ N₀ : LB Y₀.left, N₀.IsLB → LBIso N₀ (M.pull b) → RelAmple Y₀ N₀ → RelAmple B M := by
  first | exact @GlobalTheory.AmpleLocalBase.relAmple_of_closed | exact GlobalTheory.AmpleLocalBase.relAmple_of_closed | (intros; apply GlobalTheory.AmpleLocalBase.relAmple_of_closed <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ThetaCoordinatesExistUniqueSeparatePointsStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaCoordinates_exist_unique_separate_points : Laws → ∀ (K : Type) [Field K] [IsAlgClosed K] (S : Scheme.{0}) [IsLocallyNoetherian S] (P : PolAV S) (s : Sp K ⟶ S) (m : ℕ), Odd m → (m : K) ≠ 0 → ∀ (Ix : Type) (x : Ix → (Over.mk s ⟶ P.A)), (∀ i, x i ^ m ^ 2 = 1) → (∀ z, ∃ v : Ix → K, IsCoordPt P m x z fun i => fnOf (v i)) ∧ (∀ z (v v' : Ix → K), (IsCoordPt P m x z fun i => fnOf (v i)) → ((IsCoordPt P m x z fun i => fnOf (v' i)) ↔ ∃ c : Kˣ, v' = (c : K) • v)) ∧ (∀ v : Ix → K, (IsThetaPt P m x fun i => fnOf (v i)) ↔ IsCoordPt P m x 1 fun i => fnOf (v i)) ∧ (3 ≤ m → (∀ y : Over.mk s ⟶ P.A, y ^ m ^ 2 = 1 → ∃ i, x i = y) → ∀ z z' (v : Ix → K), (IsCoordPt P m x z fun i => fnOf (v i)) → (IsCoordPt P m x z' fun i => fnOf (v i)) → z = z' ∧ v ≠ 0) := by
  first | exact @GlobalTheory.CoordSep.coord_exists_unique_separate | exact GlobalTheory.CoordSep.coord_exists_unique_separate | (intros; apply GlobalTheory.CoordSep.coord_exists_unique_separate <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.TorusExtensionPointsDivisibleStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.torusExtension_points_divisible' : ∀ (k : Type) [Field k] [IsAlgClosed k] (G : Over (Sp k)) [GrpObj G] [IsCommMonObj G], Nonempty (TorusExtension G) → ∀ (n : ℕ), 1 ≤ n → ∀ y : (𝟙_ (Over (Sp k)) ⟶ G), ∃ x : (𝟙_ (Over (Sp k)) ⟶ G), x ^ n = y := by
  first | exact @GlobalTheory.SS.torusExtension_points_divisible | exact GlobalTheory.SS.torusExtension_points_divisible | (intros; apply GlobalTheory.SS.torusExtension_points_divisible <;> assumption)
end

