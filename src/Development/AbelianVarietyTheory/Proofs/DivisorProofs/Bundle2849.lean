import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0081
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0072
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.MemNonzeroLocusIffPowFn
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TotalEqCurve
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdjacentPullPull
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0005
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2773
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2631
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2753
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2427
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RefinesPolarisedDataBaseChangeSymmetric
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0100
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2757
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0077
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0025
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2566
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2651
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2764
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1592
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1624
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NontrivialIsomClassInt
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0061
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0082
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2363
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ThetaEmbeddingSectionsBaseChangeAffine
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0029
import Development.AbelianVarietyTheory.Statements.TorsionEndomorphisms.EndDeterminedOnTorsion
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0007
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2758
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LabRange
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2759
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2668

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullbackTwistedSectionIso
section
open CategoryTheory Limits AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Out
open GlobalTheory GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Vert GlobalTheory.Twist

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CutPull

variable {X Y : Scheme.{0}} (f : Y ⟶ X) {L : LB X}

theorem homEquiv_pullbackZIso_hom (hL : L.IsLB) (G : X.Modules) (n : ℤ) :
    (Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv _ _ (pullbackZIso G f hL n).hom =
      Twist.map (lbZPow L n) ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app G) ≫
        (projZIso f hL ((Scheme.Modules.pullback f).obj G) n).inv := by
  have e : (Scheme.Modules.pullbackPushforwardAdjunction f).unit.app (twist G (lbZPow L n)) ≫
      (Scheme.Modules.pushforward f).map (pullbackHom G (lbZPow L n) f) =
        Twist.map (lbZPow L n) ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app G) ≫
          (projIso (lbZPow L n) f _).inv :=
    ((Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv_unit _ _ _).symm.trans
      (Equiv.apply_symm_apply _ _)
  rw [Adjunction.homEquiv_unit, pullbackZIso, Iso.trans_hom, Functor.map_comp, ← Category.assoc,
    pullbackIso_hom, e, projZIso, Iso.trans_inv, Functor.mapIso_inv, Iso.symm_hom, Category.assoc]

theorem pullback_mulSecOfEq (hL : L.IsLB) (G : X.Modules) {n m k : ℤ} (σ : LB.Sec (lbZPow L m))
    (h : n + m = k) :
    (Scheme.Modules.pullback f).map (mulSecOfEq G σ h) ≫ (pullbackZIso G f hL k).hom =
      (pullbackZIso G f hL n).hom ≫ mulSecOfEq ((Scheme.Modules.pullback f).obj G) (zpull f σ) h := by
  apply ((Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv _ _).injective
  rw [Adjunction.homEquiv_naturality_left, Adjunction.homEquiv_naturality_right,
    homEquiv_pullbackZIso_hom, homEquiv_pullbackZIso_hom, Category.assoc]
  have e := projZIso_mulSecOfEq f hL ((Scheme.Modules.pullback f).obj G) σ h
  have e' : (projZIso f hL ((Scheme.Modules.pullback f).obj G) n).inv ≫
      (Scheme.Modules.pushforward f).map (mulSecOfEq ((Scheme.Modules.pullback f).obj G) (zpull f σ) h) =
        mulSecOfEq ((Scheme.Modules.pushforward f).obj ((Scheme.Modules.pullback f).obj G)) σ h ≫
          (projZIso f hL ((Scheme.Modules.pullback f).obj G) k).inv := by
    rw [Iso.inv_comp_eq, ← Category.assoc, Iso.eq_comp_inv]
    exact e
  rw [e', ← Category.assoc, ← Category.assoc]
  congr 1
  exact (mulSecOfEq_naturality σ h _).symm

end GlobalTheory.CutPull

namespace GlobalTheory

open GlobalTheory.CutPull in

theorem cut_pullback_iso : ∀ {X Y : Scheme.{0}} (f : Y ⟶ X) (G : X.Modules) [G.IsQuasicoherent] {L : LB X} (hL : L.IsLB) (s : L.Sec) (hL' : (L.pull f).IsLB), Nonempty ((Scheme.Modules.pullback f).obj (cut G hL s) ≅ cut ((Scheme.Modules.pullback f).obj G) hL' (secPull s f)) := by
  intro X Y f G _ L hL s hL'
  have : PreservesColimits (Scheme.Modules.pullback f) :=
    (Scheme.Modules.pullbackPushforwardAdjunction f).leftAdjoint_preservesColimits
  have hz : ∀ j, zfun (zpull f (zofSec s)) j = zfun (zofSec (secPull s f)) j := fun j => by
    rw [zfun_zpull, zfun_zofSec, zfun_zofSec]
    rfl
  have hM : mulSecOfEq ((Scheme.Modules.pullback f).obj G) (zpull f (zofSec s)) (neg_add_cancel (1 : ℤ)) =
      mulSecOfEq ((Scheme.Modules.pullback f).obj G) (zofSec (secPull s f)) (neg_add_cancel (1 : ℤ)) :=
    zhom_ext fun V t j => by rw [zcoord_mulSecOfEq_app, zcoord_mulSecOfEq_app, hz]
  have e := pullback_mulSecOfEq f hL G (zofSec s) (neg_add_cancel (1 : ℤ))
  rw [hM, ← Iso.eq_comp_inv] at e
  have key : (Scheme.Modules.pullback f).map (cutHom G hL s) =
      (pullbackZIso G f hL (-1)).hom ≫
        (mulSecOfEq ((Scheme.Modules.pullback f).obj G) (zofSec (secPull s f)) (neg_add_cancel (1 : ℤ)) ≫
          ((pullbackZIso G f hL 0).symm ≪≫ (Scheme.Modules.pullback f).mapIso (twistZZeroIso G hL).symm).hom) := by
    rw [cutHom, Functor.map_comp, e]
    simp
  exact ⟨PreservesCokernel.iso (Scheme.Modules.pullback f) (cutHom G hL s) ≪≫ cokernelIsoOfEq key ≪≫
    cokernelEpiComp _ _ ≪≫ cokernelCompIsIso _ _ ≪≫
    (cokernelCompIsIso _ (twistZZeroIso ((Scheme.Modules.pullback f).obj G) hL').inv).symm⟩

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullbackUnipotentFrameIsFrame
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Points GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.HermFrame GlobalTheory.ArInt GlobalTheory.MixDens GlobalTheory.CovTest
open GlobalTheory.FlagFibre (Low uni dens)
open ReciprocityTheory.L2DbarEstimates (V cHess)
open scoped ContDiff ComplexOrder Classical
open GlobalTheory.FlagCell GlobalTheory.FlagConnect

open GlobalTheory.Twist (resM resM_resM resM_self resM_smul)
open GlobalTheory.LB (resG_resG resG_self)

namespace GlobalTheory.UniColFrame

theorem det_uniR {R : Type*} [CommRing R] {m : ℕ} (n : Low m → R) : (uniR n).det = 1 := by
  rw [Matrix.det_of_lowerTriangular (uniR n)]
  · exact Finset.prod_eq_one fun a _ => by simp [uniR_apply]
  · intro a b h
    have h' : a < b := h
    simp [uniR_apply, h'.not_gt, h'.ne]

theorem isFrame_cols {X : Scheme.{0}} {F : X.Modules} {V : X.Opens} {m : ℕ} {e : Fin m → Γ(F, V)}
    (he : IsFrame e) (M : Matrix (Fin m) (Fin m) Γ(X, V)) (hM : IsUnit M.det) :
    IsFrame fun j => ∑ l, M l j • e l := fun W h => by
  have hM' : IsUnit (M.map (resG X h)).det := by
    have := hM.map (resG X h)
    rwa [RingHom.map_det] at this
  have hb : Function.Bijective (M.map (resG X h)).mulVec :=
    ⟨Matrix.mulVec_injective_of_isUnit ((Matrix.isUnit_iff_isUnit_det _).2 hM'),
      Matrix.mulVec_surjective_iff_isUnit.2 ((Matrix.isUnit_iff_isUnit_det _).2 hM')⟩
  have key : ⇑(Fintype.linearCombination Γ(X, W) fun j => resM F h (∑ l, M l j • e l)) =
      ⇑(Fintype.linearCombination Γ(X, W) fun i => resM F h (e i)) ∘ (M.map (resG X h)).mulVec := by
    funext a
    simp only [Function.comp_apply, Fintype.linearCombination_apply, map_sum, resM_smul,
      Finset.smul_sum, Matrix.mulVec, dotProduct, Finset.sum_smul, Matrix.map_apply, smul_smul]
    rw [Finset.sum_comm]
    simp only [mul_comm]
  rw [key]
  exact (he W h).comp hb

theorem isFrame_pullCol_uniR : ∀ (X B : Scheme.{0}) (g : X ⟶ B) (E : B.Modules) (m : ℕ), IsVB E m → ∀ (U : B.Opens) (e : Fin m → Γ(E, U)), IsFrame e → ∀ (V : X.Opens) (hV : V ≤ g ⁻¹ᵁ U) (n : Low m → Γ(X, V)), IsFrame (pullCol g e hV (uniR n)) := by
  intro X B g E m hE U e he V hV n
  have := hE.isQuasicoherent
  have h1 : IsFrame fun i => QCoh.pullbackSections g E hV (e i) := by
    have h2 := (he.pullback g).res hV
    have h3 : (fun i => resM _ hV (QCoh.pullbackSections g E (le_refl (g ⁻¹ᵁ U)) (e i))) =
        fun i => QCoh.pullbackSections g E hV (e i) :=
      funext fun i => QCoh.res_pullbackSections g E _ _ _
    rwa [h3] at h2
  exact isFrame_cols h1 (uniR n) (by rw [det_uniR]; exact isUnit_one)

end GlobalTheory.UniColFrame
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PulledBackPeriodConstantsMultiplicative
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.SiegJoin GlobalTheory.TChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

open GlobalTheory.LamRigid GlobalTheory.LamBiext

noncomputable section

namespace GlobalTheory.TChart.PeriodAdd

theorem exists_ratio {X Y S₀ : Scheme.{0}} {M : LB X} (hM : M.IsLB) {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ}
    (p : Y ⟶ S₀) (hp : Function.Surjective p.appTop.hom)
    {u u' : LB.Gen (LB.LinComb M φ ε)} (hu : u.IsGen) (hu' : u'.IsGen) :
    ∃ a : Γ(S₀, ⊤), ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (J), Good M z J →
      (val u r z J * (val u' r z J)⁻¹).val = gs (r ≫ p) z ⊤ a := by
  obtain ⟨t, -, hv⟩ := exists_gen hM (K' := PEmpty) (φ' := PEmpty.elim) (ε' := PEmpty.elim) (fun U _ h => by
      refine (Fintype.prod_sum_type _).trans (Eq.trans ?_ (Fintype.prod_empty _).symm)
      simp only [Sum.elim_inl, Sum.elim_inr, zpow_neg, Finset.prod_inv_distrib, mul_inv_cancel])
    (LB.mulGen M _ _ _ _ u (LB.invGen M _ _ u')) (DVR.mulGen_isGen _ _ _ _ _ _ _ hu (DVR.invGen_isGen _ _ _ _ hu'))
  have le : (⊤ : Y.Opens) ≤ LB.wchart M (PEmpty.elim : PEmpty → (Y ⟶ X)) PEmpty.elim := fun _ _ =>
    Set.mem_iInter.2 fun k => k.elim
  obtain ⟨a, ha⟩ := hp (res le (t.s PEmpty.elim)).val
  refine ⟨a, fun Z r z J hJ => ?_⟩
  rw [← val_inv, ← val_mul hJ, ← hv Z r z J hJ, val_of t r z J PEmpty.elim (fun k => k.elim)]
  exact (congrArg Units.val (gm_res r z le trivial _)).symm.trans ((gs_unit r z ⊤ trivial _).symm.trans
    ((congrArg (gs r z ⊤) ha.symm).trans (gs_pull r p z ⊤ trivial a)))

theorem exists_pull {X X' Y : Scheme.{0}} {L : LB X} (F : X' ⟶ X) {K : Type} [Fintype K] (φ' : K → (Y ⟶ X')) (ε : K → ℤ)
    {a : LB.Gen (LB.LinComb L (fun k => φ' k ≫ F) ε)} (ha : a.IsGen) :
    ∃ a' : LB.Gen (LB.LinComb (L.pull F) φ' ε), a'.IsGen ∧ ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z)
      (j : K → PUnit → L.ι), r z ∈ LB.wchart (L.pull F) φ' j →
      gm r z (LB.wchart (L.pull F) φ' j) (a'.s j) =
        gm r z (LB.wchart L (fun k => φ' k ≫ F) (fun k => j k PUnit.unit)) (a.s fun k => j k PUnit.unit) := by
  have le : ∀ j : K → PUnit → L.ι, LB.wchart (L.pull F) φ' j ≤
      LB.wchart L (fun k => φ' k ≫ F) (fun k => j k PUnit.unit) := fun j y hy =>
    Set.mem_iInter.2 fun k => (mem_pull (F := F) (x := φ' k y)).1 (Set.mem_iInter.1 hy k)
  refine ⟨⟨fun j => res (le j) (a.s fun k => j k PUnit.unit)⟩, isGen_of_gm _ fun y j j' hj hj' => ?_,
    fun Z r z j hj => gm_res r z (le j) hj _⟩
  refine (gm_res _ y (le j) hj _).trans ((gen_trans ha (𝟙 Y) y (le j hj) (le j' hj')).trans
    (congrArg₂ (· * ·) ?_ (gm_res _ y (le j') hj' _).symm))
  refine Finset.prod_congr rfl fun k _ => congrArg (· ^ ε k) (Eq.symm ?_)
  refine (gm_pull_g L F (𝟙 Y ≫ φ' k) y (j k) (j' k) (Set.mem_iInter.1 hj k) (Set.mem_iInter.1 hj' k)).trans ?_
  rw [Category.assoc]

theorem rigid_two {X X₁ X' Y S₀ : Scheme.{0}} {L : LB X} {L₁ : LB X₁} {F : X' ⟶ X} {F₁ : X' ⟶ X₁}
    (w : LB.Iso (L.pull F) (L₁.pull F₁)) (hw : w.IsGen) (hL : L.IsLB) (hL₁ : L₁.IsLB) {K : Type} [Fintype K]
    (φ' : K → (Y ⟶ X')) (ε : K → ℤ)
    {a : LB.Gen (LB.LinComb L (fun k => φ' k ≫ F) ε)} (ha : a.IsGen)
    {t : LB.Gen (LB.LinComb L₁ (fun k => φ' k ≫ F₁) ε)} (ht : t.IsGen)
    (p : Y ⟶ S₀) (hp : Function.Surjective p.appTop.hom) :
    ∃ c : Γ(S₀, ⊤), ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (J : (Z ⟶ X₁) → L₁.ι) (J' : (Z ⟶ X) → L.ι), Good L₁ z J →
      Good L z J' → (val t r z J * ((∏ k, gw w (r ≫ φ' k) z (J (r ≫ φ' k ≫ F₁)) (fun _ => J' (r ≫ φ' k ≫ F)) ^ ε k) *
        val a r z J')⁻¹).val = gs (r ≫ p) z ⊤ c := by
  obtain ⟨a', ha', hv'⟩ := exists_pull F φ' ε ha
  have hP : (L.pull F).IsLB := DVR.linComb_isLB _ hL _ _
  obtain ⟨t₁, ht₁, hv⟩ := exists_up ((isGen_iff w).1 hw) hL₁ hP a' ha'
  obtain ⟨c, hc⟩ := exists_ratio hL₁ p hp ht ht₁
  refine ⟨c, fun Z r z J J' hJ hJ' => Eq.trans ?_ (hc Z r z J hJ)⟩
  have m : r z ∈ LB.wchart (L.pull F) φ' (fun k _ => J' (r ≫ φ' k ≫ F)) :=
    Set.mem_iInter.2 fun k => mem_pull.2 (hJ' (r ≫ φ' k ≫ F))
  have e := (hv Z r z _ _ (hJ.mem _ r) m).trans (congrArg (_ * ·) (hv' Z r z _ m))
  exact congrArg (fun q => (val t r z J * q⁻¹).val) e.symm

theorem exists_law {S S' : Scheme.{0}} {B : Over S} {B' : Over S'} [GrpObj B] [IsCommMonObj B] [GrpObj B']
    [IsCommMonObj B'] (M : RigLB B) (c : CubicalStr B M) {f : S' ⟶ S} {β : B'.left ⟶ B.left}
    {β₂ : (G2 B').left ⟶ (G2 B).left} (hβ : IsGrpPullback B' B f β) (hsq : IsSquare β β₂) :
    ∃ t : LB.Gen (LB.LinComb (abelian₂ B M.L) (fun k => law1φ B' (x3 B' 0) (x3 B' 1) (x3 B' 2) k ≫ β₂) lawε), t.IsGen ∧
      ∀ {T₀ : Over S'} (a a' b : T₀ ⟶ B') (z₀ : T₀.left) (J₀ : (T₀.left ⟶ B.left) → M.L.ι), Good M.L z₀ J₀ →
        val (L := abelian₂ B M.L) t (lift a (lift a' b)).left z₀ (ind B J₀) =
          cubV (T := Over.mk (T₀.hom ≫ f)) c z₀ J₀ (toBase hβ.1.w a) (toBase hβ.1.w a') (toBase hβ.1.w b) := by
  have hw₀ : β ≫ B.hom = B'.hom ≫ f := hβ.1.w
  have pt_mul : ∀ {T₀ : Over S'} (a b : T₀ ⟶ B'), toBase hw₀ (a * b) = toBase hw₀ a * toBase hw₀ b :=
    fun a b => Over.OverMorphism.ext (hβ.2 _ a b _ _ rfl rfl).symm
  have β₂_lift : ∀ {T₀ : Over S'} (a b : T₀ ⟶ B'),
      (lift a b).left ≫ β₂ = (lift (toBase hw₀ a) (toBase hw₀ b)).left := fun a b => square_over_hom_ext
    (by rw [Category.assoc, hsq.1, ← Category.assoc, ← Over.comp_left, ← Over.comp_left, lift_fst, lift_fst]; rfl)
    (by rw [Category.assoc, hsq.2, ← Category.assoc, ← Over.comp_left, ← Over.comp_left, lift_snd, lift_snd]; rfl)
  have Hlam : ∀ {T₀ : Over S'} (a b : T₀ ⟶ B') {U : Type} [CommGroup U] (h : (T₀.left ⟶ B.left) → U),
      ∏ i, h (((lift a b).left ≫ β₂) ≫ lamφ B i) ^ lamε i =
        h (toBase hw₀ a * toBase hw₀ b).left * (h (toBase hw₀ a).left)⁻¹ * (h (toBase hw₀ b).left)⁻¹ *
          h (1 : Over.mk (T₀.hom ≫ f) ⟶ B).left := fun a b U _ h => by
    rw [β₂_lift]; exact prod_lam (toBase hw₀ a) (toBase hw₀ b) h
  let φ3 := law1φ B' (x3 B' 0) (x3 B' 1) (x3 B' 2)
  let β₃ : (G3 B').left ⟶ (G3 B).left :=
    (lift (toBase hw₀ (x3 B' 0)) (lift (toBase hw₀ (x3 B' 1)) (toBase hw₀ (x3 B' 2)))).left
  have fe3 : FormEq (fun I => β₃ ≫ thφ B (x3 B) I) thε (flatφ (lamφ B) (fun k => φ3 k ≫ β₂)) (flatε lamε lawε) :=
    fun U _ h => by
      have a := prod_cub (toBase hw₀ (x3 B' 0)) (toBase hw₀ (x3 B' 1)) (toBase hw₀ (x3 B' 2)) h
      have b := prod_law₁ (x3 B' 0) (x3 B' 1) (x3 B' 2) (fun χ => ∏ i, h ((χ ≫ β₂) ≫ lamφ B i) ^ lamε i)
      rw [id₃] at b
      simp only [Over.id_left, Category.id_comp, Hlam, pt_mul] at b
      rw [a, prod_flat, b]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv]
      abel
  obtain ⟨g₃, hg₃, hv₃⟩ := exists_gen M.isLB fe3 (LB.pullGen M.L (thφ B (x3 B)) thε c.t β₃)
    (DVR.pullGen_isGen _ _ _ _ c.isGen β₃)
  refine ⟨_, nest_isGen (L := M.L) (φ := lamφ B) (δ := lamε) hg₃, ?_⟩
  intro T₀ a a' b z₀ J₀ hJ₀
  show val (L := LB.LinComb M.L (lamφ B) lamε) (nest M.L (lamφ B) lamε (fun k => φ3 k ≫ β₂) lawε g₃) _ z₀ (ind B J₀) = _
  rw [val_nest hg₃ _ (good_ind hJ₀) hJ₀]
  simp only [adj_ind M.isLB hJ₀, one_zpow, Finset.prod_const_one, _root_.one_mul]
  rw [hv₃ _ _ z₀ J₀ hJ₀]
  refine (val_pull hJ₀ _ _ _).trans ?_
  refine congrArg (fun q => val (L := M.L) (φ := thφ B (x3 B)) (ε := thε) c.t q z₀ J₀) ?_
  refine hom_ext_triple B fun i => ?_
  have e1 : β₃ ≫ (x3 B i).left = (x3 B' i).left ≫ β := by
    show (lift _ (lift _ _) ≫ x3 B i).left = _
    rw [cartesian_lift_three_comp_projection]; fin_cases i <;> rfl
  rw [Category.assoc, e1, ← Category.assoc, ← Over.comp_left, cartesian_lift_three_comp_projection, ← Over.comp_left, cartesian_lift_three_comp_projection]
  fin_cases i <;> rfl

theorem isoVal_law {S S₁ S' : Scheme.{0}} {B : Over S} {B₁ : Over S₁} {B' : Over S'} [GrpObj B] [IsCommMonObj B]
    [GrpObj B₁] [IsCommMonObj B₁] [GrpObj B'] (M : RigLB B) (c : CubicalStr B M) (M₁ : RigLB B₁)
    (c₁ : CubicalStr B₁ M₁) {f : S' ⟶ S} {β : B'.left ⟶ B.left} {β₂ : (G2 B').left ⟶ (G2 B).left}
    (hβ : IsGrpPullback B' B f β) (hsq : IsSquare β β₂) {f₁ : S' ⟶ S₁} {β' : B'.left ⟶ B₁.left}
    {β₂' : (G2 B').left ⟶ (G2 B₁).left} (hβ' : IsGrpPullback B' B₁ f₁ β') (hsq' : IsSquare β' β₂')
    (hB : IsAbelianScheme B') (w : LB.Iso ((abelian₂ B M.L).pull β₂) ((abelian₂ B₁ M₁.L).pull β₂')) (hw : w.IsGen)
    {T : Over S'} (x x' y : T ⟶ B') (z : T.left) (J : (T.left ⟶ B₁.left) → M₁.L.ι) (J' : (T.left ⟶ B.left) → M.L.ι)
    (hJ : Good M₁.L z J) (hJ' : Good M.L z J') :
    @id (T.left.presheaf.stalk z)ˣ (cubV (T := Over.mk (T.hom ≫ f₁)) c₁ z J (toBase hβ'.1.w x) (toBase hβ'.1.w x')
        (toBase hβ'.1.w y)) * isoVal w (lift x y).left z J J' * isoVal w (lift x' y).left z J J' =
      isoVal w (lift (1 : T ⟶ B') (1 : T ⟶ B')).left z J J' * isoVal w (lift (x * x') y).left z J J' *
        @id (T.left.presheaf.stalk z)ˣ (cubV (T := Over.mk (T.hom ≫ f)) c z J' (toBase hβ.1.w x) (toBase hβ.1.w x')
          (toBase hβ.1.w y)) := by
  haveI := hB.comm
  have hG := GlobalTheory.globalFns_holds
  obtain ⟨a, ha, va⟩ := exists_law M c hβ hsq
  obtain ⟨t, ht, vt⟩ := exists_law M₁ c₁ hβ' hsq'
  have sj3 : Function.Surjective ((snd B' (B' ⊗ B')).left ≫ (snd B' B').left ≫ B'.hom).appTop.hom :=
    surj_comp (surj_snd hG hB _) (surj_comp (surj_snd hG hB _) (hG _ _ hB).2)
  obtain ⟨u, hu⟩ := rigid_two w hw (DVR.linComb_isLB _ M.isLB _ _) (DVR.linComb_isLB _ M₁.isLB _ _) _ lawε ha ht _ sj3
  have key : ∀ x x' y : T ⟶ B',
      (@id (T.left.presheaf.stalk z)ˣ (cubV (T := Over.mk (T.hom ≫ f₁)) c₁ z J (toBase hβ'.1.w x) (toBase hβ'.1.w x')
        (toBase hβ'.1.w y)) * (isoVal w (lift (x * x') y).left z J J' * (isoVal w (lift x y).left z J J')⁻¹ *
        (isoVal w (lift x' y).left z J J')⁻¹ *
        @id (T.left.presheaf.stalk z)ˣ (cubV (T := Over.mk (T.hom ≫ f)) c z J' (toBase hβ.1.w x) (toBase hβ.1.w x')
          (toBase hβ.1.w y)))⁻¹).val = gs T.hom z ⊤ u := by
    intro x x' y
    have e := hu T.left (lift x (lift x' y)).left z (ind B₁ J) (ind B J') (good_ind hJ) (good_ind hJ')
    have e₀ : (lift x (lift x' y)).left ≫ (snd B' (B' ⊗ B')).left ≫ (snd B' B').left ≫ B'.hom = T.hom := by
      rw [Over.w, Over.w]; exact Over.w (lift x (lift x' y))
    rw [e₀, va x x' y z J' hJ', vt x x' y z J hJ] at e
    refine Eq.trans ?_ e
    refine congrArg Units.val (congrArg₂ (· * ·) rfl (congrArg (·⁻¹) (congrArg₂ (· * ·) ?_ rfl)))
    refine (prod_law₁ x x' y (fun χ => isoVal w χ z J J')).symm.trans (Finset.prod_congr rfl fun k _ => ?_)
    refine congrArg (· ^ lawε k) ?_
    refine congrArg₂ (fun (j : ULift.{0} (Finset (Fin 2)) → M₁.L.ι) (j' : ULift.{0} (Finset (Fin 2)) → M.L.ι) =>
      gw w ((lift x (lift x' y)).left ≫ law1φ B' (x3 B' 0) (x3 B' 1) (x3 B' 2) k) z j (fun _ => j'))
      (funext fun I => congrArg J ?_) (funext fun I => congrArg J' ?_) <;> simp only [Category.assoc]
  have o : toBase hβ.1.w (1 : T ⟶ B') = 1 := map_one (pushHom hβ T)
  have o' : toBase hβ'.1.w (1 : T ⟶ B') = 1 := map_one (pushHom hβ' T)
  have k₁ := key 1 1 1
  rw [o, o', (isCub_cubV c (T := Over.mk (T.hom ≫ f)) hJ').face, (isCub_cubV c₁ (T := Over.mk (T.hom ≫ f₁)) hJ).face,
    _root_.mul_one (1 : T ⟶ B')] at k₁
  have k₂ := Units.ext ((key x x' y).trans k₁.symm)
  simp only [id] at k₂ ⊢
  apply Additive.ofMul.injective
  have k₃ := congrArg Additive.ofMul k₂
  simp only [ofMul_mul, ofMul_inv, ofMul_one] at k₃ ⊢
  linear_combination (norm := abel) k₃

theorem val_τ₀_add {o W : Type} [CommRing o] [CommRing W] [IsLocalRing W] (T : TautBase o W) (Z : Over (Sp W))
    {z : Z.left} {J : (Z.left ⟶ T.B.left) → T.M.L.ι} (hJ : Good T.M.L z J) (a a' b : Fin T.r → ℤ) :
    val (T.τ₀ (a + a') b) (toUnit Z).left z J *
        cubV T.cub z J (toUnit Z ≫ T.c₀ a) (toUnit Z ≫ T.c₀ a') (toUnit Z ≫ T.c₀ b) =
      val (T.τ₀ a b) (toUnit Z).left z J * val (T.τ₀ a' b) (toUnit Z).left z J := by
  have C := corr_of_val T.M.isLB (t := LB.mulGen T.M.L _ _ _ _ (T.τ₀ (a + a') b)
      (LB.pullGen T.M.L (thφ T.B (x3 T.B)) thε T.cub.t (lift (T.c₀ a) (lift (T.c₀ a') (T.c₀ b))).left))
    (t' := LB.mulGen T.M.L _ _ _ _ (T.τ₀ a b) (T.τ₀ a' b)) fun y J hJ => by
      refine (val_mul hJ _ _ _).trans (Eq.trans ?_ (val_mul hJ _ _ _).symm)
      refine Eq.trans (congrArg₂ (· * ·) rfl ?_) (T.τ₀_add a a' b y J hJ)
      refine (val_pull hJ _ _ _).trans ?_
      rw [Category.id_comp]; rfl
  have := (val_mul hJ _ _ _).symm.trans ((val_corr hJ C (toUnit Z).left).trans (val_mul hJ _ _ _))
  exact Eq.trans (congrArg₂ (· * ·) rfl (val_cub T.cub (toUnit Z) hJ _ _ _).symm) this

theorem period_add : ∀ (n : ℕ) (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (D : DegData V (maximalIdeal V)) (r : ℕ) (e₀ : (Fin r → ℤ) ≃+ D.toPre.X) (L : LowBase (zetaAway n) n) (V₁ : Type) [CommRing V₁] [IsDomain V₁] [IsLocalRing V₁] (f₁ : V →+* V₁) (κ₁ : L.W →+* V₁) (e : (Fin L.T.r → ℤ) ≃+ (Fin r → ℤ)) (B' : Over (Sp V₁)) [GrpObj B'] (β' : B'.left ⟶ D.toPre.P.A.left) (β'' : B'.left ⟶ L.T.B.left) (β₂ : (G2 B').left ⟶ (G2 D.toPre.P.A).left) (β₂' : (G2 B').left ⟶ (G2 L.T.B).left), IsCN V → IsDiscreteValuationRing V → IsCN V₁ → IsDiscreteValuationRing V₁ → Function.Injective f₁ → f₁.Finite → IsLocalHom f₁ → IsLocalHom κ₁ → IsGrpPullback B' D.toPre.P.A (spMap f₁) β' → IsGrpPullback B' L.T.B (spMap κ₁) β'' → IsSquare β' β₂ → IsSquare β'' β₂' → ∀ (x : (Fin L.T.r → ℤ) → (𝟙_ (Over (Sp V₁)) ⟶ B')), (∀ a, (x a).left ≫ β' = spMap f₁ ≫ (D.toPre.c (e₀ (e a))).left ∧ (x a).left ≫ β'' = spMap κ₁ ≫ (L.T.c₀ ((n : ℤ) • a)).left) → ∀ (w₁ : LB.Iso ((abelian₂ D.toPre.P.A D.toPre.P.L).pull β₂) ((abelian₂ L.T.B L.T.M.L).pull β₂')) (q : (Fin L.T.r → ℤ) → (Fin L.T.r → ℤ) → (FractionRing V₁)ˣ), w₁.IsGen → PeriodRel D.toPre L.T f₁ κ₁ w₁ (e.trans e₀) x n q → IsNormIso w₁ → ∀ a a' b, q (a + a') b = q a b * q a' b := by
  intro n V _ _ _ D r e₀ L V₁ _ _ _ f₁ κ₁ e B' _ β' β'' β₂ β₂' _ _ _ _ hf _ _ _ hβ' hβ'' sq' sq'' x hx w₁ q hw hP hN a a' b
  have hB : IsAbelianScheme B' := GlobalTheory.PolPull.isAbelianScheme_of_isGrpPullback L.T.isAb hβ''
  obtain ⟨κK, hκ, -⟩ := GlobalTheory.HalfBC.exists_kappa f₁ (RingHom.id V₁) (RingHom.id _) (fun _ => rfl) hf
  let z : (TK V₁).left := IsLocalRing.closedPoint (FractionRing V₁)
  obtain ⟨J, hJ⟩ := GlobalTheory.UU.exists_good_pt L.T.M.isLB z
  obtain ⟨J', hJ'⟩ := GlobalTheory.UU.exists_good_pt D.toPre.P.isLB z
  let p : (Fin L.T.r → ℤ) → (TK V₁ ⟶ B') := fun a => toUnit (TK V₁) ≫ x a
  let T' : Over (Sp V) := Over.mk ((TK V₁).hom ≫ spMap f₁)
  let T'' : Over (Sp L.W) := Over.mk ((TK V₁).hom ≫ spMap κ₁)
  have pD : ∀ a, Out.toBase hβ'.1.w (p a) = DVR.cP D.toPre T' ((e.trans e₀) a) := fun a => Over.OverMorphism.ext (by
    show ((TK V₁).hom ≫ (x a).left) ≫ β' = ((TK V₁).hom ≫ spMap f₁) ≫ (D.toPre.c (e₀ (e a))).left
    rw [Category.assoc, (hx a).1, Category.assoc])
  have pT : ∀ a, Out.toBase hβ''.1.w (p a) = toUnit T'' ≫ L.T.c₀ ((n : ℤ) • a) := fun a => Over.OverMorphism.ext (by
    show ((TK V₁).hom ≫ (x a).left) ≫ β'' = ((TK V₁).hom ≫ spMap κ₁) ≫ (L.T.c₀ ((n : ℤ) • a)).left
    rw [Category.assoc, (hx a).2, Category.assoc])
  have pa : p (a + a') = p a * p a' := by
    refine Over.OverMorphism.ext (hβ''.1.hom_ext ?_ (by rw [Over.w, Over.w]))
    refine Eq.trans ?_ (hβ''.2 _ (p a) (p a') (Out.toBase hβ''.1.w (p a)) (Out.toBase hβ''.1.w (p a')) rfl rfl)
    rw [pT, pT, ← MonObj.comp_mul, ← L.T.c₀_add, ← smul_add, ← pT]
    rfl
  have law := isoVal_law ⟨D.toPre.P.L, D.toPre.rig, D.toPre.P.isLB, D.toPre.rig_gen⟩ D.toPre.cub L.T.M L.T.cub hβ' sq'
    hβ'' sq'' hB w₁ hw (p a) (p a') (p b) z J J' hJ hJ'
  rw [pD, pD, pD, pT, pT, pT, ← pa] at law
  have h₀ := hN z J J' hJ hJ'
  have hD := GlobalTheory.TauTwist.val_tau_add (T := T') (Over.homMk κK hκ) (z := z) (J := J') hJ' D.tau_bimult
    ((e.trans e₀) a) ((e.trans e₀) a') ((e.trans e₀) b)
  have hT := val_τ₀_add L.T T'' (z := z) (J := J) hJ ((n : ℤ) • a) ((n : ℤ) • a') ((n : ℤ) • b)
  rw [← smul_add] at hT
  rw [← map_add] at hD
  have r₁ := hP κK hκ (a + a') b z J J' hJ hJ'
  have r₂ := hP κK hκ a b z J J' hJ hJ'
  have r₃ := hP κK hκ a' b z J J' hJ hJ'
  refine GlobalTheory.TauTwist.unitAt_injective (F := FractionRing V₁) z ?_
  rw [map_mul]
  have alg : ∀ {U : Type} [CommGroup U] {t₁ t₂ t₃ q₁ q₂ q₃ i₀ i₁ i₂ i₃ s₁ s₂ s₃ c c' : U}, t₁ = q₁ * (i₁ * s₁) →
      t₂ = q₂ * (i₂ * s₂) → t₃ = q₃ * (i₃ * s₃) → t₁ * c = t₂ * t₃ → s₁ * c' = s₂ * s₃ → i₀ = 1 →
      c' * i₂ * i₃ = i₀ * i₁ * c → q₁ = q₂ * q₃ := by
    intro U _ t₁ t₂ t₃ q₁ q₂ q₃ i₀ i₁ i₂ i₃ s₁ s₂ s₃ c c' h₁ h₂ h₃ h₄ h₅ h₆ h₇
    subst h₁ h₂ h₃ h₆
    apply Additive.ofMul.injective
    have k₄ := congrArg Additive.ofMul h₄
    have k₅ := congrArg Additive.ofMul h₅
    have k₇ := congrArg Additive.ofMul h₇
    simp only [ofMul_mul, ofMul_one] at k₄ k₅ k₇ ⊢
    linear_combination (norm := abel) k₄ - k₅ + k₇
  exact alg (U := ((TK V₁).left.presheaf.stalk z)ˣ) r₁ r₂ r₃ hD hT h₀ law

end GlobalTheory.TChart.PeriodAdd
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RankTwoFlagBundleSectionStatement
section
open CategoryTheory AlgebraicGeometry Limits ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.CovTest GlobalTheory.Published
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rank_two_flag_bundle_section : ∀ (k : Type) [CommRing k] (B Y : Scheme.{0}) [IsIntegral B] [IsIntegral Y] (q : B ⟶ Sp k)
    (p : Y ⟶ Sp k) (d : ℕ), IsArithVar q d → IsArithVar p (d + 1) → ∀ (π : Y ⟶ B) (_ : π ≫ q = p) (E : B.Modules),
    GlobalTheory.VB.IsVB E 2 → ∀ (fl : Vert.Flag ((Scheme.Modules.pullback π).obj E) 2),
    IsFlagBundle π (fun _ : Unit => E) (fun _ => 2) (fun _ => fl) →
    ∃ (Z : Scheme.{0}) (_ : IsIntegral Z) (i : Z ⟶ Y), IsArithVar (i ≫ p) d ∧
      (i ≫ π) (genericPoint Z) = genericPoint B ∧ (i ≫ π).residueDegree (genericPoint Z) ≠ 0 := by
  first | exact @GlobalTheory.CovTest.Multisection.exists_multisection | exact GlobalTheory.CovTest.Multisection.exists_multisection | (intros; apply GlobalTheory.CovTest.Multisection.exists_multisection <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RankTwoGradedDeterminantIsometric
section
open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open GlobalTheory.Cartier GlobalTheory.CovTest.SwapLine
open scoped Classical
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.VMetric

theorem isometric_grLB_tens_grLB_det : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k) (E : X.Modules)
    (h : VMetric p E 2) (H : h.IsCInf) (fl : Vert.Flag E 2),
    ((VMetric.grLB fl 0 H).tens (VMetric.grLB fl 1 H)).Isometric (VMetric.det H) := by
  intro k _ X p E h H fl
  have H₀ : (h.stepMet fl 0).IsCInf := H.restrict _ _
  have H₁ : (h.stepMet fl 1).IsCInf := H.restrict _ _
  have hS₀ := VMetric.stepSeq_shortExact fl 0
  have hS₁ := VMetric.stepSeq_shortExact fl 1

  have i₂ : IsIso (VMetric.stepSeq fl 0).g :=
    hS₀.isIso_g_iff.2 (VB.isVB_zero_iff.1 (fl.isVB (Fin.castSucc 0)))
  have e₂ : (VMetric.det H₀).Isometric (VMetric.grLB fl 0 H) :=
    CurveDens.det_isometric_of_isIsometry k X p _ _ 1 (h.stepMet fl 0) (h.grMet fl 0) H₀
      (H.grMet fl 0) (asIso (VMetric.stepSeq fl 0).g) ((VMetric.isIsometry_iff _).2 (VMetric.ext
        (funext fun σ => ChTwoModel.quot_eq_map ((h.stepMet fl 0).met σ) hS₀
          (fl.isVB (Fin.castSucc 0)) _)))

  have hf : VB.IsSubbundle (VMetric.stepSeq fl 1).f := ⟨inferInstance, 1, fl.isVB_gr 1⟩
  have e₁ := VMetric.isometric_det_tens_det k X p (VMetric.stepSeq fl 1) 1 1 (h.stepMet fl 1) H₁ hS₁
    (fl.isVB (Fin.castSucc 1)) (fl.isVB_gr 1) hf

  have e₀ : (VMetric.det (H₁.restrict hf (fl.isVB (Fin.castSucc 1)))).Isometric (VMetric.det H₀) :=
    CurveDens.det_isometric_of_isIsometry k X p _ _ 1 _ (h.stepMet fl 0) _ H₀ (Iso.refl _)
      fun σ V s t y hy => by
        refine ((h.met σ).form_restrict (fl.isSubbundle _) _ s t hy).trans ?_
        refine Eq.trans ?_ ((((h.met σ).restrict (fl.isSubbundle _) (fl.isVB _)).form_restrict hf
          (fl.isVB (Fin.castSucc 1)) s t hy).trans
          ((h.met σ).form_restrict (fl.isSubbundle _) _ _ _ hy)).symm
        congr 1
        · exact congr(($(fl.step_ι 1)).app V s).symm
        · exact congr(($(fl.step_ι 1)).app V t).symm

  have i₁ : IsIso (fl.ι (Fin.succ 1)) := fl.isIso_last
  have e₃ : (VMetric.det H₁).Isometric (VMetric.det H) :=
    CurveDens.det_isometric_of_isIsometry k X p _ _ 2 (h.stepMet fl 1) h H₁ H
      (asIso (fl.ι (Fin.succ 1))) fun σ V s t y hy =>
        ((h.met σ).form_restrict (fl.isSubbundle _) _ s t hy).symm
  exact ((((e₀.trans e₂).symm).tens_right _).trans e₁).trans e₃

end GlobalTheory.VMetric
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RealisedThetaSystemSectionGeneratesFieldFibres
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
namespace GlobalTheory.UMin

theorem isGenSec_real_pull : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (K : Type) [Field K] (i : S.R →+* K), IsGenSec ρ.P.A ρ.P.L _ (SecAt.pull ρ.P.A ρ.P.L (x := 𝟙 (Sp S.R)) ρ.th₁ i) := by
  intro o Ω _ _ _ _ S ρ K _ i
  haveI : IsAffine (Over.mk (𝟙 (Sp S.R))).left := inferInstanceAs (IsAffine (Sp S.R))
  haveI : IsAffine (Over.mk (spMap i ≫ 𝟙 (Sp S.R))).left := inferInstanceAs (IsAffine (Sp K))
  exact GlobalTheory.EmbPull.isGenSec_pullS ρ.P GlobalTheory.abelianSchemeLaws_all.2.secBaseChangeAny _ (GlobalTheory.ThetaLevel.isGenSec_real ρ)

end GlobalTheory.UMin
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RechartAtUnitaryClassicalTraitStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rechart_at_unitaryClassicalTrait : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H), 1 ≤ Dw.p + Dw.q → ∀ (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (cf : Coeff l) (C : UCompact Xo cf) (X : USetup C) (p : ℕ) [Fact p.Prime] (z : X.M.Z) (ct : UCTrait X p z) (U : X.M.Z.Opens) (u' : Sp (ratHull (X.M.ringOn U)) ⟶ Xo.XF cf), IsAffineOpen U → (gPt p ≫ ct.y) (closedPoint (PadicAlgCl p)) ∈ U → spMap (ratHull (X.M.ringOn U)).val.toRingHom ≫ u' = X.uΩ → X.M.ringOn U ≤ X.M.O ((gPt p ≫ ct.y) (closedPoint (PadicAlgCl p))) ∧ ∃ y₁ : ratHull (X.M.ringOn U) →+* PadicAlgCl p, (∀ a : X.M.ringOn U, y₁ (toRat _ a) = X.M.val (gPt p ≫ ct.y) a) ∧ spMap y₁ ≫ u' = spMap ct.ι ≫ ct.T.y ∧ ∀ a : X.o₁, ‖y₁ (toRat _ (algebraMap X.o₁ (X.M.ringOn U) a))‖ ≤ 1 := by
  first | exact @GlobalTheory.UPoinc.rechart_at_uClassical_trait | exact GlobalTheory.UPoinc.rechart_at_uClassical_trait | (intros; apply GlobalTheory.UPoinc.rechart_at_uClassical_trait <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RegularSectionOpenCoverStatement
section
open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj
open GlobalTheory GlobalTheory.ArInt GlobalTheory.ShFam.Pad GlobalTheory.TrueGeo GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.Mean4O GlobalTheory.LineNorm GlobalTheory.CoverNorm GlobalTheory.VertForm GlobalTheory.HtGen
open Formalism.MainNotions.DIV.Cons (intO)
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.regular_section_open_cover : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (L : HermLB p) (R : L.B.ι → X.functionFieldˣ), IsRatSec L.B R → ∀ (l n : ℕ) (U : X → X.Opens) (s : X → Fin n → X.functionField), (∀ x, x ∈ U x) → (∀ (x : X) (i : L.B.ι) (x₀ : X), x₀ ∈ U x → x₀ ∈ L.B.U i → (l : k) ∈ (p x₀).asIdeal → (∀ J, RegAt x₀ (s x J * R i)) ∧ (∃ J, UnitAt x₀ (s x J * R i)) ∧ ∀ x', x₀ ∈ U x' → ∀ J, ¬ UnitAt x₀ ((s x J - s x' J) * R i)) → NefOver L l := by
  first | exact @GlobalTheory.HtGenCurve.nefOver_of_localGen | exact GlobalTheory.HtGenCurve.nefOver_of_localGen | (intros; apply GlobalTheory.HtGenCurve.nefOver_of_localGen <;> assumption)
end

