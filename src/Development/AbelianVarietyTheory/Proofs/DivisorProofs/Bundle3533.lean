import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3485
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsDominantToUnitLeft
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2496
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0008
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3184
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ValuationThetaRatioEqBilinear
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3504
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GsAppTopOfSection
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2595
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3096
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ProdIso
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0082
import Development.AbelianVarietyTheory.Statements.TorsionEndomorphisms.EndDeterminedOnTorsion
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0007
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2968
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2941
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3157
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2937
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3512
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3139
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2948
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FibreIsoCarriesSharpPointsToConjugates
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3495
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3513
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PartialZetaFunctionalEquation
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsEqOfNatCastMulMem
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HeckeTateFunctionalEquationCM
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0006
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0017
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0090
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3514
import Development.AbelianVarietyTheory.Definitions.Degenerations.CharZeroOfIsPrimitiveRoot
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.GoodClass
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0160
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.HasThetaConstantsIffOfThetaLevelPullback
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ThetaCoordinatesExistUniqueSeparatePoints
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0052
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3515
import Development.AbelianVarietyTheory.Definitions.Divisors.HasRigidCoords
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3488
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0010

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaGeneratorValuesScalarMulLocalUnit
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.UPoinc GlobalTheory.TorRef
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.USep
open GlobalTheory.Poinc.ThetaOne GlobalTheory.Poinc.Sep GlobalTheory.UT GlobalTheory.FieldBaseChange

namespace GlobalTheory.USep.EvG.ThetaVal

open GlobalTheory.USep.EvG

theorem one_left' {S X : Scheme.{0}} (G : Over S) [GrpObj G] (t : X ⟶ S) :
    (1 : Over.mk t ⟶ G).left = t ≫ (η[G]).left := by
  rw [Hom.one_def]; rfl

theorem toUnit_eta_left {S : Scheme.{0}} (G : Over S) [GrpObj G] :
    (toUnit G ≫ η[G]).left = G.hom ≫ (η[G]).left := by
  rfl

@[reassoc]
theorem spMap_two' {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap g ≫ spMap f = spMap (g.comp f) := by
  simp only [spMap, ← Spec.map_comp]; rfl

theorem eta_push {S S' : Scheme.{0}} {G' : Over S'} [GrpObj G'] {G : Over S} [GrpObj G] {f : S' ⟶ S}
    {F : G'.left ⟶ G.left} (hF : IsGrpPullback G' G f F) : (toUnit G' ≫ η[G']).left ≫ F = G'.hom ≫ f ≫ (η[G]).left := by
  obtain ⟨e, he⟩ := GlobalTheory.GroupBplus.Aff.exists_mulEquiv_points_of_isGrpPullback hF G'.hom (G'.hom ≫ f) rfl
  have h1 := he 1
  rw [map_one, one_left', one_left'] at h1
  rw [toUnit_eta_left, ← h1, Category.assoc]

variable {V₁ : Type} [CommRing V₁] [IsDomain V₁]

theorem famφB_one (D : DegPre V₁) : D.famφB 0 1 = 𝟙 _ := by
  have h : padd D.P.A (𝟙 D.P.A) (toUnit D.P.A ≫ D.c 0) = 𝟙 D.P.A := by
    rw [GlobalTheory.Poinc.ThetaOne.c_zero D, MonObj.comp_one]
    exact mul_one (𝟙 D.P.A)
  show (padd D.P.A (𝟙 D.P.A) (toUnit _ ≫ D.c 0)).left = _
  rw [h]; rfl

theorem famφB_two (D : DegPre V₁) : D.famφB 0 2 = D.famφB 0 3 := by
  show (toUnit D.P.A ≫ D.c 0).left = (toUnit D.P.A ≫ η[D.P.A]).left
  rw [GlobalTheory.Poinc.ThetaOne.c_zero D, MonObj.comp_one]
  rfl

def chartPullCompPull {X X' Y : Scheme.{0}} (L : LB X) (F : X' ⟶ X) {K : Type} [Fintype K] (φ : K → (Y ⟶ X'))
    (ε : K → ℤ) : ChartPull (LB.LinComb L (fun k => φ k ≫ F) ε) (LB.LinComb (L.pull F) φ ε) (𝟙 Y) :=
  have le : ∀ j : K → L.ι, LB.wchart L (fun k => φ k ≫ F) j ≤ (𝟙 Y) ⁻¹ᵁ LB.wchart (L.pull F) φ (fun k _ => j k) :=
    fun j y hy => Set.mem_iInter.2 fun k => mem_pull.2 (Set.mem_iInter.1 hy k)
  { idx := fun j k _ => j k
    le := le
    g := fun y j j' hj hj' => by
      refine (gm_linComb L (fun k => φ k ≫ F) ε (𝟙 Y) y j j' hj hj').trans
        (Eq.trans (Finset.prod_congr rfl fun k _ => congrArg (· ^ ε k) ?_)
          (gm_linComb (L.pull F) φ ε (𝟙 Y) y _ _ (le j hj) (le j' hj')).symm)
      refine Eq.trans ?_ (gm_pull_g L F (𝟙 Y ≫ φ k) y (fun _ => j k) (fun _ => j' k)
        (Set.mem_iInter.1 (le j hj) k) (Set.mem_iInter.1 (le j' hj') k)).symm
      simp only [Category.assoc] }

theorem gm_linCombIso_pull' {A A₂ Y₂ : Scheme.{0}} {L : LB A} {L₂ : LB A₂} {φ : A₂ ⟶ A} (w : LB.Iso L₂ (L.pull φ))
    {K : Type} [Fintype K] (φ' : K → (Y₂ ⟶ A₂)) (ε : K → ℤ)
    {Z : Scheme.{0}} (r : Z ⟶ Y₂) (z : Z) (p : K → L.ι) (q : K → L₂.ι)
    (hm : r z ∈ LB.wchart (L.pull φ) φ' (fun k _ => p k) ⊓ LB.wchart L₂ φ' q) :
    gm r z (LB.wchart (L.pull φ) φ' (fun k _ => p k) ⊓ LB.wchart L₂ φ' q)
      ((LB.linCombIso w φ' ε).s (fun k _ => p k, q)) = ∏ k, gw w (r ≫ φ' k) z (p k) (q k) ^ ε k := by
  refine (map_prod _ _ _).trans (Finset.prod_congr rfl fun k _ => (map_zpow _ _ _).trans (congrArg (· ^ ε k) ?_))
  exact (gm_res r z _ hm _).trans (gm_pull r (φ' k) z ((L.pull φ).U (fun _ => p k) ⊓ L₂.U (q k))
    ⟨Set.mem_iInter.1 hm.1 k, Set.mem_iInter.1 hm.2 k⟩ _)

theorem exists_conj_fibre_one {V₁ W₀ : Type} [CommRing V₁] [IsDomain V₁] [CommRing W₀] (D : DegPre V₁) (ib : W₀ →+* V₁)
    (B₀ : Over (Sp W₀)) [GrpObj B₀] (β : D.P.A.left ⟶ B₀.left) (hβ : IsGrpPullback D.P.A B₀ (spMap ib) β)
    (K : Type) [Field K] (ev : V₁ →+* K) (k₀ : Subfield K) (hk : ∀ a, ev (ib a) ∈ k₀)
    (σ : K ≃+* K) (hσ : ∀ a ∈ k₀, σ a = a) :
    ∃ σt : (Over.mk (spMap ev) ⊗ D.P.A).left ⟶ (Over.mk (spMap ev) ⊗ D.P.A).left,
      σt ≫ (fst (Over.mk (spMap ev)) D.P.A).left = (fst (Over.mk (spMap ev)) D.P.A).left ≫ spMap σ.toRingHom ∧
      σt ≫ (snd (Over.mk (spMap ev)) D.P.A).left ≫ β = (snd (Over.mk (spMap ev)) D.P.A).left ≫ β ∧
      ∀ x : Sp K ⟶ (Over.mk (spMap ev) ⊗ D.P.A).left, x ≫ (fst (Over.mk (spMap ev)) D.P.A).left = 𝟙 _ →
        DefOver k₀ (x ≫ (snd (Over.mk (spMap ev)) D.P.A).left ≫ β) → x ≫ σt = spMap σ.toRingHom ≫ x := by
  set E := Over.mk (spMap ev) with hE
  set fK := (fst E D.P.A).left with hfK
  set q := (snd E D.P.A).left with hq
  have hw : q ≫ D.P.A.hom = fK ≫ spMap ev := (Over.w (snd E D.P.A)).trans (Over.w (fst E D.P.A)).symm
  have hf : ∀ a, (ev.comp ib) a ∈ k₀ := hk
  obtain ⟨Φ₀, hΦ₀⟩ := GlobalTheory.GroupBplus.Aff.exists_mulEquiv_points_of_isGrpPullback hβ (fK ≫ spMap ev)
    (fK ≫ spMap (ev.comp ib)) (by rw [Category.assoc, spMap_two'])
  obtain ⟨Φ₁, hΦ₁⟩ := GlobalTheory.GroupBplus.Aff.exists_mulEquiv_points_of_isGrpPullback hβ (fK ≫ spMap σ.toRingHom ≫ spMap ev)
    (fK ≫ spMap (ev.comp ib))
    (by rw [Category.assoc, Category.assoc, spMap_two', spMap_conj k₀ _ hf σ hσ])
  let qpt : Over.mk (fK ≫ spMap ev) ⟶ D.P.A := Over.homMk q hw
  let σD := Φ₁.symm (Φ₀ qpt)
  let a0 : Over.mk (fK ≫ spMap σ.toRingHom ≫ spMap ev) ⟶ E :=
    Over.homMk (fK ≫ spMap σ.toRingHom) (Category.assoc _ _ _)
  let σt : (E ⊗ D.P.A).left ⟶ (E ⊗ D.P.A).left := (lift a0 σD).left
  have hfst : σt ≫ fK = fK ≫ spMap σ.toRingHom := congrArg (fun z => z.left) (lift_fst a0 σD)
  have hsnd : σt ≫ q = σD.left := congrArg (fun z => z.left) (lift_snd a0 σD)
  have hproj : σt ≫ q ≫ β = q ≫ β := by
    rw [reassoc_of% hsnd, ← hΦ₁ σD, MulEquiv.apply_symm_apply, hΦ₀]
    rfl
  refine ⟨σt, hfst, hproj, fun x hx hdef => ?_⟩
  have hEh : (E ⊗ D.P.A).hom = fK ≫ spMap ev := (Over.w (fst E D.P.A)).symm
  let T : Over (Sp V₁) := Over.mk (spMap σ.toRingHom ≫ spMap ev)
  let m1 : T ⟶ E ⊗ D.P.A := Over.homMk (x ≫ σt) (by
    show (x ≫ σt) ≫ (E ⊗ D.P.A).hom = spMap σ.toRingHom ≫ spMap ev
    rw [hEh, Category.assoc, reassoc_of% hfst, reassoc_of% hx])
  let m2 : T ⟶ E ⊗ D.P.A := Over.homMk (spMap σ.toRingHom ≫ x) (by
    show (spMap σ.toRingHom ≫ x) ≫ (E ⊗ D.P.A).hom = spMap σ.toRingHom ≫ spMap ev
    rw [hEh, Category.assoc, reassoc_of% hx])
  have hm : m1 = m2 := by
    apply CartesianMonoidalCategory.hom_ext
    · apply Over.OverMorphism.ext
      show (x ≫ σt) ≫ fK = (spMap σ.toRingHom ≫ x) ≫ fK
      rw [Category.assoc, hfst, reassoc_of% hx, Category.assoc, hx, Category.comp_id]
    · obtain ⟨Φ₂, hΦ₂⟩ := GlobalTheory.GroupBplus.Aff.exists_mulEquiv_points_of_isGrpPullback hβ
        (spMap σ.toRingHom ≫ spMap ev) (spMap (ev.comp ib))
        (by rw [Category.assoc, spMap_two', spMap_conj k₀ _ hf σ hσ])
      apply Φ₂.injective
      apply Over.OverMorphism.ext
      rw [hΦ₂, hΦ₂]
      show (x ≫ σt) ≫ q ≫ β = (spMap σ.toRingHom ≫ x) ≫ q ≫ β
      obtain ⟨P₀, hP₀⟩ := hdef
      rw [Category.assoc, hproj, Category.assoc, ← hP₀, ← Category.assoc,
        spMap_conj k₀ k₀.subtype (fun a => a.2) σ hσ]
  exact congrArg (fun m => m.left) hm

theorem gm_thetaIso {V₁ : Type} [CommRing V₁] [IsDomain V₁] (D : DegPre V₁) {B₀ : Scheme.{0}} {M₀ : LB B₀}
    (β : D.P.A.left ⟶ B₀) (w : LB.Iso D.P.L (M₀.pull β)) {K : Type} [Field K] (r : Sp K ⟶ D.P.A.left) (z : Sp K)
    (J : (Sp K ⟶ D.P.A.left) → D.P.L.ι) (J₀ : (Sp K ⟶ B₀) → M₀.ι) (hJ : Good D.P.L z J) (hJ₀ : Good M₀ z J₀) :
    gm r z _ ((GlobalTheory.PolDeg.TautFrom.isoPull (chartPullId (LB.LinComb D.P.L (D.famφB 0) (DegPre.famε 1)))
      (chartPullCompPull M₀ β (D.famφB 0) (DegPre.famε 1)) (LB.linCombIso w (D.famφB 0) (DegPre.famε 1))).s
        (fun k => J₀ (r ≫ (D.famφB 0 k ≫ β)), fun k => J (r ≫ D.famφB 0 k))) = gwx w z J J₀ r := by
  have hz : r z ∈ (LB.LinComb M₀ (fun k => D.famφB 0 k ≫ β) (DegPre.famε 1)).U (fun k => J₀ (r ≫ (D.famφB 0 k ≫ β))) ⊓
      (LB.LinComb D.P.L (D.famφB 0) (DegPre.famε 1)).U (fun k => J (r ≫ D.famφB 0 k)) :=
    ⟨hJ₀.mem (fun k => D.famφB 0 k ≫ β) r, hJ.mem (D.famφB 0) r⟩
  refine (GlobalTheory.PolDeg.TautFrom.gm_isoPull _ _ _ r z _ hz).trans ?_
  rw [Category.comp_id]
  have hm : r z ∈ LB.wchart (M₀.pull β) (D.famφB 0) (fun k _ => J₀ (r ≫ (D.famφB 0 k ≫ β))) ⊓
      LB.wchart D.P.L (D.famφB 0) (fun k => J (r ≫ D.famφB 0 k)) :=
    ⟨Set.mem_iInter.2 fun k => mem_pull.2 (Set.mem_iInter.1 hz.1 k), hz.2⟩
  refine (gm_linCombIso_pull' w (D.famφB 0) (DegPre.famε 1) r z (fun k => J₀ (r ≫ (D.famφB 0 k ≫ β)))
    (fun k => J (r ≫ D.famφB 0 k)) hm).trans ?_
  have h0 : D.famφB 0 0 = 𝟙 _ := rfl
  rw [Fin.prod_univ_four, h0, famφB_one D, famφB_two D]
  simp only [DegPre.famε, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.head_cons, Matrix.tail_cons, Nat.cast_one, sub_self, zpow_zero, zpow_one, zpow_neg, one_mul,
    Category.comp_id, Category.id_comp, mul_inv_cancel_right]
  rw [_root_.one_mul, inv_mul_cancel_right]

theorem theta_values : ∀ (V₁ : Type) [CommRing V₁] [IsDomain V₁] [IsLocalRing V₁], IsCN V₁ → (∀ m : ℕ, m ≠ 0 → IsUnit (m : V₁)) →
    ∀ (D : DegPre V₁) (τ₀ : GlobalTheory.UChart.Gens D) (W₀ : Type) [CommRing W₀] (ib : W₀ →+* V₁) (B₀ : Over (Sp W₀)) [GrpObj B₀]
      (M₀ : LB B₀.left) (c₀ : D.X → (Sp W₀ ⟶ B₀.left))
      (τ₁ : ∀ a b : D.X, LB.Gen (LB.LinComb M₀ (K := Fin 4) ![c₀ (a + b), c₀ a, c₀ b, c₀ 0] ![-1, 1, 1, -1]))
      (β : D.P.A.left ⟶ B₀.left) (w : LB.Iso D.P.L (M₀.pull β)), GlobalTheory.USep.EvG.FromBaseWith D τ₀ ib B₀ M₀ c₀ τ₁ β w →
    ∀ (K : Type) [Field K] [IsAlgClosed K] (ev : V₁ →+* K) (k₀ : Subfield K), IsAlgClosed k₀ → (∀ a, ev (ib a) ∈ k₀) →
    ∀ (z : Sp K) (J : (Sp K ⟶ D.P.A.left) → D.P.L.ι) (J₀ : (Sp K ⟶ B₀.left) → M₀.ι), Good D.P.L z J → Good M₀ z J₀ →
    ∀ (θ : SecOver D.P.A.hom (LB.LinComb D.P.L (D.famφB 0) (DegPre.famε 1))),
    (∀ (R' : Type) [CommRing R'] (f : V₁ →+* R') θ',
      IsPullSecLC D.P.L (D.famφB 0) (DegPre.famε 1) (snd (Over.mk (Spec.map (CommRingCat.ofHom f))) D.P.A).left θ θ' →
      GlobalTheory.Poinc.ThetaOne.OneBasisAt D f θ') →
    ∃ κ : K, ∀ p : 𝟙_ (Over (Sp V₁)) ⟶ D.P.A, DefOver k₀ (spMap ev ≫ p.left ≫ β) → ∃ c ∈ k₀,
      sval (θ : LB.Sec (LB.LinComb D.P.L (D.famφB 0) (DegPre.famε 1))) (spMap ev ≫ p.left) z J =
        ((GlobalTheory.USep.EvG.gwx w z J J₀ (spMap ev ≫ p.left))⁻¹).val * toStk z (κ * c) := by
  intro V₁ _ _ _ _ _ D τ₀ W₀ _ ib B₀ _ M₀ c₀ τ₁ β w hFB K _ _ ev k₀ hk₀ hk z J J₀ hJ hJ₀ θ hθ
  obtain ⟨-, hM₀, hβ, hw, -, -, -⟩ := hFB
  let u := GlobalTheory.PolDeg.TautFrom.isoPull (chartPullId (LB.LinComb D.P.L (D.famφB 0) (DegPre.famε 1)))
    (chartPullCompPull M₀ β (D.famφB 0) (DegPre.famε 1)) (LB.linCombIso w (D.famφB 0) (DegPre.famε 1))
  have hu : u.IsGen := GlobalTheory.PolDeg.TautFrom.isoPull_isGen _ _ _ (DVR.linCombIso_isGen w hw _ _)
  have hL : (LB.LinComb D.P.L (D.famφB 0) (DegPre.famε 1)).IsLB := DVR.linComb_isLB _ D.P.isLB _ _
  have hM : (LB.LinComb M₀ (fun k => D.famφB 0 k ≫ β) (DegPre.famε 1)).IsLB := DVR.linComb_isLB _ hM₀ _ _
  obtain ⟨s, hs⟩ := ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.exists_isoRel hL hM hu
    (θ : LB.Sec (LB.LinComb D.P.L (D.famφB 0) (DegPre.famε 1)))
  let E := Over.mk (spMap ev)
  let q := (snd E D.P.A).left
  have hqw : q ≫ D.P.A.hom = (fst E D.P.A).left ≫ spMap ev := (Over.w (snd E D.P.A)).trans (Over.w (fst E D.P.A)).symm
  let R : (Sp K ⟶ (E ⊗ D.P.A).left) → Prop := fun x => x ≫ (fst E D.P.A).left = 𝟙 _ ∧ DefOver k₀ (x ≫ q ≫ β)
  have hcases : ∀ k : Fin 4, D.famφB 0 k = 𝟙 _ ∨ D.famφB 0 k ≫ β = D.P.A.hom ≫ spMap ib ≫ (η[B₀]).left := by
    intro k
    fin_cases k
    · exact Or.inl rfl
    · exact Or.inl (by show D.famφB 0 1 = _; exact famφB_one D)
    · exact Or.inr (by show D.famφB 0 2 ≫ β = _; rw [famφB_two D]; exact eta_push hβ)
    · exact Or.inr (by show D.famφB 0 3 ≫ β = _; exact eta_push hβ)
  obtain ⟨κ, -, hval⟩ := galois_values k₀ hk₀ (fun k => q ≫ (D.famφB 0 k ≫ β)) (DegPre.famε 1)
    (ReciprocityTheory.ChartRestriction.G.H1.SectionArithmetic.pullSec s q) R
    (fun t => by
      obtain ⟨c, hc⟩ := fibre_one_dim D ev (θ : LB.Sec (LB.LinComb D.P.L (D.famφB 0) (DegPre.famε 1))) (hθ K ev)
        (fun k => D.famφB 0 k ≫ β) (DegPre.famε 1) hM₀ u hu s hs t
      exact ⟨c, fun x hR z J hJ => hc x hR.1 z J hJ⟩)
    (fun σ hσ => by
      obtain ⟨σt, hfst, hproj, hfix⟩ := exists_conj_fibre_one D ib B₀ β hβ K ev k₀ hk σ hσ
      refine ⟨σt, fun k => ?_, fun x hR => hfix x hR.1 hR.2⟩
      rcases hcases k with h | h
      · show σt ≫ q ≫ D.famφB 0 k ≫ β = q ≫ D.famφB 0 k ≫ β
        rw [h, Category.id_comp]
        exact hproj
      · show σt ≫ q ≫ D.famφB 0 k ≫ β = q ≫ D.famφB 0 k ≫ β
        have hf : ∀ a, (ev.comp ib) a ∈ k₀ := hk
        rw [h, reassoc_of% hqw, reassoc_of% hfst, spMap_two'_assoc ib ev, reassoc_of% (spMap_conj k₀ _ hf σ hσ)])
  refine ⟨κ, fun p hdef => ?_⟩
  have hr : (spMap ev ≫ p.left) ≫ D.P.A.hom = spMap ev := by
    rw [Category.assoc, Over.w p]
    exact Category.comp_id _
  let a1 : Over.mk (spMap ev) ⟶ E := Over.homMk (𝟙 (Sp K)) (Category.id_comp _)
  let b1 : Over.mk (spMap ev) ⟶ D.P.A := Over.homMk (spMap ev ≫ p.left) hr
  let x : Sp K ⟶ (E ⊗ D.P.A).left := (lift a1 b1).left
  have hxf : x ≫ (fst E D.P.A).left = 𝟙 _ :=
    congrArg (fun m : Over.mk (spMap ev) ⟶ E => m.left) (lift_fst a1 b1)
  have hxq : x ≫ q = spMap ev ≫ p.left := congrArg (fun m : Over.mk (spMap ev) ⟶ D.P.A => m.left) (lift_snd a1 b1)
  have hRx : R x := ⟨hxf, by
    show DefOver k₀ (x ≫ q ≫ β)
    rw [reassoc_of% hxq]
    exact hdef⟩
  obtain ⟨c, hc, he⟩ := hval x hRx z J₀ hJ₀
  refine ⟨c, hc, ?_⟩
  have e1 : sval s (spMap ev ≫ p.left) z J₀ = toStk z (κ * c) := by
    rw [← he, ReciprocityTheory.ChartRestriction.G.H1.SectionArithmetic.sval_pullSec s q x z hJ₀, hxq]
  have e2 := gs_isoRel_at hs _ _ (spMap ev ≫ p.left) z (hJ₀.mem (fun k => D.famφB 0 k ≫ β) (spMap ev ≫ p.left))
    (hJ.mem (D.famφB 0) (spMap ev ≫ p.left))
  rw [gm_thetaIso D β w (spMap ev ≫ p.left) z J J₀ hJ hJ₀] at e2
  have e4 : (gwx w z J J₀ (spMap ev ≫ p.left)).val *
      sval (θ : LB.Sec (LB.LinComb D.P.L (D.famφB 0) (DegPre.famε 1))) (spMap ev ≫ p.left) z J = toStk z (κ * c) := by
    rw [← e1]; exact e2.symm
  rw [← e4, Units.inv_mul_cancel_left]

end GlobalTheory.USep.EvG.ThetaVal
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaMapPullO1PowerHodge
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.UMin.KeyOne

theorem isNormalScheme_of_isOpenImmersion {X Y : Scheme.{0}} (f : Y ⟶ X) [IsOpenImmersion f]
    (h : Geo.Tor.IsNormalScheme X) : Geo.Tor.IsNormalScheme Y := by
  intro y
  obtain ⟨h1, h2⟩ := h (f y)
  let e : X.presheaf.stalk (f y) ≃+* Y.presheaf.stalk y :=
    (asIso (f.stalkMap y)).commRingCatIsoToRingEquiv
  exact ⟨MulEquiv.isDomain _ e.symm.toMulEquiv, IsIntegrallyClosed.of_equiv e⟩

theorem exists_lift_of_dense {P U : Scheme.{0}} (i : U ⟶ P) [IsOpenImmersion i] (hi : Dense (Set.range i))
    {k Ω : Type} [CommRing k] [Field Ω] [Algebra k Ω] (M : RatModel k Ω) (a : M.Z ⟶ P) [IsOpenImmersion a] :
    ∃ y : Sp Ω ⟶ U, y ≫ i = M.pt ≫ a := by
  have hV : IsOpen (Set.range a) := a.isOpenEmbedding.isOpen_range
  have hne : (Set.range a).Nonempty := ⟨_, M.pt (IsLocalRing.closedPoint Ω), rfl⟩
  obtain ⟨_, ⟨z, rfl⟩, hz⟩ := hi.inter_open_nonempty _ hV hne
  have hU : IsOpen (Set.range i) := i.isOpenEmbedding.isOpen_range
  have hsub : Set.range (M.pt ≫ a) ⊆ Set.range i := by
    rintro _ ⟨w, rfl⟩
    have := ((M.pt_specializes w z).map a.continuous).mem_open hU hz
    simpa using this
  exact ⟨IsOpenImmersion.lift i (M.pt ≫ a) hsub, IsOpenImmersion.lift_fac _ _ _⟩

theorem exists_pt_eq {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H}
    {l : Geo.Tor.Level H} {Xo : Moduli Dw l} {c : Coeff l} (Y : Model Xo c (RingHom.id c.F))
    {Ω : Type} [Field Ω] [Algebra c.F Ω] (M : RatModel c.F Ω) (io : M.Z ⟶ Y.X) [IsOpenImmersion io] :
    ∃ y : Sp Ω ⟶ Xo.XF c, M.pt ≫ io = y ≫ Y.j := by
  have hid : IsIso (pullback.fst Y.s (spMap (RingHom.id c.F))) := by
    have : IsIso (spMap (RingHom.id c.F)) := by
      show IsIso (Spec.map (CommRingCat.ofHom (RingHom.id c.F)))
      rw [show CommRingCat.ofHom (RingHom.id c.F) = 𝟙 _ from rfl]
      infer_instance
    infer_instance
  haveI := Y.jQ_open
  obtain ⟨y, hy⟩ := exists_lift_of_dense Y.jQ Y.jQ_dense M (io ≫ inv (pullback.fst Y.s (spMap (RingHom.id c.F))))
  refine ⟨y, ?_⟩
  rw [Model.j, ← Category.assoc, hy, Category.assoc, Category.assoc, IsIso.inv_hom_id, Category.comp_id]

theorem lbIso_pull_pull {X Y Z : Scheme.{0}} {A B : LB X} (hA : A.IsLB) (hB : B.IsLB) (f : Y ⟶ X) (g : Z ⟶ Y)
    (h : LBIso (A.pull (g ≫ f)) (B.pull (g ≫ f))) : LBIso ((A.pull f).pull g) ((B.pull f).pull g) := by
  have hA' := pull_isLB hA f
  have hB' := pull_isLB hB f
  rw [← CechPic.cls_eq_iff (pull_isLB hA' g) (pull_isLB hB' g), CechPic.cls_pull hA' g, CechPic.cls_pull hB' g,
    CechPic.cls_pull hA f, CechPic.cls_pull hB f, ← CechPic.pull_comp, ← CechPic.pull_comp,
    ← CechPic.cls_pull hA _ (pull_isLB hA _), ← CechPic.cls_pull hB _ (pull_isLB hB _), CechPic.cls_eq_iff]
  exact h

theorem lbIso_pull_lbPow {X Y : Scheme.{0}} {A B : LB X} (hA : A.IsLB) (hB : B.IsLB) (f : Y ⟶ X) (a b d : ℕ)
    (h : LBIso (lbPow ((lbPow A a).pull f) d) (lbPow ((lbPow B b).pull f) d)) :
    LBIso ((lbPow A (a * d)).pull f) ((lbPow B (b * d)).pull f) := by
  rw [← CechPic.cls_eq_iff (pull_isLB (isLB_lbPow hA _) f) (pull_isLB (isLB_lbPow hB _) f),
    CechPic.cls_pull (isLB_lbPow hA _) f, CechPic.cls_pull (isLB_lbPow hB _) f,
    CechPic.cls_lbPow hA, CechPic.cls_lbPow hB]
  rw [← CechPic.cls_eq_iff (isLB_lbPow (pull_isLB (isLB_lbPow hA _) f) _)
    (isLB_lbPow (pull_isLB (isLB_lbPow hB _) f) _), CechPic.cls_lbPow (pull_isLB (isLB_lbPow hA _) f),
    CechPic.cls_lbPow (pull_isLB (isLB_lbPow hB _) f), CechPic.cls_pull (isLB_lbPow hA _) f,
    CechPic.cls_pull (isLB_lbPow hB _) f, CechPic.cls_lbPow hA, CechPic.cls_lbPow hB] at h
  rw [map_nsmul, map_nsmul] at h
  rw [map_nsmul, map_nsmul, mul_nsmul, mul_nsmul, h]

end GlobalTheory.UMin.KeyOne

theorem GlobalTheory.UMin.KeyOne.lbIso_pull_O1_hodge : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (o : Type) [CommRing o] (m n : ℕ) (f : Xo.XF c ⟶ PSpace o n), Odd m → 3 ≤ m → IsUnit (m : o) → n + 1 = m ^ (4 * (Module.finrank ℚ E / 2 * (Dw.p + Dw.q))) → ThMap Xo.univ.t.G Xo.univ.t.PP.L Xo.univ.t.PP.rig m (pullback.fst _ _ : Xo.XF c ⟶ Xo.X) f → ∀ (Y : Model Xo c (RingHom.id c.F)) (g : Y.X ⟶ PSpace o n), Y.j ≫ g = f → ∀ (Ω : Type) [Field Ω] [Algebra c.F Ω] (M : RatModel c.F Ω) (io : M.Z ⟶ Y.X), IsOpenImmersion io → io ≫ Y.s = M.s → LBIso ((lbPow ((ProjSpace.O1 o n).pull g) (8 * (n + 1).factorial)).pull io) ((lbPow (GlobalTheory.SiegelTor.hodge Y.t.G (Module.finrank ℚ E / 2 * (Dw.p + Dw.q))) (4 * (n + 1).factorial * (n + 1).factorial)).pull io) := by
  intro E _ _ _ H Dw l Xo c o _ m n f hm hm3 hmu hn hf Y g hg Ω _ _ M io hio hs
  haveI := hio
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap c.F Ω).injective
  have hMn : Geo.Tor.IsNormalScheme M.Z := GlobalTheory.UMin.KeyOne.isNormalScheme_of_isOpenImmersion io Y.normal
  obtain ⟨y, hy⟩ := GlobalTheory.UMin.KeyOne.exists_pt_eq Y M io
  have hpol := GlobalTheory.T.universalTriple_fibre_principallyPolarised_dimension E H Dw l Xo c Ω (y ≫ pullback.fst _ _)
  obtain ⟨⟨θ, hθ⟩, hθup⟩ := GlobalTheory.T.principallyPolarisedFibre_exists_generator_stable Xo.X Xo.univ.t.G Xo.univ.t.PP.L Xo.univ.t.PP.isLB _ Ω _ hpol
  obtain ⟨Ω', _, _, pt, cc, hfd, -, hdeg, hlist, -⟩ := GlobalTheory.T.theta_constants_listed_finite_galois_extension Xo.X Xo.univ.t.G Xo.univ.t.PP.L
    Xo.univ.t.PP.rig Xo.univ.t.PP.isLB Xo.univ.t.PP.rigGen _ m (n + 1) Ω _ θ hm hn hpol
  letI : Algebra c.F Ω' := ((algebraMap Ω Ω').comp (algebraMap c.F Ω)).toAlgebra
  haveI : IsScalarTower c.F Ω Ω' := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : CharZero Ω' := charZero_of_injective_algebraMap (algebraMap Ω Ω').injective
  obtain ⟨M', π, hM'n, hπf, hπ⟩ := GlobalTheory.T.exists_normalization_model_finiteExtension c.F Ω M Ω' hMn
  have hup := GlobalTheory.T.thetaKeyFormula_normalCover_rational_thetaConstants E H Dw l Xo c o m n f hm hm3 hmu hn hf Y g hg Ω' M' (π ≫ io)
    (spMap (algebraMap Ω Ω') ≫ y) cc hM'n
    (by rw [← Category.assoc, hπ, Category.assoc, hy, Category.assoc])
    (by rw [Category.assoc]; exact ⟨_, pt, hθup _ hθ Ω' (algebraMap Ω Ω'), hlist⟩)
  have hO : ((ProjSpace.O1 o n).pull g).IsLB := pull_isLB (ProjSpace.O1_isLB o n) g
  have hH := (GlobalTheory.T.modelSemiAbelian_relDim_cotangent_vectorBundle E H Dw l Xo c Y).2.isLB_det
  have hA := pull_isLB (isLB_lbPow hO 8) io
  have hB := pull_isLB (isLB_lbPow hH (4 * (n + 1).factorial)) io
  have key := GlobalTheory.T.lineBundleIso_pow_multiple_degree_descends_normal c.F Ω M Ω' M' π _ _ (n + 1).factorial hMn hπf hπ hA hB hdeg
    (GlobalTheory.UMin.KeyOne.lbIso_pull_pull (isLB_lbPow hO 8) (isLB_lbPow hH _) io π hup)
  exact GlobalTheory.UMin.KeyOne.lbIso_pull_lbPow hO hH io 8 (4 * (n + 1).factorial) (n + 1).factorial key
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaSquareProductIsFunctionOnSpec
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.UPoinc GlobalTheory.TorRef
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.USep
open GlobalTheory.Poinc.ThetaOne GlobalTheory.Poinc.Sep GlobalTheory.UT GlobalTheory.FieldBaseChange
open ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.Poinc.Sep.Frames GlobalTheory.UT.CoefBasic

namespace GlobalTheory.IntPointFnSq

theorem c_comp_inv (V : Type) [CommRing V] [IsDomain V] (D : DegPre V) (χ : D.X) :
    (D.c χ).left ≫ (ι[D.P.A]).left = (D.c (-χ)).left := by
  rw [← Over.comp_left]
  congr 1
  have h : D.c χ * D.c (-χ) = 1 := by
    rw [← GlobalTheory.Poinc.ThetaOne.c_zero D, ← add_neg_cancel χ, D.c_add]; rfl
  exact (eq_inv_of_mul_eq_one_right h).symm

theorem c_eq_eta (V : Type) [CommRing V] [IsDomain V] (D : DegPre V) (χ : D.X) :
    (D.c (χ + -χ)).left = (η[D.P.A]).left := by
  rw [add_neg_cancel, GlobalTheory.Poinc.ThetaOne.c_zero, ← SymFrame.eta_eq]

open GlobalTheory.IntPointFn in

theorem fn_of_theta_sq : ∀ (V : Type) [CommRing V] [IsDomain V] (D : DegPre V)
    (θ : SecOver D.P.A.hom (LB.LinComb D.P.L (D.famφB 0) (DegPre.famε 1)))
    (b : 𝟙_ (Over (Sp V)) ⟶ D.P.A) (χ : D.X)
    (t : LB.Gen (LB.LinComb D.P.L ![(η[D.P.A]).left, b.left] (DegPre.lineε 1))), t.IsGen →
    ∀ (χt : LB.Gen (LB.LinComb D.P.L ![(D.c χ * b).left, (D.c χ).left, b.left, (η[D.P.A]).left] DegPre.gtε)),
    χt.IsGen →
    ∀ (τ : LB.Gen (LB.LinComb D.P.L (K := Fin 4) ![(D.c (χ + -χ)).left, (D.c χ).left, (D.c (-χ)).left, (D.c 0).left]
      ![-1, 1, 1, -1])), τ.IsGen →
    ∃ G : V, ∀ (Z : Scheme.{0}) (r : Z ⟶ Sp V) (z : Z) J, Good D.P.L z J →
      gs r z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of V)).inv.hom G) =
        sval (θ : LB.Sec (LB.LinComb D.P.L (D.famφB 0) (DegPre.famε 1))) (r ≫ (b * D.c χ).left) z J ^ 2 *
          (val t r z J ^ 2 * val χt r z J ^ 2 * val D.sym (r ≫ (D.c χ).left) z J *
            (val τ r z J)⁻¹ * (rigV D r z J ^ 2)⁻¹).val := by
  intro V _ _ D θ b χ t ht χt hχt τ hτ
  have hL := D.P.isLB
  have e0 : (D.c 0).left = (η[D.P.A]).left := by rw [GlobalTheory.Poinc.ThetaOne.c_zero, ← SymFrame.eta_eq]
  have e1 := c_comp_inv V D χ
  have e2 := c_eq_eta V D χ
  have e4 : (b * D.c χ).left = (D.c χ * b).left := by rw [_root_.mul_comm]
  let u := LB.mulGen D.P.L _ _ _ _ (LB.mulGen D.P.L _ _ _ _ (LB.mulGen D.P.L _ _ _ _
    (LB.mulGen D.P.L _ _ _ _ (LB.mulGen D.P.L _ _ _ _ t t) (LB.mulGen D.P.L _ _ _ _ χt χt))
    (LB.pullGen D.P.L _ _ D.sym (D.c χ).left)) (LB.invGen D.P.L _ _ τ))
    (LB.invGen D.P.L _ _ (LB.mulGen D.P.L (Y := Sp V) (fun _ : PUnit => eSec D.P.A) (fun _ => 1) (fun _ : PUnit => eSec D.P.A) (fun _ => 1) D.rig D.rig))
  have hu : u.IsGen := by
    refine mulGen_isGen _ _ _ _ _ _ _ (mulGen_isGen _ _ _ _ _ _ _ (mulGen_isGen _ _ _ _ _ _ _
      (mulGen_isGen _ _ _ _ _ _ _ (mulGen_isGen _ _ _ _ _ _ _ ht ht) (mulGen_isGen _ _ _ _ _ _ _ hχt hχt))
      (pullGen_isGen _ _ _ _ D.sym_gen _)) (invGen_isGen _ _ _ _ hτ))
      (invGen_isGen _ _ _ _ (mulGen_isGen _ _ _ _ _ _ _ D.rig_gen D.rig_gen))
  obtain ⟨s', hs'⟩ := GlobalTheory.Poinc.Sep.ConjPt.exists_powSec hL (θ : LB.Sec (LB.LinComb D.P.L (D.famφB 0) (DegPre.famε 1)))
    (b * D.c χ).left 2 u hu (K' := PEmpty) PEmpty.elim PEmpty.elim (fun U _ f => by
      simp only [u, Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr, Fin.prod_univ_four, Fin.prod_univ_two,
        Fintype.prod_empty, Fintype.prod_unique, DegPre.famφB, DegPre.famε, DegPre.lineε, DegPre.gtε,
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons,
        Matrix.tail_cons, Category.comp_id, Nat.cast_one, sub_self,
        comp_padd_c_zero, comp_toUnit_c_zero, comp_toUnit_eta, eSec, e0, e1, e2, e4]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv, ofMul_zpow, ofMul_pow, ofMul_one]
      abel)
  obtain ⟨a, ha⟩ := GlobalTheory.Poinc.Sep.ConjPt.exists_fn s'
  refine ⟨(Scheme.ΓSpecIso (CommRingCat.of V)).hom.hom a, fun Z r z J hJ => ?_⟩
  have e2' : (Scheme.ΓSpecIso (CommRingCat.of V)).inv.hom ((Scheme.ΓSpecIso (CommRingCat.of V)).hom.hom a) = a := by
    rw [← CommRingCat.comp_apply, Iso.hom_inv_id]; rfl
  rw [e2', ← ha, hs' Z r z J hJ]
  congr 1
  simp only [u, val_mul hJ, val_inv, val_pull hJ, rigV]
  simp only [pow_two]

end GlobalTheory.IntPointFnSq
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToricPeriodZetaStatementsOfJetIntegralityAlgebraStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.toricPeriodZetaStatements_of_jetIntegrality_algebraicity : GlobalTheory.Published.EllipticMainTheoremCM → GlobalTheory.Published.HilbertClassFieldJ → GlobalTheory.Published.SiegelKlingenDeligneRibet → GlobalTheory.Published.PartialZetaFunctionalEquation → GlobalTheory.Published.HeckeTateFunctionalEquation → GlobalTheory.LatJet.JetInt → GlobalTheory.LatVal.LatAlg → GlobalTheory.LatVal.LatConj → GlobalTheory.Mem.LiteralAutomorphy.JoinOut := by
  first | exact @GlobalTheory.JoinFun.joinOut_of_jetInt | exact GlobalTheory.JoinFun.joinOut_of_jetInt | (intros; apply GlobalTheory.JoinFun.joinOut_of_jetInt <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionCoordinatesScalarMulSubfieldValuedStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.UPoinc GlobalTheory.TorRef
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.USep
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.torsionCoordinates_scalar_mul_subfieldValued : ∀ (g n : ℕ), n.Prime → Odd n → ∃ j₀ : ℕ, ∀ j, j₀ ≤ j → ∀ (V₁ : Type) [CommRing V₁] [IsDomain V₁] [IsLocalRing V₁], IsCN V₁ → (∀ m : ℕ, m ≠ 0 → IsUnit (m : V₁)) → ∀ (D : DegPre V₁), D.P.g = g → ∀ (X C : Type) [AddCommGroup X] (e : X ≃+ D.X) (u : X → C → V₁) (mo : X → V₁), (∀ mu, mo mu ≠ 0 ∧ ∃ c, IsUnit (u mu c)) → GlobalTheory.Poinc.Sep.IsThetaTerms D ((n ^ j) ^ 2) e (fun mu c => u mu c * mo mu) → ∀ (K : Type) [Field K] [IsAlgClosed K] (ev : V₁ →+* K) (k₀ : Subfield K), IsAlgClosed k₀ → (∀ mu c c', IsUnit (u mu c') → ∃ r ∈ k₀, ev (u mu c) = r * ev (u mu c')) → ∀ (I : Type) (y : I → (Over.mk (spMap ev) ⟶ D.P.A)), (∀ i, y i ^ (n ^ j) ^ 2 = 1) → ∀ (a : D.X) (z : Over.mk (spMap ev) ⟶ D.P.A), z.left = spMap ev ≫ (D.c a).left → ∃ (v : I → K) (l : K) (r : I → K), GlobalTheory.Ex.IsCoordPt D.P (n ^ j) y z (fun i => GlobalTheory.Ex.fnOf (v i)) ∧ (∀ i, r i ∈ k₀) ∧ ∀ i, v i = l * r i := by
  first | exact @GlobalTheory.USep.coords_scalar_mul_rational | exact GlobalTheory.USep.coords_scalar_mul_rational | (intros; apply GlobalTheory.USep.coords_scalar_mul_rational <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionFrameMulIntegralFrameEqRootMulRigStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.UPoinc GlobalTheory.TorRef
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.USep
open GlobalTheory.Poinc.ThetaOne GlobalTheory.Poinc.Sep GlobalTheory.FieldBaseChange GlobalTheory.UT
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.torsionFrame_mul_integralFrame_eq_root_mul_rig : ∀ (V₁ : Type) [CommRing V₁] [IsDomain V₁] (D : DegPre V₁) (K : Type) [Field K] (ev : V₁ →+* K) (ρ₀ : LB.Gen (D.P.L.pull (eSec D.P.A))), ρ₀.IsGen → ∀ (n : ℕ), 1 ≤ n → ∀ (b : 𝟙_ (Over (Sp V₁)) ⟶ D.P.A) (τ : LB.Gen (LB.LinComb D.P.L (Y := (Over.mk (spMap ev)).left) (K := Fin 1) (fun _ => (toUnit (Over.mk (spMap ev)) ≫ b).left) (fun _ => 1))), IsTorsFrame D.P ρ₀ n (toUnit (Over.mk (spMap ev)) ≫ b) τ → ∀ (t : LB.Gen (LB.LinComb D.P.L ![(η[D.P.A]).left, b.left] (DegPre.lineε 1))), t.IsGen → (∀ κ : LB.Gen (kapLB D (𝟙 D.P.A ^ n) (n ^ 2) 1), Normd κ → ∀ (z : (Over.mk (spMap ev)).left) J, Good D.P.L z J → val t (Over.mk (spMap ev)).hom z J ^ (n ^ 2) * val κ ((Over.mk (spMap ev)).hom ≫ b.left) z J = 1) → ∃ ζ : K, ζ ^ (n ^ 2) = 1 ∧ ∀ (z : (Over.mk (spMap ev)).left) J, Good D.P.L z J → (val τ (𝟙 _) z J).val * (val t (Over.mk (spMap ev)).hom z J).val = gs (𝟙 (Over.mk (spMap ev)).left) z ⊤ (GlobalTheory.Ex.fnOf ζ) * (val ρ₀ (Over.mk (spMap ev)).hom z J).val := by
  first | exact @GlobalTheory.USep.FrameRoot.frame_mul_eq_root | exact GlobalTheory.USep.FrameRoot.frame_mul_eq_root | (intros; apply GlobalTheory.USep.FrameRoot.frame_mul_eq_root <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TripleIsoOfLinearDegenerationDataIsoStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tripleIso_of_linear_degenerationData_iso : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], GlobalTheory.Mum.Base V → ∀ (t t' : SAB H (Sp V)) (P : PELUnif (maximalIdeal V) t) (P' : PELUnif (maximalIdeal V) t') (hD : IsPullDeg (RingHom.id V) P.D.toPre P'.D.toPre), (∀ (x : 𝓞 E) y, hD.xe (x • y) = x • hD.xe y) → (letI := H.starRing; ∀ x, P'.oD.onB.act x ≫ hD.e.hom = hD.e.hom ≫ (Over.pullback (specOf (RingHom.id V))).map (P.oD.onB.act x)) → Nonempty (SABMap t' t (𝟙 _)) := by
  first | exact @GlobalTheory.triple_iso_of_linear_data_iso | exact GlobalTheory.triple_iso_of_linear_data_iso | (intros; apply GlobalTheory.triple_iso_of_linear_data_iso <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ZarhinBundleKernelFirstCoordEquationsStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor GlobalTheory.EndLoc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.zarhinBundle_kernel_firstCoord_equations : ∀ (h M d : ℕ) (S : Scheme.{0}) (t : S ⟶ Sp (cycAway M)) (c : SiegPre h M (zetaAway M) t) (B : Over S) [GrpObj B] [IsCommMonObj B] (Q : LB (c.A ⊗ B).left) (la : c.A ⟶ B) (mu : B ⟶ c.A) (hZ : GlobalTheory.ZarhinFam.ZData c d B Q la mu) (T : Over S) (x : T ⟶ GlobalTheory.ZarhinFam.Zob c.A B), (∃ t : ((GlobalTheory.ZarhinFam.zP c.A B c.isLB hZ.2.1.isLB d mu).pull (lift (snd (GlobalTheory.ZarhinFam.Zob c.A B) T ≫ x) (fst (GlobalTheory.ZarhinFam.Zob c.A B) T)).left).Gen, t.IsGen) → ∀ i, (x ≫ GlobalTheory.ZarhinFam.pa c.A B i ≫ la) * ∏ j, (x ≫ GlobalTheory.ZarhinFam.pb c.A B j) ^ GlobalTheory.ZarhinFam.quat d j i = 1 := by
  first | (exact @GlobalTheory.ZarhinKerA.zarhinBundle_kernel) | (exact GlobalTheory.ZarhinKerA.zarhinBundle_kernel) | (intros; apply GlobalTheory.ZarhinKerA.zarhinBundle_kernel  <;> assumption)
end

