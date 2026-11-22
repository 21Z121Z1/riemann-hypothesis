import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0073
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0030
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0060
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverIffIsProperAndExistsIsAmpleLB
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0024
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0009
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.BijectiveCechDeRhamComparisonDegreeOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapPairDetCovec
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2289
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2310
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2345
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2284
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0023
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsNoetherianRingDualNumber
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0029
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0072
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ZeroSectionBase
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsDeRhamSheaf
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0007
import Development.AbelianVarietyTheory.Definitions.Divisors.IsQuasicoherentEigenQuot
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2346
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0032
import Development.AbelianVarietyTheory.PublishedTheorems.RelativeAmpleness.RelAmpleAndKTrivIff

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAmpleTensorLbPowMonoOfGenerated
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.AmpleTwistLarger

theorem isAmpleLB_tens_lbPow_succ {S : Scheme.{0}} {L M : LB S} {N m : ℕ} (hL : L.IsLB) (hM : M.IsLB)
    (hG : GlobalTheory.IsGenerated (lbPow L N)) (hA : GlobalTheory.IsAmpleLB (GlobalTheory.CechPic.tens (lbPow L (N * m)) M)) :
    GlobalTheory.IsAmpleLB (GlobalTheory.CechPic.tens (lbPow L (N * (m + 1))) M) := by
  have h₁ := GlobalTheory.isLB_lbPow hL (N * (m + 1))
  have h₂ := GlobalTheory.isLB_lbPow hL (N * m)
  have h₃ := GlobalTheory.isLB_lbPow hL N
  have hT := GlobalTheory.CechPic.isLB_tens h₁ hM
  have hS := GlobalTheory.CechPic.isLB_tens h₂ hM
  have hq := LB.isLB_div hT hS
  refine hA.tensor_isGenerated hG hT ((GlobalTheory.CechPic.cls_eq_zero_iff (LB.isLB_div hq h₃)).1 ?_)
  rw [GlobalTheory.CechPic.cls_div hq h₃, GlobalTheory.CechPic.cls_div hT hS, GlobalTheory.CechPic.cls_tens h₁ hM,
    GlobalTheory.CechPic.cls_tens h₂ hM, GlobalTheory.CechPic.cls_lbPow hL, GlobalTheory.CechPic.cls_lbPow hL, GlobalTheory.CechPic.cls_lbPow hL,
    Nat.mul_succ, add_smul]
  abel

theorem isAmpleLB_tens_lbPow_of_le : ∀ (S : Scheme.{0}) (L M : LB S) (N k : ℕ), L.IsLB → M.IsLB → GlobalTheory.IsGenerated (lbPow L N) → GlobalTheory.IsAmpleLB (GlobalTheory.CechPic.tens (lbPow L (N * k)) M) → ∀ k', k ≤ k' → GlobalTheory.IsAmpleLB (GlobalTheory.CechPic.tens (lbPow L (N * k')) M) := by
  intro S L M N k hL hM hG hA k' hk
  induction k', hk using Nat.le_induction with
  | base => exact hA
  | succ m _ ih => exact isAmpleLB_tens_lbPow_succ hL hM hG ih

end GlobalTheory.AmpleTwistLarger
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsColimitSpecQuotientComplementaryIdempotents
section
open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

open Limits

theorem specQuotIdemCoprod_bij (R : Type) [CommRing R] (e e' : R) (he : IsIdempotentElem e)
    (hs : e + e' = 1) :
    Function.Bijective ((Ideal.Quotient.mk (Ideal.span {e})).prod
      (Ideal.Quotient.mk (Ideal.span {e'}))) := by
  have he' : e' = 1 - e := by rw [← hs]; ring
  have hee : e * e' = 0 := by rw [he', mul_sub, _root_.mul_one, he.eq, sub_self]
  constructor
  · rw [injective_iff_map_eq_zero]
    intro x hx
    simp only [RingHom.prod_apply, Prod.mk_eq_zero, Ideal.Quotient.eq_zero_iff_mem,
      Ideal.mem_span_singleton'] at hx
    obtain ⟨⟨a, rfl⟩, ⟨b, hb⟩⟩ := hx
    have h1 : a * e * e' = 0 := by rw [_root_.mul_assoc, hee, mul_zero]
    have h2 : a * e * e = 0 := by
      rw [← hb, _root_.mul_assoc, mul_comm e' e, hee, mul_zero]
    calc a * e = a * e * (e + e') := by rw [hs, _root_.mul_one]
      _ = 0 := by rw [mul_add, h1, h2, add_zero]
  · rintro ⟨x, y⟩
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective y
    refine ⟨a * e' + b * e, ?_⟩
    simp only [RingHom.prod_apply, Prod.mk.injEq]
    constructor
    · rw [Ideal.Quotient.eq, Ideal.mem_span_singleton']
      exact ⟨b - a, by rw [he']; ring⟩
    · rw [Ideal.Quotient.eq, Ideal.mem_span_singleton']
      exact ⟨a - b, by rw [he']; ring⟩

theorem specQuotIdemCoprod : ∀ (R : Type) [CommRing R] (e e' : R), IsIdempotentElem e → e + e' = 1 → Nonempty (Limits.IsColimit (Limits.BinaryCofan.mk (spMap (Ideal.Quotient.mk (Ideal.span {e}))) (spMap (Ideal.Quotient.mk (Ideal.span {e'}))))) := by
  intro R _ e e' he hs
  let A := R ⧸ Ideal.span {e}
  let B := R ⧸ Ideal.span {e'}
  let φ : R →+* A × B := (Ideal.Quotient.mk (Ideal.span {e})).prod
      (Ideal.Quotient.mk (Ideal.span {e'}))
  have hφ : Function.Bijective φ := specQuotIdemCoprod_bij R e e' he hs
  let ψ : R ≃+* A × B := RingEquiv.ofBijective φ hφ
  let g : Spec (CommRingCat.of A) ⨿ Spec (CommRingCat.of B) ⟶ Sp R :=
    coprodSpec A B ≫ Spec.map (CommRingCat.ofHom φ)
  haveI : IsIso (Spec.map (CommRingCat.ofHom φ)) := by
    have : IsIso (CommRingCat.ofHom φ) := by
      change IsIso (RingEquiv.toCommRingCatIso ψ).hom
      infer_instance
    infer_instance
  haveI : IsIso g := by dsimp only [g]; infer_instance
  let i := asIso g
  refine ⟨IsColimit.ofIsoColimit (coprodIsCoprod (Spec (CommRingCat.of A)) (Spec (CommRingCat.of B)))
    (Cocone.ext i ?_)⟩
  rintro ⟨⟨⟩⟩
  · simp only [i, asIso_hom, g]
    show coprod.inl ≫ coprodSpec A B ≫ _ = spMap _
    rw [coprodSpec_inl_assoc, ← Spec.map_comp]
    rfl
  · simp only [i, asIso_hom, g]
    show coprod.inr ≫ coprodSpec A B ≫ _ = spMap _
    rw [coprodSpec_inr_assoc, ← Spec.map_comp]
    rfl

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCombAtGBaseChange
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.LineNorm
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete

open GlobalTheory.FlatModel

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FlatModel.BaseChangeComb

theorem comp_listProd' {B : Scheme.{0}} {G : Over B} [GrpObj G] {T T' : Over B} (f : T' ⟶ T) (L : List (T ⟶ G)) :
    f ≫ L.prod = (L.map (f ≫ ·)).prod := by
  induction L with
  | nil => exact MonObj.comp_one f
  | cons a L ih => rw [List.prod_cons, MonObj.comp_mul, ih, List.map_cons, List.prod_cons]

theorem dualMap_comp_epsMul' {R S : Type} [CommRing R] [CommRing S] (φ : R →+* S) (a : R) :
    (dualMap φ).comp (epsMul a) = (epsMul (φ a)).comp (dualMap φ) := by
  apply RingHom.ext
  intro r
  ext <;> simp [dualMap, epsMul, _root_.mul_comm]

theorem bc_comb_eig : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (X : Scheme.{0})
    (t : SAB H X) (R S : Type) [CommRing R] [CommRing S] (φ : R →+* S) (x : Sp R ⟶ X) (g : ℕ)
    (e : Fin g → (Sp (DualNumber R) ⟶ t.G.left)) (U : Fin g → R) (σ : 𝓞 E →+* R) (u : Sp (DualNumber R) ⟶ t.G.left),
    (IsCombAtG t x e U u → IsCombAtG t (spMap φ ≫ x) (bcV t φ e) (fun b => φ (U b)) (spMap (dualMap φ) ≫ u)) ∧
    (IsEigG t σ u → IsEigG t (φ.comp σ) (spMap (dualMap φ) ≫ u)) := by
  intro E _ _ _ H X t R S _ _ φ x g e U σ u
  refine ⟨fun h => ?_, fun h a => ?_⟩
  · obtain ⟨w, hw, hp⟩ := h
    have he : spMap (dualMap φ) ≫ (tEpsG x).hom = (tEpsG (spMap φ ≫ x)).hom := by
      show spMap (dualMap φ) ≫ spMap (algebraMap R (DualNumber R)) ≫ x =
        spMap (algebraMap S (DualNumber S)) ≫ spMap φ ≫ x
      rw [← Category.assoc, ← Category.assoc, ← spMap_comp, ← spMap_comp]
      congr 2
      apply RingHom.ext
      intro r
      ext <;> simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl]
    let bc : tEpsG (spMap φ ≫ x) ⟶ tEpsG x := Over.homMk (spMap (dualMap φ)) he
    refine ⟨fun i => bc ≫ w i, fun i => ?_, ?_⟩
    · show spMap (dualMap φ) ≫ (w i).left = spMap (epsMul (φ (U i))) ≫ spMap (dualMap φ) ≫ e i
      rw [hw i, ← Category.assoc, ← Category.assoc, ← spMap_comp, ← spMap_comp, dualMap_comp_epsMul']
    · have hl : (List.ofFn fun i => bc ≫ w i) = (List.ofFn w).map (bc ≫ ·) := by
        rw [List.map_ofFn]
        rfl
      rw [hl, ← comp_listProd', Over.comp_left, hp]
      rfl
  · show (spMap (dualMap φ) ≫ u) ≫ (t.act.act a).left = spMap (epsMul (φ (σ a))) ≫ spMap (dualMap φ) ≫ u
    rw [Category.assoc, h a, ← Category.assoc, ← Category.assoc, ← spMap_comp, ← spMap_comp, dualMap_comp_epsMul']

end GlobalTheory.FlatModel.BaseChangeComb

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCombAtZeroSectionEigenBlockFlattenedFrameStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.Cartier
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW secZ ptF LiesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR levDet secRing move)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.OrbitSep

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isCombAtZeroSection_eigenBlock_flattened_frame : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (X : Scheme.{0}) (t : SAB H X) (S : Type) [CommRing S] (x : Sp S ⟶ X) (n n' : ℕ) (e : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)) ≃ Fin n) (e' : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)) ≃ Fin n') (w' : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → (Sp (DualNumber S) ⟶ t.G.left)) (A : ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) S) (σ : E →+* ℂ) (i : Fin (Dw.mult σ)) (w : Sp (DualNumber S) ⟶ t.G.left), (∀ τ k, IsTanAtG t x (w' τ k)) → IsCombAtG t x (w' σ) (A σ i) w → IsCombAtG t x (fun c => w' (e'.symm c).1 (e'.symm c).2) (fun c => GlobalTheory.LogKSDiv.flatFrame A e e' (e ⟨σ, i⟩) c) w := by
  first | exact @GlobalTheory.LogKSDiv.isCombAtG_flatFrame | exact GlobalTheory.LogKSDiv.isCombAtG_flatFrame | (intros; apply GlobalTheory.LogKSDiv.isCombAtG_flatFrame <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsComplOfAgreeModSqZeroIdeal
section
open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.DeRham GlobalTheory.SqLift GlobalTheory.LiftSys GlobalTheory.Published
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.SqZeroSummand

variable {R : Type} [CommRing R] (I : Ideal R) {C : Type 1} [AddCommGroup C] [Module R C]

theorem smul_top_eq_sup {P Q : Submodule R C} (h : IsCompl P Q) :
    I • (⊤ : Submodule R C) = I • P ⊔ I • Q := by
  rw [← h.sup_eq_top, Submodule.smul_sup]

theorem sup_smul_top_eq {P Q : Submodule R C} (h : IsCompl P Q) :
    P ⊔ I • (⊤ : Submodule R C) = P ⊔ I • Q := by
  rw [smul_top_eq_sup I h, ← sup_assoc, sup_eq_left.mpr (Submodule.smul_le_right : I • P ≤ P)]

theorem inf_smul_top {P Q : Submodule R C} (h : IsCompl P Q) :
    P ⊓ I • (⊤ : Submodule R C) = I • P := by
  apply le_antisymm
  · intro x hx
    obtain ⟨hxP, hxJ⟩ := Submodule.mem_inf.mp hx
    rw [smul_top_eq_sup I h, Submodule.mem_sup] at hxJ
    obtain ⟨a, ha, b, hb, rfl⟩ := hxJ
    have hbQ : b ∈ Q := Submodule.smul_le_right hb
    have hbP : b ∈ P := by
      have e : b = (a + b) - a := by abel
      rw [e]; exact P.sub_mem hxP (Submodule.smul_le_right ha)
    have hb0 : b = 0 := (Submodule.disjoint_def.mp h.disjoint) b hbP hbQ
    simpa [hb0] using ha
  · exact le_inf Submodule.smul_le_right (Submodule.smul_mono le_rfl le_top)

theorem smul_smul_top (hI : I ^ 2 = 0) : I • I • (⊤ : Submodule R C) = ⊥ := by
  rw [← Submodule.mul_smul, ← sq, hI, Submodule.zero_eq_bot, Submodule.bot_smul]

theorem smul_le_of_sup_eq (hI : I ^ 2 = 0) {K F : Submodule R C}
    (h : K ⊔ I • ⊤ = F ⊔ I • ⊤) : I • K ≤ I • F := by
  calc I • K ≤ I • (K ⊔ I • ⊤) := Submodule.smul_mono le_rfl le_sup_left
    _ = I • F := by rw [h, Submodule.smul_sup, smul_smul_top I hI, sup_bot_eq]

end GlobalTheory.SqZeroSummand

open GlobalTheory.SqZeroSummand in

theorem GlobalTheory.SqZeroSummand.summand_of_agree_mod_sqZero :
    ∀ (R : Type) [CommRing R] (I : Ideal R), I ^ 2 = 0 → ∀ (C : Type 1) [AddCommGroup C] [Module R C] (F K N : Submodule R C), IsCompl F N → K ⊔ I • ⊤ = F ⊔ I • ⊤ → ((K ⊓ I • ⊤ = F ⊓ I • ⊤ → IsCompl K N) ∧ ((∃ N', IsCompl K N') → K ⊓ I • ⊤ = F ⊓ I • ⊤ ∧ ∃ u : F →ₗ[R] C, (∀ c, u c ∈ I • (⊤ : Submodule R C) ∧ u c ∈ N ∧ c.1 - u c ∈ K) ∧ (∀ c : F, c.1 ∈ I • (⊤ : Submodule R C) → u c = 0) ∧ ∀ k ∈ K, ∃ c : F, k = c.1 - u c)) := by
  intro R _ I hI C _ _ F K N hFN hKF
  have isCompl_of : K ⊓ I • ⊤ = F ⊓ I • ⊤ → IsCompl K N := by
    intro hi
    constructor
    · rw [Submodule.disjoint_def]
      intro x hxK hxN
      have hx : x ∈ F ⊔ I • N := by
        rw [← sup_smul_top_eq I hFN, ← hKF]; exact Submodule.mem_sup_left hxK
      obtain ⟨y, hy, b, hb, rfl⟩ := Submodule.mem_sup.mp hx
      have hbN : b ∈ N := Submodule.smul_le_right hb
      have hyN : y ∈ N := by
        have e : y = (y + b) - b := by abel
        rw [e]; exact N.sub_mem hxN hbN
      have hy0 : y = 0 := (Submodule.disjoint_def.mp hFN.disjoint) y hy hyN
      subst hy0
      rw [zero_add] at hxK hxN ⊢
      have hbJ : b ∈ K ⊓ I • (⊤ : Submodule R C) :=
        ⟨hxK, Submodule.smul_mono le_rfl le_top hb⟩
      rw [hi] at hbJ
      exact (Submodule.disjoint_def.mp hFN.disjoint) b hbJ.1 hbN
    · rw [codisjoint_iff, eq_top_iff, ← hFN.sup_eq_top]
      have h1 : I • F ≤ K := by
        have : I • F ≤ K ⊓ I • ⊤ := by
          rw [hi]; exact le_inf Submodule.smul_le_right (Submodule.smul_mono le_rfl le_top)
        exact this.trans inf_le_left
      have h2 : F ≤ K ⊔ N := by
        calc F ≤ F ⊔ I • ⊤ := le_sup_left
          _ = K ⊔ I • ⊤ := hKF.symm
          _ = K ⊔ (I • F ⊔ I • N) := by rw [smul_top_eq_sup I hFN]
          _ ≤ K ⊔ N := sup_le le_sup_left
              (sup_le (h1.trans le_sup_left) (Submodule.smul_le_right.trans le_sup_right))
      exact sup_le h2 le_sup_right
  refine ⟨isCompl_of, ?_⟩
  rintro ⟨N', hKN'⟩
  have hi : K ⊓ I • ⊤ = F ⊓ I • ⊤ := by
    rw [inf_smul_top I hKN', inf_smul_top I hFN]
    exact le_antisymm (smul_le_of_sup_eq I hI hKF) (smul_le_of_sup_eq I hI hKF.symm)
  have hKN := isCompl_of hi
  refine ⟨hi, (N.projection K hKN.symm) ∘ₗ F.subtype, ?_, ?_, ?_⟩
  · intro c
    simp only [LinearMap.comp_apply, Submodule.subtype_apply]
    refine ⟨?_, Submodule.projection_apply_mem _ _, Submodule.sub_projection_mem _ _⟩
    have hc : c.1 ∈ K ⊔ I • N := by
      rw [← sup_smul_top_eq I hKN, hKF]; exact Submodule.mem_sup_left c.2
    obtain ⟨k, hk, b, hb, hkb⟩ := Submodule.mem_sup.mp hc
    rw [← hkb, map_add, (Submodule.projection_apply_eq_zero_iff _).mpr hk, zero_add,
      Submodule.projection_apply_of_mem_left _ (Submodule.smul_le_right hb)]
    exact Submodule.smul_mono le_rfl le_top hb
  · intro c hc
    simp only [LinearMap.comp_apply, Submodule.subtype_apply]
    have h' : c.1 ∈ K ⊓ I • (⊤ : Submodule R C) := by rw [hi]; exact ⟨c.2, hc⟩
    exact (Submodule.projection_apply_eq_zero_iff _).mpr h'.1
  · intro k hk
    have hk' : k ∈ F ⊔ I • N := by
      rw [← sup_smul_top_eq I hFN, ← hKF]; exact Submodule.mem_sup_left hk
    obtain ⟨f, hf, b, hb, hfb⟩ := Submodule.mem_sup.mp hk'
    refine ⟨⟨f, hf⟩, ?_⟩
    simp only [LinearMap.comp_apply, Submodule.subtype_apply]
    have hbN : b ∈ N := Submodule.smul_le_right hb
    have ef : f = k - b := by rw [← hfb]; abel
    rw [ef, map_sub, (Submodule.projection_apply_eq_zero_iff _).mpr hk,
      Submodule.projection_apply_of_mem_left _ hbN]
    abel
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsDeRhamSheafIff
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Limits ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
  GlobalTheory.DeRham GlobalTheory.DeRhamSheaf

namespace GlobalTheory.HodgeSeqSheaf

variable {T : Scheme.{0}} (A : Over T) [GrpObj A]

def IsDRTriv (H : T.Modules)
    (e : ∀ (V : T.Opens) (hV : IsAffineOpen V), Γ(H, V) ≃ₗ[Γ(T, V)] primDR (onAff A hV)) : Prop :=
  ∀ (V V' : T.Opens) (hV : IsAffineOpen V) (hV' : IsAffineOpen V') (h : V' ≤ V),
    letI := resAlg h
    ∀ (φ : (onAff A hV').left ⟶ (onAff A hV).left)
      (hφ : IsGrpPullback (onAff A hV') (onAff A hV) (spMap (algebraMap Γ(T, V) Γ(T, V'))) φ),
      φ ≫ pullback.fst A.hom hV.fromSpec = pullback.fst A.hom hV'.fromSpec →
      ∀ s : Γ(H, V), e V' hV' (GlobalTheory.Twist.resM H h s) = (GlobalTheory.Published.AbelianDeRham.bcMor hφ).pull (e V hV s)

theorem isDeRhamSheaf_iff (H : T.Modules) : IsDeRhamSheaf A H ↔ ∃ e, IsDRTriv A H e := Iff.rfl

end GlobalTheory.HodgeSeqSheaf
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsDeRhamSheafIffAlt
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ConjSeq

variable (p : ℕ) [Fact p.Prime]

abbrev frobR (R : Type) [CommRing R] (hR : (p : R) = 0) : R →+* R :=
  GlobalTheory.SS.FrobField.powHom R p 1 Fact.out hR

theorem frobR_apply (R : Type) [CommRing R] (hR : (p : R) = 0) (x : R) : frobR p R hR x = x ^ p :=
  congrArg (x ^ ·) (pow_one p)

theorem frob_sp (R : Type) [CommRing R] (hR : (p : R) = 0) (h : (p : Γ(Sp R, ⊤)) = 0) :
    GlobalTheory.VB.frob (Sp R) p h = spMap (frobR p R hR) :=
  GlobalTheory.SS.FrobField.absFrob_spec R p 1 Fact.out h _ fun _ ↦ rfl

theorem frob_comp_hom (R : Type) [CommRing R] (hR : (p : R) = 0) {X : Scheme.{0}} (f : X ⟶ Sp R)
    (h : (p : Γ(X, ⊤)) = 0) : GlobalTheory.VB.frob X p h ≫ f = f ≫ spMap (frobR p R hR) := by
  have h0 : (p : Γ(Sp R, ⊤)) = 0 := GlobalTheory.SS.FrobField.cast_zero_sp R hR
  rw [GlobalTheory.VB.frob_naturality p h0 f h, frob_sp p R hR h0]

theorem cast_left (R : Type) [CommRing R] (hR : (p : R) = 0) (A : Over (Sp R)) :
    (p : Γ(A.left, ⊤)) = 0 :=
  GlobalTheory.SS.FrobField.cast_zero_of_hom A.hom (GlobalTheory.SS.FrobField.cast_zero_sp R hR)

theorem frobMor (R : Type) [CommRing R] (hR : (p : R) = 0) (A : Over (Sp R)) [GrpObj A]
    (h : (p : Γ(A.left, ⊤)) = 0) :
    GrpMor (dp0 R) (𝟙 _) A (dp0 R) (𝟙 _) A (frobR p R hR) (spMap (frobR p R hR))
      (GlobalTheory.VB.frob A.left p h) where
  dp := isDPMorphism_of_eq_bot _ rfl _ _
  base := by simp
  w := frob_comp_hom p R hR A.hom h
  mul T x y x₀ y₀ hx hy := by
    have hT : (p : Γ(T.left, ⊤)) = 0 := cast_left p R hR T
    let j : Over.mk (T.hom ≫ spMap (frobR p R hR)) ⟶ T :=
      Over.homMk (GlobalTheory.VB.frob T.left p hT) (by simpa using frob_comp_hom p R hR T.hom hT)
    have ex : x₀ = j ≫ x := Over.OverMorphism.ext (by
      simp [j, hx, GlobalTheory.VB.frob_naturality p h x.left hT])
    have ey : y₀ = j ≫ y := Over.OverMorphism.ext (by
      simp [j, hy, GlobalTheory.VB.frob_naturality p h y.left hT])
    subst ex ey
    rw [← MonObj.comp_mul]
    simp only [Over.comp_left, Over.homMk_left, j]
    exact GlobalTheory.VB.frob_naturality p h (x * y).left hT

def frobDR (R : Type) [CommRing R] (hR : (p : R) = 0) (A : Over (Sp R)) [GrpObj A] :
    primDR A →ₛₗ[frobR p R hR] primDR A :=
  (frobMor p R hR A (cast_left p R hR A)).pull

def conjDR (R : Type) [CommRing R] (hR : (p : R) = 0) (A : Over (Sp R)) [GrpObj A] :
    Submodule R (primDR A) :=
  Submodule.span R (Set.range (frobDR p R hR A))

end GlobalTheory.ConjSeq

namespace GlobalTheory.DeRhamSheaf

open Limits

variable {T : Scheme.{0}} (A : Over T) [GrpObj A]

def IsDRIso (H : T.Modules)
    (e : ∀ (V : T.Opens) (hV : IsAffineOpen V), Γ(H, V) ≃ₗ[Γ(T, V)] primDR (onAff A hV)) : Prop :=
  ∀ (V V' : T.Opens) (hV : IsAffineOpen V) (hV' : IsAffineOpen V') (h : V' ≤ V),
    letI := resAlg h
    ∀ (φ : (onAff A hV').left ⟶ (onAff A hV).left)
      (hφ : IsGrpPullback (onAff A hV') (onAff A hV) (spMap (algebraMap Γ(T, V) Γ(T, V'))) φ),
      φ ≫ pullback.fst A.hom hV.fromSpec = pullback.fst A.hom hV'.fromSpec →
      ∀ s : Γ(H, V), e V' hV' (GlobalTheory.Twist.resM H h s) = (GlobalTheory.Published.AbelianDeRham.bcMor hφ).pull (e V hV s)

theorem isDeRhamSheaf_iff (H : T.Modules) : IsDeRhamSheaf A H ↔ ∃ e, IsDRIso A H e := Iff.rfl

end GlobalTheory.DeRhamSheaf
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsDifferenceDerivationOfLiftsAddSwapUnique
section
open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

namespace GlobalTheory.Obs

theorem mul_eq_zero_of_mem_map_sq {R : Type} [CommRing R] {I : Ideal R} (hI : I ^ 2 = 0) {B' : Type} [CommRing B']
    [Algebra R B'] {x y : B'} (hx : x ∈ I.map (algebraMap R B')) (hy : y ∈ I.map (algebraMap R B')) : x * y = 0 := by
  have h := Ideal.mul_mem_mul hx hy
  rw [← sq, map_sq hI B', Ideal.zero_eq_bot, Ideal.mem_bot] at h
  exact h

theorem isTheta_mul_eq {R R₀ : Type} [CommRing R] [CommRing R₀] {I : Ideal R} (hI : I ^ 2 = 0) {B B₀ B' : Type}
    [CommRing B] [Algebra R B] [CommRing B₀] [Algebra R₀ B₀] [CommRing B'] [Algebra R B'] {p : B →+* B₀}
    {a b : B →ₐ[R] B'} {θ : Ω[B₀⁄R₀] →+ B'} (h : IsTheta I p a b θ) (x : B) {t : B'}
    (ht : t ∈ I.map (algebraMap R B')) : a x * t = b x * t := by
  have hd : (a x - b x) * t = 0 := by
    rw [← h.der x]; exact mul_eq_zero_of_mem_map_sq hI (h.mem _) ht
  rw [sub_mul, sub_eq_zero] at hd
  exact hd

theorem isTheta_add : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (hI : I ^ 2 = 0) (π : R →+* R₀) (hπ : Function.Surjective π) (hk : RingHom.ker π = I) (B B₀ : Type) [CommRing B] [Algebra R B] [CommRing B₀] [Algebra R₀ B₀] (p : B →+* B₀) (hs : SemiHom π p) (hp : Function.Surjective p) (hker : ∀ b, p b = 0 ↔ b ∈ I.map (algebraMap R B)) (B' : Type) [CommRing B'] [Algebra R B'] (a b c : B →ₐ[R] B') (θ θ' : Ω[B₀⁄R₀] →+ B'), IsTheta I p a b θ → (IsTheta I p b a (-θ) ∧ (IsTheta I p b c θ' → IsTheta I p a c (θ + θ')) ∧ (IsTheta I p a b θ' → θ = θ') ∧ (θ = 0 → a = b)) := by
  intro R R₀ _ _ I hI π hπ hk B B₀ _ _ _ _ p hs hp hker B' _ _ a b c θ θ' h
  refine ⟨⟨fun x w ↦ ?_, fun x ↦ ?_, fun w ↦ ?_⟩, fun h' ↦ ⟨fun x w ↦ ?_, fun x ↦ ?_, fun w ↦ ?_⟩, fun h' ↦ ?_,
    fun h0 ↦ ?_⟩
  · rw [AddMonoidHom.neg_apply, AddMonoidHom.neg_apply, h.smul, mul_neg, isTheta_mul_eq hI h x (h.mem w)]
  · rw [AddMonoidHom.neg_apply, h.der, neg_sub]
  · exact (Ideal.neg_mem_iff _).2 (h.mem w)
  · rw [AddMonoidHom.add_apply, AddMonoidHom.add_apply, h.smul, h'.smul, mul_add,
      isTheta_mul_eq hI h x (h'.mem w)]
  · rw [AddMonoidHom.add_apply, h.der, h'.der]; ring
  · exact Ideal.add_mem _ (h.mem w) (h'.mem w)
  · ext w
    have hw : w ∈ Submodule.span B₀ (Set.range (KaehlerDifferential.D R₀ B₀)) := by
      rw [KaehlerDifferential.span_range_derivation]; exact Submodule.mem_top
    induction hw using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨y, rfl⟩ := hy
      obtain ⟨x, rfl⟩ := hp y
      rw [h.der, h'.der]
    | zero => simp
    | add u v _ _ hu hv => rw [map_add, map_add, hu, hv]
    | smul r u _ hu =>
      obtain ⟨x, rfl⟩ := hp r
      rw [h.smul, h'.smul, hu]
  · ext x
    have := h.der x
    rw [h0, AddMonoidHom.zero_apply] at this
    exact (sub_eq_zero.1 this.symm)

end GlobalTheory.Obs
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFiniteTwistedKernelCubeLambdaStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isFinite_twisted_kernel_cubeLambda : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (A : Over (Sp R)) [GrpObj A], IsAbelianScheme A → ∀ L : LB A.left, L.IsLB → Out.RelAmple A L → ∀ (T : Over (Sp R)) [IsAffine T.left], LocallyOfFiniteType T.hom → ∀ N : LB (A ⊗ T).left, Fam A N → ∀ (H : Over (Sp R)) (h : H ⟶ A ⊗ T), IsClosedImmersion h.left → (∀ (Y : Over (Sp R)) (a : Y ⟶ A) (t : Y ⟶ T), Same A (abelian₂ A L) N a t ↔ ∃ z : Y ⟶ H, z ≫ h = lift a t) → IsFinite (h ≫ snd A T).left := by
  first | exact @GlobalTheory.TwistKerFinite.isFinite_twisted_kernel | exact GlobalTheory.TwistKerFinite.isFinite_twisted_kernel | (intros; apply GlobalTheory.TwistKerFinite.isFinite_twisted_kernel <;> assumption)
end

