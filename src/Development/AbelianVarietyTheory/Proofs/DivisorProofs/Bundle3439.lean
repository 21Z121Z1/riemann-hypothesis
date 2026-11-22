import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0073
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0089
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactificationBis
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3419
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsChartOfMemRedKer
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle0016
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3380
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3421
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3423
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3414
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3420
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3384
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3422
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0077
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsMonoFamNontrivial
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0021
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3416
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3370
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3345
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0718
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2559
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2502
import Development.AbelianVarietyTheory.Definitions.Divisors.LabRange

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTorusTangentOfRaynaudTangentOverUnit
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HeatMod.TorField

open TrivSqZeroExt (inl inr)
open ReciprocityTheory.ChartRestriction.G.Semi.Rosenlicht (coord coord_comp)

theorem exists_torTan_of_q : ∀ (R : Type) [CommRing R] [IsDomain R] (Q : DegPre R) (O : Type) [CommRing O] [StarRing O] [Module O Q.X] (oa : Q.OAct O) (Y : Ray oa) (p : epsR R ⟶ Y.H), IsTangent p → p ≫ Y.q = 1 → ∃ ℓ : Q.X →+ R, p = GlobalTheory.HeatMod.TorField.torTan ℓ ≫ Y.i := by
  intro R _ _ Q O _ _ _ oa Y p hp hq
  have hmono : ∀ {T : Over (Sp R)} (a b : T ⟶ splitTorus (Sp R) (RayEv.Chr Q)), a ≫ Y.i = b ≫ Y.i → a = b :=
    fun a b h => Y.isKernel.hom_ext h (toUnit_unique _ _)
  have hw : p ≫ Y.q = toUnit _ ≫ η[Q.P.A] := by rw [hq, Hom.one_def]
  let t := Y.isKernel.lift p (toUnit _) hw
  have ht : t ≫ Y.i = p := Y.isKernel.lift_fst _ _ _
  have := Y.i_linear.isMonHom
  have htan : Chart.spMap (Chart.fstD R) ≫ t = 1 := hmono _ _ (by
    rw [Category.assoc, ht, MonObj.one_comp]; exact (Chart.isTan_iff p).2 hp)
  let a : RayEv.Chr Q → DualNumber R := fun χ =>
    (Scheme.ΓSpecIso (CommRingCat.of (DualNumber R))).hom.hom ((coord t).hom (AddMonoidAlgebra.single χ 1))
  have hfst : ∀ χ, (a χ).fst = 1 := fun χ => by
    have e := congrArg (fun f => (coord f).hom (AddMonoidAlgebra.single χ 1)) htan
    simp only at e
    rw [coord_comp, Diag.coord_one, CommRingCat.hom_comp, RingHom.comp_apply, Chart.spMap_left] at e
    have nat := Scheme.ΓSpecIso_naturality (CommRingCat.ofHom (Chart.fstD R).toRingHom)
    have k := congrArg (fun f => f.hom ((coord t).hom (AddMonoidAlgebra.single χ 1))) nat
    simp only [CommRingCat.hom_comp, RingHom.comp_apply] at k
    rw [e, map_one] at k
    exact k.symm
  have h0 : a 0 = 1 := by
    show (Scheme.ΓSpecIso _).hom.hom ((coord t).hom (AddMonoidAlgebra.single 0 1)) = 1
    rw [Diag.coord_single_zero, map_one]
  have hadd : ∀ x y, a (x + y) = a x * a y := fun x y => by
    show (Scheme.ΓSpecIso _).hom.hom ((coord t).hom (AddMonoidAlgebra.single (x + y) 1)) = _
    rw [Diag.coord_single_add, map_mul]
  have hform : ∀ χ, a χ = 1 + inr (a χ).snd := fun χ => by
    ext
    · rw [hfst χ]; simp
    · simp
  let ℓ : Q.X →+ R :=
    { toFun := fun χ => (a χ).snd
      map_zero' := (congrArg TrivSqZeroExt.snd h0).trans TrivSqZeroExt.snd_one
      map_add' := fun x y => (congrArg TrivSqZeroExt.snd (hadd x y)).trans (by
        rw [hform x, hform y]
        simp only [mul_add, add_mul, _root_.one_mul, _root_.mul_one, TrivSqZeroExt.inr_mul_inr, add_zero,
          TrivSqZeroExt.snd_add, TrivSqZeroExt.snd_one, TrivSqZeroExt.snd_inr, zero_add]) }
  refine ⟨ℓ, ?_⟩
  rw [← ht]
  refine congrArg (· ≫ Y.i) (Diag.hom_ext fun χ => ?_)
  rw [torTan, Diag.coord_ofChar]
  show _ = (Scheme.ΓSpecIso (CommRingCat.of (DualNumber R))).inv.hom (1 + inr (a χ).snd)
  rw [← hform χ]
  show _ = (Scheme.ΓSpecIso (CommRingCat.of (DualNumber R))).inv.hom
    ((Scheme.ΓSpecIso (CommRingCat.of (DualNumber R))).hom.hom ((coord t).hom (AddMonoidAlgebra.single χ 1)))
  rw [← CommRingCat.comp_apply, Iso.hom_inv_id, CommRingCat.id_apply]

end GlobalTheory.HeatMod.TorField
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTranslatedTorusInvariantHeatOperator
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

open GlobalTheory.HeatTrans in

theorem GlobalTheory.HeatTrans.exists_heat_translate : ∀ (R : Type) [CommRing R] [IsDomain R] (Q : DegPre R) (O : Type) [CommRing O] [StarRing O] [Module O Q.X] (oa : Q.OAct O) (Y : Ray oa) (n : ℕ) (v : Fin n → TanM (𝟙 (Sp R)) Y.H) (dd : Fin n → Fld Y.H.left), (∀ a, IsInv Y.H (v a) (dd a)) → ∀ (D : Derivation ℤ R R) (h : Heat Y.H Y.q.left Q.P.L dd ⇑D), IsBasic Y h → ∀ (x : 𝟙_ (Over (Sp R)) ⟶ Y.H), ∃ h₁ : Heat Y.H ((𝟙 Y.H * (toUnit Y.H ≫ x)).left ≫ Y.q.left) Q.P.L dd ⇑D, h₁.Θ = h.Θ ∧ h₁.u = h.u ∧ (∀ i, (∃ V : Q.P.A.left.Opens, h₁.W i = Y.q.left ⁻¹ᵁ V) ∧ IsWt Y 0 _ (h₁.p i) ∧ IsWt Y 0 _ (h₁.p' i) ∧ ∀ (α : Q.X) (V : Q.P.A.left.Opens), Y.q.left ⁻¹ᵁ V ≤ h₁.W i → ∀ f, IsWt Y α (Y.q.left ⁻¹ᵁ V) f → IsWt Y α (Y.q.left ⁻¹ᵁ V) (h₁.d i _ f)) ∧ ∀ (k : ℕ) (τ τ' : SecM Y.q.left Q.P.L k) (σ σ' : SecM ((𝟙 Y.H * (toUnit Y.H ≫ x)).left ≫ Y.q.left) Q.P.L k), (∀ (Z : Scheme.{0}) (r : Z ⟶ Y.H.left) (z : Z) (J : (Z ⟶ Q.P.A.left) → Q.P.L.ι), Good Q.P.L z J → sval σ r z J = sval τ (r ≫ (𝟙 Y.H * (toUnit Y.H ≫ x)).left) z J) → (∀ (Z : Scheme.{0}) (r : Z ⟶ Y.H.left) (z : Z) (J : (Z ⟶ Q.P.A.left) → Q.P.L.ι), Good Q.P.L z J → sval σ' r z J = sval τ' (r ≫ (𝟙 Y.H * (toUnit Y.H ≫ x)).left) z J) → h.Acts k τ τ' → h₁.Acts k σ σ' := by
  intro R _ _ Q O _ _ _ oa Y n v dd hinv D h hB x
  have hTeq : (𝟙 Y.H * (toUnit Y.H ≫ x)).left = tr Y.H x := rfl
  rw [hTeq]
  have hTS := tr_tr_inv Y.H x
  have hST := tr_inv_tr Y.H x
  have hT := tr_hom Y.H x
  have hS := tr_hom Y.H x⁻¹
  set T := tr Y.H x with hTd
  set S := tr Y.H x⁻¹ with hSd
  have hdd : ∀ a (O O' : Y.H.left.Opens), O' ≤ T ⁻¹ᵁ O → ∀ f : Γ(Y.H.left, O),
      dd a O' (pbT T f O') = pbT T (dd a O f) O' := fun a => GlobalTheory.T.invariantVectorField_commutes_pointTranslation R Y.H (v a) (dd a) (hinv a) x
  have hpre : ∀ U : Y.H.left.Opens, S ⁻¹ᵁ (T ⁻¹ᵁ U) = U := fun U => by
    rw [← Scheme.Hom.comp_preimage, hST]; rfl
  have hpre' : ∀ U : Y.H.left.Opens, T ⁻¹ᵁ (S ⁻¹ᵁ U) = U := fun U => by
    rw [← Scheme.Hom.comp_preimage, hTS]; rfl
  refine ⟨⟨h.Θ, h.symm, h.u, h.J, (fun i => T ⁻¹ᵁ h.W i), h.j, (fun i => conjF T S (h.d i)),
    (fun i => pbT T (h.p i) (T ⁻¹ᵁ h.W i)), (fun i => pbT T (h.p' i) (T ⁻¹ᵁ h.W i)), ?_, ?_, ?_, ?_⟩, rfl, rfl, ?_, ?_⟩
  · refine top_le_iff.1 fun z _ => ?_
    have hz : T z ∈ ⨆ i, h.W i := h.cover ▸ trivial
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 hz
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨i, hi⟩
  · intro i
    rw [Scheme.Hom.comp_preimage]
    exact T.preimage_mono (h.le i)
  · intro i
    exact isLift_conjF Y.H D hTS hST hT hS (h.lift i)
  · intro k i i' O₁ hO f
    have hOi : O₁ ≤ T ⁻¹ᵁ h.W i := hO.trans inf_le_left
    have hOi' : O₁ ≤ T ⁻¹ᵁ h.W i' := hO.trans inf_le_right
    have hSO : S ⁻¹ᵁ O₁ ≤ h.W i ⊓ h.W i' :=
      le_inf ((S.preimage_mono hOi).trans (hpre _).le) ((S.preimage_mono hOi').trans (hpre _).le)
    have hg : S ⁻¹ᵁ O₁ ≤ Y.q.left ⁻¹ᵁ (Q.P.L.U (h.j i) ⊓ Q.P.L.U (h.j i')) :=
      le_inf (hSO.trans (inf_le_left.trans (h.le i))) (hSO.trans (inf_le_right.trans (h.le i')))
    have hg' : O₁ ≤ (T ≫ Y.q.left) ⁻¹ᵁ (Q.P.L.U (h.j i) ⊓ Q.P.L.U (h.j i')) := by
      rw [Scheme.Hom.comp_preimage, ← hpre' O₁]
      exact T.preimage_mono hg
    have hOO : O₁ ≤ T ⁻¹ᵁ (S ⁻¹ᵁ O₁) := (hpre' O₁).ge
    rw [op_conjF Y.H dd hTS hST hT hdd h.Θ h.u (h.d i) (h.p i) (h.p' i) k hOi,
      op_conjF Y.H dd hTS hST hT hdd h.Θ h.u (h.d i') (h.p i') (h.p' i') k hOi',
      GlobalTheory.KS.pbT_mul, pbT_pow S le_rfl _ _, pbT_pbT S (T ≫ Y.q.left) hg' le_rfl]
    have hSTq : S ≫ T ≫ Y.q.left = Y.q.left := by rw [← Category.assoc, hST, Category.id_comp]
    rw [hSTq, h.glue k i i' _ hSO, GlobalTheory.KS.pbT_mul, pbT_pow T hOO, pbT_pbT T Y.q.left hg hOO]
  · intro i
    obtain ⟨⟨V, hV⟩, hp, hp', hd⟩ := hB i
    refine ⟨?_, GlobalTheory.T.isRaynaudTorusWeight_pullback_pointTranslation R Q O oa Y x 0 _ _ le_rfl _ hp, GlobalTheory.T.isRaynaudTorusWeight_pullback_pointTranslation R Q O oa Y x 0 _ _ le_rfl _ hp', ?_⟩
    · exact ⟨_, (congrArg (T ⁻¹ᵁ ·) hV).trans (preimage_tr_q Y x V)⟩
    · intro α V₁ hV₁ f hf
      obtain ⟨V₂, hV₂⟩ : ∃ V₂, S ⁻¹ᵁ (Y.q.left ⁻¹ᵁ V₁) = Y.q.left ⁻¹ᵁ V₂ := ⟨_, preimage_tr_q Y x⁻¹ V₁⟩
      have hle : S ⁻¹ᵁ (Y.q.left ⁻¹ᵁ V₁) ≤ h.W i := (S.preimage_mono hV₁).trans (hpre _).le
      have hf' : IsWt Y α (S ⁻¹ᵁ (Y.q.left ⁻¹ᵁ V₁)) (pbT S f (S ⁻¹ᵁ (Y.q.left ⁻¹ᵁ V₁))) :=
        GlobalTheory.T.isRaynaudTorusWeight_pullback_pointTranslation R Q O oa Y x⁻¹ α _ _ le_rfl f hf
      have gen : ∀ (U : Y.H.left.Opens), U = Y.q.left ⁻¹ᵁ V₂ → ∀ g : Γ(Y.H.left, U), U ≤ h.W i → IsWt Y α U g →
          IsWt Y α U (h.d i U g) := by
        rintro U rfl g hU hg
        exact hd α V₂ hU g hg
      exact GlobalTheory.T.isRaynaudTorusWeight_pullback_pointTranslation R Q O oa Y x α _ _ (hpre' _).ge _ (gen _ hV₂ _ hle hf')
  · intro k τ τ' σ σ' hσ hσ' hA i
    have hW : S ⁻¹ᵁ (T ⁻¹ᵁ h.W i) ≤ h.W i := (hpre _).le
    show rsT (σ'.f fun _ => h.j i) (T ⁻¹ᵁ h.W i) = op Y.H dd h.Θ h.u (conjF T S (h.d i)) (pbT T (h.p i) (T ⁻¹ᵁ h.W i))
      (pbT T (h.p' i) (T ⁻¹ᵁ h.W i)) k (T ⁻¹ᵁ h.W i) (rsT (σ.f fun _ => h.j i) (T ⁻¹ᵁ h.W i))
    rw [GlobalTheory.T.chartFunction_rel_of_translate_section_values R Q O oa Y x k σ' τ' hσ' (h.j i) (h.W i) (h.le i), GlobalTheory.T.chartFunction_rel_of_translate_section_values R Q O oa Y x k σ τ hσ (h.j i) (h.W i) (h.le i),
      op_conjF Y.H dd hTS hST hT hdd h.Θ h.u (h.d i) (h.p i) (h.p' i) k (le_rfl : T ⁻¹ᵁ h.W i ≤ T ⁻¹ᵁ h.W i),
      pbT_pbT S T le_rfl le_rfl, hST, pbT_id hW,
      op_rsT Y.H dd (fun a => (hinv a).1) h.Θ h.u (h.d i) (h.lift i).1 (h.p i) (h.p' i) k hW le_rfl,
      GlobalTheory.KS.pbT_rsT T hW (hpre' _).ge, hA i]
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsVectorFieldPullbackBaseChangeDerivationStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_vectorField_pullback_baseChange_derivation : ∀ (Z Z' X X' : Scheme.{0}) (p : Z ⟶ X) (p' : Z' ⟶ X') (φ : Z' ⟶ Z) (g : X' ⟶ X), IsPullback φ p' p g → ∀ (U : X.affineOpens) (U' : X'.affineOpens) (hU : U'.1 ≤ g ⁻¹ᵁ U.1) (D : Derivation ℤ Γ(X, U.1) Γ(X, U.1)) (D' : Derivation ℤ Γ(X', U'.1) Γ(X', U'.1)), (∀ r, D' ((g.appLE U.1 U'.1 hU).hom r) = (g.appLE U.1 U'.1 hU).hom (D r)) → ∀ (W : Z.Opens) (hW : W ≤ p ⁻¹ᵁ U.1) (d : ∀ O : Z.Opens, Γ(Z, O) → Γ(Z, O)), IsField W d → (∀ r, d W ((p.appLE U.1 W hW).hom r) = (p.appLE U.1 W hW).hom (D r)) → ∃ d' : ∀ O : Z'.Opens, Γ(Z', O) → Γ(Z', O), IsField (φ ⁻¹ᵁ W ⊓ p' ⁻¹ᵁ U'.1) d' ∧ (∀ (O' : Z'.Opens) (h' : O' ≤ p' ⁻¹ᵁ U'.1), O' ≤ φ ⁻¹ᵁ W → ∀ r, d' O' ((p'.appLE U'.1 O' h').hom r) = (p'.appLE U'.1 O' h').hom (D' r)) ∧ ∀ (O : Z.Opens) (O' : Z'.Opens) (h : O' ≤ φ ⁻¹ᵁ O), O ≤ W → O' ≤ p' ⁻¹ᵁ U'.1 → ∀ f, d' O' ((φ.appLE O O' h).hom f) = (φ.appLE O O' h).hom (d O f) := by
  first | exact @GlobalTheory.FieldBC.exists_field_pullback | exact GlobalTheory.FieldBC.exists_field_pullback | (intros; apply GlobalTheory.FieldBC.exists_field_pullback <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsWeightPreservingLiftOfBaseDerivation
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.WtLift

variable {X A : Type} [AddCommGroup X] [CommRing A] (P : X → A → Prop)
  (hadd : ∀ χ a b, P χ a → P χ b → P χ (a + b)) (hzero : ∀ χ, P χ 0)
  (hmul : ∀ χ ψ a b, P χ a → P ψ b → P (χ + ψ) (a * b))
  (hdec : ∀ f : A, ∃! F : X →₀ A, (∀ χ, P χ (F χ)) ∧ f = F.sum (fun _ t => t))

include hdec in

def dec (f : A) : X →₀ A := (hdec f).exists.choose

include hdec in
theorem dec_spec (f : A) : (∀ χ, P χ (dec P hdec f χ)) ∧ f = (dec P hdec f).sum (fun _ t => t) :=
  (hdec f).exists.choose_spec

include hdec in
theorem dec_eq {f : A} {F : X →₀ A} (hF : ∀ χ, P χ (F χ)) (hs : f = F.sum (fun _ t => t)) : dec P hdec f = F :=
  (hdec f).unique (dec_spec P hdec f) ⟨hF, hs⟩

include hadd hdec in
theorem dec_add (a b : A) : dec P hdec (a + b) = dec P hdec a + dec P hdec b := by
  refine dec_eq P hdec (fun χ => ?_) ?_
  · rw [Finsupp.add_apply]; exact hadd _ _ _ ((dec_spec P hdec a).1 χ) ((dec_spec P hdec b).1 χ)
  · rw [Finsupp.sum_add_index' (fun _ => rfl) (fun _ _ _ => rfl), ← (dec_spec P hdec a).2, ← (dec_spec P hdec b).2]

include hzero hdec in
theorem dec_single {α : X} {f : A} (hf : P α f) : dec P hdec f = Finsupp.single α f := by
  classical
  refine dec_eq P hdec (fun χ => ?_) ?_
  · rw [Finsupp.single_apply]; split_ifs with h
    · exact h ▸ hf
    · exact hzero χ
  · rw [Finsupp.sum_single_index rfl]

include hzero hdec in
theorem dec_zero : dec P hdec (0 : A) = 0 := by
  rw [dec_single P hzero hdec (hzero 0), Finsupp.single_zero]

include hzero hmul hdec in
theorem dec_mul {χ : X} {f : A} (hf : P χ f) (h : A) (ψ : X) :
    dec P hdec (f * h) (χ + ψ) = f * dec P hdec h ψ := by
  set G : X →₀ A := Finsupp.mapDomain (fun ψ => χ + ψ) ((dec P hdec h).mapRange (f * ·) (mul_zero f)) with hG
  have hinj : Function.Injective (fun ψ : X => χ + ψ) := add_right_injective χ
  have hGv : ∀ ψ, G (χ + ψ) = f * dec P hdec h ψ := fun ψ => by
    rw [hG, Finsupp.mapDomain_apply hinj, Finsupp.mapRange_apply]
  have key : dec P hdec (f * h) = G := by
    refine dec_eq P hdec (fun ω => ?_) ?_
    · have e : ω = χ + (ω - χ) := by abel
      rw [e, hGv]; exact hmul _ _ _ _ hf ((dec_spec P hdec h).1 _)
    · rw [hG, Finsupp.sum_mapDomain_index (fun _ => rfl) (fun _ _ _ => rfl),
        Finsupp.sum_mapRange_index (fun _ => rfl), ← Finsupp.mul_sum, ← (dec_spec P hdec h).2]
  rw [key, hGv]

variable (δ₀ : A → A)

def proj (f : A) : A := (dec P hdec f).sum (fun χ t => dec P hdec (δ₀ t) χ)

include hadd hzero hdec in
theorem proj_add (h0 : ∀ a b, δ₀ (a + b) = δ₀ a + δ₀ b) (a b : A) :
    proj P hdec δ₀ (a + b) = proj P hdec δ₀ a + proj P hdec δ₀ b := by
  have hz : δ₀ 0 = 0 := by
    have := h0 0 0; simp only [add_zero] at this; exact left_eq_add.mp this
  unfold proj
  rw [dec_add P hadd hdec, Finsupp.sum_add_index']
  · intro χ; rw [hz, dec_zero P hzero hdec, Finsupp.zero_apply]
  · intro χ s t; rw [h0, dec_add P hadd hdec, Finsupp.add_apply]

include hzero hdec in
theorem proj_of_wt (hz : δ₀ 0 = 0) {α : X} {f : A} (hf : P α f) : proj P hdec δ₀ f = dec P hdec (δ₀ f) α := by
  unfold proj; rw [dec_single P hzero hdec hf, Finsupp.sum_single_index]
  rw [hz, dec_zero P hzero hdec]; rfl

include hzero hdec in

theorem induction_wt (Qp : A → Prop) (q0 : Qp 0) (qadd : ∀ a b, Qp a → Qp b → Qp (a + b))
    (qw : ∀ χ a, P χ a → Qp a) (f : A) : Qp f := by
  rw [(dec_spec P hdec f).2, Finsupp.sum]
  exact Finset.sum_induction _ Qp qadd q0 (fun χ _ => qw χ _ ((dec_spec P hdec f).1 χ))

include hadd hzero hmul hdec in
theorem proj_mul (h0 : ∀ a b, δ₀ (a + b) = δ₀ a + δ₀ b) (h1 : ∀ a b, δ₀ (a * b) = a * δ₀ b + b * δ₀ a) (a b : A) :
    proj P hdec δ₀ (a * b) = a * proj P hdec δ₀ b + b * proj P hdec δ₀ a := by
  have hz : δ₀ 0 = 0 := by
    have := h0 0 0; simp only [add_zero] at this; exact left_eq_add.mp this
  have pz : proj P hdec δ₀ 0 = 0 := by
    unfold proj; rw [dec_zero P hzero hdec, Finsupp.sum_zero_index]
  have hom : ∀ χ ψ x y, P χ x → P ψ y →
      proj P hdec δ₀ (x * y) = x * proj P hdec δ₀ y + y * proj P hdec δ₀ x := by
    intro χ ψ x y hx hy
    rw [proj_of_wt P hzero hdec δ₀ hz (hmul _ _ _ _ hx hy), proj_of_wt P hzero hdec δ₀ hz hy,
      proj_of_wt P hzero hdec δ₀ hz hx, h1, dec_add P hadd hdec, Finsupp.add_apply, dec_mul P hzero hmul hdec hx,
      add_comm χ ψ, dec_mul P hzero hmul hdec hy]
  have padd := proj_add P hadd hzero hdec δ₀ h0

  have step : ∀ ψ y, P ψ y → ∀ x, proj P hdec δ₀ (x * y) = x * proj P hdec δ₀ y + y * proj P hdec δ₀ x := by
    intro ψ y hy
    refine induction_wt P hzero hdec _ ?_ ?_ (fun χ x hx => hom χ ψ x y hx hy)
    · rw [zero_mul, pz, zero_mul, mul_zero, add_zero]
    · intro x x' ex ex'; rw [add_mul, padd, padd, ex, ex']; ring
  revert b
  intro b
  refine induction_wt P hzero hdec (fun y => proj P hdec δ₀ (a * y) = a * proj P hdec δ₀ y + y * proj P hdec δ₀ a)
    ?_ ?_ (fun ψ y hy => step ψ y hy a) b
  · simp only [mul_zero, pz, zero_mul, add_zero]
  · intro y y' ey ey'; rw [mul_add, padd, ey, ey', padd]; ring

include hzero hdec in
theorem proj_wt (hz : δ₀ 0 = 0) {α : X} {f : A} (hf : P α f) : P α (proj P hdec δ₀ f) := by
  rw [proj_of_wt P hzero hdec δ₀ hz hf]; exact (dec_spec P hdec _).1 α

end GlobalTheory.WtLift

namespace GlobalTheory.WtLift

theorem exists_isWt_lift : ∀ (R : Type) [CommRing R] [IsDomain R] (Q : DegPre R) (O : Type) [CommRing O] [StarRing O] [Module O Q.X] (oa : Q.OAct O) (Y : Ray oa) (V : Q.P.A.left.affineOpens) (D : Derivation ℤ R R) (δ₀ : Γ(Y.H.left, Y.q.left ⁻¹ᵁ V.1) → Γ(Y.H.left, Y.q.left ⁻¹ᵁ V.1)), (∀ a b, δ₀ (a + b) = δ₀ a + δ₀ b) → (∀ a b, δ₀ (a * b) = a * δ₀ b + b * δ₀ a) → (∀ r, δ₀ (constFn Y.H.hom _ r) = constFn Y.H.hom _ (D r)) → ∃ δ : Γ(Y.H.left, Y.q.left ⁻¹ᵁ V.1) → Γ(Y.H.left, Y.q.left ⁻¹ᵁ V.1), (∀ a b, δ (a + b) = δ a + δ b) ∧ (∀ a b, δ (a * b) = a * δ b + b * δ a) ∧ (∀ r, δ (constFn Y.H.hom _ r) = constFn Y.H.hom _ (D r)) ∧ ∀ (α : Q.X) f, IsWt Y α _ f → IsWt Y α _ (δ f) := by
  intro R _ _ Q O _ _ _ oa Y V D δ₀ h0 h1 hc
  have hadd : ∀ (χ : Q.X) (a b : Γ(Y.H.left, Y.q.left ⁻¹ᵁ V.1)), IsWt Y χ _ a → IsWt Y χ _ b → IsWt Y χ _ (a + b) :=
    fun χ a b ha hb => WtAlg.isWt_add ha hb
  have hzero : ∀ χ : Q.X, IsWt Y χ (Y.q.left ⁻¹ᵁ V.1) 0 := fun χ => WtAlg.isWt_zero (Y := Y) χ _
  have hmul : ∀ (χ ψ : Q.X) (a b : Γ(Y.H.left, Y.q.left ⁻¹ᵁ V.1)), IsWt Y χ _ a → IsWt Y ψ _ b →
      IsWt Y (χ + ψ) _ (a * b) :=
    fun χ ψ a b ha hb => GlobalTheory.T.isRaynaudTorusWeightFunction_mul R Q O oa Y _ χ ψ a b ha hb
  have hdec := GlobalTheory.T.existsUnique_weightDecomposition_raynaud_affine R Q O oa Y V.1 V.2
  have hz : δ₀ 0 = 0 := by
    have := h0 0 0; simp only [add_zero] at this; exact left_eq_add.mp this
  refine ⟨proj (fun χ f => IsWt Y χ _ f) hdec δ₀, proj_add _ hadd hzero hdec δ₀ h0,
    proj_mul _ hadd hzero hmul hdec δ₀ h0 h1, fun r => ?_, fun α f hf => proj_wt _ hzero hdec δ₀ hz hf⟩
  rw [proj_of_wt _ hzero hdec δ₀ hz (WtAlg.isWt_constFn (Y := Y) _ r), hc,
    dec_single _ hzero hdec (WtAlg.isWt_constFn (Y := Y) _ (D r)), Finsupp.single_eq_same]

end GlobalTheory.WtLift
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FactorPairingMumfordBundlePrincipalPolarisationStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.factorPairing_mumfordBundle_principal_polarisation : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D D' : DegData R (maximalIdeal R)) (F : Factor D.toPre D'.toPre) (_ : F.Alg) (A' : PolAV (Sp (FractionRing R))) (G' : Over (Sp R)) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ∀ (U' : Unif (maximalIdeal R) D' A' G') (oA : A'.OAct F.O) (oG : RingAct G' F.O), U'.toUnifPre.OLinear F.O F.o oA oG → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (inc : G ⟶ G') (pr : G' ⟶ G), IsMonHom inc → IsMonHom pr → inc ≫ pr = 𝟙 G → pr ≫ inc = oG.act F.e → ∃ (R' : Type) (_ : CommRing R') (_ : IsDomain R') (_ : IsLocalRing R') (ρ : R →+* R') (G₁ : Over (Sp R')) (_ : GrpObj G₁) (_ : IsCommMonObj G₁) (β : G₁.left ⟶ G.left) (β₂ : (G2 G₁).left ⟶ (G2 G).left) (A₁ : PolAV (Sp (FractionRing R'))) (gen₁ : (Over.pullback (jK R')).obj G₁ ≅ A₁.A), FinExt ρ ∧ IsGrpPullback G₁ G (spMap ρ) β ∧ Geo.Tor.IsSquare β β₂ ∧ IsMonHom gen₁.hom ∧ ExtLam G₁ (A₁.L.pull gen₁.hom.left) (((abelian₂ G' U'.LG.L).pull (lift (fst G G ≫ inc) (snd G G ≫ inc ≫ oG.act F.f) : G2 G ⟶ G2 G').left).pull β₂) := by
  first | exact @GlobalTheory.Mum.pairing_factor_mumford | exact GlobalTheory.Mum.pairing_factor_mumford | (intros; apply GlobalTheory.Mum.pairing_factor_mumford <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiltGraded
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.LowDat

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

def perp (D : Datum H) (Z : Submodule (𝓞 E) D.La) : Submodule (𝓞 E) D.La where
  carrier := {x | ∀ z ∈ Z, D.EF x z = 0}
  zero_mem' := by intro z _; simp
  add_mem' := by
    intro x y hx hy z hz
    show D.EF (x + y) z = 0
    rw [map_add, LinearMap.add_apply, hx z hz, hy z hz, add_zero]
  smul_mem' := by
    intro a x hx z hz
    show D.EF (a • x) z = 0
    rw [D.adj]
    exact hx _ (Z.smul_mem _ hz)

def IsIsoSat (D : Datum H) (Z : Submodule (𝓞 E) D.La) : Prop :=
  Z ≤ perp D Z ∧ ∀ (n : ℕ) (x : D.La), n ≠ 0 → n • x ∈ Z → x ∈ Z

def IsLower (D D' : Datum H) (Z : Submodule (𝓞 E) D.La) (f : perp D Z →ₗ[𝓞 E] D'.La) : Prop :=
  Function.Surjective f ∧ (∀ x, f x = 0 ↔ (x : D.La) ∈ Z) ∧ ∀ x y, D'.EF (f x) (f y) = D.EF x y

def lowLevel (l : Level H) : Level H :=
  { l with A := l.M', A_pos := Nat.lcm_pos (by have := l.three_le; omega) l.A_pos }

theorem ka_le (l : Level H) (c : Coeff l) : KA (lowLevel l) ≤ c.F := by
  unfold KA
  rw [IntermediateField.adjoin_le_iff]
  intro x hx
  rcases hx with rfl | hx
  · exact c.le (IntermediateField.subset_adjoin _ _ (by simp))
  · rw [Set.mem_singleton_iff] at hx; subst hx; exact c.zeta_mem

end GlobalTheory.LowDat

namespace GlobalTheory.LowDat

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R]

def lowS (C : UChart.Fam Xo c R) : Sp R ⟶ Sp (KA (lowLevel l)) :=
  spMap (C.b.comp (IntermediateField.inclusion (ka_le l c)).toRingHom)

def toF (C : UChart.Fam Xo c R) (F : Type) [Field F] [Algebra (FractionRing R) F] : c.F →+* F :=
  (algebraMap (FractionRing R) F).comp ((algebraMap R (FractionRing R)).comp C.b)

def XFLevel (C : UChart.Fam Xo c R) (tK : SAB H (Sp (FractionRing R))) (m1 : SABMap tK C.t (jK R))
    (m2 : SABMap tK Xo.univ.t (C.y ≫ pullback.fst _ _)) (F : Type) [Field F] [Algebra (FractionRing R) F]
    (I : letI := H.starRing; TateIsoQ Dw C.P.D.toPre C.P.oD F) : Prop :=
  ((I.ζ l.M' : Fˣ) : F) = toF C F ⟨zeta l.M', c.zeta_mem⟩ ∧
  ∀ (k : ℕ) (a : Dw.La) (σ : 𝟙_ (Over Xo.X) ⟶ Xo.univ.t.G),
    ((k = l.A ∧ σ = Xo.univ.etaA a) ∨
      (k = l.M ∧ a ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) Dw.La) ∧ σ = Xo.univ.eta a)) →
    ∀ x : TFK (R := R) F ⟶ C.P.A.A, C.P.ToA F k (I.ev k a) x →
      ∃ g : Sp F ⟶ tK.G.left, g ≫ m1.φ = x.left ≫ C.P.U.gen.inv.left ≫ pullback.fst C.t.G.hom (jK R) ∧
        g ≫ m2.φ = jFK (R := R) F ≫ C.y ≫ pullback.fst _ _ ≫ σ.left

def FiltGraded (C : UChart.Fam Xo c R) (Z : Submodule (𝓞 E) Dw.La) (F : Type) [Field F] [Algebra (FractionRing R) F]
    (I : letI := H.starRing; TateIsoQ Dw C.P.D.toPre C.P.oD F) : Prop :=
  ∀ n, 0 < n → ∀ a, (∃ q : QkPt C.P.D.toPre F n, QkPt.Equiv C.P.D.toPre F (I.ev n a) q ∧ q.y = 0) ↔
    ∃ b ∈ perp Dw Z, ∃ e, a = b + n • e

abbrev LowTate (C : UChart.Fam Xo c R) (D' : Datum H) (o' : Obj D' (lowLevel l) (baseKA (lowLevel l)) (lowS C))
    (F : Type) [Field F] [Algebra (FractionRing R) F] :=
  TateIso D' F (Over.mk (jFK (R := R) F ≫ jK R) ⟶ o'.t.G) (fun a g => g ≫ o'.t.act.act a)
    (fun n g g' z => Out.WeilIs o'.t.G o'.t.PP.L n g g' (unitOn z))

def LowGraded (C : UChart.Fam Xo c R) (Z : Submodule (𝓞 E) Dw.La) (D' : Datum H) (f : perp Dw Z →ₗ[𝓞 E] D'.La)
    (o' : Obj D' (lowLevel l) (baseKA (lowLevel l)) (lowS C)) (φB : o'.t.G.left ⟶ C.P.D.toPre.P.A.left)
    (F : Type) [Field F] [Algebra (FractionRing R) F]
    (I : letI := H.starRing; TateIsoQ Dw C.P.D.toPre C.P.oD F) (I' : LowTate C D' o' F) : Prop :=
  (∀ n, I'.ζ n = I.ζ n) ∧
  (∀ w, toUnit _ ≫ o'.etaA w = I'.ev (lowLevel l).A w) ∧
  (∀ w ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) D'.La), toUnit _ ≫ o'.eta w = I'.ev l.M w) ∧
  ∀ n, 0 < n → ∀ a : perp Dw Z, ∃ q : QkPt C.P.D.toPre F n,
    QkPt.Equiv C.P.D.toPre F (I.ev n a) q ∧ q.y = 0 ∧ q.g.b.left = (I'.ev n (f a)).left ≫ φB

end GlobalTheory.LowDat
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankTheoryMu
section
set_option autoImplicit false

noncomputable section

open CategoryTheory GlobalTheory.PDiv GlobalTheory.PDivGroup

namespace GlobalTheory.Dieu

def theory (p : ℕ) [Fact p.Prime] : Theory p :=
  let Bc := (GlobalTheory.T.exists_connected_dieudonne_functor_quasiLogarithms p).choose
  let Be := (GlobalTheory.T.exists_etaleDieudonneBase_by_cartierDuality p Bc).choose
  let hB := GlobalTheory.T.exists_dieudonneFunctor_glued_connected_etale p Bc Be (GlobalTheory.T.exists_connected_dieudonne_functor_quasiLogarithms p).choose_spec (GlobalTheory.T.exists_etaleDieudonneBase_by_cartierDuality p Bc).choose_spec
  let hV := GlobalTheory.T.exists_verschiebung_of_dieudonneFunctorBase p hB.choose
  { base := hB.choose, katz := hB.choose_spec.1, etDual := hB.choose_spec.2, V := hV.choose,
    F_V := hV.choose_spec.1, V_F := hV.choose_spec.2 }

end GlobalTheory.Dieu
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaloisPermutesWeightPartsUpToRootsStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.galois_permutes_weightParts_up_to_roots : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (Z : Scheme.{0}) (i : F.X ⟶ Z) (X₁ : Setup F W i), 1 ≤ g → 3 ≤ n → Odd n → IsOpenImmersion i → IsE8 W → ThetaInt F W i → IsProjOver X₁.M.s → ∀ (ε₁ : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)), IsDiagEnd F W X₁.ρ.P X₁.u ε₁ → ∀ (D : Deep X₁ ε₁) (z₁ : X₁.M.Z) (z₂ : D.X.M.Z), D.q z₂ = z₁ → ∃ U : X₁.S.HH X₁.M z₁ → D.X.Ω₁, (∀ κ, ∃ k : ℕ, 0 < k ∧ U κ ^ k = 1) ∧ ∀ σ : D.X.Ω₁ ≃ₐ[X₁.Ω₁] D.X.Ω₁, ∃ a : D.X.S.Gam ≃+ D.X.S.Gam, D.GalLab σ a ∧ (∀ x, a (D.lab x) = D.lab x) ∧ ((∀ x, a x ∈ D.X.S.HH D.X.M z₂ ↔ x ∈ D.X.S.HH D.X.M z₂) → ∀ b κ, σ (U κ * GSum.part D z₁ z₂ b κ) = U κ * GSum.part D z₁ z₂ (a b) κ) := by
  first | exact @GlobalTheory.Poinc.GalPart.exists_root_galois | exact GlobalTheory.Poinc.GalPart.exists_root_galois | (intros; apply GlobalTheory.Poinc.GalPart.exists_root_galois <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaloisTransportTorsionLabelsThetaSetupStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.galois_transport_torsion_labels_thetaSetup : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (Z : Scheme.{0}) (i : F.X ⟶ Z) (X₁ : Setup F W i), 1 ≤ g → 3 ≤ n → Odd n → IsOpenImmersion i → IsE8 W → ThetaInt F W i → IsProjOver X₁.M.s → ∀ (ε₁ : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)), IsDiagEnd F W X₁.ρ.P X₁.u ε₁ → ∀ (D : Deep X₁ ε₁) (σ : D.X.Ω₁ ≃ₐ[X₁.Ω₁] D.X.Ω₁) (s : D.X.M.Z ⟶ D.X.M.Z), D.X.M.pt ≫ s = spMap (σ : D.X.Ω₁ →+* D.X.Ω₁) ≫ D.X.M.pt → ∃ a : D.X.S.Gam ≃+ D.X.S.Gam, (∀ x, a (D.lab x) = D.lab x) ∧ ∀ (p : ℕ) [Fact p.Prime] (z₁ : X₁.M.Z) (c : CTrait X₁ p z₁) (y : Sp (OO p) ⟶ D.X.M.Z) (h : y ≫ D.q = c.y) (h' : (y ≫ s) ≫ D.q = c.y) (yy : D.X.S.Gam →+ ModN (D.X.S.r * D.X.S.N) (Fin 8 → c.T.D.toPre.X)), IsLab D.X D.ε (D.lift c y h) yy → IsLab D.X D.ε (D.lift c (y ≫ s) h') (yy.comp a.toAddMonoidHom) := by
  first | exact @GlobalTheory.Poinc.galTransport | exact GlobalTheory.Poinc.galTransport | (intros; apply GlobalTheory.Poinc.galTransport <;> assumption)
end

