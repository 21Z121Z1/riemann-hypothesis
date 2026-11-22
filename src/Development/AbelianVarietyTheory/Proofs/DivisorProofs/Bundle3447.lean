import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0073
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0089
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactificationBis
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianPartConst
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0044
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.InvariantFunctionsDescend
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0604
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RaynaudTorusWeightZeroInvariantFieldCoeffs
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3427
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0032
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0029
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0034
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2411
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0187
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3061
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3001
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0908
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2892
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3103
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3412
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2786
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2580
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2644
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0077
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2859
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0025
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0072
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsX
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NontrivialIsomClassInt
import Development.AbelianVarietyTheory.Definitions.Divisors.GenericPointAsIdeal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3414
import Development.AbelianVarietyTheory.Definitions.Divisors.SubsetSpanBy
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2497
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3418
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2478
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3421
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0392

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RaynaudCechRelationDlogDescendsToAbelianPart
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
namespace GlobalTheory.Heat.AbDescent

theorem pbT_id {X : Scheme.{0}} {U V : X.Opens} (hV : V ≤ U) (s : Γ(X, U)) : pbT (𝟙 X) s V = rsT s V := by
  rw [GlobalTheory.KS.pbT_of_le (𝟙 X) hV, GlobalTheory.KS.rsT_of_le hV]
  simp [Scheme.Hom.appLE, resG]
  rfl

theorem pbT_pbT_id {Z X : Scheme.{0}} (q : Z ⟶ X) {U V : X.Opens} (hV : V ≤ U) {W : Z.Opens} (hW : W ≤ q ⁻¹ᵁ V)
    (s : Γ(X, U)) : pbT q (pbT (𝟙 X) s V) W = pbT q s W := by
  rw [pbT_id hV, GlobalTheory.KS.pbT_rsT q hV hW]

theorem descent : ∀ (R : Type) [CommRing R] [IsDomain R] (Q : DegPre R) (O : Type) [CommRing O] [StarRing O] [Module O Q.X] (oa : Q.OAct O) (Y : Ray oa) (δH : Fld Y.H.left) (δ : Fld Q.P.A.left), (∀ (U : Q.P.A.left.Opens) (s : Γ(Q.P.A.left, U)) (W : Y.H.left.Opens), W ≤ Y.q.left ⁻¹ᵁ U → δH W (pbT Y.q.left s W) = pbT Y.q.left (δ U s) W) → ∀ (K : Type) (Wk : K → Y.H.left.Opens) (jk : K → Q.P.L.ι), (∀ k, ∃ V : Q.P.A.left.Opens, Wk k = Y.q.left ⁻¹ᵁ V) → ⨆ k, Wk k = ⊤ → (∀ k, Wk k ≤ Y.q.left ⁻¹ᵁ Q.P.L.U (jk k)) → ∀ (P : ∀ k, Γ(Y.H.left, Wk k)), (∀ k, IsWt Y 0 _ (P k)) → (∀ k k' (Wo : Y.H.left.Opens), Wo ≤ Wk k ⊓ Wk k' → rsT (P k') Wo - rsT (P k) Wo = dlg Y.H Y.q.left Q.P.L δH (jk k) (jk k') Wo) → ∃ (V : K → Q.P.A.left.Opens) (b : ∀ k, Γ(Q.P.A.left, V k)), ⨆ k, V k = ⊤ ∧ (∀ k, V k ≤ Q.P.L.U (jk k)) ∧ ∀ k k', rsT (b k') (V k ⊓ V k') - rsT (b k) (V k ⊓ V k') = dlg Q.P.A (𝟙 _) Q.P.L δ (jk k) (jk k') (V k ⊓ V k') := by
  intro R _ _ Q O _ _ _ oa Y δH δ hpb K Wk jk hV hcov hle P hP hrel
  have := Y.smooth_q
  have := (AbConst.surjective_q Y).1
  choose V hV using hV
  have hb : ∀ k, ∃ b : Γ(Q.P.A.left, V k), pbT Y.q.left b (Wk k) = P k := by
    intro k
    have key : ∀ (W : Y.H.left.Opens) (hW : W = Y.q.left ⁻¹ᵁ V k) (p : Γ(Y.H.left, W)), IsWt Y 0 W p →
        ∃ b : Γ(Q.P.A.left, V k), pbT Y.q.left b W = p := by
      intro W hW p hp
      subst hW
      obtain ⟨a, ha⟩ := AbConst.exists_app_eq Y hp
      exact ⟨a, by rw [GlobalTheory.KS.pbT_of_le _ le_rfl, ← ha, Scheme.Hom.app_eq_appLE]⟩
    exact key _ (hV k) _ (hP k)
  choose b hb using hb
  have hVle : ∀ k, V k ≤ Q.P.L.U (jk k) := by
    intro k y hy
    obtain ⟨x, rfl⟩ := Y.q.left.surjective y
    have hx : x ∈ Wk k := by rw [hV k]; exact hy
    exact hle k hx
  refine ⟨V, b, ?_, hVle, ?_⟩
  · rw [eq_top_iff]
    intro y _
    obtain ⟨x, rfl⟩ := Y.q.left.surjective y
    have hx : x ∈ ⨆ k, Wk k := by rw [hcov]; trivial
    rw [TopologicalSpace.Opens.mem_iSup] at hx ⊢
    obtain ⟨k, hk⟩ := hx
    exact ⟨k, by rw [hV k] at hk; exact hk⟩
  · intro k k'
    have hWo : Y.q.left ⁻¹ᵁ (V k ⊓ V k') ≤ Wk k ⊓ Wk k' := by
      rw [hV k, hV k']
      exact fun x hx => ⟨hx.1, hx.2⟩
    have h := hrel k k' _ hWo
    apply FunDescent.app_injective Y.q.left (V k ⊓ V k')
    have e : ∀ s : Γ(Q.P.A.left, V k ⊓ V k'),
        (Y.q.left.app (V k ⊓ V k')).hom s = pbT Y.q.left s (Y.q.left ⁻¹ᵁ (V k ⊓ V k')) := fun s => by
      rw [GlobalTheory.KS.pbT_of_le _ le_rfl, Scheme.Hom.app_eq_appLE]
    rw [e, e, GlobalTheory.KS.pbT_sub, GlobalTheory.KS.pbT_rsT _ inf_le_right le_rfl, GlobalTheory.KS.pbT_rsT _ inf_le_left le_rfl]
    have hbk : ∀ j, Y.q.left ⁻¹ᵁ (V k ⊓ V k') ≤ Wk j →
        pbT Y.q.left (b j) (Y.q.left ⁻¹ᵁ (V k ⊓ V k')) = rsT (P j) (Y.q.left ⁻¹ᵁ (V k ⊓ V k')) := by
      intro j hj
      rw [← hb j, GlobalTheory.KS.rsT_pbT _ (hV j).le hj]
    rw [hbk k' (hWo.trans inf_le_right), hbk k (hWo.trans inf_le_left), h]
    have hUo : V k ⊓ V k' ≤ Q.P.L.U (jk k) ⊓ Q.P.L.U (jk k') := inf_le_inf (hVle k) (hVle k')
    unfold dlg
    rw [GlobalTheory.KS.pbT_mul, ← hpb (V k ⊓ V k') (pbT (𝟙 _) (Q.P.L.g (jk k) (jk k')).val (V k ⊓ V k')) _ le_rfl,
      pbT_pbT_id _ hUo le_rfl, pbT_pbT_id _ hUo le_rfl]

end GlobalTheory.Heat.AbDescent
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RaynaudTorusWeightZeroInvariantFieldCoeffsStatement
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
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.raynaudTorusWeight_zero_invariantField_coeffs : ∀ (R : Type) [CommRing R] [IsDomain R] (Q : DegPre R) (O : Type) [CommRing O] [StarRing O] [Module O Q.X] (oa : Q.OAct O) (Y : Ray oa) (n : ℕ) (v : Module.Basis (Fin n) R (TanM (𝟙 (Sp R)) Y.H)) (dd : Fin n → Fld Y.H.left), (∀ a, IsInv Y.H (v a) (dd a)) →
    ∀ (V : Q.P.A.left.Opens) (δ : Fld Y.H.left), IsField (Y.q.left ⁻¹ᵁ V) δ → (∀ O, O ≤ Y.q.left ⁻¹ᵁ V → ∀ r, δ O (constFn Y.H.hom O r) = 0) →
    (∀ (α : Q.X) (V' : Q.P.A.left.Opens), V' ≤ V → ∀ f, IsWt Y α (Y.q.left ⁻¹ᵁ V') f → IsWt Y α (Y.q.left ⁻¹ᵁ V') (δ _ f)) →
    ∀ c : Fin n → Γ(Y.H.left, Y.q.left ⁻¹ᵁ V), (∀ O, O ≤ Y.q.left ⁻¹ᵁ V → ∀ f, δ O f = ∑ a, rsT (c a) O * dd a O f) →
    ∀ a, IsWt Y 0 _ (c a) := by
  first | exact @GlobalTheory.Heat.CoeffWt.isWt_coeff | exact GlobalTheory.Heat.CoeffWt.isWt_coeff | (intros; apply GlobalTheory.Heat.CoeffWt.isWt_coeff <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RaynaudWeightZeroCompatibleFunctionsEqBaseConsta
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

namespace GlobalTheory.Heat.AbConstGlob

open GlobalTheory.KS.GlueDer

variable {R : Type} [CommRing R] [IsDomain R] {Q : DegPre R} {O : Type} [CommRing O] [StarRing O] [Module O Q.X]
  {oa : Q.OAct O} (Y : Ray oa)

theorem app_rsT {U V : Q.P.A.left.Opens} (h : V ≤ U) (a : Γ(Q.P.A.left, U)) :
    (Y.q.left.app V).hom (rsT a V) = rsT ((Y.q.left.app U).hom a) (Y.q.left ⁻¹ᵁ V) := by
  rw [rsT_eq h, rsT_eq (pre_mono _ h), res_app]

theorem app_constFn (V : Q.P.A.left.Opens) (r : R) :
    (Y.q.left.app V).hom (constFn Q.P.A.hom V r) = constFn Y.H.hom _ r :=
  app_const (RingHom.id R) Q.P.A.hom Y.H.hom Y.q.left
    ((Over.w Y.q).trans ((Category.comp_id _).symm.trans (congrArg (Y.H.hom ≫ ·) (Spec.map_id _).symm))) V r

theorem exists_constFn_top (t : Γ(Q.P.A.left, ⊤)) : ∃ r : R, t = constFn Q.P.A.hom ⊤ r := by
  obtain ⟨s, rfl⟩ := (GlobalTheory.allSixLaws.1.globalFns (Sp R) Q.P.A Q.P.isAb).2 t
  refine ⟨(Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom s, ?_⟩
  simp only [constFn]
  rw [Iso.hom_inv_id_apply, Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]
  rfl

theorem exists_const_of_preimage [IsLocalRing R] [IsNoetherianRing R] {K : Type} (V : K → Q.P.A.left.Opens)
    (hc : ⨆ k, Y.q.left ⁻¹ᵁ V k = ⊤) (F : ∀ k, Γ(Y.H.left, Y.q.left ⁻¹ᵁ V k)) (hF : ∀ k, IsWt Y 0 _ (F k))
    (hag : ∀ k k' (Wo : Y.H.left.Opens), Wo ≤ Y.q.left ⁻¹ᵁ V k ⊓ Y.q.left ⁻¹ᵁ V k' →
      rsT (F k) Wo = rsT (F k') Wo) :
    ∃ r : R, ∀ k, F k = constFn Y.H.hom _ r := by
  have := Y.smooth_q
  have := (GlobalTheory.Heat.AbConst.surjective_q Y).1
  have inj := FunDescent.app_injective Y.q.left
  choose a ha using fun k => GlobalTheory.Heat.AbConst.exists_app_eq Y (hF k)
  have cov : (⊤ : Q.P.A.left.Opens) ≤ ⨆ k, V k := by
    intro y _
    obtain ⟨x, rfl⟩ := Y.q.left.surjective y
    have hx : x ∈ ⨆ k, Y.q.left ⁻¹ᵁ V k := by rw [hc]; trivial
    obtain ⟨k, hk⟩ := TopologicalSpace.Opens.mem_iSup.1 hx
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨k, hk⟩
  obtain ⟨t, ht⟩ := GlobalTheory.KS.exists_rsT_eq V (O := ⊤) (fun _ => le_top) cov a fun k l => by
    apply inj
    rw [app_rsT Y inf_le_left, app_rsT Y inf_le_right, ha, ha]
    exact hag k l _ (le_inf (pre_mono _ inf_le_left) (pre_mono _ inf_le_right))
  obtain ⟨r, rfl⟩ := exists_constFn_top t
  refine ⟨r, fun k => ?_⟩
  rw [← ha, ← ht k, GlobalTheory.KS.rsT_constFn _ le_top, app_constFn]

end GlobalTheory.Heat.AbConstGlob

open GlobalTheory.Heat.AbConstGlob in
theorem GlobalTheory.Heat.AbConstGlob.main : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] (Q : DegPre R) (O : Type) [CommRing O] [StarRing O] [Module O Q.X] (oa : Q.OAct O) (Y : Ray oa) (K : Type) (Wk : K → Y.H.left.Opens), (∀ k, ∃ V : Q.P.A.left.Opens, Wk k = Y.q.left ⁻¹ᵁ V) → ⨆ k, Wk k = ⊤ → ∀ F : ∀ k, Γ(Y.H.left, Wk k), (∀ k, IsWt Y 0 _ (F k)) → (∀ k k' (Wo : Y.H.left.Opens), Wo ≤ Wk k ⊓ Wk k' → rsT (F k) Wo = rsT (F k') Wo) → ∃ r : R, ∀ k, F k = constFn Y.H.hom _ r := by
  intro R _ _ _ _ Q O _ _ _ oa Y K Wk hW hc F hF hag
  choose V hV using hW
  obtain rfl : Wk = fun k => Y.q.left ⁻¹ᵁ V k := funext hV
  exact exists_const_of_preimage Y V hc F hF hag
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RepresentingSchemeOfFiniteSurjectiveLiftStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.representingScheme_of_finite_surjective_lift : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (A : Over (Sp R)) [GrpObj A] (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → ∀ (B S' : Over (Sp R)) (b : B ⟶ S') (P : LB (A ⊗ B).left), IsFinite S'.hom → Surjective S'.hom → Rep A b P → GlobalTheory.DualCon.Good g b.left → (∀ x : B.left, LiftAt A g b P x) → HasRep A g (𝟙_ _) := by
  first | exact @GlobalTheory.DualCon.hasRep_of_liftAt | exact GlobalTheory.DualCon.hasRep_of_liftAt | (intros; apply GlobalTheory.DualCon.hasRep_of_liftAt <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RosatiAdjointIffBiextensionPullbacksIsomorphic
section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PELU
open scoped Matrix
open GlobalTheory.UPel.HT

namespace GlobalTheory.RosatiFormAdj

theorem real_eq_of_exp {p : ℤ} {r : ℝ}
    (h : ∀ n : ℕ, 0 < n → Complex.exp (-(2 * Real.pi * Complex.I) * (p : ℂ) / n) =
      Complex.exp (-(2 * Real.pi * Complex.I) * (r : ℂ) / n)) : (p : ℝ) = r := by
  have h1 := h 1 one_pos
  simp only [Nat.cast_one, div_one] at h1
  obtain ⟨m, hm⟩ := Complex.exp_eq_exp_iff_exists_int.1 h1
  have hr : (r : ℂ) = ((p + m : ℤ) : ℂ) := by
    have := Complex.two_pi_I_ne_zero
    push_cast
    apply mul_left_cancel₀ this
    linear_combination hm
  have hr' : r = ((p + m : ℤ) : ℝ) := by exact_mod_cast hr
  have := GlobalTheory.HermAdjoint.int_eq_of_exp (p := p) (q := p + m) (fun n hn => by rw [h n hn, hr])
  rw [hr', ← this]

theorem lbIso_pull_iff_adjoint : ∀ (A : Over (Sp ℂ)) [GrpObj A] [IsCommMonObj A] (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → ∀ P : LB (G2 A).left, P.IsLB → (∃ t : (P.pull (lift (1 : A ⟶ A) (𝟙 A)).left).Gen, t.IsGen) → (∃ t : (P.pull (lift (𝟙 A) (1 : A ⟶ A)).left).Gen, t.IsGen) → LBIso P (P.pull (lift (snd A A) (fst A A)).left) → Out.RelAmple A (P.pull (lift (𝟙 A) (𝟙 A)).left) → ∀ (e : (Fin g → ℂ) → (Over.mk (𝟙 (Sp ℂ)) ⟶ A)) (La : Type) [AddCommGroup La] (Q : La →+ (Fin g → ℂ)) (EF : LinearMap.BilinForm ℤ La), IsExp (𝟙 (Sp ℂ)) e → Function.Injective Q → (∀ z, e z = 1 ↔ z ∈ Q.range) → (∀ (k : ℕ) (a b : La) (c : ℂˣ), 0 < k → (c : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * (EF a b : ℂ) / k) → Out.WeilIs A (P.pull (lift (𝟙 A) (𝟙 A)).left) k (e ((k : ℂ)⁻¹ • Q a)) (e ((k : ℂ)⁻¹ • Q b)) (unitOn c)) → ∀ (f f' : A ⟶ A) (u u' : La →+ La), IsMonHom f → IsMonHom f' → (∀ (k : ℕ) x, 0 < k → e ((k : ℂ)⁻¹ • Q (u x)) = e ((k : ℂ)⁻¹ • Q x) ≫ f) → (∀ (k : ℕ) x, 0 < k → e ((k : ℂ)⁻¹ • Q (u' x)) = e ((k : ℂ)⁻¹ • Q x) ≫ f') → (LBIso (P.pull (lift (fst A A ≫ f) (snd A A)).left) (P.pull (lift (fst A A) (snd A A ≫ f')).left) ↔ ∀ x y, EF (u x) y = EF x (u' y)) := by
  intro A _ _ g hA hg P hP h1 h2 hsym hamp e La _ Q EF he hQ hker hW f f' u u' hf hf' hu hu'
  obtain ⟨M, hM, hPM⟩ := GlobalTheory.T.exists_mumford_bundle_iso_symmetric_birigidified_complex A g hA hg P hP h1 h2 hsym
  obtain ⟨v, Hm, χ, hve, hAH⟩ := GlobalTheory.T.exists_appellHumbertFrame_of_exponential A g hA hg e he M hM
  have hN : (P.pull (lift (𝟙 A) (𝟙 A)).left).IsLB := pull_isLB hP _
  have hND := GlobalTheory.T.lineBundleIso_pullback_pair_of_lambdaBundle_iso A P M hP hM hPM A (𝟙 A) (𝟙 A)
  have hmem : ∀ z, z ∈ v.Λ ↔ z ∈ Q.range := fun z => (v.ker z).symm.trans (by rw [hve]; exact hker z)
  have hEF : ∀ a b, (EF a b : ℝ) = 2 * (hermForm Hm (Q a) (Q b)).im := by
    intro a b
    apply real_eq_of_exp
    intro k hk
    have hc := Complex.exp_ne_zero (-(2 * Real.pi * Complex.I) * (EF a b : ℂ) / k)
    have hc' := Complex.exp_ne_zero (-(2 * Real.pi * Complex.I) * (((2 * (hermForm Hm (Q a) (Q b)).im : ℝ)) : ℂ) / k)
    have w1 := hW k a b (Units.mk0 _ hc) hk rfl
    have w2 := GlobalTheory.T.commutator_pairing_diagonal_mumford_bundle A g hA hg M v Hm χ hM hAH _ hN hND hamp k (Q a) (Q b) (Units.mk0 _ hc') hk
      ((hmem _).2 ⟨a, rfl⟩) ((hmem _).2 ⟨b, rfl⟩) rfl
    rw [hve, hve] at w2
    exact congrArg Units.val (GlobalTheory.T.weilPairing_complex_value_unique (Sp ℂ) A g hA hg _ hN (𝟙 (Sp ℂ)) k _ _ _ _ w1 w2)
  obtain ⟨F, hF, -⟩ := GlobalTheory.T.existsUnique_linear_lift_of_abelianEndomorphism (Sp ℂ) A g hA hg (𝟙 (Sp ℂ)) e e f he he hf
  obtain ⟨F', hF', -⟩ := GlobalTheory.T.existsUnique_linear_lift_of_abelianEndomorphism (Sp ℂ) A g hA hg (𝟙 (Sp ℂ)) e e f' he he hf'
  have hlift : ∀ (G : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)) (φ : A ⟶ A) (w : La →+ La), (∀ z, e (G z) = e z ≫ φ) →
      (∀ (k : ℕ) x, 0 < k → e ((k : ℂ)⁻¹ • Q (w x)) = e ((k : ℂ)⁻¹ • Q x) ≫ φ) → ∀ x, G (Q x) = Q (w x) := by
    intro G φ w hG hw x
    refine sub_eq_zero.1 (GlobalTheory.T.eq_zero_of_inv_nat_smul_mem_discrete_submodule g v.Λ v.discrete (G (Q x) - Q (w x)) fun k hk => ?_)
    refine (hmem _).2 ((hker _).1 ?_)
    have e1 : e ((k : ℂ)⁻¹ • G (Q x)) = e ((k : ℂ)⁻¹ • Q (w x)) := by
      rw [← map_smul, hG, hw k x hk]
    have e2 := he.1 ((k : ℂ)⁻¹ • (G (Q x) - Q (w x))) ((k : ℂ)⁻¹ • Q (w x))
    rw [← smul_add, sub_add_cancel, e1] at e2
    exact mul_eq_right.1 e2.symm
  have hFQ := hlift F f u hF hu
  have hFQ' := hlift F' f' u' hF' hu'
  have hvF : ∀ z, v.ex (F z) = v.ex z ≫ f := fun z => by rw [hve, hve]; exact hF z
  have hvF' : ∀ z, v.ex (F' z) = v.ex z ≫ f' := fun z => by rw [hve, hve]; exact hF' z
  have hisoL := GlobalTheory.T.lineBundleIso_pullback_pair_of_lambdaBundle_iso A P M hP hM hPM (A ⊗ A) (fst A A ≫ f) (snd A A)
  have hisoR := GlobalTheory.T.lineBundleIso_pullback_pair_of_lambdaBundle_iso A P M hP hM hPM (A ⊗ A) (fst A A) (snd A A ≫ f')
  have hcl : ∀ (a b : A ⊗ A ⟶ A), (cubeLB A ![a, b] M).IsLB := fun a b => LB.isLB_linComb hM _ _
  have key : LBIso (P.pull (lift (fst A A ≫ f) (snd A A)).left) (P.pull (lift (fst A A) (snd A A ≫ f')).left) ↔
      LBIso (cubeLB A ![fst A A ≫ f, snd A A] M) (cubeLB A ![fst A A, snd A A ≫ f'] M) := by
    constructor
    · intro h
      exact LBIso.trans (hcl _ _) (pull_isLB hP _) (hcl _ _) hisoL.symm
        (LBIso.trans (pull_isLB hP _) (pull_isLB hP _) (hcl _ _) h hisoR)
    · intro h
      exact LBIso.trans (pull_isLB hP _) (hcl _ _) (pull_isLB hP _) hisoL
        (LBIso.trans (hcl _ _) (hcl _ _) (pull_isLB hP _) h hisoR.symm)
  rw [key]
  constructor
  · intro h x y
    have := GlobalTheory.T.adjoint_appellHumbertForm_of_mumfordBundle_lbIso A g hA hg _ hN hamp M v Hm χ hM hAH f f' F F' hf hf' hvF hvF' h (Q x) (Q y)
    have hh : ((EF (u x) y : ℤ) : ℝ) = ((EF x (u' y) : ℤ) : ℝ) := by
      rw [hEF, hEF, ← hFQ, ← hFQ', this]
    exact_mod_cast hh
  · intro h
    apply GlobalTheory.T.cubeLineBundle_iso_of_appellHumbert_adjoint A g hA hg _ hN hamp M v Hm χ hM hAH f f' F F' hf hf' hvF hvF'
    refine GlobalTheory.HermAdjoint.adjoint_of_im Hm F F' _ v.full fun a ha b hb => ?_
    obtain ⟨x, rfl⟩ := (hmem a).1 ha
    obtain ⟨y, rfl⟩ := (hmem b).1 hb
    have h1 := hEF (u x) y
    have h2 := hEF x (u' y)
    have h3 : ((EF (u x) y : ℤ) : ℝ) = ((EF x (u' y) : ℤ) : ℝ) := by rw [h x y]
    rw [hFQ, hFQ']
    linarith

end GlobalTheory.RosatiFormAdj
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SamePolarisedDataUniformiseFiniteExtensionStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.samePolarisedData_uniformise_finite_extension : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D₀ : DegData R (maximalIdeal R)), ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ U : Unif (maximalIdeal R) D A G, SamePol D₀.toPre D.toPre → ∃ (R' : Type) (_ : CommRing R') (_ : IsDomain R') (_ : IsLocalRing R') (ρ : R →+* R') (D₁ : DegData R' (maximalIdeal R')) (G₁ : Over (Sp R')) (_ : GrpObj G₁) (_ : IsCommMonObj G₁) (β : G₁.left ⟶ G.left) (β₂ : (G2 G₁).left ⟶ (G2 G).left) (A₁ : PolAV (Sp (FractionRing R'))) (U₁ : Unif (maximalIdeal R') D₁ A₁ G₁), FinExt ρ ∧ Nonempty (IsPullDeg ρ D₀.toPre D₁.toPre) ∧ IsGrpPullback G₁ G (spMap ρ) β ∧ Geo.Tor.IsSquare β β₂ ∧ LBIso (abelian₂ G₁ U₁.LG.L) ((abelian₂ G U.LG.L).pull β₂) := by
  first | exact @GlobalTheory.Mum.samePol_unif_finExt | exact GlobalTheory.Mum.samePol_unif_finExt | (intros; apply GlobalTheory.Mum.samePol_unif_finExt <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SelfIntersectionContinuousLimit
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry MvPolynomial Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.HermLB GlobalTheory.CxPts GlobalTheory.MetFam GlobalTheory.Published

namespace GlobalTheory.SelfCont

theorem tendsto_zero_of_pow {ι α : Type} [Fintype ι] {l : Filter α} (d : ℕ) (Φ : α → MvPolynomial ι ℝ →ₗ[ℝ] ℝ)
    (h : ∀ n : ι → ℤ, Tendsto (fun R => Φ R (lin (fun i => (n i : ℝ)) ^ d)) l (𝓝 0))
    (h' : ∀ (P : MvPolynomial ι ℝ) (e : ℕ), e ≠ d → P.IsHomogeneous e → ∀ R, Φ R P = 0) (P : MvPolynomial ι ℝ) :
    Tendsto (fun R => Φ R P) l (𝓝 0) := by
  let S : Submodule ℝ (MvPolynomial ι ℝ) :=
    { carrier := {P | Tendsto (fun R => Φ R P) l (𝓝 0)}
      add_mem' := fun {a b} ha hb => by simpa using Tendsto.add ha hb
      zero_mem' := by simpa using tendsto_const_nhds
      smul_mem' := fun c a ha => by simpa using Tendsto.const_mul c ha }
  by_contra hP
  obtain ⟨f, hf, hS⟩ := S.exists_le_ker_of_lt_top (lt_top_iff_ne_top.2 fun e => hP (show P ∈ S from e ▸ trivial))
  exact hf (Model.eq_zero_of_pow d f (fun n => hS (h n)) fun Q e he hQ =>
    hS (show Tendsto _ _ _ by simpa only [h' Q e he hQ] using tendsto_const_nhds))

variable {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k}

theorem icls_fnB_add {u v w : ∀ σ : k →+* ℂ, CxPts p σ → ℝ} (hu hc hv hd hw he) (e : ∀ σ y, w σ y = u σ y + v σ y) :
    (fnB w hw he).icls = (fnB u hu hc).icls + (fnB v hv hd).icls := by
  rw [← icls_tens, icls_eq_iff.2 (isometric_tens_fnB _ v hv hd)]
  exact icls_eq_iff.2 (isometric_of_eqOn fun σ _ y _ => (e σ y).symm)

theorem isConj_mul {u : ∀ σ : k →+* ℂ, CxPts p σ → ℝ}
    (hc : ∀ σ σ', (Weight.ofFun (u σ)).IsConj (Weight.ofFun (u σ'))) (c : ℝ) (σ σ' : k →+* ℂ) :
    (Weight.ofFun fun y => c * u σ y).IsConj (Weight.ofFun fun y => c * u σ' y) :=
  fun i y y' h hy => congrArg (c * ·) (hc σ σ' i y y' h hy)

theorem icls_fnB_mul {u : ∀ σ : k →+* ℂ, CxPts p σ → ℝ} (hu : ∀ σ y, CInfAt (u σ) y)
    (hc : ∀ σ σ', (Weight.ofFun (u σ)).IsConj (Weight.ofFun (u σ'))) (n : ℤ) :
    (fnB (fun σ y => (n : ℝ) * u σ y) (fun σ y => (hu σ y).const_mul _) (isConj_mul hc _)).icls =
      n • (fnB u hu hc).icls := by
  have key (m : ℤ) := icls_fnB_add (p := p) (w := fun σ y => ((m + 1 : ℤ) : ℝ) * u σ y) (u := fun σ y => (m : ℝ) * u σ y)
    (fun σ y => (hu σ y).const_mul _) (isConj_mul hc _) hu hc (fun σ y => (hu σ y).const_mul _) (isConj_mul hc _)
    fun σ y => by push_cast; ring
  induction n using Int.induction_on with
  | zero =>
    have := icls_fnB_add (p := p) (w := u) (u := fun σ y => ((0 : ℤ) : ℝ) * u σ y)
      (fun σ y => (hu σ y).const_mul _) (isConj_mul hc _) hu hc hu hc fun σ y => by push_cast; ring
    rw [zero_smul]
    exact right_eq_add.1 this
  | succ n ih => rw [key, ih, add_smul, one_smul]
  | pred n ih =>
    have := key (-(n : ℤ) - 1)
    simp only [sub_add_cancel] at this
    rw [sub_smul, one_smul, ← ih, this, add_sub_cancel_right]

theorem tendsto_integral_zero {α β : Type} [MeasurableSpace β] {l : Filter α} {u : α → β → ℝ} {μ : α → Measure β}
    (hu : TendstoUniformly u (fun _ => 0) l) {C : NNReal} (hC : ∀ᶠ R in l, μ R Set.univ ≤ (C : ENNReal)) :
    Tendsto (fun R => ∫ y, u R y ∂μ R) l (𝓝 0) := by
  refine Metric.tendsto_nhds.2 fun ε hε => ?_
  have h1 : (0 : ℝ) < C + 1 := by positivity
  filter_upwards [hC, Metric.tendstoUniformly_iff.1 hu _ (div_pos hε h1)] with R h₁ h₂
  have : IsFiniteMeasure (μ R) := ⟨h₁.trans_lt ENNReal.coe_lt_top⟩
  have h₃ : (μ R).real Set.univ ≤ C := ENNReal.toReal_le_coe_of_le_coe h₁
  rw [dist_zero_right]
  refine (norm_integral_le_of_norm_le_const (C := ε / (C + 1)) (.of_forall fun y => ?_)).trans_lt ?_
  · simpa only [dist_zero_left] using (h₂ y).le
  · calc ε / (C + 1) * (μ R).real Set.univ < ε / (C + 1) * (C + 1) :=
          mul_lt_mul_of_pos_left (by linarith) (div_pos hε h1)
      _ = ε := div_mul_cancel₀ _ h1.ne'

variable [IsIntegral X] {D : ℕ} {t : ℝ → ℝ} {u : ℝ → ∀ σ : k →+* ℂ, CxPts p σ → ℝ}

theorem tendsto_chInt (hX : IsArithVar p D) (hs : GenSmooth p D) (ht : Tendsto t atTop (𝓝 0))
    (hu : ∀ R σ y, CInfAt (u R σ) y) (hc : ∀ R σ σ', (Weight.ofFun (u R σ)).IsConj (Weight.ofFun (u R σ')))
    (hf : ∀ σ y, FamAt t (fun R => u R σ) (fun _ => 0) y) (N : HermLB p) (c : ℝ) :
    Tendsto (fun R => chInt (N.raise (fun σ y => c * u R σ y) (fun σ y => (hu R σ y).const_mul _) (isConj_mul (hc R) _))
      D (u R)) atTop (𝓝 0) := by
  have := hX.finite_emb
  have := Fintype.ofFinite (k →+* ℂ)
  simp only [chInt, finsum_eq_sum_of_fintype, Weight.chernInt, Measure.restrict_univ]
  rw [← Finset.sum_const_zero (s := (Finset.univ : Finset (k →+* ℂ))), ← sub_zero (0 : ℝ)]
  refine tendsto_finsetSum _ fun σ _ => ?_
  have := hX.compactSpace σ
  have hU := tendstoUniformly_of_famAt ht (hf σ)
  obtain ⟨C, hC⟩ := T.chern_part_uniform_bound k X p D hX hs t ht σ N.B (N.φ σ) (N.cInf σ) (fun R y => c * u R σ y)
    (fun R y => (hu R σ y).const_mul _) fun y => by
      simpa only [mul_zero] using (hf σ y).comp_contDiff (Ψ := fun x : ℝ => c * x) (contDiff_const.mul contDiff_id)
  exact (tendsto_integral_zero hU (hC.mono fun R h => h 1)).sub (tendsto_integral_zero hU (hC.mono fun R h => h (-1)))

omit [IsIntegral X] in

theorem isometric_comb_raise {v : ∀ σ : k →+* ℂ, CxPts p σ → ℝ} (hv : ∀ σ y, CInfAt (v σ) y)
    (hc : ∀ σ σ', (Weight.ofFun (v σ)).IsConj (Weight.ofFun (v σ'))) (N : HermLB p) (n : Fin 2 → ℤ) :
    (comb ![fnB v hv hc, N] n).Isometric ((zp N (n 1)).raise (fun σ y => (n 0 : ℝ) * v σ y)
      (fun σ y => (hv σ y).const_mul _) (isConj_mul hc _)) :=
  icls_eq_iff.1 (by
    rw [← icls_eq_iff.2 (isometric_tens_fnB _ _ _ _), icls_tens, icls_fnB_mul hv hc, icls_zp, icls_comb,
      Fin.sum_univ_two, add_comm]
    rfl)

theorem mixed_eq (H : ArCalc) (hX : IsArithVar p D) {v : ∀ σ : k →+* ℂ, CxPts p σ → ℝ} (hv : ∀ σ y, CInfAt (v σ) y)
    (hc : ∀ σ σ', (Weight.ofFun (v σ)).IsConj (Weight.ofFun (v σ'))) (N : HermLB p)
    {Θ : MvPolynomial (Fin 2) ℝ →ₗ[ℝ] ℝ} (hΘ : IsArFun ![fnB v hv hc, N] D Θ) (n : Fin 2 → ℤ) :
    Θ (MvPolynomial.X 0 * lin (fun i => (n i : ℝ)) ^ D) = 1 / 2 * chInt (comb ![fnB v hv hc, N] n) D v := by
  let A : Option (Fin 2) → Fin 2 → ℤ := fun j => Pi.single (j.elim 0 id) 1
  have h := ((H.arIso k X p D hX).2 _ _ Θ hΘ).2.2 (Option (Fin 2))
    (fun o => o.elim (fnB v hv hc) ![fnB v hv hc, N]) A (by
      rintro (_ | i)
      · exact isometric_comb_single _ 0
      · exact isometric_comb_single _ i)
  have e (j : Option (Fin 2)) : (lin fun i => (A j i : ℝ)) = MvPolynomial.X (j.elim 0 id) := lin_single _
  rw [← H.arChange k X p D hX _ _ v hv hc _ h n, LinearMap.comp_apply, AlgHom.toLinearMap_apply]
  congr 1
  rw [map_mul, map_pow, aeval_X, aeval_rename]
  simp only [Function.comp_def, e, Option.elim_none, Option.elim_some, id, aeval_X_left_apply]

theorem tendsto_selfInter : ArCalc → ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ),
    IsArithVar p D → GenSmooth p D → ∀ t : ℝ → ℝ, Tendsto t atTop (𝓝 0) → ∀ (L : ℝ → HermLB p) (L₀ : HermLB p),
    LFam t L L₀ → ∀ (a : ℝ → ℝ) (a₀ : ℝ), (∀ R, (L R).IsSelfInter (a R)) → L₀.IsSelfInter a₀ →
    Tendsto a atTop (𝓝 a₀) := by
  intro H k _ X _ p D hX hs t ht L L₀ ⟨u, hu, hc, hL, hf⟩ a a₀ ha ha₀
  choose Θ hΘ using fun R => ((H.arExists k X p D hX).2 _ ![fnB (u R) (hu R) (hc R), L₀]).1
  obtain ⟨Q, hQ⟩ := sub_dvd_pow_sub_pow (MvPolynomial.X 0 + MvPolynomial.X 1 : MvPolynomial (Fin 2) ℝ)
    (MvPolynomial.X 1) (D + 1)
  rw [add_sub_cancel_right] at hQ
  have key := tendsto_zero_of_pow (l := atTop) D (fun R => Θ R ∘ₗ LinearMap.mulLeft ℝ (MvPolynomial.X 0)) (fun n => by
    simp only [LinearMap.comp_apply, LinearMap.mulLeft_apply, fun R => mixed_eq H hX (hu R) (hc R) L₀ (hΘ R) n,
      fun R => (isometric_comb_raise (hu R) (hc R) L₀ n).chInt_eq]
    simpa only [mul_zero] using (tendsto_chInt hX hs ht hu hc hf (zp L₀ (n 1)) (n 0)).const_mul (1 / 2))
    (fun P e he hP R => (hΘ R).2 _ (1 + e) (by omega) ((isHomogeneous_X ℝ 0).mul hP)) Q
  have e₀ (R) : a₀ = Θ R (MvPolynomial.X 1 ^ (D + 1)) := ha₀.unique hX (((H.arIso k X p D hX).2 _ _ _ (hΘ R)).1 1)
  have e₁ (R) : a R = Θ R ((MvPolynomial.X 0 + MvPolynomial.X 1) ^ (D + 1)) := by
    have i : (comb ![fnB (u R) (hu R) (hc R), L₀] fun _ => 1).Isometric (L R) := icls_eq_iff.1 (by
      rw [← icls_eq_iff.2 (hL R), ← icls_eq_iff.2 (isometric_tens_fnB _ _ _ _), icls_tens, icls_comb, Fin.sum_univ_two,
        one_smul, one_smul, add_comm]
      rfl)
    have := (ha R).unique hX (i.isSelfInter hX ((hΘ R).1 _))
    simpa [lin] using this
  rw [← tendsto_sub_nhds_zero_iff]
  refine key.congr fun R => ?_
  rw [e₁ R, e₀ R, ← map_sub, hQ]
  rfl

end GlobalTheory.SelfCont

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemiAbelianDescentFromCompleteRegularCharts
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc

namespace GlobalTheory.Desc

theorem descent_semiAbelian : ∀ (X S : Scheme.{0}) [AlgebraicGeometry.IsNoetherian S], ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme S → ∀ (j : X ⟶ S) [IsOpenImmersion j], IsDominant j → ∀ (A : Over X) [GrpObj A], IsAbelianScheme A → ∀ L : LB A.left, L.IsLB → RelAmple A L → (∀ x : S, Nonempty (Chart j A x)) → ∃ (G : Over S) (_ : GrpObj G) (e : A.left ⟶ G.left), IsSemiAbelian G ∧ IsGrpPullback A G j e ∧ ∀ (x : S) (C : Chart j A x), ∃ π : C.G.left ⟶ G.left, IsGrpPullback C.G G C.ξ π ∧ C.α ≫ e = pullback.fst C.G.hom (jK C.R) ≫ π := by
  intro X S _ hS j _ hj A _ hA L hL hamp hC
  have hloc := GlobalTheory.T.exists_semiAbelianExtension_near_point X S hS j hj A hA L hL hamp hC
  obtain ⟨G, iG, e, hsemi, hpb⟩ := GlobalTheory.T.extendsToSemiAbelian_of_locally_normal_noetherian X S hS j hj A hA hloc
  exact ⟨G, iG, e, hsemi, hpb, fun x C => GlobalTheory.T.exists_grpPullback_completionChart_to_extension X S j hj A G e hsemi hpb x C⟩

end GlobalTheory.Desc
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitsCohomologyBijective
section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.units_cohomology_bijective : ∀ (q : ℕ) [NeZero q] (T : Type) [CommRing T] [IsDomain T] [IsLocalRing T], AIC T → IsUnit (q : T) → ∀ i : ℤ, Function.Bijective (gmPhi q T i) := by
  first | (exact @GlobalTheory.EtC.gmPhi_bijective_of_aic) | (exact GlobalTheory.EtC.gmPhi_bijective_of_aic) | (intros; apply GlobalTheory.EtC.gmPhi_bijective_of_aic  <;> assumption)
end

