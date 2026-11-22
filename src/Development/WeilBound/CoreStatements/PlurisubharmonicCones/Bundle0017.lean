import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeCptFiniteExtension
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeCptIsoCompare
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.Birational
import Development.WeilBound.CoreStatements.PlurisubharmonicCones.Bundle0016
import Development.WeilBound.CoreStatements.PlurisubharmonicCones.Bundle0008
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ExistsUniqueLeftBasisCoordsAdicCompletion
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.LieMultIffExistsFrame
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsExcisionNbhdAway
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsLieModel
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0013
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0018
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0043
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0151
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0095
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeInnerProductPullbackUnique
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0196
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0255
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0234
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0130
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0131
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0256
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0006
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PullCub

-- bundled from Development.WeilBound.CoreStatements.PlurisubharmonicCones.ProdSqrtLead
section
open AlgebraicGeometry CategoryTheory Limits NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp
open ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.Cmp
open scoped ComplexOrder

noncomputable section

namespace LevelTowerAlt.Comparison₂

section Gram

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X X' : Scheme.{0}} {t : SAB H X} {t' : SAB H X'}
  {f : X' ⟶ X} {Ω Ω' : Type} [Field Ω] [Field Ω'] {ξ : Sp Ω ⟶ X} {ξ' : Sp Ω' ⟶ X'} {i : Ω →+* Ω'}
  {Li Li' : Type} [AddCommGroup Li] [Module Ω Li] [AddCommGroup Li'] [Module Ω' Li']

theorem val_unique (hξ : IsCptGen ξ) (M : LieModel t.G ξ Li) {z : Sp ℂ ⟶ X} (hq : genPt ξ ⤳ centre z) {e : Li}
    {w : epsAt z ⟶ t.G} (hw : M.ValAt z e w) : e ∈ M.lat ⟨centre z, hq⟩ ∧ ∀ w', M.ValAt z e w' → w' = w := by
  obtain ⟨Vz, _, _, ⟨MR⟩⟩ := lieModel_exists X t.G ℂ z
  obtain ⟨ev, hev1, -, -⟩ := GlobalTheory.T.lie_lattice_eval_at_local_ring X t.G Ω ξ Li M ℂ z hq Vz MR hξ t.semi.smooth
  obtain ⟨x, rfl⟩ := MR.onto w (GrNorm.tan_of_valAt hw)
  obtain ⟨he, e2⟩ := (hev1 _ _).1 hw
  refine ⟨he, fun w' hw' => ?_⟩
  obtain ⟨x', rfl⟩ := MR.onto w' (GrNorm.tan_of_valAt hw')
  obtain ⟨_, e3⟩ := (hev1 _ _).1 hw'
  rw [← e2, ← e3]

theorem gram_up (m : SABMap t' t f) (hξ : IsCptGen ξ) (hξ' : IsCptGen ξ') (hd : GlobalTheory.CompanionTheory.Ar.Dominates ξ' ξ f i)
    (M : LieModel t.G ξ Li) (M' : LieModel t'.G ξ' Li') (j : Li →+ Li')
    (hpt : ∀ e, (M'.pt (j e)).left ≫ m.φ = Spec.map (CommRingCat.ofHom (dualMap i)) ≫ (M.pt e).left)
    (z : Sp ℂ ⟶ X') (hq : genPt ξ' ⤳ centre z) (hp : genPt ξ ⤳ f (centre z)) :
    ∃ φ : regAt ξ' ⟨centre z, hq⟩ →+* ℂ, (∀ a : regAt ξ' ⟨centre z, hq⟩, ValAt ξ' z (a : Ω') (φ a)) ∧
      ∀ (r : ℕ) (b : Fin r → Li) (Γ : Matrix (Fin r) (Fin r) ℂ) (b' : Fin r → Li')
        (P : Matrix (Fin r) (Fin r) (regAt ξ' ⟨centre z, hq⟩)), M.GramAt t.PP.L (z ≫ f) b Γ →
        (∀ k, b' k = ∑ l, (P l k : Ω') • j (b l)) → M'.GramAt t'.PP.L z b' ((P.map φ)ᴴ * Γ * P.map φ) := by
  classical
  set p' : Cpt ξ' := ⟨centre z, hq⟩ with hp'
  obtain ⟨Vz, _, _, ⟨MR⟩⟩ := lieModel_exists X' t'.G ℂ z
  obtain ⟨ev, hev1, hev2, -⟩ := GlobalTheory.T.lie_lattice_eval_at_local_ring X' t'.G Ω' ξ' Li' M' ℂ z hq Vz MR hξ' t'.semi.smooth
  let eA : X'.presheaf.stalk p'.1 ≃+* regAt ξ' p' :=
    RingEquiv.ofBijective (genMap ξ' p').rangeRestrict ⟨fun a b e => hξ'.inj p' (congrArg Subtype.val e),
      (genMap ξ' p').rangeRestrict_surjective⟩
  let φ : regAt ξ' p' →+* ℂ := (Scheme.stalkClosedPointTo z).hom.comp (eA.symm : regAt ξ' p' →+* X'.presheaf.stalk p'.1)
  have hφ : ∀ a : regAt ξ' p', ValAt ξ' z (a : Ω') (φ a) := fun a =>
    ⟨hq, eA.symm a, congrArg Subtype.val (eA.apply_symm_apply a), rfl⟩
  refine ⟨φ, hφ, fun r b Γ b' P ⟨v, hv, hI⟩ hP => ?_⟩
  let val : Li' → Vz := fun e => if he : e ∈ M'.lat p' then ev ⟨e, he⟩ else 0
  have hval : ∀ e (he : e ∈ M'.lat p'), val e = ev ⟨e, he⟩ := fun e he => dif_pos he
  have h0 : val 0 = 0 := by
    rw [hval 0 (zero_mem _)]
    exact map_zero ev
  have hadd : ∀ e ∈ M'.lat p', ∀ e' ∈ M'.lat p', val (e + e') = val e + val e' := fun e he e' he' => by
    rw [hval _ (add_mem he he'), hval e he, hval e' he']
    exact map_add ev ⟨e, he⟩ ⟨e', he'⟩
  have hsmul : ∀ a : regAt ξ' p', ∀ e ∈ M'.lat p', val ((a : Ω') • e) = φ a • val e := fun a e he => by
    have hm : (a : Ω') • e ∈ M'.lat p' := (M'.lat p').smul_mem a he
    rw [hval _ hm, hval e he]
    exact hev2 a (φ a) ⟨e, he⟩ (hφ a)
  have hpick : ∀ e (w : epsAt z ⟶ t'.G), M'.ValAt z e w → e ∈ M'.lat p' ∧ w = MR.pt (val e) := by
    intro e w hw
    obtain ⟨x, hx⟩ := MR.onto w (GrNorm.tan_of_valAt hw)
    rw [← hx] at hw ⊢
    obtain ⟨he, e2⟩ := (hev1 _ _).1 hw
    exact ⟨he, by rw [hval e he, e2]⟩
  have hu := fun k => val_unique hξ M (z := z ≫ f) hp (hv k)
  have hdown := fun k => HodgePull.value_pull (M' := M') (j := j) hd m.cart hpt hq hp (hu k).1
  choose w w' hw hw' hww using hdown
  have hwv : ∀ k, w k = v k := fun k => (hu k).2 _ (hw k)
  have hjL : ∀ k, j (b k) ∈ M'.lat p' := fun k => (hpick _ _ (hw' k)).1
  have hw'e : ∀ k, w' k = MR.pt (val (j (b k))) := fun k => (hpick _ _ (hw' k)).2
  have hb'L : ∀ k, b' k ∈ M'.lat p' := fun k => by
    rw [hP k]
    exact Submodule.sum_mem _ fun l _ => (M'.lat p').smul_mem (P l k) (hjL l)
  have hbv : ∀ k, val (b' k) = ∑ l, (P.map φ) l k • val (j (b l)) := fun k => by
    rw [hP k]
    exact GrNorm.val_sum h0 hadd hsmul hjL (fun l => P l k) Finset.univ
  refine ⟨fun k => MR.pt (val (b' k)), fun k => (hev1 _ _).2 ⟨hb'L k, (hval _ _).symm⟩, fun p q => ?_⟩
  simp only [hbv]
  refine HodgePull.gram_comb MR (fun l => val (j (b l))) Γ p (fun a c => ?_) (HodgePull.hodgeInnerProduct_unique m) _ p q
  rw [← hw'e, ← hw'e]
  refine ((GlobalTheory.T.hodge_inner_product_pullback_unique E H X' X t' t f m z (w' a) (w' c) (w a) (w c) (hww a) (hww c)).1 _).2 ?_
  rw [hwv, hwv]
  exact hI a c

end Gram

section Alg

variable {Ω : Type} [Field Ω] {V : Type} [AddCommGroup V] [Module Ω V] {r : ℕ}

theorem det_tri {b₀ c : Fin r → V} (hb₀ : LinearIndependent Ω b₀) {t : Fin r → Ω}
    (ht : ∀ k : Fin r, c k - t k • b₀ k ∈ flagStep Ω b₀ k) (Q : Matrix (Fin r) (Fin r) Ω) (hQ : ∀ k, c k = ∑ l, Q l k • b₀ l) :
    Q.det = ∏ k, t k := by
  classical
  choose d hd0 hd using fun k => GrNorm.exists_coeff_of_mem_flagStep (ht k)
  have key : ∀ k, (fun l => Q l k) = fun l => d k l + (Pi.single k (t k) : Fin r → Ω) l := fun k =>
    GrNorm.coeff_eq_of_li hb₀ (by
      rw [← hQ k]
      simp only [add_smul, Finset.sum_add_distrib, ← hd k]
      simp [Pi.single_apply, ite_smul])
  have h1 : Q.BlockTriangular id := fun l k hlk => by
    have h := congrFun (key k) l
    have hlk' : k < l := hlk
    rw [hd0 k l hlk'.le, Pi.single_eq_of_ne hlk'.ne', add_zero] at h
    exact h
  rw [Matrix.det_of_upperTriangular h1]
  refine Finset.prod_congr rfl fun k _ => ?_
  have h := congrFun (key k) k
  rwa [hd0 k k le_rfl, Pi.single_eq_same, zero_add] at h

theorem frame_mat (A : Subring Ω) {b b' : Fin r → V} (hb' : LinearIndependent Ω b')
    (hs : Submodule.span A (Set.range b) = Submodule.span A (Set.range b')) :
    ∃ P : Matrix (Fin r) (Fin r) A, (∀ k, b' k = ∑ l, (P l k : Ω) • b l) ∧ IsUnit P.det := by
  classical
  choose c hc using fun k => (Submodule.mem_span_range_iff_exists_fun A).1
    (show b' k ∈ Submodule.span A (Set.range b) from hs ▸ Submodule.subset_span ⟨k, rfl⟩)
  choose c' hc' using fun k => (Submodule.mem_span_range_iff_exists_fun A).1
    (show b k ∈ Submodule.span A (Set.range b') from hs ▸ Submodule.subset_span ⟨k, rfl⟩)
  let P : Matrix (Fin r) (Fin r) A := Matrix.of fun l k => c k l
  let P' : Matrix (Fin r) (Fin r) A := Matrix.of fun l k => c' k l
  have h1 : P' * P = 1 := by
    ext l k
    have key : (fun l => ((P' * P) l k : Ω)) = (Pi.single k 1 : Fin r → Ω) := GrNorm.coeff_eq_of_li hb' (by
      have e1 : ∑ l, (Pi.single k 1 : Fin r → Ω) l • b' l = b' k := by simp [Pi.single_apply, ite_smul]
      rw [e1, ← hc k]
      simp only [← hc', Finset.smul_sum, smul_smul, Matrix.mul_apply, P, P', Matrix.of_apply, AddSubmonoidClass.coe_finset_sum,
        Finset.sum_smul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun a' _ => ?_
      rw [mul_comm]
      rfl)
    rw [congrFun key l, Matrix.one_apply, Pi.single_apply]
    split_ifs <;> simp
  exact ⟨P, fun k => (hc k).symm, Matrix.isUnit_det_of_left_inverse h1⟩

theorem prod_sqrt_lead {Γ : Matrix (Fin r) (Fin r) ℂ} (h : Γ.PosDef) :
    ∏ k : Fin r, Real.sqrt (leadMinor Γ (k + 1) / leadMinor Γ k) = Real.sqrt Γ.det.re := by
  have key : ∀ n, n ≤ r → ∏ k ∈ Finset.range n, Real.sqrt (leadMinor Γ (k + 1) / leadMinor Γ k) =
      Real.sqrt (leadMinor Γ n) := by
    intro n hn
    induction n with
    | zero => simp [leadMinor_size_zero]
    | succ n ih =>
      have h1 := leadMinor_pos_of_posDef h (Nat.le_of_succ_le hn)
      rw [Finset.prod_range_succ, ih (Nat.le_of_succ_le hn), ← Real.sqrt_mul h1.le, mul_div_cancel₀ _ h1.ne']
  rw [Fin.prod_univ_eq_prod_range (fun k => Real.sqrt (leadMinor Γ (k + 1) / leadMinor Γ k)), key r le_rfl,
    leadMinor_size_self]

theorem sqrt_det_conj (Γ C : Matrix (Fin r) (Fin r) ℂ) :
    Real.sqrt (Cᴴ * Γ * C).det.re = ‖C.det‖ * Real.sqrt Γ.det.re := by
  have e : (Cᴴ * Γ * C).det = ((‖C.det‖ ^ 2 : ℝ) : ℂ) * Γ.det := by
    rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_conjTranspose, mul_right_comm]
    congr 1
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_eq_conj_mul_self]
    rfl
  rw [e, Complex.re_ofReal_mul, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (norm_nonneg _)]

end Alg

section Sec

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Sp Ω ⟶ X} {K : Type} [Fintype K] {J : K → Type} [∀ k, Fintype (J k)]
  {y : (Σ k, J k) → Ω}

theorem mono_sum {F : Type} [Field F] {I : Type} (z : K → F) (hz : ∀ k, z k ≠ 0) (s : Finset I) (a : I → K → ℤ) :
    ∏ k, z k ^ (∑ j ∈ s, a j) k = ∏ j ∈ s, ∏ k, z k ^ a j k := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert j s hj ih =>
    rw [Finset.sum_insert hj, Finset.prod_insert hj, ← ih, ← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun k _ => zpow_add₀ (hz k) _ _

theorem valAt_prod {I : Type} {z : Sp ℂ ⟶ X} (hq : genPt ξ ⤳ centre z) (s : Finset I) {a : I → Ω} {u : I → ℂ}
    (h : ∀ j, ValAt ξ z (a j) (u j)) : ValAt ξ z (∏ j ∈ s, a j) (∏ j ∈ s, u j) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨hq, 1, by simp, by rw [Finset.prod_empty]; exact map_one _⟩
  | insert j s hj ih =>
    rw [Finset.prod_insert hj, Finset.prod_insert hj]
    exact CxVal.mul (h j) ih

theorem secNorm_prod {I : Type} [Fintype I] {z : Sp ℂ ⟶ X} (hq : genPt ξ ⤳ centre z) {w : (Σ k, J k) → ℂ}
    (hw : CoordsAt ξ y z w) {L : I → HermLine J} {e t : I → Ω} {ν : I → ℝ}
    (h : ∀ j, SecNorm ξ y (L j) (e j) z w (t j) (ν j)) {A : HermLine J} (ha : A.a = ∑ j, (L j).a)
    (hh : A.h w = ∏ j, (L j).h w) : SecNorm ξ y A (∏ j, e j) z w (∏ j, t j) (∏ j, ν j) := by
  refine ⟨Finset.prod_ne_zero_iff.2 fun j _ => (h j).1, hw, fun c hc => ?_⟩
  choose u hu hν using fun j => (h j).2.2 c hc
  have hy : ∀ k, y ⟨k, c k⟩ ≠ 0 := fun k => (hw.2 k (c k) (isUnit_iff_ne_zero.2 (hc k))).1
  refine ⟨∏ j, u j, ?_, ?_⟩
  · rw [ha, mono_sum _ hy, ← Finset.prod_mul_distrib, ← Finset.prod_div_distrib]
    exact valAt_prod hq _ hu
  · rw [ha, mono_sum (fun k => ‖w ⟨k, c k⟩‖) (fun k => norm_ne_zero_iff.2 (hc k)), hh, norm_prod,
      ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun j _ => hν j

end Sec

end LevelTowerAlt.Comparison₂
end
end

-- bundled from Development.WeilBound.CoreStatements.PlurisubharmonicCones.TorusModelCochar
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp
open GroundTheory.Heights₂.Heights TensorProduct

set_option backward.isDefEq.respectTransparency false

noncomputable section
namespace LevelTowerAlt.Lin

theorem pull_inj {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G'] {f : S' ⟶ S}
    {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G f φ) {T : Over S'} {v v' : T ⟶ G'}
    (e : v.left ≫ φ = v'.left ≫ φ) : v = v' :=
  Over.OverMorphism.ext (h.1.hom_ext e (by rw [Over.w, Over.w]))

theorem isGrpPullback_iso {S : Scheme.{0}} {A B : Over S} [GrpObj A] [GrpObj B] (e : A ≅ B) [IsMonHom e.hom] :
    IsGrpPullback A B (𝟙 S) e.hom.left := by
  refine ⟨?_, fun T x y x₀ y₀ hx hy => ?_⟩
  · haveI : IsIso e.hom.left := ((Over.forget S).mapIso e).isIso_hom
    exact IsPullback.of_horiz_isIso ⟨by simp⟩
  · have e₁ : (x * y) ≫ e.hom = (x ≫ e.hom) * (y ≫ e.hom) := by
      first | exact Hom.mul_comp _ _ _ | exact MonObj.mul_comp _ _ _ | exact CategoryTheory.Hom.mul_comp _ _ _
    have : (x * y).left ≫ e.hom.left = ((x ≫ e.hom) * (y ≫ e.hom)).left := by
      rw [← e₁]; rfl
    rw [this]
    exact mul_left_congr (Category.comp_id _) _ _ _ _ hx hy

variable {L : Type} [Field L] [NumberField L]

theorem exists_generic {X : Scheme.{0}} (G : Over X) [GrpObj G] [IsCommMonObj G] [Smooth G.hom] (z : Sp (𝓞 L) ⟶ X)
    {V₀ : Type} [AddCommGroup V₀] [Module (𝓞 L) V₀] (M₀ : LieModel G z V₀) :
    ∃ (V : Type) (_ : AddCommGroup V) (_ : Module L V) (_ : Module (𝓞 L) V) (_ : IsScalarTower (𝓞 L) L V)
      (Mz : LieModel G (spMap (algebraMap (𝓞 L) L) ≫ z) V) (j : V₀ →ₗ[𝓞 L] V),
      (∀ e, (Mz.pt (j e)).left = spMap (dualMap (algebraMap (𝓞 L) L)) ≫ (M₀.pt e).left) ∧ Function.Injective j ∧
        Submodule.span L (Set.range j) = ⊤ ∧ Module.Finite (𝓞 L) V₀ ∧ Module.Finite L V := by
  obtain ⟨V, _, _, ⟨Mz⟩⟩ := lieModel_exists X G L (spMap (algebraMap (𝓞 L) L) ≫ z)
  letI : Module (𝓞 L) V := Module.compHom V (algebraMap (𝓞 L) L)
  haveI : IsScalarTower (𝓞 L) L V := ⟨fun a b x => by
    show (a • b) • x = algebraMap (𝓞 L) L a • b • x
    rw [Algebra.smul_def, mul_smul]⟩
  obtain ⟨j₀, hj₀, -⟩ := GlobalTheory.T.lie_model_existsUnique_semilinear X G (𝓞 L) L (algebraMap (𝓞 L) L) z V₀ V M₀ Mz
  let j : V₀ →ₗ[𝓞 L] V :=
    { toFun := j₀
      map_add' := j₀.map_add
      map_smul' := fun a x => j₀.map_smulₛₗ a x }
  have hj : ∀ e, (Mz.pt (j e)).left = spMap (dualMap (algebraMap (𝓞 L) L)) ≫ (M₀.pt e).left := fun e =>
    (Category.comp_id _).symm.trans (hj₀ e)
  obtain ⟨hf, hp, hb⟩ := GlobalTheory.T.lie_model_finite_base_change X G (𝓞 L) z V₀ M₀
  have hbc : IsBaseChange L j := hb L V Mz j hj
  haveI : IsLocalizedModule (nonZeroDivisors (𝓞 L)) j := (isLocalizedModule_iff_isBaseChange _ L j).2 hbc
  refine ⟨V, inferInstance, inferInstance, inferInstance, inferInstance, Mz, j, hj, ?_, ?_, hf,
    (GlobalTheory.T.lie_model_finite_base_change X G L _ V Mz).1⟩
  · refine (injective_iff_map_eq_zero j).2 fun x hx => ?_
    obtain ⟨s, hs⟩ := (IsLocalizedModule.eq_zero_iff (nonZeroDivisors (𝓞 L)) j).1 hx
    exact (smul_eq_zero.1 (show (s : 𝓞 L) • x = 0 from hs)).resolve_left (nonZeroDivisors.coe_ne_zero s)
  · refine eq_top_iff.2 fun x _ => ?_
    induction x using hbc.inductionOn with
    | zero => exact Submodule.zero_mem _
    | tmul m => exact Submodule.subset_span ⟨m, rfl⟩
    | smul s n hn => exact Submodule.smul_mem _ _ (hn trivial)
    | add a b ha hb => exact Submodule.add_mem _ (ha trivial) (hb trivial)

theorem generic_inj {X : Scheme.{0}} (G : Over X) [GrpObj G] [IsCommMonObj G] [Smooth G.hom] (z : Sp (𝓞 L) ⟶ X)
    {V₀ : Type} [AddCommGroup V₀] [Module (𝓞 L) V₀] (M₀ : LieModel G z V₀) {e e' : V₀}
    (h : spMap (dualMap (algebraMap (𝓞 L) L)) ≫ (M₀.pt e).left =
      spMap (dualMap (algebraMap (𝓞 L) L)) ≫ (M₀.pt e').left) : e = e' := by
  obtain ⟨V, _, _, _, _, Mz, j, hj, hi, -⟩ := exists_generic G z M₀
  exact hi (Mz.inj (Over.OverMorphism.ext ((hj e).trans (h.trans (hj e').symm))))

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem comp_bar (H : Host E) (τ : 𝓞 E →+* ℂ) (hτ : Function.Injective τ) (a : 𝓞 E) :
    τ (H.bar a) = starRingEnd ℂ (τ a) := by
  let ψ : E →+* ℂ := IsFractionRing.lift hτ
  have hψ : ∀ b : 𝓞 E, ψ (b : E) = τ b := fun b => IsFractionRing.lift_algebraMap hτ b
  rw [← hψ, ← hψ, H.bar_eq, IsCMField.complexEmbedding_complexConj]

theorem adj_model (t' : SAB H (Sp (𝓞 L))) (tB : SAB H (Sp L)) (m' : SABMap tB t' (spMap (algebraMap (𝓞 L) L)))
    (hpr : IsPrincipal tB) (B : HermitianBundle.{0} L) (MB : LieModel t'.G (𝟙 _) B.carrier)
    (hB : IsFibre (HodgeIP t'.G t'.PP.L) (𝟙 _) B MB) (ρ' : 𝓞 E →+* Module.End (𝓞 L) B.carrier)
    (hρ' : MB.IsActOf t'.act.act ρ') (eC : L →+* ℂ) (a : 𝓞 E) (x y : B.carrier) :
    (B.metric.form eC).inner ((1 : ComplexAt eC) ⊗ₜ[𝓞 L] ρ' a x) ((1 : ComplexAt eC) ⊗ₜ[𝓞 L] y) =
      (B.metric.form eC).inner ((1 : ComplexAt eC) ⊗ₜ[𝓞 L] x) ((1 : ComplexAt eC) ⊗ₜ[𝓞 L] ρ' (H.bar a) y) := by
  let w := fun u : B.carrier => LieTangent.epsBase (eC.comp (algebraMap (𝓞 L) L)) rfl ≫ MB.pt u
  have hl : ∀ u, MB.Lifts (eC.comp (algebraMap (𝓞 L) L)) (𝟙 t'.G.left) u (w u) := fun u => Category.comp_id _
  have ht : ∀ u, IsTanAt t'.G _ (w u) := fun u => LieTangent.isTanAt_base _ rfl (MB.tan u)
  have ha : ∀ b u, w (ρ' b u) = w u ≫ t'.act.act b := fun b u => by
    simp only [w]
    rw [hρ' b u, Category.assoc]
  have hpol : ∃ (t'' : SAB H (Sp ℂ)) (_ : SABMap t'' t' (spMap (eC.comp (algebraMap (𝓞 L) L)) ≫ 𝟙 _)),
      IsProper t''.G.hom ∧ Out.RelAmple t''.G t''.PP.L := by
    rw [Category.comp_id, ← Sl.BaseExt.spMap_comp]
    obtain ⟨t'', ⟨m⟩⟩ := Sl.BaseExt.exists_pull (spMap eC) tB
    obtain ⟨n, -⟩ := sabComp pullCubComp E H _ _ _ t' tB t'' _ _ m' m
    have := (GlobalTheory.T.isPrincipal_base_change_iff E H L ℂ eC tB t'' m).2 hpr
    exact ⟨t'', n, this.1, this.2.1⟩
  have h1 := hB eC (ρ' a x) y _ _ (hl _) (hl _)
  have h2 := hB eC x (ρ' (H.bar a) y) _ _ (hl _) (hl _)
  rw [ha] at h1 h2
  exact HodgeUnique.hodgeInnerProduct_eq ((GlobalTheory.T.hodge_inner_product_adjoint E H _ t' _ (w x) (w y) a _ hpol (ht x) (ht y)).1 h1) h2

theorem closure_basis {X V : Type} [AddCommGroup X] [AddCommGroup V] {r : ℕ} (bs : Module.Basis (Fin r) ℤ X)
    (κ : X →+ V) (x : V) : x ∈ AddSubgroup.closure (Set.range fun i => κ (bs i)) ↔ ∃ δ, κ δ = x := by
  constructor
  · intro hx
    exact (AddSubgroup.closure_le κ.range).2 (by rintro _ ⟨i, rfl⟩; exact ⟨_, rfl⟩) hx
  · rintro ⟨δ, rfl⟩
    rw [← bs.sum_repr δ, map_sum]
    refine AddSubgroup.sum_mem _ fun i _ => ?_
    rw [map_zsmul]
    exact AddSubgroup.zsmul_mem _ (AddSubgroup.subset_closure (Set.mem_range_self i)) _

theorem torusModel_cochar (X : Type) [AddCommGroup X] :
    IsCocharLie (Fl.Test.torusModel (𝟙 (Sp L)) X) := fun δ χ =>
  (GlobalTheory.Diag.charVal_eq_torusFst _ χ).symm.trans (GlobalTheory.Diag.charVal_epsVec δ χ)

theorem exists_lin {Ψ : Type} {X : Scheme.{0}} (t : SAB H X) (z : Sp (𝓞 L) ⟶ X)
    (P : AbPart t (spMap (algebraMap (𝓞 L) L) ≫ z)) (t' : SAB H (Sp (𝓞 L)))
    (m' : SABMap P.tB t' (spMap (algebraMap (𝓞 L) L))) (hpr : IsPrincipal P.tB) (B : HermitianBundle.{0} L)
    (MB : LieModel t'.G (𝟙 _) B.carrier) (hB : IsFibre (HodgeIP t'.G t'.PP.L) (𝟙 _) B MB)
    (σ : Ψ ⊕ Ψ → (𝓞 E →+* L)) (hσ : Function.Bijective σ) (hσ' : ∀ s, Function.Injective (σ s)) :
    ∃ (V : Type) (_ : AddCommGroup V) (_ : Module L V) (_ : Module (𝓞 L) V) (_ : IsScalarTower (𝓞 L) L V)
      (MV : LieModel P.tK.G (𝟙 (Sp L)) V) (A : LinPt E L Ψ V), A.σ = σ ∧ MV.IsActOf P.tK.act.act A.ρ ∧
      (∀ x, x ∈ A.Λ ↔ ∃ v : epsAt z ⟶ t.G, IsTanAt t.G z v ∧
        (MV.pt x).left ≫ P.m.φ = spMap (dualMap (algebraMap (𝓞 L) L)) ≫ v.left) ∧
      P.IsCochars MV A.I ∧
      (∃ (MB : LieModel t'.G (𝟙 _) A.Bq.carrier), IsFibre (HodgeIP t'.G t'.PP.L) (𝟙 _) A.Bq MB ∧
        ∀ x : A.Λ, MB.Lifts (algebraMap (𝓞 L) L) m'.φ (A.f x) (MV.pt x ≫ P.τ.q ≫ P.e.hom)) ∧
      Module.finrank (𝓞 L) A.Bq.carrier ≤ Module.finrank L V := by
  letI := P.τ.addCommGroup
  letI := P.τ.grpB
  haveI := P.τ.free
  haveI := P.τ.finite
  haveI := P.τ.q_hom
  haveI := P.τ.i_hom
  haveI := P.e_hom
  haveI heinv : IsMonHom P.e.inv := inferInstance
  haveI : Smooth t.G.hom := t.semi.smooth
  haveI : Smooth t'.G.hom := t'.semi.smooth
  obtain ⟨V₀, _, _, ⟨M₀⟩⟩ := lieModel_exists X t.G (𝓞 L) z
  obtain ⟨V, _, _, _, _, Mz, j, hj, hinj, hspan, hfin₀, hfin⟩ := exists_generic t.G z M₀
  obtain ⟨MV, hMV⟩ := (GlobalTheory.T.lie_model_pullback_correspondence L X _ t.G P.tK.G P.m.φ V P.m.cart).1 Mz
  have hj' : ∀ e, (MV.pt (j e)).left ≫ P.m.φ = spMap (dualMap (algebraMap (𝓞 L) L)) ≫ (M₀.pt e).left :=
    fun e => (hMV _).trans (hj e)
  obtain ⟨ρ, hρ, -⟩ := lieModel_exists_unique_act _ _ L (𝟙 _) _ MV (𝓞 E) P.tK.act.act P.tK.act.hom
    P.tK.act.one P.tK.act.mul P.tK.act.add
  obtain ⟨ρ₀, hρ₀, -⟩ := lieModel_exists_unique_act _ _ (𝓞 L) z _ M₀ (𝓞 E) t.act.act t.act.hom
    t.act.one t.act.mul t.act.add
  obtain ⟨ρ', hρ', -⟩ := lieModel_exists_unique_act _ _ (𝓞 L) (𝟙 _) _ MB (𝓞 E) t'.act.act t'.act.hom
    t'.act.one t'.act.mul t'.act.add
  have hjρ : ∀ a x, j (ρ₀ a x) = ρ a (j x) := fun a x => MV.inj (pull_inj P.m.cart (by
    rw [hj', hρ₀ a x, hρ a (j x), Over.comp_left, Over.comp_left, Category.assoc, P.m.act a, ← Category.assoc,
      ← Category.assoc, hj']))
  obtain ⟨md, hmd⟩ := GlobalTheory.T.torus_extension_module_structure L P.tK.G P.τ (𝓞 E) P.tK.act (fun a => by
    haveI := P.tB.act.hom a
    refine ⟨P.e.hom ≫ P.tB.act.act a ≫ P.e.inv, inferInstance, ?_⟩
    refine (cancel_mono P.e.hom).1 ?_
    simpa only [Category.assoc, Iso.inv_hom_id, Category.comp_id] using P.act a)
  letI := md
  let MT := Fl.Test.torusModel (𝟙 (Sp L)) P.τ.X
  have hMT : IsCocharLie MT := torusModel_cochar _
  obtain ⟨iL, hiL, -⟩ := lieModel_exists_unique_diff _ _ _ L (𝟙 _) _ _ MT MV P.τ.i
  let κ : (P.τ.X →+ ℤ) →+ V := iL.toAddMonoidHom.comp (AddMonoidHom.compHom (Int.castAddHom L))
  have hκ : ∀ δ, MV.pt (κ δ) = MT.pt ((Int.castAddHom L).comp δ) ≫ P.τ.i := fun δ => hiL _
  let bs := Module.finBasis ℤ (P.τ.X →+ ℤ)
  have hφ' : IsGrpPullback P.τ.B t'.G (spMap (algebraMap (𝓞 L) L)) (P.e.hom.left ≫ m'.φ) := by
    have := (isGrpPullback_iso P.e).comp m'.cart
    simpa using this
  obtain ⟨ε, f, hε, hf, hli, hker, hsur⟩ := GlobalTheory.T.semi_abelian_pullback_torus_extension X t.G t.semi L z P.tK.G P.m.φ P.τ t'.G _ t'.semi P.m.cart hφ'
    MT hMT V₀ B.carrier M₀ MB _ bs
  have hjε : (fun i => j (ε i)) = fun i => κ (bs i) := funext fun i => MV.inj (pull_inj P.m.cart (by
    rw [hj', hκ]
    exact (hε i).symm))
  have hfl : ∀ e, (MV.pt (j e) ≫ P.τ.q ≫ P.e.hom).left ≫ m'.φ =
      spMap (dualMap (algebraMap (𝓞 L) L)) ≫ (MB.pt (f e)).left := fun e => by
    refine Eq.trans ?_ (hf e _ (hj' e))
    simp only [Over.comp_left, Category.assoc]
  let Q : Pre E L Ψ V V₀ B :=
    { ρ := ρ, σ := σ, σ_bij := hσ, σ_inj := hσ', fin := hfin₀, j := j, j_inj := hinj, span := hspan
      ρ₀ := fun a x => ρ₀ a x, j_ρ := hjρ, r := _, ε := ε, ε_li := hli
      I_stable := fun a x hx => by
        rw [hjε, closure_basis] at hx ⊢
        obtain ⟨δ, rfl⟩ := hx
        refine ⟨δ.comp (DistribSMul.toAddMonoidHom P.τ.X a), MV.inj ?_⟩
        rw [hρ a, hκ, hκ, Category.assoc, ← hmd a, ← Category.assoc]
        exact congrArg (· ≫ P.τ.i) (GlobalTheory.Diag.epsVec_comp_diagMap ((Int.castAddHom L).comp δ) _).symm
      f := f, ker := hker, full := hsur, ρ' := fun a x => ρ' a x
      f_ρ := fun a x => generic_inj t'.G (𝟙 _) MB (by
        have e1 : MV.pt (j (ρ₀ a x)) ≫ P.τ.q ≫ P.e.hom =
            (MV.pt (j x) ≫ P.τ.q ≫ P.e.hom) ≫ P.tB.act.act a := by
          rw [hjρ, hρ a]
          simp only [Category.assoc]
          rw [P.act a]
        rw [← hfl, e1, Over.comp_left, Category.assoc]
        refine (congrArg (_ ≫ ·) (m'.act a)).trans ?_
        refine (Category.assoc _ _ _).symm.trans ?_
        refine (congrArg (· ≫ (t'.act.act a).left) (hfl x)).trans ?_
        rw [hρ' a, Over.comp_left, Category.assoc])
      bar := H.bar, bar_conj := comp_bar H, adj := adj_model t' P.tB m' hpr B MB hB ρ' hρ' }
  refine ⟨V, inferInstance, inferInstance, inferInstance, inferInstance, MV, Q.lin, rfl, hρ, fun x => ?_,
    ⟨MT, hMT, fun x => ?_⟩, ⟨MB, hB, fun x => ?_⟩, Q.rank_le⟩
  · constructor
    · rintro ⟨e, rfl⟩
      exact ⟨M₀.pt e, M₀.tan e, hj' e⟩
    · rintro ⟨v, hv, h⟩
      obtain ⟨e, rfl⟩ := M₀.onto v hv
      exact ⟨e, MV.inj (pull_inj P.m.cart ((hj' e).trans h.symm))⟩
  · show x ∈ AddSubgroup.closure (Set.range fun i => j (ε i)) ↔ _
    rw [hjε, closure_basis]
    refine exists_congr fun δ => ?_
    rw [← hκ]
    exact ⟨fun h => by rw [h], fun h => (MV.inj h).symm⟩
  · have := hfl (Q.inv x)
    rw [show j (Q.inv x) = x from Q.j_inv x] at this
    exact this

end LevelTowerAlt.Lin
end
end

