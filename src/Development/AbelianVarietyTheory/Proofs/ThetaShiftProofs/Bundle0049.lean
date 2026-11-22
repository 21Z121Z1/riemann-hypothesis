import Mathlib
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.ModelsAt
import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsValLineLogNormAtIffEmbedding
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.HolArcEqFlowOrbit
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0040
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0046
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0014
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0031
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0028
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0008
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.PairUnfoldPfA

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsIsSplit
section
noncomputable section

namespace GlobalTheory.ArcCM.Split

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.Geo.Tor

section Alg

variable {A U : Type} [CommGroup A] [CommGroup U] {θ : A → A → A → U}

def quo (θ : A → A → A → U) (k : ℕ) (x b : A) : U := cubN θ k 1 x b * (cubN θ k 1 b x)⁻¹

variable (h : IsCub θ)
include h

theorem coc_four (a b c d x : A) :
    θ (a * b) (c * d) x * θ a b x * θ c d x = θ (a * c) (b * d) x * θ a c x * θ b d x := by
  have e₁ := h.coc a b (c * d) x
  have e₂ := h.coc b c d x
  have e₃ := h.coc a c (b * d) x
  have e₄ := h.coc c b d x
  rw [mul_left_comm c b d] at e₃
  rw [mul_comm c b, h.s01 c b] at e₄
  apply Additive.ofMul.injective
  have E := fun {p q : U} (e : p = q) => congrArg Additive.ofMul e
  have a₁ := E e₁; have a₂ := E e₂; have a₃ := E e₃; have a₄ := E e₄
  simp only [ofMul_mul] at *
  linear_combination (norm := abel) a₁ - a₂ - a₃ + a₄

theorem cubN_mul_left (k : ℕ) (m m' x : A) :
    cubN θ k 1 (m * m') x * θ m m' x ^ k = θ (m ^ k) (m' ^ k) x * cubN θ k 1 m x * cubN θ k 1 m' x := by
  induction k with
  | zero => simp [cubN, h.face]
  | succ k ih =>
    have c := coc_four h (m ^ k) (m' ^ k) m m' x
    simp only [cubN, Finset.prod_range_succ, _root_.one_mul] at ih ⊢
    rw [pow_succ m, pow_succ m', pow_succ (θ m m' x), mul_pow]
    apply Additive.ofMul.injective
    have ih' := congrArg Additive.ofMul ih
    have c' := congrArg Additive.ofMul c
    simp only [ofMul_mul] at ih' c' ⊢
    linear_combination (norm := abel) ih' + c'

theorem quo_one (k : ℕ) (b : A) : quo θ k 1 b = 1 := by
  rw [quo, h.N_one, inv_one, _root_.mul_one]
  exact Finset.prod_eq_one fun _ _ => h.face₂ _ _

theorem quo_mul_left {k : ℕ} {x x' : A} (hx : x ^ k = 1) (b : A) :
    quo θ k (x * x') b * θ x x' (b ^ k) = quo θ k x b * quo θ k x' b := by
  have e₁ := cubN_mul_left h k x x' b
  have e₂ := h.N_add k 1 b x x'
  rw [hx, h.face] at e₁
  rw [h.face, _root_.one_mul, h.s01 b, h.s12 x b, h.s01 (b ^ k), h.s12 x (b ^ k)] at e₂
  apply Additive.ofMul.injective
  have a₁ := congrArg Additive.ofMul e₁
  have a₂ := congrArg Additive.ofMul e₂
  simp only [quo, ofMul_mul, ofMul_inv, ofMul_one] at a₁ a₂ ⊢
  linear_combination (norm := abel) a₁ - a₂

theorem quo_mul_right {k : ℕ} {x : A} (hx : x ^ k = 1) (b b' : A) :
    quo θ k x (b * b') * θ x (b ^ k) (b' ^ k) = quo θ k x b * quo θ k x b' := by
  have e₁ := cubN_mul_left h k b b' x
  have e₂ := h.N_add k 1 x b b'
  rw [hx, h.face, _root_.one_mul, h.face] at e₂
  rw [h.s12 b, h.s01 b, h.s12 (b ^ k), h.s01 (b ^ k)] at e₁
  apply Additive.ofMul.injective
  have a₁ := congrArg Additive.ofMul e₁
  have a₂ := congrArg Additive.ofMul e₂
  simp only [quo, ofMul_mul, ofMul_inv, ofMul_one] at a₁ a₂ ⊢
  linear_combination (norm := abel) a₂ - a₁

end Alg

variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {n : ℕ}

theorem val_cubAtT {T : Over (Sp R)} {y : T.left} {J} (hJ : Good D.P.L y J) (x x' w : T ⟶ D.P.A) :
    val (DegPre.cubAtT D T x x' w) (𝟙 _) y J = th D y J x x' w := by
  have := val_cub D.cub (𝟙 T) hJ x x' w
  rwa [Category.id_comp, Category.id_comp, Category.id_comp] at this

theorem prod_gtT {T : Over (Sp R)} (b : T ⟶ D.P.A) (χ : D.X) {U : Type} [CommGroup U] (h : (T.left ⟶ D.P.A.left) → U) :
    ∏ i, h (DegPre.gtφT D T b χ i) ^ DegPre.gtε i =
      (h (cP D _ χ * b).left)⁻¹ * h (cP D _ χ).left * h b.left * (h (1 : T ⟶ D.P.A).left)⁻¹ := by
  rw [Fin.prod_univ_four]
  show h (cP D _ χ * b).left ^ (-1 : ℤ) * h (cP D _ χ).left ^ (1 : ℤ) * h b.left ^ (1 : ℤ) *
    h (1 : T ⟶ D.P.A).left ^ (-1 : ℤ) = _
  simp only [zpow_neg, zpow_one]

variable (hc : ∀ y, D.c y ^ n = 1)
include hc

theorem cPoint_pow_eq_one (T : Over (Sp R)) (χ : D.X) : cP D T χ ^ n = 1 :=
  (cPoint_nsmul D T n χ).symm.trans (GlobalTheory.TauTwist.cPoint_nsmul_eq_one hc T χ)

theorem exists_coord (T : Over (Sp R)) (b : T ⟶ D.P.A) (χ : D.X) :
    ∃ t : LB.Gen (LB.LinComb D.P.L (DegPre.gtφT D T (b ^ n) χ) DegPre.gtε), t.IsGen ∧
      ∀ (T' : Over (Sp R)) (ρ : T' ⟶ T) (z : T'.left) (J), Good D.P.L z J →
        val t ρ.left z J = quo (th D z J) n (cP D T' χ) (ρ ≫ b) := by
  obtain ⟨t, ht, hv⟩ := exists_cubN D.cub 1 (cP D T χ) b n
  obtain ⟨u, hu, hw⟩ := exists_cubN D.cub 1 b (cP D T χ) n
  obtain ⟨t', ht', hv'⟩ := exists_gen D.P.isLB (φ' := DegPre.gtφT D T (b ^ n) χ) (ε' := DegPre.gtε) (fun U _ h => by
      rw [prod_gtT, cPoint_pow_eq_one hc, mul_comm (cP D T χ) (b ^ n), mul_comm b (cP D T χ)]
      apply Additive.ofMul.injective
      simp [Fintype.prod_sum_type, Fin.prod_univ_succ, ofMul_mul, ofMul_inv, ofMul_zpow, ofMul_pow]
      module) (LB.mulGen D.P.L _ _ _ _ t (LB.invGen D.P.L _ _ u))
    (mulGen_isGen _ _ _ _ _ _ _ ht (invGen_isGen _ _ _ _ hu))
  refine ⟨t', ht', fun T' ρ z J hJ => (hv' _ _ z J hJ).trans ((val_mul hJ _ _ _).trans
    ((congrArg₂ (· * ·) (hv T' ρ z J hJ) ((val_inv _ _).trans (congrArg (·⁻¹) (hw T' ρ z J hJ)))).trans ?_))⟩
  rw [MonObj.comp_one, comp_cP]
  rfl

theorem val_coord (T : Over (Sp R)) (b : T ⟶ D.P.A) (χ : D.X) {z : T.left} {J} (hJ : Good D.P.L z J) :
    val (exists_coord hc T b χ).choose (𝟙 _) z J = quo (th D z J) n (cP D T χ) b := by
  have := (exists_coord hc T b χ).choose_spec.2 T (𝟙 T) z J hJ
  rwa [Category.id_comp] at this

def liftPt (T : Over (Sp R)) (b : T ⟶ D.P.A) : GtPt D T where
  b := b ^ n
  s χ := (exists_coord hc T b χ).choose
  isGen χ := (exists_coord hc T b χ).choose_spec.1
  s_zero := corr_of_val D.P.isLB fun y J hJ => (val_coord hc T b 0 hJ).trans (Eq.trans (by
    rw [cPoint_zero]; exact quo_one (isCub_cubV D.cub hJ) n b) (val_one _).symm)
  mult χ χ' := corr_of_val D.P.isLB fun y J hJ =>
    (val_mul hJ _ _ _).trans ((congrArg₂ (· * ·) (val_coord hc T b _ hJ) (val_cubAtT hJ _ _ _)).trans (Eq.trans (by
      rw [cPoint_add]; exact quo_mul_left (isCub_cubV D.cub hJ) (cPoint_pow_eq_one hc T χ) b)
      ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) (val_coord hc T b _ hJ) (val_coord hc T b _ hJ))).symm))

theorem isSplit_liftPt : IsSplit D n (liftPt hc) := by
  refine ⟨fun _ _ => rfl, fun T b b' => ⟨mul_pow b b' n, fun χ => corr_of_val D.P.isLB fun y J hJ => ?_⟩,
    fun T T' h b => ⟨?_, fun χ => corr_of_val D.P.isLB fun y J hJ => ?_⟩⟩
  · exact (val_mul hJ _ _ _).trans ((congrArg₂ (· * ·) (val_coord hc T _ _ hJ) (val_cubAtT hJ _ _ _)).trans
      ((quo_mul_right (isCub_cubV D.cub hJ) (cPoint_pow_eq_one hc T χ) b b').trans
      ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) (val_coord hc T b _ hJ) (val_coord hc T b' _ hJ))).symm))
  · exact congrArg (fun q : T' ⟶ D.P.A => q.left) (map_pow (preHom h) b n).symm
  · refine (val_coord hc T' _ _ hJ).trans (Eq.trans ?_ (val_pull hJ _ _ _).symm)
    rw [Category.id_comp]
    exact ((exists_coord hc T b χ).choose_spec.2 T' h y J hJ).symm

end GlobalTheory.ArcCM.Split

namespace GlobalTheory.ArcCM

open AlgebraicGeometry CategoryTheory MonObj ReciprocityTheory.ChartRestriction.G

theorem exists_isSplit : Known → ∀ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] (D₀ : Out.DegPre R) (n : ℕ),
    0 < n → (∀ y, D₀.c y ^ n = 1) → ∃ sB, IsSplit D₀ n sB :=
  fun _ _ _ _ _ _ _ _ hc => ⟨_, Split.isSplit_liftPt hc⟩

end GlobalTheory.ArcCM
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.FderivStarStarZero
section
noncomputable section

namespace GlobalTheory.ArchConj

section Diff

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.L2.Pj.QAt.Arch GlobalTheory.IndefiniteRowSideFullHecke.L2SquaredNorms
open GlobalTheory.ArchMetricCompare

attribute [local instance] Over.cartesianMonoidalCategory

theorem fderiv_star_star_zero {g : ℕ} (F : (Fin g → ℂ) → ℂ) (w : Fin g → ℂ) :
    fderiv ℂ (star ∘ F ∘ star) 0 (star w) = star (fderiv ℂ F 0 w) := by
  by_cases hF : DifferentiableAt ℂ F 0
  · have d := hF.hasFDerivAt.star_star
    rw [star_zero] at d
    rw [d.fderiv]
    simp
  · have hG : ¬ DifferentiableAt ℂ (star ∘ F ∘ star) 0 := fun hG => hF (by
      have := hG.star_star
      have e : star ∘ (star ∘ F ∘ star) ∘ star = F := funext fun z => by simp
      rwa [star_zero, e] at this)
    rw [fderiv_zero_of_not_differentiableAt hF, fderiv_zero_of_not_differentiableAt hG]
    simp

variable {A A' : Over (Sp ℂ)} [GrpObj A] [GrpObj A'] {ψ : A'.left ⟶ A.left} (h : IsGrpPullback A' A cj ψ)
variable {X : Scheme.{0}} {L : LB X} {φ : A.left ⟶ X} {g : ℕ} (u : HolUnif A (L.pull φ) g)

theorem cj_isDiff' {t : epsR ℂ ⟶ A} {t' : epsR ℂ ⟶ A'}
    (e : t'.left ≫ ψ = spMap (dualMap (starRingEnd ℂ)) ≫ t.left) {w : Fin g → ℂ} (hd : u.IsDiff w t) :
    (cjUnif h u).IsDiff (star w) t' := by
  haveI := isIso_of_cj h
  intro U hU f
  have e2 : t'.left = spMap (dualMap (starRingEnd ℂ)) ≫ (show Sp (DualNumber ℂ) ⟶ _ from t.left) ≫ inv ψ := by
    rw [← Category.assoc]
    exact (IsIso.eq_comp_inv ψ).2 e
  have h2 : ⊤ ≤ t.left ⁻¹ᵁ (inv ψ ⁻¹ᵁ U) := fun q _ => by
    have := subsingleton_dual ℂ
    have hq := hU (show q ∈ (⊤ : (Sp (DualNumber ℂ)).Opens) from trivial)
    rw [e2] at hq
    rw [Subsingleton.elim (α := PrimeSpectrum (DualNumber ℂ)) q (spMap (dualMap (starRingEnd ℂ)) q)]
    exact hq
  have e1 : (fun z => valAt' ((cjUnif h u).ex z).left U f) =
      star ∘ (fun z => valAt' (u.ex z).left (inv ψ ⁻¹ᵁ U) (((inv ψ).app U).hom f)) ∘ star :=
    funext fun z => cj_val h _ U f
  rw [e1, fderiv_star_star_zero]
  have k : ∀ (y : Sp (DualNumber ℂ) ⟶ A'.left) (hy : ⊤ ≤ y ⁻¹ᵁ U),
      y = spMap (dualMap (starRingEnd ℂ)) ≫ (show Sp (DualNumber ℂ) ⟶ _ from t.left) ≫ inv ψ →
      TangentOrigin.evalPt y U hy f = dualMap (starRingEnd ℂ)
        (TangentOrigin.evalPt (R := DualNumber ℂ) t.left _ h2 (((inv ψ).app U).hom f)) := by
    rintro _ hy rfl
    rw [TangentOrigin.evalPt_spMap_comp _ _ U h2]
    congr 1
  refine (congrArg TrivSqZeroExt.snd (k _ hU e2)).trans ?_
  have e3 := hd _ h2 (((inv ψ).app U).hom f)
  simp only [dualMap, RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk, TrivSqZeroExt.snd_add, TrivSqZeroExt.snd_inl,
    TrivSqZeroExt.snd_inr, zero_add]
  exact congrArg (starRingEnd ℂ) e3

theorem isLieNormAt_conjugate {K : Type} [Field K] {P : Out.PolAV (Sp K)} {σ : K →+* ℂ} {t : epsR K ⟶ P.A} {v : ℝ}
    (H : IsLieNormAt P t σ v) : IsLieNormAt P t (ComplexEmbedding.conjugate σ) v := by
  obtain ⟨P', φ, w, t', h, hw, e, u, Hm, χ, z, hAH, hd, rfl⟩ := H
  have hg := g_eq h
  obtain ⟨A', _, ψ, hc⟩ : ∃ (A' : Over (Sp ℂ)) (_ : GrpObj A') (ψ : A'.left ⟶ P'.A.left),
      IsGrpPullback A' P'.A cj ψ := ⟨_, _, _, isGrpPullback_pullback P'.A cj⟩
  have sq : (spMap (dualMap (starRingEnd ℂ)) ≫ t'.left) ≫ P'.A.hom = (epsR ℂ).hom ≫ cj := by
    rw [Category.assoc, Over.w]
    change Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
    rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
    congr 2
    ext a <;> simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl]
  let t'' : epsR ℂ ⟶ A' := Over.homMk (hc.1.lift _ _ sq) (hc.1.lift_snd _ _ _)
  have e' : t''.left ≫ ψ = spMap (dualMap (starRingEnd ℂ)) ≫ t'.left := hc.1.lift_fst _ _ _
  have h' : IsGrpPullback A' P.A (spMap (ComplexEmbedding.conjugate σ)) (ψ ≫ φ) :=
    (hc.comp h).congr (spMap_conjugate σ) rfl
  have e'' : t''.left ≫ ψ ≫ φ = spMap (dualMap (ComplexEmbedding.conjugate σ)) ≫ t.left := by
    rw [← Category.assoc, e', Category.assoc]
    refine (congrArg _ e).trans ?_
    rw [← Category.assoc]
    congr 1
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    ext a <;> simp [dualMap]
  have hM := pull_isLB P.isLB φ
  have hAH' := cj_isAH hc (carry u P'.isLB hM hw) (carry_isAH _ _ hw hAH)
  have hd' := cj_isDiff' hc (carry u P'.isLB hM hw) e' (w := z) hd
  have hz : (z ⬝ᵥ Hm.mulVec (star z)).re = (star z ⬝ᵥ (Hm.map star).mulVec (star (star z))).re := by
    have := hermSq_star Hm (star z)
    rw [star_star] at this
    exact this.symm
  obtain ⟨A, isAb, g, sm, L, isLB, rigid, sym, ample, ktriv⟩ := P
  obtain rfl : P'.g = g := hg
  exact ⟨pullPol _ h', ψ ≫ φ, idIso _, t'', h', idIso_isGen (pull_isLB isLB _), e'',
    cjUnif hc (carry u P'.isLB hM hw), _, _, star z, hAH', hd', by rw [hz]; rfl⟩

end Diff

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FreeQuotientRank
open Formalism.L2.Pj Formalism.L2.PjFree Formalism.L2.Pj.QAt Formalism.L2.LamCM GlobalTheory GlobalTheory.ArcQ GlobalTheory.LamF GlobalTheory.ArcCM
open scoped LaurentSeries

theorem norms_conj : Known → ∀ (K : Type) [Field K] (P : Out.PolAV (Sp K)) (σ : K →+* ℂ) (v : ℝ), (∀ (rig : LB.Gen (P.L.pull (eSec P.A))) (th : P.L.Sec), Arch.IsThNormAt P rig th σ v → Arch.IsThNormAt P rig th ((starRingEnd ℂ).comp σ) v) ∧ ∀ η' : epsR K ⟶ P.A, Arch.IsLieNormAt P η' σ v → Arch.IsLieNormAt P η' ((starRingEnd ℂ).comp σ) v :=
  fun _ _ _ P σ v => ⟨fun rig th H => (ArchMetricCompare.isL2Sq_iff_isThNormAt P rig _ th v).1
    (ArchMetricCompare.isL2Sq_conjugate_embedding ((ArchMetricCompare.isL2Sq_iff_isThNormAt P rig σ th v).2 H)),
    fun _ H => isLieNormAt_conjugate H⟩

end GlobalTheory.ArchConj
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.FjEqZeroIffOfSameExp
section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FreeQuotientRank
open Formalism.L2.Pj Formalism.L2.PjFree Formalism.L2.Pj.QAt Formalism.L2.LamCM GlobalTheory GlobalTheory.ArcQ GlobalTheory.LamF GlobalTheory.ArcCM
open scoped LaurentSeries
open scoped Matrix

namespace GlobalTheory.FrameMatch

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem flow_lact_rmul (X : Data E r) (gm : GL (Fin r) E)
    (hgm : ∀ u v, herm X.Gm ((gm : Matrix (Fin r) (Fin r) E) *ᵥ u) ((gm : Matrix (Fin r) (Fin r) E) *ᵥ v) =
      herm X.Gm u v) (ξ : Fin r → E) (s : X.Ψ → ℂ) (x b : Frame X.Ψ r) :
    X.flow ((gm : Matrix (Fin r) (Fin r) E) *ᵥ ξ) s (rmul (lact gm x) b) = rmul (lact gm (X.flow ξ s x)) b := by
  funext τ
  have key : X.flowMat ((gm : Matrix (Fin r) (Fin r) E) *ᵥ ξ) τ (s τ) * (gm : Matrix (Fin r) (Fin r) E).map τ.1 =
      (gm : Matrix (Fin r) (Fin r) E).map τ.1 * X.flowMat ξ τ (s τ) := by
    refine Matrix.ext_of_mulVec_single fun i => ?_
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, EmbeddingHermitianPairs.flowMat_mulVec, EmbeddingHermitianPairs.flowMat_mulVec,
      GlobalTheory.PerMove.emb_mulVec, GlobalTheory.PerMove.hermC_unitary _ _ _ hgm, Matrix.mulVec_add, Matrix.mulVec_smul]
  change X.flowMat _ τ (s τ) * ((gm : Matrix (Fin r) (Fin r) E).map τ.1 * mat x τ * mat b τ) =
    (gm : Matrix (Fin r) (Fin r) E).map τ.1 * (X.flowMat ξ τ (s τ) * mat x τ) * mat b τ
  rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, key, Matrix.mul_assoc (_ : Matrix (Fin r) (Fin r) ℂ) _ (mat x τ)]

theorem fj_lact_rmul (X : Data E r) {la : Wt X.Ψ r} {P : Frame X.Ψ r → ℂ} (hP : X.IsSec la P) {gm : GL (Fin r) E}
    (hgm : gm ∈ X.Γ) {ξ : Fin r → E} (hξ : herm X.Gm ξ ξ = 0) (ν : X.Ψ → ℝ) {x b : Frame X.Ψ r} (hx : x ∈ X.dom)
    (hb : b ∈ Bor X.Ψ r) :
    X.fj la ((gm : Matrix (Fin r) (Fin r) E) *ᵥ ξ) ν P (rmul (lact gm x) b) =
      bchar la b * X.χ la gm * X.fj la ξ ν P x := by
  have h : ∀ s : X.Ψ → ℝ, P (X.flow ((gm : Matrix (Fin r) (Fin r) E) *ᵥ ξ) (fun τ => (s τ : ℂ)) (rmul (lact gm x) b)) =
      bchar la b * X.χ la gm * P (X.flow ξ (fun τ => (s τ : ℂ)) x) := fun s => by
    have h1 : X.flow ξ (fun τ => (s τ : ℂ)) x ∈ X.dom := TransvectionPeriodicity.flow_real_mem_dom X hξ s x hx
    rw [flow_lact_rmul X gm (X.Γ_stab gm hgm).1, hP.2.1 _ ((AR.Up.PairUnfoldPf.lact_mem_dom_iff X hgm _).2 h1) b hb,
      hP.2.2 gm hgm _ h1, _root_.mul_assoc]
  unfold Data.fj
  split_ifs
  · simp only [h, _root_.mul_assoc (bchar la b * X.χ la gm), MeasureTheory.integral_const_mul]
    ring
  · simp
  · simp

theorem row_eq_of_lattice (X : Data E r) (τ : E →+* ℂ) (A B : Matrix (Fin r) (Fin r) ℂ) (a : Fin r)
    (h : ∀ v ∈ X.Λ, (A *ᵥ Data.emb τ v) a = (B *ᵥ Data.emb τ v) a) (j : Fin r) : A a j = B a j := by
  obtain ⟨d, hd, hv⟩ := HermitianTraceFormVanishing.exists_smul_mem (R := 𝓞 E) (F := E) X.Λ (x := Pi.single j 1)
    (by rw [X.Λ_span]; trivial)
  have h2 := h _ hv
  have hemb : Data.emb τ (d • (Pi.single j 1 : Fin r → E)) = τ d • (Pi.single j 1 : Fin r → ℂ) := by
    funext k
    by_cases hk : k = j <;> simp [Data.emb, Algebra.smul_def, hk]
  rw [hemb, Matrix.mulVec_smul, Matrix.mulVec_smul] at h2
  simp only [Pi.smul_apply, smul_eq_mul, Matrix.mulVec_single_one, Matrix.col_apply] at h2
  refine mul_left_cancel₀ ?_ h2
  simpa using hd

theorem exists_bor (X : Data E r) {y y' : Frame X.Ψ r} (hy : y ∈ X.dom) (hy' : y' ∈ X.dom) (q : ℕ)
    (h1 : ∀ τ (a : Fin r), (a : ℕ) < q → FD.col (mat y' τ) a = FD.col (mat y τ) a)
    (h2 : ∀ τ (a : Fin r), ¬ (a : ℕ) < q → ∀ j, (mat y' τ)⁻¹ a j = (mat y τ)⁻¹ a j) :
    ∃ b ∈ Bor X.Ψ r, y' = rmul y b := by
  refine ⟨fun τ => ((mat y τ)⁻¹ * mat y' τ : Matrix (Fin r) (Fin r) ℂ), fun τ => ⟨?_, fun a c hca => ?_⟩, ?_⟩
  · change ((mat y τ)⁻¹ * mat y' τ).det ≠ 0
    rw [Matrix.det_mul]
    exact mul_ne_zero (Matrix.isUnit_nonsing_inv_det _ (hy τ).1.isUnit).ne_zero (hy' τ).1
  · change ((mat y τ)⁻¹ * mat y' τ) a c = 0
    by_cases ha : (a : ℕ) < q
    · have h3 := congrFun (congrFun (Matrix.nonsing_inv_mul (mat y τ) (hy τ).1.isUnit) a) c
      rw [Matrix.one_apply_ne hca.ne'] at h3
      rw [← h3, Matrix.mul_apply, Matrix.mul_apply]
      exact Finset.sum_congr rfl fun j _ => congrArg _ (congrFun (h1 τ c (lt_trans hca ha)) j)
    · have h3 := congrFun (congrFun (Matrix.nonsing_inv_mul (mat y' τ) (hy' τ).1.isUnit) a) c
      rw [Matrix.one_apply_ne hca.ne'] at h3
      rw [← h3, Matrix.mul_apply, Matrix.mul_apply]
      exact Finset.sum_congr rfl fun j _ => by rw [h2 τ a ha j]
  · funext τ
    change mat y' τ = mat y τ * ((mat y τ)⁻¹ * mat y' τ)
    rw [Matrix.mul_nonsing_inv_cancel_left _ _ (hy τ).1.isUnit]

variable {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l}

theorem exists_isometry {σ' : KA l →+* ℂ} {g : ℕ} {ty : Fin g → (E →+* ℂ)} (F : FamilyUnif Xo σ' ty) (i : Fin F.n)
    (P P' : (F.Di i).La →+ (Fin g → ℂ)) (hP : IsPeriod (F.Di i) ty P) (hP' : IsPeriod (F.Di i) ty P')
    (hu : F.u i P = F.u i P') (hex : ∀ z, (F.ex i P z).left = (F.ex i P' z).left) :
    ∃ gam : (F.Di i).La ≃ₗ[𝓞 E] (F.Di i).La, (∀ a, P' (gam a) = P a) ∧
      (∀ a b, (F.Di i).EF (gam a) (gam b) = (F.Di i).EF a b) ∧ ∀ a, ∃ e, gam a = a + l.M • e := by
  obtain ⟨h, gam, hh, hPh, hiso, hM, -⟩ := GlobalTheory.familyUnif_exp_unique E H Dw l Xo σ' g ty F i i P P' hP hP' hu
  haveI := hP'.2.2.1
  have h1 : ∀ z, h z = z := fun z => sub_eq_zero.1 <|
    GlobalTheory.ExpUniqFamily.linear_eq_zero_of_discrete P'.range (h.toLinearMap - LinearMap.id) (fun z =>
      (F.ex_ker i P' hP' _).1 <| (GlobalTheory.ExpUniqFamily.eq_iff_sub (F.ex i P') (F.ex_add i P' hP') _ _).1
        (Over.OverMorphism.ext ((hh z).trans (hex z)))) z
  refine ⟨gam, fun a => (hPh a).trans (h1 _), hiso,
    GlobalTheory.LevelHalf.trivial_mod_of_trivial_on_half E H (F.Di i) l gam hiso fun a ha => ?_⟩
  refine Submodule.smul_induction_on ha ?_ ?_
  · intro v hv b _
    obtain ⟨c, e, rfl⟩ := F.t_surj i b
    obtain ⟨e₁, he₁⟩ := hM (v • c) (Submodule.smul_mem_smul hv Submodule.mem_top)
    obtain ⟨m, hm⟩ : l.M ∣ l.M' := Nat.dvd_lcm_left _ _
    refine ⟨e₁ + m • (gam (v • e) - v • e), ?_⟩
    rw [smul_add, ← map_smul, smul_comm v, map_add, he₁, map_nsmul, hm, smul_add, smul_smul, smul_sub]
    abel
  · rintro x y ⟨e, he⟩ ⟨e', he'⟩
    exact ⟨e + e', by rw [map_add, he, he', smul_add]; abel⟩

variable {c : Coeff l} {σ : c.F →+* ℂ} {U : Unf Xo c σ r} (Uw : UnfWit U)

theorem comp_eq (hU : IsUnf U) {k k' : U.Comp} (x : (U.X k).dom) (x' : (U.X k').dom)
    (hu : Uw.F.u (Uw.ik k) (Uw.Pm k x) = Uw.F.u (Uw.ik k') (Uw.Pm k' x'))
    (hex : ∀ z, (Uw.F.ex (Uw.ik k) (Uw.Pm k x) z).left = (Uw.F.ex (Uw.ik k') (Uw.Pm k' x') z).left) : k' = k := by
  have hbor := GlobalTheory.CompInj.frBor_of_eq (U.un k x) (U.un k' x')
    (((Uw.lie k' x').1.trans hu.symm).trans (Uw.lie k x).1.symm) fun τ i => by
      have h' := (Uw.lie k' x').2 τ i
      simp only [← hex] at h'
      exact ((GlobalTheory.isDerivAt0_ex_isTanAt E H Dw l Xo _ _ _ Uw.F _ _ (Uw.period k x)).2.1 _).unique h'
        ((Uw.lie k x).2 τ i)
  obtain ⟨gm, -, b, -, h⟩ := (hU.2.2.2.1 k k' _ _).1 hbor
  exact congrArg Sigma.fst h

theorem exists_move (hσ : GoodEmb c σ) (hU : IsUnf U) (hpr : GlobalTheory.FrameNorm.HasPrinc U l.M) (k : U.Comp)
    (x x' : (U.X k).dom) (hu : Uw.F.u (Uw.ik k) (Uw.Pm k x) = Uw.F.u (Uw.ik k) (Uw.Pm k x'))
    (hex : ∀ z, (Uw.F.ex (Uw.ik k) (Uw.Pm k x) z).left = (Uw.F.ex (Uw.ik k) (Uw.Pm k x') z).left) :
    ∃ gm ∈ (U.X k).Γ, ∃ b ∈ Bor (U.X k).Ψ r, x'.1 = rmul (lact gm x.1) b ∧ ∀ t t', Uw.Pm k x t = Uw.Pm k x' t' →
      (Uw.φ k t' : Fin r → E) = (gm : Matrix (Fin r) (Fin r) E) *ᵥ (Uw.φ k t : Fin r → E) := by
  obtain ⟨gam, hP, hiso, hM⟩ := exists_isometry Uw.F _ _ _ (Uw.period k x) (Uw.period k x') hu hex
  let φ : (Uw.F.Di (Uw.ik k)).La →ₗ[𝓞 E] (Fin r → E) := (U.X k).Λ.subtype ∘ₗ (Uw.φ k).toLinearMap
  have hrange : LinearMap.range φ = (U.X k).Λ := by
    rw [LinearMap.range_comp, LinearEquiv.range, Submodule.map_top, Submodule.range_subtype]
  have hφ : Function.Injective φ ∧ Submodule.span E (Set.range φ) = ⊤ ∧ _ ∧ _ ∧ _ :=
    ⟨Subtype.val_injective.comp (Uw.φ k).injective, by rw [← LinearMap.coe_range, hrange]; exact (U.X k).Λ_span,
      (U.X k).Gm_herm, (U.X k).Gm_det, Uw.iso k⟩
  obtain ⟨gm, hgm, hgmφ⟩ := GlobalTheory.IsoExt.exists_unitary_of_isometry E H _ _ r (-(U.X k).ξ0) (U.X k).Gm φ φ gam
    (by rw [HermitianTraceFormVanishing.cc_neg, (U.X k).ξ0_im]) hφ hφ hiso
  have hg : ∀ a, (Uw.φ k (gam a) : Fin r → E) = (gm : Matrix (Fin r) (Fin r) E) *ᵥ (Uw.φ k a : Fin r → E) := hgmφ
  have hs : ∀ w ∈ (U.X k).Λ, ∃ a, (Uw.φ k a : Fin r → E) = w := fun w hw =>
    ⟨(Uw.φ k).symm ⟨w, hw⟩, by rw [LinearEquiv.apply_symm_apply]⟩
  have hΓ : gm ∈ (U.X k).Γ := by
    refine hpr k gm ⟨hgm, fun w => ⟨fun hw => ?_, fun hw => ?_⟩⟩ fun w hw => ?_
    · obtain ⟨a, rfl⟩ := hs w hw
      rw [← hg]
      exact (Uw.φ k _).2
    · obtain ⟨a, ha⟩ := hs _ hw
      obtain ⟨a, rfl⟩ := gam.surjective a
      rw [hg] at ha
      rw [← Matrix.mulVec_injective_iff_isUnit.2 gm.isUnit ha]
      exact (Uw.φ k _).2
    · obtain ⟨a, rfl⟩ := hs w hw
      obtain ⟨e, he⟩ := hM a
      refine ⟨_, (Uw.φ k e).2, ?_⟩
      rw [← hg, he, map_add, map_nsmul, Nat.cast_smul_eq_nsmul]
      simp
  have hy : lact gm x.1 ∈ (U.X k).dom := (AR.Up.PairUnfoldPf.lact_mem_dom_iff (U.X k) hΓ _).2 x.2
  obtain ⟨idx, -, -, hper⟩ := GlobalTheory.ArcFlow.exists_idx Uw hσ hU k
  have key : ∀ w ∈ (U.X k).Λ, ∀ j, perFr (U.X k) x'.1 w (relab c σ (Uw.e j).1) (Uw.e j).2 =
      perFr (U.X k) (lact gm x.1) w (relab c σ (Uw.e j).1) (Uw.e j).2 := fun w hw j => by
    obtain ⟨a, rfl⟩ := hs w hw
    obtain ⟨a, rfl⟩ := gam.surjective a
    rw [← Uw.Pm_eq, hP, hg, GlobalTheory.PerGam.perFr_lact _ gm hgm, Uw.Pm_eq]
  obtain ⟨b, hb, hxb⟩ := exists_bor (U.X k) hy x'.2 Dw.q
    (fun τ a ha => GlobalTheory.ArcFlow.eq_of_hermC_lattice (U.X k) τ.1 _ _ fun w hw => by
      have h1 := key w hw (idx.symm (τ, a))
      rw [hper, hper] at h1
      simpa only [Equiv.apply_symm_apply, if_pos ha] using h1)
    (fun τ a ha => row_eq_of_lattice (U.X k) τ.1 _ _ a fun w hw => by
      have h1 := key w hw (idx.symm (τ, a))
      rw [hper, hper] at h1
      simpa only [Equiv.apply_symm_apply, if_neg ha] using h1)
  refine ⟨gm, hΓ, b, hb, hxb, fun t t' ht => ?_⟩
  rw [← hg, (Uw.period k x').2.1 ((hP t).trans ht)]

theorem fj_eq_zero_iff_of_same_exp : Known → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (r : ℕ) (U : Unf Xo c σ r) (Uw : UnfWit U) (k k' : U.Comp) (x : (U.X k).dom) (x' : (U.X k').dom) (t : (Uw.F.Di (Uw.ik k)).La) (t' : (Uw.F.Di (Uw.ik k')).La) (a' : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (ν₀ : E), GoodEmb c σ → IsUnf U → GlobalTheory.FrameNorm.HasPrinc U l.M → Dom a' n → (∀ k, ∀ gm ∈ (U.X k).Γ, (U.X k).χ (laU U a' n k) gm = 1) → (U.X k).IsIso (Uw.φ k t : Fin r → E) → Uw.F.u (Uw.ik k) (Uw.Pm k x) = Uw.F.u (Uw.ik k') (Uw.Pm k' x') → (∀ z, (Uw.F.ex (Uw.ik k) (Uw.Pm k x) z).left = (Uw.F.ex (Uw.ik k') (Uw.Pm k' x') z).left) → Uw.Pm k x t = Uw.Pm k' x' t' → ∀ F ∈ sec Xo c a' n, ((U.X k).fj (laU U a' n k) (Uw.φ k t : Fin r → E) (fun τ => (τ.1 ν₀).re) (rdU U F k) x.1 = 0 ↔ (U.X k').fj (laU U a' n k') (Uw.φ k' t' : Fin r → E) (fun τ => (τ.1 ν₀).re) (rdU U F k') x'.1 = 0) := by
  intro _ E _ _ _ H Dw l Xo c σ r U Uw k k' x x' t t' a' n ν₀ hσ hU hpr hD hχ hiso hu hex ht F hF
  obtain rfl := comp_eq Uw hU x x' hu hex
  obtain ⟨gm, hgm, b, hb, hxb, hφ⟩ := exists_move Uw hσ hU hpr k' x x' hu hex
  rw [hφ t t' ht, hxb, fj_lact_rmul (U.X k') (hU.2.2.2.2.1 a' n hD F hF k') hgm hiso.2.1 _ x.2 hb, hχ k' gm hgm,
    _root_.mul_one,
    mul_eq_zero, or_iff_right (AR.Up.PairUnfoldPf.bchar_ne (U.X k') hb _)]

end GlobalTheory.FrameMatch
end

