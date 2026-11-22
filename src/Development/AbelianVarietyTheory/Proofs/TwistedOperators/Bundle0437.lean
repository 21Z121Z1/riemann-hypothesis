import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0428
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0064
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IntegralFrameChangeIntegralInvertibleMatrix
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsSmoothModerateOfIsAutFunSm
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0214
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.SqNormIntegralFundamentalDomainEqL2NormSq
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittDecompSymplInclIsotropicInclAnisotropic
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0024
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeisenbergTranslateThetaContinuousDifferentiable
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0271
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0154
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0002
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0006
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0274
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0257
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0129
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1533
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0152

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LieLatticeOnto
section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.ThetaTrace GlobalTheory.HeckeFrCompare GlobalTheory.PlaceInt
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.HkIntegral

namespace GlobalTheory.HkLie

open GlobalTheory.IntRebase

section Gen

variable {X0 : Scheme.{0}} {S : Type} [CommRing S] (x0 : Sp S ⟶ X0) {G G' : Over X0} [GrpObj G] [GrpObj G']

theorem smT_post' (a : S) (v : overAt x0 (DualNumber S) ⟶ G) (φ : G ⟶ G') :
    smT x0 a (v ≫ φ) = smT x0 a v ≫ φ := (Category.assoc _ _ _).symm

theorem smT_comm (a b : S) (v : overAt x0 (DualNumber S) ⟶ G) :
    smT x0 a (smT x0 b v) = smT x0 b (smT x0 a v) := by
  rw [smT_smT, smT_smT, _root_.mul_comm]

theorem tan_image (q : S) (v : overAt x0 (DualNumber S) ⟶ G) (h0 : smT x0 0 v = 1) (φ : G ⟶ G') [IsMonHom φ] :
    smT x0 0 (smT x0 q (v ≫ φ)) = 1 := by
  rw [smT_comm, smT_post', h0, MonObj.one_comp, smT_one']

theorem smT_natCast (v : overAt x0 (DualNumber S) ⟶ G) (h0 : smT x0 0 v = 1) (n : ℕ) :
    smT x0 (n : S) v = v ^ n := by
  induction n with
  | zero => simpa using h0
  | succ n ih => rw [Nat.cast_succ, smT_add x0 v h0, ih, smT_unit, pow_succ]

theorem comp_id_pow {P : Over X0} (v : P ⟶ G) (n : ℕ) : v ≫ (𝟙 G ^ n) = v ^ n := by
  have h := map_pow (IntRebase.preHom (G := G) v) (𝟙 G) n
  have h2 : IntRebase.preHom (G := G) v (𝟙 G) = v := Category.comp_id v
  rw [h2] at h
  exact h

variable [IsCommMonObj G] [IsCommMonObj G']

theorem combT_image {m : ℕ} (q : S) (v : Fin m → (overAt x0 (DualNumber S) ⟶ G)) (a : Fin m → S) (φ : G ⟶ G')
    [IsMonHom φ] : smT x0 q (combT x0 v a ≫ φ) = combT x0 (fun j => smT x0 q (v j ≫ φ)) a := by
  let ph : (overAt x0 (DualNumber S) ⟶ G) →* (overAt x0 (DualNumber S) ⟶ G') :=
    { toFun := fun v => v ≫ φ
      map_one' := MonObj.one_comp φ
      map_mul' := fun u w => MonObj.mul_comp u w φ }
  have h : combT x0 v a ≫ φ = ∏ j, smT x0 (a j) (v j) ≫ φ :=
    map_prod ph (fun j => smT x0 (a j) (v j)) Finset.univ
  rw [h, smT_prod]
  refine Finset.prod_congr rfl fun j _ => ?_
  rw [← smT_post', smT_comm]

theorem mul_eq_one_of_pair {m : ℕ} (p : ℕ) (q : S) (hq : q * p = 1) (U : Fin m → (overAt x0 (DualNumber S) ⟶ G))
    (U' : Fin m → (overAt x0 (DualNumber S) ⟶ G')) (hU' : ∀ j, smT x0 0 (U' j) = 1)
    (huniq : ∀ i (a b : Fin m → S), U' i = combT x0 U' a → U' i = combT x0 U' b → a = b)
    (F : G ⟶ G') (F' : G' ⟶ G) [IsMonHom F] (hF : F' ≫ F = 𝟙 _ ^ (p ^ 2)) (k k' : Matrix (Fin m) (Fin m) S)
    (hk : ∀ i, smT x0 q (U i ≫ F) = combT x0 U' (fun j => k j i))
    (hk' : ∀ i, smT x0 q (U' i ≫ F') = combT x0 U (fun j => k' j i)) : k * k' = 1 := by
  ext j i
  have h1 : smT x0 q (smT x0 q (U' i ≫ F') ≫ F) = U' i := by
    rw [← smT_post', Category.assoc, hF, comp_id_pow, ← smT_natCast x0 _ (hU' i), smT_smT, smT_smT]
    have e : q * q * ((p ^ 2 : ℕ) : S) = 1 := by
      push_cast
      linear_combination (q * p + 1) * hq
    rw [e, smT_unit]
  rw [hk', combT_image, funext hk, combT_combT x0 U' hU'] at h1
  have h2 := congrFun (huniq i _ _ h1.symm (combT_single x0 U' hU' i).symm) j
  rw [Matrix.one_apply, Matrix.mul_apply]
  rw [Pi.single_apply] at h2
  exact h2

end Gen

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l} {c : Coeff l}

theorem exists_coords {V Fr : Type} [CommRing V] [Field Fr] [Algebra V Fr] (io : c.F →+* Fr) {G G' : SAB H (Sp V)}
    (τ : E →+* ℂ) (F : G.G ⟶ G'.G) [IsMonHom F] (hF : ∀ a, G.act.act a ≫ F = F ≫ G'.act.act a) (q : V) {m : ℕ}
    (ub' : Fin m → (epsOver V V ⟶ G'.G))
    (hb : ∀ w : epsOver V V ⟶ G'.G, IsTan w → IsEigV c io G' τ w → ∃! a : Fin m → V, IsComb ub' a w)
    (w : epsOver V V ⟶ G.G) (ht : IsTan w) (he : IsEigV c io G τ w) :
    ∃ a : Fin m → V, IsComb ub' a (kapI ≫ smT (𝟙 (Sp V)) q ((IntRebase.kap ≫ w) ≫ F)) := by
  refine (hb _ (isTan_kapI _ (tan_image _ q _ (smT_zero_kap w ht) F)) ?_).exists
  refine (isEigV_kapI_iff io G' τ _).2 fun a z hz => ?_
  have h1 := (isEigV_kapI_iff io G τ (IntRebase.kap ≫ w)).1 (by rw [kapI_kap_assoc]; exact he) a z hz
  rw [← smT_post', Category.assoc (IntRebase.kap ≫ w), ← hF, ← Category.assoc (IntRebase.kap ≫ w), h1, ← smT_post', smT_comm]

theorem lie_lattice_onto : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (T : CDVR) (io : c.F →+* T.Fr) (y y' : IntFr Xo c T io) (I : IntData Xo c T io y.1) (I' : IntData Xo c T io y'.1) (f : Fib Xo (xOf y) ⟶ Fib Xo (xOf y')) (F : I.G.G ⟶ I'.G.G) (F' : I'.G.G ⟶ I.G.G) (p : ℕ) (v : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → (Sp (DualNumber T.Fr) ⟶ Xo.univ.t.G.left)), IsUnit (p : T.V) → IsMonHom F → IsMonHom F' → Ext I.m1 I.m2 I'.m1 I'.m2 f F → F ≫ F' = 𝟙 _ ^ (p ^ 2) → F' ≫ F = 𝟙 _ ^ (p ^ 2) → (∀ a, I.G.act.act a ≫ F = F ≫ I'.G.act.act a) → (∀ a, I'.G.act.act a ≫ F' = F' ≫ I.G.act.act a) → letI := io.toAlgebra; (∀ τ j, IsLieImageH p f.left (y.1.u τ j) (v τ j)) → ∃ k : ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) T.V, (∀ τ, IsUnit (k τ).det) ∧ ∀ τ i, IsCombAt y'.1.x (y'.1.u τ) (fun j => algebraMap T.V T.Fr (k τ j i)) (v τ i) := by
  intro E _ _ _ H Dw l Xo c T io y y' I I' f F F' p v hp hF hF' hExt _ hFF hl hl'
  let _ := io.toAlgebra
  intro hv
  obtain ⟨q, hq⟩ := hp.exists_left_inv
  choose k hk using fun τ i => exists_coords io τ F hl q (I'.ub τ) (I'.basis τ) (I.ub τ i) (I.tan τ i) (I.eig τ i)
  choose k' hk' using fun τ i => exists_coords io τ F' hl' q (I.ub τ) (I.basis τ) (I'.ub τ i) (I'.tan τ i) (I'.eig τ i)
  refine ⟨fun τ => Matrix.of fun j i => k τ i j, fun τ => ?_, fun τ i => ?_⟩
  · refine Matrix.isUnit_det_of_right_inverse (B := Matrix.of fun j i => k' τ i j) ?_
    refine mul_eq_one_of_pair (𝟙 (Sp T.V)) p q hq (fun i => IntRebase.kap ≫ I.ub τ i) (fun i => IntRebase.kap ≫ I'.ub τ i)
      (fun i => smT_zero_kap _ (I'.tan τ i)) ?_ F F' hFF _ _ (fun i => (isComb_iff _ _ _).1 (hk τ i))
      (fun i => (isComb_iff _ _ _).1 (hk' τ i))
    intro i a b ha hb
    have ha' := (isComb_iff (I'.ub τ) a _).2 ha
    have hb' := (isComb_iff (I'.ub τ) b _).2 hb
    rw [kapI_kap_assoc] at ha' hb'
    exact (I'.basis τ _ (I'.tan τ i) (I'.eig τ i)).unique ha' hb'
  · obtain ⟨ψ, -, hψ, hg⟩ := hExt
    obtain ⟨u, hu1, hu2⟩ := I.lift τ i
    choose u' hu1' hu2' using I'.lift τ
    obtain ⟨w, hw1, hw2, hw3⟩ := hv τ i
    have hqp : algebraMap T.V T.Fr q = (p : T.Fr)⁻¹ := by
      apply eq_inv_of_mul_eq_one_left
      rw [← map_natCast (algebraMap T.V T.Fr), ← map_mul, hq, map_one]
    have hov : u ≫ I.t'.G.hom = spMap (algebraMap T.Fr (DualNumber T.Fr)) := by
      apply GlobalTheory.IntLie.spMap_frac_cancel (V := T.V)
      rw [Category.assoc, ← I.m2.cart.1.w, ← Category.assoc, hu2, Category.assoc, Over.w (I.ub τ i)]
      show spMap _ ≫ spMap _ = _
      rw [GlobalTheory.IntLie.spMap_comp₂, GlobalTheory.IntLie.spMap_comp₂]
      show spMap ((dualMap (algebraMap T.V T.Fr)).comp (algebraMap T.V (DualNumber T.V))) = _
      rw [GlobalTheory.IntLie.dualMap_alg]
    have h := GlobalTheory.IntLie.comb_generic I'.m1 I'.m2 (I'.ub τ) u' hu2' _
      (spMap (epsMul (algebraMap T.V T.Fr q)) ≫ u ≫ ψ.left) (by
        simp only [Over.comp_left, kapI, IntRebase.kap, smT_left, Over.homMk_left, Category.id_comp, Category.assoc]
        rw [hψ, ← Category.assoc u, hu2, Category.assoc, ← Category.assoc, ← Category.assoc (spMap _) (spMap _),
          GlobalTheory.IntLie.spMap_comp₂, GlobalTheory.IntLie.spMap_comp₂, GlobalTheory.IntLie.dualMap_epsMul]) (k τ i) (hk τ i)
    let g : I.t'.G.left ⟶ pullback Xo.univ.t.G.hom (xOf y) := pullback.lift I.m1.φ I.t'.G.hom I.m1.cart.1.w
    let g' : I'.t'.G.left ⟶ pullback Xo.univ.t.G.hom (xOf y') := pullback.lift I'.m1.φ I'.t'.G.hom I'.m1.cart.1.w
    have hgg := hg g g' (pullback.lift_fst _ _ _) (pullback.lift_snd _ _ _) (pullback.lift_fst _ _ _)
      (pullback.lift_snd _ _ _)
    have hw : w = u ≫ g := by
      apply pullback.hom_ext
      · rw [hw1, Category.assoc, pullback.lift_fst, hu1]
      · rw [hw2, Category.assoc, pullback.lift_snd, hov]
    have hg' : g' ≫ pullback.fst _ _ = I'.m1.φ := pullback.lift_fst _ _ _
    have hvv : v τ i = (spMap (epsMul (algebraMap T.V T.Fr q)) ≫ u ≫ ψ.left) ≫ I'.m1.φ := by
      rw [hw3, hqp, hw, ← hg', Category.assoc, Category.assoc, Category.assoc, ← Category.assoc ψ.left, ← hgg,
        Category.assoc]
    rw [funext hu1', ← hvv] at h
    exact h

end GlobalTheory.HkLie
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.MixedThetaSeriesRapidDecay
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct ENNReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm
open scoped Pointwise
open Formalism.IndefR.Datum
open GlobalTheory.Grid

noncomputable section

namespace GlobalTheory.MixWeight

theorem trace_mul_single {m r : ℕ} (M : Matrix (Fin r) (Fin m) ℂ) (i : Fin m) (j : Fin r) (c : ℂ) :
    (M * Matrix.single i j c).trace = M j i * c := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.single_apply]
  rw [Finset.sum_eq_single j (fun b _ hb => Finset.sum_eq_zero fun c' _ => by
    rw [if_neg fun h => hb h.2.symm, mul_zero]) (by simp)]
  rw [Finset.sum_eq_single i (fun b _ hb => by rw [if_neg fun h => hb h.1.symm, mul_zero]) (by simp)]
  simp

theorem norm_le_forms {m r : ℕ} (B : Matrix (Fin r) (Fin m) ℂ) (ξ : ℂ) (hξ : ξ ≠ 0) (i : Fin m) (j : Fin r) :
    ‖B j i‖ ≤ ‖ξ‖⁻¹ * ∑ b : Bool, |2 * (ξ * (B * Matrix.single i j (if b then Complex.I else 1)).trace).re| := by
  have hξn : 0 < ‖ξ‖ := norm_pos_iff.2 hξ
  rw [Fintype.sum_bool]
  simp only [Bool.false_eq_true, ite_true, ite_false, trace_mul_single, mul_one]
  rw [le_inv_mul_iff₀ hξn, ← norm_mul]
  have h1 := Complex.norm_le_abs_re_add_abs_im (ξ * B j i)
  have e1 : |2 * (ξ * (B j i * Complex.I)).re| = 2 * |(ξ * B j i).im| := by
    rw [← mul_assoc, Complex.mul_I_re, abs_mul, abs_neg, abs_two]
  have e2 : |2 * (ξ * B j i).re| = 2 * |(ξ * B j i).re| := by rw [abs_mul, abs_two]
  rw [e1, e2]
  linarith [abs_nonneg (ξ * B j i).re, abs_nonneg (ξ * B j i).im]

theorem sum_norm_le {m r : ℕ} (G : Matrix (Fin m) (Fin m) ℂ) (hG : IsUnit G.det) (ξ : ℂ) (hξ : ξ ≠ 0) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ x : Matrix (Fin m) (Fin r) ℂ,
      ∑ k, ∑ j, ‖x k j‖ ≤ A * ∑ i : Fin m, ∑ j : Fin r, ∑ b : Bool,
        |2 * (ξ * (xᴴ * G * Matrix.single i j (if b then Complex.I else 1)).trace).re| := by
  have hg0 : 0 ≤ ∑ i, ∑ k, ‖G⁻¹ i k‖ := by positivity
  refine ⟨m * (∑ i, ∑ k, ‖G⁻¹ i k‖) * ‖ξ‖⁻¹, by positivity, fun x => ?_⟩
  have hx : x = (xᴴ * G * G⁻¹)ᴴ := by
    rw [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hG, Matrix.mul_one, Matrix.conjTranspose_conjTranspose]
  have hxkj : ∀ k j, ‖x k j‖ ≤ (∑ i, ∑ k, ‖G⁻¹ i k‖) * ∑ i, ‖(xᴴ * G) j i‖ := by
    intro k j
    rw [hx, Matrix.conjTranspose_apply, norm_star, Matrix.mul_apply, ← hx]
    refine (norm_sum_le _ _).trans ?_
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun i _ => ?_
    rw [norm_mul, mul_comm]
    refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
    exact (Finset.single_le_sum (f := fun k' => ‖G⁻¹ i k'‖) (fun _ _ => norm_nonneg _) (Finset.mem_univ k)).trans
      (Finset.single_le_sum (f := fun i' => ∑ k', ‖G⁻¹ i' k'‖) (fun _ _ => by positivity) (Finset.mem_univ i))
  have key : ∑ k, ∑ j, ‖x k j‖ ≤ m * (∑ i, ∑ k, ‖G⁻¹ i k‖) * ‖ξ‖⁻¹ * ∑ i : Fin m, ∑ j : Fin r, ∑ b : Bool,
      |2 * (ξ * (xᴴ * G * Matrix.single i j (if b then Complex.I else 1)).trace).re| := by
    calc ∑ k, ∑ j, ‖x k j‖ ≤ ∑ _k : Fin m, ∑ j, (∑ i, ∑ k, ‖G⁻¹ i k‖) * ∑ i, ‖(xᴴ * G) j i‖ :=
          Finset.sum_le_sum fun k _ => Finset.sum_le_sum fun j _ => hxkj k j
      _ = m * (∑ i, ∑ k, ‖G⁻¹ i k‖) * ∑ j, ∑ i, ‖(xᴴ * G) j i‖ := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, ← Finset.mul_sum, mul_assoc]
      _ = m * (∑ i, ∑ k, ‖G⁻¹ i k‖) * ∑ i, ∑ j, ‖(xᴴ * G) j i‖ := by congr 1; exact Finset.sum_comm
      _ ≤ m * (∑ i, ∑ k, ‖G⁻¹ i k‖) * ∑ i, ∑ j, ‖ξ‖⁻¹ * ∑ b : Bool,
            |2 * (ξ * (xᴴ * G * Matrix.single i j (if b then Complex.I else 1)).trace).re| := by
          gcongr with i _ j _
          exact norm_le_forms _ ξ hξ i j
      _ = _ := by
          rw [mul_assoc ((m : ℝ) * ∑ i, ∑ k, ‖G⁻¹ i k‖) ‖ξ‖⁻¹, Finset.mul_sum (a := ‖ξ‖⁻¹)]
          congr 1
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [Finset.mul_sum]
          rfl
  exact key

end GlobalTheory.MixWeight

namespace GlobalTheory.MixWeight

open GlobalTheory.MixModel

variable {D : D7}

theorem enorm_mixS_le' {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) {V V₀ W : HSp D} {ρ : ℕ}
    (d : HypDec V V₀ ρ) (v : GlobalTheory.Unf.VolM D W.rank ρ) (φ : WO V W → ℂ) (x : Mx D W.rank ρ) (w : WO V₀ W) :
    ‖d.mixS W ψ v.μ v.𝓕 φ x w‖ₑ ≤ GlobalTheory.HeisTaylor.supN φ := by
  simp only [HypDec.mixS, HypDec.integrandS_eq]
  refine (enorm_integral_le_lintegral_enorm _).trans ?_
  calc ∫⁻ a in v.𝓕, ‖ψ (symplOH V W (d.extY W a) (d.extX W x)) * φ (d.extY W a + d.extX W x + d.ext0 W w)‖ₑ ∂v.μ
      ≤ ∫⁻ _ in v.𝓕, GlobalTheory.HeisTaylor.supN φ ∂v.μ := by
        refine lintegral_mono fun a => ?_
        rw [enorm_mul, ← ofReal_norm (ψ _), hψ.1.2.1, ENNReal.ofReal_one, one_mul]
        exact GlobalTheory.HeisTaylor.enorm_le_supN φ _
    _ = _ := by rw [setLIntegral_const, v.covol.2.2, mul_one]

theorem one_add_pow_le {L : ℝ} (hL : 0 ≤ L) (N : ℕ) : (1 + L) ^ N ≤ 2 ^ N * (1 + L ^ N) := by
  first
  | exact @_root_.GlobalTheory.OneAddPowBoundTwistedOperators.one_add_pow_le
  | exact _root_.GlobalTheory.OneAddPowBoundTwistedOperators.one_add_pow_le
  | (apply _root_.GlobalTheory.OneAddPowBoundTwistedOperators.one_add_pow_le <;> assumption)
  | (intros; apply _root_.GlobalTheory.OneAddPowBoundTwistedOperators.one_add_pow_le <;> assumption)
  | (intros; apply @_root_.GlobalTheory.OneAddPowBoundTwistedOperators.one_add_pow_le <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.OneAddPowBoundTwistedOperators.one_add_pow_le ..)

theorem mixS_weight_le : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (θ : InfFam D), IsInfFam θ →
    ∀ (V X S₀ : HSp D) (r : ℕ) (d : GlobalTheory.MixModel.HypDec V S₀ r) (μ' : Measure (Mx D X.rank r))
    (𝓕' : Set (Mx D X.rank r)), IsCovolOne (GlobalTheory.MixModel.ratMx D X.rank r) μ' 𝓕' → ∀ N : ℕ,
    ∃ (k : ℕ) (C : ℝ), 0 ≤ C ∧ ∀ Ψ : WO V X → ℂ, IsThetaFunO ψ V X Ψ → ∀ x : Mx D X.rank r,
      ‖d.mixS X ψ μ' 𝓕' Ψ x 0‖ₑ * ENNReal.ofReal ((1 + ∑ τ, ∑ i, ∑ j, ‖compAt θ τ x i j‖) ^ N) ≤
        ENNReal.ofReal C * GlobalTheory.Size.wordSum (GlobalTheory.Size.heisDer ψ θ) GlobalTheory.HeisTaylor.supN k Ψ := by
  intro D ψ hψ θ hθ V X S₀ r d μ' 𝓕' hμ N
  let v : GlobalTheory.Unf.VolM D X.rank r := ⟨μ', 𝓕', hμ⟩
  let zA : D.what₂.Tau × Fin X.rank × Fin r × Bool → Matrix (Fin X.rank) (Fin r) ℂ :=
    fun a => Matrix.single a.2.1 a.2.2.1 (if a.2.2.2 then Complex.I else 1)
  let ℓ : D.what₂.Tau × Fin X.rank × Fin r × Bool → Mx D X.rank r → ℝ := fun a x =>
    |2 * (tauE D a.1 D.host.xi0 * ((compAt θ a.1 x)ᴴ * gramAt D X a.1 * zA a).trace).re|
  choose Z hZ using fun a : D.what₂.Tau × Fin X.rank × Fin r × Bool =>
    GlobalTheory.Unf.norm_mixS_dRho_ge D ψ hψ θ hθ V S₀ X r d v a.1 (zA a)
  have laws := GlobalTheory.Unf.SupFin.supSob_laws D ψ hψ θ hθ V X
  choose C hC using fun a : D.what₂.Tau × Fin X.rank × Fin r × Bool => (laws.2.1 a.1 (Z a)).2
  let K : NNReal := ∑ a, C a
  have hL0 : ∀ x, 0 ≤ ∑ a, ℓ a x := fun x => Finset.sum_nonneg fun a _ => abs_nonneg _

  have hpow : ∀ n : ℕ, ∀ f : WO V X → ℂ, IsThetaFunO ψ V X f → ∀ x,
      ENNReal.ofReal ((∑ a, ℓ a x) ^ n) * ‖d.mixS X ψ μ' 𝓕' f x 0‖ₑ ≤
        ((K ^ n : NNReal) : ENNReal) * GlobalTheory.Unf.supSob ψ θ n f := by
    intro n
    induction n with
    | zero =>
      intro f hf x
      rw [pow_zero, ENNReal.ofReal_one, one_mul, pow_zero, ENNReal.coe_one, one_mul]
      exact (enorm_mixS_le' hψ d v f x 0).trans (GlobalTheory.Size.wordSum_zero _ _ _).ge
    | succ n ih =>
      intro f hf x
      have step : ∀ a, ENNReal.ofReal ((∑ a, ℓ a x) ^ n) * (ENNReal.ofReal (ℓ a x) * ‖d.mixS X ψ μ' 𝓕' f x 0‖ₑ) ≤
          ((K ^ n : NNReal) : ENNReal) * ((C a : ENNReal) * GlobalTheory.Unf.supSob ψ θ (n + 1) f) := by
        intro a
        have hg := GlobalTheory.OrientedHeis.theta_dRho hθ hψ a.1 (Z a) hf
        have h1 : ENNReal.ofReal (ℓ a x) * ‖d.mixS X ψ μ' 𝓕' f x 0‖ₑ ≤
            ‖d.mixS X ψ μ' 𝓕' (dRho (heisO ψ V X) θ a.1 (Z a) f) x 0‖ₑ := by
          rw [← ofReal_norm, ← ofReal_norm, ← ENNReal.ofReal_mul (abs_nonneg _)]
          exact ENNReal.ofReal_le_ofReal (hZ a f hf x 0)
        calc _ ≤ ENNReal.ofReal ((∑ a, ℓ a x) ^ n) *
              ‖d.mixS X ψ μ' 𝓕' (dRho (heisO ψ V X) θ a.1 (Z a) f) x 0‖ₑ := by gcongr
          _ ≤ ((K ^ n : NNReal) : ENNReal) * GlobalTheory.Unf.supSob ψ θ n (dRho (heisO ψ V X) θ a.1 (Z a) f) := ih _ hg x
          _ ≤ _ := by gcongr; exact hC a n f hf
      calc ENNReal.ofReal ((∑ a, ℓ a x) ^ (n + 1)) * ‖d.mixS X ψ μ' 𝓕' f x 0‖ₑ
          = ∑ a, ENNReal.ofReal ((∑ a, ℓ a x) ^ n) * (ENNReal.ofReal (ℓ a x) * ‖d.mixS X ψ μ' 𝓕' f x 0‖ₑ) := by
            rw [pow_succ, ENNReal.ofReal_mul (pow_nonneg (hL0 x) n),
              ENNReal.ofReal_sum_of_nonneg (fun a _ => abs_nonneg _), Finset.mul_sum, Finset.sum_mul]
            refine Finset.sum_congr rfl fun a _ => ?_
            ring
        _ ≤ ∑ a, ((K ^ n : NNReal) : ENNReal) * ((C a : ENNReal) * GlobalTheory.Unf.supSob ψ θ (n + 1) f) :=
            Finset.sum_le_sum fun a _ => step a
        _ = ((K ^ (n + 1) : NNReal) : ENNReal) * GlobalTheory.Unf.supSob ψ θ (n + 1) f := by
            rw [← Finset.mul_sum, ← Finset.sum_mul, pow_succ]
            simp only [K, ENNReal.coe_mul, ENNReal.ofNNReal_finsetSum]
            ring

  have hG : ∀ τ : D.what₂.Tau, IsUnit (gramAt D X τ).det := fun τ => by
    have e : (gramAt D X τ).det = tauE D τ (HSpace.gram X).det := by rw [RingHom.map_det]; rfl
    rw [isUnit_iff_ne_zero, e]
    exact (map_ne_zero_iff _ (tauE D τ).injective).2 (gram_det_ne X)
  have hξ : ∀ τ : D.what₂.Tau, tauE D τ D.host.xi0 ≠ 0 := fun τ =>
    (map_ne_zero_iff _ (tauE D τ).injective).2 (GlobalTheory.DualPairCompare.embedding_xi_zero_ne_zero D)
  choose A hA0 hA using fun τ : D.what₂.Tau => sum_norm_le (r := r) (gramAt D X τ) (hG τ) _ (hξ τ)
  have hAt : 0 ≤ ∑ τ, A τ := Finset.sum_nonneg fun τ _ => hA0 τ
  have hrs : ∀ x : Mx D X.rank r, ∑ τ, ∑ i, ∑ j, ‖compAt θ τ x i j‖ ≤ (∑ τ, A τ) * ∑ a, ℓ a x := by
    intro x
    have e : ∑ a, ℓ a x = ∑ τ, ∑ i : Fin X.rank, ∑ j : Fin r, ∑ b : Bool, ℓ (τ, i, j, b) x := by
      simp only [Fintype.sum_prod_type]
    rw [e, Finset.mul_sum]
    refine Finset.sum_le_sum fun τ _ => (hA τ (compAt θ τ x)).trans ?_
    refine mul_le_mul_of_nonneg_right (Finset.single_le_sum (f := A) (fun τ _ => hA0 τ) (Finset.mem_univ τ)) ?_
    exact Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _
  refine ⟨N, (1 + ∑ τ, A τ) ^ N * 2 ^ N * (1 + ((K ^ N : NNReal) : ℝ)), by positivity, fun Ψ hΨ x => ?_⟩
  show _ ≤ _ * GlobalTheory.Unf.supSob ψ θ N Ψ
  have hLn := hL0 x
  have hb : (1 + ∑ τ, ∑ i, ∑ j, ‖compAt θ τ x i j‖) ^ N ≤
      (1 + ∑ τ, A τ) ^ N * 2 ^ N * (1 + (∑ a, ℓ a x) ^ N) := by
    have h1 : 1 + ∑ τ, ∑ i, ∑ j, ‖compAt θ τ x i j‖ ≤ (1 + ∑ τ, A τ) * (1 + ∑ a, ℓ a x) := by
      nlinarith [hrs x]
    calc (1 + ∑ τ, ∑ i, ∑ j, ‖compAt θ τ x i j‖) ^ N ≤ ((1 + ∑ τ, A τ) * (1 + ∑ a, ℓ a x)) ^ N :=
          pow_le_pow_left₀ (by positivity) h1 N
      _ = (1 + ∑ τ, A τ) ^ N * (1 + ∑ a, ℓ a x) ^ N := mul_pow _ _ _
      _ ≤ (1 + ∑ τ, A τ) ^ N * (2 ^ N * (1 + (∑ a, ℓ a x) ^ N)) := by gcongr; exact one_add_pow_le hLn N
      _ = _ := by ring
  have h0 := hpow 0 Ψ hΨ x
  have hN := hpow N Ψ hΨ x
  rw [pow_zero, ENNReal.ofReal_one, one_mul, pow_zero, ENNReal.coe_one, one_mul] at h0
  have hmono : GlobalTheory.Unf.supSob ψ θ 0 Ψ ≤ GlobalTheory.Unf.supSob ψ θ N Ψ := GlobalTheory.Size.wordSum_mono (Nat.zero_le N) Ψ
  calc ‖d.mixS X ψ μ' 𝓕' Ψ x 0‖ₑ * ENNReal.ofReal ((1 + ∑ τ, ∑ i, ∑ j, ‖compAt θ τ x i j‖) ^ N)
      ≤ ‖d.mixS X ψ μ' 𝓕' Ψ x 0‖ₑ * ENNReal.ofReal ((1 + ∑ τ, A τ) ^ N * 2 ^ N * (1 + (∑ a, ℓ a x) ^ N)) := by
        gcongr
    _ = ENNReal.ofReal ((1 + ∑ τ, A τ) ^ N * 2 ^ N) * (‖d.mixS X ψ μ' 𝓕' Ψ x 0‖ₑ +
          ENNReal.ofReal ((∑ a, ℓ a x) ^ N) * ‖d.mixS X ψ μ' 𝓕' Ψ x 0‖ₑ) := by
        rw [ENNReal.ofReal_mul (p := (1 + ∑ τ, A τ) ^ N * 2 ^ N) (by positivity),
          ENNReal.ofReal_add zero_le_one (by positivity), ENNReal.ofReal_one]
        ring
    _ ≤ ENNReal.ofReal ((1 + ∑ τ, A τ) ^ N * 2 ^ N) * (GlobalTheory.Unf.supSob ψ θ N Ψ +
          ((K ^ N : NNReal) : ENNReal) * GlobalTheory.Unf.supSob ψ θ N Ψ) :=
        mul_le_mul_of_nonneg_left (add_le_add (h0.trans hmono) hN) zero_le
    _ = ENNReal.ofReal ((1 + ∑ τ, A τ) ^ N * 2 ^ N * (1 + ((K ^ N : NNReal) : ℝ))) * GlobalTheory.Unf.supSob ψ θ N Ψ := by
        rw [ENNReal.ofReal_mul (p := (1 + ∑ τ, A τ) ^ N * 2 ^ N) (by positivity),
          ENNReal.ofReal_add zero_le_one (by positivity), ENNReal.ofReal_one, ENNReal.ofReal_coe_nnreal]
        ring

end GlobalTheory.MixWeight

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.OrthogonalProjectionPreservesDepthLattice
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

noncomputable section

namespace GlobalTheory.ProjCore

variable {D : D7}

theorem rat_entry' {m n : ℕ} (A : Matrix (Fin m) (Fin n) D.host.E) (i : Fin m) (j : Fin n) :
    (rat A : Mx D m n) i j = (1 : AF D.host.F) ⊗ₜ[D.host.F] A i j := rfl

theorem rat_mul_mem_hatMx {m n : ℕ} {ΛS : Submodule (𝓞 D.host.E) (Fin n → D.host.E)}
    {ΛT : Submodule (𝓞 D.host.E) (Fin m → D.host.E)} (M : Matrix (Fin m) (Fin m) D.host.E)
    (hM : ∀ y ∈ ΛT, M *ᵥ y ∈ ΛT) (I : Ideal (𝓞 D.host.E)) {z : Mx D m n} (hz : z ∈ hatMx (I • homLat ΛS ΛT)) :
    (rat M : Mx D m m) ⬝ z ∈ hatMx (I • homLat ΛS ΛT) := by
  have key : ∀ X ∈ I • homLat ΛS ΛT, M * X ∈ I • homLat ΛS ΛT := by
    intro X hX
    refine Submodule.smul_induction_on hX (fun r hr Y hY => ?_) (fun a b ha hb => ?_)
    · rw [Matrix.mul_smul]
      refine Submodule.smul_mem_smul hr ?_
      intro y hy
      rw [← Matrix.mulVec_mulVec]
      exact hM _ (hY _ hy)
    · rw [Matrix.mul_add]; exact add_mem ha hb
  induction hz using AddSubgroup.closure_induction with
  | mem w hw =>
    obtain ⟨α, hα, X, hX, rfl⟩ := hw
    refine AddSubgroup.subset_closure ⟨α, hα, M * X, key X hX, ?_⟩
    ext i j
    simp only [Matrix.mul_apply, Matrix.of_apply, TensorProduct.tmul_sum, rat_entry',
      Algebra.TensorProduct.tmul_mul_tmul, one_mul]
  | zero => rw [Matrix.mul_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [Matrix.mul_add]; exact add_mem hx hy
  | neg x _ hx => rw [Matrix.mul_neg]; exact neg_mem hx

theorem proj_mem_latCore : OnStd fun {D} _ _ _ {G} _ F => ∀ u ∈ latCore G 0, F.oz.jA ⬝ (F.oz.pA ⬝ u) ∈ latCore G 0 := by
  intro D hq T L μ0 hL sc G W M hM F hF u hu
  have hz := hF.zA
  have hqa : F.oz.qA * G.sp.dec0.a = 0 := by
    have hp := G.sp.dec0.perp
    rw [show Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) (frameMat (G.sp.P 0).sp (Yc D 0) G.sp.dec0.ι) =
        (frameMat (G.sp.P 0).sp (Yc D 0) G.sp.dec0.ι)ᴴ from Matrix.ext fun _ _ => rfl, ← hz] at hp
    rw [OrthDec.qA, Matrix.mul_assoc, hp, Matrix.mul_zero]
  have hmap : ∀ x ∈ G.Λ (.core 0), (F.oz.iA * F.oz.qA) *ᵥ x ∈ G.Λ (.core 0) := by
    intro x hx
    have hx' : x ∈ G.sp.dec0.lat (L.ΛY 0) (fun _ => 1) := by rw [← G.sp.lat0]; exact hx
    obtain ⟨y, hy, c, hc, rfl⟩ := hx'
    show _ ∈ (G.sp.P 0).lat
    rw [G.sp.lat0]
    refine ⟨y, hy, 0, fun _ => Submodule.zero_mem _, ?_⟩
    rw [Matrix.mulVec_add, Matrix.mulVec_zero, add_zero, ← hz, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec,
      Matrix.mul_assoc, F.oz.qA_iA, Matrix.mul_one, Matrix.mul_assoc, hqa, Matrix.mul_zero, Matrix.zero_mulVec, add_zero]
  have he : F.oz.jA ⬝ (F.oz.pA ⬝ u) = (rat (F.oz.iA * F.oz.qA) : Mx D _ _) ⬝ u := by
    rw [rat_mul, ← Matrix.mul_assoc]; rfl
  rw [he]
  refine ⟨?_, fun e he' => ?_⟩
  · exact GlobalTheory.OverTgt.mul_mem_latO (LT := G.Λ (.core 0)) (LT' := G.Λ (.core 0)) _
      (fun y hy => GlobalTheory.OrthSumLat.rat_mulVec_mem_latV _ hmap hy) hu.1
  · rw [← Matrix.mul_smul]
    exact rat_mul_mem_hatMx _ hmap _ (hu.2 e he')

end GlobalTheory.ProjCore
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.PulledBackLocalFunctionEqMulOfValues
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.ThetaTrace GlobalTheory.HkFam GlobalTheory.Frames GlobalTheory.HeckeEx
open GlobalTheory.IndefiniteRowSideFullHecke.FibrePushforwardExistenceTori (IsLinHom IsLieImg IsThGen IsHeckeIsog)
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.HeckeEx

theorem gs_appLE_top {X Y : Scheme.{0}} (w : Y ⟶ X) (U : X.Opens) (hi : ⊤ ≤ w ⁻¹ᵁ U) (z : Y) (a : Γ(X, U)) :
    gs (𝟙 Y) z ⊤ ((w.appLE U ⊤ hi).hom a) = gs w z U a := by
  rw [Scheme.Hom.appLE, CommRingCat.hom_comp, RingHom.comp_apply, gs_res (𝟙 Y) z hi trivial,
    gs_pull (𝟙 Y) w z U (hi trivial), Category.id_comp]

theorem appLE_eq_mul_of_sv : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {T Ω : Type} [CommRing T] [CommRing Ω] {x : Sp T ⟶ Xo.X} {k : ℤ} (w : Sp Ω ⟶ Gx x) (t t₀ : LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L k (Over.mk x))) (α : Ω), (∀ (z : Sp Ω) (J : (Sp Ω ⟶ Xo.univ.t.G.left) → Xo.univ.t.PP.L.ι), Good Xo.univ.t.PP.L z J → sv Xo.univ.t.G Xo.univ.t.PP t w z J = gs (𝟙 (Sp Ω)) z ⊤ (toΓ Ω α) * sv Xo.univ.t.G Xo.univ.t.PP t₀ w z J) → ∀ (i : (LPow Xo.univ.t.G Xo.univ.t.PP.L k (Over.mk x)).ι) (hi : ⊤ ≤ w ⁻¹ᵁ (LPow Xo.univ.t.G Xo.univ.t.PP.L k (Over.mk x)).U i), (w.appLE _ ⊤ hi).hom (t.f i) = toΓ Ω α * (w.appLE _ ⊤ hi).hom (t₀.f i) := by
  intro E _ _ _ H Dw l Xo T Ω _ _ x k w t t₀ α h i hi
  apply fn_ext
  intro z _
  have hw : w z ∈ (LPow Xo.univ.t.G Xo.univ.t.PP.L k (Over.mk x)).U i := hi trivial
  have hc : ∀ a b, (fun q => w ≫ (snd (Over.mk x) Xo.univ.t.G).left) a =
      (fun q => w ≫ (snd (Over.mk x) Xo.univ.t.G).left) b → i a = i b := fun a b _ =>
    congrArg i (Subsingleton.elim a b)
  obtain ⟨J, hJ, hJi⟩ := exists_good Xo.univ.t.PP.L Xo.univ.t.PP.isLB z
    (fun q => w ≫ (snd (Over.mk x) Xo.univ.t.G).left) i hc (fun q => Set.mem_iInter.1 hw q)
  have e := h z J hJ
  unfold sv at e
  rw [sval_of t w z J i hJi, sval_of t₀ w z J i hJi] at e
  rw [gs_appLE_top, gs_mul (𝟙 (Sp Ω)) z (⊤ : (Sp Ω).Opens) (show (𝟙 (Sp Ω) : Sp Ω ⟶ Sp Ω) z ∈ (⊤ : (Sp Ω).Opens) from trivial),
    gs_appLE_top]
  exact e

end GlobalTheory.HeckeEx
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.VacuumFixedNonsplitPlaceOfCharacterFrame
section
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR GlobalTheory.WeilParts GlobalTheory.StepLaw
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.StepLaw

theorem fixesVacAt_nonsplit_of_charFrame : ∀ (D : D7) (C : Formalism.L2.Host.CharFrame D) (η : (AE D)ˣ →* Circle), ChrEq η C.eta → ResEta D η 1 → ∀ (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)), IsWeilDatumO ψ S T χS χT om → IsSelfDualC S ΛS → IsSelfDualC T ΛT → ∀ v ε, NonSplitAt D v ε → UnramAt ε χS → UnramAt ε χT → FixesVacAt ψ S T ΛS ΛT om v ε := by
  intro D C η hη hres ψ S T χS χT om ΛS ΛT hW hS hT v ε hv hχS hχT
  have hStd : IsStdChar D ψ (-1) := hW.std
  have hTilde : IsEtaTilde D η := GlobalTheory.T.isUnramifiedEtaTildeHeckeChar_of_local_components D C η hη hres
  exact GlobalTheory.T.weilDatum_fixes_vacuum_nonSplitPlace_unramified D ψ hStd S T ΛS ΛT hS hT χS χT om ⟨η, hTilde⟩ hW v ε hv hχS hχT

end GlobalTheory.StepLaw
end

