import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualMapCompDualMap
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KodairaSpencerMatrixUnique
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2370
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0070
import Development.AutomorphicArithmetic.CMTraceForms.Bundle0002
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.StChartF
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2191
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2375
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2192
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2266
import Development.AbelianVarietyTheory.Definitions.Divisors.DivPowerCompatTwoFormDerivativeCompOneForm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2410
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2376
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2317
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2377
import Development.AbelianVarietyTheory.Definitions.Divisors.OrdGeOfForall
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0011
import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle0001

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DeformationClassPullbackEqConstantAddEps
section
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.CechKS
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CechKS

open GlobalTheory.Published GlobalTheory.Published.AbelianDeRham

theorem exists_const_add_eps_const {K : Type} [Field K] {A : Over (Sp K)} [GrpObj A]
    (z : TensorProduct K (DualNumber K) (primDR A)) :
    ∃ a b : primDR A, liftSemi (constMor A).pull z =
      (constMor A).pull a + (DualNumber.eps : DualNumber K) • (constMor A).pull b := by
  induction z with
  | zero => exact ⟨0, 0, by rw [map_zero, map_zero, smul_zero, add_zero]⟩
  | add x y hx hy =>
    obtain ⟨a, b, e⟩ := hx
    obtain ⟨a', b', e'⟩ := hy
    refine ⟨a + a', b + b', ?_⟩
    rw [map_add, e, e', map_add, map_add, smul_add]
    abel
  | tmul r c =>
    refine ⟨r.fst • c, r.snd • c, ?_⟩
    rw [liftSemi_tmul, LinearMap.map_smulₛₗ, LinearMap.map_smulₛₗ, smul_smul]
    have e1 : (TrivSqZeroExt.inl r.fst : DualNumber K) = algebraMap K (DualNumber K) r.fst := rfl
    have e2 : (TrivSqZeroExt.inr r.snd : DualNumber K) = DualNumber.eps * algebraMap K (DualNumber K) r.snd := by
      rw [DualNumber.inr_eq_smul_eps, Algebra.smul_def, mul_comm]
    have er : r = algebraMap K (DualNumber K) r.fst + DualNumber.eps * algebraMap K (DualNumber K) r.snd := by
      rw [← e1, ← e2, TrivSqZeroExt.inl_fst_add_inr_snd_eq]
    conv_lhs => rw [er]
    exact add_smul _ _ _

theorem liftMor_pull_eq_const_add_eps : GlobalTheory.Published.AbelianDeRham → ∀ (K : Type) [Field K] (A : Over (Sp K)) [GrpObj A]
    (A' : Over (Sp (DualNumber K))) [GrpObj A'] (i : A.left ⟶ A'.left)
    (h : IsGrpPullback A A' (GlobalTheory.DeRham.epsRed K) i) (g : ℕ), IsAbelianScheme A' →
    SmoothOfRelativeDimension g A'.hom → ∀ x : primDR A', ∃ b : primDR A,
      (liftMor (epsDP K) h).pull x = (constMor A).pull ((fibMor h).pull x) +
        (DualNumber.eps : DualNumber K) • (constMor A).pull b := by
  intro P K _ A _ A' _ i h g hA hg x
  have a₀ := PolPull.isAbelianScheme_of_isGrpPullback hA h
  have g₀ := (smoothOfRelativeDimension_isStableUnderBaseChange g).of_isPullback h.1 hg
  obtain ⟨z, hz⟩ := constMor_surjective P a₀ g₀ ((liftMor (epsDP K) h).pull x)
  obtain ⟨a, b, e⟩ := exists_const_add_eps_const z
  rw [hz] at e
  have red : (redMor A).pull ((liftMor (epsDP K) h).pull x) = (fibMor h).pull x :=
    GrpMor.pull_pull (liftMor (epsDP K) h) (redMor A) (fibMor h) (fun _ => rfl) (by simp) x
  have ra : (fibMor h).pull x = a := by
    rw [← red, e, map_add, LinearMap.map_smulₛₗ, redMor_constMor, redMor_constMor]
    have : (TrivSqZeroExt.fstHom K K K).toRingHom (DualNumber.eps : DualNumber K) = 0 := rfl
    rw [this, zero_smul, add_zero]
  exact ⟨b, by rw [ra]; exact e⟩

end GlobalTheory.CechKS
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DegenerationPreDataLawsOfGeneratorValues
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.UTau0

namespace GenTr

theorem stalkMap_gm_comp {X Y Z : Scheme.{0}} (f : Z ⟶ Y) (g : Y ⟶ X) (z : Z) (U : X.Opens) (u : Γ(X, U)ˣ) :
    Units.map (f.stalkMap z).hom.toMonoidHom (gm g (f z) U u) = gm (f ≫ g) z U u := by
  by_cases h : g (f z) ∈ U
  · apply Units.ext
    rw [Units.coe_map, gm_val g (f z) U h, gm_val (f ≫ g) z U h]
    exact (Scheme.Hom.germ_stalkMap_apply f _ z h _).trans rfl
  · have h' : (f ≫ g) z ∉ U := h
    simp only [gm, dif_neg h, dif_neg h', MonoidHom.one_apply, map_one]

theorem val_stalk {X Y Y' Z : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ}
    (t : LB.Gen (LB.LinComb L φ ε)) (r : Z ⟶ Y') (g : Y' ⟶ Y) (q : Z ⟶ Y) (hq : r ≫ g = q) (z : Z)
    (J : (Z ⟶ X) → L.ι) :
    val t q z J = Units.map (r.stalkMap z).hom.toMonoidHom (val t g (r z) (fun ψ => J (r ≫ ψ))) := by
  subst hq
  rw [val_of t g (r z) _ (fun k => J ((r ≫ g) ≫ φ k)) (fun k => by rw [Category.assoc])]
  exact (stalkMap_gm_comp r g z _ _).symm

theorem toUnit_TK_left (R : Type) [CommRing R] [IsDomain R] : (toUnit (TK R)).left = jK R := by
  have := Over.w (toUnit (TK R))
  simpa using this

theorem val_tau {R : Type} [CommRing R] [IsDomain R] (D : DegPre R) {z : (TK R).left} {J} (hJ : Good D.P.L z J)
    (a b : D.X) : val (D.tau a b) (𝟙 _) z J = val (D.psi (a + b)) (𝟙 _) z J * (val (D.psi a) (𝟙 _) z J)⁻¹ *
      (val (D.psi b) (𝟙 _) z J)⁻¹ * (val D.rigK (𝟙 _) z J)⁻¹ := by
  unfold DegPre.tau
  rw [val_mul hJ, val_mul hJ, val_mul hJ, val_inv, val_inv, val_inv]

end GenTr

open GenTr

theorem rlaws_transfer : ∀ (R : Type) [CommRing R] [IsDomain R] (D₀ : DegPre R) (O : Type) [CommRing O] [StarRing O]
    [Module O D₀.X] (onB : D₀.P.OAct O), (∀ (a : O) (y : D₀.X), D₀.c (a • y) = D₀.c y ≫ onB.act a) →
    ∀ (w0 : O) (uw : LB.Gen (LB.LinComb D₀.P.L (GlobalTheory.UTau0.w0φ D₀ (onB.act w0)) GlobalTheory.UTau0.w0ε)), uw.IsGen →
    LB.Gen.Corr D₀.P.L _ _ _ _ (LB.pullGen D₀.P.L _ _ uw (eSec D₀.P.A)) (LB.oneGen D₀.P.L) →
    ∀ ψ : ∀ y : D₀.X, LB.Gen (LB.LinComb D₀.P.L (K := PUnit) (fun _ => (D₀.c y).left) (fun _ => -1)),
    GlobalTheory.UTau0.RLaws D₀ onB w0 uw ψ →
    ∃ h : ∀ y, (LB.pullGen D₀.P.L _ _ (ψ y) (jK R)).IsGen,
      letI : Module O ({ D₀ with psi := fun y => LB.pullGen D₀.P.L _ _ (ψ y) (jK R), psi_gen := h } : DegPre R).X :=
        ‹Module O D₀.X›
      ∃ oa : ({ D₀ with psi := fun y => LB.pullGen D₀.P.L _ _ (ψ y) (jK R), psi_gen := h } : DegPre R).OAct O,
        oa.onB = onB ∧
        ({ D₀ with psi := fun y => LB.pullGen D₀.P.L _ _ (ψ y) (jK R), psi_gen := h } : DegPre R).PsiEven ∧
        ({ D₀ with psi := fun y => LB.pullGen D₀.P.L _ _ (ψ y) (jK R), psi_gen := h } : DegPre R).TauBimult ∧
        TraceFormTwistIso ({ D₀ with psi := fun y => LB.pullGen D₀.P.L _ _ (ψ y) (jK R), psi_gen := h } : DegPre R) oa w0 ∧
        ∀ y, PsiUnitOn ({ D₀ with psi := fun y => LB.pullGen D₀.P.L _ _ (ψ y) (jK R), psi_gen := h } : DegPre R) y
          Set.univ := by
  intro R _ _ D₀ O _ _ _ onB hc w0 uw huw hnw ψ hR
  obtain ⟨hgen, h1, h2, h3, h4⟩ := hR
  have hL := D₀.P.isLB
  have htu := toUnit_TK_left R
  let Dn : DegPre R := { D₀ with psi := fun y => LB.pullGen D₀.P.L _ _ (ψ y) (jK R), psi_gen := fun y => DVR.pullGen_isGen _ _ _ _ (hgen y) _ }
  have Fψ : ∀ (z : (TK R).left) J, Good D₀.P.L z J → ∀ y,
      val (Dn.psi y) (𝟙 _) z J =
        Units.map ((jK R).stalkMap z).hom.toMonoidHom (val (ψ y) (𝟙 _) ((jK R) z) (fun f => J (jK R ≫ f))) :=
    fun z J hJ y => (val_pull hJ _ _ _).trans (val_stalk _ _ _ _ (by simp) _ _)
  have Frig : ∀ (z : (TK R).left) J, Good D₀.P.L z J →
      val Dn.rigK (𝟙 _) z J =
        Units.map ((jK R).stalkMap z).hom.toMonoidHom (rigV D₀ ((jK R) z) (fun f => J (jK R ≫ f))) :=
    fun z J hJ => (val_pull hJ _ _ _).trans (val_stalk _ _ _ _ (by simp [htu]) _ _)
  have Ftau : ∀ (z : (TK R).left) J, Good D₀.P.L z J → ∀ a b : D₀.X,
      val (Dn.tau a b) (𝟙 _) z J =
        Units.map ((jK R).stalkMap z).hom.toMonoidHom (tauV D₀ ψ ((jK R) z) (fun f => J (jK R ≫ f)) a b) := by
    intro z J hJ a b
    rw [val_tau Dn hJ, Fψ z J hJ, Fψ z J hJ, Fψ z J hJ, Frig z J hJ, tauV, map_mul, map_mul, map_mul, map_inv, map_inv,
      map_inv]
    rfl
  have Fx : ∀ (z : (TK R).left) J, Good D₀.P.L z J → ∀ {K : Type} [Fintype K] (φ : K → (D₀.P.A.left ⟶ D₀.P.A.left))
      (ε : K → ℤ) (t : LB.Gen (LB.LinComb D₀.P.L φ ε)) (y : D₀.X),
      val (LB.pullGen D₀.P.L _ _ t (Dn.xK y)) (𝟙 _) z J =
        Units.map ((jK R).stalkMap z).hom.toMonoidHom (val t (D₀.c y).left ((jK R) z) (fun f => J (jK R ≫ f))) := by
    intro z J hJ K _ φ ε t y
    refine (val_pull hJ _ _ _).trans (val_stalk _ _ _ _ ?_ _ _)
    rw [Category.id_comp]
    show _ = (toUnit (TK R) ≫ D₀.c y).left
    rw [Over.comp_left, htu]
  have F2 : ∀ (z : (TK R).left) J, Good D₀.P.L z J → ∀ {K : Type} [Fintype K]
      (φ : K → ((D₀.P.A ⊗ D₀.P.A).left ⟶ D₀.P.A.left)) (ε : K → ℤ) (t : LB.Gen (LB.LinComb D₀.P.L φ ε)) (y y' : D₀.X),
      val (LB.pullGen D₀.P.L _ _ t (Dn.pt2 y y')) (𝟙 _) z J =
        Units.map ((jK R).stalkMap z).hom.toMonoidHom
          (val t (lift (D₀.c y) (D₀.c y')).left ((jK R) z) (fun f => J (jK R ≫ f))) := by
    intro z J hJ K _ φ ε t y y'
    refine (val_pull hJ _ _ _).trans (val_stalk _ _ _ _ ?_ _ _)
    rw [Category.id_comp, DegPre.pt2, ← htu, ← Over.comp_left, comp_lift]
  have Fcub : ∀ (z : (TK R).left) J, Good D₀.P.L z J → ∀ a a' b : D₀.X,
      val (LB.pullGen D₀.P.L (thφ D₀.P.A (x3 D₀.P.A)) thε D₀.cub.t (Dn.pt3 a a' b)) (𝟙 _) z J =
        Units.map ((jK R).stalkMap z).hom.toMonoidHom
          (val D₀.cub.t (lift (D₀.c a) (lift (D₀.c a') (D₀.c b))).left ((jK R) z) (fun f => J (jK R ≫ f))) := by
    intro z J hJ a a' b
    refine (val_pull hJ _ _ _).trans (val_stalk _ _ (lift (D₀.c a) (lift (D₀.c a') (D₀.c b))).left _ ?_ _ _)
    rw [Category.id_comp, DegPre.pt3, ← htu, ← Over.comp_left, comp_lift, comp_lift]
  refine ⟨fun y => DVR.pullGen_isGen _ _ _ _ (hgen y) _, ⟨onB, hc, ?_⟩, rfl, ?_, ?_, ⟨uw, huw, hnw, ?_⟩, ?_⟩
  · intro a u hu hun y y'
    refine corr_of_val hL fun z J hJ => ?_
    rw [val_mul hJ, Ftau z J hJ, F2 z J hJ, Ftau z J hJ, ← map_mul]
    exact congrArg _ (h3 a u hu hun y y' _ _ fun f => hJ _)
  · intro χ
    refine corr_of_val hL fun z J hJ => ?_
    rw [val_mul hJ, Fψ z J hJ, Fx z J hJ, Fψ z J hJ, ← map_mul]
    exact congrArg _ (h2 χ _ _ fun f => hJ _)
  · intro a a' b
    refine corr_of_val hL fun z J hJ => ?_
    have key : val (Dn.tau (a + a') b) (𝟙 _) z J *
        val (LB.pullGen D₀.P.L (thφ D₀.P.A (x3 D₀.P.A)) thε D₀.cub.t (Dn.pt3 a a' b)) (𝟙 _) z J =
          val (Dn.tau a b) (𝟙 _) z J * val (Dn.tau a' b) (𝟙 _) z J := by
      rw [Ftau z J hJ, Fcub z J hJ, Ftau z J hJ, Ftau z J hJ, ← map_mul, ← map_mul]
      exact congrArg _ (h1 a a' b _ _ fun f => hJ _)
    exact (val_mul hJ _ _ _).trans (key.trans (val_mul hJ _ _ _).symm)
  · intro y
    refine corr_of_val hL fun z J hJ => ?_
    have key : val (Dn.tau y (w0 • y)) (𝟙 _) z J * val (LB.pullGen D₀.P.L _ _ uw (Dn.xK y)) (𝟙 _) z J =
        val (Dn.psi y) (𝟙 _) z J * val Dn.rigK (𝟙 _) z J := by
      rw [Ftau z J hJ, Fx z J hJ, Fψ z J hJ, Frig z J hJ, ← map_mul, ← map_mul]
      exact congrArg _ (h4 y _ _ fun f => hJ _)
    exact (val_mul hJ _ _ _).trans (key.trans (val_mul hJ _ _ _).symm)
  · intro y j V _ _ hV h
    have hle : V ≤ LB.wchart D₀.P.L (fun _ : PUnit => (D₀.c y).left) j :=
      fun x hx => Set.mem_iInter.2 fun _ => hV hx
    refine ⟨(res hle ((ψ y).s j)).val, Units.isUnit _, ?_⟩
    have e := congrArg (fun q => q.hom ((ψ y).s j).val) ((jK R).naturality (homOfLE hle).op)
    simp only [CommRingCat.hom_comp, RingHom.comp_apply] at e
    refine e.trans ?_
    show _ = ((TK R).left.presheaf.map (homOfLE h).op).hom (((TK R).left.presheaf.map (homOfLE _).op).hom
      (((jK R).app _).hom ((ψ y).s j).val))
    rw [← CommRingCat.comp_apply, ← Functor.map_comp]
    rfl

end GlobalTheory.UTau0
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DepthOscillationLeBoundEveryPrime
section
open NumberField IsDedekindDomain Formalism.L2.Pj ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.FGDepth GlobalTheory.CharDepth GlobalTheory.FactorDepth GlobalTheory.RefSum
open GlobalTheory.IndefiniteRowSideFullHecke.TypedPartSplitPrimes (IsIntHom IsOrbit FrobOnType embX primeBelow SplitInK InertInK)
open GlobalTheory.IndefiniteRowSideFullHecke.BigBlockCharacters (HasChars)
open GlobalTheory.IndefiniteRowSideFullHecke.FactorDepthInertBounds (boundAll boundInert boundFine)

namespace GlobalTheory.RefSum

theorem oscLe_eOf : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), ∀ (F k m M : ℕ) (Mb Sm : ℝ) (cx : Lt1 Dw → ℕ), Shape Dw F k m → ExpBd Dw k cx Mb Sm M → ∀ (vd : ℕ → ℝ) (S R : Finset ℕ), (∀ q, 0 ≤ vd q) → (∀ (q : ℕ) [Fact q.Prime], q ∈ S → UpperTheory.Depth.SplitPlaces q H F (vd q)) → 2 ∈ S → H.d ∈ R → (∀ q : ℕ, q.Prime → q ∉ S → q ∉ R → ¬ (q : ℤ) ∣ discr E) → ∀ (p : ℕ) [Fact p.Prime], OscLe Xo c p cx (eOf F (Dw.p + Dw.q) k m Mb Sm vd M S R p) := by
  intro E _ _ _ H Dw l Xo c F k m M Mb Sm cx hS hE vd S R hvd h2 h2S hdR hR p _
  have hram := GlobalTheory.T.depthOscillation_zero_above_and_degreeBound E H Dw l Xo c F k m M Mb Sm cx hS hE p
  have hMb : 0 ≤ Mb := hE.1
  have hp : p.Prime := Fact.out
  have hp2le : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hp1 : (0 : ℝ) < (p : ℝ) - 1 := by linarith
  have hF : (0 : ℝ) ≤ F := Nat.cast_nonneg _
  have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg _
  have hFmMb : (0 : ℝ) ≤ F * m * Mb := by positivity
  unfold eOf
  split_ifs with h1 hS' h3 h4
  · exact hram.1 h1
  · exact GlobalTheory.T.depth_oscillation_le_at_two_cmField E H Dw l Xo c F k m M Mb Sm cx hS hE p (vd p) (hvd p) (h2 p hS')
  · exact hram.2
  all_goals
    have hpM : p ≤ M := Nat.le_of_not_lt h1
    have h2' : p ≠ 2 := fun h => hS' (h ▸ h2S)
    have hpd : ¬ (p : ℤ) ∣ discr E := hR p hp hS' h3
    have hM1 : (1 : ℝ) ≤ (M : ℝ) := by
      have : 1 ≤ M := le_trans hp.one_lt.le hpM
      exact_mod_cast this
    have hlog : 0 ≤ Real.logb p M := Real.logb_nonneg (by exact_mod_cast hp.one_lt) hM1
    by_cases hsq : IsSquare (-(H.d : ZMod p))
    · have hd0 : (H.d : ZMod p) ≠ 0 := by
        rw [Ne, ZMod.natCast_eq_zero_iff]
        intro hdv
        have : p = H.d := (Nat.prime_dvd_prime_iff_eq hp H.d_prime).1 hdv
        exact h3 (this ▸ hdR)
      have hs := GlobalTheory.T.depth_oscillation_le_odd_split_unramified_prime E H Dw l Xo c F k m M Mb Sm cx hS hE p h2' hpd ⟨hd0, hsq⟩
      refine OscLe.mono Xo hs ?_
      first
      | (unfold eSmall
         have hA : (F * m * Mb + Sm) / ((p : ℝ) - 1) ≤ (F * m * Mb * (4 + Real.logb p M / 2) + Sm) / ((p : ℝ) - 1) := by
           apply div_le_div_of_nonneg_right _ hp1.le
           nlinarith
         have hB : (0 : ℝ) ≤ F * (m + 1) * ((Dw.p + Dw.q : ℕ) : ℝ) ^ 2 * (Real.logb p M + 1) := by positivity
         linarith)
      | (have hA : (F * m * Mb + Sm) / ((p : ℝ) - 1) ≤ (6 * F * m * Mb + Sm) / ((p : ℝ) - 1) := by
           apply div_le_div_of_nonneg_right _ hp1.le
           nlinarith
         linarith)
    · first
      | exact GlobalTheory.T.depthOscillation_le_at_small_odd_inertPrime E H Dw l Xo c F k m M Mb Sm cx hS hE p h2' hpd hsq (by exact_mod_cast hM1)
      | exact GlobalTheory.T.depthOscillation_large_inertPrime E H Dw l Xo c F k m M Mb Sm cx hS hE p hpd hsq (by omega)

end GlobalTheory.RefSum
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DerivationContractionLieDerivativeDeRhamRules
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.CxCoh GlobalTheory.PDA GlobalTheory.PDForm GlobalTheory.SmoothLift

namespace GlobalTheory.PDForm

variable {R B : Type} [CommRing R] [CommRing B] [Algebra R B] (v : Derivation R B B)

theorem indLeft {P : DR R B → Prop} (h : ∀ b : B, P (algebraMap B _ b)) (ha : ∀ x y, P x → P y → P (x + y))
    (hm : ∀ (ω : Ω[B⁄R]) x, P x → P (ι1 ω * x)) (x : DR R B) : P x :=
  CliffordAlgebra.left_induction (P := P) 0 h ha (fun x m hx ↦ hm m x hx) x

theorem ctr_algebraMap (b : B) : ctr v (algebraMap B (DR R B) b) = 0 := by
  simp [ctr]

theorem ctr_ι (ω : Ω[B⁄R]) : ctr v (ι1 ω) = algebraMap B (DR R B) (v.liftKaehlerDifferential ω) := by
  simp [ctr]

theorem ctr_ι_mul (ω : Ω[B⁄R]) (x : DR R B) :
    ctr v (ι1 ω * x) = v.liftKaehlerDifferential ω • x - ι1 ω * ctr v x :=
  CliffordAlgebra.contractLeft_ι_mul _ _ _

theorem ctr_mul (x y : DR R B) : ctr v (x * y) = ctr v x * y + sgn x * ctr v y := by
  induction x using indLeft with
  | h b =>
    rw [← Algebra.smul_def, map_smul, ctr_algebraMap, zero_mul, zero_add, AlgHom.commutes, Algebra.smul_def]
  | ha x x' hx hx' => rw [add_mul, map_add, hx, hx', map_add, map_add, add_mul, add_mul]; abel
  | hm ω x ih =>
    rw [mul_assoc, ctr_ι_mul, ih, ctr_ι_mul, map_mul, sgn_ι]
    simp only [mul_add, sub_mul, smul_mul_assoc, mul_assoc, neg_mul]
    abel

theorem ctr_ctr (x : DR R B) : ctr v (ctr v x) = 0 :=
  CliffordAlgebra.contractLeft_contractLeft _ _

theorem ctr_sgn (x : DR R B) : ctr v (sgn x) = -sgn (ctr v x) := by
  induction x using indLeft with
  | h b => rw [AlgHom.commutes, ctr_algebraMap, map_zero, neg_zero]
  | ha x x' hx hx' => rw [map_add, map_add, hx, hx', map_add, map_add, neg_add]
  | hm ω x ih =>
    rw [map_mul, sgn_ι, neg_mul, map_neg, ctr_ι_mul, ih, ctr_ι_mul, map_sub, map_smul, map_mul, sgn_ι, mul_neg, neg_mul]

theorem ctr_mem_pred {n : ℕ} {x : DR R B} (hx : x ∈ ⋀[B]^n Ω[B⁄R]) : ctr v x ∈ ⋀[B]^(n - 1) Ω[B⁄R] := by
  induction hx using Submodule.pow_induction_on_left' with
  | algebraMap b => rw [ctr_algebraMap]; exact zero_mem _
  | add x y i _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | mem_mul m hm i x hx ih =>
    obtain ⟨ω, rfl⟩ := hm
    change ctr v (ι1 ω * x) ∈ _
    rw [ctr_ι_mul, Nat.succ_sub_one]
    refine sub_mem (Submodule.smul_mem _ _ hx) ?_
    cases i with
    | zero =>
      change x ∈ LinearMap.range _ ^ 0 at hx
      rw [pow_zero] at hx
      obtain ⟨b, rfl⟩ := Submodule.mem_one.1 hx
      rw [ctr_algebraMap, mul_zero]; exact zero_mem _
    | succ k =>
      have := mul_mem (ι_mem ω) ih
      rwa [Nat.add_sub_cancel, add_comm] at this

theorem ctr_mem {j : ℕ} {x : DR R B} (hx : x ∈ ⋀[B]^(j + 1) Ω[B⁄R]) : ctr v x ∈ ⋀[B]^j Ω[B⁄R] := by
  simpa using ctr_mem_pred v hx

theorem lie_apply (x : DR R B) : lie v x = dDR R B (ctr v x) + ctr v (dDR R B x) := rfl

theorem lie_mul (x y : DR R B) : lie v (x * y) = lie v x * y + x * lie v y := by
  simp only [lie_apply, ctr_mul, dDR_mul, map_add, ctr_sgn, dDR_sgn, sgn_sgn, map_neg, neg_mul, add_mul, mul_add]
  abel

theorem lie_algebraMap (b : B) : lie v (algebraMap B (DR R B) b) = algebraMap B (DR R B) (v b) := by
  rw [lie_apply, ctr_algebraMap, map_zero, zero_add, dDR_algebraMap, ctr_ι,
    Derivation.liftKaehlerDifferential_comp_D]

theorem lie_D (b : B) : lie v (ι1 (D R B b)) = ι1 (D R B (v b)) := by
  rw [lie_apply, ctr_ι, Derivation.liftKaehlerDifferential_comp_D, dDR_algebraMap, dDR_D, map_zero, add_zero]

theorem lie_dDR (x : DR R B) : lie v (dDR R B x) = dDR R B (lie v x) := by
  rw [lie_apply, lie_apply, dDR_dDR, map_zero, add_zero, map_add, dDR_dDR, zero_add]

theorem lie_ctr (x : DR R B) : lie v (ctr v x) = ctr v (lie v x) := by
  rw [lie_apply, lie_apply, ctr_ctr, map_zero, zero_add, map_add, ctr_ctr, add_zero]

theorem lie_mem {j : ℕ} {x : DR R B} (hx : x ∈ ⋀[B]^j Ω[B⁄R]) : lie v x ∈ ⋀[B]^j Ω[B⁄R] := by
  cases j with
  | zero =>
    have hx' := hx
    change x ∈ LinearMap.range _ ^ 0 at hx'
    rw [pow_zero] at hx'
    obtain ⟨b, rfl⟩ := Submodule.mem_one.1 hx'
    rw [lie_algebraMap]
    change _ ∈ LinearMap.range _ ^ 0
    rw [pow_zero]; exact Submodule.algebraMap_mem _
  | succ k =>
    rw [lie_apply]
    exact add_mem (dDR_mem (ctr_mem v hx)) (ctr_mem v (dDR_mem hx))

theorem ctr_lie_rules : (∀ (R B : Type) [CommRing R] [CommRing B] [Algebra R B] (v : Derivation R B B), (∀ b, ctr v (algebraMap B (DR R B) b) = 0) ∧ (∀ ω, ctr v (ι1 ω) = algebraMap B (DR R B) (v.liftKaehlerDifferential ω)) ∧ (∀ x y, ctr v (x * y) = ctr v x * y + sgn x * ctr v y) ∧ (∀ x, ctr v (ctr v x) = 0) ∧ (∀ x, ctr v (sgn x) = -sgn (ctr v x)) ∧ ∀ (j : ℕ), ∀ x ∈ ⋀[B]^(j + 1) Ω[B⁄R], ctr v x ∈ ⋀[B]^j Ω[B⁄R]) ∧ ∀ (R B : Type) [CommRing R] [CommRing B] [Algebra R B] (v : Derivation R B B), (∀ x y, lie v (x * y) = lie v x * y + x * lie v y) ∧ (∀ b, lie v (algebraMap B (DR R B) b) = algebraMap B (DR R B) (v b)) ∧ (∀ b, lie v (ι1 (D R B b)) = ι1 (D R B (v b))) ∧ (∀ x, lie v (dDR R B x) = dDR R B (lie v x)) ∧ (∀ x, lie v (ctr v x) = ctr v (lie v x)) ∧ ∀ (j : ℕ), ∀ x ∈ ⋀[B]^j Ω[B⁄R], lie v x ∈ ⋀[B]^j Ω[B⁄R] :=
  ⟨fun _ _ _ _ _ v ↦ ⟨ctr_algebraMap v, ctr_ι v, ctr_mul v, ctr_ctr v, ctr_sgn v, fun _ _ hx ↦ ctr_mem v hx⟩,
    fun _ _ _ _ _ v ↦ ⟨lie_mul v, lie_algebraMap v, lie_D v, lie_dDR v, lie_ctr v, fun _ _ hx ↦ lie_mem v hx⟩⟩

end GlobalTheory.PDForm
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DerivationTaylorPowerSeriesDerivationEqPderiv
section
open IsLocalRing GlobalTheory.FormalOrigin

namespace GlobalTheory.FormalOrigin.TaylorDeriv

theorem foldr_iterate_comm {A ι : Type} (ds : ι → A → A) (h : ∀ a b f, ds a (ds b f) = ds b (ds a f))
    (α : ι → ℕ) (a : ι) (f : A) (l : List ι) :
    l.foldr (fun i g => (ds i)^[α i] g) (ds a f) = ds a (l.foldr (fun i g => (ds i)^[α i] g) f) := by
  induction l with
  | nil => rfl
  | cons i l ih =>
    simp only [List.foldr_cons, ih]
    have : Function.Commute (ds i) (ds a) := fun x => h i a x
    exact (this.iterate_left (α i)) _

theorem foldr_iterate_add_single {A ι : Type} (ds : ι → A → A) (h : ∀ a b f, ds a (ds b f) = ds b (ds a f))
    (α : ι →₀ ℕ) (a : ι) (f : A) (l : List ι) (hl : l.Nodup) (ha : a ∈ l) :
    l.foldr (fun i g => (ds i)^[(α + Finsupp.single a 1 : ι →₀ ℕ) i] g) f
      = ds a (l.foldr (fun i g => (ds i)^[α i] g) f) := by
  classical
  induction l with
  | nil => simp at ha
  | cons i l ih =>
    rw [List.nodup_cons] at hl
    simp only [List.foldr_cons]
    by_cases hi : i = a
    · subst hi
      have : l.foldr (fun j g => (ds j)^[(α + Finsupp.single i 1 : ι →₀ ℕ) j] g) f
          = l.foldr (fun j g => (ds j)^[α j] g) f := by
        apply List.foldr_ext
        intro j hj b
        have : j ≠ i := fun e => hl.1 (e ▸ hj)
        simp [Finsupp.single_apply, this.symm]
      rw [this]
      simp [Function.iterate_succ_apply']
    · have ha' : a ∈ l := by
        rcases List.mem_cons.1 ha with e | e
        · exact absurd e.symm hi
        · exact e
      rw [ih hl.2 ha']
      have e : (α + Finsupp.single a 1 : ι →₀ ℕ) i = α i := by
        simp [Finsupp.single_apply, Ne.symm hi]
      rw [e]
      have : Function.Commute (ds i) (ds a) := fun x => h i a x
      exact (this.iterate_left (α i)) _

theorem iterOp_apply_eq_add_single {A : Type} {n : ℕ} (ds : Fin n → A → A)
    (h : ∀ a b f, ds a (ds b f) = ds b (ds a f)) (α : Fin n →₀ ℕ) (a : Fin n) (f : A) :
    iterOp ds α (ds a f) = iterOp ds (α + Finsupp.single a 1) f := by
  unfold iterOp
  rw [foldr_iterate_comm ds h, foldr_iterate_add_single ds h α a f _ (List.nodup_finRange n) (List.mem_finRange a)]

theorem prod_factorial_add_single {n : ℕ} (α : Fin n →₀ ℕ) (a : Fin n) :
    ∏ i, (((α + Finsupp.single a 1 : Fin n →₀ ℕ) i).factorial : ℚ)
      = (∏ i, ((α i).factorial : ℚ)) * ((α a : ℚ) + 1) := by
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ a), ← Finset.mul_prod_erase _ (fun i => ((α i).factorial : ℚ)) (Finset.mem_univ a)]
  have : ∏ i ∈ Finset.univ.erase a, (((α + Finsupp.single a 1 : Fin n →₀ ℕ) i).factorial : ℚ)
      = ∏ i ∈ Finset.univ.erase a, ((α i).factorial : ℚ) := by
    refine Finset.prod_congr rfl fun i hi => ?_
    have := Finset.ne_of_mem_erase hi
    simp [Finsupp.single_apply, this.symm]
  rw [this]
  simp [Nat.factorial_succ]
  ring

theorem taylor_deriv_eq_pderiv : ∀ (A B : Type) [CommRing A] [CommRing B] [Algebra ℚ B] (n : ℕ) (ev : A →+* B) (ds : Fin n → Derivation ℤ A A), (∀ a b f, ds a (ds b f) = ds b (ds a f)) → ∀ a f, taylor ev (fun i => ⇑(ds i)) (ds a f) = MvPowerSeries.pderiv B a (taylor ev (fun i => ⇑(ds i)) f) := by
  intro A B _ _ _ n ev ds h a f
  ext α
  rw [MvPowerSeries.coeff_pderiv]
  simp only [MvPowerSeries.coeff_apply, taylor]
  rw [prod_factorial_add_single, ← iterOp_apply_eq_add_single (fun i => ⇑(ds i)) h]
  have e : ((α a : B) + 1) = algebraMap ℚ B ((α a : ℚ) + 1) := by simp
  have hp : ((α a : ℚ) + 1) ≠ 0 := by positivity
  rw [e, mul_comm _ (algebraMap ℚ B _), ← Algebra.smul_def, smul_smul]
  congr 1
  field_simp

end GlobalTheory.FormalOrigin.TaylorDeriv
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DescentDatumFrameCocycleUnitStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.LBDescent
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.descentDatum_frame_cocycle_unit : ∀ {X Y : Scheme.{0}} (f : X ⟶ Y) (L : LB X), L.IsLB →
    ∀ (φ : ∀ i j, Γ(pullback f f, chart f L i j)ˣ), DescCompat f L φ → DescCocycle f L φ →
    ∀ (V : Y.Opens) (t : ∀ i, Γ(X, f ⁻¹ᵁ V ⊓ L.U i)ˣ), (∀ (i j : L.ι) (x : X), f x ∈ V → x ∈ L.U i → x ∈ L.U j →
      gm (𝟙 X) x _ (t i) = gm (𝟙 X) x _ (L.g i j) * gm (𝟙 X) x _ (t j)) →
    ∃ c : Γ(pullback f f, pullback.fst f f ⁻¹ᵁ f ⁻¹ᵁ V)ˣ,
      (∀ (z : ↥(pullback f f)) (i j : L.ι), f (pullback.fst f f z) ∈ V → pullback.fst f f z ∈ L.U i →
        pullback.snd f f z ∈ L.U j →
        gm (𝟙 _) z _ c = gm (pullback.fst f f) z _ (t i) * gm (𝟙 _) z _ (φ i j) * (gm (pullback.snd f f) z _ (t j))⁻¹) ∧
      ∀ w : ↥(Triple f), f (pullback.fst f f (pullback.fst (pullback.snd f f) (pullback.fst f f) w)) ∈ V →
        gm (pullback.fst (pullback.snd f f) (pullback.fst f f)) w _ c *
          gm (pullback.snd (pullback.snd f f) (pullback.fst f f)) w _ c = gm (pr13 f) w _ c := by
  first | exact @GlobalTheory.LBDescent.frame_cocycle | exact GlobalTheory.LBDescent.frame_cocycle | (intros; apply GlobalTheory.LBDescent.frame_cocycle <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DetSqMulPowLeProdBilinFormLatticeBasisStatement
section
open IsLocalRing GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.Poinc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.det_sq_mul_pow_le_prod_bilinForm_lattice_basis : ∀ (r : ℕ) (X₀ : Type) [AddCommGroup X₀] [Module.Free ℤ X₀] [Module.Finite ℤ X₀] (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (b : Module.Basis (Fin r) ℤ X₀) (ε : X ≃ₗ[ℤ] X₀) (k : X₀ →ₗ[ℤ] X) (β : LinearMap.BilinForm ℤ X), (∀ a b, β a b = β b a) → (∀ y, 0 ≤ β y y) → ∀ lam : ℝ, 0 ≤ lam → (∀ x, x ≠ 0 → lam ≤ β x x) → ((LinearMap.det (ε.toLinearMap ∘ₗ k) : ℤ) : ℝ) ^ 2 * lam ^ r ≤ (r : ℝ) ^ r * ∏ j, (β (k (b j)) (k (b j)) : ℝ) := by
  first | exact @GlobalTheory.LatIndex.det_sq_mul_pow_le_prod | exact GlobalTheory.LatIndex.det_sq_mul_pow_le_prod | (intros; apply GlobalTheory.LatIndex.det_sq_mul_pow_le_prod <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DvdOfForallCompleteDvrDominatingStatement
section
open AlgebraicGeometry CategoryTheory IsLocalRing ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.TorRef GlobalTheory.Poinc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dvd_of_forall_complete_dvr_dominating : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [IsIntegrallyClosed R] [CharZero R] (f g : R), g ≠ 0 → (∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V], IsAdicComplete (maximalIdeal V) V → ∀ ρ : R →+* V, Function.Injective ρ → IsLocalHom ρ → ρ g ∣ ρ f) → g ∣ f := by
  first | exact @GlobalTheory.Poinc.dvd_of_forall_complete_dvr | exact GlobalTheory.Poinc.dvd_of_forall_complete_dvr | (intros; apply GlobalTheory.Poinc.dvd_of_forall_complete_dvr <;> assumption)
end

