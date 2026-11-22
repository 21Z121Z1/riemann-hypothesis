import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsLeadOfUnif
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle0002
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FamMod
import Development.AbelianVarietyTheory.Definitions.Divisors.GalRigidOfSurjective
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0080
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0075
import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.TraceFormTwistIsoOfPullback
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0106
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2388
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2569
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0024
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0019
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0009
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.BijectiveCechDeRhamComparisonDegreeOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2434
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2547
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2581
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2597
import Development.AbelianVarietyTheory.Definitions.Divisors.StepsNonvacuous
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0029
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2598
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0073
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0030
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0060
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2480

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGenericPointFactorOfInjectiveBaseMap
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem exists_fractionRing_map_comp_eq {R W B : Type} [CommRing R] [IsDomain R] [CommRing W] [IsDomain W] [CommRing B]
    (φ : R →+* W) (hφ : Function.Injective φ) (c : R →+* B) (a : B →+* FractionRing R) (b : B →+* FractionRing W)
    (ha : Function.Injective a) (hac : a.comp c = algebraMap R (FractionRing R))
    (hbc : b.comp c = (algebraMap W (FractionRing W)).comp φ) :
    ∃ ψ : FractionRing R →+* FractionRing W,
      ψ.comp (algebraMap R (FractionRing R)) = (algebraMap W (FractionRing W)).comp φ ∧ ψ.comp a = b := by
  have hinj : Function.Injective ((algebraMap W (FractionRing W)).comp φ) :=
    (IsFractionRing.injective W (FractionRing W)).comp hφ
  refine ⟨IsFractionRing.lift hinj, ?_, ?_⟩
  · ext r
    simp only [RingHom.comp_apply, IsFractionRing.lift_algebraMap]
  · ext x
    obtain ⟨r, r', hr', h⟩ := IsFractionRing.div_surjective (A := R) (a x)
    have h0 : algebraMap R (FractionRing R) r' ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hr'
    have hac' : ∀ y, a (c y) = algebraMap R (FractionRing R) y := fun y => RingHom.congr_fun hac y
    have hbc' : ∀ y, b (c y) = ((algebraMap W (FractionRing W)).comp φ) y := fun y => RingHom.congr_fun hbc y
    have h1 : x * c r' = c r := by
      apply ha
      rw [map_mul, hac', hac', ← h, div_mul_cancel₀ _ h0]
    have h2 : ((algebraMap W (FractionRing W)).comp φ) r' ≠ 0 := by
      intro h3
      exact nonZeroDivisors.ne_zero hr' (hinj (h3.trans (map_zero _).symm))
    rw [RingHom.comp_apply, ← h, map_div₀, IsFractionRing.lift_algebraMap, IsFractionRing.lift_algebraMap,
      div_eq_iff h2, ← hbc', ← hbc', ← map_mul, h1]

theorem Modif.exists_generic_factor : ∀ (R : Type) [CommRing R] [IsDomain R] (M : Modif R) (W : Type) [CommRing W] [IsDomain W] (φ : R →+* W), Function.Injective φ → ∀ ξ : Sp W ⟶ M.S, ξ ≫ M.π = spMap φ → ∃ ψ : FractionRing R →+* FractionRing W, ψ.comp (algebraMap R (FractionRing R)) = (algebraMap W (FractionRing W)).comp φ ∧ spMap ψ ≫ M.gp = jK W ≫ ξ := by
  intro R _ _ M W _ _ φ hφ ξ hξ
  haveI := M.integral
  haveI := M.dominant
  let s : M.S := (jK W ≫ ξ) (IsLocalRing.closedPoint (FractionRing W))
  obtain ⟨B, f, hf, hs, -⟩ := M.S.exists_affine_mem_range_and_range_subset (x := s) (U := ⊤) trivial
  have hb : Set.range (jK W ≫ ξ) ⊆ Set.range f := by
    rintro _ ⟨y, rfl⟩
    have : y = IsLocalRing.closedPoint (FractionRing W) := Subsingleton.elim (α := PrimeSpectrum (FractionRing W)) _ _
    rw [this]; exact hs
  have ha : Set.range M.gp ⊆ Set.range f := by
    rintro _ ⟨y, rfl⟩
    obtain ⟨z, hz⟩ := M.gp.denseRange.exists_mem_open f.isOpenEmbedding.isOpen_range ⟨s, hs⟩
    have : y = z := Subsingleton.elim (α := PrimeSpectrum (FractionRing R)) _ _
    rw [this]; exact hz
  obtain ⟨a, ha'⟩ := Spec.map_surjective (IsOpenImmersion.lift f M.gp ha)
  obtain ⟨b, hb'⟩ := Spec.map_surjective (IsOpenImmersion.lift f (jK W ≫ ξ) hb)
  obtain ⟨c, hc'⟩ := Spec.map_surjective (f ≫ M.π)
  have e1 : Spec.map a ≫ f = M.gp := by rw [ha', IsOpenImmersion.lift_fac]
  have e2 : Spec.map b ≫ f = jK W ≫ ξ := by rw [hb', IsOpenImmersion.lift_fac]
  have hac : c ≫ a = CommRingCat.ofHom (algebraMap R (FractionRing R)) := by
    apply Spec.map_injective
    rw [Spec.map_comp, hc', ← Category.assoc, e1, M.gp_π]
  have hbc : c ≫ b = CommRingCat.ofHom φ ≫ CommRingCat.ofHom (algebraMap W (FractionRing W)) := by
    apply Spec.map_injective
    rw [Spec.map_comp, hc', ← Category.assoc, e2, Category.assoc, hξ, Spec.map_comp]
  have hred : IsReduced (Spec B) := isReduced_of_isOpenImmersion f
  have hred' : _root_.IsReduced B := (affine_isReduced_iff B).1 hred
  have hdom : IsDominant (Spec.map a) := by
    haveI : IsDominant (Spec.map a ≫ f) := e1 ▸ M.dominant
    exact IsDominant.of_comp_of_isOpenImmersion _ f
  have hainj : Function.Injective a.hom := by
    have := (PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical a.hom).1 hdom.1
    rw [nilradical_eq_zero] at this
    exact (RingHom.injective_iff_ker_eq_bot _).2 (le_bot_iff.1 this)
  obtain ⟨ψ, h1, h2⟩ := exists_fractionRing_map_comp_eq φ hφ c.hom a.hom b.hom hainj
    (congrArg CommRingCat.Hom.hom hac) (congrArg CommRingCat.Hom.hom hbc)
  refine ⟨ψ, h1, ?_⟩
  have h3 : a ≫ CommRingCat.ofHom ψ = b := by
    ext1; exact h2
  rw [← e1, ← e2, ← h3, Spec.map_comp, Category.assoc]

end GlobalTheory.Mum
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGensOfDataFrom
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Poinc GlobalTheory.SiegJoin GlobalTheory.TChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.TChart.GensFrom

theorem lam_form {S : Scheme.{0}} {B : Over S} [GrpObj B] [IsCommMonObj B] {T : Over S} (x y : T ⟶ B) (U : Type)
    [CommGroup U] (H : (T.left ⟶ B.left) → U) :
    ∏ I : ULift.{0} (Finset (Fin 2)), H ((lift x y).left ≫ (psum B (x2 B) I.down).left) ^ ((-1 : ℤ) ^ (2 - I.down.card)) =
      (∏ k, H (lamPts x y k) ^ negε k)⁻¹ := by
  have p : ∀ I : Finset (Fin 2), (lift x y).left ≫ (psum B (x2 B) I).left = (psum B ![x, y] I).left := fun I =>
    congrArg (fun q => q.left) ((psum_hom (preHom (lift x y)) (x2 B) I).trans (by
      congr 1; funext i; fin_cases i <;> simp [x2, preHom]))
  simp only [p]
  rw [← Equiv.ulift.symm.prod_comp, show (Finset.univ : Finset (Finset (Fin 2))) = {∅, {0}, {1}, {0, 1}} from by decide,
    Finset.prod_insert (by decide), Finset.prod_insert (by decide), Finset.prod_insert (by decide), Finset.prod_singleton,
    Fin.prod_univ_four]
  have q0 : psum B ![x, y] ∅ = 1 := rfl
  have q1 : psum B ![x, y] {0} = x := _root_.mul_one x
  have q2 : psum B ![x, y] {1} = y := _root_.mul_one y
  have q3 : psum B ![x, y] {0, 1} = x * y := congrArg (x * ·) (_root_.mul_one y)
  simp [q0, q1, q2, q3, lamPts, negε]
  generalize H (x * y).left = A, H x.left = A₁, H y.left = A₂, H (1 : T ⟶ B).left = A₀
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv]
  abel

end GlobalTheory.TChart.GensFrom

namespace GlobalTheory.TChart.GensFrom

variable {X Y Y' Z : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ} {F : Y' ⟶ Y}

theorem good_linComb {z : Z} {J : (Z ⟶ X) → L.ι} (hJ : Good L z J) :
    Good (LB.LinComb L φ ε) z (fun ψ k => J (ψ ≫ φ k)) := fun ψ => hJ.mem φ ψ

theorem val_flatGen (u : LB.Gen ((LB.LinComb L φ ε).pull F)) (r : Z ⟶ Y') (z : Z) {J : (Z ⟶ X) → L.ι}
    (hJ : Good L z J) : val (GlobalTheory.UU.flatGen u) r z J = val u r z (fun ψ k => J (ψ ≫ φ k)) := by
  exact (gm_res r z _ (hJ.mem (fun k => F ≫ φ k) r) _).trans
    (val_of u r z _ (fun _ k => J (r ≫ F ≫ φ k)) (fun _ => funext fun k => by simp only [Category.assoc])).symm

theorem val_unflatGen (v : LB.Gen (LB.LinComb L (fun k => F ≫ φ k) ε)) (r : Z ⟶ Y') (z : Z) {J : (Z ⟶ X) → L.ι}
    (hJ : Good L z J) : val (GlobalTheory.UU.unflatGen v) r z (fun ψ k => J (ψ ≫ φ k)) = val v r z J := by
  exact (gm_res r z _ ((good_linComb (φ := φ) (ε := ε) hJ).mem (fun _ : PUnit => F) r) _).trans
    (val_of v r z J (fun k => J ((r ≫ F) ≫ φ k)) (fun k => by simp only [Category.assoc])).symm

end GlobalTheory.TChart.GensFrom

namespace GlobalTheory.TChart.GensFrom

theorem om_lam {S S' : Scheme.{0}} {B : Over S} {B' : Over S'} [GrpObj B] [IsCommMonObj B] [GrpObj B'] [IsCommMonObj B']
    {M : LB B.left} {M' : LB B'.left} {β₂ : (G2 B').left ⟶ (G2 B).left} (w : LB.Iso (abelian₂ B' M') ((abelian₂ B M).pull β₂))
    {Z : Scheme.{0}} (p : Z ⟶ (G2 B').left) (z : Z) (J : (Z ⟶ B.left) → M.ι) (J' : (Z ⟶ B'.left) → M'.ι) :
    GlobalTheory.ArcPull.om w z (fun ψ (I : ULift.{0} (Finset (Fin 2))) => J (ψ ≫ (psum B (x2 B) I.down).left))
      (fun ψ (I : ULift.{0} (Finset (Fin 2))) => J' (ψ ≫ (psum B' (x2 B') I.down).left)) p = lamVal w p z J J' := by
  have H : ∀ i i' : (LB.div ((abelian₂ B M).pull β₂) (abelian₂ B' M')).ι, i = i' →
      gm p z ((LB.div ((abelian₂ B M).pull β₂) (abelian₂ B' M')).U i) (w.s i) =
        gm p z ((LB.div ((abelian₂ B M).pull β₂) (abelian₂ B' M')).U i') (w.s i') := by
    rintro _ _ rfl; rfl
  unfold GlobalTheory.ArcPull.om Geo.Tor.gw lamVal
  refine H (fun _ (I : ULift.{0} (Finset (Fin 2))) => J ((p ≫ β₂) ≫ (psum B (x2 B) I.down).left),
      fun (I : ULift.{0} (Finset (Fin 2))) => J' (p ≫ (psum B' (x2 B') I.down).left))
    (fun _ (I : ULift.{0} (Finset (Fin 2))) => J (p ≫ β₂ ≫ (psum B (x2 B) I.down).left),
      fun (I : ULift.{0} (Finset (Fin 2))) => J' (p ≫ (psum B' (x2 B') I.down).left)) (Prod.ext ?_ rfl)
  funext _ I
  exact congrArg J (Category.assoc _ _ _)

end GlobalTheory.TChart.GensFrom

namespace GlobalTheory.TChart.GensFrom

theorem exists_gen_of_base {W V : Type} [CommRing W] [CommRing V] {BT : Over (Sp W)} [GrpObj BT] [IsCommMonObj BT]
    {BQ : Over (Sp V)} [GrpObj BQ] [IsCommMonObj BQ] {MT : LB BT.left} {MQ : LB BQ.left} (hMT : MT.IsLB) (hMQ : MQ.IsLB)
    (iw : W →+* V) {β : BQ.left ⟶ BT.left} {β₂ : (G2 BQ).left ⟶ (G2 BT).left} (hsq : IsSquare β β₂)
    (w : LB.Iso (abelian₂ BQ MQ) ((abelian₂ BT MT).pull β₂)) (hw : w.IsGen) (x y : 𝟙_ (Over (Sp V)) ⟶ BQ)
    (x₀ y₀ : 𝟙_ (Over (Sp W)) ⟶ BT) (hx : x.left ≫ β = spMap iw ≫ x₀.left) (hy : y.left ≫ β = spMap iw ≫ y₀.left)
    (τ₁ : LB.Gen (LB.LinComb MT (lamPts x₀ y₀) negε)) (h₁ : τ₁.IsGen) :
    ∃ τ : LB.Gen (LB.LinComb MQ (lamPts x y) negε), τ.IsGen ∧ ∀ (T' : Over (Sp V)) (z : T'.left) J J',
      Good MT z J → Good MQ z J' →
        val τ (toUnit T').left z J' = lamVal w (lift (toUnit T' ≫ x) (toUnit T' ≫ y)).left z J J' *
          val τ₁ (T'.hom ≫ spMap iw) z J := by
  have hψ : (lift x y).left ≫ β₂ = spMap iw ≫ (lift x₀ y₀).left := by
    apply pullback.hom_ext
    · show ((lift x y).left ≫ β₂) ≫ (fst BT BT).left = (spMap iw ≫ (lift x₀ y₀).left) ≫ (fst BT BT).left
      rw [Category.assoc, hsq.1, ← Category.assoc, ← Over.comp_left, lift_fst, hx, Category.assoc, ← Over.comp_left,
        lift_fst]
    · show ((lift x y).left ≫ β₂) ≫ (snd BT BT).left = (spMap iw ≫ (lift x₀ y₀).left) ≫ (snd BT BT).left
      rw [Category.assoc, hsq.2, ← Category.assoc, ← Over.comp_left, lift_snd, hy, Category.assoc, ← Over.comp_left,
        lift_snd]
  obtain ⟨t₂, ht₂, hv₂⟩ := exists_gen hMT
    (φ' := fun I : ULift.{0} (Finset (Fin 2)) => (lift x₀ y₀).left ≫ (psum BT (x2 BT) I.down).left)
    (ε' := fun I => (-1 : ℤ) ^ (2 - I.down.card)) (by
      intro U _ H
      rw [lam_form x₀ y₀ U H, ← Finset.prod_inv_distrib]
      simp only [zpow_neg]) (LB.invGen MT _ _ τ₁) (DVR.invGen_isGen _ _ _ _ h₁)
  let t₃ : LB.Gen ((abelian₂ BT MT).pull (lift x₀ y₀).left) := GlobalTheory.UU.unflatGen t₂
  have ht₃ : t₃.IsGen := GlobalTheory.UU.unflatGen_isGen ht₂
  obtain ⟨a, ha, hva⟩ := GlobalTheory.ArcPull.exists_down_om hw (LB.isLB_linComb hMT _ _) (LB.isLB_linComb hMQ _ _)
    (φ' := fun _ : PUnit => (lift x y).left) (φ := fun _ => (lift x₀ y₀).left) (ε := fun _ => 1) (spMap iw)
    (fun _ => hψ) t₃ ht₃
  obtain ⟨τ, hτ, hvτ⟩ := exists_gen hMQ
    (φ := fun I : ULift.{0} (Finset (Fin 2)) => (lift x y).left ≫ (psum BQ (x2 BQ) I.down).left)
    (ε := fun I => -((-1 : ℤ) ^ (2 - I.down.card))) (φ' := lamPts x y) (ε' := negε) (by
      intro U _ H
      simp only [zpow_neg, Finset.prod_inv_distrib]
      rw [lam_form x y U H, inv_inv]) (LB.invGen MQ _ _ (GlobalTheory.UU.flatGen a))
    (DVR.invGen_isGen _ _ _ _ (GlobalTheory.UU.flatGen_isGen ha))
  refine ⟨τ, hτ, fun T' z J J' hJ hJ' => ?_⟩
  have e1 := hvτ _ (toUnit T').left z J' hJ'
  have e5 := val_flatGen (L := MQ) (φ := fun I : ULift.{0} (Finset (Fin 2)) => (psum BQ (x2 BQ) I.down).left)
    (ε := fun I => (-1 : ℤ) ^ (2 - I.down.card)) (F := (lift x y).left) a (toUnit T').left z hJ'
  rw [val_inv, e5] at e1
  have e6 : val t₃ ((toUnit T').left ≫ spMap iw) z
      (fun ψ (k : ULift.{0} (Finset (Fin 2))) => J (ψ ≫ (psum BT (x2 BT) k.down).left)) =
      val t₂ ((toUnit T').left ≫ spMap iw) z J := val_unflatGen (L := MT) (φ := fun I : ULift.{0} (Finset (Fin 2)) => (psum BT (x2 BT) I.down).left)
    (ε := fun I => (-1 : ℤ) ^ (2 - I.down.card)) (F := (lift x₀ y₀).left) t₂ ((toUnit T').left ≫ spMap iw) z hJ
  have e2 := hva _ (toUnit T').left z _ _
    (good_linComb (L := MT) (φ := fun I : ULift.{0} (Finset (Fin 2)) => (psum BT (x2 BT) I.down).left)
      (ε := fun I => (-1 : ℤ) ^ (2 - I.down.card)) hJ)
    (good_linComb (L := MQ) (φ := fun I : ULift.{0} (Finset (Fin 2)) => (psum BQ (x2 BQ) I.down).left)
      (ε := fun I => (-1 : ℤ) ^ (2 - I.down.card)) hJ')
  rw [e6, hv₂ _ _ z J hJ, val_inv, Fintype.prod_unique, zpow_one, om_lam] at e2
  have e3 : (lift (toUnit T' ≫ x) (toUnit T' ≫ y)).left = (toUnit T').left ≫ (lift x y).left := by
    rw [← comp_lift]; rfl
  have e4 : (toUnit T').left = T'.hom := by simpa using Over.w (toUnit T')
  rw [e1, e3, ← e4, ← inv_inv (val τ₁ ((toUnit T').left ≫ spMap iw) z J), e2, _root_.mul_inv, _root_.mul_inv_cancel_left]
  rfl

end GlobalTheory.TChart.GensFrom

namespace GlobalTheory.TChart

open GensFrom in

theorem exists_gens_of_dataFrom {o W V : Type} [CommRing o] [CommRing W] [IsLocalRing W] [CommRing V] [IsDomain V]
    (T : TautBase o W) (iw : W →+* V) {I : Type} [Fintype I] (s : I → V)
    (ε : I → LinearMap.BilinForm ℤ (Fin T.r → ℤ)) (n : ℕ) (Q : Data V) (e : Q.X ≃+ (Fin T.r → ℤ)) {M : ℕ}
    (eI : I ≃ Fin M) (hD : DataFrom T iw s ε n Q e) :
    ∃ τ : GlobalTheory.Poinc.Sep.Gens Q, GlobalTheory.Poinc.Sep.TauIn Q τ (fun k => s (eI.symm k))
      (fun k => (n : ℤ) • pull e.toIntLinearEquiv.toLinearMap (ε (eI.symm k))) ∧ GlobalTheory.Poinc.Sep.FromBase Q τ iw := by
  obtain ⟨β, β₂, w, hpb, hsq, hw, hc, hτ⟩ := hD
  have key := fun a b => exists_gen_of_base T.M.isLB Q.M.isLB iw hsq w hw (Q.c a) (Q.c b)
    (T.c₀ ((n : ℤ) • e a)) (T.c₀ ((n : ℤ) • e b)) (hc a) (hc b) (T.τ₀ _ _) (T.τ₀_gen _ _)
  choose τ hτg hτv using key
  refine ⟨τ, fun a b => ⟨hτg a b, ?_⟩, T.B, inferInstance, inferInstance, T.M.L, fun a => T.c₀ ((n : ℤ) • e a),
    fun a b => T.τ₀ _ _, β, β₂, w, T.isAb, T.M.isLB, hpb, hsq, hw, hc, fun a b => T.τ₀_gen _ _,
    fun T' a b z J J' hJ hJ' => hτv a b T' z J J' hJ hJ'⟩
  obtain ⟨k, hk, hv⟩ := hτ a b
  refine ⟨k, ?_, fun z J' hJ' => ?_⟩
  · rw [hk]
    refine Fintype.prod_equiv eI _ _ fun i => ?_
    simp [pull]
  · choose J hJ using fun χ : (TK V).left ⟶ T.B.left => exists_chart T.M.isLB (χ z)
    rw [hv z J J' hJ hJ', hτv a b (TK V) z J J' hJ hJ']

end GlobalTheory.TChart
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGlueCopiesOfSchemeCocycle
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.GlueCopies

theorem desc_of_compat (D : Scheme.GlueData.{0}) {S : Scheme.{0}} (p : ∀ i, D.U i ⟶ S)
    (h : ∀ i j, D.f i j ≫ p i = (D.t i j ≫ D.f j i) ≫ p j) :
    ∃ F : D.glued ⟶ S, ∀ i, D.ι i ≫ F = p i :=
  ⟨Multicoequalizer.desc D.toGlueData.diagram S p (by rintro ⟨i, j⟩; exact h i j),
    fun i => Multicoequalizer.π_desc _ _ _ _ _⟩

theorem exists_glue_copies : ∀ (Y : Scheme.{0}) (J : Type) (V : J → J → Y.Opens) (τ : ∀ i j, (V i j).toScheme ⟶ Y), (∀ i, V i i = ⊤) → (∀ i, τ i i = (V i i).ι) → (∀ (i j k : J) (x : (V i j).toScheme), (V i j).ι x ∈ V i k → τ i j x ∈ V j k) → (∀ (i j k : J) (T : Scheme.{0}) (x : T ⟶ (V i j).toScheme) (y : T ⟶ (V i k).toScheme) (w : T ⟶ (V j k).toScheme), x ≫ (V i j).ι = y ≫ (V i k).ι → x ≫ τ i j = w ≫ (V j k).ι → w ≫ τ j k = y ≫ τ i k) → ∃ (G : Scheme.{0}) (ψ : J → (Y ⟶ G)), (∀ j, IsOpenImmersion (ψ j)) ∧ (∀ g : G, ∃ j, g ∈ Set.range (ψ j)) ∧ (∀ i j, IsPullback (V i j).ι (τ i j) (ψ i) (ψ j)) ∧ ∀ (Z : Scheme.{0}) (g : J → (Y ⟶ Z)), (∀ i j, (V i j).ι ≫ g i = τ i j ≫ g j) → ∃ F : G ⟶ Z, ∀ j, ψ j ≫ F = g j := by
  intro Y J V τ hV hτ hr hc
  have mem_of : ∀ (U : Y.Opens) {T : Scheme.{0}} (f : T ⟶ U.toScheme) (p : T), (f ≫ U.ι) p ∈ U :=
    fun U T f p => by
      have h := Set.mem_range_self (f := ⇑U.ι) (f p)
      rw [Scheme.Opens.range_ι] at h
      rw [Scheme.Hom.comp_apply]; exact h
  have hs : ∀ i, ∃ s : Y ⟶ (V i i).toScheme, s ≫ (V i i).ι = 𝟙 _ := fun i =>
    ⟨IsOpenImmersion.lift (V i i).ι (𝟙 _) (by
      rw [Scheme.Opens.range_ι, hV]; intro x _; simp), IsOpenImmersion.lift_fac _ _ _⟩
  choose s hs using hs
  have ht : ∀ i j, ∃ t : (V i j).toScheme ⟶ (V j i).toScheme, t ≫ (V j i).ι = τ i j := fun i j =>
    ⟨IsOpenImmersion.lift (V j i).ι (τ i j) (by
      rintro _ ⟨x, rfl⟩
      rw [Scheme.Opens.range_ι]
      exact hr i j i x (by rw [hV]; simp)), IsOpenImmersion.lift_fac _ _ _⟩
  choose t ht using ht
  have htb : ∀ i j, t i j ≫ τ j i = (V i j).ι := fun i j => by
    have h1 := hc i j i _ (𝟙 _) ((V i j).ι ≫ s i) (t i j) (by simp [hs]) (by simp [ht])
    rw [h1, hτ, Category.assoc, hs, Category.comp_id]
  have hu : ∀ i j k, ∃ u : pullback (V i j).ι (V i k).ι ⟶ (V j k).toScheme,
      u ≫ (V j k).ι = pullback.fst _ _ ≫ τ i j := fun i j k =>
    ⟨IsOpenImmersion.lift (V j k).ι (pullback.fst _ _ ≫ τ i j) (by
      rintro _ ⟨p, rfl⟩
      rw [Scheme.Opens.range_ι, Scheme.Hom.comp_apply]
      apply hr i j k
      rw [← Scheme.Hom.comp_apply, pullback.condition]
      exact mem_of _ _ _), IsOpenImmersion.lift_fac _ _ _⟩
  choose u hu using hu
  have hub : ∀ i j k, u i j k ≫ τ j k = pullback.snd _ _ ≫ τ i k := fun i j k =>
    hc i j k _ (pullback.fst _ _) (pullback.snd _ _) (u i j k) pullback.condition (hu i j k).symm
  let D : Scheme.GlueData.{0} :=
    { J := J
      U := fun _ => Y
      V := fun p => (V p.1 p.2).toScheme
      f := fun i j => (V i j).ι
      f_mono := fun i j => inferInstance
      f_id := fun i => ⟨s i, by rw [← cancel_mono (V i i).ι, Category.assoc, hs]; simp, hs i⟩
      t := t
      t_id := fun i => by rw [← cancel_mono (V i i).ι, ht, hτ, Category.id_comp]
      t' := fun i j k => pullback.lift (u i j k) (pullback.fst _ _ ≫ t i j) (by simp [hu, ht])
      t_fac := fun i j k => pullback.lift_snd _ _ _
      cocycle := fun i j k => by
        rw [← cancel_mono (pullback.fst (V i j).ι (V i k).ι), ← cancel_mono (V i j).ι]
        simp only [Category.assoc, pullback.lift_fst_assoc, hu, hub, pullback.lift_snd_assoc, htb,
          Category.id_comp]
      f_open := fun i j => inferInstance }
  have hP : ∀ i j, IsPullback (V i j).ι (τ i j) (D.ι i) (D.ι j) := fun i j => by
    rw [← ht]
    exact IsPullback.of_isLimit (D.vPullbackConeIsLimit i j)
  refine ⟨D.glued, D.ι, fun j => D.ι_isOpenImmersion j, fun g => ?_, hP, fun Z g hg => ?_⟩
  · obtain ⟨j, y, rfl⟩ := D.ι_jointly_surjective g
    exact ⟨j, y, rfl⟩
  · refine desc_of_compat D g fun i j => ?_
    change (V i j).ι ≫ g i = (t i j ≫ (V j i).ι) ≫ g j
    rw [ht, hg]

end GlobalTheory.GlueCopies
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGroupLawTranslateDerivationInvariantForms
section
open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.InvForm

section Alg
variable {R C E : Type} [CommRing R] [CommRing C] [Algebra R C] [CommRing E] [Algebra R E]

theorem dVal_smul_left (φ : C →ₐ[R] DualNumber E) (c : C) (x : Ω[C⁄R]) :
    dVal φ (c • x) = (φ c).fst * dVal φ x := by
  letI : Algebra C E := (redHom φ).toAlgebra
  haveI : IsScalarTower R C E := IsScalarTower.of_algebraMap_eq fun r ↦ (redHom_algebraMap φ r).symm
  unfold dVal
  simp only [LinearMap.coe_restrictScalars]
  rw [LinearMap.map_smul]
  rfl

def semiDerHom (σ : C →ₐ[R] E) (θ : Ω[C⁄R] →ₗ[R] E) (hθ : ∀ (c : C) (x : Ω[C⁄R]), θ (c • x) = σ c * θ x) :
    C →ₐ[R] DualNumber E where
  toFun c := TrivSqZeroExt.inl (σ c) + TrivSqZeroExt.inr (θ (KaehlerDifferential.D R C c))
  map_one' := by ext <;> simp
  map_mul' a b := by
    ext
    · simp
    · simp [hθ, MulOpposite.smul_eq_mul_unop]; ring
  map_zero' := by ext <;> simp
  map_add' a b := by ext <;> simp
  commutes' r := by ext <;> simp [TrivSqZeroExt.algebraMap_eq_inl']

theorem fst_semiDerHom (σ : C →ₐ[R] E) (θ : Ω[C⁄R] →ₗ[R] E) (hθ : ∀ (c : C) (x : Ω[C⁄R]), θ (c • x) = σ c * θ x)
    (c : C) : (semiDerHom σ θ hθ c).fst = σ c := by simp [semiDerHom]

theorem dVal_semiDerHom (σ : C →ₐ[R] E) (θ : Ω[C⁄R] →ₗ[R] E) (hθ : ∀ (c : C) (x : Ω[C⁄R]), θ (c • x) = σ c * θ x) :
    dVal (semiDerHom σ θ hθ) = θ := by
  refine LinearMap.ext fun x ↦ ?_
  induction x using GlobalTheory.CechDR.ind1 with
  | h b c =>
    rw [dVal_smul_left, dVal_D, hθ, fst_semiDerHom]
    simp [semiDerHom]
  | h0 => simp
  | ha x y hx hy => rw [map_add, map_add, hx, hy]

end Alg
end GlobalTheory.InvForm

namespace GlobalTheory.InvForm

theorem exists_transl_val : ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] (U V : AffOp A.left)
    (θ : Ω[Sec A.hom V.unop.1⁄R] →ₗ[R] Sec A.hom U.unop.1 ⊗[R] Sec A.hom V.unop.1),
    (∀ (c : Sec A.hom V.unop.1) (x : Ω[Sec A.hom V.unop.1⁄R]), θ (c • x) = (1 ⊗ₜ c) * θ x) →
    ∃ ψ : Sec A.hom U.unop.1 →ₐ[R] DualNumber (Sec A.hom U.unop.1 ⊗[R] Sec A.hom V.unop.1),
      (∀ b, (ψ b).fst = b ⊗ₜ 1) ∧
      ∀ w : GlobalTheory.InvForm.InvForm A, θ (evForm A.hom V w.1) = GlobalTheory.InvForm.dVal ψ (evForm A.hom U w.1) := by
  intro R _ A _ U V θ hθ
  let σ : Sec A.hom V.unop.1 →ₐ[R] Sec A.hom U.unop.1 ⊗[R] Sec A.hom V.unop.1 := Algebra.TensorProduct.includeRight
  have hθ' : ∀ (c : Sec A.hom V.unop.1) (x : Ω[Sec A.hom V.unop.1⁄R]), θ (c • x) = σ c * θ x := hθ
  let φ := semiDerHom σ θ hθ'
  let aV : GlobalTheory.PDiv.SpAlg R (Sec A.hom V.unop.1) ⟶ A := Over.homMk (affPt A.hom V.unop) (affPt_w A.hom V.unop)
  let aU : GlobalTheory.PDiv.SpAlg R (Sec A.hom U.unop.1) ⟶ A := Over.homMk (affPt A.hom U.unop) (affPt_w A.hom U.unop)
  let p : Over.mk (spMap (algebraMap R (DualNumber (Sec A.hom U.unop.1 ⊗[R] Sec A.hom V.unop.1)))) ⟶ A :=
    GlobalTheory.DeRham.spOver φ ≫ aV
  let x₀ : Over.mk (spMap (algebraMap R (Sec A.hom U.unop.1 ⊗[R] Sec A.hom V.unop.1))) ⟶ A :=
    GlobalTheory.DeRham.spOver (Algebra.TensorProduct.includeLeft : Sec A.hom U.unop.1 →ₐ[R] _) ≫
      aU
  let y₀ : Over.mk (spMap (algebraMap R (Sec A.hom U.unop.1 ⊗[R] Sec A.hom V.unop.1))) ⟶ A :=
    GlobalTheory.DeRham.spOver σ ≫ aV
  let q' := y₀⁻¹ * x₀
  let q := GlobalTheory.DeRham.spOver (TrivSqZeroExt.inlAlgHom R (Sec A.hom U.unop.1 ⊗[R] Sec A.hom V.unop.1)
    (Sec A.hom U.unop.1 ⊗[R] Sec A.hom V.unop.1)) ≫ q'
  let red := GlobalTheory.DeRham.spOver (TrivSqZeroExt.fstHom R (Sec A.hom U.unop.1 ⊗[R] Sec A.hom V.unop.1)
    (Sec A.hom U.unop.1 ⊗[R] Sec A.hom V.unop.1))
  have h1 : red ≫ p = y₀ := by
    simp only [red, p, y₀, ← Category.assoc, GlobalTheory.DeRham.spOver_comp]
    congr 2
  have h2 : red ≫ q = q' := by
    simp only [red, q, ← Category.assoc, GlobalTheory.DeRham.spOver_comp]
    have : (TrivSqZeroExt.fstHom R (Sec A.hom U.unop.1 ⊗[R] Sec A.hom V.unop.1)
        (Sec A.hom U.unop.1 ⊗[R] Sec A.hom V.unop.1)).comp (TrivSqZeroExt.inlAlgHom R _ _) = AlgHom.id R _ := AlgHom.ext fun x ↦ by simp
    rw [this, GlobalTheory.PDiv.spOver_id, Category.id_comp]
  have h3 : red ≫ (p * q) = x₀ := by
    rw [MonObj.comp_mul, h1, h2, mul_inv_cancel_left]
  have htop : ⊤ ≤ (p * q).left ⁻¹ᵁ U.unop.1 := by
    apply GlobalTheory.PtExt.pt_dual_le_of_fst R A _ (p * q) U.unop.1
    change ⊤ ≤ (red ≫ (p * q)).left ⁻¹ᵁ U.unop.1
    rw [h3]
    intro t _
    change (U.unop.2.fromSpec).base ((spMap _).base t) ∈ U.unop.1
    have k := IsAffineOpen.range_fromSpec U.unop.2
    rw [Set.ext_iff] at k
    exact (k _).1 ⟨_, rfl⟩
  have hs : (p * q).left ≫ A.hom = spMap (algebraMap R (DualNumber (Sec A.hom U.unop.1 ⊗[R] Sec A.hom V.unop.1))) :=
    Over.w (p * q)
  let ψ := GlobalTheory.CechKS.FormLocal.valHom (s := A.hom) (U := U.unop.1) (p * q).left htop hs
  have hψ : spMap (ψ : Sec A.hom U.unop.1 →+* DualNumber (Sec A.hom U.unop.1 ⊗[R] Sec A.hom V.unop.1)) ≫
      affPt A.hom U.unop = (p * q).left :=
    GlobalTheory.CechKS.FormLocal.valHom_pt U.unop.2 _ htop hs
  have hfst : (TrivSqZeroExt.fstHom R (Sec A.hom U.unop.1 ⊗[R] Sec A.hom V.unop.1)
      (Sec A.hom U.unop.1 ⊗[R] Sec A.hom V.unop.1)).toRingHom.comp
      (ψ : Sec A.hom U.unop.1 →+* DualNumber (Sec A.hom U.unop.1 ⊗[R] Sec A.hom V.unop.1)) =
      ((Algebra.TensorProduct.includeLeft : Sec A.hom U.unop.1 →ₐ[R] Sec A.hom U.unop.1 ⊗[R] Sec A.hom V.unop.1) :
        Sec A.hom U.unop.1 →+* Sec A.hom U.unop.1 ⊗[R] Sec A.hom V.unop.1) := by
    apply GlobalTheory.CechKS.FormLocal.ringHom_ext_affPt (s := A.hom) U.unop.2
    change spMap _ ≫ affPt A.hom U.unop = spMap _ ≫ affPt A.hom U.unop
    rw [Cris.spMap_comp, Category.assoc, hψ]
    exact congrArg CommaMorphism.left h3
  refine ⟨ψ, fun b ↦ RingHom.congr_fun hfst b, fun w ↦ ?_⟩
  have key := w.2 (Sec A.hom U.unop.1 ⊗[R] Sec A.hom V.unop.1) V.unop U.unop φ ψ p q q'.left rfl rfl hψ.symm
  rw [dVal_semiDerHom] at key
  exact key

end GlobalTheory.InvForm
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHermitianThetaFactorStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult
attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_hermitian_theta_factor : ∀ (A : Over (Sp ℂ)) [GrpObj A] [IsCommMonObj A], IsAbelianScheme A → ∀ (L : LB A.left), L.IsLB →
    ∀ (g : ℕ) (u : HolUnif A L g), ∃ (u' : HolUnif A L g) (Hm : Matrix (Fin g) (Fin g) ℂ) (χ : u'.Λ → ℂ),
      u'.ex = u.ex ∧ Hm.IsHermitian ∧ (∀ l, ‖χ l‖ = 1) ∧
      ∀ (l : u'.Λ) i z, ⊤ ≤ (u'.ex z).left ⁻¹ᵁ L.U i →
        u'.fr i z = χ l * Complex.exp (Real.pi * (z ⬝ᵥ Hm.mulVec (star (l : Fin g → ℂ))) +
          Real.pi / 2 * ((l : Fin g → ℂ) ⬝ᵥ Hm.mulVec (star (l : Fin g → ℂ)))) * u'.fr i (z + l) := by
  first | exact @GlobalTheory.exists_appellHumbert_frame_of_isLB | exact GlobalTheory.exists_appellHumbert_frame_of_isLB | (intros; apply GlobalTheory.exists_appellHumbert_frame_of_isLB <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHomEvenDefectBimultiplicativePeriodsStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_hom_evenDefect_bimultiplicative_periods : ∀ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] (D : DegPre R), D.TauBimult → ∃ h : D.X → (FractionRing R)ˣ, (∀ a b, h (a + b) = h a * h b) ∧ EvenDefect D h := by
  first | exact @GlobalTheory.DefectHom.exists_evenDefect_hom | exact GlobalTheory.DefectHom.exists_evenDefect_hom | (intros; apply GlobalTheory.DefectHom.exists_evenDefect_hom <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIdempotentLiftFormallySmoothSquareZeroStatement
section
open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_idempotent_lift_formallySmooth_squareZero : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (hI : I ^ 2 = 0) (π : R →+* R₀) (hπ : Function.Surjective π) (hk : RingHom.ker π = I) (B' B₀' : Type) [CommRing B'] [Algebra R B'] [CommRing B₀'] [Algebra R₀ B₀'] (p' : B' →+* B₀') (hs' : SemiHom π p') (hp' : Function.Surjective p') (hker' : ∀ b, p' b = 0 ↔ b ∈ I.map (algebraMap R B')) [Algebra.FormallySmooth R B'] (e₀ : B₀' →ₐ[R₀] B₀'), (∀ x, e₀ (e₀ x) = e₀ x) → ∃ e : B' →ₐ[R] B', (∀ b, e (e b) = e b) ∧ ∀ b, p' (e b) = e₀ (p' b) := by
  first | exact @GlobalTheory.Obs.idemLift | exact GlobalTheory.Obs.idemLift | (intros; apply GlobalTheory.Obs.idemLift <;> assumption)
end

