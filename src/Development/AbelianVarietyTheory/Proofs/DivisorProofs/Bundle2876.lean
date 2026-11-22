import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.OfFactorE
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2821
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.RelationsAreFunctions
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2554
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsTorusAndQuotientHom
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ExistsZeroGt
import Development.AbelianVarietyTheory.Definitions.Divisors.IsActIffIsDiagEnd
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0080
import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle0001
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2847
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2703
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2770
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2771
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2803
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0090
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2694
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2783
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2684

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CharacterValuesGaloisFixedOfIdempotentTorsion
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum.ETors

open GlobalTheory.BXOf GlobalTheory.TorusExt ReciprocityTheory.ChartRestriction.G.DVR

theorem cubN_pow_eq_pow {A U : Type} [CommGroup A] [CommGroup U] {θ : A → A → A → U} (C : IsCub θ) (P : Subgroup A)
    (H : Subgroup U) (hθ : ∀ x ∈ P, ∀ y ∈ P, ∀ z ∈ P, θ x y z ∈ H) {n : ℕ} {b d : A} (hb : b ∈ P) (hd : d ∈ P)
    (hn : b ^ n = 1) : ∃ h ∈ H, cubN θ n 1 b (d ^ n) = h ^ n := by
  have hN : cubN θ n 1 b d ∈ H := H.prod_mem fun i _ => hθ _ (P.mul_mem P.one_mem (P.pow_mem hb i)) _ hb _ hd
  have key : ∀ j : ℕ, ∃ r ∈ H, cubN θ n 1 b (d ^ j) = cubN θ n 1 b d ^ j * r ^ n := by
    intro j
    induction j with
    | zero => exact ⟨1, H.one_mem, by rw [pow_zero, C.N_one]; simp⟩
    | succ j ih =>
      obtain ⟨r, hr, e⟩ := ih
      have a := C.N_add n 1 b (d ^ j) d
      rw [hn, _root_.mul_one (1 : A), C.face, _root_.mul_one, _root_.one_mul, e, ← pow_succ] at a
      refine ⟨r * (θ b (d ^ j) d)⁻¹, H.mul_mem hr (H.inv_mem (hθ _ hb _ (P.pow_mem hd j) _ hd)), ?_⟩
      rw [eq_mul_inv_of_mul_eq a, mul_pow, inv_pow, pow_succ (cubN θ n 1 b d), ← _root_.mul_assoc,
        mul_right_comm (cubN θ n 1 b d ^ j)]
  obtain ⟨r, hr, e⟩ := key n
  exact ⟨_ * r, H.mul_mem hN hr, by rw [e, mul_pow]⟩

theorem sig_val_fixed {X Y : Scheme.{0}} {L : LB X} (hL : L.IsLB) {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ}
    {t : LB.Gen (LB.LinComb L φ ε)} (ht : t.IsGen) {F : Type} [Field F] (σ : F →+* F)
    {J : (Spec (CommRingCat.of F) ⟶ X) → L.ι} (hJ : Good L (closedPoint F) J) (r : Spec (CommRingCat.of F) ⟶ Y)
    (hr : Spec.map (CommRingCat.ofHom σ) ≫ r = r) :
    Units.map σ.toMonoidHom (sig F (val t r (closedPoint F) J)) = sig F (val t r (closedPoint F) J) := by
  have e := val_nat ht σ hJ hJ r
  have hdel : ∀ k, del L σ J J (r ≫ φ k) = 1 := fun k => by
    rw [← del_id hL hJ (r ≫ φ k)]
    unfold del
    rw [← Category.assoc, hr, CommRingCat.ofHom_id, Spec.map_id, Category.id_comp]
  rw [hr, Finset.prod_eq_one (fun k _ => by rw [hdel, one_zpow]), _root_.one_mul] at e
  exact e.symm

theorem exists_c_eq_pow {o W : Type} [CommRing o] [CommRing W] [IsLocalRing W] (T : TautBase o W) {R : Type} [CommRing R]
    [IsDomain R] (iw : W →+* R) {I : Type} [Fintype I] (s : I → R) (ε : I → LinearMap.BilinForm ℤ (Fin T.r → ℤ)) {n : ℕ}
    (hn : 1 ≤ n) (Q : Data R) (e : Q.X ≃+ (Fin T.r → ℤ)) (h : DataFrom T iw s ε n Q e) (a : Q.X) :
    ∃ d : 𝟙_ (Over (Sp R)) ⟶ Q.B, Q.c a = d ^ n := by
  obtain ⟨β, -, -, ⟨g, gm⟩, -, -, c, -⟩ := h
  let x : (Fin T.r → ℤ) → (Over.mk ((𝟙_ (Over (Sp R))).hom ≫ spMap iw) ⟶ T.B) := fun v => toUnit _ ≫ T.c₀ v
  have xl : ∀ v, (x v).left = spMap iw ≫ (T.c₀ v).left := fun v => by
    show (𝟙 _ ≫ spMap iw) ≫ _ = _
    rw [Category.id_comp]
  have xa : ∀ v v', x (v + v') = x v * x v' := fun v v' => by
    show toUnit _ ≫ T.c₀ (v + v') = _
    rw [T.c₀_add]; exact MonObj.comp_mul _ _ _
  have w : (spMap iw ≫ (T.c₀ (e a)).left) ≫ T.B.hom = 𝟙 _ ≫ spMap iw := by
    rw [Category.assoc, Over.w]; exact (Category.comp_id _).trans (Category.id_comp _).symm
  let d : 𝟙_ (Over (Sp R)) ⟶ Q.B := Over.homMk (g.lift _ _ w) (g.lift_snd _ _ w)
  have hd : (x (e a)).left = d.left ≫ β := (xl _).trans (g.lift_fst _ _ w).symm
  have key : ∀ k : ℕ, (x (((k + 1 : ℕ) : ℤ) • e a)).left = (d ^ (k + 1)).left ≫ β := by
    intro k
    induction k with
    | zero => simpa using hd
    | succ k ih =>
      rw [Nat.cast_succ (k + 1), add_smul, one_smul, xa, pow_succ d (k + 1)]
      exact gm _ _ _ _ _ ih hd
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  refine ⟨d, Over.OverMorphism.ext (g.hom_ext ?_ ?_)⟩
  · rw [c, ← key, xl]
  · rw [Over.w, Over.w]

attribute [local instance] gtGroup

theorem charVal_pow {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {F : Type} [Field F] [Algebra (FractionRing R) F]
    (t : GtPtF D F) (χ : D.X) {y J} (hJ : Good D.P.L y J) (k : ℕ) :
    charVal (k • t) χ y J * cubN (th D y J) k 1 t.b (cP D _ χ) = charVal t χ y J ^ k := by
  have C : IsCub (th D (T := TF (R := R) F) y J) := isCub_cubV D.cub hJ
  induction k with
  | zero => rw [zero_nsmul, zero_val χ hJ]; simp [cubN]
  | succ k ih =>
    have a := add_val (k • t) t χ hJ
    rw [nsmul_b, C.s01, C.s12] at a
    simp only [cubN, Finset.prod_range_succ, _root_.one_mul] at ih ⊢
    rw [succ_nsmul, pow_succ, ← ih, mul_comm (∏ _ ∈ _, _), ← _root_.mul_assoc, a, mul_right_comm]

theorem corr_pullGen_of_torsion : ∀ {o W : Type} [CommRing o] [CommRing W] [IsLocalRing W] (T : TautBase o W) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (iw : W →+* R) {I : Type} [Fintype I] (s : I → R) (ε : I → LinearMap.BilinForm ℤ (Fin T.r → ℤ)) (n : ℕ), IsCN R → 1 ≤ n → IsUnit (n : R) → ∀ ζ : R, IsPrimitiveRoot ζ n → ∀ (Q : Data R) (e : Q.X ≃+ (Fin T.r → ℤ)), DataFrom T iw s ε n Q e → TorsRat Q.B n → ∀ (D' : DegData R (maximalIdeal R)) (F : PFactor Q D'.toPre) (σ : AlgebraicClosure (FractionRing R) ≃ₐ[FractionRing R] AlgebraicClosure (FractionRing R)), ∀ t : GtPtF D'.toPre (AlgebraicClosure (FractionRing R)), GtPtAct F.o F.e t t → (∃ z : GtPtF D'.toPre (AlgebraicClosure (FractionRing R)), GtPtF.IsNsmul n t z ∧ z.IsZero) → spMap σ.toAlgHom.toRingHom ≫ t.b.left = t.b.left → ∀ χ : D'.toPre.X, LB.Gen.Corr D'.toPre.P.L _ _ _ _ (t.s χ) (LB.pullGen D'.toPre.P.L _ _ (t.s χ) (spMap σ.toAlgHom.toRingHom)) := by
  intro o W _ _ _ T R _ _ _ iw I _ s ε n _ hn _ ζ hζ Q e hQ _ D' F σ t ht ⟨z, hz, hz0⟩ hb
  set K := AlgebraicClosure (FractionRing R) with hK
  have hσ : σ.toAlgHom.toRingHom.comp (algebraMap (FractionRing R) K) = algebraMap (FractionRing R) K :=
    RingHom.ext fun x => σ.commutes x
  have hnt : n • t = 0 := ((isNsmul_iff_eq _ _ _).1 hz).symm.trans ((isZero_iff_eq _).1 hz0)
  choose J hJ using fun ψ : (TF (R := R) K).left ⟶ D'.toPre.P.A.left =>
    exists_chart D'.toPre.P.isLB (ψ (closedPoint K))
  replace hJ : Good D'.toPre.P.L (Z := (TF (R := R) K).left) (closedPoint K) J := hJ
  suffices H : ∀ χ, σ.toAlgHom.toRingHom (sig K (charVal t χ (closedPoint K) J) : K) =
      (sig K (charVal t χ (closedPoint K) J) : K) from
    ((eq_gtExt_iff _ hσ t t).1 (gtExt_eq_self_of_charVal_fixed R D'.toPre K _ hσ t hb J hJ H).symm).2
  let H : Subgroup ((TF (R := R) K).left.presheaf.stalk (closedPoint K))ˣ :=
    MonoidHom.eqLocus ((Units.map σ.toAlgHom.toRingHom.toMonoidHom).comp (sig K)) (sig K)
  let P : Subgroup (TF (R := R) K ⟶ D'.toPre.P.A) :=
    { carrier := {x | extMap _ hσ ≫ x = x}
      mul_mem' := fun {a b} ha hb => (MonObj.comp_mul _ _ _).trans (congrArg₂ (· * ·) ha hb)
      one_mem' := MonObj.comp_one _
      inv_mem' := fun {a} ha => (GrpObj.comp_inv _ _).trans (congrArg (·⁻¹) ha) }
  have hP : ∀ d : 𝟙_ (Over (Sp R)) ⟶ D'.toPre.P.A, toUnit _ ≫ d ∈ P := fun d => by
    show extMap _ hσ ≫ toUnit _ ≫ d = toUnit _ ≫ d
    rw [← Category.assoc, toUnit_unique (extMap _ hσ ≫ toUnit _) (toUnit _)]
  have hbP : t.b ∈ P := Over.OverMorphism.ext hb
  have hθ : ∀ x ∈ P, ∀ y ∈ P, ∀ z ∈ P, th D'.toPre (T := TF (R := R) K) (closedPoint K) J x y z ∈ H := by
    intro x hx y hy z hz
    refine sig_val_fixed D'.toPre.P.isLB D'.toPre.cub.isGen _ hJ (lift x (lift y z)).left ?_
    show (extMap _ hσ ≫ lift x (lift y z)).left = _
    rw [comp_lift, comp_lift, hx, hy, hz]
  have C : IsCub (th D'.toPre (T := TF (R := R) K) (closedPoint K) J) := isCub_cubV D'.toPre.cub hJ

  have := F.o.onB.hom F.e
  have := F.o.onB.hom (star F.e)
  have := F.o.onB.hom F.f
  have := F.inc_hom
  have hr := F.o.onB.rosati (star F.e)
  rw [star_star] at hr
  obtain ⟨u, hu, u₀⟩ := exists_ros GlobalTheory.SemiRigid.globalFns D'.toPre.P.isAb D'.toPre.P.isLB _ _ hr
  have rel : ∀ χ, ∃ h ∈ H, charVal t χ (closedPoint K) J = charVal t (star F.e • χ) (closedPoint K) J * h := by
    intro χ
    refine ⟨val u (lift (cP D'.toPre _ χ) t.b).left (closedPoint K) J, ?_, ?_⟩
    · refine sig_val_fixed D'.toPre.P.isLB hu _ hJ (lift (cP D'.toPre _ χ) t.b).left ?_
      show (extMap _ hσ ≫ lift (cP D'.toPre _ χ) t.b).left = _
      rw [comp_lift, comp_cP, hbP]
    · refine (val_corr hJ (ht.2 u hu u₀ χ) (𝟙 _)).symm.trans ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) rfl ?_))
      rw [val_pull hJ, Category.id_comp]; rfl

  have root : ∀ w : ((TF (R := R) K).left.presheaf.stalk (closedPoint K))ˣ, w ^ n = 1 → w ∈ H := by
    intro w hw
    have hinj : Function.Injective ((algebraMap (FractionRing R) K).comp (algebraMap R (FractionRing R))) :=
      (algebraMap (FractionRing R) K).injective.comp (IsFractionRing.injective R _)
    have hζ' := hζ.map_of_injective hinj
    have : NeZero n := ⟨by omega⟩
    have hw' : (sig K w : K) ^ n = 1 := by
      rw [← Units.val_pow_eq_pow_val, ← map_pow, hw, map_one, Units.val_one]
    obtain ⟨i, -, hi⟩ := hζ'.eq_pow_of_pow_eq_one hw'
    have e : σ (sig K w : K) = (sig K w : K) :=
      (congrArg σ hi.symm).trans ((map_pow σ _ i).trans ((congrArg (· ^ i) (σ.commutes _)).trans hi))
    exact Units.ext e

  have img : ∀ a : Q.X, charVal t (F.f • F.xi a) (closedPoint K) J ∈ H := by
    intro a
    obtain ⟨d, hd⟩ := exists_c_eq_pow T iw s ε hn Q e hQ a
    have hc : cP D'.toPre (TF (R := R) K) (F.f • F.xi a) = (toUnit _ ≫ (d ≫ F.inc) ≫ F.o.onB.act F.f) ^ n := by
      rw [cP, F.o.c_lin, F.c_xi, hd, MonObj.pow_comp, MonObj.pow_comp, MonObj.comp_pow]
    have hbn : t.b ^ n = 1 := by rw [← nsmul_b, hnt, zero_b]
    obtain ⟨h, hh, e₁⟩ := cubN_pow_eq_pow C P H hθ hbP (hP ((d ≫ F.inc) ≫ F.o.onB.act F.f)) hbn
    have e₂ := charVal_pow t (F.f • F.xi a) hJ n
    rw [hnt, zero_val (D := D'.toPre) (F := K) _ hJ, _root_.one_mul, hc, e₁] at e₂
    have := H.mul_mem (root (charVal t (F.f • F.xi a) (closedPoint K) J * h⁻¹)
      (by rw [mul_pow, ← e₂, inv_pow, mul_inv_cancel])) hh
    rwa [inv_mul_cancel_right] at this
  intro χ
  obtain ⟨a, ha⟩ := F.onto χ
  obtain ⟨h, hh, e₁⟩ := rel χ
  obtain ⟨h', hh', e₂⟩ := rel (F.f • F.xi a)
  have m : charVal t χ (closedPoint K) J ∈ H := by
    rw [e₁, ha, eq_mul_inv_of_mul_eq e₂.symm]
    exact H.mul_mem (H.mul_mem (img a) (H.inv_mem hh')) hh
  exact congrArg Units.val m

end GlobalTheory.Mum.ETors
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CharactersEightfoldProductEqEighthPower
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.Poinc.Eq8

noncomputable section

namespace GlobalTheory.Poinc.Eq8.Chars8

theorem prod_comp {S : Scheme.{0}} {T G H : Over S} [GrpObj G] [IsCommMonObj G] [GrpObj H] [IsCommMonObj H]
    (g : G ⟶ H) [IsMonHom g] {κ : Type} (s : Finset κ) (f : κ → (T ⟶ G)) :
    (∏ i ∈ s, f i) ≫ g = ∏ i ∈ s, (f i ≫ g) := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.prod_empty, Finset.prod_empty, MonObj.one_comp]
  | insert a s ha ih => rw [Finset.prod_insert ha, Finset.prod_insert ha, MonObj.mul_comp, ih]

theorem main : ∀ (V₁ : Type) [CommRing V₁] [IsDomain V₁] [IsLocalRing V₁], IsCN V₁ → ∀ (D₀ : DegData V₁ (maximalIdeal V₁)) (A₀ : PolAV (Sp (FractionRing V₁))) (G₀ : Over (Sp V₁)) [GrpObj G₀] [IsCommMonObj G₀], IsSemiAbelian G₀ → ∀ (U₀ : Unif (maximalIdeal V₁) D₀ A₀ G₀) (D : DegData V₁ (maximalIdeal V₁)) (P : PolAV (Sp (FractionRing V₁))) (G : Over (Sp V₁)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (U : Unif (maximalIdeal V₁) D P G) (q : Fin 8 → (G ⟶ G₀)), (∀ u, IsMonHom (q u)) → (∀ (T' : Over (Sp V₁)) (y' : Fin 8 → (T' ⟶ G₀)), ∃! x : T' ⟶ G, ∀ u, x ≫ q u = y' u) → ∃ c : Fin 8 → (D₀.toPre.X →+ D.toPre.X), (∀ u, TorMatch U₀ U (RingHom.id V₁) (q u).left (c u)) ∧ Function.Bijective (fun χ : Fin 8 → D₀.toPre.X => ∑ u, c u (χ u)) := by
  intro V₁ _ _ _ hCN D₀ A₀ G₀ _ _ hG₀ U₀ D P G _ _ hG U q hq huniv
  have hB : GlobalTheory.Mum.Base V₁ := ⟨⟨hCN.1, inferInstance, hCN.2.1, hCN.2.2.1⟩, hCN.2.2.2⟩
  choose c hc using fun u => GlobalTheory.Poinc.HomTor.exists_torMatch V₁ hB G₀ hG₀ D₀ A₀ U₀ G hG D P U (q u) (hq u)

  let y : Fin 8 → Fin 8 → (G₀ ⟶ G₀) := fun u v => if v = u then 𝟙 G₀ else 1
  choose sc hsc _ using fun u => huniv G₀ (y u)
  have hscm : ∀ u, IsMonHom (sc u) := fun u => isMonHom_of_mul _ fun T a b => by
    refine (huniv T (fun v => (a * b) ≫ y u v)).unique (fun v => ?_) (fun v => ?_)
    · rw [Category.assoc, hsc]
    · haveI := hq v
      rw [MonObj.mul_comp, Category.assoc, Category.assoc, hsc]
      by_cases h : v = u
      · simp only [y, h, if_true, Category.comp_id]
      · simp only [y, h, if_false, comp_one, _root_.mul_one]
  choose d hd using fun u => GlobalTheory.Poinc.HomTor.exists_torMatch V₁ hB G hG D P U G₀ hG₀ D₀ A₀ U₀ (sc u) (hscm u)
  obtain ⟨hid₀, hone₀, -⟩ := torMatch_id_one_mul V₁ hB G₀ hG₀ D₀ A₀ U₀ G₀ hG₀ D₀ A₀ U₀
  obtain ⟨hid, hone, hmul⟩ := torMatch_id_one_mul V₁ hB G hG D P U G hG D P U

  have dc : ∀ u v, (d u).comp (c v) = if v = u then AddMonoidHom.id _ else 0 := by
    intro u v
    have h := torMatch_comp V₁ hB G₀ hG₀ D₀ A₀ U₀ V₁ hB G hG D P U (RingHom.id V₁) (q v).left V₁ hB G₀ hG₀ D₀ A₀ U₀
      (RingHom.id V₁) (sc u).left Function.injective_id (fun k hk => hk) (c v) (d u) (hc v) (hd u)
    rw [RingHom.id_comp, ← Over.comp_left, hsc] at h
    by_cases huv : v = u
    · simp only [y, huv, if_true, Over.id_left] at h ⊢
      exact torMatch_unique V₁ hB G₀ hG₀ D₀ A₀ U₀ V₁ hB G₀ hG₀ D₀ A₀ U₀ (RingHom.id V₁) _ Function.injective_id _ _ h hid₀
    · simp only [y, huv, if_false] at h ⊢
      exact torMatch_unique V₁ hB G₀ hG₀ D₀ A₀ U₀ V₁ hB G₀ hG₀ D₀ A₀ U₀ (RingHom.id V₁) _ Function.injective_id _ _ h hone₀
  have dsum : ∀ (χ : Fin 8 → D₀.toPre.X) w, d w (∑ u, c u (χ u)) = χ w := by
    intro χ w
    rw [map_sum, Finset.sum_eq_single w]
    · have := DFunLike.congr_fun (dc w w) (χ w)
      simpa using this
    · intro b _ hb
      have := DFunLike.congr_fun (dc w b) (χ b)
      simpa [hb] using this
    · intro h; exact absurd (Finset.mem_univ w) h

  have hprod : (∏ v, q v ≫ sc v) = 𝟙 G := by
    refine (huniv G q).unique (fun w => ?_) (fun w => Category.id_comp _)
    haveI := hq w
    rw [prod_comp, Finset.prod_eq_single w]
    · rw [Category.assoc, hsc]; simp only [y, if_true, Category.comp_id]
    · intro b _ hb
      rw [Category.assoc, hsc]
      simp only [y, Ne.symm hb, if_false, comp_one]
    · intro h; exact absurd (Finset.mem_univ w) h
  have hs : ∀ s : Finset (Fin 8), TorMatch U U (RingHom.id V₁) (∏ v ∈ s, q v ≫ sc v).left
      (∑ v ∈ s, (c v).comp (d v)) := by
    intro s
    induction s using Finset.induction_on with
    | empty => rw [Finset.prod_empty, Finset.sum_empty]; exact hone
    | insert a s ha ih =>
      rw [Finset.prod_insert ha, Finset.sum_insert ha]
      refine hmul _ _ _ _ ?_ ih
      have h := torMatch_comp V₁ hB G hG D P U V₁ hB G₀ hG₀ D₀ A₀ U₀ (RingHom.id V₁) (sc a).left V₁ hB G hG D P U
        (RingHom.id V₁) (q a).left Function.injective_id (fun k hk => hk) (d a) (c a) (hd a) (hc a)
      rwa [RingHom.id_comp, ← Over.comp_left] at h
  have hsum : (∑ v, (c v).comp (d v)) = AddMonoidHom.id _ := by
    have h := hs Finset.univ
    rw [hprod, Over.id_left] at h
    exact torMatch_unique V₁ hB G hG D P U V₁ hB G hG D P U (RingHom.id V₁) _ Function.injective_id _ _ h hid
  refine ⟨c, hc, fun χ χ' h => funext fun w => ?_, fun z => ⟨fun v => d v z, ?_⟩⟩
  · rw [← dsum χ w, ← dsum χ' w]; exact congrArg (d w) h
  · have := DFunLike.congr_fun hsum z
    rw [AddMonoidHom.finset_sum_apply] at this
    simpa using this

end GlobalTheory.Poinc.Eq8.Chars8

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CharactersEighthPowerElementaryMatrices
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

namespace GlobalTheory.Poinc.Eq8.PowChar

theorem isMonHom_of_coords {S : Scheme.{0}} {B C X : Over S} [GrpObj B] [GrpObj C] [GrpObj X]
    (pr : Fin 8 → (B ⟶ C)) (hpr : ∀ a, IsMonHom (pr a))
    (huniv : ∀ (T : Over S) (y : Fin 8 → (T ⟶ C)), ∃! x : T ⟶ B, ∀ a, x ≫ pr a = y a)
    (z : X ⟶ B) (h : ∀ a, IsMonHom (z ≫ pr a)) : IsMonHom z := by
  refine GlobalTheory.GrpPullPow.isMonHom_of_mul_pts z fun T x y => ?_
  refine (huniv T (fun a => (x * y) ≫ z ≫ pr a)).unique (fun a => Category.assoc _ _ _) (fun a => ?_)
  haveI := hpr a
  haveI := h a
  rw [MonObj.mul_comp, Category.assoc, Category.assoc, ← MonObj.mul_comp]

theorem isMonHom_one {S : Scheme.{0}} {B C : Over S} [GrpObj B] [GrpObj C] : IsMonHom (1 : B ⟶ C) :=
  inferInstanceAs (IsMonHom (toUnit B ≫ η[C]))

theorem exists_incl {S : Scheme.{0}} {B C : Over S} [GrpObj B] [GrpObj C]
    (pr : Fin 8 → (B ⟶ C)) (hpr : ∀ a, IsMonHom (pr a))
    (huniv : ∀ (T : Over S) (y : Fin 8 → (T ⟶ C)), ∃! x : T ⟶ B, ∀ a, x ≫ pr a = y a) :
    ∃ z : Fin 8 → (C ⟶ B), (∀ u, IsMonHom (z u)) ∧ ∀ u v, z u ≫ pr v = if v = u then 𝟙 C else 1 := by
  choose z hz _ using fun u : Fin 8 => huniv C (fun v => if v = u then 𝟙 C else 1)
  refine ⟨z, fun u => isMonHom_of_coords pr hpr huniv (z u) fun a => ?_, hz⟩
  rw [hz u a]
  split_ifs
  · infer_instance
  · exact isMonHom_one

end GlobalTheory.Poinc.Eq8.PowChar

namespace GlobalTheory.Poinc.Eq8.PowChar

theorem isMonHom_prod {S : Scheme.{0}} {X M : Over S} [GrpObj X] [GrpObj M] [IsCommMonObj M] {J : Type}
    (f : J → (X ⟶ M)) (hf : ∀ i, IsMonHom (f i)) (s : Finset J) : IsMonHom (∏ i ∈ s, f i) := by
  refine Finset.induction_on s ?_ ?_
  · rw [Finset.prod_empty]; exact isMonHom_one
  · intro a s ha ih
    rw [Finset.prod_insert ha]
    haveI := hf a
    exact inferInstanceAs (IsMonHom (lift (f a) (∏ i ∈ s, f i) ≫ μ[M]))

theorem prod_comp {S : Scheme.{0}} {X M N : Over S} [GrpObj M] [GrpObj N] [IsCommMonObj M] [IsCommMonObj N] {J : Type}
    (f : J → (X ⟶ M)) (s : Finset J) (g : M ⟶ N) [IsMonHom g] : (∏ i ∈ s, f i) ≫ g = ∏ i ∈ s, f i ≫ g := by
  refine Finset.induction_on s ?_ ?_
  · rw [Finset.prod_empty, Finset.prod_empty, MonObj.one_comp]
  · intro a s ha ih
    rw [Finset.prod_insert ha, Finset.prod_insert ha, MonObj.mul_comp, ih]

end GlobalTheory.Poinc.Eq8.PowChar

namespace GlobalTheory.Poinc.Eq8

open PowChar in

theorem characters_eighthPower_elementaryMatrices : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], GlobalTheory.Mum.Base R → IsDiscreteValuationRing R → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (U : Unif (maximalIdeal R) D A G) (G' : Over (Sp R)) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ∀ (D' : DegData R (maximalIdeal R)) (A' : PolAV (Sp (FractionRing R))) (U' : Unif (maximalIdeal R) D' A' G') (W : Matrix (Fin 8) (Fin 8) ℤ), IsE8 W → ∀ (pr : Fin 8 → (A'.A ⟶ A.A)), (∀ a, IsMonHom (pr a)) → (∀ (T' : Over (Sp (FractionRing R))) (y : Fin 8 → (T' ⟶ A.A)), ∃! z : T' ⟶ A'.A, ∀ a, z ≫ pr a = y a) → LBIso A'.L (LB.LinComb (abelian₂ A.A A.L) (K := Fin 8 × Fin 8) (fun ab => (lift (pr ab.1) (pr ab.2)).left) (fun ab => W ab.1 ab.2)) → ∀ (pG : Fin 8 → (G' ⟶ G)), (∀ v, IsMonHom (pG v)) → (∀ v, (Over.pullback (jK R)).map (pG v) ≫ U.gen.hom = U'.gen.hom ≫ pr v) → ∀ (c : Fin 8 → (D.toPre.X →+ D'.toPre.X)), (∀ v, TorMatch U U' (RingHom.id R) (pG v).left (c v)) → (Function.Bijective fun y : Fin 8 → D.toPre.X => ∑ v, c v (y v)) ∧ ∀ (a b : Fin 8) (f : G' ⟶ G') (f₁ : A'.A ⟶ A'.A) (m : D'.toPre.X →+ D'.toPre.X), IsMonHom f → MatEnd pr a b f₁ → (Over.pullback (jK R)).map f ≫ U'.gen.hom = U'.gen.hom ≫ f₁ → EndChar U' f m → ∀ w x, m (c w x) = if w = a then c b x else 0 := by
  intro R _ _ _ hR hdvr G _ _ hG D A U G' _ _ hG' D' A' U' W _ pr hpr huniv _ pG hpG hgen c hc
  haveI := hdvr
  haveI := U.gen_hom
  haveI := U'.gen_hom
  have ext : ∀ {H H' : Over (Sp R)} [GrpObj H] [GrpObj H'], IsSemiAbelian H → IsSemiAbelian H' →
      ∀ (F₁ F₂ : H ⟶ H'), IsMonHom F₁ → IsMonHom F₂ →
        (Over.pullback (jK R)).map F₁ = (Over.pullback (jK R)).map F₂ → F₁ = F₂ := by
    intro H H' _ _ h h' F₁ F₂ h₁ h₂ e
    exact (GlobalTheory.semiAbelian_hom_extends_uniquely_dvr R (FractionRing R) H H' h h' _ inferInstance).unique
      ⟨h₁, e⟩ ⟨h₂, rfl⟩
  obtain ⟨z, hzm, hz⟩ := exists_incl pr hpr huniv
  have hic : ∀ u, ∃ ic : G ⟶ G', IsMonHom ic ∧ (Over.pullback (jK R)).map ic = U.gen.hom ≫ z u ≫ U'.gen.inv := by
    intro u
    haveI := hzm u
    obtain ⟨F, ⟨hF, hF'⟩, -⟩ := GlobalTheory.semiAbelian_hom_extends_uniquely_dvr R (FractionRing R) G G' hG hG'
      (U.gen.hom ≫ z u ≫ U'.gen.inv) inferInstance
    exact ⟨F, hF, hF'⟩
  choose ic hicm hicg using hic
  have hicp : ∀ u v, ic u ≫ pG v = if v = u then 𝟙 G else 1 := by
    intro u v
    haveI := hicm u
    haveI := hpG v
    have key : (Over.pullback (jK R)).map (ic u ≫ pG v) ≫ U.gen.hom = U.gen.hom ≫ (if v = u then 𝟙 A.A else 1) := by
      rw [Functor.map_comp, Category.assoc, hgen v, ← Category.assoc, hicg u]
      simp only [Category.assoc, Iso.inv_hom_id_assoc, hz u v]
    by_cases h : v = u
    · rw [if_pos h] at key ⊢
      refine ext hG hG _ _ inferInstance inferInstance ?_
      rw [← cancel_mono U.gen.hom, key, CategoryTheory.Functor.map_id, Category.id_comp, Category.comp_id]
    · rw [if_neg h] at key ⊢
      refine ext hG hG _ _ inferInstance isMonHom_one ?_
      rw [← cancel_mono U.gen.hom, key, Functor.map_one, MonObj.comp_one, MonObj.one_comp]
  have hpw : ∀ w, (∏ v, pG v ≫ ic v) ≫ pG w = pG w := by
    intro w
    haveI := hpG w
    rw [PowChar.prod_comp, Finset.prod_eq_single w]
    · rw [Category.assoc, hicp w w, if_pos rfl, Category.comp_id]
    · intro v _ hv
      rw [Category.assoc, hicp v w, if_neg (Ne.symm hv), MonObj.comp_one]
    · intro h
      exact absurd (Finset.mem_univ w) h
  have hprod : (∏ v, pG v ≫ ic v) = 𝟙 G' := by
    have hm : IsMonHom (∏ v, pG v ≫ ic v) :=
      isMonHom_prod _ (fun v => by haveI := hpG v; haveI := hicm v; infer_instance) _
    refine ext hG' hG' _ _ hm inferInstance ?_
    rw [CategoryTheory.Functor.map_id, ← cancel_mono U'.gen.hom, Category.id_comp]
    refine (huniv _ (fun w => U'.gen.hom ≫ pr w)).unique (fun w => ?_) (fun w => rfl)
    rw [Category.assoc, ← hgen w, ← Category.assoc, ← Functor.map_comp, hpw w]
  have hinj : Function.Injective (RingHom.id R) := Function.injective_id
  have hk : ∀ k : ℕ, IsUnit (k : R) → IsUnit (k : R) := fun _ h => h
  choose d hd using fun u => GlobalTheory.Poinc.HomTor.exists_torMatch R hR G' hG' D' A' U' G hG D A U (ic u) (hicm u)
  obtain ⟨hid, hone, -⟩ := torMatch_id_one_mul R hR G hG D A U G hG D A U
  obtain ⟨hid', hone', hmul'⟩ := torMatch_id_one_mul R hR G' hG' D' A' U' G' hG' D' A' U'
  obtain ⟨-, hone'', -⟩ := torMatch_id_one_mul R hR G hG D A U G' hG' D' A' U'
  have hdc : ∀ u v, (d u).comp (c v) = if v = u then AddMonoidHom.id _ else 0 := by
    intro u v
    have h1 := torMatch_comp R hR G hG D A U R hR G' hG' D' A' U' (RingHom.id R) (pG v).left R hR G hG D A U
      (RingHom.id R) (ic u).left hinj hk (c v) (d u) (hc v) (hd u)
    rw [← Over.comp_left, hicp u v, RingHom.id_comp] at h1
    by_cases h : v = u
    · rw [if_pos h] at h1 ⊢
      rw [Over.id_left] at h1
      exact torMatch_unique R hR G hG D A U R hR G hG D A U _ _ hinj _ _ h1 hid
    · rw [if_neg h] at h1 ⊢
      exact torMatch_unique R hR G hG D A U R hR G hG D A U _ _ hinj _ _ h1 hone
  have hcd : ∑ v, (c v).comp (d v) = AddMonoidHom.id _ := by
    have hs : ∀ s : Finset (Fin 8), TorMatch U' U' (RingHom.id R) (∏ v ∈ s, pG v ≫ ic v).left
        (∑ v ∈ s, (c v).comp (d v)) := by
      intro s
      refine Finset.induction_on s ?_ ?_
      · rw [Finset.prod_empty, Finset.sum_empty]
        exact hone'
      · intro a s ha ih
        rw [Finset.prod_insert ha, Finset.sum_insert ha]
        have h1 := torMatch_comp R hR G' hG' D' A' U' R hR G hG D A U (RingHom.id R) (ic a).left R hR G' hG' D' A' U'
          (RingHom.id R) (pG a).left hinj hk (d a) (c a) (hd a) (hc a)
        rw [← Over.comp_left, RingHom.id_comp] at h1
        exact hmul' _ _ _ _ h1 ih
    have h2 := hs Finset.univ
    rw [hprod, Over.id_left] at h2
    exact torMatch_unique R hR G' hG' D' A' U' R hR G' hG' D' A' U' _ _ hinj _ _ h2 hid'
  refine ⟨?_, ?_⟩
  · rw [Function.bijective_iff_has_inverse]
    refine ⟨fun x u => d u x, fun y => ?_, fun x => ?_⟩
    · funext u
      have e : ∀ v, d u (c v (y v)) = if v = u then y v else 0 := fun v => by
        have := DFunLike.congr_fun (hdc u v) (y v)
        rw [AddMonoidHom.comp_apply] at this
        rw [this]
        split_ifs <;> rfl
      simp only [map_sum, e, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    · have := DFunLike.congr_fun hcd x
      simpa [AddMonoidHom.finset_sum_apply] using this
  · intro a b f f₁ m hf hf₁ hff₁ hm w x
    haveI := hf
    haveI := hpG w
    have hfp : f ≫ pG w = if w = a then pG b else 1 := by
      have key : (Over.pullback (jK R)).map (f ≫ pG w) ≫ U.gen.hom = U'.gen.hom ≫ (if w = a then pr b else 1) := by
        rw [Functor.map_comp, Category.assoc, hgen w, ← Category.assoc, hff₁, Category.assoc, hf₁.2 w]
      by_cases h : w = a
      · rw [if_pos h] at key ⊢
        refine ext hG' hG _ _ inferInstance (hpG b) ?_
        rw [← cancel_mono U.gen.hom, key, hgen b]
      · rw [if_neg h] at key ⊢
        refine ext hG' hG _ _ inferInstance isMonHom_one ?_
        rw [← cancel_mono U.gen.hom, key, Functor.map_one, MonObj.comp_one, MonObj.one_comp]
    have h1 := torMatch_comp R hR G hG D A U R hR G' hG' D' A' U' (RingHom.id R) (pG w).left R hR G' hG' D' A' U'
      (RingHom.id R) f.left hinj hk (c w) m (hc w) (GlobalTheory.Poinc.TorEnd.torMatch_of_endChar R hR G' hG' D' A' U' f hf m hm)
    rw [← Over.comp_left, hfp, RingHom.id_comp] at h1
    have e : m.comp (c w) = if w = a then c b else 0 := by
      by_cases h : w = a
      · rw [if_pos h] at h1 ⊢
        exact torMatch_unique R hR G hG D A U R hR G' hG' D' A' U' _ _ hinj _ _ h1 (hc b)
      · rw [if_neg h] at h1 ⊢
        exact torMatch_unique R hR G hG D A U R hR G' hG' D' A' U' _ _ hinj _ _ h1 hone''
    have := DFunLike.congr_fun e x
    rw [AddMonoidHom.comp_apply] at this
    rw [this]
    split_ifs <;> rfl

end GlobalTheory.Poinc.Eq8
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChartValueIsIntegralOfIntegralAtPointsStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chartValue_isIntegral_of_integral_at_points : ∀ {X Y : Scheme.{0}} (L : LB X) (α : Y ⟶ X) (k : ℕ) (s : SecK L α k) (j : L.ι) (W : X.Opens) (hW : W ≤ L.U j), IsAffineOpen W → IsAffineOpen (α ⁻¹ᵁ W) → (∀ x ∈ W, IntAt L α s x) → (α.app W).hom.IsIntegralElem (chartVal L α s j W hW) := by
  first | exact @GlobalTheory.Mum.chartVal_isIntegral_of_intAt | exact GlobalTheory.Mum.chartVal_isIntegral_of_intAt | (intros; apply GlobalTheory.Mum.chartVal_isIntegral_of_intAt <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChartValueMemRangeOfAgreeTraitExtensionStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chartValue_mem_range_of_agree_traitExtension : ∀ (X S Y : Scheme.{0}) (gX : X ⟶ S) (L : LB X), L.IsLB → ∀ (α : Y ⟶ X) (k : ℕ) (s : SecK L α k) (j : L.ι) (W : X.Opens) (hW : W ≤ L.U j) (hWa : IsAffineOpen W), IsAffineOpen (α ⁻¹ᵁ W) → ∀ (T : Type) [CommRing T] (lam : Γ(X, W) →+* T) (W' : Type) [CommRing W'] (io : T →+* W') (σ : SecK L (pullback.fst gX (spMap io ≫ Spec.map (CommRingCat.ofHom lam) ≫ hWa.fromSpec ≫ gX)) k), Agree L σ s → ∀ (Ω : Type) [Field Ω] (ψ : Γ(Y, α ⁻¹ᵁ W) →+* Ω) (e : W' →+* Ω), (∀ c, ψ ((α.app W).hom c) = e (io (lam c))) → ∃ w : W', ψ (chartVal L α s j W hW) = e w := by
  first | exact @GlobalTheory.Mum.chartVal_mem_range_of_agree | exact GlobalTheory.Mum.chartVal_mem_range_of_agree | (intros; apply GlobalTheory.Mum.chartVal_mem_range_of_agree <;> assumption)
end

