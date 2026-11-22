import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2811
import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle0001
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2956
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1097
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0008
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2941
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2552
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2908
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RosVal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2687
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2928
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2828
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2868
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2686
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0099
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2889
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0067
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0134
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0142
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2913
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0081
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle0002
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsExtensionSecPull
import Development.AbelianVarietyTheory.Definitions.Divisors.IsActIffIsDiagEnd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2801
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.QkToAkUInvariantUnderFieldEmbedding
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.TxFrameTranslate
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1139
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SectionValueEqAdicSumAtImageOfZeroPair
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1644
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.RelationsAreFunctions
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.GtActIffEqGtSmul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2914
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.ImmersedBy
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2870
import Development.AbelianVarietyTheory.Definitions.Divisors.IsHolPeriods

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsThetaFrameCubeConstantRootOfUnity
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.Poinc.Sep

open GlobalTheory.Poinc.Tors

noncomputable section

namespace GlobalTheory.Poinc.CubeConst

section General

variable {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [IsCommMonObj G] [GrpObj G'] [IsCommMonObj G']

theorem cubV_through (hG : GlobalFnsSt) (hA : IsAbelianScheme G') {f : S' ⟶ S} {F : G'.left ⟶ G.left}
    (gp : IsGrpPullback G' G f F) {L : RigLB G} {L' : RigLB G'} (c : CubicalStr G L) (c' : CubicalStr G' L')
    (w : LB.Iso L'.L (L.L.pull F)) (hw : w.IsGen) {T : Over S'} (z : T.left) {J J'} (hJ : Good L.L z J)
    (hJ' : Good L'.L z J') (x y u : T ⟶ G') :
    cubV c (T := Over.mk (T.hom ≫ f)) z J (pushHom gp T x) (pushHom gp T y) (pushHom gp T u) =
      GlobalTheory.ConstFam.wVal w z J J' (x * y * u).left * (GlobalTheory.ConstFam.wVal w z J J' (x * y).left)⁻¹ *
        (GlobalTheory.ConstFam.wVal w z J J' (x * u).left)⁻¹ * (GlobalTheory.ConstFam.wVal w z J J' (y * u).left)⁻¹ *
        GlobalTheory.ConstFam.wVal w z J J' x.left * GlobalTheory.ConstFam.wVal w z J J' y.left * GlobalTheory.ConstFam.wVal w z J J' u.left *
        (GlobalTheory.ConstFam.wVal w z J J' (1 : T ⟶ G').left)⁻¹ * cubV c' z J' x y u := by
  let Y : Over S' := G' ⊗ G' ⊗ G'
  let H : Over.mk (Y.hom ≫ f) ⟶ G ⊗ G ⊗ G :=
    lift (pushHom gp Y (x3 G' 0)) (lift (pushHom gp Y (x3 G' 1)) (pushHom gp Y (x3 G' 2)))
  have hψ : ∀ I : thK.{0}, thφ G' (x3 G') I ≫ F = H.left ≫ thφ G (x3 G) I := fun I => by
    have e₁ := psum_hom (pushHom gp Y) (x3 G') I.down
    have e₂ := psum_hom (preHom H) (x3 G) I.down
    have e₃ : (fun i => pushHom gp Y (x3 G' i)) = fun i => preHom H (x3 G i) :=
      funext fun i => by fin_cases i <;> simp [preHom, x3, H]
    exact congrArg (fun q => q.left) (e₁.trans ((congrArg (fun q => psum G q I.down) e₃).trans e₂.symm))
  obtain ⟨a, ha, hv⟩ := GlobalTheory.ConstFam.exists_gen_through (φ' := thφ G' (x3 G')) (φ := thφ G (x3 G)) (ε := thε)
    (h := H.left) hw L.isLB L'.isLB hψ c.t c.isGen
  have ev : ∀ {T : Over S'} (z : T.left) {J J'}, Good L.L z J → Good L'.L z J' → ∀ x y u : T ⟶ G',
      cubV c (T := Over.mk (T.hom ≫ f)) z J (pushHom gp T x) (pushHom gp T y) (pushHom gp T u) =
      GlobalTheory.ConstFam.wVal w z J J' (x * y * u).left * (GlobalTheory.ConstFam.wVal w z J J' (x * y).left)⁻¹ *
        (GlobalTheory.ConstFam.wVal w z J J' (x * u).left)⁻¹ * (GlobalTheory.ConstFam.wVal w z J J' (y * u).left)⁻¹ *
        GlobalTheory.ConstFam.wVal w z J J' x.left * GlobalTheory.ConstFam.wVal w z J J' y.left * GlobalTheory.ConstFam.wVal w z J J' u.left *
        (GlobalTheory.ConstFam.wVal w z J J' (1 : T ⟶ G').left)⁻¹ * val a (lift x (lift y u)).left z J' := by
    intro T z J J' hJ hJ' x y u
    have e := hv _ (lift x (lift y u)).left z J J' hJ hJ'
    refine Eq.trans ?_ (e.trans (congrArg (· * _) (prod_cub x y u (GlobalTheory.ConstFam.wVal w z J J'))))
    let R : Over.mk (T.hom ≫ f) ⟶ Over.mk (Y.hom ≫ f) := (Over.map f).map (lift x (lift y u))
    have p : ∀ q : Y ⟶ G', R ≫ pushHom gp Y q = pushHom gp T (lift x (lift y u) ≫ q) := fun q =>
      Over.OverMorphism.ext (Category.assoc _ _ _).symm
    have q : lift (pushHom gp T x) (lift (pushHom gp T y) (pushHom gp T u)) = R ≫ H := by
      simp only [H, comp_lift, p]
      simp [x3]
    exact congrArg (fun r => val (L := L.L) (φ := thφ G (x3 G)) (ε := thε) c.t r z J) (congrArg (fun q => q.left) q)
  have sj : Function.Surjective (Y.hom).appTop.hom := by
    have := surj_comp (surj_snd hG hA (G' ⊗ G')) (surj_comp (surj_snd hG hA G') (hG _ _ hA).2)
    rwa [Over.w, Over.w] at this
  have key := gen_unique (φ := thφ G' (x3 G')) (ε := thε) L'.isLB Y.hom
    (lift (1 : 𝟙_ (Over S') ⟶ G') (lift (1 : 𝟙_ (Over S') ⟶ G') (1 : 𝟙_ (Over S') ⟶ G'))).left (Over.w _) sj ha c'.isGen
    (fun y I' hI' => by
      obtain ⟨I, hI⟩ := GlobalTheory.ConstFam.exists_good' L.isLB y
      have E := ev (T := 𝟙_ (Over S')) y hI hI' 1 1 1
      rw [map_one, (isCub_cubV c hI).face] at E
      refine Eq.trans ?_ ((isCub_cubV (T := 𝟙_ (Over S')) c' hI').face 1 1).symm
      have fin : ∀ {A U : Type} [Group A] [CommGroup U] (h : A → U) (b : U), 1 = h (1 * 1 * 1) * (h (1 * 1))⁻¹ *
        (h (1 * 1))⁻¹ * (h (1 * 1))⁻¹ * h 1 * h 1 * h 1 * (h 1)⁻¹ * b → b = 1 := fun h b e => by
          simpa using e.symm
      exact fin (fun q : 𝟙_ (Over S') ⟶ G' => GlobalTheory.ConstFam.wVal w y I I' q.left) _ E) _
    (lift x (lift y u)).left z J' hJ'
  exact (ev z hJ hJ' x y u).trans (congrArg _ key)

theorem exists_cube_const {L : RigLB G} (c : CubicalStr G L) {T : Over S} {Γ' : Type} [AddCommGroup Γ']
    (pt : Γ' → (T ⟶ G)) (hadd : ∀ a b, pt (a + b) = pt a * pt b)
    (fr : ∀ a, LB.Gen (LB.LinComb L.L (K := Fin 1) (fun _ => (pt a).left) (fun _ => 1))) (hfr : ∀ a, (fr a).IsGen) (a a' a'' : Γ') :
    ∃ k : Γ(T.left, ⊤), ∀ (T' : Over S) (ρ : T' ⟶ T) (z : T'.left) (J), Good L.L z J →
      (cubV c z J (ρ ≫ pt a) (ρ ≫ pt a') (ρ ≫ pt a'') * ((val (fr (a + a')) ρ.left z J * val (fr (a + a'')) ρ.left z J *
        val (fr (a' + a'')) ρ.left z J * val (fr 0) ρ.left z J) * (val (fr (a + a' + a'')) ρ.left z J *
          val (fr a) ρ.left z J * val (fr a') ρ.left z J * val (fr a'') ρ.left z J)⁻¹)).val = gs ρ.left z ⊤ k := by
  have h0 : pt 0 = 1 := mul_eq_left.1 ((hadd 0 0).symm.trans (by rw [add_zero]))
  have g4 := fun b₁ b₂ b₃ b₄ => mulGen_isGen _ _ _ _ _ _ _ (mulGen_isGen _ _ _ _ _ _ _
    (mulGen_isGen _ _ _ _ _ _ _ (hfr b₁) (hfr b₂)) (hfr b₃)) (hfr b₄)
  obtain ⟨k, hk⟩ := H1.exists_const L.L L.isLB (𝟙 T.left) (fun b => ⟨b, rfl⟩) _
    (mulGen_isGen _ _ _ _ _ _ _ (pullGen_isGen L.L (thφ G (x3 G)) thε c.t c.isGen
      (lift (pt a) (lift (pt a') (pt a''))).left)
      (mulGen_isGen _ _ _ _ _ _ _ (g4 (a + a') (a + a'') (a' + a'') 0)
        (invGen_isGen _ _ _ _ (g4 (a + a' + a'') a a' a'')))) (fun U _ h => by
      refine ((Fintype.prod_sum_type _).trans (congrArg₂ (· * ·) (prod_cub (pt a) (pt a') (pt a'') h) rfl)).trans ?_
      simp only [Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr, Fintype.prod_unique, hadd, h0, zpow_neg, zpow_one]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv, ofMul_one]
      abel)
  refine ⟨k, fun T' ρ z J hJ => ?_⟩
  have e := hk _ ρ.left z J hJ
  rw [Category.comp_id] at e
  refine Eq.trans (congrArg Units.val ?_) e
  have v4 := fun b₁ b₂ b₃ b₄ => (val_mul hJ (LB.mulGen _ _ _ _ _ (LB.mulGen _ _ _ _ _ (fr b₁) (fr b₂)) (fr b₃)) (fr b₄)
    ρ.left).trans (congrArg (· * _) ((val_mul hJ _ _ _).trans (congrArg (· * _) (val_mul hJ _ _ _))))
  exact ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) (val_cub c ρ hJ _ _ _) ((val_mul hJ _ _ _).trans
    (congrArg₂ (· * ·) (v4 _ _ _ _) ((val_inv _ _).trans (congrArg (·⁻¹) (v4 _ _ _ _))))))).symm

end General

section Torsion

open GlobalTheory.ThetaCompare

variable {S : Scheme.{0}}

theorem reg_cub {A T : Over S} [GrpObj A] [IsCommMonObj A] {L : RigLB A} (c : CubicalStr A L) {y : T.left} {J}
    (hJ : Good L.L y J) (m₁ m₂ m₃ : T ⊗ A ⟶ A) :
    Reg L.L y J (fun _ _ h => h (m₁ * m₂ * m₃) * (h (m₁ * m₂))⁻¹ * (h (m₁ * m₃))⁻¹ * (h (m₂ * m₃))⁻¹ * h m₁ * h m₂ *
      h m₃ * (h 1)⁻¹) (fun z => cubV c y J (ptSecT A z ≫ m₁) (ptSecT A z ≫ m₂) (ptSecT A z ≫ m₃)) :=
  ⟨_, _, _, _, LB.pullGen L.L (thφ A (x3 A)) thε c.t (lift m₁ (lift m₂ m₃)).left,
    pullGen_isGen _ _ _ _ c.isGen _, fun _ _ h => prod_cub m₁ m₂ m₃ h, fun a => val_cub c (ptSecT A a) hJ _ _ _⟩

theorem cube_torsFrame_pow (hG : GlobalFnsSt) (P : PolAV S) [IsCommMonObj P.A] {rig : LB.Gen (P.L.pull (eSec P.A))}
    {hrig : rig.IsGen} (c : CubicalStr P.A ⟨P.L, rig, P.isLB, hrig⟩) {T : Over S} {Γ' : Type} [AddCommGroup Γ']
    (pt : Γ' → (T ⟶ P.A)) (hadd : ∀ a b, pt (a + b) = pt a * pt b) {m : ℕ}
    (fr : ∀ a, LB.Gen (LB.LinComb P.L (K := Fin 1) (fun _ => (pt a).left) (fun _ => 1)))
    (hfr : ∀ a, IsTorsFrame P rig m (pt a) (fr a)) (a a' a'' : Γ') (z : T.left) (J) (hJ : Good P.L z J) :
    (cubV c z J (pt a) (pt a') (pt a'') * ((val (fr (a + a')) (𝟙 _) z J * val (fr (a + a'')) (𝟙 _) z J *
        val (fr (a' + a'')) (𝟙 _) z J * val (fr 0) (𝟙 _) z J) * (val (fr (a + a' + a'')) (𝟙 _) z J *
          val (fr a) (𝟙 _) z J * val (fr a') (𝟙 _) z J * val (fr a'') (𝟙 _) z J)⁻¹)) ^ (m ^ 2) = 1 := by
  have h0 : pt 0 = 1 := mul_eq_left.1 ((hadd 0 0).symm.trans (by rw [add_zero]))
  obtain ⟨α, hα⟩ := GlobalTheory.EmbLocal.exists_mulPull hG P m T
  have rα := Reg.two (y := z) (J := J) α hα (snd T P.A) (snd T P.A ^ m) rfl rfl
  obtain ⟨p, hp, hp'⟩ : ∃ p : T ⊗ P.A ⟶ P.A, p ^ m = 1 ∧ ∀ w, ptSecT P.A w ≫ p = pt a :=
    ⟨fst T P.A ≫ pt a, by rw [← SymLiftOdd.comp_pow', (hfr a).1, MonObj.comp_one],
      fun w => by rw [ptSecT, lift_fst_assoc, Category.id_comp]⟩
  obtain ⟨q, hq, hq'⟩ : ∃ q : T ⊗ P.A ⟶ P.A, q ^ m = 1 ∧ ∀ w, ptSecT P.A w ≫ q = pt a' :=
    ⟨fst T P.A ≫ pt a', by rw [← SymLiftOdd.comp_pow', (hfr a').1, MonObj.comp_one],
      fun w => by rw [ptSecT, lift_fst_assoc, Category.id_comp]⟩
  have r := (((reg_cub c hJ p q (snd T P.A)).pow hJ (m ^ 2)).mul hJ
    (((((rα.pull hJ (p * q)).mul hJ (rα.pull hJ (p * snd T P.A))).mul hJ (rα.pull hJ (q * snd T P.A))).mul hJ
      (rα.pull hJ 1)).mul hJ ((((rα.pull hJ (p * q * snd T P.A)).mul hJ (rα.pull hJ p)).mul hJ (rα.pull hJ q)).mul hJ
        rα).inv)).const hG P.isAb P.isLB hJ (fun U _ h => by
      simp only [SymLiftOdd.comp_pow', lift_snd, mul_pow, hp, hq, one_pow, _root_.one_mul]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_pow, ofMul_inv, ofMul_zpow, ofMul_one]
      module) (pt a'') 1
  simp only [MonObj.comp_mul, MonObj.comp_one, pt_snd, hp', hq', _root_.mul_one] at r
  rw [(isCub_cubV c hJ).face₃] at r
  have t := fun b => congrArg Additive.ofMul (torsFrame_pow hG P hα (hfr b) hJ)
  have t₁ := t (a + a' + a'')
  have t₂ := t (a + a')
  have t₃ := t (a + a'')
  have t₄ := t (a' + a'')
  have t₅ := t a
  have t₆ := t a'
  have t₇ := t a''
  have t₈ := t 0
  simp only [← hadd] at r
  rw [← h0] at r
  generalize val α (ptSecT P.A 1).left z J = e at t₁ t₂ t₃ t₄ t₅ t₆ t₇ t₈
  apply Additive.ofMul.injective
  replace r := congrArg Additive.ofMul r
  simp only [ofMul_mul, ofMul_pow, ofMul_inv, ofMul_one] at r t₁ t₂ t₃ t₄ t₅ t₆ t₇ t₈ ⊢
  linear_combination (norm := module) r + t₂ + t₃ + t₄ + t₈ - t₁ - t₅ - t₆ - t₇

end Torsion

theorem exists_frame_cube_const : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (Z : Scheme.{0}) (i : F.X ⟶ Z) (X₁ : Setup F W i) (z₁ : X₁.M.Z) (act : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)), ∃ κ : X₁.S.Gam → X₁.S.Gam → X₁.S.Gam → X₁.S.R, (∀ a a' a'', κ a a' a'' ^ ((X₁.S.r * X₁.S.N) ^ 2) = 1) ∧ ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (ev : X₁.M.Z.presheaf.stalk z₁ →+* V) (X : Type) [AddCommGroup X] (m : ℕ) (t : Fin m → V) (δ : Fin m → LinearMap.BilinForm ℤ X) (𝔪 : UMem X₁ z₁ act V ev X t δ), ∀ (x : X₁.S.Gam → (TFK (R := V) (FractionRing V) ⟶ 𝔪.A.A)) (fr : ∀ a, FrAt (x a)), (∀ a, (x a).left ≫ 𝔪.φ = spMap 𝔪.yK ≫ (X₁.ρ.pt a).left) → (∀ a, (fr a).IsGen ∧ ∀ z J J', Good X₁.ρ.P.L z J → Good 𝔪.A.L z J' → Geo.Tor.gw 𝔪.wl (x a).left z (J ((x a).left ≫ 𝔪.φ)) (J' (x a).left) * val (fr a) (𝟙 _) z J' = val (X₁.ρ.fr a) (show (TFK (R := V) (FractionRing V)).left ⟶ (baseOver (Sp X₁.S.R)).left from spMap 𝔪.yK) z J) → ∀ (ρ : LB.Gen (𝔪.A.L.pull (eSec 𝔪.A.A))) (hρ : ρ.IsGen) (c : CubicalStr 𝔪.A.A ⟨𝔪.A.L, ρ, 𝔪.A.isLB, hρ⟩) (a a' a'' : X₁.S.Gam) (z : (TF (R := V) (FractionRing V)).left) (JA : ((TF (R := V) (FractionRing V)).left ⟶ 𝔪.A.A.left) → 𝔪.A.L.ι), Good 𝔪.A.L z JA → (@id ((TF (R := V) (FractionRing V)).left.presheaf.stalk z)ˣ (cubV c (T := TFK (R := V) (FractionRing V)) z JA (x a) (x a') (x a'')) * (@id ((TF (R := V) (FractionRing V)).left.presheaf.stalk z)ˣ (val (fr (a + a')) (𝟙 _) z JA) * @id ((TF (R := V) (FractionRing V)).left.presheaf.stalk z)ˣ (val (fr (a + a'')) (𝟙 _) z JA) * @id ((TF (R := V) (FractionRing V)).left.presheaf.stalk z)ˣ (val (fr (a' + a'')) (𝟙 _) z JA) * @id ((TF (R := V) (FractionRing V)).left.presheaf.stalk z)ˣ (val (fr 0) (𝟙 _) z JA))).val = GlobalTheory.UT.cst (FractionRing V) z (𝔪.yK (κ a a' a'')) * (@id ((TF (R := V) (FractionRing V)).left.presheaf.stalk z)ˣ (val (fr (a + a' + a'')) (𝟙 _) z JA) * @id ((TF (R := V) (FractionRing V)).left.presheaf.stalk z)ˣ (val (fr a) (𝟙 _) z JA) * @id ((TF (R := V) (FractionRing V)).left.presheaf.stalk z)ˣ (val (fr a') (𝟙 _) z JA) * @id ((TF (R := V) (FractionRing V)).left.presheaf.stalk z)ˣ (val (fr a'') (𝟙 _) z JA)).val := by
  intro g n F W Z i X₁ z₁ act
  have := X₁.ar.ded
  have : IsNoetherianRing X₁.S.R := isNoetherianRing_of_fg X₁.S.fg
  have : IsLocallyNoetherian (Sp X₁.S.R) := inferInstanceAs (IsLocallyNoetherian (Spec (CommRingCat.of X₁.S.R)))
  have := X₁.ρ.P.isAb.comm
  obtain ⟨c₀⟩ := (GlobalTheory.firstFiveLaws.1.cube (Sp X₁.S.R) X₁.ρ.P ⟨X₁.ρ.P.L, X₁.ρ.rig, X₁.ρ.P.isLB, X₁.ρ.rig_gen⟩ rfl).1
  choose k hk using exists_cube_const c₀ X₁.ρ.pt X₁.ρ.pt_add X₁.ρ.fr (fun a => (X₁.ρ.fr_tors a).2.1)
  refine ⟨fun a a' a'' => (Scheme.ΓSpecIso (CommRingCat.of X₁.S.R)).hom.hom (k a a' a''), fun a a' a'' => ?_, ?_⟩
  · rw [← map_pow]
    refine Eq.trans (congrArg _ (fn_ext (b := 1) fun y _ => ?_)) (map_one _)
    obtain ⟨J, hJ⟩ := GlobalTheory.ConstFam.exists_good' X₁.ρ.P.isLB y
    have e := hk a a' a'' _ (𝟙 _) y J hJ
    rw [Category.id_comp, Category.id_comp, Category.id_comp] at e
    have e' := congrArg Units.val (cube_torsFrame_pow GlobalTheory.firstFiveLaws.1.globalFns X₁.ρ.P c₀ X₁.ρ.pt X₁.ρ.pt_add
      X₁.ρ.fr X₁.ρ.fr_tors a a' a'' y J hJ)
    have e'' := (congrArg (· ^ ((X₁.S.r * X₁.S.N) ^ 2)) e).symm.trans ((Units.val_pow_eq_pow_val _ _).symm.trans e')
    rw [gs_eq _ y ⊤ trivial, ← map_pow, ← map_pow] at e''
    rw [gs_eq _ y ⊤ trivial, gs_eq _ y ⊤ trivial, map_one, map_one]
    exact e''
  intro V _ _ _ ev X _ m t δ 𝔪 x fr hx hfr ρ hρ c a a' a'' z JA hJA
  have := 𝔪.A.isAb.comm
  obtain ⟨J, hJ⟩ := GlobalTheory.ConstFam.exists_good' X₁.ρ.P.isLB z
  let U : Over.mk ((TFK (R := V) (FractionRing V)).hom ≫ spMap 𝔪.yK) ⟶ baseOver (Sp X₁.S.R) :=
    Over.homMk (spMap 𝔪.yK) (by
      show spMap 𝔪.yK ≫ 𝟙 _ = _
      rw [Category.comp_id]
      change _ = Spec.map (𝟙 _) ≫ _
      rw [Spec.map_id, Category.id_comp])
  have hp : ∀ b, pushHom 𝔪.cart (TFK (R := V) (FractionRing V)) (x b) = U ≫ X₁.ρ.pt b := fun b =>
    Over.OverMorphism.ext (hx b)
  have hadd : ∀ b b', x (b + b') = x b * x b' := fun b b' =>
    GlobalTheory.Poinc.PtAdd.x_add g n F W Z i X₁ z₁ act V ev X m t δ 𝔪 x hx b b' (x b') (hx b')
  have h0 : x 0 = 1 := mul_eq_left.1 ((hadd 0 0).symm.trans (by rw [add_zero]))
  have e₁ := cubV_through GlobalTheory.firstFiveLaws.1.globalFns 𝔪.A.isAb 𝔪.cart c₀ c 𝔪.wl 𝔪.wl_gen
    (T := TFK (R := V) (FractionRing V)) z hJ hJA (x a) (x a') (x a'')
  rw [hp, hp, hp, ← hadd, ← hadd, ← hadd, ← hadd, ← h0] at e₁
  have e₂ := hk a a' a'' _ U z J hJ
  have e₃ : gs U.left z ⊤ (k a a' a'') = GlobalTheory.UT.cst (FractionRing V) z
      (𝔪.yK ((Scheme.ΓSpecIso (CommRingCat.of X₁.S.R)).hom.hom (k a a' a''))) := by
    refine Eq.trans ?_ (Geo.Tor.cst_comp (𝟙 _) 𝔪.yK z _)
    rw [Category.id_comp]
    exact congrArg (gs (spMap 𝔪.yK) z ⊤) ((Scheme.ΓSpecIso (CommRingCat.of X₁.S.R)).hom_inv_id_apply _).symm
  have alg : ∀ {R : Type} [CommRing R] {κ : R} {c c₀ w₁ w₂ w₃ w₄ w₅ w₆ w₇ w₈ f₁ f₂ f₃ f₄ f₅ f₆ f₇ f₈ g₁ g₂ g₃ g₄ g₅ g₆ g₇ g₈ : Rˣ},
      c₀ = w₁ * w₂⁻¹ * w₃⁻¹ * w₄⁻¹ * w₅ * w₆ * w₇ * w₈⁻¹ * c →
      (c₀ * ((g₂ * g₃ * g₄ * g₈) * (g₁ * g₅ * g₆ * g₇)⁻¹)).val = κ →
      w₁ * f₁ = g₁ → w₂ * f₂ = g₂ → w₃ * f₃ = g₃ → w₄ * f₄ = g₄ → w₅ * f₅ = g₅ → w₆ * f₆ = g₆ → w₇ * f₇ = g₇ →
      w₈ * f₈ = g₈ → (c * (f₂ * f₃ * f₄ * f₈)).val = κ * (f₁ * f₅ * f₆ * f₇).val := by
    rintro R _ κ c c₀ w₁ w₂ w₃ w₄ w₅ w₆ w₇ w₈ f₁ f₂ f₃ f₄ f₅ f₆ f₇ f₈ g₁ g₂ g₃ g₄ g₅ g₆ g₇ g₈ rfl rfl rfl rfl rfl rfl
      rfl rfl rfl rfl
    rw [← Units.val_mul]
    refine congrArg Units.val (Additive.ofMul.injective ?_)
    simp only [ofMul_mul, ofMul_inv]
    abel
  exact alg e₁ (e₂.trans e₃) ((hfr _).2 z J JA hJ hJA) ((hfr _).2 z J JA hJ hJA) ((hfr _).2 z J JA hJ hJA)
    ((hfr _).2 z J JA hJ hJA) ((hfr _).2 z J JA hJ hJA) ((hfr _).2 z J JA hJ hJA) ((hfr _).2 z J JA hJ hJA)
    ((hfr _).2 z J JA hJ hJA)

end GlobalTheory.Poinc.CubeConst
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsToricTorsionLabelClosedPoint
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

noncomputable section
namespace GlobalTheory.Poinc.ToricLabel

theorem exists_label : ∀ (o' Ω : Type) [CommRing o'] [Field Ω] [Algebra o' Ω] [ArithBase o' Ω] (S : ThetaSys o' Ω) (ρ : S.Real), S.Big → ∀ (M : RatModel o' Ω) (U₀ : M.Z.Opens) (EE : M.Lat S.J) (FinalForm : ZHOut ρ M U₀ EE), S.admitted M U₀ → S.IsEE M U₀ EE → ∀ x : M.Z, IsClosed ({x} : Set M.Z) → ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (j : M.Z.presheaf.stalk x →+* R), GlobalTheory.Mum.Base R → IsCpl j → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (gm : G.left ⟶ FinalForm.G.left), IsGrpPullback G FinalForm.G (spMap j ≫ M.Z.fromSpecStalk x) gm → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (U : Unif (maximalIdeal R) D A G), LBIso U.LG.L (FinalForm.L.L.pull gm) → (∀ y, PsiUnitOn D.toPre y ((spMap j ≫ M.Z.fromSpecStalk x) ⁻¹' abLocus FinalForm.G)) → ∀ lam : D.toPre.X →+ ZMod (S.r * S.N), ∃ b : S.Gam, ∀ (p : ℕ) [Fact p.Prime] (y : Sp (OO p) ⟶ M.Z) (ev : R →+* OO p), M.Cen U₀ x y → spMap ev ≫ (spMap j ≫ M.Z.fromSpecStalk x) = y → ∀ y₀ : S.R →+* PadicAlgCl p, S.At M y y₀ → ∀ (u : ρ.UTest p y₀) (ε : D.toPre.X ≃+ u.D.toPre.X), GlobalTheory.Poinc.TestAtPt.IsBC FinalForm gm U ev u ε → ∀ (τ' : Multiplicative u.D.toPre.X →* (PadicAlgCl p)ˣ), (∀ χ, ((τ' (Multiplicative.ofAdd (ε χ)) : (PadicAlgCl p)ˣ) : PadicAlgCl p) = y₀ (algebraMap o' S.R S.ζ) ^ (S.r * S.N * (lam χ).val)) → ∀ (q : QkPt u.D.toPre (PadicAlgCl p) (S.r * S.N)) (x' : TFK (R := u.V) (PadicAlgCl p) ⟶ u.A.A), q.y = 0 → GlobalTheory.UT.IsTor τ' q.g → QkToAkU u.U.toUnifPre (PadicAlgCl p) (S.r * S.N) q x' → x'.left ≫ u.φ = spMap y₀ ≫ (ρ.pt b).left := by
  intro o' Ω _ _ _ _ S ρ hBig M U₀ EE FinalForm hAdm hEE x hx R _ _ _ j hBase hCpl G _ _ gm hpb D A U hLB hPsi lam
  have hj : IsLocalHom j := GlobalTheory.UPoinc.ClosedPt.isLocalHom_of_isCpl hCpl
  have hk0 : S.r * S.N ≠ 0 := Nat.mul_ne_zero (by have := S.r_pos; omega) (by have := S.N_ge; omega)
  haveI : NeZero (S.r * S.N) := ⟨hk0⟩
  set ζR : R := j ((M.stalkEquiv x).symm (algebraMap o' (M.O x) S.ζ)) with hζR
  have hζpow : ζR ^ ((S.r * S.N) ^ 2) = 1 := by
    rw [hζR, ← map_pow, ← map_pow, ← map_pow, S.prim.pow_eq_one, map_one, map_one, map_one]
  let u0 : Rˣ := Units.ofPowEqOne ζR ((S.r * S.N) ^ 2) hζpow (pow_ne_zero 2 hk0)
  have hu0 : ((u0 : Rˣ) : R) = ζR := Units.val_ofPowEqOne _ _ _ _
  let w : Rˣ := u0 ^ (S.r * S.N)
  have hw : w ^ (S.r * S.N) = 1 := by
    rw [← pow_mul, ← sq]; ext; rw [Units.val_pow_eq_pow_val, hu0, hζpow, Units.val_one]
  let τ : Multiplicative D.toPre.X →* Rˣ :=
    { toFun := fun χ => w ^ (lam (Multiplicative.toAdd χ)).val
      map_one' := by simp
      map_mul' := fun a b => by
        rw [toAdd_mul, map_add, ZMod.val_add, ← pow_eq_pow_mod _ hw, pow_add] }
  have hτ : τ ^ (S.r * S.N) = 1 := by
    refine MonoidHom.ext fun χ => ?_
    rw [MonoidHom.pow_apply, MonoidHom.one_apply]
    show (w ^ (lam (Multiplicative.toAdd χ)).val) ^ (S.r * S.N) = 1
    rw [← pow_mul, mul_comm, pow_mul, hw, one_pow]
  have hsemi : IsSemiAbelian G := by
    obtain ⟨e, he, -⟩ := grpPullback_iso hpb (isGrpPullback_pullback FinalForm.G _)
    haveI := he
    exact GlobalTheory.isSemiAbelian_of_grpIso e (IsSemiAbelian.pullback _ FinalForm.G FinalForm.semi)
  obtain ⟨s, hs, hspec⟩ := GlobalTheory.ToricTorsionSpec.main R hBase G hsemi D A U (S.r * S.N) (Nat.one_le_iff_ne_zero.2 hk0) τ hτ
  obtain ⟨b, hb⟩ := GlobalTheory.Poinc.LabIndex.torsion_section_label o' Ω S ρ hBig M U₀ EE FinalForm hAdm hEE x hx R j hBase hCpl G gm hpb D A U hLB hPsi s hs
  refine ⟨b, ?_⟩
  intro p _ y ev hCen hy y₀ hAt u ε hBC τ' hτ' q x' hq hTor hQk
  obtain ⟨ev₀, hloc, hD, bc, hmon, hpull, hxe, hev, t, ht1, ht2⟩ := hBC
  haveI : CharZero u.V :=
    RingHom.charZero ((algebraMap (FractionRing u.V) (PadicAlgCl p)).comp (algebraMap u.V (FractionRing u.V)))
  have hring : (algebraMap (FractionRing u.V) (PadicAlgCl p)).comp ((algebraMap u.V (FractionRing u.V)).comp ev₀) =
      (OO p).subtype.comp ev := RingHom.ext hev
  have hζ : ((ev ζR : OO p) : PadicAlgCl p) = y₀ (algebraMap o' S.R S.ζ) := by
    rw [hζR, GlobalTheory.Poinc.TestAtPt.val_gPt_of_stalk o' Ω M x R j hj p y ev hy, hAt]
    rfl
  have hchar : ∀ χ', ((τ' χ' : (PadicAlgCl p)ˣ) : PadicAlgCl p) = algebraMap (FractionRing u.V) (PadicAlgCl p)
      (algebraMap u.V (FractionRing u.V) (ev₀ ((τ (Multiplicative.ofAdd (hD.xe (Multiplicative.toAdd χ'))) : Rˣ) : R))) := by
    intro χ'
    obtain ⟨χ, hχ⟩ := ε.surjective (Multiplicative.toAdd χ')
    have e1 : χ' = Multiplicative.ofAdd (ε χ) := by rw [hχ]; rfl
    subst e1
    rw [hτ' χ, hev]
    simp only [toAdd_ofAdd, hxe]
    show _ = ((ev (((w ^ (lam χ).val : Rˣ) : R)) : OO p) : PadicAlgCl p)
    rw [Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val, hu0, map_pow, map_pow, SubmonoidClass.coe_pow,
      SubmonoidClass.coe_pow, hζ, ← pow_mul]
  have key := hspec u.V u.complete ev₀ hloc u.G bc hmon u.D u.A hD u.U hpull (PadicAlgCl p) τ' hchar q x' hq hTor hQk
  have h2 := hb p y ev hCen hy y₀ hAt (x'.left ≫ t) (by
    rw [Category.assoc, ht2, ← hring]
    simpa only [Category.assoc] using congrArg (· ≫ gm) key)
  rw [Category.assoc, ht1] at h2
  exact h2

end GlobalTheory.Poinc.ToricLabel
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsToricTorsionPointOfLatticeCharacter
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.Poinc.Eq8 GlobalTheory.Poinc.Sep.Spz Classical

namespace GlobalTheory.Poinc.Sep.Spz

theorem exists_torAt : ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], GlobalTheory.Mum.Base V → ∀ (G : Over (Sp V)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (D : DegData V (maximalIdeal V)) (A : PolAV (Sp (FractionRing V))) (U : Unif (maximalIdeal V) D A G) (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing V) F] (k : ℕ) (z : F), 1 ≤ k → z ^ k = 1 → ∀ c : D.toPre.X →+ ℤ, ∃ x : TFK (R := V) F ⟶ A.A, TorAt U F k z c x := by
  intro V _ _ _ hB G _ _ hG D A U F _ _ _ k z hk hz c
  obtain ⟨hAdm, hChar⟩ := hB
  haveI := hChar
  have hz0 : z ≠ 0 := by
    rintro rfl
    rw [zero_pow (by omega)] at hz
    exact zero_ne_one hz
  let u : Fˣ := Units.mk0 z hz0
  let τ : Multiplicative D.toPre.X →* Fˣ :=
    (zpowersHom Fˣ u).comp (AddMonoidHom.toMultiplicative c)
  have hu : u ^ k = 1 := by
    ext; simp [u, hz]
  have hτ : τ ^ k = 1 := by
    refine MonoidHom.ext fun χ => ?_
    rw [MonoidHom.pow_apply, MonoidHom.one_apply]
    simp only [τ, MonoidHom.comp_apply, zpowersHom_apply]
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hu, one_zpow]
  obtain ⟨q, hy, hq⟩ := GlobalTheory.ZH.TorusPerp.exists_qkPt_tor (F := F) D.tau_bimult τ hτ
  obtain ⟨f, hf⟩ := GlobalTheory.TorsionIso.torsion_eq GlobalTheory.firstFiveLaws V (maximalIdeal V) hAdm D A G hG U F k hk
  refine ⟨f q, τ, q, fun χ => ?_, hy, hq, (hf.1 q (f q)).2 rfl⟩
  simp [τ, u]

end GlobalTheory.Poinc.Sep.Spz
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTorsionLabelsGenericFibreTraitStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_torsionLabels_genericFibre_trait : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (C : LabCover D) (j : ℕ) (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W] (T : Trait C W) (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] [Algebra (FractionRing W) F] (em : Kb R →ₐ[FractionRing R] F), (∀ r, algebraMap (FractionRing R) F (algebraMap R _ r) = algebraMap (FractionRing W) F (algebraMap W _ (T.φ r))) → ∀ f : (TFK (R := W) F ⊗ T.A.A).left ⟶ (TFK (R := R) F ⊗ C.A.A).left, IsIso f → f ≫ (fst (TFK (R := R) F) C.A.A).left = (fst (TFK (R := W) F) T.A.A).left → f ≫ (snd (TFK (R := R) F) C.A.A).left ≫ C.α = (snd (TFK (R := W) F) T.A.A).left ≫ T.U.gen.inv.left ≫ pullback.fst T.G.hom (jK W) ≫ T.β → ∃ lab' : QkPt T.D'.toPre F (C.n ^ j) → (TFK (R := W) F ⟶ T.A.A), (∀ p', QkToAkU T.U.toUnifPre F (C.n ^ j) p' (lab' p')) ∧ ∀ (p : QkPt D.toPre (Kb R) (C.n ^ j)) (p₁ : QkPt D.toPre F (C.n ^ j)) (p' : QkPt T.D'.toPre F (C.n ^ j)), QkExt em.toRingHom p p₁ → p'.y = T.hD.xe.symm p₁.y → IsPullGtF T.φ T.hD F p₁.g p'.g → (lab' p').left ≫ T.U.gen.inv.left ≫ pullback.fst T.G.hom (jK W) ≫ T.β = spMap em.toRingHom ≫ (C.lab j p).left ≫ C.α := by
  first | exact @GlobalTheory.Mum.Trait.exists_lab_pull | exact GlobalTheory.Mum.Trait.exists_lab_pull | (intros; apply GlobalTheory.Mum.Trait.exists_lab_pull <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTorsionPointFromFractionAlgClosureStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum GlobalTheory.Mum.UpExt GlobalTheory.FieldBaseChange ReciprocityTheory.ChartRestriction.G.DVR
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_torsion_point_from_fractionAlgClosure : ∀ (R : Type) [CommRing R] [IsDomain R] (A : PolAV (Sp (FractionRing R))) (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] (em : Kb R →ₐ[FractionRing R] F) (N : ℕ), 1 ≤ N → ∀ x : TFK (R := R) F ⟶ A.A, x ^ N = 1 → ∃ y : TFK (R := R) (Kb R) ⟶ A.A, y ^ N = 1 ∧ x.left = spMap em.toRingHom ≫ y.left := by
  first | exact @GlobalTheory.Mum.UpExt.torsion_from_closure | exact GlobalTheory.Mum.UpExt.torsion_from_closure | (intros; apply GlobalTheory.Mum.UpExt.torsion_from_closure <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTorsionTranslateLabelThetaConstantDividesAStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_torsionTranslate_label_thetaConstant_divides_all : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (Z : Scheme.{0}) (i : F.X ⟶ Z) (X₁ : Setup F W i) (z₁ : X₁.M.Z) (act : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)) (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (ev : X₁.M.Z.presheaf.stalk z₁ →+* V) (X : Type) [AddCommGroup X] (m : ℕ) (t : Fin m → V) (δ : Fin m → LinearMap.BilinForm ℤ X) (𝔪 : UMem X₁ z₁ act V ev X t δ) (x₀ : X₁.S.Gam), X₁.M.Div X₁.S.th x₀ z₁ → ∀ a, 𝔪.YY a 0 → ∃ b : X₁.S.Gam, X₁.ρ.n • b = 0 ∧ a + b ∈ X₁.S.supI X₁.M z₁ := by
  first | exact @GlobalTheory.Poinc.Sep.TorTrans.exists_translate_mem_supI | exact GlobalTheory.Poinc.Sep.TorTrans.exists_translate_mem_supI | (intros; apply GlobalTheory.Poinc.Sep.TorTrans.exists_translate_mem_supI <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTorsionTranslateThetaSectionUnitStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_torsionTranslate_thetaSection_unit : ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (D : DegPre V) (θ : D.SecB 1 0), IntTerm.IsTheta D θ → ∀ N : ℕ, 2 ≤ N → IsUnit (N : V) → ∀ (C : Type) (b : C → (𝟙_ (Over (Sp V)) ⟶ D.P.A)), IntTerm.Exhausts D.P N b → ∀ a : 𝟙_ (Over (Sp V)) ⟶ D.P.A, ∃ c, IntTerm.UnitAt D θ (a * b c) := by
  first | exact @GlobalTheory.Poinc.IntTerm.exists_unitAt_mul | exact GlobalTheory.Poinc.IntTerm.exists_unitAt_mul | (intros; apply GlobalTheory.Poinc.IntTerm.exists_unitAt_mul <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTorusPairOfTorsionPointOver
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.Poinc.Sep

open GlobalTheory.Poinc.Tors

noncomputable section

namespace GlobalTheory.Poinc.Sep.LiesPair

theorem exists_pair_of_liesOver : ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], IsCN V → ∀ (D : DegData V (maximalIdeal V)) (A : PolAV (Sp (FractionRing V))) (G : Over (Sp V)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (U : Unif (maximalIdeal V) D A G) (w₀ : W0 U.toUnifPre), w₀.IsGen → ∀ N : ℕ, 1 ≤ N → ∀ (g : GtPtF D.toPre (FractionRing V)) (w : Frm D.toPre (FractionRing V) 1 g.b) (x : TFK (R := V) (FractionRing V) ⟶ A.A) (fr : FrAt x), (∃ o, GtPtF.IsNsmul N g o ∧ o.IsZero) → w.IsGen → fr.IsGen → LiesOver U.toUnifPre w₀ g w x fr → ∃ p : QkPt D.toPre (FractionRing V) N, p.y = 0 ∧ p.g = g ∧ QkToAkU U.toUnifPre (FractionRing V) N p x := by
  intro V _ _ _ hCN D A G _ _ hG U w₀ hw₀ N hN g w x fr hg hw hfr hov
  haveI : CharZero V := hCN.2.2.2
  have hL : GlobalTheory.UT.LL := GlobalTheory.firstFiveLaws
  have hA : AdmBase V (maximalIdeal V) := ⟨hCN.1, inferInstance, hCN.2.1, hCN.2.2.1⟩
  have hB := D.tau_bimult
  obtain ⟨o, ho₁, ho₂⟩ := hg
  letI := GlobalTheory.TorusExt.gtGroup D.toPre (FractionRing V)
  have hkg : N • g = GlobalTheory.TorusExt.iota hB (FractionRing V) 0 := by
    rw [map_zero]
    exact ((GlobalTheory.TorusExt.isNsmul_iff_eq _ _ _).1 ho₁).symm.trans ((GlobalTheory.TorusExt.isZero_iff_eq _).1 ho₂)
  let p := GlobalTheory.TorusExt.qkMk hB 0 g hkg
  have hf : (algebraMap (FractionRing V) (AlgebraicClosure (FractionRing V))).comp
      (algebraMap (FractionRing V) (FractionRing V)) = algebraMap _ _ := RingHom.comp_id _
  let pb := GlobalTheory.TorusExt.qkExt hB _ hf p
  have hp := (GlobalTheory.TorusExt.qkExt_iff hB _ hf p _).2 rfl
  let xb : TFK (R := V) (AlgebraicClosure (FractionRing V)) ⟶ A.A :=
    GlobalTheory.TorsionExt.fieldMap (FractionRing V) (AlgebraicClosure (FractionRing V)) ≫ x
  obtain ⟨wb, frb, hwb, hfrb, hlb⟩ := GlobalTheory.T.torusExtension_point_liesOver_after_field_extension V _ hA D A G hG U (AlgebraicClosure (FractionRing V)) w₀
    hw₀ g w x fr hw hfr hov xb rfl
  obtain ⟨f', f₁, -⟩ := GlobalTheory.TorsionIso.torsion_eq hL V _ hA D A G hG U (AlgebraicClosure (FractionRing V)) N hN
  have hq := (f₁ pb (f' pb)).2 rfl
  obtain ⟨w', fr', hw', hfr', hl'⟩ := GlobalTheory.Poinc.Tors.ValPair.liesOver_of_qkToAkU V _ hA D A G hG U
    (AlgebraicClosure (FractionRing V)) w₀ hw₀ _ hN pb (f' pb) rfl hq
  have e := GlobalTheory.Poinc.Tors.OneOver.eq_of_liesOver hL V _ hA D A G hG U (AlgebraicClosure (FractionRing V)) w₀ hw₀
    pb.g wb w' xb (f' pb) frb fr' hwb hw' hfrb hfr' hlb hl'
  refine ⟨p, rfl, rfl, ?_⟩
  refine (GlobalTheory.TorsionExt.qkToAkU_iff_of_algebra hL.1.globalFns hL.1.kerPow U hN hp x).2 ?_
  rw [← e] at hq
  exact hq

end GlobalTheory.Poinc.Sep.LiesPair
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTraitLiftSemiabelianExtensionModelStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_trait_lift_semiabelianExtensionModel : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (Z : Scheme.{0}) (i : F.X ⟶ Z) (X₁ : Setup F W i) (z₁ : X₁.M.Z) (Y : RatModel X₁.o₁ X₁.Ω₁) (πY : Y.Z ⟶ X₁.M.Z), Cmp.ZHAbove X₁ Y πY → ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] [IsDiscreteValuationRing V] (ev : X₁.M.Z.presheaf.stalk z₁ →+* V), IsLocalHom ev → IsCN V → ∃ (V' : Type) (_ : CommRing V') (_ : IsDomain V') (_ : IsLocalRing V') (_ : IsDiscreteValuationRing V') (j : V →+* V') (ξ : Sp V' ⟶ Y.Z), IsCN V' ∧ Function.Injective j ∧ IsLocalHom j ∧ ξ ≫ πY = spMap (j.comp ev) ≫ X₁.M.Z.fromSpecStalk z₁ := by
  first | exact @GlobalTheory.Poinc.Sep.TraitLift.exists_lift | exact GlobalTheory.Poinc.Sep.TraitLift.exists_lift | (intros; apply GlobalTheory.Poinc.Sep.TraitLift.exists_lift <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueLinearLiftOfAbelianEndomorphismStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PELU
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.existsUnique_linear_lift_of_abelianEndomorphism : ∀ (X : Scheme.{0}) (G : Over X) [GrpObj G] [IsCommMonObj G] (g : ℕ), IsAbelianScheme G → SmoothOfRelativeDimension g G.hom → ∀ (y : Sp ℂ ⟶ X) (e e' : (Fin g → ℂ) → (Over.mk y ⟶ G)) (α : G ⟶ G), IsExp y e → IsExp y e' → IsMonHom α → ∃! M : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ), ∀ z, e' (M z) = e z ≫ α := by
  first | exact @GlobalTheory.ExpLin.existsUnique_linear_lift | exact GlobalTheory.ExpLin.existsUnique_linear_lift | (intros; apply GlobalTheory.ExpLin.existsUnique_linear_lift <;> assumption)
end

