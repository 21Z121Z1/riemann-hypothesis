import Mathlib
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.BasisPowerSectionsLocalBaseChange
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsKoszulTorsionTransversalSplitZeros
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0046
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0001
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.BijectiveRestrictPointsOfEtaleOfHenselian
import Development.AbelianVarietyTheory.Definitions.KeyFormula.Bundle0001
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.IsPluriharmonicSiegel
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0004
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.SymplecticCharacters.OneEqSpTranslZero
import Development.AbelianVarietyTheory.Definitions.KeyFormula.GeomIntSelf
import Development.AbelianVarietyTheory.Statements.FundamentalDomains.AtOfNumberField
import Development.AbelianVarietyTheory.Statements.ThetaLevelCharacters.MemThetaLevelCharDimZero
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0110
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0114
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0173
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0165
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0171
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0120
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaCore
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.Bundle0004
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0123

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsInvariantOfSplitZerosTorsion
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory.KeyKa

noncomputable section

namespace GlobalTheory

theorem exists_ker_int_matrix_four_of_torsion_lift {G G' : Type} [CommGroup G] [CommGroup G']
    (φ : G →* G') (N g m : ℕ) (hN : 1 ≤ N) (hm : m ∣ N) (ξ : Fin (N ^ (2 * g)) → G)
    (hξ : ∀ a, ξ a ^ N = 1) (hinj : Function.Injective fun a => φ (ξ a))
    (hker : ∀ u : G, u ^ N = 1 → φ u = 1 → u = 1)
    (hG : ∀ k : ℕ, k ∣ N → Nat.card {x : G' // x ^ k = 1} = k ^ (2 * g))
    (al : Matrix (Fin 4) (Fin 4) ℤ)
    (hal : al.transpose * al = (m : ℤ) • (1 : Matrix (Fin 4) (Fin 4) ℤ)) :
    ∃ a : (Fin 4 → Fin (m ^ g)) → Fin 4 → Fin (N ^ (2 * g)), Function.Injective a ∧
      ∀ I c, ∏ r, ξ (a I r) ^ al r c = 1 := by
  classical
  have hm1 : 1 ≤ m := Nat.pos_of_dvd_of_pos hm hN
  have hdet0 : al.det ≠ 0 := by
    intro h0
    have h1 := congrArg Matrix.det hal
    rw [Matrix.det_mul, h0, mul_zero, Matrix.det_smul, Matrix.det_one, _root_.mul_one] at h1
    exact pow_ne_zero _ (by exact_mod_cast (by omega : m ≠ 0)) h1.symm
  have hal' : al * al.transpose = (m : ℤ) • (1 : Matrix (Fin 4) (Fin 4) ℤ) := by
    have hreg := Matrix.isRegular_of_isLeftRegular_det (A := al)
      (IsRegular.of_ne_zero hdet0).left
    apply hreg.right
    simp only [Matrix.mul_assoc, hal]
    rw [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, Matrix.one_mul]
  let ψ : Fin (N ^ (2 * g)) → {x : G' // x ^ N = 1} := fun a =>
    ⟨φ (ξ a), by rw [← map_pow, hξ, map_one]⟩
  have hfin : Finite {x : G' // x ^ N = 1} :=
    Nat.finite_of_card_ne_zero (by rw [hG N dvd_rfl]; positivity)
  have hψ : Function.Bijective ψ :=
    Function.Injective.bijective_of_nat_card_le (fun a a' h => hinj (congrArg Subtype.val h))
      (by rw [hG N dvd_rfl, Nat.card_fin])
  have hc := card_ker_int_matrix_four G' m (2 * g) al hm1 hal fun k hk => hG k (hk.trans hm)
  have hfin2 : Finite {ζ : Fin 4 → G' // ∀ c, ∏ r', ζ r' ^ al r' c = 1} :=
    Nat.finite_of_card_ne_zero (by rw [hc]; positivity)
  obtain ⟨e⟩ : Nonempty ((Fin 4 → Fin (m ^ g)) ≃ {ζ : Fin 4 → G' // ∀ c, ∏ r', ζ r' ^ al r' c = 1}) := by
    rw [← Finite.card_eq, hc, Nat.card_pi]
    simp only [Nat.card_fin, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    ring
  have htor : ∀ I r, (e I).1 r ^ N = 1 := by
    intro I r
    have h1 : ∏ c, (∏ r', (e I).1 r' ^ al r' c) ^ al r c = 1 := by
      simp only [(e I).2, one_zpow, Finset.prod_const_one]
    simp only [← Finset.prod_zpow, ← zpow_mul] at h1
    rw [Finset.prod_comm] at h1
    have h2 : ∀ r', ∏ c, (e I).1 r' ^ (al r' c * al r c) = if r' = r then (e I).1 r' ^ m else 1 := by
      intro r'
      have h3 := congrFun (congrFun hal' r') r
      simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.smul_apply, Matrix.one_apply,
        smul_eq_mul] at h3
      have h4 : ∏ c, (e I).1 r' ^ (al r' c * al r c) = (e I).1 r' ^ (∑ c, al r' c * al r c) := by
        simp only [Fin.prod_univ_four, Fin.sum_univ_four, zpow_add]
      rw [h4, h3]
      split_ifs <;> simp
    simp only [h2, Finset.prod_ite_eq', Finset.mem_univ, if_true] at h1
    obtain ⟨q, rfl⟩ := hm
    rw [pow_mul, h1, one_pow]
  choose a ha using fun I r => hψ.2 ⟨(e I).1 r, htor I r⟩
  have ha' : ∀ I r, φ (ξ (a I r)) = (e I).1 r := fun I r => congrArg Subtype.val (ha I r)
  refine ⟨a, fun I I' h => e.injective (Subtype.ext (funext fun r => ?_)), fun I c => hker _ ?_ ?_⟩
  · rw [← ha', ← ha', h]
  · rw [← Finset.prod_pow]
    refine Finset.prod_eq_one fun r _ => ?_
    rw [← zpow_natCast, ← zpow_mul, _root_.mul_comm, zpow_mul, zpow_natCast, hξ, one_zpow]
  · simp only [map_prod, map_zpow, ha', (e I).2]

theorem exists_split_ker_of_split_torsion (laws : Out.Laws) (R : Type) [CommRing R] [IsDomain R]
    [IsLocalRing R] [IsNoetherianRing R] (P : Out.PolAV (Sp R)) (N m : ℕ) (hN : IsUnit (N : R)) (hm : m ∣ N)
    (ξ : Fin (N ^ (2 * P.g)) → (𝟙_ (Over (Sp R)) ⟶ P.A)) (hξ : ∀ a, ξ a ^ N = 1)
    (hd : ∀ a a', a ≠ a' → ∀ p : Sp R, (ξ a).left p ≠ (ξ a').left p)
    (al : Matrix (Fin 4) (Fin 4) ℤ)
    (hal : al.transpose * al = (m : ℤ) • (1 : Matrix (Fin 4) (Fin 4) ℤ)) :
    ∃ ζ : (Fin 4 → Fin (m ^ P.g)) → Fin 4 → (𝟙_ (Over (Sp R)) ⟶ P.A),
      (∀ I I', I ≠ I' → ∀ p : Sp R, ∃ r, (ζ I r).left p ≠ (ζ I' r).left p) ∧
      (∀ I c, (List.ofFn fun r : Fin 4 => ζ I r ^ al r c).prod = 1) := by
  haveI : IsCommMonObj P.A := P.isAb.comm
  let k := AlgebraicClosure (IsLocalRing.ResidueField R)
  let f : R →+* k := (algebraMap (IsLocalRing.ResidueField R) k).comp (IsLocalRing.residue R)
  let t : Sp k ⟶ Sp R := Spec.map (CommRingCat.ofHom f)
  have hN1 : 1 ≤ N := Nat.pos_of_ne_zero (by rintro rfl; simp at hN)
  have hNk : (N : k) ≠ 0 := by simpa using (hN.map f).ne_zero
  letI : CommGroup (𝟙_ (Over (Sp R)) ⟶ P.A) := Hom.commGroup
  letI : CommGroup (Over.mk t ⟶ P.A) := Hom.commGroup
  let φ : (𝟙_ (Over (Sp R)) ⟶ P.A) →* (Over.mk t ⟶ P.A) :=
    MonoidHom.mk' (fun u => toUnit (Over.mk t) ≫ u) fun u v => MonObj.comp_mul _ _ _
  have hφ : ∀ u, (φ u).left = (toUnit (Over.mk t)).left ≫ u.left := fun u => rfl
  obtain ⟨p₀⟩ : Nonempty (Sp k) := inferInstance
  obtain ⟨hf, -, -, het, -⟩ := laws.mulN (Sp R) P N hN1
  have het' := het (by simpa using hN.map (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom)
  have hmul : ∀ {Z : Over (Sp R)} (y : Z ⟶ P.A), y ≫ Out.mulA P.A N = y ^ N :=
    fun y => by rw [Out.mulA, MonObj.comp_pow, Category.comp_id]
  obtain ⟨a, ha, ha'⟩ := exists_ker_int_matrix_four_of_torsion_lift φ N P.g m hN1 hm ξ hξ
    (fun a a' h => by
      by_contra hne
      apply hd a a' hne ((toUnit (Over.mk t)).left p₀)
      have h1 : (φ (ξ a)).left p₀ = (φ (ξ a')).left p₀ := congrArg (fun q : Over.mk t ⟶ P.A => q.left p₀) h
      simpa only [hφ, Scheme.Hom.comp_apply] using h1)
    (fun u hu h1 => by
      haveI : PreconnectedSpace (𝟙_ (Over (Sp R))).left :=
        inferInstanceAs (PreconnectedSpace (PrimeSpectrum R))
      haveI : Nonempty (Over.mk t).left := ⟨p₀⟩
      apply Over.OverMorphism.ext
      refine eq_of_preconnected_of_unramified (Out.mulA P.A N).left ?_ (toUnit (Over.mk t)).left ?_
      · rw [← Over.comp_left, ← Over.comp_left, hmul, hmul, hu, one_pow]
      · rw [← hφ, ← hφ, h1, map_one])
    (fun j hj => (laws.mulN (Sp R) P j (Nat.pos_of_dvd_of_pos hj hN1)).2.2.2.2 k t (by
      obtain ⟨q, rfl⟩ := hj
      rw [Nat.cast_mul] at hNk
      exact left_ne_zero_of_mul hNk)) al hal
  refine ⟨fun I r => ξ (a I r), fun I I' hI p => ?_, fun I c => ?_⟩
  · obtain ⟨r, hr⟩ := Function.ne_iff.1 (ha.ne hI)
    exact ⟨r, hd _ _ hr p⟩
  · rw [List.prod_ofFn]
    exact ha' I c

theorem exists_kaVal_of_split :
    Out.Laws → ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsPrincipalIdealRing R] (x : KeyIn R) (n l l' : ℕ) (al : ℕ → Matrix (Fin 4) (Fin 4) ℤ) (d : ℕ) (s : Fin x.P.g → RR x n) (z : Fin d → Pt x) (ch : Fin d → x.P.L.ι) (ξ : Fin (degProd x.P.g n l l' ^ (2 * x.P.g)) → Pt x), admitted x.P.g n l l' al → IsUnit ((degProd x.P.g n l l' : ℕ) : R) → EtZ x s z ch → (∀ a, ξ a ^ degProd x.P.g n l l' = 1) → (∀ a a', a ≠ a' → ∀ p : Sp R, (ξ a).left p ≠ (ξ a').left p) → ∃ κ, KaVal x n l l' al s κ := by
  intro laws R _ _ _ _ x n l l' al d s z ch ξ ⟨hn, hl, hl', hal⟩ hu hz hξ hd
  have key : ∀ L : ℕ, x.P.g * n < L → (∀ j ≤ x.P.g, L - j * n ∣ degProd x.P.g n l l') →
      ∃ (b : ∀ j, Fin ((L - j * n) ^ x.P.g) → RR x (L - j * n)) (lam : ℕ → Rˣ),
        ∀ j ≤ x.P.g, IsBasis x (b j) ∧ IsSquareDeterminantComparison x (L - j * n) (al (L - j * n)) (b j) (lam j) := by
    intro L hL hdv
    have h1 : ∀ j, ∃ (b : Fin ((L - j * n) ^ x.P.g) → RR x (L - j * n)) (lam : Rˣ),
        j ≤ x.P.g → IsBasis x b ∧ IsSquareDeterminantComparison x (L - j * n) (al (L - j * n)) b lam := by
      intro j
      by_cases hj : j ≤ x.P.g
      · have h2 : j * n ≤ x.P.g * n := Nat.mul_le_mul_right n hj
        obtain ⟨b, hb⟩ := (GlobalTheory.KeyBasis.main laws R x (L - j * n) (by omega)).1
        obtain ⟨ζ, h3, h4⟩ := exists_split_ker_of_split_torsion laws R x.P _ _ hu (hdv j hj) ξ hξ hd
          _ (hal (L - j * n))
        obtain ⟨lam, h5⟩ := GlobalTheory.T.exists_l2Val_field_or_dvr_split_kernel laws R x _ _ b ζ
          (isUnit_of_dvd_unit (Nat.cast_dvd_cast (hdv j hj)) hu) (hal _) hb h3 h4
        exact ⟨b, lam, fun _ => ⟨hb, h5⟩⟩
      · exact ⟨fun _ => ⟨fun _ => 0, fun _ _ => by rw [map_zero, map_zero, mul_zero]⟩, 1,
          fun h => absurd h hj⟩
    choose b lam h using h1
    exact ⟨b, lam, h⟩
  have hdv : ∀ j ≤ x.P.g, (l - j * n) * (l' - j * n) ∣ degProd x.P.g n l l' := fun j hj =>
    Finset.dvd_prod_of_mem (fun j => (l - j * n) * (l' - j * n))
      (Finset.mem_range.2 (Nat.lt_succ_of_le hj))
  obtain ⟨b, lam, hb⟩ := key l hl fun j hj => (dvd_mul_right _ _).trans (hdv j hj)
  obtain ⟨b', lam', hb'⟩ := key l' (hl.trans hl') fun j hj => (dvd_mul_left _ _).trans (hdv j hj)
  obtain ⟨rfl, t, ht⟩ := GlobalTheory.KeyKa.KoszulEx.exists_kosVal laws R x n l d s b z ch (by omega) hl (fun j hj => (hb j hj).1) hz
  obtain ⟨-, t', ht'⟩ := GlobalTheory.KeyKa.KoszulEx.exists_kosVal laws R x n l' _ s b' z ch (by omega) (hl.trans hl')
    (fun j hj => (hb' j hj).1) hz
  have hJ : IsUnit (∏ a, jac x s (z a) (ch a)) := IsUnit.prod_univ_iff.2 hz.2.2.1
  exact ⟨_, z, ch, b, b', t, t', hJ.unit, lam, lam', hz, hJ.unit_spec, hb, hb', ht, ht', rfl⟩

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsKoszulTorsionTransversalSplitZerosStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory.KeyKa

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_koszulTorsion_transversal_split_zeros : Out.Laws → ∀ (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] (x : KeyIn R) (n l d : ℕ) (s : Fin x.P.g → RR x n) (b : ∀ j, Fin ((l - j * n) ^ x.P.g) → RR x (l - j * n)) (z : Fin d → Pt x) (ch : Fin d → x.P.L.ι), 1 ≤ n → x.P.g * n < l → (∀ j ≤ x.P.g, IsBasis x (b j)) → EtZ x s z ch → d = x.P.g.factorial * n ^ x.P.g ∧ ∃ t : Rˣ, KosVal x l s z ch b t := by
  first | exact @GlobalTheory.KeyKa.KoszulEx.exists_kosVal | exact GlobalTheory.KeyKa.KoszulEx.exists_kosVal | (intros; apply GlobalTheory.KeyKa.KoszulEx.exists_kosVal <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.LamIsoOfDoublingPullbackEqDiagonalSq
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.KeyPow GlobalTheory.KeyFam GlobalTheory.ZM GlobalTheory.AbLaw

noncomputable section

namespace GlobalTheory.LamOfDouble

open GlobalTheory.CechPic

theorem isIso_of_factor {X Y Z : Scheme.{0}} (y : X ⟶ Z) (j : Z ⟶ Y) [Mono j] [Flat (y ≫ j)]
    [Surjective (y ≫ j)] [QuasiCompact (y ≫ j)] : IsIso j := by
  have : IsRegularEpi (y ≫ j) := inferInstance
  have : StrongEpi (y ≫ j) := inferInstance
  have : StrongEpi j := strongEpi_of_strongEpi y j
  exact isIso_of_mono_of_strongEpi j

theorem triv_of_pull_pow (hL : Out.Laws) {R : Type} [CommRing R] (A : Over (Sp R)) [GrpObj A] [IsCommMonObj A]
    (hA : IsAbelianScheme A) (M : LB A.left) (hM : M.IsLB) (ha : Out.RelAmple A M) (n : ℕ) (hn : 1 ≤ n)
    (N : LB (A ⊗ A).left) (hN : N.IsLB)
    (h0 : ∃ t : (N.pull (lift (𝟙 A) (1 : A ⟶ A)).left).Gen, t.IsGen)
    (h1 : ∃ t : (N.pull (((𝟙 A) ^ n : A ⟶ A) ▷ A).left).Gen, t.IsGen) : ∃ t : N.Gen, t.IsGen := by
  have hproj : IsProjBy A.hom :=
    (GlobalTheory.AmpleBaseChange.isProjBy_smooth_isProper_geometricallyIntegral _ A M hA hM ha R (𝟙 _) A.left (𝟙 _) A.hom
      (IsPullback.of_horiz_isIso ⟨by simp⟩)).1
  obtain ⟨H, j, hj, hH⟩ := GlobalTheory.TrivSubscheme.exists_closed_locTriv hL.globalFns R A A hA hproj N hN
  obtain ⟨t, ht⟩ := h1
  obtain ⟨y, hy⟩ := (hH A ((𝟙 A) ^ n)).1 fun p => ⟨⊤, trivial, GlobalTheory.TorsionFixedAut.exists_gen_pull _ t ht _⟩
  obtain ⟨f₁, f₂, f₃⟩ := GlobalTheory.MulAmple.finite_flat_surjective_pow hL R A hA M hM ha n hn
  have e : y.left ≫ j.left = ((𝟙 A) ^ n : A ⟶ A).left := congrArg (·.left) hy
  rw [← e] at f₁ f₂ f₃
  have : IsIso j.left := isIso_of_factor y.left j.left
  have hw : inv j.left ≫ H.hom = A.hom := by rw [← Over.w j, IsIso.inv_hom_id_assoc]
  have hloc := (hH A (𝟙 A)).2 ⟨Over.homMk (inv j.left) hw, Over.OverMorphism.ext (IsIso.inv_hom_id j.left)⟩
  have key : ∃ t : (N.pull (𝟙 A ▷ A).left).Gen, t.IsGen := by
    refine GlobalTheory.exists_gen_of_local_of_section (A ⊗ A).left A.left (fst A A).left
      (lift (𝟙 A) (1 : A ⟶ A)).left _ (pull_isLB hN _)
      (congrArg (·.left) (lift_fst (𝟙 A) (1 : A ⟶ A)))
      (GlobalTheory.BaseChangeFns.app_surjective hL.globalFns _ A hA _ _ A.hom _ _
        (GlobalTheory.SeesawGlobal.isPullback_tensor A A))
      hloc ?_
    rw [← cls_eq_zero_iff (pull_isLB (pull_isLB hN _) _), cls_pull (pull_isLB hN _), cls_pull hN, ← pull_comp,
      ← Over.comp_left, id_whiskerRight, Category.comp_id]
    exact (cls_eq_zero_iff (pull_isLB hN _)).2 h0
  rw [← cls_eq_zero_iff (pull_isLB hN _), cls_pull hN, id_whiskerRight, Over.id_left, pull_id] at key
  exact (cls_eq_zero_iff hN).1 key

section Pair

variable {S : Scheme.{0}} {A T : Over S}

def ev (c : Pic (A ⊗ A).left) (x y : T ⟶ A) : Pic T.left := pull (lift x y).left c

theorem pull_ev {T' : Over S} (h : T' ⟶ T) (c : Pic (A ⊗ A).left) (x y : T ⟶ A) :
    pull h.left (ev c x y) = ev c (h ≫ x) (h ≫ y) := by
  rw [ev, ev, ← pull_comp, ← Over.comp_left, comp_lift]

variable [GrpObj A] [IsCommMonObj A]

def Biadd (c : Pic (A ⊗ A).left) : Prop :=
  ∀ (T : Over S) (x x' y : T ⟶ A), ev c (x * x') y = ev c x y + ev c x' y ∧ ev c y (x * x') = ev c y x + ev c y x'

theorem biadd_of_axes (hG : Out.GlobalFnsSt) (hA : IsAbelianScheme A) (M : LB A.left) (hM : M.IsLB)
    (ha : Out.RelAmple A M) (N : LB (A ⊗ A).left) (hN : N.IsLB)
    (h₁ : ∃ t : (N.pull (lift (1 : A ⟶ A) (𝟙 A)).left).Gen, t.IsGen)
    (h₂ : ∃ t : (N.pull (lift (𝟙 A) (1 : A ⟶ A)).left).Gen, t.IsGen) : Biadd (cls N hN) := by
  intro T x x' y
  obtain ⟨a, b⟩ := GlobalTheory.Biadditive.biadditive_of_triv_axes hG S A M hA hM ha N hN h₁ h₂ T x x' y
  rw [← cls_eq_zero_iff (LB.isLB_linComb hN _ _), cls_linComb hN] at a b
  simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, one_smul,
    neg_smul] at a b
  constructor
  · unfold ev
    rw [← sub_eq_zero, ← a]
    abel
  · unfold ev
    rw [← sub_eq_zero, ← b]
    abel

end Pair

theorem lam_iso_of_pull_two : Out.Laws → ∀ (h k : ℕ) (o : Type) [CommRing o] (ζ : o) (R : Type) [CommRing R] [Algebra ℚ R] [IsNoetherianRing R] (β : o →+* R) (c : SiegPre h k ζ (spMap β)) (L : LB c.A.left), c.Principal → L.IsLB → LBIso (lbPow c.diag 2) (L.pull ((𝟙 c.A) ^ 2 : c.A ⟶ c.A).left) → LBIso (abelian₂ c.A L) c.P := by
  intro hL h k o _ ζ R _ _ _ β c L hc hLB hiso
  have hM : c.diag.IsLB := pull_isLB c.isLB _
  have hΛ : (abelian₂ c.A L).IsLB := LB.isLB_linComb hLB _ _
  have hN : (LB.div (abelian₂ c.A L) c.P).IsLB := LB.isLB_div hΛ c.isLB
  have hPow : (lbPow c.diag 2).IsLB := LB.isLB_linComb hM _ _
  set l := cls L hLB with hl
  set p := cls c.P c.isLB with hp
  have eΛ : cls _ hΛ = lam l (fst c.A c.A) (snd c.A c.A) := cls_cube_two hLB _ _ hΛ
  have eN : ∀ (T : Over (Sp R)) (x y : T ⟶ c.A), ev (cls _ hN) x y = lam l x y - ev p x y := by
    intro T x y
    rw [cls_div hΛ c.isLB, eΛ, ev, map_sub, pull_lam, lift_fst, lift_snd]
    rfl
  have r₁ : ev p (1 : c.A ⟶ c.A) (𝟙 c.A) = 0 := (cls_eq_zero_iff (pull_isLB c.isLB _)).2 c.rig₁
  have r₂ : ev p (𝟙 c.A) (1 : c.A ⟶ c.A) = 0 := (cls_eq_zero_iff (pull_isLB c.isLB _)).2 c.rig₂
  have n₁ : ∃ t : ((LB.div (abelian₂ c.A L) c.P).pull (lift (1 : c.A ⟶ c.A) (𝟙 c.A)).left).Gen, t.IsGen := by
    refine (cls_eq_zero_iff (pull_isLB hN _)).1 ((eN _ _ _).trans ?_)
    rw [r₁, lam_one_left, sub_zero]
  have n₂ : ∃ t : ((LB.div (abelian₂ c.A L) c.P).pull (lift (𝟙 c.A) (1 : c.A ⟶ c.A)).left).Gen, t.IsGen := by
    refine (cls_eq_zero_iff (pull_isLB hN _)).1 ((eN _ _ _).trans ?_)
    rw [r₂, lam_one_right, sub_zero]
  have bN := biadd_of_axes hL.globalFns c.ab _ hM hc.1 _ hN n₁ n₂
  have bP : Biadd p := biadd_of_axes hL.globalFns c.ab _ hM hc.1 _ c.isLB c.rig₁ c.rig₂
  have sy : ∀ (T : Over (Sp R)) (x y : T ⟶ c.A), ev p x y = ev p y x := by
    intro T x y
    have e : p = ev p (snd c.A c.A) (fst c.A c.A) := (cls_eq_iff c.isLB (pull_isLB c.isLB _)).2 c.symm
    calc ev p x y = pull (lift x y).left (ev p (snd c.A c.A) (fst c.A c.A)) := by rw [← e]; rfl
      _ = ev p y x := by rw [pull_ev, lift_fst, lift_snd]
  have dbl : ∀ (T : Over (Sp R)) (x : T ⟶ c.A), pull (x * x).left l = ev p x x + ev p x x := by
    intro T x
    have e : 2 • ev p (𝟙 c.A) (𝟙 c.A) = pull ((𝟙 c.A) ^ 2 : c.A ⟶ c.A).left l :=
      (cls_lbPow hM 2 hPow).symm.trans ((cls_eq_iff hPow (pull_isLB hLB _)).2 hiso)
    have e' := congrArg (pull x.left) e
    rw [map_nsmul, pull_ev, ← pull_comp, ← Over.comp_left, pow_two, MonObj.comp_mul, Category.comp_id,
      two_smul] at e'
    exact e'.symm
  have z : ∀ (T : Over (Sp R)) (x y : T ⟶ c.A), ev (cls _ hN) (x ^ 4) y = 0 := by
    intro T x y
    have a : ev (cls _ hN) (x * x) (y * y) = 0 := by
      have o₁ : ev p (1 : T ⟶ c.A) (1 : T ⟶ c.A) = 0 := by
        have := (bP T 1 1 1).1
        rw [_root_.mul_one] at this
        exact left_eq_add.1 this
      have o₂ := dbl T 1
      rw [_root_.mul_one, o₁] at o₂
      rw [eN, lam, _root_.mul_mul_mul_comm, dbl, dbl, dbl, o₂]
      simp only [(bP T _ _ _).1, (bP T _ _ _).2, sy T y x]
      abel
    rw [show x ^ 4 = x * x * (x * x) by rw [← pow_two, ← pow_two, ← pow_mul]]
    simp only [(bN T _ _ _).1, (bN T _ _ _).2] at a ⊢
    exact a
  have fin := triv_of_pull_pow hL c.A c.ab _ hM hc.1 4 (by norm_num) _ hN n₂ (by
    refine (cls_eq_zero_iff (pull_isLB hN _)).1 (Eq.trans ?_ (z _ (fst c.A c.A) (snd c.A c.A)))
    have e : ((𝟙 c.A) ^ 4 : c.A ⟶ c.A) ▷ c.A = lift (fst c.A c.A ^ 4) (snd c.A c.A) := by
      ext
      · rw [whiskerRight_fst, lift_fst, MonObj.comp_pow, Category.comp_id]
      · rw [whiskerRight_snd, lift_snd]
    rw [e]
    rfl)
  rw [← cls_eq_zero_iff hN, cls_div hΛ c.isLB, sub_eq_zero] at fin
  exact (cls_eq_iff hΛ c.isLB).1 fin

end GlobalTheory.LamOfDouble

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.SiegelSmoothOfRelativeDimensionCharZero
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.KeyPow GlobalTheory.KeyFam GlobalTheory.ZM GlobalTheory.AbLaw

namespace GlobalTheory.SiegDim

theorem card_torsion_of_level {G J : Type} [Group G] [Fintype J] (k : ℕ) (hk : k ≠ 0) (l : (J → ℤ) → G)
    (hadd : ∀ a b, l (a + b) = l a * l b) (htors : ∀ a, l a ^ k = 1)
    (hker : ∀ a, l a = 1 ↔ ∃ b, a = k • b) (hsurj : ∀ g : G, g ^ k = 1 → ∃ a, l a = g) :
    Nat.card {g : G // g ^ k = 1} = k ^ Fintype.card J := by
  classical
  have : NeZero k := ⟨hk⟩
  have key : ∀ a b, l a = l b ↔ ∀ i, ((a i : ℤ) : ZMod k) = (b i : ℤ) := fun a b => by
    have e : l b = l a * l (b - a) := by rw [← hadd]; congr 1; abel
    rw [e, left_eq_mul, hker]
    constructor
    · rintro ⟨c, hc⟩ i
      rw [ZMod.intCast_eq_intCast_iff_dvd_sub]
      exact ⟨c i, by simpa using congrFun hc i⟩
    · intro H
      choose c hc using fun i => (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).1 (H i)
      exact ⟨c, funext fun i => by simpa using hc i⟩
  let F : (J → ZMod k) → {g : G // g ^ k = 1} := fun c => ⟨l fun i => ((c i).val : ℤ), htors _⟩
  have hF : Function.Bijective F := by
    constructor
    · intro c c' e
      funext i
      simpa using (key _ _).1 (congrArg Subtype.val e) i
    · rintro ⟨g, hg⟩
      obtain ⟨a, rfl⟩ := hsurj g hg
      exact ⟨fun i => (a i : ZMod k), Subtype.ext ((key _ _).2 fun i => by simp)⟩
  rw [← Nat.card_eq_of_bijective F hF]
  simp [Nat.card_pi]

noncomputable def pointsEquiv {S S' : Scheme.{0}} {G' : Over S'} [GrpObj G'] {G : Over S} [GrpObj G] {f : S' ⟶ S}
    {φ : G'.left ⟶ G.left} (hp : IsGrpPullback G' G f φ) (T : Over S') :
    (T ⟶ G') ≃* (Over.mk (T.hom ≫ f) ⟶ G) where
  toFun y := Over.homMk (y.left ≫ φ) (by simp [hp.1.w])
  invFun q := Over.homMk (hp.1.lift q.left T.hom (Over.w q)) (hp.1.lift_snd _ _ _)
  left_inv y := Over.OverMorphism.ext (hp.1.hom_ext (by simp) (by simp))
  right_inv q := Over.OverMorphism.ext (by simp)
  map_mul' y y' := Over.OverMorphism.ext (hp.2 T y y' _ _ rfl rfl).symm

theorem dim_geometric_fibre {h k : ℕ} {o : Type} [CommRing o] {ζ : o} {S : Scheme.{0}} {s : S ⟶ Sp o}
    (c : SiegPre h k ζ s) (hk : 2 ≤ k) (hζ : IsUnit ζ) {K : Type} [Field K] [IsAlgClosed K] (hK : (k : K) ≠ 0)
    (x : Sp K ⟶ S) {d : ℕ} (hd : SmoothOfRelativeDimension d ((Over.pullback x).obj c.A).hom) : d = h := by
  let T := 𝟙_ (Over (Sp K))
  let β : o →+* K := (Spec.preimage ((T.hom ≫ x) ≫ s)).hom
  have hβ : (T.hom ≫ x) ≫ s = spMap β := (Spec.map_preimage ((T.hom ≫ x) ≫ s)).symm
  obtain ⟨h₁, h₂, -⟩ := c.geom K (T.hom ≫ x) β (hζ.map β).unit hβ rfl
  have n₁ := card_torsion_of_level k (by omega) (fun a => toUnit (Over.mk (T.hom ≫ x)) ≫ c.lev a)
    (fun a b => by rw [c.lev_add, MonObj.comp_mul])
    (fun a => by rw [← MonObj.comp_pow, c.lev_tors, MonObj.comp_one]) h₁ h₂
  have := c.ab.comm
  have := c.ab.smooth
  have := c.ab.proper
  have := c.ab.geomConnected
  have hab : IsAbelianScheme ((Over.pullback x).obj c.A) :=
    { comm := Functor.isCommMonObj_obj
      smooth := by change Smooth (pullback.snd c.A.hom x); infer_instance
      proper := by change IsProper (pullback.snd c.A.hom x); infer_instance
      geomConnected := by change GeometricallyConnected (pullback.snd c.A.hom x); infer_instance }
  have n₂ := GlobalTheory.UU.TorsionCount.card_torsion_points_unconditional K _ d k hab hd hK
  let e := pointsEquiv (isGrpPullback_pullback c.A x) T
  have n₃ := Nat.card_congr (e.toEquiv.subtypeEquiv (p := fun y => y ^ k = 1) (q := fun y => y ^ k = 1)
    fun y => by
      change _ ↔ e y ^ k = 1
      rw [← map_pow, MulEquiv.map_eq_one_iff])
  have n₄ : k ^ (2 * d) = k ^ (h + h) := by
    rw [← n₂, n₃, n₁]; simp
  have := Nat.pow_right_injective hk n₄
  omega

theorem smoothOfRelativeDimension :
    Out.Laws → ∀ (h k : ℕ) (o : Type) [CommRing o] (ζ : o) (R : Type) [CommRing R] [Algebra ℚ R] (β : o →+* R) (c : SiegPre h k ζ (spMap β)), 2 ≤ k → IsUnit ζ → SmoothOfRelativeDimension h c.A.hom := by
  intro _ h k o _ ζ R _ _ β c hk hζ
  have := c.ab.smooth
  have := c.ab.geomConnected
  choose n W hW hd using H1.exists_dim c.A.hom
  have : IsZariskiLocalAtSource (@SmoothOfRelativeDimension h) :=
    HasRingHomProperty.instIsZariskiLocalAtSource
  refine IsZariskiLocalAtSource.of_iSup_eq_top W
    (top_le_iff.1 fun y _ => TopologicalSpace.Opens.mem_iSup.2 ⟨y, hW y⟩) fun y => ?_
  let κ := (Sp R).residueField (c.A.hom y)
  let K := AlgebraicClosure κ
  let x : Sp K ⟶ Sp R := spMap (algebraMap κ K) ≫ (Sp R).fromSpecResidueField (c.A.hom y)
  have hK : (k : K) ≠ 0 := by
    have := map_natCast ((Spec.preimage x).hom.comp (algebraMap ℚ R)) k
    rw [← this]
    exact (_root_.map_ne_zero _).2 (Nat.cast_ne_zero.2 (by omega))
  have hp := (isGrpPullback_pullback c.A x).1
  obtain ⟨y', hy', -⟩ := Scheme.exists_preimage_of_isPullback hp y (default : PrimeSpectrum K)
    (Scheme.fromSpecResidueField_apply _ _).symm
  have : Smooth ((Over.pullback x).obj c.A).hom := by change Smooth (pullback.snd c.A.hom x); infer_instance
  have : ConnectedSpace ((Over.pullback x).obj c.A).left :=
    GeometricallyConnected.geometrically_connectedSpace (f := c.A.hom) x _ _ hp
  obtain ⟨d, hd'⟩ := exists_dim_of_preconnected ((Over.pullback x).obj c.A).hom y'
  have e : n y = h :=
    (H1.dim_base hp (hd y) hd' y' (by rw [hy']; exact hW y)).trans (dim_geometric_fibre c hk hζ hK x hd')
  have := hd y
  rwa [e] at this

end GlobalTheory.SiegDim
end

