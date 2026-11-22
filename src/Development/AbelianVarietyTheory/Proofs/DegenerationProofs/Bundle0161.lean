import Mathlib
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0154
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0132
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.PolAVIsoExtendsOfIsIntegrallyClosed
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.GenRelNeZero
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0035
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0111
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0083
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0020
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.TangentLinearity.ConstPullback
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0138
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0148
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle0001
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0158
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0133

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsValuedFieldValuationCentreLePow
section
namespace GlobalTheory

theorem exists_valuedField_centred_subalgebra (R K : Type) [CommRing R] [IsDomain R]
    [IsNoetherianRing R] [Field K] [Algebra R K] [FaithfulSMul R K] [Algebra.IsAlgebraic R K]
    (u : R) (hu : u ≠ 0) (A : Subalgebra R K) (hA : A.FG) (P : Ideal A) (hP : P.IsPrime)
    (huP : algebraMap R A u ∈ P) :
    ∃ (C : Type) (_ : NontriviallyNormedField C) (_ : IsUltrametricDist C) (_ : CompleteSpace C)
      (_ : IsAlgClosed C) (gam : K →+* C), (∀ x ∈ A, ‖gam x‖ ≤ 1) ∧
        ∀ x : A, x ∈ P → ‖gam (x : K)‖ < 1 := by
  have hinjK : Function.Injective (algebraMap R K) := FaithfulSMul.algebraMap_injective R K
  have hinj : Function.Injective (algebraMap R A) := by
    intro a b hab
    apply hinjK
    have := congrArg (fun x : A => (x : K)) hab
    simpa using this
  haveI : IsNoetherianRing A := isNoetherianRing_of_fg hA
  haveI : Algebra.IsAlgebraic A K := Algebra.IsAlgebraic.extendScalars hinj
  haveI : FaithfulSMul A K :=
    (faithfulSMul_iff_algebraMap_injective A K).2 Subtype.val_injective
  have hne : P ≠ ⊥ := by
    intro h
    rw [h, Ideal.mem_bot] at huP
    exact hu (hinj (by rw [huP, map_zero]))
  obtain ⟨C, i1, i2, i3, i4, gam, h1, h2⟩ := GlobalTheory.T.exists_complete_algClosed_field_centred_at_prime A K P hP hne
  exact ⟨C, i1, i2, i3, i4, gam, fun x hx => h1 ⟨x, hx⟩, fun x hx => h2 x hx⟩

theorem exists_valuedField_centre_le_pow : ∀ (R K : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsLocalRing R] [Field K] [Algebra R K] [FaithfulSMul R K] [Algebra.IsAlgebraic R K] (u : R), u ∈ IsLocalRing.maximalIdeal R → u ≠ 0 → ∀ R₁ : Subalgebra R K, Module.Finite R R₁ → ∀ S : ValuationSubring K, (∀ r, algebraMap R K r ∈ S) → ∀ e : ℕ, ∃ (C : Type) (_ : NontriviallyNormedField C) (_ : IsUltrametricDist C) (_ : CompleteSpace C) (_ : IsAlgClosed C) (gam : K →+* C), (∀ r, ‖gam (algebraMap R K r)‖ ≤ 1) ∧ ‖gam (algebraMap R K u)‖ < 1 ∧ ∀ f ∈ R₁, S.valuation f < 1 → ‖gam f‖ < 1 ∧ (S.valuation (algebraMap R K u) = 1 → ‖gam f‖ ≤ ‖gam (algebraMap R K u)‖ ^ e) := by
  intro R K _ _ _ _ _ _ _ _ u hum hu R₁ hfin S hS e
  have hinjK : Function.Injective (algebraMap R K) := FaithfulSMul.algebraMap_injective R K
  have hR : ∀ r, S.valuation (algebraMap R K r) ≤ 1 := fun r =>
    (S.valuation_le_one_iff _).2 (hS r)
  have hR₁ : ∀ x ∈ R₁, S.valuation x ≤ 1 := by
    intro x hx
    have hint : IsIntegral R x := by
      have h := (Algebra.IsIntegral.isIntegral (R := R) (⟨x, hx⟩ : R₁)).map R₁.val
      simpa using h
    letI : Algebra R S := ((algebraMap R K).codRestrict S.toSubring hS).toAlgebra
    haveI : IsScalarTower R S K := IsScalarTower.of_algebraMap_eq fun _ => rfl
    have hint' : IsIntegral S x := hint.tower_top
    obtain ⟨y, hy⟩ := (IsIntegrallyClosed.isIntegral_iff (R := S) (K := K)).1 hint'
    rw [← hy]
    exact (S.valuation_le_one_iff _).2 y.2
  have hfg : (Subalgebra.toSubmodule R₁).FG := Module.Finite.iff_fg.1 hfin
  let q : Ideal R₁ :=
    { carrier := {x | S.valuation (x : K) < 1}
      add_mem' := fun {a b} ha hb => by
        simpa using S.valuation.map_add_lt ha hb
      zero_mem' := by simp
      smul_mem' := fun c x hx => by
        have hx' : S.valuation (x : K) < 1 := hx
        show S.valuation ((c : K) * (x : K)) < 1
        rw [map_mul]
        exact lt_of_le_of_lt (mul_le_of_le_one_left' (hR₁ _ c.2)) hx' }
  have hq : ∀ x : R₁, x ∈ q ↔ S.valuation (x : K) < 1 := fun _ => Iff.rfl
  have hqp : q.IsPrime := by
    refine ⟨?_, ?_⟩
    · rw [Ideal.ne_top_iff_one, hq]; simp
    · intro a b hab
      by_contra hcon
      rw [not_or, hq, hq, not_lt, not_lt] at hcon
      rw [hq, Subalgebra.coe_mul, map_mul, le_antisymm (hR₁ _ a.2) hcon.1,
        le_antisymm (hR₁ _ b.2) hcon.2] at hab
      simp at hab
  by_cases hv : S.valuation (algebraMap R K u) = 1
  ·
    set U : K := algebraMap R K u with hU
    have hU0 : U ≠ 0 := fun h => hu (hinjK (by rw [← hU, h, map_zero]))
    let Q : Submodule R K := (q.restrictScalars R).map R₁.val.toLinearMap
    have hQ : Q.FG := by
      haveI : IsNoetherian R R₁ := isNoetherian_of_isNoetherianRing_of_finite R R₁
      exact Submodule.FG.map _ (IsNoetherian.noetherian _)
    let N : Submodule R K := Subalgebra.toSubmodule R₁ ⊔
      Q.map (LinearMap.mulRight R (U ^ (e + 1))⁻¹)
    have hN : N.FG := Submodule.FG.sup hfg (hQ.map _)
    let A : Subalgebra R K := Algebra.adjoin R (N : Set K)
    have hA : A.FG := by
      obtain ⟨s, hs⟩ := hN
      refine ⟨s, ?_⟩
      show _ = Algebra.adjoin R (N : Set K)
      rw [← hs, Algebra.adjoin_span]
    have hinv : ∀ x ∈ A, ∃ a ∈ R₁, S.valuation (x - a) < 1 := by
      intro x hx
      induction hx using Algebra.adjoin_induction with
      | mem x hx =>
        obtain ⟨a, ha, _, ⟨_, ⟨g, hg, rfl⟩, rfl⟩, rfl⟩ := Submodule.mem_sup.1 hx
        refine ⟨a, ha, ?_⟩
        have hg' : S.valuation (g : K) < 1 := hg
        simpa [hv] using hg'
      | algebraMap r => exact ⟨_, R₁.algebraMap_mem r, by simp⟩
      | add x y _ _ hx hy =>
        obtain ⟨a, ha, hx⟩ := hx
        obtain ⟨b, hb, hy⟩ := hy
        refine ⟨a + b, R₁.add_mem ha hb, ?_⟩
        rw [show x + y - (a + b) = (x - a) + (y - b) by ring]
        exact S.valuation.map_add_lt hx hy
      | mul x y _ _ hx hy =>
        obtain ⟨a, ha, hx⟩ := hx
        obtain ⟨b, hb, hy⟩ := hy
        refine ⟨a * b, R₁.mul_mem ha hb, ?_⟩
        rw [show x * y - a * b = (x - a) * (y - b) + (b * (x - a) + a * (y - b)) by ring]
        refine S.valuation.map_add_lt ?_ (S.valuation.map_add_lt ?_ ?_) <;> rw [map_mul]
        · exact lt_of_le_of_lt (mul_le_of_le_one_left' hx.le) hy
        · exact lt_of_le_of_lt (mul_le_of_le_one_left' (hR₁ _ hb)) hx
        · exact lt_of_le_of_lt (mul_le_of_le_one_left' (hR₁ _ ha)) hy
    have hnu : ¬ IsUnit (algebraMap R A u) := by
      intro hun
      obtain ⟨x, hx⟩ := hun.exists_right_inv
      have hx' : U * (x : K) = 1 := by
        have := congrArg (fun x : A => (x : K)) hx
        simpa using this
      obtain ⟨a, ha, hxa⟩ := hinv x x.2
      obtain ⟨M, hM, hqM⟩ := Ideal.exists_le_maximal q hqp.ne_top
      have hMc : (M.comap (algebraMap R R₁)).IsMaximal :=
        Ideal.isMaximal_comap_of_isIntegral_of_isMaximal M
      have huM : algebraMap R R₁ u ∈ M := by
        rw [← Ideal.mem_comap, IsLocalRing.eq_maximalIdeal hMc]; exact hum
      have h1 : (1 - algebraMap R R₁ u * ⟨a, ha⟩ : R₁) ∈ q := by
        rw [hq]
        have : ((1 - algebraMap R R₁ u * ⟨a, ha⟩ : R₁) : K) = U * (x - a) := by
          rw [mul_sub, hx']; simp [hU]
        rw [this, map_mul, hv, one_mul]
        exact hxa
      apply hM.ne_top
      rw [Ideal.eq_top_iff_one]
      simpa using M.add_mem (hqM h1) (M.mul_mem_right (⟨a, ha⟩ : R₁) huM)
    obtain ⟨P, hP, huP⟩ := exists_max_ideal_of_mem_nonunits (mem_nonunits_iff.2 hnu)
    obtain ⟨C, i1, i2, i3, i4, gam, h1, h2⟩ :=
      exists_valuedField_centred_subalgebra R K u hu A hA P hP.isPrime huP
    have hgu : ‖gam U‖ < 1 := h2 _ huP
    refine ⟨C, i1, i2, i3, i4, gam, fun r => h1 _ (A.algebraMap_mem r), hgu, ?_⟩
    intro f hf hvf
    have hmem : f * (U ^ (e + 1))⁻¹ ∈ A :=
      Algebra.subset_adjoin (Submodule.mem_sup_right
        (Submodule.mem_map.2 ⟨f, Submodule.mem_map.2 ⟨⟨f, hf⟩, hvf, rfl⟩, rfl⟩))
    have hle : ‖gam f‖ ≤ ‖gam U‖ ^ (e + 1) := by
      have hf' : f = f * (U ^ (e + 1))⁻¹ * U ^ (e + 1) := by field_simp
      have h3 := h1 _ hmem
      rw [hf', map_mul, norm_mul, map_pow, norm_pow]
      exact mul_le_of_le_one_left (by positivity) h3
    refine ⟨hle.trans_lt (pow_lt_one₀ (norm_nonneg _) hgu (by omega)), fun _ => hle.trans ?_⟩
    exact pow_le_pow_of_le_one (norm_nonneg _) hgu.le (by omega)
  · have huq : algebraMap R R₁ u ∈ q := lt_of_le_of_ne (hR u) hv
    obtain ⟨C, i1, i2, i3, i4, gam, h1, h2⟩ :=
      exists_valuedField_centred_subalgebra R K u hu R₁ (Subalgebra.fg_of_fg_toSubmodule hfg)
        q hqp huq
    exact ⟨C, i1, i2, i3, i4, gam, fun r => h1 _ (R₁.algebraMap_mem r), h2 _ huq,
      fun f hf hvf => ⟨h2 ⟨f, hf⟩ hvf, fun h => absurd h hv⟩⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.PolarisedAVIsoDescendsOfRationalThreeTorsion
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex GlobalTheory.Ex.Trait

set_option backward.isDefEq.respectTransparency false

namespace GlobalTheory.PolIsoDescent

open GlobalTheory.GenSpread

theorem flat_surjective {F C : Type} [Field F] [Field C] (i : Sp F ⟶ Sp C) : Flat i ∧ Surjective i :=
  have : Subsingleton (Sp C) := inferInstanceAs (Subsingleton (PrimeSpectrum C))
  ⟨inferInstance, ⟨fun _ => ⟨(default : PrimeSpectrum F), Subsingleton.elim _ _⟩⟩⟩

theorem charZero_of_hom {F C : Type} [Field F] [Field C] [CharZero C] (i : Sp F ⟶ Sp C) : CharZero F :=
  charZero_of_injective_ringHom (f := (Spec.preimage i).hom) (RingHom.injective _)

theorem exists_torsion_of_algClosed (hM : MulNSt) {S : Scheme.{0}} [IsLocallyNoetherian S] (P : PolAV S) {F C : Type}
    [Field F] [IsAlgClosed F] [Field C] [IsAlgClosed C] [CharZero C] (i : Sp F ⟶ Sp C) (t : Sp C ⟶ S) {n : ℕ}
    (hn : 1 ≤ n) (x : Over.mk (i ≫ t) ⟶ P.A) (hx : x ^ n = 1) :
    ∃ z : Over.mk t ⟶ P.A, z ^ n = 1 ∧ x.left = i ≫ z.left := by
  have := charZero_of_hom i
  obtain ⟨_, _⟩ := flat_surjective i
  have : Epi i := Flat.epi_of_flat_of_surjective _
  have h := (hM S P n hn).2.2.2.2
  have h₁ := h F (i ≫ t) (Nat.cast_ne_zero.2 (by omega))
  have h₂ := h C t (Nat.cast_ne_zero.2 (by omega))
  let ρ : Over.mk (i ≫ t) ⟶ Over.mk t := Over.homMk i rfl
  let r : {x : Over.mk t ⟶ P.A // x ^ n = 1} → {x : Over.mk (i ≫ t) ⟶ P.A // x ^ n = 1} := fun z =>
    ⟨ρ ≫ z.1, by rw [← MonObj.comp_pow, z.2, MonObj.comp_one]⟩
  have hr : Function.Injective r := fun a b e => Subtype.ext (Over.OverMorphism.ext
    ((cancel_epi i).1 (congrArg (fun q => q.1.left) e)))
  have : Finite {x : Over.mk (i ≫ t) ⟶ P.A // x ^ n = 1} :=
    Nat.finite_of_card_ne_zero (by rw [h₁]; positivity)
  obtain ⟨z, hz⟩ := ((Nat.bijective_iff_injective_and_card r).2 ⟨hr, h₂.trans h₁.symm⟩).2 ⟨x, hx⟩
  exact ⟨z.1, z.2, (congrArg (fun q => q.1.left) hz).symm⟩

theorem eq_of_torsion (hL : Laws) {S : Scheme.{0}} (P : PolAV S) {F : Type} [Field F] [IsAlgClosed F]
    (W : PolAV (Sp F)) {s : Sp F ⟶ S} {f₁ f₂ : W.A.left ⟶ P.A.left} (h₁ : IsGrpPullback W.A P.A s f₁)
    (h₂ : IsGrpPullback W.A P.A s f₂) (l₁ : LBIso W.L (P.L.pull f₁)) (l₂ : LBIso W.L (P.L.pull f₂)) {M : ℕ}
    (hM : 3 ≤ M) (hF : (M : F) ≠ 0)
    (h : ∀ y : Over.mk (𝟙 (Sp F)) ⟶ W.A, y ^ M = 1 → y.left ≫ f₁ = y.left ≫ f₂) : f₁ = f₂ := by
  obtain ⟨θ, hθ, e⟩ := grpPullback_iso h₁ h₂
  obtain ⟨w, hw⟩ := l₁.trans W.isLB (pull_isLB P.isLB _) (pull_isLB W.isLB _)
    (lbIso_pull_of_lbIso l₂ θ.hom.left e.symm).symm
  have := MatchRigid.aut_eq_id hL W (𝟙 _) hM hF θ w hw fun y hy =>
    Over.OverMorphism.ext (h₂.1.hom_ext (by rw [Over.comp_left, Category.assoc, e, h y hy]) (by rw [Over.w, Over.w]))
  rw [← e, this, Over.id_left, Category.id_comp]

theorem comp_eq_of_rational (hL : Laws) {S U : Scheme.{0}} [IsLocallyNoetherian S] (B B' : PolAV S) {C : Type}
    [Field C] [IsAlgClosed C] [CharZero C] (κ : Sp C ⟶ U) (j : U ⟶ S)
    (rB : ∀ x : Over.mk (κ ≫ j) ⟶ B.A, x ^ 3 = 1 → ∃ x₀ : U ⟶ B.A.left, x.left = κ ≫ x₀)
    (rB' : ∀ x : Over.mk (κ ≫ j) ⟶ B'.A, x ^ 3 = 1 → ∃ x₀ : U ⟶ B'.A.left, x.left = κ ≫ x₀)
    {Q : Over (Sp C)} [GrpObj Q] {f : Q.left ⟶ B.A.left} {f' : Q.left ⟶ B'.A.left}
    (hf : IsGrpPullback Q B.A (κ ≫ j) f) (hf' : IsGrpPullback Q B'.A (κ ≫ j) f')
    (hl : LBIso (B'.L.pull f') (B.L.pull f)) {F : Type} [Field F] [IsAlgClosed F] (x x' : Sp F ⟶ Q.left)
    (e : x ≫ f' = x' ≫ f') (e' : (x ≫ Q.hom) ≫ κ = (x' ≫ Q.hom) ≫ κ) : x ≫ f = x' ≫ f := by
  have := charZero_of_hom (x ≫ Q.hom)
  obtain ⟨W, h, hh, -, hm, hw⟩ := hL.polBaseChange S _ (((x ≫ Q.hom) ≫ κ) ≫ j) B'
  have hp : IsGrpPullback W.A B'.A (((x ≫ Q.hom) ≫ κ) ≫ j) h := ⟨hh, fun T x y x₀ y₀ hx hy => by
    rw [(Over.OverMorphism.ext hx : x₀ = toBase hh.w x), (Over.OverMorphism.ext hy : y₀ = toBase hh.w y), ← hm]
    rfl⟩
  have key : ∀ i : Sp F ⟶ Sp C, (x ≫ Q.hom) ≫ κ = i ≫ κ → ∃ a : W.A.left ⟶ Q.left, a ≫ f' = h ∧
      a ≫ Q.hom = W.A.hom ≫ i ∧ IsGrpPullback W.A B.A (((x ≫ Q.hom) ≫ κ) ≫ j) (a ≫ f) ∧
      LBIso W.L (B.L.pull (a ≫ f)) := fun i hi => by
    have hi' : ((x ≫ Q.hom) ≫ κ) ≫ j = i ≫ κ ≫ j := by rw [hi, Category.assoc]
    have w : h ≫ B'.A.hom = (W.A.hom ≫ i) ≫ κ ≫ j := by rw [hh.w, hi', Category.assoc]
    have a₁ := hf'.1.lift_fst _ _ w
    have a₂ := hf'.1.lift_snd _ _ w
    exact ⟨_, a₁, a₂, ((hf'.cancel (hp.congr hi' a₁.symm) a₂).comp hf).congr hi'.symm rfl,
      (LBIso.symm hw).trans W.isLB (pull_isLB B'.isLB _) (pull_isLB B.isLB _) (lbIso_pull_comp _ a₁.symm rfl hl)⟩
  obtain ⟨a, a₁, a₂, a₃, a₄⟩ := key _ rfl
  obtain ⟨a', a₁', a₂', a₃', a₄'⟩ := key _ e'
  have E : a ≫ f = a' ≫ f := by
    refine eq_of_torsion hL B W a₃ a₃' a₄ a₄' le_rfl (by norm_num) fun y hy => ?_
    have hyw : y.left ≫ W.A.hom = 𝟙 _ := Over.w y
    let ρ : Over.mk ((x ≫ Q.hom) ≫ κ ≫ j) ⟶ Over.mk (𝟙 _ ≫ ((x ≫ Q.hom) ≫ κ) ≫ j) := Over.homMk (𝟙 _) (by simp)
    obtain ⟨z, hz, ez⟩ := exists_torsion_of_algClosed hL.mulN B' (x ≫ Q.hom) (κ ≫ j) (n := 3) (by norm_num)
      (ρ ≫ pushHom hp _ y) (by rw [← MonObj.comp_pow]; erw [← map_pow, hy, map_one, MonObj.comp_one])
    replace ez : y.left ≫ h = (x ≫ Q.hom) ≫ z.left := (Category.id_comp _).symm.trans ez
    obtain ⟨z₀, hz₀⟩ := rB' z hz
    have hzw : z.left ≫ B'.A.hom = 𝟙 _ ≫ κ ≫ j := (Over.w z).trans (Category.id_comp _).symm
    let u : Over.mk (𝟙 (Sp C)) ⟶ Q := Over.homMk (hf'.1.lift z.left (𝟙 _) hzw) (hf'.1.lift_snd _ _ _)
    have u₁ : u.left ≫ f' = z.left := hf'.1.lift_fst _ _ _
    have u₂ : u.left ≫ Q.hom = 𝟙 _ := Over.w u
    let σ : Over.mk (𝟙 _ ≫ κ ≫ j) ⟶ Over.mk (κ ≫ j) := Over.homMk (𝟙 _) rfl
    let σ' : Over.mk (κ ≫ j) ⟶ Over.mk (𝟙 _ ≫ κ ≫ j) := Over.homMk (𝟙 _) (by simp)
    have hu : u ^ 3 = 1 := by
      have inj : Function.Injective (pushHom hf' (Over.mk (𝟙 _))) := fun p q h => Over.OverMorphism.ext
        (hf'.1.hom_ext (congrArg (fun m => m.left) h) (by rw [Over.w, Over.w]))
      have : pushHom hf' _ u = σ ≫ z := Over.OverMorphism.ext (u₁.trans (Category.id_comp _).symm)
      apply inj
      rw [map_pow, this, ← MonObj.comp_pow, hz, MonObj.comp_one, map_one]
    obtain ⟨v₀, hv₀⟩ := rB (σ' ≫ pushHom hf _ u)
      (by rw [← MonObj.comp_pow]; erw [← map_pow, hu, map_one, MonObj.comp_one])
    replace hv₀ : u.left ≫ f = κ ≫ v₀ := (Category.id_comp _).symm.trans hv₀
    have fin : ∀ (i : Sp F ⟶ Sp C) (b : W.A.left ⟶ Q.left), (x ≫ Q.hom) ≫ κ = i ≫ κ → b ≫ f' = h →
        b ≫ Q.hom = W.A.hom ≫ i → y.left ≫ b ≫ f = (i ≫ κ) ≫ v₀ := fun i b hi b₁ b₂ => by
      have : y.left ≫ b = i ≫ u.left := hf'.1.hom_ext
        (by rw [Category.assoc, b₁, ez, Category.assoc i, u₁, hz₀, ← Category.assoc, hi, Category.assoc])
        (by rw [Category.assoc, b₂, reassoc_of% hyw, Category.assoc, u₂]; exact (Category.comp_id _).symm)
      rw [reassoc_of% this, hv₀, Category.assoc]
    rw [fin _ a rfl a₁ a₂, fin _ a' e' a₁' a₂', e']
  have w : (x ≫ f') ≫ B'.A.hom = 𝟙 _ ≫ ((x ≫ Q.hom) ≫ κ) ≫ j := by simp [hf'.1.w]
  have y₁ := hh.lift_fst _ _ w
  have y₂ := hh.lift_snd _ _ w
  have fin : ∀ (p : Sp F ⟶ Q.left) (b : W.A.left ⟶ Q.left), x ≫ f' = p ≫ f' → b ≫ f' = h →
      b ≫ Q.hom = W.A.hom ≫ p ≫ Q.hom → p = hh.lift _ _ w ≫ b := fun p b hp b₁ b₂ => hf'.1.hom_ext
    (by rw [Category.assoc, b₁, y₁, hp]) (by rw [Category.assoc, b₂, reassoc_of% y₂])
  rw [fin x' a' e a₁' a₂', Category.assoc, ← E, ← Category.assoc, ← fin x a rfl a₁ a₂]

theorem isGrpPullback_of_one (hL : Laws) {S S' : Scheme.{0}} {t : S' ⟶ S} {G : Over S} [GrpObj G] {Q : Over S'}
    [GrpObj Q] (hG : IsAbelianScheme G) (hQ : IsAbelianScheme Q) {f : Q.left ⟶ G.left}
    (hf : IsPullback f Q.hom G.hom t) (h₀ : eSec Q ≫ f = t ≫ eSec G) : IsGrpPullback Q G t f := by
  have hp := isGrpPullback_pullback G t
  let e : Q ≅ (Over.pullback t).obj G :=
    Over.isoMk (hf.isoIsPullback _ _ hp.1) (hf.isoIsPullback_hom_snd _ _ hp.1)
  have he : e.hom.left ≫ pullback.fst G.hom t = f := hf.isoIsPullback_hom_fst _ _ hp.1
  have : IsMonHom e.hom := hL.rigidity _ _ _ hQ (TLinPf.isAb_pullback t G hG) e.hom
    (Over.OverMorphism.ext (hp.1.hom_ext
      ((Category.assoc _ _ _).trans ((congrArg (eSec Q ≫ ·) he).trans (h₀.trans (PolExtend.eSec_fst t G).symm)))
      (by rw [Over.w, Over.w])))
  exact ((isGrpPullback_of_iso e).comp hp).congr (Category.id_comp _) he

theorem lbIso_descend (hG : GlobalFnsSt) {K C : Type} [Field K] [Field C] (κ : Sp C ⟶ Sp K) (X : Over (Sp K))
    [GrpObj X] (hX : IsAbelianScheme X) {L M : LB X.left} (hL : L.IsLB) (hM : M.IsLB)
    (h : LBIso (L.pull (pullback.fst X.hom κ)) (M.pull (pullback.fst X.hom κ))) : LBIso L M := by
  obtain ⟨h₁, h₂⟩ := flat_surjective κ
  have hN := LB.isLB_div hM hL
  have : Subsingleton (Sp K) := inferInstanceAs (Subsingleton (PrimeSpectrum K))
  obtain ⟨i, hi⟩ := exists_chart hN (eSec X (default : PrimeSpectrum K))
  exact exists_gen_of_rigidified_of_flat_baseChange hG _ _ κ X _ hX hN h₁ h₂ inferInstance
    (IsoExtend.exists_gen_of_chart hN _ i fun y => by
      rw [Subsingleton.elim (α := Sp K) y (default : PrimeSpectrum K)]; exact hi)
    ((IsoExtend.lbIso_pull_iff_gen L M _).1 h)

end GlobalTheory.PolIsoDescent

open GlobalTheory.PolIsoDescent GlobalTheory.GenSpread in

theorem GlobalTheory.polAV_iso_descends_of_ratTors : Laws → Laws2 → GlobalTheory.LN.HomExtSt → ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], GlobalTheory.LN.CDvr R → ∀ (C : Type) [Field C] [IsAlgClosed C] [Algebra (FractionRing R) C] (B B' : PolAV (Sp R)), RatTors B C 3 → RatTors B' C 3 → ∀ (φ : TF (R := R) C ⊗ B.A ≅ TF (R := R) C ⊗ B'.A) (g : (TF (R := R) C ⟶ B.A) ≃* (TF (R := R) C ⟶ B'.A)), φ.hom ≫ fst _ _ = fst _ _ → (∀ x, lift (𝟙 _) x ≫ φ.hom = lift (𝟙 _) (g x)) → LBIso (B.L.pull (snd (TF (R := R) C) B.A).left) (B'.L.pull (φ.hom ≫ snd (TF (R := R) C) B'.A).left) → ∃ Ψ : B'.A ≅ B.A, IsMonHom Ψ.hom ∧ LBIso B'.L (B.L.pull Ψ.hom.left) ∧ ∀ x, g x ≫ Ψ.hom = x := by
  intro hL hL₂ hext R _ _ _ ⟨_, _, _⟩ C _ _ _ B B' rB rB' φ g hφ hg hl
  have : CharZero (FractionRing R) := charZero_of_injective_algebraMap (IsFractionRing.injective R _)
  have : CharZero C := charZero_of_injective_algebraMap (algebraMap (FractionRing R) C).injective
  let κ : Sp C ⟶ Sp (FractionRing R) := jFK (R := R) C
  let X := (Over.pullback (jK R)).obj B'.A
  let Y := (Over.pullback (jK R)).obj B.A
  let Q := (Over.pullback κ).obj X
  have hX : IsAbelianScheme X := TLinPf.isAb_pullback _ _ B'.isAb
  have hY : IsAbelianScheme Y := TLinPf.isAb_pullback _ _ B.isAb
  have hQ : IsAbelianScheme Q := TLinPf.isAb_pullback _ _ hX
  let π : Q.left ⟶ X.left := pullback.fst X.hom κ
  let p : X.left ⟶ B'.A.left := pullback.fst B'.A.hom (jK R)
  have hπ : IsGrpPullback Q X κ π := isGrpPullback_pullback X κ
  have hp : IsGrpPullback X B'.A (jK R) p := isGrpPullback_pullback B'.A (jK R)
  have hY' := isGrpPullback_pullback B.A (jK R)
  have hf' := hπ.comp hp
  have pb : ∀ A : Over (Sp R), IsPullback (snd (TF (R := R) C) A).left (fst (TF (R := R) C) A).left A.hom (κ ≫ jK R) :=
    fun A => (IsPullback.of_hasPullback (TF (R := R) C).hom A.hom).flip
  let c := hf'.1.isoIsPullback _ _ (pb B'.A)
  have c₁ : c.hom ≫ (snd (TF (R := R) C) B'.A).left = π ≫ p := hf'.1.isoIsPullback_hom_fst _ _ _
  have c₂ : c.hom ≫ (fst (TF (R := R) C) B'.A).left = Q.hom := hf'.1.isoIsPullback_hom_snd _ _ _
  have hφ' : φ.inv ≫ fst _ _ = fst _ _ := by rw [← hφ, Iso.inv_hom_id_assoc]
  let f : Q.left ⟶ B.A.left := (c.hom ≫ φ.inv.left) ≫ (snd (TF (R := R) C) B.A).left
  have hfp : IsPullback f Q.hom B.A.hom (κ ≫ jK R) := by
    have : IsIso φ.inv.left := inferInstanceAs (IsIso ((Over.forget _).map φ.inv))
    have h : IsPullback (c.hom ≫ φ.inv.left) Q.hom (fst (TF (R := R) C) B.A).left (𝟙 _) :=
      IsPullback.of_horiz_isIso ⟨by rw [Category.assoc, ← Over.comp_left, hφ', c₂, Category.comp_id]⟩
    exact Category.id_comp (κ ≫ jK R) ▸ h.paste_horiz (pb B.A)
  have pt : ∀ (x : TF (R := R) C ⟶ B.A) (u : Sp C ⟶ Q.left), u ≫ π ≫ p = (g x).left → u ≫ Q.hom = 𝟙 _ →
      u ≫ f = x.left := fun x u u₁ u₂ => by
    have : u ≫ c.hom = (lift (𝟙 _) (g x)).left := (pb B'.A).hom_ext
      (by rw [Category.assoc, c₁, u₁, ← Over.comp_left, lift_snd])
      (by rw [Category.assoc, c₂, u₂, ← Over.comp_left, lift_fst]; rfl)
    change u ≫ (c.hom ≫ _) ≫ _ = _
    rw [Category.assoc, reassoc_of% this, ← Over.comp_left, ← Over.comp_left, ← hg, Category.assoc,
      Iso.hom_inv_id_assoc, lift_snd]
  have one : ∀ P : PolAV (Sp R), (1 : TF (R := R) C ⟶ P.A).left = (κ ≫ jK R) ≫ eSec P.A := fun _ => rfl
  have hf : IsGrpPullback Q B.A (κ ≫ jK R) f := by
    refine isGrpPullback_of_one hL B.isAb hQ hfp ((pt 1 _ ?_ (Over.w η[Q])).trans (one B))
    rw [map_one, one, ← Category.assoc]
    erw [PolExtend.eSec_fst κ X, Category.assoc, PolExtend.eSec_fst (jK R) B'.A, Category.assoc]
  have hl' : LBIso (B'.L.pull (π ≫ p)) (B.L.pull f) := lbIso_pull_comp (c.hom ≫ φ.inv.left)
    (by rw [Category.assoc, ← Over.comp_left, Iso.inv_hom_id_assoc, c₁]) rfl hl.symm
  have wf : f ≫ B.A.hom = (Q.hom ≫ κ) ≫ jK R := by rw [hfp.w, Category.assoc]
  obtain ⟨f₀, hf₀⟩ := exists_desc_of_smooth_of_geometricPoints (FractionRing R) C X Y hX.smooth
    (have := hY.proper; inferInstance) (hY'.1.lift f (Q.hom ≫ κ) wf) ((hY'.1.lift_snd _ _ _).trans hπ.1.w.symm)
    fun F _ _ x x' e => by
      have e' : (x ≫ Q.hom) ≫ κ = (x' ≫ Q.hom) ≫ κ := by
        rw [Category.assoc, Category.assoc, ← hπ.1.w]
        exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ X.hom) e).trans (Category.assoc _ _ _))
      refine hY'.1.hom_ext ?_ ?_
      · rw [Category.assoc, Category.assoc, hY'.1.lift_fst]
        exact comp_eq_of_rational hL B B' κ (jK R) (fun x hx => (rB x hx).elim fun a h => ⟨a.left, h⟩)
          (fun x hx => (rB' x hx).elim fun a h => ⟨a.left, h⟩) hf hf' hl' x x'
          ((Category.assoc _ _ _).symm.trans ((congrArg (· ≫ p) e).trans (Category.assoc _ _ _))) e'
      · rw [Category.assoc, Category.assoc, hY'.1.lift_snd, ← Category.assoc, ← Category.assoc]
        exact e'
  have ef : π ≫ f₀.left ≫ pullback.fst B.A.hom (jK R) = f :=
    (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ pullback.fst B.A.hom (jK R)) hf₀).trans (hY'.1.lift_fst _ _ _))
  obtain ⟨k₁, k₂⟩ := flat_surjective κ
  have h₀ : IsGrpPullback X B.A (jK R) (f₀.left ≫ pullback.fst B.A.hom (jK R)) :=
    isGrpPullback_of_fpqc _ _ _ (jK R) κ B.A X Q π _ k₁ k₂ inferInstance hπ (hf.congr rfl ef.symm)
      (by rw [Category.assoc, hY'.1.w, ← Category.assoc, Over.w f₀])
  obtain ⟨ψ, hψ, eψ⟩ := grpPullback_iso h₀ hY'
  rw [← eψ] at ef
  obtain ⟨Ψ, m, hΨ, l⟩ := polAV_iso_extends_of_isIntegrallyClosed hL hL₂ R B B' ψ hψ
    (lbIso_descend hL.globalFns κ X hX (pull_isLB B'.isLB _) (pull_isLB B.isLB _)
      (LBIso.trans (pull_isLB (pull_isLB B'.isLB _) _) (pull_isLB B'.isLB _) (pull_isLB (pull_isLB B.isLB _) _)
        (lbIso_pull_pull B'.isLB π rfl).symm
        (LBIso.trans (pull_isLB B'.isLB _) (pull_isLB B.isLB _) (pull_isLB (pull_isLB B.isLB _) _) hl'
          (lbIso_pull_pull B.isLB π ef.symm)))) hext
  refine ⟨Ψ, m, l, fun x => Over.OverMorphism.ext ?_⟩
  have w : (g x).left ≫ B'.A.hom = 𝟙 _ ≫ κ ≫ jK R := (Over.w (g x)).trans (Category.id_comp _).symm
  have u₁ := hf'.1.lift_fst _ _ w
  have q : ψ.hom.left ≫ pullback.fst B.A.hom (jK R) = p ≫ Ψ.hom.left := by
    rw [← hΨ]
    exact ExtUnique.pullback_map_left_fst (jK R) Ψ.hom
  rw [← pt x _ u₁ (hf'.1.lift_snd _ _ w), ← ef, q, Over.comp_left]
  exact (congrArg (· ≫ Ψ.hom.left) u₁).symm.trans (by simp only [Category.assoc])
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ThetaPointsAllPrimePowerLevelsOfSingleObject
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex

namespace GlobalTheory.Ex.AllLevels

theorem ser_nested {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Geo.Tor.Level H}
    {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {O' : Type} [CommRing O'] [IsDomain O'] {b : O →+* O'}
    {a : ArcIn D l β O' b} {K : Type} [Field K] [IsAlgClosed K] [Algebra (FractionRing O') K] [Algebra (PowerSeries O') K]
    [FaithfulSMul (PowerSeries O') K] [Algebra.IsAlgebraic (PowerSeries O') K] (S : Ser a K (algebraMap _ K))
    (r m : ℕ) (hr : Odd r) (hm : Odd m) : ∃ c : Kˣ, ∀ x, S.v (r * m) (r • x) = c * S.v m x := by
  obtain ⟨C, _, _, _, _, _, gam, u, h₁, h₂, h₃, h₄⟩ := GlobalTheory.T.exists_complete_algClosed_field_powerSeries_extension O' K
  obtain ⟨A, ρ, -, -, hρ, hv⟩ := S.val C gam u h₁ h₂ h₃ h₄
  have hR : Roots u ρ := ⟨Units.ext ((hρ 1).trans ((congrArg gam S.r_one).trans h₃.symm)), fun n k hn hk => Units.ext (by
    rw [Units.val_pow_eq_pow_val, hρ, hρ, ← map_pow, ← Units.val_pow_eq_pow_val, S.roots.2 n k hn hk])⟩
  obtain ⟨b₁, -, b₃, -, b₅⟩ := GlobalTheory.T.torus_torsion_points_correspond_values O' a.D₀ a.even a.bimult C A.N A.ν
  obtain ⟨q₁, q₂⟩ := GlobalTheory.T.qval_add_of_tower E H D O' a.D₀ a.oa a.even a.bimult C A.I A.N A.ν A.q b₁ b₃
    (fun k => ⟨(b₅ k).1, (b₅ k).2.2⟩) A.hq
  have hrm : Odd (r * m) := hr.mul hm
  choose p hp _ using fun x => existsUnique_twRel A.be u (ρ (m ^ 2)) (hR.pow (pow_pos hm.pos 2)) (A.q _ x)
  choose p' hp' _ using fun x => existsUnique_twRel A.be u (ρ ((r * m) ^ 2)) (hR.pow (pow_pos hrm.pos 2)) (A.q _ x)
  obtain ⟨s, hs⟩ := (hv m hm p hp).1
  obtain ⟨s', hs'⟩ := (hv _ hrm p' hp').1
  have key : ∀ x, gam (S.v (r * m) (r • x)) = (s' * s⁻¹ : Cˣ) * gam (S.v m x) := fun x => by
    rw [hs, hs', GlobalTheory.T.twist_tx_nsmul_eq_of_odd C A.N D.La A.q q₁ q₂ _ A.be u ρ hR r m hr hm x _ _ (hp' _) (hp x), Units.val_mul,
      _root_.mul_assoc, Units.inv_mul_cancel_left]
  by_cases h : ∃ x, S.v m x ≠ 0
  · obtain ⟨x₀, h₀⟩ := h
    have e : gam (S.v (r * m) (r • x₀) / S.v m x₀) = (s' * s⁻¹ : Cˣ) := by
      rw [map_div₀, key, mul_div_cancel_right₀ _ ((map_ne_zero gam).2 h₀)]
    refine ⟨Units.mk0 (S.v (r * m) (r • x₀) / S.v m x₀) fun h => (s' * s⁻¹).ne_zero (by rw [← e, h, map_zero]),
      fun x => gam.injective ?_⟩
    rw [map_mul, Units.val_mk0, e, key]
  · simp only [not_exists, not_not] at h
    exact ⟨1, fun x => gam.injective (by rw [key, h, mul_zero, map_zero, mul_zero])⟩

theorem one_object : HV → Laws6 → GlobalTheory.LN.UDvrSt → GlobalTheory.LN.HomExtSt → ThetaPtDeterminesSt → EndDeterminedOnTorsionSt → ThetaUnifAV → AllA fun {E} _ _ _ {H} {D} {l} {Xo} {c} {W₀} Y {O'} _ _ {b} a => ∀ (K : Type) [Field K] [IsAlgClosed K] [Algebra (FractionRing O') K] [Algebra (PowerSeries O') K] [FaithfulSMul (PowerSeries O') K] [Algebra.IsAlgebraic (PowerSeries O') K], (∀ x, algebraMap (FractionRing O') K (algebraMap O' _ x) = algebraMap (PowerSeries O') K (PowerSeries.C x)) → ∀ (S : Ser a K (algebraMap _ K)) (n : ℕ), n.Prime → Odd n → (∀ j, 2 ≤ j → ∃ o : Full D K, o.ρ = S.A.ρ ∧ o.I.ζ ((n ^ j) ^ 2) = S.A.I.ζ ((n ^ j) ^ 2) ∧ o.Theta (n ^ j) (S.v (n ^ j))) → ∃ o : Full D K, o.ρ = S.A.ρ ∧ ∀ j, o.I.ζ (n ^ j) = S.A.I.ζ (n ^ j) ∧ o.Theta (n ^ j) (S.v (n ^ j)) := by
  intro hV _ _ _ h₁ h₂ _ E _ _ _ H D l Xo c W₀ Y O' _ _ _ b ϖ a _ K _ _ _ _ _ _ _ S n hn ho h
  exact exists_full_all hV.1.1 h₁ h₂ S.A.ρ S.A.I.ζ S.A.I.ζ_pow S.v (ser_nested S) hn ho h

end GlobalTheory.Ex.AllLevels
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.TorsionQuotientActionCompatOfRosatiValuesStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex GlobalTheory.Relabel
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.torsionQuotientAction_compat_of_rosatiValues : GlobalFnsSt → BrGtSt → AllD fun {E} _ _ _ {H} D => letI := H.starRing; ∀ (R R' : Type) [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] [Algebra (FractionRing R') F] (A : ArcF D R F) (D' : DegPre R') [Module (𝓞 E) D'.X] (oa' : D'.OAct (𝓞 E)), D'.PsiEven → D'.TauBimult → ∀ (N' : NumD F) (ν' : NumOf D' F N') (k : ℕ) (β : A.N.Form k) (u : Fˣ) (r : ℕ → Fˣ) (J : NumD.Iso (A.N.twist β u) N'), Roots u r → A.Bal β → (∀ (x : 𝓞 E) y, ν'.eX (J.e (A.act x y)) = x • ν'.eX (J.e y)) → (∀ (x : 𝓞 E) b, J.φ (actV (N := A.N) A.ν A.oa.onB x b) = actV ν' oa'.onB x (J.φ b)) → (∀ a : 𝓞 E, ∃ ρ ρ', RosV A.ν A.oa.onB a ρ ∧ RosV ν' oa'.onB a ρ' ∧ ∀ b b' : A.N.A, ρ' (J.φ b) (J.φ b') * (J.h (actV (N := A.N) A.ν A.oa.onB (star a) b) * J.h b' * J.h (b * actV (N := A.N) A.ν A.oa.onB a b') : Fˣ) = ρ b b' * (J.h (actV (N := A.N) A.ν A.oa.onB (star a) b * b') * J.h b * J.h (actV (N := A.N) A.ν A.oa.onB a b') : Fˣ)) → ActCompat A.ν A.oa ν' oa' β u r J := by
  first | exact @GlobalTheory.Relabel.actCompat_of_rosV | exact GlobalTheory.Relabel.actCompat_of_rosV | (intros; apply GlobalTheory.Relabel.actCompat_of_rosV <;> assumption)
end

