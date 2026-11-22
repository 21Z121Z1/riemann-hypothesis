import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0075
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0006
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2212
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2243
import Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.Bundle0023
import Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.Bundle0020
import Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.Bundle0017
import Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.Bundle0018
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsProjectiveOverRingByChartsAbelianVariety
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0006
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GeometricallyIntegralIffGeometricallyConnectedOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1333
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2545

-- bundled from Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.ExistsCartierWithMultiplicities
section
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.LogPair

private theorem unitAt_of_ord_eq_zero_coheight_one {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X]
    (hufd : ∀ x : X, UniqueFactorizationMonoid (X.presheaf.stalk x)) {v : X}
    (hv : Order.coheight v = 1) {h : X.functionField} (h0 : h ≠ 0)
    (hord : Scheme.ord h v = 0) : UnitAt v h := by
  haveI := hufd v
  haveI : Ring.KrullDimLE 1 (X.presheaf.stalk v) := krullDimLE_of_coheight_le hv.le
  by_cases hF : IsField (X.presheaf.stalk v)
  · obtain ⟨a, b, hb, hab⟩ := IsFractionRing.div_surjective (A := X.presheaf.stalk v) h
    have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
    obtain ⟨b', hbb'⟩ := hF.mul_inv_cancel hb0
    have ha0 : a ≠ 0 := by
      rintro rfl
      apply h0
      rw [← hab, map_zero, zero_div]
    obtain ⟨a', haa'⟩ := hF.mul_inv_cancel ha0
    refine ⟨a * b', ?_, ?_⟩
    · refine isUnit_iff_exists_inv.mpr ⟨a' * b, ?_⟩
      calc a * b' * (a' * b) = (a * a') * (b * b') := by ring
        _ = 1 := by rw [haa', hbb', one_mul]
    · rw [← hab, map_mul]
      have : algebraMap (X.presheaf.stalk v) X.functionField b *
          algebraMap (X.presheaf.stalk v) X.functionField b' = 1 := by
        rw [← map_mul, hbb', map_one]
      rw [eq_div_iff (fun h' => hb0 (IsFractionRing.injective (X.presheaf.stalk v) X.functionField
        (by rw [h', map_zero]))), mul_assoc, mul_comm _ (algebraMap _ _ b), this, mul_one]
  · haveI : IsDiscreteValuationRing (X.presheaf.stalk v) := by
      have hmax : ∀ I : Ideal (X.presheaf.stalk v), I ≠ ⊥ → I.IsPrime → I.IsMaximal :=
        Ring.krullDimLE_one_iff_of_isPrime_bot.mp inferInstance
      have hne : IsLocalRing.maximalIdeal (X.presheaf.stalk v) ≠ ⊥ :=
        IsLocalRing.isField_iff_maximalIdeal_eq.not.mp hF
      have key := (IsDiscreteValuationRing.TFAE (X.presheaf.stalk v) hF).out 3 0
      exact key.mp ⟨inferInstance, ⟨IsLocalRing.maximalIdeal _, ⟨hne, inferInstance⟩,
        fun P hP => IsLocalRing.eq_maximalIdeal (hmax P hP.1 hP.2)⟩⟩
    have h1 : Scheme.ordHom v hv h = 1 := by
      have := (Scheme.ord_eq_iff hv h0 (n := 0)).mp hord
      simpa using this
    have hmem : h ∈ MonoidHom.mker (Ring.ordFrac (X.presheaf.stalk v) (K := X.functionField)) :=
      MonoidHom.mem_mker.mpr h1
    rw [Ring.mker_ordFrac_eq_isUnitSubmonoid] at hmem
    obtain ⟨a, ha, rfl⟩ := hmem
    exact ⟨a, ha, rfl⟩
private theorem Scheme_ord_one {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X] (v : X) :
    Scheme.ord (1 : X.functionField) v = 0 := by
  have h := Scheme.ord_mul (x := v) (one_ne_zero : (1 : X.functionField) ≠ 0) one_ne_zero
  rw [mul_one] at h
  omega

private theorem Scheme_ord_units_zpow {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X]
    (g : (X.functionField)ˣ) (n : ℤ) (v : X) :
    Scheme.ord ((g ^ n : (X.functionField)ˣ) : X.functionField) v =
      n * Scheme.ord (g : X.functionField) v := by
  let φ : (X.functionField)ˣ →* Multiplicative ℤ :=
    { toFun := fun a => Multiplicative.ofAdd (Scheme.ord (a : X.functionField) v)
      map_one' := by simp [Scheme_ord_one]
      map_mul' := fun a b => by
        rw [Units.val_mul, Scheme.ord_mul a.ne_zero b.ne_zero, ofAdd_add] }
  have h := map_zpow φ g n
  have h2 := congrArg Multiplicative.toAdd h
  simpa [φ, toAdd_zpow, smul_eq_mul] using h2

private theorem Scheme_ord_units_inv {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X]
    (g : (X.functionField)ˣ) (v : X) :
    Scheme.ord ((g⁻¹ : (X.functionField)ˣ) : X.functionField) v =
      - Scheme.ord (g : X.functionField) v := by
  have h := Scheme.ord_mul (x := v) g.ne_zero (g⁻¹).ne_zero
  rw [Units.mul_inv, Scheme_ord_one] at h
  omega

private theorem unitAt_of_ord_eq_zero_on_open {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X]
    (hufd : ∀ x : X, UniqueFactorizationMonoid (X.presheaf.stalk x)) {y : X} (U : X.Opens)
    (hy : y ∈ U) (h : (X.functionField)ˣ)
    (hord : ∀ v ∈ U, Scheme.ord (h : X.functionField) v = 0) : UnitAt y (h : X.functionField) := by
  haveI : GlobalTheory.IsNormalScheme X :=
    ⟨fun x => inferInstance, fun x => by haveI := hufd x; infer_instance⟩
  have key : ∀ g : (X.functionField)ˣ, (∀ v ∈ U, Scheme.ord (g : X.functionField) v = 0) →
      RegAt y (g : X.functionField) := by
    intro g hg
    apply regAt_of_forall_coheight_eq_one
    intro z hz hz1
    exact (unitAt_of_ord_eq_zero_coheight_one hufd hz1 g.ne_zero (hg z (hz.mem_open U.isOpen hy))).regAt
  obtain ⟨a, ha⟩ := key h hord
  obtain ⟨b, hb⟩ := key h⁻¹ (fun v hv => by rw [Scheme_ord_units_inv, hord v hv, neg_zero])
  refine ⟨a, ?_, ha⟩
  have hab : algebraMap (X.presheaf.stalk y) X.functionField (a * b) =
      algebraMap (X.presheaf.stalk y) X.functionField 1 := by
    rw [map_mul, ha, hb, map_one, Units.mul_inv]
  exact isUnit_iff_exists_inv.mpr ⟨b, IsFractionRing.injective _ _ hab⟩

private theorem exists_local_unit_ord_eq_finite_sum {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X]
    [DecidableEq X] (hufd : ∀ x : X, UniqueFactorizationMonoid (X.presheaf.stalk x)) (c : X → ℤ)
    (S : Finset X) (hS : ∀ z ∈ S, Order.coheight z = 1) (x : X) :
    ∃ U : X.Opens, x ∈ U ∧ ∃ f : (X.functionField)ˣ, ∀ v ∈ U,
      Scheme.ord (f : X.functionField) v = ∑ z ∈ S, if v = z then c z else 0 := by
  induction S using Finset.induction_on with
  | empty => exact ⟨⊤, trivial, 1, fun v _ => by simp [Scheme_ord_one]⟩
  | insert z S hzS ih =>
    obtain ⟨U1, hx1, f1, hf1⟩ := ih (fun w hw => hS w (Finset.mem_insert_of_mem hw))
    obtain ⟨U2, hx2, π, hπ⟩ := PrimeDivCartier.exists_local_eqn X hufd z
      (hS z (Finset.mem_insert_self z S)) x
    refine ⟨U1 ⊓ U2, ⟨hx1, hx2⟩, f1 * π ^ (c z), fun v hv => ?_⟩
    rw [Finset.sum_insert hzS, Units.val_mul, Scheme.ord_mul f1.ne_zero (π ^ c z).ne_zero,
      Scheme_ord_units_zpow, hf1 v hv.1, hπ v hv.2]
    split_ifs <;> simp [add_comm]

theorem _root_.GlobalTheory.Cartier.CartierDiv.exists_mult_eq_of_locallyFactorial :
    ∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X],
      (∀ x : X, UniqueFactorizationMonoid (X.presheaf.stalk x)) → ∀ c : X → ℤ,
        (Function.support c).Finite → (∀ z, c z ≠ 0 → Order.coheight z = 1) →
          ∃ D : CartierDiv X, ∀ z, D.mult z = c z := by
  intro X _ _ hufd c hfin hc
  classical
  have hS : ∀ z ∈ hfin.toFinset, Order.coheight z = 1 :=
    fun z hz => hc z (hfin.mem_toFinset.mp hz)
  have hsum : ∀ v, (∑ z ∈ hfin.toFinset, if v = z then c z else 0) = c v := by
    intro v
    rw [Finset.sum_ite_eq]
    split_ifs with hv
    · rfl
    · have : c v = 0 := by
        by_contra h'
        exact hv (hfin.mem_toFinset.mpr h')
      exact this.symm
  choose U hxU f hf using fun x => exists_local_unit_ord_eq_finite_sum hufd c hfin.toFinset hS x
  have hmem : (fun x => germOf x (f x)) ∈ cartierGroup X := by
    intro x
    refine ⟨U x, hxU x, f x, fun y hy => ?_⟩
    rw [germOf_eq_iff]
    have hu := unitAt_of_ord_eq_zero_on_open hufd (U x ⊓ U y) ⟨hy, hxU y⟩ (f x * (f y)⁻¹)
      (fun v hv => by
        rw [Units.val_mul, Scheme.ord_mul (f x).ne_zero ((f y)⁻¹).ne_zero, Scheme_ord_units_inv,
          hf x v hv.1, hf y v hv.2, add_neg_cancel])
    simpa [div_eq_mul_inv] using hu
  let D : CartierDiv X := (⟨fun x => germOf x (f x), hmem⟩ : cartierGroup X)
  refine ⟨D, fun z => ?_⟩
  have he : D.IsEqn z (f z) := rfl
  rw [he.mult_eq, hf z z (hxU z), hsum]
end

-- bundled from Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.ExistsPrimeDivisorsSncBoundary
section
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.LogPair

set_option autoImplicit false

namespace GlobalTheory.SncComp

variable {Y : Scheme.{0}}

theorem notMem_basicOpen_of_mem_vanishingIdeal (B : Closeds Y) (U : Y.affineOpens) {a : Γ(Y, U.1)}
    (ha : a ∈ (Scheme.IdealSheafData.vanishingIdeal B).ideal U) {y : Y} (hyU : y ∈ U.1)
    (hyB : y ∈ B) : y ∉ Y.basicOpen a := by
  have h1 := (Scheme.IdealSheafData.mem_support_iff_of_mem
    (I := Scheme.IdealSheafData.vanishingIdeal B) hyU).1 (by
      rw [← SetLike.mem_coe]; simpa using hyB)
  exact (Scheme.mem_zeroLocus_iff _ _ _).1 h1 a ha

theorem exists_notMem_basicOpen_of_prod {U : Y.Opens} {ι : Type} (J : Finset ι) (f : ι → Γ(Y, U))
    {y : Y} (hy : y ∈ U) (h : y ∉ Y.basicOpen (∏ i ∈ J, f i)) : ∃ i ∈ J, y ∉ Y.basicOpen (f i) := by
  classical
  induction J using Finset.induction_on with
  | empty =>
    rw [Finset.prod_empty, Scheme.basicOpen_of_isUnit _ isUnit_one] at h
    exact (h hy).elim
  | insert a J ha ih =>
    rw [Finset.prod_insert ha, Scheme.basicOpen_mul] at h
    by_cases h' : y ∈ Y.basicOpen (f a)
    · obtain ⟨i, hi, hi'⟩ := ih fun h'' => h ⟨h', h''⟩
      exact ⟨i, Finset.mem_insert_of_mem hi, hi'⟩
    · exact ⟨a, Finset.mem_insert_self a J, h'⟩

end GlobalTheory.SncComp

namespace GlobalTheory.SncComp

variable {Y : Scheme.{0}}

theorem ne_top_of_snc [IsIntegral Y] (B : Closeds Y)
    (hB : FinalTheorems.Snc (Scheme.IdealSheafData.vanishingIdeal B)) : B ≠ ⊤ := by
  intro hBt
  obtain ⟨-, U, hU, m, f, J, hrsp, hid⟩ := hB (genericPoint Y)
  have hm : m = 0 := by
    have h := hrsp.2
    have h0 : ringKrullDim Y.functionField = 0 := ringKrullDim_eq_zero_of_field Y.functionField
    rw [show ringKrullDim (Y.presheaf.stalk (genericPoint Y)) = ringKrullDim Y.functionField from rfl,
      h0] at h
    exact_mod_cast h
  subst hm
  have hJ : J = ∅ := Finset.eq_empty_of_isEmpty J
  subst hJ
  rw [Finset.prod_empty] at hid
  have h1 := notMem_basicOpen_of_mem_vanishingIdeal B U (a := 1)
    (hid ▸ Ideal.mem_span_singleton_self _) hU (by rw [hBt]; trivial)
  exact h1 (by rw [Scheme.basicOpen_of_isUnit _ isUnit_one]; exact hU)

variable [IsIntegral Y]

theorem exists_chart_germ_eq {D : CartierDiv Y} {σ : (toLB D).Sec}
    (hσ : (presents_toLB D).rat σ = 1) {x : Y} {g : Y.functionFieldˣ} (h : D.IsEqn x g) :
    ∃ (c : (toLB D).ι) (hc : x ∈ (toLB D).U c), algebraMap (Y.presheaf.stalk x) Y.functionField
      ((Y.presheaf.germ _ x hc).hom (σ.f c)) = g := by
  obtain ⟨V, hxV, hV⟩ := h.exists_nhds
  let c : (toLB D).ι := ⟨(V, g), gen_mem hxV, hV⟩
  refine ⟨c, hxV, ?_⟩
  have e := (presents_toLB D).rat_mul σ c (gen_mem hxV)
  rw [hσ, one_mul] at e
  exact (algebraMap_germ (X := Y) (U := V) hxV (σ.f c)).trans e.symm

end GlobalTheory.SncComp

namespace GlobalTheory.SncComp

variable {Y : Scheme.{0}} [IsIntegral Y] [IsLocallyNoetherian Y]

theorem exists_local_data [GlobalTheory.IsNormalScheme Y] (B : Closeds Y)
    (hB : FinalTheorems.Snc (Scheme.IdealSheafData.vanishingIdeal B)) {s : ℕ} (w : Fin s → Y)
    (hw : Function.Injective w) (hw1 : ∀ i, Order.coheight (w i) = 1) (hwB : ∀ i, w i ∈ B)
    (D : Fin s → CartierDiv Y) (hmult : ∀ i, (D i).mult (w i) = 1 ∧ ∀ v, v ≠ w i → (D i).mult v = 0)
    (σ : ∀ i, (toLB (D i)).Sec) (hσ : ∀ i, (presents_toLB (D i)).rat (σ i) = 1) (x : Y) :
    ∃ (n : ℕ) (t : Fin n → Y.presheaf.stalk x) (c : ∀ i, (toLB (D i)).ι)
      (hc : ∀ i, x ∈ (toLB (D i)).U (c i)) (e : Fin s → Option (Fin n)),
      FinalTheorems.Rsp (Y.presheaf.stalk x) n t ∧ (∀ i j a, e i = some a → e j = some a → i = j) ∧
        ∀ i, Associated ((Y.presheaf.germ _ x (hc i)).hom ((σ i).f (c i))) ((e i).elim 1 t) := by
  classical
  obtain ⟨hreg, U, hxU, m, f, J, hrsp, hid⟩ := hB x
  obtain ⟨w₀, u, hw₀, hu⟩ := GlobalTheory.T.regular_sequence_prime_divisors Y x U.1 hxU m f hreg hrsp
  let t : Fin m → Y.presheaf.stalk x := fun j => Y.presheaf.germ U.1 x hxU (f j)
  let e : Fin s → Option (Fin m) := fun i =>
    if h : ∃ j, j ∈ J ∧ w i = w₀ j then some h.choose else none
  have he : ∀ i a, e i = some a → w i = w₀ a := by
    intro i a h
    simp only [e] at h
    split_ifs at h with h'
    cases h
    exact h'.choose_spec.2
  have key : ∀ i, ∃ g : Y.functionFieldˣ, (D i).IsEqn x g ∧
      algebraMap (Y.presheaf.stalk x) Y.functionField ((e i).elim 1 t) = g := by
    intro i
    by_cases h : ∃ j, j ∈ J ∧ w i = w₀ j
    · obtain ⟨j, hei, hwj⟩ : ∃ j, e i = some j ∧ w i = w₀ j := ⟨h.choose, dif_pos h, h.choose_spec.2⟩
      obtain ⟨hu1, -, -, -, hord, hoth⟩ := hu j
      refine ⟨u j, ?_, ?_⟩
      · refine (GlobalTheory.T.cartier_divisor_mult_characterize Y (D i)).2.2.2 x (u j) fun z hz => ?_
        by_cases hzw : z = w i
        · rw [hzw, (hmult i).1, hwj, hord]
        · rw [(hmult i).2 z hzw]
          by_cases hz1 : Order.coheight z = 1
          · have hzb := hoth z hz hz1 (hwj ▸ hzw)
            have hzU : z ∈ U.1 := hz.mem_open U.1.isOpen hxU
            rw [hu1]
            exact ((unitAt_fnOf_iff hzU _ _).2 hzb).ord_eq_zero
          · exact Scheme.ord_eq_zero_of_coheight_neq_one hz1 _
      · rw [hei, hu1]
        exact algebraMap_germ hxU (f j)
    · have hei : e i = none := dif_neg h
      refine ⟨1, ?_, by rw [hei]; simp⟩
      refine (GlobalTheory.T.cartier_divisor_mult_characterize Y (D i)).2.2.2 x 1 fun z hz => ?_
      rw [(hmult i).2 z ?_, Units.val_one, (unitAt_one z).ord_eq_zero]
      rintro rfl
      have hzU : w i ∈ U.1 := hz.mem_open U.1.isOpen hxU
      have h0 : w i ∉ Y.basicOpen (∏ j ∈ J, f j) := notMem_basicOpen_of_mem_vanishingIdeal B U
        (hid ▸ Ideal.mem_span_singleton_self _) hzU (hwB i)
      obtain ⟨j, hj, hjb⟩ := exists_notMem_basicOpen_of_prod J f hzU h0
      refine h ⟨j, hj, ?_⟩
      by_contra hne
      exact hjb ((hu j).2.2.2.2.2 (w i) hz (hw1 i) hne)
  choose g hg hga using key
  choose c hc hcg using fun i => exists_chart_germ_eq (hσ i) (hg i)
  refine ⟨m, t, c, hc, e, hrsp, fun i i' a hi hi' => hw ((he i a hi).trans (he i' a hi').symm),
    fun i => ?_⟩
  have : (Y.presheaf.germ _ x (hc i)).hom ((σ i).f (c i)) = (e i).elim 1 t :=
    IsFractionRing.injective (Y.presheaf.stalk x) Y.functionField ((hcg i).trans (hga i).symm)
  rw [this]

end GlobalTheory.SncComp

namespace GlobalTheory.SncComp

theorem relSnc_components : ∀ (k : Type) [Field k] [CharZero k] (Y : Scheme.{0}) [IsIntegral Y]
    [IsLocallyNoetherian Y] (q : Y ⟶ Sp k) (n : ℕ) [SmoothOfRelativeDimension n q], IsProjOver q →
    ∀ B : Closeds Y, FinalTheorems.Snc (Scheme.IdealSheafData.vanishingIdeal B) →
      ∃ (r : ℕ) (w : Fin r → Y) (D : Fin r → CartierDiv Y) (σ : ∀ i, (toLB (D i)).Sec),
        Function.Injective w ∧ (∀ i, (D i).mult (w i) = 1 ∧ ∀ v, v ≠ w i → (D i).mult v = 0) ∧
        (∀ v, Order.coheight v = 1 → v ∈ B → ∃ i, v = w i) ∧
        RelSnc q n (fun i => toLB (D i)) σ := by
  intro k _ _ Y _ _ q n _ hP B hB
  classical
  have : Smooth q := SmoothOfRelativeDimension.smooth n q
  have : GlobalTheory.IsNormalScheme Y := isNormalScheme_of_smooth q
  have : IsNoetherian Y := by
    obtain ⟨N, i, hi, e⟩ := hP
    have := isProper_str k N
    have : QuasiCompact q := e ▸ inferInstance
    have := QuasiCompact.compactSpace_of_compactSpace q
    exact {}
  have hfin := GlobalTheory.T.finite_codim_one_points_closed Y B (ne_top_of_snc B hB)
  let S := hfin.toFinset
  let w : Fin S.card → Y := fun i => (S.equivFin.symm i).1
  have hw : Function.Injective w := fun i j h => S.equivFin.symm.injective (Subtype.ext h)
  have hwS : ∀ i, Order.coheight (w i) = 1 ∧ w i ∈ B := fun i =>
    hfin.mem_toFinset.1 (S.equivFin.symm i).2
  have hSw : ∀ v, Order.coheight v = 1 → v ∈ B → ∃ i, v = w i := fun v h1 h2 =>
    ⟨S.equivFin ⟨v, hfin.mem_toFinset.2 ⟨h1, h2⟩⟩, by simp [w]⟩
  have hufd : ∀ x : Y, UniqueFactorizationMonoid (Y.presheaf.stalk x) :=
    AbelianProjective.ufd_stalk q
  choose D hD using fun i => GlobalTheory.T.exists_prime_cartier_divisor Y hufd (w i) (hwS i).1
  have heff : ∀ i, (D i).Eff := fun i => ((GlobalTheory.T.cartier_divisor_mult_characterize Y (D i)).1).2 fun z => by
    by_cases hz : z = w i
    · rw [hz, (hD i).1]; norm_num
    · rw [(hD i).2 z hz]
  choose σ hσ using fun i => (presents_toLB (D i)).exists_rat_eq (CartierDiv.mem_sections.2 (heff i))
  refine ⟨S.card, w, D, σ, hw, hD, hSw, ?_⟩
  refine GlobalTheory.T.regular_sequence_stalk_snc k Y q n S.card (fun i => toLB (D i)) σ (fun i => isLB_toLB _) fun x _ => ?_
  exact exists_local_data B hB w hw (fun i => (hwS i).1) (fun i => (hwS i).2) D hD σ hσ x

end GlobalTheory.SncComp
end

-- bundled from Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.KltOfSncCoefficients
section
set_option autoImplicit false

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.LogPair

namespace GlobalTheory.Discrepancy

noncomputable def DivOver.ordHom {k : Type} [Field k] {X : Scheme.{0}} [IsIntegral X] {p : X ⟶ Sp k}
    (E : DivOver p) : X.functionFieldˣ →* Multiplicative ℤ where
  toFun f := Multiplicative.ofAdd (E.ord f)
  map_one' := by simp
  map_mul' f g := by simp [E.ord_mul]

theorem DivOver.ord_prod_zpow {k : Type} [Field k] {X : Scheme.{0}} [IsIntegral X] {p : X ⟶ Sp k}
    (E : DivOver p) {ι : Type} (s : Finset ι) (f : ι → X.functionFieldˣ) (e : ι → ℤ) :
    E.ord (∏ j ∈ s, f j ^ e j) = ∑ j ∈ s, e j * E.ord (f j) := by
  have h := congrArg Multiplicative.toAdd (map_prod E.ordHom (fun j => f j ^ e j) s)
  rw [toAdd_prod] at h
  calc E.ord (∏ j ∈ s, f j ^ e j) = Multiplicative.toAdd (E.ordHom (∏ j ∈ s, f j ^ e j)) := rfl
    _ = ∑ j ∈ s, Multiplicative.toAdd (E.ordHom (f j ^ e j)) := h
    _ = ∑ j ∈ s, e j * E.ord (f j) := by
      refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [map_zpow, toAdd_zpow, smul_eq_mul]
      rfl

theorem DivOver.ord_eq_zero_of_unitAt {k : Type} [Field k] {X : Scheme.{0}} [IsIntegral X]
    {p : X ⟶ Sp k} {E : DivOver p} {x : X} (hE : E.Through x) (v : X.functionFieldˣ)
    (hv : UnitAt x (v : X.functionField)) : E.ord v = 0 := by
  obtain ⟨a, ha, hav⟩ := hv
  have h1 : (v : X.functionField) ∈ E.ring := hE _ ⟨a, hav⟩
  have hinv : algebraMap (X.presheaf.stalk x) X.functionField (↑(ha.unit⁻¹)) =
      ((v⁻¹ : X.functionFieldˣ) : X.functionField) := by
    rw [Units.val_inv_eq_inv_val]
    refine eq_inv_of_mul_eq_one_right ?_
    rw [← hav, ← map_mul, IsUnit.mul_val_inv, map_one]
  have h2 : ((v⁻¹ : X.functionFieldˣ) : X.functionField) ∈ E.ring := hE _ ⟨_, hinv⟩
  have e1 := (E.ord_nonneg_iff v).mpr h1
  have e2 := (E.ord_nonneg_iff v⁻¹).mpr h2
  rw [E.ord_inv] at e2
  omega

theorem coeff_criterion_snc : ∀ (k : Type) [Field k] [CharZero k] (Y : Scheme.{0}) [IsIntegral Y] [IsLocallyNoetherian Y] (q : Y ⟶ Sp k) (n : ℕ) [SmoothOfRelativeDimension n q] (η : RatForms q n), η ≠ 0 → ∀ (K G : CartierDiv Y) (m : ℕ) (B : Closeds Y), 0 < m → IsDivOfForm K η → FinalTheorems.Snc (Scheme.IdealSheafData.vanishingIdeal B) → (G - m • K).supp ≤ B → ∀ (y : Y) (g : Y.functionFieldˣ), G.IsEqn y g → ∀ E : DivOver q, E.Through y → ((∀ w, w ⤳ y → (G - m • K).mult w < m) → -1 < discrep E η m g) ∧ ((∀ w, w ⤳ y → (G - m • K).mult w ≤ m) → -1 ≤ discrep E η m g) := by
  intro k _ _ Y _ _ q n _ η hη K G m B hm hK hsnc hsupp y g hG E hE
  haveI : Smooth q := SmoothOfRelativeDimension.smooth n q
  have hdim : topologicalKrullDim Y = n :=
    HSCore.VanishNumberField.topologicalKrullDim_eq_of_smooth q n inferInstance
  obtain ⟨U, hy, z, J, w, u, hc⟩ := exists_isSncChart k Y q n B hsnc y
  have hgen : genericPoint Y ∈ U :=
    ((genericPoint_spec Y).mem_open_set_iff U.isOpen).mpr ⟨y, trivial, hy⟩
  have hfg := isFreeGen_formOf hgen hc.frame
  have hω0 : formOf U hgen (dOn q z) ≠ 0 := by
    intro h0
    have := hfg.1 (a₁ := 0) (a₂ := 1) (by simp only [h0, smul_zero])
    exact zero_ne_one this
  have hr : hfg.repr η ≠ 0 := by
    intro h0
    apply hη
    rw [← hfg.repr_smul η, h0, zero_smul]
  have hηh : η = ((Units.mk0 _ hr : Y.functionFieldˣ) : Y.functionField) • formOf U hgen (dOn q z) :=
    (hfg.repr_smul η).symm
  set h : Y.functionFieldˣ := Units.mk0 _ hr with hdef
  have hKy : K.IsEqn y h := hK U (dOn q z) hc.frame y hy h hηh
  have hD1 : (G - m • K).IsEqn y (g / h ^ m) := hG.sub (hKy.nsmul m)
  have hD2 := IsSncChart.isEqn_monomial k Y q n B y U hy z J w u hc (G - m • K) hsupp
  have hunit := (hD1.iff_unitAt).mp hD2
  have hzero := DivOver.ord_eq_zero_of_unitAt hE
    ((∏ j ∈ J, u j ^ (G - m • K).mult (w j)) / (g / h ^ m)) (by simpa using hunit)
  rw [div_eq_mul_inv, E.ord_mul, E.ord_inv, div_eq_mul_inv, E.ord_mul, E.ord_inv,
    DivOver.ord_prod_zpow, E.ord_pow] at hzero
  have hform : E.formOrd η = E.ord h + E.formOrd (formOf U hgen (dOn q z)) := by
    rw [hηh]
    exact E.formOrd_smul hdim hω0 h
  have hF0 : 0 ≤ E.formOrd (formOf U hgen (dOn q z)) :=
    E.formOrd_formOf_nonneg hdim hy hE (dOn q z) hω0
  have hF1 := E.sum_ord_sub_one_le_formOrd_dOn hdim hy hE z hω0 (J := ↥J) (fun j => j.1)
    Subtype.val_injective (fun j => u j.1) (fun j => hc.val j.1 j.2)
  rw [Finset.sum_coe_sort J (fun j => E.ord (u j))] at hF1
  have hnn : ∀ j ∈ J, 0 ≤ E.ord (u j) := fun j hj =>
    (E.ord_nonneg_iff _).mpr (hE _ (by rw [hc.val j hj]; exact regAt_fnOf hy _ _))
  set F := E.formOrd (formOf U hgen (dOn q z)) with hFdef
  set S := ∑ j ∈ J, E.ord (u j) with hSdef
  set T := ∑ j ∈ J, (G - m • K).mult (w j) * E.ord (u j) with hTdef
  have hm' : (0 : ℚ) < m := by exact_mod_cast hm
  have hdisc : discrep E η m g = ((m * F - T : ℤ) : ℚ) / m := by
    have hg' : E.ord g = m * E.ord h + T := by linarith
    unfold discrep
    rw [hform, hg']
    push_cast
    field_simp
    ring
  rw [hdisc]
  constructor
  · intro hlt
    have hT : T ≤ (m - 1) * S := by
      rw [hSdef, hTdef, Finset.mul_sum]
      refine Finset.sum_le_sum (fun j hj => ?_)
      have := hlt (w j) (hc.spec j hj)
      exact mul_le_mul_of_nonneg_right (by omega) (hnn j hj)
    have hS0 : 0 ≤ S := Finset.sum_nonneg hnn
    have key : -(m : ℤ) < m * F - T := by
      rcases eq_or_lt_of_le hS0 with hS | hS
      · rw [← hS] at hT
        have : (m : ℤ) * F ≥ 0 := mul_nonneg (by exact_mod_cast hm.le) hF0
        have hm0 : (0 : ℤ) < m := by exact_mod_cast hm
        linarith
      · have : (m : ℤ) * (S - 1) ≤ m * F :=
          mul_le_mul_of_nonneg_left (by linarith) (by exact_mod_cast hm.le)
        nlinarith
    rw [lt_div_iff₀ hm']
    have : ((-(m : ℤ) : ℤ) : ℚ) < ((m * F - T : ℤ) : ℚ) := by exact_mod_cast key
    push_cast at this ⊢
    linarith
  · intro hle
    have hT : T ≤ m * S := by
      rw [hSdef, hTdef, Finset.mul_sum]
      refine Finset.sum_le_sum (fun j hj => ?_)
      exact mul_le_mul_of_nonneg_right (hle (w j) (hc.spec j hj)) (hnn j hj)
    have key : -(m : ℤ) ≤ m * F - T := by
      have : (m : ℤ) * (S - 1) ≤ m * F :=
        mul_le_mul_of_nonneg_left (by linarith) (by exact_mod_cast hm.le)
      nlinarith
    rw [le_div_iff₀ hm']
    have : ((-(m : ℤ) : ℤ) : ℚ) ≤ ((m * F - T : ℤ) : ℚ) := by exact_mod_cast key
    push_cast at this ⊢
    linarith

end GlobalTheory.Discrepancy
end

