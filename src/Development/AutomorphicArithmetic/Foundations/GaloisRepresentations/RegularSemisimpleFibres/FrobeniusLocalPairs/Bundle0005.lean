import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.FrobeniusLocalPairs.Bundle0004
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.OrbitalIntegrals.Bundle0001
import Development.AutomorphicArithmetic.Foundations.Convolution.TwistedLocalOrbits.Bundle0003
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.OrbitalIntegrals.TwistedOrbitalIntegrals.ExtCont
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.OrbitalIntegrals.TwistedOrbitalIntegrals.Bundle0001
import Development.AutomorphicArithmetic.Foundations.Convolution.TwistedLocalOrbits.Bundle0001

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.FrobeniusLocalPairs.CosetSum
section
open MeasureTheory PositivityTheory.Rg.Tf.Loc

private theorem exists_reps {G ι : Type} [Group G] (H U : Subgroup G) (R : Finset ι) (x : ι → G)
    (hd : ∀ i ∈ R, ∀ j ∈ R, (∃ h ∈ H, ∃ u ∈ U, x i = h * x j * u) → i = j) :
    ∃ r : G → G, (∀ g, ∃ h ∈ H, ∃ u ∈ U, g = h * r g * u) ∧ (∀ g, ∀ h ∈ H, ∀ u ∈ U, r (h * g * u) = r g) ∧
      ∀ i ∈ R, r (x i) = x i := by
  classical
  let S : Setoid G :=
    { r := fun g g' => ∃ h ∈ H, ∃ u ∈ U, g = h * g' * u
      iseqv :=
        { refl := fun g => ⟨1, H.one_mem, 1, U.one_mem, by simp⟩
          symm := by
            rintro g g' ⟨h, hh, u, hu, rfl⟩
            exact ⟨h⁻¹, H.inv_mem hh, u⁻¹, U.inv_mem hu, by group⟩
          trans := by
            rintro g g' g'' ⟨h₁, hh₁, u₁, hu₁, rfl⟩ ⟨h₂, hh₂, u₂, hu₂, rfl⟩
            exact ⟨h₁ * h₂, H.mul_mem hh₁ hh₂, u₂ * u₁, U.mul_mem hu₂ hu₁, by group⟩ } }
  let f : Quotient S → G := fun q =>
    if hq : ∃ i ∈ R, Quotient.mk S (x i) = q then x hq.choose else q.out
  have hf : ∀ g, S.r g (f (Quotient.mk S g)) := by
    intro g
    by_cases hq : ∃ i ∈ R, Quotient.mk S (x i) = Quotient.mk S g
    · simp only [f, dif_pos hq]
      exact Quotient.exact (hq.choose_spec.2.symm)
    · simp only [f, dif_neg hq]
      exact Quotient.exact (Quotient.out_eq (Quotient.mk S g)).symm
  refine ⟨fun g => f (Quotient.mk S g), hf, ?_, ?_⟩
  · intro g h hh u hu
    have : Quotient.mk S (h * g * u) = Quotient.mk S g := Quotient.sound ⟨h, hh, u, hu, rfl⟩
    simp only [this]
  · intro i hi
    have hq : ∃ j ∈ R, Quotient.mk S (x j) = Quotient.mk S (x i) := ⟨i, hi, rfl⟩
    simp only [f, dif_pos hq]
    rw [hd _ hq.choose_spec.1 i hi (Quotient.exact hq.choose_spec.2)]

theorem UpperTheory.Gal.InertialTypesAlt.L.cosetSum :
    UpperTheory.Gal.InertialTypesAlt.L.CosetSum := by
  intro G _ _ _ _ _ _ _ _ μ hμ K H hKo hKc hHc hcomm ν hν ι R x V S hV hS hd
  classical
  haveI : SFinite μ := inferInstance
  haveI : LocallyCompactSpace H := hHc.locallyCompactSpace
  haveI : SFinite ν := inferInstance
  letI cH : CommGroup H :=
    { (inferInstance : Group H) with mul_comm := fun a b => Subtype.ext (hcomm a a.2 b b.2) }
  haveI : ν.IsInvInvariant := @Measure.IsHaarMeasure.isInvInvariant_of_regular H cH _ _ _ _ ν hν _ _
  obtain ⟨rep, hrep, hinv, hfix⟩ := exists_reps H K R x hd
  let W : G → Set H := fun y => {h | y⁻¹ * (h : G) * y ∈ K}
  have hWcont : ∀ y : G, Continuous fun h : H => y⁻¹ * (h : G) * y := fun y => by fun_prop
  have hWopen : ∀ y, IsOpen (W y) := fun y => hKo.preimage (hWcont y)
  have hWpos : ∀ y, ν (W y) ≠ 0 := fun y =>
    ((hWopen y).measure_pos ν ⟨1, by simp [W, K.one_mem]⟩).ne'
  have hWfin : ∀ y, ν (W y) ≠ ⊤ := by
    intro y
    have hc : IsCompact (W y) := by
      have e : W y = Subtype.val ⁻¹' ((fun k => y * k * y⁻¹) '' (K : Set G)) := by
        ext h
        simp only [W, Set.mem_setOf_eq, Set.mem_preimage, Set.mem_image]
        constructor
        · intro hk
          exact ⟨_, hk, by group⟩
        · rintro ⟨k, hk, hk'⟩
          rw [← hk']
          have e2 : y⁻¹ * (y * k * y⁻¹) * y = k := by group
          rw [e2]
          exact hk
      rw [e]
      exact hHc.isClosedEmbedding_subtypeVal.isCompact_preimage (hKc.image (by fun_prop))
    exact hc.measure_lt_top.ne
  have hrepK : ∀ g, ∀ k ∈ K, rep (g * k) = rep g := fun g k hk => by
    simpa using hinv g 1 H.one_mem k hk
  have hrepH : ∀ g, ∀ h ∈ H, rep (h * g) = rep g := fun g h hh => by
    simpa using hinv g h hh 1 K.one_mem
  let ρ : G → ENNReal := fun g => if (rep g)⁻¹ * g ∈ K then (ν (W (rep g)))⁻¹ else 0
  have hρK : ∀ g, ∀ k ∈ K, ρ (g * k) = ρ g := by
    intro g k hk
    simp only [ρ, hrepK g k hk, ← mul_assoc, K.mul_mem_cancel_right hk]
  have hρm : Measurable ρ := by
    have : IsLocallyConstant ρ := by
      rw [IsLocallyConstant.iff_eventually_eq]
      intro g
      have ho : IsOpen ((fun z => g⁻¹ * z) ⁻¹' (K : Set G)) := hKo.preimage (by fun_prop)
      filter_upwards [ho.mem_nhds (by simp [K.one_mem])] with z hz
      have : z = g * (g⁻¹ * z) := by group
      rw [this, hρK g _ hz]
    exact this.continuous.measurable
  have hρn : IsQuotNormaliser H ν ρ := by
    refine ⟨hρm, fun g => ?_⟩
    obtain ⟨h0, hh0, k0, hk0, hg⟩ := hrep g
    set y := rep g with hy
    have key : ∀ h : H, ρ (↑h * g) = (W y).indicator (fun _ => (ν (W y))⁻¹) (⟨h0, hh0⟩ * h) := by
      intro h
      have hr : rep (↑h * g) = y := hrepH g h h.2
      simp only [ρ, hr, Set.indicator, W, Set.mem_setOf_eq]
      have e : y⁻¹ * (↑h * g) = (y⁻¹ * ↑(⟨h0, hh0⟩ * h : H) * y) * k0 := by
        rw [hg]
        simp only [Subgroup.coe_mul]
        rw [(hcomm h0 hh0 h h.2).eq]
        group
      rw [e, K.mul_mem_cancel_right hk0]
    simp_rw [key]
    rw [lintegral_indicator_const_comp (measurable_const_mul _) (hWopen y).measurableSet]
    rw [measure_preimage_mul, ENNReal.inv_mul_cancel (hWpos y) (hWfin y)]
  rcases R.eq_empty_or_nonempty with hR | ⟨i0, hi0⟩
  · have hS0 : S = ∅ := by
      ext g
      simp [hS g, hR]
    simp [quotIntegral, hS0, hR]
  have hWV : ∀ i ∈ R, W (x i) = V := by
    intro i hi
    ext h
    exact (hV i hi h).symm
  have hV0 : ν V ≠ 0 := hWV i0 hi0 ▸ hWpos (x i0)
  have hVt : ν V ≠ ⊤ := hWV i0 hi0 ▸ hWfin (x i0)
  have hSK : ∀ g, ∀ k ∈ K, g ∈ S → g * k ∈ S := by
    intro g k hk hg
    obtain ⟨i, hi, h, hh, κ, hκ, rfl⟩ := (hS _).1 hg
    exact (hS _).2 ⟨i, hi, h, hh, κ * k, K.mul_mem hκ hk, by group⟩
  have hSH : ∀ g, ∀ h ∈ H, h * g ∈ S ↔ g ∈ S := by
    intro g h hh
    constructor
    · intro hg
      obtain ⟨i, hi, h', hh', κ, hκ, e⟩ := (hS _).1 hg
      refine (hS _).2 ⟨i, hi, h⁻¹ * h', H.mul_mem (H.inv_mem hh) hh', κ, hκ, ?_⟩
      rw [mul_assoc (h⁻¹ * h'), mul_assoc h⁻¹, ← mul_assoc h', ← e]
      group
    · intro hg
      obtain ⟨i, hi, h', hh', κ, hκ, rfl⟩ := (hS _).1 hg
      exact (hS _).2 ⟨i, hi, h * h', H.mul_mem hh hh', κ, hκ, by group⟩
  have hSo : IsOpen S := by
    rw [isOpen_iff_forall_mem_open]
    intro g hg
    refine ⟨(fun z => g⁻¹ * z) ⁻¹' (K : Set G), ?_, hKo.preimage (by fun_prop), by simp [K.one_mem]⟩
    intro z hz
    have : z = g * (g⁻¹ * z) := by group
    rw [this]
    exact hSK g _ hz hg
  let F : G → ENNReal := S.indicator 1
  have hFm : Measurable F := measurable_one.indicator hSo.measurableSet
  have hFH : ∀ h ∈ H, ∀ g, F (h * g) = F g := by
    intro h hh g
    by_cases hg : g ∈ S
    · simp [F, hg, (hSH g h hh).2 hg]
    · simp [F, hg, mt (hSH g h hh).1 hg]
  have hex : ∃ ρ, IsQuotNormaliser H ν ρ := ⟨ρ, hρn⟩
  have hswap := lintegral_normaliser_eq (μG := μ) hFm hFH hex.choose_spec hρn
  have hpt : ∀ g, F g * ρ g =
      ∑ i ∈ R, ((fun z => (x i)⁻¹ * z) ⁻¹' (K : Set G)).indicator (fun _ => (ν V)⁻¹) g := by
    intro g
    by_cases hg : g ∈ S
    · obtain ⟨i, hi, h, hh, κ, hκ, rfl⟩ := (hS _).1 hg
      have hr : rep (h * x i * κ) = x i := by rw [hinv _ h hh κ hκ, hfix i hi]
      rw [Finset.sum_eq_single_of_mem i hi]
      · simp [F, Set.indicator_of_mem hg, ρ, hr, hWV i hi, Set.indicator]
      · intro j hj hji
        rw [Set.indicator_of_notMem]
        intro hm
        apply hji
        refine hd j hj i hi ⟨h, hh, κ * ((x j)⁻¹ * (h * x i * κ))⁻¹, K.mul_mem hκ (K.inv_mem hm), ?_⟩
        group
    · have hF0 : F g = 0 := Set.indicator_of_notMem hg _
      rw [hF0, zero_mul]
      symm
      apply Finset.sum_eq_zero
      intro i hi
      rw [Set.indicator_of_notMem]
      intro hm
      apply hg
      exact (hS _).2 ⟨i, hi, 1, H.one_mem, (x i)⁻¹ * g, hm, by group⟩
  have hcomp : ∫⁻ g, F g * ρ g ∂μ = R.card * ((ν V)⁻¹ * μ K) := by
    rw [lintegral_congr (fun g => hpt g), lintegral_finset_sum]
    · simp_rw [lintegral_indicator_const (hKo.measurableSet.preimage (measurable_const_mul _)),
        measure_preimage_mul]
      rw [Finset.sum_const, nsmul_eq_mul]
    · intro i _
      exact measurable_const.indicator (hKo.measurableSet.preimage (measurable_const_mul _))
  have hI : ∫⁻ g, F g * hex.choose g ∂μ = R.card * ((ν V)⁻¹ * μ K) := hswap.trans hcomp
  have hfin : (R.card : ENNReal) * ((ν V)⁻¹ * μ K) ≠ ⊤ :=
    ENNReal.mul_ne_top (ENNReal.natCast_ne_top _)
      (ENNReal.mul_ne_top (ENNReal.inv_ne_top.2 hV0) hKc.measure_lt_top.ne)
  have hpt2 : ∀ g, (S.indicator 1 g : ℂ) * (((hex.choose g).toReal : ℝ) : ℂ)
      = (((F g * hex.choose g).toReal : ℝ) : ℂ) := by
    intro g
    by_cases hg : g ∈ S <;> simp [F, hg]
  unfold quotIntegral
  rw [dif_pos hex]
  simp_rw [hpt2]
  have hm2 : Measurable fun g => F g * hex.choose g := hFm.mul hex.choose_spec.1
  rw [integral_complex_ofReal, integral_toReal hm2.aemeasurable (ae_lt_top hm2 (hI ▸ hfin)), hI]
  congr 1
  rw [ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_natCast,
    measureReal_def, measureReal_def]
  ring
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.FrobeniusLocalPairs.ElemLocOf
section
noncomputable section

open MeasureTheory NumberField IsDedekindDomain ValuativeRel Matrix GroundTheory.Global GroundTheory.Global.SemiLocal
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets PositivityTheory.Rg.Tf.Loc UpperTheory.ConvolutionTheory.Loc
open GlobalTheory.SmGL hiding iwahori
open PositivityTheory.Rg.Tf.Geo (incFin galFin)
open UpperTheory.V.Published UpperTheory.CBC
open scoped Classical

namespace UpperTheory.Gal.InertialTypesAlt.L

private theorem quot_smul {G : Type} [Group G] [MeasurableSpace G] (μ : Measure G) (H : Subgroup G) (ν : Measure H) (c : ℂ) (F : G → ℂ) :
    quotIntegral μ H ν (fun g => c * F g) = c * quotIntegral μ H ν F := by
  unfold quotIntegral
  split_ifs
  · simp only [mul_assoc, integral_const_mul]
  · simp

private theorem quot_zero {G : Type} [Group G] [MeasurableSpace G] (μ : Measure G) (H : Subgroup G) (ν : Measure H) (F : G → ℂ)
    (h : ∀ g, F g = 0) : quotIntegral μ H ν F = 0 := by
  have := quot_smul μ H ν 0 F
  rw [zero_mul] at this
  rw [← this]
  congr 1
  funext g
  rw [h, mul_zero]

private theorem alg {A : Type} [CommGroup A] (d a b u v t : A) : d * a / u / t = d * b / v / t * (b⁻¹ * a / (v⁻¹ * u)) := by
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_div, ofMul_inv]
  abel

set_option maxHeartbeats 1600000 in
theorem elemLoc_of (hS : SuppE) (hO : OneField) (hR : Reps) (hN : NormOpen) (hD : NormDiag) (hA : Align) (hV : VolRatio)
    (hB : ∀ (E : Type) [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E] (n : ℕ)
      (r : ValueGroupWithZero E), 0 < r → r < 1 → ∃ K : Subgroup (GL (Fin n) E), (K : Set (GL (Fin n) E)) = ball n r ∧
        IsOpen (K : Set (GL (Fin n) E)) ∧ IsCompact (K : Set (GL (Fin n) E))) : ElemLoc := by
  intro k E _ _ _ _ _ _ _ _ _ _ _ _ _ σ hσ n _ _ _ _ μE μk hE hk r hr0 hr1
  obtain ⟨r₀, h00, h01, hn⟩ := hN k E σ hσ r hr0 hr1
  refine ⟨r₀, h00, h01, fun r' hle h'0 => ⟨fun x hx => (hn x (hx.trans hle)).2, ?_⟩⟩
  have h'1 : r' < 1 := hle.trans_lt h01
  obtain ⟨hcyc, -, hbr⟩ := bridge k E σ
  obtain ⟨hsg, -, -, hcl, -⟩ := hbr n
  have hc1 : Cyc (RingEquiv.refl k) 1 := ⟨fun _ => rfl, one_pos, fun _ => rfl⟩
  obtain ⟨R, hRne, hR1, hR2, hnear, hR3⟩ := hR E n σ _ hcyc r hr0 hr1
  obtain ⟨j, hj, hvol⟩ := hV k E σ hσ n r r' hr0 hr1 h'0 h'1 fun x hx => (hn x (hx.trans hle)).1
  obtain ⟨d1, d2, d3⟩ := hD k E σ hσ n
  obtain ⟨K, hK, hKo, hKc⟩ := hB E n r hr0 hr1
  obtain ⟨K', hK', hKo', hKc'⟩ := hB k n r' h'0 h'1
  obtain ⟨a1, a2, a3, -⟩ := UpperTheory.V.Z.Tf.Orb.gLTop E n
  have pE : 0 < μE.real (ball n r) := hK ▸ ENNReal.toReal_pos (hKo.measure_ne_zero μE ⟨1, one_mem _⟩) hKc.measure_ne_top
  have pk : 0 < μk.real (ball n r') := hK' ▸ ENNReal.toReal_pos (hKo'.measure_ne_zero μk ⟨1, one_mem _⟩) hKc'.measure_ne_top
  have pR : (0 : ℝ) < R.card := Nat.cast_pos.2 hRne.card_pos
  refine ⟨R.card * μE.real (ball n r) / (j * μk.real (ball n r')), by positivity, fun t ht => ?_⟩
  have hA1 : ∀ x ∈ ({t} : Set (Fin n → Eˣ)), Strict x := fun x hx => hx ▸ ht
  have hA2 := (d3 r hr1 t ht).1
  have key : ∀ x ∈ nrmSet k r t, ∀ s, Near r' s → x * s ∈ nrmSet k r t := by
    rintro _ ⟨u, hu, rfl⟩ s hs
    choose u' hu' hu'' using fun i => (hn (s i) ((hs i).trans hle)).2
    refine ⟨u * u', (hnear u u' hu hu').1, funext fun i => Units.ext ?_⟩
    simp only [nrmT, Pi.mul_apply, Units.val_mul, Units.coe_map, map_mul, hu'', mul_assoc]
  obtain ⟨-, -, -, -, hnear', -⟩ := hR k n _ _ hc1 r' h'0 h'1
  have meet' : ∀ γ g : GL (Fin n) k, g⁻¹ * γ * g ∈ elemSet r' (nrmSet k r t) →
      ∃ d : Fin n → Eˣ, Strict d ∧ IsNormOf σ (diagT E (Fin n) d) γ := fun γ g hg => by
    obtain ⟨y, x, hx, s, hs, -, e⟩ := (hS k n _ _ hc1 r' h'0 h'1 _ hA2).1 γ g hg
    obtain ⟨u, hu, e'⟩ := key x hx s hs
    refine ⟨t * u, fun i i' h => ?_, (incl y)⁻¹, ?_⟩
    · have hv : ∀ i, valuation E (u i : E) = 1 := fun i => by
        have := Valuation.map_one_add_of_lt (valuation E) ((hu i).trans_lt hr1)
        rwa [add_sub_cancel] at this
      simpa [hv] using ht i i' h
    · rw [(d1 _).1, ← e', ← e, inv_inv, map_mul, map_mul, map_inv]
      rfl
  refine ⟨fun δ γ h μδ μγ hδ hNm hμδ hμγ hm => ?_, fun γ μγ hγ hnn hμ => ?_⟩
  · unfold twOrbIntegralC orbIntegralC
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [quot_smul]
    by_cases hcase : ∃ y d, Strict d ∧ y⁻¹ * δ * sigmaGL σ y = diagT E (Fin n) d
    · obtain ⟨y, d, hd, hy⟩ := hcase
      obtain ⟨y', hy', hal⟩ := hA k E σ hσ n δ h y γ d hd hNm hy
      have oE := hO E n σ _ hcyc r hr0 hr1 μE hE _ hA1 δ y d hd (by rw [hsg]; exact hy) (twCent (sigmaGL σ) δ)
        (fun c => by rw [hsg]; rfl) μδ hμδ
      have ok := hO k n _ _ hc1 r' h'0 h'1 μk hk _ hA2 γ y' (nrmT k d) ((d1 d).2.1 hd) hy' (Subgroup.centralizer {γ})
        (fun c => by
          rw [Subgroup.mem_centralizer_singleton_iff]
          change _ ↔ c⁻¹ * γ * c = γ
          rw [mul_assoc, inv_mul_eq_iff_eq_mul, eq_comm]) μγ hμγ
      simp only [hsg] at oE
      have hdiv : ∀ u : Fin n → kˣ, nrmT k d * sgT (RingEquiv.refl k) u / u = nrmT k d := fun u => mul_div_cancel_right _ u
      by_cases hmem : nrmT k d ∈ nrmSet k r t
      · obtain ⟨u₀, hu₀⟩ := (d2 r d t).2 hmem
        have e1 := oE (R.image (u₀ * ·)) (fun u => by
          have e : d * sgT σ u / u / t = d * sgT σ u₀ / u₀ / t * (sgT σ (u₀⁻¹ * u) / (u₀⁻¹ * u)) := by
            have hm' : sgT (σ : E ≃+* E) (u₀⁻¹ * u) = (sgT (σ : E ≃+* E) u₀)⁻¹ * sgT (σ : E ≃+* E) u := by
              funext i
              simp only [sgT, Pi.mul_apply, Pi.inv_apply, map_mul, map_inv]
            rw [hm']
            exact alg _ _ _ _ _ _
          constructor
          · rintro ⟨_, rfl, hu⟩
            have h1 := (hnear _ _ (hnear _ _ hu₀ hu₀).2 hu).1
            rw [e, inv_mul_cancel_left] at h1
            obtain ⟨ρ, hρ, h2⟩ := (hR1 _).1 h1
            exact ⟨u₀ * ρ, Finset.mem_image_of_mem _ hρ, by simpa using (hR3 u₀ _ _).2 h2⟩
          · rintro ⟨_, hρ, h2⟩
            obtain ⟨ρ, hρ', rfl⟩ := Finset.mem_image.1 hρ
            refine ⟨t, rfl, ?_⟩
            rw [e]
            exact (hnear _ _ hu₀ ((hR1 _).2 ⟨ρ, hρ', (hR3 u₀ _ _).1 (by simpa using h2)⟩)).1)
          (by
            intro a ha b hb hab
            obtain ⟨a, ha', rfl⟩ := Finset.mem_image.1 ha
            obtain ⟨b, hb', rfl⟩ := Finset.mem_image.1 hb
            rw [hR2 a ha' b hb' ((hR3 _ _ _).1 hab)])
        have n1 : Near r' (1 : Fin n → kˣ) := fun i => by simp
        have e2 := ok {1} (fun u => ⟨fun _ => ⟨1, Finset.mem_singleton_self _, u, 1, rfl, n1, by simp⟩,
          fun _ => ⟨_, hmem, by rw [hdiv, div_self']; exact n1⟩⟩) (by simp)
        rw [Finset.card_image_of_injective _ (mul_right_injective u₀)] at e1
        have hmeas : MeasurableSet {z : GL (Fin n) E | y⁻¹ * (h * z * h⁻¹) * y ∈ ball n r} :=
          ((hK ▸ hKo : IsOpen (ball n r)).preimage (by fun_prop)).measurableSet
        have v1 := congrArg (fun m : Measure (GL (Fin n) E) => m {z | y⁻¹ * (h * z * h⁻¹) * y ∈ ball n r}) hm
        rw [Measure.map_apply (Continuous.measurable (by fun_prop)) hmeas,
          Measure.map_apply (f := fun t : Subgroup.centralizer {γ} => (incl (t : GL (Fin n) k) : GL (Fin n) E))
            (hcl.continuous.comp continuous_subtype_val).measurable hmeas] at v1
        have v2 : μδ.real {x : twCent (sigmaGL σ) δ | y⁻¹ * x * y ∈ ball n r} =
            j * μγ.real {x | y'⁻¹ * (x : GL (Fin n) k) * y' ∈ ball n r'} := by
          rw [← hvol γ y' _ ((d1 d).2.1 hd) hy' μγ hμγ]
          unfold Measure.real
          congr 1
          convert v1 using 2
          · ext x
            simp only [Set.mem_setOf_eq, Set.mem_preimage]
            rw [show h * (h⁻¹ * (x : GL (Fin n) E) * h) * h⁻¹ = x by group]
          · ext x
            simp only [Set.mem_setOf_eq, Set.mem_preimage]
            rw [hal _ x.2]
        refine e1.trans ?_
        rw [show quotIntegral μk _ μγ (fun g => (elemSet r' (nrmSet k r t)).indicator 1 (g⁻¹ * γ * g)) = _ from e2]
        rw [v2, ← Complex.ofReal_mul]
        congr 1
        rw [Finset.card_singleton, Nat.cast_one, one_mul, div_mul_div_comm, mul_right_comm j, mul_div_mul_right _ _ pk.ne']
      · have e1 := oE ∅ (fun u => ⟨fun ⟨_, hx, hu⟩ => absurd ((d2 r d t).1 ⟨u, hx ▸ hu⟩) hmem, by simp⟩) (by simp)
        have e2 := ok ∅ (fun u => ⟨fun ⟨x, hx, hu⟩ => absurd (by
          rw [hdiv] at hu
          simpa using key x hx _ hu) hmem, by simp⟩) (by simp)
        refine e1.trans ?_
        rw [show quotIntegral μk _ μγ (fun g => (elemSet r' (nrmSet k r t)).indicator 1 (g⁻¹ * γ * g)) = _ from e2]
        simp
    · rw [quot_zero, quot_zero, mul_zero]
      · intro g
        refine Set.indicator_of_notMem (fun hg => hcase ?_) _
        obtain ⟨d, hd, hnm⟩ := meet' γ g hg
        have hγ : IsRegSemisimple γ := by
          have e : ((normGL σ δ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E).charpoly =
              (γ : Matrix (Fin n) (Fin n) k).charpoly.map (algebraMap k E) := by
            rw [hNm, Units.val_mul, Units.val_mul, Matrix.coe_units_inv, Matrix.charpoly_units_conj, ← Matrix.charpoly_map]
            rfl
          unfold IsTwRegSemisimple at hδ
          rw [e] at hδ
          exact (Polynomial.separable_map _).1 hδ
        obtain ⟨x, hx⟩ := normInj k E σ hσ n γ hγ δ _ ⟨h, hNm⟩ hnm
        exact ⟨x, d, hd, hx.symm⟩
      · intro g
        refine Set.indicator_of_notMem (fun hg => hcase ?_) _
        obtain ⟨y, x, -, s, -, hs, e⟩ := (hS E n σ _ hcyc r hr0 hr1 _ hA1).1 δ g (by rw [hsg]; exact hg)
        exact ⟨y, _, hs, by rw [← hsg]; exact e⟩
  · refine quot_zero _ _ _ _ fun g => ?_
    rw [Pi.smul_apply, Set.indicator_of_notMem (fun hg => hnn ?_), smul_zero]
    obtain ⟨d, -, hnm⟩ := meet' γ g hg
    exact ⟨_, hnm⟩

end UpperTheory.Gal.InertialTypesAlt.L
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.FrobeniusLocalPairs.ElemTest
section
open MeasureTheory NumberField IsDedekindDomain ValuativeRel Matrix GroundTheory.Global GroundTheory.Global.SemiLocal
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets PositivityTheory.Rg.Tf.Loc UpperTheory.ConvolutionTheory.Loc
open GlobalTheory.SmGL hiding iwahori
open PositivityTheory.Rg.Tf.Geo (incFin galFin)
open UpperTheory.V.Published UpperTheory.CBC
open scoped Classical

namespace UpperTheory.Gal.InertialTypesAlt.L

section

variable {E : Type} [Field E] [ValuativeRel E] {n : ℕ}

private theorem near_mul {r : ValueGroupWithZero E} (h1 : r < 1) {x y : E} (hx : valuation E (x - 1) ≤ r)
    (hy : valuation E (y - 1) ≤ r) : valuation E (x * y - 1) ≤ r := by
  have hx1 : valuation E x ≤ 1 := by
    have e : x = (x - 1) + 1 := by ring
    rw [e]
    exact (Valuation.map_add_le _ (hx.trans h1.le) (by simp))
  have e : x * y - 1 = x * (y - 1) + (x - 1) := by ring
  rw [e]
  refine Valuation.map_add_le _ ?_ hx
  rw [map_mul]
  exact (mul_le_mul' hx1 hy).trans (by simp)

private theorem near_prod {r : ValueGroupWithZero E} (h0 : 0 < r) (h1 : r < 1) {ι : Type} (s : Finset ι) (f : ι → E)
    (hf : ∀ i ∈ s, valuation E (f i - 1) ≤ r) : valuation E (∏ i ∈ s, f i - 1) ≤ r := by
  induction s using Finset.induction_on with
  | empty => simpa using h0.le
  | insert a s ha ih =>
    rw [Finset.prod_insert ha]
    exact near_mul h1 (hf a (Finset.mem_insert_self _ _))
      (ih fun i hi => hf i (Finset.mem_insert_of_mem hi))

private theorem small_prod {r : ValueGroupWithZero E} {ι : Type} (s : Finset ι) (f : ι → E) (hs : ∀ i ∈ s, valuation E (f i) ≤ 1)
    (a : ι) (ha : a ∈ s) (hr : valuation E (f a) ≤ r) : valuation E (∏ i ∈ s, f i) ≤ r := by
  rw [← Finset.mul_prod_erase s f ha, map_mul, map_prod]
  exact (mul_le_of_le_one_right' (Finset.prod_le_one' fun i hi => hs i (Finset.mem_of_mem_erase hi))).trans hr

private theorem det_near {r : ValueGroupWithZero E} (h0 : 0 < r) (h1 : r < 1) {M : Matrix (Fin n) (Fin n) E}
    (hM : ∀ i j, valuation E (M i j - (1 : Matrix (Fin n) (Fin n) E) i j) ≤ r) : valuation E (M.det - 1) ≤ r := by
  have hb : ∀ i j, valuation E (M i j) ≤ 1 := fun i j => by
    have e : M i j = (M i j - (1 : Matrix (Fin n) (Fin n) E) i j) + (1 : Matrix (Fin n) (Fin n) E) i j := by ring
    rw [e]
    refine Valuation.map_add_le _ ((hM i j).trans h1.le) ?_
    rw [Matrix.one_apply]
    split_ifs <;> simp
  rw [Matrix.det_apply, ← Finset.add_sum_erase _ _ (Finset.mem_univ (1 : Equiv.Perm (Fin n))), add_sub_right_comm]
  refine Valuation.map_add_le _ ?_ (Valuation.map_sum_le _ fun p hp => ?_)
  · have hd : valuation E (∏ i, M i i - 1) ≤ r := near_prod h0 h1 _ _ fun i _ => by simpa using hM i i
    simpa using hd
  · have hp1 : p ≠ 1 := Finset.ne_of_mem_erase hp
    obtain ⟨a, ha⟩ : ∃ a, p a ≠ a := by
      by_contra hc
      push Not at hc
      exact hp1 (Equiv.ext hc)
    have hs : valuation E (∏ i, M (p i) i) ≤ r := by
      refine small_prod _ _ (fun i _ => hb _ _) a (Finset.mem_univ _) ?_
      simpa [Matrix.one_apply, ha] using hM (p a) a
    rcases Int.units_eq_one_or (Equiv.Perm.sign p) with e | e <;> simpa [e, Units.smul_def] using hs

end

private theorem diag_cont (E : Type) [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E] (n : ℕ) :
    Continuous (diagT E (Fin n)) :=
  (continuous_leviEmb E (points (Fin n))).comp (continuous_leviTorus E (Fin n))

theorem elemTest : ElemTest := by
  intro E _ _ _ _ n r h0 h1 A hA
  obtain ⟨K, hK, hKo, hKc⟩ := UpperTheory.ConvolutionTheory.Loc.ballSub E n r h0 h1
  haveI := (UpperTheory.V.Z.Tf.Orb.gLTop E n).2.2.1
  have mK : ∀ g : GL (Fin n) E, g ∈ ball n r ↔ g ∈ K := fun g => by rw [← hK]; rfl
  have e : elemSet r A = (fun z : GL (Fin n) E × (Fin n → Eˣ) × GL (Fin n) E => z.1 * diagT E (Fin n) z.2.1 * z.2.2) ''
      ((K : Set (GL (Fin n) E)) ×ˢ (A ×ˢ (K : Set (GL (Fin n) E)))) := by
    ext g
    constructor
    · rintro ⟨a, ha, b, hb, s, hs, rfl⟩
      exact ⟨(a, s, b), ⟨(mK a).1 ha, hs, (mK b).1 hb⟩, rfl⟩
    · rintro ⟨⟨a, s, b⟩, ⟨ha, hs, hb⟩, rfl⟩
      exact ⟨a, (mK a).2 ha, b, (mK b).2 hb, s, hs, rfl⟩
  have hS : IsCompact (elemSet r A) := by
    rw [e]
    refine (hKc.prod (hA.prod hKc)).image ?_
    exact (continuous_fst.mul ((diag_cont E n).comp (continuous_fst.comp continuous_snd))).mul
      (continuous_snd.comp continuous_snd)
  have hO : IsOpen (elemSet r A) := by
    rw [isOpen_iff_mem_nhds]
    rintro _ ⟨a, ha, b, hb, s, hs, rfl⟩
    refine Filter.mem_of_superset ((hKo.preimage (f := fun g => (a * diagT E (Fin n) s)⁻¹ * g) (by fun_prop)).mem_nhds
      (by simpa [mul_assoc] using (mK b).1 hb)) fun g hg => ?_
    exact ⟨a, ha, _, (mK _).2 hg, s, hs, by group⟩
  have hT : UpperTheory.ConvolutionTheory.C.Test ((elemSet r A).indicator (1 : GL (Fin n) E → ℂ)) := by
    refine ⟨(IsLocallyConstant.iff_eventually_eq _).2 fun g => ?_, HasCompactSupport.intro hS fun g hg => Set.indicator_of_notMem hg _⟩
    by_cases h : g ∈ elemSet r A
    · filter_upwards [hO.mem_nhds h] with y hy
      exact (Set.indicator_of_mem hy _).trans (Set.indicator_of_mem h (1 : GL (Fin n) E → ℂ)).symm
    · filter_upwards [hS.isClosed.isOpen_compl.mem_nhds h] with y hy
      exact (Set.indicator_of_notMem hy _).trans (Set.indicator_of_notMem h _).symm
  refine ⟨hO, hS, hT, hT, ?_⟩
  rintro _ ⟨a, ha, b, hb, s, hs, rfl⟩
  have hd : ∀ g ∈ ball (E := E) n r, valuation E (((GeneralLinearGroup.det g : Eˣ) : E) - 1) ≤ r := fun g hg => by
    simpa [GeneralLinearGroup.val_det_apply] using det_near h0 h1 hg
  refine ⟨s, hs, GeneralLinearGroup.det a * GeneralLinearGroup.det b, ?_, ?_⟩
  · rw [Units.val_mul]
    exact near_mul h1 (hd a ha) (hd b hb)
  · have hdiag : GeneralLinearGroup.det (diagT E (Fin n) s) = ∏ i, s i := by
      ext
      simp [GeneralLinearGroup.val_det_apply, val_diagT, Matrix.det_diagonal]
    rw [map_mul, map_mul, hdiag]
    simp only [mul_comm, mul_left_comm, mul_assoc]

end UpperTheory.Gal.InertialTypesAlt.L
end

