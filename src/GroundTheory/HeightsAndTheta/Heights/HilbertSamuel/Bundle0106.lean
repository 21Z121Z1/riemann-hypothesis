import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0017
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0035
import GroundTheory.HeightsAndTheta.Heights.Intersections.PBaseChange
import GroundTheory.HeightsAndTheta.Heights.HeightComparison.Bundle0003
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0020
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0042
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0073
import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0045
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0026
import GroundTheory.HeightsAndTheta.Heights.Intersections.StatementsAntisym
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.IsMultiHomogXpow

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PIntNumComponents
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

namespace IntNumComponents

theorem mem_minimalPrimes_iInf_iff {A : Type*} [CommRing A] {J₀ : Ideal A} {S : Finset (Ideal A)}
    (hS : ∀ W ∈ S, W ∈ J₀.minimalPrimes) (Z : Ideal A) :
    Z ∈ (⨅ W ∈ S, W).minimalPrimes ↔ Z ∈ S := by
  have hinf : (⨅ W ∈ S, W) = S.inf id := by rw [Finset.inf_eq_iInf]; rfl
  have key : ∀ Q : Ideal A, Q.IsPrime → (⨅ W ∈ S, W) ≤ Q → ∃ W ∈ S, W ≤ Q := by
    intro Q hQ hle
    rw [hinf] at hle
    exact hQ.inf_le'.mp hle
  constructor
  · intro hZ
    obtain ⟨W, hW, hWZ⟩ := key Z hZ.1.1 hZ.1.2
    have hZW : Z ≤ W := hZ.2 ⟨(hS W hW).1.1, iInf₂_le W hW⟩ hWZ
    rwa [le_antisymm hZW hWZ]
  · intro hZ
    refine ⟨⟨(hS Z hZ).1.1, iInf₂_le Z hZ⟩, fun Q hQ hQZ => ?_⟩
    obtain ⟨W, hW, hWQ⟩ := key Q hQ.1 hQ.2
    exact ((hS Z hZ).2 (hS W hW).1 (hWQ.trans hQZ)).trans hWQ

theorem isRadical_iInf {A : Type*} [CommRing A] {S : Finset (Ideal A)} (hS : ∀ W ∈ S, W.IsPrime) :
    (⨅ W ∈ S, W).IsRadical := by
  intro x hx
  obtain ⟨n, hn⟩ := hx
  simp only [Submodule.mem_iInf] at hn ⊢
  exact fun W hW => (hS W hW).mem_of_pow_mem n (hn W hW)

theorem multAt_toNat_of_isRadical {K : Type*} {ι : K → Type*} {J W : Ideal (MvPolynomial (Σ k, ι k) ℂ)}
    [W.IsPrime] (hJ : J.IsRadical) (hW : W ∈ J.minimalPrimes) : (NumbersDVR.multAt J W).toNat = 1 := by
  have h1 := localMult_eq_one_of_isRadical hJ hW
  unfold localMult at h1
  rw [dif_pos ‹W.IsPrime›] at h1
  unfold NumbersDVR.multAt
  rw [ObjectsChow.VerticalPartMultiplicity.length_localizedModule_quotient]
  exact h1

end IntNumComponents

open IntNumComponents in

theorem IntNumComponents.proof : IntNumComponents.Statement := by
  intro K _ _ ι _ P e a S hP hS
  have hJ₀h : NumbersDVR.IsMultiHomogIdeal (P.map (MvPolynomial.map (Int.castRingHom ℂ))) :=
    (Bridge.isMultiHomogIdeal_iff _).mpr (isMultiHomogIdeal_map_coeff _ hP.2.1.2.1)
  have hWh : ∀ W ∈ S, NumbersDVR.IsMultiHomogIdeal W := fun W hW =>
    FieldNumbers.PFContracted.isMultiHomogIdeal_of_mem_minimalPrimes hJ₀h (hS W hW)
  have hWdim : ∀ W ∈ S, ringKrullDim (MvPolynomial (Σ k, ι k) ℂ ⧸ W) =
      ((e + Fintype.card K : ℕ) : WithBot ℕ∞) := fun W hW => pcEquidim K ι P e hP W (hS W hW)
  have hmin := mem_minimalPrimes_iInf_iff hS
  have hJh : NumbersDVR.IsMultiHomogIdeal (⨅ W ∈ S, W) := by
    intro f hf b
    simp only [Submodule.mem_iInf] at hf ⊢
    exact fun W hW => hWh W hW f (hf W hW) b
  have hrad := isRadical_iInf (fun W hW => (hS W hW).1.1)
  have hdim : ringKrullDim (MvPolynomial (Σ k, ι k) ℂ ⧸ (⨅ W ∈ S, W)) <
      ((e + 1 + Fintype.card K : ℕ) : WithBot ℕ∞) := by
    refine lt_of_le_of_lt (Inter.BaseChange.ringKrullDim_quotient_le_of_minimalPrimes _
      (N := ((e + Fintype.card K : ℕ) : WithBot ℕ∞)) fun Z hZ => (hWdim Z ((hmin Z).mp hZ)).le) ?_
    exact_mod_cast (show e + Fintype.card K < e + 1 + Fintype.card K by omega)
  rw [NumbersDVR.IntNumAssoc.full ℂ K ι e _ hJh hdim a]
  unfold NumbersDVR.cycEval
  rw [← finsum_mem_coe_finset, finsum_mem_def]
  refine finsum_congr fun W => ?_
  unfold NumbersDVR.idealCycle
  by_cases hW : W ∈ S
  · rw [Set.indicator_of_mem (Finset.mem_coe.mpr hW)]
    have : W.IsPrime := (hS W hW).1.1
    by_cases hrel : NumbersDVR.IsRelevant W
    · rw [dif_pos ⟨(hmin W).mpr hW, hrel⟩, multAt_toNat_of_isRadical hrad ((hmin W).mpr hW)]
      simp
    · rw [dif_neg (fun h => hrel h.2), zero_mul,
        NumbersDVR.IntNumVanish.full ℂ K ι e W this (hWh W hW) (Or.inl hrel) a]
  · rw [Set.indicator_of_notMem (by simpa using hW), dif_neg (fun h => hW ((hmin W).mp h.1)), zero_mul]

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PLiftModel
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.ChartRestriction.G.AI.I1

noncomputable section

theorem LiftModel.ideal_eq_top_of_pow_mem {A : Type} [CommRing A] (J : Ideal A) {m : ℕ} (hm0 : m ≠ 0) (e : ℕ)
    (hm : (m : A) ^ e ∈ J) (hp : ∀ p ∈ m.primeFactors, J ⊔ Ideal.span {(p : A)} = ⊤) : J = ⊤ := by
  by_contra hJ
  obtain ⟨M, hM, hJM⟩ := Ideal.exists_le_maximal J hJ
  have hmM : (m : A) ∈ M := hM.isPrime.mem_of_pow_mem e (hJM hm)
  rw [Nat.prod_primeFactors_pow_factorization hm0, Nat.cast_prod] at hmM
  obtain ⟨p, hp', hpM⟩ := (Ideal.IsPrime.prod_mem_iff (hp := hM.isPrime)).mp hmM
  rw [Nat.cast_pow] at hpM
  have h1 : (p : A) ∈ M := hM.isPrime.mem_of_pow_mem _ hpM
  have hle : J ⊔ Ideal.span {(p : A)} ≤ M := sup_le hJM ((Ideal.span_singleton_le_iff_mem M).mpr h1)
  rw [hp p hp'] at hle
  exact hM.ne_top (top_le_iff.mp hle)

theorem LiftModel.mem_chartRingZ_of_mem_chartLat {K : Type} [Fintype K] {ι : K → Type} {Ω : Type} [Field Ω]
    {y : (Σ k, ι k) → Ω} {n : K → ℤ} {x : Ω} (hx : x ∈ chartLat y n 1) (c : ∀ k, ι k)
    (hc : ∀ k, y ⟨k, c k⟩ ≠ 0) : x * ∏ k, y ⟨k, c k⟩ ^ (-n k) ∈ chartRingZ y c := by
  have h := hx c hc
  simpa using h

theorem LiftModel.combine {K : Type} [Fintype K] {ι : K → Type} {Ω : Type} [Field Ω]
    (y : (Σ k, ι k) → Ω) (n : K → ℤ) {m : ℕ} (hm0 : m ≠ 0) {r₁ : ℕ} (x₁ : Fin r₁ → Ω)
    (hx₁ : ∀ j, x₁ j ∈ chartLat y n 1)
    (hg₁ : ∀ c : ∀ k, ι k, (∀ k, y ⟨k, c k⟩ ≠ 0) → ∃ (e : ℕ) (u : Fin r₁ → Ω), (∀ j, u j ∈ chartRingZ y c) ∧
      ∑ j, u j * (x₁ j * ∏ k, y ⟨k, c k⟩ ^ (-n k)) = (m : Ω) ^ e)
    (rP : ℕ → ℕ) (xP : ∀ p, Fin (rP p) → Ω) (hxP : ∀ p ∈ m.primeFactors, ∀ j, xP p j ∈ chartLat y n 1)
    (hgP : ∀ p ∈ m.primeFactors, ∀ c : ∀ k, ι k, (∀ k, y ⟨k, c k⟩ ≠ 0) → ∃ (u : Fin (rP p) → Ω) (v : Ω),
      (∀ j, u j ∈ chartRingZ y c) ∧ v ∈ chartRingZ y c ∧
        ∑ j, u j * (xP p j * ∏ k, y ⟨k, c k⟩ ^ (-n k)) + p * v = 1)
    {r₃ : ℕ} (x₃ : Fin r₃ → Ω) (hx₃ : ∀ j, x₃ j ∈ chartLat y n 1) :
    ∃ F : Finset Ω, (∀ f ∈ F, f ∈ chartLat y n 1) ∧ KH.GeneratesOn y n (fun f : F => (f : Ω)) ∧
      ∀ j, x₃ j ∈ F := by
  classical
  let F : Finset Ω := Finset.univ.image x₁ ∪ m.primeFactors.biUnion (fun p => Finset.univ.image (xP p)) ∪
    Finset.univ.image x₃
  have h₁F : ∀ j, x₁ j ∈ F := fun j => by simp [F]
  have hPF : ∀ p ∈ m.primeFactors, ∀ j, xP p j ∈ F := by
    intro p hp j
    simp only [F, Finset.mem_union, Finset.mem_biUnion, Finset.mem_image, Finset.mem_univ, true_and]
    exact Or.inl (Or.inr ⟨p, hp, j, rfl⟩)
  have h₃F : ∀ j, x₃ j ∈ F := fun j => by simp [F]
  have hFmem : ∀ f ∈ F, f ∈ chartLat y n 1 := by
    intro f hf
    simp only [F, Finset.mem_union, Finset.mem_biUnion, Finset.mem_image, Finset.mem_univ, true_and] at hf
    rcases hf with (⟨j, rfl⟩ | ⟨p, hp, j, rfl⟩) | ⟨j, rfl⟩
    · exact hx₁ j
    · exact hxP p hp j
    · exact hx₃ j
  refine ⟨F, hFmem, fun c hc => ?_, h₃F⟩
  let v : F → chartRingZ y c := fun f =>
    ⟨(f : Ω) * ∏ k, y ⟨k, c k⟩ ^ (-n k), LiftModel.mem_chartRingZ_of_mem_chartLat (hFmem f f.2) c hc⟩
  have hv : ∀ f (hf : f ∈ F), (⟨f * ∏ k, y ⟨k, c k⟩ ^ (-n k),
      LiftModel.mem_chartRingZ_of_mem_chartLat (hFmem f hf) c hc⟩ : chartRingZ y c) ∈ Ideal.span (Set.range v) :=
    fun f hf => Ideal.subset_span ⟨⟨f, hf⟩, rfl⟩
  obtain ⟨e, u, hu, hsum⟩ := hg₁ c hc
  have htop : Ideal.span (Set.range v) = ⊤ := by
    refine LiftModel.ideal_eq_top_of_pow_mem _ hm0 e ?_ fun p hp => ?_
    · have heq : ((m : chartRingZ y c) ^ e) = ∑ j, (⟨u j, hu j⟩ : chartRingZ y c) *
          ⟨x₁ j * ∏ k, y ⟨k, c k⟩ ^ (-n k), LiftModel.mem_chartRingZ_of_mem_chartLat (hFmem _ (h₁F j)) c hc⟩ := by
        apply Subtype.val_injective
        push_cast
        exact hsum.symm
      rw [heq]
      exact Ideal.sum_mem _ fun j _ => Ideal.mul_mem_left _ _ (hv _ (h₁F j))
    · obtain ⟨u', w, hu', hw, hsum'⟩ := hgP p hp c hc
      rw [Ideal.eq_top_iff_one]
      have heq : (1 : chartRingZ y c) = ∑ j, (⟨u' j, hu' j⟩ : chartRingZ y c) *
          ⟨xP p j * ∏ k, y ⟨k, c k⟩ ^ (-n k), LiftModel.mem_chartRingZ_of_mem_chartLat (hFmem _ (hPF p hp j)) c hc⟩ +
          (p : chartRingZ y c) * ⟨w, hw⟩ := by
        apply Subtype.val_injective
        push_cast
        exact hsum'.symm
      rw [heq]
      exact Ideal.add_mem _ (Ideal.mem_sup_left (Ideal.sum_mem _ fun j _ => Ideal.mul_mem_left _ _ (hv _ (hPF p hp j))))
        (Ideal.mem_sup_right (Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)))
  have h1 : (1 : chartRingZ y c) ∈ Ideal.span (Set.range v) := by
    rw [htop]
    exact Submodule.mem_top
  obtain ⟨a, ha⟩ := Ideal.mem_span_range_iff_exists_fun.mp h1
  refine ⟨fun f => (a f : Ω), fun f => (a f).2, ?_⟩
  have h := congrArg Subtype.val ha
  push_cast at h
  exact h

theorem LiftModel.isMultiHomog_rename {κ κ' : Type} [Fintype κ] [Fintype κ']
    (φ : (Σ _ : Unit, κ) → (Σ _ : Unit, κ')) {g : MRing (fun _ : Unit => κ)} {d : Unit → ℕ}
    (hg : IsMultiHomog g d) : IsMultiHomog (rename φ g) d := by
  have hdeg : ∀ {τ : Type} [Fintype τ] (m : (Σ _ : Unit, τ) →₀ ℕ), m.degree = ∑ i, m ⟨(), i⟩ := by
    intro τ _ m
    classical
    rw [Finsupp.degree_apply, Finset.sum_subset (Finset.subset_univ _) (fun x _ hx => by
      simpa using hx), Fintype.sum_sigma, Fintype.sum_unique]
  have hw : ∀ {τ : Type} (m : τ →₀ ℕ), Finsupp.weight 1 m = m.degree := by
    intro τ m
    rw [Finsupp.degree_eq_weight_one]
    rfl
  have hH : g.IsHomogeneous (d ()) := by
    intro m hm
    rw [hw, hdeg]
    exact hg m (mem_support_iff.mpr hm) ()
  have h := hH.rename_isHomogeneous (f := φ)
  intro m hm k
  have := h (mem_support_iff.mp hm)
  rw [hw, hdeg] at this
  exact this

theorem LiftModel.birational_of_subfamily {Ω : Type} [Field Ω] {r : ℕ} (x₃ : Fin r → Ω) (F : Finset Ω)
    (h : ∀ j, x₃ j ∈ F) (hb : Birational (fun p : Σ _ : Unit, Fin r => x₃ p.2)) :
    Birational (fun p : Σ _ : Unit, F => (p.2 : Ω)) := by
  intro s
  obtain ⟨d, g, g', hg, hg', hg0, hgs⟩ := hb s
  let φ : (Σ _ : Unit, Fin r) → (Σ _ : Unit, F) := fun p => ⟨(), ⟨x₃ p.2, h p.2⟩⟩
  have hev : ∀ f : MRing (fun _ : Unit => Fin r), aeval (fun p : Σ _ : Unit, F => (p.2 : Ω)) (rename φ f) =
      aeval (fun p : Σ _ : Unit, Fin r => x₃ p.2) f := fun f => by
    rw [aeval_rename]
    rfl
  refine ⟨d, rename φ g, rename φ g', LiftModel.isMultiHomog_rename φ hg, LiftModel.isMultiHomog_rename φ hg', ?_, ?_⟩
  · rw [hev]
    exact hg0
  · rw [hev, hev]
    exact hgs

theorem LiftModel.isProjVarF_genIdeal {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type}
    [Field Ω] {y : (Σ k, ι k) → Ω} {D : ℕ} (hV : IsArithVar (mCoordIdeal y) (D + 1)) :
    IsProjVarF (KH.genIdeal y) D := by
  classical
  have h := GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter.isProjVarQ_of_isArithVar hV
  exact ⟨(GroundTheory.Heights₂.Heights.NumbersDVR.Objects.isMultiProjPrime_iff _).mp h.1, h.2⟩

theorem LiftModel.core {K : Type} [Fintype K] {ι : K → Type} {Ω : Type} [Field Ω] (y : (Σ k, ι k) → Ω)
    (N : K → ℤ) (B : ∀ r : ℕ, (Fin r → Ω) → Prop) {q₁ m t₁ : ℕ} (hq₁ : 1 ≤ q₁) (hm : 1 ≤ m)
    (h₁ : ∀ t : ℕ, t₁ ≤ t → ∃ (r : ℕ) (x' : Fin r → Ω), (∀ j, x' j ∈ chartLat y ((t * q₁) • N) 1) ∧
      ∀ c : ∀ k, ι k, (∀ k, y ⟨k, c k⟩ ≠ 0) → ∃ (e : ℕ) (u : Fin r → Ω), (∀ j, u j ∈ chartRingZ y c) ∧
        ∑ j, u j * (x' j * ∏ k, y ⟨k, c k⟩ ^ (-((t * q₁) • N) k)) = (m : Ω) ^ e)
    (qP tP : ℕ → ℕ) (hqP : ∀ p ∈ m.primeFactors, 1 ≤ qP p)
    (hP : ∀ p ∈ m.primeFactors, ∀ t : ℕ, tP p ≤ t → ∃ (r : ℕ) (x' : Fin r → Ω),
      (∀ j, x' j ∈ chartLat y ((t * qP p) • N) 1) ∧
      ∀ c : ∀ k, ι k, (∀ k, y ⟨k, c k⟩ ≠ 0) → ∃ (u : Fin r → Ω) (v : Ω), (∀ j, u j ∈ chartRingZ y c) ∧
        v ∈ chartRingZ y c ∧ ∑ j, u j * (x' j * ∏ k, y ⟨k, c k⟩ ^ (-((t * qP p) • N) k)) + p * v = 1)
    {q₃ t₃ : ℕ} (hq₃ : 1 ≤ q₃)
    (h₃ : ∀ t : ℕ, t₃ ≤ t → ∃ (r : ℕ) (x' : Fin r → Ω), (∀ j, x' j ∈ chartLat y ((t * q₃) • N) 1) ∧ B r x') :
    ∃ (a : ℕ) (F : Finset Ω), 1 ≤ a ∧ (∀ f ∈ F, f ∈ chartLat y (a • N) 1) ∧
      KH.GeneratesOn y (a • N) (fun f : F => (f : Ω)) ∧ ∃ (r : ℕ) (x₃ : Fin r → Ω), (∀ j, x₃ j ∈ F) ∧ B r x₃ := by
  classical
  have hprod : ∀ s ⊆ m.primeFactors, 1 ≤ ∏ p ∈ s, qP p := fun s hs =>
    Nat.one_le_iff_ne_zero.mpr (Finset.prod_ne_zero_iff.mpr fun p hp => by have := hqP p (hs hp); omega)
  have hprodS := hprod m.primeFactors subset_rfl
  set t := t₁ + t₃ + ∑ p ∈ m.primeFactors, tP p + 1 with ht
  set Q := q₁ * q₃ * ∏ p ∈ m.primeFactors, qP p with hQ
  have hQ1 : 1 ≤ Q := Nat.one_le_iff_ne_zero.mpr (by positivity)
  have ht1 : 1 ≤ t := by omega

  have hT₁ : t₁ ≤ t * (q₃ * ∏ p ∈ m.primeFactors, qP p) :=
    le_trans (by omega) (Nat.le_mul_of_pos_right _ (by positivity))
  obtain ⟨r₁, x₁, hx₁, hg₁⟩ := h₁ _ hT₁
  have e₁ : t * (q₃ * ∏ p ∈ m.primeFactors, qP p) * q₁ = t * Q := by rw [hQ]; ring
  rw [e₁] at hx₁ hg₁

  have hT₃ : t₃ ≤ t * (q₁ * ∏ p ∈ m.primeFactors, qP p) :=
    le_trans (by omega) (Nat.le_mul_of_pos_right _ (by positivity))
  obtain ⟨r₃, x₃, hx₃, hB₃⟩ := h₃ _ hT₃
  have e₃ : t * (q₁ * ∏ p ∈ m.primeFactors, qP p) * q₃ = t * Q := by rw [hQ]; ring
  rw [e₃] at hx₃

  have hP' : ∀ p ∈ m.primeFactors, ∃ (r : ℕ) (x' : Fin r → Ω), (∀ j, x' j ∈ chartLat y ((t * Q) • N) 1) ∧
      ∀ c : ∀ k, ι k, (∀ k, y ⟨k, c k⟩ ≠ 0) → ∃ (u : Fin r → Ω) (v : Ω), (∀ j, u j ∈ chartRingZ y c) ∧
        v ∈ chartRingZ y c ∧ ∑ j, u j * (x' j * ∏ k, y ⟨k, c k⟩ ^ (-((t * Q) • N) k)) + p * v = 1 := by
    intro p hp
    have hprodp := hprod (m.primeFactors.erase p) (Finset.erase_subset _ _)
    have htp : tP p ≤ t := by
      have := Finset.single_le_sum (f := tP) (fun _ _ => Nat.zero_le _) hp
      omega
    have hTp : tP p ≤ t * (q₁ * q₃ * ∏ p' ∈ m.primeFactors.erase p, qP p') :=
      le_trans htp (Nat.le_mul_of_pos_right _ (by positivity))
    obtain ⟨r, x', hx, hg⟩ := hP p hp _ hTp
    have ep : t * (q₁ * q₃ * ∏ p' ∈ m.primeFactors.erase p, qP p') * qP p = t * Q := by
      rw [hQ, ← Finset.mul_prod_erase m.primeFactors qP hp]
      ring
    rw [ep] at hx hg
    exact ⟨r, x', hx, hg⟩
  choose! rP xP hxP hgP using hP'
  obtain ⟨F, hFmem, hFgen, hF₃⟩ :=
    LiftModel.combine y ((t * Q) • N) (by omega) x₁ hx₁ hg₁ rP xP hxP hgP x₃ hx₃
  exact ⟨t * Q, F, Nat.one_le_iff_ne_zero.mpr (by positivity), hFmem, hFgen, r₃, x₃, hF₃, hB₃⟩

theorem LiftModelGen.proof (hS : LiftSpread.Statement) (hA : LiftAtPrime.Statement) : LiftModelGen.Statement := by
  intro K _ _ ι _ _ Ω _ _ y D N hV hQ hF
  classical
  obtain ⟨q₁, m, t₁, hq₁, hm, h₁⟩ := hS K ι Ω y D N hV hQ
  have hP := fun p (hp : p ∈ m.primeFactors) =>
    hA K ι Ω y D N p hV (Nat.prime_of_mem_primeFactors hp) (hF p (Nat.prime_of_mem_primeFactors hp))
  choose! qP tP hqP hP using hP
  obtain ⟨a, F, ha, hmem, hgen, -⟩ := LiftModel.core y N (fun _ _ => True) hq₁ hm h₁ qP tP hqP hP
    (q₃ := 1) (t₃ := 0) le_rfl fun _ _ => ⟨0, Fin.elim0, fun j => j.elim0, trivial⟩
  exact ⟨a, {x // x ∈ F}, inferInstance, Subtype.val, ha, fun j => hmem j j.2, hgen⟩

theorem LiftModelNef.proof (hKA : KH.KAmpStatement) (hS : LiftSpread.Statement) (hA : LiftAtPrime.Statement)
    (hB : LiftBirationalNef.Statement) : LiftModelNef.Statement := by
  intro K _ _ ι _ _ Ω _ _ y D α b a₀ I hI hV hbir hnef hb ha₀ hF
  classical
  have hQ : KH.AmpleV ℚ (KH.genIdeal y) (b • α + fun _ => (a₀ : ℤ)) :=
    hKA ℚ K ι I (KH.genIdeal y) D α b a₀ hI (LiftModel.isProjVarF_genIdeal hV) hnef hb ha₀
  obtain ⟨q₁, m, t₁, hq₁, hm, h₁⟩ := hS K ι Ω y D _ hV hQ
  have hP := fun p (hp : p ∈ m.primeFactors) =>
    hA K ι Ω y D _ p hV (Nat.prime_of_mem_primeFactors hp) (hF p (Nat.prime_of_mem_primeFactors hp))
  choose! qP tP hqP hP using hP
  obtain ⟨q₃, t₃, hq₃, h₃⟩ := hB K ι Ω y D α b a₀ I hI hV hbir hnef hb ha₀
  obtain ⟨a, F, ha, hmem, hgen, r, x₃, hx₃F, hbir₃⟩ :=
    LiftModel.core y _ (fun r x => Birational (fun p : Σ _ : Unit, Fin r => x p.2)) hq₁ hm h₁ qP tP hqP hP hq₃ h₃
  exact ⟨a, {x // x ∈ F}, inferInstance, Subtype.val, ha, fun j => hmem j j.2, hgen,
    LiftModel.birational_of_subfamily x₃ F hx₃F hbir₃⟩

theorem LiftModel.proof (hS : LiftSpread.Statement) (hA : LiftAtPrime.Statement)
    (hB : LiftBirationalAmple.Statement) : LiftModel.Statement := by
  intro K _ _ ι _ _ Ω _ _ y D N hV hbir hQ hcQ hF
  classical
  obtain ⟨c, hc1, hcQ⟩ := hcQ
  obtain ⟨q₁, m, t₁, hq₁, hm, h₁⟩ := hS K ι Ω y D N hV hQ
  have hP := fun p (hp : p ∈ m.primeFactors) =>
    hA K ι Ω y D N p hV (Nat.prime_of_mem_primeFactors hp) (hF p (Nat.prime_of_mem_primeFactors hp))
  choose! qP tP hqP hP using hP
  obtain ⟨q₃, t₃, hq₃, h₃⟩ := hB K ι Ω y D N c hV hbir hc1 hcQ
  obtain ⟨a, F, ha, hmem, hgen, r, x₃, hx₃F, hbir₃⟩ :=
    LiftModel.core y N (fun r x => Birational (fun p : Σ _ : Unit, Fin r => x p.2)) hq₁ hm h₁ qP tP hqP hP hq₃ h₃
  exact ⟨a, {x // x ∈ F}, inferInstance, Subtype.val, ha, fun j => hmem j j.2, hgen,
    LiftModel.birational_of_subfamily x₃ F hx₃F hbir₃⟩

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PMonomialShift
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry Filter

noncomputable section

namespace MonomialShift

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]

theorem exists_chart {y : (Σ k, ι k) → Ω} {d : ℕ} (hY : IsArithVar (mCoordIdeal y) d) :
    ∃ c : ∀ k, ι k, ∀ k, y ⟨k, c k⟩ ≠ 0 := by
  have hrel := hY.2.1.2.2
  refine ⟨fun k => (hrel k).choose, fun k h0 => (hrel k).choose_spec ?_⟩
  change _ ∈ RingHom.ker _
  rw [RingHom.mem_ker]
  simp [mConeMap, h0]

theorem norm_prod_le {P : Ideal (MRing ι)} {A : HermLine ι} {a : K → ℕ} (hM : MonomialsBounded P A a)
    (c : ∀ k, ι k) (j n : ℕ) {z : (Σ k, ι k) → ℂ} (hz : z ∈ mcPts P) :
    ‖∏ k, z ⟨k, c k⟩ ^ (j * a k + n)‖ ≤ A.h z ^ j * (fsH ι).h z ^ n := by
  classical
  have e1 : ‖∏ k, z ⟨k, c k⟩ ^ (j * a k + n)‖ =
      (∏ k, ‖z ⟨k, c k⟩‖ ^ a k) ^ j * (∏ k, ‖z ⟨k, c k⟩‖) ^ n := by
    rw [norm_prod, ← Finset.prod_pow, ← Finset.prod_pow, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun k _ => ?_
    rw [norm_pow]
    ring

  let μ : (Σ k, ι k) →₀ ℕ := Finsupp.equivFunOnFinite.symm fun p => if p.2 = c p.1 then a p.1 else 0
  have hμ : ∀ k, ∑ i, μ ⟨k, i⟩ = a k := by
    intro k
    simp [μ]
  have hmon : ∏ p, z p ^ μ p = ∏ k, z ⟨k, c k⟩ ^ a k := by
    rw [Fintype.prod_sigma]
    refine Finset.prod_congr rfl fun k _ => ?_
    simp [μ, pow_ite]
  have hA : ∏ k, ‖z ⟨k, c k⟩‖ ^ a k ≤ A.h z := by
    have := hM z hz μ hμ
    rw [hmon, norm_prod] at this
    simpa [norm_pow] using this
  have hH : ∏ k, ‖z ⟨k, c k⟩‖ ≤ (fsH ι).h z := by
    have hfs : (fsH ι).h z = ∏ k, Real.sqrt (∑ i, ‖z ⟨k, i⟩‖ ^ 2) := by
      rw [fsH, GroundTheory.Heights₂.Heights.Inter.ofMetrics_fs_h]
      simp
    rw [hfs]
    refine Finset.prod_le_prod (fun k _ => norm_nonneg _) fun k _ => Real.le_sqrt_of_sq_le ?_
    exact Finset.single_le_sum (f := fun i => ‖z ⟨k, i⟩‖ ^ 2) (fun i _ => sq_nonneg _) (Finset.mem_univ (c k))
  rw [e1]
  gcongr
  exact pow_nonneg (A.pos z hz.1).le _

theorem isSmoothHerm_zcomb_fsH {A : HermLine ι} (hA : IsSmoothHerm A) (q : ℕ) :
    IsSmoothHerm (HermLine.zcomb A (fsH ι) q 1) := by
  have hH : IsSmoothHerm (fsH ι) := GroundTheory.Heights₂.Heights.Inter.isSmoothHerm_ofMetrics_fs 1
  have hfun : (HermLine.zcomb A (fsH ι) q 1).h = fun z => A.h z ^ q * (fsH ι).h z := by
    funext z
    change A.h z ^ ((q : ℕ) : ℤ) * (fsH ι).h z ^ (1 : ℤ) = _
    rw [zpow_natCast, zpow_one]
  unfold IsSmoothHerm at hA hH ⊢
  rw [hfun]
  exact (hA.pow q).mul hH

theorem proof (hPack : PackingStatement) : MonomialShift.Statement := by
  intro K _ ι _ Ω _ y D a A P0 q τ n hY hBir ha hP0 hsemi hM hq hτ
  classical
  obtain ⟨c, hc⟩ := exists_chart hY

  obtain ⟨e, he⟩ : ∃ e : K → ℕ, e = fun k => (q * n - τ) * a k + n := ⟨_, rfl⟩
  have hBa : ∀ k, (HermLine.zcomb A (fsH ι) q 1).a k = (q : ℤ) * a k + 1 := by
    intro k
    simp [HermLine.zcomb, fsH, HermLine.ofMetrics, ha]
  have hdeg : ∀ k, (n : ℤ) * (HermLine.zcomb A (fsH ι) q 1).a k = τ * A.a k + e k := by
    intro k
    rw [hBa, he]
    simp only [ha]
    push_cast [Nat.cast_sub hτ]
    ring

  obtain ⟨mv, hmv⟩ : ∃ mv : Ω, mv = ∏ k, y ⟨k, c k⟩ ^ e k := ⟨_, rfl⟩
  have hmv0 : mv ≠ 0 := by
    rw [hmv]
    exact Finset.prod_ne_zero_iff.mpr fun k _ => pow_ne_zero _ (hc k)
  have hmvx : aeval y (xpow c e) = mv := by
    simp [hmv, xpow]

  have hlat : ∀ s ∈ chartLatNm y A.a τ, mv * s ∈ chartLatNm y (HermLine.zcomb A (fsH ι) q 1).a n := by
    intro s hs c' hc'
    have h1 := hs c' hc'
    have h2 : ∏ k, (y ⟨k, c k⟩ / y ⟨k, c' k⟩) ^ e k ∈ integralClosure (chartRingZ y c') Ω := by
      have hmem : ∏ k, (y ⟨k, c k⟩ / y ⟨k, c' k⟩) ^ e k ∈ chartRingZ y c' :=
        Subalgebra.prod_mem _ fun k _ =>
          pow_mem (Algebra.subset_adjoin
            (Set.mem_range_self (f := fun p : Σ k, ι k => y p / y ⟨p.1, c' p.1⟩) ⟨k, c k⟩)) _
      exact (integralClosure (chartRingZ y c') Ω).algebraMap_mem ⟨_, hmem⟩
    have hsplit : ∀ k, y ⟨k, c' k⟩ ^ (-((n : ℤ) * (HermLine.zcomb A (fsH ι) q 1).a k)) =
        y ⟨k, c' k⟩ ^ (-((τ : ℤ) * A.a k)) * (y ⟨k, c' k⟩ ^ e k)⁻¹ := by
      intro k
      rw [hdeg k, neg_add, zpow_add₀ (hc' k), zpow_neg (y _) ((e k : ℕ) : ℤ), zpow_natCast]
    have key : mv * s * ∏ k, y ⟨k, c' k⟩ ^ (-((n : ℤ) * (HermLine.zcomb A (fsH ι) q 1).a k)) =
        (s * ∏ k, y ⟨k, c' k⟩ ^ (-((τ : ℤ) * A.a k))) * ∏ k, (y ⟨k, c k⟩ / y ⟨k, c' k⟩) ^ e k := by
      simp only [hsplit, div_eq_mul_inv, mul_pow, inv_pow, Finset.prod_mul_distrib, Finset.prod_inv_distrib, hmv]
      ring
    rw [key]
    exact mul_mem h1 h2

  have hsmall : ∀ s, IsSmallH (mCoordIdeal y) y A τ s →
      IsSmallH (mCoordIdeal y) y (HermLine.zcomb A (fsH ι) q 1) n (mv * s) := by
    intro s hs dg dh g h z hg hh hd hgh hz
    have hmh := ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.isMultiHomog_mul (isMultiHomog_xpow c e) hh
    have hb := hs dg (e + dh) g (xpow c e * h) z hg hmh
      (fun k => by have := hd k; have := hdeg k; simp only [Pi.add_apply]; push_cast; linarith)
      (by rw [hgh, map_mul, hmvx]; ring) hz
    have hApos : 0 < A.h z := A.pos z hz.1
    have hxz : eval z (map (Int.castRingHom ℂ) (xpow c e)) = ∏ k, z ⟨k, c k⟩ ^ ((q * n - τ) * a k + n) := by
      simp [xpow, he]
    have hBh : (HermLine.zcomb A (fsH ι) q 1).h z = A.h z ^ ((q : ℕ) : ℤ) * (fsH ι).h z ^ (1 : ℤ) := rfl
    calc ‖eval z (map (Int.castRingHom ℂ) g)‖
        ≤ ‖eval z (map (Int.castRingHom ℂ) (xpow c e * h))‖ * A.h z ^ τ := hb
      _ = ‖∏ k, z ⟨k, c k⟩ ^ ((q * n - τ) * a k + n)‖ * ‖eval z (map (Int.castRingHom ℂ) h)‖ * A.h z ^ τ := by
          rw [map_mul, eval_mul, norm_mul, hxz]
      _ ≤ (A.h z ^ (q * n - τ) * (fsH ι).h z ^ n) * ‖eval z (map (Int.castRingHom ℂ) h)‖ * A.h z ^ τ := by
          gcongr
          exact norm_prod_le hM c (q * n - τ) n hz
      _ = ‖eval z (map (Int.castRingHom ℂ) h)‖ * (HermLine.zcomb A (fsH ι) q 1).h z ^ n := by
          rw [hBh, zpow_natCast, zpow_one, mul_pow, ← pow_mul,
            show A.h z ^ (q * n) = A.h z ^ (q * n - τ) * A.h z ^ τ by rw [← pow_add, Nat.sub_add_cancel hτ]]
          ring

  let f : {s : chartLatNm y A.a τ // IsSmallH (mCoordIdeal y) y A τ (s : Ω)} →
      {t : chartLatNm y (HermLine.zcomb A (fsH ι) q 1).a n //
        IsSmallH (mCoordIdeal y) y (HermLine.zcomb A (fsH ι) q 1) n (t : Ω)} :=
    fun s => ⟨⟨mv * s.1, hlat s.1 s.1.2⟩, hsmall s.1 s.2⟩
  have hinj : Function.Injective f := by
    intro s t hst
    have h := congrArg (fun u => ((u.1 : chartLatNm y (HermLine.zcomb A (fsH ι) q 1).a n) : Ω)) hst
    exact Subtype.ext (Subtype.ext (mul_left_cancel₀ hmv0 h))
  have hfin := (hPack K ι Ω y D (HermLine.zcomb A (fsH ι) q 1)
    (chartLatNm y (HermLine.zcomb A (fsH ι) q 1).a) hY hBir (isSmoothHerm_zcomb_fsH hsemi.1 q)
    (fun _ => le_rfl)).1 n
  have : Finite {t : chartLatNm y (HermLine.zcomb A (fsH ι) q 1).a n //
      IsSmallH (mCoordIdeal y) y (HermLine.zcomb A (fsH ι) q 1) n (t : Ω)} := hfin.to_subtype
  have hcard := Nat.card_le_card_of_injective f hinj
  unfold smallSectionCount
  rcases Nat.eq_zero_or_pos (Nat.card {s : chartLatNm y A.a τ // IsSmallH (mCoordIdeal y) y A τ (s : Ω)})
    with h0 | hpos
  · rw [h0, Nat.cast_zero, Real.log_zero]
    exact Real.log_natCast_nonneg _
  · exact Real.log_le_log (by exact_mod_cast hpos) (by exact_mod_cast hcard)

end MonomialShift

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

