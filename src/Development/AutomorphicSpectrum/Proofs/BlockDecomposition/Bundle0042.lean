import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0016
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0002
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0019
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IsotropicMahlerBounds.LogAbsoluteWedges.WedgeSub
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0020

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MeasureUnitImage
section
open MeasureTheory Topology Filter GlobalTheory.CompanionTheory.NullFr
open scoped NNReal ENNReal Matrix

namespace GlobalTheory.CompanionTheory.NullFr.Packing

theorem exists_max_card {α : Type} (Q : Finset α → Prop) (B : ℕ) (h0 : ∃ P, Q P)
    (hB : ∀ P, Q P → P.card ≤ B) : ∃ P, Q P ∧ ∀ P', Q P' → P'.card ≤ P.card := by
  obtain ⟨P₀, hP₀⟩ := h0
  have hne : {n : ℕ | ∃ P, Q P ∧ P.card = n}.Nonempty := ⟨P₀.card, P₀, hP₀, rfl⟩
  have hbdd : BddAbove {n : ℕ | ∃ P, Q P ∧ P.card = n} := by
    refine ⟨B, ?_⟩
    rintro n ⟨P, hP, rfl⟩
    exact hB P hP
  obtain ⟨P, hP, hcard⟩ := Nat.sSup_mem hne hbdd
  refine ⟨P, hP, fun P' hP' => ?_⟩
  rw [hcard]
  exact le_csSup hbdd ⟨P', hP', rfl⟩

theorem measure_unit_image {A : Type} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    [T2Space A] [MeasurableSpace A] [BorelSpace A] {md : Aˣ →* ℝ≥0} (hmd : IsHaarMod md)
    (h : Measure A) [h.IsAddHaarMeasure] (u : Aˣ) {K : Set A} (hK : IsCompact K) :
    h ((fun x : A => (u : A) * x) '' K) = md u * h K := by
  have hc : Continuous fun x : A => (u : A) * x := continuous_const.mul continuous_id
  have hinj : Function.Injective fun x : A => (u : A) * x := fun x y hxy => by
    simpa using congrArg (fun z => ((u⁻¹ : Aˣ) : A) * z) hxy
  have hKu : IsCompact ((fun x : A => (u : A) * x) '' K) := hK.image hc
  have key := congrArg (fun μ : Measure A => μ ((fun x : A => (u : A) * x) '' K))
    (hmd h inferInstance u)
  rw [Measure.map_apply hc.measurable hKu.measurableSet, Set.preimage_image_eq _ hinj,
    Measure.smul_apply, smul_eq_mul] at key
  have hmd0 : ((md u : ℝ≥0) : ℝ≥0∞) ≠ 0 := by
    have h1 : md u * md u⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel, map_one]
    intro h0
    rw [ENNReal.coe_eq_zero] at h0
    rw [h0, zero_mul] at h1
    exact zero_ne_one h1
  rw [key, ← mul_assoc, ENNReal.mul_inv_cancel hmd0 ENNReal.coe_ne_top, one_mul]

theorem card_mul_le {A : Type} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    [T2Space A] [MeasurableSpace A] [BorelSpace A] {md : Aˣ →* ℝ≥0} (hmd : IsHaarMod md)
    (h : Measure A) [h.IsAddHaarMeasure] (u : Aˣ) {K L : Set A} (hK : IsCompact K) (P : Finset A)
    (hdisj : ∀ p ∈ P, ∀ q ∈ P, p ≠ q →
      Disjoint ((fun x : A => p + (u : A) * x) '' K) ((fun x : A => q + (u : A) * x) '' K))
    (hL : ∀ p ∈ P, ∀ w ∈ K, p + (u : A) * w ∈ L) :
    (P.card : ℝ≥0∞) * (md u * h K) ≤ h L := by
  classical
  have hcont : ∀ p : A, Continuous fun x : A => p + (u : A) * x := fun p =>
    continuous_const.add (continuous_const.mul continuous_id)
  have hmT : ∀ p : A, h ((fun x : A => p + (u : A) * x) '' K) = md u * h K := by
    intro p
    have e : (fun x : A => p + (u : A) * x) '' K =
        (fun y => -p + y) ⁻¹' ((fun x : A => (u : A) * x) '' K) := by
      ext y
      simp only [Set.mem_image, Set.mem_preimage]
      constructor
      · rintro ⟨x, hx, rfl⟩
        exact ⟨x, hx, by abel⟩
      · rintro ⟨x, hx, hxy⟩
        exact ⟨x, hx, by rw [hxy]; abel⟩
    rw [e, measure_preimage_add, GlobalTheory.CompanionTheory.NullFr.Packing.measure_unit_image hmd h u hK]
  have hsub : (⋃ p ∈ P, (fun x : A => p + (u : A) * x) '' K) ⊆ L := by
    refine Set.iUnion₂_subset fun p hp => ?_
    rintro _ ⟨w, hw, rfl⟩
    exact hL p hp w hw
  calc (P.card : ℝ≥0∞) * (md u * h K)
      = ∑ p ∈ P, h ((fun x : A => p + (u : A) * x) '' K) := by
        rw [Finset.sum_congr rfl (fun p _ => hmT p), Finset.sum_const, nsmul_eq_mul]
    _ = h (⋃ p ∈ P, (fun x : A => p + (u : A) * x) '' K) :=
        (measure_biUnion_finset (fun p hp q hq hpq => hdisj p hp q hq hpq)
          (fun p _ => (hK.image (hcont p)).measurableSet)).symm
    _ ≤ h L := measure_mono hsub

theorem net : ∀ {A : Type} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [LocallyCompactSpace A] [T2Space A] [SecondCountableTopology A] [MeasurableSpace A] [BorelSpace A] (md : Aˣ →* ℝ≥0) (_ : IsHaarMod md) (f : A) (_ : f * f = f) (C U : Set A) (_ : IsCompact C) (_ : U ∈ 𝓝 (0 : A)),
    ∃ (κ : ℝ≥0) (V : Set A), V ∈ 𝓝 (0 : A) ∧ ∀ u : Aˣ, (1 - f) * (u : A) = 1 - f → f * (u : A) ∈ V →
      ∃ N : Finset A, (∀ p ∈ N, f * p = p ∧ p ∈ C) ∧ (N.card : ℝ≥0) * md u ≤ κ ∧
        ∀ c ∈ C, f * c = c → ∃ p ∈ N, ∃ w ∈ U, f * w = w ∧ c = p + u * w := by
  intro A _ _ _ _ _ _ _ _ md hmd f _ C U hC hU
  classical
  have hU' : U ∈ 𝓝 ((0 : A) - 0) := by rwa [sub_zero]
  have h0 : (fun p : A × A => p.1 - p.2) ⁻¹' U ∈ 𝓝 ((0 : A), (0 : A)) :=
    continuous_sub.tendsto ((0 : A), (0 : A)) hU'
  obtain ⟨W₁, hW₁, W₂, hW₂, hW⟩ := mem_nhds_prod_iff.1 h0
  obtain ⟨K, hK0, hKW, hK⟩ := local_compact_nhds (Filter.inter_mem hW₁ hW₂)
  have hKU : ∀ a ∈ K, ∀ b ∈ K, a - b ∈ U := fun a ha b hb =>
    hW (Set.mk_mem_prod (hKW ha).1 (hKW hb).2)
  obtain ⟨V, hV0, -, hV⟩ := local_compact_nhds (Filter.univ_mem : Set.univ ∈ 𝓝 (0 : A))
  obtain ⟨L, hLdef⟩ : ∃ L : Set A,
      L = (fun q : A × A × A => q.1 + q.2.1 * q.2.2 + (1 - f) * q.2.2) '' (C ×ˢ V ×ˢ K) :=
    ⟨_, rfl⟩
  have hLc : IsCompact L := by
    rw [hLdef]
    exact (hC.prod (hV.prod hK)).image (by fun_prop)
  obtain ⟨μ, hμ⟩ : ∃ μ : Measure A, μ.IsAddHaarMeasure := ⟨Measure.addHaar, inferInstance⟩
  have hKpos : 0 < μ K := Measure.measure_pos_of_mem_nhds μ hK0
  have hKfin : μ K < ⊤ := hK.measure_lt_top
  have hLfin : μ L < ⊤ := hLc.measure_lt_top
  refine ⟨(μ L / μ K).toNNReal, V, hV0, ?_⟩
  intro u hu1 hfu
  have hmd0 : md u ≠ 0 := by
    intro h0
    have h1 : md u * md u⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel, map_one]
    rw [h0, zero_mul] at h1
    exact zero_ne_one h1
  have hm0 : (md u : ℝ≥0∞) * μ K ≠ 0 := mul_ne_zero (by exact_mod_cast hmd0) hKpos.ne'
  have hmtop : (md u : ℝ≥0∞) * μ K ≠ ⊤ := ENNReal.mul_ne_top ENNReal.coe_ne_top hKfin.ne
  have hLmem : ∀ P : Finset A, (∀ p ∈ P, f * p = p ∧ p ∈ C) →
      ∀ p ∈ P, ∀ w ∈ K, p + (u : A) * w ∈ L := by
    intro P hP p hp w hw
    rw [hLdef]
    refine ⟨(p, f * u, w), ⟨(hP p hp).2, hfu, hw⟩, ?_⟩
    show p + f * u * w + (1 - f) * w = p + u * w
    rw [← hu1]
    ring
  have hB : ∀ P : Finset A, ((∀ p ∈ P, f * p = p ∧ p ∈ C) ∧ ∀ p ∈ P, ∀ q ∈ P, p ≠ q →
      Disjoint ((fun x : A => p + (u : A) * x) '' K) ((fun x : A => q + (u : A) * x) '' K)) →
      P.card ≤ ⌈(μ L / ((md u : ℝ≥0∞) * μ K)).toReal⌉₊ := by
    intro P hP
    have hc := GlobalTheory.CompanionTheory.NullFr.Packing.card_mul_le hmd μ u hK P hP.2 (hLmem P hP.1)
    have h1 : (P.card : ℝ≥0∞) ≤ μ L / ((md u : ℝ≥0∞) * μ K) :=
      (ENNReal.le_div_iff_mul_le (Or.inl hm0) (Or.inl hmtop)).2 hc
    have h2 : (P.card : ℝ) ≤ (μ L / ((md u : ℝ≥0∞) * μ K)).toReal := by
      simpa using ENNReal.toReal_mono (ENNReal.div_ne_top hLfin.ne hm0) h1
    exact_mod_cast h2.trans (Nat.le_ceil _)
  obtain ⟨P, ⟨hPC, hPdisj⟩, hmax⟩ :=
    GlobalTheory.CompanionTheory.NullFr.Packing.exists_max_card (hB := hB) (h0 := ⟨∅, by simp⟩)
  refine ⟨P, hPC, ?_, ?_⟩
  · have hc := GlobalTheory.CompanionTheory.NullFr.Packing.card_mul_le hmd μ u hK P hPdisj (hLmem P hPC)
    have h2 : (((P.card : ℝ≥0) * md u : ℝ≥0) : ℝ≥0∞) ≤ μ L / μ K := by
      rw [ENNReal.le_div_iff_mul_le (Or.inl hKpos.ne') (Or.inl hKfin.ne)]
      push_cast
      rw [mul_assoc]
      exact hc
    calc (P.card : ℝ≥0) * md u = ((((P.card : ℝ≥0) * md u : ℝ≥0) : ℝ≥0∞)).toNNReal := by
          rw [ENNReal.toNNReal_coe]
      _ ≤ (μ L / μ K).toNNReal :=
          ENNReal.toNNReal_mono (ENNReal.div_ne_top hLfin.ne hKpos.ne') h2
  · intro c hc hfc
    by_cases hcP : c ∈ P
    · exact ⟨c, hcP, 0, mem_of_mem_nhds hU, by simp, by simp⟩
    · obtain ⟨p, hp, hpc⟩ : ∃ p ∈ P, ¬ Disjoint ((fun x : A => p + (u : A) * x) '' K)
          ((fun x : A => c + (u : A) * x) '' K) := by
        by_contra hcon
        push_neg at hcon
        have hQ : (∀ p ∈ insert c P, f * p = p ∧ p ∈ C) ∧ ∀ p ∈ insert c P, ∀ q ∈ insert c P,
            p ≠ q → Disjoint ((fun x : A => p + (u : A) * x) '' K)
              ((fun x : A => q + (u : A) * x) '' K) := by
          refine ⟨fun p hp => ?_, fun p hp q hq hpq => ?_⟩
          · rcases Finset.mem_insert.1 hp with rfl | hp'
            · exact ⟨hfc, hc⟩
            · exact hPC p hp'
          · rcases Finset.mem_insert.1 hp with rfl | hp' <;>
              rcases Finset.mem_insert.1 hq with rfl | hq'
            · exact absurd rfl hpq
            · exact (hcon q hq').symm
            · exact hcon p hp'
            · exact hPdisj p hp' q hq' hpq
        have hle := hmax _ hQ
        rw [Finset.card_insert_of_notMem hcP] at hle
        omega
      obtain ⟨x, ⟨k₁, hk₁, hx₁⟩, ⟨k₂, hk₂, hx₂⟩⟩ := Set.not_disjoint_iff.1 hpc
      have hx₁' : p + (u : A) * k₁ = x := hx₁
      have hx₂' : c + (u : A) * k₂ = x := hx₂
      have hw : (u : A) * (k₁ - k₂) = c - p := by linear_combination hx₁' - hx₂'
      have hfp : f * p = p := (hPC p hp).1
      refine ⟨p, hp, k₁ - k₂, hKU k₁ hk₁ k₂ hk₂, ?_, by rw [hw]; ring⟩
      calc f * (k₁ - k₂) = ((u⁻¹ : Aˣ) : A) * ((u : A) * (f * (k₁ - k₂))) := by simp
        _ = ((u⁻¹ : Aˣ) : A) * (f * ((u : A) * (k₁ - k₂))) := by ring
        _ = ((u⁻¹ : Aˣ) : A) * ((u : A) * (k₁ - k₂)) := by rw [hw, mul_sub f c p, hfc, hfp]
        _ = k₁ - k₂ := by simp

end GlobalTheory.CompanionTheory.NullFr.Packing
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MemTwKerIffAverage
section
noncomputable section

namespace GlobalTheory.CompanionTheory.TwistedAverage

open GlobalTheory.PRep

section Coset

variable {H V : Type} [Group H] [AddCommGroup V]

theorem sum_out_refine {N K : Subgroup H} (hNK : N ≤ K) [Fintype (H ⧸ N)] [Fintype (H ⧸ K)]
    [Fintype (K ⧸ N.subgroupOf K)] (f : H → V) (hf : ∀ x, ∀ k ∈ K, f (x * k) = f x) :
    ∑ q : H ⧸ N, f q.out = Fintype.card (K ⧸ N.subgroupOf K) • ∑ q : H ⧸ K, f q.out := by
  have h1 : ∀ q : H ⧸ N, f q.out = f ((Subgroup.quotientEquivProdOfLE hNK q).1).out := by
    intro q
    have hq : (Subgroup.quotientEquivProdOfLE hNK q).1 = (QuotientGroup.mk q.out : H ⧸ K) := by
      conv_lhs => rw [← QuotientGroup.out_eq' q]
      rfl
    rw [hq]
    obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul K q.out
    rw [hh, hf _ _ h.2]
  calc ∑ q : H ⧸ N, f q.out
      = ∑ q : H ⧸ N, f ((Subgroup.quotientEquivProdOfLE hNK q).1).out :=
        Finset.sum_congr rfl fun q _ => h1 q
    _ = ∑ p : (H ⧸ K) × (K ⧸ N.subgroupOf K), f p.1.out :=
        Equiv.sum_comp (Subgroup.quotientEquivProdOfLE hNK) (fun p => f p.1.out)
    _ = Fintype.card (K ⧸ N.subgroupOf K) • ∑ q : H ⧸ K, f q.out := by
        rw [Fintype.sum_prod_type]
        simp only [Finset.sum_const, Finset.card_univ]
        rw [Finset.smul_sum]

theorem sum_out_mul_right (N : Subgroup H) [N.Normal] [Fintype (H ⧸ N)] (f : H → V)
    (hf : ∀ x, ∀ k ∈ N, f (x * k) = f x) (l : H) :
    ∑ q : H ⧸ N, f (q.out * l) = ∑ q : H ⧸ N, f q.out := by
  have h1 : ∀ q : H ⧸ N, f (q.out * l) = f (q * (QuotientGroup.mk l : H ⧸ N)).out := by
    intro q
    have hq : q * (QuotientGroup.mk l : H ⧸ N) = QuotientGroup.mk (q.out * l) := by
      rw [QuotientGroup.mk_mul, QuotientGroup.out_eq']
    rw [hq]
    obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul N (q.out * l)
    rw [hh, hf _ _ h.2]
  calc ∑ q : H ⧸ N, f (q.out * l)
      = ∑ q : H ⧸ N, f (q * (QuotientGroup.mk l : H ⧸ N)).out :=
        Finset.sum_congr rfl fun q _ => h1 q
    _ = ∑ q : H ⧸ N, f q.out :=
        Equiv.sum_comp (Equiv.mulRight (QuotientGroup.mk l : H ⧸ N)) (fun q => f q.out)

end Coset

variable {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V]

def twOrbit (ρ : Representation ℂ G V) (L : Subgroup G) (θ : L →* ℂˣ) (x : V) (t : L) : V :=
  (((θ t)⁻¹ : ℂˣ) : ℂ) • ρ (t : G) x

def stabKer (ρ : Representation ℂ G V) (L : Subgroup G) (θ : L →* ℂˣ) (x : V) : Subgroup L where
  carrier := {l | ρ (l : G) x = x ∧ θ l = 1}
  mul_mem' := by
    rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
    refine ⟨?_, by rw [map_mul, ha', hb', one_mul]⟩
    rw [Subgroup.coe_mul, map_mul, Module.End.mul_apply, hb, ha]
  one_mem' := by simp
  inv_mem' := by
    rintro a ⟨ha, ha'⟩
    refine ⟨?_, by rw [map_inv, ha', inv_one]⟩
    conv_lhs => rw [← ha]
    rw [← Module.End.mul_apply, ← map_mul]
    simp

theorem twOrbit_mul_right (ρ : Representation ℂ G V) (L : Subgroup G) (θ : L →* ℂˣ) (x : V)
    (t k : L) (hk : k ∈ stabKer ρ L θ x) : twOrbit ρ L θ x (t * k) = twOrbit ρ L θ x t := by
  obtain ⟨h1, h2⟩ := hk
  simp only [twOrbit]
  rw [map_mul, h2, mul_one, Subgroup.coe_mul, map_mul, Module.End.mul_apply, h1]

theorem twOrbit_gen (ρ : Representation ℂ G V) (L : Subgroup G) (θ : L →* ℂˣ) (w : V) (l t : L) :
    twOrbit ρ L θ (ρ (l : G) w - (θ l : ℂ) • w) t =
      (θ l : ℂ) • (twOrbit ρ L θ w (t * l) - twOrbit ρ L θ w t) := by
  simp only [twOrbit]
  have h : (θ l : ℂ) * (((θ (t * l))⁻¹ : ℂˣ) : ℂ) = (((θ t)⁻¹ : ℂˣ) : ℂ) := by
    rw [← Units.val_mul, map_mul, mul_inv, mul_comm (θ t)⁻¹, mul_inv_cancel_left]
  rw [smul_sub, smul_smul, h, Subgroup.coe_mul, map_mul, Module.End.mul_apply, map_sub, map_smul,
    smul_sub, smul_smul, smul_smul, mul_comm]

theorem twOrbit_add (ρ : Representation ℂ G V) (L : Subgroup G) (θ : L →* ℂˣ) (x y : V) (t : L) :
    twOrbit ρ L θ (x + y) t = twOrbit ρ L θ x t + twOrbit ρ L θ y t := by
  simp only [twOrbit, map_add, smul_add]

theorem twOrbit_smul (ρ : Representation ℂ G V) (L : Subgroup G) (θ : L →* ℂˣ) (c : ℂ) (x : V)
    (t : L) : twOrbit ρ L θ (c • x) t = c • twOrbit ρ L θ x t := by
  simp only [twOrbit, map_smul]
  rw [smul_comm]

section Top

variable [TopologicalSpace G] [IsTopologicalGroup G]

theorem isOpen_stabKer {ρ : Representation ℂ G V} (hρ : IsSmooth ρ) (L : Subgroup G)
    (θ : L →* ℂˣ) (hθ : IsOpen (θ.ker : Set L)) (x : V) :
    IsOpen (stabKer ρ L θ x : Set L) := by
  have h1 : IsOpen {l : L | ρ (l : G) x = x} := (hρ x).preimage continuous_subtype_val
  have h2 : (stabKer ρ L θ x : Set L) = {l : L | ρ (l : G) x = x} ∩ (θ.ker : Set L) := by
    ext l
    simp [stabKer, MonoidHom.mem_ker]
  rw [h2]
  exact h1.inter hθ

theorem finiteIndex_stabKer {ρ : Representation ℂ G V} (hρ : IsSmooth ρ) {L : Subgroup G}
    (hL : IsCompact (L : Set G)) (θ : L →* ℂˣ) (hθ : IsOpen (θ.ker : Set L)) (x : V) :
    (stabKer ρ L θ x).FiniteIndex := by
  haveI : CompactSpace L := isCompact_iff_compactSpace.mp hL
  haveI : Finite (L ⧸ stabKer ρ L θ x) :=
    Subgroup.quotient_finite_of_isOpen _ (isOpen_stabKer hρ L θ hθ x)
  exact Subgroup.finiteIndex_of_finite_quotient

theorem exists_sum_eq_zero {ρ : Representation ℂ G V} (hρ : IsSmooth ρ) {L : Subgroup G}
    (hL : IsCompact (L : Set G)) (θ : L →* ℂˣ) (hθ : IsOpen (θ.ker : Set L)) {v : V}
    (hv : v ∈ twKer ρ L θ) :
    ∃ M : Subgroup L, M.FiniteIndex ∧ ∀ (N : Subgroup L) [N.Normal] [Fintype (L ⧸ N)], N ≤ M →
      ∑ q : L ⧸ N, twOrbit ρ L θ v q.out = 0 := by
  induction hv using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨l, w, rfl⟩ := hx
    refine ⟨stabKer ρ L θ w, finiteIndex_stabKer hρ hL θ hθ w, ?_⟩
    intro N _ _ hN
    have hf : ∀ x, ∀ k ∈ N, twOrbit ρ L θ w (x * k) = twOrbit ρ L θ w x :=
      fun x k hk => twOrbit_mul_right ρ L θ w x k (hN hk)
    simp only [twOrbit_gen]
    rw [← Finset.smul_sum, Finset.sum_sub_distrib,
      sum_out_mul_right N (twOrbit ρ L θ w) hf l, sub_self, smul_zero]
  | zero =>
    refine ⟨⊤, inferInstance, ?_⟩
    intro N _ _ _
    simp [twOrbit]
  | add x y _ _ hx hy =>
    obtain ⟨M₁, h₁, s₁⟩ := hx
    obtain ⟨M₂, h₂, s₂⟩ := hy
    refine ⟨M₁ ⊓ M₂, inferInstance, ?_⟩
    intro N _ _ hN
    simp only [twOrbit_add]
    rw [Finset.sum_add_distrib, s₁ N (hN.trans inf_le_left), s₂ N (hN.trans inf_le_right), add_zero]
  | smul c x _ hx =>
    obtain ⟨M, h, s⟩ := hx
    refine ⟨M, h, ?_⟩
    intro N _ _ hN
    simp only [twOrbit_smul]
    rw [← Finset.smul_sum, s N hN, smul_zero]

theorem mem_twKer_iff_average (ρ : Representation ℂ G V) (hρ : IsSmooth ρ) (L : Subgroup G)
    (hL : IsCompact (L : Set G)) (θ : L →* ℂˣ) (hθ : IsOpen (θ.ker : Set L)) (v : V) :
    v ∈ twKer ρ L θ ↔ ∃ (K : Subgroup L) (T : Finset L), IsOpen (K : Set L) ∧
      (∀ x ∈ K, ρ (x : G) v = v) ∧ (∀ x ∈ K, θ x = 1) ∧
      (∀ x : L, ∃! t, t ∈ T ∧ t⁻¹ * x ∈ K) ∧
      ∑ t ∈ T, (((θ t)⁻¹ : ℂˣ) : ℂ) • ρ t v = 0 := by
  classical
  constructor
  · intro hv
    obtain ⟨M, hM, hsum⟩ := exists_sum_eq_zero hρ hL θ hθ hv
    haveI hK : (stabKer ρ L θ v).FiniteIndex := finiteIndex_stabKer hρ hL θ hθ v
    haveI : Fintype (L ⧸ stabKer ρ L θ v) := Fintype.ofFinite _
    refine ⟨stabKer ρ L θ v, (Finset.univ : Finset (L ⧸ stabKer ρ L θ v)).image Quotient.out,
      isOpen_stabKer hρ L θ hθ v,
      fun x hx => hx.1, fun x hx => hx.2, ?_, ?_⟩
    · intro x
      refine ⟨(QuotientGroup.mk x : L ⧸ stabKer ρ L θ v).out, ⟨Finset.mem_image_of_mem _
        (Finset.mem_univ _), ?_⟩, ?_⟩
      · exact QuotientGroup.eq.1 (QuotientGroup.out_eq' _)
      · rintro t ⟨ht, hx⟩
        obtain ⟨q, -, rfl⟩ := Finset.mem_image.1 ht
        have : q = (QuotientGroup.mk x : L ⧸ stabKer ρ L θ v) := by
          rw [← QuotientGroup.out_eq' q]
          exact QuotientGroup.eq.2 hx
        rw [this]
    · rw [Finset.sum_image (fun a _ b _ h => Quotient.out_injective h)]
      set C : Subgroup L := (M ⊓ stabKer ρ L θ v).normalCore with hC
      haveI : C.Normal := Subgroup.normalCore_normal _
      haveI : C.FiniteIndex := inferInstance
      haveI : Fintype (L ⧸ C) := Fintype.ofFinite _
      have hCM : C ≤ M ⊓ stabKer ρ L θ v := Subgroup.normalCore_le _
      haveI : Finite (stabKer ρ L θ v ⧸ C.subgroupOf (stabKer ρ L θ v)) := inferInstance
      haveI : Fintype (stabKer ρ L θ v ⧸ C.subgroupOf (stabKer ρ L θ v)) := Fintype.ofFinite _
      have h0 := hsum C (hCM.trans inf_le_left)
      rw [sum_out_refine (hCM.trans inf_le_right) (twOrbit ρ L θ v)
        (fun x k hk => twOrbit_mul_right ρ L θ v x k hk)] at h0
      rw [← Nat.cast_smul_eq_nsmul ℂ, smul_eq_zero] at h0
      rcases h0 with h0 | h0
      · exact absurd h0 (Nat.cast_ne_zero.2 Fintype.card_ne_zero)
      · exact h0
  · rintro ⟨K, T, -, -, -, hT, hsum⟩
    have hne : T.Nonempty := by
      obtain ⟨t, ⟨ht, -⟩, -⟩ := hT 1
      exact ⟨t, ht⟩
    have hc : (T.card : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hne.card_pos.ne'
    have hmem : ∀ t : L, v - (((θ t)⁻¹ : ℂˣ) : ℂ) • ρ (t : G) v ∈ twKer ρ L θ := by
      intro t
      have hg : ρ (t : G) v - (θ t : ℂ) • v ∈ twKer ρ L θ := Submodule.subset_span ⟨t, v, rfl⟩
      have := (twKer ρ L θ).smul_mem (-(((θ t)⁻¹ : ℂˣ) : ℂ)) hg
      convert this using 1
      rw [smul_sub, smul_smul, neg_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, neg_smul,
        neg_smul, one_smul]
      abel
    have hs : (T.card : ℂ) • v = ∑ t ∈ T, (v - (((θ t)⁻¹ : ℂˣ) : ℂ) • ρ (t : G) v) := by
      rw [Finset.sum_sub_distrib, hsum, sub_zero, Finset.sum_const, Nat.cast_smul_eq_nsmul]
    have h1 : (T.card : ℂ) • v ∈ twKer ρ L θ := hs ▸ Submodule.sum_mem _ fun t _ => hmem t
    exact ((twKer ρ L θ).smul_mem_iff hc).1 h1

end Top

end GlobalTheory.CompanionTheory.TwistedAverage
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MonicFactorCoefficientsIntegralStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.monic_factor_coefficients_integral : ∀ (A : Type) [CommRing A] [Algebra ℂ A] (P Q : Polynomial A) (c₁ c₂ : ℂ), P.Monic → Q.Monic → (∀ u : ℂ, IsIntegral ℂ (P.eval (algebraMap ℂ A (u + c₁)) * Q.eval (algebraMap ℂ A (u + c₂)))) → ∀ k, IsIntegral ℂ (P.coeff k) ∧ IsIntegral ℂ (Q.coeff k) := by
  first | exact @GlobalTheory.CompanionTheory.IntFac.isIntegral_coeff_of_shifted_product | exact GlobalTheory.CompanionTheory.IntFac.isIntegral_coeff_of_shifted_product | (intros; apply GlobalTheory.CompanionTheory.IntFac.isIntegral_coeff_of_shifted_product <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MultiplicativeCharacterOnConeStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.multiplicative_character_on_cone : ∀ (a b : ℕ) (q : ℂ), q ≠ 0 → ∀ χ : (Fin a → ℤ) → (Fin b → ℤ) → ℂ, (∀ x x' y y', (∀ i j, i < j → x j + 1 ≤ x i) → (∀ i j, i < j → x' j + 1 ≤ x' i) → (∀ i j, i < j → y j + 1 ≤ y i) → (∀ i j, i < j → y' j + 1 ≤ y' i) → χ (x + x') (y + y') = χ x y * χ x' y') → (∃ x y, (∀ i j, i < j → x j + 1 ≤ x i) ∧ (∀ i j, i < j → y j + 1 ≤ y i) ∧ χ x y ≠ 0) → ∃ (ξa : Fin a → ℂˣ) (ξb : Fin b → ℂˣ), ∀ x y, (∀ i j, i < j → x j + 1 ≤ x i) → (∀ i j, i < j → y j + 1 ≤ y i) → χ x y = q ^ (∑ i : Fin a, ((a : ℤ) - 1 - 2 * (i : ℕ)) * x i) * (∏ i, ((ξa i ^ x i : ℂˣ) : ℂ)) * (q ^ (∑ i : Fin b, ((b : ℤ) - 1 - 2 * (i : ℕ)) * y i) * ∏ i, ((ξb i ^ y i : ℂˣ) : ℂ)) := by
  first | exact @GlobalTheory.CompanionTheory.StrictCone.mul_on_cone_eq_delta_char | exact GlobalTheory.CompanionTheory.StrictCone.mul_on_cone_eq_delta_char | (intros; apply GlobalTheory.CompanionTheory.StrictCone.mul_on_cone_eq_delta_char <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MultiplicativityFinitePlaces
section
open Matrix PositivityTheory.Rg.BcB.D1

namespace GlobalTheory.CompanionTheory.WedgeMinor

theorem det_mul_submatrix_expand {K ι ι' κ : Type} [CommRing K] [Fintype ι] [Fintype κ]
    [DecidableEq κ] (g : Matrix ι' ι K) (A : Matrix ι κ K) (t : κ → ι') :
    ((g * A).submatrix t id).det =
      ∑ s : κ → ι, (∏ i, g (t i) (s i)) * (A.submatrix s id).det := by
  have h : ((g * A).submatrix t id : κ → κ → K) = fun i => ∑ k, g (t i) k • A k := by
    funext i j
    simp [Matrix.mul_apply, Finset.sum_apply]
  have key : ∀ M : Matrix κ κ K,
      M.det = (detRowAlternating (R := K) (n := κ)).toMultilinearMap M := fun _ => rfl
  rw [key, h, MultilinearMap.map_sum]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [MultilinearMap.map_smul_univ, smul_eq_mul]
  rfl

theorem sz_nonneg {K ι κ : Type} [NormedField K] (g : Matrix ι κ K) : 0 ≤ sz g :=
  Real.iSup_nonneg fun _ => norm_nonneg _

theorem le_sz {K ι κ : Type} [NormedField K] [Finite ι] [Finite κ] (g : Matrix ι κ K)
    (i : ι) (j : κ) : ‖g i j‖ ≤ sz g :=
  le_ciSup (f := fun p : ι × κ => ‖g p.1 p.2‖) (Set.finite_range _).bddAbove (i, j)

theorem nF_nonneg {K ι κ : Type} [NormedField K] [Fintype κ] [DecidableEq κ]
    (A : Matrix ι κ K) : 0 ≤ nF A :=
  Real.iSup_nonneg fun _ => norm_nonneg _

theorem le_nF {K ι κ : Type} [NormedField K] [Finite ι] [Fintype κ] [DecidableEq κ]
    (A : Matrix ι κ K) (s : κ → ι) : ‖(A.submatrix s id).det‖ ≤ nF A :=
  le_ciSup (f := fun s : κ → ι => ‖(A.submatrix s id).det‖) (Set.finite_range _).bddAbove s

theorem norm_minor_mul_le {K ι ι' κ : Type} [NormedField K] [IsUltrametricDist K] [Fintype ι]
    [Fintype ι'] [Fintype κ] [DecidableEq κ] (g : Matrix ι' ι K) (A : Matrix ι κ K) (t : κ → ι') :
    ‖((g * A).submatrix t id).det‖ ≤ sz g ^ Fintype.card κ * nF A := by
  rw [det_mul_submatrix_expand]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg
    (mul_nonneg (pow_nonneg (sz_nonneg g) _) (nF_nonneg A)) fun s _ => ?_
  rw [norm_mul, norm_prod]
  refine mul_le_mul ?_ (le_nF A s) (norm_nonneg _) (pow_nonneg (sz_nonneg g) _)
  calc ∏ i, ‖g (t i) (s i)‖ ≤ ∏ _i : κ, sz g :=
        Finset.prod_le_prod (fun _ _ => norm_nonneg _) fun i _ => le_sz g _ _
    _ = sz g ^ Fintype.card κ := by simp

theorem nF_mul_le {K ι ι' κ : Type} [NormedField K] [IsUltrametricDist K] [Fintype ι]
    [Fintype ι'] [Fintype κ] [DecidableEq κ] (g : Matrix ι' ι K) (A : Matrix ι κ K) :
    nF (g * A) ≤ sz g ^ Fintype.card κ * nF A :=
  Real.iSup_le (fun t => norm_minor_mul_le g A t)
    (mul_nonneg (pow_nonneg (sz_nonneg g) _) (nF_nonneg A))

theorem nF_mul_right {K ι κ : Type} [NormedField K] [Fintype ι] [Fintype κ] [DecidableEq κ]
    (A : Matrix ι κ K) (s : Matrix κ κ K) : nF (A * s) = nF A * ‖s.det‖ := by
  unfold nF
  rw [Real.iSup_mul_of_nonneg (norm_nonneg _)]
  refine iSup_congr fun t => ?_
  have h : (A * s).submatrix t id = A.submatrix t id * s := by
    ext i j
    simp [Matrix.mul_apply]
  rw [h, det_mul, norm_mul]

theorem nF_square {K κ : Type} [NormedField K] [Fintype κ] [DecidableEq κ]
    (s : Matrix κ κ K) : nF s = ‖s.det‖ := by
  refine le_antisymm (Real.iSup_le (fun t => ?_) (norm_nonneg _)) ?_
  · by_cases ht : Function.Injective t
    · have hb : Function.Bijective t := Finite.injective_iff_bijective.mp ht
      have h := Matrix.det_permute (Equiv.ofBijective t hb) s
      have h' : (s.submatrix t id).det = _ := h
      rw [h', norm_mul]
      rcases Int.units_eq_one_or (Equiv.Perm.sign (Equiv.ofBijective t hb)) with h1 | h1 <;>
        simp [h1]
    · obtain ⟨i, j, hij, hne⟩ : ∃ i j, t i = t j ∧ i ≠ j := by
        simpa [Function.Injective] using ht
      rw [Matrix.det_zero_of_row_eq hne (by funext k; simp [hij])]
      simp
  · simpa using le_nF s id

theorem mulF : MulF := by
  intro K ι ι' κ _ _ _ _ _ _ A
  exact ⟨fun g => nF_mul_le g A, fun s => nF_mul_right A s, fun s => nF_square s⟩

end GlobalTheory.CompanionTheory.WedgeMinor
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MultisetAntitoneEnumerationStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.multiset_antitone_enumeration : ∀ {α : Type*} (m : Multiset α) (f : α → ℝ) (P : α → α → Prop), (∀ a b, P a b → f a < f b) → ∃ (h : ℕ) (Δ : Fin h → α), Finset.univ.val.map Δ = m ∧ Antitone (f ∘ Δ) ∧ ∀ i j, i < j → ¬ P (Δ i) (Δ j) := by
  first | exact @GlobalTheory.CompanionTheory.Multiset.exists_antitone_listing | exact GlobalTheory.CompanionTheory.Multiset.exists_antitone_listing | (intros; apply GlobalTheory.CompanionTheory.Multiset.exists_antitone_listing <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NotMemLpOfGrowthStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.not_mem_Lp_of_growth : ∀ {X : Type} [MeasurableSpace X] (μ : MeasureTheory.Measure X) (f : X → ℝ) (p : ℝ), 0 < p → MeasureTheory.MemLp f (ENNReal.ofReal p) μ → ∀ (E : ℕ → Set X), (∀ j, MeasurableSet (E j)) → Pairwise (Function.onFun Disjoint E) → ∀ (c D B r : ℝ), 0 < c → 0 < B → 0 ≤ r → (∀ j : ℕ, ENNReal.ofReal (c * D ^ j) ≤ μ (E j)) → (∀ j : ℕ, ∀ x ∈ E j, B * r ^ j ≤ |f x|) → D * r ^ p < 1 := by
  first | exact @GlobalTheory.CompanionTheory.Casselman.mul_rpow_lt_one_of_memLp_geometric | exact GlobalTheory.CompanionTheory.Casselman.mul_rpow_lt_one_of_memLp_geometric | (intros; apply GlobalTheory.CompanionTheory.Casselman.mul_rpow_lt_one_of_memLp_geometric <;> assumption)
end

