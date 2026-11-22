import PositivityTheory.AutomorphicForms.PublishedInputs.JacquetLanglands.TorusKernels.IsHolVOf
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0024
import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.ShortLatticeUnitarize.CompactBoxLattices.Bundle0001
import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.ScalarStabilizers.FinSupp

-- bundled from PositivityTheory.AutomorphicForms.PublishedInputs.JacquetLanglands.TorusKernels.PfTrCong
section
noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Base UpperTheory.V.Sd UpperTheory.V.Sd.Wc
open scoped Matrix NNReal

namespace UpperTheory.Esk.TraceCongruenceBounds

open UpperTheory.Esk

theorem nu_two {l : ℕ} [Fact l.Prime] (hl : l ≠ 2) (ι : Qbar l ≃+* ℂ) : nu ι 2 = 1 := by
  have hle : ∀ m : ℕ, nu ι (m : ℂ) ≤ 1 := by
    intro m
    induction m with
    | zero => simp
    | succ m ih => rw [Nat.cast_succ]; exact (nu ι).map_add_le ih (by simp)
  have hlt : nu ι (l : ℂ) < 1 := by
    rw [nu_apply, map_natCast, ← NNReal.coe_lt_coe, coe_nnnorm, NNReal.coe_one]
    rw [← map_natCast (algebraMap ℚ_[l] (PadicAlgCl l)) l]
    exact lt_of_eq_of_lt (PadicAlgCl.norm_extends l _) Padic.norm_p_lt_one
  obtain ⟨m, hm⟩ := (Fact.out : l.Prime).odd_of_ne_two hl
  refine le_antisymm (by simpa using hle 2) (not_lt.1 fun h2 => ?_)
  have e : (1 : ℂ) = (l : ℂ) - 2 * (m : ℂ) := by rw [hm]; push_cast; ring
  have : nu ι ((l : ℂ) - 2 * (m : ℂ)) < 1 := by
    refine (nu ι).map_sub_lt hlt ?_
    rw [map_mul]
    exact lt_of_le_of_lt (mul_le_of_le_one_right' (hle m)) h2
  rw [← e, map_one] at this
  exact lt_irrefl _ this

theorem sum_bound (ν : Valuation ℂ ℝ≥0) {β : Type*} (s : Finset β) (u x y : β → ℂ) (m : ℝ≥0)
    (hu : ∀ j ∈ s, ν (u j) ≤ 1)
    (h : ∀ j ∈ s, u j ≠ 0 → ν (x j) ≤ 1 ∧ ν (y j) ≤ 1 ∧ ν (x j - y j) ≤ m) :
    ν (∑ j ∈ s, u j * x j) ≤ 1 ∧ ν (∑ j ∈ s, u j * y j) ≤ 1 ∧
      ν (∑ j ∈ s, u j * x j - ∑ j ∈ s, u j * y j) ≤ m := by
  have key : ∀ j ∈ s, ∀ (z : ℂ) (b : ℝ≥0), (u j ≠ 0 → ν z ≤ b) → ν (u j * z) ≤ b := by
    intro j hj z b hz
    by_cases h0 : u j = 0
    · simp [h0]
    · rw [map_mul]
      exact le_trans (mul_le_mul' (hu j hj) (hz h0)) (by simp)
  refine ⟨ν.map_sum_le fun j hj => key j hj _ _ fun h0 => (h j hj h0).1,
    ν.map_sum_le fun j hj => key j hj _ _ fun h0 => (h j hj h0).2.1, ?_⟩
  rw [← Finset.sum_sub_distrib]
  refine ν.map_sum_le fun j hj => ?_
  rw [← mul_sub]
  exact key j hj _ _ fun h0 => (h j hj h0).2.2

theorem geo_expand {F I Gf : Type} [Field F] [Group Gf] [Fintype I] (D : Dat F I Gf) (k : I → ℕ) {n : ℕ}
    (a : Fin n → Gf) (S : Finset (D.Cj × D.Om)) (z : ℂ) :
    z * geo D k a S = ∑ q ∈ S ×ˢ (Finset.univ : Finset (Fin n)),
      ((Nat.card (MulAction.stabilizer (PG F) q.1) : ℂ)⁻¹ *
        D.ee ((D.rep q.1.2)⁻¹ * (D.j (D.el q.1.1).out)⁻¹ * D.rep q.1.2 * a q.2)) *
      (z * D.orb k (D.el q.1.1).out) := by
  rw [Finset.sum_product, geo, Finset.mul_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [Dat.Te, Finset.sum_mul, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

theorem ee_mem {F I Gf : Type} [Field F] [Group Gf] (D : Dat F I Gf) {x : Gf} (h : D.ee x ≠ 0) : x ∈ D.H := by
  by_contra hx
  exact h (by simp [Dat.ee, hx])

theorem nu_ee {l : ℕ} [Fact l.Prime] (ι : Qbar l ≃+* ℂ) {F I Gf : Type} [Field F] [Group Gf] (D : Dat F I Gf)
    {m : ℕ} (hm0 : 0 < m) (hm : ∀ h, D.χ h ^ m = 1) (x : Gf) : nu ι (D.ee x) ≤ 1 := by
  unfold Dat.ee
  split_ifs with hx
  · have e : (nu ι (D.χ ⟨x, hx⟩ : ℂ)) ^ m = 1 := by
      rw [← map_pow, ← Units.val_pow_eq_pow_val, hm, Units.val_one, map_one]
    exact (pow_le_one_iff hm0.ne').1 e.le
  · simp

theorem nu_card {l : ℕ} [Fact l.Prime] (hl : l ≠ 2) (ι : Qbar l ≃+* ℂ) {G : Type*} [Group G] (S : Subgroup G)
    (hS : ∃ n, Nat.card S = 2 ^ n) : nu ι ((Nat.card S : ℂ)⁻¹) = 1 := by
  obtain ⟨n, hn⟩ := hS
  rw [map_inv₀, hn, Nat.cast_pow, map_pow, Nat.cast_ofNat, nu_two hl, one_pow, inv_one]

theorem stab_le {G A B : Type*} [Group G] [MulAction G A] [MulAction G B] (p : A × B) :
    MulAction.stabilizer G p ≤ MulAction.stabilizer G p.2 := fun g hg => by
  rw [MulAction.mem_stabilizer_iff] at hg ⊢
  exact congrArg Prod.snd hg

theorem geo_bound (ν : Valuation ℂ ℝ≥0) {F I Gf : Type} [Field F] [Group Gf] [Fintype I] (D : Dat F I Gf)
    (k k' : I → ℕ) {n : ℕ} (a : Fin n → Gf) (S : Finset (D.Cj × D.Om)) (z z' : ℂ) (m : ℝ≥0)
    (hu : ∀ p ∈ S, ∀ i, ν ((Nat.card (MulAction.stabilizer (PG F) p) : ℂ)⁻¹ *
        D.ee ((D.rep p.2)⁻¹ * (D.j (D.el p.1).out)⁻¹ * D.rep p.2 * a i)) ≤ 1)
    (h : ∀ p ∈ S, ∀ i, D.ee ((D.rep p.2)⁻¹ * (D.j (D.el p.1).out)⁻¹ * D.rep p.2 * a i) ≠ 0 →
      ν (z * D.orb k (D.el p.1).out) ≤ 1 ∧ ν (z' * D.orb k' (D.el p.1).out) ≤ 1 ∧
        ν (z * D.orb k (D.el p.1).out - z' * D.orb k' (D.el p.1).out) ≤ m) :
    ν (z * geo D k a S) ≤ 1 ∧ ν (z' * geo D k' a S) ≤ 1 ∧ ν (z * geo D k a S - z' * geo D k' a S) ≤ m := by
  rw [geo_expand, geo_expand]
  refine sum_bound ν _ _ _ _ m (fun q hq => hu q.1 (Finset.mem_product.1 hq).1 q.2) fun q hq hne => ?_
  exact h q.1 (Finset.mem_product.1 hq).1 q.2 (right_ne_zero_of_mul hne)

end UpperTheory.Esk.TraceCongruenceBounds

open UpperTheory.Esk UpperTheory.Esk.TraceCongruenceBounds in
theorem UpperTheory.Esk.pf_TrCong : UpperTheory.Esk.TF → UpperTheory.Esk.DAx → UpperTheory.Esk.DTwo → UpperTheory.Esk.DGood → UpperTheory.Esk.GTerm → UpperTheory.Esk.H0b → UpperTheory.Esk.HFin → UpperTheory.Esk.TrCong := by
  intro hTF hDAx hTwo hGood hGT hH0b hFin
  intro F _ _ _ hd l _ hl ι L k₀ hk₀ c hc hcL hu ω χ hω hχ hS N t ht W r hr hW n a hreps h h'
  obtain ⟨⟨m, hm0, hm⟩, hsg⟩ := hH0b F (fun _ => k₀) c ω χ hω hχ
  have hS' : Sgn (fun v => k₀ + 2 * t v) ω := fun v => by
    rw [hS v, pow_add, pow_mul]; simp
  have hax : (mkDat c χ).Ax := hDAx F hd c hc χ ⟨m, hm0, hm⟩
  obtain ⟨hgood, hreg⟩ := hGood F c ω χ hχ W n a hreps
  have hreg' : (mkDat c χ).Reg a := by
    apply hreg
    obtain ⟨v⟩ : Nonempty (InfinitePlace F) := inferInstance
    classical
    exact ⟨L.pl v, List.count_pos_iff.1 (le_trans hr (hW v)), by rw [hcL v]; exact one_ne_zero⟩
  obtain ⟨S, hFam, hT⟩ := hTF F (InfinitePlace F) (GF F) (mkDat c χ) hax (Fin n) a
  have hyp0 : (mkDat c χ).Hyp (fun _ => k₀) a := ⟨hax, fun _ => hk₀, (hsg hS).1, hgood, hreg'⟩
  have hyp1 : (mkDat c χ).Hyp (fun v => k₀ + 2 * t v) a :=
    ⟨hax, fun _ => by omega, ((hH0b F _ c ω χ hω hχ).2 hS').1, hgood, hreg'⟩
  have fd0 : FiniteDimensional ℂ ((mkDat c χ).M fun _ => k₀) := hFin F _ c hc ω χ hω hχ hS fun _ => by omega
  have fd1 : FiniteDimensional ℂ ((mkDat c χ).M fun v => k₀ + 2 * t v) :=
    hFin F _ c hc ω χ hω hχ hS' fun _ => by omega
  rw [hT _ hyp0 fd0 h, hT _ hyp1 fd1 h']
  refine geo_bound (nu ι) (mkDat c χ) _ _ a S _ _ _ ?_ ?_
  · intro p hp i
    have hp' := hFam p hp
    rw [map_mul, nu_card hl ι _ (hTwo F c χ hu p.2 _ (stab_le p) hp'.2), one_mul]
    exact nu_ee ι _ hm0 hm _
  · intro p hp i hne
    exact hGT F l ι L c χ hcL k₀ (by omega) N t ht W r hr hW n a hreps _ _ i (hFam p hp).1 (ee_mem _ hne)
end
end

-- bundled from PositivityTheory.AutomorphicForms.PublishedInputs.JacquetLanglands.TorusKernels.ValNatCastLe
section
noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Base UpperTheory.V.Sd UpperTheory.V.Sd.Wc
open scoped Matrix NNReal

namespace UpperTheory.Esk.adelicTermLemmas

theorem ch_map {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (a b : R) (n : ℕ) :
    f (ch a b n) = ch (f a) (f b) n := by
  have key : ∀ n, f (ch a b n) = ch (f a) (f b) n ∧ f (ch a b (n + 1)) = ch (f a) (f b) (n + 1) := by
    intro n
    induction n with
    | zero => simp [ch]
    | succ n ih =>
      refine ⟨ih.2, ?_⟩
      simp only [ch, map_sub, map_mul, ih.1, ih.2]
  exact (key n).1

theorem ch_hom {R : Type*} [CommRing R] (s τ δ : R) (n : ℕ) :
    ch (s * τ) (s ^ 2 * δ) (n + 1) = s ^ n * ch τ δ (n + 1) := by
  have key : ∀ n, ch (s * τ) (s ^ 2 * δ) (n + 1) = s ^ n * ch τ δ (n + 1) ∧
      ch (s * τ) (s ^ 2 * δ) (n + 2) = s ^ (n + 1) * ch τ δ (n + 2) := by
    intro n
    induction n with
    | zero => simp [ch]
    | succ n ih =>
      refine ⟨ih.2, ?_⟩
      have e : ch (s * τ) (s ^ 2 * δ) (n + 1 + 2) =
          s * τ * ch (s * τ) (s ^ 2 * δ) (n + 2) - s ^ 2 * δ * ch (s * τ) (s ^ 2 * δ) (n + 1) := rfl
      have e' : ch τ δ (n + 1 + 2) = τ * ch τ δ (n + 2) - δ * ch τ δ (n + 1) := rfl
      rw [e, e', ih.1, ih.2]
      ring
  exact (key n).1

theorem val_prod_sub {ι : Type*} (ν : Valuation ℂ ℝ≥0) (s : Finset ι) (f g : ι → ℂ) (m : ℝ≥0)
    (hf : ∀ i ∈ s, ν (f i) ≤ 1) (hg : ∀ i ∈ s, ν (g i) ≤ 1) (hfg : ∀ i ∈ s, ν (f i - g i) ≤ m) :
    ν (∏ i ∈ s, f i) ≤ 1 ∧ ν (∏ i ∈ s, g i) ≤ 1 ∧ ν (∏ i ∈ s, f i - ∏ i ∈ s, g i) ≤ m :=
  _root_.UpperTheory.Reformulated.B.ProdSubProdLeOfFactorsClose.main ν s f g m hf hg hfg

open Classical in
theorem nz_prod {F : Type} [Field F] [NumberField F] {l : ℕ} [Fact l.Prime] {ι : Qbar l ≃+* ℂ} (D : LDat F ι) (k₀ : ℕ)
    (t : InfinitePlace F → ℕ) (W : List (Pl F)) :
    (W.map (nz D k₀ t)).prod =
      (W.map fun w => ((((normV w : ℝ) ^ ((k₀ : ℝ) / 2 - 1) : ℝ)) : ℂ)).prod * ∏ v, (l : ℂ) ^ (t v * W.count (D.pl v)) := by
  induction W with
  | nil => simp
  | cons w W ih =>
    rw [List.map_cons, List.prod_cons, ih, List.map_cons, List.prod_cons]
    have e : ∀ v, (l : ℂ) ^ (t v * (w :: W).count (D.pl v)) =
        (if D.pl v = w then (l : ℂ) ^ t v else 1) * (l : ℂ) ^ (t v * W.count (D.pl v)) := by
      intro v
      rw [List.count_cons]
      by_cases h : D.pl v = w
      · subst h
        rw [if_pos rfl]
        simp [mul_add, pow_add]
        try ring
      · have h' : ¬ (w == D.pl v) = true := by
          rw [beq_iff_eq]; exact fun e => h e.symm
        simp [h, h']
    simp only [e, Finset.prod_mul_distrib, nz]
    ring

theorem local_cong (ν : Valuation ℂ ℝ≥0) (hG : GCh) (τ δ U : ℂ) (m : ℝ≥0) (k₀ t : ℕ) (hk : 2 ≤ k₀) (hτ : ν τ ≤ 1)
    (hδ1 : ν δ ≤ 1) (hδ : ν δ ≤ m) (hτt : ν (τ ^ (2 * t) - 1) ≤ m) (hU1 : ν U ≤ 1) (hU : ν (U ^ t - 1) ≤ m) :
    ν (ch τ δ (k₀ - 1)) ≤ 1 ∧ ν (ch τ δ (k₀ + 2 * t - 1) * U ^ t) ≤ 1 ∧
      ν (ch τ δ (k₀ - 1) - ch τ δ (k₀ + 2 * t - 1) * U ^ t) ≤ m := by
  obtain ⟨n, rfl⟩ : ∃ n, k₀ = n + 2 := ⟨k₀ - 2, by omega⟩
  have e0 : n + 2 - 1 = n + 1 := by omega
  have e1 : n + 2 + 2 * t - 1 = (n + 2 * t) + 1 := by omega
  rw [e0, e1]
  obtain ⟨A1, A2⟩ := hG ν τ δ hτ hδ1 n
  obtain ⟨B1, B2⟩ := hG ν τ δ hτ hδ1 (n + 2 * t)
  have hUt : ν (U ^ t) ≤ 1 := by rw [map_pow]; exact pow_le_one₀ (by positivity) hU1
  refine ⟨A1, ?_, ?_⟩
  · rw [map_mul]; exact mul_le_one' B1 hUt
  · have e : ch τ δ (n + 1) - ch τ δ (n + 2 * t + 1) * U ^ t =
        (ch τ δ (n + 1) - τ ^ n) + (τ ^ n * (1 - τ ^ (2 * t))) + (τ ^ (n + 2 * t) - ch τ δ (n + 2 * t + 1)) +
          ch τ δ (n + 2 * t + 1) * (1 - U ^ t) := by ring
    rw [e]
    have hτn : ν (τ ^ n) ≤ 1 := by rw [map_pow]; exact pow_le_one₀ (by positivity) hτ
    refine ν.map_add_le (ν.map_add_le (ν.map_add_le (A2.trans hδ) ?_) ?_) ?_
    · rw [map_mul, ν.map_sub_swap]
      exact (mul_le_of_le_one_left (by positivity) hτn).trans hτt
    · rw [ν.map_sub_swap]; exact B2.trans hδ
    · rw [map_mul, ν.map_sub_swap]
      exact (mul_le_of_le_one_left (by positivity) B1).trans hU

end UpperTheory.Esk.adelicTermLemmas
end
end

-- bundled from PositivityTheory.AutomorphicForms.PublishedInputs.JacquetLanglands.TorusKernels.ValuationDetCongruenceSubgroupEqOne
section
noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Base UpperTheory.V.Sd UpperTheory.V.Sd.Wc
open scoped Matrix NNReal

namespace UpperTheory.Esk.adelicTermLemmas

variable {F : Type} [Field F] [NumberField F]

theorem hc_decomp {c : Pl F → ℕ} {h : GF F} (hh : h ∈ Hc c) : ∃ k ∈ Kc c, ∃ z, h = k * zc F z := by
  have hN : (zc F).range.Normal := ⟨fun n hn g => by
    obtain ⟨z, rfl⟩ := hn
    refine ⟨z, ?_⟩
    rw [(Subgroup.mem_center_iff.1 (zc_center z) g), mul_assoc, mul_inv_cancel, mul_one]⟩
  have h2 : h ∈ ((Kc c ⊔ (zc F).range : Subgroup (GF F)) : Set (GF F)) := hh
  rw [Subgroup.mul_normal] at h2
  obtain ⟨k, hk, y, ⟨z, rfl⟩, rfl⟩ := h2
  exact ⟨k, hk, z, rfl⟩

theorem valuation_det_congruence_subgroup_eq_one (w : Pl F) (n : ℕ) {g : GL (Fin 2) (w.adicCompletion F)} (hg : g ∈ K1 w n) :
    Valued.v (g : Matrix (Fin 2) (Fin 2) (w.adicCompletion F)).det = 1 := by
  obtain ⟨k, -, rfl⟩ := hg
  have hu : IsUnit (k : Matrix (Fin 2) (Fin 2) (w.adicCompletionIntegers F)).det :=
    (Matrix.GeneralLinearGroup.det k).isUnit
  rw [HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one] at hu
  rw [← hu]
  exact congrArg Valued.v ((w.adicCompletionIntegers F).subtype.map_det _).symm

theorem mem_local_congruence_of_mem_global {c : Pl F → ℕ} {k : GF F} (hk : k ∈ Kc c) (w : Pl F) :
    Matrix.GeneralLinearGroup.map (pLoc F w) k ∈ K1 w (c w) := by
  have := Subgroup.mem_iInf.1 hk w
  exact this

theorem list_prod_inv {α : Type*} (W : List α) (f : α → ℝ) : (W.map fun w => (f w)⁻¹).prod = ((W.map f).prod)⁻¹ := by
  induction W with
  | nil => simp
  | cons w W ih => simp [ih, mul_comm]

theorem det_zc (z : (Af F)ˣ) : Matrix.GeneralLinearGroup.det (zc F z) = z ^ 2 := by
  ext
  simp [zc, sq]

variable [IsTotallyReal F]

theorem absF_det_Kc {c : Pl F → ℕ} {k : GF F} (hk : k ∈ Kc c) : absF (Matrix.GeneralLinearGroup.det k) = 1 := by
  refine (Hm.absf F).2.2.1 _ fun w => ?_
  have h := valuation_det_congruence_subgroup_eq_one w (c w) (mem_local_congruence_of_mem_global hk w)
  rw [Matrix.GeneralLinearGroup.val_det_apply, RingHom.map_det]
  exact h

theorem prod_reAt {c : Pl F → ℕ} {W : List (Pl F)} {n : ℕ} {a : Fin n → GF F} (hR : IsReps c W a) {γ : GL (Fin 2) F}
    {x : GF F} {i : Fin n} {k : GF F} (hk : k ∈ Kc c) {z : (Af F)ˣ} (hrel : jF F γ * x * (k * zc F z) = x * a i) :
    ∏ v, |reAt v γ.val.det| = absF z ^ 2 * (W.map fun w => (normV w : ℝ)).prod := by
  have h1 := (Hm.absf F).2.2.2 (Matrix.GeneralLinearGroup.det γ)
  have h2 : Units.map (algebraMap F (Af F)).toMonoidHom (Matrix.GeneralLinearGroup.det γ) =
      Matrix.GeneralLinearGroup.det (jF F γ) := by
    rw [jF, Matrix.GeneralLinearGroup.map_det]; rfl
  have h3 : Matrix.GeneralLinearGroup.det (jF F γ) * (Matrix.GeneralLinearGroup.det k * z ^ 2) =
      Matrix.GeneralLinearGroup.det (a i) := by
    have := congrArg Matrix.GeneralLinearGroup.det hrel
    simp only [map_mul, det_zc] at this
    have e : Matrix.GeneralLinearGroup.det x * (Matrix.GeneralLinearGroup.det (jF F γ) * (Matrix.GeneralLinearGroup.det k * z ^ 2)) =
        Matrix.GeneralLinearGroup.det x * Matrix.GeneralLinearGroup.det (a i) := by
      rw [← this, ← mul_assoc, ← mul_assoc, ← mul_assoc, mul_comm (Matrix.GeneralLinearGroup.det x)]
    exact mul_left_cancel e
  have h4 := congrArg absF h3
  rw [(Hm.absf F).2.1, (Hm.absf F).2.1, absF_det_Kc hk, pow_two, (Hm.absf F).2.1, hR.det i] at h4
  rw [list_prod_inv] at h4
  rw [h2] at h1
  have hp : 0 < absF (Matrix.GeneralLinearGroup.det (jF F γ)) := (Hm.absf F).1 _
  have hz : 0 < absF z := (Hm.absf F).1 _
  have hN : (W.map fun w => (normV w : ℝ)).prod ≠ 0 := by
    intro h0
    rw [h0, inv_zero] at h4
    have : 0 < absF (Matrix.GeneralLinearGroup.det (jF F γ)) * (1 * (absF z * absF z)) := by positivity
    linarith
  have e1 : (∏ v, |reAt v γ.val.det|) = (absF (Matrix.GeneralLinearGroup.det (jF F γ)))⁻¹ := by
    rw [Matrix.GeneralLinearGroup.val_det_apply] at h1
    exact eq_inv_of_mul_eq_one_left h1
  rw [e1]
  rw [one_mul] at h4
  field_simp
  have h5 : absF (Matrix.GeneralLinearGroup.det (jF F γ)) * (absF z * absF z) * (W.map fun w => (normV w : ℝ)).prod = 1 := by
    rw [h4, inv_mul_cancel₀ hN]
  nlinarith [h5]

theorem val_nat_le (ν : Valuation ℂ ℝ≥0) (m : ℕ) : ν (m : ℂ) ≤ 1 := by
  induction m with
  | zero => simp
  | succ m ih =>
    push_cast
    exact (Valuation.map_add ν _ _).trans (max_le ih (by simp))

theorem tr_conj {R : Type*} [CommRing R] (g y : GL (Fin 2) R) :
    ((g * y * g⁻¹ : GL (Fin 2) R) : Matrix (Fin 2) (Fin 2) R).trace = (y : Matrix (Fin 2) (Fin 2) R).trace := by
  rw [Units.val_mul, Units.val_mul, Matrix.trace_mul_comm, ← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul]

theorem det_conj2 {R : Type*} [CommRing R] (g y : GL (Fin 2) R) :
    ((g * y * g⁻¹ : GL (Fin 2) R) : Matrix (Fin 2) (Fin 2) R).det = (y : Matrix (Fin 2) (Fin 2) R).det := by
  rw [← Matrix.GeneralLinearGroup.val_det_apply, ← Matrix.GeneralLinearGroup.val_det_apply]
  congr 1
  simp

section Loc

variable {l : ℕ} [Fact l.Prime] {ι : Qbar l ≃+* ℂ} (D : LDat F ι)

theorem nu_eq_one_iff (v : InfinitePlace F) (y : (D.pl v).adicCompletion F) : nu ι (D.em v y) = 1 ↔ Valued.v y = 1 := by
  constructor
  · intro h
    rcases lt_or_eq_of_le ((D.le v y).1 h.le) with h2 | h2
    · exact absurd ((D.lt v y).2 h2) (by rw [h]; exact lt_irrefl 1)
    · exact h2
  · intro h
    rcases lt_or_eq_of_le ((D.le v y).2 h.le) with h2 | h2
    · exact absurd ((D.lt v y).1 h2) (by rw [h]; exact lt_irrefl 1)
    · exact h2

theorem gl_apply (v : InfinitePlace F) (y : GF F) (p q : Fin 2) :
    (D.gl y v : Matrix (Fin 2) (Fin 2) ℂ) p q =
      D.em v ((↑(Matrix.GeneralLinearGroup.map (pLoc F (D.pl v)) y) : Matrix (Fin 2) (Fin 2) ((D.pl v).adicCompletion F)) p q) := rfl

theorem gl_zc (v : InfinitePlace F) (y : (Af F)ˣ) :
    (D.gl (zc F y) v : Matrix (Fin 2) (Fin 2) ℂ) = D.ea v y • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  ext p q
  rw [gl_apply]
  fin_cases p <;> fin_cases q <;> simp [zc, LDat.ea]

open Classical in
theorem loc (hU : GUnit) {c : Pl F → ℕ} (hc : ∀ v, c (D.pl v) = 1) {W : List (Pl F)} {r : ℕ} (hr : 1 ≤ r)
    (hW : ∀ v, r ≤ W.count (D.pl v)) {n : ℕ} {a : Fin n → GF F} (hR : IsReps c W a) {γ : GL (Fin 2) F} {x : GF F} {i : Fin n}
    {k : GF F} (hk : k ∈ Kc c) {z : (Af F)ˣ} (hrel : jF F γ = x * (a i * k⁻¹ * zc F z⁻¹) * x⁻¹) (v : InfinitePlace F) (N : ℕ) :
    ∃ τ δ U : ℂ, v.embedding γ.val.trace = (D.ea v z)⁻¹ * τ ∧ v.embedding γ.val.det = ((D.ea v z)⁻¹) ^ 2 * δ ∧
      nu ι τ ≤ 1 ∧ nu ι δ ≤ 1 ∧ nu ι δ ≤ nu ι l ^ r ∧ nu ι U ≤ 1 ∧ δ * U = (l : ℂ) ^ W.count (D.pl v) ∧
      ∀ t : ℕ, (l - 1) * l ^ N ∣ t → nu ι (τ ^ (2 * t) - 1) ≤ nu ι l ^ N ∧ nu ι (U ^ t - 1) ≤ nu ι l ^ N := by
  have hea : ∀ y : F, D.em v (pLoc F (D.pl v) (algebraMap F (Af F) y)) = v.embedding y := fun y => D.em_alg v y
  obtain ⟨hK, -⟩ := (glFacts F l ι D).1 c hc
  obtain ⟨hK0, hK1, hK2, -, -⟩ := hK k⁻¹ (inv_mem hk) v
  obtain ⟨u, hu⟩ := hR.loc i (D.pl v) (by rw [hc]; exact one_ne_zero)
  set M : Matrix (Fin 2) (Fin 2) ℂ := (D.gl (a i * k⁻¹) v : Matrix (Fin 2) (Fin 2) ℂ) with hM
  set T : (D.pl v).adicCompletion F := (↑(Matrix.GeneralLinearGroup.map (pLoc F (D.pl v)) (a i * k⁻¹)) : Matrix (Fin 2) (Fin 2) ((D.pl v).adicCompletion F)).trace with hT
  set Δ : (D.pl v).adicCompletion F := (↑(Matrix.GeneralLinearGroup.map (pLoc F (D.pl v)) (a i * k⁻¹)) : Matrix (Fin 2) (Fin 2) ((D.pl v).adicCompletion F)).det with hΔ
  have hτT : M.trace = D.em v T := by
    rw [hM, hT, Matrix.trace_fin_two, Matrix.trace_fin_two, map_add, gl_apply, gl_apply]
  have hδΔ : M.det = D.em v Δ := by
    rw [hM, hΔ, Matrix.det_fin_two, Matrix.det_fin_two, gl_apply, gl_apply, gl_apply, gl_apply, map_sub, (D.em v).map_mul, (D.em v).map_mul]

  have hS : (D.gl (zc F z⁻¹) v : Matrix (Fin 2) (Fin 2) ℂ) = (D.ea v z)⁻¹ • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
    rw [gl_zc, map_units_inv]
  have hj : D.gl (jF F γ) v = D.gl x v * (D.gl (a i * k⁻¹) v * D.gl (zc F z⁻¹) v) * (D.gl x v)⁻¹ := by
    rw [hrel]; simp only [map_mul, map_inv, Pi.mul_apply, Pi.inv_apply]
  have htr : v.embedding γ.val.trace = (D.ea v z)⁻¹ * M.trace := by
    have e1 : v.embedding γ.val.trace = (D.gl (jF F γ) v : Matrix (Fin 2) (Fin 2) ℂ).trace := by
      rw [Matrix.trace_fin_two, Matrix.trace_fin_two, map_add, gl_apply, gl_apply]
      simp only [jF, Matrix.GeneralLinearGroup.map_apply, ← hea]
    rw [e1, hj, tr_conj, Units.val_mul, hS, Matrix.mul_smul, Matrix.mul_one, Matrix.trace_smul, smul_eq_mul]
  have hdt : v.embedding γ.val.det = ((D.ea v z)⁻¹) ^ 2 * M.det := by
    have e1 : v.embedding γ.val.det = (D.gl (jF F γ) v : Matrix (Fin 2) (Fin 2) ℂ).det := by
      rw [Matrix.det_fin_two, Matrix.det_fin_two, map_sub, map_mul, map_mul, gl_apply, gl_apply, gl_apply, gl_apply]
      simp only [jF, Matrix.GeneralLinearGroup.map_apply, ← hea]
    rw [e1, hj, det_conj2, Units.val_mul, hS, Matrix.mul_smul, Matrix.mul_one, Matrix.det_smul, Fintype.card_fin]
  set cnt := W.count (D.pl v) with hcnt
  set e : ℂ := D.em v ((atFin (D.pl v) (unif (D.pl v)) : (D.pl v).adicCompletion F)) with he_def
  set K : Matrix (Fin 2) (Fin 2) ℂ := (D.gl k⁻¹ v : Matrix (Fin 2) (Fin 2) ℂ) with hK_def
  have hA : ∀ p q, (D.gl (a i) v : Matrix (Fin 2) (Fin 2) ℂ) p q = !![e ^ cnt, D.em v (u : (D.pl v).adicCompletion F); 0, 1] p q := by
    intro p q
    rw [gl_apply, hu]
    fin_cases p <;> fin_cases q <;> simp [aff, he_def, hcnt]
  have hMmul : M = (D.gl (a i) v : Matrix (Fin 2) (Fin 2) ℂ) * K := by
    rw [hM, hK_def, map_mul, Pi.mul_apply, Units.val_mul]
  have hτ' : M.trace = e ^ cnt * K 0 0 + D.em v (u : (D.pl v).adicCompletion F) * K 1 0 + K 1 1 := by
    rw [hMmul, Matrix.trace_fin_two]
    simp only [Matrix.mul_apply, Fin.sum_univ_two, hA]
    simp
  have hϖ : Valued.v ((atFin (D.pl v) (unif (D.pl v)) : (D.pl v).adicCompletion F)) = WithZero.exp (-1 : ℤ) :=
    Formalism.L2.Host.unif_spec _
  have hexp : WithZero.exp (-1 : ℤ) < 1 := by
    have : WithZero.exp (-1 : ℤ) < WithZero.exp 0 := WithZero.exp_lt_exp.2 (by norm_num)
    simpa using this
  have he : nu ι e < 1 := (D.lt v _).2 (by rw [hϖ]; exact hexp)
  have hu1 : nu ι (D.em v (u : (D.pl v).adicCompletion F)) ≤ 1 := (D.le v _).2 u.2
  have hcnt1 : cnt ≠ 0 := by have := hW v; omega
  have hτ1 : nu ι M.trace = 1 := by
    have h1 : nu ι (M.trace - 1) < 1 := by
      have e1 : M.trace - 1 = e ^ cnt * K 0 0 + D.em v (u : (D.pl v).adicCompletion F) * K 1 0 + (K 1 1 - 1) := by
        rw [hτ']; ring
      rw [e1]
      refine Valuation.map_add_lt _ (Valuation.map_add_lt _ ?_ ?_) hK2
      · rw [map_mul, map_pow]
        calc nu ι e ^ cnt * nu ι (K 0 0) ≤ nu ι e ^ cnt * 1 := mul_le_mul_of_nonneg_left (hK0 0 0) zero_le
          _ = nu ι e ^ cnt := mul_one _
          _ < 1 := pow_lt_one₀ zero_le he hcnt1
      · rw [map_mul]
        calc nu ι (D.em v (u : (D.pl v).adicCompletion F)) * nu ι (K 1 0) ≤ 1 * nu ι (K 1 0) := mul_le_mul_of_nonneg_right hu1 zero_le
          _ = nu ι (K 1 0) := one_mul _
          _ < 1 := hK1
    have e2 : M.trace = 1 + (M.trace - 1) := by ring
    rw [e2]
    exact Valuation.map_one_add_of_lt _ h1
  have hTv : Valued.v T = 1 := (nu_eq_one_iff D v T).1 (hτT ▸ hτ1)
  have hΔmul : Δ = (↑(Matrix.GeneralLinearGroup.map (pLoc F (D.pl v)) (a i)) : Matrix (Fin 2) (Fin 2) ((D.pl v).adicCompletion F)).det *
      (↑(Matrix.GeneralLinearGroup.map (pLoc F (D.pl v)) k⁻¹) : Matrix (Fin 2) (Fin 2) ((D.pl v).adicCompletion F)).det := by
    rw [hΔ, map_mul, Units.val_mul, Matrix.det_mul]
  have hAdet : (↑(Matrix.GeneralLinearGroup.map (pLoc F (D.pl v)) (a i)) : Matrix (Fin 2) (Fin 2) ((D.pl v).adicCompletion F)).det =
      ((atFin (D.pl v) (unif (D.pl v)) : (D.pl v).adicCompletion F)) ^ cnt := by
    rw [hu]; simp [aff, Matrix.det_fin_two, hcnt]
  have hKdet := valuation_det_congruence_subgroup_eq_one (D.pl v) (c (D.pl v)) (mem_local_congruence_of_mem_global (inv_mem hk) (D.pl v))
  have hvΔ : Valued.v Δ = Valued.v (((l : ℕ) : (D.pl v).adicCompletion F)) ^ cnt := by
    rw [hΔmul, hAdet, map_mul, hKdet, map_pow, hϖ, D.unif v, mul_one]
  have hΔ0 : Δ ≠ 0 := by
    rw [hΔ]; exact (Matrix.GeneralLinearGroup.map (pLoc F (D.pl v)) (a i * k⁻¹)).det_ne_zero
  set Y : (D.pl v).adicCompletion F := ((l : ℕ) : (D.pl v).adicCompletion F) ^ cnt / Δ with hY_def
  have hY : Valued.v Y = 1 := by
    rw [hY_def, map_div₀, map_pow, hvΔ, div_self]
    exact pow_ne_zero _ (by rw [D.unif v]; exact WithZero.exp_ne_zero)
  have hUeq : D.em v Y = (l : ℂ) ^ cnt / D.em v Δ := by
    rw [hY_def, map_div₀, map_pow, map_natCast]
  have hδ0 : D.em v Δ ≠ 0 := (map_ne_zero (D.em v)).2 hΔ0
  have hδU : M.det * D.em v Y = (l : ℂ) ^ cnt := by
    rw [hδΔ, hUeq, mul_div_cancel₀ _ hδ0]
  have hU1 : nu ι (D.em v Y) = 1 := (nu_eq_one_iff D v Y).2 hY
  have hνδ : nu ι M.det = nu ι (l : ℂ) ^ cnt := by
    have := congrArg (nu ι) hδU
    rw [map_mul, hU1, mul_one, map_pow] at this
    exact this
  have hνl : nu ι (l : ℂ) ≤ 1 := val_nat_le _ l
  have hδr : nu ι M.det ≤ nu ι (l : ℂ) ^ r := by
    rw [hνδ]; exact pow_le_pow_of_le_one zero_le hνl (hW v)
  have hδ1 : nu ι M.det ≤ 1 := hδr.trans (pow_le_one₀ zero_le hνl)
  refine ⟨M.trace, M.det, D.em v Y, htr, hdt, hτ1.le, hδ1, hδr, hU1.le, hδU, fun t ht => ⟨?_, ?_⟩⟩
  · rw [hτT]; exact hU F l ι D v T hTv N (2 * t) (dvd_mul_of_dvd_right ht 2)
  · exact hU F l ι D v Y hY N t ht

end Loc

end UpperTheory.Esk.adelicTermLemmas
end
end

