import Formalism.GaussJetBounds.Bundle0006
import Formalism.GaussJetBounds.GaussJetProofs.Bundle0001

-- bundled from Formalism.GaussJetBounds.GaussJetProofs.CoefficientBoundMembership
section
noncomputable section
open scoped BigOperators

namespace Formalism.DworkPowerSeriesWeights

open MvPolynomial Formalism.IncomingBounds

lemma det_sum_mul_expand {S : Type*} [CommRing S] {p n : ℕ} (u : Fin p → Fin n → S)
    (y : Fin n → Fin p → S) :
    (Matrix.of fun (r r' : Fin p) => ∑ a, u r a * y a r').det =
      ∑ A : Fin p → Fin n, (∏ r', y (A r') r') *
        (Matrix.of fun (r r' : Fin p) => u r (A r')).det := by
  simp only [Matrix.det_apply', Matrix.of_apply, Finset.prod_univ_sum, Fintype.piFinset_univ,
    Finset.mul_sum, Finset.prod_mul_distrib]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun A _ => Finset.sum_congr rfl fun σ _ => ?_
  ring

lemma minorProd_expand {R : Type} [CommRing R] {ι : Type} {N0 N1 Cn : ℕ}
    (x : Fin N0 → Fin N0 → R) (Y : Fin N0 → Fin N1 → MvPolynomial ι R) (p : Fin Cn → ℕ)
    (hp : ∀ c, p c ≤ N0) (I : ∀ c, Fin (p c) → Fin N1) :
    minorProd (fun i b => ∑ a, C (x i a) * Y a b) p hp I =
      ∑ A ∈ Fintype.piFinset (fun c => (Finset.univ : Finset (Fin (p c) → Fin N0))),
        (∏ c, ∏ r', Y (A c r') (I c r')) *
          C (∏ c, (Matrix.of fun (r r' : Fin (p c)) =>
            x ⟨r.val, lt_of_lt_of_le r.isLt (hp c)⟩ (A c r')).det) := by
  simp only [minorProd, det_sum_mul_expand]
  rw [Finset.prod_univ_sum]
  refine Finset.sum_congr rfl fun A _ => ?_
  rw [Finset.prod_mul_distrib, map_prod]
  congr 1
  refine Finset.prod_congr rfl fun c _ => ?_
  rw [RingHom.map_det]
  congr 1

lemma exists_monomial_prod {R ι α : Type} [CommSemiring R] (s : Finset α)
    (f : α → MvPolynomial ι R) (hf : ∀ i ∈ s, ∃ e, f i = monomial e 1) :
    ∃ e, ∏ i ∈ s, f i = monomial e 1 := by
  classical
  revert hf
  refine Finset.induction_on s (fun _ => ⟨0, ?_⟩) ?_
  · rw [Finset.prod_empty, ← MvPolynomial.C_1, MvPolynomial.C_apply]
  intro a s ha ih hf
  obtain ⟨e1, h1⟩ := hf a (Finset.mem_insert_self a s)
  obtain ⟨e2, h2⟩ := ih (fun i hi => hf i (Finset.mem_insert_of_mem hi))
  exact ⟨e1 + e2, by rw [Finset.prod_insert ha, h1, h2, MvPolynomial.monomial_mul, mul_one]⟩

private lemma coeff_sum_mem_lemma {K : Type} [Field K] {σ ι α : Type}
    (M : Submodule K (MvPolynomial σ K)) (S : Finset α) (f : α → MvPolynomial ι (MvPolynomial σ K))
    (hf : ∀ A ∈ S, ∃ e Q, Q ∈ M ∧ f A = MvPolynomial.monomial e Q) (κ : ι →₀ ℕ) :
    MvPolynomial.coeff κ (∑ A ∈ S, f A) ∈ M := by
  classical
  rw [MvPolynomial.coeff_sum]
  refine Submodule.sum_mem _ fun A hA => ?_
  obtain ⟨e, Q, hQ, hfA⟩ := hf A hA
  rw [hfA, MvPolynomial.coeff_monomial]
  split_ifs
  · exact hQ
  · exact Submodule.zero_mem _

private lemma jetPairPoly_mem_lemma_2 {K : Type} [Field K] {σ ι : Type}
    (M : Submodule K (MvPolynomial σ K)) (P : MvPolynomial ι (MvPolynomial σ K))
    (Th : MvPowerSeries ι K) (hP : ∀ κ, MvPolynomial.coeff κ P ∈ M) :
    jetPairPoly P Th ∈ M := by
  unfold jetPairPoly
  refine Submodule.sum_mem _ fun κ _ => ?_
  rw [mul_comm (MvPolynomial.coeff κ P), ← MvPolynomial.smul_eq_C_mul]
  exact Submodule.smul_mem _ _ (hP κ)

private lemma prod_mul_C_lemma_3 {K : Type} [Field K] {σ ι α : Type}
    (M : Submodule K (MvPolynomial σ K)) (s : Finset α) (f : α → MvPolynomial ι (MvPolynomial σ K))
    (Q : MvPolynomial σ K) (hf : ∀ a ∈ s, ∃ e, f a = MvPolynomial.monomial e 1) (hQ : Q ∈ M) :
    ∃ e Q', Q' ∈ M ∧ (∏ a ∈ s, f a) * MvPolynomial.C Q = MvPolynomial.monomial e Q' := by
  obtain ⟨e, he⟩ := exists_monomial_prod s f hf
  exact ⟨e, Q, hQ, by rw [he, mul_comm, MvPolynomial.C_mul_monomial, mul_one]⟩

theorem coefficient_bound_membership : CBMem := by
  unfold CBMem
  intro K _ d N0 N1 _ colN p hp I Th
  unfold frameJet nablaK
  refine jetPairPoly_mem_lemma_2 _ _ _ fun κ => ?_
  simp only [minorProd_expand]
  rw [Finset.prod_univ_sum]
  refine coeff_sum_mem_lemma _ _ _ (fun A _ => ?_) κ
  rw [Finset.prod_mul_distrib, ← map_prod]
  refine prod_mul_C_lemma_3 _ _ _ _ (fun s _ => ?_) ?_
  · exact exists_monomial_prod _ _ fun c _ => exists_monomial_prod _ _ fun r' _ => ⟨_, rfl⟩
  · refine Submodule.subset_span ?_
    simp only [xMinors, Set.mem_setOf_eq]
    exact ⟨A, rfl⟩

theorem thmAWeyl_of (hG : ThmAGauss) : ThmAWeyl := by
  unfold ThmAWeyl
  unfold ThmAGauss at hG
  intro l _ d N0 N1 _ h3 h2 hE K0 hU ζ hζ be hB g hg0 hgs U hUi ε hε TT colN p hp hp1 I nu1 nu2 size
    h1 h2' h3' a ha hsa hlog hSB c hc
  have hbd := hG l d N0 N1 h3 h2 hE K0 hU ζ hζ be hB g hg0 hgs U hUi ε hε TT colN p hp hp1 I nu1
    nu2 size h1 h2' h3' a ha hsa hlog
  have hCB := coefficient_bound_membership
  unfold CBMem at hCB
  have hmem := hCB _ d N0 N1 colN p hp I (thetaZ g U ε be)
  unfold SBSat at hSB
  refine hSB _ (Submodule.smul_mem _ c⁻¹ hmem) fun n => ?_
  rw [MvPolynomial.coeff_smul, smul_eq_mul, norm_mul, norm_inv]
  have hx := le_trans (hbd n) hc
  rcases (norm_nonneg c).eq_or_lt with h0 | hpos
  · rw [← h0, inv_zero, zero_mul]
    exact zero_le_one
  · calc _ ≤ ‖c‖⁻¹ * ‖c‖ := mul_le_mul_of_nonneg_left hx (inv_nonneg.mpr (norm_nonneg c))
      _ = 1 := inv_mul_cancel₀ hpos.ne'

end Formalism.DworkPowerSeriesWeights
end
end

-- bundled from Formalism.GaussJetBounds.GaussJetProofs.Labels
section
noncomputable section
open scoped BigOperators

namespace Formalism.DworkPowerSeriesWeights

open Formalism.IncomingBounds

theorem bddAbove_norm_coeff {R : Type} [NormedField R] {σ : Type} (Q : MvPolynomial σ R) :
    BddAbove (Set.range fun n : σ →₀ ℕ => ‖MvPolynomial.coeff n Q‖) := by
  classical
  have hfin : (Set.range fun n : σ →₀ ℕ => ‖MvPolynomial.coeff n Q‖).Finite := by
    refine Set.Finite.subset
      ((Q.support.image fun n => ‖MvPolynomial.coeff n Q‖).finite_toSet.insert 0) ?_
    rintro _ ⟨n, rfl⟩
    by_cases hn : n ∈ Q.support
    · right
      exact Finset.mem_coe.2 (Finset.mem_image_of_mem _ hn)
    · left
      simp only [MvPolynomial.notMem_support_iff.1 hn, norm_zero]
  exact hfin.bddAbove

theorem gauss_sum_powers : GaussPow := by
  classical
  intro F K _ _ φ σ Y h k hk Q n
  let E : (σ →₀ ℕ) → (σ →₀ ℕ) := fun n =>
    Finsupp.onFinset n.support (fun y => k y * n y) (fun y hy => by
      rw [Finsupp.mem_support_iff]
      exact fun h0 => hy (by rw [h0, Nat.mul_zero]))
  have hEa : ∀ n y, E n y = k y * n y := fun n y => rfl
  have hE : Function.Injective E := by
    intro n n' hnn
    ext y
    have := congrArg (fun f => f y) hnn
    simp only [hEa] at this
    exact Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero (hk y)) this
  let Q' : MvPolynomial σ F := ∑ n ∈ Q.support, MvPolynomial.monomial (E n) (MvPolynomial.coeff n Q)
  have h1 : MvPolynomial.eval₂ φ Y Q' = MvPolynomial.eval₂ φ (fun y => Y y ^ k y) Q := by
    rw [MvPolynomial.eval₂_sum, MvPolynomial.eval₂_eq]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [MvPolynomial.eval₂_monomial, Finsupp.onFinset_prod _ (fun _ => pow_zero _)]
    congr 1
    refine Finset.prod_congr rfl fun y _ => ?_
    rw [pow_mul]
  have hc : ∀ n, MvPolynomial.coeff (E n) Q' = MvPolynomial.coeff n Q := by
    intro n
    simp only [Q', MvPolynomial.coeff_sum, MvPolynomial.coeff_monomial, hE.eq_iff]
    rw [Finset.sum_ite_eq' Q.support n]
    split_ifs with hn
    · rfl
    · exact (MvPolynomial.notMem_support_iff.1 hn).symm
  rw [← h1, h, ← hc]
  exact le_ciSup (bddAbove_norm_coeff Q') (E n)

theorem labelsExist_statement : LabelsExist := by
  classical
  intro l d N0 _ hl TT nu1 size a ha hnu hsize hN
  let S : ZMod d → Finset ℤ := fun s =>
    (Finset.Icc (-(a : ℤ)) a).filter (fun j => Odd j ∧ s - (j : ZMod d) ∈ TT ∧
      (0 < j → l ^ j.toNat ≤ nu1 (s - (j : ZMod d))) ∧ (j < 0 → l ^ (-j).toNat ≤ size s))

  have hpow : ∀ (s : ZMod d) (j : ℤ), Odd j →
      (0 < j → l ^ j.toNat ≤ nu1 (s - (j : ZMod d))) → (j < 0 → l ^ (-j).toNat ≤ size s) →
      l ^ j.natAbs ≤ a := by
    intro s j hj h1 h2
    rcases lt_trichotomy j 0 with h | h | h
    · have : (-j).toNat = j.natAbs := by omega
      rw [← this]
      exact (h2 h).trans (hsize s)
    · subst h
      exact absurd hj (by decide)
    · have : j.toNat = j.natAbs := by omega
      rw [← this]
      exact (h1 h).trans (hnu _)
  have hIcc : ∀ j : ℤ, l ^ j.natAbs ≤ a → j ∈ Finset.Icc (-(a : ℤ)) a := by
    intro j hj
    have h1 : j.natAbs < l ^ j.natAbs := Nat.lt_pow_self hl
    rw [Finset.mem_Icc]
    omega
  have hcard : ∀ s, ((S s).card : ℝ) ≤ 2 * Real.logb l a + 1 := by
    intro s
    refine le_trans ?_ (oddExponentCount l a hl ha)
    exact_mod_cast Finset.card_le_card (by
      intro j hj
      simp only [S, Finset.mem_filter] at hj
      rw [Finset.mem_filter]
      exact ⟨hj.1, hj.2.1, hpow s j hj.2.1 hj.2.2.2.1 hj.2.2.2.2⟩)
  refine ⟨fun s => (S s).card,
    fun s i => (s - ((((S s).equivFin.symm i : S s) : ℤ) : ZMod d), (((S s).equivFin.symm i : S s) : ℤ)),
    a, ?_, ?_, ?_, ?_⟩
  · intro s i i' hii
    have h2 := congrArg Prod.snd hii
    simp only at h2
    exact (S s).equivFin.symm.injective (Subtype.ext h2)
  · intro s s0 j
    constructor
    · rintro ⟨i, hi⟩
      have hm := ((S s).equivFin.symm i).2
      have h1 := congrArg Prod.fst hi
      have h2 := congrArg Prod.snd hi
      simp only at h1 h2
      rw [h2] at h1 hm
      simp only [S, Finset.mem_filter] at hm
      rw [h1] at hm
      exact ⟨hm.2.2.1, hm.2.1, by rw [← h1]; ring, hm.2.2.2.1, hm.2.2.2.2⟩
    · rintro ⟨hT, hodd, hs, hp, hn⟩
      have hs0 : s - (j : ZMod d) = s0 := by rw [hs]; ring
      have hm : j ∈ S s := by
        simp only [S, Finset.mem_filter]
        rw [hs0]
        exact ⟨hIcc j (hpow s j hodd (by rw [hs0]; exact hp) hn), hodd, hT, hp, hn⟩
      refine ⟨(S s).equivFin ⟨j, hm⟩, ?_⟩
      simp only [Equiv.symm_apply_apply, hs0]
  · intro s
    have h1 := hcard s
    have h2 : ((S s).card : ℝ) + 1 ≤ (N0 : ℝ) := by linarith
    have h3 : (S s).card + 1 ≤ N0 := by exact_mod_cast h2
    show (S s).card + _ ≤ N0
    split_ifs <;> omega
  · intro s i
    show (-(((S s).equivFin.symm i : S s) : ℤ)).toNat ≤ a
    obtain ⟨j, hm⟩ := (S s).equivFin.symm i
    have hm' := (Finset.mem_Icc.1 (Finset.mem_filter.1 hm).1).1
    show (-j).toNat ≤ a
    omega

end Formalism.DworkPowerSeriesWeights
end
end

-- bundled from Formalism.GaussJetBounds.GaussJetProofs.Transfer
section
noncomputable section
open scoped BigOperators

namespace Formalism.DworkPowerSeriesWeights

open Formalism.IncomingBounds MvPowerSeries

namespace Transfer

section Maps

variable {F K : Type} [Field F] [Field K] (φ : F →+* K) {d : ℕ}

theorem map_substZero (s : ZMod d) : map φ (s0 (K := F) s) = s0 s := by
  simp [s0]
theorem map_substOne (s : ZMod d) : map φ (s1 (K := F) s) = s1 s := by
  unfold s1
  split_ifs <;> simp
theorem map_substTwo (s : ZMod d) : map φ (s2 (K := F) s) = s2 s := by
  unfold s2
  split_ifs <;> simp
theorem map_substOne' (s : ZMod d) : map φ (s1' (K := F) s) = s1' s := by
  unfold s1'
  split_ifs <;> simp
theorem map_substTwo' (s : ZMod d) : map φ (s2' (K := F) s) = s2' s := by
  unfold s2'
  split_ifs <;> simp

theorem constantCoeff_substZero (s : ZMod d) : constantCoeff (s0 (K := F) s) = 0 := by
  simp [s0]
theorem constantCoeff_substOne (s : ZMod d) : constantCoeff (s1 (K := F) s) = 0 := by
  unfold s1
  split_ifs <;> simp
theorem constantCoeff_substTwo (s : ZMod d) : constantCoeff (s2 (K := F) s) = 0 := by
  unfold s2
  split_ifs <;> simp
theorem constantCoeff_substOne' (s : ZMod d) : constantCoeff (s1' (K := F) s) = 0 := by
  unfold s1'
  split_ifs <;> simp
theorem constantCoeff_substTwo' (s : ZMod d) : constantCoeff (s2' (K := F) s) = 0 := by
  unfold s2'
  split_ifs <;> simp

theorem map_torus (l : ℕ) (ζ : F) (s : ZMod d) :
    map φ (torus l ζ s) = torus l (φ ζ) s := by
  simp [torus]

theorem cc_torus (l : ℕ) (ζ : F) (s : ZMod d) : constantCoeff (torus l ζ s) = 0 := by
  simp [torus]

theorem map_letterLog (l : ℕ) (x : V2 d) :
    map φ (letterLog (K := F) l x) = letterLog l x := by
  ext n
  rw [MvPowerSeries.coeff_map]
  change φ (letterLog (K := F) l x n) = letterLog (K := K) l x n
  simp only [letterLog]
  rw [map_sum]
  refine Finset.sum_congr rfl fun e _ => ?_
  split_ifs <;> simp

theorem cc_letterLog (l : ℕ) (x : V2 d) : constantCoeff (letterLog (K := F) l x) = 0 := by
  rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply]
  change letterLog (K := F) l x 0 = 0
  simp only [letterLog]
  refine Finset.sum_eq_zero fun e he => ?_
  have he0 : e = 0 := by simpa using he
  subst he0
  rw [if_neg]
  intro h
  have h1 := Finsupp.single_eq_zero.mp h.symm
  simp at h1

theorem map_entLog {N0 N1 : ℕ} (l : ℕ) (x : ZV d N0 N1) :
    map φ (entLog (K := F) l x) = entLog l x := by
  ext n
  rw [MvPowerSeries.coeff_map]
  change φ (entLog (K := F) l x n) = entLog (K := K) l x n
  simp only [entLog]
  rw [map_sum]
  refine Finset.sum_congr rfl fun e _ => ?_
  split_ifs <;> simp

variable [NeZero d]

theorem map_defectOne (be : MvPowerSeries (ZMod d) F) : map φ (de1 be) = de1 (map φ be) := by
  have hs : ∀ (a : ZMod d → MvPowerSeries (V2 d) F), (∀ s, MvPowerSeries.constantCoeff (a s) = 0) →
      MvPowerSeries.map φ (MvPowerSeries.subst a be) =
        MvPowerSeries.subst (fun s => MvPowerSeries.map φ (a s)) (MvPowerSeries.map φ be) :=
    fun a ha => MvPowerSeries.map_subst (MvPowerSeries.hasSubst_of_constantCoeff_zero ha) be
  unfold de1
  rw [map_sub, map_sub, hs s1 constantCoeff_substOne, hs s0 constantCoeff_substZero, hs s2 constantCoeff_substTwo]
  simp only [map_substOne, map_substZero, map_substTwo]

theorem map_defectTwo (be : MvPowerSeries (ZMod d) F) : map φ (de2 be) = de2 (map φ be) := by
  have hs : ∀ (a : ZMod d → MvPowerSeries (V2 d) F), (∀ s, MvPowerSeries.constantCoeff (a s) = 0) →
      MvPowerSeries.map φ (MvPowerSeries.subst a be) =
        MvPowerSeries.subst (fun s => MvPowerSeries.map φ (a s)) (MvPowerSeries.map φ be) :=
    fun a ha => MvPowerSeries.map_subst (MvPowerSeries.hasSubst_of_constantCoeff_zero ha) be
  unfold de2
  rw [map_sub, map_sub, hs s1' constantCoeff_substOne', hs s0 constantCoeff_substZero, hs s2' constantCoeff_substTwo']
  simp only [map_substOne', map_substZero, map_substTwo']

theorem constantCoeff_defectOne {be : MvPowerSeries (ZMod d) F} (h : constantCoeff be = 0) :
    constantCoeff (de1 be) = 0 := by
  have hz : ∀ (a : ZMod d → MvPowerSeries (V2 d) F), (∀ s, MvPowerSeries.constantCoeff (a s) = 0) →
      MvPowerSeries.constantCoeff (MvPowerSeries.subst a be) = 0 :=
    fun a ha => MvPowerSeries.constantCoeff_subst_eq_zero
      (MvPowerSeries.hasSubst_of_constantCoeff_zero ha) ha h
  unfold de1
  rw [map_sub, map_sub, hz s1 constantCoeff_substOne, hz s0 constantCoeff_substZero, hz s2 constantCoeff_substTwo]
  simp

theorem constantCoeff_defectTwo {be : MvPowerSeries (ZMod d) F} (h : constantCoeff be = 0) :
    constantCoeff (de2 be) = 0 := by
  have hz : ∀ (a : ZMod d → MvPowerSeries (V2 d) F), (∀ s, MvPowerSeries.constantCoeff (a s) = 0) →
      MvPowerSeries.constantCoeff (MvPowerSeries.subst a be) = 0 :=
    fun a ha => MvPowerSeries.constantCoeff_subst_eq_zero
      (MvPowerSeries.hasSubst_of_constantCoeff_zero ha) ha h
  unfold de2
  rw [map_sub, map_sub, hz s1' constantCoeff_substOne', hz s0 constantCoeff_substZero, hz s2' constantCoeff_substTwo']
  simp

theorem cc_of_noLow {be : MvPowerSeries (ZMod d) F} (h : NoLowBidegree be) :
    constantCoeff be = 0 := by
  by_contra hc
  have h0 := (h 0 (by rwa [MvPowerSeries.coeff_zero_eq_constantCoeff_apply])).1
  simp [degE] at h0

end Maps

section Normed

variable {F K : Type} [NormedField F] [CharZero F] [NormedField K] [CharZero K] (φ : F →+* K)

theorem map_mvExp {ι : Type} {f : MvPowerSeries ι F} (h : constantCoeff f = 0) :
    map φ (mvExp f) = mvExp (map φ f) := by
  unfold mvExp
  rw [PowerSeries.map_subst (PowerSeries.HasSubst.of_constantCoeff_zero h), PowerSeries.map_exp]

theorem integral_map (hφ : ∀ z, ‖φ z‖ = ‖z‖) {ι : Type} {U : MvPowerSeries ι F}
    (h : Integral U) : Integral (map φ U) := by
  intro n
  rw [MvPowerSeries.coeff_map, hφ]
  exact h n

theorem map_logExp {d : ℕ} [NeZero d] (l : ℕ) {f : MvPowerSeries (V2 d) F}
    (h : constantCoeff f = 0) :
    map φ (subst (letterLog (K := F) l) (mvExp f)) =
      subst (letterLog (K := K) l) (mvExp (map φ f)) := by
  have hL : ∀ x : V2 d, MvPowerSeries.constantCoeff (letterLog (K := F) l x) = 0 := cc_letterLog l
  rw [MvPowerSeries.map_subst (MvPowerSeries.hasSubst_of_constantCoeff_zero hL), map_mvExp φ h]
  congr 1
  funext x
  exact map_letterLog φ l x

end Normed

end Transfer

open Transfer in
theorem admissibleTransfer : TransferB := by
  intro F K _ _ _ _ φ hφ l d N0 N1 _ K0 ζ be
  refine ⟨?_, ?_, ?_, fun U hU => integral_map φ hφ hU⟩
  · intro hU a ha ha0
    obtain ⟨b, hb, rfl⟩ := Subfield.mem_map.mp ha
    have hb0 : b ≠ 0 := by
      rintro rfl
      simp at ha0
    obtain ⟨k, hk⟩ := hU b hb hb0
    exact ⟨k, by rw [hφ, hk, ← map_natCast φ l, hφ]⟩
  · rintro ⟨h1, h2, h3, ⟨h4, h5⟩, ⟨h6, h7⟩⟩
    have hcc : MvPowerSeries.constantCoeff be = 0 := cc_of_noLow h3
    have E1 : MvPowerSeries.subst (letterLog (K := K) l) (mvExp (de1 (MvPowerSeries.map φ be))) =
        MvPowerSeries.map φ (MvPowerSeries.subst (letterLog (K := F) l) (mvExp (de1 be))) := by
      rw [← map_defectOne, map_logExp φ l (constantCoeff_defectOne hcc)]
    have E2 : MvPowerSeries.subst (letterLog (K := K) l) (mvExp (de2 (MvPowerSeries.map φ be))) =
        MvPowerSeries.map φ (MvPowerSeries.subst (letterLog (K := F) l) (mvExp (de2 be))) := by
      rw [← map_defectTwo, map_logExp φ l (constantCoeff_defectTwo hcc)]
    have hcm : ∀ G : MvPowerSeries (V2 d) F,
        MvPowerSeries.constantCoeff (MvPowerSeries.map φ G) = φ (MvPowerSeries.constantCoeff G) := by
      intro G
      rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply, MvPowerSeries.coeff_map,
        MvPowerSeries.coeff_zero_eq_constantCoeff_apply]
    refine ⟨fun n => ?_, ?_, ?_, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
    · rw [MvPowerSeries.coeff_map]
      exact Subfield.mem_map.mpr ⟨_, h1 n, rfl⟩
    · have ht : ∀ s : ZMod d, MvPowerSeries.constantCoeff (torus l ζ s) = 0 := fun s => cc_torus l ζ s
      have := congrArg (MvPowerSeries.map φ) h2
      rw [MvPowerSeries.map_subst (MvPowerSeries.hasSubst_of_constantCoeff_zero ht)] at this
      simpa only [map_torus] using this
    · intro n hn
      rw [MvPowerSeries.coeff_map] at hn
      exact h3 n (fun h0 => hn (by rw [h0, map_zero]))
    · rw [E1]
      exact integral_map φ hφ h4
    · rw [E1, hcm, h5, map_one]
    · rw [E2]
      exact integral_map φ hφ h6
    · rw [E2, hcm, h7, map_one]
  · intro g hg hgs
    refine ⟨fun y => ?_, fun y => ?_⟩
    · rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply, MvPowerSeries.coeff_map,
        MvPowerSeries.coeff_zero_eq_constantCoeff_apply, hg y, map_zero]
    · have := congrArg (MvPowerSeries.map φ) (hgs y)
      rw [MvPowerSeries.map_subst (MvPowerSeries.hasSubst_of_constantCoeff_zero hg), map_entLog,
        MvPowerSeries.map_X] at this
      exact this

end Formalism.DworkPowerSeriesWeights
end
end

