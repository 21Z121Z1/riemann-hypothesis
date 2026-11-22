import Formalism.ThetaLogCoordinates.FockResolutionOnto.StatementH
import Formalism.ThetaLogCoordinates.FockResolutionOnto.FockMonomialProofs.GramBoundUnconditionalOfSat
import Formalism.ThetaLogCoordinates.FockResolutionOnto.FockMonomialProofs.Vanish
import Formalism.ThetaLogCoordinates.FockResolutionOnto.FockMonomialProofs.DerivativeKillsDegreeZero
import Formalism.ThetaLogCoordinates.FockResolutionOnto.FockMonomialProofs.RestrictedLatticeDividedPower
import Formalism.ThetaLogCoordinates.FockResolutionOnto.FockMonomialProofs.WmMulWmComm
import Formalism.ThetaLogCoordinates.FockResolutionOnto.FockMonomialProofs.DerivativeDividedIntegral

-- bundled from Formalism.ThetaLogCoordinates.FockResolutionOnto.FockMonomialProofs.GramBoundPosOfProjSat
section
namespace Formalism.InvariantFactorPaths.L4

open Formalism.GM Formalism.GM.M Formalism.GM.TM Formalism.GM.MeanGammaLemmas Formalism.CountingSumsFrames Formalism.InvariantFactorPaths.PW MvPolynomial Finset

theorem projAt2_of (hX : HighestVectorProjectionPos) (p : ℕ) [Fact p.Prime] (K r : ℕ) [NeZero r] (LLw : Letters (K + 1)) {q : ℕ}
    (J : Fin q → ℕ) (M : Fin q → WithTop ℤ) (ρ : Fin r) (w : Fin r → ℤ) (e e1 : ℕ) (hK : 1 ≤ K) (hr : 2 ≤ r)
    (hρ : (ρ : ℕ) = r - 1) (hv : LLw.vec (Fin.last K) = true) (he : e ≤ LLw.deg (Fin.last K))
    (hP : HypP p (setLast LLw (LLw.deg (Fin.last K) - e)) ρ e1)
    (hE : HypE p (setLast LLw (LLw.deg (Fin.last K) - e)) ρ e1)
    (hO : ResOntoK p (setLast LLw (LLw.deg (Fin.last K) - e)) J (shiftLastLetterThresholds K J M e) ρ) :
    ProjAt p LLw J M ρ w e ((K + 1) * e1) := by
  classical
  obtain ⟨Pr', hPr'⟩ := hX p K r (setLast LLw (LLw.deg (Fin.last K) - e)) J (shiftLastLetterThresholds K J M e) ρ (shiftWt w ρ e) e1
    hK hr hρ hv hP hE
  have hSp := grSpan_eq LLw J M ρ w e e1 hr hρ hv he hP hE hO
  refine ⟨(LinearMap.mulLeft ℚ_[p] (X (Fin.last K, ρ) ^ e : MvPolynomial (Fin (K + 1) × Fin r) ℚ_[p])) ∘ₗ Pr' ∘ₗ
    strip p (Fin.last K, ρ) e, ?_⟩
  intro m hm
  simp only [LinearMap.comp_apply, LinearMap.mulLeft_apply]
  by_cases hme : m (Fin.last K, ρ) = e
  · obtain ⟨m', rfl⟩ : ∃ m', m = Finsupp.single (Fin.last K, ρ) e + m' :=
      ⟨m - Finsupp.single (Fin.last K, ρ) e, (add_tsub_cancel_of_le (by
        rw [Finsupp.single_le_iff]; exact hme.ge)).symm⟩
    have hm0 : m' (Fin.last K, ρ) = 0 := by simpa using hme
    have hmD := (multiDeg_pow LLw ρ e he m').mp hm
    obtain ⟨h1, h2, h3⟩ := hPr' m' hmD hm0
    rw [strip_monomial_eq _ _ _ hm0]
    refine ⟨(hSp _).mpr ⟨_, h1, rfl⟩, ?_, ?_⟩
    · rw [← mul_smul_comm, pow_mul_int_iff]; exact h2
    · intro g hg
      obtain ⟨y, hy, rfl⟩ := (hSp g).mp hg
      rw [monomial_single_add, fock_pow_mul _ _ _ _ (xH_le_free _ J _ ρ _ y hy),
        fock_pow_mul _ _ _ _ (xH_le_free _ J _ ρ _ y hy), h3 y hy]
  · rw [strip_monomial_ne _ _ _ hme, map_zero, mul_zero]
    refine ⟨Submodule.zero_mem _, by rw [smul_zero]; exact Submodule.zero_mem _, ?_⟩
    intro g hg
    obtain ⟨y, hy, rfl⟩ := (hSp g).mp hg
    rw [fock_eq_zero_of _ 0 (fun _ => Or.inr (coeff_zero _)), fock_eq_zero_of]
    intro n
    by_cases hn : n = m
    · left
      rw [hn]
      exact coeff_pow_mul_ne _ _ y (xH_le_free _ J _ ρ _ y hy) m hme
    · right
      rw [coeff_monomial, if_neg (Ne.symm hn)]

theorem graded_bound_pos_of_proj (hX : HighestVectorProjectionPos) : GradedBoundOfSaturationPos := by
  intro p _ K r _ LLw q J M ρ e1 c0 κ hK hr hρ hv hPE hS hκ w e k g hli hspan
  by_cases he : e ≤ LLw.deg (Fin.last K)
  · obtain ⟨hP, hE⟩ := hPE (LLw.deg (Fin.last K) - e) (Nat.sub_le _ _)
    refine graded_piece_bound_holds p K r LLw J M ρ w e ((K + 1) * e1) (e1 + c0) κ
      (projAt2_of hX p K r LLw J M ρ w e e1 hK hr hρ hv he hP hE (resOntoK_of_resSatL _ J _ ρ c0 (hS e he)))
      (satAtL LLw J M ρ w e e1 c0 hr hρ hv he hP hE (hS e he)) ?_ k g hli hspan
    have : (K + 1) * e1 + 2 * (e1 + c0) = (K + 3) * e1 + 2 * c0 := by ring
    rw [this]; exact hκ
  · rw [graded_bot_holds p K r LLw J M ρ w e (not_le.mp he)] at hspan
    have hk : k = 0 := by
      by_contra hk
      have h0 : g ⟨0, Nat.pos_of_ne_zero hk⟩ ∈ Submodule.span ℤ_[p] (Set.range g) :=
        Submodule.subset_span ⟨_, rfl⟩
      rw [hspan, Submodule.mem_bot] at h0
      exact hli.ne_zero _ h0
    subst hk
    simp

section Zero

variable {p : ℕ} [Fact p.Prime]

theorem self_lift {K r : ℕ} [NeZero r] (LL : Letters (K + 1)) {q : ℕ} (J : Fin q → ℕ) (M : Fin q → WithTop ℤ)
    (ρ : Fin r) (x : MvPolynomial (Fin (K + 1) × Fin r) ℚ_[p]) (hF : x ∈ FreeOf p (Fin.last K, ρ))
    (hY : x ∈ Y p LL J M) (hi : x ∈ IntPol p (Fin (K + 1) × Fin r)) :
    ∃ h ∈ Y p LL J M, h ∈ IntPol p (Fin (K + 1) × Fin r) ∧
      initPart (Fin.last K, ρ) 0 h = ((p : ℚ_[p]) ^ 0) • x := by
  refine ⟨x, hY, hi, ?_⟩
  rw [pow_zero, one_smul, ← resL_apply, resL_of_free _ x hF]

theorem pol_le_ycond_total {r N : ℕ} [NeZero r] (LL : Letters N) (j : ℕ) (c : ℤ) (hc : (LL.total : ℤ) ≤ c) :
    Pol p r LL ≤ YCond p LL j ((c : ℤ) : WithTop ℤ) := by
  refine le_ycond LL j _ _ ?_ (fun a b x hx => Formalism.CountingSumsFrames.glAct_pol LL j a b x hx)
  intro x hx
  rw [Pol, mem_restrictSupport_iff] at hx
  rw [mem_restrictSupport_iff]
  intro m hm
  have h1 : MultiDeg LL m := hx hm
  have h2 := abs_wt_le LL j (0 : Fin r) m
  have h3 : (∑ v, m v) = LL.total := by
    rw [Fintype.sum_prod_type]
    unfold Letters.total
    exact Finset.sum_congr rfl fun i _ => h1 i
  show ((wt LL j 0 m : ℤ) : WithTop ℤ) ≤ ((c : ℤ) : WithTop ℤ)
  rw [WithTop.coe_le_coe]
  have h4 := le_abs_self (wt LL j (0 : Fin r) m)
  rw [h3] at h2
  omega

end Zero

theorem restricted_saturation_zero : ResSatLZero := by
  intro p _ r _ LL q J M ρ hr hρ hv x hx hxi
  obtain ⟨hxP, hxF, hxk⟩ := (mem_xsp LL J M ρ x).mp hx
  by_cases hfin : ∃ k, 0 + 1 ≤ J k ∧ M k ≠ ⊤
  · obtain ⟨k1, hk1, hM1⟩ := hfin
    have hne : (univ.filter fun k => 0 + 1 ≤ J k).Nonempty := ⟨k1, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hk1⟩⟩
    obtain ⟨k0, hk0, hmin⟩ := Finset.exists_min_image _ M hne
    have hk0' : 0 + 1 ≤ J k0 := (Finset.mem_filter.mp hk0).2
    have hmin' : ∀ k, 0 + 1 ≤ J k → M k0 ≤ M k := fun k hk =>
      hmin k (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hk⟩)
    have hM0 : M k0 ≠ ⊤ := fun h => hM1 (top_le_iff.mp (h ▸ hmin' k1 hk1))
    obtain ⟨c, hc⟩ := WithTop.ne_top_iff_exists.mp hM0
    by_cases hcd : c < LL.total
    · have hT : x ∈ TypesLE p LL (0 + 1) (univ.erase ρ) ((c : ℤ) : WithTop ℤ) := by
        rw [hc]; exact ((hxk k0).1 hk0').2
      have htot : LL.total = LL.deg (Fin.last 0) := by
        unfold Letters.total
        simp
      have hV := space_vanishing_holds p 0 r LL ρ c (LL.deg (Fin.last 0)) hr hρ hv (by
        rw [htot] at hcd
        simpa using hcd)
      rw [setLast_self] at hV
      have hx0 : x = 0 := by
        have : x ∈ Pol p r LL ⊓ FreeOf p (Fin.last 0, ρ) ⊓
            TypesLE p LL (0 + 1) (univ.erase ρ) ((c : ℤ) : WithTop ℤ) :=
          Submodule.mem_inf.mpr ⟨Submodule.mem_inf.mpr ⟨hxP, hxF⟩, hT⟩
        rw [hV] at this
        exact (Submodule.mem_bot _).mp this
      subst hx0
      exact self_lift LL J M ρ 0 hxF (Submodule.zero_mem _) hxi
    · refine self_lift LL J M ρ x hxF ((mem_y LL J M x).mpr ⟨hxP, fun k => ?_⟩) hxi
      by_cases hk : 0 + 1 ≤ J k
      · exact ycond_mono LL (J k) _ _ (hc ▸ hmin' k hk) (pol_le_ycond_total LL (J k) c (not_lt.mp hcd) hxP)
      · exact (hxk k).2 hk
  · refine self_lift LL J M ρ x hxF ((mem_y LL J M x).mpr ⟨hxP, fun k => ?_⟩) hxi
    by_cases hk : 0 + 1 ≤ J k
    · have : M k = ⊤ := by
        by_contra hne
        exact hfin ⟨k, hk, hne⟩
      rw [this, Formalism.CountingSumsFrames.ycond_top]
      exact Submodule.mem_top
    · exact (hxk k).2 hk

theorem gram_bound_pos_of_proj_sat (hX : HighestVectorProjectionPos) (hS : ResSatLThm) : GramBoundUnconditionalPos := by
  intro p _ K r _ LLw q J M ρ a κ hr hρ hv ht hκ
  rcases Nat.eq_zero_or_pos K with rfl | hK
  · refine graded_bound_saturation_holds p 0 r LLw J M ρ (kapC p r LLw.total) 0 κ hr hρ hv (hypPE_setLast LLw ρ)
      (fun e _ => restricted_saturation_zero p r _ J _ ρ hr hρ hv) ?_
    rw [Nat.mul_zero, Nat.add_zero]
    exact (kappa_numeric_holds p 0 r a LLw.total hr ht).trans hκ
  · refine graded_bound_pos_of_proj hX p K r LLw J M ρ (kapC p r LLw.total)
      (2 * (r.choose 2 * Nat.log p (4 * LLw.total + r - 1))) κ hK hr hρ hv (hypPE_setLast LLw ρ) ?_ (le_trans ?_ hκ)
    · intro e _
      have ht' := setLast_total_le LLw (LLw.deg (Fin.last K) - e) (Nat.sub_le _ _)
      exact resSatL_mono _ J _ ρ
        (Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (Nat.log_mono_right (by omega))))
        (hS p K r (setLast LLw (LLw.deg (Fin.last K) - e)) J (shiftLastLetterThresholds K J M e) ρ hr hρ hv)
    · have h1 := numeric_product_inequality p a r (LLw.total + r - 1) (by omega)
      have h2 := numeric_product_inequality p a r (4 * LLw.total + r - 1) (by omega)
      have hQ := lg_nonneg p a r
      have hK1 : (1 : ℝ) ≤ K := by exact_mod_cast hK
      have hKQ := mul_nonneg (sub_nonneg.mpr hK1) hQ
      have h3 : ((K : ℝ) + 3) * ((kapC p r LLw.total : ℕ) : ℝ) ≤ ((K : ℝ) + 3) * ((r : ℝ) ^ 2 / 2 * lgV2 p a r) :=
        mul_le_mul_of_nonneg_left h1 (by positivity)
      rw [Nat.cast_add, Nat.cast_mul, Nat.cast_mul (2 : ℕ), Nat.cast_mul (2 : ℕ)]
      push_cast at h2 h3 ⊢
      nlinarith

theorem theoremMFree0_of (hX : HighestVectorProjectionPos) (hS : ResSatLThm) : TheoremMFree0 := by
  obtain ⟨C₀, hC₀, hM⟩ := Formalism.InvariantFactorPaths.PW.Top.lattice_theorem_height_bound
  refine ⟨C₀, hC₀, ?_⟩
  intro p _ N r _ _ LL T a E κ Yl n₀ dd ρ hp hr hρ hadm hE hY hS' hdeg hz hκ hineq
  refine hM p N r LL T a E κ Yl n₀ dd ρ hp hr hρ hadm hE hY hS' hdeg hz hκ hineq ?_
  intro n hn i
  exact gram_bound_pos_of_proj_sat hX hS p (T.pos i) r _ T.J (T.thrUpTo i) ρ a κ hr hρ (takeD_vec_last LL T hadm n i)
    (takeD_total_le LL T hadm a Yl n₀ dd hS' hdeg n (grid_le T Yl n₀ dd n hn) i)
    ((pos_num LL T hadm p a r i).trans hκ)

end Formalism.InvariantFactorPaths.L4
end

-- bundled from Formalism.ThetaLogCoordinates.FockResolutionOnto.FockMonomialProofs.RestrictedSaturationHolds
section
namespace Formalism.InvariantFactorPaths.L4

open Formalism.GM Formalism.GM.M Formalism.GM.TM Formalism.GM.MeanGammaLemmas Formalism.GM.DimensionMonotonicity Formalism.CountingSumsFrames Formalism.InvariantFactorPaths.PW MvPolynomial Finset

section Lat
variable {p : ℕ} [Fact p.Prime] {K : ℕ}

theorem sat_of_mem_y {r : ℕ} [NeZero r] (LL : Letters (K + 1)) {q : ℕ} (J : Fin q → ℕ) (M : Fin q → WithTop ℤ)
    (ρ : Fin r) (n : ℕ) (x : MvPolynomial (Fin (K + 1) × Fin r) ℚ_[p]) (hF : x ∈ FreeOf p (Fin.last K, ρ))
    (hY : x ∈ Y p LL J M) (hi : x ∈ IntPol p (Fin (K + 1) × Fin r)) :
    ∃ h ∈ Y p LL J M, h ∈ IntPol p (Fin (K + 1) × Fin r) ∧
      initPart (Fin.last K, ρ) 0 h = ((p : ℚ_[p]) ^ n) • x := by
  have key : ∀ y ∈ FreeOf p (Fin.last K, ρ), initPart (Fin.last K, ρ) 0 y = y := by
    intro y hy
    unfold initPart
    conv_rhs => rw [y.as_sum]
    refine Finset.sum_congr rfl fun m hm => ?_
    have hm0 : m (Fin.last K, ρ) = 0 := (MvPolynomial.mem_restrictSupport_iff ℚ_[p]).1 hy hm
    rw [if_pos hm0]
  refine ⟨((p : ℚ_[p]) ^ n) • x, Submodule.smul_mem _ _ hY, ?_, key _ (Submodule.smul_mem _ _ hF)⟩
  rw [show ((p : ℚ_[p]) ^ n) = algebraMap ℤ_[p] ℚ_[p] ((p : ℤ_[p]) ^ n) by simp, algebraMap_smul]
  exact Submodule.smul_mem _ _ hi

theorem pol_le_ycond {r N : ℕ} [NeZero r] (LL : Letters N) (j : ℕ) (c : ℤ) (hc : (LL.total : ℤ) ≤ c) :
    Pol p r LL ≤ YCond p LL j ((c : ℤ) : WithTop ℤ) := by
  unfold YCond
  apply le_sSup
  refine ⟨?_, fun c d x hx => Formalism.CountingSumsFrames.glAct_pol (p := p) LL j c d x hx⟩
  intro x hx
  rw [Pol, MvPolynomial.mem_restrictSupport_iff] at hx
  rw [MvPolynomial.mem_restrictSupport_iff]
  intro m hm
  have hd := hx hm
  show ((wt LL j 0 m : ℤ) : WithTop ℤ) ≤ ((c : ℤ) : WithTop ℤ)
  rw [WithTop.coe_le_coe]
  refine le_trans ?_ hc
  calc wt LL j 0 m ≤ ∑ i, (LL.deg i : ℤ) := Finset.sum_le_sum fun i _ => by
        have h1 : (m (i, 0) : ℤ) ≤ LL.deg i := by
          rw [← hd i]
          exact_mod_cast Finset.single_le_sum (fun c _ => Nat.zero_le (m (i, c))) (Finset.mem_univ 0)
        split_ifs <;> omega
    _ = (LL.total : ℤ) := by unfold Letters.total; push_cast; rfl

theorem sat_main {s : ℕ} (LL : Letters (K + 1)) {q : ℕ} (J : Fin q → ℕ) (M : Fin q → WithTop ℤ) (c : ℤ)
    (hs : 1 ≤ s) (hv : LL.vec (Fin.last K) = true) (k0 : Fin q) (hk0 : K + 1 ≤ J k0)
    (hc : M k0 = ((c : ℤ) : WithTop ℤ)) (hmin : ∀ k, K + 1 ≤ J k → M k0 ≤ M k) (hcd : c < LL.total)
    (x : MvPolynomial (Fin (K + 1) × Fin (s + 1)) ℚ_[p]) (hx : x ∈ XSp p LL J M (Fin.last s))
    (hxi : x ∈ IntPol p (Fin (K + 1) × Fin (s + 1))) :
    ∃ h ∈ Y p LL J M, h ∈ IntPol p (Fin (K + 1) × Fin (s + 1)) ∧
      initPart (Fin.last K, Fin.last s) 0 h =
        ((p : ℚ_[p]) ^ (2 * ((s + 1).choose 2 * Nat.log p (4 * LL.total + (s + 1) - 1)))) • x := by
  obtain ⟨G, hE, hcomp⟩ := gl_action_exists p K s LL c hv
  have L := latData LL J M c raising_divided_integral derivative_divided_integral hs hv k0 hk0 hc hmin hcd G hE hcomp
  have hxW : x ∈ Wtot p LL J M (Fin.last s) :=
    mem_wtot LL J M (LL.deg (Fin.last K)) x (by rw [setLast_self]; exact hx)
  obtain ⟨f, hf, hsum⟩ := (Submodule.mem_iSup_iff_exists_finsupp _ x).mp
    (wtot_le_iso LL J M c hs hv k0 hk0 hc hmin G hE hcomp hxW)
  generalize hD : (s + 1).choose 2 * Nat.log p (4 * LL.total + (s + 1) - 1) = D
  have hpiece : ∀ la, ((p : ℚ_[p]) ^ D) • (((p : ℚ_[p]) ^ D) • f la) ∈ M2 p LL J M (Fin.last s) := by
    intro la
    obtain ⟨Q, hQ1, hQ2, hQ3⟩ := Formalism.InvariantFactorPaths.PW.Top.typeInt p _ (s + 1) G _ _ (4 * LL.total) L la
    have hQx : Q x = f la := by
      rw [← hsum, Finsupp.sum, map_sum]
      by_cases hla : la ∈ f.support
      · rw [Finset.sum_eq_single_of_mem la hla (fun mu _ hne => hQ2 mu hne _ (hf mu)), hQ1 _ (hf la)]
      · rw [Finset.sum_eq_zero (fun mu hmu => hQ2 mu (fun h => hla (h ▸ hmu)) _ (hf mu)),
          Finsupp.notMem_support_iff.mp hla]
    have h1 := hQ3 x hxi hxW
    rw [hQx, hD] at h1
    have h2 := Formalism.InvariantFactorPaths.PW.Top.weylInt p _ (s + 1) G _ _ (4 * LL.total) L la _
      (Submodule.smul_mem _ _ (hf la)) h1
    rw [hD] at h2
    exact span_le_restrictedLattice raising_divided_integral derivative_divided_integral LL hv J M c k0 hk0 hc hmin G hE _
      (fun h hh => restrictedLattice_of_deg_zero LL hv J M _ h (hw_deg_zero LL J M c G hE hcomp la h hh.1 hh.2.1) hh.2.2) h2
  have hM2 : ((p : ℚ_[p]) ^ (2 * D)) • x ∈ M2 p LL J M (Fin.last s) := by
    rw [two_mul, pow_add, ← smul_smul, ← hsum, Finsupp.sum, Finset.smul_sum, Finset.smul_sum]
    exact Submodule.sum_mem _ fun la _ => hpiece la
  have hP : ((p : ℚ_[p]) ^ (2 * D)) • x ∈ Pol p (s + 1) (setLast LL (LL.deg (Fin.last K))) := by
    rw [setLast_self]
    exact Submodule.smul_mem _ _ ((mem_xsp LL J M _ x).mp hx).1
  have h3 := restrictedLattice_exists_lift LL J M (Fin.last s) (LL.deg (Fin.last K)) _ hM2 hP
  rwa [setLast_self] at h3

end Lat

theorem restricted_saturation_holds : ResSatLThm := by
  intro p _ K r _ LL q J M ρ hr hρ hv x hx hi
  obtain ⟨s, rfl⟩ : ∃ s, r = s + 1 := ⟨r - 1, by omega⟩
  have hρ' : ρ = Fin.last s := Fin.ext (by simp [hρ])
  subst hρ'
  have hs : 1 ≤ s := by omega
  by_cases hex : ∃ k, K + 1 ≤ J k ∧ M k < ((LL.total : ℤ) : WithTop ℤ)
  · obtain ⟨k1, hk1, hk1M⟩ := hex
    obtain ⟨k0, hk0mem, hk0min⟩ := Finset.exists_min_image (univ.filter fun k => K + 1 ≤ J k) M
      ⟨k1, Finset.mem_filter.2 ⟨Finset.mem_univ _, hk1⟩⟩
    have hk0 : K + 1 ≤ J k0 := (Finset.mem_filter.1 hk0mem).2
    have hlt : M k0 < ((LL.total : ℤ) : WithTop ℤ) := lt_of_le_of_lt (hk0min k1 (Finset.mem_filter.2 ⟨Finset.mem_univ _, hk1⟩)) hk1M
    obtain ⟨c, hc⟩ := WithTop.ne_top_iff_exists.1 (ne_top_of_lt hlt)
    refine sat_main LL J M c hs hv k0 hk0 hc.symm (fun k hk => hk0min k (Finset.mem_filter.2 ⟨Finset.mem_univ _, hk⟩)) ?_ x hx hi
    rw [← hc] at hlt
    exact_mod_cast hlt
  · push_neg at hex
    have hx1 := Submodule.mem_inf.1 hx
    have hP := (Submodule.mem_inf.1 hx1.1).1
    have hF := (Submodule.mem_inf.1 hx1.1).2
    have hK := (Submodule.mem_iInf _).1 hx1.2
    have hxY : x ∈ Y p LL J M := by
      refine Submodule.mem_inf.2 ⟨hP, (Submodule.mem_iInf _).2 fun k => ?_⟩
      by_cases hJ : K + 1 ≤ J k
      · have hMk := hex k hJ
        have h1 := pol_le_ycond (p := p) (r := s + 1) LL (J k) (LL.total : ℤ) le_rfl hP
        have hmono : YCond p (r := s + 1) LL (J k) (((LL.total : ℤ) : ℤ) : WithTop ℤ) ≤
            YCond p (r := s + 1) LL (J k) (M k) := by
          unfold YCond
          apply sSup_le_sSup
          rintro S ⟨hS1, hS2⟩
          refine ⟨hS1.trans ?_, hS2⟩
          intro y hy
          rw [MvPolynomial.mem_restrictSupport_iff] at hy ⊢
          intro m hm
          exact le_trans (hy hm) hMk
        exact hmono h1
      · have := hK k
        rw [if_neg hJ] at this
        exact this
    exact sat_of_mem_y LL J M (Fin.last s) _ x hF hxY hi

end Formalism.InvariantFactorPaths.L4
end

