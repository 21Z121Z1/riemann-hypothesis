import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GelfandTsetlinLowering.ZScalarVanish
import Formalism.PeriodIntegrals.Bundle0026
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GelfandTsetlinLowering.Bundle0004
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GelfandTsetlinLowering.Bundle0005

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GelfandTsetlinLowering.ConstructionAdj
section
noncomputable section

namespace PI.WGL

open Formalism.BasicNotions MvPolynomial PI.WGL.Adj

theorem adjointBr_of (h3 : PI.HwIrred) (h5 : PI.SchurFock) (hN : Numbers) (hX : XiFacts) :
    AdjointBr := by
  intro n N h lam sg hI io hio hext hlast
  obtain ⟨hioV, hioEq⟩ := hio
  obtain ⟨hc0, hcB, -⟩ := hN n N h lam sg hI
  obtain ⟨hxi0, hxiV, -, -, -, hxiU⟩ := hX n N h lam sg hI
  obtain ⟨d, b, hbV, hexp⟩ := exists_frame n sg
  have hdel_sg : delSq ℂ n sg = nablaSq ℂ n sg := ((h3 n sg).1).symm
  have hdel_lam : delSq ℂ N lam = nablaSq ℂ N lam := ((h3 N lam).1).symm

  let br : MvPolynomial (Fin N × Fin N) ℂ →ₗ[ℂ] MvPolynomial (Fin n × Fin n) ℂ :=
    ∑ k, (nfL lam (io (b k))).smulRight (b k)
  have hbr : ∀ f, br f = ∑ k, normFock lam f (io (b k)) • b k := by
    intro f
    simp [br, LinearMap.sum_apply, LinearMap.smulRight_apply, nfL_apply]
  have hbrV : ∀ f, br f ∈ nablaSq ℂ n sg := by
    intro f
    rw [hbr]
    exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (hbV k)
  have hT : ∀ s ∈ nablaSq ℂ n sg, ∀ f, normFock lam (io s) f = normFock sg s (br f) := by
    intro s hs f
    have e := hexp s hs
    calc normFock lam (io s) f = normFock lam (io (∑ k, normFock sg s (b k) • b k)) f := by rw [← e]
      _ = ∑ k, normFock sg s (b k) * normFock lam (io (b k)) f := by
          rw [map_sum]
          simp only [map_smul]
          rw [nf_sum_smul_left]
      _ = normFock sg s (br f) := by
          rw [hbr, nf_sum_smul_right]
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [← nf_herm, mul_comm]
  have hsep : ∀ x y, x ∈ nablaSq ℂ n sg → y ∈ nablaSq ℂ n sg →
      (∀ s ∈ nablaSq ℂ n sg, normFock sg s x = normFock sg s y) → x = y := by
    intro x y hx hy hxy
    have hd : x - y ∈ nablaSq ℂ n sg := Submodule.sub_mem _ hx hy
    have h0 : normFock sg (x - y) (x - y) = 0 := by rw [nf_sub_right, hxy _ hd, sub_self]
    exact sub_eq_zero.mp (nf_self_eq_zero sg _ h0)

  have hB4 : ∀ (g : GL (Fin n) ℂ) (f : MvPolynomial (Fin N × Fin N) ℂ),
      br (sqAct ℂ N lam (embGL ℂ n N h g) f) = sqAct ℂ n sg g (br f) := by
    intro g f
    refine hsep _ _ (hbrV _) (sqAct_mem_nabla sg g _ (hbrV f)) fun s hs => ?_
    have hs' : sqAct ℂ n sg (gStar g) s ∈ nablaSq ℂ n sg := sqAct_mem_nabla sg _ s hs
    rw [← hT s hs, nf_sqAct_adj' lam (embGL ℂ n N h g) (io s) f, ← embGL_gStar, ← hioEq _ s hs,
      hT _ hs', nf_sqAct_adj' sg g s (br f)]
  have hB5 : ∀ (a : ℂˣ) (f : MvPolynomial (Fin N × Fin N) ℂ),
      br (sqAct ℂ N lam (lastGL ℂ N a) f) = ((a ^ degZ lam sg : ℂˣ) : ℂ) • br f := by
    intro a f
    refine hsep _ _ (hbrV _) (Submodule.smul_mem _ _ (hbrV f)) fun s hs => ?_
    rw [← hT s hs, nf_sqAct_adj' lam (lastGL ℂ N a) (io s) f, ← lastGL_cU, hlast _ s hs, nf_smul_left,
      nf_smul_right, hT s hs, cU_zpow_val]

  have hextV : extremal ℂ n sg ∈ nablaSq ℂ n sg := extremal_mem sg
  have hext0 : extremal ℂ n sg ≠ 0 := extremal_ne sg
  let Tm : Module.End ℂ (nablaSq ℂ n sg) :=
    LinearMap.codRestrict (nablaSq ℂ n sg) ((br ∘ₗ io) ∘ₗ (nablaSq ℂ n sg).subtype) (fun x => hbrV _)
  haveI : FiniteDimensional ℂ (nablaSq ℂ n sg) := PI.WHw.bC_fd n n sg.natW
  haveI : Nontrivial (nablaSq ℂ n sg) :=
    ⟨⟨⟨_, hextV⟩, 0, fun h0 => hext0 (congrArg Subtype.val h0)⟩⟩
  obtain ⟨κ, hκ⟩ := Module.End.exists_eigenvalue Tm
  obtain ⟨v, hv⟩ := hκ.exists_hasEigenvector
  have hv1 : br (io (v : MvPolynomial (Fin n × Fin n) ℂ)) = κ • (v : MvPolynomial (Fin n × Fin n) ℂ) := by
    have := Module.End.HasEigenvector.apply_eq_smul hv
    exact congrArg Subtype.val this
  have hv0 : (v : MvPolynomial (Fin n × Fin n) ℂ) ≠ 0 := fun h0 => hv.2 (Subtype.ext h0)
  let U : Submodule ℂ (MvPolynomial (Fin n × Fin n) ℂ) :=
    nablaSq ℂ n sg ⊓ LinearMap.ker (br ∘ₗ io - κ • LinearMap.id)
  have hmemU : ∀ x, x ∈ U ↔ x ∈ nablaSq ℂ n sg ∧ br (io x) = κ • x := by
    intro x
    simp only [U, Submodule.mem_inf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.comp_apply,
      LinearMap.smul_apply, LinearMap.id_apply, sub_eq_zero]
  have hUst : ∀ (g : GL (Fin n) ℂ), ∀ x ∈ U, sqAct ℂ n sg g x ∈ U := by
    intro g x hx
    rw [hmemU] at hx ⊢
    refine ⟨sqAct_mem_nabla sg g x hx.1, ?_⟩
    rw [hioEq g x hx.1, hB4, hx.2, sqAct_smul]
  have hall : ∀ s ∈ nablaSq ℂ n sg, br (io s) = κ • s := by
    rcases (h3 n sg).2.1 U inf_le_left hUst with hU | hU
    · exfalso
      have hvU : (v : MvPolynomial (Fin n × Fin n) ℂ) ∈ U := (hmemU _).2 ⟨v.2, hv1⟩
      rw [hU, Submodule.mem_bot] at hvU
      exact hv0 hvU
    · intro s hs
      rw [← hU] at hs
      exact ((hmemU s).1 hs).2

  set K := normFock lam (io (extremal ℂ n sg)) (io (extremal ℂ n sg)) with hKdef
  have hnorm : ∀ s ∈ nablaSq ℂ n sg, normFock lam (io s) (io s) = K * normFock sg s s := by
    have hK : star κ = K := by
      have := hT _ hextV (io (extremal ℂ n sg))
      rw [hall _ hextV, nf_smul_right, nf_extremal, mul_one] at this
      exact this.symm
    intro s hs
    rw [hT s hs, hall s hs, nf_smul_right, hK]
  have hKre : K.re = ‖((cBr h lam sg : ℤ) : ℂ)‖ ^ 2 * (normFock lam (xi ℂ h lam sg) (xi ℂ h lam sg)).re := by
    rw [hKdef, hext, PI.GTS.re_normFock_smul]
  have hKreal : K = ((K.re : ℝ) : ℂ) := by rw [hKdef]; exact nf_self_eq_re lam _
  have hcpos : 0 < ‖((cBr h lam sg : ℤ) : ℂ)‖ := by
    rw [norm_pos_iff]; exact_mod_cast hc0
  have hKpos : 0 < K.re := by
    rw [hKre]; exact mul_pos (pow_pos hcpos 2) (nf_self_re_pos lam _ hxi0)
  have hKle : K.re ≤ brBd h lam sg ^ 2 := by
    have hc2 : ‖((cBr h lam sg : ℤ) : ℂ)‖ ^ 2 ≤ cBd h lam sg ^ 2 := by
      have hcn : ‖((cBr h lam sg : ℤ) : ℂ)‖ = |((cBr h lam sg : ℤ) : ℝ)| := by
        rw [← Complex.ofReal_intCast, Complex.norm_real, Real.norm_eq_abs]
      rw [hcn]
      exact pow_le_pow_left₀ (abs_nonneg _) hcB 2
    have hSF := h5 N lam (xi ℂ h lam sg) hxiV hxiU
    have hbb : brBd h lam sg ^ 2 = cBd h lam sg ^ 2 * (Module.finrank ℂ (delSq ℂ N lam) : ℝ) := by
      unfold brBd; rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg _)]
    rw [hKre, hbb]
    exact mul_le_mul hc2 hSF (nf_self_re_nonneg lam _) (sq_nonneg _)
  refine ⟨?_, br, ⟨?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  ·
    intro s hs
    rw [hnorm s hs, hKreal, Complex.re_ofReal_mul]
    exact mul_le_mul_of_nonneg_right hKle (nf_self_re_nonneg sg s)
  ·
    intro f _
    rw [hdel_sg]; exact hbrV f
  ·
    refine ⟨io (extremal ℂ n sg), ?_, ?_⟩
    · rw [hdel_lam]; exact hioV _ hextV
    · intro h0
      have := hT _ hextV (io (extremal ℂ n sg))
      rw [h0, nf_zero_right] at this
      rw [← hKdef] at this
      rw [this] at hKpos
      simp at hKpos
  ·
    intro g f _
    exact hB4 g f
  ·
    intro a f _
    exact hB5 a f
  ·
    intro f _
    set u := br f with hu
    have huV : u ∈ nablaSq ℂ n sg := hbrV f
    have hTu : normFock lam (io u) f = normFock sg u u := hT u huV f
    have hCS := nf_cauchy_schwarz lam (io u) f
    have hnA : ‖normFock sg u u‖ = (normFock sg u u).re := by
      conv_lhs => rw [nf_self_eq_re sg u]
      exact Complex.norm_of_nonneg (nf_self_re_nonneg sg u)
    rw [nf_herm lam (io u) f, hTu, norm_star, hnA, hnorm u huV, hKreal, Complex.re_ofReal_mul] at hCS
    have hA := nf_self_re_nonneg sg u
    have hF := nf_self_re_nonneg lam f
    have hAle : (normFock sg u u).re ≤ K.re * (normFock lam f f).re := by
      rcases hA.lt_or_eq with hApos | hA0
      · refine le_of_mul_le_mul_left ?_ hApos
        nlinarith
      · rw [← hA0]; exact mul_nonneg hKpos.le hF
    calc (normFock sg u u).re ≤ K.re * (normFock lam f f).re := hAle
      _ ≤ brBd h lam sg ^ 2 * (normFock lam f f).re := mul_le_mul_of_nonneg_right hKle hF
  ·
    intro s hs f _
    exact hT s hs f

end PI.WGL
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GelfandTsetlinLowering.LiftTupleF
section
noncomputable section

namespace PI.WGL.LTF

open Formalism.BasicNotions Formalism.GradedWeylDivisibility MvPolynomial PI.WGL.LTA PI.WGL.LTM PI.WGL.LTC PI.WGL.LTD PI.WGL.LTE

theorem gmin_rowW {r c m : ℕ} (ρ : Fin m → Fin r) (κ : Fin m → Fin c) :
    IsWeightedHomogeneous (rowW r c) (gmin ρ κ) (∑ p, (Pi.single (ρ p) 1 : Fin r → ℕ)) := by
  classical
  unfold gmin
  rw [Matrix.det_apply, ← mem_weightedHomogeneousSubmodule]
  refine Submodule.sum_mem _ fun σ _ => ?_
  refine Submodule.smul_of_tower_mem _ _ ?_
  rw [mem_weightedHomogeneousSubmodule]
  have hp := IsWeightedHomogeneous.prod Finset.univ
    (fun p => (X (ρ (σ p), κ p) : MvPolynomial (Fin r × Fin c) ℤ))
    (fun p => rowW r c (ρ (σ p), κ p)) (fun p _ => isWeightedHomogeneous_X ℤ _ _)
  have hsum : ∑ p, rowW r c (ρ (σ p), κ p) = ∑ p, (Pi.single (ρ p) 1 : Fin r → ℕ) := by
    simp only [rowW]
    exact Equiv.sum_comp σ (fun p => (Pi.single (ρ p) 1 : Fin r → ℕ))
  rw [hsum] at hp
  simpa [Matrix.of_apply] using hp

theorem bidet_rowW {n K : ℕ} (sz : Fin K → ℕ) (hsz : ∀ k, sz k ≤ n) (I : ∀ k, Fin (sz k) → Fin n) :
    IsWeightedHomogeneous (rowW n n) (bideterminant ℤ sz hsz I) (tupCnt I) := by
  unfold bideterminant
  have hp := IsWeightedHomogeneous.prod Finset.univ (fun k => initMinor ℤ (n := n) (I k) (hsz k))
    (fun k => ∑ p, (Pi.single (I k p) 1 : Fin n → ℕ)) (fun k _ => gmin_rowW (I k) (Fin.castLE (hsz k)))
  convert hp using 1
  funext a
  simp only [tupCnt, Finset.sum_apply, Pi.single_apply]
  simp [eq_comm]

def w0r {n N : ℕ} (h : n + 1 = N) (lam : DomWeight N) (sg : DomWeight n) : Fin N → ℕ :=
  ∑ i : Fin n, ((if i.1 + 1 = n then (aa h lam sg i).toNat else 0) • initW N (i.1 + 1) +
    (if i.1 = 0 then (bb h lam sg i).toNat else 0) • (∑ p, (Pi.single (rowsZ h i p) 1 : Fin N → ℕ)))

theorem ite_pow_rowW {N : ℕ} (c : Prop) [Decidable c] (f : MvPolynomial (Fin N × Fin N) ℤ) (w : Fin N → ℕ)
    (hf : IsWeightedHomogeneous (rowW N N) f w) (e : ℕ) :
    IsWeightedHomogeneous (rowW N N) (if c then f ^ e else 1) ((if c then e else 0) • w) := by
  split_ifs
  · exact hf.pow e
  · simpa using isWeightedHomogeneous_one ℤ (rowW N N)

theorem constant_weighted_homogeneous {n N : ℕ} (h : n + 1 = N) (lam : DomWeight N) (sg : DomWeight n) :
    IsWeightedHomogeneous (rowW N N) (C0 h lam sg) (w0r h lam sg) := by
  have hlp : ∀ (s : ℕ) (hr : s ≤ N) (hc : s ≤ N),
      IsWeightedHomogeneous (rowW N N) (lpMinor ℤ s hr hc) (initW N s) := by
    intro s hr hc
    have hg : IsWeightedHomogeneous (rowW N N) (lpMinor ℤ s hr hc)
        (∑ p, (Pi.single (Fin.castLE hr p) 1 : Fin N → ℕ)) := gmin_rowW (Fin.castLE hr) (Fin.castLE hc)
    have hw : (∑ p, (Pi.single (Fin.castLE hr p) 1 : Fin N → ℕ)) = initW N s := by
      funext t
      simp only [Finset.sum_apply, Pi.single_apply, initW, Fin.ext_iff, Fin.coe_castLE]
      rw [show (∑ p : Fin s, if (t : ℕ) = (p : ℕ) then 1 else 0) = ∑ p : Fin s, if (p : ℕ) = t.1 then 1 else 0 from
        Finset.sum_congr rfl (fun p _ => by simp only [eq_comm])]
      rw [sum_ite_val (fun _ => 1) t.1]
      simp
    rw [hw] at hg
    exact hg
  unfold C0 w0r
  refine IsWeightedHomogeneous.prod Finset.univ _ _ fun i _ => ?_
  refine IsWeightedHomogeneous.mul ?_ ?_
  · exact ite_pow_rowW _ _ _ (hlp _ _ _) _
  · exact ite_pow_rowW _ _ _ (gmin_rowW (rowsZ h i) (Fin.castLE _)) _

def wk {n N : ℕ} (h : n + 1 = N) {m : ℕ} (ρ : Fin m → Fin n) (lifted : Prop) [Decidable lifted] : Fin N → ℕ :=
  (∑ q, (Pi.single (eRow h (ρ q)) 1 : Fin N → ℕ)) +
    (if lifted then (Pi.single (⟨N - 1, by omega⟩ : Fin N) 1 : Fin N → ℕ) else 0)

theorem G_rowW {n N : ℕ} (h : n + 1 = N) {K : ℕ} (sz : Fin K → ℕ) (hsz : ∀ k, sz k ≤ n) (L : Finset (Fin K))
    (k : Fin K) (ρ : Fin (sz k) → Fin n) :
    IsWeightedHomogeneous (rowW N N)
      (if k ∈ L then lif h ρ (by have := hsz k; omega) else unl h ρ (by have := hsz k; omega))
      (wk h ρ (k ∈ L)) := by
  unfold wk
  split_ifs with hk
  · unfold lif
    have hg : IsWeightedHomogeneous (rowW N N)
        (initMinor ℤ (liftRows h ρ) (by have := hsz k; omega : sz k + 1 ≤ N))
        (∑ p, (Pi.single (liftRows h ρ p) 1 : Fin N → ℕ)) :=
      gmin_rowW (liftRows h ρ) (Fin.castLE (by have := hsz k; omega : sz k + 1 ≤ N))
    have hw : (∑ p, (Pi.single (liftRows h ρ p) 1 : Fin N → ℕ)) =
        (∑ q, (Pi.single (eRow h (ρ q)) 1 : Fin N → ℕ)) + Pi.single (⟨N - 1, by omega⟩ : Fin N) 1 := by
      rw [Fin.sum_univ_castSucc]
      simp [liftRows]
    rw [hw] at hg
    exact hg
  · unfold unl
    have hg : IsWeightedHomogeneous (rowW N N)
        (initMinor ℤ (eRow h ∘ ρ) (by have := hsz k; omega : sz k ≤ N))
        (∑ p, (Pi.single (eRow h (ρ p)) 1 : Fin N → ℕ)) :=
      gmin_rowW (eRow h ∘ ρ) (Fin.castLE (by have := hsz k; omega : sz k ≤ N))
    rw [add_zero]
    exact hg

theorem constant_weight_apply {n N : ℕ} (h : n + 1 = N) (lam : DomWeight N) (sg : DomWeight n) (av : ℕ) (hav : av < N) :
    w0r h lam sg ⟨av, hav⟩ =
      (if hn : n - 1 < n then (aa h lam sg ⟨n - 1, hn⟩).toNat * (if av < n then 1 else 0) else 0) +
      (if hn : 0 < n then (bb h lam sg ⟨0, hn⟩).toNat * (if av = n then 1 else 0) else 0) := by
  unfold w0r
  have key : ∀ i : Fin n, (((if i.1 + 1 = n then (aa h lam sg i).toNat else 0) • initW N (i.1 + 1) +
      (if i.1 = 0 then (bb h lam sg i).toNat else 0) • (∑ p, (Pi.single (rowsZ h i p) 1 : Fin N → ℕ)))
        ⟨av, hav⟩) =
      (if i.1 = n - 1 then (aa h lam sg i).toNat * (if av < n then 1 else 0) else 0) +
      (if i.1 = 0 then (bb h lam sg i).toNat * (if av = n then 1 else 0) else 0) := by
    intro i
    have hi2 := i.2
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    congr 1
    · by_cases hi : i.1 + 1 = n
      · rw [if_pos hi, if_pos (by omega)]
        simp only [initW, hi]
      · rw [if_neg hi, if_neg (by omega), zero_mul]
    · by_cases hi : i.1 = 0
      · rw [if_pos hi, if_pos hi]
        congr 1
        rw [Finset.sum_apply]
        have e : ∀ p : Fin (i.1 + 1), (Pi.single (rowsZ h i p) 1 : Fin N → ℕ) ⟨av, hav⟩ =
            if av = n then 1 else 0 := by
          intro p
          have hp := p.2
          have hr : rowsZ h i p = ⟨N - 1, by omega⟩ := by
            simp only [rowsZ]
            rw [if_pos (by omega)]
          rw [hr, Pi.single_apply]
          by_cases hav' : av = n
          · rw [if_pos (Fin.ext (by simp only; omega)), if_pos hav']
          · rw [if_neg (fun he => hav' (by have := congrArg Fin.val he; simp only at this; omega)), if_neg hav']
        rw [Finset.sum_congr rfl (fun p _ => e p), Finset.sum_const, Finset.card_univ, Fintype.card_fin, hi,
          smul_eq_mul, zero_add, one_mul]
      · rw [if_neg hi, if_neg hi, zero_mul]
  rw [Finset.sum_apply, Finset.sum_congr rfl (fun i _ => key i), Finset.sum_add_distrib, sum_ite_val,
    sum_ite_val]

theorem cardL {n N : ℕ} (h : n + 1 = N) (lam : DomWeight N) (sg : DomWeight n) {K : ℕ} (sz : Fin K → ℕ)
    (hsz : ∀ k, sz k ≤ n) (hshape : shapeDeg sz = sg.natW) (L : Finset (Fin K)) (hL : GoodL h lam sg sz L) :
    L.card = ∑ i : Fin n, (if i.1 = 0 then 0 else (bb h lam sg i).toNat) := by
  classical
  rw [Finset.card_eq_sum_card_fiberwise (f := sz) (t := Finset.range n) ?_]
  · rw [Finset.sum_range]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← hL.2 i]
    congr 1
    ext k
    simp [Finset.mem_filter]
  · intro k hk
    rw [Finset.mem_coe, Finset.mem_range]
    replace hk := Finset.mem_coe.mp hk
    rcases sz_lt sg sz hsz hshape k with h1 | h1
    · exact h1
    · exact absurd h1 (Nat.pos_iff_ne_zero.mp (hL.1 k hk))

theorem sumB {n N : ℕ} (h : n + 1 = N) (lam : DomWeight N) (sg : DomWeight n) (hI : Interlace h lam sg) :
    ((∑ i : Fin n, (bb h lam sg i).toNat : ℕ) : ℤ) = degZ lam sg - lam.detShift := by
  subst h
  have hb : ∀ i : Fin n, (((bb rfl lam sg i).toNat : ℕ) : ℤ) = lam.w (Fin.castSucc i) - sg.w i :=
    fun i => b_val rfl lam sg hI i.1 i.2
  push_cast
  rw [Finset.sum_congr rfl (fun i _ => hb i), Finset.sum_sub_distrib]
  unfold degZ wsum
  rw [Fin.sum_univ_castSucc (f := lam.w), lam_detShift rfl lam,
    show (Fin.last n) = (⟨n, by omega⟩ : Fin (n + 1)) from rfl]
  ring

end PI.WGL.LTF
end
end

