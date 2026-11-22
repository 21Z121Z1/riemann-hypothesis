import Formalism.SharpRestriction.GrowthBounds.CoarseMultiplicity.Bundle0004
import Formalism.SharpRestriction.GrowthBounds.RootWeights.Bundle0001
import Formalism.SharpRestriction.GrowthBounds.CoarseMultiplicity.Bundle0002
import Formalism.SharpRestriction.GrowthBounds.BinomialRatio.Bundle0015
import Formalism.SharpRestriction.GrowthBounds.BinomialRatio.Bundle0003

-- bundled from Formalism.SharpRestriction.GrowthBounds.CoarseMultiplicity.FactAbs
section
noncomputable section

namespace Formalism.MainNotions.ColumnSystems.Pf

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees Formalism.MainNotions.G.GLWeightTheory

theorem fact_abs {D : Formalism.BasicNotions.D7} (h52 : Formalism.MainNotions.CovariantDegrees.FactorialUnitDecomposition D) {p : ℕ} (hp : p.Prime) (h5 : 5 ≤ p) (σ : Type)
    [Fintype σ] [DecidableEq σ] (odd : σ → Prop) [DecidablePred odd] (t ρ L : σ → ℕ)
    (hodd : ∀ v, odd v → L v = p ^ (t v + 1) ∧ ρ v < L v) (hend : ∀ v, ¬ odd v → L v = 1 ∧ ρ v = 0) (c : ℕ) :
    ∃ (T : Finset (σ →₀ ℕ)) (q : (σ →₀ ℕ) → ℚ),
      (∀ ν ∈ T, (ν.sum fun _ n => n) ≤ 4 * c ∧ (∀ v ∈ ν.support, odd v) ∧ PadicGe p (q ν) 0) ∧
      ∀ μ : σ →₀ ℕ, ∃ h : ℚ, PadicGe p h c ∧
        (∏ v, ((ρ v + L v * μ v).factorial : ℚ)) *
            (∑ ν ∈ T, q ν * ((ν.prod fun k i => (μ k).choose i : ℕ) : ℚ)) =
          (∏ v, ((ρ v).factorial : ℚ) * ((μ v).factorial : ℚ) * ((L v).factorial : ℚ) ^ (μ v)) * (1 + h) := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨h1, h2⟩ := h52 p hp h5
  set t' : σ → ℕ := fun v => if odd v then t v else 0 with ht'
  set ρ' : σ → ℕ := fun v => if odd v then ρ v else 0 with hρ'
  have hlt : ∀ k, ρ' k < p ^ (t' k + 1) := by
    intro k
    by_cases hk : odd k
    · simp only [hρ', ht', if_pos hk]
      rw [← (hodd k hk).1]; exact (hodd k hk).2
    · simp only [hρ', ht', if_neg hk]
      exact pow_pos hp.pos _
  obtain ⟨hunit, -, hop⟩ := h2 σ t' ρ' hlt
  obtain ⟨T, q, hT, hq⟩ := hop true c
  let E : (σ → ℕ) → (σ →₀ ℕ) := fun j => Finsupp.equivFunOnFinite.symm j
  have hE : Function.Injective E := Finsupp.equivFunOnFinite.symm.injective
  have hEa : ∀ j v, E j v = j v := fun j v => rfl
  refine ⟨(T.filter fun j => ∀ v, ¬ odd v → j v = 0).image E, fun ν => q ν, ?_, ?_⟩
  · intro ν hν
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.1 hν
    obtain ⟨hjT, hj0⟩ := Finset.mem_filter.1 hj
    refine ⟨?_, ?_, ?_⟩
    · rw [Finsupp.sum_fintype _ _ (fun _ => rfl)]
      exact (hT j hjT).1
    · intro v hv
      by_contra hno
      exact (Finsupp.mem_support_iff.1 hv) (hj0 v hno)
    · exact (hT j hjT).2
  · intro μ
    set e' : σ → ℕ := fun v => if odd v then μ v else 0 with he'
    set U : ℚ := ∏ k, cUnit (p ^ (t' k + 1)) (e' k) * dUnit (p ^ (t' k + 1)) (e' k) (ρ' k) with hU
    set A : ℚ := ∏ k, (((ρ' k + p ^ (t' k + 1) * e' k).factorial : ℕ) : ℚ) with hA
    set B : ℚ := ∏ k, ((ρ' k).factorial : ℚ) * ((e' k).factorial : ℚ) * ((p ^ (t' k + 1)).factorial : ℚ) ^ (e' k) with hB
    set g : ℚ := ∑ j ∈ T, q j * ∏ k, ((e' k).choose (j k) : ℚ) with hg
    have hU0 : U ≠ 0 := (hunit e').1
    have hUv : padicValRat p U = 0 := (hunit e').2
    have hAB : A = B * U := by
      rw [hA, hB, hU, ← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun k _ => ?_
      rw [h1 (t' k) (ρ' k) (e' k) (hlt k)]
      ring
    have hB0 : B ≠ 0 := by
      rw [hB]
      refine Finset.prod_ne_zero_iff.2 fun k _ => ?_
      have a1 : ((ρ' k).factorial : ℚ) ≠ 0 := Nat.cast_ne_zero.2 (Nat.factorial_ne_zero _)
      have a2 : ((e' k).factorial : ℚ) ≠ 0 := Nat.cast_ne_zero.2 (Nat.factorial_ne_zero _)
      have a3 : ((p ^ (t' k + 1)).factorial : ℚ) ≠ 0 := Nat.cast_ne_zero.2 (Nat.factorial_ne_zero _)
      exact mul_ne_zero (mul_ne_zero a1 a2) (pow_ne_zero _ a3)
    have hq' : PadicGe p (U⁻¹ - g) c := by
      have := hq e'
      simp only [if_true] at this
      have e : A / B = U := by rw [hAB]; field_simp
      rw [← hA, ← hB, e] at this
      exact this
    have hgs : (∑ ν ∈ (T.filter fun j => ∀ v, ¬ odd v → j v = 0).image E,
        q ν * ((ν.prod fun k i => (μ k).choose i : ℕ) : ℚ)) = g := by
      rw [Finset.sum_image fun a _ b _ h => hE h, hg, Finset.sum_filter]
      refine Finset.sum_congr rfl fun j _ => ?_
      by_cases hj : ∀ v, ¬ odd v → j v = 0
      · rw [if_pos hj, Finsupp.prod_fintype _ _ (fun _ => Nat.choose_zero_right _)]
        push_cast
        congr 1
        refine Finset.prod_congr rfl fun k _ => ?_
        by_cases hk : odd k
        · simp only [he', if_pos hk, hEa]
        · simp only [he', if_neg hk, hEa, hj k hk, Nat.choose_zero_right]
      · rw [if_neg hj]
        push_neg at hj
        obtain ⟨v, hv, hjv⟩ := hj
        have : (∏ k, ((e' k).choose (j k) : ℚ)) = 0 := by
          refine Finset.prod_eq_zero (Finset.mem_univ v) ?_
          simp only [he', if_neg hv]
          rw [Nat.choose_eq_zero_of_lt (Nat.pos_of_ne_zero hjv)]
          simp
        rw [this, mul_zero]
    refine ⟨(-U) * (U⁻¹ - g), ?_, ?_⟩
    · have hU' : PadicGe p (-U) 0 := padicGe_neg (Or.inr (by rw [hUv]; simp))
      have := padicGe_mul hU' hq'
      simpa using this
    · rw [hgs]
      set M : ℚ := ∏ v, (if odd v then (1 : ℚ) else ((μ v).factorial : ℚ)) with hM
      have l1 : (∏ v, ((ρ v + L v * μ v).factorial : ℚ)) = A * M := by
        rw [hA, hM, ← Finset.prod_mul_distrib]
        refine Finset.prod_congr rfl fun v _ => ?_
        by_cases hv : odd v
        · simp only [hρ', ht', he', if_pos hv, (hodd v hv).1, mul_one]
        · simp only [hρ', ht', he', if_neg hv, (hend v hv).1, (hend v hv).2]
          simp
      have l2 : (∏ v, ((ρ v).factorial : ℚ) * ((μ v).factorial : ℚ) * ((L v).factorial : ℚ) ^ (μ v)) = B * M := by
        rw [hB, hM, ← Finset.prod_mul_distrib]
        refine Finset.prod_congr rfl fun v _ => ?_
        by_cases hv : odd v
        · simp only [hρ', ht', he', if_pos hv, (hodd v hv).1, mul_one]
        · simp only [hρ', ht', he', if_neg hv, (hend v hv).1, (hend v hv).2]
          simp
      rw [l1, l2, hAB]
      field_simp
      ring

end Formalism.MainNotions.ColumnSystems.Pf
end
end

-- bundled from Formalism.SharpRestriction.GrowthBounds.CoarseMultiplicity.MulMatQOne
section
noncomputable section

open MvPolynomial

namespace Formalism.MainNotions.ColumnSystems.Pf.TF

open Formalism.MainNotions.G Formalism.GradedWeylDivisibility
open Formalism.MainNotions.G.LatticeSystems (la_tw lb_D la_tw_det lb_D_det H0_eq_twisted_nabla la_indep)
open Formalism.L2.G.Model (Lin Th0 Aa Lin_comp Lin_one Lin_Pol Lin_smul Th0_inj mem_tens_nabla mem_tens_dw map_Pol mem_Pol VS
  letterWt_anti tensor_lattice_twist_eq tens_Le edgeLat_of la_tw_mul la_tw_transpose la_tw_inv dE invT_mul_D dual_edgeBasis w_ne p_eq
  pQ_ne kapR kapR_alg lift_eq Bm Bm_eq Mx Mx_det Avec pol_iff thF gen_equiv gen_A gen_R mem_scale2 edgePlane)
open Formalism.L2.G.Model.TS

section

variable {p n' : ℕ} [Fact p.Prime] {W Qq O Kf : Type} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field Qq]
  [Algebra W Qq] [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf]
  {ι : Qq →+* Kf} {σ : Qq ≃+* Qq} {jO : W →+* O} {w : O}

theorem Avec_eq {m : ℕ} (TT : Finset (Fin n')) (aT bT : Fin n' → ℕ) :
    (Avec (vecH TT) (hhDegs TT aT bT) : ℤ) = AHH TT aT bT := by
  unfold Avec AHH
  push_cast
  rw [Fintype.sum_prod_type]
  simp only [Fintype.sum_bool, vecH, hhDegs, if_true, Bool.false_eq_true, if_false, add_zero]
  exact Finset.sum_coe_sort TT (fun s => (hhDeg aT bT s true : ℤ))

theorem flatTheta (hS : HidaSetting p n' W Qq O Kf ι σ jO w) (φ : WF p n' ≃+* W) (hφ : IsWittIdent σ φ) (m : ℕ)
    (TT : Finset (Fin n')) (aT bT : Fin n' → ℕ) (hm : 1 ≤ m) (h : Matrix (Fin (m + 1)) (Fin (m + 1)) Qq)
    (hh : IsUnit h.det) :
    ∃ Θ : ↥((Pol (KK O) (ι := TT × Bool) (m + 1) (hhDegs TT aT bT)).restrictScalars O) ≃ₗ[O]
        ↥(VHH (m := m) Kf TT aT bT),
      IsFlatTheta ι σ jO w φ TT aT bT h Θ ∧
      ∀ F, ((Θ F : ↥(VHH (m := m) Kf TT aT bT)) : MvPolynomial ((TT × Bool) × (Fin (m + 1) × Fin (m + 1))) Kf) =
        thF hS m (vecH TT) (fun x => la_tw ι σ x.1.val.val h) F.1 := by
  letI : Algebra (WF p n') O := algOfIdent jO φ
  have hw := w_ne hS
  obtain ⟨Θ0, hΘ0⟩ := gen_equiv hS m hm (fun x : TT × Bool => x.2) (Formalism.MainNotions.ColumnSystems.hhDegs TT aT bT)
    (fun x => la_tw ι σ x.1.val.val h) (fun x => la_tw_det _ _ _ _ hh)
  have hV : VS Kf m (fun x : TT × Bool => x.2) (Formalism.MainNotions.ColumnSystems.hhDegs TT aT bT) = VHH (m := m) Kf TT aT bT := rfl
  let Θ : ↥((Pol (KK O) (ι := TT × Bool) (m + 1) (Formalism.MainNotions.ColumnSystems.hhDegs TT aT bT)).restrictScalars O) ≃ₗ[O]
      ↥(VHH (m := m) Kf TT aT bT) := Θ0.trans ((LinearEquiv.ofEq _ _ hV).restrictScalars O)
  have hΘ : ∀ F, ((Θ F : ↥(VHH (m := m) Kf TT aT bT)) :
      MvPolynomial ((TT × Bool) × (Fin (m + 1) × Fin (m + 1))) Kf) =
      thF hS m (fun x : TT × Bool => x.2) (fun x => la_tw ι σ x.1.val.val h) F.1 := fun F => hΘ0 F
  refine ⟨Θ, ⟨?_, ?_, ?_⟩, hΘ⟩
  · intro F
    rw [gen_A hS m hm (fun x : TT × Bool => x.2) (Formalism.MainNotions.ColumnSystems.hhDegs TT aT bT)
      (fun x => la_tw ι σ x.1.val.val h) (fun x => la_tw_det _ _ _ _ hh) F.1 F.2, ← hΘ F,
      ← tensor_lattice_twist_eq hS m (fun x : TT × Bool => x.2) (Formalism.MainNotions.ColumnSystems.hhDegs TT aT bT) (fun x => x.1.val) h hh]
    rfl
  · intro g hg e he F i
    have h1 : InWjRg p n' O w 1 (Formalism.MainNotions.ColumnSystems.hhLetters TT) g F.1 i ↔
        ∃ y ∈ tensorLat O Kf (fun s : TT × Bool => nablaLTw O Kf m
            (letterWt m (Formalism.MainNotions.ColumnSystems.hhDegs TT aT bT s) s.2) (Mx ι σ w φ 1 (fun x : TT × Bool => x.1.val) h g s)),
          thF hS m (fun x : TT × Bool => x.2) (fun x => la_tw ι σ x.1.val.val h) F.1 =
            (algebraMap O Kf w ^ ((i : ℤ) -
              (Avec (fun x : TT × Bool => x.2) (Formalism.MainNotions.ColumnSystems.hhDegs TT aT bT) : ℤ))) • y :=
      gen_R hS φ hφ m hm 1 (Formalism.MainNotions.ColumnSystems.hhLetters TT) (fun x => x.1.val) (fun _ => rfl)
        (Formalism.MainNotions.ColumnSystems.hhDegs TT aT bT) h hh g hg F.1 F.2 i
    rw [h1, ← hΘ F, ← tens_Le hS φ m 1 (fun x : TT × Bool => x.2) (Formalism.MainNotions.ColumnSystems.hhDegs TT aT bT) (fun x => x.1.val)
      h hh g hg e he]
    have hA : (Avec (fun x : TT × Bool => x.2) (Formalism.MainNotions.ColumnSystems.hhDegs TT aT bT) : ℤ) = AHH TT aT bT :=
      Avec_eq (m := m) TT aT bT
    have h2 := mem_scale2 (O := O) (VHH (m := m) Kf TT aT bT)
      (HHten O TT aT bT fun s => LeAt p ι σ w s.val e) (algebraMap O Kf w ^ (i : ℤ))
      (algebraMap O Kf w ^ (-AHH TT aT bT)) (zpow_ne_zero _ hw) (zpow_ne_zero _ hw) (Θ F)
    have e1 : algebraMap O Kf w ^ (i : ℤ) * algebraMap O Kf w ^ (-AHH TT aT bT) = algebraMap O Kf w ^
        ((i : ℤ) - (Avec (fun x : TT × Bool => x.2) (Formalism.MainNotions.ColumnSystems.hhDegs TT aT bT) : ℤ)) := by
      rw [← zpow_add₀ hw, ← sub_eq_add_neg, ← hA]
    rw [e1] at h2
    exact h2.symm
  · intro e he hsrc
    exact (edgePlane p n' W Qq O Kf ι σ jO w hS φ hφ m 1 h hh).1 e he hsrc

theorem matQ_one (φ : WF p n' ≃+* W) (k : ℕ) : matQ (Qq := Qq) φ (1 : Matrix (Fin k) (Fin k) (WF p n')) = 1 := by
  ext a b
  simp only [matQ, Matrix.one_apply]
  split_ifs <;> simp

theorem mul_matQ_one (φ : WF p n' ≃+* W) {k : ℕ} (h : Matrix (Fin k) (Fin k) Qq) :
    h * ((matQ φ (1 : Matrix (Fin k) (Fin k) (WF p n')))⁻¹).transpose = h := by
  rw [matQ_one]
  simp

theorem isGLW_one (k : ℕ) : IsGLW (1 : Matrix (Fin k) (Fin k) (WF p n')) := by
  simp [IsGLW]

theorem Aa_dual' {K : Type} [Field K] {m : ℕ} (vec : Bool) (M : Matrix (Fin (m + 1)) (Fin (m + 1)) K)
    (hM : IsUnit M.det) : Aa vec ((M⁻¹).transpose) * (Aa vec M).transpose = 1 := by
  cases vec
  · simp [Aa, Matrix.transpose_nonsing_inv, Matrix.nonsing_inv_nonsing_inv _ hM, Matrix.mul_nonsing_inv _ hM]
  · simp [Aa, ← Matrix.transpose_mul, Matrix.mul_nonsing_inv _ hM]

theorem lift_Pol (hS : HidaSetting p n' W Qq O Kf ι σ jO w) (φ : WF p n' ≃+* W) (hφ : IsWittIdent σ φ) (m : ℕ)
    (TT : Finset (Fin n')) (aT bT : Fin n' → ℕ) (g : Matrix (Fin (m + 1)) (Fin (m + 1)) (WF p n')) (hg : IsGLW g)
    (F : MvPolynomial ((TT × Bool) × Fin (m + 1)) (KK O)) (hF : F ∈ Pol (KK O) (m + 1) (hhDegs TT aT bT)) :
    letI : Algebra (WF p n') O := algOfIdent jO φ
    liftSubst p n' O w 1 (hhLetters TT) g F ∈ Pol (KK O) (m + 1) (hhDegs TT aT bT) := by
  letI : Algebra (WF p n') O := algOfIdent jO φ
  rw [pol_iff hS, lift_eq hS φ hφ 1 (hhLetters TT) (fun x => x.1.val) (fun _ => rfl) g hg F]
  exact Lin_Pol _ _ ((pol_iff hS _ _ _).1 hF)

theorem lift_one (hS : HidaSetting p n' W Qq O Kf ι σ jO w) (φ : WF p n' ≃+* W) (hφ : IsWittIdent σ φ) (m : ℕ)
    (TT : Finset (Fin n')) (aT bT : Fin n' → ℕ) (h : Matrix (Fin (m + 1)) (Fin (m + 1)) Qq) (hh : IsUnit h.det)
    (F : MvPolynomial ((TT × Bool) × Fin (m + 1)) (KK O)) (hF : F ∈ Pol (KK O) (m + 1) (hhDegs TT aT bT)) :
    letI : Algebra (WF p n') O := algOfIdent jO φ
    map (kapR hS) (liftSubst p n' O w 1 (hhLetters TT) (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) (WF p n')) F) =
      (algebraMap O Kf w ^ Avec (vecH TT) (hhDegs TT aT bT)) •
        Lin (fun x : TT × Bool => Aa x.2 (la_tw ι σ x.1.val.val h * lb_D (m + 1) 1 (algebraMap O Kf w)))
          (Lin (fun x : TT × Bool => Aa x.2 (la_tw ι σ x.1.val.val h)⁻¹) (map (kapR hS) F)) := by
  letI : Algebra (WF p n') O := algOfIdent jO φ
  have hw := w_ne hS
  set c := algebraMap O Kf w with hc
  have hF' := (pol_iff hS _ _ _).1 hF
  rw [lift_eq hS φ hφ 1 (hhLetters TT) (fun x => x.1.val) (fun _ => rfl) 1 (isGLW_one _) F]
  have hB : Bm ι σ w φ 1 (hhLetters TT).vec (fun x : TT × Bool => x.1.val) (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) (WF p n')) =
      fun x => (if (hhLetters TT).vec x then c else 1) •
      (Aa ((hhLetters TT).vec x) (la_tw ι σ x.1.val.val h)⁻¹ *
        Aa ((hhLetters TT).vec x) (Mx ι σ w φ 1 (fun x : TT × Bool => x.1.val) h 1 x)) :=
    funext fun x => Bm_eq hw φ 1 (hhLetters TT).vec (fun x : TT × Bool => x.1.val) h hh 1 (isGLW_one _) x
  rw [hB, Lin_smul _ _ _ hF', Lin_comp]
  have hprod : ∏ x : TT × Bool, (if (hhLetters TT).vec x then c else 1) ^ hhDegs TT aT bT x =
      c ^ Avec (vecH TT) (hhDegs TT aT bT) := by
    unfold Avec
    rw [← Finset.prod_pow_eq_pow_sum]
    apply Finset.prod_congr rfl
    intro x _
    show (if x.2 = true then c else 1) ^ _ = c ^ (if x.2 = true then _ else 0)
    split_ifs <;> simp
  rw [hprod]
  have hfun : (fun x : TT × Bool => Aa ((hhLetters TT).vec x) (la_tw ι σ x.1.val.val h)⁻¹ *
        Aa ((hhLetters TT).vec x) (Mx ι σ w φ 1 (fun x : TT × Bool => x.1.val) h 1 x)) =
      fun x : TT × Bool => Aa x.2 (la_tw ι σ x.1.val.val h)⁻¹ * Aa x.2 (la_tw ι σ x.1.val.val h * lb_D (m + 1) 1 c) := by
    funext x
    unfold Mx
    rw [mul_matQ_one]
    rfl
  rw [hfun]

end

end Formalism.MainNotions.ColumnSystems.Pf.TF
end
end

-- bundled from Formalism.SharpRestriction.GrowthBounds.CoarseMultiplicity.TopOddNeEnd
section
noncomputable section

namespace Formalism.MainNotions.ColumnSystems.Pf

open Formalism.MainNotions.G MvPolynomial

theorem eig_one {R : Type} [CommSemiring R] {σ : Type} (ν μ : σ →₀ ℕ) (u : MvPolynomial σ R) :
    coeff μ (monomial ν (1 : R) * divDer ν u) = coeff μ u * ((ν.prod fun k i => (μ k).choose i : ℕ) : R) := by
  classical
  unfold divDer
  rw [Finset.mul_sum, coeff_sum]
  have key : ∀ m ∈ u.support, coeff μ (monomial ν (1 : R) * (if ν ≤ m then
      monomial (m - ν) (coeff m u * ((ν.prod fun k i => (m k).choose i : ℕ) : R)) else 0)) =
      if m = μ then coeff μ u * ((ν.prod fun k i => (μ k).choose i : ℕ) : R) else 0 := by
    intro m _
    by_cases h1 : ν ≤ m
    · rw [if_pos h1, monomial_mul, one_mul, add_tsub_cancel_of_le h1, coeff_monomial]
      by_cases h2 : m = μ
      · subst h2; simp
      · rw [if_neg h2, if_neg h2]
    · rw [if_neg h1, mul_zero, coeff_zero]
      by_cases h2 : m = μ
      · subst h2
        rw [if_pos rfl]
        obtain ⟨k, hk⟩ : ∃ k, ¬ ν k ≤ m k := by
          by_contra hcon
          push_neg at hcon
          exact h1 hcon
        have hk' : m k < ν k := not_le.1 hk
        have h0 : (ν.prod fun k i => (m k).choose i) = 0 :=
          Finset.prod_eq_zero (i := k) (Finsupp.mem_support_iff.2 (by omega)) (Nat.choose_eq_zero_of_lt hk')
        rw [h0]; simp
      · rw [if_neg h2]
  rw [Finset.sum_congr rfl key, Finset.sum_ite_eq']
  split_ifs with h
  · rfl
  · rw [notMem_support_iff.1 h, zero_mul]

theorem eigAt : EigAt := by
  intro O _ _ σ T q u μ
  unfold gOp gEv
  rw [coeff_sum, map_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun ν _ => ?_
  rw [coeff_smul, eig_one, Algebra.smul_def, map_mul, map_natCast]
  ring

theorem fock_monoMap {K : Type} [Field K] {σ τ : Type} (f : MvPolynomial σ K →ₗ[K] MvPolynomial τ K)
    (ε : (σ →₀ ℕ) → (τ →₀ ℕ)) (hε : Function.Injective ε) (hf : ∀ μ c, f (monomial μ c) = monomial (ε μ) c)
    (u u' : MvPolynomial σ K) :
    fock (f u) (f u') = ∑ μ ∈ u.support, u.coeff μ * u'.coeff μ * (expFact (ε μ) : K) := by
  classical
  have hexp : ∀ v : MvPolynomial σ K, f v = ∑ μ ∈ v.support, monomial (ε μ) (v.coeff μ) := by
    intro v
    conv_lhs => rw [← v.support_sum_monomial_coeff]
    rw [map_sum]
    exact Finset.sum_congr rfl fun μ _ => hf μ _
  have hco : ∀ (v : MvPolynomial σ K) (μ : σ →₀ ℕ), coeff (ε μ) (f v) = coeff μ v := by
    intro v μ
    rw [hexp, coeff_sum]
    have : ∀ μ' ∈ v.support, coeff (ε μ) (monomial (ε μ') (v.coeff μ')) = if μ' = μ then v.coeff μ else 0 := by
      intro μ' _
      rw [coeff_monomial]
      by_cases h : μ' = μ
      · subst h; simp
      · rw [if_neg h, if_neg fun h' => h (hε h')]
    rw [Finset.sum_congr rfl this, Finset.sum_ite_eq']
    split_ifs with h
    · rfl
    · exact (notMem_support_iff.1 h).symm
  have hsupp : (f u).support ⊆ u.support.image ε := by
    rw [hexp]
    refine (support_sum).trans ?_
    intro m hm
    obtain ⟨μ, hμ, hm⟩ := Finset.mem_biUnion.1 hm
    have := support_monomial_subset hm
    rw [Finset.mem_singleton] at this
    exact Finset.mem_image.2 ⟨μ, hμ, this.symm⟩
  rw [Formalism.MainNotions.G.GLWeightTheory.fock_form_finset_sum _ _ _ hsupp, Finset.sum_image fun a _ b _ h => hε h]
  exact Finset.sum_congr rfl fun μ _ => by rw [hco, hco]

theorem topOdd_inj (X : Loc) (j : Fin (numSeg X.TT)) : Function.Injective (topOdd X j) := by
  intro i i' e
  have e' : segPos X.TT j i = segPos X.TT j i' := congrArg Subtype.val e
  have h1 := (pos_spec X.TT j i).2
  have h2 := (pos_spec X.TT j i').2
  rw [e'] at h1
  exact (dist_strictMono X.TT j).injective (h1.symm.trans h2)

theorem topOdd_ne_end (X : Loc) (j : Fin (numSeg X.TT)) (i : Fin (segS X.TT j)) : topOdd X j i ≠ topEnd X j := by
  intro e
  have e' : segPos X.TT j i = segNext X.TT j := congrArg Subtype.val e
  exact (pos_mem X.TT j i).2 (e' ▸ (next_mem X.TT j).2)

end Formalism.MainNotions.ColumnSystems.Pf
end
end

