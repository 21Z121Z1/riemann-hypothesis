import Mathlib
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.Bundle0019
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.Bundle0022
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.Bundle0054
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.Bundle0001
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0007
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.Bundle0027
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.Bundle0029
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0073
import Development.WeilBound.CoreStatements.FlagImmersions.TowerNefGenericDominant
import Development.AutomorphicSpectrum.Statements.MetricStatements.AgreementIffGuarded
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.Bundle0003
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.Bundle0004
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.Bundle0006

-- bundled from Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.FlagChainArithVariety
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Top.FlDeg

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4
open GroundTheory.Heights₂.Heights.LowerBoundFree GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter
open GroundTheory.Heights₂.Heights.LowerBoundFree.FlagRatioTrdeg GroundTheory.Heights₂.Heights.LowerBoundFree.FlagArithVar

theorem pivotRatio_algebraicIndependent (F : Type) [Field F] (Ψ : Type) (n : ℕ) :
    AlgebraicIndependent F (pivotRatio F Ψ n) := by
  classical
  have hy := pivot_indep F Ψ n
  let δ : PivotIdxLe Ψ n → PivotIdxLe Ψ n :=
    fun q => (q.1, ⟨q.2.1, ⟨Fin.castLE (Nat.sub_le n 1) q.2.1, by simp⟩⟩)
  have hz := ratio_indep F hy δ (fun q => rfl)
  let incl : PivotIdx Ψ n → PivotIdxLe Ψ n := fun q => (q.1, ⟨q.2.1, ⟨q.2.2.1, q.2.2.2.le⟩⟩)
  have hincl : Function.Injective incl := by
    rintro ⟨τ, a, b, hb⟩ ⟨τ', a', b', hb'⟩ h
    simp only [incl, Prod.mk.injEq, Sigma.mk.inj_iff] at h
    obtain ⟨h0, h1, h2⟩ := h
    subst h0 h1
    simp only [heq_eq_eq, Subtype.mk.injEq] at h2
    subst h2
    rfl
  have hrat : (fun q : PivotIdxLe Ψ n => if δ q = q then pivotMinor (genMatFr F Ψ n q.1) q.2.1 q.2.2.1 else
      pivotMinor (genMatFr F Ψ n q.1) q.2.1 q.2.2.1 / pivotMinor (genMatFr F Ψ n (δ q).1) (δ q).2.1 (δ q).2.2.1) ∘
        incl = pivotRatio F Ψ n := by
    funext q
    have hne : δ (incl q) ≠ incl q := by
      intro h
      have := congrArg (fun r : PivotIdxLe Ψ n => ((r.2.2.1 : Fin n) : ℕ)) h
      simp only [δ, incl, Fin.val_castLE] at this
      have := q.2.2.2
      omega
    simp only [Function.comp_apply, hne, if_false]
    rfl
  exact hrat ▸ hz.comp incl hincl

theorem flag_mem_of_le (F : Type) [Field F] {K : Type} [Field K] [Algebra F K] {m : ℕ}
    (g : Matrix (Fin m) (Fin m) K) (A : IntermediateField F K) (hL : ∀ a, leadMinor g a ≠ 0)
    (j : Fin (m - 1))
    (hA : ∀ (a : Fin (m - 1)) (b : Fin m), (a : ℕ) ≤ j → (a : ℕ) < b → pivotMinor g a b / leadMinor g a ∈ A)
    (S : PluckerBlocks m m j) : flagMinor g j S / leadMinor g j ∈ A := by
  have hj : (j : ℕ) + 1 ≤ m := by have := j.2; omega
  have hent : ∀ (a : Fin (m - 1)) (b : Fin m), (a : ℕ) ≤ j → pivotMinor g a b / leadMinor g a ∈ A := by
    intro a b haj
    rcases lt_trichotomy (b : ℕ) a with h | h | h
    · rw [pivotMinor_eq_zero g a b h, zero_div]
      exact A.zero_mem
    · have e : b = Fin.castLE (Nat.sub_le m 1) a := Fin.ext h
      subst e
      show leadMinor g a / leadMinor g a ∈ A
      rw [div_self (hL a)]
      exact A.one_mem
    · exact hA a b haj h
  let U : Matrix (Fin (j + 1)) (Fin (j + 1)) K := Matrix.of fun r s =>
    pivotMinor g ⟨r, by have := r.2; have := j.2; omega⟩ (S.1.orderEmbOfFin S.2 s) /
      leadMinor g ⟨r, by have := r.2; have := j.2; omega⟩
  have hP : (pivotMatrix g).submatrix (Fin.castLE hj) (S.1.orderEmbOfFin S.2) =
      Matrix.diagonal (fun r : Fin (j + 1) => leadMinor g ⟨r, by have := r.2; have := j.2; omega⟩) * U := by
    ext r s
    rw [Matrix.diagonal_mul]
    simp only [Matrix.submatrix_apply, pivotMatrix, Matrix.of_apply, U]
    rw [dif_pos (by simp only [Fin.val_castLE]; have := r.2; have := j.2; omega)]
    rw [mul_div_cancel₀ _ (hL _)]
    rfl
  have hdet : flagMinor (pivotMatrix g) j S =
      (∏ r : Fin (j + 1), leadMinor g ⟨r, by have := r.2; have := j.2; omega⟩) * U.det := by
    unfold flagMinor
    rw [hP, Matrix.det_mul, Matrix.det_diagonal]
  have hid := FlagPivotIdentity.proof K m g j S
  rw [prod_Iic_fin, hdet] at hid
  have hne : (∏ r : Fin (j + 1), leadMinor g ⟨r, by have := r.2; have := j.2; omega⟩) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun r _ => hL _
  have hU : flagMinor g j S / leadMinor g j = U.det := by
    rw [div_eq_iff (hL j)]
    apply mul_right_cancel₀ hne
    linear_combination hid
  rw [hU, Matrix.det_apply]
  refine A.sum_mem fun σ _ => ?_
  rw [Units.smul_def]
  exact zsmul_mem (A.prod_mem fun r _ => hent _ _ (by have := r.2; simp only; omega)) _

variable {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {N : ℕ} {K : Type}

abbrev PivPos (j : K → FlBlock Ψ N) : Type := Σ k : K, {b : Fin N // ((j k).2 : ℕ) < b}

def pivPosIncl (j : K → FlBlock Ψ N) (x : PivPos j) : PivotIdx Ψ N := ((j x.1).1, ⟨(j x.1).2, x.2⟩)

theorem pivPosIncl_injective {j : K → FlBlock Ψ N} (hj : Function.Injective j) :
    Function.Injective (pivPosIncl j) := by
  rintro ⟨k, b, hb⟩ ⟨k', b', hb'⟩ h
  simp only [pivPosIncl, Prod.mk.injEq, Sigma.mk.inj_iff] at h
  obtain ⟨h0, h1, h2⟩ := h
  have hk : k = k' := hj (Prod.ext h0 h1)
  subst hk
  simp only [heq_eq_eq, Subtype.mk.injEq] at h2
  subst h2
  rfl

theorem card_pivPos [Fintype K] (j : K → FlBlock Ψ N) : Fintype.card (PivPos j) = cellDim j := by
  rw [Fintype.card_sigma, cellDim]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Fintype.card_subtype]
  have : (Finset.univ.filter fun b : Fin N => ((j k).2 : ℕ) < b) =
      Finset.Ioi (Fin.castLE (Nat.sub_le N 1) (j k).2) := by
    ext b
    simp [Fin.lt_def]
  rw [this, Fin.card_Ioi]
  simp

theorem pivotRatio_algebraicIndependent_of_eq (Ψ : Type) (N : ℕ) (I : Algebra ℚ (ΩFl Ψ N))
    (hI : I = OreLocalization.instAlgebra) :
    @AlgebraicIndependent _ ℚ (ΩFl Ψ N) (pivotRatio ℚ Ψ N) _ _ I := by
  subst hI
  exact pivotRatio_algebraicIndependent ℚ Ψ N

theorem pivotRatio_rat_algebraicIndependent (Ψ : Type) (N : ℕ) :
    AlgebraicIndependent ℚ (pivotRatio ℚ Ψ N : PivotIdx Ψ N → ΩFl Ψ N) :=
  pivotRatio_algebraicIndependent_of_eq Ψ N _ (Subsingleton.elim _ _)

theorem isArithVar_pPart (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ) (K : Type) [Fintype K] [Nonempty K]
    (j : K → FlBlock Ψ N) (hj : IsChain j) : IsArithVar (PPart j) (cellDim j + 1) := by
  classical
  let e : PivPos j ≃ Fin (cellDim j) := Fintype.equivFinOfCardEq (card_pivPos j)
  let t : Fin (cellDim j) → ΩFl Ψ N := fun i => pivotRatio ℚ Ψ N (pivPosIncl j (e.symm i))
  let c : ∀ k, PIdx j k := fun k => leadIdx Ψ N (j k)
  have hL : ∀ (τ : Ψ) (a : Fin (N - 1)), leadMinor (genMatFr ℚ Ψ N τ) a ≠ 0 := fun τ a =>
    GenLeadMinorNeZero.full ℚ Ψ N τ a
  have hc : ∀ k, yPart j ⟨k, c k⟩ ≠ 0 := fun k => by
    show yFl Ψ N ⟨j k, leadIdx Ψ N (j k)⟩ ≠ 0
    rw [yFl_lead]
    exact hL _ _
  have hind : AlgebraicIndependent ℚ t := by
    exact (pivotRatio_rat_algebraicIndependent Ψ N).comp _
      ((pivPosIncl_injective hj.inj).comp e.symm.injective)
  have hmem : ∀ i, t i ∈ IntermediateField.adjoin ℚ (coneRatios (yPart j) c) := by
    intro i
    refine IntermediateField.subset_adjoin ℚ _ ?_
    show pivotRatio ℚ Ψ N (pivPosIncl j (e.symm i)) ∈ coneRatios (yPart j) c
    obtain ⟨k, b, hb⟩ := e.symm i
    let S : PluckerBlocks N N (j k).2 := ⟨Finset.univ.image (pivotCols (j k).2 b), card_image_pivotCols _ b hb.le⟩
    refine ⟨⟨k, ⟨S.1.orderEmbOfFin S.2, (S.1.orderEmbOfFin S.2).strictMono⟩⟩, ?_⟩
    have h1 := flagMinor_eq_yFl Ψ N (j k).1 (j k).2 S
    have h2 := pivotMinor_eq_flagMinor (genMatFr ℚ Ψ N (j k).1) (j k).2 b hb.le
    have h3 := yFl_lead Ψ N (j k)
    show yFl Ψ N ⟨j k, ⟨S.1.orderEmbOfFin S.2, (S.1.orderEmbOfFin S.2).strictMono⟩⟩ /
      yFl Ψ N ⟨j k, leadIdx Ψ N (j k)⟩ = pivotMinor (genMatFr ℚ Ψ N (j k).1) (j k).2 b /
        leadMinor (genMatFr ℚ Ψ N (j k).1) (j k).2
    rw [h3]
    congr 1
    exact h1.symm.trans h2.symm
  have halg : ∀ r ∈ coneRatios (yPart j) c, IsAlgebraic (IntermediateField.adjoin ℚ (Set.range t)) r := by
    rintro _ ⟨⟨k, A⟩, rfl⟩
    have hT : ∀ (k' : K) (b : Fin N) (h : ((j k').2 : ℕ) < b),
        pivotMinor (genMatFr ℚ Ψ N (j k').1) (j k').2 b / leadMinor (genMatFr ℚ Ψ N (j k').1) (j k').2 ∈
          IntermediateField.adjoin ℚ (Set.range t) := fun k' b h =>
      IntermediateField.subset_adjoin ℚ _ ⟨e ⟨k', b, h⟩, by
        show pivotRatio ℚ Ψ N (pivPosIncl j (e.symm (e ⟨k', b, h⟩))) = _
        rw [e.symm_apply_apply]
        rfl⟩
    have hm : yPart j ⟨k, A⟩ / yPart j ⟨k, c k⟩ ∈ IntermediateField.adjoin ℚ (Set.range t) := by
      show yFl Ψ N ⟨j k, A⟩ / yFl Ψ N ⟨j k, leadIdx Ψ N (j k)⟩ ∈ _
      rw [yFl_lead, yFl_eq_flagMinor]
      refine flag_mem_of_le ℚ (genMatFr ℚ Ψ N (j k).1) _ (hL _) (j k).2 (fun a b ha hb => ?_) _
      obtain ⟨k', hk'⟩ := hj.down k ((j k).1, a) rfl ha
      have h := hT k' b (by rw [hk']; exact hb)
      rw [hk'] at h
      exact h
    exact isAlgebraic_algebraMap (⟨_, hm⟩ : IntermediateField.adjoin ℚ (Set.range t))
  exact CoordConeArithVar.full K (PIdx j) (ΩFl Ψ N) (yPart j) c (cellDim j) t ‹_› hc hind hmem halg

end GlobalTheory.CompanionTheory.Ar.Top.FlDeg
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.FlagHeightI9Properties
section
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top

namespace GlobalTheory.CompanionTheory.Ar.Top

theorem flag_gap_eq_sub {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {N : ℕ} (lam : Wt Ψ N) (τ : Ψ) (a : Fin N)
    (h : (a : ℕ) + 1 < N) :
    PB.gap (fun x : Ψ × Fin N => lam x.1 x.2) (τ, a) = lam τ a - lam τ ⟨(a : ℕ) + 1, h⟩ := by
  simp [PB.gap, PB.gapX, h]

theorem flag_dim_eq_antisymmetric_degree (Ψ : Type) [Fintype Ψ] (N : ℕ) :
    dimFl Ψ N = GroundTheory.Heights₂.Heights.antisymDegree Ψ N := by
  simp [dimFl, GroundTheory.Heights₂.Heights.antisymDegree, Nat.choose_two_right]

theorem flag_height_I9 : PB.FlagHeight → PB.Inputs → ∀ II : IntersectionSystem, IsFullIntersectionSystem II →
    ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ) [Nonempty Ψ], 2 ≤ N →
      I9 (Ψ := Ψ) (N := N) (hhFl Ψ N II) := by
  intro hFH hIn II hII Ψ _ _ N _ hN
  have hA : IsArithVar (GroundTheory.Heights₂.Heights.LowerBoundFree.PFl Ψ N) (dimFl Ψ N + 1) := by
    rw [flag_dim_eq_antisymmetric_degree]
    exact (GlobalTheory.T.flag_variety_boundary_dimension_drop Ψ N hN).1
  have hev : ∀ lam : Wt Ψ N, hhFl Ψ N II (linRoot lam ^ (dimFl Ψ N + 1)) =
      eval (fun x => lam x.1 x.2) (PB.hFlPoly Ψ N II) := fun lam =>
    GlobalTheory.T.flag_height_polynomial_eval II hII Ψ N lam hN hA
  obtain ⟨-, hgap, hdom⟩ := hFH hIn II hII Ψ N hN
  refine ⟨?_, ?_, ?_⟩
  · rintro lam - ⟨τ, a, b, hab, heq⟩
    have h : (a : ℕ) + 1 < N := hab ▸ b.2
    have hb : b = ⟨(a : ℕ) + 1, h⟩ := Fin.ext hab
    rw [hev]
    refine hgap _ (τ, a) h ?_
    rw [flag_gap_eq_sub lam τ a h, ← hb, heq, sub_self]
  · intro lam hlam
    rw [hev]
    refine hdom _ fun p hp => ?_
    obtain ⟨τ, a⟩ := p
    rw [flag_gap_eq_sub lam τ a hp, sub_nonneg]
    exact hlam τ a ⟨(a : ℕ) + 1, hp⟩ (Fin.le_def.2 (Nat.le_succ _))
  · intro τ Q hQ
    exact GlobalTheory.T.flag_height_power_sum_one_zero II hII Ψ N τ Q hN hA hQ

end GlobalTheory.CompanionTheory.Ar.Top
end

-- bundled from Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.RealTowerNefGeneral
section
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top

namespace GlobalTheory.CompanionTheory.Ar.Top

theorem rt_nefgen : PB.NefPol → PB.Inputs → ∀ II : IntersectionSystem, IsFullIntersectionSystem II → ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ) (T : RootTower Ψ N) (R : RealTower T), R.Smooth → R.Flat → ∀ B c, (∀ lam : Wt Ψ N, Dominant lam → (T.M B c).NefGen lam 0) ∧ (T.M B c).NefGen 0 1 :=
  @RootFieldNumerics.tower_nef_generic_dominant

end GlobalTheory.CompanionTheory.Ar.Top
end

-- bundled from Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.RealTowerProportional
section
noncomputable section

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top GroundTheory.Heights₂.Heights

namespace GlobalTheory.CompanionTheory.Ar.Top

namespace RealProp

theorem map_monomial_eq_zero {J : Type} [Fintype J] [DecidableEq J] (d : ℕ) (Φ : MvPolynomial J ℝ →ₗ[ℝ] ℝ)
    (h : ∀ c : J → ℝ, Φ ((-∑ x, C (c x) * X x) ^ d) = 0) (m : J →₀ ℕ) (hm : m.degree = d) :
    Φ (monomial m 1) = 0 := by
  obtain ⟨Pl, -, hev, hco, -⟩ := GlobalTheory.T.polarization_polynomial_coeff_bound J d Φ
  have hP : Pl = 0 := MvPolynomial.funext fun c => by rw [hev c, h c, map_zero]
  have h0 := hco m hm
  rw [hP, coeff_zero] at h0
  have hmul : ((m.multinomial : ℕ) : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.multinomial_pos _ _).ne'
  have hpow : ((-1 : ℝ) ^ d) ≠ 0 := pow_ne_zero _ (by norm_num)
  exact (mul_eq_zero.mp h0.symm).resolve_left (mul_ne_zero hpow hmul)

theorem eval_toWt {Ψ : Type} {N : ℕ} (lam : Ψ × Fin N → ℝ) (P : MvPolynomial (Ψ × Fin N) ℝ) :
    eval lam (PB.toWt P) = eval (PB.gap lam) P := by
  unfold PB.toWt
  induction P using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p n hp => simp only [map_mul, hp, aeval_X, eval_X, PB.gap]

theorem eval_degPoly_comap_some {e : ℕ} {σ : Type} [Fintype σ] (S : PB.AnSys e (Option σ)) (c : σ → ℝ) :
    eval c (S.comap some).degPoly = eval (fun o : Option σ => o.elim 0 c) S.degPoly := by
  simp only [PB.AnSys.degPoly, PB.formPoly, map_sum, map_mul, map_prod, eval_C, eval_X]
  refine Fintype.sum_of_injective (fun w j => some (w j)) ?_ _ _ ?_ ?_
  · intro w w' hw
    funext j
    exact Option.some_injective _ (congrFun hw j)
  · intro b hb
    have : ∃ j, b j = none := by
      by_contra hne
      exact hb ⟨fun j => (b j).get (Option.ne_none_iff_isSome.mp fun h => hne ⟨j, h⟩), funext fun j => by simp⟩
    obtain ⟨j, hj⟩ := this
    rw [Finset.prod_eq_zero (Finset.mem_univ j) (by simp [hj]), mul_zero]
  · intro w
    rfl

theorem exists_flagDeg_eq (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ) :
    ∃ c : ℝ, 0 < c ∧ ∀ lam : Wt Ψ N, flagDeg lam = c * eval (fun x : Ψ × Fin N => lam x.1 x.2) (antisymDelta Ψ N) := by
  refine ⟨((dimFl Ψ N).factorial : ℝ) * ∏ τ : Ψ, ∏ i : Fin N, ∏ k : Fin N,
      (if i < k then (((k : ℕ) : ℝ) - ((i : ℕ) : ℝ))⁻¹ else 1), ?_, ?_⟩
  · refine mul_pos (by exact_mod_cast Nat.factorial_pos _)
      (Finset.prod_pos fun τ _ => Finset.prod_pos fun i _ => Finset.prod_pos fun k _ => ?_)
    split_ifs with h
    · have : ((i : ℕ) : ℝ) < ((k : ℕ) : ℝ) := by exact_mod_cast h
      exact inv_pos.2 (by linarith)
    · exact one_pos
  · intro lam
    rw [(flagDeg_eq_weyl Ψ N lam).1, mul_assoc]
    congr 1
    simp only [antisymDelta, map_prod, map_sub, eval_X]
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun τ _ => ?_
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun i _ => ?_
    have hsplit : ∀ k : Fin N, (if i < k then (lam τ i - lam τ k) / (((k : ℕ) : ℝ) - ((i : ℕ) : ℝ)) else 1)
        = (if i < k then (((k : ℕ) : ℝ) - ((i : ℕ) : ℝ))⁻¹ else 1) * (if i < k then lam τ i - lam τ k else 1) := by
      intro k
      split_ifs <;> ring
    rw [Finset.prod_congr rfl fun k _ => hsplit k, Finset.prod_mul_distrib]
    congr 1
    simp [Finset.prod_ite, Finset.filter_lt_eq_Ioi]

theorem rhoWt_regDominant (Ψ : Type) [Fintype Ψ] (N : ℕ) : RegDominant (rhoWt : Wt Ψ N) := by
  intro τ a b hab
  have h : ((a : ℕ) : ℝ) < ((b : ℕ) : ℝ) := by exact_mod_cast hab
  simp only [rhoWt]
  linarith

theorem RealTie_n_pos {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {N : ℕ} {M : RootModel Ψ N}
    {S : PB.AnSys (dimFl Ψ N) (Option (Ψ × Fin N))} {n : ℕ} (R : RealTie M S n) : 0 < n := by
  exact Nat.pos_of_ne_zero fun hn => M.δ_pos.ne' (R.δ_eq.trans (mul_eq_zero.2 (Or.inl hn)))

theorem lin_eq_zero {J : Type} (Φ : MvPolynomial J ℝ →ₗ[ℝ] ℝ) (h : ∀ m, Φ (monomial m 1) = 0) : Φ = 0 := by
  refine (MvPolynomial.basisMonomials J ℝ).ext fun m => ?_
  rw [MvPolynomial.coe_basisMonomials, LinearMap.zero_apply]
  exact h m

theorem degree_mapDomain_some {J : Type} (m : J →₀ ℕ) : (m.mapDomain some).degree = m.degree := by
  classical
  show ∑ i ∈ (m.mapDomain some).support, (m.mapDomain some) i = ∑ i ∈ m.support, m i
  rw [Finsupp.mapDomain_support_of_injective (Option.some_injective _), Finset.sum_image
    (fun x _ y _ hxy => Option.some_injective _ hxy)]
  exact Finset.sum_congr rfl fun x _ => Finsupp.mapDomain_apply (Option.some_injective _) m x

theorem geoFun_monomial {Ψ : Type} [Fintype Ψ] {N : ℕ} (M : RootModel Ψ N) (m : Option (Ψ × Fin N) →₀ ℕ) :
    M.geoFun (monomial m 1) = M.geoMono m := by
  have := (MvPolynomial.basisMonomials (Option (Ψ × Fin N)) ℝ).constr_basis ℝ M.geoMono m
  rw [MvPolynomial.coe_basisMonomials] at this
  exact this

theorem geoFun_monomial_of_ne {Ψ : Type} [Fintype Ψ] {N : ℕ} (M : RootModel Ψ N) (m : Option (Ψ × Fin N) →₀ ℕ)
    (h : m.degree ≠ dimFl Ψ N) : M.geoFun (monomial m 1) = 0 := by
  rw [geoFun_monomial, RootModel.geoMono, if_neg h]

theorem neg_sum_eq_linA {Ψ : Type} [Fintype Ψ] {N : ℕ} (a : Option (Ψ × Fin N) → ℝ) :
    (-∑ x, C (a x) * X x : RPA Ψ N) = linA (fun τ i => a (some (τ, i))) (-a none) := by
  simp only [linA, toA, linRoot, Fintype.sum_option, map_neg, map_sum, map_mul, rename_C, rename_X]
  ring

theorem dimFl_eq_antisymDegree (Ψ : Type) [Fintype Ψ] (N : ℕ) : dimFl Ψ N = antisymDegree Ψ N := by
  rw [dimFl, antisymDegree, Nat.choose_two_right]

theorem toA_linRoot_pow {Ψ : Type} [Fintype Ψ] {N : ℕ} (lam : Wt Ψ N) (d : ℕ) :
    toA (linRoot lam ^ d) = linA lam 0 ^ d := by
  simp only [linA, map_zero, zero_mul, add_zero, toA, map_pow]

theorem exists_geoFun_eq (hProp : PB.Proportional) (hI : PB.Inputs) (II : IntersectionSystem)
    (hII : IsFullIntersectionSystem II) {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {N : ℕ} [Nonempty Ψ]
    {T : RootTower Ψ N} (R : RealTower T) (hU : R.Unif) (c : T.Comp) :
    ∃ κ : ℝ, 0 < κ ∧ ∀ (B : ℕ) (lam : Wt Ψ N),
      (T.M B c).geoFun (toA (linRoot lam ^ dimFl Ψ N)) = κ * flagDeg lam := by
  have hN2 : 2 ≤ N := by have := T.j_pos; have := T.j_lt; omega
  obtain ⟨⟨c0, hc0, hdeg⟩, hall⟩ := hProp hI Ψ N T.j hN2 T.j_lt.le
  obtain ⟨hvol, htoWt⟩ := hall (dimFl Ψ N) ((R.Sys c).comap some) (dimFl_eq_antisymDegree Ψ N) (hU c)
  obtain ⟨cf, hcf, hflag⟩ := exists_flagDeg_eq Ψ N
  have hnR : (0 : ℝ) < (R.n c : ℝ) := by exact_mod_cast RealTie_n_pos (R.tie 0 c)
  refine ⟨PB.volOf ((R.Sys c).comap some) * c0 / ((R.n c : ℝ) * cf),
    div_pos (mul_pos hvol hc0) (mul_pos hnR hcf), fun B lam => ?_⟩
  have key := GlobalTheory.T.real_tower_geometric_agreement hI II hII Ψ N (T.M B c) (R.Sys c) (R.n c) (R.tie B c) lam 0
  rw [zero_div, ← toA_linRoot_pow] at key
  have e1 : eval (PB.gapS (fun x : Ψ × Fin N => lam x.1 x.2) 0) (R.Sys c).degPoly
      = PB.volOf ((R.Sys c).comap some) * c0 * eval (fun x : Ψ × Fin N => lam x.1 x.2) (antisymDelta Ψ N) := by
    show eval (fun o : Option (Ψ × Fin N) => o.elim 0 (PB.gap fun x : Ψ × Fin N => lam x.1 x.2)) (R.Sys c).degPoly = _
    rw [← eval_degPoly_comap_some (R.Sys c) (PB.gap fun x : Ψ × Fin N => lam x.1 x.2),
      ← eval_toWt (fun x : Ψ × Fin N => lam x.1 x.2), htoWt, hdeg]
    simp only [map_mul, eval_C]
    ring
  have key2 := key.trans e1
  rw [hflag lam, div_mul_eq_mul_div, eq_div_iff (mul_pos hnR hcf).ne']
  linear_combination cf * key2

end RealProp

open RealProp in

theorem rootTower_proportional_of_unif : PB.Proportional → PB.Inputs → ∀ II : IntersectionSystem,
    IsFullIntersectionSystem II → ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ) [Nonempty Ψ] (T : RootTower Ψ N)
    (R : RealTower T), R.Unif → T.Proportional := by
  intro hProp hI II hII Ψ _ _ N _ T R hU
  have hrho : 0 < flagDeg (rhoWt : Wt Ψ N) := (flagDeg_eq_weyl Ψ N rhoWt).2.1 (rhoWt_regDominant Ψ N)
  have hvol : ∀ c : T.Comp, ∃ κ : ℝ, 0 < κ ∧ T.vol c = κ ∧ ∀ (B : ℕ) (lam : Wt Ψ N),
      (T.M B c).geoFun (toA (linRoot lam ^ dimFl Ψ N)) = κ * flagDeg lam := by
    intro c
    obtain ⟨κ, hκ, h⟩ := exists_geoFun_eq hProp hI II hII R hU c
    refine ⟨κ, hκ, ?_, h⟩
    rw [RootTower.vol, h, mul_div_assoc, div_self hrho.ne', mul_one]
  obtain ⟨Φd, hΦd⟩ := (GlobalTheory.T.flag_degree_linear_functionals Ψ N).1
  refine ⟨fun c => ?_, fun B c F => ?_, fun B B' c => ?_⟩
  · obtain ⟨κ, hκ, hv, -⟩ := hvol c
    rw [hv]
    exact hκ
  · obtain ⟨κ, -, hv, h⟩ := hvol c
    rw [hv]
    have hL : (T.M B c).geoFun ∘ₗ (rename (R := ℝ) (Option.some : Ψ × Fin N → Option (Ψ × Fin N))).toLinearMap
        - κ • Φd = 0 := by
      apply lin_eq_zero
      intro m
      by_cases hm : m.degree = dimFl Ψ N
      · refine map_monomial_eq_zero (dimFl Ψ N) _ (fun a => ?_) m hm
        have hlin : (-∑ x, C (a x) * X x : MvPolynomial (Ψ × Fin N) ℝ) = linRoot (fun τ i => a (τ, i)) := rfl
        simp only [LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.smul_apply, AlgHom.toLinearMap_apply,
          hΦd, smul_eq_mul]
        rw [hlin]
        have h1 := h B (fun τ i => a (τ, i))
        simp only [toA] at h1
        rw [h1, flagDeg, sub_self]
      · simp only [LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.smul_apply, AlgHom.toLinearMap_apply,
          hΦd, smul_eq_mul, rename_monomial]
        rw [geoFun_monomial_of_ne _ _ (by rwa [degree_mapDomain_some]),
          (GlobalTheory.T.flag_degree_linear_functionals Ψ N).2.2.2 _ _ (isHomogeneous_monomial _ rfl) hm, mul_zero, sub_zero]
    have h2 := LinearMap.congr_fun hL F
    simp only [LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.smul_apply, AlgHom.toLinearMap_apply,
      hΦd, smul_eq_mul, LinearMap.zero_apply] at h2
    simp only [toA]
    exact sub_eq_zero.mp h2
  · have hnR : (0 : ℝ) < (R.n c : ℝ) := by exact_mod_cast RealTie_n_pos (R.tie 0 c)
    have hL : (T.M B c).geoFun - (T.M B' c).geoFun = 0 := by
      apply lin_eq_zero
      intro m
      by_cases hm : m.degree = dimFl Ψ N
      · refine map_monomial_eq_zero (dimFl Ψ N) _ (fun a => ?_) m hm
        rw [LinearMap.sub_apply, sub_eq_zero, neg_sum_eq_linA]
        have k1 := GlobalTheory.T.real_tower_geometric_agreement hI II hII Ψ N (T.M B c) (R.Sys c) (R.n c) (R.tie B c)
          (fun τ i => a (some (τ, i))) (-a none)
        have k2 := GlobalTheory.T.real_tower_geometric_agreement hI II hII Ψ N (T.M B' c) (R.Sys c) (R.n c) (R.tie B' c)
          (fun τ i => a (some (τ, i))) (-a none)
        rw [R.kA_eq B B' c, ← k2] at k1
        exact mul_left_cancel₀ hnR.ne' k1
      · rw [LinearMap.sub_apply, geoFun_monomial_of_ne _ _ hm, geoFun_monomial_of_ne _ _ hm, sub_zero]
    exact sub_eq_zero.mp hL

end GlobalTheory.CompanionTheory.Ar.Top
end
end

