import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MixedFieldContraction.ContractMixedFieldStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.Bundle0001
import GroundTheory.HeightsAndTheta.Heights.Intersections.TableDegreeThreeBase
import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0033
import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0021
import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0022
import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0036
import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0034
import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0032
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle0025
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle0007
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StatementsLiftBlockDatum
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0064
import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0006
import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0028
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle0022
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Bundle0012
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Bundle0003
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Bundle0029
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0003
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0004
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0018
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle0023
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle0028
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0122
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0093
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0079
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0078
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0107

-- bundled from GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Contract
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Targets

open ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4 GroundTheory.Heights₂.Heights.Inter

theorem Contract.pulledBackForms_topDensity_vanish : pointForm_holds.Statement :=
  pointForm_holds.proof (pointFormRank_holds.proof RatioAlgDep.proof) pointFormEuler_holds.proof

theorem Contract.of_found (hIm : ReciprocityTheory.ChartRestriction.G.AI.I4.ImageArithStatement)
    (hV : GroundTheory.Heights₂.Heights.Inter.ProjectivePointVertical.Statement) :
    ReciprocityTheory.ChartRestriction.G.AI.I4.ContractStatement :=
  contract_of hIm Contract.pulledBackForms_topDensity_vanish hV

end GroundTheory.Heights₂.Heights.Targets
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.OrbitLimits.ContractMixed
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4
open GroundTheory.Heights₂.Heights.Inter

namespace ContractMixed

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {K' : Type} [Fintype K'] {ι' : K' → Type} [∀ k, Fintype (ι' k)]

def PrefixPull (κ : K → K') (v : (Σ k, ι k) → (Σ k', ι' k')) (p : ℕ) {n : ℕ} (L' : Fin n → HermLine ι') :
    Prop :=
  ∃ (h : p ≤ n) (L : Fin p → HermLine ι), (∀ j, IsSmoothHerm (L j)) ∧
    ∀ j, IsPullHerm κ v (L j) (L' (Fin.castLE h j))

omit [∀ k, Fintype (ι' k)] in

theorem PrefixPull.mono {κ : K → K'} {v : (Σ k, ι k) → (Σ k', ι' k')} {p q n : ℕ} {L' : Fin n → HermLine ι'}
    (h : PrefixPull κ v p L') (hqp : q ≤ p) : PrefixPull κ v q L' := by
  obtain ⟨hpn, L, hL, hLL⟩ := h
  exact ⟨hqp.trans hpn, fun j => L (Fin.castLE hqp j), fun j => hL _, fun j => hLL (Fin.castLE hqp j)⟩

omit [∀ k, Fintype (ι' k)] in

theorem PrefixPull.init {κ : K → K'} {v : (Σ k, ι k) → (Σ k', ι' k')} {p n : ℕ} {L' : Fin (n + 1) → HermLine ι'}
    (h : PrefixPull κ v p L') (hpn : p ≤ n) : PrefixPull κ v p (Fin.init L') := by
  obtain ⟨_, L, hL, hLL⟩ := h
  exact ⟨hpn, L, hL, fun j => hLL j⟩

theorem arInt_eq_zero (hInt : PFIntZero.Statement) {κ : K → K'} {v : (Σ k, ι k) → (Σ k', ι' k')}
    (hv : IsBlockMap κ v) {P' : Ideal (MRing ι')} {d₀ n : ℕ} (hP' : IsArithVar P' (n + 1))
    (hQ : IsArithVar (imageZ v P') d₀) {L' : Fin n → HermLine ι'} (hpre : PrefixPull κ v d₀ L')
    (A : HermLine ι') (s : MRing ι') : arInt P' s A L' = 0 := by
  obtain ⟨h, L, hL, hLL⟩ := hpre
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le h
  rw [← Fin.append_castAdd_natAdd (f := L')]
  exact hInt K ι K' ι' κ v P' d₀ m L _ _ A s hv hP' hQ hL hLL

theorem geoNum_eq_zero (hVert : PFVert.Statement) {κ : K → K'} {v : (Σ k, ι k) → (Σ k', ι' k')}
    (hv : IsBlockMap κ v) {P' : Ideal (MRing ι')} {d₀ n : ℕ} (hP' : IsArithVar P' (n + 1))
    (hQ : IsArithVar (imageZ v P') d₀) {L' : Fin n → HermLine ι'} (hpre : PrefixPull κ v d₀ L')
    {s : MRing ι'} {a : K' → ℕ} (hs : IsMultiHomog s a) (hsP : s ∉ P') {W : Ideal (MRing ι')}
    (hW : W ∈ divSupp P' s) (hh : ¬ IsHorizontal W) : geoNum n W (fun j => (L' j).a) = 0 := by
  obtain ⟨h, L, -, hLL⟩ := hpre
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le h
  rw [← Fin.append_castAdd_natAdd (f := L')]
  exact hVert K ι K' ι' κ v P' d₀ m L _ _ s a W hv hP' hQ hLL hs hsP hW hh

theorem aux (hC : ContractStatement) (hIm : ImageArithStatement) (hInt : PFIntZero.Statement)
    (hVert : PFVert.Statement) (I : AllFam) (hI : I.IsFamily) {κ : K → K'}
    {v : (Σ k, ι k) → (Σ k', ι' k')} (hv : IsBlockMap κ v) :
    ∀ (n p : ℕ) (P' : Ideal (MRing ι')) (d₀ : ℕ) (L' : Fin n → HermLine ι'),
      IsArithVar P' n → IsArithVar (imageZ v P') d₀ → d₀ < p → PrefixPull κ v p L' →
      (∀ j, IsSmoothHerm (L' j)) → I K' ι' P' n L' = 0 := by
  intro n
  induction n with
  | zero =>
    intro p _ d₀ _ _ _ hdp hpre _
    obtain ⟨h, -⟩ := hpre
    omega
  | succ n ih =>
    intro p P' d₀ L' hP' hQ hdp hpre hL'
    classical
    rcases Nat.lt_or_ge n p with hnp | hpn
    ·
      obtain ⟨h, L, hL, hLL⟩ := hpre
      have hp : p = n + 1 := by omega
      subst hp
      have e : (fun j => L' (Fin.castLE h j)) = L' := funext fun j => congrArg L' (Fin.ext rfl)
      have key := hC I hI K ι K' ι' κ v P' d₀ (n + 1) L (fun j => L' (Fin.castLE h j)) hv hP' hQ hdp hL hLL
      rwa [e] at key
    ·
      have hpre0 : PrefixPull κ v p (Fin.init L') := hpre.init hpn
      have hL0 : ∀ j, IsSmoothHerm (Fin.init L' j) := fun j => hL' _
      have hPp : P'.IsPrime := hP'.2.1.1
      choose i hi using hP'.2.1.2.2

      have key : ∀ B' : HermLine ι', IsSmoothHerm B' → (∀ k, 0 ≤ B'.a k) →
          I K' ι' P' (n + 1) (Fin.snoc (Fin.init L') B') = 0 := by
        intro B' hB' hBa
        let b : K' → ℕ := fun k => (B'.a k).toNat
        let s : MRing ι' := ∏ k, X ⟨k, i k⟩ ^ b k
        have hs : s ∉ P' := by
          intro h
          obtain ⟨k, -, hk⟩ := (Ideal.IsPrime.prod_mem_iff (hp := hPp)).1 h
          exact hi k (hPp.mem_of_pow_mem _ hk)
        have hsm : IsMultiHomog s b := by
          convert isMultiHomog_prod_X_pow (fun k => (⟨k, i k⟩ : Σ k, ι' k)) b using 1
          funext k
          simp [Finset.sum_filter]
        have hBa' : ∀ k, B'.a k = b k := fun k => (Int.toNat_of_nonneg (hBa k)).symm
        have hsec : IsSectionOn P' B' s := ⟨b, hBa', hsm, hs⟩
        rw [(hI K' ι').2.2 P' n (Fin.init L') B' s b hP' hL0 hB' hBa' hsm hs, recR_eq]
        have h1 : arInt P' s B' (Fin.init L') = 0 :=
          arInt_eq_zero hInt hv hP' hQ (hpre0.mono hdp.le) B' s
        have h2 : cycR (I K' ι') P' (Fin.init L') s = 0 := by
          unfold cycR
          refine (finsum_mem_congr rfl fun W hW => ?_).trans (finsum_mem_zero _)
          split_ifs with hH
          · have hWn : IsArithVar W n := (divSuppArith K' ι' P' n B' s W hP' hsec hW).1 hH
            obtain ⟨dW, -, hQW⟩ := hIm K ι K' ι' κ v W n hQ.1 hv hWn
            have hPW : P' ≤ W := le_sup_left.trans hW.1.1.2
            have hle : imageZ v P' ≤ imageZ v W := Ideal.comap_mono hPW
            have hdim := ringKrullDim_le_of_surjective (Ideal.Quotient.factor hle)
              (Ideal.Quotient.factor_surjective hle)
            rw [hQW.2.2.2, hQ.2.2.2] at hdim
            have hlt : dW + Fintype.card K ≤ d₀ + Fintype.card K := by exact_mod_cast hdim
            rw [ih p W dW (Fin.init L') hWn hQW (by omega) hpre0 hL0, mul_zero]
          · rw [geoNum_eq_zero hVert hv hP' hQ (hpre0.mono hdp.le) hsm hs hW hH]
            simp
        rw [h1, h2, sub_zero]

      let A' := L' (Fin.last n)
      let M : HermLine ι' := HermLine.sqMetric fun k => (-(A'.a k)).toNat
      have hM : IsSmoothHerm M := isSmoothHerm_sqMetric _
      have hA' : IsSmoothHerm A' := hL' _
      have hadd := (hI K' ι').2.1 P' n (Fin.init L') A' M hP' hL0 hA' hM
      have h3 := key (A'.tensor M) (isSmoothHerm_tensor hA' hM) fun k => by
        show 0 ≤ A'.a k + ((-(A'.a k)).toNat : ℤ)
        omega
      have h4 := key M hM fun k => by
        show (0 : ℤ) ≤ ((-(A'.a k)).toNat : ℤ)
        omega
      have e : L' = Fin.snoc (Fin.init L') A' := (Fin.snoc_init_self L').symm
      rw [e]
      linarith

theorem of_contract (hC : ContractStatement) (hIm : ImageArithStatement) (hInt : PFIntZero.Statement)
    (hVert : PFVert.Statement) : ReciprocityTheory.ChartRestriction.G.AI.I4.ContractMixedStatement := by
  intro I hI K _ ι _ K' _ ι' _ κ v P' d₀ d r L L' N hv hP' hQ hdd hL hLL hN
  refine aux hC hIm hInt hVert I hI hv (d + r) d P' d₀ (Fin.append L' N) hP' hQ hdd ?_ ?_
  · refine ⟨Nat.le_add_right d r, L, hL, fun j => ?_⟩
    have e : Fin.castLE (Nat.le_add_right d r) j = Fin.castAdd r j := rfl
    rw [e, Fin.append_left]
    exact hLL j
  · intro j
    refine Fin.addCases (fun i => ?_) (fun i => ?_) j
    · rw [Fin.append_left]
      exact IsPullHerm.isSmoothHerm hv (hLL i) (hL i)
    · rw [Fin.append_right]
      exact hN i

theorem of_found (hIm : ImageArithStatement) (hF : pointForm_holds.Statement) (hV : ProjectivePointVertical.Statement)
    (hInt : PFIntZero.Statement) (hVert : PFVert.Statement) : ReciprocityTheory.ChartRestriction.G.AI.I4.ContractMixedStatement :=
  of_contract (contract_of hIm hF hV) hIm hInt hVert

end ContractMixed

end GroundTheory.Heights₂.Heights.Targets
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.OrbitLimits.ImageArithClosed
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

theorem imageArith : ReciprocityTheory.ChartRestriction.G.AI.I4.ImageArithStatement :=
  ImageArith.of_found BlockTrdeg.proof

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.OrbitLimits.LiftBlockGraph
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.ChartRestriction.G.AI.I4
open GroundTheory.Heights₂.Heights.HilbertSamuel

noncomputable section

namespace LiftBlockGraph

variable {K : Type} {ι : K → Type} {Ω : Type} [Field Ω]

theorem generatesOn_liftCoords [Fintype K] {ι' : Type} [Fintype ι'] (y : (Σ k, ι k) → Ω) (n : K → ℤ) (x' : ι' → Ω)
    (h : KH.GeneratesOn y n x') : KH.GeneratesOn y n (liftCoords x') := by
  intro c hc
  obtain ⟨u, hu, hs⟩ := h c hc
  refine ⟨fun j => u ((Fintype.equivFin ι').symm j), fun j => hu _, ?_⟩
  rw [← hs]
  exact Fintype.sum_equiv (Fintype.equivFin ι').symm _ _ (fun j => rfl)

theorem exists_ne_zero_of_generatesOn [Fintype K] {r : ℕ} (y : (Σ k, ι k) → Ω) (n : K → ℤ) (v : Fin r → Ω)
    (c : ∀ k, ι k) (hc : ∀ k, y ⟨k, c k⟩ ≠ 0) (h : KH.GeneratesOn y n v) : ∃ j, v j ≠ 0 := by
  obtain ⟨u, -, hs⟩ := h c hc
  by_contra h0
  simp only [not_exists, not_not] at h0
  simp [h0] at hs

variable [CharZero Ω] [Fintype K] [∀ k, Fintype (ι k)]

omit [Fintype K] [∀ k, Fintype (ι k)] in

theorem chartRingZ_le_blockFnField (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k) {x : Ω} (hx : x ∈ chartRingZ y c) :
    x ∈ blockFnField y := by
  induction hx using Algebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨p, rfl⟩ := hx
    exact IntermediateField.subset_adjoin _ _ ⟨p, ⟨p.1, c p.1⟩, rfl, rfl⟩
  | algebraMap m =>
    rw [eq_intCast]
    exact intCast_mem _ m
  | add a b _ _ ha hb => exact add_mem ha hb
  | mul a b _ _ ha hb => exact mul_mem ha hb

theorem blockFnField_addBlock (y : (Σ k, ι k) → Ω) (n : K → ℤ) {r : ℕ} (v : Fin r → Ω)
    (c : ∀ k, ι k) (hc : ∀ k, y ⟨k, c k⟩ ≠ 0) (hv : ∀ j, v j ∈ chartLat y n 1) :
    blockFnField (addBlock y v) = blockFnField y := by
  apply le_antisymm
  · refine IntermediateField.adjoin_le_iff.mpr ?_
    rintro t ⟨⟨pk, pi⟩, ⟨qk, qi⟩, hpq, rfl⟩
    simp only at hpq
    subst hpq
    cases pk with
    | none =>
      set P : Ω := ∏ k, y ⟨k, c k⟩ ^ (-(((1 : ℕ) : ℤ) * n k)) with hP
      have hP0 : P ≠ 0 := Finset.prod_ne_zero_iff.mpr fun k _ => zpow_ne_zero _ (hc k)
      have h1 := chartRingZ_le_blockFnField y c (hv pi c hc)
      have h2 := chartRingZ_le_blockFnField y c (hv qi c hc)
      have : v pi / v qi = (v pi * P) / (v qi * P) := (mul_div_mul_right _ _ hP0).symm
      change v pi / v qi ∈ blockFnField y
      rw [this]
      exact div_mem h1 h2
    | some k =>
      exact IntermediateField.subset_adjoin _ _ ⟨⟨k, pi⟩, ⟨k, qi⟩, rfl, rfl⟩
  · refine IntermediateField.adjoin_le_iff.mpr ?_
    rintro t ⟨p, q, hpq, rfl⟩
    exact IntermediateField.subset_adjoin _ _
      ⟨⟨some p.1, p.2⟩, ⟨some q.1, q.2⟩, by simp [hpq], rfl⟩

theorem isArithVar_addBlock {D : ℕ} (y : (Σ k, ι k) → Ω) (n : K → ℤ) {r : ℕ} (v : Fin r → Ω)
    (hA : IsArithVar (mCoordIdeal y) (D + 1)) (hv : ∀ j, v j ∈ chartLat y n 1) (hg : KH.GeneratesOn y n v) :
    IsArithVar (mCoordIdeal (addBlock y v)) (D + 1) := by
  obtain ⟨c, hc⟩ := CoordArithOfFnField.nonzero_of_relevant y hA.2.1.2.2
  refine CoordArithOfFnField.proof K ι (Option K) (addIdx ι r) Ω y (addBlock y v) (D + 1) ⟨none⟩ ?_
    (blockFnField_addBlock y n v c hc hv).symm hA
  rintro (_ | k)
  · obtain ⟨j, hj⟩ := exists_ne_zero_of_generatesOn y n v c hc hg
    exact ⟨j, hj⟩
  · exact ⟨c k, hc k⟩

omit [CharZero Ω] in

theorem isMultiHomog_rename_none [DecidableEq K] {ι' : Type} [Fintype ι'] {g : MRing (fun _ : Unit => ι')} {e : Unit → ℕ}
    (hg : IsMultiHomog g e) :
    IsMultiHomog (rename (fun p : Σ _ : Unit, ι' =>
      (⟨none, Fintype.equivFin ι' p.2⟩ : Σ k, addIdx ι (Fintype.card ι') k)) g)
      (blockDeg (none : Option K) (e ())) := by
  classical
  set φ : (Σ _ : Unit, ι') → (Σ k, addIdx ι (Fintype.card ι') k) :=
    fun p => ⟨none, Fintype.equivFin ι' p.2⟩ with hφ
  have hinj : Function.Injective φ := by
    rintro ⟨⟨⟩, a⟩ ⟨⟨⟩, b⟩ h
    obtain ⟨-, h2⟩ := Sigma.mk.inj h
    exact congrArg (Sigma.mk ()) ((Fintype.equivFin ι').injective (eq_of_heq h2))
  intro m hm k
  rw [support_rename_of_injective hinj] at hm
  obtain ⟨m0, hm0, rfl⟩ := Finset.mem_image.mp hm
  cases k with
  | none =>
    have hterm : ∀ i : Fin (Fintype.card ι'),
        (Finsupp.mapDomain φ m0) ⟨none, i⟩ = m0 ⟨(), (Fintype.equivFin ι').symm i⟩ := by
      intro i
      have : (⟨none, i⟩ : Σ k, addIdx ι (Fintype.card ι') k) = φ ⟨(), (Fintype.equivFin ι').symm i⟩ := by
        simp [hφ]
      rw [this, Finsupp.mapDomain_apply hinj]
    change ∑ i : Fin (Fintype.card ι'), (Finsupp.mapDomain φ m0) ⟨none, i⟩ = _
    simp only [hterm]
    rw [Fintype.sum_equiv (Fintype.equivFin ι').symm (fun i => m0 ⟨(), (Fintype.equivFin ι').symm i⟩)
      (fun j => m0 ⟨(), j⟩) (fun _ => rfl)]
    have := hg m0 hm0 ()
    simp only [blockDeg, if_true]
    rw [← this]
  | some k =>
    have hterm : ∀ i, (Finsupp.mapDomain φ m0) ⟨some k, i⟩ = 0 := by
      intro i
      apply Finsupp.mapDomain_of_notMem_range
      rintro ⟨p, hp⟩
      simp only [hφ] at hp
      exact absurd (congrArg Sigma.fst hp) (by simp)
    simp [hterm, blockDeg]

omit [CharZero Ω] in

theorem blockBirational_addBlock [DecidableEq K] {ι' : Type} [Fintype ι'] (y : (Σ k, ι k) → Ω) (x' : ι' → Ω)
    (hb : Birational (fun p : Σ _ : Unit, ι' => x' p.2)) :
    BlockBirational (addBlock y (liftCoords x')) (none : Option K) := by
  intro d g h hg hh hne
  obtain ⟨e, g', h', hg', hh', hne', hs⟩ :=
    hb (aeval (addBlock y (liftCoords x')) g / aeval (addBlock y (liftCoords x')) h)
  set φ : (Σ _ : Unit, ι') → (Σ k, addIdx ι (Fintype.card ι') k) :=
    fun p => ⟨none, Fintype.equivFin ι' p.2⟩ with hφ
  have hev : ∀ f : MRing (fun _ : Unit => ι'), aeval (addBlock y (liftCoords x')) (rename φ f) =
      aeval (fun p : Σ _ : Unit, ι' => x' p.2) f := by
    intro f
    have hc : addBlock y (liftCoords x') ∘ φ = fun p => x' p.2 := by
      funext p
      simp [hφ, addBlock, liftCoords]
    rw [aeval_rename, hc]
  refine ⟨e (), rename φ g', rename φ h', isMultiHomog_rename_none hg', isMultiHomog_rename_none hh', ?_, ?_⟩
  · rw [hev]
    exact hne'
  · rw [hev, hev, hs]
    field_simp

omit [CharZero Ω] in

theorem isMultiHomogIdeal_top : IsMultiHomogIdeal (⊤ : Ideal (MRing ι)) :=
  ⟨{1}, fun f hf => ⟨0, by rw [Set.mem_singleton_iff.mp hf]; exact Inter.AvoidRing.isMultiHomog_one⟩,
    Ideal.span_singleton_one.symm⟩

end LiftBlockGraph

end

end GroundTheory.Heights₂.Heights.Targets
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.OrbitLimits.OfGenDeg
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Targets

open ReciprocityTheory.ChartRestriction.G.AI.I4 GroundTheory.Heights₂.Heights.Inter

theorem PFSum.of_genDeg (h : PushforwardArithIntersection.Statement) : ReciprocityTheory.ChartRestriction.G.AI.I4.PFSumStatement := by
  unfold PushforwardArithIntersection.Statement GenDegStatement at h
  intro I hI K _ ι _ K₂ _ ι₂ _ P₂ d G J L L' hP₂ hP hJ hL hLL'
  exact h I hI K ι (K ⊕ K₂) (Sum.elim ι ι₂) Sum.inl inlV P₂ d G J L L' isBlockMap_inl hP₂ hP hJ hL hLL'

theorem PFSum.of_found (hRat : RatR.Statement) (hCyc : ArithmeticIntersectionCycle.Statement) (hInt : ArithmeticIntersectionIntegral.Statement) :
    ReciprocityTheory.ChartRestriction.G.AI.I4.PFSumStatement :=
  PFSum.of_genDeg (PushforwardArithIntersection.proof arithVarZero hRat hCyc hInt)

end GroundTheory.Heights₂.Heights.Targets
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PChartSectionLength
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Geo (MRing multAt divSuppArith)
open GroundTheory.Heights₂.Heights (localMult localMult_map_of_flat map_eq_maximalIdeal_of_isRadical)

attribute [local instance] MvPolynomial.algebraMvPolynomial

theorem localMult_map_intCast_complex {τ : Type} [Fintype τ] (J W : Ideal (MvPolynomial τ ℤ)) [W.IsPrime]
    (W'' : Ideal (MvPolynomial τ ℂ)) (hW'' : W'' ∈ (W.map (MvPolynomial.map (Int.castRingHom ℂ))).minimalPrimes) :
    localMult (J.map (MvPolynomial.map (Int.castRingHom ℂ))) W'' = localMult J W := by
  have := HilbertSamuel.mvPolynomial_int_complex_flat τ
  have hAlg := HilbertSamuel.algebraMap_mvPolynomial_int_complex τ
  have : W''.IsPrime := hW''.1.1
  have hc : W''.comap (MvPolynomial.map (Int.castRingHom ℂ)) = W :=
    HilbertSamuel.ComplexMinimalPrimesContract.proof τ W ‹_› W'' hW''
  have : W''.LiesOver W := ⟨by rw [Ideal.under, hAlg, hc]⟩
  have hrad := HilbertSamuel.PrimeComplexRadical.proof τ W ‹_›
  have key := localMult_map_of_flat J W W''
    (by rw [hAlg]; exact map_eq_maximalIdeal_of_isRadical hrad hW'')
  rwa [hAlg] at key

theorem multAt_eq_localMult {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] (J W : Ideal (MRing ι))
    [W.IsPrime] : multAt J W = localMult J W := by
  unfold multAt localMult
  rw [dif_pos ‹_›, dif_pos ‹_›, ObjectsChow.VerticalPartMultiplicity.length_localizedModule_quotient]

theorem ChartSectionLength.proof (hComp : ChartConeComponent.Statement) (hLen : ChartConeLength.Statement) :
    ChartSectionLength.Statement := by
  intro K _ _ ι _ P n m σ i A s hP hs W hW hWh W' hW'
  have hWa := (divSuppArith K ι P (n + 1) A s W hP hs hW).1 hWh
  have : W.IsPrime := hW.1.1.1
  obtain ⟨W'', hW'', hle⟩ := hComp K ι W m σ i hWa.2.1 W' hW'
  rw [hLen K ι P n m σ i A s hP hs W hW hWh W' hW' W'' hW'' hle, multAt_eq_localMult,
    localMult_map_intCast_complex _ W W'' hW'']

end GroundTheory.Heights₂.Heights.Targets
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PSegreChartAbsIntegrable
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights

open MeasureTheory MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Geo (MRing HermLine IsSmoothHerm)
open ComplexSets Matrix

theorem SegreChartAbsIntegrable.proof (h₁ : SliceMassFinite.Statement)
    (h₂ : SegreChartSheetCompare.Statement) : SegreChartAbsIntegrable.Statement := by
  intro K _ _ ι _ P e m σ i L g _ hL hg J hJ A hA
  obtain ⟨M, hM⟩ := PtsPosDens.exists_bound hg
  obtain ⟨C, hC⟩ := h₂ K ι P e m σ i L hL
  have hJmin := mem_segreChartComponents.1 hJ
  have hℓ : linForm (Pi.single (σ.symm i) (1 : ℂ)) - 1 ∈ J := by
    rw [linForm_single]
    refine hJmin.1.2 ?_
    rw [segreChartIdeal, MvPolynomial.mem_vanishingIdeal_iff]
    rintro _ ⟨z, -, hzi, rfl⟩
    simp [hzi]
  have hInt := h₁ m e (HermNorm.std m) J (Pi.single (σ.symm i) 1) A hJmin.1.1 hℓ
    (VarIntAdd.ringKrullDim_of_isFiniteProjection hA) hA
  set c : ℝ := max M 0 * max C 0 with hc
  have hmeas : Measurable (chartAbsDens J A (chartWeight σ i g) (chartPot σ i L)) :=
    SheetSumMeasurable.measurable_sheetSum hA (fun a b => |a * b|)
      ((continuous_mul.comp continuous_id).abs.measurable) (measurable_chartWeight σ i hg) _
  refine (hInt.const_mul c).mono' hmeas.aestronglyMeasurable (Filter.Eventually.of_forall fun y => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (chartAbsDens_nonneg _ _ _ _ _)]
  refine sheetSum_le_mul (IndefiniteRowSideFullHecke.ComplexSets.fibre_finite hA y) c _ _ fun x hx s hs => ?_
  obtain ⟨hxJ, rfl⟩ := hx
  have hx1 : x (σ.symm i) = 1 := chart_coord_eq_one hJ hxJ
  have hG : |chartWeight σ i g x| ≤ max M 0 := by
    rw [chartWeight_of_coord g hx1]
    exact (hM _ (chartLift_blockNonzero σ i hx1)).trans (le_max_left _ _)
  have hD := hC J hJ A x s hxJ hs
  rw [abs_mul, one_mul, hc, mul_assoc]
  exact mul_le_mul hG (hD.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (abs_nonneg _)))
    (abs_nonneg _) (le_max_right _ _)

end GroundTheory.Heights₂.Heights
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StGoodChartDim
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo (MRing IsArithVar PBlk)

def GoodChartDim.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (e m : ℕ)
    (σ : Fin m ≃ ((k : K) → ι k)) (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)),
    IsArithVar P (e + 1) →
      ∀ J ∈ (projChartIdeal P σ Ψ).minimalPrimes,
        ringKrullDim (MvPolynomial (Fin m) ℂ ⧸ J) = (e : ℕ)

end GroundTheory.Heights₂.Heights
end
end

