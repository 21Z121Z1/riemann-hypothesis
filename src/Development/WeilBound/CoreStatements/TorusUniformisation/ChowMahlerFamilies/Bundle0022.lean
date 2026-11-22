import Mathlib
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle0005
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle0001
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.PluckerCoord
import Development.AutomorphicSpectrum.Statements.AlgebraStatements.Bundle0002
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsBundles
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.SameGenericSymm
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PTwinFullFlagRestrictLoc
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0009
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0016
import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.Bundle0009
import ReciprocityTheory.DualLattices.Bundle0005
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle0003
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle0004
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0005
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.TeichmullerCharacterOrderGenerates
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0020
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0017
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0032
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0044

-- bundled from Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.XTrivflagmodAt
section
open MvPolynomial GlobalTheory.CompanionTheory.Ar.Num GroundTheory.Heights₂.Heights.NumbersDVR
open ReciprocityTheory.ChartRestriction.G.Geo (ChartBundle chartRing)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg mcIdeal chartMon joinCoord bcCoord pullDeg liftVar fnField ck rootNum SameGeneric LatLE IsPull IsPullBC IsSubQuot QuotIso IsFrobPres FlagModel modelDeg)

namespace PositivityTheory.Xgn.A_trivflagmod_at

section Lin

variable {F : Type*} [Field F] {N : ℕ}

theorem exists_basis_cols (G : Matrix (Fin N) (Fin N) F) (hG : G.det ≠ 0) :
    ∃ u : Module.Basis (Fin N) F (Fin N → F), ∀ i j, u i j = G j i := by
  classical
  have hU : IsUnit G.det := hG.isUnit
  refine ⟨(Pi.basisFun F (Fin N)).map (G.toLinearEquiv' (G.invertibleOfIsUnitDet hU)), fun i j => ?_⟩
  have : (G.toLinearEquiv' (G.invertibleOfIsUnitDet hU)) (Pi.single i 1) = G.mulVec (Pi.single i 1) := rfl
  rw [Module.Basis.map_apply, Pi.basisFun_apply, this]
  simp

theorem repr_eq (G : Matrix (Fin N) (Fin N) F) (u : Module.Basis (Fin N) F (Fin N → F))
    (hu : ∀ i j, u i j = G j i) (a v : Fin N → F) (h : G.mulVec a = v) (i : Fin N) :
    u.repr v i = a i := by
  have e : v = ∑ q, a q • u q := by
    rw [← h]
    funext j
    simp [Finset.sum_apply, hu, Matrix.mulVec, dotProduct, mul_comm]
  rw [e, u.repr_sum_self]

theorem mulVec_repr (G : Matrix (Fin N) (Fin N) F) (u : Module.Basis (Fin N) F (Fin N → F))
    (hu : ∀ i j, u i j = G j i) (v : Fin N → F) (j : Fin N) :
    v j = ∑ q, G j q * u.repr v q := by
  conv_lhs => rw [← u.sum_repr v]
  simp [Finset.sum_apply, hu, mul_comm]

theorem lat_iff {k : Type*} [CommRing k] [Algebra k F] (R : Subalgebra k F)
    (G : Matrix (Fin N) (Fin N) F) (hG : ∀ i j, G i j ∈ R) {h : F} (hh : h ∈ R)
    (hdet : G.det * h = 1) (u : Module.Basis (Fin N) F (Fin N → F))
    (hu : ∀ i j, u i j = G j i) (v : Fin N → F) :
    (∀ q, v q ∈ R) ↔ ∀ i, u.repr v i ∈ R := by
  classical
  constructor
  · intro hv i
    let G' : Matrix (Fin N) (Fin N) R := fun i j => ⟨G i j, hG i j⟩
    have hGG : G = R.val.toRingHom.mapMatrix G' := by
      ext i j
      rfl
    have hadj : ∀ i j, G.adjugate i j ∈ R := by
      intro i j
      rw [hGG, ← RingHom.map_adjugate]
      exact (G'.adjugate i j).2
    have e : G.mulVec (h • G.adjugate.mulVec v) = v := by
      rw [Matrix.mulVec_smul, Matrix.mulVec_mulVec, Matrix.mul_adjugate, Matrix.smul_mulVec,
        Matrix.one_mulVec, smul_smul, mul_comm, hdet, one_smul]
    rw [repr_eq G u hu _ v e i]
    change h * ∑ q, G.adjugate i q * v q ∈ R
    exact mul_mem hh (sum_mem fun q _ => mul_mem (hadj i q) (hv q))
  · intro hv j
    rw [mulVec_repr G u hu v j]
    exact sum_mem fun q _ => mul_mem (hG j q) (hv q)

theorem flag_coords (G G₀ U : Matrix (Fin N) (Fin N) F) (c : F) (hc : c ≠ 0) (d : Fin N → F)
    (hd : ∀ i, d i ≠ 0) (hGU : ∀ i j, c * G i j = ∑ q, G₀ i q * U q j)
    (u w : Module.Basis (Fin N) F (Fin N → F)) (hu : ∀ i j, u i j = G j i)
    (hw : ∀ i j, w i j = (G₀ * Matrix.diagonal fun i => (d i)⁻¹) j i) (i j : Fin N) :
    w.repr (u i) j = c⁻¹ * U j i * d j := by
  refine repr_eq _ w hw (fun j => c⁻¹ * U j i * d j) _ ?_ j
  funext l
  rw [hu]
  apply mul_left_cancel₀ hc
  rw [hGU]
  simp only [Matrix.mulVec, dotProduct, Matrix.mul_diagonal, Finset.mul_sum]
  refine Finset.sum_congr rfl fun q _ => ?_
  have := hd q
  field_simp

end Lin

section Res

open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (kap redIdeal genPt)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles.FlagRestrict

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
variable {Ω : Type} [Field Ω] [Algebra O Ω]
variable {x : (Σ k, ι k) → Ω} {Q : Ideal (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver (kap O) ι)} [Q.IsPrime]

theorem rs_det (hPQ : redIdeal O (mcIdeal O x) ≤ Q) {N : ℕ} (g : Matrix (Fin N) (Fin N) Ω)
    (hg : ∀ i j, g i j ∈ locAlg x Q) :
    g.det ∈ locAlg x Q ∧ rs x Q g.det = (g.map (rs x Q)).det := by
  let ρ : locAlg x Q →+* FractionRing (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver (kap O) ι ⧸ Q) :=
    { toFun := fun a => rs x Q a
      map_one' := rs_one hPQ
      map_mul' := fun a b => rs_mul hPQ a.2 b.2
      map_zero' := rs_zero hPQ
      map_add' := fun a b => rs_add hPQ a.2 b.2 }
  let g' : Matrix (Fin N) (Fin N) (locAlg x Q) := fun i j => ⟨g i j, hg i j⟩
  have h1 : g.det = ((g'.det : locAlg x Q) : Ω) := by
    have := (locAlg x Q).val.toRingHom.map_det g'
    exact this.symm
  refine ⟨h1 ▸ g'.det.2, ?_⟩
  rw [h1]
  exact ρ.map_det g'

theorem rs_unif (hPQ : redIdeal O (mcIdeal O x) ≤ Q) {ϖ : O} (hϖ : Irreducible ϖ) {r : Ω}
    (hr : r ∈ locAlg x Q) : rs x Q (algebraMap O Ω ϖ * r) = 0 := by
  rw [rs_mul hPQ (Subalgebra.algebraMap_mem _ _) hr, rs_algebraMap hPQ,
    (IsLocalRing.residue_eq_zero_iff ϖ).2 hϖ.not_isUnit, map_zero, zero_mul]

theorem mseg_ne (hPQ : redIdeal O (mcIdeal O x) ≤ Q) {s : ∀ k, ι k}
    (hs : mseg (genPt (kap O) Q) s ≠ 0) : mseg x s ≠ 0 := by
  rw [← aeval_segForm (R := O)]
  exact aeval_ne_zero hPQ (isMultiHomog_segForm s) (red_segForm_notMem hs)

theorem mon_ne {F : Type*} [Field F] (y : (Σ k, ι k) → F) {s : ∀ k, ι k} (hs : mseg y s ≠ 0)
    (a : K → ℤ) : chartMon y s a ≠ 0 :=
  Finset.prod_ne_zero_iff.2 fun k hk => zpow_ne_zero _ (Finset.prod_ne_zero_iff.1 hs k hk)

theorem exists_frame [DecidableEq K] (hPQ : redIdeal O (mcIdeal O x) ≤ Q) {ϖ : O}
    (hϖ : Irreducible ϖ) {N : ℕ} {b : Fin N → K → ℤ} (H : TrivFlagMod O ϖ x N b)
    {s₀ : ∀ k, ι k} (hs₀ : mseg (genPt (kap O) Q) s₀ ≠ 0) :
    ∃ w : Module.Basis (Fin N) _ (Fin N → _),
      IsFlagFrame (genPt (kap O) Q)
        (scaledTrivBundle (kap O) (segreVec (genPt (kap O) Q)) N one_ne_zero) w b := by
  obtain ⟨g, hg, hov⟩ := H
  have hG : ∀ s, mseg (genPt (kap O) Q) s ≠ 0 →
      (∀ i j, (g s).map (rs x Q) i j ∈ chartRing (kap O) (mseg (genPt (kap O) Q)) s) ∧
      ∃ h ∈ chartRing (kap O) (mseg (genPt (kap O) Q)) s, ((g s).map (rs x Q)).det * h = 1 := by
    intro s hs
    obtain ⟨h1, h, hh, r, hr, hdet⟩ := hg s (mseg_ne hPQ hs)
    refine ⟨fun i j => (chartRing_sub hPQ hs (h1 i j)).2, rs x Q h, (chartRing_sub hPQ hs hh).2, ?_⟩
    obtain ⟨h2, h3⟩ := rs_det hPQ (g s) fun i j => (chartRing_sub hPQ hs (h1 i j)).1
    have hr' := (chartRing_sub hPQ hs hr).1
    rw [← h3, ← rs_mul hPQ h2 (chartRing_sub hPQ hs hh).1, hdet,
      rs_add hPQ (one_mem _) (mul_mem (Subalgebra.algebraMap_mem _ _) hr'), rs_one hPQ,
      rs_unif hPQ hϖ hr', add_zero]
  have hdet : ∀ s, mseg (genPt (kap O) Q) s ≠ 0 → ((g s).map (rs x Q)).det ≠ 0 := by
    intro s hs
    obtain ⟨-, h, -, hh⟩ := hG s hs
    exact left_ne_zero_of_mul_eq_one hh
  obtain ⟨w, hw⟩ := exists_basis_cols ((g s₀).map (rs x Q) *
      Matrix.diagonal fun i => (chartMon (genPt (kap O) Q) s₀ (b i))⁻¹) (by
    rw [Matrix.det_mul, Matrix.det_diagonal]
    exact mul_ne_zero (hdet s₀ hs₀)
      (Finset.prod_ne_zero_iff.2 fun i _ => inv_ne_zero (mon_ne _ hs₀ _)))
  refine ⟨w, (PositivityTheory.Xgn.t_flagframe_basis (kap O) _ K ι (genPt (kap O) Q) N _
    (scaledTrivBundle (kap O) (segreVec (genPt (kap O) Q)) N one_ne_zero) w b).2 fun s hs => ?_⟩
  obtain ⟨u, hu⟩ := exists_basis_cols _ (hdet s hs)
  obtain ⟨m, U, Z, hU, hZ, hUt, hUd, -, hE⟩ := hov s s₀ (mseg_ne hPQ hs) (mseg_ne hPQ hs₀)
  obtain ⟨hc1, hc2⟩ := seg_ratio (x := x) hPQ hs₀ s
  have hc0 : (mseg (genPt (kap O) Q) s / mseg (genPt (kap O) Q) s₀) ^ m ≠ 0 :=
    pow_ne_zero _ (div_ne_zero hs hs₀)
  have hgs : ∀ i j, g s i j ∈ locAlg x Q := fun i j =>
    (chartRing_sub hPQ hs ((hg s (mseg_ne hPQ hs)).1 i j)).1
  have hg0 : ∀ i j, g s₀ i j ∈ locAlg x Q := fun i j =>
    (chartRing_sub hPQ hs₀ ((hg s₀ (mseg_ne hPQ hs₀)).1 i j)).1
  have hU' : ∀ i j, U i j ∈ locAlg x Q := fun i j => (chartRing_sub hPQ hs₀ (hU i j)).1
  have hZ' : ∀ i j, Z i j ∈ locAlg x Q := fun i j => (chartRing_sub hPQ hs₀ (hZ i j)).1
  have key := flag_coords ((g s).map (rs x Q)) ((g s₀).map (rs x Q)) (U.map (rs x Q)) _ hc0
    (fun i => chartMon (genPt (kap O) Q) s₀ (b i)) (fun i => mon_ne _ hs₀ _) (by
      intro i j
      have e : (mseg x s / mseg x s₀) ^ m * g s i j =
          ∑ q, g s₀ i q * U q j + algebraMap O Ω ϖ * Z i j := congrFun (congrFun hE i) j
      have e' := congrArg (rs x Q) e
      rw [rs_mul hPQ (pow_mem hc1 m) (hgs i j), rs_pow hPQ hc1, hc2,
        rs_add hPQ (sum_mem fun q _ => mul_mem (hg0 i q) (hU' q j))
          (mul_mem (Subalgebra.algebraMap_mem _ _) (hZ' i j)), rs_unif hPQ hϖ (hZ' i j), add_zero,
        rs_sum hPQ _ _ fun q _ => mul_mem (hg0 i q) (hU' q j)] at e'
      simp only [Matrix.map_apply]
      rw [e']
      exact Finset.sum_congr rfl fun q _ => rs_mul hPQ (hg0 i q) (hU' q j)) u w hu hw
  refine ⟨u, fun i j hij => ?_, fun i => ?_, fun v => ?_⟩
  · rw [key, Matrix.map_apply, hUt j i hij, rs_zero hPQ, mul_zero, zero_mul]
  · obtain ⟨hm1, hm2⟩ := chartMon_ratio (x := x) hPQ hs hs₀ (b i)
    rw [key, Matrix.map_apply, hUd, rs_mul hPQ (pow_mem hc1 m) hm1, rs_pow hPQ hc1, hc2, hm2,
      ← mul_assoc, inv_mul_cancel₀ hc0, one_mul, div_mul_cancel₀ _ (mon_ne _ hs₀ _)]
  · obtain ⟨h1, h, hh, hd⟩ := hG s hs
    rw [← lat_iff _ _ h1 hh hd u hu v]
    refine (mem_scaledTrivLat (R := kap O)).trans (forall_congr' fun q => ⟨?_, fun hq => ⟨v q, hq, (one_mul _).symm⟩⟩)
    rintro ⟨a, ha, e⟩
    rw [e, one_mul]
    exact ha

end Res

end PositivityTheory.Xgn.A_trivflagmod_at

open PositivityTheory.Xgn.A_trivflagmod_at GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles.FlagRestrict in
theorem PositivityTheory.Xgn.t_trivflagmod_at : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (Ω : Type) [Field Ω] [Algebra O Ω] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (x : (Σ k, ι k) → Ω) (ϖ : O), Irreducible ϖ → ∀ (N : ℕ) (b : Fin N → K → ℤ), TrivFlagMod O ϖ x N b → ∀ (W : Ideal (MRing ι O)), IsMultiProjPrime W → (pointIdeal O x) ≤ W → (C ϖ : MRing ι O) ∈ W → TrivFlagAt W b := by
  intro O _ _ _ Ω _ _ K _ _ ι _ x ϖ hϖ N b H W hW hPW hϖW
  obtain ⟨hpr, -, hrel, -⟩ := SpecialIdealCorresp.proof O ϖ hϖ K ι W W hW.isPrime hϖW
  have hhom := (VocabMultiHomogIdeal.proof VocabMultiHomog.proof _ K ι _).2
    (SpecialIdealMultiHomog.proof O K ι W hW.multiHomog)
  choose s₀ hs₀ using hrel.1 hW.relevant
  have hPQ : GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles.redIdeal O (mcIdeal O x) ≤ specialIdeal W :=
    Ideal.map_mono hPW
  have hs : mseg (GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles.genPt (IsLocalRing.ResidueField O)
      (specialIdeal W)) s₀ ≠ 0 := by
    refine Finset.prod_ne_zero_iff.2 fun k _ h => hs₀ k ?_
    rw [← aeval_genPt_eq_zero_iff (specialIdeal W), aeval_X]
    exact h
  obtain ⟨w, hw⟩ := exists_frame hPQ hϖ H hs
  exact ⟨_, inferInstance, inferInstance, _, w, mcIdeal_genPt (specialIdeal W) hhom, hw⟩
end

-- bundled from Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.XXgrROm
section
open ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Up GlobalTheory.CompanionTheory.Ar.GR
open scoped Matrix

namespace PositivityTheory.Xgn.A_xgr_r_om

section
variable {C : Type} [Field C] {R : Type} [CommRing R] [Algebra R C] {v : Valuation C NNReal}
  {F : Type} [Field F]

theorem mem_x_ideal_iff (M : Submodule R (F → C)) (χ : MulChar F R) (r : R) :
    r ∈ xIdeal M χ ↔ (fun a => algebraMap R C (r * χ a)) ∈ M := by
  rw [xIdeal, Submodule.mem_comap, LinearMap.toSpanSingleton_apply]
  have he : (r • fun a : F => algebraMap R C (χ a)) = fun a => algebraMap R C (r * χ a) := by
    funext a
    simp [Algebra.smul_def, map_mul]
  rw [he]

theorem mem_aug (M : Submodule R (F → C)) (g : F → C) :
    g ∈ augIdeal M ↔ g ∈ M ∧ g 0 = 0 := Iff.rfl

theorem v_le_of_mem (hv : v.Integers R) {a b : R} (h : a ∈ Ideal.span {b}) :
    v (algebraMap R C a) ≤ v (algebraMap R C b) := by
  exact hv.le_of_dvd (Ideal.mem_span_singleton.mp h)

theorem v_eq_of_span (hv : v.Integers R) {a b : R} (h : Ideal.span {a} = Ideal.span {b}) :
    v (algebraMap R C a) = v (algebraMap R C b) := by
  apply le_antisymm
  · apply v_le_of_mem hv
    rw [← h]
    exact Ideal.mem_span_singleton_self a
  · apply v_le_of_mem hv
    rw [h]
    exact Ideal.mem_span_singleton_self b

theorem sq_bound (hv : v.Integers R) {X : Type} (s : Set (X → C)) (l : (X → C) →ₗ[R] C)
    (b : NNReal) (h : ∀ g ∈ s, ∀ g' ∈ s, v (l (g * g')) ≤ b) :
    ∀ g ∈ sqIdeal (Submodule.span R s), v (l g) ≤ b := by
  have key : ∀ x y : X → C, v (l x) ≤ b → v (l y) ≤ b → v (l (x + y)) ≤ b := by
    intro x y hx hy
    rw [map_add]
    exact le_trans (v.map_add _ _) (max_le hx hy)
  have ksm : ∀ (r : R) (x : X → C), v (l x) ≤ b → v (l (r • x)) ≤ b := by
    intro r x hx
    rw [map_smul, Algebra.smul_def, map_mul]
    exact le_trans (mul_le_of_le_one_left (by positivity) (hv.map_le_one r)) hx
  have k0 : v (l 0) ≤ b := by simp
  have step : ∀ g ∈ Submodule.span R s, ∀ g' ∈ Submodule.span R s, v (l (g * g')) ≤ b := by
    intro g hg g' hg'
    induction hg using Submodule.span_induction with
    | mem x hx =>
      induction hg' using Submodule.span_induction with
      | mem y hy => exact h x hx y hy
      | zero => simpa using k0
      | add y z _ _ hy hz => rw [mul_add]; exact key _ _ hy hz
      | smul r y _ hy => rw [mul_smul_comm]; exact ksm r _ hy
    | zero => simpa using k0
    | add x z _ _ hx hz => rw [add_mul]; exact key _ _ hx hz
    | smul r x _ hx => rw [smul_mul_assoc]; exact ksm r _ hx
  intro g hg
  unfold sqIdeal at hg
  induction hg using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨f, hf, f', hf', rfl⟩ := hx
    exact step f hf f' hf'
  | zero => exact k0
  | add x z _ _ hx hz => exact key _ _ hx hz
  | smul r x _ hx => exact ksm r _ hx

variable [Fintype F] [DecidableEq F]

theorem pow_mem_aug (AA : HopfOrder (C := C) R F) {g : F → C} (hg : g ∈ augIdeal AA.carrier)
    (k : ℕ) : g ^ (k + 1) ∈ augIdeal AA.carrier := by
  rw [mem_aug] at hg ⊢
  refine ⟨?_, by simp [Pi.pow_apply, hg.2]⟩
  induction k with
  | zero => simpa using hg.1
  | succ n ih => rw [pow_succ]; exact AA.mul_mem _ _ ih hg.1

theorem pow_mem_sq (AA : HopfOrder (C := C) R F) (χ : MulChar F R) {c : R}
    (hc : c ∈ xIdeal AA.carrier χ) {k : ℕ} (hk : 2 ≤ k) :
    (fun a => algebraMap R C (c ^ k * (χ ^ k) a)) ∈ sqIdeal (augIdeal AA.carrier) := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 2 := ⟨k - 2, by omega⟩
  have hg : (fun a => algebraMap R C (c * χ a)) ∈ augIdeal AA.carrier := by
    rw [mem_aug]
    refine ⟨(mem_x_ideal_iff _ χ c).mp hc, ?_⟩
    simp [MulChar.map_nonunit χ not_isUnit_zero]
  have he : (fun a => algebraMap R C (c ^ (j + 2) * (χ ^ (j + 2)) a)) =
      (fun a => algebraMap R C (c * χ a)) * (fun a => algebraMap R C (c * χ a)) ^ (j + 1) := by
    funext a
    simp only [Pi.mul_apply, Pi.pow_apply, MulChar.pow_apply' χ (by omega : j + 2 ≠ 0), map_pow,
      map_mul]
    ring
  rw [he]
  unfold sqIdeal
  exact Submodule.subset_span ⟨_, hg, _, pow_mem_aug AA hg j, rfl⟩

theorem sq_le (AA : HopfOrder (C := C) R F) : sqIdeal (augIdeal AA.carrier) ≤ AA.carrier := by
  unfold sqIdeal
  rw [Submodule.span_le]
  rintro h ⟨f, hf, f', hf', rfl⟩
  exact AA.mul_mem f f' ((mem_aug _ f).mp hf).1 ((mem_aug _ f').mp hf').1

omit [Fintype F] [DecidableEq F] in
theorem eig_fun (χ : MulChar F R) (r : R) (a x : F) :
    algebraMap R C (r * χ (a • x)) = algebraMap R C (χ a) * algebraMap R C (r * χ x) := by
  simp only [smul_eq_mul, map_mul]; ring

end

theorem digits {p f m : ℕ} (h1 : 1 ≤ m) (h2 : m < p ^ f) :
    ∃ d : Fin f → Fin p, (∃ n, (d n : ℕ) ≠ 0) ∧ ∑ n : Fin f, (d n : ℕ) * p ^ (n : ℕ) = m := by
  have hp : 0 < p := by
    rcases Nat.eq_zero_or_pos p with h0 | h0
    · subst h0
      rcases f with _ | f <;> simp at h2 <;> omega
    · exact h0
  have key : ∀ (g : ℕ) (m : ℕ), m < p ^ g →
      ∃ d : Fin g → Fin p, ∑ n : Fin g, (d n : ℕ) * p ^ (n : ℕ) = m := by
    intro g
    induction g with
    | zero =>
      intro m hm
      refine ⟨Fin.elim0, ?_⟩
      simp at hm
      simp [hm]
    | succ g ih =>
      intro m hm
      obtain ⟨d', hd'⟩ := ih (m / p) (by
        rw [Nat.div_lt_iff_lt_mul hp, ← pow_succ]
        exact hm)
      refine ⟨Fin.cons ⟨m % p, Nat.mod_lt _ hp⟩ d', ?_⟩
      rw [Fin.sum_univ_succ]
      simp only [Fin.cons_zero, Fin.cons_succ, Fin.val_zero, Fin.val_succ, pow_zero, mul_one]
      have hs : ∑ x : Fin g, (d' x : ℕ) * p ^ ((x : ℕ) + 1) =
          (∑ x : Fin g, (d' x : ℕ) * p ^ (x : ℕ)) * p := by
        rw [Finset.sum_mul]
        exact Finset.sum_congr rfl (fun x _ => by ring)
      rw [hs, hd']
      exact Nat.mod_add_div' m p
  obtain ⟨d, hd⟩ := key f m h2
  refine ⟨d, ?_, hd⟩
  by_contra hne
  push_neg at hne
  have hz : ∑ n : Fin f, (d n : ℕ) * p ^ (n : ℕ) = 0 :=
    Finset.sum_eq_zero (fun n _ => by simp [hne n])
  omega

theorem hasLen_quot {C : Type} [Field C] {R : Type} [CommRing R] [Algebra R C]
    (v : Valuation C NNReal) {M : Type} [AddCommGroup M] [Module R M] (φ : R →ₗ[R] M)
    (hφ : Function.Surjective φ) (δ : R) (hk : LinearMap.ker φ = Ideal.span {δ}) :
    HasLen v R M (v (algebraMap R C δ)) := by
  refine ⟨1, fun _ => δ, ⟨?_⟩, by simp⟩
  exact ((φ.quotKerEquivOfSurjective hφ).symm.trans (Submodule.quotEquivOfEq _ _ hk)).trans
    (LinearEquiv.funUnique (Fin 1) R (R ⧸ Ideal.span {δ})).symm

end PositivityTheory.Xgn.A_xgr_r_om
end

