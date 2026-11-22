import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1535
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0777
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0019
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0841
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.ExistsPowPrincipalFractionalIdeal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1517
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0832
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0830
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsFlagModelHermSum
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1010
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1526
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1531
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1041
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1489

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MulVecInv
section
open scoped TensorProduct NNReal ENNReal Matrix ComplexConjugate
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.EisRes GlobalTheory.StdPar GlobalTheory.EisUnfold
open GlobalTheory.Doubling (absE)
open GlobalTheory.EisMidHt (adVec)
open Matrix

noncomputable section

namespace GlobalTheory.FlagNorm

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {r : ℕ}

omit [NumberField E] in
theorem mulVec_inv (g : GAd σ J) (y : Fin n → AF F ⊗[F] E) :
    (matHom _ σ J g).1 *ᵥ (matHom _ σ J g⁻¹).1 *ᵥ y = y := by
  rw [mulVec_mulVec, ← Units.val_mul, ← map_mul, mul_inv_cancel, map_one, Units.val_one, one_mulVec]

omit [NumberField E] in
theorem inv_mulVec (g : GAd σ J) (y : Fin n → AF F ⊗[F] E) :
    (matHom _ σ J g⁻¹).1 *ᵥ (matHom _ σ J g).1 *ᵥ y = y := by
  rw [mulVec_mulVec, ← Units.val_mul, ← map_mul, inv_mul_cancel, map_one, Units.val_one, one_mulVec]

omit [NumberField E] in
theorem keep_inv {g : GAd σ J} {A : Submodule (AF F ⊗[F] E) (Fin n → AF F ⊗[F] E)}
    (hA : ∀ y, y ∈ A ↔ (matHom _ σ J g).1 *ᵥ y ∈ A) (y : Fin n → AF F ⊗[F] E) :
    y ∈ A ↔ (matHom _ σ J g⁻¹).1 *ᵥ y ∈ A := by
  rw [hA ((matHom _ σ J g⁻¹).1 *ᵥ y), mulVec_inv]

omit [NumberField E] in
theorem conj_mulVec (m u : GAd σ J) (y : Fin n → AF F ⊗[F] E) :
    (matHom _ σ J (m * u * m⁻¹)).1 *ᵥ y =
      (matHom _ σ J m).1 *ᵥ (matHom _ σ J u).1 *ᵥ (matHom _ σ J m⁻¹).1 *ᵥ y := by
  rw [map_mul, map_mul, Units.val_mul, Units.val_mul, ← mulVec_mulVec, ← mulVec_mulVec]

omit [NumberField E] in
theorem conj_sub (m u : GAd σ J) (y : Fin n → AF F ⊗[F] E) :
    (matHom _ σ J (m * u * m⁻¹)).1 *ᵥ y - y =
      (matHom _ σ J m).1 *ᵥ ((matHom _ σ J u).1 *ᵥ (matHom _ σ J m⁻¹).1 *ᵥ y - (matHom _ σ J m⁻¹).1 *ᵥ y) := by
  rw [conj_mulVec, mulVec_sub, mulVec_inv]

omit [NumberField E] in
theorem keep_conj {m u : GAd σ J} {A : Submodule (AF F ⊗[F] E) (Fin n → AF F ⊗[F] E)}
    (hm : ∀ y, y ∈ A ↔ (matHom _ σ J m).1 *ᵥ y ∈ A) (hu : ∀ y, y ∈ A ↔ (matHom _ σ J u).1 *ᵥ y ∈ A)
    (y : Fin n → AF F ⊗[F] E) : y ∈ A ↔ (matHom _ σ J (m * u * m⁻¹)).1 *ᵥ y ∈ A := by
  rw [conj_mulVec]
  exact (keep_inv hm y).trans ((hu _).trans (hm _))

theorem perp_inv {X : Matrix (Fin n) (Fin r) E} {k : Fin r} {g : GAd σ J}
    (hg : ∀ y, y ∈ colSpan F X {i | i ≤ k} ↔ (matHom _ σ J g).1 *ᵥ y ∈ colSpan F X {i | i ≤ k})
    {y : Fin n → AF F ⊗[F] E} (hy : y ∈ colPerp σ J X {i | i ≤ k}) :
    (matHom _ σ J g⁻¹).1 *ᵥ y ∈ colPerp σ J X {i | i ≤ k} := by
  have hcol : ∀ i : Fin (k.val + 1), (matHom _ σ J g).1 *ᵥ (fun l => adMat F (initCols X k) l i) ∈
      colSpan F X {i | i ≤ k} := fun i =>
    (hg _).1 (Submodule.subset_span ⟨i.castLE k.2, Nat.le_of_lt_succ i.2, rfl⟩)
  choose a ha using fun i => mem_colSpan_iff.1 (hcol i)
  have hB : (matHom _ σ J g).1 * adMat F (initCols X k) = adMat F (initCols X k) * Matrix.of (fun l i => a i l) :=
    Matrix.ext fun l i => (congrFun (ha i) l).symm
  have hF := GlobalTheory.UAut.form_mul_of_mul_cols hB
  rw [mem_colPerp_iff] at hy ⊢
  rw [mulVec_mulVec, hF, ← mulVec_mulVec, hy, mulVec_zero]

end GlobalTheory.FlagNorm

open GlobalTheory.FlagNorm in

theorem GlobalTheory.FlagNorm.conj_mem_unip : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
    ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (r : ℕ) (X Y : Matrix (Fin n) (Fin r) E), IsWittFrame σ J X Y →
    ∀ (T : Finset (Fin r)) (m : GAd σ J),
      (∀ k ∈ T, ∀ y, y ∈ colSpan F X {i | i ≤ k} ↔ (matHom _ σ J m).1 *ᵥ y ∈ colSpan F X {i | i ≤ k}) →
      ∀ u ∈ unip σ J X T, m * u * m⁻¹ ∈ unip σ J X T := by
  intro F E _ _ _ _ _ σ h n J hJ r X Y hW T m hm u hu
  by_cases hT : T = ∅
  · subst hT
    rw [unip_empty, Subgroup.mem_bot] at hu ⊢
    simp [hu]
  have hne := Finset.nonempty_iff_ne_empty.2 hT
  have hkMT : T.max' hne ∈ T := T.max'_mem _
  have eB : {i | ∃ k ∈ T, i ≤ k} = {i | i ≤ T.max' hne} :=
    Set.ext fun i => ⟨fun ⟨k, hk, hik⟩ => hik.trans (T.le_max' k hk), fun hi => ⟨_, hkMT, hi⟩⟩

  have keepSub : ∀ T' : Finset (Fin r), T' ⊆ T → ∀ y, y ∈ colSpan F X {i | ∃ k ∈ T', i ≤ k} ↔
      (matHom _ σ J m).1 *ᵥ y ∈ colSpan F X {i | ∃ k ∈ T', i ≤ k} := by
    intro T' hT' y
    by_cases h0 : T' = ∅
    · subst h0
      have e : {i : Fin r | ∃ k ∈ (∅ : Finset (Fin r)), i ≤ k} = ∅ := by simp
      rw [e, colSpan, Set.image_empty, Submodule.span_empty, Submodule.mem_bot, Submodule.mem_bot]
      exact ⟨fun hy => by rw [hy, mulVec_zero], fun hy => by rw [← inv_mulVec m y, hy, mulVec_zero]⟩
    · have hne' := Finset.nonempty_iff_ne_empty.2 h0
      have e : {i | ∃ k ∈ T', i ≤ k} = {i | i ≤ T'.max' hne'} :=
        Set.ext fun i => ⟨fun ⟨k, hk, hik⟩ => hik.trans (T'.le_max' k hk), fun hi => ⟨_, T'.max'_mem _, hi⟩⟩
      rw [e]
      exact hm _ (hT' (T'.max'_mem _)) y
  have eA : ∀ j : Fin r, {i | ∃ k ∈ T, i ≤ k ∧ k < j} = {i | ∃ k ∈ T.filter (· < j), i ≤ k} := fun j =>
    Set.ext fun i => ⟨fun ⟨k, hk, h1, h2⟩ => ⟨k, Finset.mem_filter.2 ⟨hk, h2⟩, h1⟩,
      fun ⟨k, hk, h1⟩ => ⟨k, (Finset.mem_filter.1 hk).1, h1, (Finset.mem_filter.1 hk).2⟩⟩
  have keepA : ∀ j : Fin r, ∀ y, y ∈ colSpan F X {i | ∃ k ∈ T, i ≤ k ∧ k < j} ↔
      (matHom _ σ J m).1 *ᵥ y ∈ colSpan F X {i | ∃ k ∈ T, i ≤ k ∧ k < j} := fun j => by
    rw [eA j]
    exact keepSub _ (Finset.filter_subset _ _)
  have keepB := keepSub T subset_rfl
  rw [eB] at keepB
  have hu1 : ∀ j, u ∈ trivOn σ J (colSpan F X {i | ∃ k ∈ T, i ≤ k ∧ k < j}) (colSpan F X {j}) :=
    fun j => Subgroup.mem_iInf.1 (Subgroup.mem_inf.1 hu).1 j
  have hu2 : u ∈ trivOn σ J (colSpan F X {i | i ≤ T.max' hne}) (colPerp σ J X {i | i ≤ T.max' hne}) := by
    have := (Subgroup.mem_inf.1 hu).2
    rw [eB] at this
    exact this
  refine Subgroup.mem_inf.2 ⟨Subgroup.mem_iInf.2 fun j => ⟨keep_conj (keepA j) (hu1 j).1, fun y hy => ?_⟩, ?_⟩
  ·
    unfold colSpan at hy
    rw [Set.image_singleton, Submodule.mem_span_singleton] at hy
    obtain ⟨a, rfl⟩ := hy
    rw [mulVec_smul, ← smul_sub]
    refine Submodule.smul_mem _ a ?_
    rw [conj_sub]
    refine (keepA j _).1 ?_
    set z := (matHom _ σ J m⁻¹).1 *ᵥ (adMat F X)ᵀ j
    by_cases hex : ∃ k ∈ T, j ≤ k
    · have hne2 : (T.filter (j ≤ ·)).Nonempty := let ⟨k, hk, hjk⟩ := hex; ⟨k, Finset.mem_filter.2 ⟨hk, hjk⟩⟩
      set k0 := (T.filter (j ≤ ·)).min' hne2
      have hk0 := Finset.mem_filter.1 ((T.filter (j ≤ ·)).min'_mem hne2)
      have hmin : ∀ k ∈ T, j ≤ k → k0 ≤ k := fun k hk hjk => (T.filter (j ≤ ·)).min'_le k (Finset.mem_filter.2 ⟨hk, hjk⟩)
      have hz : z ∈ colSpan F X {i | i ≤ k0} :=
        (keep_inv (hm k0 hk0.1) _).1 (Submodule.subset_span ⟨j, hk0.2, rfl⟩)
      have hle : colSpan F X {i | i ≤ k0} ≤
          (colSpan F X {i | ∃ k ∈ T, i ≤ k ∧ k < j}).comap ((matHom _ σ J u).1 - 1).mulVecLin := by
        refine Submodule.span_le.2 ?_
        rintro _ ⟨i, hi, rfl⟩
        have h1 := (hu1 i).2 _ (Submodule.subset_span ⟨i, Set.mem_singleton i, rfl⟩)
        have hsub : {l | ∃ k ∈ T, l ≤ k ∧ k < i} ⊆ {l | ∃ k ∈ T, l ≤ k ∧ k < j} := by
          rintro l ⟨k', hk', hlk', hk'i⟩
          refine ⟨k', hk', hlk', not_le.1 fun hjk' => ?_⟩
          exact absurd (hmin k' hk' hjk') (not_le.2 (lt_of_lt_of_le hk'i hi))
        have h2 := Submodule.span_mono (R := AF F ⊗[F] E) (Set.image_mono (f := fun i => (adMat F X)ᵀ i) hsub) h1
        change _ ∈ colSpan F X _ at h2
        simpa [sub_mulVec] using h2
      simpa [sub_mulVec] using hle hz
    · push_neg at hex
      have eAj : {i | ∃ k ∈ T, i ≤ k ∧ k < j} = {i | i ≤ T.max' hne} := by
        rw [← eB]
        exact Set.ext fun i => ⟨fun ⟨k, hk, h1, _⟩ => ⟨k, hk, h1⟩, fun ⟨k, hk, h1⟩ => ⟨k, hk, h1, hex k hk⟩⟩
      rw [eAj]
      have hxj : (adMat F X)ᵀ j ∈ colPerp σ J X {i | i ≤ T.max' hne} := by
        refine mem_colPerp_iff.2 (funext fun i => ?_)
        exact (RingHom.map_mulVec (inclR (F := F) (AF F)) _ (Xᵀ j) i).symm.trans
          ((congrArg _ (congrFun (congrFun hW.xx (i.castLE (T.max' hne).2)) j)).trans (map_zero _))
      exact hu2.2 z (perp_inv (hm _ hkMT) hxj)
  · rw [eB]
    refine ⟨keep_conj keepB hu2.1, fun y hy => ?_⟩
    rw [conj_sub]
    exact (keepB _).1 (hu2.2 _ (perp_inv (hm _ hkMT) hy))
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormalisedFamilyEqTensorPowerVacuum
section
open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker

noncomputable section

namespace GlobalTheory.FamilyTieProof

theorem std : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Base D cc δ), TaylorLogMetric.adm1 D → GL3Theta.InducedCMType D → TaylorLogMetric.IsCurveIdeal D cc → TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice D cc δ → B.kc.YFinite → ∀ N N' : ℕ, Even N → Even N' → StandardLatticesGL3.ThetaVectorUpToUnits D (TaylorLogMetric.tor0 D cc δ) (B.ω₀ / 2) (StandardLatticesGL3.stdL D N) (StandardLatticesGL3.stdL D N') (B.thZero N N') := GlobalTheory.T.base_theta_vector_is_vacuum_even_ranks

theorem detn1 : ∀ (D : D7) (N : ℕ) (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)), StandardLatticesGL3.SD D L → TaylorLogMetric.N1 D (TaylorLogMetric.detId D (StandardLatticesGL3.stdL D N) L) := GlobalTheory.T.relDetIdeal_selfDual_normOne

theorem chin1 : ∀ (D : D7) (χ : TaylorLogMetric.IdE D → ℂ), TaylorLogMetric.IsChi D χ → ∀ 𝔞 : TaylorLogMetric.IdE D, TaylorLogMetric.N1 D 𝔞 → StandardLatticesGL3.Mod1All (χ 𝔞) := GlobalTheory.T.normOneCharacter_modulusOne_all_embeddings

theorem mod1All_mul' {a b : ℂ} (ha : StandardLatticesGL3.Mod1All a) (hb : StandardLatticesGL3.Mod1All b) : StandardLatticesGL3.Mod1All (a * b) := by
  obtain ⟨h1, h1'⟩ := ha
  obtain ⟨h2, h2'⟩ := hb
  refine ⟨mul_mem h1 h2, fun σ => ?_⟩
  have e : (⟨a * b, mul_mem h1 h2⟩ : TaylorLogMetric.Qbar) = ⟨a, h1⟩ * ⟨b, h2⟩ := rfl
  rw [e, map_mul, norm_mul, h1' σ, h2' σ, one_mul]

theorem mod1All_inv {a : ℂ} (ha : StandardLatticesGL3.Mod1All a) : StandardLatticesGL3.Mod1All a⁻¹ := by
  obtain ⟨h1, h1'⟩ := ha
  refine ⟨inv_mem h1, fun σ => ?_⟩
  have e : (⟨a⁻¹, inv_mem h1⟩ : TaylorLogMetric.Qbar) = (⟨a, h1⟩ : TaylorLogMetric.Qbar)⁻¹ := rfl
  rw [e, map_inv₀, norm_inv, h1' σ, inv_one]

theorem mod1All_pow {a : ℂ} (ha : StandardLatticesGL3.Mod1All a) (n : ℕ) : StandardLatticesGL3.Mod1All (a ^ n) := by
  induction n with
  | zero =>
    refine ⟨by simpa using one_mem TaylorLogMetric.Qbar, fun σ => ?_⟩
    have e : (⟨a ^ 0, by simpa using one_mem TaylorLogMetric.Qbar⟩ : TaylorLogMetric.Qbar) = 1 := by ext; simp
    rw [e, map_one, norm_one]
  | succ n ih => rw [pow_succ]; exact mod1All_mul' ih ha

theorem mod1All_zpow {a : ℂ} (ha : StandardLatticesGL3.Mod1All a) (n : ℤ) : StandardLatticesGL3.Mod1All (a ^ n) := by
  cases n with
  | ofNat n => simpa using mod1All_pow ha n
  | negSucc n => rw [zpow_negSucc]; exact mod1All_inv (mod1All_pow ha _)

theorem genusOneVacuum_const_mul_modulusOne {D : D7} {T : TaylorLogMetric.Tor D} {t0 : ℂ} {N N' : ℕ} {L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)}
    {L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)} {G : TaylorLogMetric.VC D N N' → ℂ} {c : ℂ} (hc : StandardLatticesGL3.Mod1All c)
    (hG : StandardLatticesGL3.ThetaVectorUpToUnits D T t0 L L' G) : StandardLatticesGL3.ThetaVectorUpToUnits D T t0 L L' (fun z => c * G z) := by
  obtain ⟨b, κ, hb, hκ, rfl⟩ := hG
  exact ⟨b, c * κ, hb, mod1All_mul' hc hκ, funext fun z => by simp only [mul_assoc]⟩

theorem genusOneVacuum_indep_twoTorsionPoint {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} (hc : StandardLatticesGL3.Crv D cc δ) {t t' : ℂ}
    (ht : GL3Theta.IsTwoTorsionPointUnkilled D (TaylorLogMetric.lamOf D cc δ) t) (ht' : GL3Theta.IsTwoTorsionPointUnkilled D (TaylorLogMetric.lamOf D cc δ) t') {N N' : ℕ}
    {L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)} {L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)}
    {G : TaylorLogMetric.VC D N N' → ℂ} (h : StandardLatticesGL3.ThetaVectorUpToUnits D (TaylorLogMetric.tor0 D cc δ) t L L' G) :
    StandardLatticesGL3.ThetaVectorUpToUnits D (TaylorLogMetric.tor0 D cc δ) t' L L' G := by
  have e : GL3Theta.th0 (TaylorLogMetric.lamOf D cc δ) t = GL3Theta.th0 (TaylorLogMetric.lamOf D cc δ) t' := by
    have := GlobalTheory.ThetaConj.evenTheta_add_lattice_mem (GlobalTheory.ThetaConj.isLat_lamOf hc) t' (GlobalTheory.Glob.isThetaZero_unique_lattice hc ht ht')
    rwa [add_sub_cancel] at this
  unfold StandardLatticesGL3.ThetaVectorUpToUnits at h ⊢
  exact e ▸ h

theorem chiFac_mod1All (D : D7) (χ : TaylorLogMetric.IdE D → ℂ) (hχ : TaylorLogMetric.IsChi D χ) (N N' : ℕ)
    (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E))
    (hA : TaylorLogMetric.admitted D N N' L L') : StandardLatticesGL3.Mod1All (Base.chiFac (D := D) χ N N' L L') :=
  mod1All_mul' (mod1All_zpow (chin1 D χ hχ _ (detn1 D N L hA.2.2.1)) _)
    (mod1All_zpow (chin1 D χ hχ _ (detn1 D N' L' hA.2.2.2)) _)

theorem familyTie : GlobalTheory.ColNorms.FamilyTie := by
  intro D cc δ B χ ha hp hcc hδ hχ hY t0 ht N N' L L' hA
  have hc : StandardLatticesGL3.Crv D cc δ := ⟨hcc, hδ⟩
  have h0 := genusOneVacuum_indep_twoTorsionPoint hc B.t0 ht (std D cc δ B ha hp hcc hδ hY N N' hA.1 hA.2.1)
  exact genusOneVacuum_const_mul_modulusOne (chiFac_mod1All D χ hχ N N' L L' hA)
    (GlobalTheory.MovedVacuum.isVacuum_movedThetaVacuum D cc δ B t0 hc ht N N' L L' hA.2.2.1 hA.2.2.2 h0)

end GlobalTheory.FamilyTieProof
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneCompOfIsGrpPullback
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CxPts GlobalTheory.VB
open Limits (pullback)
open MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj

namespace GlobalTheory.PPAS

variable {S S' : Scheme.{0}}

theorem one_comp_of_isGrpPullback {A : Over S} {A' : Over S'} [GrpObj A] [GrpObj A'] {f : S' ⟶ S}
    {φ : A'.left ⟶ A.left} (h : IsGrpPullback A' A f φ) :
    (1 : A' ⟶ A').left ≫ φ = φ ≫ (1 : A ⟶ A).left := by
  have e := congrArg (fun z => z.left) (map_one (pushHom h A'))
  let g : Over.mk (A'.hom ≫ f) ⟶ A := Over.homMk φ h.1.w
  have e2 : g ≫ (1 : A ⟶ A) = 1 := by simp
  have e3 := congrArg (fun z : Over.mk (A'.hom ≫ f) ⟶ A => z.left) e2
  simp only [Over.comp_left] at e3
  rw [← e3] at e
  exact e

theorem lift_sqMap {A : Over S} {A' : Over S'} [GrpObj A] [GrpObj A'] {f : S' ⟶ S}
    {φ : A'.left ⟶ A.left} (h : IsGrpPullback A' A f φ) (a' b' : A' ⟶ A') (a b : A ⟶ A)
    (ha : a'.left ≫ φ = φ ≫ a.left) (hb : b'.left ≫ φ = φ ≫ b.left) :
    (lift a' b').left ≫ sqMap h.1.w = φ ≫ (lift a b).left := by
  apply pullback.hom_ext
  · simp only [sqMap, pullback.map, Category.assoc, pullback.lift_fst, pullback.lift_fst_assoc]
    have k₁ : (lift a' b').left ≫ pullback.fst A'.hom A'.hom = a'.left :=
      congrArg (fun z => z.left) (lift_fst a' b')
    have k₂ : (lift a b).left ≫ pullback.fst A.hom A.hom = a.left := congrArg (fun z => z.left) (lift_fst a b)
    rw [← Category.assoc, k₁, k₂, ha]
  · simp only [sqMap, pullback.map, Category.assoc, pullback.lift_snd, pullback.lift_snd_assoc]
    have k₁ : (lift a' b').left ≫ pullback.snd A'.hom A'.hom = b'.left :=
      congrArg (fun z => z.left) (lift_snd a' b')
    have k₂ : (lift a b).left ≫ pullback.snd A.hom A.hom = b.left := congrArg (fun z => z.left) (lift_snd a b)
    rw [← Category.assoc, k₁, k₂, hb]

theorem sqToBase_fst {T : Scheme.{0}} (A : Over S) (s : T ⟶ S) :
    IndefiniteRowSideFullHecke.ZeroSectionBase.sqToBase A s ≫ pullback.fst A.hom A.hom =
      (fst ((Over.pullback s).obj A) ((Over.pullback s).obj A)).left ≫ pullback.fst A.hom s :=
  congrArg (fun z => z.left) (lift_fst (IndefiniteRowSideFullHecke.ZeroSectionBase.toBase A s (fst _ _)) (IndefiniteRowSideFullHecke.ZeroSectionBase.toBase A s (snd _ _)))

theorem sqToBase_snd {T : Scheme.{0}} (A : Over S) (s : T ⟶ S) :
    IndefiniteRowSideFullHecke.ZeroSectionBase.sqToBase A s ≫ pullback.snd A.hom A.hom =
      (snd ((Over.pullback s).obj A) ((Over.pullback s).obj A)).left ≫ pullback.fst A.hom s :=
  congrArg (fun z => z.left) (lift_snd (IndefiniteRowSideFullHecke.ZeroSectionBase.toBase A s (fst _ _)) (IndefiniteRowSideFullHecke.ZeroSectionBase.toBase A s (snd _ _)))

theorem sqToBase_comp_sqMap {A : Over S} {A' : Over S'} {f : S' ⟶ S}
    {φ : A'.left ⟶ A.left} (w : φ ≫ A.hom = A'.hom ≫ f) {T : Scheme.{0}} (s : T ⟶ S')
    {ψ : ((Over.pullback s).obj A').left ⟶ ((Over.pullback (s ≫ f)).obj A).left}
    (w' : ψ ≫ ((Over.pullback (s ≫ f)).obj A).hom = ((Over.pullback s).obj A').hom ≫ 𝟙 T)
    (hψ : ψ ≫ pullback.fst A.hom (s ≫ f) = pullback.fst A'.hom s ≫ φ) :
    IndefiniteRowSideFullHecke.ZeroSectionBase.sqToBase A' s ≫ sqMap w = sqMap w' ≫ IndefiniteRowSideFullHecke.ZeroSectionBase.sqToBase A (s ≫ f) := by
  apply pullback.hom_ext
  · simp only [sqMap, pullback.map, Category.assoc, pullback.lift_fst]
    rw [sqToBase_fst, ← Category.assoc, sqToBase_fst]
    show pullback.fst _ _ ≫ pullback.fst A'.hom s ≫ φ =
      pullback.lift _ _ _ ≫ pullback.fst _ _ ≫ pullback.fst A.hom (s ≫ f)
    rw [pullback.lift_fst_assoc, Category.assoc, hψ]
  · simp only [sqMap, pullback.map, Category.assoc, pullback.lift_snd]
    rw [sqToBase_snd, ← Category.assoc, sqToBase_snd]
    show pullback.snd _ _ ≫ pullback.fst A'.hom s ≫ φ =
      pullback.lift _ _ _ ≫ pullback.snd _ _ ≫ pullback.fst A.hom (s ≫ f)
    rw [pullback.lift_snd_assoc, Category.assoc, hψ]

theorem isPrincipalPol_pull {A : Over S} {A' : Over S'} [GrpObj A] [GrpObj A'] {f : S' ⟶ S}
    {φ : A'.left ⟶ A.left} (h : IsGrpPullback A' A f φ) {c : CechPic.Pic (A ⊗ A).left}
    (hc : IndefiniteRowSideFullHecke.ZeroSectionBase.IsPrincipalPol A c) :
    IndefiniteRowSideFullHecke.ZeroSectionBase.IsPrincipalPol A' (CechPic.pull (sqMap h.1.w) c) := by
  have h1 := one_comp_of_isGrpPullback h
  refine ⟨?_, ?_, fun Ω _ _ s => ?_⟩
  · rw [← CechPic.pull_comp, lift_sqMap h _ _ 1 (𝟙 A) h1 (by simp), CechPic.pull_comp, hc.1, map_zero]
  · rw [← CechPic.pull_comp, lift_sqMap h _ _ (𝟙 A) 1 (by simp) h1, CechPic.pull_comp, hc.2.1, map_zero]
  · obtain ⟨L, hL, hA, hK, hcL⟩ := hc.2.2 Ω (s ≫ f)
    have hB' := (isGrpPullback_pullback A' s).comp h
    have hB := isGrpPullback_pullback A (s ≫ f)
    obtain ⟨e, he, hφ⟩ := grpPullback_iso hB' hB
    have h₁ := isGrpPullback_of_iso e
    have hL' := pull_isLB hL e.hom.left
    obtain ⟨w, hw⟩ := (CechPic.cls_eq_iff hL' hL').1 rfl
    refine ⟨_, hL', relAmple_pull h₁.1 hL hL' ((isGen_iff w).1 hw) ⊤ (isAffineOpen_top _)
      (fun _ => trivial) hA, kTriv_pull h₁ hL hL' ((isGen_iff w).1 hw) hK, ?_⟩
    rw [← CechPic.pull_comp, sqToBase_comp_sqMap h.1.w s h₁.1.w hφ, CechPic.pull_comp, hcL,
      pull_sqMap_lam h₁, CechPic.cls_pull hL]

theorem exists_pull (S S' : Scheme.{0}) (P : PPAS S) (f : S' ⟶ S) :
    ∃ (P' : PPAS S') (φ : P'.A.left ⟶ P.A.left), P'.g = P.g ∧ P'.IsPull P f φ := by
  have h := isGrpPullback_pullback P.A f
  exact ⟨{ A := (Over.pullback f).obj P.A
           isAb := PolPull.isAbelianScheme_of_isGrpPullback P.isAb h
           g := P.g
           smoothDim := (smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback h.1 P.smoothDim
           c := CechPic.pull (sqMap h.1.w) P.c
           isPol := isPrincipalPol_pull h P.isPol }, pullback.fst P.A.hom f, rfl, h, rfl⟩
end GlobalTheory.PPAS
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.OscillatorModelsEvaluateSecond
section
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT
open GlobalTheory.IndefiniteRowSideFullHecke.WeilGramSignature
open scoped TensorProduct InnerProductSpace
open GlobalTheory.GalLift
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.GalLift.BaseId

variable {D : D7}

section Row

open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD

theorem tie_baseChange {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c c' : Coeff l}
    (hle : c.F ≤ c'.F) {r n : ℕ} (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (σ' : c'.F →+* ℂ) (V : HSp D)
    (dict : GA D V → Σ k, Frame ((U (σ'.comp (incF c c' hle))).X k).Ψ r) (mu : GA D V → ℂ) (xr : ℝ)
    (a : (D.host.E →+* ℂ) × ℕ → ℕ) {Γ : Type} [Group Γ]
    {act : Γ → Rul Xo c →ₗ[c.F] Rul Xo c} {act' : Γ → Rul Xo c' →ₗ[c'.F] Rul Xo c'}
    {Vs : Type} [AddCommGroup Vs] [Module c'.F Vs] {Tup : Type} {dδ : Tup → DeltaDat Xo c' n}
    {Cl' : Tup → Type} [∀ t, Fintype (Cl' t)]
    {w : ∀ t, Cl' t → (Fin n → LevQ Dw (dδ t).l₂) → c'.F} {La : ∀ t, Cl' t → GenLat D.host.E n} {Nc : ∀ t, Cl' t → ℕ}
    {gam : ∀ t, Cl' t → ℕ} {vol : Tup → c'.F} {ep : ∀ t, Cl' t → c'.F} {io : Vs →ₗ[c'.F] MvPolynomial (LtN Dw n) c'.F}
    {thAd : ∀ t, (Cl' t → Vs) → (AutQ V → ℂ)} {Pl : ∀ t, (Cl' t → Vs) → Prop} {LL : IntermediateField ℚ ℂ}
    {cc : (U (σ'.comp (incF c c' hle))).Comp → ℂ} {ph : ℂ}
    (htie : OneMapTieC hle LL U σ' V dict mu xr a act act' dδ Cl' w La Nc gam vol ep io thAd Pl cc ph) (t : Tup) :
    ∃ z ∈ Subgroup.center Γ, ∃ ze ∈ LL, (∃ m : ℕ, 0 < m ∧ ze ^ m = 1) ∧ ∀ x : Cl' t → Vs, Pl t x →
      ∃ (f' : Rul Xo c') (m : ℕ) (as : Fin m → c'.F) (fs : Fin m → Rul Xo c), f' ∈ sec Xo c' a n ∧
        IsThClsD Xo c' (dδ t) (w t) (La t) (Nc t) (gam t) (vol t) (ep t) io x f' ∧ (∀ k, fs k ∈ cusp Xo c U a n) ∧
        IsBC hle f' as fs ∧ ∀ q : AutQ V, ph * thAd t x q = ∑ k, ze * σ' (as k) * ((lieFac Dw xr a : ℂ) *
          adel V dict (muPin V dict mu cc) (rdU (U (σ'.comp (incF c c' hle))) (act z (fs k))) q.out) := by
  obtain ⟨-, hC, hA, -, -, z, hz, hrow⟩ := htie
  obtain ⟨ze, hze, hroot, hrow⟩ := hrow t
  refine ⟨z, hz, ze, hze, hroot, fun x hx => ?_⟩
  obtain ⟨⟨f', hf', hcl⟩, hall⟩ := hrow x hx
  have hf's := cusp_le_sec _ _ _ _ _ hf'
  obtain ⟨m, as, fs, hfs, hBC⟩ := hC a n f' hf'
  have hBCz := hA a n z m as fs f' hf's (fun k => cusp_le_sec _ _ _ _ _ (hfs k)) hBC
  refine ⟨f', m, as, fs, hf's, hcl, hfs, hBC, fun q => ?_⟩
  have h1 := hall f' hf's hcl q
  have h2 := GlobalTheory.PhaseRational.rdU_of_isBC hle U σ' hBCz (dict q.out).1 (dict q.out).2
  have h3 : jFn V σ' (rdU (unfBC hle U σ')) dict mu (act' z f') q = mu q.out * ∑ k, σ' (as k) *
      rdU (U (σ'.comp (incF c c' hle))) (act z (fs k)) (dict q.out).1 (dict q.out).2 :=
    congrArg (mu q.out * ·) h2
  rw [h1, h3, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [adel_muPin]
  change ze * cc (dict q.out).1 * _ * _ = _
  ring

end Row

theorem phiC_congr (T : CoreJ D) {j : ℕ} {σ σ' : T.Q.c.F →+* ℂ} (e : σ = σ') {W : HSp D} (hV : T.V j σ = W)
    (hV' : T.V j σ' = W) (a : (D.host.E →+* ℂ) × ℕ → ℕ) (f : T.R j) : phiC T hV a f = phiC T hV' a f := by
  subst e
  rfl

theorem proj_model {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S) {X G : Type} [AddCommGroup X] [Module ℂ X] [Fintype G]
    (e : X →ₗ[ℂ] MMap M) (he : Function.Injective e) (L : G → (GA D V → ℂ) →ₗ[ℂ] (GA D V → ℂ)) (c : G → ℂ)
    (ρ : G → X →ₗ[ℂ] X) (hρ : ∀ g x, e (ρ g x) = postOn M (L g) (e x)) (ph : ℂ) (y y' w : X)
    (hy : e y' = postOn M (∑ g, c g • L g) (e y)) (hw : ph • y = w) : ph • y' = ∑ g, c g • ρ g w := by
  have h1 : y' = ∑ g, c g • ρ g y := by
    apply he
    rw [hy, map_sum]
    simp only [map_smul, hρ]
    ext v x
    simp [postOn, LinearMap.sum_apply, Finset.sum_apply]
  rw [h1, ← hw, Finset.smul_sum]
  exact Finset.sum_congr rfl fun g _ => by rw [map_smul, smul_comm]

theorem eq_of_reps {V : HSp D} {S : D.what₂.Tau → SPar} {θ} {M : DSModel V S} {J : Set (GA D V)} {χ : GA D V → ℂ}
    {X : Type} [AddCommGroup X] [Module ℂ X] (e : X →ₗ[ℂ] MMap M) (hr : LinearMap.range e = Mult.Mult θ M J χ) (v : M.Vec)
    (hinj : Function.Injective fun x => e x v) (ph : ℂ) (y : X) {n : ℕ} (b : Fin n → ℂ) (u : Fin n → X)
    (h : ∀ q : AutQ V, ph * e y v q.out = ∑ k, b k * e (u k) v q.out) : ph • y = ∑ k, b k • u k := by
  apply hinj
  funext g
  refine GlobalTheory.PhaseRational.eq_of_out
    (GlobalTheory.PhaseRational.mult_leftInv (hr.le (LinearMap.mem_range_self e _)) v)
    (GlobalTheory.PhaseRational.mult_leftInv (hr.le (LinearMap.mem_range_self e _)) v) (fun q => ?_) g
  simpa [map_sum, Finset.sum_apply] using h q

theorem base_identity : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A) (κw : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec), R.Char F → ∀ (fw : FWTie T R κw v₀) (i : Fin D.R.m), fw.Evaluates → EvInj T R v₀ → ∀ (O : ∀ i, OMDat T.toCore R i Unit (fun _ => A.μ0)) (ph : ℂ), OMPins T R κw v₀ O i → (O i).OneMapOf (κw i) (v₀ i (sg0 D A)) (T.cE ((i : ℕ) + 1) (O i).s0) ph → ∀ h, RepsAt (O i) (v₀ i (sg0 D A)) h → ∃ z ∈ Subgroup.center G, ∃ ze : D.what₂.LL, (∃ m : ℕ, 0 < m ∧ ze ^ m = 1) ∧ ∀ x₀, ∃ (n : ℕ) (a : Fin n → D.what₂.LL) (f : Fin n → Cu T κw i), IsClassSum (O i) κw h x₀ a f ∧ ∀ f₁ : Fin n → Cu T κw i, (∀ k, (f₁ k : T.R ((i : ℕ) + 1)) = actG (O i) z (f k : T.R ((i : ℕ) + 1))) → ph • R.thG i A.μ0 (R.jV i A.μ0 x₀) = ∑ g, RealDat.eC (A := A) (sg0 D A) g • R.gW i (sg0 D A) g (∑ k, D.what₂.embLL (ze * a k) • fw.jK i (sg0 D A) (f₁ k)) := by
  intro D G _ _ Pl0 T0 A T _ R F κw v₀ hch fw i hev hinj O ph hpins hone h hreps
  have hrk : (Vc D i).rank = (κw i).n :=
    (D.sp.V_rank _ (Nat.le_add_left _ _) i.2).trans (fw.kap i (D.eTau.symm 1)).2.2.symm
  have hs : sg0 D A = D.what₂.embLL := sgAt_mk _ R.hv0
  have hpf : T.Q.PinField := fw.laws.toLawsM.pins.2.2.1
  have hres : res T (sg0 D A) = (O i).s0 :=
    (congrArg (res T) hs).trans ((res_embLL T fw.alg_eq hpf).trans (sOv_eq T.toCore (O i).c' (O i).hle).symm)
  have hgood : GoodEmb T.Q.c (res T (sg0 D A)) := base_embedding_good T R fw.alg_eq hpf
  have hV : T.V ((i : ℕ) + 1) (res T (sg0 D A)) = Wc D i := (congrArg (T.V ((i : ℕ) + 1)) hres).trans (O i).hV
  have hfield : ∀ b, inC (O i).c' ((O i).jL b) = D.what₂.embLL b := fun b => RingHom.congr_fun hpins.2.lift.field b
  refine (tie_baseChange (O i).hle (T.U ((i : ℕ) + 1)) (inC (O i).c') (Wc D i) (O i).dict (O i).mu
    (xiR D) (wtA (κw i)) hone.2.1 ()).imp fun z hz => ⟨hz.1, hz.2.elim fun ze hze => hze.1.elim fun ze' hze' => ?_⟩
  have hze'' : D.what₂.embLL ze' = ze := hze'
  refine ⟨ze', hze.2.1.imp fun m hm => ⟨hm.1, D.what₂.embLL.injective
    ((map_pow _ _ _).trans ((congrArg (· ^ m) hze'').trans (hm.2.trans (map_one _).symm)))⟩, fun x₀ => ?_⟩
  refine hreps.elim fun J' hJ => (hJ.2.1 x₀).elim fun x hx => ?_
  refine (hze.2.2 x ((hJ.2.2.2 x).2 ⟨x₀, hx⟩)).elim fun f' h1 => h1.elim fun m h1 => h1.elim fun as h1 => h1.elim fun fs h1 => ?_
  have has : ∀ k, ∃ b : D.what₂.LL, D.what₂.embLL b = inC (O i).c' (as k) := fun k => hpins.1.le (as k).2
  have has' : (fun k => (O i).jL (has k).choose) = as := funext fun k =>
    (inC (O i).c').injective ((hfield _).trans (has k).choose_spec)
  have hfs : ∀ k, fs k ∈ T.cuspA ((i : ℕ) + 1) (wtA (κw i)) (κw i).n := fun k => hrk ▸ h1.2.2.1 k
  refine ⟨m, fun k => (has k).choose, fun k => ⟨fs k, hfs k⟩, ⟨x, f', hx, h1.1, h1.2.1, ?_⟩, fun f₁ hf₁ => ?_⟩
  · exact (congrArg (fun b => IsBC (O i).hle f' b fs) has').mpr h1.2.2.2.1
  have hHW := hch.models.HW i (sg0 D A)
  have hy : R.thF i A.μ0 (jVx R i A.μ0 x₀) ∈ LinearMap.range (R.HW i (sg0 D A)).e :=
    hHW.2.1.ge (hch.thP.thF_mem i A.μ0 _)
  refine hy.elim fun y hy => ?_
  refine proj_model (R.MW i (sg0 D A)) (R.HW i (sg0 D A)).e hHW.1
    (fun g => Links.actL (Wc D i) (R.βW i) (R.datWp i R.triv) (R.eG g)) _ (fun g => R.gW i (sg0 D A) g)
    (hch.models.gW i (sg0 D A)) ph y _ _
    ((hch.thP.thG i A.μ0 (jVx R i A.μ0 x₀)).trans (congrArg (postOn _ (R.eWf i (sg0 D A))) hy.symm)) ?_
  refine eq_of_reps (R.HW i (sg0 D A)).e hHW.2.1 (v₀ i (sg0 D A)) (hinj i _ hgood) ph y _ _ fun q => ?_
  have h2 : (R.HW i (sg0 D A)).e y (v₀ i (sg0 D A)) q.out = (O i).thAd () x q :=
    (congrArg (fun S : MMap (R.MW i (sg0 D A)) => S (v₀ i (sg0 D A)) q.out) hy).trans
      (congrFun (hJ.2.2.1 _ x hx) q).symm
  refine (congrArg (ph * ·) h2).trans ((h1.2.2.2.2 q).trans (Finset.sum_congr rfl fun k _ => congrArg₂ (· * ·) ?_ ?_))
  · exact (congrArg₂ (· * ·) hze'' (has k).choose_spec).symm.trans (map_mul D.what₂.embLL _ _).symm
  · refine (phi_cE T R O i (wtA (κw i)) (actG (O i) z (fs k)) q.out).trans ?_
    refine Eq.symm ((congrFun (hev i _ hgood hV (f₁ k)) q.out).trans ?_)
    exact congrFun ((phiC_congr T hres hV (O i).hV _ _).trans
      (congrArg (phiC T (O i).hV (wtA (κw i))) (hf₁ k))) q.out

end GlobalTheory.GalLift.BaseId

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzFockVacuumLineUniqueOfHeisenbergDerivatiStatement
section
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.schwartzFockVacuumLineUnique_of_heisenberg_derivatives : GlobalTheory.RealLift.DerEx → GlobalTheory.RealLift.VacLine := by
  first | exact @GlobalTheory.VacLn.vacLine_of_derEx | exact GlobalTheory.VacLn.vacLine_of_derEx | (intros; apply GlobalTheory.VacLn.vacLine_of_derEx <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzFunctionalDependsOnValueAtZeroStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.schwartz_functional_depends_on_value_at_zero : ∀ {Y : Type} [NormedAddCommGroup Y] [NormedSpace ℝ Y] [FiniteDimensional ℝ Y]
    (ℓ : SchwartzMap Y ℂ →L[ℂ] ℂ),
    (∀ L : Y →ₗ[ℝ] ℝ, ∀ f g : SchwartzMap Y ℂ, ⇑g = (fun x => GlobalTheory.ArchSch.ech (L x) * f x) → ℓ g = ℓ f) →
    ∀ f g : SchwartzMap Y ℂ, f 0 = g 0 → ℓ f = ℓ g := by
  first | exact @GlobalTheory.CharInvAtZero.eq_of_eq_zero | exact GlobalTheory.CharInvAtZero.eq_of_eq_zero | (intros; apply GlobalTheory.CharInvAtZero.eq_of_eq_zero <;> assumption)
end

