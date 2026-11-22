import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0331
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0040
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0042
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Formalism.PairingDivisors.StatementH
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.OddnessConditionHolds
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0329
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0288

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.SkewHermitianAdelicCoverOfAdeleCover
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.UG GlobalTheory.Doubling GlobalTheory.Eis.Conv

noncomputable section

namespace GlobalTheory.Eis.Conv.CovSkew

theorem exists_delta (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (h : IsCMExt F E σ) :
    ∃ δ : E, σ δ = -δ ∧ ∀ z : E, ∃ a b : F, z = a • (1 : E) + b • δ := by
  obtain ⟨-, hc, h2, hσ⟩ := h
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  have hnr : ¬ ComplexEmbedding.IsReal τ := IsTotallyComplex.complexEmbedding_not_isReal τ
  obtain ⟨x, hx⟩ : ∃ x, star (τ x) ≠ τ x := by
    by_contra hcon
    push Not at hcon
    apply hnr
    rw [ComplexEmbedding.isReal_iff]
    ext x
    exact hcon x
  have hδ : σ (x - σ x) = -(x - σ x) := by
    apply τ.injective
    rw [hσ, map_neg, map_sub, hσ, star_sub, star_star, neg_sub]
  have h0 : x - σ x ≠ 0 := by
    intro h0
    apply hx
    rw [← hσ, ← sub_eq_zero.mp h0]
  refine ⟨x - σ x, hδ, ?_⟩
  generalize x - σ x = δ at hδ h0
  have hli : LinearIndependent F ![(1 : E), δ] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    have h1 := congrArg σ hst
    have hsm : ∀ (a : F) (z : E), σ (a • z) = a • σ z := fun a z => σ.toLinearMap.map_smul a z
    rw [map_add, hsm, hsm, map_one, hδ, map_zero, smul_neg] at h1
    have hs : (2 * s) • (1 : E) = 0 := by
      rw [two_mul, add_smul]; linear_combination hst + h1
    have hs0 : s = 0 := by simpa using hs
    refine ⟨hs0, ?_⟩
    rw [hs0, zero_smul, zero_add] at hst
    exact (smul_eq_zero.mp hst).resolve_right h0
  intro z
  have hsp := hli.span_eq_top_of_card_eq_finrank' (by simp [h2])
  have hz : z ∈ Submodule.span F (Set.range ![(1 : E), δ]) := by rw [hsp]; trivial
  rw [Matrix.range_cons, Matrix.range_cons, Matrix.range_empty, Set.union_empty,
    Set.singleton_union, Submodule.mem_span_pair] at hz
  obtain ⟨a, b, hab⟩ := hz
  exact ⟨a, b, hab.symm⟩

section
variable {F E : Type} [Field F] [Field E] [Algebra F E] {R : Type} [CommRing R] [Algebra F R]

theorem exists_coords (δ : E) (h : ∀ z : E, ∃ a b : F, z = a • (1 : E) + b • δ) (z : R ⊗[F] E) :
    ∃ u v : R, z = u ⊗ₜ[F] (1 : E) + v ⊗ₜ[F] δ := by
  induction z with
  | zero => exact ⟨0, 0, by simp⟩
  | tmul r e =>
    obtain ⟨a, b, rfl⟩ := h e
    exact ⟨a • r, b • r, by
      rw [TensorProduct.tmul_add, TensorProduct.smul_tmul, TensorProduct.smul_tmul]⟩
  | add x y hx hy =>
    obtain ⟨u, v, rfl⟩ := hx
    obtain ⟨u', v', rfl⟩ := hy
    exact ⟨u + u', v + v', by simp only [TensorProduct.add_tmul]; abel⟩

def psi (δ : E) (a a' : R) : R ⊗[F] E := (a - a') • (1 : R ⊗[F] E) + (a + a') • ((1 : R) ⊗ₜ[F] δ)

theorem psi_eq (δ : E) (a a' : R) :
    psi δ a a' = (a - a') ⊗ₜ[F] (1 : E) + (a + a') ⊗ₜ[F] δ := by
  simp [psi, Algebra.TensorProduct.one_def, TensorProduct.smul_tmul']

theorem exists_psi [CharZero F] (σ : E →ₐ[F] E) (δ : E) (hδ : σ δ = -δ)
    (h : ∀ z : E, ∃ a b : F, z = a • (1 : E) + b • δ) {n : ℕ}
    (S : Matrix (Fin n) (Fin n) (R ⊗[F] E)) (hS : cT (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR R σ) S = -S) :
    ∃ T : Fin n → Fin n → R, ∀ i j, S i j = psi δ (T i j) (T j i) := by
  choose U V hUV using fun i j => exists_coords δ h (S i j)
  set c : R := algebraMap F R 2⁻¹ with hc
  have h2 : 2 * c = 1 := by
    rw [hc, ← map_ofNat (algebraMap F R) 2, ← map_mul, mul_inv_cancel₀ two_ne_zero, map_one]
  refine ⟨fun i j => c * c * (U i j - U j i + V i j + V j i), fun i j => ?_⟩
  have h1 : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR R σ (S j i) = - S i j := congrFun (congrFun hS i) j
  have e1 : ∀ k l, S k l = U k l • (1 : R ⊗[F] E) + V k l • ((1 : R) ⊗ₜ[F] δ) := fun k l => by
    rw [hUV]; simp [Algebra.TensorProduct.one_def, TensorProduct.smul_tmul']
  have e2 : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR R σ (S j i)
      = U j i • (1 : R ⊗[F] E) - V j i • ((1 : R) ⊗ₜ[F] δ) := by
    rw [hUV, map_add]
    change U j i ⊗ₜ[F] σ 1 + V j i ⊗ₜ[F] σ δ = _
    simp [hδ, Algebra.TensorProduct.one_def, TensorProduct.smul_tmul', TensorProduct.tmul_neg,
      sub_eq_add_neg]
  rw [e2] at h1
  have e3 := e1 i j
  have h2' : 2 * algebraMap R (R ⊗[F] E) c = 1 := by
    rw [← map_ofNat (algebraMap R (R ⊗[F] E)) 2, ← map_mul, h2, map_one]
  unfold psi
  simp only [Algebra.smul_def, map_add, map_sub, map_mul] at h1 e3 ⊢
  generalize algebraMap R (R ⊗[F] E) = f at *
  generalize ((1 : R) ⊗ₜ[F] δ) = d at *
  linear_combination (f c) * e3 + (f c) * h1 - S i j * h2'
    - f c * (f (U i j) - f (U j i) + (f (V i j) + f (V j i)) * d) * h2'

theorem psi_split (δ : E) (x x' : F) (y y' t w w' : R) :
    psi δ (algebraMap F R x + y + t * w) (algebraMap F R x' + y' + t * w')
      = inclR (F := F) R ((x - x') • (1 : E) + (x + x') • δ) + psi δ y y'
        + algebraMap R (R ⊗[F] E) t * psi δ w w' := by
  have : inclR (F := F) R ((x - x') • (1 : E) + (x + x') • δ)
      = psi δ (algebraMap F R x) (algebraMap F R x') := by
    rw [psi_eq, ← map_sub, ← map_add, Algebra.algebraMap_eq_smul_one,
      Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul, TensorProduct.smul_tmul,
      ← TensorProduct.tmul_add]
    rfl
  rw [this]
  unfold psi
  simp only [Algebra.smul_def, map_add, map_sub, map_mul]
  ring

end

theorem cover_skew : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (b C₀ : ℝ) (Ω₀ : Set (AF F)), IsCompact Ω₀ → (∀ m : ℕ, ∃ Y : Finset (AF F), (Y.card : ℝ) ≤ C₀ * b ^ m ∧ ∀ a : AF F, ∃ x : F, ∃ y ∈ Y, ∃ ω ∈ Ω₀, a = algebraMap F (AF F) x + y + (halfInf F).1 ^ m * ω) → ∀ n : ℕ, ∃ (Ω : Set (AF F ⊗[F] E)) (C : ℝ), IsCompact Ω ∧ ∀ m : Fin n → ℕ, ∃ Y : Finset (Matrix (Fin n) (Fin n) (AF F ⊗[F] E)), (Y.card : ℝ) ≤ C * ∏ i, (b ^ 2) ^ (n * m i) ∧ ∀ S : Matrix (Fin n) (Fin n) (AF F ⊗[F] E), cT (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (AF F) σ) S = -S → ∃ S₀ : Matrix (Fin n) (Fin n) E, ∃ y ∈ Y, ∃ ω : Matrix (Fin n) (Fin n) (AF F ⊗[F] E), (∀ i j, ω i j ∈ Ω) ∧ S = S₀.map (inclR (F := F) (AF F)) + y + Matrix.diagonal (fun i => (halfE F E).1 ^ m i) * ω * Matrix.diagonal (fun i => (halfE F E).1 ^ m i) := by
  intro F E _ _ _ _ _ σ hσ b C₀ Ω₀ hΩ₀ hcov n
  classical
  obtain ⟨δ, hδ, hsp⟩ := exists_delta F E σ hσ
  choose Y hY hYc using hcov
  have : IsModuleTopology (AF F) (AF F ⊗[F] E) := ⟨rfl⟩
  have : IsTopologicalRing (AF F ⊗[F] E) := isTopologicalRing_tens
  have hcont : Continuous fun p : AF F × AF F => psi (F := F) δ p.1 p.2 := by
    unfold psi
    fun_prop
  refine ⟨_, C₀ ^ (n * n), (hΩ₀.prod hΩ₀).image hcont, fun m => ?_⟩
  refine ⟨(Fintype.piFinset fun p : Fin n × Fin n => Y (m p.1 + m p.2)).image
    (fun y => Matrix.of fun i j => psi δ (y (i, j)) (y (j, i))), ?_, fun S hS => ?_⟩
  · refine (Nat.cast_le.mpr Finset.card_image_le).trans ?_
    rw [Fintype.card_piFinset, Nat.cast_prod]
    refine (Finset.prod_le_prod (fun _ _ => Nat.cast_nonneg _) (fun p _ => hY _)).trans (le_of_eq ?_)
    rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_prod,
      Fintype.card_fin, Finset.prod_pow_eq_pow_sum]
    congr 1
    simp only [← pow_mul]
    rw [Finset.prod_pow_eq_pow_sum, Fintype.sum_prod_type]
    congr 1
    simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      smul_eq_mul, ← Finset.mul_sum]
    ring
  · obtain ⟨T, hT⟩ := exists_psi σ δ hδ hsp S hS
    choose x y hy ω hω hTe using fun i j => hYc (m i + m j) (T i j)
    refine ⟨Matrix.of fun i j => (x i j - x j i) • (1 : E) + (x i j + x j i) • δ, _,
      Finset.mem_image.mpr ⟨fun p => y p.1 p.2, Fintype.mem_piFinset.mpr fun p => hy _ _, rfl⟩,
      Matrix.of fun i j => psi δ (ω i j) (ω j i),
      fun i j => ⟨(ω i j, ω j i), ⟨hω _ _, hω _ _⟩, rfl⟩, ?_⟩
    ext i j
    rw [Matrix.add_apply, Matrix.add_apply, Matrix.mul_diagonal, Matrix.diagonal_mul, hT,
      hTe i j, hTe j i, add_comm (m j) (m i), psi_split]
    have : (halfE F E).1 = algebraMap (AF F) (AF F ⊗[F] E) (halfInf F).1 := rfl
    rw [this, map_pow]
    simp only [Matrix.map_apply, Matrix.of_apply]
    ring

end GlobalTheory.Eis.Conv.CovSkew

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.WeilOperatorVacuumExactConstantEvenRank
section
noncomputable section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.VacuumScalar
open scoped BigOperators

namespace GlobalTheory.VacuumExact

variable {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} {N N' : ℕ}

theorem exists_scalar (hc : Crv D cc δ) {e0 : VC D N N' → ℂ}
    (he : e0 ∈ Th D (tor0 D cc δ) (stdL D N) (stdL D N')) (W : WeilO D cc δ N N' e0) {g : GA D N} {g' : GA D N'}
    {L L'} (hL : Moves D (g : GL (Fin N) (AE D)) L) (hL' : Moves D (g' : GL (Fin N') (AE D)) L') :
    ∃ c : ℂ, W.Om g g' e0 = c • Iop D (tor0 D cc δ) (La0 D (tor0 D cc δ) N N') (La D (tor0 D cc δ) L L') e0 := by
  have hg1 := (GlobalTheory.InducedType.induced_type D).1
  have k0 : KLat D (tor0 D cc δ) (La0 D (tor0 D cc δ) N N') :=
    Or.inr ⟨_, _, sd_of_moves (moves_one D N), sd_of_moves (moves_one D N'), rfl⟩
  have k1 : KLat D (tor0 D cc δ) (La D (tor0 D cc δ) L L') := Or.inr ⟨_, _, sd_of_moves hL, sd_of_moves hL', rfl⟩
  obtain ⟨-, hTh, -, -⟩ := GlobalTheory.T.intertwinerUnitary_all D cc δ hc N N' _ _ k0 k1 e0 he
  obtain ⟨hline, w1, -⟩ := GlobalTheory.T.theta_space_selfDual_pair_at_most_line D hg1 cc δ hc N N' _ k1
  obtain ⟨a1, -, a3, a4, -, a6, -⟩ := lattice_facts hc he W.nz hL hL'
  have heT : e0 ∈ TT D (tor0 D cc δ) N N' := ⟨he.1, 1, one_pos, fun y hy => by rw [one_smul]; exact a6 y hy⟩
  have hGT := W.maps g g' e0 heT
  have hinv : ∀ F ∈ TT D (tor0 D cc δ) N N', W.Om g g' (W.Om g⁻¹ g'⁻¹ F) = F := by
    intro F hF
    rw [← W.mul _ _ _ _ _ hF, mul_inv_cancel, mul_inv_cancel, W.one F hF]
  have hinv' : W.Om g⁻¹ g'⁻¹ (W.Om g g' e0) = e0 := by
    rw [← W.mul _ _ _ _ _ heT, inv_mul_cancel, inv_mul_cancel, W.one e0 heT]
  refine hline _ ⟨hGT.1, fun x hx z => ?_⟩ _ hTh a1
  have hWT : Wd D (tor0 D cc δ) x (W.Om g g' e0) ∈ TT D (tor0 D cc δ) N N' := by
    obtain ⟨hd, m, hm, hfix⟩ := hGT
    refine ⟨Wd_differentiable _ hd, (La D (tor0 D cc δ) L L').relIndex (La0 D (tor0 D cc δ) N N') * m,
      Nat.mul_pos (Nat.pos_of_ne_zero a4) hm, fun y hy => ?_⟩
    have h1 := AddSubgroup.nsmul_relIndex_mem (La D (tor0 D cc δ) L L') hy
    have h2 := (La D (tor0 D cc δ) L L').nsmul_mem h1 m
    have h3 := hfix _ ((La0 D (tor0 D cc δ) N N').nsmul_mem hy
      ((La D (tor0 D cc δ) L L').relIndex (La0 D (tor0 D cc δ) N N')))
    rw [smul_smul, mul_comm] at h2 h3
    rw [← Wl_apply, ← Wl_apply, ← Module.End.mul_apply, ← a3 _ h2 _ hx, add_comm, a3 _ hx _ h2,
      Module.End.mul_apply, Wl_apply _ (W.Om g g' e0), h3]
  obtain ⟨x0, hx0, hW⟩ := GlobalTheory.T.weilOperator_conj_heisenberg_moved_lattice D hg1 cc δ hc.1.1 N N' e0 W g⁻¹ g g'⁻¹ g' L _ L' _ hL hL'
    (by rw [inv_mul_cancel]; exact moves_one D N) (by rw [inv_mul_cancel]; exact moves_one D N') x hx _ hGT
  rw [hinv', ← Wl_apply x0, a6 x0 hx0] at hW
  have h := hinv _ hWT
  rw [hW, w1 x hx] at h
  exact (congrFun h z).symm

theorem split_part {e : AE D} (h1 : e * e = e) (h2 : sgA D e = e)
    (h3 : ∀ q : ℕ, q.Prime → (InertQ D q → ZeroAt D q e) ∧ (¬ InertQ D q → ZeroAt D q (1 - e)))
    (g : GA D N) {x : (AE D)ˣ} (hx : x = Matrix.GeneralLinearGroup.det (g : GL (Fin N) (AE D)) * sgU D x) :
    ∃ y : (AE D)ˣ, (∀ q : ℕ, q.Prime → InertQ D q → ZeroAt D q ((y : AE D) - 1)) ∧
      y = Matrix.GeneralLinearGroup.det ((cutG e h1 h2 g : GA D N) : GL (Fin N) (AE D)) * sgU D y ∧
      ∀ {n : ℕ} (χ : HeckeU D n), Even n → χ.f y = χ.f x := by
  set d : AE D := ((Matrix.GeneralLinearGroup.det (g : GL (Fin N) (AE D)) : (AE D)ˣ) : AE D) with hdef
  have hxv : (x : AE D) = d * sgA D x := congrArg Units.val hx
  refine ⟨Units.map (cut e h1) x, fun q hq hi => ?_, Units.ext ?_, fun χ hn => ?_⟩
  · convert VacMove.zeroAt_mul D hq ((h3 q hq).1 hi) (x - 1) using 1
    change e * x + (1 - e) * 1 - 1 = _
    ring
  · rw [Units.val_mul, det_cutG, ← hdef]
    change e * x + (1 - e) * 1 = _ * sgA D (e * x + (1 - e) * 1)
    rw [map_add, map_mul, map_mul, map_sub, map_one, h2]
    linear_combination e * hxv + ((d - 1) * (1 - sgA D x)) * h1
  · have hsplit : x = Units.map (cut e h1) x * Units.map (cut (1 - e) (compl_idem h1)) x :=
      Units.ext (cut_mul_cut e h1 (x : AE D)).1.symm
    have htriv : χ.f (Units.map (cut (1 - e) (compl_idem h1)) x) = 1 := by
      refine GlobalTheory.T.hecke_character_trivial_near_one D _ hn χ _ fun q hq hi => ?_
      convert VacMove.zeroAt_mul D hq ((h3 q hq).2 hi) (x - 1) using 1
      change (1 - e) * x + (1 - (1 - e)) * 1 - 1 = _
      ring
    conv_rhs => rw [hsplit, map_mul, htriv, mul_one]

theorem vacuum_exact : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ), Crv D cc δ → ∀ (N N' : ℕ), Even N → Even N' → ∀ e0 ∈ Th D (tor0 D cc δ) (stdL D N) (stdL D N'), ∀ (W : WeilO D cc δ N N' e0) (g : GA D N) (g' : GA D N') (x x' : (AE D)ˣ) (L₁ : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (L₁' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)), x = Matrix.GeneralLinearGroup.det (g : GL (Fin N) (AE D)) * sgU D x → x' = Matrix.GeneralLinearGroup.det (g' : GL (Fin N') (AE D)) * sgU D x' → Moves D (g : GL (Fin N) (AE D)) L₁ → Moves D (g' : GL (Fin N') (AE D)) L₁' → W.Om g g' e0 = fun z => ((W.chV.f x' ^ W.ep * W.chV'.f x ^ W.ep' : ℂˣ) : ℂ) * Iop D (tor0 D cc δ) (La0 D (tor0 D cc δ) N N') (La D (tor0 D cc δ) L₁ L₁') e0 z := by
  intro D cc δ hc N N' hN hN' e0 he W g g' x x' L L' hx hx' hL hL'
  obtain ⟨ε, -, a1, a2, h3⟩ := VacMove.exists_half_idem D
  have h1 : (ε + sgA D ε) * (ε + sgA D ε) = ε + sgA D ε := by
    have a3 : sgA D ε * sgA D ε = sgA D ε := by rw [← map_mul, a1]
    linear_combination a1 + a3 + 2 * a2
  have h2 : sgA D (ε + sgA D ε) = ε + sgA D ε := by rw [map_add, VacMove.sgA_sgA, add_comm]
  generalize ε + sgA D ε = e at h1 h2 h3
  obtain ⟨y, b1, b2, b3⟩ := split_part h1 h2 h3 g hx
  obtain ⟨y', c1, c2, c3⟩ := split_part h1 h2 h3 g' hx'
  obtain ⟨c, hO⟩ := exists_scalar hc he W hL hL'
  obtain ⟨Ls, hLs⟩ := exists_moves (cutG e h1 h2 g)
  obtain ⟨Ls', hLs'⟩ := exists_moves (cutG e h1 h2 g')
  obtain ⟨Li, hLi⟩ := exists_moves (cutG (1 - e) (compl_idem h1) (compl_fixed h2) g)
  obtain ⟨Li', hLi'⟩ := exists_moves (cutG (1 - e) (compl_idem h1) (compl_fixed h2) g')
  have hs : ∀ {n : ℕ} (k : GA D n), SuppSplit D ((cutG e h1 h2 k : GA D n) : GL (Fin n) (AE D)) :=
    fun k q hq hi => trivAt_cutG hq _ _ _ k ((h3 q hq).1 hi)
  have hi : ∀ {n : ℕ} (k : GA D n),
      SuppInert D ((cutG (1 - e) (compl_idem h1) (compl_fixed h2) k : GA D n) : GL (Fin n) (AE D)) :=
    fun k q hq hi => trivAt_cutG hq _ _ _ k ((h3 q hq).2 hi)
  have hcc := scalar_mul hc he W (cutG_mul e h1 h2 g).1 (cutG_mul e h1 h2 g).2 (cutG_mul e h1 h2 g').1
    (cutG_mul e h1 h2 g').2 (hs g) (hs g') (hi g) (hi g') hL hL' hLs hLs' hLi hLi' hO
    (W.split _ _ y y' Ls Ls' (hs g) (hs g') (fun q hq h => ⟨b1 q hq h, c1 q hq h⟩) b2 c2 hLs hLs')
    (GlobalTheory.T.weilRepresentation_vacuum_sign_inert_places D cc δ hc N N' (hN.mul_right N') e0 he W _ _ Li Li' (hi g) (hi g') hLi hLi')
  rw [Even.neg_one_pow ((hN.mul_right _).add (hN'.mul_right _)), one_mul, b3 _ hN', c3 _ hN] at hcc
  rw [hO, hcc]
  rfl

end GlobalTheory.VacuumExact
end
end

