import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HermSysHypOneLeLambdaZero
import ReciprocityTheory.SemistableReduction.Bundle0025
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0053
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsSmoothModerateOfIsAutFunSm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1335
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0052
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0004
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0982
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0949
import CompanionTheory.HarishChandraModules.LowKTypeMultiplicity.EigenspaceCyclicDensity.LowKMultOneP
import CompanionTheory.HarishChandraModules.LowKTypeMultiplicity.DiscreteSeriesCharacters.DiscreteSeriesInfinitesimalCharacter
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HolomorphicDiscreteSeries
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1326
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0074
import Formalism.RealPlaceAnalysis.Bundle0004
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1308
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemNonzeroLocusFormMap
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1336
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1337
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0046
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0005
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0016
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0015
import Development.AbelianVarietyTheory.Definitions.Divisors.IsDominantOfSection
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1271
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1338
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1193
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsClosedImmersionGenericPoint

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinearIndependentOfFiltrationSymbolDetNeZero
section
open NumberField MvPolynomial ReciprocityTheory.MultiplicativeHeights ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.ChowHt GlobalTheory.Adelic GlobalTheory.HermTools GlobalTheory.HilbertSamuel GlobalTheory.HSChoice GlobalTheory.HSShort

namespace GlobalTheory.HSShort

theorem linearIndependent_of_symbol_det_ne_zero :
    ∀ (E A' : Type) [Field E] [AddCommGroup A'] [Module E A'] (r d : ℕ) (I : Fin r → Type) [∀ a, Fintype (I a)] [∀ a, DecidableEq (I a)] (U : ℕ → Submodule E A') (sym : ∀ a : Fin r, U a →ₗ[E] (I a → E)), (∀ a < r, U (a + 1) ≤ U a) → (∀ (a : Fin r) (x : U a), sym a x = 0 ↔ x.1 ∈ U (a + 1)) → ∀ (ix : (Σ a, I a) ↪ Fin d) (J : Finset (Fin d)) (v : Fin d → A') (hv : ∀ q, v (ix q) ∈ U q.1), (∀ k ∈ J, k ∉ Set.range ix ∧ v k ∈ U r) → (∀ a, (Matrix.of fun i i' : I a => sym a ⟨v (ix ⟨a, i'⟩), hv ⟨a, i'⟩⟩ i).det ≠ 0) → LinearIndependent E (fun k : J => v k) → LinearIndependent E fun k : {k // k ∈ Set.range ix ∨ k ∈ J} => v k := by
  classical
  intro E A' _ _ _ r d I _ _ U sym hmono hker ix J v hv hJ hdet hJli
  have hle : ∀ b c : ℕ, b ≤ c → c ≤ r → U c ≤ U b := by
    intro b c hbc hcr
    induction c, hbc using Nat.le_induction with
    | base => exact le_rfl
    | succ c hbc ih => exact (hmono c (by omega)).trans (ih (by omega))
  let h : (Σ a, I a) ⊕ J → Fin d := Sum.elim ix (fun k => k.1)
  have hinj : Function.Injective h := by
    rintro (q|k) (q'|k') heq
    · exact congrArg Sum.inl (ix.injective heq)
    · exact ((hJ _ k'.2).1 ⟨q, heq⟩).elim
    · exact ((hJ _ k.2).1 ⟨q', heq.symm⟩).elim
    · exact congrArg Sum.inr (Subtype.ext heq)
  let e : (Σ a, I a) ⊕ J → {k // k ∈ Set.range ix ∨ k ∈ J} := fun x =>
    ⟨h x, by rcases x with q | k; exacts [Or.inl ⟨q, rfl⟩, Or.inr k.2]⟩
  have hb : Function.Bijective e := by
    refine ⟨fun x y hxy => hinj (congrArg Subtype.val hxy), ?_⟩
    rintro ⟨k, hk | hk⟩
    · obtain ⟨q, rfl⟩ := hk
      exact ⟨Sum.inl q, rfl⟩
    · exact ⟨Sum.inr ⟨k, hk⟩, rfl⟩
  have key : LinearIndependent E (fun x : (Σ a, I a) ⊕ J => v (h x)) := by
    rw [Fintype.linearIndependent_iff]
    intro g hg
    have hg' : (∑ q, g (Sum.inl q) • v (ix q)) + ∑ k : J, g (Sum.inr k) • v k = 0 := by
      rw [Fintype.sum_sum_type] at hg; exact hg
    have hA : ∀ n, ∀ a : Fin r, (a : ℕ) = n → ∀ i, g (Sum.inl ⟨a, i⟩) = 0 := by
      intro n
      induction n using Nat.strong_induction_on with
      | _ n ih =>
      intro a ha i
      subst ha
      obtain ⟨G, hG⟩ := LinearMap.exists_extend (sym a)
      have hGv : ∀ x (hx : x ∈ U a), G x = sym a ⟨x, hx⟩ := fun x hx =>
        LinearMap.congr_fun hG ⟨x, hx⟩
      have hker' : ∀ x ∈ U ((a : ℕ) + 1), G x = 0 := fun x hx => by
        rw [hGv x (hmono a a.isLt hx)]
        exact (hker a ⟨x, _⟩).mpr hx
      have hJ0 : ∑ k : J, g (Sum.inr k) • G (v k) = 0 :=
        Finset.sum_eq_zero fun k _ => by
          rw [hker' _ (hle ((a : ℕ) + 1) r (by have := a.isLt; omega) le_rfl (hJ k.1 k.2).2), smul_zero]
      have hS : ∑ q : (Σ b, I b), g (Sum.inl q) • G (v (ix q))
          = ∑ i : I a, g (Sum.inl ⟨a, i⟩) • sym a ⟨v (ix ⟨a, i⟩), hv ⟨a, i⟩⟩ := by
        rw [Fintype.sum_sigma, Finset.sum_eq_single a]
        · exact Finset.sum_congr rfl fun i _ => by rw [hGv]
        · intro b _ hba
          apply Finset.sum_eq_zero
          intro i _
          rcases lt_or_gt_of_ne hba with hlt | hlt
          · rw [ih b (Fin.lt_iff_val_lt_val.mp hlt) b rfl i, zero_smul]
          · have h1 := Fin.lt_iff_val_lt_val.mp hlt
            have h2 := b.isLt
            rw [hker' _ (hle ((a : ℕ) + 1) (b : ℕ) (by omega) (by omega) (hv ⟨b, i⟩)), smul_zero]
        · intro hn; exact absurd (Finset.mem_univ a) hn
      have hGg := congrArg G hg'
      simp only [map_add, map_sum, map_smul, map_zero] at hGg
      rw [hS, hJ0, add_zero] at hGg
      have hM : Matrix.mulVec (Matrix.of fun i i' : I a => sym a ⟨v (ix ⟨a, i'⟩), hv ⟨a, i'⟩⟩ i)
          (fun i' => g (Sum.inl ⟨a, i'⟩)) = 0 := by
        funext j
        have hj := congrFun hGg j
        simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at hj
        simp only [Matrix.mulVec, dotProduct, Matrix.of_apply, Pi.zero_apply]
        rw [← hj]; exact Finset.sum_congr rfl fun _ _ => mul_comm _ _
      exact congrFun (Matrix.eq_zero_of_mulVec_eq_zero (hdet a) hM) i
    have hJs : ∑ k : J, g (Sum.inr k) • v k = 0 := by
      have h0 : ∑ q : (Σ a, I a), g (Sum.inl q) • v (ix q) = 0 :=
        Finset.sum_eq_zero fun ⟨b, i⟩ _ => by rw [hA _ b rfl i, zero_smul]
      rw [h0, zero_add] at hg'; exact hg'
    rintro (⟨b, i⟩ | k)
    · exact hA _ b rfl i
    · exact Fintype.linearIndependent_iff.mp hJli (fun k => g (Sum.inr k)) hJs k
  refine (linearIndependent_equiv (Equiv.ofBijective e hb)).mp ?_
  exact key

end GlobalTheory.HSShort
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinearIndependentSiegelCols
section
noncomputable section

open scoped Matrix NNReal TensorProduct Classical
open MeasureTheory NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.Eis GlobalTheory.MixModel GlobalTheory.RegSW
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FirstTermIsoCst

def siegelCols (D : D7) (n : ℕ) : Matrix (Fin (n + n)) (Fin n) D.host.E :=
  Matrix.of fun i j => if i = finSumFinEquiv (Sum.inl j) then 1 else 0

variable (D : D7) {n : ℕ}

theorem siegelCols_castAdd (i j : Fin n) : siegelCols D n (Fin.castAdd n i) j = if i = j then 1 else 0 := by
  simp [siegelCols, Fin.castAdd_inj]

theorem siegelCols_natAdd (i j : Fin n) : siegelCols D n (Fin.natAdd n i) j = 0 := by
  simp [siegelCols, Fin.ext_iff]
  omega

theorem jst_cc (i k : Fin n) : StdUnn.Jst D n (Fin.castAdd n i) (Fin.castAdd n k) = 0 := by
  simp only [StdUnn.Jst, StdUnn.blk4, Matrix.submatrix_apply]
  rw [show finSumFinEquiv.symm (Fin.castAdd n i) = Sum.inl i from finSumFinEquiv_symm_apply_castAdd i,
    show finSumFinEquiv.symm (Fin.castAdd n k) = Sum.inl k from finSumFinEquiv_symm_apply_castAdd k]
  simp

theorem linearIndependent_siegelCols : LinearIndependent D.host.E (siegelCols D n).transpose := by
  change LinearIndependent D.host.E (fun j i => siegelCols D n i j)
  refine Fintype.linearIndependent_iff.2 fun c hc j => ?_
  have := congrFun hc (Fin.castAdd n j)
  simpa [Finset.sum_apply, Matrix.transpose_apply, siegelCols_castAdd, eq_comm] using this

theorem siegelCols_isotropic :
    Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) (siegelCols D n) * StdUnn.Jst D n * siegelCols D n = 0 := by
  ext i j
  simp only [Matrix.mul_apply, Fin.sum_univ_add, Formalism.UG.cT, Matrix.transpose_apply, Matrix.map_apply, siegelCols_castAdd,
    siegelCols_natAdd, jst_cc, map_zero, zero_mul, mul_zero, Finset.sum_const_zero, add_zero, zero_add]
  simp

end GlobalTheory.FirstTermIsoCst

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinearSystemRelationOfGenericPointStatement
section
open NumberField MvPolynomial ReciprocityTheory.MultiplicativeHeights GlobalTheory GlobalTheory.ChowHt GlobalTheory.Adelic GlobalTheory.HSCore GlobalTheory.HSChoice
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.linearSystem_relation_of_generic_point : ∀ (F : Type) [Field F] (S : LinSys F), AlgebraicGeometry.IsIntegral S.Y → ∀ (r e : ℕ) (u : Fin r → Fin S.N → F) (th : (lbPow S.L e).Sec) (η : S.Y), IsGenericPoint η Set.univ → ∀ (m : ℕ) (a : Fin m → MvPolynomial (Fin r) F), (∀ k, (a k).IsHomogeneous (e * (m - k))) → S.powVal (resPt η) th ^ m + ∑ k, MvPolynomial.eval₂ (S.baseHom (resPt η)) (fun i => S.val (resPt η) (S.comb (u i))) (a k) * S.powVal (resPt η) th ^ (k : ℕ) = 0 → ∀ (K : Type) [Field K] [Algebra F K] (x : S.Pt K), S.powVal x.1 th ^ m + ∑ k, aeval (fun i => ∑ j, algebraMap F K (u i j) * S.coords x.1 j) (a k) * S.powVal x.1 th ^ (k : ℕ) = 0 := by
  first | exact @GlobalTheory.Adelic.GenericRel.relation_of_generic | exact GlobalTheory.Adelic.GenericRel.relation_of_generic | (intros; apply GlobalTheory.Adelic.GenericRel.relation_of_generic <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogEvalSubLeBlockSphereMeanMultidegree
section
set_option autoImplicit false

noncomputable section

open NumberField MvPolynomial ReciprocityTheory.MultiplicativeHeights ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.ChowHt GlobalTheory.Adelic GlobalTheory.HermTools GlobalTheory.HilbertSamuel GlobalTheory.HSChoice GlobalTheory.HSShort

namespace GlobalTheory.LelongBlocksMulti

theorem log_eval_sub_le_blockSphereMean : ∀ (B N : ℕ) (a : Fin B → ℕ) (A : Matrix (Fin N) (Fin N) ℂ) (h : MvPolynomial (Fin B × Fin N) ℂ), A.det ≠ 0 → IsMultiHomogeneous a h → ∀ p : Fin B × Fin N → ℂ, (∀ i, frameNorm A (fun j => p (i, j)) = 1) → eval p h ≠ 0 → Real.log ‖eval p h‖ - (∑ i, (a i : ℝ)) * (harmonic (N - 1) : ℝ) / 2 ≤ blockSphereMean B N (linSubst A h) := by
  intro B N a A h hA hh p hp hne
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · rcases Nat.eq_zero_or_pos B with rfl | hB
    · have hev : ∀ z : BlockSphere 0 0, eval (blockPoint z) (linSubst A h) = eval p h := by
        intro z
        rw [GlobalTheory.SphereMeanFrame.eval_linSubst]
        refine congrArg (fun v => eval v h) (funext fun x => ?_)
        exact x.2.elim0
      have hc : (fun z : BlockSphere 0 0 => Real.log ‖eval (blockPoint z) (linSubst A h)‖) =
          fun _ => Real.log ‖eval p h‖ := funext fun z => by rw [hev z]
      unfold blockSphereMean blockSphereProb
      rw [hc, MeasureTheory.Measure.pi_of_empty _ (fun i => i.elim0)]
      simp
    · have := hp ⟨0, hB⟩
      simp [frameNorm] at this
  · let q : Fin B → Fin N → ℂ := fun i => A⁻¹.mulVec (fun j => p (i, j))
    have hq : ∀ i, ‖(WithLp.toLp 2 (q i) : EuclideanSpace ℂ (Fin N))‖ = 1 := by
      intro i
      rw [EuclideanSpace.norm_eq]
      exact hp i
    let u : BlockSphere B N := fun i =>
      ⟨WithLp.toLp 2 (q i), mem_sphere_zero_iff_norm.mpr (hq i)⟩
    have hev : eval (blockPoint u) (linSubst A h) = eval p h := by
      rw [GlobalTheory.SphereMeanFrame.eval_linSubst]
      refine congrArg (fun v => eval v h) (funext fun x => ?_)
      obtain ⟨b, j⟩ := x
      have h1 : A.mulVec (q b) = fun j => p (b, j) := by
        simp only [q]
        rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hA.isUnit, Matrix.one_mulVec]
      exact congrFun h1 j
    have key := blockSphere_logMean_bound ReciprocityTheory.MultiplicativeHeights.Closed.sj ReciprocityTheory.MultiplicativeHeights.Closed.sphereLogIntegrable hN B
      a (linSubst A h) u (GlobalTheory.HeightUnique.linSubst_homog A hh) (by rw [hev]; exact hne)
    rw [hev] at key
    calc Real.log ‖eval p h‖ - (∑ i, (a i : ℝ)) * (harmonic (N - 1) : ℝ) / 2
        = Real.log ‖eval p h‖ - (∑ i, (a i : ℝ)) / 2 * (harmonic (N - 1) : ℝ) := by ring
      _ ≤ _ := by push_cast at key ⊢; exact key

end GlobalTheory.LelongBlocksMulti
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LowestKTypeSpaceHolomorphicKModuleKilledStatement
section
open Matrix GlobalTheory.HolDS
open Formalism.REAL (GlRel IsUnitary IsWeight KHighest root Jm inG)
open Formalism.QuantumDeterminants (lowK IsHCParam)
open Formalism.MainNotions.S (IsURepOn IsIrredOn UJset IsKFin IsKTypeOf IsKStableOn IsDS lowKSub vNormSq)
open CompanionTheory.D.DSIC (KRel KUnit KStab IsSmMod)
open CompanionTheory.D.LK (IsKMod IsMin)
open scoped InnerProductSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lowestKTypeSpace_holomorphicKModule_killed : ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (D : Submodule ℂ H) (E : Fin n → Fin n → Module.End ℂ D) (lam : Fin n → ℝ), IsHCParam lam → IsHolChamber ε lam → IsDS ε lam σ → IsKMod ε σ D E → lowKSub ε lam σ ≤ D ∧ KStab ε E ((lowKSub ε lam σ).comap D.subtype) ∧ (lowKSub ε lam σ).comap D.subtype ≠ ⊥ ∧ ∀ a b : Fin n, ε a = true → ε b = false → ∀ x ∈ (lowKSub ε lam σ).comap D.subtype, E b a x = 0 := by
  first | exact @GlobalTheory.HolDS.lowKSub_kMod | exact GlobalTheory.HolDS.lowKSub_kMod | (intros; apply GlobalTheory.HolDS.lowKSub_kMod <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatchingDeterminantRootOfUnity
section
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj Formalism.IndefR.Lev GlobalTheory.IndefiniteRowSideFullHecke.LatticeBasisLifts GlobalTheory.GeoLevel
open GlobalTheory.Member (FinCong IotaOK)
open GlobalTheory.LevelCusp (IsMatch)
open GlobalTheory.Dict (castFr)
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option autoImplicit false

namespace GlobalTheory.GeoLevel

theorem det_mul_cc_det_of_isMatch {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)
    (δ : GL (Fin r) E) (h : IsMatch X X δ) :
    (δ : Matrix (Fin r) (Fin r) E).det * IsCMField.complexConj E (δ : Matrix (Fin r) (Fin r) E).det = 1 := by
  have hm : (δ : Matrix (Fin r) (Fin r) E)ᵀ * X.Gm *
      ((IsCMField.complexConj E : E →+* E).mapMatrix (δ : Matrix (Fin r) (Fin r) E)) = X.Gm := by
    ext i j
    have := h.iso (Pi.single i 1) (Pi.single j 1)
    simp only [herm, cc, Matrix.mulVec_single_one, Matrix.col_apply] at this
    simp only [Pi.single_apply, apply_ite, map_one, map_zero, mul_ite, ite_mul, mul_one, one_mul, mul_zero,
      zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true] at this
    rw [← this]
    simp only [Matrix.mul_apply, Matrix.transpose_apply, RingHom.mapMatrix_apply, Matrix.map_apply,
      Finset.sum_mul]
    rw [Finset.sum_comm]
    rfl
  have hd := congrArg Matrix.det hm
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, ← RingHom.map_det] at hd
  apply mul_left_cancel₀ X.Gm_det
  rw [mul_one]
  refine Eq.trans ?_ hd
  rw [← mul_assoc, mul_comm X.Gm.det]
  rfl

theorem four_dvd_finrank_and_det_eq_pm_one : ∀ (D : D7), 4 ∣ Module.finrank ℚ D.host.E ∧ ∀ (r : ℕ) (X : Data D.host.E r) (δ : GL (Fin r) D.host.E), IsMatch X X δ → (δ : Matrix (Fin r) (Fin r) D.host.E).det = 1 ∨ ∃ m : ℕ, 0 < m ∧ (δ : Matrix (Fin r) (Fin r) D.host.E).det ^ m = 1 := by
  intro D
  refine ⟨?_, fun r X δ h => ?_⟩
  · have hE : Module.finrank ℚ D.host.E = 4 * D.R.n := by
      have h : (Module.finrank ℚ D.host.E : ℝ) = 4 * (D.R.n : ℝ) := by
        rw [D.host.finrank_cmField]
        unfold Ranks.n
        push_cast
        ring
      exact_mod_cast h
    exact ⟨_, hE⟩
  · have h1 := det_mul_cc_det_of_isMatch X δ h
    refine Or.inr (GlobalTheory.Mem.StabDet.eq_pm_one_of_unitary D.host _ ⟨?_, h1⟩
      (GlobalTheory.Mem.StabDet.isIntegral_det X.Λ X.Λ_fg X.Λ_span _ fun v hv => (h.lat v).1 hv))
    rw [mul_comm]
    exact h1

end GlobalTheory.GeoLevel
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatrixCompletionFirstColumnStatement
section
open Matrix GlobalTheory.TorFin

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.matrix_completion_first_column : ∀ (m : ℕ) (v φ : Fin (m + 1) → ℂ), φ ⬝ᵥ v = 1 → ∃ P P' : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ, P * P' = 1 ∧ (∀ i, P i 0 = v i) ∧ ∀ j, P' 0 j = φ j := by
  first | exact @GlobalTheory.frame_first_column_first_row | exact GlobalTheory.frame_first_column_first_row | (intros; apply GlobalTheory.frame_first_column_first_row <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MonomialCountsDegreeAndWeightedSum
section
open NumberField MvPolynomial ReciprocityTheory.MultiplicativeHeights ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.ChowHt GlobalTheory.Adelic GlobalTheory.HermTools GlobalTheory.HilbertSamuel GlobalTheory.HSChoice GlobalTheory.HSShort

namespace GlobalTheory.HSShort

theorem nat_card_monoDeg_fin (D a : ℕ) (hD : 1 ≤ D) :
    Nat.card (MonoDeg (Fin D) a) = (a + D - 1).choose (D - 1) := by
  obtain ⟨d, rfl⟩ : ∃ d, D = d + 1 := ⟨D - 1, by omega⟩
  classical
  rw [Nat.card_eq_fintype_card, MonoDeg.card_eq_card_finsuppAntidiag,
    Finset.card_finsuppAntidiag_nat_eq_choose]
  simp only [Finset.card_univ, Fintype.card_fin]
  rw [show a + (d + 1) - 1 = a + d by omega, show d + 1 + a - 1 = a + d by omega,
    show d + 1 - 1 = d by omega]
  exact Nat.choose_symm_add

theorem sum_range_choose_mul_sub (d n : ℕ) :
    ∑ a ∈ Finset.range n, (a + d).choose d * (n - a) = (n + d + 1).choose (d + 2) := by
  induction n with
  | zero => simp [Nat.choose_eq_zero_of_lt]
  | succ n ih =>
    have h1 : ∑ a ∈ Finset.range n, (a + d).choose d * (n + 1 - a) =
        ∑ a ∈ Finset.range n, (a + d).choose d * (n - a) +
          ∑ a ∈ Finset.range n, (a + d).choose d := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun a ha => ?_
      have : a < n := Finset.mem_range.mp ha
      rw [show n + 1 - a = (n - a) + 1 by omega, Nat.mul_succ]
    rw [Finset.sum_range_succ, h1, ih, show n + 1 - n = 1 by omega, mul_one, add_assoc,
      ← Finset.sum_range_succ, Nat.sum_range_add_choose,
      show n + 1 + d + 1 = (n + d + 1) + 1 by omega, Nat.choose_succ_succ' (n + d + 1) (d + 1)]
    ring_nf

theorem monomial_counts : ∀ D T : ℕ, 1 ≤ D → D + 1 ≤ T →
    (∀ a : ℕ, Nat.card (MonoDeg (Fin D) a) = (a + D - 1).choose (D - 1)) ∧
    Nat.card (Σ a : Fin (T - D), MonoDeg (Fin D) a) = (T - 1).choose D ∧
    (D + 1) * ∑ a ∈ Finset.range (T - D), (a + D - 1).choose (D - 1) * (T - a) =
      (T - 1).choose D * (T + D * (D + 1)) := by
  intro D T hD hT
  have h1 := fun a => nat_card_monoDeg_fin D a hD
  obtain ⟨d, rfl⟩ : ∃ d, D = d + 1 := ⟨D - 1, by omega⟩
  obtain ⟨m, rfl⟩ : ∃ m, T = d + 2 + m := ⟨T - (d + 2), by omega⟩
  have hTD : d + 2 + m - (d + 1) = m + 1 := by omega
  have hT1 : d + 2 + m - 1 = m + d + 1 := by omega
  have hsub : ∀ a, a + (d + 1) - 1 = a + d := fun a => by omega
  simp only [hsub, show d + 1 - 1 = d by omega] at h1 ⊢
  have hsum : ∑ a ∈ Finset.range (m + 1), (a + d).choose d = (m + d + 1).choose (d + 1) :=
    Nat.sum_range_add_choose m d
  refine ⟨h1, ?_, ?_⟩
  · rw [Nat.card_sigma, hT1]
    simp only [h1]
    rw [← hsum, hTD, Finset.sum_range (fun a => (a + d).choose d)]
  · rw [hTD, hT1]
    have hw : ∑ a ∈ Finset.range (m + 1), (a + d).choose d * (d + 2 + m - a) =
        ∑ a ∈ Finset.range (m + 1), (a + d).choose d * (m + 1 - a) +
          (d + 1) * ∑ a ∈ Finset.range (m + 1), (a + d).choose d := by
      rw [Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun a ha => ?_
      have : a < m + 1 := Finset.mem_range.mp ha
      rw [show d + 2 + m - a = (m + 1 - a) + (d + 1) by omega]
      ring
    rw [hw, sum_range_choose_mul_sub, hsum]
    have key := Nat.add_one_mul_choose_eq (m + d + 1) (d + 1)
    rw [show m + 1 + d + 1 = m + d + 1 + 1 by omega]
    nlinarith [key]

end GlobalTheory.HSShort
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NefBigSecondBaseChange
section
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.HermTools GlobalTheory.Vanishing GlobalTheory.Adelic GlobalTheory.HilbertSamuel GlobalTheory.ChowHt GlobalTheory.TangentOrigin
open GlobalTheory.IndefiniteRowSideFullHecke.RadicalPowers
open GlobalTheory.HSCore GlobalTheory.QCoh
open GlobalTheory
open GlobalTheory.HSShort GlobalTheory.HSChoice MvPolynomial

namespace GlobalTheory.HSShort

theorem nef_big_second_baseChange : ∀ (F : Type) [Field F] [NumberField F] (X : Data F) (E : Type) [Field E] [NumberField E] [Algebra F E], IsNef F X.L₂ → IsBig F X.L₂ → IsNef E (X.baseChange E).L₂ ∧ IsBig E (X.baseChange E).L₂ := by
  intro F _ _ X E _ _ _ hn hb
  exact ⟨PosBaseChange.isNef_baseChange (X.toGeo.isPullback_fst E) X.geom.alg.variety.proj hn,
    PosBaseChange.isBig_baseChange (X.toGeo.isPullback_fst E) X.geom.alg.variety.proj hb⟩

end GlobalTheory.HSShort
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NilradicalAdjointExpStableStatement
section
open Matrix GlobalTheory.TorFin
open scoped ContDiff

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.nilradical_adjoint_exp_stable : ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) ℂ), Jᴴ = J → IsUnit J.det → ∀ (x : Fin n → ℂ) (Y : Matrix (Fin n) (Fin n) ℂ), Y ∈ nilRad J x → J⁻¹ * Yᴴ * J ∈ nilRad J x ∧ NormedSpace.exp Y - 1 ∈ nilRad J x := by
  first | exact @GlobalTheory.TorFin.NilAdj.nilRad_adj_exp | exact GlobalTheory.TorFin.NilAdj.nilRad_adj_exp | (intros; apply GlobalTheory.TorFin.NilAdj.nilRad_adj_exp <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonKltLocusDimLtAfterPerturbationStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.nonKlt_locus_dim_lt_after_perturbation : ∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] [GlobalTheory.IsNormalScheme X] (p : X ⟶ Sp ℂ) (n : ℕ), IsProjOver p → topologicalKrullDim X = n → ∀ (Δ D B : X → ℚ) (δ c : ℚ) (x z : X) (j : ℕ), KltAt p n Δ x → IsQCart D → IsQCart B → LcAt p n (Δ + D) x → 0 < δ → δ ≤ 1 → c ≤ 1 → Off B z → (∀ y, ¬ z ⤳ y → ∀ a : ℚ, 0 ≤ a → KltAt p n (Δ + a • D) y → KltAt p n (Δ + a • D + B) y) → topologicalKrullDim (closure ({z} : Set X)) = (j + 1 : ℕ) → LcAt p n (Δ + (1 - δ) • D + c • B) x → ¬ KltAt p n (Δ + (1 - δ) • D + c • B) x → LcCut p n (Δ + (1 - δ) • D + c • B) x j := by
  first | exact @GlobalTheory.PairStep.logCanonicalCut_of_step | exact GlobalTheory.PairStep.logCanonicalCut_of_step | (intros; apply GlobalTheory.PairStep.logCanonicalCut_of_step <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NumConsEqMulOfEffectiveDivisorSuppSection
section
open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZH GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.FlagPush
open Classical

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FlagPush.Dbl

theorem num_cons_eq_mul_of_supp_eq_range : ∀ (F : Type) [Field F] (Y : Var F) (W : Dbl Y), W.Small → ∀ Θ : CartierDiv W.Z, Θ.Eff → (Θ.supp : Set W.Z) = Set.range W.δ → ∃ μ : ℤ, μ ≠ 0 ∧ ∀ y : Fin Y.dim → CartierDiv W.Z, letI := algebraΓOfHom (W.p₁ ≫ Y.str); W.num (Fin.cons Θ y : Fin (Y.dim + 1) → CartierDiv W.Z) = μ * interNumRed F (⟨closure {W.δ (genericPoint Y.X)}, isClosed_closure⟩ : Closeds W.Z) fun i => toLB (y i) := by
  intro F _ Y W hW Θ hΘ hsupp
  letI := algebraΓOfHom (W.p₁ ≫ Y.str)
  have hstr : strHom F W.Z = W.p₁ ≫ Y.str := GlobalTheory.strHom_eq fun _ => rfl
  have hp : IsProjOver (strHom F W.Z) := hstr ▸ W.proj
  have : IsLocallyNoetherian W.Z := by
    obtain ⟨N, ι, _, h⟩ := hp
    have : LocallyOfFiniteType (strHom F W.Z) := h ▸ inferInstance
    exact LocallyOfFiniteType.isLocallyNoetherian (strHom F W.Z)
  obtain ⟨s, hs, e⟩ := GlobalTheory.RatSecCycle.exists_sec_divOfSec_eq Θ hΘ
  set η := genericPoint Y.X
  set w₀ := W.δ η
  have hδ := W.δ.isClosedEmbedding
  have hcl : closure ({w₀} : Set W.Z) = Set.range W.δ := by
    rw [← Set.image_singleton, hδ.closure_image_eq, (genericPoint_spec Y.X).def, Set.image_univ]
  have hd : topologicalKrullDim (closure ({w₀} : Set W.Z)) = Y.dim := by
    rw [topologicalKrullDim_eq_of_isEmbedding hδ.isEmbedding hcl.symm, Y.topologicalKrullDim_eq]
  have hw₀ : w₀ ∈ Θ.supp := by
    show w₀ ∈ (Θ.supp : Set W.Z); rw [hsupp]; exact ⟨η, rfl⟩
  have hmax : ¬ IsMax w₀ := fun h =>
    Θ.genericPoint_notMem_supp ((h (genericPoint_specializes w₀)).mem_closed Θ.supp.isClosed hw₀)
  have hc := GlobalTheory.SecCycle.coheight_eq_one_of_dim_closure hW hmax hd
  refine ⟨Θ.mult w₀, ?_, fun y => ?_⟩
  · have hws : w₀ ∉ ReciprocityTheory.ChartRestriction.G.Out.nonzeroLocus s := fun h =>
      (GlobalTheory.Cartier.notMem_supp_divOfSec.2 h) (e.symm ▸ hw₀)
    have := GlobalTheory.SecCycle.mult_divOfSec_ne_zero (isLB_toLB Θ) s hs hc hws
    rwa [e] at this
  · have hcons : (fun i => toLB ((Fin.cons Θ y : Fin (Y.dim + 1) → CartierDiv W.Z) i)) =
        (Fin.cons (toLB Θ) (fun i => toLB (y i)) : Fin (Y.dim + 1) → LB W.Z) := by
      funext i
      refine Fin.cases ?_ (fun j => ?_) i <;> simp
    have hF := GlobalTheory.SecCycle.interNum_cons_eq_finsum_mult F W.Z hp Y.dim hW (toLB Θ)
      (isLB_toLB Θ) (fun i => toLB (y i)) (fun i => isLB_toLB (y i)) s hs
    rw [e] at hF
    show interNum F (structureModule W.Z) _ = _
    rw [hcons, hF]
    refine finsum_eq_single _ w₀ fun w hw => ?_
    by_cases hm : Θ.mult w = 0
    · rw [hm, zero_mul]
    obtain ⟨y', rfl⟩ : w ∈ Set.range W.δ := by
      rw [← hsupp]; exact CartierDiv.mem_supp_of_mult_ne_zero hm
    have hy' : y' ≠ η := fun h => hw (by rw [h])
    have hnot : w₀ ∉ closure ({W.δ y'} : Set W.Z) := fun h => by
      have h1 : W.δ y' ⤳ W.δ η := specializes_iff_mem_closure.2 h
      have h2 : y' ⤳ η := hδ.isInducing.specializes_iff.1 h1
      exact hy' (h2.antisymm (genericPoint_specializes y')).eq
    have hsp : w₀ ⤳ W.δ y' := specializes_iff_mem_closure.2 (hcl.symm ▸ ⟨y', rfl⟩ : W.δ y' ∈ closure ({w₀} : Set W.Z))
    have h1 : topologicalKrullDim (closure ({W.δ y'} : Set W.Z)) + 1 ≤ topologicalKrullDim (closure ({w₀} : Set W.Z)) :=
      topologicalKrullDim_add_one_le isClosed_closure isClosed_closure fun z hz =>
        ⟨w₀, subset_closure rfl, hnot, hsp.trans (specializes_iff_mem_closure.2 hz)⟩
    rw [hd] at h1
    have hlt : topologicalKrullDim (closure ({W.δ y'} : Set W.Z)) < (Fintype.card (Fin Y.dim) : ℕ) := by
      rw [Fintype.card_fin]; exact GlobalTheory.SheafCycle.lt_of_add_one_le_natCast h1
    rw [GlobalTheory.SheafCycle.interNumRed_eq_zero F hp (fun i => isLB_toLB (y i)) _ hlt, mul_zero]

end GlobalTheory.FlagPush.Dbl
end
end

