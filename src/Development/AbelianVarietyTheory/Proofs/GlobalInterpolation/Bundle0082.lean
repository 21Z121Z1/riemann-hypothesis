import Mathlib
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.LevelPrimeIncidenceFiniteFibresStable
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.FormsStable
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.LevelPrimePowSmulMemValueLatticeErase
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.LogFreeZeroDensityDirichletOneModulus
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.ZerosDisc
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.Bundle0015
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalGlobalInclusion.SmulMemIdealSmul
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0073
import Formalism.LocalToGlobal.Columns.FiniteSumNonzeroLargeDepth
import Formalism.LocalToGlobal.Columns.DecorationStabilizerTrivialUnipotent
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PredMemGamRanks
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0064
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ParameterInequalitiesGood
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Bundle0002
import Formalism.GL3MeanSquares.Bundle0001
import Formalism.FrobeniusOrbits.HostCorollaries
import Formalism.SharpRestriction.GlobalSchurBounds.Bundle0003
import Formalism.SharpRestriction.GlobalSchurBounds.ZetaZeroFreeRegion
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.RayClassFamilyPsiWithExceptionalZero
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.LamIdealOfNotPrimePow
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0077
import Formalism.SharpRestriction.InertJacobiLevels.Bundle0007

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.LevelPrimeIncidenceFiniteFibresStableStatement
section
open Formalism.BasicNotions Classical NumberField GlobalTheory.LvT
open Formalism.MainNotions.product_first_zeroth_parts (Ow tops wsum ten blk nfAll CSpan IntSpan Nm_succ wSh cTw)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.levelPrime_incidence_finite_fibres_stable : ∀ (D : D7) (u : D.what₂.Word) (X : Ch D u) (i : ℕ) (M : PtModel X i) (v : X.A.vT), (∀ p, {p₁ | M.Inc v p p₁}.Finite ∧ {p₀ | M.Inc v p₀ p}.Finite) ∧ (∀ (g : M.G) p p₁, M.Inc v p p₁ ↔ M.Inc v (g • p) (g • p₁)) ∧ ∀ (p : M.Pt) x, (p.2 v).1.f x = 1 → ∃! q, (p.2 v).IsUp x q := by
  first | exact @GlobalTheory.LvT.inc_finite_stable | exact GlobalTheory.LvT.inc_finite_stable | (intros; apply GlobalTheory.LvT.inc_finite_stable <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.LevelPrimePowSmulMemValueLatticeEraseStatement
section
open Formalism.BasicNotions Classical NumberField GlobalTheory.LvT
open Formalism.MainNotions.product_first_zeroth_parts (Ow tops wsum ten blk nfAll CSpan IntSpan Nm_succ wSh cTw)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.levelPrime_pow_smul_mem_valueLattice_erase : ∀ (D : D7) (u : D.what₂.Word) (X : Ch D u) (i : ℕ) (M : PtModel X i) (Co : M.Coord), Co.Ok → ∀ w, OverT X w → X.fm.seenP w = true → ∀ (V : Finset X.A.vT) (v : X.A.vT), v ∈ V → ∀ p, ∀ y ∈ Co.valB w V p, ((X.A.T : ℂ) ^ (PtModel.lamT X i (X.fm.tauOf w v)).w ⟨0, D.R.N_pos i⟩) • y ∈ Co.valB w (V.erase v) p := by
  first | exact @GlobalTheory.LvT.pow_smul_mem_valB_erase | exact GlobalTheory.LvT.pow_smul_mem_valB_erase | (intros; apply GlobalTheory.LvT.pow_smul_mem_valB_erase <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.LogFreeZeroDensityDirichletOneModulusStatement
section
open Complex DirichletCharacter ArithmeticFunction MeasureTheory Filter Topology GlobalTheory.Lin
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.logFree_zeroDensity_dirichlet_one_modulus : ∃ A C η : ℝ, 0 < A ∧ 0 < C ∧ 0 < η ∧ ∀ (q : ℕ) [NeZero q] (T σ : ℝ), 2 ≤ T → 1 - η ≤ σ → σ ≤ 1 → ∑ χ : DirichletCharacter ℂ q, (∑ᶠ ρ ∈ zerosBox χ σ T, (ord χ ρ : ℝ)) ≤ C * ((q : ℝ) * T) ^ (A * (1 - σ)) := by
  first | exact @GlobalTheory.Lin.LogFree.zero_density | exact GlobalTheory.Lin.LogFree.zero_density | (intros; apply GlobalTheory.Lin.LogFree.zero_density <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.MemExtLatOfMemLocP
section
open NumberField IsDedekindDomain MvPolynomial Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.IndefiniteRowSideFullHecke.SubstitutionAdjoint
open scoped Matrix

namespace GlobalTheory.ExtLatMatrix

variable {K : Type} [Field K] [NumberField K] {w : HeightOneSpectrum (𝓞 K)} {L Γ : Type} [Field L]
  [LinearOrderedCommGroupWithZero Γ] {v : Valuation L Γ} {σ : K →+* L}

open NumberField IsDedekindDomain MvPolynomial in
open scoped Matrix in
variable {K : Type} [Field K] [NumberField K] {w : HeightOneSpectrum (𝓞 K)} {L Γ : Type} [Field L]
  [LinearOrderedCommGroupWithZero Γ] {v : Valuation L Γ} {σ : K →+* L} in

theorem _root_.GlobalTheory.ExtLatMatrix.mem_extLat_of_mem_locP (h : ∀ x : K, v (σ x) ≤ 1 ↔ w.valuation K x ≤ 1)
    {a : ℕ} (M : Submodule (𝓞 K) (Fin a → K)) (x : Fin a → K) (hx : x ∈ _root_.Formalism.HermitianLatticesTheory.localization₂ w.asIdeal M) :
    (fun i => σ (x i)) ∈ _root_.GlobalTheory.IndefiniteRowSideFullHecke.SubstitutionAdjoint.extLat v σ M := by
  obtain ⟨s, hs, hsx⟩ := (_root_.PI.LocGlobInclWork.mem_localization_iff w.asIdeal M x).1 hx
  have hs0 : (s : K) ≠ 0 := by
    intro h0
    apply hs
    have hs' : s = 0 := by exact_mod_cast h0
    rw [hs']
    exact w.asIdeal.zero_mem
  have hval : w.valuation K ((s : K)⁻¹) ≤ 1 := by
    rw [map_inv₀]
    have h1 : w.valuation K (s : K) = 1 := by
      rw [show (s : K) = algebraMap (𝓞 K) K s from rfl, HeightOneSpectrum.valuation_of_algebraMap]
      exact (HeightOneSpectrum.intValuation_eq_one_iff_mem_primeCompl w s).2 hs
    rw [h1, inv_one]
  have hint : σ ((s : K)⁻¹) ∈ v.integer := (h _).2 hval
  have hmem : (fun i => σ ((s • x) i)) ∈ _root_.GlobalTheory.IndefiniteRowSideFullHecke.SubstitutionAdjoint.extLat v σ M :=
    Submodule.subset_span ⟨s • x, hsx, rfl⟩
  have hsm := Submodule.smul_mem _ (⟨σ ((s : K)⁻¹), hint⟩ : v.integer) hmem
  convert hsm using 1
  funext i
  simp only [Pi.smul_apply, Subring.smul_def, smul_eq_mul]
  rw [Algebra.smul_def, map_mul, ← mul_assoc, ← map_mul, inv_mul_cancel₀ hs0, map_one, one_mul]

open NumberField IsDedekindDomain MvPolynomial in
open scoped Matrix in
variable {K : Type} [Field K] [NumberField K] {w : HeightOneSpectrum (𝓞 K)} {L Γ : Type} [Field L]
  [LinearOrderedCommGroupWithZero Γ] {v : Valuation L Γ} {σ : K →+* L} in

theorem _root_.GlobalTheory.ExtLatMatrix.extLat_matrix_integral : ∀ (K : Type) [Field K] [NumberField K]
    (w : HeightOneSpectrum (𝓞 K)) (L Γ : Type) [Field L] [LinearOrderedCommGroupWithZero Γ]
    (v : Valuation L Γ) (σ : K →+* L), (∀ x : K, v (σ x) ≤ 1 ↔ w.valuation K x ≤ 1) →
    (∀ (a : ℕ) (M : Submodule (𝓞 K) (Fin a → K)), ∀ x ∈ _root_.Formalism.HermitianLatticesTheory.localization₂ w.asIdeal M,
      (fun i => σ (x i)) ∈ _root_.GlobalTheory.IndefiniteRowSideFullHecke.SubstitutionAdjoint.extLat v σ M) ∧
    ∀ (a b : ℕ) (M : Submodule (𝓞 K) (Fin a → K)) (MW : Submodule (𝓞 K) (Fin b → K))
      (B : GL (Fin a) K) (BW : GL (Fin b) K), _root_.Formalism.L2.DIV.IsBasisAt w M B → _root_.Formalism.L2.DIV.IsBasisAt w MW BW →
      ∀ ap : Matrix (Fin a) (Fin b) L,
        (∀ y ∈ _root_.GlobalTheory.IndefiniteRowSideFullHecke.SubstitutionAdjoint.extLat v σ MW, ap *ᵥ y ∈ _root_.GlobalTheory.IndefiniteRowSideFullHecke.SubstitutionAdjoint.extLat v σ M) →
        ∀ i j, v ((((B⁻¹ : GL (Fin a) K) : Matrix (Fin a) (Fin a) K).map σ * ap *
          (BW : Matrix (Fin b) (Fin b) K).map σ) i j) ≤ 1 := by
  intro K _ _ w L Γ _ _ v σ h
  refine ⟨fun a M x hx => _root_.GlobalTheory.ExtLatMatrix.mem_extLat_of_mem_locP h M x hx, ?_⟩
  intro a b M MW B BW hB hBW ap hap i j
  have hunit : ∀ t : 𝓞 K, t ∉ w.asIdeal → v (σ ((t : K)⁻¹)) ≤ 1 := by
    intro t ht
    refine (h _).2 ?_
    rw [map_inv₀]
    have h1 : w.valuation K (t : K) = 1 := by
      rw [show (t : K) = algebraMap (𝓞 K) K t from rfl, HeightOneSpectrum.valuation_of_algebraMap]
      exact (HeightOneSpectrum.intValuation_eq_one_iff_mem_primeCompl w t).2 ht
    rw [h1, inv_one]
  have hint : ∀ y ∈ _root_.GlobalTheory.IndefiniteRowSideFullHecke.SubstitutionAdjoint.extLat v σ M, ∀ k,
      v (((((B⁻¹ : GL (Fin a) K) : Matrix (Fin a) (Fin a) K).map σ) *ᵥ y) k) ≤ 1 := by
    intro y hy
    unfold _root_.GlobalTheory.IndefiniteRowSideFullHecke.SubstitutionAdjoint.extLat at hy
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨m, hm, rfl⟩ := hy
      have hm' : m ∈ _root_.Formalism.HermitianLatticesTheory.localization₂ w.asIdeal (_root_.Formalism.L2.DIV.colLat B) := by
        unfold _root_.Formalism.L2.DIV.IsBasisAt at hB
        rw [← hB]
        exact _root_.Formalism.HermitianLatticesTheory.locBasic_le_locS _ _ hm
      obtain ⟨t, ht, htm⟩ := (_root_.PI.LocGlobInclWork.mem_localization_iff w.asIdeal _ m).1 hm'
      unfold _root_.Formalism.L2.DIV.colLat at htm
      obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun (𝓞 K)).1 htm
      have ht0 : (t : K) ≠ 0 := by
        intro h0
        apply ht
        have ht' : t = 0 := by exact_mod_cast h0
        rw [ht']
        exact w.asIdeal.zero_mem
      have hBc : (B : Matrix (Fin a) (Fin a) K) *ᵥ (fun k => (c k : K)) = (t : K) • m := by
        funext r
        have hr := congrFun hc r
        simp only [Finset.sum_apply, Pi.smul_apply] at hr
        simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul]
        rw [← Algebra.smul_def] at *
        convert hr using 1
        · refine Finset.sum_congr rfl fun k _ => ?_
          rw [Algebra.smul_def, mul_comm]
          try rfl
      have hBm : ((B⁻¹ : GL (Fin a) K) : Matrix (Fin a) (Fin a) K) *ᵥ m =
          (t : K)⁻¹ • fun k => (c k : K) := by
        have e : m = (t : K)⁻¹ • ((B : Matrix (Fin a) (Fin a) K) *ᵥ (fun k => (c k : K))) := by
          rw [hBc, smul_smul, inv_mul_cancel₀ ht0, one_smul]
        rw [e, Matrix.mulVec_smul, Matrix.mulVec_mulVec]
        simp
      intro k
      have e : ((((B⁻¹ : GL (Fin a) K) : Matrix (Fin a) (Fin a) K).map σ) *ᵥ (fun i => σ (m i))) k =
          σ ((((B⁻¹ : GL (Fin a) K) : Matrix (Fin a) (Fin a) K) *ᵥ m) k) := by
        simp [Matrix.mulVec, dotProduct, map_sum, map_mul]
      rw [e, hBm, Pi.smul_apply, smul_eq_mul, map_mul, map_mul]
      refine mul_le_one' (hunit t ht) ((h _).2 ?_)
      exact HeightOneSpectrum.valuation_le_one w (c k)
    | zero => simp
    | add y z _ _ hy hz =>
      intro k
      rw [Matrix.mulVec_add, Pi.add_apply]
      exact v.map_add_le (hy k) (hz k)
    | smul c y _ hy =>
      intro k
      rw [Matrix.mulVec_smul, Pi.smul_apply, Subring.smul_def, smul_eq_mul, map_mul]
      exact mul_le_one' c.2 (hy k)
  have hcol : (fun k => σ ((BW : Matrix (Fin b) (Fin b) K) k j)) ∈ _root_.GlobalTheory.IndefiniteRowSideFullHecke.SubstitutionAdjoint.extLat v σ MW := by
    refine _root_.GlobalTheory.ExtLatMatrix.mem_extLat_of_mem_locP h MW _ ?_
    unfold _root_.Formalism.L2.DIV.IsBasisAt at hBW
    rw [hBW]
    exact _root_.Formalism.HermitianLatticesTheory.locBasic_le_locS _ _ (Submodule.subset_span ⟨j, rfl⟩)
  have key := hint _ (hap _ hcol) i
  convert key using 2
  simp only [Matrix.mul_apply, Matrix.mulVec, dotProduct, Matrix.map_apply, Finset.sum_mul,
    Finset.mul_sum, mul_assoc]
  exact Finset.sum_comm

end GlobalTheory.ExtLatMatrix
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.MemFormsIffExistsEquivariantExtensionStatement
section
open Formalism.BasicNotions Classical NumberField GlobalTheory.LvT
open Formalism.MainNotions.product_first_zeroth_parts (Ow tops wsum ten blk nfAll CSpan IntSpan Nm_succ wSh cTw)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_forms_iff_exists_equivariant_extension : ∀ (D : D7) (u : D.what₂.Word) (X : Ch D u) (i : ℕ) (M : PtModel X i) (φ : Fn X i), φ ∈ X.fm.Fi i ↔ ∃ Φ, M.IsExt φ Φ := by
  first | exact @GlobalTheory.LvT.PtModel.mem_Fi_iff_exists_isExt | exact GlobalTheory.LvT.PtModel.mem_Fi_iff_exists_isExt | (intros; apply GlobalTheory.LvT.PtModel.mem_Fi_iff_exists_isExt <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.NotDvdCardStabilizerForm
section
noncomputable section

namespace GlobalTheory.LvT.StabOrder

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Col Formalism.L2.DIV GlobalTheory.Mem.Col2

theorem rank_le (R : Ranks) {i j : ℕ} (h : i ≤ j) : R.N i ≤ R.N j := by
  unfold Ranks.N
  exact Nat.add_le_add_left (Nat.mul_le_mul_right _ h) _

theorem prime_le_of_embed {E G : Type} [Field E] [NumberField E] [Group G] [Finite G] {n : ℕ}
    (φ : G →* ((Fin n → E) ≃ₗ[E] (Fin n → E))) (hφ : Function.Injective φ) {p : ℕ} (hp : p.Prime)
    (hd : p ∣ Nat.card G) : p ≤ Module.finrank ℚ E * n + 1 := by
  haveI : Finite φ.range := Finite.of_surjective _ φ.rangeRestrict_surjective
  have h := prime_le_of_dvd_card φ.range hp (by rwa [← Nat.card_congr (MonoidHom.ofInjective hφ).toEquiv])
  rwa [Module.finrank_fin_fun] at h

theorem prime_le_of_embed_GL {E G : Type} [Field E] [NumberField E] [Group G] [Finite G] {n : ℕ}
    (φ : G →* GL (Fin n) E) (hφ : Function.Injective φ) {p : ℕ} (hp : p.Prime)
    (hd : p ∣ Nat.card G) : p ≤ Module.finrank ℚ E * n + 1 :=
  prime_le_of_embed ((LinearMap.GeneralLinearGroup.generalLinearEquiv E (Fin n → E)).toMonoidHom.comp
      ((Matrix.GeneralLinearGroup.toLin (n := Fin n) (R := E)).toMonoidHom.comp φ))
    ((LinearMap.GeneralLinearGroup.generalLinearEquiv E (Fin n → E)).injective.comp
      ((Matrix.GeneralLinearGroup.toLin (n := Fin n) (R := E)).injective.comp hφ)) hp hd

def pairStab {K : Type} [Field K] [NumberField K] [StarRing K] {S : GSD K} (Y : Cpl S) (p : Y.Pts) : Subgroup S.G :=
  MulAction.stabilizer S.G p

theorem pairStab_le {K : Type} [Field K] [NumberField K] [StarRing K] {S : GSD K} (Y : Cpl S) (p : Y.Pts) {g : S.G}
    (hg : g ∈ pairStab Y p) : g • p.1.1 = p.1.1 :=
  congrArg (fun q : Y.Pts => q.1.1) (show g • p = p from hg)

section Concrete

variable {F : Fields} {Pr : Primes F} {R : Ranks} {W : Wts F Pr.Word R} {a : ℝ}

theorem prime_le_and_lt (hF : F.Ok) (hS : Sizes Pr W a) (u : Pr.Word) {n : ℕ} (hn : n ≤ R.N R.m)
    (Γ : Subgroup (UF F.E n)) [Finite Γ] {p : ℕ} (hp : p.Prime) (hd : p ∣ Nat.card Γ) :
    p ≤ 2 * F.f * R.N R.m + 1 ∧ 2 * F.f * R.N R.m + 1 < Pr.T u := by
  refine ⟨?_, hS.T_big u⟩
  have h := prime_le_of_embed ((UF F.E n).subtype.comp Γ.subtype)
    (Subtype.val_injective.comp Subtype.val_injective) hp hd
  rw [hF.finrank_E] at h
  exact h.trans (Nat.succ_le_succ (Nat.mul_le_mul_left _ hn))

theorem prime_le_and_lt_step (hF : F.Ok) (hS : Sizes Pr W a) (u : Pr.Word) {j : ℕ} (hj : j ≤ R.m)
    (Γ : Subgroup (UF F.E (R.N j))) [Finite Γ] {p : ℕ} (hp : p.Prime) (hd : p ∣ Nat.card Γ) :
    p ≤ 2 * F.f * R.N R.m + 1 ∧ 2 * F.f * R.N R.m + 1 < Pr.T u :=
  prime_le_and_lt hF hS u (rank_le R hj) Γ hp hd

theorem prime_le_and_lt_row (hF : F.Ok) (hS : Sizes Pr W a) (u : Pr.Word)
    (Γ : Subgroup (UF F.E (R.N R.m - 1))) [Finite Γ] {p : ℕ} (hp : p.Prime) (hd : p ∣ Nat.card Γ) :
    p ≤ 2 * F.f * R.N R.m + 1 ∧ 2 * F.f * R.N R.m + 1 < Pr.T u :=
  prime_le_and_lt hF hS u (Nat.sub_le _ _) Γ hp hd

variable {n : ℕ} {ST SG Q : Finset (HeightOneSpectrum (𝓞 F.E))}

theorem exists_embed_deco (Λ : LevFam F.E F.K n SG) (Θ : LevQFam F.E F.K n Q) (p : DecoF F.E n ST SG Q)
    {G : Type} [Group G] (j : G →* FrmG Λ Θ) (hj : Function.Injective j) (hfix : ∀ g, j g • p = p) :
    ∃ φ : G →* MulAction.stabilizer (UF F.E n × GLG F.E n SG) p.deco, Function.Injective φ :=
  ⟨{ toFun := fun g => ⟨((j g).1, ((j g).2.1 : GLG F.E n SG)), congrArg DecoF.deco (hfix g)⟩
     map_one' := Subtype.ext (by
       show (((j 1).1, ((j 1).2.1 : GLG F.E n SG)) : UF F.E n × GLG F.E n SG) = 1
       rw [map_one]; rfl)
     map_mul' := fun x y => Subtype.ext (by
       show (((j (x * y)).1, ((j (x * y)).2.1 : GLG F.E n SG)) : UF F.E n × GLG F.E n SG) = _
       rw [map_mul]; rfl) }, fun x y h => by
    have h1 : (((j x).1, ((j x).2.1 : GLG F.E n SG)) : UF F.E n × GLG F.E n SG) = ((j y).1, ((j y).2.1 : GLG F.E n SG)) :=
      congrArg Subtype.val h
    exact hj (FramedForms.incl_injective Λ Θ
      (FramedForms.stab_inj p (hfix x) (hfix y) (Prod.mk.inj h1).1 (Prod.mk.inj h1).2))⟩

theorem finite_and_prime_le_frm (hF : F.Ok) (Λ : LevFam F.E F.K n SG) (Θ : LevQFam F.E F.K n Q) (p : DecoF F.E n ST SG Q)
    {G : Type} [Group G] (j : G →* FrmG Λ Θ) (hj : Function.Injective j) (hfix : ∀ g, j g • p = p) :
    Finite G ∧ ∀ q : ℕ, q.Prime → q ∣ Nat.card G → q ≤ 2 * F.f * n + 1 := by
  obtain ⟨φ, hφ⟩ := exists_embed_deco Λ Θ p j hj hfix
  haveI := DecoSet.finite_stabilizer (posStar_of_conj hF.conjE) p.deco
  refine ⟨Finite.of_injective φ hφ, fun q hq hd => ?_⟩
  have h := DecoSet.prime_le_of_dvd_card p.deco _ le_rfl hq (hd.trans (Subgroup.card_dvd_of_injective φ hφ))
  rwa [hF.finrank_E] at h

theorem not_dvd_card_frm (hF : F.Ok) (hS : Sizes Pr W a) (u : Pr.Word) (hT : (Pr.T u).Prime) (hn : n ≤ R.N R.m)
    (Λ : LevFam F.E F.K n SG) (Θ : LevQFam F.E F.K n Q) (p : DecoF F.E n ST SG Q)
    {G : Type} [Group G] (j : G →* FrmG Λ Θ) (hj : Function.Injective j) (hfix : ∀ g, j g • p = p) :
    ¬ Pr.T u ∣ Nat.card G := fun hd => by
  have h1 := (finite_and_prime_le_frm hF Λ Θ p j hj hfix).2 _ hT hd
  have h2 := hS.T_big u
  have h3 := Nat.mul_le_mul_left (2 * F.f) hn
  omega

theorem not_dvd_card_stabilizer_over (hF : F.Ok) (hS : Sizes Pr W a) (u : Pr.Word) (hT : (Pr.T u).Prime) (hn : n ≤ R.N R.m)
    (Λ : LevFam F.E F.K n SG) (Θ : LevQFam F.E F.K n Q) {G Z : Type} [Group G] [MulAction G Z]
    (j : G →* FrmG Λ Θ) (hj : Function.Injective j) (π : Z → DecoF F.E n ST SG Q) (hπ : ∀ g z, π (g • z) = j g • π z) (z : Z) :
    ¬ Pr.T u ∣ Nat.card (MulAction.stabilizer G z) :=
  not_dvd_card_frm hF hS u hT hn Λ Θ (π z) (j.comp (MulAction.stabilizer G z).subtype) (hj.comp Subtype.val_injective)
    fun g => (hπ g.1 z).symm.trans (congrArg π g.2)

theorem not_dvd_card_stabilizer_form (hF : F.Ok) (hS : Sizes Pr W a) (u : Pr.Word) (hT : (Pr.T u).Prime) (hn : n ≤ R.N R.m)
    (Λ : LevFam F.E F.K n SG) (d : DecoSet F.E n ST SG) : ¬ Pr.T u ∣ Nat.card (MulAction.stabilizer (FormG Λ) d) := fun hd => by
  haveI := DecoSet.finite_stabilizer (posStar_of_conj hF.conjE) d
  let φ : MulAction.stabilizer (FormG Λ) d →* MulAction.stabilizer (UF F.E n × GLG F.E n SG) d :=
    { toFun := fun g => ⟨FormG.incl Λ g.1, g.2⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  have hφ : Function.Injective φ := fun x y h => by
    have h1 : FormG.incl Λ x.1 = FormG.incl Λ y.1 := congrArg Subtype.val h
    have h2 := congrArg Prod.fst h1
    have h3 := congrArg Prod.snd h1
    exact Subtype.ext (Prod.ext h2 (Subtype.ext h3))
  have h1 := DecoSet.prime_le_of_dvd_card d _ le_rfl hT (hd.trans (Subgroup.card_dvd_of_injective φ hφ))
  rw [hF.finrank_E] at h1
  have h2 := hS.T_big u
  have h3 := Nat.mul_le_mul_left (2 * F.f) hn
  omega

variable (sel : HeightOneSpectrum (𝓞 F.F) → HeightOneSpectrum (𝓞 F.E)) {S : Set ℕ} (mu : Tup F.F F.E F.K S)
  (cst : LocCst F (rowSG Pr sel mu)) (L : ChIdx F Pr R (QE sel (mu : Chr F.F F.E F.K)))

theorem not_dvd_card_chF (hF : F.Ok) (hS : Sizes Pr W a) (u : Pr.Word) (hT : (Pr.T u).Prime) {j : ℕ} (hj : j ≤ R.m)
    (b : L.β j) (p : ((chF W sel mu L u j).mem b).D) :
    ¬ Pr.T u ∣ Nat.card (MulAction.stabilizer ((chF W sel mu L u j).mem b).G p) :=
  not_dvd_card_stabilizer_over hF hS u hT (rank_le R hj) (L.levG j b) (L.levQ j b) (G := ((chF W sel mu L u j).mem b).G)
    (MonoidHom.id _) Function.injective_id id (fun _ _ => rfl) p

theorem not_dvd_card_cpl (hF : F.Ok) (hS : Sizes Pr W a) (u : Pr.Word) (hT : (Pr.T u).Prime) {m2 : ℕ} (hm : m2 + 1 ≤ R.m)
    (b : L.β (m2 + 1)) (hY : YbHyp (R := R) sel mu cst L u m2 b) (p : (ybCpl W sel mu cst L u m2 b hY).Pts) :
    ¬ Pr.T u ∣ Nat.card (pairStab (ybCpl W sel mu cst L u m2 b hY) p) :=
  not_dvd_card_frm hF hS u hT (rank_le R hm) (L.levG (m2 + 1) b) (L.levQ (m2 + 1) b) p.1.1
    (pairStab (ybCpl W sel mu cst L u m2 b hY) p).subtype Subtype.val_injective fun g => pairStab_le _ p g.2

theorem not_dvd_card_evGSD (hF : F.Ok) (hS : Sizes Pr W a) (u : Pr.Word) (hT : (Pr.T u).Prime) (Cr : Chars F Pr R.m)
    (P : LevFam F.E F.K R.r Pr.vGs) (d : (evGSD W Cr sel mu P u).D) :
    ¬ Pr.T u ∣ Nat.card (MulAction.stabilizer (evGSD W Cr sel mu P u).G d) :=
  not_dvd_card_stabilizer_form hF hS u hT (Nat.sub_le _ _) _ d

theorem not_dvd_card_stepAt (hF : F.Ok) (hS : Sizes Pr W a) (u : Pr.Word) (hT : (Pr.T u).Prime)
    (Tp : TopLev F Pr R (QE sel (mu : Chr F.F F.E F.K))) {j : ℕ} (hj : j ≤ R.m) (c : (stepAt sel mu cst L Tp u j).Cl) :
    ¬ Pr.T u ∣ Nat.card ((stepAt sel mu cst L Tp u j).Stab c) :=
  letI := (stepAt sel mu cst L Tp u j).actD c.1
  not_dvd_card_stabilizer_over hF hS u hT (rank_le R hj) (levGAt sel mu L Tp j c.1) (levQAt sel mu L Tp j c.1)
    (G := (stepAt sel mu cst L Tp u j).G c.1) (Z := (stepAt sel mu cst L Tp u j).D c.1)
    (MonoidHom.id _) Function.injective_id (fun p => p.1.1) (fun _ _ => rfl) _

end Concrete

section Record

variable {D : D7} {u : D.what₂.Word}

theorem stabUnit_of_embed (X : Ch D u) (E : Type) [Field E] [NumberField E]
    (hT : Module.finrank ℚ E * D.R.N D.R.m + 1 < X.A.T)
    (h : ∀ i, i ≤ D.R.m → ∀ c : X.C.cls i, ∃ j : X.C.stab i c →* GL (Fin (D.R.N i)) E, Function.Injective j) :
    StabUnit X := fun i hi c hd => by
  obtain ⟨j, hj⟩ := h i hi c
  have h1 := prime_le_of_embed_GL j hj X.A.T_prime hd
  have h2 := Nat.mul_le_mul_left (Module.finrank ℚ E) (rank_le D.R hi)
  omega

theorem stabUnit_of_chainIn (X : Ch D u) {E K : Type} [Field E] [NumberField E] [StarRing E] [Field K] [NumberField K] [StarRing K]
    (I : ChainIn E K D.what₂.Tau D.R) (emb : D.what₂.Tau → E →+* K) (σ : K →+* ℂ) (hI : I.Ok)
    (hC : X.C = I.chain emb σ hI (D.hcW u)) (hT : Module.finrank ℚ E * D.R.N D.R.m + 1 < X.A.T) : StabUnit X := by
  refine stabUnit_of_embed X E hT ?_
  rw [hC]
  intro i _ c
  refine ⟨((I.S i).gam c.1).comp (MulAction.stabilizer _ ((I.S i).rep c)).subtype, ?_⟩
  rw [injective_iff_map_eq_one]
  exact fun g hg => Subtype.ext ((hI.step i).stab_inj c.1 g.1 _ g.2 hg)

theorem not_dvd_card_stabP {X : Ch D u} (h : StabUnit X) (c : X.fm.clsP) : ¬ X.A.T ∣ Nat.card (X.fm.stabilizer₂ c) := fun hd =>
  h _ le_rfl (X.fm.til c) (hd.trans (Subgroup.card_dvd_of_injective (X.fm.stabMap c) (X.fm.stabMap_inj c)))

theorem stabUnit_of_concrete (X : Ch D u) {F : Fields} (hF : F.Ok) {Pr : Primes F} (W : Wts F Pr.Word D.R) {a : ℝ}
    (hS : Sizes Pr W a) (u' : Pr.Word) (hT : Pr.T u' = X.A.T)
    (sel : HeightOneSpectrum (𝓞 F.F) → HeightOneSpectrum (𝓞 F.E)) {S : Set ℕ} (mu : Tup F.F F.E F.K S)
    (cst : LocCst F (rowSG Pr sel mu)) (L : ChIdx F Pr D.R (QE sel (mu : Chr F.F F.E F.K)))
    (m2 : ℕ) (hm : D.R.m = m2 + 2) (b : L.β (m2 + 1)) (hY : YbHyp (R := D.R) sel mu cst L u' m2 b)
    (Λ : LevFam F.E F.K (D.R.N D.R.m) Pr.vGs) (Θ : LevQFam F.E F.K (D.R.N D.R.m) (QE sel (mu : Chr F.F F.E F.K)))
    (hlow : ∀ i, i ≤ m2 → ∀ c : X.C.cls i, ∃ (β : L.β i) (p : ((chF W sel mu L u' i).mem β).D),
      Nonempty (X.C.stab i c ≃* MulAction.stabilizer ((chF W sel mu L u' i).mem β).G p))
    (hmid : ∀ c : X.C.cls (m2 + 1), ∃ p : (ybCpl W sel mu cst L u' m2 b hY).Pts,
      Nonempty (X.C.stab (m2 + 1) c ≃* pairStab (ybCpl W sel mu cst L u' m2 b hY) p))
    (htop : ∀ c : X.C.cls D.R.m, ∃ p : (frmGSD (colValF W sel mu u' D.R.m) Λ Θ).D,
      Nonempty (X.C.stab D.R.m c ≃* MulAction.stabilizer (frmGSD (colValF W sel mu u' D.R.m) Λ Θ).G p)) :
    StabUnit X := by
  have hp : (Pr.T u').Prime := hT ▸ X.A.T_prime
  intro i hi c
  rw [← hT]
  rcases (show i ≤ m2 ∨ i = m2 + 1 ∨ i = D.R.m by omega) with h | rfl | rfl
  · obtain ⟨β, p, ⟨e⟩⟩ := hlow i h c
    rw [Nat.card_congr e.toEquiv]
    exact not_dvd_card_chF sel mu L hF hS u' hp hi β p
  · obtain ⟨p, ⟨e⟩⟩ := hmid c
    rw [Nat.card_congr e.toEquiv]
    exact not_dvd_card_cpl sel mu cst L hF hS u' hp hi b hY p
  · obtain ⟨p, ⟨e⟩⟩ := htop c
    rw [Nat.card_congr e.toEquiv]
    exact not_dvd_card_stabilizer_over hF hS u' hp le_rfl Λ Θ (G := (frmGSD (colValF W sel mu u' D.R.m) Λ Θ).G)
      (MonoidHom.id _) Function.injective_id id (fun _ _ => rfl) p

end Record

end GlobalTheory.LvT.StabOrder
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ParameterInequalitiesGoodStatement
section
open GlobalTheory.NT Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory Formalism.BasicNotions NumberField IsDedekindDomain
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.parameter_inequalities_good : ∀ eps : ℝ, 0 < eps → eps < 1 / 52 → ∃ Cb x₀ : ℝ, 0 < Cb ∧ ∀ s : Scale, s.eps = eps → x₀ ≤ s.x → ∀ n L₂ : ℕ, s.x ^ (eps / 4) ≤ (n : ℝ) → (n : ℝ) ≤ 2 * s.x ^ Formalism.MainNotions.G.hG s → (L₂ : ℝ) ≤ 1242 / eps → (Formalism.MainNotions.G.orbitSmallMultiplicity (Formalism.MainNotions.G.rG s) (Formalism.MainNotions.G.hG s) s.x + 1) * ((6 * Formalism.MainNotions.G.rG s + 1) * Formalism.MainNotions.G.goodU s.delta1) ≤ n ∧ (n : ℝ) * (L₂.choose (Formalism.MainNotions.G.KG s) : ℝ) * s.delta1 ^ Formalism.MainNotions.G.KG s + n * (1 - Formalism.G0.markedBound s.delta1 (Formalism.MainNotions.G.rG s) (Formalism.MainNotions.G.goodU s.delta1)) ^ Formalism.MainNotions.G.orbitSmallMultiplicity (Formalism.MainNotions.G.rG s) (Formalism.MainNotions.G.hG s) s.x + n * Formalism.G0.binUpper (Formalism.MainNotions.G.goodG' (Formalism.MainNotions.G.rG s) s.delta1 (Formalism.MainNotions.G.hG s) s.x) s.delta1 (Formalism.MainNotions.G.orbitWindowCount (Formalism.MainNotions.G.rG s) s.delta1 (Formalism.MainNotions.G.hG s) s.x - 1) ≤ Cb * s.x ^ (-2 : ℝ) := by
  first | exact @GlobalTheory.OrbitTerms.orbit_terms_le | exact GlobalTheory.OrbitTerms.orbit_terms_le | (intros; apply GlobalTheory.OrbitTerms.orbit_terms_le <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.RayClassFamilyPsiWithExceptionalZeroStatement
section
open Complex ArithmeticFunction MeasureTheory Filter Topology NumberField GlobalTheory.Hk GlobalTheory.Mem
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rayClassFamily_psi_with_exceptional_zero : ∀ c₀ : ℝ, 0 < c₀ → c₀ ≤ 1 / 20 → ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ (𝓕 : LFam) (χ : AddChar 𝓕.G ℂ) (Z : Finset ℝ) (u : ℝ), 𝓕.ExcZ χ c₀ Z → 2 ≤ u → Real.log 𝓕.B ≤ Real.sqrt (Real.log u) → ‖𝓕.psi χ u - (if χ = 1 then (u : ℂ) else 0) + ∑ β ∈ Z, (u : ℂ) ^ (β : ℂ) / (β : ℂ)‖ ≤ C * u * Real.exp (-c * Real.sqrt (Real.log u)) := by
  first | exact @GlobalTheory.Hk.PsiExc.psi_exceptional | exact GlobalTheory.Hk.PsiExc.psi_exceptional | (intros; apply GlobalTheory.Hk.PsiExc.psi_exceptional <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.SzRowLaRhoBotStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.LevelStarExponents Formalism.MainNotions Formalism.MainNotions.Inhab GlobalTheory.EX NumberField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sizes_sizeLa_sizeRho_sizeBot : SzRow (fun _ _ L => SizeLa L ∧ SizeRho L ∧ SizeBot L) := by
  first | exact @GlobalTheory.EX.szRow_la_rho_bot | exact GlobalTheory.EX.szRow_la_rho_bot | (intros; apply GlobalTheory.EX.szRow_la_rho_bot <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.SzRowRankPolysLeTO
section
open Formalism.BasicNotions Formalism.BasicNotions.LevelStarExponents Formalism.MainNotions Formalism.MainNotions.Inhab GlobalTheory.EX NumberField

namespace GlobalTheory.EX

theorem four_polys_le_of_cube_le (d n r y T : ℝ) (hd0 : 0 ≤ d) (hn0 : 0 ≤ n) (_hr0 : 0 ≤ r)
    (hd : d ≤ y) (hn : n ≤ y) (hr : r ≤ y) (hy : 10000 ≤ y) (hT : y ^ 3 ≤ T) :
    (d + 2) * n + 2 * r ≤ T ∧ 40 * (d + 2) ≤ T ∧ 11 * d ^ 2 ≤ T ∧
      r + 2 * (2 * 5 ^ 4 * r) * (d + 1) ≤ T := by
  have hy0 : 0 ≤ y := by linarith
  have h1 : 10000 * y ≤ y * y := mul_le_mul_of_nonneg_right hy hy0
  have h2 : 10000 * (y * y) ≤ T := by
    have : 10000 * (y * y) ≤ y * (y * y) := mul_le_mul_of_nonneg_right hy (mul_nonneg hy0 hy0)
    have e : y * (y * y) = y ^ 3 := by ring
    linarith
  have hdn : d * n ≤ y * y := mul_le_mul hd hn hn0 hy0
  have hdd : d * d ≤ y * y := mul_le_mul hd hd hd0 hy0
  have hrd : r * d ≤ y * y := mul_le_mul hr hd hd0 hy0
  refine ⟨?_, ?_, ?_, ?_⟩ <;> nlinarith

theorem szRow_rank_polys_le_TO :
    SzRow (fun C D L => (((D.R.f * D.R.r.choose 2 : ℕ) + 2) * (nWv D.R L.sc : ℕ) + 2 * D.R.r ≤ (TOv L.sc : ℕ)) ∧ (40 * ((D.R.f * D.R.r.choose 2 : ℕ) + 2) ≤ (TOv L.sc : ℕ)) ∧ (11 * (D.R.f * D.R.r.choose 2 : ℕ) ^ 2 ≤ (TOv L.sc : ℕ)) ∧ (D.R.r + 2 * (2 * 5 ^ 4 * D.R.r) * ((D.R.f * D.R.r.choose 2 : ℕ) + 1) ≤ (TOv L.sc : ℕ))) := by
  intro eps he he' C _
  obtain ⟨x0, hx0⟩ := GlobalTheory.EX.rank_basic_bounds eps he he'
  refine ⟨0, fun cD _ => ⟨0, fun ch _ => ⟨max x0 10000, fun D L heps hx hV => ?_⟩⟩⟩
  obtain ⟨-, -, hr, -, -, -, -, -, -, hD, -, hnW, -⟩ :=
    hx0 L.sc D.R heps (le_trans (le_max_left _ _) hx) hV.ranks
  have hx1 : (10000 : ℝ) ≤ L.sc.x := le_trans (le_max_right _ _) hx
  have hx2 : (1 : ℝ) ≤ L.sc.x := by linarith
  have mono : ∀ a b : ℝ, a ≤ b → L.sc.x ^ a ≤ L.sc.x ^ b :=
    fun a b h => Real.rpow_le_rpow_of_exponent_le hx2 h
  have hy : (10000 : ℝ) ≤ L.sc.x ^ (23 : ℝ) := by
    have := mono 1 23 (by norm_num)
    rw [Real.rpow_one] at this
    linarith
  have hT : (L.sc.x ^ (23 : ℝ)) ^ 3 ≤ (TOv L.sc : ℝ) := by
    have e : (L.sc.x ^ (23 : ℝ)) ^ 3 = L.sc.x ^ (69 : ℝ) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by linarith)]
      norm_num
    rw [e]
    exact le_trans (mono 69 377 (by norm_num)) (Nat.le_ceil _)
  obtain ⟨h1, h2, h3, h4⟩ := four_polys_le_of_cube_le
    ((D.R.f * D.R.r.choose 2 : ℕ) : ℝ) (nWv D.R L.sc : ℝ) (D.R.r : ℝ) (L.sc.x ^ (23 : ℝ)) (TOv L.sc : ℝ)
    (Nat.cast_nonneg _) (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    (hD.trans (mono _ _ (by norm_num))) (hnW.trans (mono _ _ (by norm_num)))
    (hr.trans (mono _ _ (by norm_num))) hy hT
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact_mod_cast h1
  · exact_mod_cast h2
  · exact_mod_cast h3
  · exact_mod_cast h4

end GlobalTheory.EX
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.SzRowRankSizesStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.LevelStarExponents Formalism.MainNotions Formalism.MainNotions.Inhab GlobalTheory.EX NumberField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sizes_sizeN_sizeM_sizeK_sizeT_sizeTT_sizeDe2_sizeLw : SzRow (fun _ _ L => SizeN L ∧ SizeM L ∧ SizeK L ∧ SizeT L ∧ SizeTT L ∧ SizeDe2 L ∧ SizeLw L) := by
  first | exact @GlobalTheory.EX.szRow_rankSizes | exact GlobalTheory.EX.szRow_rankSizes | (intros; apply GlobalTheory.EX.szRow_rankSizes <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.SzRowTOPPLeBStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.LevelStarExponents Formalism.MainNotions Formalism.MainNotions.Inhab GlobalTheory.EX NumberField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sizes_TOv_mul_PP_le_b_and_sqrt_b : SzRow (fun C D L => (((TOv L.sc : ℕ) : ℝ) * (C.T.CP * zBase L ^ C.T.eP) * L.sc.x ^ C.T.Cb ≤ L.sc.b) ∧ (((TOv L.sc : ℕ) : ℝ) * (C.T.CP * zBase L ^ C.T.eP) ≤ L.sc.b ^ (1 / 2 : ℝ)) ∧ ((C.T.CP * zBase L ^ C.T.eP) ^ 3 * ((TOv L.sc : ℕ) : ℝ) ^ 2 * L.sc.x ^ C.T.Cb ≤ L.sc.b) ∧ ((C.T.CP * zBase L ^ C.T.eP) ^ 3 * ((TOv L.sc : ℕ) : ℝ) ^ 2 ≤ L.sc.b ^ (1 / 2 : ℝ))) := by
  first | exact @GlobalTheory.EX.szRow_TO_PP_le_b | exact GlobalTheory.EX.szRow_TO_PP_le_b | (intros; apply GlobalTheory.EX.szRow_TO_PP_le_b <;> assumption)
end

