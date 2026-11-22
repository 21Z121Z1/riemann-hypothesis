import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0005
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0521
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0490
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0017
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.OneSubPhiOntoOfFilZero
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0006
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0474
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BdRpToBdR
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0497
import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0006
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0003
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0303
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0512
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0266
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsBasisDD
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0496
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsGaloisPrescribedUnramifiedKummer
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0008
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0434
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0492
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0375
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0494
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0399
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0378
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0511
import Development.AbelianVarietyTheory.CrystallinePeriods.RingIface
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0488
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0498

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EisensteinDvdOfDvdRestrictClosedDisc
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP

theorem dvd_of_dvd_restrict_discS : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (ρ : ℝ≥0), bk.ρ₀ ≤ ρ → ρ < 1 → ∀ R : bk.DS ρ →+* bk.DS bk.ρ₀, IsDiscMap (RingHom.id bk.S) R → ∀ y, toDisc l (X : bk.S) bk.ρ₀ bk.E ∣ R y → toDisc l (X : bk.S) ρ bk.E ∣ y := by
  intro l _ K bk ρ h0 h1 R hR y hy
  obtain ⟨q, k, r, hr, e⟩ := GlobalTheory.T.weierstrass_division_closedDisc_breuilKisin l K bk ρ h0 h1 y
  have e' := congrArg R e
  rw [map_mul, map_add, map_mul, hR.ext, hR.ext, RingHom.id_apply, RingHom.id_apply] at e'
  have hd : toDisc l (X : bk.S) bk.ρ₀ bk.E ∣ toDisc l (X : bk.S) bk.ρ₀ (r : bk.S) := by
    have h2 := hy.mul_left (R (((l : ℕ) : bk.DS ρ) ^ k))
    rw [e'] at h2
    exact (dvd_add_right (dvd_mul_right _ _)).1 h2
  have hr0 := GlobalTheory.T.breuilKisin_poly_eq_zero_of_disc_dvd l K bk r hr hd
  rw [hr0, Polynomial.coe_zero, map_zero, add_zero] at e
  exact ((isUnit_l_disc l (X : bk.S) ρ).pow k).dvd_mul_left.1 ⟨q, e⟩

end GlobalTheory.BSP
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EisensteinPowSmulValueEqSumBasis
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per
open GlobalTheory.BKGal.HatVal
open scoped GlobalTheory.BKGal.HatVal

theorem GlobalTheory.BKGal.HatVal.Epow_smul_jB_toBcris_eq_sum : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] [TameDescentExponentData K l e a] (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e) (ι : Type) [Fintype ι] [DecidableEq ι] (η H : ℕ) (D : BKDat O K l e a ι η H) (T : LocLat (Gl l) ℚ_[l] K O) (R : GalDat t ϖ (sQ l) D T) (σ : D.MMl) (c : ι → ι → OA l O), (∀ j, inclL t ϖ D.toPhiMod (c j) = inclO l O (((1 : O) ⊗ₜ[ℤ_[l]] ϖ.ev a (eis l a e) : OA l O) ^ H) • (Pi.single j 1 : ι → OW l O)) → ∃ s : ι → ZMod a → invL l (S O K e), (∀ j τ, (s j τ : K⟦X⟧) = E K l e ^ η * σ.1 τ j) ∧ toB l O ((1 : O) ⊗ₜ[ℤ_[l]] ϖ.ev a (eis l a e) : OA l O) ^ (H + η) • R.jB (toBcris t ϖ D.toPhiMod σ) = ∑ j, ϖ.iB t K (s j) • R.jB (fun i => toB l O (c j i)) := by
  intro l _ a e _ _ O K _ _ _ _ _ _ _ _ _ _ t ϖ ι _ _ η H D T R σ c hc
  have hσM : E K l e ^ η • σ.1 ∈ D.Mext (invL l (S O K e)) :=
    D.smul_mem_Mext (le_trans (A_le_S l e) (le_away _ _)) σ.2
  refine ⟨fun j τ => ⟨E K l e ^ η * σ.1 τ j, mem_tot.1 hσM τ j⟩, fun j τ => rfl, ?_⟩
  set ej : ι → Vec K a ι := fun j _ => Pi.single j 1 with hej
  have hejM : ∀ j, ej j ∈ D.M := fun j => mem_tot.2 fun τ => mem_vecs.2 fun i => by
    simp only [hej]
    rcases eq_or_ne i j with rfl | h
    · rw [Pi.single_eq_same]; exact one_mem _
    · rw [Pi.single_eq_of_ne h]; exact zero_mem _
  have hL : ∀ j, E K l e ^ H • ej j ∈ D.L := fun j => D.lower _ (hejM j)
  have hcol : ∀ j τ i, (D.mxInv τ *ᵥ (E K l e ^ H • ej j) τ) i = E K l e ^ H * D.mxInv τ i j := by
    intro j τ i
    simp only [hej, Pi.smul_apply, Matrix.mulVec_smul, Matrix.mulVec_single_one, smul_eq_mul,
      Matrix.col_apply, Matrix.transpose_apply]
  have hℓ : ∀ j i τ, E K l e ^ H * D.mxInv τ i j ∈ A O K := fun j i τ => by
    rw [← hcol]; exact D.mem_extc_iff.1 (mem_tot.1 (hL j) τ) i
  set ℓ : ι → ι → ZMod a → A O K := fun j i τ => ⟨_, hℓ j i τ⟩ with hℓdef
  have hcj : ∀ j, c j = fun i => ϖ.iTot t K (ℓ j i) := by
    intro j
    apply inclL_injective t ϖ D.toPhiMod
    rw [hc j]
    have hv : E K l e ^ H • ej j ∈ ME D.toPhiMod := mem_ME_of_mem_L (hL j)
    have h1 := toW_of_mx t ϖ D.toPhiMod ⟨_, hv⟩ (ℓ j) (fun τ => by
      have h2 : (fun i => ((ℓ j i τ : A O K) : K⟦X⟧)) = D.mxInv τ *ᵥ (E K l e ^ H • ej j) τ :=
        funext fun i => (hcol j τ i).symm
      change (E K l e ^ H • ej j) τ = D.mx τ *ᵥ fun i => ((ℓ j i τ : A O K) : K⟦X⟧)
      rw [h2, Matrix.mulVec_mulVec, D.mx_mul_mxInv, Matrix.one_mulVec])
    rw [← inclL_apply] at h1
    rw [← h1]
    ext1 i
    rw [toW_apply, Pi.smul_apply, smul_eq_mul]
    rcases eq_or_ne i j with rfl | h
    · have h3 : (fun τ => (⟨(E K l e ^ H • ej i) τ i, mem_tot.1 hv τ i⟩ : invE l e (A O K))) =
          fun τ => ⟨(((fun _ => EIn l e (A O K)) ^ H : ZMod a → A O K) τ : K⟦X⟧),
            le_away _ _ (((fun _ => EIn l e (A O K)) ^ H : ZMod a → A O K) τ).2⟩ :=
        funext fun τ => Subtype.ext (by simp [hej, EIn])
      rw [h3, ϖ.iW_of_mem t K]
      simp only [map_pow, ϖ.iTot_E t K, Pi.single_eq_same, mul_one]
    · have h3 : (fun τ => (⟨(E K l e ^ H • ej j) τ i, mem_tot.1 hv τ i⟩ : invE l e (A O K))) = 0 :=
        funext fun τ => Subtype.ext (by simp [hej, Pi.single_eq_of_ne h])
      rw [h3, map_zero, Pi.single_eq_of_ne h, mul_zero]
  have hB : ∀ f : ZMod a → A O K, toB l O (ϖ.iTot t K f) =
      ϖ.iB t K (fun τ => ⟨f τ, le_away _ _ (A_le_S l e (f τ).2)⟩) := fun f => by
    rw [toB, AlgHom.comp_apply, ← ϖ.iC_of_mem t K, ← ϖ.iB_of_mem t K]
  have hE : toB l O ((1 : O) ⊗ₜ[ℤ_[l]] ϖ.ev a (eis l a e) : OA l O) =
      toB l O (ϖ.iTot t K (fun _ => EIn l e _)) := by rw [ϖ.iTot_E t K]
  rw [← LinearEquiv.map_smul]
  simp only [← LinearEquiv.map_smul, ← map_sum]
  congr 1
  funext i
  simp only [Pi.smul_apply, Finset.sum_apply, smul_eq_mul, toBcris_apply, hE, hcj, hB, ← map_pow, ← map_mul,
    ← map_sum]
  congr 1
  funext τ
  apply Subtype.ext
  simp only [Pi.mul_apply, Pi.pow_apply, Finset.sum_apply, Subalgebra.coe_mul, Subalgebra.coe_pow,
    AddSubmonoidClass.coe_finsetSum, hℓdef]
  change (E K l e) ^ (H + η) * (D.mxInv τ *ᵥ σ.1 τ) i = ∑ j, E K l e ^ η * σ.1 τ j * (E K l e ^ H * D.mxInv τ i j)
  simp only [Matrix.mulVec, dotProduct, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EmbeddingProductSeriesToTensorBcrisInjectiveFinEStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.embeddingProductSeriesToTensorBcris_injective_finExt : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (LL : FinExt l) (t : Wq l a →ₐ[ℤ_[l]] ↥(OL LL)) (ϖ : PiSys l e), Function.Injective (ϖ.iB t ↥LL.1) := by
  first | exact @GlobalTheory.BKReal.IBInj.iB_injective_finExt | exact GlobalTheory.BKReal.IBInj.iB_injective_finExt | (intros; apply GlobalTheory.BKReal.IBInj.iB_injective_finExt <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EtaleComparisonOfWachBasis
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL Formalism.MainNotions.DeltaInvariantLattices

noncomputable section

namespace GlobalTheory.NL.NygaardExtension

theorem map_incl_smul {O R R' M : Type} [CommRing O] [CommRing R] [CommRing R'] [Algebra O R]
    [Algebra O R'] [AddCommGroup M] [Module O M] (f : R →ₐ[O] R') (a : R) (y : R ⊗[O] M) :
    TensorProduct.map f.toLinearMap (LinearMap.id : M →ₗ[O] M) (a • y) =
      f a • TensorProduct.map f.toLinearMap (LinearMap.id : M →ₗ[O] M) y := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | add x x' hx hx' => simp only [smul_add, map_add, hx, hx']
  | tmul r u => simp [TensorProduct.smul_tmul']

section Generic

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL]
    [CommRing O] [Algebra O LL] [TopologicalSpace LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    {W : LocWach PD LL O v n} {RA RW : Type} [CommRing RA] [CommRing RW] [Algebra O RA]
    [Algebra O RW] {inclR : RA →ₐ[O] RW} {φR : RW →ₐ[O] RW} {gR : G → (RW →ₐ[O] RW)} {πA : RA}
    (E : EtTie W RA RW inclR φR gR πA)

theorem TAinf_smul (T : LocLat G Qp LL O) (a : RA) {z : TW RW T} (hz : z ∈ TAinf inclR T) :
    inclR a • z ∈ TAinf inclR T := by
  obtain ⟨y, rfl⟩ := hz
  exact ⟨a • y, map_incl_smul inclR a y⟩

theorem NAinf_smul (T : LocLat G Qp LL O) (a : RA) {z : TW RW T} (hz : z ∈ NAinf W E T) :
    inclR a • z ∈ NAinf W E T := by
  induction hz using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨a', x, hx, rfl⟩ := hz
    refine Submodule.subset_span ⟨a * a', x, hx, ?_⟩
    rw [smul_smul, map_mul]
  | zero => rw [smul_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [smul_add]; exact add_mem hx hy
  | smul o x _ hx => rw [smul_comm]; exact Submodule.smul_mem _ o hx

theorem p5inf_of_sand (T : LocLat G Qp LL O) (c : RW) (m : ℕ) (hc : c = inclR (E.io W.X) ^ m)
    (h1 : ∀ x ∈ W.N T, ∃ y : TW RA T, TWincl inclR T y =
        TensorProduct.map (LinearMap.mulLeft O c) LinearMap.id (E.jD T x))
    (h2 : ∀ t : ↥T.L.T, (c ⊗ₜ[O] t : TW RW T) ∈ Submodule.span O {z : TW RW T | ∃ a : RA, ∃ y ∈ W.N T,
        z = TensorProduct.map (LinearMap.mulLeft O (inclR a)) LinearMap.id (E.jD T y)}) :
    wachInfiniteLevelJumpBound W E T m m := by
  subst hc
  simp only [GlobalTheory.NL.SandArb.map_mulLeft] at h1 h2
  refine ⟨fun z hz => ?_, fun z hz => ?_⟩
  · obtain ⟨y, rfl⟩ := hz
    induction y using TensorProduct.induction_on with
    | zero => rw [map_zero, smul_zero]; exact zero_mem _
    | add x x' hx hx' => rw [map_add, smul_add]; exact add_mem hx hx'
    | tmul r t =>
      have e : inclR (E.io W.X) ^ m • TensorProduct.map inclR.toLinearMap LinearMap.id (r ⊗ₜ[O] t) =
          inclR r • ((inclR (E.io W.X) ^ m) ⊗ₜ[O] t : TW RW T) := by
        simp [TensorProduct.smul_tmul', mul_comm]
      rw [e]
      exact NAinf_smul E T r (h2 t)
  · induction hz using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨a, x, hx, rfl⟩ := hz
      obtain ⟨y, hy⟩ := h1 x hx
      rw [smul_comm]
      exact TAinf_smul T a ⟨y, hy⟩
    | zero => rw [smul_zero]; exact zero_mem _
    | add x y _ _ hx hy => rw [smul_add]; exact add_mem hx hy
    | smul o x _ hx => rw [smul_comm]; exact Submodule.smul_mem _ o hx

theorem etale_comparison_of_wach_basis (T : LocLat G Qp LL O) (hT : IsCrys PD T.ρ) {r : ℕ}
    (b : Module.Basis (Fin r) (LetA O n) ↥(W.N T))
    (hφ : ∀ y : TW RW T, TWmap φR T y = y ↔ ∃ t : ↥T.L.T, y = (1 : RW) ⊗ₜ[O] t) : p1et W E T := by
  obtain ⟨c, hc⟩ := GlobalTheory.WachTensor.exists_basis_jD E T ((W.N_base T hT).basis b)
  have hc' : ∀ j, c j = E.jD T (b j : W.DD T) := fun j => by
    rw [hc, IsBaseChange.basis_apply b (W.N_base T hT) j]; rfl
  refine ⟨⟨r, fun j => (b j : W.DD T), fun j => (b j).2, fun x hx => ?_, fun y => ?_⟩, hφ⟩
  · have key : ∀ a : Fin r → LetA O n, x = ∑ j, a j • (b j : W.DD T) ↔
        (⟨x, hx⟩ : ↥(W.N T)) = ∑ j, a j • b j := by
      intro a
      rw [Subtype.ext_iff]
      simp
    refine ⟨fun j => b.repr ⟨x, hx⟩ j, (key _).2 (b.sum_repr ⟨x, hx⟩).symm, fun a ha => ?_⟩
    rw [(key a).1 ha, b.repr_sum_self]
  · refine ⟨fun j => c.repr y j, ?_, fun a ha => ?_⟩
    · show y = _
      simp only [← hc']
      exact (c.sum_repr y).symm
    · have ha' : y = ∑ j, a j • c j := by simpa only [← hc'] using ha
      rw [ha', c.repr_sum_self]

end Generic

set_option maxHeartbeats 1600000 in

theorem main : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW),
    p1eL D.loc D.locA HW F := by
  intro D HW F l _ K s LL h T hT
  refine ⟨?_, ?_⟩
  · obtain ⟨b⟩ := N_basis D HW F l K s LL h T hT
    exact etale_comparison_of_wach_basis _ T hT b (GlobalTheory.WittTensorFixed.main l K LL T).2.1
  · obtain ⟨m, h1, h2⟩ := GlobalTheory.NL.SandArb.sandwich D HW F l K s LL h T hT
    exact ⟨m, p5inf_of_sand _ T _ m rfl h1 h2⟩

end GlobalTheory.NL.NygaardExtension
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsAinfLiftPeriodPowSmulIntertwinerStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
open Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_ainf_lift_period_pow_smul_intertwiner : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (τ : Ainf l), bk.IsPer τ → ∀ (d d' : ℕ) (S : Strat bk d) (S' : Strat bk d') (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) ℤ_[l]) (ρ' : ↥(GK K) → Matrix (Fin d') (Fin d') ℤ_[l]) (T : Matrix (Fin d) (Fin d) (WCb l)) (T' : Matrix (Fin d') (Fin d') (WCb l)), MReal S ρ T → MReal S' ρ' T' → ∀ (f : Matrix (Fin d') (Fin d) ℤ_[l]) (X : Matrix (Fin d') (Fin d) (WCb l)), T' * X = zW f * T → ∃ (M : ℕ) (x : Matrix (Fin d') (Fin d) (Ainf l)), x.map (inclW l) = inclW l τ ^ M • X := by
  first | exact @GlobalTheory.BSP.PoleBound.exists_pow_smul | exact GlobalTheory.BSP.PoleBound.exists_pow_smul | (intros; apply GlobalTheory.BSP.PoleBound.exists_pow_smul <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsAlgEquivExtendingWittTiltFrobeniusStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
open Matrix

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_algEquiv_extending_wittTiltFrobenius : ∀ (l : ℕ) [Fact l.Prime] (a : ℕ) [NeZero a], ∃ Φ : Om l ≃ₐ[ℚ_[l]] Om l,
    ∀ w : Wq l a, Φ (GlobalTheory.TameFrob.iotaO l a w) = GlobalTheory.TameFrob.iotaO l a (sigma l a w) := by
  first | exact @GlobalTheory.TameFrob.exists_algEquiv_iotaO_sigma | exact GlobalTheory.TameFrob.exists_algEquiv_iotaO_sigma | (intros; apply GlobalTheory.TameFrob.exists_algEquiv_iotaO_sigma <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsBaseEqOfClosedDiscExtendsNormLeOne
section
noncomputable section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP

theorem exists_toDisc_eq_of_extends_norm_le_one : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (A : Type)
    [CommRing A] (s : bk.S →+* A) (ι : Type), TopBasis s bk.J ι → ∀ ρ : ℝ≥0, 0 < ρ → ρ < 1 →
    ∀ y : Disc l (s X) ρ, (∀ ρ₁ : ℝ≥0, ρ₁ < 1 → ∃ (ρ' : ℝ≥0) (R : Disc l (s X) ρ' →+* Disc l (s X) ρ)
      (y' : Disc l (s X) ρ'), ρ₁ ≤ ρ' ∧ ρ ≤ ρ' ∧ ρ' < 1 ∧ IsDiscMap (RingHom.id A) R ∧ R y' = y ∧ ‖y'‖ ≤ 1) →
    ∃ a, toDisc l (s X) ρ a = y := by
  intro l _ K bk A _ s ι TB ρ hρ hρ1 y hy
  have hj : ∀ ρ' : ℝ≥0, 0 < ρ' → ∃ j : bk.DS ρ' →+* Disc l (s X) ρ', IsDiscMap s j := fun ρ' h =>
    GlobalTheory.T.exists_closedDiscExtension_of_pow_dvd l bk.S A s X (s X) ρ' ρ' 1 h (by rw [pow_one]) (by rw [pow_one])
  obtain ⟨j, hjd⟩ := hj ρ hρ
  obtain ⟨cD, hc1, -, hc3, hc4, -, hc6, -, -⟩ := GlobalTheory.T.closedDisc_coefficients_topologicallyFree l K bk A s ι TB ρ hρ hρ1 j hjd

  have hz : ∀ i, ∃ z : bk.S, toDisc l (X : bk.S) ρ z = cD i y := by
    intro i
    apply GlobalTheory.T.disc_bounded_function_isPowerSeries l K bk ρ hρ hρ1
    intro ρ₁ hρ₁
    obtain ⟨ρ', R, y', h1, h2, h3, hR, hRy, hy'⟩ := hy ρ₁ hρ₁
    have hρ' : 0 < ρ' := hρ.trans_le h2
    obtain ⟨j', hj'd⟩ := hj ρ' hρ'
    obtain ⟨cD', hc1', -, hc3', -⟩ := GlobalTheory.T.closedDisc_coefficients_topologicallyFree l K bk A s ι TB ρ' hρ' h3 j' hj'd
    obtain ⟨RS, hRS⟩ := GlobalTheory.T.exists_closedDiscExtension_of_pow_dvd l bk.S bk.S (RingHom.id _) X X ρ' ρ 1 hρ (by simp) (by simpa using h2)
    refine ⟨ρ', RS, cD' i y', h1, h2, h3, hRS, ?_, (hc3' i y').trans hy'⟩

    have htor : ∀ z : bk.DS ρ, l • z = 0 → z = 0 := fun z hz => by
      rw [nsmul_eq_mul] at hz
      exact (isUnit_l_disc l (X : bk.S) ρ).mul_right_eq_zero.1 hz
    have hF : Continuous ((RS : bk.DS ρ' →+ bk.DS ρ).comp (cD' i)) :=
      AddMonoidHomClass.continuous_of_bound _ 1 fun x => by
        show ‖RS (cD' i x)‖ ≤ 1 * ‖x‖
        rw [one_mul]; exact (hRS.norm_le _).trans (hc3' i x)
    have hG : Continuous ((cD i).comp (R : Disc l (s X) ρ' →+ Disc l (s X) ρ)) :=
      AddMonoidHomClass.continuous_of_bound _ 1 fun x => by
        show ‖cD i (R x)‖ ≤ 1 * ‖x‖
        rw [one_mul]; exact (hc3 i _).trans (hR.norm_le x)
    have key := (GlobalTheory.T.closedDiscGaugeCompletion_basic_properties l A (s X) ρ').2.2.1 (bk.DS ρ) htor _ _ hF hG fun a => by
      show RS (cD' i (toDisc l (s X) ρ' a)) = cD i (R (toDisc l (s X) ρ' a))
      rw [hc1', hRS.ext, hR.ext, hc1]; rfl
    rw [← hRy]
    exact DFunLike.congr_fun key y'
  choose z hz using hz

  haveI : IsAdicComplete bk.J bk.S := bk.complete
  have hfin : ∀ n : ℕ, {i | z i ∉ bk.J ^ n}.Finite := by
    intro n
    obtain ⟨r, hr, hr'⟩ := (GlobalTheory.T.closedDisc_toDisc_injective_of_adicBasis l K bk bk.S (RingHom.id _) Unit (TopBasis.self bk.J) ρ hρ hρ1).2.1 n
    refine (Filter.mem_cofinite.1 (hc4 y (Metric.closedBall_mem_nhds 0 hr))).subset fun i hi h => hi ?_
    have h' : ‖toDisc l (X : bk.S) ρ (z i)‖ ≤ r := by
      rw [hz i]; simpa using h
    have := hr' (z i) h'
    rwa [Ideal.map_id] at this
  obtain ⟨a, ha⟩ := (GlobalTheory.T.topologicalBasis_basic_facts bk.S A s bk.J ι TB bk.complete.toIsHausdorff).2.2.2.1 z hfin
  refine ⟨a, ?_⟩
  have h0 : ‖y - toDisc l (s X) ρ a‖ ≤ 0 := hc6 _ 0 le_rfl fun i => by
    rw [map_sub, hc1, ha, hz, sub_self, norm_zero]
  exact (sub_eq_zero.1 (norm_le_zero_iff.1 h0)).symm

end GlobalTheory.BSP
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsBcrisTensorLatticeEquivPeriodRing
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

noncomputable section
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 10000000

namespace GlobalTheory.BKGal.CrisTensor

theorem mem_finiteCocycles_iff_bcrisTensor_coboundary {l : ℕ} [Fact l.Prime] {LL : FinExt l} (T : QLat LL) (Pl : LocPrime l)
    (hpow : ∀ v : T.V, ∃ n : ℕ, (l : ↥LL.1) ^ n • v ∈ T.L.T)
    (β : TW (OB l ↥(OL LL)) T ≃ₗ[↥(OL LL)] T.V ⊗[ℚ_[l]] Pl.R.B)
    (h1 : ∀ x : ↥T.L.T, β ((1 : OB l ↥(OL LL)) ⊗ₜ[↥(OL LL)] x) = (x : T.V) ⊗ₜ[ℚ_[l]] (1 : Pl.R.B))
    (h2 : ∀ g b, β (actB (sQ l) T g b) = actVB (Pl.PD (Formalism.MainNotions.ElementDenominator.qlExt l)) T.ρ g (β b))
    (c : Gl l → T.V) (hc : c ∈ continuousCocycles T.ρ) :
    c ∈ finiteCocycles (Pl.PD (Formalism.MainNotions.ElementDenominator.qlExt l)) T.ρ ↔ ∃ b, IsCobOf (sQ l) T b c := by
  have hl : ∀ n : ℕ, (l : ↥LL.1) ^ n ≠ 0 := fun n =>
    pow_ne_zero _ (Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero)
  have key : ∀ (b : TW (OB l ↥(OL LL)) T) (g : Gl l) (n : ℕ),
      β ((l : ↥(OL LL)) ^ n • (actB (sQ l) T g b - b)) =
        (l : ↥LL.1) ^ n • (actVB (Pl.PD (Formalism.MainNotions.ElementDenominator.qlExt l)) T.ρ g (β b) - β b) := by
    intro b g n
    have e1 := β.map_smul ((l : ↥(OL LL)) ^ n) (actB (sQ l) T g b - b)
    have e2 : β (actB (sQ l) T g b - b) = actVB (Pl.PD (Formalism.MainNotions.ElementDenominator.qlExt l)) T.ρ g (β b) - β b :=
      (map_sub β _ _).trans (congrArg (· - β b) (h2 g b))
    have e3 : (((l : ↥(OL LL)) ^ n : ↥(OL LL)) : ↥LL.1) = (l : ↥LL.1) ^ n := by simp
    rw [← e3, ← e2]
    exact e1
  have kx : ∀ (g : Gl l) (n : ℕ) (x : ↥T.L.T), (x : T.V) = (l : ↥LL.1) ^ n • c g →
      β ((1 : OB l ↥(OL LL)) ⊗ₜ[↥(OL LL)] x) = (l : ↥LL.1) ^ n • (c g ⊗ₜ[ℚ_[l]] (1 : Pl.R.B)) := by
    intro g n x hx
    rw [h1, hx]
    exact (TensorProduct.smul_tmul' _ _ _).symm
  constructor
  · rintro ⟨-, y, hy⟩
    obtain ⟨b, rfl⟩ := β.surjective y
    refine ⟨b, fun g n x hx => β.injective ?_⟩
    exact (kx g n x hx).trans ((congrArg (fun z => (l : ↥LL.1) ^ n • z) (hy g)).trans (key b g n).symm)
  · rintro ⟨b, hb⟩
    refine ⟨hc, β b, fun g => ?_⟩
    obtain ⟨n, hn⟩ := hpow (c g)
    have h3 := (kx g n ⟨_, hn⟩ rfl).symm.trans ((congrArg β (hb g n ⟨_, hn⟩ rfl)).trans (key b g n))
    have h4 := congrArg (fun z => ((l : ↥LL.1) ^ n)⁻¹ • z) h3
    simpa only [inv_smul_smul₀ (hl n)] using h4

theorem exists_equiv : ∀ (l : ℕ) [Fact l.Prime] (LL : FinExt l) (T : QLat LL) (Pl : LocPrime l) (AI : LocAinf l Pl), IsStd Pl AI → ∃ β : TW (OB l ↥(OL LL)) T ≃ₗ[↥(OL LL)] T.V ⊗[ℚ_[l]] Pl.R.B, (∀ x : ↥T.L.T, β ((1 : OB l ↥(OL LL)) ⊗ₜ[↥(OL LL)] x) = (x : T.V) ⊗ₜ[ℚ_[l]] (1 : Pl.R.B)) ∧ (∀ g b, β (actB (sQ l) T g b) = actVB (Pl.PD (Formalism.MainNotions.ElementDenominator.qlExt l)) T.ρ g (β b)) ∧ (∀ b, β (TWmap (frobOB l ↥(OL LL)) T b) = φVB (LL := ↥LL.1) (Pl.PD (Formalism.MainNotions.ElementDenominator.qlExt l)) (β b)) ∧ ∀ c ∈ continuousCocycles T.ρ, (c ∈ finiteCocycles (Pl.PD (Formalism.MainNotions.ElementDenominator.qlExt l)) T.ρ ↔ ∃ b, IsCobOf (sQ l) T b c) := by
  intro l _ LL T Pl AI hS
  obtain ⟨Ti⟩ := hS
  have hz : ∀ z : ℤ_[l], Ti.eB (algebraMap ℚ_[l] Pl.R.B (z : ℚ_[l])) = algebraMap ℤ_[l] (Per.Bcris l) z :=
    fun z => (Ti.zB z).trans (GlobalTheory.RingIface.aB_zl l z).symm
  exact ⟨linEquiv T Ti.eB hz, linEquiv_one T Ti.eB hz, linEquiv_act T Ti.eB hz Ti.actB,
    linEquiv_frob T Ti.eB hz Ti.frob,
    mem_finiteCocycles_iff_bcrisTensor_coboundary T Pl (exists_pow_smul_mem T) _ (linEquiv_one T Ti.eB hz) (linEquiv_act T Ti.eB hz Ti.actB)⟩

end GlobalTheory.BKGal.CrisTensor
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsBcrisTensorLatticeToDeRhamMapStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_bcrisTensorLattice_to_deRham_map : ∀ (l : ℕ) [Fact l.Prime] (Pl : LocPrime l) (AI : LocAinf l Pl) (Td : LocTied l Pl AI) (LL : FinExt l) (T : QLat LL), ∃ X : TW (OB l ↥(OL LL)) T →+ T.V ⊗[ℚ_[l]] Pl.R.BdR, ∀ (o : ↥(OL LL)) (b : Per.Bcris l) (x : ↥T.L.T), X ((o ⊗ₜ[ℤ_[l]] b) ⊗ₜ[↥(OL LL)] x) = ((o : ↥LL.1) • (x : T.V)) ⊗ₜ[ℚ_[l]] GlobalTheory.BKGal.JumpDR.cB Td b := by
  first | exact @GlobalTheory.BKGal.CrisTensDR.main | exact GlobalTheory.BKGal.CrisTensDR.main | (intros; apply GlobalTheory.BKGal.CrisTensDR.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsClosedDiscExtensionBreuilKisinHomStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_closedDisc_extension_breuilKisinHom : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K), ∀ (B : Obj l ↥(OL K)) (f g : Hom bk.prism B) (ρ : ℝ≥0), bk.ρ₀ ≤ ρ → ρ ≤ 1 → ∃ F : bk.DS ρ →+* Disc l (BK.hf f X) ρ, IsDiscMap (BK.hf g) F := by
  first | exact @GlobalTheory.BSP.DiscPrism.disc_map_exists | exact GlobalTheory.BSP.DiscPrism.disc_map_exists | (intros; apply GlobalTheory.BSP.DiscPrism.disc_map_exists <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsCoeffDeRhamPlusActionOnVTensorBdRStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_coeffDeRhamPlus_action_on_VTensorBdR : ∀ (l : ℕ) [Fact l.Prime] (Pl : LocPrime l) (AI : LocAinf l Pl) (Td : LocTied l Pl AI) (LL : FinExt l) (T : QLat LL), ∃ A : OD l ↥(OL LL) →+ (T.V ⊗[ℚ_[l]] Pl.R.BdR →+ T.V ⊗[ℚ_[l]] Pl.R.BdR), ∀ (o : ↥(OL LL)) (b : Per.BdRp l) (v : T.V) (c : Pl.R.BdR), A (o ⊗ₜ[ℤ_[l]] b) (v ⊗ₜ[ℚ_[l]] c) = ((o : ↥LL.1) • v) ⊗ₜ[ℚ_[l]] (GlobalTheory.BKGal.JumpDR.cD Td b * c) := by
  first | exact @GlobalTheory.BKGal.JumpDR.exists_odAction | exact GlobalTheory.BKGal.JumpDR.exists_odAction | (intros; apply GlobalTheory.BKGal.JumpDR.exists_odAction <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsCoversTameOfFrobeniusTeichmullerStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_coversTame_of_frobenius_teichmuller : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] [TameDescentExponentData K l e a] (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e) (k : GQ l) (s : ZMod a) (z : Fq l a), z ^ e = 1 → (∀ w : Wq l a, Per.σA k (wA l a w) = wA l a ((sigma l a ^ s.val) w)) → ϖ.kummer k = Fq.val l a z → ∃ γ : TameGal K l e a, Covers K t ϖ k γ := by
  first | exact @GlobalTheory.CoverGen.exists_covers_of_sigma_teich | exact GlobalTheory.CoverGen.exists_covers_of_sigma_teich | (intros; apply GlobalTheory.CoverGen.exists_covers_of_sigma_teich <;> assumption)
end

