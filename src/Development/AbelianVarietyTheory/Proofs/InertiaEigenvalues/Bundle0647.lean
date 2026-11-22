import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0635
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0638
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0435
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0446
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0481
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0462
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0005
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0014
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0404
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0594
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0561
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0374
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0643
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0161
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0640
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0554
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0562
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0003
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0011
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0639
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0015
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0637
import Formalism.SharpRestriction.LevelLetterCocycles.EmbeddingTypes
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0014
import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0015
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0007
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEtaleBasisLimitLatticeTower
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0641

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BlochKatoRightExact
section
noncomputable section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module

namespace GlobalTheory.BKRightExact

section Generic

variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR) {LL : Type} [Field LL] [Algebra Qp LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    {V' : Type} [AddCommGroup V'] [Module LL V'] [Module Qp V'] [IsScalarTower Qp LL V']

section Res

variable (L : Type) [Field L] [Algebra Qp L] [Algebra L LL] [Module L V] [IsScalarTower L LL V]
  [IsScalarTower Qp L V] (ρ : Representation LL G V)

def res : Representation L G V where
  toFun g := (ρ g).restrictScalars L
  map_one' := by ext; simp
  map_mul' g h := by ext; simp

theorem Dcris_res : Dcris PD (res L ρ) = (Dcris PD ρ).restrictScalars L := by
  ext x
  simp only [Dcris, Submodule.restrictScalars_mem, Submodule.mem_iInf, LinearMap.mem_ker,
    LinearMap.sub_apply, LinearMap.id_apply]
  rfl

theorem DdR_res : DdR PD (res L ρ) = (DdR PD ρ).restrictScalars L := by
  ext x
  simp only [DdR, Submodule.restrictScalars_mem, Submodule.mem_iInf, LinearMap.mem_ker,
    LinearMap.sub_apply, LinearMap.id_apply]
  rfl

theorem isCrys_res (h : IsCrys PD ρ) : IsCrys PD (res L ρ) := by
  unfold IsCrys at h ⊢
  rw [Dcris_res]
  change finrank L ↥(Dcris PD ρ) = _
  rw [← Module.finrank_mul_finrank L LL ↥(Dcris PD ρ), ← Module.finrank_mul_finrank L LL V, h,
    mul_left_comm]

theorem isDR_of_res [FiniteDimensional L LL] (h : IsDR PD (res L ρ)) : IsDR PD ρ := by
  unfold IsDR at h ⊢
  rw [DdR_res] at h
  change finrank L ↥(DdR PD ρ) = _ at h
  rw [← Module.finrank_mul_finrank L LL ↥(DdR PD ρ), ← Module.finrank_mul_finrank L LL V,
    mul_left_comm] at h
  exact Nat.eq_of_mul_eq_mul_left Module.finrank_pos h

end Res

variable (f : V →ₗ[LL] V')

theorem map_φVB (x : V ⊗[Qp] B) :
    AlgebraTensorModule.map f (LinearMap.id : B →ₗ[Qp] B) (φVB PD (LL := LL) x) =
      φVB PD (LL := LL) (AlgebraTensorModule.map f (LinearMap.id : B →ₗ[Qp] B) x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul v b => simp [φVB]
  | add x y hx hy => simp only [map_add, hx, hy]

theorem map_ιV (x : V ⊗[Qp] B) :
    AlgebraTensorModule.map f (LinearMap.id : BdR →ₗ[Qp] BdR) (ιV PD (LL := LL) x) =
      ιV PD (LL := LL) (AlgebraTensorModule.map f (LinearMap.id : B →ₗ[Qp] B) x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul v b => simp [ιV]
  | add x y hx hy => simp only [map_add, hx, hy]

theorem map_mem_FilV {a : ℤ} {y : V ⊗[Qp] BdR} (hy : y ∈ FilV PD (LL := LL) (V := V) a) :
    AlgebraTensorModule.map f (LinearMap.id : BdR →ₗ[Qp] BdR) y ∈ FilV PD (LL := LL) (V := V') a := by
  obtain ⟨z, rfl⟩ := hy
  refine ⟨AlgebraTensorModule.map f LinearMap.id z, ?_⟩
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul v b => simp
  | add x y hx hy => simp only [map_add, hx, hy]

theorem map_actVB {ρ : Representation LL G V} {ρ' : Representation LL G V'}
    (hf : ∀ g x, f (ρ g x) = ρ' g (f x)) (g : G) (x : V ⊗[Qp] B) :
    AlgebraTensorModule.map f (LinearMap.id : B →ₗ[Qp] B) (actVB PD ρ g x) =
      actVB PD ρ' g (AlgebraTensorModule.map f (LinearMap.id : B →ₗ[Qp] B) x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul v b => simp [actVB, hf]
  | add x y hx hy => simp only [map_add, hx, hy]

include PD in
theorem tmul_one_injective {v w : V} (h : v ⊗ₜ[Qp] (1 : B) = w ⊗ₜ[Qp] (1 : B)) : v = w := by
  have h1 : (1 : B) ≠ 0 := fun h0 => PD.not_mem_filtration_two (by
    rw [← mul_one PD.t, h0, mul_zero, map_zero]; exact Submodule.zero_mem _)
  obtain ⟨φ, hφ⟩ := Module.Projective.exists_dual_eq_one Qp h1
  have := congrArg (fun z => TensorProduct.rid Qp V (LinearMap.lTensor V φ z)) h
  simpa [hφ] using this

end Generic

theorem lift_periods {l : ℕ} [Fact l.Prime] {P : LocPrime l} {AI : LocAinf l P} (T : LocTied l P AI)
    (K : FinExt l) (LL : Type) [Field LL] [Algebra ℚ_[l] LL] [FiniteDimensional ℚ_[l] LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] LL V]
    [FiniteDimensional LL V] (ρ : Representation LL ↥(GK K) V)
    {V' : Type} [AddCommGroup V'] [Module LL V'] [Module ℚ_[l] V'] [IsScalarTower ℚ_[l] LL V']
    [FiniteDimensional LL V'] (ρ' : Representation LL ↥(GK K) V') (f : V →ₗ[LL] V')
    (hf : ∀ g x, f (ρ g x) = ρ' g (f x)) (hs : Function.Surjective f) (h : IsCrys (P.PD K) ρ) :
    IsDR (P.PD K) ρ' ∧
      (∀ y ∈ Dcris (P.PD K) ρ', ∃ x ∈ Dcris (P.PD K) ρ,
        AlgebraTensorModule.map f (LinearMap.id : P.R.B →ₗ[ℚ_[l]] P.R.B) x = y) ∧
      ∀ y ∈ DdR (P.PD K) ρ', ∃ x ∈ DdR (P.PD K) ρ,
        AlgebraTensorModule.map f (LinearMap.id : P.R.BdR →ₗ[ℚ_[l]] P.R.BdR) x = y := by
  let L : FinExt l := ⟨⊥, inferInstance⟩
  letI : Algebra ↥L.1 LL :=
    ((algebraMap ℚ_[l] LL).comp (IntermediateField.botEquiv ℚ_[l] (Om l)).toRingEquiv.toRingHom).toAlgebra
  haveI : IsScalarTower ℚ_[l] ↥L.1 LL := IsScalarTower.of_algebraMap_eq fun x =>
    (congrArg (algebraMap ℚ_[l] LL) ((IntermediateField.botEquiv ℚ_[l] (Om l)).commutes x)).symm
  haveI : FiniteDimensional ↥L.1 LL := Module.Finite.of_restrictScalars_finite ℚ_[l] _ _
  letI : Module ↥L.1 V := Module.compHom V (algebraMap ↥L.1 LL)
  letI : Module ↥L.1 V' := Module.compHom V' (algebraMap ↥L.1 LL)
  haveI : IsScalarTower ↥L.1 LL V := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  haveI : IsScalarTower ↥L.1 LL V' := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  haveI : IsScalarTower ℚ_[l] ↥L.1 V := IsScalarTower.to₁₂₄ ℚ_[l] ↥L.1 LL V
  haveI : IsScalarTower ℚ_[l] ↥L.1 V' := IsScalarTower.to₁₂₄ ℚ_[l] ↥L.1 LL V'
  haveI : FiniteDimensional ↥L.1 V := Module.Finite.trans LL V
  haveI : FiniteDimensional ↥L.1 V' := Module.Finite.trans LL V'
  have hc := isCrys_res (P.PD K) ↥L.1 ρ h
  have hd := (GlobalTheory.Per.CrisDR.isDR_of_isCrys l P AI T K L V _ hc).1
  obtain ⟨-, h1⟩ := (GlobalTheory.Per.CrysSubQuot.crys_sub_quot l P AI T K L V (res ↥L.1 ρ) V' (res ↥L.1 ρ')
    (f.restrictScalars ↥L.1) hf).2 hs hc
  obtain ⟨h2, h3⟩ := (GlobalTheory.DRSubQuot.deRham_sub_quot l P AI T K L V (res ↥L.1 ρ) V' (res ↥L.1 ρ')
    (f.restrictScalars ↥L.1) hf).2 hs hd
  rw [Dcris_res, Dcris_res] at h1
  rw [DdR_res, DdR_res] at h3
  refine ⟨isDR_of_res (P.PD K) ↥L.1 ρ' h2, h1, fun y hy => ?_⟩
  obtain ⟨a, ha⟩ := GlobalTheory.DRFil.exists_mem_FilV (P.PD K) (LL := ↥L.1) y
  obtain ⟨x, hx, hxy⟩ := h3 a y ⟨hy, ha⟩
  exact ⟨x, hx.1, hxy⟩

theorem bkARightExact_of_tied : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ K : FinExt l, Formalism.MainNotions.LocalSituation.bkARightExact (P.PD K) := by
  intro l _ P AI T K LL _ _ _ O _ _ hO A A' f hf hs hA _ c' hc'
  haveI := hO.2.1
  obtain ⟨hdr, hl1, hl2⟩ := lift_periods T K LL A.ρ A'.ρ f hf hs hA
  obtain ⟨-, x', hx'⟩ := hc'
  obtain ⟨hd1, d₂', hd2, hfil⟩ := GlobalTheory.T.crystalline_coboundary_lift l P AI T K LL O hO A' hdr c' x' hx'
  obtain ⟨d₁, hd₁, e₁⟩ := hl1 _ hd1
  obtain ⟨d₂, hd₂, e₂⟩ := hl2 _ hd2
  obtain ⟨x, y, c, hy, hx1, hx2, hc, hcx⟩ := GlobalTheory.T.exists_blochKato_cocycle_of_crys_deRham_pair l P AI T K LL O hO A d₁ hd₁ d₂ hd₂
  refine ⟨c, hc, ?_⟩
  rw [← hx1, map_sub, map_φVB] at e₁
  rw [← hx2, map_sub, map_ιV] at e₂
  obtain ⟨v, hv⟩ := (GlobalTheory.T.tensor_fundamental_exact_sequence_crystalline l P AI T K LL A'.V).2
    (AlgebraTensorModule.map f (LinearMap.id : P.R.B →ₗ[ℚ_[l]] P.R.B) x - x')
    (by rw [map_sub, eq_comm, sub_eq_sub_iff_sub_eq_sub]; exact e₁)
    (by
      have := Submodule.sub_mem _ (map_mem_FilV (P.PD K) f hy) hfil
      rw [← e₂] at this
      rw [map_sub]
      convert this using 1
      abel)
  refine ⟨v, funext fun g => tmul_one_injective (P.PD K) ?_⟩
  have h1 := congrArg (AlgebraTensorModule.map f (LinearMap.id : P.R.B →ₗ[ℚ_[l]] P.R.B)) (hcx g)
  rw [map_sub, map_actVB (P.PD K) f hf, AlgebraTensorModule.map_tmul, LinearMap.id_apply] at h1
  have h2 : actVB (P.PD K) A'.ρ g (v ⊗ₜ[ℚ_[l]] (1 : P.R.B)) = A'.ρ g v ⊗ₜ[ℚ_[l]] (1 : P.R.B) := by
    simp [actVB]
  change (A'.ρ g v - v) ⊗ₜ[ℚ_[l]] (1 : P.R.B) = (f (c g) - c' g) ⊗ₜ[ℚ_[l]] (1 : P.R.B)
  rw [sub_tmul, sub_tmul, h1, hx', ← h2, ← hv, map_sub]
  abel

end GlobalTheory.BKRightExact
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ComparisonMatrixFrobeniusDisc
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP.Height

private theorem map_smul_ringHom' {n : Type} {α β : Type} [CommRing α] [CommRing β] (F : α →+* β) (c : α)
    (M : Matrix n n α) : (c • M).map F = F c • M.map F :=
  Matrix.map_smul' F c M (map_mul F)

private theorem smul_cancel' {n : Type} {D : Type} [CommRing D] {c : D} (hc : c ∈ nonZeroDivisors D)
    {M M' : Matrix n n D} (h : c • M = c • M') : M = M' := by
  ext i j
  have := congrFun (congrFun h i) j
  simp only [Matrix.smul_apply, smul_eq_mul] at this
  exact (mul_cancel_left_mem_nonZeroDivisors hc).1 this

private theorem alg' {n : Type} [Fintype n] [DecidableEq n] {D : Type} [CommRing D] (Φ : D →+* D)
    (L pf pg fE gE : D) (a N : ℕ) (xf xg Af Ag ε Fm : Matrix n n D)
    (h1f : (L * pf ^ N) • (xf * Af) = fE ^ (a + 2 * N) • (Fm * xf.map Φ))
    (h1g : (L * pg ^ N) • (xg * Ag) = gE ^ (a + 2 * N) • (Fm * xg.map Φ))
    (hR : gE ^ N • (xf * ε) = fE ^ N • xg) (hpf : Φ fE = pf) (hpg : Φ gE = pg) :
    (L * pf ^ N * pg ^ N * gE ^ N) • (xf * (gE ^ (a + N) • (Af * ε.map Φ))) =
      (L * pf ^ N * pg ^ N * gE ^ N) • (xf * (fE ^ (a + N) • (ε * Ag))) := by
  have hΦR : pg ^ N • (xf.map Φ * ε.map Φ) = pf ^ N • xg.map Φ := by
    have := congrArg (fun M => M.map Φ) hR
    simpa only [map_smul_ringHom', Matrix.map_mul, map_pow, hpf, hpg] using this
  calc (L * pf ^ N * pg ^ N * gE ^ N) • (xf * (gE ^ (a + N) • (Af * ε.map Φ)))
      = (pg ^ N * gE ^ (a + 2 * N)) • (((L * pf ^ N) • (xf * Af)) * ε.map Φ) := by
        simp only [Matrix.mul_smul, Matrix.smul_mul, smul_smul, Matrix.mul_assoc]; congr 1; ring
    _ = (pg ^ N * gE ^ (a + 2 * N)) • ((fE ^ (a + 2 * N) • (Fm * xf.map Φ)) * ε.map Φ) := by rw [h1f]
    _ = (gE ^ (a + 2 * N) * fE ^ (a + 2 * N)) • (Fm * (pg ^ N • (xf.map Φ * ε.map Φ))) := by
        simp only [Matrix.mul_smul, Matrix.smul_mul, smul_smul, Matrix.mul_assoc]; congr 1; ring
    _ = (gE ^ (a + 2 * N) * fE ^ (a + 2 * N)) • (Fm * (pf ^ N • xg.map Φ)) := by rw [hΦR]
    _ = (fE ^ (a + 2 * N) * pf ^ N) • (gE ^ (a + 2 * N) • (Fm * xg.map Φ)) := by
        simp only [Matrix.mul_smul, Matrix.smul_mul, smul_smul, Matrix.mul_assoc]; congr 1; ring
    _ = (fE ^ (a + 2 * N) * pf ^ N) • ((L * pg ^ N) • (xg * Ag)) := by rw [h1g]
    _ = (fE ^ (a + N) * L * pf ^ N * pg ^ N) • ((fE ^ N • xg) * Ag) := by
        simp only [Matrix.mul_smul, Matrix.smul_mul, smul_smul, Matrix.mul_assoc]; congr 1; ring
    _ = (fE ^ (a + N) * L * pf ^ N * pg ^ N) • ((gE ^ N • (xf * ε)) * Ag) := by rw [hR]
    _ = (L * pf ^ N * pg ^ N * gE ^ N) • (xf * (fE ^ (a + N) • (ε * Ag))) := by
        simp only [Matrix.mul_smul, Matrix.smul_mul, smul_smul, Matrix.mul_assoc]; congr 1; ring

theorem rel_frob : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (d : ℕ) (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) ℤ_[l]) (τ : Ainf l) (s : Seed bk d ρ τ) (ht : Height s), bk.IsPer τ → ∀ (B : Obj l ↥(OL K)) (f₀ : Hom bk.prism B), toDisc l (BK.hf f₀ X) bk.ρ₀ (BK.hf f₀ bk.E) ∈ nonZeroDivisors (Disc l (BK.hf f₀ X) bk.ρ₀) → ∀ (f g : Hom bk.prism B) (ε : Matrix (Fin d) (Fin d) (Disc l (BK.hf f₀ X) bk.ρ₀)), ht.Rel (BK.hf f₀ X) f g ε → ∀ Φ : Disc l (BK.hf f₀ X) bk.ρ₀ →+* Disc l (BK.hf f₀ X) bk.ρ₀, IsDiscMap B.D.φ Φ → toDisc l (BK.hf f₀ X) bk.ρ₀ (BK.hf g bk.E) ^ (ht.a + s.N) • ((ht.A.map (BK.hf f)).map (toDisc l (BK.hf f₀ X) bk.ρ₀) * ε.map Φ) = toDisc l (BK.hf f₀ X) bk.ρ₀ (BK.hf f bk.E) ^ (ht.a + s.N) • (ε * (ht.A.map (BK.hf g)).map (toDisc l (BK.hf f₀ X) bk.ρ₀)) := by
  intro l _ K bk d ρ τ s ht hτ B f₀ hE f g ε hR Φ hΦ

  have hρpos : 0 < bk.ρ₀ := by
    unfold BK.ρ₀; exact NNReal.rpow_pos (by exact_mod_cast (Fact.out : l.Prime).pos)
  have hρle : bk.ρ₀ ≤ 1 := by
    unfold BK.ρ₀
    exact NNReal.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast (Fact.out : l.Prime).one_lt.le)
      (by have : (0 : ℝ) ≤ 1 / (bk.Ep.natDegree : ℝ) := by positivity
          linarith)

  have hnS : ‖toDisc l (X : bk.S) bk.ρ₀ (frobS l bk.a X)‖ ≤ bk.ρ₀ := by
    rw [frobS_X]
    refine (norm_toDisc_pow_le (l := l) (u := (X : bk.S)) l hρpos).trans ?_
    exact pow_le_of_le_one (by positivity) (by exact_mod_cast hρle) (Fact.out : l.Prime).ne_zero
  have hΦS := isDiscMap_map (frobS l bk.a) hnS

  have key : ∀ (h : Hom bk.prism B) (Fh : Disc l (X : bk.S) bk.ρ₀ →+* Disc l (BK.hf f₀ X) bk.ρ₀), IsDiscMap (BK.hf h) Fh →
      (((l : Disc l (BK.hf f₀ X) bk.ρ₀) ^ s.c₁ * toDisc l (BK.hf f₀ X) bk.ρ₀ (B.D.φ (BK.hf h bk.E)) ^ s.N) •
        (ht.bas.map Fh * (ht.A.map (BK.hf h)).map (toDisc l (BK.hf f₀ X) bk.ρ₀)) =
      toDisc l (BK.hf f₀ X) bk.ρ₀ (BK.hf h bk.E) ^ (ht.a + 2 * s.N) • (s.F.map ((toDisc l (BK.hf f₀ X) bk.ρ₀).comp ((BK.hf h).comp C)) * (ht.bas.map Fh).map Φ)) := by
    intro h Fh hFh
    have hφ : ∀ x, BK.hf h (frobS l bk.a x) = B.D.φ (BK.hf h x) := fun x => h.f_φ x
    have c1 : IsDiscMap (B.D.φ.comp (BK.hf h)) (Φ.comp Fh) :=
      ⟨fun x => by simp [hFh.ext, hΦ.ext], fun x => (hΦ.norm_le _).trans (hFh.norm_le _)⟩
    have c2 : IsDiscMap (B.D.φ.comp (BK.hf h)) (Fh.comp (Disc.map (frobS l bk.a) hnS)) :=
      ⟨fun x => by simp [hFh.ext, hΦS.ext, hφ], fun x => (hFh.norm_le _).trans (hΦS.norm_le _)⟩
    have hc : Φ.comp Fh = Fh.comp (Disc.map (frobS l bk.a) hnS) := c1.unique c2
    have hP := congrArg (fun M => M.map Fh) (GlobalTheory.T.latticeBasis_frobenius_equation_disc l K bk d ρ τ s ht hτ _ hΦS)
    simp only [map_smul_ringHom', Matrix.map_mul, Matrix.map_map, map_mul, map_pow, map_natCast] at hP
    have eA : (ht.A.map (BK.hf h)).map (toDisc l (BK.hf f₀ X) bk.ρ₀) = ht.A.map (Fh ∘ toDisc l (X : bk.S) bk.ρ₀) := by
      ext i j; exact (hFh.ext _).symm
    have eF : s.F.map ((toDisc l (BK.hf f₀ X) bk.ρ₀).comp ((BK.hf h).comp C)) =
        s.F.map (Fh ∘ (toDisc l (X : bk.S) bk.ρ₀).comp C) := by
      ext i j; exact (hFh.ext _).symm
    have eB : (ht.bas.map Fh).map Φ = ht.bas.map (Fh ∘ Disc.map (frobS l bk.a) hnS) := by
      ext i j; exact RingHom.congr_fun hc _
    have e1 : toDisc l (BK.hf f₀ X) bk.ρ₀ (B.D.φ (BK.hf h bk.E)) = Fh (toDisc l (X : bk.S) bk.ρ₀ (frobS l bk.a bk.E)) :=
      ((hFh.ext _).trans (congrArg _ (hφ _))).symm
    have e2 : toDisc l (BK.hf f₀ X) bk.ρ₀ (BK.hf h bk.E) = Fh (toDisc l (X : bk.S) bk.ρ₀ bk.E) := (hFh.ext _).symm
    simp only [eA, eF, eB, e1, e2]
    exact hP

  have hn := GlobalTheory.T.norm_breuilKisinHom_uniformizer_frobenius_le l K bk B f₀
  have hFf := isDiscMap_map (BK.hf f) (hn f).1
  have hFg := isDiscMap_map (BK.hf g) (hn g).1
  have h1f := key f _ hFf
  have h1g := key g _ hFg
  have hFm : s.F.map ((toDisc l (BK.hf f₀ X) bk.ρ₀).comp ((BK.hf g).comp C)) = s.F.map ((toDisc l (BK.hf f₀ X) bk.ρ₀).comp ((BK.hf f).comp C)) := by
    congr 1; funext w; simp [GlobalTheory.T.breuilKisin_prism_homs_agree_on_witt l K bk B f g w]
  simp only [hFm] at h1g

  have hreg : ∀ h : Hom bk.prism B, toDisc l (BK.hf f₀ X) bk.ρ₀ (BK.hf h bk.E) ∈ nonZeroDivisors (Disc l (BK.hf f₀ X) bk.ρ₀) := by
    intro h
    obtain ⟨v, hv⟩ := (GlobalTheory.T.breuilKisin_two_homs_E_regular_associated l K bk B f₀ h).2.1
    have e : toDisc l (BK.hf f₀ X) bk.ρ₀ (BK.hf h bk.E) = toDisc l (BK.hf f₀ X) bk.ρ₀ (BK.hf f₀ bk.E) * toDisc l (BK.hf f₀ X) bk.ρ₀ (v : B.A) :=
      (congrArg _ hv).symm.trans (map_mul _ _ _)
    exact (congrArg (· ∈ nonZeroDivisors (Disc l (BK.hf f₀ X) bk.ρ₀)) e).mpr
      (Submonoid.mul_mem _ hE ((v.isUnit.map (toDisc l (BK.hf f₀ X) bk.ρ₀)).mem_nonZeroDivisors))
  have hunit : ∀ (h : Hom bk.prism B) (Fh : Disc l (X : bk.S) bk.ρ₀ →+* Disc l (BK.hf f₀ X) bk.ρ₀), IsDiscMap (BK.hf h) Fh →
      IsUnit (toDisc l (BK.hf f₀ X) bk.ρ₀ (B.D.φ (BK.hf h bk.E))) := by
    intro h Fh hFh
    have := (GlobalTheory.T.isUnit_closedDisc_frobenius_eisenstein l K bk).map Fh
    have e : Fh (toDisc l (X : bk.S) bk.ρ₀ (frobS l bk.a bk.E)) = toDisc l (BK.hf f₀ X) bk.ρ₀ (B.D.φ (BK.hf h bk.E)) :=
      (hFh.ext _).trans (congrArg _ (h.f_φ _))
    exact (congrArg IsUnit e).mp this
  have hpf : Φ (toDisc l (BK.hf f₀ X) bk.ρ₀ (BK.hf f bk.E)) = toDisc l (BK.hf f₀ X) bk.ρ₀ (B.D.φ (BK.hf f bk.E)) := hΦ.ext _
  have hpg : Φ (toDisc l (BK.hf f₀ X) bk.ρ₀ (BK.hf g bk.E)) = toDisc l (BK.hf f₀ X) bk.ρ₀ (B.D.φ (BK.hf g bk.E)) := hΦ.ext _
  have hAlg := alg' Φ _ _ _ _ _ _ _ _ _ _ _ _ _ h1f h1g (hR _ _ hFf hFg) hpf hpg
  have hc : ((l : Disc l (BK.hf f₀ X) bk.ρ₀) ^ s.c₁ * toDisc l (BK.hf f₀ X) bk.ρ₀ (B.D.φ (BK.hf f bk.E)) ^ s.N *
      toDisc l (BK.hf f₀ X) bk.ρ₀ (B.D.φ (BK.hf g bk.E)) ^ s.N * toDisc l (BK.hf f₀ X) bk.ρ₀ (BK.hf g bk.E) ^ s.N) ∈ nonZeroDivisors _ := by
    refine Submonoid.mul_mem _ (Submonoid.mul_mem _ (Submonoid.mul_mem _ ?_ ?_) ?_) (pow_mem (hreg g) _)
    · exact ((isUnit_l_disc l (BK.hf f₀ X) bk.ρ₀).pow _).mem_nonZeroDivisors
    · exact ((hunit f _ hFf).pow _).mem_nonZeroDivisors
    · exact ((hunit g _ hFg).pow _).mem_nonZeroDivisors
  have hM := smul_cancel' hc hAlg
  have hF0 : Disc.map (BK.hf f) (hn f).1 (toDisc l (X : bk.S) bk.ρ₀ bk.E) ∈ nonZeroDivisors _ :=
    (congrArg (· ∈ nonZeroDivisors (Disc l (BK.hf f₀ X) bk.ρ₀)) (hFf.ext bk.E)).mpr (hreg f)
  have := GlobalTheory.T.basis_matrix_map_cancel_left l K bk d ρ τ s ht _ _ hF0 _ _ hM
  exact this

end GlobalTheory.BSP.Height
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CrystallineCharacterJumpOneAtEmbedding
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module
open Classical

namespace GlobalTheory.HWL

theorem charRep_crys_jump_one : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ (K LL : FinExt l), CaseA K LL → ∀ (τ₀ : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1) (x : P.R.B), IsUnit x → (⇑P.φB)^[finrank ℚ_[l] ↥(K0 K)] x = (l : P.R.B) * x → P.ιB x ∈ (P.PD K).Fil 1 → P.ιB x ∉ (P.PD K).Fil 2 → (∀ j : ℕ, 0 < j → j < finrank ℚ_[l] ↥(K0 K) → P.ιB ((⇑P.φB)^[j] x) ∈ (P.PD K).Fil 0 ∧ P.ιB ((⇑P.φB)^[j] x) ∉ (P.PD K).Fil 1) → ∀ c : ↥(GK K) →* (↥(K0 K))ˣ, (∀ g : ↥(GK K), P.actQ (g : GQ l) x = algebraMap ↥(K0 K) P.R.B ((c g : (↥(K0 K))ˣ) : ↥(K0 K)) * x) → ∀ μ : ↥(GK K) →* (↥LL.1)ˣ, Continuous (fun g : ↥(GK K) => ((μ g : (↥LL.1)ˣ) : ↥LL.1)) → (∀ g : ↥(GK K), ((μ g : (↥LL.1)ˣ) : ↥LL.1) * τ₀ (algebraMap ↥(K0 K) ↥K.1 ((c g : (↥(K0 K))ˣ) : ↥(K0 K))) = 1) → IsCrys (P.PD K) (charRep μ) ∧ ∀ (τ : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1) (b : ℤ), multV (P.PD K) (charRep μ) τ b = if b = (if τ = τ₀ then 1 else 0) then 1 else 0 := by
  intro l _ P AI hT K LL hA τ₀ x hx _hφn hF1 hF2 hφj c hc μ hcont hμ
  let ι0 := IsScalarTower.toAlgHom ℚ_[l] ↥(K0 K) ↥K.1
  have hsurj : Function.Surjective ι0 := fun y =>
    ⟨⟨y.1, IntermediateField.mem_inf.2 ⟨y.2, hA.1 y.2⟩⟩, Subtype.ext rfl⟩
  obtain ⟨emb, hbij, hemb⟩ := GlobalTheory.HWL.exists_letters l P K 1 LL hA.2.2
  haveI : NeZero (finrank ℚ_[l] ↥(K0 K)) := ⟨by haveI := (P.PD K).finK₀; exact Module.finrank_pos.ne'⟩
  have hit : ∀ (j : ℕ) (i : ZMod (finrank ℚ_[l] ↥(K0 K))) (a : ↥(K0 K)),
      emb i ((⇑(P.PD K).σ)^[j] a) = emb (i - j) a := by
    intro j
    induction j with
    | zero => intro i a; simp
    | succ j ih =>
      intro i a
      rw [Function.iterate_succ_apply, ih]
      have h := DFunLike.congr_fun (hemb (i - j - 1)) a
      rw [sub_add_cancel] at h
      rw [AlgHom.comp_apply] at h
      rw [h]
      congr 1
      push_cast
      ring_nf
  obtain ⟨i₀, hi₀⟩ := hbij.2 (τ₀.comp ι0)
  have hμ' : ∀ g : ↥(GK K), ((μ g : (↥LL.1)ˣ) : ↥LL.1) * (τ₀.comp ι0) ((c g : (↥(K0 K))ˣ) : ↥(K0 K)) = 1 :=
    fun g => hμ g
  have key : ∀ τ : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1, ∃ w ∈ DcrisL (P.PD K) (charRep μ) (τ.comp ι0),
      ιV (P.PD K) (LL := ↥LL.1) (V := ↥LL.1) w ∈ FilV (P.PD K) (LL := ↥LL.1) (V := ↥LL.1) (if τ = τ₀ then 1 else 0) ∧
      ιV (P.PD K) (LL := ↥LL.1) (V := ↥LL.1) w ∉ FilV (P.PD K) (LL := ↥LL.1) (V := ↥LL.1) ((if τ = τ₀ then 1 else 0) + 1) := by
    intro τ
    obtain ⟨i, hi⟩ := hbij.2 (τ.comp ι0)
    have hj : ∀ a : ↥(K0 K), (τ.comp ι0) ((⇑(P.PD K).σ)^[(i - i₀).val] a) = (τ₀.comp ι0) a := by
      intro a
      rw [← hi, ← hi₀, hit, ZMod.natCast_zmod_val, sub_sub_cancel]
    by_cases hτ : τ = τ₀
    · subst hτ
      have h0 : (i - i₀).val = 0 := by
        rw [hbij.1 (hi.trans hi₀.symm), sub_self, ZMod.val_zero]
      rw [h0] at hj
      have := GlobalTheory.T.exists_invariant_vector_exact_filtrationDegree_Bcris l P AI hT K LL x hx c hc μ (τ.comp ι0) (τ.comp ι0) 0 hμ' hj 1
        (by simpa using hF1) (by simpa [show (1 : ℤ) + 1 = 2 by norm_num] using hF2)
      simpa using this
    · have hpos : 0 < (i - i₀).val := by
        rw [Nat.pos_iff_ne_zero]
        intro h0
        rw [ZMod.val_eq_zero, sub_eq_zero] at h0
        subst h0
        apply hτ
        have hc' : τ.comp ι0 = τ₀.comp ι0 := hi.symm.trans hi₀
        refine AlgHom.ext fun y => ?_
        obtain ⟨z, rfl⟩ := hsurj y
        exact DFunLike.congr_fun hc' z
      have hlt : (i - i₀).val < finrank ℚ_[l] ↥(K0 K) := ZMod.val_lt _
      obtain ⟨h1, h2⟩ := hφj _ hpos hlt
      have := GlobalTheory.T.exists_invariant_vector_exact_filtrationDegree_Bcris l P AI hT K LL x hx c hc μ (τ₀.comp ι0) (τ.comp ι0) (i - i₀).val hμ' hj 0
        h1 (by simpa using h2)
      simpa [hτ] using this
  have hcrys := GlobalTheory.T.isCrys_character_of_crystalline_vectors l P AI hT K LL hA μ hcont (fun τ => if τ = τ₀ then 1 else 0) key
  exact ⟨hcrys, GlobalTheory.T.crystalline_character_jumps_of_exact_degree l P AI hT K LL hA μ hcont (fun τ => if τ = τ₀ then 1 else 0) key hcrys⟩

end GlobalTheory.HWL
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DeRhamCocycleDimensionCompareStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N GlobalTheory.HyodoDef GlobalTheory.Pst TensorProduct Module
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.de_rham_cocycle_dimension_compare : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ (K : FinExt l) (V : Type) [AddCommGroup V] [Module ℚ_[l] V] [FiniteDimensional ℚ_[l] V] [TopologicalSpace V] [IsModuleTopology ℚ_[l] V] [ContinuousAdd V] [ContinuousConstSMul ℚ_[l] V] (ρ : Representation ℚ_[l] ↥(GK K) V) (V' : Type) [AddCommGroup V'] [Module ℚ_[l] V'] [FiniteDimensional ℚ_[l] V'] [TopologicalSpace V'] [IsModuleTopology ℚ_[l] V'] [ContinuousAdd V'] [ContinuousConstSMul ℚ_[l] V'] (ρ' : Representation ℚ_[l] ↥(GK K) V') (m : V →ₗ[ℚ_[l]] V' →ₗ[ℚ_[l]] ℚ_[l]), (∀ v, Continuous fun g => ρ g v) → (∀ y, Continuous fun g => ρ' g y) → IsDR (P.PD K) ρ' → IsDual1 (P.PD K) ρ ρ' m → ∀ c ∈ geometricCocycles (P.PD K) ρ, ∀ a ∈ crystallineCocycles (P.PD K) ρ', CobL (P.PD K) (cupL ρ' m c a) := by
  first | exact @GlobalTheory.HyodoOrth.hyodo_orth | exact GlobalTheory.HyodoOrth.hyodo_orth | (intros; apply GlobalTheory.HyodoOrth.hyodo_orth <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DeRhamCrystallineOfLatticeReadsStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.deRham_crystalline_of_lattice_reads : ∀ (l : ℕ) [Fact l.Prime] (K L₀ : FinExt l) (P : LocPrime l) (AI : LocAinf l P) (T : LocTied l P AI) (a : ℕ) (d : ℕ) (ρ : ↥(GK K) →* GL (Fin d) ℤ_[l]) (r : ↥(GK K) →* GL (Fin a) (Om l)) (b : Fin d → Matrix (Fin a) (Fin a) (Om l)) (e : Fin d → ℤ_[l]), Reads ρ r b e → ∀ (L : FinExt l) (r' : ↥(GK K) →* GL (Fin a) ↥L.1) (R : Representation ↥L.1 ↥(GK K) (Fin a → ↥L.1)), L₀.1 ≤ L.1 → (∀ g v, R g v = (r' g).val *ᵥ v) → (∀ g i j, (((r' g).val i j : ↥L.1) : Om l) = (r g).val i j) → (Formalism.MainNotions.N.IsDR (P.PD K) (qRep ρ) → Formalism.MainNotions.N.IsDR (P.PD K) R) ∧ (IsCrys (P.PD K) (qRep ρ) → IsCrys (P.PD K) R) := by
  first | exact @GlobalTheory.ReadPass.isDR_isCrys_of_reads | exact GlobalTheory.ReadPass.isDR_isCrys_of_reads | (intros; apply GlobalTheory.ReadPass.isDR_isCrys_of_reads; all_goals assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EmbTypeUeIffLocalEmbeddingInCMHalfTypeStatement
section
open NumberField IsDedekindDomain Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.ConjugateSelfDual ReciprocityTheory.Gal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.embTypeUe_iff_localEmbeddingInCMHalfType : ∀ (D : D7) (i : D.nd.Loc) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)) (ep : Bool) (τ : Br.Kw D.nbr i w hw →ₐ[ℚ_[D.nd.l i]] Br.LL D.nbr i w hw), EmbeddingTypes.EmbTypeUe (i := i) (w := w) (hw := hw) ep τ ↔ GlobalTheory.IndefiniteRowSideFullHecke.SplitPlaceTypes.EmbIn (N := D.nd) D.nbr i ep w hw τ := by
  first | exact @GlobalTheory.TypeUeHalf.main | exact GlobalTheory.TypeUeHalf.main | (intros; apply GlobalTheory.TypeUeHalf.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExactLocalConditionsTopCoreStatement
section
open GlobalTheory.AdmLoc GlobalTheory.TopSteps Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exactLocalConditions_topCore : ∀ {l : ℕ} [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), Nonempty (LocTied l P AI) → ∀ (H : LocHW l P), GlobalTheory.IndefiniteRowSideFullHecke.InvariantsVanishing.ErrorExponentStatement P → GlobalTheory.IndefiniteRowSideFullHecke.AdmissibleTwistedCharClasses.Stmt P → GlobalTheory.IndefiniteRowSideFullHecke.AdmissibleCharUnramified.AdmChiOneUnramified P → ∀ (K LL : FinExt l) (hA : CaseA K LL) (lam : ↥(OL LL)), Irreducible lam → tableLineDegreeTwo.TopCore (P.PD K) (H.W K 1 LL hA.2.2).emb lam (IK K) := by
  first | exact @GlobalTheory.TopDict.topCore_of_typings | exact GlobalTheory.TopDict.topCore_of_typings | (intros; apply GlobalTheory.TopDict.topCore_of_typings <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsBoundedSemistablePeriodsNullFamilyStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_bounded_semistable_periods_null_family : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (τ : Ainf l) (hτ : bk.IsPer τ) (d : ℕ) (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) ℤ_[l]) (hρ : ∀ g, IsUnit (ρ g)) (s : WSeed bk d ρ τ), ∃ (ι : Type) (TB : TopBasis bk.ev bk.J ι) (k : ℕ) (v : ι → Matrix (Fin d) (Fin d) (Ainf l)) (Z : ι → Matrix (Fin d) (Fin d) (bk.DS bk.ρ₀)), (∀ (n : ℕ) (a b : Fin d), {i | v i a b ∉ (bk.J ^ n).map bk.ev}.Finite) ∧ (∀ j : bk.DS bk.ρ₀ →+* bk.DA bk.ρ₀, IsDiscMap bk.ev j → ∀ i, s.W * (Z i).map j = (v i).map bk.iA) ∧ ∀ a b : Fin d, HasSum (fun i => bk.iA (v i a b * TB.b i)) (bk.iA ((l : Ainf l) ^ k * τ ^ (2 * s.N) * if a = b then 1 else 0)) := by
  first | exact @GlobalTheory.BKLim.exists_bounded_periods_wseed | exact GlobalTheory.BKLim.exists_bounded_periods_wseed | (intros; apply GlobalTheory.BKLim.exists_bounded_periods_wseed <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsBreuilKisinFrameHeightOfJumpsLeStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_breuilKisin_frame_height_of_jumps_le : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (τ : Ainf l), bk.IsPer τ → ∀ (C : Core l), C.InvdR → ∀ (N N₀ d : ℕ) (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) (ℤ_[l])) (F : Frame bk N d ρ), F.IsDR → ∀ H : Hodge C (bk.ev bk.E) (fun g => (ρ g).map (zOm l)) K, (∀ i, |(H.p i : ℤ) - H.q| ≤ N₀) → ∃ F₀ : Frame bk N₀ d ρ, F₀.T = F.T ∧ F₀.ε = F.ε := by
  first | (exact @GlobalTheory.BKLim.Lower.exists_frame_of_jumps_le) | (exact GlobalTheory.BKLim.Lower.exists_frame_of_jumps_le) | (intros; apply GlobalTheory.BKLim.Lower.exists_frame_of_jumps_le  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEtaleBasisLimitLatticeTowerStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_etale_basis_limit_lattice_tower : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (τ : Ainf l), bk.IsPer τ → ∀ (d N : ℕ) (ρ : ↥(GK K) →* GL (Fin d) ℤ_[l]) (tw : Tower ρ) (F : ∀ n, Pre bk N (tw.d' n) fun g => (tw.ρ' n g).val), ∃ T0 : Matrix (Fin d) (Fin d) (WCb l), IsUnit T0 ∧ ∀ n, ∃ (R : Matrix (Fin d) (Fin (tw.d' n)) (WCb l)) (R' : Matrix (Fin (tw.d' n)) (Fin d) (WCb l)), (∀ i j, R i j ∈ bk.OE) ∧ (∀ i j, R' i j ∈ bk.OE) ∧ (∀ i j, (l : WCb l) ^ n ∣ (zW (tw.Pi n) * (F n).T - T0 * R) i j) ∧ (∀ i j, (l : WCb l) ^ n ∣ (R * R' - (1 : Matrix (Fin d) (Fin d) (WCb l))) i j) := by
  first | exact @GlobalTheory.BKLim.EtaleLimit.main | exact GlobalTheory.BKLim.EtaleLimit.main | (intros; apply GlobalTheory.BKLim.EtaleLimit.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsLogTiltKummerCoboundaryBdRStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N GlobalTheory.Pst GlobalTheory.PMon TensorProduct Module
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_log_tilt_kummerCoboundary_BdR : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (T : LocTied l P AI), ∃ u : P.R.BdR, ∀ g : GQ l, P.actQdR g u = u + P.ιB ((kummer P g : ℚ_[l]) • P.tB) := by
  first | exact @GlobalTheory.PMon.exists_log_tilt_BdR | exact GlobalTheory.PMon.exists_log_tilt_BdR | (intros; apply GlobalTheory.PMon.exists_log_tilt_BdR <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsMonodromyFrobeniusSolutionFilStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N GlobalTheory.Pst GlobalTheory.PMon TensorProduct Module
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_monodromy_frobenius_solution_fil : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (T : LocTied l P AI) (ι : Bst P →ₐ[ℚ_[l]] P.R.BdR), (∀ b, ι (Polynomial.C b) = P.ιB b) → ∀ (K : FinExt l) (V : Type) [AddCommGroup V] [Module ℚ_[l] V] (x y : V ⊗[ℚ_[l]] Bst P), (l : ℚ_[l]) • phiV P ℚ_[l] V x - x = monV P ℚ_[l] V y → ∃ z : V ⊗[ℚ_[l]] Bst P, monV P ℚ_[l] V z = x ∧ phiV P ℚ_[l] V z - z = y ∧ LinearMap.lTensor V ι.toLinearMap z ∈ FilV (P.PD K) (LL := ℚ_[l]) (V := V) 0 := by
  first | exact @GlobalTheory.PMon.solve_mon_phi_fil | exact GlobalTheory.PMon.solve_mon_phi_fil | (intros; apply GlobalTheory.PMon.solve_mon_phi_fil <;> assumption)
end

