import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaMod
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
import Formalism.SharpRestriction.LevelLetterCocycles.SumRepresentations
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteDimensionalFilDR
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0409
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0001
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle0003
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ValuationDetOfMemKO
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.Bundle0001
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0123
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsCuspidalIffCompositions
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0163
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0170
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0053
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0056
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0149
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0176
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0174
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0171
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0162
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0147
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0148
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.TypeOrthOfAvTied
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.FiniteDimensionalForms
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0230
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0190
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0014
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
import Formalism.SatakeDualWeyl.KpqSubgroupCompact

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.SumRepDeRhamIffAndMultiplicityAdd
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
open Formalism.BasicNotions.Loc
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.DirectSumLocal

open Module

noncomputable def splitEquiv (k : Type) [Field k] (a b : ℕ) : (Fin (a + b) → k) ≃ₗ[k] (Fin a → k) × (Fin b → k) :=
  (LinearEquiv.funCongrLeft k k finSumFinEquiv).trans (LinearEquiv.sumArrowLequivProdArrow (Fin a) (Fin b) k k)

theorem splitEquiv_sumRep {Γ k : Type} [Group Γ] [Field k] {a b : ℕ} (r₁ : Γ →* GL (Fin a) k)
    (r₂ : Γ →* GL (Fin b) k) (g : Γ) (v : Fin (a + b) → k) :
    splitEquiv k a b ((Formalism.MainNotions.SumRepresentations.At.sumRep r₁ r₂ g : Matrix _ _ k).mulVec v) =
      (((r₁ g : Matrix _ _ k)).mulVec (splitEquiv k a b v).1, ((r₂ g : Matrix _ _ k)).mulVec (splitEquiv k a b v).2) := by
  ext i
  · simp [splitEquiv, Formalism.MainNotions.SumRepresentations.At.sumRep, Formalism.MainNotions.SumRepresentations.At.blkHom, Matrix.mulVec, dotProduct, Fin.sum_univ_add, Matrix.fromBlocks]
    rfl
  · simp [splitEquiv, Formalism.MainNotions.SumRepresentations.At.sumRep, Formalism.MainNotions.SumRepresentations.At.blkHom, Matrix.mulVec, dotProduct, Fin.sum_univ_add, Matrix.fromBlocks]
    rfl

end GlobalTheory.DirectSumLocal

namespace GlobalTheory.DirectSumLocal

theorem isdRE_sumRep_and_multE_add : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), Nonempty (LocTied l P AI) → ∀ (E Ω : Type) [Field E] [Field Ω] [Algebra E Ω] (Gw : Subgroup (Ω ≃ₐ[E] Ω)) (O : Type) [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l E Ω Gw O) (LL' : FinExt l) (a b : ℕ) (r₁ : ↥Gw →* GL (Fin a) ↥LL'.1) (r₂ : ↥Gw →* GL (Fin b) ↥LL'.1), (Bw.IsdRE P LL' (Formalism.MainNotions.SumRepresentations.At.sumRep r₁ r₂) ↔ Bw.IsdRE P LL' r₁ ∧ Bw.IsdRE P LL' r₂) ∧ ∀ (τ' : ↥Bw.Kw.1 →ₐ[ℚ_[l]] ↥LL'.1) (c : ℤ), Bw.multE P LL' (Formalism.MainNotions.SumRepresentations.At.sumRep r₁ r₂) τ' c = Bw.multE P LL' r₁ τ' c + Bw.multE P LL' r₂ τ' c := by
  intro l _ P AI hT E Ω _ _ _ Gw O _ _ _ Bw LL' a b r₁ r₂
  obtain ⟨T⟩ := hT
  have he : ∀ g v, splitEquiv (↥LL'.1) a b (Bw.repE LL' (Formalism.MainNotions.SumRepresentations.At.sumRep r₁ r₂) g v) =
      (Bw.repE LL' r₁ g (splitEquiv (↥LL'.1) a b v).1, Bw.repE LL' r₂ g (splitEquiv (↥LL'.1) a b v).2) := by
    intro g v
    exact splitEquiv_sumRep r₁ r₂ _ v
  obtain ⟨h1, -, h3⟩ := GlobalTheory.Per.DirectSumHT.directSum_hodgeTate l P AI T Bw.Kw LL' (Fin (a + b) → ↥LL'.1)
    (Bw.repE LL' (Formalism.MainNotions.SumRepresentations.At.sumRep r₁ r₂)) (Fin a → ↥LL'.1) (Bw.repE LL' r₁) (Fin b → ↥LL'.1)
    (Bw.repE LL' r₂) (splitEquiv (↥LL'.1) a b) he
  refine ⟨?_, fun τ' c => h3 τ' c⟩
  unfold Formalism.BasicNotions.LocBridge.IsdRE
  unfold Formalism.MainNotions.N.IsDR at h1
  simpa only [Module.finrank_fin_fun] using h1

end GlobalTheory.DirectSumLocal
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.TameBlockVectorJacquetNonzero
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.JacBlock

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel Matrix

abbrev sizes (r t : ℕ) : Fin (t + 1) → ℕ := Fin.cons r (fun _ => 1)

theorem sum_sizes (r t : ℕ) : ∑ a, sizes r t a = r + t := by simp [sizes, Fin.sum_cons]

def blocks (r t : ℕ) : (Σ a : Fin (t + 1), Fin (sizes r t a)) ≃ Fin (r + t) := stdBlocks _ (sum_sizes r t)

theorem blocks_zero (r t : ℕ) (i : Fin r) : blocks r t ⟨0, i⟩ = Fin.castAdd t i := by
  ext
  have hv := stdBlocks_val (sizes r t) (sum_sizes r t) 0 i
  haveI : IsEmpty (Fin ((0 : Fin (t + 1)) : ℕ)) := by simp only [Fin.val_zero]; infer_instance
  rw [Finset.univ_eq_empty, Finset.sum_empty, zero_add] at hv
  exact hv

theorem blocks_succ (r t : ℕ) (j : Fin t) (i : Fin (sizes r t j.succ)) :
    blocks r t ⟨j.succ, i⟩ = Fin.natAdd r j := by
  ext
  have hi : (i : ℕ) = 0 := by have := i.2; simp [sizes] at this; omega
  simp [blocks, stdBlocks_val, hi, Fin.sum_univ_succ, sizes]

def zeroIdx (r t : ℕ) (j : Fin t) : Fin (sizes r t j.succ) := ⟨0, by simp [sizes]⟩

theorem natAdd_eq (r t : ℕ) (j : Fin t) : Fin.natAdd r j = blocks r t ⟨j.succ, zeroIdx r t j⟩ :=
  (blocks_succ r t j _).symm

theorem blk_castAdd (r t : ℕ) (i : Fin r) : blk (blocks r t) (Fin.castAdd t i) = 0 := by
  unfold blk; rw [← blocks_zero, Equiv.symm_apply_apply]

theorem blk_natAdd (r t : ℕ) (j : Fin t) : blk (blocks r t) (Fin.natAdd r j) = j.succ := by
  unfold blk; rw [natAdd_eq, Equiv.symm_apply_apply]

theorem natAdd_ne_castAdd {r t : ℕ} (i : Fin t) (j : Fin r) : Fin.natAdd r i ≠ Fin.castAdd t j := by
  intro h; have := congrArg Fin.val h; simp at this; omega

theorem det_of_lowerLeft {R : Type} [CommRing R] {r t : ℕ} (M : Matrix (Fin (r + t)) (Fin (r + t)) R)
    (h0 : ∀ (i : Fin t) (j : Fin r), M (Fin.natAdd r i) (Fin.castAdd t j) = 0) :
    M.det = (M.submatrix (Fin.castAdd t) (Fin.castAdd t)).det * (M.submatrix (Fin.natAdd r) (Fin.natAdd r)).det := by
  rw [← Matrix.det_submatrix_equiv_self finSumFinEquiv M,
    ← Matrix.fromBlocks_toBlocks (M.submatrix finSumFinEquiv finSumFinEquiv)]
  have : (M.submatrix finSumFinEquiv finSumFinEquiv).toBlocks₂₁ = 0 := by
    ext i j; simp [Matrix.toBlocks₂₁, h0]
  rw [this, Matrix.det_fromBlocks_zero₂₁]
  congr 2 <;> ext i j <;> simp [Matrix.toBlocks₁₁, Matrix.toBlocks₂₂]

theorem det_lowerRight {R : Type} [CommRing R] {r t : ℕ} (M : Matrix (Fin (r + t)) (Fin (r + t)) R)
    (h0 : ∀ (i : Fin t) (j : Fin r), M (Fin.natAdd r i) (Fin.castAdd t j) = 0)
    (h1 : M.submatrix (Fin.castAdd t) (Fin.castAdd t) = 1) :
    (M.submatrix (Fin.natAdd r) (Fin.natAdd r)).det = M.det := by
  rw [det_of_lowerLeft M h0, h1, det_one, one_mul]

end GlobalTheory.JacBlock

namespace GlobalTheory.JacBlock

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.SplitRead ValuativeRel Matrix

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def stab {G W : Type} [Group G] [AddCommGroup W] [Module ℂ W] (ρ : Representation ℂ G W) (v : W) : Subgroup G :=
  GlobalTheory.DoubleCosetSetoid.repStabilizer ρ v

theorem KOne_le_stab {r t : ℕ} {χ : kˣ →* ℂˣ} (hχ : IsTame χ) {W : Type} [AddCommGroup W] [Module ℂ W]
    {π : Representation ℂ (GL (Fin (r + t)) k) W} {v : W} (hv : IsBlockVec χ π v) :
    KOne k (Fin (r + t)) ≤ stab π v := by
  intro h hh
  have hKO := GlobalTheory.StepData.KOne_le_KO hh
  have hm := GlobalTheory.StepData.mem_KOne.1 hh
  have hM : GlobalTheory.StepData.MaxM (h.val.submatrix (Fin.natAdd r) (Fin.natAdd r) - 1) := by
    intro i j
    have := hm (Fin.natAdd r i) (Fin.natAdd r j)
    simpa [Matrix.one_apply] using this
  obtain ⟨g', hg', hgv⟩ := GlobalTheory.StepData.exists_mem_KOne hM
  have hu := GlobalTheory.StepData.det_of_mem_KOne hg'
  have key := hv h hKO (fun i j => by
      have := hm (Fin.natAdd r i) (Fin.castAdd t j)
      simpa [Matrix.one_apply, natAdd_ne_castAdd i j] using this)
    (fun i j => by
      have := hm (Fin.castAdd t i) (Fin.castAdd t j)
      simpa [Matrix.one_apply] using this)
    (Matrix.GeneralLinearGroup.det g') (by rw [Matrix.GeneralLinearGroup.val_det_apply, hgv])
  show π h v = v
  rw [key, hχ _ hu, Units.val_one, one_smul]

end GlobalTheory.JacBlock

namespace GlobalTheory.JacBlock

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.SplitRead ValuativeRel Matrix

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem unipRad_inf_KO_le_stab {r t : ℕ} {χ : kˣ →* ℂˣ} {W : Type} [AddCommGroup W] [Module ℂ W]
    {π : Representation ℂ (GL (Fin (r + t)) k) W} {v : W} (hv : IsBlockVec χ π v) :
    unipRad k (blocks r t) ⊓ KO k (Fin (r + t)) ≤ stab π v := by
  intro h hh
  obtain ⟨hP, hD⟩ := mem_unipRad.1 hh.1
  have h0 : ∀ (i : Fin t) (j : Fin r), h.val (Fin.natAdd r i) (Fin.castAdd t j) = 0 := fun i j =>
    mem_parab.1 hP _ _ (by rw [blk_castAdd, blk_natAdd]; exact Fin.succ_pos i)
  have h1 : h.val.submatrix (Fin.castAdd t) (Fin.castAdd t) = 1 := by
    ext i j
    rw [Matrix.submatrix_apply, Matrix.one_apply]
    by_cases hij : i = j
    · subst hij
      rw [if_pos rfl]
      rw [← blocks_zero]
      exact (hD 0 i i).trans (Matrix.one_apply_eq _)
    · rw [if_neg hij]
      rw [← blocks_zero, ← blocks_zero]
      exact (hD 0 i j).trans (Matrix.one_apply_ne hij)
  have hdet : (h.val.submatrix (Fin.natAdd r) (Fin.natAdd r)).det = 1 := by
    rw [det_lowerRight _ h0 h1, ← Matrix.GeneralLinearGroup.val_det_apply, det_eq_one_of_mem_unipRad k hh.1,
      Units.val_one]
  have key := hv h hh.2 (fun i j => by simp [h0]) (fun i j => by
      have := congrFun (congrFun h1 i) j
      simp only [Matrix.submatrix_apply] at this
      simp [this, Matrix.one_apply]) 1 (by rw [hdet, Units.val_one])
  show π h v = v
  rw [key, map_one, Units.val_one, one_smul]

end GlobalTheory.JacBlock

namespace GlobalTheory.JacBlock

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.SplitRead ValuativeRel Matrix

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem intM_leviEmb {α n : Type} {m : α → Type} [Fintype α] [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)]
    [Fintype n] [DecidableEq n] (e : (Σ a, m a) ≃ n) (y : Levi k m) (hy : ∀ a, GlobalTheory.StepData.IntM (y a).val) :
    GlobalTheory.StepData.IntM (leviEmb k e y).val := by
  intro p q
  obtain ⟨⟨a, i⟩, rfl⟩ := e.surjective p
  obtain ⟨⟨b, j⟩, rfl⟩ := e.surjective q
  by_cases h : a = b
  · subst h
    rw [leviEmb_apply_same]
    exact hy a i j
  · rw [leviEmb_apply_ne k e y h]
    exact zero_mem _

abbrev single {r t : ℕ} (j : Fin t) (g : GL (Fin (sizes r t j.succ)) k) : Levi k (fun a => Fin (sizes r t a)) :=
  Pi.mulSingle j.succ g

theorem single_mem_KO {r t : ℕ} (j : Fin t) {g : GL (Fin (sizes r t j.succ)) k}
    (hg : g ∈ KO k (Fin (sizes r t j.succ))) (a : Fin (t + 1)) : single j g a ∈ KO k (Fin (sizes r t a)) := by
  by_cases ha : a = j.succ
  · subst ha
    rw [single, Pi.mulSingle_eq_same]
    exact hg
  · rw [single, Pi.mulSingle_eq_of_ne ha]
    exact one_mem _

theorem deltaHalf_single {r t : ℕ} (j : Fin t) {g : GL (Fin (sizes r t j.succ)) k}
    (hg : g ∈ KO k (Fin (sizes r t j.succ))) : deltaHalf k (fun a => Fin (sizes r t a)) (single j g) = 1 := by
  rw [deltaHalf_apply]
  refine Finset.prod_eq_one fun a _ => isUnram_absPow k _ _ ?_
  exact GlobalTheory.StepData.valuation_det_of_mem_KO (single_mem_KO j hg a)

theorem act_single {r t : ℕ} {χ : kˣ →* ℂˣ} {W : Type} [AddCommGroup W] [Module ℂ W]
    {π : Representation ℂ (GL (Fin (r + t)) k) W} {v : W} (hv : IsBlockVec χ π v) (j : Fin t)
    {g : GL (Fin (sizes r t j.succ)) k} (hg : g ∈ KO k (Fin (sizes r t j.succ))) :
    π (leviEmb k (blocks r t) (single j g)) v = (χ (Matrix.GeneralLinearGroup.det g) : ℂ) • v := by
  set h := leviEmb k (blocks r t) (single j g) with hdef
  have hKO : h ∈ KO k (Fin (r + t)) := by
    refine GlobalTheory.StepData.mem_KO.2 ⟨intM_leviEmb _ _ fun a => GlobalTheory.StepData.intM_of_mem_KO (single_mem_KO j hg a), ?_⟩
    rw [hdef, ← map_inv]
    exact intM_leviEmb _ _ fun a => GlobalTheory.StepData.intM_of_mem_KO (inv_mem (single_mem_KO j hg a))
  have h0 : ∀ (i : Fin t) (j' : Fin r), h.val (Fin.natAdd r i) (Fin.castAdd t j') = 0 := fun i j' => by
    rw [natAdd_eq, ← blocks_zero]
    exact leviEmb_apply_ne k _ _ (Fin.succ_ne_zero i) _ _
  have hx0 : single j g 0 = 1 := Pi.mulSingle_eq_of_ne (Fin.succ_ne_zero j).symm _
  have h1 : h.val.submatrix (Fin.castAdd t) (Fin.castAdd t) = 1 := by
    have hx0' : ((single j g 0 : GL (Fin (sizes r t 0)) k) : Matrix (Fin (sizes r t 0)) (Fin (sizes r t 0)) k) = 1 := by
      rw [hx0, Units.val_one]
    ext i i'
    rw [Matrix.submatrix_apply, ← blocks_zero, ← blocks_zero, hdef]
    exact (leviEmb_apply_same k (blocks r t) (single j g) 0 i i').trans (congrFun (congrFun hx0' i) i')
  have key := hv h hKO (fun i j' => by simp [h0]) (fun i j' => by
      have := congrFun (congrFun h1 i) j'
      simp only [Matrix.submatrix_apply] at this
      simp [this, Matrix.one_apply]) (Matrix.GeneralLinearGroup.det g) (by
      rw [det_lowerRight _ h0 h1, ← Matrix.GeneralLinearGroup.val_det_apply, hdef, det_leviEmb k,
        Finset.prod_eq_single j.succ (fun b _ hb => by rw [single, Pi.mulSingle_eq_of_ne hb, map_one]) (by simp),
        single, Pi.mulSingle_eq_same])
  exact key

end GlobalTheory.JacBlock

namespace GlobalTheory.JacBlock

theorem exists_jacquet_ne_zero_of_isBlockVec : GlobalTheory.Published.DepthZeroJacquetInjective → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (r t : ℕ) (χ : kˣ →* ℂˣ) (π : Irr k (r + t)) (v : π.V), GlobalTheory.SplitWeil.IsTame χ → v ≠ 0 → IsBlockVec χ π.π v → ∃ (e : (Σ a : Fin (t + 1), Fin ((Fin.cons r (fun _ => 1) : Fin (t + 1) → ℕ) a)) ≃ Fin (r + t)) (x : GlobalTheory.PRep.Jacquet π.π (GlobalTheory.SmGL.unipRad k e)), x ≠ 0 ∧ ∀ (j : Fin t) (g : GL (Fin ((Fin.cons r (fun _ => 1) : Fin (t + 1) → ℕ) j.succ)) k), g ∈ GlobalTheory.SplitWeil.KO k (Fin ((Fin.cons r (fun _ => 1) : Fin (t + 1) → ℕ) j.succ)) → GlobalTheory.SmGL.jac e π.π (Pi.mulSingle j.succ g) x = (χ (Matrix.GeneralLinearGroup.det g) : ℂ) • x := by
  intro hP k _ _ _ _ r t χ π v hχ hv0 hv
  refine ⟨blocks r t, Submodule.Quotient.mk v, ?_, ?_⟩
  · intro hx
    apply hv0
    refine hP k (r + t) (t + 1) _ (blocks r t) π v ?_ hx
    rintro ⟨h, hh⟩
    have := sup_le (KOne_le_stab hχ hv) (unipRad_inf_KO_le_stab hv) hh
    simp only [MonoidHom.one_apply, Units.val_one, one_smul]
    exact this
  · intro j g hg
    rw [GlobalTheory.SmGL.jac_mk, deltaHalf_single j hg, act_single hv j hg, inv_one, Units.val_one, one_smul,
      Submodule.Quotient.mk_smul]

end GlobalTheory.JacBlock

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.TameParahoricRepSplitsAsProduct
section
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.SplitRead GlobalTheory.ThetaGL GlobalTheory.TameIwahori ValuativeRel

noncomputable section

namespace GlobalTheory.TameIwahori

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem isSmoothChar_of_eq_on_units {ψ θ : kˣ →* ℂˣ} (hθ : IsSmoothChar θ)
    (h : ∀ u : kˣ, valuation k (u : k) = 1 → ψ u = θ u) : IsSmoothChar ψ := by
  have h1 : IsUnram (ψ * θ⁻¹) := fun u hu => by simp [h u hu]
  have h2 : ψ = (ψ * θ⁻¹) * θ := by ext u; simp
  rw [h2]
  exact (isSmoothChar_of_isUnram h1).mul hθ

theorem exists_prinSeries (hBZ : GlobalTheory.Published.BernsteinZelevinskyFiniteness)
    (hD : GlobalTheory.Published.DepthZeroJacquetInjective) {n : ℕ} (π : Irr k n) {v : π.V} {θ : Fin n → kˣ →* ℂˣ}
    (hθ : ∀ i, IsSmoothChar (θ i)) (hv : v ≠ 0) (h : IsIwVec θ π.π v) :
    ∃ ψ : Fin n → kˣ →* ℂˣ, (∀ i (u : kˣ), valuation k (u : k) = 1 → ψ i u = θ i u) ∧
      (∀ i, InSupport π.π (ψ i)) ∧ IsSubquotient π.π (prinSeries ψ) := by
  have hl : HasFiniteLength (jacB π.π) :=
    (hasFiniteLength_comp_iff _ _ (leviTorus k (Fin n)).surjective).2
      ((hBZ k).2.1 _ _ _ (points (Fin n)) _ π.π π.smooth (hasFiniteLength_of_isIrreducible π.irr))
  obtain ⟨ψ, l, hl0, hψ, hu⟩ := GlobalTheory.T.exists_torusEigenform_of_compactTorus_eigenvector k n _ (jacB π.π) (Submodule.Quotient.mk v) θ
    (isSmooth_jacB π.smooth) hl hθ (GlobalTheory.T.tameIwahoriEigenvector_jacquetQuotient_ne_zero hD k n π v θ hv h) fun t ht => by
      rw [UnramFixed.jacB_apply, jacBU_mk, h.2 t ht]
      have : ((deltaHalf k fun _ : Fin n => Unit).comp (leviTorus k (Fin n)).toMonoidHom) t = 1 :=
        UnramFixed.deltaHalf_torusO k ht
      rw [this]
      simp
  exact ⟨ψ, hu, GlobalTheory.T.mem_supercuspidalSupport_of_torus_jacquet_eigenform k n _ π.π ψ l hl0 hψ,
    SatakeExists.isSubquotient_of_eigenform π.smooth π.irr _ l hl0 hψ⟩

theorem hasFiniteLength_prinSeries (hBZ : GlobalTheory.Published.BernsteinZelevinskyFiniteness) {n : ℕ}
    {ψ : Fin n → kˣ →* ℂˣ} (hψ : ∀ i, IsSmoothChar (ψ i)) : HasFiniteLength (prinSeries ψ) := by
  have hs : IsSmoothChar (torusChar ψ) := by
    unfold torusChar
    refine Finset.prod_induction _ IsSmoothChar (fun _ _ => IsSmoothChar.mul) isSmoothChar_one fun a _ => ?_
    exact (hψ a).comp _ (continuous_apply a)
  refine (hBZ k).2.2.1 _ _ _ (points (Fin n)) _ _ ?_ ?_
  · refine isSmooth_comp ((isSmooth_ofChar_iff _).2 hs) _ (continuous_pi fun i => ?_)
    exact continuous_glDet.comp (continuous_apply i)
  · exact (hasFiniteLength_comp_iff _ _ (leviTorus k (Fin n)).symm.surjective).2
      (hasFiniteLength_of_isIrreducible (isIrreducible_ofChar _))

theorem exists_model (hBZ : GlobalTheory.Published.BernsteinZelevinskyFiniteness) {n : ℕ}
    {ψ : Fin n → kˣ →* ℂˣ} (hψ : ∀ i, IsSmoothChar (ψ i)) :
    ∃ (V : Type) (_ : AddCommGroup V) (_ : Module ℂ V) (A : Representation ℂ (GL (Fin n) k) V),
      Nonempty (A.Equiv (prinSeries ψ)) ∧ IsSmooth A ∧ HasFiniteLength A :=
  ⟨_, _, _, prinSeries ψ, ⟨.refl _⟩, isSmooth_parInd _ _, hasFiniteLength_prinSeries hBZ hψ⟩

theorem isCuspSupport_of_prinSeries {n : ℕ} (σ : Irr k n) {ψ : Fin n → kˣ →* ℂˣ}
    (hψ : ∀ i, IsSmoothChar (ψ i)) (h : IsSubquotient σ.π (prinSeries ψ)) :
    IsCuspSupport σ.π (fun _ : Fin n => 1) fun a => (Irr.ofDet 1 (ψ a) (hψ a)).π :=
  ⟨σ.irr, fun a => ⟨one_pos, isIrreducible_ofChar _, isCuspidal_detRep_one (hψ a)⟩, _,
    h.trans (PrinProd.isSubquotient_prinSeries_multiProd k n ψ)⟩

theorem exists_eq_of_inSupport (hG : GlobalTheory.Published.GeometricLemma) {n : ℕ} (σ : Irr k n) {ψ : Fin n → kˣ →* ℂˣ}
    (hψ : ∀ i, IsSmoothChar (ψ i)) (h : IsSubquotient σ.π (prinSeries ψ)) {μ : kˣ →* ℂˣ}
    (hμ : InSupport σ.π μ) : ∃ i, μ = ψ i := by
  have h1 := JacquetExact.inSupport_of_isSubquotient k _ _ _ _ _ μ (isSmooth_parInd _ _)
    (h.trans (PrinProd.isSubquotient_prinSeries_multiProd k n ψ)) hμ
  obtain ⟨a, ha⟩ := ProdSupport.exists_inSupport_of_multiProd hG k _ _ _ _ _ _ μ
    (fun a => (Irr.ofDet 1 (ψ a) (hψ a)).smooth) (fun a => isIrreducible_ofChar _) h1
  exact ⟨a, (Model.inSupport_one_iff _ _).1 ha⟩

def twistIrr {n : ℕ} (σ : Irr k n) (χ : kˣ →* ℂˣ) (hχ : IsSmoothChar χ) : Irr k n where
  V := σ.V
  π := twist σ.π (detChar (Fin n) χ)
  smooth := isSmooth_twist σ.smooth hχ.detChar
  irr := by
    have φ : Subrepresentation (twist σ.π (detChar (Fin n) χ)) ≃o Subrepresentation σ.π :=
      { toFun := fun S => ⟨S.toSubmodule, fun g v hv => by
          have := S.toSubmodule.smul_mem (((detChar (Fin n) χ g)⁻¹ : ℂˣ) : ℂ) (S.apply_mem_toSubmodule g hv)
          rwa [twist_apply, smul_smul, Units.inv_mul, one_smul] at this⟩
        invFun := fun S => ⟨S.toSubmodule, fun g v hv =>
          S.toSubmodule.smul_mem _ (S.apply_mem_toSubmodule g hv)⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl
        map_rel_iff' := Iff.rfl }
    exact φ.isSimpleOrder_iff.2 σ.irr

theorem tameSplit : GlobalTheory.Published.BernsteinZelevinskyFiniteness → GlobalTheory.Published.GeometricLemma →
    GlobalTheory.Published.UnlinkedProductIrreducible → GlobalTheory.Published.DepthZeroJacquetInjective →
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], TameSplit k := by
  intro hBZ hG hU hD k _ _ _ _ r t χ π v hχ htame hram hv hpar
  let θ : Fin (r + t) → kˣ →* ℂˣ := Fin.append (fun _ : Fin r => 1) fun _ : Fin t => χ
  have hθ : ∀ i, IsSmoothChar (θ i) := fun i => by
    induction i using Fin.addCases with
    | left i => simpa [θ] using isSmoothChar_one
    | right i => simpa [θ] using hχ
  obtain ⟨ψ, hψθ, -, hsub⟩ := exists_prinSeries hBZ hD π hθ hv (GlobalTheory.T.tameIwahoriTorusCharVector_of_parahoricDetCharVector k r t χ _ π.π v htame hpar)
  have hψ : ∀ i, IsSmoothChar (ψ i) := fun i => isSmoothChar_of_eq_on_units (hθ i) (hψθ i)
  let ψ₁ : Fin r → kˣ →* ℂˣ := fun i => ψ (Fin.castAdd t i)
  let ψ₂ : Fin t → kˣ →* ℂˣ := fun i => ψ (Fin.natAdd r i)
  have hψ₁ : ∀ i (u : kˣ), valuation k (u : k) = 1 → ψ₁ i u = 1 := fun i u hu => by
    simpa [θ] using hψθ (Fin.castAdd t i) u hu
  have hψ₂ : ∀ i (u : kˣ), valuation k (u : k) = 1 → ψ₂ i u = χ u := fun i u hu => by
    simpa [θ] using hψθ (Fin.natAdd r i) u hu
  have happ : Fin.append ψ₁ ψ₂ = ψ := Fin.append_castAdd_natAdd
  rw [← happ] at hsub
  obtain ⟨σ₁, σ₂, h₁, h₂, hπ⟩ : ∃ (σ₁ : Irr k r) (σ₂ : Irr k t), IsSubquotient σ₁.π (prinSeries ψ₁) ∧
      IsSubquotient σ₂.π (prinSeries ψ₂) ∧ IsSubquotient π.π (prod₂ σ₁.π σ₂.π) := by
    obtain ⟨V, _, _, A, ⟨φA⟩, sA, lA⟩ := exists_model hBZ (ψ := ψ₁) fun i => hψ _
    obtain ⟨W, _, _, B, ⟨φB⟩, sB, lB⟩ := exists_model hBZ (ψ := ψ₂) fun i => hψ _
    obtain ⟨σ₁, σ₂, h₁, h₂, hπ⟩ := GlobalTheory.T.exists_irreducible_subquotient_twoBlockConstituents k r t _ _ _ π.π A B π.irr sA sB lA lB
      (hsub.trans (GlobalTheory.T.prinSeries_append_isSubquotient_prod₂ k r t ψ₁ ψ₂ V W A B ⟨φA⟩ ⟨φB⟩))
    exact ⟨σ₁, σ₂, h₁.trans (.of_injective φA.toIntertwiningMap φA.injective),
      h₂.trans (.of_injective φB.toIntertwiningMap φB.injective), hπ⟩
  have hirr : (prod₂ σ₁.π σ₂.π).IsIrreducible := by
    refine hU k r t r t σ₁ σ₂ _ _ _ _ (isCuspSupport_of_prinSeries σ₁ (fun i => hψ _) h₁)
      (isCuspSupport_of_prinSeries σ₂ (fun i => hψ _) h₂) ?_
    rintro a b h α ⟨φ⟩
    refine hram fun u hu => ?_
    let g : GL (Fin 1) k := Matrix.GeneralLinearGroup.scalar (Fin 1) u
    have hg : Matrix.GeneralLinearGroup.det g = u := ProdSupport.det_scalar_one rfl u
    obtain ⟨c, hc⟩ : ∃ c : ℂ, φ (1 : ℂ) = c := ⟨_, rfl⟩
    have h0 : c ≠ 0 := fun h => one_ne_zero (α := ℂ) (φ.injective ((hc.trans h).trans (map_zero φ).symm))
    have h1 : φ (detRep (Fin 1) (ψ₁ a) g (1 : ℂ)) = (detChar (Fin 1) (unrChar k α) g : ℂ) •
        detRep (Fin 1) (ψ₂ b) g c := hc ▸ φ.toIntertwiningMap.isIntertwining _ _ g (1 : ℂ)
    simp only [detRep, ofChar_apply, detChar_apply, hg, hψ₁ a u hu, hψ₂ b u hu, isUnram_unrChar k α u hu,
      Units.val_one, one_mul, one_smul] at h1
    exact Units.ext ((mul_eq_right₀ h0).1 (h1.symm.trans hc))
  obtain ⟨φ⟩ := hπ.nonempty_equiv π.irr hirr
  let f := φ.symm v
  have hf0 : f ≠ 0 := fun h => hv (φ.symm.injective (h.trans (map_zero φ.symm).symm))
  have hf : IsParahoricVec χ (prod₂ σ₁.π σ₂.π) f := fun h hh hl u hu => by
    have := φ.symm.toIntertwiningMap.isIntertwining _ _ h v
    rw [hpar h hh hl u hu, map_smul] at this
    exact this.symm
  obtain ⟨w, hw⟩ := GlobalTheory.T.parahoricVector_twoBlockProduct_exists_perm_ne_zero k r t χ _ _ σ₁.π σ₂.π f hf0 hf
  obtain ⟨s, y, hy0, hy⟩ := GlobalTheory.T.tameIwahoriVector_twoBlockProduct_perm_value_first k r t θ _ _ σ₁.π σ₂.π f w (GlobalTheory.T.tameIwahoriTorusCharVector_of_parahoricDetCharVector k r t χ _ _ f htame hf) hw
  obtain ⟨μ, hμ, hμs, -⟩ := exists_prinSeries hBZ hD σ₁ (fun i => hθ _) hy0 hy
  have hwP : GlobalTheory.Parabolic.permGL k w ∈ parab k (two (stdSum (rfl : r + t = r + t))) := by
    have key : ∀ (i : Fin r) (j : Fin t), Fin.castAdd t i ≠ w (Fin.natAdd r j) := fun i j hij => by
      obtain ⟨i, rfl⟩ := s.surjective i
      obtain ⟨a, ha⟩ := exists_eq_of_inSupport hG σ₁ (fun i => hψ _) h₁ (hμs i)
      refine hram fun u hu => ?_
      have h1 := hμ i u hu
      rw [ha, hij, Equiv.symm_apply_apply] at h1
      simpa [θ] using h1.symm.trans (hψ₁ a u hu)
    refine (mem_parab_two k).2 fun j i => (GlobalTheory.Parabolic.permGL_apply w _ _).trans (if_neg fun hji => ?_)
    have hF : ∀ b, ∃ c, w (Fin.natAdd r b) = Fin.natAdd r c := fun b => by
      generalize hx : w (Fin.natAdd r b) = x
      induction x using Fin.addCases with
      | left a => exact absurd hx.symm (key a b)
      | right c => exact ⟨c, rfl⟩
    choose c hc using hF
    have hinj : Function.Injective c := fun b b' h =>
      Fin.natAdd_injective _ _ (w.injective (by rw [hc, hc, h]))
    obtain ⟨b, hb⟩ := Finite.surjective_of_injective hinj j
    have h2 : w (Fin.natAdd r b) = w (Fin.castAdd t i) := by rw [hc, hb]; exact hji
    have h3 := congrArg Fin.val (w.injective h2)
    have := i.2
    simp at h3
    omega
  have hf1 : f.1.1 1 ≠ 0 := fun h => hw (by
    have := f.1.2 ⟨_, hwP⟩ 1
    rw [mul_one, h, map_zero] at this
    exact this)
  obtain ⟨s₁, s₂⟩ := GlobalTheory.T.spherical_factors_of_parahoricVector_twoBlockProduct k r t χ _ _ σ₁.π σ₂.π f hf hf1
  refine ⟨σ₁, twistIrr σ₂ χ⁻¹ hχ.inv, s₁, s₂, ?_⟩
  have e : twist (twist σ₂.π (detChar (Fin t) χ⁻¹)) (detChar (Fin t) χ) = σ₂.π := by
    ext g x
    simp [smul_smul]
  show Nonempty (π.π.Equiv (prod₂ σ₁.π (twist (twist σ₂.π (detChar (Fin t) χ⁻¹)) (detChar (Fin t) χ))))
  rw [e]
  exact ⟨φ.symm⟩

end GlobalTheory.TameIwahori
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.TypeOrthogonalityOfForm
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.ThetaExh

theorem typeOrth_of_pin : ∀ (hL : GlobalTheory.Published.LocalLanglandsGL) (D : D7) (P : Pin hL D), ∀ i : D.nd.Loc, MtForm D P.M i → GlobalTheory.ThetaExh.TypeOrth D.nd D.naut i := by
  intro hL D P i hF
  obtain ⟨B, hB, hinner⟩ := hF
  exact GlobalTheory.ThetaExh.typeOrth_of_avTied D P.M P.H.av i B hB hinner
    (GlobalTheory.AlgFormsFin.finiteDimensional_forms D D.R.nV (P.M.loc i).wt (GlobalTheory.T.finite_doubleCosets_definiteUnitary_maximalLevel D.host.E D.R.nV))

end GlobalTheory.ThetaExh
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.UnramifiedLocalPairActsOnVacuaByHeisenbergCombStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.Hk3
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unramifiedLocalPair_acts_on_vacua_by_heisenberg_comb : ∀ (L : Type) [Field L] [CharZero L] [Valued L (WithZero (Multiplicative ℤ))] [CompleteSpace L] (ϖ : L) (σ : L →+* L) (q : ℕ) (δ : L) (n n' : ℕ) (JS : GL (Fin n) L) (JT : GL (Fin n') L) (ψ : AddChar L ℂ) (M : Type) [AddCommGroup M] [Module ℂ M] (ρ : Matrix (Fin n') (Fin n) L → Module.End ℂ M) (ω : Formalism.UG.UJ σ (JS : Matrix (Fin n) (Fin n) L) × Formalism.UG.UJ σ (JT : Matrix (Fin n') (Fin n') L) →* Module.End ℂ M), LocPair ϖ σ q δ JS JT ψ ρ ω → ∀ p, ∃ c : Matrix (Fin n') (Fin n) L →₀ ℂ, ∀ s, LocVac ρ s → ω p s = c.sum fun x z => z • ρ x s := by
  first | exact @GlobalTheory.Hk3.locPair_act_vac_comb | exact GlobalTheory.Hk3.locPair_act_vac_comb | (intros; apply GlobalTheory.Hk3.locPair_act_vac_comb <;> assumption)
end

