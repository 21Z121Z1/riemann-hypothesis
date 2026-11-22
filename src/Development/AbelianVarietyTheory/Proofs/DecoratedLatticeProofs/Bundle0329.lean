import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0017
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemHatIffOfSelfDual
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0322
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0023
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0015
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0019
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.HasDerivAtZeroAndIsTheta
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0322
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0222
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0226
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0296
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0318
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0023
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0227
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0325
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0194
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.CosInj
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.InfiniteQAtOfIs
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0321
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.Bundle0001
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.Bundle0005
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.ConcreteLevelAdelicSubset
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedVolumeStatements.LevelSubgroupProperties
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.DstarIdxPf
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0027

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsUnitaryFiniteAdelicMapSelfDualCompletions
section
open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP

noncomputable section

namespace GlobalTheory.Core.Rk.OrthIsom

open scoped TensorProduct

theorem mul_inv_mem_UJ {R : Type} [CommRing R] {n : ℕ} (σ : R →+* R) (J : Matrix (Fin n) (Fin n) R)
    (β β' : GL (Fin n) R) (h : Formalism.UG.cT σ β'.1 * J * β'.1 = Formalism.UG.cT σ β.1 * J * β.1) :
    β' * β⁻¹ ∈ Formalism.UG.UJ σ J := by
  change Formalism.UG.cT σ (β' * β⁻¹).1 * J * (β' * β⁻¹).1 = J
  calc Formalism.UG.cT σ (β' * β⁻¹).1 * J * (β' * β⁻¹).1
      = Formalism.UG.cT σ (β⁻¹).1 * (Formalism.UG.cT σ β'.1 * J * β'.1) * (β⁻¹).1 := by
        rw [Units.val_mul, Formalism.UG.cT_mul]; simp only [Matrix.mul_assoc]
    _ = Formalism.UG.cT σ (β.1 * (β⁻¹).1) * J * (β.1 * (β⁻¹).1) := by
        rw [h, Formalism.UG.cT_mul]; simp only [Matrix.mul_assoc]
    _ = J := by rw [Units.mul_inv, Formalism.UG.cT_one, Matrix.one_mul, Matrix.mul_one]

theorem mem_iff_of_frames {R : Type} [CommRing R] {n : ℕ} (S : Subring R) (β β' : GL (Fin n) R)
    (H H' : Set (Fin n → R)) (h : ∀ y, y ∈ H ↔ ∀ i, ((β⁻¹).val *ᵥ y) i ∈ S)
    (h' : ∀ y, y ∈ H' ↔ ∀ i, ((β'⁻¹).val *ᵥ y) i ∈ S) (y : Fin n → R) :
    y ∈ H ↔ (β' * β⁻¹).val *ᵥ y ∈ H' := by
  rw [h, h', Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel_left]

section Alg

variable {F E : Type} [Field F] [Field E] [Algebra F E] {n : ℕ} (R : Type) [CommRing R] [Algebra F R]

theorem swap_symm_mem_HR (σ : E →ₐ[F] E) (J : Matrix (Fin n) (Fin n) E)
    (g : GL (Fin n) (E ⊗[F] R)) (hg : g ∈ Formalism.UG.UPts σ J R) :
    Formalism.UG.bc (Algebra.TensorProduct.comm F R E).symm.toAlgHom.toRingHom g ∈ HR R σ J := by
  have h := Formalism.UG.Final.BCMem _ _ (Fin n) (Formalism.UG.sigR σ R) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR R σ)
    (Algebra.TensorProduct.comm F R E).symm.toAlgHom.toRingHom
    (RingHom.ext fun x => ?_) (J.map (Formalism.UG.inclE R)) g hg
  · exact h
  induction x using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | add a b ha hb => simp only [map_add, ha, hb]
  | tmul a x => rfl

theorem swap_mulVec (g : GL (Fin n) (E ⊗[F] R)) (z : Fin n → R ⊗[F] E) :
    (fun i => Algebra.TensorProduct.comm F R E
      (((Formalism.UG.bc (Algebra.TensorProduct.comm F R E).symm.toAlgHom.toRingHom g).val *ᵥ z) i)) =
      g.val *ᵥ fun i => Algebra.TensorProduct.comm F R E (z i) := by
  funext i
  simp only [Matrix.mulVec, dotProduct, map_sum, map_mul]
  refine Finset.sum_congr rfl fun j _ => ?_
  congr 1
  exact (Algebra.TensorProduct.comm F R E).apply_symm_apply (g.val i j)

end Alg

section Swap

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}

theorem mem_latHat_iff_swap (Λ : Submodule (𝓞 E) (Fin n → E)) (z : Fin n → Af F ⊗[F] E) :
    z ∈ Formalism.MainNotions.StandardLattice.latHat F E (Λ : Set (Fin n → E)) ↔
      (fun i => Algebra.TensorProduct.comm F (Af F) E (z i)) ∈ Formalism.L2.Herm.hatL (F := F) Λ := by
  refine ⟨GlobalTheory.PrincInLevel.swap_mem_hatL Λ z, fun h => ?_⟩
  have h1 := GlobalTheory.PrincInLevel.swap_symm_mem_hat Λ _ h
  simp only [AlgEquiv.symm_apply_apply] at h1
  exact h1

theorem exists_of_swap (σ : E →ₐ[F] E) (J : Matrix (Fin n) (Fin n) E) (Λ Λ' : Submodule (𝓞 E) (Fin n → E))
    (g : GL (Fin n) (E ⊗[F] Af F)) (hg : g ∈ Formalism.UG.UPts σ J (Af F))
    (h : ∀ y, y ∈ Formalism.L2.Herm.hatL (F := F) Λ ↔ g.val *ᵥ y ∈ Formalism.L2.Herm.hatL (F := F) Λ') :
    ∃ b ∈ HR (Af F) σ J, ∀ w : Fin n → Af F ⊗[F] E,
      w ∈ Formalism.MainNotions.StandardLattice.latHat F E (Λ : Set (Fin n → E)) ↔ b.val *ᵥ w ∈ Formalism.MainNotions.StandardLattice.latHat F E (Λ' : Set (Fin n → E)) := by
  refine ⟨_, swap_symm_mem_HR (Af F) σ J g hg, fun w => ?_⟩
  rw [mem_latHat_iff_swap, mem_latHat_iff_swap, swap_mulVec]
  exact h _

end Swap

theorem exists_unitary_latHat : ∀ (D : D7) (A : HSp D) (L L' : Submodule (𝓞 D.host.E) (Fin A.rank → D.host.E)),
    IsSelfDualC A L → IsSelfDualC A L' →
    ∃ b ∈ HR (Af D.host.F) D.sp.cm.sig A.gram, ∀ w : Fin A.rank → TensorProduct D.host.F (Af D.host.F) D.host.E,
      w ∈ Formalism.MainNotions.StandardLattice.latHat D.host.F D.host.E (L : Set (Fin A.rank → D.host.E)) ↔
        b.val *ᵥ w ∈ Formalism.MainNotions.StandardLattice.latHat D.host.F D.host.E (L' : Set (Fin A.rank → D.host.E)) := by
  intro D A L L' hL hL'
  obtain ⟨β, e, hβ⟩ := GlobalTheory.AdIsom.exists_orth hL
  obtain ⟨β', e', hβ'⟩ := GlobalTheory.AdIsom.exists_orth hL'
  refine exists_of_swap D.sp.cm.sig A.gram L L' (β' * β⁻¹) (mul_inv_mem_UJ _ _ β β' (hβ'.trans hβ.symm)) ?_
  rw [e, e']
  exact mem_iff_of_frames (GlobalTheory.IndefiniteRowSideFullHecke.FlatSpaceComponents.OA D) β β' _ _ (GlobalTheory.AdIsom.mem_hat_lat β) (GlobalTheory.AdIsom.mem_hat_lat β')

end GlobalTheory.Core.Rk.OrthIsom
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HasDerivAtHeisenbergThetaSeries
section
open scoped ComplexConjugate Matrix NNReal ENNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP GlobalTheory.Core.Rk.SWLaw
open GlobalTheory.Core.Rk.SW
open scoped ContDiff

noncomputable section

namespace GlobalTheory.Core.Rk.OntoDer

theorem hasDerivAt_term {G : Type} [AddCommGroup G] (a : ℝ →+ G) (p : G →+ ℂ) (κ : ℂ) (hκ : ∀ t : ℝ, p (a t) = t * κ)
    (φ φ₁ : G → ℂ) (hφ : ∀ x, HasDerivAt (fun t : ℝ => φ (x + a t)) (φ₁ x) 0) (u : G) (s : ℝ) :
    HasDerivAt (fun t : ℝ => Complex.exp (t * p (a t) + t * p u + t * p u) * φ (u + a t))
      (Complex.exp (s * p (a s) + s * p u + s * p u) * ((p + p) (u + a s) * φ (u + a s) + φ₁ (u + a s))) s := by
  have h1 : HasDerivAt (fun t : ℝ => φ (u + a t)) (φ₁ (u + a s)) s := by
    have h := hφ (u + a s)
    rw [← sub_self s] at h
    have h' := HasDerivAt.comp_sub_const s s h
    refine h'.congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => ?_)
    show φ (u + a t) = φ (u + a s + a (t - s))
    rw [map_sub, add_assoc, add_sub_cancel]
  have h0 : HasDerivAt (fun t : ℝ => (t : ℂ)) 1 s := Complex.ofRealCLM.hasDerivAt
  have h2 := (((h0.mul (h0.mul_const κ)).add (h0.mul_const (p u))).add (h0.mul_const (p u))).cexp
  have h3 := h2.mul h1
  simp only [hκ]
  refine h3.congr_deriv ?_
  simp only [AddMonoidHom.add_apply, map_add, hκ, Pi.add_apply, Pi.mul_apply]
  ring

variable {D : D7}

theorem two_halves (S T : HSp D) (x y : WO S T) : symplO S T x y = symplOH S T x y + symplOH S T x y := by
  unfold symplOH
  rw [← add_mul, ← map_add, add_halves, map_one, one_mul]

theorem phase_identity {S S₀ T : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (x y a b ξ : Mx D T.rank ρ) :
    symplOH S T (d.extX T x + d.extY T y) (d.extX T a + d.extY T b) +
        (-(symplOH S T (d.extX T (x + a)) (d.extY T (y + b)))) + symplO S T (d.extX T (x + a + ξ)) (d.extY T (y + b)) =
      -(symplOH S T (d.extX T x) (d.extY T y)) + symplO S T (d.extX T (x + ξ)) (d.extY T y) +
        (symplOH S T (d.extX T a) (d.extY T b) + symplOH S T (d.extX T (x + ξ)) (d.extY T b) +
          symplOH S T (d.extX T (x + ξ)) (d.extY T b)) := by
  simp only [two_halves, map_add, GlobalTheory.WeilVacMove.symplOH_add_left, GlobalTheory.WeilVacMove.symplOH_add_right,
    HypDec.symplOH_extX_extX, HypDec.symplOH_extY_extY,
    GlobalTheory.WeilVacMove.symplOH_skew S T (d.extX T a) (d.extY T y)]
  ring

theorem eq_ext (A B : HSp D) (w : WO (dblSp A) B) :
    w = (dblDec A).extX B (HMul.hMul w (dblDec A).jX) + (dblDec A).extY B (HMul.hMul w (dblDec A).jY) := by
  have h0 : HMul.hMul (dblDec A).j0 (dblDec A).p0 = (0 : Mx D (dblSp A).rank (dblSp A).rank) := by
    ext i j
    rw [Matrix.mul_apply]
    exact Finset.sum_eq_zero fun k _ => Fin.elim0 k
  have h := (dblDec A).sum_eq_one
  rw [h0, add_zero] at h
  rw [HypDec.extX_apply, HypDec.extY_apply, Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_add, h, Matrix.mul_one]

def mulLine {m n k : ℕ} (M : ℝ →+ Mx D m n) (j : Mx D n k) : ℝ →+ Mx D m k where
  toFun t := HMul.hMul (M t) j
  map_zero' := by rw [map_zero, Matrix.zero_mul]
  map_add' s t := by rw [map_add, Matrix.add_mul]

theorem continuous_mulLine {m n k : ℕ} {M : ℝ →+ Mx D m n} (hM : Continuous M) (j : Mx D n k) :
    Continuous (mulLine M j) := hM.matrix_mul continuous_const

theorem map_mul_zero {m n k : ℕ} {R : Type} [CommRing R] (q : AE D →+* R) {u : Mx D m n} (hu : u.map q = 0)
    (j : Mx D n k) : (HMul.hMul u j : Mx D m k).map q = 0 := by
  rw [Matrix.map_mul, hu, Matrix.zero_mul]

theorem exists_summable_bound {θ : InfFam D} (hθ : IsInfFam θ) {m n : ℕ} {φ : Mx D m n → ℂ}
    (hφ : GlobalTheory.IndefiniteRowSideFullHecke.SchwartzBruhatMixedFamilies.IsSchwartzBruhat φ) {Q : Set (Mx D m n)} (hQ : IsCompact Q) :
    ∃ b : Matrix (Fin m) (Fin n) D.host.E → ℝ, Summable b ∧ ∀ x ∈ Q, ∀ ξ, ‖φ (x + rat ξ)‖ ≤ b ξ := by
  obtain ⟨N, hN⟩ := GlobalTheory.T.exists_summable_bound_schwartz_majorant_rational_translates D θ hθ m n
  obtain ⟨-, K, hK, hC⟩ := GlobalTheory.T.schwartzBruhatAdelicMatrix_continuous_le_majorant D θ hθ m n φ hφ
  obtain ⟨C, hC⟩ := hC N
  obtain ⟨b, hb, hb'⟩ := hN K Q hK hQ
  refine ⟨fun ξ => |C| * b ξ, hb.mul_left _, fun x hx ξ => (hC _).trans ?_⟩
  exact mul_le_mul (le_abs_self C) (hb' x hx ξ) (GlobalTheory.Unf.maj_nonneg _ _ _ _) (abs_nonneg C)

set_option maxHeartbeats 1600000 in

theorem hasDerivAt_heisO_thetaSeries : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (A B : HSp D) (φ : Mx D B.rank A.rank → ℂ), GlobalTheory.IndefiniteRowSideFullHecke.SchwartzBruhatMixedFamilies.IsSchwartzBruhat φ → ∀ f : WO (dblSp A) B → ℂ, (∀ w : WO (dblSp A) B, f w = ψ (-(symplOH (dblSp A) B ((dblDec A).extX B (HMul.hMul w (dblDec A).jX)) ((dblDec A).extY B (HMul.hMul w (dblDec A).jY)))) * ∑' ξ : Matrix (Fin B.rank) (Fin A.rank) D.host.E, ψ (symplO (dblSp A) B ((dblDec A).extX B (HMul.hMul w (dblDec A).jX + rat ξ)) ((dblDec A).extY B (HMul.hMul w (dblDec A).jY))) * φ (HMul.hMul w (dblDec A).jX + rat ξ)) → ∀ M : ℝ →+ WO (dblSp A) B, Continuous M → (∀ t, (M t).map (finPart D) = 0) → ∃ φ' : Mx D B.rank A.rank → ℂ, GlobalTheory.IndefiniteRowSideFullHecke.SchwartzBruhatMixedFamilies.IsSchwartzBruhat φ' ∧ ∀ f' : WO (dblSp A) B → ℂ, (∀ w : WO (dblSp A) B, f' w = ψ (-(symplOH (dblSp A) B ((dblDec A).extX B (HMul.hMul w (dblDec A).jX)) ((dblDec A).extY B (HMul.hMul w (dblDec A).jY)))) * ∑' ξ : Matrix (Fin B.rank) (Fin A.rank) D.host.E, ψ (symplO (dblSp A) B ((dblDec A).extX B (HMul.hMul w (dblDec A).jX + rat ξ)) ((dblDec A).extY B (HMul.hMul w (dblDec A).jY))) * φ' (HMul.hMul w (dblDec A).jX + rat ξ)) → ∀ w, HasDerivAt (fun t : ℝ => heisO ψ (dblSp A) B (M t) f w) (f' w) 0 := by
  intro D ψ hψ A B φ hφ f hf M hM hM0
  obtain ⟨θ, hθ⟩ := hψ.2.1
  obtain ⟨lam, hl, hlam⟩ := GlobalTheory.WeilVacMove.exists_log hψ
  have hn : ∀ z, ‖ψ z‖ = 1 := hψ.1.2.1
  haveI : IsTopologicalAddGroup (AE D) := IsTopologicalRing.to_topologicalAddGroup
  let d := dblDec A
  let a : ℝ →+ Mx D B.rank A.rank := mulLine M d.jX
  let b : ℝ →+ Mx D B.rank A.rank := mulLine M d.jY
  let L : ℝ →+ WO (dblSp A) B := mulLine b d.pY
  have ha : Continuous a := continuous_mulLine hM _
  have hL : Continuous L := continuous_mulLine (continuous_mulLine hM _) _
  have ha0 : ∀ t, (a t).map (finPart D) = 0 := fun t => map_mul_zero _ (hM0 t) _
  have hL0 : ∀ t, (L t).map (finPart D) = 0 := fun t => map_mul_zero _ (map_mul_zero _ (hM0 t) _) _
  let p : Mx D B.rank A.rank →+ ℂ := (GlobalTheory.WeilVacMove.phase lam (dblSp A) B (L 1)).comp (d.extX B)
  have hX : Continuous (d.extX B) := continuous_id.matrix_mul continuous_const
  have hp : Continuous p := hl.comp (GlobalTheory.WeilVacMove.continuous_symplOH (dblSp A) B hX continuous_const)
  have hp0 : ∀ u : Mx D B.rank A.rank, u.map (infPart D) = 0 → p u = 0 := fun u hu => by
    show lam (symplOH (dblSp A) B (d.extX B u) (L 1)) = 0
    rw [(GlobalTheory.WeilVacMove.symplOH_fin_real (dblSp A) B (d.extX B u) (L 1) (map_mul_zero _ hu _) (hL0 1)).1, map_zero]
  have hψp : ∀ (u : Mx D B.rank A.rank) (t : ℝ),
      ψ (symplOH (dblSp A) B (d.extX B u) (d.extY B (b t))) = Complex.exp (t * p u) := fun u t =>
    GlobalTheory.WeilVacMove.psi_sympl_line hl hlam hL hL0 (d.extX B u) t
  have hκ : ∀ t : ℝ, p (a t) = t * p (a 1) := fun t =>
    GlobalTheory.WeilVacMove.additive_real (p.comp a) (hp.comp ha) t
  obtain ⟨hd, hm, hadd⟩ := GlobalTheory.T.isSchwartzBruhatAdelicMatrix_closed_deriv_linear_add D _ _ φ hφ
  obtain ⟨φ₁, hφ₁, hder⟩ := hd a ha ha0
  have hℓ := hm (p + p) (hp.add hp) fun u hu => by rw [AddMonoidHom.add_apply, hp0 u hu, add_zero]
  have hφ' := (GlobalTheory.T.isSchwartzBruhatAdelicMatrix_closed_deriv_linear_add D _ _ _ hℓ).2.2 φ₁ hφ₁
  refine ⟨_, hφ', fun f' hf' w => ?_⟩
  set φ' : Mx D B.rank A.rank → ℂ := (fun x => (p + p) x * φ x) + φ₁ with hφ'def
  let x : Mx D B.rank A.rank := HMul.hMul w d.jX
  let y : Mx D B.rank A.rank := HMul.hMul w d.jY
  let c : Matrix (Fin B.rank) (Fin A.rank) D.host.E → ℂ := fun ξ =>
    ψ (symplO (dblSp A) B (d.extX B (x + rat ξ)) (d.extY B y))
  let e : Matrix (Fin B.rank) (Fin A.rank) D.host.E → ℝ → ℂ := fun ξ t =>
    Complex.exp (t * p (a t) + t * p (x + rat ξ) + t * p (x + rat ξ))
  have he : ∀ ξ t, e ξ t = ψ (symplOH (dblSp A) B (d.extX B (a t)) (d.extY B (b t)) +
      symplOH (dblSp A) B (d.extX B (x + rat ξ)) (d.extY B (b t)) +
      symplOH (dblSp A) B (d.extX B (x + rat ξ)) (d.extY B (b t))) := fun ξ t => by
    rw [AddChar.map_add_eq_mul, AddChar.map_add_eq_mul, hψp, hψp, ← Complex.exp_add, ← Complex.exp_add]
  have he0 : ∀ ξ, e ξ 0 = 1 := fun ξ => by simp [e]
  have hform : ∀ t, heisO ψ (dblSp A) B (M t) f w =
      ψ (-(symplOH (dblSp A) B (d.extX B x) (d.extY B y))) * ∑' ξ, c ξ * (e ξ t * φ (x + rat ξ + a t)) := by
    intro t
    have e1 : HMul.hMul (w + M t) (dblDec A).jX = x + a t := Matrix.add_mul _ _ _
    have e2 : HMul.hMul (w + M t) (dblDec A).jY = y + b t := Matrix.add_mul _ _ _
    have e3 : symplOH (dblSp A) B w (M t) =
        symplOH (dblSp A) B (d.extX B x + d.extY B y) (d.extX B (a t) + d.extY B (b t)) :=
      congrArg₂ (symplOH (dblSp A) B) (eq_ext A B w) (eq_ext A B (M t))
    rw [heisO, hf, e1, e2, e3, ← mul_assoc, ← tsum_mul_left, ← tsum_mul_left]
    refine tsum_congr fun ξ => ?_
    rw [he, add_right_comm x (rat ξ) (a t), ← mul_assoc, ← mul_assoc, ← mul_assoc, ← AddChar.map_add_eq_mul,
      ← AddChar.map_add_eq_mul, ← AddChar.map_add_eq_mul, ← AddChar.map_add_eq_mul, phase_identity]
  have hQ : IsCompact ((fun t : ℝ => x + a t) '' Set.Icc (-1) 1) :=
    isCompact_Icc.image (continuous_const.add ha)
  obtain ⟨u, hu, hu'⟩ := exists_summable_bound hθ hφ' hQ
  obtain ⟨v, hv, hv'⟩ := exists_summable_bound hθ hφ (isCompact_singleton (x := x))
  have key := hasDerivAt_tsum_of_isPreconnected (t := Set.Ioo (-1 : ℝ) 1) (y₀ := (0 : ℝ)) (y := (0 : ℝ))
    (g := fun ξ t => c ξ * (e ξ t * φ (x + rat ξ + a t)))
    (g' := fun ξ t => c ξ * (e ξ t * φ' (x + rat ξ + a t))) hu isOpen_Ioo isPreconnected_Ioo
    (fun ξ t _ => (hasDerivAt_term a p _ hκ φ φ₁ hder (x + rat ξ) t).const_mul (c ξ))
    (fun ξ t ht => by
      rw [norm_mul, norm_mul, he, hn, hn, one_mul, one_mul, add_right_comm]
      exact hu' _ ⟨t, Set.Ioo_subset_Icc_self ht, rfl⟩ ξ)
    (by norm_num)
    (Summable.of_norm_bounded hv fun ξ => by
      rw [norm_mul, norm_mul, he, hn, hn, one_mul, one_mul, map_zero, add_zero]
      exact hv' x rfl ξ)
    (by norm_num)
  simp only [he0, map_zero, add_zero, one_mul] at key
  rw [hf', funext hform]
  exact key.const_mul _

end GlobalTheory.Core.Rk.OntoDer

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsCompactOpenProductLevelsFamily
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.QPl ValuativeRel
open GlobalTheory.PosOne (toOne Covers TriPos)
open GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage (app HasTensorVal fl opEFJ IsQuotIntFJ RFJ)
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (IsCO)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.QVal GlobalTheory.FinPl

noncomputable section

namespace GlobalTheory.QVal.LevCO

variable {D : D7}

theorem isCO_iSup_map (V : HSp D) {r : ℕ} (k : Fin r → Type) [∀ i, Field (k i)] [∀ i, ValuativeRel (k i)]
    [∀ i, TopologicalSpace (k i)] [∀ i, IsNonarchimedeanLocalField (k i)] (q : ∀ i, GlobalTheory.FinPl.SplitPt D (k i))
    (hq : Function.Injective fun i => (q i).v) (Y : Fin r → Type) [∀ i, Fintype (Y i)] [∀ i, DecidableEq (Y i)]
    (F : ∀ i, GlobalTheory.LocMod.Frame (k i) V.rank (Y i)) (gl : ∀ i, GL (Y i) (k i) →* GA D V)
    (hgl : ∀ i g, SuppAt (q i).e V (gl i g) ∧ (mt V (gl i g)).map (q i).pr = (F i).β * g.val * (F i).γ)
    (L : ∀ i, Subgroup (GL (Y i) (k i))) (hL : ∀ i, IsCO (L i)) :
    IsCO ((⨆ i, (L i).map (gl i)).subgroupOf (GlobalTheory.FinPl.grpAt V (fun p => ∃ i, (q i).v = p))) := by
  set P : GlobalTheory.FinPl.Pl D → Prop := fun p => ∃ i, (q i).v = p with hPdef
  have hA : GlobalTheory.FinPl.grpAt V P = GlobalTheory.FinPl.grpAt V (fun p => ∃ i, p = (q i).v) := by
    congr 1
    funext p
    exact propext ⟨fun ⟨i, h⟩ => ⟨i, h.symm⟩, fun ⟨i, h⟩ => ⟨i, h.symm⟩⟩
  obtain ⟨Ψ, hc, -, -, huniq⟩ := GlobalTheory.FixLev.exists_section V k q hq Y F
  let lh : ∀ i, GA D V →* GL (Y i) (k i) := fun i => GlobalTheory.FixLev.locHom (q i) V (F i)
  have hlh_self : ∀ i g, lh i (gl i g) = g := fun i g =>
    Units.ext (GlobalTheory.FixLev.frame_cancel (F i) ((GlobalTheory.FixLev.locHom_spec _ _ _ _).symm.trans (hgl i g).2))
  have hmat_ne : ∀ i j, i ≠ j → ∀ g, (mt V (gl j g)).map (q i).pr = 1 := fun i j hij g =>
    GlobalTheory.T.matrix_proj_eq_one_of_suppAt_distinct_finitePlace D (k i) (k j) (q i) (q j) V (gl j g) (fun e => hij (hq e)) (hgl j g).1
  have hlh_ne : ∀ i j, i ≠ j → ∀ g, lh i (gl j g) = 1 := fun i j hij g => Units.ext (by
    show (F i).γ * (mt V (gl j g)).map (q i).pr * (F i).β = 1
    rw [hmat_ne i j hij g, Matrix.mul_one, (F i).γβ])
  set H := ⨆ i, (L i).map (gl i) with hHdef
  have hglA : ∀ i g, gl i g ∈ GlobalTheory.FinPl.grpAt V P := fun i g =>
    GlobalTheory.T.mem_supportedSubgroup_of_suppAt_splitPlace_mem D (k i) (q i) V _ (hgl i g).1 P ⟨i, rfl⟩
  have hHL : ∀ x ∈ H, ∀ i, lh i x ∈ L i := by
    intro x hx i
    have hle : H ≤ (L i).comap (lh i) := iSup_le fun j => Subgroup.map_le_iff_le_comap.2 fun g hg => by
      show lh i (gl j g) ∈ L i
      by_cases hij : i = j
      · subst hij
        rw [hlh_self]
        exact hg
      · rw [hlh_ne i j hij]
        exact one_mem _
    exact hle hx
  let Φ : (∀ i, GL (Y i) (k i)) → GA D V := fun y => ((List.finRange r).map fun i => gl i (y i)).prod
  have hΦA : ∀ y, Φ y ∈ GlobalTheory.FinPl.grpAt V P := fun y =>
    Subgroup.list_prod_mem _ fun z hz => by
      obtain ⟨i, -, rfl⟩ := List.mem_map.1 hz
      exact hglA i (y i)
  have hΦH : ∀ y, (∀ i, y i ∈ L i) → Φ y ∈ H := fun y hy =>
    Subgroup.list_prod_mem _ fun z hz => by
      obtain ⟨i, -, rfl⟩ := List.mem_map.1 hz
      exact Subgroup.mem_iSup_of_mem i (Subgroup.mem_map_of_mem _ (hy i))
  have hΦloc : ∀ y i, (mt V (Φ y)).map (q i).pr = (F i).β * (y i).val * (F i).γ := fun y i => by
    show (mt V ((List.finRange r).map fun i => gl i (y i)).prod).map (q i).pr = _
    rw [GlobalTheory.FixLev.map_mt_list_prod, List.map_map]
    exact (GlobalTheory.FixLev.list_prod_single (fun i' => (mt V (gl i' (y i'))).map (q i).pr) i
      (fun i' hi' => hmat_ne i i' (Ne.symm hi') _) _ (List.nodup_finRange r) (List.mem_finRange i)).trans
      (hgl i (y i)).2
  have hΨΦ : ∀ y, Ψ y = Φ y := fun y => huniq (Φ y) (by rw [← hA]; exact hΦA y) y (hΦloc y)
  have hx_eq : ∀ x ∈ GlobalTheory.FinPl.grpAt V P, Ψ (fun i => lh i x) = x := fun x hx =>
    huniq x (by rw [← hA]; exact hx) _ fun i => GlobalTheory.FixLev.locHom_spec _ _ _ x
  have hmem : ∀ x : GlobalTheory.FinPl.grpAt V P, (x : GA D V) ∈ H ↔ ∀ i, lh i x ∈ L i := fun x =>
    ⟨fun h => hHL _ h, fun h => by rw [← hx_eq x x.2, hΨΦ]; exact hΦH _ h⟩
  refine ⟨?_, ?_⟩
  · have hset : ((H.subgroupOf (GlobalTheory.FinPl.grpAt V P) : Subgroup _) : Set (GlobalTheory.FinPl.grpAt V P)) =
        ⋂ i, (fun g : GlobalTheory.FinPl.grpAt V P => lh i g.1) ⁻¹' (L i : Set _) := by
      ext g
      simp only [SetLike.mem_coe, Subgroup.mem_subgroupOf, Set.mem_iInter, Set.mem_preimage]
      exact hmem g
    rw [hset]
    exact isOpen_iInter_of_finite fun i =>
      (hL i).1.preimage ((GlobalTheory.FixLev.continuous_locHom _ _ _).comp continuous_subtype_val)
  · rw [Subtype.isCompact_iff]
    have himg : (((↑) : GlobalTheory.FinPl.grpAt V P → GA D V) ''
        ((H.subgroupOf (GlobalTheory.FinPl.grpAt V P) : Subgroup _) : Set (GlobalTheory.FinPl.grpAt V P))) =
        Ψ '' Set.pi Set.univ fun i => (L i : Set _) := by
      ext g
      constructor
      · rintro ⟨x, hx, rfl⟩
        have hx' : (x : GA D V) ∈ H := Subgroup.mem_subgroupOf.1 hx
        exact ⟨fun i => lh i x, fun i _ => hHL _ hx' i, hx_eq x x.2⟩
      · rintro ⟨y, hy, rfl⟩
        refine ⟨⟨Ψ y, ?_⟩, ?_, rfl⟩
        · rw [hΨΦ]
          exact hΦA y
        · show Ψ y ∈ H
          rw [hΨΦ]
          exact hΦH y fun i => hy i (Set.mem_univ _)
    rw [himg]
    exact (isCompact_univ_pi fun i => (hL i).2).image hc

theorem isCO_levJ_levB : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (σ : ℕ) (S : Dbl2 ψ σ) (r : ℕ) (Q : Fin r → QStep S),
    Function.Injective (fun i => (Q i).q.v) → IsCO (levJ Q) ∧ IsCO (levB Q) := by
  intro D ψ σ S r Q hinj
  exact ⟨isCO_iSup_map S.J.W (fun i => (Q i).k) (fun i => (Q i).q) hinj _ (fun i => (Q i).F.G₁) (fun i => (Q i).gl₁)
      (fun i g => (Q i).loc₁ g) (fun i => (Q i).L₁.J) (fun i => (Q i).co₁),
    isCO_iSup_map S.B'.V (fun i => (Q i).k) (fun i => (Q i).q) hinj _ (fun i => (Q i).F.G₂) (fun i => (Q i).gl₂)
      (fun i g => (Q i).loc₂ g) (fun i => (Q i).L₂.J) (fun i => (Q i).co₂)⟩

end GlobalTheory.QVal.LevCO

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsJointlySmoothBiThetaWeilRepSecondVariable
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.BiActRight

open GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger GlobalTheory.ChiGrid GlobalTheory.BiTransfer

variable {D : D7}

theorem conjSource_conjAdjoint_apply {S A' : HSp D} (omb : Om S A') (g : GA D S) (h : GA D A') (f : WO S A' → ℂ)
    (y : WO A' S) :
    conjSource (conjAdjoint omb) (negGA A' h, g) (fun y' => f (dagger A' S y')) y = omb (g, h) f (dagger A' S y) := by
  have e1 : conjSource (conjAdjoint omb) (negGA A' h, g) =
      cjEnd (Equiv.refl (WO A' S)) (cjEnd (daggerEquiv S A') (omb (g, h))) := by
    simp only [conjSource, conjAdjoint, MonoidHom.comp_apply, MonoidHom.prodMap, MonoidHom.coe_mk, OneHom.coe_mk,
      MulEquiv.coe_toMonoidHom, MulEquiv.symm_apply_apply, MonoidHom.id_apply, Prod.map]
    rfl
  have e2 : (fun y' => f (dagger A' S y')) =
      GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj (Equiv.refl (WO A' S)) (GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj (daggerEquiv S A') f) := by
    funext y'; simp [GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj, daggerEquiv]
  rw [e1, e2, cjEnd_cj, cjEnd_cj]
  simp [GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj, daggerEquiv]

theorem resS_symm_swap {W A B : HSp D} (d : OrthDec W A B) (T : HSp D) (u : WO A T) (y : WO B T) :
    (d.symm.resS T).symm (y, u) = (d.resS T).symm (u, y) :=
  add_comm (y ⬝ d.pB) (u ⬝ d.pA)

theorem isBiTheta_act_right : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (A S A' : HSp D) (χS' χA' : (AE D)ˣ →* Circle) (omb : Om S A'), IsWeilDatumO ψ S A' χS' χA' omb → ∀ C, IsBiTheta ψ A S A' C → ∀ q, IsBiTheta ψ A S A' fun u v => omb q (C u) v := by
  intro D ψ A S A' χS' χA' omb hω C hC q
  obtain ⟨g, h⟩ := q
  have hw1 := ((GlobalTheory.T.weilConjugationAdjointRule_standard_char D ψ hω.std S A').conj_adjoint χS' χA' omb hω).1
  have hw2 := ((GlobalTheory.T.weilConjugationAdjointRule_standard_char D ψ hω.std A' S).conj_source χA' χS' (conjAdjoint omb) hw1).1
  let d := sumDec A (negSp A')
  have hG := (GlobalTheory.T.weil_operator_commutes_superposition_slices_source D ψ _ (negSp A') A S d.symm _ _ (conjSource (conjAdjoint omb)) hw2 _ (isThetaFunO_join d hC)
    Unit 0 (fun _ => 0) (fun _ => 0) measurable_const (integrable_zero _ _ _) (negGA A' h, g)).1
  refine isBiTheta_of_join d ?_
  convert hG using 1
  funext x
  simp only [resS_symm_swap, join_symm]
  exact (conjSource_conjAdjoint_apply omb g h (C (d.resS S x).1) (d.resS S x).2).symm

end GlobalTheory.BiActRight

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsOneCombSphLevel
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.QPl ValuativeRel
open GlobalTheory.PosOne (toOne Covers TriPos)
open GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage (app HasTensorVal fl opEFJ IsQuotIntFJ RFJ)
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (IsCO)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.QPl.SphOne

theorem isOneComb_sph_level : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (n : Type) [Fintype n] [DecidableEq n] (c P : ℕ), 1 ≤ P → P ≤ c → ∀ (ψ : AddChar k Circle), Continuous ψ → HasConductor ψ 1 → ∀ ν : Measure k, IsUnitVol ν → ∀ (L : Level (GL (n ⊕ Fin c) k)), L.J = KO k _ → (∀ j, L.lam j = 1) → IsOneComb ψ ν P L 1 (Finsupp.single 1 1) ∧ prX (Cgrp L.J 1) = KO k n := by
  intro k _ _ _ _ _ _ n _ _ c P h1 h2 ψ _ hψ ν hν L hJ hlam
  obtain ⟨J, lam⟩ := L
  dsimp only at hJ hlam
  subst hJ
  have e : lam = 1 := MonoidHom.ext fun j => hlam j
  subst e
  refine ⟨?_, GlobalTheory.QPl.PinTest.prX_KO⟩
  exact GlobalTheory.QPl.PinTest.isOneComb_sph hψ hν h1 h2

end GlobalTheory.QPl.SphOne
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LintegralBesselGroupHaarEqConstMulProdStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lintegral_besselGroup_haar_eq_const_mul_prod : ∀ (D : D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (u : D.what₂.Word) (ψ : AddChar (AF D.host.F) ℂ) (A : HSp D) (B : SBes X h u ψ A) (μSf : Measure (Formalism.L2.SG.Pf.SfinSub X.B.I X.eR (X.zR u))), μSf.IsHaarMeasure → SigmaFinite μSf → IsHaarOnSet X.B.I (X.SinfU u) (((X.muN u).prod (X.muH u)).map (fun p => p.1 * p.2)) → ∃ c : ℝ, 0 < c ∧ ∀ Φ : X.B.I.GA → ENNReal, Measurable Φ → ∫⁻ s, Φ (iotaX X h s.1) ∂B.lev.μR = ENNReal.ofReal c * ∫⁻ a, ∫⁻ t, Φ (a, t.1) ∂μSf ∂(((X.muN u).prod (X.muH u)).map (fun p => p.1 * p.2)) := by
  first | exact @GlobalTheory.Core.Mi.BesHaar.lintegral_besGrp_eq | exact GlobalTheory.Core.Mi.BesHaar.lintegral_besGrp_eq | (intros; apply GlobalTheory.Core.Mi.BesHaar.lintegral_besGrp_eq <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RamifiedLevelStabilizerIffAllDataStatement
section
open Formalism.BasicNotions
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ramifiedLevel_stabilizer_iff_all_data : ∀ D : D7, GlobalTheory.SeeSaw.RamIff D := by
  first | exact @GlobalTheory.SeeSaw.ramIff_all | exact GlobalTheory.SeeSaw.ramIff_all | (intros; apply GlobalTheory.SeeSaw.ramIff_all <;> assumption)
end

