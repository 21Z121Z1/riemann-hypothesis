import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0747
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0620
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0744
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0742
import Development.WeilBound.CoreStatements.AutomorphicKernels.UnitarySchrodingerModel.CoefDataExists
import Development.WeilBound.CoreStatements.PublishedTheorems.SiegelWeilSchrodinger.SiegelWeilUnitarySchrodingerLit
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0370
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0375
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.Bundle0003
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0363
import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.ThetaIdempotents.HeckeEta
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0745
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.IwasawaUnipotent.IwaU
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.SegmentCuspLines.CuspStdSubGeneric
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0004
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.UnipotentDerivatives.DerUnipLeUnipB
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0561
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TwistedJacquetPhiMinusEquiv
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0392
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CuspidalPairSubGeneric
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0222
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0746

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CellConditionsOfSmulEq
section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw PositivityTheory.Rg.Rsw.L GlobalTheory.CompanionTheory.MuC
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open IsDedekindDomain NumberField

noncomputable section

namespace GlobalTheory.CompanionTheory.MuC

variable {D : D7} {p : ℕ}

theorem isIdem_mul_self_right {S : Finset (Pl D)} {e : AE D} (he : IsIdem S e) : e * e = e := by
  have h : e * e - e = 0 := by
    refine GlobalTheory.CompanionTheory.AdeleComp.eq_zero_of_comps D _ (fun w => ?_) (fun v => ?_)
    · rw [RingHom.map_sub, RingHom.map_mul, he.1 w, mul_one, sub_self]
    · rw [RingHom.map_sub, RingHom.map_mul, he.2 v]
      split_ifs
      · rw [mul_one, sub_self]
      · rw [mul_zero, sub_self]
  exact sub_eq_zero.1 h

theorem entry_sub_one_of_bc {B : Type} [CommRing B] (φ : AE D →+* B) {u : G D p}
    (h : Formalism.UG.bc φ (GlobalTheory.AdelicU.matHom (AF D.host.F) D.sp.cm.sig (Jst D p) u) = 1)
    (i j : Fin (p + p)) : φ ((mat u - 1) i j) = 0 := by
  have h1 : φ.mapMatrix (mat u) = 1 := congrArg Units.val h
  have h2 : φ.mapMatrix (mat u - 1) = 0 := by
    rw [map_sub, h1, map_one, sub_self]
  exact congrFun (congrFun h2 i) j

theorem smul_mat_sub_one_eq_zero {S : Finset (Pl D)} {e : AE D} (he : IsIdem S e) {u : G D p}
    (hu : u ∈ KOff D p S) : e • (mat u - 1) = 0 := by
  obtain ⟨h1, h2, -⟩ := GlobalTheory.AdelicU.mem_levelOff.1 hu
  have h1' := GlobalTheory.AdelicU.mem_finPts_iff_forall.1 h1
  ext i j
  change e * (mat u - 1) i j = 0
  refine GlobalTheory.CompanionTheory.AdeleComp.eq_zero_of_comps D _ (fun w => ?_) (fun v => ?_)
  · have hb := GlobalTheory.AdelicU.matHom_projArch D.sp.cm.sig (Jst D p) w u
    rw [h1' w, map_one] at hb
    rw [RingHom.map_mul, entry_sub_one_of_bc _ (Units.ext (congrArg Units.val hb.symm)) i j, mul_zero]
  · rw [RingHom.map_mul, he.2 v]
    split_ifs with hv
    · have hb := GlobalTheory.AdelicU.matHom_proj D.sp.cm.sig (Jst D p) v u
      rw [h2 v hv, map_one] at hb
      have hc : cv D v ((mat u - 1) i j) = 0 :=
        entry_sub_one_of_bc _ (Units.ext (congrArg Units.val hb.symm)) i j
      rw [hc, mul_zero]
    · rw [zero_mul]

theorem smul_mat_mul_right {S : Finset (Pl D)} {e : AE D} (he : IsIdem S e) (g : G D p) {u : G D p}
    (hu : u ∈ KOff D p S) : e • mat (g * u) = e • mat g := by
  have h1 : e • mat u = e • (1 : Mx D (p + p) (p + p)) := by
    have := smul_mat_sub_one_eq_zero he hu
    rwa [smul_sub, sub_eq_zero] at this
  have h2 : mat (g * u) = mat g * mat u := rfl
  rw [h2, ← Matrix.mul_smul, h1, Matrix.mul_smul, mul_one]

theorem smul_lowC_mul_right {S : Finset (Pl D)} {e : AE D} (he : IsIdem S e) (g : G D p) {u : G D p}
    (hu : u ∈ KOff D p S) : e • lowC (g * u) = e • lowC g := by
  have h := smul_mat_mul_right he g hu
  ext i j
  exact congrFun (congrFun h _) _

theorem smul_lowD_mul_right {S : Finset (Pl D)} {e : AE D} (he : IsIdem S e) (g : G D p) {u : G D p}
    (hu : u ∈ KOff D p S) : e • lowD (g * u) = e • lowD g := by
  have h := smul_mat_mul_right he g hu
  ext i j
  exact congrFun (congrFun h _) _

theorem cell_conditions_of_smul_eq {R : Type*} [CommRing R] {n : Type*} [Fintype n] [DecidableEq n] {e : R}
    (hee : e * e = e) {c c' d d' x y : Matrix n n R} (hc : e • c' = e • c) (hd : e • d' = e • d)
    (hxe : e • x = x) (hy : y * c = e • (1 : Matrix n n R)) (hx : c * x = e • d) :
    (e • y) * c' = e • (1 : Matrix n n R) ∧ c' * x = e • d' := by
  constructor
  · rw [Matrix.smul_mul, ← Matrix.mul_smul, hc, Matrix.mul_smul, hy, smul_smul, hee]
  · calc c' * x = c' * (e • x) := by rw [hxe]
      _ = (e • c') * x := by rw [Matrix.mul_smul, Matrix.smul_mul]
      _ = (e • c) * x := by rw [hc]
      _ = c * (e • x) := by rw [Matrix.mul_smul, Matrix.smul_mul]
      _ = c * x := by rw [hxe]
      _ = e • d := hx
      _ = e • d' := hd.symm

theorem isB_of_smul_eq {S : Finset (Pl D)} {e : AE D} (he : IsIdem S e) {g g' : G D p}
    (hc : e • lowC g' = e • lowC g) (hd : e • lowD g' = e • lowD g) (x : hermS D p e)
    (h : IsB e g x) : IsB e g' x := by
  obtain ⟨⟨y, hy⟩, hx⟩ := h
  have hxe : e • x.1.1 = x.1.1 := x.2
  obtain ⟨h1, h2⟩ := cell_conditions_of_smul_eq (isIdem_mul_self_right he) hc hd hxe hy hx
  exact ⟨⟨e • y, h1⟩, h2⟩

theorem isB_mul_right_iff {D : D7} {p : ℕ} {S : Finset (Pl D)} {e : AE D} (he : IsIdem S e)
    {g u : G D p} (hu : u ∈ KOff D p S) (x : hermS D p e) : IsB e (g * u) x ↔ IsB e g x :=
  ⟨isB_of_smul_eq he (smul_lowC_mul_right he g hu).symm (smul_lowD_mul_right he g hu).symm x,
    isB_of_smul_eq he (smul_lowC_mul_right he g hu) (smul_lowD_mul_right he g hu) x⟩

end GlobalTheory.CompanionTheory.MuC

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CenterActsByScalarOnCyclicStatement
section
open Matrix Finset MeasureTheory
open scoped ContDiff ComplexConjugate InnerProductSpace
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD
open PositivityTheory.RgTw (Mat)
open GlobalTheory.CompanionTheory.GLK (e1 e2 f1)
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.center_acts_by_scalar_on_cyclic : ∀ (n : ℕ) (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] (F1 F2 : Fin n → Fin n → Module.End ℂ V), (∀ x : V, ∃ S : Submodule ℂ V, FiniteDimensional ℂ S ∧ x ∈ S ∧ ∀ a b, ∀ w ∈ S, kF F1 F2 a b w ∈ S) → ∀ (z : Module.End ℂ V), (∀ a b, z * F1 a b = F1 a b * z ∧ z * F2 a b = F2 a b * z) → ∀ (ev : V →ₗ[ℂ] ℂ) (c : ℂ), (∀ v, ev (z v) = c * ev v) → (∀ S : Submodule ℂ V, FiniteDimensional ℂ S → (∀ a b, ∀ w ∈ S, kF F1 F2 a b w ∈ S) → (∀ w ∈ S, ev w = 0) → ∀ w ∈ S, w = 0) → ∀ x : V, z x = c • x := by
  first | exact @GlobalTheory.CompanionTheory.ModelS.eq_smul_of_commute_of_ev | exact GlobalTheory.CompanionTheory.ModelS.eq_smul_of_commute_of_ev | (intros; apply GlobalTheory.CompanionTheory.ModelS.eq_smul_of_commute_of_ev <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CoefficientDataExistsStatement
section
noncomputable section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.coefficient_data_exists : PositivityTheory.PfSWUS.CoefDataExists := by
  first | exact @GlobalTheory.CompanionTheory.SWCoef.coefDataExists | exact GlobalTheory.CompanionTheory.SWCoef.coefDataExists | (intros; apply GlobalTheory.CompanionTheory.SWCoef.coefDataExists <;> assumption)
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConstantTermCofiniteIdealTransferStatement
section
open NumberField GlobalTheory.CuspRep MeasureTheory PositivityTheory.Affgl GlobalTheory.CompanionTheory.CTFin
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.constant_term_cofinite_ideal_transfer : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (r s : ℕ) (L : Subgroup (GL (Fin (r + s)) (Af E))), IsOpen (L : Set (GL (Fin (r + s)) (Af E))) → ∀ (W : Type) [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W] (ρ : Representation ℂ (Kinf E (r + s)) W), GlobalTheory.Published.AutFin.IsContRep ρ → ∀ J : Set (Module.End ℂ (Sm E (r + s))), Cofin J → ∀ J₁ : Set (Module.End ℂ (Sm E r)), Cofin J₁ → (∀ F : Sm E (r + s), (∀ (x : BlockIx (r + s) r → Ad E) (g : GA E (r + s)), F.1 (unip x * g) = F.1 g) → (∀ z ∈ J, z F = 0) → ∀ G : Sm E r, (∀ m, G.1 m = F.1 (lev (Ad E) r s (m, 1))) → ∀ z ∈ J₁, z G = 0) → ∀ (t : GL (Fin (r + s)) (Af E)) (κ : Kinf E (r + s)), ∃ (L₁ : Subgroup (GL (Fin r) (Af E))) (ρ₁ : Representation ℂ (Kinf E r) W), IsOpen (L₁ : Set (GL (Fin r) (Af E))) ∧ GlobalTheory.Published.AutFin.IsContRep ρ₁ ∧ ∀ F ∈ goodCT L ρ J, ∀ m₂ : GA E s, ∃ G ∈ genSpace L₁ ρ₁ J₁, ∀ m₁ : GA E r, G.1 m₁ = F.1 (lev (Ad E) r s (m₁, m₂) * finGL E (r + s) t * infGL E (r + s) (Unitary.toUnits κ)) := by
  first | exact @GlobalTheory.CompanionTheory.CTFin.Slice1.slice_mem_genSpace | exact GlobalTheory.CompanionTheory.CTFin.Slice1.slice_mem_genSpace | (intros; apply GlobalTheory.CompanionTheory.CTFin.Slice1.slice_mem_genSpace <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousUnipotentBlockFamily
section
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw PositivityTheory.Rg.Rsw.L GlobalTheory.CompanionTheory.MuC
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open IsDedekindDomain NumberField

namespace GlobalTheory.CompanionTheory.MuC

theorem continuous_unipotent_block_family {X R : Type} [TopologicalSpace X] [TopologicalSpace R] [Zero R] [One R] {n : ℕ}
    {f : X → Matrix (Fin n) (Fin n) R} (hf : Continuous f) :
    Continuous fun x => blk4 (1 : Matrix (Fin n) (Fin n) R) (f x) 0 1 := by
  unfold blk4
  exact (continuous_const.matrix_fromBlocks hf continuous_const continuous_const).matrix_submatrix _ _

theorem unipotent_block_mul_add {R : Type} [CommRing R] {n : ℕ} (b c : Matrix (Fin n) (Fin n) R) :
    blk4 (1 : Matrix (Fin n) (Fin n) R) b 0 1 * blk4 1 c 0 1 = blk4 1 (b + c) 0 1 := by
  unfold blk4
  rw [Matrix.submatrix_mul_equiv, Matrix.fromBlocks_multiply]
  simp [add_comm]

theorem continuous_nb {D : D7} {p : ℕ} {nb : hermA D p → G D p} (hnb : IsNMap nb) : Continuous nb := by
  have emb := isEmbedding_matHom (AF D.host.F) D.sp.cm.sig (Jst D p)
  rw [emb.continuous_iff, Units.continuous_iff]
  have hv : Continuous fun b : hermA D p => (b.1 : Mx D p p) := continuous_subtype_val
  have hm : ∀ b, (AdelicU.matHom _ D.sp.cm.sig (Jst D p) (nb b)).1 = blk4 1 b.1 0 1 := hnb
  constructor
  · refine (continuous_unipotent_block_family hv).congr fun b => ?_
    exact (hm b).symm
  · refine (continuous_unipotent_block_family hv.neg).congr fun b => ?_
    symm
    refine Units.inv_eq_of_mul_eq_one_right ?_
    simp only [Function.comp]
    rw [hm b, unipotent_block_mul_add]
    simp [blk4]

end GlobalTheory.CompanionTheory.MuC
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EisensteinFamilyHeightBoundStatement
section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eisenstein_family_height_bound : ∀ (D : D7) (n : ℕ) (H : G D n → ℝ≥0), IsHt H → (∃ C : Set (G D n), IsCompact C ∧ ∀ g, ∃ q ∈ P D n, ∃ c ∈ C, g = q * c) →
  ∀ (χ : (AE D)ˣ →* Circle) (s₁ : ℂ) (φ : G D n → ℂ), Continuous φ → IsLaw χ s₁ φ →
    ∃ B : ℝ, 0 ≤ B ∧ ∀ (z : ℂ) (g : G D n), ‖fam H φ s₁ z g‖ ≤ B * (H g : ℝ) ^ (z.re + (n : ℝ) / 2) := by
  first | exact @GlobalTheory.CompanionTheory.FamMajorant.fam_majorant | exact GlobalTheory.CompanionTheory.FamMajorant.fam_majorant | (intros; apply GlobalTheory.CompanionTheory.FamMajorant.fam_majorant <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EisensteinTopologyStatement
section
open PositivityTheory.Rg.SwEis
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eisenstein_topology : ETop := by
  first | exact @GlobalTheory.CompanionTheory.SwEisTop.eTop | exact GlobalTheory.CompanionTheory.SwEisTop.eTop | (intros; apply GlobalTheory.CompanionTheory.SwEisTop.eTop <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EqZeroOnUnitaryOfVanishAtOneStatement
section
open Matrix Finset MeasureTheory
open scoped ContDiff ComplexConjugate InnerProductSpace
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD
open PositivityTheory.RgTw (Mat)
open GlobalTheory.CompanionTheory.GLK (e1 e2 f1)
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eq_zero_on_unitary_of_vanish_at_one : ∀ (n : ℕ) (S : Submodule ℂ (GlobalTheory.CompanionTheory.ModelS.SmF n)), FiniteDimensional ℂ S → (∀ a b : Fin n, ∀ w ∈ S, GlobalTheory.CompanionTheory.ModelS.Kf a b w ∈ S) → (∀ w ∈ S, w.1 1 = 0) → ∀ w ∈ S, ∀ k : Matrix.unitaryGroup (Fin n) ℂ, w.1 k.1 = 0 := by
  first | exact @GlobalTheory.CompanionTheory.ModelS.Sep.main | exact GlobalTheory.CompanionTheory.ModelS.Sep.main | (intros; apply GlobalTheory.CompanionTheory.ModelS.Sep.main <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsHaarUnitaryGroupStatement
section
open Matrix Finset MeasureTheory
open scoped ContDiff ComplexConjugate InnerProductSpace
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD
open PositivityTheory.RgTw (Mat)
open GlobalTheory.CompanionTheory.GLK (e1 e2 f1)
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_haar_unitary_group : ∀ (n : ℕ) [MeasurableSpace (Matrix.unitaryGroup (Fin n) ℂ)] [BorelSpace (Matrix.unitaryGroup (Fin n) ℂ)], ∃ κ : Measure (Matrix.unitaryGroup (Fin n) ℂ), IsFiniteMeasure κ ∧ κ.IsMulRightInvariant ∧ κ.IsOpenPosMeasure := by
  first | exact @GlobalTheory.CompanionTheory.ModelS.exists_rightInvariant_measure_unitaryGroup | exact GlobalTheory.CompanionTheory.ModelS.exists_rightInvariant_measure_unitaryGroup | (intros; apply GlobalTheory.CompanionTheory.ModelS.exists_rightInvariant_measure_unitaryGroup <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsIrreducibleOfComp
section
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.BZMir GlobalTheory.BZSeg GlobalTheory.SplitWeil GlobalTheory.Published GlobalTheory.LocGL.SupportUnique GlobalTheory.SplitRead GlobalTheory.JHMult

noncomputable section

namespace GlobalTheory.CompanionTheory.DerClass

set_option synthInstance.maxHeartbeats 400000

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

variable (k) in

noncomputable def iterLevi (n : ℕ) : (j : ℕ) → (GL (Fin n) k →* Mir k (n + j))
  | 0 => levi k n
  | j + 1 => ((levi k (n + j + 1)).comp (Mir k (n + j)).subtype).comp (iterLevi n j)

abbrev dd (n j : ℕ) : Fin 2 → ℕ := ![n, j + 1]

theorem sum_dd (n j : ℕ) : ∑ a, dd n j a = n + j + 1 := by
  simp [dd, Fin.sum_univ_two, add_assoc]

abbrev ee (n j : ℕ) : (Σ a, Fin (dd n j a)) ≃ Fin (n + j + 1) := stdBlocks (dd n j) (sum_dd n j)

section Entries

variable {n j : ℕ} {g : GL (Fin (n + j + 1)) k}

end Entries

def blkF {n : ℕ} (g : Matrix (Fin n) (Fin n) k) (a b : ℕ) : k :=
  if h : a < n ∧ b < n then g ⟨a, h.1⟩ ⟨b, h.2⟩ else if a = b then 1 else 0

abbrev fstLevi (n j : ℕ) : GL (Fin (dd n j 0)) k →* Levi k fun a => Fin (dd n j a) :=
  MonoidHom.mulSingle (fun a => GL (Fin (dd n j a)) k) 0

end GlobalTheory.CompanionTheory.DerClass
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsKFiniteSubmoduleContainingStatement
section
open Matrix Finset MeasureTheory
open scoped ContDiff ComplexConjugate InnerProductSpace
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD
open PositivityTheory.RgTw (Mat)
open GlobalTheory.CompanionTheory.GLK (e1 e2 f1)
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_k_finite_submodule_containing : ∀ (n : ℕ) (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] (F1 F2 : Fin n → Fin n → Module.End ℂ V), Formalism.REAL.GlRel F1 → Formalism.REAL.GlRel F2 → (∀ a b c d, F1 a b * F2 c d = F2 c d * F1 a b) → ∀ f : V, (∀ x : V, ∃ T ∈ alg F1 F2, T f = x) → ∀ S₀ : Submodule ℂ V, FiniteDimensional ℂ S₀ → f ∈ S₀ → (∀ a b, ∀ w ∈ S₀, kF F1 F2 a b w ∈ S₀) → ∀ x : V, ∃ S : Submodule ℂ V, FiniteDimensional ℂ S ∧ x ∈ S ∧ ∀ a b, ∀ w ∈ S, kF F1 F2 a b w ∈ S := by
  first | exact @GlobalTheory.CompanionTheory.ModelS.LocFin.cyclic_locFin | exact GlobalTheory.CompanionTheory.ModelS.LocFin.cyclic_locFin | (intros; apply GlobalTheory.CompanionTheory.ModelS.LocFin.cyclic_locFin <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsPermShiftedWeightEqInfCharStatement
section
open Matrix Finset MeasureTheory
open scoped ContDiff ComplexConjugate InnerProductSpace
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD
open PositivityTheory.RgTw (Mat)
open GlobalTheory.CompanionTheory.GLK (e1 e2 f1)
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_perm_shifted_weight_eq_inf_char : ∀ (n : ℕ) (lam : Fin n → ℤ) (lev : Fin n → ℕ), IsLev lam lev → ∃ σ : Equiv.Perm (Fin n), ∀ a : Fin n, (GlobalTheory.CompanionTheory.ModelS.yZ lam lev a : ℂ) + ((n : ℂ) - 1) / 2 - ((a : ℕ) : ℂ) = infOf lam false (σ a) := by
  first | exact @GlobalTheory.CompanionTheory.ModelS.ReversedBlocks.exists_perm_yZ | exact GlobalTheory.CompanionTheory.ModelS.ReversedBlocks.exists_perm_yZ | (intros; apply GlobalTheory.CompanionTheory.ModelS.ReversedBlocks.exists_perm_yZ <;> assumption)
end

