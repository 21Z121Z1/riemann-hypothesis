import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0450
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.TwTransAlt
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0431
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0390
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0185
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0439
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.InstExists
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0019
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0024
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0443
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0451
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.OnFramesRdApply
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0036
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0035
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0030
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0017
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0018
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0149
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0452
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0029

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ResiduePairStabilizerKeepsIntegralLastCoordDivStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.SeeSaw GlobalTheory.LatPair GlobalTheory.SplitWeil
open GlobalTheory.Unf GlobalTheory.Grow GlobalTheory.FinPl ValuativeRel IsLocalRing
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.AdForm
open GlobalTheory.AdForm

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.residuePairStabilizer_keeps_integralLastCoordDiv : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (m' m : ℕ) (hm : m' = m) (b b' : Matrix (Fin m') (Fin m') k), b * b' = 1 → b' * b = 1 →
    ∀ P : Pair k (Fin m'), (∀ x, x ∈ P.lat ↔ ∀ r, (b *ᵥ x) r ∈ 𝒪[k]) →
    ∀ (c τ : k) (q : Unif k), valuation k τ = valuation k ((q.1 : 𝒪[k]) : k) → valuation k c = 1 →
    (∀ u : Fin m' → k, (∀ r, u r ∈ 𝒪[k]) → ∀ r0 : Fin m', r0.1 + 1 = m' →
      ∃ s : 𝒪[k], (s : k) = c * u r0 ∧ P.HasVal (b' *ᵥ u) (IsLocalRing.residue 𝒪[k] s)) →
    ∀ g : GL (Fin m') k, g • P = P →
      (b * g.val * b').reindex (finCongr hm) (finCongr hm) * (b * (g⁻¹).val * b').reindex (finCongr hm) (finCongr hm) = 1 ∧
      (∀ u : Fin m → k, ((∀ r, u r ∈ 𝒪[k]) ∧ ∀ r0 : Fin m, r0.1 + 1 = m → ∃ s ∈ 𝒪[k], u r0 = τ * s) ↔
        ((∀ r, ((b * g.val * b').reindex (finCongr hm) (finCongr hm) *ᵥ u) r ∈ 𝒪[k]) ∧
          ∀ r0 : Fin m, r0.1 + 1 = m → ∃ s ∈ 𝒪[k], ((b * g.val * b').reindex (finCongr hm) (finCongr hm) *ᵥ u) r0 = τ * s)) ∧
      (∀ u : Fin m → k, (∀ r, u r ∈ 𝒪[k]) ↔
        ∀ r, (((b * (g⁻¹).val * b').reindex (finCongr hm) (finCongr hm))ᵀ *ᵥ u) r ∈ 𝒪[k]) := by
  first | exact @GlobalTheory.PairKeep.keep | exact GlobalTheory.PairKeep.keep | (intros; apply GlobalTheory.PairKeep.keep <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RowLatticeSelfDualComponentsRescaledWordFrame
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (latV Moves MonoAt OrthAt PrimAt idAt intAt grpAt colMul Lat SplitPt GoodBF GluedCore IsSumFrame)
open GlobalTheory.SeeSaw (idV dI FI)
open ValuativeRel
open GlobalTheory.Core.Mi.LatMatch

noncomputable section

namespace GlobalTheory.Core.Mi.LatMatch

variable {D : D7}

def basY (X : HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) :
    Module.Basis (Fin (D.sp.Y 0).rank) D.host.E (VS D).V :=
  X.bas.reindex (finCongr (rank_eq X h)).symm

theorem cY_eq_basY (X : HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (z : (VS D).V) :
    GlobalTheory.Core.SBesEx.cY X h z = (basY X h).equivFun z := by
  funext k
  simp [GlobalTheory.Core.SBesEx.cY, HidaSetting.crd, crdOf, basY, Module.Basis.repr_reindex]

theorem mem_hermitianCoordinateLattice_iff (S : HSp D) (y : Fin S.rank → D.host.E) :
    y ∈ Formalism.L2.Herm.crdLat S S.L0 ↔ S.frame.equivFun.symm y ∈ S.L0 := by
  constructor
  · rintro ⟨w, hw, rfl⟩
    simpa [Formalism.L2.Herm.crd] using hw
  · intro hy
    exact ⟨_, hy, S.frame.equivFun.apply_symm_apply y⟩

theorem mem_rowLatticeYZeroFrame_iff_basis_sum (I : Formalism.MainNotions.S.AutInst) (hI : I = Formalism.L2.SG.InstExistsPf.instOf D)
    (ιE : I.E ≃+* D.host.E) (hId : ∀ x : I.E, HEq (ιE x) x) (bas : Module.Basis (Fin I.n) D.host.E (VS D).V)
    (hL : ∀ x : Fin I.n → I.E, x ∈ I.L ↔ (∑ i, ιE (x i) • bas i) ∈ (VS D).L0) (hn : (D.sp.Y 0).rank = I.n)
    (y : Fin (D.sp.Y 0).rank → D.host.E) :
    y ∈ latS D ↔ (∑ k, y k • bas (Fin.cast hn k)) ∈ (VS D).L0 := by
  subst hI
  have hι : ∀ x, ιE x = x := fun x => eq_of_heq (hId x)
  have e1 := hL y
  have e2 : (∑ i, ιE (y i) • bas i) = ∑ k, y k • bas (Fin.cast hn k) :=
    Finset.sum_congr rfl fun i _ => congrArg (· • bas i) (hι (y i))
  refine Iff.trans ?_ (e1.trans (Eq.to_iff (congrArg (· ∈ (VS D).L0) e2)))
  rw [mem_hermitianCoordinateLattice_iff]
  show _ ↔ y ∈ Formalism.L2.SG.InstExistsPf.Lv D
  rw [Formalism.L2.SG.InstExistsPf.mem_Lv, Module.Basis.equivFun_symm_apply]

theorem mem_latS (X : HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (hId : IdE X)
    (y : Fin (D.sp.Y 0).rank → D.host.E) :
    y ∈ latS D ↔ (basY X h).equivFun.symm y ∈ (VS D).L0 := by
  rw [mem_rowLatticeYZeroFrame_iff_basis_sum X.B.I h X.ιE hId X.bas X.L_eq (rank_eq X h), Module.Basis.equivFun_symm_apply]
  simp [basY]

theorem cY_mem_latS (X : HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (hId : IdE X) (z : (VS D).V) :
    GlobalTheory.Core.SBesEx.cY X h z ∈ latS D ↔ z ∈ (VS D).L0 := by
  rw [mem_latS X h hId, cY_eq_basY, LinearEquiv.symm_apply_apply]

theorem hT_swap (x y : (VS D).V) : (VS D).hT y x = star ((VS D).hT x y) := by
  have := (VS D).herm.eq x y
  rw [← this]
  rfl

end GlobalTheory.Core.Mi.LatMatch

namespace GlobalTheory.Core.Mi.LatMatch

variable {D : D7}

theorem hT_fY_mem (X : HidaSetting D) (i : Fin D.R.rS) {Y : (VS D).V} (hY : Y ∈ (VS D).L0) :
    (VS D).hT (X.fY i) Y ∈ aaD D i := by
  have key : (VS D).L0 ≤ (aaD D i : Submodule (𝓞 D.host.E) D.host.E).comap
      (((VS D).hT (X.fY i)).restrictScalars (𝓞 D.host.E)) := by
    rw [X.Lam_split]
    refine sup_le (sup_le ?_ ?_) ?_
    · refine Submodule.span_le.2 ?_
      rintro _ ⟨a, x, hx, rfl⟩
      show (VS D).hT (X.fY i) (x • X.eX a) ∈ (aaD D i : Submodule (𝓞 D.host.E) D.host.E)
      rw [map_smul, smul_eq_mul, hT_swap, X.ef]
      by_cases hai : a = i
      · subst hai; simpa using hx
      · simp [hai]
    · intro x hx
      show (VS D).hT (X.fY i) x ∈ (aaD D i : Submodule (𝓞 D.host.E) D.host.E)
      rw [((X.Lb_perp x hx) i).2]; exact zero_mem _
    · refine Submodule.span_le.2 ?_
      rintro _ ⟨a, x, hx, rfl⟩
      show (VS D).hT (X.fY i) (x • X.fY a) ∈ (aaD D i : Submodule (𝓞 D.host.E) D.host.E)
      rw [map_smul, X.ff, smul_zero]; exact zero_mem _
  exact key hY

theorem hT_eX_mem (X : HidaSetting D) (i : Fin D.R.rS) {Y : (VS D).V} (hY : Y ∈ (VS D).L0) :
    (VS D).hT (X.eX i) Y ∈ (aaD D i)⁻¹ := by
  have key : (VS D).L0 ≤ (((aaD D i)⁻¹ : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) :
      Submodule (𝓞 D.host.E) D.host.E).comap (((VS D).hT (X.eX i)).restrictScalars (𝓞 D.host.E)) := by
    rw [X.Lam_split]
    refine sup_le (sup_le ?_ ?_) ?_
    · refine Submodule.span_le.2 ?_
      rintro _ ⟨a, x, hx, rfl⟩
      show (VS D).hT (X.eX i) (x • X.eX a) ∈ (((aaD D i)⁻¹ : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) :
        Submodule (𝓞 D.host.E) D.host.E)
      rw [map_smul, X.ee, smul_zero]; exact zero_mem _
    · intro x hx
      show (VS D).hT (X.eX i) x ∈ (((aaD D i)⁻¹ : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) :
        Submodule (𝓞 D.host.E) D.host.E)
      rw [((X.Lb_perp x hx) i).1]; exact zero_mem _
    · refine Submodule.span_le.2 ?_
      rintro _ ⟨a, x, hx, rfl⟩
      show (VS D).hT (X.eX i) (x • X.fY a) ∈ (((aaD D i)⁻¹ : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) :
        Submodule (𝓞 D.host.E) D.host.E)
      rw [map_smul, smul_eq_mul, X.ef]
      by_cases hai : i = a
      · subst hai; simpa using hx
      · simp [hai]
  exact key hY

theorem smul_eX_mem_iff (X : HidaSetting D) (i : Fin D.R.rS) (c : D.host.E) :
    c • X.eX i ∈ (VS D).L0 ↔ c ∈ aaD D i := by
  constructor
  · intro hc
    have := hT_fY_mem X i hc
    rwa [map_smul, smul_eq_mul, hT_swap, X.ef, if_pos rfl, star_one, mul_one] at this
  · intro hc
    rw [X.Lam_split]
    exact Submodule.mem_sup_left (Submodule.mem_sup_left (Submodule.subset_span ⟨i, c, hc, rfl⟩))

theorem smul_fY_mem_iff (X : HidaSetting D) (i : Fin D.R.rS) (c : D.host.E) :
    c • X.fY i ∈ (VS D).L0 ↔ c ∈ (aaD D i)⁻¹ := by
  constructor
  · intro hc
    have := hT_eX_mem X i hc
    rwa [map_smul, smul_eq_mul, X.ef, if_pos rfl, mul_one] at this
  · intro hc
    rw [X.Lam_split]
    exact Submodule.mem_sup_right (Submodule.subset_span ⟨i, c, hc, rfl⟩)

end GlobalTheory.Core.Mi.LatMatch

namespace GlobalTheory.Core.Mi.LatMatch

variable {D : D7}

theorem star_smul_dotProduct {n : ℕ} (c : D.host.E) (v w : Fin n → D.host.E) :
    star (c • v) ⬝ᵥ w = star c * (star v ⬝ᵥ w) := by
  simp only [dotProduct, Pi.star_apply, Pi.smul_apply, smul_eq_mul, star_mul', Finset.mul_sum, mul_assoc]

theorem qX_mulVec_apply {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (y : Fin S.rank → D.host.E) (i : Fin ρ) :
    (d.qX *ᵥ y) i = star (fun r => d.e' r i) ⬝ᵥ (S.gram *ᵥ y) := by
  rw [HypDec.qX, ← Matrix.mulVec_mulVec]; rfl

theorem qY_mulVec_apply {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (y : Fin S.rank → D.host.E) (i : Fin ρ) :
    (d.qY *ᵥ y) i = star (fun r => d.e r i) ⬝ᵥ (S.gram *ᵥ y) := by
  rw [HypDec.qY, ← Matrix.mulVec_mulVec]; rfl

end GlobalTheory.Core.Mi.LatMatch

namespace GlobalTheory.Core.Mi.LatMatch

theorem latS_rescaled_frame : ∀ (D : D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (u : D.what₂.Word) (ψ : AddChar (AF D.host.F) ℂ) (A : HSp D) (B : SBes X h u ψ A) (μ lam : D.host.E), GlobalTheory.Core.Mi.IdE X → B.FrameAt μ lam → IsSelfDualC (D.sp.Y 0) (latS D) ∧ (∀ y ∈ latS D, ∀ i, (fun r => (B.d.qX *ᵥ y) i * B.d.e r i) ∈ latS D ∧ (fun r => (B.d.qY *ᵥ y) i * B.d.e' r i) ∈ latS D) ∧ (∀ (i : Fin D.R.rS) (t : D.host.E), t • (fun r => B.d.e r i) ∈ latS D ↔ GlobalTheory.Core.SBesEx.scl μ lam i * t ∈ aaD D i) ∧ ∀ (i : Fin D.R.rS) (t : D.host.E), t • (fun r => B.d.e' r i) ∈ latS D ↔ (star (GlobalTheory.Core.SBesEx.scl μ lam i))⁻¹ * t ∈ (aaD D i)⁻¹ := by
  intro D X h u ψ A B μ lam hId hF
  have hcY_smul : ∀ (c : D.host.E) (z : (VS D).V), c • GlobalTheory.Core.SBesEx.cY X h z = GlobalTheory.Core.SBesEx.cY X h (c • z) := by
    intro c z; rw [cY_eq_basY, cY_eq_basY, map_smul]
  have hcol_e : ∀ i, (fun r => B.d.e r i) = GlobalTheory.Core.SBesEx.scl μ lam i • GlobalTheory.Core.SBesEx.cY X h (X.eX i) := by
    intro i; funext r; rw [hF.e]; rfl
  have hcol_e' : ∀ i, (fun r => B.d.e' r i) =
      (star (GlobalTheory.Core.SBesEx.scl μ lam i))⁻¹ • GlobalTheory.Core.SBesEx.cY X h (X.fY i) := by
    intro i; funext r; rw [hF.e']; rfl
  have colE : ∀ i (t : D.host.E), t • (fun r => B.d.e r i) ∈ latS D ↔ GlobalTheory.Core.SBesEx.scl μ lam i * t ∈ aaD D i := by
    intro i t
    rw [hcol_e, smul_smul, hcY_smul, cY_mem_latS X h hId, smul_eX_mem_iff, mul_comm]
  have colE' : ∀ i (t : D.host.E), t • (fun r => B.d.e' r i) ∈ latS D ↔
      (star (GlobalTheory.Core.SBesEx.scl μ lam i))⁻¹ * t ∈ (aaD D i)⁻¹ := by
    intro i t
    rw [hcol_e', smul_smul, hcY_smul, cY_mem_latS X h hId, smul_fY_mem_iff, mul_comm]
  have hdot := @star_smul_dotProduct D (D.sp.Y 0).rank
  have hqX := qX_mulVec_apply B.d
  have hqY := qY_mulVec_apply B.d
  refine ⟨GlobalTheory.LineSelfDual.isSelfDualC_selfDualLatticeCoordsInFrame D (D.sp.Y 0), ?_, colE, colE'⟩
  intro y hy i
  have hY : (basY X h).equivFun.symm y ∈ (VS D).L0 := (mem_latS X h hId y).1 hy
  have hyY : y = GlobalTheory.Core.SBesEx.cY X h ((basY X h).equivFun.symm y) := by
    rw [cY_eq_basY, LinearEquiv.apply_symm_apply]
  set Y := (basY X h).equivFun.symm y
  constructor
  · have hq : (B.d.qX *ᵥ y) i = (GlobalTheory.Core.SBesEx.scl μ lam i)⁻¹ * (VS D).hT (X.fY i) Y := by
      rw [hqX, hcol_e', hdot, hyY, GlobalTheory.Core.SBesEx.cY_isom D X h hId Y (X.fY i), star_inv₀, star_star]
    show (B.d.qX *ᵥ y) i • (fun r => B.d.e r i) ∈ latS D
    rw [colE, hq]
    by_cases hs : GlobalTheory.Core.SBesEx.scl μ lam i = 0
    · rw [hs, zero_mul]; exact FractionalIdeal.mem_coe.mp (zero_mem _)
    · rw [← mul_assoc, mul_inv_cancel₀ hs, one_mul]; exact hT_fY_mem X i hY
  · have hq : (B.d.qY *ᵥ y) i = star (GlobalTheory.Core.SBesEx.scl μ lam i) * (VS D).hT (X.eX i) Y := by
      rw [hqY, hcol_e, hdot, hyY, GlobalTheory.Core.SBesEx.cY_isom D X h hId Y (X.eX i)]
    show (B.d.qY *ᵥ y) i • (fun r => B.d.e' r i) ∈ latS D
    rw [colE', hq]
    by_cases hs : star (GlobalTheory.Core.SBesEx.scl μ lam i) = 0
    · rw [hs, _root_.inv_zero, zero_mul]; exact FractionalIdeal.mem_coe.mp (zero_mem _)
    · rw [← mul_assoc, inv_mul_cancel₀ hs, one_mul]; exact hT_eX_mem X i hY

end GlobalTheory.Core.Mi.LatMatch

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SchrodingerFunctionUnitaryLeviRadicalActions
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

noncomputable section

namespace GlobalTheory.Core.Rk.SchLaws

variable {D : D7}

theorem isWeilDatumO_zero_one {ψ : AddChar (AF D.host.F) ℂ} {A B : HSp D} {χB : (AE D)ˣ →* Circle}
    {omh : WRep (dblSp A) B} (hW : IsWeilDatumO ψ (dblSp A) B 1 χB omh) :
    IsWeilDatumO ψ (zeroSp D) B 1 χB 1 where
  std := hW.std
  hecS := hW.hecS
  hecT := hW.hecT
  resS := ⟨hW.resS.1, fun η _ a => by rw [show (zeroSp D).rank = 0 from rfl, pow_zero]; rfl⟩
  resT := hW.resT
  om_pres := fun _ _ hf => hf
  om_heis := fun g h w₀ f _ => by
    have e : actO (zeroSp D) B g h w₀ = w₀ := Matrix.ext fun _ j => Fin.elim0 j
    rw [e]; rfl
  om_aut := fun _ _ _ _ _ _ => rfl
  om_cont := fun _ _ _ => continuous_const
  om_unit := fun _ _ _ _ _ _ _ => rfl
  om_split := fun e _ g h _ _ x y hx _ => by
    have hx1 : x = 1 := by
      apply Units.ext
      unfold IsDetAt at hx
      haveI : IsEmpty (Fin (zeroSp D).rank) := Fin.isEmpty
      rw [Matrix.det_isEmpty] at hx
      rw [hx]; simp
    refine ⟨1, one_pos, fun ℓ _ f _ => ?_⟩
    simp [splitFacO, hx1]

theorem chr_gramOf_eq (ψ : AddChar (AF D.host.F) ℂ) (A B : HSp D) (x : Mx D B.rank A.rank) (c : skewA D A.rank) :
    chr ψ (gramOf B x) c = ψ ((dblDec A).qS B c x) := by
  rw [chr, HypDec.qS, HypDec.symplOH_extX_extY, pairS, adj_mul, mem_skewA.1 c.2, Matrix.mul_assoc, Matrix.neg_mul,
    Matrix.trace_neg, map_neg (trHalf D), Matrix.trace_mul_comm, gramOf]

theorem sch_laws : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (A B : HSp D) (χB : (AE D)ˣ →* Circle) (omh : WRep (dblSp A) B), IsWeilDatumO ψ (dblSp A) B 1 χB omh → ∀ (ν : Measure (WO A B)) (𝓨 : Set (WO A B)), IsCovolOne (ratL B A) ν 𝓨 → ∀ f, IsThetaFunO ψ (dblSp A) B f → (∀ h x, sch ψ A B ν 𝓨 (omh (1, h) f) x = sch ψ A B ν 𝓨 f (mt B h⁻¹ ⬝ x)) ∧ (∀ (m : GL (Fin A.rank) (AE D)) x, sch ψ A B ν 𝓨 (omh ((dblDec A).levi m, 1) f) x = ((χB⁻¹ (Matrix.GeneralLinearGroup.det m) : Circle) : ℂ) * npow (absA D (Matrix.GeneralLinearGroup.det m)) ((B.rank : ℂ) / 2) * sch ψ A B ν 𝓨 f (x ⬝ m.1)) ∧ (∀ c x, sch ψ A B ν 𝓨 (omh ((dblDec A).nC c, 1) f) x = chr ψ (gramOf B x) c * sch ψ A B ν 𝓨 f x) ∧ swSec A B omh ν 𝓨 f 1 = sch ψ A B ν 𝓨 f 0 := by
  intro D ψ A B χB omh hW ν 𝓨 hν f hf
  have h := GlobalTheory.MixSourceFormulas.mixed_source D ψ (dblSp A) (zeroSp D) B A.rank (dblDec A) 1 χB omh 1 hW
    (isWeilDatumO_zero_one hW) ν 𝓨 hν f hf
  refine ⟨fun g x => ?_, fun m x => ?_, fun c x => ?_, ?_⟩
  · rw [sch, h.target]
    rfl
  · rw [sch, h.levi, Pi.smul_apply, smul_eq_mul, MonoidHom.inv_apply, GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.halfMod, GlobalTheory.Doubling.npow,
      Complex.ofReal_cpow (NNReal.coe_nonneg _)]
    push_cast
    rfl
  · rw [sch, h.centre, chr_gramOf_eq ψ A B]
    rfl
  · rw [sch, mixS_dblDec_zero, GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero.swSec, Prod.mk_one_one, map_one, Module.End.one_apply]

end GlobalTheory.Core.Rk.SchLaws

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SeeSawLastPeriodFactorizationOfClassDataStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.KJInf Formalism.L2.Forms GlobalTheory.SeeSaw
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.seeSawLastPeriodFactorization_of_classData : ∀ (D : D7) (c : Comm D) (𝒯 : Type) (t : 𝒯 → Tup c), c.Is → (∀ s, (t s).Is) → ClsPinD t → PerX t := by
  first | exact @GlobalTheory.SeeSaw.perX_of_clsPinD | exact GlobalTheory.SeeSaw.perX_of_clsPinD | (intros; apply GlobalTheory.SeeSaw.perX_of_clsPinD <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SelfDualLatticesConsecutiveStepStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.RootEx GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.SplitWeil GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.self_dual_lattices_consecutive_step : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : RealPack ex), PkHyp W → ∀ j, j + 1 < D.R.m → ∀ (g : GA D (Yc D j)) (g' : GA D (Yc D (j + 1))), g ∈ GfC (Yc D j) → g' ∈ GfC (Yc D (j + 1)) → ∀ (M : GlobalTheory.FinPl.Lat (Yc D j)) (M' : GlobalTheory.FinPl.Lat (Yc D (j + 1))), IsSelfDualC (Yc D j) M → IsSelfDualC (Yc D (j + 1)) M' → (∀ P, GlobalTheory.FinPl.Moves (Yc D j) g ((pk W).ΛY j) M P) → (∀ P, GlobalTheory.FinPl.Moves (Yc D (j + 1)) g' ((pk W).ΛY (j + 1)) M' P) → (∀ P, ∀ x ∈ GinfC (Yc D j), ∀ x' ∈ GinfC (Yc D (j + 1)), GlobalTheory.FinPl.Vac (pk W).ψ (Yc D j) (Yc D (j + 1)) M M' (fun _ => True) ((pk W).ωY W.P.A3.A.μ0 j (x * g, x' * g') (pureTensorO (pk W).ψ (pk W).θ (Yc D j) (Yc D (j + 1)) (cart ((pk W).MY j)) (cart ((pk W).MY (j + 1))) (onb ((pk W).MY j)) (onb ((pk W).MY (j + 1))) ((pk W).vac j) P))) ∧ (pk W).ωY W.P.A3.A.μ0 j (g, g') (pureTensorO (pk W).ψ (pk W).θ (Yc D j) (Yc D (j + 1)) (cart ((pk W).MY j)) (cart ((pk W).MY (j + 1))) (onb ((pk W).MY j)) (onb ((pk W).MY (j + 1))) ((pk W).vac j) 1) ≠ 0 := by
  first | exact @GlobalTheory.StepMove.fock_vac_moved | exact GlobalTheory.StepMove.fock_vac_moved | (intros; apply GlobalTheory.StepMove.fock_vac_moved <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SelfDualLatticesTopStep
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.RootEx GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.SplitWeil GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.TopMove

section Package

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks]
  [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks)

theorem weil_rec {n k : ℕ} (e : n = k) {χS χT : (AE D)ˣ →* Circle} {o : Om (Yc D n) D.sp.X'}
    (h : IsWeilDatumO R.ψ (Yc D n) D.sp.X' χS χT o) :
    IsWeilDatumO R.ψ (Yc D k) D.sp.X' χS χT (Eq.rec (motive := fun n _ => Om (Yc D n) D.sp.X') o e) := by
  subst e
  exact h

theorem vac_rec {n k : ℕ} (e : n = k) {f : WO (Yc D n) D.sp.X' → ℂ}
    (h : IsVacO R.ψ R.θ (Yc D n) D.sp.X' (cart (R.MY n)) (cart R.MX) (R.ΛY n) R.ΛX f) :
    IsVacO R.ψ R.θ (Yc D k) D.sp.X' (cart (R.MY k)) (cart R.MX) (R.ΛY k) R.ΛX
      (Eq.rec (motive := fun n _ => WO (Yc D n) D.sp.X' → ℂ) f e) := by
  subst e
  exact h

theorem weil_omT (hω : R.chain_ωX) (t : T) (j : ℕ) (h : j + 2 * 0 + 2 = D.R.m) :
    IsWeilDatumO R.ψ (Yc D (j + 1)) D.sp.X' (Lift.chrStep (R.toLevCh.mu t) R.eta D.R.m).1
      (Lift.chrStep (R.toLevCh.mu t) R.eta D.R.m).2 (omT R t j h) :=
  weil_rec R (idx_top h) (hω t)

theorem isVacO_vacT (hv : R.chain_vX) (t : T) (j : ℕ) (h : j + 2 * 0 + 2 = D.R.m) :
    IsVacO R.ψ R.θ (Yc D (j + 1)) D.sp.X' (cart (R.MY (j + 1))) (cart R.MX) (R.ΛY (j + 1)) R.ΛX (vacT R j h) :=
  vac_rec R (idx_top h) (hv t).1

end Package

theorem fock_vac_moved_top : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : RealPack ex), PkHyp W → ∀ j (h : j + 2 * 0 + 2 = D.R.m) (g : GA D (Yc D (j + 1))) (gT : GA D D.sp.X'), g ∈ GfC (Yc D (j + 1)) → gT ∈ GfC D.sp.X' → ∀ (M' : GlobalTheory.FinPl.Lat (Yc D (j + 1))) (LT : GlobalTheory.FinPl.Lat D.sp.X'), IsSelfDualC (Yc D (j + 1)) M' → IsSelfDualC D.sp.X' LT → (∀ P, GlobalTheory.FinPl.Moves (Yc D (j + 1)) g ((pk W).ΛY (j + 1)) M' P) → (∀ P, GlobalTheory.FinPl.Moves D.sp.X' gT (pk W).ΛX LT P) → (∀ P, GlobalTheory.FinPl.Vac (pk W).ψ (Yc D (j + 1)) D.sp.X' M' LT (fun _ => True) (omT (pk W) W.P.A3.A.μ0 j h (g, gT) (pureTensorO (pk W).ψ (pk W).θ (Yc D (j + 1)) D.sp.X' (cart ((pk W).MY (j + 1))) (cart (pk W).MX) (onb ((pk W).MY (j + 1))) (onb (pk W).MX) (vacT (pk W) j h) P))) ∧ omT (pk W) W.P.A3.A.μ0 j h (g, gT) (pureTensorO (pk W).ψ (pk W).θ (Yc D (j + 1)) D.sp.X' (cart ((pk W).MY (j + 1))) (cart (pk W).MX) (onb ((pk W).MY (j + 1))) (onb (pk W).MX) (vacT (pk W) j h) 1) ≠ 0 := by
  intro D L hT Gi Gl Kc Yd cX ex W hW j h g gT hg hgT M' LT hM' hLT hm hmT
  have hLev := hW.bot.hyp.2.2.2.1.lev
  have sdY : IsSelfDualC (Yc D (j + 1)) ((pk W).ΛY (j + 1)) :=
    GlobalTheory.SDFrameLattice.isSelfDualC_of_isSDFrame D _ _ _ _ (hLev.βY (j + 1) (by omega))
  have sdX : IsSelfDualC D.sp.X' (pk W).ΛX := GlobalTheory.SDFrameLattice.isSelfDualC_of_isSDFrame D _ _ _ _ hLev.βX
  have key := GlobalTheory.StepMove.gen (weil_omT (pk W) W.Q.charW.base.chain.ωX W.P.A3.A.μ0 j h) sdY hM' sdX hLT hg hgT (hm _) (hmT _)
    (onb ((pk W).MY (j + 1))) (onb (pk W).MX) (isVacO_vacT (pk W) W.Q.charW.base.chain.vX W.P.A3.A.μ0 j h)
  refine ⟨fun P => ?_, key.2⟩
  have h1 := key.1 P 1 (one_mem _) 1 (one_mem _)
  rwa [one_mul, one_mul] at h1

end GlobalTheory.TopMove

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SphericalParameterTransferSplitPlaceStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep
open GlobalTheory.FinZeta (Gv embV Kv VacFin IsLocKer KerU)
open GlobalTheory.SphTheta (IsStd CayleyRule intMat liftPar)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke IsCommensurated Tj SatU ordL Ov)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sphericalParameterTransfer_splitPlace : ∀ D : D7, TransferOn D fun v => IsSplit (E := D.host.E) v := by
  first | exact @GlobalTheory.ChainOnto.SplitTransfer.transferOn_isSplit | exact GlobalTheory.ChainOnto.SplitTransfer.transferOn_isSplit | (intros; apply GlobalTheory.ChainOnto.SplitTransfer.transferOn_isSplit <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitFrameGLFiniteMatrixOffPlaceEqOneStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.SeeSaw GlobalTheory.LatPair GlobalTheory.SplitWeil
open GlobalTheory.Unf GlobalTheory.Grow GlobalTheory.FinPl ValuativeRel IsLocalRing
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.AdForm

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.splitFrameGL_finiteMatrix_offPlace_eq_one : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : SplitPt D k) (S : HSp D) (n : Type) [Fintype n] [DecidableEq n] (β : Frame p S n) (g : GL n k) (m : ℕ) (hm : S.rank = m) (x : GL (Fin m) (EF D)), x.1 = finM S hm (β.gl g) → ∀ v : Pl D, v ≠ p.v → Formalism.UG.bc (Formalism.UG.prV (E := D.host.E) v) x = 1 := by
  first | exact @GlobalTheory.StabOff.bc_prV_finM_eq_one | exact GlobalTheory.StabOff.bc_prV_finM_eq_one | (intros; apply GlobalTheory.StabOff.bc_prV_finM_eq_one <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceBaseEqOfSameIdempotentPrimeStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.StepData GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.AdForm ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.splitPlace_baseEq_of_same_idempotentPrime : ∀ (D : D7) (k k' : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [Field k'] [ValuativeRel k'] [TopologicalSpace k'] [IsNonarchimedeanLocalField k'] (q : GlobalTheory.FinPl.SplitPt D k) (q' : GlobalTheory.FinPl.SplitPt D k') (PP : Formalism.L2.DIV.Pl D.host.E), Formalism.L2.NTheta.IsIdemAt q.e PP → Formalism.L2.NTheta.IsIdemAt q'.e PP → q.v = q'.v := by
  first | exact @GlobalTheory.FinPl.SplitPlace.v_eq_of_isIdemAt | exact GlobalTheory.FinPl.SplitPlace.v_eq_of_isIdemAt | (intros; apply GlobalTheory.FinPl.SplitPlace.v_eq_of_isIdemAt <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceConjPartLineMultipleMemIffStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.RootEx GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.SplitWeil GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.splitPlace_conjPart_lineMultiple_mem_iff : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (q : GlobalTheory.FinPl.SplitPt D k) (S : HSp D) (L : GlobalTheory.FinPl.Lat S) (Y : Type) [Fintype Y] [DecidableEq Y] (F : Frame k S.rank Y) (u u' : Fin S.rank → D.host.E) (m₁ : Y) (c₁ : k), IsSelfDualC S L → IntIn q S F L → valuation k c₁ = 1 → (∀ r, F.β r m₁ = c₁ * (ofSplit q).pr (u' r)) → (∑ r, ∑ r', star (u r) * S.gram r r' * u' r' = 1) → (∀ m, m ≠ m₁ → ∑ r, ∑ r', (ofSplit q).pr (star (u r)) * (ofSplit q).pr (S.gram r r') * F.β r' m = 0) → ∀ a : AE D, ((fun r => cA D q.e * (a * incA D (u r))) ∈ GlobalTheory.FinPl.latV S L (· = q.v) ↔ q.pr (cA D a) ∈ 𝒪[k]) := by
  first | exact @GlobalTheory.ColsConj.conj_part_mem_iff | exact GlobalTheory.ColsConj.conj_part_mem_iff | (intros; apply GlobalTheory.ColsConj.conj_part_mem_iff <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceFrameGLMemCompactRealTrivialStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.SeeSaw GlobalTheory.LatPair GlobalTheory.SplitWeil
open GlobalTheory.Unf GlobalTheory.Grow GlobalTheory.FinPl ValuativeRel IsLocalRing
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.AdForm

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.splitPlaceFrameGL_mem_compactRealTrivial : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : SplitPt D k) (S : HSp D) (n : Type) [Fintype n] [DecidableEq n] (β : Frame p S n) (g : GL n k), β.gl g ∈ GfC S := by
  first | exact @GlobalTheory.FrameGfC.gl_mem_GfC | exact GlobalTheory.FrameGfC.gl_mem_GfC | (intros; apply GlobalTheory.FrameGfC.gl_mem_GfC <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceFrameMovedBackIsLatticeBasisStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.StepData GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.AdForm ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.splitPlaceFrame_movedBack_isLatticeBasis : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (q : GlobalTheory.FinPl.SplitPt D k) (V : HSp D) (g : GA D V) (L N : GlobalTheory.FinPl.Lat V) (P : GlobalTheory.FinPl.Pl D → Prop), P q.v → IsSelfDualC V L → IsSelfDualC V N → GlobalTheory.FinPl.Moves V g L N P → ∀ (Y : Type) [Fintype Y] (β β' : Matrix (Fin V.rank) Y k), β = (Formalism.L2.Theta.mt V g).map q.pr * β' → (∀ y : Y → k, (∀ i, y i ∈ 𝒪[k]) ↔ (fun i => q.sec ((β *ᵥ y) i)) ∈ GlobalTheory.FinPl.latV V N (· = q.v)) → ∀ y : Y → k, (∀ i, y i ∈ 𝒪[k]) ↔ (fun i => q.sec ((β' *ᵥ y) i)) ∈ GlobalTheory.FinPl.latV V L (· = q.v) := by
  first | exact @GlobalTheory.FinPl.FrameBack.frame_back | exact GlobalTheory.FinPl.FrameBack.frame_back | (intros; apply GlobalTheory.FinPl.FrameBack.frame_back <;> assumption)
end

