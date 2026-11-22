import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.VacuumIwasawa.CwInvIota
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.SplitStab
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.Bundle0001
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilDatumProperties
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0038
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0051
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKsingGrp
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0025
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilAvacIwaA
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.LiftedSchrodingerDatum
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.AwayActions.FinBase
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0030
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0052
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.FockSpaces.Bundle0002
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0039
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0029
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LocalWeilOperators.Bundle0003
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0041
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0053

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilAvacKB
section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
namespace PositivityTheory.SiegelWeilFormula.Avac
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
open PositivityTheory.SiegelWeilFormula.KSing.UnitaryGroupBasics (mkGR inFrame_mul inFrame_one cw_mul cw_one form_w)
variable {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ}
theorem iota_vg_k (hO : _root_.PositivityTheory.SiegelWeilFormula.LocOpEx_k) (hI : _root_.PositivityTheory.SiegelWeilFormula.LocInst_k) (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (w : InfinitePlace F) (y : GR d.n) (hy : InK (mR y))
    {g : (Fin d.m × Fin d.n × Fin 2 → Af F) → ℂ} {Φ : d.Fn} (hΦ : Φ ∈ d.sch) (hT : d.T Φ = _root_.PositivityTheory.SiegelWeilFormula.Avac.vg_k R g) :
    ∃ c : ℂ, d.T (d.om (R.ι w y) Φ) = _root_.PositivityTheory.SiegelWeilFormula.Avac.vg_k R (c • g) := by
  obtain ⟨L, hL⟩ := hO F E σ d R w
  obtain ⟨sL, ρ, p, q, e, -, hld, -, hk⟩ := hI F E σ d R w L hL
  have h1 := (hL y _ _root_.PositivityTheory.SiegelWeilFormula.Avac.isSchwartz_fourierProjection_one).2 (_root_.PositivityTheory.SiegelWeilFormula.Avac.psiW_k R g w) (_root_.PositivityTheory.SiegelWeilFormula.Avac.psiW_indep_k R g w) Φ hΦ (hT.trans (_root_.PositivityTheory.SiegelWeilFormula.Avac.vg_tens_k R g w))
  refine ⟨F0 p q e y, ?_⟩
  rw [h1, hk y 1 hy, hld.kvac y hy, _root_.PositivityTheory.SiegelWeilFormula.Avac.vg_tens_k R _ w]
  funext X
  simp only [_root_.PositivityTheory.SiegelWeilFormula.RD_k.tens, _root_.PositivityTheory.SiegelWeilFormula.Avac.psiW_k, Pi.smul_apply, smul_eq_mul, _root_.PositivityTheory.SiegelWeilFormula.Avac.fP_smul_one_k]
  ring
theorem dZ_conjT_k {ζ : ℂ} : (dZ d.n ζ)ᴴ = dZ d.n (star ζ) := by
  simp [dZ, Matrix.fromBlocks_conjTranspose, Matrix.conjTranspose_smul]
theorem star_zeta_k (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) : star R.ζ = R.ζ⁻¹ := by
  rcases R.hζ with ⟨-, h⟩ | ⟨-, h⟩ <;> rw [h] <;> simp
theorem kdec_k (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (w : InfinitePlace F) (k : d.G)
    (hk : d.cw w (inFrame d.b k) * (d.cw w (inFrame d.b k))ᴴ = 1) :
    ∃ y : GR d.n, InK (mR y) ∧ d.cw w (inFrame d.b (R.ι w y)) = d.cw w (inFrame d.b k) := by
  have hζ0 := Krd.zeta_ne R.hζ
  obtain ⟨M, hM⟩ : ∃ M, M = d.cw w (inFrame d.b k) := ⟨_, rfl⟩
  have hY := Krd.inG_conj R.hζ M (hM ▸ _root_.PositivityTheory.SiegelWeilFormula.KSing.UnitaryGroupBasics.form_w_k d R w k)
  have hMM : Mᴴ * M = 1 := (Matrix.mul_eq_one_comm_of_equiv (Equiv.refl _)).1 (hM ▸ hk)
  refine ⟨mkGR _ hY, ⟨hY, ?_⟩, ?_⟩
  · show (dZ d.n R.ζ * M * dZ d.n R.ζ⁻¹)ᴴ * (dZ d.n R.ζ * M * dZ d.n R.ζ⁻¹) = 1
    have hA : (dZ d.n R.ζ)ᴴ = dZ d.n R.ζ⁻¹ := by rw [_root_.PositivityTheory.SiegelWeilFormula.Avac.dZ_conjT_k, _root_.PositivityTheory.SiegelWeilFormula.Avac.star_zeta_k]
    have hB : (dZ d.n R.ζ⁻¹)ᴴ = dZ d.n R.ζ := by rw [_root_.PositivityTheory.SiegelWeilFormula.Avac.dZ_conjT_k, star_inv₀, _root_.PositivityTheory.SiegelWeilFormula.Avac.star_zeta_k, inv_inv]
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, hA, hB]
    calc dZ d.n R.ζ * (Mᴴ * dZ d.n R.ζ⁻¹) * (dZ d.n R.ζ * M * dZ d.n R.ζ⁻¹)
        = dZ d.n R.ζ * (Mᴴ * (dZ d.n R.ζ⁻¹ * dZ d.n R.ζ) * M) * dZ d.n R.ζ⁻¹ := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [Krd.dZ_inv_mul hζ0, Matrix.mul_one, hMM, Matrix.mul_one, Krd.dZ_mul_inv hζ0]
  · rw [← hM]
    have h := R.at_w w (mkGR _ hY)
    calc d.cw w (inFrame d.b (R.ι w (mkGR _ hY)))
        = dZ d.n R.ζ⁻¹ * (dZ d.n R.ζ * d.cw w (inFrame d.b (R.ι w (mkGR _ hY)))) := by
          rw [← Matrix.mul_assoc, Krd.dZ_inv_mul hζ0, Matrix.one_mul]
      _ = dZ d.n R.ζ⁻¹ * (dZ d.n R.ζ * M * dZ d.n R.ζ⁻¹ * dZ d.n R.ζ) := by rw [h]; rfl
      _ = M := by
          simp only [Matrix.mul_assoc]
          rw [Krd.dZ_inv_mul hζ0, Matrix.mul_one, ← Matrix.mul_assoc, Krd.dZ_inv_mul hζ0, Matrix.one_mul]
theorem cw_inv_iota_k (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (w : InfinitePlace F) (y : GR d.n) (k : d.G) (w' : InfinitePlace F) :
    d.cw w' (inFrame d.b ((R.ι w y)⁻¹ * k)) = d.cw w' (inFrame d.b (R.ι w y)⁻¹) * d.cw w' (inFrame d.b k) := by
  rw [_root_.PositivityTheory.SiegelWeilFormula.KSing.UnitaryGroupBasics.inFrame_mul_k, _root_.PositivityTheory.SiegelWeilFormula.KSing.UnitaryGroupBasics.cw_mul_k]
theorem peel_k (hO : _root_.PositivityTheory.SiegelWeilFormula.LocOpEx_k) (hI : _root_.PositivityTheory.SiegelWeilFormula.LocInst_k) (hA : _root_.PositivityTheory.SiegelWeilFormula.FinAct_k) (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (S : Finset (InfinitePlace F)) :
    ∀ k : d.G, (∀ w ∈ S, d.cw w (inFrame d.b k) * (d.cw w (inFrame d.b k))ᴴ = 1) →
      (∀ w ∉ S, d.cw w (inFrame d.b k) = 1) → ∀ g ∈ SB (Fin d.m × Fin d.n × Fin 2 → Af F), ∀ Φ ∈ d.sch,
        d.T Φ = _root_.PositivityTheory.SiegelWeilFormula.Avac.vg_k R g → ∃ g' ∈ SB (Fin d.m × Fin d.n × Fin 2 → Af F), d.T (d.om k Φ) = _root_.PositivityTheory.SiegelWeilFormula.Avac.vg_k R g' := by
  induction S using Finset.induction_on with
  | empty =>
    intro k _ h1 g hg Φ hΦ hT
    obtain ⟨g', hg', H⟩ := hA F E σ d k (fun w => h1 w (Finset.notMem_empty w)) g hg
    exact ⟨g', hg', H _ (_root_.PositivityTheory.SiegelWeilFormula.Avac.gauss_indep_k R) Φ hΦ hT⟩
  | insert w S hw ih =>
    intro k h0 h1 g hg Φ hΦ hT
    obtain ⟨y, hy, hyw⟩ := _root_.PositivityTheory.SiegelWeilFormula.Avac.kdec_k R w k (h0 w (Finset.mem_insert_self w S))
    have hinv : ∀ w', w' ≠ w → d.cw w' (inFrame d.b (R.ι w y)⁻¹) = 1 := fun w' h => by
      rw [← map_inv]; exact R.off_w w w' y⁻¹ h
    have e1 : d.cw w (inFrame d.b (R.ι w y)⁻¹) * d.cw w (inFrame d.b (R.ι w y)) = 1 := by
      rw [← _root_.PositivityTheory.SiegelWeilFormula.KSing.UnitaryGroupBasics.cw_mul_k, ← _root_.PositivityTheory.SiegelWeilFormula.KSing.UnitaryGroupBasics.inFrame_mul_k, inv_mul_cancel, _root_.PositivityTheory.SiegelWeilFormula.Avac.inFrame_one_k, _root_.PositivityTheory.SiegelWeilFormula.KSing.UnitaryGroupBasics.cw_one_k]
    have hkw : d.cw w (inFrame d.b ((R.ι w y)⁻¹ * k)) = 1 := by rw [_root_.PositivityTheory.SiegelWeilFormula.Avac.cw_inv_iota_k, ← hyw, e1]
    have hkw' : ∀ w', w' ≠ w → d.cw w' (inFrame d.b ((R.ι w y)⁻¹ * k)) = d.cw w' (inFrame d.b k) := fun w' h => by
      rw [_root_.PositivityTheory.SiegelWeilFormula.Avac.cw_inv_iota_k, hinv w' h, Matrix.one_mul]
    obtain ⟨g₁, hg₁, e₁⟩ := ih ((R.ι w y)⁻¹ * k)
      (fun w' h => by
        rw [hkw' w' (fun e => hw (e ▸ h))]
        exact h0 w' (Finset.mem_insert_of_mem h))
      (fun w' h => by
        by_cases e : w' = w
        · rw [e, hkw]
        · rw [hkw' w' e]
          exact h1 w' fun h' => (Finset.mem_insert.1 h').elim e h)
      g hg Φ hΦ hT
    obtain ⟨c, e₂⟩ := _root_.PositivityTheory.SiegelWeilFormula.Avac.iota_vg_k hO hI R w y hy (d.ok.dbl.weil.2.1.pres _ Φ hΦ) e₁
    refine ⟨c • g₁, Submodule.smul_mem _ c hg₁, ?_⟩
    rw [show k = R.ι w y * ((R.ι w y)⁻¹ * k) from (mul_inv_cancel_left _ _).symm, map_mul, Module.End.mul_apply]
    exact e₂
theorem vg_K'_k (hO : _root_.PositivityTheory.SiegelWeilFormula.LocOpEx_k) (hI : _root_.PositivityTheory.SiegelWeilFormula.LocInst_k) (hA : _root_.PositivityTheory.SiegelWeilFormula.FinAct_k) (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d)
    {g : (Fin d.m × Fin d.n × Fin 2 → Af F) → ℂ} (hg : g ∈ SB _) {Φ : d.Fn} (hΦ : Φ ∈ d.sch) (hT : d.T Φ = _root_.PositivityTheory.SiegelWeilFormula.Avac.vg_k R g)
    {k : d.G} (hk : k ∈ d.K) : ∃ g' ∈ SB (Fin d.m × Fin d.n × Fin 2 → Af F), d.T (d.om k Φ) = _root_.PositivityTheory.SiegelWeilFormula.Avac.vg_k R g' :=
  _root_.PositivityTheory.SiegelWeilFormula.Avac.peel_k hO hI hA R Finset.univ k (fun w _ => ((d.ok.stdK k).1 hk).1 w) (fun w h => absurd (Finset.mem_univ w) h) g hg Φ hΦ hT
theorem vac_K'_k (hT : _root_.PositivityTheory.SiegelWeilFormula.TAll_k) (hF : _root_.PositivityTheory.SiegelWeilFormula.FockMem_k) (hO : _root_.PositivityTheory.SiegelWeilFormula.LocOpEx_k) (hI : _root_.PositivityTheory.SiegelWeilFormula.LocInst_k) (hA : _root_.PositivityTheory.SiegelWeilFormula.FinAct_k) (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) :
    ∀ Φ ∈ d.sch, d.T Φ ∈ R.vac → ∀ k ∈ d.K, d.T (d.om k Φ) ∈ R.vac := by
  let S' : Submodule ℂ d.Fn :=
    { carrier := {Φ | Φ ∈ d.sch ∧ ∀ k ∈ d.K, d.T (d.om k Φ) ∈ R.vac}
      zero_mem' := ⟨zero_mem _, fun k _ => by
        rw [map_zero]
        have : d.T 0 = 0 := (_root_.PositivityTheory.SiegelWeilFormula.Avac.Tl_k d).map_zero
        rw [this]; exact zero_mem _⟩
      add_mem' := fun {a b} ha hb => ⟨add_mem ha.1 hb.1, fun k hk => by
        rw [map_add]
        have : d.T (d.om k a + d.om k b) = d.T (d.om k a) + d.T (d.om k b) := (_root_.PositivityTheory.SiegelWeilFormula.Avac.Tl_k d).map_add _ _
        rw [this]; exact add_mem (ha.2 k hk) (hb.2 k hk)⟩
      smul_mem' := fun c a ha => ⟨Submodule.smul_mem _ c ha.1, fun k hk => by
        rw [map_smul]
        have : d.T (c • d.om k a) = c • d.T (d.om k a) := (_root_.PositivityTheory.SiegelWeilFormula.Avac.Tl_k d).map_smul _ _
        rw [this]; exact Submodule.smul_mem _ c (ha.2 k hk)⟩ }
  have hle : R.vac ≤ S'.map (_root_.PositivityTheory.SiegelWeilFormula.Avac.Tl_k d) := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨g, hg, rfl⟩
    have hm : _root_.PositivityTheory.SiegelWeilFormula.Avac.vg_k R g ∈ d.schM := (hF F E σ d R).1 (_root_.PositivityTheory.SiegelWeilFormula.Avac.vac_le_fock_k R (_root_.PositivityTheory.SiegelWeilFormula.Avac.vg_mem_k R hg))
    obtain ⟨Φ, hΦ, e⟩ := (hT.1 F E σ d).2.1 _ hm
    refine ⟨Φ, ⟨hΦ, fun k hk => ?_⟩, e⟩
    obtain ⟨g', hg', e'⟩ := _root_.PositivityTheory.SiegelWeilFormula.Avac.vg_K'_k hO hI hA R hg hΦ e hk
    rw [e']; exact _root_.PositivityTheory.SiegelWeilFormula.Avac.vg_mem_k R hg'
  intro Φ hΦ hv k hk
  obtain ⟨Φ', hΦ', e⟩ := hle hv
  have : Φ' = Φ := _root_.PositivityTheory.SiegelWeilFormula.Avac.T_inj_k hT.1 hΦ'.1 hΦ e
  rw [← this]
  exact hΦ'.2 k hk
end PositivityTheory.SiegelWeilFormula.Avac
end
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKawayFinBase
section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
namespace PositivityTheory.SiegelWeilFormula.KAway
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
namespace SDf
variable (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ)
theorem cw_eInf_k (w : InfinitePlace F) {p q : Type} (Z : Matrix p q (AE F E)) : d.cw w (eInf F • Z) = d.cw w Z := by
  ext i j
  simp only [_root_.PositivityTheory.SiegelWeilFormula.SD_k.cw, Matrix.map_apply, Matrix.smul_apply, St.piInf_smul, eInf_fst_apply, map_one, one_mul]
theorem cw_finOne_k (w : InfinitePlace F) {p q : Type} (Z : Matrix p q (AE F E)) : d.cw w (finOne F • Z) = 0 := by
  ext i j
  simp only [_root_.PositivityTheory.SiegelWeilFormula.SD_k.cw, Matrix.map_apply, Matrix.smul_apply, Place.piInf_finOne, Matrix.zero_apply]
theorem cw_zero_iff_k {p q : Type} (Z : Matrix p q (AE F E)) : (∀ w, d.cw w Z = 0) ↔ eInf F • Z = 0 := by
  constructor
  · intro h
    refine _root_.PositivityTheory.SiegelWeilFormula.Place.cw_ext_k d (fun w => ?_) ?_
    · rw [_root_.PositivityTheory.SiegelWeilFormula.KAway.SDf.cw_eInf_k, h w]
      ext i j
      simp [_root_.PositivityTheory.SiegelWeilFormula.SD_k.cw]
    · rw [smul_smul, finOne_mul_eInf, zero_smul, smul_zero]
  · intro h w
    rw [← _root_.PositivityTheory.SiegelWeilFormula.KAway.SDf.cw_eInf_k d w Z, h]
    ext i j
    simp [_root_.PositivityTheory.SiegelWeilFormula.SD_k.cw]
theorem cw_one_iff_k {p : Type} [DecidableEq p] (M : Matrix p p (AE F E)) :
    (∀ w, d.cw w M = 1) ↔ eInf F • M = eInf F • (1 : Matrix p p (AE F E)) := by
  have h1 : ∀ w, d.cw w (1 : Matrix p p (AE F E)) = 1 := fun w => by
    simp only [_root_.PositivityTheory.SiegelWeilFormula.SD_k.cw]
    exact Matrix.map_one _ (map_zero _) (map_one _)
  constructor
  · intro h
    refine _root_.PositivityTheory.SiegelWeilFormula.Place.cw_ext_k d (fun w => ?_) ?_
    · rw [_root_.PositivityTheory.SiegelWeilFormula.KAway.SDf.cw_eInf_k, _root_.PositivityTheory.SiegelWeilFormula.KAway.SDf.cw_eInf_k, h w, h1 w]
    · rw [smul_smul, smul_smul, finOne_mul_eInf, zero_smul, zero_smul]
  · intro h w
    rw [← _root_.PositivityTheory.SiegelWeilFormula.KAway.SDf.cw_eInf_k d w M, h, _root_.PositivityTheory.SiegelWeilFormula.KAway.SDf.cw_eInf_k, h1 w]
def InvFin_k (f : Mx F E d.m d.n → ℂ) : Prop := ∀ X Z, (∀ w, d.cw w Z = 0) → f (X + Z) = f X
def InvInf_k (G : Mx F E d.m d.n → ℂ) : Prop := ∀ X Z, finOne F • Z = 0 → G (X + Z) = G X
def fcrd_k (X : Mx F E d.m d.n) : Fin d.m × Fin d.n × Fin 2 → Af F := fun k => (d.crd X k).2
theorem gram_add_left_k (X X' Z : Mx F E d.m d.n) : d.gram (X + X') Z = d.gram X Z + d.gram X' Z := by
  simp only [_root_.PositivityTheory.SiegelWeilFormula.SD_k.gram, Matrix.transpose_add, Matrix.add_mul]
theorem gram_add_right_k (X Z Z' : Mx F E d.m d.n) : d.gram X (Z + Z') = d.gram X Z + d.gram X Z' := by
  simp only [_root_.PositivityTheory.SiegelWeilFormula.SD_k.gram]
  rw [Matrix.map_add _ (map_add _), Matrix.mul_add]
theorem gram_smul_left_k (c : AF F) (X Z : Mx F E d.m d.n) : d.gram (c • X) Z = c • d.gram X Z := by
  simp only [_root_.PositivityTheory.SiegelWeilFormula.SD_k.gram, Matrix.transpose_smul, Matrix.smul_mul]
theorem gram_smul_right_k (c : AF F) (X Z : Mx F E d.m d.n) : d.gram X (c • Z) = c • d.gram X Z := by
  simp only [_root_.PositivityTheory.SiegelWeilFormula.SD_k.gram]
  have : (c • Z).map (cA σ) = c • Z.map (cA σ) := by
    ext i j
    simp [map_smul]
  rw [this, Matrix.mul_smul]
theorem gram_fin_inf_k {X Z : Mx F E d.m d.n} (hX : eInf F • X = 0) (hZ : finOne F • Z = 0) : d.gram X Z = 0 := by
  have eX : X = finOne F • X := by
    conv_lhs => rw [← smul_split X, hX, zero_add]
  rw [eX, _root_.PositivityTheory.SiegelWeilFormula.KAway.SDf.gram_smul_left_k, ← _root_.PositivityTheory.SiegelWeilFormula.KAway.SDf.gram_smul_right_k, hZ]
  simp [_root_.PositivityTheory.SiegelWeilFormula.SD_k.gram]
theorem gram_inf_fin_k {X Z : Mx F E d.m d.n} (hX : finOne F • X = 0) (hZ : eInf F • Z = 0) : d.gram X Z = 0 := by
  have eZ : Z = finOne F • Z := by
    conv_lhs => rw [← smul_split Z, hZ, zero_add]
  rw [eZ, _root_.PositivityTheory.SiegelWeilFormula.KAway.SDf.gram_smul_right_k, ← _root_.PositivityTheory.SiegelWeilFormula.KAway.SDf.gram_smul_left_k, hX]
  simp [_root_.PositivityTheory.SiegelWeilFormula.SD_k.gram]
theorem tt_add_k (M M' : Mx F E d.n d.n) : d.tt (M + M') = d.tt M + d.tt M' := by
  simp only [_root_.PositivityTheory.SiegelWeilFormula.SD_k.tt, Matrix.trace_add, map_add]
theorem crd_add_k (X Z : Mx F E d.m d.n) (k) : d.crd (X + Z) k = d.crd X k + d.crd Z k := by
  simp only [_root_.PositivityTheory.SiegelWeilFormula.SD_k.crd, Matrix.add_apply, map_add, Finsupp.add_apply]
theorem crd_smul_k (c : AF F) (X : Mx F E d.m d.n) (k) : d.crd (c • X) k = c * d.crd X k := by
  simp only [_root_.PositivityTheory.SiegelWeilFormula.SD_k.crd, Matrix.smul_apply, map_smul, Finsupp.smul_apply, smul_eq_mul]
theorem cmb_crd_k (X : Mx F E d.m d.n) : d.cmb (d.crd X) = X := by
  ext i j
  simp only [_root_.PositivityTheory.SiegelWeilFormula.SD_k.cmb, _root_.PositivityTheory.SiegelWeilFormula.SD_k.crd]
  conv_rhs => rw [← (Algebra.TensorProduct.basis (AF F) d.bs).sum_repr (X i j)]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Algebra.TensorProduct.basis_apply, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
theorem cmb_smul_k (c : AF F) (x : Fin d.m × Fin d.n × Fin 2 → AF F) : d.cmb (fun k => c * x k) = c • d.cmb x := by
  ext i j
  simp only [_root_.PositivityTheory.SiegelWeilFormula.SD_k.cmb, Matrix.smul_apply, Finset.smul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [TensorProduct.smul_tmul', smul_eq_mul]
theorem fcrd_invInf_k (g : (Fin d.m × Fin d.n × Fin 2 → Af F) → ℂ) : _root_.PositivityTheory.SiegelWeilFormula.KAway.SDf.InvInf_k d (fun X => g (_root_.PositivityTheory.SiegelWeilFormula.KAway.SDf.fcrd_k d X)) := by
  intro X Z hZ
  show g (_root_.PositivityTheory.SiegelWeilFormula.KAway.SDf.fcrd_k d (X + Z)) = g (_root_.PositivityTheory.SiegelWeilFormula.KAway.SDf.fcrd_k d X)
  congr 1
  funext k
  show (d.crd (X + Z) k).2 = (d.crd X k).2
  rw [_root_.PositivityTheory.SiegelWeilFormula.KAway.SDf.crd_add_k]
  change (d.crd X k).2 + (d.crd Z k).2 = (d.crd X k).2
  have : (d.crd Z k).2 = 0 := by
    rw [← finOne_snd_mul (d.crd Z k), ← _root_.PositivityTheory.SiegelWeilFormula.KAway.SDf.crd_smul_k, hZ]
    simp [_root_.PositivityTheory.SiegelWeilFormula.SD_k.crd]
  rw [this, add_zero]
theorem invInf_fcrd_k {G : Mx F E d.m d.n → ℂ} (hG : _root_.PositivityTheory.SiegelWeilFormula.KAway.SDf.InvInf_k d G) (X : Mx F E d.m d.n) :
    G X = G (d.cmb fun k => pairA F 0 (_root_.PositivityTheory.SiegelWeilFormula.KAway.SDf.fcrd_k d X k)) := by
  set Y := d.cmb fun k => pairA F 0 (_root_.PositivityTheory.SiegelWeilFormula.KAway.SDf.fcrd_k d X k) with hY
  have hp : ∀ c : AF F, finOne F * c = pairA F 0 c.2 := fun c =>
    Prod.ext (finOne_fst_mul c) (finOne_snd_mul c)
  have e1 : finOne F • X = Y := by
    conv_lhs => rw [← _root_.PositivityTheory.SiegelWeilFormula.KAway.SDf.cmb_crd_k d X]
    rw [← _root_.PositivityTheory.SiegelWeilFormula.KAway.SDf.cmb_smul_k]
    simp only [hp, hY, _root_.PositivityTheory.SiegelWeilFormula.KAway.SDf.fcrd_k]
  have e2 : finOne F • Y = Y := by
    rw [hY, ← _root_.PositivityTheory.SiegelWeilFormula.KAway.SDf.cmb_smul_k]
    congr 1
    funext k
    rw [hp]
    rfl
  have h := hG Y (X - Y) (by rw [smul_sub, e1, e2, sub_self])
  rw [add_sub_cancel] at h
  exact h
def StepF_k (x : d.G) (A B : (Mx F E d.m d.n → ℂ) → Mx F E d.m d.n → ℂ) : Prop :=
  (∀ f, _root_.PositivityTheory.SiegelWeilFormula.KAway.SDf.InvFin_k d f → _root_.PositivityTheory.SiegelWeilFormula.KAway.SDf.InvFin_k d (A f)) ∧ ∀ G, _root_.PositivityTheory.SiegelWeilFormula.KAway.SDf.InvInf_k d G → _root_.PositivityTheory.SiegelWeilFormula.KAway.SDf.InvInf_k d (B G) ∧
    ∀ f, _root_.PositivityTheory.SiegelWeilFormula.KAway.SDf.InvFin_k d f → ∀ Φ ∈ d.sch, d.T Φ = (fun X => f X * G X) → d.T (d.om x Φ) = fun X => A f X * B G X
theorem step_comp_k {x x' : d.G} {A A' B B' : (Mx F E d.m d.n → ℂ) → Mx F E d.m d.n → ℂ}
    (h : _root_.PositivityTheory.SiegelWeilFormula.KAway.SDf.StepF_k d x A B) (h' : _root_.PositivityTheory.SiegelWeilFormula.KAway.SDf.StepF_k d x' A' B') : _root_.PositivityTheory.SiegelWeilFormula.KAway.SDf.StepF_k d (x * x') (A ∘ A') (B ∘ B') := by
  refine ⟨fun f hf => h.1 _ (h'.1 f hf), fun G hG => ⟨(h.2 _ (h'.2 G hG).1).1, fun f hf Φ hΦ hT => ?_⟩⟩
  have e1 := (h'.2 G hG).2 f hf Φ hΦ hT
  have e2 := (h.2 (B' G) (h'.2 G hG).1).2 (A' f) (h'.1 f hf) (d.om x' Φ) (d.om_sch x' Φ hΦ) e1
  rw [map_mul, Module.End.mul_apply]
  exact e2
theorem key_split_k {f G A' B' : Mx F E d.m d.n → ℂ} (hf : _root_.PositivityTheory.SiegelWeilFormula.KAway.SDf.InvFin_k d f) (hA : _root_.PositivityTheory.SiegelWeilFormula.KAway.SDf.InvFin_k d A') (hG : _root_.PositivityTheory.SiegelWeilFormula.KAway.SDf.InvInf_k d G)
    (hB : _root_.PositivityTheory.SiegelWeilFormula.KAway.SDf.InvInf_k d B') (h : ∀ X, f X * G X = A' X * B' X) : ∀ X Y, f X * G Y = A' X * B' Y := by
  intro X Y
  have hW1 : eInf F • X + finOne F • Y = X + finOne F • (Y - X) := by
    calc eInf F • X + finOne F • Y = (eInf F • X + finOne F • X) + finOne F • (Y - X) := by rw [smul_sub]; abel
      _ = X + finOne F • (Y - X) := by rw [smul_split]
  have hW2 : eInf F • X + finOne F • Y = Y + eInf F • (X - Y) := by
    calc eInf F • X + finOne F • Y = (eInf F • Y + finOne F • Y) + eInf F • (X - Y) := by rw [smul_sub]; abel
      _ = Y + eInf F • (X - Y) := by rw [smul_split]
  have hfin : ∀ w, d.cw w (finOne F • (Y - X)) = 0 := fun w => _root_.PositivityTheory.SiegelWeilFormula.KAway.SDf.cw_finOne_k d w _
  have hinf : finOne F • (eInf F • (X - Y)) = 0 := by rw [smul_smul, finOne_mul_eInf, zero_smul]
  have e := h (eInf F • X + finOne F • Y)
  rw [hW1, hf X _ hfin, hA X _ hfin, ← hW1, hW2, hG Y _ hinf, hB Y _ hinf] at e
  exact e
theorem step_conj_k (hT : _root_.PositivityTheory.SiegelWeilFormula.TAll_k) {x₁ x₂ x' : d.G} {A₁ A₂ B₁ B₂ B' : (Mx F E d.m d.n → ℂ) → Mx F E d.m d.n → ℂ}
    (h₁ : _root_.PositivityTheory.SiegelWeilFormula.KAway.SDf.StepF_k d x₁ A₁ B₁) (h₂ : _root_.PositivityTheory.SiegelWeilFormula.KAway.SDf.StepF_k d x₂ A₂ B₂) (h' : _root_.PositivityTheory.SiegelWeilFormula.KAway.SDf.StepF_k d x' id B') (h1 : x₁ * x₂ = 1) :
    ∃ B, _root_.PositivityTheory.SiegelWeilFormula.KAway.SDf.StepF_k d (x₁ * x' * x₂) id B := by
  have hc := _root_.PositivityTheory.SiegelWeilFormula.KAway.SDf.step_comp_k d (_root_.PositivityTheory.SiegelWeilFormula.KAway.SDf.step_comp_k d h₁ h') h₂
  have h0 := _root_.PositivityTheory.SiegelWeilFormula.KAway.SDf.step_comp_k d h₁ h₂
  refine ⟨fun G => if h : ∃ X₀, G X₀ ≠ 0 ∧ B₁ (B₂ G) X₀ ≠ 0 then
      (G h.choose / B₁ (B₂ G) h.choose) • B₁ (B' (B₂ G)) else 0,
    fun f hf => hf, fun G hG => ⟨?_, fun f hf Φ hΦ hTΦ => ?_⟩⟩
  · dsimp only
    split_ifs with h
    · intro X Z hZ
      simp only [Pi.smul_apply, smul_eq_mul]
      have e := (hc.2 G hG).1 X Z hZ
      simp only [Function.comp_apply] at e
      rw [e]
    · intro X Z _
      rfl
  · have e := (hc.2 G hG).2 f hf Φ hΦ hTΦ
    have e0 := (h0.2 G hG).2 f hf Φ hΦ hTΦ
    rw [h1, map_one, Module.End.one_apply, hTΦ] at e0
    have key := _root_.PositivityTheory.SiegelWeilFormula.KAway.SDf.key_split_k d hf (h0.1 f hf) hG (h0.2 G hG).1 (fun X => congrFun e0 X)
    by_cases hz : (∀ X, f X = 0) ∨ ∀ X, G X = 0
    · have hΦ0 : Φ = 0 := d.T_inj hT Φ hΦ (by
        rw [hTΦ]
        funext X
        rcases hz with hz | hz <;> simp [hz])
      subst hΦ0
      rw [map_zero, d.T_zero]
      funext X
      rcases hz with hz | hz
      · simp [hz]
      · have hn : ¬ ∃ X₀, G X₀ ≠ 0 ∧ B₁ (B₂ G) X₀ ≠ 0 := fun ⟨X₀, h, _⟩ => h (hz X₀)
        simp [dif_neg hn]
    · push Not at hz
      obtain ⟨⟨u₀, hu₀⟩, ⟨X₁, hX₁⟩⟩ := hz
      have hex : ∃ X₀, G X₀ ≠ 0 ∧ B₁ (B₂ G) X₀ ≠ 0 := by
        refine ⟨X₁, hX₁, fun h0' => ?_⟩
        have := key u₀ X₁
        simp only [Function.comp_apply] at this
        rw [h0', mul_zero] at this
        exact mul_ne_zero hu₀ hX₁ this
      have hB0 := hex.choose_spec.2
      have hA : ∀ u, A₁ (A₂ f) u = f u * (G hex.choose / B₁ (B₂ G) hex.choose) := by
        intro u
        have := key u hex.choose
        simp only [Function.comp_apply] at this
        rw [mul_div_assoc', eq_div_iff hB0]
        linear_combination -this
      rw [e]
      funext X
      simp only [Function.comp_apply, id_eq, dif_pos hex, Pi.smul_apply, smul_eq_mul, hA]
      ring
end SDf
end PositivityTheory.SiegelWeilFormula.KAway
end
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKfockFock
section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix SchwartzMap Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
namespace PositivityTheory.SiegelWeilFormula.KFock
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
theorem fockMem_k : _root_.PositivityTheory.SiegelWeilFormula.FockMem_k := by
  intro F E _ _ _ _ _ σ d R
  exact ⟨_root_.PositivityTheory.SiegelWeilFormula.KFock.fock_le_k d R, fun w Ψ hΨ => ⟨fun P => _root_.PositivityTheory.SiegelWeilFormula.KFock.away_tens_k R w Ψ hΨ P, _root_.PositivityTheory.SiegelWeilFormula.KFock.away_inv_k R w Ψ hΨ⟩, fun w f hf => _root_.PositivityTheory.SiegelWeilFormula.KFock.fock_dec_k R w f hf⟩
theorem T_sub_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (Φ Φ' : d.Fn) : d.T (Φ - Φ') = d.T Φ - d.T Φ' := by
  have h := _root_.PositivityTheory.SiegelWeilFormula.KFock.T_add_k d (Φ - Φ') Φ'
  rw [sub_add_cancel] at h
  exact eq_sub_of_add_eq h.symm
theorem T_inj_k (hB : _root_.PositivityTheory.SiegelWeilFormula.TBij_k) (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) {Φ Φ' : d.Fn} (h : Φ ∈ d.sch) (h' : Φ' ∈ d.sch) (e : d.T Φ = d.T Φ') : Φ = Φ' :=
  sub_eq_zero.mp ((hB F E σ d).2.2 _ (d.sch.sub_mem h h') (by rw [_root_.PositivityTheory.SiegelWeilFormula.KFock.T_sub_k, e, sub_self]))
theorem linLift_k (hB : _root_.PositivityTheory.SiegelWeilFormula.TBij_k) (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) {V : Type} [AddCommGroup V] [Module ℂ V] (t : V →ₗ[ℂ] (Mx F E d.m d.n → ℂ))
    (ht : ∀ v, t v ∈ d.schM) : ∃ φ : V →ₗ[ℂ] d.Fn, ∀ v, φ v ∈ d.sch ∧ d.T (φ v) = t v := by
  choose φ0 hφ0 using fun v => (hB F E σ d).2.1 (t v) (ht v)
  refine ⟨{ toFun := φ0, map_add' := fun v v' => ?_, map_smul' := fun a v => ?_ }, fun v => hφ0 v⟩
  · refine _root_.PositivityTheory.SiegelWeilFormula.KFock.T_inj_k hB d (hφ0 (v + v')).1 (d.sch.add_mem (hφ0 v).1 (hφ0 v').1) ?_
    rw [_root_.PositivityTheory.SiegelWeilFormula.KFock.T_add_k, (hφ0 _).2, (hφ0 _).2, (hφ0 _).2, map_add]
  · refine _root_.PositivityTheory.SiegelWeilFormula.KFock.T_inj_k hB d (hφ0 (a • v)).1 (d.sch.smul_mem a (hφ0 v).1) ?_
    rw [RingHom.id_apply, _root_.PositivityTheory.SiegelWeilFormula.KFock.T_smul_k, (hφ0 _).2, (hφ0 _).2, map_smul]
def tensP_k {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (w : InfinitePlace F) (Ψ : Mx F E d.m d.n → ℂ) : PX d.m d.n →ₗ[ℂ] (Mx F E d.m d.n → ℂ) where
  toFun P := R.tens w (fP P) Ψ
  map_add' P Q := by
    funext X
    simp only [_root_.PositivityTheory.SiegelWeilFormula.RD_k.tens, fP_add, Pi.add_apply, add_mul]
  map_smul' a P := by
    funext X
    simp only [_root_.PositivityTheory.SiegelWeilFormula.RD_k.tens, fP_smul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply, mul_assoc]
theorem liftEx_of_k : _root_.PositivityTheory.SiegelWeilFormula.TBij_k → _root_.PositivityTheory.SiegelWeilFormula.FockMem_k → _root_.PositivityTheory.SiegelWeilFormula.LiftEx_k := by
  intro hB hF F E _ _ _ _ _ σ d R w Ψ hΨ
  obtain ⟨φ, hφ⟩ := _root_.PositivityTheory.SiegelWeilFormula.KFock.linLift_k hB d (_root_.PositivityTheory.SiegelWeilFormula.KFock.tensP_k R w Ψ) fun P => (hF F E σ d R).1 (((hF F E σ d R).2.1 w Ψ hΨ).1 P)
  exact ⟨φ, hφ⟩
theorem liftEx_k (hB : _root_.PositivityTheory.SiegelWeilFormula.TBij_k) : _root_.PositivityTheory.SiegelWeilFormula.LiftEx_k := _root_.PositivityTheory.SiegelWeilFormula.KFock.liftEx_of_k hB _root_.PositivityTheory.SiegelWeilFormula.KFock.fockMem_k
theorem liftSw1_k (hB : _root_.PositivityTheory.SiegelWeilFormula.TBij_k) (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (w : InfinitePlace F) (f : (Fin d.m → Fin d.n → ℂ) → ℂ) (hf : IsSw f)
    (Ψ : Mx F E d.m d.n → ℂ) (hΨ : Ψ ∈ R.away w) : ∃ Φ ∈ d.sch, d.T Φ = R.tens w f Ψ :=
  (hB F E σ d).2.1 _ (_root_.PositivityTheory.SiegelWeilFormula.KFock.tens_mem_k d R w f hf Ψ hΨ)
end PositivityTheory.SiegelWeilFormula.KFock
end
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKfockGood
section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix SchwartzMap Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
namespace PositivityTheory.SiegelWeilFormula.KFock
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
theorem goodAwayEx_k : _root_.PositivityTheory.SiegelWeilFormula.GoodAwayEx_k := by
  intro F E _ _ _ _ _ σ d R w
  let g := (GlobalTheory.RealLift.intPts F (Fin d.m × Fin d.n × Fin 2)).indicator (1 : (Fin d.m × Fin d.n × Fin 2 → Af F) → ℂ)
  have hg : g ∈ SB (Fin d.m × Fin d.n × Fin 2 → Af F) := GlobalTheory.RealLift.indicator_intPts_mem_SB
  let Ψ : Mx F E d.m d.n → ℂ := fun X =>
    (∏ w' ∈ Finset.univ.erase w, fP (1 : PX d.m d.n) (R.loc w' X)) * g fun k => (d.crd X k).2
  have hΨ : Ψ ∈ R.away w := Submodule.subset_span ⟨fun _ => 1, g, hg, rfl⟩
  refine ⟨Ψ, _root_.PositivityTheory.SiegelWeilFormula.KFock.away_inv_k R w Ψ hΨ, fun h0 => ?_, fun f hf => _root_.PositivityTheory.SiegelWeilFormula.KFock.tens_mem_k d R w f hf Ψ hΨ⟩
  have h1 := congrFun h0 0
  have hc : (fun k => (d.crd (0 : Mx F E d.m d.n) k).2) = 0 := by
    funext k
    unfold _root_.PositivityTheory.SiegelWeilFormula.SD_k.crd
    rw [Matrix.zero_apply, map_zero, Finsupp.zero_apply]
    rfl
  have hg0 : g (fun k => (d.crd (0 : Mx F E d.m d.n) k).2) = 1 := by
    rw [hc]
    exact Set.indicator_of_mem GlobalTheory.RealLift.zero_mem_intPts _
  have hp : (∏ w' ∈ Finset.univ.erase w, fP (1 : PX d.m d.n) (R.loc w' 0)) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun w' _ => fP_one_ne _
  exact hp (by simpa [Ψ, hg0] using h1)
end PositivityTheory.SiegelWeilFormula.KFock
end
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKlocopLocJJA
section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix SchwartzMap Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
namespace PositivityTheory.SiegelWeilFormula
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
namespace RD
variable {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d)
theorem _root_.PositivityTheory.SiegelWeilFormula.RD_k.isW_eps (w : InfinitePlace F) {ε : ℤˣ} {w₀ : d.G} (h : d.IsW ε w₀) : ε = R.ε := by
  have hmem : (mat2 w₀)ᵀ * dbl (incM F d.Y.J) * (mat2 w₀).map (cA σ) = dbl (incM F d.Y.J) := w₀.2
  have hmat : mat2 w₀ = incM F d.b.1 * inFrame d.b w₀ * incM F (d.b⁻¹).1 := by
    simp only [inFrame, ← Matrix.mul_assoc]
    rw [_root_.PositivityTheory.SiegelWeilFormula.Krd.bb_k d, Matrix.one_mul, Matrix.mul_assoc, _root_.PositivityTheory.SiegelWeilFormula.Krd.bb_k d, Matrix.mul_one]
  have hc := congrArg (d.cw w) hmem
  rw [_root_.PositivityTheory.SiegelWeilFormula.Krd.cw_mul_k d, _root_.PositivityTheory.SiegelWeilFormula.Krd.cw_mul_k d, _root_.PositivityTheory.SiegelWeilFormula.Place.cw_cA_k d, _root_.PositivityTheory.SiegelWeilFormula.Krd.cw_transpose_k d, _root_.PositivityTheory.SiegelWeilFormula.Krd.dbl_incM_k d, _root_.PositivityTheory.SiegelWeilFormula.Krd.cw_incM_k d, hmat,
    _root_.PositivityTheory.SiegelWeilFormula.Krd.cw_mul_k d, _root_.PositivityTheory.SiegelWeilFormula.Krd.cw_mul_k d, _root_.PositivityTheory.SiegelWeilFormula.Krd.cw_incM_k d, _root_.PositivityTheory.SiegelWeilFormula.Krd.cw_incM_k d, _root_.PositivityTheory.SiegelWeilFormula.RD_k.cw_wM h w] at hc
  set P := d.b.1.map (d.B.emb w).1
  set Pi := (d.b⁻¹).1.map (d.B.emb w).1
  set D := (dbl d.Y.J).map (d.B.emb w).1
  set Wc := wM d.n ((ε : ℤ) : ℂ)
  have hPiP : Pi * P = 1 := by
    simp only [Pi, P]
    rw [← Matrix.map_mul, Units.inv_mul, Matrix.map_one _ (map_zero _) (map_one _)]
  have hQ := _root_.PositivityTheory.SiegelWeilFormula.Krd.hQ_w_k d R.hε w
  apply eps_of_unit d.ok.hn ε R.ε
  calc Wcᵀ * Krd.Qc d.n R.ε * Wc.map star
      = (Pi * P)ᵀ * Wcᵀ * (Pᵀ * D * P.map star) * Wc.map star * (Pi * P).map star := by
        rw [hPiP, hQ, Matrix.transpose_one, Krd.mapStar_one, Matrix.one_mul, Matrix.mul_one]
    _ = Pᵀ * ((P * Wc * Pi)ᵀ * D * (P * Wc * Pi).map star) * P.map star := by
        simp only [Matrix.transpose_mul, Krd.mapStar_mul, Matrix.mul_assoc]
    _ = Krd.Qc d.n R.ε := by rw [hc, hQ]
end RD
end PositivityTheory.SiegelWeilFormula
end
end
end

