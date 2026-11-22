import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.VacuumIwasawa.Bundle0001
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.SplitStab
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.Bundle0001
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilDatumProperties
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0038
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.LiftedSchrodingerDatum
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.AwayActions.AwStep
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0030
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0040
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0029
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.PolynomialGaussianIntegrals.ContinuousLoc
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0039
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0028
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.FockSpaces.ProdGenMem

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilAvacKA
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
theorem crd_add_k (X Z : Mx F E d.m d.n) (k : Fin d.m × Fin d.n × Fin 2) : d.crd (X + Z) k = d.crd X k + d.crd Z k := by
  simp only [_root_.PositivityTheory.SiegelWeilFormula.SD_k.crd, Matrix.add_apply, map_add, Finsupp.coe_add, Pi.add_apply]
theorem crd_fin_k {Z : Mx F E d.m d.n} (hZ : finOne F • Z = 0) (k : Fin d.m × Fin d.n × Fin 2) : (d.crd Z k).2 = 0 := by
  have h := congrArg (fun M => d.crd M k) hZ
  simp only [_root_.PositivityTheory.SiegelWeilFormula.SD_k.crd, Matrix.smul_apply, map_smul, Finsupp.smul_apply, Matrix.zero_apply, map_zero, Finsupp.coe_zero,
    Pi.zero_apply, smul_eq_mul] at h
  have h2 := congrArg Prod.snd h
  have e : ∀ c : AF F, (finOne F * c).2 = c.2 := fun c => by
    show (1 : Af F) * c.2 = c.2
    exact one_mul _
  simp only [_root_.PositivityTheory.SiegelWeilFormula.SD_k.crd]
  rw [← e]
  exact h2
theorem loc_add_of_k (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (w : InfinitePlace F) {Z : Mx F E d.m d.n} (hZ : d.cw w Z = 0) (X : Mx F E d.m d.n) :
    R.loc w (X + Z) = R.loc w X := by
  have : d.cw w (X + Z) = d.cw w X := by
    simp only [_root_.PositivityTheory.SiegelWeilFormula.SD_k.cw] at hZ ⊢
    rw [Matrix.map_add _ (map_add _), hZ, add_zero]
  unfold _root_.PositivityTheory.SiegelWeilFormula.RD_k.loc
  rw [this]
def psiW_k (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (g : (Fin d.m × Fin d.n × Fin 2 → Af F) → ℂ) (w : InfinitePlace F) (X : Mx F E d.m d.n) : ℂ :=
  (∏ w' ∈ Finset.univ.erase w, fP 1 (R.loc w' X)) * g fun k => (d.crd X k).2
theorem vg_tens_k (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (g : (Fin d.m × Fin d.n × Fin 2 → Af F) → ℂ) (w : InfinitePlace F) :
    _root_.PositivityTheory.SiegelWeilFormula.Avac.vg_k R g = R.tens w (fP 1) (_root_.PositivityTheory.SiegelWeilFormula.Avac.psiW_k R g w) := by
  funext X
  simp only [_root_.PositivityTheory.SiegelWeilFormula.Avac.vg_k, _root_.PositivityTheory.SiegelWeilFormula.RD_k.tens, _root_.PositivityTheory.SiegelWeilFormula.Avac.psiW_k]
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ w)]
  ring
theorem psiW_indep_k (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (g : (Fin d.m × Fin d.n × Fin 2 → Af F) → ℂ) (w : InfinitePlace F) :
    ∀ X Z, (∀ w', w' ≠ w → d.cw w' Z = 0) → finOne F • Z = 0 → _root_.PositivityTheory.SiegelWeilFormula.Avac.psiW_k R g w (X + Z) = _root_.PositivityTheory.SiegelWeilFormula.Avac.psiW_k R g w X := by
  intro X Z h1 h2
  have e1 : (∏ w' ∈ Finset.univ.erase w, fP 1 (R.loc w' (X + Z))) = ∏ w' ∈ Finset.univ.erase w, fP 1 (R.loc w' X) :=
    Finset.prod_congr rfl fun w' hw' => by rw [_root_.PositivityTheory.SiegelWeilFormula.Avac.loc_add_of_k R w' (h1 w' (Finset.ne_of_mem_erase hw'))]
  have e2 : (fun k => (d.crd (X + Z) k).2) = fun k => (d.crd X k).2 := by
    funext k
    rw [_root_.PositivityTheory.SiegelWeilFormula.Avac.crd_add_k]
    show (d.crd X k).2 + (d.crd Z k).2 = (d.crd X k).2
    rw [_root_.PositivityTheory.SiegelWeilFormula.Avac.crd_fin_k h2, add_zero]
  unfold _root_.PositivityTheory.SiegelWeilFormula.Avac.psiW_k
  rw [e1, e2]
theorem gauss_indep_k (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) :
    ∀ X Z, (∀ w, d.cw w Z = 0) → (∏ w, fP 1 (R.loc w (X + Z))) = ∏ w, fP 1 (R.loc w X) := by
  intro X Z h
  exact Finset.prod_congr rfl fun w _ => by rw [_root_.PositivityTheory.SiegelWeilFormula.Avac.loc_add_of_k R w (h w)]
theorem fP_smul_one_k (c : ℂ) (u : Fin d.m → Fin d.n → ℂ) : fP (c • (1 : PX d.m d.n)) u = c * fP 1 u := by
  simp only [fP, evX, MvPolynomial.smul_eq_C_mul, mul_one, MvPolynomial.eval_C, map_one, one_mul]
theorem isSchwartz_fourierProjection_one : IsSw (fP (1 : PX d.m d.n)) := by
  obtain ⟨φ, hφ⟩ := KMain.schwartz_polyGauss (m := d.m) (n := d.n) (2 * Real.pi) (by positivity) 1
  exact ⟨φ, hφ⟩
end PositivityTheory.SiegelWeilFormula.Avac
end
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilAvacRes
section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
namespace PositivityTheory.SiegelWeilFormula.Avac
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
variable {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} (L : _root_.PositivityTheory.SiegelWeilFormula.LD_k d)
def ins_k (z : Fin d.m × Fin L.n × Fin 2 → Af F) : Fin d.m × Fin d.n × Fin 2 → Af F :=
  fun k => if h : ∃ j, L.em j = k.2.1 then z (k.1, h.choose, k.2.2) else 0
def ext_k (X' : Mx F E d.m L.n) : Mx F E d.m d.n := fun a i => if h : ∃ j, L.em j = i then X' a h.choose else 0
theorem choose_em_k (j : Fin L.n) (h : ∃ j', L.em j' = L.em j) : h.choose = j := L.inj h.choose_spec
theorem ext_sub_k (X : Mx F E d.m d.n) (hX : ∀ a, X a L.i₀ = 0) : _root_.PositivityTheory.SiegelWeilFormula.Avac.ext_k L (X.submatrix id L.em) = X := by
  funext a i
  by_cases h : ∃ j, L.em j = i
  · simp only [_root_.PositivityTheory.SiegelWeilFormula.Avac.ext_k, dif_pos h, Matrix.submatrix_apply, id, h.choose_spec]
  · have : i = L.i₀ := by
      by_contra hi
      exact h ((L.rng i).1 hi)
    simp only [_root_.PositivityTheory.SiegelWeilFormula.Avac.ext_k, dif_neg h]
    rw [this, hX]
theorem crd_ext_k (X' : Mx F E d.m L.n) (k : Fin d.m × Fin d.n × Fin 2) :
    (d.crd (_root_.PositivityTheory.SiegelWeilFormula.Avac.ext_k L X') k).2 = _root_.PositivityTheory.SiegelWeilFormula.Avac.ins_k L (fun k' => (L.sd.crd X' k').2) k := by
  by_cases h : ∃ j, L.em j = k.2.1
  · simp only [_root_.PositivityTheory.SiegelWeilFormula.SD_k.crd, _root_.PositivityTheory.SiegelWeilFormula.Avac.ext_k, _root_.PositivityTheory.SiegelWeilFormula.Avac.ins_k, dif_pos h]
  · simp only [_root_.PositivityTheory.SiegelWeilFormula.SD_k.crd, _root_.PositivityTheory.SiegelWeilFormula.Avac.ext_k, _root_.PositivityTheory.SiegelWeilFormula.Avac.ins_k, dif_neg h, map_zero, Finsupp.coe_zero, Pi.zero_apply]
    rfl
theorem continuous_ins_k : Continuous (_root_.PositivityTheory.SiegelWeilFormula.Avac.ins_k L (F := F)) := by
  refine continuous_pi fun k => ?_
  by_cases h : ∃ j, L.em j = k.2.1
  · simp only [_root_.PositivityTheory.SiegelWeilFormula.Avac.ins_k, dif_pos h]; exact continuous_apply _
  · simp only [_root_.PositivityTheory.SiegelWeilFormula.Avac.ins_k, dif_neg h]; exact continuous_const
def prj_k (z : Fin d.m × Fin d.n × Fin 2 → Af F) : Fin d.m × Fin L.n × Fin 2 → Af F := fun k => z (k.1, L.em k.2.1, k.2.2)
theorem prj_ins_k (z : Fin d.m × Fin L.n × Fin 2 → Af F) : _root_.PositivityTheory.SiegelWeilFormula.Avac.prj_k L (_root_.PositivityTheory.SiegelWeilFormula.Avac.ins_k L z) = z := by
  funext k
  have h : ∃ j, L.em j = L.em k.2.1 := ⟨_, rfl⟩
  simp only [_root_.PositivityTheory.SiegelWeilFormula.Avac.prj_k, _root_.PositivityTheory.SiegelWeilFormula.Avac.ins_k, dif_pos h, _root_.PositivityTheory.SiegelWeilFormula.Avac.choose_em_k L k.2.1 h]
theorem SB_ins_k {g : (Fin d.m × Fin d.n × Fin 2 → Af F) → ℂ} (hg : g ∈ SB (Fin d.m × Fin d.n × Fin 2 → Af F)) :
    (fun z => g (_root_.PositivityTheory.SiegelWeilFormula.Avac.ins_k L z)) ∈ SB (Fin d.m × Fin L.n × Fin 2 → Af F) := by
  refine ⟨hg.1.comp_continuous (_root_.PositivityTheory.SiegelWeilFormula.Avac.continuous_ins_k L), ?_⟩
  have hc : IsCompact (_root_.PositivityTheory.SiegelWeilFormula.Avac.prj_k L '' tsupport g) := hg.2.isCompact.image (continuous_pi fun k => continuous_apply _)
  refine hc.of_isClosed_subset (isClosed_tsupport _) ?_
  refine (tsupport_comp_subset_preimage g (_root_.PositivityTheory.SiegelWeilFormula.Avac.continuous_ins_k L)).trans fun z hz => ⟨_root_.PositivityTheory.SiegelWeilFormula.Avac.ins_k L z, hz, _root_.PositivityTheory.SiegelWeilFormula.Avac.prj_ins_k L z⟩
theorem sum_loc_k {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (w : InfinitePlace F) (X : Mx F E d.m d.n) :
    ∑ a, ∑ i, ‖R.loc w X a i‖ ^ 2 = ∑ i, ∑ a, ‖(((R.fr w)⁻¹).1 *ᵥ fun b => d.cw w X b i) a‖ ^ 2 := by
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun a _ => ?_
  simp only [_root_.PositivityTheory.SiegelWeilFormula.RD_k.loc, Matrix.map_apply, norm_star]
  rfl
theorem hζ'_k {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) : R.ζ = 1 ∨ R.ζ = Complex.I := by
  rcases R.hζ with h | h
  · exact Or.inl h.2
  · exact Or.inr h.2
theorem gauss_ext_k (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (R' : _root_.PositivityTheory.SiegelWeilFormula.RD_k L.sd) (w : InfinitePlace F) (X' : Mx F E d.m L.n) :
    fP 1 (R.loc w (_root_.PositivityTheory.SiegelWeilFormula.Avac.ext_k L X')) = fP 1 (R'.loc w X') := by
  suffices key : ∑ a, ∑ i, ‖R'.loc w X' a i‖ ^ 2 = ∑ a, ∑ i, ‖R.loc w (_root_.PositivityTheory.SiegelWeilFormula.Avac.ext_k L X') a i‖ ^ 2 by
    simp only [fP, gs, key, evX, map_one]
  rw [_root_.PositivityTheory.SiegelWeilFormula.Avac.sum_loc_k, _root_.PositivityTheory.SiegelWeilFormula.Avac.sum_loc_k]
  refine Fintype.sum_of_injective L.em L.inj _ _ (fun i hi => ?_) (fun j => ?_)
  · have h : ¬ ∃ j, L.em j = i := fun ⟨j, hj⟩ => hi ⟨j, hj⟩
    have : (fun b => d.cw w (_root_.PositivityTheory.SiegelWeilFormula.Avac.ext_k L X') b i) = 0 := by
      funext b
      simp only [_root_.PositivityTheory.SiegelWeilFormula.SD_k.cw, _root_.PositivityTheory.SiegelWeilFormula.Avac.ext_k, Matrix.map_apply, dif_neg h, map_zero, Pi.zero_apply]
    simp [this]
  · have h : ∃ j', L.em j' = L.em j := ⟨_, rfl⟩
    have e : (fun b => d.cw w (_root_.PositivityTheory.SiegelWeilFormula.Avac.ext_k L X') b (L.em j)) = fun b => L.sd.cw w X' b j := by
      funext b
      simp only [_root_.PositivityTheory.SiegelWeilFormula.SD_k.cw, _root_.PositivityTheory.SiegelWeilFormula.Avac.ext_k, Matrix.map_apply, dif_pos h, _root_.PositivityTheory.SiegelWeilFormula.Avac.choose_em_k L j h]
    rw [e]
    exact norm_frame_eq d.ok.hm (d.A.J.map (d.B.emb w).1) (R'.fr w) (R.fr w) R'.ζ R.ζ (R'.sg w) (R.sg w) (_root_.PositivityTheory.SiegelWeilFormula.Avac.hζ'_k R')
      (_root_.PositivityTheory.SiegelWeilFormula.Avac.hζ'_k R) (R'.hfr w) (R.hfr w) _
theorem res_vg_k (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (R' : _root_.PositivityTheory.SiegelWeilFormula.RD_k L.sd) (g : (Fin d.m × Fin d.n × Fin 2 → Af F) → ℂ) :
    (fun X' => _root_.PositivityTheory.SiegelWeilFormula.Avac.vg_k R g (_root_.PositivityTheory.SiegelWeilFormula.Avac.ext_k L X')) = _root_.PositivityTheory.SiegelWeilFormula.Avac.vg_k R' (fun z => g (_root_.PositivityTheory.SiegelWeilFormula.Avac.ins_k L z)) := by
  funext X'
  simp only [_root_.PositivityTheory.SiegelWeilFormula.Avac.vg_k]
  congr 1
  · exact Finset.prod_congr rfl fun w _ => _root_.PositivityTheory.SiegelWeilFormula.Avac.gauss_ext_k L R R' w X'
  · congr 1
    funext k
    exact _root_.PositivityTheory.SiegelWeilFormula.Avac.crd_ext_k L X' k
def resL_k : (Mx F E d.m d.n → ℂ) →ₗ[ℂ] (Mx F E d.m L.n → ℂ) := LinearMap.funLeft ℂ ℂ (_root_.PositivityTheory.SiegelWeilFormula.Avac.ext_k L)
theorem res_vac_k (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (R' : _root_.PositivityTheory.SiegelWeilFormula.RD_k L.sd) {f : Mx F E d.m d.n → ℂ} (hf : f ∈ R.vac) : _root_.PositivityTheory.SiegelWeilFormula.Avac.resL_k L f ∈ R'.vac := by
  have : R.vac ≤ R'.vac.comap (_root_.PositivityTheory.SiegelWeilFormula.Avac.resL_k L) := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨g, hg, rfl⟩
    show _root_.PositivityTheory.SiegelWeilFormula.Avac.resL_k L (_root_.PositivityTheory.SiegelWeilFormula.Avac.vg_k R g) ∈ R'.vac
    have e : _root_.PositivityTheory.SiegelWeilFormula.Avac.resL_k L (_root_.PositivityTheory.SiegelWeilFormula.Avac.vg_k R g) = _root_.PositivityTheory.SiegelWeilFormula.Avac.vg_k R' (fun z => g (_root_.PositivityTheory.SiegelWeilFormula.Avac.ins_k L z)) := _root_.PositivityTheory.SiegelWeilFormula.Avac.res_vg_k L R R' g
    rw [e]
    exact _root_.PositivityTheory.SiegelWeilFormula.Avac.vg_mem_k R' (_root_.PositivityTheory.SiegelWeilFormula.Avac.SB_ins_k L hg)
  exact this hf
theorem vac_res'_k (hT : _root_.PositivityTheory.SiegelWeilFormula.TAll_k) (hF : _root_.PositivityTheory.SiegelWeilFormula.FockMem_k) (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (R' : _root_.PositivityTheory.SiegelWeilFormula.RD_k L.sd) :
    ∀ Φ ∈ d.sch, d.T Φ ∈ R.vac → ∃ Φ', L.IsRes Φ Φ' ∧ L.sd.T Φ' ∈ R'.vac := by
  intro Φ hΦ hv
  have h1 : _root_.PositivityTheory.SiegelWeilFormula.Avac.resL_k L (d.T Φ) ∈ R'.vac := _root_.PositivityTheory.SiegelWeilFormula.Avac.res_vac_k L R R' hv
  have h2 : _root_.PositivityTheory.SiegelWeilFormula.Avac.resL_k L (d.T Φ) ∈ L.sd.schM := (hF F E σ L.sd R').1 (_root_.PositivityTheory.SiegelWeilFormula.Avac.vac_le_fock_k R' h1)
  obtain ⟨Φ', hΦ', e⟩ := (hT.1 F E σ L.sd).2.1 _ h2
  refine ⟨Φ', ⟨hΦ', fun X hX => ?_⟩, e ▸ h1⟩
  rw [e]
  show d.T Φ (_root_.PositivityTheory.SiegelWeilFormula.Avac.ext_k L (X.submatrix id L.em)) = d.T Φ X
  rw [_root_.PositivityTheory.SiegelWeilFormula.Avac.ext_sub_k L X hX]
end PositivityTheory.SiegelWeilFormula.Avac
end
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKawayAwStep
section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
open GlobalTheory.Doubling (absE)
namespace PositivityTheory.SiegelWeilFormula.KAway
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
variable (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ)
theorem cw_mul_k (w : InfinitePlace F) {p q r : Type} [Fintype q] (M : Matrix p q (AE F E)) (N : Matrix q r (AE F E)) :
    d.cw w (M * N) = d.cw w M * d.cw w N := by
  simp only [_root_.PositivityTheory.SiegelWeilFormula.SD_k.cw]
  exact Matrix.map_mul
theorem cw_one_k (w : InfinitePlace F) {p : Type} [DecidableEq p] : d.cw w (1 : Matrix p p (AE F E)) = 1 := by
  simp only [_root_.PositivityTheory.SiegelWeilFormula.SD_k.cw]
  exact Matrix.map_one _ (map_zero _) (map_one _)
theorem cw_transpose_k (w : InfinitePlace F) {p q : Type} (M : Matrix p q (AE F E)) : d.cw w Mᵀ = (d.cw w M)ᵀ := by
  simp only [_root_.PositivityTheory.SiegelWeilFormula.SD_k.cw, Matrix.transpose_map]
theorem cw_eW_self_k (w : InfinitePlace F) {p q : Type} (M : Matrix p q (AE F E)) : d.cw w (eW w • M) = d.cw w M := by
  ext i j
  simp [_root_.PositivityTheory.SiegelWeilFormula.SD_k.cw, piInf_eW]
theorem cw_eW_ne_k {w w' : InfinitePlace F} (h : w' ≠ w) {p q : Type} (M : Matrix p q (AE F E)) : d.cw w' (eW w • M) = 0 := by
  ext i j
  simp [_root_.PositivityTheory.SiegelWeilFormula.SD_k.cw, piInf_eW, h]
theorem eW_smul_eq_iff_k (w : InfinitePlace F) {p q : Type} (M M' : Matrix p q (AE F E)) :
    eW w • M = eW w • M' ↔ d.cw w M = d.cw w M' := by
  constructor
  · intro h
    rw [← _root_.PositivityTheory.SiegelWeilFormula.KAway.cw_eW_self_k d w M, h, _root_.PositivityTheory.SiegelWeilFormula.KAway.cw_eW_self_k]
  · intro h
    apply _root_.PositivityTheory.SiegelWeilFormula.Place.cw_ext_k d
    · intro w'
      by_cases hw : w' = w
      · subst hw
        rw [_root_.PositivityTheory.SiegelWeilFormula.KAway.cw_eW_self_k, _root_.PositivityTheory.SiegelWeilFormula.KAway.cw_eW_self_k, h]
      · rw [_root_.PositivityTheory.SiegelWeilFormula.KAway.cw_eW_ne_k d hw, _root_.PositivityTheory.SiegelWeilFormula.KAway.cw_eW_ne_k d hw]
    · rw [finOne_eW_smul, finOne_eW_smul]
theorem eW_smul_of_supp_k {w : InfinitePlace F} {p q : Type} {Z : Matrix p q (AE F E)}
    (hZ : ∀ w', w' ≠ w → d.cw w' Z = 0) (hf : finOne F • Z = 0) : eW w • Z = Z := by
  apply _root_.PositivityTheory.SiegelWeilFormula.Place.cw_ext_k d
  · intro w'
    by_cases hw : w' = w
    · subst hw
      rw [_root_.PositivityTheory.SiegelWeilFormula.KAway.cw_eW_self_k]
    · rw [_root_.PositivityTheory.SiegelWeilFormula.KAway.cw_eW_ne_k d hw, hZ w' hw]
  · rw [finOne_eW_smul, hf]
theorem gram_smul_right_k (a : AF F) (X Z : Mx F E d.m d.n) : d.gram X (a • Z) = a • d.gram X Z := by
  have : (a • Z).map (cA σ) = a • Z.map (cA σ) := by
    ext i j
    simp [map_smul]
  simp only [_root_.PositivityTheory.SiegelWeilFormula.SD_k.gram, this, Matrix.mul_smul]
theorem gram_smul_left_k (a : AF F) (X Z : Mx F E d.m d.n) : d.gram (a • X) Z = a • d.gram X Z := by
  simp only [_root_.PositivityTheory.SiegelWeilFormula.SD_k.gram, Matrix.transpose_smul, Matrix.smul_mul]
theorem gram_add_k (X Z : Mx F E d.m d.n) :
    d.gram (X + Z) (X + Z) = d.gram X X + (d.gram X Z + d.gram Z X + d.gram Z Z) := by
  simp only [_root_.PositivityTheory.SiegelWeilFormula.SD_k.gram, Matrix.transpose_add, Matrix.add_mul, Matrix.mul_add, Matrix.map_add _ (map_add _)]
  abel
theorem cw_eq_one_of_k (w : InfinitePlace F) {M : Mx F E d.n d.n} (h : eW w • M = eW w • (1 : Mx F E d.n d.n)) :
    d.cw w M = 1 := by
  rw [(_root_.PositivityTheory.SiegelWeilFormula.KAway.eW_smul_eq_iff_k d w M 1).1 h, _root_.PositivityTheory.SiegelWeilFormula.KAway.cw_one_k]
namespace Step
variable {d} (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (w : InfinitePlace F)
theorem stepN_k (hT : _root_.PositivityTheory.SiegelWeilFormula.TAll_k) (x : d.G) (β : Mx F E d.n d.n) (hx : inFrame d.b x = Matrix.fromBlocks 1 β 0 1)
    (hβ : eW w • β = 0) :
    R.StepOK w x id (fun Ψ X => d.B.ψ (-(⅟(2 : AF F) * d.tt (β * d.gram X X))) * Ψ X) := by
  have hP := hT.2.1 F E σ d
  refine ⟨fun f hf => hf, fun Ψ hΨ => ⟨?_, fun f hf Φ hΦ hTΦ => ?_⟩⟩
  · intro X Z hZ hf
    have hZe : eW w • Z = Z := _root_.PositivityTheory.SiegelWeilFormula.KAway.eW_smul_of_supp_k d hZ hf
    have h1 : d.gram X Z = eW w • d.gram X Z := by
      calc d.gram X Z = d.gram X (eW w • Z) := by rw [hZe]
        _ = _ := _root_.PositivityTheory.SiegelWeilFormula.KAway.gram_smul_right_k d _ X Z
    have h2 : d.gram Z X = eW w • d.gram Z X := by
      calc d.gram Z X = d.gram (eW w • Z) X := by rw [hZe]
        _ = _ := _root_.PositivityTheory.SiegelWeilFormula.KAway.gram_smul_left_k d _ Z X
    have h3 : d.gram Z Z = eW w • d.gram Z Z := by
      calc d.gram Z Z = d.gram (eW w • Z) Z := by rw [hZe]
        _ = _ := _root_.PositivityTheory.SiegelWeilFormula.KAway.gram_smul_left_k d _ Z Z
    have key : β * d.gram (X + Z) (X + Z) = β * d.gram X X := by
      rw [_root_.PositivityTheory.SiegelWeilFormula.KAway.gram_add_k, h1, h2, h3, ← smul_add, ← smul_add, Matrix.mul_add, Matrix.mul_smul, ← Matrix.smul_mul, hβ,
        Matrix.zero_mul, add_zero]
    simp only
    rw [key, hΨ X Z hZ hf]
  · funext X
    rw [(hP Φ hΦ).1 x β hx X, hTΦ]
    simp only [_root_.PositivityTheory.SiegelWeilFormula.RD_k.tens, id]
    ring
theorem stepM_k (hT : _root_.PositivityTheory.SiegelWeilFormula.TAll_k) (x : d.G) (a a' : GL (Fin d.n) (AE F E))
    (hx : inFrame d.b x = Matrix.fromBlocks a.1 0 0 a'.1) (ha : eW w • a'.1 = eW w • (1 : Mx F E d.n d.n)) :
    R.StepOK w x id (fun Ψ X => (d.χ (Matrix.GeneralLinearGroup.det a) : ℂ) *
      (((absE F E (Matrix.GeneralLinearGroup.det a) : ℝ) ^ ((d.m : ℝ) / 2) : ℝ) : ℂ) * Ψ (X * (a'⁻¹).1ᵀ)) := by
  have hP := hT.2.1 F E σ d
  have hc : d.cw w (a'⁻¹).1 = 1 := by
    have h1 : d.cw w a'.1 = 1 := _root_.PositivityTheory.SiegelWeilFormula.KAway.cw_eq_one_of_k d w ha
    have h2 : d.cw w ((a'⁻¹).1 * a'.1) = 1 := by
      rw [← Units.val_mul, inv_mul_cancel, Units.val_one, _root_.PositivityTheory.SiegelWeilFormula.KAway.cw_one_k]
    rwa [_root_.PositivityTheory.SiegelWeilFormula.KAway.cw_mul_k, h1, Matrix.mul_one] at h2
  refine ⟨fun f hf => hf, fun Ψ hΨ => ⟨?_, fun f hf Φ hΦ hTΦ => ?_⟩⟩
  · intro X Z hZ hf
    simp only
    rw [Matrix.add_mul, hΨ (X * (a'⁻¹).1ᵀ) (Z * (a'⁻¹).1ᵀ) (fun w' hw' => by rw [_root_.PositivityTheory.SiegelWeilFormula.KAway.cw_mul_k, hZ w' hw', Matrix.zero_mul])
      (by rw [← Matrix.smul_mul, hf, Matrix.zero_mul])]
  · funext X
    rw [(hP Φ hΦ).2.1 x a a' hx X, hTΦ]
    have hl : R.loc w (X * (a'⁻¹).1ᵀ) = R.loc w X := by
      unfold _root_.PositivityTheory.SiegelWeilFormula.RD_k.loc
      rw [_root_.PositivityTheory.SiegelWeilFormula.KAway.cw_mul_k, _root_.PositivityTheory.SiegelWeilFormula.KAway.cw_transpose_k, hc, Matrix.transpose_one, Matrix.mul_one]
    simp only [_root_.PositivityTheory.SiegelWeilFormula.RD_k.tens, id, hl]
    ring
end Step
end PositivityTheory.SiegelWeilFormula.KAway
end
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKfinpolybNuf
section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix SchwartzMap Classical InnerProductSpace
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl PositivityTheory.Rg.Sw
namespace PositivityTheory.SiegelWeilFormula.KFPB
open PositivityTheory.SiegelWeilFormula.KFP
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
variable {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ}
theorem continuous_loc_k (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (w : InfinitePlace F) : Continuous (fun X : Mx F E d.m d.n => R.loc w X) := by
  have h := _root_.PositivityTheory.SiegelWeilFormula.Place.continuous_cw_k d w (p := Fin d.m) (q := Fin d.n)
  unfold _root_.PositivityTheory.SiegelWeilFormula.RD_k.loc
  refine continuous_pi fun a => continuous_pi fun j => ?_
  simp only [Matrix.map_apply, Matrix.mul_apply]
  exact continuous_star.comp (continuous_finsetSum _ fun i _ =>
    continuous_const.mul ((continuous_apply j).comp ((continuous_apply i).comp h)))
theorem continuous_arc_k (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) : Continuous (_root_.PositivityTheory.SiegelWeilFormula.KFP.arc_k R) := by
  unfold _root_.PositivityTheory.SiegelWeilFormula.KFP.arc_k
  refine (EuclideanSpace.equiv (_root_.PositivityTheory.SiegelWeilFormula.KFP.Iw_k d) ℝ).symm.continuous.comp (continuous_pi fun i => ?_)
  have h : Continuous fun X : Mx F E d.m d.n => R.loc i.1 X i.2.1 i.2.2.1 :=
    (continuous_apply _).comp ((continuous_apply _).comp (_root_.PositivityTheory.SiegelWeilFormula.KFPB.continuous_loc_k R i.1))
  split_ifs
  · exact Complex.continuous_re.comp h
  · exact Complex.continuous_im.comp h
theorem continuous_fin_k : Continuous (_root_.PositivityTheory.SiegelWeilFormula.KFP.fin_k d) := by
  unfold _root_.PositivityTheory.SiegelWeilFormula.KFP.fin_k
  exact continuous_pi fun k => continuous_snd.comp ((continuous_apply k).comp (_root_.PositivityTheory.SiegelWeilFormula.KFock.continuous_crd_k d))
theorem continuous_zOf_k : Continuous (fun u : _root_.PositivityTheory.SiegelWeilFormula.KFP.Iw_k d → ℝ => _root_.PositivityTheory.SiegelWeilFormula.KFP.zOf_k u) := by
  refine continuous_pi fun w => continuous_pi fun a => continuous_pi fun j => ?_
  have : (fun u : _root_.PositivityTheory.SiegelWeilFormula.KFP.Iw_k d → ℝ => _root_.PositivityTheory.SiegelWeilFormula.KFP.zOf_k u w a j) =
      fun u => Complex.equivRealProdCLM.symm (u (w, a, j, true), u (w, a, j, false)) := by
    funext u
    rfl
  rw [this]
  exact Complex.equivRealProdCLM.symm.continuous.comp ((continuous_apply _).prodMk (continuous_apply _))
theorem zOf_add_k (u v : _root_.PositivityTheory.SiegelWeilFormula.KFP.Iw_k d → ℝ) : _root_.PositivityTheory.SiegelWeilFormula.KFP.zOf_k (u + v) = _root_.PositivityTheory.SiegelWeilFormula.KFP.zOf_k u + _root_.PositivityTheory.SiegelWeilFormula.KFP.zOf_k v := by
  funext w a j
  apply Complex.ext <;> simp [_root_.PositivityTheory.SiegelWeilFormula.KFP.zOf_k]
theorem jn_eq_cmb_k (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) :
    ∃ cF : _root_.PositivityTheory.SiegelWeilFormula.KFP.Vw_k d × _root_.PositivityTheory.SiegelWeilFormula.KFP.Yf_k d → (Fin d.m × Fin d.n × Fin 2 → AF F), Continuous cF ∧
      (∀ p q, cF (p + q) = cF p + cF q) ∧ ∀ p, _root_.PositivityTheory.SiegelWeilFormula.KFP.jn_k R p.1 p.2 = d.cmb (cF p) := by
  obtain ⟨L, hL⟩ := _root_.PositivityTheory.SiegelWeilFormula.KFock.archEquiv_k d R
  let cF : _root_.PositivityTheory.SiegelWeilFormula.KFP.Vw_k d × _root_.PositivityTheory.SiegelWeilFormula.KFP.Yf_k d → (Fin d.m × Fin d.n × Fin 2 → AF F) := fun p k =>
    (Prod.mk ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (L.symm (_root_.PositivityTheory.SiegelWeilFormula.KFP.zOf_k (EuclideanSpace.equiv (_root_.PositivityTheory.SiegelWeilFormula.KFP.Iw_k d) ℝ p.1)) k))
      (p.2 k) : AF F)
  refine ⟨cF, ?_, fun p q => ?_, fun p => ?_⟩
  · refine continuous_pi fun k => ?_
    have e : (fun p : _root_.PositivityTheory.SiegelWeilFormula.KFP.Vw_k d × _root_.PositivityTheory.SiegelWeilFormula.KFP.Yf_k d => cF p k) = fun p =>
        (Prod.mk ((GroundTheory.Global.homeomorphMixedSpace F).symm (L.symm (_root_.PositivityTheory.SiegelWeilFormula.KFP.zOf_k (EuclideanSpace.equiv (_root_.PositivityTheory.SiegelWeilFormula.KFP.Iw_k d) ℝ p.1)) k))
          (p.2 k) : AF F) := by
      funext p
      simp only [cF]
      rw [homeo_symm_eq]
    rw [e]
    exact Continuous.prodMk ((GroundTheory.Global.homeomorphMixedSpace F).symm.continuous.comp ((continuous_apply k).comp
      (L.symm.continuous.comp (_root_.PositivityTheory.SiegelWeilFormula.KFPB.continuous_zOf_k.comp ((EuclideanSpace.equiv (_root_.PositivityTheory.SiegelWeilFormula.KFP.Iw_k d) ℝ).continuous.comp continuous_fst)))))
      ((continuous_apply k).comp continuous_snd)
  · funext k
    refine Prod.ext ?_ ?_
    · show (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (L.symm (_root_.PositivityTheory.SiegelWeilFormula.KFP.zOf_k (EuclideanSpace.equiv (_root_.PositivityTheory.SiegelWeilFormula.KFP.Iw_k d) ℝ (p + q).1)) k) =
        (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (L.symm (_root_.PositivityTheory.SiegelWeilFormula.KFP.zOf_k (EuclideanSpace.equiv (_root_.PositivityTheory.SiegelWeilFormula.KFP.Iw_k d) ℝ p.1)) k) +
        (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (L.symm (_root_.PositivityTheory.SiegelWeilFormula.KFP.zOf_k (EuclideanSpace.equiv (_root_.PositivityTheory.SiegelWeilFormula.KFP.Iw_k d) ℝ q.1)) k)
      rw [← map_add, Prod.fst_add, map_add, _root_.PositivityTheory.SiegelWeilFormula.KFPB.zOf_add_k, map_add]
      rfl
    · rfl
  · refine (_root_.PositivityTheory.SiegelWeilFormula.KFP.exists_jn_k R p.1 p.2).unique ⟨_root_.PositivityTheory.SiegelWeilFormula.KFP.arc_jn_k R p.1 p.2, _root_.PositivityTheory.SiegelWeilFormula.KFP.fin_jn_k R p.1 p.2⟩ ⟨?_, ?_⟩
    · rw [_root_.PositivityTheory.SiegelWeilFormula.KFP.arc_eq_iff_k]
      intro w
      rw [← hL (cF p) w]
      have : (fun k => InfiniteAdeleRing.ringEquiv_mixedSpace F (cF p k).1) =
          L.symm (_root_.PositivityTheory.SiegelWeilFormula.KFP.zOf_k (EuclideanSpace.equiv (_root_.PositivityTheory.SiegelWeilFormula.KFP.Iw_k d) ℝ p.1)) := by
        funext k
        exact RingEquiv.apply_symm_apply _ _
      rw [this, ContinuousLinearEquiv.apply_symm_apply]
    · funext k
      show (d.crd (d.cmb (cF p)) k).2 = p.2 k
      rw [_root_.PositivityTheory.SiegelWeilFormula.KFock.crd_cmb'_k]
def jnpE_k (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) : _root_.PositivityTheory.SiegelWeilFormula.KFP.Vw_k d × _root_.PositivityTheory.SiegelWeilFormula.KFP.Yf_k d ≃ₜ+ Mx F E d.m d.n where
  toFun p := _root_.PositivityTheory.SiegelWeilFormula.KFP.jn_k R p.1 p.2
  invFun X := (_root_.PositivityTheory.SiegelWeilFormula.KFP.arc_k R X, _root_.PositivityTheory.SiegelWeilFormula.KFP.fin_k d X)
  left_inv p := Prod.ext (_root_.PositivityTheory.SiegelWeilFormula.KFP.arc_jn_k R p.1 p.2) (_root_.PositivityTheory.SiegelWeilFormula.KFP.fin_jn_k R p.1 p.2)
  right_inv X := _root_.PositivityTheory.SiegelWeilFormula.KFP.jn_arc_fin_k R X
  map_add' p q := by
    obtain ⟨cF, -, hadd, heq⟩ := _root_.PositivityTheory.SiegelWeilFormula.KFPB.jn_eq_cmb_k R
    show _root_.PositivityTheory.SiegelWeilFormula.KFP.jn_k R (p + q).1 (p + q).2 = _root_.PositivityTheory.SiegelWeilFormula.KFP.jn_k R p.1 p.2 + _root_.PositivityTheory.SiegelWeilFormula.KFP.jn_k R q.1 q.2
    rw [heq, heq, heq, hadd, _root_.PositivityTheory.SiegelWeilFormula.KFock.cmb_add_k]
  continuous_toFun := by
    obtain ⟨cF, hc, -, heq⟩ := _root_.PositivityTheory.SiegelWeilFormula.KFPB.jn_eq_cmb_k R
    have : (fun p : _root_.PositivityTheory.SiegelWeilFormula.KFP.Vw_k d × _root_.PositivityTheory.SiegelWeilFormula.KFP.Yf_k d => _root_.PositivityTheory.SiegelWeilFormula.KFP.jn_k R p.1 p.2) = fun p => d.cmb (cF p) := funext heq
    show Continuous fun p : _root_.PositivityTheory.SiegelWeilFormula.KFP.Vw_k d × _root_.PositivityTheory.SiegelWeilFormula.KFP.Yf_k d => _root_.PositivityTheory.SiegelWeilFormula.KFP.jn_k R p.1 p.2
    rw [this]
    exact (_root_.PositivityTheory.SiegelWeilFormula.KFock.continuous_cmb_k d).comp hc
  continuous_invFun := (_root_.PositivityTheory.SiegelWeilFormula.KFPB.continuous_arc_k R).prodMk _root_.PositivityTheory.SiegelWeilFormula.KFPB.continuous_fin_k
end PositivityTheory.SiegelWeilFormula.KFPB
end
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKfockMem
section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix SchwartzMap Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
namespace PositivityTheory.SiegelWeilFormula.KFock
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
theorem prodGen_mem_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (S : InfinitePlace F → 𝓢(Fin d.m → Fin d.n → ℂ, ℂ))
    (g : (Fin d.m × Fin d.n × Fin 2 → Af F) → ℂ) (hg : g ∈ SB (Fin d.m × Fin d.n × Fin 2 → Af F)) :
    (fun X => (∏ w, S w (R.loc w X)) * g fun k => (d.crd X k).2) ∈ d.schM := by
  obtain ⟨T, hT⟩ := piProdSch (InfinitePlace F) (Fin d.m → Fin d.n → ℂ) S
  obtain ⟨L, hL⟩ := _root_.PositivityTheory.SiegelWeilFormula.KFock.archEquiv_k d R
  rw [_root_.PositivityTheory.SiegelWeilFormula.SD_k.schM, Submodule.mem_comap]
  refine Submodule.subset_span ⟨SchwartzMap.compCLMOfContinuousLinearEquiv ℂ L T, g, hg, ?_⟩
  funext c
  simp only [LinearMap.funLeft_apply, pureA, SchwartzMap.compCLMOfContinuousLinearEquiv_apply, Function.comp, hT, hL,
    _root_.PositivityTheory.SiegelWeilFormula.KFock.crd_cmb_k]
theorem fock_le_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) : R.fock ≤ d.schM := by
  refine Submodule.span_le.mpr ?_
  rintro _ ⟨P, g, hg, rfl⟩
  have h := _root_.PositivityTheory.SiegelWeilFormula.KFock.prodGen_mem_k d R (fun w => (isSw_fP (P w)).choose) g hg
  have e : (fun X => (∏ w, fP (P w) (R.loc w X)) * g fun k => (d.crd X k).2) =
      fun X => (∏ w, (isSw_fP (P w)).choose (R.loc w X)) * g fun k => (d.crd X k).2 := by
    funext X
    congr 1
    exact Finset.prod_congr rfl fun w _ => by rw [(isSw_fP (P w)).choose_spec]
  change _ ∈ d.schM
  rw [e]
  exact h
theorem tens_mem_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (w : InfinitePlace F) (f : (Fin d.m → Fin d.n → ℂ) → ℂ) (hf : IsSw f)
    (Ψ : Mx F E d.m d.n → ℂ) (hΨ : Ψ ∈ R.away w) : R.tens w f Ψ ∈ d.schM := by
  obtain ⟨φ, hφ⟩ := hf
  have h : R.away w ≤ d.schM.comap (_root_.PositivityTheory.SiegelWeilFormula.KFock.tensL_k R w f) := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨P, g, hg, rfl⟩
    have h := _root_.PositivityTheory.SiegelWeilFormula.KFock.prodGen_mem_k d R (Function.update (fun w' => (isSw_fP (P w')).choose) w φ) g hg
    show R.tens w f _ ∈ d.schM
    convert h using 1
    funext X
    show f (R.loc w X) * ((∏ w' ∈ Finset.univ.erase w, fP (P w') (R.loc w' X)) * g fun k => (d.crd X k).2) =
      (∏ w', (Function.update (fun w' => (isSw_fP (P w')).choose) w φ w') (R.loc w' X)) * g fun k => (d.crd X k).2
    rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ w), Function.update_self, hφ, mul_assoc]
    congr 2
    refine Finset.prod_congr rfl fun w' hw' => ?_
    rw [Function.update_of_ne (Finset.ne_of_mem_erase hw'), (isSw_fP (P w')).choose_spec]
  exact h hΨ
end PositivityTheory.SiegelWeilFormula.KFock
end
end
end

