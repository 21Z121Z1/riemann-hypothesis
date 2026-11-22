import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LagrangianDecomposition.Bundle0004
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.SplitStab
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.Bundle0001
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0036
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0063
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LagrangianDecomposition.Bundle0010
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilDatumProperties
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0028
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.ParabolicBlockForms.CosBijPf
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0035
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.LiftedSchrodingerDatum
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0029
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0034
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0046
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0060
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0059
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.AdelicDilations.COneLawPf
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0049
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.AdelicDilations.Bundle0003
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.VacuumIwasawa.EmEqInr
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKwhitIwa
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilAvacIwaC

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilAldHgt
section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
namespace PositivityTheory.SiegelWeilFormula.Ald
theorem hgtPull_k : _root_.PositivityTheory.SiegelWeilFormula.Ald.HgtPull_k := _root_.PositivityTheory.SiegelWeilFormula.Ldexb.hgtPull_k
end PositivityTheory.SiegelWeilFormula.Ald
end
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilAldSiegel
section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
namespace PositivityTheory.SiegelWeilFormula.Ald
variable {F : Type} [Field F] [NumberField F]
theorem siegelSmall_of_k (hF : SliceFacts) (hAC : AdaptedChar) : _root_.PositivityTheory.SiegelWeilFormula.Ald.SiegelSmall_k := by
  intro F E _ _ _ _ _ σ d n h Y b j ε hn hs hb e1 e2 hj dd0 dd' had0 had' om1 hsp1 hsr1 φ₀ hφ₀ h0 om' hbox
  intro l hl hinv p t hpt φ hφ
  have hψ : IsStd d.B.ψ := d.ok.good.std
  have hchar : ∀ (y : Fin d.m × Fin n × Fin 2 → AF F), ∀ φ ∈ schA F (Fin d.m × Fin n × Fin 2),
      l (fun x => d.B.ψ (x ⬝ᵥ y) * φ x) = l φ := by
    intro y φ hφ
    obtain ⟨z, hz⟩ := (hAC F E σ d.m n d.bs d.A Y b dd' had' hb).2 y
    have := hinv z φ hφ
    rw [Darboux.rho, hz, schr_zero_fst] at this
    exact this
  obtain ⟨c, hc⟩ := GlobalTheory.T.character_invariant_adelic_form_eq_mul_eval_zero F d.B.ψ hψ (Fin d.m × Fin n × Fin 2) l hl hchar
  have hbm : boxFun φ φ₀ ∈ schA F (K1 d.m n) := GlobalTheory.SchwartzBox.boxFun_mem_schA F _ _ φ hφ φ₀ hφ₀
  have hb1 := hbox p φ hφ
  have hm1 : boxFun (om' p φ) φ₀ ∈ schA F (K1 d.m n) := hb1 ▸ hsp1.pres (j p) _ hbm
  have hmem : om' p φ ∈ schA F (Fin d.m × Fin n × Fin 2) := by
    have := (hF F _ _).1 _ hm1
    rwa [slice0_box_one _ h0] at this
  rw [hc _ hmem, hc _ hφ]
  have hv : om' p φ 0 = ev0 (K1 d.m n) (om1 (j p) (boxFun φ φ₀)) := by
    rw [hb1]
    simp [ev0, boxFun, h0]
  obtain ⟨t', ht', hdet⟩ := _root_.PositivityTheory.SiegelWeilFormula.Ald.jPar_k d h hb hj p t hpt
  have hkill : ∀ (z : Matrix (Fin d.m) (Fin d.n) (AE F E)), ∀ Ψ ∈ schA F (K1 d.m n),
      ev0 (K1 d.m n) ((GlobalTheory.TowU.reindexD dd0 (eK d.m h).symm).rho d.B.ψ
        (z * (diagCols (Fin d.n) : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n) (AE F E))ᵀ) Ψ) = ev0 (K1 d.m n) Ψ := by
    intro z Ψ _
    have h1 := (hAC F E σ d.m d.n d.bs d.A d.Y d.b dd0 had0 d.ok.frame).1 z
    rw [Darboux.rho, GlobalTheory.TowU.reindexD_e, h1]
    simp [ev0, schr]
  have key := hsr1 (ev0 (K1 d.m n)) (evalZero_mem_adelicSchwartzAdmittedForms _) hkill (j p) t' ht' (boxFun φ φ₀) hbm
  rw [hv, key, hdet]
  simp [ev0, boxFun, h0]
  ring
end PositivityTheory.SiegelWeilFormula.Ald
end
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilAscfourbCos
section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix Classical ComplexOrder
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
open GlobalTheory.Doubling (absE)
set_option linter.unusedSimpArgs false
namespace PositivityTheory.SiegelWeilFormula.Act.C4
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
variable {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} (L : _root_.PositivityTheory.SiegelWeilFormula.LD_k d)
namespace Bq
theorem surj_k {γ : d.G} (hγ : γ ∈ rat2 σ d.Y) (hS : _root_.PositivityTheory.SiegelWeilFormula.Act.FirstOrbit L γ) :
    ∃ p ∈ par2 σ d.Y, p ∈ rat2 σ d.Y ∧ ∃ g ∈ rat2 σ L.Y, γ = p * L.j g := by
  have hσ := _root_.PositivityTheory.SiegelWeilFormula.kfour.sigma_sigma_of_good_k d.ok.good
  obtain ⟨⟨ε, hε⟩, -⟩ := d.ok.frame
  obtain ⟨⟨ε', hε'⟩, -⟩ := L.ok.frame
  have hee : ε = ε' := _root_.PositivityTheory.SiegelWeilFormula.Afc.eps_eq_k L hε hε'
  subst hee
  obtain ⟨G0, hG0⟩ := Afc.rat_frame (b := d.b) γ hγ
  obtain ⟨G0', hG0'⟩ := Afc.rat_frame (b := d.b) γ⁻¹ (inv_mem hγ)
  have hGG : G0' * G0 = 1 := kfour.incM_injective (F := F) (by
    rw [kfour.incM_mul', ← hG0, ← hG0', ← GlobalTheory.EisBL.DoubledParabolic.inFrame_mul, inv_mul_cancel, GlobalTheory.EisBL.DoubledParabolic.inFrame_one,
      Afc.incM_one'])
  have hS0 : ∀ i, G0 (Sum.inr i) (Sum.inl L.i₀) = 0 := fun i => by
    have h1 := hS i
    rw [hG0] at h1
    exact kfour.inclR_injective (F := F) (h1.trans (map_zero _).symm)
  set v : Fin d.n → E := fun k => G0 (Sum.inl k) (Sum.inl L.i₀) with hv_def
  have hv : v ≠ 0 := by
    intro h0
    have h1 := congrFun (congrFun hGG (Sum.inl L.i₀)) (Sum.inl L.i₀)
    have h2 : ∀ k, G0 (Sum.inl k) (Sum.inl L.i₀) = 0 := fun k => congrFun h0 k
    rw [Matrix.mul_apply, Fintype.sum_sum_type] at h1
    simp only [h2, hS0, mul_zero, Finset.sum_const_zero, add_zero, Matrix.one_apply_eq] at h1
    exact zero_ne_one h1
  obtain ⟨a, ha⟩ := exists_gl_col L.i₀ v hv
  obtain ⟨p1, hp1r, hp1⟩ := Afc.levi_ex hσ d.ok.frame a⁻¹
  have hp1P : p1 ∈ par2 σ d.Y :=
    (ComplexParameterFamilyContinuity.mem_stabiliser_iff_frame_lower_block d.ok.frame p1).2 (by rw [hp1, Matrix.toBlocks_fromBlocks₂₁])
  set P1 : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) E :=
    Matrix.fromBlocks (a⁻¹).1 0 0 ((((a⁻¹)⁻¹).1)ᵀ.map σ) with hP1_def
  have hP1 : inFrame d.b p1 = incM F P1 := by
    rw [hp1, hP1_def, Afc.incM_fromBlocks, show incM F (0 : Matrix (Fin d.n) (Fin d.n) E) = 0 from kfour.incM_zero]
  set M1 := P1 * G0 with hM1_def
  have hM1 : inFrame d.b (p1 * γ) = incM F M1 := by
    rw [GlobalTheory.EisBL.DoubledParabolic.inFrame_mul, hP1, hG0, hM1_def, kfour.incM_mul']
  have hγ1 : p1 * γ ∈ rat2 σ d.Y := mul_mem hp1r hγ
  have hx : ∀ r, M1 r (Sum.inl L.i₀) = (1 : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) E) r (Sum.inl L.i₀) := by
    intro r
    rw [hM1_def, Matrix.mul_apply, Fintype.sum_sum_type]
    rcases r with i | i
    · simp only [hP1_def, Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂, Matrix.zero_apply, zero_mul,
        Finset.sum_const_zero, add_zero]
      have e1 : ∀ j, G0 (Sum.inl j) (Sum.inl L.i₀) = a.1 j L.i₀ := fun j => (ha j).symm
      simp only [e1]
      rw [← Matrix.mul_apply, ← Units.val_mul, inv_mul_cancel, Units.val_one]
      simp [Matrix.one_apply]
    · simp [hP1_def, hS0, Matrix.one_apply]
  have hform := form_E hε (p1 * γ) hM1
  have hy := yrow_zero hform hx
  set H := M1.submatrix (_root_.PositivityTheory.SiegelWeilFormula.Act.C4.emS_k L) (_root_.PositivityTheory.SiegelWeilFormula.Act.C4.emS_k L) with hH_def
  have hH := _root_.PositivityTheory.SiegelWeilFormula.Act.C4.Bq.blockH_form_k L hform hx hy
  have hε1 : (((ε : ℤ) : E)) * (((ε : ℤ) : E)) = 1 := by
    rw [← Int.cast_mul, ← Units.val_mul, Int.units_mul_self, Units.val_one, Int.cast_one]
  have hεσ : (σ : E →+* E) (((ε : ℤ) : E)) = ((ε : ℤ) : E) := map_intCast _ _
  obtain ⟨hHH', hH'H⟩ := kunf.frame_inv_pf (σ : E →+* E) hσ (((ε : ℤ) : E)) hε1 hεσ H hH
  set H' := Matrix.fromBlocks ((H.toBlocks₂₂.map (σ : E →+* E))ᵀ) ((((ε : ℤ) : E)) • (H.toBlocks₁₂.map (σ : E →+* E))ᵀ)
      ((((ε : ℤ) : E)) • (H.toBlocks₂₁.map (σ : E →+* E))ᵀ) ((H.toBlocks₁₁.map (σ : E →+* E))ᵀ) with hH'_def
  have hIA : incM F H * incM F H' = 1 := by rw [← kfour.incM_mul', hHH', Afc.incM_one']
  have hformA : (incM F H)ᵀ * kunf.jw L.n (((ε : ℤ) : AE F E)) * (incM F H).map (cA σ) =
      kunf.jw L.n (((ε : ℤ) : AE F E)) := by
    have h1 := congrArg (incM F) hH
    rw [kfour.incM_mul', kfour.incM_mul', ← Afc.incM_transpose, ← Afc.incM_map_cA, ← QA_eq] at h1
    exact h1
  obtain ⟨h, hh⟩ := kunf.exists_of_frame (Y := L.Y) hε' (incM F H) (incM F H') hIA hformA
  have hhr : h ∈ rat2 σ L.Y := kunf.rat_of_inFrame hh
  have hh' : inFrame L.b h⁻¹ = incM F H' := by
    rw [GlobalTheory.EisBL.DoubledParabolic.inFrame_inv, hh]
    exact Matrix.inv_eq_right_inv hIA
  have hnF : inFrame d.b (p1 * γ * L.j h⁻¹) = incM F (M1 * _root_.PositivityTheory.SiegelWeilFormula.Act.C4.padE_k L H') := by
    rw [GlobalTheory.EisBL.DoubledParabolic.inFrame_mul, GlobalTheory.EisBL.DoubledParabolic.inFrame_mul, hP1, hG0, _root_.PositivityTheory.SiegelWeilFormula.Act.C4.inFrame_j_k, hh', _root_.PositivityTheory.SiegelWeilFormula.Act.C4.padM_incM_k, hM1_def,
      kfour.incM_mul', kfour.incM_mul']
  have hnq : NQ (Sum.inl L.i₀) (Sum.inr L.i₀) (inFrame d.b (p1 * γ * L.j h⁻¹)) := by
    rw [hnF]
    exact NQ.map _ (_root_.PositivityTheory.SiegelWeilFormula.Act.C4.Bq.nq_E_k L hx hy hHH')
  have hnP : p1 * γ * L.j h⁻¹ ∈ par2 σ d.Y := (ComplexParameterFamilyContinuity.mem_stabiliser_iff_frame_lower_block d.ok.frame _).2 hnq.projected_block_lower_sum
  have hnR : p1 * γ * L.j h⁻¹ ∈ rat2 σ d.Y := mul_mem hγ1 (_root_.PositivityTheory.SiegelWeilFormula.Act.C4.j_rat_k L (inv_mem hhr))
  refine ⟨p1⁻¹ * (p1 * γ * L.j h⁻¹), mul_mem (inv_mem hp1P) hnP, mul_mem (inv_mem hp1r) hnR, h, hhr, ?_⟩
  rw [map_inv]
  group
theorem rep_mk_k {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} (x : rat2 σ d.Y) :
    ∃ p ∈ par2 σ d.Y, p ∈ rat2 σ d.Y ∧ _root_.PositivityTheory.SiegelWeilFormula.Act.rep_k (GlobalTheory.AutomorphicL2Unitary.mk ((par2 σ d.Y).subgroupOf (rat2 σ d.Y)) x) = p * x := by
  obtain ⟨γ, hγ⟩ := GlobalTheory.AutomorphicL2Unitary.mk_eq_iff.1
    (Quotient.out_eq (GlobalTheory.AutomorphicL2Unitary.mk ((par2 σ d.Y).subgroupOf (rat2 σ d.Y)) x)).symm
  refine ⟨((γ : rat2 σ d.Y) : d.G), Subgroup.mem_subgroupOf.1 γ.2, (γ : rat2 σ d.Y).2, ?_⟩
  show (((Quotient.out (GlobalTheory.AutomorphicL2Unitary.mk ((par2 σ d.Y).subgroupOf (rat2 σ d.Y)) x)) : rat2 σ d.Y) : d.G) = _
  rw [← hγ]
  rfl
end Bq
theorem cos_bij_pf_k : ∃ e : _root_.PositivityTheory.SiegelWeilFormula.Act.Cs_k L.sd ≃ {q : _root_.PositivityTheory.SiegelWeilFormula.Act.Cs_k d // _root_.PositivityTheory.SiegelWeilFormula.Act.FirstOrbit L (_root_.PositivityTheory.SiegelWeilFormula.Act.rep_k q)}, ∀ q', ∃ p ∈ par2 σ d.Y, p ∈ rat2 σ d.Y ∧
    _root_.PositivityTheory.SiegelWeilFormula.Act.rep_k (e q').1 = p * L.j (_root_.PositivityTheory.SiegelWeilFormula.Act.rep_k q') := by
  set H := (par2 σ d.Y).subgroupOf (rat2 σ d.Y) with hH
  set H' := (par2 σ L.Y).subgroupOf (rat2 σ L.Y) with hH'
  let jr : rat2 σ L.Y → rat2 σ d.Y := fun γ => ⟨L.j γ, _root_.PositivityTheory.SiegelWeilFormula.Act.C4.j_rat_k L γ.2⟩
  let e0 : _root_.PositivityTheory.SiegelWeilFormula.Act.Cs_k L.sd → _root_.PositivityTheory.SiegelWeilFormula.Act.Cs_k d := Quotient.lift (fun γ => GlobalTheory.AutomorphicL2Unitary.mk H (jr γ)) (by
    intro a b hab
    have hab' : b * a⁻¹ ∈ H' := QuotientGroup.rightRel_apply.1 hab
    rw [GlobalTheory.AutomorphicL2Unitary.mk_eq_iff]
    refine ⟨⟨jr (b * a⁻¹), ?_⟩, ?_⟩
    · rw [hH', Subgroup.mem_subgroupOf] at hab'
      rw [hH, Subgroup.mem_subgroupOf]
      exact _root_.PositivityTheory.SiegelWeilFormula.Act.C4.j_par_k L hab'
    · apply Subtype.ext
      show L.j ((b : G2 σ L.Y) * (a : G2 σ L.Y)⁻¹) * L.j a = L.j b
      rw [map_mul, map_inv, inv_mul_cancel_right])
  have he0 : ∀ γ, e0 (GlobalTheory.AutomorphicL2Unitary.mk H' γ) = GlobalTheory.AutomorphicL2Unitary.mk H (jr γ) := fun γ => rfl
  have hS : ∀ q', _root_.PositivityTheory.SiegelWeilFormula.Act.FirstOrbit L (_root_.PositivityTheory.SiegelWeilFormula.Act.rep_k (e0 q')) := by
    intro q'
    induction q' using Quotient.inductionOn with
    | h γ =>
      obtain ⟨p, hp, -, hrep⟩ := _root_.PositivityTheory.SiegelWeilFormula.Act.C4.Bq.rep_mk_k (jr γ)
      have e1 : _root_.PositivityTheory.SiegelWeilFormula.Act.rep_k (e0 (GlobalTheory.AutomorphicL2Unitary.mk H' γ)) = p * L.j γ := by rw [he0]; exact hrep
      show _root_.PositivityTheory.SiegelWeilFormula.Act.FirstOrbit L (_root_.PositivityTheory.SiegelWeilFormula.Act.rep_k (e0 (GlobalTheory.AutomorphicL2Unitary.mk H' γ)))
      rw [e1]
      exact _root_.PositivityTheory.SiegelWeilFormula.Act.C4.Bq.inStabilizer_parabolic_mul L hp (_root_.PositivityTheory.SiegelWeilFormula.Act.C4.Bq.inStabilizer_smallerGroupEmbed L γ)
  let e : _root_.PositivityTheory.SiegelWeilFormula.Act.Cs_k L.sd → {q : _root_.PositivityTheory.SiegelWeilFormula.Act.Cs_k d // _root_.PositivityTheory.SiegelWeilFormula.Act.FirstOrbit L (_root_.PositivityTheory.SiegelWeilFormula.Act.rep_k q)} := fun q' => ⟨e0 q', hS q'⟩
  have hinj : Function.Injective e := by
    intro q1 q2 h12
    have h0 : e0 q1 = e0 q2 := congrArg Subtype.val h12
    induction q1 using Quotient.inductionOn with
    | h a =>
      induction q2 using Quotient.inductionOn with
      | h b =>
        change GlobalTheory.AutomorphicL2Unitary.mk H (jr a) = GlobalTheory.AutomorphicL2Unitary.mk H (jr b) at h0
        obtain ⟨γ, hγ⟩ := GlobalTheory.AutomorphicL2Unitary.mk_eq_iff.1 h0
        have hγv : ((γ : rat2 σ d.Y) : d.G) = L.j ((b : G2 σ L.Y) * (a : G2 σ L.Y)⁻¹) := by
          have := congrArg Subtype.val hγ
          simp only [Subgroup.coe_mul, jr] at this
          rw [map_mul, map_inv, ← this, mul_inv_cancel_right]
        have hP : (b : G2 σ L.Y) * (a : G2 σ L.Y)⁻¹ ∈ par2 σ L.Y := by
          apply _root_.PositivityTheory.SiegelWeilFormula.Act.C4.Bq.par_of_j_k L
          rw [← hγv]
          exact Subgroup.mem_subgroupOf.1 γ.2
        change GlobalTheory.AutomorphicL2Unitary.mk H' a = GlobalTheory.AutomorphicL2Unitary.mk H' b
        rw [GlobalTheory.AutomorphicL2Unitary.mk_eq_iff]
        refine ⟨⟨b * a⁻¹, Subgroup.mem_subgroupOf.2 hP⟩, ?_⟩
        simp
  have hsurj : Function.Surjective e := by
    rintro ⟨q, hq⟩
    obtain ⟨p, hpP, hpR, g, hg, hγ⟩ := _root_.PositivityTheory.SiegelWeilFormula.Act.C4.Bq.surj_k L (Quotient.out q).2 hq
    refine ⟨GlobalTheory.AutomorphicL2Unitary.mk H' ⟨g, hg⟩, Subtype.ext ?_⟩
    show GlobalTheory.AutomorphicL2Unitary.mk H (jr ⟨g, hg⟩) = q
    conv_rhs => rw [← Quotient.out_eq q]
    rw [GlobalTheory.AutomorphicL2Unitary.mk_eq_iff]
    refine ⟨⟨⟨p, hpR⟩, Subgroup.mem_subgroupOf.2 hpP⟩, Subtype.ext ?_⟩
    exact hγ.symm
  refine ⟨Equiv.ofBijective e ⟨hinj, hsurj⟩, fun q' => ?_⟩
  induction q' using Quotient.inductionOn with
  | h γ =>
    obtain ⟨p, hpP, hpR, hrep⟩ := _root_.PositivityTheory.SiegelWeilFormula.Act.C4.Bq.rep_mk_k (jr γ)
    obtain ⟨p', hp'P, hp'R, hrep'⟩ := _root_.PositivityTheory.SiegelWeilFormula.Act.C4.Bq.rep_mk_k (d := L.sd) γ
    refine ⟨p * L.j p'⁻¹, mul_mem hpP (_root_.PositivityTheory.SiegelWeilFormula.Act.C4.j_par_k L (inv_mem hp'P)), mul_mem hpR (_root_.PositivityTheory.SiegelWeilFormula.Act.C4.j_rat_k L (inv_mem hp'R)), ?_⟩
    show _root_.PositivityTheory.SiegelWeilFormula.Act.rep_k (e0 (GlobalTheory.AutomorphicL2Unitary.mk H' γ)) = _
    rw [he0, hrep, hrep', map_mul, map_inv]
    simp only [jr]
    group
end PositivityTheory.SiegelWeilFormula.Act.C4
end
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilAstepCLaw
section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix Classical ComplexOrder
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
open GlobalTheory.Doubling (absE)
namespace PositivityTheory.SiegelWeilFormula.AStep
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
theorem cOneLaw_pf_k (H : _root_.PositivityTheory.SiegelWeilFormula.AStep.Hyps_k) {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (L : _root_.PositivityTheory.SiegelWeilFormula.LD_k d) {Φ : d.Fn} (hΦ : Φ ∈ d.sch) (w : InfinitePlace F)
    {nb' lam' 𝓖'} (hc' : CoefData (σ := σ) (Y := L.Y) L.b nb' lam' 𝓖') (T' : nF σ L.Y L.b)
    (τ : ℝ) (y : GR d.n) (hy : IsDil (Pi.single L.i₀ 1) τ y) (z : ℂ) (x : d.G) :
    _root_.PositivityTheory.SiegelWeilFormula.AStep.cOne_k d L (d.sec0 Φ) (s0 d.m d.n) z nb' lam' 𝓖' T' (R.ι w y * x) =
      Complex.exp (τ * (2 * z + d.n)) * _root_.PositivityTheory.SiegelWeilFormula.AStep.cOne_k d L (d.sec0 Φ) (s0 d.m d.n) z nb' lam' 𝓖' T' x := by
  set c := Complex.exp (τ * (2 * z + d.n)) with hc
  have hterm : ∀ g : L.sd.G, ((d.Ht (L.j g * (R.ι w y * x)) : ℝ) : ℂ) ^ (z - s0 d.m d.n) * d.sec0 Φ (L.j g * (R.ι w y * x)) =
      c * (((d.Ht (L.j g * x) : ℝ) : ℂ) ^ (z - s0 d.m d.n) * d.sec0 Φ (L.j g * x)) := by
    intro g
    rw [← mul_assoc, _root_.PositivityTheory.SiegelWeilFormula.AStep.j_comm_dil_k R L w τ y hy g, mul_assoc]
    obtain ⟨ha, h0⟩ := _root_.PositivityTheory.SiegelWeilFormula.AStep.a_dil_k R w L.i₀ τ y hy (L.j g * x)
    rw [_root_.PositivityTheory.SiegelWeilFormula.AStep.constantTerm_dilation H R w L.i₀ τ y hy hΦ]
    have e1 : ((d.Ht (R.ι w y * (L.j g * x)) : ℝ) : ℂ) = ((Real.exp (2 * τ) : ℝ) : ℂ) * ((d.a (L.j g * x) : ℝ) : ℂ) := by
      unfold _root_.PositivityTheory.SiegelWeilFormula.SD_k.Ht
      rw [Real.coe_toNNReal _ (by rw [ha]; exact mul_nonneg (Real.exp_pos _).le h0), ha, Complex.ofReal_mul]
    have e2 : ((d.Ht (L.j g * x) : ℝ) : ℂ) = ((d.a (L.j g * x) : ℝ) : ℂ) := by
      unfold _root_.PositivityTheory.SiegelWeilFormula.SD_k.Ht
      rw [Real.coe_toNNReal _ h0]
    rw [e1, e2, Complex.mul_cpow_ofReal_nonneg (Real.exp_pos _).le h0, cpow_exp, hc]
    have e3 : Complex.exp (((2 * τ : ℝ) : ℂ) * (z - s0 d.m d.n)) * Complex.exp (τ * d.m) = Complex.exp (τ * (2 * z + d.n)) := by
      rw [← Complex.exp_add]
      congr 1
      unfold s0
      push_cast
      ring
    rw [← e3]
    ring
  unfold _root_.PositivityTheory.SiegelWeilFormula.AStep.cOne_k
  have hfun : (fun g : L.sd.G => ((d.Ht (L.j g * (R.ι w y * x)) : ℝ) : ℂ) ^ (z - s0 d.m d.n) * d.sec0 Φ (L.j g * (R.ι w y * x))) =
      fun g => c * (((d.Ht (L.j g * x) : ℝ) : ℂ) ^ (z - s0 d.m d.n) * d.sec0 Φ (L.j g * x)) := funext hterm
  rw [hfun]
  have hcs : ∀ (Ψ : L.sd.G → ℂ), GlobalTheory.Eis.cosetSum (par2 σ L.Y) (rat2 σ L.Y) (fun g => c * Ψ g) =
      fun g' => c * GlobalTheory.Eis.cosetSum (par2 σ L.Y) (rat2 σ L.Y) Ψ g' := by
    intro Ψ
    funext g'
    simp only [GlobalTheory.Eis.cosetSum, GlobalTheory.Eis.term]
    exact tsum_mul_left
  rw [hcs]
  simp only [fc, mul_assoc]
  exact integral_const_mul _ _
end PositivityTheory.SiegelWeilFormula.AStep
end
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilAstepHolW
section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix Classical ComplexOrder
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
namespace PositivityTheory.SiegelWeilFormula.AStep
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
theorem decW_pf_k {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (w : InfinitePlace F) (x : d.G) :
    ∃ (x' : d.G) (y : GR d.n), x = x' * R.ι w y ∧ ∀ y' : GR d.n, x' * R.ι w y' = R.ι w y' * x' := by
  obtain ⟨x', y, h, hx⟩ := _root_.PositivityTheory.SiegelWeilFormula.KSplitW.decompW_k d R w x
  exact ⟨x', y, h, _root_.PositivityTheory.SiegelWeilFormula.KSplitW.commW_k d R w x' hx⟩
end PositivityTheory.SiegelWeilFormula.AStep
end
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilAvacIwaE
section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
namespace PositivityTheory.SiegelWeilFormula.Avac
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
open GlobalTheory.Doubling (absE)
section Gen
variable {ι κ R : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] [Semiring R]
end Gen
def emEq_k {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} (L : _root_.PositivityTheory.SiegelWeilFormula.LD_k d) : Fin L.n ⊕ Unit ≃ Fin d.n :=
  Equiv.ofBijective (Sum.elim L.em fun _ => L.i₀) ⟨by
    rintro (a | a) (b | b) h
    · exact congrArg Sum.inl (L.inj h)
    · exact absurd h ((L.rng (L.em a)).2 ⟨a, rfl⟩)
    · exact absurd h.symm ((L.rng (L.em b)).2 ⟨b, rfl⟩)
    · rfl, fun i => by
    by_cases h : i = L.i₀
    · exact ⟨Sum.inr (), h.symm⟩
    · obtain ⟨a, ha⟩ := (L.rng i).1 h
      exact ⟨Sum.inl a, ha⟩⟩
theorem emEq_inl_k {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} (L : _root_.PositivityTheory.SiegelWeilFormula.LD_k d) (a : Fin L.n) : _root_.PositivityTheory.SiegelWeilFormula.Avac.emEq_k L (Sum.inl a) = L.em a := rfl
theorem emEq_inr_k {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} (L : _root_.PositivityTheory.SiegelWeilFormula.LD_k d) (u : Unit) : _root_.PositivityTheory.SiegelWeilFormula.Avac.emEq_k L (Sum.inr u) = L.i₀ := rfl
theorem det_emb_k {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} (L : _root_.PositivityTheory.SiegelWeilFormula.LD_k d) (N : Matrix (Fin d.n) (Fin d.n) (AE F E)) (N' : Matrix (Fin L.n) (Fin L.n) (AE F E))
    (h0 : ∀ k, N L.i₀ k = (1 : Matrix (Fin d.n) (Fin d.n) (AE F E)) L.i₀ k ∧
      N k L.i₀ = (1 : Matrix (Fin d.n) (Fin d.n) (AE F E)) k L.i₀)
    (h1 : N.submatrix L.em L.em = N') : N.det = N'.det := by
  rw [← Matrix.det_submatrix_equiv_self (_root_.PositivityTheory.SiegelWeilFormula.Avac.emEq_k L) N]
  have hne : ∀ a, L.em a ≠ L.i₀ := fun a => (L.rng (L.em a)).2 ⟨a, rfl⟩
  have : N.submatrix (_root_.PositivityTheory.SiegelWeilFormula.Avac.emEq_k L) (_root_.PositivityTheory.SiegelWeilFormula.Avac.emEq_k L) = Matrix.fromBlocks N' 0 0 1 := by
    ext (a | a) (b | b)
    · rw [Matrix.submatrix_apply, _root_.PositivityTheory.SiegelWeilFormula.Avac.emEq_inl_k, _root_.PositivityTheory.SiegelWeilFormula.Avac.emEq_inl_k, Matrix.fromBlocks_apply₁₁, ← h1, Matrix.submatrix_apply]
    · rw [Matrix.submatrix_apply, _root_.PositivityTheory.SiegelWeilFormula.Avac.emEq_inl_k, _root_.PositivityTheory.SiegelWeilFormula.Avac.emEq_inr_k, Matrix.fromBlocks_apply₁₂, (h0 (L.em a)).2,
        Matrix.one_apply_ne (hne a), Matrix.zero_apply]
    · rw [Matrix.submatrix_apply, _root_.PositivityTheory.SiegelWeilFormula.Avac.emEq_inl_k, _root_.PositivityTheory.SiegelWeilFormula.Avac.emEq_inr_k, Matrix.fromBlocks_apply₂₁, (h0 (L.em b)).1,
        Matrix.one_apply_ne (hne b).symm, Matrix.zero_apply]
    · rw [Matrix.submatrix_apply, _root_.PositivityTheory.SiegelWeilFormula.Avac.emEq_inr_k, Matrix.fromBlocks_apply₂₂, (h0 L.i₀).1, Matrix.one_apply_eq,
        Matrix.one_apply_eq]
  rw [this, Matrix.det_fromBlocks_zero₂₁, Matrix.det_one, mul_one]
theorem emm_inj_k {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} (L : _root_.PositivityTheory.SiegelWeilFormula.LD_k d) : Function.Injective (Sum.map L.em L.em) := Sum.map_injective.2 ⟨L.inj, L.inj⟩
theorem emm_rng_k {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} (L : _root_.PositivityTheory.SiegelWeilFormula.LD_k d) : ∀ c, c ∉ I0 L.i₀ ↔ c ∈ Set.range (Sum.map L.em L.em) := by
  rintro (c | c)
  · simp only [I0, Set.mem_insert_iff, Set.mem_singleton_iff, Sum.inl.injEq, reduceCtorEq, or_false]
    rw [show (¬c = L.i₀) ↔ c ∈ Set.range L.em from L.rng c]
    constructor
    · rintro ⟨a, rfl⟩; exact ⟨Sum.inl a, rfl⟩
    · rintro ⟨(a | a), h⟩
      · exact ⟨a, Sum.inl_injective h⟩
      · simp at h
  · simp only [I0, Set.mem_insert_iff, Set.mem_singleton_iff, Sum.inr.injEq, reduceCtorEq, false_or]
    rw [show (¬c = L.i₀) ↔ c ∈ Set.range L.em from L.rng c]
    constructor
    · rintro ⟨a, rfl⟩; exact ⟨Sum.inr a, rfl⟩
    · rintro ⟨(a | a), h⟩
      · simp at h
      · exact ⟨a, Sum.inr_injective h⟩
theorem idI_j_k {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} (L : _root_.PositivityTheory.SiegelWeilFormula.LD_k d) (g : L.sd.G) : IdI (I0 L.i₀) (inFrame d.b (L.j g)) := fun u hu v => L.j_out g u hu v
theorem j_K_k {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} (L : _root_.PositivityTheory.SiegelWeilFormula.LD_k d) {k : L.sd.G} (hk : k ∈ L.sd.K) : L.j k ∈ d.K := by
  have hL := (L.ok.stdK k).1 hk
  refine (d.ok.stdK (L.j k)).2 ⟨fun w => ?_, fun k'' hk'' i j => ?_⟩
  · have hI := (_root_.PositivityTheory.SiegelWeilFormula.Avac.idI_j_k L k).map (piInf (d.B.emb w))
    refine (hI.mul hI.ct).eq_one (_root_.PositivityTheory.SiegelWeilFormula.Avac.emm_inj_k L) (_root_.PositivityTheory.SiegelWeilFormula.Avac.emm_rng_k L) ?_
    rw [hI.sub_mul _ (_root_.PositivityTheory.SiegelWeilFormula.Avac.emm_inj_k L) (_root_.PositivityTheory.SiegelWeilFormula.Avac.emm_rng_k L), ← Matrix.conjTranspose_submatrix, Matrix.submatrix_map, L.j_in]
    exact hL.1 w
  · obtain ⟨k₀, hk₀, rfl⟩ : ∃ k₀ ∈ ({k, k⁻¹} : Set L.sd.G), k'' = L.j k₀ := by
      rcases hk'' with rfl | rfl
      · exact ⟨k, Or.inl rfl, rfl⟩
      · exact ⟨k⁻¹, Or.inr rfl, (map_inv L.j k).symm⟩
    by_cases hi : i ∈ I0 L.i₀
    · rw [(_root_.PositivityTheory.SiegelWeilFormula.Avac.idI_j_k L k₀ i hi j).1]; exact _root_.PositivityTheory.SiegelWeilFormula.KSplitW.finOne_one_mem_k d i j
    by_cases hj : j ∈ I0 L.i₀
    · rw [(_root_.PositivityTheory.SiegelWeilFormula.Avac.idI_j_k L k₀ j hj i).2]; exact _root_.PositivityTheory.SiegelWeilFormula.KSplitW.finOne_one_mem_k d i j
    obtain ⟨a, rfl⟩ := (_root_.PositivityTheory.SiegelWeilFormula.Avac.emm_rng_k L i).1 hi
    obtain ⟨b, rfl⟩ := (_root_.PositivityTheory.SiegelWeilFormula.Avac.emm_rng_k L j).1 hj
    have e := congrFun (congrFun (L.j_in k₀) a) b
    rw [Matrix.submatrix_apply] at e
    rw [e]
    exact hL.2 k₀ hk₀ a b
theorem a_j_k {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} (L : _root_.PositivityTheory.SiegelWeilFormula.LD_k d) (h : L.sd.G) : d.a (L.j h) = L.a h := by
  obtain ⟨p', t', hp', k', hk', rfl⟩ := L.ok.hgt.iwa h
  have h21L := _root_.PositivityTheory.SiegelWeilFormula.KWhit.parabolic_lowerLeft_block_zero L.sd p' t' hp'
  obtain ⟨t₂, hp₂, hdet₂⟩ := _root_.PositivityTheory.SiegelWeilFormula.Avac.isPar_of_frame_k L.sd p' h21L
  have hI := _root_.PositivityTheory.SiegelWeilFormula.Avac.idI_j_k L p'
  have h21 : (inFrame d.b (L.j p')).toBlocks₂₁ = 0 := by
    ext a b
    simp only [Matrix.toBlocks₂₁, Matrix.of_apply, Matrix.zero_apply]
    by_cases ha : Sum.inr a ∈ I0 L.i₀
    · rw [(hI _ ha _).1]; simp
    by_cases hb : Sum.inl b ∈ I0 L.i₀
    · rw [(hI _ hb _).2]; simp
    obtain ⟨a', ha'⟩ := (_root_.PositivityTheory.SiegelWeilFormula.Avac.emm_rng_k L _).1 ha
    obtain ⟨b', hb'⟩ := (_root_.PositivityTheory.SiegelWeilFormula.Avac.emm_rng_k L _).1 hb
    rcases a' with a' | a'
    · simp at ha'
    rcases b' with b' | b'
    · have e := congrFun (congrFun (L.j_in p') (Sum.inr a')) (Sum.inl b')
      simp only [Matrix.submatrix_apply] at e
      rw [← ha', ← hb', e]
      have := congrFun (congrFun h21L a') b'
      simpa [Matrix.toBlocks₂₁] using this
    · simp at hb'
  obtain ⟨t₁, hp₁, hdet₁⟩ := _root_.PositivityTheory.SiegelWeilFormula.Avac.isPar_of_frame_k d (L.j p') h21
  have hdet : Matrix.GeneralLinearGroup.det t₁ = Matrix.GeneralLinearGroup.det t₂ := by
    refine Units.ext ?_
    rw [hdet₁, hdet₂]
    refine _root_.PositivityTheory.SiegelWeilFormula.Avac.det_emb_k L _ _ (fun k => ⟨?_, ?_⟩) ?_
    · simp only [Matrix.toBlocks₁₁, Matrix.of_apply]
      rw [(hI _ (Or.inl rfl) _).1]; simp [Matrix.one_apply]
    · simp only [Matrix.toBlocks₁₁, Matrix.of_apply]
      rw [(hI _ (Or.inl rfl) _).2]; simp [Matrix.one_apply]
    · ext a b
      have e := congrFun (congrFun (L.j_in p') (Sum.inl a)) (Sum.inl b)
      simpa [Matrix.toBlocks₁₁] using e
  rw [map_mul, d.ok.hgt.val _ _ hp₁ _ (_root_.PositivityTheory.SiegelWeilFormula.Avac.j_K_k L hk'), L.ok.hgt.val _ _ hp₂ _ hk', hdet]
theorem q_ht'_k {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} (L : _root_.PositivityTheory.SiegelWeilFormula.LD_k d) {q : d.G} {lam : (AE F E)ˣ} (hq : IsQ F E L.i₀ (inFrame d.b q) lam) (h : L.sd.G) :
    d.a (q * L.j h) = (absE F E lam : ℝ) * L.a h := by
  obtain ⟨t, hp, hdet⟩ := _root_.PositivityTheory.SiegelWeilFormula.Avac.isPar_of_frame_k d q (isQ_21 hq)
  have e : Matrix.GeneralLinearGroup.det t = lam :=
    Units.ext (by rw [hdet, det_row (isQ_11 hq).1, (isQ_11 hq).2])
  rw [_root_.PositivityTheory.SiegelWeilFormula.Avac.a_mul_par_k d hp, e, _root_.PositivityTheory.SiegelWeilFormula.Avac.a_j_k L h]
end PositivityTheory.SiegelWeilFormula.Avac
end
end
end

