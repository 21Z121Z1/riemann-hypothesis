import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.UnfoldingCompactness.Bundle0005
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.SplitStab
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.Bundle0001
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0042
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0009
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.WhittakerCovolume.Bundle0005
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilDatumProperties
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0030
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0031
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKwhitIwa
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.WhittakerCovolume.Bundle0003
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.LiftedSchrodingerDatum
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.RationalHermitianMeasures.IncMScalarMul
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0029
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SchrodingerCommutation.Imports

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKunfCore
section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl
namespace PositivityTheory.SiegelWeilFormula.kunf
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ}
  {Y : Spc F E n} {b : GL (Fin n ⊕ Fin n) E}
theorem unfoldCore_k (B : Base F E) (hB : _root_.UpperTheory.TP.W.GoodK σ B) (hb : IsFrame2 σ Y b) {nb : nA σ Y b → G2 σ Y}
    {lam : Measure (nA σ Y b)} {𝓖 : Set (nA σ Y b)} (hc : CoefData (σ := σ) (Y := Y) b nb lam 𝓖)
    (φ : G2 σ Y → ℂ) (hφ : Continuous φ) (hrat : ∀ p ∈ par2 σ Y, p ∈ rat2 σ Y → ∀ y, φ (p * y) = φ y)
    (hone : ∀ p t, IsPar p t → Matrix.GeneralLinearGroup.det t = 1 → ∀ y, φ (p * y) = φ y)
    (hmaj : ∀ C : Set (G2 σ Y), IsCompact C → ∃ u : GlobalTheory.Eis.Cosets (par2 σ Y) (rat2 σ Y) → ℝ, Summable u ∧
      ∀ g ∈ C, ∀ q, ‖GlobalTheory.Eis.term (par2 σ Y) (rat2 σ Y) φ g q‖ ≤ u q)
    {ε : ℤˣ} {w : G2 σ Y} (hw : inFrame b w = Matrix.fromBlocks 0 1 (((ε : ℤ) : AE F E) • 1) 0) (x : G2 σ Y) :
    Integrable (fun β => φ (w * nb β * x)) lam ∧ ∀ T : nF σ Y b, IsND T →
      fc B.ψ b nb lam 𝓖 (GlobalTheory.Eis.cosetSum (par2 σ Y) (rat2 σ Y) φ) T x =
        ∫ β, φ (w * nb β * x) * B.ψ (-(Algebra.trace (AF F) (AE F E) (T.1.1 * β.1).trace)) ∂lam := by
  classical
  obtain ⟨hnb, hHaar, h𝓖, -⟩ := hc
  have := hHaar
  have : Countable (rat2 σ Y) := GlobalTheory.EisBL.DoubledGroupTopology.countable_rational_points_doubled σ Y
  have : Countable (GlobalTheory.Eis.Cosets (par2 σ Y) (rat2 σ Y)) := Quotient.countable
  obtain ⟨ε₀, hε₀⟩ := hb.1
  have hw_rat : w ∈ rat2 σ Y := by
    refine rat_of_inFrame (b := b) (M := Matrix.fromBlocks 0 1 (((ε : ℤ) : E) • 1) 0) ?_
    rw [hw]
    ext (i | i) (j | j) <;> simp [incM, Matrix.one_apply] <;> split_ifs <;> simp
  have hLI : GlobalTheory.AutomorphicL2Unitary.LeftInv (par2 σ Y ⊓ rat2 σ Y) φ := fun γ hγ g => hrat γ hγ.1 hγ.2 g
  let nbR : nF σ Y b → rat2 σ Y := fun ν => ⟨nb ν.1, nb_rat hnb ν.2⟩
  have nbR_zero : nbR 0 = 1 := Subtype.ext (nb_zero hnb)
  have nbR_add : ∀ ν ν', nbR (ν + ν') = nbR ν * nbR ν' := fun ν ν' => Subtype.ext (nb_add hnb ν.1 ν'.1)
  let act : GlobalTheory.Eis.Cosets (par2 σ Y) (rat2 σ Y) → nF σ Y b → GlobalTheory.Eis.Cosets (par2 σ Y) (rat2 σ Y) :=
    fun q ν => GlobalTheory.AutomorphicL2Unitary.rmul _ (nbR ν) q
  have hact0 : ∀ q, act q 0 = q := fun q => by
    show GlobalTheory.AutomorphicL2Unitary.rmul _ (nbR 0) q = q
    rw [nbR_zero, GlobalTheory.AutomorphicL2Unitary.rmul_one]
  have hact : ∀ q ν ν', act (act q ν) ν' = act q (ν + ν') := fun q ν ν' => by
    show GlobalTheory.AutomorphicL2Unitary.rmul _ (nbR ν') (GlobalTheory.AutomorphicL2Unitary.rmul _ (nbR ν) q) = GlobalTheory.AutomorphicL2Unitary.rmul _ (nbR (ν + ν')) q
    rw [nbR_add, GlobalTheory.AutomorphicL2Unitary.rmul_mul]
  let A : GlobalTheory.Eis.Cosets (par2 σ Y) (rat2 σ Y) → nA σ Y b → ℂ := fun q β =>
    GlobalTheory.Eis.term (par2 σ Y) (rat2 σ Y) φ (nb β * x) q
  have hA : ∀ q, Continuous (A q) := fun q =>
    hφ.comp (continuous_const.mul ((continuous_nb hnb).mul continuous_const))
  have hAmk : ∀ (γ : rat2 σ Y) β, A (GlobalTheory.AutomorphicL2Unitary.mk _ γ) β = φ (γ.1 * (nb β * x)) := fun γ β =>
    GlobalTheory.Eis.term_mk hLI (nb β * x) γ
  have hAact : ∀ q ν β, A (act q ν) β = A q (β + (ν : nA σ Y b)) := fun q ν β => by
    have e : act q ν = GlobalTheory.AutomorphicL2Unitary.mk _ (q.out * nbR ν) := by
      show GlobalTheory.AutomorphicL2Unitary.rmul _ (nbR ν) q = _
      conv_lhs => rw [← Quotient.out_eq q]
      rfl
    rw [e, hAmk]
    show φ ((q.out : rat2 σ Y).1 * nb ν.1 * (nb β * x)) = φ ((q.out : rat2 σ Y).1 * (nb (β + ν.1) * x))
    rw [nb_add hnb, nb_comm hnb β]
    simp only [mul_assoc]
  obtain ⟨C, hC, hcov⟩ := _root_.PositivityTheory.SiegelWeilFormula.kunf.exists_cover_k B hB hb
  obtain ⟨u, hu, hAu'⟩ := hmaj ((fun β => nb β * x) '' C) (hC.image ((continuous_nb hnb).mul continuous_const))
  have hAu : ∀ q, ∀ β ∈ C, ‖A q β‖ ≤ u q := fun q β hβ => hAu' _ ⟨β, hβ, rfl⟩ q
  let q₀ : GlobalTheory.Eis.Cosets (par2 σ Y) (rat2 σ Y) := GlobalTheory.AutomorphicL2Unitary.mk _ ⟨w, hw_rat⟩
  have hq₀ : ∀ ν, act q₀ ν = GlobalTheory.AutomorphicL2Unitary.mk _ (⟨w, hw_rat⟩ * nbR ν) := fun ν => rfl
  have hinj : Function.Injective (act q₀) := fun ν ν' h => by
    rw [hq₀, hq₀] at h
    obtain ⟨γ, hγ⟩ := GlobalTheory.AutomorphicL2Unitary.mk_eq_iff.1 h
    have hP : (w * nb ν'.1) * (w * nb ν.1)⁻¹ ∈ par2 σ Y := by
      have e : (w * nb ν'.1) = (γ : rat2 σ Y).1 * (w * nb ν.1) := (congrArg Subtype.val hγ).symm
      rw [e, mul_inv_cancel_right]
      exact Subgroup.mem_subgroupOf.1 γ.2
    exact (Subtype.ext (big_inj hb hw hnb hP)).symm
  have hAq₀ : ∀ β, A q₀ β = φ (w * nb β * x) := fun β => by
    rw [hAmk, mul_assoc]
  have hI := abs_integrable lam (nF σ Y b) 𝓖 h𝓖 act hact0 hact A hA hAact C hC hcov u hu hAu q₀ hinj
  refine ⟨hI.congr (Filter.Eventually.of_forall hAq₀), fun T hT => ?_⟩
  let χ₀ : nA σ Y b → ℂ := fun β => B.ψ (-(Algebra.trace (AF F) (AE F E) (T.1.1 * β.1).trace))
  have htr : Continuous fun M : Matrix (Fin n) (Fin n) (AE F E) => Algebra.trace (AF F) (AE F E) M.trace :=
    (IsModuleTopology.continuous_of_linearMap (Algebra.trace (AF F) (AE F E))).comp continuous_id.matrix_trace
  have hχc : Continuous χ₀ :=
    hB.std.1.comp ((htr.comp (continuous_const.matrix_mul continuous_subtype_val)).neg)
  have hχadd : ∀ β β', χ₀ (β + β') = χ₀ β * χ₀ β' := fun β β' => by
    simp only [χ₀, AddSubgroup.coe_add, Matrix.mul_add, Matrix.trace_add, map_add, neg_add]
    exact AddChar.map_add_eq_mul _ _ _
  have hχΛ : ∀ ν : nF σ Y b, χ₀ (ν : nA σ Y b) = 1 := fun ν => by
    simp only [χ₀, AddChar.map_neg_eq_inv, psi_rat hB.std T ν, inv_one]
  have hsmall : ∀ q, (∀ ν, act q₀ ν ≠ q) →
      ∃ β₀, χ₀ β₀ ≠ 1 ∧ ∀ ν β, A (act q ν) (β + β₀) = A (act q ν) β := fun q hq => by
    rcases _root_.PositivityTheory.SiegelWeilFormula.kunf.cells_k B hB hb hw hnb T hT (q.out : rat2 σ Y).1 (q.out : rat2 σ Y).2 with
      ⟨p, hpP, hpΓ, ν, hνF, hγ⟩ | ⟨β₀, hψ, t, hpar, hdet⟩
    · exfalso
      refine hq ⟨ν, hνF⟩ ?_
      rw [hq₀, ← Quotient.out_eq q]
      refine GlobalTheory.AutomorphicL2Unitary.mk_eq_iff.2 ⟨⟨⟨p, hpΓ⟩, Subgroup.mem_subgroupOf.2 hpP⟩, Subtype.ext ?_⟩
      exact hγ.symm
    · refine ⟨β₀, hψ, fun ν β => ?_⟩
      rw [hAact, hAact]
      show φ ((q.out : rat2 σ Y).1 * (nb (β + β₀ + ν.1) * x)) = φ ((q.out : rat2 σ Y).1 * (nb (β + ν.1) * x))
      set γ := (q.out : rat2 σ Y).1
      have e : γ * (nb (β + β₀ + ν.1) * x) = (γ * nb β₀ * γ⁻¹) * (γ * (nb (β + ν.1) * x)) := by
        rw [show β + β₀ + ν.1 = β₀ + (β + ν.1) by abel, nb_add hnb]
        group
      rw [e, hone _ t hpar hdet]
  obtain ⟨-, -, heq⟩ := abs_unfold lam (nF σ Y b) 𝓖 h𝓖 act hact0 hact A hA hAact χ₀ hχc hχadd hχΛ C hC hcov u hu hAu
    q₀ hinj hsmall
  show ∫ β in 𝓖, GlobalTheory.Eis.cosetSum (par2 σ Y) (rat2 σ Y) φ (nb β * x) * χ₀ β ∂lam = ∫ β, φ (w * nb β * x) * χ₀ β ∂lam
  have e2 : ∫ β, φ (w * nb β * x) * χ₀ β ∂lam = ∫ β, A q₀ β * χ₀ β ∂lam :=
    integral_congr_ae (Filter.Eventually.of_forall fun β => by simp only [hAq₀])
  rw [e2]
  exact heq
end PositivityTheory.SiegelWeilFormula.kunf
end
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKwhitDictAsm
section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
open GlobalTheory.Doubling (absE)
namespace PositivityTheory.SiegelWeilFormula.KWhit
open PositivityTheory.SiegelWeilFormula
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
theorem asm_gramR_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (η : E) (Y : Fin d.n → Fin d.m → AF F ⊗[F] E) :
    HeckeCharacterZeroLocus.SiegelWeilU.gramR (AF F) σ (_root_.PositivityTheory.SiegelWeilFormula.KWhit.Jd_k d η) Y =
      (HeckeCharacterZeroLocus.SiegelWeilU.inclR (F := F) (AF F) η) • (d.gram (toMx Y) (toMx Y))ᵀ := by
  ext c a
  simp only [HeckeCharacterZeroLocus.SiegelWeilU.gramR, HeckeCharacterZeroLocus.SiegelWeilU.hR, HeckeCharacterZeroLocus.SiegelWeilU.hform, HeckeCharacterZeroLocus.SiegelWeilU.JR, _root_.PositivityTheory.SiegelWeilFormula.KWhit.Jd_k,
    Matrix.map_apply, Matrix.transpose_apply, Matrix.smul_apply, smul_eq_mul, _root_.PositivityTheory.SiegelWeilFormula.SD_k.gram, Matrix.mul_apply, toMx,
    Matrix.of_apply, incM, map_mul, Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [asm_incl, asm_cA]
  ring
theorem asm_phase_cell_k {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} {R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d} {x : d.G} {t u : GL (Fin d.n) (AE F E)} {T : nF σ d.Y d.b} {η : E}
    {T₀ : Matrix (Fin d.n) (Fin d.n) E} {hOf : nA σ d.Y d.b → HeckeCharacterZeroLocus.SiegelWeilU.HermR (AF F) σ d.n}
    {θ : InfinitePlace F → (HeckeCharacterZeroLocus.SiegelWeilU.Ainf F ⊗[F] E →+* ℂ)} {fr : InfinitePlace F → GL (Fin d.m) ℂ}
    {g : InfinitePlace F → GL (Fin d.n) ℂ} (hr : _root_.PositivityTheory.SiegelWeilFormula.KWhit.Rel_k d R x t u T η T₀ hOf θ fr g) (β : nA σ d.Y d.b)
    (Y : Fin d.n → Fin d.m → AF F ⊗[F] E) :
    -(⅟(2 : AF F) * d.tt (β.1 * d.gram (toMx Y) (toMx Y))) =
      PositivityTheory.PfSWUS.Loc.trPair (AF F) ((hOf β).1) (HeckeCharacterZeroLocus.SiegelWeilU.gramR (AF F) σ (_root_.PositivityTheory.SiegelWeilFormula.KWhit.Jd_k d η) Y) := by
  rw [PositivityTheory.PfSWUS.Loc.trPair, _root_.PositivityTheory.SiegelWeilFormula.KWhit.asm_gramR_k, hr.hof β, _root_.PositivityTheory.SiegelWeilFormula.SD_k.tt, asm_half, Matrix.neg_mul, asm_scalar_mul,
    Matrix.smul_mul, Matrix.trace_neg, Matrix.trace_smul, smul_eq_mul, map_neg, mul_neg, neg_neg]
  congr 1
  congr 1
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.transpose_apply, Matrix.smul_apply, smul_eq_mul,
    Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun c _ => ?_
  ring
theorem asm_phase_whit_k {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} {R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d} {x : d.G} {t u : GL (Fin d.n) (AE F E)} {T : nF σ d.Y d.b} {η : E}
    {T₀ : Matrix (Fin d.n) (Fin d.n) E} {hOf : nA σ d.Y d.b → HeckeCharacterZeroLocus.SiegelWeilU.HermR (AF F) σ d.n}
    {θ : InfinitePlace F → (HeckeCharacterZeroLocus.SiegelWeilU.Ainf F ⊗[F] E →+* ℂ)} {fr : InfinitePlace F → GL (Fin d.m) ℂ}
    {g : InfinitePlace F → GL (Fin d.n) ℂ} (hr : _root_.PositivityTheory.SiegelWeilFormula.KWhit.Rel_k d R x t u T η T₀ hOf θ fr g) (β : nA σ d.Y d.b) :
    -d.tt (T.1.1 * β.1) =
      -PositivityTheory.PfSWUS.Loc.trPair (AF F) ((Td η T₀).map (HeckeCharacterZeroLocus.SiegelWeilU.inclR (AF F))) ((hOf β).1) := by
  rw [neg_inj, PositivityTheory.PfSWUS.Loc.trPair, hr.hof β, hr.rat, _root_.PositivityTheory.SiegelWeilFormula.SD_k.tt, asm_scalar_mul, Matrix.mul_neg, Matrix.mul_smul,
    Matrix.trace_neg, Matrix.trace_smul, smul_eq_mul, map_neg]
  have h2 : ∑ a, ∑ c, ((Td η T₀).map (HeckeCharacterZeroLocus.SiegelWeilU.inclR (F := F) (AF F))) a c * ((hOf β).1 : Mx F E d.n d.n) c a =
      algebraMap (AF F) (AE F E) (-2) * (HeckeCharacterZeroLocus.SiegelWeilU.inclR (F := F) (AF F) η *
        (incM F T₀ * ((hOf β).1 : Mx F E d.n d.n)ᵀ).trace) := by
    simp only [Td, Matrix.map_apply, Matrix.transpose_apply, Matrix.smul_apply, smul_eq_mul, map_mul, map_neg,
      map_ofNat, Matrix.trace, Matrix.diag, Matrix.mul_apply, incM, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun c _ => ?_
    rw [asm_incl]
    ring
  rw [h2, ← Algebra.smul_def (-2 : AF F) _, LinearMap.map_smul, smul_eq_mul, ← mul_assoc]
  have h5 : algebraMap F (AF F) (1 / 2) * (-2 : AF F) = -1 := by
    rw [show (-2 : AF F) = algebraMap F (AF F) (-2) by rw [map_neg, map_ofNat], ← map_mul]
    norm_num
  rw [h5]
  ring
theorem asm_c_ne_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (t : GL (Fin d.n) (AE F E)) :
    (d.χ (Matrix.GeneralLinearGroup.det t) : ℂ) *
      (((absE F E (Matrix.GeneralLinearGroup.det t) : ℝ) ^ ((d.m : ℝ) / 2) : ℝ) : ℂ) ≠ 0 := by
  have hpos : 0 < (absE F E (Matrix.GeneralLinearGroup.det t) : ℝ) := by
    have h : absE F E (Matrix.GeneralLinearGroup.det t) * absE F E (Matrix.GeneralLinearGroup.det t)⁻¹ = 1 := by
      rw [← map_mul, mul_inv_cancel, map_one]
    have h0 : absE F E (Matrix.GeneralLinearGroup.det t) ≠ 0 := left_ne_zero_of_mul_eq_one h
    exact_mod_cast pos_iff_ne_zero.2 h0
  exact mul_ne_zero (Circle.coe_ne_zero _) (Complex.ofReal_ne_zero.2 (Real.rpow_pos_of_pos hpos _).ne')
theorem dictAsmX_k : _root_.PositivityTheory.SiegelWeilFormula.KWhit.DictAsmX_k := by
  intro hCell hRel hH hM hTh hT hA F E _ _ _ _ _ σ d R Φ hΦ P gf hpg x hx nb lam 𝓖 hcd ε w hw T hTnd
  obtain ⟨t, u, hxtu⟩ := hx
  obtain ⟨η, T₀, hOf, θ, fr, g, l, εs, Φg, Φf, Φv, μ, ν, hr, hΦg, hani, hεs, hcm, hherm, hTT, hdet, hchr, hpl, hfr,
    hpure, hprod, hsdW, hsdH⟩ := hRel hT hA F E σ d R Φ hΦ P gf hpg x t u hxtu T hTnd
  obtain ⟨lv, L₁, L₂, C, hC, hlv, hco, hstd, hht⟩ := hH F E σ d R x t u T η T₀ hOf θ fr g hr nb lam 𝓖 hcd ε w hw
  obtain ⟨hMβ, hMZ⟩ := hM F E σ d R x t u T η T₀ hOf θ fr g hr
  obtain ⟨hembβ, hpresβ⟩ := hMβ nb lam 𝓖 hcd ν hsdH
  obtain ⟨νc, hνc⟩ := (hA F E σ d).1
  obtain ⟨hembZ, hpresZ⟩ := hMZ μ νc hsdW hνc
  obtain ⟨μH, 𝓕, hμH, h𝓕, horb⟩ := hTh F E σ d η hr.ne hr.herm
  set c : ℂ := (d.χ (Matrix.GeneralLinearGroup.det t) : ℂ) *
      (((absE F E (Matrix.GeneralLinearGroup.det t) : ℝ) ^ ((d.m : ℝ) / 2) : ℝ) : ℂ) with hc
  have hc0 : c ≠ 0 := _root_.PositivityTheory.SiegelWeilFormula.KWhit.asm_c_ne_k d t
  have hTx : ∀ Y, d.T (d.om x Φ) (toMx Y) = c * Φg Y := by
    intro Y
    rw [hΦg Y]
    exact (hT.2.1 F E σ d Φ hΦ.1).2.1 x t u hxtu (toMx Y)
  have hint : ∀ z : ℂ, ∀ β : nA σ d.Y d.b,
      flat d.a (d.sec0 Φ) (s0 d.m d.n) z (w * nb β * x) * d.B.ψ (-d.tt (T.1.1 * β.1)) =
        c * (C : ℂ) ^ (z - s0 d.m d.n) * Gen.whI (AF F) σ (_root_.PositivityTheory.SiegelWeilFormula.KWhit.Jd_k d η) d.B.ψ μ Φg (Gen.nuA θ g lv L₁ L₂)
          ((Td η T₀).map (HeckeCharacterZeroLocus.SiegelWeilU.inclR (AF F))) z (hOf β) := by
    intro z β
    obtain ⟨hνpos, ha⟩ := hht β
    have hcell := hCell hT F E σ d νc hνc ε w hw Φ hΦ.1 (nb β) x β.1 (hcd.1 β)
    have hZ : ∫ Z, d.B.ψ (-(⅟(2 : AF F) * d.tt (β.1 * d.gram Z Z))) * d.T (d.om x Φ) Z ∂νc =
        c * PositivityTheory.PfSWUS.Loc.jtR (AF F) σ (_root_.PositivityTheory.SiegelWeilFormula.KWhit.Jd_k d η) d.B.ψ μ Φg (hOf β) := by
      rw [← hpresZ.integral_comp hembZ]
      simp only [PositivityTheory.PfSWUS.Loc.jtR, hTx, _root_.PositivityTheory.SiegelWeilFormula.KWhit.asm_phase_cell_k hr β]
      rw [← integral_const_mul]
      congr 1
      funext Y
      ring
    have hs : s0 d.m d.n = ((d.m : ℂ) - d.n) / 2 := rfl
    simp only [flat]
    rw [hcell, hZ, ha, _root_.PositivityTheory.SiegelWeilFormula.KWhit.asm_phase_whit_k hr β, asm_cpow_split hC hνpos]
    simp only [Gen.whI, hs]
    ring
  refine ⟨2, _root_.PositivityTheory.SiegelWeilFormula.KWhit.Jd_k d η, Td η T₀, d.bs, d.B.ψ, θ, l, εs, fr, g, lv, L₁, L₂, Φg, Φf, Φv, μ, ν, c, C,
    ⟨hcm, hherm, hTT, hdet, hchr, hpl, hfr, hlv, hco, hstd, hpure, hprod, hsdW, hsdH⟩, hani, hεs, hC,
    ⟨0, fun z _ => ⟨fun hI => ?_, ?_⟩⟩, μH, 𝓕, hμH, h𝓕, ?_⟩
  · have hk : c * (C : ℂ) ^ (z - s0 d.m d.n) ≠ 0 :=
      mul_ne_zero hc0 (Complex.cpow_ne_zero_iff.2 (Or.inl (Complex.ofReal_ne_zero.2 hC.ne')))
    have h1 : Integrable (fun β => flat d.a (d.sec0 Φ) (s0 d.m d.n) z (w * nb β * x) *
        d.B.ψ (-d.tt (T.1.1 * β.1))) lam :=
      hI.mul_bdd (_root_.PositivityTheory.SiegelWeilFormula.KWhit.lin_psi_meas_k d T.1.1).aestronglyMeasurable
        (Eventually.of_forall fun β => (GlobalTheory.StdCharFromIsStd.norm_psi d.ok.good.std _).le)
    have h2 := h1.const_mul (c * (C : ℂ) ^ (z - s0 d.m d.n))⁻¹
    have hcomp : Integrable (fun β => Gen.whI (AF F) σ (_root_.PositivityTheory.SiegelWeilFormula.KWhit.Jd_k d η) d.B.ψ μ Φg (Gen.nuA θ g lv L₁ L₂)
        ((Td η T₀).map (HeckeCharacterZeroLocus.SiegelWeilU.inclR (AF F))) z (hOf β)) lam := by
      refine h2.congr (Eventually.of_forall fun β => ?_)
      simp only [hint z β]
      exact inv_mul_cancel_left₀ hk _
    exact (hpresβ.integrable_comp_emb hembβ).1 hcomp
  · simp_rw [hint z]
    rw [integral_const_mul, hpresβ.integral_comp hembβ]
  · rw [horb T T₀ hr.rat (d.om x Φ) (_root_.PositivityTheory.SiegelWeilFormula.KWhit.om_mem_sch_k d x hΦ.1)]
    have : (fun Y => d.T (d.om x Φ) (toMx Y)) = fun Y => c * Φg Y := funext hTx
    rw [this, asm_meanC_smul]
end PositivityTheory.SiegelWeilFormula.KWhit
end
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKwhitLinX
section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
namespace PositivityTheory.SiegelWeilFormula.KWhit
open PositivityTheory.SiegelWeilFormula
theorem linRedC_k : _root_.PositivityTheory.SiegelWeilFormula.KWhit.LinRedC_k := by
  intro hT hTC hLB hU hS c F E _ _ _ _ _ σ d hE k cs Φs hK x hW nb lam 𝓖 hcd ε w hw T hND
  have hTT : _root_.PositivityTheory.SiegelWeilFormula.TTheta_k := hT.2.2.2.1
  have hTA : _root_.PositivityTheory.SiegelWeilFormula.ThetaAuto_k := hT.2.2.2.2
  have hsch : ∀ i ∈ (Finset.univ : Finset (Fin k)), Φs i ∈ d.sch := fun i _ => (hK i).1
  have hsum := _root_.PositivityTheory.SiegelWeilFormula.KWhit.lin_sum_mem_k d Finset.univ cs Φs hsch
  have hIfun : d.I (∑ i, cs i • Φs i) = ∑ i, cs i • d.I (Φs i) := by
    funext y; rw [_root_.PositivityTheory.SiegelWeilFormula.KWhit.lin_I_sum_k d hTT hTA Finset.univ cs Φs hsch y]; simp [Finset.sum_apply]
  have horb : d.orb T (d.om x (∑ i, cs i • Φs i)) = ∑ i, cs i * d.orb T (d.om x (Φs i)) := by
    rw [← hTC F E σ d _ hsum nb lam 𝓖 hcd T x, hIfun,
      _root_.PositivityTheory.SiegelWeilFormula.KWhit.lin_fc_sum_k hLB d hcd T hND x Finset.univ cs (fun i => d.I (Φs i)) (fun i => ((hTA F E σ d).2.2 _ (hK i).1).2.1)
        (fun i => ((hTA F E σ d).2.2 _ (hK i).1).2.2)]
    exact Finset.sum_congr rfl fun i _ => by rw [hTC F E σ d _ (hK i).1 nb lam 𝓖 hcd T x]
  have horbc : c * d.orb T (d.om x (∑ i, cs i • Φs i)) = ∑ i, cs i * (c * d.orb T (d.om x (Φs i))) := by
    rw [horb, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  choose t ht using fun i => hU F E σ d (s0 d.m d.n) (d.sec0 (Φs i)) (hS F E σ d (Φs i) (hK i)) (hE (Φs i) (hK i))
  have hval := lin_holValueAt_sum Finset.univ cs
    (fun i z => ∫ β, flat d.a (d.sec0 (Φs i)) (s0 d.m d.n) z (w * nb β * x) * d.B.ψ (-d.tt (T.1.1 * β.1)) ∂lam)
    (fun i => c * d.orb T (d.om x (Φs i))) (s0 d.m d.n) (fun i _ => hW i nb lam 𝓖 hcd ε w hw T hND)
  rw [horbc]
  refine hval.congr ⟨∑ i, |t i|, fun z hz => ?_⟩
  have hzi : ∀ i, t i < z.re := fun i => lt_of_le_of_lt
    ((le_abs_self _).trans (Finset.single_le_sum (fun j _ => abs_nonneg (t j)) (Finset.mem_univ i))) hz
  have hint : ∀ i, Integrable (fun β => flat d.a (d.sec0 (Φs i)) (s0 d.m d.n) z (w * nb β * x) *
      d.B.ψ (-d.tt (T.1.1 * β.1))) lam := fun i =>
    ((ht i z (hzi i) nb lam 𝓖 hcd ε w hw x).1).mul_bdd (_root_.PositivityTheory.SiegelWeilFormula.KWhit.lin_psi_meas_k d T.1.1).aestronglyMeasurable
      (Eventually.of_forall fun β => (GlobalTheory.StdCharFromIsStd.norm_psi d.ok.good.std _).le)
  show ∑ i, cs i * ∫ β, flat d.a (d.sec0 (Φs i)) (s0 d.m d.n) z (w * nb β * x) * d.B.ψ (-d.tt (T.1.1 * β.1)) ∂lam =
    ∫ β, flat d.a (d.sec0 (∑ i, cs i • Φs i)) (s0 d.m d.n) z (w * nb β * x) * d.B.ψ (-d.tt (T.1.1 * β.1)) ∂lam
  refine (Finset.sum_congr rfl fun i _ => (integral_const_mul _ _).symm).trans ?_
  rw [← integral_finsetSum _ fun i _ => (hint i).const_mul (cs i)]
  congr 1
  funext β
  simp only [flat, _root_.PositivityTheory.SiegelWeilFormula.KWhit.constantTerm_finsetSum, Finset.mul_sum, Finset.sum_mul]
  exact Finset.sum_congr rfl fun i _ => by ring
end PositivityTheory.SiegelWeilFormula.KWhit
end
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKwhitVac
section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
namespace PositivityTheory.SiegelWeilFormula.KWhit
open PositivityTheory.SiegelWeilFormula
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
def vac_gen_k {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) : Set (Mx F E d.m d.n → ℂ) :=
  {f | ∃ φ, Dense.Good φ ∧ f = _root_.PositivityTheory.SiegelWeilFormula.KWhit.genF_k R (fun _ => 1) (Dense.pf φ)}
theorem vac_gen_sub_k {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) : _root_.PositivityTheory.SiegelWeilFormula.KWhit.vac_gen_k R ⊆ R.vac := by
  rintro _ ⟨φ, hφ, rfl⟩
  exact Submodule.subset_span ⟨Dense.pf φ, Dense.pf_mem hφ, rfl⟩
theorem vac_le_span_k {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) : R.vac ≤ Submodule.span ℂ (_root_.PositivityTheory.SiegelWeilFormula.KWhit.vac_gen_k R) := by
  refine Submodule.span_le.2 ?_
  rintro _ ⟨g, hg, rfl⟩
  have := Dense.mem_span_pf hg
  clear hg
  have key : _root_.PositivityTheory.SiegelWeilFormula.KWhit.genL_k R (fun _ => 1) g ∈ Submodule.span ℂ (_root_.PositivityTheory.SiegelWeilFormula.KWhit.vac_gen_k R) := by
    induction this using Submodule.span_induction with
    | mem x hx => obtain ⟨φ, hφ, rfl⟩ := hx; exact Submodule.subset_span ⟨φ, hφ, rfl⟩
    | zero => rw [map_zero]; exact zero_mem _
    | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
    | smul a x _ hx => rw [map_smul]; exact Submodule.smul_mem _ _ hx
  exact key
theorem vac_isPureBy_k {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d)
    (φ : ∀ u : HeightOneSpectrum (𝓞 F), (Fin d.m × Fin d.n × Fin 2 → Fv F u) → ℂ) (hφ : Dense.Good φ) (Φ : d.Fn)
    (h : d.T Φ = _root_.PositivityTheory.SiegelWeilFormula.KWhit.genF_k R (fun _ => 1) (Dense.pf φ)) : ∃ gf, _root_.PositivityTheory.SiegelWeilFormula.KWhit.IsPureBy_k R Φ (fun _ => 1) gf := by
  refine ⟨φ, fun v => hφ.1 v, hφ.2.mono fun v hv => hv, ?_⟩
  rw [h]
  rfl
theorem vacSpan_k : _root_.PositivityTheory.SiegelWeilFormula.KWhit.VacSpan_k := by
  intro hT hF hPK hVK F E _ _ _ _ _ σ d R Φ hΦ hTΦ
  have hB := hT.1 F E σ d
  have hvf : R.vac ≤ R.fock := (hVK F E σ d R).2.1
  have h1 : d.T Φ ∈ Submodule.span ℂ (_root_.PositivityTheory.SiegelWeilFormula.KWhit.vac_gen_k R) := _root_.PositivityTheory.SiegelWeilFormula.KWhit.vac_le_span_k R hTΦ
  obtain ⟨k, c, gs, hsum⟩ := Submodule.mem_span_set'.1 h1
  have hpre : ∀ i : Fin k, ∃ Ψ ∈ d.sch, d.T Ψ = (gs i : Mx F E d.m d.n → ℂ) := fun i =>
    hB.2.1 _ ((hF F E σ d R).1 (hvf (_root_.PositivityTheory.SiegelWeilFormula.KWhit.vac_gen_sub_k R (gs i).2)))
  choose Φs hΦs hTs using hpre
  refine ⟨k, c, Φs, fun i => ⟨hPK F E σ d R (Φs i) (hΦs i) (hTs i ▸ hvf (_root_.PositivityTheory.SiegelWeilFormula.KWhit.vac_gen_sub_k R (gs i).2)),
    hTs i ▸ _root_.PositivityTheory.SiegelWeilFormula.KWhit.vac_gen_sub_k R (gs i).2, ?_⟩, ?_⟩
  · obtain ⟨φ, hφ, e⟩ := (gs i).2
    exact _root_.PositivityTheory.SiegelWeilFormula.KWhit.vac_isPureBy_k R φ hφ (Φs i) ((hTs i).trans e)
  · have hmem : Φ - ∑ i, c i • Φs i ∈ d.sch :=
      sub_mem hΦ (Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (hΦs i))
    have h0 : d.T (Φ - ∑ i, c i • Φs i) = 0 := by
      rw [_root_.PositivityTheory.SiegelWeilFormula.KWhit.T_sub_k, _root_.PositivityTheory.SiegelWeilFormula.KWhit.T_sum_k, ← hsum]
      simp only [hTs, sub_self]
    exact (sub_eq_zero.1 (hB.2.2 _ hmem h0))
end PositivityTheory.SiegelWeilFormula.KWhit
end
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilMeasdictHOf
section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw SiegelEisensteinSeries.Grp
namespace PositivityTheory.SiegelWeilFormula.MeasD
open PositivityTheory.SiegelWeilFormula PositivityTheory.SiegelWeilFormula.KWhit PositivityTheory.SiegelWeilFormula.kfour
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
section HOf
variable {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} {η : E} (hOf : nA σ d.Y d.b → HeckeCharacterZeroLocus.SiegelWeilU.HermR (AF F) σ d.n)
theorem hOf_val_k (hne : η ≠ 0)
    (hof : ∀ β, β.1 = -(incM F (Matrix.scalar (Fin d.n) η) * ((hOf β).1 : Mx F E d.n d.n)ᵀ)) (β : nA σ d.Y d.b) :
    ((hOf β).1 : Mx F E d.n d.n) = -(inclR (F := F) (AF F) η⁻¹ • (β.1)ᵀ) := by
  ext a b
  have h := congrFun (congrFun (hof β) b) a
  rw [incM_scalar_mul] at h
  simp only [Matrix.neg_apply, Matrix.smul_apply, Matrix.transpose_apply, smul_eq_mul] at h ⊢
  linear_combination inclR (F := F) (AF F) η⁻¹ * h - ((hOf β).1 a b) * inclR_inv_mul (F := F) hne
theorem inv_mem_k (herm : ∀ i j, σ (η * d.A.J j i) = η * d.A.J i j) (S : HeckeCharacterZeroLocus.SiegelWeilU.HermR (AF F) σ d.n) :
    (-(inclR (F := F) (AF F) η • (S.1 : Mx F E d.n d.n)ᵀ)) ∈ nA σ d.Y d.b := by
  have hσ := _root_.PositivityTheory.SiegelWeilFormula.kfour.sigma_sigma_of_good_k d.ok.good
  obtain ⟨⟨ε, hb⟩, -⟩ := d.ok.frame
  have hrel := _root_.PositivityTheory.SiegelWeilFormula.MeasD.eta_sign_k d herm hb
  rw [mem_nA_iff hσ hb]
  have hS : ∀ a b, HeckeCharacterZeroLocus.SiegelWeilU.sigR (AF F) σ (S.1 b a) = S.1 a b := S.2
  have h1 : ∀ a b, cA σ (S.1 b a) = S.1 a b := fun a b => by rw [← sigR_eq]; exact hS a b
  have h2 : cA σ (inclR (F := F) (AF F) η) = -(((ε : ℤ) : AE F E)) * inclR (F := F) (AF F) η := by
    rw [cA_inclR', hrel, map_mul, map_neg, inclR_int]
  show (-(inclR (F := F) (AF F) η • (S.1 : Mx F E d.n d.n)ᵀ))ᵀ =
    -((((ε : ℤ) : AE F E)) • (-(inclR (F := F) (AF F) η • (S.1 : Mx F E d.n d.n)ᵀ)).map (cA σ))
  ext a b
  simp only [Matrix.transpose_apply, Matrix.neg_apply, Matrix.smul_apply, Matrix.map_apply, smul_eq_mul, map_neg, map_mul,
    h1, h2]
  linear_combination (inclR (F := F) (AF F) η * S.1 a b) * eps_sq (F := F) (E := E) ε
def hEq_k (hne : η ≠ 0)
    (hof : ∀ β, β.1 = -(incM F (Matrix.scalar (Fin d.n) η) * ((hOf β).1 : Mx F E d.n d.n)ᵀ))
    (herm : ∀ i j, σ (η * d.A.J j i) = η * d.A.J i j) :
    nA σ d.Y d.b ≃ₜ+ HeckeCharacterZeroLocus.SiegelWeilU.HermR (AF F) σ d.n where
  toFun := hOf
  invFun S := ⟨-(inclR (F := F) (AF F) η • (S.1 : Mx F E d.n d.n)ᵀ), _root_.PositivityTheory.SiegelWeilFormula.MeasD.inv_mem_k herm S⟩
  left_inv β := by
    apply Subtype.ext
    show -(inclR (F := F) (AF F) η • ((hOf β).1 : Mx F E d.n d.n)ᵀ) = β.1
    rw [hof β, incM_scalar_mul]
  right_inv S := by
    apply Subtype.ext
    rw [_root_.PositivityTheory.SiegelWeilFormula.MeasD.hOf_val_k hOf hne hof]
    ext a b
    simp only [Matrix.transpose_apply, Matrix.neg_apply, Matrix.smul_apply, smul_eq_mul]
    linear_combination (S.1 a b) * inclR_inv_mul (F := F) hne
  map_add' β γ := by
    apply Subtype.ext
    show ((hOf (β + γ)).1 : Mx F E d.n d.n) = (hOf β).1 + (hOf γ).1
    rw [_root_.PositivityTheory.SiegelWeilFormula.MeasD.hOf_val_k hOf hne hof, _root_.PositivityTheory.SiegelWeilFormula.MeasD.hOf_val_k hOf hne hof, _root_.PositivityTheory.SiegelWeilFormula.MeasD.hOf_val_k hOf hne hof]
    ext a b
    simp only [AddSubgroup.coe_add, Matrix.transpose_apply, Matrix.neg_apply, Matrix.smul_apply, Matrix.add_apply,
      smul_eq_mul]
    ring
  continuous_toFun := by
    apply continuous_induced_rng.2
    have hc : Continuous fun β : nA σ d.Y d.b => -(inclR (F := F) (AF F) η⁻¹ • (β.1 : Mx F E d.n d.n)ᵀ) :=
      (Continuous.fun_const_smul (continuous_subtype_val.matrix_transpose) _).fun_neg
    exact hc.congr fun β => (_root_.PositivityTheory.SiegelWeilFormula.MeasD.hOf_val_k hOf hne hof β).symm
  continuous_invFun := by
    apply continuous_induced_rng.2
    show Continuous fun S : HeckeCharacterZeroLocus.SiegelWeilU.HermR (AF F) σ d.n => -(inclR (F := F) (AF F) η • (S.1 : Mx F E d.n d.n)ᵀ)
    exact (Continuous.fun_const_smul (continuous_subtype_val.matrix_transpose) _).fun_neg
end HOf
end PositivityTheory.SiegelWeilFormula.MeasD
end
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilTweylBase
section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl PositivityTheory.Rg.Sw
namespace PositivityTheory.SiegelWeilFormula.tweyl
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
variable (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ)
theorem std_k : IsStd d.B.ψ := d.ok.good.std
include d in
theorem cm_k : IsCMExt F E σ := d.ok.good.1
theorem hS_k : IsUSplitting (adeleClass F) d.B.ψ d.dd (fun (g : UA σ d.A.J) x => mat g * x) d.S := d.ok.dbl.lin
theorem hO_k : IsUSplitting (adeleClass F) d.B.ψ d.dd (actB (cA σ)) d.om := d.ok.dbl.weil.2.1
theorem hR_k : SiegelRule (cA σ) (adeleClass F) d.B.ψ (-1) (incM F d.A.J) (dbl (incM F d.Y.J)) d.dd d.χ
    (diagCols (Fin d.n)) d.om := d.ok.dbl.weil.2.2
theorem mat_mul_inv_k (g : UA σ d.A.J) : mat g * mat g⁻¹ = 1 := by
  show g.1.1 * (g⁻¹).1.1 = 1
  rw [← Units.val_mul, ← Subgroup.coe_mul, mul_inv_cancel]; rfl
end PositivityTheory.SiegelWeilFormula.tweyl
end
end
end

