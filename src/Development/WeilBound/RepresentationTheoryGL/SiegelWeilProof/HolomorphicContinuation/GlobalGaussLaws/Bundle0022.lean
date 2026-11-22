import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.Bundle0008
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0299
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LintegralNormSqEqToL2
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0355
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0276
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.Bundle0021
import Mathlib

-- bundled from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.DerOneC
section
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.Rg.Sw.Glob.DerOneCH

open PositivityTheory.Rg.Sw.Glob.DerOneH

variable {D : D7} {n : ℕ} {V : HSp D} {θ : InfFam D} {τ : D.what₂.Tau}

theorem frame_lie {s : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ} {ε : Fin V.rank → Bool}
    {fr X : Matrix (Fin V.rank) (Fin V.rank) ℂ} (hfr : IsTauFrame V τ s ε fr) (hX : IsUe ε X) :
    fr * X * fr⁻¹ ∈ lieAt V τ := by
  obtain ⟨hd, hJ, -⟩ := hfr
  have hi : fr * fr⁻¹ = 1 := Matrix.mul_nonsing_inv fr hd
  have hiH : (fr⁻¹)ᴴ * frᴴ = 1 := by rw [← Matrix.conjTranspose_mul, hi, Matrix.conjTranspose_one]
  show (fr * X * fr⁻¹)ᴴ * gramAt D V τ + gramAt D V τ * (fr * X * fr⁻¹) = 0
  calc (fr * X * fr⁻¹)ᴴ * gramAt D V τ + gramAt D V τ * (fr * X * fr⁻¹)
      = (fr⁻¹)ᴴ * Xᴴ * frᴴ * gramAt D V τ * (fr * fr⁻¹) +
          ((fr⁻¹)ᴴ * frᴴ) * gramAt D V τ * (fr * X * fr⁻¹) := by
        rw [hi, hiH]; simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc, Matrix.mul_one, Matrix.one_mul]
    _ = (fr⁻¹)ᴴ * (Xᴴ * Matrix.diagonal (sgn ε) + Matrix.diagonal (sgn ε) * X) * fr⁻¹ := by
        rw [← hJ]; simp only [Matrix.mul_assoc, Matrix.mul_add, Matrix.add_mul]
    _ = 0 := by rw [hX]; simp

theorem hhT_eq {s : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ} {ε : Fin V.rank → Bool}
    {fr X : Matrix (Fin V.rank) (Fin V.rank) ℂ} (hfr : IsTauFrame V τ s ε fr) (t : ℝ) :
    hhT θ V τ fr X t = oneP θ V τ (fr * X * fr⁻¹) t := by
  have hu : IsUnit fr := (Matrix.isUnit_iff_isUnit_det fr).2 hfr.1
  unfold hhT oneP
  congr 1
  have h1 : t • (fr * X * fr⁻¹) = fr * ((t : ℂ) • X) * fr⁻¹ := by
    rw [Matrix.mul_smul, Matrix.smul_mul, Complex.coe_smul]
  rw [h1, Matrix.exp_conj _ _ hu]

theorem compAt_mul {r : ℕ} (τ' : D.what₂.Tau) (A : Matrix (Fin r) (Fin r) (AE D)) (z : Mx D r n) :
    compAt θ τ' (HMul.hMul A z) = HMul.hMul (compAt θ τ' A) (compAt θ τ' z) := by
  show Matrix.map (HMul.hMul A z) ⇑((θ τ').comp (infPart D)) =
    HMul.hMul (Matrix.map A ⇑((θ τ').comp (infPart D))) (Matrix.map z ⇑((θ τ').comp (infPart D)))
  exact Matrix.map_mul

theorem finPart_mul {r : ℕ} (A : Matrix (Fin r) (Fin r) (AE D)) (z : Mx D r n) :
    (HMul.hMul A z).map (finPart D) = HMul.hMul (A.map (finPart D)) (z.map (finPart D)) :=
  Matrix.map_mul

open Classical in
theorem comp_oneP (hθ : IsInfFam θ) {Y : Matrix (Fin V.rank) (Fin V.rank) ℂ} (hY : Y ∈ lieAt V τ) (t : ℝ)
    (τ' : D.what₂.Tau) :
    compAt θ τ' (mt V (oneP θ V τ Y t)) = if τ' = τ then NormedSpace.exp (t • Y) else 1 := by
  have h := (GlobalTheory.RegSch.ChartDer.isAtTau_iff θ V τ _ _).1 (GlobalTheory.Mem.Lift.isAtTau_oneP hθ hY t)
  split_ifs with e
  · subst e; exact h.1
  · exact h.2.1 τ' e

theorem fin_oneP (hθ : IsInfFam θ) {Y : Matrix (Fin V.rank) (Fin V.rank) ℂ} (hY : Y ∈ lieAt V τ) (t : ℝ) :
    (mt V (oneP θ V τ Y t)).map (finPart D) = 1 :=
  ((GlobalTheory.RegSch.ChartDer.isAtTau_iff θ V τ _ _).1 (GlobalTheory.Mem.Lift.isAtTau_oneP hθ hY t)).2.2

section
attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

theorem diff_entry {m : ℕ} (Y : Matrix (Fin m) (Fin m) ℂ) (C : Matrix (Fin m) (Fin n) ℂ) (i : Fin m) (j : Fin n) :
    Differentiable ℝ fun u : ℝ => ((NormedSpace.exp (u • Y) : Matrix (Fin m) (Fin m) ℂ) * C) i j := by
  have : (fun u : ℝ => ((NormedSpace.exp (u • Y) : Matrix (Fin m) (Fin m) ℂ) * C) i j) =
      fun u => ∑ k, (NormedSpace.exp (u • Y) : Matrix (Fin m) (Fin m) ℂ) i k * C k j := by
    funext u; rfl
  rw [this]
  exact Differentiable.fun_sum fun k _ => fun u => ((GlobalTheory.Mem.Lift.hasDerivAt_exp_entry Y u i k).differentiableAt).mul_const _

end

theorem key (hθ : IsInfFam θ) {Y : Matrix (Fin V.rank) (Fin V.rank) ℂ} (hY : Y ∈ lieAt V τ)
    (Φ : schwartzA θ V.rank n) :
    Continuous Φ.1 ∧ ∀ z : Mx D V.rank n, Differentiable ℝ fun u : ℝ => Φ.1 (HMul.hMul (mt V (oneP θ V τ Y u)) z) := by
  classical
  obtain ⟨φ, hφ⟩ := Φ
  refine Submodule.span_induction (p := fun φ _ => Continuous φ ∧ ∀ z : Mx D V.rank n,
      Differentiable ℝ fun u : ℝ => φ (HMul.hMul (mt V (oneP θ V τ Y u)) z)) ?_ ?_ ?_ ?_ hφ
  · rintro _ ⟨f, g, hg, rfl⟩
    have hC : Continuous fun x : Mx D V.rank n => fun τ i j => compAt θ τ x i j :=
      continuous_pi fun τ => continuous_pi fun i => continuous_pi fun j =>
        (continuous_apply j).comp ((continuous_apply i).comp (GlobalTheory.RealWeil.continuous_compAt hθ τ V.rank n))
    have hF : Continuous fun x : Mx D V.rank n => fun i j => finPart D (x i j) :=
      continuous_pi fun i => continuous_pi fun j =>
        GlobalTheory.SchwartzSch.continuous_finPart'.comp ((continuous_apply j).comp (continuous_apply i))
    refine ⟨(f.continuous.comp hC).mul (hg.1.continuous.comp hF), fun z => ?_⟩
    have e : (fun u : ℝ => (fun x : Mx D V.rank n => f (fun τ i j => compAt θ τ x i j) *
        g (fun i j => finPart D (x i j))) (HMul.hMul (mt V (oneP θ V τ Y u)) z)) =
        fun u => f (fun τ' i j => ((if τ' = τ then NormedSpace.exp (u • Y) else 1) * compAt θ τ' z) i j) *
          g (fun i j => finPart D (z i j)) := by
      funext u
      dsimp only
      have h1 : (fun τ' i j => compAt θ τ' (HMul.hMul (mt V (oneP θ V τ Y u)) z) i j) =
          fun τ' i j => ((if τ' = τ then NormedSpace.exp (u • Y) else 1) * compAt θ τ' z) i j := by
        funext τ' i j; rw [compAt_mul, comp_oneP hθ hY]
      have h2 : (fun i j => finPart D ((HMul.hMul (mt V (oneP θ V τ Y u)) z : Mx D V.rank n) i j)) =
          fun i j => finPart D (z i j) := by
        have h := finPart_mul (mt V (oneP θ V τ Y u)) z
        rw [fin_oneP hθ hY, Matrix.one_mul] at h
        funext i j; exact congrFun (congrFun h i) j
      rw [h1, h2]
    rw [e]
    refine Differentiable.mul_const (f.differentiable.comp ?_) _
    refine differentiable_pi.2 fun τ' => differentiable_pi.2 fun i => differentiable_pi.2 fun j => ?_
    by_cases h : τ' = τ
    · simp only [h, if_true]
      exact diff_entry Y (compAt θ τ z) i j
    · simp only [h, if_false, Matrix.one_mul]
      exact differentiable_const _
  · exact ⟨continuous_const, fun z => by simpa using differentiable_const (0 : ℂ)⟩
  · rintro x y - - ⟨h1, h2⟩ ⟨h3, h4⟩
    exact ⟨h1.add h3, fun z => (h2 z).add (h4 z)⟩
  · rintro a x - ⟨h1, h2⟩
    exact ⟨continuous_const.mul h1, fun z => (h2 z).const_mul a⟩

end PositivityTheory.Rg.Sw.Glob.DerOneCH

namespace PositivityTheory.Rg.Sw.Glob

open PositivityTheory.Rg.Sw.Glob.DerOneH PositivityTheory.Rg.Sw.Glob.DerOneCH

theorem curveSt : CurveSt := by
  intro D n V θ τ s ε fr X hθ hs hfr hX
  have hY := frame_lie hfr hX
  have hh : ∀ t, hhT θ V τ fr X t = oneP θ V τ (fr * X * fr⁻¹) t := hhT_eq hfr
  have hadd : ∀ a b, hhT θ V τ fr X (a + b) = hhT θ V τ fr X a * hhT θ V τ fr X b := fun a b => by
    simp only [hh]; exact GlobalTheory.Mem.Lift.oneP_add hθ hY a b
  refine ⟨by rw [hh]; exact GlobalTheory.Mem.Lift.oneP_zero hθ, hadd, fun Φ => ⟨fun y => ?_, fun z t => ?_⟩⟩
  · have hc : Continuous fun p : GA D V × ℝ => HMul.hMul (mt V (hhT θ V τ fr X p.2)) (HMul.hMul (mt V p.1⁻¹) y) := by
      simp only [hh]
      exact ((GlobalTheory.RealWeil.continuous_mt V).1.comp ((GlobalTheory.Mem.Lift.continuous_oneP hθ hY).comp continuous_snd)).matrix_mul
        (((GlobalTheory.RealWeil.continuous_mt V).2.comp continuous_fst).matrix_mul continuous_const)
    exact (key hθ hY Φ).1.comp hc
  · set w := HMul.hMul (mt V (hhT θ V τ fr X t)) z with hw
    have hdiff : DifferentiableAt ℝ (fun v : ℝ => Φ.1 (HMul.hMul (mt V (hhT θ V τ fr X v)) w)) 0 := by
      simp only [hh]; exact (key hθ hY Φ).2 w 0
    have hd0 : HasDerivAt (fun v : ℝ => Φ.1 (HMul.hMul (mt V (hhT θ V τ fr X v)) w))
        (DX θ V τ fr X Φ.1 w) 0 := hdiff.hasDerivAt
    have h1 := HasDerivAt.comp_sub_const t t (by rw [sub_self]; exact hd0)
    refine h1.congr_of_eventuallyEq (Filter.Eventually.of_forall fun u => ?_)
    show Φ.1 (HMul.hMul (mt V (hhT θ V τ fr X u)) z) = Φ.1 (HMul.hMul (mt V (hhT θ V τ fr X (u - t))) w)
    rw [hw, ← Matrix.mul_assoc, ← GlobalTheory.MixModel.mt_mul V, ← hadd, sub_add_cancel]

end PositivityTheory.Rg.Sw.Glob
end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.DilDSt
section
noncomputable section

open Topology

namespace PositivityTheory.Rg.Sw.Glob

def ContDeriv : Prop :=
  ∀ (m n : ℕ) (U : Set ℂ), IsOpen U → ∀ f : ℂ → (Fin m → Fin n → ℂ) → ℂ,
    ContinuousOn (fun p : ℂ × (Fin m → Fin n → ℂ) => f p.1 p.2) (U ×ˢ Set.univ) →
    (∀ u, DifferentiableOn ℂ (fun z => f z u) U) →
    ∀ r : ℕ, ContinuousOn (fun p : ℂ × (Fin m → Fin n → ℂ) => iteratedDeriv r (fun z => f z p.2) p.1) (U ×ˢ Set.univ)

def SchScale : Prop :=
  ∀ (m n : ℕ) (f : (Fin m → Fin n → ℂ) → ℂ) (s : ℝ) (X : Fin n → ℝ) (a : ℂ), IsSch f →
    IsSch (fun u => a * f (fun i j => u i j * Real.exp (s * X j)))

end PositivityTheory.Rg.Sw.Glob
end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.GaussJ
section
noncomputable section

open scoped Matrix ComplexOrder
open Matrix

namespace PositivityTheory.Rg.Sw.Glob.GaussH

variable {n : ℕ}

theorem mul_I_smul_one (X : Matrix (Fin n) (Fin n) ℂ) : X * (Complex.I • (1 : Matrix (Fin n) (Fin n) ℂ)) = Complex.I • X := by
  rw [Matrix.mul_smul, Matrix.mul_one]

theorem conj_I_smul_one : (Complex.I • (1 : Matrix (Fin n) (Fin n) ℂ))ᴴ = -(Complex.I • (1 : Matrix (Fin n) (Fin n) ℂ)) := by
  rw [Matrix.conjTranspose_smul, Matrix.conjTranspose_one, Complex.star_def, Complex.conj_I, neg_smul]

end PositivityTheory.Rg.Sw.Glob.GaussH
end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.ProdF
section
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct ComplexOrder
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.Rg.Sw.Glob.VacK

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.Glob PositivityTheory.Rg.Sw.Glob.VacS PositivityTheory.Rg.Sw.Glob.VacB PositivityTheory.Rg.Sw.Glob.VacC
  PositivityTheory.Rg.Sw.Glob.VacD PositivityTheory.Rg.Sw.Glob.VacE PositivityTheory.Rg.Sw.Glob.VacF PositivityTheory.Rg.Sw.Glob.VacG PositivityTheory.Rg.Sw.Glob.VacH
  PositivityTheory.Rg.Sw.Glob.VacI PositivityTheory.Rg.Sw.Glob.VacJ

theorem prodF {m n : ℕ} (t : ℝ) (ε : Fin m → Bool) (φ : Fin n → ℝ) :
    ∏ a, ∏ j, ((Real.cos (φ j) : ℂ) + Complex.I * (rhoT t ε a : ℂ) * (Real.sin (φ j) : ℂ)) =
      (∏ j, Complex.exp (Complex.I * (φ j : ℂ))) ^ (cnt (epsT t ε) true) *
        ((∏ j, Complex.exp (Complex.I * (φ j : ℂ)))⁻¹) ^ (cnt (epsT t ε) false) := by
  have inner : ∀ a, ∏ j, ((Real.cos (φ j) : ℂ) + Complex.I * (rhoT t ε a : ℂ) * (Real.sin (φ j) : ℂ)) =
      if epsT t ε a = true then ∏ j, Complex.exp (Complex.I * (φ j : ℂ))
      else (∏ j, Complex.exp (Complex.I * (φ j : ℂ)))⁻¹ := by
    intro a
    by_cases h : epsT t ε a = true
    · rw [if_pos h]
      refine Finset.prod_congr rfl fun j _ => ?_
      simp only [rhoT, if_pos h]
      rw [show Complex.I * (φ j : ℂ) = (φ j : ℂ) * Complex.I by ring, Complex.exp_mul_I, ← Complex.ofReal_cos,
        ← Complex.ofReal_sin]
      push_cast
      ring
    · rw [if_neg h, ← Finset.prod_inv_distrib]
      refine Finset.prod_congr rfl fun j _ => ?_
      simp only [rhoT, if_neg h]
      rw [← Complex.exp_neg, show -(Complex.I * (φ j : ℂ)) = (-(φ j : ℂ)) * Complex.I by ring, Complex.exp_mul_I,
        Complex.cos_neg, Complex.sin_neg, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
      push_cast
      ring
  rw [Finset.prod_congr rfl (fun a _ => inner a), Finset.prod_ite, Finset.prod_const, Finset.prod_const]
  simp only [cnt, Bool.not_eq_true]

theorem alg (a a' X : ℂ) (ha : a ≠ 0) (ha' : a' ≠ 0) (hX : X ≠ 0) (e : ℤ) (p q : ℕ) :
    1 * (a' ^ e * (a'⁻¹) ^ (((p + q : ℕ) : ℤ) - e)) * (X ^ p * (X⁻¹) ^ q) * (a ^ e * (a⁻¹) ^ (((p + q : ℕ) : ℤ) - e)) =
      (a * a * (a' * a')) ^ e * (a * X⁻¹ * a') ^ (-(p : ℤ)) * (a * X * a') ^ (-(q : ℤ)) := by
  rw [inv_zpow', inv_zpow', neg_sub, zpow_sub₀ ha, zpow_sub₀ ha']
  simp only [zpow_neg, zpow_natCast, mul_zpow, inv_pow, mul_pow]
  have hA : a ^ e ≠ 0 := zpow_ne_zero e ha
  have hA' : a' ^ e ≠ 0 := zpow_ne_zero e ha'
  have hXp : X ^ p ≠ 0 := pow_ne_zero p hX
  have hXq : X ^ q ≠ 0 := pow_ne_zero q hX
  field_simp
  ring

end PositivityTheory.Rg.Sw.Glob.VacK
end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.UnipotentBlockMulAdd
section
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.Rg.Sw.Glob

open GlobalTheory.CompanionTheory.HermPoisson

variable {D : D7} {n : ℕ}

namespace FZNH

theorem unipotent_block_mul_add {R : Type} [CommRing R] (b c : Matrix (Fin n) (Fin n) R) :
    blk4 1 b 0 1 * blk4 1 c 0 1 = blk4 (1 : Matrix (Fin n) (Fin n) R) (b + c) 0 1 := by
  unfold blk4
  rw [Matrix.submatrix_mul_equiv, Matrix.fromBlocks_multiply]
  congr 1
  simp [add_comm]

theorem block_matrix_one {R : Type} [CommRing R] : blk4 (1 : Matrix (Fin n) (Fin n) R) 0 0 1 = 1 := by
  unfold blk4
  rw [Matrix.fromBlocks_one]
  exact Matrix.submatrix_one_equiv _

theorem mat_injective : Function.Injective (mat (D := D) (n := n)) := fun x y h =>
  GlobalTheory.AdelicU.matHom_injective _ _ _ (Units.ext h)

theorem mat_mul (x y : G D n) : mat (x * y) = mat x * mat y := by
  simp only [mat, map_mul, Units.val_mul]

theorem mat_one : mat (1 : G D n) = 1 := by
  simp only [mat, map_one, Units.val_one]

theorem nb_add {nb : hermA D n → G D n} (h : PositivityTheory.PfSWUS.IsNMap nb) (b c : hermA D n) :
    nb (b + c) = nb b * nb c := by
  apply mat_injective
  rw [mat_mul, h, h, h, unipotent_block_mul_add]
  rfl

theorem nb_zero {nb : hermA D n → G D n} (h : PositivityTheory.PfSWUS.IsNMap nb) : nb 0 = 1 := by
  apply mat_injective
  rw [h, mat_one]
  exact block_matrix_one

theorem nb_neg {nb : hermA D n → G D n} (h : PositivityTheory.PfSWUS.IsNMap nb) (b : hermA D n) : (nb b)⁻¹ = nb (-b) := by
  have h' : nb (-b) * nb b = 1 := by rw [← nb_add h, neg_add_cancel, nb_zero h]
  exact (eq_inv_of_mul_eq_one_left h').symm

set_option synthInstance.maxHeartbeats 400000 in
theorem nb_continuous {nb : hermA D n → G D n} (h : PositivityTheory.PfSWUS.IsNMap nb) : Continuous nb := by
  obtain ⟨i1, -⟩ := lattice_Mx D n n
  haveI : IsTopologicalAddGroup (Mx D n n) := i1
  have he := GlobalTheory.AdelicU.isEmbedding_matHom (AF D.host.F) D.sp.cm.sig (Jst D n)
  rw [he.continuous_iff, Units.continuous_iff]
  have hc : Continuous fun b : hermA D n => blk4 (1 : Mx D n n) b.1 0 1 := by
    unfold blk4
    exact (continuous_const.matrix_fromBlocks continuous_subtype_val continuous_const continuous_const).matrix_submatrix _ _
  refine ⟨?_, ?_⟩
  · convert hc using 1
    funext b
    exact h b
  · convert hc.comp continuous_neg using 1
    funext b
    simp only [Function.comp_apply]
    rw [← map_inv, nb_neg h]
    exact h (-b)

end FZNH

open FZNH

theorem fourierZeroN : FourierZeroN := by
  intro D n ψ hψ nb lam 𝓖 hcd f hf hinv hco
  obtain ⟨hnb, hH, h𝓖, -⟩ := hcd
  funext g
  have key := hermFourierZero D n ψ hψ lam hH 𝓖 h𝓖 (fun b => f (nb b * g))
    (hf.comp ((nb_continuous hnb).mul continuous_const)) (fun x l hl => by
      obtain ⟨β, hβ⟩ := (ofHermE_bijective (D := D) (r := n)).2 ⟨l, hl⟩
      show f (nb (x + l) * g) = f (nb x * g)
      rw [show x + l = l + x from add_comm x l, nb_add hnb, mul_assoc]
      refine hinv l ⟨β, ?_⟩ _
      rw [← ofHermE_val, hβ]) (fun β => hco β g) 0
  simpa [nb_zero hnb] using key

end PositivityTheory.Rg.Sw.Glob
end
end

