import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.WeilSiegelTheta.Bundle0001
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0396
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0746
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0736
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0741
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0752
import Development.WeilBound.CoreStatements.AutomorphicKernels.UnitarySchrodingerModel.CoefDataExists
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0370
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0375
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0275

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RationalGroupLeOfGeneratorsMem
section
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.EC
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.RatGen

open GlobalTheory.StdUnn.Model GlobalTheory.StdUnn.Gen

variable {D : D7} {n : ℕ}

abbrev rm (x : Matrix (Fin n) (Fin n) D.host.E) : Mx D n n := x.map (incA D)

theorem rm_mul (x y : Matrix (Fin n) (Fin n) D.host.E) : rm (x * y) = rm x * rm y :=
  Matrix.map_mul

theorem rm_add (x y : Matrix (Fin n) (Fin n) D.host.E) : rm (x + y) = rm x + rm y :=
  Matrix.map_add _ (map_add _) x y

theorem rm_neg (x : Matrix (Fin n) (Fin n) D.host.E) : rm (-x) = -rm x := by
  ext i j; simp [rm]

theorem rm_one : rm (1 : Matrix (Fin n) (Fin n) D.host.E) = 1 := by
  simp [rm]

theorem rm_zero : rm (0 : Matrix (Fin n) (Fin n) D.host.E) = 0 := by
  simp [rm]

theorem blockMatrix_map (a b c d : Matrix (Fin n) (Fin n) D.host.E) :
    (blk4 a b c d).map (incA D) = blk4 (rm a) (rm b) (rm c) (rm d) := by
  ext i j
  simp only [blk4, Matrix.map_apply, Matrix.submatrix_apply]
  rcases finSumFinEquiv.symm i with i | i <;> rcases finSumFinEquiv.symm j with j | j <;> rfl

def ru (u : GL (Fin n) D.host.E) : GL (Fin n) (AE D) := Units.map (incA D).mapMatrix.toMonoidHom u

theorem ru_val (u : GL (Fin n) D.host.E) : (ru u).1 = rm u.1 := rfl

theorem ru_inv_val (u : GL (Fin n) D.host.E) : ((ru u)⁻¹).1 = rm (u⁻¹).1 := rfl

variable {S : Subgroup (G D n)}
  (hm : ∀ (g : G D n) (a : GL (Fin n) D.host.E), mat g = blk4 (a.1.map (incA D)) 0 0 (adj ((a⁻¹).1.map (incA D))) → g ∈ S)
  (hn : ∀ (g : G D n) (b : Matrix (Fin n) (Fin n) D.host.E), mat g = blk4 1 (b.map (incA D)) 0 1 → g ∈ S)
  (hw : ∀ g : G D n, mat g = blk4 0 1 (-1) 0 → g ∈ S)

include hm hn in
theorem mem_of_upper {g : G D n} {a b d : Matrix (Fin n) (Fin n) D.host.E} (hg : mat g = blk4 (rm a) (rm b) 0 (rm d))
    (ha : IsUnit a) : g ∈ S := by
  obtain ⟨u, rfl⟩ := ha
  obtain ⟨m, hmm⟩ := exists_levi (D := D) (n := n) (ru u)⁻¹
  have hmm' : mat m = blk4 (rm (u⁻¹).1) 0 0 (adj (rm u.1)) := by
    rw [hmm, ru_inv_val, inv_inv, ru_val]
  have h1 : (adj (rm u.1) : Mx D n n) * rm d = 1 := by simpa using (rel hg).2.1
  have hmS : m ∈ S := hm m u⁻¹ (by rw [hmm', inv_inv])
  rw [← S.mul_mem_cancel_left hmS]
  refine hn _ ((u⁻¹).1 * b) ?_
  have h2 : rm (u⁻¹).1 * rm u.1 = 1 := by
    rw [← rm_mul, Units.inv_mul, rm_one]
  rw [mat_mul, hmm', hg, submatrix_fromBlocks_mul]
  simp only [h2, mul_zero, zero_mul, add_zero, zero_add, h1]
  change _ = blk4 1 (rm _) 0 1
  rw [rm_mul]

include hm hn hw in
theorem mem_of_lower {g : G D n} {a c d : Matrix (Fin n) (Fin n) D.host.E} (hg : mat g = blk4 (rm a) 0 (rm c) (rm d))
    (hd : IsUnit d) : g ∈ S := by
  obtain ⟨w, hww⟩ := exists_weyl (D := D) (n := n)
  rw [← S.mul_mem_cancel_left (hw w hww), ← S.mul_mem_cancel_right (hw w hww)]
  refine mem_of_upper hm hn (a := -d) (b := c) (d := -a) ?_ hd.neg
  rw [mat_mul, mat_mul, hww, hg, submatrix_fromBlocks_mul, submatrix_fromBlocks_mul, rm_neg, rm_neg]
  simp

include hm hn hw in
theorem mem_of_isUnit {g : G D n} {a b c d : Matrix (Fin n) (Fin n) D.host.E}
    (hg : mat g = blk4 (rm a) (rm b) (rm c) (rm d)) (hd : IsUnit d) : g ∈ S := by
  obtain ⟨u, rfl⟩ := hd
  have h1 : (adj (rm u.1) : Mx D n n) * rm b = adj (rm b) * rm u.1 := neg_add_eq_zero.1 (rel hg).2.2
  have h0 : rm u.1 * rm (u⁻¹).1 = 1 := by rw [← rm_mul, Units.mul_inv, rm_one]
  have h0' : rm (u⁻¹).1 * rm u.1 = 1 := by rw [← rm_mul, Units.inv_mul, rm_one]
  have h2 : (adj (rm (u⁻¹).1) : Mx D n n) * adj (rm u.1) = 1 := by rw [← adj_mul, h0, adj_one]
  have h3 : (adj (-(rm b * rm (u⁻¹).1)) : Mx D n n) = -(rm b * rm (u⁻¹).1) := by
    rw [adj_neg, adj_mul]
    congr 1
    calc (adj (rm (u⁻¹).1) : Mx D n n) * adj (rm b) = adj (rm (u⁻¹).1) * (adj (rm b) * rm u.1) * rm (u⁻¹).1 := by
          rw [mul_assoc, mul_assoc, h0, mul_one]
      _ = rm b * rm (u⁻¹).1 := by rw [← h1, ← mul_assoc, h2, one_mul]
  obtain ⟨x, hx⟩ := (exists_unip _).2 h3
  have hxS : x ∈ S := hn x (-(b * (u⁻¹).1)) (by rw [hx]; change _ = blk4 1 (rm _) 0 1; rw [rm_neg, rm_mul])
  rw [← S.mul_mem_cancel_left hxS]
  refine mem_of_lower hm hn hw (a := a + -(b * (u⁻¹).1) * c) (c := c) (d := u.1) ?_ u.isUnit
  rw [mat_mul, hx, hg, submatrix_fromBlocks_mul, rm_add, rm_mul, rm_neg, rm_mul]
  simp only [one_mul, zero_mul, zero_add, neg_mul, mul_assoc, h0', mul_one, add_neg_cancel]

theorem adj_rm {x : Matrix (Fin n) (Fin n) D.host.E} (hx : ∀ i j, (D.sp.cm.sig : D.host.E →+* D.host.E) (x i j) = x j i) :
    adj (rm x : Mx D n n) = rm x := by
  ext i j
  simp only [adj, Matrix.transpose_apply, Matrix.map_apply]
  rw [GlobalTheory.DualPairCheck.cA_incA]
  exact congrArg _ (hx j i)

theorem exists_herm_isUnit (c d p q : Matrix (Fin n) (Fin n) D.host.E) (h : c * p + d * q = 1) :
    ∃ x : Matrix (Fin n) (Fin n) D.host.E, (∀ i j, (D.sp.cm.sig : D.host.E →+* D.host.E) (x i j) = x j i) ∧
      IsUnit (c * x + d) := by
  obtain ⟨x, hx, hu⟩ := GlobalTheory.HermTransversal.exists_herm_notMem (D.sp.cm.sig : D.host.E →+* D.host.E) D.host.xi0
    (GlobalTheory.DualPairCompare.embedding_xi_zero_ne_zero D) (GlobalTheory.DualPairCheck.star_purely_imaginary_eq_neg D) (RingHom.id _) (D.sp.cm.sig : D.host.E →+* D.host.E)
    (fun _ => rfl) c d p q h ⊥ Ideal.bot_isMaximal
  refine ⟨x, hx, ?_⟩
  have e : x.map (RingHom.id D.host.E) = x := by ext i j; rfl
  rw [e] at hu
  refine (Matrix.isUnit_iff_isUnit_det _).2 (isUnit_iff_ne_zero.2 fun h0 => hu ?_)
  rw [h0, zero_mul]
  exact Ideal.zero_mem _

end GlobalTheory.CompanionTheory.RatGen

namespace GlobalTheory.CompanionTheory

theorem RatGen.GF_le_of_levi_unip_weyl : ∀ (D : D7) (n : ℕ) (S : Subgroup (G D n)),
  (∀ (g : G D n) (a : GL (Fin n) D.host.E), mat g = blk4 (a.1.map (incA D)) 0 0 (adj ((a⁻¹).1.map (incA D))) → g ∈ S) →
  (∀ (g : G D n) (b : Matrix (Fin n) (Fin n) D.host.E), mat g = blk4 1 (b.map (incA D)) 0 1 → g ∈ S) →
  (∀ g : G D n, mat g = blk4 0 1 (-1) 0 → g ∈ S) → GF D n ≤ S := by
  intro D n S hm hn hw γ hγ
  have hrat : ∀ {γ : G D n}, γ ∈ GF D n →
      ∃ x : Matrix (Fin (n + n)) (Fin (n + n)) D.host.E, mat γ = x.map (incA D) := by
    intro γ h
    obtain ⟨x, -, hx⟩ := h
    exact ⟨x.1, (congrArg Units.val hx).symm⟩
  obtain ⟨M, hM⟩ := hrat hγ
  obtain ⟨M', hM'⟩ := hrat ((GF D n).inv_mem hγ)
  obtain ⟨a, b, c, d, rfl⟩ := GlobalTheory.StdUnn.Gen.exists_blockMatrixTwoByTwoFin_eq M
  obtain ⟨p', p, q', q, rfl⟩ := GlobalTheory.StdUnn.Gen.exists_blockMatrixTwoByTwoFin_eq M'
  rw [RatGen.blockMatrix_map] at hM hM'
  have h1 : mat γ * mat γ⁻¹ = 1 := by rw [← GlobalTheory.StdUnn.Gen.mat_mul, mul_inv_cancel]; rfl
  rw [hM, hM', Model.submatrix_fromBlocks_mul, ← Model.block_matrix_one] at h1
  have h2 : RatGen.rm (c * p + d * q) = RatGen.rm (1 : Matrix (Fin n) (Fin n) D.host.E) := by
    rw [RatGen.rm_add, RatGen.rm_mul, RatGen.rm_mul, RatGen.rm_one]
    exact (Model.blockMatrixTwoByTwoFin_injective h1).2.2.2
  have h3 : c * p + d * q = 1 := Matrix.map_injective GlobalTheory.MixModel.incA_injective h2
  obtain ⟨x, hx, hu⟩ := RatGen.exists_herm_isUnit c d p q h3
  obtain ⟨y, hy⟩ := (Model.exists_unip (RatGen.rm x)).2 (RatGen.adj_rm hx)
  rw [← S.mul_mem_cancel_right (hn y x hy)]
  refine RatGen.mem_of_isUnit hm hn hw (a := a) (b := a * x + b) (c := c) (d := c * x + d) ?_ hu
  rw [GlobalTheory.StdUnn.Gen.mat_mul, hM, hy, Model.submatrix_fromBlocks_mul, RatGen.rm_add, RatGen.rm_add, RatGen.rm_mul, RatGen.rm_mul]
  simp only [mul_one, mul_zero, add_zero]

end GlobalTheory.CompanionTheory
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ResATranslate
section
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.ResMu

open Set GlobalTheory.Eis

variable {D : D7} {p : ℕ}

theorem law_ratInv {n : ℕ} {z : ℂ} {s : G D n → ℂ} (hs : IsLaw 1 z s) : LeftInv (P D n ⊓ GF D n) s := fun γ hγ g => by
  obtain ⟨a, ha⟩ := GlobalTheory.StdUnn.LeftInvSect.exists_blkA hγ.1
  obtain ⟨u, hu⟩ := GlobalTheory.StdUnn.LeftInvSect.det_rat hγ.2 a ha
  have h1 : absA D (Units.map (incA D).toMonoidHom u) = 1 := absE_inclR u
  rw [hs γ hγ.1 a ha g, hu, h1]
  simp

theorem rho_right {f : G D p → ℂ} (hf : IsRho f) (x : G D p) : IsRho fun g => f (g * x) :=
  ⟨hf.1.comp (continuous_id.mul continuous_const), law_right hf.2 x⟩

theorem fam_law_real {H : G D p → ℝ≥0} (hH : IsHt H) {f : G D p → ℂ} (hf : IsRho f) (σ : ℝ) :
    IsLaw 1 (σ : ℂ) (fam H f ((p : ℂ) / 2) (σ : ℂ)) := fam_law hH hf.2 σ

theorem fam_cont_at {H : G D p → ℝ≥0} (hH : IsHt H) {f : G D p → ℂ} (hf : Continuous f) (s₁ : ℂ) (σ : ℝ) :
    Continuous (fam H f s₁ (σ : ℂ)) :=
  (fam_cont hH hf s₁).comp (f := fun g : G D p => ((σ, g) : ℝ × G D p)) (by fun_prop)

theorem fam_at (H : G D p → ℝ≥0) (f : G D p → ℂ) : fam H f ((p : ℂ) / 2) (((p : ℝ) / 2 : ℝ) : ℂ) = f := by
  funext g
  have : ((((p : ℝ) / 2 : ℝ) : ℂ)) - (p : ℂ) / 2 = 0 := by push_cast; ring
  simp [fam, this]

theorem res_leftInv {H : G D p → ℝ≥0} (hH : IsHt H) {f : G D p → ℂ} (hf : IsRho f) (σ : ℝ) :
    LeftInv (GF D p) (res H f σ) := fun γ hγ g => by
  simp only [res, eisS]
  rw [leftInv_cosetSum (law_ratInv (fam_law_real hH hf σ)) γ hγ g]

theorem eis_right (s : G D p → ℂ) (x : G D p) : eisS s x = eisS (fun g => s (g * x)) 1 := by
  simp only [eisS]
  rw [cosetSum_mul_right, one_mul]

theorem res_equi (hS : SphBound) (hp : 1 ≤ p) {H : G D p → ℝ≥0} (hH : IsHt H) {C : Set (G D p)} (hC : IsCompact C)
    (hcov : ∀ g, ∃ q ∈ P D p, ∃ c ∈ C, g = q * c) {f : G D p → ℂ} (hf : IsRho f) (x : G D p) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ x' in 𝓝 x, ∀ σ ∈ Ioc ((p : ℝ) / 2) (p / 2 + 1), ‖res H f σ x' - res H f σ x‖ ≤ ε := by
  obtain ⟨B, hB0, hB⟩ := eis_bound hS hp hH (isCompact_singleton (x := (1 : G D p)))
  have hK : IsCompact (Icc ((p : ℝ) / 2) (p / 2 + 1) ×ˢ C) := isCompact_Icc.prod hC
  have hε' : 0 < ε / (2 * (B + 1)) := by positivity
  have hfc := fam_cont hH hf.1 ((p : ℂ) / 2)
  have hev : ∀ᶠ x' in 𝓝 x, ∀ y ∈ Icc ((p : ℝ) / 2) (p / 2 + 1) ×ˢ C,
      ‖fam H f ((p : ℂ) / 2) (y.1 : ℂ) (y.2 * x') - fam H f ((p : ℂ) / 2) (y.1 : ℂ) (y.2 * x)‖ <
        ε / (2 * (B + 1)) * (H y.2 : ℝ) ^ (y.1 + p / 2) := by
    refine hK.eventually_forall_of_forall_eventually fun y _ => ?_
    have c1 : Continuous fun u : G D p × (ℝ × G D p) => fam H f ((p : ℂ) / 2) (u.2.1 : ℂ) (u.2.2 * u.1) :=
      hfc.comp (f := fun u : G D p × (ℝ × G D p) => ((u.2.1, u.2.2 * u.1) : ℝ × G D p)) (by fun_prop)
    have c2 : Continuous fun u : G D p × (ℝ × G D p) => fam H f ((p : ℂ) / 2) (u.2.1 : ℂ) (u.2.2 * x) :=
      hfc.comp (f := fun u : G D p × (ℝ × G D p) => ((u.2.1, u.2.2 * x) : ℝ × G D p)) (by fun_prop)
    have c3 : Continuous fun u : G D p × (ℝ × G D p) => ε / (2 * (B + 1)) * (H u.2.2 : ℝ) ^ (u.2.1 + p / 2) :=
      continuous_const.mul ((NNReal.continuous_coe.comp (hH.1.comp (continuous_snd.comp continuous_snd))).rpow
        ((continuous_fst.comp continuous_snd).add continuous_const) fun u => Or.inl (NNReal.coe_pos.2 (hH.2.1 _)).ne')
    refine ((c1.sub c2).norm.continuousAt.eventually_lt c3.continuousAt ?_)
    simp only [Pi.sub_apply, sub_self, norm_zero]
    exact mul_pos hε' (Real.rpow_pos_of_pos (NNReal.coe_pos.2 (hH.2.1 _)) _)
  filter_upwards [hev] with x' hx' σ hσ
  have hI' : σ ∈ Icc ((p : ℝ) / 2) (p / 2 + 1) := ⟨hσ.1.le, hσ.2⟩
  have hl := fam_law_real hH hf σ
  have hc := fam_cont_at hH hf.1 ((p : ℂ) / 2) σ
  have hct : ∀ y : G D p, Continuous fun g => fam H f ((p : ℂ) / 2) (σ : ℂ) (g * y) := fun y =>
    hc.comp (continuous_id.mul continuous_const)
  have hb := law_bound hH hcov (law_sub (law_right hl x') (law_right hl x)) (δ := ε / (2 * (B + 1))) (fun c hc =>
    (hx' (σ, c) ⟨hI', hc⟩).le)
  have hf' := (hB σ hσ 1 rfl _ _ hb).2
  rw [eis_sub (conv_of_section hS hp hH hC hcov hσ (hct x') (law_right hl x') 1)
    (conv_of_section hS hp hH hC hcov hσ (hct x) (law_right hl x) 1), ← eis_right, ← eis_right] at hf'
  have e : res H f σ x' - res H f σ x =
      ((σ - p / 2 : ℝ) : ℂ) * (eisS (fam H f ((p : ℂ) / 2) (σ : ℂ)) x' - eisS (fam H f ((p : ℂ) / 2) (σ : ℂ)) x) := by
    simp only [res]; ring
  rw [e, norm_mul, Complex.norm_real, Real.norm_of_nonneg (by linarith [hσ.1])]
  have : ε / (2 * (B + 1)) * B ≤ ε := by
    rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
    nlinarith
  linarith

theorem res_cont (hS : SphBound) (hp : 1 ≤ p) {H : G D p → ℝ≥0} (hH : IsHt H) {C : Set (G D p)} (hC : IsCompact C)
    (hcov : ∀ g, ∃ q ∈ P D p, ∃ c ∈ C, g = q * c) {f : G D p → ℂ} (hf : IsRho f) {σ : ℝ}
    (hσ : σ ∈ Ioc ((p : ℝ) / 2) (p / 2 + 1)) : Continuous (res H f σ) := by
  rw [continuous_iff_continuousAt]
  intro x
  rw [ContinuousAt, Metric.tendsto_nhds]
  intro ε hε
  filter_upwards [res_equi hS hp hH hC hcov hf x (half_pos hε)] with x' hx'
  rw [dist_eq_norm]
  linarith [hx' σ hσ]

theorem resA_near (hS : SphBound) (hp : 1 ≤ p) {H : G D p → ℝ≥0} (hH : IsHt H) {C : Set (G D p)} (hC : IsCompact C)
    (hcov : ∀ g, ∃ q ∈ P D p, ∃ c ∈ C, g = q * c) {f : G D p → ℂ} (hf : IsRho f) (x : G D p) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ x' in 𝓝 x, ‖resA H f x' - resA H f x‖ ≤ ε := by
  filter_upwards [res_equi hS hp hH hC hcov hf x hε] with x' hx'
  have h1 := ((res_tendsto hS hp hH hC hcov hf x').sub (res_tendsto hS hp hH hC hcov hf x)).norm
  refine le_of_tendsto h1 ?_
  refine ufil_le p ?_
  filter_upwards [ev_Ioc p] with σ hσ using hx' σ hσ

theorem resA_cont (hS : SphBound) (hp : 1 ≤ p) {H : G D p → ℝ≥0} (hH : IsHt H) {C : Set (G D p)} (hC : IsCompact C)
    (hcov : ∀ g, ∃ q ∈ P D p, ∃ c ∈ C, g = q * c) {f : G D p → ℂ} (hf : IsRho f) : Continuous (resA H f) := by
  rw [continuous_iff_continuousAt]
  intro x
  rw [ContinuousAt, Metric.tendsto_nhds]
  intro ε hε
  filter_upwards [resA_near hS hp hH hC hcov hf x (half_pos hε)] with x' hx'
  rw [dist_eq_norm]
  linarith

theorem resA_leftInv (hS : SphBound) (hp : 1 ≤ p) {H : G D p → ℝ≥0} (hH : IsHt H) {C : Set (G D p)} (hC : IsCompact C)
    (hcov : ∀ g, ∃ q ∈ P D p, ∃ c ∈ C, g = q * c) {f : G D p → ℂ} (hf : IsRho f) : LeftInv (GF D p) (resA H f) := fun γ hγ g => by
  refine tendsto_nhds_unique (res_tendsto hS hp hH hC hcov hf (γ * g)) ?_
  have := res_tendsto hS hp hH hC hcov hf g
  refine this.congr fun σ => ?_
  rw [res_leftInv hH hf σ γ hγ g]

theorem resA_unif (hS : SphBound) (hp : 1 ≤ p) {H : G D p → ℝ≥0} (hH : IsHt H) {C : Set (G D p)} (hC : IsCompact C)
    (hcov : ∀ g, ∃ q ∈ P D p, ∃ c ∈ C, g = q * c) {f : G D p → ℂ} (hf : IsRho f) {C' : Set (G D p)} (hC' : IsCompact C')
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ σ in ((ufil p : Ultrafilter ℝ) : Filter ℝ), ∀ c ∈ C', ‖res H f σ c - resA H f c‖ ≤ ε := by
  refine hC'.induction_on (p := fun S => ∀ᶠ σ in ((ufil p : Ultrafilter ℝ) : Filter ℝ), ∀ c ∈ S, ‖res H f σ c - resA H f c‖ ≤ ε)
    (by simp) (fun s t hst h => h.mono fun σ hσ c hc => hσ c (hst hc))
    (fun s t hs ht => by
      filter_upwards [hs, ht] with σ h1 h2 c hc
      exact hc.elim (h1 c) (h2 c)) fun x _ => ?_
  have hε3 : 0 < ε / 3 := by positivity
  refine ⟨_, mem_nhdsWithin_of_mem_nhds ((res_equi hS hp hH hC hcov hf x hε3).and (resA_near hS hp hH hC hcov hf x hε3)), ?_⟩
  have h1 : ∀ᶠ σ in ((ufil p : Ultrafilter ℝ) : Filter ℝ), ‖res H f σ x - resA H f x‖ < ε / 3 := by
    have := (res_tendsto hS hp hH hC hcov hf x)
    rw [Metric.tendsto_nhds] at this
    filter_upwards [this _ hε3] with σ hσ
    rwa [dist_eq_norm] at hσ
  filter_upwards [h1, ufil_le p (ev_Ioc p)] with σ hσ hI c hc
  have a1 := hc.1 σ hI
  have a2 := hc.2
  calc ‖res H f σ c - resA H f c‖ = ‖(res H f σ c - res H f σ x) + (res H f σ x - resA H f x) - (resA H f c - resA H f x)‖ := by
        congr 1; ring
    _ ≤ ‖res H f σ c - res H f σ x‖ + ‖res H f σ x - resA H f x‖ + ‖resA H f c - resA H f x‖ :=
        (norm_sub_le _ _).trans (by gcongr; exact norm_add_le _ _)
    _ ≤ ε := by linarith

theorem resA_translate (hS : SphBound) (hp : 1 ≤ p) {H : G D p → ℝ≥0} (hH : IsHt H) {C : Set (G D p)} (hC : IsCompact C)
    (hcov : ∀ g, ∃ q ∈ P D p, ∃ c ∈ C, g = q * c) {f : G D p → ℂ} (hf : IsRho f) (x : G D p) :
    resA H f x = resA H (fun g => f (g * x)) 1 := by
  have hfx := rho_right hf x
  have hd := tendsto_diff hS hp hH hC hcov
    (S := fun σ g => fam H f ((p : ℂ) / 2) (σ : ℂ) (g * x)) (S' := fun σ => fam H (fun g => f (g * x)) ((p : ℂ) / 2) (σ : ℂ))
    ((fam_cont hH hf.1 _).comp (f := fun u : ℝ × G D p => ((u.1, u.2 * x) : ℝ × G D p)) (by fun_prop)).continuousOn
    (fam_cont hH hfx.1 _).continuousOn
    (fun σ _ => law_right (fam_law_real hH hf σ) x) (fun σ _ => fam_law_real hH hfx σ)
    (by simp only [fam_at])
  have h1 := (hd.mono_left (ufil_le p)).add (res_tendsto hS hp hH hC hcov hfx 1)
  rw [zero_add] at h1
  refine tendsto_nhds_unique (res_tendsto hS hp hH hC hcov hf x) (h1.congr fun σ => ?_)
  simp only [res]
  rw [eis_right (fam H f ((p : ℂ) / 2) (σ : ℂ)) x]
  ring

end GlobalTheory.CompanionTheory.ResMu
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SchwartzFunctionLatticeIndicatorSum
section
open Matrix MeasureTheory GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.LeibOrd GlobalTheory.SplitWeil GlobalTheory.JHMult GlobalTheory.CompanionTheory.BZShell GlobalTheory.CompanionTheory.MirPair GlobalTheory.CompanionTheory.BZCore
open scoped Topology

noncomputable section

namespace GlobalTheory.CompanionTheory.BZCore

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {d : ℕ}
  {V : Type} [AddCommGroup V] [Module ℂ V]

theorem exists_latZ_subset_of_mem_nhds (z : GL (Fin d) k) (ϖ : k)
    (hz : (z : Matrix (Fin d) (Fin d) k) = ϖ • (1 : Matrix (Fin d) (Fin d) k))
    (hϖ : ValuativeRel.valuation k ϖ < 1) (hϖ0 : ϖ ≠ 0) {U : Set (Fin d → k)} (hU : U ∈ 𝓝 (0 : Fin d → k)) :
    ∃ r : ℕ, ((latZ z (r : ℤ)).sub : Set (Fin d → k)) ⊆ U := by
  have hall : ∀ᶠ t : k in 𝓝 0, ∀ w ∈ ((lat0 : COSub k d).sub : Set (Fin d → k)), t • w ∈ U := by
    refine (lat0 : COSub k d).isCompact.eventually_forall_of_forall_eventually fun w _ => ?_
    have hc : Continuous fun p : k × (Fin d → k) => p.1 • p.2 := continuous_fst.smul continuous_snd
    have h0 : U ∈ 𝓝 (((0 : k), w).1 • ((0 : k), w).2) := by simpa using hU
    exact hc.continuousAt.eventually h0
  have ht : Filter.Tendsto (fun n : ℕ => ϖ ^ n) Filter.atTop (𝓝 0) := by
    rw [(IsValuativeTopology.hasBasis_nhds_zero' k).tendsto_right_iff]
    intro γ hγ
    have : MulArchimedean (ValuativeRel.ValueGroupWithZero k) :=
      ValuativeRel.isRankLeOne_iff_mulArchimedean.mp inferInstance
    obtain ⟨n, hn⟩ := exists_pow_lt₀ hϖ (Units.mk0 γ hγ)
    filter_upwards [Filter.eventually_ge_atTop n] with m hm
    rw [map_pow]
    exact lt_of_le_of_lt (pow_le_pow_right_of_le_one' hϖ.le hm) hn
  obtain ⟨r, hr⟩ := (ht.eventually hall).exists
  refine ⟨r, fun y hy => ?_⟩
  have h1 : ϖ ^ r • ((((z ^ (r : ℤ) : GL (Fin d) k)⁻¹ : GL (Fin d) k) : Matrix (Fin d) (Fin d) k).mulVec y) ∈ U :=
    hr _ hy
  have h2 : ϖ ^ r • ((((z ^ (r : ℤ) : GL (Fin d) k)⁻¹ : GL (Fin d) k) : Matrix (Fin d) (Fin d) k).mulVec y) = y := by
    have := zpow_mulVec z ϖ hz hϖ0 (r : ℤ)
      ((((z ^ (r : ℤ) : GL (Fin d) k)⁻¹ : GL (Fin d) k) : Matrix (Fin d) (Fin d) k).mulVec y)
    rw [mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mulVec, zpow_natCast] at this
    exact this.symm
  rwa [h2] at h1

theorem exists_latZ_invariant (z : GL (Fin d) k) (ϖ : k)
    (hz : (z : Matrix (Fin d) (Fin d) k) = ϖ • (1 : Matrix (Fin d) (Fin d) k))
    (hϖ : ValuativeRel.valuation k ϖ < 1) (hϖ0 : ϖ ≠ 0) (f : SchF k d V) :
    ∃ r₀ : ℕ, ∀ y, ∀ l ∈ (latZ z (r₀ : ℤ)).sub, f.1 (y + l) = f.1 y := by
  have hlc : IsLocallyConstant f.1 := f.2.1
  have hK : IsCompact (tsupport f.1) := f.2.2
  have hW : ∀ᶠ l : Fin d → k in 𝓝 0, ∀ y ∈ tsupport f.1, f.1 (y + l) = f.1 y := by
    refine hK.eventually_forall_of_forall_eventually fun y _ => ?_
    have hc : Continuous fun p : (Fin d → k) × (Fin d → k) => p.2 + p.1 := continuous_snd.add continuous_fst
    have h1 := (IsLocallyConstant.iff_eventually_eq _).1 (hlc.comp_continuous hc) ((0 : Fin d → k), y)
    have h2 := (IsLocallyConstant.iff_eventually_eq _).1 (hlc.comp_continuous continuous_snd)
      ((0 : Fin d → k), y)
    filter_upwards [h1, h2] with p hp1 hp2
    have e1 : f.1 (p.2 + p.1) = f.1 (y + 0) := hp1
    have e2 : f.1 p.2 = f.1 y := hp2
    rw [e1, e2, add_zero]
  obtain ⟨r₀, hr₀⟩ := exists_latZ_subset_of_mem_nhds z ϖ hz hϖ hϖ0 hW
  refine ⟨r₀, fun y l hl => ?_⟩
  by_cases hy : y ∈ tsupport f.1
  · exact hr₀ hl y hy
  by_cases hyl : y + l ∈ tsupport f.1
  · have := hr₀ ((latZ z (r₀ : ℤ)).sub.neg_mem hl) (y + l) hyl
    rw [add_neg_cancel_right] at this
    exact this.symm
  · rw [image_eq_zero_of_notMem_tsupport hy, image_eq_zero_of_notMem_tsupport hyl]

theorem exists_eq_sum_ind_of_invariant (L : COSub k d) (f : SchF k d V)
    (hf : ∀ y, ∀ l ∈ L.sub, f.1 (y + l) = f.1 y) :
    ∃ I : Finset ((Fin d → k) × V), f = ∑ p ∈ I, ind L p.1 p.2 := by
  classical
  have hK : IsCompact (tsupport f.1) := f.2.2
  obtain ⟨t, ht⟩ := hK.elim_finite_subcover (fun c : Fin d → k => {y | y - c ∈ L.sub})
    (fun c => (isClopen_coset L c).isOpen) (fun y _ => Set.mem_iUnion.2 ⟨y, by simp⟩)
  let mk : (Fin d → k) → (Fin d → k) ⧸ L.sub := QuotientAddGroup.mk
  have hmk : ∀ (q : (Fin d → k) ⧸ L.sub) (y : Fin d → k), y - Quotient.out q ∈ L.sub ↔ mk y = q := by
    intro q y
    have e : mk (Quotient.out q) = q := QuotientAddGroup.out_eq' q
    constructor
    · intro h
      rw [← e]
      exact (QuotientAddGroup.eq.2 (by simpa [sub_eq_add_neg, add_comm] using h)).symm
    · intro h
      have h' : mk (Quotient.out q) = mk y := e.trans h.symm
      simpa [sub_eq_add_neg, add_comm] using QuotientAddGroup.eq.1 h'
  let Q : Finset ((Fin d → k) ⧸ L.sub) := t.image mk
  let φ : ((Fin d → k) ⧸ L.sub) → (Fin d → k) × V := fun q => (Quotient.out q, f.1 (Quotient.out q))
  have hφ : Function.Injective φ := fun q q' h => by
    have h1 : Quotient.out q = Quotient.out q' := congrArg Prod.fst h
    rw [← QuotientAddGroup.out_eq' q, ← QuotientAddGroup.out_eq' q', h1]
  refine ⟨Q.image φ, Subtype.ext (funext fun y => ?_)⟩
  rw [Finset.sum_image hφ.injOn, Submodule.coe_sum, Finset.sum_apply]
  have hterm : ∀ q ∈ Q, ((ind L (φ q).1 (φ q).2 : SchF k d V) : (Fin d → k) → V) y =
      if mk y = q then f.1 y else 0 := by
    intro q _
    show (ind L (φ q).1 (φ q).2).1 y = _
    rw [ind_apply]
    by_cases h : mk y = q
    · have hm : y - Quotient.out q ∈ L.sub := (hmk q y).2 h
      rw [if_pos hm, if_pos h]
      have := hf (Quotient.out q) _ hm
      rw [add_sub_cancel] at this
      exact this.symm
    · rw [if_neg (fun hm => h ((hmk q y).1 hm)), if_neg h]
  rw [Finset.sum_congr rfl hterm, Finset.sum_ite_eq]
  split_ifs with hy
  · rfl
  · refine image_eq_zero_of_notMem_tsupport fun hyK => hy ?_
    obtain ⟨c, hct, hc⟩ := Set.mem_iUnion₂.1 (ht hyK)
    have hc' : y - c ∈ L.sub := hc
    have : mk y = mk c := (QuotientAddGroup.eq.2 (by simpa [sub_eq_add_neg, add_comm] using hc')).symm
    rw [this]
    exact Finset.mem_image_of_mem mk hct

theorem schF_eq_sum_ind (z : GL (Fin d) k) (ϖ : k)
    (hz : (z : Matrix (Fin d) (Fin d) k) = ϖ • (1 : Matrix (Fin d) (Fin d) k))
    (hϖ : ValuativeRel.valuation k ϖ < 1) (hϖ0 : ϖ ≠ 0) (f : SchF k d V) :
    ∃ r₀ : ℕ, ∀ r : ℕ, r₀ ≤ r → ∃ I : Finset ((Fin d → k) × V), f = ∑ p ∈ I, ind (latZ z (r : ℤ)) p.1 p.2 := by
  obtain ⟨r₀, hr₀⟩ := exists_latZ_invariant z ϖ hz hϖ hϖ0 f
  refine ⟨r₀, fun r hr => exists_eq_sum_ind_of_invariant _ f fun y l hl => hr₀ y l ?_⟩
  exact latZ_anti z ϖ hz hϖ hϖ0 _ _ (by exact_mod_cast hr) hl

end GlobalTheory.CompanionTheory.BZCore

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnipotentMapContinuousAdditiveStatement
section
noncomputable section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unipotent_map_continuous_additive : ∀ (D : D7) (n : ℕ) (nb : PositivityTheory.GramSchwartzFunctions.BC.hermA D n → GlobalTheory.StdUnn.G D n), PositivityTheory.PfSWUS.IsNMap nb → Continuous nb ∧ (∀ b c, nb (b + c) = nb b * nb c) ∧ ∀ γ ∈ PositivityTheory.GramSchwartzFunctions.BC.ratHerm D n, nb γ ∈ GlobalTheory.StdUnn.GF D n := by
  first | exact @GlobalTheory.CompanionTheory.SiegelUnip.nb_facts | exact GlobalTheory.CompanionTheory.SiegelUnip.nb_facts | (intros; apply GlobalTheory.CompanionTheory.SiegelUnip.nb_facts <;> assumption)
end
end

