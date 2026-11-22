import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0447
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.RealDescent.RealLeviDescent.Bundle0001
import CompanionTheory.RealGroups.DiscreteSeries.DiscreteSeriesClassification.DiscreteSeriesExhaustion.FarRegularity.LKTExists
import CompanionTheory.HarishChandraModules.LowKTypeMultiplicity.EigenspaceCyclicDensity.CreationOperators.DifferentialBoundedSupport
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0457
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0449
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0006
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.DeRhamJacobian.IsdRJ
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0244
import Development.WeilBound.CoreStatements.PlaceConnectedComponents.IsOpenQuotientMapArt0
import GroundTheory.LocalFields.Bundle0013
import GroundTheory.LocalFields.KroneckerWeber
import GroundTheory.PAdicHodge.FieldOfNormsCyclBase
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0107
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0716
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0327
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0435
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0411

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LatticeMaxEvenAlmostAll
section
open NumberField IsDedekindDomain Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet PositivityTheory.ThKR GlobalTheory.CompanionTheory.KFin
open Formalism.UG (cT)
open scoped TensorProduct

set_option linter.unusedSectionVars false

noncomputable section

namespace GlobalTheory.CompanionTheory.KFin.AE

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {v : HeightOneSpectrum (𝓞 F)}

theorem sigR_inclR (e : E) : sigR (Fv F v) σ (inclR (Fv F v) e) = inclR (Fv F v) (σ e) := rfl

theorem hR_apply (x y : Fin n → Fv F v ⊗[F] E) :
    hR (Fv F v) σ J x y = ∑ i, ∑ j, sigR (Fv F v) σ (x i) * inclR (Fv F v) (J i j) * y j := rfl

theorem sigR_sigR (hσ : ∀ e, σ (σ e) = e) (y : Fv F v ⊗[F] E) : sigR (Fv F v) σ (sigR (Fv F v) σ y) = y := by
  induction y with
  | zero => simp
  | tmul a b => simp [sigR, hσ]
  | add a b ha hb => rw [map_add, map_add, ha, hb]

theorem sigR_hR (hσ : ∀ e, σ (σ e) = e) (hJ : ∀ i j, σ (J j i) = J i j) (x y : Fin n → Fv F v ⊗[F] E) :
    sigR (Fv F v) σ (hR (Fv F v) σ J x y) = hR (Fv F v) σ J y x := by
  rw [hR_apply, hR_apply, Finset.sum_comm]
  simp only [map_sum, map_mul, sigR_sigR hσ, sigR_inclR]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [← hJ i j]
  ring

theorem hR_mem (hJv : ∀ i j, inclR (Fv F v) (J i j) ∈ intLoc F E v) {x y : Fin n → Fv F v ⊗[F] E}
    (hx : ∀ i, x i ∈ intLoc F E v) (hy : ∀ i, y i ∈ intLoc F E v) : hR (Fv F v) σ J x y ∈ intLoc F E v := by
  rw [hR_apply]
  exact sum_mem fun i _ => sum_mem fun j _ => mul_mem (mul_mem (sigR_mem_intLoc σ (hx i)) (hJv i j)) (hy j)

theorem hR_single (i : Fin n) (z : Fin n → Fv F v ⊗[F] E) :
    hR (Fv F v) σ J (Pi.single i 1) z = (J.map (inclR (F := F) (Fv F v)) *ᵥ z) i := by
  rw [hR_apply, Finset.sum_eq_single i]
  · simp [Matrix.mulVec, dotProduct]
  · intro j _ hj
    simp [Pi.single_apply, hj]
  · simp

theorem mem_of_hR_single (hdet : J.det ≠ 0) (hJi : ∀ i j, inclR (Fv F v) (J⁻¹ i j) ∈ intLoc F E v)
    {z : Fin n → Fv F v ⊗[F] E} (hz : ∀ i, hR (Fv F v) σ J (Pi.single i 1) z ∈ intLoc F E v) (a : Fin n) :
    z a ∈ intLoc F E v := by
  have e : J⁻¹.map (inclR (F := F) (Fv F v)) * J.map (inclR (F := F) (Fv F v)) = 1 := by
    rw [← Matrix.map_mul, Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.2 hdet), Matrix.map_one _ (map_zero _) (map_one _)]
  have hz' : z = J⁻¹.map (inclR (F := F) (Fv F v)) *ᵥ (J.map (inclR (F := F) (Fv F v)) *ᵥ z) := by
    rw [Matrix.mulVec_mulVec, e, Matrix.one_mulVec]
  obtain ⟨w, hw⟩ : ∃ w, w = J.map (inclR (F := F) (Fv F v)) *ᵥ z := ⟨_, rfl⟩
  have hw' : ∀ j, w j ∈ intLoc F E v := fun j => by rw [hw, ← hR_single (σ := σ)]; exact hz j
  rw [← hw] at hz'
  rw [hz']
  simp only [Matrix.mulVec, dotProduct]
  exact sum_mem fun j _ => mul_mem (hJi a j) (hw' j)

end GlobalTheory.CompanionTheory.KFin.AE

namespace GlobalTheory.CompanionTheory.KFin.AE

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {v : HeightOneSpectrum (𝓞 F)}

theorem single_mem_latLoc_std (i : Fin n) :
    (Pi.single i 1 : Fin n → Fv F v ⊗[F] E) ∈ latLoc F (stdLattice E n) v := by
  refine mem_latLoc_stdLattice.2 fun j => ?_
  by_cases h : j = i
  · subst h; simp only [Pi.single_eq_same]; exact one_mem _
  · rw [Pi.single_eq_of_ne h]; exact zero_mem _

theorem sum_single_smul (y : Fin n → Fv F v ⊗[F] E) : ∑ i, y i • (Pi.single i 1 : Fin n → Fv F v ⊗[F] E) = y := by
  funext j
  simp [Finset.sum_apply, Pi.single_apply]

theorem isLat_latLoc_std : IsLat (intLoc F E v) (latLoc F (stdLattice E n) v) := by
  constructor
  · refine Submodule.fg_def.2 ⟨Set.range fun i => (Pi.single i 1 : Fin n → Fv F v ⊗[F] E), Set.finite_range _,
      le_antisymm ?_ ?_⟩
    · rw [Submodule.span_le]
      rintro y ⟨i, rfl⟩
      exact single_mem_latLoc_std i
    · intro y hy
      have h := mem_latLoc_stdLattice.1 hy
      rw [← sum_single_smul y]
      refine sum_mem fun i _ => ?_
      have : y i • (Pi.single i 1 : Fin n → Fv F v ⊗[F] E) =
          (⟨y i, h i⟩ : intLoc F E v) • (Pi.single i 1 : Fin n → Fv F v ⊗[F] E) := rfl
      rw [this]
      exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_range_self i))
  · rw [eq_top_iff]
    intro y _
    rw [← sum_single_smul y]
    exact sum_mem fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span (single_mem_latLoc_std i))

end GlobalTheory.CompanionTheory.KFin.AE

namespace GlobalTheory.CompanionTheory.KFin.AE

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {v : HeightOneSpectrum (𝓞 F)}

theorem hR_self_eq (hσ : ∀ e, σ (σ e) = e) (hJ : ∀ i j, σ (J j i) = J i j) (x : Fin n → Fv F v ⊗[F] E) :
    hR (Fv F v) σ J x x = inclR (Fv F v) (2⁻¹ : E) * hR (Fv F v) σ J x x +
      sigR (Fv F v) σ (inclR (Fv F v) (2⁻¹ : E) * hR (Fv F v) σ J x x) := by
  have hs : σ (2⁻¹ : E) = 2⁻¹ := by rw [map_inv₀, map_ofNat]
  rw [map_mul, sigR_hR hσ hJ, sigR_inclR, hs, ← add_mul, ← map_add]
  have : (2⁻¹ : E) + 2⁻¹ = 1 := by norm_num
  rw [this, map_one, one_mul]

theorem isMaxEven_isAdapted_std (hσ : ∀ e, σ (σ e) = e) (hJ : IsHermND σ J)
    (hJv : ∀ i j, inclR (Fv F v) (J i j) ∈ intLoc F E v) (hJi : ∀ i j, inclR (Fv F v) (J⁻¹ i j) ∈ intLoc F E v)
    (h2 : inclR (Fv F v) (2⁻¹ : E) ∈ intLoc F E v) {r : ℕ} (x y : Fin r → Fin n → Fv F v ⊗[F] E)
    (hx : ∀ i a, x i a ∈ intLoc F E v) (hy : ∀ i a, y i a ∈ intLoc F E v) :
    IsMaxEven (sigR (Fv F v) σ) (intLoc F E v) (hR (Fv F v) σ J) (latLoc F (stdLattice E n) v) ∧
      IsAdapted (intLoc F E v) (hR (Fv F v) σ J) x y (latLoc F (stdLattice E n) v) := by
  have hint : ∀ a ∈ latLoc F (stdLattice E n) v, ∀ b ∈ latLoc F (stdLattice E n) v,
      hR (Fv F v) σ J a b ∈ intLoc F E v := fun a ha b hb =>
    hR_mem hJv (mem_latLoc_stdLattice.1 ha) (mem_latLoc_stdLattice.1 hb)
  refine ⟨⟨isLat_latLoc_std, ⟨hint, fun a ha => ⟨_, mul_mem h2 (hint a ha a ha), hR_self_eq hσ hJ.1 a⟩⟩, ?_⟩, ?_⟩
  · intro L' hL' hle z hz
    refine mem_latLoc_stdLattice.2 (mem_of_hR_single (σ := σ) hJ.2 hJi fun i => ?_)
    exact hL'.1 _ (hle (single_mem_latLoc_std i)) _ hz
  · intro z
    simp only [mem_latLoc_stdLattice]
    have hc : ∀ (c d : Fin r → Fv F v ⊗[F] E) (a : Fin n),
        (z - ∑ i, c i • x i - ∑ i, d i • y i) a = z a - ∑ i, c i * x i a - ∑ i, d i * y i a := by
      intro c d a
      simp [Finset.sum_apply]
    constructor
    · intro hz
      have h1 : ∀ i, hR (Fv F v) σ J (x i) z ∈ intLoc F E v := fun i => hR_mem hJv (hx i) hz
      have h3 : ∀ i, hR (Fv F v) σ J (y i) z ∈ intLoc F E v := fun i => hR_mem hJv (hy i) hz
      refine ⟨h1, h3, fun a => ?_⟩
      rw [hc]
      exact sub_mem (sub_mem (hz a) (sum_mem fun i _ => mul_mem (h3 i) (hx i a)))
        (sum_mem fun i _ => mul_mem (h1 i) (hy i a))
    · rintro ⟨h1, h3, hw⟩ a
      have := hw a
      rw [hc] at this
      have e : z a = (z a - ∑ i, hR (Fv F v) σ J (y i) z * x i a - ∑ i, hR (Fv F v) σ J (x i) z * y i a) +
          ∑ i, hR (Fv F v) σ J (y i) z * x i a + ∑ i, hR (Fv F v) σ J (x i) z * y i a := by ring
      rw [e]
      exact add_mem (add_mem this (sum_mem fun i _ => mul_mem (h3 i) (hx i a)))
        (sum_mem fun i _ => mul_mem (h1 i) (hy i a))

end GlobalTheory.CompanionTheory.KFin.AE

namespace GlobalTheory.CompanionTheory.KFin.AE

theorem exists_lattice_maxEven_adapted : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {r : ℕ} {X Y : Matrix (Fin n) (Fin r) E}, IsCMExt F E σ → IsHermND σ J → IsWittFrame σ J X Y → ∃ (L : Submodule (𝓞 E) (Fin n → E)) (_ : Submodule.IsLattice E L), ∀ᶠ v in Filter.cofinite, IsMaxEven (sigR (Fv F v) σ) (intLoc F E v) (hR (Fv F v) σ J) (latLoc F L v) ∧ IsAdapted (intLoc F E v) (hR (Fv F v) σ J) (colV v X) (colV v Y) (latLoc F L v) := by
  intro F E _ _ _ _ _ σ n J r X Y hcm hJ _hW
  have hσ : ∀ e, σ (σ e) = e := fun e => by
    obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
    exact τ.injective (by rw [hcm.2.2.2, hcm.2.2.2, star_star])
  refine ⟨stdLattice E n, isLattice_stdLattice, ?_⟩
  filter_upwards [Filter.eventually_all.2 fun i => Filter.eventually_all.2 fun j => eventually_one_tmul_mem_intLoc (F := F) (J i j),
    Filter.eventually_all.2 fun i => Filter.eventually_all.2 fun j => eventually_one_tmul_mem_intLoc (F := F) (J⁻¹ i j),
    eventually_one_tmul_mem_intLoc (F := F) (2⁻¹ : E),
    Filter.eventually_all.2 fun i => Filter.eventually_all.2 fun a => eventually_one_tmul_mem_intLoc (F := F) (X a i),
    Filter.eventually_all.2 fun i => Filter.eventually_all.2 fun a => eventually_one_tmul_mem_intLoc (F := F) (Y a i)]
    with v h1 h2 h3 h4 h5
  exact isMaxEven_isAdapted_std hσ hJ h1 h2 h3 (colV v X) (colV v Y) h4 h5

end GlobalTheory.CompanionTheory.KFin.AE
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LeviAdjointOnChains
section
open Finset PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD GlobalTheory.CompanionTheory.LvChain
open CompanionTheory.D.LK (Pos)
open scoped InnerProductSpace

noncomputable section

namespace GlobalTheory.CompanionTheory.LvChainAdj

variable {n : ℕ} {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]

def ip (x z : Cq n V) : ℂ := ∑ A, ⟪x A, z A⟫_ℂ

theorem sgL_conj (i : Lt n) (A : Finset (Lt n)) : (starRingEnd ℂ) (sgL i A) = sgL i A := by
  simp [PositivityTheory.RgBcC.RealD.sgL]

theorem sgL_erase_self (i : Lt n) {A : Finset (Lt n)} (h : i ∈ A) : sgL i (A.erase i) = sgL i A := by
  rw [GlobalTheory.CompanionTheory.LvChain.sgL_erase i h, GlobalTheory.CompanionTheory.LvChain.twL_self, one_mul]

theorem ip_creL (i : Lt n) (x z : Cq n V) : ip (creL i x) z = ip x (annL i z) := by
  classical
  have hL : GlobalTheory.CompanionTheory.LvChainAdj.ip (PositivityTheory.RgBcC.RealD.creL i x) z =
      ∑ A ∈ Finset.univ.filter (fun A => i ∈ A),
        PositivityTheory.RgBcC.RealD.sgL i A * ⟪x (A.erase i), z A⟫_ℂ := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun A _ => ?_
    rw [GlobalTheory.CompanionTheory.LvChain.creL_apply]
    split_ifs <;> simp [inner_smul_left, GlobalTheory.CompanionTheory.LvChainAdj.sgL_conj] <;> ring
  have hR : GlobalTheory.CompanionTheory.LvChainAdj.ip x (PositivityTheory.RgBcC.RealD.annL i z) =
      ∑ B ∈ Finset.univ.filter (fun B => i ∉ B),
        PositivityTheory.RgBcC.RealD.sgL i B * ⟪x B, z (insert i B)⟫_ℂ := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun B _ => ?_
    rw [GlobalTheory.CompanionTheory.LvChain.annL_apply]
    split_ifs <;> simp [inner_smul_right]
  rw [hL, hR]
  refine Finset.sum_nbij' (fun A => A.erase i) (fun B => insert i B) ?_ ?_ ?_ ?_ ?_
  · intro A _
    simp
  · intro B _
    simp
  · intro A hA
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hA
    exact Finset.insert_erase hA
  · intro B hB
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hB
    exact Finset.erase_insert hB
  · intro A hA
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hA
    rw [GlobalTheory.CompanionTheory.LvChainAdj.sgL_erase_self i hA, Finset.insert_erase hA]

theorem ip_conj (x z : Cq n V) : (starRingEnd ℂ) (ip x z) = ip z x := by
  unfold GlobalTheory.CompanionTheory.LvChainAdj.ip
  rw [map_sum]
  exact Finset.sum_congr rfl fun A _ => inner_conj_symm (z A) (x A)

theorem ip_annL (i : Lt n) (x z : Cq n V) : ip (annL i x) z = ip x (creL i z) := by
  rw [← GlobalTheory.CompanionTheory.LvChainAdj.ip_conj z (PositivityTheory.RgBcC.RealD.annL i x), ← GlobalTheory.CompanionTheory.LvChainAdj.ip_creL i z x,
    GlobalTheory.CompanionTheory.LvChainAdj.ip_conj]

theorem ip_creL_annL (i k : Lt n) (x z : Cq n V) :
    ip ((creL k * annL i : Module.End ℂ (Cq n V)) x) z = ip x ((creL i * annL k : Module.End ℂ (Cq n V)) z) := by
  rw [Module.End.mul_apply, Module.End.mul_apply, GlobalTheory.CompanionTheory.LvChainAdj.ip_creL,
    GlobalTheory.CompanionTheory.LvChainAdj.ip_annL]

theorem ip_add_left (x y z : Cq n V) : ip (x + y) z = ip x z + ip y z := by
  unfold GlobalTheory.CompanionTheory.LvChainAdj.ip
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun A _ => by rw [← inner_add_left]; rfl

theorem ip_add_right (x y z : Cq n V) : ip x (y + z) = ip x y + ip x z := by
  unfold GlobalTheory.CompanionTheory.LvChainAdj.ip
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun A _ => by rw [← inner_add_right]; rfl

theorem ip_smul_left (c : ℂ) (x z : Cq n V) : ip (c • x) z = (starRingEnd ℂ) c * ip x z := by
  unfold GlobalTheory.CompanionTheory.LvChainAdj.ip
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun A _ => by rw [← inner_smul_left]; rfl

theorem ip_smul_right (c : ℂ) (x z : Cq n V) : ip x (c • z) = c * ip x z := by
  unfold GlobalTheory.CompanionTheory.LvChainAdj.ip
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun A _ => by rw [← inner_smul_right]; rfl

theorem ip_zero_left (z : Cq n V) : ip (0 : Cq n V) z = 0 := by
  unfold GlobalTheory.CompanionTheory.LvChainAdj.ip
  exact Finset.sum_eq_zero fun A _ => by
    rw [show (0 : PositivityTheory.RgBcC.RealD.Cq n V) A = 0 from rfl, inner_zero_left]

theorem ip_zero_right (x : Cq n V) : ip x (0 : Cq n V) = 0 := by
  unfold GlobalTheory.CompanionTheory.LvChainAdj.ip
  exact Finset.sum_eq_zero fun A _ => by
    rw [show (0 : PositivityTheory.RgBcC.RealD.Cq n V) A = 0 from rfl, inner_zero_right]

theorem ip_sum_left {ι : Type} (s : Finset ι) (f : ι → Cq n V) (z : Cq n V) :
    ip (∑ a ∈ s, f a) z = ∑ a ∈ s, ip (f a) z := by
  classical
  refine Finset.induction_on s ?_ ?_
  · rw [Finset.sum_empty, Finset.sum_empty, GlobalTheory.CompanionTheory.LvChainAdj.ip_zero_left]
  · intro a s ha ih
    rw [Finset.sum_insert ha, Finset.sum_insert ha, GlobalTheory.CompanionTheory.LvChainAdj.ip_add_left, ih]

theorem ip_sum_right {ι : Type} (s : Finset ι) (x : Cq n V) (f : ι → Cq n V) :
    ip x (∑ a ∈ s, f a) = ∑ a ∈ s, ip x (f a) := by
  classical
  refine Finset.induction_on s ?_ ?_
  · rw [Finset.sum_empty, Finset.sum_empty, GlobalTheory.CompanionTheory.LvChainAdj.ip_zero_right]
  · intro a s ha ih
    rw [Finset.sum_insert ha, Finset.sum_insert ha, GlobalTheory.CompanionTheory.LvChainAdj.ip_add_right, ih]

theorem adCL_conj (p q : Fin n) (l k : Lt n) : (starRingEnd ℂ) (adCL false p q l k) = adCL false p q l k := by
  unfold PositivityTheory.RgBcC.RealD.adCL
  split_ifs <;> simp

theorem adCL_swap (p q : Fin n) (l k : Lt n) : adCL false p q l k = adCL false q p k l := by
  unfold PositivityTheory.RgBcC.RealD.adCL
  simp only [Bool.false_xor, Bool.false_bne, Prod.ext_iff]
  congr 1
  · exact if_congr
      ⟨fun ⟨h1, h2, h3, h4⟩ => ⟨h3.symm, h2.symm, h1.symm, h4.symm⟩,
        fun ⟨h1, h2, h3, h4⟩ => ⟨h3.symm, h2.symm, h1.symm, h4.symm⟩⟩ rfl rfl
  · exact if_congr
      ⟨fun ⟨h1, h2, h3, h4⟩ => ⟨h4, h2.symm, h3.symm, h1⟩,
        fun ⟨h1, h2, h3, h4⟩ => ⟨h4, h2.symm, h3.symm, h1⟩⟩ rfl rfl

theorem inUU_iff_of_adCL {lev : Fin n → ℕ} {p q : Fin n} (h : lev p = lev q) {l k : Lt n}
    (hc : adCL false p q l k ≠ 0) : inUU lev l ↔ inUU lev k := by
  unfold PositivityTheory.RgBcC.RealD.adCL at hc
  unfold PositivityTheory.RgBcC.RealD.inUU
  split_ifs at hc with h1 h2 h2
  · exact absurd (sub_self _) hc
  · obtain ⟨hq, -, hk⟩ := h1
    simp [hk, h, hq]
  · obtain ⟨hp, -, hk⟩ := h2
    simp [hk, hp, h]
  · exact absurd (sub_self _) hc

theorem ip_term {lev : Fin n → ℕ} {p q : Fin n} (h : lev p = lev q) (l k : Lt n) (x z : Cq n V) :
    ip ((if inUU lev l then adCL false p q l k • (creL k * annL l) else 0 : Module.End ℂ (Cq n V)) x) z =
      ip x ((if inUU lev k then adCL false q p k l • (creL l * annL k) else 0 : Module.End ℂ (Cq n V)) z) := by
  rw [← GlobalTheory.CompanionTheory.LvChainAdj.adCL_swap p q l k]
  by_cases hc : PositivityTheory.RgBcC.RealD.adCL false p q l k = 0
  · simp only [hc, zero_smul, ite_self, LinearMap.zero_apply, GlobalTheory.CompanionTheory.LvChainAdj.ip_zero_left,
      GlobalTheory.CompanionTheory.LvChainAdj.ip_zero_right]
  · have hiff := GlobalTheory.CompanionTheory.LvChainAdj.inUU_iff_of_adCL h hc
    by_cases hl : PositivityTheory.RgBcC.RealD.inUU lev l
    · rw [if_pos hl, if_pos (hiff.mp hl), LinearMap.smul_apply, LinearMap.smul_apply,
        GlobalTheory.CompanionTheory.LvChainAdj.ip_smul_left, GlobalTheory.CompanionTheory.LvChainAdj.ip_smul_right, GlobalTheory.CompanionTheory.LvChainAdj.adCL_conj,
        GlobalTheory.CompanionTheory.LvChainAdj.ip_creL_annL]
    · rw [if_neg hl, if_neg (mt hiff.mpr hl), LinearMap.zero_apply, LinearMap.zero_apply,
        GlobalTheory.CompanionTheory.LvChainAdj.ip_zero_left, GlobalTheory.CompanionTheory.LvChainAdj.ip_zero_right]

theorem ip_adLL {lev : Fin n → ℕ} {p q : Fin n} (h : lev p = lev q) (x z : Cq n V) :
    ip (adLL lev false p q x) z = ip x (adLL lev false q p z) := by
  unfold PositivityTheory.RgBcC.RealD.adLL
  simp only [LinearMap.sum_apply, GlobalTheory.CompanionTheory.LvChainAdj.ip_sum_left, GlobalTheory.CompanionTheory.LvChainAdj.ip_sum_right]
  conv_lhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
  exact GlobalTheory.CompanionTheory.LvChainAdj.ip_term h l k x z

theorem ip_liftL {E1 E2 : Fin n → Fin n → Module.End ℂ V}
    (hU : ∀ a b (x y : V), ⟪kA E1 E2 a b x, y⟫_ℂ = ⟪x, kA E1 E2 b a y⟫_ℂ) (p q : Fin n) (x z : Cq n V) :
    ip (liftL n (kA E1 E2 p q) x) z = ip x (liftL n (kA E1 E2 q p) z) := by
  unfold GlobalTheory.CompanionTheory.LvChainAdj.ip
  exact Finset.sum_congr rfl fun A _ => hU p q (x A) (z A)

theorem Lv_adjoint : ∀ (n : ℕ) (lev : Fin n → ℕ) (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (E1 E2 : Fin n → Fin n → Module.End ℂ V),
    (∀ a b (x y : V), ⟪kA E1 E2 a b x, y⟫_ℂ = ⟪x, kA E1 E2 b a y⟫_ℂ) → ∀ p q : Fin n, lev p = lev q → ∀ x z : Cq n V,
      ∑ A, ⟪Lv lev E1 E2 p q x A, z A⟫_ℂ = ∑ A, ⟪x A, Lv lev E1 E2 q p z A⟫_ℂ := by
  intro n lev V _ _ E1 E2 hU p q h x z
  show GlobalTheory.CompanionTheory.LvChainAdj.ip _ _ = GlobalTheory.CompanionTheory.LvChainAdj.ip _ _
  unfold GlobalTheory.CompanionTheory.LvChain.Lv
  rw [LinearMap.add_apply, LinearMap.add_apply, GlobalTheory.CompanionTheory.LvChainAdj.ip_add_left,
    GlobalTheory.CompanionTheory.LvChainAdj.ip_add_right, GlobalTheory.CompanionTheory.LvChainAdj.ip_liftL hU,
    GlobalTheory.CompanionTheory.LvChainAdj.ip_adLL h]

end GlobalTheory.CompanionTheory.LvChainAdj
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LeviRaisingKillsTopChain
section
open Finset PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD GlobalTheory.CompanionTheory.LvChain
open CompanionTheory.D.LK (Pos)
open scoped InnerProductSpace

noncomputable section

namespace GlobalTheory.CompanionTheory.LvChain

theorem adCL_mem_omU {n : ℕ} {lev : Fin n → ℕ} {p q : Fin n} (hpq : p < q) (hl : lev p = lev q) {l k : Lt n}
    (hc : adCL false p q l k ≠ 0) (hm : l ∈ omU lev) : k ∈ omU lev ∧ k ≠ l := by
  have hcase : (q = l.2.1.1 ∧ k.1 = xor false l.1 ∧ k.2.1 = (p, l.2.1.2)) ∨
      (l.2.1.2 = p ∧ k.1 = xor false l.1 ∧ k.2.1 = (l.2.1.1, q)) := by
    by_contra hn
    rw [not_or] at hn
    exact hc (by simp only [adCL, if_neg hn.1, if_neg hn.2, sub_self])
  obtain ⟨h1, h2⟩ : l.1 = false ∧ lev l.2.1.1 < lev l.2.1.2 := (mem_filter.1 hm).2
  have hne : p ≠ q := ne_of_lt hpq
  rcases hcase with ⟨e1, e0, e2⟩ | ⟨e1, e0, e2⟩
  · refine ⟨mem_filter.2 ⟨mem_univ _, ?_, ?_⟩, fun e => ?_⟩
    · rw [e0, h1]; rfl
    · rw [e2]; show lev p < lev l.2.1.2; rw [hl, e1]; exact h2
    · rw [e] at e2; exact hne (e1.trans (congrArg Prod.fst e2)).symm
  · refine ⟨mem_filter.2 ⟨mem_univ _, ?_, ?_⟩, fun e => ?_⟩
    · rw [e0, h1]; rfl
    · rw [e2]; show lev l.2.1.1 < lev q; rw [← hl, ← e1]; exact h2
    · rw [e] at e2; exact hne (e1.symm.trans (congrArg Prod.snd e2))

theorem Lv_single_omU : ∀ (n : ℕ) (lev : Fin n → ℕ) (V : Type) [AddCommGroup V] [Module ℂ V]
    (E1 E2 : Fin n → Fin n → Module.End ℂ V) (u : V),
    (∀ a b : Fin n, a < b → kA E1 E2 a b u = 0) → ∀ p q : Fin n, p < q → lev p = lev q →
      Lv lev E1 E2 p q (Pi.single (omU lev) u : Cq n V) = 0 := by
  intro n lev V _ _ E1 E2 u hu p q hpq hl
  have h1 : liftL n (kA E1 E2 p q) (Pi.single (omU lev) u : Cq n V) = 0 := by
    funext A
    rw [liftL_apply]
    by_cases e : A = omU lev
    · subst e
      rw [Pi.single_eq_same]
      exact hu p q hpq
    · rw [Pi.single_eq_of_ne e, map_zero]
      rfl
  have h2 : adLL lev false p q (Pi.single (omU lev) u : Cq n V) = 0 := by
    simp only [adLL, LinearMap.sum_apply]
    refine Finset.sum_eq_zero fun l _ => Finset.sum_eq_zero fun k _ => ?_
    split_ifs with hS
    swap
    · rfl
    by_cases hc : adCL false p q l k = 0
    · rw [hc, zero_smul]; rfl
    suffices h : creL k (annL l (Pi.single (omU lev) u : Cq n V)) = 0 by
      rw [LinearMap.smul_apply, Module.End.mul_apply, h, smul_zero]
    funext B
    by_contra h
    obtain ⟨-, h3⟩ := creL_ne h
    obtain ⟨-, h4⟩ := annL_ne h3
    have e : insert l (B.erase k) = omU lev := by
      by_contra h'
      exact h4 (Pi.single_eq_of_ne h' _)
    have hm : l ∈ omU lev := e ▸ mem_insert_self _ _
    obtain ⟨hk, hkl⟩ := adCL_mem_omU hpq hl hc hm
    rw [← e] at hk
    rcases mem_insert.1 hk with h5 | h5
    · exact hkl h5
    · exact notMem_erase _ _ h5
  show liftL n (kA E1 E2 p q) _ + adLL lev false p q _ = 0
  rw [h1, h2, add_zero]

end GlobalTheory.CompanionTheory.LvChain
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalEmbeddingRangeEqFieldStatement
section
noncomputable section
open NumberField IsDedekindDomain Neutral.B1 Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations
open GlobalTheory.HeckeGal GlobalTheory.Pst GlobalTheory.TripleGal GlobalTheory.CompanionTheory.LTHodge
open scoped Classical
open ValuativeRel GroundTheory.LocalField GroundTheory.LocalField.FormalGroup
open scoped GroundTheory.PAdicHodge.CyclNorms

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_embedding_range_eq_field : ∀ {l : ℕ} [Fact l.Prime] {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] {Gw : Subgroup (Ω ≃ₐ[E] Ω)}
    {O : Type} [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l E Ω Gw O)
    (w : HeightOneSpectrum (𝓞 E)) (φ : w.adicCompletion E →+* Om l), Continuous φ →
    (∀ y : E, φ (algebraMap E (w.adicCompletion E) y) = Bw.j (algebraMap E Ω y)) →
    Set.range φ = (Bw.Kw.1 : Set (Om l)) := by
  first | exact @GlobalTheory.CompanionTheory.LTHodge.CompletionRange.range_eq_Kw | exact GlobalTheory.CompanionTheory.LTHodge.CompletionRange.range_eq_Kw | (intros; apply GlobalTheory.CompanionTheory.LTHodge.CompletionRange.range_eq_Kw <;> assumption)
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalGlobalArtinCompatibleStatement
section
noncomputable section
open NumberField IsDedekindDomain Neutral.B1 Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations
open GlobalTheory.HeckeGal GlobalTheory.Pst GlobalTheory.TripleGal GlobalTheory.CompanionTheory.LTHodge
open scoped Classical
open ValuativeRel GroundTheory.LocalField GroundTheory.LocalField.FormalGroup
open scoped GroundTheory.PAdicHodge.CyclNorms

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_global_artin_compatible : ∀ {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (w : HeightOneSpectrum (𝓞 E)) {Ωv : Type} [Field Ωv] [Algebra (w.adicCompletion E) Ωv]
    [IsSepClosure (w.adicCompletion E) Ωv] (j : Ω →+* Ωv),
    (∀ y : E, j (algebraMap E Ω y) = algebraMap (w.adicCompletion E) Ωv (algebraMap E (w.adicCompletion E) y)) →
    ∀ (a : (w.adicCompletion E)ˣ) (σ : G E Ω) (g : Ωv ≃ₐ[w.adicCompletion E] Ωv),
    (∀ x : Ω, g (j x) = j (σ x)) →
    (∀ (y : Ωv) (hy : y ∈ maximalAbelianExtension (w.adicCompletion E) Ωv),
      ((localArtinMap (w.adicCompletion E) Ωv a ⟨y, hy⟩ : maximalAbelianExtension (w.adicCompletion E) Ωv) : Ωv) = g y) →
    ∀ (L : IntermediateField E Ω) [FiniteDimensional E L] [IsAbelianGalois E L],
    PositivityTheory.FamInh.res L (toAb E Ω σ) = PositivityTheory.FamInh.res L (PositivityTheory.FamInh.art0 E Ω (localIdele E w a)) := by
  first | exact @GlobalTheory.CompanionTheory.LTLink.local_restriction_abelianization_artin | exact GlobalTheory.CompanionTheory.LTLink.local_restriction_abelianization_artin | (intros; apply GlobalTheory.CompanionTheory.LTLink.local_restriction_abelianization_artin <;> assumption)
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocallyConstantFiniteBallSumStatement
section
open Matrix GlobalTheory.PRep GlobalTheory.BZMir GlobalTheory.SplitWeil GlobalTheory.CompanionTheory.MirFourier GlobalTheory.CompanionTheory.MirLevi
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.locally_constant_finite_ball_sum : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (E : Type) [AddCommGroup E] [Module ℂ E] (φ : (Fin n → k) → E) (s S : kˣ), (∀ v a : Fin n → k, Multiplicative.ofAdd a ∈ polyBall (k := k) n s → φ (v + a) = φ v) → (∀ v : Fin n → k, φ v ≠ 0 → Multiplicative.ofAdd v ∈ polyBall (k := k) n S) → ∃ R : Finset (Fin n → k), ∀ v : Fin n → k, φ v = ∑ x ∈ R, @ite _ (Multiplicative.ofAdd (v - x) ∈ polyBall (k := k) n s) (Classical.propDecidable _) (φ x) 0 := by
  first | exact @GlobalTheory.CompanionTheory.MirFourier.exists_finset_eq_sum_polyBall_translates | exact GlobalTheory.CompanionTheory.MirFourier.exists_finset_eq_sum_polyBall_translates | (intros; apply GlobalTheory.CompanionTheory.MirFourier.exists_finset_eq_sum_polyBall_translates <;> assumption)
end

