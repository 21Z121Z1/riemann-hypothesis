import Mathlib
import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.WeakApproximationFinitePlace
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsRadNMulLevM
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0678
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2023
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMulRightInvariantHaarAdelicUnitaryGroupHermiti
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0429
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0042
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0483
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0471
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0498
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0477
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0460
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0814
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0470
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0481
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0463
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0540
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0788
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0800
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0799
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0801
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0811
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0047
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0812
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0572
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0813
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IwahoriFactorisation.StrictDominance.SatakeSocle.SocleOne
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0598

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsRightInvariantHaarLevi
section
open scoped Matrix NNReal ENNReal TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.CompanionTheory.QKAvg
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CompanionTheory.QKAvg

variable {D : D7} {B W : HSp D} {t : ℕ} (d : HypDec B W t)

def levPair : GA D W × GL (Fin t) (AE D) →* levM d where
  toFun p := ⟨⟨d.emb0 p.1 * d.levi p.2, mul_mem (GlobalTheory.GodementSectionReduction.wittCoreEmbedding_mem_isotropicStabilizer d _) (GlobalTheory.RegSW.levi_mem d _)⟩, p.1, p.2, rfl⟩
  map_one' := Subtype.ext (Subtype.ext (by simp))
  map_mul' p q := Subtype.ext (Subtype.ext (by
    show d.emb0 (p.1 * q.1) * d.levi (p.2 * q.2) = d.emb0 p.1 * d.levi p.2 * (d.emb0 q.1 * d.levi q.2)
    rw [map_mul, map_mul]
    calc d.emb0 p.1 * d.emb0 q.1 * (d.levi p.2 * d.levi q.2)
        = d.emb0 p.1 * (d.emb0 q.1 * d.levi p.2) * d.levi q.2 := by group
      _ = d.emb0 p.1 * (d.levi p.2 * d.emb0 q.1) * d.levi q.2 := by rw [d.wittHyperbolic_anisotropic_commute_levi]
      _ = _ := by group))

theorem coe_levPair (p : GA D W × GL (Fin t) (AE D)) :
    (((levPair d p : levM d) : GlobalTheory.RegSW.stab d) : GA D B) = d.emb0 p.1 * d.levi p.2 := rfl

theorem mt_eq_of_levPair (p : GA D W × GL (Fin t) (AE D)) :
    d.p0 ⬝ (mt B (((levPair d p : levM d) : GlobalTheory.RegSW.stab d) : GA D B) ⬝ d.j0) = mt W p.1 := by
  rw [coe_levPair, mt_mul, Matrix.mul_assoc, d.wittDecomp_levi_inclAnisotropic, d.wittDecomp_anisotropicEmbedding_inclAnisotropic, cancel₂ d.p0_j0, Matrix.one_mul]

theorem onX_levPair (p : GA D W × GL (Fin t) (AE D)) :
    GlobalTheory.RegSW.onX d ((levPair d p : levM d) : GlobalTheory.RegSW.stab d) = p.2 := by
  have h : mt B (((levPair d p : levM d) : GlobalTheory.RegSW.stab d) : GA D B) ⬝ d.jX = d.jX ⬝ p.2.1 := by
    rw [coe_levPair, mt_mul, Matrix.mul_assoc, d.levi_jX, ← Matrix.mul_assoc, d.wittDecomp_anisotropicEmbedding_inclX]
  exact Units.ext ((GlobalTheory.RegSW.eq_of_mul_jX d (GlobalTheory.RegSW.mul_jX d _)).trans (GlobalTheory.RegSW.eq_of_mul_jX d h).symm)

theorem levPair_bijective : Function.Bijective (levPair d) := by
  constructor
  · intro p q h
    refine Prod.ext (mt_injective W ?_) ?_
    · rw [← mt_eq_of_levPair d p, ← mt_eq_of_levPair d q, h]
    · rw [← onX_levPair d p, ← onX_levPair d q, h]
  · rintro ⟨⟨q, hq⟩, g, a, e⟩
    exact ⟨(g, a), Subtype.ext (Subtype.ext e.symm)⟩

def levEquiv : (GA D W × GL (Fin t) (AE D)) ≃* levM d := MulEquiv.ofBijective (levPair d) (levPair_bijective d)

theorem continuous_levEquiv : Continuous (levEquiv d) := by
  have := isTopologicalRing_tens (F := D.host.F) (E := D.host.E) (R := AF D.host.F)
  obtain ⟨-, -, -, -, h5, -⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D B
  have h : Continuous fun p : GA D W × GL (Fin t) (AE D) => d.emb0 p.1 * d.levi p.2 :=
    (d.continuous_embed.comp continuous_fst).mul (d.continuous_levi.comp continuous_snd)
  exact (h.subtype_mk _).subtype_mk _

theorem continuous_levEquiv_symm : Continuous (levEquiv d).symm := by
  have := isTopologicalRing_tens (F := D.host.F) (E := D.host.E) (R := AF D.host.F)
  have hv : Continuous fun m : levM d => ((m : GlobalTheory.RegSW.stab d) : GA D B) :=
    continuous_subtype_val.comp continuous_subtype_val
  refine Continuous.prodMk (continuous_of_mt W ?_) ?_
  · have hc : Continuous fun m : levM d => d.p0 ⬝ (mt B ((m : GlobalTheory.RegSW.stab d) : GA D B) ⬝ d.j0) :=
      continuous_const.matrix_mul (((continuous_mt B).comp hv).matrix_mul continuous_const)
    refine hc.congr fun m => ?_
    have := mt_eq_of_levPair d ((levEquiv d).symm m)
    rwa [show levPair d ((levEquiv d).symm m) = m from (levEquiv d).apply_symm_apply m] at this
  · refine ((GlobalTheory.RegSW.continuous_onX d).comp continuous_subtype_val).congr fun m => ?_
    have := onX_levPair d ((levEquiv d).symm m)
    rwa [show levPair d ((levEquiv d).symm m) = m from (levEquiv d).apply_symm_apply m] at this

end GlobalTheory.CompanionTheory.QKAvg

theorem GlobalTheory.CompanionTheory.QKAvg.exists_haar_of_prod {G₁ G₂ M : Type} [Group G₁] [Group G₂] [Group M] [TopologicalSpace G₁]
    [TopologicalSpace G₂] [TopologicalSpace M] [IsTopologicalGroup G₁] [IsTopologicalGroup G₂] [IsTopologicalGroup M]
    [LocallyCompactSpace G₁] [LocallyCompactSpace G₂] [SecondCountableTopology G₁] [SecondCountableTopology G₂]
    [T2Space G₂] [MeasurableSpace G₁] [BorelSpace G₁] [MeasurableSpace M] [BorelSpace M]
    (e : (G₁ × G₂) ≃* M) (he : Continuous e) (he' : Continuous e.symm)
    (h₁ : ∀ μ : Measure G₁, μ.IsHaarMeasure → μ.IsMulRightInvariant)
    (h₂ : ∀ a : G₂, Measure.modularCharacterFun a = 1) :
    ∃ νM : Measure M, νM.IsHaarMeasure ∧ νM.IsMulRightInvariant := by
  borelize G₂
  haveI hr1 : (Measure.haar : Measure G₁).IsMulRightInvariant := h₁ _ inferInstance
  haveI hr2 : (Measure.haar : Measure G₂).IsMulRightInvariant := GlobalTheory.ParAvg.isMulRightInvariant_of_modular _ h₂
  obtain ⟨ν, hνH, hνR⟩ : ∃ ν : Measure (G₁ × G₂), ν.IsHaarMeasure ∧ ν.IsMulRightInvariant :=
    ⟨(Measure.haar : Measure G₁).prod Measure.haar, inferInstance, inferInstance⟩
  refine ⟨Measure.map e ν, MulEquiv.isHaarMeasure_map ν e he he', ⟨fun m => ?_⟩⟩
  obtain ⟨p, rfl⟩ := e.surjective m
  rw [Measure.map_map (measurable_mul_const _) he.measurable]
  have h : (fun x => x * e p) ∘ e = e ∘ fun x => x * p := by
    funext x; simp [map_mul]
  rw [h, ← Measure.map_map he.measurable (measurable_mul_const _), map_mul_right_eq_self]

set_option synthInstance.maxHeartbeats 400000 in

theorem GlobalTheory.CompanionTheory.QKAvg.top_GL (D : D7) (t : ℕ) : LocallyCompactSpace (GL (Fin t) (AE D)) ∧
    SecondCountableTopology (GL (Fin t) (AE D)) ∧ T2Space (GL (Fin t) (AE D)) := by
  obtain ⟨-, m2, m3, m4, -⟩ := lattice_Mx D t t
  haveI : LocallyCompactSpace (Mx D t t)ᵐᵒᵖ := MulOpposite.opHomeomorph.symm.isClosedEmbedding.locallyCompactSpace
  haveI : SecondCountableTopology (Mx D t t)ᵐᵒᵖ := MulOpposite.opHomeomorph.symm.secondCountableTopology
  haveI : T2Space (Mx D t t)ᵐᵒᵖ := MulOpposite.opHomeomorph.symm.isEmbedding.t2Space
  haveI : T1Space (Mx D t t) := @T2Space.t1Space _ _ m4
  exact ⟨(Units.isClosedEmbedding_embedProduct (α := Mx D t t)).locallyCompactSpace,
    (Units.isEmbedding_embedProduct (M := Mx D t t)).secondCountableTopology,
    (Units.isEmbedding_embedProduct (M := Mx D t t)).t2Space⟩

theorem GlobalTheory.CompanionTheory.QKAvg.exists_levM_haar : ∀ (D : D7) (B W : HSp D) (t : ℕ) (d : HypDec B W t) [LocallyCompactSpace (levM d)],
    ∃ νM : Measure (levM d), νM.IsHaarMeasure ∧ νM.IsMulRightInvariant := by
  intro D B W t d _
  obtain ⟨g1, g2, g3, g4, g5, -, -⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D W
  obtain ⟨l1, l2, l3⟩ := GlobalTheory.CompanionTheory.QKAvg.top_GL D t
  exact GlobalTheory.CompanionTheory.QKAvg.exists_haar_of_prod (levEquiv d) (continuous_levEquiv d) (continuous_levEquiv_symm d)
    (GlobalTheory.AdelicPointsUnimod.isMulRightInvariant_of_isHaarMeasure D W) (GlobalTheory.T.modularCharacter_adelic_GL_eq_one D t)
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FibreFunctionLocallyConstantCompact
section
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.Rodier GlobalTheory.CompanionTheory.BZPsiPG
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.CompanionTheory.BZPsiPG.FibCompact

theorem exists_right_invariant {G Z : Type} [Group G] [AddCommGroup Z] [Module ℂ Z] [TopologicalSpace G]
    [IsTopologicalGroup G] (H : Subgroup G) (ρ : Representation ℂ H Z) (f : cIndSpace H ρ) :
    ∃ S : Set G, IsOpen S ∧ (1 : G) ∈ S ∧ ∀ s ∈ S, ∀ p : G, f.1.1.1 (p * s) = f.1.1.1 p := by
  have hopen : IsOpen {s : G | GlobalTheory.PRep.ind H ρ s f.1.1 = f.1.1} := f.1.2
  refine ⟨_, hopen, ?_, fun s hs p => ?_⟩
  · show GlobalTheory.PRep.ind H ρ 1 f.1.1 = f.1.1
    simp
  · have hs' : GlobalTheory.PRep.ind H ρ s f.1.1 = f.1.1 := hs
    exact congrFun (congrArg Subtype.val hs') p

theorem exists_compact_support {G Z : Type} [Group G] [AddCommGroup Z] [Module ℂ Z] [TopologicalSpace G]
    [IsTopologicalGroup G] (H : Subgroup G) (ρ : Representation ℂ H Z) (f : cIndSpace H ρ) :
    ∃ C : Set G, IsCompact C ∧ ∀ p : G, f.1.1.1 p ≠ 0 → ∃ h ∈ H, ∃ c ∈ C, p = h * c :=
  f.2

section Column

variable (k : Type) [Field k]

def col (n : ℕ) (p : Mir k n) : Fin n → k :=
  fun j => ((p : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) (Fin.castSucc j) (Fin.last n)

theorem last_last (n : ℕ) (p : Mir k n) :
    ((p : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) (Fin.last n) (Fin.last n) = 1 := by
  have h := congrFun ((GlobalTheory.BZMir.mem_Mir_iff k (p : GL (Fin (n + 1)) k)).1 p.2) (Fin.last n)
  simpa [GlobalTheory.BZMir.eLast] using h

theorem last_column_entry_product_formula (n : ℕ) (a : Fin n → k) (A : Matrix (Fin n) (Fin n) k)
    (P : Matrix (Fin (n + 1)) (Fin (n + 1)) k) (hP : P (Fin.last n) (Fin.last n) = 1) (j : Fin n) :
    ((1 + colMat k n a) * glEmbMat k n A * P) (Fin.castSucc j) (Fin.last n) =
      a j + (A.mulVec (fun l => P (Fin.castSucc l) (Fin.last n))) j := by
  rw [add_mul, one_mul, GlobalTheory.BZMir.colMat_mul_glEmbMat, add_mul, Matrix.add_apply]
  simp [Matrix.mul_apply, Fin.sum_univ_castSucc, GlobalTheory.BZMir.glEmbMat, GlobalTheory.BZMir.colMat, Matrix.mulVec,
    dotProduct, hP, Fin.castSucc_ne_last]
  all_goals ring

theorem col_uM_levi_mul (n : ℕ) (a : Fin n → k) (g : GL (Fin n) k) (p : Mir k n) :
    col k n (uM k n a * levi k n g * p) = a + (g : Matrix (Fin n) (Fin n) k).mulVec (col k n p) := by
  funext j
  exact GlobalTheory.CompanionTheory.BZPsiPG.FibCompact.last_column_entry_product_formula k n a (g : Matrix (Fin n) (Fin n) k)
    ((p : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) (GlobalTheory.CompanionTheory.BZPsiPG.FibCompact.last_last k n p) j

theorem col_one (n : ℕ) : col k n 1 = 0 := by
  funext j
  simp [GlobalTheory.CompanionTheory.BZPsiPG.FibCompact.col, Matrix.one_apply, Fin.castSucc_ne_last]

theorem col_uM_levi (n : ℕ) (a : Fin n → k) (g : GL (Fin n) k) :
    col k n (uM k n a * levi k n g) = a := by
  have h := GlobalTheory.CompanionTheory.BZPsiPG.FibCompact.col_uM_levi_mul k n a g 1
  rwa [mul_one, GlobalTheory.CompanionTheory.BZPsiPG.FibCompact.col_one, Matrix.mulVec_zero, add_zero] at h

end Column

section Top

variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem continuous_midV (i t : ℕ) : Continuous (midV k i t) := by
  refine continuous_pi fun j => ?_
  induction j using Fin.addCases with
  | left l =>
    show Continuous fun v : Fin t → k => Fin.append (0 : Fin i → k) v (Fin.castAdd t l)
    simp only [Fin.append_left, Pi.zero_apply]
    exact continuous_const
  | right l =>
    show Continuous fun v : Fin t → k => Fin.append (0 : Fin i → k) v (Fin.natAdd i l)
    simp only [Fin.append_right]
    exact continuous_apply l

theorem continuous_col_inv (n : ℕ) : Continuous (fun c : Mir k n => col k n c⁻¹) :=
  continuous_pi fun j =>
    (Units.continuous_coe_inv.comp continuous_subtype_val).matrix_elem (Fin.castSucc j) (Fin.last n)

theorem isLocallyConstant_uM {Z : Type} (n : ℕ) (F : Mir k n → Z) (S : Set (Mir k n)) (hS : IsOpen S)
    (h1 : (1 : Mir k n) ∈ S) (hF : ∀ s ∈ S, ∀ p, F (p * s) = F p) (g : GL (Fin n) k) :
    IsLocallyConstant (fun y : Fin n → k => F (uM k n y * levi k n g)) := by
  rw [IsLocallyConstant.iff_exists_open]
  intro y₀
  have hu := (GlobalTheory.T.continuous_levi_unipotent_proj k n).2.1
  set L := GlobalTheory.BZMir.levi k n g
  let φ : (Fin n → k) → GlobalTheory.BZMir.Mir k n := fun y => L⁻¹ * GlobalTheory.CompanionTheory.BZPsiPG.uM k n (y - y₀) * L
  have hφ : Continuous φ :=
    (continuous_const.mul (hu.comp (continuous_id.sub continuous_const))).mul continuous_const
  refine ⟨φ ⁻¹' S, hS.preimage hφ, ?_, fun y hy => ?_⟩
  · show L⁻¹ * GlobalTheory.CompanionTheory.BZPsiPG.uM k n (y₀ - y₀) * L ∈ S
    rw [sub_self, GlobalTheory.CompanionTheory.BZPsiPG.uM_zero, mul_one, inv_mul_cancel]
    exact h1
  · have hadd : GlobalTheory.CompanionTheory.BZPsiPG.uM k n y =
        GlobalTheory.CompanionTheory.BZPsiPG.uM k n y₀ * GlobalTheory.CompanionTheory.BZPsiPG.uM k n (y - y₀) := by
      rw [← GlobalTheory.CompanionTheory.BZPsiPG.uM_add]
      congr 1
      abel
    have hy' : GlobalTheory.CompanionTheory.BZPsiPG.uM k n y * L = GlobalTheory.CompanionTheory.BZPsiPG.uM k n y₀ * L * φ y := by
      rw [hadd]
      simp only [φ]
      group
    show F (GlobalTheory.CompanionTheory.BZPsiPG.uM k n y * L) = F (GlobalTheory.CompanionTheory.BZPsiPG.uM k n y₀ * L)
    rw [hy']
    exact hF _ hy _

end Top

theorem fibV_main : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (i t : ℕ) {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] (τ : Representation ℂ (Mir k i) V) (σ : Representation ℂ (GL (Fin t) k) W), IsSmooth τ → IsSmooth σ → ∀ (f : cIndSpace (HPG k i t) (hRep τ σ)) (g : GL (Fin (i + t)) k), IsLocallyConstant (fibV f g) ∧ HasCompactSupport (fibV f g) := by
  intro k _ _ _ _ i t V W _ _ _ _ τ σ _ _ f g
  constructor
  · obtain ⟨S, hS, h1, hSf⟩ := GlobalTheory.CompanionTheory.BZPsiPG.FibCompact.exists_right_invariant _ _ f
    exact (GlobalTheory.CompanionTheory.BZPsiPG.FibCompact.isLocallyConstant_uM k (i + t) _ S hS h1 hSf g).comp_continuous
      (GlobalTheory.CompanionTheory.BZPsiPG.FibCompact.continuous_midV k i t)
  · obtain ⟨C, hC, hCf⟩ := GlobalTheory.CompanionTheory.BZPsiPG.FibCompact.exists_compact_support _ _ f
    let proj : GlobalTheory.BZMir.Mir k (i + t) → Fin t → k := fun c j =>
      -(((g : Matrix (Fin (i + t)) (Fin (i + t)) k) *ᵥ GlobalTheory.CompanionTheory.BZPsiPG.FibCompact.col k (i + t) c⁻¹) (Fin.natAdd i j))
    have hproj : Continuous proj := continuous_pi fun j =>
      ((continuous_apply (Fin.natAdd i j)).comp
        (continuous_const.matrix_mulVec (GlobalTheory.CompanionTheory.BZPsiPG.FibCompact.continuous_col_inv k (i + t)))).neg
    refine HasCompactSupport.of_support_subset_isCompact (hC.image hproj) ?_
    intro v hv
    obtain ⟨h, hh, c, hc, hp⟩ := hCf (GlobalTheory.CompanionTheory.BZPsiPG.uM k (i + t) (GlobalTheory.CompanionTheory.BZPsiPG.midV k i t v) *
      GlobalTheory.BZMir.levi k (i + t) g) hv
    refine ⟨c, hc, ?_⟩
    obtain ⟨x, q, hxq⟩ := GlobalTheory.T.parabolic_unipotent_levi_decomp k i t ⟨h, hh⟩
    have hxq' : h = GlobalTheory.CompanionTheory.BZPsiPG.uM k (i + t) (GlobalTheory.CompanionTheory.BZPsiPG.topV k i t x) *
        GlobalTheory.BZMir.levi k (i + t) q := hxq
    have key : GlobalTheory.CompanionTheory.BZPsiPG.topV k i t x = GlobalTheory.CompanionTheory.BZPsiPG.midV k i t v +
        (g : Matrix (Fin (i + t)) (Fin (i + t)) k) *ᵥ GlobalTheory.CompanionTheory.BZPsiPG.FibCompact.col k (i + t) c⁻¹ := by
      rw [← GlobalTheory.CompanionTheory.BZPsiPG.FibCompact.col_uM_levi_mul, hp, mul_inv_cancel_right, hxq',
        GlobalTheory.CompanionTheory.BZPsiPG.FibCompact.col_uM_levi]
    funext j
    have hj := congrFun key (Fin.natAdd i j)
    simp only [GlobalTheory.CompanionTheory.BZPsiPG.topV, GlobalTheory.CompanionTheory.BZPsiPG.midV, Fin.append_right, Pi.add_apply, Pi.zero_apply] at hj
    show -(((g : Matrix (Fin (i + t)) (Fin (i + t)) k) *ᵥ GlobalTheory.CompanionTheory.BZPsiPG.FibCompact.col k (i + t) c⁻¹) (Fin.natAdd i j)) = v j
    rw [neg_eq_iff_add_eq_zero, add_comm]
    exact hj.symm

end GlobalTheory.CompanionTheory.BZPsiPG.FibCompact

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FibreMeasureExtensionUnique
section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.PiLocalization₂ GlobalTheory.CompanionTheory.SW.StageF GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

noncomputable section

namespace GlobalTheory.CompanionTheory.SW.StageF.FoldF

theorem foldF : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (M : ℕ) (J : Matrix (Fin M) (Fin M) E) (t : F) (n : ℕ) (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [MeasurableSpace R] [BorelSpace R] (d : ℕ) (b : Module.Basis (Fin d) F E) (lam : Measure R) (m₁ : HermR R σ 1 → Measure (Fin 1 → Fin (M + 1) → R ⊗[F] E)) (m' : HermR R σ n → Measure (Fin n → Fin M → R ⊗[F] E)) (s : (Fin 1 → Fin (M + 1) → R ⊗[F] E) → HA R σ (blockOne (algebraMap F E t) J)) (B₀ : Set R) (a : R → Rˣ) (κ₁ cm : Rˣ → ℝ≥0), HermitianMeasureData σ J t n b lam m₁ m' s B₀ a κ₁ cm → ∀ φ : (Fin (n + 1) → Fin (M + 1) → R ⊗[F] E) → ℝ≥0∞, Measurable φ → ∫⁻ S, ∫⁻ v, φ v ∂(fibSF σ J t m₁ m' s B₀ a κ₁ cm S) ∂(coordHerm R σ b lam (n + 1)) = MidF σ J t m₁ m' s B₀ a κ₁ b lam φ := by
  intro F E _ _ _ _ _ σ M J t n R _ _ _ _ _ d b lam m₁ m' s B₀ a κ₁ cm D φ hφ
  obtain ⟨hTR, hLC, hSC, hT2, -⟩ := D.hR
  haveI := hTR
  haveI := hLC
  haveI := hSC
  haveI := hT2
  have hσ := D.hCM
  have hlam := D.hlam
  haveI := hlam
  obtain ⟨hKring, hKlc, hKsc, hKt2, hsig, htr, -, -, -, -⟩ := GlobalTheory.T.tensor_locally_compact_ring F E σ hσ R
  haveI := hKring
  haveI := hKlc
  haveI := hKsc
  haveI := hKt2
  haveI : BorelSpace (R ⊗[F] E) := ⟨rfl⟩
  obtain ⟨hκh, -, hνh⟩ := GlobalTheory.T.coordinate_haar_measure F E σ hσ R d b lam hlam
  haveI := hκh
  haveI hHb : ∀ m, BorelSpace (HermR R σ m) := fun _ => ⟨rfl⟩
  haveI hHlc : ∀ m, LocallyCompactSpace (HermR R σ m) := fun m =>
    (GlobalTheory.T.hermitian_matrices_locally_compact_borel F E σ hσ R m).1
  haveI hHsc : ∀ m, SecondCountableTopology (HermR R σ m) := fun m =>
    (GlobalTheory.T.hermitian_matrices_locally_compact_borel F E σ hσ R m).2.1
  haveI : (coordHerm R σ b lam n).IsAddHaarMeasure := hνh n
  haveI : SigmaFinite (coordK R b lam) := inferInstance
  haveI : SigmaFinite (coordHerm R σ b lam n) := inferInstance
  obtain ⟨e, he00, he0j, heij, hemap⟩ := GlobalTheory.T.coordinate_homeomorph_tensor_product_measure F E σ hσ R d b lam hlam n
  obtain ⟨m₀, D₀⟩ := GlobalTheory.T.local_fibre_measure_extension_by_one F E σ M J t n R d b lam m₁ m' s B₀ a κ₁ cm D
  obtain ⟨hs0c, hacS, hcvc, hschc, -⟩ :=
    GlobalTheory.T.continuousOn_schur_coordinates_and_isOpen_Bset F E σ M J t n R d b lam m₁ m₀ s B₀ a κ₁ cm D₀
  have hBopen : IsOpen (BsetF R σ B₀ : Set (HermR R σ (n + 1))) := D.hB₀.preimage hs0c
  have hGon0 := GlobalTheory.T.fibre_measure_extension_by_one_integral F E σ M J t n R d b lam m₁ m' s B₀ a κ₁ cm D φ hφ
  have hmeas := GlobalTheory.T.fibre_measure_extension_symmetric F E σ M J t n R d b lam m₁ m' s B₀ a κ₁ cm D φ hφ
  have hsubst := GlobalTheory.T.lintegral_coordK_coordHerm_scale_shear F E σ M J t n R d b lam m₁ m₀ s B₀ a κ₁ cm D₀
  have hGoff0 : ∀ S, S ∉ BsetF R σ B₀ →
      ∫⁻ v, φ v ∂(fibSF σ J t m₁ m' s B₀ a κ₁ cm S) = 0 := by
    intro S hS
    have h0 : fibSF σ J t m₁ m' s B₀ a κ₁ cm S = 0 := by
      unfold fibSF
      exact Set.indicator_of_notMem hS _
    rw [h0, lintegral_zero_measure]
  obtain ⟨G, hG⟩ : ∃ G : HermR R σ (n + 1) → ℝ≥0∞,
      G = fun S => ∫⁻ v, φ v ∂(fibSF σ J t m₁ m' s B₀ a κ₁ cm S) := ⟨_, rfl⟩
  have hGoff : ∀ S, S ∉ BsetF R σ B₀ → G S = 0 := by
    intro S hS
    rw [hG]
    exact hGoff0 S hS
  have hGon : ∀ S ∈ (BsetF R σ B₀ : Set (HermR R σ (n + 1))), G S =
      (κ₁ (a (s0 R (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E)))) : ℝ≥0∞) *
      (cm (a (s0 R (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E)))) : ℝ≥0∞) ^ n *
      Pint σ J t m₁ m' s φ ((a (s0 R (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E)))) : R)
        (cvec R t a (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E))) (schur R σ t a S) := by
    intro S hS
    rw [hG]
    exact hGon0 S hS
  show ∫⁻ S, (fun S => ∫⁻ v, φ v ∂(fibSF σ J t m₁ m' s B₀ a κ₁ cm S)) S ∂(coordHerm R σ b lam (n + 1)) = _
  rw [← hG]
  clear hGon0 hGoff0 hG
  have hGm : Measurable G := by
    refine measurable_of_restrict_of_restrict_compl hBopen.measurableSet ?_ ?_
    · have hsub : (BsetF R σ B₀ : Set (HermR R σ (n + 1))) ⊆
          {S | s0 R (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E)) ∈ B₀} := fun S h => h
      have hk := continuousOn_iff_continuous_restrict.1 (hacS.mono hsub)
      have hc := continuousOn_iff_continuous_restrict.1 (hcvc.mono hsub)
      have hw := continuousOn_iff_continuous_restrict.1 (hschc.mono hsub)
      have hP := hmeas.comp (((Units.continuous_val.comp hk).prodMk (hc.prodMk hw)).measurable)
      have hE : (BsetF R σ B₀ : Set (HermR R σ (n + 1))).domRestrict G = _ :=
        funext fun S => hGon S S.2
      rw [hE]
      exact (((ENNReal.continuous_coe.comp (D.hκc.comp hk)).measurable).mul
        (((ENNReal.continuous_coe.comp (D.hcmc.comp hk)).measurable).pow_const n)).mul hP
    · have hE : (BsetF R σ B₀ : Set (HermR R σ (n + 1)))ᶜ.domRestrict G = fun _ => 0 :=
        funext fun S => hGoff S S.2
      rw [hE]
      exact measurable_const
  have hL : ∫⁻ S, G S ∂(coordHerm R σ b lam (n + 1)) =
      ∫⁻ x, ∫⁻ r, ∫⁻ S'', G (e (x, r, S'')) ∂(coordHerm R σ b lam n)
        ∂(Measure.pi fun _ => coordK R b lam) ∂lam := by
    have hGe : Measurable (fun p => G (e p)) := hGm.comp e.continuous.measurable
    rw [← hemap, lintegral_map hGm e.continuous.measurable, lintegral_prod _ hGe.aemeasurable]
    refine lintegral_congr fun x => ?_
    exact lintegral_prod _ (hGe.comp measurable_prodMk_left).aemeasurable
  have hs0 : ∀ p, s0 R (e p : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E)) = p.1 :=
    fun p => Fold.corner_half_trace_of_cm_pure_tensor R σ hσ _ _ (he00 p)
  have hoff : ∀ x, x ∉ B₀ → ∫⁻ r, ∫⁻ S'', G (e (x, r, S'')) ∂(coordHerm R σ b lam n)
      ∂(Measure.pi fun _ => coordK R b lam) = 0 := by
    intro x hx
    have h0 : ∀ (r : Fin n → R ⊗[F] E) (S'' : HermR R σ n), G (e (x, r, S'')) = 0 := by
      intro r S''
      refine hGoff _ fun h => hx ?_
      have h1 : s0 R (e (x, r, S'') : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E)) ∈ B₀ := h
      rwa [hs0] at h1
    simp [h0]
  have hon : ∀ x ∈ B₀, ∫⁻ r, ∫⁻ S'', G (e (x, r, S'')) ∂(coordHerm R σ b lam n)
      ∂(Measure.pi fun _ => coordK R b lam) = (κ₁ (a x) : ℝ≥0∞) * ∫⁻ c : Fin n → R ⊗[F] E,
        ∫⁻ S', Pint σ J t m₁ m' s φ ((a x : Rˣ) : R) c S' ∂(coordHerm R σ b lam n)
        ∂(Measure.pi fun _ => coordK R b lam) := by
    intro x hx
    obtain ⟨u, hu⟩ : ∃ u : Rˣ, u = a x := ⟨_, rfl⟩
    rw [← hu]
    obtain ⟨cr, hcrdef⟩ : ∃ cr : (Fin n → R ⊗[F] E) → Fin n → R ⊗[F] E,
        cr = fun r j => ((((u⁻¹ : Rˣ) : R) ⊗ₜ[F] (algebraMap F E t⁻¹)) * r j) := ⟨_, rfl⟩
    have hcr : Continuous cr := by
      rw [hcrdef]
      exact continuous_pi fun j => continuous_const.mul (continuous_apply j)
    let w : (Fin n → R ⊗[F] E) → HermR R σ n := fun r => ⟨Fold.qM R σ t (cr r), Fold.qM_mem R σ hσ t _⟩
    have hw : Measurable w := by
      have hwc : Continuous w := by
        refine Continuous.subtype_mk (continuous_pi fun i => continuous_pi fun j => ?_) _
        exact ((hsig.comp ((continuous_apply i).comp hcr)).mul continuous_const).mul
          ((continuous_apply j).comp hcr)
      exact hwc.measurable
    let f : (Fin n → R ⊗[F] E) × HermR R σ n → ℝ≥0∞ := fun z =>
      Pint σ J t m₁ m' s φ (u : R) z.1 z.2
    have hf : Measurable f :=
      hmeas.comp (measurable_const.prodMk measurable_id)
    have hpt : ∀ (r : Fin n → R ⊗[F] E) (S'' : HermR R σ n), G (e (x, r, S'')) =
        ((κ₁ u : ℝ≥0∞) * (cm u : ℝ≥0∞) ^ n) * f (cr r, S'' - w r) := by
      intro r S''
      have h0 : s0 R (e (x, r, S'') : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E)) = x := hs0 _
      have h1 : cvec R t a (e (x, r, S'') : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E)) = cr r := by
        funext j
        rw [hcrdef]
        show ((((a (s0 R _))⁻¹ : Rˣ) : R) ⊗ₜ[F] (algebraMap F E t⁻¹)) * _ = _
        rw [h0, he0j, ← hu]
      have h2 : schur R σ t a (e (x, r, S'')) = S'' - w r := by
        rw [Fold.schur_split R σ hσ t a (e (x, r, S'')) S'' (heij (x, r, S''))]
        have h3 : (⟨Fold.qM R σ t (cvec R t a (e (x, r, S'') : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E))),
            Fold.qM_mem R σ hσ t _⟩ : HermR R σ n) = w r := Subtype.ext (congrArg (Fold.qM R σ t) h1)
        rw [h3]
      have hB : e (x, r, S'') ∈ (BsetF R σ B₀ : Set (HermR R σ (n + 1))) := by
        show s0 R _ ∈ B₀
        rw [h0]
        exact hx
      rw [hGon _ hB, h0, h1, h2, ← hu]
    have hC : ((κ₁ u : ℝ≥0∞) * (cm u : ℝ≥0∞) ^ n) ≠ ∞ :=
      ENNReal.mul_ne_top ENNReal.coe_ne_top (ENNReal.pow_ne_top ENNReal.coe_ne_top)
    have hS : ∫⁻ c, ∫⁻ S', f (c, S') ∂(coordHerm R σ b lam n) ∂(Measure.pi fun _ => coordK R b lam) =
        (cm u : ℝ≥0∞) ^ n * ∫⁻ r, ∫⁻ S'', f (cr r, S'' - w r) ∂(coordHerm R σ b lam n)
          ∂(Measure.pi fun _ => coordK R b lam) := by
      rw [hcrdef]
      exact hsubst u w hw f hf
    calc ∫⁻ r, ∫⁻ S'', G (e (x, r, S'')) ∂(coordHerm R σ b lam n)
          ∂(Measure.pi fun _ => coordK R b lam)
        = ∫⁻ r, ∫⁻ S'', ((κ₁ u : ℝ≥0∞) * (cm u : ℝ≥0∞) ^ n) * f (cr r, S'' - w r)
          ∂(coordHerm R σ b lam n) ∂(Measure.pi fun _ => coordK R b lam) := by
          simp only [hpt]
      _ = ((κ₁ u : ℝ≥0∞) * (cm u : ℝ≥0∞) ^ n) * ∫⁻ r, ∫⁻ S'', f (cr r, S'' - w r)
          ∂(coordHerm R σ b lam n) ∂(Measure.pi fun _ => coordK R b lam) := by
          simp only [lintegral_const_mul' _ _ hC]
      _ = (κ₁ u : ℝ≥0∞) * ((cm u : ℝ≥0∞) ^ n * ∫⁻ r, ∫⁻ S'', f (cr r, S'' - w r)
          ∂(coordHerm R σ b lam n) ∂(Measure.pi fun _ => coordK R b lam)) := mul_assoc _ _ _
      _ = (κ₁ u : ℝ≥0∞) * ∫⁻ c, ∫⁻ S', f (c, S') ∂(coordHerm R σ b lam n)
          ∂(Measure.pi fun _ => coordK R b lam) := by rw [hS]
      _ = _ := rfl
  rw [hL]
  unfold MidF
  calc _ = ∫⁻ x, B₀.indicator (fun x => ∫⁻ r, ∫⁻ S'', G (e (x, r, S'')) ∂(coordHerm R σ b lam n)
        ∂(Measure.pi fun _ => coordK R b lam)) x ∂lam := by
        refine lintegral_congr fun x => ?_
        by_cases hx : x ∈ B₀
        · rw [Set.indicator_of_mem hx]
        · rw [Set.indicator_of_notMem hx, hoff x hx]
    _ = ∫⁻ x in B₀, ∫⁻ r, ∫⁻ S'', G (e (x, r, S'')) ∂(coordHerm R σ b lam n)
        ∂(Measure.pi fun _ => coordK R b lam) ∂lam := lintegral_indicator D.hB₀.measurableSet _
    _ = _ := setLIntegral_congr_fun D.hB₀.measurableSet hon

end GlobalTheory.CompanionTheory.SW.StageF.FoldF
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HyperbolicRankOneGlobalVolumeStatement
section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free GlobalTheory.CompanionTheory.WeilSiegel.HypStep
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hyperbolic_rank_one_global_volume : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → 3 ≤ M → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (laminf : Measure (Ainf F)) (lam : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Fv F v)), IsStdInf laminf → (∀ v, IsStdV v (lam v)) → ∀ (h₂ : ∀ a b : Fin 1, σ ((0 : Matrix (Fin 1) (Fin 1) E) b a) = (0 : Matrix (Fin 1) (Fin 1) E) a b) (minf : HermR (Ainf F) σ 1 → Measure (Fin 1 → Fin (M + 2) → Ainf F ⊗[F] E)) (m : ∀ v : HeightOneSpectrum (𝓞 F), HermR (Fv F v) σ 1 → Measure (Fin 1 → Fin (M + 2) → Fv F v ⊗[F] E)), IsGramFibFree (Ainf F) σ (hypOne J) 1 (coordW (Ainf F) b laminf 1 (M + 2)) (coordHerm (Ainf F) σ b laminf 1) minf → (∀ v, IsGramFibFree (Fv F v) σ (hypOne J) 1 (coordW (Fv F v) b (lam v) 1 (M + 2)) (coordHerm (Fv F v) σ b (lam v) 1) (m v)) → ∀ I : Measure (Fin 1 → Fin (M + 2) → AF F ⊗[F] E), IsEulerProd b I 1 (minf (hermOf (Ainf F) σ (0 : Matrix (Fin 1) (Fin 1) E) h₂)) (fun v => m v (hermOf (Fv F v) σ (0 : Matrix (Fin 1) (Fin 1) E) h₂)) → Summable (fun v => |(m v (hermOf (Fv F v) σ (0 : Matrix (Fin 1) (Fin 1) E) h₂) (primV σ J b v)).toReal - 1|) ∧ ∃ S₃ : Finset (HeightOneSpectrum (𝓞 F)), ∀ S, S₃ ⊆ S → ∀ (Ψinf : (Fin 1 → Fin (M + 2) → Ainf F ⊗[F] E) → ℝ≥0∞) (Ψ : ∀ v : HeightOneSpectrum (𝓞 F), (Fin 1 → Fin (M + 2) → Fv F v ⊗[F] E) → ℝ≥0∞), Measurable Ψinf → (∀ v, Measurable (Ψ v)) → ∫⁻ y, purePr σ J b S Ψinf Ψ y ∂I = ((∫⁻ y, Ψinf y ∂(minf (hermOf (Ainf F) σ (0 : Matrix (Fin 1) (Fin 1) E) h₂))) * ∏ v ∈ S, ∫⁻ y, Ψ v y ∂(m v (hermOf (Fv F v) σ (0 : Matrix (Fin 1) (Fin 1) E) h₂))) * ENNReal.ofReal (∏' v : {v // v ∉ S}, (m v.1 (hermOf (Fv F v.1) σ (0 : Matrix (Fin 1) (Fin 1) E) h₂) (primV σ J b v.1)).toReal) := by
  first | exact @GlobalTheory.CompanionTheory.WeilSiegel.HypStep.PrimOne.prim_formula | exact GlobalTheory.CompanionTheory.WeilSiegel.HypStep.PrimOne.prim_formula | (intros; apply GlobalTheory.CompanionTheory.WeilSiegel.HypStep.PrimOne.prim_formula <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LOneSatakeBoundStatement
section
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.SplitWeil ValuativeRel
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.l_one_satake_bound : PositivityTheory.SphericalProduct.LOneSat := by
  first | exact @GlobalTheory.CompanionTheory.OneSat.lOneSat | exact GlobalTheory.CompanionTheory.OneSat.lOneSat | (intros; apply GlobalTheory.CompanionTheory.OneSat.lOneSat <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalIsotropicOrbitOfE0Statement
section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free GlobalTheory.CompanionTheory.WeilSiegel.HypStep GlobalTheory.CompanionTheory.WeilSiegel.HypMass
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_isotropic_orbit_of_e0 : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (v : HeightOneSpectrum (𝓞 F)) (y : Fin 1 → Fin (M + 2) → Fv F v ⊗[F] E), LinearIndependent (Fv F v ⊗[F] E) y → gramR (Fv F v) σ (hypOne J) y = 0 → ∃ g : HA (Fv F v) σ (hypOne J), actW (Fv F v) σ (hypOne J) g (e0 _ M) = y := by
  first | exact @GlobalTheory.CompanionTheory.WeilSiegel.HypOrbit.exists_actW_e0_eq | exact GlobalTheory.CompanionTheory.WeilSiegel.HypOrbit.exists_actW_e0_eq | (intros; apply GlobalTheory.CompanionTheory.WeilSiegel.HypOrbit.exists_actW_e0_eq <;> assumption)
end

