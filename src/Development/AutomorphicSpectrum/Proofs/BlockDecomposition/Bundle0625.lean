import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.LocalComparisonSplitting.EulerFactorLevels.EulerFinOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1459
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1274
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1243
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0049
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0330
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0219
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsUniqueIsConjAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1388
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0554
import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.WeakApproximationFinitePlace
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0590
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.HaarFundamentalDomainOrthogonalSum
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.ZelevinskyCosocles.LUnlinkedComm
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0003
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0592
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.InstAddCommGroupTwo
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0599
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.SquareIntegrableTempered.CasselmanNecTemp
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.PropsCos
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0001
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JacquetMultiplicityTransitiveLe
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0600
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0572
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalOrderTwoPrimesAlmostAll

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IntegralOfTwistConjugatePlace
section
noncomputable section

open NumberField IsDedekindDomain Matrix Polynomial Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host
open GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.CompanionTheory.SuppFinTw

open PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.G8.Fin

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {a b : ℕ}

def atH (a b : ℕ) (w : Pl E) : Gf E a b →* GLw a w × GLw b w :=
  (GeneralLinearGroup.map (pLoc E w)).prodMap (GeneralLinearGroup.map (pLoc E w))

abbrev thW (a b : ℕ) (w : Pl E) : GLw a w × GLw b w →* GLw a w × GLw b w := (thL a w).prodMap (thL b w)

abbrev dW (w : Pl E) (δ₁ : GL (Fin a) E) (δ₂ : GL (Fin b) E) : GLw a w × GLw b w := (locEl a w δ₁, locEl b w δ₂)

abbrev dG (δ₁ : GL (Fin a) E) (δ₂ : GL (Fin b) E) : Gf E a b := (ratF E a δ₁, ratF E b δ₂)

abbrev KK (E : Type) [Field E] [NumberField E] [IsCMField E] (a b : ℕ) : Subgroup (Gf E a b) := (Kf E a).prod (Kf E b)

omit [IsCMField E] in
theorem atH_apply (w : Pl E) (y : Gf E a b) : atH a b w y = atW w y := rfl

theorem mem_KK_iff (g : Gf E a b) : g ∈ KK E a b ↔ ∀ u : Pl E, atH a b u g ∈ K2 a b u := by
  simp only [KK, Subgroup.mem_prod, Kf, Subgroup.mem_iInf, Subgroup.mem_comap]
  exact ⟨fun h u => ⟨h.1 u, h.2 u⟩, fun h => ⟨fun u => (h u).1, fun u => (h u).2⟩⟩

theorem ext_atH {g h : Gf E a b} (H : ∀ u : Pl E, atH a b u g = atH a b u h) : g = h :=
  Prod.ext (GlobalTheory.EulerTwRestr.gl_ext fun u => congrArg Prod.fst (H u))
    (GlobalTheory.EulerTwRestr.gl_ext fun u => congrArg Prod.snd (H u))

theorem ae_mem_GL {n : ℕ} (x : GL (Fin n) (Af E)) :
    ∀ᶠ w in cofinite, GeneralLinearGroup.map (pLoc E w) x ∈ GlobalTheory.LFun.KGL w n := by
  have h1 : ∀ᶠ w in cofinite, ∀ i j, pLoc E w (x.1 i j) ∈ (w : Pl E).adicCompletionIntegers E :=
    eventually_all.2 fun i => eventually_all.2 fun j => (x.1 i j).2
  have h2 : ∀ᶠ w in cofinite, ∀ i j, pLoc E w ((x⁻¹).1 i j) ∈ (w : Pl E).adicCompletionIntegers E :=
    eventually_all.2 fun i => eventually_all.2 fun j => ((x⁻¹).1 i j).2
  filter_upwards [h1, h2] with w h1 h2
  exact GlobalTheory.EulerTwRestr.mem_KGL_iff.2 ⟨fun i j => by rw [GlobalTheory.EulerTwRestr.loc_val]; exact h1 i j,
    fun i j => by rw [GlobalTheory.EulerTwRestr.loc_inv_val]; exact h2 i j⟩

theorem ae_mem (g : Gf E a b) : ∀ᶠ u in cofinite, atH a b u g ∈ K2 a b u := by
  filter_upwards [ae_mem_GL g.1, ae_mem_GL g.2] with u h1 h2
  exact ⟨h1, h2⟩

theorem exists_GL_of_family {n : ℕ} (z : ∀ u : Pl E, GLw n u) (hz : ∀ᶠ u in cofinite, z u ∈ GlobalTheory.LFun.KGL u n) :
    ∃ g : GL (Fin n) (Af E), ∀ u, GeneralLinearGroup.map (pLoc E u) g = z u := by
  let M : Matrix (Fin n) (Fin n) (Af E) := Matrix.of fun i j =>
    ⟨fun w => (z w).1 i j, hz.mono fun w h => (GlobalTheory.EulerTwRestr.mem_KGL_iff.1 h).1 i j⟩
  let M' : Matrix (Fin n) (Fin n) (Af E) := Matrix.of fun i j =>
    ⟨fun w => ((z w)⁻¹).1 i j, hz.mono fun w h => (GlobalTheory.EulerTwRestr.mem_KGL_iff.1 h).2 i j⟩
  have hloc : ∀ P Q : Matrix (Fin n) (Fin n) (Af E),
      (∀ w : Pl E, P.map (pLoc E w) = Q.map (pLoc E w)) → P = Q := fun P Q h =>
    Matrix.ext fun i j => Subtype.ext (funext fun w => congrFun (congrFun (h w) i) j)
  have hMM' : M * M' = 1 := hloc _ _ fun w => by
    rw [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)]
    exact (z w).mul_inv
  have hM'M : M' * M = 1 := hloc _ _ fun w => by
    rw [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)]
    exact (z w).inv_mul
  exact ⟨⟨M, M', hMM', hM'M⟩, fun u => Units.ext (Matrix.ext fun i j => rfl)⟩

theorem exists_of_family (z : ∀ u : Pl E, GLw a u × GLw b u) (hz : ∀ᶠ u in cofinite, z u ∈ K2 a b u) :
    ∃ g : Gf E a b, ∀ u, atH a b u g = z u := by
  obtain ⟨g₁, h₁⟩ := exists_GL_of_family (fun u => (z u).1) (hz.mono fun u h => h.1)
  obtain ⟨g₂, h₂⟩ := exists_GL_of_family (fun u => (z u).2) (hz.mono fun u h => h.2)
  exact ⟨(g₁, g₂), fun u => Prod.ext (h₁ u) (h₂ u)⟩

theorem thP_thP (y : Gf E a b) : thP E a b (thP E a b y) = y :=
  Prod.ext (GlobalTheory.EulerTw.Comm.thF_thF y.1) (GlobalTheory.EulerTw.Comm.thF_thF y.2)

theorem atH_thP_congr {u v : Pl E} (huv : GlobalTheory.EulerTw.cPl E u = v) {g h : Gf E a b}
    (H : atH a b v g = atH a b v h) : atH a b u (thP E a b g) = atH a b u (thP E a b h) := by
  subst huv
  refine Prod.ext ?_ ?_
  · change GeneralLinearGroup.map (pLoc E u) (thF E a g.1) = GeneralLinearGroup.map (pLoc E u) (thF E a h.1)
    rw [GlobalTheory.EulerTw.IntRead.map_thF, GlobalTheory.EulerTw.IntRead.map_thF]
    exact congrArg _ (congrArg Prod.fst H)
  · change GeneralLinearGroup.map (pLoc E u) (thF E b g.2) = GeneralLinearGroup.map (pLoc E u) (thF E b h.2)
    rw [GlobalTheory.EulerTw.IntRead.map_thF, GlobalTheory.EulerTw.IntRead.map_thF]
    exact congrArg _ (congrArg Prod.snd H)

theorem integral_of_twist_conjugate_place (u : Pl E) {g : Gf E a b} (H : atH a b u (thP E a b g) ∈ K2 a b u) :
    atH a b (GlobalTheory.EulerTw.cPl E u) g ∈ K2 a b (GlobalTheory.EulerTw.cPl E u) := by
  refine ⟨GlobalTheory.EulerTw.IntRead.mem_KGL_of_thAt u _ ?_, GlobalTheory.EulerTw.IntRead.mem_KGL_of_thAt u _ ?_⟩
  · have := H.1
    change GeneralLinearGroup.map (pLoc E u) (thF E a g.1) ∈ _ at this
    rwa [GlobalTheory.EulerTw.IntRead.map_thF] at this
  · have := H.2
    change GeneralLinearGroup.map (pLoc E u) (thF E b g.2) ∈ _ at this
    rwa [GlobalTheory.EulerTw.IntRead.map_thF] at this

theorem map_thF_of_not_split {n : ℕ} {w : Pl E} (hw : ¬ IsSplitAt w) (g : GL (Fin n) (Af E)) :
    GeneralLinearGroup.map (pLoc E w) (thF E n g) = thL n w (GeneralLinearGroup.map (pLoc E w) g) := by
  rw [GlobalTheory.EulerTw.IntRead.map_thF]
  refine Units.ext (Matrix.ext fun i j => ?_)
  have h2 := GlobalTheory.ThetaPull.thetaGL_apply (a := n) (cj w) (GeneralLinearGroup.map (pLoc E w) g) i j
  have e : thL n w = thetaGL n (cj w) := if_neg hw
  rw [e, h2, GlobalTheory.EulerTw.IntRead.thAt_apply, GlobalTheory.EulerTwRestr.loc_inv_val, GlobalTheory.EulerTwRestr.loc_inv_val]
  congr 1
  exact GlobLev.conjLoc_eq_cj hw _

theorem usage₇ {w : Pl E} (hw : ¬ IsSplitAt w) (g : Gf E a b) :
    atH a b w (thP E a b g) = thW a b w (atH a b w g) :=
  Prod.ext (map_thF_of_not_split hw g.1) (map_thF_of_not_split hw g.2)

theorem thW_of_split {w : Pl E} (hw : IsSplitAt w) (y : GLw a w × GLw b w) : thW a b w y = y := by
  simp [thL, hw]

theorem atH_dG_of_not_split {w : Pl E} (hw : ¬ IsSplitAt w) (δ₁ : GL (Fin a) E) (δ₂ : GL (Fin b) E) :
    atH a b w (dG δ₁ δ₂) = dW w δ₁ δ₂ := by
  refine Prod.ext ?_ ?_
  · simp only [locEl, if_neg hw]; rfl
  · simp only [locEl, if_neg hw]; rfl

theorem atH_norm_of_split {w : Pl E} (hw : IsSplitAt w) (δ₁ : GL (Fin a) E) (δ₂ : GL (Fin b) E) :
    atH a b w (dG δ₁ δ₂ * thP E a b (dG δ₁ δ₂)) = dW w δ₁ δ₂ := by
  refine Prod.ext ?_ ?_
  · simp only [locEl, if_pos hw]
    change GeneralLinearGroup.map (pLoc E w) (ratF E a δ₁ * thF E a (ratF E a δ₁)) = _
    rw [← GlobalTheory.EulerTw.Comm.thF_ratF, ← map_mul]; rfl
  · simp only [locEl, if_pos hw]
    change GeneralLinearGroup.map (pLoc E w) (ratF E b δ₂ * thF E b (ratF E b δ₂)) = _
    rw [← GlobalTheory.EulerTw.Comm.thF_ratF, ← map_mul]; rfl

theorem mem_or_conj {S : Set (Pl E)} (hS : IsSection S) (u : Pl E) : u ∈ S ∨ ∃ v ∈ S, u = GlobalTheory.EulerTw.cPl E v := by
  obtain ⟨v, ⟨hv, hvu⟩, -⟩ := hS u
  rcases GlobLev.eq_or_eq_conjSrc hvu.symm with h | h
  · exact Or.inl (h ▸ hv)
  · exact Or.inr ⟨v, hv, h⟩

theorem split_of_conj_ne {v : Pl E} (h : GlobalTheory.EulerTw.cPl E v ≠ v) : IsSplitAt v := by
  by_contra hv
  exact h (GlobLev.conjSrc_eq_of_not_split hv)

theorem cPl_cPl (v : Pl E) : GlobalTheory.EulerTw.cPl E (GlobalTheory.EulerTw.cPl E v) = v := GlobalTheory.ThetaPull.conjSrc_conjSrc _

theorem conj_not_mem {S : Set (Pl E)} (hS : IsSection S) {v : Pl E} (hv : v ∈ S) (h : IsSplitAt v) :
    GlobalTheory.EulerTw.cPl E v ∉ S := by
  intro hc
  obtain ⟨u, hne, hu⟩ := h
  have h1 : (GlobalTheory.EulerTw.cPl E v).under (𝓞 (maximalRealSubfield E)) = v.under (𝓞 (maximalRealSubfield E)) :=
    (GlobalTheory.EulerTwRestr.mem_orb_iff v _).1 (by simp [GlobalTheory.EulerTw.orb])
  have h2 : GlobalTheory.EulerTw.cPl E v = v := (hS v).unique ⟨hc, h1⟩ ⟨hv, rfl⟩
  rcases GlobLev.eq_or_eq_conjSrc hu with h3 | h3
  · exact hne h3
  · exact hne (h3.trans h2)

end GlobalTheory.CompanionTheory.SuppFinTw

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.InverseDoubleCosetNonsplit
section
open NumberField IsDedekindDomain Matrix Polynomial GlobalTheory.BCT GlobalTheory.UnitaryBC Formalism.UG GlobalTheory.PRep
open GlobalTheory.CuspRep Formalism.BasicNotions
open scoped Classical
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.CompanionTheory.InvDoubleCoset

section Generic

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {n : ℕ}

def wJ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (n : ℕ) : GL (Fin n) L :=
  ⟨antiJ L n, antiJ L n, GlobalTheory.UnitarySwap.antiJ_mul_self, GlobalTheory.UnitarySwap.antiJ_mul_self⟩

theorem cT_antiJ (σ : L →+* L) : cT σ (antiJ L n) = antiJ L n := by
  ext i j
  simp only [cT, Matrix.transpose_apply, Matrix.map_apply, antiJ]
  by_cases h : i.val + j.val + 1 = n
  · rw [if_pos h, if_pos (by omega)]; simp
  · rw [if_neg h, if_neg (by omega)]; simp

theorem wJ_mem_GU (σ : L →+* L) : wJ L n ∈ GU σ n := by
  change cT σ (antiJ L n) * antiJ L n * antiJ L n = antiJ L n
  rw [cT_antiJ, GlobalTheory.UnitarySwap.antiJ_mul_self, Matrix.one_mul]

theorem wJ_mem_GLint (O : Subring L) : wJ L n ∈ GLint (Fin n) O := by
  have h : ∀ i j, antiJ L n i j ∈ O := fun i j => by
    simp only [antiJ]
    split_ifs
    · exact O.one_mem
    · exact O.zero_mem
  exact GlobalTheory.AdelicU.mem_GLint_iff.2 ⟨h, h⟩

theorem wJ_conj_diag {σ : L →+* L} {ϖ : L} (hϖ : σ ϖ = ϖ) (d : Fin n → ℤ) (t : GU σ n)
    (ht : t.1.1 = Matrix.diagonal fun i => ϖ ^ d i) : wJ L n * t.1 * wJ L n = (t.1)⁻¹ := by
  have h0 : cT σ t.1.1 * antiJ L n * t.1.1 = antiJ L n := t.2
  have hc : cT σ t.1.1 = t.1.1 := by
    rw [ht]
    ext i j
    by_cases h : i = j
    · subst h
      simp [cT, map_zpow₀, hϖ]
    · simp [cT, Matrix.diagonal_apply_ne _ h, Matrix.diagonal_apply_ne _ (Ne.symm h)]
  rw [hc] at h0
  refine eq_inv_of_mul_eq_one_left (Units.ext ?_)
  change antiJ L n * t.1.1 * antiJ L n * t.1.1 = 1
  calc antiJ L n * t.1.1 * antiJ L n * t.1.1 = antiJ L n * (t.1.1 * antiJ L n * t.1.1) := by
        simp only [Matrix.mul_assoc]
    _ = 1 := by rw [h0, GlobalTheory.UnitarySwap.antiJ_mul_self]

end Generic

theorem inv_mem_doubleCoset : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E →
    ∀ (w : Pl E), ¬ IsSplitAt w → ∀ (n : ℕ) (g : UL n w),
      ∃ k₁ ∈ KL n w, ∃ k₂ ∈ KL n w, g⁻¹ = k₁ * g * k₂ := by
  intro E _ _ _ hU w hw n g
  obtain ⟨-, -, -, hns, -⟩ := GlobalTheory.T.placeConjugation_properties_cmField E hU w
  obtain ⟨-, ⟨ϖ, q, hUI, -⟩, -⟩ := hns hw
  obtain ⟨b, hbK, hb⟩ := GlobalTheory.LFun.InertChart.exists_congr_antiJ (n := n) hUI (B := 1) (one_mem _) (cT_one _)
  have hb' : cT (cj w) b.val * b.val = antiJ _ n := by simpa using hb
  have hconj : ∀ x : GLw n w, b * x * b⁻¹ ∈ UL n w ↔ x ∈ UJ (cj w) (antiJ _ n) := fun x => by
    rw [GlobalTheory.CompanionTheory.UnitaryWitt.UL_eq_of_not_split hw]
    exact GlobalTheory.CompanionTheory.UnitaryWitt.conj_mem_UJ_one_iff _ b x hb'
  have hback : b⁻¹ * g.1 * b ∈ UJ (cj w) (antiJ _ n) :=
    (hconj _).1 (by rw [show b * (b⁻¹ * g.1 * b) * b⁻¹ = g.1 by group]; exact g.2)
  have hbi := (GlobalTheory.LFun.KGL w n).inv_mem hbK
  have hO : Ov E w = intL (w.adicCompletion E) := Subring.ext fun _ => Iff.rfl
  have hKU : ∀ k ∈ KU (cj w) n, (k.1 : GLw n w) ∈ GlobalTheory.LFun.KGL w n := fun k hk => by
    have h : k.1 ∈ intPts (intL (w.adicCompletion E)).subtype (GU (cj w) n) := Subgroup.mem_subgroupOf.1 hk
    show k.1 ∈ (bc (Ov E w).subtype).range
    rw [hO]
    exact (Subgroup.mem_inf.1 h).2
  obtain ⟨d, t, ht, k₁, hk₁, k₂, hk₂, e⟩ := GlobalTheory.ChainOnto.CayleyVac.exists_cartanU hUI ⟨_, hback⟩
  have e' : b⁻¹ * g.1 * b = k₁.1 * t.1 * k₂.1 := congrArg Subtype.val e
  have hinv : (t.1)⁻¹ = wJ _ n * t.1 * wJ _ n := (wJ_conj_diag hUI.2.2.1 d t ht).symm

  set c : GLw n w := (k₂.1 : GLw n w)⁻¹ * wJ _ n * (k₁.1 : GLw n w)⁻¹ with hc
  have hcU : c ∈ UJ (cj w) (antiJ _ n) :=
    mul_mem (mul_mem (inv_mem k₂.2) (wJ_mem_GU _)) (inv_mem k₁.2)
  have hcK : c ∈ GlobalTheory.LFun.KGL w n :=
    mul_mem (mul_mem (inv_mem (hKU k₂ hk₂)) (wJ_mem_GLint _)) (inv_mem (hKU k₁ hk₁))
  have hx : b * c * b⁻¹ ∈ UL n w := (hconj _).2 hcU
  have hxK : (⟨b * c * b⁻¹, hx⟩ : UL n w) ∈ KL n w :=
    Subgroup.mem_subgroupOf.2 (mul_mem (mul_mem hbK hcK) hbi)
  refine ⟨_, hxK, _, hxK, Subtype.ext ?_⟩
  show (g.1)⁻¹ = b * c * b⁻¹ * g.1 * (b * c * b⁻¹)
  have hg : g.1 = b * (k₁.1 * t.1 * k₂.1) * b⁻¹ := by
    rw [← e']
    group
  have hti : (k₁.1 * t.1 * k₂.1 : GLw n w)⁻¹ = c * (k₁.1 * t.1 * k₂.1) * c := by
    rw [_root_.mul_inv_rev, _root_.mul_inv_rev, hinv, hc]
    group
  calc (g.1)⁻¹ = b * (k₁.1 * t.1 * k₂.1 : GLw n w)⁻¹ * b⁻¹ := by
        rw [hg]
        group
    _ = b * c * b⁻¹ * g.1 * (b * c * b⁻¹) := by
        rw [hti, hg]
        group

end GlobalTheory.CompanionTheory.InvDoubleCoset
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsOpenFreeFramePairs
section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw PositivityTheory.Rg.Rsw.L
open IsDedekindDomain NumberField
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.FreeFrames

theorem isOpen_free_frame_pairs {R : Type*} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
    (r t a : ℕ) (e : R) (he : e * e = e) (U : Set R) (hU : IsOpen U) (h1 : (1 : R) ∈ U)
    (hb : ∀ x ∈ U, ∃ b, x * b = e) :
    IsOpen {z : Matrix (Fin a) (Fin r) R × Matrix (Fin a) (Fin t) R |
      ∃ (L₁ : Matrix (Fin r) (Fin a) R) (L₂ : Matrix (Fin t) (Fin a) R),
        L₁ * (e • z.1) = e • 1 ∧ L₁ * (e • z.2) = 0 ∧ L₂ * (e • z.1) = 0 ∧ L₂ * (e • z.2) = e • 1} := by
  classical
  rw [isOpen_iff_mem_nhds]
  rintro z₀ ⟨L₁, L₂, h11, h12, h21, h22⟩
  let L : Matrix (Fin r ⊕ Fin t) (Fin a) R := Matrix.fromRows L₁ L₂
  let Z : Matrix (Fin a) (Fin r) R × Matrix (Fin a) (Fin t) R → Matrix (Fin a) (Fin r ⊕ Fin t) R :=
    fun z => Matrix.fromCols (e • z.1) (e • z.2)
  let C : Matrix (Fin a) (Fin r) R × Matrix (Fin a) (Fin t) R → Matrix (Fin r ⊕ Fin t) (Fin r ⊕ Fin t) R :=
    fun z => L * Z z + (1 - e) • (1 : Matrix (Fin r ⊕ Fin t) (Fin r ⊕ Fin t) R)
  have hone : (1 : Matrix (Fin r ⊕ Fin t) (Fin r ⊕ Fin t) R) = Matrix.fromBlocks 1 0 0 1 :=
    Matrix.fromBlocks_one.symm
  have hLZ : L * Z z₀ = e • (1 : Matrix (Fin r ⊕ Fin t) (Fin r ⊕ Fin t) R) := by
    simp only [L, Z]
    rw [Matrix.fromRows_mul_fromCols, h11, h12, h21, h22, hone, Matrix.fromBlocks_smul]
    simp only [smul_zero]
  have hC0 : C z₀ = 1 := by
    simp only [C]
    rw [hLZ, ← add_smul]
    simp
  have hZc : Continuous Z := by
    refine continuous_matrix fun i j => ?_
    cases j with
    | inl j =>
      have h : Continuous fun z : Matrix (Fin a) (Fin r) R × Matrix (Fin a) (Fin t) R => e * z.1 i j :=
        Continuous.mul continuous_const (continuous_fst.matrix_elem i j)
      simpa [Z] using h
    | inr j =>
      have h : Continuous fun z : Matrix (Fin a) (Fin r) R × Matrix (Fin a) (Fin t) R => e * z.2 i j :=
        Continuous.mul continuous_const (continuous_snd.matrix_elem i j)
      simpa [Z] using h
  have hCc : Continuous C := by
    exact (continuous_const.matrix_mul hZc).add continuous_const
  have hd : Continuous fun z => (C z).det := hCc.matrix_det
  have hnhds : (fun z => (C z).det) ⁻¹' U ∈ 𝓝 z₀ := by
    refine (hU.preimage hd).mem_nhds ?_
    simpa [Set.mem_preimage, hC0] using h1
  refine Filter.mem_of_superset hnhds ?_
  intro z hz
  obtain ⟨b, hb'⟩ := hb _ hz
  have hLz : L * Z z = C z - (1 - e) • (1 : Matrix (Fin r ⊕ Fin t) (Fin r ⊕ Fin t) R) := by
    simp only [C, add_sub_cancel_right]
  have hee : e * (1 - e) = 0 := by rw [mul_sub, he, mul_one, sub_self]
  have key : ((e * b) • ((C z).adjugate * L)) * Z z = e • (1 : Matrix (Fin r ⊕ Fin t) (Fin r ⊕ Fin t) R) := by
    rw [Matrix.smul_mul, Matrix.mul_assoc, hLz, Matrix.mul_sub, Matrix.adjugate_mul, Matrix.mul_smul,
      Matrix.mul_one, smul_sub, smul_smul, smul_smul]
    have h2 : e * b * (1 - e) = 0 := by
      rw [mul_right_comm, hee, zero_mul]
    have h3 : e * b * (C z).det = e := by
      rw [mul_assoc, mul_comm b, hb', he]
    rw [h2, h3, zero_smul, sub_zero]
  set L' := (e * b) • ((C z).adjugate * L) with hL'
  have key' : Matrix.fromBlocks (L'.toRows₁ * (e • z.1)) (L'.toRows₁ * (e • z.2))
      (L'.toRows₂ * (e • z.1)) (L'.toRows₂ * (e • z.2)) =
      Matrix.fromBlocks (e • 1) 0 0 (e • 1) := by
    rw [← Matrix.fromRows_mul_fromCols, Matrix.fromRows_toRows]
    have := key
    simp only [Z] at this
    rw [this, hone, Matrix.fromBlocks_smul]
    simp only [smul_zero]
  obtain ⟨a1, a2, a3, a4⟩ := Matrix.fromBlocks_inj.1 key'
  exact ⟨L'.toRows₁, L'.toRows₂, a1, a2, a3, a4⟩

theorem isOpen_free : ∀ (D : D7) (r t a : ℕ) (e : AE D), e * e = e →
    (∃ U : Set (AE D), IsOpen U ∧ 1 ∈ U ∧ ∀ x ∈ U, ∃ b, x * b = e) →
    IsOpen {z : Mx D a r × Mx D a t | Free e (e • z.1, e • z.2)} := by
  rintro D r t a e he ⟨U, hU, h1, hb⟩
  exact isOpen_free_frame_pairs r t a e he U hU h1 hb

end GlobalTheory.CompanionTheory.FreeFrames
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsotropicFramesSumByOrbit
section
noncomputable section

namespace GlobalTheory.CompanionTheory.WeilSiegel.HypStep.Unf

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free GlobalTheory.CompanionTheory.WeilSiegel.HypStep
open GlobalTheory.CompanionTheory.SW.ThetaStage

theorem linearIndependent_gact {F E : Type} [Field F] [Field E] [Algebra F E] (σ : E →ₐ[F] E)
    {M n : ℕ} {J : Matrix (Fin M) (Fin M) E} (g : UJ (σ : E →+* E) J) {X : Fin n → Fin M → E}
    (hX : LinearIndependent E X) : LinearIndependent E (gact σ g X) := by
  have hker : LinearMap.ker
      (Matrix.mulVecLin ((g : GL (Fin M) E) : Matrix (Fin M) (Fin M) E)) = ⊥ := by
    refine LinearMap.ker_eq_bot.2 fun x y h => ?_
    have h1 : gact σ g (fun _ : Fin 1 => x) = gact σ g (fun _ : Fin 1 => y) :=
      funext fun _ => h
    have h2 := congrArg (gact σ g⁻¹) h1
    rw [gact_inv_gact, gact_inv_gact] at h2
    exact congrFun h2 0
  have h3 : gact σ g X =
      (Matrix.mulVecLin ((g : GL (Fin M) E) : Matrix (Fin M) (Fin M) E)) ∘ X := by
    funext a
    rfl
  rw [h3]
  exact hX.map' (Matrix.mulVecLin ((g : GL (Fin M) E) : Matrix (Fin M) (Fin M) E)) hker

theorem gact_mem_framesE {F E : Type} [Field F] [Field E] [Algebra F E] (σ : E →ₐ[F] E)
    {M n : ℕ} {J : Matrix (Fin M) (Fin M) E} (g : UJ (σ : E →+* E) J)
    {T : Matrix (Fin n) (Fin n) E} {X : Fin n → Fin M → E} (hX : X ∈ framesE σ J T) :
    gact σ g X ∈ framesE σ J T :=
  ⟨linearIndependent_gact σ g hX.1, (gramE_gact σ g X).trans hX.2⟩

theorem tsum_framesOne : ∀ (F E : Type) [Field F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) (M : ℕ) (J : Matrix (Fin M) (Fin M) E) (n : ℕ) (rr : framesE σ (hypOne J) (0 : Matrix (Fin 1) (Fin 1) E) → UJ (σ : E →+* E) (hypOne J)), (∀ q, gact σ (rr q) q.1 = e0 E M) → ∀ f : (Fin (n + 1) → Fin (M + 2) → E) → ℝ≥0∞, ∑' X : framesE σ (hypOne J) (0 : Matrix (Fin (n + 1)) (Fin (n + 1)) E), f X.1 = ∑' q : framesE σ (hypOne J) (0 : Matrix (Fin 1) (Fin 1) E), ∑' X : framesOne σ J n, f (gact σ (rr q)⁻¹ X.1) := by
  intro F E _ _ _ σ M J n rr hrr f
  have hrow : ∀ (q : framesE σ (hypOne J) (0 : Matrix (Fin 1) (Fin 1) E))
      (X : framesOne σ J n), gact σ (rr q)⁻¹ X.1 0 = q.1 0 := by
    intro q X
    have h := congrArg (gact σ (rr q)⁻¹) (hrr q)
    rw [gact_inv_gact] at h
    have h0 := congrFun h 0
    have hX : X.1 0 = e0 E M 0 := X.2.2
    change ((((rr q)⁻¹ : UJ (σ : E →+* E) (hypOne J)) : GL (Fin (M + 2)) E) :
      Matrix (Fin (M + 2)) (Fin (M + 2)) E) *ᵥ X.1 0 = q.1 0
    rw [hX, h0]
    rfl
  let m : framesE σ (hypOne J) (0 : Matrix (Fin 1) (Fin 1) E) × framesOne σ J n →
      framesE σ (hypOne J) (0 : Matrix (Fin (n + 1)) (Fin (n + 1)) E) :=
    fun p => ⟨gact σ (rr p.1)⁻¹ p.2.1, gact_mem_framesE σ _ p.2.2.1⟩
  have hinj : Function.Injective m := by
    rintro ⟨q, X⟩ ⟨q', X'⟩ h
    have h1 : gact σ (rr q)⁻¹ X.1 = gact σ (rr q')⁻¹ X'.1 := congrArg Subtype.val h
    have hq : q = q' := by
      apply Subtype.ext
      funext a
      have ha : a = 0 := Subsingleton.elim _ _
      subst ha
      rw [← hrow q X, ← hrow q' X', h1]
    subst hq
    have h2 := congrArg (gact σ (rr q)) h1
    rw [gact_gact_inv, gact_gact_inv] at h2
    exact Prod.ext rfl (Subtype.ext h2)
  have hsurj : Function.Surjective m := by
    rintro ⟨Y, hY⟩
    have hq : (fun _ : Fin 1 => Y 0) ∈
        framesE σ (hypOne J) (0 : Matrix (Fin 1) (Fin 1) E) := by
      refine ⟨hY.1.comp (fun _ : Fin 1 => (0 : Fin (n + 1)))
        (Function.injective_of_subsingleton _), ?_⟩
      funext a b
      exact congrFun (congrFun hY.2 0) 0
    let q : framesE σ (hypOne J) (0 : Matrix (Fin 1) (Fin 1) E) := ⟨_, hq⟩
    have hX : gact σ (rr q) Y ∈ framesOne σ J n :=
      ⟨gact_mem_framesE σ _ hY, congrFun (hrr q) 0⟩
    exact ⟨(q, ⟨_, hX⟩), Subtype.ext (gact_inv_gact σ (rr q) Y)⟩
  let e := Equiv.ofBijective m ⟨hinj, hsurj⟩
  rw [← e.tsum_eq (fun Y => f Y.1), ENNReal.tsum_prod']
  rfl

end GlobalTheory.CompanionTheory.WeilSiegel.HypStep.Unf
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JacquetMultiplicityOfEquiv
section
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.Cos

namespace GlobalTheory.CompanionTheory.JacquetCongr

theorem jm_congr_of_equiv : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {h N : ℕ} (x : Fin h → IrrGL k) (hd : ∑ a, (x a).1 = N) {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] (π : Representation ℂ (GL (Fin N) k) V) (σ : Representation ℂ (GL (Fin N) k) W), Nonempty (π.Equiv σ) → jm x hd π = jm x hd σ := by
  intro k _ _ _ _ h N x hd V W _ _ _ _ π σ ⟨φ⟩
  exact jhMult_congr_right _ (GlobalTheory.SmGL.Exponents.jacEquiv _ φ)

end GlobalTheory.CompanionTheory.JacquetCongr
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JacquetMultiplicityPosOfSocleStatement
section
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.jacquet_multiplicity_pos_of_socle : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (h N : ℕ) (x : Fin h → IrrGL k) (hd : ∑ a, (x a).1 = N) {V : Type} [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V), IsSmooth π → (∀ a, 0 < (x a).1) → IsSocle π (prodIrr x hd) → Zc.jm x hd π ≠ 0 := by
  first | exact @GlobalTheory.CompanionTheory.SocleFrob.jm_ne_zero_of_isSocle | exact GlobalTheory.CompanionTheory.SocleFrob.jm_ne_zero_of_isSocle | (intros; apply GlobalTheory.CompanionTheory.SocleFrob.jm_ne_zero_of_isSocle <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JacquetMultiplicityTransitiveLeStatement
section
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.Cos
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.jacquet_multiplicity_transitive_le : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], GlobalTheory.Published.IrreducibleAdmissibleGL → ∀ {g N : ℕ} (y : Fin g → IrrGL k) (hy : ∑ b, (y b).1 = N) (Wb : Fin g → List (IrrGL k)) {V : Type} [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V), IsSmooth π → HasFiniteLength π → (∀ b, ∑ a, ((Wb b).get a).1 = (y b).1) → jm y hy π * ∏ b, jmL (Wb b) (y b).rep ≤ jmL (List.ofFn Wb).flatten π := by
  first | exact @GlobalTheory.CompanionTheory.CsStages.jm_mul_prod_jmL_le | exact GlobalTheory.CompanionTheory.CsStages.jm_mul_prod_jmL_le | (intros; apply GlobalTheory.CompanionTheory.CsStages.jm_mul_prod_jmL_le <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LamIsLatticeStatement
section
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.CompanionTheory.SiegelND.Integ.Hua GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.HS
open scoped Matrix

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lam_is_lattice : ∀ (K : Type) [Field K] [NumberField K] (m : ℕ) (c : Matrix (Fin m) (Fin m) K), IsLat (lam c) := by
  first | exact @GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.HS.isLat_lam_of_matrix | exact GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.HS.isLat_lam_of_matrix | (intros; apply GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.HS.isLat_lam_of_matrix <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalOrderTwoPrimesAlmostAllStatement
section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free GlobalTheory.CompanionTheory.WeilSiegel.HypStep
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_order_two_primes_almost_all : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E), ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite, ∀ O : Subring (Fv F v ⊗[F] E), (∀ y, y ∈ O ↔ ∀ k, (Algebra.TensorProduct.basis (Fv F v) b).repr y k ∈ v.adicCompletionIntegers F) → ∃ π₁ π₂ : O, (∀ P : Ideal O, P.IsMaximal → P = Ideal.span {π₁} ∨ P = Ideal.span {π₂}) ∧ IsUnit (π₁ : Fv F v ⊗[F] E) ∧ IsUnit (π₂ : Fv F v ⊗[F] E) := by
  first | exact @GlobalTheory.CompanionTheory.SW.QuadMaxIdeal.maximal_ideals | exact GlobalTheory.CompanionTheory.SW.QuadMaxIdeal.maximal_ideals | (intros; apply GlobalTheory.CompanionTheory.SW.QuadMaxIdeal.maximal_ideals <;> assumption)
end

