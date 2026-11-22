import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0868
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.Bundle0009
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZarhinDualPolarisation.FlatFiniteFibres.FlatOfFibresFinite
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0869
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsSmoothHermCombLine
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterRed
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1002
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0021
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0610
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0592
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0867
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0593
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0606
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0049
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0588
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.LeviMatchingWords.MatchLM
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0642
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0466
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HeckeCosetSumCompact
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0495
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0699
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0870

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CompactLevelExistsStatement
section
open NumberField GlobalTheory.BCT Formalism.L2.Host PositivityTheory.Rg.BcB.F.Ex0 PositivityTheory.Rg.Bc.ArchbcB.B
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.compact_level_exists : KEx := by
  first | exact @GlobalTheory.CompanionTheory.KExLevel.kEx | exact GlobalTheory.CompanionTheory.KExLevel.kEx | (intros; apply GlobalTheory.CompanionTheory.KExLevel.kEx <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EpiOfFiniteFlatStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.epi_of_finite_flat : PositivityTheory.Tls2.Zar3.Ch1.EpiOfFF := by
  first | exact @GlobalTheory.CompanionTheory.Dblock.epiOfFF | exact GlobalTheory.CompanionTheory.Dblock.epiOfFF | (intros; apply GlobalTheory.CompanionTheory.Dblock.epiOfFF <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FactorThroughFiniteFlatStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.factor_through_finite_flat : PositivityTheory.Tls2.Zar3.Ch1.FactorThroughFF := by
  first | exact @GlobalTheory.CompanionTheory.FlatFactor.factorThroughFF | exact GlobalTheory.CompanionTheory.FlatFactor.factorThroughFF | (intros; apply GlobalTheory.CompanionTheory.FlatFactor.factorThroughFF <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteOfFiniteFibresStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_of_finite_fibres : PositivityTheory.Tls2.Zar3.Ch1.FiniteOfFibres := by
  first | exact @GlobalTheory.CompanionTheory.AbFibre.finiteOfFibres | exact GlobalTheory.CompanionTheory.AbFibre.finiteOfFibres | (intros; apply GlobalTheory.CompanionTheory.AbFibre.finiteOfFibres <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FlatOfFibresFiniteStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flat_of_fibres_finite : PositivityTheory.Tls2.Zar3.Ch1.FlatOfFibresFinite := by
  first | exact @GlobalTheory.CompanionTheory.FlatFib.flatOfFibresFinite | exact GlobalTheory.CompanionTheory.FlatFib.flatOfFibresFinite | (intros; apply GlobalTheory.CompanionTheory.FlatFib.flatOfFibresFinite <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HypersurfaceComplexPointsMeasurableNullStatement
section
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry Limits TopologicalSpace MvPolynomial MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.ProjSpace GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.Points GlobalTheory.ChartGlue
open GroundTheory.Arith.SchemeCoh GroundTheory.Arith.SchemeCoh.ProjSpace
open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open GlobalTheory.CompanionTheory.MPDict GlobalTheory.CompanionTheory.MixZ
open ReciprocityTheory.ChartRestriction.G.Geo (mcPts IsMultiHomog SameOrbit)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hypersurface_complex_points_measurable_null : ∀ (m : ℕ) (n : Fin (m + 1) → ℕ) (X : Scheme.{0}) [IsIntegral X] (i : X ⟶ MP ℤ m n) [IsClosedImmersion i] (D : ℕ)
    (f : Pol n) (a : Fin (m + 1) → ℕ), IsMultiHomog f a → f ∉ ptIdeal (i (genericPoint X)) →
    MeasurableSet {y : GlobalTheory.CxPts (i ≫ mpStr ℤ m n) σ₀ | ∃ z, IsUnder (PtsOver.map i rfl _ y) z ∧
      eval z (map (Int.castRingHom ℂ) f) = 0} ∧
    ∀ c : GlobalTheory.AlgChart (i ≫ mpStr ℤ m n) σ₀ D, volume (c.e.target ∩ c.e.symm ⁻¹'
      {y | ∃ z, IsUnder (PtsOver.map i rfl _ y) z ∧ eval z (map (Int.castRingHom ℂ) f) = 0}) = 0 := by
  first | exact @GlobalTheory.CompanionTheory.MixZ.zeroLocus_measurable_null | exact GlobalTheory.CompanionTheory.MixZ.zeroLocus_measurable_null | (intros; apply GlobalTheory.CompanionTheory.MixZ.zeroLocus_measurable_null <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IwahoriDoubleCosetFinite
section
open NumberField IsDedekindDomain Matrix Polynomial Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.CompanionTheory.IwDcosFin

theorem finite_image_mk_of_isCompact {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    {H : Subgroup G} (hH : IsOpen (H : Set G)) {C : Set G} (hC : IsCompact C) :
    ((QuotientGroup.mk : G → G ⧸ H) '' C).Finite := by
  obtain ⟨s, hs⟩ := hC.elim_finite_subcover (fun g : G => (fun x => g * x) '' (H : Set G))
    (fun g => (Homeomorph.mulLeft g).isOpenMap _ hH)
    (fun x _ => Set.mem_iUnion.2 ⟨x, 1, H.one_mem, mul_one x⟩)
  refine (s.finite_toSet.image (QuotientGroup.mk : G → G ⧸ H)).subset ?_
  rintro _ ⟨x, hx, rfl⟩
  obtain ⟨g, hg, hy⟩ : ∃ g ∈ s, g⁻¹ * x ∈ H := by
    simpa using hs hx
  exact ⟨g, hg, QuotientGroup.eq.2 hy⟩

theorem dcos_finite_support_iwGL : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (w : Pl E) (a : ℕ) (t : GLw a w),
    (Function.support fun q : GLw a w ⧸ iwGL a w => dcos a w t q.out).Finite ∧ IsOpen (iwGL a w : Set (GLw a w)) ∧
      IsCompact (iwGL a w : Set (GLw a w)) ∧ iwGL a w ≤ GlobalTheory.LFun.KGL w a ∧
      (iwGL a w).relIndex (GlobalTheory.LFun.KGL w a) ≠ 0 := by
  intro E _ _ _ w a t
  have hIo : IsOpen (iwGL a w : Set (GLw a w)) :=
    GlobalTheory.SmGL.IwahoriOnto.isOpen_iwahori (w.adicCompletion E) (Fin a)
  have hIc : IsCompact (iwGL a w : Set (GLw a w)) :=
    GlobalTheory.SmGL.IwahoriOnto.isCompact_iwahori (w.adicCompletion E) (Fin a)
  refine ⟨?_, hIo, hIc, GlobalTheory.CompanionTheory.IwLevels.iwGL_le_KGL w a,
    GlobalTheory.CompanionTheory.IwLevels.relIndex_ne_zero hIo (GlobalTheory.CompanionTheory.IwLevels.isCompact_KGL w a)⟩
  refine (finite_image_mk_of_isCompact hIo (GlobalTheory.CompanionTheory.IwFacts.isCompact_support_dcos w a t)).subset ?_
  intro q hq
  exact ⟨q.out, hq, QuotientGroup.out_eq' q⟩

end GlobalTheory.CompanionTheory.IwDcosFin
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.KernelFiniteFlatStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kernel_finite_flat : PositivityTheory.Tls2.Zar3.Ch1.KernelFinFlat := by
  first | exact @GlobalTheory.CompanionTheory.Ar.KerFF.kernelFinFlat | exact GlobalTheory.CompanionTheory.Ar.KerFF.kernelFinFlat | (intros; apply GlobalTheory.CompanionTheory.Ar.KerFF.kernelFinFlat <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MatchingUnitOf
section
noncomputable section

open NumberField IsDedekindDomain Matrix Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.LFun PositivityTheory.Rg.BcB.F.F5 PositivityTheory.Rg.BcB.F.Eig PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcN.F2 PositivityTheory.Rg.BcB.F.Tail PositivityTheory.Rg.Bc.ArchbcB.B PositivityTheory.Rg.BcB.F
open PositivityTheory.Rg.BcB.F.U (lpow lone)
open scoped Classical
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.CompanionTheory.MatchUnit

theorem hint_ind_conv {H : Type} [Group H] (K : Subgroup H) (y : H) :
    hint K (fun z => (K : Set H).indicator (1 : H → ℂ) z * (K : Set H).indicator (1 : H → ℂ) (z⁻¹ * y)) =
      (K : Set H).indicator (1 : H → ℂ) y := by
  by_cases hy : y ∈ K
  · have e : (fun z => (K : Set H).indicator (1 : H → ℂ) z * (K : Set H).indicator (1 : H → ℂ) (z⁻¹ * y)) =
        (K : Set H).indicator (1 : H → ℂ) := by
      funext z
      by_cases hz : z ∈ K
      · have hzy : z⁻¹ * y ∈ K := mul_mem (inv_mem hz) hy
        simp [Set.indicator_of_mem (show z ∈ (K : Set H) from hz),
          Set.indicator_of_mem (show z⁻¹ * y ∈ (K : Set H) from hzy)]
      · simp [Set.indicator_of_notMem (show z ∉ (K : Set H) from hz)]
    rw [e, GlobalTheory.CompanionTheory.FamClP.hint_ind, Set.indicator_of_mem (show y ∈ (K : Set H) from hy)]
    rfl
  · have e : (fun z => (K : Set H).indicator (1 : H → ℂ) z * (K : Set H).indicator (1 : H → ℂ) (z⁻¹ * y)) =
        fun _ => (0 : ℂ) := by
      funext z
      by_cases hz : z ∈ K
      · have hzy : z⁻¹ * y ∉ K := fun h => hy (by simpa using mul_mem hz h)
        simp [Set.indicator_of_notMem (show z⁻¹ * y ∉ (K : Set H) from hzy)]
      · simp [Set.indicator_of_notMem (show z ∉ (K : Set H) from hz)]
    rw [e, GlobalTheory.CompanionTheory.FamClP.hint_zero, Set.indicator_of_notMem (show y ∉ (K : Set H) from hy)]

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem blk_mem_KGL_iff {a b n : ℕ} (h : a + b = n) (w : Pl E) (m : GLw a w × GLw b w)
    (X : Multiplicative (Matrix (Fin a) (Fin b) (w.adicCompletion E))) :
    blk h w m (Multiplicative.toAdd X) ∈ GlobalTheory.LFun.KGL w n ↔ m ∈ K2 a b w ∧ X ∈ intMat a b w := by
  obtain ⟨hN, hM⟩ := GlobalTheory.CompanionTheory.LeviInt.comap_uN_and_map_sM E a b n h w
  have hdiag : ∀ c ∈ K2 a b w, blk h w c 0 ∈ GlobalTheory.LFun.KGL w n := fun c hc => hM ⟨c, hc, rfl⟩
  have hNK : ∀ Z, Z ∈ intMat a b w ↔ blk h w 1 (Multiplicative.toAdd Z) ∈ GlobalTheory.LFun.KGL w n := by
    intro Z
    rw [← hN, Subgroup.mem_comap, Subgroup.mem_subgroupOf, GlobalTheory.LeviFubini.uN_val]
  have hsplit : blk h w m (Multiplicative.toAdd X) = blk h w m 0 * blk h w 1 (Multiplicative.toAdd X) := by
    have := GlobalTheory.CompanionTheory.IntDec.blk_add h w m 0 (Multiplicative.toAdd X)
    simpa using this
  constructor
  · intro hb
    have hm : m ∈ K2 a b w := by
      have h2 := GlobalTheory.LeviFubini.levH_mem_KGL_of_mem E a b n h w
        ⟨blk h w m (Multiplicative.toAdd X), GlobalTheory.LeviFubini.blk_mem h w m _⟩ hb
      rw [GlobalTheory.LeviFubini.levH_blk] at h2
      exact Subgroup.mem_prod.2 h2
    refine ⟨hm, (hNK X).2 ?_⟩
    have e : blk h w 1 (Multiplicative.toAdd X) = (blk h w m 0)⁻¹ * blk h w m (Multiplicative.toAdd X) := by
      rw [hsplit]
      group
    rw [e]
    exact mul_mem (inv_mem (hdiag m hm)) hb
  · rintro ⟨hm, hX⟩
    rw [hsplit]
    exact mul_mem (hdiag m hm) ((hNK X).1 hX)

variable {n : ℕ}

theorem val_toSub {w : Pl E} (hU : UL n w = ⊤) (y : GLw n w) : ((toSub (UL n w) y : UL n w) : GLw n w) = y := by
  have hy : y ∈ UL n w := hU ▸ Subgroup.mem_top y
  simp [toSub, hy]

theorem lone_toSub {w : Pl E} (hU : UL n w = ⊤) (y : GLw n w) :
    lone (KL n w) (toSub (UL n w) y) = if y ∈ GlobalTheory.LFun.KGL w n then 1 else 0 := by
  rw [GlobalTheory.CompanionTheory.UnitaryWord.lone_KL]
  unfold GlobalTheory.CompanionTheory.UnitaryWord.unitFn
  by_cases hy : y ∈ GlobalTheory.LFun.KGL w n
  · have : toSub (UL n w) y ∈ (KL n w : Set (UL n w)) := by
      show toSub (UL n w) y ∈ KL n w
      rw [KL, Subgroup.mem_subgroupOf, val_toSub hU]
      exact hy
    rw [if_pos hy, Set.indicator_of_mem this]
    rfl
  · have : toSub (UL n w) y ∉ (KL n w : Set (UL n w)) := by
      intro h'
      have h'' : toSub (UL n w) y ∈ KL n w := h'
      rw [KL, Subgroup.mem_subgroupOf, val_toSub hU] at h''
      exact hy h''
    rw [if_neg hy, Set.indicator_of_notMem this]

theorem ct_lone {a b : ℕ} (h : a + b = n) {w : Pl E} (hU : UL n w = ⊤) (m : GLw a w × GLw b w) :
    ct h w (fun y => lone (KL n w) (toSub (UL n w) y)) m = if m ∈ K2 a b w then 1 else 0 := by
  have hk : ∀ X : Multiplicative (Matrix (Fin a) (Fin b) (w.adicCompletion E)),
      GlobalTheory.BCT.avg (fun k : GlobalTheory.LFun.KGL w n => lone (KL n w) (toSub (UL n w)
        ((k : GLw n w)⁻¹ * blk h w m (Multiplicative.toAdd X) * k))) =
      if m ∈ K2 a b w ∧ X ∈ intMat a b w then 1 else 0 := by
    intro X
    have e : (fun k : GlobalTheory.LFun.KGL w n => lone (KL n w) (toSub (UL n w)
        ((k : GLw n w)⁻¹ * blk h w m (Multiplicative.toAdd X) * k))) =
        fun _ => if m ∈ K2 a b w ∧ X ∈ intMat a b w then (1 : ℂ) else 0 := by
      funext k
      rw [lone_toSub hU]
      have hiff : (k : GLw n w)⁻¹ * blk h w m (Multiplicative.toAdd X) * k ∈ GlobalTheory.LFun.KGL w n ↔
          m ∈ K2 a b w ∧ X ∈ intMat a b w := by
        rw [← blk_mem_KGL_iff h w m X, Subgroup.mul_mem_cancel_right _ k.2,
          Subgroup.mul_mem_cancel_left _ (inv_mem k.2)]
      simp only [hiff]
    rw [e]
    exact GlobalTheory.CompanionTheory.CtS.avg_const _
  unfold ct
  simp only [hk]
  by_cases hm : m ∈ K2 a b w
  · obtain ⟨h1, h2⟩ := Subgroup.mem_prod.1 hm
    have hv : Valued.v (m.1.val.det ^ b / m.2.val.det ^ a) = 1 := by
      rw [map_div₀, map_pow, map_pow, GlobalTheory.CompanionTheory.CtHecke.v_det h1, GlobalTheory.CompanionTheory.CtHecke.v_det h2]
      simp
    have habs : absHalf w (m.1.val.det ^ b / m.2.val.det ^ a) = 1 := by
      unfold absHalf
      rw [GlobalTheory.CompanionTheory.CtHecke.ordL_eq_zero hv]
      simp
    have e : (fun X : Multiplicative (Matrix (Fin a) (Fin b) (w.adicCompletion E)) =>
        if m ∈ K2 a b w ∧ X ∈ intMat a b w then (1 : ℂ) else 0) =
        (intMat a b w : Set _).indicator 1 := by
      funext X
      by_cases hX : X ∈ intMat a b w
      · simp [hm, hX, Set.indicator_of_mem (show X ∈ (intMat a b w : Set _) from hX)]
      · simp [hX, Set.indicator_of_notMem (show X ∉ (intMat a b w : Set _) from hX)]
    rw [e, GlobalTheory.CompanionTheory.FamClP.hint_ind, habs, if_pos hm, mul_one]
  · have e : (fun X : Multiplicative (Matrix (Fin a) (Fin b) (w.adicCompletion E)) =>
        if m ∈ K2 a b w ∧ X ∈ intMat a b w then (1 : ℂ) else 0) = fun _ => 0 := by
      funext X
      simp [hm]
    rw [e, GlobalTheory.CompanionTheory.FamClP.hint_zero, if_neg hm, mul_zero]

theorem ctMu_lone {a b : ℕ} (h : a + b = n) {w : Pl E} (hU : UL n w = ⊤) (μ : (w.adicCompletion E)ˣ →* ℂˣ)
    (hμ : ∀ u : (w.adicCompletion E)ˣ, ordL (u : w.adicCompletion E) = 0 → μ u = 1) :
    ctMu h w μ (lone (KL n w)) = idem (K2 a b w) := by
  funext m
  unfold ctMu
  rw [ct_lone h hU]
  by_cases hm : m ∈ K2 a b w
  · have h1 : μ (-1) = 1 := by
      refine hμ _ (GlobalTheory.CompanionTheory.CtHecke.ordL_eq_zero ?_)
      simp
    have hu := GlobalTheory.CompanionTheory.CtHecke.mu_unit hμ hm
    have e : μ ((-1) ^ (a * b) * GeneralLinearGroup.det m.1 ^ b * GeneralLinearGroup.det m.2 ^ a) = 1 := by
      rw [mul_assoc, map_mul, hu, map_pow, h1]
      simp
    rw [e, if_pos hm]
    unfold idem
    rw [Set.indicator_of_mem (show m ∈ (K2 a b w : Set _) from hm), Subgroup.relIndex_self]
    simp
  · rw [if_neg hm, mul_zero]
    unfold idem
    rw [Set.indicator_of_notMem (show m ∉ (K2 a b w : Set _) from hm)]

theorem lpow_lone_one {w : Pl E} : lpow (KL n w) (lone (KL n w)) 1 = (KL n w : Set (UL n w)).indicator 1 := by
  funext y
  show lconv (lone (KL n w)) (lone (KL n w)) y = _
  rw [GlobalTheory.CompanionTheory.UnitaryWord.lone_KL]
  exact hint_ind_conv (KL n w) y

theorem isHecke_lone_KL (hE : Unr E) {w : Pl E} : IsHecke (KL n w) (lone (KL n w)) := by
  rw [GlobalTheory.CompanionTheory.UnitaryWord.lone_KL]
  refine ⟨HasCompactSupport.intro (GlobalTheory.CompanionTheory.SphLine.isCompact_KL hE n w) fun x hx =>
    Set.indicator_of_notMem hx _, fun k hk x => ?_⟩
  have h1 : k * x ∈ KL n w ↔ x ∈ KL n w := Subgroup.mul_mem_cancel_left _ hk
  have h2 : x * k ∈ KL n w ↔ x ∈ KL n w := Subgroup.mul_mem_cancel_right _ hk
  unfold GlobalTheory.CompanionTheory.UnitaryWord.unitFn
  by_cases hx : x ∈ KL n w
  · exact ⟨by rw [Set.indicator_of_mem (show k * x ∈ (KL n w : Set _) from h1.2 hx),
      Set.indicator_of_mem (show x ∈ (KL n w : Set _) from hx)]; rfl,
      by rw [Set.indicator_of_mem (show x * k ∈ (KL n w : Set _) from h2.2 hx),
      Set.indicator_of_mem (show x ∈ (KL n w : Set _) from hx)]; rfl⟩
  · exact ⟨by rw [Set.indicator_of_notMem (show k * x ∉ (KL n w : Set _) from fun h => hx (h1.1 h)),
      Set.indicator_of_notMem (show x ∉ (KL n w : Set _) from hx)],
      by rw [Set.indicator_of_notMem (show x * k ∉ (KL n w : Set _) from fun h => hx (h2.1 h)),
      Set.indicator_of_notMem (show x ∉ (KL n w : Set _) from hx)]⟩

theorem isOpen_levelSubgroup' (a b : ℕ) (w : Pl E) : IsOpen (K2 a b w : Set (GLw a w × GLw b w)) := by
  have e : (K2 a b w : Set (GLw a w × GLw b w)) =
      (GlobalTheory.LFun.KGL w a : Set (GLw a w)) ×ˢ (GlobalTheory.LFun.KGL w b : Set (GLw b w)) := rfl
  rw [e]
  exact (GlobalTheory.LFun.SatCompare.isOpen_isCompact_KGL w a).1.prod (GlobalTheory.LFun.SatCompare.isOpen_isCompact_KGL w b).1

theorem matchLMUnitOf : PositivityTheory.Rg.BcB.F.MLM.MatchLMUnitOf := by
  intro hI hS hId E _ _ _ hE n d _ a ha w hwB hgood
  have hT : w ∉ d.T := fun h => hwB (by simp [LocData.B, h])
  have hS₀ : w ∉ d.S₀ := fun h => hwB (by simp [LocData.B, h])
  have hBad : w ∉ d.Bad := fun h => hwB (by simp [LocData.B, h])
  have hP : w ∉ d.P := by simp [LocData.P, hT, hS₀]
  have hlev : d.lev a w = K2 a (n - a) w := by
    unfold LocData.lev
    rw [if_neg hT, if_neg (by simp [hS₀, hBad])]
  have htr : (d.eL a).tr d.P d.one w = idem (K2 a (n - a) w) := by
    unfold LM.tr
    rw [if_neg hP]
    show idem (d.lev a w) = _
    rw [hlev]
  rw [htr]
  by_cases hw : IsSplitAt w
  · rw [if_pos hw]
    obtain ⟨-, -, -, -, hμ⟩ := hgood hw
    have hU : UL n w = ⊤ := if_pos hw
    have hc := ctMu_lone (Nat.add_sub_cancel' ha) hU (d.μ w) hμ
    have h : Match n a (n - a) w (d.μ w) (lpow (KL n w) (lone (KL n w)) 1)
        (mconv (ctMu (Nat.add_sub_cancel' ha) w (d.μ w) (lone (KL n w)))
          (ctMu (Nat.add_sub_cancel' ha) w (d.μ w) (lone (KL n w)))) :=
      hS E n a ha w hw (d.μ w) hμ (lone (KL n w)) (isHecke_lone_KL hE) 1 le_rfl
    obtain ⟨hH, -, hU'⟩ := hId E a (n - a) w (K2 a (n - a) w) (isOpen_levelSubgroup' a (n - a) w) le_rfl
    rw [hc, (hU' _ hH).1, lpow_lone_one] at h
    exact h
  · rw [if_neg hw]
    exact hI E hE w hw n a ha

end GlobalTheory.CompanionTheory.MatchUnit

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MeasureZeroSetAvoidedByHolomorphicMapStatement
section
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry Limits TopologicalSpace MvPolynomial MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.ProjSpace GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.Points GlobalTheory.ChartGlue
open GroundTheory.Arith.SchemeCoh GroundTheory.Arith.SchemeCoh.ProjSpace
open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open GlobalTheory.CompanionTheory.MPDict GlobalTheory.CompanionTheory.MixZ
open ReciprocityTheory.ChartRestriction.G.Geo (mcPts IsMultiHomog SameOrbit)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.measure_zero_set_avoided_by_holomorphic_map : ∀ {k : Type} [CommRing k] {X : Scheme.{0}} {q : X ⟶ Sp k} {σ : k →+* ℂ} {D : ℕ} {T : Type}
    [TopologicalSpace T] (A : FinHolAtlas D T) (F : T → GlobalTheory.CxPts q σ) (hF : Continuous F),
    (∀ (W : X.Opens) (f : Γ(X, W)), A.HoloOn (F ⁻¹' ptsIn q σ W) (ev q σ W f ∘ F)) →
    ∀ (Z : Set (GlobalTheory.CxPts q σ)), MeasurableSet Z →
    (∀ c : GlobalTheory.AlgChart q σ D, volume (c.e.target ∩ c.e.symm ⁻¹' Z) = 0) →
    (∀ y, y ∉ Z → ∃ x, F x = y) → (∀ x x', F x ∉ Z → F x = F x' → x = x') →
    ∀ {B : LB X} (φ : GlobalTheory.Weight q σ B), φ.IsCInf → ∀ (ε : ℤˣ) (K : Fin A.n → Set (Fin D → ℂ)),
    (∀ j, IsCompact (K j)) → (∀ j, K j ⊆ (A.chart j).target) →
    (∀ x, ∃ j, ∃ u ∈ K j, (A.chart j).symm u = x) →
    φ.chernPart D ε ≤ ∑ j, Measure.map (F ∘ (A.chart j).symm)
      ((volume.restrict (K j \ (F ∘ (A.chart j).symm) ⁻¹' Z)).withDensity fun u =>
        ENNReal.ofReal |locDens A (fun _ => φ.locPot.pullback F hF) j u|) := by
  first | exact @GlobalTheory.CompanionTheory.ArchDom.chernPart_le_sum_map | exact GlobalTheory.CompanionTheory.ArchDom.chernPart_le_sum_map | (intros; apply GlobalTheory.CompanionTheory.ArchDom.chernPart_le_sum_map <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MuCharacterExistsStatement
section
open NumberField GlobalTheory.BCT Formalism.L2.Host PositivityTheory.Rg.BcB.F.Ex0 PositivityTheory.Rg.Bc.ArchbcB.B
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mu_character_exists : (∀ (E : Type) [Field E] [NumberField E] [IsCMField E], GlobalTheory.BCT.Unr E → ∃ (μ : HChar E) (e : InfinitePlace E → ℤ), IsMu μ e) → MuEx := by
  first | exact @GlobalTheory.CompanionTheory.MuOpen.muEx_of_exists | exact GlobalTheory.CompanionTheory.MuOpen.muEx_of_exists | (intros; apply GlobalTheory.CompanionTheory.MuOpen.muEx_of_exists <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SectionExistsStatement
section
open NumberField GlobalTheory.BCT Formalism.L2.Host PositivityTheory.Rg.BcB.F.Ex0 PositivityTheory.Rg.Bc.ArchbcB.B
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sec_ex : SecEx := by
  first | exact @GlobalTheory.CompanionTheory.SecThrough.secEx | exact GlobalTheory.CompanionTheory.SecThrough.secEx | (intros; apply GlobalTheory.CompanionTheory.SecThrough.secEx <;> assumption)
end

