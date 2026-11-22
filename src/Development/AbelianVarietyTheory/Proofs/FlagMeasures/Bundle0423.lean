import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ChartGen
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.MaxMass
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.SiegelMassRatioOfLI
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.Bundle0045
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.Bundle0027
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.DiscEquiv
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MaximalHermitianLatticeLocalStructureDiscriminan
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.Bundle0030
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.ExistsLatticeOfFibLocNeZeroGood
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.Bundle0022
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.ExistsLocalData
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.MemSmulOfMemSmulLocF
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.NGAnalytic
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.DataInst
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.InVolumesAtOfSWS
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.GlobSet
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.StepNormOneOfLeaves
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.Bundle0034
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.Bundle0030
import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.Bundle0006
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.NGData
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.TermLoc
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0013
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0418
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0310
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0037
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0420

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.JordanExponentsMaximalHermitianLatticeBadPrime
section
open NumberField GlobalTheory.Mass Formalism.HermitianLatticesTheory Formalism.HermitianLattices.Ext.L3 Formalism.L2.SG.Pf.Cnt
open scoped Classical

noncomputable section
namespace GlobalTheory.MaxLatExpo

theorem main : ∀ (K F V : Type) [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V], IsCMUnram K → IsFixF K F → ∀ h : V →ₗ⋆[K] V →ₗ[K] K, h.IsSymm → IsTotPosDef h → ∀ M : Submodule (𝓞 K) V, IsMaxLat h M → ∀ P ∈ badP h M, ∀ (b : Fin (Module.finrank K (⊤ : Submodule K V)) → V) (a : Fin (Module.finrank K (⊤ : Submodule K V)) → 𝓞 F), IsJordanIn h ⊤ M (P.comap (algebraMap (𝓞 F) (𝓞 K))) b a → ∃ i, vF (P.comap (algebraMap (𝓞 F) (𝓞 K))) (a i) = 1 ∧ ∀ j, j ≠ i → vF (P.comap (algebraMap (𝓞 F) (𝓞 K))) (a j) = 0 := by
  intro K F V _ _ _ _ _ _ _ _ _ _ _ hK hF h hs hd M hM P hPb b a hJ
  have hP : P.IsMaximal := hPb.1
  have hp : (P.comap (algebraMap (𝓞 F) (𝓞 K))).IsMaximal :=
    Ideal.isMaximal_comap_of_isIntegral_of_isMaximal P
  have hpp := hp.isPrime
  have hl : ∀ L : Submodule (𝓞 K) V, locF (P.comap (algebraMap (𝓞 F) (𝓞 K))) L = loc (K := K) P L :=
    fun L => locF_eq_loc hK hF hP L
  obtain ⟨-, -, -, hloc⟩ := GlobalTheory.MaxLatStruct.main K V h hK hs (UnimodularLocalization.nondegenerate hd) M hM
  obtain ⟨hconj, -, -, x, hxM, ⟨a0, ha0x, ha0P, ha0P2⟩, hstr⟩ := hloc P hPb
  have hext : extP K (P.comap (algebraMap (𝓞 F) (𝓞 K))) = P := ThirdPropositionSlot.map_comap_eq_of_inert hK hF hP hconj
  obtain ⟨hbX, hspan, horth, hdiag, ha⟩ := hJ
  have hL : IsLatIn (⊤ : Submodule K V) M := ⟨hM.1.1.fg, hM.1.1.span_eq_top⟩
  have hdI : dualIn h ⊤ M = dual h M := by
    ext z; simp [dualIn]
  set p := P.comap (algebraMap (𝓞 F) (𝓞 K)) with hpdef
  set S := HU.SP K p with hSdef
  have hB : ∀ z, z ∈ locF p M ↔ ∀ i, h (b i) z / algebraMap (𝓞 K) K (algebraMap (𝓞 F) (𝓞 K) (a i)) ∈ S := fun z => by
    exact (Formalism.L2.SG.Pf.G2.mem_B_iff hbX hspan horth hdiag ha hpp hL z).trans ⟨fun h => h.2, fun h => ⟨Submodule.mem_top, h⟩⟩
  have hA : ∀ z, z ∈ locF p (dual h M) ↔ ∀ i, h (b i) z ∈ S := fun z => by
    rw [← hdI]; exact (Formalism.L2.SG.Pf.G2.mem_locF_dualIn_iff hbX hspan horth hdiag ha hF hp hL z).trans ⟨fun h => h.2, fun h => ⟨Submodule.mem_top, h⟩⟩
  have hR : ∀ c, c ∈ locR (K := K) P → c ∈ S := fun c hc => HU.mem_SP_iff_locF.2 (by rw [locF_eq_loc hK hF hP (1 : Submodule (𝓞 K) K)]; exact hc)

  obtain ⟨a0', ha0'⟩ : a0 ∈ Set.range (algebraMap (𝓞 F) (𝓞 K)) := by
    refine (conjO_eq_iff_mem_range hF a0).1 (RingOfIntegers.ext ?_)
    rw [conjO_coe]
    change star ((a0 : K)) = (a0 : K)
    rw [ha0x]; exact hs.eq x x
  have ha0ne : a0' ≠ 0 := by
    rintro rfl
    apply ha0P2
    rw [← ha0', map_zero]; exact Submodule.zero_mem _
  have hv0 : vF p a0' = 1 := by
    have h1 := localValuationFiltration.mem_pow_vF hp ha0ne
    have h2 := localValuationFiltration.notMem_pow_vF hp ha0ne
    have hin : a0' ∈ p := by rw [hpdef, Ideal.mem_comap, ha0']; exact ha0P
    rcases Nat.lt_or_ge (vF p a0') 2 with hlt | hge
    · interval_cases hv : vF p a0'
      · rw [zero_add, pow_one] at h2; exact absurd hin h2
      · rfl
    · exfalso
      apply ha0P2
      have := localizedQuotients.ι_mem_pow (K := K) (Ideal.pow_le_pow_right hge h1)
      rwa [hext, ha0'] at this
  have hd0 : h x x = algebraMap (𝓞 K) K (algebraMap (𝓞 F) (𝓞 K) a0') := by rw [ha0', ← ha0x]
  have hdne : h x x ≠ 0 := by rw [hd0]; exact Formalism.L2.SG.Pf.G2.jK_ι_ne_zero ha0ne
  have hα : ∀ i, algebraMap (𝓞 K) K (algebraMap (𝓞 F) (𝓞 K) (a i)) ≠ 0 := fun i => Formalism.L2.SG.Pf.G2.jK_ι_ne_zero (ha i)
  have hy : ∀ k i, h (b k) ((algebraMap (𝓞 K) K (algebraMap (𝓞 F) (𝓞 K) (a i)))⁻¹ • b i) = if k = i then 1 else 0 := by
    intro k i
    rw [LinearMap.map_smul, smul_eq_mul]
    split_ifs with hki
    · subst hki; rw [hdiag]; exact inv_mul_cancel₀ (hα k)
    · rw [horth k i hki, mul_zero]
  have hyA : ∀ i, (algebraMap (𝓞 K) K (algebraMap (𝓞 F) (𝓞 K) (a i)))⁻¹ • b i ∈ loc (K := K) P (dual h M) := by
    intro i
    rw [← hl, hA]
    intro k
    rw [hy]
    split_ifs
    · exact S.one_mem
    · exact S.zero_mem
  choose c hc hcM using fun i => hstr _ (hyA i)
  have hcS : ∀ i, c i ∈ S := fun i => hR _ (hc i)
  have hE : ∀ i k, ((if k = i then (1 : K) else 0) - c i * (h x x)⁻¹ * h (b k) x) / algebraMap (𝓞 K) K (algebraMap (𝓞 F) (𝓞 K) (a k)) ∈ S := by
    intro i k
    have h1 := hcM i
    rw [← hl] at h1
    have := (hB _).1 h1 k
    rwa [map_sub, hy, LinearMap.map_smul, smul_eq_mul] at this
  have hξ : ∀ k, h (b k) x / algebraMap (𝓞 K) K (algebraMap (𝓞 F) (𝓞 K) (a k)) ∈ S :=
    (hB x).1 (LocF.le_locF p M hxM)
  have hdS : h x x ∈ S := by rw [hd0]; exact HU.jK_mem_SP _

  have hle1 : ∀ i, vF p (a i) ≤ 1 := by
    intro i
    by_contra hgt
    push_neg at hgt
    have h1 : h x x / algebraMap (𝓞 K) K (algebraMap (𝓞 F) (𝓞 K) (a i)) ∈ S := by
      have e : h x x / algebraMap (𝓞 K) K (algebraMap (𝓞 F) (𝓞 K) (a i)) =
          h x x * (((if i = i then (1 : K) else 0) - c i * (h x x)⁻¹ * h (b i) x) / algebraMap (𝓞 K) K (algebraMap (𝓞 F) (𝓞 K) (a i))) + c i * (h (b i) x / algebraMap (𝓞 K) K (algebraMap (𝓞 F) (𝓞 K) (a i))) := by
        rw [if_pos rfl]; field_simp; ring
      rw [e]
      exact S.add_mem (S.mul_mem hdS (hE i i)) (S.mul_mem (hcS i) (hξ i))
    have h1' : algebraMap (𝓞 K) K a0 / algebraMap (𝓞 K) K (algebraMap (𝓞 F) (𝓞 K) (a i)) ∈ S := by
      rw [show algebraMap (𝓞 K) K a0 = h x x from ha0x]; exact h1
    have h2 := (Formalism.L2.SG.Pf.G2.div_mem_SP_iff hp (ha i) a0).1 h1'
    rw [hext] at h2
    exact ha0P2 (Ideal.pow_le_pow_right hgt h2)
  have huniq : ∀ i j, i ≠ j → vF p (a j) = 1 → 1 ≤ vF p (a i) → False := by
    intro i j hij hj hi
    have hci : c i / algebraMap (𝓞 K) K (algebraMap (𝓞 F) (𝓞 K) (a j)) ∈ S := by
      have e : c i / algebraMap (𝓞 K) K (algebraMap (𝓞 F) (𝓞 K) (a j)) = c i * (((if j = j then (1 : K) else 0) - c j * (h x x)⁻¹ * h (b j) x) / algebraMap (𝓞 K) K (algebraMap (𝓞 F) (𝓞 K) (a j)))
          - c j * (((if j = i then (1 : K) else 0) - c i * (h x x)⁻¹ * h (b j) x) / algebraMap (𝓞 K) K (algebraMap (𝓞 F) (𝓞 K) (a j))) := by
        rw [if_pos rfl, if_neg (fun e => hij e.symm)]; ring
      rw [e]
      exact S.sub_mem (S.mul_mem (hcS i) (hE j j)) (S.mul_mem (hcS j) (hE i j))
    obtain ⟨t, ht, w, hw⟩ := HU.mem_SP.1 (hcS i)
    have hw1 : algebraMap (𝓞 K) K w / algebraMap (𝓞 K) K (algebraMap (𝓞 F) (𝓞 K) (a j)) ∈ S := by
      rw [hw, mul_div_assoc]; exact S.mul_mem (HU.jK_mem_SP _) hci
    have hwP : w ∈ P := by
      have := (Formalism.L2.SG.Pf.G2.div_mem_SP_iff hp (ha j) w).1 hw1
      rwa [hj, pow_one, hext] at this
    have hw2 : algebraMap (𝓞 K) K w / algebraMap (𝓞 K) K (algebraMap (𝓞 F) (𝓞 K) a0') ∈ S :=
      (Formalism.L2.SG.Pf.G2.div_mem_SP_iff hp ha0ne w).2 (by rw [hv0, pow_one, hext]; exact hwP)
    have htne : algebraMap (𝓞 K) K (algebraMap (𝓞 F) (𝓞 K) t) ≠ 0 := Formalism.L2.SG.Pf.G2.jK_ι_ne_zero (Formalism.L2.SG.Pf.G2.ne_zero_of_notMem ht)
    have htinv : (algebraMap (𝓞 K) K (algebraMap (𝓞 F) (𝓞 K) t))⁻¹ ∈ S := HU.mem_SP.2 ⟨t, ht, 1, by rw [map_one, mul_inv_cancel₀ htne]⟩
    have hcd : c i * (h x x)⁻¹ ∈ S := by
      have e : c i * (h x x)⁻¹ = (algebraMap (𝓞 K) K (algebraMap (𝓞 F) (𝓞 K) t))⁻¹ * (algebraMap (𝓞 K) K w / algebraMap (𝓞 K) K (algebraMap (𝓞 F) (𝓞 K) a0')) := by
        rw [hw, ← hd0]; field_simp
      rw [e]; exact S.mul_mem htinv hw2
    have h1 : algebraMap (𝓞 K) K 1 / algebraMap (𝓞 K) K (algebraMap (𝓞 F) (𝓞 K) (a i)) ∈ S := by
      have e : algebraMap (𝓞 K) K 1 / algebraMap (𝓞 K) K (algebraMap (𝓞 F) (𝓞 K) (a i)) = ((if i = i then (1 : K) else 0) - c i * (h x x)⁻¹ * h (b i) x) / algebraMap (𝓞 K) K (algebraMap (𝓞 F) (𝓞 K) (a i))
          + (c i * (h x x)⁻¹) * (h (b i) x / algebraMap (𝓞 K) K (algebraMap (𝓞 F) (𝓞 K) (a i))) := by
        rw [if_pos rfl, map_one]; ring
      rw [e]; exact S.add_mem (hE i i) (S.mul_mem hcd (hξ i))
    have h2 := (Formalism.L2.SG.Pf.G2.div_mem_SP_iff hp (ha i) 1).1 h1
    rw [hext] at h2
    exact hP.ne_top ((Ideal.eq_top_iff_one P).2 (Ideal.pow_le_self (by omega) h2))
  have hex : ∃ i, vF p (a i) ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    apply hPb.2
    have hinv : ∀ i, algebraMap (𝓞 K) K 1 / algebraMap (𝓞 K) K (algebraMap (𝓞 F) (𝓞 K) (a i)) ∈ S := fun i =>
      (Formalism.L2.SG.Pf.G2.div_mem_SP_iff hp (ha i) 1).2 (by rw [hcon i, pow_zero, Ideal.one_eq_top]; exact Submodule.mem_top)
    have heq : loc (K := K) P (dual h M) = loc (K := K) P M := by
      rw [← hl, ← hl]
      ext z
      rw [hA, hB]
      constructor
      · intro hz i
        have e : h (b i) z / algebraMap (𝓞 K) K (algebraMap (𝓞 F) (𝓞 K) (a i)) = h (b i) z * (algebraMap (𝓞 K) K 1 / algebraMap (𝓞 K) K (algebraMap (𝓞 F) (𝓞 K) (a i))) := by
          rw [map_one]; ring
        rw [e]; exact S.mul_mem (hz i) (hinv i)
      · intro hz i
        have e : h (b i) z = algebraMap (𝓞 K) K (algebraMap (𝓞 F) (𝓞 K) (a i)) * (h (b i) z / algebraMap (𝓞 K) K (algebraMap (𝓞 F) (𝓞 K) (a i))) := by
          field_simp [hα i]
        rw [e]; exact S.mul_mem (HU.jK_mem_SP _) (hz i)
    obtain ⟨σ, hσ⟩ := GlobalTheory.MaxLatStruct.star_int (K := K)
    have hinj := IsFractionRing.injective (𝓞 K) K
    have hstar : ∀ r : 𝓞 K, star (algebraMap (𝓞 K) K r) ∈ Set.range (algebraMap (𝓞 K) K) :=
      fun r => ⟨σ r, hσ r⟩
    unfold IsUnimodularAt
    rw [locDual_dualAt_loc h hinj hstar, ← le_antisymm (locDual_loc_dual_le h P M)
      (locDual_dualAt_le h hstar P M hM.1.1.fg)]
    exact heq
  obtain ⟨i, hi⟩ := hex
  have hi1 : vF p (a i) = 1 := le_antisymm (hle1 i) (Nat.one_le_iff_ne_zero.2 hi)
  refine ⟨i, hi1, fun j hji => ?_⟩
  by_contra hj
  exact huniq j i hji hi1 (Nat.one_le_iff_ne_zero.2 hj)

end GlobalTheory.MaxLatExpo
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.NormsInvariantsGenericRationalFramePair
section
open NumberField MeasureTheory Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.TermLoc Formalism.L2.SG.RowsConc Formalism.L2.SG.NGCut Formalism.L2.SG.NGAnalytic Formalism.FourierDecayAlt GlobalTheory.Unfold GlobalTheory.LocOver GlobalTheory.GenMass
open scoped Classical ENNReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.GenMass.Norms

theorem sqrt_norm_eq (D : D7) (x : D.host.E) :
    Real.sqrt |((Algebra.norm ℚ x : ℚ) : ℝ)| = ∏ w : InfinitePlace D.host.E, w x := by
  have := Formalism.MainNotions.InterlacingSignCuts.host_totallyComplex D
  have h1 := InfinitePlace.prod_eq_abs_norm x
  have h2 : ∏ w : InfinitePlace D.host.E, w x ^ w.mult = (∏ w : InfinitePlace D.host.E, w x) ^ 2 := by
    rw [← Finset.prod_pow]
    exact Finset.prod_congr rfl fun w _ => by rw [(IsTotallyComplex.isComplex w).mult_eq_two]
  rw [← Rat.cast_abs, ← h1, h2]
  exact Real.sqrt_sq (Finset.prod_nonneg fun w _ => w.1.nonneg _)

theorem prod_natPow (D : D7) (g m : ℕ) :
    ∏ w : InfinitePlace D.host.E, w ((g : D.host.E) ^ m) = ((g : ℝ) ^ m) ^ D.R.f := by
  rw [← Formalism.MainNotions.LatticeGluingRadicals.d_card D, ← Finset.card_univ, ← Finset.prod_const]
  exact Finset.prod_congr rfl fun w _ => by rw [map_pow, InfinitePlace.map_natCast]

theorem localInvariantNorm_eq_prod_infinitePlaces_div (D : D7) (T T' : D.host.E) (Z : Formalism.L2.SG.CntLocal.MatZ D) :
    Formalism.L2.SG.CntLocal.sqrtAbsNormOfScaledGram T T' Z =
      (∏ w : InfinitePlace D.host.E, w (Formalism.L2.SG.CntLocal.GZ T T' Z)) / (((gS D : ℕ) : ℝ) ^ D.R.m) ^ D.R.f := by
  unfold Formalism.L2.SG.CntLocal.sqrtAbsNormOfScaledGram
  rw [sqrt_norm_eq, ← prod_natPow, ← Finset.prod_div_distrib]
  exact Finset.prod_congr rfl fun w _ => by rw [map_div₀]

theorem rd_pow_f (D : D7) : D.host.rdE ^ D.R.f = |(NumberField.discr D.host.F : ℝ)| := by
  have h := Formalism.MainNotions.BridgeLemma.szf_rd_pow D
  rw [Formalism.L2.SG.NGCut.LeadingMinorIntegrality.discr_sq] at h
  have hrd := Formalism.L2.SG.NGCut.LeadingMinorIntegrality.rd_pos (D := D)
  refine (pow_left_inj₀ (by positivity) (abs_nonneg _) two_ne_zero).1 ?_
  rw [h]; push_cast; rw [abs_pow]

theorem one_le_tprod_real {ι : Type} (a : ι → ℝ) (ha : ∀ i, 1 ≤ a i) : 1 ≤ ∏' i, a i := by
  by_cases h : Multipliable a
  · refine ge_of_tendsto' h.hasProd fun s => ?_
    exact Finset.one_le_prod (fun i _ => ha i)
  · rw [tprod_eq_one_of_not_multipliable h]

theorem one_le_nM {K V : Type} [Field K] [NumberField K] [StarRing K] (F : Type) [Field F] [NumberField F]
    [Algebra F K] [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
    (h : V →ₗ⋆[K] V →ₗ[K] K) (U : Submodule K V) (M : Submodule (𝓞 K) V) :
    1 ≤ Formalism.L2.SG.Pf.Cnt.nM F h U M := by
  unfold Formalism.L2.SG.Pf.Cnt.nM
  refine one_le_tprod_real _ fun p => one_le_pow₀ ?_
  have h0 : p.1 ≠ ⊥ := Ring.ne_bot_of_isMaximal_of_not_isField p.2 (RingOfIntegers.not_isField F)
  have h1 : Ideal.absNorm p.1 ≠ 0 := by rwa [Ne, Ideal.absNorm_eq_zero_iff]
  exact_mod_cast Nat.one_le_iff_ne_zero.2 h1

theorem m_eq (D : D7) : D.R.m = 2 * D.R.rS + 2 := by
  obtain ⟨t, ht⟩ := D.R.m_even
  have h2 := D.R.two_le_m
  unfold Ranks.rS
  omega

theorem norms_generic : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), (D.mem u).A.T ≡ (D.mem u').A.T [MOD (gS D) ^ 2] → ∀ (G' : LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E)) (Λ : LV D) (w : Point D.host.E (D.R.rS + 1)), G'.zt = G'.fl.z → TotPos (Gval (lf D (X.Fu u)) G') → IsRowLat D (X.Fu u) Λ → G' ∈ Formalism.L2.SG.CntLocal.EZ ((Tu D u' : ℕ) : D.host.E) (X.Fu u) Λ (ZhatL (lf D (X.Fu u)) G') → IsInCell (ZhatOM (ZhatL (lf D (X.Fu u)) G')) w → (∀ a, 1 ≤ ∏ v : InfinitePlace D.host.E, (D.host.rdE ^ (2 * (endIdx (toPts w) a * (2 * D.R.rS + 1 - endIdx (toPts w) a))))⁻¹ * v (endMin (toPts w) a) ^ 2) ∧ ((gS D : ℝ)) ^ ((2 * D.R.rS + 2) * Fintype.card (InfinitePlace D.host.E)) ≤ NGPt D.host.rdE (Tu D u * Tu D u') (toPts w) ∧ Formalism.L2.SG.CntLocal.sqrtAbsNormOfScaledGram ((Tu D u : ℕ) : D.host.E) ((Tu D u' : ℕ) : D.host.E) (ZhatL (lf D (X.Fu u)) G') ^ (D.R.k - 1) * Formalism.L2.SG.MassDataConc.ngFac D = PN.abelian₂ (2 * D.host.v) D.R.rS D.R.k D.R.f * NGPt D.host.rdE (Tu D u * Tu D u') (toPts w) ^ (D.R.k - 1) := by
  intro D X Y u u' hT G' Λ w hzt hP hrow hE hcell
  have hun := hrow.2.1.2.1
  have hz := hrow.2.1.2.2.1.1
  have hX := hrow.2.2
  have hz' : G'.fl.z ∈ Λ := hE.1.1.1
  have hX' := hE.2.2.2.1.2
  have hF : ∀ b, frame (lf D (X.Fu u)) b ∈ Λ := PtPf.frame_mem _ hz hX
  have hF' : ∀ b, frame G' b ∈ Λ := PtPf.frame_mem _ hz' hX'
  have hrd := Formalism.L2.SG.NGCut.LeadingMinorIntegrality.rd_pos (D := D)
  have hg : (0 : ℝ) < (gS D : ℕ) := by exact_mod_cast Formalism.MainNotions.LatticeGluingRadicals.z_gS_pos D
  have hGeq := LeadingMinorIntegrality.gpt_eq (T := Tu D u) (T' := Tu D u') (lf D (X.Fu u)) G' _ hcell
  set P : ℝ := ∏ v : InfinitePlace D.host.E, v (Gval (lf D (X.Fu u)) G') with hPdef
  have hNG : NGPt D.host.rdE (Tu D u * Tu D u') (toPts w) =
      ((D.host.rdE ^ D.R.f) ^ (2 * D.R.rS * (D.R.rS + 1)))⁻¹ * P := by
    unfold NGPt
    rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Formalism.MainNotions.LatticeGluingRadicals.d_card D, hGeq, inv_pow,
      ← pow_mul, ← pow_mul, mul_comm D.R.f]
    rfl
  have hN0 : Formalism.L2.SG.CntLocal.sqrtAbsNormOfScaledGram ((Tu D u : ℕ) : D.host.E) ((Tu D u' : ℕ) : D.host.E)
      (ZhatL (lf D (X.Fu u)) G') = P / (((gS D : ℕ) : ℝ) ^ D.R.m) ^ D.R.f := localInvariantNorm_eq_prod_infinitePlaces_div D _ _ _
  refine ⟨fun a => ?_, ?_, ?_⟩
  · have hj : endIdx (toPts w) a ≤ D.R.rS + 1 := (toPts w).1.sizeUpTo_le _
    obtain ⟨o, ho, e⟩ := LeadingMinorIntegrality.lead_mem hun (lf D (X.Fu u)) G' hz hX hz' hX' _ hj
    rw [← LeadingMinorIntegrality.lead_cell _ _ hcell, ← LeadingMinorIntegrality.endMin_eq] at e
    have hE5 := PtPf.blockEndMinors_of_cell _ (PtPf.zhatOM_isIntegral _ _ hun hF hF') _ hcell
    have h0 : endMin (toPts w) a ≠ 0 := (hE5 a).2
    rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Formalism.MainNotions.LatticeGluingRadicals.d_card D]
    have hsq := LeadingMinorIntegrality.prod_sq_ge _ o ho (by rw [e]; exact h0)
    rw [e] at hsq
    rw [inv_pow, ← div_eq_inv_mul, one_le_div (by positivity), ← pow_mul, mul_comm _ D.R.f, pow_mul]
    exact hsq
  · have hI := Formalism.L2.SG.Pf.Cnt.mmInt_of_EZ hT (Y.rowsOK u) hzt rfl hP hrow hE
    have hn := PI.UnitaryGroupMassFormula.CntFormula.R6.norm_mass_of_jordan D u u' hT (X.Fu u) (Y.what₂ u) (Y.rowsOK u) _ G' hzt rfl hP hI
    have h1 := one_le_nM D.host.F (VS D).hT (Formalism.L2.SG.Pf.Cnt.UPair D (X.Fu u) G')
      (Formalism.L2.SG.Pf.Cnt.MMof D (X.Fu u) G')
    replace h1 := h1.trans_eq hn
    rw [zpow_neg, zpow_natCast, ← rd_pow_f] at h1
    replace h1 : 1 ≤ ((D.host.rdE ^ D.R.f) ^ (2 * D.R.rS * (D.R.rS + 1)))⁻¹ *
        (P / (((gS D : ℕ) : ℝ) ^ D.R.m) ^ D.R.f) := hN0 ▸ h1
    rw [← mul_div_assoc, one_le_div (by positivity)] at h1
    rw [hNG, Formalism.MainNotions.LatticeGluingRadicals.d_card D, ← m_eq, pow_mul]
    exact h1
  · have hv : 2 * D.host.v = D.host.rdE := by unfold Host.v; ring
    rw [hN0, hNG, hv]
    unfold Formalism.L2.SG.MassDataConc.ngFac PN.abelian₂
    rw [sqrt_norm_eq, prod_natPow, ← mul_pow, div_mul_cancel₀ _ (by positivity)]
    have e : D.host.rdE ^ (2 * D.R.rS * (D.R.rS + 1) * (D.R.k - 1) * D.R.f) =
        ((D.host.rdE ^ D.R.f) ^ (2 * D.R.rS * (D.R.rS + 1))) ^ (D.R.k - 1) := by
      rw [← pow_mul, ← pow_mul]; congr 1; ring
    rw [e, ← mul_pow, mul_inv_cancel_left₀ (by positivity)]

end GlobalTheory.GenMass.Norms
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.RationalClassLatticesIffRationalClassLocalFrameP
section
noncomputable section

open scoped Classical ENNReal
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full
  Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.Unfold

namespace GlobalTheory.Unfold.RatCls

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {T T' : D.host.E} {F : LFlag (VS D) D.R.rS T} {F' : LFlag (VS D) D.R.rS T'}

theorem principalPolarisation_exists_unique_section : (1 : GV D) ∈ H0 F F' := ⟨Subgroup.one_mem _, fun _ => rfl, fun _ => rfl⟩

theorem mul_mem_isometriesFixingBothFrames {g h : GV D} (hg : g ∈ H0 F F') (hh : h ∈ H0 F F') : g * h ∈ H0 F F' := by
  refine ⟨Subgroup.mul_mem _ hg.1 hh.1, fun a => ?_, fun a => ?_⟩
  · show g (h (frame F a)) = frame F a
    rw [hh.2.1 a, hg.2.1 a]
  · show g (h (frame F' a)) = frame F' a
    rw [hh.2.2 a, hg.2.2 a]

theorem inv_mem_isometriesFixingBothFrames {h : GV D} (hh : h ∈ H0 F F') : h⁻¹ ∈ H0 F F' := by
  refine ⟨Subgroup.inv_mem _ hh.1, fun a => ?_, fun a => ?_⟩
  · show h.symm (frame F a) = frame F a
    rw [LinearEquiv.symm_apply_eq, hh.2.1 a]
  · show h.symm (frame F' a) = frame F' a
    rw [LinearEquiv.symm_apply_eq, hh.2.2 a]

theorem ext_one (p : PlF D) : Ext p (1 : GV D) 1 := fun _ => rfl

theorem ext_mul {p : PlF D} {g h : GV D} {g' h' : Vp D p ≃ₗ[(D.s.atP p).Ep] Vp D p}
    (hg : Ext p g g') (hh : Ext p h h') : Ext p (g * h) (g' * h') := fun x => by
  show g' (h' (baseChange₂ D p x)) = baseChange₂ D p (g (h x))
  rw [hh x, hg (h x)]

theorem ext_inv {p : PlF D} {g : GV D} {g' : Vp D p ≃ₗ[(D.s.atP p).Ep] Vp D p}
    (hg : Ext p g g') : Ext p g⁻¹ g'⁻¹ := fun x => by
  show g'.symm (baseChange₂ D p x) = baseChange₂ D p (g.symm x)
  rw [LinearEquiv.symm_apply_eq, hg, LinearEquiv.apply_symm_apply]

end GlobalTheory.Unfold.RatCls

open GlobalTheory.Unfold.RatCls in
attribute [local instance] Formalism.BasicNotions.Host.cmStar in

theorem GlobalTheory.Unfold.ratCls_agree : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), ∀ (F : LFlag (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)) (F' : LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E)) (w : Point D.host.E (D.R.rS + 1)), ZhatOM (ZhatL F F') = ptMat w → Gval F F' ≠ 0 → ∀ (Z : LocDat D) (FP : ∀ p : PlF D, LocNG.FPair (locH Z p) D.R.rS), Based Z FP (Tu D u) (Tu D u') F F' → (∀ p, (FP p).RelG (LocNG.theta (Z.M p))) → Equivalence (GRel (Z := Z) (FP := FP) F F') ∧ (∀ y y' : Dat Z FP, GRel F F' y y' → (stabY F F' y).encard = (stabY F F' y').encard) ∧ ∀ (Λ₁ Λ₂ : LV D) (y₁ y₂ : Dat Z FP), LocOver Λ₁ y₁ → LocOver Λ₂ y₂ → (LRel F F' Λ₁ Λ₂ ↔ GRel F F' y₁ y₂) ∧ stabL F F' Λ₁ = stabY F F' y₁ := by
  intro D X Y u u' F F' w hZ hG Z FP hB hR
  have hact : ∀ p, ∃ act : MulAction (FP p).UW0 (LocNG.Datum (FP p)),
      (∀ (g : (FP p).UW0) d d', LocNG.Datum.Moves g.1 d d' ↔ act.smul g d = d') ∧
      ∀ d (g : (FP p).UW0), g.1 ∈ LocNG.Datum.Stab d ↔ act.smul g d = d := by
    intro p
    refine GlobalTheory.T.exists_complementUnitary_mulAction_localInnerDatum (Z.M p) (Z.agree p).1 (locH Z p) D.R.rS D.R.k (FP p) ?_ (hR p)
    rw [finrank_Vp]
    obtain ⟨j, hj⟩ := D.R.m_even
    have h2 := D.R.two_le_m
    show D.R.k + D.R.m - 1 = D.R.k + 2 * (D.R.m / 2 - 1) + 1
    omega
  choose act hmv _ using hact
  obtain ⟨hu, hw, -, hlift⟩ := GlobalTheory.T.rationalAutomorphism_local_extension_moves_lattices D X Y u u' F F' w hZ hG Z FP hB hR
  have hdict := GlobalTheory.T.globalInnerDatum_eq_iff_local_data_eq D X Y u u' F F' w hZ hG Z FP hB hR

  have rm_fun : ∀ h ∈ H0 F F', ∀ y y₁ y₂ : Dat Z FP, RMoves h y y₁ → RMoves h y y₂ → y₁ = y₂ := by
    intro h hh y y₁ y₂ r₁ r₂
    funext p
    obtain ⟨g₁, e₁, m₁⟩ := r₁ p
    obtain ⟨g₂, e₂, m₂⟩ := r₂ p
    obtain rfl : g₁ = g₂ := (hu h p).unique e₁ e₂
    have hm := hw h hh p g₁ e₁
    exact ((hmv p ⟨g₁, hm⟩ _ _).1 m₁).symm.trans ((hmv p ⟨g₁, hm⟩ _ _).1 m₂)
  have rm_one : ∀ y : Dat Z FP, RMoves (1 : GV D) y y := by
    intro y p
    refine ⟨1, ext_one p, (hmv p 1 _ _).2 ?_⟩
    letI := act p
    exact one_smul _ _
  have rm_mul : ∀ h₁ ∈ H0 F F', ∀ h₂ ∈ H0 F F', ∀ y y' y'' : Dat Z FP,
      RMoves h₁ y y' → RMoves h₂ y' y'' → RMoves (h₂ * h₁) y y'' := by
    intro h₁ hh₁ h₂ hh₂ y y' y'' r₁ r₂ p
    obtain ⟨g₁, e₁, m₁⟩ := r₁ p
    obtain ⟨g₂, e₂, m₂⟩ := r₂ p
    let a₁ : (FP p).UW0 := ⟨g₁, hw h₁ hh₁ p g₁ e₁⟩
    let a₂ : (FP p).UW0 := ⟨g₂, hw h₂ hh₂ p g₂ e₂⟩
    refine ⟨g₂ * g₁, ext_mul e₂ e₁, (hmv p (a₂ * a₁) _ _).2 ?_⟩
    letI := act p
    have f₁ : a₁ • y p = y' p := (hmv p a₁ _ _).1 m₁
    have f₂ : a₂ • y' p = y'' p := (hmv p a₂ _ _).1 m₂
    show (a₂ * a₁) • y p = y'' p
    rw [mul_smul, f₁, f₂]
  have rm_inv : ∀ h ∈ H0 F F', ∀ y y' : Dat Z FP, RMoves h y y' → RMoves h⁻¹ y' y := by
    intro h hh y y' r p
    obtain ⟨g, e, m⟩ := r p
    let a : (FP p).UW0 := ⟨g, hw h hh p g e⟩
    refine ⟨g⁻¹, ext_inv e, (hmv p a⁻¹ _ _).2 ?_⟩
    letI := act p
    have f : a • y p = y' p := (hmv p a _ _).1 m
    show a⁻¹ • y' p = y p
    rw [inv_smul_eq_iff, f]
  have conj : ∀ h ∈ H0 F F', ∀ y y' : Dat Z FP, RMoves h y y' →
      ∀ k ∈ stabY F F' y, h * k * h⁻¹ ∈ stabY F F' y' := by
    intro h hh y y' hm k hk
    refine ⟨mul_mem_isometriesFixingBothFrames (mul_mem_isometriesFixingBothFrames hh hk.1) (inv_mem_isometriesFixingBothFrames hh), ?_⟩
    rw [mul_assoc]
    exact rm_mul _ (mul_mem_isometriesFixingBothFrames hk.1 (inv_mem_isometriesFixingBothFrames hh)) h hh _ _ _
      (rm_mul _ (inv_mem_isometriesFixingBothFrames hh) k hk.1 _ _ _ (rm_inv h hh y y' hm) hk.2) hm
  refine ⟨⟨fun y => ⟨1, principalPolarisation_exists_unique_section, rm_one y⟩, fun ⟨h, hh, hm⟩ => ⟨h⁻¹, inv_mem_isometriesFixingBothFrames hh, rm_inv h hh _ _ hm⟩,
    fun ⟨h₁, hh₁, m₁⟩ ⟨h₂, hh₂, m₂⟩ => ⟨h₂ * h₁, mul_mem_isometriesFixingBothFrames hh₂ hh₁, rm_mul h₁ hh₁ h₂ hh₂ _ _ _ m₁ m₂⟩⟩, ?_, ?_⟩
  · rintro y y' ⟨h, hh, hm⟩
    have e : stabY F F' y' = (MulAut.conj h) '' stabY F F' y := by
      ext k
      constructor
      · intro hk
        refine ⟨h⁻¹ * k * h⁻¹⁻¹, conj h⁻¹ (inv_mem_isometriesFixingBothFrames hh) y' y (rm_inv h hh y y' hm) k hk, ?_⟩
        simp [MulAut.conj_apply, mul_assoc]
      · rintro ⟨k, hk, rfl⟩
        exact conj h hh y y' hm k hk
    rw [e, (MulAut.conj h).injective.encard_image]
  · intro Λ₁ Λ₂ y₁ y₂ h₁ h₂
    have key : ∀ h ∈ H0 F F', ∀ (Λ Λ' : LV D) (y y' : Dat Z FP), LocOver Λ y → LocOver Λ' y' →
        (gdat F F' (Formalism.HermitianLatticesTheory.gmap h Λ) = gdat F F' Λ' ↔ RMoves h y y') := by
      intro h hh Λ Λ' y y' hl hl'
      obtain ⟨y'', hl'', hm''⟩ := hlift h hh Λ y hl
      rw [hdict _ _ y'' y' hl'' hl']
      constructor
      · rintro rfl
        exact hm''
      · intro hm
        exact rm_fun h hh y y'' y' hm'' hm
    refine ⟨⟨fun ⟨h, hh, he⟩ => ⟨h, hh, (key h hh _ _ _ _ h₁ h₂).1 he⟩,
      fun ⟨h, hh, hm⟩ => ⟨h, hh, (key h hh _ _ _ _ h₁ h₂).2 hm⟩⟩, ?_⟩
    ext h
    exact ⟨fun ⟨hh, he⟩ => ⟨hh, (key h hh _ _ _ _ h₁ h₁).1 he⟩, fun ⟨hh, hm⟩ => ⟨hh, (key h hh _ _ _ _ h₁ h₁).2 hm⟩⟩
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.RationalIsometryCoordinateMatrixRealPlace
section
open scoped Classical ENNReal
open Matrix MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.LocWSOf Formalism.L2.SG.PoincareInHH.PoincareSetting GlobalTheory.CovDom GlobalTheory.CovDomGrp
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CovDomGrp

theorem coordMat_place : ∀ {D : D7} (X : HidaSetting D) {x : X.B.I.GA} (n : (VS D).V ≃ₗ[D.host.E] (VS D).V) (γ : Matrix (Fin (2 * D.R.rS + D.R.k + 1)) (Fin (2 * D.R.rS + D.R.k + 1)) D.host.E), Formalism.L2.SG.TermOp.RatLink X x n → (∀ y, crdH X (n y) = γ *ᵥ crdH X y) → ∀ τ : D.what₂.Tau, γ.map (embS D τ) = (X.B.I.P (vOf X τ) * uMat (x.1 (vOf X τ)) * (X.B.I.P (vOf X τ))⁻¹).submatrix (ci X) (ci X) := by
  intro D X x n γ hR hγ τ
  obtain ⟨M, -, h1, -, h4⟩ := hR
  have hPu : IsUnit (X.B.I.P (vOf X τ)).det :=
    (Matrix.isUnit_iff_isUnit_det _).1 (X.B.I.P_unit (vOf X τ))
  have hP : X.B.I.P (vOf X τ) * uMat (x.1 (vOf X τ)) * (X.B.I.P (vOf X τ))⁻¹ =
      (M : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E).map (X.B.I.φ (vOf X τ)) := by
    rw [h1 (vOf X τ)]
    simp only [← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hPu, Matrix.one_mul]
    rw [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hPu, Matrix.mul_one]

  have hN : ∀ c, γ *ᵥ c = (((M : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E).map X.ιE).submatrix (ci X) (ci X)) *ᵥ c := by
    intro c
    have hc := hγ (vecOf X c)
    rw [crdH_vecOf] at hc
    rw [← hc]
    funext i
    rw [crdH_eq_crd, h4]
    simp only [Matrix.mulVec, dotProduct, map_sum, map_mul, Matrix.submatrix_apply, Matrix.map_apply]
    rw [← (ci X).sum_comp]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [← crdH_eq_crd, crdH_vecOf]
  have hγe : γ = ((M : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E).map X.ιE).submatrix (ci X) (ci X) :=
    Matrix.toLin'.injective (LinearMap.ext fun c => by rw [Matrix.toLin'_apply, Matrix.toLin'_apply]; exact hN c)
  rw [hP, hγe]
  ext i j
  simp only [Matrix.map_apply, Matrix.submatrix_apply, X.φ_eq]
  congr 1
  simp [vOf]

end GlobalTheory.CovDomGrp
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.RealPtsEqImage
section
open scoped Classical ENNReal Pointwise
open MeasureTheory Matrix NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.LocWSOf Formalism.MainNotions.S.Cnt Formalism.L2.SG.KappaOffDiagonal Formalism.MainNotions.LatticeGluingRadicals GlobalTheory.TypeAsm
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.TypeAsm.RatIsomReal

theorem realPts_eq_image : ∀ (D : D7) (X : HidaSetting D) (C : Choice X 1) (Γ : Set ((VS D).V ≃ₗ[D.host.E] (VS D).V)),
    (∀ n ∈ Γ, n ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT) →
      GlobalTheory.DegVol.realPts (phiV C) Γ = trI C '' {y | ∃ (x : X.B.I.GA) (n : (VS D).V ≃ₗ[D.host.E] (VS D).V),
        RatLink X x n ∧ y = x.1 ∧ n ∈ Γ} := by
  intro D X C Γ hΓ
  ext m
  constructor
  · rintro ⟨n, hn, hm⟩
    obtain ⟨x, hx⟩ := Formalism.L2.SG.Pf.ratPt_holds D X n (hΓ n hn)
    exact ⟨x.1, ⟨x, n, hx, rfl, hn⟩, GLinkPf.eq_of_act C (GLinkPf.trI_act C hx) (fun τ y => hm τ y)⟩
  · rintro ⟨_, ⟨x, n, hx, rfl, hn⟩, rfl⟩
    exact ⟨n, hn, fun τ y => GLinkPf.trI_act C hx τ y⟩

end GlobalTheory.TypeAsm.RatIsomReal
end
end

