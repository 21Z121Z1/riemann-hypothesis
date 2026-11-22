import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ExistsUnitarySupportedAtPlaceOfMulEqIdem
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0014
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0038
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0139
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0277
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0285
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0154
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0136
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.HzUnit
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SelfDualSplitComponentIsLatticeStabilizerEq
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0287
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0289
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0060
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SymmetricDoubleIntegralFiniteCombination
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0026
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.CosInj
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PhiTopAgree
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0295
import Formalism.LocalToGlobal.Columns.FiniteSumNonzeroLargeDepth
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0080
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0023
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0282
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.Bundle0002
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.Bundle0003
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.Bundle0001
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0020
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0216
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0072

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FlatMapFourierJacobiToBesselLocalModel
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.LocMod GlobalTheory.StepData

noncomputable section

namespace GlobalTheory.LocMod

theorem flatFB_holds : ∀ (D : D7), FlatLaw D → GlobalTheory.FinPl.FlatLaws D → OmLoc D → FlatFB D := by
  intro D hFL hFLs hOm k _ _ _ _ _ _ p ν hν ψ ψk hχ σ J B st s hs n n' _ _ _ _ c G₀ FW FA F₀ FV hJF hCF hBF Tm hTm
  have hstd : IsStdChar D ψ (-1) := st.weil.std
  obtain ⟨hcont, hne⟩ := (GlobalTheory.T.weilCharacter_splitPlace_exists_continuous_nontrivial D k p ψ hstd).2.1 ψk hχ
  have hc : c = 2 * σ + 1 := hBF.1
  let L : SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k) →ₗ[ℂ] (WO J.W₀ B.V₀ → ℂ) :=
    { toFun := fun Φ => flatFB st (Tm Φ)
      map_add' := fun Φ Φ' => by
        simp only [map_add]
        exact (GlobalTheory.T.jacobiToBesselFlatSchwartz_add_smul D hFL ψ hstd σ J B st _ _ (hTm.theta Φ) (hTm.theta Φ')).1
      map_smul' := fun a Φ => by
        simp only [map_smul, RingHom.id_apply]
        exact (GlobalTheory.T.jacobiToBesselFlatSchwartz_add_smul D hFL ψ hstd σ J B st _ _ (hTm.theta Φ) (hTm.theta Φ)).2 a }
  obtain ⟨L₀, hL₀⟩ := GlobalTheory.T.flatMap_laws_factor_fourierJacobi_source k ψk ν hcont hne hν n n' c σ (WO J.W₀ B.V₀ → ℂ) L hc
    (GlobalTheory.T.flat_fourierJacobi_to_bessel_column_mul_laws D hFLs hOm k p ψ ψk hχ σ J B st s hs n n' c G₀ FW FA F₀ FV hJF hCF hBF Tm hTm)
    (GlobalTheory.T.fourierJacobi_bessel_flatMap_row_multiplication D hFLs hOm k p ψ ψk hχ σ J B st s hs n n' c G₀ FW FA F₀ FV hJF hCF hBF Tm hTm)
    (GlobalTheory.T.localFlatMap_translationLaws_jacobiToBessel_free D hFLs hOm k p ψ ψk hχ σ J B st s hs n n' c G₀ FW FA F₀ FV hJF hCF hBF Tm hTm)
    (GlobalTheory.T.fourierJacobi_bessel_flatMap_unipotent_law D hFLs hOm k p ψ ψk hχ σ J B st s hs n n' c G₀ FW FA F₀ FV hJF hCF hBF Tm hTm)
  exact ⟨L₀, GlobalTheory.T.fourierJacobi_bessel_flatMap_factor_isLocalModel D hFLs hOm k p ν hν ψ ψk hχ σ J B st s hs n n' c G₀ FW FA F₀ FV hJF hCF hBF Tm hTm L₀ hL₀, hL₀⟩

end GlobalTheory.LocMod

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FoldrExtract
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.FinPl
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.LocMod GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain ValuativeRel

noncomputable section

namespace GlobalTheory.FixedLevelIsolate

theorem foldr_extract {ι X : Type} [DecidableEq ι] (g : ι → X → X) (i : ι)
    (hc : ∀ a, a ≠ i → ∀ x, g a (g i x) = g i (g a x)) :
    ∀ (l : List ι) (x : X), i ∈ l → l.foldr g x = g i ((l.erase i).foldr g x) := by
  intro l x hi
  induction l with
  | nil => simp at hi
  | cons a t ih =>
    by_cases ha : a = i
    · subst ha
      simp
    · have hit : i ∈ t := by
        rcases List.mem_cons.1 hi with h | h
        · exact absurd h.symm ha
        · exact h
      have he : (a :: t).erase i = a :: t.erase i := by
        simp [ha]
      rw [he, List.foldr_cons, List.foldr_cons, ih hit, hc a ha]

variable {D : D7}

theorem latO_mono {S T : HSp D} (LS : Set (Fin S.rank → D.host.E)) (LT : Set (Fin T.rank → D.host.E))
    {P P' : Pl D → Prop} (h : ∀ p, P p → P' p) : latO S T LS LT P ≤ latO S T LS LT P' := by
  apply AddSubgroup.closure_mono
  rintro w ⟨α, hα, hv, rest⟩
  exact ⟨α, hα, fun p hp => hv p fun hq => hp (h p hq), rest⟩

theorem vac_mono {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {LS : Lat S} {LT : Lat T} {P P' : Pl D → Prop}
    (h : ∀ p, P p → P' p) {f : WO S T → ℂ} (hf : Vac ψ S T LS LT P' f) : Vac ψ S T LS LT P f :=
  ⟨hf.1, fun u hu => hf.2.1 u (latO_mono _ _ h hu), fun e he u hu hh => hf.2.2 e he u (latO_mono _ _ h hu) hh⟩

theorem eg_combAt {c : Comm D} {v : VCom c} (G : GLoc v) (j : ℕ) (hj : j ≤ G.s) : CombAt (· = G.q.v) (G.eg j) := by
  intro u hu a b
  have h := (G.eg_is j (G.s - j) (by omega)).1 u hu a b
  exact (GlobalTheory.FinPl.FrameLat.idem_iff G.q _).2 h

end GlobalTheory.FixedLevelIsolate

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FourierJacobiProductMapHaarFiniteOnCompacts
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.QPl ValuativeRel
open GlobalTheory.PosOne (toOne Covers TriPos)
open GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage (app HasTensorVal fl opEFJ IsQuotIntFJ RFJ)
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (IsCO)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance high] GlobalTheory.SplitWeil.matrixMeasurableSpace
open GlobalTheory.HaarR

noncomputable section
namespace GlobalTheory.HaarR

theorem finite_on_compacts_prodRFJ : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (n : Type) [Fintype n] [DecidableEq n] (c ρ : ℕ), 1 ≤ ρ → ρ < c → ∀ (ν : Measure k), ν.IsAddHaarMeasure → ∀ m : Measure (GL n k), m.IsHaarMeasure → IsFiniteMeasureOnCompacts (((m.prod (volN ν n c (ρ + 1))).prod (Measure.pi fun _ : n => ν)).map (prodRFJ ρ)) := by
  intro k _ _ _ _ _ _ n _ _ c ρ hp hpc ν hν m hm
  haveI := GlobalTheory.SplitWeil.secondCountable k
  haveI := GlobalTheory.SplitWeil.t2Space k
  haveI : BorelSpace (GL (n ⊕ Fin c) k) := GlobalTheory.SplitFlip.borel_GL
  haveI := QuotLinear.finiteOnCompacts_volN (n := n) (c := c) (p := ρ + 1) ν
  haveI : LocallyCompactSpace (N k n c (ρ + 1)) :=
    (QuotLinear.isClosed_N (k := k) (n := n) (c := c) (p := ρ + 1)).isClosedEmbedding_subtypeVal.locallyCompactSpace
  haveI : SecondCountableTopology (N k n c (ρ + 1)) := TopologicalSpace.Subtype.secondCountableTopology _
  haveI : IsLocallyFiniteMeasure (volN ν n c (ρ + 1)) := isLocallyFiniteMeasure_of_isFiniteMeasureOnCompacts
  haveI : SigmaFinite (volN ν n c (ρ + 1)) := sigmaFinite_of_locallyFinite
  haveI : IsLocallyFiniteMeasure ν := isLocallyFiniteMeasure_of_isFiniteMeasureOnCompacts
  haveI : SigmaFinite ν := sigmaFinite_of_locallyFinite
  set M := (m.prod (volN ν n c (ρ + 1))).prod (Measure.pi fun _ : n => ν) with hM
  haveI : IsFiniteMeasureOnCompacts M := by rw [hM]; infer_instance
  refine ⟨fun K hK => ?_⟩
  obtain ⟨D, hD, hD'⟩ := GlobalTheory.RootEx.ProperTriple.proper_triple k n c ρ hp hpc _ (hK.image continuous_subtype_val)
  have hD2 : IsCompact ((fun w : GL n k × N k n c (ρ + 1) × (n → k) => ((w.1, w.2.1), w.2.2)) '' D) :=
    hD.image (by fun_prop)
  have hsub : prodRFJ ρ ⁻¹' K ⊆ (fun w : GL n k × N k n c (ρ + 1) × (n → k) => ((w.1, w.2.1), w.2.2)) '' D := by
    intro z hz
    exact ⟨(z.1.1, z.1.2, z.2), hD' _ ⟨_, hz, rfl⟩, rfl⟩
  by_cases hf : AEMeasurable (prodRFJ (k := k) (n := n) (c := c) ρ) M
  · rw [Measure.map_apply_of_aemeasurable hf hK.isClosed.measurableSet]
    exact (measure_mono hsub).trans_lt hD2.measure_lt_top
  · rw [Measure.map_of_not_aemeasurable hf]
    simp

end GlobalTheory.HaarR
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FractionalIdealGeneratedByOneAlmostEverywhere
section
open Formalism.BasicNotions IsDedekindDomain NumberField

namespace GlobalTheory.IdeleGen

theorem exists_nat_mem_mul_integral {E : Type} [Field E] [NumberField E]
    (I : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) (hI : I ≠ 0) :
    ∃ N : ℕ, N ≠ 0 ∧ (N : E) ∈ I ∧ ∀ b ∈ I, ∃ o : 𝓞 E, (N : E) * b = (o : E) := by
  obtain ⟨a, ha, hint⟩ := I.isFractional
  have ha0 : a ≠ 0 := nonZeroDivisors.ne_zero ha
  have hbot : (I : Submodule (𝓞 E) E) ≠ ⊥ := by
    intro h
    apply hI
    exact FractionalIdeal.coeToSubmodule_injective (h.trans FractionalIdeal.coe_zero.symm)
  obtain ⟨x, hxI, hx0⟩ := (Submodule.ne_bot_iff _).1 hbot
  obtain ⟨j, hj⟩ := hint x hxI
  have hj' : (j : E) = (a : E) * x := by
    simpa [Algebra.smul_def] using hj
  have haE : (a : E) ≠ 0 := by exact_mod_cast ha0
  have hj0 : j ≠ 0 := by
    intro h; rw [h] at hj'; simp at hj'
    rcases hj' with h1 | h1
    · first | exact ha0 h1 | exact ha0 h1.symm | exact haE h1 | exact haE h1.symm
    · first | exact hx0 h1 | exact hx0 h1.symm
  set Nd := Ideal.absNorm (Ideal.span {a}) with hNd
  set Nj := Ideal.absNorm (Ideal.span {j}) with hNj
  have hNd0 : Nd ≠ 0 := by
    rw [hNd, Ne, Ideal.absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot]; exact ha0
  have hNj0 : Nj ≠ 0 := by
    rw [hNj, Ne, Ideal.absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot]; exact hj0
  obtain ⟨o₁, ho₁⟩ := Ideal.mem_span_singleton'.1 (Ideal.absNorm_mem (Ideal.span {a}))
  obtain ⟨o₂, ho₂⟩ := Ideal.mem_span_singleton'.1 (Ideal.absNorm_mem (Ideal.span {j}))
  have ho₁E : ((Nd : 𝓞 E) : E) = (o₁ : E) * (a : E) := by rw [← ho₁]; push_cast; ring
  have ho₂E : ((Nj : 𝓞 E) : E) = (o₂ : E) * (j : E) := by rw [← ho₂]; push_cast; ring
  refine ⟨Nd * Nj, mul_ne_zero hNd0 hNj0, ?_, ?_⟩
  · have : ((Nd * Nj : ℕ) : E) = ((Nd : 𝓞 E) * o₂ * a : 𝓞 E) • x := by
      rw [Algebra.smul_def]
      have e1 : ((Nd * Nj : ℕ) : E) = ((Nd : 𝓞 E) : E) * ((Nj : 𝓞 E) : E) := by push_cast; ring
      rw [e1, ho₂E]
      have hal : ∀ z : 𝓞 E, algebraMap (𝓞 E) E z = (z : E) := fun _ => rfl
      rw [hal]
      push_cast
      linear_combination ((Nd : E) * (o₂ : E)) * hj'
    rw [this]
    exact Submodule.smul_mem _ _ hxI
  · intro b hb
    obtain ⟨y, hy⟩ := hint b hb
    have hy' : (y : E) = (a : E) * b := by simpa [Algebra.smul_def] using hy
    refine ⟨(Nj : 𝓞 E) * o₁ * y, ?_⟩
    have e1 : ((Nd * Nj : ℕ) : E) = ((Nd : 𝓞 E) : E) * ((Nj : 𝓞 E) : E) := by push_cast; ring
    rw [e1, ho₁E]
    push_cast
    linear_combination (-((Nj : E) * (o₁ : E))) * hy'

theorem aeGen : ∀ (D : D7) (I : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E), I ≠ 0 →
    ∃ S : Finset (HeightOneSpectrum (𝓞 D.host.F)), ∀ v ∉ S, ∃ c : 𝓞 D.host.F, c ∉ v.asIdeal ∧
      ((c : D.host.F) : D.host.E) ∈ I ∧ ∀ b ∈ I, ∃ o : 𝓞 D.host.E, ((c : D.host.F) : D.host.E) * b = (o : D.host.E) := by
  intro D I hI
  obtain ⟨N, hN0, hNI, hNb⟩ := exists_nat_mem_mul_integral I hI
  have hc0 : Ideal.span {(N : 𝓞 D.host.F)} ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact_mod_cast hN0
  have hfin := Ideal.finite_factors hc0
  refine ⟨hfin.toFinset, fun v hv => ⟨(N : 𝓞 D.host.F), ?_, ?_, ?_⟩⟩
  · intro hmem
    apply hv
    rw [Set.Finite.mem_toFinset, Set.mem_setOf_eq, Ideal.dvd_iff_le, Ideal.span_singleton_le_iff_mem]
    exact hmem
  · have : (((N : 𝓞 D.host.F) : D.host.F) : D.host.E) = (N : D.host.E) := by push_cast; rfl
    rw [this]; exact hNI
  · have : (((N : 𝓞 D.host.F) : D.host.F) : D.host.E) = (N : D.host.E) := by push_cast; rfl
    rw [this]; exact hNb

end GlobalTheory.IdeleGen
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FractionalIdealLocalGeneratorAtBasePrime
section
open Formalism.BasicNotions IsDedekindDomain NumberField

namespace GlobalTheory.LocGen

theorem exists_gen_mul_of_isIntegral {R S : Type*} [CommRing R] [CommRing S] [IsDedekindDomain S] [Algebra R S]
    [Algebra.IsIntegral R S] (hinj : Function.Injective (algebraMap R S)) (p : Ideal R) [p.IsPrime] (hp : p ≠ ⊥)
    (J : Ideal S) (hJ : J ≠ ⊥) :
    ∃ y ∈ J, y ≠ 0 ∧ ∃ c : R, c ∉ p ∧ ∀ j ∈ J, ∃ o : S, algebraMap R S c * j = y * o := by
  obtain ⟨r, hr, hr0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hp
  have hr'0 : algebraMap R S r ≠ 0 := fun h => hr0 (hinj (by rw [h, map_zero]))
  have hJ0 : J ≠ 0 := hJ
  have hIv0 : J * Ideal.span {algebraMap R S r} ≠ 0 :=
    mul_ne_zero hJ0 (by rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]; exact hr'0)
  obtain ⟨y, hy⟩ := exists_sup_span_eq (Ideal.mul_le_left : J * Ideal.span {algebraMap R S r} ≤ J) hIv0
  have hyJ : y ∈ J := hy ▸ Ideal.mem_sup_right (Ideal.mem_span_singleton_self y)
  obtain ⟨K, hK⟩ : J ∣ Ideal.span {y} := Ideal.dvd_iff_le.mpr ((Ideal.span_singleton_le_iff_mem _).mpr hyJ)
  have key : ¬ Ideal.comap (algebraMap R S) K ≤ p := by
    intro h
    obtain ⟨Q, hKQ, hQ, hQp⟩ := Ideal.exists_ideal_over_prime_of_isIntegral p K h
    have hrQ : algebraMap R S r ∈ Q := by
      rw [← Ideal.mem_comap, hQp]; exact hr
    have h1 : J * Ideal.span {algebraMap R S r} ≤ J * Q :=
      Ideal.mul_mono_right ((Ideal.span_singleton_le_iff_mem _).mpr hrQ)
    have h2 : Ideal.span {y} ≤ J * Q := hK ▸ Ideal.mul_mono_right hKQ
    have h3 : J ≤ J * Q := calc J = _ := hy.symm
      _ ≤ J * Q := sup_le h1 h2
    have h4 : J * Q = J * ⊤ := by
      rw [Ideal.mul_top]; exact le_antisymm Ideal.mul_le_left h3
    exact hQ.ne_top (mul_left_cancel₀ hJ0 h4)
  rw [SetLike.not_le_iff_exists] at key
  obtain ⟨c, hcK, hcp⟩ := key
  rw [Ideal.mem_comap] at hcK
  refine ⟨y, hyJ, ?_, c, hcp, ?_⟩
  · rintro rfl
    have hJK : J * K = 0 := by rw [← hK, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    have hK0 : K = 0 := (mul_eq_zero.mp hJK).resolve_left hJ0
    rw [hK0, Ideal.zero_eq_bot, Ideal.mem_bot] at hcK
    exact hcp (by rw [hinj (hcK.trans (map_zero _).symm)]; exact p.zero_mem)
  · intro j hj
    have hm : j * algebraMap R S c ∈ Ideal.span {y} := hK ▸ Ideal.mul_mem_mul hj hcK
    obtain ⟨o, ho⟩ := Ideal.mem_span_singleton'.mp hm
    exact ⟨o, by rw [mul_comm, ← ho, mul_comm]⟩

end GlobalTheory.LocGen

namespace GlobalTheory

open GlobalTheory.LocGen in

theorem fracIdeal_locGen : ∀ (D : D7) (I : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E), I ≠ 0 →
    ∀ v : HeightOneSpectrum (𝓞 D.host.F), ∃ a : D.host.E, a ≠ 0 ∧ ∃ c : 𝓞 D.host.F, c ∉ v.asIdeal ∧
      ((c : D.host.F) : D.host.E) * a ∈ I ∧
      ∀ b ∈ I, ∃ o : 𝓞 D.host.E, ((c : D.host.F) : D.host.E) * b = a * (o : D.host.E) := by
  intro D I hI v
  letI : Algebra (𝓞 D.host.F) (𝓞 D.host.E) := (RingOfIntegers.mapRingHom D.host.F.subtype).toAlgebra
  have hφ : ∀ c : 𝓞 D.host.F, ((algebraMap (𝓞 D.host.F) (𝓞 D.host.E) c : 𝓞 D.host.E) : D.host.E) =
      ((c : D.host.F) : D.host.E) := fun c => rfl
  haveI : Algebra.IsIntegral (𝓞 D.host.F) (𝓞 D.host.E) := Algebra.IsIntegral.tower_top (R := ℤ)
  have hinj : Function.Injective (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) := by
    intro x y h
    have h' := congrArg (fun z : 𝓞 D.host.E => (z : D.host.E)) h
    simp only [hφ] at h'
    exact RingOfIntegers.ext (Subtype.ext h')
  obtain ⟨d, J, hd, rfl⟩ := FractionalIdeal.exists_eq_spanSingleton_mul I
  have hJ : J ≠ ⊥ := by
    rintro rfl
    exact hI (by rw [FractionalIdeal.coeIdeal_bot, mul_zero])
  obtain ⟨y, hyJ, hy0, c, hcv, hc⟩ := exists_gen_mul_of_isIntegral hinj v.asIdeal v.ne_bot J hJ
  have hd' : ((d : 𝓞 D.host.E) : D.host.E) ≠ 0 := by
    rwa [Ne, RingOfIntegers.coe_eq_zero_iff]
  have hy' : ((y : 𝓞 D.host.E) : D.host.E) ≠ 0 := by
    rwa [Ne, RingOfIntegers.coe_eq_zero_iff]
  refine ⟨(y : D.host.E) * (d : D.host.E)⁻¹, mul_ne_zero hy' (inv_ne_zero hd'), c, hcv, ?_, ?_⟩
  · rw [FractionalIdeal.mem_singleton_mul]
    refine ⟨algebraMap (𝓞 D.host.E) D.host.E (algebraMap (𝓞 D.host.F) (𝓞 D.host.E) c * y), ?_, ?_⟩
    · exact (FractionalIdeal.mem_coeIdeal _).mpr ⟨_, J.mul_mem_left _ hyJ, rfl⟩
    · rw [map_mul]
      show _ = _ * (((algebraMap (𝓞 D.host.F) (𝓞 D.host.E) c : 𝓞 D.host.E) : D.host.E) * (y : D.host.E))
      rw [hφ]
      ring
  · intro b hb
    rw [FractionalIdeal.mem_singleton_mul] at hb
    obtain ⟨b', hb', rfl⟩ := hb
    obtain ⟨j, hj, rfl⟩ := (FractionalIdeal.mem_coeIdeal _).mp hb'
    obtain ⟨o, ho⟩ := hc j hj
    refine ⟨o, ?_⟩
    have h2 : ((c : D.host.F) : D.host.E) * (j : D.host.E) = (y : D.host.E) * (o : D.host.E) := by
      have h3 := congrArg (algebraMap (𝓞 D.host.E) D.host.E) ho
      rw [map_mul, map_mul] at h3
      exact h3
    calc ((c : D.host.F) : D.host.E) * (((d : 𝓞 D.host.E) : D.host.E)⁻¹ * (j : D.host.E))
        = (d : D.host.E)⁻¹ * (((c : D.host.F) : D.host.E) * (j : D.host.E)) := by ring
      _ = (d : D.host.E)⁻¹ * ((y : D.host.E) * (o : D.host.E)) := by rw [h2]
      _ = _ := by ring

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FullOfSpanEqTop
section
namespace GlobalTheory.FullLatticeOfSpan

open NumberField

theorem exists_smul_mem {E : Type} [Field E] [NumberField E] {V : Type} [AddCommGroup V]
    [Module E V] [Module (𝓞 E) V] [IsScalarTower (𝓞 E) E V] (N : Submodule (𝓞 E) V) {x : V}
    (hx : x ∈ Submodule.span E (N : Set V)) : ∃ d : 𝓞 E, d ≠ 0 ∧ d • x ∈ N := by
  induction hx using Submodule.span_induction with
  | mem y hy => exact ⟨1, one_ne_zero, by simpa using hy⟩
  | zero => exact ⟨1, one_ne_zero, by simp⟩
  | add y z _ _ hy hz =>
    obtain ⟨a, ha, hay⟩ := hy
    obtain ⟨b, hb, hbz⟩ := hz
    refine ⟨a * b, mul_ne_zero ha hb, ?_⟩
    rw [smul_add]
    refine N.add_mem ?_ ?_
    · rw [mul_comm, mul_smul]; exact N.smul_mem _ hay
    · rw [mul_smul]; exact N.smul_mem _ hbz
  | smul c y _ hy =>
    obtain ⟨a, ha, hay⟩ := hy
    obtain ⟨r, s, hs, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 E) c
    have hs0 : s ≠ 0 := nonZeroDivisors.ne_zero hs
    have hsE : algebraMap (𝓞 E) E s ≠ 0 := by
      intro h
      exact hs0 (IsFractionRing.injective (𝓞 E) E (by rw [h, map_zero]))
    refine ⟨a * s, mul_ne_zero ha hs0, ?_⟩
    have : (a * s) • ((algebraMap (𝓞 E) E r / algebraMap (𝓞 E) E s) • y) = r • (a • y) := by
      rw [← algebraMap_smul E (a * s), ← algebraMap_smul E r, ← algebraMap_smul E a,
        smul_smul, smul_smul, map_mul]
      congr 1
      field_simp
    rw [this]
    exact N.smul_mem _ hay

theorem exists_nat_dvd {E : Type} [Field E] [NumberField E] (d : 𝓞 E) (hd : d ≠ 0) :
    ∃ m : ℕ, 0 < m ∧ d ∣ (m : 𝓞 E) := by
  refine ⟨Ideal.absNorm (Ideal.span {d}), ?_, ?_⟩
  · apply Nat.pos_of_ne_zero
    rw [Ne, Ideal.absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot]
    exact hd
  · exact Ideal.mem_span_singleton.mp (Ideal.absNorm_mem _)

theorem full_of_span_eq_top : ∀ {E : Type} [inst : Field E] [NumberField E] {n : ℕ}
    (N : Submodule (NumberField.RingOfIntegers E) (Formalism.L2.Col.Sp E n)),
    Submodule.span E (↑N : Set (Formalism.L2.Col.Sp E n)) = ⊤ → GlobalTheory.ThetaMove.Full N := by
  intro E _ _ n N hN x
  obtain ⟨d, hd, hdx⟩ := exists_smul_mem N (x := x) (by rw [hN]; trivial)
  obtain ⟨m, hm, c, hc⟩ := exists_nat_dvd d hd
  refine ⟨m, hm, ?_⟩
  rw [hc, mul_comm, mul_smul]
  exact N.smul_mem _ hdx

end GlobalTheory.FullLatticeOfSpan
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.GoodMajorantLevelConjUnitaryAdelicMaximalCompact
section
open scoped Matrix NNReal TensorProduct Classical
open MeasureTheory NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.Eis GlobalTheory.MixModel GlobalTheory.RegSW GlobalTheory.RegSch
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (swSec sZero IsKFinVec)
open GlobalTheory.Core.Rk.SW (sch)
open GlobalTheory.Mem.AutSpace (SmFun)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RegSch

theorem good_level_conj_stab : ∀ (D : D7) (T T₀ : HSp D) (r : ℕ) (d : HypDec T T₀ r) (b : GL (Fin T.rank) (AE D)), IsMaj T b → HasIw d (Kmax T b) → ∀ l : Lvl T, l.Good → HasIw d l.K ∧ IsCompact (l.K : Set (GA D T)) ∧ ∃ q : stab d, ConjBy (q : GA D T) l.K (Kmax T b) := by
  intro D T T₀ r d b hb hIw l hl
  have hL0 : GlobalTheory.EisCont.IsLevel T (AdelicU.frameLat T) b :=
    ⟨AdelicU.SelfDual.isLattice_frameLat T, AdelicU.SelfDual.isSelfDualAt_frameLat D T, hb⟩
  have hL : GlobalTheory.EisCont.IsLevel T l.L l.c := ⟨hl.1, hl.2.1, hl.2.2⟩
  obtain ⟨g, hg⟩ := GlobalTheory.T.exists_adelic_unitary_conj_selfDual_majorant_levels D T (AdelicU.frameLat T) l.L b l.c hL0 hL
  obtain ⟨q, k₀, hk₀, hgq⟩ := hIw g
  have hconj : ConjBy (q : GA D T) l.K (Kmax T b) := by
    intro k
    have h1 : k ∈ l.K ↔ g⁻¹ * k * g ∈ Kmax T b := hg k
    rw [h1, hgq]
    constructor
    · intro h
      have := (Kmax T b).mul_mem (hk₀) ((Kmax T b).mul_mem h ((Kmax T b).inv_mem hk₀))
      simpa [mul_assoc] using this
    · intro h
      have := (Kmax T b).mul_mem ((Kmax T b).inv_mem hk₀) ((Kmax T b).mul_mem h hk₀)
      simpa [mul_assoc] using this
  haveI : Submodule.IsLattice D.host.E l.L := hl.1
  refine ⟨?_, isCompact_levelAll (AdelicU.isCMExt_host D) _ _ _, q, hconj⟩
  intro h
  obtain ⟨q₁, k₁, hk₁, e⟩ := hIw (h * q)
  refine ⟨q₁ * q⁻¹, (q : GA D T) * k₁ * (q : GA D T)⁻¹, ?_, ?_⟩
  · rw [hconj]
    simpa [mul_assoc] using hk₁
  · have : h = (q₁ : GA D T) * k₁ * (q : GA D T)⁻¹ := by rw [← e]; group
    rw [this]; simp [mul_assoc]

end GlobalTheory.RegSch
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HalfGeneratedPointActsScalarOnLatticeVacua
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw ValuativeRel IsLocalRing GlobalTheory.FinPl
open GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData (lastKer)
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.HalfGenScalar

theorem addChar_ne_zero {A : Type} [AddCommGroup A] (ψ : AddChar A ℂ) (a : A) : ψ a ≠ 0 := by
  intro h
  have h1 : ψ a * ψ (-a) = 1 := by rw [← AddChar.map_add_eq_mul, add_neg_cancel, AddChar.map_zero_eq_one]
  rw [h, zero_mul] at h1
  exact zero_ne_one h1

theorem exists_scalar : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (Λ : AddSubgroup (WO S T)) (z : WO S T),
    z ∈ AddSubgroup.closure {u | u ∈ Λ ∧ ∃ e, IsSplitIdem D e ∧ IsHalf e u} →
    ∃ c : ℂ, ∀ f, IsLatVac (heisO ψ S T) Λ f → heisO ψ S T z f = c • f := by
  intro D ψ S T Λ z hz
  induction hz using AddSubgroup.closure_induction with
  | mem u hu =>
    obtain ⟨huΛ, e, he, hh⟩ := hu
    exact ⟨1, fun f hf => by rw [one_smul]; exact hf.2 e he u huΛ hh⟩
  | zero => exact ⟨1, fun f _ => by rw [one_smul]; exact GlobalTheory.SplitScalar.heisO_zero ψ S T f⟩
  | add x y _ _ ihx ihy =>
    obtain ⟨cx, hcx⟩ := ihx
    obtain ⟨cy, hcy⟩ := ihy
    refine ⟨(ψ (symplOH S T x y))⁻¹ * (cx * cy), fun f hf => ?_⟩
    have h1 := GlobalTheory.SplitScalar.heisO_heisO ψ S T x y f
    rw [hcy f hf, GlobalTheory.SplitScalar.heisO_smul, hcx f hf, smul_smul] at h1
    have hne := addChar_ne_zero ψ (symplOH S T x y)
    rw [mul_smul, mul_comm cx cy, h1, smul_smul, inv_mul_cancel₀ hne, one_smul]
  | neg x _ ihx =>
    obtain ⟨cx, hcx⟩ := ihx
    by_cases h0 : cx = 0
    · refine ⟨0, fun f hf => ?_⟩
      have h1 := GlobalTheory.SplitScalar.heisO_heisO ψ S T (-x) x f
      rw [hcx f hf, h0, zero_smul, neg_add_cancel, GlobalTheory.SplitScalar.heisO_zero] at h1
      have hf0 : f = 0 := by
        have h2 : heisO ψ S T (-x) (0 : WO S T → ℂ) = 0 := by
          simpa using GlobalTheory.SplitScalar.heisO_smul ψ S T (-x) 0 (0 : WO S T → ℂ)
        rw [h2] at h1
        exact (smul_eq_zero.1 h1.symm).resolve_left (addChar_ne_zero ψ _)
      subst hf0
      rw [zero_smul]
      simpa using GlobalTheory.SplitScalar.heisO_smul ψ S T (-x) 0 (0 : WO S T → ℂ)
    · refine ⟨ψ (symplOH S T (-x) x) / cx, fun f hf => ?_⟩
      have h1 := GlobalTheory.SplitScalar.heisO_heisO ψ S T (-x) x f
      rw [hcx f hf, GlobalTheory.SplitScalar.heisO_smul, neg_add_cancel, GlobalTheory.SplitScalar.heisO_zero] at h1
      rw [div_eq_inv_mul, mul_smul, ← h1, smul_smul, inv_mul_cancel₀ h0, one_smul]

end GlobalTheory.HalfGenScalar

end
end

