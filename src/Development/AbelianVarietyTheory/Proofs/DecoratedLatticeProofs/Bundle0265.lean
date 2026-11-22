import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0021
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0248
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0210
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0056
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AdelicTransportMeasureSecond
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0321
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0065
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0005
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCombAt
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0014
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0002
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0241
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FlatContrIntIndicator
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FlatMapsPreserveSchwartzBruhatAndSurjective
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitaryConvergent
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0236
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0249
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0017

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RealMeasureUniformInTupleOfThetaLiftScalar
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.ChainTw
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (SplitProj IsProjAt IsIdemOf LiftsChar rdA grpCo frCo gAt)
open GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection (Blocks parahoric datum)
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.LiftRows (Given)

noncomputable section

namespace GlobalTheory.RealMeasOne

variable {D : D7}

theorem ginfC_facts (V : HSp D) : IsTopologicalGroup (GA D V) ∧ LocallyCompactSpace (GA D V) ∧
    SecondCountableTopology (GA D V) ∧ T2Space (GA D V) ∧ BorelSpace (GA D V) ∧ LocallyCompactSpace (GinfC V) ∧
    SecondCountableTopology (GinfC V) ∧ BorelSpace (GinfC V) := by
  obtain ⟨i1, i2, i3, i4, i5, i6, -⟩ := GlobalTheory.Ker.CongTop.adelicUnitary_top_cong D V
  exact ⟨i1, i2, i3, i4, i5, i6.isClosedEmbedding_subtypeVal.locallyCompactSpace,
    Topology.IsInducing.subtypeVal.secondCountableTopology, Subtype.borelSpace _⟩

theorem eq_map_of_lev {V : HSp D} (K : Subgroup (GA D V)) (hK : K ≤ GfC V) (A : Set (GA D V)) (ν : Measure (GA D V))
    (mR : Measure (GinfC V)) (hH : mR.IsHaarMeasure)
    (h : ∀ (f : GinfC V → ℂ) (F : GA D V → ℂ), Integrable f mR → (∀ b : GinfC V, ∀ κ ∈ K, F ((b : GA D V) * κ) = f b) →
      IntegrableOn F A ν ∧ ∫ g in A, F g ∂ν = ∫ b, f b ∂mR) :
    mR = Measure.map (GlobalTheory.AutMult.toInf V) (ν.restrict A) := by
  obtain ⟨i1, i2, i3, i4, i5, i6, i7, i8⟩ := ginfC_facts V
  haveI := hH
  have hmeas : Measurable (GlobalTheory.AutMult.toInf V) := (GlobalTheory.AutMult.continuous_toInf V).measurable

  have hfin : ∀ G : Set (GinfC V), MeasurableSet G → mR G < ⊤ →
      mR G = Measure.map (GlobalTheory.AutMult.toInf V) (ν.restrict A) G := by
    intro G hG hGf
    have hS : MeasurableSet (GlobalTheory.AutMult.toInf V ⁻¹' G) := hmeas hG
    have hf : Integrable (G.indicator fun _ => (1 : ℂ)) mR :=
      (integrable_indicator_iff hG).2 ((integrableOn_const_iff (by simp)).2 (Or.inr hGf))
    obtain ⟨hi, he⟩ := h (G.indicator fun _ => (1 : ℂ)) ((GlobalTheory.AutMult.toInf V ⁻¹' G).indicator fun _ => (1 : ℂ)) hf
      (fun b κ hκ => by
        have h1 : GlobalTheory.AutMult.toInf V ((b : GA D V) * κ) = b := by
          rw [map_mul, GlobalTheory.AutMult.toInf_coe, (GlobalTheory.ChainOnto.HaarInf.toInf_eq_one_iff V κ).2 (hK hκ), mul_one]
        classical
        rw [Set.indicator_apply, Set.indicator_apply, Set.mem_preimage, h1])
    have hi' : ν.restrict A (GlobalTheory.AutMult.toInf V ⁻¹' G) < ⊤ := by
      have := ((integrable_indicator_iff hS).1 hi)
      rcases (integrableOn_const_iff (by simp)).1 this with h0 | h0
      · simp at h0
      · exact h0
    rw [integral_indicator_const _ hS, integral_indicator_const _ hG] at he
    have he' : (ν.restrict A).real (GlobalTheory.AutMult.toInf V ⁻¹' G) = mR.real G := by
      simpa using he
    rw [Measure.map_apply hmeas hG]
    exact ((ENNReal.toReal_eq_toReal_iff' hGf.ne hi'.ne).1 he'.symm)
  refine Measure.ext fun G hG => ?_
  have hU : ⋃ n, G ∩ spanningSets mR n = G := by rw [← Set.inter_iUnion, iUnion_spanningSets, Set.inter_univ]
  have hmono : Monotone fun n => G ∩ spanningSets mR n := fun a b hab =>
    Set.inter_subset_inter_right _ (monotone_spanningSets mR hab)
  rw [← hU, hmono.measure_iUnion, hmono.measure_iUnion]
  refine iSup_congr fun n => hfin _ (hG.inter (measurableSet_spanningSets mR n)) ?_
  exact (measure_mono Set.inter_subset_right).trans_lt (measure_spanningSets_lt_top mR n)

end GlobalTheory.RealMeasOne

namespace GlobalTheory.RealMeasOne

variable {D : D7}

theorem infMat_toInf (V : HSp D) (φ : Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ) (g : GA D V) :
    infMat D.sp.cm.sig V.gram φ (GlobalTheory.AutMult.toInf V g : GA D V) = infMat D.sp.cm.sig V.gram φ g := by
  conv_rhs => rw [← GlobalTheory.AutMult.toInf_mul_toFin g]
  rw [GlobalTheory.PointAtPlaceHom.infMat_mul, GlobalTheory.TensRep.infMat_of_mem_fin V φ (GlobalTheory.AutMult.toFin V g).2, Matrix.mul_one]

theorem eq_of_measLevW {V : HSp D}
    {good : ∀ ρ : D.what₂.Tau, Measure (UpqT (V.sig (tauE D ρ)).1 (V.sig (tauE D ρ)).2) → Prop}
    (hgood : ∀ ρ m, good ρ m → m.IsHaarMeasure)
    {K₁ K₂ : Subgroup (GL (Fin V.rank) (Lev.EAf D))} {ν₁ ν₂ : Measure (GA D V)}
    (h₁ : Lev.IsMeasLevW V K₁ good ν₁) (h₂ : Lev.IsMeasLevW V K₂ good ν₂)
    (m₁ m₂ : Measure (GinfC V)) (hH₁ : m₁.IsHaarMeasure) (hH₂ : m₂.IsHaarMeasure)
    (e₁ : m₁ = Measure.map (GlobalTheory.AutMult.toInf V) (ν₁.restrict {g | Lev.finE V g ∈ K₁}))
    (e₂ : m₂ = Measure.map (GlobalTheory.AutMult.toInf V) (ν₂.restrict {g | Lev.finE V g ∈ K₂})) : m₁ = m₂ := by
  obtain ⟨i1, i2, i3, i4, i5, i6, i7, i8⟩ := ginfC_facts V
  haveI := hH₁
  haveI := hH₂
  have := fun P Q => (GlobalTheory.UpqTopology.upq_lcsc P Q).1
  have := fun P Q => (GlobalTheory.UpqTopology.upq_lcsc P Q).2.1
  have := fun P Q => (GlobalTheory.UpqTopology.upq_lcsc P Q).2.2.1
  have := fun P Q => (GlobalTheory.UpqTopology.upq_lcsc P Q).2.2.2.2.1
  obtain ⟨-, ⟨θ, hθ⟩, h1⟩ := h₁
  obtain ⟨⟨A, hA⟩, h1⟩ := h1 θ hθ
  obtain ⟨⟨m, hm⟩, h1⟩ := h1 A hA
  obtain ⟨-, -, h2⟩ := h₂
  obtain ⟨-, h2⟩ := h2 θ hθ
  obtain ⟨-, h2⟩ := h2 A hA
  have h2 := h2 m hm
  let B : ∀ ρ : D.what₂.Tau, TopologicalSpace.PositiveCompacts (UpqT (V.sig (tauE D ρ)).1 (V.sig (tauE D ρ)).2) :=
    fun ρ => Classical.arbitrary _
  have hB : ∀ ρ, MeasurableSet (B ρ : Set (UpqT (V.sig (tauE D ρ)).1 (V.sig (tauE D ρ)).2)) := fun ρ =>
    (B ρ).isCompact.measurableSet
  let S : Set (GA D V) := {h | ∀ ρ, ∃ b ∈ (B ρ : Set _), UpqT.mat b * A ρ = A ρ * infMat D.sp.cm.sig V.gram (θ ρ) h}
  have hSc : IsClosed S := by
    have e : S = ⋂ ρ, (fun h => A ρ * infMat D.sp.cm.sig V.gram (θ ρ) h) ⁻¹'
        ((fun b => UpqT.mat b * A ρ) '' (B ρ : Set (UpqT (V.sig (tauE D ρ)).1 (V.sig (tauE D ρ)).2))) := by
      ext h
      simp only [Set.mem_iInter]
      exact Iff.rfl
    rw [e]
    refine isClosed_iInter fun ρ => IsClosed.preimage ?_ ?_
    · exact continuous_const.matrix_mul (GlobalTheory.Mem.VolExists.continuous_infMat (σ := D.sp.cm.sig) V.gram (hθ ρ))
    · exact ((B ρ).isCompact.image ((GlobalTheory.UpqTopology.continuous_mat).matrix_mul continuous_const)).isClosed
  have hS : MeasurableSet S := hSc.measurableSet
  let E : Set (GinfC V) := Subtype.val ⁻¹' S
  have hE : MeasurableSet E := measurable_subtype_coe hS
  have hpre : GlobalTheory.AutMult.toInf V ⁻¹' E = S := by
    ext h
    simp only [E, S, Set.mem_preimage, Set.mem_setOf_eq, infMat_toInf]
  have hval : ∀ (K : Subgroup (GL (Fin V.rank) (Lev.EAf D))) (ν : Measure (GA D V)),
      Measure.map (GlobalTheory.AutMult.toInf V) (ν.restrict {g | Lev.finE V g ∈ K}) E =
        ν {h | Lev.finE V h ∈ K ∧ ∀ ρ, ∃ b ∈ (B ρ : Set _), UpqT.mat b * A ρ = A ρ * infMat D.sp.cm.sig V.gram (θ ρ) h} := by
    intro K ν
    rw [Measure.map_apply (GlobalTheory.AutMult.continuous_toInf V).measurable hE, hpre, Measure.restrict_apply hS]
    congr 1
    ext h
    exact and_comm
  have v1 : m₁ E = ∏ ρ, m ρ (B ρ) := by rw [e₁, hval]; exact h1 m hm (fun ρ => B ρ) hB
  have v2 : m₂ E = ∏ ρ, m ρ (B ρ) := by rw [e₂, hval]; exact h2 (fun ρ => B ρ) hB
  have h0 : ∏ ρ, m ρ (B ρ) ≠ 0 := Finset.prod_ne_zero_iff.2 fun ρ _ => by
    have := hgood ρ (m ρ) (hm ρ)
    exact (Measure.measure_pos_of_nonempty_interior (m ρ) (B ρ).interior_nonempty).ne'
  have ht : ∏ ρ, m ρ (B ρ) ≠ ⊤ := ENNReal.prod_ne_top fun ρ _ => by
    have := hgood ρ (m ρ) (hm ρ)
    exact (B ρ).isCompact.measure_lt_top.ne
  have e : m₂ = ((Measure.haarScalarFactor m₂ m₁ : NNReal) : ENNReal) • m₁ := Measure.isMulLeftInvariant_eq_smul m₂ m₁
  have e' := v2
  rw [e, Measure.smul_apply, v1, smul_eq_mul] at e'
  have hc : ((Measure.haarScalarFactor m₂ m₁ : NNReal) : ENNReal) = 1 :=
    (ENNReal.mul_left_inj h0 ht).1 (e'.trans (one_mul _).symm)
  rw [e, hc, one_smul]

end GlobalTheory.RealMeasOne

namespace GlobalTheory.RealMeasOne

theorem models_good {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (hM : R.IsModels) (j : ℕ)
    (hj : j < D.R.m) :
    ∃ good : ∀ ρ : D.what₂.Tau, Measure (UpqT ((Yc D j).sig (tauE D ρ)).1 ((Yc D j).sig (tauE D ρ)).2) → Prop,
      (∀ ρ m, good ρ m → m.IsHaarMeasure) ∧
      ∀ t, Lev.IsMeasLevW (Yc D j) (lev D.sp.cm (Yc D j).gram (R.βY j) (R.datYt t j R.triv)) good (R.νY t j) := by
  rcases Nat.lt_or_ge (j + 1) D.R.m with h | h
  · exact ⟨fun _ m => Lev.IsMinf m, fun _ _ hm => hm.1, fun t => (hM.νY t j h).1⟩
  · obtain rfl : j = D.R.m - 1 := by omega
    exact ⟨fun _ m => m.IsHaarMeasure ∧ IsProbabilityMeasure m, fun _ _ hm => hm.1, fun t => (hM.νY' t).1⟩

theorem one_real_measure : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), Given R F →
    (∀ h : RangeX R, RChain R h) → RangeX R → RMeas R := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F hG hC hR j hj
  by_cases hT : Nonempty T
  swap
  · exact ⟨0, fun t => (hT ⟨t⟩).elim⟩
  obtain ⟨t₀⟩ := hT
  have hlev : ∀ t, ∃ mR, IsLevMeas (stY R t j) mR := fun t =>
    (GlobalTheory.T.thetaChainStage_finiteLevel_eq_product_localLevels D (comR R t) (twR R t) (hC hR t).1 j hj.le (stY R t j) ((hC hR t).2.1 j hj)).2.2.2.2.2
  choose mR hmR using hlev
  obtain ⟨good, hgood, hW⟩ := models_good R hG.core.models j hj
  have hmap : ∀ t, mR t = Measure.map (GlobalTheory.AutMult.toInf (Yc D j))
      ((R.νY t j).restrict {g | Lev.finE (Yc D j) g ∈ lev D.sp.cm (Yc D j).gram (R.βY j) (R.datYt t j R.triv)}) := fun t => by
    exact eq_map_of_lev (Lev.levG (Yc D j) (R.βY j) (R.datYt t j R.triv)) inf_le_left _ _ (mR t) (hmR t).1 (hmR t).2
  refine ⟨mR t₀, fun t => ?_⟩
  have e : mR t = mR t₀ := by
    exact eq_of_measLevW hgood (hW t) (hW t₀) (mR t) (mR t₀) (hmR t).1 (hmR t₀).1 (hmap t) (hmap t₀)
  rw [← e]
  exact hmR t

end GlobalTheory.RealMeasOne

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SliceColMem
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.StepData GlobalTheory.SymChain

noncomputable section
namespace GlobalTheory.LocMod.GValProof

section
variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem card_frame {N : ℕ} {Y : Type} [Fintype Y] [DecidableEq Y] (F : Frame k N Y) : Fintype.card Y = N := by
  apply le_antisymm
  · calc Fintype.card Y = (F.γ * F.β).rank := by rw [F.γβ, Matrix.rank_one]
      _ ≤ F.β.rank := Matrix.rank_mul_le_right _ _
      _ ≤ Fintype.card (Fin N) := Matrix.rank_le_card_height _
      _ = N := Fintype.card_fin N
  · calc N = Fintype.card (Fin N) := (Fintype.card_fin N).symm
      _ = (F.β * F.γ).rank := by rw [F.βγ, Matrix.rank_one]
      _ ≤ F.γ.rank := Matrix.rank_mul_le_right _ _
      _ ≤ Fintype.card Y := Matrix.rank_le_card_height _

theorem core_of_bes (p : Place D k) {ρ : ℕ} (B : BesLev D ρ) (s : k) {n : Type} [Fintype n] [DecidableEq n] {c : ℕ}
    (FA : Frame k B.A.rank n) (G : Frame k B.V.rank (n ⊕ Fin c)) (h : p.IsBesFrame B s FA G) :
    ∃ F₀ : Frame k B.V₀.rank (n ⊕ Unit), p.IsCoreFrame B s FA F₀ := by
  obtain ⟨hc, hA, -, hz, -⟩ := h
  let f : D.host.E →+* k := p.π.comp (incA D)
  have hpr : ∀ a, p.pr a = f a := fun _ => rfl
  let e : n ⊕ Unit → n ⊕ Fin c := Sum.elim Sum.inl fun _ => Sum.inr ⟨ρ, by omega⟩
  have he : Function.Injective e := by
    rintro (a | ⟨⟩) (b | ⟨⟩) hab <;> simp_all [e]
  let βA : Matrix (Fin B.V₀.rank) n k := B.o.iA.map p.pr * FA.β
  let β : Matrix (Fin B.V₀.rank) (n ⊕ Unit) k :=
    Matrix.of fun r y => Sum.elim (fun a => βA r a) (fun _ => s * p.pr (vecB B.o B.ζ r)) y
  let I : Matrix (Fin B.V.rank) (Fin B.V₀.rank) k := B.d.i₀.map p.pr
  have hmap : I * B.o.iA.map p.pr = (B.d.i₀ * B.o.iA).map p.pr := (Matrix.map_mul (f := f)).symm
  have hIβ : I * β = G.β.submatrix id e := by
    ext r (a | ⟨⟩)
    · simp only [submatrix_apply, id, e, Sum.elim_inl]
      rw [hA]
      have : (I * β) r (Sum.inl a) = (I * βA) r a := by
        simp only [Matrix.mul_apply, β, Matrix.of_apply, Sum.elim_inl]
      rw [this, ← Matrix.mul_assoc, hmap]
    · simp only [submatrix_apply, id, e, Sum.elim_inr]
      rw [hz ⟨ρ, by omega⟩ rfl r, hpr, RingHom.map_mulVec]
      simp only [Matrix.mul_apply, β, Matrix.of_apply, Sum.elim_inr, mulVec, dotProduct, Finset.mul_sum, I,
        Function.comp_apply, hpr]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [Matrix.map_apply, hpr]
      ring
  let γ : Matrix (n ⊕ Unit) (Fin B.V₀.rank) k := G.γ.submatrix e id * I
  have hγβ : γ * β = 1 := by
    rw [Matrix.mul_assoc, hIβ, ← Matrix.submatrix_mul _ _ _ _ _ Function.bijective_id, G.γβ, Matrix.submatrix_one _ he]
  have hcard : Fintype.card (n ⊕ Unit) = B.V₀.rank := by
    have h1 := card_frame G
    have h2 := B.d.rank_add
    simp only [Fintype.card_sum, Fintype.card_fin, Fintype.card_unit] at h1 ⊢
    omega
  have hβγ : β * γ = 1 := (Matrix.mul_eq_one_comm_of_equiv (Fintype.equivFinOfCardEq hcard)).1 hγβ
  exact ⟨⟨β, γ, hβγ, hγβ⟩, fun r a => rfl, fun r => rfl⟩

theorem hz_link (p : Place D k) {ρ σ : ℕ} (B : BesLev D ρ) (B' : BesLev D σ) (l : Link B B'.L B'.ζ) :
    p.hz B = -p.xi ^ 2 * p.hz B' := by
  let f : D.host.E →+* k := p.π.comp (incA D)
  have hpr : ∀ a, p.pr a = f a := fun _ => rfl
  rw [Place.hz, Place.hz, Place.xi, l.norm, hpr, hpr, hpr, map_mul, map_mul, GlobalTheory.DualPairCheck.star_purely_imaginary_eq_neg, map_neg]
  ring

theorem cont_of_cond (ψ : AddChar k Circle) (h : HasConductor ψ 1) : Continuous ψ := h.continuous

theorem one_mem_SB (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] :
    (Set.indicator {x : Matrix n n' k | ∀ r q, x r q ∈ 𝒪[k]} fun _ => (1 : ℂ)) ∈ SB (Matrix n n' k) := by
  set S : Set (Matrix n n' k) := {x | ∀ r q, x r q ∈ 𝒪[k]} with hSdef
  have hS : (S : Set (n → n' → k)) = Set.univ.pi fun _ => Set.univ.pi fun _ => (𝒪[k] : Set k) := by
    ext x
    exact ⟨fun h r _ q _ => h r q, fun h r q => h r (Set.mem_univ _) q (Set.mem_univ _)⟩
  have hO : IsOpen S := by
    change IsOpen (S : Set (n → n' → k))
    rw [hS]
    exact isOpen_set_pi Set.finite_univ fun _ _ => isOpen_set_pi Set.finite_univ fun _ _ =>
      Valuation.isOpen_integer (v := valuation k)
  have hK : IsCompact S := by
    change IsCompact (S : Set (n → n' → k))
    rw [hS]
    exact isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => IsNonarchimedeanLocalField.isCompact_closedBall k 1
  refine ⟨?_, HasCompactSupport.intro hK fun x hx => by simp [Set.indicator, hx]⟩
  refine (IsLocallyConstant.iff_exists_open _).2 fun x => ?_
  by_cases hx : x ∈ S
  · exact ⟨S, hO, hx, fun y hy => by simp [Set.indicator, hy, hx]⟩
  · exact ⟨Sᶜ, hK.isClosed.isOpen_compl, hx, fun y hy => by
      have hy' : y ∉ S := hy
      simp [Set.indicator, hy', hx]⟩

theorem sliceCol_mem {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] {f : Matrix n (n' ⊕ Unit) k → ℂ}
    (hf : f ∈ SB _) : (fun a : Matrix n n' k => f (fromCols a 0)) ∈ SB _ := by
  have hc : Continuous fun a : Matrix n n' k => fromCols a (0 : Matrix n Unit k) := by
    refine continuous_matrix fun i j => ?_
    rcases j with j | j
    · simp only [fromCols_apply_inl]; exact continuous_id.matrix_elem i j
    · simp only [fromCols_apply_inr]; exact continuous_const
  have hd : Continuous fun x : Matrix n (n' ⊕ Unit) k => x.toCols₁ :=
    continuous_matrix fun i j => continuous_id.matrix_elem i (Sum.inl j)
  refine ⟨hf.1.comp_continuous hc, HasCompactSupport.intro (hf.2.isCompact.image hd) fun a ha => ?_⟩
  by_contra h0
  exact ha ⟨fromCols a 0, subset_tsupport _ h0, toCols₁_fromCols _ _⟩

theorem sliceRow_mem {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] {f : Matrix (n ⊕ Unit) n' k → ℂ}
    (hf : f ∈ SB _) : (fun a : Matrix n n' k => f (fromRows a 0)) ∈ SB _ := by
  have hc : Continuous fun a : Matrix n n' k => fromRows a (0 : Matrix Unit n' k) := by
    refine continuous_matrix fun i j => ?_
    rcases i with i | i
    · simp only [fromRows_apply_inl]; exact continuous_id.matrix_elem i j
    · simp only [fromRows_apply_inr]; exact continuous_const
  have hd : Continuous fun x : Matrix (n ⊕ Unit) n' k => x.toRows₁ :=
    continuous_matrix fun i j => continuous_id.matrix_elem (Sum.inl i) j
  refine ⟨hf.1.comp_continuous hc, HasCompactSupport.intro (hf.2.isCompact.image hd) fun a ha => ?_⟩
  by_contra h0
  exact ha ⟨fromRows a 0, subset_tsupport _ h0, toRows₁_fromRows _ _⟩
end

theorem gval : ∀ (D : D7), FlatBF D → FlatFB D → ContrLoc D → GlobalTheory.LocFlat.SymCollapse →
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (ν : Measure k), IsUnitVol ν →
  ∀ (p : Place D k) (s κ : ℕ) (S : SymData k s κ) (t : Type) [Fintype t] [DecidableEq t]
    (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → p.IsChar ψ S.ψ → ∀ (j c : ℕ) (H : j + 1 + 1 + c = s), ∃ C : ℂ, C ≠ 0 ∧
  ∀ (σ : ℕ) (B : BesLev D (σ + 1))
    (J : JacLev D (σ + 1)) (B' : BesLev D σ) (F : Dbl p B J B' (XIx (Fin κ) t j) (XIx (Fin κ) t (j + 1)) (XIx (Fin κ) t (j + 1 + 1)) c)
    (s₁ : StepBF ψ B J) (s₂ : StepFB ψ J B') (l : Link B B'.L B'.ζ) (vL : VolM D B'.L.rank J.W₀.rank)
    (c₁ : WO B.A J.W₀ →₀ ℂ) (c₂ : WO J.W₀ B'.A →₀ ℂ),
    p.IsCombAt ψ F.F₀ F.F₁ c₁ ((S.T t).entry S.ψ ν j (c + 1) (by omega) 1 1) →
    p.IsCombAt ψ F.F₁ F.F₂ c₂ ((S.T t).entry S.ψ ν (j + 1) c H 1 1) →
  ∀ T₁ T₂, p.IsModel ψ F.G₀ F.G₁ T₁ → p.IsModel ψ F.G₁ F.G₂ T₂ → ∀ Φ₁ Φ₂ O₁ O₂,
    Φ₁.1 = (S.T t).Phi j (c + 1 + 1) (by omega) → Φ₂.1 = (S.T t).Phi (j + 1) (c + 1) (by omega) → IsOne O₁ → IsOne O₂ →
    GlobalTheory.Unf.contr l J.W₀ vL (flatBF s₁ (T₁ Φ₁)) (flatFB s₂ (T₂ Φ₂)) =
      C • biComb ψ B.A J.W₀ B'.A c₁ c₂ (GlobalTheory.Unf.contr l J.W₀ vL (flatBF s₁ (T₁ O₁)) (flatFB s₂ (T₂ O₂))) := by
  intro D hBF hFB hCL hSym k _ _ _ _ _ _ ν hν p s κ S t _ _ ψ hstd hchar j c H
  by_cases hc : ∃ r, c = 2 * r
  swap
  · refine ⟨1, one_ne_zero, ?_⟩
    intro σ B J B' F
    exact absurd ⟨σ, by have := F.bes.1; omega⟩ hc
  obtain ⟨r, hr⟩ := hc
  obtain ⟨-, hPC, hPR, hDS⟩ := hSym k ν hν s κ S t
  obtain ⟨-, C, hC, hval⟩ := hDS j c H r hr
  refine ⟨(C : ℂ), by exact_mod_cast hC.ne', ?_⟩
  intro σ B J B' F s₁ s₂ l vL c₁ c₂ hc₁ hc₂ T₁ T₂ hT₁ hT₂ Φ₁ Φ₂ O₁ O₂ hΦ₁ hΦ₂ hO₁ hO₂
  have hσ : σ = r := by have := F.bes.1; omega
  subst hσ
  have hψc : Continuous S.ψ := cont_of_cond S.ψ S.cond
  obtain ⟨C₀, hC₀⟩ := core_of_bes p B F.s F.F₀ F.G₀ F.bes
  obtain ⟨C₂, hC₂⟩ := core_of_bes p B' (F.s * p.xi) F.F₂ F.G₂ F.bes'
  have hjac : p.IsJacFrame J F.s (-p.xi ^ 2 * p.hz B') F.F₁ F.G₁ := by
    rw [← hz_link p B B' l]; exact F.jac
  obtain ⟨U₁, hU₁, hU₁e⟩ := hBF k p ν hν.1 ψ S.ψ hchar (σ + 1) B J s₁ F.s F.s_ne _ _ (c + 1 + 1) F.F₀ C₀ F.G₀ F.F₁ F.G₁ hC₀ F.bes F.jac T₁ hT₁
  obtain ⟨U₂, hU₂, hU₂e⟩ := hFB k p ν hν.1 ψ S.ψ hchar σ J B' s₂ F.s F.s_ne _ _ (c + 1) F.F₁ F.G₁ F.F₂ C₂ F.G₂ hjac hC₂ F.bes' T₂ hT₂
  obtain ⟨Λ, hΛ, hΛe⟩ := hCL k p ν hν.1 ψ hstd S.ψ hchar (σ + 1) σ B B' l J.W₀ vL F.s F.s_ne _ _ _ F.F₀ C₀ F.F₁ F.F₂ C₂ hC₀ hC₂ U₁ U₂ hU₁ hU₂
  have hfl := GlobalTheory.LocFlat.flat_SB_onto k S.ψ ν hψc hν.1
  have m₁ := fun Φ : SB _ => ((hfl (XIx (Fin κ) t (j + 1)) (XIx (Fin κ) t j) (c + 1 + 1) (σ + 1 + 1) (by omega)).1 (by omega)).1 Φ.1 Φ.2
  have m₂ := fun Φ : SB _ => ((hfl (XIx (Fin κ) t (j + 1 + 1)) (XIx (Fin κ) t (j + 1)) (c + 1) (σ + 1) (by omega)).2 (by omega)).1 Φ.1 Φ.2
  let Ψ₁ : SB _ := ⟨_, m₁ Φ₁⟩
  let Ψ₂ : SB _ := ⟨_, m₂ Φ₂⟩
  let P₁ : SB _ := ⟨_, m₁ O₁⟩
  let P₂ : SB _ := ⟨_, m₂ O₂⟩
  rw [hU₁e Φ₁ Ψ₁ rfl, hU₂e Φ₂ Ψ₂ rfl, hU₁e O₁ P₁ rfl, hU₂e O₂ P₂ rfl]
  obtain ⟨Ξ, hΞ, e1⟩ := hΛe Ψ₁ Ψ₂
  obtain ⟨ΞO, hΞO, e2⟩ := hΛe P₁ P₂
  rw [e1, e2]

  have hE₁ : (S.T t).entry S.ψ ν j (c + 1) (by omega) 1 1 ∈ SB _ := by
    obtain ⟨C', hC', hpc⟩ := hPC j (c + 1) (by omega) (σ + 1) (by omega)
    have hs := sliceCol_mem Ψ₁.2
    have e : (S.T t).entry S.ψ ν j (c + 1) (by omega) 1 1 = (C'⁻¹ : ℂ) • fun a => Ψ₁.1 (fromCols a 0) := by
      funext a
      simp only [Ψ₁, Pi.smul_apply, smul_eq_mul]
      rw [hΦ₁, hpc]
      have hC'0 : (C' : ℂ) ≠ 0 := by exact_mod_cast hC'.ne'
      simp only [toCols₁_fromCols, fromCols_apply_inr, Matrix.zero_apply]
      have hz : (fun _ => (0 : k)) ∈ box (XIx (Fin κ) t (j + 1)) (S.ϖ ^ (σ + 1))⁻¹ := (box _ _).zero_mem
      simp only [hz, if_true, mul_one]
      rw [← mul_assoc, inv_mul_cancel₀ hC'0, one_mul]
    rw [e]; exact (SB _).smul_mem _ hs
  have hE₂ : (S.T t).entry S.ψ ν (j + 1) c H 1 1 ∈ SB _ := by
    obtain ⟨C', hC', hpr⟩ := hPR (j + 1) c H σ hr
    have hs := sliceRow_mem Ψ₂.2
    have e : (S.T t).entry S.ψ ν (j + 1) c H 1 1 = (C'⁻¹ : ℂ) • fun a => Ψ₂.1 (fromRows a 0) := by
      funext a
      simp only [Ψ₂, Pi.smul_apply, smul_eq_mul]
      rw [hΦ₂, hpr]
      have hC'0 : (C' : ℂ) ≠ 0 := by exact_mod_cast hC'.ne'
      simp only [toRows₁_fromRows, fromRows_apply_inr, Matrix.zero_apply]
      have hz : a.fromRows (0 : Matrix Unit (XIx (Fin κ) t (j + 1)) k) (Sum.inr ()) ∈ box (XIx (Fin κ) t (j + 1)) (S.ϖ ^ (σ + 1)) := (box _ _).zero_mem
      simp only [hz, if_true, mul_one]
      rw [← mul_assoc, inv_mul_cancel₀ hC'0, one_mul]
    rw [e]; exact (SB _).smul_mem _ hs
  let E₁ : SB _ := ⟨_, hE₁⟩
  let E₂ : SB _ := ⟨_, hE₂⟩
  have hCne : (C : ℂ) ≠ 0 := by exact_mod_cast hC.ne'
  have hΞ' : ∀ q, ((C : ℂ)⁻¹ • Ξ).1 q = E₁.1 q.1 * E₂.1 q.2 := by
    intro q
    rw [Submodule.coe_smul, Pi.smul_apply, hΞ]
    simp only [Ψ₁, Ψ₂, E₁, E₂]
    rw [hΦ₁, hΦ₂, hval q, smul_eq_mul]
    field_simp
  have hΞe : Ξ = (C : ℂ) • ((C : ℂ)⁻¹ • Ξ) := by rw [smul_smul, mul_inv_cancel₀ hCne, one_smul]

  have hun := GlobalTheory.LocFlat.flat_contr_intIndicator k S.ψ ν S.cond hν
  let Q₁ : SB (Matrix (XIx (Fin κ) t (j + 1)) (XIx (Fin κ) t j) k) := ⟨_, one_mem_SB _ _⟩
  let Q₂ : SB (Matrix (XIx (Fin κ) t (j + 1 + 1)) (XIx (Fin κ) t (j + 1)) k) := ⟨_, one_mem_SB _ _⟩
  have hP₁ : P₁.1 = Set.indicator {x : Matrix (XIx (Fin κ) t (j + 1)) (XIx (Fin κ) t j ⊕ Unit) k | ∀ r q, x r q ∈ 𝒪[k]} fun _ => 1 := by
    simp only [P₁]
    rw [hO₁, (hun (XIx (Fin κ) t (j + 1)) (XIx (Fin κ) t j) (XIx (Fin κ) t j) (c + 1 + 1) (σ + 1 + 1)).1, if_neg (by omega)]
  have hP₂ : P₂.1 = Set.indicator {x : Matrix (XIx (Fin κ) t (j + 1 + 1) ⊕ Unit) (XIx (Fin κ) t (j + 1)) k | ∀ r q, x r q ∈ 𝒪[k]} fun _ => 1 := by
    simp only [P₂]
    rw [hO₂, (hun (XIx (Fin κ) t (j + 1 + 1)) (XIx (Fin κ) t (j + 1)) (XIx (Fin κ) t j) (c + 1) (σ + 1)).2.1 (by omega) (by omega)]
  have hΞO' : ∀ q, ΞO.1 q = Q₁.1 q.1 * Q₂.1 q.2 := by
    intro q
    rw [hΞO, hP₁, hP₂]
    exact (hun (XIx (Fin κ) t (j + 1)) (XIx (Fin κ) t j) (XIx (Fin κ) t (j + 1 + 1)) 0 0).2.2 q
  have hbi := (GlobalTheory.BiComb.comb_bimodel_and_line D k p ψ _ _ _).1 B.A J.W₀ B'.A F.F₀ F.F₁ F.F₂ Λ c₁ c₂ E₁ Q₁ E₂ Q₂ ((C : ℂ)⁻¹ • Ξ) ΞO hΛ hc₁ hc₂ rfl rfl hΞ' hΞO'
  rw [hΞe, map_smul, hbi]

theorem gval_of_laws : ∀ (D : D7), FlatBF D → FlatFB D → ContrLoc D → GlobalTheory.LocFlat.SymCollapse → GVal D := by
  intro D hBF hFB hCL hSym k _ _ _ _ _ _ ν hν p s κ S t _ _ ψ hchar j c H
  by_cases hstd : IsStdChar D ψ (-1)
  · exact gval D hBF hFB hCL hSym k ν hν p s κ S t ψ hstd hchar j c H
  · refine ⟨1, one_ne_zero, ?_⟩
    intro σ B J B' F s₁
    exact absurd s₁.weil.std hstd

end GlobalTheory.LocMod.GValProof
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.StandardUnitaryChartMemRationalIff
section
open scoped Matrix NNReal ComplexConjugate TensorProduct ContDiff
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.Core.Rk.SWLaw GlobalTheory.Core.Rk.SW GlobalTheory.StdUnn
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (RealMat IsFockVec)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (swSec sZero)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.StdUnn.ChartRat

variable {D : D7}

theorem mem_GF_iff {n : ℕ} (g : G D n) : g ∈ GF D n ↔ mat g ∈ ratMx D (n + n) (n + n) := by
  constructor
  · rintro ⟨γ, -, h⟩
    exact ⟨γ.1, congrArg Units.val h⟩
  · rintro ⟨γ, hγ⟩
    replace hγ : rat γ = mat g := hγ
    have h : γᴴ * Jst D n * γ = Jst D n := by
      apply rat_injective
      rw [rat_mul, rat_mul, rat_conjTranspose, hγ]
      exact g.2
    have hdet : γ.det ≠ 0 := by
      intro h0
      have hu : IsUnit (mat g).det := Matrix.isUnits_det_units _
      rw [← hγ, rat, ← RingHom.mapMatrix_apply, ← RingHom.map_det, h0, map_zero] at hu
      have h01 : (0 : AE D) = 1 := isUnit_zero_iff.1 hu
      exact zero_ne_one (incA_injective (D := D) (by rw [map_zero, map_one]; exact h01))
    exact ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero γ hdet, h, Units.ext hγ⟩

end GlobalTheory.StdUnn.ChartRat

namespace GlobalTheory.StdUnn

theorem chart_mem_GF_iff : ∀ (D : D7) (A : HSp D) (μ : D.host.E), IsSkew μ → ∀ κ : GA D (dblSp A) ≃* G D A.rank,
    IsChart A μ κ → ∀ g, g ∈ GQ (dblSp A) ↔ κ g ∈ GF D A.rank := by
  intro D A μ hμ κ hκ g
  obtain ⟨-, hdet, -⟩ := GlobalTheory.T.doubledBasisSkewColumnMatrix_gram_inverse D A μ hμ
  have hTi : rat (Tm A μ)⁻¹ * rat (Tm A μ) = 1 := by
    rw [← rat_mul, Matrix.nonsing_inv_mul _ hdet, rat_one]
  have hTi' : rat (Tm A μ) * rat (Tm A μ)⁻¹ = 1 := by
    rw [← rat_mul, Matrix.mul_nonsing_inv _ hdet, rat_one]
  have e1 : mat (κ g) = rat (Tm A μ)⁻¹ * (mt (dblSp A) g * rat (Tm A μ)) := by
    rw [← hκ g, ← Matrix.mul_assoc, hTi, Matrix.one_mul]
  have e2 : mt (dblSp A) g = rat (Tm A μ) * mat (κ g) * rat (Tm A μ)⁻¹ := by
    rw [hκ g, Matrix.mul_assoc, hTi', Matrix.mul_one]
  rw [GlobalTheory.MixModel.mem_GQ_iff, ChartRat.mem_GF_iff]
  constructor
  · intro h
    rw [e1]
    exact ratMx_mul (rat_mem _) (ratMx_mul h (rat_mem _))
  · intro h
    rw [e2]
    exact ratMx_mul (ratMx_mul (rat_mem _) h) (rat_mem _)

end GlobalTheory.StdUnn
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaChainLocalZetaNonvanishingOfRealStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaChainLocalZetaNonvanishing_of_real : ∀ D : D7, MetEx D → LevFacts D → LevelLaw D → CoefSupp D → RealZeta D → ZetaNe D := by
  first | exact @GlobalTheory.ChainOnto.ZetaNeProof.zetaNe_of_real | exact GlobalTheory.ChainOnto.ZetaNeProof.zetaNe_of_real | (intros; apply GlobalTheory.ChainOnto.ZetaNeProof.zetaNe_of_real <;> assumption)
end

