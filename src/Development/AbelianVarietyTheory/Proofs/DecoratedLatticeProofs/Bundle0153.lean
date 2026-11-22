import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0012
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0015
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0008
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0024
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.TransvectionAction
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0009
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0291
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0296
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0027
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0023
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0299
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUnramifiedHeckeCharHalfExponentRestrictQua
import Formalism.LocalToGlobal.BesselHermitianTheta.Bundle0003
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ContinuousResTSymm
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ComplexEmbeddingHermitianQuadrupleSum
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0289
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0032
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0068
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0147
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0105
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0106
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0124
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0142
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0121
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0128
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0122
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0127
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0143
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0014
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsClosedNFlag
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0214
import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.Bundle0005
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsMulRightInvariantOfFundamentalDomain
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0199
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0144
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.EntryAgree
import Formalism.LocalToGlobal.Columns.ChainTw
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0008
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0137
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0132
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0148

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CharacterAnnihilatorCompactBox
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf
open scoped ComplexOrder ENNReal NNReal ContDiff

namespace GlobalTheory.MatAnnih

theorem trace_mul_smul_single (D : D7) {m n : ℕ} (y : Mx D n m) (r : AF D.host.F) (i : Fin n) (j : Fin m)
    (a : D.host.E) :
    Algebra.trace (AF D.host.F) (AE D) (y ⬝ (r • Matrix.single j i (incA D a) : Mx D m n)).trace =
      r * Algebra.trace (AF D.host.F) (AE D) (incA D a * y i j) := by
  rw [Matrix.mul_smul, Matrix.trace_smul, Matrix.trace_mul_single, map_smul, smul_eq_mul, op_smul_eq_mul, mul_comm (y i j)]

theorem finPart_sum_tmul (D : D7) {d : ℕ} (x : Fin d → Af D.host.F) (e : Fin d → D.host.E) :
    finPart D (∑ l, pairA D.host.F 0 (x l) ⊗ₜ[D.host.F] e l) = ∑ l, x l ⊗ₜ[D.host.F] e l := by
  unfold finPart
  rw [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, map_sum]
  rfl

theorem annih_mem_box : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (m n : ℕ), ∀ V ∈ nhds (0 : Mx D m n), ∃ K : Set (Mx D n m), IsCompact K ∧ ∀ y : Mx D n m, (∀ ξ ∈ V, ξ.map (infPart D) = 0 → ψ (Algebra.trace (AF D.host.F) (AE D) (y ⬝ ξ).trace) = 1) → InBox K y := by
  intro D ψ hψ m n V hV
  obtain ⟨d, c, e, hce⟩ := GlobalTheory.TwistCoords.finPart_eq_sum_trace D
  haveI : IsModuleTopology (AF D.host.F) (AE D) := ⟨rfl⟩
  haveI : ContinuousSMul (AF D.host.F) (AE D) := IsModuleTopology.toContinuousSMul _ _

  let M : (Fin n × Fin m × Fin d) → Mx D m n := fun p => Matrix.single p.2.1 p.1 (incA D (c p.2.2))
  let φ : (Fin n × Fin m × Fin d) → Af D.host.F → Mx D m n := fun p t => (pairA D.host.F 0 t) • M p
  have hpair : Continuous fun t : Af D.host.F => pairA D.host.F 0 t := continuous_const.prodMk continuous_id
  have hφ : ∀ p, Continuous (φ p) := fun p =>
    Continuous.smul (f := fun t : Af D.host.F => pairA D.host.F 0 t) (g := fun _ => M p) hpair continuous_const
  have hφ0 : ∀ p, φ p 0 = 0 := fun p => by
    have : pairA D.host.F 0 (0 : Af D.host.F) = 0 := rfl
    simp only [φ, this, zero_smul]
  have hO : (⋂ p, φ p ⁻¹' V) ∈ nhds (0 : Af D.host.F) :=
    Filter.iInter_mem.2 fun p => (hφ p).continuousAt.preimage_mem_nhds (by rw [hφ0]; exact hV)
  obtain ⟨K₀, hK₀, hmem⟩ := GlobalTheory.ScalarAnnih.exists_compact_of_annih D ψ hψ _ hO
  let g : (Fin n × Fin m × Fin d → Af D.host.F) → Mx D n m :=
    fun z => Matrix.of fun i j => ∑ l, pairA D.host.F 0 (z (i, j, l)) ⊗ₜ[D.host.F] e l
  have hg : Continuous g := by
    refine continuous_matrix fun i j => ?_
    show Continuous fun z : Fin n × Fin m × Fin d → Af D.host.F => ∑ l, pairA D.host.F 0 (z (i, j, l)) ⊗ₜ[D.host.F] e l
    refine continuous_finset_sum _ fun l _ => ?_
    have : (fun z : Fin n × Fin m × Fin d → Af D.host.F => (pairA D.host.F 0 (z (i, j, l)) ⊗ₜ[D.host.F] e l : AE D)) =
        fun z => pairA D.host.F 0 (z (i, j, l)) • ((1 : AF D.host.F) ⊗ₜ[D.host.F] e l : AE D) := by
      funext z; rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    rw [this]
    exact (hpair.comp (continuous_apply (A := fun _ : Fin n × Fin m × Fin d => Af D.host.F) (i, j, l))).smul
      (continuous_const (y := ((1 : AF D.host.F) ⊗ₜ[D.host.F] e l : AE D)))
  refine ⟨g '' Set.pi Set.univ (fun _ => K₀), (isCompact_univ_pi fun _ => hK₀).image hg, fun y hy => ?_⟩
  let z : Fin n × Fin m × Fin d → Af D.host.F :=
    fun p => sndA D.host.F (Algebra.trace (AF D.host.F) (AE D) (incA D (c p.2.2) * y p.1 p.2.1))
  refine ⟨g z, ⟨z, fun p _ => hmem _ fun t ht => ?_, rfl⟩, ?_⟩
  · have hu : (pairA D.host.F 0 t • Matrix.single p.2.1 p.1 (incA D (c p.2.2)) : Mx D m n) ∈ V :=
      Set.mem_iInter.1 ht p
    have hinf : (pairA D.host.F 0 t • Matrix.single p.2.1 p.1 (incA D (c p.2.2)) : Mx D m n).map (infPart D) = 0 := by
      ext k l
      simp only [Matrix.map_apply, Matrix.smul_apply, Matrix.zero_apply, Matrix.single_apply]
      split_ifs
      · change infPart D (pairA D.host.F 0 t • ((1 : AF D.host.F) ⊗ₜ[D.host.F] c p.2.2)) = 0
        rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
        change (fstA D.host.F (pairA D.host.F 0 t)) ⊗ₜ[D.host.F] (c p.2.2) = 0
        exact TensorProduct.zero_tmul _ _
      · rw [smul_zero, map_zero]
    have h1 := hy _ hu hinf
    have e2 := trace_mul_smul_single D y (pairA D.host.F 0 t) p.1 p.2.1 (c p.2.2)
    have e1 : pairA D.host.F 0 (t * z p) = pairA D.host.F 0 t *
        Algebra.trace (AF D.host.F) (AE D) (incA D (c p.2.2) * y p.1 p.2.1) :=
      Prod.ext (zero_mul _).symm rfl
    exact (congrArg ψ (e1.trans e2.symm)).trans h1
  · refine Matrix.ext fun i j => ?_
    rw [Matrix.map_apply, Matrix.sub_apply, Matrix.zero_apply, (finPart D).map_sub, sub_eq_zero, hce]
    exact (finPart_sum_tmul D (fun l => z (i, j, l)) e).symm

end GlobalTheory.MatAnnih
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ConjWeilDatumViaAdjointExchangedPair
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

namespace GlobalTheory.ConjAdjWeil

open GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger GlobalTheory.PairLift

variable {D : D7}

theorem dagger_eq (S T : HSp D) (x : WO S T) : dagger S T x = adjO T S x := by
  simp only [dagger, adjO, giA, gA, adj, Matrix.mul_assoc]
  rfl

theorem cj_dagger (S T : HSp D) (f : WO S T → ℂ) : cj (dagger T S) f = dag S T f := by
  funext y; simp only [GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj, dag, dagger_eq]

theorem conjAdjoint_apply {S T : HSp D} (om : Rep S T) (g : GA D T) (h : GA D S) (f : WO T S → ℂ) :
    conjAdjoint om (g, h) f = dag S T (om (h, g) (dag T S f)) := by
  show cj (dagger T S) (om (h, g) (cj (dagger S T) f)) = _
  rw [cj_dagger, cj_dagger]

theorem chi_conj {χ : (AE D)ˣ →* Circle} {n : ℕ} (hR : ResEta D χ n) (y : (AE D)ˣ) :
    χ (Units.map (cA D).toMonoidHom y) = (χ y)⁻¹ := by
  obtain ⟨⟨η, hη⟩, hall⟩ := hR
  have hprod : y * Units.map (cA D).toMonoidHom y =
      idF D (Units.map (Algebra.norm (AF D.host.F) : AE D →* AF D.host.F) y) := by
    apply Units.ext
    rw [GlobalTheory.Mem.EtaTilde.idF_norm]
    rfl
  have h1 : χ y * χ (Units.map (cA D).toMonoidHom y) = 1 := by
    rw [← map_mul, hprod, hall η hη, hη.2.2.1, one_pow]
  exact eq_inv_of_mul_eq_one_right h1

theorem isSplitIdem_conj {e : AE D} (h : IsSplitIdem D e) : IsSplitIdem D (cA D e) := by
  obtain ⟨h1, h2, v, ε, hε, h3⟩ := h
  exact ⟨by rw [← map_mul, h1], by rw [cA_cA, mul_comm, h2], v, ε, hε, by rw [cA_cA, add_comm, h3]⟩

theorem suppAt_conj {e : AE D} {V : HSp D} {g : GA D V} (h : SuppAt e V g) : SuppAt (cA D e) V g := by
  intro i j
  rw [cA_cA, add_comm]
  exact h i j

theorem det_inv_eq (V : HSp D) (g : GA D V) : (mt V g⁻¹).det = cA D (mt V g).det := by
  have h1 : (giA V).det * (gA V).det = 1 := by rw [← Matrix.det_mul, giA_mul_gA, Matrix.det_one]
  rw [mt_inv, Matrix.det_mul, Matrix.det_mul, adj, Matrix.det_transpose, RingHom.map_det, RingHom.mapMatrix_apply]
  linear_combination ((mt V g).map (cA D)).det * h1

theorem isDetAt_conj {e : AE D} (he : e * e = e) {V : HSp D} {g : GA D V} {x : (AE D)ˣ} (hx : IsDetAt e V g x) :
    IsDetAt (cA D e) V g (Units.map (cA D).toMonoidHom x⁻¹) := by
  have hd : (mt V g⁻¹).det * (mt V g).det = 1 := by rw [← Matrix.det_mul, mt_inv_mul, Matrix.det_one]
  have hz : ((x⁻¹ : (AE D)ˣ) : AE D) = e * (mt V g⁻¹).det + (1 - e) := by
    apply Units.inv_eq_of_mul_eq_one_left
    rw [hx]
    linear_combination e * hd + ((mt V g⁻¹).det * (mt V g).det - (mt V g⁻¹).det - (mt V g).det + 1) * he
  show cA D ((x⁻¹ : (AE D)ˣ) : AE D) = cA D e * (mt V g).det + (1 - cA D e)
  rw [hz, map_add, map_mul, map_sub, map_one, det_inv_eq, cA_cA]

end GlobalTheory.ConjAdjWeil

namespace GlobalTheory.ConjAdjWeil

open GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger GlobalTheory.PairLift

theorem isWeilDatumO_conjAdjoint : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle)
    (om : Om S T), IsWeilDatumO ψ S T χS χT om → IsWeilDatumO ψ T S χT χS (GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.conjAdjoint om) := by
  intro D ψ S T χS χT om hw
  have hS : AdjLaw ψ S T := GlobalTheory.AdjLawPf.adjLaw D ψ hw.std S T
  have hT : AdjLaw ψ T S := GlobalTheory.AdjLawPf.adjLaw D ψ hw.std T S
  have thB : ∀ f : WO T S → ℂ, IsThetaFunO ψ T S f → IsThetaFunO ψ S T (dag T S f) := hT.theta
  have thA : ∀ f : WO S T → ℂ, IsThetaFunO ψ S T f → IsThetaFunO ψ T S (dag S T f) := hS.theta
  have key : ∀ (g : GA D T) (h : GA D S) (f : WO T S → ℂ),
      conjAdjoint om (g, h) f = dag S T (om (h, g) (dag T S f)) := fun g h f => conjAdjoint_apply om g h f
  have dd : ∀ f : WO T S → ℂ, dag S T (dag T S f) = f := fun f => by
    funext y; simp only [dag, hT.invol, Complex.conj_conj]
  have d0 : adjO S T 0 = 0 := by
    have := hS.add 0 0
    rw [add_zero] at this
    exact (add_eq_left.1 this.symm)
  have d0' : adjO T S 0 = 0 := by
    have := hT.add 0 0
    rw [add_zero] at this
    exact (add_eq_left.1 this.symm)
  refine ⟨hw.std, hw.hecT, hw.hecS, hw.resT, hw.resS, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rintro ⟨g, h⟩ f hf
    rw [key]
    exact thA _ (hw.om_pres _ _ (thB f hf))
  · intro g h w₀ f hf
    have e1 : dag T S (heisO ψ T S w₀ f) = heisO ψ S T (adjO S T w₀) (dag T S f) := by
      rw [hT.Heisenberg₂, hT.invol]
    rw [key, key, e1, hw.om_heis _ _ _ _ (thB f hf), ← hS.act, ← hS.Heisenberg₂]
  · intro γ hγ γ' hγ' f hf
    rw [key]
    have := hw.om_aut γ' hγ' γ hγ (dag T S f) (thB f hf)
    simp only [dag] at this ⊢
    rw [d0, this, d0', Complex.conj_conj]
  · intro f hf w
    have e : (fun p : GA D T × GA D S => conjAdjoint om p f w) =
        fun p => starRingEnd ℂ (om (Prod.swap p) (dag T S f) (adjO S T w)) := by
      funext p
      obtain ⟨g, h⟩ := p
      rw [key]
      rfl
    rw [e]
    exact Complex.continuous_conj.comp ((hw.om_cont _ (thB f hf) _).comp continuous_swap)
  · intro μ 𝓕 hμ h𝓕 p f hf
    obtain ⟨g, h⟩ := p
    haveI : BorelSpace (WO S T) := ⟨rfl⟩
    haveI : BorelSpace (WO T S) := ⟨rfl⟩
    let dE : WO T S ≃+ WO S T :=
      { toFun := adjO S T, invFun := adjO T S, left_inv := hT.invol, right_inv := hS.invol, map_add' := hS.add }
    let hE : WO S T ≃ₜ WO T S :=
      { toFun := adjO T S, invFun := adjO S T, left_inv := hS.invol, right_inv := hT.invol,
        continuous_toFun := hT.cont, continuous_invFun := hS.cont }
    set ν : Measure (WO S T) := μ.map dE with hν
    have hνH : ν.IsAddHaarMeasure := dE.isAddHaarMeasure_map μ hS.cont hT.cont
    have hfm : Measurable (adjO T S) := hT.cont.measurable
    have hdm : Measurable (adjO S T) := hS.cont.measurable
    have hmp : MeasurePreserving (adjO T S) ν μ := by
      refine ⟨hfm, ?_⟩
      rw [hν, Measure.map_map hfm (show Measurable dE from hdm)]
      have : adjO T S ∘ dE = id := funext fun w => hT.invol w
      rw [this, Measure.map_id]
    have hemb : MeasurableEmbedding (adjO T S) := hE.measurableEmbedding
    have hfd : IsAddFundamentalDomain (ratL T S) (adjO T S ⁻¹' 𝓕) ν := by
      refine h𝓕.preimage_of_equiv hmp.quasiMeasurePreserving
        (e := fun γ : ratL S T => (⟨adjO S T γ, (hS.rat γ).2 γ.2⟩ : ratL T S)) ⟨?_, ?_⟩ ?_
      · intro a b hab
        have := congrArg (fun z : ratL T S => adjO T S (z : WO S T)) hab
        simp only [hT.invol] at this
        exact Subtype.ext this
      · intro b
        refine ⟨⟨adjO T S b, (hT.rat b).2 b.2⟩, Subtype.ext ?_⟩
        exact hS.invol b
      · intro γ x
        show adjO T S (adjO S T (γ : WO T S) + x) = (γ : WO T S) + adjO T S x
        rw [hT.add, hT.invol]
    calc ∫⁻ w in 𝓕, ‖conjAdjoint om (g, h) f w‖ₑ ^ 2 ∂μ
        = ∫⁻ w in 𝓕, (fun z => ‖om (h, g) (dag T S f) z‖ₑ ^ 2) (adjO S T w) ∂μ := by
          congr 1
          funext w
          rw [key]
          simp [dag]
      _ = ∫⁻ z in adjO T S ⁻¹' 𝓕, (fun z => ‖om (h, g) (dag T S f) z‖ₑ ^ 2) (adjO S T (adjO T S z)) ∂ν :=
          (hmp.setLIntegral_comp_preimage_emb hemb (fun w => (fun z => ‖om (h, g) (dag T S f) z‖ₑ ^ 2) (adjO S T w)) 𝓕).symm
      _ = ∫⁻ z in adjO T S ⁻¹' 𝓕, ‖om (h, g) (dag T S f) z‖ₑ ^ 2 ∂ν := by simp only [hS.invol]
      _ = ∫⁻ z in adjO T S ⁻¹' 𝓕, ‖dag T S f z‖ₑ ^ 2 ∂ν := hw.om_unit ν _ hνH hfd (h, g) _ (thB f hf)
      _ = ∫⁻ z in adjO T S ⁻¹' 𝓕, (fun w => ‖f w‖ₑ ^ 2) (adjO T S z) ∂ν := by
          congr 1
          funext z
          simp [dag]
      _ = ∫⁻ w in 𝓕, ‖f w‖ₑ ^ 2 ∂μ := hmp.setLIntegral_comp_preimage_emb hemb (fun w => ‖f w‖ₑ ^ 2) 𝓕
  · intro e he g h hsg hsh x y hx hy
    obtain ⟨r, hr, hℓ⟩ := hw.om_split (cA D e) (isSplitIdem_conj he) h g (suppAt_conj hsh) (suppAt_conj hsg) _ _
      (isDetAt_conj he.1 hy) (isDetAt_conj he.1 hx)
    refine ⟨r, hr, fun ℓ hinv f hf => ?_⟩
    have dadd : ∀ a b : WO S T → ℂ, dag S T (a + b) = dag S T a + dag S T b := fun a b => by
      funext z; simp [dag]
    have dsmul : ∀ (c : ℂ) (a : WO S T → ℂ), dag S T (c • a) = starRingEnd ℂ c • dag S T a := fun c a => by
      funext z; simp [dag]
    let ℓ' : (WO S T → ℂ) →ₗ[ℂ] ℂ :=
      { toFun := fun F => starRingEnd ℂ (ℓ (dag S T F))
        map_add' := fun a b => by simp only [dadd, map_add]
        map_smul' := fun c a => by
          simp only [dsmul, map_smul, smul_eq_mul, map_mul, RingHom.id_apply, Complex.conj_conj] }
    have hinv' : ∀ u : WO S T, (∀ i j, cA D (cA D e) * u i j = u i j) → ∀ F, IsThetaFunO ψ S T F →
        ℓ' (heisO ψ S T u F) = ℓ' F := by
      intro u hu F hF
      have hu' : IsHalf e u := fun i j => by have := hu i j; rwa [cA_cA] at this
      have e2 : dag S T (heisO ψ S T u F) = heisO ψ T S (adjO T S u) (dag S T F) := by rw [hS.Heisenberg₂, hS.invol]
      show starRingEnd ℂ (ℓ (dag S T (heisO ψ S T u F))) = starRingEnd ℂ (ℓ (dag S T F))
      rw [e2, hinv _ (hT.half e u hu') _ (thA F hF)]
    have main := hℓ ℓ' hinv' (dag T S f) (thB f hf)
    have m2 : starRingEnd ℂ (ℓ (dag S T (om (h, g) (dag T S f)))) =
        (r : ℂ) * (splitFacO χS χT (Units.map (cA D).toMonoidHom y⁻¹) (Units.map (cA D).toMonoidHom x⁻¹) : ℂ) *
          starRingEnd ℂ (ℓ f) := by
      have := main
      simp only [ℓ', LinearMap.coe_mk, AddHom.coe_mk, dd] at this
      exact this
    have hconj := congrArg (starRingEnd ℂ) m2
    rw [Complex.conj_conj] at hconj
    have hfac : (splitFacO χS χT (Units.map (cA D).toMonoidHom y⁻¹) (Units.map (cA D).toMonoidHom x⁻¹))⁻¹ =
        splitFacO χT χS x y := by
      unfold splitFacO
      rw [chi_conj hw.resT, chi_conj hw.resS, map_inv, map_inv, inv_inv, inv_inv, _root_.mul_inv_rev, inv_inv]
    rw [key, hconj, map_mul, map_mul, Complex.conj_conj, Complex.conj_ofReal, ← Circle.coe_inv_eq_conj, hfac]

end GlobalTheory.ConjAdjWeil
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ContDiffHeisenbergTranslateThetaFunctionRealCoor
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct ContDiff
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.ThetaTranslate

open GlobalTheory.FockCompare GlobalTheory.OrientedHeis

theorem hasDerivAt_expLine {H : ℝ → ℂ} {h' : ℂ} (hH : HasDerivAt H h' 0) (a k : ℝ) :
    HasDerivAt (fun s : ℝ => Complex.exp (-(Real.pi * Complex.I) * ((a + s * k : ℝ) : ℂ)) * H s)
      (Complex.exp (-(Real.pi * Complex.I) * (a : ℂ)) * (-(Real.pi * Complex.I) * (k : ℂ) * H 0 + h')) 0 := by
  have h1 : HasDerivAt (fun s : ℝ => a + s * k) k 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).mul_const k).const_add a
  have h2 : HasDerivAt (fun s : ℝ => ((a + s * k : ℝ) : ℂ)) (k : ℂ) 0 := h1.ofReal_comp
  have h3 := ((h2.const_mul (-(Real.pi * Complex.I))).cexp).mul hH
  exact h3.congr_deriv (by simp only [zero_mul, add_zero]; ring)

theorem contDiff_heisO_iota_fderiv : ∀ (D : D7) (θ : InfFam D) (σ : (D.what₂.Tau → ℂ) →+ AE D), GlobalTheory.FockCompare.Chart θ σ → ∀ (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S T : HSp D) (F : WO S T → ℂ), IsThetaFunO ψ S T F → ∀ v : WO S T, ContDiff ℝ ∞ (fun z : GlobalTheory.FockCompare.RW T S => heisO ψ S T (GlobalTheory.FockCompare.iotaW σ T S z) F v) ∧ ∀ z u : GlobalTheory.FockCompare.RW T S, fderiv ℝ (fun z : GlobalTheory.FockCompare.RW T S => heisO ψ S T (GlobalTheory.FockCompare.iotaW σ T S z) F v) z u = (Real.pi * Complex.I) * ((GlobalTheory.OrientedHeis.omO S T z u : ℝ) : ℂ) * heisO ψ S T (GlobalTheory.FockCompare.iotaW σ T S z) F v + heisO ψ S T (GlobalTheory.FockCompare.iotaW σ T S z) (fun y => deriv (fun s : ℝ => heisO ψ S T (GlobalTheory.FockCompare.iotaW σ T S (s • u)) F y) 0) v := by
  intro D θ σ h ψ hψ S T F hF v
  have hG : ContDiff ℝ ∞ fun x : RW T S => F (v + iotaW σ T S x) := theta_sm h hF v
  have eg : (fun z : RW T S => heisO ψ S T (iotaW σ T S z) F v) = fun z =>
      Complex.exp (-(Real.pi * Complex.I) * (Complex.ofRealCLM (omO S T (piW θ T S v) z))) *
        F (v + iotaW σ T S z) := by
    funext z; rw [heisO_iota h hψ]; rfl
  have hsm : ContDiff ℝ ∞ (fun z : RW T S => heisO ψ S T (iotaW σ T S z) F v) := by
    rw [eg]
    exact (Complex.contDiff_exp.comp (contDiff_const.mul (Complex.ofRealCLM.contDiff.comp
      (LinearMap.toContinuousLinearMap (omO S T (piW θ T S v))).contDiff))).mul hG
  refine ⟨hsm, fun z u => ?_⟩
  have hHc : ContDiff ℝ ∞ fun x : RW T S => F ((v + iotaW σ T S z) + iotaW σ T S x) := theta_sm h hF _
  have hH : HasDerivAt (fun s : ℝ => F ((v + iotaW σ T S z) + iotaW σ T S (s • u)))
      (deriv (fun s : ℝ => F ((v + iotaW σ T S z) + iotaW σ T S (s • u))) 0) 0 :=
    ((hHc.comp (contDiff_id.smul contDiff_const)).differentiable (by simp) 0).hasDerivAt
  have hline : HasDerivAt (fun s : ℝ => heisO ψ S T (iotaW σ T S (z + s • u)) F v)
      (Complex.exp (-(Real.pi * Complex.I) * ((omO S T (piW θ T S v) z : ℝ) : ℂ)) *
        (-(Real.pi * Complex.I) * ((omO S T (piW θ T S v) u : ℝ) : ℂ) *
          F ((v + iotaW σ T S z) + iotaW σ T S ((0 : ℝ) • u)) +
          deriv (fun s : ℝ => F ((v + iotaW σ T S z) + iotaW σ T S (s • u))) 0)) 0 := by
    have eline : (fun s : ℝ => heisO ψ S T (iotaW σ T S (z + s • u)) F v) = fun s =>
        Complex.exp (-(Real.pi * Complex.I) * ((omO S T (piW θ T S v) z + s * omO S T (piW θ T S v) u : ℝ) : ℂ)) *
          F ((v + iotaW σ T S z) + iotaW σ T S (s • u)) := by
      funext s
      rw [heisO_iota h hψ, (omO S T (piW θ T S v)).map_add, LinearMap.map_smul, smul_eq_mul, (iotaW σ T S).map_add,
        add_assoc]
    rw [eline]
    exact hasDerivAt_expLine hH _ _
  have hf : HasDerivAt (fun s : ℝ => heisO ψ S T (iotaW σ T S (z + s • u)) F v)
      (fderiv ℝ (fun z : RW T S => heisO ψ S T (iotaW σ T S z) F v) z u) 0 := by
    have hd : HasFDerivAt (fun z : RW T S => heisO ψ S T (iotaW σ T S z) F v)
        (fderiv ℝ (fun z : RW T S => heisO ψ S T (iotaW σ T S z) F v) z) (z + (0 : ℝ) • u) := by
      rw [zero_smul, add_zero]; exact (hsm.differentiable (by simp) z).hasFDerivAt
    have hl : HasDerivAt (fun s : ℝ => z + s • u) u 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).smul_const u).const_add z
    exact hd.comp_hasDerivAt (0 : ℝ) hl
  have hF' : HasDerivAt (fun s : ℝ => heisO ψ S T (iotaW σ T S (s • u)) F (v + iotaW σ T S z))
      (Complex.exp (-(Real.pi * Complex.I) * ((0 : ℝ) : ℂ)) *
        (-(Real.pi * Complex.I) * ((omO S T (piW θ T S v) u + omO S T z u : ℝ) : ℂ) *
          F ((v + iotaW σ T S z) + iotaW σ T S ((0 : ℝ) • u)) +
          deriv (fun s : ℝ => F ((v + iotaW σ T S z) + iotaW σ T S (s • u))) 0)) 0 := by
    have eF : (fun s : ℝ => heisO ψ S T (iotaW σ T S (s • u)) F (v + iotaW σ T S z)) = fun s =>
        Complex.exp (-(Real.pi * Complex.I) *
          ((0 + s * (omO S T (piW θ T S v) u + omO S T z u) : ℝ) : ℂ)) *
          F ((v + iotaW σ T S z) + iotaW σ T S (s • u)) := by
      funext s
      rw [heisO_iota h hψ, (piW θ T S).map_add, h.pi_iota, LinearMap.map_smul, smul_eq_mul, (omO S T).map_add,
        LinearMap.add_apply, zero_add]
    rw [eF]
    exact hasDerivAt_expLine hH _ _
  rw [hf.unique hline, heisO_iota h hψ z F v, heisO_iota h hψ z _ v]
  beta_reduce
  rw [hF'.deriv]
  simp only [zero_smul, map_zero, add_zero, Complex.ofReal_zero, mul_zero, Complex.exp_zero, one_mul,
    Complex.ofReal_add]
  ring

end GlobalTheory.ThetaTranslate

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsFlagStabiliserMoveLatticeSplitWitt
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel GlobalTheory.IwaPlace Matrix

noncomputable section

namespace GlobalTheory.IwaPlace

theorem iwasawa_flag_move : ∀ (D : D7) (S S₀ : HSp D) (ρ : ℕ) (d : HypDec S S₀ ρ) (L : Lat S) (L₀ : Lat S₀) (v : Pl D), Tame D v → IsSDAt S v (latV S L (· = v)) → MonoAt d L L₀ v → ∀ h ∈ grpAt S (· = v), ∃ q ∈ grpAt S (· = v), (∃ a : Mx D ρ ρ, (∀ i j, j < i → a i j = 0) ∧ mt S q ⬝ d.jX = d.jX ⬝ a) ∧ ∃ Λ₀ : AddSubgroup (Fin S₀.rank → AE D), IsSDAt S₀ v Λ₀ ∧ ∀ z : Fin S.rank → AE D, (∀ i, z i ∈ idAt D (· = v)) → (mt S (h⁻¹ * q) *ᵥ z ∈ latV S L (· = v) ↔ (∀ i, colMul d.jX i ((d.pX *ᵥ z) i) ∈ latV S L (· = v)) ∧ (∀ i, colMul d.jY i ((d.pY *ᵥ z) i) ∈ latV S L (· = v)) ∧ d.p0 *ᵥ z ∈ Λ₀) := by
  intro D S S₀ ρ d L L₀ v hT hL hM h hh
  obtain ⟨⟨ε, hεε, hεc, hεI, hε, -⟩, -⟩ := GlobalTheory.T.adelicPoint_components_atPlaces_lattices_vacua D (· = v)
  have hMsd := GlobalTheory.T.isSelfDualLatticeAtPlace_comap_unitarySupported D S v h⁻¹ (inv_mem hh) _ hL
  set M := (latV S L (· = v)).comap (Matrix.mulVecLin (mt S h⁻¹)).toAddMonoidHom with hMdef
  obtain ⟨b, hbu, hbI, hbM, c', hc'M, hpair⟩ := GlobalTheory.T.exists_flag_dual_basis_selfDualLatticeAtPlace D S S₀ ρ d v ε hεε hεc hεI hε hT M hMsd
  obtain ⟨w, hw, hw1⟩ := GlobalTheory.T.exists_integral_trace_idempotent_at_tamePlace D v ε hεε hεc hεI hε hT
  obtain ⟨c'', hc''M, hpair', hiso⟩ := GlobalTheory.T.exists_isotropic_dual_columns_selfDualLatticeAtPlace D S S₀ ρ d v ε hεε hεc hεI hε M hMsd w hw hw1 b c' hbI hbM hc'M hpair
  obtain ⟨α, β, hα, hβ, hαβ, hX, hY⟩ := GlobalTheory.T.selfDualLattice_hyperbolic_line_ideals_at_place D S S₀ ρ d L L₀ v ε hεε hεc hεI hε hL hM
  have hc''I : ∀ i j, c'' i j ∈ idAt D (· = v) := fun i j => hMsd.1 _ (hc''M j) i
  obtain ⟨q, hq, hqX, hqα, hqβ⟩ := GlobalTheory.T.exists_unitarySupportedAtPlace_of_dual_isotropic_frames D S S₀ ρ d v ε hεε hεc hεI hε α β b c'' hα hβ hαβ hbI hc''I hpair' hiso
  have hNsd := GlobalTheory.T.isSelfDualLatticeAtPlace_comap_unitarySupported D S v q hq M hMsd
  obtain ⟨Λ₀, hΛ, hz⟩ := GlobalTheory.T.selfDualLatticeAtPlace_splits_hyperbolic_plus_core D S S₀ ρ d v ε hεε hεc hεI hε _ α β hNsd hα hβ hαβ
    (fun i => by
      rw [AddSubgroup.mem_comap]
      change mt S q *ᵥ colMul d.jX i (α i) ∈ M
      rw [hqα]; exact hbM i)
    (fun i => by
      rw [AddSubgroup.mem_comap]
      change mt S q *ᵥ colMul d.jY i (cA D (β i)) ∈ M
      rw [hqβ]; exact hc''M i)
  refine ⟨q, hq, ⟨b ⬝ Matrix.diagonal β + (1 - ε) • (1 : Mx D ρ ρ), fun i j hji => ?_, hqX⟩, Λ₀, hΛ, fun z hz' => ?_⟩
  · rw [Matrix.add_apply, Matrix.mul_diagonal, hbu i j hji, Matrix.smul_apply, Matrix.one_apply_ne (ne_of_gt hji)]
    simp
  · have e1 : (mt S (h⁻¹ * q) *ᵥ z ∈ latV S L (· = v)) ↔
        z ∈ (M.comap (Matrix.mulVecLin (mt S q)).toAddMonoidHom) := by
      rw [AddSubgroup.mem_comap, hMdef, AddSubgroup.mem_comap]
      change _ ↔ mt S h⁻¹ *ᵥ (mt S q *ᵥ z) ∈ _
      rw [Matrix.mulVec_mulVec, ← mt_mul]
    rw [e1, hz z hz']
    refine and_congr (forall_congr' fun i => (hX i _ (mulVec_mem_idAt _ hz' i)).symm)
      (and_congr (forall_congr' fun i => (hY i _ (mulVec_mem_idAt _ hz' i)).symm) Iff.rfl)

end GlobalTheory.IwaPlace

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsNormOfConjFixedUnitTamePlaceStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel GlobalTheory.IwaPlace Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_norm_of_conjFixed_unit_tamePlace : ∀ (D : D7) (v : Pl D) (ε : AE D), Tame D v → ε * ε = ε → cA D ε = ε → ε ∈ intAt D (· = v) → (∀ a, a ∈ idAt D (· = v) ↔ ε * a = a) → ∀ u ∈ intAt D (· = v), cA D u = u → (∃ y ∈ intAt D (· = v), u * y = ε) → ∃ x ∈ intAt D (· = v), x * cA D x = u := by
  first | exact @GlobalTheory.FixedUnitNorm.fixed_unit_norm | exact GlobalTheory.FixedUnitNorm.fixed_unit_norm | (intros; apply GlobalTheory.FixedUnitNorm.fixed_unit_norm <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsRationalWittFlagCoordinatesOfMemUnipotentStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_rational_wittFlagCoordinates_of_mem_unipotent : ∀ (D : D7) (V V₀ : HSp D) (ρ : ℕ) (d : HypDec V V₀ ρ) (γ : GA D V), γ ∈ GQ V → γ ∈ flagN d → ∃ (c : skewA D ρ) (b : Mx D ρ V₀.rank) (u : UX D ρ), γ = d.nC c * (d.nB b * d.levi u.1) ∧ c.1 ∈ ratMx D ρ ρ ∧ b ∈ ratMx D ρ V₀.rank ∧ u ∈ UXQ D ρ := by
  first | exact @GlobalTheory.RatCoord.rat_coords_of_mem_flagN | exact GlobalTheory.RatCoord.rat_coords_of_mem_flagN | (intros; apply GlobalTheory.RatCoord.rat_coords_of_mem_flagN <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsSplitPointFrameCharacterStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl ValuativeRel NumberField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_splitPoint_frame_character : ∀ (D : D7), (∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [IsTopologicalRing k] [CharZero k] (T : ℕ), T.Prime → Nat.card (IsLocalRing.ResidueField 𝒪[k]) = T → Irreducible (T : 𝒪[k]) → ∀ (w : Formalism.L2.DIV.Pl D.host.E) (e : AE D), Formalism.L2.NTheta.IsIdemAt e w → IsSplitIdem D e → Ideal.absNorm w.asIdeal = T → ¬ (w.asIdeal ^ 2 ∣ Ideal.span {(T : 𝓞 D.host.E)}) → ∃ p : SplitPt D k, p.e = e) ∧ ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : SplitPt D k), (∀ (S : HSp D) (n : Type) [Fintype n] [DecidableEq n] (b : Matrix (Fin S.rank) n k) (b' : Matrix n (Fin S.rank) k), b * b' = 1 → b' * b = 1 → ∃ β : Frame p S n, β.b = b) ∧ ∀ ψ : AddChar (AF D.host.F) ℂ, IsStdChar D ψ (-1) → ∃ χ : AddChar k Circle, p.IsChar ψ χ ∧ Continuous χ ∧ χ ≠ 1 ∧ (p.UnitAA → GlobalTheory.SplitWeil.HasConductor χ 1) := by
  first | exact @GlobalTheory.InhPt.exists_splitPt_frame_char | exact GlobalTheory.InhPt.exists_splitPt_frame_char | (intros; apply GlobalTheory.InhPt.exists_splitPt_frame_char <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsTwistIndexRepresentativeOfBoundsStatement
section
open NumberField IsDedekindDomain MeasureTheory ValuativeRel Matrix Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.TwBridge
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_twistIndex_representative_of_bounds : ∀ (X : Fields) (Pr : Primes X) (R : Ranks) (Ch : Chars X Pr R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (S₀ : Set ℕ) (mu : Tup X.F X.E X.K S₀) (cst : LocCst X (rowSG Pr sel mu)) (σ₀ : X.K →+* ℂ) (P : rowSG Pr sel mu) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : X.E →+* k) (s : ℕ) (W : TwData k) [MeasurableSpace k] [BorelSpace k] (ν : Measure k), IsUnitVol ν → cst.Ok → AtTwist (R := R) sel mu cst σ₀ P ι s W → ∀ (L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K))) (G : ChGlob X R.m), L.Ok Ch sel mu cst G s → IdxProd sel mu cst L → ∀ j c (h : j + 1 + c = s) (γ : AutY X R (j + 1)), (∀ x ∈ lamYat (Pr := Pr) (R := R) (j + 1) P.1, γ⁻¹ x ∈ lamYat (Pr := Pr) (R := R) (j + 1) P.1 ∧ ((qOf P.1 : X.E) ^ (j + 1)) • γ x ∈ lamYat (Pr := Pr) (R := R) (j + 1) P.1) → (∃ al : L.β j, FiniteSumNonzeroLargeDepth Ch sel mu cst j P (L.h j al P) γ) → Nonempty (L.β (j + 1)) → ∃ b : L.β (j + 1), SameDC (Pr := Pr) cst.sharp (j + 1) P.1 (L.h (j + 1) b P) γ := by
  first | exact @GlobalTheory.MRepsPick.exists_rep_of_bounds | exact GlobalTheory.MRepsPick.exists_rep_of_bounds | (intros; apply GlobalTheory.MRepsPick.exists_rep_of_bounds <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsUnimodularBasisSelfDualLatticeAtPlace
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel GlobalTheory.IwaPlace Matrix

namespace GlobalTheory.IwaPlace.SDBasis

theorem exists_basis_unimodular : ∀ (D : D7) (S : HSp D) (v : Pl D) (ε : AE D) (Λ : AddSubgroup (Fin S.rank → AE D)), Tame D v → ε * ε = ε → cA D ε = ε → ε ∈ intAt D (· = v) → (∀ a, a ∈ idAt D (· = v) ↔ ε * a = a) → IsSDAt S v Λ → ∃ β β' : Matrix (Fin S.rank) (Fin S.rank) (AE D), (∀ i j, β i j ∈ idAt D (· = v)) ∧ (∀ i j, β' i j ∈ idAt D (· = v)) ∧ β * β' = ε • (1 : Matrix (Fin S.rank) (Fin S.rank) (AE D)) ∧ β' * β = ε • (1 : Matrix (Fin S.rank) (Fin S.rank) (AE D)) ∧ (∀ y : Fin S.rank → AE D, (∀ i, y i ∈ idAt D (· = v)) → (y ∈ Λ ↔ ∀ i, (β' *ᵥ y) i ∈ intAt D (· = v))) ∧ (∀ i j, (adj β * (gA S * β)) i j ∈ intAt D (· = v)) ∧ (∀ i j, cA D ((adj β * (gA S * β)) i j) = (adj β * (gA S * β)) j i) ∧ ∃ H' : Matrix (Fin S.rank) (Fin S.rank) (AE D), (∀ i j, H' i j ∈ intAt D (· = v)) ∧ adj β * (gA S * β) * H' = ε • (1 : Matrix (Fin S.rank) (Fin S.rank) (AE D)) := by
  intro D S v ε Λ hT hεε hcε hεO hε hΛ
  obtain ⟨β, β', hβ, hβ', h1, h2, h3⟩ :=
    GlobalTheory.T.exists_integralBasis_of_latticeAtPlace_stable D S.rank v ε Λ hT hεε hcε hεO hε hΛ.1 (GlobalTheory.T.selfDualLatticeAtPlace_smul_integral_mem D S v Λ hΛ) hΛ.2.1 (GlobalTheory.T.exists_nat_mul_selfDualLatticeAtPlace_integral D S v Λ hΛ)
  exact ⟨β, β', hβ, hβ', h1, h2, h3, GlobalTheory.T.selfDualLatticeAtPlace_basis_gram_integral_invertible D S v ε Λ β β' hεε hcε hεO hε hΛ hβ hβ' h1 h2 h3⟩

end GlobalTheory.IwaPlace.SDBasis
end

