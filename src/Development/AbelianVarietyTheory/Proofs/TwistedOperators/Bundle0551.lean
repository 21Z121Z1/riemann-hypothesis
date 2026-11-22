import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0546
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.MemLatOIffExistsActO
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0082
import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.IdemSplit
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0513
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0019
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.Bundle0007
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0217
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaGrowthOfThetaSquareIntegrable
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0008
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CuspAlongOfPairLifts
import Development.AbelianVarietyTheory.Proofs.HeightProofs.TypeAtOfDiscreteSeries
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0010
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.SqNormIntegralFundamentalDomainEqL2NormSq
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContDiffDerivSnoc
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0523
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0404
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0027
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0214
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0005
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0304
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NormDwLeSobNorm
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0542
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0343
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0235
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0215
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0354
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0533
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0006
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0004
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0393
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.TwistPlacesOffPrimeQZero
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0004
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0006
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ToricSymbols
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0296
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0528
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0534
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ContinuousReprSymm
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0126
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0205
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0241
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0499
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0525
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0428

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ActOMemLatOOfHat
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.LastVertexInv GlobalTheory.LastVertexMove

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

namespace GlobalTheory.StdHalfLat

variable {D : D7}

theorem idemSum_mul_eq_zero {P P' : Finset (Pl D.host.E)} {e e' : AE D} (he : IsIdemSum e P) (he' : IsIdemSum e' P')
    (hPP : ∀ w ∈ P, ∀ w' ∈ P', w ≠ w' ∧ ¬ Formalism.IndefR.Lev.IsConjPl (D := D) w w') : e * (e' + cA D e') = 0 := by
  obtain ⟨⟨es, hes, rfl⟩, -⟩ := he
  obtain ⟨⟨es', hes', rfl⟩, -⟩ := he'
  rw [map_sum, ← Finset.sum_add_distrib, Finset.mul_sum]
  refine Finset.sum_eq_zero fun w' hw' => ?_
  rw [Finset.sum_mul]
  refine Finset.sum_eq_zero fun w hw => ?_
  obtain ⟨h1, h2⟩ := hPP w hw w' hw'
  rw [mul_add, Formalism.IndefR.Fin.idem_orth (Formalism.IndefR.Fin.idemAt_split (hes w hw)) (hes w hw) (hes' w' hw') h1,
    Formalism.IndefR.Fin.idem_orth_conj (Formalism.IndefR.Fin.idemAt_split (hes w hw)) (hes w hw) (hes' w' hw') h2, add_zero]

theorem ne_and_not_conj {S : Finset ℕ} {w w' : Pl D.host.E} (hw : ¬ Off S w) (hw' : Off S w') :
    w ≠ w' ∧ ¬ Formalism.IndefR.Lev.IsConjPl (D := D) w w' := by
  unfold Off at hw hw'
  push_neg at hw
  obtain ⟨q, hq, hqw⟩ := hw
  refine ⟨fun h => hw' q hq (h ▸ hqw), fun h => ?_⟩
  obtain ⟨c', hc', hc'eq⟩ := h _ hqw
  apply hw' q hq
  have : c' = (q : 𝓞 D.host.E) := by
    apply RingOfIntegers.ext
    rw [hc'eq]
    simp
  rwa [this] at hc'

theorem actO_eq_self_of_half {S T : HSp D} {e a b : AE D} (ha : e * (a + cA D a) = 0) (hb : e * (b + cA D b) = 0)
    {g : GA D S} {h : GA D T} (hg : SuppAt a S g) (hh : SuppAt b T h) {x : WO S T} (hx : IsHalf e x) :
    actO S T g h x = x := by
  have hx' : ∀ c : AE D, e * c = 0 → (1 - c) • x = x := fun c hc => by
    ext i j
    simp only [Matrix.smul_apply, smul_eq_mul]
    rw [← hx i j, ← mul_assoc, sub_mul, one_mul, mul_comm c e, hc, sub_zero]
  unfold actO
  have k1 : HMul.hMul (mt T h) (x : Matrix (Fin T.rank) (Fin S.rank) (AE D)) = (x : Matrix (Fin T.rank) (Fin S.rank) (AE D)) := by
    conv_lhs => rw [← hx' _ hb]
    rw [Matrix.mul_smul, ← Matrix.smul_mul, GlobalTheory.SplitScalar.off_smul_mt hh, Matrix.smul_mul, Matrix.one_mul, hx' _ hb]
  rw [k1]
  conv_lhs => rw [← hx' _ ha]
  rw [Matrix.smul_mul, ← Matrix.mul_smul, GlobalTheory.SplitScalar.off_smul_mt_inv hg, Matrix.mul_smul, Matrix.mul_one, hx' _ ha]

theorem suppAt_inv' {a : AE D} {V : HSp D} {g : GA D V} (hg : SuppAt a V g) : SuppAt a V g⁻¹ := by
  have h := GlobalTheory.SplitScalar.off_smul_mt_inv hg
  rw [← sub_eq_zero, ← smul_sub, sub_smul, one_smul, sub_eq_zero] at h
  exact fun i j => (congrFun (congrFun h i) j).symm

end GlobalTheory.StdHalfLat

namespace GlobalTheory.StdHalfLat

open Matrix

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

variable {D : D7}

theorem actO_mem_latO_of_hat {S T : HSp D} (g : GA D S) (h : GA D T)
    {ΛS ΛS' : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)} {ΛT ΛT' : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)}
    (hS : ∀ v ∈ Formalism.L2.Herm.hatL (F := D.host.F) ΛS,
      (mt S g).map (toEAf D) *ᵥ v ∈ Formalism.L2.Herm.hatL (F := D.host.F) ΛS')
    (hT : ∀ v ∈ Formalism.L2.Herm.hatL (F := D.host.F) ΛT,
      (mt T h).map (toEAf D) *ᵥ v ∈ Formalism.L2.Herm.hatL (F := D.host.F) ΛT')
    {u : WO S T} (hu : u ∈ latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True) :
    actO S T g h u ∈ latO S T (ΛS' : Set (Fin S.rank → D.host.E)) (ΛT' : Set (Fin T.rank → D.host.E)) fun _ => True := by
  induction hu using AddSubgroup.closure_induction with
  | mem u hu =>
    obtain ⟨α, hα, -, a, ha, s, hs, t, ht, rfl⟩ := hu
    have e := GlobalTheory.AdelicLatMove.rankOne_pure S T a s t 1 α
    rw [mul_one] at e
    rw [← e, GlobalTheory.AdelicLatMove.actO_rankOne]
    exact GlobalTheory.AdelicLatMove.rankOne_mem_latO S T ΛS' ΛT' a ha _
      (hS _ (GlobalTheory.AdelicLatMove.pure_mem_hatL ΛS 1 (one_mem _) s hs)) _
      (hT _ (GlobalTheory.AdelicLatMove.pure_mem_hatL ΛT α hα t ht))
  | zero => simp only [actO, Matrix.mul_zero, Matrix.zero_mul]; exact zero_mem _
  | add y z _ _ hy hz => simp only [actO, Matrix.mul_add, Matrix.add_mul] at hy hz ⊢; exact add_mem hy hz
  | neg y _ hy => simp only [actO, Matrix.mul_neg, Matrix.neg_mul] at hy ⊢; exact neg_mem hy

theorem mem_latO_iff_of_half {S T : HSp D} (g : GA D S) (h : GA D T)
    {ΛS ΛS' : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)} {ΛT ΛT' : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)}
    (hS : ∀ v ∈ Formalism.L2.Herm.hatL (F := D.host.F) ΛS,
      (mt S g).map (toEAf D) *ᵥ v ∈ Formalism.L2.Herm.hatL (F := D.host.F) ΛS')
    (hS' : ∀ v ∈ Formalism.L2.Herm.hatL (F := D.host.F) ΛS',
      (mt S g⁻¹).map (toEAf D) *ᵥ v ∈ Formalism.L2.Herm.hatL (F := D.host.F) ΛS)
    (hT : ∀ v ∈ Formalism.L2.Herm.hatL (F := D.host.F) ΛT,
      (mt T h).map (toEAf D) *ᵥ v ∈ Formalism.L2.Herm.hatL (F := D.host.F) ΛT')
    (hT' : ∀ v ∈ Formalism.L2.Herm.hatL (F := D.host.F) ΛT',
      (mt T h⁻¹).map (toEAf D) *ᵥ v ∈ Formalism.L2.Herm.hatL (F := D.host.F) ΛT)
    {e a b : AE D} (ha : e * (a + cA D a) = 0) (hb : e * (b + cA D b) = 0) (hg : SuppAt a S g) (hh : SuppAt b T h)
    {x : WO S T} (hx : IsHalf e x) :
    x ∈ latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) (fun _ => True) ↔
      x ∈ latO S T (ΛS' : Set (Fin S.rank → D.host.E)) (ΛT' : Set (Fin T.rank → D.host.E)) fun _ => True := by
  constructor
  · intro hm
    have := actO_mem_latO_of_hat g h hS hT hm
    rwa [actO_eq_self_of_half ha hb hg hh hx] at this
  · intro hm
    have := actO_mem_latO_of_hat g⁻¹ h⁻¹ hS' hT' hm
    rwa [actO_eq_self_of_half ha hb (suppAt_inv' hg) (suppAt_inv' hh) hx] at this

theorem half_nsmul {m n : ℕ} {e : AE D} {x : Mx D m n} (hx : IsHalf e x) (k : ℕ) : IsHalf e (k • x) := fun i j => by
  have h := hx i j
  simp only [Matrix.smul_apply, nsmul_eq_mul]
  linear_combination (k : AE D) * h

end GlobalTheory.StdHalfLat

namespace GlobalTheory.StdHalfLat

open Matrix

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

theorem hat_moves {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {U : Set T} (N : Std G U)
    {X : Node} (hX : DefNode D.R.m X) :
    (∀ v ∈ Formalism.L2.Herm.hatL (F := D.host.F) (colLat (N.fr X)),
      (mt (G.V X) (N.u X).1).map (toEAf D) *ᵥ v ∈ Formalism.L2.Herm.hatL (F := D.host.F) (G.Λ X)) ∧
    ∀ v ∈ Formalism.L2.Herm.hatL (F := D.host.F) (G.Λ X),
      (mt (G.V X) (N.u X).1⁻¹).map (toEAf D) *ᵥ v ∈ Formalism.L2.Herm.hatL (F := D.host.F) (colLat (N.fr X)) := by
  refine ⟨fun v hv => (N.u_lat X hX v).1 hv, fun v hv => (N.u_lat X hX _).2 ?_⟩
  have e : (Formalism.IndefR.Lev.finE (G.V X) (N.u X).1).1 *ᵥ ((mt (G.V X) (N.u X).1⁻¹).map (toEAf D) *ᵥ v) = v := by
    rw [show (mt (G.V X) (N.u X).1⁻¹).map (toEAf D) = (Formalism.IndefR.Lev.finE (G.V X) (N.u X).1⁻¹).1 from rfl,
      Matrix.mulVec_mulVec, ← Units.val_mul, ← map_mul, mul_inv_cancel, map_one, Units.val_one, Matrix.one_mulVec]
  rw [e]
  exact hv

theorem exists_kill {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {U : Set T} (N : Std G U)
    {t : T} (ht : t ∈ U) {p : Pair T} (d : FinDatum G t p) {X : Node} (hX : DefNode D.R.m X) :
    ∃ a : AE D, d.e * (a + cA D a) = 0 ∧ SuppAt a (G.V X) (N.u X).1 := by
  obtain ⟨P', e', he', hsupp, hoff⟩ := N.u_supp X hX
  refine ⟨e', idemSum_mul_eq_zero d.e_is he' fun w hw w' hw' => ne_and_not_conj ?_ (hoff w' hw'), hsupp⟩
  intro hw0
  have h3 := N.off w hw0
  rcases d.P_over w hw with h | ⟨w'', hw'', h⟩
  · exact h3.1 h
  · exact h3.2.1 t ht w'' hw'' h

end GlobalTheory.StdHalfLat

namespace GlobalTheory.LastVertexMove

open GlobalTheory.StdHalfLat

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

theorem isSBHalf_stdLat : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T}
    (S : GridChoice W U) {t : T}, t ∈ U → ∀ {p : Pair T}, DefPair D.R.m p → ∀ d : FinDatum G t p,
    d.P = locPl G t → IsSBHalf d.e (stdLat S p) d.fn := by
  intro D T L sc G W U S t ht p hp d _
  have key : ∀ x, IsHalf d.e x →
      (x ∈ latO (G.pS p) (G.pT p) (G.latS p : Set _) (G.latT p : Set _) (fun _ => True) ↔ x ∈ stdLat S p) := by
    intro x hx
    obtain ⟨h1, h2⟩ := hp.nodes
    rcases p with ⟨i, j⟩ | ⟨t', i, j⟩ | i | ⟨t', j⟩
    · obtain ⟨a, ha, hga⟩ := exists_kill S.N ht d h2
      obtain ⟨b, hb, hgb⟩ := exists_kill S.N ht d h1
      have m2 := hat_moves S.N h2
      have m1 := hat_moves S.N h1
      exact (mem_latO_iff_of_half (negGA _ (S.N.u (.grid (i + 1) j)).1) (S.N.u (.grid i j)).1
        m2.1 (fun v hv => by rw [← map_inv]; exact m2.2 v hv) m1.1 m1.2 ha hb hga hgb hx).symm
    · exact hp.elim
    · exact hp.elim
    · obtain ⟨a, ha, hga⟩ := exists_kill S.N ht d h1
      obtain ⟨b, hb, hgb⟩ := exists_kill S.N ht d h2
      have m1 := hat_moves S.N h1
      have m2 := hat_moves S.N h2
      exact (mem_latO_iff_of_half (S.N.u (.top j)).1 (S.N.u (.top (j + 1))).1
        m1.1 m1.2 m2.1 m2.2 ha hb hga hgb hx).symm
  obtain ⟨hsupp, k, hk, hinv, hfin⟩ := d.sb
  refine ⟨hsupp, k, hk, fun u hu hub y => hinv u ((key u hub).2 hu) hub y, fun y hy => ?_⟩
  exact (key _ (half_nsmul (hsupp y hy) k)).1 (hfin y hy)

end GlobalTheory.LastVertexMove
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.AveragePreservesKFiniteness
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.Grow GlobalTheory.Size

noncomputable section

namespace GlobalTheory.AvgCoeff

open MeasureTheory

theorem exists_finset_sep {K : Type} (S : Submodule ℂ (K → ℂ)) [FiniteDimensional ℂ S] :
    ∃ T : Finset K, ∀ s ∈ S, (∀ t ∈ T, s t = 0) → s = 0 := by
  classical
  let f : Finset K → Submodule ℂ S := fun T =>
    ⨅ t ∈ T, LinearMap.ker ((LinearMap.proj (R := ℂ) (φ := fun _ : K => ℂ) t).comp S.subtype)
  obtain ⟨T, -, hT⟩ := (measure fun T => Module.finrank ℂ (f T)).wf.has_min Set.univ ⟨∅, trivial⟩
  refine ⟨T, fun s hs h0 => ?_⟩
  by_contra hne
  obtain ⟨t, ht⟩ := Function.ne_iff.1 hne
  have hmem : ∀ T' : Finset K, ∀ u : S, u ∈ f T' ↔ ∀ t ∈ T', (u : K → ℂ) t = 0 := fun T' u => by
    simp [f, Submodule.mem_iInf]
  have hle : f (insert t T) ≤ f T := fun u hu =>
    (hmem T u).2 fun t' ht' => (hmem _ u).1 hu t' (Finset.mem_insert_of_mem ht')
  have hlt : f (insert t T) < f T := by
    refine lt_of_le_of_ne hle fun heq => ?_
    have h1 : (⟨s, hs⟩ : S) ∈ f T := (hmem T _).2 h0
    rw [← heq] at h1
    exact ht ((hmem _ _).1 h1 t (Finset.mem_insert_self t T))
  exact hT (insert t T) trivial (Submodule.finrank_lt_finrank_of_lt hlt)

theorem integral_mem {K K' : Type} [MeasurableSpace K'] (μ : Measure K') (S : Submodule ℂ (K → ℂ))
    [FiniteDimensional ℂ S] (F : K' → K → ℂ) (hF : ∀ k', F k' ∈ S)
    (hi : ∀ k, Integrable (fun k' => F k' k) μ) : (fun k => ∫ k', F k' k ∂μ) ∈ S := by
  obtain ⟨T, hT⟩ := exists_finset_sep S
  let R : S →ₗ[ℂ] (T → ℂ) := LinearMap.pi fun t : T => (LinearMap.proj (R := ℂ) (φ := fun _ : K => ℂ) (t : K)).comp S.subtype
  have hker : LinearMap.ker R = ⊥ := by
    refine LinearMap.ker_eq_bot'.2 fun u hu => Subtype.ext ?_
    refine hT u u.2 fun t ht => ?_
    have := congrFun hu ⟨t, ht⟩
    simpa [R] using this
  obtain ⟨L, hL⟩ := LinearMap.exists_leftInverse_of_injective R hker
  let b := Pi.basisFun ℂ T
  have hexp : ∀ s ∈ S, s = ∑ t : T, s t • ((L (b t) : S) : K → ℂ) := by
    intro s hs
    have h1 : (⟨s, hs⟩ : S) = L (R ⟨s, hs⟩) := by rw [← LinearMap.comp_apply, hL, LinearMap.id_apply]
    have h2 : R ⟨s, hs⟩ = ∑ t : T, s t • b t := by
      conv_lhs => rw [← b.sum_repr (R ⟨s, hs⟩)]
      simp [R, b]
    rw [h2, map_sum] at h1
    have h3 := congrArg (fun u : S => (u : K → ℂ)) h1
    simpa [Submodule.coe_sum, map_smul] using h3
  have : (fun k => ∫ k', F k' k ∂μ) = ∑ t : T, (∫ k', F k' t ∂μ) • ((L (b t) : S) : K → ℂ) := by
    funext k
    have hk : ∀ k', F k' k = ∑ t : T, F k' t * ((L (b t) : S) : K → ℂ) k := fun k' => by
      conv_lhs => rw [hexp (F k') (hF k')]
      simp [Finset.sum_apply]
    simp_rw [hk]
    rw [integral_finset_sum (f := fun (t : T) k' => F k' t * ((L (b t) : S) : K → ℂ) k) Finset.univ
      fun t _ => (hi t).mul_const _]
    simp [Finset.sum_apply, integral_mul_const]
  rw [this]
  exact Submodule.sum_mem _ fun t _ => Submodule.smul_mem _ _ (L (b t)).2

theorem coeffSpan_finiteDimensional {K W : Type} [Group K] [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
    (ρ : Representation ℂ K W) : FiniteDimensional ℂ (GlobalTheory.Published.AutFin.coeffSpan ρ) := by
  first
  | exact @_root_.GlobalTheory.CoefficientSpanFiniteDimensional.finiteDimensional_coeffSpan
  | exact _root_.GlobalTheory.CoefficientSpanFiniteDimensional.finiteDimensional_coeffSpan
  | (apply _root_.GlobalTheory.CoefficientSpanFiniteDimensional.finiteDimensional_coeffSpan <;> assumption)
  | (intros; apply _root_.GlobalTheory.CoefficientSpanFiniteDimensional.finiteDimensional_coeffSpan <;> assumption)
  | (intros; apply @_root_.GlobalTheory.CoefficientSpanFiniteDimensional.finiteDimensional_coeffSpan <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.CoefficientSpanFiniteDimensional.finiteDimensional_coeffSpan ..)

theorem coeffSpan_mulRight {K W : Type} [Group K] [AddCommGroup W] [Module ℂ W] (ρ : Representation ℂ K W) (k' : K)
    {f : K → ℂ} (hf : f ∈ GlobalTheory.Published.AutFin.coeffSpan ρ) : (fun k => f (k * k')) ∈ GlobalTheory.Published.AutFin.coeffSpan ρ := by
  have : GlobalTheory.Published.AutFin.coeffSpan ρ ≤ (GlobalTheory.Published.AutFin.coeffSpan ρ).comap (LinearMap.funLeft ℂ ℂ (· * k')) := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨ℓ, w, rfl⟩
    exact Submodule.subset_span ⟨ℓ, ρ k' w, funext fun k => by simp [LinearMap.funLeft, map_mul]⟩
  exact this hf

end GlobalTheory.AvgCoeff

namespace GlobalTheory.CuspKFin

open Formalism.REAL GlobalTheory.Published.AutFin GlobalTheory.AvgCoeff

theorem kFinAt_avg_of_kFinAt : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (N : GlobalTheory.Grid.Node D) (ψ : GA D N.V → ℂ),
    IsAutFunSm θ N.V ψ → ∀ (τ τ' : D.what₂.Tau) (e : Formalism.REAL.KG (N.M.ε τ') → ℂ),
    GlobalTheory.TypeSum.KFinFun (N.M.ε τ') e → GlobalTheory.CuspKFin.KFinAt θ N τ ψ →
    GlobalTheory.CuspKFin.KFinAt θ N τ (GlobalTheory.SeriesToClosure.avg θ N.V τ' (N.M.ε τ') (N.M.fr τ') e ψ) := by
  intro D θ hθ N ψ hψ τ τ' e he hK
  obtain ⟨W, i1, i2, i3, ρ, hρc, hρ⟩ := hK
  refine ⟨W, i1, i2, i3, ρ, hρc, fun x => ?_⟩
  haveI : IsTopologicalGroup (GA D N.V) := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA _ _
  haveI := coeffSpan_finiteDimensional ρ
  have hec : Continuous e := by
    obtain ⟨F, -, heF, hc, -⟩ := he
    exact hc e heF
  have hAc : Continuous fun k' : Formalism.REAL.KG (N.M.ε τ') => atTau θ N.V τ' ((N.M.fr τ')⁻¹ * Formalism.REAL.toMK k' * N.M.fr τ') :=
    (GlobalTheory.PointAtPlaceHom.continuousOn_atTau hθ N.V τ').comp_continuous GlobalTheory.SeriesToClosure.continuous_conjK
      fun k => conj_mem_UH (N.M.fr_unit τ') (N.M.fr_gram τ') k
  have hmem : ∀ k' : Formalism.REAL.KG (N.M.ε τ'), (fun k => ψ (x * kAt θ N.V τ (N.M.ε τ) (N.M.fr τ) k *
      atTau θ N.V τ' ((N.M.fr τ')⁻¹ * Formalism.REAL.toMK k' * N.M.fr τ'))) ∈ GlobalTheory.Published.AutFin.coeffSpan ρ := by
    intro k'
    by_cases h : τ' = τ
    · subst h
      have h2 := coeffSpan_mulRight ρ k' (hρ x)
      convert h2 using 2 with k
      rw [mul_assoc]
      congr 2
      simp only [kAt]
      rw [← GlobalTheory.SeriesToClosure.at_mul hθ (N.M.fr_unit τ') (N.M.fr_gram τ')
        (GlobalTheory.TypeSum.K_le_UJ (GlobalTheory.TypeSum.toMK_mem_K k)) (GlobalTheory.TypeSum.K_le_UJ (GlobalTheory.TypeSum.toMK_mem_K k'))]
      rfl
    · have hc : ∀ k, kAt θ N.V τ (N.M.ε τ) (N.M.fr τ) k * atTau θ N.V τ' ((N.M.fr τ')⁻¹ * Formalism.REAL.toMK k' * N.M.fr τ') =
          atTau θ N.V τ' ((N.M.fr τ')⁻¹ * Formalism.REAL.toMK k' * N.M.fr τ') * kAt θ N.V τ (N.M.ε τ) (N.M.fr τ) k := fun k =>
        GlobalTheory.PointAtPlaceComm.atTau_comm D θ hθ N.V τ τ' (Ne.symm h) _
          (conj_mem_UH (N.M.fr_unit τ) (N.M.fr_gram τ) k) _ (conj_mem_UH (N.M.fr_unit τ') (N.M.fr_gram τ') k')
      have h2 := hρ (x * atTau θ N.V τ' ((N.M.fr τ')⁻¹ * Formalism.REAL.toMK k' * N.M.fr τ'))
      convert h2 using 2 with k
      rw [mul_assoc, hc, ← mul_assoc]
  have hcont : ∀ k, Continuous fun k' : Formalism.REAL.KG (N.M.ε τ') => e k' * ψ (x * kAt θ N.V τ (N.M.ε τ) (N.M.fr τ) k *
      atTau θ N.V τ' ((N.M.fr τ')⁻¹ * Formalism.REAL.toMK k' * N.M.fr τ')) := fun k =>
    hec.mul (hψ.cont.comp (continuous_const.mul hAc))
  have key := GlobalTheory.AvgCoeff.integral_mem (muK (N.M.ε τ')) (GlobalTheory.Published.AutFin.coeffSpan ρ)
    (fun k' k => e k' * ψ (x * kAt θ N.V τ (N.M.ε τ) (N.M.fr τ) k *
      atTau θ N.V τ' ((N.M.fr τ')⁻¹ * Formalism.REAL.toMK k' * N.M.fr τ')))
    (fun k' => Submodule.smul_mem _ (e k') (hmem k')) (fun k => GlobalTheory.ExpansionAverage.integrable_K (hcont k))
  exact key

end GlobalTheory.CuspKFin

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.BesselCoreVertexLatticeSplitsAlongOrthDecompositStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.orthAt_oB_lat0_of_std : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (F : Frames G), Std F → ∀ (ρ : ℕ) (h : 2 * ρ + 2 ≤ D.R.m) (v : GlobalTheory.FinPl.Pl D), OrthAt (F.oB ρ h) (lat0 F ρ h) (G.Λ (.core (2 * ρ + 2))) (idLat (G.pl.stA sc ^ (ρ + 1) * (G.pl.stAbar sc ^ (ρ + 1))⁻¹) (Submodule.span (𝓞 D.host.E) {F.ζ 0})) v := by
  first | exact @GlobalTheory.AscFin.CoreSum.besselCoreVertexLattice_splitsAlongOrthDecomposition | exact GlobalTheory.AscFin.CoreSum.besselCoreVertexLattice_splitsAlongOrthDecomposition | (intros; apply GlobalTheory.AscFin.CoreSum.besselCoreVertexLattice_splitsAlongOrthDecomposition <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.BesselHandedFunctionProductEqCoreLiftMulPairingStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Asc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.besselHandedFunction_product_eq_coreLift_mul_pairing : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (σ : ℕ) (J : JacL D (σ + 1)) (B : BesL D σ) (s : StFB ψ J B), ∀ (vL : VolM D B.L.rank J.W₀.rank) (χA χz : (AE D)ˣ →* Circle) (omb : Om J.W₀ B.A) (omz : Om J.W₀ B.L), s.χW = χA * χz → IsWeilDatumO ψ J.W₀ B.A s.χV χA omb → IsWeilDatumO ψ J.W₀ B.L s.χV χz omz → ∀ (φ : GA D J.W₀ → ℂ) Ξ₁ Φ' Φ₀, IsThetaFunO ψ J.W₀ B.A Ξ₁ → IsThetaFunO ψ J.W₀ B.L Φ' → IsThetaFunO ψ J.W₀ B.L Φ₀ → handP s vL omz φ Φ₀ (B.o.boxT J.W₀ Ξ₁ Φ') = thPair vL.μ vL.𝓕 Φ' Φ₀ • liftT omb J.v0.μ J.v0.𝓕 φ Ξ₁ := by
  first | exact @GlobalTheory.HandProd.handP_boxT | exact GlobalTheory.HandProd.handP_boxT | (intros; apply GlobalTheory.HandProd.handP_boxT <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.BesselStepBasePointScaledCoordinatesStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin
open ValuativeRel
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.besselStep_basePoint_scaled_coordinates : OnStd fun {D} _ _ {sc} {G} W F => ∀ σ (h : 2 * (σ + 1) + 2 ≤ D.R.m), ∀ v ∈ G.pl.S0, ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (p : GlobalTheory.FinPl.SplitPt D k) (β : GlobalTheory.FinPl.Frame p (G.V (.grid (2 * (σ + 1) + 1) 0)) (Fin (G.V (.grid (2 * (σ + 1) + 1) 0)).rank)) (ϖ : 𝒪[k])
    (κ : Fin (2 * (σ + 1) + 1 - 1) → Fin (G.V (.grid (2 * (σ + 1) + 1) 0)).rank),
  p.v = v →
  Formalism.L2.NTheta.IsIdemAt p.e (G.pl.w v) →
  β.IsLat (G.Λ (.grid (2 * (σ + 1) + 1) 0)) (Submodule.pi Set.univ fun _ => (1 : Submodule 𝒪[k] k)) →
  Irreducible ϖ →
  Function.Injective κ →
  (∀ r i, β.b i (κ r) = (ϖ : k) ^ (G.pl.depth sc v * (r.1 + 1)) * p.pr (incA D ((G.colDec (2 * (σ + 1) + 1) (by omega) (by omega)).a i r))) →
  (∀ j, j ∉ Set.range κ → ∀ r, ((Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) (G.colDec (2 * (σ + 1) + 1) (by omega) (by omega)).a * (G.V (.grid (2 * (σ + 1) + 1) 0)).gram).map
      (fun c => p.pr (incA D c)) * β.b) r j = 0) →
  ∃ s t : Fin (σ + 1) → k, (∀ q, s q • (β.b' *ᵥ fun i => p.pr (xZero (F.dJ (σ + 1) h) i q)) = Pi.single (κ ⟨q.1, by omega⟩) 1) ∧
    (∀ q, t q • ((fun i => p.pr (cA D (xZero (F.dJ (σ + 1) h) i q))) ᵥ*
    ((G.V (.grid (2 * (σ + 1) + 1) 0)).gram.map (fun c => p.pr (incA D c)) * β.b)) = Pi.single (κ ⟨2 * (σ + 1) - 1 - q.1, by omega⟩) 1) := by
  first | exact @GlobalTheory.FrameZero.xclauses | exact GlobalTheory.FrameZero.xclauses | (intros; apply GlobalTheory.FrameZero.xclauses <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.BottomTriangleIntegralLeftInvariant
section
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx MeasureTheory
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx MeasureTheory

open GlobalTheory.Grid

namespace GlobalTheory.RowTest.BottomRat

theorem I_rat_left : ∀ {D : D7} {T : Type} [Finite T] {L : LevCh D T} {μ₀ : T} {sc : Consts} {G : GridData L sc} {W : G.Weil}
    {i j : Fin D.R.m} {A A' WW : HSp D} {X : Tri T A A' WW}, GlobalTheory.FunPr.Hypotheses₂ → (∀ D, GlobalTheory.NormSum.Inp D) → L.Is μ₀ →
    IsBottomTri W i j X →
    ∀ t P, ∀ γ ∈ GQ WW, ∀ x, X.I W.ψ W.θ t P (γ * x) = X.I W.ψ W.θ t P x := by
  intro D T _ L μ₀ sc G W i j A A' WW X _ _ _ hX t P γ hγ x
  have hw := hX.is.weil t
  have hF : IsThetaFunO W.ψ (neg A) WW (pureTensorO W.ψ W.θ (neg A) WW (fun τ => -X.rA.s τ) X.rW.s X.rA.B X.rW.B (X.f t) P) :=
    GlobalTheory.Chain.InnerSteps.theta_pureTensorO (S := neg A) hX.is.isVac.1 hX.is.isVac.2.inf (fun τ => -X.rA.s τ) X.rA.B X.rW.s X.rW.B
      (GlobalTheory.ConstRatio.theta_f hX.is t).1 P
  unfold Tri.I
  congr 1
  funext g
  unfold Tri.ker thetaKO
  set F := pureTensorO W.ψ W.θ (neg A) WW (fun τ => -X.rA.s τ) X.rW.s X.rA.B X.rW.B (X.f t) P
  set ω' := (X.ω t).toSgn true
  have e : ∀ y, X.ω t (g, y) = ω' ((ofSgn true A).symm g, y) := fun y => by
    simp [ω', WRep.toSgn]
  rw [e, e]
  have e2 : (((ofSgn true A).symm g, γ * x) : GA D (sgn true A) × GA D WW) = (1, γ) * ((ofSgn true A).symm g, x) := by simp
  rw [e2, map_mul, Module.End.mul_apply]
  exact hw.om_aut 1 (one_mem _) γ hγ _ (hw.om_pres _ _ hF)

end GlobalTheory.RowTest.BottomRat
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ClassConditionsCoreFromMixedCoordinateFunctionStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.class_conditions_core_from_mixedCoordinateFunction : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (V V₀ W W₀ : HSp D) (ρ σ : ℕ) (dV : HypDec V V₀ ρ) (dW : HypDec W W₀ σ) (vS : VolM D W.rank ρ) (p : Pieces V₀ W W₀ ρ σ) (y : Mx D V₀.rank σ) (β₁ : Mx D W.rank ρ → ℂ) (g' : WO V₀ W → ℂ) (Φ : WO V W → ℂ), IsThetaFunO ψ V₀ W g' → IsThetaFunO ψ V W Φ → (∀ x', dV.mixS W ψ vS.μ vS.𝓕 Φ x' = β₁ x' • g') → (∀ ξ ∈ p.B₁, heisO ψ V₀ W (dW.incX V₀ ξ) g' = ψ (symplO V₀ W (dW.incAdj V₀ y) (dW.incX V₀ ξ)) • g') → (∀ η ∈ p.B₂, heisO ψ V₀ W (dW.incY V₀ η) g' = g') → IsLatVac (heisO ψ V₀ W) (p.Γ₀.map (dW.inc0 V₀)) g' → (∀ ξ ∈ p.B₁, heisO ψ V W (dV.ext0 W (dW.incX V₀ ξ)) Φ = ψ (symplO V₀ W (dW.incAdj V₀ y) (dW.incX V₀ ξ)) • Φ) ∧ (∀ η ∈ p.B₂, heisO ψ V W (dV.ext0 W (dW.incY V₀ η)) Φ = Φ) ∧ IsLatVac (fun w f => heisO ψ V W w f) (p.Γ₀.map ((dV.ext0 W).comp (dW.inc0 V₀))) Φ := by
  first | exact @GlobalTheory.ClsCoreFromMix.main | exact GlobalTheory.ClsCoreFromMix.main | (intros; apply GlobalTheory.ClsCoreFromMix.main <;> assumption)
end

