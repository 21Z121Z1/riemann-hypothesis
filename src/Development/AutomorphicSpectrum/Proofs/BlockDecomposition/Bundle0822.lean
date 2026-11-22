import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0818
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0813
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0789
import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.WeakApproximationFinitePlace
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsRadNMulLevM
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0816
import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.ThetaIdempotents.HeckeEta
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PartialConstantTermBound
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0812
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2005
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2006
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0641
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0656
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0480
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JacobiMapsExist
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0819
import Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinContinuation.EisensteinChartSplitting.TChartSplit
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0815
import Formalism.LocalToGlobal.BesselHermitianTheta.Bundle0003
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1870
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0771
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0820
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TypedSpaceApproximation
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.InfinitesimalCharacterGlue
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.T2SpaceAdelicGeneralLinearGroupNumberField
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0125

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FlatNodeFunctionStatement
section
open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec GlobalTheory.CompanionTheory.CTFin PositivityTheory.Rg.Rs PositivityTheory.Rg.Rs.InducedTensorMap
open PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation GlobalTheory.CompanionTheory.LimV
open scoped ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flat_node_function : ∀ {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {r s : ℕ} (e₁ : GA E r → ℂ) (e₂ : GA E s → ℂ), FlatFn e₁ → FlatFn e₂ → FlatFn (nodeFn e₁ e₂) := by
  first | exact @GlobalTheory.CompanionTheory.LimV.NodeFlat.flatFn_nodeFn | exact GlobalTheory.CompanionTheory.LimV.NodeFlat.flatFn_nodeFn | (intros; apply GlobalTheory.CompanionTheory.LimV.NodeFlat.flatFn_nodeFn <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HaarSkewMatricesConjScaling
section
noncomputable section
open scoped Matrix NNReal ENNReal TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.CompanionTheory.QKAvg
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.SkewMod

open GlobalTheory.CompanionTheory.IwaAd GlobalTheory.CompanionTheory.CgMod

variable {D : D7} {n : ℕ}

def skewPart (D : D7) (n : ℕ) (x : Mx D n n) : Mx D n n := half D • (x - adj x)

theorem skewPart_add (x y : Mx D n n) : skewPart D n (x + y) = skewPart D n x + skewPart D n y := by
  simp only [skewPart, adj_add]
  rw [← smul_add]
  congr 1
  abel

def skewPartHom (D : D7) (n : ℕ) : Mx D n n →+ Mx D n n := AddMonoidHom.mk' (skewPart D n) skewPart_add

theorem skewPart_mem (x : Mx D n n) : skewPart D n x ∈ skewA D n := by
  rw [mem_skewA, skewPart, adj_smul, cA_half, adj_sub, adj_adj, ← smul_neg, neg_sub]

theorem skewPart_of_mem {s : Mx D n n} (hs : s ∈ skewA D n) : skewPart D n s = s := by
  rw [skewPart, mem_skewA.1 hs, sub_neg_eq_add, smul_add]
  exact half_smul_add s

theorem skewPart_anti {c : AE D} (hc : cA D c = -c) {s : Mx D n n} (hs : s ∈ skewA D n) :
    skewPart D n (c • s) = 0 := by
  rw [skewPart, adj_smul, mem_skewA.1 hs, hc, neg_smul, smul_neg, neg_neg, sub_self, smul_zero]

theorem skewPart_split {d e : AE D} (he : cA D e = -e) (hde : d * e = 1) (x : Mx D n n) :
    skewPart D n x + d • skewPart D n (e • x) = x := by
  have h : d * half D * e = half D := by rw [mul_comm d, mul_assoc, hde, mul_one]
  rw [skewPart, skewPart, adj_smul, he, neg_smul, sub_neg_eq_add, ← smul_add, smul_smul, smul_smul, h, smul_add,
    smul_sub]
  have := half_smul_add x
  rw [sub_add_add_cancel]
  exact this

set_option synthInstance.maxHeartbeats 400000 in
theorem continuous_skewPart : Continuous (skewPartHom D n) := by
  haveI : IsTopologicalAddGroup (Mx D n n) := (lattice_Mx D n n).1
  have h : Continuous fun x : Mx D n n => x - adj x := continuous_id.sub (continuous_adj (D := D) (m := n) (n := n))
  change Continuous fun x : Mx D n n => half D • (x - adj x)
  exact h.const_smul (half D)

theorem lr_skew (a : GL (Fin n) (AE D)) : ∀ s ∈ skewA D n, GlobalTheory.ModuLR.lrCE a (ad a)⁻¹ s ∈ skewA D n :=
  fun s hs => (skewConj a.1 ⟨s, hs⟩).2

theorem lr_skew_symm (a : GL (Fin n) (AE D)) :
    ∀ s ∈ skewA D n, (GlobalTheory.ModuLR.lrCE a (ad a)⁻¹).symm s ∈ skewA D n :=
  fun s hs => (skewConj (a⁻¹).1 ⟨s, hs⟩).2

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1000000 in

theorem map_skewConj : ∀ (D : D7) (r : ℕ) (κ : Measure (skewA D r)), κ.IsAddHaarMeasure → ∀ a : GL (Fin r) (AE D), κ.map (skewConj a.1) = ((absA D (Matrix.GeneralLinearGroup.det a) ^ r)⁻¹ : ℝ≥0) • κ := by
  intro D n κ hκ a
  obtain ⟨i1, i2, i3, i4, -, -⟩ := lattice_Mx D n n
  haveI : IsTopologicalAddGroup (Mx D n n) := i1
  haveI : LocallyCompactSpace (Mx D n n) := i2
  haveI : SecondCountableTopology (Mx D n n) := i3
  haveI : T2Space (Mx D n n) := i4
  haveI : BorelSpace (Mx D n n) := ⟨rfl⟩
  haveI : BorelSpace (skewA D n) := Subtype.borelSpace _
  haveI : SecondCountableTopology (skewA D n) := Topology.IsInducing.subtypeVal.secondCountableTopology
  haveI : T2Space (skewA D n) := Topology.IsEmbedding.subtypeVal.t2Space
  have hcl : IsClosed (skewA D n : Set (Mx D n n)) := isClosed_eq continuous_adj continuous_neg
  haveI : LocallyCompactSpace (skewA D n) := hcl.isClosedEmbedding_subtypeVal.locallyCompactSpace
  obtain ⟨d, e, hde, hd, he⟩ := exists_anti_units D
  have hsq := char_sq (skewA D n) (skewPartHom D n) continuous_skewPart skewPart_mem
    (fun s hs => skewPart_of_mem hs) (mulCE d e hde)
    (fun s hs => skewPart_anti hd hs) (fun s hs => skewPart_anti he hs)
    (fun x => skewPart_split he hde x) (GlobalTheory.ModuLR.lrCE a (ad a)⁻¹)
    (lr_smul a d e hde) (lr_skew a) (lr_skew_symm a)
  have hlr : addEquivAddHaarChar (GlobalTheory.ModuLR.lrCE a (ad a)⁻¹) =
      absA D (Matrix.GeneralLinearGroup.det a : (AE D)ˣ) ^ n * absA D (Matrix.GeneralLinearGroup.det a : (AE D)ˣ) ^ n := by
    have h := GlobalTheory.ResidueEisenstein.ModMat.addEquivAddHaarChar_lrCE _ _ D.sp.cm.sig (isCMExt_host D) n n a (ad a)⁻¹
    rw [h]
    exact congrArg (fun t => absA D (Matrix.GeneralLinearGroup.det a : (AE D)ˣ) ^ n * t ^ n) (absA_det_ad_inv a)
  have hT : addEquivAddHaarChar (restr (skewA D n) _ (lr_skew a) (lr_skew_symm a)) =
      absA D (Matrix.GeneralLinearGroup.det a : (AE D)ˣ) ^ n :=
    (pow_left_inj₀ zero_le zero_le two_ne_zero).1 ((hsq.trans hlr).trans (sq _).symm)
  have h := addEquivAddHaarChar_smul_map κ (restr (skewA D n) _ (lr_skew a) (lr_skew_symm a))
  have e1 : (⇑(restr (skewA D n) _ (lr_skew a) (lr_skew_symm a)) : skewA D n → skewA D n) = skewConj a.1 := rfl
  rw [hT, e1] at h
  have hne : absA D (Matrix.GeneralLinearGroup.det a : (AE D)ˣ) ^ n ≠ 0 := pow_ne_zero _ (absA_pos _).ne'
  conv_rhs => rw [← h]
  rw [smul_smul, inv_mul_cancel₀ hne, one_smul]

end GlobalTheory.CompanionTheory.SkewMod
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HeightPullbackFirstBlockStatement
section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.height_pullback_first_block : ∀ (D : D7) (n ρ p : ℕ) (hn : ρ + p = n) (ι : G D ρ →* G D n), Continuous ι →
  (∀ (h : G D ρ) (a b c d : Mx D ρ ρ), mat h = blk4 a b c d →
    mat (ι h) = blk4 (bl hn a 0 0 1) (bl hn b 0 0 0) (bl hn c 0 0 0) (bl hn d 0 0 1)) →
  ∀ H : G D n → ℝ≥0, IsHt H → IsHt (fun h : G D ρ => H (ι h)) := by
  first | exact @GlobalTheory.CompanionTheory.HtPull.isHt_blockPull | exact GlobalTheory.CompanionTheory.HtPull.isHt_blockPull | (intros; apply GlobalTheory.CompanionTheory.HtPull.isHt_blockPull <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermitianMeasureConjugationStatement
section
noncomputable section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermitian_measure_conjugation : ∀ (D : D7) (n : ℕ) (lam : Measure (hermA D n)), lam.IsAddHaarMeasure → ∀ (a : GL (Fin n) (AE D)) (f : hermA D n → ℂ), ∫ c, f (GlobalTheory.CompanionTheory.IwaAd.cg a c) ∂lam = npow (absA D (Matrix.GeneralLinearGroup.det a)) (-(n : ℂ)) * ∫ c, f c ∂lam := by
  first | exact @GlobalTheory.CompanionTheory.CgMod.integral_cg | exact GlobalTheory.CompanionTheory.CgMod.integral_cg | (intros; apply GlobalTheory.CompanionTheory.CgMod.integral_cg <;> assumption)
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IntegrableThetaKernelProduct
section
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS
open IsDedekindDomain NumberField
open GlobalTheory.RegSch (ikS projS Lvl)
open PositivityTheory.Rg.Rsw PositivityTheory.Rg.Rsw.L
open GlobalTheory.CompanionTheory.ColumnSplitting
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.ColumnSplitting

namespace Integ

variable {D : D7} {n t : ℕ} {B W : HSp D}

theorem det_bl {r t n : ℕ} (hn : r + t = n) (y : Mx D r t) :
    Matrix.det (bl hn 1 y 0 1 : Mx D n n) = 1 := by
  unfold bl
  rw [Matrix.det_submatrix_equiv_self, Matrix.det_fromBlocks_zero₂₁]
  simp

def blU {r t n : ℕ} (hn : r + t = n) (y : Mx D r t) : GL (Fin n) (AE D) :=
  ⟨bl hn 1 y 0 1, bl hn 1 (-y) 0 1, GlobalTheory.CompanionTheory.JacobiMaps.sh_mul hn _ _ rfl,
    GlobalTheory.CompanionTheory.JacobiMaps.sh_mul hn _ _ (neg_neg y).symm⟩

theorem det_blU {r t n : ℕ} (hn : r + t = n) (y : Mx D r t) (a : GL (Fin n) (AE D)) (ha : a.1 = bl hn 1 y 0 1) :
    Matrix.GeneralLinearGroup.det a = 1 := by
  apply Units.ext
  rw [Matrix.GeneralLinearGroup.val_det_apply, Units.val_one, ha]
  exact det_bl hn y

theorem lintegral_comp_char_one {A : Type} [AddCommGroup A] [TopologicalSpace A] [IsTopologicalAddGroup A]
    [LocallyCompactSpace A] [SecondCountableTopology A] [T2Space A] [MeasurableSpace A] [BorelSpace A]
    (μ : Measure A) [μ.IsAddHaarMeasure] (φ : A ≃ₜ+ A) (hc : addEquivAddHaarChar φ = 1) (g : A → ℝ≥0∞) :
    ∫⁻ y, g (φ y) ∂μ = ∫⁻ y, g y ∂μ := by
  have key := addEquivAddHaarChar_smul_map μ φ
  rw [hc, one_smul] at key
  have hp : MeasurePreserving φ μ μ := ⟨φ.continuous.measurable, key⟩
  exact hp.lintegral_comp_emb φ.toHomeomorph.measurableEmbedding g

theorem lintegral_bl {a r t n : ℕ} (hn : r + t = n) (y : Mx D r t) (ν : Measure (Mx D a n))
    (hν : ν.IsAddHaarMeasure) (g : Mx D a n → ℝ≥0∞) :
    ∫⁻ U, g (mm U (bl hn 1 y 0 1)) ∂ν = ∫⁻ U, g U ∂ν := by
  obtain ⟨i1, i2, i3, i4, i5⟩ := top_mx (D := D) a n
  haveI := isTopologicalRing_tens (F := D.host.F) (E := D.host.E) (R := AF D.host.F)
  let φ := GlobalTheory.ModuLR.lrCE (1 : GL (Fin a) (AE D)) (blU hn y)
  have hc : addEquivAddHaarChar φ = 1 := by
    have h := GlobalTheory.ResidueEisenstein.ModMat.addEquivAddHaarChar_lrCE D.host.F D.host.E D.sp.cm.sig (isCMExt_host D) a n
      (1 : GL (Fin a) (AE D)) (blU hn y)
    rw [det_blU hn y (blU hn y) rfl] at h
    simpa only [map_one, one_pow, mul_one] using h
  have e : ∀ U : Mx D a n, mm U (bl hn 1 y 0 1) = φ U := fun U => by
    simp only [φ]
    rw [GlobalTheory.ModuLR.lrCE_apply, Units.val_one, Matrix.one_mul]
    rfl
  simp only [e]
  exact lintegral_comp_char_one ν φ hc g

theorem jn_first {a r t n : ℕ} (hn : r + t = n) (w : Mx D a r) (v : Mx D a t) :
    (jn hn w v).submatrix id (fun j => finCongr hn (Fin.castAdd t j)) = w := by
  ext i j
  simp [jn, Matrix.submatrix_apply, Matrix.fromCols]

theorem xu_bl (d : HypDec B W t) (hn : W.rank + t = n) (x₀ : Matrix (Fin W.rank) (Fin W.rank) D.host.E)
    (h : GA D W) (U : Mx D t n) (y : Mx D W.rank t) :
    mm (XU d hn x₀ h U) (bl hn 1 y 0 1) =
      mm d.jX (mm U (bl hn 1 y 0 1)) + mm d.j0 (mm (jn hn (ww W x₀ h) 0) (bl hn 1 y 0 1)) := by
  unfold XU
  simp only [mm]
  rw [Matrix.add_mul, Matrix.mul_assoc, Matrix.mul_assoc]

theorem inner_eq (hIkL : IkLint) (hJn : JnBl) {d : HypDec B W t} (hn : W.rank + t = n) (I : IkD d n) {θ : InfFam D}
    (hθ : IsInfFam θ) {M : Mx D B.rank n → ℂ} (hM : M ∈ schwartzA θ B.rank n)
    (hM0 : ∀ x, 0 ≤ (M x).re ∧ (M x).im = 0) (x₀ : Matrix (Fin W.rank) (Fin W.rank) D.host.E) (h : GA D W)
    (y : Mx D W.rank t) :
    ∫⁻ U, ∫⁻ k : I.l.K, ‖M (mm (mt B ((k : GA D B)⁻¹)) (mm (XU d hn x₀ h U) (bl hn 1 y 0 1)))‖ₑ ∂I.νK ∂I.μ₁ =
      ‖ikp I M (jn hn (ww W x₀ h) (mm (ww W x₀ h) y + 0))‖ₑ := by
  obtain ⟨𝓕, hf⟩ := I.cov₁
  have hb : mm (jn hn (ww W x₀ h) 0) (bl hn 1 y 0 1) = jn hn (ww W x₀ h) (mm (ww W x₀ h) y + 0) :=
    hJn D n t _ _ hn _ _ y
  rw [← hb, ← hIkL D n t B W d I θ hθ M hM hM0]
  simp only [xu_bl]
  exact lintegral_bl hn y I.μ₁ hf.1
    (fun U => ∫⁻ k : I.l.K, ‖M (mm (mt B ((k : GA D B)⁻¹)) (mm d.jX U + mm d.j0 (mm (jn hn (ww W x₀ h) 0) (bl hn 1 y 0 1))))‖ₑ ∂I.νK)

theorem continuous_jn {a r t n : ℕ} (hn : r + t = n) :
    Continuous fun u : Mx D a r × Mx D a t => jn hn u.1 u.2 := by
  refine continuous_matrix fun i j => ?_
  change Continuous fun u : Mx D a r × Mx D a t =>
    Matrix.fromCols u.1 u.2 i ((finSumFinEquiv.trans (finCongr hn)).symm j)
  generalize (finSumFinEquiv.trans (finCongr hn)).symm j = s
  cases s with
  | inl k => exact continuous_fst.matrix_elem i k
  | inr k => exact continuous_snd.matrix_elem i k

theorem continuous_bl {r t n : ℕ} (hn : r + t = n) : Continuous fun y : Mx D r t => (bl hn 1 y 0 1 : Mx D n n) :=
  (continuous_const.matrix_fromBlocks continuous_id continuous_const continuous_const).matrix_submatrix _ _

theorem continuous_pt {d : HypDec B W t} (hn : W.rank + t = n) (I : IkD d n)
    (x₀ : Matrix (Fin W.rank) (Fin W.rank) D.host.E) :
    Continuous fun p : I.l.K × Par D n t W =>
      mm (mt B ((p.1 : GA D B)⁻¹)) (mm (XU d hn x₀ p.2.1 p.2.2.1) (bl hn 1 p.2.2.2 0 1)) := by
  have := isTopologicalRing_tens (F := D.host.F) (E := D.host.E) (R := AF D.host.F)
  obtain ⟨-, k2, -, -, k5, -⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D B
  obtain ⟨-, g2, -, -, g5, -⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D W
  have hT := (top_mx (D := D) B.rank n).1
  have hU : Continuous fun p : I.l.K × Par D n t W => p.2.2.1 := continuous_fst.comp (continuous_snd.comp continuous_snd)
  have hh : Continuous fun p : I.l.K × Par D n t W => p.2.1 := continuous_fst.comp continuous_snd
  have hy : Continuous fun p : I.l.K × Par D n t W => p.2.2.2 := continuous_snd.comp (continuous_snd.comp continuous_snd)
  have hX : Continuous fun p : I.l.K × Par D n t W => XU d hn x₀ p.2.1 p.2.2.1 :=
    (continuous_const.matrix_mul hU).add (continuous_const.matrix_mul
      ((continuous_jn hn).comp (((continuous_ww x₀).comp hh).prodMk continuous_const)))
  exact ((continuous_mt B).comp (continuous_subtype_val.comp continuous_fst).inv).matrix_mul
    (hX.matrix_mul ((continuous_bl hn).comp hy))

end Integ

open Integ in

theorem integrable_core : IkSch → Dom → OrbFin → Shift → IkLint → Fub4 → JnBl → ∀ (D : D7) (n t : ℕ) (B W : HSp D) (d : HypDec B W t) (hn : W.rank + t = n) (I : IkD d n) θ, IsInfFam θ → ∀ (μ : Measure (Mx D W.rank t)), μ.IsAddHaarMeasure → ∀ (x₀ : Matrix (Fin W.rank) (Fin W.rank) D.host.E), x₀.det ≠ 0 → ∀ Φ ∈ schwartzA θ B.rank n, ∀ η ∈ schwartzA θ W.rank t, Integrable (core hn I x₀ Φ η) (I.νK.prod (Q0 I μ)) := by
  intro hIk hDom hOrb _ hIkL hFub hJn D n t B W d hn I θ hθ μ hμ x₀ hx₀ Φ hΦ η hη
  obtain ⟨M, hM, hM0, hMd⟩ := hDom D θ hθ B.rank n n id Function.injective_id Φ hΦ
  have hΨ : ikp I M ∈ schwartzA θ W.rank n := (hIk D n t B W d I θ hθ M hM).2
  obtain ⟨N, hN, -, hNd⟩ := hDom D θ hθ W.rank n W.rank (fun j => finCongr hn (Fin.castAdd t j))
    (fun a b h => by simpa using h) (ikp I M) hΨ

  obtain ⟨h1, h2⟩ := top_par (D := D) n t W
  obtain ⟨-, i2, i3, i4, i5⟩ := top_mx (D := D) t n
  obtain ⟨-, j2, j3, j4, j5⟩ := top_mx (D := D) W.rank t
  obtain ⟨-, g2, g3, -, -, -⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D W
  obtain ⟨-, k2, -, -, k5, -⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D B
  have hBG : BorelSpace (GA D W) := ⟨rfl⟩
  have hB : BorelSpace (GA D B) := ⟨rfl⟩
  have hK : BorelSpace I.l.K := Subtype.borelSpace _
  have o0 : OpensMeasurableSpace (Par D n t W) := h1.opensMeasurable
  have oK : OpensMeasurableSpace I.l.K := hK.opensMeasurable
  have e1 : SecondCountableTopologyEither I.l.K (Par D n t W) := ⟨Or.inr h2⟩
  have o1 : OpensMeasurableSpace (I.l.K × Par D n t W) := Prod.opensMeasurableSpace
  obtain ⟨𝓕, hf⟩ := I.cov₁
  have := hf.1
  have := I.haar
  have := I.probK
  have hcM : Continuous M := (GlobalTheory.CompanionTheory.WeilTheta.schwartzA_continuous_and_dominated D θ hθ _ _ M hM).1
  have hcΦ : Continuous Φ := (GlobalTheory.CompanionTheory.WeilTheta.schwartzA_continuous_and_dominated D θ hθ _ _ Φ hΦ).1
  have hcη : Continuous η := (GlobalTheory.CompanionTheory.WeilTheta.schwartzA_continuous_and_dominated D θ hθ _ _ η hη).1
  have hpt := continuous_pt (d := d) hn I x₀
  have hy : Continuous fun p : I.l.K × Par D n t W => p.2.2.2 := continuous_snd.comp (continuous_snd.comp continuous_snd)
  have hcore : Continuous (core hn I x₀ Φ η) :=
    (hcΦ.comp hpt).mul (Complex.continuous_conj.comp (hcη.comp hy))
  refine ⟨hcore.measurable.aestronglyMeasurable, ?_⟩

  set F : I.l.K × GA D W × Mx D t n × Mx D W.rank t → ℝ≥0∞ := fun p =>
    ‖M (mm (mt B ((p.1 : GA D B)⁻¹)) (mm (XU d hn x₀ p.2.1 p.2.2.1) (bl hn 1 p.2.2.2 0 1)))‖ₑ * ‖η p.2.2.2‖ₑ with hF
  have hFm : Measurable F :=
    (hcM.comp hpt).measurable.enorm.mul (hcη.comp hy).measurable.enorm
  have hle : ∀ p, ‖core hn I x₀ Φ η p‖ₑ ≤ F p := fun p => by
    simp only [core, hF, enorm_mul, RCLike.enorm_conj]
    gcongr
    rw [enorm_le_iff_norm_le]
    refine (hMd _).trans ?_
    simpa using Complex.re_le_norm _
  have hη' : ∫⁻ y, ‖η y‖ₑ ∂μ < ⊤ :=
    hasFiniteIntegral_iff_enorm.1 (GlobalTheory.CompanionTheory.WSum.integrable_schwartzA_haar D θ hθ W.rank t μ η hη).2
  have hN' : ∫⁻ h, ‖N (ww W x₀ h)‖ₑ ∂I.m < ⊤ := hOrb D θ hθ W I.m I.haar x₀ hx₀ N hN
  have hin : ∀ y h, ∫⁻ U, ∫⁻ k : I.l.K, F (k, h, U, y) ∂I.νK ∂I.μ₁ ≤ ‖N (ww W x₀ h)‖ₑ * ‖η y‖ₑ := fun y h => by
    simp only [hF]
    have e : ∀ U, ∫⁻ k : I.l.K, ‖M (mm (mt B ((k : GA D B)⁻¹)) (mm (XU d hn x₀ h U) (bl hn 1 y 0 1)))‖ₑ * ‖η y‖ₑ ∂I.νK =
        (∫⁻ k : I.l.K, ‖M (mm (mt B ((k : GA D B)⁻¹)) (mm (XU d hn x₀ h U) (bl hn 1 y 0 1)))‖ₑ ∂I.νK) * ‖η y‖ₑ := fun U =>
      lintegral_mul_const' _ _ enorm_ne_top
    simp only [e]
    rw [lintegral_mul_const' _ _ enorm_ne_top, inner_eq hIkL hJn hn I hθ hM hM0 x₀ h y]
    gcongr
    rw [enorm_le_iff_norm_le]
    have h3 := hNd (jn hn (ww W x₀ h) (mm (ww W x₀ h) y + 0))
    rw [jn_first] at h3
    exact h3.trans (Complex.re_le_norm _)
  rw [hasFiniteIntegral_iff_enorm]
  calc ∫⁻ p, ‖core hn I x₀ Φ η p‖ₑ ∂(I.νK.prod (Q0 I μ))
      ≤ ∫⁻ p, F p ∂(I.νK.prod (Q0 I μ)) := lintegral_mono hle
    _ = ∫⁻ y, ∫⁻ h, ∫⁻ U, ∫⁻ k : I.l.K, F (k, h, U, y) ∂I.νK ∂I.μ₁ ∂I.m ∂μ :=
        (hFub I.l.K (GA D W) (Mx D t n) (Mx D W.rank t) I.νK I.m I.μ₁ μ).2 F hFm
    _ ≤ ∫⁻ y, ∫⁻ h, ‖N (ww W x₀ h)‖ₑ * ‖η y‖ₑ ∂I.m ∂μ :=
        lintegral_mono fun y => lintegral_mono fun h => hin y h
    _ = (∫⁻ h, ‖N (ww W x₀ h)‖ₑ ∂I.m) * ∫⁻ y, ‖η y‖ₑ ∂μ := by
        simp only [lintegral_mul_const' _ _ enorm_ne_top]
        rw [lintegral_const_mul' _ _ hN'.ne]
    _ < ⊤ := ENNReal.mul_lt_top hN' hη'

end GlobalTheory.CompanionTheory.ColumnSplitting

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ScalarSectionExistsStatement
section
open ResidueKilled.Tr
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.scalar_section_exists : TScal := by
  first | exact @GlobalTheory.CompanionTheory.ScalWall.tScal | exact GlobalTheory.CompanionTheory.ScalWall.tScal | (intros; apply GlobalTheory.CompanionTheory.ScalWall.tScal <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SecondColumnsMulBlockDiagonal
section
noncomputable section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS
open IsDedekindDomain NumberField
open GlobalTheory.RegSch (ikS projS Lvl)
open PositivityTheory.Rg.Rsw PositivityTheory.Rg.Rsw.L
open GlobalTheory.CompanionTheory.ColumnSplitting
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.ColumnSplitting.Cov

variable {D : D7} {n t : ℕ} {B W : HSp D}

theorem jn_bl {a r : ℕ} (hn : r + t = n) (w : Mx D a r) (v : Mx D a t) (g : Mx D t t) :
    mm (jn hn w v) (bl hn 1 0 0 g) = jn hn w (mm v g) := by
  simp only [jn, bl, mm]
  rw [Matrix.submatrix_mul_equiv, Matrix.fromCols_mul_fromBlocks]
  simp

theorem jn_c (hn : W.rank + t = n) {a : ℕ} (U : Mx D a n) : jn hn (c1 hn U) (c2 hn U) = U := by
  ext i j
  obtain ⟨k, rfl⟩ := (finSumFinEquiv.trans (finCongr hn)).surjective j
  rcases k with k | k <;> simp [jn, c1, c2]

theorem first_columns_join_eq (hn : W.rank + t = n) {a : ℕ} (w : Mx D a W.rank) (v : Mx D a t) : c1 hn (jn hn w v) = w := by
  ext i j
  simp [jn, c1]

theorem second_columns_join_eq (hn : W.rank + t = n) {a : ℕ} (w : Mx D a W.rank) (v : Mx D a t) : c2 hn (jn hn w v) = v := by
  ext i j
  simp [jn, c2]

theorem first_columns_mul_block_diagonal (hn : W.rank + t = n) {a : ℕ} (U : Mx D a n) (g : Mx D t t) :
    c1 hn (mm U (bl hn 1 0 0 g)) = c1 hn U := by
  conv_lhs => rw [← jn_c hn U, jn_bl, first_columns_join_eq]

theorem second_columns_mul_block_diagonal (hn : W.rank + t = n) {a : ℕ} (U : Mx D a n) (g : Mx D t t) :
    c2 hn (mm U (bl hn 1 0 0 g)) = mm (c2 hn U) g := by
  conv_lhs => rw [← jn_c hn U, jn_bl, second_columns_join_eq]

theorem map_char {A : Type} [AddCommGroup A] [TopologicalSpace A] [IsTopologicalAddGroup A] [LocallyCompactSpace A]
    [SecondCountableTopology A] [T2Space A]
    [MeasurableSpace A] [BorelSpace A] (μ : Measure A) [μ.IsAddHaarMeasure] (φ : A ≃ₜ+ A) (c : ℝ≥0) (hc0 : c ≠ 0)
    (hc : addEquivAddHaarChar φ = c) : μ.map φ = c⁻¹ • μ := by
  haveI : TopologicalSpace.PseudoMetrizableSpace A := inferInstance
  haveI : μ.Regular := Measure.Regular.of_sigmaCompactSpace_of_isLocallyFiniteMeasure _
  have h4 := addEquivAddHaarChar_smul_map μ φ
  rw [hc] at h4
  conv_rhs => rw [← h4]
  rw [smul_smul, inv_mul_cancel₀ hc0, one_smul]

set_option maxHeartbeats 1200000 in

theorem map_right (a b : ℕ) (μ : Measure (Mx D a b)) (hμ : μ.IsAddHaarMeasure) (g : GL (Fin b) (AE D)) :
    μ.map (fun y => mm y g.1) =
      ((absA D (Matrix.GeneralLinearGroup.det g))⁻¹ ^ a : ℝ≥0) • μ := by
  haveI := hμ
  obtain ⟨i1, i2, i3, i4, -, -⟩ := lattice_Mx D a b
  haveI : IsTopologicalAddGroup (Mx D a b) := i1
  haveI : LocallyCompactSpace (Mx D a b) := i2
  haveI : SecondCountableTopology (Mx D a b) := i3
  haveI : T2Space (Mx D a b) := i4
  haveI : BorelSpace (Mx D a b) := ⟨rfl⟩
  haveI := isTopologicalRing_tens (F := D.host.F) (E := D.host.E) (R := AF D.host.F)
  have hc : addEquivAddHaarChar (GlobalTheory.ModuLR.lrCE (1 : GL (Fin a) (AE D)) g) = absA D (Matrix.GeneralLinearGroup.det g) ^ a := by
    have := GlobalTheory.ResidueEisenstein.ModMat.addEquivAddHaarChar_lrCE D.host.F D.host.E D.sp.cm.sig (isCMExt_host D) a b
      (1 : GL (Fin a) (AE D)) g
    simpa using this
  have hA : absA D (Matrix.GeneralLinearGroup.det g) ≠ 0 := (GlobalTheory.CompanionTheory.IwaAd.absA_pos _).ne'
  have e : (fun y : Mx D a b => mm y g.1) = GlobalTheory.ModuLR.lrCE (1 : GL (Fin a) (AE D)) g := by
    funext y
    rw [GlobalTheory.ModuLR.lrCE_apply, Units.val_one, Matrix.one_mul]
  rw [e, inv_pow]
  exact map_char μ _ _ (pow_ne_zero _ hA) hc

end GlobalTheory.CompanionTheory.ColumnSplitting.Cov

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SectionInvariantHeisenbergWeylStatement
section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.section_invariant_heisenberg_weyl : ∀ {D : D7} {n ρ p : ℕ} {hn : ρ + p = n} (M : Maps D hn) (χ : (AE D)ˣ →* Circle) (s : ℂ) (f : G D n → ℂ), IsLaw χ s f → ∀ (x : Mx D ρ p) (h : G D n), f (M.w * M.nzx 0 x * h) = f (M.w * h) := by
  first | exact @GlobalTheory.CompanionTheory.FJE.LawW.law_w | exact GlobalTheory.CompanionTheory.FJE.LawW.law_w | (intros; apply GlobalTheory.CompanionTheory.FJE.LawW.law_w <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ThetaTotalOfHeckeEtaStatement
section
open PositivityTheory.Rg.Rsw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.theta_total_of_hecke_eta : HeckeEta → ThTotal := by
  first | exact @GlobalTheory.CompanionTheory.ThTot.thTotal | exact GlobalTheory.CompanionTheory.ThTot.thTotal | (intros; apply GlobalTheory.CompanionTheory.ThTot.thTotal <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TypedSpaceApproximationStatement
section
open scoped Classical
open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.Rs PositivityTheory.Rg.BcB.SpectralAccumulation
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.typed_space_approximation : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (N : ℕ) [MeasurableSpace (GA E N)] [BorelSpace (GA E N)]
  (μ : Measure (GA E N)) [μ.IsHaarMeasure] (K : Subgroup (GL (Fin N) (Af E))) (W : Submodule ℂ (Kinf E N → ℂ))
  (R ε δ : ℝ) (α : GA E N → ℂ) (F : Set (GA E N)), IsOpen (K : Set (GL (Fin N) (Af E))) → FiniteDimensional ℂ W → 0 < ε →
  Continuous α → HasCompactSupport α → 0 < δ → IsFundamentalDomain (latticeGL E N) F μ →
  ∃ Ω : Set (GA E N), IsCompact Ω ∧ ∀ (V : Submodule ℂ (Sm E N)) (ψ : Sm E N), IsDiscrete V → ψ ∈ V → TypeB K W ψ →
    InfBdd R V → (∀ r, 0 < r → r < N → ∀ c ∈ ExpV r V, pE E N r c ≤ -ε * (r * ((N : ℝ) - r))) →
    (∃ s : ℂ, δ ≤ ‖s‖ ∧ ∀ x, ∫ y, α y * ψ.1 (x * y) ∂μ = s * ψ.1 x) →
    (∫⁻ x in F, ‖ψ.1 x‖ₑ ^ 2 ∂μ) = 1 → 1 ≤ 2 * ∫⁻ x in Ω, ‖ψ.1 x‖ₑ ^ 2 ∂μ := by
  first | exact @GlobalTheory.CompanionTheory.Conc.conc | exact GlobalTheory.CompanionTheory.Conc.conc | (intros; apply GlobalTheory.CompanionTheory.Conc.conc <;> assumption)
end

