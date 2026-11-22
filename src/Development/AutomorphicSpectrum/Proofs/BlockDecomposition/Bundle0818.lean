import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0813
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0789
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0812
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2005
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2006
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0505
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0150
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0145
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0751
import Development.WeilBound.CoreStatements.AutomorphicKernels.UnitarySchrodingerModel.Bundle0001
import Development.WeilBound.CoreStatements.AutomorphicKernels.UnitarySchrodingerModel.CoefDataExists
import Development.WeilBound.CoreStatements.PublishedTheorems.SiegelWeilSchrodinger.SiegelWeilUnitarySchrodingerLit
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0370
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0375
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.Bundle0003
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0539
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NondegenerateCharacterCellFactorization
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0744
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.AdelicConjTransposeBlockMatrixTwoByTwoFin
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle0078
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0536
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0506
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0728
import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.ThetaIdempotents.HeckeEta
import Formalism.LocalToGlobal.BesselHermitianTheta.Bundle0003
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1870
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0771
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PartialConstantTermBound

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FlatNodeFunction
section
open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec GlobalTheory.CompanionTheory.CTFin PositivityTheory.Rg.Rs PositivityTheory.Rg.Rs.InducedTensorMap
open PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation GlobalTheory.CompanionTheory.LimV
open scoped ContDiff

namespace GlobalTheory.CompanionTheory.LimV.NodeFlat

theorem flatFn_nodeFn : ∀ {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {r s : ℕ} (e₁ : GA E r → ℂ) (e₂ : GA E s → ℂ), FlatFn e₁ → FlatFn e₂ → FlatFn (nodeFn e₁ e₂) := by
  intro E _ _ _ r s e₁ e₂ h₁ h₂
  have ap : ∀ (u : BlockIx (r + s) r → Ad E) (m : GA E r × GA E s) (k : Kinf E (r + s))
      (c : GL (Fin (r + s)) (Af E)), c ∈ KO E (r + s) →
      nodeFn e₁ e₂ (unip u * lev (Ad E) r s m * cf (r + s) k c) = e₁ m.1 * e₂ m.2 :=
    fun u m k c hc => GlobalTheory.T.node_function_levi_decomposition e₁ e₂ h₁ h₂ u m k c hc
  have hleft : ∀ (v : BlockIx (r + s) r → Ad E) (x : GA E (r + s)),
      nodeFn e₁ e₂ (unip v * x) = nodeFn e₁ e₂ x := by
    intro v x
    obtain ⟨u, m, k, c, hc, rfl⟩ := exists_iw x
    rw [← mul_assoc, ← mul_assoc, ← PositivityTheory.Rg.Rs.InducedTensorMap.D.unip_add', ap _ _ _ _ hc, ap _ _ _ _ hc]
  have hright : ∀ (x : GA E (r + s)) (k' : Kinf E (r + s)), ∀ c' ∈ KO E (r + s),
      nodeFn e₁ e₂ (x * cf (r + s) k' c') = nodeFn e₁ e₂ x := by
    intro x k' c' hc'
    obtain ⟨u, m, k, c, hc, rfl⟩ := exists_iw x
    rw [mul_assoc _ (cf (r + s) k c), PositivityTheory.Rg.Rs.InducedTensorMap.cf_mul,
      ap _ _ _ _ ((KO E (r + s)).mul_mem hc hc'), ap _ _ _ _ hc]
  have key : ∀ m : GA E r × GA E s,
      ContDiffAt ℝ ∞ (chart (nodeFn e₁ e₂) (lev (Ad E) r s m)) (oneL E (r + s)) := by
    intro m
    obtain ⟨b₁, b₂, κ, u, hb₁, hb₂, hκ, hb₁1, hb₂1, hκ1, hloc⟩ := exists_local E r s
    have c₁ : ContDiffAt ℝ ∞ (fun y => e₁ (m.1 * infGL E r (b₁ y))) (oneL E (r + s)) := by
      have := (contDiffAt_chart h₁.sm m.1 (val_mem_invSet (b₁ (oneL E (r + s))))).comp (oneL E (r + s)) hb₁
      simpa only [Function.comp_def, chart_val] using this
    have c₂ : ContDiffAt ℝ ∞ (fun y => e₂ (m.2 * infGL E s (b₂ y))) (oneL E (r + s)) := by
      have := (contDiffAt_chart h₂.sm m.2 (val_mem_invSet (b₂ (oneL E (r + s))))).comp (oneL E (r + s)) hb₂
      simpa only [Function.comp_def, chart_val] using this
    refine ContDiffAt.congr_of_eventuallyEq (c₁.mul c₂) ?_
    filter_upwards [hloc] with y hy
    have hyw : y = toL (unip (u y) * lev (Cinf E) r s (b₁ y, b₂ y) * Unitary.toUnits (κ y)).val := by
      show y = toL ((unip (u y) * lev (Cinf E) r s (b₁ y, b₂ y)).val * (κ y).1)
      rw [← hy]
      rfl
    conv_lhs => rw [hyw, chart_val]
    obtain ⟨v, hv⟩ := lev_mul_infGL m (u y) (b₁ y) (b₂ y) (κ y)
    rw [hv, ap _ _ _ _ ((KO E (r + s)).one_mem)]
  refine ⟨fun x => ?_, hright, ?_⟩
  · obtain ⟨u, m, k, c, hc, rfl⟩ := exists_iw x
    rw [ap _ _ _ _ hc]
    exact mul_ne_zero (h₁.ne _) (h₂.ne _)
  refine GlobalTheory.DiscSMO.mem_Sm_of_one fun x => ?_
  obtain ⟨u, m, k, g, hg, rfl⟩ := exists_iw x
  have e1 : chart (nodeFn e₁ e₂) (unip u * lev (Ad E) r s m * cf (r + s) k g) =
      chart (nodeFn e₁ e₂) (lev (Ad E) r s m * cf (r + s) k g) := by
    funext z
    unfold chart
    split_ifs
    · simp only [mul_assoc]
      exact hleft u _
    · rfl
  rw [e1, cf, infGL_comm, ← mul_assoc]
  refine GlobalTheory.DiscSMO.contDiffAt_chart_mul ?_
  rw [← chart_rt_fin]
  have e2 : (fun x => (fun x => nodeFn e₁ e₂ (x * infGL E (r + s) (Unitary.toUnits k))) (x * finGL E (r + s) g)) =
      nodeFn e₁ e₂ := by
    funext z
    show nodeFn e₁ e₂ (z * finGL E (r + s) g * infGL E (r + s) (Unitary.toUnits k)) = nodeFn e₁ e₂ z
    rw [mul_assoc, ← infGL_comm]
    exact hright z k g hg
  rw [e2]
  exact key m

end GlobalTheory.CompanionTheory.LimV.NodeFlat
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermitianMeasureConjugation
section
noncomputable section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC

namespace GlobalTheory.CompanionTheory.CgMod

section Abstract

variable {M : Type} [AddCommGroup M] [TopologicalSpace M]

def restr (S : AddSubgroup M) (U : M ≃ₜ+ M) (hU : ∀ s ∈ S, U s ∈ S) (hU' : ∀ s ∈ S, U.symm s ∈ S) : S ≃ₜ+ S where
  toFun s := ⟨U s.1, hU _ s.2⟩
  invFun s := ⟨U.symm s.1, hU' _ s.2⟩
  left_inv s := Subtype.ext (U.left_inv s.1)
  right_inv s := Subtype.ext (U.right_inv s.1)
  map_add' x y := Subtype.ext (map_add U x.1 y.1)
  continuous_toFun := (U.continuous.comp continuous_subtype_val).subtype_mk _
  continuous_invFun := (U.symm.continuous.comp continuous_subtype_val).subtype_mk _

def dbl [IsTopologicalAddGroup M] (S : AddSubgroup M) (P : M →+ M) (hPc : Continuous P) (hPm : ∀ x, P x ∈ S)
    (hPs : ∀ s ∈ S, P s = s) (L : M ≃ₜ+ M) (h1 : ∀ s ∈ S, P (L s) = 0) (h2 : ∀ s ∈ S, P (L.symm s) = 0)
    (h3 : ∀ x, P x + L (P (L.symm x)) = x) : (S × S) ≃ₜ+ M where
  toFun p := p.1.1 + L p.2.1
  invFun x := (⟨P x, hPm x⟩, ⟨P (L.symm x), hPm _⟩)
  left_inv p := by
    refine Prod.ext (Subtype.ext ?_) (Subtype.ext ?_)
    · change P (p.1.1 + L p.2.1) = p.1.1
      rw [map_add, hPs _ p.1.2, h1 _ p.2.2, add_zero]
    · change P (L.symm (p.1.1 + L p.2.1)) = p.2.1
      have hl : L.symm (L p.2.1) = p.2.1 := L.left_inv _
      rw [map_add, map_add, h2 _ p.1.2, zero_add, hl, hPs _ p.2.2]
  right_inv x := h3 x
  map_add' p q := by
    change (p.1.1 + q.1.1) + L (p.2.1 + q.2.1) = (p.1.1 + L p.2.1) + (q.1.1 + L q.2.1)
    rw [map_add]; abel
  continuous_toFun :=
    (continuous_subtype_val.comp continuous_fst).add (L.continuous.comp (continuous_subtype_val.comp continuous_snd))
  continuous_invFun := (hPc.subtype_mk _).prodMk ((hPc.comp L.symm.continuous).subtype_mk _)

theorem char_sq [IsTopologicalAddGroup M] [LocallyCompactSpace M] [SecondCountableTopology M] [T2Space M]
    [MeasurableSpace M] [BorelSpace M] (S : AddSubgroup M) [LocallyCompactSpace S] (P : M →+ M)
    (hPc : Continuous P) (hPm : ∀ x, P x ∈ S) (hPs : ∀ s ∈ S, P s = s) (L : M ≃ₜ+ M)
    (h1 : ∀ s ∈ S, P (L s) = 0) (h2 : ∀ s ∈ S, P (L.symm s) = 0) (h3 : ∀ x, P x + L (P (L.symm x)) = x)
    (U : M ≃ₜ+ M) (hUL : ∀ x, U (L x) = L (U x)) (hU : ∀ s ∈ S, U s ∈ S) (hU' : ∀ s ∈ S, U.symm s ∈ S) :
    addEquivAddHaarChar (restr S U hU hU') ^ 2 = addEquivAddHaarChar U := by
  haveI : SecondCountableTopology S := Topology.IsInducing.subtypeVal.secondCountableTopology
  haveI : T2Space S := Topology.IsEmbedding.subtypeVal.t2Space
  set Ψ := dbl S P hPc hPm hPs L h1 h2 h3 with hΨ
  set T := restr S U hU hU' with hT
  have e : ((Ψ.symm.trans (GlobalTheory.ModuLR.prodCE T T)).trans Ψ) = U := by
    ext x
    obtain ⟨p, rfl⟩ := Ψ.surjective x
    change Ψ (GlobalTheory.ModuLR.prodCE T T (Ψ.symm (Ψ p))) = U (Ψ p)
    have hl : Ψ.symm (Ψ p) = p := Ψ.left_inv p
    rw [hl]
    change U p.1.1 + L (U p.2.1) = U (p.1.1 + L p.2.1)
    rw [map_add, hUL]
  rw [sq, ← GlobalTheory.T.addEquivAddHaarChar_prodCongr, ← GlobalTheory.ModuLR.addEquivAddHaarChar_transport Ψ (GlobalTheory.ModuLR.prodCE T T), e]

end Abstract

theorem exists_anti {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (h : IsCMExt F E σ) : ∃ δ : E, δ ≠ 0 ∧ σ δ = -δ := by
  obtain ⟨-, hc, -, hs⟩ := h
  obtain ⟨v⟩ : Nonempty (NumberField.InfinitePlace E) := inferInstance
  have hv : v.IsComplex := hc.isComplex v
  have hsq : ∀ x, σ (σ x) = x := fun x => v.embedding.injective (by rw [hs, hs]; simp)
  have hx : ∃ x, σ x ≠ x := by
    by_contra hn
    push_neg at hn
    apply NumberField.InfinitePlace.not_isReal_iff_isComplex.2 hv
    rw [NumberField.InfinitePlace.isReal_iff, NumberField.ComplexEmbedding.isReal_iff]
    ext x
    have := hs v.embedding x
    rw [hn] at this
    simpa [NumberField.ComplexEmbedding.conjugate_coe_eq] using this.symm
  obtain ⟨x, hx⟩ := hx
  exact ⟨x - σ x, sub_ne_zero.2 (Ne.symm hx), by rw [map_sub, hsq]; abel⟩

open GlobalTheory.CompanionTheory.IwaAd GlobalTheory.CompanionTheory.HermVol

variable {D : D7} {n : ℕ}

theorem cA_incA (D : D7) (x : D.host.E) : cA D (incA D x) = incA D (D.sp.cm.sig x) := by
  simp [cA, sigR, incA, inclR]

theorem hermPart_anti {c : AE D} (hc : cA D c = -c) {s : Mx D n n} (hs : s ∈ hermA D n) :
    hermPart D n (c • s) = 0 := by
  have h : adj s = s := hs
  rw [hermPart, adj_smul, h, hc, neg_smul, add_neg_cancel, smul_zero]

theorem hermPart_split {d e : AE D} (he : cA D e = -e) (hde : d * e = 1) (x : Mx D n n) :
    hermPart D n x + d • hermPart D n (e • x) = x := by
  have h : d * half D * e = half D := by rw [mul_comm d, mul_assoc, hde, mul_one]
  rw [hermPart, hermPart, adj_smul, he, neg_smul, ← sub_eq_add_neg, ← smul_sub, smul_smul, smul_smul, h, smul_add,
    smul_sub]
  exact (add_add_sub_cancel _ _ _).trans (half_smul_add x)

set_option synthInstance.maxHeartbeats 400000 in

def mulCE (d e : AE D) (hde : d * e = 1) : Mx D n n ≃ₜ+ Mx D n n where
  toFun x := d • x
  invFun x := e • x
  left_inv x := by
    change e • d • x = x
    rw [smul_smul, mul_comm, hde, one_smul]
  right_inv x := by
    change d • e • x = x
    rw [smul_smul, hde, one_smul]
  map_add' := smul_add d
  continuous_toFun := continuous_const_smul d
  continuous_invFun := continuous_const_smul e

def hermPartHom (D : D7) (n : ℕ) : Mx D n n →+ Mx D n n := AddMonoidHom.mk' (hermPart D n) hermPart_add

set_option maxHeartbeats 400000 in
theorem val_det_ad_inv (a : GL (Fin n) (AE D)) :
    ((Matrix.GeneralLinearGroup.det ((ad a)⁻¹ : GL (Fin n) (AE D)) : (AE D)ˣ) : AE D) = cA D (Matrix.GeneralLinearGroup.det a : (AE D)ˣ) := by
  change (adj a.1 : Mx D n n).det = cA D a.1.det
  rw [adj, Matrix.det_transpose, RingHom.map_det]
  rfl

theorem absA_det_ad_inv (a : GL (Fin n) (AE D)) :
    absA D (Matrix.GeneralLinearGroup.det ((ad a)⁻¹ : GL (Fin n) (AE D)) : (AE D)ˣ) =
      absA D (Matrix.GeneralLinearGroup.det a : (AE D)ˣ) := by
  have h : (Matrix.GeneralLinearGroup.det ((ad a)⁻¹ : GL (Fin n) (AE D)) : (AE D)ˣ) =
      conjUnit D.sp.cm.sig (Matrix.GeneralLinearGroup.det a : (AE D)ˣ) := Units.ext (val_det_ad_inv a)
  rw [h]
  exact GlobalTheory.DiagThetaRule.absA_conj D _

theorem exists_anti_units (D : D7) : ∃ d e : AE D, d * e = 1 ∧ cA D d = -d ∧ cA D e = -e := by
  obtain ⟨δ, hδ, hσ⟩ := exists_anti _ (isCMExt_host D)
  refine ⟨incA D δ, incA D δ⁻¹, ?_, ?_, ?_⟩
  · rw [← map_mul, mul_inv_cancel₀ hδ, map_one]
  · rw [cA_incA, hσ, map_neg]
  · rw [cA_incA, map_inv₀, hσ, inv_neg, map_neg]

theorem lr_herm (a : GL (Fin n) (AE D)) : ∀ s ∈ hermA D n, GlobalTheory.ModuLR.lrCE a (ad a)⁻¹ s ∈ hermA D n :=
  fun s hs => (cg a ⟨s, hs⟩).2

theorem lr_herm_symm (a : GL (Fin n) (AE D)) :
    ∀ s ∈ hermA D n, (GlobalTheory.ModuLR.lrCE a (ad a)⁻¹).symm s ∈ hermA D n :=
  fun s hs => (cg a⁻¹ ⟨s, hs⟩).2

theorem lr_smul (a : GL (Fin n) (AE D)) (d e : AE D) (hde : d * e = 1) (x : Mx D n n) :
    GlobalTheory.ModuLR.lrCE a (ad a)⁻¹ (mulCE d e hde x) = mulCE d e hde (GlobalTheory.ModuLR.lrCE a (ad a)⁻¹ x) := by
  change a.1 * (d • x) * ((ad a)⁻¹ : GL (Fin n) (AE D)).1 = d • (a.1 * x * ((ad a)⁻¹ : GL (Fin n) (AE D)).1)
  rw [Matrix.mul_smul, Matrix.smul_mul]

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1000000 in
theorem integral_cg : ∀ (D : D7) (n : ℕ) (lam : Measure (hermA D n)), lam.IsAddHaarMeasure → ∀ (a : GL (Fin n) (AE D)) (f : hermA D n → ℂ), ∫ c, f (GlobalTheory.CompanionTheory.IwaAd.cg a c) ∂lam = npow (absA D (Matrix.GeneralLinearGroup.det a)) (-(n : ℂ)) * ∫ c, f c ∂lam := by
  intro D n lam hlam a f
  obtain ⟨i1, i2, i3, i4, -, -⟩ := lattice_Mx D n n
  haveI : IsTopologicalAddGroup (Mx D n n) := i1
  haveI : LocallyCompactSpace (Mx D n n) := i2
  haveI : SecondCountableTopology (Mx D n n) := i3
  haveI : T2Space (Mx D n n) := i4
  haveI : BorelSpace (Mx D n n) := ⟨rfl⟩
  haveI : SecondCountableTopology (hermA D n) := Topology.IsInducing.subtypeVal.secondCountableTopology
  haveI : T2Space (hermA D n) := Topology.IsEmbedding.subtypeVal.t2Space
  haveI : LocallyCompactSpace (hermA D n) := (isClosed_hermA (D := D) (r := n)).isClosedEmbedding_subtypeVal.locallyCompactSpace
  obtain ⟨d, e, hde, hd, he⟩ := exists_anti_units D
  have hsq := char_sq (hermA D n) (hermPartHom D n) continuous_hermPart hermPart_mem
    (fun s hs => hermPart_of_mem hs) (mulCE d e hde)
    (fun s hs => hermPart_anti hd hs) (fun s hs => hermPart_anti he hs)
    (fun x => hermPart_split he hde x) (GlobalTheory.ModuLR.lrCE a (ad a)⁻¹)
    (lr_smul a d e hde) (lr_herm a) (lr_herm_symm a)
  have hlr : addEquivAddHaarChar (GlobalTheory.ModuLR.lrCE a (ad a)⁻¹) =
      absA D (Matrix.GeneralLinearGroup.det a : (AE D)ˣ) ^ n * absA D (Matrix.GeneralLinearGroup.det a : (AE D)ˣ) ^ n := by
    have h := GlobalTheory.ResidueEisenstein.ModMat.addEquivAddHaarChar_lrCE _ _ D.sp.cm.sig (isCMExt_host D) n n a (ad a)⁻¹
    rw [h]
    exact congrArg (fun t => absA D (Matrix.GeneralLinearGroup.det a : (AE D)ˣ) ^ n * t ^ n) (absA_det_ad_inv a)
  have hT : addEquivAddHaarChar (restr (hermA D n) _ (lr_herm a) (lr_herm_symm a)) =
      absA D (Matrix.GeneralLinearGroup.det a : (AE D)ˣ) ^ n :=
    (pow_left_inj₀ zero_le zero_le two_ne_zero).1 ((hsq.trans hlr).trans (sq _).symm)
  have h : ∫ c, f (cg a c) ∂lam = _ := integral_comp_char lam (restr (hermA D n) _ (lr_herm a) (lr_herm_symm a)) f
  rw [h, hT, npow_neg_nat (absA_pos _) n]

end GlobalTheory.CompanionTheory.CgMod
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IntegralShiftHerm
section
noncomputable section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
attribute [local instance] Formalism.BasicNotions.Host.cmStar

open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
namespace GlobalTheory.CompanionTheory.IwaAd
open GlobalTheory.StdUnn GlobalTheory.StdUnn.Model GlobalTheory.StdUnn.LeftInvSect PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS
variable {D : D7} {n : ℕ}
theorem integral_mul_right (m : ℕ) (μ : Measure (Mx D m n)) (hμ : μ.IsAddHaarMeasure) (a : GL (Fin n) (AE D))
    (f : Mx D m n → ℂ) :
    ∫ y, f (HMul.hMul y a.1 : Mx D m n) ∂μ = npow (absA D (Matrix.GeneralLinearGroup.det a)) (-(m : ℂ)) * ∫ y, f y ∂μ := by
  obtain ⟨i1, i2, i3, i4, -, -⟩ := lattice_Mx D m n
  haveI : IsTopologicalAddGroup (Mx D m n) := i1
  haveI : LocallyCompactSpace (Mx D m n) := i2
  haveI : SecondCountableTopology (Mx D m n) := i3
  haveI : T2Space (Mx D m n) := i4
  haveI : BorelSpace (Mx D m n) := ⟨rfl⟩
  haveI := isTopologicalRing_tens (F := D.host.F) (E := D.host.E) (R := AF D.host.F)
  let φ := GlobalTheory.ModuLR.lrCE (1 : GL (Fin m) (AE D)) a
  have hc : addEquivAddHaarChar φ = absA D (Matrix.GeneralLinearGroup.det a) ^ m := by
    have := GlobalTheory.ResidueEisenstein.ModMat.addEquivAddHaarChar_lrCE D.host.F D.host.E D.sp.cm.sig (isCMExt_host D) m n
      (1 : GL (Fin m) (AE D)) a
    simpa using this
  have hA : 0 < absA D (Matrix.GeneralLinearGroup.det a) := absA_pos _
  have e : ∀ y : Mx D m n, (HMul.hMul y a.1 : Mx D m n) = φ y := fun y => by
    simp only [φ]
    rw [GlobalTheory.ModuLR.lrCE_apply, Units.val_one, Matrix.one_mul]
  have key : ∫ y, f (φ y) ∂μ = ((((addEquivAddHaarChar φ)⁻¹ : ℝ≥0) : ℝ) : ℂ) * ∫ y, f y ∂μ :=
    integral_comp_char μ φ f
  rw [hc, npow_neg_nat hA] at key
  simp only [e]
  exact key

theorem integral_shift {A : Type} [AddCommGroup A] [TopologicalSpace A] [IsTopologicalAddGroup A]
    [MeasurableSpace A] [BorelSpace A] (μ : Measure A) [μ.IsAddHaarMeasure] (f : A → ℂ) (g : A) :
    ∫ x, f (x - g) ∂μ = ∫ x, f x ∂μ :=
  integral_sub_right_eq_self f g

theorem integral_shift_herm (lam : Measure (hermA D n)) (hl : lam.IsAddHaarMeasure) (f : hermA D n → ℂ) (g : hermA D n) :
    ∫ x, f (x - g) ∂lam = ∫ x, f x ∂lam := by
  obtain ⟨i1, -, -, -, -, -⟩ := lattice_Mx D n n
  haveI : IsTopologicalAddGroup (Mx D n n) := i1
  haveI : BorelSpace (Mx D n n) := ⟨rfl⟩
  exact integral_shift lam f g

theorem halfTr_add (x y : AE D) : halfTr (x + y) = halfTr x + halfTr y := by
  simp [halfTr, mul_add]

theorem halfTr_neg (x : AE D) : halfTr (-x) = -halfTr x := by
  simp [halfTr]

theorem inner_mul_right (V : HSp D) {r : ℕ} (x : Mx D V.rank r) (s : Mx D r r) :
    StdUnn.inner V (HMul.hMul x s : Mx D V.rank r) (HMul.hMul x s : Mx D V.rank r) =
      adj s * StdUnn.inner V x x * s := by
  unfold StdUnn.inner
  rw [adj_mul]
  simp only [Matrix.mul_assoc]

theorem trace_cg (a : GL (Fin n) (AE D)) (c Q : Mx D n n) :
    Matrix.trace (a.1 * c * adj a.1 * (adj (a⁻¹).1 * Q * (a⁻¹).1)) = Matrix.trace (c * Q) := by
  have h1 : a.1 * c * adj a.1 * (adj (a⁻¹).1 * Q * (a⁻¹).1) = a.1 * (c * Q * (a⁻¹).1) := by
    calc _ = a.1 * c * (adj a.1 * adj (a⁻¹).1) * Q * (a⁻¹).1 := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [adj_mul_adj_inv]; simp only [Matrix.mul_assoc, Matrix.mul_one]
  rw [h1, Matrix.trace_mul_comm, Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.mul_one]

theorem trace_beta (a : GL (Fin n) (AE D)) (B c : Mx D n n) :
    Matrix.trace (B * (a.1 * c * adj a.1)) = Matrix.trace (adj a.1 * B * a.1 * c) := by
  rw [← Matrix.mul_assoc, Matrix.trace_mul_comm]
  simp only [Matrix.mul_assoc]

theorem weil_pt {ψ : AddChar (AF D.host.F) ℂ} {χ : (AE D)ˣ →* Circle} {θ : InfFam D} {V : HSp D}
    {μ : Measure (Mx D V.rank n)} {ω : G D n →* Module.End ℂ (schwartzA θ V.rank n)} (hω : IsWeilSch ψ χ θ V μ ω)
    (a : GL (Fin n) (AE D)) {m u : G D n} (hm : mat m = blk4 a.1 0 0 (adj (a⁻¹).1)) {b1 : Mx D n n}
    (hu : mat u = blk4 1 b1 0 1) (φ : schwartzA θ V.rank n) (y : Mx D V.rank n) :
    (ω (m * u) φ).1 y = (χ (Matrix.GeneralLinearGroup.det a) : ℂ) *
      npow (absA D (Matrix.GeneralLinearGroup.det a)) ((V.rank : ℂ) / 2) *
      (ψ (halfTr (Matrix.trace (b1 * StdUnn.inner V (HMul.hMul y a.1 : Mx D V.rank n) (HMul.hMul y a.1 : Mx D V.rank n)))) *
        φ.1 (HMul.hMul y a.1 : Mx D V.rank n)) := by
  rw [map_mul, Module.End.mul_apply, hω.levi m a hm, hω.unip u b1 hu]

theorem jt_step {ψ : AddChar (AF D.host.F) ℂ} {χ : (AE D)ˣ →* Circle} {θ : InfFam D} {V : HSp D}
    {μ : Measure (Mx D V.rank n)} {ω : G D n →* Module.End ℂ (schwartzA θ V.rank n)} (hω : IsWeilSch ψ χ θ V μ ω)
    (hμ : μ.IsAddHaarMeasure) (a : GL (Fin n) (AE D)) {m u : G D n} (hm : mat m = blk4 a.1 0 0 (adj (a⁻¹).1))
    {b1 : hermA D n} (hu : mat u = blk4 1 b1.1 0 1) (φ : schwartzA θ V.rank n) (c : hermA D n) :
    Jt ψ V μ (ω (m * u) φ).1 (cg a c) = (χ (Matrix.GeneralLinearGroup.det a) : ℂ) *
      npow (absA D (Matrix.GeneralLinearGroup.det a)) ((V.rank : ℂ) / 2) *
      (npow (absA D (Matrix.GeneralLinearGroup.det a)) (-(V.rank : ℂ)) * Jt ψ V μ φ.1 (c + b1)) := by
  set F : Mx D V.rank n → ℂ := fun y => φ.1 y * ψ (halfTr (Matrix.trace (HMul.hMul (c + b1).1 (StdUnn.inner V y y) : Mx D n n))) with hF
  have hpt : ∀ y : Mx D V.rank n, (ω (m * u) φ).1 y *
      ψ (halfTr (Matrix.trace (HMul.hMul (cg a c).1 (StdUnn.inner V y y) : Mx D n n))) =
      ((χ (Matrix.GeneralLinearGroup.det a) : ℂ) * npow (absA D (Matrix.GeneralLinearGroup.det a)) ((V.rank : ℂ) / 2)) *
        F (HMul.hMul y a.1 : Mx D V.rank n) := by
    intro y
    have hy : y = (HMul.hMul (HMul.hMul y a.1 : Mx D V.rank n) (a⁻¹).1 : Mx D V.rank n) := by
      rw [Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.mul_one]
    set Y : Mx D V.rank n := HMul.hMul y a.1 with hY
    have e1 : Matrix.trace (HMul.hMul (cg a c).1 (StdUnn.inner V y y) : Mx D n n) =
        Matrix.trace (c.1 * StdUnn.inner V Y Y) := by
      rw [hy, inner_mul_right]
      exact trace_cg a c.1 _
    rw [weil_pt hω a hm hu, e1]
    simp only [hF]
    have e2 : Matrix.trace (HMul.hMul (c + b1).1 (StdUnn.inner V Y Y) : Mx D n n) =
        Matrix.trace (c.1 * StdUnn.inner V Y Y) + Matrix.trace (b1.1 * StdUnn.inner V Y Y) := by
      rw [← Matrix.trace_add, ← Matrix.add_mul]
      rfl
    rw [e2, halfTr_add, AddChar.map_add_eq_mul]
    ring
  unfold Jt
  simp only [hpt]
  rw [integral_const_mul, integral_mul_right V.rank μ hμ a F]

end GlobalTheory.CompanionTheory.IwaAd
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalVolumeRankOneIsotropicStatement
section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_volume_rank_one_isotropic : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → 3 ≤ M → ∀ (h₀ : ∀ a b : Fin 1, σ ((0 : Matrix (Fin 1) (Fin 1) E) b a) = (0 : Matrix (Fin 1) (Fin 1) E) a b), ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (v : HeightOneSpectrum (𝓞 F)) (lam : Measure (Fv F v)), IsStdV v lam → ∀ (m : HermR (Fv F v) σ 1 → Measure (Fin 1 → Fin M → Fv F v ⊗[F] E)), IsGramFibFree (Fv F v) σ J 1 (coordW (Fv F v) b lam 1 M) (coordHerm (Fv F v) σ b lam 1) m → ∀ A : Set (Fin 1 → Fin M → Fv F v ⊗[F] E), IsCompact A → IsOpen A → m (hermOf (Fv F v) σ (0 : Matrix (Fin 1) (Fin 1) E) h₀) A < ⊤ ∧ ∀ ε : ℝ, 0 < ε → ∃ U ∈ 𝓝 (0 : Fv F v), ∀ V : Set (Fv F v), MeasurableSet V → V ⊆ U → |(coordW (Fv F v) b lam 1 M (A ∩ {X | algebraMap F (Fv F v) (1 / 2) * Algebra.trace (Fv F v) (Fv F v ⊗[F] E) (gramR (Fv F v) σ J X 0 0) ∈ V})).toReal - (m (hermOf (Fv F v) σ (0 : Matrix (Fin 1) (Fin 1) E) h₀) A).toReal * (lam V).toReal| ≤ ε * (lam V).toReal := by
  first | exact @GlobalTheory.CompanionTheory.SW.AvgZero.avg_zero | exact GlobalTheory.CompanionTheory.SW.AvgZero.avg_zero | (intros; apply GlobalTheory.CompanionTheory.SW.AvgZero.avg_zero <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NondegenerateCharacterCellFactorizationStatement
section
noncomputable section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS GlobalTheory.Eis GlobalTheory.CompanionTheory.SwUnf
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.nondegenerate_character_cell_factorization : ∀ {D : D7} {n : ℕ} {ψ : AddChar (AF D.host.F) ℂ}, IsCharAF D.host.F ψ → ∀ (β : HermE D n), β.1.det ≠ 0 → ∀ (W : Submodule D.host.E (Fin n → D.host.E)), W ≠ ⊥ → ∃ ν : hermA D n, ψ (-halfTr (Matrix.trace (HMul.hMul (β.1.map (incA D)) ν.1 : Mx D n n))) ≠ 1 ∧ ∀ (γ u : G D n), γ ∈ GF D n → ∀ x : Matrix (Fin (n + n)) (Fin (n + n)) D.host.E, mat γ = x.map (incA D) → cellKer x = W → mat u = blk4 1 ν.1 0 1 → ∃ p ∈ P D n, ∃ a : GL (Fin n) (AE D), blkA (mat p) = a.1 ∧ Matrix.GeneralLinearGroup.det a = 1 ∧ γ * u = p * γ := by
  first | exact @GlobalTheory.CompanionTheory.SwUnf.SmallCell.small_cell | exact GlobalTheory.CompanionTheory.SwUnf.SmallCell.small_cell | (intros; apply GlobalTheory.CompanionTheory.SwUnf.SmallCell.small_cell <;> assumption)
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SectionInvariantHeisenbergWeyl
section
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.FJE.LawW

open GlobalTheory.StdUnn.Model GlobalTheory.StdUnn.LeftInvSect GlobalTheory.CompanionTheory.PcB

variable {D : D7} {n ρ p : ℕ} {hn : ρ + p = n}

def qm (hn : ρ + p = n) (x : Mx D ρ p) : Mx D (n + n) (n + n) :=
  blk4 (bl hn 1 0 (adj x) 1) 0 0 (bl hn 1 (-x) 0 1)

theorem qm_mul_w (M : Maps D hn) (x : Mx D ρ p) :
    qm hn x * mat M.w = mat M.w * mat (M.nzx 0 x) := by
  rw [M.w_mat, M.nzx_mat, qm, submatrix_fromBlocks_mul, submatrix_fromBlocks_mul]
  have hz : ((0 : hermA D ρ).1 : Mx D ρ ρ) = 0 := rfl
  rw [hz]
  simp only [blockMatrix_multiply]
  congr 1 <;> simp
  · rw [blockMatrix_add']; simp
  · rw [blockMatrix_add']; simp

theorem mat_conj (M : Maps D hn) (x : Mx D ρ p) : mat (M.w * M.nzx 0 x * M.w⁻¹) = qm hn x := by
  have h : mat M.w * mat M.w⁻¹ = 1 := by rw [← mat_mul, mul_inv_cancel, mat_one]
  calc mat (M.w * M.nzx 0 x * M.w⁻¹) = (mat M.w * mat (M.nzx 0 x)) * mat M.w⁻¹ := rfl
    _ = qm hn x * (mat M.w * mat M.w⁻¹) := by rw [← qm_mul_w, mul_assoc]
    _ = qm hn x := by rw [h, mul_one]

theorem exists_low (hn : ρ + p = n) (c : Mx D p ρ) :
    ∃ a : GL (Fin n) (AE D), a.1 = bl hn 1 0 c 1 :=
  ⟨⟨bl hn 1 0 c 1, bl hn 1 0 (-c) 1, by rw [lowerUnipotent_mul, add_neg_cancel, blockMatrix_one], by rw [lowerUnipotent_mul, neg_add_cancel, blockMatrix_one]⟩, rfl⟩

theorem det_low (hn : ρ + p = n) (c : Mx D p ρ) (a : GL (Fin n) (AE D)) (ha : a.1 = bl hn 1 0 c 1) :
    Matrix.GeneralLinearGroup.det a = 1 := by
  apply Units.ext
  change a.1.det = 1
  rw [ha, bl, Matrix.det_submatrix_equiv_self, Matrix.det_fromBlocks_zero₁₂]
  simp

theorem blkA_qm (hn : ρ + p = n) (x : Mx D ρ p) : blkA (qm hn x) = bl hn 1 0 (adj x) 1 := by
  ext i j
  simp [qm, blkA, blk4, Matrix.toBlocks₁₁]

theorem law_w : ∀ {D : D7} {n ρ p : ℕ} {hn : ρ + p = n} (M : Maps D hn) (χ : (AE D)ˣ →* Circle) (s : ℂ) (f : G D n → ℂ),
    IsLaw χ s f → ∀ (x : Mx D ρ p) (h : G D n), f (M.w * M.nzx 0 x * h) = f (M.w * h) := by
  intro D n ρ p hn M χ s f hf x h
  have hq := mat_conj M x
  have hP : M.w * M.nzx 0 x * M.w⁻¹ ∈ P D n := GlobalTheory.CompanionTheory.SwUnf.SmallCell.mem_siegelParabolic_of_lowerLeft_entries_eq_zero hq
  obtain ⟨a, ha⟩ := exists_low hn (adj x)
  have hA : blkA (mat (M.w * M.nzx 0 x * M.w⁻¹)) = a.1 := by rw [hq, blkA_qm, ha]
  have key := hf _ hP a hA (M.w * h)
  rw [det_low hn (adj x) a ha, map_one, map_one] at key
  have e : M.w * M.nzx 0 x * M.w⁻¹ * (M.w * h) = M.w * M.nzx 0 x * h := by group
  rw [e] at key
  simpa using key

end GlobalTheory.CompanionTheory.FJE.LawW
end
end

