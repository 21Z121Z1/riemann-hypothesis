import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0019
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0018
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0265
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0005
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0155
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0243
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0191
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0328
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0168
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsDualFamilyOfIsLattice
import Development.AbelianVarietyTheory.Definitions.Foundations.GLintEqKOAndPrincEqKOne
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0179
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0125
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.DoubleCollapse
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0115
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PairOperatorStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0190
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0046
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0097
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCombAt
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0014
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0002
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0010
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0032
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.StandardOrderExtendedBasisApplyLowBlock
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0008
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0191
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0149
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0024
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0019
import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0005
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0192
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0193
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0017
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0194

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ParahoricChartIntegralGLEqLatticeStabilizer
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.ChainTw
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (SplitProj IsProjAt IsIdemOf LiftsChar rdA grpCo frCo gAt)
open GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection (Blocks parahoric datum)
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.Chain GlobalTheory.ChainFr GlobalTheory.PairLift GlobalTheory.Chain.RealIt

noncomputable section
namespace GlobalTheory.ChartStab

set_option maxHeartbeats 1000000 in

theorem mem_splitLat_iff {D : D7} {n : ℕ} {Λ : Submodule (𝓞 D.host.E) (Fin n → D.host.E)} {β : GL (Fin n) (EAf D)}
    (hβ : Formalism.L2.DIV.IsFrame β Λ) {v : HeightOneSpectrum (𝓞 D.host.F)} (φ : SplitProj D v) (u : Fin n → Fv D.host.F v) :
    u ∈ GlobalTheory.AdelicU.splitLat (GlobalTheory.SplitProjChart.emb φ) Λ ↔
      ∀ i, Valued.v ((((frCo φ β)⁻¹ : GL (Fin n) (Fv D.host.F v)).1 *ᵥ u) i) ≤ 1 := by
  set e := GlobalTheory.EmbChart.idem (GlobalTheory.SplitProjChart.emb φ) with he_def
  have hπ : GlobalTheory.SplitHecke.Chart e v (rdA φ) := GlobalTheory.SplitProjChart.chart_idem φ
  have he : IsSplitIdem D e := GlobalTheory.EmbChart.isSplitIdem_idem _
  have hemb : GlobalTheory.AdelicU.chartEmb hπ = GlobalTheory.SplitProjChart.emb φ := AlgHom.ext fun x => by
    rw [GlobalTheory.AdelicU.chartEmb_apply, GlobalTheory.SplitProjChart.rdA_incA]; rfl
  choose y hy using fun k => hπ.1 (u k)
  obtain ⟨Λ₁, hle, hfg, heq⟩ := GlobalTheory.ChainOnto.LStab.exists_fg_sub hβ
  have hsl : GlobalTheory.AdelicU.splitLat (GlobalTheory.SplitProjChart.emb φ) Λ₁ = GlobalTheory.AdelicU.splitLat (GlobalTheory.SplitProjChart.emb φ) Λ := by
    ext w
    rw [GlobalTheory.AdelicU.mem_splitLat, GlobalTheory.AdelicU.mem_splitLat, GlobalTheory.ChainOnto.LStab.latLoc_eq hle hfg heq v]
  have h1 := GlobalTheory.AdelicU.SplitFrame.mem_latHat_iff_of_support (GlobalTheory.AdelicU.isCMExt_host D) _ hfg
    (GlobalTheory.AdelicU.SplitFrame.vecLoc_self he hπ y) (GlobalTheory.AdelicU.SplitFrame.vecLoc_ne he hπ y)
  rw [hemb, hsl, show (fun k => rdA φ (y k)) = u from funext hy] at h1
  rw [← h1, GlobalTheory.SplitFrameColumn.latHat_iff_hatL, heq]
  have hβ' := hβ (fun k => Algebra.TensorProduct.comm D.host.F (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) D.host.E (finPart D (e * y k)))
  rw [hβ']
  have hsw : (fun k => Algebra.TensorProduct.comm D.host.F (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) D.host.E (finPart D (e * y k))) =
      toEAf D e • fun k => toEAf D (y k) := funext fun k => (toEAf D).map_mul e (y k)
  rw [hsw, Matrix.mulVec_smul]
  set w : Fin n → EAf D := (β⁻¹).1 *ᵥ fun k => toEAf D (y k) with hw
  refine forall_congr' fun i => ?_
  have h2 : (toEAf D e • w) i = toEAf D (e * GlobalTheory.AdelicLatMove.finEmb D (w i)) := by
    rw [map_mul, GlobalTheory.SplitFrameColumn.toEAf_finEmb]; rfl
  have h3 : rdA φ (GlobalTheory.AdelicLatMove.finEmb D (w i)) =
      ((((frCo φ β)⁻¹ : GL (Fin n) (Fv D.host.F v)).1 *ᵥ u) i) := by
    rw [← GlobalTheory.SplitProjChart.rdE_toEAf, GlobalTheory.SplitFrameColumn.toEAf_finEmb, hw, RingHom.map_mulVec]
    unfold frCo
    rw [← map_inv]
    congr 1
    funext k
    exact (GlobalTheory.SplitProjChart.rdE_toEAf φ (y k)).trans (hy k)
  rw [h2, show toEAf D (e * GlobalTheory.AdelicLatMove.finEmb D (w i)) =
      Algebra.TensorProduct.comm D.host.F (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) D.host.E (finPart D (e * GlobalTheory.AdelicLatMove.finEmb D (w i))) from rfl,
    GlobalTheory.SplitFrameColumn.comm_mem_intAf_iff, hπ.2.2.2, GlobalTheory.SplitHecke.isInt_Ov, HeightOneSpectrum.mem_adicCompletionIntegers, h3]

theorem hermND (D : D7) (V : HSp D) : IsHermND D.sp.cm.sig V.gram :=
  (GlobalTheory.Mem.Vol.cmData_isCMExt_and_gram_isHermND _ _ D.sp.cm).2 V

theorem isSelfDualAt_of_isSelfDualC {D : D7} (V : HSp D) {Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)}
    (hΛ : IsSelfDualC V Λ) (v : HeightOneSpectrum (𝓞 D.host.F)) :
    GlobalTheory.AdelicU.IsSelfDualAt D.sp.cm.sig V.gram Λ v := by
  refine (GlobalTheory.AdelicU.SelfDual.forall_isSelfDualAt_iff (hermND D V).2 hΛ.1).2 (fun y => ?_) v
  refine (hΛ.2 y).trans (forall₂_congr fun x _ => ?_)
  constructor
  · rintro ⟨b, hb⟩
    exact ⟨b, hb⟩
  · rintro ⟨b, hb⟩
    exact ⟨b, hb⟩

theorem isSplitBasis_frCo {D : D7} {n : ℕ} {Λ : Submodule (𝓞 D.host.E) (Fin n → D.host.E)} {β : GL (Fin n) (EAf D)}
    (hβ : Formalism.L2.DIV.IsFrame β Λ) {v : HeightOneSpectrum (𝓞 D.host.F)} (φ : SplitProj D v) :
    GlobalTheory.AdelicU.IsSplitBasis (GlobalTheory.SplitProjChart.emb φ) Λ (frCo φ β) := fun u => by
  rw [mem_splitLat_iff hβ φ, Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec]
  simp only [HeightOneSpectrum.mem_adicCompletionIntegers]

theorem grpCo_emb {D : D7} (V : HSp D) {v : HeightOneSpectrum (𝓞 D.host.F)} (φ : SplitProj D v)
    (B : GL (Fin V.rank) (Fv D.host.F v)) (x : GlobalTheory.FinZeta.Gv V v) :
    grpCo φ V B (GlobalTheory.AdelicU.emb D.sp.cm.sig V.gram v x) =
      GlobalTheory.AdelicU.splitEquivIn (GlobalTheory.AdelicU.isCMExt_host D) (hermND D V) (GlobalTheory.SplitProjChart.emb φ) B x := by
  rw [GlobalTheory.AdelicU.splitEquivIn_apply, ← GlobalTheory.SplitChartLink.rdA_matHom_embV]
  rfl

section Reindex

variable {K : Type} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]

theorem reindex_mem_KO {m ι : Type} [Fintype m] [DecidableEq m] [Fintype ι] [DecidableEq ι] (ε : ι ≃ m)
    {x : GL m K} (hx : x ∈ GlobalTheory.SplitWeil.KO K m) (y : GL ι K) (h : ∀ i j, y.1 i j = x.1 (ε i) (ε j)) :
    y ∈ GlobalTheory.SplitWeil.KO K ι := by
  obtain ⟨a, rfl⟩ := hx
  refine ⟨Units.map (Matrix.reindexAlgEquiv (ValuativeRel.valuation K).integer (ValuativeRel.valuation K).integer ε.symm).toMonoidHom a, ?_⟩
  ext i j
  rw [h]
  simp [Matrix.reindexAlgEquiv_apply, Matrix.reindex_apply]

theorem mem_KO_iff_reindex {m ι : Type} [Fintype m] [DecidableEq m] [Fintype ι] [DecidableEq ι] (ε : ι ≃ m)
    (x : GL m K) (y : GL ι K) (h : ∀ i j, y.1 i j = x.1 (ε i) (ε j)) :
    x ∈ GlobalTheory.SplitWeil.KO K m ↔ y ∈ GlobalTheory.SplitWeil.KO K ι :=
  ⟨fun hx => reindex_mem_KO ε hx y h,
    fun hy => reindex_mem_KO ε.symm hy x fun i j => by rw [h]; simp⟩

end Reindex

theorem chart_stab : ∀ (D : D7) (s : PiLocalization₂ D) (k : ℕ) (v : HeightOneSpectrum (𝓞 D.host.F)) (φ : SplitProj D v) (ι : GL (Fin D.R.r ⊕ Blocks k D.R.t) (Fv D.host.F v) →* GA D s.V), IsSelfDualC s.V s.Λ → Formalism.L2.DIV.IsFrame s.β s.Λ → IsChart s k φ ι → ∀ e : GL (Fin D.R.r ⊕ Blocks k D.R.t) (Fv D.host.F v) → GlobalTheory.FinZeta.Gv s.V v, (∀ y, ι y = GlobalTheory.AdelicU.emb D.sp.cm.sig s.V.gram v (e y)) → ∀ y, e y ∈ GlobalTheory.AdelicU.stabLoc D.sp.cm.sig s.V.gram s.Λ v ↔ y ∈ GlobalTheory.SplitWeil.KO (Fv D.host.F v) _ := by
  intro D s k v φ ι hsd hfr hch e he y
  obtain ⟨ε, -, hε⟩ := hch
  have hB := isSplitBasis_frCo hfr φ
  have hL := isSelfDualAt_of_isSelfDualC s.V hsd v
  rw [GlobalTheory.AdelicU.mem_stabLoc_iff_GLint (GlobalTheory.AdelicU.isCMExt_host D) (hermND D s.V) hL hB,
    (GlobalTheory.AdelicU.GLint_eq_KO_and_princ_eq_KOne v _).1]
  have h2 := (hε y).2
  rw [he y, grpCo_emb] at h2
  exact mem_KO_iff_reindex ε _ y fun i j => by rw [← h2]; rfl

end GlobalTheory.ChartStab
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RamUnitaryHolds
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil ValuativeRel IsLocalRing GlobalTheory.IndefiniteRowSideFullHecke.AdjointOperatorIdentities
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FinPl.RamUnit

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {p : SplitPt D k} {S : HSp D} {n : Type} [Fintype n] [DecidableEq n]

def pet (vS : Vol S) (ψ ψ' : Form k n (GA D S → ℂ)) (P : Pair k n) : ℂ :=
  ∫ g in vS.𝓕, ψ P g * star (ψ' P g) ∂vS.μ

theorem rep_apply (β : Frame p S n) (g : GL n k) (f : GA D S → ℂ) (x : GA D S) :
    β.rep g f x = f (x * β.gl g) := rfl

theorem pet_const (vS : Vol S) (β : Frame p S n) {ψ ψ' : Form k n (GA D S → ℂ)} (hψ : ψ ∈ EqForm β.rep)
    (hψ' : ψ' ∈ EqForm β.rep) (hl : ∀ P, ∀ γ ∈ GQ S, ∀ g, ψ P (γ * g) = ψ P g)
    (hl' : ∀ P, ∀ γ ∈ GQ S, ∀ g, ψ' P (γ * g) = ψ' P g) (P Q : Pair k n) : pet vS ψ ψ' P = pet vS ψ ψ' Q := by
  obtain ⟨g, rfl⟩ := MulAction.exists_smul_eq (GL n k) P Q
  unfold pet
  rw [hψ g P, hψ' g P]
  simp only [rep_apply]
  exact (GlobalTheory.ChainOnto.setIntegral_fd_mul_right D S vS.μ vS.𝓕 vS.haar vS.fund (fun x => ψ P x * star (ψ' P x))
    (fun γ hγ x => by simp only [hl P γ hγ, hl' P γ hγ]) (β.gl g)).symm

theorem sum_pet_FFStar (vS : Vol S) (hS : CoCpt S) (q : Unif k) (χ : AddChar 𝓀[k] ℂ)
    (hχ : ∀ a, (starRingEnd ℂ) (χ a) = χ (-a))
    {φ ψ : Form k n (GA D S → ℂ)} (hφ : ∀ P, IsContAut S (φ P)) (hψ : ∀ P, IsContAut S (ψ P))
    (L : Submodule 𝒪[k] (n → k)) :
    ∑ P ∈ withLat L, pet vS (FFStar q χ φ) ψ P = ∑ P₁ ∈ withKer L, pet vS φ (FF q χ ψ) P₁ := by
  have hint : ∀ P₁ P, IntegrableOn (fun g => φ P₁ g * star (ψ P g)) vS.𝓕 vS.μ := fun P₁ P =>
    (GlobalTheory.CocompactParam.continuous_integral_param D S hS vS Unit (fun g _ => φ P₁ g * star (ψ P g))
      (((hφ P₁).2.mul (hψ P).2.star).comp continuous_fst)
      (fun γ hγ g _ => by simp only [(hφ P₁).1 γ hγ, (hψ P).1 γ hγ])).1 ()
  have e1 : ∀ P ∈ withLat L, pet vS (FFStar q χ φ) ψ P =
      ∑ P₁ ∈ withKer L, χ (-cross q P₁ P) * ∫ g in vS.𝓕, φ P₁ g * star (ψ P g) ∂vS.μ := by
    intro P hP
    rw [mem_withLat] at hP
    unfold pet
    rw [FFStar_apply, hP]
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_mul, mul_assoc]
    rw [integral_finset_sum _ (fun P₁ _ => (hint P₁ P).const_mul _)]
    exact Finset.sum_congr rfl fun P₁ _ => integral_const_mul _ _
  have e2 : ∀ P₁ ∈ withKer L, pet vS φ (FF q χ ψ) P₁ =
      ∑ P ∈ withLat L, χ (-cross q P₁ P) * ∫ g in vS.𝓕, φ P₁ g * star (ψ P g) ∂vS.μ := by
    intro P₁ hP₁
    rw [mem_withKer] at hP₁
    unfold pet
    rw [FF_apply, hP₁]
    have : ∀ g, φ P₁ g * star ((∑ P ∈ withLat L, χ (cross q P₁ P) • ψ P) g) =
        ∑ P ∈ withLat L, χ (-cross q P₁ P) * (φ P₁ g * star (ψ P g)) := fun g => by
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, star_sum, Finset.mul_sum, star_mul']
      refine Finset.sum_congr rfl fun P _ => ?_
      rw [← hχ]
      change φ P₁ g * ((starRingEnd ℂ) (χ (cross q P₁ P)) * star (ψ P g)) = _
      ring
    simp only [this]
    rw [integral_finset_sum _ (fun P _ => (hint P₁ P).const_mul _)]
    exact Finset.sum_congr rfl fun P _ => integral_const_mul _ _
  rw [Finset.sum_congr rfl e1, Finset.sum_congr rfl e2, Finset.sum_comm]

end GlobalTheory.FinPl.RamUnit

namespace GlobalTheory.FinPl.RamUnit

theorem ramUnitary_holds : ∀ D : D7, GlobalTheory.FinPl.RamUnitary D := by
  intro D k _ _ _ _ p n _ _ q χ hχ ε S hS vS β P φ₀ φ₀' hφ₀ hφ₀'
  obtain ⟨φ, hφ, rfl⟩ := hφ₀
  obtain ⟨φ', hφ', rfl⟩ := hφ₀'
  have hB := GlobalTheory.FinPl.ramBijective_holds D k p n q χ hχ (resChar χ hχ q) rfl ε S β P
  obtain ⟨hA, eA⟩ := hB.2.1 φ hφ
  obtain ⟨hA', eA'⟩ := hB.2.1 φ' hφ'
  rw [eA, eA']
  have hO : OperatorIdentities k n (GA D S → ℂ) q (resChar χ hχ q) :=
    ((GlobalTheory.PairOp.pairOperatorStatement k q χ hχ n).1 (GA D S → ℂ)).2
  set X := FFStar q (resChar χ hχ q) φ with hX
  set X' := FFStar q (resChar χ hχ q) φ' with hX'
  have cX : ∀ Q, IsContAut S (X Q) := fun Q => by
    have := hA.2.2 (ε⁻¹ • Q)
    rwa [dia_apply, smul_inv_smul] at this
  have cX' : ∀ Q, IsContAut S (X' Q) := fun Q => by
    have := hA'.2.2 (ε⁻¹ • Q)
    rwa [dia_apply, smul_inv_smul] at this
  have eFF : FF q (resChar χ hχ q) X' = ((resCard k : ℂ) ^ Fintype.card n) • φ' := hO.FF_FFStar_ram φ' hφ'.2.1
  have c2 : ∀ Q, IsContAut S ((FF q (resChar χ hχ q) X') Q) := fun Q => by
    rw [eFF]
    exact ⟨fun γ hγ g => by simp only [Pi.smul_apply, smul_eq_mul, (hφ'.2.2 Q).1 γ hγ],
      continuous_const.mul (hφ'.2.2 Q).2⟩
  have hsum := sum_pet_FFStar vS hS q (resChar χ hχ q) (conj_resChar hχ q) hφ.2.2 cX' P.lat
  have k1 : ∀ Q ∈ withLat P.lat, pet vS X X' Q = pet vS X X' (ε • P) := fun Q _ =>
    pet_const vS β (FFStar_mem_EqForm q _ hφ.1) (FFStar_mem_EqForm q _ hφ'.1) (fun Q => (cX Q).1)
      (fun Q => (cX' Q).1) Q (ε • P)
  have k2 : ∀ Q ∈ withKer P.lat, pet vS φ (FF q (resChar χ hχ q) X') Q = pet vS φ (FF q (resChar χ hχ q) X') P :=
    fun Q _ => pet_const vS β hφ.1 (FF_mem_EqForm q _ (FFStar_mem_EqForm q _ hφ'.1)) (fun Q => (hφ.2.2 Q).1)
      (fun Q => (c2 Q).1) Q P
  rw [Finset.sum_congr rfl k1, Finset.sum_congr rfl k2, Finset.sum_const, Finset.sum_const,
    ← card_withLat_eq_card_withKer] at hsum
  have hN : (withLat P.lat).card ≠ 0 := (Finset.card_pos.2 ⟨P, mem_withLat.2 rfl⟩).ne'
  have hpe : pet vS X X' (ε • P) = pet vS φ (FF q (resChar χ hχ q) X') P := by
    rw [← Nat.cast_smul_eq_nsmul ℂ, ← Nat.cast_smul_eq_nsmul ℂ] at hsum
    exact smul_right_injective ℂ (Nat.cast_ne_zero.2 hN) hsum
  change pet vS X X' (ε • P) = _
  rw [hpe, eFF]
  unfold pet
  simp only [Pi.smul_apply, smul_eq_mul, star_mul', star_pow, Complex.star_def, Complex.conj_natCast]
  rw [← integral_const_mul]
  congr 1
  funext g
  ring

end GlobalTheory.FinPl.RamUnit
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RowFourierOntoAndSpanTransformedLastRow
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.SeeSaw GlobalTheory.LocMod
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.LocMod.LastRow

open GlobalTheory.LocFlat.CFac

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  [MeasurableSpace k] [BorelSpace k]

theorem fourier_inversion_const (ψ : AddChar k Circle) (ν : Measure k) (hψ : Continuous ψ) (hne : ψ ≠ 1)
    [ν.IsAddHaarMeasure] (I : Type) [Fintype I] :
    ∃ C : ℝ, 0 < C ∧ ∀ (a : I → k) (g : (I → k) → ℂ), g ∈ SB (I → k) →
      ∫ l : I → k, (ψ (-(l ⬝ᵥ a)) : ℂ) * (∫ x, g x * (ψ (x ⬝ᵥ l) : ℂ) ∂(Measure.pi fun _ => ν))
        ∂(Measure.pi fun _ => ν) = (C : ℂ) * g a := by
  classical
  have := secondCountable k
  have := t2Space k
  obtain ⟨c, hc⟩ := (conductor_exists k).1 ψ hψ hne
  have hpsi : ∀ u : k, (ψ (-u) : ℂ) * ψ u = 1 := by
    intro u
    rw [← Circle.coe_mul, ← AddChar.map_add_eq_mul, neg_add_cancel, AddChar.map_zero_eq_one, Circle.coe_one]
  refine ⟨(nabs k c * ν.real (𝒪[k] : Set k) ^ 2) ^ Fintype.card I, ?_, fun a g hg => ?_⟩
  · have hO : 0 < ν.real (𝒪[k] : Set k) :=
      ENNReal.toReal_pos ((isOpen_int k).measure_pos ν ⟨0, zero_mem _⟩).ne' (isCompact_int k).measure_lt_top.ne
    have := nabs_pos k c
    positivity
  set μI : Measure (I → k) := Measure.pi fun _ => ν with hμI
  set h : (I → k) → ℂ := fun x => g (x + a) with hhdef
  have hh : h ∈ SB (I → k) :=
    ⟨hg.1.comp_continuous (continuous_add_const a), hg.2.comp_homeomorph (Homeomorph.addRight a)⟩
  have htr : ∀ l : I → k, (ψ (-(l ⬝ᵥ a)) : ℂ) * ∫ x₁, g x₁ * (ψ (x₁ ⬝ᵥ l) : ℂ) ∂μI =
      ∫ x, h x * (ψ (x ⬝ᵥ l) : ℂ) ∂μI := by
    intro l
    rw [← integral_const_mul, ← integral_add_right_eq_self _ a]
    congr 1
    funext x
    have e1 : (x + a) ⬝ᵥ l = x ⬝ᵥ l + l ⬝ᵥ a := by rw [add_dotProduct, dotProduct_comm a l]
    rw [hhdef, e1, AddChar.map_add_eq_mul, Circle.coe_mul]
    linear_combination (g (x + a) * (ψ (x ⬝ᵥ l) : ℂ)) * hpsi (l ⬝ᵥ a)
  simp only [htr]
  obtain ⟨s, hs⟩ := FourierPi.fourier_inversion_pi μI hc hh
  have hb : ∀ r : kˣ, μI.real (FourierPi.box I r) = ν.real (cball r) ^ Fintype.card I := by
    intro r
    simp [hμI, Measure.real, FourierPi.box, Measure.pi_pi]
  rw [hs, hb, hb, ← mul_pow, measureReal_cball, measureReal_cball]
  have h4 : nabs k c = nabs k s * nabs k (c * s⁻¹) := by
    rw [← nabs_mul, mul_comm, inv_mul_cancel_right]
  simp only [hhdef, zero_add, h4]
  push_cast
  ring

end GlobalTheory.LocMod.LastRow

namespace GlobalTheory.LocMod.LastRow

open GlobalTheory.LocFlat.CFac

theorem transform_onto_and_span_lastRow : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (ν : Measure k), ν.IsAddHaarMeasure → ∀ (ψk : AddChar k Circle), Continuous ψk → ψk ≠ 1 → ∀ (n Z : Type) [Fintype n] [DecidableEq n] [Fintype Z] [DecidableEq Z], (∀ b : SB (Matrix Unit n k), ∃ c : SB (Matrix n Unit k), ∀ η, b.1 η = GlobalTheory.StepData.hat ψk ν (-1) (fun y => c.1 (Matrix.of fun r _ => y r)) (η ())) ∧ ∀ Ξ₂ : SB (Matrix (Z ⊕ Unit) n k), ∃ (N : ℕ) (a : Fin N → SB (Matrix Z n k)) (c : Fin N → SB (Matrix n Unit k)) (g : Fin N → SB (Matrix (Z ⊕ Unit) n k)), (∀ i x, (g i).1 x = (a i).1 x.toRows₁ * GlobalTheory.StepData.hat ψk ν (-1) (fun y => (c i).1 (Matrix.of fun r _ => y r)) (x (Sum.inr ()))) ∧ Ξ₂ = ∑ i, g i := by
  intro k _ _ _ _ _ _ ν hν ψk hψ hne n Z _ _ _ _
  haveI := hν
  haveI := secondCountable k
  haveI : T2Space k := GlobalTheory.SplitWeil.t2Space k
  haveI : NonarchimedeanAddGroup k := ⟨fun V hV => by
    obtain ⟨s, hs⟩ := GlobalTheory.SplitWeil.exists_cball_subset hV
    exact ⟨⟨⟨⟨⟨GlobalTheory.SplitWeil.cball s, GlobalTheory.SplitWeil.add_mem_cball⟩, by simp [GlobalTheory.SplitWeil.cball]⟩,
      GlobalTheory.SplitWeil.neg_mem_cball⟩, GlobalTheory.SplitWeil.isOpen_cball s⟩, hs⟩⟩
  haveI : TotallyDisconnectedSpace k := inferInstance
  haveI hTD : ∀ (a b : Type) [Fintype a] [Fintype b], TotallyDisconnectedSpace (Matrix a b k) :=
    fun a b _ _ => inferInstanceAs (TotallyDisconnectedSpace (a → b → k))
  haveI hLC : ∀ (a b : Type) [Fintype a] [Fintype b], LocallyCompactSpace (Matrix a b k) :=
    fun a b _ _ => inferInstanceAs (LocallyCompactSpace (a → b → k))
  haveI hT2 : ∀ (a b : Type), T2Space (Matrix a b k) := fun a b => inferInstanceAs (T2Space (a → b → k))
  have part1 : ∀ b : SB (Matrix Unit n k), ∃ c : SB (Matrix n Unit k), ∀ η,
      b.1 η = GlobalTheory.StepData.hat ψk ν (-1) (fun y => c.1 (Matrix.of fun r _ => y r)) (η ()) := by
    obtain ⟨C, hC, hinv⟩ := fourier_inversion_const ψk ν hψ hne n
    obtain ⟨c0, hc0⟩ := (conductor_exists k).1 ψk hψ hne
    intro b
    let e1 : (n → k) ≃ₜ Matrix Unit n k := (Homeomorph.funUnique Unit (n → k)).symm
    let g : SB (n → k) := comapH e1 b
    have hF := FourierPi.fourier_mem_SB (Measure.pi fun _ : n => ν) hc0 g.2
    let e2 : Matrix n Unit k ≃ₜ (n → k) := Homeomorph.piCongrRight fun _ => Homeomorph.funUnique Unit k
    refine ⟨((C : ℂ)⁻¹) • comapH e2 ⟨_, hF⟩, fun η => ?_⟩
    unfold GlobalTheory.StepData.hat
    have e3 : ∀ y : n → k, ((((C : ℂ)⁻¹) • comapH e2 ⟨_, hF⟩ : SB (Matrix n Unit k)).1
        (Matrix.of fun r _ => y r)) * (ψk ((-1) * (η () ⬝ᵥ y)) : ℂ) =
        (C : ℂ)⁻¹ * ((ψk (-(y ⬝ᵥ η ())) : ℂ) * ∫ x, g.1 x * (ψk (x ⬝ᵥ y) : ℂ) ∂(Measure.pi fun _ => ν)) := by
      intro y
      rw [neg_one_mul, dotProduct_comm]
      change (C : ℂ)⁻¹ * (∫ x, g.1 x * (ψk (x ⬝ᵥ y) : ℂ) ∂(Measure.pi fun _ => ν)) * _ = _
      ring
    simp only [e3]
    rw [integral_const_mul, hinv (η ()) g.1 g.2, ← mul_assoc,
      inv_mul_cancel₀ (by exact_mod_cast hC.ne'), one_mul]
    rfl
  refine ⟨part1, fun Ξ₂ => ?_⟩
  let e : Matrix (Z ⊕ Unit) n k ≃ₜ Matrix Z n k × Matrix Unit n k := Homeomorph.sumArrowHomeomorphProdArrow
  have hspan := GlobalTheory.LocFlat.CFac.Span.span_prodSB_eq_top (Matrix Z n k) (Matrix Unit n k)
  have hmem : comapH e.symm Ξ₂ ∈ Submodule.span ℂ
      (Set.range fun q : SB (Matrix Z n k) × SB (Matrix Unit n k) => prodSB q.1 q.2) := by
    rw [hspan]; trivial
  obtain ⟨N, f, q, hq⟩ := Submodule.mem_span_set'.mp hmem
  choose p hp using fun i => (q i).2
  choose c hc using fun i => part1 (p i).2
  refine ⟨N, fun i => f i • (p i).1, c, fun i => comapH e (prodSB (f i • (p i).1) (p i).2), fun i x => ?_, ?_⟩
  · rw [comapH_apply, prodSB_apply]
    congr 1
    exact hc i _
  · have h1 : Ξ₂ = comapH e (comapH e.symm Ξ₂) := by
      ext x; simp only [comapH_apply, Homeomorph.symm_apply_apply]
    rw [h1, ← hq, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul, ← hp i]
    ext x
    simp only [comapH_apply, prodSB_apply, SetLike.val_smul, Pi.smul_apply, smul_eq_mul, mul_assoc]

end GlobalTheory.LocMod.LastRow
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SatakeEsymmScaledMultisetAddSegmentStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep
open GlobalTheory.FinZeta (Gv embV Kv VacFin IsLocKer KerU)
open GlobalTheory.SphTheta (IsStd CayleyRule intMat liftPar)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke IsCommensurated Tj SatU ordL Ov)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.satake_esymm_scaled_multiset_add_segment : ∀ (E : Type) [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) (a t k : ℕ) (B : Multiset ℂˣ) (z y : ℂˣ), B.card = a → k ≤ a + t → satEig (qV E w) (a + t) (B.map (z * y⁻¹ * ·) + seg w z t) k = ∑ j ∈ Finset.range (a + 1), (if j ≤ k then (qV E w : ℂ) ^ ((a - j) * (k - j)) * (Formalism.L2.Col.gaussBin (qV E w) t (k - j) : ℂ) * ((z : ℂ) * ((Real.sqrt (qV E w) : ℂ) ^ a)⁻¹) ^ k * (((y : ℂ))⁻¹ * (Real.sqrt (qV E w) : ℂ) ^ (a + t)) ^ j else 0) * satEig (qV E w) a B j := by
  first | exact @GlobalTheory.ChainOnto.satEig_map_add_seg | exact GlobalTheory.ChainOnto.satEig_map_add_seg | (intros; apply GlobalTheory.ChainOnto.satEig_map_add_seg <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SatakeStringGivesSimplePoleHypothesesStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift GlobalTheory.Core.Rk.Exh
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.satake_string_gives_simple_pole_hypotheses : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.LiftRows.Given R F → R.FullP → ∀ i t s, HasString R i t s → ∃ B c : GlobalTheory.LFun.Fam D.host.E, GlobalTheory.LFun.IsSysParamD D (GlobalTheory.IndefiniteRowSideFullHecke.LabelSettingScalars.badPl R t) (Vc D i).rank s B ∧ GlobalTheory.IndefiniteRowSideFullHecke.SimplePoleTwistedLift.Hyp (GlobalTheory.IndefiniteRowSideFullHecke.LabelSettingScalars.badPl R t : Set (HeightOneSpectrum (𝓞 D.host.F))) D.R.r D.R.t c B (GlobalTheory.LFun.val (F := D.host.F) (chiV R i t)) (GlobalTheory.LFun.val (F := D.host.F) (chiV R i t)) := by
  first | exact @GlobalTheory.Core.Rk.StringPole.string_pole_hyp | exact GlobalTheory.Core.Rk.StringPole.string_pole_hyp | (intros; apply GlobalTheory.Core.Rk.StringPole.string_pole_hyp <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SatakeVectorIffInverseDoubleCosetsStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep
open GlobalTheory.FinZeta (Gv embV Kv VacFin IsLocKer KerU)
open GlobalTheory.SphTheta (IsStd CayleyRule intMat liftPar)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke IsCommensurated Tj SatU ordL Ov)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.satake_vector_iff_inverse_doubleCosets : ∀ (E : Type) [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) (n : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (GL (Fin n) (w.adicCompletion E)) V) (x : V) (B : Multiset ℂˣ), x ≠ 0 → x ∈ fixed ρ (KGL w n) → B.card = n → (IsSatVecGL w ρ x B ↔ ∀ ϖ, IsUnifV E w ϖ → ∀ j ≤ n, heckeVec ρ (KGL w n) (fun g => Tj ℂ n (Ov E w) ϖ j g⁻¹) x = satEig (qV E w) n (B.map (·⁻¹)) j • x) := by
  first | exact @GlobalTheory.ChainOnto.SatInv.satVec_iff_inv | exact GlobalTheory.ChainOnto.SatInv.satVec_iff_inv | (intros; apply GlobalTheory.ChainOnto.SatInv.satVec_iff_inv <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SetIntegralFundamentalDomainRightTranslateInvariStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep
open GlobalTheory.FinZeta (Gv embV Kv VacFin IsLocKer KerU)
open GlobalTheory.SphTheta (IsStd CayleyRule intMat liftPar)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke IsCommensurated Tj SatU ordL Ov)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.setIntegral_fundamentalDomain_right_translate_invariant : ∀ (D : D7) (S : HSp D) (ν : Measure (GA D S)) (𝓕 : Set (GA D S)), ν.IsHaarMeasure → IsFundamentalDomain (GQ S) 𝓕 ν → ∀ F : GA D S → ℂ, (∀ γ ∈ GQ S, ∀ g, F (γ * g) = F g) → ∀ a : GA D S, ∫ g in 𝓕, F (g * a) ∂ν = ∫ g in 𝓕, F g ∂ν := by
  first | exact @GlobalTheory.ChainOnto.setIntegral_fd_mul_right | exact GlobalTheory.ChainOnto.setIntegral_fd_mul_right | (intros; apply GlobalTheory.ChainOnto.setIntegral_fd_mul_right <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SmallEntriesAndStringsAvoidExcludedNormPowersStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.small_entries_and_strings_avoid_excluded_norm_powers : ∀ (K : Type) [Field K] [NumberField K] (w : HeightOneSpectrum (𝓞 K)) (r t : ℕ), r + 2 ≤ t → ∀ k ∈ ({(t : ℤ) - 1, 1 - (t : ℤ), (t : ℤ) + 1, -((t : ℤ) + 1)} : Set ℤ), (∀ β : ℂ, β ≠ 0 → ‖β‖ ≤ ((Ideal.absNorm w.asIdeal : ℕ) : ℝ) ^ ((r : ℝ) / 2) → ‖β⁻¹‖ ≤ ((Ideal.absNorm w.asIdeal : ℕ) : ℝ) ^ ((r : ℝ) / 2) → β ≠ GlobalTheory.LFun.npow w ((k : ℂ) / 2)) ∧ ∀ x : ℂˣ, ‖(x : ℂ)‖ = 1 → x ≠ 1 → ∀ β ∈ GlobalTheory.LFun.seg w x t, (β : ℂ) ≠ GlobalTheory.LFun.npow w ((k : ℂ) / 2) := by
  first | exact @GlobalTheory.RkNs.small_entries_and_strings_avoid_excluded | exact GlobalTheory.RkNs.small_entries_and_strings_avoid_excluded | (intros; apply GlobalTheory.RkNs.small_entries_and_strings_avoid_excluded <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaChainCuspSpaceFiniteDimOfHarishChandraStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaChainCuspSpaceFiniteDim_of_harishChandra : GlobalTheory.Published.HarishChandraFinite → ∀ D : D7, LevFacts D → FinDim D := by
  first | exact @GlobalTheory.ChainOnto.finDim_of_levFacts | exact GlobalTheory.ChainOnto.finDim_of_levFacts | (intros; apply GlobalTheory.ChainOnto.finDim_of_levFacts <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaLiftChainHeckeParameterTwistNextTargetCharStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaLiftChainHeckeParameter_twist_next_target_char : ∀ (D : D7) (c : Com D) (B : GlobalTheory.LFun.Fam D.host.E) (k : ℕ), GlobalTheory.LFun.twist (chainPar c B k) (GlobalTheory.LFun.val (F := D.host.F) (c.chT (k + 1)))⁻¹ = GlobalTheory.LFun.twist B (GlobalTheory.LFun.val (F := D.host.F) (c.μ (k + 1)))⁻¹ + ∑ i ∈ Finset.Icc 1 k, GlobalTheory.LFun.segFam (GlobalTheory.LFun.val (F := D.host.F) (c.μ i * (c.μ (k + 1))⁻¹)) D.R.t := by
  first | exact @GlobalTheory.ChainOnto.chainPar_twist_chT | exact GlobalTheory.ChainOnto.chainPar_twist_chT | (intros; apply GlobalTheory.ChainOnto.chainPar_twist_chT <;> assumption)
end

