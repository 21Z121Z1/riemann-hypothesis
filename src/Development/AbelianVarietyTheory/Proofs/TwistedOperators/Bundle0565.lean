import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0547
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IdempotentMulAddOneSubInverse
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0079
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0081
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1155
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SupportedSubgroupSplitCommutePrimeIdempotents
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0235
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0137
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0524
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0540
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1868
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.TwistPlacesOffPrimeQZero
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0004
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0006
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0019
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ToricSymbols
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0521
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0533
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0296
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLowestKTypeFockMapThetaVectors
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DualTypePlacesIsSplitNonconjugateOfAdmissible
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0166
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0164
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IdempotentMulEqZeroOfOrthogonal
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0131
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHasLocalSmall
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0006
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1858
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0216
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0548
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0513
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.SqNormIntegralFundamentalDomainEqL2NormSq
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0027
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0010
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0500
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContDiffDerivSnoc
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0549
import Development.AbelianVarietyTheory.Proofs.HeightProofs.TypeAtOfDiscreteSeries
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0091
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.DiscreteSeriesHermitianUniqueOfClassification
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHeightLeTwoMulQuotHeight
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0372
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0538

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SmulMtCutPartCompl
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.ExpansionInvariance
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.ExpansionInvariance

open GlobalTheory.IdemSupport

variable {D : D7}

open Classical in

def cutPart (a : AE D) (V : HSp D) (g : GA D V) : GA D V :=
  if h : a * a = a ∧ cA D a = a then ⟨piece h.1 g.1, piece_mem _ _ h.1 h.2 g.2⟩ else g

theorem mt_cutPart {a : AE D} (h : a * a = a) (hc : cA D a = a) (V : HSp D) (g : GA D V) :
    Formalism.L2.Theta.mt V (cutPart a V g) = a • Formalism.L2.Theta.mt V g + (1 - a) • (1 : Matrix _ _ (AE D)) := by
  have e : cutPart a V g = ⟨piece h g.1, piece_mem _ _ h hc g.2⟩ := dif_pos ⟨h, hc⟩
  rw [e]
  rfl

end GlobalTheory.ExpansionInvariance

namespace GlobalTheory.ExpansionInvariance

open GlobalTheory.IdemSupport

variable {D : D7}

theorem idem_conj_sum {e : AE D} (he : e * e = e) (hc : e * cA D e = 0) :
    (e + cA D e) * (e + cA D e) = e + cA D e ∧ cA D (e + cA D e) = e + cA D e := by
  have h1 : cA D e * cA D e = cA D e := by rw [← RingHom.map_mul, he]
  refine ⟨by linear_combination he + h1 + 2 * hc, ?_⟩
  rw [RingHom.map_add, GlobalTheory.SplitOnto.cA_cA, add_comm]

theorem idem_compl {f : AE D} (hf : f * f = f ∧ cA D f = f) : (1 - f) * (1 - f) = 1 - f ∧ cA D (1 - f) = 1 - f := by
  refine ⟨by linear_combination hf.1, ?_⟩
  rw [RingHom.map_sub, RingHom.map_one, hf.2]

theorem cutPart_mul {f : AE D} (hf : f * f = f ∧ cA D f = f) (V : HSp D) (g : GA D V) :
    g = cutPart f V g * cutPart (1 - f) V g := by
  have h2 := idem_compl hf
  refine GlobalTheory.IdemSupport.mt_inj V ?_
  rw [GlobalTheory.IdemSupport.mt_mul, mt_cutPart hf.1 hf.2, mt_cutPart h2.1 h2.2, sub_sub_cancel]
  exact (mix_split hf.1 rfl rfl).symm

theorem suppAt_cutPart {e : AE D} (he : e * e = e) (hc : e * cA D e = 0) (V : HSp D) (g : GA D V) :
    SuppAt e V (cutPart (e + cA D e) V g) := by
  have hf := idem_conj_sum he hc
  exact (supp_iff _ _).2 (smul_mix hf.1 (mt_cutPart hf.1 hf.2 V g))

theorem smul_mt_cutPart_compl {e : AE D} (he : e * e = e) (hc : e * cA D e = 0) (V : HSp D) (g : GA D V) :
    e • Formalism.L2.Theta.mt V (cutPart (1 - (e + cA D e)) V g) = e • (1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)) := by
  have hf := idem_conj_sum he hc
  have h2 := idem_compl hf
  rw [mt_cutPart h2.1 h2.2, sub_sub_cancel, smul_add, smul_smul, smul_smul]
  have k1 : e * (1 - (e + cA D e)) = 0 := by linear_combination -he - hc
  have k2 : e * (e + cA D e) = e := by linear_combination he + hc
  rw [k1, k2, zero_smul, zero_add]

end GlobalTheory.ExpansionInvariance

namespace GlobalTheory.ExpansionInvariance

variable {D : D7}

theorem actO_cutPart_compl {S T : HSp D} {e : AE D} (he : e * e = e) (hc : e * cA D e = 0) (g : GA D S) {z : WO S T}
    (hz : IsHalf e z) : actO S T (cutPart (1 - (e + cA D e)) S g)⁻¹ 1⁻¹ z = z := by
  have hz' : e • z = z := Matrix.ext fun i j => hz i j
  unfold actO
  rw [inv_inv, inv_one, GlobalTheory.IdemSupport.mt_one, Matrix.one_mul]
  conv_lhs => rw [← hz']
  rw [Matrix.smul_mul, ← Matrix.mul_smul, smul_mt_cutPart_compl he hc, Matrix.mul_smul, Matrix.mul_one, hz']

theorem halfInd_cutPart {S T : HSp D} {e : AE D} (he : e * e = e) (hc : e * cA D e = 0) (Λ : AddSubgroup (WO S T))
    (g : GA D S) (x : WO S T) :
    halfInd e Λ (actO S T (cutPart (e + cA D e) S g)⁻¹ 1⁻¹ x) = halfInd e Λ (actO S T g⁻¹ 1⁻¹ x) := by
  have hf := idem_conj_sum he hc
  have hg : g = cutPart (e + cA D e) S g * cutPart (1 - (e + cA D e)) S g := cutPart_mul hf S g
  have key : actO S T g⁻¹ 1⁻¹ x = actO S T (cutPart (1 - (e + cA D e)) S g)⁻¹ 1⁻¹
      (actO S T (cutPart (e + cA D e) S g)⁻¹ 1⁻¹ x) := by
    rw [← GlobalTheory.SplitLinear.actO_mul, ← mul_inv_rev, ← hg, inv_one, mul_one]
  rw [key]
  by_cases hy : IsHalf e (actO S T (cutPart (e + cA D e) S g)⁻¹ 1⁻¹ x)
  · rw [actO_cutPart_compl he hc g hy]
  · unfold halfInd
    rw [if_neg fun h => hy h.2, if_neg fun h => hy (GlobalTheory.ThetaMove.isHalf_of_act _ _ h.2)]

end GlobalTheory.ExpansionInvariance

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SmulOfMapsInlMemS
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.VacAny
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames GlobalTheory.BigNZ GlobalTheory.AdelicU GlobalTheory.WeilM
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ Num IsTripleOf IsDatumA IsDatumB skewGram mulG colV adjV₁)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chars Rep IsTriple Acts SInf At latAtV realAd evI)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.FlipMatch

noncomputable section

namespace GlobalTheory.SmallDat

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {i j : ℕ}

theorem ofMaps_inlS (t : T) (e : Num G i j) (x : HomA G t i j × HomB G i j) (p : Fin (spW₁ G i j).rank)
    (k : Fin (spV G i j).rank) : ofMaps t e x p (e (.inl k)) = GlobalTheory.BigDat.divG (spW₁ G i j) x.1 k p := by
  simp only [ofMaps, submatrix_apply, id, Equiv.symm_apply_apply, fromCols_apply_inl, transpose_apply]

theorem ofMaps_inrS (t : T) (e : Num G i j) (x : HomA G t i j × HomB G i j) (p : Fin (spW₁ G i j).rank)
    (k : Fin (spV₁ G i j).rank) : ofMaps t e x p (e (.inr k)) = cA D (GlobalTheory.BigDat.divG (spV₁ G i j) (-x.2) p k) := by
  simp only [ofMaps, submatrix_apply, id, Equiv.symm_apply_apply, fromCols_apply_inr, map_apply]

theorem ofMaps_genA (t : T) (e : Num G i j) (β : AF D.host.F) (a : D.host.E) (s : Fin (spW₁ G i j).rank → D.host.E)
    (r : Fin (spV G i j).rank → D.host.E) :
    ofMaps t e (Matrix.of fun i' j' => β ⊗ₜ[D.host.F] (a * r i' * ∑ k, star (s k) * (spW₁ G i j).gram k j'), 0) =
      β • GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F (vecMulVec (star s) (Sum.elim (a • r) 0 ∘ e.symm)) := by
  ext p q
  obtain ⟨k | k, rfl⟩ := e.surjective q
  · refine (ofMaps_inlS t e _ p k).trans ((GlobalTheory.BigDat.divG_gen (spW₁ G i j) β a s r k p).trans ?_)
    rw [GlobalTheory.BigDat.smul_incM_apply, vecMulVec_apply, Function.comp_apply, Equiv.symm_apply_apply, Sum.elim_inl, mul_comm]
    rfl
  · refine (ofMaps_inrS t e _ p k).trans ?_
    rw [GlobalTheory.BigDat.smul_incM_apply, vecMulVec_apply, Function.comp_apply, Equiv.symm_apply_apply, Sum.elim_inr, neg_zero,
      GlobalTheory.BigDat.divG_zero, Pi.zero_apply, mul_zero, TensorProduct.tmul_zero]
    exact map_zero _

theorem ofMaps_genB (t : T) (e : Num G i j) (β : AF D.host.F) (a : D.host.E) (s : Fin (spV₁ G i j).rank → D.host.E)
    (r : Fin (spW₁ G i j).rank → D.host.E) :
    ofMaps t e (0, Matrix.of fun i' j' => β ⊗ₜ[D.host.F] (a * r i' * ∑ k, star (s k) * (negSp (spV₁ G i j)).gram k j')) =
      β • GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F (vecMulVec (star r) (Sum.elim 0 (star (a • star s)) ∘ e.symm)) := by
  have hneg : -(Matrix.of fun i' j' => β ⊗ₜ[D.host.F] (a * r i' * ∑ k, star (s k) * (negSp (spV₁ G i j)).gram k j') :
      Matrix _ _ (AE D)) = Matrix.of fun i' j' => β ⊗ₜ[D.host.F] (a * r i' * ∑ k, star (s k) * (spV₁ G i j).gram k j') := by
    ext p q
    simp only [Matrix.neg_apply, of_apply, negSp_gram, Matrix.neg_apply, mul_neg, Finset.sum_neg_distrib, neg_neg,
      TensorProduct.tmul_neg]
  ext p q
  obtain ⟨k | k, rfl⟩ := e.surjective q
  · refine (ofMaps_inlS t e _ p k).trans ((congrFun (congrFun (GlobalTheory.BigDat.divG_zero (spW₁ G i j)) k) p).trans ?_)
    rw [GlobalTheory.BigDat.smul_incM_apply, vecMulVec_apply, Function.comp_apply, Equiv.symm_apply_apply, Sum.elim_inl,
      Pi.zero_apply, mul_zero, TensorProduct.tmul_zero]
    rfl
  · refine (ofMaps_inrS t e _ p k).trans ?_
    rw [GlobalTheory.BigDat.smul_incM_apply, vecMulVec_apply, Function.comp_apply, Equiv.symm_apply_apply, Sum.elim_inr, hneg,
      GlobalTheory.BigDat.divG_gen]
    change β ⊗ₜ[D.host.F] star (a * r p * star (s k)) = β ⊗ₜ[D.host.F] (star (r p) * star (a * star (s k)))
    rw [← star_mul']
    congr 2
    ring

theorem smul_ofMaps_inl_memS {t : T} {e : Num G i j} {Bs : Base D.host.F D.host.E} {Γ : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.Geo G i j}
    {X : Chars D.host.F D.host.E} (h : IsDoublyCompatible t i j e Bs Γ X) (v : Pl D.host.F) {x : HomA G t i j}
    (hx : x ∈ latA G t i j) : GlobalTheory.LatVac.liftV v 1 • ofMaps t e (x, 0) ∈ latAtV Γ.V' Γ.W v := by
  refine GlobalTheory.BigDat.map_mem_of_closure ((DistribMulAction.toAddMonoidHom (PtS G i j) (GlobalTheory.LatVac.liftV v 1)).comp
    ((maps t e).symm.toLinearMap.toAddMonoidHom.comp (AddMonoidHom.inl _ _))) ?_ hx
  rintro _ ⟨α, hα, -, a, ha, s, hs, r, hr, rfl⟩
  exact (congrArg (fun z => GlobalTheory.LatVac.liftV v 1 • z ∈ latAtV Γ.V' Γ.W v) (ofMaps_genA t e (pairA _ 0 α) a s r)).mpr
    (GlobalTheory.BigDat.one_smul_gen_mem _ _ v hα (h.2.ge (GlobalTheory.BigDat.star_mem_conjSub hs))
      (h.1.2.1.ge (GlobalTheory.BigDat.pair_mem e (GlobalTheory.BigDat.smul_mem_scLat_of_mem ha hr) (zero_mem _))))

theorem smul_ofMaps_inr_memS {t : T} {e : Num G i j} {Bs : Base D.host.F D.host.E} {Γ : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.Geo G i j}
    {X : Chars D.host.F D.host.E} (h : IsDoublyCompatible t i j e Bs Γ X) (v : Pl D.host.F) {x : HomB G i j}
    (hx : x ∈ latB G i j) : GlobalTheory.LatVac.liftV v 1 • ofMaps t e (0, x) ∈ latAtV Γ.V' Γ.W v := by
  refine GlobalTheory.BigDat.map_mem_of_closure ((DistribMulAction.toAddMonoidHom (PtS G i j) (GlobalTheory.LatVac.liftV v 1)).comp
    ((maps t e).symm.toLinearMap.toAddMonoidHom.comp (AddMonoidHom.inr _ _))) ?_ hx
  rintro _ ⟨α, hα, -, a, ha, s, hs, r, hr, rfl⟩
  exact (congrArg (fun z => GlobalTheory.LatVac.liftV v 1 • z ∈ latAtV Γ.V' Γ.W v) (ofMaps_genB t e (pairA _ 0 α) a s r)).mpr
    (GlobalTheory.BigDat.one_smul_gen_mem _ _ v hα (h.2.ge (GlobalTheory.BigDat.star_mem_conjSub hr))
      (h.1.2.1.ge (GlobalTheory.BigDat.pair_mem e (zero_mem _)
        (GlobalTheory.BigDat.star_mem_conjSub (GlobalTheory.BigDat.smul_mem_scLat_of_mem ha (GlobalTheory.BigDat.star_mem_conjSub hs))))))

theorem latPtS_le_latAtV : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (t : T) (i j : ℕ) (e : Num G i j) (Bs : Base D.host.F D.host.E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.Geo G i j) (X : Chars D.host.F D.host.E), GlobalTheory.FlipMatch.IsDoublyCompatible t i j e Bs Γ X →
    ∀ v : Pl D.host.F, ∀ u ∈ GlobalTheory.SmallDat.latPtS t e v, u ∈ latAtV Γ.V' Γ.W v := by
  intro D T L sc G t i j e Bs Γ X h v u hu
  obtain ⟨hat, h1, h2⟩ := hu
  have e1 : GlobalTheory.LatVac.liftV v 1 • u = u := by
    have := hat (1 - GlobalTheory.LatVac.liftV v 1) (by rw [map_sub, map_one, GlobalTheory.LatVac.evFin_liftV, sub_self])
    rw [sub_smul, one_smul, sub_eq_zero] at this
    exact this.symm
  have e2 : u = ofMaps t e (mapA t e u, 0) + ofMaps t e (0, mapB e u) :=
    ((ofMaps_maps t e u).symm.trans (congrArg (ofMaps t e) (Prod.ext (add_zero _).symm (zero_add _).symm))).trans
      (map_add (maps t e).symm (mapA t e u, 0) (0, mapB e u))
  have e3 := add_mem (smul_ofMaps_inl_memS h v h1) (smul_ofMaps_inr_memS h v h2)
  rwa [← smul_add, ← e2, e1] at e3

end GlobalTheory.SmallDat

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SplitOff
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3

open scoped TensorProduct
open GlobalTheory.MovedDict Formalism.L2.Ker GlobalTheory.SignedHC

open scoped TensorProduct
open GlobalTheory.MovedDict Formalism.L2.Ker GlobalTheory.SignedHC

noncomputable section

namespace GlobalTheory.MovedKappaEx

def OffPrime {D : D7} (e : Formalism.L2.Theta.AE D) (q : ℕ) : Prop :=
  ∀ v ε, IsPlaceIdem D v ε → e + cA D e = algebraMap (AF D.host.F) (Formalism.L2.Theta.AE D) ε → ((q : 𝓞 D.host.F)) ∉ v.asIdeal

def splitOff {D : D7} (V : HSp D) (Q : Finset ℕ) : Subgroup (GfC V) :=
  Subgroup.closure {g | ∃ e, IsSplitIdem D e ∧ (∀ q ∈ Q, OffPrime e q) ∧ SuppAt e V (g : GA D V)}

def RatFin {D : D7} (V : HSp D) (g : GfC V) : Prop := ∃ γ ∈ GQ V, finHom V γ = finHom V (g : GA D V)

def UnitAt (q : ℕ) [Fact q.Prime] (c : ℂ) : Prop := ∀ lam : Qbar →+* ℂ_[q], ‖lamC lam c‖ = 1

section
variable {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type}
    {A : FamIn D.what₂.LL Γ Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks}

def JetKap (ch : Choice R) (p : Pair T) (x : FinPt ch.G p.small) (y : FinPt ch.G p.big) (κ : ℂ) : Prop :=
  ∀ k : FVar D (ch.G.pT p).rank (ch.G.pS p).rank →₀ ℕ,
      fockIn ch.W ch.S.N.frC p (ch.W.om p (ch.G.toPair p ((x * ch.S.N.u p.small : FinPt ch.G p.small) : Formalism.L2.Theta.GA D (ch.G.V p.small)) ((y * ch.S.N.u p.big : FinPt ch.G p.big) : Formalism.L2.Theta.GA D (ch.G.V p.big))) (ch.S.Z.vac p))
        (MvPolynomial.monomial k 1) 0 = ch.S.Z.c0 p * opp p ((k.prod fun v e => period ch.S.Z.δ v.1 ^ e) *
          Formalism.MainNotions.GL3Theta.applyAt0 D (MvPolynomial.monomial k 1) fun z => κ * Iop D (tor0 D D.host.ccK ch.S.Z.δ) (La0 D (tor0 D D.host.ccK ch.S.Z.δ) _ _) (Formalism.MainNotions.TaylorLogMetric.La D (tor0 D D.host.ccK ch.S.Z.δ) (GlobalTheory.MovedDict.srcLat ch.S.toGridChoice p x y) (GlobalTheory.MovedDict.tgtLat ch.S.toGridChoice p x y)) (ch.S.Z.e0 p) z)

end

end GlobalTheory.MovedKappaEx
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.StandardPairFirstInvariantCongruenceOneStatement
section
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
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.standardPairFirst_invariant_congruenceOne : ∀ (D : D7) (A WW : HSp D) (ν : (AE D)ˣ →* Circle) (e : AE D) (Sf : Finset (Formalism.L2.DIV.Pl D.host.E)), IsIdemSum e Sf → ∀ (I : Ideal (𝓞 D.host.E)) (βA : GL (Fin A.rank) (Lev.EAf D)) (βW : GL (Fin WW.rank) (Lev.EAf D)) (N : ℕ), 0 < N → ((N : ℕ) : 𝓞 D.host.E) ∈ I → (∀ w ∈ Sf, ((N : ℕ) : 𝓞 D.host.E) ∈ w.asIdeal) → (∀ u : (AE D)ˣ, infPart D (u : AE D) = 1 → (∃ w ∈ Formalism.L2.Herm.intAf D.host.F D.host.E, toEAf D (u : AE D) = 1 + (N : Lev.EAf D) * w) → (∃ w ∈ Formalism.L2.Herm.intAf D.host.F D.host.E, toEAf D ((u⁻¹ : (AE D)ˣ) : AE D) = 1 + (N : Lev.EAf D) * w) → ν u = 1) → ∀ (κ : GA D WW) (z : GL (Fin WW.rank) (Formalism.L2.Herm.intAf D.host.F D.host.E)), Formalism.L2.DIV.frGL βW z = Lev.finE WW κ → (∀ a b, ∃ w ∈ Formalism.L2.Herm.intAf D.host.F D.host.E, ((z.1 a b : Formalism.L2.Herm.intAf D.host.F D.host.E) : Lev.EAf D) - (1 : Matrix (Fin WW.rank) (Fin WW.rank) (Lev.EAf D)) a b = (N : Lev.EAf D) * w) → ∀ x, GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.stdFst ν e I A WW βA βW (actO (GlobalTheory.Grid.neg A) WW 1 κ x) = GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.stdFst ν e I A WW βA βW x := by
  first | exact @GlobalTheory.StdFstInv.stdFst_actO | exact GlobalTheory.StdFstInv.stdFst_actO | (intros; apply GlobalTheory.StdFstInv.stdFst_actO <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.StepVecCongr
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.ChainCol

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

open Classical in

def extDat {m n : ℕ} (e e' : AE D) (Λ : AddSubgroup (Mx D m n)) (φ : Mx D m n → ℂ) : Mx D m n → ℂ :=
  fun x => if IsHalf e x ∧ x.map ((e - e') * ·) ∈ Λ then φ (x.map (e' * ·)) else 0

open Classical in

def stepDat (S T : HSp D) (βS : GL (Fin S.rank) (EAf D)) (βT : GL (Fin T.rank) (EAf D))
    (LS : LevDat D.host.E ℂ S.rank) (χj ξ : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (Q : Finset (Pl D.host.E)) (e : AE D) :
    WO S T → ℂ :=
  fun x => if IsHalf e x ∧ IsIntM (frMapO S T βS βT x) then
      omegaG LS χj (fun PP => redM PP (frMapO S T βS βT x)) * omegaQ Q LS.r ξ 1 (fun PP => redM PP (frMapO S T βS βT x))
    else 0

theorem r_le_colY {T : Type} (L : LevCh D T) (j : ℕ) : D.R.r ≤ (columnBlock L j).sp.rank := by
  rcases j with _ | j
  · exact r_le_Y 0
  · by_cases h : j + 1 < D.R.m
    · rw [colY_lt L h]; exact r_le_Y _
    · rw [show columnBlock L (j + 1) = ⟨D.sp.X', L.ΛX⟩ from if_neg h]; exact r_le_X

def colDat {T : Type} (L : LevCh D T) (t : T) (j : ℕ) : LevDat D.host.E ℂ (columnBlock L j).sp.rank :=
  Formalism.IndefR.Lev.datY _ D.R.r D.R.t j (r_le_colY L j) L.Pg (L.Q t) (LevelP.triv L.Pg D.R.r ℂ) L.chi (L.xiR t) Formalism.IndefR.Lev.Frm.B

theorem lsp_heq {X : LSp D} {S : HSp D} {Λ : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)} (h : X = ⟨S, Λ⟩) :
    X.sp = S ∧ HEq X.lat Λ := by
  subst h; exact ⟨rfl, HEq.rfl⟩

theorem datY_heq {n n' : ℕ} (h : n = n') (r t j : ℕ) (hr : r ≤ n) (hr' : r ≤ n') (Pg Q : Finset (Pl D.host.E))
    (P : LevelP Pg r ℂ) (χ : ℕ → ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (ξ : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ)
    (fr : Formalism.IndefR.Lev.Frm) :
    HEq (Formalism.IndefR.Lev.datY n r t j hr Pg Q P χ ξ fr) (Formalism.IndefR.Lev.datY n' r t j hr' Pg Q P χ ξ fr) := by
  subst h; rfl

theorem stepVec_congr {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {S S' T T' : HSp D} (hS : S = S') (hT : T = T')
    {sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ} {sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ}
    {sS' : D.what₂.Tau → Matrix (Fin S'.rank) (Fin S'.rank) ℂ} {sT' : D.what₂.Tau → Matrix (Fin T'.rank) (Fin T'.rank) ℂ}
    {ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)} {ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)}
    {ΛS' : Submodule (𝓞 D.host.E) (Fin S'.rank → D.host.E)} {ΛT' : Submodule (𝓞 D.host.E) (Fin T'.rank → D.host.E)}
    {βS : GL (Fin S.rank) (EAf D)} {βT : GL (Fin T.rank) (EAf D)} {βS' : GL (Fin S'.rank) (EAf D)} {βT' : GL (Fin T'.rank) (EAf D)}
    {LS : LevDat D.host.E ℂ S.rank} {LS' : LevDat D.host.E ℂ S'.rank} {χj ξ : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ}
    {Q : Finset (Pl D.host.E)} {f₀ f : WO S T → ℂ} {f₀' f' : WO S' T' → ℂ}
    (h1 : HEq sS sS') (h2 : HEq sT sT') (h3 : HEq ΛS ΛS') (h4 : HEq ΛT ΛT') (h5 : HEq βS βS') (h6 : HEq βT βT')
    (h7 : HEq LS LS') (h8 : HEq f₀ f₀') (h9 : HEq f f')
    (h : IsStepVecOf ψ θ S T sS sT ΛS ΛT βS βT LS χj Q ξ f₀ f) :
    IsStepVecOf ψ θ S' T' sS' sT' ΛS' ΛT' βS' βT' LS' χj Q ξ f₀' f' := by
  subst hS hT
  cases h1; cases h2; cases h3; cases h4; cases h5; cases h6; cases h7; cases h8; cases h9
  exact h

end GlobalTheory.ChainCol
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SymplecticFormOffIdempotentPartOrthogonalHalf
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

noncomputable section

namespace GlobalTheory.IdemOffOrth

theorem symplO_compl_half : ∀ (D : D7) (S T : HSp D) (P : Finset (Formalism.L2.DIV.Pl D.host.E)) (e : AE D), IsIdemSum e P → ∀ w x : WO S T, (IsHalf e x ∨ IsHalf (cA D e) x) → symplO S T ((1 - e - cA D e) • w) x = 0 := by
  intro D S T P e he w x hx
  have h1 : e * e = e := (GlobalTheory.PlaceModelSum.isOrthSum_of_isIdemSum he).idem
  have h2 : e * cA D e = 0 := he.2
  have c1 : cA D e * cA D e = cA D e := by rw [← map_mul, h1]
  have hz : symplO S T (0 : WO S T) x = 0 := by
    have := GlobalTheory.BigDat.symplO_cA_smul S T (0 : AE D) w x
    rw [map_zero, zero_smul, zero_smul, GlobalTheory.BigDat.symplO_zero_right'] at this
    exact this.symm
  rcases hx with hx | hx
  · have hxe : x = cA D (cA D e) • x := by
      rw [GlobalTheory.DualPairCheck.cA_cA]; exact (GlobalTheory.BigDat.smul_of_isHalf hx).symm
    rw [hxe, GlobalTheory.BigDat.symplO_cA_smul, smul_smul]
    have : cA D e * (1 - e - cA D e) = 0 := by linear_combination -c1 - (mul_comm e (cA D e) ▸ h2 : cA D e * e = 0)
    rw [this, zero_smul]; exact hz
  · rw [← GlobalTheory.BigDat.smul_of_isHalf hx, GlobalTheory.BigDat.symplO_cA_smul, smul_smul]
    have : e * (1 - e - cA D e) = 0 := by linear_combination -h1 - h2
    rw [this, zero_smul]; exact hz

end GlobalTheory.IdemOffOrth
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaLiftBoundedNormStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.theta_lift_bounded_norm : GlobalTheory.FunPr.Hypotheses₂ → ∀ (D : D7), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.Sizes D → ∀ (G₀ : Type) [Group G₀] [Fintype G₀] (Pl0 T : Type) (A : FamIn D.what₂.LL G₀ Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (G : GlobalTheory.Grid.GridPre R), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.RowBase R → G.Is → ∀ i, i < D.R.m → ∃ N : ℕ, ∀ Φ, IsThetaFunO R.ψ (GlobalTheory.Grid.neg (G.P (i + 1)).V) (G.P i).V Φ → ∃ C : NNReal, ∀ f : GA D (G.P (i + 1)).V → ℂ, GlobalTheory.Size.growthSize (G.P i).V N (fun h => ∫ g in (G.mP (i + 1)).fd, thetaKO (G.dn i).ω g h Φ * f g ∂(G.mP (i + 1)).ν) ≤ (C : ENNReal) * GlobalTheory.IndefiniteRowSideFullHecke.RapidDecayLift.decayInt (G.mP (i + 1)).ν (G.mP (i + 1)).fd N f := by
  first | exact @GlobalTheory.DownLiftGrowth.growthSize_lift_le_decayInt | exact GlobalTheory.DownLiftGrowth.growthSize_lift_le_decayInt | (intros; apply GlobalTheory.DownLiftGrowth.growthSize_lift_le_decayInt <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaLiftDiagonalRapidDecayStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.theta_lift_diagonal_rapid_decay : GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.LiftsCuspidal → GlobalTheory.FunPr.Hypotheses₂ → ∀ (D : D7), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.Sizes D → ∀ (G₀ : Type) [Group G₀] [Fintype G₀] (Pl0 T : Type) (A : FamIn D.what₂.LL G₀ Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (G : GlobalTheory.Grid.GridPre R), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.RowBase R → G.Is → ∀ i, i < D.R.m → ∀ Φ, IsThetaFunO R.ψ (GlobalTheory.Grid.neg (G.P (i + 1)).V) (G.P i).V Φ → ∀ F : (G.P (i + 1)).Maps, F ∈ (G.P (i + 1)).Cusp R.θ → ∀ v : SmT (G.P (i + 1)).M, (∀ h, IntegrableOn (fun g => thetaKO (G.dn i).ω g h Φ * F v g) (G.mP (i + 1)).fd (G.mP (i + 1)).ν) → ∀ C : Set (GA D (G.P i).V), IsCompact C → ∀ ε : ℝ, 0 < ε → ∃ (n : ℕ) (f : Fin n → (WO (G.P (i + 1)).V (G.P i).V → ℂ)) (p : Fin n → GlobalTheory.Grid.Pol (G.P (i + 1)) (G.P i)), (∀ l, GlobalTheory.Grid.IsFinVec R.ψ R.θ true (G.P (i + 1)) (G.P i) (f l)) ∧ ∀ h ∈ C, ‖(∫ g in (G.mP (i + 1)).fd, thetaKO (G.dn i).ω g h Φ * F v g ∂(G.mP (i + 1)).ν) - ∑ l, ∫ g in (G.mP (i + 1)).fd, thetaKO (G.dn i).ω g h (GlobalTheory.Grid.fock R.ψ R.θ true (G.P (i + 1)) (G.P i) (f l) (p l)) * F v g ∂(G.mP (i + 1)).ν‖ < ε := by
  first | exact @GlobalTheory.DownApprox.approx | exact GlobalTheory.DownApprox.approx | (intros; apply GlobalTheory.DownApprox.approx <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaLiftHorizontalAlgebraicCoeffsStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.theta_lift_horizontal_algebraic_coeffs : GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.LiftsCuspidal → GlobalTheory.FunPr.Hypotheses₂ → ∀ (D : D7), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.Sizes D → ∀ (G₀ : Type) [Group G₀] [Fintype G₀] (Pl0 T : Type) (A : FamIn D.what₂.LL G₀ Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (G : GlobalTheory.Grid.GridPre R), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.RowBase R → G.Is → ∀ t i j, i ≤ D.R.m → j < D.R.m → ∀ Φ, IsThetaFunO R.ψ (G.V i j).V (G.V i (j + 1)).V Φ → ∃ a b : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ h g, ‖thetaKO (G.th t i j).ω h g Φ‖ ≤ C * GlobalTheory.Grow.quotHeight (G.V i j).V h ^ a * GlobalTheory.Grow.quotHeight (G.V i (j + 1)).V g ^ b := by
  first | exact @GlobalTheory.ThetaArrowGrowth.thetaKO_le_quotHeight_arrow | exact GlobalTheory.ThetaArrowGrowth.thetaKO_le_quotHeight_arrow | (intros; apply GlobalTheory.ThetaArrowGrowth.thetaKO_le_quotHeight_arrow <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaLiftHorizontalExistsCoeffs
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.ThetaArrowApprox

theorem thetaKO_approx_fock : GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.LiftsCuspidal → GlobalTheory.FunPr.Hypotheses₂ → ∀ (D : D7), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.Sizes D → ∀ (G₀ : Type) [Group G₀] [Fintype G₀] (Pl0 T : Type) (A : FamIn D.what₂.LL G₀ Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (G : GlobalTheory.Grid.GridPre R), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.RowBase R → G.Is → ∀ t i j, i ≤ D.R.m → j < D.R.m → ∀ Φ, IsThetaFunO R.ψ (G.V i j).V (G.V i (j + 1)).V Φ → ∃ a b : ℕ, ∀ ε : ℝ, 0 < ε → ∃ (n : ℕ) (fs : Fin n → (WO (G.V i j).V (G.V i (j + 1)).V → ℂ)) (ps : Fin n → PolF D (G.V i (j + 1)).V.rank (G.V i j).V.rank), (∀ l, GlobalTheory.Grid.IsFinVec R.ψ R.θ false (G.V i j) (G.V i (j + 1)) (fs l)) ∧ ∀ h g, ‖thetaKO (G.th t i j).ω h g (∑ l, GlobalTheory.Grid.fock R.ψ R.θ false (G.V i j) (G.V i (j + 1)) (fs l) (ps l)) - thetaKO (G.th t i j).ω h g Φ‖ ≤ ε * GlobalTheory.Grow.quotHeight (G.V i j).V h ^ a * GlobalTheory.Grow.quotHeight (G.V i (j + 1)).V g ^ b := by
  intro _ _ D _ G₀ _ _ Pl0 T A Ks _ _ _ R G hRB hG t i j hi hj Φ hΦ
  have hω : IsWeilDatumO R.ψ (G.V i j).V (G.V i (j + 1)).V _ _ (G.th t i j).ω :=
    (GlobalTheory.Grid.isWeil_false _ _ _ _ _ _).1 (hG.arrows.th t i j hi hj).weil
  obtain ⟨a, ha⟩ := GlobalTheory.KernelApprox.exists_kernel_approx hRB.inf hω
    (fun X => ∃ (n : ℕ) (fs : Fin n → (WO (G.V i j).V (G.V i (j + 1)).V → ℂ)) (ps : Fin n → PolF D (G.V i (j + 1)).V.rank (G.V i j).V.rank),
      (∀ l, GlobalTheory.Grid.IsFinVec R.ψ R.θ false (G.V i j) (G.V i (j + 1)) (fs l)) ∧
        X = ∑ l, GlobalTheory.Grid.fock R.ψ R.θ false (G.V i j) (G.V i (j + 1)) (fs l) (ps l)) hΦ
    (fun U hU hΦU μ 𝓕 hμ d ε hε => by
      obtain ⟨n, fs, ps, h1, h2, h3⟩ := GlobalTheory.T.gridDownArrow_thetaFunction_fock_dense_of_level D G₀ Pl0 T A Ks R G hRB hG t i j hi hj U hU Φ hΦU μ 𝓕 hμ d ε hε
      exact ⟨_, ⟨n, fs, ps, h1, rfl⟩, h2, h3⟩)
  refine ⟨a, a, fun ε hε => ?_⟩
  obtain ⟨X, ⟨n, fs, ps, hfs, rfl⟩, hX⟩ := ha ε hε
  exact ⟨n, fs, ps, hfs, fun h g => hX h g⟩

end GlobalTheory.ThetaArrowApprox

end
end

