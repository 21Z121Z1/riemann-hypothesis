import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.L2UnitaryRepresentationData
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsGrpDataMapHaar
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0189
import Formalism.LocalToGlobal.IndefiniteReal.ZeroPartEigenvalueConvention
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0032
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0010
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowLevelMatch
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.Bundle0001
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryIntegralAdelicElementExists
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0933
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0070
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IsSelfDualCLatFrame
import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.NatCastKPZero
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0210
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0316
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.DiscreteSeriesCharacter
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0009
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsAdmOnOfFiniteDimensional
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsFiniteUnitaryMoverStandardLattice
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0205
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0212
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0196

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.CoverHaarPushforwardSignatureUnitaryGroup
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.S Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum
open Formalism.IndefR.Mult (DSModel dualPar parA parB)
open Formalism.MainNotions.SchurIrreducible (AdmGK ARi ARiiiUp ARiiiDown ARiiiLine DiscreteSeriesBlattner admQ5)
open GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction hiding Mat
open GlobalTheory.IndefiniteRowSideFullHecke.BarMatrix (SignCompat plainMat barMat)
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (fockIp)
open GlobalTheory.Chain (signed)
open GlobalTheory.Chain.RealIt (LPol locS locT IsPolyIso)
open MeasureTheory Matrix
open scoped TensorProduct InnerProductSpace ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ArchRec

namespace GlobalTheory.ArchRec

theorem haar_of_proper {p q n : ℕ} (T : GrpData p q) (ε : Fin n → Bool) (μ : Measure (Formalism.REAL.UJ ε))
    [μ.IsHaarMeasure] (π : T.G →* Formalism.REAL.UJ ε) (hp : IsProperMap π) (hs : Function.Surjective π) :
    ∃ c : NNReal, c ≠ 0 ∧ Topology.IsQuotientMap π ∧ Measurable π ∧ Measure.map π T.haar = c • μ := by
  have hc : Continuous π := hp.continuous
  have ht : Filter.Tendsto π (Filter.cocompact T.G) (Filter.cocompact (Formalism.REAL.UJ ε)) := by
    refine Filter.hasBasis_cocompact.tendsto_right_iff.2 fun K hK => ?_
    have hK' : IsCompact (π ⁻¹' K) := hp.isCompact_preimage hK
    exact hK'.compl_mem_cocompact
  haveI hν : (Measure.map π T.haar).IsHaarMeasure := Measure.isHaarMeasure_map T.haar π hc hs ht
  refine ⟨Measure.haarScalarFactor (Measure.map π T.haar) μ,
    (Measure.haarScalarFactor_pos_of_isHaarMeasure _ _).ne', hp.isClosedMap.isQuotientMap hc hs,
    hc.measurable, ?_⟩
  exact Measure.isMulLeftInvariant_eq_smul _ μ

open GlobalTheory.RealPar.SqInt (reixHom continuous_reixHom) in

noncomputable def reixUJ {p q n : ℕ} {ε : Fin n → Bool} {e : Ix p q ≃ Fin n} (h : SignCompat ε e) :
    Formalism.UG.Upq p q ≃ₜ* Formalism.REAL.UJ ε where
  toFun g := ⟨Units.map (reixHom e) g.1, GlobalTheory.IndefiniteRowSideFullHecke.BarMatrix.plainMat_mem h g.2⟩
  invFun g := ⟨Units.map (reixHom e.symm) g.1, by
    have hg : (umat g)ᴴ * Formalism.REAL.Jm ε * umat g = Formalism.REAL.Jm ε := g.2
    change (Matrix.reindex e.symm e.symm (umat g))ᴴ * Formalism.UG.Jpq p q * Matrix.reindex e.symm e.symm (umat g) =
      Formalism.UG.Jpq p q
    have hJ : Formalism.UG.Jpq p q = Matrix.reindex e.symm e.symm (Formalism.REAL.Jm ε) := by
      rw [← GlobalTheory.IndefiniteRowSideFullHecke.BarMatrix.reindex_form h]; simp
    rw [hJ]
    simp only [Matrix.reindex_apply, Matrix.conjTranspose_submatrix, Matrix.submatrix_mul_equiv, hg]⟩
  left_inv g := Subtype.ext (Units.ext (by
    change Matrix.reindex e.symm e.symm (Matrix.reindex e e _) = _
    simp))
  right_inv g := Subtype.ext (Units.ext (by
    change Matrix.reindex e e (Matrix.reindex e.symm e.symm _) = _
    simp))
  map_mul' a b := Subtype.ext (map_mul (Units.map (reixHom e)) a.1 b.1)
  continuous_toFun := Continuous.subtype_mk (((continuous_reixHom e).units_map _).comp continuous_subtype_val) _
  continuous_invFun := Continuous.subtype_mk (((continuous_reixHom e.symm).units_map _).comp continuous_subtype_val) _

theorem cover_haar_map : ∀ (p q n : ℕ) (T : GrpData p q) (ε : Fin n → Bool) (e : Ix p q ≃ Fin n) (br : Bool) (μ : Measure (Formalism.REAL.UJ ε)), SignCompat ε e → μ.IsHaarMeasure → ∃ (π : T.G →* Formalism.REAL.UJ ε) (c : NNReal), c ≠ 0 ∧ (∀ g, umat (π g) = phi br e ((T.cov g : GL (Ix p q) ℂ) : Mat p q)) ∧ Topology.IsQuotientMap π ∧ Measurable π ∧ Measure.map π T.haar = c • μ := by
  intro p q n T ε e br μ h hμ
  obtain ⟨C, hC, -⟩ := GlobalTheory.LeviIso.exists_conj_gauge_invariant n ε
    (if br then starRingEnd ℂ else RingHom.id ℂ) (by cases br <;> simp)
  let π : T.G →* Formalism.REAL.UJ ε :=
    (C.toMonoidHom.comp (reixUJ h).toMonoidHom).comp (GlobalTheory.DetSqrtCover.covHom T)
  have hcov : IsProperMap (GlobalTheory.DetSqrtCover.covHom T) := GlobalTheory.DetSqrtCover.isProperMap_covU T
  have hp : IsProperMap π :=
    (C.toHomeomorph.isProperMap.comp (reixUJ h).toHomeomorph.isProperMap).comp hcov
  have hs : Function.Surjective π :=
    (C.surjective.comp (reixUJ h).surjective).comp (GlobalTheory.DetSqrtCover.surjective_covU T)
  obtain ⟨c, hc0, hq, hm, hmap⟩ := haar_of_proper T ε μ π hp hs
  refine ⟨π, c, hc0, fun g => ?_, hq, hm, hmap⟩
  have hre : umat (reixUJ h (GlobalTheory.DetSqrtCover.covHom T g)) =
      Matrix.reindex e e ((T.cov g : GL (Ix p q) ℂ) : Mat p q) :=
    GlobalTheory.RealPar.SqInt.reixHom_apply e _
  have hconj := hC (reixUJ h (GlobalTheory.DetSqrtCover.covHom T g))
  change umat (C (reixUJ h (GlobalTheory.DetSqrtCover.covHom T g))) = _
  refine hconj.trans ?_
  change (umat (reixUJ h (GlobalTheory.DetSqrtCover.covHom T g))).map _ = _
  rw [hre]
  cases br
  · ext i j
    simp [phi, plainMat]
  · ext i j
    simp [phi, barMat]

end GlobalTheory.ArchRec
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.CrdLatEqLatFrame
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField IsDedekindDomain
open scoped InnerProductSpace Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

open scoped TensorProduct

namespace GlobalTheory.ConjPlaceRed

section General

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem resS_conj_zero (τ : E →ₐ[F] E) (w w' : Pl E)
    (hc : ∀ c ∈ w.asIdeal, ∃ c' ∈ w'.asIdeal, (c' : E) = τ (c : E)) (s t : Formalism.L2.Herm.intAf F E)
    (ht : (t : E ⊗[F] Formalism.L2.Herm.Af F) = Formalism.UG.sigR τ (Formalism.L2.Herm.Af F) (s : E ⊗[F] Formalism.L2.Herm.Af F))
    (hs : resS F w s = 0) : resS F w' t = 0 := by
  let σ : Formalism.L2.Herm.intAf F E →+* Formalism.L2.Herm.intAf F E :=
    ((Formalism.UG.sigR τ (Formalism.L2.Herm.Af F)).comp
      (Formalism.L2.Herm.intAf F E).subtype).codRestrict _ (fun x => GlobalTheory.ResConjPlace.conj_mem_int τ x.2)
  have hts : t = σ s := Subtype.ext ht
  have h3 : idS F w.asIdeal ≤ (idS F w'.asIdeal).comap σ := by
    refine Ideal.map_le_iff_le_comap.2 fun c hcw => ?_
    obtain ⟨c', hc', hcc⟩ := hc c hcw
    have : σ (oToS F E c) = oToS F E c' := by
      apply Subtype.ext
      show τ (c : E) ⊗ₜ[F] _ = (c' : E) ⊗ₜ[F] _
      rw [hcc]; rfl
    rw [Ideal.mem_comap, Ideal.mem_comap, this]
    exact Ideal.mem_map_of_mem _ hc'
  rw [hts]
  rw [GlobalTheory.GeoActCompare.resS_eq_resI, GlobalTheory.GeoActCompare.resI_eq_zero_iff] at hs ⊢
  exact h3 hs

theorem resS_conj_ite (τ : E →ₐ[F] E) (w w' : Pl E)
    (hc : ∀ c ∈ w.asIdeal, ∃ c' ∈ w'.asIdeal, (c' : E) = τ (c : E)) (s t : Formalism.L2.Herm.intAf F E)
    (ht : (t : E ⊗[F] Formalism.L2.Herm.Af F) = Formalism.UG.sigR τ (Formalism.L2.Herm.Af F) (s : E ⊗[F] Formalism.L2.Herm.Af F))
    (b : Prop) [Decidable b] (hs : resS F w s = if b then 1 else 0) : resS F w' t = if b then 1 else 0 := by
  let c : Formalism.L2.Herm.intAf F E := if b then 1 else 0
  have hc1 : resS F w c = if b then 1 else 0 := by
    simp only [c]; split_ifs <;> simp
  have hc2 : resS F w' c = if b then 1 else 0 := by
    simp only [c]; split_ifs <;> simp
  have hcs : Formalism.UG.sigR τ (Formalism.L2.Herm.Af F) (c : E ⊗[F] Formalism.L2.Herm.Af F) = (c : E ⊗[F] Formalism.L2.Herm.Af F) := by
    simp only [c]; split_ifs <;> simp
  have h0 := resS_conj_zero τ w w' hc (s - c) (t - c) (by
    rw [AddSubgroupClass.coe_sub, AddSubgroupClass.coe_sub, map_sub, ht, hcs]) (by
    rw [map_sub, hs, hc1, sub_self])
  rw [map_sub, sub_eq_zero, hc2] at h0
  exact h0

end General

variable {D : D7}

theorem crdLat_eq_latFrame (V : HSp D) : Formalism.L2.Herm.crdLat V V.L0 = GlobalTheory.PlaceModel.latFrame V := by
  ext y
  rw [GlobalTheory.PlaceModel.mem_latFrame]
  constructor
  · rintro ⟨v, hv, rfl⟩
    have e : ∑ i, (Formalism.L2.Herm.crd V v) i • V.frame i = v := V.frame.sum_equivFun v
    show ∑ i, (Formalism.L2.Herm.crd V v) i • V.frame i ∈ V.L0
    rw [e]; exact hv
  · intro hy
    refine ⟨_, hy, ?_⟩
    show V.frame.equivFun (∑ i, y i • V.frame i) = y
    rw [← Module.Basis.equivFun_symm_apply, LinearEquiv.apply_symm_apply]

end GlobalTheory.ConjPlaceRed

namespace GlobalTheory.ConjPlaceRed

theorem Lv_eq_latFrame (D : D7) : Formalism.L2.SG.InstExistsPf.Lv D = GlobalTheory.PlaceModel.latFrame (Yc D 0) := by
  ext y
  rw [Formalism.L2.SG.InstExistsPf.mem_Lv]
  exact (GlobalTheory.PlaceModel.mem_latFrame (Yc D 0) y).symm

theorem mem_Lf (D : D7) (v : Fin (Yc D 0).rank → EAf D) :
    v ∈ Formalism.L2.Herm.hatL (F := D.host.F) (GlobalTheory.PlaceModel.latFrame (Yc D 0)) ↔
      v ∈ lamAf (F := D.host.F) (Formalism.L2.SG.InstExistsPf.Lv D) := by
  rw [Lv_eq_latFrame]
  exact (Set.ext_iff.1 (Formalism.IndefR.Eqv.lamAf_eq_hatL (V := Yc D 0) (GlobalTheory.PlaceModel.latFrame (Yc D 0))) v).symm

theorem mem_St_of_Kset (D : D7) (β : GL (Fin (Yc D 0).rank) (EAf D)) (x : (Formalism.L2.SG.InstExistsPf.instOf D).Gf)
    (hβ : IsFrame β (GlobalTheory.PlaceModel.latFrame (Yc D 0))) (hx : x ∈ (Formalism.L2.SG.InstExistsPf.instOf D).Kset) :
    x.1 ∈ St β := by
  have hS : ∀ v, v ∈ (Formalism.L2.SG.InstExistsPf.instOf D).Lf ↔
      (Formalism.L2.SG.InstExistsPf.instOf D).fmat x *ᵥ v ∈ (Formalism.L2.SG.InstExistsPf.instOf D).Lf := hx
  have hSi : ∀ v, v ∈ (Formalism.L2.SG.InstExistsPf.instOf D).Lf ↔
      (((x.1)⁻¹ : GL (Fin (Formalism.L2.SG.InstExistsPf.instOf D).n) _) : Matrix _ _ _) *ᵥ v ∈
        (Formalism.L2.SG.InstExistsPf.instOf D).Lf :=
    (Formalism.UG.stabGL (Formalism.L2.SG.InstExistsPf.instOf D).Lf).inv_mem hx
  refine (GlobalTheory.LevSplit.mem_St_iff β _ hβ (x.1 : GL (Fin (Yc D 0).rank) (EAf D))).2 ⟨fun y hy => (mem_Lf D _).2 ((hS y).1 ((mem_Lf D y).1 hy)),
    fun y hy => (mem_Lf D _).2 ((hSi y).1 ((mem_Lf D y).1 hy))⟩

set_option maxHeartbeats 1000000 in

theorem redFn_conj_eq_one : ∀ (D : D7) (β : GL (Fin (Yc D 0).rank) (EAf D)) (x : (Formalism.L2.SG.InstExistsPf.instOf D).Gf)
    (PP PP' : Formalism.L2.DIV.Pl D.host.E),
    IsFrame β (Formalism.L2.Herm.crdLat (Yc D 0) (Yc D 0).L0) → x ∈ (Formalism.L2.SG.InstExistsPf.instOf D).Kset →
    IsConjPl PP' PP → Formalism.L2.DIV.redFn β PP' x.1 = 1 → Formalism.L2.DIV.redFn β PP x.1 = 1 := by
  intro D β x PP PP' hβ hx hc h1
  rw [crdLat_eq_latFrame] at hβ
  have hsd := GlobalTheory.PlaceModel.isSelfDualC_latFrame (Yc D 0)
  obtain ⟨m, s, s', hs, hd⟩ := GlobalTheory.LatVacDual.dualFamily D (Yc D 0) _ hsd
  obtain ⟨G, hG⟩ := GlobalTheory.FrameGram.exists_unit_adelic star (Formalism.UG.sigR D.sp.cm.sig (Formalism.L2.Herm.Af D.host.F))
    (fun _ => GlobalTheory.LevSplit.sigR_int) (fun _ => rfl) (Yc D 0).gram β _ hβ (fun y hy => (hsd.2 y).1 hy) s s' hs hd
  obtain ⟨h, hh⟩ := mem_St_of_Kset D β x hβ hx
  have hU : β * Formalism.UG.bc (Formalism.L2.Herm.intAf D.host.F D.host.E).subtype h * β⁻¹ ∈
      Formalism.UG.UJ (Formalism.UG.sigR D.sp.cm.sig (Formalism.L2.Herm.Af D.host.F))
        ((Yc D 0).gram.map (Formalism.UG.inclE (F := D.host.F) (Formalism.L2.Herm.Af D.host.F))) := by
    have e : β * Formalism.UG.bc (Formalism.L2.Herm.intAf D.host.F D.host.E).subtype h * β⁻¹ = x.1 := hh
    rw [e]
    exact x.2
  have key := GlobalTheory.FrameMove.conj_gram_sub (Formalism.UG.sigR D.sp.cm.sig (Formalism.L2.Herm.Af D.host.F))
    (Formalism.L2.Herm.intAf D.host.F D.host.E) _ β G h hG hU
  rw [← hh, redFn_frGL] at h1 ⊢
  have h1' : Formalism.UG.bc (resS D.host.F PP') h⁻¹ = 1 := by rw [map_inv, h1, inv_one]
  have h2 : Formalism.UG.bc (resS D.host.F PP) (G * h * G⁻¹) = 1 := by
    apply Units.ext
    ext i j
    have hz : resS D.host.F PP' ((h⁻¹).val j i) = if j = i then 1 else 0 := by
      have e : ((Formalism.UG.bc (resS D.host.F PP') h⁻¹ : GL (Fin (Yc D 0).rank) (kP PP')) : Matrix _ _ (kP PP')) j i =
          resS D.host.F PP' ((h⁻¹).val j i) := rfl
      rw [← e, h1', Units.val_one, Matrix.one_apply]
    have h0 := resS_conj_ite D.sp.cm.sig PP' PP hc _ _ (key i j) (j = i) hz
    refine h0.trans ?_
    rw [Units.val_one, Matrix.one_apply]
    exact if_congr eq_comm rfl rfl
  rw [map_mul, map_mul, map_inv] at h2
  exact conj_eq_one_iff.1 h2

end GlobalTheory.ConjPlaceRed
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.EventuallyLocalIntegersIffPowerBasisCoordsAll
section
open MeasureTheory Set Filter Polynomial NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots GlobalTheory.TrEll
open GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups (mapH diagH)
open scoped TensorProduct ComplexConjugate Matrix

noncomputable section
namespace GlobalTheory.TrUnitLat

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {r : ℕ}
  (P : PPol σ r)

theorem map_mem_intLoc_fld {v : HeightOneSpectrum (𝓞 F)} {c : Fv F v ⊗[F] E} (hc : c ∈ intLoc F E v) :
    Algebra.TensorProduct.map (AlgHom.id F (Fv F v)) (IsScalarTower.toAlgHom F E (Fld P)) c ∈
      intLoc F (Fld P) v := by
  refine intLoc_induction (p := fun c => Algebra.TensorProduct.map (AlgHom.id F (Fv F v))
      (IsScalarTower.toAlgHom F E (Fld P)) c ∈ intLoc F (Fld P) v) (fun a ha x => ?_) (by simp)
    (fun y z hy hz => by rw [map_add]; exact add_mem hy hz) (fun y hy => by rw [map_neg]; exact neg_mem hy) hc
  rw [Algebra.TensorProduct.map_tmul]
  exact tmul_mem_intLoc ha ⟨algebraMap E (Fld P) x, x.2.algebraMap⟩

theorem eventually_mem_intLoc_iff_coordEquiv_mem :
    ∀ᶠ v : HeightOneSpectrum (𝓞 F) in cofinite, ∀ y : Fv F v ⊗[F] Fld P,
      y ∈ intLoc F (Fld P) v ↔ coordEquiv P (Fv F v) y ∈ latLoc F (stdLattice E r) v := by
  let b := RingOfIntegers.basis (Fld P)
  filter_upwards [eventually_all.2 fun i => eventually_all.2 fun j =>
      eventually_one_tmul_mem_intLoc (F := F) ((powB P).repr (b j : Fld P) i),
    eventually_all.2 fun i => eventually_one_tmul_mem_intLoc (F := F) (E := Fld P) (powB P i)] with v h1 h2 y
  rw [mem_latLoc_stdLattice]
  constructor
  · intro hy i
    rw [coordEquiv_apply]
    refine intLoc_induction (p := fun y => coordF P (Fv F v) i y ∈ intLoc F E v) (fun a ha x => ?_) (by simp)
      (fun y z hy hz => by rw [map_add]; exact add_mem hy hz) (fun y hy => by rw [map_neg]; exact neg_mem hy) hy
    rw [coordF_tmul]
    have e : (powB P).repr (x : Fld P) i = ∑ j, b.repr x j • (powB P).repr (b j : Fld P) i := by
      conv_lhs => rw [← b.sum_repr x]
      simp only [map_sum, map_zsmul, Finsupp.coe_finset_sum, Finset.sum_apply]
      refine Finset.sum_congr rfl fun j _ => ?_
      simp [← zsmul_eq_mul, map_zsmul]
    rw [e, TensorProduct.tmul_sum]
    refine sum_mem fun j _ => ?_
    rw [TensorProduct.tmul_smul]
    refine zsmul_mem ?_ _
    have e2 : a ⊗ₜ[F] ((powB P).repr (b j : Fld P) i) =
        (a ⊗ₜ[F] ((1 : 𝓞 E) : E)) * ((1 : Fv F v) ⊗ₜ[F] (powB P).repr (b j : Fld P) i) := by simp
    rw [e2]
    exact mul_mem (tmul_mem_intLoc ha 1) (h1 i j)
  · intro h
    rw [← coordInv_coordF P (Fv F v) y]
    refine sum_mem fun i _ => ?_
    rw [smul_eq_map_mul]
    exact mul_mem (map_mem_intLoc_fld P (h i)) (h2 i)

end GlobalTheory.TrUnitLat

theorem GlobalTheory.TrUnitLat.eventually_mem_intLoc_iff_coordEquiv_mem_all : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (r : ℕ) (P : PPol σ r), ∀ᶠ v : HeightOneSpectrum (𝓞 F) in cofinite, ∀ y : Fv F v ⊗[F] Fld P, y ∈ intLoc F (Fld P) v ↔ GlobalTheory.TrUnitLat.coordEquiv P (Fv F v) y ∈ latLoc F (stdLattice E r) v :=
  fun F E _ _ _ _ _ σ r P => GlobalTheory.TrUnitLat.eventually_mem_intLoc_iff_coordEquiv_mem P
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsCartanSystem
section
open MeasureTheory Matrix Filter Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.FlagMeas GlobalTheory.GKModule GlobalTheory.RealInd GlobalTheory.OpTrace
open GlobalTheory.SmoothGlob (lieSet)
open GlobalTheory.Dec (IsHaarSub HasInfChar IsSqIntIrr)
open GlobalTheory.Orb (ujMat ujRep CcMat IsBiFinite IsUnitEquiv IsCharFn IsRegSS cent HasOrbInt quotMeas)
open GlobalTheory.AutomorphicL2Unitary (IsTopIrreducible)
open GlobalTheory.HCChar GlobalTheory.Published GlobalTheory.Published.Langlands
open scoped InnerProductSpace Topology ENNReal ComplexConjugate

noncomputable section

namespace GlobalTheory.CartanFinite

variable {n : ℕ}

theorem exists_scale {G : Matrix (Fin n) (Fin n) ℂ} (hG : Gᴴ = G) {z : Fin n → ℂ} (hz : Function.Injective z)
    (h : (diagonal z)ᴴ * G * diagonal z = G) :
    ∃ d : Fin n → ℂ, (∀ a, d a ≠ 0) ∧ ∀ a b, ((diagonal d)ᴴ * G * diagonal d) a b ∈ ({0, 1, -1} : Finset ℂ) := by
  have h1 : ∀ a b, G a b ≠ 0 → conj (z a) * z b = 1 := fun a b hab => by
    have := congrFun (congrFun h a) b
    rw [diagonal_conjTranspose, mul_diagonal, diagonal_mul, Pi.star_apply, Complex.star_def] at this
    exact mul_right_cancel₀ hab (by linear_combination this)
  have h2 : ∀ a b, G a b ≠ 0 → ∑ c, G a c = G a b := fun a b hab => by
    refine Finset.sum_eq_single b (fun c _ hc => ?_) (by simp)
    by_contra hac
    have h0 : conj (z a) ≠ 0 := left_ne_zero_of_mul_eq_one (h1 a b hab)
    exact hc (hz (mul_left_cancel₀ h0 ((h1 a c hac).trans (h1 a b hab).symm)))
  have h3 : ∀ a, ∃ d : ℂ, d ≠ 0 ∧ (∑ c, G a c ≠ 0 → d ^ 2 * conj (∑ c, G a c) = 1) := fun a => by
    by_cases h0 : ∑ c, G a c = 0
    · exact ⟨1, one_ne_zero, fun h => absurd h0 h⟩
    · obtain ⟨d, hd⟩ := IsAlgClosed.exists_pow_nat_eq (conj (∑ c, G a c))⁻¹ two_pos
      have h0' : conj (∑ c, G a c) ≠ 0 := (map_ne_zero _).2 h0
      refine ⟨d, fun e => inv_ne_zero h0' (by rw [← hd, e]; simp), fun _ => by rw [hd, inv_mul_cancel₀ h0']⟩
  choose d hd0 hd using h3
  refine ⟨d, hd0, fun a b => ?_⟩
  rw [diagonal_conjTranspose, mul_diagonal, diagonal_mul, Pi.star_apply, Complex.star_def]
  by_cases hab : G a b = 0
  · simp [hab]
  have hba : G b a = conj (G a b) := (congrFun (congrFun hG b) a).symm
  have hba0 : G b a ≠ 0 := by rw [hba]; exact (map_ne_zero _).2 hab
  have ha := hd a (by rwa [h2 a b hab])
  have hb := hd b (by rwa [h2 b a hba0])
  rw [h2 a b hab] at ha
  rw [h2 b a hba0, hba, Complex.conj_conj] at hb
  have ha' := congrArg conj ha
  rw [map_mul, map_pow, Complex.conj_conj, map_one] at ha'
  have : (conj (d a) * G a b * d b) ^ 2 = 1 := by linear_combination (d b ^ 2 * G a b) * ha' + hb
  rcases sq_eq_one_iff.1 this with e | e <;> simp [e]

def IsEigenbasis (s : Matrix (Fin n) (Fin n) ℂ) (g : GL (Fin n) ℂ) : Prop :=
  ∃ z : Fin n → ℂ, Function.Injective z ∧ s * g = g * diagonal z

theorem exists_isEigenbasis {s : Matrix (Fin n) (Fin n) ℂ} (hs : IsRegSS s) : ∃ g, IsEigenbasis s g := by
  have hc : s.charpoly.roots.card = n := by
    rw [← (IsAlgClosed.splits s.charpoly).natDegree_eq_card_roots, charpoly_natDegree_eq_dim, Fintype.card_fin]
  obtain ⟨z, hz⟩ : ∃ z : Fin n → ℂ, s.charpoly.roots = Finset.univ.val.map z := by
    induction' hr : s.charpoly.roots using Quotient.inductionOn with l
    rw [hr] at hc
    obtain rfl : l.length = n := hc
    exact ⟨l.get, by simp⟩
  have he : s.charpoly = (diagonal z).charpoly := by
    rw [charpoly_diagonal, (IsAlgClosed.splits s.charpoly).eq_prod_roots_of_monic s.charpoly_monic, hz,
      Multiset.map_map]
    rfl
  have hd : IsRegSS (diagonal z) := by rwa [IsRegSS, ← he]
  obtain ⟨g, hg⟩ := hd.exists_conj he
  refine ⟨g, z, ?_, hg⟩
  rwa [IsRegSS, charpoly_diagonal, Polynomial.separable_prod_X_sub_C_iff] at hd

theorem commute_diagonal {z : Fin n → ℂ} (hz : Function.Injective z) (w : Fin n → ℂ) {u : Matrix (Fin n) (Fin n) ℂ}
    (h : u * diagonal z = diagonal z * u) : u * diagonal w = diagonal w * u := by
  ext a b
  have := congrFun (congrFun h a) b
  rw [mul_diagonal, diagonal_mul] at this ⊢
  by_cases hab : a = b
  · rw [hab, mul_comm]
  · have h0 : u a b = 0 := by
      by_contra h0
      exact hab (hz (mul_left_cancel₀ h0 (by linear_combination -this)))
    simp [h0]

variable {ε : Fin n → Bool}

theorem exists_isEigenbasis_gram {s : UJ ε} (hs : IsRegSS (ujMat ε s)) : ∃ g : GL (Fin n) ℂ,
    IsEigenbasis (ujMat ε s) g ∧ ∀ a b, (g.1ᴴ * Jm ε * g.1) a b ∈ ({0, 1, -1} : Finset ℂ) := by
  obtain ⟨g, z, hz, hg⟩ := exists_isEigenbasis hs
  have hU : (ujMat ε s)ᴴ * Jm ε * ujMat ε s = Jm ε := s.2
  obtain ⟨d, hd0, hd⟩ := exists_scale (G := g.1ᴴ * Jm ε * g.1)
    (by simp [conjTranspose_mul, Jm_conjTranspose, Matrix.mul_assoc]) hz (by
      calc _ = (g.1 * diagonal z)ᴴ * Jm ε * (g.1 * diagonal z) := by simp only [conjTranspose_mul, Matrix.mul_assoc]
        _ = g.1ᴴ * ((ujMat ε s)ᴴ * Jm ε * ujMat ε s) * g.1 := by
          simp only [← hg, conjTranspose_mul, Matrix.mul_assoc]
        _ = _ := by rw [hU])
  let D : GL (Fin n) ℂ := ⟨diagonal d, diagonal fun a => (d a)⁻¹, by simp [hd0], by simp [hd0]⟩
  refine ⟨g * D, ⟨z, hz, ?_⟩, fun a b => ?_⟩
  · change _ * (g.1 * diagonal d) = g.1 * diagonal d * _
    rw [← Matrix.mul_assoc, hg, Matrix.mul_assoc, Matrix.mul_assoc, commute_diagonal hz d (u := diagonal z) rfl]
  · have e : (g.1 * diagonal d)ᴴ * Jm ε * (g.1 * diagonal d) =
        (diagonal d)ᴴ * (g.1ᴴ * Jm ε * g.1) * diagonal d := by simp only [conjTranspose_mul, Matrix.mul_assoc]
    rw [← e] at hd
    exact hd a b

theorem conj_mem_cent {s s' x u : UJ ε} {g g' : GL (Fin n) ℂ} (h : IsEigenbasis (ujMat ε s) g)
    (h' : IsEigenbasis (ujMat ε s') g') (hx : x.1 * g = g') (hu : u ∈ cent s) : x * u * x⁻¹ ∈ cent s' := by
  obtain ⟨z, hz, hg⟩ := h
  obtain ⟨w, -, hg'⟩ := h'
  have h1 : ujMat ε u * ujMat ε s = ujMat ε s * ujMat ε u := by
    rw [← map_mul, ← map_mul, GlobalTheory.Orb.mem_cent.1 hu]
  have e : ∀ {t : Matrix (Fin n) (Fin n) ℂ} {k : GL (Fin n) ℂ} {y}, t * k.1 = k.1 * diagonal y →
      diagonal y = (k⁻¹).1 * t * k.1 := fun ht => by rw [Matrix.mul_assoc, ht, Units.inv_mul_cancel_left]
  have h2 := commute_diagonal hz w (u := (g⁻¹).1 * ujMat ε u * g.1) (by
    simp only [e hg, Matrix.mul_assoc, Units.mul_inv_cancel_left]
    rw [← Matrix.mul_assoc (ujMat ε u), h1, Matrix.mul_assoc])
  rw [e hg', ← hx] at h2
  have h3 : (g⁻¹ * u.1 * g) * ((x.1 * g)⁻¹ * s'.1 * (x.1 * g)) = ((x.1 * g)⁻¹ * s'.1 * (x.1 * g)) * (g⁻¹ * u.1 * g) :=
    Units.ext h2
  refine GlobalTheory.Orb.mem_cent.2 (Subtype.ext ?_)
  have h4 := congrArg (fun y => (x.1 * g) * y * (x.1 * g)⁻¹) h3
  simp only [Subgroup.coe_mul, Subgroup.coe_inv]
  simpa [mul_assoc] using h4

theorem conj_of_gram_eq {s s' : UJ ε} {g g' : GL (Fin n) ℂ} (h : IsEigenbasis (ujMat ε s) g)
    (h' : IsEigenbasis (ujMat ε s') g') (hG : g.1ᴴ * Jm ε * g.1 = g'.1ᴴ * Jm ε * g'.1) :
    ∃ x, (cent s).map (MulAut.conj x).toMonoidHom = cent s' := by
  have hx : g' * g⁻¹ ∈ UJ ε := by
    change (g'.1 * (g⁻¹).1)ᴴ * Jm ε * (g'.1 * (g⁻¹).1) = Jm ε
    calc _ = (g⁻¹).1ᴴ * (g'.1ᴴ * Jm ε * g'.1) * (g⁻¹).1 := by simp only [conjTranspose_mul, Matrix.mul_assoc]
      _ = (g.1 * (g⁻¹).1)ᴴ * Jm ε * (g.1 * (g⁻¹).1) := by simp only [← hG, conjTranspose_mul, Matrix.mul_assoc]
      _ = _ := by simp
  refine ⟨⟨_, hx⟩, le_antisymm ?_ fun u hu => ⟨(⟨_, hx⟩ : UJ ε)⁻¹ * u * (⟨_, hx⟩ : UJ ε)⁻¹⁻¹,
    conj_mem_cent h' h (by simp) hu, by simp [mul_assoc]⟩⟩
  rintro _ ⟨u, hu, rfl⟩
  exact conj_mem_cent h h' (by simp) hu

theorem exists_system {H ι : Type} [Group H] [Finite ι] {P : Subgroup H → Prop} (R : Subgroup H → ι → Prop)
    (h1 : ∀ T, P T → ∃ i, R T i)
    (h2 : ∀ T T' i, R T i → R T' i → ∃ x, T.map (MulAut.conj x).toMonoidHom = T') :
    ∃ 𝒯 : Finset (Subgroup H), (∀ T ∈ 𝒯, P T) ∧
      ∀ T, P T → ∃! T', T' ∈ 𝒯 ∧ ∃ x, T.map (MulAut.conj x).toMonoidHom = T' := by
  classical
  have hm : ∀ (T : Subgroup H) x y, (T.map (MulAut.conj x).toMonoidHom).map (MulAut.conj y).toMonoidHom =
      T.map (MulAut.conj (y * x)).toMonoidHom := fun T x y => by
    rw [Subgroup.map_map, map_mul]; rfl
  have h0 : ∀ T : Subgroup H, T.map (MulAut.conj (1 : H)).toMonoidHom = T := fun T => by
    rw [map_one]; exact T.map_id
  let S : Setoid {T // P T} := ⟨fun T T' => ∃ x, T.1.map (MulAut.conj x).toMonoidHom = T'.1,
    fun T => ⟨1, h0 _⟩, fun ⟨x, hx⟩ => ⟨x⁻¹, by rw [← hx, hm, inv_mul_cancel, h0]⟩,
    fun ⟨x, hx⟩ ⟨y, hy⟩ => ⟨y * x, by rw [← hm, hx, hy]⟩⟩
  choose f hf using h1
  have : Finite (Quotient S) := Finite.of_injective (fun q : Quotient S => f q.out.1 q.out.2) fun q q' e =>
    Quotient.out_equiv_out.1 (h2 _ _ _ (hf q.out.1 q.out.2)
      ((congrArg (R q'.out.1) e).mpr (hf q'.out.1 q'.out.2)))
  have := Fintype.ofFinite (Quotient S)
  refine ⟨Finset.univ.image fun q : Quotient S => q.out.1, fun T hT => ?_, fun T hT =>
    ⟨(Quotient.mk S ⟨T, hT⟩).out.1, ⟨Finset.mem_image_of_mem _ (Finset.mem_univ _),
      S.symm (Quotient.mk_out (s := S) ⟨T, hT⟩)⟩, ?_⟩⟩
  · obtain ⟨q, -, rfl⟩ := Finset.mem_image.1 hT
    exact q.out.2
  · rintro T' ⟨hT', hx⟩
    obtain ⟨q, -, rfl⟩ := Finset.mem_image.1 hT'
    rw [Quotient.sound (s := S) (a := ⟨T, hT⟩) (b := q.out) hx, q.out_eq]

theorem exists_isCartanSystem : ∀ (n : ℕ) (ε : Fin n → Bool), ∃ 𝒯 : Finset (Subgroup (UJ ε)), IsCartanSystem 𝒯 := by
  intro n ε
  refine exists_system (ι := Fin n → Fin n → ({0, 1, -1} : Finset ℂ)) (fun T i => ∃ (s : UJ ε) (g : GL (Fin n) ℂ),
    T = cent s ∧ IsEigenbasis (ujMat ε s) g ∧ ∀ a b, (g.1ᴴ * Jm ε * g.1) a b = i a b) ?_ ?_
  · rintro _ ⟨s, hs, rfl⟩
    obtain ⟨g, hg, hG⟩ := exists_isEigenbasis_gram hs
    exact ⟨fun a b => ⟨_, hG a b⟩, s, g, rfl, hg, fun _ _ => rfl⟩
  · rintro _ _ i ⟨s, g, rfl, hg, hG⟩ ⟨s', g', rfl, hg', hG'⟩
    exact conj_of_gram_eq hg hg' (Matrix.ext fun a b => (hG a b).trans (hG' a b).symm)

end GlobalTheory.CartanFinite
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsFiniteUnitaryMoverStandardLatticeStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_finite_unitary_mover_standard_lattice : ∀ (D : D7) (S T : HSp D) (C : Ctx S T) (hn : T.rank ≤ S.rank) (ΛT : Lt D.host.E T.rank), IsSelfDualC T ΛT → IsAA C.X.Λ ΛT → ∀ (βS : GL (Fin S.rank) (Lev.EAf D)) (βT : GL (Fin T.rank) (Lev.EAf D)), Formalism.L2.DIV.IsFrame βS (stdL D.host.E S.rank) → Formalism.L2.DIV.IsFrame βT ΛT → ∀ (Pg Q : Finset (Formalism.L2.DIV.Pl D.host.E)) (ξ : ∀ PP : Formalism.L2.DIV.Pl D.host.E, (Formalism.L2.DIV.kP PP)ˣ →* ℂˣ), Pg.Nonempty → (∀ PP, PP ∈ Pg ∨ PP ∈ Q → (2 : 𝓞 D.host.E) ∉ PP.asIdeal) → ∀ e : AE D, IsIdemSum e (Pg ∪ Q) → ∀ a : AE D, (∃ b : AE D, a * b = e) → ∃ (k₀ : GA D S) (Λ' : Lt D.host.E S.rank), GlobalTheory.LiftLevel.IsMover S T βS βT e a k₀ ∧ IsMov (fmtC S k₀⁻¹) Λ' (stdL D.host.E S.rank) := by
  first | exact @GlobalTheory.LiftLevel.exists_mover | exact GlobalTheory.LiftLevel.exists_mover | (intros; apply GlobalTheory.LiftLevel.exists_mover <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsFockPolynomialIsoUnitaryPairStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Matrix GlobalTheory.Chain GlobalTheory.Chain.RealIt
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_fockPolynomialIso_unitaryPair : ∀ (p q r s a b : ℕ) (ε : Fin a → Bool) (ε' : Fin b → Bool) (e : Ix p q ≃ Fin a) (e' : Ix r s ≃ Fin b), GlobalTheory.IndefiniteRowSideFullHecke.BarMatrix.SignCompat ε e → GlobalTheory.IndefiniteRowSideFullHecke.BarMatrix.SignCompat ε' e' → ∃ κ : LPol b a ≃ₗ[ℂ] Pol p q r s, IsPolyIso ε ε' e e' κ := by
  first | exact @GlobalTheory.Chain.RealIt.PolyIso.exists_isPolyIso | exact GlobalTheory.Chain.RealIt.PolyIso.exists_isPolyIso | (intros; apply GlobalTheory.Chain.RealIt.PolyIso.exists_isPolyIso <;> assumption)
end

