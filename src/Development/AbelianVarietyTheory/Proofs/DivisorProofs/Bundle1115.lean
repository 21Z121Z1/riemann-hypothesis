import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0894
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0005
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RamificationIdxEqOneOfIsSquare
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DefiniteUnitaryClassSetFinite
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0016
import Formalism.LocalToGlobal.IndefiniteReal.SubgroupCharExtensionOneApply
import Formalism.LocalToGlobal.IndefiniteReal.ScalarOnPartsFull
import Formalism.LocalToGlobal.IndefiniteReal.OrthogonalComplementCharacterisation
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0001
import Formalism.LocalToGlobal.IndefiniteReal.HeckeTupleStatement
import Formalism.LocalRingCardinality.Bundle0007
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0016
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0108
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0141
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0158
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0001
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1092
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1076
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1036
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1086
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HighestWeightTensor
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HomKillsTorsionOfComplexPointsOneEmbedding
import Development.AbelianVarietyTheory.Definitions.CMLattices.IsDiffOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1041
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1077
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDiagonalLagrangianInvariantForm
import GroundTheory.AutomorphicForms.GL2.GJMatrixAdelic

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeCharacterOfIdeleClass
section
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun

noncomputable section

open scoped TensorProduct
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun

namespace GlobalTheory.HeckeBridge

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem compInf_eq_infTens (w : InfinitePlace F) (z : AF F ⊗[F] E) :
    compInf F E w z = Algebra.TensorProduct.map (GlobalTheory.AutFunCompare.evW w) (AlgHom.id F E) (infTens F E z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a x => rfl
  | add x y hx hy => rw [map_add, map_add, map_add, hx, hy]

theorem coe_infDiag (k : Eˣ) :
    (Formalism.L2.Host.infDiag k : AdeleRing (𝓞 E) E) = (algebraMap E (InfiniteAdeleRing E) k, 1) := by
  classical
  rw [Formalism.L2.Host.infDiag, MonoidHom.finsetProd_apply, Units.coe_prod]
  let p1 : AdeleRing (𝓞 E) E →+* InfiniteAdeleRing E := RingHom.fst _ _
  let p2 : AdeleRing (𝓞 E) E →+* FiniteAdeleRing (𝓞 E) E := RingHom.snd _ _
  refine Prod.ext ?_ ?_
  · change p1 _ = _
    rw [map_prod]
    change ∏ w : InfinitePlace E, Pi.mulSingle w (algebraMap E w.Completion (k : E)) = _
    exact Finset.univ_prod_mulSingle _
  · change p2 _ = _
    rw [map_prod]
    exact Finset.prod_eq_one fun _ _ => rfl

theorem exists_tensor_adele_equiv (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (hcm : IsCMExt F E σ) :
    ∃ (Φ : AF F ⊗[F] E ≃+* AdeleRing (𝓞 E) E) (j : Ainf F ⊗[F] E ≃+* InfiniteAdeleRing E),
      Continuous Φ ∧ Continuous Φ.symm ∧ (∀ x : E, j ((1 : Ainf F) ⊗ₜ[F] x) = algebraMap E (InfiniteAdeleRing E) x) ∧
      ∀ z, Φ z = (j (infTens F E z), finAdEquiv F E (finTens F E z)) := by
  obtain ⟨j, hjc, hjc', hj⟩ := GlobalTheory.HeckeTensorRead.exists_infinite_equiv F E σ hcm
  obtain ⟨s, hs, hsc, hsc'⟩ := GlobalTheory.AdSplit.exists_adele_equiv F E
  refine ⟨s.trans (j.prodCongr (finAdEquiv F E)), j, (hjc.prodMap GlobalTheory.DefU.ClassFin.continuous_finAdEquiv).comp hsc, hsc'.comp (hjc'.prodMap continuous_finAdEquiv_symm), hj,
    fun z => Prod.ext (congrArg j (hs z).1) (congrArg (finAdEquiv F E) (hs z).2)⟩

theorem exists_hchar (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) : IsCMExt F E σ → ∀ χ : Chr F E, IsHecke F E χ → ∃ H : Formalism.L2.Host.HChar E,
      (∀ (W : HeightOneSpectrum (𝓞 E)) (x : (W.adicCompletion E)ˣ), H.loc W x = locChar χ W x) ∧
      ∀ (τ : ∀ w : InfinitePlace F, EmbOver E w) (m : InfinitePlace F → ℤ), HasExp τ χ m →
        H.HasInf (fun w => (τ w).1) m := by
  intro hcm χ hχ
  obtain ⟨Φ, j, -, hΦc, hj, hΦ⟩ := exists_tensor_adele_equiv F E σ hcm
  have hfin : ∀ x : E, finAdEquiv F E ((1 : Af F) ⊗ₜ[F] x) = algebraMap E (FiniteAdeleRing (𝓞 E) E) x := fun x => by
    rw [show finAdEquiv F E ((1 : Af F) ⊗ₜ[F] x) = _ from toFinAd_tmul 1 x, map_one, one_mul]
  let u : Neutral.B1.Ideles E →* (AF F ⊗[F] E)ˣ := Units.map Φ.symm.toRingHom.toMonoidHom
  have hu : Continuous u := Continuous.units_map _ hΦc
  have ht : Continuous (Circle.toUnits : Circle →* ℂˣ) :=
    Units.continuous_iff.2 ⟨continuous_subtype_val, by
      have h : Continuous fun z : Circle => ((z⁻¹ : Circle) : ℂ) := continuous_subtype_val.comp continuous_inv
      refine h.congr fun z => ?_
      simp⟩
  have hdiag : ∀ k : Eˣ, u (Neutral.B1.diagUnits E k) = Units.map (inclR (F := F) (AF F)).toMonoidHom k := fun k =>
    Units.ext (Φ.symm_apply_eq.2 (by
      rw [hΦ]
      change (algebraMap E (InfiniteAdeleRing E) k, algebraMap E (FiniteAdeleRing (𝓞 E) E) k) = _
      refine Prod.ext (hj k).symm (hfin k).symm))
  have hloc : ∀ (W : HeightOneSpectrum (𝓞 E)) (x : (W.adicCompletion E)ˣ),
      u (Neutral.B1.localIdele E W x) = locIdele F W x := fun W x =>
    Units.ext (Φ.symm_apply_eq.2 (by
      rw [hΦ, infTens_locIdele, map_one, finTens_locIdele]
      rfl))
  let H : Formalism.L2.Host.HChar E := ⟨Circle.toUnits.comp (χ.comp u), ht.comp (hχ.1.comp hu), fun k => by
    change Circle.toUnits (χ (u _)) = 1
    rw [hdiag, hχ.2, map_one]⟩
  refine ⟨H, fun W x => ?_, fun τ m hm k => ?_⟩
  · change Circle.toUnits (χ (u _)) = Circle.toUnits (χ (locIdele F W x))
    rw [hloc]
  · set z := u (Formalism.L2.Host.infDiag k) with hz
    have hz1 : Φ (z : AF F ⊗[F] E) = (Formalism.L2.Host.infDiag k : AdeleRing (𝓞 E) E) := Φ.apply_symm_apply _
    rw [coe_infDiag, hΦ] at hz1
    have hinf : infTens F E z = (1 : Ainf F) ⊗ₜ[F] (k : E) :=
      j.injective ((congrArg Prod.fst hz1).trans (hj k).symm)
    have hfin1 : finTens F E z = 1 :=
      (finAdEquiv F E).injective ((congrArg Prod.snd hz1).trans (map_one _).symm)
    have hAt : At (evI F) ((z : AF F ⊗[F] E) - 1) := by
      intro a ha
      have ha1 : a.1 = 0 := (InfiniteAdeleRing.ringEquiv_mixedSpace F).injective (ha.trans (map_zero _).symm)
      refine tens_ext ?_ ?_
      · rw [Algebra.smul_def, map_mul, map_zero]
        change (a.1 ⊗ₜ[F] (1 : E)) * _ = 0
        rw [ha1, TensorProduct.zero_tmul, zero_mul]
      · rw [Algebra.smul_def, map_mul, map_zero, map_sub, map_one, hfin1, sub_self, mul_zero]
    have hpi : ∀ w, piInf (τ w) z = (τ w).1 k := fun w => by
      change infEmb (τ w) (compInf F E w z) = _
      rw [compInf_eq_infTens, hinf, Algebra.TensorProduct.map_tmul, map_one, infEmb_tmul, map_one, one_mul]
      rfl
    change ((χ z : Circle) : ℂ) = _
    rw [hm z hAt]
    exact Finset.prod_congr rfl fun w _ => by rw [hpi w]

end GlobalTheory.HeckeBridge
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeOperatorOffDifferent
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SphericalComm

theorem exists_unif_of_not_dvd {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (P : HeightOneSpectrum (𝓞 E)) (h : ¬ P.asIdeal ∣ differentIdeal (𝓞 F) (𝓞 E)) :
    ∃ x : 𝓞 F, ∃ y : 𝓞 E, (y : E) = algebraMap F E (x : F) ∧ y ∈ P.asIdeal ∧ y ∉ P.asIdeal ^ 2 := by
  by_contra hne
  push Not at hne
  apply h
  have hle : (P.asIdeal.under (𝓞 F)).map (algebraMap (𝓞 F) (𝓞 E)) ≤ P.asIdeal ^ 2 := by
    rw [Ideal.map_le_iff_le_comap]
    intro x hx
    exact hne x _ rfl hx
  haveI := P.isMaximal
  haveI : (P.asIdeal.under (𝓞 F)).IsMaximal := Ideal.IsMaximal.under _ _
  have hb : P.asIdeal.under (𝓞 F) ≠ ⊥ := Ideal.under_ne_bot _ P.ne_bot
  have := pow_sub_one_dvd_differentIdeal (𝓞 F) P.asIdeal 2 hb (Ideal.dvd_iff_le.2 hle)
  simpa using this

end GlobalTheory.SphericalComm
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeTestProductSupportFiniteLeftCosets
section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount
open scoped TensorProduct Classical

namespace GlobalTheory.CosetFin

variable {H : Type} [Group H]

theorem finite_mk_mul (A K : Subgroup H) (x : H) (h : (K.map (MulAut.conj x).toMonoidHom).relIndex A ≠ 0) :
    {q : H ⧸ K | ∃ a ∈ A, q = (QuotientGroup.mk (a * x) : H ⧸ K)}.Finite := by
  set S := (K.map (MulAut.conj x).toMonoidHom).subgroupOf A
  haveI : S.FiniteIndex := ⟨h⟩
  haveI : Finite (A ⧸ S) := Subgroup.finite_quotient_of_finiteIndex
  refine (Set.finite_range (fun t : A ⧸ S => (QuotientGroup.mk ((t.out : H) * x) : H ⧸ K))).subset ?_
  rintro q ⟨a, ha, rfl⟩
  refine ⟨(QuotientGroup.mk (⟨a, ha⟩ : A) : A ⧸ S), ?_⟩
  obtain ⟨u, hu⟩ := QuotientGroup.mk_out_eq_mul S (⟨a, ha⟩ : A)
  simp only
  rw [hu]
  have hu2 : ((u : A) : H) ∈ K.map (MulAut.conj x).toMonoidHom := u.2
  obtain ⟨k, hk, hke⟩ := hu2
  rw [QuotientGroup.eq]
  have : ((u : A) : H) = x * k * x⁻¹ := by rw [← hke]; rfl
  simp only [Subgroup.coe_mul, this]
  have e : (a * (x * k * x⁻¹) * x)⁻¹ * (a * x) = k⁻¹ := by group
  rw [e]; exact K.inv_mem hk

theorem finite_mk_dcoset (K₀ K : Subgroup H) (hc : K.relIndex K₀ ≠ 0)
    (hconj : ∀ y : H, (K.map (MulAut.conj y).toMonoidHom).relIndex K₀ ≠ 0) (s : H) :
    {q : H ⧸ K | ∃ k₁ ∈ K₀, ∃ k₂ ∈ K₀, q = (QuotientGroup.mk (k₁ * s * k₂) : H ⧸ K)}.Finite := by
  set T := K.subgroupOf K₀
  haveI : T.FiniteIndex := ⟨hc⟩
  haveI : Finite (K₀ ⧸ T) := Subgroup.finite_quotient_of_finiteIndex
  refine (Set.finite_iUnion (fun t : K₀ ⧸ T => finite_mk_mul K₀ K (s * (t.out : H)) (hconj _))).subset ?_
  rintro q ⟨k₁, hk₁, k₂, hk₂, rfl⟩
  refine Set.mem_iUnion.2 ⟨(QuotientGroup.mk (⟨k₂, hk₂⟩ : K₀) : K₀ ⧸ T), k₁, hk₁, ?_⟩
  obtain ⟨u, hu⟩ := QuotientGroup.mk_out_eq_mul T (⟨k₂, hk₂⟩ : K₀)
  rw [hu, QuotientGroup.eq]
  have hu2 : ((u : K₀) : H) ∈ K := u.2
  simp only [Subgroup.coe_mul]
  have e : (k₁ * s * k₂)⁻¹ * (k₁ * (s * (k₂ * ((u : K₀) : H)))) = ((u : K₀) : H) := by group
  rw [e]; exact hu2

theorem finite_mk_support (K₀ K : Subgroup H) (hc : K.relIndex K₀ ≠ 0)
    (hconj : ∀ y : H, (K.map (MulAut.conj y).toMonoidHom).relIndex K₀ ≠ 0) (φ : H → ℂ) (S : Finset H)
    (hS : ∀ g, φ g ≠ 0 → ∃ s ∈ S, ∃ k₁ ∈ K₀, ∃ k₂ ∈ K₀, g = k₁ * s * k₂) :
    {q : H ⧸ K | ∃ g, φ g ≠ 0 ∧ q = (QuotientGroup.mk g : H ⧸ K)}.Finite := by
  refine (S.finite_toSet.biUnion fun s _ => finite_mk_dcoset K₀ K hc hconj s).subset ?_
  rintro q ⟨g, hg, rfl⟩
  obtain ⟨s, hs, k₁, hk₁, k₂, hk₂, rfl⟩ := hS g hg
  exact Set.mem_biUnion hs ⟨k₁, hk₁, k₂, hk₂, rfl⟩

theorem relIndex_ne_zero_open_compact {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (U K : Subgroup G) (hU : IsOpen (U : Set G)) (hK : IsCompact (K : Set G)) : U.relIndex K ≠ 0 := by
  haveI : CompactSpace K := isCompact_iff_compactSpace.mp hK
  haveI : Finite (K ⧸ U.subgroupOf K) :=
    Subgroup.quotient_finite_of_isOpen _ (hU.preimage continuous_subtype_val)
  exact Subgroup.index_ne_zero_of_finite

theorem isOpen_map_conj {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (U : Subgroup G) (hU : IsOpen (U : Set G)) (y : G) :
    IsOpen ((U.map (MulAut.conj y).toMonoidHom : Subgroup G) : Set G) := by
  have e : ((U.map (MulAut.conj y).toMonoidHom : Subgroup G) : Set G) = (fun g => y⁻¹ * g * y) ⁻¹' (U : Set G) := by
    ext g
    simp only [Subgroup.coe_map, Set.mem_image, SetLike.mem_coe, Set.mem_preimage]
    constructor
    · rintro ⟨k, hk, rfl⟩
      have : y⁻¹ * ((MulAut.conj y).toMonoidHom k) * y = k := by
        show y⁻¹ * (y * k * y⁻¹) * y = k; group
      rw [this]; exact hk
    · intro h
      refine ⟨_, h, ?_⟩
      show y * (y⁻¹ * g * y) * y⁻¹ = g; group
  rw [e]
  exact hU.preimage ((continuous_const.mul continuous_id).mul continuous_const)

end GlobalTheory.CosetFin

namespace GlobalTheory.CosetFin

theorem commensurable_map_conj {G : Type} [Group G] {A B : Subgroup G} (h : A.Commensurable B) (y : G) :
    (A.map (MulAut.conj y).toMonoidHom).Commensurable (B.map (MulAut.conj y).toMonoidHom) := by
  have hinj : Function.Injective (MulAut.conj y).toMonoidHom := (MulAut.conj y).injective
  exact ⟨by rw [Subgroup.relIndex_map_map_of_injective _ _ hinj]; exact h.1,
    by rw [Subgroup.relIndex_map_map_of_injective _ _ hinj]; exact h.2⟩

end GlobalTheory.CosetFin

open GlobalTheory.CosetFin in

theorem GlobalTheory.testProd_support_finite : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (L : G.Level) (f : G.GAf → ℂ),
    IsTest (MonoidHom.id _) L.K.toSubgroup L.K.toSubgroup f →
      (∀ k ∈ L.K.toSubgroup, ∀ k' ∈ L.K.toSubgroup, ∀ g, f (k * g * k') = f g) →
    ∀ (K' : Subgroup (Gr G 1)) (f' : Gr G 1 → ℂ), IsTest (sigG G 1) (KHT p G.m G.n 1 G.Fw) K' f' →
      (∀ k ∈ K', ∀ k' ∈ K', ∀ g, f' (k * g * k') = f' g) →
      (Function.support (fun q : (G.GAf × Gr G 1) ⧸ (L.K.toSubgroup.prod K' : Subgroup (G.GAf × Gr G 1)) =>
        f q.out.1 * f' q.out.2)).Finite := by
  intro p _ G L f hf _ K' f' hf' _
  obtain ⟨-, -, -, S, hS⟩ := hf
  obtain ⟨hc', -, -, S', hS'⟩ := hf'

  have hA : {a : G.GAf ⧸ L.K.toSubgroup | ∃ g, f g ≠ 0 ∧ a = (QuotientGroup.mk g : G.GAf ⧸ L.K.toSubgroup)}.Finite := by
    refine finite_mk_support L.K.toSubgroup L.K.toSubgroup ?_ ?_ f S hS
    · rw [Subgroup.relIndex_self]; exact one_ne_zero
    · intro y
      exact relIndex_ne_zero_open_compact _ _ (isOpen_map_conj _ L.K.isOpen y) L.compact

  have hB : {b : Gr G 1 ⧸ K' | ∃ g, f' g ≠ 0 ∧ b = (QuotientGroup.mk g : Gr G 1 ⧸ K')}.Finite := by
    refine finite_mk_support (KHT p G.m G.n 1 G.Fw) K' hc'.1 ?_ f' S' hS'
    intro y
    have h1 := (GlobalTheory.heckeOperator_integral p G 1 Nat.one_pos).1 y
    exact ((commensurable_map_conj hc' y).trans h1).1
  let ψ : (G.GAf × Gr G 1) ⧸ (L.K.toSubgroup.prod K' : Subgroup (G.GAf × Gr G 1)) →
      (G.GAf ⧸ L.K.toSubgroup) × (Gr G 1 ⧸ K') :=
    fun q => ((QuotientGroup.mk q.out.1 : G.GAf ⧸ L.K.toSubgroup), (QuotientGroup.mk q.out.2 : Gr G 1 ⧸ K'))
  have hψ : Function.Injective ψ := by
    intro q r hqr
    simp only [ψ, Prod.mk.injEq, QuotientGroup.eq] at hqr
    rw [← QuotientGroup.out_eq' q, ← QuotientGroup.out_eq' r]
    apply QuotientGroup.eq.2
    exact Subgroup.mem_prod.2 ⟨by simpa using hqr.1, by simpa using hqr.2⟩
  refine ((hA.prod hB).preimage hψ.injOn).subset ?_
  intro q hq
  have h1 : f q.out.1 ≠ 0 := left_ne_zero_of_mul hq
  have h2 : f' q.out.2 ≠ 0 := right_ne_zero_of_mul hq
  exact ⟨⟨_, h1, rfl⟩, ⟨_, h2, rfl⟩⟩
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianSelfDualLatticeSpaceFormHermitianNondegStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermitianSelfDualLatticeSpace_form_hermitian_nondeg_unimodular : ∀ (D : D7) (B : Base D.host.F D.host.E), B.IsGood D.sp.cm.sig →
    ∀ (n : ℕ) (X : Spc D.host.F D.host.E n) (r s : ℕ), X.IsHerm D.sp.cm.sig B r s →
      (GlobalTheory.WeilSchrodinger.sesq D X.Jᵀ).IsSymm ∧ (GlobalTheory.WeilSchrodinger.sesq D X.Jᵀ).Nondegenerate ∧
        Formalism.HermitianLatticesTheory.IsUnimodular (GlobalTheory.WeilSchrodinger.sesq D X.Jᵀ) X.L := by
  first | exact @GlobalTheory.WeilSchrodingerHerm.main | exact GlobalTheory.WeilSchrodingerHerm.main | (intros; apply GlobalTheory.WeilSchrodingerHerm.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HighestWeightInRangePlusSubmodule
section
open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.FockAlg GlobalTheory.SteepMult

namespace GlobalTheory.SteepMult

theorem hw_lift_orth : ∀ (R S : ℕ) (W : Type) [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
    (actW : Mat R S →ₗ[ℂ] Module.End ℂ W) (B : W →ₗ⋆[ℂ] W →ₗ[ℂ] ℂ) (V : Type) [AddCommGroup V] [Module ℂ V]
    (act : Mat R S →ₗ[ℂ] Module.End ℂ V) (φ : W →ₗ[ℂ] V) (F : Submodule ℂ V) (Λ : Ix R S → ℚ) (w : V),
    IsUnitary actW B → KStable act F → (∀ Z, IsKC Z → ∀ x, φ (actW Z x) = act Z (φ x)) →
    w ∈ LinearMap.range φ ⊔ F → w ∈ hwSub act Λ → w ∉ F →
    ∃ Ψ ∈ (F.comap φ).orthogonalBilin B, Ψ ≠ 0 ∧ Ψ ∈ hwSub actW Λ := by
  intro R S W _ _ _ actW B V _ _ act φ F Λ w hU hF hφ hw hhw hwF
  obtain ⟨_hherm, hpos, hadj⟩ := hU
  set K := F.comap φ with hK
  have hKst : ∀ Z, IsKC Z → ∀ x ∈ K, actW Z x ∈ K := by
    intro Z hZ x hx
    simp only [hK, Submodule.mem_comap] at hx ⊢
    rw [hφ Z hZ]; exact hF Z hZ _ hx
  have hperp : ∀ y, y ∈ K.orthogonalBilin B ↔ ∀ v ∈ K, B v y = 0 := fun y => Iff.rfl
  have hsame_symm : ∀ a b : Ix R S, sameBlock a b → sameBlock b a := by
    intro a b; cases a <;> cases b <;> simp [sameBlock]
  have hsame_refl : ∀ a : Ix R S, sameBlock a a := by
    intro a; cases a <;> simp [sameBlock]
  have hpos_same : ∀ a b : Ix R S, posC a b → sameBlock a b := by
    intro a b; cases a <;> cases b <;> simp [posC, sameBlock]
  have hKC_E : ∀ a b : Ix R S, sameBlock a b → IsKC (Eab a b) := by
    intro a b hab c d hcd
    simp only [Eab, Matrix.single_apply]
    split_ifs with h
    · obtain ⟨rfl, rfl⟩ := h; exact absurd hab hcd
    · rfl
  have hperpE : ∀ a b, sameBlock a b → ∀ y ∈ K.orthogonalBilin B, actW (Eab a b) y ∈ K.orthogonalBilin B := by
    intro a b hab y hy
    rw [hperp] at hy ⊢
    intro v hv
    rw [← hadj b a (hsame_symm a b hab) v y]
    exact hy _ (hKst _ (hKC_E b a (hsame_symm a b hab)) v hv)
  have hdisj : ∀ y ∈ K, y ∈ K.orthogonalBilin B → y = 0 := by
    intro y h1 h2
    by_contra hne
    have := hpos y hne
    rw [(hperp y).1 h2 y h1] at this; simp at this
  have hdec : ∀ x, ∃ κ ∈ K, x - κ ∈ K.orthogonalBilin B := by
    intro x
    let b := Module.finBasis ℂ K
    let G : W →ₗ[ℂ] (Fin (Module.finrank ℂ K) → ℂ) := LinearMap.pi fun i => B (b i : W)
    have key : ∀ y, G y = 0 → ∀ v ∈ K, B v y = 0 := by
      intro y hy v hv
      have h1 : (B.flip y) ∘ₛₗ K.subtype = 0 := b.ext fun i => by simpa [G] using congrFun hy i
      simpa using LinearMap.congr_fun h1 ⟨v, hv⟩
    have hinj : Function.Injective (G ∘ₗ K.subtype) := by
      rw [injective_iff_map_eq_zero]
      intro z hz
      exact Subtype.ext (hdisj z z.2 ((hperp z).2 (key z hz)))
    have hsurj : Function.Surjective (G ∘ₗ K.subtype) :=
      (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (by simp)).1 hinj
    obtain ⟨z, hz⟩ := hsurj (G x)
    refine ⟨z, z.2, (hperp _).2 (key _ ?_)⟩
    rw [map_sub, ← hz]; simp
  obtain ⟨y, hy, f, hf, rfl⟩ := Submodule.mem_sup.1 hw
  obtain ⟨x, rfl⟩ := hy
  obtain ⟨κ, hκ, hΨ⟩ := hdec x
  have hκF : φ κ ∈ F := hκ
  have hfκ : f + φ κ ∈ F := F.add_mem hf hκF
  have hφΨ : φ (x - κ) = (φ x + f) - (f + φ κ) := by rw [map_sub]; abel
  have gen : ∀ (Z : Mat R S) (c : ℂ), IsKC Z → act Z (φ x + f) = c • (φ x + f) →
      actW Z (x - κ) - c • (x - κ) ∈ K.orthogonalBilin B → actW Z (x - κ) - c • (x - κ) = 0 := by
    intro Z c hZ hw' hperpZ
    refine hdisj _ ?_ hperpZ
    show φ (actW Z (x - κ) - c • (x - κ)) ∈ F
    rw [map_sub, map_smul, hφ Z hZ, hφΨ, map_sub, hw', smul_sub]
    have : c • (φ x + f) - act Z (f + φ κ) - (c • (φ x + f) - c • (f + φ κ))
        = c • (f + φ κ) - act Z (f + φ κ) := by abel
    rw [this]
    exact F.sub_mem (F.smul_mem _ hfκ) (hF Z hZ _ hfκ)
  refine ⟨x - κ, hΨ, ?_, ?_⟩
  · intro h0
    apply hwF
    rw [sub_eq_zero.1 h0]; exact F.add_mem hκF hf
  · simp only [hwSub, wtSub, Submodule.mem_inf, Submodule.mem_iInf, LinearMap.mem_ker,
      LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply, sub_eq_zero] at hhw ⊢
    obtain ⟨hwt, hkill⟩ := hhw
    refine ⟨fun a => ?_, fun a b hab => ?_⟩
    · have e := gen (Eab a a) ((Λ a : ℚ) : ℂ) (hKC_E a a (hsame_refl a)) (hwt a)
        (Submodule.sub_mem _ (hperpE a a (hsame_refl a) _ hΨ) (Submodule.smul_mem _ _ hΨ))
      exact sub_eq_zero.1 e
    · have e := gen (Eab a b) 0 (hKC_E a b (hpos_same a b hab)) (by rw [hkill a b hab, zero_smul])
        (Submodule.sub_mem _ (hperpE a b (hpos_same a b hab) _ hΨ) (Submodule.smul_mem _ _ hΨ))
      simpa using e

end GlobalTheory.SteepMult
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HighestWeightTensorRootShift
section
open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.FockAlg GlobalTheory.SteepMult

namespace GlobalTheory.SteepMult

lemma adP_Eab_diag {R S : ℕ} (c : Ix R S) (y x : NC R S) :
    adP (Eab c c) y x =
      if y = x then ((if c = y.1.1 then 1 else 0) - (if c = y.1.2 then 1 else 0)) else 0 := by
  obtain ⟨⟨y1, y2⟩, hy⟩ := y
  obtain ⟨⟨x1, x2⟩, hx⟩ := x
  simp only [adP, Eab, Matrix.single_apply, Subtype.mk.injEq, Prod.mk.injEq]
  split_ifs <;> aesop

theorem hw_tensor_one : ∀ (R S : ℕ) (W : Type) [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
    (actW : Mat R S →ₗ[ℂ] Module.End ℂ W) (Λ : Ix R S → ℚ) (v : W), IsKLieAct actW →
    (∀ w, w ∈ ⨆ μ : Ix R S → ℚ, wtSub actW μ) → IsHW actW Λ v → GlobalTheory.BlockReps.gen actW v = ⊤ →
    ∀ (ν : Ix R S → ℚ) (y : (Fin 1 → NC R S) → W), IsHW (tAct 1 actW) ν y →
      ∃ a b, ¬ sameBlock a b ∧ ν = GlobalTheory.RealLift.addRoot Λ a b := by
  intro R S W _ _ _ actW Λ v hL hwts hv hgen ν y hy
  have hirr : ∀ U, KStable actW U → U = ⊥ ∨ U = ⊤ := by
    intro U hU
    rcases GlobalTheory.BlockReps.gen_irred (W := ⊤) hL (fun Z _ w _ => Submodule.mem_top) (fun w _ => hwts w)
      Submodule.mem_top hv U hU (hgen ▸ le_top) with h | h
    · exact Or.inl h
    · exact Or.inr (top_le_iff.1 (hgen ▸ GlobalTheory.BlockReps.gen_le h hU))
  obtain ⟨φ, hφ, h1, h2⟩ := GlobalTheory.TensorHW.exists_dual hL hv hirr
  obtain ⟨hy0, hy⟩ := hy
  rw [GlobalTheory.TensorHW.mem_hw] at hy
  obtain ⟨hyw, hyr⟩ := hy
  have hupd : ∀ (g : Fin 1 → NC R S) (x : NC R S), Function.update g 0 x = fun _ => x := by
    intro g x; funext i; rw [Subsingleton.elim i 0]; simp
  have hex : ∃ x : NC R S, φ (y fun _ => x) ≠ 0 := by
    by_contra hne
    push_neg at hne
    have hall : ∀ g, φ (y g) = 0 := fun g => by
      have : g = fun _ => g 0 := by funext i; rw [Subsingleton.elim i 0]
      rw [this]; exact hne _
    have hbot := GlobalTheory.TensorHW.ker_bot hL hirr φ hφ h1 h2 (Submodule.span ℂ (Set.range y)) ?_ ?_
    · apply hy0
      funext g
      have : y g ∈ Submodule.span ℂ (Set.range y) := Submodule.subset_span ⟨g, rfl⟩
      rw [hbot] at this
      exact this
    · rw [Submodule.span_le]; rintro _ ⟨g, rfl⟩; exact hall g
    · intro a b hab
      rw [Submodule.span_le]
      rintro _ ⟨g, rfl⟩
      have := congrFun (hyr a b hab) g
      rw [tAct_apply] at this
      simp only [Pi.zero_apply] at this
      show actW (Eab a b) (y g) ∈ Submodule.span ℂ (Set.range y)
      rw [eq_neg_of_add_eq_zero_left this]
      exact Submodule.neg_mem _ (Submodule.sum_mem _ fun i _ => Submodule.sum_mem _ fun x _ =>
        Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩))
  obtain ⟨x, hx⟩ := hex
  refine ⟨x.1.1, x.1.2, x.2, funext fun c => ?_⟩
  have := congrArg φ (congrFun (hyw c) (fun _ => x))
  rw [tAct_apply] at this
  simp only [Fin.sum_univ_one, adP_Eab_diag, hupd, ite_smul, zero_smul, Finset.sum_ite_eq,
    Finset.mem_univ, if_true, map_add, map_smul, h1, Pi.smul_apply, smul_eq_mul] at this
  have key : ((ν c : ℚ) : ℂ) = ((GlobalTheory.RealLift.addRoot Λ x.1.1 x.1.2 c : ℚ) : ℂ) := by
    apply mul_right_cancel₀ hx
    rw [← this]
    simp only [GlobalTheory.RealLift.addRoot]
    split_ifs <;> push_cast <;> ring
  exact_mod_cast key

end GlobalTheory.SteepMult
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HomKillsTorsionOfComplexPointsOneEmbeddingStatement
section
open NumberField
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CM
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hom_kills_torsion_of_complexPoints_oneEmbedding : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E)
    (K : Type) [Field K] [NumberField K] (σ : K →+* ℂ) (A B : GlobalTheory.CM.PAT H (Sp (𝓞 K))) (G : A.t.G ⟶ B.t.G),
    IsMonHom G → ∀ m : ℕ, 0 < m →
    (∀ x : Over.mk (spMap (σ.comp (algebraMap (𝓞 K) K))) ⟶ A.t.G, x ^ m = 1 → x ≫ G = 1) →
    ∀ (T : Over (Sp (𝓞 K))) (x : T ⟶ A.t.G), x ^ m = 1 → x ≫ G = 1 := by
  first | exact @GlobalTheory.TorsionKill.kill_torsion | exact GlobalTheory.TorsionKill.kill_torsion | (intros; apply GlobalTheory.TorsionKill.kill_torsion <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IndefiniteUnitaryCharacterEqOneCayleyRotationStatement
section
open scoped Matrix
open Formalism.BasicNotions.TH
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.indefiniteUnitaryCharacter_eq_one_cayleyRotation : ∀ (R S : ℕ) (χ : Mat R S → ℂ),
    (∀ g h : Mat R S, gᴴ * Jm R S * g = Jm R S → hᴴ * Jm R S * h = Jm R S → χ (g * h) = χ g * χ h) →
    ContinuousOn χ {g : Mat R S | gᴴ * Jm R S * g = Jm R S} →
    (∀ g : Mat R S, gᴴ * Jm R S * g = Jm R S → χ g ≠ 0) →
    ∀ (i0 : Fin R) (j0 : Fin S) (x : ℝ),
      χ (Matrix.fromBlocks (Matrix.diagonal (Function.update 1 i0 ((1 + 2 * Complex.I * x) / (1 - 2 * Complex.I * x)))) 0 0
        (Matrix.diagonal (Function.update 1 j0 ((1 - 2 * Complex.I * x) / (1 + 2 * Complex.I * x))))) = 1 := by
  first | exact @GlobalTheory.UnitaryCharRot.char_eq_one_rot | exact GlobalTheory.UnitaryCharRot.char_eq_one_rot | (intros; apply GlobalTheory.UnitaryCharRot.char_eq_one_rot <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralDiagonalCoordsEqPosMulAdeleHaarStatement
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped Matrix TensorProduct FourierTransform
open MeasureTheory GroundTheory.Automorphic.GJMatrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integral_diagonalCoords_eq_pos_mul_adeleHaar : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ], ∃ c₀ : ℝ, 0 < c₀ ∧ ∀ H : (κ → AF F) → ℂ, (Integrable (fun p => H (GlobalTheory.DiagForm.glue p)) (GlobalTheory.DiagForm.mu F κ) ↔ Integrable H (adeleMeasurePi F)) ∧ ∫ p, H (GlobalTheory.DiagForm.glue p) ∂(GlobalTheory.DiagForm.mu F κ) = c₀ * ∫ t, H t ∂(adeleMeasurePi F) := by
  first | exact @GlobalTheory.diagForm_glue_integral | exact GlobalTheory.diagForm_glue_integral | (intros; apply GlobalTheory.diagForm_glue_integral <;> assumption)
end

