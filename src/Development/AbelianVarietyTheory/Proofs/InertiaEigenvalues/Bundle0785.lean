import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StableIffCarrierEq
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsComp
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0779
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsAdelicUnitaryTrivialOutsideSplitPlaceLocEq
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0401
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0036
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsIrreducibleIffOfLinearEquiv
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0053
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0646
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.UnitaryAdmissibleMatrixCoefficient
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0001
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle0003
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IwahoriProjSurjective
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SupercuspidalSupportUniqueGL
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0194
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0237
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0362
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0781
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0749
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0754
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0014
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LengthPosOfPosDef
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0019
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0024
import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.GaussianBinomialClosedForm
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.SqNormIntegralFundamentalDomainEqL2NormSq
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0212
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0183

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GoodProjectorEqGoodIdempotentTypePlaces
section
open NumberField IsDedekindDomain ReciprocityTheory.Aut Formalism.AUTREP Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2 Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev GlobalTheory.TypeRec GlobalTheory.TypeVec
attribute [local instance] GlobalTheory.TypeRec.factG Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.RowGood

section Act

variable {D : D7} {V : HSp D} {β : GL (Fin V.rank) (EAf D)} {L : LevDat D.host.E ℂ V.rank}

theorem hasType_flag1 {P : LevelP L.Pg L.r ℂ} {F : Theta.GA D V → ℂ} (h : HasType V β (withP L P) F) : HasType V β (flag1L L) F := by
  intro κ hκ x
  have h1 : rTup β L (finE V κ) = 1 := hκ.2.2
  rw [h κ ⟨hκ.1, hκ.2.1, by
    show rTup β L (finE V κ) ∈ P.H
    rw [h1]; exact P.H.one_mem⟩ x]
  unfold levChi
  rw [levFn_withP, levFn_flag1, h1, blockDiagonalExtendByOnePrimeField_one, one_mul]

end Act

theorem asAlgebraHom_eq_sum {G H M : Type} [Fintype G] [Group H] [AddCommGroup M] [Module ℂ M] (ρ : Representation ℂ H M)
    (ε : G ≃ H) (a : MonoidAlgebra ℂ H) (z : M) : ρ.asAlgebraHom a z = ∑ g, a.coeff (ε g) • ρ (ε g) z := by
  classical
  induction a using MonoidAlgebra.induction_linear with
  | zero => simp
  | add a b ha hb => simp [ha, hb, add_smul, Finset.sum_add_distrib]
  | single h c =>
    obtain ⟨h, rfl⟩ := ε.surjective h
    rw [Representation.asAlgebraHom_single]
    simp [Finsupp.single_apply]

theorem pi_induction {I : Type} [Finite I] [DecidableEq I] {H : I → Type} [∀ i, Group (H i)] (p : (∀ i, H i) → Prop) (h1 : p 1)
    (hm : ∀ a b, p a → p b → p (a * b)) (hs : ∀ i x, p (Pi.mulSingle i x)) (a : ∀ i, H i) : p a := by
  cases nonempty_fintype I
  rw [← Finset.noncommProd_mulSingle a]
  exact Finset.noncommProd_induction _ _ _ p hm h1 fun i _ => hs i _

open scoped Classical in

theorem exists_act {D : D7} {s : ∀ k : Fin 2, D.nd.PlG k → SplitPlace D.host.E}
    {j : ∀ k v, ℚ_[D.host.g k] ≃+* (s k v).v.adicCompletion (maximalRealSubfield D.host.E)}
    {A : Type} [AddCommGroup A] [Module ℂ A] (ρA : GAf D.host.E D.R.r →* Module.End ℂ A)
    (ρ : Representation ℂ (G0g D.nd) (KFix D s j ρA))
    (hρ : ∀ k v y x, IsLiftAt (s k v) (j k v) y x → ∀ z,
      ((ρ (GlobalTheory.GoodTypes.facHom D k v (GlobalTheory.GLp.red (D.host.g k) D.R.r y)) z : KFix D s j ρA) : A) = ρA x z)
    (q : G0g D.nd → GAf D.host.E D.R.r → Prop) (q1 : q 1 1) (qm : ∀ a x b y, q a x → q b y → q (a * b) (x * y))
    (ql : ∀ k v y x, IsLiftAt (s k v) (j k v) y x → q (GlobalTheory.GoodTypes.facHom D k v (GlobalTheory.GLp.red (D.host.g k) D.R.r y)) x)
    (a : G0g D.nd) : ∃ x, q a x ∧ ∀ z, ((ρ a z : KFix D s j ρA) : A) = ρA x z := by
  refine pi_induction (fun a : G0g D.nd => ∃ x, q a x ∧ ∀ z, ((ρ a z : KFix D s j ρA) : A) = ρA x z) ?_ ?_ ?_ a
  · exact ⟨1, q1, fun z => by rw [map_one, map_one]; rfl⟩
  · rintro a b ⟨x, hx, hx'⟩ ⟨y, hy, hy'⟩
    exact ⟨x * y, qm _ _ _ _ hx hy, fun z => by rw [map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, hx', hy']⟩
  · rintro ⟨k, v⟩ h
    obtain ⟨y, rfl⟩ := GlobalTheory.GLp.Model.red_surjective (g := D.host.g k) D.R.r h
    obtain ⟨x, hx⟩ : ∃ x, IsLiftAt (s k v) (j k v) y x := GlobalTheory.SplitLift.exists_trivOutside_loc_eq D.R.r (s k v) _
    exact ⟨x, ql k v y x hx, hρ k v y x hx⟩

theorem levelChoiceData_eq_withLevel_trivial {D : D7} {T : Type} (C : LevCh D T) (P : LevelP C.Pg D.R.r ℂ) : C.dat0 P = withP (C.dat0 C.triv) P := rfl

theorem hasType_rows {D : D7} {T : Type} (C : LevCh D T) {Sp : D.what₂.Tau → _} (θ) (M : Mult.DSModel (Yc D 0) Sp)
    (P : LevelP C.Pg D.R.r ℂ) {Tm : Mult.MMap M}
    (h : Tm ∈ Mult.Mult θ M (levS _ (C.βY 0) (C.dat0 P)) (levChi _ (C.βY 0) (C.dat0 P))) (v : M.Vec) :
    HasType (Yc D 0) (C.βY 0) (flag1L (C.dat0 C.triv)) (Tm v) := by
  rw [levelChoiceData_eq_withLevel_trivial] at h
  exact hasType_flag1 (L := C.dat0 C.triv) (P := P) fun κ hκ x => principalLevelFrame.mult_lev h v κ hκ x

theorem levChi_flag {D : D7} {V : HSp D} {β : GL (Fin V.rank) (EAf D)} {L : LevDat D.host.E ℂ V.rank} (hs : L.s = 0) (hQ : L.Q = ∅)
    (x : Theta.GA D V) : levChi V β (flagL L) x = 1 := by
  unfold levChi levFn
  have h2 : ext1 (flagL L).P.H (flagL L).P.chi (rTup β (flagL L) (finE V x)) = 1 := subgroupCharExtension_one_apply _ _
  have h3 : (flagL L).s = 0 := hs
  have h4 : (flagL L).Q = ∅ := hQ
  rw [h2, h3, h4]
  simp

theorem fix_of_lifts_comp {D : D7} {s : ∀ k : Fin 2, D.nd.PlG k → SplitPlace D.host.E}
    {j : ∀ k v, ℚ_[D.host.g k] ≃+* (s k v).v.adicCompletion (maximalRealSubfield D.host.E)}
    {V : HSp D} {Sp : D.what₂.Tau → _} (P : principalLevelFrame.RowPsi V D.R.r) (M : Mult.DSModel V Sp) (β : GL (Fin V.rank) (EAf D))
    (L : LevDat D.host.E ℂ V.rank) (hs : L.s = 0) (hQ : L.Q = ∅) (φ : GAf D.host.E D.R.r →* GAf D.host.E D.R.r)
    (ρ : Representation ℂ (G0g D.nd) (KFix D s j ((principalLevelFrame.actM P M).comp φ)))
    (hρ : ∀ k v y x, IsLiftAt (s k v) (j k v) y x → ∀ z,
      ((ρ (GlobalTheory.GoodTypes.facHom D k v (GlobalTheory.GLp.red (D.host.g k) D.R.r y)) z : KFix D s j ((principalLevelFrame.actM P M).comp φ)) :
        Mult.MMap M) = ((principalLevelFrame.actM P M).comp φ) x z)
    {G : Type} [Group G] [Fintype G] (eG : G ≃* G0 L.Pg L.r) (c : G → ℂ) (cG : G0 L.Pg L.r ≃* G0g D.nd)
    (e : MonoidAlgebra ℂ (G0g D.nd)) (hc : ∀ g, e.coeff (cG (eG g)) = c g)
    (hl : ∀ k v y x, IsLiftAt (s k v) (j k v) y x →
      IsLevelLift V β L (cG.symm (GlobalTheory.GoodTypes.facHom D k v (GlobalTheory.GLp.red (D.host.g k) D.R.r y))) (P.ψ (φ x)))
    (Tm : Mult.MMap M) (hK : Tm ∈ KFix D s j ((principalLevelFrame.actM P M).comp φ))
    (hty : ∀ v, HasType V β (flag1L L) (Tm v)) (hfix : Mult.postOn M (gaL V β L eG c) Tm = Tm) :
    ρ.asAlgebraHom e ⟨Tm, hK⟩ = ⟨Tm, hK⟩ := by
  have key := exists_act ((principalLevelFrame.actM P M).comp φ) ρ hρ (fun a x => IsLevelLift V β L (cG.symm a) (P.ψ (φ x)))
    (by
      refine ⟨P.into _, ?_, ?_⟩
      · rw [map_one φ, map_one P.ψ, map_one (finE V)]; exact one_mem _
      · rw [map_one φ, map_one P.ψ, map_one (finE V), rTup_one, map_one])
    (fun a x b y hx hy => by
      refine ⟨P.into _, ?_, ?_⟩
      · rw [map_mul φ, map_mul P.ψ, map_mul (finE V)]; exact mul_mem hx.2.1 hy.2.1
      · rw [map_mul φ, map_mul P.ψ, map_mul (finE V), rTup_mul hx.2.1 hy.2.1, hx.2.2, hy.2.2, map_mul])
    hl
  apply Subtype.ext
  rw [asAlgebraHom_eq_sum ρ (eG.trans cG).toEquiv, Submodule.coe_sum]
  apply MultilinearMap.ext
  intro v
  funext h
  have h1 : (∑ g : G, c g • actL V β L (eG g)) (Tm v) h = Tm v h :=
    congrFun (congrArg (fun U : Mult.MMap M => U v) hfix) h
  rw [LinearMap.sum_apply, Finset.sum_apply] at h1
  rw [MultilinearMap.sum_apply, Finset.sum_apply]
  refine Eq.trans (Finset.sum_congr rfl fun g _ => ?_) h1
  obtain ⟨x, hx, hx'⟩ := key (cG (eG g))
  rw [MulEquiv.symm_apply_apply] at hx
  have h2 := level_action_spec (hty v) ⟨_, hx⟩ _ hx h
  rw [levChi_flag hs hQ, inv_one, one_mul] at h2
  have e1 : (eG.trans cG).toEquiv g = cG (eG g) := rfl
  rw [e1, hc, Submodule.coe_smul, hx']
  exact congrArg (c g * ·) h2.symm

theorem good_idem_fix_conj : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd) {X0 : BaseLevelRowSide D} (Y : GlobalTheory.Mem.R3.Read (A3 := A3) R.toRealDat F.lv2 X0), GlobalTheory.Mem.R3.Pins R F cG → ∀ (s : ∀ k : Fin 2, D.nd.PlG k → SplitPlace D.host.E) (j : ∀ k v, ℚ_[D.host.g k] ≃+* (s k v).v.adicCompletion (maximalRealSubfield D.host.E)), (∀ k v, (s k v).w = D.naut.plGw k v) → (∀ k v, Continuous (j k v)) → ∀ (c : GAf D.host.E D.R.r), (∀ (k : Fin 2) (v : D.nd.PlG k) (y : GL (Fin D.R.r) ℤ_[D.host.g k]) (x : GAf D.host.E D.R.r), IsLiftAt (s k v) (j k v) y x → IsLevelLift (Yc D 0) (R.βY 0) (R.dat0 R.triv) (cG.symm (GlobalTheory.GoodTypes.facHom D k v (GlobalTheory.GLp.red (D.host.g k) D.R.r y))) (Y.PY.ψ (c * x * c⁻¹))) → ∀ (ρ : Representation ℂ (G0g D.nd) (KFix D s j ((principalLevelFrame.actM Y.PY (R.MY 0)).comp (MulAut.conj c).toMonoidHom))), (∀ (k : Fin 2) (v : D.nd.PlG k) (y : GL (Fin D.R.r) ℤ_[D.host.g k]) (x : GAf D.host.E D.R.r), IsLiftAt (s k v) (j k v) y x → ∀ z, ((ρ (GlobalTheory.GoodTypes.facHom D k v (GlobalTheory.GLp.red (D.host.g k) D.R.r y)) z : KFix D s j ((principalLevelFrame.actM Y.PY (R.MY 0)).comp (MulAut.conj c).toMonoidHom)) : Mult.MMap (R.MY 0)) = ((principalLevelFrame.actM Y.PY (R.MY 0)).comp (MulAut.conj c).toMonoidHom) x z) → ∀ (b : Bool) (Tm : Mult.MMap (R.MY 0)) (hK : Tm ∈ KFix D s j ((principalLevelFrame.actM Y.PY (R.MY 0)).comp (MulAut.conj c).toMonoidHom)), Tm ∈ Mult.goodPart R.θ (R.MY 0) (levS _ (R.βY 0) (R.dat0 (R.toRealDat.levR F.lv2 b))) (levChi _ (R.βY 0) (R.dat0 (R.toRealDat.levR F.lv2 b))) R.toRealDat.e0 → ρ.asAlgebraHom D.ntypes.e0 ⟨Tm, hK⟩ = ⟨Tm, hK⟩ := by
  intro D G _ _ Pl0 I0 T A3 Ks _ _ _ R F cG X0 Y hP s j _ _ c hc ρ hρ b Tm hK hT
  obtain ⟨-, -, -, hco, -, -⟩ := hP.keep.grp
  exact fix_of_lifts_comp Y.PY (R.MY 0) (R.βY 0) (R.dat0 R.triv) rfl rfl (MulAut.conj c).toMonoidHom ρ hρ R.eG
    (RealDat.eC (A := A3.A) D.what₂.embLL) cG D.ntypes.e0 (fun g => (hco g).symm) hc Tm hK
    (fun v => hasType_rows R.toLevCh R.θ (R.MY 0) _ hT.1 v) (sub_eq_zero.1 (LinearMap.mem_ker.1 hT.2))

end GlobalTheory.RowGood

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IntegralGLPullbackContinuousRingEquiv
section
open IsDedekindDomain NumberField
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.IntegralPullback

open Filter Topology ValuativeRel

theorem valued_le_one_of_map {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E]
    {v : HeightOneSpectrum (𝓞 F)} {w : HeightOneSpectrum (𝓞 E)}
    (c : v.adicCompletion F ≃+* w.adicCompletion E) (hc : Continuous c) (z : v.adicCompletion F)
    (hz : Valued.v (c z) ≤ 1) : Valued.v z ≤ 1 := by
  by_contra h
  rw [not_le] at h
  have hz0 : z ≠ 0 := by
    rintro rfl
    simp at h
  have hcz : c z ≠ 0 := (map_ne_zero c).mpr hz0

  have hinv : Valued.v z⁻¹ < 1 := by
    rw [map_inv₀]
    exact inv_lt_one_of_one_lt₀ h
  have ht : Tendsto (fun n : ℕ => (c z⁻¹) ^ n) atTop (𝓝 0) := by
    have := (hc.tendsto 0).comp (Valued.tendsto_zero_pow_of_v_lt_one hinv)
    simpa [Function.comp_def, map_pow] using this

  have h1 : 1 ≤ Valued.v (c z⁻¹) := by
    rw [map_inv₀]
    calc (1 : WithZero (Multiplicative ℤ)) = Valued.v (c z)⁻¹ * Valued.v (c z) := by
          rw [← map_mul, inv_mul_cancel₀ hcz, map_one]
      _ ≤ Valued.v (c z)⁻¹ * 1 := by gcongr
      _ = Valued.v (c z)⁻¹ := mul_one _
  have hU : {y : w.adicCompletion E | Valued.v y < 1} ∈ 𝓝 (0 : w.adicCompletion E) :=
    Valued.mem_nhds_zero.mpr ⟨1, fun y hy => by simpa using hy⟩
  obtain ⟨n, hn⟩ := (ht.eventually_mem hU).exists
  have hn' : Valued.v ((c z⁻¹) ^ n) < 1 := hn
  rw [map_pow] at hn'
  exact absurd hn' (not_lt.mpr (one_le_pow₀ h1))

theorem mem_integer_iff {E : Type} [Field E] [NumberField E] {w : HeightOneSpectrum (𝓞 E)}
    (z : w.adicCompletion E) :
    z ∈ (valuation (w.adicCompletion E)).integer ↔ Valued.v z ≤ 1 := by
  rw [Valuation.mem_integer_iff, ← Valuation.vle_one_iff (valuation (w.adicCompletion E))]
  show Valued.v z ≤ Valued.v 1 ↔ _
  rw [map_one]

private theorem mem_KO_of_integral_entries' {F : Type} [Field F] [NumberField F]
    {v : HeightOneSpectrum (𝓞 F)} {n : ℕ} (A : GL (Fin n) (v.adicCompletion F))
    (h1 : ∀ i j, (A : Matrix (Fin n) (Fin n) (v.adicCompletion F)) i j ∈
      (valuation (v.adicCompletion F)).integer)
    (h2 : ∀ i j, ((A⁻¹ : GL (Fin n) (v.adicCompletion F)) :
      Matrix (Fin n) (Fin n) (v.adicCompletion F)) i j ∈ (valuation (v.adicCompletion F)).integer) :
    A ∈ GlobalTheory.SplitWeil.KO (v.adicCompletion F) (Fin n) := by

  let P : Matrix (Fin n) (Fin n) (valuation (v.adicCompletion F)).integer :=
    Matrix.of fun i j => ⟨_, h1 i j⟩
  let Q : Matrix (Fin n) (Fin n) (valuation (v.adicCompletion F)).integer :=
    Matrix.of fun i j => ⟨_, h2 i j⟩
  let f := algebraMap (valuation (v.adicCompletion F)).integer (v.adicCompletion F)
  have hP : P.map f = (A : Matrix (Fin n) (Fin n) _) := by
    ext i j
    simp only [P, f, Matrix.map_apply, Matrix.of_apply, Algebra.algebraMap_ofSubsemiring_apply]
  have hQ : Q.map f = ((A⁻¹ : GL (Fin n) _) : Matrix (Fin n) (Fin n) _) := by
    ext i j
    simp only [Q, f, Matrix.map_apply, Matrix.of_apply, Algebra.algebraMap_ofSubsemiring_apply]
  have inj : ∀ X Y : Matrix (Fin n) (Fin n) (valuation (v.adicCompletion F)).integer,
      X.map f = Y.map f → X = Y := by
    intro X Y h
    exact Matrix.ext fun i j => Subtype.ext (congrFun (congrFun h i) j)
  have hPQ : P * Q = 1 := inj _ _ (by
    rw [Matrix.map_mul, Matrix.map_one f (map_zero f) (map_one f), hP, hQ]
    exact A.mul_inv)
  have hQP : Q * P = 1 := inj _ _ (by
    rw [Matrix.map_mul, Matrix.map_one f (map_zero f) (map_one f), hP, hQ]
    exact A.inv_mul)
  unfold GlobalTheory.SplitWeil.KO
  refine MonoidHom.mem_range.mpr ⟨⟨P, Q, hPQ, hQP⟩, ?_⟩
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  rw [Matrix.GeneralLinearGroup.map_apply]
  exact congrFun (congrFun hP i) j

private theorem entry_mem_integer_of_map_mem_KO {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E]
    {v : HeightOneSpectrum (𝓞 F)} {w : HeightOneSpectrum (𝓞 E)}
    (c : v.adicCompletion F ≃+* w.adicCompletion E) (hc : Continuous c) {n : ℕ}
    (M : GL (Fin n) (v.adicCompletion F))
    (hM : Matrix.GeneralLinearGroup.map c.toRingHom M ∈ GlobalTheory.SplitWeil.KO (w.adicCompletion E) (Fin n))
    (i j : Fin n) :
    (M : Matrix (Fin n) (Fin n) (v.adicCompletion F)) i j ∈
      (valuation (v.adicCompletion F)).integer := by
  unfold GlobalTheory.SplitWeil.KO at hM
  obtain ⟨C, hC⟩ := MonoidHom.mem_range.mp hM
  rw [GlobalTheory.IntegralPullback.mem_integer_iff]
  apply valued_le_one_of_map c hc
  rw [← GlobalTheory.IntegralPullback.mem_integer_iff]
  have hij := congrArg (fun g : GL (Fin n) (w.adicCompletion E) =>
    (g : Matrix (Fin n) (Fin n) (w.adicCompletion E)) i j) hC
  simp only [Matrix.GeneralLinearGroup.map_apply] at hij
  have : c ((M : Matrix (Fin n) (Fin n) (v.adicCompletion F)) i j) =
      ((C : Matrix (Fin n) (Fin n) (valuation (w.adicCompletion E)).integer) i j :
        w.adicCompletion E) := hij.symm
  rw [this]
  exact ((C : Matrix (Fin n) (Fin n) (valuation (w.adicCompletion E)).integer) i j).2

theorem mem_KO_of_map : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] {v : HeightOneSpectrum (𝓞 F)} {w : HeightOneSpectrum (𝓞 E)} (c : v.adicCompletion F ≃+* w.adicCompletion E), Continuous c → ∀ {n : ℕ} (A : GL (Fin n) (v.adicCompletion F)), Matrix.GeneralLinearGroup.map c.toRingHom A ∈ GlobalTheory.SplitWeil.KO (w.adicCompletion E) (Fin n) → A ∈ GlobalTheory.SplitWeil.KO (v.adicCompletion F) (Fin n) := by
  intro F E _ _ _ _ v w c hc n A hA
  have hAinv : Matrix.GeneralLinearGroup.map c.toRingHom A⁻¹ ∈
      GlobalTheory.SplitWeil.KO (w.adicCompletion E) (Fin n) := by
    rw [map_inv]
    exact inv_mem hA
  exact mem_KO_of_integral_entries' A (entry_mem_integer_of_map_mem_KO c hc A hA) (entry_mem_integer_of_map_mem_KO c hc A⁻¹ hAinv)

end GlobalTheory.IntegralPullback
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsCuspidalJacquetModuleSecondBlockOfVanishing
section
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel Topology

namespace GlobalTheory.JacMinCuspGL

open GlobalTheory.SmGL.CuspMax GlobalTheory.JacMinCusp Matrix

theorem isCuspidal_jac₂_inr : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (a b n : ℕ) (h : a + b = n) (V : Type) [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GL (Fin n) k) V), IsSmooth π →
    (∀ (r t : ℕ) (h' : r + t = n), 0 < t → t < b → Subsingleton (Jacquet π (unipRad k (two (stdSum h'))))) →
    IsCuspidal (k := k) (n := Fin b) ((jac₂ (stdSum h) π).comp (MonoidHom.inr (GL (Fin a) k) (GL (Fin b) k))) := by
  intro k _ _ _ _ a b n h V _ _ π hπ hmin
  set J := (jac₂ (stdSum h) π).comp (MonoidHom.inr (GL (Fin a) k) (GL (Fin b) k)) with hJdef
  refine (isCuspidal_iff_maximal k b _ J).2 ⟨isSmooth_comp (isSmooth_jac₂ _ hπ) _
    (continuous_const.prodMk continuous_id :
      Continuous fun x : GL (Fin b) k => ((1 : GL (Fin a) k), x)),
    fun r t h' hr ht => ?_⟩
  have hcd : a + r + t = n := by omega
  have hJ : twKer π (unipRad k (two (stdSum hcd))) 1 = ⊤ :=
    Submodule.Quotient.subsingleton_iff.1 (hmin (a + r) t hcd ht (by omega))
  set Kab := twKer π (unipRad k (two (stdSum h))) 1 with hKab
  set K' := twKer J (unipRad k (two (stdSum h'))) 1 with hK'

  have hB : ∀ g : GL (Fin a) k × GL (Fin b) k, g.1 = 1 → GeneralLinearGroup.det g.2 = 1 → ∀ v : V,
      jac₂ (stdSum h) π g (Submodule.Quotient.mk v) =
        Submodule.Quotient.mk (π (leviEmb k (two (stdSum h)) (leviTwo k _ _ g)) v) := by
    intro g h1 h2 v
    have hd : deltaHalf k (Two (Fin a) (Fin b)) (leviTwo k _ _ g) = 1 := by
      rw [deltaHalf_two, h1, h2]; simp
    show jac (two (stdSum h)) π (leviTwo k _ _ g) _ = _
    rw [jac_mk, hd]; simp
  have hN : ∀ u ∈ unipRad k (two (stdSum h)), ∀ v : V,
      (Submodule.Quotient.mk (π u v) : V ⧸ Kab) = Submodule.Quotient.mk v := by
    intro u hu v
    exact (Submodule.Quotient.eq Kab).2 (Submodule.subset_span ⟨⟨u, hu⟩, v, by simp⟩)

  have hC : ∀ u ∈ unipRad k (two (stdSum hcd)), ∀ v : V,
      (Submodule.Quotient.mk (π u v) : V ⧸ Kab) - Submodule.Quotient.mk v ∈ K' := by
    intro u hu v
    have hu' := (mem_unipRad_two_iff hcd).1 hu
    have hp : u ∈ parab k (two (stdSum h)) := by
      rw [mem_parab]
      intro i j hij
      rw [blk_two_stdSum_lt] at hij
      rw [hu' i j (by omega), Matrix.one_apply_ne]
      intro hij'; subst hij'; omega
    obtain ⟨n', hn', hun⟩ := exists_levi_mul_unip k (two (stdSum h)) ⟨u, hp⟩
    set g := (leviTwo k (Fin a) (Fin b)).symm (leviProj k (two (stdSum h)) ⟨u, hp⟩) with hg
    have hlg : leviTwo k _ _ g = leviProj k (two (stdSum h)) ⟨u, hp⟩ := by simp [g]
    have hg1 : g.1 = 1 := by
      ext i j
      show (leviProj k (two (stdSum h)) ⟨u, hp⟩ false : Matrix (Fin a) (Fin a) k) i j = _
      rw [leviProj_apply, two_false, two_false]
      rw [hu' _ _ (by simp; omega)]
      simp [Matrix.one_apply, stdSum]
    have hg2 : g.2 ∈ unipRad k (two (stdSum h')) := by
      rw [mem_unipRad_two_iff]
      intro i j hij
      show (leviProj k (two (stdSum h)) ⟨u, hp⟩ true : Matrix (Fin b) (Fin b) k) i j = _
      rw [leviProj_apply, two_true, two_true]
      rw [hu' _ _ (by simp; omega)]
      simp [Matrix.one_apply, stdSum]
    have hdet : GeneralLinearGroup.det g.2 = 1 := det_eq_one_of_mem_unipRad k hg2
    have hu_eq : u = leviEmb k (two (stdSum h)) (leviTwo k _ _ g) * n' := by rw [hlg]; exact hun
    have hJu : J g.2 (Submodule.Quotient.mk v) = Submodule.Quotient.mk (π u v) := by
      rw [hu_eq, map_mul, Module.End.mul_apply]
      show jac₂ (stdSum h) π (1, g.2) _ = _
      rw [hB (1, g.2) rfl hdet, show ((1, g.2) : GL (Fin a) k × GL (Fin b) k) = g from Prod.ext hg1.symm rfl]
      refine (Submodule.Quotient.eq Kab).2 ?_
      rw [← map_sub]
      refine twKer_le_comap π _ _ (leviEmb_mem_normalizer k _ _) ?_
      have := (Submodule.Quotient.eq Kab).1 (hN n' hn' v)
      rw [← neg_sub]
      exact Kab.neg_mem this
    rw [← hJu]
    exact Submodule.subset_span ⟨⟨g.2, hg2⟩, Submodule.Quotient.mk v, by simp⟩
  refine Submodule.Quotient.subsingleton_iff.2 (eq_top_iff.2 fun x _ => ?_)
  obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective Kab x
  have hle : twKer π (unipRad k (two (stdSum hcd))) 1 ≤ K'.comap Kab.mkQ := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨u, w, rfl⟩
    simpa [Submodule.mkQ_apply] using hC u u.2 w
  exact hle (hJ ▸ Submodule.mem_top)

end GlobalTheory.JacMinCuspGL
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsSubquotientJacquetModuleRefineTensorStatement
section
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL ValuativeRel
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isSubquotient_jacquetModule_refine_tensor : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (n s : ℕ) (d : Fin s → ℕ) (e : (Σ a, Fin (d a)) ≃ Fin n) (V : Type) [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GL (Fin n) k) V), IsSmooth π →
    ∀ (X : Fin s → Type) [∀ a, AddCommGroup (X a)] [∀ a, Module ℂ (X a)]
    (ρ : ∀ a, Representation ℂ (GL (Fin (d a)) k) (X a)), (∀ a, IsSmooth (ρ a)) →
    IsSubquotient (piTensor ρ) (jac e π) →
    ∀ (t : Fin s → ℕ) (d' : ∀ a, Fin (t a) → ℕ) (e' : ∀ a, (Σ b, Fin (d' a b)) ≃ Fin (d a))
    (Y : ∀ a, Fin (t a) → Type) [∀ a b, AddCommGroup (Y a b)] [∀ a b, Module ℂ (Y a b)]
    (ρ' : ∀ a b, Representation ℂ (GL (Fin (d' a b)) k) (Y a b)),
    (∀ a, IsSubquotient (piTensor (ρ' a)) (jac (e' a) (ρ a))) →
    ∃ E : (Σ c : Fin (∑ a, t a), Fin (d' (finSigmaFinEquiv.symm c).1 (finSigmaFinEquiv.symm c).2)) ≃ Fin n,
      IsSubquotient (piTensor fun c => ρ' (finSigmaFinEquiv.symm c).1 (finSigmaFinEquiv.symm c).2) (jac E π) := by
  first | exact @GlobalTheory.JacStages.isSubquotient_jac_refine | exact GlobalTheory.JacStages.isSubquotient_jac_refine | (intros; apply GlobalTheory.JacStages.isSubquotient_jac_refine <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsUnitBlockDetOfConjLower
section
open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.SchurExt
open scoped ContDiff Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isUnit_block_det_of_conj_lower : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (m r : ℕ) (x : GA E (m + r + 1 + 1)) (k : GL (Fin (m + r + 1 + 1)) (Af E)), IsUnit (Dof (x : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E))).det → IsUnit (Dof (conjLowUni ((Yof (x : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E))).map (pFin E)) (k : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Af E)))).det → IsUnit (Scof (x : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E))).det ∧ IsUnit (Dof ((x * finGL E (m + r + 1 + 1) k : GA E (m + r + 1 + 1)) : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E))).det ∧ mkGL (Dof ((x * finGL E (m + r + 1 + 1) k : GA E (m + r + 1 + 1)) : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E))) = mkGL (Dof (x : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E))) * finGL E (r + 1) (mkGL (Dof (conjLowUni ((Yof (x : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E))).map (pFin E)) (k : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Af E))))) ∧ mkGL (Scof ((x * finGL E (m + r + 1 + 1) k : GA E (m + r + 1 + 1)) : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E))) = mkGL (Scof (x : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E))) * finGL E (m + 1) (mkGL (Scof (conjLowUni ((Yof (x : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E))).map (pFin E)) (k : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Af E))))) ∧ (∀ i j, pInf E (Yof ((x * finGL E (m + r + 1 + 1) k : GA E (m + r + 1 + 1)) : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E)) i j) = pInf E (Yof (x : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E)) i j)) ∧ (∀ i j, pFin E (Yof ((x * finGL E (m + r + 1 + 1) k : GA E (m + r + 1 + 1)) : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E)) i j) = pFin E (Yof (x : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E)) i j) + Yof (conjLowUni ((Yof (x : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E))).map (pFin E)) (k : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Af E))) i j) ∧ Xof ((x * finGL E (m + r + 1 + 1) k : GA E (m + r + 1 + 1)) : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E)) (Fin.last m) 0 = Xof (x : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E)) (Fin.last m) 0 + sFin E (∑ j, ∑ l, pFin E (Scof (x : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E)) (Fin.last m) j) * Xof (conjLowUni ((Yof (x : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E))).map (pFin E)) (k : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Af E))) j l * pFin E ((Dof (x : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E)))⁻¹ l 0)) := by
  first | (exact @GlobalTheory.SchurExt.AdBridge.schur_data_mul_finGL) | (exact GlobalTheory.SchurExt.AdBridge.schur_data_mul_finGL) | (intros; apply GlobalTheory.SchurExt.AdBridge.schur_data_mul_finGL <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.KummerCharacterFactorsAbsoluteGaloisAbelianization
section
open NumberField IsDedekindDomain Polynomial Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host GlobalTheory.HeckeGal GlobalTheory.WeilDeligne GlobalTheory.LocGL GlobalTheory.LocLanglands GlobalTheory.GLq GlobalTheory.SmGL Formalism.L2.NT

namespace GlobalTheory.KummerAb

theorem kummer_char_eq_of_toAb_eq : ∀ (E' Ω : Type) [Field E'] [NumberField E'] [Field Ω] [Algebra E' Ω] [IsAlgClosure E' Ω]
    (m : ℕ) (hm : 0 < m) (ζ : E') (hζ : IsPrimitiveRoot ζ m) (c : E') (hc : c ≠ 0) (y : Ω)
    (hy : y ^ m = algebraMap E' Ω c) (σ τ : G E' Ω) (he : toAb E' Ω σ = toAb E' Ω τ), σ y / y = τ y / y := by
  intro E' Ω _ _ _ _ _ m hm ζ hζ c hc y hy σ τ he
  have hc' : algebraMap E' Ω c ≠ 0 := (map_ne_zero_iff _ (algebraMap E' Ω).injective).mpr hc
  have hy0 : y ≠ 0 := by
    rintro rfl
    rw [zero_pow hm.ne'] at hy
    exact hc' hy.symm
  haveI : NeZero m := ⟨hm.ne'⟩
  have hζ' : IsPrimitiveRoot (algebraMap E' Ω ζ) m := hζ.map_of_injective (algebraMap E' Ω).injective
  have key : ∀ ρ : G E' Ω, ∃ e : E', ρ y = algebraMap E' Ω e * y := by
    intro ρ
    have h1 : (ρ y / y) ^ m = 1 := by
      rw [div_pow, ← map_pow, hy, AlgEquiv.commutes, div_self hc']
    obtain ⟨i, -, hi⟩ := hζ'.eq_pow_of_pow_eq_one h1
    refine ⟨ζ ^ i, ?_⟩
    rw [map_pow, hi, div_mul_cancel₀ _ hy0]
  let φ : G E' Ω →* Ωˣ := MonoidHom.mk' (fun ρ => Units.mk0 (ρ y / y)
      (div_ne_zero ((map_ne_zero_iff _ ρ.injective).mpr hy0) hy0)) (by
    intro a b
    ext
    obtain ⟨e, he⟩ := key b
    simp only [Units.val_mul, Units.val_mk0, AlgEquiv.mul_apply, he, map_mul, AlgEquiv.commutes]
    field_simp)
  have hφ : ∀ ρ, (φ ρ : Ω) = ρ y / y := fun ρ => rfl
  have hint : IsIntegral E' y := Algebra.IsIntegral.isIntegral y
  haveI : FiniteDimensional E' (IntermediateField.adjoin E' {y}) := IntermediateField.adjoin.finiteDimensional hint
  have hopen : IsOpen (φ.ker : Set (G E' Ω)) := by
    refine Subgroup.isOpen_mono (H₁ := (IntermediateField.adjoin E' {y}).fixingSubgroup) ?_ (IntermediateField.fixingSubgroup_isOpen _)
    intro ρ hρ
    have : ρ y = y := (IntermediateField.mem_fixingSubgroup_iff _ _).mp hρ y
      (IntermediateField.subset_adjoin E' {y} rfl)
    rw [MonoidHom.mem_ker]
    ext
    rw [hφ, this, div_self hy0, Units.val_one]
  have hclosed : IsClosed (φ.ker : Set (G E' Ω)) := Subgroup.isClosed_of_isOpen _ hopen
  have hle : (commutator (G E' Ω)).topologicalClosure ≤ φ.ker :=
    Subgroup.topologicalClosure_minimal _ (Abelianization.commutator_subset_ker φ) hclosed
  have hmem : σ⁻¹ * τ ∈ (commutator (G E' Ω)).topologicalClosure := QuotientGroup.eq.mp he
  have h2 := hle hmem
  rw [MonoidHom.mem_ker, map_mul, map_inv, inv_mul_eq_one] at h2
  rw [← hφ, ← hφ, h2]

end GlobalTheory.KummerAb
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.L2OHeisOEq
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift

noncomputable section

namespace GlobalTheory.HeisTranslateBound

open GlobalTheory.Size GlobalTheory.OrientedHeis

theorem l2O_heisO_eq {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {S T : HSp D}
    (hψ : IsStdChar D ψ (-1)) (hθ : IsInfFam θ) {μ : Measure (WO S T)} {𝓕 : Set (WO S T)}
    (hμ : IsCovolOne (ratL T S) μ 𝓕) {g : WO S T → ℂ} (hg : IsThetaFunO ψ S T g) (u : WO S T) :
    l2O μ 𝓕 (heisO ψ S T u g) = l2O μ 𝓕 g := by
  have hg' := GlobalTheory.Unf.MatCoef.theta_heisO_any hψ hθ hg u
  have e := ipO_heisO hψ hμ.1 hμ.2.1 hg hg u
  rw [ipO_self, ipO_self, sqNormIntegralFundamentalDomain_eq_l2Norm_sq μ 𝓕 hg'.cont, sqNormIntegralFundamentalDomain_eq_l2Norm_sq μ 𝓕 hg.cont, Complex.ofReal_inj,
    pow_left_inj₀ ENNReal.toReal_nonneg ENNReal.toReal_nonneg two_ne_zero] at e
  exact (ENNReal.toReal_eq_toReal_iff' (l2NormOnFundamentalDomain_thetaFunction_ne_top hψ hμ.1 hμ.2.1 hg') (l2NormOnFundamentalDomain_thetaFunction_ne_top hψ hμ.1 hμ.2.1 hg)).1 e

theorem sobO_heisO_eq {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {S T : HSp D}
    (hψ : IsStdChar D ψ (-1)) (hθ : IsInfFam θ) {μ : Measure (WO S T)} {𝓕 : Set (WO S T)}
    (hμ : IsCovolOne (ratL T S) μ 𝓕) {h : WO S T → ℂ} (hh : IsThetaFunO ψ S T h) {u : WO S T}
    (hu : u.map (infPart D) = 0) (d : ℕ) :
    sobO ψ θ μ 𝓕 d (heisO ψ S T u h) = sobO ψ θ μ 𝓕 d h := by
  have := wordSum_eq_mul (A := heisDer ψ θ) (p := l2O μ 𝓕) (d := d) (x := h) (y := heisO ψ S T u h) (c := 1)
    fun l => by
      have e : wordAct (heisDer ψ θ) l (heisO ψ S T u h) = heisO ψ S T u (wordAct (heisDer ψ θ) l h) :=
        wordAct_rel (R := fun g g' => g = heisO ψ S T u g') l
          (fun a _ _ _ e => e ▸ GlobalTheory.FinTranslate.dRho_heisO hθ hu a.1 _ _) rfl
      rw [e, one_mul, l2O_heisO_eq hψ hθ hμ (theta_word hψ hθ l hh) u]
  rw [one_mul] at this
  exact this

end GlobalTheory.HeisTranslateBound

open GlobalTheory.Size GlobalTheory.HeisTranslateBound GlobalTheory.OrientedHeis in

theorem GlobalTheory.HeisTranslateBound.sobO_finsupp_sum_le : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D), IsStdChar D ψ (-1) → IsInfFam θ → ∀ (μ : Measure (WO S T)) (𝓕 : Set (WO S T)), IsCovolOne (ratL T S) μ 𝓕 → ∀ c : WO S T →₀ ℂ, (∀ u ∈ c.support, u.map (infPart D) = 0) → ∀ h : WO S T → ℂ, IsThetaFunO ψ S T h → ∀ d : ℕ, GlobalTheory.Size.sobO ψ θ μ 𝓕 d (c.sum fun u z => z • heisO ψ S T u h) ≤ (∑ u ∈ c.support, ‖c u‖ₑ) * GlobalTheory.Size.sobO ψ θ μ 𝓕 d h := by
  intro D ψ θ S T hψ hθ μ 𝓕 hμ c hc h hh d
  have ht : ∀ u, IsThetaFunO ψ S T (c u • heisO ψ S T u h) := fun u =>
    theta_smul (c u) (GlobalTheory.Unf.MatCoef.theta_heisO_any hψ hθ hh u)
  refine (sobO_sum_le hψ hθ c.support (g := fun u => c u • heisO ψ S T u h) (fun u _ => ht u) d).trans ?_
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun u hu => ?_
  rw [sobO_smul, sobO_heisO_eq hψ hθ hμ hh (hc u hu)]
end
end

