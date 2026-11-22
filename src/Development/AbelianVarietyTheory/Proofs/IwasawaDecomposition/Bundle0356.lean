import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExponentAndTwistData
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.TupOfOneMemLabT
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.T2SpaceAdelicGeneralLinearGroupNumberField
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0222
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsMulRightInvariantOfFundamentalDomain
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.DefClassNum
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.IdeleClassFiniteness.Bundle0001
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.IdeleClassFiniteness.LatticeIdealNonzero
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0300
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0309
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0316
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0302
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0337
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0341
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.GoodPartHasComplexCoordinates
import Formalism.LocalToGlobal.IndefiniteReal.BaseLiftsPackageOfPrimitiveLinks
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0027
import Formalism.LocalToGlobal.Divisibility.DivisionCompatibleToSub2Indef2
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0030
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0032
import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowsJoinPinned
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowLevelMatch
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0199
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0206
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0245
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0205
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0247
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0207
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0203
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0320
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0204
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnitsLiftSpec
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Formalism.LocalToGlobal.NumberFieldFamilies.JMtInjective
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteDimensionalAdjoinRange
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0101
import Development.AutomorphicArithmetic.CyclotomicBounds.Bundle0002
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0343
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0283
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0001
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0007
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0322
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0019

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsCentralGroupAlgebraIdempotentUniversal
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.HeightCounting.FormsStep NumberField IsDedekindDomain Polynomial
open scoped TensorProduct

namespace GlobalTheory.HeightCounting.FormsStep

theorem eIdem_all : ∀ D : D7, EIdem D := by
  intro D
  haveI : ∀ k, Fact (D.host.g k).Prime := fun k => ⟨D.host.g_prime k⟩
  haveI : ∀ k, NeZero (D.host.g k) := fun k => ⟨(D.host.g_prime k).ne_zero⟩
  let φ : ↥D.LL0 →+* ℂ := D.what₂.embLL.comp (algebraMap ↥D.LL0 D.what₂.LL)
  have hφ : Function.Injective φ := φ.injective
  let M := MonoidAlgebra.mapRangeRingHom (G0g D.nd) φ
  have hM : Function.Injective M := by
    intro x y h
    refine MonoidAlgebra.ext (Finsupp.ext fun g => hφ ?_)
    have := congrArg (fun z => z.coeff g) h
    simpa [M, MonoidAlgebra.mapRangeRingHom] using this
  have he : M (eL D) = D.ntypes.e0 := by
    refine MonoidAlgebra.ext (Finsupp.ext fun g => ?_)
    have := D.nStage_trivialCharacter_coeff_eq g
    simpa [M, eL, MonoidAlgebra.mapRangeRingHom, φ] using this
  have hc : ∀ a, D.ntypes.e0 * a = a * D.ntypes.e0 := fun a => by
    rw [← GlobalTheory.RowLev.ES_good]; exact GlobalTheory.RowLev.ES_comm _ a
  have hi : D.ntypes.e0 * D.ntypes.e0 = D.ntypes.e0 := by
    rw [← GlobalTheory.RowLev.ES_good]; exact GlobalTheory.RowLev.ES_mul_self _
  have hs : ∀ g : G0g D.nd, M (MonoidAlgebra.of _ _ g) = MonoidAlgebra.of _ _ g := fun g => by
    simp [M, MonoidAlgebra.of_apply, MonoidAlgebra.mapRangeRingHom]
  refine ⟨hM ?_, fun g => hM ?_⟩
  · rw [map_mul, he, hi]
  · rw [map_mul, map_mul, he, hs, hc]

end GlobalTheory.HeightCounting.FormsStep
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsFiniteMeasureQuotMeasure
section
open NumberField IsDedekindDomain Matrix MeasureTheory Topology
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.UnitaryBC GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL

noncomputable section

namespace GlobalTheory.CovolGL

theorem lcsc_GL (R : Type) [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] [T2Space R]
    [LocallyCompactSpace R] [SecondCountableTopology R] (n : ℕ) :
    LocallyCompactSpace (GL (Fin n) R) ∧ SecondCountableTopology (GL (Fin n) R) := by
  haveI : LocallyCompactSpace (Matrix (Fin n) (Fin n) R) := inferInstanceAs (LocallyCompactSpace (Fin n → Fin n → R))
  haveI : LocallyCompactSpace (Matrix (Fin n) (Fin n) R)ᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.isClosedEmbedding.locallyCompactSpace
  haveI : SecondCountableTopology (Matrix (Fin n) (Fin n) R) :=
    inferInstanceAs (SecondCountableTopology (Fin n → Fin n → R))
  haveI : SecondCountableTopology (Matrix (Fin n) (Fin n) R)ᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.isEmbedding.secondCountableTopology
  exact ⟨Units.isClosedEmbedding_embedProduct.locallyCompactSpace, Units.isEmbedding_embedProduct.secondCountableTopology⟩

variable {E : Type} [Field E] [NumberField E] {a : ℕ}

theorem pFin_ratGL (γ : GL (Fin a) E) :
    GeneralLinearGroup.map (pFin E) (ratGL E a γ) = PIW.ClassFinD.glIncl E a γ := by
  ext i j
  rfl

variable [IsTotallyComplex E]

theorem pFin_splitCentre (t : ℝ) : GeneralLinearGroup.map (pFin E) (splitCentre E a t) = 1 :=
  pFin_infGL _

variable (E a) in

theorem isFiniteMeasure_quotMeasure (μ : Measure (GA E a)) [μ.IsHaarMeasure] :
    IsFiniteMeasure (GlobalTheory.AutomorphicL2Unitary.quotMeasure (latticeGL E a) μ) := by
  classical
  haveI := GlobalTheory.AdelicUnitaryTop.locallyCompact_finiteAdele E
  haveI := GlobalTheory.AdelicUnitaryTop.secondCountable_finiteAdele E
  haveI := GlobalTheory.AdelicUnitaryTop.t2Space_finiteAdeleRing_of_numberField E
  letI : MeasurableSpace (GL (Fin a) (Cinf E)) := borel _
  haveI : BorelSpace (GL (Fin a) (Cinf E)) := ⟨rfl⟩
  letI : MeasurableSpace (GL (Fin a) (Af E)) := borel _
  haveI : BorelSpace (GL (Fin a) (Af E)) := ⟨rfl⟩
  obtain ⟨_, _⟩ := lcsc_GL (Cinf E) a
  obtain ⟨_, _⟩ := lcsc_GL (Af E) a
  obtain ⟨e, he⟩ := GlobalTheory.T.exists_adelicGL_homeomorph_infinite_finite E a
  obtain ⟨S, hS⟩ := PIW.ClassFinD.borelKGL_of GlobalTheory.T.iwasawaDecomposition_finiteAdeles_GL GlobalTheory.T.strongApproximation_upperUnitriangular_finiteAdeles PIW.ClassFinD.idele_class_finite E a
  choose Λ hΛ hΛK using fun s => GlobalTheory.T.exists_lattice_stabilizer_conj_finiteAdeleGL_integral E a s
  choose Ω hΩ hcov using fun s => GlobalTheory.T.exists_finite_measure_reduction_domain_infinity E a (Λ s) (hΛ s) (Measure.haar : Measure (GL (Fin a) (Cinf E)))
  refine ⟨?_⟩
  rw [quotMeasure_univ (isFundamentalDomain_stdDom (latticeGL E a) μ)]
  refine GlobalTheory.Mem.VolFin.measure_lt_top_of_cover e (latticeGL E a) μ S (PIW.ClassFinD.KGL E a) (GlobalTheory.T.isCompact_integralGL_finiteAdeles E a) Ω hΩ
    (fun g => ?_) _ (isFundamentalDomain_stdDom _ μ)
  obtain ⟨γ, s, hs, k, hk, hx⟩ := hS (GeneralLinearGroup.map (pFin E) g)
  obtain ⟨η, hη, n, hn⟩ := hcov s (GeneralLinearGroup.map (pInf E) (ratGL E a γ⁻¹ * g))
  have hmem : ratGL E a η * splitCentre E a 1 ^ n * ratGL E a γ⁻¹ ∈ latticeGL E a :=
    mul_mem (mul_mem (ratGL_mem_latticeGL η) (zpow_mem_latticeGL n)) (ratGL_mem_latticeGL _)
  have hg : ratGL E a η * splitCentre E a 1 ^ n * ratGL E a γ⁻¹ * g =
      (ratGL E a η * splitCentre E a 1 ^ n) * (ratGL E a γ⁻¹ * g) := by simp only [mul_assoc]
  refine ⟨⟨_, hmem⟩, s, hs, ?_, ?_⟩
  · rw [Subgroup.smul_def, smul_eq_mul, he, hg, map_mul]
    exact hn
  · rw [Subgroup.smul_def, smul_eq_mul, he]
    simp only [map_mul, map_zpow, pFin_ratGL, pFin_splitCentre, _root_.one_zpow, mul_one, hx, map_inv]
    refine ⟨s⁻¹ * PIW.ClassFinD.glIncl E a η * s * k, (PIW.ClassFinD.KGL E a).mul_mem (hΛK s η hη) hk, ?_⟩
    simp only [smul_eq_mul]
    group

variable (E a) in

theorem isMulRightInvariant (μ : Measure (GA E a)) [μ.IsHaarMeasure] : μ.IsMulRightInvariant := by
  have hd := isFundamentalDomain_stdDom (latticeGL E a) μ
  have hfin := isFiniteMeasure_quotMeasure E a μ
  have h1 : μ (stdDom (latticeGL E a)) ≠ ⊤ := by
    rw [← quotMeasure_univ hd]; exact measure_ne_top _ _
  exact GlobalTheory.UnitU.isMulRightInvariant_of_fundamentalDomain _ μ hd (hd.measure_ne_zero (NeZero.ne μ)) h1

theorem finvol : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (μ : Measure (GA E a))
    [μ.IsHaarMeasure], IsFiniteMeasure (GlobalTheory.AutomorphicL2Unitary.quotMeasure (latticeGL E a) μ) ∧ μ.IsMulRightInvariant :=
  fun E _ _ _ a μ _ => ⟨isFiniteMeasure_quotMeasure E a μ, isMulRightInvariant E a μ⟩

end GlobalTheory.CovolGL
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsFixedBasisReductionMapConj
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.AutomorphicEvaluation Formalism.L2.DIV Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ConcreteSettingExists MeasureTheory NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.SRe
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.SRe

theorem cong_zsmul {V : Type*} [AddCommGroup V] (W : AddSubgroup V) {r g : ℕ} (u : Fin r → V)
    (hu : ∀ j, g • u j ∈ W) (a a' : Fin r → ℤ) (h : ∀ l, (a l : ZMod g) = a' l) :
    ∑ l, a l • u l - ∑ l, a' l • u l ∈ W := by
  rw [← Finset.sum_sub_distrib]
  refine W.sum_mem fun l _ => ?_
  have h1 : ((a l - a' l : ℤ) : ZMod g) = 0 := by push_cast; rw [h l, sub_self]
  obtain ⟨t, ht⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).1 h1
  rw [← sub_smul, ht, mul_comm, mul_zsmul, natCast_zsmul]
  exact W.zsmul_mem (hu l) t

theorem cong_nsmul {V : Type*} [AddCommGroup V] (W : AddSubgroup V) {r g : ℕ} (u : Fin r → V)
    (hu : ∀ j, g • u j ∈ W) (a a' : Fin r → ℕ) (h : ∀ l, (a l : ZMod g) = a' l) :
    ∑ l, a l • u l - ∑ l, a' l • u l ∈ W := by
  have := cong_zsmul W u hu (fun l => (a l : ℤ)) (fun l => (a' l : ℤ)) (fun l => by push_cast; exact h l)
  simpa only [natCast_zsmul] using this

theorem sum_nsmul_sum {V : Type*} [AddCommGroup V] {r : ℕ} (u : Fin r → V) (a : Fin r → ℕ)
    (b : Fin r → Fin r → ℕ) :
    ∑ j, a j • ∑ l, b l j • u l = ∑ l, (∑ j, a j * b l j) • u l := by
  simp only [Finset.smul_sum, smul_smul, Finset.sum_smul]
  exact Finset.sum_comm

theorem rebase_rel {V : Type*} [AddCommGroup V] (W : AddSubgroup V) {r g : ℕ} [NeZero g] (F : V →+ V) (u : Fin r → V)
    (hu : ∀ j, g • u j ∈ W) (M c d : Matrix (Fin r) (Fin r) (ZMod g)) (hcd : c * d = 1)
    (h : ∀ i, F (u i) - ∑ j, (M j i).val • u j ∈ W) (i : Fin r) :
    F (∑ j, (c j i).val • u j) - ∑ m, ((d * M * c) m i).val • ∑ l, (c l m).val • u l ∈ W := by
  rw [map_sum]
  simp only [map_nsmul]
  have e1 : ∑ j, (c j i).val • F (u j) = ∑ j, (c j i).val • (F (u j) - ∑ l, (M l j).val • u l) +
      ∑ j, (c j i).val • ∑ l, (M l j).val • u l := by
    rw [← Finset.sum_add_distrib]; congr 1; funext j; rw [← smul_add, sub_add_cancel]
  rw [e1, sum_nsmul_sum, sum_nsmul_sum, add_sub_assoc]
  refine W.add_mem (W.sum_mem fun j _ => W.nsmul_mem (h j) _) (cong_nsmul W u hu _ _ fun l => ?_)
  have e2 : c * (d * M * c) = M * c := by rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hcd, Matrix.one_mul]
  have e3 := congrFun (congrFun e2 l) i
  rw [Matrix.mul_apply, Matrix.mul_apply] at e3
  simp only [Nat.cast_sum, Nat.cast_mul, ZMod.natCast_zmod_val]
  rw [show ∑ x, c x i * M l x = ∑ j, M l j * c j i from Finset.sum_congr rfl fun _ _ => mul_comm _ _, ← e3]
  exact Finset.sum_congr rfl fun _ _ => mul_comm _ _

theorem rebase_span {V : Type*} [AddCommGroup V] (W : AddSubgroup V) {r g : ℕ} [NeZero g] (u : Fin r → V)
    (hu : ∀ j, g • u j ∈ W) (c d : Matrix (Fin r) (Fin r) (ZMod g)) (hcd : c * d = 1) (a : Fin r → ℤ) :
    ∃ e : Fin r → ℤ, ∑ j, a j • u j - ∑ m, e m • ∑ j, (c j m).val • u j ∈ W := by
  refine ⟨fun m => ∑ l, ((d m l).val : ℤ) * a l, ?_⟩
  have e1 : ∑ m, (∑ l, ((d m l).val : ℤ) * a l) • ∑ j, (c j m).val • u j =
      ∑ j, (∑ m, (∑ l, ((d m l).val : ℤ) * a l) * ((c j m).val : ℤ)) • u j := by
    simp only [Finset.smul_sum, ← natCast_zsmul, smul_smul, Finset.sum_smul]
    exact Finset.sum_comm
  rw [e1]
  refine cong_zsmul W u hu _ _ fun j => ?_
  have e2 := congrFun (congrFun hcd j) j
  push_cast
  simp only [ZMod.natCast_val, ZMod.cast_id', id]
  have e3 : ∑ m, (∑ l, d m l * (a l : ZMod g)) * c j m = ∑ l, (c * d) j l * (a l : ZMod g) := by
    simp only [Matrix.mul_apply, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
  rw [e3, hcd]
  simp [Matrix.one_apply]

variable {D : D7}

theorem incl_sum_nsmul (X : HidaSetting D) {r : ℕ} (a : Fin r → ℕ) (x : Fin r → Fin X.B.I.n → X.B.I.E) :
    incl X.B.I (∑ j, a j • x j) = ∑ j, a j • incl X.B.I (x j) := by
  funext t
  simp [incl, map_sum, map_nsmul, Finset.sum_apply]

theorem incl_nsmul (X : HidaSetting D) (a : ℕ) (x : Fin X.B.I.n → X.B.I.E) :
    incl X.B.I (a • x) = a • incl X.B.I x := by
  funext t
  simp [incl, map_nsmul]

theorem nsmul_mem_wLat (X : HidaSetting D) (w : HeightOneSpectrum (𝓞 D.host.E)) (g : ℕ)
    (hg : ((g : ℕ) : 𝓞 D.host.E) ∈ w.asIdeal) {y : Fin X.B.I.n → X.B.I.E} (hy : y ∈ X.B.I.L) :
    g • y ∈ wLat X w := by
  apply Submodule.subset_span
  refine ⟨(g : 𝓞 X.B.I.E), ⟨(g : 𝓞 D.host.E), hg, by simp⟩, y, hy, by ext t; simp⟩

theorem incl_mem_wLf (X : HidaSetting D) (w : HeightOneSpectrum (𝓞 D.host.E)) {y : Fin X.B.I.n → X.B.I.E}
    (hy : y ∈ wLat X w) : incl X.B.I y ∈ wLf X w :=
  Submodule.subset_span ⟨⟨y, hy⟩, rfl⟩

theorem fixRed_conj : ∀ (D : D7) (X : HidaSetting D) (red : X.B.I.Gf → G0g D.nd) (b : (Σ k : Fin 2, D.nd.PlG k) → Fin D.R.r → Fin X.B.I.n → X.B.I.E) (c : G0g D.nd), (∀ kv : (Σ k : Fin 2, D.nd.PlG k), ((D.host.g kv.1 : ℕ) : 𝓞 D.host.E) ∈ (D.naut.plGw kv.1 kv.2).asIdeal) → FixRed X red b → ∃ b' : (Σ k : Fin 2, D.nd.PlG k) → Fin D.R.r → Fin X.B.I.n → X.B.I.E, FixRed X (fun k => c⁻¹ * red k * c) b' := by
  intro D X red b c hg hf
  classical
  refine ⟨fun kv i => ∑ j, (((c kv : GL (Fin D.R.r) (ZMod (D.host.g kv.1))) :
    Matrix (Fin D.R.r) (Fin D.R.r) (ZMod (D.host.g kv.1))) j i).val • b kv j, fun kv => ?_⟩
  haveI : NeZero (D.host.g kv.1) := ⟨(D.host.g_prime kv.1).ne_zero⟩
  obtain ⟨⟨hbL, hbspan⟩, hrel⟩ := hf kv
  have hcd : ((c kv : GL (Fin D.R.r) (ZMod (D.host.g kv.1))) : Matrix (Fin D.R.r) (Fin D.R.r) (ZMod (D.host.g kv.1))) *
      (((c kv)⁻¹ : GL (Fin D.R.r) (ZMod (D.host.g kv.1))) : Matrix (Fin D.R.r) (Fin D.R.r) (ZMod (D.host.g kv.1))) = 1 :=
    Units.mul_inv (c kv)
  have hgL : ∀ j, D.host.g kv.1 • b kv j ∈ (wLat X (D.naut.plGw kv.1 kv.2)).toAddSubgroup :=
    fun j => nsmul_mem_wLat X _ _ (hg kv) (hbL j)
  refine ⟨⟨fun i => ?_, fun y hy => ?_⟩, fun k hk i => ?_⟩
  · exact Submodule.sum_mem _ fun j _ => nsmul_mem (hbL j) _
  · obtain ⟨a, ha⟩ := hbspan y hy
    obtain ⟨e, he⟩ := rebase_span _ (b kv) hgL _ _ hcd a
    refine ⟨e, ?_⟩
    have h2 := Submodule.add_mem _ ha he
    simp only [Int.cast_smul_eq_zsmul] at h2 ⊢
    rwa [sub_add_sub_cancel] at h2
  · have hu : ∀ j, D.host.g kv.1 • incl X.B.I (b kv j) ∈ (wLf X (D.naut.plGw kv.1 kv.2)).toAddSubgroup := fun j => by
      rw [← incl_nsmul]; exact incl_mem_wLf X _ (hgL j)
    have hM : ∀ i, (Matrix.mulVecLin (X.B.I.fmat k)).toAddMonoidHom (incl X.B.I (b kv i)) -
        ∑ j, (((red k kv : GL (Fin D.R.r) (ZMod (D.host.g kv.1))) :
          Matrix (Fin D.R.r) (Fin D.R.r) (ZMod (D.host.g kv.1))) j i).val • incl X.B.I (b kv j) ∈
        (wLf X (D.naut.plGw kv.1 kv.2)).toAddSubgroup := fun i => by
      have := hrel k hk i
      simp only [Nat.cast_smul_eq_nsmul] at this
      exact this
    have key := rebase_rel _ _ _ hu _ _ _ hcd hM i
    simp only [LinearMap.toAddMonoidHom_coe, Matrix.mulVecLin_apply] at key
    simp only [incl_sum_nsmul, Nat.cast_smul_eq_nsmul, Pi.mul_apply, Pi.inv_apply, Units.val_mul]
    exact key

end GlobalTheory.Mem.SRe

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.KernelJoinOnV0Three
section
open Formalism.BasicNotions Formalism.L2.Indef Formalism.L2.DIV Formalism.IndefR.Cx Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.IndefR.Lev Formalism.L2.Theta NumberField MeasureTheory GlobalTheory.Mem.SJ Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.ColDict
open scoped InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.SJ.KernelJoin

theorem heq_of_reindex {K W Mem : Type} [Field K] (a : Mem → ℕ) {V : W → Type} [∀ u, AddCommGroup (V u)]
    [∀ u, Module K (V u)] {Z : Mem → Type} {Y : W → Type} (b : ∀ x, Fin (a x) → Z x) (g : ∀ u, V u → Y u)
    (w w' : W → Mem) (ν : ∀ u, (Fin (a (w u)) → K) ≃ₗ[K] V u) (ν' : ∀ u, (Fin (a (w' u)) → K) ≃ₗ[K] V u)
    (hw : w = w') (hν : HEq ν ν') (h : ∀ u i, HEq (b (w' u) i) (g u (ν' u (Pi.single i 1)))) :
    ∀ u i, HEq (b (w u) i) (g u (ν u (Pi.single i 1))) := by
  subst hw
  cases hν
  exact h

theorem smul_apply_eq_of_eq {A B : Type} [AddCommGroup B] [Module ℂ B] (f : A → B) {a a' : A} (h : a = a')
    (k κ : ℂ) {b : B} (hb : f a' = κ • b) : k • f a = (k * κ) • b := by
  rw [h, hb, mul_smul]

theorem kernelJoin_onV0 : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (n : ℕ), A3.fam3.Ok3 n → A3.fam3.TypesSep3 → R.WeakCharacterisation F → PrimRows3 R F → SchurAll D → (D.sp.Y 0).SigOK → ∀ (S0 : IndefData (A3.side3 F.P0 F.ψ0 (R.toCx3 F).zs)) (p0 : BaseLevelRowSide D) (C : ColData (F.Dc (R.toCx3 F).zs) (F.Sp (R.toCx3 F).zs) ((R.toCx3 F).data F.cr true)) (NuC : ∀ u, Submodule (RingOfIntegers D.what₂.LL) (Fin ((F.Dc (R.toCx3 F).zs).a u) → D.what₂.LL)) (I : DivisionCompatibilityDataThreeSided D A3 F.P0 F.ψ0 F.P1 F.ψ1 (R.toCx3 F).zs S0 ((R.toCx3 F).data F.cr true) p0 (F.Dc (R.toCx3 F).zs)), DivDef3 D A3 F.P0 F.ψ0 F.P1 F.ψ1 (R.toCx3 F).zs S0 ((R.toCx3 F).data F.cr true) p0 C NuC I → DivRows3 D A3 F.P0 F.ψ0 F.P1 F.ψ1 (R.toCx3 F).zs S0 ((R.toCx3 F).data F.cr true) p0 C NuC I → (∀ (u : D.what₂.Word) (x : Fin ((F.Dc (R.toCx3 F).zs).a (I.wU u)) → D.what₂.LL) (y : Fin ((A3.side3 F.P1 F.ψ1 (R.toCx3 F).zs).nV A3.A.μ0) → D.what₂.LL), D.what₂.embLL ((F.Dc (R.toCx3 F).zs).Pt (I.wU u) A3.A.μ0 x y) = D.what₂.perCol u (I.tup A3.A.μ0) (D.jN u (I.eNu u x)) (I.jA A3.A.μ0 ((rV0 D A3.A F.P1 F.ψ1 A3.A.μ0).mulVec y))) → ∃ (Rd : Read D (R.toCx3 F) F.fc (twAt D.what₂.embLL A3.A.v0)) (M : Seam Rd F.cr), HEq Rd.wU I.wU ∧ M.ChainTie ∧ M.GoodPartHasComplexCoordinates ∧ M.RowTie (F.eV (R.toCx3 F).zs) ∧ M.ColNorm ∧ (D.what₂.V0 D.what₂.mu0).map (D.what₂.iota D.what₂.mu0) = ⊤ ∧ ∀ (St : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : St.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (Gd : GoodOp St) (hK : St.LevelSubgroupCharacter) (pw : ∀ u, PerW St hK u) (wdD : (F.Dc (R.toCx3 F).zs).Mem → D.what₂.Word) (bR : ∀ x, Fin ((F.Dc (R.toCx3 F).zs).a x) → (D.mem (wdD x)).A.Mram), (∀ u, wdD (I.wU u) = u) → F.Sp (R.toCx3 F).zs = spOf (twAt D.what₂.embLL A3.A.v0) (F.Dc (R.toCx3 F).zs) hK Gd wdD (fun x => pw (wdD x)) bR → (∀ u i, HEq (bR (I.wU u) i) (D.eMu u (D.jN u (I.eNu u (Pi.single i 1))))) → ∀ (t : GA D (D.sp.Y 0)) (c : ℝ), EvalTieT (R.MY 0) R.ν0 R.fd0 (R.toRealDat.EEat (R.toRealDat.levR F.lv2 true)) St Gd (Formalism.L2.SG.RowsJoinPinned.iotaX St h).toMulEquiv t c → ∀ (sEE : (R.toCx3 F).EE →ₗ⋆[ℂ] (F.fc (R.toCx3 F).zs).Sp.HH) (sEEc : Tw (twAt D.what₂.embLL A3.A.v0) R.HE.H →ₗ⋆[ℂ] Tw (twAt D.what₂.embLL A3.A.v0) (HHX St)) (κS : ℂ), HEq sEE sEEc → κS ≠ 0 → (∀ (x : Tw (twAt D.what₂.embLL A3.A.v0) R.HE.H) (hx : R.HE.e (Tw.out x) ∈ (R.toRealDat.EEat (R.toRealDat.levR F.lv2 true))), sEEc x = Tw.mk (twAt D.what₂.embLL A3.A.v0) (κS • sEEofTT (R.MY 0) R.ν0 R.fd0 (R.toRealDat.EEat (R.toRealDat.levR F.lv2 true)) St Gd (Formalism.L2.SG.RowsJoinPinned.iotaX St h).toMulEquiv t c ⟨R.HE.e (Tw.out x), hx⟩)) → ∀ (eE : D.what₂.EE →ₗ[ℂ] R.HE.H), (∀ y, eE (D.jEE (I.eRR y)) = Tw.out (s := twAt D.what₂.embLL A3.A.v0) (E := R.HE.H) ((R.toCx3 F).iC F.cr true A3.A.μ0 (cpt A3.A.v0.embedding y))) → ∀ (j : D.what₂.EE ≃ₗᵢ[ℂ] EEC St Gd) (v₀ : (R.MY 0).Vec) (a : ℂ), (∀ x, ((j x : EEC St Gd) : L2X St) =ᵐ[muX St] fun g => a * ev (R.MY 0) v₀ (R.HE.e (eE x)) ((Formalism.L2.SG.RowsJoinPinned.iotaX St h).symm g * t)) → ∀ u, ∃ κ : ℂ, κ ≠ 0 ∧ ∀ (x : D.what₂.EE) (φ : D.what₂.Mu u) (T' : Cu St u hK), colDictL St (pw u).Tr hK T' = ((D.eMu u φ : (D.mem u).A.Mram) : (D.mem u).C.cls 0 → (D.mem u).C.Y 0 → ℂ) → ⟪sEE (M.eR x), (F.fc (R.toCx3 F).zs).Sp.Pu (Rd.wU u) (cjv (twAt D.what₂.embLL A3.A.v0) (M.cφ u φ))⟫_ℂ = cj (twAt D.what₂.embLL A3.A.v0) (κ * ⟪((conjHH St Gd (j x) : HHX St) : L2X St), PuFun St u hK (pw u).Dt T'⟫_ℂ) := by
  intro D G _ _ Pl0 I0 T A3 Ks _ _ _ R F n hOk hSep hCW hPR hSchur hSig S0 p0 C NuC I hDef hRows hPer
  obtain ⟨Rd, hwU, heNu, heRR, hjV, hV0, hIota, hNu, hRR, hDc⟩ :=
    exists_read_of_divDef3 D G Pl0 I0 T A3 Ks R F n hOk S0 p0 _ C NuC I hDef
  obtain ⟨M⟩ := seam_nonempty D _ _ _ _ _ Rd F.cr
  have hCx := cxFacts_of_prims D G Pl0 I0 T A3 Ks R F n hOk hSep hCW hPR
  have hRow := rows_eq_rows_level D _ _ _ _ _ Rd F.cr M _ hCx (hRR hRows)
  have hCV := chainTie_and_v0Onto D _ _ _ _ _ Rd F.cr M
  refine ⟨Rd, M, hwU, hCV.1 (hDc hPer), hCV.2 hV0,
    ⟨hRow.1, hRow.2.1, ⟨_, Real.sqrt_pos.2 (hCx.pos.2.2 true), hRow.2.2⟩, 1, one_ne_zero, fun y => by
      rw [one_smul]; exact RowB.theta_eq D _ _ _ _ _ Rd F.cr M _ hCx hIota y⟩,
    colNorm_of_nuTie D _ _ _ _ _ Rd F.cr M hNu, thetaMap_referenceTuple_goodPart_onto_rows D _ _ _ _ _ Rd F.cr _ hCx hIota hV0, ?_⟩
  intro St h Gd hK pw wdD bR hwd hSp hbR t c hEv sEE sEEc κS hS hκS hsEEc eE heE j v₀ a hj u
  have hwUe : Rd.wU = I.wU := eq_of_heq hwU
  have heRRe : Rd.eRR = I.eRR := eq_of_heq heRR
  have hME : ∀ x, M.eR x = Tw.mkL (twAt D.what₂.embLL A3.A.v0) R.HE.H (eE x) := by
    have hsp : Submodule.span ℂ (Set.range fun i => D.jEE (D.div.RR.b i)) = ⊤ := D.jEE_basis.2
    have hext := LinearMap.ext_on_range hsp (f := M.eR)
      (g := (Tw.mkL (twAt D.what₂.embLL A3.A.v0) R.HE.H).comp eE) (fun i => ?_)
    · exact fun x => LinearMap.congr_fun hext x
    · obtain ⟨y, hy⟩ := Rd.eRR.surjective (D.div.RR.b i)
      have h1 := heE y
      rw [← heRRe] at h1
      rw [← hy, M.eR_eq y]
      exact (congrArg (Tw.mkL (twAt D.what₂.embLL A3.A.v0) R.HE.H) h1).symm
  have hmem : ∀ x, R.HE.e (eE x) ∈ R.toRealDat.EEat (R.toRealDat.levR F.lv2 true) := fun x => by
    have h1 := hRow.1 x
    rw [hME x] at h1
    exact h1
  let e : D.what₂.EE →ₗ[ℂ] R.toRealDat.EEat (R.toRealDat.levR F.lv2 true) :=
    LinearMap.codRestrict _ (R.HE.e ∘ₗ eE) hmem
  have hSch := SchurMove.schur_iotaX D _ (R.MY 0) (R.toRealDat.EEat (R.toRealDat.levR F.lv2 true)) St h R.θ _ _ t
    hSchur hSig hCW.base.models.inf (goodPart_le _ _ _ _ _)
  obtain ⟨κ₀, hκ₀, hκe⟩ := sEEofTT_eq_smul_conjHH D _ (R.MY 0) _ St Gd R.ν0 R.fd0
    (Formalism.L2.SG.RowsJoinPinned.iotaX St h).toMulEquiv t c hSch hEv e j v₀ a hj
  have h3 : ∀ z : HHX St, (Tw.mk (twAt D.what₂.embLL A3.A.v0) z).out = z := fun z => rfl
  have hkey : ∀ x, (sEEc (M.eR x)).out = (κS * κ₀) • conjHH St Gd (j x) := fun x => by
    have hx : R.HE.e (Tw.out (M.eR x)) ∈ R.toRealDat.EEat (R.toRealDat.levR F.lv2 true) :=
      (congrArg (fun z => R.HE.e (Tw.out z) ∈ R.toRealDat.EEat (R.toRealDat.levR F.lv2 true)) (hME x)).mpr (hmem x)
    have h2 : (⟨R.HE.e (Tw.out (M.eR x)), hx⟩ : R.toRealDat.EEat (R.toRealDat.levR F.lv2 true)) = e x :=
      Subtype.ext (congrArg (fun z => R.HE.e (Tw.out z)) (hME x))
    exact (congrArg Tw.out (hsEEc (M.eR x) hx)).trans (smul_apply_eq_of_eq _ h2 κS κ₀ (hκe x))
  have hwd' : ∀ u, wdD (Rd.wU u) = u := fun u => (congrArg wdD (congrFun hwUe u)).trans (hwd u)
  have hbR' := heq_of_reindex _ bR (fun u v => D.eMu u (D.jN u v)) Rd.wU I.wU Rd.eNu I.eNu hwUe heNu hbR
  exact GlobalTheory.T.good_operator_spectrum D _ _ _ _ _ Rd F.cr M St Gd hK pw wdD bR hwd' hSp hbR' sEE sEEc hS j (κS * κ₀)
    (mul_ne_zero hκS hκ₀) hkey u

end GlobalTheory.Mem.SJ.KernelJoin
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LiftedHeckeOperatorsAtGeneratorsCommute
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial
open Formalism.L2.Fam.NPC Formalism.L2.Fam.NPC.BaseC GlobalTheory.HeckeLocN

noncomputable section

namespace GlobalTheory.HeckeLocCommute

set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 400000

theorem hLC_commute : ∀ (D : D7) (M : MtFam D) (C : NChoice D) (hR : HeckeLift0 (mt0 M) C.Q), HeckeStdPlain → GenHyp M C.Q → (∀ v : PlE D.host, IsSplitPl D.host v → ∃ (s : SplitPlace D.host.E) (ϖ : s.v.adicCompletion (maximalRealSubfield D.host.E)), IsConjPl D.host v s.w ∧ IsUnif D.host.E s.v ϖ) → (∀ j w v k v' k', Commute (hLC (mt0 M) C.Q hR j w v k) (hLC (mt0 M) C.Q hR j w v' k')) := by
  classical
  intro D M C hR hstd hgen hsplit j w v k v' k'
  by_cases h : (1 ≤ j ∧ j ≤ D.R.m) ∧ GenAt0 D.host (D.what₂.places.resChar w) (C.Q w) v k
  swap
  · have : hLC (mt0 M) C.Q hR j w v k = 0 := by unfold hLC; rw [dif_neg h]
    rw [this]; exact Commute.zero_left _
  by_cases h' : (1 ≤ j ∧ j ≤ D.R.m) ∧ GenAt0 D.host (D.what₂.places.resChar w) (C.Q w) v' k'
  swap
  · have : hLC (mt0 M) C.Q hR j w v' k' = 0 := by unfold hLC; rw [dif_neg h']
    rw [this]; exact Commute.zero_right _
  obtain ⟨⟨h1, h2⟩, hg⟩ := h
  obtain ⟨-, hg'⟩ := h'
  obtain ⟨B, hB, hBv⟩ := hgen w j h1 h2
  obtain ⟨s, ϖ, hc, hu⟩ := hsplit v hg.1
  obtain ⟨s', ϖ', hc', hu'⟩ := hsplit v' hg'.1
  have hsB : s.v ∉ B := hBv v k s hg hc
  have hsB' : s'.v ∉ B := hBv v' k' s' hg' hc'
  have hstd' := hstd D.host.E D.R.nV (M (D.what₂.muTw w) j h1 h2).wt (M (D.what₂.muTw w) j h1 h2).J
    (M (D.what₂.muTw w) j h1 h2).χ B (M (D.what₂.muTw w) j h1 h2).J_open hB s ϖ k hsB hu hg.2.2.2.2.1 hg.2.2.2.2.2
  have hcomm := hstd'.2.2.1 s' ϖ' k' hsB' hu' hg'.2.2.2.2.1 hg'.2.2.2.2.2
  rw [commute_iff_eq]
  ext x
  apply Formalism.L2.Fam.NPC.LatticeFinitenessFree.jMt_injective
  apply (M (D.what₂.muTw w) j h1 h2).real_inj
  have hf : (M (D.what₂.muTw w) j h1 h2).real (D.what₂.jMt (D.what₂.muTw w) j x) ∈
      NG.TypeSp (M (D.what₂.muTw w) j h1 h2).wt.ρ (M (D.what₂.muTw w) j h1 h2).J (M (D.what₂.muTw w) j h1 h2).χ := by
    rw [← (M (D.what₂.muTw w) j h1 h2).real_range]; exact LinearMap.mem_range_self _ _
  have e1 := hLC_spec (mt0 M) C.Q hR j w v k h1 h2 hg s ϖ hc hu
  have e2 := hLC_spec (mt0 M) C.Q hR j w v' k' h1 h2 hg' s' ϖ' hc' hu'
  simp only [Module.End.mul_apply]
  change (mt0 M (D.what₂.muTw w) j h1 h2).real _ = (mt0 M (D.what₂.muTw w) j h1 h2).real _
  rw [e1, e2, e2, e1]
  exact hcomm _ hf

end GlobalTheory.HeckeLocCommute
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocalBridgesAtPlacesOverResidueCharOfLargeCoeff
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial
open Formalism.L2.Fam.NPC Formalism.L2.Fam.NPC.BaseC GlobalTheory.HeckeLocN

namespace GlobalTheory.HeckeLocN.BridgeAll

set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 400000

theorem exists_finExt_ge {l : ℕ} [Fact l.Prime] {ι : Type} (S : Set ι) (hS : S.Finite) (L : ι → Loc.FinExt l) :
    ∃ F : Loc.FinExt l, ∀ i ∈ S, (L i).1 ≤ F.1 := by
  induction S, hS using Set.Finite.induction_on with
  | empty => exact ⟨⟨⊥, inferInstance⟩, fun i hi => absurd hi (Set.notMem_empty i)⟩
  | @insert a s _ _ ih =>
    obtain ⟨F, hF⟩ := ih
    have h1 := F.2
    have h2 := (L a).2
    refine ⟨⟨(L a).1 ⊔ F.1, IntermediateField.finiteDimensional_sup _ _⟩, ?_⟩
    rintro i (rfl | hi)
    · exact le_sup_left
    · exact (hF i hi).trans le_sup_right

theorem placesOver_finite (E : Type) [Field E] [NumberField E] {l : ℕ} (hl : l.Prime) :
    (placesOver E l).Finite := by
  have h0 : Ideal.span {(l : 𝓞 E)} ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact_mod_cast hl.ne_zero
  refine (Ideal.finite_factors h0).subset fun v hv => ?_
  exact Ideal.dvd_span_singleton.2 hv

theorem exists_bridge_good {R : Ranks} (H : Host R) (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra H.E Ω]
    [IsAlgClosure H.E Ω] (u : HeightOneSpectrum (𝓞 H.E)) (A : ValuationSubring Ω) (hA : IsPlaceOver A u) :
    ∃ L0 : Loc.FinExt l, u ∈ placesOver H.E l → ∀ LL : Loc.FinExt l, L0.1 ≤ LL.1 →
      ∃ Bw : LocBridge l H.E Ω (Dec (F := H.E) A) ↥(Loc.OL LL),
        (∀ x, x ∈ A ↔ ‖Bw.j x‖ ≤ 1) ∧ Loc.GoodCoef H.condN Bw.LL ∧
        ∀ x : ↥(Loc.OL LL), ((Bw.toLL x : ↥Bw.LL.1) : Loc.Om l) = ((x : ↥LL.1) : Loc.Om l) := by
  by_cases hu : u ∈ placesOver H.E l
  · obtain ⟨j, L0, hj, hB⟩ := GlobalTheory.PlaceBridge.exists_locBridge l H.E Ω u A hu hA
    let L1 : Loc.FinExt l := UpperTheory.KStar.Cyc.rootsExt l _ (UpperTheory.KStar.Cyc.lcm_ne_zero (l := l) H.toHostRaw)
    have f0 := L0.2
    have f1 := L1.2
    refine ⟨⟨L0.1 ⊔ L1.1, IntermediateField.finiteDimensional_sup _ _⟩, fun _ LL hLL => ?_⟩
    obtain ⟨Bw, e1, e2, e3, e4⟩ := hB LL (le_sup_left.trans hLL)
    refine ⟨Bw, by rw [e1]; exact hj, ?_, e4⟩
    rw [e2]
    exact UpperTheory.KStar.Cyc.mem_of_rootsExt_le _ (le_sup_right.trans hLL)
  · exact ⟨⟨⊥, inferInstance⟩, fun h => absurd h hu⟩

theorem brAt_of_large : ∀ (D : D7) (w : D.what₂.places.Pl), ∃ F0 : Loc.FinExt (D.what₂.places.resChar w),
    ∀ (X : CoefIn D.what₂) (j : ℕ), F0.1 ≤ (X.Kx j w).1 → BrAt X j w := by
  intro D w
  choose L hL using fun u : PlE D.host =>
    exists_bridge_good D.host (D.what₂.places.resChar w) D.nd.Om u (D.nd.plOm.1 u) (D.nd.plOm.2 u)
  obtain ⟨F, hF⟩ := exists_finExt_ge _ (placesOver_finite D.host.E (D.what₂.places.resChar_prime w)) L
  refine ⟨F, fun X j hX u hu => ?_⟩
  obtain ⟨Bw, h1, h2, h3⟩ := hL u hu (X.Kx j w) ((hF u hu).trans hX)
  exact ⟨Bw, h1, h2, fun z => (iqC_alg X j w z).trans (h3 z).symm⟩

end GlobalTheory.HeckeLocN.BridgeAll
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MinpolyIrreducibleLocalEmbeddingStatement
section
open NumberField IsDedekindDomain ValuativeRel Matrix MeasureTheory TensorProduct Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.Whittaker GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocDict
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.minpoly_irreducible_local_embedding : ∀ (K L Ω : Type) [Field Ω] [Field K] [NumberField K] [Algebra K Ω] [IsAlgClosure K Ω] [Field L] [NumberField L] [Algebra L Ω] [Algebra K L] [IsScalarTower K L Ω] (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 K)), IsPlaceOver A v → (∀ σ : G K Ω, ∃ τ ∈ Dec (F := K) A, ∀ x : L, τ (algebraMap L Ω x) = σ (algebraMap L Ω x)) → ∀ ι : Ω →ₐ[K] Kbar v, IsLocEmb A v ι → ∀ α : L, Irreducible ((minpoly K α).map (algebraMap K (v.adicCompletion K))) := by
  first | exact @GlobalTheory.LocIrred.minpoly_map_adicCompletion_irreducible | exact GlobalTheory.LocIrred.minpoly_map_adicCompletion_irreducible | (intros; apply GlobalTheory.LocIrred.minpoly_map_adicCompletion_irreducible <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.OmFrameExistsWithJE
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial

noncomputable section

namespace GlobalTheory.HeightCounting

theorem omFrame_exists_with_jE (D : D7) (jE : D.host.E →+* Qb) : ∃ fr : OmFrame D, fr.jE = jE := by
  letI : Algebra D.host.E Qb := jE.toAlgebra
  haveI : Algebra.IsAlgebraic ℚ Qb := inferInstance
  haveI : IsScalarTower ℚ D.host.E Qb := .of_algebraMap_eq fun x => (map_ratCast jE x).symm
  haveI : Algebra.IsAlgebraic D.host.E Qb := .tower_top (K := ℚ) D.host.E
  haveI : IsAlgClosure D.host.E Qb := ⟨inferInstance, inferInstance⟩
  let e : D.nd.Om ≃ₐ[D.host.E] Qb := IsAlgClosure.equiv D.host.E D.nd.Om Qb
  exact ⟨⟨jE, e.toRingEquiv, fun x => e.commutes x⟩, rfl⟩

end GlobalTheory.HeightCounting
end
end

