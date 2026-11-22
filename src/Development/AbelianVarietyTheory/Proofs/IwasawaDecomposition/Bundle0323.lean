import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.T2SpaceAdelicGeneralLinearGroupNumberField
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0222
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsMulRightInvariantOfFundamentalDomain
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.DefClassNum
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.IdeleClassFiniteness.Bundle0001
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.IdeleClassFiniteness.LatticeIdealNonzero
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0307
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0298
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0302
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RowsRestWordColumnUnitBaseTupleAlt
import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousKapSymm
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0303
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsLocallyConstantModulus
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0283
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0001
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0007
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLevelJCharacterEqMemberOffPlaces
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChartWiden
import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
import ReciprocityTheory.DualLattices.Bundle0018
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0030
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsSplittingCharacterSelf
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0016
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0201
import Development.AbelianVarietyTheory.Proofs.HeightProofs.EqOrConjOfPlaceOf
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0304
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ContinuousMapPFin
import Formalism.LocalToGlobal.BesselHermitianTheta.AllTied
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.AdelicDataRowMeasureScaleTrivialTuple
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsGrpDataMapHaar
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0252
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0220
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0305

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFiniteMeasureReductionDomainInfinity
section
open NumberField IsDedekindDomain Matrix MeasureTheory Topology
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.UnitaryBC GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL

noncomputable section

namespace GlobalTheory.GLInfReduction

variable {E : Type} [Field E] [NumberField E] {a : ℕ}

def entries (y : Matrix (Fin a) (Fin a) (Cinf E)) : GlobalTheory.FlagMeas.MatInf E a := fun w i k => y i k w

def dn (y : Matrix (Fin a) (Fin a) (Cinf E)) : ℝ := ∏ w, ‖(y.det) w‖ ^ 2

theorem detNorm_entries (y : Matrix (Fin a) (Fin a) (Cinf E)) :
    GlobalTheory.FlagMeas.detNorm E a (entries y) = dn y := by
  unfold GlobalTheory.FlagMeas.detNorm dn
  refine Finset.prod_congr rfl fun w _ => ?_
  have : Matrix.of (entries y w) = (Pi.evalRingHom (fun _ : InfinitePlace E => ℂ) w).mapMatrix y := by
    ext i k; rfl
  rw [this, ← RingHom.map_det]; rfl

theorem entries_mul (g y : Matrix (Fin a) (Fin a) (Cinf E)) : entries (g * y) = entries g * entries y := by
  funext w i k
  change (g * y) i k w = (Matrix.of (entries g w) * Matrix.of (entries y w)) i k
  simp [Matrix.mul_apply, Finset.sum_apply, entries]

theorem dn_mul (g y : Matrix (Fin a) (Fin a) (Cinf E)) : dn (g * y) = dn g * dn y := by
  simp [dn, Matrix.det_mul, mul_pow, Finset.prod_mul_distrib]

theorem dn_pos (y : GL (Fin a) (Cinf E)) : 0 < dn (y : Matrix (Fin a) (Fin a) (Cinf E)) := by
  refine Finset.prod_pos fun w _ => ?_
  have h : (y : Matrix (Fin a) (Fin a) (Cinf E)).det * ((y⁻¹ : GL (Fin a) (Cinf E)) : Matrix (Fin a) (Fin a) (Cinf E)).det = 1 := by
    rw [← Matrix.det_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.det_one]
  have h' := congrFun h w
  have hne : (y : Matrix (Fin a) (Fin a) (Cinf E)).det w ≠ 0 := left_ne_zero_of_mul_eq_one h'
  positivity

end GlobalTheory.GLInfReduction

open GlobalTheory.GLInfReduction in

theorem GlobalTheory.GLInfReduction.exists_cover_of_finite_measure (E : Type) [Field E] [NumberField E] [IsTotallyComplex E]
    (a : ℕ) (Λ : Submodule (𝓞 E) (Fin a → E)) (hΛ : Submodule.IsLattice E Λ)
    [MeasurableSpace (GL (Fin a) (Cinf E))] [BorelSpace (GL (Fin a) (Cinf E))]
    (ν : Measure (GL (Fin a) (Cinf E))) [ν.IsHaarMeasure] :
    ∃ Ω : Set (GL (Fin a) (Cinf E)), ν Ω < ⊤ ∧ ∀ y, ∃ γ : GL (Fin a) E,
      (∀ x, (γ : Matrix (Fin a) (Fin a) E) *ᵥ x ∈ Λ ↔ x ∈ Λ) ∧
      ∃ n : ℤ, GeneralLinearGroup.map (pInf E) (ratGL E a γ * splitCentre E a 1 ^ n) * y ∈ Ω := by
  rcases Nat.eq_zero_or_pos a with rfl | ha
  · refine ⟨Set.univ, ?_, fun y => ⟨1, by simp, 0, trivial⟩⟩
    haveI : Subsingleton (GL (Fin 0) (Cinf E)) := ⟨fun x y => Units.ext (Subsingleton.elim _ _)⟩
    haveI : Finite (GL (Fin 0) (Cinf E)) := Finite.of_subsingleton
    exact isCompact_univ.measure_lt_top
  set r := Fintype.card (InfinitePlace E) with hr_def
  have hr : 0 < r := Fintype.card_pos
  set N : ℕ := 2 * a * r with hN_def
  have hN : 0 < N := by positivity
  have hNR : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'

  have hslab := GlobalTheory.T.covolume_unitDetNormSlab_latticeAut_lt_top E inferInstance a ha Λ hΛ
  simp only [GlobalTheory.FlagMeas.covol, iInf_lt_iff] at hslab
  obtain ⟨D, hDm, hcov, hDlt⟩ := hslab
  have hD' := GlobalTheory.T.haar_infiniteGL_lt_top_of_infiniteGLHaarMeasure_lt_top E a ν D hDm hDlt
  set S : Set (GL (Fin a) (Cinf E)) := {y | entries (y : Matrix (Fin a) (Fin a) (Cinf E)) ∈ D} with hS
  have hS' : ν S < ⊤ := hD'

  let c : ℝ → GL (Fin a) (Cinf E) := fun t => GeneralLinearGroup.map (pInf E) (splitCentre E a t)
  have hc_val : ∀ t : ℝ, (c t : Matrix (Fin a) (Fin a) (Cinf E)) =
      Matrix.scalar (Fin a) (fun _ : InfinitePlace E => Complex.exp (t : ℂ)) := by
    intro t
    simp only [c, splitCentre, pInf_infGL]
    rfl
  have hc_dn : ∀ t : ℝ, dn (c t : Matrix (Fin a) (Fin a) (Cinf E)) = Real.exp (N * t) := by
    intro t
    rw [hc_val, dn]
    simp only [Matrix.scalar_apply, Matrix.det_diagonal, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
      Pi.pow_apply, norm_pow, Complex.norm_exp_ofReal]
    rw [← hr_def, ← Real.exp_nat_mul, ← Real.exp_nat_mul, ← Real.exp_nat_mul, hN_def]
    congr 1; push_cast; ring
  have hcomm : ∀ t g, c t * g = g * c t := by
    intro t g
    have := congrArg (GeneralLinearGroup.map (pInf E)) (splitCentre_comm (E := E) (a := a) t (infGL E a g))
    simpa [map_mul] using this
  have hcint : ∀ n : ℤ, GeneralLinearGroup.map (pInf E) (splitCentre E a 1 ^ n) = c n := by
    intro n; simp only [c, splitCentre_intCast]
  refine ⟨⋃ k ∈ Finset.range N, (fun h => c (-(k : ℝ) / N) * h) ⁻¹' S, ?_, ?_⟩
  · refine lt_of_le_of_lt (measure_biUnion_finset_le _ _) ?_
    refine ENNReal.sum_lt_top.2 fun k _ => ?_
    rw [measure_preimage_mul]
    exact hS'
  · intro y
    set L := Real.log (dn (y : Matrix (Fin a) (Fin a) (Cinf E)))
    have hL : Real.exp L = dn (y : Matrix (Fin a) (Fin a) (Cinf E)) := Real.exp_log (dn_pos y)
    set m := ⌊L⌋
    set q := m / (N : ℤ)
    set ρ := m % (N : ℤ)
    have hρ0 : 0 ≤ ρ := Int.emod_nonneg _ (by exact_mod_cast hN.ne')
    have hρN : ρ < N := Int.emod_lt_of_pos _ (by exact_mod_cast hN)
    have hm : ρ + N * q = m := by simp only [ρ, q]; rw [Int.emod_def]; ring
    set k := ρ.toNat
    have hk : (k : ℤ) = ρ := Int.toNat_of_nonneg hρ0
    have hkN : k < N := by omega
    set x := c (-(k : ℝ) / N) * (c ((-q : ℤ) : ℝ) * y)
    have hx : dn (x : Matrix (Fin a) (Fin a) (Cinf E)) = Real.exp (L - m) := by
      simp only [x, Units.val_mul, dn_mul, hc_dn, ← hL, ← Real.exp_add]
      congr 1
      have hmR : (ρ : ℝ) + N * q = m := by exact_mod_cast hm
      have hkR : (k : ℝ) = ρ := by exact_mod_cast hk
      rw [← hmR, hkR]; push_cast; field_simp; ring
    have hxS : 1 ≤ GlobalTheory.FlagMeas.detNorm E a (entries (x : Matrix (Fin a) (Fin a) (Cinf E))) ∧
        GlobalTheory.FlagMeas.detNorm E a (entries (x : Matrix (Fin a) (Fin a) (Cinf E))) < Real.exp 1 := by
      rw [detNorm_entries, hx]
      constructor
      · exact Real.one_le_exp (by linarith [Int.floor_le L])
      · exact Real.exp_lt_exp.2 (by linarith [Int.lt_floor_add_one L])
    obtain ⟨g, ⟨γ, hγΛ, hgγ⟩, hgD⟩ := hcov _ hxS
    refine ⟨γ, hγΛ, -q, ?_⟩
    simp only [Set.mem_iUnion, Finset.mem_range]
    refine ⟨k, hkN, ?_⟩
    set R := GeneralLinearGroup.map (pInf E) (ratGL E a γ)
    have hR : entries (R : Matrix (Fin a) (Fin a) (Cinf E)) = g := by
      funext w i j
      rw [hgγ w i j]
      exact pInf_algebraMap (γ i j) w
    have e1 : c (-(k : ℝ) / N) * (GeneralLinearGroup.map (pInf E) (ratGL E a γ * splitCentre E a 1 ^ (-q)) * y) = R * x := by
      rw [map_mul, hcint, ← mul_assoc, ← mul_assoc, hcomm, mul_assoc, mul_assoc]
    change entries ((c (-(k : ℝ) / N) * (GeneralLinearGroup.map (pInf E) (ratGL E a γ * splitCentre E a 1 ^ (-q)) * y) :
      GL (Fin a) (Cinf E)) : Matrix (Fin a) (Fin a) (Cinf E)) ∈ D
    rw [e1, Units.val_mul, entries_mul, hR]
    exact hgD
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsGoodIntegralFormsLatticeBaseLevelStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_goodIntegralForms_lattice_base_level : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd), (∀ o : D.what₂.O, ∃ k : Ks, algebraMap Ks D.what₂.LL k = D.what₂.OtoLL o) → Inputs D → Pins R F cG → Holds R F → ∀ (i : Fin D.R.m) (M : Type) [AddCommGroup M] [Module ℂ M] [FiniteDimensional ℂ M] (E : M →ₗ[ℂ] (R.toRealDat.HW i (sg0 D A3.A)).H), Function.Injective E → LinearMap.range E = (R.toRealDat.Wat i (sg0 D A3.A) (R.toRealDat.levL F.lv2 false (sg0 D A3.A))).comap (R.toRealDat.HW i (sg0 D A3.A)).e → ∃ L : Rows.OLat D.what₂.O (D.what₂.embLL.comp D.what₂.OtoLL) M, ∀ x, x ∈ L.carrier ↔ ∃ v ∈ (R.toRealDat.FW i).MK, v ∈ (R.toRealDat.FW i).Wgood F.lv2.P0 F.lv2.ψ0⁻¹ (fun g => (idemOf A3.A.X).coeff g) ∧ E x = (R.toRealDat.FW i).j (sg0 D A3.A) v := by
  first | exact @GlobalTheory.Mem.GoodLatFree.exists_oLat_good | exact GlobalTheory.Mem.GoodLatFree.exists_oLat_good | (intros; apply GlobalTheory.Mem.GoodLatFree.exists_oLat_good <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsHaarFundamentalDomainIsometryTransportStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix Formalism.IndefR.Datum
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_haar_fundamentalDomain_isometryTransport : ∀ (D : D7) (V V' : HSp D) (I : GlobalTheory.Mem.Isom.IsoMat V V') (S : HSp D) (μ : Measure (WO S V')) (𝓕 : Set (WO S V')), μ.IsAddHaarMeasure → IsAddFundamentalDomain (ratL V' S) 𝓕 μ → ∃ (ν : Measure (WO S V)) (𝓖 : Set (WO S V)), ν.IsAddHaarMeasure ∧ IsAddFundamentalDomain (ratL V S) 𝓖 ν ∧ ∀ u : WO S V → ENNReal, ∫⁻ w in 𝓕, u ((I.phi S).symm w) ∂μ = ∫⁻ w in 𝓖, u w ∂ν := by
  first | exact @GlobalTheory.Mem.Isom.haar_fd_phi | exact GlobalTheory.Mem.Isom.haar_fd_phi | (intros; apply GlobalTheory.Mem.Isom.haar_fd_phi <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsHilbertChainOfLevelOverTopsStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_hilbertChain_of_level_over_tops : ∀ (D : D7) (C : ChainReal D) (b : Bool) (U : D.what₂.Tup → Prop) (Top : D.what₂.Tup → Hs) (jX : ∀ μ, (Top μ).T →ₗ[ℂ] C.AmbX), 2 ≤ D.R.m → PeterssonHilbertSpace.IsHermPos (C.EEc b) (C.ipE b) → (∀ μ, C.EEc b ≤ C.CC b μ 0 ∧ C.CCXP b μ ≤ C.CCX b μ ∧ PeterssonHilbertSpace.IsHermPos (C.CCX b μ) (C.ipXP b μ) ∧ ∀ j, j ≤ D.R.m - 1 → C.CCP b μ j ≤ C.CC b μ j ∧ PeterssonHilbertSpace.IsHermPos (C.CC b μ j) (C.ipP b μ j)) → (∀ μ, PeterssonHilbertSpace.IsHermPos (C.CC b μ 0) (C.ipE b)) → (∀ μ, U μ → Function.Injective (jX μ) ∧ LinearMap.range (jX μ) = C.CCXP b μ ∧ ∀ x x', ⟪x, x'⟫_ℂ = C.ipXP b μ (jX μ x) (jX μ x')) → ∃ (EE : Hs) (Mult : D.what₂.Tup → ℕ → Hs) (multZero : ∀ μ, (Mult μ 0).T ≃ₗᵢ[ℂ] EE.T) (multTop : ∀ μ, (Mult μ D.R.m).T ≃ₗᵢ[ℂ] (Top μ).T) (io : ∀ μ j, (Mult μ (j + 1)).T →ₗ[ℂ] (Mult μ j).T) (jE : EE.T →ₗ[ℂ] C.Amb 0) (jM : ∀ μ j, (Mult μ j).T →ₗ[ℂ] C.Amb j), Function.Injective jE ∧ LinearMap.range jE = C.EEc b ∧ (∀ x x', ⟪x, x'⟫_ℂ = C.ipE b (jE x) (jE x')) ∧ (∀ μ, U μ → ∀ j, 1 ≤ j → j ≤ D.R.m - 1 → Function.Injective (jM μ j) ∧ LinearMap.range (jM μ j) = C.CCP b μ j ∧ ∀ x x', ⟪x, x'⟫_ℂ = C.ipP b μ j (jM μ j x) (jM μ j x')) ∧ (∀ μ, U μ → ∀ x (v : (Mult μ 1).T) (h : jM μ 1 v ∈ C.CC b μ 1), ⟪x, multZero μ (io μ 0 v)⟫_ℂ = C.ipE b (jE x) (C.ioC b μ 0 ⟨jM μ 1 v, h⟩ : C.Amb 0)) ∧ (∀ μ, U μ → ∀ j, 1 ≤ j → j + 1 ≤ D.R.m - 1 → ∀ x (v : (Mult μ (j + 1)).T) (h : jM μ (j + 1) v ∈ C.CC b μ (j + 1)), ⟪x, io μ j v⟫_ℂ = C.ipP b μ j (jM μ j x) (C.ioC b μ j ⟨jM μ (j + 1) v, h⟩ : C.Amb j)) ∧ (∀ μ, U μ → ∀ x (v : (Mult μ D.R.m).T) (v' : (Mult μ (D.R.m - 1 + 1)).T), HEq v' v → ∀ h : jX μ (multTop μ v) ∈ C.CCX b μ, ⟪x, io μ (D.R.m - 1) v'⟫_ℂ = C.ipP b μ (D.R.m - 1) (jM μ (D.R.m - 1) x) (C.ioX b μ ⟨jX μ (multTop μ v), h⟩ : C.Amb (D.R.m - 1))) ∧ (∀ μ, ¬ U μ → ∀ j, io μ j = 0) := by
  first | exact @GlobalTheory.ChainHilb.exists_chainHilb | exact GlobalTheory.ChainHilb.exists_chainHilb | (intros; apply GlobalTheory.ChainHilb.exists_chainHilb <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIwasawaDecompositionUpperUnitriangularInteStatement
section
open NumberField IsDedekindDomain ValuativeRel Matrix MeasureTheory TensorProduct Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.Whittaker GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocDict
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_iwasawa_decomposition_upperUnitriangular_integral : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (m : ℕ) (g : GL (Fin m) k), ∃ u ∈ unipB k (Fin m), ∃ t : Fin m → kˣ, ∃ κ ∈ KO k (Fin m), g = u * diagT k (Fin m) t * κ := by
  first | exact @GlobalTheory.SmGL.exists_unipB_mul_diagT_mul_KO | exact GlobalTheory.SmGL.exists_unipB_mul_diagT_mul_KO | (intros; apply GlobalTheory.SmGL.exists_unipB_mul_diagT_mul_KO <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLevelJCharacterEqMemberOffPlacesStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_levelJ_character_eq_member_off_places : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (Ch0 : B.Word → ℕ → Type) (chOf0 : ∀ u i, ((I.rec7 l Z).mem u).C.cls i → Ch0 u i) (F : ∀ u, FormsTiedSym (I.rec7 l Z) u (Ch0 u) (chOf0 u)) (u : B.Word) (a : I.ι) (Q : Finset (HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F))) (h1 : 1 ≤ B.R.m - 1) (Ch : Type) (_ : Finite Ch) (chOf : (I.stp u a (B.R.m - 1)).Cl → Ch) (K : ∀ β : Ch, LevelChart (I.rec7 l Z) (B.T u) (badQ (I.rec7 l Z) Q) (B.R.m - 1) (Nat.sub_le _ _) (fun c : {c // chOf c = β} => (I.chain l u a).stab (B.R.m - 1) c.1) (fun c => latCrd (I.rec7 l Z) (B.R.m - 1) (Nat.sub_le _ _) (I.latAt u a (B.R.m - 1) c.1))) (g : Ch → Ch0 u (B.R.m - 1)), (∀ v, v ∈ Q ↔ I.UnderQ a v) → (∀ u, I.StdF l Z u (F u)) → (∀ u j v h, (F u).glevJ.fr j v h = 1) → I.ReadsK l Z u a (B.R.m - 1) (Nat.sub_le _ _) chOf K → (∀ β, ∀ v, v ∉ Q → (K β).lev.Uloc v = ((F u).ch (B.R.m - 1) h1 (succ_pred_m B.R) (g β)).lev.Uloc v) → (∀ β (κ : (K β).lev.U) (κ' : ((F u).ch (B.R.m - 1) h1 (succ_pred_m B.R) (g β)).lev.U), κ.1 = κ'.1 → (∀ v ∈ Q, bc (prV (E := (I.rec7 l Z).host.E) v) κ.1 = 1) → (K β).lev.chi κ = ((F u).ch (B.R.m - 1) h1 (succ_pred_m B.R) (g β)).lev.chi κ') → ∀ J : TwLevJ I l Z F Q u a chOf K, ∃ χ : J.levJ.U →* ℂˣ, (∀ β (κ : J.levJ.U) (κ' : (K β).lev.U), κ'.1 = reGL (rankN (I.rec7 l Z) (B.R.m - 1) (Nat.sub_le _ _)) _ κ.1 → (K β).lev.chi κ' = χ κ) ∧ ∀ (κ : J.levJ.U) (κ' : (F u).levJ.U), κ'.1 = reGL (rankN (I.rec7 l Z) (B.R.m - 1) (Nat.sub_le _ _)) _ κ.1 → (∀ v ∈ Q, bc (prV (E := (I.rec7 l Z).host.E) v) κ.1 = 1) → χ κ = (F u).levJ.chi κ' := by
  first | exact @GlobalTheory.Mem.Col2.TC.twLevJ_exists_chi_off | exact GlobalTheory.Mem.Col2.TC.twLevJ_exists_chi_off | (intros; apply GlobalTheory.Mem.Col2.TC.twLevJ_exists_chi_off <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLocalHoweContractionCompactUnitaryStatement
section
open Formalism.MainNotions.S Matrix GlobalTheory.CompactHowe
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_local_howe_contraction_compact_unitary : ∀ (N n : ℕ) (hn : n ≤ N) (ν : Fin N → ℕ) (x₁ x₃ : ℤ) (Λ : Fin n → ℝ) (Λ' : Fin N → ℝ) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (H' : Type) [NormedAddCommGroup H'] [InnerProductSpace ℂ H'] [FiniteDimensional ℂ H'] (σ' : Matrix (Fin N) (Fin N) ℂ → (H' →L[ℂ] H')), Antitone ν → (∀ b : Fin N, n ≤ (b : ℕ) → ν b = 0) → (∀ a, Λ a = (x₃ : ℝ) - ν (Fin.castLE hn (Fin.rev a))) → (∀ b, Λ' b = -(x₁ : ℝ) - ν (Fin.rev b)) → IsURepOn (UJset (allPos n)) σ → IsKTypeOf (allPos n) σ Λ ⊤ → IsURepOn (UJset (allPos N)) σ' → IsKTypeOf (allPos N) σ' Λ' ⊤ → ∃ I : MvPolynomial (Fin N × Fin n) ℂ →ₗ[ℂ] H' →ₗ[ℂ] H, I ≠ 0 ∧ ∀ h ∈ UJset (allPos N), ∀ g ∈ UJset (allPos n), ∀ P v, I ((h.det ^ x₁ * g.det ^ x₃) • subst2 h (g⁻¹)ᵀ P) (σ' h v) = σ g (I P v) := by
  first | exact @GlobalTheory.CompactHowe.exists_local_contraction | exact GlobalTheory.CompactHowe.exists_local_contraction | (intros; apply GlobalTheory.CompactHowe.exists_local_contraction <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsMkTauE
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th IsDedekindDomain NumberField
  Formalism.IndefR.Links Formalism.L2.JoinChr Formalism.L2.Host Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CharInfPlace

section General

variable (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem exists_inf : ∃ Θ : Ainf F ⊗[F] E →+* InfiniteAdeleRing E,
    ∀ a x, Θ (a ⊗ₜ[F] x) = GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.infiniteAdeleMap F E a * algebraMap E _ x := by
  letI : Algebra F (InfiniteAdeleRing E) :=
    ((algebraMap E (InfiniteAdeleRing E)).comp (algebraMap F E)).toAlgebra
  let f : E →ₐ[F] InfiniteAdeleRing E := ⟨algebraMap E _, fun _ => rfl⟩
  let g : Ainf F →ₐ[F] InfiniteAdeleRing E :=
    ⟨GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.infiniteAdeleMap F E,
      fun x => congrArg Prod.fst (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.adeleMap_algebraMap F E x)⟩
  exact ⟨(Algebra.TensorProduct.productMap g f).toRingHom, fun a x => rfl⟩

theorem exists_fin : ∃ Θ : Af F ⊗[F] E →+* FiniteAdeleRing (𝓞 E) E,
    ∀ a x, Θ (a ⊗ₜ[F] x) = GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.finiteAdeleMap F E a * algebraMap E _ x := by
  letI : Algebra F (FiniteAdeleRing (𝓞 E) E) :=
    ((algebraMap E (FiniteAdeleRing (𝓞 E) E)).comp (algebraMap F E)).toAlgebra
  let f : E →ₐ[F] FiniteAdeleRing (𝓞 E) E := ⟨algebraMap E _, fun _ => rfl⟩
  let g : Af F →ₐ[F] FiniteAdeleRing (𝓞 E) E :=
    ⟨GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.finiteAdeleMap F E,
      fun x => congrArg Prod.snd (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.adeleMap_algebraMap F E x)⟩
  exact ⟨(Algebra.TensorProduct.productMap g f).toRingHom, fun a x => rfl⟩

variable {F E}

theorem comp_eq [StarRing E] {Θ : Ainf F ⊗[F] E →+* InfiniteAdeleRing E}
    (hΘ : ∀ a x, Θ (a ⊗ₜ[F] x) = GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.infiniteAdeleMap F E a * algebraMap E _ x)
    {φ : E →+* ℂ} {θ : Ainf F ⊗[F] E →+* ℂ} (h : IsInfEmb φ θ) {w : InfinitePlace E}
    (hw : InfinitePlace.mk φ = w) {y y' : Ainf F ⊗[F] E} (e : θ y = θ y') : Θ y w = Θ y' w := by
  let p : Ainf F ⊗[F] E →+* ℂ := (InfinitePlace.Completion.extensionEmbedding w).comp
    ((Pi.evalRingHom (fun v : InfinitePlace E => v.Completion) w).comp Θ)
  have hp : IsInfEmb w.embedding p := by
    refine ⟨fun x => ?_, ?_⟩
    · change InfinitePlace.Completion.extensionEmbedding w (Θ (1 ⊗ₜ[F] x) w) = _
      rw [hΘ, map_one, one_mul]
      exact InfinitePlace.Completion.extensionEmbedding_coe w (WithAbs.toAbs _ x)
    · have : (fun a : Ainf F => p (a ⊗ₜ[F] (1 : E))) = fun a =>
          InfinitePlace.Completion.extensionEmbedding w (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.infiniteAdeleMap F E a w) := by
        funext a
        change InfinitePlace.Completion.extensionEmbedding w (Θ (a ⊗ₜ[F] 1) w) = _
        rw [hΘ, map_one, mul_one]
      rw [this]
      exact (InfinitePlace.Completion.isometry_extensionEmbedding w).continuous.comp
        ((LiesOver.continuous_completionMap (v := w.comap (algebraMap F E)) (w := w)).comp
          (continuous_apply _))
  refine (InfinitePlace.Completion.extensionEmbedding w).injective ?_
  change p y = p y'
  rcases InfinitePlace.mk_eq_iff.1 (hw.trans (InfinitePlace.mk_embedding w).symm) with h1 | h1
  · rw [← h1] at hp
    rwa [GlobalTheory.AutFunCompare.isInfEmb_unique φ p θ hp h]
  · have hq : IsInfEmb w.embedding ((starRingEnd ℂ).comp θ) :=
      ⟨fun x => by rw [← h1, RingHom.comp_apply, h.1]; rfl, Complex.continuous_conj.comp h.2⟩
    rw [GlobalTheory.AutFunCompare.isInfEmb_unique _ p _ hp hq, RingHom.comp_apply, RingHom.comp_apply, e]

end General

theorem conjugate_emb {R : Ranks} (H : Host R) (g : R.GG) :
    ComplexEmbedding.conjugate (H.emb g) = H.emb (g * R.cc) := by
  rw [Formalism.L2.Geo.emb_mul_cc_comp]
  refine RingHom.ext fun x => ?_
  have hcm := H.isCMField_hostE
  have h : IsCMField.complexConj H.E x = H.conj x := by
    apply H.φ₀.injective
    rw [IsCMField.complexEmbedding_complexConj, Formalism.HC.HostAx.conjE_apply]
  show starRingEnd ℂ (H.emb g x) = H.emb g (H.conj x)
  rw [← h, IsCMField.complexEmbedding_complexConj]

theorem exists_mk_tauE (D : D7) (w : InfinitePlace D.host.E) : ∃ τ, InfinitePlace.mk (tauE D τ) = w := by
  obtain ⟨g, hg⟩ := (factEmb D.R D.host).1.2 w.embedding
  have e : InfinitePlace.mk (D.host.emb g) = w := by rw [hg, InfinitePlace.mk_embedding]
  by_cases h : g ∈ D.R.Psi
  · obtain ⟨τ, hτ⟩ := (Formalism.L2.Geo.exists_tauEmb_iff D g).2 h
    exact ⟨τ, (congrArg _ hτ.symm).trans e⟩
  · obtain ⟨τ, hτ⟩ := (Formalism.L2.Geo.exists_tauEmb_iff D (g * D.R.cc)).2
      (by_contra fun h' => h ((Formalism.L2.Geo.mem_Psi_iff_mul_cc_notMem _).2 h'))
    rw [← conjugate_emb] at hτ
    exact ⟨τ, (congrArg _ hτ.symm).trans ((InfinitePlace.mk_conjugate_eq _).trans e)⟩

section Mult

variable {D : D7} {Θ : AE D →+* AdeleRing (𝓞 D.host.E) D.host.E}
  (hΘ : ∀ a x, Θ (a ⊗ₜ[D.host.F] x) =
    GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.adeleMap D.host.F D.host.E a * algebraMap D.host.E _ x)

include hΘ

theorem mult_inc (x : D.host.E) : Θ (incA D x) = algebraMap D.host.E _ x := by
  change Θ ((1 : AF D.host.F) ⊗ₜ[D.host.F] x) = _
  rw [hΘ, map_one, one_mul]

theorem mult_fst {Ψ : Ainf D.host.F ⊗[D.host.F] D.host.E →+* InfiniteAdeleRing D.host.E}
    (hΨ : ∀ a x, Ψ (a ⊗ₜ[D.host.F] x) =
      GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.infiniteAdeleMap D.host.F D.host.E a * algebraMap D.host.E _ x) (z : AE D) :
    (Θ z).1 = Ψ (infPart D z) := by
  induction z using TensorProduct.induction_on with
  | zero => rw [RingHom.map_zero, RingHom.map_zero, RingHom.map_zero]; rfl
  | add x y hx hy => rw [RingHom.map_add, RingHom.map_add, RingHom.map_add, ← hx, ← hy]; rfl
  | tmul a x => rw [hΘ]; exact (hΨ a.1 x).symm

theorem mult_snd {Ψ : Af D.host.F ⊗[D.host.F] D.host.E →+* FiniteAdeleRing (𝓞 D.host.E) D.host.E}
    (hΨ : ∀ a x, Ψ (a ⊗ₜ[D.host.F] x) =
      GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.finiteAdeleMap D.host.F D.host.E a * algebraMap D.host.E _ x) (z : AE D) :
    (Θ z).2 = Ψ (finPart D z) := by
  induction z using TensorProduct.induction_on with
  | zero => rw [RingHom.map_zero, RingHom.map_zero, RingHom.map_zero]; rfl
  | add x y hx hy => rw [RingHom.map_add, RingHom.map_add, RingHom.map_add, ← hx, ← hy]; rfl
  | tmul a x => rw [hΘ]; exact (hΨ a.2 x).symm

set_option maxHeartbeats 800000 in

theorem mult_locE (P : HeightOneSpectrum (𝓞 D.host.E)) (e : AE D) (he : IsPlIdem D e P) (k : D.host.Eˣ) :
    Θ (locE D e (k : D.host.E)) =
      ((localIdele D.host.E P (atFin P k) : Ideles D.host.E) : AdeleRing (𝓞 D.host.E) D.host.E) := by
  obtain ⟨Φ, hΦ⟩ := GlobalTheory.IdemSupport.exists_comp D
  obtain ⟨Ψ, hΨ⟩ := exists_inf D.host.F D.host.E
  have hfin : ∀ z, (Θ z).2 = Φ z := fun z => by
    induction z using TensorProduct.induction_on with
    | zero => rw [RingHom.map_zero, RingHom.map_zero]; rfl
    | add x y hx hy => rw [RingHom.map_add, RingHom.map_add, ← hx, ← hy]; rfl
    | tmul a x =>
      have e : (a ⊗ₜ[D.host.F] x : AE D) = algebraMap (AF D.host.F) (AE D) a * incA D x := by
        change _ = (a ⊗ₜ[D.host.F] (1 : D.host.E)) * ((1 : AF D.host.F) ⊗ₜ[D.host.F] x)
        rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
      rw [hΘ, e, RingHom.map_mul, hΦ.inc]
      refine FiniteAdeleRing.ext _ fun Q => ?_
      change _ = Φ _ Q * _
      rw [hΦ.base, GlobalTheory.CharTransport.locMap_eq]
      rfl
  obtain ⟨d0, d1, d2⟩ := GlobalTheory.CharTransport.isDelta_of_isPlIdem hΦ he
  have hl : Θ (locE D e (k : D.host.E)) =
      1 + Θ e * (algebraMap D.host.E (AdeleRing (𝓞 D.host.E) D.host.E) (k : D.host.E) - 1) :=
    (GlobalTheory.CharTransport.map_loc Θ e (incA D (k : D.host.E))).trans (by rw [mult_inc hΘ])
  rw [hl]
  refine Prod.ext ?_ (FiniteAdeleRing.ext _ fun Q => ?_)
  · change 1 + (Θ e).1 * _ = 1
    rw [mult_fst hΘ hΨ, d0, RingHom.map_zero, zero_mul, add_zero]
  · classical
    change 1 + (Θ e).2 Q * (algebraMap D.host.E (Q.adicCompletion D.host.E) (k : D.host.E) - 1) =
      Function.update (fun w : HeightOneSpectrum (𝓞 D.host.E) => (1 : w.adicCompletion D.host.E)) P
        (algebraMap D.host.E (P.adicCompletion D.host.E) (k : D.host.E)) Q
    rw [hfin]
    by_cases hQ : Q = P
    · subst hQ
      rw [d1, Function.update_self]
      ring
    · rw [d2 Q hQ, Function.update_of_ne hQ]
      ring

set_option maxHeartbeats 800000 in

theorem mult_infLoc {θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)} (hθ : IsInfFam (D := D) θ)
    (τ : D.what₂.Tau) (k : D.host.Eˣ) (x : AE D) (hx : IsInfLoc D θ τ (k : D.host.E) x) :
    Θ x = ((infIdele D.host.E (plOf D θ τ) (atInf (plOf D θ τ) k) : Ideles D.host.E) :
      AdeleRing (𝓞 D.host.E) D.host.E) := by
  classical
  obtain ⟨Ψ, hΨ⟩ := exists_inf D.host.F D.host.E
  obtain ⟨Φ, hΦ⟩ := exists_fin D.host.F D.host.E
  obtain ⟨h1, h2, h3⟩ := hx
  have hpl : InfinitePlace.mk (tauE D τ) = plOf D θ τ :=
    congrArg InfinitePlace.mk (RingHom.ext fun y => ((hθ τ).1 y).symm)
  refine Prod.ext (funext fun w => ?_) ?_
  · change (Θ x).1 w = Pi.mulSingle (M := fun w : InfinitePlace D.host.E => w.Completion) (plOf D θ τ)
      (algebraMap D.host.E (plOf D θ τ).Completion (k : D.host.E)) w
    rw [mult_fst hΘ hΨ]
    by_cases hw : w = plOf D θ τ
    · subst hw
      rw [Pi.mulSingle_eq_same, comp_eq hΨ (hθ τ) hpl h3, ← mult_fst hΘ hΨ, mult_inc hΘ]
      rfl
    · obtain ⟨τ', hτ'⟩ := exists_mk_tauE D w
      have hne : τ' ≠ τ := by
        rintro rfl
        exact hw (hτ'.symm.trans hpl)
      rw [Pi.mulSingle_eq_of_ne hw, comp_eq hΨ (hθ τ') hτ' ((h2 τ' hne).trans (RingHom.map_one _).symm),
        RingHom.map_one]
      rfl
  · change (Θ x).2 = 1
    rw [mult_snd hΘ hΦ, h1, RingHom.map_one]

end Mult

theorem chrEq_infLoc : ∀ (D : D7) (c : IdC D) (χ : Formalism.L2.Host.HChar D.host.E), Formalism.IndefR.Links.ChrEq c χ →
    ∀ θ, IsInfFam (D := D) θ → ∀ (τ : D.what₂.Tau) (k : D.host.Eˣ) (x : (AE D)ˣ),
      Formalism.L2.JoinChr.IsInfLoc D θ τ (k : D.host.E) (x : AE D) → ((c x : Circle) : ℂ) =
        ((χ.locInf (Formalism.L2.JoinChr.plOf D θ τ) (Formalism.L2.Host.atInf (Formalism.L2.JoinChr.plOf D θ τ) k) : ℂˣ) : ℂ) := by
  intro D c χ hcχ θ hθ τ k x hx
  have hχ : χ.IsUnitary := (GlobalTheory.T.heckeCharacter_ideleCharacter_match_unique D).2.2 c χ hcχ
  obtain ⟨Θ, hc, hΘ⟩ := GlobalTheory.CharTransport.exists_toAdele D.host.F D.host.E
  let u : (AE D)ˣ →* Ideles D.host.E := Units.map Θ.toMonoidHom
  have hu : Continuous u := Continuous.units_map _ hc
  let c' : (AE D)ˣ →* Circle :=
    { toFun := fun x => ⟨((χ.1 (u x) : ℂˣ) : ℂ), mem_sphere_zero_iff_norm.2 (hχ _)⟩
      map_one' := Circle.ext (by simp)
      map_mul' := fun x y => Circle.ext (by
        change ((χ.1 (u (x * y)) : ℂˣ) : ℂ) = ((χ.1 (u x) : ℂˣ) : ℂ) * ((χ.1 (u y) : ℂˣ) : ℂ)
        rw [map_mul, map_mul, Units.val_mul]) }
  have hcoe : ∀ x, ((c' x : Circle) : ℂ) = ((χ.1 (u x) : ℂˣ) : ℂ) := fun x => rfl
  have h' : ChrEq c' χ := by
    refine ⟨⟨?_, fun x => Circle.ext ?_⟩, fun P e he k x hx => ?_⟩
    · exact Continuous.subtype_mk (Units.continuous_val.comp (χ.2.1.comp hu)) _
    · have : u (Units.map (incA D).toMonoidHom x) = diagUnits D.host.E x := Units.ext (mult_inc hΘ x)
      rw [hcoe, this, χ.2.2]
      rfl
    · have : u x = localIdele D.host.E P (atFin P k) := by
        refine Units.ext ?_
        change Θ (x : AE D) = _
        rw [hx, mult_locE hΘ P e he]
      rw [hcoe, this]
      rfl
  have : u x = infIdele D.host.E (plOf D θ τ) (atInf (plOf D θ τ) k) :=
    Units.ext (mult_infLoc hΘ hθ τ k x hx)
  rw [(GlobalTheory.T.heckeCharacter_ideleCharacter_match_unique D).2.1 c c' χ hcχ h', hcoe, this]
  rfl

end GlobalTheory.CharInfPlace
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsMultilinearMapOfIsotypicCommutingSubgroupsStatement
section
open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC Formalism.UG Formalism.BasicNotions GlobalTheory.DefU
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_multilinearMap_of_isotypic_commuting_subgroups : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (G V : Type) [Group G] [AddCommGroup V] [Module ℂ V] (H : ι → Type) [∀ v, Group (H v)] (Wv : ι → Type) [∀ v, AddCommGroup (Wv v)] [∀ v, Module ℂ (Wv v)] [∀ v, FiniteDimensional ℂ (Wv v)] (ρ : Representation ℂ G V) (s : ∀ v, H v →* G) (σ : ∀ v, Representation ℂ (H v) (Wv v)), Nontrivial V → (∀ v, (σ v).IsIrreducible) → (∀ u v, u ≠ v → ∀ a b, Commute (s u a) (s v b)) → (∀ v, (⨆ f : (σ v).IntertwiningMap (ρ.comp (s v)), LinearMap.range f.toLinearMap) = ⊤) → ∃ F : MultilinearMap ℂ Wv V, F ≠ 0 ∧ ∀ v (h : H v) (x : ∀ u, Wv u), ρ (s v h) (F x) = F (Function.update x v (σ v h (x v))) := by
  first | exact @GlobalTheory.exists_multilinearMap_of_isotypic_commuting | exact GlobalTheory.exists_multilinearMap_of_isotypic_commuting | (intros; apply GlobalTheory.exists_multilinearMap_of_isotypic_commuting <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsRealPlaceRecordTied
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory

theorem exists_realPlace_record_tied :
    (∀ (p q : ℕ) (T : GrpData p q) (lam : Ix p q → ℚ), IsParam lam → ∃ R : DSRep T, HasParam R lam) →
    ∀ D : D7, ∃ A : ProvA, ProvisionCompatibility D A := by
  intro H D
  classical
  choose grp hgrp using fun p q : ℕ =>
    GlobalTheory.DetSqrtCover.exists_grpData_map_haar p q (D.cd.cd p q) (D.cd.haar p q)
  have key : ∀ (p q : ℕ) (lam : Ix p q → ℚ), ∃ R : DSRep (grp p q),
      IsParam lam → HasParam R lam := by
    intro p q lam
    by_cases h : IsParam lam
    · obtain ⟨R, hR⟩ := H p q (grp p q) lam h
      exact ⟨R, fun _ => hR⟩
    · obtain ⟨R, -⟩ := H p q (grp p q) _ (realPlaceStdParam_isParam p q)
      exact ⟨R, fun h' => absurd h' h⟩
  choose ds hds using key
  exact ⟨⟨grp, fun p q r s => Classical.choice (GlobalTheory.T.nonempty_fockModel_unitary_dual_pair p q r s _ _ _), ds⟩,
    ⟨hgrp, fun p q lam h => by first | exact hds p q lam h | exact fun _ => hds p q lam h⟩⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsTorusBoundsOfConsecutiveRatioBoundsStatement
section
open NumberField IsDedekindDomain ValuativeRel Matrix MeasureTheory TensorProduct Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.Whittaker GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocDict
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_torus_bounds_of_consecutive_ratio_bounds : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (m : ℕ) (r1 r2 : Fin m → kˣ), ∃ R1 R2 : kˣ, ∀ t : Fin (m + 1) → kˣ, t (Fin.last m) = 1 → (∀ i : Fin m, valuation k (r2 i : k) ≤ valuation k ((t i.castSucc : k) / t i.succ) ∧ valuation k ((t i.castSucc : k) / t i.succ) ≤ valuation k (r1 i : k)) → ∀ i, valuation k (R2 : k) ≤ valuation k (t i : k) ∧ valuation k (t i : k) ≤ valuation k (R1 : k) := by
  first | exact @GlobalTheory.chain_bound | exact GlobalTheory.chain_bound | (intros; apply GlobalTheory.chain_bound <;> assumption)
end

