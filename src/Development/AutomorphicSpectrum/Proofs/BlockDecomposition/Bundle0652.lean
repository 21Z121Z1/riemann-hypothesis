import Mathlib
import Development.WeilBound.CoreStatements.PublishedTheorems.JacquetShalikaBound.lift_levelP_alt₂
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0562
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1428
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0616
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0621
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0607
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.LocalComparisonSplitting.EulerFactorLevels.LocCompareSplit
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0622
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1369
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1414
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DetGramRatOneNeZero
import Development.WeilBound.CoreStatements.AutomorphicKernels.IsobaricBaseChange.IntegralCoefficientBaseChange.UnitaryBaseChangeCharacters.UnitaryBaseChangeLemmas.ToComplBijective
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0641
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0322
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0632
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0623
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0590
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.HaarFundamentalDomainOrthogonalSum

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsUnitForm
section
noncomputable section

open NumberField IsDedekindDomain Matrix Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.LFun PositivityTheory.JacquetShalikaLocal

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.CompanionTheory.JSUnit

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ}

theorem norm_central (π : CuspSub E a) (H : π.V →ₗ⋆[ℂ] π.V →ₗ[ℂ] ℂ) (hp : ∀ φ, φ ≠ 0 → 0 < (H φ φ).re)
    (hi : ∀ k φ ψ, H (π.op (.fin k) φ) (π.op (.fin k) ψ) = H φ ψ) {ω : HChar E} (hω : π.HasCentChar ω) (z) :
    ‖((ω.1 (finId E z) : ℂˣ) : ℂ)‖ = 1 := by
  have := Submodule.nontrivial_iff_ne_bot.2 π.ne_bot
  obtain ⟨x, hx⟩ := exists_ne (0 : π.V)
  have h1 : π.op (.fin (GeneralLinearGroup.scalar (Fin a) z)) x = ((ω.1 (finId E z) : ℂˣ) : ℂ) • x := hω z x
  have h2 := hi (GeneralLinearGroup.scalar (Fin a) z) x x
  rw [h1] at h2
  generalize ((ω.1 (finId E z) : ℂˣ) : ℂ) = c at h2 ⊢
  simp only [map_smulₛₗ, map_smul, LinearMap.smul_apply, smul_eq_mul] at h2
  have hne : H x x ≠ 0 := fun e => by
    have h := hp x hx
    simp [e] at h
  have h3 : starRingEnd ℂ c * c = 1 := mul_right_cancel₀ hne (by linear_combination h2)
  rw [Complex.conj_mul'] at h3
  have h4 : ‖c‖ ^ 2 = 1 := by exact_mod_cast h3
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).1 h4

theorem norm_loc (π : CuspSub E a) (H : π.V →ₗ⋆[ℂ] π.V →ₗ[ℂ] ℂ) (hp : ∀ φ, φ ≠ 0 → 0 < (H φ φ).re)
    (hi : ∀ k φ ψ, H (π.op (.fin k) φ) (π.op (.fin k) ψ) = H φ ψ) (χ : HChar E) {ω : HChar E} (hu : ω.IsUnitary)
    (hω : (π.twist χ).HasCentChar ω) (ha : a ≠ 0) (w : HeightOneSpectrum (𝓞 E)) (g : GL (Fin a) (w.adicCompletion E)) :
    ‖((χ.loc w (GeneralLinearGroup.det g) : ℂˣ) : ℂ)‖ = 1 := by
  have e : (π.twist χ).twist χ⁻¹ = π := by
    rw [← CuspSub.twist_mul, mul_inv_cancel, CuspSub.twist_one]
  have h2 := hω.twist χ⁻¹
  rw [e] at h2
  have h3 := norm_central π H hp hi h2 (GeneralLinearGroup.det (locGL E a w g))
  rw [finId_det_locGL] at h3
  generalize GeneralLinearGroup.det g = u at h3 ⊢
  have h4 : ‖((ω.loc w u : ℂˣ) : ℂ)‖ = 1 := hu _
  have h5 : (ω * χ⁻¹ ^ a).loc w u = ω.loc w u * (χ.loc w u)⁻¹ ^ a := rfl
  change ‖(((ω * χ⁻¹ ^ a).loc w u : ℂˣ) : ℂ)‖ = 1 at h3
  rw [h5] at h3
  simp only [Units.val_mul, Units.val_pow_eq_pow_val, Units.val_inv_eq_inv_val, norm_mul, norm_pow, norm_inv, h4,
    one_mul] at h3
  have h6 := (pow_eq_one_iff_of_nonneg (by positivity) ha).1 h3
  exact inv_eq_one.1 h6

theorem exists_unit_form : G1 := by
  intro E _ _ _ a π hu w
  obtain ⟨ω, hωu, hω⟩ := hu
  rw [CG.hasCentChar_mk] at hω
  obtain ⟨π₀, χ, hn, rfl⟩ := GlobalTheory.CompanionTheory.TwistNorm.exists_twist_normalised π
  obtain ⟨H, h1, h2, h3, -, -⟩ := GlobalTheory.GelfandKazhdanHerm.exists_invariant_hermitian
    GlobalTheory.CompanionTheory.CuspFinGL.cuspFormsBoundedGL E a π₀ hn
  let T := π₀.toTwist χ
  have hT : ∀ g x, (π₀.twist χ).locRep w g (T x) =
      ((χ.loc w (GeneralLinearGroup.det g) : ℂˣ) : ℂ) • T (π₀.locRep w g x) := fun g x => by
    rw [CuspSub.locRep_eq, CuspSub.op_toTwist, opAdd, zero_smul, add_zero, map_smul, opMul, CuspSub.chiDet_locGL]
    rfl
  have hn1 : ∀ g : GL (Fin a) (w.adicCompletion E), ‖((χ.loc w (GeneralLinearGroup.det g) : ℂˣ) : ℂ)‖ = 1 := fun g => by
    rcases eq_or_ne a 0 with rfl | ha
    · rw [show GeneralLinearGroup.det g = 1 from Units.ext (by simp [Matrix.det_isEmpty]), map_one]
      simp
    · exact norm_loc π₀ H h2 h3 χ hωu hω ha w g
  refine ⟨(H.comp T.symm.toLinearMap).compl₂ T.symm.toLinearMap, ?_⟩
  refine And.intro (fun u v => ?_) (And.intro (fun u hu => ?_) fun g u v => ?_)
  · simpa using h1 (T.symm u) (T.symm v)
  · exact h2 _ (T.symm.map_ne_zero_iff.2 hu)
  · obtain ⟨u, rfl⟩ := T.surjective u
    obtain ⟨v, rfl⟩ := T.surjective v
    rw [hT, hT]
    generalize hc : ((χ.loc w (GeneralLinearGroup.det g) : ℂˣ) : ℂ) = c
    have hcc : starRingEnd ℂ c * c = 1 := by
      rw [Complex.conj_mul', ← hc, hn1 g]
      simp
    simp only [LinearMap.compl₂_apply, LinearMap.comp_apply, LinearEquiv.coe_coe, map_smulₛₗ, map_smul, LinearMap.smul_apply,
      LinearEquiv.symm_apply_apply, smul_eq_mul]
    rw [CuspSub.locRep_eq, h3, ← mul_assoc, RingHom.id_apply, mul_comm c, hcc, one_mul]

end GlobalTheory.CompanionTheory.JSUnit

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FactorInductionStatement
section
open GlobalTheory.CompanionTheory.EGlue
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.factor_induction : GlobalTheory.CompanionTheory.EGlue.FactorStep := by
  first | exact @GlobalTheory.CompanionTheory.EGlue.factorStep_holds | exact GlobalTheory.CompanionTheory.EGlue.factorStep_holds | (intros; apply GlobalTheory.CompanionTheory.EGlue.factorStep_holds <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FactorLimitStatement
section
open GlobalTheory.CompanionTheory.EGlue
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.factor_limit : GlobalTheory.CompanionTheory.EGlue.ConvComp → GlobalTheory.CompanionTheory.EGlue.LimTrees → GlobalTheory.CompanionTheory.EGlue.LeafBound → GlobalTheory.CompanionTheory.EGlue.ConvInf → GlobalTheory.CompanionTheory.EGlue.InfOfEq → GlobalTheory.CompanionTheory.EGlue.CapEquiv → GlobalTheory.CompanionTheory.EGlue.MCloseFacts → GlobalTheory.CompanionTheory.EGlue.FactorLim := by
  first | exact @GlobalTheory.CompanionTheory.EGlue.FactorLimProof.factorLim_of_parts | exact GlobalTheory.CompanionTheory.EGlue.FactorLimProof.factorLim_of_parts | (intros; apply GlobalTheory.CompanionTheory.EGlue.FactorLimProof.factorLim_of_parts <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteConjugacyExistsStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_conjugacy_exists : PositivityTheory.Rg.BcB.G8.Fin.CjEx := by
  first | exact @GlobalTheory.CompanionTheory.CjEx.cjEx | exact GlobalTheory.CompanionTheory.CjEx.cjEx | (intros; apply GlobalTheory.CompanionTheory.CjEx.cjEx <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteEulerProductOfStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_euler_product_of : PositivityTheory.Rg.BcB.G8.Fin.EulerFinOf' := by
  first | exact @GlobalTheory.CompanionTheory.EulerAsm.eulerFinOf' | exact GlobalTheory.CompanionTheory.EulerAsm.eulerFinOf' | (intros; apply GlobalTheory.CompanionTheory.EulerAsm.eulerFinOf' <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteNonsplitSignPlacesStatement
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.UnitaryClasses
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.IndefiniteRowSideFullHecke.SelfReciprocalLocalField PositivityTheory.BCUSide.HermitianLocalForms
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_nonsplit_sign_places : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (n : ℕ) (γ₀ : GL (Fin n) E) (H₀ : Matrix (Fin n) (Fin n) E), IsHerm (IsCMField.complexConj E).toRingEquiv.toRingHom H₀ → H₀.det ≠ 0 → (∀ τ : E →+* ℂ, ∃ Q : Matrix (Fin n) (Fin n) ℂ, Q.det ≠ 0 ∧ H₀.map τ = cT (starRingEnd ℂ) Q * Q) → ∀ P₁ : E[X], {w : Pl E | ¬ IsSplitAt w ∧ sgnOn (cj w) (H₀.map (algebraMap E (w.adicCompletion E))) (atPl w P₁) (γ₀.val.map (algebraMap E (w.adicCompletion E))) ≠ 1}.Finite := by
  first | exact @GlobalTheory.CompanionTheory.FinSign.main | exact GlobalTheory.CompanionTheory.FinSign.main | (intros; apply GlobalTheory.CompanionTheory.FinSign.main <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteOnCompactsOrbitMeasure
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

namespace GlobalTheory.CompanionTheory.ColumnSplitting.Cpt

variable {D : D7} {n t : ℕ} {B W : HSp D}

theorem isCompact_mt_preimage (V : HSp D) {T : Set (Mx D V.rank V.rank)} (hT : IsCompact T) :
    IsCompact {g : GA D V | mt V g ∈ T} := by
  have := isTopologicalRing_tens (F := D.host.F) (E := D.host.E) (R := AF D.host.F)
  obtain ⟨-, -, -, i4, -⟩ := top_mx (D := D) V.rank V.rank
  have i1 : T1Space (Mx D V.rank V.rank) := @T2Space.t1Space _ _ i4
  have he : Topology.IsClosedEmbedding (fun g : GA D V =>
      Units.embedProduct (Mx D V.rank V.rank) (GlobalTheory.AdelicU.matHom (AF D.host.F) D.sp.cm.sig V.gram g)) :=
    Units.isClosedEmbedding_embedProduct.comp (isClosedEmbedding_matHom_GAd D.sp.cm.sig V.gram)
  have hc : Continuous fun X : Mx D V.rank V.rank => giA V * (adj X * gA V) :=
    continuous_const.matrix_mul (continuous_adj.matrix_mul continuous_const)
  have hK := he.isCompact_preimage (hT.prod ((hT.image hc).image MulOpposite.continuous_op))
  refine hK.of_isClosed_subset (hT.isClosed.preimage (continuous_mt V)) fun g hg => ?_
  refine ⟨hg, _, ⟨mt V g, hg, rfl⟩, ?_⟩
  simp only [Units.embedProduct_apply]
  rw [← GlobalTheory.MixModel.mt_inv]; rfl

theorem det_ne_zero {x₀ : Matrix (Fin W.rank) (Fin W.rank) D.host.E} {b : Matrix (Fin W.rank) (Fin W.rank) D.host.E}
    (hb : b.det ≠ 0) (h : gramQ W x₀ = b) : x₀.det ≠ 0 := by
  intro h0
  apply hb
  rw [← h, gramQ]
  simp [Matrix.det_mul, h0]

theorem rat_inv_mul {x₀ : Matrix (Fin W.rank) (Fin W.rank) D.host.E} (h : x₀.det ≠ 0) :
    mm (rat x₀⁻¹) (rat x₀) = (1 : Mx D W.rank W.rank) := by
  rw [mm, ← rat_mul, Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.2 h)]
  exact Matrix.map_one _ (map_zero _) (map_one _)

theorem rat_mul_inv {x₀ : Matrix (Fin W.rank) (Fin W.rank) D.host.E} (h : x₀.det ≠ 0) :
    mm (rat x₀) (rat x₀⁻¹) = (1 : Mx D W.rank W.rank) := by
  rw [mm, ← rat_mul, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.2 h)]
  exact Matrix.map_one _ (map_zero _) (map_one _)

theorem join_first_second_columns_eq (hn : W.rank + t = n) {a : ℕ} (U : Mx D a n) : jn hn (c1 hn U) (c2 hn U) = U := by
  ext i j
  obtain ⟨s, rfl⟩ := (finSumFinEquiv.trans (finCongr hn)).surjective j
  rcases s with s | s <;> simp [jn, c1, c2]

theorem continuous_jn (hn : W.rank + t = n) {a : ℕ} :
    Continuous fun p : Mx D a W.rank × Mx D a t => jn hn p.1 p.2 := by
  refine continuous_matrix fun i j => ?_
  simp only [jn, Matrix.submatrix_apply, id]
  rcases (finSumFinEquiv.trans (finCongr hn)).symm j with s | s
  · exact (continuous_fst.matrix_elem i s)
  · exact (continuous_snd.matrix_elem i s)

theorem box_rec (d : HypDec B W t) {a : ℕ} (u : Mx D t a) (w : Mx D W.rank a) :
    mm d.p0 (mm d.jX u + mm d.j0 w) = w ∧ mm d.pX (mm d.jX u + mm d.j0 w) = u := by
  constructor
  · rw [mm, Matrix.mul_add, mm, mm, ← Matrix.mul_assoc, ← Matrix.mul_assoc, d.p0_jX, d.p0_j0,
      Matrix.zero_mul, Matrix.one_mul, zero_add]
  · rw [mm, Matrix.mul_add, mm, mm, ← Matrix.mul_assoc, ← Matrix.mul_assoc, d.pX_jX, d.pX_j0,
      Matrix.zero_mul, Matrix.one_mul, add_zero]

theorem zp_rec (d : HypDec B W t) (hn : W.rank + t = n) (x₀ : Matrix (Fin W.rank) (Fin W.rank) D.host.E)
    (p : Par D n t W) :
    mm d.p0 (zp d hn x₀ p).1 = ww W x₀ p.1 ∧ mm d.pX (zp d hn x₀ p).1 = c1 hn p.2.1 ∧
      mm d.p0 (zp d hn x₀ p).2 = mm (ww W x₀ p.1) p.2.2 ∧
      mm d.pX ((zp d hn x₀ p).2 - mm (zp d hn x₀ p).1 p.2.2) = c2 hn p.2.1 := by
  obtain ⟨h1, h2⟩ := box_rec (a := W.rank) d (c1 hn p.2.1) (ww W x₀ p.1)
  refine ⟨h1, h2, ?_, ?_⟩
  · change mm d.p0 (mm (mm d.jX (c1 hn p.2.1) + mm d.j0 (ww W x₀ p.1)) p.2.2 + mm d.jX (c2 hn p.2.1)) = _
    simp only [mm] at h1 ⊢
    rw [Matrix.mul_add, ← Matrix.mul_assoc d.p0 _ p.2.2, h1, ← Matrix.mul_assoc, d.p0_jX, Matrix.zero_mul, add_zero]
  · change mm d.pX (mm (mm d.jX (c1 hn p.2.1) + mm d.j0 (ww W x₀ p.1)) p.2.2 + mm d.jX (c2 hn p.2.1) -
      mm (mm d.jX (c1 hn p.2.1) + mm d.j0 (ww W x₀ p.1)) p.2.2) = _
    rw [add_sub_cancel_left, mm, mm, ← Matrix.mul_assoc, d.pX_jX, Matrix.one_mul]

theorem ac_ac (V : HSp D) {a b : ℕ} (g : GA D V) (z : Mx D V.rank a × Mx D V.rank b) :
    ac V g (ac V g⁻¹ z) = z := by
  have e : ∀ {c : ℕ} (x : Mx D V.rank c), mm (mt V g) (mm (mt V g⁻¹) x) = x := fun x => by
    rw [mm, mm, ← Matrix.mul_assoc, GlobalTheory.MixModel.mt_mul_inv, Matrix.one_mul]
  exact Prod.ext (e z.1) (e z.2)

theorem exists_box (d : HypDec B W t) (hn : W.rank + t = n) (I : IkD d n)
    {x₀ : Matrix (Fin W.rank) (Fin W.rank) D.host.E} (hx : x₀.det ≠ 0)
    {C : Set (Mx D B.rank W.rank × Mx D B.rank t)} (hC : IsCompact C) :
    ∃ (Ah : Set (GA D W)) (AU : Set (Mx D t n)) (Ay : Set (Mx D W.rank t)),
      IsCompact Ah ∧ IsCompact AU ∧ IsCompact Ay ∧ ∀ (k : I.l.K) (p : Par D n t W),
        ac B ((k : GA D B)⁻¹) (zp d hn x₀ p) ∈ C → p.1 ∈ Ah ∧ p.2.1 ∈ AU ∧ p.2.2 ∈ Ay := by
  have := isTopologicalRing_tens (F := D.host.F) (E := D.host.E) (R := AF D.host.F)
  obtain ⟨-, -, -, -, g5, -⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D W
  obtain ⟨t1, -, -, -, -⟩ := top_mx (D := D) B.rank W.rank
  obtain ⟨t2, -, -, -, -⟩ := top_mx (D := D) B.rank t
  obtain ⟨t3, -, -, -, -⟩ := top_mx (D := D) t W.rank
  obtain ⟨t4, -, -, -, -⟩ := top_mx (D := D) t t
  set C' : Set (Mx D B.rank W.rank × Mx D B.rank t) :=
    (fun u : GA D B × (Mx D B.rank W.rank × Mx D B.rank t) => ac B u.1 u.2) '' ((I.l.K : Set (GA D B)) ×ˢ C) with hC'
  have cC' : IsCompact C' := (I.good.isCompact_K.prod hC).image (continuous_ac B)
  set Aw : Set (Mx D W.rank W.rank) := (fun z : Mx D B.rank W.rank × Mx D B.rank t => mm d.p0 z.1) '' C' with hAw
  have cAw : IsCompact Aw := cC'.image (continuous_const.matrix_mul continuous_fst)
  set T : Set (Mx D W.rank W.rank) := (fun X : Mx D W.rank W.rank => mm X (rat x₀⁻¹)) '' Aw with hT
  have cT : IsCompact T := cAw.image (continuous_id.matrix_mul continuous_const)
  set Ah : Set (GA D W) := (fun g : GA D W => g⁻¹) '' {g : GA D W | mt W g ∈ T} with hAh
  have cAh : IsCompact Ah := (isCompact_mt_preimage W cT).image continuous_inv
  set Ay : Set (Mx D W.rank t) :=
    (fun u : GA D W × (Mx D B.rank W.rank × Mx D B.rank t) => mm (rat x₀⁻¹) (mm (mt W u.1) (mm d.p0 u.2.2))) ''
      (Ah ×ˢ C') with hAy
  have cAy : IsCompact Ay := (cAh.prod cC').image (continuous_const.matrix_mul
    (((continuous_mt W).comp continuous_fst).matrix_mul
      (continuous_const.matrix_mul (continuous_snd.comp continuous_snd))))
  set AU : Set (Mx D t n) :=
    (fun u : (Mx D B.rank W.rank × Mx D B.rank t) × Mx D W.rank t =>
      jn hn (mm d.pX u.1.1) (mm d.pX (u.1.2 - mm u.1.1 u.2))) '' (C' ×ˢ Ay) with hAU
  have s2 : ContinuousSub (Mx D B.rank t) := @IsTopologicalAddGroup.to_continuousSub _ _ _ t2
  have cAU : IsCompact AU := (cC'.prod cAy).image ((continuous_jn (W := W) hn).comp
    ((continuous_const.matrix_mul (continuous_fst.comp continuous_fst)).prodMk
      (continuous_const.matrix_mul ((continuous_snd.comp continuous_fst).sub
        ((continuous_fst.comp continuous_fst).matrix_mul continuous_snd)))))
  refine ⟨Ah, AU, Ay, cAh, cAU, cAy, fun k p hp => ?_⟩
  have e1 := rat_mul_inv hx
  have e2 := rat_inv_mul hx
  simp only [mm] at e1 e2
  have hz : zp d hn x₀ p ∈ C' := ⟨((k : GA D B), ac B ((k : GA D B)⁻¹) (zp d hn x₀ p)), ⟨k.2, hp⟩, ac_ac B _ _⟩
  obtain ⟨r1, r2, r3, r4⟩ := zp_rec d hn x₀ p
  have hw : ww W x₀ p.1 ∈ Aw := ⟨_, hz, r1⟩
  have hg : mt W p.1⁻¹ ∈ T := ⟨_, hw, by
    change mm (mm (mt W p.1⁻¹) (rat x₀)) (rat x₀⁻¹) = _
    simp only [mm]
    rw [Matrix.mul_assoc, e1, Matrix.mul_one]⟩
  have hh : p.1 ∈ Ah := ⟨p.1⁻¹, hg, inv_inv _⟩
  have hy : p.2.2 ∈ Ay := ⟨(p.1, zp d hn x₀ p), ⟨hh, hz⟩, by
    change mm (rat x₀⁻¹) (mm (mt W p.1) (mm d.p0 (zp d hn x₀ p).2)) = _
    rw [r3]
    change mm (rat x₀⁻¹) (mm (mt W p.1) (mm (mm (mt W p.1⁻¹) (rat x₀)) p.2.2)) = _
    simp only [mm]
    rw [← Matrix.mul_assoc (mt W p.1), ← Matrix.mul_assoc (mt W p.1),
      GlobalTheory.MixModel.mt_mul_inv, Matrix.one_mul, ← Matrix.mul_assoc, e2, Matrix.one_mul]⟩
  have hU : p.2.1 ∈ AU := ⟨(zp d hn x₀ p, p.2.2), ⟨hz, hy⟩, by
    change jn hn (mm d.pX (zp d hn x₀ p).1) (mm d.pX ((zp d hn x₀ p).2 - mm (zp d hn x₀ p).1 p.2.2)) = _
    rw [r2, r4, join_first_second_columns_eq]⟩
  exact ⟨hh, hU, hy⟩

end GlobalTheory.CompanionTheory.ColumnSplitting.Cpt

namespace GlobalTheory.CompanionTheory.ColumnSplitting

theorem isFiniteMeasureOnCompacts_nuT : ∀ (D : D7) (n t : ℕ) (B W : HSp D) (d : HypDec B W t) (hn : W.rank + t = n)
    (I : IkD d n) (μ : Measure (Mx D W.rank t)), μ.IsAddHaarMeasure → ∀ (b₀ : HermE D W.rank), b₀.1.det ≠ 0 →
    ∀ x₀, gramQ W x₀ = b₀.1 → IsFiniteMeasureOnCompacts (nuT hn I μ x₀) := by
  intro D n t B W d hn I μ hμ b₀ hb x₀ hx
  obtain ⟨-, i2, i3, i4, i5⟩ := top_mx (D := D) t n
  obtain ⟨-, j2, j3, j4, j5⟩ := top_mx (D := D) W.rank t
  obtain ⟨-, g2, g3, -, -, -⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D W
  obtain ⟨-, -, -, k4, -⟩ := top_mx (D := D) B.rank W.rank
  obtain ⟨-, -, -, l4, -⟩ := top_mx (D := D) B.rank t
  obtain ⟨p1, p2⟩ := top_pair (D := D) B.rank W.rank t
  have : BorelSpace (GA D W) := ⟨rfl⟩
  obtain ⟨hc, 𝓕, hf⟩ := I.cov₁
  have := 𝓕
  have := I.haar
  have := I.probK
  have o1 : OpensMeasurableSpace (Mx D B.rank W.rank × Mx D B.rank t) := p1.opensMeasurable
  have := sigmaFinite_parameter_product_measure I μ hμ
  refine ⟨fun C hC => ?_⟩
  obtain ⟨Ah, AU, Ay, cAh, cAU, cAy, h⟩ := Cpt.exists_box d hn I (Cpt.det_ne_zero hb hx) hC
  rw [nuT, Measure.map_apply (measurable_pi hn I x₀) hC.measurableSet]
  have hsub : (fun p : I.l.K × Par D n t W => ac B ((p.1 : GA D B)⁻¹) (zp d hn x₀ p.2)) ⁻¹' C ⊆
      Set.univ ×ˢ (Ah ×ˢ (AU ×ˢ Ay)) := fun p hp => by
    obtain ⟨a, b, c⟩ := h p.1 p.2 hp
    exact ⟨trivial, a, b, c⟩
  refine (measure_mono hsub).trans_lt ?_
  rw [Q0, Measure.prod_prod, Measure.prod_prod, Measure.prod_prod]
  exact ENNReal.mul_lt_top (measure_lt_top _ _) (ENNReal.mul_lt_top cAh.measure_lt_top
    (ENNReal.mul_lt_top cAU.measure_lt_top cAy.measure_lt_top))

end GlobalTheory.CompanionTheory.ColumnSplitting
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteReindexingStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_reindexing : PositivityTheory.Rg.BcB.G8.Fin.Reindex := by
  first | exact @GlobalTheory.CompanionTheory.SecReindex.reindex | exact GlobalTheory.CompanionTheory.SecReindex.reindex | (intros; apply GlobalTheory.CompanionTheory.SecReindex.reindex <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteRestrictionVanishingStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_restriction_vanishing : PositivityTheory.Rg.BcB.G8.Fin.RestrV := by
  first | exact @GlobalTheory.CompanionTheory.EulerV.main | exact GlobalTheory.CompanionTheory.EulerV.main | (intros; apply GlobalTheory.CompanionTheory.EulerV.main <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteTwistedDoubleCosets
section
noncomputable section

open NumberField IsDedekindDomain Matrix Polynomial Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.G8.Fin GlobalTheory.CompanionTheory.LocalHypotheses
open scoped Classical

namespace GlobalTheory.CompanionTheory.LocHypSplit

theorem finite_of_subset_mul {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (T K' : Subgroup G)
    (hK' : IsOpen (K' : Set G)) (D : Set G) (hD : IsCompact D)
    (P : G → Prop) (hP : ∀ x, P x → ∃ t ∈ T, ∃ d ∈ D, x = t * d) :
    {q : DoubleCoset.Quotient (T : Set G) (K' : Set G) | P (Quotient.out q)}.Finite := by
  obtain ⟨s, hs⟩ := compact_covered_by_mul_left_translates hD
    (show (interior (K' : Set G)).Nonempty from ⟨1, hK'.interior_eq.symm ▸ K'.one_mem⟩)
  refine (s.finite_toSet.image fun g => DoubleCoset.mk T K' g⁻¹).subset ?_
  intro q hq
  obtain ⟨t, ht, d, hd, hx⟩ := hP _ hq
  have := hs hd
  simp only [Set.mem_iUnion, Set.mem_preimage, SetLike.mem_coe] at this
  obtain ⟨g, hg, hgd⟩ := this
  refine ⟨g, hg, ?_⟩
  rw [← DoubleCoset.out_eq' T K' q, DoubleCoset.eq]
  exact ⟨t, ht, g * d, hgd, by simp [hx, mul_assoc]⟩

open scoped Pointwise in

theorem finite_doubleCosets_split : ∀ {H : Type} [Group H] [TopologicalSpace H] [IsTopologicalGroup H] (σ : H →* H) (K : Subgroup H) (d d' : H) (f : H × H → ℂ)
  (C₁ C₂ : Set H), Continuous σ → (∀ g, σ (σ g) = g) → IsOpen (K : Set H) → IsCompact (K : Set H) → (∀ k ∈ K, σ k ∈ K) →
  IsCompact C₁ → IsCompact C₂ → (∀ y, f y ≠ 0 → y.1 ∈ C₁ ∧ y.2 ∈ C₂) →
  (∀ C : Set H, IsCompact C → {q : DoubleCoset.Quotient (twCent (MonoidHom.id H) (d * σ d') : Set H) (K : Set H) |
    ∃ k ∈ K, (Quotient.out q * k)⁻¹ * (d * σ d') * MonoidHom.id H (Quotient.out q * k) ∈ C}.Finite) →
  {q : DoubleCoset.Quotient (twCent (swTw σ) (d, d') : Set (H × H)) (K.prod K : Set (H × H)) |
    ∃ k ∈ K.prod K, f ((Quotient.out q * k)⁻¹ * (d, d') * swTw σ (Quotient.out q * k)) ≠ 0}.Finite := by
  intro H _ _ _ σ K d d' f C₁ C₂ hσc hσ hKo hKc _ hC₁ hC₂ hf hfin
  have hC : IsCompact (C₁ * σ '' C₂) := hC₁.mul (hC₂.image hσc)
  have hSf := hfin _ hC
  set S := {q : DoubleCoset.Quotient (twCent (MonoidHom.id H) (d * σ d') : Set H) (K : Set H) |
    ∃ k ∈ K, (Quotient.out q * k)⁻¹ * (d * σ d') * MonoidHom.id H (Quotient.out q * k) ∈ C₁ * σ '' C₂} with hS
  have hR : IsCompact ((fun q => Quotient.out q) '' S : Set H) := (hSf.image _).isCompact
  set A : Set H := ((fun q => Quotient.out q) '' S : Set H) * (K : Set H) with hAdef
  have hA : IsCompact A := hR.mul hKc
  set B : Set H := σ '' ((fun a => d⁻¹ * a) '' A * C₁) with hBdef
  have hB : IsCompact B := ((hA.image (continuous_const.mul continuous_id)).mul hC₁).image hσc
  have hKKo : IsOpen ((K.prod K : Subgroup (H × H)) : Set (H × H)) := by
    rw [Subgroup.coe_prod]; exact hKo.prod hKo
  have hKKc : IsCompact ((K.prod K : Subgroup (H × H)) : Set (H × H)) := by
    rw [Subgroup.coe_prod]; exact hKc.prod hKc
  have hD : IsCompact ((fun p : (H × H) × (H × H) => p.1 * p.2⁻¹) ''
      ((A ×ˢ B) ×ˢ ((K.prod K : Subgroup (H × H)) : Set (H × H)))) :=
    ((hA.prod hB).prod hKKc).image (continuous_fst.mul continuous_snd.inv)
  have key : ∀ y₁ y₂ : H, y₁⁻¹ * d * σ y₂ ∈ C₁ → y₂⁻¹ * d' * σ y₁ ∈ C₂ →
      ∃ t ∈ twCent (swTw σ) (d, d'), ∃ a ∈ A, ∃ b ∈ B, ((y₁, y₂) : H × H) = t * (a, b) := by
    intro y₁ y₂ h₁ h₂
    have hN : y₁⁻¹ * (d * σ d') * y₁ ∈ C₁ * σ '' C₂ := by
      refine Set.mem_mul.2 ⟨_, h₁, _, ⟨_, h₂, rfl⟩, ?_⟩
      simp only [map_mul, map_inv, hσ]
      group
    obtain ⟨h, k, hh, hk, e⟩ := DoubleCoset.mk_out_eq_mul (twCent (MonoidHom.id H) (d * σ d')) K y₁
    have ez : Quotient.out (DoubleCoset.mk (twCent (MonoidHom.id H) (d * σ d')) K y₁) * k⁻¹ = h * y₁ := by
      rw [e, mul_inv_cancel_right]
    have hh' : h * (d * σ d') = d * σ d' * h := hh
    have hq : DoubleCoset.mk (twCent (MonoidHom.id H) (d * σ d')) K y₁ ∈ S := by
      refine ⟨k⁻¹, inv_mem hk, ?_⟩
      rw [ez, MonoidHom.id_apply]
      have : (h * y₁)⁻¹ * (d * σ d') * (h * y₁) = y₁⁻¹ * (d * σ d') * y₁ := by
        rw [_root_.mul_inv_rev, mul_assoc, ← mul_assoc (d * σ d') h y₁, ← hh']
        group
      rw [this]; exact hN
    have hw : h * y₁ ∈ A := by
      rw [← ez]
      exact Set.mem_mul.2 ⟨_, ⟨_, hq, rfl⟩, _, inv_mem hk, rfl⟩
    have ht := (mem_twCent_swTw σ hσ d d' (h⁻¹, d' * σ h⁻¹ * d'⁻¹)).2 ⟨inv_mem hh, rfl⟩
    set t₂ := d' * σ h⁻¹ * d'⁻¹ with ht₂
    have e₁ : h⁻¹ * d = d * σ t₂ := congrArg Prod.fst ht
    have e₂ : d⁻¹ * h * d = (σ t₂)⁻¹ := by
      have : σ t₂ = d⁻¹ * (h⁻¹ * d) := by rw [e₁]; group
      rw [this]; group
    refine ⟨(h⁻¹, t₂), ht, h * y₁, hw, t₂⁻¹ * y₂,
      ⟨(d⁻¹ * (h * y₁)) * (y₁⁻¹ * d * σ y₂), Set.mem_mul.2 ⟨_, ⟨_, hw, rfl⟩, _, h₁, rfl⟩, ?_⟩, ?_⟩
    · have : d⁻¹ * (h * y₁) * (y₁⁻¹ * d * σ y₂) = (d⁻¹ * h * d) * σ y₂ := by group
      rw [this, e₂, map_mul, map_inv, hσ, hσ]
    · ext <;> simp
  refine finite_of_subset_mul (twCent (swTw σ) (d, d')) (K.prod K) hKKo _ hD
    (fun x => ∃ k ∈ K.prod K, f ((x * k)⁻¹ * (d, d') * swTw σ (x * k)) ≠ 0) ?_
  rintro x ⟨k, hk, hx⟩
  obtain ⟨t, ht, a, ha, b, hb, e⟩ := key (x * k).1 (x * k).2 (hf _ hx).1 (hf _ hx).2
  have e' : x * k = t * (a, b) := e
  refine ⟨t, ht, (a, b) * k⁻¹, ⟨(((a, b)), k), ⟨⟨ha, hb⟩, hk⟩, rfl⟩, ?_⟩
  rw [← mul_assoc, ← e', mul_inv_cancel_right]

end GlobalTheory.CompanionTheory.LocHypSplit

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FramesSumByFirstVectorStatement
section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free GlobalTheory.CompanionTheory.WeilSiegel.HypStep GlobalTheory.CompanionTheory.WeilSiegel.HypStep.Unf
open GlobalTheory.CompanionTheory.SW.ThetaStage
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.frames_sum_by_first_vector : ∀ (F E : Type) [Field F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) (M : ℕ) (J : Matrix (Fin M) (Fin M) E) (n : ℕ) (f : (Fin (n + 1) → Fin (M + 2) → E) → ℝ≥0∞), ∑' X : framesOne σ J n, f X.1 = ∑' Y : framesE σ J (0 : Matrix (Fin n) (Fin n) E), ∑' a : Fin 1 → Fin n → E, f (consA a Y.1) := by
  first | exact @GlobalTheory.CompanionTheory.WeilSiegel.HypStep.Unf.FrOne.tsum_framesOne | exact GlobalTheory.CompanionTheory.WeilSiegel.HypStep.Unf.FrOne.tsum_framesOne | (intros; apply GlobalTheory.CompanionTheory.WeilSiegel.HypStep.Unf.FrOne.tsum_framesOne <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FramesSumInvariantUnderStabiliserStatement
section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free GlobalTheory.CompanionTheory.WeilSiegel.HypStep GlobalTheory.CompanionTheory.WeilSiegel.HypStep.Unf
open GlobalTheory.CompanionTheory.SW.ThetaStage
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.frames_sum_invariant_under_stabiliser : ∀ (F E : Type) [Field F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) (M : ℕ) (J : Matrix (Fin M) (Fin M) E) (n : ℕ) (w : UJ (σ : E →+* E) (hypOne J)), gact σ w (e0 E M) = e0 E M → ∀ f : (Fin (n + 1) → Fin (M + 2) → E) → ℝ≥0∞, ∑' X : framesOne σ J n, f (gact σ w X.1) = ∑' X : framesOne σ J n, f X.1 := by
  first | exact @GlobalTheory.CompanionTheory.WeilSiegel.HypStep.Unf.tsum_gact_framesOne | exact GlobalTheory.CompanionTheory.WeilSiegel.HypStep.Unf.tsum_gact_framesOne | (intros; apply GlobalTheory.CompanionTheory.WeilSiegel.HypStep.Unf.tsum_gact_framesOne <;> assumption)
end

