import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0044
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0045
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0008
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0010
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0009
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0007
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1165
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1142
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0730
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1257
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0005
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0288
import Development.AbelianVarietyTheory.Definitions.Divisors.DiagValExtTraceNonneg
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0001
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1258
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1235
import Development.AbelianVarietyTheory.Definitions.Divisors.NonemptyValExtOfOverLa
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1241
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0042
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0006
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0042
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0030
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0032
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FrameUniformEmbeddingSecond
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0076
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0082
import Development.AbelianVarietyTheory.Counterexamples.LevelGroupExamples.Bundle0004
import Development.AbelianVarietyTheory.Definitions.Divisors.IsIsoQuotToImOmegaLieOfSplit
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0030
import Formalism.LocalToGlobal.CMDeterminantIdeals.Bundle0001
import Formalism.PolynomialDimension.Bundle0001
import Formalism.SharpRestriction.GrowthBounds.HermitianTensor.Bundle0006
import Formalism.SharpRestriction.GrowthBounds.ScaleEdges.Bundle0007
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VecMulMapEqZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1278
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0003

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspidalLetterRealExponentEqZeroIffIsUnitary
section
open NumberField IsDedekindDomain MeasureTheory Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DiscSpec GlobalTheory.ResW GlobalTheory.Published
open scoped TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.ResW

theorem rexp_eq_zero_iff_isUnitary : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (x : Letter E), 1 ≤ x.1 → (rexp x = 0 ↔ x.2.IsUnitary) ∧ (x.2.IsUnitary ↔ (CG.mk x.2).IsUnitary) := by
  intro E _ _ _ x ha
  refine ⟨?_, (CG.isUnitary_mk _).symm⟩
  have hc : ∀ φ ∈ x.2.V, zc E x.1 φ = cex x • φ :=
    Classical.epsilon_spec (p := fun c : ℂ => ∀ φ ∈ x.2.V, zc E x.1 φ = c • φ)
      (by rw [zc_eq_scL]; exact Central.lie_scalar x.2 (1 : Cinf E))
  have hd : 0 < Module.finrank ℚ E := Module.finrank_pos
  have hpos : (0 : ℝ) < x.1 * Module.finrank ℚ E := by positivity
  have hz := (zc_comm_mem_eigen E x.1).2.2
  rw [rexp, div_eq_zero_iff, or_iff_left hpos.ne']
  constructor
  · intro h0
    have hne : (x.1 * (Module.finrank ℚ E : ℂ)) ≠ 0 := by exact_mod_cast hpos.ne'
    obtain ⟨χ, h1, -, h2, -⟩ := exists_abs_cpow E (-cex x / (x.1 * (Module.finrank ℚ E : ℂ)))
    have hre : (-cex x / (x.1 * (Module.finrank ℚ E : ℂ))).re = 0 := by
      rw [← Nat.cast_mul, Complex.div_natCast_re, Complex.neg_re, h0]; simp
    have hχ : χ.IsUnitary := fun y => by
      rw [h2, hre, nu, Model.eq_one_of_isAbsPow (GlobalTheory.HeckeGal.Model.absPow_isAbsPow E 0)]
      exact isUnitary_one y
    have hn : IsNormalised (x.2.twist χ) := by
      rintro _ ⟨φ, hφ, rfl⟩ t g
      have h3 : zc E x.1 (mulChi x.1 χ φ) = (0 : ℂ) • mulChi x.1 χ φ := by
        rw [h1, hc φ hφ, mul_div_cancel₀ _ hne, ← add_smul, add_neg_cancel, map_smul]
      simpa using (hz _ 0).1 h3 t g
    obtain ⟨ω, hω⟩ := Central.exists_hasCentral E x.1 x.2
    have h4 := ((hω.twist χ).isUnitary_iff.1 (GlobalTheory.SpehPair.isUnitary_of_isNormalised hn)).mul
      (isUnitary_pow hχ x.1).inv
    rw [mul_inv_cancel_right] at h4
    exact hω.isUnitary_iff.2 h4
  · intro hu
    obtain ⟨φ, hφ, h0⟩ := (Submodule.ne_bot_iff _).1 x.2.ne_bot
    obtain ⟨g, hg⟩ : ∃ g, φ.1 g ≠ 0 := Function.ne_iff.1 fun e => h0 (Subtype.ext e)
    have h1 := congrArg norm ((hz φ _).1 (hc φ hφ) 1 g)
    rw [splitCentre_eq_scalar, hu.norm_eq hφ, norm_mul, Complex.norm_exp] at h1
    have h2 := (mul_eq_right₀ (norm_ne_zero_iff.2 hg)).1 h1.symm
    simpa using h2

end GlobalTheory.ResW
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DdcExtensionTraceChernFormsStatement
section
open Matrix Complex ComplexConjugate Filter Topology
open scoped ComplexOrder ContDiff
open GlobalTheory.HermFrame GlobalTheory.IndefiniteRowSideFullHecke.HermitianCurvatureForms

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ddc_extension_trace_chern_forms : ∀ {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedSpace ℝ V] [IsScalarTower ℝ ℂ V] {m l : Type} [Fintype m] [Fintype l] [DecidableEq m] [DecidableEq l] {U : Set V} {H : V → Matrix (m ⊕ l) (m ⊕ l) ℂ} {z : V} (h : IsHermFrame U H) (hs : ∀ x ∈ U, IsUnit (subGram (H x)).det) (hz : z ∈ U) (hb : ∀ x ∈ U, ExtBlocksAt H x) (ξ₁ η₁ ξ₂ η₂ : V), ddcForm (extTrace H) z ξ₁ η₁ ξ₂ η₂ = chTwo (gramS H) z ξ₁ η₁ ξ₂ η₂ + chTwo (gramQ H) z ξ₁ η₁ ξ₂ η₂ - chTwo H z ξ₁ η₁ ξ₂ η₂ := by
  first | exact @GlobalTheory.SubQuotChTwo.ddcForm_extTrace_eq | exact GlobalTheory.SubQuotChTwo.ddcForm_extTrace_eq | (intros; apply GlobalTheory.SubQuotChTwo.ddcForm_extTrace_eq <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DefiniteFormStabilizerFiniteAwayFromPStatement
section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount
open scoped TensorProduct Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.definiteForm_stabilizer_finite_away_from_p : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p), G.a = 1 → ∀ (L : G.Level) (K' : Subgroup (Gr G 1)),
  Subgroup.Commensurable K' (KHT p G.m G.n 1 G.Fw) → ∀ (B : GlobalTheory.LKDef.DForm G) (x : G.GAf × Gr G 1),
    Finite (GlobalTheory.LKLoc.locPart B.emb.range (L.K.toSubgroup.prod K') x) := by
  first | (exact @GlobalTheory.DefStab.finite_locPart) | (exact GlobalTheory.DefStab.finite_locPart) | (intros; apply GlobalTheory.DefStab.finite_locPart  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DefiniteUnitaryLocalComponentMemIntegralGLCofiniStatement
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.definiteUnitaryLocalComponent_mem_integralGL_cofinite : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (y : UA E n), ∀ᶠ w in cofinite, cLoc w y ∈ GlobalTheory.LFun.KGL w n := by
  first | exact @GlobalTheory.BCT.SuppFin.cLoc_mem_KGL_cofinite | exact GlobalTheory.BCT.SuppFin.cLoc_mem_KGL_cofinite | (intros; apply GlobalTheory.BCT.SuppFin.cLoc_mem_KGL_cofinite <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DetFactorDepthEqChartValueAndSumStatement
section
open AlgebraicGeometry CategoryTheory NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.CharDepth GlobalTheory.FactorDepth
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.detFactorDepth_eq_chart_value_and_sum : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), letI := H.starRing; ∀ (p : ℕ) [Fact p.Prime] (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (Ch : IntegralChartA3 Xo c T io y) (X : ValExt T p), (∀ (f : Lt1 Dw) (k : ℕ), nuFac p y f k = nuFacC Ch X f k) ∧ ∀ cx : Lt1 Dw → ℕ, nuProd p y cx = nuP p y cx := by
  first | exact @GlobalTheory.FactorDepth.nuFac_eq_nuFacC_and_nuProd_eq_nuP | exact GlobalTheory.FactorDepth.nuFac_eq_nuFacC_and_nuProd_eq_nuP | (intros; apply GlobalTheory.FactorDepth.nuFac_eq_nuFacC_and_nuProd_eq_nuP <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DetTwistedSylvesterSqMulDetPowEqResultantSqStatement
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.det_twistedSylvester_sq_mul_det_pow_eq_resultant_sq : ∀ (k : Type) [Field k] (a b : ℕ) (A : GL (Fin a) k) (B : Matrix (Fin b) (Fin b) k), LinearMap.det (GlobalTheory.LeviDesc.adL A B) ^ 2 * A.val.det ^ (2 * b) = resultant A.val.charpoly B.charpoly ^ 2 := by
  first | exact @GlobalTheory.LeviDesc.det_adL_sq_mul_det_pow | exact GlobalTheory.LeviDesc.det_adL_sq_mul_det_pow | (intros; apply GlobalTheory.LeviDesc.det_adL_sq_mul_det_pow <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DictionaryComponentFrameMarkingUniformisation
section
namespace GlobalTheory.AdTh.MarkUniq

section Geo

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

theorem isDerivAt0_comp_lin {g g' : ℕ} {X : Scheme.{0}} {e : (Fin g → ℂ) → (Sp ℂ ⟶ X)}
    (he : IsHolTo Set.univ e) (L : (Fin g' → ℂ) →ₗ[ℂ] (Fin g → ℂ)) {w : Fin g' → ℂ}
    {v : Sp (DualNumber ℂ) ⟶ X} (h : IsDerivAt0 (fun z => e (L z)) w v) : IsDerivAt0 e (L w) v := by
  have h0 : spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ v = e 0 := by simpa only [map_zero] using h.1
  refine ⟨h0, fun U hU f => (h.2 U hU f).trans ?_⟩
  have hmem : (0 : Fin g → ℂ) ∈ {b ∈ (Set.univ : Set (Fin g → ℂ)) | ⊤ ≤ e b ⁻¹ᵁ U} := by
    refine ⟨trivial, ?_⟩
    rw [← h0]
    intro x _
    exact hU (Set.mem_univ _)
  have hd : DifferentiableAt ℂ (fun z => valAt' (e z) U f) 0 :=
    ((he U f).2 0 hmem).differentiableAt ((he U f).1.mem_nhds hmem)
  let L' := LinearMap.toContinuousLinearMap L
  have hd' : HasFDerivAt (fun z => valAt' (e z) U f) (fderiv ℂ (fun z => valAt' (e z) U f) 0) (L' 0) := by
    rw [map_zero]; exact hd.hasFDerivAt
  exact DFunLike.congr_fun (hd'.comp (0 : Fin g' → ℂ) L'.hasFDerivAt).fderiv w

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {s : KA l →+* ℂ} {g g' : ℕ} {ty : Fin g → (E →+* ℂ)} {ty' : Fin g' → (E →+* ℂ)}

theorem ex_eq (F : FamilyUnif Xo s ty') (i : Fin F.n) (P : (F.Di i).La →+ (Fin g' → ℂ)) (hP : IsPeriod (F.Di i) ty' P)
    (ex : (Fin g → ℂ) → (Over.mk (F.u i P) ⟶ Xo.univ.t.G)) (hadd : ∀ z w, ex (z + w) = ex z * ex w)
    (hol : IsHolTo Set.univ (fun z => (ex z).left)) (R : (Fin g → ℂ) →ₗ[ℂ] (Fin g' → ℂ))
    (v : ∀ j : Fin g, epsPt (F.u i P) ⟶ Xo.univ.t.G)
    (h1 : ∀ j, IsDerivAt0 (fun z => (ex z).left) (Pi.single j 1) (v j).left)
    (h2 : ∀ j, IsDerivAt0 (fun z => (F.ex i P z).left) (R (Pi.single j 1)) (v j).left) (z : Fin g → ℂ) :
    F.ex i P (R z) = ex z := by
  have dk : DiscreteTopology {z // F.ex i P z = 1} := by
    have h0 : (fun z => F.ex i P z = 1) = fun z => z ∈ P.range := funext fun z => propext (F.ex_ker i P hP z)
    show DiscreteTopology (Subtype fun z => F.ex i P z = 1)
    rw [h0]
    exact hP.2.2.1
  have hol' := GlobalTheory.ExpChain.isHolTo_ex F i P hP
  obtain ⟨f, hf, -⟩ := existsUnique_linear_lift_fibre Xo.X Xo.X Xo.univ.t.G Xo.univ.t.G _ _ g g' ex (F.ex i P) (𝟙 _)
    (MonoidHom.id _) Xo.univ.t.semi.smooth hadd (F.ex_add i P hP) hol hol' (F.ex_diff i P hP) dk (Category.id_comp _)
    (fun x => Category.comp_id _)
  have hf : ∀ z, F.ex i P (f z) = ex z := hf
  have hfR : f = R := by
    refine LinearMap.pi_ext' fun j => LinearMap.ext_ring ?_
    show f (Pi.single j 1) = R (Pi.single j 1)
    have h3 : IsDerivAt0 (fun z => (F.ex i P z).left) (f (Pi.single j 1)) (v j).left :=
      isDerivAt0_comp_lin hol' f (by simpa only [hf] using h1 j)
    exact ((F.ex_diff i P hP).2 (v j) (h2 j).1).unique h3 (h2 j)
  rw [← hfR, hf]

theorem exists_transport (F : FamilyUnif Xo s ty) (i : Fin F.n) (P : (F.Di i).La →+ (Fin g → ℂ))
    (hP : IsPeriod (F.Di i) ty P) (x0 : Sp ℂ ⟶ Xo.X) (h : x0 = F.u i P) :
    ∃ ex : (Fin g → ℂ) → (Over.mk x0 ⟶ Xo.univ.t.G),
      (∀ z, (ex z).left = (F.ex i P z).left) ∧ (∀ z w, ex (z + w) = ex z * ex w) ∧
      (∀ w, ∃ v : epsPt x0 ⟶ Xo.univ.t.G, IsDerivAt0 (fun z => (F.ex i P z).left) w v.left) ∧
      ∀ a ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) Dw.La),
        toUnit _ ≫ Xo.univ.eta a = ex ((l.M : ℂ)⁻¹ • P (F.t i a)) := by
  subst h
  exact ⟨F.ex i P, fun _ => rfl, F.ex_add i P hP, fun w => ((F.ex_diff i P hP).1 w).exists, F.ex_eta i P hP⟩

theorem mark_congr {J : Type} (e : Fin g ≃ J) (e' : Fin g' ≃ J) (F : FamilyUnif Xo s ty) (F' : FamilyUnif Xo s ty')
    (i : Fin F.n) (i' : Fin F'.n) (P : (F.Di i).La →+ (Fin g → ℂ)) (P' : (F'.Di i').La →+ (Fin g' → ℂ))
    (hP : IsPeriod (F.Di i) ty P) (hP' : IsPeriod (F'.Di i') ty' P') (x : Sp ℂ ⟶ Xo.X) (hx : x = F.u i P)
    (hx' : x = F'.u i' P') (u : J → (Sp (DualNumber ℂ) ⟶ Xo.univ.t.G.left))
    (hu : ∀ j, u j ≫ Xo.univ.t.G.hom = spMap (algebraMap ℂ (DualNumber ℂ)) ≫ x)
    (h1 : ∀ j, IsDerivAt0 (fun z => (F.ex i P z).left) (Pi.single (e.symm j) 1) (u j))
    (h2 : ∀ j, IsDerivAt0 (fun z => (F'.ex i' P' z).left) (Pi.single (e'.symm j) 1) (u j))
    (gam : (F.Di i).La → (F'.Di i').La) (hg : ∀ a j, P' (gam a) j = P a (e.symm (e' j))) :
    ∀ a ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) Dw.La),
      ∃ b, gam (F.t i a) = F'.t i' a + l.M • b := by
  classical
  intro a ha
  subst hx'
  obtain ⟨ex, hl, hadd, -, heta⟩ := exists_transport F i P hP _ hx
  have hl' : (fun z => (ex z).left) = fun z => (F.ex i P z).left := funext hl
  let R : (Fin g → ℂ) →ₗ[ℂ] (Fin g' → ℂ) := LinearMap.funLeft ℂ ℂ fun j => e.symm (e' j)
  have hR : ∀ j, R (Pi.single j 1) = Pi.single (e'.symm (e j)) 1 := fun j => by
    funext k
    show (Pi.single j (1 : ℂ) : Fin g → ℂ) (e.symm (e' k)) = _
    simp only [Pi.single_apply, Equiv.symm_apply_eq, Equiv.eq_symm_apply]
  have key := ex_eq F' i' P' hP' ex hadd (by rw [hl']; exact GlobalTheory.ExpChain.isHolTo_ex F i P hP) R
    (fun j => Over.homMk (u (e j)) (hu _))
    (fun j => by rw [hl']; have := h1 (e j); rw [Equiv.symm_apply_apply] at this; exact this)
    (fun j => by rw [hR]; exact h2 (e j))
  have h3 : F'.ex i' P' ((l.M : ℂ)⁻¹ • P' (gam (F.t i a))) = F'.ex i' P' ((l.M : ℂ)⁻¹ • P' (F'.t i' a)) := by
    rw [← F'.ex_eta i' P' hP' a ha, heta a ha, ← key, map_smul]
    congr 2
    exact funext (hg _)
  have h4 : F'.ex i' P' ((l.M : ℂ)⁻¹ • P' (gam (F.t i a)) - (l.M : ℂ)⁻¹ • P' (F'.t i' a)) = 1 := by
    have h5 := F'.ex_add i' P' hP' ((l.M : ℂ)⁻¹ • P' (gam (F.t i a)) - (l.M : ℂ)⁻¹ • P' (F'.t i' a))
      ((l.M : ℂ)⁻¹ • P' (F'.t i' a))
    rw [sub_add_cancel, h3] at h5
    exact (mul_eq_right.1 h5.symm)
  obtain ⟨b, hb⟩ := (F'.ex_ker i' P' hP' _).1 h4
  have hM : (l.M : ℂ) ≠ 0 := by have := l.three_le; exact Nat.cast_ne_zero.2 (by omega)
  refine ⟨b, hP'.2.1 ?_⟩
  rw [map_add, map_nsmul, hb, ← smul_sub, ← Nat.cast_smul_eq_nsmul ℂ, smul_inv_smul₀ hM, add_sub_cancel]

end Geo

end GlobalTheory.AdTh.MarkUniq

open NumberField Matrix Complex MeasureTheory IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct Classical ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.AdTh.MarkUniq

theorem realM_mt {D : D7} {θ : InfFam D} (hθ : IsInfFam θ) (W : HSp D) (h : GA D W) (τ : D.host.E →+* ℂ)
    (hτ : ∃ ρ, τ = tauE D ρ) (t : Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ) (ht : IsInfEmb τ t) :
    realM θ (Formalism.L2.Theta.mt W h) τ = archM W t h := by
  have e : θ hτ.choose = t := GlobalTheory.LettersCheck.isInfEmb_unique τ _ _ (by
    have := hθ hτ.choose
    rwa [← hτ.choose_spec] at this) ht
  rw [realM, dif_pos hτ, ← e]
  rfl

theorem finVec_congr {D : D7} (W : HSp D) (N : ℕ) (p m q : Fin W.rank → D.host.E)
    (y w : Fin W.rank → Af D.host.F ⊗[D.host.F] D.host.E) (h : p = m + N • q) (ew : finVec W p - y = N • w) :
    finVec W m - y = N • (w - finVec W q) := by
  funext i
  have e1 := congrFun ew i
  have e2 : finVec W p i = finVec W m i + N • finVec W q i := by
    rw [h]
    exact (map_add (TensorProduct.mk D.host.F (Af D.host.F) D.host.E 1) _ _).trans
      (congrArg _ (map_nsmul (TensorProduct.mk D.host.F (Af D.host.F) D.host.E 1) _ _))
  simp only [Pi.sub_apply, Pi.smul_apply, nsmul_eq_mul] at e1 e2 ⊢
  rw [mul_sub, ← e1, e2]
  ring

theorem rat_eq_of_archM {D : D7} (W : HSp D) {γ γ' : GA D W} (hγ : γ ∈ GQ W) (hγ' : γ' ∈ GQ W) (τ : D.host.E →+* ℂ)
    (t : Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ) (ht : IsInfEmb τ t) (h : archM W t γ = archM W t γ') : γ = γ' := by
  have key : ∀ δ : GA D W, ∀ δ₀ : GL (Fin W.rank) D.host.E,
      (∀ i j, (matHom W δ).1 i j = (1 : AF D.host.F) ⊗ₜ δ₀.1 i j) → ∀ i j, archM W t δ i j = τ (δ₀.1 i j) := by
    intro δ δ₀ he i j
    change t (Algebra.TensorProduct.map (fstA D.host.F) (AlgHom.id D.host.F D.host.E) ((matHom W δ).1 i j)) = _
    rw [he, Algebra.TensorProduct.map_tmul, map_one]
    exact ht.1 _
  obtain ⟨δ₀, -, he⟩ := hγ
  obtain ⟨δ₁, -, he'⟩ := hγ'
  have h0 : ∀ i j, (matHom W γ).1 i j = (1 : AF D.host.F) ⊗ₜ δ₀.1 i j := fun i j =>
    (congrArg (fun x : GL (Fin W.rank) (AF D.host.F ⊗[D.host.F] D.host.E) => x.1 i j) he).symm
  have h1 : ∀ i j, (matHom W γ').1 i j = (1 : AF D.host.F) ⊗ₜ δ₁.1 i j := fun i j =>
    (congrArg (fun x : GL (Fin W.rank) (AF D.host.F ⊗[D.host.F] D.host.E) => x.1 i j) he').symm
  refine Subtype.ext (Units.ext (Matrix.ext fun i j => ?_))
  refine (h0 i j).trans (Eq.trans ?_ (h1 i j).symm)
  rw [τ.injective ((key γ δ₀ h0 i j).symm.trans ((congrFun (congrFun h i) j).trans (key γ' δ₁ h1 i j)))]

end GlobalTheory.AdTh.MarkUniq

open GlobalTheory.AdTh.MarkUniq in
set_option maxHeartbeats 1000000 in

theorem GlobalTheory.AdTh.dict_atComp_markAd : ∀ (D : D7) (H : Geo.Tor.Host D.host.E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (r : ℕ) (U : Unf Xo c σ r), GoodEmb c σ → IsUnf U → 1 ≤ r → l.A = 1 → ∀ (θ : InfFam D) (W : HSp D) (hr : W.rank = r) (dict : GA D W → Σ k, Frame (U.X k).Ψ r) (ι : Dw.La →ₗ[𝓞 D.host.E] (Fin W.rank → D.host.E)) (g : ℕ) (e : Fin g ≃ Σ τ : D.host.E →+* ℂ, Fin (Dw.mult τ)) (F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (fun j => relab c σ (e j).1)) (ik : U.Comp → Fin F.n) (φ : ∀ k, (F.Di (ik k)).La ≃ₗ[𝓞 D.host.E] (U.X k).Λ) (th : ∀ k, (U.X k).Ψ → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (x₀ : (D.host.E →+* ℂ) → Matrix (Fin r) (Fin r) ℂ), IsInfFam θ → (∀ k, IsMod W hr (U.X k)) → (∀ k, IsOrthogonalFrame (U.X k) x₀) → (∀ k τ, IsInfEmb τ.1 (th k τ)) → DictLat U W hr dict ι e F ik φ th x₀ → ∀ (Wt : UW (Formalism.L2.PjFree.Unf.ofPj U)) (h : GA D W), IsONFr (U.X (dict h).1) (dict h).2 ∧ ∃ γ, AtComp θ W hr U.X dict x₀ h γ ∧ MarkAd l W hr ι (γ * h) (Wt.mark (dict h).1) ∧ ∀ γ', AtComp θ W hr U.X dict x₀ h γ' → γ' = γ := by
  intro D H Dw l Xo c σ r U hσ hU hr1 hA θ W hr dict ι g e F ik φ th x₀ hθ hMod hx₀ hth hD Wt h
  subst hr
  obtain ⟨γ, hγ, hΛ, hm, hfr⟩ := hD.2 h
  obtain ⟨θ', hθ'⟩ := (GlobalTheory.Member.infiniteAdele_bijective D).1
  obtain ⟨hAr, -, -⟩ := GlobalTheory.T.archimedeanMatrix_unitary_continuous_multiplicative D W θ' hθ'
  generalize hk : dict h = kx at hΛ hm hfr
  obtain ⟨k, x⟩ := kx
  dsimp only at hΛ hm hfr ⊢
  have hG : (U.X k).Gm = -W.gramᵀ := (hMod k).model.1
  obtain ⟨-, hu2, hu3⟩ := GlobalTheory.UnitFrames.unit_frame_eq_orthonormal_mul_triangular D.host.E W.rank (U.X k).p0
    (U.X k).Ψ (U.X k).Gm (U.X k).Gm_herm
  have hfr' : ∀ τ : (U.X k).Ψ, mat x τ = archM W (θ' τ.1) (γ * h) * x₀ τ.1 := fun τ => by
    rw [hfr τ, GlobalTheory.LettersCheck.isInfEmb_unique τ.1 _ _ (hth k τ) (hθ' τ.1)]
    rfl
  have hmove : ∀ (γ' : GA D W) (τ : (U.X k).Ψ),
      mat (frMove θ W rfl (U.X k) γ' (fun τ => x₀ τ.1)) τ = archM W (θ' τ.1) γ' * x₀ τ.1 := fun γ' τ => by
    rw [← realM_mt hθ W γ' τ.1 (((hMod k).psi τ.1).1 τ.2) _ (hθ' τ.1)]
    rfl
  have hON : IsONFr (U.X k) x := fun τ => by
    rw [hfr', hu3 τ.1 _ _ (by rw [hG]; exact (hAr τ.1).2.2.2.2 _)]
    exact hx₀ k τ.1 τ.2
  have hdom : x ∈ (U.X k).dom := (hu2 x hON).1
  have hmem : ∀ v, v ∈ (U.X k).Λ ↔ v ∈ latG W (γ * h) := fun v => by
    rw [← SetLike.mem_coe, hΛ]
    exact Set.ext_iff.1 (Set.image_id _) v
  refine ⟨hON, γ, ?_, ?_, ?_⟩
  · unfold AtComp
    rw [hk]
    refine ⟨hγ, SetLike.coe_injective hΛ.symm, funext fun τ => ?_⟩
    exact (hfr' τ).trans (hmove _ τ).symm
  · intro a ha
    obtain ⟨P, hPe, hP, hy, hd⟩ := hD.1.2 k ⟨x, hdom⟩
    obtain ⟨P', hPe', hP', hy', hd', -⟩ := Wt.pt k ⟨x, hdom⟩
    have hφ : ∀ v, Wt.φ k ((Wt.φ k).symm v) = v := (Wt.φ k).apply_symm_apply
    obtain ⟨b, hb⟩ := mark_congr e Wt.e F Wt.F (ik k) (Wt.ik k) P P' hP hP' _ hy hy'
      (fun j => (U.un k ⟨x, hdom⟩).u j.1 j.2) (fun j => ((U.un k ⟨x, hdom⟩).tan j.1 j.2).1)
      (fun j => hd j.1 j.2) (fun j => hd' j.1 j.2) (fun a => (Wt.φ k).symm (φ k a)) (fun a j => by
        rw [hPe, hPe', Equiv.apply_symm_apply]
        exact congrArg (fun v : (U.X k).Λ => perFr (U.X k) x (v : Fin W.rank → D.host.E) _ _) (hφ (φ k a))) a ha
    obtain ⟨w, hw, ew⟩ := hm a ha
    have hb' : (φ k (F.t (ik k) a) : Fin W.rank → D.host.E) =
        Wt.mark k a + l.M • (Wt.φ k b : Fin W.rank → D.host.E) := by
      have := congrArg (fun z => (Wt.φ k z : Fin W.rank → D.host.E)) hb
      simp only [map_add, map_nsmul] at this
      exact (congrArg Subtype.val (hφ _)).symm.trans this
    refine ⟨w - finVec W (Wt.φ k b : Fin W.rank → D.host.E), sub_mem hw
      (((GlobalTheory.MarkCoset.latG_spec D W _).1 _).1 ((hmem _).1 (Wt.φ k b).2)), ?_⟩
    exact finVec_congr W l.M _ _ _ _ _ hb' ew
  · intro γ' hγ'
    unfold AtComp at hγ'
    rw [hk] at hγ'
    obtain ⟨hq, -, hx⟩ := hγ'
    obtain ⟨τ₀⟩ : Nonempty (D.host.E →+* ℂ) := inferInstance
    obtain ⟨τ, hτ⟩ : ∃ τ, τ ∈ (U.X k).Ψ := by
      by_cases h : ComplexEmbedding.conjugate τ₀ ∈ (U.X k).Ψ
      · exact ⟨_, h⟩
      · exact ⟨τ₀, ((U.X k).cmType τ₀).2 h⟩
    have h1 : archM W (θ' τ) (γ' * h) * x₀ τ = archM W (θ' τ) (γ * h) * x₀ τ := by
      rw [← hmove _ ⟨τ, hτ⟩, ← hfr' ⟨τ, hτ⟩]
      exact congrArg (fun y => mat y ⟨τ, hτ⟩) hx.symm
    have hdet : IsUnit (x₀ τ).det :=
      (((hu2 (fun τ => x₀ τ.1) fun τ => hx₀ k τ.1 τ.2).1 ⟨τ, hτ⟩).1).isUnit
    have h2 : archM W (θ' τ) (γ' * h) = archM W (θ' τ) (γ * h) := by
      have := congrArg (· * (x₀ τ)⁻¹) h1
      simpa only [Matrix.mul_nonsing_inv_cancel_right _ _ hdet] using this
    refine rat_eq_of_archM W hq hγ τ _ (hθ' τ) ?_
    have h3 : ∀ δ : GA D W, archM W (θ' τ) δ = archM W (θ' τ) (δ * h) * archM W (θ' τ) h⁻¹ := fun δ => by
      rw [← (hAr τ).2.1, mul_inv_cancel_right]
    rw [h3 γ', h3 γ, h2]
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualNumberSpecAffineOpenFunctionsBijectiveStatement
section
open CategoryTheory AlgebraicGeometry MonoidalCategory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Pdiv GlobalTheory.LieVB
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dualNumberSpec_affineOpen_functions_bijective : ∀ (O : Type) [CommRing O] (V : (Sp O).Opens), IsAffineOpen V → Function.Bijective (fun ab : Γ(Sp O, V) × Γ(Sp O, V) => (specO O (DualNumber O)).hom.appLE V ((specO O (DualNumber O)).hom ⁻¹ᵁ V) le_rfl ab.1 + (specO O (DualNumber O)).hom.appLE V ((specO O (DualNumber O)).hom ⁻¹ᵁ V) le_rfl ab.2 * resG _ le_top (epsFn O)) := by
  first | exact @GlobalTheory.LieVB.bijective_add_mul_epsFn | exact GlobalTheory.LieVB.bijective_add_mul_epsFn | (intros; apply GlobalTheory.LieVB.bijective_add_mul_epsFn <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualWeylDimFormulaDualityBound
section
open NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.DualWeyl GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.DefPt MvPolynomial
open scoped Matrix

namespace GlobalTheory.WeylDimBound

theorem dim_eq_weylDim (n : ℕ) (la : Fin n → ℕ) (hla : Antitone la) :
    (GlobalTheory.DualWeyl.dim la : ℚ) = Formalism.CountingSumsFrames.weylDim n (fun i => (la i : ℤ)) :=
  Formalism.MainNotions.flipOneThree.Pf.pb_finrank ℂ n la hla

theorem dim_dual (n : ℕ) (la : Fin n → ℕ) (hla : Antitone la) (s : ℕ) (hs : ∀ i, la i ≤ s) :
    GlobalTheory.DualWeyl.dim (fun i => s - la (Fin.rev i)) = GlobalTheory.DualWeyl.dim la := by
  have hanti : Antitone (fun i : Fin n => s - la (Fin.rev i)) := by
    intro i j hij
    have := hla (Fin.rev_le_rev.mpr hij)
    dsimp only
    omega
  have h1 := dim_eq_weylDim n _ hanti
  have h2 := dim_eq_weylDim n la hla
  have h3 : Formalism.CountingSumsFrames.weylDim n (fun i => (((s - la (Fin.rev i) : ℕ)) : ℤ)) =
      Formalism.CountingSumsFrames.weylDim n (fun i => (la i : ℤ)) := by
    have e : (fun i : Fin n => (((s - la (Fin.rev i) : ℕ)) : ℤ)) =
        fun i => -((fun k => (la k : ℤ)) i.rev) + (s : ℤ) := by
      funext i
      rw [Nat.cast_sub (hs _)]
      ring
    rw [e, Formalism.MainNotions.Pf14.weylDim_shift n (fun i => -((fun k => (la k : ℤ)) i.rev)) (s : ℤ)]
    exact Formalism.MainNotions.Pf14.weylDim_dual n (fun k => (la k : ℤ))
  exact_mod_cast h1.trans (h3.trans h2.symm)

theorem sum_card_lt (n : ℕ) : ∑ i : Fin n, (Finset.univ.filter fun j : Fin n => i < j).card = n.choose 2 := by
  have h1 : ∀ i : Fin n, (Finset.univ.filter fun j : Fin n => i < j).card = n - 1 - i := by
    intro i
    rw [← Fin.card_Ioi]
    congr 1
    ext j
    simp
  simp only [h1]
  rw [Fin.sum_univ_eq_sum_range (fun k => n - 1 - k) n, Finset.sum_range_reflect (fun k => k) n,
    Finset.sum_range_id, Nat.choose_two_right]

theorem prod_ite_lt (n : ℕ) (c : ℝ) :
    ∏ i : Fin n, ∏ j : Fin n, (if i < j then c else 1) = c ^ n.choose 2 := by
  simp only [Finset.prod_ite, Finset.prod_const, one_pow, mul_one]
  rw [Finset.prod_pow_eq_pow_sum, sum_card_lt]

theorem weylDim_le (n : ℕ) (la : Fin n → ℕ) (hla : Antitone la) (w : ℤ) :
    ((Formalism.CountingSumsFrames.weylDim n (fun i => (la i : ℤ)) : ℚ) : ℝ) ≤ ((∑ i, |((la i : ℤ) : ℝ) - w|) + 1) ^ n.choose 2 := by
  set S := ∑ i, |((la i : ℤ) : ℝ) - w| with hS
  have hcast : ((Formalism.CountingSumsFrames.weylDim n (fun i => (la i : ℤ)) : ℚ) : ℝ) = ∏ i : Fin n, ∏ j : Fin n,
      (if i < j then (((la i : ℝ) - la j) + ((j : ℕ) : ℝ) - ((i : ℕ) : ℝ)) / (((j : ℕ) : ℝ) - ((i : ℕ) : ℝ)) else 1) := by
    unfold Formalism.CountingSumsFrames.weylDim
    rw [Rat.cast_prod]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [Rat.cast_prod]
    refine Finset.prod_congr rfl fun j _ => ?_
    split_ifs <;> push_cast <;> ring
  have hpair : ∀ i j : Fin n, i ≠ j → |((la i : ℤ) : ℝ) - w| + |((la j : ℤ) : ℝ) - w| ≤ S := by
    intro i j hij
    rw [← Finset.sum_pair (f := fun k => |((la k : ℤ) : ℝ) - w|) hij]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun k _ _ => abs_nonneg _
  rw [hcast, ← prod_ite_lt]
  refine Finset.prod_le_prod (fun i _ => Finset.prod_nonneg fun j _ => ?_)
    fun i _ => Finset.prod_le_prod (fun j _ => ?_) fun j _ => ?_
  · split_ifs with hij
    · have hd : ((i : ℕ) : ℝ) + 1 ≤ ((j : ℕ) : ℝ) := by exact_mod_cast (Fin.lt_def.mp hij)
      have ha : (la j : ℝ) ≤ la i := by exact_mod_cast hla hij.le
      exact div_nonneg (by linarith) (by linarith)
    · exact zero_le_one
  · split_ifs with hij
    · have hd : ((i : ℕ) : ℝ) + 1 ≤ ((j : ℕ) : ℝ) := by exact_mod_cast (Fin.lt_def.mp hij)
      have ha : (la j : ℝ) ≤ la i := by exact_mod_cast hla hij.le
      exact div_nonneg (by linarith) (by linarith)
    · exact zero_le_one
  · split_ifs with hij
    · have hd : ((i : ℕ) : ℝ) + 1 ≤ ((j : ℕ) : ℝ) := by exact_mod_cast (Fin.lt_def.mp hij)
      have ha : (la j : ℝ) ≤ la i := by exact_mod_cast hla hij.le
      have hp := hpair i j hij.ne
      have h1 := le_abs_self (((la i : ℤ) : ℝ) - w)
      have h2 := neg_abs_le (((la j : ℤ) : ℝ) - w)
      push_cast at hp h1 h2
      rw [div_le_iff₀ (by linarith)]
      nlinarith
    · exact le_rfl

theorem dim_weyl_dual_bound : ∀ (n : ℕ) (la : Fin n → ℕ), Antitone la →
    (dim la : ℚ) = Formalism.CountingSumsFrames.weylDim n (fun i => (la i : ℤ)) ∧
      (∀ s : ℕ, (∀ i, la i ≤ s) → dim (fun i => s - la (Fin.rev i)) = dim la) ∧
      ∀ w : ℤ, (dim la : ℝ) ≤ ((∑ i, |((la i : ℤ) : ℝ) - w|) + 1) ^ n.choose 2 := by
  intro n la hla
  refine ⟨dim_eq_weylDim n la hla, fun s hs => dim_dual n la hla s hs, fun w => ?_⟩
  have h : (dim la : ℝ) = ((dim la : ℚ) : ℝ) := (Rat.cast_natCast _).symm
  rw [h, dim_eq_weylDim n la hla]
  exact weylDim_le n la hla w

end GlobalTheory.WeylDimBound
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EigenbasisBaseChangeStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.CM GlobalTheory.FlatDegreeCompare
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eigenbasis_base_change : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (k k' : Type) [Field k] [NumberField k] [Field k'] [NumberField k'] (i : k →+* k') (t : SAB H (Sp k)) (t' : SAB H (Sp k')) (n : SABMap t' t (spMap i)) (m : ℕ) (x : Fin m → (epsR k ⟶ t.G)) (x' : Fin m → (epsR k' ⟶ t'.G)) (χ : 𝓞 E →+* k), (∀ a, IsVecOver i n.φ (x a) (x' a)) → EigenvectorLieDegree.IsEigBasis t.act χ x → EigenvectorLieDegree.IsEigBasis t'.act (i.comp χ) x' := by
  first | exact @GlobalTheory.EigBasisExtend.isEigBasis_extend | exact GlobalTheory.EigBasisExtend.isEigBasis_extend | (intros; apply GlobalTheory.EigBasisExtend.isEigBasis_extend <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EigenbasisSignatureExistsStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.CM GlobalTheory.FlatDegreeCompare
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eigenbasis_signature_exists : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (c : Coeff l) (k : Type) [Field k] [NumberField k] (j : c.F →+* k) (o : Obj D l (baseKA l) (spMap j ≫ spMap (IntermediateField.inclusion c.le).toRingHom)) (τ : E →+* ℂ), τ (H.rt : E) = H.rt0 → (∃ x : Fin D.p → (epsR k ⟶ o.t.G), EigenvectorLieDegree.IsEigBasis o.t.act ((EigenvectorLieDegree.embIn c j τ).comp (algebraMap (𝓞 E) E)) x) ∧ ∃ x : Fin D.q → (epsR k ⟶ o.t.G), EigenvectorLieDegree.IsEigBasis o.t.act ((EigenvectorLieDegree.embIn c j (conjEmb τ)).comp (algebraMap (𝓞 E) E)) x := by
  first | exact @GlobalTheory.EigBasisExist.exists_eigBases | exact GlobalTheory.EigBasisExist.exists_eigBases | (intros; apply GlobalTheory.EigBasisExist.exists_eigBases <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PropZStatementStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.prop_z_statement : GlobalTheory.IndefiniteRowSideFullHecke.SpecialFibreUnits.PropZ := by
  first | exact @GlobalTheory.PropZRow.propZ | exact GlobalTheory.PropZRow.propZ | (intros; apply GlobalTheory.PropZRow.propZ <;> assumption)
end

