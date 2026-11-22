import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0066
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0051
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0071
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0005
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0007
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2166
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2179
import Mathlib
import Development.AutomorphicArithmetic.FrobeniusLocalisation.Bundle0008
import Formalism.LocalRingCardinality.HostCls
import Development.AbelianVarietyTheory.Definitions.Divisors.NormNegCmConstantEqAtAllEmbeddings
import Formalism.LocalRingCardinality.Bundle0003
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0072
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Development.AbelianVarietyTheory.Definitions.Divisors.WedgeNrmLeOfWedgeNormLe
import Development.AbelianVarietyTheory.Definitions.Divisors.IsHomWeightHomWeight
import Development.AbelianVarietyTheory.Definitions.Divisors.MemLevEigenIffTransl
import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.RealCubicMeans.LogMeanShares.LogMeanStatements.Bundle0001
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0058
import Development.AbelianVarietyTheory.Definitions.Divisors.BadElt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2067
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1554
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2042
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2090
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.FiniteAndFinrankLeOfPointwise
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2174
import Development.AbelianVarietyTheory.Definitions.Foundations.CanonicalExponents
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ClausesIffExistsUnique
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0034
import Development.AbelianVarietyTheory.Definitions.Divisors.MulSmulIdemMem
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0022
import Development.AbelianVarietyTheory.Definitions.Divisors.IsHomogeneousCompIdeal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2167
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0064
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0093
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0087
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0078
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0029
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0005
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0014
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0042
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0006
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1529
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2057
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2169
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2184
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0049

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumOrdSubOneLeOrdWedgeDifferentials
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
open GlobalTheory.Discrepancy GlobalTheory.Cartier GlobalTheory.QCoh
open GlobalTheory.TopForm

namespace GlobalTheory.Discrepancy.DivOver

theorem sum_ord_sub_one_le_formOrd_dOn : ∀ {k : Type} [Field k] [PerfectField k] {X : Scheme.{0}} [IsIntegral X] {p : X ⟶ Sp k}
    [LocallyOfFiniteType p] {n : ℕ}, topologicalKrullDim X = n → ∀ (E : DivOver p) {U : X.Opens} {y : X}
    (hy : y ∈ U), E.Through y → ∀ (z : Fin n → Γ(X, U)), formOf U (gen_mem hy) (dOn p z) ≠ 0 →
    ∀ {J : Type} [Fintype J] (e : J → Fin n), Function.Injective e → ∀ (u : J → X.functionFieldˣ),
    (∀ j, (u j : X.functionField) = fnOf U (gen_mem hy) (z (e j))) →
    ∑ j, E.ord (u j) - 1 ≤ E.formOrd (formOf U (gen_mem hy) (dOn p z)) := by
  intro k _ _ X _ p _ n hn E U y hy hE z hz0 J _ e he u hu
  classical
  letI := (Cartier.constFn p).toAlgebra
  letI := E.const.toAlgebra
  haveI : IsScalarTower k E.ring X.functionField := IsScalarTower.of_algebraMap_eq' rfl
  let x : Fin n → X.functionField := fun i => fnOf U (gen_mem hy) (z i)
  have hxV : ∀ i, x i ∈ E.ring := fun i => hE _ (regAt_fnOf hy _ (z i))
  have hη : formOf U (gen_mem hy) (dOn p z) = dWedge k x := by
    change TopForm.formMap n _ _ (dForm _ z) = _
    rw [formMap_dForm]
    rfl
  obtain ⟨t, ht⟩ := IsDiscreteValuationRing.exists_irreducible E.ring
  have ht0 : algebraMap E.ring X.functionField t ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective E.ring X.functionField)).mpr ht.ne_zero
  let S : Finset (Fin n) := Finset.univ.map ⟨e, he⟩
  have hxe : ∀ j, x (e j) = (u j : X.functionField) := fun j => (hu j).symm
  have hxS : ∀ i ∈ S, x i ≠ 0 := by
    intro i hi
    obtain ⟨j, -, rfl⟩ := Finset.mem_map.1 hi
    change x (e j) ≠ 0
    rw [hxe j]
    exact (u j).ne_zero
  obtain ⟨γ, hγ⟩ := GlobalTheory.smul_dlogWedge_mem_regForms k t ht0 S x
    (fun i hi => exists_eq_unit_mul_zpow ht (hxS i hi)) (fun i _ => ⟨⟨x i, hxV i⟩, rfl⟩)
  obtain ⟨ω, hω⟩ := E.exists_isFreeGen hn
  obtain ⟨a, rfl⟩ := hω.2 γ
  have hbr : ∀ θ, GlobalTheory.formMap k E.ring X.functionField n θ = E.toRat n θ := fun _ => rfl
  have hP : (∏ i ∈ S, x i) = ∏ j, (u j : X.functionField) := by
    rw [Finset.prod_map]
    exact Finset.prod_congr rfl fun j _ => hxe j
  have hPne : (∏ i ∈ S, x i) ≠ 0 := Finset.prod_ne_zero_iff.2 hxS
  have h2 : dWedge k x = (∏ i ∈ S, x i) • dlogWedge k S x := by
    rw [GlobalTheory.dlogWedge_eq_smul, smul_smul, mul_inv_cancel₀ hPne, one_smul]
  have h3 : (algebraMap E.ring X.functionField t) • dlogWedge k S x =
      (algebraMap E.ring X.functionField a) • E.toRat n ω := by
    calc (algebraMap E.ring X.functionField t) • dlogWedge k S x = t • dlogWedge k S x :=
          algebraMap_smul _ t _
      _ = GlobalTheory.formMap k E.ring X.functionField n (a • ω) := hγ.symm
      _ = a • E.toRat n ω := by rw [map_smul, hbr]
      _ = (algebraMap E.ring X.functionField a) • E.toRat n ω := (algebraMap_smul _ a _).symm
  have key : formOf U (gen_mem hy) (dOn p z) =
      ((∏ i ∈ S, x i) * (algebraMap E.ring X.functionField t)⁻¹ *
        algebraMap E.ring X.functionField a) • E.toRat n ω := by
    rw [hη, h2, mul_assoc, mul_smul, mul_smul, ← h3, inv_smul_smul₀ ht0]
  have ha0 : algebraMap E.ring X.functionField a ≠ 0 := by
    intro h
    apply hz0
    rw [key, h, mul_zero, zero_smul]
  let f : X.functionFieldˣ := (∏ j, u j) * (Units.mk0 _ ht0)⁻¹ * Units.mk0 _ ha0
  have hf : formOf U (gen_mem hy) (dOn p z) = (f : X.functionField) • E.toRat n ω := by
    rw [key, hP]
    simp [f]
  have hsum : ∀ s : Finset J, E.ord (∏ j ∈ s, u j) = ∑ j ∈ s, E.ord (u j) := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp
    | insert j s hj ih => rw [Finset.prod_insert hj, Finset.sum_insert hj, E.ord_mul, ih]
  have hordt : E.ord (Units.mk0 _ ht0) = 1 :=
    (congrArg WithZero.log (Ring.ordFrac_irreducible (K := X.functionField) ht)).trans
      (WithZero.log_exp 1)
  have horda : 0 ≤ E.ord (Units.mk0 _ ha0) := (E.ord_nonneg_iff _).2 a.2
  rw [IsFormOrd.formOrd_eq hz0 ⟨ω, hω, f, hf, rfl⟩]
  simp only [f, E.ord_mul, E.ord_inv, hsum, hordt]
  omega

end GlobalTheory.Discrepancy.DivOver
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SupConstantLogBound
section
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct

namespace GlobalTheory.ConstSzRows

theorem supConst_size_rows : ∀ (D : D7) (M : ℕ) (Lb w : ℝ), 1 ≤ M → 1 ≤ Lb → Real.log M ≤ 30 * Lb → fieldSz D.host.E ≤ 3 * Lb → Real.log (D.R.f * D.R.r) ≤ Lb → 1 ≤ w → Real.log w ≤ 25 * Lb → 1 ≤ GlobalTheory.LevGeo.supConst D.host.E D.R.r D.host.d M w ∧ Real.log (GlobalTheory.LevGeo.supConst D.host.E D.R.r D.host.d M w) ≤ 4000 * ((D.R.f : ℝ) * D.R.r * Lb) ^ 3 := by
  intro D M Lb w hM hLb hMl hsz hfrl hw hwl
  haveI : IsCMField D.host.E := inferInstance
  have hfd := GlobalTheory.FramedCMPointCompare.fdeg_host D
  have hf0 : 1 ≤ D.R.f := by have : 0 < D.R.n := D.R.ord_pos; unfold Formalism.BasicNotions.Ranks.f; omega
  have hr2 : 2 ≤ D.R.r := by
    have := D.R.two_le_m; have := D.R.m_add_three_le_k; unfold Formalism.BasicNotions.Ranks.r; omega
  have hqd := D.host.qd_big
  have hd1 : 1 ≤ D.host.d := by omega
  have hq1 : 1 ≤ D.host.q := by omega
  have hfR : (1 : ℝ) ≤ D.R.f := by exact_mod_cast hf0
  have hrR : (1 : ℝ) ≤ D.R.r := by exact_mod_cast (by omega : 1 ≤ D.R.r)
  have hnR : (Module.finrank ℚ D.host.E : ℝ) = 2 * D.R.f := by exact_mod_cast D.host.finrank_E'
  have hnpos : (0 : ℝ) < Module.finrank ℚ D.host.E := by rw [hnR]; linarith
  have hrd := (GlobalTheory.CovTop.log_rd_le_fieldSz D.host.E).trans hsz
  have hld : Real.log |(discr D.host.E : ℝ)| ≤ 6 * D.R.f * Lb := by
    have h := (div_le_iff₀ hnpos).1 hrd
    rw [hnR] at h; linarith
  set L : ℝ := 25 * Lb / 2 with hL
  have hdE : Real.log (ReciprocityTheory.ChartRestriction.G.FD.dE D.host.E) ≤ 4 * (ReciprocityTheory.ChartRestriction.G.FD.fdeg D.host.E : ℝ) * L := by
    unfold ReciprocityTheory.ChartRestriction.G.FD.dE; rw [hfd]; nlinarith
  have hdpow : D.host.d ^ D.R.f ≤ (discr D.host.E).natAbs :=
    Nat.le_of_dvd (Nat.pos_of_ne_zero (Int.natAbs_ne_zero.2 (discr_ne_zero _))) (UpperTheory.HF.rad_bounds2 D.host.toHostAx).2.2.1
  have hdpowR : ((D.host.d : ℝ)) ^ D.R.f ≤ |(discr D.host.E : ℝ)| := by
    have : (((discr D.host.E).natAbs : ℕ) : ℝ) = |(discr D.host.E : ℝ)| := by
      rw [Nat.cast_natAbs, Int.cast_abs]
    rw [← this]; exact_mod_cast hdpow
  have hdR : (0 : ℝ) < D.host.d := by exact_mod_cast hd1
  have hlogd : Real.log D.host.d ≤ 4 * L := by
    have h1 := Real.log_le_log (by positivity) hdpowR
    rw [Real.log_pow] at h1
    have h3 : (D.R.f : ℝ) * Real.log D.host.d ≤ D.R.f * (6 * Lb) := by linarith
    have h4 := le_of_mul_le_mul_left h3 (by linarith)
    linarith
  have hlogfr : Real.log ((ReciprocityTheory.ChartRestriction.G.FD.fdeg D.host.E : ℝ) * D.R.r) ≤ L := by
    rw [hfd]; push_cast at hfrl; linarith
  have hmain := GlobalTheory.T.supremum_constant_log_bound D.host.E D.R.r D.host.d M w L hr2 hd1 hM (by linarith) hw hlogfr
    (by linarith) hdE hlogd (by linarith)
  refine ⟨hmain.1, hmain.2.trans ?_⟩
  rw [hfd]
  have hx : (1 : ℝ) ≤ (D.R.f : ℝ) * D.R.r := one_le_mul_of_one_le_of_one_le hfR hrR
  have h1 : ((D.R.f : ℝ) * D.R.r) ^ 2 * Lb ≤ ((D.R.f : ℝ) * D.R.r) ^ 3 * Lb ^ 3 :=
    mul_le_mul (pow_le_pow_right₀ hx (by norm_num)) (le_self_pow₀ hLb (by norm_num)) (by linarith) (by positivity)
  have h2 : (0 : ℝ) ≤ ((D.R.f : ℝ) * D.R.r) ^ 2 * Lb := by positivity
  calc 250 * (D.R.f : ℝ) ^ 2 * (D.R.r : ℝ) ^ 2 * L = 3125 * (((D.R.f : ℝ) * D.R.r) ^ 2 * Lb) := by rw [hL]; ring
    _ ≤ 4000 * (((D.R.f : ℝ) * D.R.r) ^ 3 * Lb ^ 3) := by linarith
    _ = 4000 * ((D.R.f : ℝ) * D.R.r * Lb) ^ 3 := by ring

end GlobalTheory.ConstSzRows
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SupLatticeRankEqSumComponentRanks
section
noncomputable section

namespace GlobalTheory.RankAdd

open NumberField IsDedekindDomain MeasureTheory Module ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.BasicNotions
  Formalism.BasicNotions.TH Formalism.L2.Theta GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.FlatTw GlobalTheory.IndefiniteRowSideFullHecke.ComponentMassSum

set_option synthInstance.maxHeartbeats 200000

theorem finrank_iSup_of_indep {R V ι : Type} [Field R] [AddCommGroup V] [Module R V] [FiniteDimensional R V]
    [Fintype ι] (S : ι → Submodule R V) (hS : iSupIndep S) :
    finrank R (⨆ i, S i : Submodule R V) = ∑ i, finrank R (S i) := by
  classical
  have key : ∀ s : Finset ι, finrank R (⨆ i ∈ s, S i : Submodule R V) = ∑ i ∈ s, finrank R (S i) := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp
    | insert a s ha ih =>
      rw [Finset.iSup_insert, Finset.sum_insert ha, ← ih]
      have hd : Disjoint (S a) (⨆ i ∈ s, S i) := hS.disjoint_biSup (y := (s : Set ι)) (by exact_mod_cast ha)
      have h := Submodule.finrank_sup_add_finrank_inf_eq (S a) (⨆ i ∈ s, S i)
      rw [hd.eq_bot, finrank_bot, add_zero] at h
      exact h
  have hu : (⨆ i ∈ (Finset.univ : Finset ι), S i) = ⨆ i, S i := iSup_congr fun i => iSup_pos (Finset.mem_univ i)
  rw [← hu]
  exact key Finset.univ

variable {D : D7} {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l}
  {c : Coeff l} {r : ℕ}

theorem rankOn_eq_finrank_span (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (Z : Comp Xo c) (G : WTZ D.host.E) :
    rankOn U Z G = finrank c.F (Submodule.span c.F (partLat U Z G : Set (cuspW Xo c U G))) := by
  have hset : (partLat U Z G : Set (cuspW Xo c U G)) =
      Submodule.inclusion (cuspOn_le U Z G) '' (latOn U Z G : Set (cuspOn U Z G)) := by
    simp [partLat]
  rw [hset, Submodule.span_image]
  exact (LinearEquiv.finrank_eq (Submodule.equivMapOfInjective _
    (Submodule.inclusion_injective (cuspOn_le U Z G)) _))

end GlobalTheory.RankAdd

namespace GlobalTheory.RankAdd

open NumberField IsDedekindDomain MeasureTheory Module ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.BasicNotions
  Formalism.BasicNotions.TH Formalism.L2.Theta GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.FlatTw GlobalTheory.IndefiniteRowSideFullHecke.ComponentMassSum

set_option synthInstance.maxHeartbeats 200000

theorem cuspOn_comap_indep {D : D7} {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E} {Dw : Datum H} {l : Level H}
    {Xo : Moduli Dw l} {c : Coeff l} {r : ℕ} (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (G : WTZ D.host.E) :
    iSupIndep (fun Z : Comp Xo c => (cuspOn U Z G).comap (cuspW Xo c U G).subtype) := fun Z => by
  rw [Submodule.disjoint_def]
  intro x hx hx'
  have hle : (⨆ (j) (_ : j ≠ Z), (cuspOn U j G).comap (cuspW Xo c U G).subtype) ≤
      LinearMap.ker ((LinearMap.mulLeft c.F (idem Z)).comp (cuspW Xo c U G).subtype) :=
    iSup₂_le fun j hj y hy => by
      rw [LinearMap.mem_ker, LinearMap.comp_apply, LinearMap.mulLeft_apply]
      exact GlobalTheory.CuspSplit.idem_mul_eq_zero (Ne.symm hj) (Submodule.mem_comap.1 hy)
  have h0 := hle hx'
  rw [LinearMap.mem_ker, LinearMap.comp_apply, LinearMap.mulLeft_apply] at h0
  apply Subtype.ext
  calc (x : Rul Xo c) = idem Z * x :=
        (GlobalTheory.CuspSplit.idem_mul_of_mem_cuspOn (Submodule.mem_comap.1 hx)).symm
    _ = 0 := h0

set_option maxHeartbeats 1000000 in

theorem rankW_eq_finsum_rankOn : ∀ (D : D7) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : Datum H) (l : Level H)
    (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (x : ℝ)
    (V : (c.F →+* ℂ) → HSp D) (dict : ∀ σ, GA D (V σ) → Σ k, Frame ((U σ).X k).Ψ r) (G : WTZ D.host.E),
    (∀ σ, GoodEmb c σ → IsUnf (U σ)) → GoodW U x V dict G → rankW U G = ∑ᶠ Z : Comp Xo c, rankOn U Z G := by
  intro D H Dw l Xo c r U x V dict G hU hG
  obtain ⟨-, -, -, hsup⟩ := GlobalTheory.CuspSplit.splits D H Dw l Xo c r U V dict hU G
  haveI := CompFin.finite_comp Xo c
  haveI := Fintype.ofFinite (Comp Xo c)

  obtain ⟨-, ⟨s, hs⟩, htop⟩ := hG
  haveI : FiniteDimensional c.F (cuspW Xo c U G) := by
    refine Module.Finite.of_fg_top ⟨s, ?_⟩
    rw [← htop, ← hs, Submodule.span_span_of_tower]
  set S : Comp Xo c → Submodule c.F (cuspW Xo c U G) :=
    fun Z => Submodule.span c.F (partLat U Z G : Set (cuspW Xo c U G)) with hSdef
  have hspan : Submodule.span c.F (latW U G : Set (cuspW Xo c U G)) = ⨆ Z, S Z := by
    apply le_antisymm
    · rw [Submodule.span_le, ← hsup]
      intro y hy
      have hle : (⨆ Z : Comp Xo c, partLat U Z G) ≤ (⨆ Z, S Z).restrictScalars (𝓞 c.F) :=
        iSup_le fun Z z hz => (le_iSup S Z) (Submodule.subset_span hz)
      exact hle hy
    · exact iSup_le fun Z => Submodule.span_mono (by rw [← hsup]; exact le_iSup (fun Z => partLat U Z G) Z)
  have hind : iSupIndep S := (cuspOn_comap_indep U G).mono fun Z =>
    Submodule.span_le.2 fun y hy => Submodule.mem_comap.2 (GlobalTheory.CuspSplit.coe_mem_of_mem_partLat hy)
  rw [finsum_eq_sum_of_fintype]
  show finrank c.F (Submodule.span c.F (latW U G : Set (cuspW Xo c U G))) = _
  rw [hspan, finrank_iSup_of_indep S hind]
  exact Finset.sum_congr rfl fun Z _ => (rankOn_eq_finrank_span U Z G).symm

end GlobalTheory.RankAdd
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TestValueEqConstMulReadingSecZ
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
set_option synthInstance.maxHeartbeats 400000

namespace GlobalTheory

section IntWeight

open Formalism.L2.Pj

variable {K : Type} [Field K] {ι : Type}
  {pts : ∀ (S : Type) [CommRing S] [Algebra K S], Type}
  {mapR : ∀ {S T : Type} [CommRing S] [Algebra K S] [CommRing T] [Algebra K T], (S →ₐ[K] T) → pts S → pts T → Prop}
  {borR : ∀ {S : Type} [CommRing S] [Algebra K S], (ι → Sˣ) → pts S → pts S → Prop}

theorem evalAt_borR_of_borChart_int [Fintype ι] (h : BorChart pts mapR borR) (e : ι → ℤ) {f : Rules pts}
    (hf : IsNatural pts mapR f)
    (hw : ∀ (p : TRing K) (t : ι → (p.R)ˣ) (y y' : pts p.R), borR t y y' →
      f p y' = ((∏ i, t i ^ e i : (p.R)ˣ) : p.R) * f p y)
    (S : Type) [CommRing S] [Algebra K S] (t : ι → Sˣ)
    (y y' : pts S) (hy : FromTest pts mapR y) (hy' : FromTest pts mapR y') (hb : borR t y y') :
    evalAt pts mapR f y' = ((∏ i, t i ^ e i : Sˣ) : S) * evalAt pts mapR f y := by
  unfold evalAt
  rw [dif_pos hy, dif_pos hy']
  apply eq_of_locM (K := K)
  intro m hm
  obtain ⟨A, u, c, c', B, uB, uB', tB, π, π', cB, hc, hc', hπ, hπ', hbB, e1, e2, e3⟩ := h S t y y' hb m
  rw [map_mul, chartAt_val hf hc' hy'.choose_spec.choose_spec.choose_spec,
    chartAt_val hf hc hy.choose_spec.choose_spec.choose_spec, ← e1, ← e2, AlgHom.comp_apply, AlgHom.comp_apply,
    ← hf A B π u uB hπ, ← hf A B π' u uB' hπ', hw B tB uB uB' hbB, map_mul]
  congr 1
  have key : ∀ i, Units.map cB.toRingHom.toMonoidHom (tB i) = Units.map (locM K m).toRingHom.toMonoidHom (t i) :=
    fun i => Units.ext (by simpa using e3 i)
  have h1 : cB ((∏ i, tB i ^ e i : (B.R)ˣ) : B.R) =
      ((Units.map cB.toRingHom.toMonoidHom (∏ i, tB i ^ e i) : (Localization.AtPrime m)ˣ) : Localization.AtPrime m) := rfl
  have h2 : locM K m ((∏ i, t i ^ e i : Sˣ) : S) =
      ((Units.map (locM K m).toRingHom.toMonoidHom (∏ i, t i ^ e i) : (Localization.AtPrime m)ˣ) :
        Localization.AtPrime m) := rfl
  rw [h1, h2, map_prod, map_prod]
  simp_rw [map_zpow, key]

end IntWeight

open Formalism.L2.Pj AllWt

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H}

theorem evR_frBor_of_mem_secZ (hS : Out.SecBaseChangeSt) (Xo : Moduli Dw l) (c : Coeff l) (e : Ix Dw → ℤ)
    {f : Rul Xo c} (hf : f ∈ secZ Xo c e) (S : Type) [CommRing S] [IsReduced S] [Algebra c.F S]
    (t : Ix Dw → Sˣ) (y y' : FrPt Xo c S) (hb : FrBor t y y') :
    evR Xo c f y' = ((∏ i, t i ^ e i : Sˣ) : S) * evR Xo c f y := by
  have hB := (GlobalTheory.T.framedModuli_algebraicLaws_chart_weight_integrality hS E H Dw l Xo c).2.1
  have hall := GlobalTheory.T.framedPoint_reduced_from_testRing hS E H Dw l Xo c
  exact evalAt_borR_of_borChart_int hB e hf.1 hf.2 S t y y' (hall S y) (hall S y') hb

theorem test_value_eq_const_mul_reading_secZ (hS : Out.SecBaseChangeSt) {Xo : Moduli Dw l} {c : Coeff l}
    {σ : c.F →+* ℂ} {r : ℕ} (U : Unf Xo c σ r) (hU : IsUnf U) (e : Ix Dw → ℤ) (p : TRing c.F)
    (y : FrPt Xo c p.R) (ψ : p.R →ₐ[c.F] CAt σ) :
    ∃ (k : U.Comp) (x : (U.X k).dom) (u : ℂ), ∀ f ∈ secZ Xo c e,
      Formalism.L2.Pj.toC (ψ (f p y)) = u * rdU U f k x.1 := by
  obtain ⟨-, -, hW, -, -, -, -⟩ := GlobalTheory.T.framedModuli_algebraicLaws_chart_weight_integrality hS E H Dw l Xo c
  obtain ⟨z, hz⟩ := GlobalTheory.Frames.FramedBaseChange.exists_frMap hS E H Dw l Xo c p.R (CAt σ) ψ y
  obtain ⟨k, x, t, ht⟩ := hU.2.2.1 z
  haveI : IsReduced (CAt σ) := inferInstanceAs (IsReduced ℂ)
  refine ⟨k, x, Formalism.L2.Pj.toC ((∏ i, t i ^ e i : (CAt σ)ˣ) : CAt σ), fun f hf => ?_⟩
  have hft : FromTest (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) z := ⟨p, ψ, y, hz⟩
  have hev : evR Xo c f z = ψ (f p y) := by
    unfold evR evalAt
    rw [dif_pos hft]
    exact hW f hf.1 (CAt σ) _ p _ ψ _ y z hft.choose_spec.choose_spec.choose_spec hz
  have hw := evR_frBor_of_mem_secZ hS Xo c e hf (CAt σ) t _ _ ht
  rw [← hev, hw]
  classical
  show _ = _ * (if h : x.1 ∈ (U.X k).dom then Formalism.L2.Pj.toC (evR Xo c f (U.un k ⟨x.1, h⟩)) else 0)
  rw [dif_pos x.2]
  rfl

theorem reading_linearIndependent_secZ (hS : Out.SecBaseChangeSt) {Xo : Moduli Dw l} {c : Coeff l}
    {σ : c.F →+* ℂ} {r : ℕ} (U : Unf Xo c σ r) (hU : IsUnf U) (e : Ix Dw → ℤ) (m : ℕ) (b : Fin m → Rul Xo c)
    (hb : ∀ i, b i ∈ secZ Xo c e) (hli : LinearIndependent c.F b) :
    LinearIndependent ℂ (fun i => rdU U (b i)) := by
  have h := fun p y ψ => test_value_eq_const_mul_reading_secZ hS U hU e p y ψ
  have : CharZero c.F := RingHom.charZero σ
  rw [Fintype.linearIndependent_iff]
  intro w hw
  have hθ : ∀ θ : Module.Dual c.F (CAt σ), ∀ i, θ (toCAt σ (w i)) = 0 := by
    intro θ
    have hz : ∑ i, θ (toCAt σ (w i)) • b i = 0 := by
      funext p y
      have hpt := descend_cpts σ p (fun i => b i p y) w (fun ψ => by
        obtain ⟨k', x, u, hk⟩ := h p y ψ
        have e1 : ∀ i, w i * cvalR σ (ψ (b i p y)) = u * (w i * rdU U (b i) k' x.1) := by
          intro i; rw [show cvalR σ (ψ (b i p y)) = Formalism.L2.Pj.toC (ψ (b i p y)) from rfl, hk (b i) (hb i)]; ring
        have e2 := congrFun (congrFun hw k') x.1
        simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at e2
        simp_rw [e1]
        rw [← Finset.mul_sum, e2, mul_zero]) θ
      simpa [Finset.sum_apply] using hpt
    exact fun i => Fintype.linearIndependent_iff.1 hli _ hz i
  intro i
  exact (Module.forall_dual_apply_eq_zero_iff c.F (toCAt σ (w i))).1 fun θ => hθ θ i

theorem cuspW_finiteDimensional_of_isUnf (hS : Out.SecBaseChangeSt) {Xo : Moduli Dw l} {c : Coeff l} {r : ℕ}
    (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (σ : c.F →+* ℂ) (hσ : GoodEmb c σ) (hU : IsUnf (U σ)) (G : WTZ E) :
    FiniteDimensional c.F (cuspW Xo c U G) := by
  classical
  let W : Submodule ℂ (FDSec (U σ).X) :=
    { carrier := {P | P ∈ holSub (U σ).X (modelWt (U σ) G) ∧ ∀ k, ∀ x ∉ ((U σ).X k).dom, P k x = 0}
      add_mem' := fun {P Q} hP hQ => ⟨add_mem hP.1 hQ.1, fun k x hx => by
        change P k x + Q k x = 0
        rw [hP.2 k x hx, hQ.2 k x hx, add_zero]⟩
      zero_mem' := ⟨zero_mem _, fun k x hx => rfl⟩
      smul_mem' := fun t P hP => ⟨Submodule.smul_mem _ t hP.1, fun k x hx => by
        change t • P k x = 0
        rw [hP.2 k x hx, smul_zero]⟩ }
  haveI : FiniteDimensional ℂ W :=
    GlobalTheory.T.finiteDimensional_cuspSections_vanishing_offDomain E r (U σ).Comp (U σ).X (modelWt (U σ) G) W (fun P hP => hP.1) (fun P hP => hP.2)
  have key : ∀ s : Finset (cuspW Xo c U G),
      LinearIndependent c.F (fun i : s => (i : cuspW Xo c U G)) → s.card ≤ Module.finrank ℂ W := by
    intro s hs
    let e := s.equivFin
    have h0 : LinearIndependent c.F (fun j : Fin s.card => ((e.symm j : s) : cuspW Xo c U G)) :=
      hs.comp (fun j => e.symm j) e.symm.injective
    have hb : LinearIndependent c.F
        (fun j : Fin s.card => (((e.symm j : s) : cuspW Xo c U G) : Rul Xo c)) :=
      h0.map' (cuspW Xo c U G).subtype (Submodule.ker_subtype _)
    have hc := reading_linearIndependent_secZ hS (U σ) hU (exZ Dw G) s.card _
      (fun j => cuspW_le_secZ G ((e.symm j : s) : cuspW Xo c U G).2) hb
    have hmem : ∀ j : Fin s.card,
        rdU (U σ) (((e.symm j : s) : cuspW Xo c U G) : Rul Xo c) ∈ W :=
      fun j => ⟨(mem_cuspW.1 ((e.symm j : s) : cuspW Xo c U G).2).2 σ hσ, fun k x hx => by
        simp [rdU, hx]⟩
    let b' : Fin s.card → W := fun j => ⟨_, hmem j⟩
    have hc' : LinearIndependent ℂ b' := LinearIndependent.of_comp W.subtype hc
    have := hc'.fintype_card_le_finrank
    simpa using this
  haveI : Module.Free c.F ↥(cuspW Xo c U G) := Module.Free.of_divisionRing _ _
  exact Module.rank_lt_aleph0_iff.mp ((rank_le key).trans_lt (Cardinal.natCast_lt_aleph0))

end GlobalTheory

theorem GlobalTheory.Deep.finiteDimensional_V_of_good : ∀ (D : D7) (T : Core D) (j : ℕ) (Y : Deep T j) (e : ℕ) (o : ℝ), Y.Good e o → ∀ G : WTZ D.host.E, FiniteDimensional Y.d.c₂.F (Y.V G) := by
  intro D T j Y e o hY G
  have hσ : Formalism.L2.Pj.GoodEmb Y.d.c₂ (Formalism.L2.Pj.goodOf Y.d.c₂ Y.d.c₂.F.val.toRingHom) :=
    Formalism.L2.Pj.goodEmb_goodOf _ _
  exact GlobalTheory.cuspW_finiteDimensional_of_isUnf GlobalTheory.abelianSchemeLaws_all.1.secBaseChange Y.U _ hσ (hY.unf _ hσ) G
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaOneMapBaseTupleOfCharacterisationExtremal
section
open NumberField Matrix Complex MeasureTheory IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct Classical ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.OneMapTies

theorem oneMapRow0_of_ties_core : Formalism.MainNotions.ModuliIntegralCharts.H1.ChartIndepSt2 → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : Formalism.L2.DIV.FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec), GlobalTheory.Hk3.Core R F → TieIn T R κ v₀ → IoExt R → ∀ (O : ∀ i, OMDat T.toCore R i Unit (fun _ => A.μ0)) (i : Fin D.R.m), OMPins T R κ v₀ O i → OneMapRow0 T R κ v₀ O i := by
  intro hCI D G _ _ Pl0 T0 A T _ R F κ v₀ hR ht hio O i hpins
  obtain ⟨cc, -, u, -, hequiv, hser, hid⟩ :=
    GlobalTheory.T.exists_unitModulus_constants_equivariant_dictionary hCI D G Pl0 T0 A T R F κ v₀ hR ht hio i _ _ (O i) hpins.2
  exact GlobalTheory.OneMapBase.oneMapRow0_of_rows T R κ v₀ O i (u • cc) 1 hpins hequiv hid
    (GlobalTheory.PhRatCommon.phRat_of_ser_core D G Pl0 T0 A T R F κ v₀ hR ht O i hpins (u • cc) hser
      (GlobalTheory.T.exists_cuspForm_classSum_normalisedData hCI D G Pl0 T0 A T R F κ v₀ hR ht i _ _ (O i) hpins.2 ()) hequiv)

end GlobalTheory.OneMapTies
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraceHeckeOperatorSplitOnePlaceStatement
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.trace_heckeOperator_split_one_place : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ n : ℕ, 1 ≤ n → ∀ π : Submodule ℂ (UA E n → ℂ), IsAutRepU π → ∀ S : Set (Pl E), IsSection S → ∀ K' : ∀ w : Pl E, Subgroup (UL n w), IsLevelFam (fun w : Pl E => MonoidHom.id (UL n w)) (KL n) K' → ∀ f : ∀ w : Pl E, UL n w → ℂ, IsTest (KL n) K' f → ∀ w ∈ S, ∀ σ : SmIrr (UL n w), IsCompU π w σ → trOn (π ⊓ fixed (RF E n) (globLev S K')) (hop S K' f) * twTr σ.ρ (KL n w) (K' w) ((K' w : Set (UL n w)).indicator 1) LinearMap.id = twTr σ.ρ (KL n w) (K' w) (f w) LinearMap.id * trOn (π ⊓ fixed (RF E n) (globLev S K')) (hop S K' (Function.update f w ((K' w : Set (UL n w)).indicator 1))) := by
  first | exact @GlobalTheory.BCT.Peel.trOn_hop_peel | exact GlobalTheory.BCT.Peel.trOn_hop_peel | (intros; apply GlobalTheory.BCT.Peel.trOn_hop_peel <;> assumption)
end

