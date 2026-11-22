import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FlatVectorEqGaussSumSmulCentralTranslate
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0021
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0042
import Development.AbelianVarietyTheory.Definitions.ThetaValues.ExistsRootNotMem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMapOfOfExtends
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0006
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0249
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle1012
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0046
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0031
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0028
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsRhoPtOfSplitting
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsComp
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0009
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DepthZeroSupport
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0682
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0985
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnivChar
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0016
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0827
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LevelLiftIsLiftPrincipalLevelDatumRealisation
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1838
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0934
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0026
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0137
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1674
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0016
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NonemptyAlgHomOfIsIntegral
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0691
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0824

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FlatVectorEqGaussSumSmulCentralTranslateStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ConjTwist GlobalTheory.GalTw ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flatVector_eq_gaussSum_smul_centralTranslate : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A), GlobalTheory.Hk3.Core R F → QGuard R → ∀ (i : Fin D.R.m) (t : T0), VStd D i → ∃ (z : GA D (Vc D i)) (B : ℂ) (ε : ℤ) (r : ℕ) (ψP : ∀ PP : Pl D.host.E, AddChar (kP PP) ℂ), IsCentAt i (R.Q t) z ∧ (∀ τ : ℂ ≃+* ℂ, FixBase T R i τ → τ B = B) ∧ (∀ PP ∈ R.Q t, (ψP PP).IsPrimitive) ∧ ∀ t' : T0, R.Q t' = R.Q t → ∀ f', IsFlatVec R i t' f' → ∃ s : (AE D)ˣ, f' = (B * (∏ PP ∈ R.Q t, GlobalTheory.FlatConj.gaussP PP (ψP PP) (R.xiR t' PP) r) ^ ε * ((R.xi t' s : Circle) : ℂ)) • R.ωP i t' (z, 1) (R.vP i t') := by
  first | exact @GlobalTheory.FlatForm.flat_eq_gauss_smul_om | exact GlobalTheory.FlatForm.flat_eq_gauss_smul_om | (intros; apply GlobalTheory.FlatForm.flat_eq_gauss_smul_om <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsotypicRealNonzeroStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
open ReciprocityTheory.Aut Formalism.AUTREP
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isotypic_real_nonzero : PrN → ∀ hL : GlobalTheory.Published.LocalLanglandsGL, GlobalTheory.LiftRef.AtRows hL fun D cf _ Rw a M => ∀ (j : ℕ) (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) (σ : D.what₂.FT), D.what₂.isot j σ ≠ ⊥ → ∃ (S : Submodule ℂ (Formalism.AUTREP.GAf D.host.E D.R.nV → (M D.what₂.mu0 j h1 h2).wt.W)) (hS : NG.IsIrrRep (M D.what₂.mu0 j h1 h2).wt.ρ S), (NG.isoTyp (M D.what₂.mu0 j h1 h2).wt.ρ S).comap (M D.what₂.mu0 j h1 h2).real ≠ ⊥ ∧ ∀ μ : D.naut.CG 1, (a.chr.e1 μ).1 = cf.mu0 ⟨j - 1, by omega⟩ → ∀ w, IsSplitPl D.host w → D.nbc.locAU j (a.A.cls j h1 h2 (GlobalTheory.LiftRef.autOf (M D.what₂.mu0 j h1 h2) S hS)) w = D.naut.lpChar (D.naut.lpSum (Rw.locR σ w) (spehLoc D.nd D.naut ⟨1, μ, D.R.t⟩ w)) (D.naut.locG D.naut.etaTinv w) := by
  first | exact @GlobalTheory.LiftRef.local_lift_at_reference | exact GlobalTheory.LiftRef.local_lift_at_reference | (intros; apply GlobalTheory.LiftRef.local_lift_at_reference <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ThetaLiftEqMultiplePrincipalLevelClassSum
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.TwSys GlobalTheory.TwAll GlobalTheory.SupLaw GlobalTheory.LiftLeaf
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0 FullRk SgJ BasisOf)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1600000

noncomputable section

namespace GlobalTheory.LiftClassSumPrinc

theorem isReps_mul_central {G Γ : Type} [Group G] [Group Γ] (ι : Γ →* G) (J : Subgroup G) {I : Type} (y : I → G)
    {z : G} (hz : z ∈ Subgroup.center G) (hy : Bridge.IsReps ι J y) : Bridge.IsReps ι J fun i => y i * z := by
  have hc : ∀ a : G, a * z = z * a := fun a => ((Subgroup.mem_center_iff.1 hz) a)
  intro h
  obtain ⟨i, ⟨γ, k, hk⟩, hu⟩ := hy (h * z⁻¹)
  refine ⟨i, ⟨γ, k, ?_⟩, fun i' ⟨γ', k', hk'⟩ => hu i' ⟨γ', k', ?_⟩⟩
  · calc h = h * z⁻¹ * z := by group
      _ = ι γ * y i * k * z := by rw [hk]
      _ = ι γ * y i * (z * k) := by rw [mul_assoc _ (k : G) z, hc (k : G)]
      _ = ι γ * (y i * z) * k := by simp only [mul_assoc]
  · have hc' : ∀ a : G, a * z⁻¹ = z⁻¹ * a := fun a => ((Subgroup.mem_center_iff.1 (Subgroup.inv_mem _ hz)) a)
    rw [hk', mul_assoc _ (k' : G) z⁻¹, hc' (k' : G)]
    group

theorem stab_mul_central {G Γ : Type} [Group G] [Group Γ] (ι : Γ →* G) (J : Subgroup G) (y : G) {z : G}
    (hz : z ∈ Subgroup.center G) : Bridge.stab ι J (y * z) = Bridge.stab ι J y := by
  have hc : ∀ a : G, a * z = z * a := fun a => ((Subgroup.mem_center_iff.1 hz) a)
  ext γ
  rw [Bridge.mem_stab, Bridge.mem_stab]
  have e : (y * z)⁻¹ * ι γ * (y * z) = y⁻¹ * ι γ * y :=
    calc (y * z)⁻¹ * ι γ * (y * z) = z⁻¹ * ((y⁻¹ * ι γ * y) * z) := by group
      _ = z⁻¹ * (z * (y⁻¹ * ι γ * y)) := by rw [hc (y⁻¹ * ι γ * y)]
      _ = y⁻¹ * ι γ * y := by group
  rw [e]

theorem map_mem_center {G H : Type} [Group G] [Group H] (f : G →* H) (hf : Function.Surjective f) {z : G}
    (hz : z ∈ Subgroup.center G) : f z ∈ Subgroup.center H := by
  rw [Subgroup.mem_center_iff]
  intro a
  obtain ⟨a', rfl⟩ := hf a
  rw [← map_mul, ← map_mul, (Subgroup.mem_center_iff.1 hz) a']

theorem twist_good_of {D : D7} (ψ : Twist D Circle) (hQ : ψ.Q = ∅) (hc : ψ.chi = 1) : ψ.Good := by
  obtain ⟨Q, chi, res⟩ := ψ
  dsimp only at hQ hc
  subst hQ hc
  exact ⟨by rw [MonoidHom.ker_one, Subgroup.coe_top]; exact isOpen_univ, fun _ => rfl, fun _ => rfl, splitSet_empty, fun _ _ _ _ _ => rfl,
    fun _ h => absurd h (Finset.notMem_empty _)⟩

theorem lev_eq_of {F E LL : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
    [CommRing LL] {n : ℕ} (hc : CMData F E) (J : Matrix (Fin n) (Fin n) E) (β : GL (Fin n) (E ⊗[F] Af F))
    (L L' : LevDat E LL n) (hr : L.r = L'.r) (ht : L.t = L'.t) (hP : L.Pg = L'.Pg) (hQ : L.Q = L'.Q)
    (hH : L.P.H = ⊥) (hH' : L'.P.H = ⊥) : lev hc J β L = lev hc J β L' := by
  obtain ⟨r, hr0, t, s, Pg, Q, P, cg, xq⟩ := L
  obtain ⟨r', hr0', t', s', Pg', Q', P', cg', xq'⟩ := L'
  dsimp only at hr ht hP hQ hH hH'
  subst hr ht hP hQ
  ext x
  rw [mem_lev, mem_lev, hH, hH', Subgroup.mem_bot, Subgroup.mem_bot]
  rfl

open GlobalTheory.ConjTwist in

theorem ser_transl {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (i : Fin D.R.m) (t : T0)
    {χS χT : (AE D)ˣ →* Circle} (hom : IsWeilDatumO R.ψ (Vc D i) (Wc D i) χS χT (R.ωP i t)) (hθ : IsInfFam R.θ)
    (hv : IsThetaFunO R.ψ (Vc D i) (Wc D i) (R.vP i t)) {k : GA D (Vc D i)} (hk : k ∈ GfC (Vc D i)) (c : ℂ)
    (u : ∀ ρ, lowT (R.MW i (sg0 D A)) ρ) (h : GA D (Vc D i)) (w : (R.cV i).W) (g : GA D (Wc D i)) :
    ser R i t (c • R.ωP i t (k, 1) (R.vP i t)) u h w g = c * ser R i t (R.vP i t) u (h * k) w g := by
  simp only [ser, thetaKO]
  rw [GlobalTheory.FiniteFock.pureTensorO_smul, ← GlobalTheory.OrientedHeis.om_fin_pureTensorO R.ψ _ _ _ _ (R.ωP i t) hom R.θ hθ k hk 1
    (one_mem _) _ _ _ _ (R.vP i t) _ hv, map_smul, Pi.smul_apply, ← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, mul_one,
    smul_eq_mul]

open GlobalTheory.ConjTwist GlobalTheory.FlatVecSum in

theorem sum_eq_classSum {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (j : Fin D.R.m) (t : T0)
    {B : Base (Vc D j) (Wc D j)} (hB : BaseOf R j B) (ψ : Twist D Circle) {c0 : ℂ} (hc0 : c0 ≠ 0) {z' : GA D (Vc D j)}
    (hz' : z' ∈ GfC (Vc D j)) (hzc : Formalism.IndefR.FWT.fin (Vc D j) z' ∈ Subgroup.center (Bridge.Gf (Vc D j)))
    (hflat : c0 • R.ωP j t (z', 1) (R.vP j t) = (princ B).vecFlat ψ)
    {χS χT : (AE D)ˣ →* Circle} (hom : IsWeilDatumO R.ψ (Vc D j) (Wc D j) χS χT (R.ωP j t)) (hθ : IsInfFam R.θ)
    (hv : IsThetaFunO R.ψ (Vc D j) (Wc D j) (R.vP j t)) {m : ℕ} (h₀ : Fin m → GA D (Vc D j))
    (J : Subgroup (Bridge.Gf (Vc D j))) (hrel : ((princ B).levJ ψ).relIndex J = 1) (Ef : Bridge.Gf (Vc D j) → (R.cV j).W)
    (u : ∀ ρ, lowT (R.MW j (sg0 D A)) ρ) (g : GA D (Wc D j)) :
    ∑ k, ((((princ B).levJ ψ).relIndex J : ℕ) : ℂ)⁻¹ *
        ((Nat.card (Bridge.stab (Bridge.ratF (Vc D j)) ((princ B).levJ ψ) (Formalism.IndefR.FWT.fin (Vc D j) (h₀ k * z'))) : ℕ) : ℂ)⁻¹ *
        thetaKO (R.ωP j t) (h₀ k * z') g
          ((pureTensorO R.ψ R.θ (Vc D j) (Wc D j) (fun _ => 1) (cart (R.MW j (sg0 D A))) (R.BV j) (onb (R.MW j (sg0 D A)))
            (R.vP j t) ∘ₗ R.ioP j (PiTensorProduct.tprod ℂ u)) (Ef (Formalism.IndefR.FWT.fin (Vc D j) (h₀ k * z')))) =
      (c0⁻¹ • (princ B).classSum (R.ωP j t) ψ h₀
        (fun h => R.ioP j (PiTensorProduct.tprod ℂ u) (Ef (h * Formalism.IndefR.FWT.fin (Vc D j) z')))) g := by
  rw [Pi.smul_apply, Base.classSum_apply, Finset.sum_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  have hfin1 : Formalism.IndefR.FWT.fin (Vc D j) (h₀ k * z') = finPt (Vc D j) (h₀ k) * Formalism.IndefR.FWT.fin (Vc D j) z' :=
    map_mul _ _ _
  rw [Pi.smul_apply, smul_eq_mul, hrel, Nat.cast_one, inv_one, one_mul, hfin1, stab_mul_central _ _ _ hzc,
    show (princ B).F = B.F from rfl, hB.series_eq_ser, ← hflat, ser_transl R j t hom hθ hv hz', mul_left_comm _ c0,
    ← mul_assoc c0⁻¹ c0, inv_mul_cancel₀ hc0, one_mul]
  rfl

open Classical GlobalTheory.ConjTwist GlobalTheory.FlatVecSum in

theorem thF_eq_classSum_princ : ∀ (D : D7) (X : RealSide D) (E : IntegralHeckeForms.XD D) (Y : SerSide X E) (i : D.ntw.Tw) (j : Fin D.R.m) (b : Bool) (t : X.T),
    X.R.xi t = (Y.Z.ρ.B i j b).de.chi → X.R.Q t = (Y.Z.ρ.B i j b).de.Q → ∀ (y : (X.R.HV j t).H) (u : ∀ ρ, lowT (X.R.MW j (sg0 D X.A3.A)) ρ),
    ∃ (m : ℕ) (h₀ : Fin m → GA D (Vc D j)) (c : ℂ) (z : Bridge.Gf (Vc D j)),
      IsClassSystem (Vc D j) ((GlobalTheory.FlatVecSum.princ (Y.Z.ρ.B i j b)).levJ (Y.Z.ρ.tw i b 0 ∅ 1)) h₀ ∧ z ∈ Subgroup.center (Bridge.Gf (Vc D j)) ∧
      X.R.thF j t y (fun ρ => (u ρ : ↥((X.R.MW j (sg0 D X.A3.A)).sm ρ))) =
        c • (GlobalTheory.FlatVecSum.princ (Y.Z.ρ.B i j b)).classSum (X.R.ωP j t) (Y.Z.ρ.tw i b 0 ∅ 1) h₀
          (fun h => X.R.ioP j (PiTensorProduct.tprod ℂ u) ((X.R.HV j t).e y (h * z))) := by
  intro D X E Y i j b t hxi hQ y u
  have hB : BaseOf X.R.toRealDat j (Y.Z.ρ.B i j b) := GlobalTheory.PinBase.baseOf_of_pin D X Y.Z.ρ Y.Z.good Y.Z.pin i j b
  have hG : (Y.Z.ρ.B i j b).Good := Y.Z.good.base i j b
  have hC : GlobalTheory.Hk3.Core X.R.toRealDat X.F.lv2 :=
    ⟨X.char.lev, X.char.grp, X.char.fam, X.char.models, X.char.chain, X.char.thP⟩
  have he : (Y.Z.ρ.tw i b 0 ∅ 1).Q = ∅ := half_empty _
  have hone : (Y.Z.ρ.tw i b 0 ∅ 1).chi = 1 := charOf_one _ _
  have hψ : (Y.Z.ρ.tw i b 0 ∅ 1).Good := twist_good_of _ he hone
  have hadm : (Y.Z.ρ.B i j b).admitted (Y.Z.ρ.tw i b 0 ∅ 1).Q := by rw [he]; exact Base.admissible_empty_of_good hG
  have htup : IsTupOf X.R.toRealDat (Y.Z.ρ.B i j b) (Y.Z.ρ.tw i b 0 ∅ 1) t :=
    ⟨by rw [hxi, hone, mul_one], by rw [hQ, he, Finset.union_empty]⟩
  obtain ⟨⟨f, hf⟩, -⟩ := GlobalTheory.FlatVecExist.flatVec_existsUnique D X.Γ X.Pl0 X.T X.A3.A _ X.R.toRealDat X.F.lv2 hC X.guard j t
  obtain ⟨z', c0, hz', hc0, hfz⟩ :=
    GlobalTheory.T.flatVector_eq_unit_mul_centralTranslate_liftVector D X.Γ X.Pl0 X.T X.A3.A _ X.R.toRealDat X.F.lv2 hC X.guard j t (X.std j) f hf
  have hflat : f = (princ (Y.Z.ρ.B i j b)).vecFlat (Y.Z.ρ.tw i b 0 ∅ 1) :=
    eq_vecFlat_princ hB htup hC.lev hG hψ hadm hf

  have hβ : (princ (Y.Z.ρ.B i j b)).F.βS = X.R.βV j := hB.βS
  have hrW : (Wc D j).rank = D.R.r := D.sp.W_rank _ (Nat.le_add_left _ _) j.2
  have hrV : (Vc D j).rank = D.R.r + D.R.t := D.sp.V_rank _ (Nat.le_add_left _ _) j.2
  have hJ : (princ (Y.Z.ρ.B i j b)).levJ (Y.Z.ρ.tw i b 0 ∅ 1) =
      (levEnv (Vc D j) (X.R.βV j) (X.R.datVt j t)).J := by
    unfold Base.levJ
    rw [hβ, GlobalTheory.LiftClassSumPrinc.lev_eq_of _ _ _ ((princ (Y.Z.ρ.B i j b)).levS (Y.Z.ρ.tw i b 0 ∅ 1))
      (Formalism.IndefR.Lev.flag1L (X.R.datVt j t)) (by show (Wc D j).rank = D.R.r; exact hrW)
      (by show (Vc D j).rank - (Wc D j).rank = D.R.t; omega) (by show (Y.Z.ρ.B i j b).G.Pg = X.R.Pg; exact hB.Pg)
      (by show (Y.Z.ρ.B i j b).de.Q ∪ (Y.Z.ρ.tw i b 0 ∅ 1).Q = X.R.Q t; rw [he, Finset.union_empty, hQ]) rfl rfl]
    rfl
  have hrel : ((princ (Y.Z.ρ.B i j b)).levJ (Y.Z.ρ.tw i b 0 ∅ 1)).relIndex
      (levEnv (Vc D j) (X.R.βV j) (X.R.datVt j t)).J = 1 := Subgroup.relIndex_eq_one.2 hJ.ge
  refine (exists_isClassSystem (princ (Y.Z.ρ.B i j b)) (princ_good hG).frame (Y.Z.ρ.tw i b 0 ∅ 1)).elim fun m hm =>
    hm.elim fun h₀ hcs => ?_
  have hzc : Formalism.IndefR.FWT.fin (Vc D j) z' ∈ Subgroup.center (Bridge.Gf (Vc D j)) :=
    GlobalTheory.LiftClassSumPrinc.map_mem_center (finHom (Vc D j)).rangeRestrict (MonoidHom.rangeRestrict_surjective _) hz'.1
  refine ⟨m, h₀, c0⁻¹, Formalism.IndefR.FWT.fin (Vc D j) z', hcs, hzc, ?_⟩
  have hfin1 : ∀ k, Formalism.IndefR.FWT.fin (Vc D j) (h₀ k * z') = finPt (Vc D j) (h₀ k) * Formalism.IndefR.FWT.fin (Vc D j) z' :=
    fun k => map_mul _ _ _
  have hy : Bridge.IsReps (Bridge.ratF (Vc D j)) ((princ (Y.Z.ρ.B i j b)).levJ (Y.Z.ρ.tw i b 0 ∅ 1))
      (fun k => Formalism.IndefR.FWT.fin (Vc D j) (h₀ k * z')) := by
    rw [show (fun k => Formalism.IndefR.FWT.fin (Vc D j) (h₀ k * z')) = fun k => finPt (Vc D j) (h₀ k) * Formalism.IndefR.FWT.fin (Vc D j) z'
      from funext hfin1]
    exact GlobalTheory.LiftClassSumPrinc.isReps_mul_central _ _ _ hzc hcs.reps
  have hh : ∀ k, h₀ k * z' ∈ GfC (Vc D j) := fun k => mul_mem (hcs.fin k) hz'.2.1
  have hθ : IsInfFam X.R.θ := hC.models.inf
  have hvθ : IsThetaFunO X.R.ψ (Vc D j) (Wc D j) (X.R.vP j t) :=
    GlobalTheory.AdTh.MinorWeight.pure_one _ (X.R.vP j t) ▸ hC.thP.pt_theta j t 1
  funext g
  refine (hC.thP.thF j t).elim fun thP hPF => ?_
  have hx : (X.R.HV j t).e y ∈ Bridge.AdForms (Bridge.ratF (Vc D j)) (X.R.cV j).coef.ρ
      (levEnv _ (X.R.βV j) (X.R.datVt j t)).J (levEnv _ (X.R.βV j) (X.R.datVt j t)).χ :=
    (hC.models.HV j t).2.1.le (LinearMap.mem_range_self _ y)
  have hfin : ∀ k ∈ GfC (Vc D j), ∀ hk : Formalism.IndefR.FWT.fin (Vc D j) k ∈ Formalism.IndefR.FWT.levJ X.R.toRealDat j t, ∀ P,
      X.R.ωP j t (k, 1) (X.R.ptP j t P) =
      (((levEnv (Vc D j) (X.R.βV j) (X.R.datVt j t)).χ ⟨Formalism.IndefR.FWT.fin (Vc D j) k, hk⟩ : ℂˣ) : ℂ)⁻¹ • X.R.ptP j t P :=
    fun k hk hk' =>
    GlobalTheory.FiniteFock.om_pureTensorO_of_finite X.R.ψ X.R.θ (Vc D j) (Wc D j) _ _ (X.R.ωP j t) hC.models.inf
      (hC.thP.ωP j t) _ _ _ _ _ (hC.thP.pt_theta j t) k hk 1 (one_mem _) _
      (GlobalTheory.AdTh.LevelLawCore.omega_level_vP_core D X.Γ X.Pl0 X.T X.A3.A _ X.R.toRealDat X.F.lv2 hC j t k (X.std j) hk hk')
  have key := GlobalTheory.LiftUnfold.integral_theta (hC.thP.ωP j t) (D.sp.V_sig _) (hC.models.vpos j) (X.R.cV j) (hC.models.cV j)
    (X.R.βV j) (X.R.datVt j t) (fun _ => Iff.rfl) hx
    (pureTensorO X.R.ψ X.R.θ (Vc D j) (Wc D j) (fun _ => 1) (cart (X.R.MW j (sg0 D X.A3.A))) (X.R.BV j)
      (onb (X.R.MW j (sg0 D X.A3.A))) (X.R.vP j t) ∘ₗ X.R.ioP j (PiTensorProduct.tprod ℂ u)) (fun w => hC.thP.pt_theta j t _)
    (fun a ha w => (hC.thP.ioP j t).1 a ha _ w) (fun k hk hk' w => hfin k hk hk' _)
    (hC.models.νV j t) _ (Fin m) (fun k => h₀ k * z') hJ.le (by rw [hrel]; exact one_ne_zero) hy hh g
  have h1 := congrFun (hPF.2 y u) g
  have h2 := hPF.1.eq ((X.R.extV j t).rangeRestrict y) (PiTensorProduct.tprod ℂ u) g
  refine h1.trans (h2.trans (Eq.trans ?_ (key.trans ?_)))
  · rfl
  exact sum_eq_classSum X.R.toRealDat j t hB (Y.Z.ρ.tw i b 0 ∅ 1) hc0.1 hz'.2.1 hzc (hfz.symm.trans hflat) (hC.thP.ωP j t) hθ
    hvθ h₀ _ hrel ((X.R.HV j t).e y) u g

end GlobalTheory.LiftClassSumPrinc

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.XiIntComb
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.TwSys GlobalTheory.TwAll GlobalTheory.SupLaw GlobalTheory.LiftLeaf
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0 FullRk SgJ BasisOf)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

noncomputable section

namespace GlobalTheory.XiIntComb

variable {D : D7} {X : RealSide D} {E : IntegralHeckeForms.XD D}

def Good (Y : SerSide X E) (i : D.ntw.Tw) (j : Fin D.R.m) (b : Bool) (s : Finset (Pl D.host.E)) (h : GA D (Vc D j)) (u : ℂ)
    (P : PolF D (Wc D j).rank (Vc D j).rank) : Prop :=
  ∃ c : ℕ, ∀ Q M, InRange D.ntw i Q → (∀ v ∈ Q, ((normProd s : ℕ) : 𝓞 D.host.E) ∉ v.asIdeal) → ∀ a,
    ∃ (n : ℕ) (o : Fin n → D.ntw.O i) (m : Fin n → NX.FmK Y.S ((j : ℕ) + 1)), (∀ k, Subtype.val (m k) ∈ (Y.S.A ((j : ℕ) + 1)).MK) ∧
      (((D.ntw.l i : ℕ) : ℂ) ^ c * u) • Y.Z.ρ.xi i j b D.nexp Q M h P a =
        ∑ k, Y.Z.ρ.eO i b (o k) • evW Y.YS X.geo.v₀ j (Subtype.val (m k))

variable (Y : SerSide X E) (i : D.ntw.Tw) (j : Fin D.R.m) (b : Bool) (s : Finset (Pl D.host.E)) (h : GA D (Vc D j)) (u : ℂ)

theorem xi_eq_lin (Q : Finset (Pl D.host.E)) (M : ℕ) (P : PolF D (Wc D j).rank (Vc D j).rank) (a) :
    Y.Z.ρ.xi i j b D.nexp Q M h P a = xiLin Y.Z.ρ D.nexp i j b Q M h a P := rfl

theorem good_zero : Good Y i j b s h u 0 := by
  refine ⟨0, fun Q M _ _ a => ⟨0, Fin.elim0, Fin.elim0, fun k => k.elim0, ?_⟩⟩
  rw [xi_eq_lin, map_zero, smul_zero, Finset.univ_eq_empty, Finset.sum_empty]

theorem good_smul {P : PolF D (Wc D j).rank (Vc D j).rank} (hP : Good Y i j b s h u P) (o : D.ntw.O i) :
    Good Y i j b s h u (Y.Z.ρ.eO i b o • P) := by
  obtain ⟨c, hc⟩ := hP
  refine ⟨c, fun Q M hQ hs a => ?_⟩
  obtain ⟨n, o', m, hm, he⟩ := hc Q M hQ hs a
  refine ⟨n, fun k => o * o' k, m, hm, ?_⟩
  rw [xi_eq_lin, map_smul, smul_comm, ← xi_eq_lin, he, Finset.smul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [smul_smul, map_mul]

theorem good_add {P P' : PolF D (Wc D j).rank (Vc D j).rank} (hP : Good Y i j b s h u P) (hP' : Good Y i j b s h u P') :
    Good Y i j b s h u (P + P') := by
  obtain ⟨c, hc⟩ := hP
  obtain ⟨c', hc'⟩ := hP'
  refine ⟨c + c', fun Q M hQ hs a => ?_⟩
  obtain ⟨n, o, m, hm, he⟩ := hc Q M hQ hs a
  obtain ⟨n', o', m', hm', he'⟩ := hc' Q M hQ hs a
  have hl : Y.Z.ρ.eO i b ((D.ntw.l i : ℕ) : D.ntw.O i) = ((D.ntw.l i : ℕ) : ℂ) := map_natCast _ _
  refine ⟨n + n', Fin.append (fun k => ((D.ntw.l i : ℕ) : D.ntw.O i) ^ c' * o k)
    (fun k => ((D.ntw.l i : ℕ) : D.ntw.O i) ^ c * o' k), Fin.append m m', fun k => ?_, ?_⟩
  · refine Fin.addCases (fun k => ?_) (fun k => ?_) k
    · rw [Fin.append_left]; exact hm k
    · rw [Fin.append_right]; exact hm' k
  · rw [Fin.sum_univ_add]
    simp only [Fin.append_left, Fin.append_right]
    rw [xi_eq_lin, map_add, smul_add, ← xi_eq_lin, ← xi_eq_lin]
    congr 1
    · rw [show (((D.ntw.l i : ℕ) : ℂ) ^ (c + c') * u) = ((D.ntw.l i : ℕ) : ℂ) ^ c' * (((D.ntw.l i : ℕ) : ℂ) ^ c * u) by ring,
        mul_smul, he, Finset.smul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [smul_smul, map_mul, map_pow, hl]
    · rw [show (((D.ntw.l i : ℕ) : ℂ) ^ (c + c') * u) = ((D.ntw.l i : ℕ) : ℂ) ^ c * (((D.ntw.l i : ℕ) : ℂ) ^ c' * u) by ring,
        mul_smul, he', Finset.smul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [smul_smul, map_mul, map_pow, hl]

end GlobalTheory.XiIntComb

open GlobalTheory.XiIntComb in
theorem GlobalTheory.XiIntComb.xi_int_comb : GlobalTheory.Published.GlobalArtinReciprocity → GlobalTheory.IndefiniteRowSideFullHecke.RationalRayLevels.SeriesRat → GlobalTheory.IndefiniteRowSideFullHecke.TwistSeries.SerInt → ∀ (D : D7) (X : RealSide D) (E : IntegralHeckeForms.XD D) (Y : SerSide X E), FieldOk X → (∀ (j : Fin D.R.m) hV, GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.FramePin X.core X.R.toRealDat j X.core.σ₀ hV) → ∀ i, D.ntw.NonzeroIndexPlace i → ∀ (j : Fin D.R.m) b s h P, Y.Z.ρ.IsDatum i j b s h P → ∃ (u : ℂ) (c : ℕ), u ≠ 0 ∧ ∀ Q M, InRange D.ntw i Q → (∀ v ∈ Q, ((normProd s : ℕ) : 𝓞 D.host.E) ∉ v.asIdeal) → ∀ a, ∃ (n : ℕ) (o : Fin n → D.ntw.O i) (m : Fin n → NX.FmK Y.S ((j : ℕ) + 1)), (∀ k, Subtype.val (m k) ∈ (Y.S.A ((j : ℕ) + 1)).MK) ∧ (((D.ntw.l i : ℕ) : ℂ) ^ c * u) • Y.Z.ρ.xi i j b D.nexp Q M h P a = ∑ k, Y.Z.ρ.eO i b (o k) • evW Y.YS X.geo.v₀ j (Subtype.val (m k)) := by
  intro hAR hSR hSI D X E Y hF hFP i hi j b s h P hd
  obtain ⟨u, hu0, hgen⟩ := GlobalTheory.T.thetaSeries_integral_core_supLattice_combination hAR hSR hSI D X E Y hF hFP i hi j b s h ⟨hd.split, hd.off, hd.fin, hd.supp, zero_mem _⟩
  have hB := Y.Z.good.base i j b
  have hm : ∀ τ, (Y.Z.ρ.B i j b).w.p τ + (Y.Z.ρ.B i j b).w.q τ ≤ (Wc D j).rank := fun τ => by
    have h1 := hB.sig τ
    have h2 := Formalism.BasicNotions.sig_sum _ hB.sigOK (tauE D τ)
    rw [← h1] at h2
    exact h2.le
  have hinj := GlobalTheory.T.harmonic_polynomial_eq_zero_of_function D _ _ _ (Y.Z.ρ.B i j b).F.BS hB.wt hm
  have key : ∀ φ ∈ coefLatFn (Formalism.L2.Host.embLL0 D) (labLL0 D) (Y.Z.ρ.eO i b).range (Y.Z.ρ.B i j b).w.lam
      ((Y.Z.ρ.B i j b).latAt (finPt _ h)), ∃ P' ∈ (Y.Z.ρ.B i j b).valSpace,
        harmFn (Wc D j).rank (Y.Z.ρ.B i j b).w (Y.Z.ρ.B i j b).F.BS P' = φ ∧ Good Y i j b s h u P' := by
    intro φ hφ
    induction hφ using Submodule.span_induction with
    | mem _ h1 =>
      obtain ⟨F, -, rfl⟩ := h1
      obtain ⟨P', h2, h3⟩ := GlobalTheory.T.harmonic_polys_reach_small_field_coefficient_functions hAR hSR hSI D X E Y hF hFP i hi j b F
      exact ⟨P', h2, h3, hgen P' h2 F h3⟩
    | zero => exact ⟨0, zero_mem _, map_zero _, good_zero Y i j b s h u⟩
    | add _ _ _ _ h1 h2 =>
      obtain ⟨P₁, a1, rfl, g1⟩ := h1
      obtain ⟨P₂, a2, rfl, g2⟩ := h2
      exact ⟨P₁ + P₂, add_mem a1 a2, map_add _ _ _, good_add Y i j b s h u g1 g2⟩
    | smul c _ _ h1 =>
      obtain ⟨P₁, a1, rfl, g1⟩ := h1
      obtain ⟨_, o, rfl⟩ := c
      exact ⟨Y.Z.ρ.eO i b o • P₁, Submodule.smul_mem _ _ a1, map_smul _ _ _, good_smul Y i j b s h u g1 o⟩
  obtain ⟨P', h1, h2, ⟨c, hc⟩⟩ := key _ hd.mem.2
  obtain rfl : P = P' := sub_eq_zero.1 (hinj (P - P') (sub_mem hd.mem.1 h1) (by rw [map_sub, h2]; exact sub_self _))
  exact ⟨u, c, hu0, hc⟩
end
end

