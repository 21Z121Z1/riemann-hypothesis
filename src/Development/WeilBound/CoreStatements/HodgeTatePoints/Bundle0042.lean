import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.KleimanNefness.Bundle0002
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.GenericPointSectionHypotheses
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.IsFieldSubalgebraSelf
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0025
import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.Bundle0012
import Development.WeilBound.CoreStatements.HodgeTatePoints.Bundle0041
import Development.WeilBound.CoreStatements.HodgeTatePoints.Bundle0037
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.GermComp1ZeroPointLeft
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0010
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0013
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0007
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.Bundle0001
import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0019
import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0033
import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0028
import ReciprocityTheory.DualLattices.Bundle0005
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle0003
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle0004
import Development.WeilBound.CoreStatements.HodgeTatePoints.Bundle0040
import Development.WeilBound.CoreStatements.HodgeTatePoints.RbFund
import Development.WeilBound.CoreStatements.HodgeTatePoints.Bundle0029
import Development.WeilBound.CoreStatements.HodgeTatePoints.Bundle0034
import Development.WeilBound.CoreStatements.HodgeTatePoints.RcFlag
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0054
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0015
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.TwistSubEqChartSecOver
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PSegreBase
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0065
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ExistsNeZeroOfWeight
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0070
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0067

-- bundled from Development.WeilBound.CoreStatements.HodgeTatePoints.KleimanInputUniverseZero
section
namespace PositivityTheory.HtPt.Kra

universe u w

theorem kleiman_input : GroundTheory.Heights₂.Heights.Kleiman.GenericPointSectionInput.Statement.{u, w} :=
  GroundTheory.Heights₂.Heights.Kleiman.GenericPointSectionInput.proof interNumEventual interNumAdditive
    (intersectionNumberCut_of_mixedTwistShift mixedTwistShift) interNumPointDeg

theorem kleiman_input_universe_zero : GroundTheory.Heights₂.Heights.Kleiman.GenericPointSectionInput.Statement.{0, 0} := kleiman_input

end PositivityTheory.HtPt.Kra
end

-- bundled from Development.WeilBound.CoreStatements.HodgeTatePoints.MapFirstPower
section
noncomputable section

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj

namespace PositivityTheory.HtPt.Cc

open Formalism.MainNotions.ModuliIntegralCharts.H1.FBMap in
theorem map_first_power {R R₂ : Type} [CommRing R] [CommRing R₂] {f : R →+* R₂} {d : ℕ} {O : Type} [CommRing O]
    [StarRing O] {B : FB R d O} {B₂ : FB R₂ d O} (h : IsMapOf f B B₂) (m : ℕ) :
    pow1 B₂ m = MvPowerSeries.map f (pow1 B m) := by
  have hact : ∀ a : O, mp f (B.A.act a) = B₂.A.act a := fun a => funext fun i => (h.act a i).symm
  unfold pow1
  rw [map_prod]
  refine Finset.prod_congr rfl fun n _ => ?_
  have hc : ∀ (j : Fin 3) (i : Fin d),
      constantCoeff ((![comp1 (B.A.act (n : O)) (pt R d 0), pt R d 0, pt R d 1] : Fin 3 → Pt R 2 d) j i) = 0 := by
    intro j i
    fin_cases j
    · exact cz_comp1 _ (B.A.const _) _ (cz_pt 0) i
    · exact cz_pt 0 i
    · exact cz_pt 1 i
  rw [map_ev' f _ hc B.ph1, ← h.ph1]
  congr 1
  funext j
  fin_cases j
  · simp [mp_comp1 f _ _ (cz_pt 0), mp_pt, hact]
  · simp [mp_pt]
  · simp [mp_pt]

private theorem lin_map' {R R₂ : Type} [CommRing R] [CommRing R₂] (f : R →+* R₂) {d : ℕ}
    (φ : Pt R 1 d) (m : ℕ) : lin (fun i => MvPowerSeries.map f (φ i)) m = (lin φ m).map f := by
  ext i j
  simp [lin, Matrix.map_apply, MvPowerSeries.coeff_map]

private theorem bil_map' {R R₂ : Type} [CommRing R] [CommRing R₂] (f : R →+* R₂) {d : ℕ}
    (g : PS R 2 d) (m n : ℕ) : bil (MvPowerSeries.map f g) m n = (bil g m n).map f := by
  ext i j
  simp [bil, Matrix.map_apply, MvPowerSeries.coeff_map]

theorem map_mats : ∀ (R R₂ : Type) [CommRing R] [CommRing R₂] (f : R →+* R₂) (d : ℕ) (O : Type) [CommRing O] [StarRing O] (B : FB R d O) (B₂ : FB R₂ d O), IsMapOf f B B₂ → (∀ a, rho B₂ a = (rho B a).map f ∧ bil (B₂.ad a) 1 1 = (bil (B.ad a) 1 1).map f) ∧ bil B₂.sy 1 1 = (bil B.sy 1 1).map f ∧ ∀ p, hw B₂ p = (hw B p).map f ∧ am B₂ p = (am B p).map f := by
  intro R R₂ _ _ f d O _ _ B B₂ h
  have hact : ∀ a : O, B₂.A.act a = fun i => MvPowerSeries.map f (B.A.act a i) :=
    fun a => funext fun i => h.act a i
  refine ⟨fun a => ⟨?_, ?_⟩, ?_, fun p => ⟨?_, ?_⟩⟩
  · show lin (B₂.A.act a) 1 = _
    rw [hact, lin_map']
    rfl
  · rw [h.ad, bil_map']
  · rw [h.sy, bil_map']
  · show lin (B₂.A.act (p : O)) p = _
    rw [hact, lin_map']
    rfl
  · show bil (pow1 B₂ p) p 1 = _
    rw [map_first_power h, bil_map']
    rfl

end PositivityTheory.HtPt.Cc
end
end

-- bundled from Development.WeilBound.CoreStatements.HodgeTatePoints.PfCoordOfSystem
section
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4

namespace PositivityTheory.HtPt.Aig

open ReciprocityTheory.ChartRestriction.G.AI.I2 in

theorem pfCoord_of_system :
    ReciprocityTheory.ChartRestriction.G.Geo.ArithIntersectionSystemStatement → PFCoordStatement := by
  rintro ⟨II, hSys, -, hPF, -⟩
  intro I hI K _ ι _ K' _ ι' _ κ v Ω _ _ y d L L' hv hP' hP hL hL'
  have hU : UniqueStatement :=
    GroundTheory.Heights₂.Heights.Inter.ThmIUnique.proof GroundTheory.Heights₂.Heights.Inter.arithVarZero
  have hd : 1 ≤ d := by
    rcases Nat.eq_zero_or_pos d with rfl | h
    · exact absurd hP (GroundTheory.Heights₂.Heights.Inter.arithVarZero K ι _)
    · exact h
  have hL's : ∀ j, IsSmoothHerm (L' j) := fun j =>
    GroundTheory.Heights₂.Heights.Inter.PushforwardArithIntersection.isSmoothHerm_pull hv (hL j) (hL' j)
  have e1 : I K' ι' (mCoordIdeal y) d L' = II K' ι' (mCoordIdeal y) d L' :=
    hU K' ι' (I K' ι') (II K' ι') (IsIntersectionFamily.isRFamily (hI K' ι'))
      (IsIntersectionFamily.isRFamily (hSys K' ι')) _ d L' hd hP' hL's
  have e2 : I K ι (imageZ v (mCoordIdeal y)) d L = II K ι (imageZ v (mCoordIdeal y)) d L :=
    hU K ι (I K ι) (II K ι) (IsIntersectionFamily.isRFamily (hI K ι))
      (IsIntersectionFamily.isRFamily (hSys K ι)) _ d L hd hP hL
  rw [e1, e2]
  exact hPF K ι K' ι' κ v Ω y d L L' hv hP' hP hL hL'

theorem pfCoord : ReciprocityTheory.ChartRestriction.G.Geo.ArithIntersectionSystemStatement → PFCoordStatement :=
  pfCoord_of_system

end PositivityTheory.HtPt.Aig
end

-- bundled from Development.WeilBound.CoreStatements.HodgeTatePoints.RdFlagFin
section
open ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Up GlobalTheory.CompanionTheory.Ar.GR
open scoped Matrix

namespace PositivityTheory.HtPt.Rd

theorem flag_om : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C], v.Integers R → v (p : C) < 1 → ∀ (F : Type) [Field F] [Fintype F] [DecidableEq F] [CharP F p] (f : ℕ), Fintype.card F = p ^ f → ∀ (N : Type) [AddCommGroup N] [Module F N] [Fintype N] [DecidableEq N] (AA : HopfOrder (C := C) R N), FStable F AA.carrier → ∀ (n : ℕ) (b : Module.Basis (Fin n) F N), ∀ (χ : MulChar F R) (s : Fin n → NNReal) (r : NNReal), (∀ i : Fin n, HasLen v R (OmType (stepOrder AA.carrier (flagSub b i) (b i)) χ) (s i)) → HasLen v R (OmType AA.carrier χ) r → ∏ i, s i ≤ r :=
  flag_om_of @PositivityTheory.HtPt.Rb.fund_ex @PositivityTheory.HtPt.Rc.subquo @PositivityTheory.HtPt.Rc.om_split
    @PositivityTheory.HtPt.Rc.om_step

theorem gr_partial : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C], v.Integers R → v (p : C) < 1 → ∀ (F : Type) [Field F] [Fintype F] [DecidableEq F] [CharP F p] (f : ℕ), Fintype.card F = p ^ f → ∀ (N : Type) [AddCommGroup N] [Module F N] [Fintype N] [DecidableEq N] (AA : HopfOrder (C := C) R N), FStable F AA.carrier → ∀ (n : ℕ) (b : Module.Basis (Fin n) F N), ∀ (χ : MulChar F R) (s : Fin n → NNReal), (∀ i : Fin n, HasLen v R (OmType (stepOrder AA.carrier (flagSub b i) (b i)) χ) (s i)) → HasLen v R (OmType AA.carrier χ) (∏ i, s i) → ∀ j : ℕ, HasLen v R (OmType (AA.carrier.map (LinearMap.funLeft R C (Subtype.val : flagSub b j → N))) χ) (∏ i ∈ Finset.univ.filter (fun i : Fin n => (i : ℕ) < j), s i) :=
  gr_partial_of @PositivityTheory.HtPt.Rb.fund_ex @PositivityTheory.HtPt.Rc.subquo @PositivityTheory.HtPt.Rc.step
    @PositivityTheory.HtPt.Rc.om_split @PositivityTheory.HtPt.Rc.om_step

end PositivityTheory.HtPt.Rd
end

-- bundled from Development.WeilBound.CoreStatements.HodgeTatePoints.SiubOf
section
open MvPolynomial ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Kleiman2

namespace PositivityTheory.HtPt.Siub

theorem exists_multilinear {M : Type} [AddCommGroup M] {n : ℕ} (g : (Fin n → M) → ℤ)
    (hg : ∀ (v : Fin n → M) (i : Fin n) (x y : M),
      g (Function.update v i (x + y)) = g (Function.update v i x) + g (Function.update v i y)) :
    ∃ f : MultilinearMap ℤ (fun _ : Fin n => M) ℤ, ∀ v, f v = g v := by
  refine ⟨⟨g, ?_, ?_⟩, fun _ => rfl⟩
  · intro inst v i x y
    have h := hg v i x y
    convert h
  · intro inst v i c x
    have hi : inst = instDecidableEqFin n := Subsingleton.elim _ _
    subst hi
    have h := map_zsmul (AddMonoidHom.mk' (fun z : M => g (Function.update v i z)) (hg v i)) c x
    simp only [AddMonoidHom.mk'_apply] at h
    convert h

theorem siu_base_of (hnum : ∀ (M : Type) [AddCommGroup M] (d : ℕ) (f : MultilinearMap ℤ (fun _ : Fin (d + 1) => M) ℤ) (μ e : M), 0 < f (fun _ => μ) → ∃ t : ℚ, 0 < t ∧ ∀ (a : ℕ) (m : ℤ), 1 ≤ a → (m : ℚ) = a * t → ((d + 1 : ℕ) : ℤ) * f (Fin.snoc (α := fun _ => M) (fun _ : Fin d => a • μ + m • e) ((2 * m) • e)) < f (fun _ => a • μ + m • e)) :
    VeryAmpleNefPlusAmple.Statement → SectionCount.Statement → ∀ (F : Type) [Field F] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] [Algebra F Ω] (y : (Σ k, ι k) → Ω) (k₀ : K) (d : ℕ) (μ : K → ℤ), IsModelWithBase F y k₀ → GroundTheory.Heights₂.Heights.FieldNumbers.relDim (mIdealOver F y) = ((d + 1 : ℕ) : WithBot (WithTop ℤ)) → IsNef F y μ → 0 < GroundTheory.Heights₂.Heights.NumbersDVR.intNum F (mIdealOver F y) (fun _ : Fin (d + 1) => μ) → ∃ a m : ℕ, 1 ≤ a ∧ 1 ≤ m ∧ ∃ σ ∈ secOver F y (a • μ - (m : ℤ) • baseDeg k₀), σ ≠ 0 := by
  intro hK hS F _ K _ _ ι _ Ω _ _ y k₀ d μ hy hd hnef hpos
  have hP := GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization.isMultiProjPrime_mIdealOver (S := F) y hy.1
  obtain ⟨f, hf⟩ := exists_multilinear (M := K → ℤ) (n := d + 1)
    (fun v => GroundTheory.Heights₂.Heights.NumbersDVR.intNum F (mIdealOver F y) v)
    (GroundTheory.Heights₂.Heights.FieldNumbers.IntNumAdd.full F K ι (mIdealOver F y) hP.multiHomog hP.relevant
      (d + 1) hd)
  obtain ⟨t, ht, hlt⟩ := hnum (K → ℤ) d f μ (baseDeg k₀) (by rw [hf]; exact hpos)
  obtain ⟨a, m, ha, hm, hva⟩ := hK (d + 1) F K ι Ω y k₀ hy hd μ hnef t ht
  have hmpos : 0 < m := by
    have ha' : (0 : ℚ) < a := by exact_mod_cast ha
    have : (0 : ℚ) < m := by rw [hm]; exact mul_pos ha' ht
    exact_mod_cast this
  obtain ⟨r, rfl⟩ := Int.eq_ofNat_of_zero_le hmpos.le
  have hr : 0 < r := by exact_mod_cast hmpos
  have hlt' := hlt a r ha hm
  rw [hf, hf] at hlt'
  have hq : (2 * (r : ℤ)) • baseDeg k₀ = (2 * r) • baseDeg k₀ := by
    rw [← natCast_zsmul]; push_cast; rfl
  rw [hq] at hlt'
  obtain ⟨C, hC⟩ := hS F K ι Ω y k₀ d (a • μ + (r : ℤ) • baseDeg k₀) (2 * r) hy hd hva (by omega)
  obtain ⟨n, hn, hfin⟩ := GroundTheory.Heights₂.Heights.Kleiman.exists_pos_of_eventually_lower (d := d)
    (sub_pos.mpr hlt') (C := C)
    (f := fun n : ℕ => (Module.finrank F
      (secOver F y (n • (a • μ + (r : ℤ) • baseDeg k₀ - (2 * r) • baseDeg k₀))) : ℝ))
    (Filter.eventually_atTop.mpr ⟨1, fun n hn => by
      have := hC n hn
      rwa [Int.cast_sub, Int.cast_mul, Int.cast_natCast]⟩) 1 one_pos
  rw [one_mul] at hfin
  have e : n • (a • μ + (r : ℤ) • baseDeg k₀ - (2 * r) • baseDeg k₀) =
      (n * a) • μ - ((n * r : ℕ) : ℤ) • baseDeg k₀ := by
    module
  rw [e] at hfin
  refine ⟨n * a, n * r, Nat.mul_pos hn ha, Nat.mul_pos hn hr, ?_⟩
  refine Submodule.exists_mem_ne_zero_of_ne_bot fun h => ?_
  rw [h, finrank_bot] at hfin
  simp at hfin

theorem prod_mem_secOver {F : Type} [Field F] {K : Type} [Fintype K] {ι : K → Type} {Ω : Type} [Field Ω]
    [Algebra F Ω] (y : (Σ k, ι k) → Ω) (i : ∀ k, ι k) :
    (∏ k, y ⟨k, i k⟩) ∈ secOver F y (1 : K → ℤ) := by
  simp only [secOver, Submodule.mem_iInf, Submodule.mem_comap, LinearMap.mulRight_apply,
    Subalgebra.mem_toSubmodule]
  intro c _
  rw [← Finset.prod_mul_distrib]
  refine Subalgebra.prod_mem _ fun k _ => ?_
  rw [Pi.one_apply, zpow_neg_one, ← div_eq_mul_inv]
  exact Algebra.subset_adjoin ⟨⟨k, i k⟩, rfl⟩

open GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization in
theorem siu_segre_of_base (hbase : VeryAmpleNefPlusAmple.Statement → SectionCount.Statement → ∀ (F : Type) [Field F] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] [Algebra F Ω] (y : (Σ k, ι k) → Ω) (k₀ : K) (d : ℕ) (μ : K → ℤ), IsModelWithBase F y k₀ → GroundTheory.Heights₂.Heights.FieldNumbers.relDim (mIdealOver F y) = ((d + 1 : ℕ) : WithBot (WithTop ℤ)) → IsNef F y μ → 0 < GroundTheory.Heights₂.Heights.NumbersDVR.intNum F (mIdealOver F y) (fun _ : Fin (d + 1) => μ) → ∃ a m : ℕ, 1 ≤ a ∧ 1 ≤ m ∧ ∃ σ ∈ secOver F y (a • μ - (m : ℤ) • baseDeg k₀), σ ≠ 0) :
    VeryAmpleNefPlusAmple.Statement → SectionCount.Statement → ∀ (F : Type) [Field F] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] [Algebra F Ω] (y : (Σ k, ι k) → Ω) (d : ℕ) (μ : K → ℤ), (∀ k, ∃ i, y ⟨k, i⟩ ≠ 0) → GroundTheory.Heights₂.Heights.FieldNumbers.relDim (mIdealOver F y) = ((d + 1 : ℕ) : WithBot (WithTop ℤ)) → IsNef F y μ → 0 < GroundTheory.Heights₂.Heights.NumbersDVR.intNum F (mIdealOver F y) (fun _ : Fin (d + 1) => μ) → ∃ a : ℕ, 1 ≤ a ∧ ∃ σ ∈ secOver F y (a • μ - 1), σ ≠ 0 := by
  intro hK hS F _ K _ _ ι _ Ω _ _ y d μ hy hd hnef hpos
  obtain ⟨a, m, ha, hm, σ, hσ, hσ0⟩ := hbase hK hS F (Unit ⊕ K) _ Ω (segreJoin y) (Sum.inl ()) d
    (pullDeg μ) (SegreBase.proof F K ι Ω y hy).1
    ((SegreDim.proof F K ι Ω y hy).trans hd)
    ((SegreNef.proof SegreDim.proof SegreNum.proof F K ι Ω y hy μ).2 hnef)
    (lt_of_lt_of_eq hpos (SegreNum.proof F K ι Ω y hy (d + 1) (fun _ => μ)).symm)
  have e : a • pullDeg (K₁ := Unit) μ - (m : ℤ) • baseDeg (Sum.inl ()) =
      pullDeg (a • μ) + (-(m : ℤ)) • baseDeg (Sum.inl ()) := by
    rw [neg_smul, ← sub_eq_add_neg]
    congr 1
    funext k
    cases k <;> simp [pullDeg]
  rw [e, SegreTwist.proof F K ι Ω y hy] at hσ
  choose i hi using hy
  have hp := ModelTwistGenerated.pow_mem_secOver y (prod_mem_secOver (F := F) y i) (m - 1)
  have hmul := ModelTwistGenerated.secOver_mul y hσ hp
  have e' : ((a • μ + fun _ => -(m : ℤ)) + ((m - 1 : ℕ) : ℤ) • (1 : K → ℤ)) = a • μ - 1 := by
    funext k
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, Pi.one_apply, smul_eq_mul, Nat.cast_sub hm]
    push_cast
    ring
  rw [e'] at hmul
  exact ⟨a, ha, _, hmul, mul_ne_zero hσ0 (pow_ne_zero _ (Finset.prod_ne_zero_iff.mpr fun k _ => hi k))⟩

theorem siu_segre_of (hnum : ∀ (M : Type) [AddCommGroup M] (d : ℕ) (f : MultilinearMap ℤ (fun _ : Fin (d + 1) => M) ℤ) (μ e : M), 0 < f (fun _ => μ) → ∃ t : ℚ, 0 < t ∧ ∀ (a : ℕ) (m : ℤ), 1 ≤ a → (m : ℚ) = a * t → ((d + 1 : ℕ) : ℤ) * f (Fin.snoc (α := fun _ => M) (fun _ : Fin d => a • μ + m • e) ((2 * m) • e)) < f (fun _ => a • μ + m • e)) :
    VeryAmpleNefPlusAmple.Statement → SectionCount.Statement → ∀ (F : Type) [Field F] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] [Algebra F Ω] (y : (Σ k, ι k) → Ω) (d : ℕ) (μ : K → ℤ), (∀ k, ∃ i, y ⟨k, i⟩ ≠ 0) → GroundTheory.Heights₂.Heights.FieldNumbers.relDim (mIdealOver F y) = ((d + 1 : ℕ) : WithBot (WithTop ℤ)) → IsNef F y μ → 0 < GroundTheory.Heights₂.Heights.NumbersDVR.intNum F (mIdealOver F y) (fun _ : Fin (d + 1) => μ) → ∃ a : ℕ, 1 ≤ a ∧ ∃ σ ∈ secOver F y (a • μ - 1), σ ≠ 0 :=
  siu_segre_of_base (siu_base_of hnum)

end PositivityTheory.HtPt.Siub
end

