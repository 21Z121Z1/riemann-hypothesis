import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0089
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.BiextChangeSecondFactor
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ConjugateHermitianLineIsometries
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterRes
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.RationalSections.ThmISt
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PCoordConeArithVar
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.Assembly
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.GermSys
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsFlatAnIffIsConstMul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0090
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0068
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0091
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.AdelicGroupAlgebraActionInjective
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0005
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0002
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.GlueApplyOfNotInFibre
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.QQuasiCompact
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0014
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0004
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0011
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0015
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0007
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.Bundle0001
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterBridge

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.IntersectionHiddenFirst
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Fl
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CompanionTheory.Ar.Flat.DegZ

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Flat.DegZ.IsoMap

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB.LogPf ReciprocityTheory.ChartRestriction.G.PullbackSections.CVA

variable {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) {d : ℕ}

def Zp {n : ℕ} (a : Pt R n d) : Prop := ∀ i, constantCoeff (a i) = 0

theorem zp_pt {n : ℕ} (j : Fin n) : Zp (pt R d j) := fun i => by
  show constantCoeff (X (j, i) : PS R n d) = 0
  simp

theorem zp_zero {n : ℕ} : Zp (0 : Pt R n d) := fun i => by simp

theorem zp_comp1 {n : ℕ} {φ : Pt R 1 d} {a : Pt R n d} (hφ : Zp φ) (ha : Zp a) : Zp (comp1 φ a) :=
  fun i => constantCoeff_ev (CZ.cons ha CZ.nil) (hφ i)

theorem zp_mP {n : ℕ} {a : Pt R n d} (ha : Zp a) : Zp (mP f a) := fun i => by
  have h : coeff (0 : Fin n × Fin d →₀ ℕ) (MvPowerSeries.map f (a i)) = f (coeff 0 (a i)) := coeff_map _ _ _
  rw [coeff_zero_eq_constantCoeff_apply, coeff_zero_eq_constantCoeff_apply, ha i, map_zero] at h
  exact h

theorem map_ev1 {n : ℕ} {a : Pt R n d} (ha : Zp a) (g : PS R 1 d) :
    MvPowerSeries.map f (ev ![a] g) = ev ![mP f a] (MvPowerSeries.map f g) := by
  rw [map_ev' f (CZ.cons ha CZ.nil), mV_cons, mV_nil]

theorem map_ev2 {n : ℕ} {a b : Pt R n d} (ha : Zp a) (hb : Zp b) (g : PS R 2 d) :
    MvPowerSeries.map f (ev ![a, b] g) = ev ![mP f a, mP f b] (MvPowerSeries.map f g) := by
  rw [map_ev' f (CZ.cons ha (CZ.cons hb CZ.nil)), mV_cons, mV_cons, mV_nil]

theorem map_ev3 {n : ℕ} {a b c : Pt R n d} (ha : Zp a) (hb : Zp b) (hc : Zp c) (g : PS R 3 d) :
    MvPowerSeries.map f (ev ![a, b, c] g) = ev ![mP f a, mP f b, mP f c] (MvPowerSeries.map f g) := by
  rw [map_ev' f (CZ.cons ha (CZ.cons hb (CZ.cons hc CZ.nil))), mV_cons, mV_cons, mV_cons, mV_nil]

theorem mapPoint_comp1' {n : ℕ} (φ : Pt R 1 d) {a : Pt R n d} (ha : Zp a) :
    mP f (comp1 φ a) = comp1 (mP f φ) (mP f a) := by
  funext i
  exact map_ev1 f ha (φ i)

variable {O : Type} [CommRing O] [StarRing O]

theorem zp_add (B : Germ.FB R d O) {n : ℕ} {a b : Pt R n d} (ha : Zp a) (hb : Zp b) : Zp (B.G.add a b) :=
  fun i => constantCoeff_ev (CZ.cons ha (CZ.cons hb CZ.nil)) (B.G.const i)

theorem zp_act (B : Germ.FB R d O) (a : O) : Zp (B.A.act a) := B.A.const a

variable {f} {B : Germ.FB R d O} {C : Germ.FB S d O}

theorem mapPoint_add (h : IsMapOf f B C) {n : ℕ} {a b : Pt R n d} (ha : Zp a) (hb : Zp b) :
    mP f (B.G.add a b) = C.G.add (mP f a) (mP f b) := by
  funext i
  show MvPowerSeries.map f (ev ![a, b] (B.G.F i)) = ev ![mP f a, mP f b] (C.G.F i)
  rw [h.F, map_ev2 f ha hb]

theorem mapPoint_act (h : IsMapOf f B C) (a : O) : mP f (B.A.act a) = C.A.act a := by
  funext i
  exact (h.act a i).symm

theorem isIso_mP {B₂ : Germ.FB R d O} {C₂ : Germ.FB S d O} {φ ψ : Germ.Pt R 1 d} {lam : Germ.PS R 2 d}
    (h₁ : IsMapOf f B C) (h₂ : IsMapOf f B₂ C₂) (I : IsIso B B₂ φ ψ lam) :
    IsIso C C₂ (mP f φ) (mP f ψ) (MvPowerSeries.map f lam) := by
  have hφ : Zp φ := I.c₁
  have hψ : Zp ψ := I.c₂
  refine ⟨zp_mP f hφ, zp_mP f hψ, ?_, ?_, ⟨?_, ?_⟩, ?_, fun a => ?_, ?_, ?_, ?_, fun a => ?_⟩
  · have h := congrArg (mP f) I.inv₁
    rwa [mapPoint_comp1' f _ hψ, mapPoint_pt] at h
  · have h := congrArg (mP f) I.inv₂
    rwa [mapPoint_comp1' f _ hφ, mapPoint_pt] at h
  · have h := congrArg (MvPowerSeries.map f) I.ax.1
    simpa only [map_ev2 f zp_zero (zp_pt 0), mapPoint_zero f, mapPoint_pt, map_one] using h
  · have h := congrArg (MvPowerSeries.map f) I.ax.2
    simpa only [map_ev2 f (zp_pt 0) zp_zero, mapPoint_zero f, mapPoint_pt, map_one] using h
  · have h := congrArg (mP f) I.law
    simp only [mapPoint_comp1' f _ (zp_add _ (zp_pt _) (zp_pt _)), mapPoint_comp1' f _ (zp_pt _),
      mapPoint_add h₁ (zp_comp1 hφ (zp_pt _)) (zp_comp1 hφ (zp_pt _)), mapPoint_add h₂ (zp_pt _) (zp_pt _), mapPoint_pt] at h
    simpa only [mapPoint_comp1' f _ (zp_pt _), mapPoint_pt] using h
  · have h := congrArg (mP f) (I.act a)
    rwa [mapPoint_comp1' f _ (zp_act _ _), mapPoint_comp1' f _ hφ, mapPoint_act h₁, mapPoint_act h₂] at h
  · have h := congrArg (MvPowerSeries.map f) I.ph1
    simp (maxDischargeDepth := 6) only [map_mul, map_ev2 f, map_ev3 f, mapPoint_comp1' f, mapPoint_add h₂, mapPoint_pt,
      ← h₁.ph1, ← h₂.ph1, hφ, zp_pt, zp_comp1, zp_add] at h
    exact h
  · have h := congrArg (MvPowerSeries.map f) I.ph2
    simp (maxDischargeDepth := 6) only [map_mul, map_ev2 f, map_ev3 f, mapPoint_comp1' f, mapPoint_add h₂, mapPoint_pt,
      ← h₁.ph2, ← h₂.ph2, hφ, zp_pt, zp_comp1, zp_add] at h
    exact h
  · have h := congrArg (MvPowerSeries.map f) I.sy
    simp (maxDischargeDepth := 6) only [map_mul, map_ev2 f, mapPoint_comp1' f, mapPoint_pt,
      ← h₁.sy, ← h₂.sy, hφ, zp_pt, zp_comp1] at h
    exact h
  · have h := congrArg (MvPowerSeries.map f) (I.ad a)
    simp (maxDischargeDepth := 6) only [map_mul, map_ev2 f, mapPoint_comp1' f, mapPoint_act h₂, mapPoint_pt,
      ← h₁.ad, ← h₂.ad, hφ, zp_pt, zp_comp1, zp_act] at h
    exact h

end GlobalTheory.CompanionTheory.Ar.Flat.DegZ.IsoMap

namespace GlobalTheory.CompanionTheory.Ar.Flat.DegZ

theorem isIso_map : ∀ (R S : Type) [CommRing R] [CommRing S] (f : R →+* S) (d : ℕ) (O : Type) [CommRing O] [StarRing O]
    (B B₂ : Germ.FB R d O) (C C₂ : Germ.FB S d O) (φ ψ : Germ.Pt R 1 d) (lam : Germ.PS R 2 d),
    IsMapOf f B C → IsMapOf f B₂ C₂ → IsIso B B₂ φ ψ lam →
      IsIso C C₂ (fun i => MvPowerSeries.map f (φ i)) (fun i => MvPowerSeries.map f (ψ i)) (MvPowerSeries.map f lam) := by
  intro R S _ _ f d O _ _ B B₂ C C₂ φ ψ lam h₁ h₂ I
  exact IsoMap.isIso_mP h₁ h₂ I

end GlobalTheory.CompanionTheory.Ar.Flat.DegZ
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsArithVarOfBlockAlgebraic
section
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Cmp

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 ReciprocityTheory.AnForm.M Filter Topology
open ReciprocityTheory.ChartRestriction.G.AI.I1 (IsBlockMap pullDeg)
open Algebra GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.CoordinateConeArithVar

section Dim

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω] [CharZero Ω]

omit [Fintype K] [∀ k, Fintype (ι k)] in

theorem ratioField_eq_blockFnField (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k) (hc : ∀ k, y ⟨k, c k⟩ ≠ 0) :
    ratioField y c = blockFnField y := by
  apply le_antisymm
  · refine IntermediateField.adjoin_le_iff.mpr ?_
    rintro _ ⟨p, rfl⟩
    exact IntermediateField.subset_adjoin _ _ ⟨p, ⟨p.1, c p.1⟩, rfl, rfl⟩
  · refine IntermediateField.adjoin_le_iff.mpr ?_
    rintro _ ⟨p, q, hpq, rfl⟩
    have hp : y p / y ⟨p.1, c p.1⟩ ∈ ratioField y c := IntermediateField.subset_adjoin _ _ ⟨p, rfl⟩
    have hq : y q / y ⟨q.1, c q.1⟩ ∈ ratioField y c := IntermediateField.subset_adjoin _ _ ⟨q, rfl⟩
    have key : y p / y q = (y p / y ⟨p.1, c p.1⟩) / (y q / y ⟨q.1, c q.1⟩) := by
      rw [← hpq]
      have h0 := hc p.1
      by_cases hq0 : y q = 0
      · simp [hq0]
      · field_simp
    rw [key]
    exact div_mem hp hq

theorem ringKrullDim_coord (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k) (hc : ∀ k, y ⟨k, c k⟩ ≠ 0) :
    ringKrullDim (MRing ι ⧸ mCoordIdeal y) =
      (((Algebra.trdeg ℤ (blockFnField y) + (Fintype.card K : Cardinal)).toENat + 1 : ℕ∞) : WithBot ℕ∞) := by
  haveI hP : (mCoordIdeal y).IsPrime := RingHom.ker_isPrime (mConeMap y)
  have hdim := GroundTheory.Heights₂.Heights.IntDomainDim.full (MRing ι ⧸ mCoordIdeal y)
    (algebraMap_injective _ (horizontal y))
  have hne : ∀ k, ∃ i, ratioPtL y c ⟨k, i⟩ ≠ 0 := by
    intro k
    refine ⟨c k, fun h0 => ?_⟩
    have h1 := congrArg Subtype.val h0
    change ratioPt y c ⟨k, c k⟩ = 0 at h1
    simp [ratioPt, hc k] at h1
  have htr := GroundTheory.Heights₂.Heights.ConeTrdeg.full K ι (ratioField y c) (ratioPtL y c)
    (birational y c hc) hne (horizontal _)
  rw [mCoordIdeal_ratioPtL y c hc] at htr
  rw [hdim, htr, ratioField_eq_blockFnField y c hc]

omit [Fintype K] [∀ k, Fintype (ι k)] in

theorem trdeg_eq_of_le_of_isAlgebraic {L₁ L₂ : IntermediateField ℚ Ω} (h : L₁ ≤ L₂)
    (halg : ∀ t ∈ L₂, IsAlgebraic L₁ t) : Algebra.trdeg ℤ L₂ = Algebra.trdeg ℤ L₁ := by
  letI : Algebra L₁ L₂ := (IntermediateField.inclusion h).toRingHom.toAlgebra
  let f : L₂ →ₐ[L₁] Ω :=
    { toRingHom := L₂.val.toRingHom
      commutes' := fun _ => rfl }
  haveI : Algebra.IsAlgebraic L₁ L₂ :=
    ⟨fun x => (isAlgebraic_algHom_iff f Subtype.val_injective).mp (halg x x.2)⟩
  have h0 : trdeg L₁ L₂ = 0 := trdeg_eq_zero
  rw [← trdeg_add_eq (R := ℤ) (S := L₁) (A := L₂), h0, add_zero]

end Dim

theorem isArithVar_of_isAlgebraic_image (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (K' : Type)
    [Fintype K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)] (κ : K → K') (v : (Σ k, ι k) → Σ k, ι' k) (Ω : Type)
    [Field Ω] [CharZero Ω] (y : (Σ k, ι' k) → Ω) (d : ℕ) (hv : IsBlockMap κ v)
    (hy : ∀ k, ∃ i, y ⟨k, i⟩ ≠ 0) (hz : IsArithVar (mCoordIdeal (y ∘ v)) d)
    (halg : ∀ t ∈ blockFnField y, IsAlgebraic (blockFnField (y ∘ v)) t) : IsArithVar (mCoordIdeal y) d := by
  classical
  obtain ⟨hK, -, -, hdz⟩ := hz
  obtain ⟨hκ, -, hfst, hsurj⟩ := hv
  choose c' hc' using hy
  have hcv : ∀ k : K, ∃ i : ι k, (y ∘ v) ⟨k, i⟩ ≠ 0 := by
    intro k
    obtain ⟨⟨k', i⟩, hp⟩ := hsurj ⟨κ k, c' (κ k)⟩ ⟨k, rfl⟩
    have h2 : k' = k := by
      apply hκ
      have h3 := hfst ⟨k', i⟩
      rw [hp] at h3
      exact h3.symm
    subst h2
    exact ⟨i, fun h0 => hc' _ (by rw [← hp]; exact h0)⟩
  choose c hc using hcv
  have e1 := hdz.symm.trans (ringKrullDim_coord (y ∘ v) c hc)
  have hle : blockFnField (y ∘ v) ≤ blockFnField y := by
    refine IntermediateField.adjoin_le_iff.mpr ?_
    rintro _ ⟨p, q, hpq, rfl⟩
    exact IntermediateField.subset_adjoin _ _ ⟨v p, v q, by rw [hfst, hfst, hpq], rfl⟩
  have htr := trdeg_eq_of_le_of_isAlgebraic hle halg
  unfold IsArithVar IsMultiProjPrime
  refine ⟨⟨κ hK.some⟩, ⟨RingHom.ker_isPrime (mConeMap y), isMultiHomogIdeal y, relevant y c' hc'⟩,
    horizontal y, ?_⟩
  rw [ringKrullDim_coord y c' hc', htr]
  generalize Algebra.trdeg ℤ ↥(blockFnField (y ∘ v)) = T at e1 ⊢
  simp only [map_add, map_natCast] at e1 ⊢
  generalize Cardinal.toENat T = e at e1 ⊢
  induction e using ENat.recTopCoe with
  | top =>
    exfalso
    have h5 : ((d + Fintype.card K : ℕ) : ℕ∞) = ⊤ := by exact_mod_cast e1
    exact ENat.natCast_ne_top _ h5
  | coe m =>
    norm_cast at e1 ⊢
    omega

end GlobalTheory.CompanionTheory.Ar.Cmp
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsCombTangentIffLinearSum
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Fl
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CompanionTheory.Ar.Flat.CPoint

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Flat.CPoint

theorem isComb_lieModel_pt_iff : ∀ (S : Scheme.{0}) (R : Type) [CommRing R] (G : Over S) [GrpObj G] [IsCommMonObj G] (x : Sp R ⟶ S) (Em : Type)
    [AddCommGroup Em] [Module R Em] (M : LieModel G x Em) (n : ℕ) (b : Fin n → Em) (cf : Fin n → R) (e : Em),
    IsComb cf (fun i => M.pt (b i)) (M.pt e) ↔ e = ∑ i, cf i • b i := by
  intro S R _ G _ _ x Em _ _ M n b cf e
  have hu : ∀ u : Fin n → (epsAt x ⟶ G),
      (∀ i, (u i).left = spMap (epsMul (cf i)) ≫ (M.pt (b i)).left) ↔ u = fun i => M.pt (cf i • b i) := by
    intro u
    constructor
    · intro h
      funext i
      exact Over.OverMorphism.ext ((h i).trans (M.smul _ _).symm)
    · rintro rfl i
      exact M.smul _ _
  have h0 : M.pt 0 = 1 := by
    have h := M.add 0 0
    rw [add_zero] at h
    exact mul_left_cancel (h.symm.trans (_root_.mul_one _).symm)
  have hsum : ∀ (m : ℕ) (f : Fin m → Em), M.pt (∑ i, f i) = (List.ofFn fun i => M.pt (f i)).prod := by
    intro m f
    induction m with
    | zero => rw [Finset.univ_eq_empty, Finset.sum_empty, List.ofFn_zero, List.prod_nil, h0]
    | succ m ih => rw [Fin.sum_univ_succ, List.ofFn_succ, List.prod_cons, M.add, ih]
  constructor
  · rintro ⟨u, hu1, hu2⟩
    rw [(hu u).1 hu1] at hu2
    apply M.inj
    rw [hu2]
    exact (hsum n (fun i => cf i • b i)).symm
  · intro he
    refine ⟨fun i => M.pt (cf i • b i), (hu _).2 rfl, ?_⟩
    rw [he]
    exact hsum n (fun i => cf i • b i)

end GlobalTheory.CompanionTheory.Ar.Flat.CPoint
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelPullbackCorrespondenceStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lie_model_pullback_correspondence : ∀ (R : Type) [CommRing R] (X : Scheme.{0}) (x : Sp R ⟶ X) (G : Over X) [GrpObj G] (G₀ : Over (Sp R)) [GrpObj G₀] (ψ : G₀.left ⟶ G.left) (L : Type) [AddCommGroup L] [Module R L], IsGrpPullback G₀ G x ψ → (∀ M : LieModel G x L, ∃ M₀ : LieModel G₀ (𝟙 _) L, ∀ e, (M₀.pt e).left ≫ ψ = (M.pt e).left) ∧ ∀ M₀ : LieModel G₀ (𝟙 _) L, ∃ M : LieModel G x L, ∀ e, (M₀.pt e).left ≫ ψ = (M.pt e).left := by
  first | exact @GlobalTheory.CompanionTheory.Ar.LieMove.main | exact GlobalTheory.CompanionTheory.Ar.LieMove.main | (intros; apply GlobalTheory.CompanionTheory.Ar.LieMove.main <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.NumberFieldEmbeddingsIntoCpIntegral
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Fl
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CompanionTheory.Ar.Flat.CPoint

noncomputable section
namespace GlobalTheory.CompanionTheory.Ar.Flat.CPoint

theorem embeddings_padicComplex : ∀ (E : Type) [Field E] [NumberField E] (p : Nat.Primes),
    (∀ (s : E →+* ℂ_[p]) (a : 𝓞 E), s (a : E) ∈ (algebraMap (OCp p) ℂ_[p]).range) ∧
      Nat.card (E →+* ℂ_[p]) = Module.finrank ℚ E := by
  intro E _ _ p
  refine ⟨fun s a => ?_, ?_⟩
  · have hO : IsIntegral (OCp p) (s (a : E)) :=
      (RingOfIntegers.isIntegral_coe a).map_of_comp_eq (Int.castRingHom (OCp p)) s (RingHom.ext_int _ _)
    have hv := Valuation.valuationSubring.integers (v := NormedField.valuation (K := ℂ_[p]))
    exact hv.exists_of_le_one (hv.isIntegral_iff_v_le_one.mp hO)
  · rw [Nat.card_eq_fintype_card]
    exact NumberField.Embeddings.card E ℂ_[p]

end GlobalTheory.CompanionTheory.Ar.Flat.CPoint
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ProperHasPowerFns
section
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Conj.ProperPowFns

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Fl
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem powFns_of_proper_algClosed : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (k : Type) [Field k] [IsAlgClosed k] (tB : SAB H (Sp k)), IsProper tB.G.hom → PowFns tB :=
  fun _ _ _ _ _ _ _ _ tB hp n =>
    haveI := hp
    AbelianSchemeGerms.globalFns_powObj GlobalTheory.globalFns_holds tB.G tB.semi n

end GlobalTheory.CompanionTheory.Ar.Conj.ProperPowFns
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.QuasiFiniteGroupFiniteStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.quasi_finite_group_finite : ∀ (R : Type) [CommRing R] [IsDomain R] (T : Type) [CommGroup T] (Γ : BT.QFGroup R T), Finite T := by
  first | exact @GlobalTheory.CompanionTheory.Ar.BT.QFGroup.finite_of_qfGroup | exact GlobalTheory.CompanionTheory.Ar.BT.QFGroup.finite_of_qfGroup | (intros; apply GlobalTheory.CompanionTheory.Ar.BT.QFGroup.finite_of_qfGroup <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ReduceLatticeActionToResidue
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Fl
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CompanionTheory.Ar.Flat.CPoint

noncomputable section
namespace GlobalTheory.CompanionTheory.Ar.Flat.CPoint

section EvalRank

variable {E : Type} [Field E] [NumberField E]

theorem trace_eigProj {K V : Type} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (ρ : 𝓞 E →+* Module.End K V) (σ : E →+* K) :
    LinearMap.trace K V (HT.eigProj ρ σ) = (Module.finrank K (HT.eigSp ρ σ) : K) := by
  have h : LinearMap.IsProj (HT.eigSp ρ σ) (HT.eigProj ρ σ) :=
    ⟨fun x => HT.LatBasic.eigProj_mem ρ σ x, fun x hx => HT.LatBasic.eigProj_of_mem hx⟩
  exact h.trace

theorem trace_eigProj_eq_sum {K V : Type} [Field K] [AddCommGroup V] [Module K V]
    (ρ : 𝓞 E →+* Module.End K V) (σ : E →+* K) :
    LinearMap.trace K V (HT.eigProj ρ σ) =
      ∑ k, σ (HT.dualInt E k) * LinearMap.trace K V (ρ (RingOfIntegers.basis E k)) := by
  simp [HT.eigProj, map_sum, map_smul]

variable {Ω Vs C : Type} [Field Ω] [AddCommGroup Vs] [Module Ω Vs] [Field C]

theorem comb_single {R : Subring Ω} {g : ℕ} (ℓ : Fin g → Vs) (j : Fin g) :
    comb (R := R) ℓ (Pi.single j 1) = ℓ j := by
  classical
  unfold comb
  rw [Finset.sum_eq_single j (fun i _ h => by simp [Pi.single_apply, h]) (by simp)]
  simp

theorem exists_comb {R : Subring Ω} {g : ℕ} {ℓ : Fin g → Vs} {v : Vs}
    (h : v ∈ Submodule.span R (Set.range ℓ)) : ∃ x : Fin g → R, v = comb ℓ x := by
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun R).1 h
  exact ⟨c, by rw [← hc]; rfl⟩

theorem trace_of_comb {R : Subring Ω} {g : ℕ} {ℓ : Fin g → Vs} (hl : LinearIndependent Ω ℓ)
    (hs : Submodule.span Ω (Set.range ℓ) = ⊤) (f : Module.End Ω Vs) (x : Fin g → Fin g → R)
    (hx : ∀ j, f (ℓ j) = comb ℓ (x j)) :
    LinearMap.trace Ω Vs f = ((∑ j, x j j : R) : Ω) := by
  classical
  set b := Module.Basis.mk hl hs.ge with hb
  have hbj : ∀ j, b j = ℓ j := fun j => by simp [hb]
  rw [LinearMap.trace_eq_matrix_trace Ω b f, Matrix.trace]
  push_cast
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Matrix.diag_apply, LinearMap.toMatrix_apply, hbj, hx j, comb]
  simp only [← hbj, map_sum, map_smul, Module.Basis.repr_self]
  simp [Finsupp.single_apply]

theorem trace_of_cols {g : ℕ} (f : Module.End C (Fin g → C)) (y : Fin g → Fin g → C)
    (hy : ∀ j, f (Pi.single j 1) = y j) :
    LinearMap.trace C (Fin g → C) f = ∑ j, y j j := by
  classical
  rw [LinearMap.trace_eq_matrix_trace C (Pi.basisFun C (Fin g)) f, Matrix.trace]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Matrix.diag_apply, LinearMap.toMatrix_apply]
  simp [hy j]

end EvalRank

theorem finrank_eigSp_eval : ∀ (E : Type) [Field E] [NumberField E] (Ω Vs C : Type) [Field Ω] [CharZero Ω] [AddCommGroup Vs] [Module Ω Vs]
    [FiniteDimensional Ω Vs] [Field C] [CharZero C] (ρ : 𝓞 E →+* Module.End Ω Vs) (R' : Subring Ω) (g : ℕ)
    (ℓ : Fin g → Vs) (ψ : R' →+* C) (ρC : 𝓞 E →+* Module.End C (Fin g → C)) (σ : E →+* Ω) (σC : E →+* C),
    LinearIndependent Ω ℓ → Submodule.span Ω (Set.range ℓ) = ⊤ →
    (∀ a i, ρ a (ℓ i) ∈ Submodule.span R' (Set.range ℓ)) → Tied ℓ ψ ρ ρC →
    (∀ e : E, ∃ h : σ e ∈ R', ψ ⟨σ e, h⟩ = σC e) →
    Module.finrank C (HT.eigSp ρC σC) = Module.finrank Ω (HT.eigSp ρ σ) := by
  intro E _ _ Ω Vs C _ _ _ _ _ _ _ ρ R' g ℓ ψ ρC σ σC hl hs hst hT hσ
  classical
  choose M hM using fun (a : 𝓞 E) (j : Fin g) => exists_comb (hst a j)
  have hC : ∀ a j, ρC a (Pi.single j 1) = fun i => ψ (M a j i) := by
    intro a j
    have := hT a (Pi.single j 1) (M a j) (by rw [comb_single]; exact hM a j)
    rw [← this]
    congr 1
    ext i
    by_cases h : i = j
    · subst h; simp
    · simp [Pi.single_apply, h]
  have tΩ : ∀ a, LinearMap.trace Ω Vs (ρ a) = ((∑ j, M a j j : R') : Ω) :=
    fun a => trace_of_comb hl hs (ρ a) (M a) (hM a)
  have tC : ∀ a, LinearMap.trace C (Fin g → C) (ρC a) = ψ (∑ j, M a j j) := by
    intro a
    rw [trace_of_cols (ρC a) (fun j i => ψ (M a j i)) (hC a), map_sum]
  set T : R' := ∑ k, ⟨σ (HT.dualInt E k), (hσ _).1⟩ * ∑ j, M (RingOfIntegers.basis E k) j j with hTdef
  have h1 : (Module.finrank Ω (HT.eigSp ρ σ) : Ω) = (T : Ω) := by
    rw [← trace_eigProj, trace_eigProj_eq_sum, hTdef]
    push_cast
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [tΩ]
    push_cast
    rfl
  have h2 : T = (Module.finrank Ω (HT.eigSp ρ σ) : R') := by
    apply Subtype.ext
    rw [← h1]
    simp
  have h3 : (Module.finrank C (HT.eigSp ρC σC) : C) = ψ T := by
    rw [← trace_eigProj, trace_eigProj_eq_sum, hTdef, map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [tC, map_mul]
    congr 1
    exact ((hσ _).2).symm
  rw [h2, map_natCast] at h3
  exact_mod_cast h3

end GlobalTheory.CompanionTheory.Ar.Flat.CPoint
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ResolutionStatementHolds
section
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo

namespace GlobalTheory.CompanionTheory.Ar.Link

theorem resBridgeStatement_holds : ReciprocityTheory.ChartRestriction.G.Geo.ResBridgeStatement :=
  ReciprocityTheory.ChartRestriction.G.Geo.resBridge

end GlobalTheory.CompanionTheory.Ar.Link
end

