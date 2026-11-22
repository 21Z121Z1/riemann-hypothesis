import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StableIffCarrierEq
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0208
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0175
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1416
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DsExistsOfDiscreteSeriesExists
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0005
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0279
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FieldValuesMemFixedField
import Formalism.LocalToGlobal.Columns.Bundle0012
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0068
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0004
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0283
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1389
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1098
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0014
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0390
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingSpecNormalisedCharacterEq
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TypeIdempotentCoeffAcrossLayers
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0003
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0132
import Formalism.LocalToGlobal.Columns.Bundle0011

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EigensystemCarriedByFiniteTypeOfMeetsLevelRows
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3
open Classical
open GlobalTheory.Mem.R3.HasLabelling

noncomputable section

namespace GlobalTheory.Mem.R3.LabCarry

theorem inner_eq_zero_of_normal {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H]
    (T : H →ₗ[ℂ] H) (hT : Commute T (LinearMap.adjoint T)) {a b : ℂ} (hab : a ≠ b) {x y : H}
    (hx : T x = a • x) (hy : T y = b • y) : ⟪x, y⟫_ℂ = 0 := by
  set S : H →ₗ[ℂ] H := T - b • LinearMap.id with hS
  have hSy : S y = 0 := by simp [hS, hy]
  have hSadj : LinearMap.adjoint S = LinearMap.adjoint T - (starRingEnd ℂ b) • LinearMap.id := by
    rw [hS, map_sub, LinearEquiv.map_smulₛₗ, LinearMap.adjoint_id]
  have hSc : Commute S (LinearMap.adjoint S) := by
    rw [hSadj, hS]
    have h1 : Commute T (starRingEnd ℂ b • (LinearMap.id : H →ₗ[ℂ] H)) := (Commute.one_right T).smul_right _
    have h2 : Commute (b • (LinearMap.id : H →ₗ[ℂ] H)) (LinearMap.adjoint T) := (Commute.one_left _).smul_left _
    have h3 : Commute (b • (LinearMap.id : H →ₗ[ℂ] H)) (starRingEnd ℂ b • (LinearMap.id : H →ₗ[ℂ] H)) :=
      ((Commute.one_left _).smul_left _).smul_right _
    exact (hT.sub_right h1).sub_left (h2.sub_right h3)
  have hSa : LinearMap.adjoint S y = 0 := by
    have h0 : ⟪LinearMap.adjoint S y, LinearMap.adjoint S y⟫_ℂ = 0 := by
      rw [LinearMap.adjoint_inner_left]
      have : S (LinearMap.adjoint S y) = LinearMap.adjoint S (S y) := by
        have := congrArg (fun f : H →ₗ[ℂ] H => f y) hSc.eq
        simpa [Module.End.mul_apply] using this
      rw [this, hSy, map_zero, inner_zero_right]
    exact inner_self_eq_zero.1 h0
  have hTa : LinearMap.adjoint T y = (starRingEnd ℂ b) • y := by
    have := hSa
    rw [hSadj, LinearMap.sub_apply, sub_eq_zero] at this
    simpa using this
  have key : ⟪T x, y⟫_ℂ = ⟪x, LinearMap.adjoint T y⟫_ℂ := (LinearMap.adjoint_inner_right T x y).symm
  rw [hx, hTa, inner_smul_left, inner_smul_right] at key
  have hne : starRingEnd ℂ a ≠ starRingEnd ℂ b := fun h => hab ((starRingEnd ℂ).injective h)
  have : (starRingEnd ℂ a - starRingEnd ℂ b) * ⟪x, y⟫_ℂ = 0 := by rw [sub_mul, key, sub_self]
  exact (mul_eq_zero.1 this).resolve_left (sub_ne_zero.2 hne)

end GlobalTheory.Mem.R3.LabCarry

namespace GlobalTheory.Mem.R3.LabCarry

theorem twSub_iSup {E I : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] (s : Bool) (V : I → Submodule ℂ E) :
    Tw.sub s (⨆ p, V p) = ⨆ p, Tw.sub s (V p) := by
  refine le_antisymm (fun x hx => ?_) (iSup_le fun p x hx => Submodule.mem_iSup_of_mem (p := V) p hx)
  exact Submodule.iSup_induction V (motive := fun y => Tw.mk s y ∈ ⨆ p, Tw.sub s (V p)) hx
    (fun p y hy => Submodule.mem_iSup_of_mem p hy) (zero_mem _) fun y z hy hz => add_mem hy hz

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

theorem carries_of_eq (R : RealDat3 D A3 Ks) (p : A3.fam3.base3.Ix) {c c' : Pl D.host.E → List ℤ → ℂ}
    (heq : R.EEc c' = R.EEc c) (h : R.Carries p c') : R.Carries p c := by
  have key : ∀ V W : Submodule ℂ R.HE.H, V = W →
      (V ≠ ⊥ ∧ V.map (LinearMap.adjoint (R.Th A3.A.μ0)) ≤
        Submodule.span ℂ (R.jX A3.A.μ0 '' ((A3.rowI A3.A.μ0).inertTypeEigenspaceSum p.1 : Set (A3.A.fam.R A3.A.μ0).S.Forms))) →
      (W ≠ ⊥ ∧ W.map (LinearMap.adjoint (R.Th A3.A.μ0)) ≤
        Submodule.span ℂ (R.jX A3.A.μ0 '' ((A3.rowI A3.A.μ0).inertTypeEigenspaceSum p.1 : Set (A3.A.fam.R A3.A.μ0).S.Forms))) := by
    rintro V W rfl hV; exact hV
  exact key _ _ heq h

end GlobalTheory.Mem.R3.LabCarry

namespace GlobalTheory.Mem.R3.LabCarry

set_option maxHeartbeats 1000000 in

theorem carried : GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.DiscreteSeriesExists → GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.CuspRapidDecay → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd) (X0 : BaseLevelRowSide D) (Y : Read (A3 := A3) R.toRealDat F.lv2 X0) (Z : ReadL R F X0 Y), Pins R F cG → Holds R F → HostHyp D → ∀ (c : Pl D.host.E → List ℤ → ℂ) (b : Bool) (x : R.HE.H), x ≠ 0 → x ∈ R.EEc c → R.HE.e x ∈ R.toRealDat.EEat (R.toRealDat.levR F.lv2 b) → ∃ p, R.Carries p c := by
  intro hWe hDs hHC hCu D G _ _ Pl0 I0 T A3 Ks _ _ _ R F cG X0 Y Z hP hHo hHost c b x hx0 hxc hxb
  by_contra hno
  push_neg at hno
  obtain ⟨hcore, hSF, -, -, hEEc, -, -⟩ := GlobalTheory.CoreThree.heckeCharacterisation_places_parts_of_weak R F hP.char
  obtain ⟨h, -, hN, -, hev, hchar⟩ := GlobalTheory.T.exists_sphericalOperators_rows_normal_eigenspaces R.toRealDat F.lv2 (hcore hHo.aux.ex)
    (GlobalTheory.Hk3.schurAll_of_cuspRapidDecay hCu R.toRealDat) R.SF hSF

  have heig : ∀ c' (y : R.HE.H), y ∈ R.EEc c' → ∀ P d, GlobalTheory.Hk3.Good R.toRealDat A3.A.μ0 P →
      GlobalTheory.Hk3.IsLab (Yc D 0) P d → h P (Finsupp.single d 1) y = c' P (dualLab d) • y := by
    intro c' y hy P d hG hL
    rw [hEEc c'] at hy
    rw [hev c' P hG (Finsupp.single d 1) y hy]
    congr 1
    simp [GlobalTheory.Hk3.evC, Finsupp.sum_single_index, hL]

  have horth : ∀ c', R.EEc c' ≠ R.EEc c → R.EEc c' ≤ (ℂ ∙ x)ᗮ := by
    intro c' hne y hy
    have hex : ∃ P d, GlobalTheory.Hk3.Good R.toRealDat A3.A.μ0 P ∧ GlobalTheory.Hk3.IsLab (Yc D 0) P d ∧
        c' P (dualLab d) ≠ c P (dualLab d) := by
      by_contra hall
      push_neg at hall
      apply hne
      ext z
      constructor
      · intro hz
        rw [hEEc c]
        exact hchar c z fun P d hG hL => by rw [heig c' z hz P d hG hL, hall P d hG hL]
      · intro hz
        rw [hEEc c']
        exact hchar c' z fun P d hG hL => by rw [heig c z hz P d hG hL, hall P d hG hL]
    obtain ⟨P, d, hG, hL, hcc⟩ := hex
    have hT : Commute (h P (Finsupp.single d 1)) (LinearMap.adjoint (h P (Finsupp.single d 1))) := by
      rw [hN.2 P hG]
      exact hN.1 P P hG hG _ _
    rw [Submodule.mem_orthogonal_singleton_iff_inner_right]
    have := inner_eq_zero_of_normal _ hT hcc (heig c' y hy P d hG hL) (heig c x hxc P d hG hL)
    rw [← inner_conj_symm, this, map_zero]

  have hpart : ∀ p, R.EEp3 p ≤ (ℂ ∙ x)ᗮ := by
    intro p
    unfold RealDat3.EEp3
    refine iSup₂_le fun c' hc' => horth c' fun heq => hno p ?_
    exact carries_of_eq R p heq hc'

  have hxT : (Tw.mk (twAt D.what₂.embLL A3.A.v0) x : Tw (twAt D.what₂.embLL A3.A.v0) R.HE.H) ∈ (R.toCx3 F).EEl b := hxb
  rw [← (hHo.prim.sumE b).2] at hxT
  have hxS : x ∈ ⨆ p, R.EEp3 p := by
    have h1 : (Tw.mk (twAt D.what₂.embLL A3.A.v0) x : Tw (twAt D.what₂.embLL A3.A.v0) R.HE.H) ∈
        Tw.sub (twAt D.what₂.embLL A3.A.v0) (⨆ p, R.EEp3 p) := by
      rw [twSub_iSup]
      have hle : (⨆ p, (R.toCx3 F).EEp p ⊓ (R.toCx3 F).EEl b) ≤
          ⨆ p, Tw.sub (twAt D.what₂.embLL A3.A.v0) (R.EEp3 p) := iSup_mono fun p => inf_le_left
      exact hle hxT
    exact h1
  have hself : x ∈ (ℂ ∙ x)ᗮ := (iSup_le hpart) hxS
  rw [Submodule.mem_orthogonal_singleton_iff_inner_right] at hself
  exact hx0 (inner_self_eq_zero.1 hself)

end GlobalTheory.Mem.R3.LabCarry
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsAlgebraicRootsCoeffFieldContainsTwistValue
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.Col2

noncomputable section

namespace GlobalTheory.Mem.Col2.RootsIn

open NumberField IsDedekindDomain Formalism.L2.DIV GlobalTheory.Mem.Col2
open ReciprocityTheory.Neutral.Bridge.HCFR Neutral.B1

def finOr {α : Type} (s : Set α) : Finset α := by
  classical
  exact if h : s.Finite then h.toFinset else ∅

theorem mem_finOr {α : Type} {s : Set α} (h : s.Finite) {x : α} : x ∈ finOr s ↔ x ∈ s := by
  unfold finOr
  rw [dif_pos h, Set.Finite.mem_toFinset]

def rootN (N : ℕ) : ℂ := Complex.exp (2 * Real.pi * Complex.I / N)

theorem rootN_isAlgebraic (N : ℕ) : IsAlgebraic ℚ (rootN N) := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp only [rootN, Nat.cast_zero, div_zero, Complex.exp_zero]
    exact isAlgebraic_one
  · have h : rootN N ^ N = 1 := (Complex.isPrimitiveRoot_exp N hN.ne').pow_eq_one
    exact (IsIntegral.of_pow hN (by rw [h]; exact isIntegral_one)).isAlgebraic

def ramSet {E : Type} [Field E] [NumberField E] (χ : Formalism.L2.Host.HChar E) : Set (HeightOneSpectrum (𝓞 E)) :=
  {Q | ¬ χ.UnrAt Q}

def overN {E : Type} [Field E] [NumberField E] (n : ℕ) : Set (HeightOneSpectrum (𝓞 E)) :=
  {Q' | ((n : ℕ) : 𝓞 E) ∈ Q'.asIdeal}

def rootsOf {E : Type} [Field E] [NumberField E] (χ : Formalism.L2.Host.HChar E) : Finset ℂ := by
  classical
  exact (finOr (ramSet χ)).biUnion fun Q =>
    (finOr (overN (E := E) (Ideal.absNorm Q.asIdeal))).image fun Q' => rootN (Nat.card (kP Q'))

def Sv (P : Pre) (Ξ : Set (Formalism.L2.Host.HChar P.host.E)) : Finset ℂ := by
  classical
  exact (finOr Ξ).biUnion rootsOf

theorem isAlgebraic_of_mem_Sv (P : Pre) (Ξ : Set (Formalism.L2.Host.HChar P.host.E)) (z : ℂ) (hz : z ∈ Sv P Ξ) : IsAlgebraic ℚ z := by
  unfold Sv at hz
  obtain ⟨χ, -, hχ⟩ := Finset.mem_biUnion.1 hz
  unfold rootsOf at hχ
  obtain ⟨Q, -, hQ⟩ := Finset.mem_biUnion.1 hχ
  obtain ⟨Q', -, rfl⟩ := Finset.mem_image.1 hQ
  exact rootN_isAlgebraic _

theorem ramSet_finite {E : Type} [Field E] [NumberField E] (χ : Formalism.L2.Host.HChar E) : (ramSet χ).Finite := by
  have h := GlobalTheory.HeckeSplit.eventually_unrAt χ.1 χ.2.1
  rw [Filter.eventually_cofinite] at h
  refine h.subset fun Q hQ => ?_
  simp only [ramSet, Set.mem_setOf_eq] at hQ ⊢
  rwa [GlobalTheory.HeckeSplit.unrAt_iff]

theorem overN_finite {E : Type} [Field E] [NumberField E] {n : ℕ} (hn : n ≠ 0) : (overN (E := E) n).Finite := by
  have hne : (Ideal.span {((n : ℕ) : 𝓞 E)} : Ideal (𝓞 E)) ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact_mod_cast hn
  refine (Ideal.finite_factors hne).subset fun Q hQ => ?_
  simp only [overN, Set.mem_setOf_eq] at hQ ⊢
  rw [Ideal.dvd_iff_le, Ideal.span_singleton_le_iff_mem]
  exact hQ

theorem exists_ram {F E K : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [Field K] {σ : K →+* ℂ}
    {μ : Chr F E K} {ξ : Formalism.L2.Host.HChar E} (h : Reads σ μ ξ) {v : HeightOneSpectrum (𝓞 F)} (hv : v ∈ Qprime μ) :
    ∃ Q : HeightOneSpectrum (𝓞 E), Q.under (𝓞 F) = v ∧ ¬ ξ.UnrAt Q := by
  by_contra hne
  push_neg at hne
  simp only [Qprime, Set.mem_setOf_eq] at hv
  apply hv
  intro x hx
  rw [MonoidHom.mem_ker]
  obtain ⟨a, rfl⟩ := finAf_surjective F E x
  simp only [inertAt, Subgroup.mem_inf] at hx
  obtain ⟨hx1, hx2⟩ := hx

  have hcomp : ∀ P : HeightOneSpectrum (𝓞 E),
      ((GlobalTheory.HeckeSplit.finPart E P a : (P.adicCompletion E)ˣ) : P.adicCompletion E) =
        afIso F E (finAf F E a : AfE F E) P := by
    intro P
    rw [afIso_finAf]
    rfl

  have key : ξ.1 a = ξ.1 (GlobalTheory.HeckeSplit.infIdele E (GlobalTheory.HeckeSplit.infPart E a)) := by
    rw [GlobalTheory.HeckeSplit.char_eq_prod_local ξ.1 ξ.2.1 a ∅ ?_, Finset.prod_empty, mul_one]
    intro P _
    by_cases hPv : P.under (𝓞 F) = v
    · apply (GlobalTheory.HeckeSplit.unrAt_iff E ξ P).2 (hne P hPv)
      rw [hcomp]
      simp only [intU, Submonoid.mem_units_iff] at hx1
      have h1 := (mem_rInt_iff F E _).1 hx1.1 P
      have h2 := (mem_rInt_iff F E _).1 hx1.2 P
      have hprod : afIso F E (finAf F E a : AfE F E) P *
          afIso F E (((finAf F E a)⁻¹ : (AfE F E)ˣ) : AfE F E) P = 1 := by
        have h : afIso F E ((finAf F E a : AfE F E) * (((finAf F E a)⁻¹ : (AfE F E)ˣ) : AfE F E)) P = 1 := by
          rw [Units.mul_inv, map_one]
          rfl
        rw [map_mul] at h
        exact h
      have hv' : Valued.v (afIso F E (finAf F E a : AfE F E) P) *
          Valued.v (afIso F E (((finAf F E a)⁻¹ : (AfE F E)ˣ) : AfE F E) P) = 1 := by
        rw [← map_mul, hprod, map_one]
      refine le_antisymm h1 ?_
      calc (1 : _) = _ := hv'.symm
        _ ≤ Valued.v (afIso F E (finAf F E a : AfE F E) P) * 1 := by gcongr
        _ = _ := mul_one _
    · have h1 : GlobalTheory.HeckeSplit.finPart E P a = 1 := by
        apply Units.ext
        rw [hcomp, Units.val_one]
        exact (mem_suppAt_iff F E v _).1 hx2 P hPv
      rw [h1, map_one, map_one]
  have hb : finAf F E (GlobalTheory.HeckeSplit.infIdele E (GlobalTheory.HeckeSplit.infPart E a)) = 1 := by
    apply Units.ext
    apply (afIso F E).injective
    rw [afIso_finAf, Units.val_one, map_one]
    rfl
  have e1 := h a
  have e2 := h (GlobalTheory.HeckeSplit.infIdele E (GlobalTheory.HeckeSplit.infPart E a))
  rw [hb, map_one, Units.val_one, map_one] at e2
  rw [key, e2] at e1
  apply Units.ext
  rw [Units.val_one]
  apply σ.injective
  rw [map_one]
  exact e1.symm

end GlobalTheory.Mem.Col2.RootsIn

open GlobalTheory.Mem.Col2.RootsIn in

theorem GlobalTheory.Mem.Col2.exists_roots_valsIn : ∃ Sv : ∀ P : Pre, Set (Formalism.L2.Host.HChar P.host.E) → Finset ℂ, (∀ P Ξ, ∀ z ∈ Sv P Ξ, IsAlgebraic ℚ z) ∧
  ∀ (B : Base) (px : PreX B.toPre) (I : Col2.ColIn B px), I.Ok → (∀ z ∈ Sv B.toPre (Set.range I.xi), z ∈ B.LLC) → ValsIn I := by
  refine ⟨GlobalTheory.Mem.Col2.RootsIn.Sv, fun P Ξ z hz => isAlgebraic_of_mem_Sv P Ξ z hz, ?_⟩
  intro B px I hI hS
  refine ⟨?_, ?_⟩
  ·
    intro a P _
    exact ⟨_, (hI.xi_reads a _).symm⟩
  · intro a P hP
    obtain ⟨v, hv, hsel, -⟩ := I.exists_of_mem_Q hP
    obtain ⟨Q, hQv, hQ⟩ := exists_ram (hI.xi_reads a) hv
    have hPv : P.asIdeal.under (𝓞 B.fields.F) = v.asIdeal := hsel ▸ hI.sel_ok v

    have hQP : ((Ideal.absNorm Q.asIdeal : ℕ) : 𝓞 B.fields.E) ∈ P.asIdeal := by
      have h2 : ((Ideal.absNorm Q.asIdeal : ℕ) : 𝓞 B.fields.F) ∈ P.asIdeal.under (𝓞 B.fields.F) := by
        rw [hPv, ← hQv]
        show _ ∈ Ideal.comap (algebraMap (𝓞 B.fields.F) (𝓞 B.fields.E)) Q.asIdeal
        rw [Ideal.mem_comap, map_natCast]
        exact Ideal.absNorm_mem _
      have h3 : ((Ideal.absNorm Q.asIdeal : ℕ) : 𝓞 B.fields.F) ∈
          Ideal.comap (algebraMap (𝓞 B.fields.F) (𝓞 B.fields.E)) P.asIdeal := h2
      rw [Ideal.mem_comap, map_natCast] at h3
      exact h3
    have hQ0 : Ideal.absNorm Q.asIdeal ≠ 0 := fun h0 => Q.ne_bot (Ideal.absNorm_eq_zero_iff.1 h0)
    have hN : Nat.card (kP P) ≠ 0 := by
      have hP0 : Ideal.absNorm P.asIdeal ≠ 0 := fun h0 => P.ne_bot (Ideal.absNorm_eq_zero_iff.1 h0)
      rwa [Ideal.absNorm_apply, Submodule.cardQuot_apply] at hP0
    have hmem : rootN (Nat.card (kP P)) ∈ GlobalTheory.Mem.Col2.RootsIn.Sv B.toPre (Set.range I.xi) := by
      unfold GlobalTheory.Mem.Col2.RootsIn.Sv
      refine Finset.mem_biUnion.2 ⟨I.xi a, (mem_finOr (Set.finite_range _)).2 ⟨a, rfl⟩, ?_⟩
      unfold rootsOf
      refine Finset.mem_biUnion.2 ⟨Q, (mem_finOr (ramSet_finite _)).2 hQ, ?_⟩
      exact Finset.mem_image.2 ⟨P, (mem_finOr (overN_finite hQ0)).2 hQP, rfl⟩
    obtain ⟨z, hz⟩ := (B.mem_LLC).1 (hS _ hmem)
    refine ⟨z, IsPrimitiveRoot.of_map_of_injective (f := B.embLL) ?_ B.embLL.injective⟩
    rw [hz]
    exact Complex.isPrimitiveRoot_exp _ hN
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsEqOfMemISup
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3

namespace GlobalTheory.Mem.EigCarry

theorem exists_eq_of_mem_iSup {ι κ M : Type} [AddCommGroup M] [Module ℂ M] (op : ι → Module.End ℂ M) (χ : κ → ι → ℂ)
    (E : κ → Submodule ℂ M) (hE : ∀ k, ∀ y ∈ E k, ∀ i, op i y = χ k i • y) (ψ : ι → ℂ) (x : M) (hx0 : x ≠ 0)
    (hx : ∀ i, op i x = ψ i • x) (hmem : x ∈ ⨆ k, E k) : ∃ k, χ k = ψ := by
  first
  | (rename_i h_3 h_4; revert ι κ M h_3 h_4 op χ E hE ψ x hx0 hx hmem; exact @_root_.GlobalTheory.JointEigenSupremum.target)
  | exact @_root_.GlobalTheory.JointEigenSupremum.target
  | exact _root_.GlobalTheory.JointEigenSupremum.target
  | (apply _root_.GlobalTheory.JointEigenSupremum.target <;> assumption)
  | (intros; apply _root_.GlobalTheory.JointEigenSupremum.target <;> assumption)
  | (intros; apply @_root_.GlobalTheory.JointEigenSupremum.target <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.JointEigenSupremum.target ..)

theorem exists_part_eq {ι C H M : Type} [AddCommGroup H] [Module ℂ H] [AddCommGroup M] [Module ℂ M] (e : H →ₗ[ℂ] M)
    (op : ι → Module.End ℂ M) (χ : C → ι → ℂ) (N : Submodule ℂ M) (E : C → Submodule ℂ H)
    (hE : ∀ c y, y ∈ E c ↔ e y ∈ N ∧ ∀ i, op i (e y) = χ c i • e y) (S : C → Prop) (c : C) (x : H) (hx : x ∈ E c)
    (h0 : e x ≠ 0) (hs : x ∈ ⨆ (c' : C) (_ : S c'), E c') : ∃ c', S c' ∧ E c' = E c := by
  have hle : (⨆ (c' : C) (_ : S c'), E c') ≤ (⨆ k : {c' // S c'}, (E k.1).map e).comap e := by
    refine iSup₂_le fun c' hc' y hy => ?_
    exact (le_iSup (fun k : {c' // S c'} => (E k.1).map e) ⟨c', hc'⟩) ⟨y, hy, rfl⟩
  obtain ⟨k, hk⟩ := exists_eq_of_mem_iSup op (fun k : {c' // S c'} => χ k.1) (fun k => (E k.1).map e)
    (by rintro k _ ⟨y, hy, rfl⟩; exact ((hE _ y).1 hy).2) (χ c) (e x) h0 ((hE c x).1 hx).2 (hle hs)
  refine ⟨k.1, k.2, ?_⟩
  ext y
  rw [hE, hE]
  exact and_congr_right fun _ => forall_congr' fun q => by rw [congrFun hk q]

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

theorem ssetF_base {R : RealDat3 D A3 Ks} {F : Face3 D A3} (hC : R.WeakCharacterisation F) : SsetF R.toRealDat A3.A.μ0 = R.SF := by
  have hL := hC.base.lev
  have hQ : R.Q A3.A.μ0 = ∅ := by
    refine Finset.eq_empty_of_forall_notMem fun PP hP => ?_
    refine (hL.Q_ram A3.A.μ0 PP).2 (Or.inl hP) ?_
    rw [hL.xi_base]
    intro x hx
    rfl
  ext v
  rw [hC.inert.SF v]
  unfold SsetF
  rw [hQ]
  simp only [Finset.union_empty, Finset.mem_image]
  refine exists_congr fun PP => and_congr_right fun _ => ?_
  exact ⟨fun h => h ▸ rfl, fun h => HeightOneSpectrum.ext h⟩

abbrev RowOp (R : RealDat3 D A3 Ks) : Type :=
  {q : HeightOneSpectrum (𝓞 D.host.E) × List ℤ × Finset (GA D (Yc D 0)) //
    Hecke₂ (Yc D 0) (levS _ (R.βY 0) (R.dat0 R.triv)) (levChi _ (R.βY 0) (R.dat0 R.triv)) R.SF q.1 q.2.1 q.2.2}

theorem mem_eEc_iff (R : RealDat3 D A3 Ks) (c : HeightOneSpectrum (𝓞 D.host.E) → List ℤ → ℂ) (x : R.HE.H) :
    x ∈ R.EEc c ↔ R.HE.e x ∈ Mult.Mult R.θ (R.MY 0) (levS _ (R.βY 0) (R.dat0 R.triv)) (levChi _ (R.βY 0) (R.dat0 R.triv)) ∧
      ∀ q : RowOp R, heckeOn (R.MY 0) q.1.2.2 (R.HE.e x) = c q.1.1 (dualLab q.1.2.1) • R.HE.e x := by
  unfold RealDat3.EEc partDual partFull
  simp only [Submodule.mem_comap, Submodule.mem_inf, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
    LinearMap.smul_apply, LinearMap.id_apply, sub_eq_zero]
  exact and_congr_right fun _ => ⟨fun h q => h _ _ _ q.2, fun h P d S hS => h ⟨(P, d, S), hS⟩⟩

theorem carries_of_mem (R : RealDat3 D A3 Ks) (c : HeightOneSpectrum (𝓞 D.host.E) → List ℤ → ℂ) (x : R.HE.H)
    (hx : x ∈ R.EEc c) (h0 : R.HE.e x ≠ 0) (hs : x ∈ ⨆ p, R.EEp3 p) : ∃ p, R.Carries p c := by
  have hle : (⨆ p, R.EEp3 p) ≤ ⨆ (c') (_ : ∃ p, R.Carries p c'), R.EEc c' :=
    iSup_le fun p => iSup₂_le fun c' hc' =>
      le_iSup₂_of_le (f := fun c' (_ : ∃ p, R.Carries p c') => R.EEc c') c' ⟨p, hc'⟩ le_rfl
  obtain ⟨c', ⟨p, hp⟩, heq⟩ := exists_part_eq R.HE.e (fun q : RowOp R => heckeOn (R.MY 0) q.1.2.2)
    (fun c q => c q.1.1 (dualLab q.1.2.1)) _ R.EEc (mem_eEc_iff R) (fun c' => ∃ p, R.Carries p c') c x hx h0 (hle hs)
  exact ⟨p, heq ▸ hp.1, (Submodule.map_mono heq.ge).trans hp.2⟩

theorem mem_iSup_eEp3 (R : RealDat3 D A3 Ks) (F : Face3 D A3) (b : Bool) (hP : (R.toCx3 F).PartsE b) (x : R.HE.H)
    (hx : R.HE.e x ∈ R.toRealDat.EEat (R.toRealDat.levR F.lv2 b)) : x ∈ ⨆ p, R.EEp3 p := by
  have h1 : Tw.mk (twAt D.what₂.embLL A3.A.v0) x ∈ (R.toCx3 F).EEl b := hx
  rw [← hP.2] at h1
  have h2 : (⨆ p, (R.toCx3 F).EEp p ⊓ (R.toCx3 F).EEl b) ≤ Tw.sub (twAt D.what₂.embLL A3.A.v0) (⨆ p, R.EEp3 p) := by
    refine iSup_le fun p => inf_le_left.trans fun y hy => ?_
    exact (le_iSup (fun p => R.EEp3 p) p) hy
  exact h2 h1

theorem carries_of_hasEig : GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.DiscreteSeriesExists → GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.CuspRapidDecay → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd) (X0 : BaseLevelRowSide D) (Y : Read (A3 := A3) R.toRealDat F.lv2 X0), Pins R F cG → Holds R F → HostHyp D → ∀ (π : D.what₂.FT) c, HasEig R F Y π c → ∃ p, R.Carries p c := by
  intro _ _ _ hCusp D G _ _ Pl0 I0 T A3 Ks _ _ _ R F cG X0 Y hPins hHolds _ π c hc
  obtain ⟨hCore, hSF, hEE, -⟩ := GlobalTheory.CoreOfWeak.core_of_weak R F hPins.char hHolds.aux.ex
  have hμ : Y.tupT D.what₂.mu0 = A3.A.μ0 := by rw [← Y.tup0, Y.tupT_tup]
  unfold HasEig at hc
  rw [hμ, ssetF_base hPins.char] at hc
  obtain ⟨b, hb⟩ := principalLevelFrame.rowRepR_occ R.θ (Y.eFT π)
  obtain ⟨U, hU, hU0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hb
  obtain ⟨x, hx, hxU⟩ := GlobalTheory.T.rowTypePart_le_eigensystemPart (s := 1) R.toRealDat F.lv2 hCore
    (GlobalTheory.Hk3.schurAll_of_cuspRapidDecay hCusp R.toRealDat) R.SF hSF Y.hF Y.PY Y.PW Y.stdPsi.1 Y.stdPsi.2 _ _ c hc b U hU
  rw [← hEE] at hx
  refine carries_of_mem R c x hx (hxU ▸ hU0) (mem_iSup_eEp3 R F b (hHolds.prim.sumE b) x ?_)
  rw [hxU]
  exact hU.1

end GlobalTheory.Mem.EigCarry
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsEquivariantLabelMapTwistCuspidalLabelStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_equivariant_labelMap_twist_cuspidalLabel : ∀ (K : Type) [Field K] [Fintype K] [DecidableEq K] (C : Formalism.IrreducibleCountingLemmas.TYPES.LabelConv K), Formalism.IrreducibleCountingLemmas.TYPES.CuspParam K C → ∃ O : Formalism.IrreducibleCountingLemmas.TYPES.LabelMap K C, Formalism.IrreducibleCountingLemmas.TYPES.LabelMapEquivariant O ∧ LabTwLawO O ∧ ∀ (d : ℕ) (τ : FDRep ℂ (GL (Fin d) K)), 1 ≤ d → CategoryTheory.Simple τ → Formalism.IrreducibleCountingLemmas.TYPES.IsCuspidal K τ → Formalism.IrreducibleCountingLemmas.TYPES.HasCuspLabel C τ (O.lab d τ) := by
  first | exact @GlobalTheory.CuspTwist.exists_labelMap_twist_cuspLabel | exact GlobalTheory.CuspTwist.exists_labelMap_twist_cuspLabel | (intros; apply GlobalTheory.CuspTwist.exists_labelMap_twist_cuspLabel <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFiniteGroupIdentificationFixedPlaces
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.Col2

noncomputable section

namespace GlobalTheory.Mem.R3

theorem exists_grpIdent : ∀ (X : Stages) (px : PreX X.B.toPre) (I : Col2.ColIn X.B px) (U : Set I.ι) (L : Formalism.IndefR.Links.LevCh X.toD7 (TupU I U)), I.Ok → GrpAt X I → LevOf X I U L → ∃ (eG : Gc X.B px ≃* G0 L.Pg X.toD7.R.r) (cG : G0 L.Pg X.toD7.R.r ≃* G0g X.toD7.nd) (plg : (Σ k : Fin 2, X.toD7.nd.PlG k) ≃ L.Pg) (iso : ∀ kv : (Σ k : Fin 2, X.toD7.nd.PlG k), ZMod (X.toD7.host.g kv.1) ≃+* kP (plg kv).1), IsPlacewiseIdentity X (px := px) eG ∧ (∀ kv, ((plg kv : L.Pg) : Pl X.toD7.host.E) = X.toD7.naut.plGw kv.1 kv.2) ∧ (∀ kv, L.C.P.Div kv.1 (plg kv).1) ∧ ∀ g kv, eG g (plg kv) = Formalism.UG.bc (iso kv : ZMod (X.toD7.host.g kv.1) →+* kP (plg kv).1) ((eG.trans cG) g kv) := by
  intro X px I U L hI hG hL
  obtain ⟨plg0, hplg0⟩ := hG.pl
  have hPr := (base_fields_primes_ok X.B px).2.1
  have h1 : ∀ P, P ∈ L.Pg ↔ P ∈ (X.B.primes px).vGs := fun P => by rw [hL.Pg]; exact Iff.rfl
  let eG : Gc X.B px ≃* G0 L.Pg X.toD7.R.r :=
    { toFun := fun g PP => g ⟨PP.1, (h1 _).1 PP.2⟩
      invFun := fun h PP => h ⟨PP.1, (h1 _).2 PP.2⟩
      left_inv := fun g => rfl
      right_inv := fun h => rfl
      map_mul' := fun _ _ => rfl }
  let plg : (Σ k : Fin 2, X.toD7.nd.PlG k) ≃ L.Pg := plg0.trans (Equiv.subtypeEquivRight fun P => (h1 P).symm)
  have hmem : ∀ kv : (Σ k : Fin 2, X.toD7.nd.PlG k), ((plg kv : L.Pg) : Pl X.toD7.host.E) ∈ (X.B.primes px).vG kv.1 :=
    fun kv => (hI.pibar kv.1 _).2 (hplg0 kv).2
  have hiso : ∀ kv : (Σ k : Fin 2, X.toD7.nd.PlG k), Nonempty (ZMod (X.toD7.host.g kv.1) ≃+* kP (plg kv).1) := by
    intro kv
    haveI : Fact (X.toD7.host.g kv.1).Prime := ⟨hPr.g_prime kv.1⟩
    obtain ⟨e⟩ := Formalism.L2.Col.residueField_equiv_zmod (X := X.B.fields) (plg kv).1 (X.toD7.host.g kv.1) (hPr.vG_norm kv.1 _ (hmem kv))
    exact ⟨e.symm⟩
  let iso : ∀ kv : (Σ k : Fin 2, X.toD7.nd.PlG k), ZMod (X.toD7.host.g kv.1) ≃+* kP (plg kv).1 := fun kv => Classical.choice (hiso kv)
  let cG : G0 L.Pg X.toD7.R.r ≃* G0g X.toD7.nd :=
    { toEquiv := (Equiv.piCongrLeft (fun PP : L.Pg => GL (Fin X.toD7.R.r) (kP PP.1)) plg).symm.trans
        (Equiv.piCongrRight fun kv => (Formalism.L2.Col.generalLinearEquivOfRingEquiv X.toD7.R.r (iso kv).symm).toEquiv)
      map_mul' := fun f f' => by
        funext kv
        exact map_mul (Formalism.L2.Col.generalLinearEquivOfRingEquiv X.toD7.R.r (iso kv).symm) (f (plg kv)) (f' (plg kv)) }
  refine ⟨eG, cG, plg, iso, fun g P h h' => rfl, fun kv => (hplg0 kv).1, fun kv => ?_, fun g kv => ?_⟩
  · rw [hL.C]
    exact (hplg0 kv).2
  · show _ = Formalism.UG.bc (iso kv : ZMod (X.toD7.host.g kv.1) →+* kP (plg kv).1)
      (Formalism.L2.Col.generalLinearEquivOfRingEquiv X.toD7.R.r (iso kv).symm (eG g (plg kv)))
    ext i j
    simp [Formalism.UG.bc, Formalism.L2.Col.generalLinearEquivOfRingEquiv]
end GlobalTheory.Mem.R3

end
end

