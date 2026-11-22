import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0003
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CoboundaryMemBlochKatoCocycles
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0252
import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.Bundle0005
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0483
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0656
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0005
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0352
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0349
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0358
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0492
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0545
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0638
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0548
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0580
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0599
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0575
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0623
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0455
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0609
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0614
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0611
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0014
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0620
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0392
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0594
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0561
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0606
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0664
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnipotentBlockColumnIndex
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsWeilDatumOOneOfRankZero
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.WeilSiegelFormulaUnitary
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0126

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemContinuousCocyclesRestrictLattice
section
noncomputable section

namespace GlobalTheory.NL.RightExactKs

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N TensorProduct GlobalTheory.NL

section Generic

theorem dvd_pow_of_not_isUnit {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    {p : O} (hp : ¬ IsUnit p) {a : O} (ha : a ≠ 0) : ∃ n : ℕ, a ∣ p ^ n := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  obtain ⟨n, hn⟩ := IsDiscreteValuationRing.associated_pow_irreducible ha hϖ
  have h1 : ϖ ∣ p := by
    rw [← Ideal.mem_span_singleton, ← hϖ.maximalIdeal_eq]
    exact hp
  exact ⟨n, hn.dvd.trans (pow_dvd_pow_of_dvd h1 n)⟩

variable {G : Type} [Group G] [TopologicalSpace G] [CompactSpace G] {LL : Type} [Field LL]
  {O : Type} [CommRing O] [Algebra O LL] [IsDomain O] [IsDiscreteValuationRing O]
  [IsFractionRing O LL]
  {V : Type} [AddCommGroup V] [Module LL V] [Module O V] [IsScalarTower O LL V]
  [TopologicalSpace V] [ContinuousAdd V] [ContinuousConstSMul LL V] {ρ : Representation LL G V}
  {V' : Type} [AddCommGroup V'] [Module LL V'] [Module O V'] [IsScalarTower O LL V']
  [TopologicalSpace V'] [ContinuousAdd V'] [ContinuousConstSMul LL V']
  {ρ' : Representation LL G V'}

theorem lift_integral {L : Lattice (O := O) ρ} {L' : Lattice (O := O) ρ'} (F : LatHom L L')
    (hT : IsOpen (L.T : Set V)) {p : ℕ} (hp : ¬ IsUnit (p : O)) (c' : ↥(latticeCocycles L')) (c : G → V)
    (hc : c ∈ continuousCocycles ρ) (v : V') (hv : ∀ g, F.f (c g) - (c' : G → V') g = ρ' g v - v) :
    ∃ (n : ℕ) (c₁ : ↥(latticeCocycles L)), (∀ g, (c₁ : G → V) g = ((p : LL) ^ n) • c g) ∧
      F.H1map (Submodule.Quotient.mk c₁) = (p ^ n : ℕ) • (Submodule.Quotient.mk c' : LatticeCohomology L') := by
  obtain ⟨a, ha, h⟩ := GlobalTheory.H1fGeneratorBoundAlt.exists_smul_fun_mem L hT c hc.1
  obtain ⟨b, hb, h'⟩ := GlobalTheory.H1fGeneratorBoundAlt.exists_smul_mem L' v
  obtain ⟨n, d, hd⟩ := dvd_pow_of_not_isUnit hp (mul_ne_zero ha hb)
  have h1 : (p : O) ^ n • c ∈ latticeCocycles L := by
    refine ⟨Submodule.smul_mem ((continuousCocycles ρ).restrictScalars O) _ hc, fun g _ => ?_⟩
    change (p : O) ^ n • c g ∈ L.T
    rw [hd, mul_assoc, mul_comm, mul_smul]
    exact L.T.smul_mem _ (h g)
  have h2 : (p : O) ^ n • v ∈ L'.T := by
    rw [hd, mul_comm, ← mul_assoc, mul_smul]
    exact L'.T.smul_mem _ h'
  refine ⟨n, ⟨_, h1⟩, fun g => ?_, ?_⟩
  · change (p : O) ^ n • c g = _
    rw [← algebraMap_smul LL, map_pow, map_natCast]
  · rw [← Nat.cast_smul_eq_nsmul O, ← Submodule.Quotient.mk_smul]
    refine (Submodule.Quotient.eq _).2 ⟨_, h2, ?_⟩
    funext g
    change ρ' g ((p : O) ^ n • v) - (p : O) ^ n • v =
      F.f ((p : O) ^ n • c g) - ((p ^ n : ℕ) : O) • (c' : G → V') g
    rw [Nat.cast_pow, LinearMap.map_smul_of_tower, LinearMap.map_smul_of_tower, ← smul_sub,
      ← smul_sub, hv]

end Generic

theorem lift_integral_res {G : Type} [Group G] [TopologicalSpace G] {Qp LL O : Type} [Field Qp]
    [TopologicalSpace Qp] [Field LL] [Algebra Qp LL] [CommRing O] [Algebra O LL]
    [TopologicalSpace LL] (hO : GoodO (Qp := Qp) LL O) (H : Subgroup G) [CompactSpace ↥H]
    (T₁ T₂ : LocLat G Qp LL O) (π : LatHom T₁.L T₂.L) {p : ℕ} (hp : ¬ IsUnit (p : O))
    (c₂ : ↥(latticeCocycles (resLat T₂ H))) (κ₂ : LatticeCohomology (resLat T₂ H)) (hκ : Submodule.Quotient.mk c₂ = κ₂)
    (c : ↥H → T₁.V) (hc : c ∈ continuousCocycles (T₁.ρ.comp H.subtype)) (v : T₂.V)
    (hv : ∀ g : ↥H, π.f (c g) - (c₂ : ↥H → T₂.V) g = T₂.ρ (g : G) v - v) :
    ∃ (n : ℕ) (c₁ : ↥(latticeCocycles (resLat T₁ H))) (κ₁ : LatticeCohomology (resLat T₁ H)),
      Submodule.Quotient.mk c₁ = κ₁ ∧ (∀ g, (c₁ : ↥H → T₁.V) g = ((p : LL) ^ n) • c g) ∧
      (resHom π H).H1map κ₁ = (p ^ n : ℕ) • κ₂ := by
  obtain ⟨hD, hDVR, hF⟩ := hO.1
  obtain ⟨n, c₁, h1, h2⟩ := lift_integral (resHom π H) (GlobalTheory.Cyc.locLat_isOpen hO T₁) hp c₂ c hc v hv
  exact ⟨n, c₁, _, rfl, h1, hκ ▸ h2⟩

theorem mem_continuousCocycles_restrictLattice {G : Type} [Group G] [TopologicalSpace G] {Qp LL O : Type} [Field Qp]
    [Field LL] [Algebra Qp LL] [CommRing O] [Algebra O LL] [TopologicalSpace LL]
    (T : LocLat G Qp LL O) (H : Subgroup G) (c : ↥(latticeCocycles (resLat T H))) :
    (c : ↥H → T.V) ∈ continuousCocycles (T.ρ.comp H.subtype) := c.2.1

theorem smul_coboundary {Qp LL V B : Type} [Field Qp] [Field LL] [Algebra Qp LL] [AddCommGroup V]
    [Module LL V] [Module Qp V] [IsScalarTower Qp LL V] [CommRing B] [Algebra Qp B]
    (f : V ⊗[Qp] B →ₗ[LL] V ⊗[Qp] B) (a : LL) {y y' : V} {x : V ⊗[Qp] B} (h : y' = a • y)
    (hx : y ⊗ₜ[Qp] (1 : B) = f x - x) : y' ⊗ₜ[Qp] (1 : B) = f (a • x) - a • x := by
  rw [h, map_smul, ← smul_sub, ← hx]
  rfl

variable {l : ℕ} [Fact l.Prime]

theorem not_isUnit_l (P : LocPrime l) (LL : FinExt l) : ¬ IsUnit ((l : ℕ) : ↥(OL LL)) := by
  intro hu
  obtain ⟨u, hu⟩ := hu.exists_right_inv
  have h1 : ((l : ℕ) : ↥LL.1) * (u : ↥LL.1) = 1 := by
    have := congrArg (algebraMap ↥(OL LL) ↥LL.1) hu
    rwa [map_mul, map_natCast, map_one] at this
  have h2 := congrArg (P.v LL) h1
  rw [AddValuation.map_mul, AddValuation.map_one, P.v_l] at h2
  have h3 : 0 ≤ P.v LL (u : ↥LL.1) := (P.v_O LL _).2 u.2
  have h4 : (1 : WithTop ℚ) ≤ 0 := h2 ▸ le_add_of_nonneg_right h3
  exact absurd h4 (by simp)

theorem continuous_incl {K E : FinExt l} (hle : K.1 ≤ E.1) :
    Continuous (Subgroup.inclusion (GK_le hle)) :=
  continuous_subtype_val.subtype_mk _

def resRep {K LL : FinExt l} (E : FinExt l) (hle : K.1 ≤ E.1) (T : Lt K LL) :
    GRep ↥(GK E) ℚ_[l] ↥LL.1 ↥(OL LL) where
  V := T.V
  ρ := T.ρ.comp (Subgroup.inclusion (GK_le hle))
  cont x := (T.cont x).comp (continuous_incl hle)

set_option maxHeartbeats 1600000 in

theorem lift_rational (P : LocPrime l) (AI : LocAinf l P) (hP : LocTied l P AI) {K LL : FinExt l}
    (E : FinExt l) (hle : K.1 ≤ E.1) (H : Subgroup ↥(GK K))
    (hH : ∀ x : ↥(GK K), x ∈ H ↔ (x : GQ l) ∈ GK E) (T₁ T₂ : Lt K LL) (π : LatHom T₁.L T₂.L)
    (hπ : Function.Surjective π.f) (h₁ : IsCrys (P.PD K) T₁.ρ) (h₂ : IsCrys (P.PD K) T₂.ρ)
    (c₂ : ↥H → T₂.V) (hc₂ : c₂ ∈ continuousCocycles (T₂.ρ.comp H.subtype))
    (x₂ : T₂.V ⊗[ℚ_[l]] P.R.B)
    (hx₂ : ∀ g : ↥H, c₂ g ⊗ₜ[ℚ_[l]] (1 : P.R.B) = actVB (P.PD K) T₂.ρ (g : ↥(GK K)) x₂ - x₂) :
    ∃ c₁ ∈ continuousCocycles (T₁.ρ.comp H.subtype),
      (∃ x₁ : T₁.V ⊗[ℚ_[l]] P.R.B,
        ∀ g : ↥H, c₁ g ⊗ₜ[ℚ_[l]] (1 : P.R.B) = actVB (P.PD K) T₁.ρ (g : ↥(GK K)) x₁ - x₁) ∧
      ∃ v : T₂.V, ∀ g : ↥H, π.f (c₁ g) - c₂ g = T₂.ρ (g : ↥(GK K)) v - v := by
  let a : ↥(GK E) → ↥H := fun g => ⟨Subgroup.inclusion (GK_le hle) g, (hH _).2 g.2⟩
  let b : ↥H → ↥(GK E) := fun g => ⟨((g : ↥(GK K)) : GQ l), (hH _).1 g.2⟩
  have ha : Continuous a := (continuous_incl hle).subtype_mk _
  have hb : Continuous b := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
  have hres := fun (T : Lt K LL) (hT : IsCrys (P.PD K) T.ρ) =>
    (GlobalTheory.Per.TiedRestrict.restrict_crys_deRham l P AI hP K E LL hle T.V T.ρ).1 hT
  have hc' : c₂ ∘ a ∈ finiteCocycles (P.PD E) (resRep E hle T₂).ρ := by
    refine ⟨⟨hc₂.1.comp ha, fun g h => hc₂.2 (a g) (a h)⟩, x₂, fun g => ?_⟩
    exact (hx₂ (a g)).trans (congrArg (fun f : T₂.V ⊗[ℚ_[l]] P.R.B →ₗ[↥LL.1] T₂.V ⊗[ℚ_[l]] P.R.B => f x₂ - x₂)
      (GlobalTheory.Cyc.actVB_inclusion P K E LL hle T₂ g).symm)
  obtain ⟨c, ⟨hc, x, hx⟩, v, hv⟩ := GlobalTheory.T.bloch_kato_right_exact l P AI hP E ↥LL.1 ↥(OL LL)
    (GlobalTheory.LocalIntegers.good_integers l LL).1 (resRep E hle T₁) (resRep E hle T₂) π.f
    (fun g y => π.equiv _ y) hπ (hres T₁ h₁) (hres T₂ h₂) _ hc'
  refine ⟨c ∘ b, ⟨hc.1.comp hb, fun g h => hc.2 (b g) (b h)⟩, ⟨x, fun g => ?_⟩, v, fun g => ?_⟩
  · let x' : T₁.V ⊗[ℚ_[l]] P.R.B := x
    exact (hx (b g)).trans (congrArg (fun f : T₁.V ⊗[ℚ_[l]] P.R.B →ₗ[↥LL.1] T₁.V ⊗[ℚ_[l]] P.R.B => f x' - x')
      (GlobalTheory.Cyc.actVB_inclusion P K E LL hle T₁ (b g)))
  · exact (congrFun hv (b g)).symm

theorem compactSpace_sub {K E : FinExt l} (hle : K.1 ≤ E.1) (H : Subgroup ↥(GK K))
    (hH : ∀ x : ↥(GK K), x ∈ H ↔ (x : GQ l) ∈ GK E) : CompactSpace ↥H := by
  have := GlobalTheory.H1fGeneratorBoundAlt.compactSpace_GK E
  let a : ↥(GK E) → ↥H := fun g => ⟨Subgroup.inclusion (GK_le hle) g, (hH _).2 g.2⟩
  have ha : Continuous a := (continuous_incl hle).subtype_mk _
  have hs : Function.Surjective a := fun g => ⟨⟨((g : ↥(GK K)) : GQ l), (hH _).1 g.2⟩, rfl⟩
  exact hs.compactSpace ha

theorem mem_GKs_iff (P : LocPrime l) {K LL : FinExt l} {s m : ℕ}
    (W : LocWach (P.PD K) ↥LL.1 ↥(OL LL) (P.v LL) m) (hs : W.s = s) (x : ↥(GK K)) :
    x ∈ W.GKs ↔ (x : GQ l) ∈ GK (GlobalTheory.IndefiniteRowSideFullHecke.LevelConstants.KsFin K s) := by
  rw [GlobalTheory.Cyc.mem_GKs_iff_mem_Gj, hs]
  rfl

set_option maxHeartbeats 1600000 in

theorem lift_cocycle (P : LocPrime l) (AI : LocAinf l P) (hP : LocTied l P AI) {K LL : FinExt l}
    {s m : ℕ} (hK : K.1 ≤ Ks K s) (W : LocWach (P.PD K) ↥LL.1 ↥(OL LL) (P.v LL) m) (hs : W.s = s)
    (T₁ T₂ : Lt K LL) (π : LatHom T₁.L T₂.L)
    (hπ : Function.Surjective π.f) (h₁ : IsCrys (P.PD K) T₁.ρ) (h₂ : IsCrys (P.PD K) T₂.ρ)
    (c₂ : ↥(latticeCocycles (resLat T₂ W.GKs))) (κ₂ : LatticeCohomology (resLat T₂ W.GKs))
    (hκ : Submodule.Quotient.mk c₂ = κ₂) (x₂ : T₂.V ⊗[ℚ_[l]] P.R.B)
    (hx₂ : ∀ g : ↥W.GKs, (c₂ : ↥W.GKs → T₂.V) g ⊗ₜ[ℚ_[l]] (1 : P.R.B) =
      actVB (P.PD K) T₂.ρ (g : ↥(GK K)) x₂ - x₂) :
    ∃ (n : ℕ) (c₁ : ↥(latticeCocycles (resLat T₁ W.GKs))) (κ₁ : LatticeCohomology (resLat T₁ W.GKs)),
      Submodule.Quotient.mk c₁ = κ₁ ∧
      (∃ x₁ : T₁.V ⊗[ℚ_[l]] P.R.B, ∀ g : ↥W.GKs, (c₁ : ↥W.GKs → T₁.V) g ⊗ₜ[ℚ_[l]] (1 : P.R.B) =
        actVB (P.PD K) T₁.ρ (g : ↥(GK K)) x₁ - x₁) ∧
      (resHom π W.GKs).H1map κ₁ = (l ^ n : ℕ) • κ₂ := by
  have hH := mem_GKs_iff P W hs
  have := compactSpace_sub (E := GlobalTheory.IndefiniteRowSideFullHecke.LevelConstants.KsFin K s) hK W.GKs hH
  refine (lift_rational P AI hP (GlobalTheory.IndefiniteRowSideFullHecke.LevelConstants.KsFin K s) hK W.GKs hH T₁ T₂ π hπ h₁ h₂ _
    (mem_continuousCocycles_restrictLattice T₂ W.GKs c₂) x₂ hx₂).elim fun c hc => hc.2.1.elim fun x hx =>
      hc.2.2.elim fun v hv => ?_
  refine (lift_integral_res (GlobalTheory.LocalIntegers.good_integers l LL).1
    W.GKs T₁ T₂ π (not_isUnit_l P LL) c₂ κ₂ hκ c hc.1 v hv).elim fun n h => h.elim fun c₁ h =>
      h.elim fun κ₁ h => ?_
  exact ⟨n, c₁, κ₁, h.1, ⟨((l : ↥LL.1) ^ n) • x, fun g => smul_coboundary _ _ (h.2.1 g) (hx g)⟩,
    h.2.2⟩

end GlobalTheory.NL.RightExactKs
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NonemptyDiscPeriodAinfBasisDataOfIsPer
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
open Matrix

namespace GlobalTheory.BSP.HeightEx

theorem exists_cols_det_ne_zero {R : Type} [CommRing R] [IsDomain R] {d : ℕ} {κ : Type} (col : κ → Fin d → R)
    (h : ∀ r : Fin d → R, (∀ k, r ⬝ᵥ col k = 0) → r = 0) :
    ∃ σ : Fin d → κ, (Matrix.of fun a b => col (σ b) a).det ≠ 0 := by
  classical
  let F := FractionRing R
  let v : κ → Fin d → F := fun k a => algebraMap R F (col k a)
  have hinj : Function.Injective (algebraMap R F) := IsFractionRing.injective R F
  have hspan : Submodule.span F (Set.range v) = ⊤ := by
    by_contra hne
    obtain ⟨f, hf0, hf⟩ := Submodule.exists_le_ker_of_lt_top _ (lt_top_iff_ne_top.2 hne)
    obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors R)
      (fun a : Fin d => f (Pi.single a 1))
    choose r hr using hb
    have hb0 : algebraMap R F b ≠ 0 := fun h0 => nonZeroDivisors.coe_ne_zero b (hinj (h0.trans (map_zero _).symm))
    have hr0 : r = 0 := h r fun k => hinj (by
      have h1 : f (v k) = 0 := hf (Submodule.subset_span ⟨k, rfl⟩)
      rw [LinearMap.pi_apply_eq_sum_univ] at h1
      rw [map_zero, dotProduct, map_sum]
      have h2 : ∀ a, algebraMap R F (r a * col k a) =
          algebraMap R F b * (v k a • f fun j => if a = j then 1 else 0) := fun a => by
        have e : (fun j => if a = j then (1 : F) else 0) = Pi.single a 1 := by
          ext j; simp [Pi.single_apply, eq_comm]
        rw [map_mul, hr, e, Algebra.smul_def, smul_eq_mul]; ring
      rw [Finset.sum_congr rfl fun a _ => h2 a, ← Finset.mul_sum, h1, mul_zero])
    refine hf0 ((Pi.basisFun F (Fin d)).ext fun a => ?_)
    have h3 := hr a
    rw [hr0, Pi.zero_apply, map_zero, Algebra.smul_def] at h3
    rw [Pi.basisFun_apply]
    exact (mul_eq_zero.1 h3.symm).resolve_left hb0
  obtain ⟨κ', a, -, hs, hli⟩ := exists_linearIndependent' F v
  let B : Module.Basis κ' F (Fin d → F) := Module.Basis.mk hli (by rw [hs, hspan])
  let e : κ' ≃ Fin d := B.indexEquiv (Pi.basisFun F (Fin d))
  refine ⟨a ∘ e.symm, fun h0 => ?_⟩
  have hu : IsUnit ((Matrix.of fun x y => col (a (e.symm y)) x).map (algebraMap R F)) :=
    Matrix.linearIndependent_cols_iff_isUnit.1 (hli.comp e.symm e.symm.injective)
  have h4 := (Matrix.isUnit_iff_isUnit_det _).1 hu
  rw [← RingHom.mapMatrix_apply, ← RingHom.map_det] at h4
  exact h4.ne_zero ((congrArg (algebraMap R F) h0).trans (map_zero _))

variable {l : ℕ} [Fact l.Prime] {K : FinExt l} (bk : BK K)

theorem inclW_injective : Function.Injective (inclW l) :=
  WittVector.map_injective _ (IsFractionRing.injective (OCb l) (Cb l))

theorem injective_of_topBasis {S A : Type} [CommRing S] [CommRing A] {s : S →+* A} {I : Ideal S} {ι : Type}
    (TB : TopBasis s I ι) : Function.Injective s := fun a b h => by
  have e : ∀ a, TB.c TB.i₀ (s a * TB.b TB.i₀) = a := fun a => by rw [TB.c_mul, TB.c_self, mul_one]
  rw [← e a, h, e]

theorem evW_mem (s : bk.S) : bk.evW s ∈ bk.OE := fun _ => ⟨0, s, 0, by simp⟩

theorem exists_cols (hinj : Function.Injective bk.iA) {d : ℕ} {ι : Type}
    (v : ι → Matrix (Fin d) (Fin d) (Ainf l)) (β : ι → Ainf l) (c : Ainf l) (hc : c ≠ 0)
    (h : ∀ a b : Fin d, HasSum (fun i => bk.iA (v i a b * β i)) (bk.iA (c * if a = b then 1 else 0))) :
    ∃ σ : Fin d → ι × Fin d, (Matrix.of fun a b => v (σ b).1 a (σ b).2).det ≠ 0 := by
  refine exists_cols_det_ne_zero (fun (k : ι × Fin d) a => v k.1 a k.2) fun r hr => funext fun b => ?_
  have h1 := hasSum_sum (s := Finset.univ) fun a _ => (h a b).mul_left (bk.iA (r a))
  have h2 : (fun i => ∑ a, bk.iA (r a) * bk.iA (v i a b * β i)) = fun _ => 0 := funext fun i => by
    have h3 := hr (i, b)
    simp only [dotProduct] at h3
    simp only [← map_mul, ← map_sum, ← mul_assoc, ← Finset.sum_mul, h3, zero_mul, map_zero]
  rw [h2] at h1
  have h4 := h1.unique hasSum_zero
  simp only [← map_mul, ← map_sum] at h4
  have h5 := hinj (h4.trans (map_zero _).symm)
  simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true] at h5
  exact (mul_eq_zero.1 h5).resolve_right hc

theorem mem_lattice (hev : Function.Injective bk.ev) {d : ℕ} (Y1 : Matrix (Fin d) (Fin d) (Ainf l)) (m : ℕ)
    (P Y' : Matrix (Fin d) (Fin d) (WCb l)) (hY' : (l : WCb l) ^ m • Y' = Y1.map (inclW l) * P)
    (hP : ∀ v : Fin d → WCb l, (∀ i, v i ∈ bk.OE) → ∀ n : ℕ, (∀ i, (l : WCb l) ^ n ∣ (Y1.map (inclW l) *ᵥ v) i) →
      ∃ w : Fin d → WCb l, (∀ i, w i ∈ bk.OE) ∧ (l : WCb l) ^ m • v = (l : WCb l) ^ n • (P *ᵥ w))
    (y : Fin d → Ainf l) (δ : bk.S) (c : Fin d → bk.S) (hδ : δ ≠ 0)
    (h : (fun a => bk.ev δ * y a) = Y1 *ᵥ fun a => bk.ev (c a)) :
    ∃ w : Fin d → WCb l, (∀ i, w i ∈ bk.OE) ∧ (fun a => inclW l (y a)) = Y' *ᵥ w := by
  have h0 : bk.evW δ ≠ 0 := fun h0 =>
    hδ (hev (inclW_injective (h0.trans (by rw [map_zero, map_zero]))))
  obtain ⟨n, u, u', -, hu', huu, he⟩ := (GlobalTheory.T.integral_elements_unit_factorization l K bk).2.2.2.1 _ (evW_mem bk δ) h0
  have hl0 : (l : WCb l) ≠ 0 := WittVector.p_nonzero l (Cb l)
  have h1 : Y1.map (inclW l) *ᵥ (u' • fun a => bk.evW (c a)) = (l : WCb l) ^ n • fun a => inclW l (y a) := by
    rw [Matrix.mulVec_smul]
    funext a
    have h2 := congrArg (inclW l) (congrFun h a)
    rw [RingHom.map_mulVec, map_mul] at h2
    change bk.evW δ * _ = (Y1.map (inclW l) *ᵥ fun a => bk.evW (c a)) a at h2
    rw [Pi.smul_apply, ← h2, he, Pi.smul_apply, smul_eq_mul, smul_eq_mul]
    linear_combination ((l : WCb l) ^ n * inclW l (y a)) * huu
  obtain ⟨w, hw, hw2⟩ := hP (u' • fun a => bk.evW (c a)) (fun i => bk.OE.mul_mem hu' (evW_mem bk _)) n
    (fun i => by rw [h1]; exact ⟨_, rfl⟩)
  refine ⟨w, hw, ?_⟩
  have h3 := congrArg (Y1.map (inclW l)).mulVec hw2
  rw [Matrix.mulVec_smul, h1, Matrix.mulVec_smul, Matrix.mulVec_mulVec, ← hY', Matrix.smul_mulVec, smul_comm] at h3
  exact smul_right_injective _ (pow_ne_zero m hl0) (smul_right_injective _ (pow_ne_zero n hl0) h3)

theorem nonempty_height : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (τ : Ainf l), bk.IsPer τ → ∀ (d : ℕ) (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) ℤ_[l]), (∀ g, IsUnit (ρ g)) → ∀ s : Seed bk d ρ τ, Nonempty (Height s) := by
  intro l _ K bk τ hτ d ρ hρ s
  obtain ⟨-, -, ⟨hρ0, hρ1, -⟩, -⟩ := GlobalTheory.BSP.flat_disc l K bk
  obtain ⟨ι, TB, k, v, Zf, -, hvZ, hsum⟩ := GlobalTheory.T.exists_bounded_periods_disc_ainf l K bk τ hτ d ρ hρ s
  have hinj : Function.Injective bk.iA := (GlobalTheory.T.closedDisc_toDisc_injective_of_adicBasis l K bk _ bk.ev ι TB _ hρ0 hρ1).1
  have hev := injective_of_topBasis TB
  have hτ0 : τ ≠ 0 := (GlobalTheory.T.breuilKisin_period_isUnit_wittTilt_and_ne_zero l K bk τ hτ).2.2.1
  have hl0 : (l : Ainf l) ≠ 0 := WittVector.p_nonzero l (OCb l)
  obtain ⟨j₀, hj₀⟩ : ∃ j : bk.DS bk.ρ₀ →+* bk.DA bk.ρ₀, IsDiscMap bk.ev j :=
    GlobalTheory.BSP.exists_discMap_of_pow_dvd l _ _ bk.ev X (bk.ev X) _ _ 1 hρ0 (by rw [pow_one]) (by rw [pow_one])
  obtain ⟨σ, hσ⟩ := exists_cols bk hinj v TB.b _ (mul_ne_zero (pow_ne_zero k hl0) (pow_ne_zero _ hτ0)) hsum
  set Y1 : Matrix (Fin d) (Fin d) (Ainf l) := Matrix.of fun a b => v (σ b).1 a (σ b).2 with hY1
  let Z1 : Matrix (Fin d) (Fin d) (bk.DS bk.ρ₀) := Matrix.of fun a b => Zf (σ b).1 a (σ b).2
  have hZ1 : ∀ j : bk.DS bk.ρ₀ →+* bk.DA bk.ρ₀, IsDiscMap bk.ev j → s.W * Z1.map j = Y1.map bk.iA :=
    fun j hj => Matrix.ext fun a b => congrFun (congrFun (hvZ j hj (σ b).1) a) (σ b).2
  clear_value Y1 Z1
  have hdet : (Y1.map (inclW l)).det ≠ 0 := fun h0 => hσ (inclW_injective (by
    rw [RingHom.map_det, map_zero]; exact h0))
  obtain ⟨δ, A1, hδ, hA1⟩ := GlobalTheory.T.crystallineLattice_frobenius_rational_columns l K bk τ hτ d ρ hρ s Y1 Z1 hσ hZ1
  have hgal : ∀ g : ↥(GK K), bk.FixFlat g → τ ^ s.N • ((ρ g).map (algebraMap ℤ_[l] (Ainf l)) *
      Y1.map (Per.σA (g : GQ l))) = Per.σA (g : GQ l) τ ^ s.N • Y1 := fun g hg => by
    obtain ⟨G, hG⟩ := (GlobalTheory.BSP.galois_discMap l K bk).2 _ hρ0 (g : GQ l)
    obtain ⟨hfix, hW⟩ := GlobalTheory.T.crystallineDiscPeriods_galois_action_eq l K bk τ hτ d ρ hρ s g hg G hG
    have e1 : (Z1.map j₀).map G = Z1.map j₀ := Matrix.ext fun a b => hfix j₀ hj₀ _
    have e2 : s.W.map G * Z1.map j₀ = (Y1.map (Per.σA (g : GQ l))).map bk.iA := by
      rw [← e1, ← Matrix.map_mul, hZ1 j₀ hj₀]
      exact Matrix.ext fun a b => hG.ext _
    have e3 := congrArg (· * Z1.map j₀) hW
    simp only [Matrix.smul_mul, Matrix.mul_assoc] at e3
    rw [e2, hZ1 j₀ hj₀, hG.ext] at e3
    refine Matrix.ext fun a b => hinj ?_
    have e4 := congrFun (congrFun e3 a) b
    simp only [Matrix.smul_apply, Matrix.mul_apply, Matrix.map_apply, smul_eq_mul, map_mul, map_pow, map_sum,
      RingHom.comp_apply] at e4 ⊢
    exact e4
  obtain ⟨m, P, Y', hP, hPd, hY', hlat, hsat⟩ := GlobalTheory.T.exists_integralWittLattice_basis l K bk d _ hdet
  have hY'u := GlobalTheory.T.isUnit_saturated_basis_etale_lattice l K bk τ hτ d s.N ρ hρ Y1 δ A1 hdet hδ hA1 hgal m P Y' hP hPd hY' hlat hsat
  obtain ⟨Y, hYu, hY⟩ := GlobalTheory.T.ainf_closed_membership_limit l K bk d (fun y : Fin d → Ainf l => ∃ x : Fin d → bk.DS bk.ρ₀,
      ∀ j : bk.DS bk.ρ₀ →+* bk.DA bk.ρ₀, IsDiscMap bk.ev j → s.W *ᵥ (fun a => j (x a)) = fun a => bk.iA (y a))
    ⟨0, fun j _ => by simp only [Pi.zero_apply, map_zero]; exact Matrix.mulVec_zero _⟩
    (fun y z ⟨x, hx⟩ ⟨x', hx'⟩ => ⟨x + x', fun j hj => by
      simp only [Pi.add_apply, map_add]
      exact (Matrix.mulVec_add s.W (fun a => j (x a)) fun a => j (x' a)).trans (by rw [hx j hj, hx' j hj]; rfl)⟩)
    (fun c y ⟨x, hx⟩ => ⟨fun a => toDisc l X bk.ρ₀ c * x a, fun j hj => by
      simp only [map_mul, hj.ext]
      exact (Matrix.mulVec_smul s.W (bk.iA (bk.ev c)) fun a => j (x a)).trans (by rw [hx j hj]; rfl)⟩)
    (fun y ⟨x, hx⟩ => by
      obtain ⟨t, ht⟩ := (isUnit_l_disc l (X : bk.S) bk.ρ₀).exists_left_inv
      refine ⟨fun a => t * x a, fun j hj => ?_⟩
      have ht' := congrArg j ht
      rw [map_mul, map_natCast, map_one] at ht'
      simp only [map_mul]
      refine (Matrix.mulVec_smul s.W (j t) fun a => j (x a)).trans ?_
      rw [hx j hj]
      funext a
      rw [Pi.smul_apply, smul_eq_mul, map_mul, map_natCast, ← mul_assoc, ht', one_mul])
    (GlobalTheory.T.crystalline_disc_period_module_isClosed_lAdic l K bk τ hτ d ρ hρ s) Y1 Y' hdet hY'u
    (fun c => ⟨Z1 *ᵥ fun a => toDisc l X bk.ρ₀ (c a), fun j hj => by
      simp only [RingHom.map_mulVec]
      have e : (j ∘ fun a => toDisc l X bk.ρ₀ (c a)) = bk.iA ∘ fun a => bk.ev (c a) := funext fun a => hj.ext _
      rw [e, ← hZ1 j hj, ← Matrix.mulVec_mulVec]⟩)
    (fun y hy => by
      obtain ⟨δ, c, hδ, h⟩ := GlobalTheory.T.crystallineLattice_rational_in_columns l K bk τ hτ d ρ hρ s Y1 Z1 hdet hZ1 y hy
      exact mem_lattice bk hev Y1 m P Y' hY' hlat y δ c hδ h)
  obtain ⟨k', S', hS'⟩ := GlobalTheory.T.basis_dvd_tauPow_lPow_ainf l K bk τ hτ d ρ hρ s Y hYu hY
  have hcol : ∀ b : Fin d, ∃ x : Fin d → bk.DS bk.ρ₀, ∀ j : bk.DS bk.ρ₀ →+* bk.DA bk.ρ₀, IsDiscMap bk.ev j →
      s.W *ᵥ (fun a => j (x a)) = fun a => bk.iA (Y a b) := fun b =>
    (hY fun a => Y a b).2 ⟨Pi.single b 1, by
      funext a
      simp [Matrix.mulVec, dotProduct, Pi.single_apply, apply_ite]⟩
  have hφ := fun b => (hY _).1 (GlobalTheory.T.crystallineLattice_discSpan_frobenius_stable l K bk τ hτ d ρ hρ s _ (hcol b))
  choose x hx using hcol
  choose c hc using hφ
  have hZ : ∀ j : bk.DS bk.ρ₀ →+* bk.DA bk.ρ₀, IsDiscMap bk.ev j →
      s.W * (Matrix.of fun a b => x b a).map j = Y.map bk.iA :=
    fun j hj => Matrix.ext fun a b => congrFun (hx b j hj) a
  have hA : Y.map WittVector.frobenius = Y * (Matrix.of fun a b => c b a).map bk.ev :=
    Matrix.ext fun a b => congrFun (hc b) a
  obtain ⟨b, A', hA'⟩ := GlobalTheory.T.exists_frobenius_matrix_mul_eq_E_pow_of_period l K bk τ hτ d Y S' _ k' _ hYu hS' hA
  exact ⟨⟨Y, hYu, _, GlobalTheory.T.isUnit_discBasis_crystallineLattice l K bk τ hτ d ρ hρ s Y _ k' S' hS' hZ, hZ, 0, b, _, A', hA', by
    rw [pow_zero, one_smul]; exact hA⟩⟩

end GlobalTheory.BSP.HeightEx
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PrismComparisonMatrixPowSmulBoundedOnDisc
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP

theorem comparisonMatrix_bounded : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (d : ℕ) (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) ℤ_[l]) (τ : Ainf l) (s : Seed bk d ρ τ) (ht : Height s), bk.IsPer τ → ∀ (B : Obj l ↥(OL K)) (f g : Hom bk.prism B) (ι : Type), TopBasis (BK.hf f) bk.J ι → ∀ ε : Matrix (Fin d) (Fin d) (Disc l (BK.hf f X) bk.ρ₀), ht.Rel (BK.hf f X) f g ε → ∃ (k : ℕ) (x : Matrix (Fin d) (Fin d) B.A), x.map (toDisc l (BK.hf f X) bk.ρ₀) = ((l : ℕ) : Disc l (BK.hf f X) bk.ρ₀) ^ k • ε := by
  intro l _ K bk d ρ τ s ht hper B f g ι tb ε hrel
  have hnorm := GlobalTheory.T.norm_breuilKisinHom_uniformizer_frobenius_le l K bk B f g
  let Φ : Disc l (BK.hf f X) bk.ρ₀ →+* Disc l (BK.hf f X) bk.ρ₀ := Disc.map B.D.φ hnorm.2
  have hΦ : IsDiscMap B.D.φ Φ := isDiscMap_map _ _
  have hreg := GlobalTheory.T.toDisc_injective_and_nonZeroDivisors_of_topBasis l K bk B.A (BK.hf f) ι tb
  have hpair := GlobalTheory.T.breuilKisin_two_homs_E_regular_associated l K bk B f g
  have heq := GlobalTheory.T.comparisonMatrix_frobenius_disc l K bk d ρ τ s ht hper B f hreg.2.1 f g ε hrel Φ hΦ
  have hQ : ht.A.map (BK.hf g) * ht.A'.map (BK.hf g) =
      BK.hf g bk.E ^ ht.b • (1 : Matrix (Fin d) (Fin d) B.A) := by
    rw [← Matrix.map_mul (f := BK.hf g), ht.A_mul, Matrix.map_smul' _ _ _ (map_mul _), Matrix.map_one _ (map_zero _) (map_one _), map_pow]
  obtain ⟨h, c, hc⟩ := GlobalTheory.T.matrix_phi_equation_to_family_equation B.A (Disc l (BK.hf f X) bk.ρ₀) (toDisc l (BK.hf f X) bk.ρ₀) Φ
    (BK.hf f bk.E) (BK.hf g bk.E) hpair.2.1 d d (ht.a + s.N) (ht.a + s.N) ht.b (ht.A.map (BK.hf f))
    (ht.A.map (BK.hf g)) (ht.A'.map (BK.hf g)) hQ ε heq
  have hφX : B.D.φ (BK.hf f X) = BK.hf f X ^ l := by
    have h1 : B.D.φ (f.f X) = f.f (bk.prism.D.φ X) := (f.f_φ X).symm
    have h2 : bk.prism.D.φ X = X ^ l := frobS_X l bk.a
    exact h1.trans ((congrArg f.f h2).trans (map_pow f.f _ l))
  have key := GlobalTheory.T.exists_bounded_of_phi_equation_disc l K bk B.A (BK.hf f) ι tb B.D.φ hφX Φ hΦ (Fin d × Fin d) c
    (fun _ _ => Set.toFinite _) h (fun j => ε j.1 j.2)
  have htend : Filter.Tendsto (fun j : Fin d × Fin d => ε j.1 j.2) Filter.cofinite
      (nhds (0 : Disc l (BK.hf f X) bk.ρ₀)) := by
    simp only [Filter.cofinite_eq_bot, Filter.tendsto_bot]
  have hsum : ∀ j : Fin d × Fin d, HasSum (fun i => Φ (ε i.1 i.2) * toDisc l (BK.hf f X) bk.ρ₀ (c i j))
      (toDisc l (BK.hf f X) bk.ρ₀ (BK.hf f bk.E) ^ h * ε j.1 j.2) := fun j => by
    have hs := hasSum_fintype (fun i : Fin d × Fin d => Φ (ε i.1 i.2) * toDisc l (BK.hf f X) bk.ρ₀ (c i j))
    have e : toDisc l (BK.hf f X) bk.ρ₀ (BK.hf f bk.E) ^ h * ε j.1 j.2 =
        ∑ k : Fin d × Fin d, Φ (ε k.1 k.2) * toDisc l (BK.hf f X) bk.ρ₀ (c k j) := hc j
    convert hs using 1
  have k2 := key htend hsum
  obtain ⟨k, v, hv, -⟩ := k2
  refine ⟨k, Matrix.of fun i j => v (i, j), ?_⟩
  ext i j
  simp only [Matrix.map_apply, Matrix.of_apply, Matrix.smul_apply, smul_eq_mul]
  exact hv (i, j)

end GlobalTheory.BSP
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PrismaticFCrystalHomExtBreuilKisinPrismStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.prismaticFCrystalHom_ext_breuilKisin_prism : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (M M' : FCrys l ↥(OL K)) (u u' : FHom M M'), u.u bk.prism = u'.u bk.prism → u = u' := by
  first | exact @GlobalTheory.BSP.fhom_ext_bk | exact GlobalTheory.BSP.fhom_ext_bk | (intros; apply GlobalTheory.BSP.fhom_ext_bk <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.QuotientAverageUnipotentBlockColumnTransformEqZeStatement
section
open NumberField IsDedekindDomain MeasureTheory Matrix GlobalTheory.CuspRep GlobalTheory.CuspGeneric
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.quotientAverage_unipotentBlock_columnTransform_eq_zero : ∀ (E : Type) [Field E] [NumberField E] (a : ℕ) (ψ : AddChar (Ad E) ℂ), StdPsi ψ → ∀ (m : ℕ) (f : GA E a → ℂ), m + 1 < a → Good ψ (m + 1) f → ∀ r, 0 < r → r ≤ m → ∀ g : GA E a, avg (ratV E (UnipotentBlockColumnIndex a r m)) (fun n => colT ψ (m + 1) f (blkU n * g)) = 0 := by
  first | exact @GlobalTheory.CuspGeneric.avg_colT_blk_eq_zero | exact GlobalTheory.CuspGeneric.avg_colT_blk_eq_zero | (intros; apply GlobalTheory.CuspGeneric.avg_colT_blk_eq_zero <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RationalSourceActsOnOrientedThetaBySubstitution
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open GlobalTheory.RawLift
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RatSubst

theorem om_rat_left_apply : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (ω : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsWeilDatumO ψ S T χS χT ω → ∀ f, IsThetaFunO ψ S T f → ∀ γ ∈ GQ S, ∀ x, ω (γ, 1) f x = f (actO S T γ⁻¹ 1 x) := by
  intro D ψ S T χS χT ω hω f hf γ hγ x
  have h := GlobalTheory.SiegelFormula.om_rat_apply hω hγ (one_mem (GQ T)) (actO S T γ⁻¹ 1 x) hf
    (GlobalTheory.ThetaClosed.isThetaFunO_heisO_all hω.std hf _)
  have e : actO S T γ 1 (actO S T γ⁻¹ 1 x) = x := by
    have h1 : Formalism.L2.Theta.mt T 1 = 1 := rfl
    have h2 : Formalism.L2.Theta.mt S γ * Formalism.L2.Theta.mt S γ⁻¹ = 1 := by
      have : Formalism.L2.Theta.mt S (γ * γ⁻¹) = Formalism.L2.Theta.mt S γ * Formalism.L2.Theta.mt S γ⁻¹ := rfl
      rw [← this, mul_inv_cancel]; rfl
    unfold actO
    rw [inv_inv, h1, Matrix.one_mul, Matrix.one_mul, Matrix.mul_assoc, h2, Matrix.mul_one]
  rwa [e] at h

end GlobalTheory.RatSubst
end

