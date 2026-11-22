import Formalism.SharpRestriction.LevelLetterCocycles.LatticeBoundsOfThreeParts
import Formalism.SharpRestriction.LevelLetterCocycles.WachCoordinates
import Formalism.SharpRestriction.LevelLetterCocycles.ArcLiftingSetup
import Formalism.SharpRestriction.LevelLetterCocycles.QuotientImageDivisibility.Bundle0001
import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.CrystallineLiftingInputs
import Formalism.SharpRestriction.LevelLetterCocycles.QuotientImageDivisibility.Bundle0003

-- bundled from Formalism.SharpRestriction.LevelLetterCocycles.QuotientImageDivisibility.ContentBoundLevel
section
noncomputable section

namespace Formalism.MainNotions.N.Pv.LocalLengthBound

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc PowerSeries Formalism.MainNotions.N.Pv.LocalLengthBound.Ser TensorProduct

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}

def ContentBoundLevel [NeZero n] (W : LocWach PD LL O v n) : Prop :=
  ∀ (d : ℕ) (T₁ T₂ : LocLat G Qp LL O) (F : LatHom T₁.L T₂.L) (b : ZMod n → ℕ) (S η m : ℕ),
    Formalism.MainNotions.RamifiedCoefficientChains.SetCS W d T₁ T₂ F b S η m → ∀ c ∈ Formalism.MainNotions.RamifiedCoefficientChains.S9.evens n d,
    ∃ κ : ℤ, (κ : ℝ) ≤ (((b c + S : ℕ) : ℝ) + 1) / ((PD.p : ℝ) - 1) + 2 +
        Formalism.MainNotions.RamifiedCoefficientChains.S9.EG PD.p (Formalism.MainNotions.RamifiedCoefficientChains.hpar n b S) η S +
        Formalism.TruncatedSeriesCounting.RamifiedCoefficientChains.sig₂ PD.p (Formalism.MainNotions.RamifiedCoefficientChains.hpar n b S + η) +
        ((b (c - 1 - 1) + S : ℕ) : ℝ) - (b (c - 1) : ℝ) + 1 ∧
    ∀ ell ∈ (fun z => φVB PD (LL := LL) (V := T₂.V) (φVB PD (LL := LL) (V := T₂.V) z)) ''
        Formalism.MainNotions.CrystallineLiftingInputs.Dlat W T₂ (c - 1 - 1 - 1),
      ell ∈ FilCris PD T₂.ρ (b (c - 1) : ℤ) →
      ∃ y : W.DD T₁, Formalism.MainNotions.CrystallineLiftingInputs.InI W T₁ c y ∧
        ∃ hB : W.Q ^ (b c + S) • W.map F y ∈ W.N T₂,
        ∀ (ζ : LL), IsPrimitiveRoot ζ PD.p → ∀ (u : PowerSeries LL),
          W.lev c ζ W.q = X * u → constantCoeff u ≠ 0 →
        ∀ (dd : ℤ → T₂.V ⊗[Qp] BdR), (∃ m₀, LB m₀ dd) →
          W.levN T₂ c ζ ⟨W.Q ^ (b c + S) • W.map F y, hB⟩ = smulS ((X * u) ^ (b c + S)) dd →
          (∀ i : ℤ, i < ((b c + S : ℕ) : ℤ) → i ≠ 0 → dd i = 0) ∧
          dd 0 = ((PD.p : LL) ^ κ) • ιV PD (LL := LL) (V := T₂.V) (φVB PD (LL := LL) (V := T₂.V) ell) ∧
          ∀ i : ℤ, dd i ∈ Formalism.MainNotions.DeltaInvariantLattices.ιDi W T₂ c

end Formalism.MainNotions.N.Pv.LocalLengthBound
end
end

-- bundled from Formalism.SharpRestriction.LevelLetterCocycles.QuotientImageDivisibility.H2Bound
section
noncomputable section

namespace Formalism.MainNotions.N.Pv.LocalLengthBound

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc PowerSeries Formalism.MainNotions.N.Pv.LocalLengthBound.Ser TensorProduct

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}

def H2Bound [NeZero n] (W : LocWach PD LL O v n) : Prop :=
  ∀ (d : ℕ) (T₁ T₂ : LocLat G Qp LL O) (F : LatHom T₁.L T₂.L) (b : ZMod n → ℕ) (S η m : ℕ),
    Formalism.MainNotions.RamifiedCoefficientChains.SetCS W d T₁ T₂ F b S η m → ∀ c ∈ Formalism.MainNotions.RamifiedCoefficientChains.S9.evens n d,
    ∃ e : ℕ, (e : ℝ) ≤ Formalism.TruncatedSeriesCounting.RamifiedCoefficientChains.sig₂ PD.p (Formalism.MainNotions.RamifiedCoefficientChains.hpar n b S + η) +
        ((b (c - 1) + S : ℕ) : ℝ) - (b c : ℝ) / (PD.p : ℝ) +
        Formalism.MainNotions.RamifiedCoefficientChains.lam PD.p (Formalism.MainNotions.RamifiedCoefficientChains.hpar n b S + η) + 3 ∧
      ∀ (ζ : LL), IsPrimitiveRoot ζ PD.p → ∀ (u : PowerSeries LL),
        W.lev c ζ W.q = X * u → constantCoeff u ≠ 0 →
      ∀ (w : W.DD T₂), Formalism.MainNotions.RamifiedCoefficientChains.S9.QPowSmulMemPullback W T₂ c η w →
      ∀ (K : ℕ) (hK : W.Q ^ K • w ∈ W.N T₂) (dd : ℤ → T₂.V ⊗[Qp] BdR), (∃ m₀, LB m₀ dd) →
        W.levN T₂ c ζ ⟨W.Q ^ K • w, hK⟩ = smulS ((X * u) ^ K) dd →
        ∃ x ∈ Formalism.MainNotions.RamifiedCoefficientChains.S9.NDl W T₂ (c - 1 - 1),
          ((PD.p : LL) ^ e) • dd 0 - ιV PD (LL := LL) (V := T₂.V)
              (φVB PD (LL := LL) (V := T₂.V) (φVB PD (LL := LL) (V := T₂.V)
                (Formalism.MainNotions.ArcLiftingSetup.cmpD W T₂ x))) ∈
            Formalism.MainNotions.WachCoordinates.FilLev W T₂ c 0 (-(η : ℤ))

end Formalism.MainNotions.N.Pv.LocalLengthBound
end
end

-- bundled from Formalism.SharpRestriction.LevelLetterCocycles.QuotientImageDivisibility.LemmaDN0
section
noncomputable section

namespace Formalism.MainNotions.N.Pv.LocalLengthBound

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}

def LemmaDN0 [NeZero n] (W : LocWach PD LL O v n) : Prop :=
  ∀ (d : ℕ) (T₁ T₂ : LocLat G Qp LL O) (F : LatHom T₁.L T₂.L) (b : ZMod n → ℕ) (S η m : ℕ),
    Formalism.MainNotions.RamifiedCoefficientChains.SetCS W d T₁ T₂ F b S η m → m = 0 → ∀ i ∈ Formalism.MainNotions.RamifiedCoefficientChains.S9.evens n d,
    ∀ x ∈ Formalism.MainNotions.RamifiedCoefficientChains.S9.NDl W T₂ i,
      ((PD.p : O) ^ S) • x ∈ (Formalism.MainNotions.RamifiedCoefficientChains.S9.NDl W T₂ i).map
          (W.π₀ • (LinearMap.id : W.DD T₂ →ₗ[O] W.DD T₂)) ⊔
        (Formalism.MainNotions.RamifiedCoefficientChains.S9.PhiPullΔ W T₂ i).map
          ((Formalism.MainNotions.LiftingTheory.qp W ^ (b i + S)) • (LinearMap.id : W.DD T₂ →ₗ[O] W.DD T₂))

end Formalism.MainNotions.N.Pv.LocalLengthBound
end
end

-- bundled from Formalism.SharpRestriction.LevelLetterCocycles.QuotientImageDivisibility.MemZeroSubCoe
section
set_option linter.unusedVariables false

noncomputable section

namespace Formalism.MainNotions.N.Pv.LocalLengthBound

open Module Formalism.MainNotions.RamifiedCoefficientChains.S9

variable {O : Type} [CommRing O] {FF : Type} [AddCommGroup FF] [Module O FF]

def kerSub (A : Submodule O FF) {M : Type} [AddCommGroup M] [Module O M] (w : ↥A →ₗ[O] M)
    (Y : Submodule O M) : Submodule O FF :=
  (Y.comap w).map A.subtype

theorem mem_kerSub (A : Submodule O FF) {M : Type} [AddCommGroup M] [Module O M]
    (w : ↥A →ₗ[O] M) (Y : Submodule O M) (x : FF) :
    x ∈ kerSub A w Y ↔ ∃ h : x ∈ A, w ⟨x, h⟩ ∈ Y := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y.2, by simpa using hy⟩
  · rintro ⟨h, hY⟩
    exact ⟨⟨x, h⟩, hY, rfl⟩

theorem kerSub_le (A : Submodule O FF) {M : Type} [AddCommGroup M] [Module O M]
    (w : ↥A →ₗ[O] M) (Y : Submodule O M) : kerSub A w Y ≤ A := by
  rintro x ⟨y, -, rfl⟩
  exact y.2

theorem mem_kerSub_coe (A : Submodule O FF) {M : Type} [AddCommGroup M] [Module O M]
    (w : ↥A →ₗ[O] M) (Y : Submodule O M) (x : ↥A) :
    (x : FF) ∈ kerSub A w Y ↔ w x ∈ Y := by
  rw [mem_kerSub]
  exact ⟨fun ⟨_, h⟩ => h, fun h => ⟨x.2, h⟩⟩

theorem pstep_len (A : Submodule O FF) {M : Type} [AddCommGroup M] [Module O M]
    (w : ↥A →ₗ[O] M) (Y : Submodule O M) {lenO : ℕ∞} {m : ℕ} {c : ℝ} (L kO : ℕ)
    (hL : Module.length O (M ⧸ Y) ≤ (L : ℕ∞)) (hk : lenO = kO) (hc : (L : ℝ) ≤ c * kO) :
    PStep lenO m c A (kerSub A w Y) False := by
  refine ⟨kerSub_le A w Y, M ⧸ Y, inferInstance, inferInstance, Y.mkQ.comp w, fun x => ?_,
    fun h => h.elim, fun _ => ⟨L, kO, hL, hk, hc⟩⟩
  rw [LinearMap.comp_apply, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero,
    mem_kerSub_coe]

theorem pstep_gen (A : Submodule O FF) {M : Type} [AddCommGroup M] [Module O M]
    (w : ↥A →ₗ[O] M) (X : Submodule O M) (s : Finset M) {lenO : ℕ∞} {m : ℕ} {c : ℝ}
    (hs : s.card ≤ m) (hw : ∀ a, w a ∈ X ⊔ Submodule.span O (s : Set M)) :
    PStep lenO m c A (kerSub A w X) True := by
  classical
  set Y := X ⊔ Submodule.span O (s : Set M) with hY
  set Xc : Submodule O ↥Y := X.comap Y.subtype
  refine ⟨kerSub_le A w X, ↥Y ⧸ Xc, inferInstance, inferInstance,
    Xc.mkQ.comp (w.codRestrict Y hw), fun x => ?_, fun _ => ?_, fun h => (h trivial).elim⟩
  · rw [LinearMap.comp_apply, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero,
      mem_kerSub_coe]
    simp [Xc]
  · let ψ : ↥(Submodule.span O (s : Set M)) →ₗ[O] ↥Y ⧸ Xc :=
      Xc.mkQ.comp (Submodule.inclusion (le_sup_right : Submodule.span O (s : Set M) ≤ Y))
    let g : M → ↥Y ⧸ Xc := fun x =>
      if h : x ∈ Submodule.span O (s : Set M) then ψ ⟨x, h⟩ else 0
    refine ⟨s.image g, Finset.card_image_le.trans hs, ?_⟩
    have hrange : LinearMap.range ψ = ⊤ := by
      rw [eq_top_iff]
      rintro q -
      obtain ⟨⟨y, hy⟩, rfl⟩ := Submodule.Quotient.mk_surjective Xc q
      obtain ⟨x, hx, z, hz, rfl⟩ := Submodule.mem_sup.1 hy
      refine ⟨⟨z, hz⟩, ?_⟩
      simp only [ψ, LinearMap.comp_apply, Submodule.mkQ_apply]
      rw [Submodule.Quotient.eq]
      simp only [Xc, Submodule.mem_comap, Submodule.subtype_apply]
      have : ((Submodule.inclusion (le_sup_right : Submodule.span O (s : Set M) ≤ Y) ⟨z, hz⟩ -
          ⟨x + z, hy⟩ : ↥Y) : M) = -x := by
        simp
      rw [this]
      exact X.neg_mem hx
    rw [eq_top_iff, ← hrange, LinearMap.range_eq_map, ← Submodule.span_span_coe_preimage,
      Submodule.map_span]
    apply Submodule.span_mono
    rintro _ ⟨⟨x, hxs⟩, hx, rfl⟩
    refine Finset.mem_coe.2 (Finset.mem_image.2 ⟨x, hx, ?_⟩)
    simp [g, hxs]

end Formalism.MainNotions.N.Pv.LocalLengthBound

namespace Formalism.MainNotions.N.Pv.LocalLengthBound

open Module Formalism.MainNotions.RamifiedCoefficientChains.S9

variable {O : Type} [CommRing O] {FF : Type} [AddCommGroup FF] [Module O FF]

def zeroSubA {LL : Type} [Field LL] [Algebra O LL] {U : Type} [AddCommGroup U] [Module LL U]
    (A : Submodule O FF) (φ : ↥A →+ U) (hφ : ∀ (c : O) (x : ↥A), φ (c • x) = algebraMap O LL c • φ x) :
    Submodule O ↥A where
  carrier := {x | φ x = 0}
  zero_mem' := by simp
  add_mem' := fun {a b} ha hb => by simp only [Set.mem_setOf_eq] at *; rw [map_add, ha, hb, add_zero]
  smul_mem' := fun c x hx => by simp only [Set.mem_setOf_eq] at *; rw [hφ, hx, smul_zero]

def zeroSub {LL : Type} [Field LL] [Algebra O LL] {U : Type} [AddCommGroup U] [Module LL U]
    (A : Submodule O FF) (φ : ↥A →+ U) (hφ : ∀ (c : O) (x : ↥A), φ (c • x) = algebraMap O LL c • φ x) :
    Submodule O FF :=
  (zeroSubA A φ hφ).map A.subtype

theorem mem_zeroSub_coe {LL : Type} [Field LL] [Algebra O LL] {U : Type} [AddCommGroup U]
    [Module LL U] (A : Submodule O FF) (φ : ↥A →+ U)
    (hφ : ∀ (c : O) (x : ↥A), φ (c • x) = algebraMap O LL c • φ x) (x : ↥A) :
    (x : FF) ∈ zeroSub A φ hφ ↔ φ x = 0 := by
  constructor
  · rintro ⟨y, hy, hyx⟩
    have : y = x := Subtype.ext hyx
    subst this
    exact hy
  · intro h
    exact ⟨x, h, rfl⟩

theorem zeroSub_le {LL : Type} [Field LL] [Algebra O LL] {U : Type} [AddCommGroup U] [Module LL U]
    (A : Submodule O FF) (φ : ↥A →+ U)
    (hφ : ∀ (c : O) (x : ↥A), φ (c • x) = algebraMap O LL c • φ x) : zeroSub A φ hφ ≤ A := by
  rintro x ⟨y, -, rfl⟩
  exact y.2

theorem pstep_rank [IsDomain O] [IsPrincipalIdealRing O] {LL : Type} [Field LL] [Algebra O LL]
    [IsFractionRing O LL] [Module.Finite O FF] {U : Type} [AddCommGroup U] [Module LL U]
    (A : Submodule O FF) (φ : ↥A →+ U)
    (hφ : ∀ (c : O) (x : ↥A), φ (c • x) = algebraMap O LL c • φ x) {lenO : ℕ∞} {m : ℕ} {c : ℝ}
    (hm : finrank LL ↥(Submodule.span LL (Set.range φ)) ≤ m) :
    PStep lenO m c A (zeroSub A φ hφ) True := by
  classical
  set K := zeroSubA A φ hφ with hK
  refine ⟨zeroSub_le A φ hφ, ↥A ⧸ K, inferInstance, inferInstance, K.mkQ, fun x => ?_, fun _ => ?_,
    fun h => (h trivial).elim⟩
  · rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, mem_zeroSub_coe]
    rfl

  haveI : IsNoetherian O FF := isNoetherian_of_isNoetherianRing_of_finite O FF
  haveI : Module.Finite O ↥A := Module.IsNoetherian.finite O ↥A
  haveI : Module.Finite O (↥A ⧸ K) := Module.Finite.quotient O K

  have hinj : Function.Injective (algebraMap O LL) := IsFractionRing.injective O LL
  haveI : NoZeroSMulDivisors O (↥A ⧸ K) := by
    refine ⟨fun {a q} h => ?_⟩
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective K q
    rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero] at h
    by_cases ha : a = 0
    · exact Or.inl ha
    · right
      rw [Submodule.Quotient.mk_eq_zero]
      change φ (a • x) = 0 at h
      change φ x = 0
      rw [hφ] at h
      have ha' : algebraMap O LL a ≠ 0 := fun h0 => ha (hinj (by rw [h0, map_zero]))
      exact (smul_eq_zero.1 h).resolve_left ha'
  haveI : Module.Free O (↥A ⧸ K) := Module.free_of_finite_type_torsion_free'
  let ι := Module.Free.ChooseBasisIndex O (↥A ⧸ K)
  let bQ : Basis ι O (↥A ⧸ K) := Module.Free.chooseBasis O (↥A ⧸ K)

  have hrep : ∀ i, ∃ x : ↥A, K.mkQ x = bQ i := fun i => Submodule.Quotient.mk_surjective K (bQ i)
  choose xr hxr using hrep
  let u : ι → U := fun i => φ (xr i)
  have hu : LinearIndependent LL u := by
    rw [Fintype.linearIndependent_iff]
    intro g hg i
    obtain ⟨d, hd⟩ := IsLocalization.exist_integer_multiples_of_finset (nonZeroDivisors O)
      (Finset.univ.image g)
    have hint : ∀ j, ∃ a : O, algebraMap O LL a = (d : O) • g j := by
      intro j
      obtain ⟨a, ha⟩ := hd (g j) (Finset.mem_image_of_mem g (Finset.mem_univ j))
      exact ⟨a, ha⟩
    choose a ha using hint
    have hsum : φ (∑ j, a j • xr j) = 0 := by
      rw [map_sum]
      simp only [hφ, ha]
      simp only [Algebra.smul_def, mul_smul]
      rw [← Finset.smul_sum]
      change algebraMap O LL (d : O) • ∑ j, g j • u j = 0
      rw [hg, smul_zero]
    have hQ : ∑ j, a j • bQ j = 0 := by
      have : K.mkQ (∑ j, a j • xr j) = 0 := by
        rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
        exact hsum
      rw [map_sum] at this
      simpa [hxr] using this
    have hai : a i = 0 := (Fintype.linearIndependent_iff.1 bQ.linearIndependent) a hQ i
    have hd0 : algebraMap O LL (d : O) ≠ 0 := by
      intro h0
      have : (d : O) = 0 := hinj (by rw [h0, map_zero])
      exact nonZeroDivisors.coe_ne_zero d this
    have := ha i
    rw [hai, map_zero, Algebra.smul_def] at this
    exact (mul_eq_zero.1 this.symm).resolve_left hd0

  obtain ⟨gA, hgA⟩ := (Module.Finite.fg_top (R := O) (M := ↥A))
  have hspan : Submodule.span LL (Set.range φ) ≤ Submodule.span LL (φ '' (gA : Set ↥A)) := by
    rw [Submodule.span_le]
    rintro _ ⟨x, rfl⟩
    have hx : x ∈ Submodule.span O (gA : Set ↥A) := by rw [hgA]; trivial
    induction hx using Submodule.span_induction with
    | mem y hy => exact Submodule.subset_span ⟨y, hy, rfl⟩
    | zero => simp
    | add y z _ _ hy hz => rw [map_add]; exact Submodule.add_mem _ hy hz
    | smul r y _ hy => rw [hφ]; exact Submodule.smul_mem _ _ hy
  haveI : FiniteDimensional LL ↥(Submodule.span LL (φ '' (gA : Set ↥A))) :=
    FiniteDimensional.span_of_finite LL (gA.finite_toSet.image φ)
  haveI : FiniteDimensional LL ↥(Submodule.span LL (Set.range φ)) :=
    Submodule.finiteDimensional_of_le hspan
  let u' : ι → ↥(Submodule.span LL (Set.range φ)) := fun i =>
    ⟨u i, Submodule.subset_span ⟨xr i, rfl⟩⟩
  have hu' : LinearIndependent LL u' :=
    LinearIndependent.of_comp (Submodule.span LL (Set.range φ)).subtype hu
  have hcard : Fintype.card ι ≤ m := (hu'.fintype_card_le_finrank).trans hm
  refine ⟨Finset.univ.image bQ, Finset.card_image_le.trans (by simpa using hcard), ?_⟩
  rw [Finset.coe_image, Finset.coe_univ, Set.image_univ]
  exact bQ.span_eq

end Formalism.MainNotions.N.Pv.LocalLengthBound

namespace Formalism.MainNotions.N.Pv.LocalLengthBound

open Formalism.MainNotions.RamifiedCoefficientChains.S9

variable {O : Type} [CommRing O] {FF : Type} [AddCommGroup FF] [Module O FF]

theorem pchain_of_gen {lenO : ℕ∞} {m : ℕ} {c : ℝ} {A B : Submodule O FF}
    (h : PStep lenO m c A B True) : PChain lenO m c A B 1 0 := by
  refine ⟨1, fun i => if i = 0 then A else B, {0}, by simp, by simp, by simp, by simp, by simp,
    fun i hi => ?_⟩
  have hi0 : i = 0 := by omega
  subst hi0
  simpa using h

theorem pchain_of_len {lenO : ℕ∞} {m : ℕ} {c : ℝ} {A B : Submodule O FF}
    (h : PStep lenO m c A B False) : PChain lenO m c A B 0 1 := by
  refine ⟨1, fun i => if i = 0 then A else B, ∅, by simp, by simp, by simp, by simp, by simp,
    fun i hi => ?_⟩
  have hi0 : i = 0 := by omega
  subst hi0
  simpa using h

end Formalism.MainNotions.N.Pv.LocalLengthBound
end
end

-- bundled from Formalism.SharpRestriction.LevelLetterCocycles.QuotientImageDivisibility.RkDcrisLSumZero
section
noncomputable section

namespace Formalism.MainNotions.N.Pv.LocalLengthBound

open Formalism.WeaklyAdmissibleFiltrations Module TensorProduct

open Formalism.BasicNotions

section Dec

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}

private lemma mem_DcrisL_iff' (T : LocLat G Qp LL O) (σ : K₀ →ₐ[Qp] LL) (x : T.V ⊗[Qp] B) :
    x ∈ DcrisL PD T.ρ σ ↔ x ∈ Dcris PD T.ρ ∧
      ∀ c : K₀, mulVB (K₀ := K₀) (B := B) (V := T.V) (LL := LL) c x = σ c • x := by
  simp only [DcrisL, Submodule.mem_inf, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
    LinearMap.smul_apply, LinearMap.id_apply, sub_eq_zero]

private lemma mem_DdRE_iff' (T : LocLat G Qp LL O) (τ : K →ₐ[Qp] LL) (y : T.V ⊗[Qp] BdR) :
    y ∈ DdRE PD T.ρ τ ↔ y ∈ DdR PD T.ρ ∧
      ∀ c : K, mulVdR (K := K) (BdR := BdR) (V := T.V) (LL := LL) c y = τ c • y := by
  simp only [DdRE, Submodule.mem_inf, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
    LinearMap.smul_apply, LinearMap.id_apply, sub_eq_zero]

private lemma iotaV_injective (T : LocLat G Qp LL O) : Function.Injective (ιV PD (LL := LL) (V := T.V)) := by
  have h : ∀ x, ιV PD (LL := LL) (V := T.V) x =
      LinearMap.lTensor T.V (PD.ι.toLinearMap.restrictScalars Qp) x := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul a b => first | rfl | simp [ιV]
    | add a b ha hb => rw [map_add, map_add, ha, hb]
  intro x y hxy
  rw [h, h] at hxy
  exact Module.Flat.lTensor_preserves_injective_linearMap _ (by exact PD.ι_inj) hxy

private lemma iotaV_mulVB_comm (T : LocLat G Qp LL O) (c : K₀) (x : T.V ⊗[Qp] B) :
    ιV PD (LL := LL) (V := T.V) (mulVB (K₀ := K₀) (B := B) (V := T.V) (LL := LL) c x) =
      mulVdR (K := K) (BdR := BdR) (V := T.V) (LL := LL) (algebraMap K₀ K c)
        (ιV PD (LL := LL) (V := T.V) x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a b => simp [ιV, mulVB, mulVdR, ← IsScalarTower.algebraMap_apply]
  | add a b ha hb => rw [map_add, map_add, map_add, map_add, ha, hb]

theorem rk_lift (hK : Function.Bijective (algebraMap K₀ K)) (σ : K₀ →ₐ[Qp] LL) :
    ∃ τ : K →ₐ[Qp] LL, τ.comp (IsScalarTower.toAlgHom Qp K₀ K) = σ := by
  let e : K₀ ≃ₐ[Qp] K := AlgEquiv.ofBijective (IsScalarTower.toAlgHom Qp K₀ K) hK
  refine ⟨σ.comp (e.symm : K →ₐ[Qp] K₀), ?_⟩
  ext x
  have hx : (IsScalarTower.toAlgHom Qp K₀ K) x = e x := rfl
  simp only [AlgHom.comp_apply, hx, AlgEquiv.coe_algHom, AlgEquiv.symm_apply_apply]

variable [NeZero n] (W : LocWach PD LL O v n)

include W in
theorem rk_DcrisL_map (hK : Function.Bijective (algebraMap K₀ K)) (hQ : Formalism.MainNotions.RamifiedCoefficientChains.DdREqDcris PD LL)
    (T : LocLat G Qp LL O) (hT : IsCrys PD T.ρ) (τ : K →ₐ[Qp] LL) :
    (DcrisL PD T.ρ (τ.comp (IsScalarTower.toAlgHom Qp K₀ K))).map (ιV PD (LL := LL) (V := T.V)) =
      DdRE PD T.ρ τ := by
  have hD := (hQ hK T.V T.ρ hT).1
  ext y
  rw [Submodule.mem_map, mem_DdRE_iff']
  constructor
  · rintro ⟨x, hx, rfl⟩
    rw [mem_DcrisL_iff'] at hx
    refine ⟨?_, fun c => ?_⟩
    · rw [← hD]; exact Submodule.mem_map_of_mem hx.1
    · obtain ⟨c₀, rfl⟩ := hK.2 c
      rw [← iotaV_mulVB_comm, hx.2 c₀, map_smul]
      first | rfl | simp
  · rintro ⟨hyD, hyc⟩
    rw [← hD, Submodule.mem_map] at hyD
    obtain ⟨x, hxD, rfl⟩ := hyD
    refine ⟨x, (mem_DcrisL_iff' T _ x).mpr ⟨hxD, fun c₀ => ?_⟩, rfl⟩
    apply iotaV_injective (PD := PD) T
    rw [iotaV_mulVB_comm, hyc, map_smul]
    first | rfl | simp

include W in
theorem rk_finrank_DcrisL (hK : Function.Bijective (algebraMap K₀ K)) (hQ : Formalism.MainNotions.RamifiedCoefficientChains.DdREqDcris PD LL)
    (T : LocLat G Qp LL O) (hT : IsCrys PD T.ρ) (σ : K₀ →ₐ[Qp] LL) :
    finrank LL ↥(DcrisL PD T.ρ σ) = finrank LL T.V := by
  obtain ⟨τ, hτ⟩ := rk_lift hK σ
  rw [← hτ]
  have hmap := rk_DcrisL_map W hK hQ T hT τ
  have hE := (hQ hK T.V T.ρ hT).2 τ
  rw [← hE.2.1, ← hmap]
  exact (Submodule.equivMapOfInjective _ (iotaV_injective (PD := PD) T) _).finrank_eq

end Dec

end Formalism.MainNotions.N.Pv.LocalLengthBound
end
end

