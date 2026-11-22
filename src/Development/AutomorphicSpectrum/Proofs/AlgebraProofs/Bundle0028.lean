import Mathlib
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle0005
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle0001
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.IsLatFamilyLineFamZero
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0020
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0025
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsBundles
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.SameGenericSymm
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.LinearIndependentEigProj
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.QuotientEigenDifference
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0012
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0026
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0016
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.GermComp1ZeroPointLeft
import Development.WeilBound.CoreStatements.HodgeTatePoints.Comp1IdentityLeft
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0024
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle0002
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle0006
import Development.WeilBound.CoreStatements.HodgeTatePoints.Bundle0021
import Development.WeilBound.CoreStatements.HodgeTatePoints.Bundle0025

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.ChartBundleQuotientEquivalence
section
open MvPolynomial GlobalTheory.CompanionTheory.Ar.Num GroundTheory.Heights₂.Heights.NumbersDVR
open ReciprocityTheory.ChartRestriction.G.Geo (ChartBundle chartRing)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg mcIdeal chartMon joinCoord bcCoord pullDeg liftVar fnField ck rootNum SameGeneric LatLE IsPull IsPullBC IsSubQuot QuotIso IsFrobPres FlagModel modelDeg)

namespace GlobalTheory.CompanionTheory.Ar.Num.QuotEquivIso

theorem main : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (Ω : Type) [Field Ω] [Algebra O Ω] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (x : (Σ k, ι k) → Ω) (N N₁ : ℕ) (V : Type) [AddCommGroup V] [Module Ω V] (V₁ : Type) [AddCommGroup V₁] [Module Ω V₁] (E E' : ChartBundle O (mseg x) N V) (F F' : ChartBundle O (mseg x) N₁ V₁), QuotEquiv O x E.lat E'.lat F.lat F'.lat ↔ QuotIso O x E E' F F' := by
  intro O _ _ _ Ω _ _ K _ _ ι _ x N N₁ V _ _ V₁ _ _ E E' F F'
  unfold GlobalTheory.CompanionTheory.Ar.Num.QuotEquiv GlobalTheory.CompanionTheory.Ar.Num.IsQuotHom
    GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles.QuotIso
  constructor
  · rintro ⟨Γ, ⟨hlat, hΓ⟩, hΓ'⟩
    have hloc : ∀ s, GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles.mseg x s ≠ 0 →
        GlobalTheory.CompanionTheory.Ar.Num.LocFree
          (ReciprocityTheory.ChartRestriction.G.Geo.chartRing O (GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles.mseg x) s)
          (N + N₁) (Γ s) := by
      intro s hs
      obtain ⟨h1, h2, h3, _⟩ := hΓ s hs
      obtain ⟨_, h6⟩ := hΓ' s hs
      exact (GlobalTheory.CompanionTheory.Ar.Num.LocFreeSchanuel.main _ N N₁ (E.lat s) (F.lat s) (F'.lat s) (Γ s)
        (((GlobalTheory.CompanionTheory.Ar.Num.BundleOfFamily.main O Ω K ι x N V).2 E).2 s hs)
        (((GlobalTheory.CompanionTheory.Ar.Num.BundleOfFamily.main O Ω K ι x N₁ V₁).2 F).2 s hs)
        (((GlobalTheory.CompanionTheory.Ar.Num.BundleOfFamily.main O Ω K ι x N₁ V₁).2 F').2 s hs)
        (hlat.1 s hs) h1 h2 h3 h6).1
    obtain ⟨Pb, hPb⟩ := (GlobalTheory.CompanionTheory.Ar.Num.BundleOfFamily.main O Ω K ι x (N + N₁) (V × V₁)).1 Γ hlat hloc
    refine ⟨Pb, fun s hs => ?_⟩
    rw [hPb s hs]
    obtain ⟨h1, h2, h3, h4⟩ := hΓ s hs
    obtain ⟨h5, h6⟩ := hΓ' s hs
    exact ⟨fun v => ⟨h5 v, h4 v⟩, fun v => ⟨fun h => Exists.elim h fun w hw => (h1 v w hw).1, h2 v⟩, h3,
      fun w => ⟨fun h => Exists.elim h fun v hv => (h1 v w hv).2, h6 w⟩⟩
  · rintro ⟨Pb, hPb⟩
    refine ⟨Pb.lat, ⟨((GlobalTheory.CompanionTheory.Ar.Num.BundleOfFamily.main O Ω K ι x _ _).2 Pb).1, fun s hs => ?_⟩,
      fun s hs => ?_⟩
    · obtain ⟨h1, h2, h3, h4⟩ := hPb s hs
      exact ⟨fun v w hvw => ⟨(h2 v).1 ⟨w, hvw⟩, (h4 w).1 ⟨v, hvw⟩⟩, fun v hv => (h2 v).2 hv, h3,
        fun v hv => (h1 v).2 hv⟩
    · obtain ⟨h1, -, -, h4⟩ := hPb s hs
      exact ⟨fun v hv => (h1 v).1 hv, fun w hw => (h4 w).2 hw⟩

end GlobalTheory.CompanionTheory.Ar.Num.QuotEquivIso
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.EigCoordApply
section
open scoped NNReal
open NumberField GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference GlobalTheory.CompanionTheory.Ar

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Flat.ExG

def kerFil {C : Type} [Field C] {w : Valuation C ℝ≥0} {S W : Type} [AddCommGroup W] [Module C W]
    (a : S → w.valuationSubring) (r : ℕ) (g : S → (Fin r → C) →ₗ[C] W) :
    Submodule w.valuationSubring (S → Fin r → C) where
  carrier := {f | f ∈ freeLattice a r ∧ ∀ s, g s (f s) = 0}
  zero_mem' := ⟨zero_mem _, fun s => by simp⟩
  add_mem' := fun hx hy => ⟨add_mem hx.1 hy.1, fun s => by simp [hx.2 s, hy.2 s]⟩
  smul_mem' := fun c f hf => ⟨Submodule.smul_mem _ c hf.1, fun s => by
    have e : (c • f) s = (c : C) • f s := rfl
    rw [e, map_smul, hf.2 s, smul_zero]⟩

theorem mem_kerFil {C : Type} [Field C] {w : Valuation C ℝ≥0} {S W : Type} [AddCommGroup W] [Module C W]
    {a : S → w.valuationSubring} {r : ℕ} {g : S → (Fin r → C) →ₗ[C] W} {f : S → Fin r → C} :
    f ∈ kerFil a r g ↔ f ∈ freeLattice a r ∧ ∀ s, g s (f s) = 0 := Iff.rfl

def eigCoord {E : Type} [Field E] [NumberField E] {C M : Type} [Field C] [AddCommGroup M] [Module C M]
    (ρ : 𝓞 E →+* Module.End C M) {N : ℕ} (t : Fin N → M) (s : E →+* C) : (Fin N → C) →ₗ[C] M :=
  Fintype.linearCombination C (fun j => HT.eigProj ρ s (t j))

theorem eigCoord_apply {E : Type} [Field E] [NumberField E] {C M : Type} [Field C] [AddCommGroup M] [Module C M]
    (ρ : 𝓞 E →+* Module.End C M) {N : ℕ} (t : Fin N → M) (s : E →+* C) (y : Fin N → C) :
    eigCoord ρ t s y = ∑ j, y j • HT.eigProj ρ s (t j) := by
  simp [eigCoord, Fintype.linearCombination_apply]

def TargetO : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] (C : Type) [Field C] [CharZero C] (ν : Valuation C ℝ≥0)
    (bar : 𝓞 E ≃+* 𝓞 E) (σ σ' : E →+* C) (rk : (E →+* C) → ℕ) (p q : ℕ),
    (∃ ℓ : C, 0 < ν ℓ ∧ ν ℓ < 1) →
    (∀ (s : E →+* C) (a : 𝓞 E), s (a : E) ∈ ν.valuationSubring) →
    Nat.card (E →+* C) = Module.finrank ℚ E → (∀ a : 𝓞 E, σ' (a : E) = σ (bar a : 𝓞 E)) →
    (∀ a, bar (bar a) = a) →
    ∃ γ : C, γ ≠ 0 ∧ ∀ (W : Type) [AddCommGroup W] [Module C W] [Module ν.valuationSubring W]
      [IsScalarTower ν.valuationSubring C W] [FiniteDimensional C W]
      (ρ : 𝓞 E →+* Module.End C W) (ρH : 𝓞 E →+* Module.End C (W × Module.Dual C W))
      (HV : Submodule ν.valuationSubring (W × Module.Dual C W)) (Lie : Submodule ν.valuationSubring W)
      (x : Fin (p + q) → W × Module.Dual C W) (v : Fin p → W) (w : Fin q → W)
      (u : Fin (p + q) → W × Module.Dual C W) (A : Matrix (Fin (p + q)) (Fin (p + q)) C),
      (∀ a y, (ρH a y).1 = ρ a y.1) → (∀ a φ, ρH a (0, φ) = (0, φ ∘ₗ ρ (bar a))) →
      HV.map ((LinearMap.fst C W (Module.Dual C W)).restrictScalars ν.valuationSubring) = Lie →
      (∀ φ : Module.Dual C W, (0, φ) ∈ HV ↔ ∀ e ∈ Lie, φ e ∈ (algebraMap ν.valuationSubring C).range) →
      HT.IsFreeOn ρH HV x → (∀ s, Module.finrank C (HT.eigSp ρ s) = rk s) →
      LinearIndependent C v → Submodule.span ν.valuationSubring (Set.range v) = HT.eigSub ρ σ Lie →
      LinearIndependent C w → Submodule.span ν.valuationSubring (Set.range w) = HT.eigSub ρ σ' Lie →
      IsAdapted ρH σ v w u → LinearIndependent C (fun i => ∑ j, A i j • u j) →
      Submodule.span ν.valuationSubring (Set.range fun i => ∑ j, A i j • u j) = HT.eigQuot ρH σ HV →
      ∃ ε : (ν.valuationSubring)ˣ, A.det = algebraMap ν.valuationSubring C ε * γ

end GlobalTheory.CompanionTheory.Ar.Flat.ExG
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.FilteredExactSequenceProjectorBundles
section
open GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Flat.DegCurve

namespace GlobalTheory.CompanionTheory.Ar.Flat.DegCurve

theorem subDeg_range_shortExact : ∀ (K : Type) [Field K] (C : ACurve K) (V : Type) [AddCommGroup V] [Module K V] [FiniteDimensional K V] (V' : Type) [AddCommGroup V'] [Module K V'] [FiniteDimensional K V'] (V'' : Type) [AddCommGroup V''] [Module K V''] [FiniteDimensional K V''] (L : C.I → AddSubgroup V) (L' : C.I → AddSubgroup V') (L'' : C.I → AddSubgroup V'') (f : V →ₗ[K] V') (g : V' →ₗ[K] V'') (P : V →ₗ[K] V) (P' : V' →ₗ[K] V') (P'' : V'' →ₗ[K] V''), IsBun C L' → ShortExact C L L' L'' f g → (∀ x, P (P x) = P x) → (∀ x, P' (P' x) = P' x) → (∀ x, P'' (P'' x) = P'' x) → (∀ x, f (P x) = P' (f x)) → (∀ y, g (P' y) = P'' (g y)) → IsHom C L' L' P' → subDeg C L' (LinearMap.range P') = subDeg C L (LinearMap.range P) + subDeg C L'' (LinearMap.range P'') := by
  intro K _ C V _ _ _ V' _ _ _ V'' _ _ _ L L' L'' f g P P' P'' hB hSE hP hP' hP'' hfP hgP hHom
  obtain ⟨hinj, hex, hsurj, hL, hL''⟩ := hSE
  have mP : ∀ v ∈ LinearMap.range P, P v = v := by
    intro v hv
    obtain ⟨u, rfl⟩ := LinearMap.mem_range.1 hv
    exact hP u
  have mP' : ∀ v ∈ LinearMap.range P', P' v = v := by
    intro v hv
    obtain ⟨u, rfl⟩ := LinearMap.mem_range.1 hv
    exact hP' u
  have mP'' : ∀ v ∈ LinearMap.range P'', P'' v = v := by
    intro v hv
    obtain ⟨u, rfl⟩ := LinearMap.mem_range.1 hv
    exact hP'' u
  let f₀ : LinearMap.range P →ₗ[K] LinearMap.range P' :=
    LinearMap.codRestrict (LinearMap.range P') (f.domRestrict (LinearMap.range P)) (fun v =>
      LinearMap.mem_range.2 ⟨f v, by
        show P' (f v) = f v
        rw [← hfP, mP _ v.2]⟩)
  let g₀ : LinearMap.range P' →ₗ[K] LinearMap.range P'' :=
    LinearMap.codRestrict (LinearMap.range P'') (g.domRestrict (LinearMap.range P')) (fun v =>
      LinearMap.mem_range.2 ⟨g v, by
        show P'' (g v) = g v
        rw [← hgP, mP' _ v.2]⟩)
  have hSE0 : ShortExact C (sub C L (LinearMap.range P)) (sub C L' (LinearMap.range P'))
      (sub C L'' (LinearMap.range P'')) f₀ g₀ := by
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · intro x y h
      apply Subtype.ext
      apply hinj
      exact congrArg Subtype.val h
    · intro y
      constructor
      · intro hy
        have hy' : g (y : V') = 0 := congrArg Subtype.val hy
        obtain ⟨x, hx⟩ := (hex (y : V')).1 hy'
        refine ⟨⟨P x, LinearMap.mem_range_self P x⟩, ?_⟩
        apply Subtype.ext
        show f (P x) = (y : V')
        rw [hfP, hx, mP' _ y.2]
      · rintro ⟨x, rfl⟩
        apply Subtype.ext
        show g (f (x : V)) = 0
        exact (hex _).2 ⟨x, rfl⟩
    · intro z
      obtain ⟨y, hy⟩ := hsurj (z : V'')
      refine ⟨⟨P' y, LinearMap.mem_range_self P' y⟩, ?_⟩
      apply Subtype.ext
      show g (P' y) = (z : V'')
      rw [hgP, hy, mP'' _ z.2]
    · intro i x
      show (x : V) ∈ L i ↔ f (x : V) ∈ L' i
      exact hL i x
    · intro i z
      constructor
      · intro hz
        obtain ⟨y, hyL, hy⟩ := (hL'' i z).1 hz
        refine ⟨⟨P' y, LinearMap.mem_range_self P' y⟩, hHom i y hyL, ?_⟩
        apply Subtype.ext
        show g (P' y) = (z : V'')
        rw [hgP, hy, mP'' _ z.2]
      · rintro ⟨y, hyL, rfl⟩
        exact (hL'' i _).2 ⟨y, hyL, rfl⟩
  have hBW : IsBun C (sub C L' (LinearMap.range P')) :=
    (SubQuot.isBun_sub_quot K C V' L' (LinearMap.range P') hB).1
  exact (deg_shortExact K C (LinearMap.range P) (LinearMap.range P') (LinearMap.range P'')
    (sub C L (LinearMap.range P)) (sub C L' (LinearMap.range P')) (sub C L'' (LinearMap.range P''))
    f₀ g₀ hBW hSE0).2.2

end GlobalTheory.CompanionTheory.Ar.Flat.DegCurve
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.FormalBilinearTermProduct
section
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj

namespace GlobalTheory.CompanionTheory.Ar.Conj.BilCalc

theorem bil_calc : ∀ (R : Type) [CommRing R] (d : ℕ) (f g : PS R 2 d) (φ ψ : Pt R 1 d), AxOne f → AxOne g → (∀ i, constantCoeff (φ i) = 0) → (∀ i, constantCoeff (ψ i) = 0) → AxOne (f * g) ∧ (∀ m, bil (f * g) m 1 = bil f m 1 + bil g m 1) ∧ (∀ n, bil (f * g) 1 n = bil f 1 n + bil g 1 n) ∧ AxOne (ev (n := 2) ![comp1 φ (pt R d 0), comp1 ψ (pt R d 1)] f) ∧ bil (ev (n := 2) ![comp1 φ (pt R d 0), comp1 ψ (pt R d 1)] f) 1 1 = (lin φ 1).transpose * bil f 1 1 * lin ψ 1 ∧ (∀ m n, bil (ev (n := 2) ![pt R d 1, pt R d 0] f) m n = (bil f n m).transpose) ∧ ∀ m n : ℕ, 1 ≤ m → 1 ≤ n → bil (ev (n := 2) ![ptPow R d m 0, ptPow R d n 1] f) m n = bil f 1 1 :=
  @PositivityTheory.HtPt.Ca.bil_calc

end GlobalTheory.CompanionTheory.Ar.Conj.BilCalc
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.FormalLinearTermCompositionStatement
section
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.formal_linear_term_composition : ∀ (R : Type) [CommRing R] (d : ℕ) (φ ψ : Pt R 1 d), (∀ i, constantCoeff (φ i) = 0) → (∀ i, constantCoeff (ψ i) = 0) → lin (comp1 φ ψ) 1 = lin φ 1 * lin ψ 1 ∧ lin (pt R (n := 1) d 0) 1 = 1 ∧ ∀ p : ℕ, 1 ≤ p → lin (comp1 φ (ptPow R d p 0)) p = lin φ 1 ∧ lin (comp1 φ (comp1 ψ (ptPow R d p 0))) p = lin φ 1 * lin ψ 1 := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Conj.lin_comp_chain | exact GlobalTheory.CompanionTheory.Ar.Conj.lin_comp_chain | (intros; apply GlobalTheory.CompanionTheory.Ar.Conj.lin_comp_chain <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.FormalModuleActionLaws
section
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj

namespace GlobalTheory.CompanionTheory.Ar.Conj.NatAct

theorem act_nat_iterated : ∀ (R : Type) [CommRing R] (d : ℕ) (O : Type) [CommRing O] [StarRing O] (B : FB R d O), B.A.act 0 = 0 ∧ (∀ n : ℕ, B.A.act ((n + 1 : ℕ) : O) = B.G.add (B.A.act (n : O)) (pt R d 0)) ∧ (∀ a b, comp1 (B.A.act a) (B.A.act b) = comp1 (B.A.act b) (B.A.act a)) ∧ ∀ n, AxOne (pow1 B n) ∧ AxOne (pow2 B n) :=
  @PositivityTheory.HtPt.Ca.act_zero

end GlobalTheory.CompanionTheory.Ar.Conj.NatAct
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.HermitianSignatureBasis
section
open AlgebraicGeometry CategoryTheory Limits NumberField GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Flat

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Flat.AdaptedEx

section Main

variable {E : Type} [Field E] [NumberField E] {K W : Type} [Field K] [AddCommGroup W] [Module K W]
  {ρ : 𝓞 E →+* Module.End K W} {ρH : 𝓞 E →+* Module.End K (W × Module.Dual K W)}

theorem fst_proj (hact : ∀ a y, (ρH a y).1 = ρ a y.1) (σ : E →+* K) (y : W × Module.Dual K W) :
    (HT.eigProj ρH σ y).1 = HT.eigProj ρ σ y.1 := by
  simp only [HT.eigProj, LinearMap.sum_apply, LinearMap.smul_apply, Prod.fst_sum, Prod.smul_fst, hact]

theorem comp_proj {bar : 𝓞 E ≃+* 𝓞 E} (hinr : ∀ a f, ρH a (0, f) = (0, f ∘ₗ ρ (bar a))) {σ σ' : E →+* K}
    (hσ : ∀ a : 𝓞 E, σ' (a : E) = σ (bar a : 𝓞 E)) (hb : ∀ a, bar (bar a) = a) {φ : Module.Dual K W}
    (h : ((0 : W), φ) ∈ HT.eigSp ρH σ) : φ ∘ₗ HT.eigProj ρ σ' = φ := by
  have h3 : ∀ k z, φ (ρ (RingOfIntegers.basis E k) z) = σ' ((RingOfIntegers.basis E k : 𝓞 E) : E) • φ z := by
    intro k z
    have h1 := HT.LatBasic.mem_eigSp.1 h (bar (RingOfIntegers.basis E k))
    rw [hinr, hb, ← hσ] at h1
    have h2 := congrArg Prod.snd h1
    exact LinearMap.congr_fun h2 z
  have h2 : ∑ k, σ' (HT.dualInt E k) * σ' ((RingOfIntegers.basis E k : 𝓞 E) : E) = 1 := by
    rw [← map_one σ', ← HT.LatBasic.sum_dualInt_mul, map_sum]
    simp
  ext z
  simp only [HT.eigProj, LinearMap.comp_apply, LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_smul, h3,
    smul_smul]
  rw [← Finset.sum_smul, h2, one_smul]

theorem dual_frame [CharZero K] {q : ℕ} {b : Fin q → W} (hb : LinearIndependent K b) {τ : E →+* K}
    (hspan : Submodule.span K (Set.range b) = HT.eigSp ρ τ) :
    ∃ f : Fin q → Module.Dual K W, (∀ x, HT.eigProj ρ τ x = ∑ j, f j x • b j) ∧
      (∀ j j', f j (b j') = if j = j' then 1 else 0) ∧
      ∀ j (c : 𝓞 E), f j ∘ₗ ρ c = τ (c : E) • f j := by
  classical
  let B := Module.Basis.span hb
  let π : W →ₗ[K] Submodule.span K (Set.range b) := (HT.eigProj ρ τ).codRestrict _ fun x => by
    rw [hspan]
    exact HT.LatBasic.eigProj_mem ρ τ x
  have hπ : ∀ x, ((π x : Submodule.span K (Set.range b)) : W) = HT.eigProj ρ τ x := fun x => rfl
  have hfix : ∀ x ∈ HT.eigSp ρ τ, HT.eigProj ρ τ x = x := fun x hx => HT.LatBasic.eigProj_of_mem hx
  refine ⟨fun j => B.coord j ∘ₗ π, fun x => ?_, fun j j' => ?_, fun j c => ?_⟩
  · have h1 := congrArg Subtype.val (B.sum_repr (π x))
    rw [hπ] at h1
    rw [← h1, AddSubmonoidClass.coe_finsetSum]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp [B, Module.Basis.span_apply]
  · have h1 : π (b j') = B j' := Subtype.ext (by
      rw [hπ, Module.Basis.span_apply]
      exact hfix _ (hspan ▸ Submodule.subset_span ⟨j', rfl⟩))
    simp [h1, Finsupp.single_apply, eq_comm]
  · ext x
    have h1 : π (ρ c x) = τ (c : E) • π x := Subtype.ext (by
      have h2 : HT.eigProj ρ τ (ρ c x) = ρ c (HT.eigProj ρ τ x) := by
        have hcomm : ∀ k, ρ (RingOfIntegers.basis E k) (ρ c x) = ρ c (ρ (RingOfIntegers.basis E k) x) := fun k => by
          rw [← Module.End.mul_apply, ← map_mul, mul_comm, map_mul, Module.End.mul_apply]
        simp only [HT.eigProj, LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_smul, hcomm]
      rw [hπ, h2, HT.LatBasic.mem_eigSp.1 (HT.LatBasic.eigProj_mem ρ τ x) c]
      rfl)
    simp [h1]

end Main

theorem exists_adapted_basis : ∀ (E : Type) [Field E] [NumberField E] (K W : Type) [Field K] [CharZero K] [AddCommGroup W] [Module K W] [FiniteDimensional K W] (ρ : 𝓞 E →+* Module.End K W) (ρH : 𝓞 E →+* Module.End K (W × Module.Dual K W)) (bar : 𝓞 E ≃+* 𝓞 E) (σ σ' : E →+* K) (p q : ℕ) (v : Fin p → W) (w : Fin q → W), (∀ a y, (ρH a y).1 = ρ a y.1) → (∀ a φ, ρH a (0, φ) = (0, φ ∘ₗ ρ (bar a))) → (∀ a : 𝓞 E, σ' (a : E) = σ (bar a : 𝓞 E)) → (∀ a, bar (bar a) = a) → LinearIndependent K v → Submodule.span K (Set.range v) = HT.eigSp ρ σ → LinearIndependent K w → Submodule.span K (Set.range w) = HT.eigSp ρ σ' → ∃ u, IsAdapted ρH σ v w u ∧ LinearIndependent K u ∧ Submodule.span K (Set.range u) = HT.eigSp ρH σ := by
  intro E _ _ K W _ _ _ _ _ ρ ρH bar σ σ' p q v w hact hinr hσσ' hbar hv hvs hw hws
  classical
  obtain ⟨f, hf1, hf2, hf4⟩ := dual_frame hw hws
  let u : Fin (p + q) → W × Module.Dual K W :=
    Fin.addCases (fun i => HT.eigProj ρH σ (v i, 0)) (fun j => ((0 : W), f j))
  have hul : ∀ i, u (Fin.castAdd q i) = HT.eigProj ρH σ (v i, 0) := fun i => by simp [u]
  have hur : ∀ j, u (Fin.natAdd p j) = ((0 : W), f j) := fun j => by simp [u]
  have hvm : ∀ i, v i ∈ HT.eigSp ρ σ := fun i => hvs ▸ Submodule.subset_span ⟨i, rfl⟩
  have hu1 : ∀ i, (u (Fin.castAdd q i)).1 = v i := fun i => by
    rw [hul, fst_proj hact]
    exact HT.LatBasic.eigProj_of_mem (hvm i)
  have hueig : ∀ i, u i ∈ HT.eigSp ρH σ := by
    intro i
    induction i using Fin.addCases with
    | left i =>
      rw [hul]
      exact HT.LatBasic.eigProj_mem _ _ _
    | right j =>
      rw [hur, HT.LatBasic.mem_eigSp]
      intro a
      have h1 := hf4 j (bar a)
      rw [hσσ', hbar] at h1
      rw [hinr, h1]
      simp
  have had : IsAdapted ρH σ v w u := by
    unfold IsAdapted
    exact ⟨hueig, hu1, fun j => ⟨by rw [hur], fun j' => by rw [hur]; exact hf2 j j'⟩⟩
  refine ⟨u, had, ?_, le_antisymm ?_ ?_⟩
  · rw [Fintype.linearIndependent_iff]
    intro g hg
    rw [Fin.sum_univ_add] at hg
    have h1 : ∑ i, g (Fin.castAdd q i) • v i = 0 := by
      have h := congrArg Prod.fst hg
      simpa [Prod.fst_sum, hu1, hur] using h
    have hc := Fintype.linearIndependent_iff.1 hv _ h1
    have h3 : ∑ j, g (Fin.natAdd p j) • f j = 0 := by
      have h := congrArg Prod.snd hg
      simpa [Prod.snd_sum, hur, hc] using h
    have hd : ∀ j', g (Fin.natAdd p j') = 0 := fun j' => by
      have h := LinearMap.congr_fun h3 (w j')
      simpa [LinearMap.sum_apply, hf2] using h
    intro i
    induction i using Fin.addCases with
    | left i => exact hc i
    | right j => exact hd j
  · rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    exact hueig i
  · intro y hye
    have hy1 : y.1 ∈ Submodule.span K (Set.range v) := by
      rw [hvs]
      refine HT.LatBasic.mem_eigSp.2 fun a => ?_
      rw [← hact, HT.LatBasic.mem_eigSp.1 hye a]
      rfl
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun K).1 hy1
    obtain ⟨z, hz⟩ : ∃ z, z = y - ∑ i, c i • u (Fin.castAdd q i) := ⟨_, rfl⟩
    have hze : z ∈ HT.eigSp ρH σ := by
      rw [hz]
      exact Submodule.sub_mem _ hye (Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (hueig _))
    have hz1 : z.1 = 0 := by
      rw [hz, Prod.fst_sub, Prod.fst_sum, sub_eq_zero, ← hc]
      simp [hu1]
    have hzz : ((0 : W), z.2) = z := Prod.ext hz1.symm rfl
    have hcomp : z.2 ∘ₗ HT.eigProj ρ σ' = z.2 := comp_proj hinr hσσ' hbar (hzz.symm ▸ hze)
    have hd : z.2 = ∑ j, z.2 (w j) • f j := by
      ext x
      have h1 := LinearMap.congr_fun hcomp x
      rw [LinearMap.comp_apply, hf1, map_sum] at h1
      rw [← h1]
      simp [LinearMap.sum_apply, mul_comm]
    have e2 : ∑ j, z.2 (w j) • (((0 : W), f j) : W × Module.Dual K W) = z := by
      refine Prod.ext ?_ ?_
      · simp [Prod.fst_sum, hz1]
      · rw [Prod.snd_sum]
        simpa using hd.symm
    have e3 : y = ∑ i, (Fin.addCases c (fun j => z.2 (w j)) i : K) • u i := by
      rw [Fin.sum_univ_add]
      simp only [Fin.addCases_left, Fin.addCases_right, hur]
      rw [e2, hz]
      abel
    rw [e3]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

end GlobalTheory.CompanionTheory.Ar.Flat.AdaptedEx
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.HodgeAnnihilatorLatticeHoldsStatement
section
open GlobalTheory.CompanionTheory.Ar.Num
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hodge_annihilator_lattice_holds : ∀ {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {F : Type} [Zero F] [One F] [Fintype F] {n : ℕ} {Sg : Type} {r s : Sg → ℕ} (D : LieLatticeData Ω F n Sg r s) (R : Subalgebra o Ω) (p : ℕ) (w : Ω) (χ : Sg → F → Ω), CharData R p w χ → D.Base R p w → p.Prime → IsNoetherianRing R → IsFractionRing R Ω → IsIntegrallyClosedIn R Ω → ∀ φ : Equiv.Perm Sg, D.TestFacts R p w χ φ → D.Good₁ R p χ → ∀ τ, mulLat w (stdLat R _) ≤ D.af R p (χ τ) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Num.hodge_annihilator_lattice | exact GlobalTheory.CompanionTheory.Ar.Num.hodge_annihilator_lattice | (intros; apply GlobalTheory.CompanionTheory.Ar.Num.hodge_annihilator_lattice <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.HodgeTateChartDifferentBound
section
open Module NumberField GlobalTheory.CompanionTheory.Ar.HT TensorProduct

namespace GlobalTheory.CompanionTheory.Ar.HT

theorem dualMap_exists_unique_split : ∀ (A K : Type) [CommRing A] [Field K] [Algebra A K] [CharZero K] (hAK : Function.Injective (algebraMap A K)) (E : Type) [Field E] [NumberField E] (c : E ≃+* E) (hc : ∀ x, c (c x) = x) (p R N : ℕ) [Fact p.Prime] (Ω : Type) [AddCommGroup Ω] [Module K Ω] [Module A Ω] [IsScalarTower A K Ω] (D : HTChart A K c p R N Ω) (κ : A) (σ : E →+* K) (d : A) (m : ℕ), (∀ (σ : E →+* K) (a : 𝓞 E), σ (a : E) ∈ (algebraMap A K).range) → GeneratesDiff σ d → κ * (p : A) ^ m ∣ (p : A) ^ R → (∀ x ∈ D.om, κ • x ∈ D.om') → Module.Projective A (D.omHT (σ.comp c.toRingHom)) → (∃ (i : Module.Dual A (D.omHT (σ.comp c.toRingHom)) →ₗ[A] (Fin N → A)), D.IsDualMap σ d m i) ∧ (∀ i i', D.IsDualMap σ d m i → D.IsDualMap σ d m i' → ∀ w, ∃ x : Fin N → A, i w = i' w + ((p : A) ^ m) • x) ∧ ∀ i, D.IsDualMap σ d m i → ∃ r : (Fin N → A) →ₗ[A] Module.Dual A (D.omHT (σ.comp c.toRingHom)), ∀ w, ∃ w', r (i w) = w + ((p : A) ^ m) • w' :=
  @PositivityTheory.HtPt.Ga.dual_map

end GlobalTheory.CompanionTheory.Ar.HT
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.HodgeTateChartDifferentGeneratorsStatement
section
open Module NumberField GlobalTheory.CompanionTheory.Ar.HT TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hodge_tate_chart_different_generators : ∀ (A K : Type) [CommRing A] [Field K] [Algebra A K] [CharZero K] (hAK : Function.Injective (algebraMap A K)) (E : Type) [Field E] [NumberField E] (c : E ≃+* E) (hc : ∀ x, c (c x) = x) (p R N : ℕ) [Fact p.Prime] (Ω : Type) [AddCommGroup Ω] [Module K Ω] [Module A Ω] [IsScalarTower A K Ω] (D : HTChart A K c p R N Ω) (σ : E →+* K) (d : A), (∀ a : 𝓞 E, σ (a : E) ∈ (algebraMap A K).range) → GeneratesDiff σ d → ∃ G H Z Z' : Matrix (Fin N) (Fin N) A, (∀ i j, algebraMap A K (G i j) = D.gram σ d i j) ∧ G * H = 1 + ((p : A) ^ R) • Z ∧ H * G = 1 + ((p : A) ^ R) • Z' := by
  first | exact @GlobalTheory.CompanionTheory.Ar.HT.gram_integral_unit_mod | exact GlobalTheory.CompanionTheory.Ar.HT.gram_integral_unit_mod | (intros; apply GlobalTheory.CompanionTheory.Ar.HT.gram_integral_unit_mod <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.HodgeTateChartDivisibilityStatement
section
open Module NumberField GlobalTheory.CompanionTheory.Ar.HT TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hodge_tate_chart_divisibility : ∀ (A K : Type) [CommRing A] [Field K] [Algebra A K] [CharZero K] (hAK : Function.Injective (algebraMap A K)) (E : Type) [Field E] [NumberField E] (c : E ≃+* E) (hc : ∀ x, c (c x) = x) (p R N : ℕ) [Fact p.Prime] (Ω : Type) [AddCommGroup Ω] [Module K Ω] [Module A Ω] [IsScalarTower A K Ω] (D : HTChart A K c p R N Ω) (κ : A) (σ : E →+* K) (m : ℕ), (∀ a : 𝓞 E, σ (a : E) ∈ (algebraMap A K).range) → κ * (p : A) ^ m ∣ (p : A) ^ R → (∀ x ∈ D.om, κ • x ∈ D.om') → (∀ x, D.q σ x ∈ D.omHT σ) ∧ (D.omHT σ).FG ∧ ∀ y ∈ D.omHT σ, ∃ x : Fin N → A, ∃ y' ∈ D.omHT σ, y = D.q σ x + ((p : A) ^ m) • y' := by
  first | exact @GlobalTheory.CompanionTheory.Ar.HT.q_onto_eigenpart_mod_pow | exact GlobalTheory.CompanionTheory.Ar.HT.q_onto_eigenpart_mod_pow | (intros; apply GlobalTheory.CompanionTheory.Ar.HT.q_onto_eigenpart_mod_pow <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.HodgeTateChartNonUnitP
section
open Module NumberField GlobalTheory.CompanionTheory.Ar.HT TensorProduct

namespace GlobalTheory.CompanionTheory.Ar.HT

theorem chart_rank_add_conj : ∀ (A K : Type) [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsIntegrallyClosed A] [Field K] [Algebra A K] [IsFractionRing A K] [CharZero K] (E : Type) [Field E] [NumberField E] (c : E ≃+* E) (hc : ∀ x, c (c x) = x) (p R N : ℕ) [Fact p.Prime] (Ω : Type) [AddCommGroup Ω] [Module K Ω] [Module A Ω] [IsScalarTower A K Ω] (D : HTChart A K c p R N Ω) (κ : A) (σ : E →+* K) (d d' : A), ¬ IsUnit (p : A) → κ ∣ (p : A) ^ R → GeneratesDiff σ d → GeneratesDiff (σ.comp c.toRingHom) d' → Module.Projective A (D.omHT σ) → Module.Projective A (D.omHT (σ.comp c.toRingHom)) → D.HasTestPoints κ → Module.finrank A (D.omHT σ) + Module.finrank A (D.omHT (σ.comp c.toRingHom)) = N :=
  @PositivityTheory.HtPt.Gb.chart_rank

end GlobalTheory.CompanionTheory.Ar.HT
end

