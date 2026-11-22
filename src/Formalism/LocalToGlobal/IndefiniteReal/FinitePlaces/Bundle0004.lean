import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.Bundle0003
import Formalism.LocalRingCardinality.SpanPowerMembership.Adelic

-- bundled from Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.ActsLinOfSplitLin
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.IndefR.Datum

namespace Formalism.IndefR.Fin.LevelGroupLemmas

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

theorem mt_mul' (V : HSp D) (a b : GA D V) : Formalism.L2.Theta.mt V (a * b) = Formalism.L2.Theta.mt V a * Formalism.L2.Theta.mt V b := by
  simp [Formalism.L2.Theta.mt, map_mul, Units.val_mul]

theorem mt_one' (V : HSp D) : Formalism.L2.Theta.mt V (1 : GA D V) = 1 := by
  simp [Formalism.L2.Theta.mt, map_one, Units.val_one]

theorem actO_eq {S T : HSp D} (g : GA D S) (h : GA D T) (x : WO S T) :
    actO S T g h x = HMul.hMul (HMul.hMul (Formalism.L2.Theta.mt T h) x) (Formalism.L2.Theta.mt S g⁻¹) := rfl

theorem actO_actO {S T : HSp D} (g g' : GA D S) (h h' : GA D T) (x : WO S T) :
    actO S T g h (actO S T g' h' x) = actO S T (g * g') (h * h') x := by
  rw [actO_eq, actO_eq, actO_eq, _root_.mul_inv_rev, mt_mul', mt_mul']
  simp only [Matrix.mul_assoc]

theorem actO_one {S T : HSp D} (x : WO S T) : actO S T 1 1 x = x := by
  rw [actO_eq, inv_one, mt_one', mt_one', Matrix.one_mul, Matrix.mul_one]

theorem actO_add {S T : HSp D} (g : GA D S) (h : GA D T) (x y : WO S T) :
    actO S T g h (x + y) = actO S T g h x + actO S T g h y := by
  rw [actO_eq, actO_eq, actO_eq, Matrix.mul_add, Matrix.add_mul]

theorem actO_nsmul {S T : HSp D} (g : GA D S) (h : GA D T) (k : ℕ) (x : WO S T) :
    actO S T g h (k • x) = k • actO S T g h x := by
  induction k with
  | zero => rw [zero_nsmul, zero_nsmul, actO_eq, Matrix.mul_zero, Matrix.zero_mul]
  | succ k ih => rw [succ_nsmul, actO_add, ih, succ_nsmul]

theorem isHalf_mul_mul {e : AE D} {a b c : ℕ} (M : Matrix (Fin a) (Fin b) (AE D)) (x : Matrix (Fin b) (Fin c) (AE D))
    (N : Matrix (Fin c) (Fin c) (AE D)) (hx : IsHalf e x) : IsHalf e (M * x * N) := by
  intro i j
  simp only [Matrix.mul_apply, Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun k _ => ?_
  conv_rhs => rw [← hx k l]
  ring

theorem isHalf_actO {S T : HSp D} {e : AE D} (g : GA D S) (h : GA D T) (x : WO S T) :
    IsHalf e (actO S T g h x) ↔ IsHalf e x := by
  constructor
  · intro hx
    have : actO S T g⁻¹ h⁻¹ (actO S T g h x) = x := by
      rw [actO_actO, inv_mul_cancel, inv_mul_cancel, actO_one]
    rw [← this]
    exact isHalf_mul_mul _ _ _ hx
  · intro hx
    exact isHalf_mul_mul _ _ _ hx

def actPull {S T : HSp D} (p : GA D S × GA D T) (Φ : WO S T → ℂ) : WO S T → ℂ :=
  fun t => Φ (actO S T p.1⁻¹ p.2⁻¹ t)

theorem actPull_mul {S T : HSp D} (p q : GA D S × GA D T) (Φ : WO S T → ℂ) :
    actPull p (actPull q Φ) = actPull (p * q) Φ := by
  funext t
  simp only [actPull, actO_actO, Prod.fst_mul, Prod.snd_mul, _root_.mul_inv_rev]

def ActsLin {S T : HSp D} (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ))
    (Tm : (WO S T → ℂ) →ₗ[ℂ] (WO S T → ℂ)) (e : AE D) (Λ : AddSubgroup (WO S T)) (p : GA D S × GA D T) (c : ℂ) :
    Prop :=
  ∀ Φ, IsSBHalf e Λ Φ → om p (Tm Φ) = c • Tm (actPull p Φ)

theorem actsLin_one {S T : HSp D} {om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)}
    {Tm : (WO S T → ℂ) →ₗ[ℂ] (WO S T → ℂ)} {e : AE D} {Λ : AddSubgroup (WO S T)} : ActsLin om Tm e Λ 1 1 := by
  intro Φ _
  have : actPull (1 : GA D S × GA D T) Φ = Φ := by
    funext t; simp [actPull, actO_one]
  rw [this, map_one, one_smul]
  rfl

theorem sbHalf_actPull {S T : HSp D} {e : AE D} {Λ : AddSubgroup (WO S T)} (p : GA D S × GA D T)
    (hΛ : ∀ t, IsHalf e t → (actO S T p.1⁻¹ p.2⁻¹ t ∈ Λ ↔ t ∈ Λ)) {Φ : WO S T → ℂ} (hΦ : IsSBHalf e Λ Φ) :
    IsSBHalf e Λ (actPull p Φ) := by
  obtain ⟨hsupp, k, hk, hinv, hcpt⟩ := hΦ
  refine ⟨fun t ht => (isHalf_actO _ _ t).1 (hsupp _ ht), k, hk, fun u hu hue t => ?_, fun t ht => ?_⟩
  · simp only [actPull]
    rw [actO_add, actO_nsmul]
    exact hinv _ ((hΛ u hue).2 hu) ((isHalf_actO _ _ u).2 hue) _
  · have hth : IsHalf e t := (isHalf_actO _ _ t).1 (hsupp _ ht)
    have h1 := hcpt _ ht
    rw [← actO_nsmul] at h1
    have hkt : IsHalf e (k • t) := fun i j => by
      simp only [Matrix.smul_apply, nsmul_eq_mul]
      rw [mul_left_comm, hth i j]
    exact (hΛ _ hkt).1 h1

theorem actsLin_mul {S T : HSp D} {om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)}
    {Tm : (WO S T → ℂ) →ₗ[ℂ] (WO S T → ℂ)} {e : AE D} {Λ : AddSubgroup (WO S T)} {p q : GA D S × GA D T} {c d : ℂ}
    (hp : ActsLin om Tm e Λ p c) (hq : ActsLin om Tm e Λ q d)
    (hsb : ∀ Φ, IsSBHalf e Λ Φ → IsSBHalf e Λ (actPull q Φ)) : ActsLin om Tm e Λ (p * q) (c * d) := by
  intro Φ hΦ
  rw [map_mul, Module.End.mul_apply, hq Φ hΦ, LinearMap.map_smul, hp _ (hsb Φ hΦ), actPull_mul, smul_smul, mul_comm d c]

theorem actsLin_of_splitLin (hSL : SplitLin D) {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {χS χT : (AE D)ˣ →* Circle}
    {om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)} (hW : IsWeilDatumO ψ S T χS χT om)
    {ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)} {ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)}
    (hsS : IsSelfDualC S ΛS) (hsT : IsSelfDualC T ΛT) {P : Finset (Formalism.L2.DIV.Pl D.host.E)} {e : AE D}
    (he : IsIdemSum e P) {f₀ : WO S T → ℂ} (hf₀ : IsThetaFunO ψ S T f₀)
    (hfix : ∀ u ∈ latAll S T ΛS ΛT, (IsHalf e u ∨ IsHalf (cA D e) u) → heisO ψ S T u f₀ = f₀)
    {Tm : (WO S T → ℂ) →ₗ[ℂ] (WO S T → ℂ)}
    (hTm : IsPlaceModel ψ (symplO S T) (heisO ψ S T) e (latAll S T ΛS ΛT) 1 f₀ Tm)
    {e₁ : AE D} (hs : IsSplitIdem D e₁) (h1 : e₁ * e = e₁) {g : GA D S} {h : GA D T}
    (hg : SuppAt e₁ S g) (hh : SuppAt e₁ T h) {x y : (AE D)ˣ} (hx : IsDetAt e₁ S g x) (hy : IsDetAt e₁ T h y)
    (hlat : ∀ t : WO S T, IsHalf e t → (actO S T g h t ∈ latAll S T ΛS ΛT ↔ t ∈ latAll S T ΛS ΛT))
    (hn : ∃ (μ : Measure (WO S T)) (𝓕 : Set (WO S T)), IsCovolOne (ratL T S) μ 𝓕 ∧ nrm2 μ 𝓕 f₀ = 1) :
    ActsLin om Tm e (latAll S T ΛS ΛT) (g, h) (splitFacO χS χT x y : ℂ) := by
  obtain ⟨r, _, hact, hr1⟩ :=
    hSL ψ S T χS χT om hW ΛS ΛT hsS hsT P e he f₀ hf₀ hfix Tm hTm e₁ hs h1 g h hg hh x y hx hy
  have hr : r = 1 := hr1 hlat hn
  intro Φ hΦ
  rw [hact Φ hΦ, hr]
  simp only [Complex.ofReal_one, one_mul]
  rfl

theorem isPlaceModel_comp {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {χS χT : (AE D)ˣ →* Circle}
    {om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)} (hW : IsWeilDatumO ψ S T χS χT om) {e : AE D}
    {Λ : AddSubgroup (WO S T)} {c : ℂ} {f₀ : WO S T → ℂ} {Tm : (WO S T → ℂ) →ₗ[ℂ] (WO S T → ℂ)}
    (hTm : IsPlaceModel ψ (symplO S T) (heisO ψ S T) e Λ c f₀ Tm)
    (hth : ∀ Φ, IsSBHalf e Λ Φ → IsThetaFunO ψ S T (Tm Φ)) (p : GA D S × GA D T)
    (hfx : ∀ x : WO S T, (IsHalf e x ∨ IsHalf (cA D e) x) → actO S T p.1 p.2 x = x) (h0 : om p f₀ = f₀) :
    IsPlaceModel ψ (symplO S T) (heisO ψ S T) e Λ c f₀ ((om p).comp Tm) where
  trans Φ hΦ x hx := by
    rw [LinearMap.comp_apply, hTm.trans Φ hΦ x hx, LinearMap.comp_apply]
    have := hW.om_heis p.1 p.2 x (Tm Φ) (hth Φ hΦ)
    rw [hfx x (Or.inl hx)] at this
    exact this
  modul Φ hΦ y hy := by
    rw [LinearMap.comp_apply, hTm.modul Φ hΦ y hy, LinearMap.comp_apply]
    have := hW.om_heis p.1 p.2 y (Tm Φ) (hth Φ hΦ)
    rw [hfx y (Or.inr hy)] at this
    exact this
  vac := by rw [LinearMap.comp_apply, hTm.vac, h0]

theorem om_fix_of_thetaAt {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {χS χT : (AE D)ˣ →* Circle}
    {om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)} (hW : IsWeilDatumO ψ S T χS χT om) {e : AE D}
    {Λ : AddSubgroup (WO S T)} {c : ℂ} {f₀ Φ f : WO S T → ℂ}
    (hθ : IsThetaAt ψ (symplO S T) (heisO ψ S T) e Λ c f₀ Φ f)
    (hth : ∀ Tm, IsPlaceModel ψ (symplO S T) (heisO ψ S T) e Λ c f₀ Tm →
      ∀ Φ', IsSBHalf e Λ Φ' → IsThetaFunO ψ S T (Tm Φ')) (p : GA D S × GA D T)
    (hfx : ∀ x : WO S T, (IsHalf e x ∨ IsHalf (cA D e) x) → actO S T p.1 p.2 x = x) (h0 : om p f₀ = f₀) :
    om p f = f := by
  obtain ⟨⟨Tm, hTm⟩, hall⟩ := hθ
  have hf : f = Tm Φ := hall Tm hTm
  have h2 : f = ((om p).comp Tm) Φ := hall _ (isPlaceModel_comp hW hTm (hth Tm hTm) p hfx h0)
  rw [LinearMap.comp_apply, ← hf] at h2
  exact h2.symm

end Formalism.IndefR.Fin.LevelGroupLemmas

end
end

-- bundled from Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.IdemLoc
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta IsDedekindDomain NumberField Polynomial
open scoped TensorProduct

set_option synthInstance.maxHeartbeats 160000

namespace Formalism.IndefR.Fin

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Loc

variable {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))

theorem af_ext {x y : Af F} (h : ∀ w, evalV F w x = evalV F w y) : x = y := by
  first
    | exact RestrictedProduct.ext h
    | exact Subtype.ext (funext h)
    | (ext w
       exact h w)

open Classical in

def sglV (a : v.adicCompletion F) : Af F :=
  ⟨Pi.single v a, by
    refine Filter.eventually_cofinite.2 ((Set.finite_singleton v).subset ?_)
    intro w hw
    by_contra hne
    apply hw
    have : w ≠ v := hne
    rw [Pi.single_eq_of_ne this]
    exact zero_mem _⟩

theorem sglV_same (a : v.adicCompletion F) : evalV F v (sglV v a) = a := by
  classical
  first
    | exact Pi.single_eq_same (i := v) (x := a)
    | exact Pi.single_eq_same v a
    | simp [sglV, evalV]

theorem sglV_ne (a : v.adicCompletion F) {w : HeightOneSpectrum (𝓞 F)} (h : w ≠ v) : evalV F w (sglV v a) = 0 := by
  classical
  first
    | exact Pi.single_eq_of_ne h a
    | exact Pi.single_eq_of_ne (i := v) h a
    | simp [sglV, evalV, h]

theorem sglV_add (a b : v.adicCompletion F) : sglV v (a + b) = sglV v a + sglV v b := by
  refine af_ext fun w => ?_
  rw [map_add]
  by_cases h : w = v
  · subst h
    rw [sglV_same, sglV_same, sglV_same]
  · rw [sglV_ne _ _ h, sglV_ne _ _ h, sglV_ne _ _ h, add_zero]

theorem sglV_mul (a b : v.adicCompletion F) : sglV v (a * b) = sglV v a * sglV v b := by
  refine af_ext fun w => ?_
  rw [map_mul]
  by_cases h : w = v
  · subst h
    rw [sglV_same, sglV_same, sglV_same]
  · rw [sglV_ne _ _ h, sglV_ne _ _ h, sglV_ne _ _ h, mul_zero]

theorem sglV_zero : sglV v (0 : v.adicCompletion F) = 0 := by
  refine af_ext fun w => ?_
  rw [map_zero]
  by_cases h : w = v
  · subst h
    rw [sglV_same]
  · rw [sglV_ne _ _ h]

theorem sglV_smul (f : F) (a : v.adicCompletion F) :
    algebraMap F (Af F) f * sglV v a = sglV v (algebraMap F (v.adicCompletion F) f * a) := by
  refine af_ext fun w => ?_
  rw [map_mul, AlgHom.commutes]
  by_cases h : w = v
  · subst h
    rw [sglV_same, sglV_same] <;> rfl
  · rw [sglV_ne _ _ h, sglV_ne _ _ h, mul_zero]

theorem sglV_int {a : v.adicCompletion F} (ha : a ∈ v.adicCompletionIntegers F) : sglV v a ∈ intAf F := by
  first
    | (intro w
       by_cases h : w = v
       · subst h
         rw [sglV_same]
         exact ha
       · rw [sglV_ne _ _ h]
         exact zero_mem _)
    | (intro w
       by_cases h : w = v
       · subst h
         show evalV F w (sglV w a) ∈ _
         rw [sglV_same]
         exact ha
       · show evalV F w (sglV v a) ∈ _
         rw [sglV_ne _ _ h]
         exact zero_mem _)

def sA : v.adicCompletion F →ₙ+* AF F where
  toFun a := pairA F 0 (sglV v a)
  map_mul' a b := Prod.ext (by show (0 : Ainf F) = 0 * 0; rw [mul_zero]) (sglV_mul v a b)
  map_zero' := Prod.ext rfl (sglV_zero v)
  map_add' a b := Prod.ext (by show (0 : Ainf F) = 0 + 0; rw [add_zero]) (sglV_add v a b)

theorem sA_smul (f : F) (a : v.adicCompletion F) :
    algebraMap F (AF F) f * sA v a = sA v (algebraMap F (v.adicCompletion F) f * a) := by
  first
    | exact Prod.ext (mul_zero _) (sglV_smul v f a)
    | (refine Prod.ext ?_ ?_
       · show _ * (0 : Ainf F) = 0
         exact mul_zero _
       · exact sglV_smul v f a)

theorem sA_one_mul (a : AF F) : sA v 1 * a = sA v (evalV F v (sndA F a)) := by
  refine Prod.ext ?_ ?_
  · show (0 : Ainf F) * _ = 0
    exact zero_mul _
  · show sglV v 1 * _ = sglV v _
    refine af_ext fun w => ?_
    rw [map_mul]
    by_cases h : w = v
    · subst h
      rw [sglV_same, sglV_same, one_mul] <;> rfl
    · rw [sglV_ne _ _ h, sglV_ne _ _ h, zero_mul]

theorem mem_O_of_integral {y : v.adicCompletion F} (hy : IsIntegral ℤ y) : Valued.v y ≤ 1 := by
  first
    | (have hm := (Valuation.integer.integers (Valued.v : Valuation (v.adicCompletion F) _)).mem_of_integral
         (IsIntegral.tower_top hy)
       first
         | exact hm
         | (obtain ⟨o, rfl⟩ := hm
            exact o.2)
         | (rcases hm with ⟨o, ho⟩
            rw [← ho]
            exact o.2))
    | (have hm := Valuation.Integers.mem_of_integral (Valuation.integer.integers (Valued.v : Valuation (v.adicCompletion F) _))
         (IsIntegral.tower_top (A := (Valued.v : Valuation (v.adicCompletion F) _).integer) hy)
       first
         | exact hm
         | (obtain ⟨o, rfl⟩ := hm
            exact o.2))

theorem val_coe_lt_one_iff (f : 𝓞 F) :
    Valued.v (((f : F) : v.adicCompletion F)) < 1 ↔ f ∈ v.asIdeal := by
  have e : Valued.v (((f : F) : v.adicCompletion F)) = v.intValuation f := by
    first
      | (rw [IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
         exact IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap (v := v) (r := f))
      | simp [IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation', IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap]
  rw [e]
  first
    | exact IsDedekindDomain.HeightOneSpectrum.intValuation_lt_one_iff_mem v f
    | exact (IsDedekindDomain.HeightOneSpectrum.intValuation_lt_one_iff_dvd v f).trans Ideal.dvd_span_singleton
    | (rw [IsDedekindDomain.HeightOneSpectrum.intValuation_lt_one_iff_dvd, Ideal.dvd_span_singleton])

theorem val_coe_le_one (f : 𝓞 F) : Valued.v (((f : F) : v.adicCompletion F)) ≤ 1 := by
  first
    | exact mem_O_of_integral v ((NumberField.RingOfIntegers.isIntegral_coe f).map (algebraMap F (v.adicCompletion F)).toIntAlgHom)
    | (rw [IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation',
         ← IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap (v := v) (r := f) ▸ rfl]
       exact IsDedekindDomain.HeightOneSpectrum.intValuation_le_one v f)
    | (have e : Valued.v (((f : F) : v.adicCompletion F)) = v.intValuation f := by
         rw [IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
         exact IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap (v := v) (r := f)
       rw [e]
       exact IsDedekindDomain.HeightOneSpectrum.intValuation_le_one v f)

set_option maxHeartbeats 800000 in

theorem roots_exist (t N : 𝓞 F) (hN : N ∈ v.asIdeal) (ht : t ∉ v.asIdeal) :
    ∃ r₁ r₂ : v.adicCompletion F, r₁ + r₂ = ((t : F) : v.adicCompletion F) ∧ r₁ * r₂ = ((N : F) : v.adicCompletion F) ∧
      Valued.v r₁ < 1 ∧ Valued.v r₂ = 1 := by
  haveI : HenselianLocalRing (v.adicCompletionIntegers F) := inferInstance
  have hI : (Valued.v : Valuation (v.adicCompletion F) _).Integers (v.adicCompletionIntegers F) :=
    ⟨Subtype.val_injective, fun x => x.2, fun r hr => ⟨⟨r, hr⟩, rfl⟩⟩
  have ea : ∀ x : v.adicCompletionIntegers F, algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F) x = (x : v.adicCompletion F) := fun x => rfl
  have hnu : ∀ x : v.adicCompletionIntegers F, ¬ IsUnit x ↔ Valued.v (x : v.adicCompletion F) < 1 := by
    intro x
    have hle := hI.map_le_one x
    rw [ea] at hle
    rw [hI.isUnit_iff_valuation_eq_one, ea]
    exact ⟨fun h => lt_of_le_of_ne hle h, fun h => ne_of_lt h⟩
  have ht1 : Valued.v (((t : F) : v.adicCompletion F)) = 1 :=
    le_antisymm (val_coe_le_one v t) (not_lt.1 fun h => ht ((val_coe_lt_one_iff v t).1 h))
  have hN1 : Valued.v (((N : F) : v.adicCompletion F)) < 1 := (val_coe_lt_one_iff v N).2 hN
  obtain ⟨t', ht'⟩ : ∃ t' : v.adicCompletionIntegers F, (t' : v.adicCompletion F) = ((t : F) : v.adicCompletion F) := ⟨⟨_, val_coe_le_one v t⟩, rfl⟩
  obtain ⟨N', hN'⟩ : ∃ N' : v.adicCompletionIntegers F, (N' : v.adicCompletion F) = ((N : F) : v.adicCompletion F) := ⟨⟨_, val_coe_le_one v N⟩, rfl⟩
  have hmon : (Polynomial.X ^ 2 - Polynomial.C t' * Polynomial.X + Polynomial.C N').Monic := by
    first
      | monicity!
      | exact Polynomial.monic_of_natDegree_le_of_coeff_eq_one 2 (by compute_degree!) (by simp)
  have he0 : Polynomial.eval (0 : v.adicCompletionIntegers F) (Polynomial.X ^ 2 - Polynomial.C t' * Polynomial.X + Polynomial.C N') = N' := by simp
  have h0 : Polynomial.eval (0 : v.adicCompletionIntegers F) (Polynomial.X ^ 2 - Polynomial.C t' * Polynomial.X + Polynomial.C N') ∈ IsLocalRing.maximalIdeal (v.adicCompletionIntegers F) := by
    rw [he0, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, hnu, hN']
    exact hN1
  have hd0 : Polynomial.eval (0 : v.adicCompletionIntegers F) (Polynomial.derivative (Polynomial.X ^ 2 - Polynomial.C t' * Polynomial.X + Polynomial.C N')) = -t' := by simp
  have hu : IsUnit (Polynomial.eval (0 : v.adicCompletionIntegers F) (Polynomial.derivative (Polynomial.X ^ 2 - Polynomial.C t' * Polynomial.X + Polynomial.C N'))) := by
    rw [hd0]
    refine IsUnit.neg ?_
    rw [hI.isUnit_iff_valuation_eq_one, ea, ht']
    exact ht1
  obtain ⟨a, ha, ha0⟩ := HenselianLocalRing.is_henselian _ hmon 0 h0 hu
  have ha1 : Valued.v (a : v.adicCompletion F) < 1 := by
    have h4 := ha0
    rw [sub_zero, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, hnu] at h4
    exact h4
  have h2 : (a : v.adicCompletion F) ^ 2 - ((t : F) : v.adicCompletion F) * a + ((N : F) : v.adicCompletion F) = 0 := by
    have ha' : Polynomial.eval a (Polynomial.X ^ 2 - Polynomial.C t' * Polynomial.X + Polynomial.C N') = 0 := ha
    simp only [Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_mul,
      Polynomial.eval_X, Polynomial.eval_C] at ha'
    have h3 := congrArg (fun x : v.adicCompletionIntegers F => (x : v.adicCompletion F)) ha'
    push_cast at h3
    rw [ht', hN'] at h3
    exact h3
  refine ⟨(a : v.adicCompletion F), ((t : F) : v.adicCompletion F) - a, by ring, by linear_combination -h2, ha1, ?_⟩
  first
    | rw [Valuation.map_sub_eq_of_lt_left _ (by rw [ht1]; exact ha1), ht1]
    | rw [Valuation.map_sub_eq_of_lt_right _ (by rw [ht1]; exact ha1), ht1]

end Loc

end Formalism.IndefR.Fin

end
end

-- bundled from Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.PlaceDualASt
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.IndefR.Datum
open scoped TensorProduct ComplexOrder

namespace Formalism.IndefR.Fin

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def PlaceLatDualIi (D : D7) : Prop :=
  ∀ (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S T : HSp D)
    (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)),
    IsSelfDualC S ΛS → IsSelfDualC T ΛT →
    ∀ (P : Finset (Formalism.L2.DIV.Pl D.host.E)) (e : AE D), IsIdemSum e P →
      (∀ y : WO S T, IsHalf (cA D e) y →
        ((∀ x ∈ latAll S T ΛS ΛT, IsHalf e x → ψ (symplO S T x y) = 1) ↔ y ∈ latAll S T ΛS ΛT))

def PlaceLatDualIii (D : D7) : Prop :=
  ∀ (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S T : HSp D)
    (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)),
    IsSelfDualC S ΛS → IsSelfDualC T ΛT →
    ∀ (P : Finset (Formalism.L2.DIV.Pl D.host.E)) (e : AE D), IsIdemSum e P →
      (∀ x : WO S T, IsHalf e x →
        ((∀ y ∈ latAll S T ΛS ΛT, IsHalf (cA D e) y → ψ (symplO S T x y) = 1) ↔ x ∈ latAll S T ΛS ΛT))

end Formalism.IndefR.Fin

end
end

-- bundled from Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.PlaceDualBSt
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.IndefR.Datum
open scoped TensorProduct ComplexOrder

namespace Formalism.IndefR.Fin

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def PlaceLatDualIv (D : D7) : Prop :=
  ∀ (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S T : HSp D)
    (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)),
    IsSelfDualC S ΛS → IsSelfDualC T ΛT →
    ∀ (P : Finset (Formalism.L2.DIV.Pl D.host.E)) (e : AE D), IsIdemSum e P →
      ∀ k : ℕ, 0 < k → ∀ e₁ : AE D, (e₁ = e ∨ e₁ = cA D e) →
        ∃ R : Finset (WO S T), ∀ u ∈ latAll S T ΛS ΛT, IsHalf e₁ u →
          ∃ r ∈ R, ∃ v ∈ latAll S T ΛS ΛT, IsHalf e₁ v ∧ u = r + k • v

def PlaceLatDualV (D : D7) : Prop :=
  ∀ (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S T : HSp D)
    (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)),
    IsSelfDualC S ΛS → IsSelfDualC T ΛT →
    ∀ (P : Finset (Formalism.L2.DIV.Pl D.host.E)) (e : AE D), IsIdemSum e P →
      ∀ e₁ : AE D, (e₁ = e ∨ e₁ = cA D e) → ∀ x : WO S T, IsHalf e₁ x → ∃ k : ℕ, 0 < k ∧ k • x ∈ latAll S T ΛS ΛT

def PlaceLatDualVi (D : D7) : Prop :=
  ∀ (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S T : HSp D)
    (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)),
    IsSelfDualC S ΛS → IsSelfDualC T ΛT →
    ∀ e' : AE D, IsSplitIdem D e' → ∀ (g : GA D S) (h : GA D T), SuppAt e' S g → SuppAt e' T h →
      ∃ k : ℕ, 0 < k ∧ ∀ t ∈ latAll S T ΛS ΛT, k • actO S T g h t ∈ latAll S T ΛS ΛT

end Formalism.IndefR.Fin

end
end

