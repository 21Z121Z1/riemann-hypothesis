import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.PoitouTateNineTermTransgressionZeroApply
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.H2EquivOfTorsionCharacter
import Formalism.SharpRestriction.LevelLetterCocycles.BlochKatoPhases
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0251
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0250
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0001
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0001
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0194
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0246

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TwistedDualEvalBidualApply
section
noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal

namespace GlobalTheory.DualSide

section Anti

variable {R : Type*} [CommRing R] {G : Type*} [Group G] [TopologicalSpace G]
  {M : Type*} [AddCommGroup M] [Module R M] [TopologicalSpace M]
  [IsTopologicalAddGroup M] [ContinuousConstSMul R M]
  {M' : Type*} [AddCommGroup M'] [Module R M'] [TopologicalSpace M']
  [IsTopologicalAddGroup M'] [ContinuousConstSMul R M']
  {P : Type*} [AddCommGroup P] [Module R P] [TopologicalSpace P]
  [IsTopologicalAddGroup P] [ContinuousConstSMul R P]

theorem cupH11_anticomm (rho : Representation R G M) (rho' : Representation R G M')
    (rhoP : Representation R G P) (b : M →ₗ[R] M' →ₗ[R] P)
    (hb : Continuous fun p : M × M' => b p.1 p.2)
    (hbe : ∀ g x y, b (rho g x) (rho' g y) = rhoP g (b x y))
    (hb' : Continuous fun p : M' × M => b.flip p.1 p.2)
    (hbe' : ∀ g y x, b.flip (rho' g y) (rho g x) = rhoP g (b.flip y x))
    (h : ContAction rho) (h' : ContAction rho') (x : H1 rho) (y : H1 rho') :
    cupProductH1H1 rho' rho rhoP b.flip hb' hbe' h y x = -cupProductH1H1 rho rho' rhoP b hb hbe h' x y := by
  induction x using Submodule.Quotient.induction_on with | H x =>
  induction y using Submodule.Quotient.induction_on with | H y =>
  rw [eq_neg_iff_add_eq_zero]
  change Submodule.Quotient.mk (cupCocycleZ1Z1 rho' rho rhoP b.flip hb' hbe' h y x +
    cupCocycleZ1Z1 rho rho' rhoP b hb hbe h' x y) = 0
  rw [Submodule.Quotient.mk_eq_zero]
  refine (separated_dvr_second_cohomology_mem _ _).2 ⟨fun g => -b (x.1 g) (y.1 g), (hb.comp (x.2.1.prodMk y.2.1)).neg, ?_⟩
  funext p
  obtain ⟨g, k⟩ := p
  change _ = b (rho g (x.1 k)) (y.1 g) + b (x.1 g) (rho' g (y.1 k))
  simp only [d1_apply, map_neg, ← hbe, x.2.2 g k, y.2.2 g k, map_add, LinearMap.add_apply]
  abel

theorem mapH1_bijective (rho : Representation R G M) (rho' : Representation R G M')
    (u : M ≃ₗ[R] M') (hu : Continuous u.toLinearMap) (hu' : Continuous u.symm.toLinearMap)
    (he : ∀ g m, u.toLinearMap (rho g m) = rho' g (u.toLinearMap m)) :
    Function.Bijective (mapH1 rho rho' u.toLinearMap hu he) := by
  have he' : ∀ g m, u.symm.toLinearMap (rho' g m) = rho g (u.symm.toLinearMap m) := fun g m => by
    apply u.injective
    have := he g (u.symm m)
    simp only [LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply] at this ⊢
    exact this.symm
  refine Function.bijective_iff_has_inverse.2 ⟨mapH1 rho' rho u.symm.toLinearMap hu' he',
    fun x => ?_, fun x => ?_⟩
  · induction x using Submodule.Quotient.induction_on with
    | H z => exact congrArg Submodule.Quotient.mk (Subtype.ext (funext fun g => u.symm_apply_apply _))
  · induction x using Submodule.Quotient.induction_on with
    | H z => exact congrArg Submodule.Quotient.mk (Subtype.ext (funext fun g => u.apply_symm_apply _))

end Anti

section Dual

variable {R : Type*} [CommRing R] {Γ : Type*} [Group Γ] {M : Type*} [AddCommGroup M] [Module R M]

theorem finite_TDual [Finite R] [Finite M] : Finite (TDual R M) :=
  Finite.of_injective _ (DFunLike.coe_injective (F := TDual R M))

def evalBidual : M →ₗ[R] TDual R (TDual R M) := evalPair

@[simp] theorem twistedDual_evalBidual_apply (m : M) (φ : TDual R M) :
    (evalBidual m : TDual R (TDual R M)) φ = φ m := rfl

theorem evalBidual_equiv (χ : Γ →* Rˣ) (rho : Representation R Γ M) (g : Γ) (m : M) :
    evalBidual (rho g m) = twDual χ (twDual χ rho) g (evalBidual m) := by
  ext φ
  simp only [twistedDual_evalBidual_apply, twDual_apply, inv_inv, map_inv]
  rw [← mul_assoc, Units.mul_inv, one_mul]

variable [TopologicalSpace R] [DiscreteTopology R] [TopologicalSpace M] [DiscreteTopology M]

theorem contAction_twDual [TopologicalSpace Γ] [ContinuousInv Γ] [Finite M] {χ : Γ →* Rˣ}
    {rho : Representation R Γ M} (hχ : ContAction (charRep χ)) (h : ContAction rho) :
    ContAction (twDual χ rho) := by
  have h1 : Continuous fun (p : Γ × TDual R M) (m : M) => twDual χ rho p.1 p.2 m :=
    continuous_pi fun m => hχ.comp (continuous_fst.prodMk
      ((continuous_of_discreteTopology (f := fun q : TDual R M × M => q.1 q.2)).comp
        (continuous_snd.prodMk (h.comp (continuous_fst.inv.prodMk continuous_const)))))
  exact (IsLocallyConstant.desc _ (fun (φ : TDual R M) (m : M) => φ m)
    ((IsLocallyConstant.iff_continuous _).2 h1) DFunLike.coe_injective).continuous

variable {D : Type*} [Group D] [TopologicalSpace D]

def evalH1 (χ : D →* Rˣ) (rho : Representation R D M) : H1 rho →ₗ[R] H1 (twDual χ (twDual χ rho)) :=
  mapH1 rho _ evalBidual continuous_of_discreteTopology (evalBidual_equiv χ rho)

theorem cup11_res_evalH1 [TopologicalSpace Γ] (χ : Γ →* Rˣ) (rho : Representation R Γ M)
    (φ : D →* Γ) (hφ : Continuous φ) (h : ContAction (rho.comp φ))
    (h' : ContAction ((twDual χ rho).comp φ)) (x : H1 rho) (y : H1 ((twDual χ rho).comp φ)) :
    cupH1H1TwistedDual χ (twDual χ rho) φ h' (resH1 (twDual χ (twDual χ rho)) φ hφ (evalH1 χ rho x)) y =
      -cupH1H1TwistedDual χ rho φ h y (resH1 rho φ hφ x) := by
  have e := cupH11_anticomm ((twDual χ rho).comp φ) (rho.comp φ) ((charRep χ).comp φ) evalPair.flip
    continuous_of_discreteTopology (fun g y x => evalPair_equiv χ rho (φ g) x y)
    continuous_of_discreteTopology (fun g x y => evalPair_equiv χ rho (φ g) x y) h' h y
    (resH1 rho φ hφ x)
  refine Eq.trans ?_ e
  induction x using Submodule.Quotient.induction_on with | H x =>
  induction y using Submodule.Quotient.induction_on with | H y =>
  rfl

end Dual

theorem evalH1_bijective {n : ℕ} [NeZero n] {Γ : Type*} [Group Γ] [TopologicalSpace Γ] {M : Type}
    [AddCommGroup M] [Module (ZMod n) M] [Finite M] [TopologicalSpace M] [DiscreteTopology M]
    (χ : Γ →* (ZMod n)ˣ) (rho : Representation (ZMod n) Γ M) :
    Function.Bijective (evalH1 χ rho) :=
  mapH1_bijective rho _ (LinearEquiv.ofBijective (evalBidual (R := ZMod n) (M := M))
    (GlobalTheory.TateTop.eval_bijective (n := n) (M := M))) continuous_of_discreteTopology
    continuous_of_discreteTopology (evalBidual_equiv χ rho)

section Global

open GlobalTheory.Published GlobalTheory.Published.PoitouTate

variable {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω]
  {l : ℕ} [Fact l.Prime] {r : ℕ} {S : Finset (HeightOneSpectrum (𝓞 F))}
  {Av : S → ValuationSubring Ω}
  {μ : GS Ω (S : Set (HeightOneSpectrum (𝓞 F))) →* (ZMod (l ^ r))ˣ}
  {j : ∀ v : S, H2 ((charRep μ).comp (locFam S Av v)) →ₗ[ZMod (l ^ r)] ZMod (l ^ r)}
  {M : Type} [AddCommGroup M] [Module (ZMod (l ^ r)) M] [Finite M] [TopologicalSpace M]
  [DiscreteTopology M]
  {ρ : Representation (ZMod (l ^ r)) (GS Ω (S : Set (HeightOneSpectrum (𝓞 F)))) M}

omit [TopologicalSpace M] [DiscreteTopology M] in
theorem finite_TDual_pow : Finite (TDual (ZMod (l ^ r)) M) :=
  haveI : NeZero (l ^ r) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
  finite_TDual

theorem mem_range_loc1_twDual_iff (hρ : ContAction ρ) {hρ' : ContAction (twDual μ ρ)}
    (h : NineTermExact S Av μ j (twDual μ ρ) hρ')
    (y : ∀ v : S, H1 ((twDual μ ρ).comp (locFam S Av v))) :
    y ∈ LinearMap.range (loc1 S Av (twDual μ ρ)) ↔ ∀ x : H1 ρ,
      ∑ v : S, j v (cupH1H1TwistedDual μ ρ (locFam S Av v) (hρ.comp' (continuous_locFam S Av v)) (y v)
        (resH1 ρ (locFam S Av v) (continuous_locFam S Av v) x)) = 0 := by
  have : NeZero (l ^ r) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
  rw [h.mem_range_localization_H1_iff, (evalH1_bijective μ ρ).2.forall]
  refine forall_congr' fun x => ?_
  simp only [cup11_res_evalH1 μ ρ _ _ (hρ.comp' (continuous_locFam S Av _)), map_neg,
    Finset.sum_neg_distrib, neg_eq_zero]

end Global

open GlobalTheory.Published GlobalTheory.Published.PoitouTate in

theorem exact_annihilators (h : PoitouTateTotallyComplex)
    (F Ω : Type) [Field F] [NumberField F] [IsTotallyComplex F] [Field Ω] [Algebra F Ω]
    [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (r : ℕ) (hr : 0 < r) (ζ : Ω)
    (hζ : IsPrimitiveRoot ζ (l ^ r)) :
    ∃ inv : InvFam F Ω l r, IsLocalInvariants ζ inv ∧
    ∀ (S : Finset (HeightOneSpectrum (𝓞 F))), ContainsAbove S l →
    ∀ (Av : S → ValuationSubring Ω), (∀ v, IsPlaceOver (Av v) v.1) →
    ∀ (μ : GS Ω (S : Set (HeightOneSpectrum (𝓞 F))) →* (ZMod (l ^ r))ˣ)
      (hμ : μ.comp (toGS Ω _) = cycMod F Ω l r),
    ∀ (M : Type) [AddCommGroup M] [Module (ZMod (l ^ r)) M] [Finite M] [TopologicalSpace M]
      [DiscreteTopology M]
      (ρ : Representation (ZMod (l ^ r)) (GS Ω (S : Set (HeightOneSpectrum (𝓞 F)))) M)
      (hρ : ContAction ρ),
      (∀ x : ∀ v : S, H1 (ρ.comp (locFam S Av v)),
        x ∈ LinearMap.range (loc1 S Av ρ) ↔ ∀ y : H1 (twDual μ ρ),
          ∑ v : S, invAt S Av μ hμ inv v (cupH1H1TwistedDual μ ρ (locFam S Av v)
            (hρ.comp' (continuous_locFam S Av v))
            (resH1 (twDual μ ρ) (locFam S Av v) (continuous_locFam S Av v) y) (x v)) = 0) ∧
      (∀ y : ∀ v : S, H1 ((twDual μ ρ).comp (locFam S Av v)),
        y ∈ LinearMap.range (loc1 S Av (twDual μ ρ)) ↔ ∀ x : H1 ρ,
          ∑ v : S, invAt S Av μ hμ inv v (cupH1H1TwistedDual μ ρ (locFam S Av v)
            (hρ.comp' (continuous_locFam S Av v)) (y v)
            (resH1 ρ (locFam S Av v) (continuous_locFam S Av v) x)) = 0) := by
  obtain ⟨inv, hinv, h⟩ := h F Ω l r hr ζ hζ
  refine ⟨inv, hinv, fun S hS Av hA μ hμ M _ _ _ _ _ ρ hρ => ⟨?_, ?_⟩⟩
  · exact (h S hS Av hA μ hμ M ρ hρ).1.mem_range_localization_H1_iff
  · have := finite_TDual_pow (l := l) (r := r) (M := M)
    exact mem_range_loc1_twDual_iff hρ (h S hS Av hA μ hμ _ (twDual μ ρ)
      (contAction_twDual (contAction_charRep hμ) hρ)).1

end GlobalTheory.DualSide
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ValuationPolynomialAtRootOfUnitySubOne
section
open IsDiscreteValuationRing

namespace GlobalTheory.PolyCycloValue

theorem card_double_min (S : Set ℕ) (a : ℕ → ℕ) (q : ℕ → ℝ) (w : ℕ) (hw : w ∈ S)
    (hq : ∀ k, 1 ≤ k → 0 < q k) (hqa : ∀ k k', 1 ≤ k → k < k' → q k' < q k) :
    ∃ BB : Finset ℕ, BB.card ≤ w + a w ∧ ∀ k, 1 ≤ k → k ∉ BB → ∀ i ∈ S, ∀ j ∈ S,
      (∀ m ∈ S, (a i : ℝ) + i * q k ≤ a m + m * q k) →
      (∀ m ∈ S, (a j : ℝ) + j * q k ≤ a m + m * q k) → i = j := by
  classical
  let M : ℕ → ℕ → Prop := fun k i => i ∈ S ∧ ∀ m ∈ S, (a i : ℝ) + i * q k ≤ a m + m * q k
  let B : Set ℕ := {k | 1 ≤ k ∧ ∃ i j, i < j ∧ M k i ∧ M k j}
  have hch : ∀ k, ∃ i j, k ∈ B → i < j ∧ M k i ∧ M k j := by
    intro k
    by_cases hk : k ∈ B
    · obtain ⟨-, i, j, h⟩ := hk
      exact ⟨i, j, fun _ => h⟩
    · exact ⟨0, 0, fun h => absurd h hk⟩
  choose I J hIJ using hch

  have hA : ∀ k, 1 ≤ k → ∀ i m, M k i → m ∈ S → m ≤ i → a i ≤ a m := by
    intro k hk i m hi hm hmi
    have h1 := hi.2 m hm
    have h2 : (m : ℝ) * q k ≤ i * q k :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast hmi) (hq k hk).le
    have : (a i : ℝ) ≤ a m := by linarith
    exact_mod_cast this
  have hA' : ∀ k, 1 ≤ k → ∀ i m, M k i → m ∈ S → m < i → a i < a m := by
    intro k hk i m hi hm hmi
    have h1 := hi.2 m hm
    have h2 : (m : ℝ) * q k < i * q k :=
      mul_lt_mul_of_pos_right (by exact_mod_cast hmi) (hq k hk)
    have : (a i : ℝ) < a m := by linarith
    exact_mod_cast this
  have hB : ∀ k k', 1 ≤ k → k < k' → ∀ m m', M k m → M k' m' → m ≤ m' := by
    intro k k' hk hkk m m' hm hm'
    by_contra hlt
    have hlt' : (m' : ℝ) < m := by exact_mod_cast (not_le.mp hlt)
    have h1 := hm.2 m' hm'.1
    have h2 := hm'.2 m hm.1
    have h3 := hqa k k' hk hkk
    nlinarith [mul_pos (sub_pos.mpr hlt') (sub_pos.mpr h3)]
  let φ : ℕ → ℕ := fun k => if I k < w then I k else w + a (J k)
  have hmaps : Set.MapsTo φ B (Finset.range (w + a w) : Set ℕ) := by
    intro k hk
    obtain ⟨hlt, hi, hj⟩ := hIJ k hk
    simp only [Finset.coe_range, Set.mem_Iio, φ]
    split_ifs with h
    · omega
    · have := hA' k hk.1 (J k) w hj hw (by omega)
      omega
  have hne : ∀ k ∈ B, ∀ k' ∈ B, k < k' → φ k ≠ φ k' := by
    intro k hk k' hk' hkk
    obtain ⟨hlt, hi, hj⟩ := hIJ k hk
    obtain ⟨hlt', hi', hj'⟩ := hIJ k' hk'
    have h1 := hB k k' hk.1 hkk _ _ hj hi'
    have h2 := hA' k' hk'.1 (J k') (J k) hj' hj.1 (by omega)
    simp only [φ]
    split_ifs <;> omega
  have hinj : Set.InjOn φ B := by
    intro k hk k' hk' h
    rcases lt_trichotomy k k' with h1 | h1 | h1
    · exact absurd h (hne k hk k' hk' h1)
    · exact h1
    · exact absurd h.symm (hne k' hk' k hk h1)
  have hfin : B.Finite := Set.Finite.of_injOn hmaps hinj (Finset.finite_toSet _)
  refine ⟨hfin.toFinset, ?_, ?_⟩
  · have := Finset.card_le_card_of_injOn (s := hfin.toFinset) (t := Finset.range (w + a w)) φ
      (by simpa using hmaps) (by simpa using hinj)
    simpa using this
  · intro k hk hkB i hi j hj hmi hmj
    rw [Set.Finite.mem_toFinset] at hkB
    by_contra hij
    rcases lt_or_gt_of_ne hij with h | h
    · exact hkB ⟨hk, i, j, h, ⟨hi, hmi⟩, ⟨hj, hmj⟩⟩
    · exact hkB ⟨hk, j, i, h, ⟨hj, hmj⟩, ⟨hi, hmi⟩⟩

section Val

variable {R : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]

theorem addVal_ne_top {x : R} (hx : x ≠ 0) : addVal R x ≠ ⊤ := by
  rwa [Ne, addVal_eq_top_iff]

theorem toNat_addVal_pos {x : R} (hx : x ≠ 0) (hu : ¬ IsUnit x) : 0 < (addVal R x).toNat := by
  have h1 := addVal_ne_top hx
  have h2 : addVal R x ≠ 0 := by rwa [Ne, addVal_eq_zero_iff]
  exact Nat.pos_of_ne_zero (by simp [ENat.toNat_eq_zero, h1, h2])

theorem nval_mul_pow (l : ℕ) {x y : R} (hx : x ≠ 0) (hy : y ≠ 0) (n : ℕ) :
    Formalism.MainNotions.BlochKatoReduction.Gen.nval R l (x * y ^ n) =
      Formalism.MainNotions.BlochKatoReduction.Gen.nval R l x + n * Formalism.MainNotions.BlochKatoReduction.Gen.nval R l y := by
  unfold Formalism.MainNotions.BlochKatoReduction.Gen.nval
  obtain ⟨s, hs⟩ := ENat.ne_top_iff_exists.mp (addVal_ne_top hx)
  obtain ⟨t, ht⟩ := ENat.ne_top_iff_exists.mp (addVal_ne_top hy)
  have : addVal R (x * y ^ n) = ((s + n * t : ℕ) : ℕ∞) := by
    rw [(addVal R).map_mul, (addVal R).map_pow, ← hs, ← ht]; simp
  rw [this, ← hs, ← ht]
  simp only [ENat.toNat_coe]
  push_cast
  ring

theorem addVal_lt_of_nval_lt (l : ℕ) {x y : R} (hx : x ≠ 0) (hy : y ≠ 0)
    (h : Formalism.MainNotions.BlochKatoReduction.Gen.nval R l x < Formalism.MainNotions.BlochKatoReduction.Gen.nval R l y) : addVal R x < addVal R y := by
  unfold Formalism.MainNotions.BlochKatoReduction.Gen.nval at h
  obtain ⟨s, hs⟩ := ENat.ne_top_iff_exists.mp (addVal_ne_top hx)
  obtain ⟨t, ht⟩ := ENat.ne_top_iff_exists.mp (addVal_ne_top hy)
  rw [← hs, ← ht] at h ⊢
  simp only [ENat.toNat_coe] at h
  have : (s : ℝ) < t := lt_of_not_ge fun hge =>
    absurd h (not_lt.mpr (div_le_div_of_nonneg_right hge (Nat.cast_nonneg _)))
  exact_mod_cast this

theorem sum_unique_min (l : ℕ) (S : Finset ℕ) (t : ℕ → R) (ht : ∀ i ∈ S, t i ≠ 0) (i₀ : ℕ)
    (hi₀ : i₀ ∈ S)
    (h : ∀ i ∈ S, i ≠ i₀ → Formalism.MainNotions.BlochKatoReduction.Gen.nval R l (t i₀) < Formalism.MainNotions.BlochKatoReduction.Gen.nval R l (t i)) :
    ∑ i ∈ S, t i ≠ 0 ∧
      Formalism.MainNotions.BlochKatoReduction.Gen.nval R l (∑ i ∈ S, t i) = Formalism.MainNotions.BlochKatoReduction.Gen.nval R l (t i₀) := by
  have h0 := addVal_ne_top (ht i₀ hi₀)
  have h1 : addVal R (t i₀) < addVal R (∑ i ∈ S.erase i₀, t i) :=
    (addVal R).map_lt_sum h0 fun i hi =>
      addVal_lt_of_nval_lt l (ht i₀ hi₀) (ht i (Finset.mem_of_mem_erase hi))
        (h i (Finset.mem_of_mem_erase hi) (Finset.ne_of_mem_erase hi))
  have h2 : addVal R (∑ i ∈ S, t i) = addVal R (t i₀) := by
    rw [← Finset.add_sum_erase S t hi₀]
    exact (addVal R).map_add_eq_of_lt_left h1
  refine ⟨fun hz => h0 ?_, ?_⟩
  · rw [← h2, hz]; simp
  · unfold Formalism.MainNotions.BlochKatoReduction.Gen.nval; rw [h2]

end Val

theorem value_at_root_sub_one : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (l : ℕ), l.Prime → (l : O) ≠ 0 → ¬ IsUnit (l : O) → ∀ (h : Polynomial O) (w : ℕ), h.coeff w ≠ 0 → ∃ (BB : Finset ℕ) (c : ℕ → ℝ), BB.card ≤ w + (IsDiscreteValuationRing.addVal O (h.coeff w)).toNat ∧ ∀ k, 1 ≤ k → k ∉ BB → c k ≤ Formalism.MainNotions.BlochKatoReduction.Gen.nval O l (h.coeff w) + w / (Nat.totient (l ^ k) : ℝ) ∧ ∀ (O' : Type) [CommRing O'] [IsDomain O'] [IsDiscreteValuationRing O'] [Algebra O O'] [IsLocalHom (algebraMap O O')], Function.Injective (algebraMap O O') → ∀ ζ : O', IsPrimitiveRoot ζ (l ^ k) → Polynomial.aeval (ζ - 1) h ≠ 0 ∧ Formalism.MainNotions.BlochKatoReduction.Gen.nval O' l (Polynomial.aeval (ζ - 1) h) = c k := by
  intro O _ _ _ l hl hl0 hlu h w hw
  set e : ℝ := ((addVal O (l : O)).toNat : ℝ) with he
  have hepos : 0 < e := by rw [he]; exact_mod_cast toNat_addVal_pos hl0 hlu
  have hphi : ∀ k, (0 : ℝ) < (Nat.totient (l ^ k) : ℝ) := fun k => by
    exact_mod_cast Nat.totient_pos.mpr (pow_pos hl.pos k)
  let a : ℕ → ℕ := fun i => (addVal O (h.coeff i)).toNat
  let q : ℕ → ℝ := fun k => e / (Nat.totient (l ^ k) : ℝ)
  have hwS : w ∈ h.support := Polynomial.mem_support_iff.mpr hw
  obtain ⟨BB, hcard, hBB⟩ := card_double_min (h.support : Set ℕ) a q w hwS
    (fun k _ => div_pos hepos (hphi k)) (by
      intro k k' hk hkk
      refine div_lt_div_of_pos_left hepos (hphi k) ?_
      rw [Nat.totient_prime_pow hl (by omega), Nat.totient_prime_pow hl (by omega)]
      have h1 : l ^ (k - 1) < l ^ (k' - 1) := Nat.pow_lt_pow_right hl.one_lt (by omega)
      have h2 : 0 < l - 1 := by have := hl.one_lt; omega
      exact_mod_cast Nat.mul_lt_mul_of_pos_right h1 h2)
  have hmin : ∀ k, ∃ i ∈ h.support, ∀ m ∈ h.support, (a i : ℝ) + i * q k ≤ a m + m * q k :=
    fun k => Finset.exists_min_image h.support (fun i => (a i : ℝ) + i * q k) ⟨w, hwS⟩
  choose I hIS hI using hmin
  have hform : ∀ k i : ℕ, Formalism.MainNotions.BlochKatoReduction.Gen.nval O l (h.coeff i) + i / (Nat.totient (l ^ k) : ℝ)
      = ((a i : ℝ) + i * q k) / e := by
    intro k i
    have := hphi k
    simp only [Formalism.MainNotions.BlochKatoReduction.Gen.nval, a, q, ← he]
    field_simp
  refine ⟨BB, fun k => ((a (I k) : ℝ) + I k * q k) / e, hcard, fun k hk hkB => ⟨?_, ?_⟩⟩
  · rw [hform]
    exact div_le_div_of_nonneg_right (hI k w hwS) hepos.le
  · intro O' _ _ _ _ _ hinj ζ hζ
    have hl0' : (l : O') ≠ 0 := by
      rw [← map_natCast (algebraMap O O')]
      exact fun h0 => hl0 (hinj (by rw [h0, map_zero]))
    have hlu' : ¬ IsUnit (l : O') := by
      rw [← map_natCast (algebraMap O O')]
      exact fun h0 => hlu (IsLocalHom.map_nonunit _ h0)
    obtain ⟨hz, hv⟩ := GlobalTheory.T.normalizedValuation_primitiveRoot_prime_pow_sub_one O' l k hl hk hl0' hlu' ζ hζ
    have hc : ∀ i ∈ h.support, algebraMap O O' (h.coeff i) ≠ 0 := fun i hi h0 =>
      Polynomial.mem_support_iff.mp hi (hinj (by rw [h0, map_zero]))
    have hval : ∀ i ∈ h.support,
        Formalism.MainNotions.BlochKatoReduction.Gen.nval O' l (algebraMap O O' (h.coeff i) * (ζ - 1) ^ i)
          = ((a i : ℝ) + i * q k) / e := by
      intro i hi
      rw [nval_mul_pow l (hc i hi) hz, hv, GlobalTheory.T.normalizedValuation_algebraMap_eq O O' hinj, ← hform, mul_one_div]
    have key := sum_unique_min l h.support
      (fun i => algebraMap O O' (h.coeff i) * (ζ - 1) ^ i)
      (fun i hi => mul_ne_zero (hc i hi) (pow_ne_zero _ hz)) (I k) (hIS k) (by
        intro i hi hne
        rw [hval i hi, hval _ (hIS k)]
        refine div_lt_div_of_pos_right ?_ hepos
        refine lt_of_le_of_ne (hI k i hi) fun heq => hne ?_
        exact hBB k hk hkB i hi (I k) (hIS k) (fun m hm => heq ▸ hI k m hm) (hI k))
    rw [hval _ (hIS k)] at key
    rw [Polynomial.aeval_def, Polynomial.eval₂_eq_sum, Polynomial.sum_def]
    exact key

end GlobalTheory.PolyCycloValue
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ZlSpanImageContinuousRepFinite
section
open Formalism.MainNotions.N GlobalTheory.Cong GlobalTheory.PsChar

namespace GlobalTheory

theorem zl_span_image_finite : ∀ (l : ℕ) [Fact l.Prime] (Γ : Type) [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ] (a : ℕ) (r : Γ →* GL (Fin a) (PadicAlgCl l)), Continuous r → ∃ t : Finset Γ, ∀ f : Γ →₀ ℤ_[l], ∃ f' : Γ →₀ ℤ_[l], f'.support ⊆ t ∧ (f.sum fun h c => ((algebraMap ℚ_[l] (PadicAlgCl l)) (c : ℚ_[l])) • ((r h : GL (Fin a) (PadicAlgCl l)) : Matrix (Fin a) (Fin a) (PadicAlgCl l))) = (f'.sum fun h c => ((algebraMap ℚ_[l] (PadicAlgCl l)) (c : ℚ_[l])) • ((r h : GL (Fin a) (PadicAlgCl l)) : Matrix (Fin a) (Fin a) (PadicAlgCl l))) := by
  intro l _ Γ _ _ _ _ a r hr
  classical
  obtain ⟨L, hLfin, hL⟩ := GlobalTheory.T.exists_finiteExtension_entries_of_compact_rep l Γ a r hr
  let ρ : Γ → Matrix (Fin a) (Fin a) (PadicAlgCl l) := fun g => ((r g : GL (Fin a) (PadicAlgCl l)) : Matrix (Fin a) (Fin a) (PadicAlgCl l))
  have hρ : Continuous ρ := Units.continuous_val.comp hr
  let e : Matrix (Fin a) (Fin a) L →ₗ[ℚ_[l]] Matrix (Fin a) (Fin a) (PadicAlgCl l) :=
    LinearMap.mapMatrix L.val.toLinearMap
  let V := LinearMap.range e
  haveI : FiniteDimensional ℚ_[l] V := LinearMap.finiteDimensional_range e
  have hρV : ∀ g, ρ g ∈ V := fun g => ⟨fun i j => ⟨ρ g i j, hL g i j⟩, by ext i j; rfl⟩
  let ρV : Γ → V := fun g => ⟨ρ g, hρV g⟩
  have hρVc : Continuous ρV := hρ.subtype_mk _
  let b := Module.finBasis ℚ_[l] V
  let φ : V →ₗ[ℚ_[l]] (Fin (Module.finrank ℚ_[l] V) → ℚ_[l]) := b.equivFun.toLinearMap
  have hφinj : Function.Injective φ := b.equivFun.injective
  have hφ : Continuous φ := LinearMap.continuous_of_finiteDimensional φ
  obtain ⟨C, hC⟩ := isCompact_univ.exists_bound_of_continuousOn (hφ.comp hρVc).continuousOn
  obtain ⟨c, hc⟩ := NormedField.exists_lt_norm ℚ_[l] C
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC 1 (Set.mem_univ _))
  have hcpos : 0 < ‖c‖ := lt_of_le_of_lt hC0 hc
  have hc0 : c ≠ 0 := norm_pos_iff.mp hcpos
  have hbd : ∀ g i, ‖c⁻¹ * φ (ρV g) i‖ ≤ 1 := by
    intro g i
    rw [norm_mul, norm_inv]
    have h1 := (norm_le_pi_norm (φ (ρV g)) i).trans (hC g (Set.mem_univ _))
    rw [inv_mul_le_iff₀ hcpos]
    linarith
  let ψ : Γ → (Fin (Module.finrank ℚ_[l] V) → ℤ_[l]) := fun g i => ⟨c⁻¹ * φ (ρV g) i, hbd g i⟩
  obtain ⟨G, hG⟩ : (Submodule.span ℤ_[l] (Set.range ψ)).FG := IsNoetherian.noetherian _
  have hGT : ∀ x ∈ G, ∃ T : Finset (Fin (Module.finrank ℚ_[l] V) → ℤ_[l]),
      ↑T ⊆ Set.range ψ ∧ x ∈ Submodule.span ℤ_[l] (T : Set _) := fun x hx =>
    Submodule.mem_span_finite_of_mem_span (hG ▸ Submodule.subset_span hx)
  choose T hT1 hT2 using hGT
  let U := G.attach.biUnion (fun x => T x.1 x.2)
  have hU : ∀ y ∈ U, ∃ g, ψ g = y := by
    intro y hy
    obtain ⟨x, -, hx⟩ := Finset.mem_biUnion.mp hy
    exact hT1 x.1 x.2 hx
  let t : Finset Γ := U.image (fun y => if h : ∃ g, ψ g = y then h.choose else 1)
  refine ⟨t, ?_⟩
  have hspan : Submodule.span ℤ_[l] (Set.range ψ) ≤ Submodule.span ℤ_[l] (ψ '' (t : Set Γ)) := by
    rw [← hG, Submodule.span_le]
    intro x hx
    refine Submodule.span_mono ?_ (hT2 x hx)
    intro y hy
    have hyU : y ∈ U := Finset.mem_biUnion.mpr ⟨⟨x, hx⟩, Finset.mem_attach _ _, hy⟩
    have hex : ∃ g, ψ g = y := hU y hyU
    refine ⟨hex.choose, ?_, hex.choose_spec⟩
    simp only [t, Finset.coe_image, Set.mem_image, Finset.mem_coe]
    exact ⟨y, hyU, by rw [dif_pos hex]⟩

  let A : (Γ →₀ ℤ_[l]) → V := fun f => f.sum fun h c' => ((c' : ℚ_[l])) • ρV h
  have hSM : ∀ f : Γ →₀ ℤ_[l], (f.sum fun h c' => ((algebraMap ℚ_[l] (PadicAlgCl l)) (c' : ℚ_[l])) • ρ h) = ((A f : V) : Matrix (Fin a) (Fin a) (PadicAlgCl l)) := by
    intro f
    simp only [A, Finsupp.sum, Submodule.coe_sum, Submodule.coe_smul, algebraMap_smul]
    rfl
  have hLC : ∀ f : Γ →₀ ℤ_[l], ∀ i, ((Finsupp.linearCombination ℤ_[l] ψ f i : ℤ_[l]) : ℚ_[l]) = c⁻¹ * φ (A f) i := by
    intro f i
    have hcs : ∀ F : Γ → ℤ_[l], ((∑ x ∈ f.support, F x : ℤ_[l]) : ℚ_[l]) = ∑ x ∈ f.support, (F x : ℚ_[l]) :=
      fun F => map_sum PadicInt.Coe.ringHom F f.support
    rw [Finsupp.linearCombination_apply]
    unfold Finsupp.sum
    simp only [A]
    unfold Finsupp.sum
    rw [Finset.sum_apply, hcs, map_sum, Finset.sum_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun h _ => ?_
    rw [map_smul, Pi.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul, PadicInt.coe_mul]
    simp only [ψ]
    ring
  intro f
  have hx : Finsupp.linearCombination ℤ_[l] ψ f ∈ Submodule.span ℤ_[l] (ψ '' (t : Set Γ)) :=
    hspan (Finsupp.mem_span_range_iff_exists_finsupp.mpr ⟨f, rfl⟩)
  obtain ⟨f', hf'sup, hf'⟩ := (Finsupp.mem_span_image_iff_linearCombination ℤ_[l]).mp hx
  refine ⟨f', ?_, ?_⟩
  · rw [Finsupp.mem_supported] at hf'sup
    exact_mod_cast hf'sup
  · show (f.sum fun h c' => ((algebraMap ℚ_[l] (PadicAlgCl l)) (c' : ℚ_[l])) • ρ h) = (f'.sum fun h c' => ((algebraMap ℚ_[l] (PadicAlgCl l)) (c' : ℚ_[l])) • ρ h)
    rw [hSM, hSM]
    congr 1
    apply hφinj
    funext i
    have h1 := hLC f i
    have h2 := hLC f' i
    rw [hf'] at h2
    have : c⁻¹ * φ (A f) i = c⁻¹ * φ (A f') i := h1.symm.trans h2
    exact mul_left_cancel₀ (inv_ne_zero hc0) this

end GlobalTheory
end

