import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TateUnramifiedOfTorsionUnramified
import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1041
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1472
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1500
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1415
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1397
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1517
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1566
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0057
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0013
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1565
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1564
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1577
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0907
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0414
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0915
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1571

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatSurjectiveSpMapOfDvr
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem flat_surjective_spMap_of_dvr : ∀ (R K W K' : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K] [Algebra R K] [IsFractionRing R K] [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field K'] [Algebra W K'] [IsFractionRing W K'] [Algebra R W] [Algebra K K'] [Algebra R K'] [IsScalarTower R W K'] [IsScalarTower R K K'], (maximalIdeal R).map (algebraMap R W) = maximalIdeal W → Flat (spMap (algebraMap R W)) ∧ Surjective (spMap (algebraMap R W)) := by
  intro R K W K' _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ h
  have hinj : Function.Injective (algebraMap R W) := by
    have h1 : (algebraMap W K').comp (algebraMap R W) = (algebraMap K K').comp (algebraMap R K) := by
      rw [← IsScalarTower.algebraMap_eq, ← IsScalarTower.algebraMap_eq]
    have h2 : Function.Injective ((algebraMap K K').comp (algebraMap R K)) :=
      (algebraMap K K').injective.comp (IsFractionRing.injective R K)
    rw [← h1] at h2
    exact Function.Injective.of_comp h2
  have hfl : Module.Flat R W := by
    rw [IsDedekindDomain.flat_iff_torsion_eq_bot, eq_bot_iff]
    intro x hx
    obtain ⟨⟨a, ha⟩, hax⟩ := (Submodule.mem_torsion_iff x).1 hx
    have ha0 : a ≠ 0 := nonZeroDivisors.ne_zero ha
    change a • x = 0 at hax
    rw [Algebra.smul_def] at hax
    rcases mul_eq_zero.1 hax with h0 | h0
    · exact absurd (hinj (h0.trans (map_zero _).symm)) ha0
    · simp [h0]
  have hloc : IsLocalHom (algebraMap R W) := by
    refine ((IsLocalRing.local_hom_TFAE (algebraMap R W)).out 0 2).2 ?_
    rw [h]
  have hff : Module.FaithfullyFlat R W := Module.FaithfullyFlat.of_flat_of_isLocalHom
  have hrf : (algebraMap R W).FaithfullyFlat := RingHom.faithfullyFlat_algebraMap_iff.2 hff
  obtain ⟨h1, h2⟩ := (flat_and_surjective_SpecMap_iff (CommRingCat.ofHom (algebraMap R W))).2 hrf
  exact ⟨h1, h2⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockToSchrodingerMapExistsOfArchHeisenbergDeriva
section
noncomputable section

open scoped TensorProduct Matrix Classical GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift

namespace GlobalTheory.FockMapEx

theorem fockEx_of_derEx : DerEx → FockEx := by
  intro hDer F E _ _ _ _ _ σ α β κ _ _ _ _ _ P Q R S ψ τ JA JB d a b A C hCM hψ hFr
  obtain ⟨D, hD⟩ := hDer F E σ α β κ ψ JA JB d hψ
  have hDf : ∀ u, At (evI F) u → ∀ (f : SInf F κ) x, D u f x =
      fderiv ℝ f x (fun i => evI F ((d.e u).1 i)) - 2 * Real.pi * Complex.I *
        (Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (∑ i, x i * evI F ((d.e u).2 i)) : ℝ) * f x :=
    fun u hu f x => (hD u hu f).2 x
  obtain ⟨hadd, hsm, hcom⟩ := GlobalTheory.T.archHeisenbergDerivative_additive_commutator σ JA JB d D hDf
  have hex := fun c : InfinitePlace F → Matrix (Ix P Q) (Ix R S) ℂ => GlobalTheory.T.existsUnique_archimedeanMatrix_adeleExtension_of_components σ τ hCM (fun w => A w * c w * (C w)ᵀ)
  choose uOf huOf using fun c => (hex c).exists
  have huniq : ∀ c u, At (evI F) u → (∀ w, u.map (piInf (τ w)) = A w * c w * (C w)ᵀ) → u = uOf c :=
    fun c u hu hw => (hex c).unique ⟨hu, hw⟩ (huOf c)
  have hAt_add : ∀ u u' : Matrix α β (AE F E), At (evI F) u → At (evI F) u' → At (evI F) (u + u') :=
    fun u u' hu hu' z hz => by rw [smul_add, hu z hz, hu' z hz, add_zero]
  have hAt_smul : ∀ (r : ℝ) (u : Matrix α β (AE F E)), At (evI F) u → At (evI F) (realAd F r • u) :=
    fun r u hu z hz => by rw [smul_comm, hu z hz, smul_zero]
  let H : (InfinitePlace F → Matrix (Ix P Q) (Ix R S) ℂ) → Module.End ℂ (SInf F κ) :=
    fun c => (D (uOf c)).toLinearMap
  have hHadd : ∀ c c', H (c + c') = H c + H c' := by
    intro c c'
    have e : uOf (c + c') = uOf c + uOf c' := by
      symm
      refine huniq _ _ (hAt_add _ _ (huOf c).1 (huOf c').1) fun w => ?_
      rw [Matrix.map_add _ (map_add _), (huOf c).2 w, (huOf c').2 w]
      simp [Matrix.mul_add, Matrix.add_mul]
    ext1 f
    simp only [H, e, hadd _ _ (huOf c).1 (huOf c').1]
    rfl
  have hHsmul : ∀ (r : ℝ) c, H ((r : ℂ) • c) = (r : ℂ) • H c := by
    intro r c
    have e : uOf ((r : ℂ) • c) = realAd F r • uOf c := by
      symm
      refine huniq _ _ (hAt_smul r _ (huOf c).1) fun w => ?_
      rw [GlobalTheory.T.realScalarArchimedeanAdele_smul_matrix_realPlace σ τ hCM, (huOf c).2 w]
      simp [Matrix.mul_smul, Matrix.smul_mul]
    ext1 f
    simp only [H, e, hsm _ r (huOf c).1]
    rfl
  have hHcomm : ∀ c c', H c * H c' - H c' * H c =
      ((4 * Real.pi : ℂ) * Complex.I * ((∑ w, ∑ a, ∑ b, lineSign a b * c w a b * star (c' w a b)).im : ℂ)) • 1 := by
    intro c c'
    ext1 f
    have h1 := hcom _ _ (huOf c).1 (huOf c').1 f
    rw [GlobalTheory.T.archimedeanTrace_symplecticForm_orthonormalFrames σ τ JA JB a b A C hCM hFr _ _ c c' (huOf c).1 (huOf c').1 (huOf c).2 (huOf c').2] at h1
    simp only [H, LinearMap.sub_apply, Module.End.mul_apply, ContinuousLinearMap.coe_coe, LinearMap.smul_apply,
      Module.End.one_apply]
    rw [h1]
    congr 1
    push_cast
    ring
  obtain ⟨f₀, hf₀, hv⟩ := GlobalTheory.T.exists_fock_vacuum_gaussian_frames σ τ JA JB d a b A C D hCM hFr hDf
  have hHvac : ∀ w a b, H (Pi.single w (Matrix.single a b 1)) f₀ +
      (lineSign a b * Complex.I) • H (Pi.single w (Matrix.single a b Complex.I)) f₀ = 0 := fun w a b =>
    hv w a b _ _ (huOf _).1 (huOf _).1 (huOf _).2 (huOf _).2
  obtain ⟨Φ, hinj, hint⟩ := GlobalTheory.T.exists_fockMap_of_canonicalCommutationRelations H hHadd hHsmul hHcomm f₀ hf₀ hHvac
  refine ⟨Φ, hinj, fun u hu c hc T => ?_⟩
  rw [hint, huniq c u hu hc]
  exact (hD _ (huOf c).1 (Φ T)).1

end GlobalTheory.FockMapEx
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FreeActionFramedPointsOfUnipotentModTwoPrimes
section
open CategoryTheory NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.Pj GlobalTheory.DualWeyl GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.DefPt ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open scoped Matrix Classical
open AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.FreeLev

@[instance_reducible] def ptModule {E : Type} [Field E] [NumberField E] (P : ReciprocityTheory.ChartRestriction.G.Out.PolAV (Sp ℂ)) (act : OAct (𝓞 E) P.A) :
    letI := P.isAb.comm
    Module (𝓞 E) (Additive (𝟙_ (Over (Sp ℂ)) ⟶ P.A)) :=
  letI := P.isAb.comm
  have h0 : act.act 0 = 1 := by
    have h := act.add 0 0
    rw [add_zero] at h
    exact (mul_eq_left.1 h.symm)
  { smul := fun c q => Additive.ofMul (q.toMul ≫ act.act c)
    one_smul := fun q => by
      show Additive.ofMul (q.toMul ≫ act.act 1) = q
      rw [act.one, Category.comp_id]; rfl
    mul_smul := fun a b q => by
      show Additive.ofMul (q.toMul ≫ act.act (a * b)) = Additive.ofMul ((q.toMul ≫ act.act b) ≫ act.act a)
      rw [mul_comm, act.mul, Category.assoc]
    smul_zero := fun c => by
      haveI := act.hom c
      show Additive.ofMul ((1 : 𝟙_ (Over (Sp ℂ)) ⟶ P.A) ≫ act.act c) = Additive.ofMul 1
      rw [MonObj.one_comp]
    smul_add := fun c q q' => by
      haveI := act.hom c
      show Additive.ofMul ((q.toMul * q'.toMul) ≫ act.act c) = Additive.ofMul (q.toMul ≫ act.act c * q'.toMul ≫ act.act c)
      rw [MonObj.mul_comp]
    add_smul := fun a b q => by
      show Additive.ofMul (q.toMul ≫ act.act (a + b)) = Additive.ofMul (q.toMul ≫ act.act a * q.toMul ≫ act.act b)
      rw [act.add, MonObj.comp_mul]
    zero_smul := fun q => by
      show Additive.ofMul (q.toMul ≫ act.act 0) = Additive.ofMul 1
      rw [h0, MonObj.comp_one] }

set_option maxHeartbeats 800000 in

theorem free_of_unip : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (G : Type) [Group G] (h : G → (Dw.La →ₗ[𝓞 E] Dw.La)) (m g₁ g₂ : ℕ) (I₁ I₂ : Ideal (𝓞 E)), 1 ≤ Dw.p + Dw.q → g₁.Prime → g₂.Prime → g₁ ≠ g₂ → I₁ ≠ ⊤ → I₂ ≠ ⊤ → (g₁ : 𝓞 E) ∈ I₁ → (g₂ : 𝓞 E) ∈ I₂ → l.Mb ≤ I₁ → l.Mb ≤ I₂ → (∀ g x, ((h g - 1) ^ m) x ∈ I₁ • (⊤ : Submodule (𝓞 E) Dw.La)) → (∀ g x, ((h g - 1) ^ m) x ∈ I₂ • (⊤ : Submodule (𝓞 E) Dw.La)) → (∀ g, (∀ x, h g x - x ∈ l.Mb • (⊤ : Submodule (𝓞 E) Dw.La)) → g = 1) → FreePt Xo c (fun g => (h g, (LinearMap.id : Dw.La →ₗ[𝓞 E] Dw.La))) := by
  intro E _ _ _ H Dw l Xo c G _ h m g₁ g₂ I₁ I₂ _ hg₁ hg₂ hne hI₁ hI₂ hm₁ hm₂ hMb₁ hMb₂ hu₁ hu₂ hfaith
  intro g k _ _ y y' hR hx
  obtain ⟨ρ, ν, -, hlev, hmove⟩ := hR
  have hfix : y.x ≫ ρ = y.x := hmove.1.symm.trans hx
  obtain ⟨x', hx'⟩ := GlobalTheory.T.exists_fixed_complexPoint_of_fixed_fieldPoint E H Dw l Xo k y.x ρ hfix
  obtain ⟨P, act, θ, N, ev, hθ, hN, hθN, hcomm, hadd, hlin, hker, honto, hrel⟩ :=
    GlobalTheory.T.exists_finiteOrder_fibreAut_at_levelMove_fixedPoint E H Dw l Xo x' ρ ν (h g) LinearMap.id hlev hx'
  have hM0 : 0 < l.M := by have := l.three_le; omega
  obtain ⟨Λ, _, _, F, ψ, hfin, htf, hFN, hψadd, hψlin, hψker, hψonto, hψF⟩ :=
    GlobalTheory.T.periodLattice_action_of_finiteOrder_automorphism E P act θ N l.M hθ hN hθN hcomm hM0
  letI := P.isAb.comm
  letI : Module (𝓞 E) (Additive (𝟙_ (Over (Sp ℂ)) ⟶ P.A)) := ptModule P act
  let evL : Dw.La →ₗ[𝓞 E] Additive (𝟙_ (Over (Sp ℂ)) ⟶ P.A) :=
    { toFun := fun a => Additive.ofMul (ev a)
      map_add' := fun a b => congrArg Additive.ofMul (hadd a b)
      map_smul' := fun c a => congrArg Additive.ofMul (hlin c a) }
  let ψL : Λ →ₗ[𝓞 E] Additive (𝟙_ (Over (Sp ℂ)) ⟶ P.A) :=
    { toFun := fun a => Additive.ofMul (ψ a)
      map_add' := fun a b => congrArg Additive.ofMul (hψadd a b)
      map_smul' := fun c a => congrArg Additive.ofMul (hψlin c a) }
  let θL : Additive (𝟙_ (Over (Sp ℂ)) ⟶ P.A) →ₗ[𝓞 E] Additive (𝟙_ (Over (Sp ℂ)) ⟶ P.A) :=
    { toFun := fun q => Additive.ofMul (q.toMul ≫ θ)
      map_add' := fun q q' => by
        show Additive.ofMul ((q.toMul * q'.toMul) ≫ θ) = Additive.ofMul (q.toMul ≫ θ * q'.toMul ≫ θ)
        rw [MonObj.mul_comp]
      map_smul' := fun c q => by
        show Additive.ofMul ((q.toMul ≫ act.act c) ≫ θ) = Additive.ofMul ((q.toMul ≫ θ) ≫ act.act c)
        rw [Category.assoc, Category.assoc, hcomm] }
  have hMmem : (l.M : 𝓞 E) ∈ l.Mb := by
    have h1 : (l.M : 𝓞 E) ∈ Ideal.span {(l.M : 𝓞 E)} := Ideal.subset_span rfl
    rw [← l.prod] at h1
    exact Ideal.mul_le_left h1
  refine hfaith g (GlobalTheory.T.sub_mem_smul_top_of_neat_level_alt E Dw.La Λ _ l.Mb l.M N m g₁ g₂ I₁ I₂ evL ψL θL F (h g) hfin htf hM0 hMmem
    (fun a => by
      show Additive.ofMul (ev a) = 0 ↔ _
      rw [← hker a]; exact ofMul_eq_zero)
    (fun q hq => by
      obtain ⟨a, ha⟩ := honto q.toMul (fun c hc => by
        have := hq c hc
        exact congrArg Additive.toMul this)
      exact ⟨a, congrArg Additive.ofMul ha⟩)
    (fun b => by
      show Additive.ofMul (ψ b) = 0 ↔ _
      rw [← hψker b]; exact ofMul_eq_zero)
    (fun q hq => by
      obtain ⟨b, hb⟩ := hψonto q.toMul (by
        have := congrArg Additive.toMul hq
        rwa [toMul_nsmul] at this)
      exact ⟨b, congrArg Additive.ofMul hb⟩)
    (fun b => congrArg Additive.ofMul (hψF b))
    (fun a => congrArg Additive.ofMul (hrel a))
    hN hFN hg₁ hg₂ hne hI₁ hI₂ hm₁ hm₂ hMb₁ hMb₂ (hu₁ g) (hu₂ g))

end GlobalTheory.FreeLev
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FreeFiniteFinrank
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.TateFree

open GlobalTheory.PDiv

variable {M : Type} [CommGroup M] {l : ℕ} [Fact l.Prime] {r : ℕ}

theorem lev_sum {I : Type} (s : Finset I) (f : I → Tate l M) (n : ℕ) :
    (∑ i ∈ s, f i).lev n = ∏ i ∈ s, (f i).lev n := by
  let h : Tate l M →+ Additive M :=
    { toFun := fun t => Additive.ofMul (t.lev n), map_zero' := rfl, map_add' := fun _ _ => rfl }
  have := congrArg Additive.toMul (map_sum h f s)
  rw [toMul_sum] at this
  exact this

theorem zpow_pow_comm' (a : M) (k : ℤ) (m : ℕ) : (a ^ k) ^ m = (a ^ m) ^ k := by
  rw [← zpow_natCast, ← zpow_natCast a m, ← zpow_mul, ← zpow_mul, mul_comm]

theorem exists_pow_eq (hc : ∀ n : ℕ, Nat.card {x : M // x ^ (l ^ n) = 1} = l ^ (r * n)) (n : ℕ)
    (x : M) (hx : x ^ l ^ n = 1) : ∃ y : M, y ^ l ^ (n + 1) = 1 ∧ y ^ l = x := by
  have hp : l.Prime := Fact.out
  let K : ℕ → Subgroup M := fun n => (powMonoidHom (l ^ n) : M →* M).ker
  have hmem : ∀ n (y : M), y ∈ K n ↔ y ^ l ^ n = 1 := fun n y => by
    simp [K, MonoidHom.mem_ker, powMonoidHom_apply]
  have hK : ∀ n, Nat.card (K n) = l ^ (r * n) := fun n =>
    (Nat.card_congr (Equiv.subtypeEquivRight fun y => hmem n y)).trans (hc n)
  have hfin : ∀ n, Finite (K n) := fun n =>
    Nat.finite_of_card_ne_zero (by rw [hK n]; exact pow_ne_zero _ hp.ne_zero)
  let φ : K (n + 1) →* M := (powMonoidHom l).comp (K (n + 1)).subtype
  have hφ : ∀ y : K (n + 1), φ y = (y : M) ^ l := fun y => rfl
  have hrange : φ.range ≤ K n := by
    rintro _ ⟨y, rfl⟩
    rw [hmem, hφ, ← pow_mul, ← pow_succ']
    exact (hmem _ _).1 y.2
  have h1 : ∀ z : M, z ^ l = 1 → z ^ l ^ (n + 1) = 1 := fun z h => by
    rw [pow_succ', pow_mul, h, one_pow]
  have hker : Nat.card φ.ker = l ^ (r * 1) := by
    rw [← hc 1]
    refine Nat.card_congr
      { toFun := fun z => ⟨z.1.1, by rw [pow_one, ← hφ]; exact MonoidHom.mem_ker.1 z.2⟩
        invFun := fun z => ⟨⟨z.1, (hmem _ _).2 (h1 _ (by simpa using z.2))⟩,
          MonoidHom.mem_ker.2 (by rw [hφ]; simpa using z.2)⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
  have hcard : Nat.card φ.range = l ^ (r * n) := by
    have h := Subgroup.card_eq_card_quotient_mul_card_subgroup φ.ker
    rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange φ).toEquiv, hker, hK] at h
    refine Nat.eq_of_mul_eq_mul_right (pow_pos hp.pos (r * 1)) ?_
    rw [← h, ← pow_add]
    ring_nf
  haveI := hfin n
  have heq : φ.range = K n := Subgroup.eq_of_le_of_card_ge hrange (by rw [hcard, hK])
  obtain ⟨y, hy⟩ : x ∈ φ.range := heq ▸ (hmem n x).2 hx
  exact ⟨y.1, (hmem _ _).1 y.2, hy⟩

theorem exists_tate (hc : ∀ n : ℕ, Nat.card {x : M // x ^ (l ^ n) = 1} = l ^ (r * n)) (x : M)
    (hx : x ^ l = 1) : ∃ t : Tate l M, t.lev 1 = x := by
  choose L hL using exists_pow_eq hc
  let u : ∀ m : ℕ, {y : M // y ^ l ^ (m + 1) = 1} := fun m =>
    Nat.rec (motive := fun m => {y : M // y ^ l ^ (m + 1) = 1}) ⟨x, by simpa using hx⟩
      (fun m y => ⟨L (m + 1) y.1 y.2, (hL _ _ _).1⟩) m
  have hu : ∀ m, (u (m + 1)).1 ^ l = (u m).1 := fun m => (hL _ _ _).2
  let s : ℕ → M := fun k => Nat.casesOn k 1 fun m => (u m).1
  refine ⟨Tate.mk s fun k => ⟨?_, ?_⟩, rfl⟩
  · rcases k with _ | m
    · exact one_pow _
    · exact (u m).2
  · rcases k with _ | m
    · exact hx
    · exact hu m

theorem exists_independent (hr : Nat.card {x : M // x ^ l = 1} = l ^ r) :
    ∃ e : Fin r → M, (∀ i, e i ^ l = 1) ∧
      ∀ k : Fin r → ℤ, ∏ i, e i ^ k i = 1 → ∀ i, (l : ℤ) ∣ k i := by
  have hp : l.Prime := Fact.out
  let K : Subgroup M := (powMonoidHom l : M →* M).ker
  have hmem : ∀ y : M, y ∈ K ↔ y ^ l = 1 := fun y => by
    simp [K, MonoidHom.mem_ker, powMonoidHom_apply]
  have hK : Nat.card K = l ^ r :=
    (Nat.card_congr (Equiv.subtypeEquivRight fun y => hmem y)).trans hr
  haveI : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; exact pow_ne_zero _ hp.ne_zero)
  letI : Module (ZMod l) (Additive K) := AddCommGroup.zmodModule fun z => by
    apply Additive.toMul.injective
    apply Subtype.ext
    simp only [toMul_nsmul, toMul_zero, SubmonoidClass.coe_pow, OneMemClass.coe_one]
    exact (hmem _).1 (Additive.toMul z).2
  haveI : Finite (Additive K) := inferInstanceAs (Finite K)
  haveI : Fintype (Additive K) := Fintype.ofFinite _
  haveI hMF : Module.Finite (ZMod l) (Additive K) := Module.Finite.of_finite
  haveI hMFr : Module.Free (ZMod l) (Additive K) := Module.Free.of_divisionRing _ _
  have hfr : Module.finrank (ZMod l) (Additive K) = r := by
    have h1 := Module.card_eq_pow_finrank (K := ZMod l) (V := Additive K)
    rw [ZMod.card, ← Nat.card_eq_fintype_card] at h1
    exact Nat.pow_right_injective hp.two_le (h1.symm.trans hK)
  let b : Module.Basis (Fin r) (ZMod l) (Additive K) :=
    @Module.finBasisOfFinrankEq (ZMod l) (Additive K) _ _ _ hMFr _ hMF r hfr
  let v : Fin r → Additive K := @DFunLike.coe _ _ _ Module.Basis.instFunLike b
  have hv : LinearIndependent (ZMod l) v := b.linearIndependent
  refine ⟨fun i => ((Additive.toMul (v i) : K) : M), fun i => (hmem _).1 (Additive.toMul (v i)).2,
    fun k hk i => ?_⟩
  have hli := Fintype.linearIndependent_iff.1 hv (fun i => (k i : ZMod l)) ?_ i
  · exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).1 hli
  · simp_rw [Int.cast_smul_eq_zsmul]
    apply Additive.toMul.injective
    apply Subtype.ext
    rw [toMul_sum]
    simpa [toMul_zsmul] using hk

theorem free_finite_finrank (M : Type) [CommGroup M] (l : ℕ) [Fact l.Prime] (r : ℕ)
    (hc : ∀ n : ℕ, Nat.card {x : M // x ^ (l ^ n) = 1} = l ^ (r * n)) :
    Module.Free ℤ_[l] (Tate l M) ∧ Module.Finite ℤ_[l] (Tate l M) ∧
      Module.finrank ℤ_[l] (Tate l M) = r := by
  have hp : l.Prime := Fact.out
  obtain ⟨e, he1, hind⟩ := exists_independent (M := M) (l := l) (r := r) (by simpa using hc 1)
  choose t ht using fun i => exists_tate hc (e i) (he1 i)

  have key : ∀ n (k : Fin r → ℤ), ∏ i, (t i).lev n ^ k i = 1 → ∀ i, (l : ℤ) ^ n ∣ k i := by
    intro n
    induction n with
    | zero => intro k _ i; simp
    | succ n ih =>
      intro k hk i
      have hl : ∀ j, (t j).lev (n + 1) ^ l ^ n = e j := fun j => by
        rw [add_comm, Tate.lev_add_pow, ht]
      have h1 : ∏ j, e j ^ k j = 1 := by
        have h2 := congrArg (· ^ (l ^ n)) hk
        simp only [one_pow, ← Finset.prod_pow, zpow_pow_comm', hl] at h2
        exact h2
      choose k' hk' using hind k h1
      have h3 : ∏ j, (t j).lev n ^ k' j = 1 := by
        rw [← hk]
        refine Finset.prod_congr rfl fun j _ => ?_
        rw [hk' j, zpow_mul, zpow_natCast, Tate.lev_succ]
      rw [hk' i, pow_succ']
      exact mul_dvd_mul_left _ (ih k' h3 i)
  have key2 : ∀ n (k k' : Fin r → ℕ), ∏ i, (t i).lev n ^ k i = ∏ i, (t i).lev n ^ k' i →
      ∀ i, (l : ℤ) ^ n ∣ (k i : ℤ) - k' i := fun n k k' h =>
    key n (fun i => (k i : ℤ) - k' i) (by
      simp only [zpow_sub, zpow_natCast, Finset.prod_mul_distrib, Finset.prod_inv_distrib, h,
        mul_inv_cancel])

  have hgen : ∀ n (x : M), x ^ l ^ n = 1 → ∃ c : Fin r → ℕ, ∏ i, (t i).lev n ^ c i = x := by
    intro n
    haveI : NeZero (l ^ n) := ⟨pow_ne_zero _ hp.ne_zero⟩
    haveI : Finite {x : M // x ^ l ^ n = 1} :=
      Nat.finite_of_card_ne_zero (by rw [hc n]; exact pow_ne_zero _ hp.ne_zero)
    let ψ : (Fin r → ZMod (l ^ n)) → {x : M // x ^ l ^ n = 1} := fun c =>
      ⟨∏ i, (t i).lev n ^ (c i).val, by
        rw [← Finset.prod_pow]
        exact Finset.prod_eq_one fun i _ => by
          rw [← pow_mul, mul_comm, pow_mul, Tate.lev_pow, one_pow]⟩
    have hinj : Function.Injective ψ := fun c c' h => funext fun i => by
      have h1 := key2 n _ _ (congrArg Subtype.val h) i
      rw [← sub_eq_zero, ← ZMod.natCast_zmod_val (c i), ← ZMod.natCast_zmod_val (c' i)]
      have h2 := (ZMod.intCast_zmod_eq_zero_iff_dvd (((c i).val : ℤ) - (c' i).val) (l ^ n)).2
        (by exact_mod_cast h1)
      push_cast at h2
      exact h2
    have hbij := hinj.bijective_of_nat_card_le (by
      rw [hc n, Nat.card_fun, Nat.card_zmod, Nat.card_eq_fintype_card, Fintype.card_fin, ← pow_mul,
        mul_comm])
    intro x hx
    obtain ⟨c, hc'⟩ := hbij.2 ⟨x, hx⟩
    exact ⟨fun i => (c i).val, congrArg Subtype.val hc'⟩

  let Φ := Fintype.linearCombination ℤ_[l] t
  have hΦ : ∀ a n, (Φ a).lev n = ∏ i, (t i).lev n ^ digit n (a i) := fun a n => by
    rw [Fintype.linearCombination_apply, lev_sum]
    rfl
  have hinj : Function.Injective Φ := by
    refine (injective_iff_map_eq_zero Φ).2 fun a ha => funext fun i =>
      PadicInt.ext_of_toZModPow.1 fun n => ?_
    have h1 := key2 n (fun i => digit n (a i)) (fun _ => 0) (by
      rw [← hΦ, ha]
      simp) i
    rw [← cast_digit, Pi.zero_apply, map_zero]
    have h2 := (ZMod.intCast_zmod_eq_zero_iff_dvd (digit n (a i) : ℤ) (l ^ n)).2
      (by simpa using h1)
    exact_mod_cast h2
  have hsurj : Function.Surjective Φ := by
    intro x
    choose c hc' using fun n => hgen n (x.lev n) (x.lev_pow n)
    have hdiv : ∀ i n, (l : ℤ) ^ n ∣ ((c (n + 1) i : ℕ) : ℤ) - c n i := fun i n =>
      key2 n (c (n + 1)) (c n) (by
        rw [hc' n, ← x.lev_succ, ← hc' (n + 1), ← Finset.prod_pow]
        refine Finset.prod_congr rfl fun j _ => ?_
        rw [← pow_mul, mul_comm, pow_mul, Tate.lev_succ]) i
    have hex : ∀ i, ∃ a : ℤ_[l], ∀ n, PadicInt.toZModPow n a = ((c n i : ℤ) : ZMod (l ^ n)) :=
      fun i => ⟨_, PadicInt.toZModPow_ofIntSeq_of_pow_dvd_sub (fun n => (c n i : ℤ)) l (hdiv i)⟩
    choose a ha using hex
    refine ⟨a, Tate.ext fun n => ?_⟩
    rw [hΦ, ← hc' n]
    refine Finset.prod_congr rfl fun i _ => pow_digit_eq ((t i).lev_pow n) ?_
    rw [ha, Int.cast_natCast]
  let E : (Fin r → ℤ_[l]) ≃ₗ[ℤ_[l]] Tate l M := LinearEquiv.ofBijective Φ ⟨hinj, hsurj⟩
  exact ⟨Module.Free.of_equiv E, Module.Finite.equiv E,
    E.finrank_eq.symm.trans (Module.finrank_fin_fun ℤ_[l])⟩

end GlobalTheory.TateFree
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorHigherLevelPointsEqOfSameImage
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT
open GlobalTheory.UPel.HT.MapComp

namespace GlobalTheory.UPel.HT.LiftUniq

theorem eq_of_same_image : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N N' : ℕ) (hd : N ∣ N') (hc : N'.Coprime p) (S : Scheme.{0}) (s : S ⟶ Sp R) (o : Obj b N s) (M' : Model b N') (π : M'.X ⟶ S), π ≫ s = M'.s → ∀ (om : ObjMap (M'.univ.forget N hd hc) o π) (T : Scheme.{0}) (g₁ g₂ : T ⟶ M'.X), g₁ ≫ π = g₂ ≫ π → (∀ a, g₁ ≫ (M'.univ.eta a).left ≫ om.φ = g₂ ≫ (M'.univ.eta a).left ≫ om.φ) → g₁ = g₂ := by
  intro p _ D R _ b N N' hd hc S s o M' π hπ om T g₁ g₂ hg hη
  obtain ⟨o₁, ⟨m₁⟩⟩ := GlobalTheory.T.exists_harrisTaylorObject_pullback p D R b N' M'.X T M'.s g₁ M'.univ
  obtain ⟨ψ, ψ₂, hcart, hsq, hact0, hpol, hη'⟩ : ∃ (ψ : M'.univ.A.left ⟶ o.A.left)
      (ψ₂ : (M'.univ.A ⊗ M'.univ.A).left ⟶ (o.A ⊗ o.A).left), IsGrpPullback M'.univ.A o.A π ψ ∧
      IsSquare ψ ψ₂ ∧ (∀ c, (M'.univ.act.act c).left ≫ ψ = ψ ≫ (o.act.act c).left) ∧
      Nonempty (LBIso M'.univ.P (o.P.pull ψ₂)) ∧
      (∀ a, g₁ ≫ (M'.univ.eta a).left ≫ ψ = g₂ ≫ (M'.univ.eta a).left ≫ ψ) :=
    ⟨om.φ, om.φ₂, om.cart, om.sq, om.act, ⟨om.pol⟩, hη⟩
  obtain ⟨hpol⟩ := hpol
  clear hη
  have hpb : IsPullback ψ M'.univ.A.hom o.A.hom π := hcart.1
  have w : (m₁.φ ≫ ψ) ≫ o.A.hom = (o₁.A.hom ≫ g₂) ≫ π := by
    have h2 : m₁.φ ≫ M'.univ.A.hom = o₁.A.hom ≫ g₁ := m₁.cart.1.w
    rw [Category.assoc, hpb.w, ← Category.assoc, h2, Category.assoc, hg, Category.assoc]
  obtain ⟨φ, hφ, hφ'⟩ : ∃ φ : o₁.A.left ⟶ M'.univ.A.left, φ ≫ ψ = m₁.φ ≫ ψ ∧
      φ ≫ M'.univ.A.hom = o₁.A.hom ≫ g₂ :=
    ⟨hpb.lift _ _ w, hpb.lift_fst _ _ _, hpb.lift_snd _ _ _⟩
  have n : IsGrpPullback o₁.A o.A (g₂ ≫ π) (φ ≫ ψ) := by
    rw [hφ, ← hg]; exact m₁.cart.comp hcart
  obtain ⟨φ₂, sq⟩ := exists_isSquare hφ'
  have e : m₁.φ₂ ≫ ψ₂ = φ₂ ≫ ψ₂ :=
    isSquare_unique (isSquare_comp m₁.sq hsq) (hφ ▸ isSquare_comp sq hsq)
  have hact : ∀ c, (o₁.act.act c).left ≫ φ = φ ≫ (M'.univ.act.act c).left := by
    intro c
    apply hpb.hom_ext
    · rw [Category.assoc, hφ, ← Category.assoc, m₁.act, Category.assoc, hact0, Category.assoc, hact0,
        ← Category.assoc, ← Category.assoc, hφ]
    · rw [Category.assoc, hφ', ← Category.assoc, Over.w, Category.assoc, Over.w, hφ']
  have heta : ∀ y, (o₁.eta y).left ≫ φ = g₂ ≫ (M'.univ.eta y).left := by
    intro y
    apply hpb.hom_ext
    · rw [Category.assoc, hφ, ← Category.assoc, m₁.eta, Category.assoc, Category.assoc]
      exact hη' y
    · rw [Category.assoc, hφ', ← Category.assoc, Over.w, Category.assoc, Over.w]
      show 𝟙 _ ≫ g₂ = g₂ ≫ 𝟙 _
      rw [Category.id_comp, Category.comp_id]
  have pol : LBIso o₁.P (M'.univ.P.pull φ₂) :=
    LBIso.trans o₁.isLB (pull_isLB o.isLB _) (pull_isLB M'.univ.isLB _)
      (LBIso.trans o₁.isLB (pull_isLB M'.univ.isLB _) (pull_isLB o.isLB _) m₁.pol
        (lbIso_pull_comp hpol m₁.φ₂ rfl))
      (LBIso.symm (lbIso_pull_comp hpol φ₂ e))
  let m₂ : ObjMap o₁ M'.univ g₂ :=
    { φ := φ, φ₂ := φ₂, cart := hcart.cancel n hφ', sq := sq, act := hact, pol := pol, eta := heta }
  have h2 : g₂ ≫ M'.s = g₁ ≫ M'.s := by rw [← hπ, ← Category.assoc, ← hg, Category.assoc]
  exact ((M'.rep T (g₁ ≫ M'.s) o₁).unique ⟨rfl, ⟨m₁⟩⟩ ⟨h2, ⟨m₂⟩⟩)

end GlobalTheory.UPel.HT.LiftUniq
end
end

