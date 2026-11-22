import Mathlib
import ReciprocityTheory.L2DbarEstimates.Imports
import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.FourSignHolds
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.L2ExtensionLogCanonical
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0004
import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0634
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0020
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0019
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
import Development.AbelianVarietyTheory.Definitions.Divisors.IsKSValueOneOfRetraction
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0004
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0064
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CobOneEqZeroOfConnecting
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0635
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CardNonempty
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DUnitMemRangeOfMemKerIdeal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0577
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0636
import Development.AbelianVarietyTheory.Definitions.Divisors.ToRingActOpOfRingAct
import Development.AbelianVarietyTheory.Definitions.Divisors.NonemptyHomFixRepTrivial
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleLocalInverse
section
open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff

namespace GlobalTheory.OTY

theorem Etale.contDiffAt_chart {n : ℕ} {Y : Type} [TopologicalSpace Y] [T2Space Y]
    [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] {ι La : Type} [AddCommGroup La]
    {A : WeightedAtlas n Y ι La} {U : Set Y} {z : Y → V n} (hE : Etale A U z) {x : Y} (hx : x ∈ U)
    {i : ι} (hi : x ∈ (A.chart i).source) :
    ContDiffAt ℂ ∞ (z ∘ (A.chart i).symm) (A.chart i x) := by
  have hS : IsOpen ((A.chart i).target ∩ (A.chart i).symm ⁻¹' U) :=
    (A.chart i).isOpen_inter_preimage_symm hE.isOpen
  have hmem : A.chart i x ∈ (A.chart i).target ∩ (A.chart i).symm ⁻¹' U :=
    ⟨(A.chart i).map_source hi, by simp [(A.chart i).left_inv hi, hx]⟩
  rw [contDiffAt_euclidean]
  intro k
  have hk : DifferentiableOn ℂ (fun w => (z ∘ (A.chart i).symm) w k)
      ((A.chart i).target ∩ (A.chart i).symm ⁻¹' U) :=
    (EuclideanSpace.proj (𝕜 := ℂ) k).differentiable.comp_differentiableOn (hE.holo i)
  exact (contDiffOn_of_differentiableOn n _ _ hS hk).contDiffAt (hS.mem_nhds hmem)

theorem etale_local_inverse : ∀ (n : ℕ) (Y : Type) [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] (ι La : Type) [AddCommGroup La] (A : WeightedAtlas n Y ι La), ∀ (U : Set Y) (z : Y → V n), Etale A U z → ∀ e : OpenPartialHomeomorph U (V n), IsChart n (fun y : U => z y) e → ∀ v ∈ e.target, ∀ i, ((e.symm v : U) : Y) ∈ (A.chart i).source → ContDiffAt ℂ ∞ (fun v' => A.chart i (e.symm v' : U)) v ∧ (∀ᶠ v' in 𝓝 v, ((e.symm v' : U) : Y) ∈ (A.chart i).source) ∧ ∀ ξ : V n, fderiv ℂ (fun v' => A.chart i (e.symm v' : U)) v (jz A z i (e.symm v : U) ξ) = ξ := by
  intro n Y _ _ _ _ _ ι La _ A U z hE e he v hv i hi
  set g : V n → V n := z ∘ (A.chart i).symm with hg_def
  have hg : ContDiffAt ℂ ∞ g (A.chart i (e.symm v : U)) := hE.contDiffAt_chart (e.symm v).2 hi
  have hdet : (jz A z i (e.symm v : U)).det ≠ 0 := hE.det_ne i _ (e.symm v).2 hi
  set f' : V n ≃L[ℂ] V n :=
    (jz A z i (e.symm v : U)).toContinuousLinearEquivOfDetNeZero hdet with hf'_def
  have hf'coe : (f' : V n →L[ℂ] V n) = fderiv ℂ g (A.chart i (e.symm v : U)) := by
    ext w; rfl
  have hf' : HasFDerivAt g (f' : V n →L[ℂ] V n) (A.chart i (e.symm v : U)) := by
    rw [hf'coe]; exact (hg.differentiableAt (by simp)).hasFDerivAt
  have hn : (∞ : WithTop ℕ∞) ≠ 0 := by simp
  have hstrict := hg.hasStrictFDerivAt' hf' hn

  have hgv : g (A.chart i (e.symm v : U)) = v := by
    have h1 : z (e.symm v : U) = e (e.symm v) := he (e.map_target hv)
    show z ((A.chart i).symm (A.chart i (e.symm v : U))) = v
    rw [(A.chart i).left_inv hi, h1, e.right_inv hv]

  set h : V n → V n := fun v' => A.chart i (e.symm v' : U) with hh_def
  have hcoe : ContinuousAt (fun v' => ((e.symm v' : U) : Y)) v :=
    continuous_subtype_val.continuousAt.comp (e.continuousAt_symm hv)
  have hhc : ContinuousAt h v :=
    ContinuousAt.comp (g := A.chart i) (f := fun v' => ((e.symm v' : U) : Y)) (x := v)
      ((A.chart i).continuousAt hi) hcoe
  have hsrc : ∀ᶠ v' in 𝓝 v, ((e.symm v' : U) : Y) ∈ (A.chart i).source :=
    hcoe.preimage_mem_nhds ((A.chart i).open_source.mem_nhds hi)
  have htgt : ∀ᶠ v' in 𝓝 v, v' ∈ e.target := e.open_target.mem_nhds hv

  have hright : ∀ᶠ v' in 𝓝 v, g (h v') = v' := by
    filter_upwards [hsrc, htgt] with v' h1 h2
    have h3 : z (e.symm v') = e (e.symm v') := he (e.map_target h2)
    show z ((A.chart i).symm (A.chart i (e.symm v' : U))) = v'
    rw [(A.chart i).left_inv h1, h3, e.right_inv h2]

  have hleft : ∀ᶠ v' in 𝓝 v,
      hstrict.localInverse g f' (A.chart i (e.symm v : U)) (g (h v')) = h v' :=
    hhc.tendsto.eventually hstrict.eventually_left_inverse
  have heq : h =ᶠ[𝓝 v] hstrict.localInverse g f' (A.chart i (e.symm v : U)) := by
    filter_upwards [hleft, hright] with v' h1 h2
    rw [← h1, h2]
  have hinv := hstrict.to_localInverse
  rw [hgv] at hinv
  have hGc : ContDiffAt ℂ ∞ (hstrict.localInverse g f' (A.chart i (e.symm v : U))) v := by
    have := hg.to_localInverse hf' hn
    rw [hgv] at this
    exact this
  refine ⟨hGc.congr_of_eventuallyEq heq, hsrc, fun ξ => ?_⟩
  have hfd : fderiv ℂ h v = (f'.symm : V n →L[ℂ] V n) :=
    heq.fderiv_eq.trans hinv.hasFDerivAt.fderiv
  change fderiv ℂ h v (jz A z i (e.symm v : U) ξ) = ξ
  rw [hfd]
  exact f'.symm_apply_apply ξ

end GlobalTheory.OTY
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EvMemIdealSmulAddP
section
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup

namespace GlobalTheory

theorem Chart.ev_mem_ideal_smul_add_p (p : ℕ) (O : Type) [CommRing O] (G : PDivGroup p O) (d : ℕ)
    (c : QLog.Chart G d) (n : ℕ) (I : Ideal O) (h : MvPowerSeries (Fin d) O) :
    (∀ α, coeff α h ∈ I) → ∃ a ∈ I • (⊤ : Submodule O (G.A n)), ∃ b : G.A n,
      c.ev n h = a + (p : G.A n) * b := by
  intro hI
  classical
  obtain ⟨N, hN⟩ := (c.isEval n).2 1
  let S : Finset (Fin d →₀ ℕ) := Finset.Iic (Finsupp.equivFunOnFinite.symm fun _ => N)
  let h₁ : MvPowerSeries (Fin d) O := ∑ α ∈ S, monomial α (coeff α h)
  have hmon : ∀ α, (monomial α (coeff α h) : MvPowerSeries (Fin d) O) =
      coeff α h • monomial α (1 : O) := by
    intro α
    ext β
    simp only [coeff_monomial, coeff_smul]
    split_ifs <;> simp
  have hcoeff : ∀ β ∈ S, coeff β h₁ = coeff β h := by
    intro β hβ
    simp only [h₁, map_sum, coeff_monomial]
    rw [Finset.sum_eq_single_of_mem β hβ]
    · simp
    · intro b _ hb; simp [Ne.symm hb]
  have h₂ : (p : G.A n) ^ 1 ∣ c.ev n (h - h₁) := by
    apply hN
    intro β hβ
    have hmem : β ∈ S := by
      simp only [S, Finset.mem_Iic]
      intro i
      show β i ≤ N
      have : β i ≤ β.degree := by
        by_cases h0 : β i = 0
        · omega
        rw [Finsupp.degree]
        exact Finset.single_le_sum (f := fun j => β j) (fun _ _ => Nat.zero_le _)
          (by simpa using h0)
      omega
    rw [map_sub, hcoeff β hmem, sub_self]
  obtain ⟨b, hb⟩ := h₂
  refine ⟨c.ev n h₁, ?_, b, ?_⟩
  · simp only [h₁, map_sum]
    refine Submodule.sum_mem _ fun α _ => ?_
    rw [hmon, map_smul]
    exact Submodule.smul_mem_smul (hI α) Submodule.mem_top
  · rw [map_sub, pow_one] at hb
    rw [← hb]; ring

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdjointPrimeToPSimilitudeStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_adjoint_primeToP_similitude : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (g : D.La →ₗ[D.O] D.La) (c k : ℕ), c.Coprime p → k.Coprime p → (∀ x y, D.EF (g x) (g y) = c * D.EF x y) → (∀ x, ∃ y, g y = k • x) → c ∣ k ^ 2 → ∃ g' : D.La →ₗ[D.O] D.La, (∀ x, g (g' x) = k • x) ∧ (∀ x, g' (g x) = k • x) ∧ (∀ x y, D.EF (g' x) (g' y) = (k ^ 2 / c) * D.EF x y) ∧ (∀ x, ∃ y, g' y = k • x) ∧ (k ^ 2 / c).Coprime p ∧ (k ^ 2 / c) ∣ k ^ 2 ∧ c * (k ^ 2 / c) = k ^ 2 := by
  first | exact @GlobalTheory.UPel.HT.Hecke.exists_adjoint_similitude | exact GlobalTheory.UPel.HT.Hecke.exists_adjoint_similitude | (intros; apply GlobalTheory.UPel.HT.Hecke.exists_adjoint_similitude <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAffineMapNeTop
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.DeRham

namespace GlobalTheory.PointSec

theorem exists_affine_map_ne_top : ∀ (R' : Type) [CommRing R'] (X X' : Scheme.{0}) (s' : X' ⟶ Sp R') (φ : X' ⟶ X), Surjective s' → ∀ m : Ideal R', m.IsMaximal → ∃ U : X.affineOpens, Ideal.map (algebraMap R' (Sec s' (φ ⁻¹ᵁ U.1))) m ≠ ⊤ := by
  intro R' _ X X' s' φ hs m hm
  obtain ⟨x', hx'⟩ := hs.surj (⟨m, hm.isPrime⟩ : PrimeSpectrum R')
  obtain ⟨U, hU, hxU, -⟩ := (TopologicalSpace.Opens.isBasis_iff_nbhd.1 X.isBasis_affineOpens)
    (show φ.base x' ∈ (⊤ : X.Opens) from trivial)
  refine ⟨⟨U, hU⟩, ?_⟩
  have hx : x' ∈ φ ⁻¹ᵁ U := hxU
  intro htop
  let g : Sec s' (φ ⁻¹ᵁ U) →+* X'.presheaf.stalk x' := (X'.presheaf.germ (φ ⁻¹ᵁ U) x' hx).hom
  have key : ∀ a ∈ m, ¬ IsUnit (g (algebraMap R' (Sec s' (φ ⁻¹ᵁ U)) a)) := by
    intro a ha hu
    have h1 : x' ∈ X'.basicOpen (algebraMap R' (Sec s' (φ ⁻¹ᵁ U)) a : Γ(X', φ ⁻¹ᵁ U)) :=
      (Scheme.mem_basicOpen _ _ _ hx).2 hu
    change x' ∈ X'.basicOpen ((X'.presheaf.map (homOfLE (le_top : φ ⁻¹ᵁ U ≤ s' ⁻¹ᵁ ⊤)).op)
      (s'.app ⊤ ((Scheme.ΓSpecIso (CommRingCat.of R')).inv a))) at h1
    have h2 : x' ∈ X'.basicOpen (s'.app ⊤ ((Scheme.ΓSpecIso (CommRingCat.of R')).inv a)) :=
      Scheme.basicOpen_restrict X' (homOfLE (le_top : φ ⁻¹ᵁ U ≤ s' ⁻¹ᵁ ⊤)) _ h1
    have h3 : x' ∈ s' ⁻¹ᵁ (Sp R').basicOpen ((Scheme.ΓSpecIso (CommRingCat.of R')).inv a) := by
      rw [Scheme.preimage_basicOpen]; exact h2
    have h4 : s'.base x' ∈ (Sp R').basicOpen ((Scheme.ΓSpecIso (CommRingCat.of R')).inv a) := h3
    rw [basicOpen_eq_of_affine] at h4
    have h2 : s'.base x' ∈ PrimeSpectrum.basicOpen a := h4
    rw [hx'] at h2
    exact h2 ha
  have hle : Ideal.map (algebraMap R' (Sec s' (φ ⁻¹ᵁ U))) m ≤
      (IsLocalRing.maximalIdeal (X'.presheaf.stalk x')).comap g := by
    rw [Ideal.map_le_iff_le_comap]
    intro a ha
    exact key a ha
  have h1 : (1 : Sec s' (φ ⁻¹ᵁ U)) ∈ (IsLocalRing.maximalIdeal (X'.presheaf.stalk x')).comap g :=
    hle (by rw [show Ideal.map (algebraMap R' (Sec s' (φ ⁻¹ᵁ U))) m = ⊤ from htop]; trivial)
  rw [Ideal.mem_comap, map_one] at h1
  exact (IsLocalRing.mem_maximalIdeal _).1 h1 isUnit_one
end GlobalTheory.PointSec
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAinfFrameLiftTwistedFrobenius
section
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

namespace GlobalTheory.FLam

theorem exists_fixed {B : Type} [CommRing B] (q : B) [h : IsAdicComplete (Ideal.span {q}) B]
    (σ : B →+* B) (hσ : σ q = q) (w : B) : ∃ c : B, c = -w + q * σ c := by
  first
  | exact @_root_.GlobalTheory.FixedPointApproximation.exists_fixed
  | exact _root_.GlobalTheory.FixedPointApproximation.exists_fixed
  | (apply _root_.GlobalTheory.FixedPointApproximation.exists_fixed <;> assumption)
  | (intros; apply _root_.GlobalTheory.FixedPointApproximation.exists_fixed <;> assumption)
  | (intros; apply @_root_.GlobalTheory.FixedPointApproximation.exists_fixed <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.FixedPointApproximation.exists_fixed ..)

theorem one_add_pow_of_sq {B : Type} [CommRing B] (x : B) (hx : x * x = 0) (n : ℕ) :
    (1 + x) ^ n = 1 + n * x := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, ih]; push_cast
    linear_combination (n : B) * hx

theorem frobenius_mu (p : ℕ) [Fact p.Prime] (O : Type) [CommRing O] [Fact ¬IsUnit (p : O)]
    [IsAdicComplete (Ideal.span {(p : O)}) O] (ε : PreTilt O p) :
    WittVector.frobenius (Sandwich.mu ε) = (Sandwich.mu ε + 1) ^ p - 1 := by
  unfold Sandwich.mu
  rw [WittVector.frobenius_eq_map_frobenius, map_sub, map_one, WittVector.map_teichmuller,
    frobenius_def, map_pow]
  ring

theorem σ_τ {p : ℕ} [Fact p.Prime] {O : Type} [CommRing O] [Fact ¬IsUnit (p : O)]
    [IsAdicComplete (Ideal.span {(p : O)}) O] {ε : PreTilt O p} (F : BFrame ε) :
    F.σ F.τ = p * F.τ := by
  have tf : ∀ x : F.B, (p : F.B) * x = 0 → x = 0 := by
    intro x hx
    have h1 : (p : F.Q) * algebraMap F.B F.Q x = 0 := by
      rw [← map_natCast (algebraMap F.B F.Q), ← map_mul, hx, map_zero]
    have h2 := (F.frame.unit_p.mul_right_eq_zero).1 h1
    exact F.frame.inj (by rw [h2, map_zero])
  apply sub_eq_zero.1
  apply tf
  have e1 : (p : F.B) * F.σ F.τ = F.a (WittVector.frobenius (Sandwich.mu ε)) := by
    rw [← F.σ_a, ← F.p_τ, map_mul, map_natCast]
  have e2 : F.a (WittVector.frobenius (Sandwich.mu ε)) = p * (p * F.τ) := by
    have hsq : (p * F.τ) * (p * F.τ) = 0 := by
      rw [show (p : F.B) * F.τ * (p * F.τ) = p * p * (F.τ * F.τ) by ring, F.τ_sq, mul_zero]
    rw [frobenius_mu, map_sub, map_pow, map_add, map_one, ← F.p_τ, add_comm,
      one_add_pow_of_sq _ hsq]
    ring
  rw [mul_sub, e1, e2, sub_self]

end GlobalTheory.FLam

open GlobalTheory.FLam in

theorem GlobalTheory.FLam.exists_lam : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ (ε : PreTilt O p) (hε : IsPrimitiveSystem ε), ∀ F : BFrame ε, ∀ u : F.B, F.τ ∣ u - 1 → ∃ l : F.B, F.τ ∣ l - 1 ∧ F.σ l = u * l := by
  intro p _ C _ _ _ v O _ _ _ _ _ _ ε _ F u hu
  obtain ⟨w, hw⟩ := hu
  haveI : IsAdicComplete (Ideal.span {(p : F.B)}) F.B := F.frame.complete
  obtain ⟨c, hc⟩ := exists_fixed (p : F.B) F.σ (map_natCast F.σ p) w
  refine ⟨1 + F.τ * c, ⟨c, by ring⟩, ?_⟩
  have hu' : u = 1 + F.τ * w := by rw [← hw]; ring
  rw [map_add, map_one, map_mul, σ_τ, hu']
  have hτ := F.τ_sq
  linear_combination (-(w * c)) * hτ - F.τ * hc
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCartierDualLiftLinearCoefficientsMod
section
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat GlobalTheory.LawDer

theorem GlobalTheory.QLog.Chart.exists_dual_lift_lin : ∀ (p : ℕ) (O : Type) [CommRing O] (G : PDivGroup p O) (d : ℕ) (c : QLog.Chart G d) (m : Ideal O), (p : O) ∈ m → ∃ n : ℕ, ∀ u : Fin d → O, ∃ φ : G.dual.A n, ∀ F, φ (c.ev n F) - ∑ i, u i * lin F i ∈ m := by
  intro p O _ G d c m hp
  obtain ⟨n, hn⟩ := c.ker 1 2
  refine ⟨n, fun u => ?_⟩
  let L : MvPowerSeries (Fin d) O →ₗ[O] O := ∑ i, u i • coeff (Finsupp.single i 1)
  have hL : ∀ F, L F = ∑ i, u i * lin F i := fun F => by simp [L, LinearMap.sum_apply, lin]
  let f : MvPowerSeries (Fin d) O →ₗ[O] O ⧸ m := m.mkQ ∘ₗ L
  have hk : LinearMap.ker (c.ev n).toLinearMap ≤ LinearMap.ker f := by
    intro F hF
    have h := hn F hF
    change Ideal.Quotient.mk m (L F) = 0
    rw [Ideal.Quotient.eq_zero_iff_mem, hL]
    refine Submodule.sum_mem _ fun i _ => m.mul_mem_left _ ?_
    obtain ⟨a, ha⟩ := h (Finsupp.single i 1) (by simp)
    have : lin F i = p ^ 1 * a := ha
    rw [this, pow_one]
    exact m.mul_mem_right _ hp
  let g : G.A n →ₗ[O] O ⧸ m := (LinearMap.ker (c.ev n).toLinearMap).liftQ f hk ∘ₗ
    ((c.ev n).toLinearMap.quotKerEquivOfSurjective (c.surj n)).symm.toLinearMap
  have hg : ∀ F, g (c.ev n F) = f F := fun F => by
    have : ((c.ev n).toLinearMap.quotKerEquivOfSurjective (c.surj n)).symm (c.ev n F) =
        Submodule.Quotient.mk F := by
      rw [LinearEquiv.symm_apply_eq]; rfl
    simp only [g, LinearMap.comp_apply, LinearEquiv.coe_coe, this, Submodule.liftQ_apply]
  obtain ⟨φ, hφ⟩ := Module.projective_lifting_property m.mkQ g m.mkQ_surjective
  refine ⟨WithConv.toConv φ, fun F => ?_⟩
  rw [← hL, ← Submodule.Quotient.eq]
  exact (LinearMap.congr_fun hφ (c.ev n F)).trans (hg F)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCartierDualTangentOfCoboundaryOneEqSmul
section
open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup

noncomputable section

namespace GlobalTheory

namespace PDiv

open Coalgebra Bialgebra

theorem exists_tangent_of_cobOne_eq_smul (O A : Type) [CommRing O] [CommRing A] [Bialgebra O A]
    [Module.Finite O A] [Module.Projective O A] [Coalgebra.IsCocomm O A] (a : O) (b : A)
    (z : A ⊗[O] A) (h : cobOne O A b = a • z) :
    ∃ u : Cot O (CartierDual O A) →ₗ[O] O ⧸ Ideal.span {a},
      ∀ φ : CartierDual O A, u (dUnit O φ) = Ideal.Quotient.mk _ (φ b) := by
  let D : CartierDual O A →ₗ[O] O ⧸ Ideal.span {a} :=
    (Ideal.Quotient.mkₐ O (Ideal.span {a})).toLinearMap ∘ₗ CartierDual.evalAt O A b
  have hcomul : comul b = b ⊗ₜ 1 + 1 ⊗ₜ b + a • z := by
    rw [← h, cobOne_apply]; abel
  have hD : ∀ φ ψ : CartierDual O A, D (φ * ψ) =
      counitAlgHom O (CartierDual O A) φ • D ψ + counitAlgHom O (CartierDual O A) ψ • D φ := by
    intro φ ψ
    have e : (φ * ψ) b = φ b * ψ 1 + φ 1 * ψ b + a * CartierDual.pair O A A (φ ⊗ₜ ψ) z := by
      rw [CartierDual.mul_apply, hcomul, map_add, map_add, map_smul]
      simp
    have ha : Ideal.Quotient.mk (Ideal.span {a}) a = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.subset_span rfl)
    simp only [D, LinearMap.comp_apply, CartierDual.evalAt_apply, AlgHom.toLinearMap_apply,
      Ideal.Quotient.mkₐ_eq_mk, e, map_add, map_mul, ha, zero_mul, add_zero, Algebra.smul_def,
      Ideal.Quotient.algebraMap_eq]
    rw [show counitAlgHom O (CartierDual O A) φ = φ 1 from rfl,
      show counitAlgHom O (CartierDual O A) ψ = ψ 1 from rfl]
    ring
  exact ⟨AugCot.lift _ D hD, fun φ => AugCot.lift_d _ D hD φ⟩

end PDiv

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCechCoboundaryOfDegreeTwoImageCoboundaryAlStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CechPoset

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_cech_coboundary_of_degreeTwo_image_coboundary' : ∀ {κ : Type} [LinearOrder κ] {R : Type} [CommRing R] (F : (NE κ)ᵒᵖ ⥤ CommAlgCat.{0} R) (y : CC F 2), δ F 2 y = 0 → ∀ f : C1 F, e2 F y = d1 F f → ∃ c : CC F 1, δ F 1 c = y := by
  first | exact @GlobalTheory.CechPoset.exists_cech_coboundary_of_degreeTwo_image_coboundary | exact GlobalTheory.CechPoset.exists_cech_coboundary_of_degreeTwo_image_coboundary | (intros; apply GlobalTheory.CechPoset.exists_cech_coboundary_of_degreeTwo_image_coboundary <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCechCocycleCohomologousPosetOneCocycleStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CechPoset

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_cech_cocycle_cohomologous_posetOneCocycle : ∀ {κ : Type} [LinearOrder κ] {R : Type} [CommRing R] (F : (NE κ)ᵒᵖ ⥤ CommAlgCat.{0} R) (f : Z1 F), ∃ z : CC F 1, δ F 1 z = 0 ∧ ∃ g : C0 F, f.1 - e1 F z = d0 F g := by
  first | exact @GlobalTheory.CechPoset.exists_cech_cocycle_cohomologous | exact GlobalTheory.CechPoset.exists_cech_cocycle_cohomologous | (intros; apply GlobalTheory.CechPoset.exists_cech_cocycle_cohomologous <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCechPrimitiveOfImageCoboundaryStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CechPoset

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_cech_primitive_of_image_coboundary : ∀ {κ : Type} [LinearOrder κ] {R : Type} [CommRing R] (F : (NE κ)ᵒᵖ ⥤ CommAlgCat.{0} R) (z : CC F 1), δ F 1 z = 0 → ∀ g : C0 F, e1 F z = d0 F g → ∃ c : CC F 0, δ F 0 c = z := by
  first | exact @GlobalTheory.CechHOneInj.exists_cech_primitive | exact GlobalTheory.CechHOneInj.exists_cech_primitive | (intros; apply GlobalTheory.CechHOneInj.exists_cech_primitive <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCompatiblePDivGroupLevelCoordinates
section
set_option autoImplicit false

open GlobalTheory GlobalTheory.PDivGroup
open scoped TensorProduct

namespace GlobalTheory.PDiv

theorem exists_aug_dUnit_eq {R A : Type*} [CommRing R] [CommRing A] [Bialgebra R A] (w : Cot R A) :
    ∃ a : A, Coalgebra.counit (R := R) a = 0 ∧ dUnit R a = w := by
  obtain ⟨x, rfl⟩ := (augIdeal R A).toCotangent_surjective w
  exact ⟨x, x.2, AugCot.d_coe _ x⟩

theorem exists_aug_lift_dUnit_eq {R A C : Type*} [CommRing R] [CommRing A] [CommRing C] [Bialgebra R A]
    [Bialgebra R C] {f : C →ₐc[R] A} (hf : Function.Surjective f) (a : A)
    (ha : Coalgebra.counit (R := R) a = 0) (w : Cot R C) (hw : cotMap f w = dUnit R a) :
    ∃ c : C, Coalgebra.counit (R := R) c = 0 ∧ dUnit R c = w ∧ f c = a := by
  obtain ⟨y, hy, rfl⟩ := exists_aug_dUnit_eq w
  have h1 : dUnit R (f y - a) = 0 := by
    rw [dUnit, map_sub, sub_eq_zero]
    exact (cotMap_d f y).symm.trans hw
  have h2 : Bialgebra.counitAlgHom R A (f y - a) = 0 := by simp [hy, ha]
  rw [dUnit, AugCot.d_eq_zero_iff, h2, map_zero, sub_zero] at h1
  have h3 : f y - a ∈ Ideal.map (f : C →ₐ[R] A) (augIdeal R C ^ 2) := by
    rw [Ideal.map_pow]
    have := kerIdeal_of_surjective hf
    rw [kerIdeal] at this
    rw [this]
    exact h1
  obtain ⟨z, hz, hfz⟩ := (Ideal.mem_map_iff_of_surjective (f : C →ₐ[R] A) hf).1 h3
  have hz0 : Bialgebra.counitAlgHom R C z = 0 := Ideal.pow_le_self two_ne_zero hz
  have hz1 : Coalgebra.counit (R := R) z = 0 := hz0
  refine ⟨y - z, by rw [map_sub, hy, hz1, sub_zero], ?_, ?_⟩
  · rw [dUnit, map_sub, (AugCot.d_eq_zero_iff _ z).2 (by rw [hz0, map_zero, sub_zero]; exact hz), sub_zero]
  · have : f z = f y - a := hfz
    rw [map_sub, this, sub_sub_cancel]

theorem exists_compatible_dUnit_eq {p : ℕ} {O : Type} [CommRing O] (G : PDivGroup p O) (w : G.omega) :
    ∃ x : ∀ n, G.A n, (∀ n, Coalgebra.counit (R := O) (x n) = 0) ∧ (∀ n, G.res n (x (n + 1)) = x n) ∧
      ∀ n, dUnit O (x n) = w.1 n := by
  obtain ⟨a, ha⟩ := exists_aug_dUnit_eq (w.1 0)
  have step : ∀ (n : ℕ) (a : {a : G.A n // Coalgebra.counit (R := O) a = 0 ∧ dUnit O a = w.1 n}),
      ∃ c : {a : G.A (n + 1) // Coalgebra.counit (R := O) a = 0 ∧ dUnit O a = w.1 (n + 1)},
        G.res n c.1 = a.1 := fun n a => by
    obtain ⟨c, h1, h2, h3⟩ := exists_aug_lift_dUnit_eq (G.res_surjective n) a.1 a.2.1 (w.1 (n + 1))
      ((w.2 n).trans a.2.2.symm)
    exact ⟨⟨c, h1, h2⟩, h3⟩
  choose s hs using step
  let x : ∀ n, {a : G.A n // Coalgebra.counit (R := O) a = 0 ∧ dUnit O a = w.1 n} :=
    fun n => Nat.rec ⟨a, ha⟩ s n
  exact ⟨fun n => (x n).1, fun n => (x n).2.1, fun n => hs n (x n), fun n => (x n).2.2⟩

theorem exists_compatible_coordinates (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C]
    (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)]
    [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O] (hv : v.Integers O) (G : PDivGroup p O) :
    ∃ (d : ℕ) (x : ∀ n, Fin d → G.A n), (∀ n i, Coalgebra.counit (R := O) (x n i) = 0) ∧
      (∀ n i, G.res n (x (n + 1) i) = x n i) ∧
      (∀ n, Submodule.span O (Set.range fun i => PDiv.dUnit O (x n i)) = ⊤) ∧
      ∀ n, ∃ l : Fin d → (PDiv.Cot O (G.A n) →ₗ[O] O ⧸ Ideal.span {(p : O) ^ n}),
        ∀ i j, l i (PDiv.dUnit O (x n j)) = if i = j then 1 else 0 := by
  have : ValuationRing O := ValuationRing.of_integers v hv
  obtain ⟨h1, h2⟩ := omega_finite_projective p C v O hv G
  have : Module.Free O G.omega := Module.free_of_flat_of_isLocalRing
  let b := Module.finBasis O G.omega
  choose x hx0 hx1 hx2 using fun i => exists_compatible_dUnit_eq G (b i)
  refine ⟨_, fun n i => x i n, fun n i => hx0 i n, fun n i => hx1 i n, fun n => ?_, fun n => ?_⟩
  · have : (fun i => dUnit O (x i n)) = G.omegaLevel n ∘ b := funext fun i => hx2 i n
    rw [this, Set.range_comp, ← Submodule.map_span, b.span_eq, Submodule.map_top,
      LinearMap.range_eq_top.2 (G.omegaLevel_surjective n)]
  · have hker : ∀ i, LinearMap.ker (G.omegaLevel n) ≤
        LinearMap.ker ((Ideal.span {(p : O) ^ n}).mkQ ∘ₗ b.coord i) := fun i w hw => by
      obtain ⟨u, rfl⟩ := (G.omega_val_eq_zero_iff n w).1 hw
      rw [LinearMap.mem_ker, LinearMap.comp_apply, map_smul, Submodule.mkQ_apply,
        Submodule.Quotient.mk_eq_zero, smul_eq_mul]
      exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)
    refine ⟨fun i => ((LinearMap.ker (G.omegaLevel n)).liftQ _ (hker i)) ∘ₗ
      ((G.omegaLevel n).quotKerEquivOfSurjective (G.omegaLevel_surjective n)).symm.toLinearMap, fun i j => ?_⟩
    have h : ((G.omegaLevel n).quotKerEquivOfSurjective (G.omegaLevel_surjective n)).symm (dUnit O (x j n)) =
        Submodule.Quotient.mk (b j) := by
      rw [LinearEquiv.symm_apply_eq, hx2]
      rfl
    rw [LinearMap.comp_apply, LinearEquiv.coe_coe, h, Submodule.liftQ_apply, LinearMap.comp_apply,
      Module.Basis.coord_apply, b.repr_self, Finsupp.single_apply]
    by_cases hij : i = j
    · rw [if_pos hij, if_pos hij.symm]; rfl
    · rw [if_neg hij, if_neg (Ne.symm hij), map_zero]

end GlobalTheory.PDiv
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGeneratorRigidifiedLocallyTrivialStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_generator_rigidified_locally_trivial : ∀ (T : Scheme.{0}) (A' : Over T) [GrpObj A'] (N : LB A'.left), IsAbelianScheme A' → N.IsLB → Out.Rigidified A' N → (∀ τ : T, ∃ V : T.Opens, τ ∈ V ∧ ∃ s : (N.pull (A'.hom ⁻¹ᵁ V).ι).Gen, s.IsGen) → ∃ s : N.Gen, s.IsGen := by
  first | exact @GlobalTheory.RigTriv.exists_gen_of_locally_trivial | exact GlobalTheory.RigTriv.exists_gen_of_locally_trivial | (intros; apply GlobalTheory.RigTriv.exists_gen_of_locally_trivial <;> assumption)
end

