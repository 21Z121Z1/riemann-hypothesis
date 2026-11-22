import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0610
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0651
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0649
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0656
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0643
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsEqAddOfRedVEq
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0644
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0586
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0619
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0646
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0620
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0614
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0645
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChartWiden
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0021
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0404
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle0011
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0601
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0659
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ToroidalBoundaryMetricData
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0036
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NonzeroPlacesOverPrimes
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0041

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CellCoordinatesBaseChange
section
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory GlobalTheory.LocM GlobalTheory.LieMet GlobalTheory.DRFlag GlobalTheory.GrCl
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.FlagMod (ev tanPull initSpan)
open GlobalTheory.FlagEmb (plN plk lform LeftInv)
open GlobalTheory.ProjSpace (pt)

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.GrCl.CellGlue

theorem linearIndependent_of_leftInv {K : Type} [Field K] {m M : ℕ} {D c : Fin m → Fin M → K} (h : LeftInv D c) :
    LinearIndependent K c := by
  rw [Fintype.linearIndependent_iff]
  intro g hg z
  have e := congrArg (fun v : Fin M → K => ∑ r, D z r * v r) hg
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, mul_zero, Finset.sum_const_zero,
    Finset.mul_sum] at e
  rw [Finset.sum_comm] at e
  have key : ∀ i, ∑ r, D z r * (g i * c i r) = if z = i then g i else 0 := fun i => by
    have e1 : ∑ r, D z r * (g i * c i r) = g i * ∑ r, D z r * c i r := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun r _ => by ring
    rw [e1, h z i]
    split_ifs <;> simp
  simpa [key] using e

theorem span_comp_castLE {S : Type} [CommRing S] {Q : Type} [AddCommGroup Q] [Module S Q] {m k : ℕ} (hk : k ≤ m)
    (v : Fin m → Q) : Submodule.span S (Set.range (v ∘ Fin.castLE hk)) = initSpan S v k := by
  unfold initSpan
  congr 1
  ext y
  constructor
  · rintro ⟨l, rfl⟩
    exact ⟨Fin.castLE hk l, l.2, rfl⟩
  · rintro ⟨j, hj, rfl⟩
    exact ⟨⟨j, hj⟩, rfl⟩

theorem map_gell {S S' : Type} [CommRing S] [CommRing S'] (φ : S →+* S') {m a k b N : ℕ} (hk : k ≤ m)
    (D : Fin m → Fin (N + 1) → S) (w : GPm m a b) (q : Fin (plN N k + 1)) :
    φ (gell a b hk D w q) = gell a b hk (fun l => φ ∘ D l) w q := by
  simp only [gell, lform, map_prod, Function.comp_apply]

theorem comp_gxi {R K : Type} [CommRing R] [CommRing K] {m a k b N : ℕ} (hk : k ≤ m) (c : Fin m → Fin (N + 1) → R)
    (w : GPm m a b) (ψ : MvPolynomial (GVar m a k b) R →+* K) :
    ψ ∘ gxi a b hk c w =
      plk (gvec (fun l => (ψ.comp MvPolynomial.C) ∘ c l) w (ψ ∘ MvPolynomial.X) ∘ Fin.castLE hk) id := by
  unfold gxi
  rw [GlobalTheory.FlagEmb.map_plk]
  simp only [comp_gvec]
  rfl

theorem mem_cell_of_initSpan_eq : ∀ (K R R' : Type) [Field K] [CommRing R] [CommRing R'] (m a k b N : ℕ) (hk : k ≤ m)
    (D c : Fin m → Fin (N + 1) → R) (D' c' : Fin m → Fin (N + 1) → R') (φ : R →+* K)
    (ψ' : MvPolynomial (GVar m a k b) R' →+* K) (w' : GPm m a b), a ≤ k → k ≤ b → LeftInv D c → LeftInv D' c' →
    (∀ e : ℕ, e = a ∨ e = b →
      initSpan K (fun l => φ ∘ c l) e = initSpan K (fun l => (ψ'.comp MvPolynomial.C) ∘ c' l) e) →
    (∃ w : GPm m a b, ∑ q, φ (gell a b hk D w q) * ψ' (gxi a b hk c' w' q) ≠ 0) ∧
      ∀ w : GPm m a b, ∑ q, φ (gell a b hk D w q) * ψ' (gxi a b hk c' w' q) ≠ 0 →
        ∃ (ψ : MvPolynomial (GVar m a k b) R →+* K) (u : Kˣ),
          ψ.comp MvPolynomial.C = φ ∧ ψ' ∘ gxi a b hk c' w' = (u : K) • (ψ ∘ gxi a b hk c w) := by
  intro K R R' _ _ _ m a k b N hk D c D' c' φ ψ' w' hak hkb hDc hDc' hab
  have hcK : LinearIndependent K (fun l => φ ∘ c l) := linearIndependent_of_leftInv (hDc.map φ)
  have hcK' : LinearIndependent K (fun l => (ψ'.comp MvPolynomial.C) ∘ c' l) :=
    linearIndependent_of_leftInv (hDc'.map (ψ'.comp MvPolynomial.C))
  obtain ⟨hGi, -, hGe⟩ := GlobalTheory.T.grassmann_cell_span_preserved K m a k b (Fin (N + 1) → K) (fun l => (ψ'.comp MvPolynomial.C) ∘ c' l) w'
    (ψ' ∘ MvPolynomial.X) hak hkb
  have hUi := (hGi hcK').comp _ (Fin.castLE_injective hk)
  have hlo : initSpan K (fun l => φ ∘ c l) a ≤ Submodule.span K (Set.range
      (gvec (fun l => (ψ'.comp MvPolynomial.C) ∘ c' l) w' (ψ' ∘ MvPolynomial.X) ∘ Fin.castLE hk)) := by
    rw [hab a (Or.inl rfl), ← hGe a (Or.inl le_rfl), span_comp_castLE]
    exact GlobalTheory.FlagMod.initSpan_mono _ hak
  have hhi : Submodule.span K (Set.range
      (gvec (fun l => (ψ'.comp MvPolynomial.C) ∘ c' l) w' (ψ' ∘ MvPolynomial.X) ∘ Fin.castLE hk)) ≤
        initSpan K (fun l => φ ∘ c l) b := by
    rw [hab b (Or.inr rfl), ← hGe b (Or.inr le_rfl), span_comp_castLE]
    exact GlobalTheory.FlagMod.initSpan_mono _ hkb
  obtain ⟨hex, hcell⟩ := GlobalTheory.T.grassmann_cell_coordinates_exist K m a k b N hk (fun l => φ ∘ D l) (fun l => φ ∘ c l) _ hak hkb (hDc.map φ) hUi
    hlo hhi
  have hsum : ∀ w : GPm m a b, ∑ q, φ (gell a b hk D w q) * ψ' (gxi a b hk c' w' q) =
      ∑ q, gell a b hk (fun l => φ ∘ D l) w q *
        plk (gvec (fun l => (ψ'.comp MvPolynomial.C) ∘ c' l) w' (ψ' ∘ MvPolynomial.X) ∘ Fin.castLE hk) id q :=
    fun w => Finset.sum_congr rfl fun q _ => by rw [map_gell, ← comp_gxi]; rfl
  refine ⟨?_, fun w hw => ?_⟩
  · obtain ⟨w, hw⟩ := hex
    exact ⟨w, by rwa [hsum]⟩
  · rw [hsum] at hw
    obtain ⟨x, hx⟩ := hcell w hw
    have hC : (MvPolynomial.eval₂Hom φ x).comp MvPolynomial.C = φ := by
      ext r; simp
    have hX : MvPolynomial.eval₂Hom φ x ∘ MvPolynomial.X = x := by
      funext v; simp
    obtain ⟨hVi, -, -⟩ := GlobalTheory.T.grassmann_cell_span_preserved K m a k b (Fin (N + 1) → K) (fun l => φ ∘ c l) w x hak hkb
    have hVi' := (hVi hcK).comp _ (Fin.castLE_injective hk)
    obtain ⟨r, hr⟩ := ((GlobalTheory.T.plucker_nonzero_iff_independent K N k _ _).2 hVi').1 ⟨hUi, by rw [hx, span_comp_castLE]⟩
    refine ⟨MvPolynomial.eval₂Hom φ x, r, hC, ?_⟩
    rw [comp_gxi, comp_gxi, hC, hX]
    exact hr

end GlobalTheory.GrCl.CellGlue
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CellGeneratorMemConeOfSmulCombinationStatement
section
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cell_generator_mem_cone_of_smul_combination : ∀ {O : Type} [CommRing O] (bar : O → O) (φ : InvFun O) {X : Type} [AddCommGroup X] [Module O X]
    [Module.Finite O X] {m m' : ℕ} (δ : Fin m → LinearMap.BilinForm ℤ X) (γ : Fin m' → LinearMap.BilinForm ℤ X)
    (i : Fin m) (k : ℕ) (a : Fin m' → ℕ), IsCell bar φ δ → IsCell bar φ γ → 0 < k → k • δ i = ∑ j, a j • γ j →
    ∀ j, 0 < a j → ∃ (k' : ℕ) (b : Fin m → ℕ), 0 < k' ∧ k' • γ j = ∑ l, b l • δ l := by
  first | exact @GlobalTheory.PolFan.cell_gen_mem_cone_of_smul | exact GlobalTheory.PolFan.cell_gen_mem_cone_of_smul | (intros; apply GlobalTheory.PolFan.cell_gen_mem_cone_of_smul <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CellGeneratorsSmulMemOtherCellConeStatement
section
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cell_generators_smul_mem_other_cellCone : ∀ {O : Type} [CommRing O] (bar : O → O) (φ : InvFun O) {X : Type} [AddCommGroup X] [Module O X]
    [Module.Finite O X] {m m' : ℕ} (δ : Fin m → LinearMap.BilinForm ℤ X) (γ : Fin m' → LinearMap.BilinForm ℤ X)
    (c : Fin m' → ℝ), IsCell bar φ δ → IsCell bar φ γ → (∀ j, 0 ≤ c j) →
    ∑ i, toReal (δ i) = ∑ j, c j • toReal (γ j) →
    ∀ i, ∃ (k : ℕ) (a : Fin m' → ℕ), 0 < k ∧ k • δ i = ∑ j, a j • γ j := by
  first | exact @GlobalTheory.PolFan.exists_smul_eq_sum_of_sum_toReal_eq | exact GlobalTheory.PolFan.exists_smul_eq_sum_of_sum_toReal_eq | (intros; apply GlobalTheory.PolFan.exists_smul_eq_sum_of_sum_toReal_eq <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CellsOfChartsPolynomialStatement
section
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory GlobalTheory.LocM GlobalTheory.LieMet GlobalTheory.DRFlag GlobalTheory.GrCl
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.FlagMod (ev tanPull initSpan)
open GlobalTheory.FlagEmb (plN plk lform LeftInv)
open GlobalTheory.ProjSpace (pt)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cells_of_charts_polynomial : ∀ (O : Type) [CommRing O] [IsDedekindDomain O] [CharZero O] (Z : Scheme.{0}) (s : Z ⟶ Sp O), IsProjOver s → ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme Z → Flat s → ∀ (ch : Charts Z) (g : ∀ a, O →+* ch.R a) (V J : Type) [Finite V] [Finite J] (N : ℕ) (ξ : ∀ a, J → Fin (N + 1) → MvPolynomial V (ch.R a)) (ℓ : ∀ a, J → Fin (N + 1) → ch.R a), (∀ a, ch.χ a ≫ s = spMap (g a)) → (∀ a, Cells (MvPolynomial.C : ch.R a →+* MvPolynomial V (ch.R a)) (ξ a) (ℓ a)) → (∀ (K : Type) [Field K] (a a' : ch.ι) (φ : ch.R a →+* K) (j' : J) (ψ' : MvPolynomial V (ch.R a') →+* K), spMap φ ≫ ch.χ a = spMap (ψ'.comp MvPolynomial.C) ≫ ch.χ a' → ∃ (j : J) (ψ : MvPolynomial V (ch.R a) →+* K) (u : Kˣ), ψ.comp MvPolynomial.C = φ ∧ ψ' ∘ ξ a' j' = (u : K) • (ψ ∘ ξ a j)) → ∃ (Z' : Scheme.{0}) (f : Z' ⟶ Z) (q : Z' ⟶ PSpace O N) (κ : ∀ a, J → (Sp (MvPolynomial V (ch.R a)) ⟶ Z')), CellCl s ch g ξ f q κ := by
  first | exact @GlobalTheory.GrCl.exists_cellCl | exact GlobalTheory.GrCl.exists_cellCl | (intros; apply GlobalTheory.GrCl.exists_cellCl <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CharacterTrivialOnUnitTransvections
section
open ReciprocityTheory.ChartRestriction.G.FD NumberField GlobalTheory.UnipKill

namespace GlobalTheory.UnipKill

theorem gl_pow_mulVec {E : Type} [Field E] {N : ℕ} (g : GL (Fin N) E) (ξ : Fin N → E) (ε : E)
    (h : (g : Matrix (Fin N) (Fin N) E).mulVec ξ = ε • ξ) (k : ℕ) :
    ((g ^ k : GL (Fin N) E) : Matrix (Fin N) (Fin N) E).mulVec ξ = ε ^ k • ξ := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, Units.val_mul, ← Matrix.mulVec_mulVec, h, Matrix.mulVec_smul, ih, smul_smul,
      pow_succ']

theorem killsScaled : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (N : ℕ) (X : Data E N),
    1 < Module.finrank ℚ E / 2 → ∀ (φ : X.Γ →* Multiplicative ℝ) (ξ : Fin N → E), ξ ∈ X.Λ → ξ ≠ 0 →
    herm X.Gm ξ ξ = 0 → ∃ u : 𝓞 E, u ≠ 0 ∧ cc (u : E) = u ∧ ∀ t : E, cc t = t → IsIntegral ℤ t →
    ∀ γ : X.Γ, ((γ : GL (Fin N) E) : Matrix (Fin N) (Fin N) E) =
      transvMat X.Gm ξ (X.m * (u * t) * X.κ0) → φ γ = 1 := by
  intro E _ _ _ N X hdeg φ ξ hξ hξ0 hiso
  obtain ⟨η, d, hd, hη, hξη, hηη⟩ := GlobalTheory.T.exists_isotropic_dual_lattice_vector E N X ξ hξ hξ0 hiso
  obtain ⟨u0, hu0c, hu0⟩ := GlobalTheory.T.exists_real_unit_not_root_of_unity E hdeg
  have hM : ((d : 𝓞 E) * X.den) ≠ 0 :=
    mul_ne_zero (Nat.cast_ne_zero.2 hd.ne') X.den_ne
  obtain ⟨k1, hk1, c, hc⟩ := GlobalTheory.T.dvd_unit_pow_sub_one E u0 _ hM

  obtain ⟨v, hv⟩ : ∃ v : (𝓞 E)ˣ, v = u0 ^ k1 := ⟨_, rfl⟩
  rw [← hv] at hc
  obtain ⟨ε, hε⟩ : ∃ ε : E, ε = ((v : 𝓞 E) : E) := ⟨_, rfl⟩
  have hεpow : ε = ((u0 : 𝓞 E) : E) ^ k1 := by
    rw [hε, hv, Units.val_pow_eq_pow_val]; exact map_pow (algebraMap (𝓞 E) E) _ _
  have hεc : cc ε = ε := by rw [hεpow, cc_pow, hu0c]
  have hε0 : ε ≠ 0 := by
    rw [hε]; exact (v.isUnit.map (algebraMap (𝓞 E) E)).ne_zero
  have hεint : IsIntegral ℤ ε := by rw [hε]; exact RingOfIntegers.isIntegral_coe _
  have hεinv : IsIntegral ℤ ε⁻¹ := by
    have h1 : (((v⁻¹ : (𝓞 E)ˣ) : 𝓞 E) : E) * ε = 1 := by
      have := congrArg (algebraMap (𝓞 E) E) (Units.inv_mul v)
      rw [map_mul, map_one] at this
      rw [hε]; exact this
    rw [← eq_inv_of_mul_eq_one_left h1]
    exact RingOfIntegers.isIntegral_coe _
  have hε1 : ε - 1 = d * X.den * c := by
    have := congrArg (algebraMap (𝓞 E) E) hc
    rw [map_sub, map_one, map_mul, map_mul, map_natCast] at this
    rw [hε]; exact this
  obtain ⟨g, hgU, hgξ⟩ :=
    GlobalTheory.T.exists_unitary_stabilizer_scaling_isotropic E N X ξ η d ε c hd hξ hη hiso hηη hξη hεc hε0 hεint hεinv hε1
  obtain ⟨k2, hk2, hmem⟩ := GlobalTheory.T.pow_mem_arithmetic_subgroup_of_stabilizer E N X g hgU
  have hgmξ := gl_pow_mulVec g ξ ε hgξ k2
  have hgiso : IsIsom X.Gm ((g ^ k2 : GL (Fin N) E) : Matrix (Fin N) (Fin N) E) :=
    (X.Γ_stab _ hmem).1
  obtain ⟨θ, hθ⟩ : ∃ θ : E, θ = ε ^ k2 := ⟨_, rfl⟩
  rw [← hθ] at hgmξ
  have hθc : cc θ = θ := by rw [hθ, cc_pow, hεc]
  have hθ0 : θ ≠ 0 := by rw [hθ]; exact pow_ne_zero _ hε0
  have hθint : IsIntegral ℤ (θ ^ 2) := by rw [hθ]; exact (hεint.pow _).pow _
  have hθ2 : θ ^ 2 ≠ 1 := by
    have := hu0 (k1 * k2 * 2) (by positivity)
    rwa [pow_mul, pow_mul, ← hεpow, ← hθ] at this

  have hucoe : ((((v : 𝓞 E) ^ k2) ^ 2 - 1 : 𝓞 E) : E) = θ ^ 2 - 1 := by
    rw [hθ, hε]
    simp only [map_sub, map_pow, map_one]
  refine ⟨((v : 𝓞 E) ^ k2) ^ 2 - 1, ?_, ?_, ?_⟩
  · intro h0
    apply hθ2
    have : θ ^ 2 - 1 = 0 := by rw [← hucoe, h0]; exact map_zero (algebraMap (𝓞 E) E)
    exact sub_eq_zero.1 this
  · rw [hucoe, cc_sub, cc_pow, hθc, cc_one]
  intro t ht hti γ hγ
  rw [hucoe] at hγ
  obtain ⟨a, ha, hav⟩ := X.transv ξ hξ hiso t ht hti
  have hθt : cc (θ ^ 2 * t) = θ ^ 2 * t := by rw [cc_mul, cc_pow, hθc, ht]
  obtain ⟨b, hb, hbv⟩ := X.transv ξ hξ hiso (θ ^ 2 * t) hθt (hθint.mul hti)
  have eq1 : (⟨g ^ k2, hmem⟩ : X.Γ) * ⟨a, ha⟩ = ⟨b, hb⟩ * ⟨g ^ k2, hmem⟩ := by
    apply Subtype.ext
    apply Units.ext
    show ((g ^ k2 : GL (Fin N) E) : Matrix (Fin N) (Fin N) E) * (a : Matrix (Fin N) (Fin N) E) =
      (b : Matrix (Fin N) (Fin N) E) * ((g ^ k2 : GL (Fin N) E) : Matrix (Fin N) (Fin N) E)
    rw [hav, hbv, GlobalTheory.T.isometry_conj_transvection_scale E N X.Gm _ ξ θ hgiso hgmξ hθc hθ0]
    congr 2
    ring
  have eq2 : φ ⟨a, ha⟩ = φ ⟨b, hb⟩ := by
    have := congrArg φ eq1
    rw [map_mul, map_mul, mul_comm] at this
    exact mul_right_cancel this
  have eq3 : (⟨b, hb⟩ : X.Γ) = ⟨a, ha⟩ * γ := by
    apply Subtype.ext
    apply Units.ext
    show (b : Matrix (Fin N) (Fin N) E) =
      (a : Matrix (Fin N) (Fin N) E) * ((γ : GL (Fin N) E) : Matrix (Fin N) (Fin N) E)
    rw [hbv, hav, hγ, transvMat_mul_self X.Gm ξ hiso]
    congr 1
    ring
  have eq4 : φ ⟨a, ha⟩ * φ γ = φ ⟨a, ha⟩ := by rw [← map_mul, ← eq3, ← eq2]
  exact mul_eq_left.1 eq4

end GlobalTheory.UnipKill
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChartLocalGroupFiniteIndexAtFurtherPlaceStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
open scoped TensorProduct
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chartLocalGroup_finiteIndex_at_furtherPlace : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (Ch0 : B.Word → ℕ → Type) (chOf0 : ∀ u i, ((I.rec7 l Z).mem u).C.cls i → Ch0 u i) (F : ∀ u, FormsTiedSym (I.rec7 l Z) u (Ch0 u) (chOf0 u)) (u : B.Word) (a : I.ι) (Q : Finset (HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F))) (h1 : 1 ≤ B.R.m - 1) (Ch : Type) (_ : Finite Ch) (chOf : (I.stp u a (B.R.m - 1)).Cl → Ch) (K : ∀ β : Ch, LevelChart (I.rec7 l Z) (B.T u) (badQ (I.rec7 l Z) Q) (B.R.m - 1) (Nat.sub_le _ _) (fun c : {c // chOf c = β} => (I.chain l u a).stab (B.R.m - 1) c.1) (fun c => latCrd (I.rec7 l Z) (B.R.m - 1) (Nat.sub_le _ _) (I.latAt u a (B.R.m - 1) c.1))) (g : Ch → Ch0 u (B.R.m - 1)), (∀ v, v ∈ Q ↔ I.UnderQ a v) → (∀ u, I.StdF l Z u (F u)) → (∀ u j v h, (F u).glevJ.fr j v h = 1) → (∃ k : Ch → GA B (B.R.N (B.R.m - 1)), I.Reads u a (B.R.m - 1) chOf (fun β => (K β).lev.Lb) (fun β => (K β).lev.U) (fun β => (K β).lev.chi) (fun c => ((K (chOf c)).y ⟨c, rfl⟩).1) (fun c s => ((K (chOf c)).stabI ⟨c, rfl⟩ s).1) k ∧ ∀ β (v : HeightOneSpectrum (𝓞 B.host.F)), I.UnderQ a v → bc (prV (E := B.host.E) v) (k β) = 1) → (∀ β, ∀ v, v ∉ Q → (K β).lev.Uloc v = ((F u).ch (B.R.m - 1) h1 (succ_pred_m B.R) (g β)).lev.Uloc v) → (∀ β (κ : (K β).lev.U) (κ' : ((F u).ch (B.R.m - 1) h1 (succ_pred_m B.R) (g β)).lev.U), κ.1 = κ'.1 → (∀ v ∈ Q, bc (prV (E := (I.rec7 l Z).host.E) v) κ.1 = 1) → (K β).lev.chi κ = ((F u).ch (B.R.m - 1) h1 (succ_pred_m B.R) (g β)).lev.chi κ') → ∀ (Lb0 : Submodule (𝓞 (I.rec7 l Z).host.E) (Fin ((I.rec7 l Z).sp.X (B.R.m - 1)).rank → (I.rec7 l Z).host.E)), (F u).levJ.Lb = reL (rankN (I.rec7 l Z) (B.R.m - 1) (Nat.sub_le _ _)) Lb0 → ∀ β v, v ∈ Q → ((((K β).lev.Uloc v).comap (reGL (rankN (I.rec7 l Z) (B.R.m - 1) (Nat.sub_le _ _)) _).toMonoidHom).subgroupOf (⨆ β', ((K β').lev.Uloc v).comap (reGL (rankN (I.rec7 l Z) (B.R.m - 1) (Nat.sub_le _ _)) _).toMonoidHom)).FiniteIndex := by
  first | exact @GlobalTheory.Mem.Col2.FinAtQ.chartLoc_finiteIndex | exact GlobalTheory.Mem.Col2.FinAtQ.chartLoc_finiteIndex | (intros; apply GlobalTheory.Mem.Col2.FinAtQ.chartLoc_finiteIndex <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChartRingFormallyUnramified
section
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.TorRef

namespace GlobalTheory.GenFan

theorem formallyUnramified_residue_comp_of_isEtaleCompletion :
    ∀ (k : Type) [Field k] (m e : ℕ) [CharZero (ChartRing k m e)] {A : Type} [CommRing A] [IsLocalRing A]
      (φ : A →+* ChartRing k m e), IsEtaleCompletion φ → ((residue (ChartRing k m e)).comp φ).FormallyUnramified := by
  intro k _ m e _ A _ _ φ hφ
  obtain ⟨-, hmax, hfin⟩ := hφ
  haveI : IsLocalHom φ := by
    constructor
    intro a ha
    by_contra hna
    have h1 : a ∈ maximalIdeal A := (mem_maximalIdeal a).2 hna
    have h2 : φ a ∈ maximalIdeal (ChartRing k m e) := hmax ▸ Ideal.mem_map_of_mem φ h1
    exact (mem_maximalIdeal _).1 h2 ha
  rw [← ResidueField.map_comp_residue]
  refine RingHom.FormallyUnramified.comp (RingHom.FormallyUnramified.of_surjective residue_surjective) ?_
  have hfin' : (ResidueField.map φ).Finite := by
    rw [← ResidueField.map_comp_residue] at hfin
    exact RingHom.Finite.of_comp_finite hfin
  haveI : CharZero k := RingHom.charZero (algebraMap k (ChartRing k m e))
  haveI : CharZero (ResidueField (ChartRing k m e)) :=
    (RingHom.charZero_iff ((residue (ChartRing k m e)).comp (algebraMap k (ChartRing k m e))).injective).1 inferInstance
  haveI : CharZero (ResidueField A) := RingHom.charZero (ResidueField.map φ)
  letI := (ResidueField.map φ).toAlgebra
  haveI : Module.Finite (ResidueField A) (ResidueField (ChartRing k m e)) := hfin'
  haveI : Algebra.IsSeparable (ResidueField A) (ResidueField (ChartRing k m e)) := inferInstance
  exact Algebra.FormallyUnramified.of_isSeparable _ _

end GlobalTheory.GenFan
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CoefficientMapLevelCharacterEquivariantStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.Col2
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.coefficient_map_level_character_equivariant : ∀ (X : Stages) (px : PreX X.B.toPre) (I : Col2.ColIn X.B px) (hX : X.B.fields.Ok) (U : Set I.ι) (Xg : Finset (Gc X.B px → X.B.LL)) (tr : TrI X.B px) (L : Formalism.IndefR.Links.LevCh X.toD7 (TupU I U)) (eG : Gc X.B px ≃* G0 L.Pg X.toD7.R.r), I.Ok → ValsIn I → LevOf X I U L → IsPlacewiseIdentity X (px := px) eG → L.βX = 1 → ∀ (cX : CoefA X.toD7.sp.X') (c : VV X.B.fields.K X.B.wts.sgTrue →ₛₗ[X.B.embLL] cX.W), (∀ (γ : GQ X.toD7.sp.X') (γE : GL (Fin X.toD7.sp.X'.rank) X.toD7.host.E) (g : GL (Fin (X.B.R.N X.B.R.m - 1)) X.B.fields.E), Bridge.IsRatMat X.toD7.sp.X' γ γE → MatEq γE g → ∀ v, c (rhoV X.B.fields.emb X.B.wts.sgTrue g v) = cX.coef.ρ γ (c v)) → LinearIndependent ℂ (fun i => c (bVV X.B.fields.K X.B.wts.sgTrue i)) → Submodule.span ℂ (Set.range fun i => c (bVV X.B.fields.K X.B.wts.sgTrue i)) = ⊤ → (∀ x y, inner ℂ (c x) (c y) = X.B.embLL (pairV X.B.fields.emb X.B.wts.sgTrue 1 x y)) → ∀ t, ∃ P : Bridge.ClassPres (Bridge.ratF X.toD7.sp.X') ((famR X I hX U Xg tr).A.MtildeCSD t) X.toD7.what₂.embLL cX.coef.ρ (levEnv X.toD7.sp.X' L.βX (L.datXt t)).J (levEnv X.toD7.sp.X' L.βX (L.datXt t)).χ, (∀ x, P.coef x = c x) ∧ (∀ c', RowAd.decoAd X I t (P.y c') = (Formalism.L2.Col.mtildeKGSD (Pr := X.B.primes px) X.B.wts I.Ch I.sel t.1).outSec.rep c') ∧ ∀ (f : ((famR X I hX U Xg tr).A.MtildeCSD t).Forms) (h : Bridge.Gf X.toD7.sp.X'), P.ext (f : _ → _) h = c ((((Formalism.L2.Col.mtildeKGSD (Pr := X.B.primes px) X.B.wts I.Ch I.sel t.1).res (Formalism.L2.Col.mtildeKOk _ _ _ _ hX)).symm f).1 (RowAd.decoAd X I t h)) := by
  first | exact @GlobalTheory.Mem.R3.RowStdPres.exists_pres | exact GlobalTheory.Mem.R3.RowStdPres.exists_pres | (intros; apply GlobalTheory.Mem.R3.RowStdPres.exists_pres <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CompleteHolomorphicCoordinatesIndependentDiffere
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor GlobalTheory.ShFam.Hor.LogCh
open scoped Matrix CategoryTheory.Obj Topology
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section

namespace GlobalTheory.CompleteCoords

theorem exists_linearIndependent_extend {M : Type*} [AddCommGroup M] [Module ℂ M]
    [FiniteDimensional ℂ M] {a : ℕ} (ℓ : Fin a → M) (hℓ : LinearIndependent ℂ ℓ) :
    ∀ m : ℕ, a + m ≤ Module.finrank ℂ M → ∃ f : Fin (a + m) → M, LinearIndependent ℂ f ∧
      ∀ i : Fin a, f (Fin.castAdd m i) = ℓ i := by
  intro m
  induction m with
  | zero => intro _; exact ⟨ℓ, hℓ, fun i => rfl⟩
  | succ m ih =>
    intro h
    obtain ⟨f, hf, hfℓ⟩ := ih (by omega)
    obtain ⟨x, hx⟩ := exists_linearIndependent_snoc_of_lt_finrank hf (by omega)
    refine ⟨Fin.snoc f x, hx, fun i => ?_⟩
    have e : (Fin.castAdd (m + 1) i : Fin (a + (m + 1))) = Fin.castSucc (Fin.castAdd m i) := rfl
    rw [e, Fin.snoc_castSucc, hfℓ]

theorem complete_coords : ∀ (n a : ℕ) (v₀ : ReciprocityTheory.L2DbarEstimates.V n) (O : Set (ReciprocityTheory.L2DbarEstimates.V n)) (G : Fin a → ReciprocityTheory.L2DbarEstimates.V n → ℂ), IsOpen O → v₀ ∈ O → (∀ i, DifferentiableOn ℂ (G i) O) → (∀ i, G i v₀ = 0) → LinearIndependent ℂ (fun i => fderiv ℂ (G i) v₀) → ∃ ψ : OpenPartialHomeomorph (ReciprocityTheory.L2DbarEstimates.V n) (Fin n → ℂ), v₀ ∈ ψ.source ∧ ψ.source ⊆ O ∧ ψ v₀ = 0 ∧ DifferentiableOn ℂ ψ ψ.source ∧ DifferentiableOn ℂ ψ.symm ψ.target ∧ ∀ v ∈ ψ.source, ∀ (j : Fin n) (hj : (j : ℕ) < a), ψ v j = G ⟨j, hj⟩ v := by
  intro n a v₀ O G hO hv₀ hG hG0 hli
  classical
  set ℓ : Fin a → (ReciprocityTheory.L2DbarEstimates.V n →L[ℂ] ℂ) := fun i => fderiv ℂ (G i) v₀ with hℓdef
  have hfr : Module.finrank ℂ (ReciprocityTheory.L2DbarEstimates.V n →L[ℂ] ℂ) = n := by
    rw [← LinearEquiv.finrank_eq (LinearMap.toContinuousLinearMap), Module.finrank_linearMap,
      finrank_euclideanSpace_fin, Module.finrank_self, Nat.mul_one]
  have han : a ≤ n := by
    have := hli.fintype_card_le_finrank
    simpa [hfr] using this
  obtain ⟨f', hf', hf'ℓ⟩ := exists_linearIndependent_extend ℓ hli (n - a) (by rw [hfr]; omega)
  have hn : a + (n - a) = n := by omega
  set f : Fin n → (ReciprocityTheory.L2DbarEstimates.V n →L[ℂ] ℂ) := fun j => f' (Fin.cast hn.symm j) with hfdef
  have hf : LinearIndependent ℂ f := hf'.comp _ (Fin.cast_injective _)
  have hfa : ∀ (j : Fin n) (h : (j : ℕ) < a), f j = ℓ ⟨j, h⟩ := by
    intro j h
    have e : Fin.cast hn.symm j = Fin.castAdd (n - a) ⟨j, h⟩ := Fin.ext rfl
    simp only [hfdef, e, hf'ℓ]

  set Φ : ReciprocityTheory.L2DbarEstimates.V n → (Fin n → ℂ) :=
    fun v j => if h : (j : ℕ) < a then G ⟨j, h⟩ v else f j (v - v₀) with hΦ
  have hGan : ∀ i, ∀ x ∈ O, AnalyticAt ℂ (G i) x := fun i x hx =>
    ReciprocityTheory.ChartRestriction.G.AR.Up.DivLA.analyticAt_of_diffOn hO (hG i) hx
  have hΦan : ∀ x ∈ O, AnalyticAt ℂ Φ x := by
    intro x hx
    refine (analyticAt_pi_iff (f := fun j v => Φ v j)).2 fun j => ?_
    by_cases h : (j : ℕ) < a
    · simpa [hΦ, h] using hGan ⟨j, h⟩ x hx
    · simp only [hΦ, h, dite_false]
      exact ((f j).analyticAt _).comp (analyticAt_id.sub analyticAt_const)

  set D : ReciprocityTheory.L2DbarEstimates.V n →L[ℂ] (Fin n → ℂ) := ContinuousLinearMap.pi f with hD
  have hΦD : HasFDerivAt Φ D v₀ := by
    refine (hasFDerivAt_pi (φ := fun j v => Φ v j)).2 fun j => ?_
    by_cases h : (j : ℕ) < a
    · simp only [hΦ, h, dite_true]
      rw [hfa j h]
      exact ((hGan ⟨j, h⟩ v₀ hv₀).differentiableAt).hasFDerivAt
    · simp only [hΦ, h, dite_false]
      have e : (fun x => f j (x - v₀)) = fun x => f j x - f j v₀ := by
        funext x; simp [map_sub]
      rw [e]
      exact (f j).hasFDerivAt.sub_const _
  have hinj : Function.Injective D := by
    rw [injective_iff_map_eq_zero]
    intro v hv
    have hv' : ∀ j, f j v = 0 := fun j => by
      have := congrFun hv j
      simpa [hD] using this
    have hspan : Submodule.span ℂ (Set.range f) = ⊤ := by
      rcases Nat.eq_zero_or_pos n with h0 | hpos
      · subst h0
        exact Subsingleton.elim _ _
      · haveI : Nonempty (Fin n) := ⟨⟨0, hpos⟩⟩
        exact hf.span_eq_top_of_card_eq_finrank (by simp [hfr])
    have hall : ∀ φ : ReciprocityTheory.L2DbarEstimates.V n →L[ℂ] ℂ, φ v = 0 := by
      intro φ
      have hmem : φ ∈ Submodule.span ℂ (Set.range f) := hspan ▸ Submodule.mem_top
      refine Submodule.span_induction (p := fun φ _ => φ v = 0) ?_ ?_ ?_ ?_ hmem
      · rintro _ ⟨j, rfl⟩; exact hv' j
      · simp
      · intro x y _ _ hx hy; simp [hx, hy]
      · intro c x _ hx; simp [hx]
    by_contra hne
    obtain ⟨φ, hφ⟩ := SeparatingDual.exists_ne_zero (R := ℂ) hne
    exact hφ (hall φ)
  have hsurj : Function.Surjective D := by
    have := (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (f := (D : ReciprocityTheory.L2DbarEstimates.V n →ₗ[ℂ] (Fin n → ℂ)))
      (by simp [finrank_euclideanSpace_fin])).1 hinj
    exact this
  set e : ReciprocityTheory.L2DbarEstimates.V n ≃L[ℂ] (Fin n → ℂ) := ContinuousLinearEquiv.ofBijective D
    (LinearMap.ker_eq_bot.2 hinj) (LinearMap.range_eq_top.2 hsurj) with he
  have heD : (e : ReciprocityTheory.L2DbarEstimates.V n →L[ℂ] (Fin n → ℂ)) = D := by
    rw [he, ContinuousLinearEquiv.coe_ofBijective]
  have hs : HasStrictFDerivAt Φ (e : ReciprocityTheory.L2DbarEstimates.V n →L[ℂ] (Fin n → ℂ)) v₀ := by
    have h1 := ((hΦan v₀ hv₀).contDiffAt (n := 1)).hasStrictFDerivAt one_ne_zero
    rwa [hΦD.fderiv, ← heD] at h1

  have hΦC : ContDiffOn ℂ 1 Φ O := AnalyticOnNhd.contDiffOn (fun x hx => hΦan x hx) hO.uniqueDiffOn
  set W : Set (ReciprocityTheory.L2DbarEstimates.V n) :=
    O ∩ fderiv ℂ Φ ⁻¹' Set.range ContinuousLinearEquiv.toContinuousLinearMap with hW
  have hWo : IsOpen W :=
    (hΦC.continuousOn_fderiv_of_isOpen hO le_rfl).isOpen_inter_preimage hO
      ContinuousLinearEquiv.isOpen
  have hv₀W : v₀ ∈ W := ⟨hv₀, ⟨e, by rw [hΦD.fderiv, heD]⟩⟩
  refine ⟨(hs.toOpenPartialHomeomorph Φ).restrOpen W hWo, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [OpenPartialHomeomorph.restrOpen_source]
    exact ⟨hs.mem_toOpenPartialHomeomorph_source, hv₀W⟩
  · rw [OpenPartialHomeomorph.restrOpen_source]
    exact fun x hx => hx.2.1
  · show Φ v₀ = 0
    funext j
    by_cases h : (j : ℕ) < a
    · simp [hΦ, h, hG0]
    · simp [hΦ, h]
  · intro x hx
    rw [OpenPartialHomeomorph.restrOpen_source] at hx
    exact (hΦan x hx.2.1).differentiableAt.differentiableWithinAt
  · intro y hy
    set ψ := (hs.toOpenPartialHomeomorph Φ).restrOpen W hWo with hψ
    have hx : ψ.symm y ∈ ψ.source := ψ.map_target hy
    rw [hψ, OpenPartialHomeomorph.restrOpen_source] at hx
    obtain ⟨e', he'⟩ := hx.2.2
    have hd : HasFDerivAt (ψ : ReciprocityTheory.L2DbarEstimates.V n → (Fin n → ℂ))
        (e' : ReciprocityTheory.L2DbarEstimates.V n →L[ℂ] (Fin n → ℂ)) (ψ.symm y) := by
      have := (hΦan _ hx.2.1).differentiableAt.hasFDerivAt
      rw [← he'] at this
      exact this
    exact (ψ.hasFDerivAt_symm hy hd).differentiableAt.differentiableWithinAt
  · intro v _ j hj
    show Φ v j = _
    simp [hΦ, hj]

end GlobalTheory.CompleteCoords
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ComplexPointMemClosedIffFactorVanishes
section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor GlobalTheory.ShFam.Hor.LogCh
open scoped Matrix CategoryTheory.Obj Topology

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ShFam

theorem mem_iff_exists_ev_eq_zero_of_ideal_eq_span_prod : ∀ (k : Type) [CommRing k] (Y : Scheme.{0}) (p : Y ⟶ Sp k) (σ : k →+* ℂ) (D : TopologicalSpace.Closeds Y) (U : Y.affineOpens) (m : ℕ) (f : Fin m → Γ(Y, U.1)) (J : Finset (Fin m)), (Scheme.IdealSheafData.vanishingIdeal D).ideal U = Ideal.span {∏ i ∈ J, f i} → ∀ x : CxPts p σ, x ∈ CxPts.ptsIn p σ U.1 → (x.1 (IsLocalRing.closedPoint ℂ) ∈ D ↔ ∃ i ∈ J, CxPts.ev p σ U.1 (f i) x = 0) := by
  intro k _ Y p σ D U m f J h x hx
  have h1 := (ev_eq_zero_iff h hx).symm
  rw [LiesIn] at h1
  rw [h1, CxPts.ev_eq hx, map_prod, Finset.prod_eq_zero_iff]
  simp only [CxPts.ev_eq hx]

end GlobalTheory.ShFam
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ConjGeneratorsMemFramePrimesTrueColumnsStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Theta GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.AtMember
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.conjGenerators_mem_framePrimes_trueColumns : ∀ (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : Bl.ColW B f T) (Z : w.Lt) (t : Bl.ColT w Z), HalfAt (Formalism.L2.Herm.toErrXS t.full.1) (Fr.at (w.st Z) f) := by
  first | exact @GlobalTheory.AtMember.conj_gen_mem_frame | exact GlobalTheory.AtMember.conj_gen_mem_frame | (intros; apply GlobalTheory.AtMember.conj_gen_mem_frame <;> assumption)
end

