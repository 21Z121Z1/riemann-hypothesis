import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0622
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0013
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0011
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0100
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0039
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0016
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockDegreeGapBound
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemHeightOneIdealIffAdditiveValuationPos
import Development.AbelianVarietyTheory.Definitions.Divisors.DatumOfIsIntegersLattice
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.MulStableIntegral
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsDiscreteValuationRingValuationSubringAtPrime
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.AddMonoidHomEqZeroOfEventually
import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0774
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0736
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0019
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0020
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormalisedIsoPowerBundleRatioUnitEqOne
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Out
open GlobalTheory.HomFixMat GlobalTheory.HomFixUniq

noncomputable section

namespace GlobalTheory.HomFixUnit

theorem ratio_unit_eq_one : ∀ (Rg : Type) [CommRing Rg] (A B : Over (Sp Rg)) [GrpObj A] [GrpObj B] (L : LB A.left) (M : LB B.left) (k : ℕ) (eA : LB.Gen (L.pull (eSec A))) (eB : LB.Gen (M.pull (eSec B))), IsAbelianScheme A → L.IsLB → M.IsLB → ∀ (R : Type) [CommRing R] (t : Sp R ⟶ Sp Rg) (A' B' : Over (Sp R)) [GrpObj A'] [GrpObj B'] (φA' : A'.left ⟶ A.left) (φB' : B'.left ⟶ B.left) (Φ' : A' ⟶ B') (ψA : A'.left ⟶ (topS Rg ⊗ A).left) (ψB : B'.left ⟶ (topS Rg ⊗ B).left) (α α₂ : LB.Gen (isoLB (L := L) (M := M) k Φ' ψA ψB)) (v : Γ(A'.left, ⊤)ˣ), IsTest A B L M t A' B' φA' φB' Φ' → ψA ≫ (snd (topS Rg) A).left = φA' → ψB ≫ (snd (topS Rg) B).left = φB' → (∀ p, α.s p = res (le_top : (isoLB (L := L) (M := M) k Φ' ψA ψB).U p ≤ ⊤) v * α₂.s p) → RigEq L M k eA eB t Φ' ψA ψB α → RigEq L M k eA eB t Φ' ψA ψB α₂ → v = 1 := by
  intro Rg _ A B _ _ L M k eA eB hA hL hM R _ t A' B' _ _ φA' φB' Φ' ψA ψB α α₂ v hT hψA hψB hv hα hα₂
  have hA' : IsAbelianScheme A' := GlobalTheory.PolPull.isAbelianScheme_of_isGrpPullback hA hT.1
  refine Formalism.MainNotions.ModuliIntegralCharts.H1.ChartFrameTrA.unit_eq_one_of_eSec GlobalTheory.globalFns_holds A' hA' v ?_
  show (zeroPt A').appTop.hom v.val = 1
  let W : ((Fin 1 → M.ι) × (Fin 1 → L.ι)) → (Sp R).Opens := fun p =>
    (zeroPt A') ⁻¹ᵁ (isoLB (L := L) (M := M) k Φ' ψA ψB).U p ⊓
      t ⁻¹ᵁ LB.wchart L (fun _ : PUnit => eSec A) (fun _ => p.2 0) ⊓
      t ⁻¹ᵁ LB.wchart M (fun _ : PUnit => eSec B) (fun _ => p.1 0)
  have hloc : ∀ p, ((Sp R).presheaf.map (homOfLE (le_top : W p ≤ ⊤)).op).hom
      ((zeroPt A').appTop.hom v.val) = 1 := by
    intro p
    have h1 := hα p
    have h2 := hα₂ p
    rw [hv p, Units.val_mul, map_mul] at h1
    have hres : (Scheme.Hom.appLE (zeroPt A') ((isoLB (L := L) (M := M) k Φ' ψA ψB).U p) (W p)
        (inf_le_left.trans inf_le_left)).hom
          ((res (le_top : (isoLB (L := L) (M := M) k Φ' ψA ψB).U p ≤ ⊤) v : Γ(A'.left, (isoLB (L := L) (M := M) k Φ' ψA ψB).U p)ˣ) : Γ(A'.left, (isoLB (L := L) (M := M) k Φ' ψA ψB).U p)) =
        ((Sp R).presheaf.map (homOfLE (le_top : W p ≤ ⊤)).op).hom ((zeroPt A').appTop.hom v.val) := by
      show (A'.left.presheaf.map (homOfLE (le_top : (isoLB (L := L) (M := M) k Φ' ψA ψB).U p ≤ ⊤)).op ≫
        Scheme.Hom.appLE (zeroPt A') ((isoLB (L := L) (M := M) k Φ' ψA ψB).U p) (W p)
          (inf_le_left.trans inf_le_left)).hom v.val = _
      rw [Scheme.Hom.map_appLE]
      rfl
    rw [hres] at h1
    have key := h1.trans h2.symm
    rw [_root_.mul_assoc] at key
    exact (IsUnit.mul_left_inj (IsUnit.mul ((α₂.s p).isUnit.map _) (((eA.s _).isUnit.map _).pow k))).1
      (key.trans (_root_.one_mul _).symm)
  have hcov : (⊤ : (Sp R).Opens) ≤ iSup W := by
    rintro x -
    have hc : ∀ {X : Scheme.{0}} (N : LB X), N.IsLB → ∀ y : X, ∃ i, y ∈ N.U i := fun N hN y =>
      TopologicalSpace.Opens.mem_iSup.1 (by rw [hN.cover]; trivial)
    obtain ⟨iL, hiL⟩ := hc L hL ((eSec A) (t x))
    obtain ⟨iM, hiM⟩ := hc M hM ((eSec B) (t x))
    haveI := hT.2.2.1
    have eA' : zeroPt A' ≫ ψA ≫ (snd (topS Rg) A).left = t ≫ eSec A := by
      rw [hψA]; exact GlobalTheory.UU.eSec_comp_of_isGrpPullback hT.1
    have eB' : zeroPt A' ≫ (Φ'.left ≫ ψB) ≫ (snd (topS Rg) B).left = t ≫ eSec B := by
      have h0 : zeroPt A' ≫ Φ'.left = zeroPt B' := congrArg Over.Hom.left (IsMonHom.one_hom Φ')
      rw [Category.assoc, hψB, ← Category.assoc, h0]
      exact GlobalTheory.UU.eSec_comp_of_isGrpPullback hT.2.1
    refine TopologicalSpace.Opens.mem_iSup.2 ⟨(fun _ => iM, fun _ => iL), ?_⟩
    refine ⟨⟨⟨Set.mem_iInter.2 fun _ => ?_, Set.mem_iInter.2 fun _ => ?_⟩, Set.mem_iInter.2 fun _ => hiL⟩,
      Set.mem_iInter.2 fun _ => hiM⟩
    · show ((Φ'.left ≫ ψB) ≫ (snd (topS Rg) B).left) (zeroPt A' x) ∈ M.U iM
      rw [← Scheme.Hom.comp_apply, eB', Scheme.Hom.comp_apply]
      exact hiM
    · show (ψA ≫ (snd (topS Rg) A).left) (zeroPt A' x) ∈ L.U iL
      rw [← Scheme.Hom.comp_apply, eA', Scheme.Hom.comp_apply]
      exact hiL
  exact TopCat.Sheaf.eq_of_locally_eq' (Sp R).sheaf W ⊤ (fun p => homOfLE le_top) hcov _ 1
    (fun p => (hloc p).trans (map_one ((Sp R).presheaf.map (homOfLE le_top : W p ⟶ ⊤).op).hom).symm)

end GlobalTheory.HomFixUnit
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NotDvdTrace
section
open Formalism.BasicNotions Formalism.BasicNotions.DV Formalism.MainNotions Formalism.MainNotions.G NumberField GlobalTheory.IndefiniteRowSideFullHecke.LevelLossDegreeBounds

namespace GlobalTheory.LevelCoprime

open Formalism.FrobeniusOrbits

section Host

variable {R : Ranks} (H : Host R)

theorem phi_conj (φ : H.E →+* ℂ) (x : H.E) : φ (H.conj x) = starRingEnd ℂ (φ x) :=
  H.conjE_apply φ x

theorem conj_conj (x : H.E) : H.conj (H.conj x) = x := by
  apply H.φ₀.injective
  rw [phi_conj, phi_conj, Complex.conj_conj]

theorem sigma_conj (σ : H.E ≃ₐ[ℚ] H.E) (x : H.E) : σ (H.conj x) = H.conj (σ x) := by
  apply H.φ₀.injective
  have h1 := phi_conj H (H.φ₀.comp (σ : H.E →+* H.E)) x
  exact h1.trans (phi_conj H H.φ₀ (σ x)).symm

theorem b_sq : H.sqrtMinusD ^ 2 = -(H.d : H.E) := H.sqd_sq

theorem conj_b : H.conj H.sqrtMinusD = -H.sqrtMinusD := by
  apply H.φ₀.injective
  have h3 : H.φ₀ H.sqrtMinusD = Complex.I * (Real.sqrt H.d : ℂ) := H.φ₀_mem
  rw [phi_conj, map_neg, h3]
  simp

theorem agree_on_K (σ τ : H.E ≃ₐ[ℚ] H.E) (h : σ H.sqrtMinusD = τ H.sqrtMinusD) (x : H.E) (hx : x ∈ H.K) :
    σ x = τ x := by
  have hx' : x ∈ IntermediateField.adjoin ℚ {H.sqrtMinusD} := hx
  clear hx
  induction hx' using IntermediateField.adjoin_induction with
  | mem y hy => rw [Set.mem_singleton_iff.1 hy]; exact h
  | algebraMap r => simp
  | add a b _ _ ha hb => rw [map_add, map_add, ha, hb]
  | inv a _ ha => rw [map_inv₀, map_inv₀, ha]
  | mul a b _ _ ha hb => rw [map_mul, map_mul, ha, hb]

theorem trace_rat (x : H.E) (hx : x ∈ H.K) : ∃ r : ℚ, algebraMap ℚ H.E r = x + H.conj x := by
  haveI : IsGalois ℚ H.E := H.hostE_isGalois
  have hmem : x + H.conj x ∈ (⊥ : IntermediateField ℚ H.E) := by
    rw [← IsGalois.fixedField_top, IntermediateField.mem_fixedField_iff]
    intro σ _
    have hb : σ H.sqrtMinusD = H.sqrtMinusD ∨ σ H.sqrtMinusD = -H.sqrtMinusD := by
      apply sq_eq_sq_iff_eq_or_eq_neg.1
      rw [← map_pow, b_sq, map_neg, map_natCast]
    rw [map_add, sigma_conj]
    rcases hb with hb | hb
    · have := agree_on_K H σ 1 hb x hx
      rw [this]; rfl
    · have := agree_on_K H σ H.conj (hb.trans (conj_b H).symm) x hx
      rw [this, conj_conj, add_comm]
  exact IntermediateField.mem_bot.1 hmem

theorem trace_int (x : 𝓞 H.E) (hx : (x : H.E) ∈ H.K) : ∃ a : ℤ, (a : H.E) = x + H.conj x := by
  obtain ⟨r, hr⟩ := trace_rat H x hx
  have h1 : IsIntegral ℤ (H.conj (x : H.E)) :=
    IsIntegral.map (H.conj : H.E →+* H.E).toIntAlgHom x.isIntegral_coe
  have h2 : IsIntegral ℤ (algebraMap ℚ H.E r) := hr ▸ x.isIntegral_coe.add h1
  have h3 : IsIntegral ℤ r := (isIntegral_algebraMap_iff (algebraMap ℚ H.E).injective).1 h2
  obtain ⟨a, ha⟩ := IsIntegrallyClosed.algebraMap_eq_of_integral h3
  refine ⟨a, ?_⟩
  rw [← hr, ← ha]
  simp

theorem trace_sq_le (x : H.E) (a : ℤ) (T : ℕ) (ha : (a : H.E) = x + H.conj x) (hT : x * H.conj x = T) :
    a ^ 2 ≤ 4 * T := by
  have h1 := congrArg H.φ₀ ha
  have h2 := congrArg H.φ₀ hT
  rw [map_add, phi_conj, map_intCast, Complex.add_conj] at h1
  rw [map_mul, phi_conj, map_natCast, Complex.mul_conj, Complex.normSq_apply] at h2
  have h3 : (a : ℝ) = 2 * (H.φ₀ x).re := by exact_mod_cast h1
  have h4 : (H.φ₀ x).re * (H.φ₀ x).re + (H.φ₀ x).im * (H.φ₀ x).im = (T : ℝ) := by exact_mod_cast h2
  have h5 : (a : ℝ) ^ 2 ≤ 4 * T := by
    rw [h3, ← h4]
    nlinarith [mul_self_nonneg (H.φ₀ x).im]
  exact_mod_cast h5

end Host

theorem four_dvd {E : Type} [Field E] [NumberField E] (n : ℤ) (y : E) (hy : IsIntegral ℤ y)
    (h : (n : E) = 4 * y) : (4 : ℤ) ∣ n := by
  have h1 : y = algebraMap ℚ E ((n : ℚ) / 4) := by
    rw [map_div₀, map_intCast, h]
    simp
  rw [h1] at hy
  have h3 := (isIntegral_algebraMap_iff (algebraMap ℚ E).injective).1 hy
  obtain ⟨a, ha⟩ := IsIntegrallyClosed.algebraMap_eq_of_integral h3
  refine ⟨a, ?_⟩
  have h4 : (a : ℚ) = (n : ℚ) / 4 := by simpa using ha
  have h5 : (n : ℚ) = 4 * a := by rw [h4]; ring
  exact_mod_cast h5

theorem not_dvd_trace {D : D7} (X : ErrX D) (u : D.what₂.Word) (a : ℤ)
    (ha : (a : D.host.E) = X.piT u + D.host.conj (X.piT u)) : ¬ (((D.mem u).A.T : ℤ) ∣ a) := by
  intro hd
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton.1 (X.piT_cong u)
  have hdiv : ∃ b : 𝓞 D.host.E, X.piT u = 1 + 4 * b := by
    have h4 : (4 : ℕ) ∣ D.host.QS :=
      (show (4 : ℕ) ∣ 2 ^ (D.R.e + 2) from ⟨2 ^ D.R.e, by ring⟩).trans D.host.tower_dvd
    obtain ⟨k, hk⟩ := h4
    refine ⟨(k * D.host.q * D.host.d * (D.host.g 0 * D.host.g 1) ^ 2 : ℕ) * c, ?_⟩
    rw [hk] at hc
    push_cast at hc ⊢
    linear_combination hc
  obtain ⟨b, hb⟩ := hdiv
  have hn := X.piT_norm u
  have hle := trace_sq_le D.host _ a _ ha hn
  have hb' : ((X.piT u : 𝓞 D.host.E) : D.host.E) = 1 + 4 * (b : D.host.E) := by
    rw [hb]; simp [map_ofNat]
  have hbi : IsIntegral ℤ (D.host.conj (b : D.host.E)) :=
    IsIntegral.map (D.host.conj : D.host.E →+* D.host.E).toIntAlgHom b.isIntegral_coe
  have hb0 := b.isIntegral_coe
  rw [hb'] at ha hn
  simp only [map_add, map_mul, map_one, map_ofNat] at ha hn
  have h1 : (4 : ℤ) ∣ a - 2 := four_dvd _ _ (hb0.add hbi) (by push_cast; linear_combination ha)
  have h4 : IsIntegral ℤ (4 : D.host.E) := by
    simpa using (isIntegral_algebraMap (R := ℤ) (A := D.host.E) (x := 4))
  have h2 : (4 : ℤ) ∣ ((D.mem u).A.T : ℤ) - 1 :=
    four_dvd _ _ ((hb0.add hbi).add ((h4.mul hb0).mul hbi)) (by push_cast; linear_combination -hn)
  have h3 := (D.mem u).A.T_prime.two_le
  obtain ⟨k, rfl⟩ := hd
  set T : ℤ := ((D.mem u).A.T : ℤ) with hT
  have h5 : 5 ≤ T := by omega
  have hk : k ≠ 0 := by
    rintro rfl
    omega
  have hk2 : 1 ≤ k ^ 2 := by
    have := sq_pos_of_ne_zero hk
    omega
  nlinarith [mul_pow T k 2]

theorem coprime_conj {D : D7} (X : ErrX D) (u : D.what₂.Word) (w : D.what₂.places.Pl)
    (hw : D.what₂.places.resChar w = (D.mem u).A.T) :
    ¬ (0 < vAdd (D.plEq w) (D.embE (X.piT u : D.host.E)) ∧
      0 < vAdd (D.plEq w) (star (D.embE (X.piT u : D.host.E)))) := by
  rintro ⟨h1, h2⟩
  obtain ⟨a, ha⟩ := trace_int D.host (X.piT u) (X.piT_K u)
  have hp := (D.mem u).A.T_prime
  have hn := X.piT_norm u
  have hT0 : (((D.mem u).A.T : ℕ) : D.host.E) ≠ 0 := Nat.cast_ne_zero.2 hp.ne_zero
  rw [← hn] at hT0
  rw [← D.embE_conj] at h2
  have i1 : IsIntegral ℤ (D.embE (X.piT u : D.host.E)) :=
    IsIntegral.map D.embE.toIntAlgHom (X.piT u).isIntegral_coe
  have i2 : IsIntegral ℤ (D.embE (D.host.conj (X.piT u : D.host.E))) :=
    IsIntegral.map (D.embE.comp (D.host.conj : D.host.E →+* D.host.E)).toIntAlgHom (X.piT u).isIntegral_coe
  let y : 𝓞 D.what₂.LL := ⟨_, i1⟩
  let z : 𝓞 D.what₂.LL := ⟨_, i2⟩
  have hy : y ≠ 0 := fun h => (map_ne_zero D.embE).2 (left_ne_zero_of_mul hT0) (congrArg Subtype.val h)
  have hz : z ≠ 0 := fun h => (map_ne_zero D.embE).2 (right_ne_zero_of_mul hT0) (congrArg Subtype.val h)
  have m1 := (GlobalTheory.TypeLoss.mem_heightOneIdeal_iff_additiveValuation_pos (D.plEq w) y hy).2 h1
  have m2 := (GlobalTheory.TypeLoss.mem_heightOneIdeal_iff_additiveValuation_pos (D.plEq w) z hz).2 h2
  have e : ((a : ℤ) : 𝓞 D.what₂.LL) = y + z := by
    apply RingOfIntegers.coe_injective
    rw [map_intCast, map_add]
    change _ = D.embE _ + D.embE _
    rw [← map_add, ← ha, map_intCast]
  have m3 : ((a : ℤ) : 𝓞 D.what₂.LL) ∈ (D.plEq w).asIdeal := e ▸ Ideal.add_mem _ m1 m2
  have m4 : (((D.mem u).A.T : ℕ) : 𝓞 D.what₂.LL) ∈ (D.plEq w).asIdeal := hw ▸ resChar_mem D w
  have hc : IsCoprime (((D.mem u).A.T : ℕ) : ℤ) a :=
    (Nat.prime_iff_prime_int.1 hp).irreducible.coprime_iff_not_dvd.2 (not_dvd_trace X u a ha)
  obtain ⟨s, t, hst⟩ := hc
  apply (D.plEq w).isPrime.ne_top
  rw [Ideal.eq_top_iff_one]
  have h := congrArg (Int.cast : ℤ → 𝓞 D.what₂.LL) hst
  push_cast at h
  rw [← h]
  exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ m4) (Ideal.mul_mem_left _ _ m3)

end GlobalTheory.LevelCoprime
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NotMemHalfLatticeOfOddMultiplier
section
open NumberField IsDedekindDomain WeierstrassCurve GlobalTheory GlobalTheory.Published GlobalTheory.CMModel Formalism.L2.Th1.F
open scoped IntermediateField BigOperators Topology ComplexConjugate

namespace GlobalTheory.CMModel

theorem mem_lattice_of_even_kerReps :
    ∀ (L : PeriodPair) (α a : ℂ) (S : Finset ℂ), α ≠ 0 → MulStable L α → IsKerReps L α S →
      Even S.card → α * a ∈ L.lattice → 2 * a ∈ L.lattice → a ∈ L.lattice := by
  intro L α a S hα hst hS hev h1 h2
  obtain ⟨m, hm⟩ := hev
  have hc := kerRepsCard L α S hα hst hS
  obtain ⟨t, n, ht, -, -⟩ := mulStableIntegral L α hst
  have hN : α * conj α = 2 * (m : ℂ) + 1 := by
    rw [Complex.mul_conj, ← hc, hm]
    push_cast
    ring
  have key : a = t • (α * a) - α * (α * a) - m • (2 * a) := by
    rw [zsmul_eq_mul, nsmul_eq_mul, ← ht]
    linear_combination (-a) * hN
  rw [key]
  exact sub_mem (sub_mem (zsmul_mem h1 t) (hst _ h1)) (nsmul_mem h2 m)

end GlobalTheory.CMModel
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NuAbsPlaceFine
section
open Formalism.BasicNotions Formalism.BasicNotions.DV Formalism.MainNotions Formalism.MainNotions.G NumberField GlobalTheory.IndefiniteRowSideFullHecke.LevelLossDegreeBounds

namespace GlobalTheory.FockDegreeFine

open Classical GlobalTheory.FockDegreeGap

variable {D : D7} {L : SizeData₂ D}

noncomputable def topConst (D : D7) (c : ℝ) (τ : D.what₂.Tau) : ℝ :=
  ∑ t : D.host.TT, if (D.eTau τ : D.R.GG) = D.R.tau1 t then c else 0

theorem topConst_top (c : ℝ) {τ : D.what₂.Tau} {t : D.host.TT}
    (h : (D.eTau τ : D.R.GG) = D.R.tau1 t) : topConst D c τ = c := by
  unfold topConst
  rw [Finset.sum_eq_single t, if_pos h]
  · intro s _ hs
    exact if_neg fun h' => hs (Subtype.ext (tau1_injective (h'.symm.trans h)))
  · simp

theorem topConst_nonneg {c : ℝ} (hc : 0 ≤ c) (τ : D.what₂.Tau) : 0 ≤ topConst D c τ := by
  unfold topConst
  refine Finset.sum_nonneg fun t _ => ?_
  split_ifs
  · exact hc
  · exact le_rfl

theorem sum_topConst (c : ℝ) : ∑ τ, topConst D c τ = (D.host.TT.card : ℝ) * c := by
  unfold topConst
  rw [Finset.sum_comm]
  have : ∀ t ∈ (Finset.univ : Finset D.host.TT),
      (∑ τ : D.what₂.Tau, if (D.eTau τ : D.R.GG) = D.R.tau1 t then c else 0) = c := by
    intro t _
    rw [Finset.sum_eq_single (D.eTau.symm ⟨D.R.tau1 t, (Formalism.HC.Frame.mem_Psi_iff _).2 rfl⟩)]
    · simp
    · intro τ _ hτ
      refine if_neg fun h' => hτ ?_
      rw [Equiv.eq_symm_apply]
      exact Subtype.ext h'
    · simp
  rw [Finset.sum_congr rfl this]
  simp

noncomputable def offWt (D : D7) (j : ℕ) (τ : D.what₂.Tau) : ℝ :=
  if τ ∉ topsOf D.host D.eTau then wj D j τ else 0

theorem mem_topsOf (τ : D.what₂.Tau) :
    τ ∈ topsOf D.host D.eTau ↔ (D.eTau τ : D.R.GG) ∈ D.host.topPlaces := by
  unfold topsOf
  simp

theorem sum_offWt (j : ℕ) : ∑ τ, offWt D j τ = sizeOffTops D j := by
  unfold offWt sizeOffTops
  rw [Finset.sum_filter]

theorem end_rows (P : ParameterChoice' D L) (u : D.what₂.Word) (i : ℕ) (hi : i < D.R.m) (τ : D.what₂.Tau) :
    |nuRow D u (i + 1) τ 0 + nuRow D u (i + 1) τ (D.R.k - 1) - wj D (i + 1) τ -
        (topWt L τ + offWt D (i + 1) τ)| ≤
      4 * L.Sc + 2 * D.R.N D.R.m + 1 + L.etaSz + topConst D (L.sc.b' / L.sc.x) τ := by
  have hk : 5 ≤ D.R.k := by have := D.R.m_add_three_le_k; have := D.R.two_le_m; omega
  have hk0 : 0 < D.R.k := by omega
  have hS := L.Sc_pos
  have he := L.etaSz_pos
  have hNm : (0 : ℝ) ≤ D.R.N D.R.m := Nat.cast_nonneg _
  have hc : 0 ≤ L.sc.b' / L.sc.x :=
    div_nonneg (GlobalTheory.HCEntries.b'_pos L).le (by linarith [L.sc.one_lt_alt])
  obtain ⟨a1, a2⟩ := head_row u i hi τ 0 hk0
  obtain ⟨b1, b2⟩ := head_row u i hi τ (D.R.k - 1) (by omega)
  rw [D.hcW_first u τ hk0] at a1 a2
  rw [D.hcW_last u τ hk0] at b1 b2
  rw [abs_le]
  unfold offWt
  by_cases ha : (D.eTau τ : D.R.GG) ∈ D.host.topPlaces
  · obtain ⟨t, ht⟩ := GlobalTheory.HCEntries.exists_top ha
    rw [topWt_top L ht, topConst_top _ ht, if_neg (not_not.2 ((mem_topsOf τ).2 ha))]
    rw [(L.top_u τ t hk0 ht).1] at a1 a2
    rw [(L.top_u τ t hk0 ht).2] at b1 b2
    obtain ⟨c1, c2⟩ := L.win_top (i + 1) (by omega) hi τ t ht
    constructor <;> linarith
  · rw [topWt_off L ha, if_pos (fun h => ha ((mem_topsOf τ).1 h))]
    rw [P.uk_extreme τ (by omega) ha] at b1 b2
    have h0 := topConst_nonneg hc τ
    have h1 := P.cloud_place_bound τ (by omega) ha
    have h2 := L.cloud_v τ ⟨0, by omega⟩
    have h3 : (((D.hc τ).v ⟨0, by omega⟩ : ℚ) : ℝ) < (((D.hc τ).u ⟨0, hk0⟩ : ℚ) : ℝ) := by
      exact_mod_cast (D.hc τ).u_gt_v ⟨0, by omega⟩
    have h4 := L.cloud_v τ ⟨D.R.k - 2, by omega⟩
    push_cast at h1 b1 b2
    constructor <;> linarith [h2.1, h2.2, h4.1, h4.2]

theorem nuAbs_place_fine (P : ParameterChoice' D L) (u : D.what₂.Word) (i : ℕ) (hi : i < D.R.m) (τ : D.what₂.Tau) :
    |nuAbs D u (i + 1) τ - ((D.R.k : ℝ) - 1) * wj D (i + 1) τ - (topWt L τ + offWt D (i + 1) τ)| ≤
      D.R.k * (L.Sc + D.R.N D.R.m) + D.R.m * ((D.R.t : ℝ) + 1) * (2 * L.etaSz) +
        (4 * L.Sc + 2 * D.R.N D.R.m + 1 + L.etaSz + topConst D (L.sc.b' / L.sc.x) τ) := by
  obtain ⟨n, hn⟩ : ∃ n, D.R.k = n + 2 := ⟨D.R.k - 2, by have := D.R.m_add_three_le_k; omega⟩
  have hN : D.R.N (i + 1 - 1) = n + 1 + 1 + i * (D.R.t + 1) := by unfold Ranks.N; rw [hn]; rfl
  have hS := L.Sc_pos
  have he := L.etaSz_pos
  have hNm : (0 : ℝ) ≤ D.R.N D.R.m := Nat.cast_nonneg _
  have hkn : (D.R.k : ℝ) = n + 2 := by exact_mod_cast hn
  have s0 := abs_le.1 (end_rows P u i hi τ)
  rw [show D.R.k - 1 = n + 1 by omega] at s0
  unfold nuAbs
  rw [hN, Finset.sum_range_add, Finset.sum_range_succ, Finset.sum_range_succ']
  have hmid : ∀ r < n, |nuRow D u (i + 1) τ (r + 1) - wj D (i + 1) τ| ≤ L.Sc + D.R.N D.R.m := by
    intro r hr
    obtain ⟨a1, a2⟩ := head_row u i hi τ (r + 1) (by omega)
    obtain ⟨b1, b2⟩ := L.cloud_u u τ ⟨r + 1, by omega⟩ (by show 1 ≤ r + 1; omega) (by show r + 1 + 1 < D.R.k; omega)
    rw [abs_le]
    constructor <;> linarith
  have s1 := abs_le.1 (abs_sum_range_sub _ n _ _ hmid)
  have s2 := abs_le.1 (abs_sum_range_sub (fun r => nuRow D u (i + 1) τ (n + 1 + 1 + r)) (i * (D.R.t + 1)) 0 _
    (fun r hr => block_row L u i hi τ _ (by omega) (by unfold Ranks.N; omega)))
  have hi' : (i : ℝ) ≤ D.R.m := by exact_mod_cast hi.le
  have s8 : (i : ℝ) * ((D.R.t : ℝ) + 1) * (2 * L.etaSz) ≤ D.R.m * ((D.R.t : ℝ) + 1) * (2 * L.etaSz) := by gcongr
  push_cast at s2
  rw [mul_zero] at s2
  rw [hkn, abs_le]
  constructor <;> linarith [s0.1, s0.2, s1.1, s1.2, s2.1, s2.2]

theorem arith (k m t N S η : ℝ) (hm : 1 ≤ m) (hk : 1 ≤ k) (hkm : k + m ≤ N) (ht : 1 ≤ t) (hS : 0 ≤ S) (hη : 0 ≤ η) :
    k * (S + N) + m * (t + 1) * (2 * η) + (4 * S + 2 * N + 1 + η) + (k * (S + 2 * N) + 2 * m * (η + 2 * N)) ≤
      20 * (k * S + N ^ 2 + m * t * η) := by
  have h1 : S ≤ k * S := le_mul_of_one_le_left hS hk
  have h2 : k * N ≤ N * N := mul_le_mul_of_nonneg_right (by linarith) (by linarith)
  have h3 : m * N ≤ N * N := mul_le_mul_of_nonneg_right (by linarith) (by linarith)
  have h4 : N ≤ N * N := le_mul_of_one_le_left (by linarith) (by linarith)
  have h5 : η ≤ m * η := le_mul_of_one_le_left hη hm
  have h6 : m * η ≤ t * (m * η) := le_mul_of_one_le_left (by linarith) ht
  nlinarith

theorem degree_fine : ∀ {D : D7} (L : SizeData₂ D), SizesAt L → ParameterChoice' D L → KapDef D → 2 ≤ L.sc.x → ∀ (u : D.what₂.Word), ∀ j ∈ SizeData₂.lifts D, |degPi D u j - (fockDeg D j : ℝ) - (topSum L + sizeOffTops D j)| ≤ 20 * degErr L := by
  intro D L h P hK hx u j hj
  obtain ⟨j1, j2⟩ := Finset.mem_Icc.1 hj
  obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
  have hc : 0 ≤ L.sc.b' / L.sc.x :=
    div_nonneg (GlobalTheory.HCEntries.b'_pos L).le (by linarith [L.sc.one_lt_alt])
  have hm : (1 : ℝ) ≤ D.R.m := by exact_mod_cast (by have := D.R.two_le_m; omega : 1 ≤ D.R.m)
  have har := arith D.R.k D.R.m D.R.t (D.R.N D.R.m) L.Sc L.etaSz hm (GlobalTheory.HCEntries.one_le_k D) (ranks_le D).1
    L.t_win.1 L.Sc_pos.le L.etaSz_pos.le
  unfold degPi fockDeg topSum degErr Nm
  rw [← sum_topWt, ← sum_offWt, Int.cast_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib,
    ← Finset.sum_sub_distrib]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  refine (Finset.sum_le_sum (g := fun τ => 20 * ((D.R.k : ℝ) * L.Sc + (D.R.N D.R.m : ℝ) ^ 2 +
    (D.R.m : ℝ) * (D.R.t : ℝ) * L.etaSz) + topConst D (L.sc.b' / L.sc.x) τ) fun τ _ => ?_).trans ?_
  · obtain ⟨w0, -⟩ := GlobalTheory.HCEntries.wj_bounds h hx (i + 1) j1 j2 τ
    have a := abs_le.1 (nuAbs_place_fine P u i j2 τ)
    have b := abs_le.1 (letters_place L hK i j2 τ w0)
    rw [abs_le]
    constructor <;> linarith [a.1, a.2, b.1, b.2]
  · rw [Finset.sum_add_distrib, sum_topConst, Finset.sum_const, Finset.card_univ, D.what₂.card_Tau, nsmul_eq_mul,
      mul_div_assoc]
    have : 0 ≤ (D.host.TT.card : ℝ) * (L.sc.b' / L.sc.x) := mul_nonneg (Nat.cast_nonneg _) hc
    linarith

end GlobalTheory.FockDegreeFine
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PAdicEvaluationSubstCompatibleThickening
section
set_option autoImplicit false

noncomputable section

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

namespace GlobalTheory.QLog

theorem hasVal_subst : ∀ (p : ℕ) [Fact p.Prime] (B O Q : Type) [CommRing B] [CommRing Q] [CommRing O] [Algebra B Q] (θ : B →+* O), IsFrame p Q θ → ∀ (σ : Type) [Fintype σ] [DecidableEq σ] (z : σ → B), (∀ i, ∃ N : ℕ, (p : B) ∣ z i ^ N) → ∀ E : MvPowerSeries σ B →ₐ[B] B, IsEval p z E → ∀ (τ : Type) [Fintype τ] [DecidableEq τ] (u : τ → MvPowerSeries σ B) (f : MvPowerSeries τ Q) (q : Q), (∀ j, constantCoeff (u j) = 0) → DIn (⊤ : Ideal B) f → HasVal p (fun j => E (u j)) f q → HasVal p z (subst (up Q u) f) q := by
  intro p _ B O Q _ _ _ _ θ hF σ _ _ z hz E hE τ _ _ u f q hu hf hq
  intro m
  obtain ⟨M0, hM0⟩ := GlobalTheory.T.tail_subst_pAdically_small_of_integral_differential p B O Q θ hF σ z hz τ u f hu hf m
  obtain ⟨M1, hM1⟩ := hq m
  obtain ⟨g, hg⟩ : ∃ g : MvPolynomial τ Q, g = trunc' Q (Finsupp.equivFunOnFinite.symm fun _ => max M0 M1) f := ⟨_, rfl⟩
  obtain ⟨N2, hN2⟩ := GlobalTheory.T.hasVal_subst_polynomial_eval p B O Q θ hF σ z hz E hE τ u hu g m
  refine ⟨N2, fun N' hN' => ?_⟩
  obtain ⟨b1, hb1⟩ := hM1 (max M0 M1) (le_max_right _ _)
  obtain ⟨b2, hb2⟩ := hN2 N' hN'
  obtain ⟨b3, hb3⟩ := hM0 (max M0 M1) (le_max_left _ _) (Finsupp.equivFunOnFinite.symm fun _ => N')
  rw [← hg] at hb1 hb3
  have hs : HasSubst (up Q u) := hasSubst_of_constantCoeff_zero fun j => by
    simp [up, hu j]
  have hsplit : subst (up Q u) f = subst (up Q u) (g : MvPowerSeries τ Q) + subst (up Q u) (f - (g : MvPowerSeries τ Q)) := by
    rw [← subst_add hs]; congr 1; ring
  refine ⟨b1 + b2 - b3, ?_⟩
  rw [hsplit, map_add, map_add]
  simp only [map_mul, map_sub, map_add, map_pow, map_natCast] at hb1 hb2 hb3 ⊢
  linear_combination hb1 + hb2 - hb3

end GlobalTheory.QLog
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmallExtensionPrimitiveLiftStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.small_extension_primitive_lift : ∀ (R R' R₀ : Type) [CommRing R] [CommRing R'] [CommRing R₀] (t : R) (σ : R →+* R') (σ₀ : R →+* R₀) (g : ℕ) (A : Over (Sp R)) [GrpObj A] (A' : Over (Sp R')) [GrpObj A'] (A₀ : Over (Sp R₀)) [GrpObj A₀] (φ : A'.left ⟶ A.left) (φ₀ : A₀.left ⟶ A.left) (h : IsGrpPullback A' A (spMap σ) φ) (h₀ : IsGrpPullback A₀ A (spMap σ₀) φ₀), SmallExt t σ σ₀ → IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → StructureSheafH1Primitive A' → NoPrimitiveStructureSheafH2 A₀ → Function.Surjective (pullHO1 h.1.w) := by
  first | exact @GlobalTheory.AbCoh.pullHO1_surjective_of_smallExt | exact GlobalTheory.AbCoh.pullHO1_surjective_of_smallExt | (intros; apply GlobalTheory.AbCoh.pullHO1_surjective_of_smallExt <;> assumption)
end

