import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0013
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0011
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0006
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0283
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0014
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0019
import Development.AbelianVarietyTheory.Definitions.Divisors.OrthSubrepresentation
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0253
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0267
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0604
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0003
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0018
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.Bundle0002
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle0002
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0585
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0596
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0017
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0298
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0422
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0410

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorNormLeIffTensorNormBound
section
open MvPolynomial

noncomputable section

namespace GlobalTheory.TensorNormCompare

open Formalism.BasicNotions Formalism.L2.DIV GlobalTheory.IndefiniteRowSideFullHecke

variable {ι : Type} [Fintype ι] {n n' : ℕ}

theorem fockS_re_nonneg {σ : Type} (f : MvPolynomial σ ℂ) : 0 ≤ (fockS f f).re := by
  obtain ⟨r, hr, h⟩ := TensorPlaceNorm.fockS_self_nonneg f
  rw [h, Complex.ofReal_re]; exact hr

theorem fockS_re_pos' {σ : Type} {f : MvPolynomial σ ℂ} (hf : f ≠ 0) : 0 < (fockS f f).re := by
  have : (fockS f f).re = ∑ m ∈ f.support, ‖f.coeff m‖ ^ 2 * (mfact m : ℝ) := by
    have e : fockS f f = ((∑ m ∈ f.support, ‖f.coeff m‖ ^ 2 * (mfact m : ℝ) : ℝ) : ℂ) := by
      unfold fockS
      push_cast
      refine Finset.sum_congr rfl fun m _ => ?_
      rw [← Complex.conj_mul']
      rfl
    rw [e, Complex.ofReal_re]
  rw [this]
  refine Finset.sum_pos (fun m hm => mul_pos (pow_pos (norm_pos_iff.mpr (mem_support_iff.mp hm)) 2) ?_)
    (support_nonempty.mpr hf)
  exact_mod_cast Finset.prod_pos fun k _ => Nat.factorial_pos _

theorem fockS_conj_symm {σ : Type} (f g : MvPolynomial σ ℂ) : (starRingEnd ℂ) (fockS g f) = fockS f g := by
  classical
  rw [fockS_eq_sum g f (f.support ∪ g.support) Finset.subset_union_right,
    fockS_eq_sum f g (f.support ∪ g.support) Finset.subset_union_left, map_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  simp only [map_mul, map_natCast, Complex.star_def, Complex.conj_conj]
  ring

def fockCore (σ : Type) : InnerProductSpace.Core ℂ (MvPolynomial σ ℂ) where
  inner f g := fockS f g
  conj_inner_symm f g := fockS_conj_symm f g
  re_inner_nonneg f := fockS_re_nonneg f
  add_left f f' g := by
    change fockL (f + f') g = fockL f g + fockL f' g
    rw [map_add, LinearMap.add_apply]
  smul_left f g r := by
    change fockL (r • f) g = _ * fockL f g
    rw [LinearMap.map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul]
  definite f h := by
    by_contra hf
    have h' : fockS f f = 0 := h
    have := fockS_re_pos' hf
    rw [h'] at this
    simp at this

theorem exists_norm_bound {E F : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [NormedAddCommGroup F]
    [InnerProductSpace ℂ F] (S : Submodule ℂ E) [FiniteDimensional ℂ S] (A : S →ₗ[ℂ] F) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ f : S, (inner ℂ (A f) (A f)).re ≤ C * (inner ℂ f.1 f.1).re := by
  let B := LinearMap.toContinuousLinearMap A
  refine ⟨‖B‖ ^ 2, by positivity, fun f => ?_⟩
  have h1 : (inner ℂ (A f) (A f)).re = ‖A f‖ ^ 2 := inner_self_eq_norm_sq (𝕜 := ℂ) (A f)
  have h2 : (inner ℂ f.1 f.1).re = ‖f.1‖ ^ 2 := inner_self_eq_norm_sq (𝕜 := ℂ) f.1
  have h3 : ‖A f‖ ≤ ‖B‖ * ‖f.1‖ := B.le_opNorm f
  rw [h1, h2, ← mul_pow]
  exact pow_le_pow_left₀ (norm_nonneg _) h3 2

theorem exists_fock_bound {σ σ' : Type} (S : Submodule ℂ (MvPolynomial σ ℂ)) [FiniteDimensional ℂ S]
    (A : S →ₗ[ℂ] MvPolynomial σ' ℂ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ f : S, (fockS (A f) (A f)).re ≤ C * (fockS f.1 f.1).re := by
  exact @exists_norm_bound _ _ (fockCore σ).toNormedAddCommGroup (InnerProductSpace.ofCore (fockCore σ).toCore)
    (fockCore σ').toNormedAddCommGroup (InnerProductSpace.ofCore (fockCore σ').toCore) S ‹_› A

theorem finiteDimensional_nablaSq (lam : DomWeight n) : FiniteDimensional ℂ (nablaSq ℂ n lam) := by
  obtain ⟨b, ⟨-, hb, -⟩, -⟩ := Formalism.GradedWeylDivisibility.sSBasis ℂ n n lam.natW
  have : Finite (Formalism.GradedWeylDivisibility.ssIdx n n lam.natW) := (Formalism.GradedWeylDivisibility.sSIdxFinite n n _).to_subtype
  unfold nablaSq
  rw [← hb]
  exact FiniteDimensional.span_of_finite ℂ (Set.finite_range b)

theorem extremal_fock_pos (lam : DomWeight n) : 0 < (fockS (extremal ℂ n lam) (extremal ℂ n lam)).re :=
  fockS_re_pos' (Formalism.GradedWeylDivisibility.hwNe ℂ n n le_rfl lam.natW)

end GlobalTheory.TensorNormCompare
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TiltLiftOfRingAutomorphism
section
open GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps GlobalTheory.DetInv Matrix TensorProduct

noncomputable section
namespace GlobalTheory.DetInv

theorem span_p_map_ringEquiv (p : ℕ) {O : Type} [CommRing O] (γ : O ≃+* O) :
    Ideal.span {(p : O)} = Ideal.map (γ : O →+* O) (Ideal.span {(p : O)}) := by
  rw [Ideal.map_span, Set.image_singleton]
  simp

def modPEquiv (p : ℕ) {O : Type} [CommRing O] (γ : O ≃+* O) : ModP O p ≃+* ModP O p :=
  Ideal.quotientEquiv _ _ γ (span_p_map_ringEquiv p γ)

def perfectionEquiv (p : ℕ) [Fact p.Prime] {R : Type} [CommRing R] [CharP R p] (e : R ≃+* R) :
    Perfection R p ≃+* Perfection R p :=
  RingEquiv.ofRingHom (Perfection.map p (e : R →+* R)) (Perfection.map p (e.symm : R →+* R))
    (RingHom.ext fun x => Perfection.ext (R := R) (p := p) fun n => by simp [Perfection.coeff_map])
    (RingHom.ext fun x => Perfection.ext (R := R) (p := p) fun n => by simp [Perfection.coeff_map])

theorem perfectionEquiv_coeff (p : ℕ) [Fact p.Prime] {R : Type} [CommRing R] [CharP R p]
    (e : R ≃+* R) (x : Perfection R p) (n : ℕ) :
    Perfection.coeff R p n (perfectionEquiv p e x) = e (Perfection.coeff R p n x) :=
  Perfection.coeff_map p (e : R →+* R) x n

def tiltEquiv (p : ℕ) [Fact p.Prime] {O : Type} [CommRing O] [Fact ¬IsUnit (p : O)]
    (γ : O ≃+* O) : PreTilt O p ≃+* PreTilt O p :=
  perfectionEquiv p (modPEquiv p γ)

theorem tiltEquiv_coeff (p : ℕ) [Fact p.Prime] {O : Type} [CommRing O] [Fact ¬IsUnit (p : O)]
    (γ : O ≃+* O) (x : PreTilt O p) (n : ℕ) (y : O)
    (hy : PreTilt.coeff n x = Ideal.Quotient.mk (Ideal.span {(p : O)}) y) :
    PreTilt.coeff n (tiltEquiv p γ x) = Ideal.Quotient.mk (Ideal.span {(p : O)}) (γ y) := by
  have : PreTilt.coeff n (tiltEquiv p γ x) = modPEquiv p γ (PreTilt.coeff n x) :=
    perfectionEquiv_coeff p (modPEquiv p γ) x n
  rw [this, hy]
  exact Ideal.quotientEquiv_mk _ _ γ _ y

theorem ringEquiv_tilt_theta : ∀ (p : ℕ) [Fact p.Prime] (O : Type) [CommRing O] [Fact ¬IsUnit (p : O)]
    [IsAdicComplete (Ideal.span {(p : O)}) O] (γ : O ≃+* O), ∃ Γ : PreTilt O p ≃+* PreTilt O p,
    (∀ x, (Γ x).untilt = γ x.untilt) ∧ ∀ a : Ainf p O, WittVector.fontaineTheta O p
      (WittVector.map (Γ : PreTilt O p →+* PreTilt O p) a) = γ (WittVector.fontaineTheta O p a) := by
  intro p _ O _ _ _ γ
  refine ⟨tiltEquiv p γ, fun x => ?_, fun a => ?_⟩
  · exact GlobalTheory.Per.untilt_natural (γ : O →+* O) (tiltEquiv p γ : PreTilt O p →+* PreTilt O p)
      (fun x n y hy => tiltEquiv_coeff p γ x n y hy) x
  · exact GlobalTheory.Per.fontaineTheta_natural (γ : O →+* O) (tiltEquiv p γ : PreTilt O p →+* PreTilt O p)
      (fun x n y hy => tiltEquiv_coeff p γ x n y hy) a

end GlobalTheory.DetInv
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusPointOverFractionField
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.UPel.HT.EtLev

namespace GlobalTheory

theorem exists_compatible_primitive_prime_pow_roots :
    ∀ (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [IsAlgClosed k] [CharZero k],
      ∃ ζ : ℕ → kˣ, (∀ r, IsPrimitiveRoot (ζ r) (p ^ r)) ∧ ∀ r, ζ (r + 1) ^ p = ζ r := by
  intro p hp k _ _ _
  have hp' : p.Prime := hp.out

  have hroot : ∀ u : kˣ, ∃ v : kˣ, v ^ p = u := by
    intro u
    obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq (u : k) hp'.pos
    have hz0 : z ≠ 0 := by
      rintro rfl
      rw [zero_pow hp'.ne_zero] at hz
      exact u.ne_zero hz.symm
    exact ⟨Units.mk0 z hz0, Units.ext (by simpa using hz)⟩
  choose f hf using hroot

  haveI : NeZero (p : k) := ⟨by exact_mod_cast hp'.ne_zero⟩
  obtain ⟨z₁, hz₁⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot k p
  have hz₁0 : z₁ ≠ 0 := hz₁.ne_zero hp'.ne_zero
  have hu₁ : IsPrimitiveRoot (Units.mk0 z₁ hz₁0) p := by
    rw [← IsPrimitiveRoot.coe_units_iff]; simpa using hz₁

  have step : ∀ (n : ℕ) (x : kˣ), IsPrimitiveRoot (x ^ p) (p ^ (n + 1)) →
      IsPrimitiveRoot x (p ^ (n + 2)) := by
    intro n x hx
    rw [IsPrimitiveRoot.iff_orderOf] at hx ⊢
    have hdvd : orderOf x ∣ p ^ (n + 2) := by
      apply orderOf_dvd_of_pow_eq_one
      rw [pow_succ', pow_mul, ← hx, pow_orderOf_eq_one]
    obtain ⟨i, hi, hio⟩ := (Nat.dvd_prime_pow hp').1 hdvd
    rcases Nat.lt_or_ge i (n + 2) with h | h
    · exfalso
      have h1 : (x ^ p) ^ (p ^ n) = 1 := by
        rw [← pow_mul, ← pow_succ', ← orderOf_dvd_iff_pow_eq_one, hio]
        exact Nat.pow_dvd_pow p (by omega)
      have h2 := orderOf_dvd_of_pow_eq_one h1
      rw [hx] at h2
      have := Nat.le_of_dvd (pow_pos hp'.pos n) h2
      have h3 : p ^ n < p ^ (n + 1) := Nat.pow_lt_pow_right hp'.one_lt (by omega)
      omega
    · rw [hio, le_antisymm hi h]
  let g : ℕ → kˣ := fun n => Nat.rec (Units.mk0 z₁ hz₁0) (fun _ u => f u) n
  have g0 : g 0 = Units.mk0 z₁ hz₁0 := rfl
  have gs : ∀ n, g (n + 1) = f (g n) := fun n => rfl
  have gprim : ∀ n, IsPrimitiveRoot (g n) (p ^ (n + 1)) := by
    intro n
    induction n with
    | zero => simpa [g0] using hu₁
    | succ n ih =>
      apply step
      rw [gs, hf]; exact ih
  refine ⟨fun r => match r with | 0 => 1 | r + 1 => g r, ?_, ?_⟩
  · intro r
    cases r with
    | zero => simpa using IsPrimitiveRoot.one
    | succ r => exact gprim r
  · intro r
    cases r with
    | zero => show g 0 ^ p = 1; simpa using (gprim 0).pow_eq_one
    | succ r => show g (r + 1) ^ p = g r; rw [gs, hf]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedHarishChandraIsotypicPart
section
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical

noncomputable section

namespace GlobalTheory.Shin.HcIso

theorem kills_hcTw : ∀ (F : Type) [Field F] [Finite F], ∀ (t : F →+* F) (a b n : ℕ), n = a + b →
    ∀ (α A : GL (Fin a) F → ℂ) (β B : GL (Fin b) F → ℂ), IsChar ℂ ℂ A → IsChar ℂ ℂ B → Kills α A →
      Kills β B → Kills (hcTw t a b α β n) (hc a b A B n) := by
  intro F _ _ t a b n hn α A β B hA hB hαA hβB
  obtain ⟨H, π, hmem, hsurj, hπ, -, -⟩ := GlobalTheory.T.exists_blockParabolic_subgroup_levi_projection F a b n hn
  have hcard : (Nat.card {p : GL (Fin n) F // InPar a p} : ℂ) = (Nat.card H : ℂ) := by
    congr 1
    exact Nat.card_congr (Equiv.subtypeEquivRight fun x => (hmem x).symm)
  have hE : ∀ (α : GL (Fin a) F → ℂ) (β : GL (Fin b) F → ℂ) (z : GL (Fin n) F),
      (if InPar a z then α (tlG a z) * β (brG a b z) else 0) =
        ext0 H (fun p => α (π p).1 * β (π p).2) z := by
    intro α β z
    unfold ext0
    by_cases h : InPar a z
    · have hz : z ∈ H := (hmem z).2 h
      rw [if_pos h, dif_pos hz]
      show _ = α (π ⟨z, hz⟩).1 * β (π ⟨z, hz⟩).2
      rw [hπ]
    · have hz : z ∉ H := fun hz => h ((hmem z).1 hz)
      rw [if_neg h, dif_neg hz]
  have h1 : hcTw t a b α β n = fun x => (Nat.card H : ℂ)⁻¹ *
      ∑ᶠ y : GL (Fin n) F, ext0 H (fun p => α (π p).1 * β (π p).2) (y⁻¹ * x * (fun y => gal t n y) y) := by
    funext x
    unfold hcTw
    rw [hcard]
    congr 1
    congr 1
    funext y
    exact hE α β _
  have hid : ∀ y : GL (Fin n) F, gal (RingHom.id F) n y = y := by
    intro y
    ext i j
    simp [gal]
  have h2 : hc a b A B n = ind H (fun p => A (π p).1 * B (π p).2) := by
    funext x
    unfold hc hcTw ind
    rw [hcard]
    congr 1
    congr 1
    funext y
    rw [hid, hE]
  have hk := GlobalTheory.T.isotypicPart_exteriorProduct_inflated_surjection H (GL (Fin a) F) (GL (Fin b) F) π hsurj α A β B hA hB hαA hβB
  rw [h1, h2]
  exact GlobalTheory.T.isInCharacterIsotypicPart_twistedInduction (GL (Fin n) F) H (fun y => gal t n y) _ _ hk

end GlobalTheory.Shin.HcIso
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValuationBoundMultiplierSqrtNegD
section
open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate
open NumberField GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.LatVal ReciprocityTheory.ChartRestriction.L1 Formalism.L2.Th1.F
open GlobalTheory.CMVal GlobalTheory.HeckeGal
open ModularForm (E₄ E₆)

namespace GlobalTheory.SzMult

theorem main : ∀ (l : ℕ) [Fact l.Prime] (lam : algebraicClosure ℚ ℂ →+* ℂ_[l]) (d : ℕ) (σ p : ℂ), d.Prime → 4 < d → l ≠ d → Sz l lam 0 (12 * p) → Sz l lam 0 (-2 * (d : ℂ) * σ + ((d : ℂ) + 1) * p) → (l = 3 → d % 3 = 2) → Sz l lam (if l = 2 then (if d % 4 = 3 then 1 else 2) else 0) σ := by
  intro l _ lam d σ p hd hd4 hld hA hB h3
  have hlp : l.Prime := Fact.out
  obtain ⟨hint, -, hmul, hmono, -, hl, -⟩ := GlobalTheory.T.algebraicValuationAtLeast_basic_properties l lam
  obtain ⟨-, hadd2, -, -, hZ, -⟩ := GlobalTheory.QFam.SzSum.sz_ring l lam
  have hne : ∀ n : ℕ, ¬ l ∣ n → (n : ℂ) ≠ 0 := by
    intro n hn h
    apply hn
    rw [Nat.cast_eq_zero.mp h]
    exact dvd_zero l
  have hinv : ∀ n : ℕ, ¬ l ∣ n → Sz l lam 0 ((n : ℂ)⁻¹) := by
    intro n hn
    apply hint n _ hn
    rw [mul_inv_cancel₀ (hne n hn)]
    exact isIntegral_one
  have hnat : ∀ n : ℕ, Sz l lam 0 (n : ℂ) := fun n => by exact_mod_cast hZ n
  have hm0 : ∀ (r : ℝ) (x y : ℂ), Sz l lam 0 x → Sz l lam r y → Sz l lam r (x * y) := by
    intro r x y hx hy
    simpa using hmul 0 r x y hx hy
  have hcancel : ∀ (r : ℝ) (n : ℕ) (x : ℂ), ¬ l ∣ n → Sz l lam r ((n : ℂ) * x) → Sz l lam r x := by
    intro r n x hn h
    have := hm0 r _ _ (hinv n hn) h
    rwa [← mul_assoc, inv_mul_cancel₀ (hne n hn), one_mul] at this
  have hkey : ∀ r : ℝ, 0 ≤ r → Sz l lam r (((d : ℂ) + 1) * p) → Sz l lam r (((2 * d : ℕ) : ℂ) * σ) := by
    intro r hr h
    have hB' := hmono 0 r _ hr hB
    have := (hadd2 r _ _ h hB').2
    convert this using 1
    push_cast
    ring
  have hmulk : ∀ (r : ℝ) (m k : ℕ), d + 1 = m * k → Sz l lam r ((m : ℂ) * p) → Sz l lam r (((d : ℂ) + 1) * p) := by
    intro r m k hk h
    have := hm0 r (k : ℂ) _ (hnat k) h
    have e : ((d : ℂ) + 1) = (m : ℂ) * k := by exact_mod_cast hk
    rw [e]
    convert this using 1
    ring
  by_cases h2 : l = 2
  · subst h2
    have hd2 : ¬ 2 ∣ d := by
      intro h
      have := (Nat.prime_dvd_prime_iff_eq Nat.prime_two hd).mp h
      omega
    have h4p : Sz 2 lam 0 (((4 : ℕ) : ℂ) * p) := by
      apply hcancel 0 3 _ (by norm_num)
      convert hA using 1
      push_cast
      ring
    rw [if_pos rfl]
    split_ifs with h43
    · obtain ⟨k, hk⟩ : 4 ∣ d + 1 := by omega
      have h1 := hkey 0 le_rfl (hmulk 0 4 k hk h4p)
      have h2s : Sz 2 lam 0 (((2 : ℕ) : ℂ) * σ) := by
        apply hcancel 0 d _ hd2
        convert h1 using 1
        push_cast
        ring
      have := (hl 0 σ).mp h2s
      norm_num at this
      exact this
    · have h2p : Sz 2 lam 1 (((2 : ℕ) : ℂ) * p) := by
        have := (hl 0 (((2 : ℕ) : ℂ) * p)).mp (by convert h4p using 1; push_cast; ring)
        norm_num at this ⊢
        exact this
      obtain ⟨k, hk⟩ : 2 ∣ d + 1 := by omega
      have h1 := hkey 1 zero_le_one (hmulk 1 2 k hk h2p)
      have h2s : Sz 2 lam 1 (((2 : ℕ) : ℂ) * σ) := by
        apply hcancel 1 d _ hd2
        convert h1 using 1
        push_cast
        ring
      have := (hl 1 σ).mp h2s
      norm_num at this
      exact this
  · rw [if_neg h2]
    by_cases h3' : l = 3
    · subst h3'
      have hd3 := h3 rfl
      have h3p : Sz 3 lam 0 (((3 : ℕ) : ℂ) * p) := by
        apply hcancel 0 4 _ (by norm_num)
        convert hA using 1
        push_cast
        ring
      obtain ⟨k, hk⟩ : 3 ∣ d + 1 := by omega
      have h1 := hkey 0 le_rfl (hmulk 0 3 k hk h3p)
      exact hcancel 0 (2 * d) σ (by omega) h1
    · have hl2 : ∀ n : ℕ, n.Prime → l ∣ n → l = n := fun n hn h =>
        (Nat.prime_dvd_prime_iff_eq hlp hn).mp h
      have h12 : ¬ l ∣ 12 := by
        intro h
        rcases (Nat.Prime.dvd_mul hlp).mp (show l ∣ 2 * 2 * 3 from h) with h' | h'
        · rcases (Nat.Prime.dvd_mul hlp).mp h' with h'' | h'' <;>
            exact h2 (hl2 2 Nat.prime_two h'')
        · exact h3' (hl2 3 Nat.prime_three h')
      have h2d : ¬ l ∣ 2 * d := by
        intro h
        rcases (Nat.Prime.dvd_mul hlp).mp h with h' | h'
        · exact h2 (hl2 2 Nat.prime_two h')
        · exact hld (hl2 d hd h')
      have hp : Sz l lam 0 p := by
        apply hcancel 0 12 p h12
        exact_mod_cast hA
      have h1 := hkey 0 le_rfl (hmulk 0 1 (d + 1) (by ring) (by simpa using hp))
      exact hcancel 0 (2 * d) σ h2d h1

end GlobalTheory.SzMult
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValuationBoundThreeInert
section
open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate
open NumberField GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.LatVal ReciprocityTheory.ChartRestriction.L1 Formalism.L2.Th1.F
open GlobalTheory.CMVal GlobalTheory.HeckeGal
open ModularForm (E₄ E₆)

namespace GlobalTheory.ArithThreeInert

theorem main : ∀ [Fact (Nat.Prime 3)] (lam : algebraicClosure ℚ ℂ →+* ℂ_[3]) (d : ℕ) (w σ p : ℂ), d % 3 = 1 → w ^ 2 = -(d : ℂ) → Sz 3 lam 0 (((1 + w) ^ 2 - (1 + (d : ℂ))) * σ - ((1 + w) ^ 2 - 1) * p) → Sz 3 lam 0 (((1 - w) ^ 2 - (1 + (d : ℂ))) * σ - ((1 - w) ^ 2 - 1) * p) → Sz 3 lam 0 σ := by
  intro _ lam d w σ p hd hw h1 h2
  obtain ⟨hint, hadd, hmul, -, hneg, -, -⟩ := GlobalTheory.T.algebraicValuationAtLeast_basic_properties 3 lam
  have hsub : ∀ x y : ℂ, Sz 3 lam 0 x → Sz 3 lam 0 y → Sz 3 lam 0 (x - y) := by
    intro x y hx hy
    rw [sub_eq_add_neg]; exact hadd 0 x (-y) hx (hneg 0 y hy)
  have hI : ∀ x : ℂ, IsIntegral ℤ x → Sz 3 lam 0 x := by
    intro x hx
    exact hint 1 x (by norm_num) (by simpa using hx)
  have hw_int : IsIntegral ℤ w := by
    refine ⟨Polynomial.X ^ 2 + Polynomial.C (d : ℤ), ?_, ?_⟩
    · exact Polynomial.Monic.def.mpr (by
        rw [Polynomial.leadingCoeff_X_pow_add_C (by norm_num)])
    · simp [hw]
  have hA : Sz 3 lam 0 ((1 + w) ^ 2 - 1) :=
    hI _ (((isIntegral_one.add hw_int).pow 2).sub isIntegral_one)
  have hB : Sz 3 lam 0 ((1 - w) ^ 2 - 1) :=
    hI _ (((isIntegral_one.sub hw_int).pow 2).sub isIntegral_one)
  have hW : Sz 3 lam 0 w := hI _ hw_int
  have hcomb : Sz 3 lam 0 (((((1 - w) ^ 2 - 1) *
      (((1 + w) ^ 2 - (1 + (d : ℂ))) * σ - ((1 + w) ^ 2 - 1) * p)) -
      (((1 + w) ^ 2 - 1) * (((1 - w) ^ 2 - (1 + (d : ℂ))) * σ - ((1 - w) ^ 2 - 1) * p))) * w) := by
    have := hmul 0 0 _ _ (hsub _ _ (by simpa using hmul 0 0 _ _ hB h1) (by simpa using hmul 0 0 _ _ hA h2)) hW
    simpa using this
  have heq : ((((1 - w) ^ 2 - 1) *
      (((1 + w) ^ 2 - (1 + (d : ℂ))) * σ - ((1 + w) ^ 2 - 1) * p)) -
      (((1 + w) ^ 2 - 1) * (((1 - w) ^ 2 - (1 + (d : ℂ))) * σ - ((1 - w) ^ 2 - 1) * p))) * w
      = ((4 * d ^ 2 : ℕ) : ℂ) * (-σ) := by
    push_cast
    linear_combination (4 * (d : ℂ) * σ) * hw
  rw [heq] at hcomb
  have hd0 : ((4 * d ^ 2 : ℕ) : ℂ) ≠ 0 := by
    have : d ≠ 0 := by rintro rfl; simp at hd
    exact_mod_cast (by positivity : 0 < 4 * d ^ 2).ne'
  have h3 : ¬ 3 ∣ 4 * d ^ 2 := by
    intro h
    have h0 : (4 * d ^ 2) % 3 = 0 := Nat.mod_eq_zero_of_dvd h
    rw [Nat.mul_mod, Nat.pow_mod, hd] at h0
    norm_num at h0
  have hinv : Sz 3 lam 0 (((4 * d ^ 2 : ℕ) : ℂ))⁻¹ :=
    hint (4 * d ^ 2) _ h3 (by rw [mul_inv_cancel₀ hd0]; exact isIntegral_one)
  have hm := hmul 0 0 _ _ hinv hcomb
  rw [zero_add] at hm
  have hfin := hneg 0 _ hm
  rw [← mul_assoc, inv_mul_cancel₀ hd0, one_mul, neg_neg] at hfin
  exact hfin

end GlobalTheory.ArithThreeInert
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeierstrassTorsionQExpansionIntegral
section
open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.LatVal ReciprocityTheory.ChartRestriction.L1 Formalism.L2.Th1.F

namespace GlobalTheory.WpFam.ExpansionIntegral

theorem main : ∀ (l : ℕ) [Fact l.Prime] (lam : algebraicClosure ℚ ℂ →+* ℂ_[l]) (N : ℕ) [NeZero N] (M : ℕ)
    (x : Fin 2 → ZMod N), ¬ l ∣ M → M • x = 0 → x ≠ 0 →
    QAll (Sz l lam 0) N (wB N x) ∧ QAll (Sz l lam 0) N (wpd N x) := by
  intro l hl lam N _ M x hM hx hx0
  have hpos : 0 < M := Nat.pos_of_ne_zero fun h => hM (h ▸ dvd_zero l)
  have hpow : ∀ e : ℕ, ¬ l ∣ M ^ e := fun e h => hM (hl.out.dvd_of_dvd_pow h)
  have hsz := (GlobalTheory.T.algebraicValuationAtLeast_basic_properties l lam).1
  refine ⟨⟨cB N x, GlobalTheory.T.weierstrass_division_value_q_expansion N x hx0, fun k => hsz (M ^ 2) _ (hpow 2) ?_⟩,
    ⟨cD N x, GlobalTheory.T.hasQExpansion_normalizedDerivWeierstrassPTorsion N x, fun k => hsz (M ^ 3) _ (hpow 3) ?_⟩⟩
  · rw [Nat.cast_pow]
    exact (GlobalTheory.T.isIntegral_weierstrassTorsion_qCoefficients N M x k hpos hx).1
  · rw [Nat.cast_pow]
    exact (GlobalTheory.T.isIntegral_weierstrassTorsion_qCoefficients N M x k hpos hx).2.1

end GlobalTheory.WpFam.ExpansionIntegral
end

