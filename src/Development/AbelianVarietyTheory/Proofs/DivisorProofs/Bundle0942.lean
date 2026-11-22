import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0930
import Development.AbelianVarietyTheory.Definitions.Divisors.OneMemH0WeightZero
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv
import GroundTheory.GlobalFields.IdeleGroups.IdeleNorms
import GroundTheory.AutomorphicForms.ReductionFinite
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0910
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MvIsIntMapMap
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.BiextCoeffSecondLinear
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0922
import Development.AbelianVarietyTheory.Definitions.Divisors.GalMapMul

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobeniusActsOnTypeAtValuation
section
set_option autoImplicit false

namespace GlobalTheory.PrimePart

open NumberField MvPowerSeries IsLocalRing ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.FGDepth GlobalTheory.CharDepth
  GlobalTheory.FactorDepth GlobalTheory.IndefiniteRowSideFullHecke.TypedPartSplitPrimes

section ResidueField

variable {k : Type} [Field k] {p : ℕ} [Fact p.Prime] [CharP k p] {d : ℕ}

theorem sqrtNeg_ne_neg (h2 : p ≠ 2) (hd : (d : ZMod p) ≠ 0) {r : k} (hr : r ^ 2 = -(d : k)) : r ≠ -r := by
  intro h
  have h2k : (2 : k) ≠ 0 := by
    intro h0
    have : p ∣ 2 := (CharP.cast_eq_zero_iff k p 2).1 (by exact_mod_cast h0)
    exact h2 ((Nat.prime_dvd_prime_iff_eq Fact.out Nat.prime_two).1 this)
  have hr0 : r = 0 := by
    have : 2 * r = 0 := by linear_combination h
    exact (mul_eq_zero.1 this).resolve_left h2k
  have hdk : (d : k) = 0 := by
    rw [hr0] at hr
    linear_combination hr
  exact hd ((ZMod.natCast_eq_zero_iff d p).2 ((CharP.cast_eq_zero_iff k p d).1 hdk))

theorem sqrtNeg_pow_of_isSquare (hs : IsSquare (-(d : ZMod p))) {r : k} (hr : r ^ 2 = -(d : k)) : r ^ p = r := by
  obtain ⟨m, hm⟩ := hs
  have h1 : r ^ 2 = (ZMod.castHom (dvd_refl p) k m) ^ 2 := by
    rw [hr, ← map_pow, sq, ← hm, map_neg, map_natCast]
  rcases sq_eq_sq_iff_eq_or_eq_neg.1 h1 with h | h
  · rw [h, ← map_pow, ZMod.pow_card]
  · rw [h, ← map_neg, ← map_pow, ZMod.pow_card]

theorem sqrtNeg_pow_ne_of_not_isSquare (hs : ¬ IsSquare (-(d : ZMod p))) {r : k} (hr : r ^ 2 = -(d : k)) :
    r ^ p ≠ r := by
  have hd : (d : ZMod p) ≠ 0 := fun h => hs (by rw [h, neg_zero]; exact IsSquare.zero)
  have hd' : -(d : ZMod p) ≠ 0 := neg_ne_zero.2 hd
  have h2 : p ≠ 2 := by
    rintro rfl
    apply hs
    generalize (-(d : ZMod 2)) = x
    exact ⟨x, by rw [← sq, ZMod.pow_card]⟩
  have he : (-(d : ZMod p)) ^ (p / 2) = -1 :=
    (ZMod.pow_div_two_eq_neg_one_or_one p hd').resolve_left fun h => hs ((ZMod.euler_criterion p hd').2 h)
  have hk : (-(d : k)) ^ (p / 2) = -1 := by
    have := congrArg (ZMod.castHom (dvd_refl p) k) he
    rwa [map_pow, map_neg, map_neg, map_natCast, map_one] at this
  have hp : p = 2 * (p / 2) + 1 := by
    have := (Fact.out : p.Prime).eq_two_or_odd.resolve_left h2
    omega
  have h3 : r ^ p = -r := by
    conv_lhs => rw [hp]
    rw [pow_succ, pow_mul, hr, hk, neg_one_mul]
  rw [h3]
  exact (sqrtNeg_ne_neg h2 hd hr).symm

end ResidueField

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {l : Level H}

theorem label_rt_sq (H : Host E) (σ : E →+* ℂ) : σ (H.rt : E) ^ 2 = -(H.d : ℂ) := by
  have := congrArg (σ.comp (algebraMap (𝓞 E) E)) H.rt_sq
  rwa [map_pow, map_neg, map_natCast] at this

theorem conj_label_rt (H : Host E) (σ : E →+* ℂ) :
    ComplexEmbedding.conjugate σ (H.rt : E) = -σ (H.rt : E) := by
  rw [ComplexEmbedding.conjugate_coe_eq]
  have h := label_rt_sq H σ
  generalize σ (H.rt : E) = z at h
  have hd : (0 : ℝ) < H.d := by exact_mod_cast H.d_prime.pos
  have h1 := congrArg Complex.re h
  have h2 := congrArg Complex.im h
  simp [sq] at h1 h2
  have h3 : z.re = 0 := by
    by_contra h0
    have h4 : z.im = 0 := by
      have : z.re * z.im = 0 := by linarith
      exact (mul_eq_zero.1 this).resolve_left h0
    rw [h4] at h1
    nlinarith [mul_self_nonneg z.re]
  apply Complex.ext <;> simp [h3]

theorem exists_w0_sq_even_constant (H : Host E) : ∃ n : ℕ, H.w0 ^ 2 = H.w0 - 2 * n := by
  refine ⟨(H.d + 1) / 8, ?_⟩
  have h8 : ((H.d : ℕ) : 𝓞 E) + 1 = 8 * (((H.d + 1) / 8 : ℕ) : 𝓞 E) := by
    have : H.d + 1 = 8 * ((H.d + 1) / 8) := by have := H.d_mod; omega
    exact_mod_cast this
  have h4 : (4 : 𝓞 E) ≠ 0 := by norm_num
  apply mul_left_cancel₀ h4
  have h1 := H.two_weight_eq_one_add_root
  have h2 := H.rt_sq
  linear_combination (2 * H.w0 - 1 + H.rt) * h1 + h2 - h8

variable {c : Coeff l} {T : CDVR} (io : c.F →+* T.Fr) {p : ℕ} [Fact p.Prime] (X : ValExt T p)

theorem red_eq_of_label_eq {σ σ' : E →+* ℂ} {a b : 𝓞 E} (h : σ' (a : E) = σ (b : E)) :
    red io X σ' a = red io X σ b := by
  have h1 : embK c σ' a = embK c σ b := Subtype.ext h
  have h2 : embO io X σ' a = embO io X σ b := X.ints.hom_inj (by
    rw [algebraMap_embO, algebraMap_embO, embX, embX, RingHom.comp_apply, RingHom.comp_apply, RingHom.comp_apply,
      RingHom.comp_apply, h1])
  rw [red, red, RingHom.comp_apply, RingHom.comp_apply, h2]

theorem frobOnType : FrobOnType io X := by
  intro σ σ' hF
  haveI := charP_residueField_of_irreducible X
  have hred : ∀ a, red io X σ' a = red io X σ a ^ p := fun a => (red_eq_pow_iff io X σ σ' a p).2 (hF a)
  have hr : red io X σ H.rt ^ 2 = -(H.d : ResidueField X.O) := by
    rw [← map_pow, H.rt_sq, map_neg, map_natCast]
  have hpm : σ' (H.rt : E) = σ (H.rt : E) ∨ σ' (H.rt : E) = -σ (H.rt : E) :=
    sq_eq_sq_iff_eq_or_eq_neg.1 (by rw [label_rt_sq, label_rt_sq])
  refine ⟨fun hs => ?_, fun hi => ?_⟩
  · have key : σ' (H.rt : E) = σ (H.rt : E) := by
      refine hpm.resolve_right fun h => ?_
      by_cases h2 : p = 2
      · subst h2
        obtain ⟨n, hn⟩ := exists_w0_sq_even_constant H
        have hw : ∀ τ : E →+* ℂ, 2 * τ (H.w0 : E) = 1 + τ (H.rt : E) := fun τ => by
          have := congrArg (τ.comp (algebraMap (𝓞 E) E)) H.two_weight_eq_one_add_root
          rwa [map_mul, map_add, map_one, map_ofNat] at this
        have h1 : σ' (H.w0 : E) = σ ((1 - H.w0 : 𝓞 E) : E) := by
          have e : σ ((1 - H.w0 : 𝓞 E) : E) = 1 - σ (H.w0 : E) := by
            have := map_sub (σ.comp (algebraMap (𝓞 E) E)) 1 H.w0
            rwa [map_one] at this
          rw [e]
          linear_combination (1 / 2) * hw σ' + (1 / 2) * hw σ + (1 / 2) * h
        have h3 := red_eq_of_label_eq io X h1
        rw [hred, ← map_pow, hn, map_sub, map_sub, map_mul, map_one, map_ofNat] at h3
        have h4 : (2 : ResidueField X.O) = 0 := by
          exact_mod_cast CharP.cast_eq_zero (ResidueField X.O) 2
        apply one_ne_zero (α := ResidueField X.O)
        linear_combination -h3 + (red io X σ H.w0 - red io X σ n) * h4
      · have h1 : σ' (H.rt : E) = σ ((-H.rt : 𝓞 E) : E) := by
          rw [h]; exact (map_neg (σ.comp (algebraMap (𝓞 E) E)) H.rt).symm
        have h3 := red_eq_of_label_eq io X h1
        rw [hred, sqrtNeg_pow_of_isSquare hs.2 hr, map_neg] at h3
        exact sqrtNeg_ne_neg h2 hs.1 hr h3
    rw [InPsi, InPsi, key]
  · have key : σ' (H.rt : E) = -σ (H.rt : E) := by
      refine hpm.resolve_left fun h => ?_
      have h3 := red_eq_of_label_eq io X h
      rw [hred] at h3
      exact sqrtNeg_pow_ne_of_not_isSquare hi hr h3
    rw [InPsi, InPsi, key, conj_label_rt]

theorem frobOnType_all (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (l : Level H) (c : Coeff l)
    (p : ℕ) [Fact p.Prime] (T : CDVR) (io : c.F →+* T.Fr) (X : ValExt T p) : FrobOnType io X :=
  frobOnType io X

end GlobalTheory.PrimePart
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FujisakiDivisionQuaternionAlgebraModCentre
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.QSA GlobalTheory.Published
open Matrix
open scoped Quaternion Topology TensorProduct

noncomputable section

namespace GlobalTheory.QSA.FujisakiQ

variable {R : Type*} [CommRing R] {a b : R}

def ofCoords (v : Fin 4 → R) : ℍ[R, a, b] := ⟨v 0, v 1, v 2, v 3⟩

theorem coords_ofCoords (v : Fin 4 → R) : coords (ofCoords v : ℍ[R, a, b]) = v := by
  ext i; fin_cases i <;> rfl

theorem ofCoords_coords (x : ℍ[R, a, b]) : ofCoords (coords x) = x := by
  ext <;> rfl

def lmat (w : ℍ[R, a, b]) : Matrix (Fin 4) (Fin 4) R :=
  !![w.re, a * w.imI, b * w.imJ, -(a * b) * w.imK;
     w.imI, w.re, b * w.imK, -(b * w.imJ);
     w.imJ, -(a * w.imK), w.re, a * w.imI;
     w.imK, -w.imJ, w.imI, w.re]

theorem lmat_mulVec (w v : ℍ[R, a, b]) : lmat w *ᵥ coords v = coords (w * v) := by
  ext i; fin_cases i <;>
    simp [lmat, coords, Matrix.mulVec, dotProduct, Fin.sum_univ_four] <;> ring

theorem det_lmat (w : ℍ[R, a, b]) : (lmat w).det = nrm w ^ 2 := by
  rw [Matrix.det_succ_row_zero]
  simp [lmat, Fin.sum_univ_succ, Matrix.det_fin_three, nrm]
  have h1 : (Fin.succAbove 1 2 : Fin 4) = 3 := by decide
  have h2 : (Fin.succAbove 2 2 : Fin 4) = 3 := by decide
  have h3 : (Fin.succAbove 3 2 : Fin 4) = 2 := by decide
  simp [h1, h2, h3]
  ring

theorem nrm_smul (t : R) (x : ℍ[R, a, b]) : nrm (t • x) = t ^ 2 * nrm x := by
  simp [nrm]; ring

theorem nrm_star (x : ℍ[R, a, b]) : nrm (star x) = nrm x := by
  simp [nrm]

theorem star_mul_eq (x : ℍ[R, a, b]) : star x * x = algebraMap R ℍ[R, a, b] (nrm x) := by
  ext <;> simp [nrm, QuaternionAlgebra.algebraMap_eq] <;> ring

theorem mul_inv_of_unit (x : ℍ[R, a, b]) (u : Rˣ) (hu : (u : R) = nrm x) :
    x * (((u⁻¹ : Rˣ) : R) • star x) = 1 ∧ (((u⁻¹ : Rˣ) : R) • star x) * x = 1 := by
  constructor
  · rw [mul_smul_comm, mul_star_eq, ← hu, Algebra.algebraMap_eq_smul_one, smul_smul,
      Units.inv_mul, one_smul]
  · rw [smul_mul_assoc, star_mul_eq, ← hu, Algebra.algebraMap_eq_smul_one, smul_smul,
      Units.inv_mul, one_smul]

variable [TopologicalSpace R] [IsTopologicalRing R]

theorem continuous_coord (i : Fin 4) : Continuous fun x : ℍ[R, a, b] => coords x i :=
  (continuous_apply i).comp continuous_induced_dom

@[fun_prop] theorem continuous_re : Continuous fun x : ℍ[R, a, b] => x.re := continuous_coord 0
@[fun_prop] theorem continuous_imI : Continuous fun x : ℍ[R, a, b] => x.imI := continuous_coord 1
@[fun_prop] theorem continuous_imJ : Continuous fun x : ℍ[R, a, b] => x.imJ := continuous_coord 2
@[fun_prop] theorem continuous_imK : Continuous fun x : ℍ[R, a, b] => x.imK := continuous_coord 3

theorem continuous_ofCoords : Continuous (ofCoords : (Fin 4 → R) → ℍ[R, a, b]) :=
  continuous_induced_rng.2 (by
    have : (coords ∘ (ofCoords : (Fin 4 → R) → ℍ[R, a, b])) = id := funext coords_ofCoords
    rw [this]; exact continuous_id)

theorem continuous_star' : Continuous (star : ℍ[R, a, b] → ℍ[R, a, b]) := by
  refine continuous_induced_rng.2 (continuous_pi fun i => ?_)
  fin_cases i <;> simp [coords, Function.comp_def] <;> fun_prop

theorem continuous_mul' : Continuous fun p : ℍ[R, a, b] × ℍ[R, a, b] => p.1 * p.2 := by
  refine continuous_induced_rng.2 (continuous_pi fun i => ?_)
  fin_cases i <;> simp [coords, Function.comp_def] <;> fun_prop

theorem continuous_star_mul : Continuous fun p : ℍ[R, a, b] × ℍ[R, a, b] => star p.1 * p.2 := by
  refine continuous_induced_rng.2 (continuous_pi fun i => ?_)
  fin_cases i <;> simp [coords, Function.comp_def] <;> fun_prop

theorem continuous_const_mul' (c : ℍ[R, a, b]) : Continuous fun u : ℍ[R, a, b] => c * u := by
  refine continuous_induced_rng.2 (continuous_pi fun i => ?_)
  fin_cases i <;> simp [coords, Function.comp_def] <;> fun_prop

end GlobalTheory.QSA.FujisakiQ

namespace GlobalTheory.QSA.FujisakiQ

variable {F : Type} [Field F] [NumberField F] {a b : F}

theorem rat_mul (x y : ℍ[F, a, b]) : rat (x * y) = rat x * rat y := by
  ext <;> simp [rat]

theorem rat_star (x : ℍ[F, a, b]) : rat (star x) = star (rat x) := by
  ext <;> simp [rat]

theorem rat_one : rat (1 : ℍ[F, a, b]) = 1 := by
  ext <;> simp [rat]

theorem coords_rat (x : ℍ[F, a, b]) :
    coords (rat x) = fun i => algebraMap F (AF F) (coords x i) := by
  ext i; fin_cases i <;> rfl

theorem rat_inv (x : ℍ[F, a, b]) (hx : nrm x ≠ 0) :
    x * ((nrm x)⁻¹ • star x) = 1 ∧ ((nrm x)⁻¹ • star x) * x = 1 :=
  mul_inv_of_unit x (Units.mk0 (nrm x) hx) rfl

theorem exists_rat_mem (B : Set (Fin 4 → AF F))
    (hB : ∀ g : Matrix (Fin 4) (Fin 4) (AF F), IsUnit g.det → (∃ u : (AF F)ˣ, (u : AF F) = g.det ∧
      (GroundTheory.Global.IdeleGroup.ideleModule F u : ℝ) ≤ 1) →
      ∃ ξ : Fin 4 → F, ξ ≠ 0 ∧ g *ᵥ (fun i => algebraMap F (AF F) (ξ i)) ∈ B)
    (hdiv : ∀ x : ℍ[F, a, b], nrm x = 0 → x = 0)
    (w : DA F a b) (u : (AF F)ˣ) (hu : (u : AF F) = nrm w)
    (hmod : GroundTheory.Global.IdeleGroup.ideleModule F u = 1) :
    ∃ δ : ℍ[F, a, b], nrm δ ≠ 0 ∧ w * rat δ ∈ ofCoords '' B := by
  have hdet : (lmat w).det = ((u ^ 2 : (AF F)ˣ) : AF F) := by rw [det_lmat, Units.val_pow_eq_pow_val, hu]
  obtain ⟨ξ, hξ0, hξ⟩ := hB (lmat w) (by rw [hdet]; exact Units.isUnit _)
    ⟨u ^ 2, hdet.symm, by rw [map_pow, hmod, one_pow]; simp⟩
  let δ : ℍ[F, a, b] := ofCoords ξ
  refine ⟨δ, fun h => hξ0 ?_, ⟨lmat w *ᵥ coords (rat δ), ?_, ?_⟩⟩
  · have h0 := hdiv _ h
    ext i
    have := congrArg (fun x => coords x i) h0
    simp only [δ, coords_ofCoords] at this
    rw [this]; fin_cases i <;> rfl
  · rw [coords_rat, coords_ofCoords]; exact hξ
  · rw [lmat_mulVec, ofCoords_coords]

end GlobalTheory.QSA.FujisakiQ

namespace GlobalTheory.QSA.FujisakiQ

open GroundTheory.Global.IdeleGroup in

theorem fujisaki_mod_centre : ∀ (F : Type) [Field F] [NumberField F] (a b : F), a ≠ 0 → b ≠ 0 → (∀ x : ℍ[F, a, b], nrm x = 0 → x = 0) → ∃ C : Set (DA F a b), IsCompact C ∧ ∀ y : DA F a b, IsUnit (nrm y) → ∃ (δ : ℍ[F, a, b]) (l : AF F) (c c' : DA F a b), nrm δ ≠ 0 ∧ IsUnit l ∧ c ∈ C ∧ c' ∈ C ∧ c * c' = 1 ∧ c' * c = 1 ∧ y = l • (rat δ * c) := by
  intro F _ _ a b _ _ hdiv
  obtain ⟨B, hBc, hB⟩ := GlobalTheory.T.adelic_minkowski_exists_short_rational_vector F 4 (by norm_num)
  obtain ⟨B', hB'⟩ : ∃ B' : Set (DA F a b), B' = ofCoords '' B := ⟨_, rfl⟩
  have hB'c : IsCompact B' := hB' ▸ hBc.image continuous_ofCoords
  obtain ⟨S, hS⟩ : ∃ S : Set (DA F a b), S = (fun p : DA F a b × DA F a b => star p.1 * p.2) '' (B' ×ˢ B') := ⟨_, rfl⟩
  have hSc : IsCompact S := hS ▸ (hB'c.prod hB'c).image continuous_star_mul
  obtain ⟨Z, hZ⟩ : ∃ Z : Set ℍ[F, a, b], Z = {γ | rat γ ∈ S} := ⟨_, rfl⟩
  have hZf : Z.Finite := by
    have hT : (Set.pi Set.univ (fun i : Fin 4 =>
        {k : F | algebraMap F (AF F) k ∈ (fun y : DA F a b => coords y i) '' S})).Finite :=
      Set.Finite.pi fun i => GroundTheory.Automorphic.Reduction.finite_setOf_algebraMap_mem
        (hSc.image (continuous_coord i))
    refine (hT.image (ofCoords : (Fin 4 → F) → ℍ[F, a, b])).subset fun γ hγ => ?_
    rw [hZ] at hγ
    refine ⟨coords γ, fun i _ => ⟨rat γ, hγ, ?_⟩, ofCoords_coords γ⟩
    show coords (rat γ) i = _
    rw [coords_rat]
  obtain ⟨C, hC⟩ : ∃ C : Set (DA F a b), C =
    B' ∪ ⋃ γ ∈ Z, (fun u => rat ((nrm γ)⁻¹ • star γ) * u) '' (star '' B') := ⟨_, rfl⟩
  have hCc : IsCompact C := hC ▸ hB'c.union (hZf.isCompact_biUnion fun γ _ =>
    (hB'c.image continuous_star').image (continuous_const_mul' _))
  refine ⟨C, hCc, fun y hy => ?_⟩
  obtain ⟨uy, huy⟩ := hy
  obtain ⟨l, hl⟩ := ideleModule_surjective (K := F)
    ⟨Real.sqrt (ideleModule F uy : ℝ), Real.sqrt_pos.2 (ideleModule F uy).2⟩
  obtain ⟨uz, huz⟩ : ∃ uz : (AF F)ˣ, uz = l⁻¹ ^ 2 * uy := ⟨_, rfl⟩
  obtain ⟨z, hz⟩ : ∃ z : DA F a b, z = ((l⁻¹ : (AF F)ˣ) : AF F) • y := ⟨_, rfl⟩
  have hnz : (uz : AF F) = nrm z := by
    rw [hz, nrm_smul, ← huy, huz, Units.val_mul, Units.val_pow_eq_pow_val]
  have hmod : ideleModule F uz = 1 := by
    have h : ideleModule F uz * ideleModule F l ^ 2 = ideleModule F uy := by
      rw [← map_pow, ← map_mul]
      congr 1
      rw [huz, mul_comm, ← mul_assoc, ← mul_pow, mul_inv_cancel, one_pow, one_mul]
    have h' := congrArg Subtype.val h
    rw [hl] at h'
    have hp := (ideleModule F uy).2
    have h'' : (ideleModule F uz : ℝ) * (ideleModule F uy : ℝ) = (ideleModule F uy : ℝ) := by
      have e : ((⟨Real.sqrt (ideleModule F uy : ℝ), Real.sqrt_pos.2 hp⟩ : {r : ℝ // 0 < r}) ^ 2 : {r : ℝ // 0 < r}).1
          = (ideleModule F uy : ℝ) := by
        show Real.sqrt (ideleModule F uy : ℝ) ^ 2 = _
        exact Real.sq_sqrt hp.le
      rw [Positive.val_mul, e] at h'; exact h'
    exact Subtype.ext (mul_right_cancel₀ hp.ne' (h''.trans (one_mul _).symm))
  obtain ⟨zi, hzi_def⟩ : ∃ zi : DA F a b, zi = ((uz⁻¹ : (AF F)ˣ) : AF F) • star z := ⟨_, rfl⟩
  have hzi := mul_inv_of_unit z uz hnz
  rw [← hzi_def] at hzi
  have hu1 : ((uz⁻¹ : (AF F)ˣ) : AF F) = nrm zi := by
    rw [hzi_def, nrm_smul, nrm_star, ← hnz, sq, mul_assoc, Units.inv_mul, mul_one]
  obtain ⟨δ, hδ, hc'⟩ := exists_rat_mem B hB hdiv zi uz⁻¹ hu1 (by rw [map_inv, hmod, inv_one])
  obtain ⟨δ', hδ', hc2⟩ := exists_rat_mem B hB hdiv (star z) uz ((nrm_star z).trans hnz.symm).symm hmod
  obtain ⟨γ, hγdef⟩ : ∃ γ : ℍ[F, a, b], γ = star δ' * δ := ⟨_, rfl⟩
  have hγ : rat γ = star (star z * rat δ') * (zi * rat δ) := by
    rw [hγdef, rat_mul, rat_star, star_mul, star_star]
    simp only [mul_assoc]
    rw [← mul_assoc z zi, hzi.1, one_mul]
  have hγZ : γ ∈ Z := by
    rw [hZ]; show rat γ ∈ S; rw [hS]; exact ⟨(star z * rat δ', zi * rat δ), ⟨hB' ▸ hc2, hB' ▸ hc'⟩, hγ.symm⟩
  have hγ0 : nrm γ ≠ 0 := by
    rw [hγdef, nrm_mul, nrm_star]; exact mul_ne_zero hδ' hδ
  have hγi := rat_inv γ hγ0
  have hd := rat_inv δ hδ
  have e1 : (nrm γ)⁻¹ • star γ * star δ' = (nrm δ)⁻¹ • star δ := by
    calc (nrm γ)⁻¹ • star γ * star δ' = (nrm γ)⁻¹ • star γ * star δ' * (δ * ((nrm δ)⁻¹ • star δ)) := by
          rw [hd.1, mul_one]
      _ = ((nrm γ)⁻¹ • star γ * γ) * ((nrm δ)⁻¹ • star δ) := by rw [hγdef]; simp only [mul_assoc]
      _ = (nrm δ)⁻¹ • star δ := by rw [hγi.2, one_mul]
  have hc : rat ((nrm γ)⁻¹ • star γ) * star (star z * rat δ') = rat ((nrm δ)⁻¹ • star δ) * z := by
    rw [star_mul, star_star, ← rat_star, ← mul_assoc, ← rat_mul, e1]
  refine ⟨δ, (l : AF F), rat ((nrm γ)⁻¹ • star γ) * star (star z * rat δ'), zi * rat δ, hδ, l.isUnit,
    hC ▸ Or.inr (Set.mem_biUnion hγZ ⟨_, ⟨_, hB' ▸ hc2, rfl⟩, rfl⟩), hC ▸ Or.inl (hB' ▸ hc'), ?_, ?_, ?_⟩
  · rw [mul_assoc, ← hγ, ← rat_mul, hγi.2, rat_one]
  · rw [hc, ← mul_assoc, mul_assoc zi, ← rat_mul, hd.1, rat_one, mul_one, hzi.2]
  · rw [hc, ← mul_assoc, ← rat_mul, hd.1, rat_one, one_mul, hz, smul_smul, Units.mul_inv, one_smul]

end GlobalTheory.QSA.FujisakiQ
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaugeHermitianCombinationOfSteps
section
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.IsoTriv.HermRead

open MvPowerSeries
open ReciprocityTheory.ChartRestriction.G.TB (dAct)

section Lin

variable {C : Type} [Field C] {d : ℕ} {σ : Type}

theorem mv_sum (A : Matrix (Fin d) (Fin d) C) {β : Type} (s : Finset β) (x : β → Fin d → MvPowerSeries σ C) :
    mv A (∑ b ∈ s, x b) = ∑ b ∈ s, mv A (x b) := by
  funext e
  simp only [mv, Finset.sum_apply, Finset.smul_sum]
  exact Finset.sum_comm

theorem mv_mv (A A' : Matrix (Fin d) (Fin d) C) (w : Fin d → MvPowerSeries σ C) :
    mv A (mv A' w) = mv (A * A') w := by
  funext e
  simp only [mv, Matrix.mul_apply, Finset.smul_sum, Finset.sum_smul, smul_smul]
  exact Finset.sum_comm

theorem add_mv (A A' : Matrix (Fin d) (Fin d) C) (w : Fin d → MvPowerSeries σ C) :
    mv (A + A') w = mv A w + mv A' w := by
  funext e
  simp only [mv, Matrix.add_apply, add_smul, Finset.sum_add_distrib, Pi.add_apply]

end Lin

theorem map_sum_of_additive {M Q : Type} [AddCommMonoid M] [AddCommGroup Q] (p : M → Prop) (h0 : p 0)
    (hp : ∀ x y, p x → p y → p (x + y)) (f : M → Q) (hf : ∀ x y, p x → p y → f (x + y) = f x + f y)
    {β : Type} (s : Finset β) (x : β → M) (hx : ∀ b, p (x b)) :
    p (∑ b ∈ s, x b) ∧ f (∑ b ∈ s, x b) = ∑ b ∈ s, f (x b) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    refine ⟨by simpa using h0, ?_⟩
    have := hf 0 0 h0 h0
    rw [add_zero] at this
    simpa using this
  | insert b s hb ih =>
    rw [Finset.sum_insert hb, Finset.sum_insert hb]
    exact ⟨hp _ _ (hx b) ih.1, by rw [hf _ _ (hx b) ih.1, ih.2]⟩

theorem finSt_of (hAdd : AddSt) (hAct : ActSt) (hUnit : UnitSt) (hBi : BiaddSt) : FinSt := by
  intro C _ _ v d R _ _ O _ _ B hB h hg σ _ κ _ w hw w0 n a ι _ e t ht
  obtain ⟨hU0, hUadd, hUneg, -⟩ := hUnit C v σ
  obtain ⟨hI0, -, hIadd⟩ := hAdd C v d (fglOf hB) σ
  have hIact := fun c => (hAct C v d R O B hB σ c).2
  have hbi := hBi C v d R O B hB h hg σ
  let U : AddSubgroup (MvPowerSeries σ C) :=
    { carrier := {s | LogUnit v s}
      add_mem' := fun {s t} hs ht => hUadd s t hs ht
      zero_mem' := hU0
      neg_mem' := fun {s} hs => hUneg s hs }
  let π := QuotientAddGroup.mk' U
  have key : ∀ s, π s = 0 ↔ LogUnit v s := fun s => QuotientAddGroup.eq_zero_iff s
  have h1 : ∀ z, IntLog (fglOf hB) z → ∀ x y, IntLog (fglOf hB) x → IntLog (fglOf hB) y →
      π (pairSer (fglOf hB) h (x + y) z) = π (pairSer (fglOf hB) h x z) + π (pairSer (fglOf hB) h y z) := by
    intro z hz x y hx hy
    have := (key _).2 (hbi x y z hx hy hz).2.1
    rw [map_sub, map_add, sub_eq_zero] at this
    exact this.symm
  have h2 : ∀ z, IntLog (fglOf hB) z → ∀ x y, IntLog (fglOf hB) x → IntLog (fglOf hB) y →
      π (pairSer (fglOf hB) h z (x + y)) = π (pairSer (fglOf hB) h z x) + π (pairSer (fglOf hB) h z y) := by
    intro z hz x y hx hy
    have := (key _).2 (hbi x y z hx hy hz).2.2.1
    rw [map_sub, map_add, sub_eq_zero] at this
    exact this.symm
  have h3 : ∀ (c : O) x z, IntLog (fglOf hB) x → IntLog (fglOf hB) z →
      π (pairSer (fglOf hB) h (mv (dAct C B c) x) z) =
        π (pairSer (fglOf hB) h x (mv (dAct C B (star c)) z)) := by
    intro c x z hx hz
    have := (key _).2 ((hbi x x z hx hx hz).2.2.2 c)
    rwa [map_sub, sub_eq_zero] at this
  let F : κ → κ → O →+ MvPowerSeries σ C ⧸ U := fun b b' =>
    AddMonoidHom.mk' (fun c => π (pairSer (fglOf hB) h (w b) (mv (dAct C B c) (w b')))) fun c c' => by
      rw [ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.EigA.dAct_add, add_mv]
      exact h2 _ (hw b) _ _ (hIact _ _ (hw b')) (hIact _ _ (hw b'))
  have hF : ∀ b b' c, F b b' c = π (pairSer (fglOf hB) h (w b) (mv (dAct C B c) (w b'))) := fun _ _ _ => rfl
  have hj : ∀ j, π (pairSer (fglOf hB) h (∑ b, mv (dAct C B (a b j)) (w b))
      (mv (dAct C B w0) (∑ b, mv (dAct C B (a b j)) (w b)))) =
        ∑ b, ∑ b', F b b' (star (a b j) * a b' j * w0) := by
    intro j
    have hy : IntLog (fglOf hB) (∑ b, mv (dAct C B (a b j)) (w b)) :=
      (map_sum_of_additive (IntLog (fglOf hB)) hI0 hIadd (fun _ => (0 : ℤ)) (by simp) Finset.univ _
        fun b => hIact _ _ (hw b)).1
    have hz := hIact w0 _ hy
    generalize hzz : mv (dAct C B w0) (∑ b, mv (dAct C B (a b j)) (w b)) = z at hz
    refine (map_sum_of_additive (IntLog (fglOf hB)) hI0 hIadd (fun x => π (pairSer (fglOf hB) h x z)) (h1 _ hz)
      Finset.univ _ fun b => hIact (a b j) _ (hw b)).2.trans (Finset.sum_congr rfl fun b _ => ?_)
    rw [h3 _ _ _ (hw b) hz, ← hzz, mv_mv, mv_sum, ← ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.EigA.dAct_mul]
    refine (map_sum_of_additive (IntLog (fglOf hB)) hI0 hIadd (fun x => π (pairSer (fglOf hB) h (w b) x))
      (h2 _ (hw b)) Finset.univ _ fun b' => hIact _ _ (hIact _ _ (hw b'))).2.trans
      (Finset.sum_congr rfl fun b' _ => ?_)
    rw [hF, mv_mv, ← ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.EigA.dAct_mul, mul_right_comm]
  rw [← key, map_sub, sub_eq_zero, map_sum, Finset.sum_congr rfl fun j _ => hj j, Finset.sum_comm, map_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [Finset.sum_comm, map_sum]
  refine Finset.sum_congr rfl fun b' _ => ?_
  rw [← map_sum, ← Finset.sum_mul, ht, map_sum, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_zsmul, Int.cast_smul_eq_zsmul, map_zsmul, hF]

end GlobalTheory.IsoTriv.HermRead
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HenselianDirectedUnionSubalgebrasStatement
section
open GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.henselian_directed_union_subalgebras : ∀ (q : ℕ) [NeZero q] (T : Type) [CommRing T] [IsDomain T] [IsLocalRing T], AIC T → IsUnit (q : T) → ∀ (O : Type) [CommRing O] [Algebra T O] [Algebra (Polynomial T) O] [IsScalarTower T (Polynomial T) O] [HenselianLocalRing O] [IsSepClosed (IsLocalRing.ResidueField O)], (∃ (ι : Type) (_ : Preorder ι) (_ : IsDirected ι (· ≤ ·)) (_ : Nonempty ι) (Si : ι → Subalgebra (Polynomial T) O), Monotone Si ∧ (∀ s : O, ∃ i, s ∈ Si i) ∧ ∀ i, ∃ (E : Type) (_ : CommRing E) (_ : Algebra (Polynomial T) E) (_ : Algebra.Etale (Polynomial T) E) (P : Ideal E) (_ : P.IsPrime), Nonempty (Localization.AtPrime P ≃ₐ[(Polynomial T)] Si i)) → ∀ (A : Type) [CommRing A] [Algebra (Polynomial T) A] [Algebra T A] [IsScalarTower T (Polynomial T) A] (π : O →ₐ[Polynomial T] A), Function.Surjective π → ∀ u : (TensorProduct T (FractionRing T) A)ˣ, ∃ v : (TensorProduct T (FractionRing T) A)ˣ, v ^ q = u := by
  first | (exact @GlobalTheory.QUnits.tensorFractionRing_units_pow_surj) | (exact GlobalTheory.QUnits.tensorFractionRing_units_pow_surj) | (intros; apply GlobalTheory.QUnits.tensorFractionRing_units_pow_surj  <;> assumption)
end

