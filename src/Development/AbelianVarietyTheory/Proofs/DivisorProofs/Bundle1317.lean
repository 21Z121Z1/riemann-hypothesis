import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0049
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1258
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1285
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1277
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1259
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1217
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1275
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1287
import Development.AbelianVarietyTheory.Definitions.Divisors.KernelNormConstantSpec
import Formalism.SharpRestriction.GlobalSchurBounds.StandardLatticesGL3
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0027
import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsTopologicalRingAE
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0068
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0825
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0988
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1023
import Formalism.LocalToGlobal.BesselHermitianTheta.Bundle0003
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0029
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.MemLatOIffExistsActO
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0126
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1280
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1090
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1104

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryLocalSignEqOneOfIntegralSeparableReductio
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.BCT

theorem kapSign_eq_one_of_integral : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (w : Pl E),
    (∀ x, cj w (cj w x) = x) → (∀ x, Valued.v (cj w x) = Valued.v x) →
    ∀ P₀ : (w.adicCompletionIntegers E)[X], IsCoprime P₀ (derivative P₀) →
    ∀ γ : UL n w, γ.1.val.charpoly = P₀.map (algebraMap (w.adicCompletionIntegers E) (w.adicCompletion E)) →
    γ ∈ KL n w → ∀ Q₁ : (w.adicCompletion E)[X],
    Q₁ ∣ P₀.map (algebraMap (w.adicCompletionIntegers E) (w.adicCompletion E)) → kapSign n w Q₁ γ.1 = 1 := by
  intro E _ _ _ n w hinv hv P₀ hcop γ hchar hK Q₁ hdvd
  unfold kapSign
  split_ifs with hs
  · rfl
  simp only
  have hU : (γ.1.val.map (cj w))ᵀ * γ.1.val = 1 := by
    have h2 : (UL n w : Subgroup (GLw n w)) = UJ (cj w) 1 := by unfold UL; rw [if_neg hs]
    have h : γ.1 ∈ UJ (cj w) 1 := by rw [← h2]; exact γ.2
    simpa [UJ, cT] using h
  set K := w.adicCompletion E
  set f := algebraMap (w.adicCompletionIntegers E) K with hf
  have finj : Function.Injective f := fun a b h => Subtype.ext h
  set V₁ := LinearMap.ker (Matrix.toLin' (aeval γ.1.val Q₁)) with hV₁
  set G := (Matrix.of fun i j => ∑ k, cj w ((Module.finBasis K V₁ i).1 k) * (Module.finBasis K V₁ j).1 k) with hG
  by_cases h0 : G.det = 0
  · rw [h0]; simp [ordL]
  obtain ⟨g, hg⟩ := hK
  have hγ : γ.1.val = g.val.map (fun x => (x : K)) := by
    have := congrArg (fun u => (u : GLw n w).val) hg
    simpa [bc] using this.symm
  have hmon : P₀.Monic := by
    apply Polynomial.monic_of_injective finj
    rw [← hchar]; exact Matrix.charpoly_monic _
  obtain ⟨Q₁₀, Q₂₀, A, B, c, hc, hP, hAB, hQ⟩ := GlobalTheory.T.dvd_integral_monic_coprime_derivative_bezout_factor E w P₀ hmon hcop Q₁ hdvd
  set q₁ := Q₁₀.map f
  set q₂ := Q₂₀.map f
  have hAB' : A.map f * q₁ + B.map f * q₂ = 1 := by
    have := congrArg (Polynomial.map f) hAB
    simpa [Polynomial.map_add, Polynomial.map_mul] using this
  have hCH : aeval γ.1.val (q₁ * q₂) = 0 := by
    rw [← Polynomial.map_mul, ← hP, ← hchar]; exact Matrix.aeval_self_charpoly _
  have hmem : ∀ x, x ∈ V₁ ↔ aeval γ.1.val q₁ *ᵥ x = 0 := by
    intro x
    rw [hV₁, LinearMap.mem_ker, Matrix.toLin'_apply, hQ, map_mul, aeval_C]
    rw [show (algebraMap K (Matrix (Fin n) (Fin n) K) c) = c • (1 : Matrix (Fin n) (Fin n) K) from
      (Algebra.algebraMap_eq_smul_one c)]
    rw [smul_mul_assoc, one_mul, Matrix.smul_mulVec, smul_eq_zero]
    simp [hc]
  set e := aeval γ.1.val (q₂ * B.map f) with he
  have heint : ∀ i j, Valued.v (e i j) ≤ 1 := by
    intro i j
    have : e = (aeval g.val (Q₂₀ * B)).map (fun x => (x : K)) := by
      rw [he, ← Polynomial.map_mul, Polynomial.aeval_map_algebraMap, hγ,
        show g.val.map (fun x => (x : K)) = (Algebra.ofId (w.adicCompletionIntegers E) K).mapMatrix g.val from rfl,
        Polynomial.aeval_algHom_apply]
      rfl
    rw [this, Matrix.map_apply]
    exact ((aeval g.val (Q₂₀ * B)) i j).2
  have hcomm1 : ∀ x, aeval γ.1.val q₁ *ᵥ (e *ᵥ x) = 0 := by
    intro x
    rw [Matrix.mulVec_mulVec, he, ← map_mul, ← mul_assoc, map_mul, hCH, zero_mul, Matrix.zero_mulVec]
  have he1 : e = 1 - aeval γ.1.val (A.map f) * aeval γ.1.val q₁ := by
    rw [he, ← map_mul, mul_comm q₂, eq_sub_iff_add_eq, ← map_add, add_comm, hAB', map_one]
  have hfix : ∀ x ∈ V₁, e *ᵥ x = x := by
    intro x hx
    rw [he1, Matrix.sub_mulVec, Matrix.one_mulVec, ← Matrix.mulVec_mulVec, (hmem x).1 hx,
      Matrix.mulVec_zero, sub_zero]
  have hker2 : ∀ y, aeval γ.1.val q₂ *ᵥ (y - e *ᵥ y) = 0 := by
    intro y
    rw [he1, Matrix.sub_mulVec, Matrix.one_mulVec, sub_sub_cancel, Matrix.mulVec_mulVec, ← map_mul, ← map_mul,
      show q₂ * (A.map f * q₁) = A.map f * (q₁ * q₂) by ring, map_mul, hCH, mul_zero, Matrix.zero_mulVec]
  have horth := GlobalTheory.T.unitary_aeval_kernels_orthogonal_of_coprime K (cj w) n γ.1.val hU q₁ q₂ (A.map f) (B.map f) hAB' hCH V₁ hmem (Module.finBasis K V₁) h0
  obtain ⟨s, fb, hfb⟩ := GlobalTheory.T.orthogonal_projection_integral_adic E w (cj w) hinv hv n V₁ e heint (fun x => (hmem _).2 (hcomm1 x)) hfix
    (fun x hx y => horth x hx _ (hker2 y))
  exact GlobalTheory.T.even_ordL_conjGramDet_of_unit_gram_adicCompletion E w (cj w) hv n V₁ (Module.finBasis K V₁) fb hfb

end GlobalTheory.BCT
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryRankOneSphericalIntegrandDiagonalTorusFac
section
open MeasureTheory GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.SatakeBound GlobalTheory.WeylCell Formalism.UG GlobalTheory.WeylCell.WeylUnipotentShell

noncomputable section

namespace GlobalTheory.WeylCell.U21TorusFactor

open Formalism.UG

theorem swap_rev_comm {n : ℕ} (a i : Fin n) :
    Equiv.swap a a.rev i.rev = (Equiv.swap a a.rev i).rev := by
  rcases eq_or_ne i a with rfl | h1
  · simp [Equiv.swap_apply_left, Equiv.swap_apply_right]
  rcases eq_or_ne i a.rev with rfl | h2
  · simp [Equiv.swap_apply_left, Equiv.swap_apply_right]
  rw [Equiv.swap_apply_of_ne_of_ne h1 h2, Equiv.swap_apply_of_ne_of_ne]
  · exact fun h => h2 (by rw [← h, Fin.rev_rev])
  · exact fun h => h1 (Fin.rev_injective h)

theorem conj_diag_apply {R : Type} [CommRing R] {n : ℕ} (s : Equiv.Perm (Fin n))
    (Y Yi T : Matrix (Fin n) (Fin n) R) (hinv : Yi * Y = 1)
    (hY : ∀ i j, i ≠ s j → Y i j = 0) (hYi : ∀ i j, j ≠ s i → Yi i j = 0)
    (hT : ∀ i j, i ≠ j → T i j = 0) (i j : Fin n) :
    (Yi * T * Y) i j = if i = j then T (s i) (s i) else 0 := by
  have e1 : (Yi * T * Y) i j = Yi i (s j) * T (s j) (s j) * Y (s j) j := by
    rw [Matrix.mul_apply, Finset.sum_eq_single (s j)]
    · rw [Matrix.mul_apply, Finset.sum_eq_single (s j)]
      · intro p _ hp; rw [hT p (s j) hp, mul_zero]
      · intro h; exact absurd (Finset.mem_univ _) h
    · intro r _ hr; rw [hY r j hr, mul_zero]
    · intro h; exact absurd (Finset.mem_univ _) h
  rw [e1]
  split_ifs with hij
  · subst hij
    have e2 : (Yi * Y) i i = Yi i (s i) * Y (s i) i := by
      rw [Matrix.mul_apply, Finset.sum_eq_single (s i)]
      · intro p _ hp; rw [hY p i hp, mul_zero]
      · intro h; exact absurd (Finset.mem_univ _) h
    rw [hinv, Matrix.one_apply_eq] at e2
    calc Yi i (s i) * T (s i) (s i) * Y (s i) i = T (s i) (s i) * (Yi i (s i) * Y (s i) i) := by ring
      _ = T (s i) (s i) := by rw [← e2, mul_one]
  · rw [hYi i (s j) (fun h => hij (s.injective h).symm), zero_mul, zero_mul]

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))]

theorem ordL_inv (z : L) : ordL z⁻¹ = -ordL z := by
  rcases eq_or_ne z 0 with rfl | hz
  · simp [ordL]
  have h1 := GlobalTheory.BorelUMod.v_eq_exp (inv_ne_zero hz)
  rw [map_inv₀, GlobalTheory.BorelUMod.v_eq_exp hz, ← WithZero.exp_neg, WithZero.exp_inj] at h1
  linarith

theorem ordL_map {σ : L →+* L} (hσ : ∀ x, Valued.v (σ x) = Valued.v x) (z : L) : ordL (σ z) = ordL z := by
  rcases eq_or_ne z 0 with rfl | hz
  · simp
  have hz' : σ z ≠ 0 := (map_ne_zero σ).2 hz
  have h1 := hσ z
  rw [GlobalTheory.BorelUMod.v_eq_exp hz, GlobalTheory.BorelUMod.v_eq_exp hz', WithZero.exp_inj] at h1
  linarith

end GlobalTheory.WeylCell.U21TorusFactor

namespace GlobalTheory.WeylCell.U21TorusFactor

open Formalism.UG

theorem torus_factor : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] [CompleteSpace L] (ϖ : L)
    (σ : L →+* L) (q : ℕ), IsUnramInv ϖ σ q →
    ∀ (n : ℕ) (k : Fin (n / 2)), ¬ k.val + 1 < n / 2 → ¬ Even n →
    ∀ y : GU σ n, y ∈ KU σ n → IsWeylRep (simpleU k) (y : GL (Fin n) L) →
    ∀ (α : Fin (n / 2) → ℂˣ) (φ : GU σ n → ℂ), IsSphericalU q (fun i => (α i : ℂ)) φ →
    ∀ t : GU σ n, (∀ i j, i ≠ j → ((t : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i j = 0) → ∀ w x : GU σ n,
      φ (y⁻¹ * t * w * x) * (q : ℂ) ^ (-4 * ordL (((t : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) (lo k) (lo k))) =
        chiDeltaU q (fun i => (actU k α i : ℂ)) t * φ (y⁻¹ * w * x) := by
  intro L _ _ _ ϖ σ q hU n k hk hn y hy hw α φ hφ t ht w x
  have hσv : ∀ z, Valued.v (σ z) = Valued.v z := hU.2.1
  have hq : (q : ℂ) ≠ 0 := by
    have := hU.2.2.2.2.2.1
    exact_mod_cast (by omega : q ≠ 0)
  have hs : simpleU k = Equiv.swap (lo k) (lo k).rev := by
    rw [simpleU, if_neg hk]
  set a : Fin n := lo k with ha
  have hkv : k.val = n / 2 - 1 := by have := k.2; omega
  have hodd : n % 2 = 1 := by
    rcases Nat.even_or_odd n with h | h
    · exact absurd h hn
    · exact Nat.odd_iff.1 h
  have hav : a.val = k.val := rfl
  have hrv : (a.rev).val = n - 1 - k.val := by rw [Fin.val_rev, hav]; omega

  set Y : Matrix (Fin n) (Fin n) L := (((y : GU σ n) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) with hYd
  set Yi : Matrix (Fin n) (Fin n) L := ((((y : GU σ n) : GL (Fin n) L)⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) with hYid
  set T : Matrix (Fin n) (Fin n) L := (((t : GU σ n) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) with hTd
  have hinv : Yi * Y = 1 := by
    rw [hYid, hYd, ← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hYw : ∀ i j, i ≠ Equiv.swap a a.rev j → Y i j = 0 := by
    intro i j h; rw [← hs] at h; exact hw i j h
  have hYi : ∀ i j, j ≠ Equiv.swap a a.rev i → Yi i j = 0 := by
    intro i j h
    have hm := (GlobalTheory.LGrp.mem_GU_iff σ n _).1 (y : GU σ n).2 i j
    rw [hYid, hm]
    have : j.rev ≠ Equiv.swap a a.rev i.rev := by
      rw [swap_rev_comm]; exact fun h' => h (Fin.rev_injective h')
    exact (congrArg σ (hYw _ _ this)).trans (map_zero σ)
  set b : GU σ n := y⁻¹ * t * y with hbd
  have hb : ∀ i j, (((b : GU σ n) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i j =
      if i = j then T (Equiv.swap a a.rev i) (Equiv.swap a a.rev i) else 0 := by
    intro i j
    have : (((b : GU σ n) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) = Yi * T * Y := by
      simp [hbd, hYid, hYd, hTd, Units.val_mul]
    rw [this]
    exact conj_diag_apply _ Y Yi T hinv hYw hYi ht i j
  have hB : IsBorelU b := by
    intro i j hij
    rw [hb, if_neg (ne_of_gt hij)]
  have hsph := hφ b (y⁻¹ * w * x) 1 hB (one_mem _)
  have hprod : y⁻¹ * t * w * x = b * (y⁻¹ * w * x) * 1 := by
    rw [hbd]; group

  have hTa : T a a ≠ 0 ∧ ordL (T a.rev a.rev) = -ordL (T a a) := by
    set Ti : Matrix (Fin n) (Fin n) L := ((((t : GU σ n) : GL (Fin n) L)⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) with hTid
    have h1 : T * Ti = 1 := by
      rw [hTid, hTd, ← Units.val_mul, mul_inv_cancel, Units.val_one]
    have h2 : (T * Ti) a a = T a a * Ti a a := by
      rw [Matrix.mul_apply, Finset.sum_eq_single a]
      · intro p _ hp; rw [ht a p (Ne.symm hp), zero_mul]
      · intro h; exact absurd (Finset.mem_univ _) h
    rw [h1, Matrix.one_apply_eq] at h2
    have hne : T a a ≠ 0 := by intro h0; rw [h0, zero_mul] at h2; exact one_ne_zero h2
    have hTi : Ti a a = (T a a)⁻¹ := by
      exact eq_inv_of_mul_eq_one_right h2.symm
    have hm := (GlobalTheory.LGrp.mem_GU_iff σ n _).1 (t : GU σ n).2 a a
    rw [← hTid, hTi] at hm
    refine ⟨hne, ?_⟩
    rw [← ordL_map hσv (T a.rev a.rev)]
    exact (congrArg ordL hm.symm).trans (ordL_inv _)

  have e : ∀ (β : Fin (n / 2) → ℂ) (g : GU σ n), chiDeltaU q β g =
      ∏ i : Fin (n / 2), β i ^ ordL ((((g : GU σ n) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) (lo i) (lo i)) *
        (q : ℂ) ^ (-(ordL ((((g : GU σ n) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) (lo i) (lo i))) *
          ((n : ℤ) - 1 - 2 * (i.val : ℤ))) := by
    intro β g
    unfold chiDeltaU
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [dif_pos (by have := i.2; omega)]
    rfl
  have hact : ∀ i, (actU k α i : ℂ) = if i = k then (α k : ℂ)⁻¹ else α i := by
    intro i
    unfold actU
    rw [dif_neg hk]
    by_cases hi : i = k
    · subst hi; simp [Function.update_self, Units.val_inv_eq_inv_val]
    · simp [Function.update_of_ne hi, hi]
  have key : chiDeltaU q (fun i => (α i : ℂ)) b * (q : ℂ) ^ (-4 * ordL (T (lo k) (lo k))) =
      chiDeltaU q (fun i => (actU k α i : ℂ)) t := by
    rw [e, e, Fintype.prod_eq_mul_prod_compl k, Fintype.prod_eq_mul_prod_compl k]
    have hrest : ∏ i ∈ ({k}ᶜ : Finset (Fin (n / 2))),
        (α i : ℂ) ^ ordL ((((b : GU σ n) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) (lo i) (lo i)) *
          (q : ℂ) ^ (-(ordL ((((b : GU σ n) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) (lo i) (lo i))) *
            ((n : ℤ) - 1 - 2 * (i.val : ℤ))) =
        ∏ i ∈ ({k}ᶜ : Finset (Fin (n / 2))),
        (actU k α i : ℂ) ^ ordL ((((t : GU σ n) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) (lo i) (lo i)) *
          (q : ℂ) ^ (-(ordL ((((t : GU σ n) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) (lo i) (lo i))) *
            ((n : ℤ) - 1 - 2 * (i.val : ℤ))) := by
      refine Finset.prod_congr rfl fun i hi => ?_
      have hik : i ≠ k := by simpa using hi
      have hfix : Equiv.swap a a.rev (lo i) = lo i := by
        apply Equiv.swap_apply_of_ne_of_ne
        · intro h; apply hik; ext; have := congrArg Fin.val h; simpa [ha] using this
        · intro h; have := congrArg Fin.val h; rw [hrv] at this
          have h3 : (lo i : Fin n).val = i.val := rfl
          have := i.2; omega
      rw [hb, if_pos rfl, hfix, hact, if_neg hik]
    rw [hrest, hb, if_pos rfl, ← ha, Equiv.swap_apply_left, hTa.2, hact, if_pos rfl]
    have hE : ((n : ℤ) - 1 - 2 * (k.val : ℤ)) = 2 := by omega
    rw [hE]
    set o := ordL (T a a)
    set R := ∏ i ∈ ({k}ᶜ : Finset (Fin (n / 2))),
        (actU k α i : ℂ) ^ ordL ((((t : GU σ n) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) (lo i) (lo i)) *
          (q : ℂ) ^ (-(ordL ((((t : GU σ n) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) (lo i) (lo i))) *
            ((n : ℤ) - 1 - 2 * (i.val : ℤ)))
    have hqq : (q : ℂ) ^ (-(-o) * 2) * (q : ℂ) ^ (-4 * o) = (q : ℂ) ^ (-o * 2) := by
      rw [← zpow_add₀ hq]; ring_nf
    have hα : (α k : ℂ) ^ (-o) = ((α k : ℂ)⁻¹) ^ o := by rw [zpow_neg, inv_zpow]
    calc (α k : ℂ) ^ (-o) * (q : ℂ) ^ (-(-o) * 2) * R * (q : ℂ) ^ (-4 * o)
        = (α k : ℂ) ^ (-o) * ((q : ℂ) ^ (-(-o) * 2) * (q : ℂ) ^ (-4 * o)) * R := by ring
      _ = ((α k : ℂ)⁻¹) ^ o * (q : ℂ) ^ (-o * 2) * R := by rw [hqq, hα]
  rw [hprod, hsph]
  calc chiDeltaU q (fun i => (α i : ℂ)) b * φ (y⁻¹ * w * x) * (q : ℂ) ^ (-4 * ordL (T (lo k) (lo k)))
      = (chiDeltaU q (fun i => (α i : ℂ)) b * (q : ℂ) ^ (-4 * ordL (T (lo k) (lo k)))) * φ (y⁻¹ * w * x) := by ring
    _ = _ := by rw [key]

end GlobalTheory.WeylCell.U21TorusFactor
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryWeylSimpleReflectionRevCommSqEqOneStatement
section
open MeasureTheory GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.SatakeBound GlobalTheory.WeylCell Formalism.UG
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitaryWeylSimpleReflection_rev_comm_sq_eq_one : ∀ (n : ℕ) (k : Fin (n / 2)), (∀ i, simpleU k i.rev = (simpleU k i).rev) ∧ simpleU k * simpleU k = 1 := by
  first | exact @GlobalTheory.simpleU_rev_and_sq | exact GlobalTheory.simpleU_rev_and_sq | (intros; apply GlobalTheory.simpleU_rev_and_sq <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.VacuumRealRestrictionGaussianMulTheta
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField Matrix MvPolynomial
open GlobalTheory.SignedHC GlobalTheory.ChiGrid Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.FunObj
attribute [local instance] Formalism.BasicNotions.Host.cmStar

open GlobalTheory.FockCompare GlobalTheory.VacRealForm

namespace GlobalTheory.VacRealForm

theorem vacuum_real_form : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GlobalTheory.ChiGrid.GridData L sc} (W : G.Weil) {U : Set T} (N : GlobalTheory.FunObj.Std G U) (δ : ℂ), Formalism.MainNotions.StandardLatticesGL3.Crv D D.host.ccK δ → δ ≠ 0 → ∀ (t : T) (j : ℕ), j + 1 ≤ D.R.m → ∀ f, IsVacO W.ψ W.θ _ _ (G.cartS W.cart (.top t j)) (G.onT W.cart (.top t j)) (N.latS (.top t j) : Set _) (N.latT (.top t j) : Set _) f → ∃ θ : Formalism.MainNotions.TaylorLogMetric.VC D (G.pS (.top t j)).rank (G.pT (.top t j)).rank → ℂ, θ ∈ Formalism.MainNotions.TaylorLogMetric.Th D (Formalism.MainNotions.TaylorLogMetric.tor0 D D.host.ccK δ) (Formalism.MainNotions.StandardLatticesGL3.stdL D _) (Formalism.MainNotions.StandardLatticesGL3.stdL D _) ∧ θ ≠ 0 ∧ ∀ w : WO (G.pS (.top t j)) (G.pT (.top t j)), w.map (finPart D) = 0 → f w = Complex.exp (-((Real.pi * Formalism.L2.Pj.xiR D : ℝ) : ℂ) * ∑ τ, ∑ a, ∑ b, ((‖((N.frC (.top (j + 1)) τ)⁻¹ * compAt W.θ τ w * N.frC (.top j) τ) a b‖ ^ 2 : ℝ) : ℂ)) * θ (δ • (fun τ => (N.frC (.top (j + 1)) τ)⁻¹ * compAt W.θ τ w * N.frC (.top j) τ)) := by
  intro D T L sc G W U N δ hC hδ t j hj f hf
  obtain ⟨σ, hσ⟩ := GlobalTheory.RealLineAt.exists_inverse_chart hf.2.inf
  have hU : ∀ X τ, IsUnit (N.frC X τ).det := fun X τ => by
    show IsUnit ((tauE D τ).mapMatrix (N.fr X).1).det
    rw [← RingHom.map_det]
    exact (Matrix.isUnits_det_units (N.fr X)).map _
  have hs : ∀ Z : D.what₂.Tau → Fin (G.pT (.top t j)).rank → Fin (G.pS (.top t j)).rank → ℂ, δ⁻¹ • δ • Z = Z :=
    fun Z => inv_smul_smul₀ hδ Z
  refine ⟨thY σ (G.pS (.top t j)) (G.pT (.top t j)) (N.frC (.top j)) (N.frC (.top (j + 1))) f δ,
    ⟨?_, ?_⟩, ?_, ?_⟩
  · exact (GlobalTheory.T.differentiable_fockVacuum_gaussian_definitePair W N σ hσ t j hj f hf).comp (differentiable_id.const_smul δ⁻¹)
  · exact GlobalTheory.T.vacuum_realRestriction_satisfies_standardThetaLaw W N σ δ hσ hC hδ t j hj f hf
  · obtain ⟨z, hz⟩ := GlobalTheory.T.definite_pair_unit_vacuum_real_point_ne_zero W N σ hσ t j hj f hf
    intro h0
    apply hz
    have e : thY σ (G.pS (.top t j)) (G.pT (.top t j)) (N.frC (.top j)) (N.frC (.top (j + 1))) f δ
        (δ • fun τ => ((N.frC (.top (j + 1)) τ)⁻¹ * Matrix.of (z τ) * N.frC (.top j) τ : Matrix _ _ ℂ)) = 0 :=
      congrFun h0 _
    unfold thY gZ at e
    erw [hs] at e
    rw [mul_eq_zero] at e
    rcases e with e | e
    · convert e using 3
      funext τ
      simp only [frPt, Matrix.of_apply]
      rw [show Matrix.of ((N.frC (.top (j + 1)) τ)⁻¹ * Matrix.of (z τ) * N.frC (.top j) τ) =
        (N.frC (.top (j + 1)) τ)⁻¹ * Matrix.of (z τ) * N.frC (.top j) τ from rfl,
        ← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ (hU _ τ), Matrix.one_mul, Matrix.mul_assoc,
        Matrix.mul_nonsing_inv _ (hU _ τ), Matrix.mul_one]
      rfl
    · exact absurd e (Complex.exp_ne_zero _)
  · intro w hw
    unfold thY gZ
    erw [hs]
    have e1 : frPt (N.frC (.top j)) (N.frC (.top (j + 1)))
        (fun τ => ((N.frC (.top (j + 1)) τ)⁻¹ * compAt W.θ τ w * N.frC (.top j) τ : Matrix _ _ ℂ)) =
        piW W.θ (G.pT (.top t j)) (G.pS (.top t j)) w := by
      funext τ
      simp only [frPt]
      rw [show Matrix.of ((N.frC (.top (j + 1)) τ)⁻¹ * compAt W.θ τ w * N.frC (.top j) τ) =
        (N.frC (.top (j + 1)) τ)⁻¹ * compAt W.θ τ w * N.frC (.top j) τ from rfl,
        ← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ (hU _ τ), Matrix.one_mul, Matrix.mul_assoc,
        Matrix.mul_nonsing_inv _ (hU _ τ), Matrix.mul_one]
      rfl
    rw [e1, hσ.iota_pi hw, ← mul_assoc, mul_comm _ (f w), mul_assoc, ← Complex.exp_add]
    have e2 : -((Real.pi * Formalism.L2.Pj.xiR D : ℝ) : ℂ) * ∑ τ, ∑ a, ∑ b,
        ((‖((N.frC (.top (j + 1)) τ)⁻¹ * compAt W.θ τ w * N.frC (.top j) τ) a b‖ ^ 2 : ℝ) : ℂ) +
        ((Real.pi * Formalism.L2.Pj.xiR D * sqSum (fun τ => ((N.frC (.top (j + 1)) τ)⁻¹ * compAt W.θ τ w * N.frC (.top j) τ : Matrix _ _ ℂ)) : ℝ) : ℂ) = 0 := by
      simp only [sqSum]
      push_cast
      ring
    rw [e2, Complex.exp_zero, mul_one]

end GlobalTheory.VacRealForm
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilDatumUniqueOnThetaFunctions
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum GlobalTheory.WeilParts MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.WeilUniq

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {χS χT : (AE D)ˣ →* Circle}
  {om om' : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)}

theorem om_om_inv (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)) (p : GA D S × GA D T) (f : WO S T → ℂ) :
    om p (om p⁻¹ f) = f := by
  rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]

theorem om_inv_om (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)) (p : GA D S × GA D T) (f : WO S T → ℂ) :
    om p⁻¹ (om p f) = f := by
  rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]

theorem exists_scalar (H : IsWeilDatumO ψ S T χS χT om) (H' : IsWeilDatumO ψ S T χS χT om') (p : GA D S × GA D T) :
    ∃ c : Circle, ∀ f, IsThetaFunO ψ S T f → om p f = (c : ℂ) • om' p f := by
  obtain ⟨c, hc, h⟩ := GlobalTheory.T.schurLemma_thetaFunctions_orientedPair D ψ H.std S T (om' p⁻¹ * om p)
    (fun f hf => H'.om_pres _ _ (H.om_pres _ _ hf))
    (fun w f hf => by
      obtain ⟨g, h⟩ := p
      have e := GlobalTheory.AdelicLatMove.actO_actO_inv S T g⁻¹ h⁻¹ w
      rw [inv_inv, inv_inv] at e
      rw [Module.End.mul_apply, Module.End.mul_apply, H.om_heis g h w f hf, Prod.inv_mk,
        H'.om_heis _ _ _ _ (H.om_pres _ _ hf), e])
    (fun μ 𝓕 hμ h𝓕 f hf => by
      rw [Module.End.mul_apply, H'.om_unit μ 𝓕 hμ h𝓕 _ _ (H.om_pres _ _ hf), H.om_unit μ 𝓕 hμ h𝓕 _ _ hf])
  refine ⟨⟨c, mem_sphere_zero_iff_norm.2 hc⟩, fun f hf => ?_⟩
  have := congrArg (om' p) (h f hf)
  rwa [Module.End.mul_apply, om_om_inv, map_smul] at this

theorem exists_ne_zero_at_zero (hψ : IsStdChar D ψ (-1)) {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) (h0 : f ≠ 0) :
    ∃ f₀, IsThetaFunO ψ S T f₀ ∧ f₀ 0 ≠ 0 := by
  obtain ⟨w, hw⟩ := Function.ne_iff.1 h0
  refine ⟨heisO ψ S T w f, GlobalTheory.ThetaClosed.isThetaFunO_heisO_all hψ hf w, ?_⟩
  unfold heisO
  rw [zero_add]
  refine mul_ne_zero ?_ hw
  exact (ψ.val_isUnit _).ne_zero

theorem exists_isDetAt {e : AE D} (he : e * e = e) (V : HSp D) (g : GA D V) : ∃ y, IsDetAt e V g y :=
  ⟨Units.mkOfMulEqOne (e * (Formalism.L2.Theta.mt V g).det + (1 - e)) (e * cA D (Formalism.L2.Theta.mt V g).det + (1 - e)) (by
    linear_combination (e * e) * det_conj_mul V g +
      (2 - (Formalism.L2.Theta.mt V g).det - cA D (Formalism.L2.Theta.mt V g).det) * he), Units.val_mkOfMulEqOne _⟩

theorem suppAt_one (e : AE D) (V : HSp D) : SuppAt e V 1 := by
  intro i j
  rw [GlobalTheory.AdelicLatMove.mt_one, sub_self, Matrix.zero_apply, mul_zero]

theorem scalar_split (H : IsWeilDatumO ψ S T χS χT om) (H' : IsWeilDatumO ψ S T χS χT om') {e : AE D}
    (he : IsSplitIdem D e) {g : GA D S} {h : GA D T} (hg : SuppAt e S g) (hh : SuppAt e T h) {c : Circle}
    (hc : ∀ f, IsThetaFunO ψ S T f → om (g, h) f = (c : ℂ) • om' (g, h) f) : c = 1 := by
  obtain ⟨x, hx⟩ := exists_isDetAt he.1 S g
  obtain ⟨y, hy⟩ := exists_isDetAt he.1 T h
  obtain ⟨r, hr, h1⟩ := H.om_split e he g h hg hh x y hx hy
  obtain ⟨r', hr', h2⟩ := H'.om_split e he g h hg hh x y hx hy
  obtain ⟨ℓ, hℓ, f, hf, hne⟩ := GlobalTheory.T.exists_split_place_half_heisenberg_invariant_form D ψ H.std S T e he
  have e1 := h1 ℓ hℓ f hf
  rw [hc f hf, map_smul, h2 ℓ hℓ f hf, smul_eq_mul] at e1
  have e2 : (c : ℂ) * r' = r := by
    apply mul_right_cancel₀ (mul_ne_zero (Circle.coe_ne_zero (splitFacO χS χT x y)) hne)
    linear_combination e1
  have e3 : r' = r := by
    have := congrArg norm e2
    rwa [norm_mul, Circle.norm_coe, one_mul, Complex.norm_real, Complex.norm_real, Real.norm_of_nonneg hr.le,
      Real.norm_of_nonneg hr'.le] at this
  subst e3
  apply Circle.ext
  apply mul_right_cancel₀ (Complex.ofReal_ne_zero.2 hr.ne')
  rw [e2, Circle.coe_one, one_mul]

theorem weilDatum_unique : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om om' : (GA D S × GA D T →* Module.End ℂ (WO S T → ℂ))), IsWeilDatumO ψ S T χS χT om → IsWeilDatumO ψ S T χS χT om' → ∀ p f, IsThetaFunO ψ S T f → om p f = om' p f := by
  intro D ψ hψ S T χS χT om om' H H' p f hf
  by_cases h0 : f = 0
  · rw [h0, map_zero, map_zero]
  obtain ⟨f₀, hf₀, h00⟩ := exists_ne_zero_at_zero hψ hf h0
  have hne : ∀ q, om' q f₀ ≠ 0 := fun q hq => by
    have := om_inv_om om' q f₀
    rw [hq, map_zero] at this
    exact h00 (by rw [← this]; rfl)
  choose c hc using exists_scalar H H'
  have hmul : ∀ q q', c (q * q') = c q * c q' := fun q q' => by
    apply Circle.ext
    apply smul_left_injective ℂ (hne (q * q'))
    have := hc (q * q') f₀ hf₀
    dsimp only
    rw [← this, map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, hc q' f₀ hf₀, map_smul,
      hc q _ (H'.om_pres _ _ hf₀), smul_smul, Circle.coe_mul, mul_comm]
  have hcont : Continuous c := by
    refine continuous_induced_rng.2 (continuous_iff_continuousAt.2 fun q => ?_)
    obtain ⟨w, hw⟩ := Function.ne_iff.1 (hne q)
    have h1 : ContinuousAt (fun q' => om q' f₀ w / om' q' f₀ w) q :=
      (H.om_cont f₀ hf₀ w).continuousAt.div (H'.om_cont f₀ hf₀ w).continuousAt hw
    refine h1.congr ?_
    filter_upwards [(H'.om_cont f₀ hf₀ w).continuousAt.eventually_ne hw] with q' hq'
    rw [hc q' f₀ hf₀, Pi.smul_apply, smul_eq_mul, mul_div_cancel_right₀ _ hq']
    rfl
  have hrat : ∀ γ ∈ GQ S, ∀ γ' ∈ GQ T, c (γ, γ') = 1 := fun γ hγ γ' hγ' => by
    have h1 := congrFun (hc (γ, γ') f₀ hf₀) 0
    rw [Pi.smul_apply, H.om_aut γ hγ γ' hγ' f₀ hf₀, H'.om_aut γ hγ γ' hγ' f₀ hf₀, smul_eq_mul] at h1
    apply Circle.ext
    apply mul_right_cancel₀ h00
    rw [← h1, Circle.coe_one, one_mul]
  let ν : GA D S × GA D T →* Circle := MonoidHom.mk' c hmul
  have hS := GlobalTheory.T.unitary_adelic_character_trivial_rat_and_split D S (ν.comp (MonoidHom.inl _ _)) (hcont.comp (Continuous.prodMk_left _))
    (fun γ hγ => hrat γ hγ 1 (one_mem _))
    (fun e he g hg => scalar_split H H' he hg (suppAt_one e T) (hc (g, 1)))
  have hT := GlobalTheory.T.unitary_adelic_character_trivial_rat_and_split D T (ν.comp (MonoidHom.inr _ _)) (hcont.comp (Continuous.prodMk_right _))
    (fun γ hγ => hrat 1 (one_mem _) γ hγ)
    (fun e he h hh => scalar_split H H' he (suppAt_one e S) hh (hc (1, h)))
  have h1 : c p = 1 := by
    have e : p = (p.1, 1) * (1, p.2) := by rw [Prod.mk_mul_mk, mul_one, one_mul]
    rw [e, hmul, show c (p.1, 1) = 1 from hS p.1, show c (1, p.2) = 1 from hT p.2, mul_one]
  rw [hc p f hf, h1, Circle.coe_one, one_smul]

end GlobalTheory.WeilUniq
end

