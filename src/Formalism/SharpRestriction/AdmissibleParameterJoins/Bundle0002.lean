import Formalism.SharpRestriction.GrowthBounds.SmallOrderPrimes
import Formalism.SharpRestriction.GlobalSchurBounds.CMFieldLemmas
import Formalism.SharpRestriction.GlobalSchurBounds.Bundle0001
import Formalism.SharpRestriction.GrowthBounds.Bundle0002
import Formalism.SharpRestriction.Divisibility.SchurIrreducible
import Formalism.SharpRestriction.CuspSpanNormBounds.PlaceDegreeData
import Mathlib
import Formalism.SharpRestriction.AdmissibleParameterJoins.SfromGLa
import Formalism.SharpRestriction.GlobalSchurBounds.StandardLattice

-- bundled from Formalism.SharpRestriction.AdmissibleParameterJoins.GandSa
section
noncomputable section

namespace Formalism.MainNotions.J

open Formalism.BasicNotions Formalism.MainNotions.G
open scoped BigOperators

variable {D : D7} {L : SizeData₂ D}

def posOn (D : D7) (h t0 : HH D) (T : Finset (HH D)) : Finset (Fin (addOrderOf h)) :=
  Finset.univ.filter (fun i => t0 + (i : ℕ) • h ∈ T)

def BadOrb (X : Inst D L) (h t : HH D) (T : Finset (HH D)) : Prop :=
  ¬ IsGoodOrbit (addOrderOf h) (posOn D h (X.bs h t) T) (L2 D L.sc) (KG L.sc) (rG L.sc) L.sc.delta1
    (hG L.sc) L.sc.x

open Classical in

def BadProb (X : Inst D L) (Cb : ℝ) : Prop :=
  ∀ h : HH D, L.sc.x ^ (L.sc.eps / 4) ≤ (addOrderOf h : ℝ) → ∀ t : HH D,
    (∑ T : Finset (HH D), if t ∈ T ∧ BadOrb X h t T then UnusedSlot33.bern L.sc.delta1 T else 0) ≤
      (Cb * L.sc.x ^ (-2 : ℝ)) * L.sc.delta1

open Classical in

def TopsOK (X : Inst D L) (Cb : ℝ) (T : Finset (HH D)) : Prop :=
  L.sc.delta1 * D.R.n / 2 ≤ (T.card : ℝ) ∧ (T.card : ℝ) ≤ 2 * L.sc.delta1 * D.R.n ∧
  ∑ p ∈ largeOrderResiduePrimes L, Real.log p / p * ((T.filter (fun t => BadOrb X (hP D p) t T)).card : ℝ) ≤
    4 * (Cb * L.sc.x ^ (-2 : ℝ)) * L.sc.delta1 * D.R.n * ∑ p ∈ largeOrderResiduePrimes L, Real.log p / p

theorem delta1_pos (s : Scale) : 0 < s.delta1 := by
  unfold Scale.delta1
  exact Real.rpow_pos_of_pos (by linarith [s.one_lt_alt]) _

theorem delta1_le_one (s : Scale) : s.delta1 ≤ 1 := by
  unfold Scale.delta1
  exact Real.rpow_le_one_of_one_le_of_nonpos (le_of_lt s.one_lt_alt) (by linarith [s.eps_pos])

theorem badOrb_congr (X : Inst D L) (h t : HH D) (T T' : Finset (HH D))
    (hT : ∀ x ∈ UnusedSlot33.coset t h, (x ∈ T ↔ x ∈ T')) : BadOrb X h t T ↔ BadOrb X h t T' := by
  unfold BadOrb
  have hpos : posOn D h (X.bs h t) T = posOn D h (X.bs h t) T' := by
    unfold posOn
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    apply hT
    obtain ⟨i, hi⟩ := X.bs_orb h t
    generalize X.bs h t = b at hi ⊢
    subst hi
    simp only [UnusedSlot33.coset, Set.mem_setOf_eq]
    refine ⟨((j : ℕ) : ℤ) - (i : ℤ), ?_⟩
    rw [sub_smul, natCast_zsmul, natCast_zsmul]
    abel
  rw [hpos]

theorem tops_exist_of (X : Inst D L) (Cb : ℝ) (h6 : UnusedSlot33.Conclusion6 D L.sc) (h16 : 16 ≤ L.sc.delta1 * D.R.n)
    (h32 : BadProb X Cb) : ∃ T : Finset (HH D), TopsOK X Cb T := by
  have hmem : ∀ p ∈ largeOrderResiduePrimes L, L.sc.x ^ (L.sc.eps / 4) ≤ (addOrderOf (hP D p) : ℝ) := by
    intro p hp
    unfold largeOrderResiduePrimes at hp
    exact (Finset.mem_filter.mp hp).2.2.2
  obtain ⟨T, h1, h2, h3⟩ := h6 L.sc.delta1 (delta1_pos L.sc) (delta1_le_one L.sc) h16
    (Cb * L.sc.x ^ (-2 : ℝ)) (fun h t T => BadOrb X h t T)
    (fun h t T T' hT => badOrb_congr X h t T T' hT) h32 (largeOrderResiduePrimes L) (hP D) (fun p => Real.log p / p) hmem
    (fun p _ => div_nonneg (Real.log_natCast_nonneg p) (Nat.cast_nonneg p))
  exact ⟨T, h1, h2, h3⟩

theorem frobenius_step_large_order {p : ℕ} (hp : IsResidueClassZero D p) : stepP D p = hP D p := by
  simp [stepP, IsSg, hp]

theorem badOrb_TT (X : Inst D L) {p : ℕ} (hp : IsResidueClassZero D p) (t : HH D) :
    BadOrb X (hP D p) t D.host.TT ↔ ¬ Good X p (X.bs (stepP D p) t) := by
  rw [frobenius_step_large_order hp]
  try exact Iff.rfl

theorem primes_eq (L : SizeData₂ D) :
    (AuxBlock8.primesResidueBelow D L.sc.X').filter
      (fun p => L.sc.x ^ (L.sc.eps / 4) ≤ (addOrderOf (hP D p) : ℝ)) = largeOrderResiduePrimes L := by
  ext p
  unfold largeOrderResiduePrimes AuxBlock8.primesResidueBelow
  simp only [Finset.mem_filter, Finset.mem_range]
  constructor
  · rintro ⟨⟨h1, h2, h3, h4⟩, h5⟩
    exact ⟨h1, h2, h4, h5⟩
  · rintro ⟨h1, h2, h4, h5⟩
    exact ⟨⟨h1, h2, Nat.lt_ceil.mp h1, h4⟩, h5⟩

theorem tops_share_bound (D : D7) (L : SizeData₂ D) (X : Inst D L) (Cb S : ℝ) (hCb : 0 ≤ Cb)
    (h : TopsOK X Cb D.host.TT) (hS : ∑ p ∈ largeOrderResiduePrimes L, Real.log p / p ≤ S)
    (hbig : 8 * Cb * S ≤ L.sc.x ^ L.sc.eps) : Formalism.MainNotions.AuxBlock8.adm2 D L X := by
  classical
  obtain ⟨h1, h2, h3⟩ := h
  have hx : 0 < L.sc.x := by linarith [L.sc.one_lt_alt]
  have hδ := delta1_pos L.sc
  have hc0 : ∀ p ∈ largeOrderResiduePrimes L, IsResidueClassZero D p := by
    intro p hp
    unfold largeOrderResiduePrimes at hp
    exact (Finset.mem_filter.mp hp).2.2.1
  have hS0 : 0 ≤ S := le_trans (Finset.sum_nonneg
    (fun p _ => div_nonneg (Real.log_natCast_nonneg p) (Nat.cast_nonneg p))) hS
  have hx2 : 0 ≤ L.sc.x ^ (-2 : ℝ) := Real.rpow_nonneg hx.le _
  have hco : 0 ≤ 4 * (Cb * L.sc.x ^ (-2 : ℝ)) * L.sc.delta1 * D.R.n :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (mul_nonneg hCb hx2)) hδ.le) (Nat.cast_nonneg _)
  refine ⟨⟨by linarith, by linarith⟩, ?_⟩
  unfold AuxBlock8.BTT
  rw [primes_eq L]
  calc ∑ p ∈ largeOrderResiduePrimes L, Real.log p / p *
          ((D.host.TT.filter (fun t => ¬ Good X p (X.bs (stepP D p) t))).card : ℝ)
      = ∑ p ∈ largeOrderResiduePrimes L, Real.log p / p *
          ((D.host.TT.filter (fun t => BadOrb X (hP D p) t D.host.TT)).card : ℝ) := by
        apply Finset.sum_congr rfl
        intro p hp
        rw [Finset.filter_congr (fun t _ => (badOrb_TT X (hc0 p hp) t).symm)]
    _ ≤ 4 * (Cb * L.sc.x ^ (-2 : ℝ)) * L.sc.delta1 * D.R.n * ∑ p ∈ largeOrderResiduePrimes L, Real.log p / p := h3
    _ ≤ 4 * (Cb * L.sc.x ^ (-2 : ℝ)) * L.sc.delta1 * D.R.n * S := mul_le_mul_of_nonneg_left hS hco
    _ ≤ (D.host.TT.card : ℝ) * L.sc.x ^ (-2 + L.sc.eps) := by
        rw [Real.rpow_add hx]
        have hCS : 0 ≤ Cb * S := mul_nonneg hCb hS0
        have hT : L.sc.delta1 * D.R.n ≤ 2 * D.host.TT.card := by linarith
        nlinarith [mul_le_mul_of_nonneg_left hT (mul_nonneg hx2 hCS),
          mul_le_mul_of_nonneg_left hbig (mul_nonneg hx2 (Nat.cast_nonneg D.host.TT.card : (0 : ℝ) ≤ _))]

end Formalism.MainNotions.J

end
end

-- bundled from Formalism.SharpRestriction.AdmissibleParameterJoins.GandSb
section
noncomputable section

namespace Formalism.MainNotions.J

open Formalism.BasicNotions Formalism.MainNotions.G Formalism.MainNotions.UnusedSlot33 NumberField IsDedekindDomain
open scoped TensorProduct

def ArithLevel (D : D7) {p : ℕ} (G : GAtP p) : Prop :=
  ∃ (σ : D.host.E →ₐ[D.host.F] D.host.E) (J : Matrix (Fin D.R.k) (Fin D.R.k) D.host.E) (g : ℕ)
    (v : HeightOneSpectrum (𝓞 D.host.F)),
    (∀ x, σ x = D.host.conj x) ∧ IsHerm (σ : D.host.E →+* D.host.E) J ∧ IsDef σ J ∧ g.Prime ∧
    2 * D.R.f * D.R.k < g - 1 ∧ ((g : 𝓞 D.host.F) ∈ v.asIdeal) ∧
    letI := tensTop (F := D.host.F) (E := D.host.E) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)
    letI := tensTop (F := D.host.F) (E := D.host.E) (v.adicCompletion D.host.F)
    ∃ (U : Subgroup (GL (Fin D.R.k) (D.host.E ⊗[D.host.F] FiniteAdeleRing (𝓞 D.host.F) D.host.F)))
      (Uw : Subgroup (GL (Fin D.R.k) (D.host.E ⊗[D.host.F] v.adicCompletion D.host.F))),
      U ≤ UPts σ J (FiniteAdeleRing (𝓞 D.host.F) D.host.F) ∧
      IsCompact (U : Set (GL (Fin D.R.k) (D.host.E ⊗[D.host.F] FiniteAdeleRing (𝓞 D.host.F) D.host.F))) ∧
      IsOpen {x : UPts σ J (FiniteAdeleRing (𝓞 D.host.F) D.host.F) | (x : GL _ _) ∈ U} ∧
      IsProG g Uw ∧ (∀ u ∈ U, bc (prV v) u ∈ Uw) ∧
      ∀ i : G.comp, ∃ emb : (G.lev i).Γ →*
          GL (Fin D.R.k) (D.host.E ⊗[D.host.F] FiniteAdeleRing (𝓞 D.host.F) D.host.F),
        Function.Injective emb ∧
        (∀ γ, emb γ ∈ ratPts σ J (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) ∧
        ∀ L : G.P.Tup, G.P.IsLatTup L →
          ∃ y ∈ UPts σ J (FiniteAdeleRing (𝓞 D.host.F) D.host.F),
            ∀ γ, (G.lev i).smul γ L = L → emb γ ∈ U.map (MulAut.conj y).toMonoidHom

end Formalism.MainNotions.J

end
end

-- bundled from Formalism.SharpRestriction.AdmissibleParameterJoins.GandSc
section
noncomputable section

namespace Formalism.MainNotions.J

section MatTransport

open Matrix

variable {p q n : ℕ} (e : (Fin p ⊕ Fin q) ≃ Fin n) (ε : Fin n → Bool)

def trIx (M : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) : Matrix (Fin n) (Fin n) ℂ := Matrix.reindex e e M

end MatTransport

open Formalism.BasicNotions.TH Formalism.MainNotions.S
open scoped Matrix

def DSTieAt (X : ProvA) (p q : ℕ) (lam : Ix p q → ℚ) (e : Ix p q ≃ Fin (p + q)) (ε : Fin (p + q) → Bool)
    (lamS : Fin (p + q) → ℝ) (c : ℝ)
    (σ : Matrix (Fin (p + q)) (Fin (p + q)) ℂ → ((X.ds p q lam).U.H →L[ℂ] (X.ds p q lam).U.H))
    (χ : (X.grp p q).G → ℂ) (E : (X.ds p q lam).U.H →L[ℂ] (X.ds p q lam).U.H) : Prop :=
    (∀ a, ε (e a) = a.isLeft) ∧ (∀ a, lamS (e a) = (lam a : ℝ) + c) ∧ Formalism.QuantumDeterminants.IsHCParam lamS ∧
    IsDS ε lamS σ ∧ (∀ g, ‖χ g‖ = 1) ∧ (∀ Y ∈ pR p q, χ ((X.grp p q).expt Y) = 1) ∧
    (∀ g, (X.ds p q lam).U.π g = χ g • σ (trIx e (((X.grp p q).cov g : GL (Ix p q) ℂ) : Mat p q))) ∧
    Formalism.MainNotions.SchurIrreducible.isoVec (X.ds p q lam) (blattner lam) ⊆ (lowKSub ε lamS σ : Set (X.ds p q lam).U.H) ∧
    IsOrthProjOnto E (lowKSub ε lamS σ)

def DSTie (X : ProvA) (p q : ℕ) (lam : Ix p q → ℚ) : Prop :=
  ∃ e ε lamS c σ χ E, DSTieAt X p q lam e ε lamS c σ χ E

def DSTies (X : ProvA) : Prop := ∀ (p q : ℕ) (lam : Ix p q → ℚ), IsParam lam → DSTie X p q lam

section Transport

variable {p q : ℕ} (e : Ix p q ≃ Fin (p + q)) (ε : Fin (p + q) → Bool) (hε : ∀ a, ε (e a) = a.isLeft)

include hε

end Transport

end Formalism.MainNotions.J

end
end

-- bundled from Formalism.SharpRestriction.AdmissibleParameterJoins.SfromGLb
section
noncomputable section

namespace Formalism.MainNotions.J

open NumberField Formalism.HermitianLatticesTheory Formalism.BasicNotions

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem stdForm_apply (K : Type) [Field K] [StarRing K] (M : ℕ) (x y : Fin M → K) :
    StandardLattice.stdForm K M x y = ∑ i, star (x i) * y i := rfl

theorem std_ortho (K : Type) [Field K] [NumberField K] [StarRing K] (M : ℕ) :
    IsOrthoLattice (StandardLattice.stdForm K M) (StandardLattice.stdLat K M) M := by
  have e : (fun i : Fin M => (Pi.single i 1 : Fin M → K)) = Pi.basisFun K (Fin M) := by
    funext i; simp
  refine ⟨fun i => Pi.single i 1, ?_, ?_, rfl, fun i j => ?_⟩
  · rw [e]; exact (Pi.basisFun K (Fin M)).linearIndependent
  · rw [e]; exact (Pi.basisFun K (Fin M)).span_eq
  · by_cases hij : i = j
    · subst hij; simp [stdForm_apply, Pi.single_apply]
    · simp [stdForm_apply, Pi.single_apply, hij, Ne.symm hij]

theorem massRatio_host_of (D : D7) (h : StandardLattice.MassRatio₂ D) : ∀ (j : ℕ), 3 ≤ j →
    ∀ (V V' : Type) [AddCommGroup V] [Module D.host.E V] [Module (𝓞 D.host.E) V]
      [IsScalarTower (𝓞 D.host.E) D.host.E V] [AddCommGroup V'] [Module D.host.E V']
      [Module (𝓞 D.host.E) V'] [IsScalarTower (𝓞 D.host.E) D.host.E V']
      (h : V →ₗ⋆[D.host.E] V →ₗ[D.host.E] D.host.E) (h' : V' →ₗ⋆[D.host.E] V' →ₗ[D.host.E] D.host.E)
      (L : Submodule (𝓞 D.host.E) V) (L' : Submodule (𝓞 D.host.E) V'),
      h.IsSymm → h'.IsSymm → IsOrthoLattice h L j → IsOrthoLattice h' L' (j - 1) →
      mass h L / mass h' L' = massRatioRightSide D.host.E j := by
  intro j hj V V' _ _ _ _ _ _ _ _ hV hV' L L' _ _ hL hL'
  rw [mass_ortho_eq hL (std_ortho D.host.E j), mass_ortho_eq hL' (std_ortho D.host.E (j - 1))]
  exact h j hj

theorem massRatio_all_of (h : StandardLattice.SiegelMassRatioCM) : SiegelMassRatio := by
  intro K _ _ _ hK M hM V V' _ _ _ _ _ _ _ _ hV hV' L L' _ _ hL hL'
  rw [mass_ortho_eq hL (std_ortho K M), mass_ortho_eq hL' (std_ortho K (M - 1))]
  exact h K hK M hM

theorem zetaR_eq (M : ℕ) (hM : 2 ≤ M) : (riemannZeta (M : ℂ)).re = StandardLattice.zetaR M := by
  have h1 : (1 : ℝ) < ((M : ℂ)).re := by
    simp only [Complex.natCast_re]; exact_mod_cast hM
  rw [zeta_eq_tsum_one_div_nat_add_one_cpow h1]
  have h2 : (∑' n : ℕ, 1 / ((n : ℂ) + 1) ^ (M : ℂ)) = ((StandardLattice.zetaR M : ℝ) : ℂ) := by
    unfold StandardLattice.zetaR
    rw [Complex.ofReal_tsum]
    refine tsum_congr fun n => ?_
    rw [Complex.cpow_natCast]
    push_cast
    rfl
  rw [h2, Complex.ofReal_re]

theorem lBound_host_of (D : D7) (h : StandardLattice.gram_det_kernel_dual_lattice D) : ∀ i : ℕ, 2 ≤ i →
    |Real.log (lValEta D.host.E i)| ≤ (D.R.f : ℝ) * Real.log (riemannZeta (i : ℂ)).re := by
  intro i hi
  rw [zetaR_eq i hi]
  exact h i hi

end Formalism.MainNotions.J

end
end

