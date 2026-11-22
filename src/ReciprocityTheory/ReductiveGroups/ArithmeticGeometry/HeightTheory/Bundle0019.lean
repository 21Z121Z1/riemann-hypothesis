import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.Bundle0018
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.Bundle0009
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.Bundle0011
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.Bundle0015
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.Bundle0008
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.HNormPtsA
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.Bundle0012

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.BasisBlock0
section
namespace ReciprocityTheory.ChartRestriction.G.T0

open NumberField

variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι]
  {Ω : ι → Type} [∀ c, Field (Ω c)] [∀ c, Algebra K (Ω c)]
  {WT : Type} [AddCommGroup WT]
  {A : ι → Type} [∀ c, CommRing (A c)] [∀ c, Algebra (Ω c) (A c)] [∀ c, Algebra K (A c)]
  [∀ c, Algebra (𝓞 K) (A c)]
  {𝒜 : (c : ι) → WT → Submodule (Ω c) (A c)}

namespace Data

variable (d : Data K ι Ω WT A)

theorem basis_block0 (hd : d.AxH 𝒜) (h : d.S1) (c : ι) :
    letI : Algebra (KTf K d.D d.N) (OmS (Ω c) d.D d.N) := (d.KTtoS h c).toAlgebra;
    ∃ (n : ℕ) (b : Module.Basis (Fin n) (KTf K d.D d.N) (OmS (Ω c) d.D d.N)) (Q0 : KTp K d.D d.N)
      (M : Fin (d.N + 1) → Matrix (Fin n) (Fin n) (KTp K d.D d.N)),
      Q0 ≠ 0 ∧ (∀ x, d.sub0 x Q0 = Q0) ∧ (∀ j a a' x, d.sub0 x (M j a a') = M j a a') ∧
      ∀ j, Algebra.leftMulMatrix b (algebraMap (Ω c) (OmS (Ω c) d.D d.N)
          (ratio (Ω := Ω c) (d.w j c) (d.w (d.jc c) c))) =
        (M j).map fun q => algebraMap (KTp K d.D d.N) (KTf K d.D d.N) q /
          algebraMap (KTp K d.D d.N) (KTf K d.D d.N) Q0 := by
  letI _inst : Algebra (KTf K d.D d.N) (OmS (Ω c) d.D d.N) := (d.KTtoS h c).toAlgebra
  obtain ⟨L, E, _, _, _, _, eL, eE, hcomp, hconst, hLc⟩ := d.decomp_block0 hd h c
  letI iLY : Algebra (FractionRing (MvPolynomial (Fin (d.N + 1)) L))
      (FractionRing (MvPolynomial (Fin (d.N + 1)) E)) :=
    (VariableBasisExtension.liftY (L := L) (E := E) (σ := Fin (d.N + 1))).toAlgebra
  obtain ⟨b', _, hb'2⟩ := VariableBasisExtension.basis_extend (σ := Fin (d.N + 1)) (Module.finBasis L E)
  letI iFO : Algebra (FractionRing (MvPolynomial (Fin (d.N + 1)) L)) (OmS (Ω c) d.D d.N) :=
    ((d.KTtoS h c).comp eL.symm.toRingHom).toAlgebra
  have hback : ∀ q : FractionRing (MvPolynomial (Fin (d.N + 1)) L),
      eE.symm (VariableBasisExtension.liftY q) = d.KTtoS h c (eL.symm q) := by
    intro q
    have h1 := hcomp (eL.symm q)
    rw [RingEquiv.apply_symm_apply] at h1
    rw [← h1, RingEquiv.symm_apply_apply]
  let eEl : FractionRing (MvPolynomial (Fin (d.N + 1)) E) ≃ₗ[FractionRing (MvPolynomial (Fin (d.N + 1)) L)]
      OmS (Ω c) d.D d.N :=
    AddEquiv.toLinearEquiv eE.symm.toAddEquiv (by
      intro q x
      show eE.symm (q • x) = q • eE.symm x
      rw [Algebra.smul_def, Algebra.smul_def, map_mul]
      congr 1
      exact hback q)
  let B0 := b'.map eEl
  let B : Module.Basis (Fin (Module.finrank L E)) (KTf K d.D d.N) (OmS (Ω c) d.D d.N) :=
    B0.mapCoeffs eL.symm (fun q x => rfl)
  have htr : ∀ (y : OmS (Ω c) d.D d.N) a a', Algebra.leftMulMatrix B y a a' =
      eL.symm (Algebra.leftMulMatrix b' (eE y) a a') := by
    intro y a a'
    rw [Algebra.leftMulMatrix_eq_repr_mul, Algebra.leftMulMatrix_eq_repr_mul]
    have hy : eEl.symm (y * eEl (b' a')) = eE y * b' a' := by
      show eE (y * eE.symm (b' a')) = eE y * b' a'
      rw [map_mul, RingEquiv.apply_symm_apply]
    simp only [B]
    erw [Module.Basis.mapCoeffs_apply, Module.Basis.mapCoeffs_repr]
    simp only [LinearEquiv.trans_apply, LinearEquiv.restrictScalars_apply, Finsupp.mapRange.linearEquiv_apply,
      Finsupp.mapRange_apply, B0, Module.Basis.map_apply, Module.Basis.map_repr]
    rw [hy]
    exact rfl
  choose e he using hconst
  choose P Q hQ hPinv hQinv hPQ using hLc
  let mm : Fin (d.N + 1) × Fin (Module.finrank L E) × Fin (Module.finrank L E) → L := fun t =>
    Algebra.leftMulMatrix (Module.finBasis L E)
      (e (ratio (Ω := Ω c) (d.w t.1 c) (d.w (d.jc c) c))) t.2.1 t.2.2
  have hinj := IsFractionRing.injective (KTp K d.D d.N) (KTf K d.D d.N)
  have hne : ∀ t, algebraMap (KTp K d.D d.N) (KTf K d.D d.N)
      (∏ s ∈ Finset.univ.erase t, Q (mm s)) ≠ 0 := by
    intro t
    rw [map_ne_zero_iff _ hinj]
    exact Finset.prod_ne_zero_iff.mpr fun s _ => hQ _
  have hfrac : ∀ t, algebraMap (KTp K d.D d.N) (KTf K d.D d.N) (P (mm t)) /
        algebraMap (KTp K d.D d.N) (KTf K d.D d.N) (Q (mm t)) =
      algebraMap (KTp K d.D d.N) (KTf K d.D d.N) (P (mm t) * ∏ s ∈ Finset.univ.erase t, Q (mm s)) /
        algebraMap (KTp K d.D d.N) (KTf K d.D d.N) (∏ s, Q (mm s)) := by
    intro t
    rw [← Finset.mul_prod_erase Finset.univ (fun s => Q (mm s)) (Finset.mem_univ t), map_mul, map_mul,
      mul_div_mul_right _ _ (hne t)]
  have hLtoC : ∀ l : L, algebraMap L (FractionRing (MvPolynomial (Fin (d.N + 1)) L)) l =
      algebraMap (MvPolynomial (Fin (d.N + 1)) L) (FractionRing (MvPolynomial (Fin (d.N + 1)) L))
        (MvPolynomial.C l) := by
    intro l
    rw [IsScalarTower.algebraMap_apply L (MvPolynomial (Fin (d.N + 1)) L)
      (FractionRing (MvPolynomial (Fin (d.N + 1)) L)), MvPolynomial.algebraMap_eq]
  refine ⟨Module.finrank L E, B, ∏ s, Q (mm s),
    fun j => Matrix.of fun a a' => P (mm (j, a, a')) * ∏ s ∈ Finset.univ.erase (j, a, a'), Q (mm s),
    ?_, ?_, ?_, ?_⟩
  · exact Finset.prod_ne_zero_iff.mpr fun s _ => hQ _
  · intro x
    rw [map_prod]
    exact Finset.prod_congr rfl fun s _ => hQinv _ x
  · intro j a a' x
    simp only [Matrix.of_apply]
    rw [map_mul, map_prod, hPinv]
    congr 1
    exact Finset.prod_congr rfl fun s _ => hQinv _ x
  · intro j
    ext a a'
    simp only [Matrix.map_apply, Matrix.of_apply]
    rw [htr, he, hb'2, Matrix.map_apply, hLtoC, hPQ]
    exact hfrac (j, a, a')

end Data

end ReciprocityTheory.ChartRestriction.G.T0
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.HDiscAG
section
namespace ReciprocityTheory.ChartRestriction.G.T0

open NumberField IsDedekindDomain

theorem prod_zpow_eq {ι G : Type*} [CommGroupWithZero G] {x : G} (hx : x ≠ 0) (s : Finset ι)
    (f : ι → ℤ) : ∏ i ∈ s, x ^ f i = x ^ ∑ i ∈ s, f i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert j s hj ih => rw [Finset.prod_insert hj, Finset.sum_insert hj, ih, zpow_add₀ hx]

variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι]
  {Ω : ι → Type} [∀ c, Field (Ω c)] [∀ c, Algebra K (Ω c)]
  {WT : Type} [AddCommGroup WT]
  {A : ι → Type} [∀ c, CommRing (A c)] [∀ c, Algebra (Ω c) (A c)] [∀ c, Algebra K (A c)]
  [∀ c, Algebra (𝓞 K) (A c)]
  {𝒜 : (c : ι) → WT → Submodule (Ω c) (A c)}

namespace Data

variable (d : Data K ι Ω WT A)

theorem disc_at (hd : d.AxH 𝒜) (h : d.S1) (la : HeightOneSpectrum (𝓞 K)) :
    ∃ n t : ℕ, ∃ N : ℤ, (d.htOf hd h).Ila la = n ∧ d.NlaG h d.wF hd.a4.choose la = N ∧
      ∃ u : Op d.D d.N la, IsUnit u ∧ d.De hd h =
        (algebraMap K (KTf K d.D d.N) ((unif la : 𝓞 K) : K)) ^ (((2 * n + t : ℕ) : ℤ) - 2 * N) *
          OpToKT d.D d.N la u := by
  classical
  letI : ∀ c, Algebra (KTf K d.D d.N) (OmS (Ω c) d.D d.N) := fun c => (d.KTtoS h c).toAlgebra
  letI : ∀ c, Algebra (Op d.D d.N la) (OmS (Ω c) d.D d.N) := fun c => d.algOp h la c
  letI := algOpKT (K := K) d.D d.N la
  haveI := Op_isDVR (K := K) d.D d.N la
  haveI := isFractionRing_Op (K := K) d.D d.N la
  have hF := fun c => d.comp_facts hd h la c
  haveI : ∀ c, IsScalarTower (Op d.D d.N la) (KTf K d.D d.N) (OmS (Ω c) d.D d.N) :=
    fun c => (hF c).2.1
  haveI : ∀ c, FiniteDimensional (KTf K d.D d.N) (OmS (Ω c) d.D d.N) := fun c => (hF c).2.2.1
  haveI : ∀ c, Algebra.IsSeparable (KTf K d.D d.N) (OmS (Ω c) d.D d.N) := fun c => (hF c).2.2.2.1
  let n : ∀ c, AddValuation (OmS (Ω c) d.D d.N) (WithTop ℤ) → ℤ := fun c w =>
    d.ord c (d.Wres c w) d.wF (hd.a4.choose c)
  choose g hg0 hgw hgiff using fun c => d.comp_g hd h la c (n c)
  have hset : d.AdmissibleOmegaFamiliesAtPrimeOfSection hd.a4.choose la =
      {y | ∀ c, g c * y c ∈ integralClosure (Op d.D d.N la) (OmS (Ω c) d.D d.N)} := by
    ext y
    simp only [AdmissibleOmegaFamiliesAtPrimeOfSection, Set.mem_setOf_eq]
    exact forall_congr' fun c => hgiff c (y c)
  have hb : ∀ k c, g c * d.bvecG hd.sel hd.a4.choose k c ∈
      integralClosure (Op d.D d.N la) (OmS (Ω c) d.D d.N) := fun k c =>
    (hgiff c _).mp (fun w hw => d.b_mem hd h la k c w hw)
  obtain ⟨nn, t, u, hlen, hdisc⟩ := HDiscLat.lattice_main (R := Op d.D d.N la)
    (F := KTf K d.D d.N) (unifOp_irreducible d.D d.N la) g hg0 (d.del_eq hd h)
    (d.bvecG hd.sel hd.a4.choose) hb (d.b_linIndep hd h)
  choose uN huN hN using fun c => d.comp_norm hd h la c (hg0 c) (n c) (hgw c)
  let Nc : ι → ℤ := fun c => ∑ᶠ (w : AddValuation (OmS (Ω c) d.D d.N) (WithTop ℤ))
    (_ : w ∈ d.PlOver la c), (d.fze h c w : ℤ) * n c w
  have hfin : ∀ c, (d.PlOver la c).Finite := fun c => by
    obtain ⟨i1, i2, i3, i4, i5, i6⟩ := hF c
    rw [d.plOver_eq h la c]
    exact ValPl.placesOver_finite (F := KTf K d.D d.N) (Op d.D d.N la) (OmS (Ω c) d.D d.N)
  refine ⟨nn, t, ∑ c, Nc c, ?_, ?_, ?_⟩
  · change Module.length (Op d.D d.N la)
      (↥(Submodule.span (Op d.D d.N la) (d.AdmissibleOmegaFamiliesAtPrimeOfSection hd.a4.choose la)) ⧸
        (Submodule.span (Op d.D d.N la) (Set.range (d.bvecG hd.sel hd.a4.choose))).comap
          (Submodule.span (Op d.D d.N la) (d.AdmissibleOmegaFamiliesAtPrimeOfSection hd.a4.choose la)).subtype) = nn
    rw [hset]
    exact hlen
  · simp only [NlaG, Nc]
    push_cast
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [finsum_mem_eq_finite_toFinset_sum _ (hfin c), finsum_mem_eq_finite_toFinset_sum _ (hfin c)]
    push_cast
    rfl
  · set X := OpToKT d.D d.N la (unifOp d.D d.N la) with hX
    have hX0 : X ≠ 0 := (map_ne_zero_iff _ (OpToKT_injective d.D d.N la)).mpr
      (unifOp_irreducible d.D d.N la).ne_zero
    let U : (Op d.D d.N la)ˣ := ∏ c, (huN c).unit
    have hprod : ∏ c, Algebra.norm (KTf K d.D d.N) (g c) =
        X ^ (∑ c, Nc c) * OpToKT d.D d.N la (U : Op d.D d.N la) := by
      rw [Finset.prod_congr rfl fun c _ => hN c, Finset.prod_mul_distrib, prod_zpow_eq hX0,
        ← map_prod]
      congr 2
      simp only [U, Units.coe_prod, IsUnit.unit_spec]
    rw [hprod] at hdisc
    refine ⟨↑(u * U⁻¹ * U⁻¹), Units.isUnit _, ?_⟩
    rw [algK_unif, ← hX]
    set V := OpToKT d.D d.N la (U : Op d.D d.N la)
    set V' := OpToKT d.D d.N la ((U⁻¹ : (Op d.D d.N la)ˣ) : Op d.D d.N la)
    have hU : V * V' = 1 := by
      simp only [V, V']
      rw [← map_mul, Units.mul_inv, map_one]
    set Y := X ^ (∑ c, Nc c)
    have hY : Y ≠ 0 := zpow_ne_zero _ hX0
    have h2 : X ^ (2 * ∑ c, Nc c) = Y ^ 2 := by
      rw [mul_comm, zpow_mul]
      norm_cast
    have hone : (Y * V) ^ 2 * ((Y ^ 2)⁻¹ * V' * V') = 1 := by
      calc (Y * V) ^ 2 * ((Y ^ 2)⁻¹ * V' * V') = (Y ^ 2 * (Y ^ 2)⁻¹) * ((V * V') * (V * V')) := by
            ring
        _ = 1 := by rw [mul_inv_cancel₀ (pow_ne_zero 2 hY), hU]; ring
    have hdisc' : d.De hd h * (Y * V) ^ 2 =
        OpToKT d.D d.N la ↑u * X ^ (2 * nn + t) := by
      rw [← map_pow, ← map_mul]
      exact hdisc
    rw [zpow_sub₀ hX0, zpow_natCast, h2, Units.val_mul, Units.val_mul, map_mul, map_mul]
    calc d.De hd h = d.De hd h * ((Y * V) ^ 2 * ((Y ^ 2)⁻¹ * V' * V')) := by rw [hone, mul_one]
      _ = (d.De hd h * (Y * V) ^ 2) * ((Y ^ 2)⁻¹ * V' * V') := by ring
      _ = _ := by rw [hdisc', div_eq_mul_inv]; ring

end Data

end ReciprocityTheory.ChartRestriction.G.T0
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.HNormPts
section
namespace ReciprocityTheory.ChartRestriction.G.T0

open NumberField

variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι]
  {Ω : ι → Type} [∀ c, Field (Ω c)] [∀ c, Algebra K (Ω c)]
  {WT : Type} [AddCommGroup WT]
  {A : ι → Type} [∀ c, CommRing (A c)] [∀ c, Algebra (Ω c) (A c)] [∀ c, Algebra K (A c)]
  [∀ c, Algebra (𝓞 K) (A c)]
  {𝒜 : (c : ι) → WT → Submodule (Ω c) (A c)}

namespace Data

variable (d : Data K ι Ω WT A)

theorem norm_at_la (hd : d.AxH 𝒜) (h : d.S1) (c : ι) (la : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    (ϖ : 𝓞 K) (hϖ : ϖ ∈ la.asIdeal) (hϖ2 : ϖ ∉ la.asIdeal ^ 2)
    (y : OmS (Ω c) d.D d.N) (hy : y ≠ 0) :
    ∃ u : Op d.D d.N la, IsUnit u ∧
      letI : Algebra (KTf K d.D d.N) (OmS (Ω c) d.D d.N) := (d.KTtoS h c).toAlgebra
      Algebra.norm (KTf K d.D d.N) y =
        (algebraMap K (KTf K d.D d.N) (ϖ : K)) ^
          (∑ᶠ (w : AddValuation (OmS (Ω c) d.D d.N) (WithTop ℤ)) (_ : w ∈ d.PlOver la c),
            (d.fze h c w : ℤ) * WithTop.untopD 0 (w y)) * OpToKT d.D d.N la u :=
  d.norm_at_la_A hd h c la ϖ hϖ hϖ2 y hy

open MeasureTheory in

theorem norm_at_sg (hd : d.AxH 𝒜) (h : d.S1) (c : ι) (sg : K →+* ℂ) :
    letI : Algebra (KTf K d.D d.N) (OmS (Ω c) d.D d.N) := (d.KTtoS h c).toAlgebra
    ∀ᵐ z ∂(ReciprocityTheory.MultiplicativeHeights.blockSphereProb d.D (d.N + 1)),
      (d.ST c sg (d.tOf z)).Finite ∧ (d.ST c sg (d.tOf z)).ncard = d.delc c ∧
      (∀ (g : Ω c) (a b : KTp K d.D d.N) (t0 : Fin (d.N + 1) → ℂ), g ≠ 0 → b ≠ 0 →
        (Algebra.norm (KTf K d.D d.N) (algebraMap (Ω c) (OmS (Ω c) d.D d.N) g) *
            algebraMap (KTp K d.D d.N) (KTf K d.D d.N) b =
          algebraMap (KTp K d.D d.N) (KTf K d.D d.N) a) →
        d.evT sg t0 (d.tOf z) b ≠ 0 → d.evT sg t0 (d.tOf z) a / d.evT sg t0 (d.tOf z) b = ∏ᶠ (P : Ω c →+* ℂ) (_ : P ∈ d.ST c sg (d.tOf z)), P g) ∧
      (∀ (a b : KTp K d.D d.N) (t0 : Fin (d.N + 1) → ℂ), b ≠ 0 →
        (Algebra.norm (KTf K d.D d.N) (d.rationalBaseRow c) * algebraMap (KTp K d.D d.N) (KTf K d.D d.N) b =
          algebraMap (KTp K d.D d.N) (KTf K d.D d.N) a) →
        d.evT sg t0 (d.tOf z) b ≠ 0 → d.evT sg t0 (d.tOf z) a / d.evT sg t0 (d.tOf z) b = ∏ᶠ (P : Ω c →+* ℂ) (_ : P ∈ d.ST c sg (d.tOf z)),
          ∑ j, t0 j * P (ratio (Ω := Ω c) (d.w j c) (d.w (d.jc c) c))) :=
  d.norm_at_sg_B hd h c sg

end Data

end ReciprocityTheory.ChartRestriction.G.T0
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.TraceFib
section
namespace ReciprocityTheory.ChartRestriction.G.T0

open NumberField MvPolynomial

variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι]
  {Ω : ι → Type} [∀ c, Field (Ω c)] [∀ c, Algebra K (Ω c)]
  {WT : Type} [AddCommGroup WT]
  {A : ι → Type} [∀ c, CommRing (A c)] [∀ c, Algebra (Ω c) (A c)] [∀ c, Algebra K (A c)]
  [∀ c, Algebra (𝓞 K) (A c)]
  {𝒜 : (c : ι) → WT → Submodule (Ω c) (A c)}

namespace Data

variable (d : Data K ι Ω WT A)

theorem trace_fib (hd : d.AxH 𝒜) (h : d.S1) (c : ι) (sg : K →+* ℂ) (t : Fin d.D → Fin (d.N + 1) → ℂ)
    (y : Fin (d.N + 1 + d.D) → ℂ)
    (hpt : ∀ q : MvPolynomial (TVar d.D d.N) K, q ≠ 0 →
      eval₂ sg (NPB.gpt (fun q => t q.1 q.2) y) q ≠ 0) (g : Ω c) :
    letI : Algebra (KTf K d.D d.N) (OmS (Ω c) d.D d.N) := (d.KTtoS h c).toAlgebra
    tauPev sg _ hpt (Algebra.trace (KTf K d.D d.N) (OmS (Ω c) d.D d.N)
        (algebraMap (Ω c) (OmS (Ω c) d.D d.N) g)) =
      ∑ᶠ (P : Ω c →+* ℂ) (_ : P ∈ d.ST c sg t), P g := by
  letI : Algebra (KTf K d.D d.N) (OmS (Ω c) d.D d.N) := (d.KTtoS h c).toAlgebra
  letI : Algebra (KTf K d.D d.N) ℂ := (tauPev sg _ hpt).toAlgebra
  obtain ⟨hfd, hrk⟩ := d.omS_finite hd h c
  have : CharZero (KTf K d.D d.N) :=
    charZero_of_injective_algebraMap (R := K) (algebraMap K (KTf K d.D d.N)).injective
  have hy : ∀ i, y (Fin.natAdd (d.N + 1) i) ≠ 0 := fun i h0 => by
    have := hpt (X (i.succ, 0)) (X_ne_zero _)
    rw [eval₂_X, NPB.gpt_succ, h0, zero_mul] at this
    exact this rfl
  obtain ⟨hinj, hrange⟩ := d.fibre_core hd h c sg _ hpt
  rw [d.ST_scale c sg t y hy] at hrange
  rw [← hrange, finsum_mem_range hinj, finsum_eq_sum_of_fintype]
  exact trace_eq_sum_embeddings ℂ

theorem de_fibre (hd : d.AxH 𝒜) (h : d.S1) (a b : KTp K d.D d.N) (hab : d.IsPres hd h a b)
    (sg : K →+* ℂ) :
    ∀ᵐ z ∂(ReciprocityTheory.MultiplicativeHeights.blockSphereProb d.D (d.N + 1)),
      d.evT sg 0 (d.tOf z) b ≠ 0 →
      d.evT sg 0 (d.tOf z) a / d.evT sg 0 (d.tOf z) b =
        (Matrix.of fun k l : Fin d.del => ∑ c, ∑ᶠ (P : Ω c →+* ℂ) (_ : P ∈ d.ST c sg (d.tOf z)),
          P (ratio (Ω := Ω c) (d.thp (hd.sel k) c) (hd.a4.choose c)) *
          P (ratio (Ω := Ω c) (d.thp (hd.sel l) c) (hd.a4.choose c))).det := by
  haveI : Countable K := countable_numberField K
  filter_upwards [NPB.ae_gen (D := d.D) (N := d.N) sg] with z hz hb
  refine (div_eq_iff hb).2 ?_
  have hG : ∀ (m : Fin d.D → ℕ) (p : MvPolynomial (Fin d.D × Fin (d.N + 1)) K),
      ReciprocityTheory.MultiplicativeHeights.IsMultiHomogeneous m p → p ≠ 0 →
      eval₂ sg (fun q : Fin d.D × Fin (d.N + 1) => d.tOf z q.1 q.2) p ≠ 0 :=
    fun m p h1 h2 => hz m p h1 h2
  have h0 : ∀ q : MvPolynomial (TVar d.D d.N) K,
      eval₂ sg (NPB.gpt (fun q : Fin d.D × Fin (d.N + 1) => d.tOf z q.1 q.2)
        (Fin.append (fun _ : Fin (d.N + 1) => (0 : ℂ)) (fun _ : Fin d.D => (1 : ℂ)))) q =
        d.evT sg 0 (d.tOf z) q := by
    intro q
    unfold Data.evT
    congr 1
    funext v
    obtain ⟨i, j⟩ := v
    induction i using Fin.cases with
    | zero => simp [NPB.gpt]
    | succ i => simp [NPB.gpt]
  suffices H : ∀ Dv : ℂ, (∀ y : Fin (d.N + 1 + d.D) → ℂ,
      (∀ q : MvPolynomial (TVar d.D d.N) K, q ≠ 0 →
        eval₂ sg (NPB.gpt (fun q : Fin d.D × Fin (d.N + 1) => d.tOf z q.1 q.2) y) q ≠ 0) →
      eval₂ sg (NPB.gpt (fun q : Fin d.D × Fin (d.N + 1) => d.tOf z q.1 q.2) y) a =
        Dv * eval₂ sg (NPB.gpt (fun q : Fin d.D × Fin (d.N + 1) => d.tOf z q.1 q.2) y) b) →
      d.evT sg 0 (d.tOf z) a = Dv * d.evT sg 0 (d.tOf z) b by
    refine H _ fun y hpt => ?_
    have h1 := congrArg (tauPev sg _ hpt) hab.2.1
    rw [map_mul, tauPev_apply, tauPev_apply] at h1
    rw [h1]
    congr 1
    rw [Data.De, RingHom.map_det]
    congr 1
    ext k l
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, map_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    have ht := d.trace_fib hd h c sg (d.tOf z) y hpt
      (ratio (Ω := Ω c) (d.thp (hd.sel k) c) (hd.a4.choose c) *
        ratio (Ω := Ω c) (d.thp (hd.sel l) c) (hd.a4.choose c))
    simp only [map_mul] at ht
    simpa only [Data.bvecG] using ht
  intro Dv hDv
  have hR : NPB.psi sg (fun q : Fin d.D × Fin (d.N + 1) => d.tOf z q.1 q.2) a -
      MvPolynomial.C Dv * NPB.psi sg (fun q : Fin d.D × Fin (d.N + 1) => d.tOf z q.1 q.2) b = 0 := by
    by_contra hR
    obtain ⟨y, hy, hgen⟩ := NPB.exists_gen sg _ hG _ hR
    apply hy
    rw [map_sub, map_mul, MvPolynomial.eval_C, NPB.eval_psi, NPB.eval_psi, hDv y hgen, sub_self]
  have e0 := congrArg
    (MvPolynomial.eval (Fin.append (fun _ : Fin (d.N + 1) => (0 : ℂ)) (fun _ : Fin d.D => (1 : ℂ)))) hR
  rw [map_sub, map_mul, MvPolynomial.eval_C, NPB.eval_psi, NPB.eval_psi, h0, h0, map_zero] at e0
  exact sub_eq_zero.mp e0

end Data

end ReciprocityTheory.ChartRestriction.G.T0
end

