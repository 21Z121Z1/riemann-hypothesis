import Mathlib
import Formalism.CharacterColumnKernels.StatementRho
import Formalism.GaloisCohomology.LocalTateDualityK
import ReciprocityTheory.Hypotheses.GalCohDefs
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LevRepZApply
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnitLemmaGroup
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0002
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0143
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0081
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0065
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsLocalRingOfIdem
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0005
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0125
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0130
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0148
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0147

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TransferCardH0H1Eq
section
open ReciprocityTheory.Gal

noncomputable section

namespace GlobalTheory.ShapeNeg

theorem transfer_card_H0_H1 : ∀ {O : Type} [CommRing O] {G G' : Type} [Group G] [TopologicalSpace G] [Group G'] [TopologicalSpace G']
    (i : G ≃ₜ* G') {M : Type} [AddCommGroup M] [Module O M] (ρ : Representation O G M)
    (p r : ℕ) [NeZero (p ^ r)] (c : O) (h : ((p : O) ^ r) ∈ Ideal.span {c}),
    letI := GlobalTheory.ShapeNeg.levZ (M := M) p r h
    Nat.card (ReciprocityTheory.Gal.H0 (GlobalTheory.ShapeNeg.levRep ρ c)) =
        Nat.card (ReciprocityTheory.Gal.H0 (GlobalTheory.ShapeNeg.levRepZ p r h (ρ.comp i.symm.toMulEquiv.toMonoidHom))) ∧
      Nat.card (ReciprocityTheory.Gal.H1 (GlobalTheory.ShapeNeg.levRep ρ c)) =
        Nat.card (ReciprocityTheory.Gal.H1 (GlobalTheory.ShapeNeg.levRepZ p r h (ρ.comp i.symm.toMulEquiv.toMonoidHom))) := by
  intro O _ G G' _ _ _ _ i M _ _ ρ p r _ c h
  letI := levZ (M := M) p r h

  have hact : ∀ (g' : G') (x : Lev M c),
      levRepZ p r h (ρ.comp i.symm.toMulEquiv.toMonoidHom) g' x = levRep ρ c (i.symm g') x :=
    fun g' x => rfl
  constructor
  · apply Nat.card_congr
    refine Equiv.subtypeEquivRight ?_
    intro x
    show (∀ g, levRep ρ c g x = x) ↔ ∀ g', levRepZ p r h (ρ.comp i.symm.toMulEquiv.toMonoidHom) g' x = x
    constructor
    · intro hx g'; rw [hact]; exact hx _
    · intro hx g
      have := hx (i g)
      rw [hact, ContinuousMulEquiv.symm_apply_apply] at this
      exact this
  · apply Nat.card_congr
    let ρ' := levRepZ p r h (ρ.comp i.symm.toMulEquiv.toMonoidHom)
    have hs : Continuous (i.symm : G' → G) := i.symm.continuous
    have hi : Continuous (i : G → G') := i.continuous
    let e : Z1 (levRep ρ c) ≃ Z1 ρ' :=
      { toFun := fun f => ⟨(f : G → Lev M c) ∘ i.symm, f.2.1.comp hs, fun a b => by
          show (f : G → Lev M c) (i.symm (a * b)) = (f : G → Lev M c) (i.symm a) + ρ' a ((f : G → Lev M c) (i.symm b))
          rw [map_mul, f.2.2]; rfl⟩
        invFun := fun f => ⟨(f : G' → Lev M c) ∘ i, f.2.1.comp hi, fun a b => by
          show (f : G' → Lev M c) (i (a * b)) = (f : G' → Lev M c) (i a) + levRep ρ c a ((f : G' → Lev M c) (i b))
          rw [map_mul, f.2.2, hact, ContinuousMulEquiv.symm_apply_apply]⟩
        left_inv := fun f => by
          apply Subtype.ext; funext g; show (f : G → Lev M c) (i.symm (i g)) = _
          rw [ContinuousMulEquiv.symm_apply_apply]
        right_inv := fun f => by
          apply Subtype.ext; funext g; show (f : G' → Lev M c) (i (i.symm g)) = _
          rw [ContinuousMulEquiv.apply_symm_apply] }
    refine Quotient.congr e ?_
    intro a b
    rw [Submodule.quotientRel_def, Submodule.quotientRel_def, Submodule.mem_comap, Submodule.mem_comap,
      Submodule.coe_subtype, Submodule.coe_subtype, mem_coboundaries1, mem_coboundaries1]
    constructor
    · rintro ⟨m, hm⟩
      refine ⟨m, fun g' => ?_⟩
      have := hm (i.symm g')
      rw [hact]
      exact this
    · rintro ⟨m, hm⟩
      refine ⟨m, fun g => ?_⟩
      have := hm (i g)
      rw [hact] at this
      change (a : G → Lev M c) (i.symm (i g)) - (b : G → Lev M c) (i.symm (i g)) = _ at this
      rw [ContinuousMulEquiv.symm_apply_apply] at this
      exact this

end GlobalTheory.ShapeNeg
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnitLemmaSelfAdjointLieOfCountLimitDescent
section
noncomputable section

namespace GlobalTheory.UnitLemma.LieEnd

open GlobalTheory.UnitLemma Polynomial Filter Topology

theorem eta_mul (K : UQ) {x y : K.E} (hx : x ≠ 0) (hy : y ≠ 0) : K.eta (x * y) = K.eta x * K.eta y := by
  unfold UQ.eta val
  rw [map_mul, WithZero.log_mul ((Valuation.ne_zero_iff _).2 hx) ((Valuation.ne_zero_iff _).2 hy), neg_add,
    zpow_add₀ (by norm_num)]

theorem eta_sq (K : UQ) (x : K.E) : K.eta x * K.eta x = 1 := by
  unfold UQ.eta
  rw [← mul_zpow]
  norm_num

theorem q_ne_zero (K : UQ) : K.q ≠ 0 := by
  intro hq
  have hc := K.card_res
  have hpos : 0 < Nat.card (IsLocalRing.ResidueField K.O) := Nat.card_pos
  rw [hq] at hc
  simp at hc
  omega

theorem exists_small (K : UQ) : ∃ a : K.O, K.Small a := by
  obtain ⟨p, hp⟩ := IsDiscreteValuationRing.exists_irreducible K.O
  obtain ⟨y, hy⟩ := K.c_int p
  have hinj := IsFractionRing.injective K.O K.E
  have hy' : K.c (algebraMap K.O K.E y) = algebraMap K.O K.E p := by rw [← hy, K.c_c]
  have hy0 : y ≠ 0 := by
    rintro rfl
    have h0 : algebraMap K.O K.E p = 0 := by simpa using hy
    exact hp.ne_zero ((map_eq_zero_iff _ hinj).1 h0)
  refine ⟨p * y, mul_ne_zero hp.ne_zero hy0, Ideal.mul_mem_right _ _ ((IsLocalRing.mem_maximalIdeal _).2 hp.not_isUnit), ?_⟩
  rw [map_mul, map_mul, hy, hy', mul_comm]

variable {K : UQ}

theorem mulLeft_prod (B₁ B₂ : InvAlg K) (x : B₁.A × B₂.A) :
    LinearMap.mulLeft K.E x = (LinearMap.mulLeft K.E x.1).prodMap (LinearMap.mulLeft K.E x.2) := LinearMap.ext fun y => Prod.ext (by simp) (by simp)

theorem prod_P (B₁ B₂ : InvAlg K) : (B₁.prod B₂).P = B₁.P * B₂.P := by
  show (LinearMap.mulLeft K.E ((B₁.g, B₂.g) : B₁.A × B₂.A)).charpoly = _
  rw [mulLeft_prod]
  exact LinearMap.charpoly_prodMap _ _

theorem trace_prod (B₁ B₂ : InvAlg K) (x : B₁.A × B₂.A) :
    Algebra.trace K.E (B₁.A × B₂.A) x = Algebra.trace K.E B₁.A x.1 + Algebra.trace K.E B₂.A x.2 := Algebra.trace_prod_apply x

theorem linLim (h1 : CountIdentity) (h2 : UnitaryLimit) (B : InvAlg K) (hB : B.LieReg) (a : K.O)
    (ha : K.Small a) (x : B.A) (hx : B.Plus x) : B.LinLim a x (B.N x : ℝ) := by
  have hw : ∀ k : ℕ, IsUnit (algebraMap K.O B.A a ^ k) := by
    intro k
    apply IsUnit.pow
    rw [IsScalarTower.algebraMap_apply K.O K.E B.A]
    exact (IsUnit.mk0 _ ((map_ne_zero_iff _ (IsFractionRing.injective K.O K.E)).2 ha.1)).map _
  have hσ : B.σ (algebraMap K.O B.A a) = algebraMap K.O B.A a := by
    rw [IsScalarTower.algebraMap_apply K.O K.E B.A, B.σ_alg, ha.2.2]
  refine (h2 K B hB a ha x hx).congr fun k => ?_
  have e : x * algebraMap K.O B.A a ^ (2 * k) =
      x * (algebraMap K.O B.A a ^ k * B.σ (algebraMap K.O B.A a ^ k)) := by
    rw [map_pow, hσ, ← pow_add, two_mul]
  rw [e, h1 K B hB x _ hx (hw k), Rat.cast_natCast]

theorem nonempty_of_N_ne_zero (B : InvAlg K) (x : B.A) (h : B.N x ≠ 0) : (B.X x).Nonempty := by
  by_contra he
  apply h
  have : IsEmpty (B.X x) := Set.isEmpty_coe_sort.2 (Set.not_nonempty_iff_eq_empty.1 he)
  have : IsEmpty (Orb K.O B.T (B.X x)) := ⟨fun o => isEmptyElim (Quot.out o)⟩
  exact finsum_of_isEmpty _

theorem X_empty (B : InvAlg K) (y : B.A) (hy : y ≠ 0) (h : ∀ z, Algebra.trace K.E B.A (y * z) = 0) (x : B.A) :
    ¬ (B.X x).Nonempty := by
  rintro ⟨L, hL⟩
  obtain ⟨⟨hfg, -⟩, -, hdual⟩ := hL
  have hmem : ∀ s : B.A, y * s ∈ L := fun s => (hdual _).2 fun z _ => by
    have h0 : B.herm x (y * s) z = 0 := by
      unfold InvAlg.herm
      rw [show x * (y * s) * B.σ z = y * (x * s * B.σ z) by ring]
      exact h _
    rw [h0]
    exact zero_mem _
  obtain ⟨φ, hφ⟩ := Module.Projective.exists_dual_eq_one K.E hy
  have htop : (⊤ : Submodule K.O K.E) ≤ L.map ((φ : B.A →ₗ[K.E] K.E).restrictScalars K.O) := by
    intro e _
    refine Submodule.mem_map.2 ⟨y * algebraMap K.E B.A e, hmem _, ?_⟩
    rw [LinearMap.restrictScalars_apply, mul_comm, ← Algebra.smul_def, map_smul, hφ, smul_eq_mul, mul_one]
  have : Module.Finite K.O K.E := ⟨by rw [← top_le_iff.1 htop]; exact hfg.map _⟩
  obtain ⟨p, hp⟩ := IsDiscreteValuationRing.exists_irreducible K.O
  have hp0 : algebraMap K.O K.E p ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective K.O K.E)).2 hp.ne_zero
  obtain ⟨r, hr⟩ := IsIntegrallyClosed.isIntegral_iff.1
    (Algebra.IsIntegral.isIntegral (R := K.O) (algebraMap K.O K.E p)⁻¹)
  apply hp.not_isUnit
  have hpr : p * r = 1 :=
    IsFractionRing.injective K.O K.E (by rw [map_mul, hr, map_one, mul_inv_cancel₀ hp0])
  exact ⟨⟨p, r, hpr, by rw [mul_comm, hpr]⟩, rfl⟩

theorem exists_rad (B : InvAlg K) (h : B.gramDet 1 = 0) :
    ∃ y : B.A, y ≠ 0 ∧ ∀ z, Algebra.trace K.E B.A (y * z) = 0 := by
  classical
  set b := Module.finBasis K.E B.A
  have h' : (Matrix.of fun i j => B.herm 1 (b i) (b j)).det = 0 := h
  obtain ⟨v, hv0, hv⟩ := Matrix.exists_vecMul_eq_zero_iff.2 h'
  have hj : ∀ j, Algebra.trace K.E B.A ((∑ i, v i • b i) * B.σ (b j)) = 0 := by
    intro j
    have hvj := congrFun hv j
    simp only [Matrix.vecMul, dotProduct, Matrix.of_apply, InvAlg.herm, one_mul, Pi.zero_apply] at hvj
    rw [Finset.sum_mul, map_sum]
    simpa [smul_mul_assoc] using hvj
  refine ⟨∑ i, v i • b i, fun h0 => hv0 (funext fun i => Fintype.linearIndependent_iff.1 b.linearIndependent v h0 i), ?_⟩
  intro z
  have hz : z = ∑ j, K.c (b.repr (B.σ z) j) • B.σ (b j) := by
    conv_lhs => rw [← B.σ_σ z, ← b.sum_repr (B.σ z)]
    rw [map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Algebra.smul_def, Algebra.smul_def, map_mul, B.σ_alg]
  rw [hz, Finset.mul_sum, map_sum]
  refine Finset.sum_eq_zero fun j _ => ?_
  rw [mul_smul_comm, map_smul, hj, smul_zero]

theorem rep_plus (B : InvAlg K) (k : B.Cl) : B.Plus k.rep := ⟨Units.isUnit _, (Quot.out k).2⟩

theorem eta_norm (B : InvAlg K) (h : B.gramDet 1 ≠ 0) (x : B.A) (hx : IsUnit x) :
    K.eta (Algebra.norm K.E x) = K.eta (B.gramDet 1) * K.eta (B.gramDet x) := by
  have hn : Algebra.norm K.E x ≠ 0 := (hx.map (Algebra.norm K.E)).ne_zero
  rw [GlobalTheory.T.gramDet_eq_norm_mul_gramDet_one K B x, eta_mul K hn h, mul_left_comm, eta_sq, mul_one]

theorem cast_finsum {ι : Type} (f : ι → ℚ) : ((∑ᶠ i, f i : ℚ) : ℝ) = ∑ᶠ i, (f i : ℝ) := (Rat.castHom ℝ).toAddMonoidHom.map_finsum_of_injective Rat.cast_injective f

theorem unitLemmaLie_of (h1 : CountIdentity) (h2 : UnitaryLimit) (h3 : LinearDescent) : UnitLemmaLie := by
  intro K B₁ B₂ hg₁ hg₂ hsep
  show (-(K.q : ℚ)) ^ (-val K.O (resultant B₁.P B₂.P)) * InvAlg.kapSum B₁ B₂ = B₁.stSum * B₂.stSum
  obtain ⟨a, ha⟩ := exists_small K
  have hB : (B₁.prod B₂).LieReg := ⟨Prod.ext hg₁ hg₂, by rw [prod_P]; exact hsep⟩
  have hB₁ : B₁.LieReg := ⟨hg₁, hsep.of_mul_left⟩
  have hB₂ : B₂.LieReg := ⟨hg₂, hsep.of_mul_right⟩
  have hLD := h3 K B₁ B₂ hg₁ hg₂ hsep a ha (fun x => ((B₁.prod B₂).N x : ℝ)) (fun x => (B₁.N x : ℝ))
    (fun x => (B₂.N x : ℝ)) (fun x hx => linLim h1 h2 _ hB a ha x hx)
    (fun x hx => linLim h1 h2 _ hB₁ a ha x hx) (fun x hx => linLim h1 h2 _ hB₂ a ha x hx)
  simp only [← Rat.cast_mul] at hLD
  rw [← cast_finsum, ← cast_finsum, ← cast_finsum] at hLD
  have hq : (-(K.q : ℝ)) ^ val K.O (resultant B₁.P B₂.P) =
      (((-(K.q : ℚ)) ^ val K.O (resultant B₁.P B₂.P) : ℚ) : ℝ) := by
    rw [Rat.cast_zpow, Rat.cast_neg, Rat.cast_natCast]
  rw [hq, ← Rat.cast_mul, ← Rat.cast_mul] at hLD
  have hQ := Rat.cast_injective hLD
  have hq0 : (-(K.q : ℚ)) ≠ 0 := by simpa using q_ne_zero K
  by_cases hd : B₁.gramDet 1 = 0
  · obtain ⟨y, hy0, hy⟩ := exists_rad B₁ hd
    have hN₁ : ∀ x, B₁.N x = 0 := fun x =>
      by_contra fun hx => X_empty B₁ y hy0 hy x (nonempty_of_N_ne_zero B₁ x hx)
    have hN : ∀ x, (B₁.prod B₂).N x = 0 := by
      intro x
      by_contra hx
      refine X_empty (B₁.prod B₂) ((y, 0) : B₁.A × B₂.A) (fun h0 => hy0 (congrArg Prod.fst h0))
        (fun z => ?_) x (nonempty_of_N_ne_zero _ x hx)
      have key : ∀ w : B₁.A × B₂.A, Algebra.trace K.E (B₁.A × B₂.A) ((y, 0) * w) = 0 := fun w => by
        rw [trace_prod]
        simp [hy]
      exact key z
    simp [InvAlg.kapSum, InvAlg.stSum, hN, hN₁]
  · have he : K.eta (B₁.gramDet 1) * K.eta (B₁.gramDet 1) = 1 := eta_sq K _
    have hS : ∑ᶠ k : (B₁.prod B₂).Cl, K.eta (Algebra.norm K.E (InvAlg.Cl.rep k).1) * (B₁.prod B₂).N k.rep =
        K.eta (B₁.gramDet 1) * InvAlg.kapSum B₁ B₂ := by
      unfold InvAlg.kapSum
      rw [mul_finsum]
      refine finsum_congr fun k => ?_
      rw [eta_norm B₁ hd _ (Prod.isUnit_iff.1 (rep_plus _ k).1).1, mul_assoc]
    have hS₁ : ∑ᶠ k : B₁.Cl, K.eta (Algebra.norm K.E k.rep) * B₁.N k.rep =
        K.eta (B₁.gramDet 1) * B₁.stSum := by
      unfold InvAlg.stSum
      rw [mul_finsum]
      refine finsum_congr fun k => ?_
      rw [eta_norm B₁ hd _ (rep_plus _ k).1]
      by_cases hk : B₁.N k.rep = 0
      · rw [hk, mul_zero, mul_zero]
      · rw [GlobalTheory.T.eta_gramDet_eq_one_of_selfDual_lattice K B₁ k.rep (rep_plus _ k).2 (nonempty_of_N_ne_zero B₁ _ hk), mul_one]
    have hst : ∑ᶠ k : B₂.Cl, B₂.N k.rep = B₂.stSum := rfl
    rw [hS, hS₁, hst] at hQ
    have hk : InvAlg.kapSum B₁ B₂ =
        (-(K.q : ℚ)) ^ val K.O (resultant B₁.P B₂.P) * (B₁.stSum * B₂.stSum) := by
      calc InvAlg.kapSum B₁ B₂
          = K.eta (B₁.gramDet 1) * (K.eta (B₁.gramDet 1) * InvAlg.kapSum B₁ B₂) := by
            rw [← mul_assoc, he, one_mul]
        _ = K.eta (B₁.gramDet 1) * ((-(K.q : ℚ)) ^ val K.O (resultant B₁.P B₂.P) *
            (K.eta (B₁.gramDet 1) * B₁.stSum * B₂.stSum)) := by rw [hQ]
        _ = (-(K.q : ℚ)) ^ val K.O (resultant B₁.P B₂.P) * (B₁.stSum * B₂.stSum) *
            (K.eta (B₁.gramDet 1) * K.eta (B₁.gramDet 1)) := by ring
        _ = _ := by rw [he, mul_one]
    rw [hk, ← mul_assoc, ← zpow_add₀ hq0, neg_add_cancel, zpow_zero, one_mul]

end GlobalTheory.UnitLemma.LieEnd
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ValResultantEqDegreeMulUnramifiedExt
section
open GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Unr Polynomial

noncomputable section

namespace GlobalTheory.UnitLemma.Unr.ResVal

theorem int_lift : ∀ (K K' : UQ) (d : ℕ) (φ : K.E →+* K'.E), IsUnrExt K K' d φ →
    ∃ φO : K.O →+* K'.O, (∀ x, algebraMap K'.O K'.E (φO x) = φ (algebraMap K.O K.E x)) ∧
      @Algebra.IsIntegral K.O K'.O _ _ φO.toAlgebra := GlobalTheory.T.exists_integerMap_isIntegral_unramifiedInvolutionExt

theorem val_norm : ∀ (K K' : UQ) (d : ℕ) (φ : K.E →+* K'.E), IsUnrExt K K' d φ → ∀ y : K'.E,
    val K.O (@Algebra.norm K.E K'.E _ _ φ.toAlgebra y) = (d : ℤ) * val K'.O y := GlobalTheory.T.dvrFractionFieldAddVal_norm_unramifiedLocalExt

theorem res_gen : ∀ (K K' : UQ) (d : ℕ) (φ : K.E →+* K'.E), IsUnrExt K K' d φ →
    ∀ (B : InvAlg K) (ψ : K'.E →+* B.A), (∀ e, ψ (φ e) = algebraMap K.E B.A e) → Nontrivial B.A →
    (∀ y : K'.O, ψ (algebraMap K'.O K'.E y) ∈ Algebra.adjoin K.O ({B.g} : Set B.A)) →
    ∀ (s : K'.O) (Q : K'.O[X]), Q.Monic → Q.eval₂ (ψ.comp (algebraMap K'.O K'.E)) B.g = 0 →
    Q.map (IsLocalRing.residue K'.O) = (X - C (IsLocalRing.residue K'.O s)) ^ Q.natDegree →
    ∀ y : K'.O, ∃ f : K.O[X], ∃ z ∈ IsLocalRing.maximalIdeal K'.O,
      algebraMap K'.O K'.E y = f.eval₂ (φ.comp (algebraMap K.O K.E)) (algebraMap K'.O K'.E s) +
        algebraMap K'.O K'.E z := GlobalTheory.T.residue_generates_unramifiedExt_residueField

theorem res_mult : ∀ (K K' : UQ) (d : ℕ) (φ : K.E →+* K'.E), IsUnrExt K K' d φ → ∀ s : K'.O,
    (∀ y : K'.O, ∃ f : K.O[X], ∃ z ∈ IsLocalRing.maximalIdeal K'.O,
      algebraMap K'.O K'.E y = f.eval₂ (φ.comp (algebraMap K.O K.E)) (algebraMap K'.O K'.E s) +
        algebraMap K'.O K'.E z) →
    ∀ (p : K.O[X]) (r c : K'.O[X]), p.Monic → r.Monic →
    r.map (IsLocalRing.residue K'.O) = (X - C (IsLocalRing.residue K'.O s)) ^ r.natDegree →
    p.natDegree = d * r.natDegree →
    p.map (φ.comp (algebraMap K.O K.E)) = (r * c).map (algebraMap K'.O K'.E) →
    ¬ (c.map (IsLocalRing.residue K'.O)).IsRoot (IsLocalRing.residue K'.O s) := GlobalTheory.T.not_isRoot_residue_cofactor_unramifiedExt

theorem val_neg_one_pow {K : UQ} (k : ℕ) (x : K.E) : val K.O ((-1) ^ k * x) = val K.O x := by
  rcases neg_one_pow_eq_or K.E k with h | h <;> simp [h, val, Valuation.map_neg]

theorem val_mul' {K : UQ} {x y : K.E} (hx : x ≠ 0) (hy : y ≠ 0) : val K.O (x * y) = val K.O x + val K.O y := by
  unfold val
  rw [map_mul, WithZero.log_mul (by simpa using hx) (by simpa using hy), neg_add]

theorem val_mul_unit {K : UQ} (x : K.E) (u : K.O) (hu : IsUnit u) :
    val K.O (x * algebraMap K.O K.E u) = val K.O x := by
  by_cases hx : x = 0
  · simp [hx]
  have hu0 : algebraMap K.O K.E u ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective K.O K.E)).2 hu.ne_zero
  rw [val_mul' hx hu0, GlobalTheory.UnitLemma.Orbit.val_unit u hu, add_zero]

theorem norm_res {E A : Type} [Field E] [CommRing A] [Algebra E A] [Module.Finite E A] (g : A) (p : E[X])
    (hp : p.Monic) : ∃ k : ℕ, Algebra.norm E (aeval g p) = (-1) ^ k * resultant p (LinearMap.mulLeft E g).charpoly := by
  let u := Module.finBasis E A
  have h := GlobalTheory.TraceDetSplit.det_aeval (Algebra.leftMulMatrix u g) p hp
  rw [GlobalTheory.TraceDetSplit.charpoly_leftMul_basis, aeval_algHom_apply, ← Algebra.norm_eq_matrix_det] at h
  exact ⟨_, h⟩

theorem charpoly_subsingleton {E A : Type} [Field E] [CommRing A] [Algebra E A] [Module.Finite E A]
    [Subsingleton A] (g : A) : (LinearMap.mulLeft E g).charpoly = 1 := by
  apply eq_one_of_monic_natDegree_zero (LinearMap.charpoly_monic _)
  rw [LinearMap.charpoly_natDegree, Module.finrank_zero_of_subsingleton]

theorem aeval_P {K : UQ} (B : InvAlg K) : aeval B.g B.P = 0 := by
  have h := Polynomial.aeval_algHom_apply (Algebra.lmul K.E B.A) B.g B.P
  have h0 : aeval (Algebra.lmul K.E B.A B.g) B.P = 0 := LinearMap.aeval_self_charpoly _
  rw [h0] at h
  exact Algebra.lmul_injective (h.symm.trans (map_zero _).symm)

theorem norm_tower {K K' : UQ} (φ : K.E →+* K'.E) (B : InvAlg K) (ψ : K'.E →+* B.A)
    (hψ : ∀ e, ψ (φ e) = algebraMap K.E B.A e) (x : B.A) :
    Algebra.norm K.E x = @Algebra.norm K.E K'.E _ _ φ.toAlgebra (@Algebra.norm K'.E B.A _ _ ψ.toAlgebra x) := by
  letI : Algebra K.E K'.E := φ.toAlgebra
  letI : Algebra K'.E B.A := ψ.toAlgebra
  haveI : IsScalarTower K.E K'.E B.A := IsScalarTower.of_algebraMap_eq fun e => (hψ e).symm
  rw [Algebra.norm_apply K.E x, Algebra.norm_apply K'.E x, ← LinearMap.det_restrictScalars]
  rfl

theorem monic_dvd_pow {F : Type} [Field F] (a : F) (n : ℕ) (f : F[X]) (hf : f.Monic) (h : f ∣ (X - C a) ^ n) :
    f = (X - C a) ^ f.natDegree := by
  obtain ⟨i, -, hi⟩ := (dvd_prime_pow (prime_X_sub_C a) n).1 h
  have e := eq_of_monic_of_associated hf ((monic_X_sub_C a).pow i) hi
  rw [e, natDegree_pow, natDegree_X_sub_C, mul_one]

theorem val_resultant_unr : ∀ (K K' : UQ) (d : ℕ) (φ : K.E →+* K'.E), IsUnrExt K K' d φ → Odd d → ∀ (B₁ B₂ : InvAlg K) (ψ₁ : K'.E →+* B₁.A) (ψ₂ : K'.E →+* B₂.A) (h₁ : ∀ e, ψ₁ (φ e) = algebraMap K.E B₁.A e) (h₁' : ∀ e, B₁.σ (ψ₁ e) = ψ₁ (K'.c e)) (h₂ : ∀ e, ψ₂ (φ e) = algebraMap K.E B₂.A e) (h₂' : ∀ e, B₂.σ (ψ₂ e) = ψ₂ (K'.c e)), (∀ y : K'.O, (ψ₁.prod ψ₂) (algebraMap K'.O K'.E y) ∈ Algebra.adjoin K.O ({(B₁.prod B₂).g} : Set (B₁.prod B₂).A)) → (B₁.P * B₂.P).Separable → ∀ s : K'.O, (∃ Q : K'.O[X], Q.map (algebraMap K'.O K'.E) = (overExt φ B₁ ψ₁ h₁ h₁').P * (overExt φ B₂ ψ₂ h₂ h₂').P ∧ Q.map (IsLocalRing.residue K'.O) = (X - C (IsLocalRing.residue K'.O s)) ^ Q.natDegree) → val K.O (resultant B₁.P B₂.P) = d * val K'.O (resultant (overExt φ B₁ ψ₁ h₁ h₁').P (overExt φ B₂ ψ₂ h₂ h₂').P) := by
  intro K K' d φ hU _ B₁ B₂ ψ₁ ψ₂ h₁ h₁' h₂ h₂' hO hsep s ⟨Q, hQ, hQr⟩
  set B₁' := overExt φ B₁ ψ₁ h₁ h₁' with hB₁'
  set B₂' := overExt φ B₂ ψ₂ h₂ h₂' with hB₂'
  by_cases t₁ : Subsingleton B₁.A
  · have e1 : B₁.P = 1 := charpoly_subsingleton B₁.g
    haveI : Subsingleton B₁'.A := t₁
    have e1' : B₁'.P = 1 := charpoly_subsingleton (E := K'.E) (A := B₁'.A) B₁'.g
    simp [e1, e1', val]
  by_cases t₂ : Subsingleton B₂.A
  · have e2 : B₂.P = 1 := charpoly_subsingleton B₂.g
    haveI : Subsingleton B₂'.A := t₂
    have e2' : B₂'.P = 1 := charpoly_subsingleton (E := K'.E) (A := B₂'.A) B₂'.g
    simp [e2, e2', val]
  haveI : Nontrivial B₁.A := not_subsingleton_iff_nontrivial.1 t₁
  haveI : Nontrivial B₂.A := not_subsingleton_iff_nontrivial.1 t₂
  have hPm₁ : B₁'.P.Monic := LinearMap.charpoly_monic _
  have hPm₂ : B₂'.P.Monic := LinearMap.charpoly_monic _
  have hinj' := IsFractionRing.injective K'.O K'.E
  have hinj := IsFractionRing.injective K.O K.E
  have hQm : Q.Monic := monic_of_injective hinj' (by rw [hQ]; exact hPm₁.mul hPm₂)
  obtain ⟨r₁, hr₁⟩ := IsIntegrallyClosed.eq_map_mul_C_of_dvd K'.E hQm
    (show B₁'.P ∣ Q.map (algebraMap K'.O K'.E) by rw [hQ]; exact dvd_mul_right _ _)
  obtain ⟨r₂, hr₂⟩ := IsIntegrallyClosed.eq_map_mul_C_of_dvd K'.E hQm
    (show B₂'.P ∣ Q.map (algebraMap K'.O K'.E) by rw [hQ]; exact dvd_mul_left _ _)
  rw [hPm₁.leadingCoeff, C_1, mul_one] at hr₁
  rw [hPm₂.leadingCoeff, C_1, mul_one] at hr₂
  have hr₁m : r₁.Monic := monic_of_injective hinj' (by rw [hr₁]; exact hPm₁)
  have hr₂m : r₂.Monic := monic_of_injective hinj' (by rw [hr₂]; exact hPm₂)
  have hQr₁₂ : Q = r₁ * r₂ := Polynomial.map_injective _ hinj' (by rw [hQ, Polynomial.map_mul, hr₁, hr₂])
  have hres : ∀ r : K'.O[X], r.Monic → r ∣ Q →
      r.map (IsLocalRing.residue K'.O) = (X - C (IsLocalRing.residue K'.O s)) ^ r.natDegree := by
    intro r hr hrQ
    have := monic_dvd_pow _ _ _ (hr.map _) (hQr ▸ Polynomial.map_dvd _ hrQ)
    rwa [hr.natDegree_map] at this
  have hr₁r := hres r₁ hr₁m (by rw [hQr₁₂]; exact dvd_mul_right _ _)
  have hr₂r := hres r₂ hr₂m (by rw [hQr₁₂]; exact dvd_mul_left _ _)
  obtain ⟨φO, hφO, hint⟩ := int_lift K K' d φ hU
  have hφc : (algebraMap K'.O K'.E).comp φO = φ.comp (algebraMap K.O K.E) := RingHom.ext hφO
  have hg₂ : IsIntegral K.O B₂.g := by
    letI : Algebra K.O K'.O := φO.toAlgebra
    letI : Algebra K'.O B₂.A := (ψ₂.comp (algebraMap K'.O K'.E)).toAlgebra
    haveI : IsScalarTower K.O K'.O B₂.A := IsScalarTower.of_algebraMap_eq fun x => by
      change algebraMap K.O B₂.A x = ψ₂ (algebraMap K'.O K'.E (φO x))
      rw [hφO, h₂, ← IsScalarTower.algebraMap_apply]
    haveI : Algebra.IsIntegral K.O K'.O := hint
    have h2 : IsIntegral K'.O B₂.g := ⟨r₂, hr₂m, by
      change eval₂ (ψ₂.comp (algebraMap K'.O K'.E)) B₂.g r₂ = 0
      rw [← eval₂_map, hr₂]
      exact aeval_P B₂'⟩
    exact isIntegral_trans (R := K.O) _ h2
  have hs₂ : B₂.P.Separable := hsep.of_mul_right
  obtain ⟨p₂, hp₂m, hp₂⟩ := GlobalTheory.UnitLemma.Orbit.exists_monic_map_eq_charpoly₂ B₂ hs₂ hg₂
  have hs₂' : B₂'.P.Separable := GlobalTheory.T.separable_charpoly_invAlgBaseChangeUnramified K K' d φ hU B₂ ψ₂ h₂ h₂' hs₂
  have hcomp : ∀ (A : Type) [CommRing A] [Algebra K.E A] [Algebra K.O A] [IsScalarTower K.O K.E A] (ψ : K'.E →+* A),
      (∀ e, ψ (φ e) = algebraMap K.E A e) → (ψ.comp (algebraMap K'.O K'.E)).comp φO = algebraMap K.O A := by
    intro A _ _ _ _ ψ hψ
    ext x
    simp [hφO, hψ, ← IsScalarTower.algebraMap_apply]
  have hf0 : aeval B₂'.g (p₂.map φO) = 0 := by
    change eval₂ (ψ₂.comp (algebraMap K'.O K'.E)) B₂.g (p₂.map φO) = 0
    rw [eval₂_map, hcomp B₂.A ψ₂ h₂, ← aeval_def, ← aeval_map_algebraMap K.E, hp₂]
    exact aeval_P B₂
  obtain ⟨c', hc'⟩ := GlobalTheory.UnitLemma.Orbit.charpoly_dvd_map_of_aeval_eq_zero B₂' hs₂' _ hf0
  have hfm : (p₂.map φO).Monic := hp₂m.map _
  have hc'm : c'.Monic := hPm₂.of_mul_monic_left (by rw [← hc']; exact hfm.map _)
  obtain ⟨c₂, hc₂⟩ := IsIntegrallyClosed.eq_map_mul_C_of_dvd K'.E hfm
    (show c' ∣ (p₂.map φO).map (algebraMap K'.O K'.E) from ⟨B₂'.P, by rw [hc', mul_comm]⟩)
  rw [hc'm.leadingCoeff, C_1, mul_one] at hc₂
  have hfrc : p₂.map φO = r₂ * c₂ :=
    Polynomial.map_injective _ hinj' (by rw [hc', Polynomial.map_mul, hr₂, hc₂])
  have hgen := res_gen K K' d φ hU (B₁.prod B₂) (ψ₁.prod ψ₂) (fun e => Prod.ext (h₁ e) (h₂ e)) (show Nontrivial (B₁.A × B₂.A) from inferInstance)
    hO s Q hQm (by
      show (eval₂ ((ψ₁.prod ψ₂).comp (algebraMap K'.O K'.E)) ((B₁.g, B₂.g) : B₁.A × B₂.A) Q : B₁.A × B₂.A) = 0
      refine Prod.ext ?_ ?_
      · change (RingHom.fst B₁.A B₂.A) (eval₂ ((ψ₁.prod ψ₂).comp (algebraMap K'.O K'.E)) ((B₁.g, B₂.g) : B₁.A × B₂.A) Q) = 0
        rw [hom_eval₂]
        change eval₂ (ψ₁.comp (algebraMap K'.O K'.E)) B₁.g Q = 0
        rw [← eval₂_map, hQ, eval₂_mul]
        have h0 : eval₂ ψ₁ B₁.g B₁'.P = 0 := aeval_P B₁'
        rw [h0, zero_mul]
      · change (RingHom.snd B₁.A B₂.A) (eval₂ ((ψ₁.prod ψ₂).comp (algebraMap K'.O K'.E)) ((B₁.g, B₂.g) : B₁.A × B₂.A) Q) = 0
        rw [hom_eval₂]
        change eval₂ (ψ₂.comp (algebraMap K'.O K'.E)) B₂.g Q = 0
        rw [← eval₂_map, hQ, eval₂_mul]
        have h0 : eval₂ ψ₂ B₂.g B₂'.P = 0 := aeval_P B₂'
        rw [h0, mul_zero]) hQr
  have hdeg : p₂.natDegree = d * r₂.natDegree := by
    have a1 : p₂.natDegree = Module.finrank K.E B₂.A := by
      rw [← natDegree_map_eq_of_injective hinj p₂, hp₂]; exact LinearMap.charpoly_natDegree _
    have a2 : r₂.natDegree = @Module.finrank K'.E B₂.A _ _ ψ₂.toAlgebra.toModule := by
      rw [← natDegree_map_eq_of_injective hinj' r₂, hr₂]; exact LinearMap.charpoly_natDegree _
    rw [a1, a2, ← hU.2.2.2.2]
    letI : Algebra K.E K'.E := φ.toAlgebra
    letI : Algebra K'.E B₂.A := ψ₂.toAlgebra
    haveI : IsScalarTower K.E K'.E B₂.A := IsScalarTower.of_algebraMap_eq fun e => (h₂ e).symm
    exact (Module.finrank_mul_finrank K.E K'.E B₂.A).symm
  have hmap : p₂.map (φ.comp (algebraMap K.O K.E)) = (r₂ * c₂).map (algebraMap K'.O K'.E) := by
    rw [← hfrc, Polynomial.map_map, hφc]
  have hnr := res_mult K K' d φ hU s hgen p₂ r₂ c₂ hp₂m hr₂m hr₂r hdeg hmap
  have hu : IsUnit (resultant c₂ r₁) := by
    rw [← IsLocalRing.residue_ne_zero_iff_isUnit, ← resultant_map_map, hr₁r,
      resultant_X_sub_C_pow_right _ _ _ _ natDegree_map_le]
    exact mul_ne_zero (pow_ne_zero _ (neg_ne_zero.2 one_ne_zero)) (pow_ne_zero _ hnr)
  obtain ⟨k₁, hk₁⟩ := norm_res B₁.g B₂.P (LinearMap.charpoly_monic _)
  have hk₁' : Algebra.norm K.E (aeval B₁.g B₂.P) = (-1) ^ k₁ * resultant B₂.P B₁.P := hk₁
  obtain ⟨k₂, hk₂⟩ := norm_res (E := K'.E) (A := B₁'.A) B₁'.g ((p₂.map φO).map (algebraMap K'.O K'.E)) (hfm.map _)
  have e : (aeval B₁'.g ((p₂.map φO).map (algebraMap K'.O K'.E)) : B₁.A) = aeval B₁.g B₂.P := by
    change eval₂ ψ₁ B₁.g ((p₂.map φO).map (algebraMap K'.O K'.E)) = _
    rw [Polynomial.map_map, eval₂_map, ← hp₂, aeval_map_algebraMap, aeval_def, ← RingHom.comp_assoc,
      hcomp B₁.A ψ₁ h₁]
  have hk₂' : @Algebra.norm K'.E B₁.A _ _ ψ₁.toAlgebra (aeval B₁.g B₂.P) =
      (-1) ^ k₂ * resultant (B₂'.P * c₂.map (algebraMap K'.O K'.E)) B₁'.P := by
    rw [← e, hc₂, ← hc']; exact hk₂
  have hmul := resultant_mul_left B₂'.P (c₂.map (algebraMap K'.O K'.E)) B₁'.P B₁'.P.natDegree le_rfl
  rw [← hPm₂.natDegree_mul (by rw [hc₂]; exact hc'm)] at hmul
  have hcu : resultant (c₂.map (algebraMap K'.O K'.E)) B₁'.P = algebraMap K'.O K'.E (resultant c₂ r₁) := by
    rw [← hr₁, natDegree_map_eq_of_injective hinj', natDegree_map_eq_of_injective hinj', resultant_map_map]
  calc val K.O (resultant B₁.P B₂.P) = val K.O (resultant B₂.P B₁.P) := by
        rw [resultant_comm, val_neg_one_pow]
    _ = val K.O (Algebra.norm K.E (aeval B₁.g B₂.P)) := by rw [hk₁', val_neg_one_pow]
    _ = d * val K'.O (@Algebra.norm K'.E B₁.A _ _ ψ₁.toAlgebra (aeval B₁.g B₂.P)) := by
        rw [norm_tower φ B₁ ψ₁ h₁, val_norm K K' d φ hU]
    _ = d * val K'.O (resultant B₂'.P B₁'.P) := by
        rw [hk₂', val_neg_one_pow, hmul, hcu, val_mul_unit _ _ hu]
    _ = d * val K'.O (resultant B₁'.P B₂'.P) := by
        rw [resultant_comm B₂'.P, val_neg_one_pow]

end GlobalTheory.UnitLemma.Unr.ResVal
end
end

