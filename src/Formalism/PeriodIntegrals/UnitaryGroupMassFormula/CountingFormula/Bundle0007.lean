import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.Bundle0005
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.Bundle0006

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.DensAtGoodOf
section
noncomputable section

namespace PI.UnitaryGroupMassFormula.CntFormula

open NumberField Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.CntLocal IsDedekindDomain
open Classical ValuativeRel

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def LocDens : Prop :=
  ∀ (F E : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [CommRing E] [Algebra F E]
    [TopologicalSpace E] [MeasurableSpace E] (M : Loc.Model F E),
    IsNonarchimedeanLocalField F → CharZero F →
    ∀ (V : Type) [AddCommGroup V] [Module E V] (H : Loc.HermSp M V) (Λ : Submodule M.L.O V),
      H.IsSelfDual Λ → ∀ ϖ : 𝒪[F], Irreducible ϖ →
      ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (G₀ : Matrix ι ι E), (∀ a b, G₀ a b ∈ M.L.O) →
        (∀ a b, G₀ b a = M.L.cj (G₀ a b)) → (∃ y ∈ M.L.O, G₀.det * y = 1) →
        Fintype.card ι ≤ Module.finrank E V →
        ∃ η : ℝ, (η = 1 ∨ η = -1) ∧
          H.dens ϖ Λ G₀ = Formalism.L2.SG.DensExact.densProd (Nat.card 𝓀[F]) η
            (Module.finrank E V) (Fintype.card ι) 0

def ETwo : Prop :=
  ∀ (F E : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [CommRing E] [Algebra F E]
    [TopologicalSpace E] (L : Loc.LocE F E),
    (∀ x : E, x ≠ 0 → IsUnit x) ∨ ∃ e : E ≃ₐ[F] F × F, ∀ x, e (L.cj x) = (e x).swap

def LocDensSplit : Prop :=
  ∀ (F E : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [CommRing E] [Algebra F E]
    [TopologicalSpace E] [MeasurableSpace E] (M : Loc.Model F E),
    IsNonarchimedeanLocalField F → CharZero F →
    (∃ e : E ≃ₐ[F] F × F, ∀ x, e (M.L.cj x) = (e x).swap) →
    ∀ (V : Type) [AddCommGroup V] [Module E V] (H : Loc.HermSp M V) (Λ : Submodule M.L.O V),
      H.IsSelfDual Λ → ∀ ϖ : 𝒪[F], Irreducible ϖ →
      ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (G₀ : Matrix ι ι E), (∀ a b, G₀ a b ∈ M.L.O) →
        (∀ a b, G₀ b a = M.L.cj (G₀ a b)) → (∃ y ∈ M.L.O, G₀.det * y = 1) →
        Fintype.card ι ≤ Module.finrank E V →
          H.dens ϖ Λ G₀ = Formalism.L2.SG.DensExact.densProd (Nat.card 𝓀[F]) 1
            (Module.finrank E V) (Fintype.card ι) 0

def LocDensField : Prop :=
  ∀ (F E : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [CommRing E] [Algebra F E]
    [TopologicalSpace E] [MeasurableSpace E] (M : Loc.Model F E),
    IsNonarchimedeanLocalField F → CharZero F →
    (∀ x : E, x ≠ 0 → IsUnit x) →
    ∀ (V : Type) [AddCommGroup V] [Module E V] (H : Loc.HermSp M V) (Λ : Submodule M.L.O V),
      H.IsSelfDual Λ → ∀ ϖ : 𝒪[F], Irreducible ϖ →
      ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (G₀ : Matrix ι ι E), (∀ a b, G₀ a b ∈ M.L.O) →
        (∀ a b, G₀ b a = M.L.cj (G₀ a b)) → (∃ y ∈ M.L.O, G₀.det * y = 1) →
        Fintype.card ι ≤ Module.finrank E V →
          H.dens ϖ Λ G₀ = Formalism.L2.SG.DensExact.densProd (Nat.card 𝓀[F]) (-1)
            (Module.finrank E V) (Fintype.card ι) 0

theorem locDens_of (h0 : ETwo) (hS : LocDensSplit) (hF : LocDensField) : LocDens := by
  intro F E _ _ _ _ _ _ _ M hl hc V _ _ H Λ hΛ ϖ hϖ ι _ _ G₀ h1 h2 h3 h4
  rcases h0 F E M.L with hE | hE
  · exact ⟨-1, Or.inr rfl, hF F E M hl hc hE V H Λ hΛ ϖ hϖ ι G₀ h1 h2 h3 h4⟩
  · exact ⟨1, Or.inl rfl, hS F E M hl hc hE V H Λ hΛ ϖ hϖ ι G₀ h1 h2 h3 h4⟩

theorem star_eq_conjF (D : Formalism.BasicNotions.D7) (x : D.host.E) : star x = D.conjF x := by
  rw [D.conjF_eq]
  have := D.host.isCMField_hostE
  apply D.host.φ₀.injective
  change D.host.φ₀ (NumberField.IsCMField.complexConj D.host.E x) = D.host.φ₀ (D.host.conj x)
  rw [NumberField.IsCMField.complexEmbedding_complexConj]
  exact (D.host.toHostAx.conjE_apply D.host.φ₀ x).symm

theorem ga_herm (D : Formalism.BasicNotions.D7) (u u' : D.what₂.Word) (Z : MatZ D) (a b) :
    Ga (Tn u) (Tn u') Z b a = star (Ga (Tn u) (Tn u') Z a b) := by
  rcases a with a | a <;> rcases b with b | b <;>
    simp [Ga, Matrix.fromBlocks, Matrix.conjTranspose_apply, and_comm] <;> split_ifs <;> simp [Tn]

theorem gaPlus_herm (D : Formalism.BasicNotions.D7) (δ : ∀ p : PlF D, (D.s.atP p).Fp)
    (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep) (p : PlF D) (hA : Agree δ M p)
    (hs : (M p).split = none) (u u' : D.what₂.Word) (Z : MatZ D) (a b) :
    GaPlus M δ p (Tn u) (Tn u') Z b a = (M p).L.cj (GaPlus M δ p (Tn u) (Tn u') Z a b) := by
  have hcj : (M p).L.cj = (D.s.atP p).cj := hA.2.2.1
  simp only [GaPlus, hs, GaLoc, Matrix.of_apply]
  rw [map_mul, map_mul, hcj, (D.s.atP p).cj_ιE, ← star_eq_conjF, ← ga_herm, ← hcj, (M p).L.cj_cj]
  ring

theorem densAtGood_at (h : LocDens) (D : Formalism.BasicNotions.D7) (δ : ∀ p : PlF D, (D.s.atP p).Fp)
    (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep) (hA : ∀ p, Agree δ M p) (L : LocSp D M)
    (u u' : D.what₂.Word) (ϖ : ∀ p : PlF D, 𝒪[(D.s.atP p).Fp]) (hϖ : ∀ p, Irreducible (ϖ p))
    (Z : MatZ D) (p : PlF D) (hG : GoodAt L δ (Tn u) (Tn u') Z p) :
    ∃ η : ℝ, (η = 1 ∨ η = -1) ∧
      densP L δ ϖ (Tn u) (Tn u') Z p =
        Formalism.L2.SG.DensExact.densProd (Nat.card 𝓀[(D.s.atP p).Fp]) η D.R.r (2 * (D.R.rS + 1)) 0 := by
  obtain ⟨hs, hSD, hI, hdet⟩ := hG
  have hl : IsNonarchimedeanLocalField (D.s.atP p).Fp := (D.s.atP p).lf
  have hc : CharZero (D.s.atP p).Fp := (D.s.atP p).char0
  have hcard : Fintype.card (Fin (D.R.rS + 1) ⊕ Fin (D.R.rS + 1)) = 2 * (D.R.rS + 1) := by
    rw [Fintype.card_sum, Fintype.card_fin]; ring
  have hr : Module.finrank (D.s.atP p).Ep (L.V p) = D.R.r := L.rank p
  have hm : Fintype.card (Fin (D.R.rS + 1) ⊕ Fin (D.R.rS + 1)) ≤ Module.finrank (D.s.atP p).Ep (L.V p) := by
    rw [hcard, hr]; have := tuple_short D; omega
  have hh := gaPlus_herm D δ M p (hA p) hs u u' Z
  obtain ⟨η, hη, he⟩ := h (D.s.atP p).Fp (D.s.atP p).Ep (M p) hl hc (L.V p) (L.H p) (lattice₂ L p (VS D).L0) hSD
    (ϖ p) (hϖ p) (Fin (D.R.rS + 1) ⊕ Fin (D.R.rS + 1)) (GaPlus M δ p (Tn u) (Tn u') Z) hI hh
    hdet hm
  refine ⟨η, hη, ?_⟩
  rw [hr, hcard] at he
  exact he

theorem densAtGood_of (h : LocDens) : DensAtGood :=
  fun D δ M hA L u u' _ _ _ _ ϖ hϖ Z p hG => densAtGood_at h D δ M hA L u u' ϖ hϖ Z p hG

theorem densAtGood_of' (h0 : ETwo) (hS : LocDensSplit) (hF : LocDensField) : DensAtGood :=
  densAtGood_of (locDens_of h0 hS hF)

end PI.UnitaryGroupMassFormula.CntFormula
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.GzNeOfTotPos
section
noncomputable section

namespace PI.UnitaryGroupMassFormula.CntFormula

open NumberField Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.CntLocal IsDedekindDomain
open Classical ValuativeRel

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def SelfDualCof : Prop :=
  ∀ (D : Formalism.BasicNotions.D7) (δ : ∀ p : PlF D, (D.s.atP p).Fp) (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep),
    (∀ p, Agree δ M p) → ∀ L : LocSp D M,
      ∀ᶠ p in Filter.cofinite, (L.H p).IsSelfDual (lattice₂ L p (VS D).L0)

def DeltaUnitCof : Prop :=
  ∀ (D : Formalism.BasicNotions.D7) (δ : ∀ p : PlF D, (D.s.atP p).Fp) (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep),
    (∀ p, Agree δ M p) → ∀ᶠ p in Filter.cofinite, δ p ∈ 𝒪[(D.s.atP p).Fp] ∧ (δ p)⁻¹ ∈ 𝒪[(D.s.atP p).Fp]

def IotaIntCof : Prop :=
  ∀ (D : Formalism.BasicNotions.D7) (x : D.host.E), ∀ᶠ p in Filter.cofinite, (D.s.atP p).ιE x ∈ (D.s.atP p).O

def DetGaNe : Prop :=
  ∀ (D : Formalism.BasicNotions.D7) (T T' : D.host.E) (Z : MatZ D), GZ T T' Z ≠ 0 → (Ga T T' Z).det ≠ 0

def GaCof : Prop :=
  ∀ (D : Formalism.BasicNotions.D7) (δ : ∀ p : PlF D, (D.s.atP p).Fp) (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep),
    (∀ p, Agree δ M p) → ∀ (T T' : D.host.E) (Z : MatZ D), (Ga T T' Z).det ≠ 0 →
      ∀ᶠ p in Filter.cofinite, (∀ a b, GaPlus M δ p T T' Z a b ∈ (M p).L.O) ∧
        ∃ y ∈ (M p).L.O, (GaPlus M δ p T T' Z).det * y = 1

end PI.UnitaryGroupMassFormula.CntFormula
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.OFRepFin
section
noncomputable section

namespace PI.UnitaryGroupMassFormula.CntFormula

open NumberField Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.CntLocal
open Classical

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem hT_sum_left (D : Formalism.BasicNotions.D7) {ι : Type} (s : Finset ι) (c : ι → D.host.E) (e : ι → (VS D).V)
    (w : (VS D).V) : (VS D).hT (∑ a ∈ s, c a • e a) w = ∑ a ∈ s, star (c a) * (VS D).hT (e a) w := by
  rw [map_sum, LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [LinearMap.map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, starRingEnd_apply]

theorem hT_sum_right (D : Formalism.BasicNotions.D7) {ι : Type} (s : Finset ι) (c : ι → D.host.E) (e : ι → (VS D).V)
    (v : (VS D).V) : (VS D).hT v (∑ a ∈ s, c a • e a) = ∑ a ∈ s, c a * (VS D).hT v (e a) := by
  rw [map_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [map_smul, smul_eq_mul]

theorem hT_swap (D : Formalism.BasicNotions.D7) (x y : (VS D).V) : (VS D).hT y x = star ((VS D).hT x y) := by
  have h := (VS D).herm.eq x y
  rw [starRingEnd_apply] at h
  exact h.symm

theorem pW_dec (D : Formalism.BasicNotions.D7) (v : (VS D).V) :
    v = pW D v + ∑ a, (VS D).hT (D.sp.hypF a) v • D.sp.hypE a + ∑ a, (VS D).hT (D.sp.hypE a) v • D.sp.hypF a
      - ((VS D).hT D.sp.zm v / (D.sp.T : D.host.E)) • D.sp.zm := by
  unfold pW
  abel

theorem delta_zero {K : Type} [Field K] [StarRing K] {r : ℕ} (β Δ : Matrix (Fin r) (Fin (r + 1)) K)
    (R : Matrix (Fin (r + 1)) (Fin r) K) (hR : β * R = 1) (hΔR : Δ * R = 0)
    (hM : Δ.conjTranspose * β + β.conjTranspose * Δ = 0) : Δ = 0 := by
  have h : (Δ.conjTranspose * β + β.conjTranspose * Δ) * R = (0 : Matrix (Fin (r + 1)) (Fin (r + 1)) K) * R := by rw [hM]
  rw [Matrix.add_mul, Matrix.mul_assoc, Matrix.mul_assoc, hR, hΔR, Matrix.mul_one, Matrix.mul_zero,
    add_zero, Matrix.zero_mul] at h
  rw [← Matrix.conjTranspose_conjTranspose Δ, h, Matrix.conjTranspose_zero]

theorem finite_level_index : FinK := by
  intro D T T' F0 Λ hF Z R hR Wf Af hWf hAf
  obtain ⟨-, -, hFe, -, c, hc, hFz⟩ := hF
  have hE : ∀ x, Good D T' F0 Λ Z x → ∀ (a : Fin D.R.rS) b,
      (VS D).hT (D.sp.hypE a) (fr D x b) = betaZ D Z a b := by
    intro x hx a b
    have h := hx.2.1 (Fin.castSucc a) b
    simp only [brS, FlagG.fvec, Fin.snoc_castSucc, hFe] at h
    simpa [betaZ] using h
  have hzm : ∀ x, Good D T' F0 Λ Z x → ∀ b,
      star c * (VS D).hT D.sp.zm (fr D x b) = Z (Fin.last _) b := by
    intro x hx b
    have h := hx.2.1 (Fin.last _) b
    simp only [brS, FlagG.fvec, Fin.snoc_last, hFz] at h
    rw [LinearMap.map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, starRingEnd_apply] at h
    exact h
  have pW_sub : ∀ v v' : (VS D).V, pW D (v - v') = pW D v - pW D v' := by
    intro v v'
    simp only [pW, map_sub, sub_smul, Finset.sum_sub_distrib, sub_div]
    abel
  refine Set.Finite.of_injOn (f := fun x => (pWf D x, alM D x * R)) (t := Wf ×ˢ Af) ?_ ?_
    (hWf.prod hAf)
  · intro x hx
    exact ⟨hx.2.1, hx.2.2⟩
  intro x hx x' hx' hxx'
  obtain ⟨hp, hal⟩ := Prod.mk.inj hxx'
  obtain ⟨Δ, hΔ⟩ : ∃ Δ, Δ = alM D x - alM D x' := ⟨_, rfl⟩
  have huE : ∀ a b, (VS D).hT (D.sp.hypE a) (fr D x b - fr D x' b) = 0 := by
    intro a b
    rw [map_sub, hE x hx.1, hE x' hx'.1, sub_self]
  have huz : ∀ b, (VS D).hT D.sp.zm (fr D x b - fr D x' b) = 0 := by
    intro b
    have hsc : star c ≠ 0 := star_ne_zero.mpr hc
    have h0 : star c * ((VS D).hT D.sp.zm (fr D x b) - (VS D).hT D.sp.zm (fr D x' b)) = 0 := by
      rw [mul_sub, hzm x hx.1, hzm x' hx'.1, sub_self]
    rw [map_sub]
    exact (mul_eq_zero.mp h0).resolve_left hsc
  have huF : ∀ a b, (VS D).hT (D.sp.hypF a) (fr D x b - fr D x' b) = Δ a b := by
    intro a b
    rw [hΔ, Matrix.sub_apply, map_sub]
    rfl
  have hupW : ∀ b, pW D (fr D x b - fr D x' b) = 0 := by
    intro b
    rw [pW_sub]
    have h := congrFun hp b
    simp only [pWf] at h
    rw [h, sub_self]
  have hu : ∀ b, fr D x b - fr D x' b = ∑ a, Δ a b • D.sp.hypE a := by
    intro b
    conv_lhs => rw [pW_dec D (fr D x b - fr D x' b)]
    simp only [hupW, huE, huz, huF, zero_smul, Finset.sum_const_zero, zero_div, zero_add, add_zero,
      sub_zero]
  have hΔR : Δ * R = 0 := by
    rw [hΔ, Matrix.sub_mul, hal, sub_self]
  have hM : Δ.conjTranspose * betaZ D Z + (betaZ D Z).conjTranspose * Δ = 0 := by
    ext a b
    have hG : (VS D).hT (fr D x a) (fr D x b) = (VS D).hT (fr D x' a) (fr D x' b) := by
      rw [hx.1.2.2 a b, hx'.1.2.2 a b]
    have hxa : fr D x a = fr D x' a + ∑ c, Δ c a • D.sp.hypE c := by
      rw [← hu a]
      abel
    have hxb : fr D x b = fr D x' b + ∑ c, Δ c b • D.sp.hypE c := by
      rw [← hu b]
      abel
    rw [hxa, hxb] at hG
    simp only [map_add, LinearMap.add_apply] at hG
    have h1 : (VS D).hT (∑ c, Δ c a • D.sp.hypE c) (∑ c, Δ c b • D.sp.hypE c) = 0 := by
      rw [hT_sum_left]
      refine Finset.sum_eq_zero fun c _ => ?_
      rw [hT_sum_right]
      simp [D.sp.hyp_ee]
    have h2 : (VS D).hT (fr D x' a) (∑ c, Δ c b • D.sp.hypE c) =
        ((betaZ D Z).conjTranspose * Δ) a b := by
      rw [hT_sum_right, Matrix.mul_apply]
      refine Finset.sum_congr rfl fun c _ => ?_
      rw [Matrix.conjTranspose_apply, ← hE x' hx'.1 c a, hT_swap D (D.sp.hypE c) (fr D x' a)]
      ring
    have h3 : (VS D).hT (∑ c, Δ c a • D.sp.hypE c) (fr D x' b) = (Δ.conjTranspose * betaZ D Z) a b := by
      rw [hT_sum_left, Matrix.mul_apply]
      refine Finset.sum_congr rfl fun c _ => ?_
      rw [Matrix.conjTranspose_apply, hE x' hx'.1 c b]
    rw [Matrix.add_apply, Matrix.zero_apply, ← h2, ← h3]
    rw [h1, add_zero] at hG
    linear_combination hG
  have hΔ0 : Δ = 0 := delta_zero (betaZ D Z) Δ R hR hΔR hM
  have hfr : ∀ b, fr D x b = fr D x' b := by
    intro b
    have h := hu b
    rw [hΔ0] at h
    simp only [Matrix.zero_apply, zero_smul, Finset.sum_const_zero] at h
    exact sub_eq_zero.mp h
  refine Prod.ext (funext fun i => ?_) ?_
  · have h := hfr (Fin.castSucc i)
    simpa [fr] using h
  · have h := hfr (Fin.last _)
    simpa [fr] using h

end PI.UnitaryGroupMassFormula.CntFormula
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.OFRepRank
section
noncomputable section

namespace PI.UnitaryGroupMassFormula.CntFormula

open NumberField Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.CntLocal
open Classical

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem rank_gram : RankG := by
  intro D T T' Z hG
  classical
  by_cases hdet : Z.det = 0
  · have hm : leadMinorE Z D.R.rS ≠ 0 := by
      intro hm
      apply hG
      have h1 : leadMinorE Z (D.R.rS + 1) = 0 := by
        unfold Formalism.MainNotions.S.leadMinorE
        rw [dif_pos le_rfl, Fin.castLE_rfl, Matrix.submatrix_id_id]
        exact hdet
      simp [Formalism.L2.SG.CntLocal.GZ, h1, hm]
    have h : D.R.rS ≤ D.R.rS + 1 := Nat.le_succ _
    set B := Z.submatrix (Fin.castLE h) (Fin.castLE h) with hB
    have hBdet : B.det ≠ 0 := by
      have e : leadMinorE Z D.R.rS = B.det := by
        unfold Formalism.MainNotions.S.leadMinorE
        rw [dif_pos h]
      rwa [← e]
    refine ⟨Matrix.of fun j i => if hj : (j : ℕ) < D.R.rS then B⁻¹ ⟨j, hj⟩ i else 0, ?_⟩
    have hBB : B * B⁻¹ = 1 := Matrix.mul_nonsing_inv B (isUnit_iff_ne_zero.2 hBdet)
    ext a i
    rw [← hBB]
    simp only [Matrix.mul_apply, betaZ, Matrix.submatrix_apply, Matrix.of_apply, Fin.sum_univ_castSucc,
      Fin.coe_castSucc, Fin.is_lt, dif_pos, Fin.val_last, lt_irrefl, not_false_eq_true, dif_neg, mul_zero,
      add_zero, id]
    rfl
  · refine ⟨(Z⁻¹).submatrix id Fin.castSucc, ?_⟩
    have hZ : Z * Z⁻¹ = 1 := Matrix.mul_nonsing_inv Z (isUnit_iff_ne_zero.2 hdet)
    unfold betaZ
    rw [← Matrix.submatrix_mul _ _ _ _ _ Function.bijective_id, hZ]
    exact Matrix.submatrix_one_embedding Fin.castSuccEmb

end PI.UnitaryGroupMassFormula.CntFormula
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.ResidueFieldCard
section
noncomputable section

namespace PI.UnitaryGroupMassFormula.CntFormula

open NumberField IsDedekindDomain ValuativeRel Formalism.MainNotions.S Formalism.MainNotions.S.LocalSplitGroups

theorem resCard_loc {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {sig : E →ₐ[F] E} {p : HeightOneSpectrum (𝓞 F)} (A : Loc.LocAt F E sig p) :
    Nat.card 𝓀[A.Fp] = p.asIdeal.absNorm := by
  have := A.lf
  have key : ∀ x y : F, valuation A.Fp (A.ιF x) ≤ valuation A.Fp (A.ιF y) ↔
      p.valuation F x ≤ p.valuation F y := fun x y => by
    rw [← Valuation.vle_iff_le]; exact A.val x y
  have keyle1 : ∀ x : F, valuation A.Fp (A.ιF x) ≤ 1 ↔ p.valuation F x ≤ 1 := fun x => by
    have h := key x 1
    rwa [map_one, map_one, map_one] at h
  have keylt1 : ∀ x : F, valuation A.Fp (A.ιF x) < 1 ↔ p.valuation F x < 1 := fun x => by
    have h := key 1 x
    rw [map_one, map_one, map_one] at h
    rw [← not_le, ← not_le, h]
  let f : 𝓞 F →+* 𝒪[A.Fp] :=
    { toFun := fun x => ⟨A.ιF (algebraMap (𝓞 F) F x),
        (keyle1 _).2 (p.valuation_le_one (K := F) x)⟩
      map_one' := by ext; simp
      map_mul' := by intro a b; ext; simp
      map_zero' := by ext; simp
      map_add' := by intro a b; ext; simp }
  let φ : 𝓞 F →+* 𝓀[A.Fp] := (IsLocalRing.residue 𝒪[A.Fp]).comp f
  have hmax : ∀ w : 𝒪[A.Fp], w ∈ IsLocalRing.maximalIdeal 𝒪[A.Fp] ↔ valuation A.Fp (w : A.Fp) < 1 :=
    fun w => by
      rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
      exact Valuation.Integer.not_isUnit_iff_valuation_lt_one
  have hker : RingHom.ker φ = p.asIdeal := by
    ext x
    rw [RingHom.mem_ker, RingHom.comp_apply, IsLocalRing.residue_eq_zero_iff, hmax]
    exact (keylt1 _).trans (p.valuation_lt_one_iff_mem (K := F) x)
  have hsurj : Function.Surjective φ := by
    intro z0
    obtain ⟨z, rfl⟩ := IsLocalRing.residue_surjective z0
    have hS : {w : A.Fp | valuation A.Fp (w - z) < 1} ∈ nhds (z : A.Fp) :=
      (IsValuativeTopology.hasBasis_nhds' (z : A.Fp)).mem_of_mem one_ne_zero
    obtain ⟨w, ⟨x', rfl⟩, hw⟩ := A.dense.inter_nhds_nonempty hS
    have hw' : valuation A.Fp (A.ιF x' - z) < 1 := hw
    have hx' : p.valuation F x' ≤ 1 := by
      rw [← keyle1]
      have hz : valuation A.Fp (z : A.Fp) ≤ 1 := z.2
      have := Valuation.map_add_le (valuation A.Fp) hw'.le hz
      simpa using this
    obtain ⟨a, ha⟩ := IsDedekindDomain.HeightOneSpectrum.exists_valuation_sub_lt_of_integer
      (v := p) (K := F) hx' 1
    have ha' : p.valuation F (algebraMap (𝓞 F) F a - x') < 1 := by simpa using ha
    refine ⟨a, ?_⟩
    rw [RingHom.comp_apply, ← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff, hmax]
    have h1 : valuation A.Fp (A.ιF (algebraMap (𝓞 F) F a - x')) < 1 := (keylt1 _).2 ha'
    have h2 := Valuation.map_add_lt (valuation A.Fp) h1 hw'
    have he : ((f a - z : 𝒪[A.Fp]) : A.Fp) =
        A.ιF (algebraMap (𝓞 F) F a - x') + (A.ιF x' - z) := by
      simp only [map_sub]
      show A.ιF (algebraMap (𝓞 F) F a) - (z : A.Fp) = _
      ring
    rw [he]
    exact h2
  rw [← hker, Ideal.absNorm_apply, Submodule.cardQuot_apply]
  exact (Nat.card_congr (RingHom.quotientKerEquivOfSurjective hsurj).toEquiv).symm

theorem residue_field_card : ResCard := fun D p => resCard_loc _

end PI.UnitaryGroupMassFormula.CntFormula
end
end

