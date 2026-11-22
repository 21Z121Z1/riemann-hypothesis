import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CrystallineOrdinaryIdeals.Imports
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.Bundle0007
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.Bundle0006
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.OrdinaryDeformation
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.TriDefs
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CrystallineOrdinaryIdeals.Bundle0001

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CrystallineOrdinaryIdeals.ChosenFrobeniusIsFrobenius
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal Module UpperTheory.V.Loc UpperTheory.V.U3 UpperTheory.V.Alg IsLocalRing Polynomial Topology

namespace GlobalTheory.OrdLoc

variable {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsLocalRing O] [Algebra ℤ_[l] O]

theorem hl_normal' (D : Dat3 l O) : D.HL.Normal := by
  unfold Dat3.HL; infer_instance

theorem hl_isOpen' (D : Dat3 l O) : IsOpen (D.HL : Set (GQ l)) := by
  have e : (D.η.ker : Set (GQ l)) = (D.Kv.1.fixingSubgroup : Set (GQ l)) := by
    ext g; exact D.η_ker g
  have h1 : IsOpen (D.η.ker : Set (GQ l)) := by
    rw [e]; haveI := D.Kv.2; exact IntermediateField.fixingSubgroup_isOpen D.Kv.1
  exact h1.inter D.τ_open

theorem finiteIndex_of_open' (H : OpenSubgroup (GQ l)) : (H : Subgroup (GQ l)).FiniteIndex := by
  haveI : CompactSpace (GQ l) := inferInstanceAs (CompactSpace (Om l ≃ₐ[ℚ_[l]] Om l))
  exact Subgroup.finiteIndex_of_finite_quotient

theorem exists_isFr (D : Dat3 l O) : ∃ σ, IsFr D σ := by
  haveI : CompactSpace (GQ l) := inferInstanceAs (CompactSpace (Om l ≃ₐ[ℚ_[l]] Om l))
  haveI hHn : D.HL.Normal := hl_normal' D
  have hHo : IsOpen (D.HL : Set (GQ l)) := hl_isOpen' D
  obtain ⟨hIn, -, -, ⟨σ₀, hσ₀⟩, -⟩ := iqBasic l
  haveI : D.HL.FiniteIndex := finiteIndex_of_open' ⟨D.HL, hHo⟩
  set N : Subgroup (GQ l) := D.HL ⊔ Iq l with hN
  haveI : N.FiniteIndex := Subgroup.finiteIndex_of_le le_sup_left
  haveI : N.Normal := Subgroup.sup_normal _ _
  set q : GQ l ⧸ N := (σ₀ : GQ l ⧸ N)
  set m := orderOf q with hm
  have hm1 : 1 ≤ m := orderOf_pos q
  have hmN : σ₀ ^ m ∈ N := by
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow]; exact pow_orderOf_eq_one q
  obtain ⟨h, hh, i₀, hi₀, hhi⟩ := Subgroup.mem_sup_of_normal_right.1 hmN
  let φ := QuotientGroup.mk' (Iq l)
  have hφ : ∀ {x}, φ x = 1 ↔ x ∈ Iq l := fun {x} => QuotientGroup.eq_one_iff x
  have hφm : φ σ₀ ^ m = φ h := by
    rw [← map_pow, ← hhi, map_mul, hφ.2 hi₀, mul_one]
  refine ⟨h, ⟨hh, ?_⟩, σ₀, m, hσ₀, hm1, ?_⟩
  ·
    rw [eq_top_iff]
    intro g _
    rw [← SetLike.mem_coe, Subgroup.topologicalClosure_coe]
    rw [mem_closure_iff]
    intro U hU hgU
    have hdense := frobDense σ₀ hσ₀
    have hV : IsOpen (D.HL.subtype '' U) := (hHo.isOpenEmbedding_subtypeVal).isOpenMap U hU
    have hcl : (D.HL.subtype g) ∈ closure ((Iq l ⊔ Subgroup.zpowers σ₀ : Subgroup (GQ l)) : Set (GQ l)) := by
      rw [← Subgroup.topologicalClosure_coe, hdense]; trivial
    obtain ⟨x, ⟨u, huU, rfl⟩, hxT⟩ := mem_closure_iff.1 hcl _ hV ⟨g, hgU, rfl⟩
    obtain ⟨i, hi, z, hz, hiz⟩ := Subgroup.mem_sup_of_normal_left.1 hxT
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hz
    change i * σ₀ ^ k = (u : GQ l) at hiz
    have hkN : σ₀ ^ k ∈ N := by
      have : σ₀ ^ k = i⁻¹ * (u : GQ l) := by rw [← hiz]; group
      rw [this]
      exact N.mul_mem (Subgroup.mem_sup_right (Subgroup.inv_mem _ hi)) (Subgroup.mem_sup_left u.2)
    have hdvd : (m : ℤ) ∣ k := by
      rw [hm, orderOf_dvd_iff_zpow_eq_one, ← QuotientGroup.mk_zpow, QuotientGroup.eq_one_iff]; exact hkN
    obtain ⟨j, rfl⟩ := hdvd
    have hφu : φ (u : GQ l) = φ h ^ j := by
      rw [← hiz, map_mul, hφ.2 hi, one_mul, map_zpow, zpow_mul, zpow_natCast, hφm]
    have hy : (u : GQ l) * h ^ (-j) ∈ Iq l := by
      rw [← hφ, map_mul, map_zpow, hφu, zpow_neg, mul_inv_cancel]
    refine ⟨u, huU, ?_⟩
    have e : u = (⟨(u : GQ l) * h ^ (-j), D.HL.mul_mem u.2 (D.HL.zpow_mem hh _)⟩ : ↥D.HL) * (⟨h, hh⟩ : ↥D.HL) ^ j := by
      ext; simp
    rw [SetLike.mem_coe, e]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hy) (Subgroup.mem_sup_right (Subgroup.zpow_mem_zpowers _ _))
  · rw [← hhi]; simpa using Subgroup.inv_mem _ hi₀

theorem fr_isFr : ∀ {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsLocalRing O] [Algebra ℤ_[l] O] (D : Dat3 l O),
    GlobalTheory.OrdLoc.IsFr D (GlobalTheory.OrdLoc.fr D) := by
  intro l _ O _ _ _ D
  exact Classical.epsilon_spec (exists_isFr D)

end GlobalTheory.OrdLoc
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CrystallineOrdinaryIdeals.CrystallineDeformationFibreProductAmalgamation
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal Module UpperTheory.V.Loc UpperTheory.V.U3 UpperTheory.V.Alg IsLocalRing Polynomial Topology

namespace GlobalTheory.FibreGlue

theorem main : ∀ {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O] [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O] [IsAdicComplete (maximalIdeal O) O] (D : Dat3 l O) (E : Type) [Field E] [Algebra ℚ_[l] E] [Module.Finite ℚ_[l] E] [Algebra O E] [Algebra ℤ_[l] E] [IsScalarTower ℤ_[l] O E] [IsScalarTower ℤ_[l] ℚ_[l] E] (B : Type) [CommRing B] [Algebra ℚ_[l] B] [Module.Finite ℚ_[l] B] [Algebra O B] [Algebra ℤ_[l] B] [IsScalarTower ℤ_[l] O B] [IsScalarTower ℤ_[l] ℚ_[l] B] [Algebra E B] [IsScalarTower O E B] [IsScalarTower ℚ_[l] E B] (π : B →ₐ[E] E) (hπ : ∀ a, π a = 0 → IsNilpotent a) (C : Type) [CommRing C] [Algebra ℚ_[l] C] [Module.Finite ℚ_[l] C] [Algebra O C] [Algebra ℤ_[l] C] [IsScalarTower ℤ_[l] O C] [IsScalarTower ℤ_[l] ℚ_[l] C] [Algebra E C] [IsScalarTower O E C] [IsScalarTower ℚ_[l] E C] (πC : C →ₐ[E] E) (hπC : ∀ a, πC a = 0 → IsNilpotent a) (T : Type) [CommRing T] [Algebra ℚ_[l] T] [Module.Finite ℚ_[l] T] [Algebra O T] [Algebra ℤ_[l] T] [IsScalarTower ℤ_[l] O T] [IsScalarTower ℤ_[l] ℚ_[l] T] [Algebra E T] [IsScalarTower O E T] [IsScalarTower ℚ_[l] E T] (πT : T →ₐ[E] E) (hπT : ∀ a, πT a = 0 → IsNilpotent a) (p₁ : T →ₐ[E] B) (p₂ : T →ₐ[E] C), π.comp p₁ = πT → πC.comp p₂ = πT → (∀ b c, π b = πC c → ∃! t, p₁ t = b ∧ p₂ t = c) → ∀ (r₁ : GQ l →* GG 3 B) (r₂ : GQ l →* GG 3 C), D.InDcr (π : B →+* E) r₁ → D.InDcr (πC : C →+* E) r₂ → ∃ r : GQ l →* GG 3 T, D.InDcr (πT : T →+* E) r ∧ (GG.map (p₁ : T →+* B)).comp r = r₁ ∧ (GG.map (p₂ : T →+* C)).comp r = r₂ := by
  intro l _ O _ _ _ _ _ _ _ D E _ _ _ _ _ _ _ B _ _ _ _ _ _ _ _ _ _ π hπ C _ _ _ _ _ _ _ _ _ _ πC hπC T _ _ _ _ _ _ _ _ _ _ πT hπT p₁ p₂ h1 h2 huniq r₁ r₂ hr₁ hr₂
  have hpt : ∀ x, π (p₁ x) = πC (p₂ x) := fun x => by
    rw [← AlgHom.comp_apply, h1, ← AlgHom.comp_apply, h2]
  have hf : ∀ x y, (p₁ : T →+* B) x = (p₁ : T →+* B) y → (p₂ : T →+* C) x = (p₂ : T →+* C) y → x = y := by
    intro x y e1 e2
    obtain ⟨t, -, ht⟩ := huniq (p₁ x) (p₂ x) (hpt x)
    exact (ht x ⟨rfl, rfl⟩).trans (ht y ⟨e1.symm, e2.symm⟩).symm
  have hq : ∀ b c, (π : B →+* E) b = (πC : C →+* E) c → ∃ x, (p₁ : T →+* B) x = b ∧ (p₂ : T →+* C) x = c :=
    fun b c e => (huniq b c e).exists
  have hred : (GG.map (π : B →+* E)).comp r₁ = (GG.map (πC : C →+* E)).comp r₂ := hr₁.red.trans hr₂.red.symm
  obtain ⟨r, e1, e2⟩ := OrdinaryDeformation.glue_hom (p₁ : T →+* B) (p₂ : T →+* C) (π : B →+* E) (πC : C →+* E) hf hq r₁ r₂ hred
  refine ⟨r, ?_, e1, e2⟩
  have hd := OrdinaryDeformation.dcr_pair (D := D) (p₁.restrictScalars ℚ_[l]) (p₂.restrictScalars ℚ_[l]) hf
    (π := (π : B →+* E)) (π' := (πC : C →+* E)) (r := r) (by rw [← e1] at hr₁; exact hr₁) (by rw [← e2] at hr₂; exact hr₂)
  have hc : (π : B →+* E).comp ((p₁.restrictScalars ℚ_[l] : T →ₐ[ℚ_[l]] B) : T →+* B) = (πT : T →+* E) :=
    RingHom.ext fun x => by
      change π (p₁ x) = πT x
      rw [← AlgHom.comp_apply, h1]
  rw [hc] at hd
  exact hd

end GlobalTheory.FibreGlue
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CrystallineOrdinaryIdeals.ExistsFiniteLocalLiftOfSaturatedIdeal
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal Module UpperTheory.V.Loc UpperTheory.V.U3 UpperTheory.V.Alg IsLocalRing Polynomial Topology

namespace GlobalTheory.ThickenSaturated

theorem isLocalRing_quot_pow {A : Type} [CommRing A] (m : Ideal A) [hm : m.IsMaximal] (k : ℕ)
    (hk : k ≠ 0) : IsLocalRing (A ⧸ m ^ k) := by
  have hne : m ^ k ≠ ⊤ := fun h => hm.ne_top (top_le_iff.1 (h ▸ Ideal.pow_le_self hk))
  haveI : Nontrivial (A ⧸ m ^ k) := Ideal.Quotient.nontrivial_iff.2 hne
  obtain ⟨M0, hM0⟩ := Ideal.exists_maximal (A ⧸ m ^ k)
  have key : ∀ M : Ideal (A ⧸ m ^ k), M.IsMaximal → M.comap (Ideal.Quotient.mk (m ^ k)) = m := by
    intro M hM
    have h1 : (M.comap (Ideal.Quotient.mk (m ^ k))).IsMaximal :=
      Ideal.comap_isMaximal_of_surjective _ Ideal.Quotient.mk_surjective
    have h2 : m ^ k ≤ M.comap (Ideal.Quotient.mk (m ^ k)) := by
      intro x hx
      rw [Ideal.mem_comap, Ideal.Quotient.eq_zero_iff_mem.2 hx]
      exact M.zero_mem
    have h3 : m ≤ M.comap (Ideal.Quotient.mk (m ^ k)) := h1.isPrime.le_of_pow_le h2
    exact (hm.eq_of_le h1.ne_top h3).symm
  exact IsLocalRing.of_unique_max_ideal ⟨M0, hM0, fun M hM =>
    Ideal.comap_injective_of_surjective _ Ideal.Quotient.mk_surjective
      ((key M hM).trans (key M0 hM0).symm)⟩

theorem core {K : Type} [Field K] {A : Type} [CommRing A] [IsNoetherianRing A] [Algebra K A]
    (δ : A) (hδ : ∀ a, δ * a = 0 → a = 0)
    {B : Type} [CommRing B] [IsLocalRing B] [Algebra K B] [Module.Finite K B] (g : A →ₐ[K] B) :
    ∃ I : Ideal A, IsLocalRing (A ⧸ I) ∧ Module.Finite K (A ⧸ I) ∧ I ≤ RingHom.ker g ∧
      ∀ a, δ * a ∈ I → g a = 0 := by
  set mB := IsLocalRing.maximalIdeal B with hmB
  set m : Ideal A := mB.comap (g : A →+* B) with hm
  haveI : IsArtinianRing B := IsArtinianRing.of_finite K B
  obtain ⟨n, hn⟩ : IsNilpotent mB := by
    have := IsArtinianRing.isNilpotent_jacobson_bot (R := B)
    rwa [IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top] at this
  have hj : m ^ (n + 1) ≤ RingHom.ker g := by
    intro x hx
    have h1 : x ∈ (mB ^ (n + 1)).comap (g : A →+* B) := Ideal.le_comap_pow _ _ hx
    rw [pow_succ, hn, zero_mul, Ideal.zero_eq_bot, Ideal.mem_comap, Ideal.mem_bot] at h1
    exact RingHom.mem_ker.2 h1
  obtain ⟨k, hjk, hk⟩ := GlobalTheory.T.exists_le_mem_pow_of_mul_mem_pow_of_nonZeroDivisor m δ hδ (n + 1)
  haveI : m.IsPrime := Ideal.comap_isPrime _ _
  have hinj : Function.Injective (Ideal.quotientMapₐ mB g le_rfl : A ⧸ m →ₐ[K] B ⧸ mB) :=
    Ideal.quotientMap_injective
  haveI : Module.Finite K (B ⧸ mB) :=
    Module.Finite.of_surjective (Ideal.Quotient.mkₐ K mB).toLinearMap Ideal.Quotient.mk_surjective
  haveI hfin : Module.Finite K (A ⧸ m) := Module.Finite.of_injective (Ideal.quotientMapₐ mB g le_rfl : A ⧸ m →ₐ[K] B ⧸ mB).toLinearMap hinj
  haveI : IsArtinianRing (A ⧸ m) := IsArtinianRing.of_finite K (A ⧸ m)
  haveI : m.IsMaximal := Ideal.Quotient.maximal_of_isField _ (IsArtinianRing.isField_of_isDomain _)
  refine ⟨m ^ k, isLocalRing_quot_pow m k (by omega), GlobalTheory.T.module_finite_quotient_maximal_pow m hfin k,
    (Ideal.pow_le_pow_right hjk).trans hj, fun a ha => ?_⟩
  exact RingHom.mem_ker.1 (hj (hk a ha))

theorem main : ∀ {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [Algebra ℤ_[l] O] (R : Type) [CommRing R] [Algebra O R] [IsNoetherianRing R] (J : Ideal R) (d : R), (l : R) ∣ d → (∀ a, d * a ∈ J → a ∈ J) → ∀ (B : Type) [CommRing B] [IsLocalRing B] [Algebra ℚ_[l] B] [Module.Finite ℚ_[l] B] [Algebra O B] [Algebra ℤ_[l] B] [IsScalarTower ℤ_[l] O B] [IsScalarTower ℤ_[l] ℚ_[l] B] (f : R →ₐ[O] B), J ≤ RingHom.ker f → ∃ (B' : Type) (_ : CommRing B') (_ : IsLocalRing B') (_ : Algebra ℚ_[l] B') (_ : Module.Finite ℚ_[l] B') (_ : Algebra O B') (_ : Algebra ℤ_[l] B') (_ : IsScalarTower ℤ_[l] O B') (_ : IsScalarTower ℤ_[l] ℚ_[l] B') (f' : R →ₐ[O] B') (q : B' →ₐ[ℚ_[l]] B), J ≤ RingHom.ker f' ∧ (∀ a, q (f' a) = f a) ∧ ∀ b, f' d * b = 0 → q b = 0 := by
  intro l hl O _ _ R _ _ _ J d _ hdJ B _ _ _ _ _ _ _ _ f hJf
  let x : R ⧸ J := Ideal.Quotient.mk J (l : R)
  let A := Localization.Away x
  haveI : IsNoetherianRing A := IsLocalization.isNoetherianRing (Submonoid.powers x) A inferInstance
  have hlA : IsUnit ((l : ℕ) : A) := by
    have := IsLocalization.Away.algebraMap_isUnit (S := A) x
    simpa [x, map_natCast] using this
  let ψ₀ : ℤ_[l] →+* A := (algebraMap O A).comp (algebraMap ℤ_[l] O)
  have hψ₀ : ∀ y : nonZeroDivisors ℤ_[l], IsUnit (ψ₀ y) := by
    rintro ⟨y, hy⟩
    have hy0 : y ≠ 0 := nonZeroDivisors.ne_zero hy
    show IsUnit (ψ₀ y)
    rw [PadicInt.unitCoeff_spec hy0, map_mul, map_pow, map_natCast]
    exact ((Units.isUnit _).map ψ₀).mul (hlA.pow _)
  let ψ : ℚ_[l] →+* A := IsLocalization.lift (M := nonZeroDivisors ℤ_[l]) hψ₀
  letI algQA : Algebra ℚ_[l] A := ψ.toAlgebra
  let g₀ : R ⧸ J →+* B := Ideal.Quotient.lift J f.toRingHom (fun a ha => RingHom.mem_ker.1 (hJf ha))
  have hu : IsUnit (g₀ x) := by
    have h1 : g₀ x = algebraMap ℚ_[l] B (l : ℚ_[l]) := by
      simp [g₀, x, map_natCast]
    rw [h1]
    exact (isUnit_iff_ne_zero.2 (Nat.cast_ne_zero.2 hl.out.ne_zero)).map _
  let g : A →+* B := IsLocalization.Away.lift x hu
  have hg : ∀ w, g (algebraMap (R ⧸ J) A w) = g₀ w := fun w => IsLocalization.Away.lift_eq x hu w
  have hgO : ∀ z : O, g (algebraMap O A z) = algebraMap O B z := by
    intro z
    rw [IsScalarTower.algebraMap_apply O (R ⧸ J) A, hg]
    exact f.commutes z
  have hgψ : g.comp ψ = algebraMap ℚ_[l] B := by
    refine IsLocalization.ringHom_ext (nonZeroDivisors ℤ_[l]) ?_
    ext y
    simp only [RingHom.comp_apply, ψ, IsLocalization.lift_eq, ψ₀, hgO]
    rw [← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply]
  let gK : A →ₐ[ℚ_[l]] B := { g with commutes' := fun r => RingHom.congr_fun hgψ r }
  let δ : A := algebraMap (R ⧸ J) A (Ideal.Quotient.mk J d)
  have hδ : ∀ a, δ * a = 0 → a = 0 := by
    intro a ha
    obtain ⟨⟨w, s⟩, rfl⟩ := IsLocalization.mk'_surjective (Submonoid.powers x) a
    change δ * IsLocalization.mk' A w s = 0 at ha
    change IsLocalization.mk' A w s = 0
    have e : δ = IsLocalization.mk' A (Ideal.Quotient.mk J d) (1 : Submonoid.powers x) :=
      (IsLocalization.mk'_one A _).symm
    rw [e, ← IsLocalization.mk'_mul, one_mul, IsLocalization.mk'_eq_zero_iff] at ha
    obtain ⟨c, hc⟩ := ha
    rw [IsLocalization.mk'_eq_zero_iff]
    refine ⟨c, ?_⟩
    obtain ⟨w', rfl⟩ := Ideal.Quotient.mk_surjective w
    obtain ⟨c', hc'⟩ := Ideal.Quotient.mk_surjective (c : R ⧸ J)
    rw [← hc', ← map_mul, ← map_mul, Ideal.Quotient.eq_zero_iff_mem] at hc
    rw [← hc', ← map_mul, Ideal.Quotient.eq_zero_iff_mem]
    apply hdJ
    simpa [mul_comm, mul_left_comm, mul_assoc] using hc
  obtain ⟨I, hloc, hfin, hIker, hI⟩ := core δ hδ gK
  letI algZ : Algebra ℤ_[l] (A ⧸ I) := ((algebraMap ℚ_[l] (A ⧸ I)).comp (algebraMap ℤ_[l] ℚ_[l])).toAlgebra
  have tZO : IsScalarTower ℤ_[l] O (A ⧸ I) := IsScalarTower.of_algebraMap_eq fun y => by
    show Ideal.Quotient.mk I (ψ (algebraMap ℤ_[l] ℚ_[l] y)) = Ideal.Quotient.mk I (algebraMap O A (algebraMap ℤ_[l] O y))
    rw [IsLocalization.lift_eq]
    rfl
  have tZQ : IsScalarTower ℤ_[l] ℚ_[l] (A ⧸ I) := IsScalarTower.of_algebraMap_eq fun _ => rfl
  let f' : R →ₐ[O] A ⧸ I := (Ideal.Quotient.mkₐ O I).comp
    ((IsScalarTower.toAlgHom O (R ⧸ J) A).comp (Ideal.Quotient.mkₐ O J))
  have hf' : ∀ a, f' a = Ideal.Quotient.mk I (algebraMap (R ⧸ J) A (Ideal.Quotient.mk J a)) := fun _ => rfl
  let q : A ⧸ I →ₐ[ℚ_[l]] B := Ideal.Quotient.liftₐ I gK (fun a ha => RingHom.mem_ker.1 (hIker ha))
  have hq : ∀ a, q (Ideal.Quotient.mk I a) = g a := fun _ => rfl
  refine ⟨A ⧸ I, inferInstance, hloc, inferInstance, hfin, inferInstance, algZ, tZO, tZQ, f', q, ?_, ?_, ?_⟩
  · intro a ha
    rw [RingHom.mem_ker, hf', Ideal.Quotient.eq_zero_iff_mem.2 ha, map_zero, map_zero]
  · intro a
    rw [hf', hq, hg]
    rfl
  · intro b hb
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective b
    rw [hf', ← map_mul, Ideal.Quotient.eq_zero_iff_mem] at hb
    rw [hq]
    exact hI a hb

end GlobalTheory.ThickenSaturated
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CrystallineOrdinaryIdeals.ExistsGLConjEqDiagonalOfCharpolyEqProdStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal Module UpperTheory.V.Loc UpperTheory.V.U3 UpperTheory.V.Alg IsLocalRing Polynomial Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.diagonalize_of_distinct_eigenvalues : ∀ {C : Type} [CommRing C] [IsLocalRing C] (A : Matrix (Fin 3) (Fin 3) C) (p : Fin 3 → C), (∀ a b, a ≠ b → IsUnit (p a - p b)) → A.charpoly = ∏ a, (X - Polynomial.C (p a)) → ∃ h : GL (Fin 3) C, (h : Matrix (Fin 3) (Fin 3) C) * A * ((h⁻¹ : GL (Fin 3) C) : Matrix (Fin 3) (Fin 3) C) = Matrix.diagonal p := by
  first | exact @GlobalTheory.exists_GL_conj_eq_diagonal_of_charpoly_eq_prod | exact GlobalTheory.exists_GL_conj_eq_diagonal_of_charpoly_eq_prod | (intros; apply GlobalTheory.exists_GL_conj_eq_diagonal_of_charpoly_eq_prod <;> assumption)
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CrystallineOrdinaryIdeals.ExistsTruncatedPolynomialThickeningFibreSquareStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal Module UpperTheory.V.Loc UpperTheory.V.U3 UpperTheory.V.Alg IsLocalRing Polynomial Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_truncated_polynomial_thickening_fibre_square : ∀ {E B : Type} [Field E] [CommRing B] [Algebra E B] [Module.Finite E B] (π : B →ₐ[E] E), (∀ a, π a = 0 → IsNilpotent a) → ∀ J : ℕ, ∃ (C : Type) (_ : CommRing C) (_ : Algebra E C) (_ : Module.Finite E C) (T : Type) (_ : CommRing T) (_ : Algebra E T) (_ : Module.Finite E T) (πC : C →ₐ[E] E) (p₁ : T →ₐ[E] B) (p₂ : T →ₐ[E] C) (t : C), IsNilpotent t ∧ (∀ a, πC a = 0 → IsNilpotent a) ∧ (∀ a, π (p₁ a) = 0 → IsNilpotent a) ∧ π.comp p₁ = πC.comp p₂ ∧ (∀ b c, π b = πC c → ∃ s, p₁ s = b ∧ p₂ s = c) ∧ ∀ (P y : T) (j : ℕ) (v : Cˣ), j ≤ J → p₂ P = t ^ j * v → P * y = 0 → p₁ y = 0 := by
  intro E B _ _ _ _ π hπ J
  classical
  haveI : IsArtinianRing B := IsArtinianRing.of_finite E B
  obtain ⟨e, he⟩ : IsNilpotent (RingHom.ker (π : B →+* E)) := by
    rw [Ideal.FG.isNilpotent_iff_le_nilradical (IsNoetherian.noetherian _)]
    intro c hc
    exact mem_nilradical.mpr (hπ c (by simpa using hc))
  set I := RingHom.ker (π : B →+* E) with hIdef
  set N := J * e + 1 with hN
  have hN0 : N ≠ 0 := by omega
  haveI : Module.Finite E (AdjoinRoot ((X : E[X]) ^ N)) :=
    (AdjoinRoot.powerBasis' (monic_X_pow N)).finite
  haveI : Module.Finite B (AdjoinRoot ((X : B[X]) ^ N)) :=
    (AdjoinRoot.powerBasis' (monic_X_pow N)).finite
  haveI : Module.Finite E (AdjoinRoot ((X : B[X]) ^ N)) := Module.Finite.trans B _
  have hrootE : (AdjoinRoot.root ((X : E[X]) ^ N)) ^ N = 0 := by
    rw [← AdjoinRoot.mk_X, ← map_pow, AdjoinRoot.mk_self]
  have hrootB : (AdjoinRoot.root ((X : B[X]) ^ N)) ^ N = 0 := by
    rw [← AdjoinRoot.mk_X, ← map_pow, AdjoinRoot.mk_self]
  let πC : AdjoinRoot ((X : E[X]) ^ N) →ₐ[E] E :=
    AdjoinRoot.liftAlgHom _ (AlgHom.id E E) 0 (by simp [hN0])
  let p1 : AdjoinRoot ((X : B[X]) ^ N) →ₐ[E] B :=
    AdjoinRoot.liftAlgHom _ (AlgHom.id E B) 0 (by simp [hN0])
  let p2 : AdjoinRoot ((X : B[X]) ^ N) →ₐ[E] AdjoinRoot ((X : E[X]) ^ N) :=
    AdjoinRoot.liftAlgHom _ ((Algebra.ofId E _).comp π) (AdjoinRoot.root _)
      (by rw [eval₂_X_pow]; exact hrootE)
  have hp1 : ∀ q : B[X], p1 (AdjoinRoot.mk _ q) = q.coeff 0 := by
    intro q
    simp [p1, AdjoinRoot.liftAlgHom_mk, eval₂_at_zero]
  have hp1of : ∀ b : B, p1 (AdjoinRoot.of _ b) = b := fun b =>
    AdjoinRoot.liftAlgHom_of _ _ _ _ _
  have hπC : ∀ q : E[X], πC (AdjoinRoot.mk _ q) = q.coeff 0 := by
    intro q
    simp [πC, AdjoinRoot.liftAlgHom_mk, eval₂_at_zero]
  have hp2 : ∀ q : B[X], p2 (AdjoinRoot.mk _ q) = AdjoinRoot.mk _ (q.map (π : B →+* E)) := by
    intro q
    rw [AdjoinRoot.liftAlgHom_mk, ← AdjoinRoot.aeval_eq, aeval_def, eval₂_map]
    rfl
  have hp2root : p2 (AdjoinRoot.root _) = AdjoinRoot.root _ := AdjoinRoot.liftAlgHom_root _ _ _ _
  have hp2map : ∀ q : E[X], p2 (AdjoinRoot.mk _ (q.map (algebraMap E B))) = AdjoinRoot.mk _ q := by
    intro q
    rw [hp2, Polynomial.map_map]
    congr 1
    conv_rhs => rw [← Polynomial.map_id (p := q)]
    congr 1
    ext r
    simp
  have hnilT : ∀ a, π (p1 a) = 0 → IsNilpotent a := by
    intro a ha
    obtain ⟨q, rfl⟩ := AdjoinRoot.mk_surjective a
    rw [hp1] at ha
    obtain ⟨r, hr⟩ : X ∣ q - C (q.coeff 0) := X_dvd_iff.mpr (by simp)
    have hq : q = C (q.coeff 0) + X * r := by rw [← hr]; ring
    rw [hq, map_add, map_mul, AdjoinRoot.mk_X, AdjoinRoot.mk_C]
    exact Commute.isNilpotent_add (Commute.all _ _) ((hπ _ ha).map _)
      ⟨N, by rw [mul_pow, hrootB, zero_mul]⟩
  have hnilC : ∀ a, πC a = 0 → IsNilpotent a := by
    intro a ha
    obtain ⟨q, rfl⟩ := AdjoinRoot.mk_surjective a
    rw [hπC] at ha
    obtain ⟨r, rfl⟩ := X_dvd_iff.mpr ha
    exact ⟨N, by rw [map_mul, AdjoinRoot.mk_X, mul_pow, hrootE, zero_mul]⟩
  have hcomm : π.comp p1 = πC.comp p2 := by
    refine AlgHom.ext fun a => ?_
    obtain ⟨q, rfl⟩ := AdjoinRoot.mk_surjective a
    simp only [AlgHom.comp_apply, hp1, hp2, hπC, coeff_map]
    rfl
  have hsurj : ∀ b c, π b = πC c → ∃ s, p1 s = b ∧ p2 s = c := by
    intro b c hbc
    obtain ⟨q, rfl⟩ := AdjoinRoot.mk_surjective c
    rw [hπC] at hbc
    refine ⟨AdjoinRoot.of _ b + AdjoinRoot.mk _ (q.map (algebraMap E B)) -
      AdjoinRoot.of _ (algebraMap E B (q.coeff 0)), ?_, ?_⟩
    · rw [map_sub, map_add, ← AdjoinRoot.mk_C, ← AdjoinRoot.mk_C, hp1, hp1, hp1]
      simp
    · rw [map_sub, map_add, hp2map, ← AdjoinRoot.mk_C, ← AdjoinRoot.mk_C, hp2, hp2]
      simp [hbc]
  have hker : ∀ Q, p2 Q = 0 → Q ∈ I.map (AdjoinRoot.of ((X : B[X]) ^ N)) := by
    intro Q hQ
    obtain ⟨q, rfl⟩ := AdjoinRoot.mk_surjective Q
    rw [hp2, AdjoinRoot.mk_eq_zero] at hQ
    have hmod : (q %ₘ (X ^ N)).map (π : B →+* E) = 0 := by
      rw [map_modByMonic _ (monic_X_pow N), Polynomial.map_pow, map_X]
      exact (modByMonic_eq_zero_iff_dvd (monic_X_pow N)).mpr hQ
    have hmk : AdjoinRoot.mk ((X : B[X]) ^ N) q = AdjoinRoot.mk _ (q %ₘ (X ^ N)) := by
      conv_lhs => rw [← modByMonic_add_div q (X ^ N)]
      rw [map_add, map_mul, AdjoinRoot.mk_self, zero_mul, add_zero]
    rw [hmk]
    have hin : q %ₘ (X ^ N) ∈ I.map (C : B →+* B[X]) := by
      rw [Ideal.mem_map_C_iff]
      intro n
      rw [hIdef, RingHom.mem_ker]
      have := congrArg (fun p => p.coeff n) hmod
      simpa using this
    have := Ideal.mem_map_of_mem (AdjoinRoot.mk ((X : B[X]) ^ N)) hin
    rw [Ideal.map_map] at this
    exact this
  refine ⟨AdjoinRoot ((X : E[X]) ^ N), inferInstance, inferInstance, inferInstance,
    AdjoinRoot ((X : B[X]) ^ N), inferInstance, inferInstance, inferInstance, πC, p1, p2,
    AdjoinRoot.root _, ⟨N, hrootE⟩, hnilC, hnilT, hcomm, hsurj, ?_⟩
  intro P y j v hj hP hPy
  obtain ⟨qv, hqv⟩ := AdjoinRoot.mk_surjective (v : AdjoinRoot ((X : E[X]) ^ N))
  set V := AdjoinRoot.mk ((X : B[X]) ^ N) (qv.map (algebraMap E B)) with hVdef
  have hV : p2 V = v := by rw [hVdef, hp2map, hqv]
  have hVu : IsUnit V := by
    have hw : π (p1 V) ≠ 0 := by
      rw [← AlgHom.comp_apply, hcomm, AlgHom.comp_apply, hV]
      exact (v.isUnit.map πC).ne_zero
    have h1 : IsNilpotent (V - AdjoinRoot.of _ (algebraMap E B (π (p1 V)))) := by
      apply hnilT
      rw [map_sub, map_sub, hp1of, AlgHom.commutes]
      simp
    have h2 : IsUnit (AdjoinRoot.of ((X : B[X]) ^ N) (algebraMap E B (π (p1 V)))) :=
      ((Ne.isUnit hw).map (algebraMap E B)).map _
    have := h1.isUnit_add_left_of_commute h2 (Commute.all _ _)
    simpa using this
  obtain ⟨Vi, hVi⟩ : ∃ Vi, V * Vi = 1 := hVu.exists_right_inv
  set Q := P - AdjoinRoot.root ((X : B[X]) ^ N) ^ j * V with hQdef
  have hQ2 : p2 Q = 0 := by
    rw [hQdef, map_sub, map_mul, map_pow, hV, hP, hp2root, sub_self]
  set K := I.map (AdjoinRoot.of ((X : B[X]) ^ N)) with hK
  have hQK : Q ∈ K := hker Q hQ2
  set R := -(Q * Vi) with hR
  have hRK : R ∈ K := K.neg_mem (K.mul_mem_right _ hQK)
  have hxR : AdjoinRoot.root ((X : B[X]) ^ N) ^ j * y = R * y := by
    rw [hR]
    linear_combination (-(AdjoinRoot.root ((X : B[X]) ^ N) ^ j * y)) * hVi + Vi * hPy +
      (Vi * y) * hQdef
  have hpow : ∀ k : ℕ, AdjoinRoot.root ((X : B[X]) ^ N) ^ (j * k) * y = R ^ k * y := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      have hsplit : AdjoinRoot.root ((X : B[X]) ^ N) ^ (j * (k + 1)) =
          AdjoinRoot.root ((X : B[X]) ^ N) ^ (j * k) * AdjoinRoot.root ((X : B[X]) ^ N) ^ j := by
        rw [← pow_add]
        congr 1
      calc AdjoinRoot.root ((X : B[X]) ^ N) ^ (j * (k + 1)) * y
          = AdjoinRoot.root ((X : B[X]) ^ N) ^ (j * k) *
              (AdjoinRoot.root ((X : B[X]) ^ N) ^ j * y) := by
            rw [hsplit, mul_assoc]
        _ = R * (AdjoinRoot.root ((X : B[X]) ^ N) ^ (j * k) * y) := by rw [hxR]; ring
        _ = R ^ (k + 1) * y := by rw [ih]; ring
  have hRe : R ^ e = 0 := by
    have h3 : R ^ e ∈ K ^ e := Ideal.pow_mem_pow hRK e
    rw [hK, ← Ideal.map_pow, he, Ideal.zero_eq_bot, Ideal.map_bot] at h3
    exact (Ideal.mem_bot).1 h3
  have hy0 : AdjoinRoot.root ((X : B[X]) ^ N) ^ (j * e) * y = 0 := by
    rw [hpow, hRe, zero_mul]
  have hlt : j * e < N := by
    have := Nat.mul_le_mul_right e hj
    omega
  obtain ⟨qy, rfl⟩ := AdjoinRoot.mk_surjective y
  rw [hp1]
  rw [← AdjoinRoot.mk_X, ← map_pow, ← map_mul, AdjoinRoot.mk_eq_zero] at hy0
  obtain ⟨s, hs⟩ := hy0
  have h4 := congrArg (fun p => p.coeff (j * e)) hs
  simp only [coeff_X_pow_mul'] at h4
  simpa [Nat.not_le.mpr hlt] using h4
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CrystallineOrdinaryIdeals.GaloisSubgroupLBasicProperties
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal Module UpperTheory.V.Loc UpperTheory.V.U3 UpperTheory.V.Alg IsLocalRing Polynomial Topology

namespace GlobalTheory.OrdLoc

theorem hl_basic : ∀ {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsLocalRing O] [Algebra ℤ_[l] O] (D : Dat3 l O), D.HL.Normal ∧ IsOpen (D.HL : Set (GQ l)) ∧ IsOpenEmbedding D.HL.subtype ∧ (∀ s ∈ D.HL, s ∈ Iq l → D.Ψ s = cycA l l O s ^ D.e) ∧ GlobalTheory.OrdLoc.IsInertiaInfiniteCyclotomic D (GlobalTheory.OrdLoc.s0 D) := by
  intro l _ O _ _ _ D
  have hη : IsOpen (D.η.ker : Set (GQ l)) := by
    have : D.η.ker = GK D.Kv := Subgroup.ext fun g => D.η_ker g
    rw [this]
    haveI := D.Kv.2
    exact IntermediateField.fixingSubgroup_isOpen D.Kv.1
  have ho : IsOpen (D.HL : Set (GQ l)) := hη.inter D.τ_open
  have hex : ∃ s, IsInertiaInfiniteCyclotomic D s := by
    obtain ⟨s, ⟨hs1, hs2⟩, hs⟩ := ((cycInertia l).2 D.HL ho).2
    exact ⟨s, hs1, hs2, hs⟩
  refine ⟨inferInstanceAs (D.η.ker ⊓ D.τ.ker).Normal, ho, ho.isOpenEmbedding_subtypeVal, fun s hs hi => ?_,
    Classical.epsilon_spec hex⟩
  have ht : D.τ s = 1 := hs.2
  rw [D.Ψ_I s hi, ht, mul_one]

end GlobalTheory.OrdLoc
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CrystallineOrdinaryIdeals.NilpotentTwistStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal Module UpperTheory.V.Loc UpperTheory.V.U3 UpperTheory.V.Alg IsLocalRing Polynomial Topology
private theorem sh_s0_eq_diagonal_psi_sub_psi {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsLocalRing O] [Algebra ℤ_[l] O] (D : Dat3 l O) {C : Type} [CommRing C] [Algebra O C] (r : GQ l →* GG 3 C) (h : (r D.s0).mat = Matrix.diagonal (fun a => algebraMap O C (UpperTheory.V.UnitaryThreeInertia.psi D.Ψ a D.s0))) (b : Fin 3) : D.sh r b D.s0 = Matrix.diagonal (fun c => algebraMap O C (UpperTheory.V.UnitaryThreeInertia.psi D.Ψ c D.s0) - algebraMap O C (UpperTheory.V.UnitaryThreeInertia.psi D.Ψ b D.s0)) := by
  rw [Dat3.sh, h, Matrix.scalar_apply, Matrix.diagonal_sub]
private theorem tr_lemma_2 {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsLocalRing O] [Algebra ℤ_[l] O] (D : Dat3 l O) {C : Type} [CommRing C] [Algebra O C] (r : GQ l →* GG 3 C) (h : (r D.s0).mat = Matrix.diagonal (fun a => algebraMap O C (UpperTheory.V.UnitaryThreeInertia.psi D.Ψ a D.s0))) (a : Fin 3) : D.tr r a = algebraMap O C (D.cc a) * (r D.fr).mat a a := by
  rw [Dat3.tr, sh_s0_eq_diagonal_psi_sub_psi D r h, sh_s0_eq_diagonal_psi_sub_psi D r h, Matrix.diagonal_mul_diagonal, Matrix.trace, Fin.sum_univ_three]
  simp only [Matrix.diag, Matrix.diagonal_mul, Dat3.cc, map_mul, map_sub]
  fin_cases a <;> simp <;> ring

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ordinary_derivative_entry_formula : ∀ {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsLocalRing O] [Algebra ℤ_[l] O] (D : Dat3 l O) {C : Type} [CommRing C] [Algebra O C] (r : GQ l →* GG 3 C), (r (GlobalTheory.OrdLoc.s0 D)).mat = Matrix.diagonal (fun a => algebraMap O C (UpperTheory.V.UnitaryThreeInertia.psi D.Ψ a (GlobalTheory.OrdLoc.s0 D))) → ∀ a : Fin 3, GlobalTheory.OrdLoc.dd D r a = algebraMap O C (GlobalTheory.OrdLoc.cc D a * GlobalTheory.OrdLoc.cc D (a + 1)) * ((r (GlobalTheory.OrdLoc.fr D)).mat a a - algebraMap O C ((cycA l l O (GlobalTheory.OrdLoc.fr D) : Oˣ) : O) * (r (GlobalTheory.OrdLoc.fr D)).mat (a + 1) (a + 1)) := by
  intro l _ O _ _ _ D C _ _ r h a
  simp only [Dat3.dd, tr_lemma_2 D r h, map_mul]
  ring
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CrystallineOrdinaryIdeals.SaturatingElementNotMemMinimalPrimesReducedOrdin
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal Module UpperTheory.V.Loc UpperTheory.V.U3 UpperTheory.V.Alg IsLocalRing Polynomial Topology

namespace GlobalTheory.OrdLoc

theorem mem_IY_of_del_mul_mem {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsLocalRing O]
    [Algebra ℤ_[l] O] (D : Dat3 l O) (U : D.Univ) {a : U.R}
    (h : del D U.r.hom * a ∈ IY D U) : a ∈ IY D U := by
  obtain ⟨n, hn⟩ := h
  exact ⟨n + 1, by rw [pow_succ, mul_assoc]; exact hn⟩

theorem del_notMem_of_mem_minimalPrimes_Icr : ∀ {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsLocalRing O]
    [Algebra ℤ_[l] O] (D : Dat3 l O) (U : D.Univ), ∀ P ∈ (GlobalTheory.OrdLoc.Icr D U).minimalPrimes,
    GlobalTheory.OrdLoc.del D U.r.hom ∉ P := by
  intro l _ O _ _ _ D U P hP hd
  rw [Icr, Ideal.radical_minimalPrimes] at hP
  obtain ⟨y, hy, hxy⟩ := Ideal.exists_mul_mem_of_mem_minimalPrimes hP hd
  exact hy (mem_IY_of_del_mul_mem D U hxy)

end GlobalTheory.OrdLoc

example : ∀ {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsLocalRing O] [Algebra ℤ_[l] O] (D : Dat3 l O) (U : D.Univ), ∀ P ∈ (GlobalTheory.OrdLoc.Icr D U).minimalPrimes, GlobalTheory.OrdLoc.del D U.r.hom ∉ P := GlobalTheory.OrdLoc.del_notMem_of_mem_minimalPrimes_Icr
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CrystallineOrdinaryIdeals.SpanCharacterSubCyclotomicEqOfPositiveWeightStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal Module UpperTheory.V.Loc UpperTheory.V.U3 UpperTheory.V.Alg IsLocalRing Polynomial Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.span_character_sub_cyclotomic_eq_of_positive_weight : ∀ {l : ℕ} [Fact l.Prime] {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (φ : G →* GQ l) (hφ : IsOpenEmbedding φ) {E : Type} [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] [Algebra ℤ_[l] E] [IsScalarTower ℤ_[l] ℚ_[l] E] {B : Type} [CommRing B] [Algebra ℚ_[l] B] [Module.Finite ℚ_[l] B] [TopologicalSpace B] [IsModuleTopology ℚ_[l] B] [IsTopologicalRing B] [Algebra ℤ_[l] B] [IsScalarTower ℤ_[l] ℚ_[l] B] [Algebra E B] [IsScalarTower ℚ_[l] E B] (π : B →ₐ[E] E) (hπ : ∀ a, π a = 0 → IsNilpotent a) (χ : G →* Bˣ), Continuous (fun g => (χ g : B)) → ∀ w : ℤ, 1 ≤ w → (∀ g, φ g ∈ Iq l → χ g = cycA l l B (φ g) ^ w) → ∀ σ : G, ((Iq l).comap φ ⊔ Subgroup.zpowers σ).topologicalClosure = ⊤ → Ideal.span (Set.range fun g => (χ g : B) - (cycA l l B (φ g) : B)) = (if w = 1 then Ideal.span {(χ σ : B) - (cycA l l B (φ σ) : B)} else ⊤) := by
  first | exact @GlobalTheory.CharCycIdeal.span_range_sub_cyc | exact GlobalTheory.CharCycIdeal.span_range_sub_cyc | (intros; apply GlobalTheory.CharCycIdeal.span_range_sub_cyc <;> assumption)
end

