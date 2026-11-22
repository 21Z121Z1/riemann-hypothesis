import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.Bundle0008
import Development.AutomorphicArithmetic.AutomorphicVarieties.PublishedTheorems.KisinCrTrivial
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.Bundle0039
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.DimZ1fCrystallineDeformation
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.Bundle0015
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.Bundle0002
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.Bundle0001
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.Bundle0001
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.Bundle0038

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.ChartCount
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal Module UpperTheory.V.Loc UpperTheory.V.U3 UpperTheory.V.Alg UpperTheory.V.Published IsLocalRing Polynomial

private noncomputable def jet {σ E : Type} [Field E] (i : σ) : MvPowerSeries σ E →ₐ[E] DualNumber E where
  toFun f := ⟨MvPowerSeries.constantCoeff f, MvPowerSeries.coeff (Finsupp.single i 1) f⟩
  map_one' := by
    classical
    ext
    · simp
    · simp [MvPowerSeries.coeff_one]
  map_mul' f g := by
    classical
    refine TrivSqZeroExt.ext (map_mul MvPowerSeries.constantCoeff f g) ?_
    refine Eq.trans ?_ (DualNumber.snd_mul _ _).symm
    show MvPowerSeries.coeff (Finsupp.single i 1) (f * g) =
      MvPowerSeries.constantCoeff f * MvPowerSeries.coeff (Finsupp.single i 1) g +
        MvPowerSeries.coeff (Finsupp.single i 1) f * MvPowerSeries.constantCoeff g
    simp [MvPowerSeries.coeff_mul, Finsupp.antidiagonal_single, Finset.Nat.antidiagonal_succ, mul_comm]
  map_zero' := by ext <;> simp
  map_add' f g := TrivSqZeroExt.ext (map_add MvPowerSeries.constantCoeff f g) (map_add (MvPowerSeries.coeff _) f g)
  commutes' c := by
    classical
    ext <;> simp [MvPowerSeries.algebraMap_apply, MvPowerSeries.coeff_C, TrivSqZeroExt.algebraMap_eq_inl]

private theorem snd_mul_left {E : Type} [CommRing E] (A : Matrix (Fin 3) (Fin 3) E)
    (X : Matrix (Fin 3) (Fin 3) (DualNumber E)) :
    (A.map (algebraMap E (DualNumber E)) * X).map TrivSqZeroExt.snd = A * X.map TrivSqZeroExt.snd := by
  ext a b
  simp [Matrix.mul_apply, TrivSqZeroExt.algebraMap_eq_inl, TrivSqZeroExt.snd_sum]

private theorem snd_mul_right {E : Type} [CommRing E] (A : Matrix (Fin 3) (Fin 3) E)
    (X : Matrix (Fin 3) (Fin 3) (DualNumber E)) :
    (X * A.map (algebraMap E (DualNumber E))).map TrivSqZeroExt.snd = X.map TrivSqZeroExt.snd * A := by
  ext a b
  simp [Matrix.mul_apply, TrivSqZeroExt.algebraMap_eq_inl, TrivSqZeroExt.snd_sum, mul_comm]

private theorem exists_coc {G E : Type} [Group G] [CommRing E] (r : G →* GG 3 E) (r' : G →* GG 3 (DualNumber E))
    (h1 : ∀ g, (r' g).right = (r g).right) (h2 : ∀ g a b, ((r' g).mat a b).fst = (r g).mat a b) :
    ∃ γ, IsCoc r γ ∧ DualDef r γ r' := by
  obtain ⟨γ, -, hc, hd⟩ := exists_isCoc (RingHom.ker (TrivSqZeroExt.fstHom E E E))
    ((GG.map (algebraMap E (DualNumber E))).comp r) r' (by
      rw [eq_bot_iff, Ideal.mul_le]
      intro x hx y hy
      have hx' : x.fst = 0 := hx
      have hy' : y.fst = 0 := hy
      rw [Ideal.mem_bot]
      ext <;> simp [hx', hy']) (MonoidHom.ext fun g => SemidirectProduct.ext (Units.ext (Matrix.ext fun a b => by
      refine Ideal.Quotient.eq.2 ?_
      show ((r' g).mat a b - algebraMap E (DualNumber E) ((r g).mat a b)).fst = 0
      simp [h2, TrivSqZeroExt.algebraMap_eq_inl])) (h1 g))
  refine ⟨fun g => (γ g).map TrivSqZeroExt.snd, fun g h => ?_, fun g => ⟨h1 g, fun a b => ?_⟩⟩
  · have e : adRep ((GG.map (algebraMap E (DualNumber E))).comp r) g (γ h) =
        (r g).mat.map (algebraMap E (DualNumber E)) * (if (r g).right = 1 then γ h else thetaLie (γ h)) *
          (((r g).left⁻¹ : GL (Fin 3) E) : Matrix (Fin 3) (Fin 3) E).map (algebraMap E (DualNumber E)) := rfl
    have e' : ∀ X, adRep r g X = (r g).mat * (if (r g).right = 1 then X else thetaLie X) *
          (((r g).left⁻¹ : GL (Fin 3) E) : Matrix (Fin 3) (Fin 3) E) := fun X => rfl
    show (γ (g * h)).map _ = _
    rw [hc g h, Matrix.map_add _ TrivSqZeroExt.snd_add, e, e', snd_mul_right, snd_mul_left]
    split_ifs
    · rfl
    · unfold thetaLie
      rw [Matrix.map_neg _ TrivSqZeroExt.snd_neg, ← Jmat_map (algebraMap E (DualNumber E)), snd_mul_right, snd_mul_left]
      rfl
  · refine TrivSqZeroExt.ext (h2 g a b) ?_
    have e : (r' g).mat = (1 + γ g) * (r g).mat.map (algebraMap E (DualNumber E)) := (hd g).2
    have e2 := congrArg (fun X : Matrix (Fin 3) (Fin 3) (DualNumber E) => X.map TrivSqZeroExt.snd a b) e
    simp only [snd_mul_right] at e2
    refine e2.trans ?_
    show _ = ((γ g).map TrivSqZeroExt.snd * (r g).mat) a b
    refine congrArg (fun X : Matrix (Fin 3) (Fin 3) E => (X * (r g).mat) a b) ?_
    ext c d
    simp only [Matrix.map_apply, Matrix.add_apply, Matrix.one_apply]
    split_ifs <;> simp

theorem UpperTheory.V.Loc.chartCount :
    LocalPublishedTheorems → ∀ {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O] [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O] [IsAdicComplete (maximalIdeal O) O] (D : Dat3 l O) (U : D.Univ) (E : Type) [Field E] [Algebra ℚ_[l] E] [Module.Finite ℚ_[l] E] [Algebra O E] [Algebra ℤ_[l] E] [IsScalarTower ℤ_[l] O E] [IsScalarTower ℤ_[l] ℚ_[l] E] [IsFractionRing O E] (x : U.R →ₐ[O] O), IsBase D.η D.Ψ U.r.hom x → ∀ (n : ℕ) (w : Fin n → ℤ) (φ : U.R →ₐ[O] MvPowerSeries (Fin n) E) (u : Fin n → GQ l × Fin 3 × Fin 3), UpperTheory.V.Loc.IsCompl (D.It U) x φ → (∀ g a b, φ ((U.r.hom g).mat a b) ∈ wtPart E w (wt a b)) → (∀ i j, MvPowerSeries.coeff (Finsupp.single j 1) (φ ((U.r.hom (u i).1).mat (u i).2.1 (u i).2.2)) = if i = j then 1 else 0) → ∀ j, Nat.card {i // w i = j} ≤ locDims j := by
  intro hP l _ O _ _ _ _ _ _ _ D U E _ _ _ _ _ _ _ _ x hx n w φ u hφ hg hu j
  letI : TopologicalSpace E := moduleTopology ℚ_[l] E
  haveI : IsModuleTopology ℚ_[l] E := ⟨rfl⟩
  haveI : IsTopologicalRing E := IsModuleTopology.isTopologicalRing ℚ_[l] E
  have hxe : ∀ g a b, algebraMap O E (x ((U.r.hom g).mat a b)) = (D.rz E g).mat a b := fun g a b =>
    congrArg (fun r : GQ l →* GG 3 O => algebraMap O E ((r g).mat a b)) hx
  let d : GQ l → Fin 3 → E := fun g b => algebraMap O E ((D.Ψ g ^ wt1 b : Oˣ) : O)
  have hd : ∀ g, (D.rz E g).mat = Matrix.diagonal (d g) := fun g =>
    Matrix.diagonal_map (map_zero (algebraMap O E))
  have hdd : ∀ g b, d g b * d g⁻¹ b = 1 := fun g b => by
    simp only [d]
    rw [← map_mul, ← Units.val_mul, ← mul_zpow, ← map_mul]
    simp
  have hdc : ∀ b, Continuous fun g => d g b := fun b => by
    have := (ptCont (l := l) U.R E ((Algebra.ofId O E).comp x)).1 _ _ (U.r.cont b b)
    refine Continuous.congr this fun g => (hxe g b b).trans ?_
    rw [hd, Matrix.diagonal_apply_eq]
  have key : ∀ i, ∃ γ ∈ finiteCocycles (MonoidHom.id _) (adRep (D.rz E)), ∀ g a b,
      γ g a b = MvPowerSeries.coeff (Finsupp.single i 1) (φ ((U.r.hom g).mat a b)) * d g⁻¹ b := fun i => by
    let F : U.R →ₐ[O] DualNumber E := ((jet i).restrictScalars O).comp φ
    obtain ⟨γ, hc, hγ⟩ := exists_coc (D.rz E) (push F U.r.hom) (fun g => U.r.hasMult g)
      (fun g a b => (hφ.const _).trans (hxe g a b))
    have he : ∀ g a b, γ g a b = (F ((U.r.hom g).mat a b)).snd * d g⁻¹ b := fun g a b => by
      have : (F ((U.r.hom g).mat a b)).snd = (γ g * (D.rz E g).mat) a b :=
        congrArg TrivSqZeroExt.snd ((hγ g).2 a b)
      rw [this, hd, Matrix.mul_diagonal, mul_assoc, hdd, mul_one]
    refine ⟨γ, (rtTangent hP D U E γ ⟨?_, hc⟩ _ hγ).1 ⟨F, rfl, fun y hy => ?_⟩, he⟩
    · refine continuous_pi fun a => continuous_pi fun b => ?_
      simp only [he]
      refine Continuous.mul ?_ ((hdc b).comp continuous_inv)
      haveI : Module.Finite ℚ_[l] (DualNumber E) := inferInstanceAs (Module.Finite ℚ_[l] (E × E))
      have hq := (ptCont (l := l) U.R (DualNumber E) F).1 _ _ (U.r.cont a b)
      letI : TopologicalSpace (DualNumber E) := moduleTopology ℚ_[l] _
      haveI : IsModuleTopology ℚ_[l] (DualNumber E) := ⟨rfl⟩
      exact (IsModuleTopology.continuous_of_linearMap
        ((TrivSqZeroExt.sndHom E E).restrictScalars ℚ_[l])).comp hq
    · rw [← hφ.ker, RingHom.mem_ker] at hy
      show jet i (φ y) = 0
      rw [hy, map_zero]
  choose γ hγ he using key
  obtain ⟨hfin, hdim, -⟩ := dim_Z1f_crystalline_deformation hP D E j
  haveI : Module.Finite E ↥(finiteCocycles (MonoidHom.id _) (adRep (D.rz E)) ⊓ Submodule.pi Set.univ fun _ => gw E j) :=
    Module.Finite.of_injective (Submodule.inclusion inf_le_left) (Submodule.inclusion_injective _)
  let v : {i // w i = j} → ↥(finiteCocycles (MonoidHom.id _) (adRep (D.rz E)) ⊓ Submodule.pi Set.univ fun _ => gw E j) :=
    fun i => ⟨γ i, hγ i, fun g _ a b hab => by
      rw [he, hg g a b _ (by
        rw [Finsupp.weight_single, one_smul, i.2]
        exact hab.symm), zero_mul]⟩
  have hv : LinearIndependent E v := by
    rw [Fintype.linearIndependent_iff]
    intro c hc k
    have h1 := congrArg (fun y : ↥(finiteCocycles (MonoidHom.id _) (adRep (D.rz E)) ⊓ Submodule.pi Set.univ fun _ => gw E j) =>
      y.1 (u k).1 (u k).2.1 (u k).2.2 * d (u k).1 (u k).2.2) hc
    simp only [v, Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, Matrix.sum_apply, Pi.smul_apply,
      Matrix.smul_apply, he, hu, smul_eq_mul, Subtype.val_inj] at h1
    simpa [mul_assoc, mul_comm (d (u k).1⁻¹ _), hdd] using h1
  rw [← hdim, Nat.card_eq_fintype_card]
  exact hv.fintype_card_le_finrank
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.TorAut
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal Module UpperTheory.V.Loc UpperTheory.V.U3 UpperTheory.V.Alg UpperTheory.V.Published IsLocalRing Polynomial

private theorem gg_ext {A : Type} [CommRing A] {x y : GG 3 A} (h : ∀ a b, x.mat a b = y.mat a b)
    (h' : x.right = y.right) : x = y :=
  SemidirectProduct.ext (Units.ext (Matrix.ext h)) h'

private theorem exists_unit {l : ℕ} [Fact l.Prime] (O : Type) [CommRing O] [IsLocalRing O] [CharZero O]
    [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O] :
    ∃ t : Oˣ, (t : O) - 1 ∈ maximalIdeal O ∧ Function.Injective fun j : ℤ => t ^ j := by
  have h1 : (maximalIdeal O).comap (algebraMap ℤ_[l] O) = maximalIdeal ℤ_[l] :=
    eq_maximalIdeal (Ideal.isMaximal_comap_of_isIntegral_of_isMaximal (maximalIdeal O))
  have h2 : (l : O) ∈ maximalIdeal O := by
    have : (l : ℤ_[l]) ∈ maximalIdeal ℤ_[l] := by
      rw [PadicInt.maximalIdeal_eq_span_p]; exact Ideal.mem_span_singleton_self _
    rw [← h1, Ideal.mem_comap, map_natCast] at this
    exact this
  have h3 : IsUnit (1 - (-(l : O))) := isUnit_one_sub_self_of_mem_nonunits _ (neg_mem h2)
  obtain ⟨t, ht⟩ := h3
  refine ⟨t, by simpa [ht] using h2, injective_zpow_iff_not_isOfFinOrder.2 fun h => ?_⟩
  obtain ⟨n, hn, e⟩ := isOfFinOrder_iff_pow_eq_one.1 h
  have e1 : (((1 + l) ^ n : ℕ) : O) = ((1 : ℕ) : O) := by
    have := congrArg Units.val e
    rw [Units.val_pow_eq_pow_val, ht] at this
    simpa using this
  have e2 := Nat.cast_injective e1
  have := (Fact.out : l.Prime).pos
  have e3 : 1 < (1 + l) ^ n := Nat.one_lt_pow hn.ne' (by omega)
  omega

theorem UpperTheory.V.Loc.torAut :
    LocalPublishedTheorems → ∀ {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O] [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O] [IsAdicComplete (maximalIdeal O) O] (D : Dat3 l O) (U : D.Univ) (x : U.R →ₐ[O] O), IsBase D.η D.Ψ U.r.hom x → ∃ (t : Oˣ) (θ : U.R →ₐ[O] U.R), (Function.Injective fun j : ℤ => t ^ j) ∧ x.comp θ = x ∧ (∀ a ∈ D.It U, θ a ∈ D.It U) ∧ ∀ g a b, θ ((U.r.hom g).mat a b) = algebraMap O U.R ((t ^ wt a b : Oˣ) : O) * (U.r.hom g).mat a b := by
  intro hP l _ O _ _ _ _ _ _ _ D U x hx
  obtain ⟨t, ht1, ht⟩ := exists_unit (l := l) O
  have hres : ∀ (C : Type) [CommRing C] [Algebra O C] [IsCO O C] (j : ℤ),
      res O C (algebraMap O C ((t ^ j : Oˣ) : O)) = 1 := fun C _ _ _ j => by
    have e : Units.map (algebraMap O (ResidueField O) : O →* ResidueField O) t = 1 := by
      apply Units.ext
      have := (residue_eq_zero_iff _).2 ht1
      rw [map_sub, map_one, sub_eq_zero] at this
      exact this
    have e2 := congrArg Units.val (map_zpow (Units.map (algebraMap O (ResidueField O) : O →* ResidueField O)) t j)
    rw [e, one_zpow] at e2
    rw [AlgHom.commutes]
    exact e2
  have hmat : ∀ (C : Type) [CommRing C] [Algebra O C] (r : GQ l →* GG 3 C) g a b,
      (conjBy (tor C (Units.map (algebraMap O C : O →* C) t)) r g).mat a b =
        algebraMap O C ((t ^ wt a b : Oˣ) : O) * (r g).mat a b := fun C _ _ r g a b => by
    rw [(conjBy_tor r _).1, ← map_zpow]
    rfl
  let r' : GLift O D.η D.Ψ U.R :=
    { hom := conjBy (tor U.R (Units.map (algebraMap O U.R : O →* U.R) t)) U.r.hom
      cont := fun a b N => by
        simp only [hmat, map_mul]
        exact (IsLocallyConstant.const _).mul (U.r.cont a b N)
      red := fun g => by
        rw [← U.r.red g]
        refine gg_ext (fun a b => ?_) ((conjBy_tor _ _).2.1 g)
        show res O U.R (GG.mat _ a b) = res O U.R (GG.mat _ a b)
        rw [hmat, map_mul, hres, one_mul] }
  obtain ⟨θ, hθ, -⟩ := (U.rep U.R).2 r' trivial
  have hθm : ∀ g a b, θ ((U.r.hom g).mat a b) =
      algebraMap O U.R ((t ^ wt a b : Oˣ) : O) * (U.r.hom g).mat a b := fun g a b =>
    (congrArg (fun r : GLift O D.η D.Ψ U.R => (r.hom g).mat a b) hθ).trans (hmat _ _ g a b)
  have uniq : ∀ (C : Type) [CommRing C] [Algebra O C] [IsCO O C] (f f' : U.R →ₐ[O] C),
      (∀ g a b, f ((U.r.hom g).mat a b) = f' ((U.r.hom g).mat a b)) → f = f' := fun C _ _ _ f f' h => by
    obtain ⟨F, -, hF⟩ := (U.rep C).2 (U.r.map f') trivial
    refine (hF f ?_).trans (hF f' rfl).symm
    exact GLift.ext (MonoidHom.ext fun g => gg_ext (h g) rfl)
  have hxe : ∀ g a b, x ((U.r.hom g).mat a b) = (r0 D.η D.Ψ g).mat a b := fun g a b =>
    congrArg (fun r : GQ l →* GG 3 O => (r g).mat a b) hx
  refine ⟨t, θ, ht, uniq O _ _ fun g a b => ?_, fun y hy => ?_, hθm⟩
  · rw [AlgHom.comp_apply, hθm, map_mul, AlgHom.commutes]
    by_cases hab : a = b
    · simp [hab, wt]
    · rw [hxe, GG.mat, unitaryThreeReflection_left, tor_val, Matrix.diagonal_apply_ne _ hab, mul_zero]
  · by_cases hI : D.It U = ⊤
    · rw [hI]; trivial
    haveI : Nontrivial (U.R ⧸ D.It U) := Ideal.Quotient.nontrivial_iff.2 hI
    haveI : IsCO O (U.R ⧸ D.It U) := co_quot O U.R _ (Ideal.Quotient.mkₐ O _) (Ideal.Quotient.mkₐ_surjective O _)
    obtain ⟨f, hf, hfI⟩ := rtConj hP D U (U.R ⧸ D.It U) (push (Ideal.Quotient.mkₐ O _) U.r.hom)
      (tor _ (Units.map (algebraMap O (U.R ⧸ D.It U) : O →* _) t)) (fun a b => by
        rw [← res_eq_zero_iff O, Matrix.sub_apply, tor_val]
        by_cases hab : a = b
        · subst hab
          rw [Matrix.diagonal_apply_eq, Matrix.one_apply_eq, map_sub, map_one, ← map_zpow]
          exact sub_eq_zero.2 (hres _ _)
        · rw [Matrix.diagonal_apply_ne _ hab, Matrix.one_apply_ne hab, sub_zero, map_zero])
      ⟨_, rfl, fun a ha => Ideal.Quotient.eq_zero_iff_mem.2 ha⟩
    have e : f = (Ideal.Quotient.mkₐ O _).comp θ := uniq _ _ _ fun g a b => by
      rw [AlgHom.comp_apply, hθm, map_mul, AlgHom.commutes]
      exact (congrArg (fun r : GQ l →* GG 3 (U.R ⧸ D.It U) => (r g).mat a b) hf).trans (hmat _ _ g a b)
    have := hfI hy
    rw [e] at this
    exact Ideal.Quotient.eq_zero_iff_mem.1 this
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.ValuationRingClearLastRowEntry
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal Module UpperTheory.V.Loc UpperTheory.V.U3 UpperTheory.V.Alg UpperTheory.V.Published IsLocalRing Polynomial

namespace UpperTheory.V.Loc

private def TriangularForm {ι A C : Type} [CommRing A] [CommRing C] (M : ι → Matrix (Fin 3) (Fin 3) A) (d : ι → Fin 3 → A)
    (S T : Set ι) (φ : A →+* C) (h : GL (Fin 3) C) : Prop :=
  (∀ g ∈ S, ∀ a b, b < a →
    (((h⁻¹ : GL (Fin 3) C) : Matrix (Fin 3) (Fin 3) C) * (M g).map φ * (h : Matrix (Fin 3) (Fin 3) C)) a b = 0) ∧
  ∀ g ∈ T, ∀ a,
    (((h⁻¹ : GL (Fin 3) C) : Matrix (Fin 3) (Fin 3) C) * (M g).map φ * (h : Matrix (Fin 3) (Fin 3) C)) a a = φ (d g a)

section

variable {ι A C C' : Type} [CommRing A] [CommRing C] [CommRing C'] {M : ι → Matrix (Fin 3) (Fin 3) A}
  {d : ι → Fin 3 → A} {S T : Set ι}

private theorem conjugate_entry_map (X : Matrix (Fin 3) (Fin 3) A) (φ : A →+* C) (ψ : C →+* C') (h : GL (Fin 3) C) (a b : Fin 3) :
    ((((Matrix.GeneralLinearGroup.map ψ h)⁻¹ : GL (Fin 3) C') : Matrix (Fin 3) (Fin 3) C') * X.map (ψ.comp φ) *
      (Matrix.GeneralLinearGroup.map ψ h : Matrix (Fin 3) (Fin 3) C')) a b =
    ψ ((((h⁻¹ : GL (Fin 3) C) : Matrix (Fin 3) (Fin 3) C) * X.map φ * (h : Matrix (Fin 3) (Fin 3) C)) a b) := by
  rw [← map_inv, ← Matrix.map_apply (f := ψ), Matrix.map_mul, Matrix.map_mul]
  rfl

private theorem triangular_form_map {φ : A →+* C} {h : GL (Fin 3) C} (ψ : C →+* C') (H : TriangularForm M d S T φ h) :
    TriangularForm M d S T (ψ.comp φ) (Matrix.GeneralLinearGroup.map ψ h) :=
  ⟨fun g hg a b hab => by rw [conjugate_entry_map, H.1 g hg a b hab, map_zero],
    fun g hg a => by rw [conjugate_entry_map, H.2 g hg a]; rfl⟩

private theorem triangular_form_of_injective_map {φ : A →+* C} {h : GL (Fin 3) C} (ψ : C →+* C') (hψ : Function.Injective ψ)
    (H : TriangularForm M d S T (ψ.comp φ) (Matrix.GeneralLinearGroup.map ψ h)) : TriangularForm M d S T φ h :=
  ⟨fun g hg a b hab => hψ (by rw [← conjugate_entry_map, H.1 g hg a b hab, map_zero]),
    fun g hg a => hψ (by rw [← conjugate_entry_map, H.2 g hg a]; rfl)⟩

private theorem triangular_mul_diag {X Y : Matrix (Fin 3) (Fin 3) C} (hX : X.BlockTriangular id) (hY : Y.BlockTriangular id)
    (a : Fin 3) : (X * Y) a a = X a a * Y a a := by
  rw [Matrix.mul_apply, Finset.sum_eq_single a]
  · intro b _ hb
    rcases lt_or_gt_of_ne hb with h | h
    · rw [hX h, zero_mul]
    · rw [hY h, mul_zero]
  · simp

private theorem triangular_form_borel_change {φ : A →+* C} {h : GL (Fin 3) C} (hT : T ⊆ S) (H : TriangularForm M d S T φ h) (k : GL (Fin 3) C)
    (hk : ((k * h : GL (Fin 3) C) : Matrix (Fin 3) (Fin 3) C).BlockTriangular id) : TriangularForm M d S T φ k⁻¹ := by
  obtain ⟨b, hb⟩ : ∃ b, b = k * h := ⟨_, rfl⟩
  rw [← hb] at hk
  obtain rfl : k = b * h⁻¹ := by rw [hb, mul_inv_cancel_right]
  have hi : ((b⁻¹ : GL (Fin 3) C) : Matrix (Fin 3) (Fin 3) C).BlockTriangular id := by
    rw [Matrix.coe_units_inv]
    haveI := b.invertible
    exact Matrix.blockTriangular_inv_of_blockTriangular hk
  have e : ∀ X : Matrix (Fin 3) (Fin 3) C, (((b * h⁻¹)⁻¹⁻¹ : GL (Fin 3) C) : Matrix (Fin 3) (Fin 3) C) * X *
      ((b * h⁻¹)⁻¹ : GL (Fin 3) C) = b * (((h⁻¹ : GL (Fin 3) C) : Matrix (Fin 3) (Fin 3) C) * X * h) *
      (b⁻¹ : GL (Fin 3) C) := fun X => by
    simp only [inv_inv, _root_.mul_inv_rev, Units.val_mul, Matrix.mul_assoc]
  have hU : ∀ g ∈ S, (((h⁻¹ : GL (Fin 3) C) : Matrix (Fin 3) (Fin 3) C) * (M g).map φ * h).BlockTriangular id :=
    fun g hg a b hab => H.1 g hg a b hab
  refine ⟨fun g hg a c hac => ?_, fun g hg a => ?_⟩
  · rw [e]
    exact ((hk.mul (hU g hg)).mul hi) hac
  · rw [e, triangular_mul_diag (hk.mul (hU g (hT hg))) hi, triangular_mul_diag hk (hU g (hT hg)), H.2 g hg a, mul_right_comm,
      ← triangular_mul_diag hk hi, Units.mul_inv, Matrix.one_apply_eq, one_mul]

end

private theorem exists_sl2_valuation_kill {F : Type} [Field F] (V : ValuationSubring F) (a b : F) :
    ∃ x y z w : V, x * w - y * z = 1 ∧ (z : F) * a + w * b = 0 := by
  by_cases ha : a = 0
  · exact ⟨0, -1, 1, 0, by simp, by simp [ha]⟩
  by_cases hb : b = 0
  · exact ⟨1, 0, 0, 1, by simp, by simp [hb]⟩
  rcases V.mem_or_inv_mem (b / a) with h | h
  · exact ⟨1, 0, -⟨_, h⟩, 1, by simp, by simp [ha]⟩
  · exact ⟨0, -1, 1, -⟨_, h⟩, by simp, by simp [hb]⟩

private theorem valuation_ring_clear_last_row_entry {F : Type} [Field F] (V : ValuationSubring F) (Y : Matrix (Fin 3) (Fin 3) F) (c : Fin 3) :
    ∃ k : Matrix (Fin 3) (Fin 3) V, k.det = 1 ∧ (k.map V.subtype * Y) 2 c = 0 ∧
      (Y 1 0 = 0 → Y 2 0 = 0 → (k.map V.subtype * Y) 1 0 = 0 ∧ (k.map V.subtype * Y) 2 0 = 0) := by
  obtain ⟨x, y, z, w, h1, h2⟩ := exists_sl2_valuation_kill V (Y 1 c) (Y 2 c)
  refine ⟨!![1, 0, 0; 0, x, y; 0, z, w], ?_, ?_, fun e1 e2 => ⟨?_, ?_⟩⟩
  · simpa [Matrix.det_fin_three] using h1
  · simpa [Matrix.mul_apply, Fin.sum_univ_three] using h2
  · simp [Matrix.mul_apply, Fin.sum_univ_three, e1, e2]
  · simp [Matrix.mul_apply, Fin.sum_univ_three, e1, e2]

private theorem valuation_ring_clear_first_column {F : Type} [Field F] (V : ValuationSubring F) (Y : Matrix (Fin 3) (Fin 3) F) :
    ∃ k : Matrix (Fin 3) (Fin 3) V, k.det = 1 ∧ (k.map V.subtype * Y) 1 0 = 0 ∧
      (k.map V.subtype * Y) 2 0 = Y 2 0 := by
  obtain ⟨x, y, z, w, h1, h2⟩ := exists_sl2_valuation_kill V (Y 0 0) (Y 1 0)
  refine ⟨!![x, y, 0; z, w, 0; 0, 0, 1], ?_, ?_, ?_⟩
  · simpa [Matrix.det_fin_three] using h1
  · simpa [Matrix.mul_apply, Fin.sum_univ_three] using h2
  · simp [Matrix.mul_apply, Fin.sum_univ_three]

private theorem upper_triangular_of_entries_zero {F : Type} [Field F] {Z : Matrix (Fin 3) (Fin 3) F} (h1 : Z 1 0 = 0) (h2 : Z 2 0 = 0)
    (h3 : Z 2 1 = 0) : Z.BlockTriangular id := by
  intro i j hij
  fin_cases i <;> fin_cases j <;> first | exact absurd hij (by decide) | simpa

private theorem iwasawa_triangularization {F : Type} [Field F] (V : ValuationSubring F) (X : Matrix (Fin 3) (Fin 3) F) :
    ∃ k : GL (Fin 3) V, ((k : Matrix (Fin 3) (Fin 3) V).map V.subtype * X).BlockTriangular id := by
  obtain ⟨k1, d1, a1, -⟩ := valuation_ring_clear_last_row_entry V X 0
  obtain ⟨k2, d2, a2, b2⟩ := valuation_ring_clear_first_column V (k1.map V.subtype * X)
  obtain ⟨k3, d3, a3, b3⟩ := valuation_ring_clear_last_row_entry V (k2.map V.subtype * (k1.map V.subtype * X)) 1
  obtain ⟨b3, c3⟩ := b3 a2 (b2.trans a1)
  obtain ⟨k, hk⟩ := (Matrix.isUnit_iff_isUnit_det (k3 * (k2 * k1))).2
    (by rw [Matrix.det_mul, Matrix.det_mul, d1, d2, d3, one_mul, one_mul]; exact isUnit_one)
  refine ⟨k, ?_⟩
  rw [hk, Matrix.map_mul, Matrix.map_mul, Matrix.mul_assoc, Matrix.mul_assoc]
  exact upper_triangular_of_entries_zero b3 c3 a3

private theorem exists_common_ring_same_kernel {A K L : Type} [CommRing A] [Field K] [Field L] (f : A →+* K) (g : A →+* L)
    (h : RingHom.ker f = RingHom.ker g) :
    ∃ (T : Type) (_ : CommRing T) (_ : Nontrivial T) (i : K →+* T) (j : L →+* T), i.comp f = j.comp g := by
  letI : Algebra (A ⧸ RingHom.ker f) K := (RingHom.kerLift f).toAlgebra
  letI : Algebra (A ⧸ RingHom.ker f) L := (Ideal.Quotient.lift _ g fun a ha => by rwa [h] at ha).toAlgebra
  have h2 : Function.Injective (algebraMap (A ⧸ RingHom.ker f) L) := by
    rw [injective_iff_map_eq_zero]
    intro a ha
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
    rw [Ideal.Quotient.eq_zero_iff_mem, h]
    exact ha
  refine ⟨TensorProduct (A ⧸ RingHom.ker f) K L, inferInstance,
    Algebra.TensorProduct.nontrivial_of_algebraMap_injective_of_isDomain _ _ _ (RingHom.kerLift_injective f) h2,
    (Algebra.TensorProduct.includeLeft (S := A ⧸ RingHom.ker f)).toRingHom,
    Algebra.TensorProduct.includeRight.toRingHom, RingHom.ext fun a => ?_⟩
  exact ((Algebra.TensorProduct.includeLeft (S := A ⧸ RingHom.ker f) (A := K) (B := L)).commutes
    (Ideal.Quotient.mk _ a)).trans
    ((Algebra.TensorProduct.includeRight (A := K) (B := L)).commutes (Ideal.Quotient.mk _ a)).symm

private theorem triangular_form_finite_extension {ι A K B : Type} [CommRing A] [Field K] [CommRing B] [Nontrivial B]
    {M : ι → Matrix (Fin 3) (Fin 3) A} {d : ι → Fin 3 → A} {S T : Set ι} (f : A →+* K) (i : K →+* B)
    (h : GL (Fin 3) B) (H : TriangularForm M d S T (i.comp f) h) :
    ∃ (K' : Type) (_ : Field K') (_ : Algebra K K') (_ : FiniteDimensional K K') (h' : GL (Fin 3) K'),
      TriangularForm M d S T ((algebraMap K K').comp f) h' := by
  classical
  letI := i.toAlgebra
  let s : Set B := Set.range (fun p : Fin 3 × Fin 3 => (h : Matrix (Fin 3) (Fin 3) B) p.1 p.2) ∪
    Set.range (fun p : Fin 3 × Fin 3 => ((h⁻¹ : GL (Fin 3) B) : Matrix (Fin 3) (Fin 3) B) p.1 p.2)
  have hs : s.Finite := (Set.finite_range _).union (Set.finite_range _)
  let B₀ := Algebra.adjoin K s
  haveI : Algebra.FiniteType K B₀ := (Subalgebra.fg_iff_finiteType _).1 (Subalgebra.fg_def.2 ⟨s, hs, rfl⟩)
  let X : Matrix (Fin 3) (Fin 3) B₀ := fun a b => ⟨_, Algebra.subset_adjoin (Or.inl ⟨(a, b), rfl⟩)⟩
  let Y : Matrix (Fin 3) (Fin 3) B₀ := fun a b => ⟨_, Algebra.subset_adjoin (Or.inr ⟨(a, b), rfl⟩)⟩
  have hXY : X * Y = 1 := by
    apply Matrix.map_injective (f := B₀.val.toRingHom) Subtype.val_injective
    show (X * Y).map B₀.val.toRingHom = (1 : Matrix (Fin 3) (Fin 3) B₀).map B₀.val.toRingHom
    rw [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)]
    exact h.mul_inv
  let h₀ : GL (Fin 3) B₀ := ⟨X, Y, hXY, mul_eq_one_comm.1 hXY⟩
  have H0 : TriangularForm M d S T ((algebraMap K B₀).comp f) h₀ :=
    triangular_form_of_injective_map B₀.val.toRingHom Subtype.val_injective H
  obtain ⟨m, hm⟩ := Ideal.exists_maximal B₀
  letI := Ideal.Quotient.field m
  exact ⟨B₀ ⧸ m, inferInstance, inferInstance, finite_of_finite_type_of_isJacobsonRing K (B₀ ⧸ m), _,
    triangular_form_map (Ideal.Quotient.mk m) H0⟩

private theorem triangular_form_specialization {ι A F K : Type} [CommRing A] [Field F] [Field K]
    {M : ι → Matrix (Fin 3) (Fin 3) A} {d : ι → Fin 3 → A} {S T : Set ι} (hT : T ⊆ S) (φ : A →+* F) (f : A →+* K)
    (hf : RingHom.ker φ ≤ RingHom.ker f) (h : GL (Fin 3) F) (H : TriangularForm M d S T φ h) :
    ∃ (K' : Type) (_ : Field K') (_ : Algebra K K') (_ : FiniteDimensional K K') (h' : GL (Fin 3) K'),
      TriangularForm M d S T ((algebraMap K K').comp f) h' := by
  haveI := RingHom.ker_isPrime f
  have hu : ∀ y : (RingHom.ker f).primeCompl, IsUnit (φ y) := fun y => Ne.isUnit fun e => y.2 (hf e)
  obtain ⟨V, hV, hl⟩ := IsLocalRing.exists_factor_valuationRing
    (IsLocalization.lift (S := Localization.AtPrime (RingHom.ker f)) hu)
  let g₀ : Localization.AtPrime (RingHom.ker f) →+* V := (IsLocalization.lift hu).codRestrict V.toSubring hV
  haveI : IsLocalHom g₀ := hl
  let g : A →+* V := g₀.comp (algebraMap _ _)
  have hg : V.subtype.comp g = φ := RingHom.ext fun a => IsLocalization.lift_eq hu a
  have hk : RingHom.ker f = RingHom.ker ((residue V).comp g) := by
    ext a
    rw [RingHom.mem_ker (f := (residue V).comp g), RingHom.comp_apply, residue_eq_zero_iff,
      ← IsLocalization.AtPrime.to_map_mem_maximal_iff (Localization.AtPrime (RingHom.ker f)) (RingHom.ker f) a,
      mem_maximalIdeal, mem_maximalIdeal, mem_nonunits_iff, mem_nonunits_iff]
    exact (isUnit_map_iff g₀ _).not.symm
  obtain ⟨k, hk'⟩ := iwasawa_triangularization V h
  have H1 := triangular_form_borel_change hT H (Matrix.GeneralLinearGroup.map V.subtype k) hk'
  rw [← map_inv, ← hg] at H1
  have H2 := triangular_form_map (residue V) (triangular_form_of_injective_map V.subtype Subtype.val_injective H1)
  obtain ⟨B, _, _, i, j, e⟩ := exists_common_ring_same_kernel f _ hk
  have H3 := triangular_form_map j H2
  rw [← e] at H3
  exact triangular_form_finite_extension f i _ H3

private theorem triangular_in_iff_triangular_form {O A C D : Type} [CommRing O] [CommRing A] [CommRing C] [Algebra O A] [Algebra O C] [Group D]
    (η : D →* ℤˣ) (Ψ : D →* Oˣ) (I : Subgroup D) (u : D →* GG 3 A) (hu : HasMult η u) (φ : A →ₐ[O] C)
    (h : GL (Fin 3) C) : UpperTheory.V.UnitaryThreeInertia.TriIn η Ψ I (push φ u) h ↔
      TriangularForm (fun g => (u g).mat) (fun g a => algebraMap O A (UpperTheory.V.UnitaryThreeInertia.psi Ψ a g)) {g | η g = 1}
        {g | g ∈ I ∧ η g = 1} φ h := by
  have e : ∀ g, η g = 1 → (conjBy h⁻¹ (push φ u) g).mat =
      ((h⁻¹ : GL (Fin 3) C) : Matrix (Fin 3) (Fin 3) C) * (u g).mat.map (φ : A →+* C) * h := by
    intro g hg
    have h1 : (push φ u g).right = 1 := (hu g).trans hg
    have h2 : (push φ u g).left.val = (u g).mat.map (φ : A →+* C) := rfl
    rw [← h2]
    simp [conjBy, GG.mat, h1]
  have hw : ∀ a b : Fin 3, wt a b < 0 ↔ b < a := by decide
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨fun g hg a b hab => ?_, fun g hg a => ?_⟩
    · rw [← e g hg]
      exact h1 g hg a b ((hw a b).2 hab)
    · rw [← e g hg.2, h2 g hg.1 hg.2 a]
      exact (φ.commutes _).symm
  · rintro ⟨h1, h2⟩
    refine ⟨fun g hg a b hab => ?_, fun g hg hg' a => ?_⟩
    · rw [e g hg]
      exact h1 g hg a b ((hw a b).1 hab)
    · rw [e g hg', h2 g ⟨hg, hg'⟩ a]
      exact φ.commutes _

end UpperTheory.V.Loc

theorem UpperTheory.V.Loc.lemma2c :
    LocalPublishedTheorems → ∀ {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O] [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O] [IsAdicComplete (maximalIdeal O) O] (D : Dat3 l O) (U : D.Univ) (K : Type) [Field K] [Algebra O K] (r : GQ l →* GG 3 K), D.On U r → ∃ (K' : Type) (_ : Field K') (_ : Algebra K K') (_ : Algebra O K') (_ : IsScalarTower O K K') (_ : FiniteDimensional K K') (h : GL (Fin 3) K'), UpperTheory.V.UnitaryThreeInertia.TriIn D.η D.Ψ (Iq l) ((GG.map (algebraMap K K')).comp r) h := by
  intro hP l _ O _ _ _ _ _ _ _ D U K _ _ r ⟨f, hr, hf⟩
  obtain ⟨-, hp, hl, -⟩ := UpperTheory.V.Loc.rtBasic hP D U
  haveI : IsDomain (D.Rt U) := Ideal.Quotient.isDomain _
  let φ : U.R →ₐ[O] FractionRing (D.Rt U) :=
    (IsScalarTower.toAlgHom O (D.Rt U) (FractionRing (D.Rt U))).comp (Ideal.Quotient.mkₐ O _)
  have hφ : RingHom.ker φ = D.It U := by
    ext a
    rw [RingHom.mem_ker, ← Ideal.Quotient.eq_zero_iff_mem]
    exact map_eq_zero_iff _ (IsFractionRing.injective (D.Rt U) (FractionRing (D.Rt U)))
  have hl0 : ((l : ℕ) : FractionRing (D.Rt U)) ≠ 0 := fun e => hl (by rw [← hφ, RingHom.mem_ker, map_natCast, e])
  haveI : CharZero (FractionRing (D.Rt U)) := by
    refine charZero_of_inj_zero fun n hn => ?_
    by_contra h0
    have h1 : (n : ℤ_[l]) ≠ 0 := Nat.cast_ne_zero.2 h0
    have h2 := congrArg ((algebraMap O (FractionRing (D.Rt U))).comp (algebraMap ℤ_[l] O))
      (PadicInt.unitCoeff_spec h1)
    rw [map_natCast, hn, map_mul, map_pow, map_natCast] at h2
    exact mul_ne_zero ((Units.isUnit _).map _).ne_zero (pow_ne_zero _ hl0) h2.symm
  obtain ⟨⟨h, H⟩, -⟩ := UpperTheory.V.Loc.lemma2b hP D U _ (push φ U.r.hom) ⟨φ, rfl, hφ.ge⟩
  rw [UpperTheory.V.Loc.triangular_in_iff_triangular_form _ _ _ _ U.r.hasMult] at H
  obtain ⟨K', _, _, _, h', H'⟩ := UpperTheory.V.Loc.triangular_form_specialization (fun g hg => hg.2) _ (f : U.R →+* K) (hφ.le.trans hf) h H
  letI : Algebra O K' := ((algebraMap K K').comp (algebraMap O K)).toAlgebra
  haveI : IsScalarTower O K K' := IsScalarTower.of_algebraMap_eq fun _ => rfl
  refine ⟨K', inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, h', ?_⟩
  subst hr
  exact (UpperTheory.V.Loc.triangular_in_iff_triangular_form _ _ _ _ U.r.hasMult ((IsScalarTower.toAlgHom O K K').comp f) h').2 H'
end

