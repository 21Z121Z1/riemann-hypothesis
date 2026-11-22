import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.FormsFiniteness.OrderedCechToCatCochainsOneApplyValueAtSubset
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle0044
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle0021
import GroundTheory.AutomorphicForms.AutomorphicFormSpaces.GKStableLaplacian
import GroundTheory.AutomorphicForms.AutomorphicFormSpaces.GKStableCartan
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Bundle0006
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Bundle0005
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.RTwist
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0116
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0765
import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0300
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0016
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle0039
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Bundle0007
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle0036
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle0042
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FinrankLetterHomComp

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.ExistsBasisAlgModLaplacianOfTypesCentre
section
open NumberField NumberField.mixedEmbedding Matrix MeasureTheory GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm UpperTheory.V.Af.Fin
open scoped TensorProduct
attribute [local instance 100] LieRing.ofAssociativeRing

private theorem algMod_add {M : Type} [AddCommGroup M] [Module ℂ M] (S : Submodule ℂ M) (A B : Module.End ℂ M)
    (hAB : A * B = B * A) (hA : AlgMod S ⊥ A) (hB : AlgMod S ⊥ B) : AlgMod S ⊥ (A + B) := by
  refine UpperTheory.algMod_bot_of_mem_adjoin_commuting M S {A, B} ?_ ?_ (A + B)
    (Subalgebra.add_mem _ (Algebra.subset_adjoin (by simp)) (Algebra.subset_adjoin (by simp)))
  · intro x hx y hy
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx hy
    rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;> first | rfl | exact hAB | exact hAB.symm
  · intro T hT
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hT
    rcases hT with rfl | rfl <;> assumption

theorem UpperTheory.exists_basis_algMod_laplacian_of_types_centre :
    ∀ (K : Type) [Field K] [NumberField K] (n : ℕ) (S : Submodule ℂ (archSmooth K n)), Types S → Centre S → ∃ (d : ℕ) (b : Module.Basis (Fin d) ℝ (isExpLieAlgebra K n).lieSubalgebra), AlgMod S ⊥ (uAction (laplacianU K n b)) := by
  intro K _ _ n S hT hC
  obtain ⟨d, b, ε, B, hε, horth, hsymm, hinv, hK⟩ := exists_archCartanData K n
  refine ⟨d, b, ?_⟩
  have hε2 : ∀ i, ε i * ε i = 1 := fun i => by rcases hε i with e | e <;> rw [e] <;> norm_num
  have hΩ : casimir b ε ∈ (isExpLieAlgebra K n).centerU := casimir_mem_center hε2 horth hsymm hinv
  rw [laplacianU_eq_casimir_add b ε, map_add]
  refine algMod_add S _ _ (Zc_comm_uAction (uAction_mem_Zc hΩ) _).eq (hC _ hΩ) ?_
  refine UpperTheory.algMod_bot_compact_casimir_of_types K n S hT (Fin d) (fun i => b i) (fun i => 1 - ε i) fun i => ?_
  rcases hε i with e | e
  · exact Or.inl (by rw [e, sub_self])
  · exact Or.inr (hK i e)
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.HeckeCharSignFixed
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N Polynomial GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Af.Bc UpperTheory.V.Published

private theorem isAlgPos_mul {F : Type} [Field F] [NumberField F] {χ χ' : HChar F} {n n' : (F →+* ℂ) → ℤ}
    (h : IsAlgPos χ n) (h' : IsAlgPos χ' n') : IsAlgPos (χ * χ') (n + n') := fun k hk => by
  have e : (χ * χ').inf k = χ.inf k * χ'.inf k := rfl
  rw [e, Units.val_mul, h k hk, h' k hk, ← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun φ _ => (zpow_add₀ ((map_ne_zero φ).2 k.ne_zero) _ _).symm

private theorem quadChar_order (E : Type) [Field E] [NumberField E] [IsCMField E] : (quadChar E).OrderDvd 2 := by
  refine Subtype.ext (MonoidHom.ext fun x => ?_)
  change (Units.map (Int.castRingHom ℂ).toMonoidHom (GlobalTheory.IdeleNormChar.normSign E x)) ^ 2 = 1
  rw [← map_pow, Int.units_sq, map_one]

private theorem place_eq {F : Type} [Field F] [NumberField F] (h : Function.Surjective (algebraMap ℚ F))
    (v v' : InfinitePlace F) : v = v' := by
  rw [← v.mk_embedding, ← v'.mk_embedding]
  congr 1
  ext x
  obtain ⟨q, rfl⟩ := h x
  simp

private theorem exists_sign {F : Type} [Field F] [NumberField F] (h : Function.Surjective (algebraMap ℚ F))
    (χ : HChar F) : ∃ m : ℕ, ∀ v : InfinitePlace F, χ.locInf v (-1) = (-1) ^ m := by
  obtain ⟨v₀⟩ : Nonempty (InfinitePlace F) := inferInstance
  have h2 : χ.locInf v₀ (-1) ^ 2 = 1 := by rw [← map_pow, neg_one_sq, map_one]
  have h3 : ((χ.locInf v₀ (-1) : ℂˣ) : ℂ) ^ 2 = 1 := by rw [← Units.val_pow_eq_pow_val, h2, Units.val_one]
  rcases sq_eq_one_iff.1 h3 with e | e
  · exact ⟨0, fun v => by rw [place_eq h v v₀, pow_zero]; exact Units.ext e⟩
  · exact ⟨1, fun v => by rw [place_eq h v v₀, pow_one]; exact Units.ext e⟩

theorem UpperTheory.heckeChar_sign_fixed :
    UpperTheory.V.Af.Bc.SignFix := by
  intro E Ω _ _ _ hE _ _ _ l _ ι χ μ ⟨hμc, art, a, ha, hχ, hL⟩ n
  obtain ⟨m, hm⟩ := exists_sign (surjective_algebraMap_real E hE) χ
  have ho : (quadChar E ^ (m + n)).OrderDvd 2 := by
    have := quadChar_order E
    unfold HChar.OrderDvd at this ⊢
    rw [← pow_mul, mul_comm, pow_mul, this, one_pow]
  have hη := isAlgPos_zero_of_orderDvd two_pos ho
  obtain ⟨δ, hδc, hδ⟩ := ha.exists_isLAdicOf ι hη
  have h0 : (1 : HChar E).IsAbsPow 0 := ⟨fun v x _ => rfl, fun v => by simp [HChar.val, HChar.locK, HChar.loc],
    fun k => by simp [HChar.inf]⟩
  have h1 : compNorm E 1 = 1 * (GlobalTheory.ThetaPull.thetaChar (1 : HChar E))⁻¹ := by
    rw [map_one, one_mul, eq_comm, inv_eq_one]
    exact Subtype.ext (MonoidHom.ext fun x => inv_one)
  have hres := GlobalTheory.T.ladicCharacter_restrict_cmField_eq_cyclotomicPow E Ω l ι 1 0 h0 1 h1 (m + n) δ (by rw [one_mul]; exact ⟨hδc, art, 0, ha, hη, hδ⟩) 0 (by simp)
  refine ⟨χ * quadChar E ^ (m + n), μ * δ, ⟨hμc.mul hδc, art, a + 0, ha, isAlgPos_mul hχ hη, hL.mul hδ⟩, ?_, ?_, fun v => ?_⟩
  · rw [map_mul, map_pow, compNorm_quadChar, one_pow, mul_one]
  · rw [MonoidHom.mul_comp, hres, zpow_zero, mul_one]
  · rw [HChar.locInf_mul, locInf_pow, hm, quadChar_locInf, ← pow_add, ← add_assoc, pow_add, ← two_mul, pow_mul]
    simp
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.MemISupAutomorphicRepsOfInvariantForm
section
open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC GlobalTheory.DefU

theorem UpperTheory.mem_iSup_automorphicReps_of_invariant_form :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (B : (UA E n → ℂ) →ₗ⋆[ℂ] (UA E n → ℂ) →ₗ[ℂ] ℂ), (∀ φ, IsAutFormU φ → B φ φ = 0 → φ = 0) → (∀ x φ ψ, IsAutFormU φ → IsAutFormU ψ → B (RU E n x φ) (RU E n x ψ) = B φ ψ) → ∀ φ : UA E n → ℂ, IsAutFormU φ → φ ∈ ⨆ σ : {σ : Submodule ℂ (UA E n → ℂ) // IsAutRepU σ}, σ.1 := by
  intro E _ _ _ n B hdef hinv φ hφ
  classical
  haveI : FiniteDimensional ℂ (admitted.X φ) := hφ.kfin
  have hXA : admitted.X φ ≤ autU E n := Submodule.span_le.2 (by
    rintro _ ⟨k, rfl⟩
    exact RU_mem_autU _ _ (mem_autU.2 hφ))
  have haut : ∀ v : admitted.X φ, IsAutFormU (v : UA E n → ℂ) := fun v => mem_autU.1 (hXA v.2)
  let Z : Subrepresentation ((RU E n).comp (infU E n).subtype) :=
    ⟨admitted.X φ, fun g v hv => admitted.RU_mem_X φ g hv⟩
  let ρ : Representation ℂ (infU E n) (admitted.X φ) := Z.toRepresentation
  have hρ : ∀ g (v : admitted.X φ), ((ρ g v : admitted.X φ) : UA E n → ℂ) = RU E n g v := fun _ _ => rfl
  let B' : admitted.X φ →ₗ⋆[ℂ] admitted.X φ →ₗ[ℂ] ℂ := (B.comp (admitted.X φ).subtype).compl₂ (admitted.X φ).subtype
  have hx := UpperTheory.mem_iSup_irreducible_of_admissible_unitary (infU E n) (admitted.X φ) ρ B'
    (fun v hv => Subtype.ext (hdef _ (haut v) hv))
    (fun g u v => hinv g _ _ (haut u) (haut v))
    (fun v => ⟨⊥, fun k hk => by rw [Subgroup.mem_bot.1 hk, map_one]; rfl, inferInstance,
      fun w => Set.finite_range _⟩)
    ⟨φ, admitted.self_mem_X φ⟩
  have hle : (⨆ U : {U : Submodule ℂ (admitted.X φ) // U ≠ ⊥ ∧ (∀ g, ∀ u ∈ U, ρ g u ∈ U) ∧
      ∀ N ≤ U, (∀ g, ∀ u ∈ N, ρ g u ∈ N) → N = ⊥ ∨ N = U}, U.1) ≤
      (⨆ σ : {σ : Submodule ℂ (UA E n → ℂ) // IsAutRepU σ}, σ.1).comap (admitted.X φ).subtype := by
    refine iSup_le ?_
    rintro ⟨U, h0, hst, hirr⟩ u hu
    let Y : Subrepresentation ρ := ⟨U, fun g v hv => hst g v hv⟩
    let τ : Representation ℂ (infU E n) U := Y.toRepresentation
    have hτ : τ.IsIrreducible := by
      refine (GlobalTheory.CuspRep.isIrreducible_iff _).2 ⟨Submodule.nontrivial_iff_ne_bot.2 h0, fun N hN => ?_⟩
      rcases hirr (N.map U.subtype) (Submodule.map_subtype_le _ _) (by
        rintro g _ ⟨w, hw, rfl⟩
        exact ⟨τ g w, hN g w hw, rfl⟩) with h | h
      · left
        exact Submodule.map_injective_of_injective U.injective_subtype (by rw [h, Submodule.map_bot])
      · right
        exact Submodule.map_injective_of_injective U.injective_subtype
          (by rw [h, Submodule.map_top, Submodule.range_subtype])
    exact UpperTheory.admissible_equivariantForms_representation E n B hdef hinv U τ
      (GlobalTheory.ClassFin.span_range_eq_top_of_isIrreducible _ _ τ hτ)
      ((admitted.X φ).subtype ∘ₗ U.subtype) (fun v => haut v.1) (fun _ _ => rfl) ⟨u, hu⟩
  exact hle hx
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.WeilDeligneCharacterTwistPeriod
section
noncomputable section

open Formalism.ConjugateSelfDual Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Module TensorProduct GlobalTheory.Pst Polynomial

private theorem zpow_fix {Q R : Type} [Field Q] [CommRing R] [Algebra Q R] (f : R →ₐ[Q] R) (T : Rˣ) (c : Qˣ)
    (h : (c : Q) • f (T : R) = T) (m : ℤ) : ((c ^ m : Qˣ) : Q) • f ((T ^ m : Rˣ) : R) = ((T ^ m : Rˣ) : R) := by
  have e : Units.map (algebraMap Q R : Q →* R) c * Units.map (f : R →* R) T = T := by
    ext; simpa [Algebra.smul_def] using h
  have e' : Units.map (algebraMap Q R : Q →* R) (c ^ m) * Units.map (f : R →* R) (T ^ m) = T ^ m := by
    rw [map_zpow, map_zpow, ← mul_zpow, e]
  rw [Algebra.smul_def]
  exact congrArg Units.val e'

private theorem smul_mul_tmul {Q A R : Type} [Field Q] [Field A] [CommRing R] [Algebra Q R] [Algebra Q A]
    (c : Q) (x : A ⊗[Q] R) (b : R) : algebraMap Q A c • (x * (1 : A) ⊗ₜ[Q] b) = x * (1 : A) ⊗ₜ[Q] (c • b) := by
  rw [algebraMap_smul, tmul_smul, mul_smul_comm]

variable {l : ℕ} [Fact l.Prime] (P : LocPrime l) {K L : FinExt l}

private theorem stRep_mul (κ η : ↥(GK K) →* (↥L.1)ˣ) (g : ↥(GK K)) (a : ↥L.1) (h : (κ g : ↥L.1) = a * η g)
    (u : ↥L.1 ⊗[ℚ_[l]] Bst P) (b : Bst P) :
    stRep P (UpperTheory.V.Loc.chRep κ) g (u * (1 : ↥L.1) ⊗ₜ[ℚ_[l]] b) =
      a • (stRep P (UpperTheory.V.Loc.chRep η) g u * (1 : ↥L.1) ⊗ₜ[ℚ_[l]] actSt P (g : GQ l) b) := by
  induction u using TensorProduct.induction_on with
  | zero => simp
  | tmul v x =>
    rw [Algebra.TensorProduct.tmul_mul_tmul, stRep_tmul, stRep_tmul, Algebra.TensorProduct.tmul_mul_tmul,
      map_mul (actSt P (g : GQ l)), smul_tmul']
    congr 1
    simp [UpperTheory.V.Loc.chRep, h, mul_assoc]
  | add x y hx hy => simp only [add_mul, map_add, hx, hy, smul_add]

private theorem phiV_mul (u : ↥L.1 ⊗[ℚ_[l]] Bst P) (b : Bst P) :
    phiV P ↥L.1 ↥L.1 (u * (1 : ↥L.1) ⊗ₜ[ℚ_[l]] b) = phiV P ↥L.1 ↥L.1 u * (1 : ↥L.1) ⊗ₜ[ℚ_[l]] phiSt P b := by
  induction u using TensorProduct.induction_on with
  | zero => simp
  | tmul v x =>
    rw [Algebra.TensorProduct.tmul_mul_tmul, phiV_tmul, phiV_tmul, Algebra.TensorProduct.tmul_mul_tmul, map_mul]
  | add x y hx hy => simp only [add_mul, map_add, hx, hy]

private theorem phiV_pow_mul (c : ℚ_[l]) (b : Bst P) (hb : c • phiSt P b = b) (k : ℕ) (u : ↥L.1 ⊗[ℚ_[l]] Bst P) :
    (algebraMap ℚ_[l] ↥L.1 c) ^ k • (phiV P ↥L.1 ↥L.1 ^ k) (u * (1 : ↥L.1) ⊗ₜ[ℚ_[l]] b) =
      (phiV P ↥L.1 ↥L.1 ^ k) u * (1 : ↥L.1) ⊗ₜ[ℚ_[l]] b := by
  induction k generalizing u with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, pow_succ, End.mul_apply, End.mul_apply, mul_smul, ← map_smul, phiV_mul, smul_mul_tmul, hb, ih]

theorem UpperTheory.weilDeligne_character_twist_period :
    UpperTheory.V.Af.Wd.TwistPer := by
  intro l _ K L κ χ η m hκ hc hη
  have hu := UpperTheory.weilDeligne_unramified_period l K L η hc hη
  unfold UpperTheory.V.Af.Wd.cycL at hκ
  generalize UpperTheory.V.Loc.PP l = P at hu hκ ⊢
  obtain ⟨u, hu0, hu1, hu2⟩ := hu
  have hl : (l : ℚ_[l]) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : l.Prime).ne_zero
  let T : (Bst P)ˣ := Units.map (C : P.R.B →+* Bst P) (isUnit_tB P).unit⁻¹
  have hT : (T : Bst P) = C (tInv P) := rfl
  have h1 : ∀ g : GQ l, ((P.χQ g ^ m : ℚ_[l]ˣ) : ℚ_[l]) • actSt P g ((T ^ m : (Bst P)ˣ) : Bst P) = ((T ^ m : (Bst P)ˣ) : Bst P) :=
    fun g => zpow_fix (actSt P g) T (P.χQ g) (by rw [hT, actSt_C, smul_C, smul_actQ_tInv]) m
  have h2 := zpow_fix (phiSt P) T (Units.mk0 _ hl) (by rw [hT, phiSt_C, smul_C, Units.val_mk0, smul_phiB_tInv]) m
  refine ⟨u * (1 : ↥L.1) ⊗ₜ[ℚ_[l]] ((T ^ m : (Bst P)ˣ) : Bst P), fun h0 => hu0 ?_, fun g => ?_, fun g k hk => ?_⟩
  · have := congrArg (· * (1 : ↥L.1) ⊗ₜ[ℚ_[l]] (((T ^ m)⁻¹ : (Bst P)ˣ) : Bst P)) h0
    simpa only [mul_assoc, Algebra.TensorProduct.tmul_mul_tmul, Units.mul_inv, mul_one, zero_mul,
      ← Algebra.TensorProduct.one_def] using this
  · rw [stRep_mul P κ η g ((χ g : ↥L.1) * algebraMap ℚ_[l] ↥L.1 ((P.χQ (g : GQ l) ^ m : ℚ_[l]ˣ) : ℚ_[l])) ?_, hu1,
      mul_smul, smul_mul_tmul, h1]
    rw [hκ g, Units.val_mul, Units.val_mul, mul_comm (χ g : ↥L.1)]
    simp
  · have e : (l : ↥L.1) ^ (m * k) = (algebraMap ℚ_[l] ↥L.1 ((Units.mk0 _ hl ^ m : ℚ_[l]ˣ) : ℚ_[l])) ^ k := by
      simp [zpow_mul]
    rw [e, mul_smul, phiV_pow_mul P _ _ h2, ← smul_mul_assoc, hu2 g k hk]
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.WeilDeligneTriangularizable
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Module
open GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.Pst.DpstMap UpperTheory.V UpperTheory.V.Af.Wd

private theorem nil_line {k W : Type} [Field k] [AddCommGroup W] [Module k W] (h1 : finrank k W = 1) {N : End k W}
    (hN : IsNilpotent N) : N = 0 := by
  obtain ⟨y, hy0, hy⟩ := finrank_eq_one_iff'.1 h1
  obtain ⟨c, hc⟩ := hy (N y)
  obtain ⟨n, hn⟩ := hN
  have hp : ∀ m : ℕ, (N ^ m) y = c ^ m • y := by
    intro m
    induction m with
    | zero => simp
    | succ m ih => rw [pow_succ', End.mul_apply, ih, map_smul, ← hc, smul_smul, pow_succ]
  have h2 := hp n
  rw [hn, LinearMap.zero_apply] at h2
  have hc0 : c = 0 := by
    rcases smul_eq_zero.1 h2.symm with h | h
    · exact (pow_eq_zero_iff'.1 h).1
    · exact absurd h hy0
  ext x
  obtain ⟨a, rfl⟩ := hy x
  rw [map_smul, ← hc, hc0]
  simp

private theorem snoc_ops {k W' W W'' Γ : Type} [Field k] [AddCommGroup W'] [Module k W'] [AddCommGroup W] [Module k W]
    [AddCommGroup W''] [Module k W''] {n : ℕ} {N' : End k W'} {N : End k W} {N'' : End k W''} {R' : Γ → End k W'}
    {R : Γ → End k W} {R'' : Γ → End k W''} {f : W' →ₗ[k] W} {p : W →ₗ[k] W''} (hf : Function.Injective f)
    (hp : Function.Surjective p) (hex : Function.Exact f p) (h1 : finrank k W'' = 1) (hfN : ∀ x, f (N' x) = N (f x))
    (hfR : ∀ a x, f (R' a x) = R a (f x)) (hpN : ∀ x, p (N x) = N'' (p x)) (hpR : ∀ a x, p (R a x) = R'' a (p x))
    {μ : Γ → Fin (n + 1) → k} (hI : IsTri (ops N' R') (ops 0 fun a i => μ a (Fin.castSucc i))) (hN : IsNilpotent N'')
    (hl : ∀ a y, R'' a y = μ a (Fin.last n) • y) : IsTri (ops N R) (ops 0 μ) := by
  refine UpperTheory.abelianField_window_triple_snoc k _ _ _ _ n (ops N' R') _ (ops N'' R'') f p hf hp hex h1 ?_ ?_ _ ?_ ?_
  · rintro (_ | σ) x
    · exact hfN x
    · exact hfR σ x
  · rintro (_ | σ) x
    · exact hpN x
    · exact hpR σ x
  · convert hI using 1
    funext a i
    cases a <;> rfl
  · rintro (_ | σ) y
    · rw [ops_none, ops_none, nil_line h1 hN]
      simp
    · exact hl σ y

theorem UpperTheory.weilDeligne_triangularizable :
    UpperTheory.V.Af.Wd.WdTri := by
  intro F Ω _ _ _ _ _ l _ ι w A h O _ _ _ Bw hj L n
  induction n with
  | zero =>
    intro V _ _ _ _ _ ρ κ μ ⟨b, _⟩ _ hV
    haveI := hV.finite
    have h0 : finrank ℂ (WDSpace (Loc.PP l) ι ρ) = 0 := by
      rw [LetterDim.finrank_wdSpace l _ ι _ L V ρ hV, finrank_eq_card_basis b, Fintype.card_fin]
    exact ⟨finBasisOfFinrankEq ℂ _ h0, fun a => ⟨fun i => i.elim0, fun i => i.elim0⟩⟩
  | succ n ih =>
    intro V _ _ _ _ _ ρ κ μ hT hκ hV
    obtain ⟨S, hS, p, hp, hker, hpT, hT'⟩ := UpperTheory.weilDeligne_triangular_initial_segment _ _ _ n _ _ hT
    let ρ' : Representation ↥L.1 ↥(GK Bw.Kw) ↥S := ρ.subrepresentation S fun g x hx => hS g x hx
    have hf : ∀ g v, S.subtype (ρ' g v) = ρ g (S.subtype v) := fun _ _ => rfl
    have hpe : ∀ g v, p (ρ g v) = Loc.chRep (κ (Fin.last n)) g (p v) := fun g v => hpT g v
    have hex : Function.Exact S.subtype p := by
      rw [LinearMap.exact_iff, hker, Submodule.range_subtype]
    obtain ⟨h', h'', hinj, hsurj, hexW⟩ := UpperTheory.weil_deligne_functor_exactness l ι Bw.Kw L ↥S V ↥L.1 ρ' ρ (Loc.chRep (κ (Fin.last n)))
      S.subtype p hf hpe S.subtype_injective hp hex hV
    haveI := hV.finite
    haveI := h'.finite
    haveI := h''.finite
    have h1 : finrank ℂ (WDSpace (Loc.PP l) ι (Loc.chRep (κ (Fin.last n)))) = 1 := by
      rw [LetterDim.finrank_wdSpace l _ ι _ L _ _ h'', finrank_self]
    have hI := ih ↥S ρ' (fun i => κ (Fin.castSucc i)) (fun σ i => μ σ (Fin.castSucc i)) hT'
      (fun i => hκ (Fin.castSucc i)) h'
    exact snoc_ops hinj hsurj hexW h1 (wdLin_wdN _ ι hf) (wdLin_wdRho _ ι Bw h hj hf) (wdLin_wdN _ ι hpe)
      (wdLin_wdRho _ ι Bw h hj hpe) hI (isNilpotent_wdN _ ι _) (hκ (Fin.last n) h'')
end

