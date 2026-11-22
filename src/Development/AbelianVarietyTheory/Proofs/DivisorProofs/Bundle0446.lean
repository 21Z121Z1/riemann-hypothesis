import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0009
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0008
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0425
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0371
import Development.AbelianVarietyTheory.Definitions.Divisors.OrthSubrepresentation
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0263
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0438
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0277
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0262
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.WeightedSumBounds.PeriodValuationTheory
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.WeightedSumBounds.Bundle0004
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0004
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0432
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0426
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0192
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0235
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0249
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0304
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0427
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0372
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0428
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0359
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0395
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0400
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0365
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0385
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0411

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CupProductNaturalInSheafComplexPairing
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace GlobalTheory

theorem cup_natural_in_pairing : ∀ (R : Type) [CommRing R] {I J K I' J' K' : Cx R} (μ : Pair I J K) (ν : Pair I' J' K') (f : I ⟶ I') (g : J ⟶ J') (u : K ⟶ K'), μ.Compat ν f g u → ∀ (E : Spc) {n m k : ℤ} (hk : n + m = k) a b, cpush _ u k (μ.cup E hk a b) = ν.cup E hk (cpush _ f n a) (cpush _ g m b) := by
  intro R _ I J K I' J' K' μ ν f g u hc E n m k hk a b
  obtain ⟨α, rfl⟩ := a.mk_surjective
  obtain ⟨β, rfl⟩ := b.mk_surjective
  obtain ⟨γ, hγ⟩ := (GlobalTheory.T.cup_eq_class_of_isAW R μ hk).1 α β
  rw [(GlobalTheory.T.cup_eq_class_of_isAW R μ hk).2 α β γ hγ]
  simp only [cpush, cpost_mk]
  refine ((GlobalTheory.T.cup_eq_class_of_isAW R ν hk).2 _ _ _ ?_).symm
  intro N w h U x
  have hm := fun {L L' : Cx R} (φ : L ⟶ L') {d : ℤ} (c : Cochain ((chains R).obj E) L d) p s hs U x =>
    (GlobalTheory.T.etaleCochainEvalOnSimplex_basic_properties R (E := E) (I := L) (n := d)).2.2.2.2 φ c p s hs U x
  change ev (γ.1.comp (Cochain.ofHom u) (add_zero k)) N w h U x = _
  rw [hm, hγ N w h U x]
  refine (map_sum ((u.f w).hom.app (op U)).hom _ _).trans ?_
  refine Finset.sum_congr rfl fun p _ => ?_
  change Sec.map (u.f w) _ = _ • ν.mul U _ _ w _ (ev (α.1.comp (Cochain.ofHom f) (add_zero n)) _ _ _ U _) (ev (β.1.comp (Cochain.ofHom g) (add_zero m)) _ _ _ U _)
  rw [hm, hm, Units.smul_def, Units.smul_def, ← hc]
  exact map_zsmul ((u.f w).hom.app (op U)).hom _ _

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspidalCharacterGLFiniteFieldFrobeniusPow
section
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical

namespace GlobalTheory.Shin

theorem psiG_gal (F : Type) [Field F] [Finite F] (t : F ≃+* F) (S : F[X] → ℂ) :
    ∀ (n : ℕ) (x : GL (Fin n) F),
      psiG S n (gal (t : F →+* F) n x) = psiG (fun P => S (P.map (t : F →+* F))) n x := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro x
    rw [GlobalTheory.T.primitiveFunctionCharpolyGL_harishChandra_recursion F S n (gal (t : F →+* F) n x), GlobalTheory.T.primitiveFunctionCharpolyGL_harishChandra_recursion F _ n x]
    congr 1
    · simp only [chG, gal]
      congr 1
      rw [← Matrix.charpoly_map]
      rfl
    · refine Finset.sum_congr rfl fun a ha => ?_
      rw [GlobalTheory.T.harishChandraInductionGL_fieldAutomorphism F t a (n - a) n]
      have ha' : a < n := Finset.mem_range.1 ha
      congr 1
      funext y
      exact ih a ha' y

theorem cusp_gal : ∀ (F : Type) [Field F] [Finite F] (θ : AlgebraicClosure F →* ℂ) (t : F ≃+* F) (j : ℕ),
    (∀ x, t x = x ^ (ringChar F ^ j)) → ∀ (m k : ℕ) (x : GL (Fin m) F),
    cusp θ m k (gal (t : F →+* F) m x) = cusp θ m (k * ringChar F ^ j) x := by
  intro F _ _ θ t j ht m k x
  simp only [cusp]
  rw [psiG_gal F t]
  congr 2
  funext P
  exact GlobalTheory.T.rootSum_map_frobenius_pow_eq_rootSum_mul F θ (t : F →+* F) j (fun y => ht y) k P

end GlobalTheory.Shin
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DegreeLatticePrimeScaling
section
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical

namespace GlobalTheory.Shin.NormSurj

variable {F F' : Type} [Field F] [Field F'] [Algebra F F']

theorem coe_galAct (n : ℕ) (t : F' ≃ₐ[F] F') (x : GL (Fin n) F') :
    ((galAct F F' n t x : GL (Fin n) F') : Matrix (Fin n) (Fin n) F') =
      (x : Matrix (Fin n) (Fin n) F').map t := by
  rfl

theorem map_incl (n : ℕ) (t : F' ≃ₐ[F] F') (γ : GL (Fin n) F) :
    ((incl F F' n γ : GL (Fin n) F') : Matrix (Fin n) (Fin n) F').map t =
      ((incl F F' n γ : GL (Fin n) F') : Matrix (Fin n) (Fin n) F') := by
  ext i j
  simp [incl, gal]

theorem adjoin_stable (n : ℕ) (t : F' ≃ₐ[F] F') (γ : GL (Fin n) F) :
    ∀ x ∈ Algebra.adjoin F' {((incl F F' n γ : GL (Fin n) F') : Matrix (Fin n) (Fin n) F')},
      x.map t ∈ Algebra.adjoin F' {((incl F F' n γ : GL (Fin n) F') : Matrix (Fin n) (Fin n) F')} := by
  intro x hx
  induction hx using Algebra.adjoin_induction with
  | mem x hx =>
    rw [Set.mem_singleton_iff.1 hx, map_incl]
    exact Algebra.subset_adjoin rfl
  | algebraMap r =>
    have : (algebraMap F' (Matrix (Fin n) (Fin n) F') r).map t = algebraMap F' _ (t r) := by
      ext i j
      simp only [Matrix.map_apply, Matrix.algebraMap_matrix_apply]
      split_ifs <;> simp
    rw [this]; exact Subalgebra.algebraMap_mem _ _
  | add x y _ _ hx hy =>
    rw [Matrix.map_add _ (map_add t)]; exact Subalgebra.add_mem _ hx hy
  | mul x y _ _ hx hy =>
    have := Matrix.map_mul (L := x) (M := y) (f := (t : F' →+* F'))
    erw [this]; exact Subalgebra.mul_mem _ hx hy

theorem adjoin_comm {A : Type} [Ring A] [Algebra F' A] (M : A) :
    ∀ x ∈ Algebra.adjoin F' {M}, ∀ y ∈ Algebra.adjoin F' {M}, x * y = y * x := by
  intro x hx y hy
  rw [Algebra.adjoin_singleton_eq_range_aeval] at hx hy
  obtain ⟨p, rfl⟩ := (AlgHom.mem_range _).1 hx
  obtain ⟨q, rfl⟩ := (AlgHom.mem_range _).1 hy
  rw [← map_mul, mul_comm, map_mul]

theorem inv_mem_of_finite {n : ℕ} [Finite F'] (B : Subalgebra F' (Matrix (Fin n) (Fin n) F'))
    (δ : GL (Fin n) F') (h : (δ : Matrix (Fin n) (Fin n) F') ∈ B) :
    ((δ⁻¹ : GL (Fin n) F') : Matrix (Fin n) (Fin n) F') ∈ B := by
  haveI : Finite (Matrix (Fin n) (Fin n) F') := inferInstanceAs (Finite (Fin n → Fin n → F'))
  let f : B → B := fun b => ⟨δ, h⟩ * b
  have hf : Function.Injective f := by
    intro a b hab
    have h1 : (δ : Matrix (Fin n) (Fin n) F') * a = δ * b := congrArg Subtype.val hab
    apply Subtype.ext
    have h2 := congrArg (fun m => ((δ⁻¹ : GL (Fin n) F') : Matrix (Fin n) (Fin n) F') * m) h1
    simpa [← mul_assoc] using h2
  obtain ⟨b, hb⟩ := (Finite.injective_iff_surjective.1 hf) 1
  have hb' : (δ : Matrix (Fin n) (Fin n) F') * b = 1 := congrArg Subtype.val hb
  have : ((δ⁻¹ : GL (Fin n) F') : Matrix (Fin n) (Fin n) F') = b := by
    calc ((δ⁻¹ : GL (Fin n) F') : Matrix (Fin n) (Fin n) F')
        = ((δ⁻¹ : GL (Fin n) F') : Matrix (Fin n) (Fin n) F') * (δ * b) := by rw [hb', mul_one]
      _ = b := by rw [← mul_assoc]; simp
  rw [this]; exact b.2

def unitsIn {n : ℕ} [Finite F'] (B : Subalgebra F' (Matrix (Fin n) (Fin n) F')) :
    Subgroup (GL (Fin n) F') where
  carrier := {δ | (δ : Matrix (Fin n) (Fin n) F') ∈ B}
  one_mem' := by simpa using B.one_mem
  mul_mem' := fun ha hb => by simpa using B.mul_mem ha hb
  inv_mem' := fun h => inv_mem_of_finite B _ h

theorem nrm_surj_adjoin : ∀ (F F' : Type) [Field F] [Field F'] [Algebra F F'] [Finite F'] (s : F' ≃ₐ[F] F'),
    (∀ t : F' ≃ₐ[F] F', t ∈ Subgroup.zpowers s) → ∀ (n : ℕ) (γ : GL (Fin n) F), ∃ δ : GL (Fin n) F',
      (δ : Matrix (Fin n) (Fin n) F') ∈
        Algebra.adjoin F' {((incl F F' n γ : GL (Fin n) F') : Matrix (Fin n) (Fin n) F')} ∧
      nrm s δ = incl F F' n γ := by
  intro F F' _ _ _ _ s hs n γ
  set M : Matrix (Fin n) (Fin n) F' := ((incl F F' n γ : GL (Fin n) F') : Matrix (Fin n) (Fin n) F') with hM
  set B := Algebra.adjoin F' {M} with hB
  obtain ⟨hfix, hinj, -, hcomm4, hmul⟩ := GlobalTheory.T.galoisTwistedNormGL_basic_properties F F' s hs n
  have hcard := GlobalTheory.T.card_twistedNorm_one_mul_card_fixed_units F F' s hs n B (adjoin_stable n s γ)
  have hstab : ∀ (t : F' ≃ₐ[F] F') (δ : GL (Fin n) F'), δ ∈ unitsIn B → galAct F F' n t δ ∈ unitsIn B :=
    fun t δ h => by
      show ((galAct F F' n t δ : GL (Fin n) F') : Matrix (Fin n) (Fin n) F') ∈ B
      rw [coe_galAct]; exact adjoin_stable n t γ _ h
  have hcommB : ∀ x ∈ B, ∀ y ∈ B, x * y = y * x := adjoin_comm M
  have hcommU : ∀ δ ∈ unitsIn B, ∀ ε ∈ unitsIn B, δ * ε = ε * δ := fun δ hδ ε hε =>
    Units.ext (by simpa using hcommB _ hδ _ hε)
  have hnrm_mem : ∀ δ ∈ unitsIn B, nrm s δ ∈ unitsIn B := by
    intro δ hδ
    unfold nrm nrmG
    apply Subgroup.list_prod_mem
    intro x hx
    obtain ⟨i, -, rfl⟩ := List.mem_map.1 hx
    exact hstab _ _ hδ
  have hmulU : ∀ δ ∈ unitsIn B, ∀ ε ∈ unitsIn B, nrm s (δ * ε) = nrm s δ * nrm s ε :=
    fun δ hδ ε hε => hmul δ ε (fun t u => hcommU _ (hstab t δ hδ) _ (hstab u ε hε))
  let N : unitsIn B →* unitsIn B := MonoidHom.mk' (fun δ => ⟨nrm s δ, hnrm_mem δ δ.2⟩)
    (fun a b => Subtype.ext (hmulU a a.2 b b.2))
  have hfixN : ∀ δ ∈ unitsIn B, galAct F F' n s (nrm s δ) = nrm s δ := by
    intro δ hδ
    have h4 := hcomm4 δ
    rw [hcommU _ (hnrm_mem δ hδ) _ hδ] at h4
    exact mul_left_cancel h4
  let W : Set (unitsIn B) := {x | galAct F F' n s x = x}
  have hRW : (N.range : Set (unitsIn B)) ⊆ W := by
    rintro _ ⟨δ, rfl⟩
    exact hfixN δ δ.2
  have hVW : Nat.card {x : GL (Fin n) F // ((incl F F' n x : GL (Fin n) F') : Matrix (Fin n) (Fin n) F') ∈ B}
      = Nat.card W := by
    apply Nat.card_congr
    refine Equiv.ofBijective (fun x => ⟨⟨incl F F' n x.1, x.2⟩, (hfix _).2 ⟨x.1, rfl⟩⟩) ⟨?_, ?_⟩
    · intro a b h
      have := congrArg (fun y : W => ((y : unitsIn B) : GL (Fin n) F')) h
      exact Subtype.ext (hinj this)
    · rintro ⟨⟨x, hx⟩, hxW⟩
      obtain ⟨y, rfl⟩ := (hfix x).1 hxW
      exact ⟨⟨y, hx⟩, rfl⟩
  have hUc : Nat.card {x : GL (Fin n) F' // (x : Matrix (Fin n) (Fin n) F') ∈ B} = Nat.card (unitsIn B) :=
    Nat.card_congr (Equiv.subtypeEquivRight (fun x => Iff.rfl))
  have hKc : Nat.card {ε : GL (Fin n) F' // (ε : Matrix (Fin n) (Fin n) F') ∈ B ∧ nrm s ε = 1}
      = Nat.card N.ker := by
    apply Nat.card_congr
    exact
      { toFun := fun ε => ⟨⟨ε.1, ε.2.1⟩, (MonoidHom.mem_ker).2 (Subtype.ext ε.2.2)⟩
        invFun := fun ε => ⟨ε.1.1, ε.1.2, congrArg Subtype.val ((MonoidHom.mem_ker).1 ε.2)⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
  have hsplit : Nat.card N.ker * Nat.card N.range = Nat.card (unitsIn B) := by
    rw [← Subgroup.index_ker]; exact Subgroup.card_mul_index _
  have hKpos : 0 < Nat.card N.ker := Nat.card_pos
  have hVR : Nat.card W = Nat.card N.range := by
    rw [← hVW]
    rw [hKc, hUc, ← hsplit] at hcard
    exact Nat.eq_of_mul_eq_mul_left hKpos hcard
  have hEq : (N.range : Set (unitsIn B)) = W := by
    apply Set.eq_of_subset_of_ncard_le hRW
    · rw [← Nat.card_coe_set_eq, ← Nat.card_coe_set_eq, hVR]; rfl
  have hmem : (⟨incl F F' n γ, Algebra.subset_adjoin rfl⟩ : unitsIn B) ∈ W := by
    show galAct F F' n s (incl F F' n γ) = incl F F' n γ
    exact (hfix _).2 ⟨γ, rfl⟩
  rw [← hEq] at hmem
  obtain ⟨δ, hδ⟩ := hmem
  exact ⟨δ, δ.2, congrArg Subtype.val hδ⟩

end GlobalTheory.Shin.NormSurj
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DifferentialOperatorDepthIntegralCoordinates
section
namespace GlobalTheory.FGDepth.Coord

open MvPowerSeries ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Sh GlobalTheory.FGDepth

noncomputable section

variable {C : Type} [Field C]

theorem hs0 {σ τ : Type} [Finite σ] {a : σ → MvPowerSeries τ C}
    (h : ∀ s, constantCoeff (a s) = 0) : HasSubst a := hasSubst_of_constantCoeff_zero h

theorem cX {σ : Type} (s : σ) : constantCoeff (X s : MvPowerSeries σ C) = 0 := by simp

open MvPowerSeries in
private lemma subst_sum_smul_X' {C : Type} [Field C] {σ τ ι : Type} [Fintype ι]
    {b : σ → MvPowerSeries τ C} (hb : HasSubst b) (c : ι → C) (g : ι → σ) :
    subst b (∑ a, c a • (X (g a) : MvPowerSeries σ C)) = ∑ a, c a • b (g a) := by
  rw [← coe_substAlgHom hb, map_sum]
  simp only [map_smul, coe_substAlgHom, subst_X hb]

open MvPowerSeries in
private lemma mvIsInt_X_divisor {C : Type} [Field C] (v : AddValuation C (WithTop ℝ)) {σ : Type}
    (s : σ) : _root_.ReciprocityTheory.PGsh.MvIsInt v (X s : MvPowerSeries σ C) := by
  classical
  intro α
  show 0 ≤ v (coeff α (X s : MvPowerSeries σ C))
  rw [coeff_X]
  split_ifs <;> simp

open MvPowerSeries in
variable {C : Type} [Field C] in

theorem _root_.GlobalTheory.FGDepth.Coord.depth_in_coords : ∀ (C : Type) [Field C] [CharZero C]
    (v : AddValuation C (WithTop ℝ)) (i d c : ℕ) (G : _root_.ReciprocityTheory.PGsh.LogFGL v d) (u : Fin i → Fin d → C)
    (Φ Ψ : Fin d → MvPowerSeries (Fin d) C),
    (∀ a, _root_.ReciprocityTheory.PGsh.MvIsInt v (Φ a) ∧ constantCoeff (Φ a) = 0 ∧ _root_.ReciprocityTheory.PGsh.MvIsInt v (Ψ a) ∧
      constantCoeff (Ψ a) = 0) →
    (∀ a, subst Ψ (Φ a) = X a ∧ subst Φ (Ψ a) = X a) →
    ∀ (t : Fin d → MvPowerSeries (Fin i) C), (∀ a, constantCoeff (t a) = 0) →
    (∀ e, subst t (subst Φ (G.lg e)) = ∑ a, u a e • X a) →
    _root_.GlobalTheory.FGDepth.detDepth G u c = ⨅ f : {f : MvPowerSeries (Σ _ : Fin i, Fin d) C //
      _root_.ReciprocityTheory.PGsh.MvIsInt v f}, _root_.GlobalTheory.FGDepth.toE (v (_root_.GlobalTheory.FGDepth.derivAt0
        (_root_.GlobalTheory.FGDepth.detPow C i c) (subst (fun x : (Σ _ : Fin i, Fin d) =>
          subst (fun a : Fin i => (X ⟨x.1, a⟩ : MvPowerSeries (Σ _ : Fin i, Fin i) C)) (t x.2))
            f.1))) := by
  intro C _ _ v i d c G u Φ Ψ hΦΨ hinv t ht0 ht
  have hΦ : HasSubst Φ := hasSubst_of_constantCoeff_zero fun a => (hΦΨ a).2.1
  have hΨ : HasSubst Ψ := hasSubst_of_constantCoeff_zero fun a => (hΦΨ a).2.2.2
  have htS : HasSubst t := hasSubst_of_constantCoeff_zero ht0
  have hlg : HasSubst G.lg := hasSubst_of_constantCoeff_zero G.2
  have hex0 : ∀ a, constantCoeff (_root_.GlobalTheory.FGDepth.expOf G a) = 0 := (_root_.GlobalTheory.FGDepth.isExp_expOf G).1
  have hexS : HasSubst (_root_.GlobalTheory.FGDepth.expOf G) := hasSubst_of_constantCoeff_zero hex0
  have hLin0 : ∀ e, constantCoeff (∑ a, u a e • (X a : MvPowerSeries (Fin i) C)) = 0 := by
    intro e
    simp [map_sum]
  have hLinS : HasSubst fun e => ∑ a, u a e • (X a : MvPowerSeries (Fin i) C) :=
    hasSubst_of_constantCoeff_zero hLin0
  have hΦtS : HasSubst fun a => subst t (Φ a) :=
    hasSubst_of_constantCoeff_zero fun a => constantCoeff_subst_eq_zero htS ht0 (hΦΨ a).2.1

  have hΦt : ∀ a, subst t (Φ a) =
      subst (fun e => ∑ b, u b e • (X b : MvPowerSeries (Fin i) C))
        (_root_.GlobalTheory.FGDepth.expOf G a) := by
    intro a
    have h1 : (fun e => ∑ b, u b e • (X b : MvPowerSeries (Fin i) C)) =
        fun e => subst (fun a => subst t (Φ a)) (G.lg e) := by
      funext e
      rw [← subst_comp_subst_apply hΦ htS, ht]
    rw [h1, ← subst_comp_subst_apply hlg hΦtS, _root_.GlobalTheory.FGDepth.subst_lg_expOf, subst_X hΦtS]
  have ht_eq : ∀ e, t e = subst (fun e => ∑ b, u b e • (X b : MvPowerSeries (Fin i) C))
      (subst (_root_.GlobalTheory.FGDepth.expOf G) (Ψ e)) := by
    intro e
    rw [subst_comp_subst_apply hexS hLinS]
    calc t e = subst t (X e) := (subst_X htS e).symm
      _ = subst t (subst Φ (Ψ e)) := by rw [(hinv e).2]
      _ = subst (fun a => subst t (Φ a)) (Ψ e) := subst_comp_subst_apply hΦ htS _
      _ = _ := by simp_rw [hΦt]

  have hXb : ∀ b : Fin i, HasSubst fun a : Fin i =>
      (X ⟨b, a⟩ : MvPowerSeries (Σ _ : Fin i, Fin i) C) :=
    fun b => hasSubst_of_constantCoeff_zero fun a => constantCoeff_X _
  have hXd : ∀ b : Fin i, HasSubst fun a : Fin d =>
      (X ⟨b, a⟩ : MvPowerSeries (Σ _ : Fin i, Fin d) C) :=
    fun b => hasSubst_of_constantCoeff_zero fun a => constantCoeff_X _
  have hLinB0 : ∀ (b : Fin i) (e : Fin d),
      constantCoeff (∑ a, u a e • (X ⟨b, a⟩ : MvPowerSeries (Σ _ : Fin i, Fin i) C)) = 0 := by
    intro b e
    simp [map_sum]
  have hLinBS : ∀ b : Fin i, HasSubst fun e =>
      ∑ a, u a e • (X ⟨b, a⟩ : MvPowerSeries (Σ _ : Fin i, Fin i) C) :=
    fun b => hasSubst_of_constantCoeff_zero (hLinB0 b)
  have hE0 : ∀ x, constantCoeff
      (_root_.GlobalTheory.FGDepth.expAlong (fun _ : Fin i => G) (fun _ : Fin i => u) x) = 0 :=
    fun x => constantCoeff_subst_eq_zero (hLinBS x.1) (hLinB0 x.1) (hex0 x.2)
  have hES : HasSubst
      (_root_.GlobalTheory.FGDepth.expAlong (fun _ : Fin i => G) (fun _ : Fin i => u)) :=
    hasSubst_of_constantCoeff_zero hE0
  have hΨ0 : ∀ x : (Σ _ : Fin i, Fin d), constantCoeff
      (subst (fun a : Fin d => (X ⟨x.1, a⟩ : MvPowerSeries (Σ _ : Fin i, Fin d) C)) (Ψ x.2)) = 0 :=
    fun x => constantCoeff_subst_eq_zero (hXd x.1) (fun a => constantCoeff_X _) (hΦΨ x.2).2.2.2
  have hΨS : HasSubst fun x : (Σ _ : Fin i, Fin d) =>
      subst (fun a : Fin d => (X ⟨x.1, a⟩ : MvPowerSeries (Σ _ : Fin i, Fin d) C)) (Ψ x.2) :=
    hasSubst_of_constantCoeff_zero hΨ0
  have hΦ0 : ∀ x : (Σ _ : Fin i, Fin d), constantCoeff
      (subst (fun a : Fin d => (X ⟨x.1, a⟩ : MvPowerSeries (Σ _ : Fin i, Fin d) C)) (Φ x.2)) = 0 :=
    fun x => constantCoeff_subst_eq_zero (hXd x.1) (fun a => constantCoeff_X _) (hΦΨ x.2).2.1
  have hΦS : HasSubst fun x : (Σ _ : Fin i, Fin d) =>
      subst (fun a : Fin d => (X ⟨x.1, a⟩ : MvPowerSeries (Σ _ : Fin i, Fin d) C)) (Φ x.2) :=
    hasSubst_of_constantCoeff_zero hΦ0

  have key : ∀ x : (Σ _ : Fin i, Fin d),
      subst (fun a : Fin i => (X ⟨x.1, a⟩ : MvPowerSeries (Σ _ : Fin i, Fin i) C)) (t x.2) =
      subst (_root_.GlobalTheory.FGDepth.expAlong (fun _ : Fin i => G) (fun _ : Fin i => u))
        (subst (fun a : Fin d => (X ⟨x.1, a⟩ : MvPowerSeries (Σ _ : Fin i, Fin d) C))
          (Ψ x.2)) := by
    rintro ⟨b, e⟩
    have hlin : (fun e' => subst (fun a : Fin i =>
        (X ⟨b, a⟩ : MvPowerSeries (Σ _ : Fin i, Fin i) C))
          (∑ a, u a e' • (X a : MvPowerSeries (Fin i) C))) =
        fun e' => ∑ a, u a e' • (X ⟨b, a⟩ : MvPowerSeries (Σ _ : Fin i, Fin i) C) := by
      funext e'
      exact subst_sum_smul_X' (hXb b) (fun a => u a e') id
    rw [ht_eq e, subst_comp_subst_apply hLinS (hXb b), hlin,
      subst_comp_subst_apply hexS (hLinBS b), subst_comp_subst_apply (hXd b) hES]
    congr 1
    funext a
    rw [subst_X hES]
    rfl

  have hround : (fun x : (Σ _ : Fin i, Fin d) => subst
      (fun x : (Σ _ : Fin i, Fin d) =>
        subst (fun a : Fin d => (X ⟨x.1, a⟩ : MvPowerSeries (Σ _ : Fin i, Fin d) C)) (Ψ x.2))
      (subst (fun a : Fin d => (X ⟨x.1, a⟩ : MvPowerSeries (Σ _ : Fin i, Fin d) C)) (Φ x.2))) =
      X := by
    funext x
    rw [subst_comp_subst_apply (hXd x.1) hΨS]
    simp_rw [subst_X hΨS]
    rw [← subst_comp_subst_apply hΨ (hXd x.1), (hinv x.2).1, subst_X (hXd x.1)]
  unfold _root_.GlobalTheory.FGDepth.detDepth _root_.GlobalTheory.FGDepth.depth
  simp_rw [key]
  apply le_antisymm
  · refine le_iInf fun f => ?_
    rw [← subst_comp_subst_apply hΨS hES]
    exact iInf_le_of_le ⟨_, _root_.ReciprocityTheory.ChartRestriction.G.Sh.PTb.mvIsInt_subst v f.2
      (fun x => _root_.ReciprocityTheory.ChartRestriction.G.Sh.PTb.mvIsInt_subst v (hΦΨ x.2).2.2.1 (fun a => mvIsInt_X_divisor v _) (fun a => constantCoeff_X _))
      hΨ0⟩ le_rfl
  · refine le_iInf fun f => ?_
    refine iInf_le_of_le ⟨_, _root_.ReciprocityTheory.ChartRestriction.G.Sh.PTb.mvIsInt_subst v f.2
      (fun x => _root_.ReciprocityTheory.ChartRestriction.G.Sh.PTb.mvIsInt_subst v (hΦΨ x.2).1 (fun a => mvIsInt_X_divisor v _) (fun a => constantCoeff_X _))
      hΦ0⟩ ?_
    rw [← subst_comp_subst_apply hΨS hES, subst_comp_subst_apply hΦS hΨS, hround, subst_self]
    rfl

end

end GlobalTheory.FGDepth.Coord
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EnlargeBaseSeparablePointIntegralClosureStatement
section
open IsLocalRing Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.enlarge_base_separable_point_integralClosure : ∀ (T O : Type) [CommRing T] [IsDomain T] [IsLocalRing T] [CommRing O] [IsLocalRing O] [Algebra T O]
    [Algebra (Polynomial T) O] [IsScalarTower T (Polynomial T) O], GlobalTheory.LocAcyc.AbsIntClosed T →
    ∀ (P : Ideal (Polynomial T)) [P.IsPrime] (φ : Localization.AtPrime P →+* O),
    φ.comp (algebraMap (Polynomial T) _) = algebraMap (Polynomial T) O →
    GlobalTheory.IndefiniteRowSideFullHecke.ProjectiveSpaceOverSpec.IsStrictHenselisation φ → P = GlobalTheory.KeyOriginCut.originIdeal T →
    ∀ (q : ℕ), 0 < q → IsUnit (q : T) →
    ∀ (A : Type) [CommRing A] [IsDomain A] [IsLocalRing A] [IsNoetherianRing A] [IsIntegrallyClosed A]
      [Algebra.EssFiniteType ℤ A] (i : A →+* T)
      (EA : Type) [CommRing EA] [Algebra (Polynomial A) EA] [Algebra A EA]
      [IsScalarTower A (Polynomial A) EA] [Algebra.Etale (Polynomial A) EA]
      (QA : Ideal EA) [QA.IsPrime] (jA : Localization.AtPrime QA →+* O)
      (ψA : GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA) →+* GlobalTheory.LocAcyc.GenFib T O)
      (DA : Type) [CommRing DA] [Algebra (GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA)) DA]
      (actA : Multiplicative (ZMod q) →* (DA ≃ₐ[GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA)] DA)),
    GlobalTheory.KeyOriginEnlarge.Fits T O q A i EA QA jA ψA DA actA →
    ∀ ρ : Localization.AtPrime QA →+* A, GlobalTheory.KeyOriginEnlarge.Retracts T O A i EA QA jA ρ →
    ∃ (A' : Type) (_ : CommRing A') (_ : IsDomain A') (_ : IsLocalRing A') (_ : IsNoetherianRing A')
      (_ : IsIntegrallyClosed A') (_ : Algebra.EssFiniteType ℤ A') (i' : A' →+* T)
      (EA' : Type) (_ : CommRing EA') (_ : Algebra (Polynomial A') EA') (_ : Algebra A' EA')
      (_ : IsScalarTower A' (Polynomial A') EA') (_ : Algebra.Etale (Polynomial A') EA')
      (QA' : Ideal EA') (_ : QA'.IsPrime) (jA' : Localization.AtPrime QA' →+* O)
      (ψA' : GlobalTheory.LocAcyc.GenFib A' (Localization.AtPrime QA') →+* GlobalTheory.LocAcyc.GenFib T O)
      (DA' : Type) (_ : CommRing DA') (_ : Algebra (GlobalTheory.LocAcyc.GenFib A' (Localization.AtPrime QA')) DA')
      (actA' : Multiplicative (ZMod q) →* (DA' ≃ₐ[GlobalTheory.LocAcyc.GenFib A' (Localization.AtPrime QA')] DA')),
      GlobalTheory.KeyOriginEnlarge.Fits T O q A' i' EA' QA' jA' ψA' DA' actA' ∧
      (∃ ρ' : Localization.AtPrime QA' →+* A',
        GlobalTheory.KeyOriginEnlarge.Retracts T O A' i' EA' QA' jA' ρ' ∧ GlobalTheory.KeyOriginEnlarge.PointAtZero A' (Localization.AtPrime QA') DA' ρ') ∧
      ∃ (β : GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA) →+* GlobalTheory.LocAcyc.GenFib A' (Localization.AtPrime QA')) (h : DA →+* DA'),
        ψA'.comp β = ψA ∧
        h.comp (algebraMap (GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA)) DA) = (algebraMap (GlobalTheory.LocAcyc.GenFib A' (Localization.AtPrime QA')) DA').comp β := by
  first | (exact @GlobalTheory.KeyOriginEnlargePoint.enlarge_point) | (exact GlobalTheory.KeyOriginEnlargePoint.enlarge_point) | (intros; apply GlobalTheory.KeyOriginEnlargePoint.enlarge_point  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleSheafComplexQuasiIsoIffSections
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

noncomputable section
namespace GlobalTheory.EtC.QisSec

variable {R : Type} [CommRing R]

abbrev secF (U : Scheme.{0}) : Shv R ⥤ ModuleCat.{1} (ULift.{1} R) :=
  sheafToPresheaf _ _ ⋙ (evaluation _ _).obj (op U)

theorem loc_mono {U : Scheme.{0}} {P Q : ∀ V : Scheme.{0}, (V ⟶ U) → Prop} (h : Loc U P)
    (hPQ : ∀ V g, P V g → Q V g) : Loc U Q := GlobalTheory.T.etaleLocal_property_calculus_rules.2.1 U P Q h hPQ

section Cone
variable {K L : Cx R} (f : K ⟶ L) {U : Scheme.{0}}

end Cone

section Main
variable {K L : Cx R} (f : K ⟶ L)

end Main

end GlobalTheory.EtC.QisSec

namespace GlobalTheory.EtC

end GlobalTheory.EtC
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAlexanderWhitneyDiagonalSwapHomotopyStatement
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_alexanderWhitneyDiagonal_swap_homotopy : ∃ h : ∀ N, Pr N →₀ ℤ, (∀ N, Pr.Deg (N + 1) (h N)) ∧ Pr.d 0 (h 0) = Pr.aw 0 - Pr.wa 0 ∧ ∀ N, Pr.d (N + 1) (h (N + 1)) + Pr.bd (h N) = Pr.aw (N + 1) - Pr.wa (N + 1) := by
  first | exact @GlobalTheory.EtC.pr_aw_wa_homotopy | exact GlobalTheory.EtC.pr_aw_wa_homotopy | (intros; apply GlobalTheory.EtC.pr_aw_wa_homotopy <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCochainMapOfFibreCocyclePairingStatement
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_cochain_map_of_fibre_cocycle_pairing : ∀ (q N : ℕ) (i₁ i₂ i : ℤ) (h : i₁ + i₂ = i) (d : ℕ) (z : Cocycle ((chains (ZMod q)).obj (fibQ q N)) (res (ZMod q) (tw q i₂)) (2 * (d : ℤ))), ∃ ψ : Cocycle (res (ZMod q) (tw q i₁)) (Jcx (ZMod q) q N (res (ZMod q) (tw q i))) (2 * (d : ℤ)), ∀ (m w : ℤ) (hw : m + 2 * (d : ℤ) = w) (U : Scheme.{0}) (a : Sec ((res (ZMod q) (tw q i₁)).X m) U), ∃ c : Cochain ((chains (ZMod q)).obj (sch.obj U ⨯ fibQ q N)) (res (ZMod q) (tw q i)) w, Sec.map (ψ.1.v m w hw) a = Jsec c ∧ ∀ (k : ℕ) (s : ℤ) (hs : -(k : ℤ) + w = s) (V : Scheme.{0}) (y : Sx (sch.obj U ⨯ fibQ q N) k V), ev c k s hs V y = twCast h ((twPair q i₁ i₂).mul V m (-(k : ℤ) + 2 * (d : ℤ)) s (by omega) (Sec.res (Sx.map (prod.fst : sch.obj U ⨯ fibQ q N ⟶ _) y : V ⟶ U) a) (ev z.1 k (-(k : ℤ) + 2 * (d : ℤ)) rfl V (Sx.map prod.snd y))) := by
  first | (exact @GlobalTheory.EtC.PsiModel.psi_exists) | (exact GlobalTheory.EtC.PsiModel.psi_exists) | (intros; apply GlobalTheory.EtC.PsiModel.psi_exists  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCocycleLiftingLineBundleTransitionUnitsStatement
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC GlobalTheory.EtC.KumPic
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_cocycle_lifting_lineBundle_transition_units : ∀ (q : ℕ) (C : Shv ℤ) (qb : C ⟶ Gm) (E : Spc) (L : E ⟶ ofCat (glCat 1)), Inv q E → (∀ U : Scheme.{0}, IsUnit (q : Γ(U, ⊤)) → Function.Bijective (Sec.map qb (U := U))) → ∃ a : Cocycle ((chains ℤ).obj E) (sgl C) 1, ∀ (U : Scheme.{0}) (x : Sx E 1 U), ∃ c : Sec C U, Sec.map qb c = unitSec (lineUnit L x) ∧ ev a.1 1 0 (by simp) U x = Sec.map (sglι C) c := by
  first | exact @GlobalTheory.EtC.KumPic.lift_cocycle | exact GlobalTheory.EtC.KumPic.lift_cocycle | (intros; apply GlobalTheory.EtC.KumPic.lift_cocycle <;> assumption)
end

