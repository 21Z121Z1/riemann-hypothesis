import Mathlib
import Development.AbelianVarietyTheory.Definitions.CMLattices.LamLetters
import Development.AbelianVarietyTheory.Definitions.CMLattices.ExistsIsThetaDegOfIsLocalModel
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0022
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0021
import Development.AbelianVarietyTheory.Definitions.CMLattices.IsDiffOf
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0024
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.WeilIsGrpPullbackOfCommute
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.Bundle0017
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0021
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import Formalism.LocalToGlobal.ProjectiveLattices.RosatiLatticeNorms.LamPtClauses
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0011
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0013

-- bundled from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.EqOfLamEq
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.LamCM
open scoped CategoryTheory.Obj ComplexOrder
open GlobalTheory GlobalTheory.CM GlobalTheory.LamF

noncomputable section

namespace GlobalTheory.CM.PairingInj

open GlobalTheory.KerPow GlobalTheory.CM.PairingIso

theorem eq_one_of_gen_cubeLB {S : Scheme.{0}} {A : Over S} [GrpObj A] [IsCommMonObj A]
    {L : LB A.left} (hL : L.IsLB) (hK : Out.KTriv A L) {T : Over S} (x : T ⟶ A)
    (g₁ : ∃ t : LB.Gen (cubeLB A ![fst T A ≫ x, snd T A] L), t.IsGen) : x = 1 := by
  have g₂ : HasGen L _ _ := g₁
  have g₃ : LocGen L (fst T A).left
      (fun I : ULift.{0} (Finset (Fin 2)) => (psum A ![fst T A ≫ x, snd T A] I.down).left)
      (fun I => (-1) ^ (2 - I.down.card)) := fun _ => ⟨⊤, trivial, g₂.pull _ fun _ => rfl⟩
  have b₁ := locGen_base hL (fst T A).left x.left (b := (fst T A ≫ x).left) rfl
  have b₀ := locGen_base hL (fst T A).left (1 : T ⟶ A).left (b := (1 : T ⊗ A ⟶ A).left)
    (congrArg (fun q : T ⊗ A ⟶ A => q.left) (MonObj.comp_one (fst T A) : fst T A ≫ (1 : T ⟶ A) = 1).symm)
  have b := b₀.comb hL b₁ (φ'' := ![(1 : T ⊗ A ⟶ A).left, (fst T A ≫ x).left]) (ε'' := ![1, -1])
    fun U _ k => by simp [Fin.prod_univ_two]
  refine eq_one_of_locGen hK x (g₃.comb hL b fun U _ k => ?_)
  rw [PrimNorm.prod_square_id, Fin.prod_univ_two, Fin.prod_univ_two]
  show k ((fst T A ≫ x) * snd T A).left * (k (fst T A ≫ x).left)⁻¹ * (k (snd T A).left)⁻¹ * k (1 : T ⊗ A ⟶ A).left *
    (k (1 : T ⊗ A ⟶ A).left ^ (1 : ℤ) * k (fst T A ≫ x).left ^ (-1 : ℤ))⁻¹ =
    k ((fst T A ≫ x) * snd T A).left ^ (1 : ℤ) * k (snd T A).left ^ (-1 : ℤ)
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv, ofMul_zpow]
  module

theorem eq_of_lamEq : Out.Laws → ∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (P : Out.PolAV S) (X : Over S) (f g : X ⟶ P.A), LamEq P.L f (𝟙 P.A) P.L g (𝟙 P.A) → f = g := by
  intro hL S _ P X f g h
  have := P.isAb.comm
  obtain ⟨ρ, hρ⟩ := P.rigid
  obtain ⟨⟨c⟩, -⟩ := hL.cube S P ⟨P.L, ρ, P.isLB, hρ⟩ rfl
  have hT : ∃ t : LB.Gen (Theta P.A P.L), t.IsGen := ⟨c.t, c.isGen⟩
  have C := LamCalc.lamEq_calculus S X P.A P.A P.A P.A P.L P.L P.L P.isLB P.isLB P.isLB
  have h₁ : LamEq P.L (f * g⁻¹) (𝟙 P.A) P.L (g * g⁻¹) (𝟙 P.A) :=
    ((C f g⁻¹ (𝟙 _) (𝟙 _) g g⁻¹ (𝟙 _) (𝟙 _) g (𝟙 _)).2.2.1 hT hT h).1
      (C g⁻¹ g (𝟙 _) (𝟙 _) g g (𝟙 _) (𝟙 _) g (𝟙 _)).1
  rw [mul_inv_cancel] at h₁
  have h₂ := LamCalc.lbIso_of_lamEq h₁ (fst X P.A) (snd X P.A)
  rw [Category.comp_id, MonObj.comp_one] at h₂
  refine mul_inv_eq_one.1 (eq_one_of_gen_cubeLB P.isLB P.ktriv _ (exists_gen_of_lbIso
    (LamCalc.cubeLB_isLB P.isLB _) (LamCalc.cubeLB_isLB P.isLB _) h₂.symm ?_))
  exact hasGen_of_trivial P.isLB fun U _ k => (PrimNorm.prod_square_id _ _ k).trans (by simp [PrimNorm.diff₂])

end GlobalTheory.CM.PairingInj
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsCmAdjoinActionOfEquation
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CM

namespace GlobalTheory.CM

private theorem okAct_group_identity {A : Type*} [CommGroup A] (i w : A) (k m n m' n' : ℤ) :
    i ^ (m * m' - n * n' * k) * w ^ (m * n' + n * m' + n * n') =
      (i ^ m * w ^ n) ^ m' * (w ^ m * (w * i ^ (-k)) ^ n) ^ n' := by
  have h1 : m * m' - n * n' * k = m * m' + (-k) * n * n' := by ring
  rw [h1]
  simp only [mul_zpow, ← zpow_mul, zpow_add]
  ac_rfl

theorem exists_okAct_of_equation : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (W : G ⟶ G), IsMonHom W → (W ≫ W) * (𝟙 G) ^ ((1 + H.d) / 4) = W → ∃ a : OAct (OK H) G, a.act (wK H) = W ∧ ∀ m n : ℤ, a.act ((m : OK H) + (n : OK H) * wK H) = (𝟙 G) ^ m * W ^ n := by
  intro E _ _ _ H S G _ _ W hW hEq
  obtain ⟨-, hco, -, hsq, -⟩ := OK_isDedekindDomain_and_projective E H
  set k : ℕ := (1 + H.d) / 4 with hk
  choose c hc hcu using hco
  have hcoord : ∀ m n : ℤ, c ((m : OK H) + (n : OK H) * wK H) = (m, n) := fun m n =>
    (hcu _ (m, n) rfl).symm
  have hWW : W ≫ W = W * (𝟙 G) ^ (-(k : ℤ)) := by
    rw [zpow_neg, zpow_natCast, eq_mul_inv_iff_mul_eq]
    exact hEq
  let F : OK H → (G ⟶ G) := fun a => (𝟙 G) ^ (c a).1 * W ^ (c a).2
  have hF : ∀ m n : ℤ, F ((m : OK H) + (n : OK H) * wK H) = (𝟙 G) ^ m * W ^ n := fun m n => by
    simp only [F, hcoord]
  have hex : ∀ a : OK H, ∃ m n : ℤ, a = (m : OK H) + (n : OK H) * wK H := fun a => ⟨_, _, hc a⟩
  refine ⟨⟨F, fun a => ?_, ?_, fun a b => ?_, fun a b => ?_⟩, ?_, hF⟩
  · have h1 := Serre.isMonHom_zpow (𝟙 G) (c a).1
    have h2 := Serre.isMonHom_zpow W (c a).2
    exact Serre.isMonHom_mul _ _
  · have := hF 1 0
    simpa using this
  · obtain ⟨m, n, rfl⟩ := hex a
    obtain ⟨m', n', rfl⟩ := hex b
    have e : ((m : OK H) + (n : OK H) * wK H) * ((m' : OK H) + (n' : OK H) * wK H) =
        ((m * m' - n * n' * (k : ℤ) : ℤ) : OK H) + ((m * n' + n * m' + n * n' : ℤ) : OK H) * wK H := by
      push_cast
      linear_combination ((n : OK H) * (n' : OK H)) * hsq
    rw [e, hF, hF, hF]
    simp only [MonObj.comp_mul, GrpObj.comp_zpow, MonObj.mul_comp, GrpObj.zpow_comp, Category.comp_id,
      Category.id_comp, hWW]
    exact okAct_group_identity _ _ _ _ _ _ _
  · obtain ⟨m, n, rfl⟩ := hex a
    obtain ⟨m', n', rfl⟩ := hex b
    have e : ((m : OK H) + (n : OK H) * wK H) + ((m' : OK H) + (n' : OK H) * wK H) =
        ((m + m' : ℤ) : OK H) + ((n + n' : ℤ) : OK H) * wK H := by
      push_cast
      ring
    rw [e, hF, hF, hF, zpow_add, zpow_add]
    exact mul_mul_mul_comm _ _ _ _
  · have := hF 0 1
    simpa using this

end GlobalTheory.CM
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsEqSmulOfFinrankOne
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CM

namespace GlobalTheory.CM.LatData

section General

variable {R M : Type} [CommRing R] [IsDomain R] [AddCommGroup M] [Module R M] [Module.Finite R M]

theorem exists_span_smul_mem {r : ℕ} (hr : Module.finrank R M = r) :
    ∃ (v : Fin r → M) (c : R), c ≠ 0 ∧ ∀ m : M, ∃ s : Fin r → R, c • m = ∑ i, s i • v i := by
  obtain ⟨v, hv⟩ := exists_linearIndependent_of_le_finrank (R := R) (M := M) hr.ge
  have h1 := (Submodule.span R (Set.range v)).finrank_quotient_add_finrank
  rw [finrank_span_eq_card hv, Fintype.card_fin, hr] at h1
  have h2 : Module.IsTorsion R (M ⧸ Submodule.span R (Set.range v)) :=
    Module.finrank_eq_zero_iff_isTorsion.1 (by omega)
  obtain ⟨c, hc, hc0⟩ := Submodule.annihilator_top_inter_nonZeroDivisors h2
  refine ⟨v, c, nonZeroDivisors.ne_zero hc0, fun m => ?_⟩
  have h3 := Submodule.mem_annihilator.1 hc (Submodule.Quotient.mk m) trivial
  rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero,
    Submodule.mem_span_range_iff_exists_fun] at h3
  obtain ⟨s, hs⟩ := h3
  exact ⟨s, hs.symm⟩

theorem finrank_add_le_of_disjoint {A B : Submodule R M} (h : Disjoint A B) :
    Module.finrank R A + Module.finrank R B ≤ Module.finrank R M := by
  have h1 := A.finrank_quotient_add_finrank
  have h2 : Module.finrank R B ≤ Module.finrank R (M ⧸ A) := by
    refine LinearMap.finrank_le_finrank_of_injective (f := A.mkQ ∘ₗ B.subtype) ?_
    rw [injective_iff_map_eq_zero]
    intro b hb
    exact Subtype.ext (Submodule.disjoint_def.1 h _ ((Submodule.Quotient.mk_eq_zero A).1 hb) b.2)
  omega

end General

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem rt0_ne_neg (H : Host E) : H.rt0 ≠ -H.rt0 := fun h => by
  have h0 : H.rt0 = 0 := by linear_combination h / 2
  have := H.sqrt_neg_disc_sq
  rw [h0] at this
  exact H.d_prime.ne_zero (by simpa using this)

theorem exists_embedding (H : Host E) {ρ : ℂ} (hρ : ρ ^ 2 = -(H.d : ℂ)) : ∃ τ : E →+* ℂ, τ (H.rt : E) = ρ := by
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  have h1 : τ (H.rt : E) ^ 2 = -(H.d : ℂ) := by
    have := congrArg (fun x : 𝓞 E => τ (x : E)) H.rt_sq
    simpa using this
  rcases sq_eq_sq_iff_eq_or_eq_neg.1 (h1.trans hρ.symm) with h | h
  · exact ⟨τ, h⟩
  · refine ⟨(starRingEnd ℂ).comp τ, ?_⟩
    have hre : ρ.re = 0 := by
      have e1 := congrArg Complex.re hρ
      have e2 := congrArg Complex.im hρ
      have hd : (0 : ℝ) < H.d := Nat.cast_pos.2 H.d_prime.pos
      simp [pow_two] at e1 e2
      have e3 : ρ.re * ρ.im = 0 := by linarith
      rcases mul_eq_zero.1 e3 with e | e
      · exact e
      · rw [e] at e1
        nlinarith [mul_self_nonneg ρ.re]
    rw [RingHom.comp_apply, h]
    apply Complex.ext <;> simp [hre]

variable {D : Datum H} {g : ℕ} {ty : Fin g → (E →+* ℂ)} {Pe : D.La →+ (Fin g → ℂ)} (hP : IsPeriod D ty Pe)

theorem card_le_finrank_lat {ρ ρ' : ℂ} (hne : ρ ≠ ρ') {n : ℕ} (hn : 0 < n)
    (hs : ∀ a : D.La, n • a ∈ PureType.lat hP ρ ⊔ PureType.lat hP ρ') {τ : E →+* ℂ} (hτ : τ (H.rt : E) = ρ) :
    Nat.card {i // ty i = τ} ≤ Module.finrank (𝓞 E) (PureType.lat hP ρ) := by
  classical
  have := D.fin
  obtain ⟨v, c, hc, hv⟩ := exists_span_smul_mem (R := 𝓞 E) (M := PureType.lat hP ρ) rfl
  let pr : (Fin g → ℂ) →ₗ[ℂ] ({i // ty i = τ} → ℂ) := LinearMap.funLeft ℂ ℂ Subtype.val
  have hsm : ∀ (s : 𝓞 E) (a : D.La), pr (Pe (s • a)) = τ (s : E) • pr (Pe a) := fun s a => by
    funext i
    simp only [pr, LinearMap.funLeft_apply, Pi.smul_apply, smul_eq_mul]
    rw [hP.1, i.2]
  let W : Submodule ℂ ({i // ty i = τ} → ℂ) := Submodule.span ℂ (Set.range fun i => pr (Pe (v i)))
  have h1 : ∀ a : PureType.lat hP ρ, pr (Pe a) ∈ W := fun a => by
    obtain ⟨s, hs⟩ := hv a
    have hc' : τ (c : E) ≠ 0 := by simpa using hc
    rw [← W.smul_mem_iff hc', ← hsm, ← Submodule.coe_smul, hs, Submodule.coe_sum, map_sum, map_sum]
    refine W.sum_mem fun i _ => ?_
    rw [Submodule.coe_smul, hsm]
    exact W.smul_mem _ (Submodule.subset_span ⟨i, rfl⟩)
  have h2 : ∀ a : D.La, pr (Pe a) ∈ W := fun a => by
    obtain ⟨x, hx, y, hy, hxy⟩ := Submodule.mem_sup.1 (hs a)
    have hn' : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
    have hy0 : pr (Pe y) = 0 := funext fun i => hy i (by rw [i.2, hτ]; exact hne)
    rw [← W.smul_mem_iff hn', Nat.cast_smul_eq_nsmul, ← map_nsmul, ← map_nsmul, ← hxy, map_add, map_add, hy0,
      add_zero]
    exact h1 ⟨x, hx⟩
  have h3 : W = ⊤ := by
    rw [eq_top_iff]
    rintro w -
    obtain ⟨z, rfl⟩ := LinearMap.funLeft_surjective_of_injective ℂ ℂ
      (Subtype.val : {i // ty i = τ} → Fin g) Subtype.val_injective w
    have hz : z ∈ Submodule.span ℝ (Set.range Pe) := by rw [hP.2.2.2.1]; trivial
    have : Submodule.span ℝ (Set.range Pe) ≤ (W.comap pr).restrictScalars ℝ :=
      Submodule.span_le.2 (by rintro _ ⟨a, rfl⟩; exact h2 a)
    exact this hz
  have h4 := finrank_le_of_span_eq_top h3
  simpa [Nat.card_eq_fintype_card] using h4

theorem finrank_lat (ht : IsTypeFn H D.p D.q ty) {n : ℕ} (hn : 0 < n)
    (hs : ∀ a : D.La, n • a ∈ PureType.lat hP H.rt0 ⊔ PureType.lat hP (-H.rt0)) :
    Module.finrank (𝓞 E) (PureType.lat hP H.rt0) = D.p ∧
      Module.finrank (𝓞 E) (PureType.lat hP (-H.rt0)) = D.q := by
  have := D.fin
  have hne := rt0_ne_neg H
  obtain ⟨τ, hτ⟩ := exists_embedding H H.sqrt_neg_disc_sq
  obtain ⟨τ', hτ'⟩ := exists_embedding H (ρ := -H.rt0) (by rw [neg_sq, H.sqrt_neg_disc_sq])
  have h1 := card_le_finrank_lat hP hne hn hs hτ
  have h2 := card_le_finrank_lat hP hne.symm hn (fun a => sup_comm (PureType.lat hP H.rt0) _ ▸ hs a) hτ'
  rw [(ht τ).1 hτ] at h1
  rw [(ht τ').2 (by rw [hτ']; exact hne.symm)] at h2
  have h3 := finrank_add_le_of_disjoint (PureType.disjoint_lat hP hne)
  rw [D.rank] at h3
  omega

end GlobalTheory.CM.LatData

namespace GlobalTheory.CM

end GlobalTheory.CM
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsIsExpPush
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CM

namespace GlobalTheory.CM

theorem isHolTo_comp_hom {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] {X Y : Scheme.{0}} {B : Set V}
    {y : V → (Sp ℂ ⟶ X)} (h : IsHolTo B y) (φ : X ⟶ Y) : IsHolTo B (fun b => y b ≫ φ) := by
  intro U s
  have hfun : (fun b => valAt' (y b ≫ φ) U s) = fun b => valAt' (y b) (φ ⁻¹ᵁ U) ((φ.app U).hom s) :=
    funext fun b => (valAt'_comp _ φ U s).symm
  rw [hfun]
  exact h (φ ⁻¹ᵁ U) _

theorem exists_isExp_push : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type) [CommRing R] (σ : R →+* ℂ) (T : PAT H (Sp R)) (T' : PAT H (Sp ℂ)) (m : SABMap T'.t T.t (spMap σ)) (D : Datum H) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (Pe : D.La →+ (Fin g → ℂ)) (e' : (Fin g → ℂ) → (Over.mk (spMap (RingHom.id ℂ)) ⟶ T'.t.G)), IsExp T' (RingHom.id ℂ) D ty Pe e' → ∃ e : (Fin g → ℂ) → (Over.mk (spMap σ) ⟶ T.t.G), IsExp T σ D ty Pe e ∧ ∀ z, (e z).left = (e' z).left ≫ m.φ := by
  intro E _ _ _ H R _ σ T T' m D g ty Pe e' ⟨hP, hol, hadd, hon, hker, hlin, hw⟩
  have hL : LBIso T'.t.PP.L (T.t.PP.L.pull m.cm.F) := by
    obtain ⟨w, hw, -⟩ := m.lin
    exact ⟨w, hw⟩
  have hid : spMap (RingHom.id ℂ) = 𝟙 (Sp ℂ) := Spec.map_id _
  have hT : (Over.mk (spMap (RingHom.id ℂ))).hom ≫ spMap σ = spMap σ := by
    show spMap (RingHom.id ℂ) ≫ spMap σ = spMap σ
    rw [hid, Category.id_comp]
  obtain ⟨p, hp⟩ := LiePull.exists_pushEquiv m.cart (Over.mk (spMap (RingHom.id ℂ))) (spMap σ) hT.symm
  refine ⟨fun z => p (e' z), ⟨hP, ?_, fun z w => (congrArg p (hadd z w)).trans (map_mul p _ _),
    p.surjective.comp hon, fun z => ?_, fun a z => ?_, fun k a b c hk hc => ?_⟩, fun z => hp _⟩
  · have h : (fun z => (p (e' z)).left) = fun z => (e' z).left ≫ m.φ := funext fun z => hp _
    exact h ▸ isHolTo_comp_hom hol m.φ
  · exact (map_eq_one_iff p p.injective).trans (hker z)
  · apply Over.OverMorphism.ext
    beta_reduce
    rw [Over.comp_left, hp, hp, hlin, Over.comp_left, Category.assoc, Category.assoc]
    exact congrArg _ (m.act a)
  · have key : ∀ (y : Sp ℂ ⟶ Sp R) (_ : y = (Over.mk (spMap (RingHom.id ℂ))).hom ≫ spMap σ)
        (x₀ y₀ : Over.mk y ⟶ T.t.G) (x x' : Over.mk (spMap (RingHom.id ℂ)) ⟶ T'.t.G),
        x₀.left = x.left ≫ m.φ → y₀.left = x'.left ≫ m.φ →
        Out.WeilIs T'.t.G T'.t.PP.L k x x' (unitOn c) → Out.WeilIs T.t.G T.t.PP.L k x₀ y₀ (unitOn c) := by
      rintro y rfl x₀ y₀ x x' h₁ h₂ h₃
      exact (weilIs_grpPullback_of_comm _ _ _ _ _ m.φ _ _ T.t.PP.isLB T'.t.PP.isLB m.cart hL _ k x x' x₀ y₀ _
        h₁ h₂).1 h₃
    exact key _ hT.symm _ _ _ _ (hp _) (hp _) (hw k a b c hk hc)

end GlobalTheory.CM
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsIsPolFibreOfKeyPB
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.LamCM
open scoped CategoryTheory.Obj ComplexOrder
open GlobalTheory GlobalTheory.CM GlobalTheory.LamF

namespace GlobalTheory.KeyFibre

theorem eq_dualMapR_of_algebraMap {R R' : Type} [CommRing R] [CommRing R'] (f : R →+* R')
    (F : DualNumber R →+* DualNumber R') (h : ∀ a, F (algebraMap R _ a) = algebraMap R' _ (f a))
    (he : F DualNumber.eps = DualNumber.eps) : F = Chart.dualMapR f := by
  refine RingHom.ext fun x => ?_
  have e : x = algebraMap R _ x.fst + algebraMap R _ x.snd * DualNumber.eps := by
    ext <;> simp [TrivSqZeroExt.algebraMap_eq_inl]
  rw [e, map_add, map_mul, h, h, he]
  ext <;> simp [Chart.dualMapR, TrivSqZeroExt.algebraMap_eq_inl]

theorem exists_isPolFibre_of_keyPB : ∀ (R R' : Type) [CommRing R] [CommRing R'] (f : R →+* R') (x : KeyIn R) (x' : KeyIn R'), KeyPB x' x f → ∃ (φ : x'.P.A.left ⟶ x.P.A.left) (hg : x'.P.g = x.P.g), IsPolFibre f x.P x'.P φ ∧ ∀ i, IsVecOver f φ (x.v (i.cast hg)) (x'.v i) := by
  intro R R' _ _ f x x' h
  obtain ⟨φ, he, w, hg, F, hφ, hw, h1, h2, hF, hε, hv⟩ := h
  refine ⟨φ, hg, ⟨hg, hφ, LBIso.symm ⟨w, hw⟩⟩, fun i => ?_⟩
  have := hv i
  rw [eq_dualMapR_of_algebraMap f F hF hε] at this
  exact this

end GlobalTheory.KeyFibre
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsKroneckerCmLogPeriodEqConst
section
open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj GlobalTheory GlobalTheory.CM

namespace GlobalTheory.LamF

theorem exists_kronecker_logOm_re (E : Type) [Field E] [NumberField E] {d d' : ℕ} (h : d' = d) [Fact d.Prime]
    [NeZero d] (hd : d % 4 = 3) :
    ∃ (_ : NeZero d') (χ : DirichletCharacter ℂ d'), IsKroneckerChar χ ∧ (GlobalTheory.CM.logOm E χ).re =
      Real.eulerMascheroniConstant + Real.log (2 * Real.pi / rootDiscr E) -
        (deriv (DirichletCharacter.LFunction ((quadraticChar (ZMod d)).ringHomComp (Int.castRingHom ℂ))) 1 /
          DirichletCharacter.LFunction ((quadraticChar (ZMod d)).ringHomComp (Int.castRingHom ℂ)) 1).re := by
  subst h
  exact ⟨inferInstance, _, isKroneckerChar_quadraticChar hd, by
    rw [GlobalTheory.CM.logOm, Complex.sub_re, Complex.ofReal_re]⟩

theorem exists_kronecker_logOm_eq : ∀ (D : D7) (Q : Par D), Q.PinHost → ∀ large₂ : SizeData₂ D,
    ∃ (_ : NeZero Q.H.d) (χ : DirichletCharacter ℂ Q.H.d),
      IsKroneckerChar χ ∧ (GlobalTheory.CM.logOm D.host.E χ).re = large₂.logOm := by
  intro D Q hp large₂
  haveI : Fact D.host.d.Prime := ⟨D.host.hyp.2.1⟩
  haveI : NeZero D.host.d := ⟨D.host.hyp.2.1.ne_zero⟩
  have hd : D.host.d % 4 = 3 := by
    have := Q.H.d_mod
    rw [hp.1] at this
    omega
  obtain ⟨i, χ, hχ, e⟩ := exists_kronecker_logOm_re D.host.E hp.1 hd
  refine ⟨i, χ, hχ, e.trans ?_⟩
  have hv : 2 * Real.pi / rootDiscr D.host.E = Real.pi / D.host.v := by
    rw [Formalism.BasicNotions.Host.v, Formalism.BasicNotions.Host.rdE, rootDiscr_def, Int.cast_abs, one_div, div_div_eq_mul_div, mul_comm]
  rw [hv, SizeData₂.logOm, large₂.logDerivative_at_one_eq]
  rfl

end GlobalTheory.LamF
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsMonHomFactorOfFlatSurjective
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.LamCM
open scoped CategoryTheory.Obj ComplexOrder
open GlobalTheory GlobalTheory.CM GlobalTheory.LamF

namespace GlobalTheory

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain in
open scoped CategoryTheory.Obj ComplexOrder in

theorem _root_.GlobalTheory.exists_monHom_factor_of_flat_surjective : ∀ (S : Scheme.{0}) (G G' G'' : Over S) [GrpObj G] [GrpObj G'] [GrpObj G''] (Φ : G ⟶ G') (f : G ⟶ G''), IsMonHom Φ → IsMonHom f → Flat Φ.left → Surjective Φ.left → QuasiCompact Φ.left → (∀ (T : Over S) (x : T ⟶ G), x ≫ Φ = 1 → x ≫ f = 1) → (∃ ψ : G' ⟶ G'', IsMonHom ψ ∧ Φ ≫ ψ = f) ∧ Epi Φ := by
  intro S G G' G'' _ _ _ Φ f hΦ hf hflat hsurj hqc hker
  haveI := hΦ
  haveI := hf
  haveI : EffectiveEpi Φ := _root_.GlobalTheory.CosetQuotient.effectiveEpi_of_left Φ
  haveI : Flat (Φ ⊗ₘ Φ).left := _root_.GlobalTheory.CosetQuotient.flat_tensorHom Φ Φ
  haveI : Surjective (Φ ⊗ₘ Φ).left := _root_.GlobalTheory.CosetQuotient.surjective_tensorHom Φ Φ
  haveI : QuasiCompact (Φ ⊗ₘ Φ).left := _root_.GlobalTheory.CosetQuotient.quasiCompact_tensorHom Φ Φ
  haveI : EffectiveEpi (Φ ⊗ₘ Φ) := _root_.GlobalTheory.CosetQuotient.effectiveEpi_of_left _
  have hcompat : ∀ {Z : Over S} (g₁ g₂ : Z ⟶ G), g₁ ≫ Φ = g₂ ≫ Φ → g₁ ≫ f = g₂ ≫ f := by
    intro Z g₁ g₂ h
    have h1 : (g₁ / g₂) ≫ Φ = 1 := by
      rw [GrpObj.div_comp, h, div_self']
    have h2 := hker Z _ h1
    rwa [GrpObj.div_comp, div_eq_one] at h2
  refine ⟨⟨EffectiveEpi.desc Φ f hcompat, ⟨?_, ?_⟩, EffectiveEpi.fac Φ f hcompat⟩, inferInstance⟩
  · rw [← IsMonHom.one_hom (f := Φ), Category.assoc, EffectiveEpi.fac, IsMonHom.one_hom]
  · rw [← cancel_epi (Φ ⊗ₘ Φ), ← Category.assoc, ← IsMonHom.mul_hom (f := Φ), Category.assoc,
      EffectiveEpi.fac, IsMonHom.mul_hom, ← Category.assoc, tensorHom_comp_tensorHom, EffectiveEpi.fac]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsMulEquivPointsOfIsGrpPullback
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.LamCM
open scoped CategoryTheory.Obj ComplexOrder
open GlobalTheory GlobalTheory.CM GlobalTheory.LamF

namespace GlobalTheory.LamF

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain in
open scoped CategoryTheory.Obj ComplexOrder in

theorem _root_.GlobalTheory.LamF.exists_mulEquiv_points_of_isGrpPullback :
    ∀ (S S' : Scheme.{0}) (f : S' ⟶ S) (G : Over S) (G' : Over S') [GrpObj G] [GrpObj G'] (φ : G'.left ⟶ G.left), _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsGrpPullback G' G f φ → ∀ T : Over S', ∃ Φ : (T ⟶ G') ≃* (Over.mk (T.hom ≫ f) ⟶ G), ∀ x, (Φ x).left = x.left ≫ φ := by
  intro S S' f G G' _ _ φ hφ T
  obtain ⟨hpb, hmul⟩ := hφ
  let toFun : (T ⟶ G') → (Over.mk (T.hom ≫ f) ⟶ G) := fun x =>
    Over.homMk (x.left ≫ φ) (by
      show (x.left ≫ φ) ≫ G.hom = T.hom ≫ f
      rw [Category.assoc, hpb.w, ← Category.assoc, Over.w])
  let invFun : (Over.mk (T.hom ≫ f) ⟶ G) → (T ⟶ G') := fun y =>
    Over.homMk (hpb.lift y.left T.hom (by simpa using Over.w y)) (hpb.lift_snd _ _ _)
  have hto : ∀ x, (toFun x).left = x.left ≫ φ := fun x => rfl
  refine ⟨{ toFun := toFun, invFun := invFun, left_inv := ?_, right_inv := ?_, map_mul' := ?_ }, hto⟩
  · intro x
    ext1
    refine hpb.hom_ext ?_ ?_
    · exact hpb.lift_fst _ _ _
    · exact (hpb.lift_snd _ _ _).trans (Over.w x).symm
  · intro y
    ext1
    exact hpb.lift_fst _ _ _
  · intro x y
    ext1
    exact (hmul T x y (toFun x) (toFun y) (hto x) (hto y)).symm

end GlobalTheory.LamF
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsOActExtendDedekind
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CM

namespace GlobalTheory.CM

theorem exists_oAct_extend_dedekind : (∀ (T K : Type) [CommRing T] [IsDomain T] [IsDiscreteValuationRing T] [Field K] [Algebra T K] [IsFractionRing T K] (G G' : Over (Sp T)) [GrpObj G] [GrpObj G'], IsSemiAbelian G → IsSemiAbelian G' → ∀ f : (Over.pullback (spMap (algebraMap T K))).obj G ⟶ (Over.pullback (spMap (algebraMap T K))).obj G', IsMonHom f → ∃! F : G ⟶ G', IsMonHom F ∧ (Over.pullback (spMap (algebraMap T K))).map F = f) → ∀ (R K : Type) [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K] [IsFractionRing R K] (O : Type) [CommRing O] (G : Over (Sp R)) [GrpObj G] (G₀ : Over (Sp K)) [GrpObj G₀] (φ : G₀.left ⟶ G.left), IsAbelianScheme G → IsGrpPullback G₀ G (spMap (algebraMap R K)) φ → ∀ a₀ : OAct O G₀, ∃ a : OAct O G, ∀ c, (a₀.act c).left ≫ φ = φ ≫ (a.act c).left := by
  intro H R K _ _ _ _ _ O _ G _ G₀ _ φ hG hφ a₀
  have key := fun c => GlobalTheory.T.abelianScheme_hom_extends_dedekind_of_isGrpPullback_alt H R K G G G₀ G₀ φ φ hG hG hφ hφ (a₀.act c) (a₀.hom c)
  choose F hF hc hu using key
  refine ⟨⟨F, hF, ?_, ?_, ?_⟩, hc⟩
  · refine (hu 1 (𝟙 G) ?_).symm
    rw [a₀.one]
    simp
  · intro a b
    refine (hu (a * b) (F a ≫ F b) ?_).symm
    rw [a₀.mul, Over.comp_left, Over.comp_left, Category.assoc, hc b, ← Category.assoc, hc a, Category.assoc]
  · intro a b
    refine (hu (a + b) (F a * F b) ?_).symm
    let ψ : Over.mk (G₀.hom ≫ spMap (algebraMap R K)) ⟶ G := Over.homMk φ hφ.1.w
    have h := hφ.2 G₀ (a₀.act a) (a₀.act b) (ψ ≫ F a) (ψ ≫ F b) (hc a).symm (hc b).symm
    rw [a₀.add, ← h, ← MonObj.comp_mul]
    rfl

end GlobalTheory.CM
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsPolarisedAbelianSchemePowerStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CM

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_polarisedAbelianScheme_power : ∀ (R : Type) [CommRing R] (P : Out.PolAV (Sp R)) (n : ℕ), ∃ (Q : Out.PolAV (Sp R)) (_ : Out.IsPowGrp Q.A P.A n), Q.g = n * P.g := by
  first | exact @GlobalTheory.CM.exists_polAV_isPowGrp | exact GlobalTheory.CM.exists_polAV_isPowGrp | (intros; apply GlobalTheory.CM.exists_polAV_isPowGrp <;> assumption)
end

