import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0049
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnitLemmaGroup
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1240
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0045
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1234
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0180
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1235
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0046
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsLocModelIsPrimeOf
import Development.AbelianVarietyTheory.Definitions.Divisors.NotDominatesTopPlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1180
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1196
import Development.AbelianVarietyTheory.Definitions.Divisors.SmallFam
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0014
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0016
import Development.AbelianVarietyTheory.Definitions.Divisors.IsNefHermitianTwistingSheaf
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NefFibOfIsGenerated
import Development.AbelianVarietyTheory.Definitions.Divisors.IsDominantOfSection

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCompactClosureZpowersLeftMulGLIffIntegral
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.TwOrbLat

section Top

variable {E : Type} [Field E] [NumberField E] {w : Pl E} {a : ℕ}

theorem isCompact_boundedGL (R : ℝ) :
    IsCompact {g : GLw a w | ∀ i j, ‖g.val i j‖ ≤ R ∧ ‖(g⁻¹).val i j‖ ≤ R} := by
  haveI := GlobalTheory.AdelicUnitaryTop.properSpace_adicCompletion E w
  have hK : IsCompact {A : Matrix (Fin a) (Fin a) (w.adicCompletion E) | ∀ i j, ‖A i j‖ ≤ R} := by
    have h : IsCompact (Set.pi Set.univ fun _ : Fin a => Set.pi Set.univ fun _ : Fin a =>
        Metric.closedBall (0 : w.adicCompletion E) R) :=
      isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_closedBall _ _
    have e : {A : Matrix (Fin a) (Fin a) (w.adicCompletion E) | ∀ i j, ‖A i j‖ ≤ R} =
        (Set.pi Set.univ fun _ : Fin a => Set.pi Set.univ fun _ : Fin a =>
          Metric.closedBall (0 : w.adicCompletion E) R) :=
      Set.ext fun A => ⟨fun hA i _ j _ => by simpa using hA i j, fun hA i j => by simpa using hA i trivial j trivial⟩
    rw [e]
    exact h
  have h := (Units.isClosedEmbedding_embedProduct (α := Matrix (Fin a) (Fin a) (w.adicCompletion E))).isCompact_preimage
    (hK.prod (hK.image MulOpposite.continuous_op))
  convert h using 1
  ext g
  simp only [Set.mem_setOf_eq, Set.mem_preimage, Units.embedProduct_apply, Set.mem_prod,
    (MulOpposite.op_injective).mem_set_image]
  exact ⟨fun hg => ⟨fun i j => (hg i j).1, fun i j => (hg i j).2⟩, fun hg i j => ⟨hg.1 i j, hg.2 i j⟩⟩

theorem isCompact_closure_zpowers_iff (g : GLw a w) :
    IsCompact (closure (Subgroup.zpowers g : Set (GLw a w))) ↔
      ∃ R : ℝ, ∀ n : ℤ, ∀ i j, ‖(g ^ n).val i j‖ ≤ R := by
  constructor
  · intro hc
    have hb : ∀ i j : Fin a, ∃ C : ℝ, ∀ h ∈ closure (Subgroup.zpowers g : Set (GLw a w)), ‖h.val i j‖ ≤ C :=
      fun i j => hc.exists_bound_of_continuousOn (f := fun h : GLw a w => h.val i j)
        ((Units.continuous_val (M := Matrix (Fin a) (Fin a) (w.adicCompletion E))).matrix_elem i j).continuousOn
    choose C hC using hb
    refine ⟨∑ i, ∑ j, max (C i j) 0, fun n i j => ?_⟩
    have h1 := hC i j (g ^ n) (subset_closure (Subgroup.zpow_mem_zpowers g n))
    calc _ ≤ max (C i j) 0 := h1.trans (le_max_left _ _)
      _ ≤ ∑ j', max (C i j') 0 :=
        Finset.single_le_sum (f := fun j' => max (C i j') 0) (fun _ _ => le_max_right _ _) (Finset.mem_univ j)
      _ ≤ _ := Finset.single_le_sum (f := fun i' => ∑ j', max (C i' j') 0)
        (fun _ _ => Finset.sum_nonneg fun _ _ => le_max_right _ _) (Finset.mem_univ i)
  · rintro ⟨R, hR⟩
    refine (isCompact_boundedGL R).closure_of_subset ?_
    intro h hh
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hh
    refine fun i j => ⟨hR n i j, ?_⟩
    rw [← _root_.zpow_neg]
    exact hR (-n) i j

end Top

section Alg

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {w : Pl E} {K : GlobalTheory.UnitLemma.UQ}
  (e : K.E ≃+* w.adicCompletion E) {a : ℕ} {B : GlobalTheory.UnitLemma.InvAlg K} (b : Module.Basis (Fin a) K.E B.A)

omit [IsCMField E] in
theorem norm_le_one_iff_mem (he : ∀ x, x ∈ (algebraMap K.O K.E).range ↔ Valued.v (e x) ≤ 1) (x : K.E) :
    ‖e x‖ ≤ 1 ↔ x ∈ (algebraMap K.O K.E).range := by
  rw [he]
  exact Valued.toNormedField.norm_le_one_iff

omit [IsCMField E] in

theorem exists_norm_ge (he : ∀ x, x ∈ (algebraMap K.O K.E).range ↔ Valued.v (e x) ≤ 1) (R : ℝ) :
    ∃ c : K.E, c ≠ 0 ∧ R ≤ ‖e c‖ := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible K.O
  have hπ0 : algebraMap K.O K.E π ≠ 0 := by
    rw [Ne, map_eq_zero_iff _ (IsFractionRing.injective K.O K.E)]
    exact hπ.ne_zero
  have hn : ¬ (algebraMap K.O K.E π)⁻¹ ∈ (algebraMap K.O K.E).range := by
    rintro ⟨o, ho⟩
    apply hπ.not_isUnit
    have h : π * o = 1 := IsFractionRing.injective K.O K.E (by rw [map_mul, ho, mul_inv_cancel₀ hπ0, map_one])
    exact isUnit_iff_exists_inv.2 ⟨o, h⟩
  have h1 : 1 < ‖e (algebraMap K.O K.E π)⁻¹‖ := by
    rw [← not_le, norm_le_one_iff_mem e he]
    exact hn
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt R h1
  refine ⟨((algebraMap K.O K.E π)⁻¹) ^ n, pow_ne_zero _ (inv_ne_zero hπ0), ?_⟩
  rw [map_pow, norm_pow]
  exact hn.le

omit [IsCMField E] in

theorem exists_fg_of_crd_le (he : ∀ x, x ∈ (algebraMap K.O K.E).range ↔ Valued.v (e x) ≤ 1) (R : ℝ) :
    ∃ M : Submodule K.O B.A, M.FG ∧ ∀ y, (∀ i, ‖crd e b y i‖ ≤ R) → y ∈ M := by
  obtain ⟨c, hc0, hc⟩ := exists_norm_ge e he R
  refine ⟨Submodule.span K.O (Set.range fun j => c • b j), Submodule.fg_span (Set.finite_range _), fun y hy => ?_⟩
  have hec : e c ≠ 0 := by rwa [Ne, map_eq_zero_iff _ e.injective]
  rw [← b.sum_repr y]
  refine Submodule.sum_mem _ fun j _ => ?_
  have hm : b.repr y j / c ∈ (algebraMap K.O K.E).range := by
    rw [← norm_le_one_iff_mem e he, map_div₀, norm_div, div_le_one (norm_pos_iff.2 hec)]
    exact (hy j).trans hc
  obtain ⟨o, ho⟩ := hm
  have : b.repr y j • b j = o • (c • b j) := by
    rw [← algebraMap_smul K.E o, smul_smul, ho, div_mul_cancel₀ _ hc0]
  rw [this]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)

theorem isIntegral_of_bounded (he : ∀ x, x ∈ (algebraMap K.O K.E).range ↔ Valued.v (e x) ≤ 1) (u : B.A)
    (R : ℝ) (hR : ∀ n : ℕ, ∀ i j, ‖mulHom e b (u ^ n) i j‖ ≤ R) : IsIntegral K.O u := by
  obtain ⟨M, hMfg, hM⟩ := exists_fg_of_crd_le e b he (∑ j, R * ‖crd e b 1 j‖)
  have hle : Subalgebra.toSubmodule (Algebra.adjoin K.O {u}) ≤ M := by
    rw [Algebra.adjoin_eq_span, Submodule.span_le, ← Submonoid.powers_eq_closure]
    rintro _ ⟨n, rfl⟩
    refine hM _ fun i => ?_
    have h1 : crd e b (u ^ n) = mulHom e b (u ^ n) *ᵥ crd e b 1 := by rw [← crd_mul, mul_one]
    rw [h1]
    simp only [Matrix.mulVec, dotProduct]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right (hR n i j) (norm_nonneg _)
  haveI : IsNoetherian K.O M := isNoetherian_of_fg_of_noetherian M hMfg
  haveI : IsNoetherian K.O (Subalgebra.toSubmodule (Algebra.adjoin K.O {u})) := isNoetherian_of_le hle
  exact isIntegral_of_submodule_noetherian _ this u (Algebra.self_mem_adjoin_singleton K.O u)

theorem bounded_of_fg (he : ∀ x, x ∈ (algebraMap K.O K.E).range ↔ Valued.v (e x) ≤ 1) (M : Submodule K.O B.A)
    (hM : M.FG) : ∃ R : ℝ, ∀ y ∈ M, ∀ i j, ‖mulHom e b y i j‖ ≤ R := by
  obtain ⟨S, rfl⟩ := hM
  refine ⟨∑ y ∈ S, ∑ i, ∑ j, ‖mulHom e b y i j‖, fun x hx i j => ?_⟩
  obtain ⟨f, -, rfl⟩ := Submodule.mem_span_finset.1 hx
  have hsum : mulHom e b (∑ y ∈ S, f y • y) i j = ∑ y ∈ S, e (algebraMap K.O K.E (f y)) * mulHom e b y i j := by
    rw [mulHom_apply]
    simp only [mulHom_apply, Finset.sum_mul, smul_mul_assoc]
    simp only [← algebraMap_smul K.E (f _), map_sum, map_smul, Finsupp.coe_finset_sum, Finset.sum_apply,
      Finsupp.smul_apply, smul_eq_mul, map_mul]
  rw [hsum]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun y _ => ?_)
  rw [norm_mul]
  have h1 : ‖e (algebraMap K.O K.E (f y))‖ ≤ 1 := (norm_le_one_iff_mem e he _).2 ⟨f y, rfl⟩
  calc _ ≤ 1 * ‖mulHom e b y i j‖ := mul_le_mul_of_nonneg_right h1 (norm_nonneg _)
    _ = ‖mulHom e b y i j‖ := one_mul _
    _ ≤ ∑ j', ‖mulHom e b y i j'‖ :=
      Finset.single_le_sum (f := fun j' => ‖mulHom e b y i j'‖) (fun _ _ => norm_nonneg _) (Finset.mem_univ j)
    _ ≤ ∑ i', ∑ j', ‖mulHom e b y i' j'‖ :=
      Finset.single_le_sum (f := fun i' => ∑ j', ‖mulHom e b y i' j'‖)
        (fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _) (Finset.mem_univ i)

end Alg

section Main

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {w : Pl E} {K : GlobalTheory.UnitLemma.UQ}
  (e : K.E ≃+* w.adicCompletion E) {a : ℕ} {B : GlobalTheory.UnitLemma.InvAlg K} (b : Module.Basis (Fin a) K.E B.A)

theorem mulGL_zpow_val (t : B.Aˣ) (n : ℤ) : ((mulGL e b t) ^ n).val = mulHom e b ((t ^ n : B.Aˣ) : B.A) := by
  rw [← map_zpow]
  rfl

theorem isCompact_closure_zpowers_mulGL_iff' (he : ∀ x, x ∈ (algebraMap K.O K.E).range ↔ Valued.v (e x) ≤ 1)
    (t : B.Aˣ) : IsCompact (closure (Subgroup.zpowers (mulGL e b t) : Set (GLw a w))) ↔
      t ∈ GlobalTheory.UnitLemma.intUnits K.O B.A := by
  rw [isCompact_closure_zpowers_iff]
  simp only [mulGL_zpow_val]
  constructor
  · rintro ⟨R, hR⟩
    refine ⟨isIntegral_of_bounded e b he _ R fun n i j => ?_, isIntegral_of_bounded e b he _ R fun n i j => ?_⟩
    · have := hR n i j
      rwa [zpow_natCast, Units.val_pow_eq_pow_val] at this
    · have := hR (-(n : ℤ)) i j
      rwa [_root_.zpow_neg, zpow_natCast, ← inv_pow, Units.val_pow_eq_pow_val] at this
  · rintro ⟨h1, h2⟩
    obtain ⟨R, hR⟩ := bounded_of_fg e b he _
      (fg_adjoin_of_finite (s := {(t : B.A), ((t⁻¹ : B.Aˣ) : B.A)}) (Set.toFinite _)
        (by rintro x (rfl | rfl); exacts [h1, h2]))
    refine ⟨R, fun n i j => hR _ ((Subalgebra.mem_toSubmodule _).2 ?_) i j⟩
    obtain ⟨k, rfl | rfl⟩ := Int.eq_nat_or_neg n
    · rw [zpow_natCast, Units.val_pow_eq_pow_val]
      exact Subalgebra.pow_mem _ (Algebra.subset_adjoin (Set.mem_insert _ _)) k
    · rw [_root_.zpow_neg, zpow_natCast, ← inv_pow, Units.val_pow_eq_pow_val]
      exact Subalgebra.pow_mem _ (Algebra.subset_adjoin (Set.mem_insert_of_mem _ (Set.mem_singleton _))) k

end Main

theorem isCompact_closure_zpowers_mulGL_iff : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (w : Pl E) (K : GlobalTheory.UnitLemma.UQ) (e : K.E ≃+* w.adicCompletion E), (∀ x, x ∈ (algebraMap K.O K.E).range ↔ Valued.v (e x) ≤ 1) → ∀ (a : ℕ) (B : GlobalTheory.UnitLemma.InvAlg K) (b : Module.Basis (Fin a) K.E B.A) (t : B.Aˣ), IsCompact (closure (Subgroup.zpowers (GlobalTheory.TwOrbLat.mulGL e b t) : Set (GLw a w))) ↔ t ∈ GlobalTheory.UnitLemma.intUnits K.O B.A :=
  fun _ _ _ _ _ _ e he _ _ b t => isCompact_closure_zpowers_mulGL_iff' e b he t

end GlobalTheory.TwOrbLat
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsGoodGlRepPiTensorActionAtFactorAndCommute
section
noncomputable section

open scoped TensorProduct
open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.RealLift GlobalTheory.HoweR

namespace GlobalTheory.HoweR.FactorAct

variable {T : Type} [Fintype T] [DecidableEq T] {V : T → Type} [∀ w, AddCommGroup (V w)] [∀ w, Module ℂ (V w)]

theorem atPl_tprod' (w : T) (L : Module.End ℂ (V w)) (f : ∀ i, V i) :
    atPl w L (PiTensorProduct.tprod ℂ f) = PiTensorProduct.tprod ℂ (Function.update f w (L (f w))) := by
  rw [atPl, PiTensorProduct.map_tprod]
  congr 1
  funext i
  by_cases h : i = w
  · subst h; simp
  · simp [Function.update_of_ne h]

theorem atPl_mul' (w : T) (L L' : Module.End ℂ (V w)) : atPl w (L * L') = atPl w L * atPl w L' := by
  refine PiTensorProduct.ext (MultilinearMap.ext fun f => ?_)
  simp [atPl_tprod']

theorem atPl_comm' {w w' : T} (h : w ≠ w') (L : Module.End ℂ (V w)) (L' : Module.End ℂ (V w')) (x : ⨂[ℂ] i, V i) :
    atPl w L (atPl w' L' x) = atPl w' L' (atPl w L x) := by
  induction x using PiTensorProduct.induction_on with
  | smul_tprod r f =>
    simp only [map_smul, atPl_tprod', Function.update_of_ne h, Function.update_of_ne h.symm]
    rw [Function.update_comm h]
  | add x y hx hy => simp only [map_add, hx, hy]

def intersection_update_fsHerm_neg_one (f : ∀ i, V i) (w : T) : V w →ₗ[ℂ] ⨂[ℂ] i, V i := (PiTensorProduct.tprod ℂ (s := V)).toLinearMap f w

theorem position_apply (f : ∀ i, V i) (w : T) (v : V w) : intersection_update_fsHerm_neg_one f w v = PiTensorProduct.tprod ℂ (Function.update f w v) := rfl

theorem position_self (f : ∀ i, V i) (w : T) : intersection_update_fsHerm_neg_one f w (f w) = PiTensorProduct.tprod ℂ f := by
  rw [position_apply, Function.update_eq_self]

theorem atPl_tprod_update (f : ∀ i, V i) (w : T) (L : Module.End ℂ (V w)) (v : V w) :
    atPl w L (intersection_update_fsHerm_neg_one f w v) = intersection_update_fsHerm_neg_one f w (L v) := by
  simp [position_apply, atPl_tprod']

variable {p q : ℕ}

theorem atPl_sub' (w : T) (A B : Module.End ℂ (V w)) : atPl w (A - B) = atPl w A - atPl w B :=
  map_sub ((PiTensorProduct.mapMultilinear ℂ V V).toLinearMap (fun i => (LinearMap.id : V i →ₗ[ℂ] V i)) w) A B

theorem actAt_lie (w : T) {a : Mat p q →ₗ[ℂ] Module.End ℂ (V w)} (h : IsLieAct a) : IsLieAct (actAt w a) := by
  intro X Y
  rw [actAt_apply, actAt_apply, actAt_apply, h X Y, atPl_sub', atPl_mul', atPl_mul']

theorem actAt_wts (w : T) {a : Mat p q →ₗ[ℂ] Module.End ℂ (V w)} (h : ∀ v, v ∈ ⨆ μ : Ix p q → ℚ, wtSub a μ)
    (x : ⨂[ℂ] i, V i) : x ∈ ⨆ μ : Ix p q → ℚ, wtSub (actAt w a) μ := by
  induction x using PiTensorProduct.induction_on with
  | smul_tprod r f =>
    refine Submodule.smul_mem _ _ ?_
    rw [← position_self f w]
    refine Submodule.iSup_induction _ (motive := fun v => intersection_update_fsHerm_neg_one f w v ∈ ⨆ μ : Ix p q → ℚ, wtSub (actAt w a) μ) (h (f w))
      ?_ (by simp) ?_
    · intro μ y hy
      refine Submodule.mem_iSup_of_mem μ ?_
      simp only [wtSub, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
        LinearMap.smul_apply, LinearMap.id_apply] at hy ⊢
      intro c
      rw [actAt_apply, atPl_tprod_update, ← map_smul, ← map_sub, hy c, map_zero]
    · intro x y hx hy
      rw [map_add]; exact add_mem hx hy
  | add x y hx hy => exact Submodule.add_mem _ hx hy

theorem actAt_locU (w : T) {a : Mat p q →ₗ[ℂ] Module.End ℂ (V w)} (h : LocU (fun c : Ix p q => c.isLeft) (units a)) :
    LocU (fun c : Ix p q => c.isLeft) (units (actAt w a)) := by
  refine GlobalTheory.T.isLocallyBlockUnitary_of_iSup_intertwiner_range (Ix p q) (V w) (fun c : Ix p q => c.isLeft) (units a) (⨂[ℂ] i, V i) (units (actAt w a))
    {g | ∃ f : ∀ i, V i, g = intersection_update_fsHerm_neg_one f w} ?_ ?_ h
  · rintro g ⟨f, rfl⟩ c d _ x
    simp only [units, actAt_apply, atPl_tprod_update]
  · refine eq_top_iff.2 ?_
    rw [← PiTensorProduct.span_tprod_eq_top]
    refine Submodule.span_le.2 ?_
    rintro _ ⟨f, rfl⟩
    refine (le_iSup₂ (f := fun (g : V w →ₗ[ℂ] ⨂[ℂ] i, V i) (_ : g ∈ {g | ∃ f : ∀ i, V i, g = intersection_update_fsHerm_neg_one f w}) =>
      LinearMap.range g) (intersection_update_fsHerm_neg_one f w) ⟨f, rfl⟩ : _) ⟨f w, position_self f w⟩

end GlobalTheory.HoweR.FactorAct

namespace GlobalTheory.HoweR

theorem actAt_good_comm : ∀ (T : Type) [Fintype T] [DecidableEq T] (V : T → Type) [∀ w, AddCommGroup (V w)]
    [∀ w, Module ℂ (V w)], ∀ (R S : T → ℕ) (a : ∀ w, Mat (R w) (S w) →ₗ[ℂ] Module.End ℂ (V w)), (∀ w, Good (a w)) →
    (∀ w, Good (actAt w (a w))) ∧ ∀ w w', w ≠ w' → ∀ Z Z' v,
      actAt w (a w) Z (actAt w' (a w') Z' v) = actAt w' (a w') Z' (actAt w (a w) Z v) := by
  intro T _ _ V _ _ R S a ha
  refine ⟨fun w => ⟨FactorAct.actAt_lie w (ha w).1, FactorAct.actAt_wts w (ha w).2.1, FactorAct.actAt_locU w (ha w).2.2⟩,
    fun w w' hw Z Z' v => ?_⟩
  exact FactorAct.atPl_comm' hw _ _ v

end GlobalTheory.HoweR

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIntegralOfMemAdjoinInv
section
open GlobalTheory.LN

namespace GlobalTheory.ValCrit

open Polynomial in

theorem _root_.GlobalTheory.ValCrit.isIntegral_of_mem_adjoin_inv {R K : Type*} [CommRing R] [Field K] [Algebra R K]
    (y : K) (hy : y ≠ 0)
    (h : y⁻¹ ∈ Algebra.adjoin R {y}) : IsIntegral R y⁻¹ := by
  rw [Algebra.adjoin_singleton_eq_range_aeval] at h
  obtain ⟨p, hp⟩ := h
  letI : Invertible y := invertibleOfNonzero hy
  set n := p.natDegree
  have hrefl : (reflect n p).degree < ((n + 1 : ℕ) : WithBot ℕ) := by
    refine lt_of_le_of_lt (degree_le_natDegree) ?_
    have : (reflect n p).natDegree ≤ n := natDegree_reflect_le.trans (by simp [n])
    exact_mod_cast Nat.lt_succ_of_le this
  refine ⟨X ^ (n + 1) - reflect n p, monic_X_pow_sub hrefl, ?_⟩
  have key := eval₂_reflect_mul_pow (algebraMap R K) y n p le_rfl
  rw [invOf_eq_inv] at key
  have hp' : eval₂ (algebraMap R K) y p = y⁻¹ := hp
  rw [hp'] at key
  have hval : eval₂ (algebraMap R K) y⁻¹ (reflect n p) = y⁻¹ ^ (n + 1) := by
    have hyn : y ^ n ≠ 0 := pow_ne_zero _ hy
    rw [← mul_inv_cancel_right₀ hyn (eval₂ (algebraMap R K) y⁻¹ (reflect n p)), key, pow_succ,
      inv_pow, mul_comm]
  rw [eval₂_sub, eval₂_X_pow, hval, sub_self]

private theorem maximalIdeal_map_sup_span_ne_univ_of_inv_not_mem_adjoin {R K : Type} [CommRing R]
    [IsLocalRing R] [Field K] [Algebra R K] (y : K) (hnot : y⁻¹ ∉ Algebra.adjoin R {y}) :
    (IsLocalRing.maximalIdeal R).map (algebraMap R (Algebra.adjoin R {y})) ⊔
      Ideal.span {(⟨y, Algebra.self_mem_adjoin_singleton R y⟩ : Algebra.adjoin R {y})} ≠ ⊤ := by
  set S := Algebra.adjoin R {y}
  set ys : S := ⟨y, Algebra.self_mem_adjoin_singleton R y⟩
  intro hJ
  set π := Ideal.Quotient.mk (Ideal.span {ys})
  have hsurj : Function.Surjective (π.comp (algebraMap R S)) := by
    intro s
    obtain ⟨s, hs⟩ := Ideal.Quotient.mk_surjective s
    have hs2 : (s : K) ∈ (Polynomial.aeval (R := R) y).range := by
      rw [← Algebra.adjoin_singleton_eq_range_aeval]
      exact s.2
    obtain ⟨f, hf⟩ := hs2
    have hfs : Polynomial.aeval ys f = s :=
      Subtype.ext (by rw [← hf, Polynomial.aeval_subalgebra_coe]; rfl)
    refine ⟨f.coeff 0, ?_⟩
    rw [← hs, ← hfs, RingHom.comp_apply]
    conv_rhs => rw [← Polynomial.X_mul_divX_add f]
    rw [map_add, map_mul, Polynomial.aeval_X, Polynomial.aeval_C, map_add, map_mul,
      Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_span_singleton_self ys), zero_mul, zero_add]
  have htop : (IsLocalRing.maximalIdeal R).map (π.comp (algebraMap R S)) = ⊤ := by
    have := congrArg (Ideal.map π) hJ
    rwa [Ideal.map_sup, Ideal.map_map, Ideal.map_quotient_self, sup_bot_eq, Ideal.map_top] at this
  obtain ⟨a, ha, ha1⟩ := (Ideal.mem_map_iff_of_surjective _ hsurj).1
    (htop ▸ Submodule.mem_top : (1 : S ⧸ Ideal.span {ys}) ∈ _)
  have hmem : ys ∣ algebraMap R S (1 - a) := by
    rw [← Ideal.mem_span_singleton, map_sub, map_one, ← Ideal.Quotient.eq]
    exact ha1.symm
  have hunitA : IsUnit (algebraMap R S (1 - a)) :=
    (IsLocalRing.isUnit_one_sub_self_of_mem_nonunits a
      ((IsLocalRing.mem_maximalIdeal a).1 ha)).map _
  obtain ⟨u, hu⟩ := isUnit_of_dvd_unit hmem hunitA
  apply hnot
  have h1 : ((u⁻¹ : Sˣ) : S) * ys = 1 := by rw [← hu, Units.inv_mul]
  have h2 : (((u⁻¹ : Sˣ) : S) : K) = y⁻¹ := eq_inv_of_mul_eq_one_left (congrArg Subtype.val h1)
  exact h2 ▸ ((u⁻¹ : Sˣ) : S).2

theorem _root_.GlobalTheory.ValCrit.dvd_of_forall_cdvr : ∀ (R : Type) [CommRing R] [IsDomain R]
    [IsLocalRing R] [IsNoetherianRing R] [IsIntegrallyClosed R] [CharZero R] (p q : R), q ≠ 0 →
    (∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (φ : R →+* V),
      _root_.GlobalTheory.LN.CDvr V → Function.Injective φ →
      (IsLocalRing.maximalIdeal V).comap φ = IsLocalRing.maximalIdeal R → φ q ∣ φ p) →
    q ∣ p := by
  intro R _ _ _ _ _ _ p q hq H
  by_cases hp : p = 0
  · exact hp ▸ dvd_zero q
  by_contra hdvd
  set K := FractionRing R
  have hinjK : Function.Injective (algebraMap R K) := IsFractionRing.injective R K
  have hpK : algebraMap R K p ≠ 0 := (map_ne_zero_iff _ hinjK).2 hp
  have hqK : algebraMap R K q ≠ 0 := (map_ne_zero_iff _ hinjK).2 hq
  set y : K := algebraMap R K q / algebraMap R K p with hy_def
  have hy : y ≠ 0 := div_ne_zero hqK hpK
  set S := Algebra.adjoin R {y}
  have hnot : y⁻¹ ∉ S := by
    intro hmem
    have hint := _root_.GlobalTheory.ValCrit.isIntegral_of_mem_adjoin_inv y hy hmem
    obtain ⟨r, hr⟩ := IsIntegrallyClosed.isIntegral_iff.1 hint
    refine hdvd ⟨r, hinjK ?_⟩
    rw [map_mul, hr, hy_def, inv_div, mul_comm, div_mul_cancel₀ _ hqK]
  let ys : S := ⟨y, Algebra.self_mem_adjoin_singleton R y⟩
  have hinjS : Function.Injective (algebraMap R S) := by
    intro a b hab
    exact hinjK (congrArg Subtype.val hab)
  haveI : Algebra.FiniteType R S := Algebra.FiniteType.adjoin_of_finite (Set.finite_singleton y)
  haveI : IsNoetherianRing S := Algebra.FiniteType.isNoetherianRing R S
  haveI : CharZero S := charZero_of_injective_algebraMap hinjS
  set J : Ideal S := (IsLocalRing.maximalIdeal R).map (algebraMap R S) ⊔ Ideal.span {ys}
  have hJ : J ≠ ⊤ := maximalIdeal_map_sup_span_ne_univ_of_inv_not_mem_adjoin y hnot
  obtain ⟨P, hPmax, hJP⟩ := Ideal.exists_le_maximal J hJ
  have hyP : ys ∈ P := hJP (Ideal.mem_sup_right (Ideal.mem_span_singleton_self ys))
  have hcomapP : P.comap (algebraMap R S) = IsLocalRing.maximalIdeal R := by
    refine ((IsLocalRing.maximalIdeal.isMaximal R).eq_of_le ?_ ?_).symm
    · exact (hPmax.isPrime.comap (algebraMap R S)).ne_top
    · exact Ideal.map_le_iff_le_comap.1 (le_trans le_sup_left hJP)
  obtain ⟨V, _, _, _, φ, hV, hφ, hcomap⟩ :=
    _root_.GlobalTheory.PrimeUnif.exists_cdvr S P
  have hψ : Function.Injective (φ.comp (algebraMap R S)) := hφ.comp hinjS
  have hψc : (IsLocalRing.maximalIdeal V).comap (φ.comp (algebraMap R S)) =
      IsLocalRing.maximalIdeal R := by
    rw [← Ideal.comap_comap, hcomap, hcomapP]
  obtain ⟨v, hv⟩ := H V (φ.comp (algebraMap R S)) hV hψ hψc
  have hrel : ys * algebraMap R S p = algebraMap R S q := by
    apply Subtype.ext
    change y * algebraMap R K p = algebraMap R K q
    rw [hy_def, div_mul_cancel₀ _ hpK]
  have hψp : φ (algebraMap R S p) ≠ 0 := by
    intro h0
    exact hp (hψ (by simpa using h0))
  have hone : φ ys * v = 1 := by
    apply mul_left_cancel₀ hψp
    simp only [RingHom.comp_apply] at hv
    rw [← hrel, map_mul] at hv
    calc φ (algebraMap R S p) * (φ ys * v) = φ ys * φ (algebraMap R S p) * v := by ring
      _ = φ (algebraMap R S p) := hv.symm
      _ = φ (algebraMap R S p) * 1 := (mul_one _).symm
  have hunit : IsUnit (φ ys) := isUnit_iff_exists_inv.2 ⟨v, hone⟩
  have hys : ys ∉ P := by
    rw [← hcomap, Ideal.mem_comap]
    exact fun h => (IsLocalRing.mem_maximalIdeal _).1 h hunit
  exact hys hyP

end GlobalTheory.ValCrit
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLogCanonicalEquationChangeFormPerturbedDivisorStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep GlobalTheory.FieldPair
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isLogCanonicalEquation_changeForm_perturbed_divisor : ∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] (p : X ⟶ Sp ℂ) [LocallyOfFiniteType p] (n : ℕ),
    topologicalKrullDim X = n → ∀ (Δ D : X → ℚ) (η η' : RatForms p n) (x : X) (m mD l : ℕ)
    (gG fD g a F : X.functionFieldˣ) (A : CartierDiv X) (δ t : ℚ), η' ≠ 0 → η = (F : X.functionField) • η' →
    0 < m → 0 < mD → IsLogEqn p Δ η x m gG →
    (∀ z, z ⤳ x → ∀ E : DivOver p, E.IsAt z → D z = (E.ord fD : ℚ) / mD) → A.IsEqn x a →
    ∃ (m₂ : ℕ) (g₂ : X.functionFieldˣ), 0 < m₂ ∧
      IsLogEqn p (Δ + (1 - δ) • D + t • qWeil (CartierDiv.principal g + l • A) 1) η' x m₂ g₂ ∧
      ∀ E : DivOver p, discrep E η' m₂ g₂ = E.formOrd η' + E.ord F - E.ord gG / m
        - (1 - δ) * (E.ord fD / mD) - t * E.ord (g * a ^ l) := by
  first | exact @GlobalTheory.PairStep.isLogEqn_changeForm_add | exact GlobalTheory.PairStep.isLogEqn_changeForm_add | (intros; apply GlobalTheory.PairStep.isLogEqn_changeForm_add <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsNefOfSemiPosGeneratedBySmallSections
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.GenNef

theorem isNef_of_gen_small : GlobalTheory.Published.ArCalc → ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (M : HermLB p) (n : ℕ) (s : Fin n → M.B.Sec), M.SemiPos D → (∀ i, s i ∈ M.smallSec) → (∀ x : X, ∃ i, x ∈ ReciprocityTheory.ChartRestriction.G.Out.nonzeroLocus (s i)) → M.IsNef D := by
  intro _ k _ X _ p D hX M n s hsp hsm hs
  have hcov : ⨆ i, ReciprocityTheory.ChartRestriction.G.Out.nonzeroLocus (s i) = ⊤ :=
    top_le_iff.1 fun x _ =>
      have ⟨i, hi⟩ := hs x
      Opens.mem_iSup.2 ⟨i, hi⟩
  exact GlobalTheory.VolBr.Model.isNef_of_small hX M hsp
    (GlobalTheory.TrueGeo.OfLattice.nefFib_of_isGenerated hX M (GlobalTheory.isGenerated_of_finite s hcov))
    fun x => have ⟨i, hi⟩ := hs x; ⟨s i, hsm i, hi⟩

end GlobalTheory.GenNef

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsUnitStalkTransitionPulledBackFlagFramesStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZH GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.FlagPush
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isUnit_stalk_transition_pulledBack_flagFrames : ∀ (F : Type) [Field F] (X Y : Var F) (ι : Type) [Fintype ι] (m : ι → ℕ) (E : Fr (ratOf X) m 0) (E' : Fr (ratOf Y) m m) (φ : X.Fn →ₐ[F] Y.Fn) (f : Y.X ⟶ X.X), Refines E E' φ f → ∀ W : Dbl Y, (∀ u : X.Fn, W.α₁ (φ u) = W.α₂ (φ u)) → ∀ z : W.Z, ∀ A₁ ∈ E'.S (W.p₁ z), ∀ A₂ ∈ E'.S (W.p₂ z), Par 0 (algebraMap (W.Z.presheaf.stalk z) W.Z.functionField).range (A₁.map W.α₁ * (A₂.map W.α₂)⁻¹) := by
  first | exact @GlobalTheory.FlagPush.Dbl.transition_par_stalk | exact GlobalTheory.FlagPush.Dbl.transition_par_stalk | (intros; apply GlobalTheory.FlagPush.Dbl.transition_par_stalk <;> assumption)
end

