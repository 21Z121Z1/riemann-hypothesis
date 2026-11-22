import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.DifferentialFormsCech.CechDifferentialPullback.Bridge
import Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.FormUniq
import GroundTheory.AutomorphicForms.GL2.GodementSectionLocal
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LevelChainValuations.LatDefs
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.SplittingFieldLattices.GrSplit
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0181
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0166
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0171
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ConeSectionRestriction.GeoDefs
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0182
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.ConstantCoeffSurjective
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.GaloisTwistIdentitySection

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FormsToCechBijective
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite Limits GroundTheory.Arith.SchemeCoh GlobalTheory.SheafPull CrystallineSemistableComparison CrystallineSemistableComparison.Om CrystallineSemistableComparison.Om.Cech

namespace GlobalTheory.CompanionTheory.OmCech

theorem res_bijective_of_le {T : TopCat.{0}} (P : (Opens T)ᵒᵖ ⥤ AddCommGrpCat.{0}) {V W : Opens T}
    (h : V ≤ W) (h' : W ≤ V) : Function.Bijective (res P h) :=
  Function.bijective_iff_has_inverse.2
    ⟨res P h', fun x => by rw [res_res, res_refl], fun x => by rw [res_res, res_refl]⟩

theorem formCoch_bijective {K : Type} [Field K] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K))
    {ι : Type} (U : ι → X.Opens)
    (hUaff : ∀ (n : ℕ) (i : Fin (n + 1) → ι), IsAffineOpen (⨅ a, U (i a))) (a n : ℕ) :
    Function.Bijective (formCoch q U a n) := by
  have hb : ∀ i : Fin (n + 1) → ι, Function.Bijective
      (fun x => res (modulesAb (GlobalTheory.HodgeCoh.Omega q a)).obj (inter_le_capO U i)
        (toOm q a (Pb.capO U i) x)) := fun i =>
    (res_bijective_of_le _ (inter_le_capO U i) (le_of_eq (inter_eq_iInf U i).symm)).comp
      (GlobalTheory.HodgeCoh.toOm_bijective q a (hUaff n i))
  refine ⟨fun c c' h => funext fun i => (hb i).1 (congrFun h i), fun σ => ?_⟩
  choose c hc using fun i => (hb i).2 (σ i)
  exact ⟨c, funext hc⟩

theorem formToCO_bijective : ∀ {K : Type} [Field K] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K)) {ι : Type}
    (U : ι → X.Opens) (hUaff : ∀ (n : ℕ) (i : Fin (n + 1) → ι), IsAffineOpen (⨅ a, U (i a))) (a j : ℕ),
    Function.Bijective (formToCO q U a j) := by
  intro K _ X q ι U hUaff a j
  have hB := formCoch_bijective q U hUaff a
  constructor
  · rw [injective_iff_map_eq_zero]
    intro x hx
    obtain ⟨⟨c, hc⟩, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    have hc' : (Glob.formCos q U a).cx.d j c = 0 := hc
    have hx' : formToCO q U a j ((Glob.formCos q U a).cx.cls c hc') = 0 := hx
    rw [formToCO_cls, GroundTheory.Arith.SchemeCoh.cls_eq_zero_iff] at hx'
    refine (Submodule.Quotient.mk_eq_zero _).2 ?_
    change c ∈ (Glob.formCos q U a).cx.B j
    cases j with
    | zero =>
      rw [coboundaries_zero, AddSubgroup.mem_bot] at hx'
      exact (hB 0).1 (hx'.trans (map_zero _).symm)
    | succ n =>
      rw [coboundaries_succ] at hx'
      obtain ⟨τ, hτ⟩ := hx'
      obtain ⟨b, rfl⟩ := (hB n).2 τ
      exact ⟨b, (hB (n + 1)).1 ((formCoch_d q U a n b).trans hτ)⟩
  · intro y
    obtain ⟨σ, hσ, rfl⟩ := exists_cls (P := (modulesAb (GlobalTheory.HodgeCoh.Omega q a)).obj) (U := U) (n := j) y
    obtain ⟨c, rfl⟩ := (hB j).2 σ
    have hc : (Glob.formCos q U a).cx.d j c = 0 :=
      (hB (j + 1)).1 (((formCoch_d q U a j c).trans hσ).trans (map_zero _).symm)
    exact ⟨(Glob.formCos q U a).cx.cls c hc, formToCO_cls q U a c hc⟩

end GlobalTheory.CompanionTheory.OmCech
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FormsToCechSmul
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite Limits GroundTheory.Arith.SchemeCoh GlobalTheory.SheafPull CrystallineSemistableComparison CrystallineSemistableComparison.Om CrystallineSemistableComparison.Om.Cech

set_option autoImplicit false

noncomputable section
namespace GlobalTheory.CompanionTheory.OmBridge

open GlobalTheory.HodgeCoh GlobalTheory.CechDR

variable {K : Type} [Field K] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K))

theorem algebraMap_sec (W : X.Opens) (r : K) :
    letI := algΓ q
    algebraMap K (Sec q W) r = restrictTop W (algebraMap K Γ(X, ⊤) r) := by
  letI := algΓ q
  change ((Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫ q.appLE ⊤ W le_top).hom r =
    (((Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫ q.appTop) ≫ X.presheaf.map (homOfLE le_top).op).hom r
  congr 2

theorem toOm_smul (a : ℕ) (W : X.Opens) (r : K) (x : OmU q W a) :
    letI := algΓ q
    CrystallineSemistableComparison.Om.Cech.toOm q a W (r • x) =
      (smulAbRingHom (Omega q a) (algebraMap K Γ(X, ⊤) r)).hom.app (op W) (CrystallineSemistableComparison.Om.Cech.toOm q a W x) := by
  letI := algΓ q
  rw [← algebraMap_smul (Sec q W) r x]
  have h := ((toOmega q a).app (op W)).hom.map_smul (algebraMap K (Sec q W) r) x
  refine h.trans ?_
  rw [algebraMap_sec q W r]
  rfl

variable {ι : Type} (U : ι → X.Opens) (a : ℕ)

theorem formCoch_smul (n : ℕ) (r : K) (c : (Glob.formCos q U a).X n) :
    letI := algΓ q
    formCoch q U a n (r • c) =
      push U (smulAbRingHom (Omega q a) (algebraMap K Γ(X, ⊤) r)).hom n (formCoch q U a n c) := by
  letI := algΓ q
  funext i
  change res _ (inter_le_capO U i) (CrystallineSemistableComparison.Om.Cech.toOm q a (Pb.capO U i) (r • c i)) =
    (smulAbRingHom (Omega q a) (algebraMap K Γ(X, ⊤) r)).hom.app (op (inter U i))
      (res _ (inter_le_capO U i) (CrystallineSemistableComparison.Om.Cech.toOm q a (Pb.capO U i) (c i)))
  rw [toOm_smul]
  exact (ConcreteCategory.congr_hom
    ((smulAbRingHom (Omega q a) (algebraMap K Γ(X, ⊤) r)).hom.naturality
      (homOfLE (inter_le_capO U i)).op) _).symm

theorem formToCO_smul (j : ℕ) (r : K) (x : (Glob.formCos q U a).cx.H j) :
    formToCO q U a j (r • x) = r • formToCO q U a j x := by
  letI := algΓ q
  obtain ⟨⟨c, hc⟩, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  have hc' : (Glob.formCos q U a).cx.d j c = 0 := hc
  have hrc : (Glob.formCos q U a).cx.d j (r • c) = 0 := by rw [map_smul, hc', smul_zero]
  change formToCO q U a j ((Glob.formCos q U a).cx.cls (r • c) hrc) =
    r • formToCO q U a j ((Glob.formCos q U a).cx.cls c hc')
  rw [formToCO_cls, formToCO_cls]
  have hd : d (modulesAb (Omega q a)).obj U j (formCoch q U a j c) = 0 := by
    rw [← formCoch_d]
    exact (congrArg _ hc').trans (map_zero _)
  change _ = GroundTheory.Arith.SchemeCoh.cechHMap U (smulAbRingHom (Omega q a) (algebraMap K Γ(X, ⊤) r)).hom j
    (GroundTheory.Arith.SchemeCoh.cls (formCoch q U a j c) hd)
  rw [GroundTheory.Arith.SchemeCoh.cechHMap_cls]
  exact GroundTheory.Arith.SchemeCoh.cls_congr U (formCoch_smul q U a j r c) _ _

end GlobalTheory.CompanionTheory.OmBridge
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FunctorId
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false

noncomputable section

open CategoryTheory AlgebraicGeometry CrystallineSemistableComparison CrystallineSemistableComparison.HT CrystallineSemistableComparison.Pb GlobalTheory.LogCris

namespace GlobalTheory.CompanionTheory.HodgePull

variable {K : Type} [CommRing K] {X : Scheme.{0}} {q : X ⟶ Spec (CommRingCat.of K)}

theorem thick_ext {T T' : Thick (smFun X q)} (hB : T.B = T'.B) (hr : HEq T.ring T'.ring) (hi : HEq T.i T'.i)
    (hJ : HEq T.J T'.J) (hδ : HEq T.δ T'.δ) (hy : HEq T.y T'.y) : T = T' := by
  have hs : T.s = 1 := s_eq_one (γ := dividedPowersBot K) (p := 0) (q := q) (κ := Ideal.Quotient.mk ⊥) T
  have hs' : T'.s = 1 := s_eq_one (γ := dividedPowersBot K) (p := 0) (q := q) (κ := Ideal.Quotient.mk ⊥) T'
  cases T with
  | @mk B ring i J δ adm compat α y inα w x v s hx hs0 hv =>
  cases T' with
  | @mk B' ring' i' J' δ' adm' compat' α' y' inα' w' x' v' s' hx' hs0' hv' =>
  dsimp only at hB hr hi hJ hδ hy hs hs'
  subst hB
  obtain rfl := eq_of_heq hr
  obtain rfl := eq_of_heq hi
  obtain rfl := eq_of_heq hJ
  obtain rfl := eq_of_heq hδ
  obtain rfl := eq_of_heq hy
  obtain rfl : x = x' := funext fun j => Empty.elim j
  obtain rfl : v = v' := funext fun j => Empty.elim j
  obtain rfl : s = s' := hs.trans hs'.symm
  rfl

theorem hom_heq {T₁ T₂ T₁' T₂' : Thick (smFun X q)} (h : T₁ = T₂) (h' : T₁' = T₂') (f : T₁ ⟶ T₁') (g : T₂ ⟶ T₂')
    (hφ : HEq f.φ g.φ) : HEq f g := by
  subst h h'
  exact heq_of_eq (Thick.Hom.ext (eq_of_heq hφ) (funext fun j => Empty.elim j))

theorem obj_id (T : Thick (smFun X q)) : (smMor (𝟙 X) (Category.id_comp q)).obj T = T :=
  thick_ext rfl HEq.rfl HEq.rfl HEq.rfl HEq.rfl (heq_of_eq (Subtype.ext (Prod.ext rfl (Category.comp_id _))))

theorem functor_id : (smMor (𝟙 X) (Category.id_comp q)).functor = 𝟭 _ :=
  Functor.hext obj_id fun T T' f => hom_heq (obj_id T) (obj_id T') _ _ HEq.rfl

abbrev idMor (q : X ⟶ Spec (CommRingCat.of K)) (a : ℕ) : CH.Mor (grT (smFun X q) a) (grT (smFun X q) a) (RingHom.id K) :=
  (smS (𝟙 X) (Category.id_comp q)).sq (a := thFil _ (a : ℤ)) (b := thFil _ ((a : ℤ) + 1)) (a' := thFil _ (a : ℤ))
    (b' := thFil _ ((a : ℤ) + 1)) (fun _ _ hx => hx) fun _ _ hx => hx

theorem τ_id (a : ℕ) (T : Thick (smFun X q)) (y : (grT (smFun X q) a).obj T) :
    (idMor q a).τ T y = y := by
  obtain ⟨x, hx⟩ := y
  obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective x
  rfl

theorem pullC_id (a n : ℕ) (z : CH.Cn (grT (smFun X q) a) n) : (idMor q a).pullC n z = z := by
  funext s
  have h : s ⋙ (idMor q a).G = s := by
    change s ⋙ (smMor (𝟙 X) (Category.id_comp q)).functor = s
    rw [functor_id]
    exact Functor.comp_id s
  exact (τ_id a _ _).trans (eq_of_heq (congr_arg_heq z h))

theorem pullH_id : ∀ (K : Type) [Field K] (X : Scheme.{0}) (q : X ⟶ Spec (CommRingCat.of K)) (a n : ℕ) (x : Hdg q a n),
    pullH (𝟙 X) (Category.id_comp q) a n x = x := by
  intro K _ X q a n x
  obtain ⟨⟨z, hz⟩, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  exact congrArg (Submodule.Quotient.mk (p := _)) (Subtype.ext (pullC_id a n z))

end GlobalTheory.CompanionTheory.HodgePull

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsSmoothOfTranslationLaw
section
set_option maxSynthPendingDepth 1

open MeasureTheory Matrix GroundTheory.LocalField GroundTheory.Automorphic GroundTheory.Automorphic.GodementSectionLocal
open scoped ValuativeRel

namespace GlobalTheory.CompanionTheory.GodementFix

variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]

theorem exists_congruence_fix {χ : Fˣ →* ℂˣ} (h : Continuous χ) {Φ : (Fin 2 → F) → ℂ}
    (hΦ : Φ ∈ schwartzBruhat2 F) :
    ∃ m : ℕ, ∀ u ∈ GLnLocal.congruenceSubgroup F 2 m,
      rightTranslate u Φ = Φ ∧ χ (detU u) = 1 ∧ ∀ s : ℂ, modPow ((detU u : Fˣ) : F) s = 1 := by
  obtain ⟨N, M, hMN, hinv, hsupp⟩ := exists_invariant_of_mem_schwartzBruhat2 hΦ
  refine ⟨max (N - M).toNat (max (quasiCharConductor χ) 1), fun u hu ↦ ?_⟩
  set m := max (N - M).toNat (max (quasiCharConductor χ) 1) with hm
  have hu0 : u ∈ GLnLocal.integralGL F 2 := GLnLocal.congruenceSubgroup_le F 2 m hu
  refine ⟨?_, ?_, fun s ↦ ?_⟩
  · funext x
    simp only [rightTranslate]
    by_cases hx : x ∈ box F M
    · set D : Matrix (Fin 2) (Fin 2) F := (u : Matrix (Fin 2) (Fin 2) F) - 1 with hD
      have hxD : x ᵥ* D ∈ box F N := by
        refine box_antitone (show N ≤ M + m by omega) (mem_box.2 fun j ↦ ?_)
        simp only [Matrix.vecMul, dotProduct, Fin.sum_univ_two]
        exact add_mem (mul_mem_valBall (mem_box.1 hx 0)
            (sub_one_mem_valBall_of_mem_congruenceSubgroup hu 0 j))
          (mul_mem_valBall (mem_box.1 hx 1)
            (sub_one_mem_valBall_of_mem_congruenceSubgroup hu 1 j))
      have he : x ᵥ* (u : Matrix (Fin 2) (Fin 2) F) = x + x ᵥ* D := by
        rw [hD, Matrix.vecMul_sub, Matrix.vecMul_one]
        abel
      rw [he, hinv x _ hxD]
    · have h0 : Φ x = 0 := by
        by_contra h
        exact hx (hsupp x h)
      have h1 : Φ (x ᵥ* (u : Matrix (Fin 2) (Fin 2) F)) = 0 := by
        by_contra h
        exact hx ((vecMul_mem_box_iff hu0 M x).1 (hsupp _ h))
      rw [h0, h1]
  · have hmem : detU u ∈ unitFiltrationUnits F m :=
      (mem_unitFiltrationUnits_iff_valBall (by omega)).2 (det_sub_one_mem_valBall hu)
    exact unitFiltrationUnits_quasiCharConductor_le_ker h
      (unitFiltrationUnits_antitone (by omega) hmem)
  · rw [modPow_units_eq_zpow, ord_det_eq_zero hu0]
    simp

end GlobalTheory.CompanionTheory.GodementFix
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LatticeFiltrationAdicClosed
section
set_option autoImplicit false

open DividedPowers CrystallineSemistableComparison.Pb

namespace GlobalTheory.CompanionTheory.LatAdicClosedB

section
variable {W B : Type} [CommRing W] [CommRing B] [Algebra ℚ B] (f : W →+* B) (ξ : W) (l M : ℕ)

noncomputable def q (l M i : ℕ) : ℚ := (i.factorial : ℚ)⁻¹ * (((l : ℚ) ^ M)⁻¹) ^ i

def S (j : ℕ) : AddSubgroup B :=
  AddSubgroup.closure {b | ∃ (w : W) (i : ℕ), j ≤ i ∧ b = f w * Lat.dpE f ξ l M i}

theorem ι_mem (x : Lat.A f ξ l M) : Lat.ι f ξ l M x ∈ Lat.sub f ξ l M :=
  Subtype.prop (show ↥(Lat.sub f ξ l M) from x)

end

end GlobalTheory.CompanionTheory.LatAdicClosedB
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LatticeFiltrationLAdicClosed
section
set_option autoImplicit false

noncomputable section

open DividedPowers CrystallineSemistableComparison.Pb

namespace GlobalTheory.CompanionTheory.LatClosed

variable {W B : Type} [CommRing W] [CommRing B] [Algebra ℚ B] (f : W →+* B) (ξ : W) (l M : ℕ)

def T (r : ℕ) : AddSubgroup B :=
  AddSubgroup.closure {b | ∃ (w : W) (i : ℕ), r ≤ i ∧ b = f w * Lat.dpE f ξ l M i}

theorem dpE_eq (i : ℕ) : Lat.dpE f ξ l M i =
    (((i.factorial : ℚ))⁻¹ * (((l : ℚ) ^ M)⁻¹) ^ i) • f ξ ^ i := by
  simp only [Lat.dpE, Lat.η, smul_pow, smul_smul]

theorem dpE_mem {r i : ℕ} (h : r ≤ i) : Lat.dpE f ξ l M i ∈ Ideal.span {f ξ ^ r} := by
  rw [dpE_eq, Algebra.smul_def, Ideal.mem_span_singleton]
  exact Dvd.dvd.mul_left (pow_dvd_pow _ h) _

theorem mul_dpE (hl : l ≠ 0) (r : ℕ) : f ξ * Lat.dpE f ξ l M r =
    f ((l : W) ^ M * ((r + 1 : ℕ) : W)) * Lat.dpE f ξ l M (r + 1) := by
  have hl' : (l : ℚ) ≠ 0 := Nat.cast_ne_zero.2 hl
  have hf : ((r.factorial : ℕ) : ℚ) ≠ 0 := Nat.cast_ne_zero.2 (Nat.factorial_ne_zero r)
  have hr : ((r + 1 : ℕ) : ℚ) ≠ 0 := Nat.cast_ne_zero.2 (Nat.succ_ne_zero r)
  have key : ((r.factorial : ℚ))⁻¹ * (((l : ℚ) ^ M)⁻¹) ^ r =
      (((l ^ M * (r + 1) : ℕ)) : ℚ) * (((r + 1).factorial : ℚ)⁻¹ * (((l : ℚ) ^ M)⁻¹) ^ (r + 1)) := by
    rw [Nat.factorial_succ]
    push_cast at hr ⊢
    have hu : (l : ℚ) ^ M * ((l : ℚ) ^ M)⁻¹ = 1 := mul_inv_cancel₀ (pow_ne_zero _ hl')
    generalize ((l : ℚ) ^ M)⁻¹ = u at hu ⊢
    field_simp
    rw [pow_succ]
    linear_combination (-(u ^ r)) * hu
  rw [dpE_eq, dpE_eq, key, Algebra.smul_def, Algebra.smul_def, map_mul, map_natCast]
  simp only [map_mul, map_pow, map_natCast]
  push_cast
  ring

theorem T_split (r : ℕ) {b : B} (hb : b ∈ T f ξ l M r) :
    ∃ c : W, ∃ t ∈ T f ξ l M (r + 1), b = f c * Lat.dpE f ξ l M r + t := by
  induction hb using AddSubgroup.closure_induction with
  | mem x hx =>
    obtain ⟨w, i, hi, rfl⟩ := hx
    rcases hi.eq_or_lt with rfl | hlt
    · exact ⟨w, 0, zero_mem _, by simp⟩
    · exact ⟨0, _, AddSubgroup.subset_closure ⟨w, i, hlt, rfl⟩, by simp⟩
  | zero => exact ⟨0, 0, zero_mem _, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨c, t, ht, rfl⟩ := hx
    obtain ⟨c', t', ht', rfl⟩ := hy
    exact ⟨c + c', t + t', add_mem ht ht', by rw [map_add]; ring⟩
  | neg x _ hx =>
    obtain ⟨c, t, ht, rfl⟩ := hx
    exact ⟨-c, -t, neg_mem ht, by rw [map_neg]; ring⟩

theorem T_mem_span {r : ℕ} {b : B} (hb : b ∈ T f ξ l M r) : b ∈ Ideal.span {f ξ ^ r} := by
  induction hb using AddSubgroup.closure_induction with
  | mem x hx =>
    obtain ⟨w, i, hi, rfl⟩ := hx
    exact Ideal.mul_mem_left _ _ (dpE_mem f ξ l M hi)
  | zero => exact zero_mem _
  | add x y _ _ hx hy => exact add_mem hx hy
  | neg x _ hx => exact neg_mem hx

theorem mem_T_zero {b : B} (hb : b ∈ Lat.sub f ξ l M) : b ∈ T f ξ l M 0 := by
  obtain ⟨n, c, rfl⟩ := (GlobalTheory.T.mem_lattice_sub_iff_sum f ξ l M b).1 hb
  exact sum_mem fun i _ => AddSubgroup.subset_closure ⟨c i, i, Nat.zero_le _, rfl⟩

theorem xi_mul_mem (hl : l ≠ 0) (r : ℕ) (e : W) :
    f (ξ * e) * Lat.dpE f ξ l M r ∈ T f ξ l M (r + 1) := by
  refine AddSubgroup.subset_closure ⟨e * ((l : W) ^ M * ((r + 1 : ℕ) : W)), r + 1, le_rfl, ?_⟩
  rw [map_mul, map_mul f e, mul_assoc (f e), ← mul_dpE f ξ l M hl r]
  ring

variable {f ξ l M}

theorem l_ne_zero {m : ℕ} (h : Lat.Hyp f ξ l m) : l ≠ 0 := fun h0 => h.l0 (by simp [h0])

theorem dvd_of_mem {m r : ℕ} (h : Lat.Hyp f ξ l m) (hr : r < m) {c : W}
    (hc : f c * Lat.dpE f ξ l M r ∈ Ideal.span {f ξ ^ (r + 1)}) : ξ ∣ c := by
  have hl : (l : ℚ) ≠ 0 := Nat.cast_ne_zero.2 (l_ne_zero h)
  obtain ⟨b, hb⟩ := Ideal.mem_span_singleton.1 hc
  set s : ℚ := ((r.factorial : ℚ))⁻¹ * (((l : ℚ) ^ M)⁻¹) ^ r with hs
  have hs0 : s ≠ 0 := by
    have : ((r.factorial : ℕ) : ℚ) ≠ 0 := Nat.cast_ne_zero.2 (Nat.factorial_ne_zero r)
    rw [hs]; positivity
  rw [dpE_eq, ← hs] at hb
  refine h.gr r hr c (s⁻¹ • b) ?_
  have : s⁻¹ • (f c * s • f ξ ^ r) = s⁻¹ • (f ξ ^ (r + 1) * b) := by rw [hb]
  rwa [mul_smul_comm, smul_smul, inv_mul_cancel₀ hs0, one_smul, ← mul_smul_comm] at this

theorem T_of_span {m : ℕ} (h : Lat.Hyp f ξ l m) (r : ℕ) {b : B} (h0 : b ∈ T f ξ l M 0)
    (hb : b ∈ Ideal.span {f ξ ^ r}) : b ∈ T f ξ l M r := by
  induction r with
  | zero => exact h0
  | succ r ih =>
    have hr : b ∈ T f ξ l M r :=
      ih (Ideal.span_singleton_le_span_singleton.2 (pow_dvd_pow _ (Nat.le_succ r)) hb)
    by_cases hrm : r < m
    · obtain ⟨c, t, ht, rfl⟩ := T_split f ξ l M r hr
      have hc : f c * Lat.dpE f ξ l M r ∈ Ideal.span {f ξ ^ (r + 1)} := by
        have := sub_mem hb (T_mem_span f ξ l M ht)
        rwa [add_sub_cancel_right] at this
      obtain ⟨e, rfl⟩ := dvd_of_mem h hrm hc
      exact add_mem (xi_mul_mem f ξ l M (l_ne_zero h) r e) ht
    · have hz : f ξ ^ (r + 1) = 0 := pow_eq_zero_of_le (by omega) h.nil
      rw [hz, Ideal.span_singleton_eq_bot.2 rfl, Ideal.mem_bot] at hb
      rw [hb]; exact zero_mem _

theorem tf_pow {m : ℕ} (h : Lat.Hyp f ξ l m) (hc : Lat.DPClosed (Lat.ι f ξ l M) (Lat.γB f ξ)) (r n : ℕ)
    (a : Lat.A f ξ l M) (H : (l : Lat.A f ξ l M) ^ n * a ∈ pdP (Lat.γ f ξ l M hc) r) :
    a ∈ pdP (Lat.γ f ξ l M hc) r := by
  induction n with
  | zero => simpa using H
  | succ n ih =>
    rw [pow_succ', mul_assoc] at H
    exact ih (GlobalTheory.T.lattice_filtration_l_torsion_free f ξ l M m h hc r _ H)

theorem lat_ι_mem_T_zero (x : Lat.A f ξ l M) : Lat.ι f ξ l M x ∈ T f ξ l M 0 :=
  mem_T_zero f ξ l M (Subtype.prop x)

theorem closed_succ {m : ℕ} (h : Lat.Hyp f ξ l m) (hc : Lat.DPClosed (Lat.ι f ξ l M) (Lat.γB f ξ)) (r : ℕ)
    (ih : ∀ x : Lat.A f ξ l M, (∀ n : ℕ, x ∈ Ideal.span {(l : Lat.A f ξ l M) ^ n} ⊔ pdP (Lat.γ f ξ l M hc) r) →
      x ∈ pdP (Lat.γ f ξ l M hc) r)
    (x : Lat.A f ξ l M)
    (hx : ∀ n : ℕ, x ∈ Ideal.span {(l : Lat.A f ξ l M) ^ n} ⊔ pdP (Lat.γ f ξ l M hc) (r + 1)) :
    x ∈ pdP (Lat.γ f ξ l M hc) (r + 1) := by
  have E := GlobalTheory.T.lattice_filtration_comap_span_pow f ξ l M m h hc
  have hle : pdP (Lat.γ f ξ l M hc) (r + 1) ≤ pdP (Lat.γ f ξ l M hc) r := by
    rw [E, E]
    exact Ideal.comap_mono (Ideal.span_singleton_le_span_singleton.2 (pow_dvd_pow _ (Nat.le_succ r)))
  have hxr : x ∈ pdP (Lat.γ f ξ l M hc) r := ih x fun n => sup_le_sup_left hle _ (hx n)
  have hxr' : Lat.ι f ξ l M x ∈ Ideal.span {f ξ ^ r} := by
    rw [E] at hxr; exact hxr
  by_cases hrm : r < m
  · obtain ⟨c, t, ht, hcx⟩ := T_split f ξ l M r (T_of_span h r (lat_ι_mem_T_zero x) hxr')
    have hz : Ideal.Quotient.mk (Ideal.span {ξ}) c = 0 := by
      refine h.cpl.toIsHausdorff.haus' _ fun n => ?_
      obtain ⟨a, y, hy, hxa⟩ := Ideal.mem_span_singleton_sup.1 (hx n)
      have hay : (l : Lat.A f ξ l M) ^ n * a ∈ pdP (Lat.γ f ξ l M hc) r := by
        have : (l : Lat.A f ξ l M) ^ n * a = x - y := by rw [← hxa]; ring
        rw [this]; exact sub_mem hxr (hle hy)
      have ha := tf_pow h hc r n a hay
      have ha' : Lat.ι f ξ l M a ∈ Ideal.span {f ξ ^ r} := by
        rw [E] at ha; exact ha
      obtain ⟨d, t', ht', hda⟩ := T_split f ξ l M r (T_of_span h r (lat_ι_mem_T_zero a) ha')
      have hy' : Lat.ι f ξ l M y ∈ Ideal.span {f ξ ^ (r + 1)} := by
        rw [E] at hy; exact hy
      have hxa' : Lat.ι f ξ l M a * (l : B) ^ n + Lat.ι f ξ l M y = Lat.ι f ξ l M x := by
        rw [← hxa]; simp only [map_add, map_mul, map_pow, map_natCast]
      have e : f (c - (l : W) ^ n * d) * Lat.dpE f ξ l M r =
          (l : B) ^ n * t' + Lat.ι f ξ l M y - t := by
        simp only [map_sub, map_mul, map_pow, map_natCast]
        linear_combination (-1) * hcx - hxa' + (l : B) ^ n * hda
      have hm : f (c - (l : W) ^ n * d) * Lat.dpE f ξ l M r ∈ Ideal.span {f ξ ^ (r + 1)} := by
        rw [e]
        exact sub_mem (add_mem (Ideal.mul_mem_left _ _ (T_mem_span f ξ l M ht')) hy') (T_mem_span f ξ l M ht)
      have hdv := dvd_of_mem h hrm hm
      have heq : Ideal.Quotient.mk (Ideal.span {ξ}) c = Ideal.Quotient.mk (Ideal.span {ξ}) ((l : W) ^ n * d) :=
        Ideal.Quotient.eq.2 (Ideal.mem_span_singleton.2 hdv)
      rw [SModEq.zero, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
      exact ⟨Ideal.Quotient.mk _ d, by rw [heq, map_mul, map_pow, map_natCast]⟩
    obtain ⟨e, rfl⟩ := Ideal.mem_span_singleton.1 (Ideal.Quotient.eq_zero_iff_mem.1 hz)
    rw [E, Ideal.mem_comap, hcx]
    exact T_mem_span f ξ l M (add_mem (xi_mul_mem f ξ l M (l_ne_zero h) r e) ht)
  · have h0 : f ξ ^ r = 0 := pow_eq_zero_of_le (not_lt.1 hrm) h.nil
    rw [h0, Ideal.span_singleton_eq_bot.2 rfl, Ideal.mem_bot] at hxr'
    rw [E, Ideal.mem_comap, hxr']
    exact zero_mem _

theorem closed : ∀ {W B : Type} [CommRing W] [CommRing B] [Algebra ℚ B] (f : W →+* B) (ξ : W) (l M : ℕ) (m : ℕ),
    Lat.Hyp f ξ l m → ∀ hc : Lat.DPClosed (Lat.ι f ξ l M) (Lat.γB f ξ), ∀ (r : ℕ) (x : Lat.A f ξ l M),
    (∀ n : ℕ, x ∈ Ideal.span {(l : Lat.A f ξ l M) ^ n} ⊔ pdP (Lat.γ f ξ l M hc) r) →
    x ∈ pdP (Lat.γ f ξ l M hc) r := by
  intro W B _ _ _ f ξ l M m h hc r
  induction r with
  | zero =>
    intro x _
    rw [GlobalTheory.T.lattice_filtration_comap_span_pow f ξ l M m h hc 0]
    simp
  | succ r ih => exact closed_succ h hc r ih

end GlobalTheory.CompanionTheory.LatClosed
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NoetherNormalizationFiniteStatement
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor CrystallineSemistableComparison.Pb
attribute [local instance] MvPolynomial.gradedAlgebra
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.noether_normalization_finite : ∀ {K : Type} [Field K] {X : Scheme.{0}} {N d e : ℕ} (i : X ⟶ PSpace K N) (y : Fin (d + 1) → MvPolynomial (Fin (N + 1)) K) (hy : ∀ k, (y k).IsHomogeneous e) {V : X.Opens} (hV : V ≤ ⨅ k, i ⁻¹ᵁ Proj.basicOpen (grK K N) (y k)), 0 < e → ∀ (q : X ⟶ Spec (CommRingCat.of K)), i ≫ PSpace.str K N = q → Module.Finite (Algebra.adjoin K (Set.range fun k => Ideal.Quotient.mk (homIdeal i) (y k))) (MvPolynomial (Fin (N + 1)) K ⧸ homIdeal i) → ∀ (S : Finset (Fin (d + 1))) (hS : V ≤ i ⁻¹ᵁ Proj.basicOpen (grK K N) (yS y S)) (ht : ∀ k, IsUnit (tV i y hy V hV k)), letI := (strV q V).toAlgebra; ∀ a, IsIntegral (torusS K (fun k => (ht k).unit) S) (evV i (yS y S) V hS a) := by
  first | exact @GlobalTheory.CompanionTheory.GeoInteg.isIntegral_torusS | exact GlobalTheory.CompanionTheory.GeoInteg.isIntegral_torusS | (intros; apply GlobalTheory.CompanionTheory.GeoInteg.isIntegral_torusS <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PrimePowAnnihilatorReductionStatement
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory GroundTheory.PAdicHodge CrystallineSemistableComparison CrystallineSemistableComparison.PAlg
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.prime_pow_annihilator_reduction : ∀ {l : ℕ} [Fact l.Prime] (A : PAlg l) (n m : ℕ), Function.Surjective (A.red (Nat.le_add_right n m)) ∧ (∀ x : A.Acr (n + m), A.red (Nat.le_add_right n m) x = 0 ↔ x ∈ Ideal.span {(l : A.Acr (n + m)) ^ n}) ∧ (∀ x : A.Acr (n + m), (l : A.Acr (n + m)) ^ n * x = 0 ↔ A.red (Nat.le_add_left m n) x = 0) ∧ ∀ x : A.U, (l : A.U) ^ n * x ∈ Ideal.span {(l : A.U) ^ (n + m)} ↔ x ∈ Ideal.span {(l : A.U) ^ m} := by
  first | exact @GlobalTheory.CompanionTheory.PerfAlg.lseq | exact GlobalTheory.CompanionTheory.PerfAlg.lseq | (intros; apply GlobalTheory.CompanionTheory.PerfAlg.lseq <;> assumption)
end

