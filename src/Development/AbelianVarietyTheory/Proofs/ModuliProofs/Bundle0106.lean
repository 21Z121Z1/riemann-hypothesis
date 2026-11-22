import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.SemicharacterSqEqOneOfSymmetric
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.Bundle0016
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.Bundle0013
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.Bundle0015
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.Bundle0018
import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.AppLESurjective
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle0001
import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.ExistsSectionRing
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0019
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0004
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsPrimitiveNormalisation
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsAbelianSchemeAndExtendOfGenericHoms
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0066
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0101
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0102
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsIsMonHomOfComplementary
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.LatticeHom

variable {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} {g : ℕ}

theorem exists_chart_lbPow (u : HolUnif A L g) (hL : L.IsLB) (n : ℕ) (z : Fin g → ℂ) :
    ∃ k : (lbPow L n).ι, ⊤ ≤ (u.ex z).left ⁻¹ᵁ (lbPow L n).U k := by
  obtain ⟨i, hi⟩ := SymmetricSemicharacter.exists_chart u SymmetricSemicharacter.valueRules hL z
  refine ⟨fun _ => i, ?_⟩
  rwa [Cartier.lbPow_U]

theorem fr_pow_ne_zero (u : HolUnif A L g) (n : ℕ) {z : Fin g → ℂ} {k : (lbPow L n).ι}
    (hk : ⊤ ≤ (u.ex z).left ⁻¹ᵁ (lbPow L n).U k) : u.fr (k PUnit.unit) z ^ n ≠ 0 :=
  pow_ne_zero n (u.fr_ne _ z (Cartier.lbPow_U L n k ▸ hk))

theorem le_preimage_nonzeroLocus_iff (u : HolUnif A L g) (hL : L.IsLB) {n : ℕ} {s : (lbPow L n).Sec}
    {θ : (Fin g → ℂ) → ℂ} (hs : u.IsFnPow n s θ) (z : Fin g → ℂ) :
    ⊤ ≤ (u.ex z).left ⁻¹ᵁ Out.nonzeroLocus s ↔ θ z ≠ 0 := by
  constructor
  · intro h
    obtain ⟨k, hk⟩ := TopologicalSpace.Opens.mem_iSup.1 ((top_le_preimage_iff_mem _ _).1 h)
    have h1 := (top_le_preimage_basicOpen_iff _ _ _).1 ((top_le_preimage_iff_mem _ _).2 hk)
    rw [hs k z (top_le_preimage_of_valAt'_ne_zero _ h1)] at h1
    exact left_ne_zero_of_mul h1
  · intro h
    obtain ⟨k, hk⟩ := exists_chart_lbPow u hL n z
    refine top_le_preimage_mono _ (le_iSup (fun k => A.left.basicOpen (s.f k)) k) ?_
    rw [top_le_preimage_basicOpen_iff, hs k z hk]
    exact mul_ne_zero h (fr_pow_ne_zero u n hk)

theorem valAt'_eq_div_of_mul (u : HolUnif A L g) (hL : L.IsLB) {n : ℕ} {s s' : (lbPow L n).Sec}
    {θ θ' : (Fin g → ℂ) → ℂ} (hs : u.IsFnPow n s θ) (hs' : u.IsFnPow n s' θ') (r : Γ(A.left, Out.nonzeroLocus s))
    (hr : ∀ k, resG _ (inf_le_right : Out.nonzeroLocus s ⊓ (lbPow L n).U k ≤ _) (s'.f k) =
      resG _ inf_le_left r * resG _ inf_le_right (s.f k)) {z : Fin g → ℂ} (hz : θ z ≠ 0) :
    valAt' (u.ex z).left _ r = θ' z / θ z := by
  obtain ⟨k, hk⟩ := exists_chart_lbPow u hL n z
  have hW := (top_le_preimage_inf _ _ _).2 ⟨(le_preimage_nonzeroLocus_iff u hL hs z).2 hz, hk⟩
  have h := congrArg (valAt' (u.ex z).left _) (hr k)
  rw [valAt'_mul, valAt'_res _ _ _ hW, valAt'_res _ _ _ hW, valAt'_res _ _ _ hW, hs k z hk, hs' k z hk,
    ← _root_.mul_assoc] at h
  rw [mul_right_cancel₀ (fr_pow_ne_zero u n hk) h, mul_div_cancel_right₀ _ hz]

theorem exists_regular_quotients (u : HolUnif A L g) (hL : L.IsLB) {n : ℕ} {κ : Type*} {s : κ → (lbPow L n).Sec}
    {θ : κ → (Fin g → ℂ) → ℂ} (hs : ∀ j, u.IsFnPow n (s j) (θ j)) (i : κ) {z₀ : Fin g → ℂ} (h0 : θ i z₀ ≠ 0) :
    ∃ (U : A.left.Opens) (ρ : κ → Γ(A.left, U)), ⊤ ≤ (u.ex z₀).left ⁻¹ᵁ U ∧
      ∀ z, ⊤ ≤ (u.ex z).left ⁻¹ᵁ U → θ i z ≠ 0 ∧ ∀ j, valAt' (u.ex z).left U (ρ j) = θ j z / θ i z := by
  obtain ⟨k, hk⟩ := exists_chart_lbPow u hL n z₀
  have hle := A.left.basicOpen_le ((s i).f k)
  obtain ⟨v, hv⟩ : IsUnit (resG A.left hle ((s i).f k)) := RingedSpace.isUnit_res_basicOpen _ _
  refine ⟨A.left.basicOpen ((s i).f k), fun j => resG A.left hle ((s j).f k) * (v⁻¹).val, ?_, fun z hz => ?_⟩
  · rw [top_le_preimage_basicOpen_iff, hs i k z₀ hk]
    exact mul_ne_zero h0 (fr_pow_ne_zero u n hk)
  · have hk' := top_le_preimage_mono _ hle hz
    have h1 := (top_le_preimage_basicOpen_iff _ _ _).1 hz
    rw [hs i k z hk'] at h1
    refine ⟨left_ne_zero_of_mul h1, fun j => ?_⟩
    rw [valAt'_mul, valAt'_units_inv _ hz, hv, valAt'_res _ _ _ hz, valAt'_res _ _ _ hz, hs i k z hk', hs j k z hk',
      ← div_eq_mul_inv, mul_div_mul_right _ _ (right_ne_zero_of_mul h1)]

theorem isMonHom_of_lift {A' : Over (Sp ℂ)} [GrpObj A'] {L' : LB A'.left} {g' : ℕ} (u : HolUnif A L g)
    (u' : HolUnif A' L' g') [Smooth A.hom] (F : (Fin g → ℂ) →ₗ[ℂ] (Fin g' → ℂ)) (f : A ⟶ A')
    (hf : ∀ z, u'.ex (F z) = u.ex z ≫ f) : IsMonHom f := by
  have hr : IsReduced A.left := isReduced_of_smooth_complex _ A.hom inferInstance
  have h0 : u.ex 0 = η[A] := by
    rw [(u.ker 0).2 u.Λ.zero_mem, Hom.one_def, toUnit_unit, Category.id_comp]
  have h0' : u'.ex 0 = η[A'] := by
    rw [(u'.ker 0).2 u'.Λ.zero_mem, Hom.one_def, toUnit_unit, Category.id_comp]
  refine ⟨?_, ?_⟩
  · rw [← h0, ← hf, map_zero, h0']
  · have hft : LocallyOfFiniteType (A ⊗ A).hom := by
      change LocallyOfFiniteType (pullback.fst A.hom A.hom ≫ A.hom)
      infer_instance
    refine TorusEnd.hom_ext_of_points (existsUnique_hom_of_locally_regular existsUnique_point_of_ringHom
      (eq_of_valAt'_eq valAt'_rules existsUnique_point_of_ringHom) A' (A ⊗ A)
      (isReduced_tensorObj_complex A A hr hr inferInstance inferInstance) hft) fun y => ?_
    obtain ⟨z, hz⟩ := u.ex_onto (y ≫ fst A A)
    obtain ⟨w, hw⟩ := u.ex_onto (y ≫ snd A A)
    have hy : y = lift (u.ex z) (u.ex w) := by
      ext1 <;> simp [hz, hw]
    rw [hy, ← Category.assoc, ← Hom.mul_def, ← u.ex_add, ← hf, map_add, u'.ex_add, Hom.mul_def, ← Category.assoc,
      lift_map, ← hf, ← hf]

theorem exists_isMonHom_of_complementary (hamp : Out.AmpleSt) (P P' : Out.PolAV (Sp ℂ)) {g g' : ℕ}
    (u : HolUnif P.A P.L g) (u' : HolUnif P'.A P'.L g') {Hm : Matrix (Fin g) (Fin g) ℂ} {χ : u.Λ → ℂ}
    {Hm' : Matrix (Fin g') (Fin g') ℂ} {χ' : u'.Λ → ℂ}
    (hsec : ∀ (k : ℕ) θ, u.IsThetaFn Hm χ k θ → ∃ s, u.IsFnPow k s θ)
    (hfn : ∀ (k : ℕ) s, ∃ θ, u'.IsThetaFn Hm' χ' k θ ∧ u'.IsFnPow k s θ)
    (F : (Fin g → ℂ) →ₗ[ℂ] (Fin g' → ℂ)) (hF : ∀ l ∈ u.Λ, F l ∈ u'.Λ) (d : ℕ)
    (hd : ∀ z₀, ∃ G : (Fin g → ℂ) → ℂ, G z₀ ≠ 0 ∧
      ∀ θ, u'.IsThetaFn Hm' χ' 4 θ → u.IsThetaFn Hm χ d (fun z => θ (F z) * G z)) :
    ∃ f : P.A ⟶ P'.A, IsMonHom f ∧ ∀ z, u'.ex (F z) = u.ex z ≫ f := by
  have hsm := P.isAb.smooth
  have hr : IsReduced P.A.left := isReduced_of_smooth_complex _ P.A.hom hsm
  let Φ : (𝟙_ (Over (Sp ℂ)) ⟶ P.A) → (𝟙_ (Over (Sp ℂ)) ⟶ P'.A) := fun y => u'.ex (F (Function.surjInv u.ex_onto y))
  have hΦ : ∀ z, Φ (u.ex z) = u'.ex (F z) := fun z => by
    have h1 : Function.surjInv u.ex_onto (u.ex z) - z ∈ u.Λ := by
      rw [← u.ker]
      have := u.ex_add (Function.surjInv u.ex_onto (u.ex z) - z) z
      rw [sub_add_cancel, Function.surjInv_eq u.ex_onto] at this
      exact mul_eq_right.1 this.symm
    have := SectionTheta.ex_add_lattice u' (F z) ⟨_, hF _ h1⟩
    rwa [← map_add, add_sub_cancel] at this
  obtain ⟨m, s, hcov, hD⟩ := veryAmple_lbPow hamp ℂ P' 4 le_rfl
  choose θ hθ hθs using fun j => hfn 4 (s j)
  obtain ⟨f, hf, -⟩ := existsUnique_hom_of_locally_regular existsUnique_point_of_ringHom
      (eq_of_valAt'_eq valAt'_rules existsUnique_point_of_ringHom) P'.A P.A hr inferInstance Φ fun y => by
    obtain ⟨z₀, rfl⟩ := u.ex_onto y
    obtain ⟨i, hi⟩ := TorusEnd.exists_top_le_preimage_of_iSup_eq_top (u'.ex (F z₀)).left _ hcov
    obtain ⟨haff, r, hr, hgen⟩ := hD i
    have hmem := le_preimage_nonzeroLocus_iff u' P'.isLB (hθs i)
    obtain ⟨G, hG0, hG⟩ := hd z₀
    choose t ht using fun j => hsec d _ (hG _ (hθ j))
    obtain ⟨U, ρ, hU0, hU⟩ := exists_regular_quotients u P.isLB ht i (mul_ne_zero ((hmem _).1 hi) hG0)
    refine ⟨U, _, hU0, haff, fun y' hy' => ?_, fun ψ => ?_⟩
    · obtain ⟨z, rfl⟩ := u.ex_onto y'
      rw [hΦ]
      exact (hmem _).2 (left_ne_zero_of_mul (hU z hy').1)
    · obtain ⟨Q, rfl⟩ := hgen ψ
      refine ⟨MvPolynomial.eval₂ (RingHom.comp (P.A.hom.appLE ⊤ _ le_top).hom
        (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom) ρ Q, fun y' hy' => ?_⟩
      obtain ⟨z, rfl⟩ := u.ex_onto y'
      have h1 := left_ne_zero_of_mul (hU z hy').1
      have h2 := right_ne_zero_of_mul (hU z hy').1
      rw [hΦ, TorusEnd.valAt'_eval₂ _ _ hy', TorusEnd.valAt'_eval₂ _ _ ((hmem _).2 h1)]
      congr 2
      funext j
      rw [(hU z hy').2 j, valAt'_eq_div_of_mul u' P'.isLB (hθs i) (hθs j) (r j) (hr j) h1, mul_div_mul_right _ _ h2]
  have hfe : ∀ z, u'.ex (F z) = u.ex z ≫ f := fun z => by rw [hf, hΦ]
  exact ⟨f, isMonHom_of_lift u u' F f hfe, hfe⟩

end GlobalTheory.LatticeHom
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsNonzeroLocusLeOpenPolarisationComplex
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.KS

namespace GlobalTheory.AmpleBasis

open SectionRing

variable {K : Type} [Field K] {X : Scheme.{0}} (p : X ⟶ Sp K) (L : LB X)

def Extends (N : ℕ) (D : X.Opens) (t : Fam p L) (f : Γ(X, D)) (e : ℕ) : Prop :=
  ∃ σ ∈ secs p L (N * e), ∀ k,
    resG X (inf_le_right : D ⊓ chart L k ≤ _) (evalFam p L k σ) =
      resG X (inf_le_left : D ⊓ chart L k ≤ _) f *
        resG X (inf_le_right : D ⊓ chart L k ≤ _) (evalFam p L k t) ^ e

variable {p L} {N : ℕ} {D : X.Opens} {t : Fam p L}

theorem Extends.mul {f g : Γ(X, D)} {e e' : ℕ} (hf : Extends p L N D t f e)
    (hg : Extends p L N D t g e') : Extends p L N D t (f * g) (e + e') := by
  obtain ⟨σ, hσ, h⟩ := hf
  obtain ⟨τ, hτ, h'⟩ := hg
  refine ⟨σ * τ, ?_, fun k => ?_⟩
  · rw [mul_add]
    exact SetLike.GradedMul.mul_mem hσ hτ
  · simp only [map_mul]
    rw [h k, h' k, pow_add]
    ring

theorem Extends.add {f g : Γ(X, D)} {e : ℕ} (hf : Extends p L N D t f e)
    (hg : Extends p L N D t g e) : Extends p L N D t (f + g) e := by
  obtain ⟨σ, hσ, h⟩ := hf
  obtain ⟨τ, hτ, h'⟩ := hg
  refine ⟨σ + τ, add_mem hσ hτ, fun k => ?_⟩
  simp only [map_add]
  rw [h k, h' k, add_mul]

theorem extends_one (ht : t ∈ secs p L N) (e : ℕ) : Extends p L N D t 1 e := by
  refine ⟨t ^ e, ?_, fun k => ?_⟩
  · have hp := SetLike.pow_mem_graded e ht
    rwa [smul_eq_mul, mul_comm] at hp
  · rw [map_pow, map_pow, map_one]
    exact (_root_.one_mul _).symm

private theorem resG_constHom' {U V : X.Opens} (h : V ≤ U) (a : K) :
    resG X h (constHom p U a) = constHom p V a := by
  have hU : U ≤ p ⁻¹ᵁ ⊤ := fun _ _ => trivial
  have e : p.appLE ⊤ U hU ≫ X.presheaf.map (homOfLE h).op = p.appLE ⊤ V (h.trans hU) := by
    rw [Scheme.Hom.appLE_map]
  exact congrArg (fun φ => φ.hom ((Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom a)) e

theorem extends_const (a : K) : Extends p L N D t (constHom p D a) 0 := by
  refine ⟨fun j => constHom p (chart L j) a, ?_, fun k => ?_⟩
  · rw [mul_zero]
    intro i j
    rw [trans_zero, _root_.one_mul]
    change resG X _ (constHom p _ a) = resG X _ (constHom p _ a)
    rw [resG_constHom', resG_constHom']
  · rw [pow_zero, _root_.mul_one]
    change resG X _ (constHom p _ a) = resG X _ (constHom p _ a)
    rw [resG_constHom', resG_constHom']

private theorem extends_add (ht : t ∈ secs p L N) {f : Γ(X, D)} {e : ℕ}
    (hf : Extends p L N D t f e) (e' : ℕ) : Extends p L N D t f (e + e') := by
  simpa only [_root_.mul_one] using hf.mul (extends_one ht e')

theorem extends_eval₂ {J : Type} (ht : t ∈ secs p L N) (r : J → Γ(X, D))
    (hr : ∀ j, Extends p L N D t (r j) 1) (F : MvPolynomial J K) :
    ∃ e, Extends p L N D t (MvPolynomial.eval₂ (constHom p D) r F) e := by
  induction F using MvPolynomial.induction_on
  next a =>
    refine ⟨0, ?_⟩
    rw [MvPolynomial.eval₂_C]
    exact extends_const a
  next P Q hP hQ =>
    obtain ⟨a, ha⟩ := hP
    obtain ⟨b, hb⟩ := hQ
    refine ⟨a + b, ?_⟩
    rw [MvPolynomial.eval₂_add]
    refine (extends_add ht ha b).add ?_
    rw [add_comm a b]
    exact extends_add ht hb a
  next P j hP =>
    obtain ⟨a, ha⟩ := hP
    refine ⟨a + 1, ?_⟩
    rw [MvPolynomial.eval₂_mul, MvPolynomial.eval₂_X]
    exact ha.mul (hr j)

private theorem basicOpen_resG' {U V : X.Opens} (h : V ≤ U) (x : Γ(X, U)) :
    X.basicOpen (resG X h x) = V ⊓ X.basicOpen x :=
  Scheme.basicOpen_res X x (homOfLE h).op

theorem exists_locus (s : (lbPow L N).Sec) (f : Γ(X, Out.nonzeroLocus s)) (e : ℕ)
    (hf : Extends p L N (Out.nonzeroLocus s) (secEquiv p L N s : Fam p L) f e)
    (y : X) (hy : y ∈ X.basicOpen f) :
    ∃ (n : ℕ) (σ : (lbPow L n).Sec), y ∈ Out.nonzeroLocus σ ∧ Out.nonzeroLocus σ ≤ X.basicOpen f := by
  obtain ⟨σ, hσ, h⟩ := hf
  have hmem : σ * (secEquiv p L N s : Fam p L) ∈ secs p L (N * e + N) :=
    SetLike.GradedMul.mul_mem hσ (secEquiv p L N s).2
  have key : ∀ k, (Out.nonzeroLocus s ⊓ chart L k) ⊓
      X.basicOpen (evalFam p L k (σ * (secEquiv p L N s : Fam p L))) =
      (Out.nonzeroLocus s ⊓ chart L k ⊓ X.basicOpen f) ⊓
        (Out.nonzeroLocus s ⊓ chart L k ⊓ X.basicOpen (evalFam p L k (secEquiv p L N s : Fam p L))) := by
    intro k
    rw [← basicOpen_resG' (inf_le_right : Out.nonzeroLocus s ⊓ chart L k ≤ _), map_mul, map_mul, h k,
      _root_.mul_assoc, ← pow_succ, Scheme.basicOpen_mul, Scheme.basicOpen_pow _ _ e.succ_pos,
      basicOpen_resG', basicOpen_resG']
  refine ⟨N * e + N, (secEquiv p L (N * e + N)).symm ⟨_, hmem⟩, ?_, ?_⟩
  · change y ∈ ⨆ k, X.basicOpen (evalFam p L k (σ * (secEquiv p L N s : Fam p L)))
    have hyD : y ∈ Out.nonzeroLocus s := X.basicOpen_le f hy
    obtain ⟨k, hk⟩ := TopologicalSpace.Opens.mem_iSup.mp (show y ∈ ⨆ k, X.basicOpen (s.f k) from hyD)
    have hkc : y ∈ chart L k := X.basicOpen_le _ hk
    have hmemk : y ∈ (Out.nonzeroLocus s ⊓ chart L k) ⊓
        X.basicOpen (evalFam p L k (σ * (secEquiv p L N s : Fam p L))) := by
      rw [key k]
      exact ⟨⟨⟨hyD, hkc⟩, hy⟩, ⟨⟨hyD, hkc⟩, hk⟩⟩
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨k, hmemk.2⟩
  · change (⨆ k, X.basicOpen (evalFam p L k (σ * (secEquiv p L N s : Fam p L)))) ≤ X.basicOpen f
    refine iSup_le fun k z hz => ?_
    have hz2 := hz
    rw [map_mul, Scheme.basicOpen_mul] at hz2
    have hz' : z ∈ X.basicOpen (s.f k) := hz2.2
    have hzD : z ∈ Out.nonzeroLocus s := TopologicalSpace.Opens.mem_iSup.mpr ⟨k, hz'⟩
    have hkc : z ∈ chart L k := X.basicOpen_le _ hz'
    have hzk : z ∈ (Out.nonzeroLocus s ⊓ chart L k) ⊓
        X.basicOpen (evalFam p L k (σ * (secEquiv p L N s : Fam p L))) := ⟨⟨hzD, hkc⟩, hz⟩
    rw [key k] at hzk
    exact hzk.1.2

end GlobalTheory.AmpleBasis

namespace GlobalTheory

open SectionRing AmpleBasis

theorem exists_nonzeroLocus_le : Out.Laws → ∀ (P₀ : Out.PolAV (Sp ℂ)) (O : P₀.A.left.Opens) (y : P₀.A.left), y ∈ O → ∃ (n : ℕ) (σ : (lbPow P₀.L n).Sec), y ∈ Out.nonzeroLocus σ ∧ Out.nonzeroLocus σ ≤ O := by
  intro hL P₀ O y hy
  obtain ⟨m, s, hcov, hs⟩ := veryAmple_lbPow hL.ample ℂ P₀ 4 le_rfl
  have hyt : y ∈ (⨆ i, Out.nonzeroLocus (s i)) := by
    rw [hcov]
    trivial
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp hyt
  obtain ⟨haff, r, hr, hpoly⟩ := hs i
  obtain ⟨f, hfO, hyf⟩ := haff.exists_basicOpen_le ⟨y, hy⟩ hi
  obtain ⟨F, hF⟩ := hpoly f
  have hrj : ∀ j, Extends P₀.A.hom P₀.L 4 (Out.nonzeroLocus (s i)) (secEquiv P₀.A.hom P₀.L 4 (s i) : Fam P₀.A.hom P₀.L)
      (r j) 1 := by
    intro j
    refine ⟨secEquiv P₀.A.hom P₀.L 4 (s j), ?_, fun k => ?_⟩
    · rw [Nat.mul_one]
      exact (secEquiv P₀.A.hom P₀.L 4 (s j)).2
    · rw [pow_one]
      exact hr j k
  obtain ⟨e, he⟩ := extends_eval₂ (secEquiv P₀.A.hom P₀.L 4 (s i)).2 r hrj F
  have he' : Extends P₀.A.hom P₀.L 4 (Out.nonzeroLocus (s i))
      (secEquiv P₀.A.hom P₀.L 4 (s i) : Fam P₀.A.hom P₀.L) f e := by
    rw [hF]
    exact he
  obtain ⟨n, σ, hyσ, hσf⟩ := exists_locus (s i) f e he' y hyf
  exact ⟨n, σ, hyσ, hσf.trans hfO⟩

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsTripleOfFieldExtension
section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory.TripleDescent

variable {S S' : Scheme.{0}} {f : S' ⟶ S}

theorem lift_left_fst {T X Y : Over S} (a : T ⟶ X) (b : T ⟶ Y) : (lift a b).left ≫ (fst X Y).left = a.left :=
  congrArg (fun q => q.left) (lift_fst a b)

theorem lift_left_snd {T X Y : Over S} (a : T ⟶ X) (b : T ⟶ Y) : (lift a b).left ≫ (snd X Y).left = b.left :=
  congrArg (fun q => q.left) (lift_snd a b)

theorem isPullback_tensor {X Y : Over S} {X' Y' : Over S'} {a : X'.left ⟶ X.left} {b : Y'.left ⟶ Y.left}
    (ha : IsPullback a X'.hom X.hom f) (hb : IsPullback b Y'.hom Y.hom f) (c : (X' ⊗ Y').left ⟶ (X ⊗ Y).left)
    (c₁ : c ≫ (fst X Y).left = (fst X' Y').left ≫ a) (c₂ : c ≫ (snd X Y).left = (snd X' Y').left ≫ b) :
    IsPullback c (X' ⊗ Y').hom (X ⊗ Y).hom f := by
  have p : IsPullback (snd X Y).left (fst X Y).left Y.hom X.hom := (IsPullback.of_hasPullback X.hom Y.hom).flip
  have p' : IsPullback (snd X' Y').left (fst X' Y').left Y'.hom X'.hom :=
    (IsPullback.of_hasPullback X'.hom Y'.hom).flip
  have q := p'.paste_horiz hb
  rw [← c₂, ← ha.w] at q
  have r := (IsPullback.of_right q c₁ p).paste_vert ha
  rwa [Over.w, Over.w] at r

variable {G : Over S} {G' : Over S'} [GrpObj G] [IsCommMonObj G] [GrpObj G'] [IsCommMonObj G']
  {φ : G'.left ⟶ G.left} {L : LB G.left} {L' : LB G'.left}

theorem lbIso_cubeLB_pull (h : IsGrpPullback G' G f φ) (hw : LBIso L' (L.pull φ)) {T' : Over S'} {T : Over S} {n : ℕ}
    (x' : Fin n → (T' ⟶ G')) (x : Fin n → (T ⟶ G)) (U : Over.mk (T'.hom ≫ f) ⟶ T)
    (hx : ∀ i, pushPt h.1.w (x' i) = U ≫ x i) :
    LBIso (cubeLB G' x' L') ((cubeLB G x L).pull U.left) := by
  obtain ⟨w, hw⟩ := hw
  exact (iso_linComb ((isGen_iff w).1 hw) _ _).chartPull (chartPullId _)
    (chartPullOut L _ _ U.left _ fun I => psum_push h x' x U hx I.down)

theorem exists_gen_cubeLB_pull (h : IsGrpPullback G' G f φ) (hL : L.IsLB) (hL' : L'.IsLB) (hw : LBIso L' (L.pull φ))
    {T' : Over S'} {T : Over S} {n : ℕ} (x' : Fin n → (T' ⟶ G')) (x : Fin n → (T ⟶ G))
    (U : Over.mk (T'.hom ≫ f) ⟶ T) (hx : ∀ i, pushPt h.1.w (x' i) = U ≫ x i) (t : (cubeLB G' x' L').Gen)
    (ht : t.IsGen) : ∃ t : ((cubeLB G x L).pull U.left).Gen, t.IsGen := by
  obtain ⟨w, hw⟩ := hw
  obtain ⟨c, hc, -⟩ := exists_up ((isGen_iff w).1 hw) hL hL' t ht
  exact gen_chartPull (chartPullOut L _ _ U.left _ fun I => psum_push h x' x U hx I.down) c hc

end GlobalTheory.TripleDescent

open GlobalTheory.TripleDescent in

theorem GlobalTheory.exists_triple_of_fieldExtension : Out.Laws → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (K₀ K : Type) [Field K₀] [Field K] (i : K₀ →+* K) (τ : SAB H (Sp K)) (A₀ : Over (Sp K₀)) [GrpObj A₀] (φ : τ.G.left ⟶ A₀.left) (L₀ : LB A₀.left) (r : OAct (𝓞 E) A₀), IsAbelianScheme A₀ → IsGrpPullback τ.G A₀ (spMap i) φ → L₀.IsLB → LBIso τ.PP.L (L₀.pull φ) → (∀ c, (τ.act.act c).left ≫ φ = φ ≫ (r.act c).left) → ∃ (τ₀ : SAB H (Sp K₀)) (e : τ₀.G ≅ A₀), IsMonHom e.hom ∧ LBIso τ₀.PP.L (L₀.pull e.hom.left) ∧ ∀ c, τ₀.act.act c ≫ e.hom = e.hom ≫ r.act c := by
  intro hLaws E _ _ _ H K₀ K _ _ i τ A₀ _ φ L₀ r hA h hL₀ hw hact
  have := hA.comm
  have A₂ := AbelianSchemeGerms.isAbelianScheme_tensor A₀ A₀ hA hA
  have A₃ := AbelianSchemeGerms.isAbelianScheme_tensor A₀ _ hA A₂
  have lb : ∀ {S : Scheme.{0}} {B : Over S} [GrpObj B] [IsCommMonObj B] {T : Over S} {n : ℕ} (x : Fin n → (T ⟶ B))
      {L : LB B.left}, L.IsLB → (cubeLB B x L).IsLB := fun x L hL => DVR.linComb_isLB _ hL _ _
  have pa : ∀ {T : Over (Sp K)} (x : T ⟶ τ.G) a,
      pushPt h.1.w (x ≫ τ.act.act a) = pushPt h.1.w x ≫ r.act a := fun x a =>
    Over.OverMorphism.ext (by
      show (x.left ≫ _) ≫ _ = (x.left ≫ _) ≫ _
      rw [Category.assoc, hact, Category.assoc])
  have hP := τ.PP.isLB
  let U₁ := pushPt h.1.w (𝟙 τ.G)
  have e₁ : U₁.left = φ := Category.id_comp _
  let U₂ := lift (pushPt h.1.w (fst τ.G τ.G)) (pushPt h.1.w (snd τ.G τ.G))
  let U₃ := lift (pushPt h.1.w (x3 τ.G 0)) (lift (pushPt h.1.w (x3 τ.G 1)) (pushPt h.1.w (x3 τ.G 2)))
  have u₁ : U₂.left ≫ (fst A₀ A₀).left = (fst τ.G τ.G).left ≫ φ := lift_left_fst _ _
  have u₂ : U₂.left ≫ (snd A₀ A₀).left = (snd τ.G τ.G).left ≫ φ := lift_left_snd _ _
  have P₂ : IsPullback U₂.left (τ.G ⊗ τ.G).hom (A₀ ⊗ A₀).hom (spMap i) := isPullback_tensor h.1 h.1 _ u₁ u₂
  have P₃ : IsPullback U₃.left (τ.G ⊗ τ.G ⊗ τ.G).hom (A₀ ⊗ A₀ ⊗ A₀).hom (spMap i) := by
    refine isPullback_tensor h.1 P₂ _ (lift_left_fst _ _) ?_
    refine (lift_left_snd _ _).trans ?_
    apply pullback.hom_ext
    · refine (lift_left_fst _ _).trans (Eq.symm ?_)
      exact (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) u₁).trans (Category.assoc _ _ _).symm)
    · refine (lift_left_snd _ _).trans (Eq.symm ?_)
      exact (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) u₂).trans (Category.assoc _ _ _).symm)
  have D₁ := GlobalTheory.T.lineBundle_trivial_iso_descend_field K₀ K i _ _ A₀.hom _ _ hA.smooth hA.proper hA.geomConnected h.1
  have D₂ := GlobalTheory.T.lineBundle_trivial_iso_descend_field K₀ K i _ _ (A₀ ⊗ A₀).hom _ _ A₂.smooth A₂.proper A₂.geomConnected P₂
  have D₃ := GlobalTheory.T.lineBundle_trivial_iso_descend_field K₀ K i _ _ (A₀ ⊗ A₀ ⊗ A₀).hom _ _ A₃.smooth A₃.proper A₃.geomConnected P₃
  have hT : ∃ t : LB.Gen (Theta A₀ L₀), t.IsGen := D₃.1 _ (lb _ hL₀)
    (exists_gen_cubeLB_pull h hL₀ hP hw (x3 τ.G) (x3 A₀) U₃ (fun j => by fin_cases j <;> simp [x3, U₃])
      τ.cub.t τ.cub.isGen)
  have ha : ∀ a, LBIso (cubeLB A₀ ![fst A₀ A₀ ≫ r.act a, snd A₀ A₀] L₀)
      (cubeLB A₀ ![fst A₀ A₀, snd A₀ A₀ ≫ r.act (H.bar a)] L₀) := fun a => by
    have k₁ := lbIso_cubeLB_pull h hw ![fst τ.G τ.G ≫ τ.act.act a, snd τ.G τ.G]
      ![fst A₀ A₀ ≫ r.act a, snd A₀ A₀] U₂ (fun j => by
        fin_cases j
        · exact (pa _ a).trans (by simp [U₂])
        · simp [U₂])
    have k₂ := lbIso_cubeLB_pull h hw ![fst τ.G τ.G, snd τ.G τ.G ≫ τ.act.act (H.bar a)]
      ![fst A₀ A₀, snd A₀ A₀ ≫ r.act (H.bar a)] U₂ (fun j => by
        fin_cases j
        · simp [U₂]
        · exact (pa _ _).trans (by simp [U₂]))
    exact D₂.2 _ _ (lb _ hL₀) (lb _ hL₀) (LBIso.trans (pull_isLB (lb _ hL₀) _) (by exact lb _ hP) (pull_isLB (lb _ hL₀) _)
      k₁.symm (LBIso.trans (by exact lb _ hP) (by exact lb _ hP) (pull_isLB (lb _ hL₀) _) (τ.adj a) k₂))
  have hp : LBIso L₀ (cubeLB A₀ ![𝟙 A₀, r.act H.w0] L₀) := by
    have k := lbIso_cubeLB_pull h hw ![𝟙 τ.G, τ.act.act H.w0] ![𝟙 A₀, r.act H.w0] U₁ (fun j => by
      fin_cases j
      · simp [U₁]
      · exact (congrArg (pushPt h.1.w) (Category.id_comp _).symm).trans (pa _ _))
    rw [e₁] at k
    exact D₁.2 _ _ hL₀ (lb _ hL₀) (LBIso.trans (pull_isLB hL₀ _) hP (pull_isLB (lb _ hL₀) _)
      hw.symm (LBIso.trans hP (by exact lb _ hP) (pull_isLB (lb _ hL₀) _) τ.prim k))
  obtain ⟨PP, cub, sym, iso, -, prim, adj⟩ :=
    GlobalTheory.PrimNorm.exists_primitive_normalisation hLaws.globalFns E H _ A₀ r L₀ hA hL₀ hT ha
  refine ⟨⟨A₀, GlobalTheory.isSemiAbelian_of_isAbelianScheme A₀ hA, r, PP, cub, sym, adj, prim⟩, Iso.refl _,
    inferInstanceAs (IsMonHom (𝟙 A₀)), ?_, fun c => (Category.comp_id _).trans (Category.id_comp _).symm⟩
  exact (LBIso.trans PP.isLB (lb _ hL₀) hL₀ iso hp.symm).chartPull (chartPullId _) (chartPullPull L₀ _ (𝟙 _) rfl)
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.LogDerivativePrincipalPolarisationIndependentStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.KS
theorem _root_.GlobalTheory.T.logDerivative_principalPolarisation_independent : ∀ (K : Type) [Field K] (P₀ : Out.PolAV (Sp K)) (g : ℕ) (v : Fin g → (epsR K ⟶ P₀.A)) (dd : Fin g → ∀ O : P₀.A.left.Opens, Γ(P₀.A.left, O) → Γ(P₀.A.left, O)), IsLieBasis v → (∀ a, IsInvDer (v a) (dd a)) → ∀ (X : Scheme.{0}) (m : P₀.A.left ⟶ X) (L : LB X), L.IsLB → LBIso P₀.L (L.pull m) → (∃ φ, IsDlog m L dd φ) ∧ ∀ φ, IsDlog m L dd φ → (∀ a, IsCoc _ (φ a)) ∧ ∀ c, IsCob _ (lc P₀.A.hom c φ) → c = 0 := by
  first | exact @GlobalTheory.KS.DlogPol.dlog_independent | exact GlobalTheory.KS.DlogPol.dlog_independent | (intros; apply GlobalTheory.KS.DlogPol.dlog_independent <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.RigidifiedSymmetricKernelTrivialDescendFieldExtStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rigidified_symmetric_kernelTrivial_descend_fieldExt : ∀ (K₀ K : Type) [Field K₀] [Field K] (i : K₀ →+* K) (A₀ : Over (Sp K₀)) (A : Over (Sp K)) [GrpObj A₀] [GrpObj A] (φ : A.left ⟶ A₀.left) (L₀ : LB A₀.left) (L : LB A.left), IsAbelianScheme A₀ → IsGrpPullback A A₀ (spMap i) φ → L₀.IsLB → L.IsLB → LBIso L (L₀.pull φ) → (Out.Rigidified A L → Out.Rigidified A₀ L₀) ∧ (Out.Sym A L → Out.Sym A₀ L₀) ∧ (Out.KTriv A L → Out.KTriv A₀ L₀) := by
  first | exact @GlobalTheory.PolDescent.rigidified_sym_kTriv_descend | exact GlobalTheory.PolDescent.rigidified_sym_kTriv_descend | (intros; apply GlobalTheory.PolDescent.rigidified_sym_kTriv_descend <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.SectionCoordinatesPullIsoNonzeroLocusStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sectionCoordinates_pull_iso_nonzeroLocus : ∀ (X : Scheme.{0}) (M : LB X) (I : Type) (th : I → M.Sec), M.IsLB → (∀ (X' : Scheme.{0}) (π : X' ⟶ X), ∃ th' : I → (M.pull π).Sec, ∀ (R : Type) [CommRing R] (x : Sp R ⟶ X') (v : I → R), SecCoord (M.pull π) th' x v ↔ SecCoord M th (x ≫ π) v) ∧ (∀ M' : LB X, M'.IsLB → LBIso M M' → ∃ th' : I → M'.Sec, ∀ (R : Type) [CommRing R] (x : Sp R ⟶ X) (v : I → R), SecCoord M' th' x v ↔ SecCoord M th x v) ∧ ∀ (R : Type) [CommRing R] (x : Sp R ⟶ X) (v : I → R) (i : I) (p : Sp R), SecCoord M th x v → (x p ∈ Out.nonzeroLocus (th i) ↔ v i ∉ p.asIdeal) := by
  first | exact @GlobalTheory.ZM.CoordMove.secCoord_pull_iso_locus | exact GlobalTheory.ZM.CoordMove.secCoord_pull_iso_locus | (intros; apply GlobalTheory.ZM.CoordMove.secCoord_pull_iso_locus <;> assumption)
end

