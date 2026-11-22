import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2403
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2813
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0108
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsWithoutCohomology
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AppellHumbertRealMultiplication
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2535
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2584
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2832
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2231
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0630
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2781
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0078
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0029
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0007

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AmpleRigidLevelRigid
section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
  CartesianMonoidalCategory MonObj TensorProduct NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AmpleRigid

open GlobalTheory.CechPic GlobalTheory.RealMult

set_option autoImplicit false in
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct NumberField in
attribute [local instance] Over.cartesianMonoidalCategory in

theorem _root_.GlobalTheory.AmpleRigid.mul_comp_of_grpPullback_id {S : Scheme.{0}} {G' G : Over S} [GrpObj G'] [GrpObj G]
    (f : G' ⟶ G) (h : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsGrpPullback G' G (𝟙 S) f.left) {T : Over S} (x y : T ⟶ G') :
    (x * y) ≫ f = (x ≫ f) * (y ≫ f) := by
  have H := h.2 T x y
  revert H
  generalize hg : T.hom ≫ 𝟙 S = g
  rw [Category.comp_id] at hg
  subst hg
  intro H
  exact Over.OverMorphism.ext (H (x ≫ f) (y ≫ f) rfl rfl).symm

set_option autoImplicit false in
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct NumberField in
attribute [local instance] Over.cartesianMonoidalCategory in

theorem _root_.GlobalTheory.AmpleRigid.isMonHom_of_mul_comp {S : Scheme.{0}} {G H : Over S} [GrpObj G] [GrpObj H]
    (e : G ⟶ H) (mul : ∀ (T : Over S) (x y : T ⟶ G), (x * y) ≫ e = (x ≫ e) * (y ≫ e)) :
    IsMonHom e := by
  have hone : (1 : 𝟙_ (Over S) ⟶ G) ≫ e = 1 := by
    have h1 := mul (𝟙_ (Over S)) 1 1
    rw [_root_.mul_one] at h1
    exact _root_.left_eq_mul.mp h1
  refine ⟨?_, ?_⟩
  · simpa [Hom.one_def] using hone
  · have h2 := mul (G ⊗ G) (fst G G) (snd G G)
    simpa [Hom.mul_def] using h2

variable {F : Type} [Field F] [NumberField F] {𝔠 : FracId F}

theorem exists_totPos_mem (𝔠 : FracId F) : ∃ c : 𝔠.elt, IsTotPos (c : F) := by
  obtain ⟨x, hx0, hx⟩ := FractionalIdeal.exists_ne_zero_mem_isInteger (𝔠.ne_zero)
  refine ⟨⟨x • algebraMap (𝓞 F) F x, Submodule.smul_mem _ x hx⟩, fun τ => ?_⟩
  have hx' : algebraMap (𝓞 F) F x ≠ 0 := (map_ne_zero_iff _ (FaithfulSMul.algebraMap_injective (𝓞 F) F)).2 hx0
  have hτ : τ (algebraMap (𝓞 F) F x) ≠ 0 := (map_ne_zero τ).2 hx'
  show 0 < τ (x • algebraMap (𝓞 F) F x)
  rw [Algebra.smul_def, map_mul]
  exact mul_self_pos.2 hτ

theorem pull_cls_diag {S : Scheme.{0}} (X : Obj F 𝔠 S) (ψ : X.A.left ⟶ X.A.left) (hψ : X.IsPullBy X (𝟙 _) ψ)
    (c : 𝔠.elt) :
    pull ψ (cls (X.diag c) (pull_isLB (X.isLB c) _)) = cls (X.diag c) (pull_isLB (X.isLB c) _) := by
  obtain ⟨φ₂, hsq, hiso⟩ := hψ.pol
  have hw : ψ ≫ X.A.hom = X.A.hom := by simpa using hψ.grp.1.w
  have hw2 : φ₂ ≫ (X.A ⊗ X.A).hom = (X.A ⊗ X.A).hom := by
    calc φ₂ ≫ (X.A ⊗ X.A).hom = φ₂ ≫ (fst X.A X.A).left ≫ X.A.hom := by rw [Over.w]
      _ = (fst X.A X.A).left ≫ ψ ≫ X.A.hom := by rw [← Category.assoc, hsq.1, Category.assoc]
      _ = (X.A ⊗ X.A).hom := by rw [hw, Over.w]
  let Ψ : X.A ⟶ X.A := Over.homMk ψ hw
  let Φ : X.A ⊗ X.A ⟶ X.A ⊗ X.A := Over.homMk φ₂ hw2
  have e : Ψ ≫ lift (𝟙 X.A) (𝟙 X.A) = lift (𝟙 X.A) (𝟙 X.A) ≫ Φ := by
    apply CartesianMonoidalCategory.hom_ext
    · apply Over.OverMorphism.ext
      simp only [Category.assoc, lift_fst, Category.comp_id, Over.comp_left]
      rw [show Φ.left = φ₂ from rfl, hsq.1, ← Category.assoc, ← Over.comp_left, lift_fst]
      rfl
    · apply Over.OverMorphism.ext
      simp only [Category.assoc, lift_snd, Category.comp_id, Over.comp_left]
      rw [show Φ.left = φ₂ from rfl, hsq.2, ← Category.assoc, ← Over.comp_left, lift_snd]
      rfl
  have e' : ψ ≫ (lift (𝟙 X.A) (𝟙 X.A)).left = (lift (𝟙 X.A) (𝟙 X.A)).left ≫ φ₂ := congrArg (·.left) e
  have h1 : pull φ₂ (cls (X.P c) (X.isLB c)) = cls (X.P c) (X.isLB c) :=
    ((cls_eq_iff (X.isLB c) (pull_isLB (X.isLB c) φ₂)).2 (hiso c)).symm
  unfold Obj.diag
  rw [cls_pull (X.isLB c), ← pull_comp, e', pull_comp, h1]

theorem eq_id_of_level_fixed (hS : SerreAmpleSt) {K : Type} [Field K] [IsAlgClosed K] (X : Obj F 𝔠 (Sp K))
    {N : ℕ} (hN : 3 ≤ N) (hNK : (N : K) ≠ 0) (β : X.Level N) (ψ : X.A.left ⟶ X.A.left)
    (hψ : X.IsPullBy X (𝟙 _) ψ) (hfix : ∀ i, (β.pt i).left ≫ ψ = (β.pt i).left) : ψ = 𝟙 _ := by
  have hw : ψ ≫ X.A.hom = X.A.hom := by simpa using hψ.grp.1.w
  haveI : IsIso ψ := hψ.grp.1.isIso_fst_of_isIso
  let σ : X.A ≅ X.A := Over.isoMk (asIso ψ) hw
  have hσl : σ.hom.left = ψ := rfl
  have hmul : ∀ (T : Over (Sp K)) (x y : T ⟶ X.A), (x * y) ≫ σ.hom = (x ≫ σ.hom) * (y ≫ σ.hom) :=
    fun T x y => mul_comp_of_grpPullback_id σ.hom hψ.grp x y
  haveI hmon : IsMonHom σ.hom := isMonHom_of_mul_comp σ.hom hmul
  obtain ⟨c, hc⟩ := exists_totPos_mem 𝔠
  have hpt : ∀ i, β.pt i ≫ σ.hom = β.pt i := fun i => Over.OverMorphism.ext (hfix i)
  have hact : ∀ a, X.rm.act a ≫ σ.hom = σ.hom ≫ X.rm.act a := fun a => Over.OverMorphism.ext (hψ.act a)
  have key := hS K X.A X.ab (X.diag c) (pull_isLB (X.isLB c) _) (X.pos c hc) N hN hNK σ hmon
    (pull_cls_diag X ψ hψ c) (fun Ω _ _ t x hx => by
      obtain ⟨a, b, rfl⟩ := β.surj Ω t x hx
      rw [hmul, Category.assoc, Category.assoc, hact, ← Category.assoc (β.pt 0), hpt, Category.assoc,
        Category.assoc, hact, ← Category.assoc (β.pt 1), hpt])
  exact congrArg (·.left) key

theorem levelRigid_of_serreAmple : SerreAmpleSt → LevelRigidSt := by
  intro hS F _ _ 𝔠 N hN R _ hNR X β g hg hfix
  have hw : g ≫ X.A.hom = X.A.hom := by simpa using hg.grp.1.w
  let σ : X.A ⟶ X.A := Over.homMk g hw
  haveI : IsMonHom σ := isMonHom_of_mul_comp σ (fun T x y => mul_comp_of_grpPullback_id σ hg.grp x y)
  have key : σ = 𝟙 _ := by
    refine eq_id_of_forall_geometric_fibre laws_without_cohomology.1 X.A X.ab σ (IsMonHom.one_hom σ)
      fun t => ?_
    let K : Type := AlgebraicClosure ((Sp R).residueField t)
    let f : Sp K ⟶ Sp R :=
      Spec.map (CommRingCat.ofHom (algebraMap ((Sp R).residueField t) K)) ≫ (Sp R).fromSpecResidueField t
    obtain ⟨X', β', φ, hφ, hpt⟩ := Obj.exists_isLevelPull β f
    have h1 : X'.IsPullBy X (𝟙 _ ≫ f) (φ ≫ g) := by
      have := hφ.comp hg
      rwa [Category.comp_id, ← Category.id_comp f] at this
    obtain ⟨ψ, hψ, hψφ⟩ := h1.cancel hφ
    have hNK : (N : K) ≠ 0 := by
      have hu := hNR.map (Spec.preimage f).hom
      rw [map_natCast] at hu
      exact hu.ne_zero
    have hψw : ψ ≫ X'.A.hom = X'.A.hom := by simpa using hψ.grp.1.w
    have hψ1 : ψ = 𝟙 _ := eq_id_of_level_fixed hS X' hN hNK β' ψ hψ fun i => by
      refine hφ.grp.1.hom_ext ?_ ?_
      · rw [Category.assoc, hψφ, ← Category.assoc, hpt i, Category.assoc, hfix i]
      · rw [Category.assoc, hψw]
    refine ⟨Sp K, X'.A.left, f, φ, X'.A.hom, (default : PrimeSpectrum K), ?_, hφ.grp.1, ?_⟩
    · exact (Scheme.Hom.comp_apply _ _ _).trans (Scheme.fromSpecResidueField_apply t _)
    · change φ ≫ g = φ
      rw [← hψφ, hψ1, Category.id_comp]
  exact congrArg (·.left) key

end GlobalTheory.AmpleRigid
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AppellHumbertDiagonalReal
section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult GlobalTheory.TorusRM
open scoped nonZeroDivisors

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.RiemInt

open GlobalTheory.RosatiAH GlobalTheory.AppellHumbertTrivial

theorem im_hermForm_int {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} {g : ℕ} (hL : L.IsLB) (u : HolUnif A L g)
    {Hm : Matrix (Fin g) (Fin g) ℂ} {χ : u.Λ → ℂ} (h : IsFactorAH u Hm χ) (l m : u.Λ) :
    ∃ n : ℤ, (hermForm Hm l m).im = n := by
  have hper : ∀ (l : u.Λ) z, u.ex (z + l) = u.ex z := fun l z => by
    rw [u.ex_add, (u.ker l).2 l.2, _root_.mul_one]
  obtain ⟨i, hi⟩ := PullHermitian.exists_chart (u.ex 0).left hL
  have hil : ⊤ ≤ (u.ex (0 + l)).left ⁻¹ᵁ L.U i := by rwa [hper]
  have him : ⊤ ≤ (u.ex (0 + m)).left ⁻¹ᵁ L.U i := by rwa [hper]
  have hlm : ⊤ ≤ (u.ex (0 + l + m)).left ⁻¹ᵁ L.U i := by rwa [hper]
  have h1 := h.2.2 l i 0 hi
  have h2 := h.2.2 m i _ hil
  have h3 := h.2.2 m i 0 hi
  have h4 := h.2.2 l i _ him
  have hne := u.fr_ne i _ hlm
  have hs : hermForm Hm m l = star (hermForm Hm l m) := by
    unfold hermForm
    rw [← Matrix.star_dotProduct_star, Matrix.star_mulVec, star_star, h.1.eq, Matrix.dotProduct_mulVec]
  have hχl : χ l ≠ 0 := norm_ne_zero_iff.1 (by rw [h.2.1]; exact one_ne_zero)
  have hχm : χ m ≠ 0 := norm_ne_zero_iff.1 (by rw [h.2.1]; exact one_ne_zero)
  rw [h2] at h1
  rw [h4, h1] at h3
  simp only [zero_add, zero_dotProduct, mul_zero] at h3 hne
  rw [add_comm (m : Fin g → ℂ) l] at h3
  unfold hermForm at hs ⊢
  rw [hs] at h3
  generalize (l : Fin g → ℂ) ⬝ᵥ Hm.mulVec (star (l : Fin g → ℂ)) = a at h3
  generalize (m : Fin g → ℂ) ⬝ᵥ Hm.mulVec (star (m : Fin g → ℂ)) = b at h3
  generalize (l : Fin g → ℂ) ⬝ᵥ Hm.mulVec (star (m : Fin g → ℂ)) = c at h3 ⊢
  simp only [Complex.exp_add] at h3
  have he : Complex.exp (Real.pi * c) = Complex.exp (Real.pi * star c) := by
    refine mul_right_cancel₀ (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero hχl hχm)
      (Complex.exp_ne_zero (Real.pi / 2 * a))) (Complex.exp_ne_zero (Real.pi / 2 * b))) hne) ?_
    linear_combination h3
  obtain ⟨n, hn⟩ := Complex.exp_eq_exp_iff_exists_int.1 he
  refine ⟨n, ?_⟩
  have := congrArg Complex.im hn
  simp at this
  have hp := Real.pi_pos
  refine mul_left_cancel₀ (a := 2 * Real.pi) (by positivity) ?_
  linear_combination this

variable {g : ℕ}

theorem diag_eq_two_mul (Hc H2 : Matrix (Fin (g + g)) (Fin (g + g)) ℂ)
    (hSc : ∀ x y x' y', hermForm Hc (Fin.append x y) (Fin.append x' y') = hermForm Hc (Fin.append y x) (Fin.append y' x'))
    (hS2 : ∀ x y x' y', hermForm H2 (Fin.append x y) (Fin.append x' y') = hermForm H2 (Fin.append y x) (Fin.append y' x'))
    (hM2 : ∀ x y x' y', hermForm H2 (Fin.append x y) (Fin.append x' y') =
      hermForm Hc (Fin.append x ((2 : ℂ) • y)) (Fin.append x' ((2 : ℂ) • y'))) (z w : Fin g → ℂ) :
    hermForm Hc (Fin.append z z) (Fin.append w w) = 2 * hermForm Hc (Fin.append z 0) (Fin.append 0 w) := by
  have hA : ∀ x x', hermForm Hc (Fin.append x 0) (Fin.append x' 0) = 0 := by
    intro x x'
    have e1 := hM2 x 0 x' 0
    have e2 := hS2 x 0 x' 0
    have e3 := hM2 0 x 0 x'
    have e4 := hSc x 0 x' 0
    simp only [smul_zero] at e1
    have e5 : Fin.append (0 : Fin g → ℂ) ((2 : ℂ) • x) = (2 : ℂ) • Fin.append 0 x := by
      rw [← append_smul, smul_zero]
    have e6 : Fin.append (0 : Fin g → ℂ) ((2 : ℂ) • x') = (2 : ℂ) • Fin.append 0 x' := by
      rw [← append_smul, smul_zero]
    rw [e5, e6, hermForm_smul_left, hermForm_smul_right] at e3
    have hs : (star (2 : ℂ)) = 2 := by simp
    rw [hs] at e3
    linear_combination (-1/3 : ℂ) * (-e1 + e2 + e3 - 4 * e4)
  have hA2 : ∀ y y', hermForm Hc (Fin.append 0 y) (Fin.append 0 y') = 0 := by
    intro y y'
    rw [← hSc y 0 y' 0]
    exact hA y y'
  rw [herm_append, hA, hA2, ← hSc z 0 0 w]
  ring

end GlobalTheory.RiemInt

open GlobalTheory.RosatiAH GlobalTheory.RiemInt in

theorem GlobalTheory.RiemInt.riemannForm_int : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (𝔠 : FracId F)
    (X : Obj F 𝔠 (Sp ℂ)) (c : 𝔠.elt), IsTotPos (c : F) →
    ∀ (u : HolUnif X.A (X.diag c) (Module.finrank ℚ F)) (e : Fin (Module.finrank ℚ F) ≃ (F →+* ℝ)),
    (∀ (a : 𝓞 F) w, u.ex (fun j ↦ (e j (a : F) : ℂ) * w j) = u.ex w ≫ X.rm.act a) →
    ∀ (h : Fin (Module.finrank ℚ F) → ℝ) (χ : u.Λ → ℂ), u.IsAH (Matrix.diagonal fun j ↦ (h j : ℂ)) χ →
    ∀ (c' : 𝔠.elt) (l l' : u.Λ), ∃ n : ℤ,
      (∑ j, (h j : ℂ) * (((e j ((c' : F) / (2 * (c : F))) : ℂ) * (l : Fin (Module.finrank ℚ F) → ℂ) j) *
        starRingEnd ℂ ((l' : Fin (Module.finrank ℚ F) → ℂ) j))).im = n := by
  intro F _ _ _ 𝔠 X c hc u e hu h χ hAH c' l l'
  obtain ⟨U0, hU0⟩ := GlobalTheory.exists_holUnif_tensor_self X.A X.ab (X.diag c) _ u
  have hAb2 := AbelianSchemeGerms.isAbelianScheme_tensor X.A X.A X.ab X.ab
  have frame : ∀ c' : 𝔠.elt, ∃ (U : HolUnif (X.A ⊗ X.A) (X.P c') (Module.finrank ℚ F + Module.finrank ℚ F))
      (H : Matrix (Fin (Module.finrank ℚ F + Module.finrank ℚ F)) (Fin (Module.finrank ℚ F + Module.finrank ℚ F)) ℂ)
      (χ : U.Λ → ℂ), (∀ x y, U.ex (Fin.append x y) = lift (u.ex x) (u.ex y)) ∧ IsFactorAH U H χ := fun c' => by
    obtain ⟨U, H, χ', hex, hF⟩ := GlobalTheory.exists_isFactorAH_frame_of_unif (X.A ⊗ X.A) hAb2 _ _ U0 (X.P c') (X.isLB c')
    exact ⟨U, H, χ', fun x y => by rw [hex]; exact hU0 x y, hF⟩
  choose U H χ' hex hF using frame
  have hswap : ∀ d v, (U d).ex (fswap _ v) = (U d).ex v ≫ lift (snd X.A X.A) (fst X.A X.A) := by
    intro d v
    rw [eq_append v, fswap_append, hex, hex]
    simp
  have hmul : ∀ d d' (b : 𝓞 F) v, (U d').ex (fmul (dmul fun j => (e j (b : F) : ℂ)) v) =
      (U d).ex v ≫ lift (fst X.A X.A) (snd X.A X.A ≫ X.rm.act b) := by
    intro d d' b v
    rw [eq_append v, fmul_append, hex, hex, dmul_apply, hu]
    simp
  have hdiag : ∀ z, (U c).ex (fdiag _ z) = u.ex z ≫ lift (𝟙 X.A) (𝟙 X.A) := by
    intro z
    rw [fdiag_apply, hex]
    simp
  have hdLB : (X.diag c).IsLB := LB.isLB_pull (X.isLB c) _
  have hD := hermForm_eq_of_lbIso_pull X.A (X.A ⊗ X.A) (X.diag c) (X.P c) hdLB (X.isLB c) _ _ u (U c) _ χ (H c) (χ' c)
    (isFactorAH_of_isAH hAH) (hF c) (lift (𝟙 X.A) (𝟙 X.A)) (fdiag _) hdiag (by unfold Obj.diag; exact GlobalTheory.lbIso_refl hdLB)
  have hS : ∀ d x y x' y', hermForm (H d) (Fin.append x y) (Fin.append x' y') =
      hermForm (H d) (Fin.append y x) (Fin.append y' x') := by
    intro d x y x' y'
    have := hermForm_eq_of_lbIso_pull (X.A ⊗ X.A) (X.A ⊗ X.A) (X.P d) (X.P d) (X.isLB d) (X.isLB d) _ _ (U d) (U d)
      (H d) (χ' d) (H d) (χ' d) (hF d) (hF d) (lift (snd X.A X.A) (fst X.A X.A)) (fswap _) (hswap d) (X.symm d)
      (Fin.append x y) (Fin.append x' y')
    rwa [fswap_append, fswap_append] at this
  have hM : ∀ (b : 𝓞 F) d x y x' y', hermForm (H (b • d)) (Fin.append x y) (Fin.append x' y') =
      hermForm (H d) (Fin.append x (dmul (fun j => (e j (b : F) : ℂ)) y))
        (Fin.append x' (dmul (fun j => (e j (b : F) : ℂ)) y')) := by
    intro b d x y x' y'
    have := hermForm_eq_of_lbIso_pull (X.A ⊗ X.A) (X.A ⊗ X.A) (X.P (b • d)) (X.P d) (X.isLB _) (X.isLB d) _ _
      (U (b • d)) (U d) (H _) (χ' _) (H d) (χ' d) (hF _) (hF d)
      (lift (fst X.A X.A) (snd X.A X.A ≫ X.rm.act b)) (fmul (dmul fun j => (e j (b : F) : ℂ)))
      (hmul _ d b) (X.smul b d) (Fin.append x y) (Fin.append x' y')
    rwa [fmul_append, fmul_append] at this
  have h2F : (((2 : 𝓞 F)) : F) = 2 := by norm_cast
  have h2 : (dmul fun j => (e j (((2 : 𝓞 F) : F)) : ℂ)) = (2 : ℂ) • LinearMap.id := by
    refine LinearMap.ext fun z => funext fun k => ?_
    simp only [dmul_apply, h2F, map_ofNat, LinearMap.smul_apply, LinearMap.id_apply, Pi.smul_apply, smul_eq_mul,
      Complex.ofReal_ofNat]
  have hB : ∀ z w, 2 * hermForm (H c) (Fin.append z 0) (Fin.append 0 w) =
      ∑ j, (h j : ℂ) * (z j * starRingEnd ℂ (w j)) := by
    intro z w
    rw [← diag_eq_two_mul (H c) (H ((2 : 𝓞 F) • c)) (hS c) (hS _) (fun x y x' y' => by rw [hM 2 c, h2]; rfl),
      ← fdiag_apply, ← fdiag_apply, ← hD]
    simp only [hermForm, dotProduct, Matrix.mulVec_diagonal, Pi.star_apply, RCLike.star_def]
    exact Finset.sum_congr rfl fun j _ => by ring

  have hl : Fin.append (l : Fin (Module.finrank ℚ F) → ℂ) 0 ∈ (U c').Λ := by
    rw [← (U c').ker, hex, (u.ker _).2 l.2, (u.ker _).2 u.Λ.zero_mem]
    refine CartesianMonoidalCategory.hom_ext _ _ ?_ ?_
    · rw [lift_fst, MonObj.one_comp]
    · rw [lift_snd, MonObj.one_comp]
  have hl' : Fin.append 0 (l' : Fin (Module.finrank ℚ F) → ℂ) ∈ (U c').Λ := by
    rw [← (U c').ker, hex, (u.ker _).2 l'.2, (u.ker _).2 u.Λ.zero_mem]
    refine CartesianMonoidalCategory.hom_ext _ _ ?_ ?_
    · rw [lift_fst, MonObj.one_comp]
    · rw [lift_snd, MonObj.one_comp]
  obtain ⟨n, hn⟩ := im_hermForm_int (A := X.A ⊗ X.A) (X.isLB c') (U c') (hF c') ⟨_, hl⟩ ⟨_, hl'⟩
  refine ⟨n, ?_⟩
  rw [← hn]
  congr 1
  have hc0 : (c : F) ≠ 0 := by
    intro h0
    have := hc (e ⟨0, Module.finrank_pos⟩)
    rw [h0, map_zero] at this
    exact lt_irrefl _ this
  obtain ⟨b, d, hd, hbd⟩ := IsFractionRing.div_surjective (A := 𝓞 F) ((c' : F) / (c : F))
  have hd0 : (d : F) ≠ 0 := by
    have := nonZeroDivisors.ne_zero hd
    exact_mod_cast this
  change (b : F) / (d : F) = _ at hbd
  have hcc : d • c' = b • c := by
    apply Subtype.ext
    rw [div_eq_div_iff hd0 hc0] at hbd
    simp only [Submodule.coe_smul, Algebra.smul_def]
    change (d : F) * c' = (b : F) * c
    rw [hbd, mul_comm]
  have hde : ∀ j, (e j (d : F) : ℂ) ≠ 0 := fun j => by
    exact_mod_cast (map_ne_zero (e j)).2 hd0
  set w : Fin (Module.finrank ℚ F) → ℂ := fun j => (e j (d : F) : ℂ)⁻¹ * (l' : Fin (Module.finrank ℚ F) → ℂ) j with hw
  have e1 := hM d c' l 0 0 w
  have e2 := hM b c l 0 0 w
  have e3 : dmul (fun j => (e j (d : F) : ℂ)) w = l' := by
    funext j
    simp only [dmul_apply, hw]
    rw [← _root_.mul_assoc, mul_inv_cancel₀ (hde j), _root_.one_mul]
  rw [hcc, e2, map_zero, map_zero, e3] at e1
  change _ = hermForm (H c') (Fin.append (l : Fin (Module.finrank ℚ F) → ℂ) 0) (Fin.append 0 (l' : Fin (Module.finrank ℚ F) → ℂ))
  rw [← e1]
  refine mul_left_cancel₀ (two_ne_zero (α := ℂ)) ?_
  rw [hB, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  have e4 : (c' : F) / (2 * (c : F)) = (b : F) / (d : F) / 2 := by
    rw [hbd]; field_simp
  have := hde j
  simp only [e4, dmul_apply, hw, map_div₀, map_mul, map_inv₀, map_ofNat, Complex.conj_ofReal, Complex.ofReal_div,
    Complex.ofReal_ofNat]
  field_simp
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithmeticModelAffineCoverRadical
section
open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open Formalism.BasicNotions.DV Formalism.MainNotions.WeightThresholdDefs GlobalTheory.FlagAr GlobalTheory.ShFam.Pad GlobalTheory.VB GlobalTheory.ShFam GlobalTheory.TrueGeo Formalism.L2.Pj GlobalTheory.Toroidal
open Formalism.MainNotions.DIV.Cons (intO)
open GlobalTheory.ArLieBase

set_option autoImplicit false

namespace GlobalTheory.BlowArith

theorem exists_isArithVar_effCartier_isIso (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k)
    [IsIntegral X] (D : ℕ) (hX : IsArithVar p D) (J : X.IdealSheafData)
    (hJ : genericPoint X ∉ J.support) :
    ∃ (Y : Scheme.{0}) (ρ : Y ⟶ X), IsArithVar (ρ ≫ p) D ∧
      ReciprocityTheory.AnForm.R.FinalTheorems.EffCartier (J.comap ρ) ∧
      ∀ V : X.Opens, (∀ x ∈ V, x ∉ J.support) → IsIso (ρ ∣_ V) := by
  have := hX.isNoetherianRing
  obtain ⟨Y, b, hb, hproj, hiso⟩ := ProjBlowup.exists_blowup p hX.isProjOver J
  let V : X.Opens := J.support.compl
  have hbV : IsIso (b ∣_ V) := hiso V fun _ hx => hx
  have : Nonempty V.toScheme := ⟨⟨genericPoint X, hJ⟩⟩
  have : IsIntegral V.toScheme := isIntegral_of_isOpenImmersion V.ι
  have : Nonempty (b ⁻¹ᵁ V).toScheme := ⟨inv (b ∣_ V) (Classical.arbitrary _)⟩
  have : IsIntegral (b ⁻¹ᵁ V).toScheme := isIntegral_of_isOpenImmersion (b ∣_ V)
  have hU : (J.comap b).support.compl = b ⁻¹ᵁ V := by
    ext y
    exact not_congr (ProjBlowup.mem_support_comap J b y)
  have hdom : IsSchemeTheoreticallyDominant (b ⁻¹ᵁ V).ι :=
    hU ▸ ProjBlowup.isSchemeTheoreticallyDominant_compl_of_effCartier Y _ hb.1
  have : IsNoetherian Y := isNoetherian_of_isProjOver hproj
  have : IsIntegral Y := by
    have : IsReduced Y := IsSchemeTheoreticallyDominant.isReduced (b ⁻¹ᵁ V).ι
    have h := ((IrreducibleSpace.isIrreducible_univ (b ⁻¹ᵁ V).toScheme).image _
      (b ⁻¹ᵁ V).ι.continuous.continuousOn).closure
    rw [Set.image_univ, (b ⁻¹ᵁ V).ι.denseRange.closure_range] at h
    have : IrreducibleSpace Y := (irreducibleSpace_def _).2 h
    exact isIntegral_of_irreducibleSpace_of_isReduced Y
  have hfac : (b ⁻¹ᵁ V).ι ≫ b = b ∣_ V ≫ V.ι := (morphismRestrict_ι b V).symm
  have hoi : IsOpenImmersion ((b ⁻¹ᵁ V).ι ≫ b) := by rw [hfac]; infer_instance
  have hg : (b ⁻¹ᵁ V).ι (genericPoint _) = genericPoint Y := genericPoint_eq_of_isOpenImmersion _
  have hgen : b (genericPoint Y) = genericPoint X := by
    rw [← hg, ← Scheme.Hom.comp_apply]
    exact genericPoint_eq_of_isOpenImmersion _
  have hdeg : b.residueDegree (genericPoint Y) ≠ 0 := by
    intro h0
    have h1 := CurveDegreesCompare.residueDegree_comp (b ⁻¹ᵁ V).ι b (genericPoint _)
    rw [CurveDegreesCompare.residueDegree_of_isOpenImmersion, hg, h0, zero_mul] at h1
    exact one_ne_zero h1
  have hflat : Flat ((b ≫ p) ≫ spMap (Int.castRingHom k)) := by
    rw [flat_int_iff_charZero]
    have := hX.charZero
    have : IsDominant b := ⟨by
      rw [DenseRange, dense_iff_closure_eq, ← Set.univ_subset_iff, ← genericPoint_closure]
      exact closure_mono (Set.singleton_subset_iff.2 ⟨_, hgen⟩)⟩
    have := IsSchemeTheoreticallyDominant.of_isDominant b
    have hinj' : Function.Injective b.appTop := Scheme.Hom.app_injective b ⊤
    exact charZero_of_injective_ringHom (f := b.appTop.hom) hinj'
  exact ⟨Y, b, ⟨hX.isDomain, hX.finite, ‹_›, hproj, hflat,
    DimCover.topologicalKrullDim_eq k X Y p (b ≫ p) D hX hproj hflat b rfl hgen hdeg⟩, hb.1, hiso⟩

end GlobalTheory.BlowArith

namespace GlobalTheory.ArLieBase

theorem exists_blowup_principalises : ∀ (F : Type) [Field F] [NumberField F] (G T : Scheme.{0}) (s : G ⟶ Sp F) (S : Set G) (d : ℕ) (ι : G ⟶ T) (X W : Scheme.{0}) (q : X ⟶ Sp (𝓞 F)) (jB : W ⟶ X) (πB : W ⟶ G) (ρ : X ⟶ T), IsPre s S d ι q jB πB ρ → ∀ (n : ℕ) (U : Fin n → X.Opens) (m : Fin n → ℕ) (A : ∀ j, Fin (m j) → Γ(X, U j)) (N : Fin n → ℕ), (∀ j, IsAffineOpen (U j)) → (∀ j, N j ≠ 0) → (∀ j, (N j : Γ(X, U j)) ∈ (Ideal.span (Set.range (A j))).radical) → ∃ (X' W' : Scheme.{0}) (b : X' ⟶ X) (jB' : W' ⟶ X') (πB' : W' ⟶ G), IsPre s S d ι (b ≫ q) jB' πB' (b ≫ ρ) ∧ ∀ (Y : Scheme.{0}) (ν : Y ⟶ X') (w : Y) (j : Fin n), (ν ≫ b) w ∈ U j → ∃ (V : Y.Opens) (hV : V ≤ (ν ≫ b) ⁻¹ᵁ U j), w ∈ V ∧ IsAffineOpen V ∧ ∃ k, ∀ k', ((ν ≫ b).appLE (U j) V hV).hom (A j k) ∣ ((ν ≫ b).appLE (U j) V hV).hom (A j k') := by
  intro F _ _ G T s S d ι X W q jB πB ρ h n U m A N hU hN hA
  have hX := h.1
  have := hX.isIntegral
  have := hX.isLocallyNoetherian
  have hc := hX.charZero
  set p : ℕ := ∏ j, N j with hpdef
  have hp0 : p ≠ 0 := Finset.prod_ne_zero_iff.2 fun j _ => hN j
  have hpA : ∀ j, (p : Γ(X, U j)) ∈ (Ideal.span (Set.range (A j))).radical := by
    intro j
    obtain ⟨c, hc⟩ := Finset.dvd_prod_of_mem N (Finset.mem_univ j)
    rw [hpdef, hc, Nat.cast_mul]
    exact Ideal.mul_mem_right _ _ (hA j)
  obtain ⟨J, hJp, hJE⟩ := GlobalTheory.Principalise.exists_idealSheaf_principalises X p n U m A hU hpA
  have hgen : genericPoint X ∈ X.basicOpen (p : Γ(X, ⊤)) := by
    have hne : (p : Γ(X, ⊤)) ≠ 0 := Nat.cast_ne_zero.2 hp0
    have hb : X.basicOpen (p : Γ(X, ⊤)) ≠ ⊥ := fun h0 => hne ((basicOpen_eq_bot_iff _).1 h0)
    have : Nonempty (X.basicOpen (p : Γ(X, ⊤))) := by
      by_contra h1
      apply hb
      rw [eq_bot_iff]
      intro x hx
      exact (h1 ⟨⟨x, hx⟩⟩).elim
    exact ((genericPoint_spec X).mem_open_set_iff (X.basicOpen (p : Γ(X, ⊤))).isOpen).mpr
      (by simpa using this)
  have hJg : genericPoint X ∉ J.support := fun hx => hJp _ hx hgen
  obtain ⟨X', b, hX', hE, hiso⟩ := GlobalTheory.BlowArith.exists_isArithVar_effCartier_isIso (𝓞 F) X q d hX J hJg
  let V : X.Opens := J.support.compl
  have hbV : IsIso (b ∣_ V) := hiso V fun _ hx => hx
  have huF : IsUnit ((p : ℕ) : Γ(Sp F, ⊤)) := by
    have := (IsUnit.mk0 (p : F) (Nat.cast_ne_zero.2 hp0)).map (Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom
    simpa using this
  have huW : IsUnit ((p : ℕ) : Γ(W, ⊤)) := by
    let φ : Γ(Sp F, ⊤) →+* Γ(W, ⊤) := ((πB ≫ s).app ⊤).hom
    have := huF.map φ
    rwa [map_natCast φ] at this
  have hrange : Set.range jB ⊆ Set.range V.ι := by
    rintro _ ⟨w, rfl⟩
    rw [Scheme.Opens.range_ι]
    have hw : w ∈ jB ⁻¹ᵁ X.basicOpen (p : Γ(X, ⊤)) := by
      simp only [Scheme.preimage_basicOpen, map_natCast]
      exact (Scheme.basicOpen_of_isUnit W huW).ge (show w ∈ (⊤ : W.Opens) from trivial)
    exact fun hx => hJp _ hx hw
  let jV : W ⟶ V.toScheme := IsOpenImmersion.lift V.ι jB hrange
  have hjV : jV ≫ V.ι = jB := IsOpenImmersion.lift_fac _ _ _
  let jB' : W ⟶ X' := jV ≫ inv (b ∣_ V) ≫ (b ⁻¹ᵁ V).ι
  have hjB' : jB' ≫ b = jB := by
    simp only [jB', Category.assoc, ← morphismRestrict_ι, IsIso.inv_hom_id_assoc, hjV]
  have hsq : IsPullback jB' (𝟙 W) b jB := by
    have h1 : IsPullback (jV ≫ inv (b ∣_ V)) (𝟙 W) (b ∣_ V) jV :=
      IsPullback.of_vert_isIso ⟨by simp⟩
    have h2 := h1.paste_horiz (isPullback_morphismRestrict b V).flip
    simpa [jB', Category.assoc, hjV] using h2
  have hpb : IsPullback jB' (πB ≫ s) (b ≫ q) (spMap (algebraMap (𝓞 F) F)) := by
    simpa using hsq.paste_vert h.2.1
  refine ⟨X', W, b, jB', πB, ⟨hX', hpb, h.2.2.1, h.2.2.2.1, ?_⟩, ?_⟩
  · rw [← Category.assoc, hjB']
    exact h.2.2.2.2
  · intro Y ν w j hw
    exact hJE X' Y b ν hE w j hw

end GlobalTheory.ArLieBase
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BaseChangePullSumMulPointValueEqStatement
section
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.baseChangePull_sum_mul_pointValue_eq : ∀ (R D : Type) [CommRing R] [CommRing D] [Algebra R D] (B : Over (Sp R)) (B' : Over (Sp D)) (q : B'.left ⟶ (SpAlg R D ⊗ B).left) (w : q ≫ (SpAlg R D ⊗ B).hom = B'.hom ≫ spMap (algebraMap R D)) (π : B'.left ⟶ B.left), q ≫ (fst (SpAlg R D) B).left = B'.hom → q ≫ (snd (SpAlg R D) B).left = π → ∀ (mB : IsMor (dp0 R) (B.hom ≫ 𝟙 _) (dp0 D) (B'.hom ≫ 𝟙 _) (algebraMap R D) π) (J : Type) [Fintype J] (d : J → D) (β : J → Z1 (O (dp0 R) (B.hom ≫ 𝟙 _))), bcPull w (sumMul d fun i ↦ fv (β i)) = fv (∑ i, d i • mB.coef.pullbackOneCocycle (β i)) := by
  first | exact @GlobalTheory.PtExt.bcPull_sumMul_fv | exact GlobalTheory.PtExt.bcPull_sumMul_fv | (intros; apply GlobalTheory.PtExt.bcPull_sumMul_fv <;> assumption)
end

