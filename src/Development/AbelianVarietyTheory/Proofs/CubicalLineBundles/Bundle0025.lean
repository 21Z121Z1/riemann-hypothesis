import Mathlib
import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.PowObjGeometricallyConnected
import Development.AbelianVarietyTheory.Statements.PrincipalLattices.LogHermFormOfUnitDiscriminant
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0004
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsPrimitiveNormalisation
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverIffIsProperAndExistsIsAmpleLB
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0015
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsAbelianSchemeAndExtendOfGenericHoms
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.MeanLogCovolumeEqMeanClassGroup
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0015
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0018
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0019
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0020
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0021
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0014
import Development.AbelianVarietyTheory.Definitions.CMLattices.IsDiffOf
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsGenOfGenericFibre

-- bundled from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.LocZeroTranslDiffComp
section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Serre
open scoped CategoryTheory.Obj UpperHalfPlane TensorProduct

namespace GlobalTheory.TripleProd

open GlobalTheory.CechPic

section Local

variable {Y Y' B B' : Scheme.{0}}

def LocZero (π : Y ⟶ B) (c : Pic Y) : Prop :=
  ∀ p : B, ∃ V : B.Opens, p ∈ V ∧ pull (π ⁻¹ᵁ V).ι c = 0

theorem pull_eq_zero_of_range {W : Y.Opens} {c : Pic Y} (H : pull W.ι c = 0) (h : Y' ⟶ Y) (hW : ∀ y, h y ∈ W) :
    pull h c = 0 := by
  have hr : Set.range h ⊆ Set.range W.ι := by
    rintro _ ⟨y, rfl⟩
    rw [Scheme.Opens.range_ι]
    exact hW y
  rw [← IsOpenImmersion.lift_fac W.ι h hr, pull_comp, H, map_zero]

theorem LocZero.sub {π : Y ⟶ B} {c d : Pic Y} (H : LocZero π c) (H' : LocZero π d) : LocZero π (c - d) := by
  intro p
  obtain ⟨V, hV, t⟩ := H p
  obtain ⟨V', hV', t'⟩ := H' p
  refine ⟨V ⊓ V', ⟨hV, hV'⟩, ?_⟩
  rw [map_sub, pull_eq_zero_of_range t (π ⁻¹ᵁ (V ⊓ V')).ι fun y => y.2.1,
    pull_eq_zero_of_range t' (π ⁻¹ᵁ (V ⊓ V')).ι fun y => y.2.2, sub_zero]

theorem LocZero.pull_over {π : Y ⟶ B} {c : Pic Y} (H : LocZero π c) {π' : Y' ⟶ B} (h : Y' ⟶ Y) (sq : h ≫ π = π') :
    LocZero π' (pull h c) := by
  subst sq
  intro p
  obtain ⟨V, hV, t⟩ := H p
  refine ⟨V, hV, ?_⟩
  rw [← pull_comp]
  exact pull_eq_zero_of_range t _ fun y => y.2

theorem locZero_base (π : Y ⟶ B) (c : Pic B) : LocZero π (pull π c) := by
  obtain ⟨L, hL, rfl⟩ := cls_surj c
  intro p
  obtain ⟨i, hi⟩ := exists_chart hL p
  refine ⟨L.U i, hi, ?_⟩
  rw [← pull_comp]
  exact (cls_eq_zero_iff (pull_isLB hL _)).2
    (BoxKernel.gen_of_chart (pull_isLB hL _) (fun _ => i) fun y => mem_pull.2 y.2)

theorem locZero_iff (π : Y ⟶ B) {N : LB Y} (hN : N.IsLB) :
    (∀ p : B, ∃ V : B.Opens, p ∈ V ∧ ∃ c : LB.Gen (N.pull (π ⁻¹ᵁ V).ι), c.IsGen) ↔ LocZero π (cls N hN) :=
  forall_congr' fun _ => exists_congr fun _ => and_congr_right fun _ =>
    (cls_eq_zero_iff (pull_isLB hN _)).symm

end Local

section Kernel

variable {S : Scheme.{0}} {A G H : Over S} [GrpObj A] [GrpObj G] [GrpObj H]

theorem cls_translDiff {L : LB A.left} (hL : L.IsLB) {T : Over S} (x : T ⟶ A) :
    cls (Out.translDiff A L x) (LB.isLB_linComb hL _ _) =
      pull ((fst T A ≫ x) * snd T A).left (cls L hL) - pull (snd T A).left (cls L hL) := by
  refine (cls_linComb hL _ _ _).trans ?_
  rw [Fin.sum_univ_two]
  show (1 : ℤ) • pull ((fst T A ≫ x) * snd T A).left (cls L hL) + (-1 : ℤ) • pull (snd T A).left (cls L hL) = _
  rw [one_zsmul, neg_one_zsmul, sub_eq_add_neg]

theorem locZero_translDiff_comp {N : LB A.left} {L : LB G.left} (hN : N.IsLB) (hL : L.IsLB) (b : Pic H.left)
    (p : A ⟶ G) (q : A ⟶ H) [IsMonHom p] [IsMonHom q] (u : G ⟶ A) (hp : u ≫ p = 𝟙 G) (hq : u ≫ q = 1)
    (e : cls N hN = pull p.left (cls L hL) + pull q.left b) {T : Over S} (x : T ⟶ A)
    (hx : LocZero (fst T A).left (cls (Out.translDiff A N x) (LB.isLB_linComb hN _ _))) :
    LocZero (fst T G).left (cls (Out.translDiff G L (x ≫ p)) (LB.isLB_linComb hL _ _)) := by
  have H₁ := hx.pull_over (π' := (fst T G).left) (T ◁ u).left (congrArg (fun q => q.left) (whiskerLeft_fst T u))
  have H₂ := (H₁.sub (locZero_base (fst T G).left (pull (x ≫ q).left b))).sub
    (locZero_base (fst T G).left (-pull (1 : T ⟶ H).left b))
  have e₁ : T ◁ u ≫ ((fst T A ≫ x) * snd T A) ≫ p = (fst T G ≫ x ≫ p) * snd T G := by
    rw [MonObj.mul_comp, MonObj.comp_mul, Category.assoc, whiskerLeft_fst_assoc, whiskerLeft_snd_assoc, hp,
      Category.comp_id]
  have e₂ : T ◁ u ≫ ((fst T A ≫ x) * snd T A) ≫ q = fst T G ≫ x ≫ q := by
    rw [MonObj.mul_comp, MonObj.comp_mul, Category.assoc, whiskerLeft_fst_assoc, whiskerLeft_snd_assoc, hq,
      MonObj.comp_one, _root_.mul_one]
  have e₃ : T ◁ u ≫ snd T A ≫ p = snd T G := by rw [whiskerLeft_snd_assoc, hp, Category.comp_id]
  have e₄ : T ◁ u ≫ snd T A ≫ q = fst T G ≫ (1 : T ⟶ H) := by
    rw [whiskerLeft_snd_assoc, hq, MonObj.comp_one, MonObj.comp_one]
  convert H₂ using 1
  rw [cls_translDiff hL, cls_translDiff hN, e]
  simp only [map_sub, map_add, map_neg, ← pull_comp, ← Over.comp_left, e₁, e₂, e₃, e₄]
  abel

theorem kTriv_prod {N : LB (G ⊗ H).left} {L : LB G.left} {L' : LB H.left} (hN : N.IsLB) (hL : L.IsLB)
    (hL' : L'.IsLB) (e : cls N hN = pull (fst G H).left (cls L hL) + pull (snd G H).left (cls L' hL'))
    (hK : Out.KTriv G L) (hK' : Out.KTriv H L') : Out.KTriv (G ⊗ H) N := by
  intro R _ t x hx
  have hx' := (locZero_iff _ (LB.isLB_linComb hN _ _)).1 hx
  have h₁ : x ≫ fst G H = 1 := hK R t _ ((locZero_iff _ (LB.isLB_linComb hL _ _)).2
    (locZero_translDiff_comp hN hL _ (fst G H) (snd G H) (lift (𝟙 G) 1) (lift_fst _ _) (lift_snd _ _) e x hx'))
  have h₂ : x ≫ snd G H = 1 := hK' R t _ ((locZero_iff _ (LB.isLB_linComb hL' _ _)).2
    (locZero_translDiff_comp hN hL' _ (snd G H) (fst G H) (lift 1 (𝟙 H)) (lift_snd _ _) (lift_fst _ _)
      (e.trans (add_comm _ _)) x hx'))
  show x = 1
  apply CartesianMonoidalCategory.hom_ext
  · rw [h₁, MonObj.one_comp]
  · rw [h₂, MonObj.one_comp]

end Kernel

section Cube

variable {S : Scheme.{0}} {A G : Over S} [GrpObj A] [IsCommMonObj A] [GrpObj G] [IsCommMonObj G] {n : ℕ}

def cubeCls {T : Over S} (x : Fin n → (T ⟶ G)) (c : Pic G.left) : Pic T.left :=
  ∑ I : ULift.{0} (Finset (Fin n)), ((-1 : ℤ) ^ (n - I.down.card)) • pull (psum G x I.down).left c

theorem cls_cubeLB {T : Over S} (x : Fin n → (T ⟶ G)) {L : LB G.left} (hL : L.IsLB) :
    cls (cubeLB G x L) (LB.isLB_linComb hL _ _) = cubeCls x (cls L hL) :=
  cls_linComb hL _ _ _

theorem cubeCls_add {T : Over S} (x : Fin n → (T ⟶ G)) (c d : Pic G.left) :
    cubeCls x (c + d) = cubeCls x c + cubeCls x d := by
  simp only [cubeCls, map_add, smul_add, Finset.sum_add_distrib]

theorem pull_cubeCls {T T' : Over S} (ρ : T' ⟶ T) (x : Fin n → (T ⟶ G)) (c : Pic G.left)
    (y : Fin n → (T' ⟶ G)) (h : ∀ i, y i = ρ ≫ x i) : cubeCls y c = pull ρ.left (cubeCls x c) := by
  rw [cubeCls, cubeCls, map_sum]
  refine Finset.sum_congr rfl fun I _ => ?_
  rw [map_zsmul, ← pull_comp, PrimNorm.psum_pre ρ x y h]

end Cube

section Triple

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {S : Scheme.{0}} (t : SAB H S) {T : Over S}

abbrev ppCls : Pic t.G.left := cls t.PP.L t.PP.isLB

end Triple

end GlobalTheory.TripleProd
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.MeanLogLieNormSqEqMeanLogEta
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory
open scoped CategoryTheory.Obj UpperHalfPlane

namespace GlobalTheory

theorem exists_periodPair_image_ideal {K : Type} [Field K] [NumberField K] (hK : Module.finrank ℚ K = 2)
    {σ : K →+* ℂ} (hσ : ¬ ComplexEmbedding.IsReal σ) {I : Ideal (𝓞 K)} (hI : I ≠ ⊥) :
    ∃ L : PeriodPair, ∀ z, z ∈ L.lattice ↔ ∃ a ∈ I, z = σ (a : K) := by
  have hr : Module.finrank ℤ I = 2 :=
    (Ideal.finrank_eq_finrank (RingOfIntegers.basis K) I hI).trans ((RingOfIntegers.rank K).trans hK)
  let b : Module.Basis (Fin 2) ℤ I := Module.finBasisOfFinrankEq ℤ _ hr
  have hs : ∀ x : I, σ ((x : 𝓞 K) : K) =
      b.repr x 0 * σ ((b 0 : 𝓞 K) : K) + b.repr x 1 * σ ((b 1 : 𝓞 K) : K) := by
    intro x
    have := congrArg (fun x : I => σ ((x : 𝓞 K) : K)) (b.sum_repr x)
    rw [Fin.sum_univ_two] at this
    simpa using this.symm
  obtain ⟨a, ha⟩ := CMLattice.exists_im_ne_zero σ hσ
  have hb0 : σ ((b 0 : 𝓞 K) : K) ≠ 0 := by
    rw [map_ne_zero]
    have : (b 0 : 𝓞 K) ≠ 0 := fun h => b.ne_zero 0 (Subtype.ext h)
    exact_mod_cast this
  have h0 : (σ ((b 1 : 𝓞 K) : K) * starRingEnd ℂ (σ ((b 0 : 𝓞 K) : K))).im ≠ 0 := by
    intro h0
    have e := hs ⟨a * b 0, I.mul_mem_left a (b 0).2⟩
    have e' := congrArg (fun z => (z * starRingEnd ℂ (σ ((b 0 : 𝓞 K) : K))).im) e
    simp only [RingOfIntegers.coe_eq_algebraMap, map_mul] at e' h0 ha hb0
    rw [add_mul, _root_.mul_assoc, _root_.mul_assoc, _root_.mul_assoc, Complex.mul_conj, Complex.add_im,
      Complex.mul_im, Complex.mul_im, Complex.mul_im, h0] at e'
    simp [ha, hb0] at e'
  refine ⟨⟨σ ((b 0 : 𝓞 K) : K), σ ((b 1 : 𝓞 K) : K), ?_⟩, fun z => ?_⟩
  · rw [LinearIndependent.pair_iff]
    intro x y e
    have e1 := congrArg Complex.re e
    have e2 := congrArg Complex.im e
    simp at e1 e2 h0
    constructor
    · refine mul_right_cancel₀ h0 ?_
      linear_combination (σ ((b 1 : 𝓞 K) : K)).im * e1 - (σ ((b 1 : 𝓞 K) : K)).re * e2
    · refine mul_right_cancel₀ h0 ?_
      linear_combination (σ ((b 0 : 𝓞 K) : K)).re * e2 - (σ ((b 0 : 𝓞 K) : K)).im * e1
  · rw [PeriodPair.mem_lattice]
    constructor
    · rintro ⟨m, n, rfl⟩
      exact ⟨_, (m • b 0 + n • b 1).2, by simp⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨_, _, (hs ⟨x, hx⟩).symm⟩

theorem mean_log_lieNormSq_eq_mean_log_eta :
    ThetaUnifAV → Out.PolBaseChangeSt → (∀ (T K : Type) [CommRing T] [IsDomain T] [IsDiscreteValuationRing T] [Field K] [Algebra T K] [IsFractionRing T K] (G G' : Over (Sp T)) [GrpObj G] [GrpObj G'], IsSemiAbelian G → IsSemiAbelian G' → ∀ f : (Over.pullback (spMap (algebraMap T K))).obj G ⟶ (Over.pullback (spMap (algebraMap T K))).obj G', IsMonHom f → ∃! F : G ⟶ G', IsMonHom F ∧ (Over.pullback (spMap (algebraMap T K))).map F = f) → ∀ (K : Type) [Field K] [NumberField K], Module.finrank ℚ K = 2 → ∀ (σ₀ : K →+* ℂ), ¬ ComplexEmbedding.IsReal σ₀ → ∀ (𝔟 : ClassGroup (𝓞 K) → nonZeroDivisors (Ideal (𝓞 K))), (∀ C, ClassGroup.mk0 (𝔟 C) = C) → ∀ (M : IntermediateField ℚ ℂ) [NumberField M] (κ : K →+* M) (P : Out.PolAV (Sp (𝓞 M))) (v : epsR (𝓞 M) ⟶ P.A) (L₀ : (𝓞 M →+* ℂ) → PeriodPair) (Q : ClassGroup (𝓞 K) → Out.PolAV (Sp (𝓞 M))) (t : ∀ C, epsR (𝓞 M) ⟶ (Q C).A) (L : ClassGroup (𝓞 K) → (𝓞 M →+* ℂ) → PeriodPair) (δ : ClassGroup (𝓞 K) → (𝓞 M)ˣ), (∀ a, (κ a : ℂ) = σ₀ a) ∧ (P.g = 1 ∧ IsLieBasis ![v] ∧ (∀ (R' : Type) [CommRing R'] (f' : (𝓞 M) →+* R') (P' : Out.PolAV (Sp R')) (φ' : P'.A.left ⟶ P.A.left) (v' : epsR R' ⟶ P'.A), IsPolFibre f' P P' φ' → IsVecOver f' φ' v v' → IsLieBasis ![v']) ∧ ∀ s' : (𝓞 M) →+* ℂ, (∀ (P' : Out.PolAV (Sp ℂ)) (φ' : P'.A.left ⟶ P.A.left) (v' : epsR ℂ ⟶ P'.A) (u' : HolUnif P'.A P'.L P'.g) (w' : Fin P'.g → ℂ), IsPolFibre s' P P' φ' → IsVecOver s' φ' v v' → u'.IsDiff w' v' → w' ≠ 0 ∧ ∀ z : ℂ, z ∈ (L₀ s').lattice ↔ z • w' ∈ u'.Λ)) ∧ (∀ C, ((Q C).g = 1 ∧ IsLieBasis ![(t C)] ∧ (∀ (R' : Type) [CommRing R'] (f' : (𝓞 M) →+* R') (P' : Out.PolAV (Sp R')) (φ' : P'.A.left ⟶ (Q C).A.left) (v' : epsR R' ⟶ P'.A), IsPolFibre f' (Q C) P' φ' → IsVecOver f' φ' (t C) v' → IsLieBasis ![v']) ∧ ∀ s' : (𝓞 M) →+* ℂ, (∀ (P' : Out.PolAV (Sp ℂ)) (φ' : P'.A.left ⟶ (Q C).A.left) (v' : epsR ℂ ⟶ P'.A) (u' : HolUnif P'.A P'.L P'.g) (w' : Fin P'.g → ℂ), IsPolFibre s' (Q C) P' φ' → IsVecOver s' φ' (t C) v' → u'.IsDiff w' v' → w' ≠ 0 ∧ ∀ z : ℂ, z ∈ (L C s').lattice ↔ z • w' ∈ u'.Λ))) ∧ (∀ C s, (L C s).g₂ ^ 3 - 27 * (L C s).g₃ ^ 2 = s (δ C : 𝓞 M)) ∧ (∃ c : ℂ, c ≠ 0 ∧ ∀ z, z ∈ (L₀ ((algebraMap M ℂ).comp (algebraMap (𝓞 M) M))).lattice ↔ ∃ a : 𝓞 K, z = c * σ₀ (a : K)) → (∃ β : ClassGroup (𝓞 K) → M, (∀ C, β C ≠ 0) ∧ (∀ a : 𝓞 K, (∀ (P₁ Q₁ : Out.PolAV (Sp M)) (φ₁ : P₁.A.left ⟶ P.A.left) (ψ₁ : Q₁.A.left ⟶ P.A.left) (v₁ : epsR M ⟶ P₁.A) (t₁ : epsR M ⟶ Q₁.A), IsPolFibre (algebraMap (𝓞 M) M) P P₁ φ₁ → IsPolFibre (algebraMap (𝓞 M) M) P Q₁ ψ₁ → IsVecOver (algebraMap (𝓞 M) M) φ₁ v v₁ → IsVecOver (algebraMap (𝓞 M) M) ψ₁ v t₁ → ∃ f₁ : P₁.A ⟶ Q₁.A, IsMonHom f₁ ∧ IsLieComb ![κ (a : K)] ![t₁] (v₁ ≫ f₁))) ∧ (∀ C (x : K), (∀ b ∈ (𝔟 C : Ideal (𝓞 K)), IsIntegral ℤ (x * (b : K))) → (∀ (P₁ Q₁ : Out.PolAV (Sp M)) (φ₁ : P₁.A.left ⟶ P.A.left) (ψ₁ : Q₁.A.left ⟶ (Q C).A.left) (v₁ : epsR M ⟶ P₁.A) (t₁ : epsR M ⟶ Q₁.A), IsPolFibre (algebraMap (𝓞 M) M) P P₁ φ₁ → IsPolFibre (algebraMap (𝓞 M) M) (Q C) Q₁ ψ₁ → IsVecOver (algebraMap (𝓞 M) M) φ₁ v v₁ → IsVecOver (algebraMap (𝓞 M) M) ψ₁ (t C) t₁ → ∃ f₁ : P₁.A ⟶ Q₁.A, IsMonHom f₁ ∧ IsLieComb ![β C * κ x] ![t₁] (v₁ ≫ f₁))) ∧ ∀ C, ∀ y ∈ (𝔟 C : Ideal (𝓞 K)), (∀ (P₁ Q₁ : Out.PolAV (Sp M)) (φ₁ : P₁.A.left ⟶ (Q C).A.left) (ψ₁ : Q₁.A.left ⟶ P.A.left) (v₁ : epsR M ⟶ P₁.A) (t₁ : epsR M ⟶ Q₁.A), IsPolFibre (algebraMap (𝓞 M) M) (Q C) P₁ φ₁ → IsPolFibre (algebraMap (𝓞 M) M) P Q₁ ψ₁ → IsVecOver (algebraMap (𝓞 M) M) φ₁ (t C) v₁ → IsVecOver (algebraMap (𝓞 M) M) ψ₁ v t₁ → ∃ f₁ : P₁.A ⟶ Q₁.A, IsMonHom f₁ ∧ IsLieComb ![(β C)⁻¹ * κ (y : K)] ![t₁] (v₁ ≫ f₁))) → ∀ n : (M →+* ℂ) → ℝ, (∀ s, IsLieNormSq P v (s.comp (algebraMap (𝓞 M) M)) (n s)) → ∀ (σ : K →+* ℂ) (τ : ClassGroup (𝓞 K) → ℍ), (∀ C, IsIdealClassPoint σ C (τ C)) → (∑ s, Real.log (n s)) / Module.finrank ℚ M = (∑ C, -Real.log (4 * Real.pi * (τ C).im * ‖ModularForm.eta (τ C)‖ ^ 4)) / classNumber K := by
  intro hU hB hN K _ _ hK σ₀ h₀ 𝔟 h𝔟 M _ κ P v L₀ Q t L δ ⟨_, ⟨hPg, hv, hvb, hPL⟩, hQ, hδ, _⟩
    ⟨β, hβ, hEnd, h1, h2⟩ n hn σ τ hτ
  let _ : Algebra K M := κ.toAlgebra
  have hvt : IsTangent v := hv.1 0
  have htt : ∀ C, IsTangent (t C) := fun C => (hQ C).2.1.1 0
  obtain ⟨P₀, φ, hφ⟩ := exists_isPolFibre hB (algebraMap (𝓞 M) M) P
  obtain ⟨v₀, hv₀, -⟩ := existsUnique_isVecOver hφ.2.1.1 v
  choose Q₀ ψ hψ using fun C => exists_isPolFibre hB (algebraMap (𝓞 M) M) (Q C)
  choose t₀ ht₀ using fun C => (existsUnique_isVecOver (hψ C).2.1.1 (t C)).exists
  choose Lc hLc using fun C => exists_periodPair_image_ideal hK h₀ (nonZeroDivisors.coe_ne_zero (𝔟 C))
  have key := mean_log_covolume_eq_mean_classGroup K M hK σ₀ h₀ 𝔟 Lc h𝔟 hLc
    (fun s => L₀ (s.comp (algebraMap (𝓞 M) M))) (fun C s => L C (s.comp (algebraMap (𝓞 M) M))) δ β
    (fun s a => by
      obtain ⟨f, hf, hc⟩ := hEnd a P₀ P₀ φ φ v₀ v₀ hφ hφ hv₀ hv₀
      exact (EllipticHom.multiplier_iff_exists_hom hU hB _ P P v v _ _ _ _ hPg hPg hvt hvt (hPL _) (hPL _)).2
        (hom_deriv_baseChange _ P P v v _ _ P₀ P₀ φ φ v₀ v₀ f _ hφ hφ hv₀ hv₀ hf hc ℂ s))
    (fun C s => hδ C _) hβ
    (fun C x hx => ⟨T.isIntegral_derivative_curve_hom_good_reduction hN hB M P (Q C) v (t C) _ hvt (hQ C).2.2.1 (h1 C x hx), fun s => by
      obtain ⟨f, hf, hc⟩ := h1 C x hx P₀ (Q₀ C) φ (ψ C) v₀ (t₀ C) hφ (hψ C) hv₀ (ht₀ C)
      exact (EllipticHom.multiplier_iff_exists_hom hU hB _ P (Q C) v (t C) _ _ _ _ hPg (hQ C).1 hvt (htt C) (hPL _) ((hQ C).2.2.2 _)).2
        (hom_deriv_baseChange _ P (Q C) v (t C) _ _ _ _ _ _ _ _ f _ hφ (hψ C) hv₀ (ht₀ C) hf hc ℂ s)⟩)
    (fun C y hy => ⟨T.isIntegral_derivative_curve_hom_good_reduction hN hB M (Q C) P (t C) v _ (htt C) hvb (h2 C y hy), fun s => by
      obtain ⟨f, hf, hc⟩ := h2 C y hy (Q₀ C) P₀ (ψ C) φ (t₀ C) v₀ (hψ C) hφ (ht₀ C) hv₀
      exact (EllipticHom.multiplier_iff_exists_hom hU hB _ (Q C) P (t C) v _ _ _ _ (hQ C).1 hPg (htt C) hvt ((hQ C).2.2.2 _) (hPL _)).2
        (hom_deriv_baseChange _ (Q C) P (t C) v _ _ _ _ _ _ _ _ f _ (hψ C) hφ (ht₀ C) hv₀ hf hc ℂ s)⟩)
  rw [← log_pi_sub_mean_log_latticeNormDisc K hK σ₀ h₀ 𝔟 Lc h𝔟 hLc σ τ hτ, ← key]
  have hlog : ∀ s : M →+* ℂ, Real.log (n s) = Real.log Real.pi -
      Real.log |((L₀ (s.comp (algebraMap (𝓞 M) M))).ω₁ *
        starRingEnd ℂ (L₀ (s.comp (algebraMap (𝓞 M) M))).ω₂).im| := by
    intro s
    obtain ⟨hp, hr⟩ := isLieNormSq_iff_eq_pi_div_covolume hU hB _ P v _ _ hPg hvt (hPL (s.comp (algebraMap (𝓞 M) M)))
    rw [(hr _).1 (hn s), Real.log_div Real.pi_ne_zero]
    intro h
    rw [h, div_zero] at hp
    exact lt_irrefl _ hp
  have hM : (Module.finrank ℚ M : ℝ) ≠ 0 := by exact_mod_cast Module.finrank_pos.ne'
  simp only [hlog, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Embeddings.card, nsmul_eq_mul]
  field_simp

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.QuadraticEquationOfDerivative
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory
open scoped CategoryTheory.Obj UpperHalfPlane

namespace GlobalTheory.LieMultiple

variable {R : Type} [CommRing R] {G : Over (Sp R)} [GrpObj G]

theorem isLieComb_natCast_pow {v : epsR R ⟶ G} (hv : IsTangent v) (n : ℕ) :
    IsLieComb ![(n : R)] ![v] (v ^ n) := by
  induction n with
  | zero =>
    rw [Nat.cast_zero, pow_zero]
    exact (lieMultiple_calculus R G G v v v 0 0).2.2.2.2.2 hv
  | succ n ih =>
    rw [Nat.cast_succ, pow_succ]
    exact (lieMultiple_calculus R G G v _ v n 1).2.1 hv ih
      (lieMultiple_calculus R G G v v v 0 0).2.2.2.2.1

theorem isMonHom_id_pow [IsCommMonObj G] (n : ℕ) : IsMonHom ((𝟙 G) ^ n) := by
  induction n with
  | zero =>
    rw [pow_zero]
    exact inferInstanceAs (IsMonHom (toUnit G ≫ η[G]))
  | succ n ih =>
    rw [pow_succ]
    exact inferInstanceAs (IsMonHom (lift ((𝟙 G) ^ n) (𝟙 G) ≫ μ[G]))

theorem quadratic_equation_of_derivative : ThetaUnifAV → Out.PolBaseChangeSt → ∀ (k : Type) [Field k] (s : k →+* ℂ) (P : Out.PolAV (Sp k)) (v : epsR k ⟶ P.A) (W : P.A ⟶ P.A) (w : k) (n : ℕ), IsTangent v → (∀ (R' : Type) [CommRing R'] (f' : k →+* R') (P' : Out.PolAV (Sp R')) (φ' : P'.A.left ⟶ P.A.left) (v' : epsR R' ⟶ P'.A), IsPolFibre f' P P' φ' → IsVecOver f' φ' v v' → IsLieBasis ![v']) → IsMonHom W → IsLieComb ![w] ![v] (v ≫ W) → w * w + n = w → (W ≫ W) * (𝟙 P.A) ^ n = W := by
  intro hT hB k _ s P v W w n hv hb hW hw heq
  have hc := P.isAb.comm
  have h1 := isMonHom_id_pow (G := P.A) n
  have h2 : IsMonHom ((W ≫ W) * (𝟙 P.A) ^ n) :=
    inferInstanceAs (IsMonHom (lift (W ≫ W) ((𝟙 P.A) ^ n) ≫ μ[P.A]))
  refine GlobalTheory.T.curve_hom_ext_of_derivative_lieBasis hT hB k s P P v _ _ hb h2 hW ?_
  have h3 : IsLieComb ![w] ![v ≫ W] ((v ≫ W) ≫ W) :=
    (lieMultiple_calculus k P.A P.A v _ v w w).2.2.2.1 W hw
  have h4 : IsLieComb ![w * w] ![v] ((v ≫ W) ≫ W) :=
    (lieMultiple_calculus k P.A P.A v _ _ w w).2.2.1 hw h3
  have h5 : IsLieComb ![w * w + n] ![v] (((v ≫ W) ≫ W) * v ^ n) :=
    (lieMultiple_calculus k P.A P.A v _ _ (w * w) n).2.1 hv h4 (isLieComb_natCast_pow hv n)
  rw [heq, isLieComb_one_iff_comp] at h5
  rw [isLieComb_one_iff_comp] at hw
  rw [MonObj.comp_mul, MonObj.comp_pow, Category.comp_id, ← Category.assoc, h5, ← hw]

end GlobalTheory.LieMultiple
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.SurjectiveAppTopOfSection
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CM

set_option backward.isDefEq.respectTransparency false

namespace GlobalTheory.TrivDedekind

theorem surjective_appTop_of_section {K : Type} [Field K] {Y : Scheme.{0}} [IsIntegral Y] (p : Y ⟶ Sp K)
    [UniversallyClosed p] (e : Sp K ⟶ Y) (he : e ≫ p = 𝟙 _) : Function.Surjective p.appTop.hom := by
  have hF : IsField Γ(Y, ⊤) := isField_of_universallyClosed K p
  let _ := hF.toField
  have hinj : Function.Injective e.appTop.hom := e.appTop.hom.injective
  have hc : ∀ a, e.appTop.hom (p.appTop.hom a) = a := fun a => by
    rw [← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop, he]
    simp
  exact fun c => ⟨e.appTop.hom c, hinj (hc _)⟩

theorem exists_gen_of_generic : ∀ (R K : Type) [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K] [IsFractionRing R K] (A : Over (Sp R)) [GrpObj A], IsAbelianScheme A → ∀ (X' : Scheme.{0}) (π : X' ⟶ A.left) (p : X' ⟶ Sp K), IsPullback π p A.hom (spMap (algebraMap R K)) → ∀ N : LB A.left, N.IsLB → (∃ t : LB.Gen (N.pull (eSec A)), t.IsGen) → (∃ t : LB.Gen (N.pull π), t.IsGen) → ∃ t : LB.Gen N, t.IsGen := by
  intro R K _ _ _ _ _ A _ hA X' π p H N hN ⟨ρ, hρ⟩ ⟨t, ht⟩
  have := hA.smooth
  have := hA.proper
  have := forall_geometricallyIntegral_of_smooth_of_geometricallyConnected _ _ A.hom hA.smooth hA.geomConnected
  have : CompactSpace A.left := QuasiCompact.compactSpace_of_compactSpace A.hom
  have : QuasiSeparatedSpace A.left := quasiSeparatedSpace_of_quasiSeparated A.hom
  have : IsIntegral X' := DvrModel.isIntegral_of_geometricallyIntegral H
  have : UniversallyClosed p := MorphismProperty.of_isPullback H inferInstance
  have he : eSec A ≫ A.hom = 𝟙 _ := Over.w η[A]
  exact GenericTriv.exists_gen_of_fibre (algebraMap R K) (IsFractionRing.injective R K) A.hom (eSec A) he π p H
    (surjective_appTop_of_section p (H.lift (spMap (algebraMap R K) ≫ eSec A) (𝟙 _)
      (by rw [Category.assoc, he]; simp)) (H.lift_snd _ _ _)) hN ρ hρ t ht

end GlobalTheory.TrivDedekind
end

