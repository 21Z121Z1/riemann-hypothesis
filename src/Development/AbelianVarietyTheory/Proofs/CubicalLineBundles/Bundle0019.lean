import Mathlib
import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.PowObjGeometricallyConnected
import Development.AbelianVarietyTheory.Statements.PrincipalLattices.LogHermFormOfUnitDiscriminant
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0110
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0015
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsLinearOfIsMonHom
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsHomOfLinearScalingHermForm
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.EqZeroOfSumEmbeddingSmul
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0014
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0009
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.ExistsUniqueEqConstMulOriginSec
import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.OpensRangeChartYSupOpensRangeChartZ
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.Bundle0006
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0002
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0008
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.KernelPolarisationTrivialOfSectionsVanishZeroStatement
import Formalism.LocalToGlobal.CMDeterminantIdeals.LambdaLowerBound
import ReciprocityTheory.SemistableReduction.Bundle0009
import Development.AbelianVarietyTheory.Statements.FundamentalDomains.KeyFormulaPowOfKeyFormula

-- bundled from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.KTrivOfUnimodular
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Serre
open scoped CategoryTheory.Obj UpperHalfPlane TensorProduct

namespace GlobalTheory.HermTensorKernel

open GlobalTheory.CechPic

section Local

variable {Y Y' B : Scheme.{0}}

def LocZero (π : Y ⟶ B) (c : Pic Y) : Prop :=
  ∀ p : B, ∃ V : B.Opens, p ∈ V ∧ ∀ (Z : Scheme.{0}) (f : Z ⟶ Y), (∀ z, π (f z) ∈ V) → pull f c = 0

theorem LocZero.add {π : Y ⟶ B} {c d : Pic Y} (hc : LocZero π c) (hd : LocZero π d) : LocZero π (c + d) := by
  intro p
  obtain ⟨V, hV, H⟩ := hc p
  obtain ⟨V', hV', H'⟩ := hd p
  refine ⟨V ⊓ V', ⟨hV, hV'⟩, fun Z f hf => ?_⟩
  rw [map_add, H Z f fun z => (hf z).1, H' Z f fun z => (hf z).2, add_zero]

theorem LocZero.pull {π : Y ⟶ B} {c : Pic Y} (hc : LocZero π c) (k : Y' ⟶ Y) :
    LocZero (k ≫ π) (pull k c) := by
  intro p
  obtain ⟨V, hV, H⟩ := hc p
  exact ⟨V, hV, fun Z f hf => (pull_comp f k c).symm.trans (H Z (f ≫ k) hf)⟩

theorem locZero_base (π : Y ⟶ B) (d : Pic B) : LocZero π (pull π d) := by
  obtain ⟨D, hD, rfl⟩ := cls_surj d
  intro p
  obtain ⟨i, hi⟩ := exists_chart hD p
  refine ⟨D.U i, hi, fun Z f hf => (pull_comp f π _).symm.trans ?_⟩
  exact (cls_eq_zero_iff (pull_isLB hD (f ≫ π))).2
    (BoxKernel.gen_of_chart (pull_isLB hD _) (fun _ => i) fun z => mem_pull.2 (hf z))

theorem locZero_iff (π : Y ⟶ B) {M : LB Y} (hM : M.IsLB) :
    (∀ p : B, ∃ V : B.Opens, p ∈ V ∧ ∃ c : LB.Gen (M.pull (π ⁻¹ᵁ V).ι), c.IsGen) ↔ LocZero π (cls M hM) := by
  refine forall_congr' fun p => exists_congr fun V => and_congr_right fun _ => ?_
  rw [← cls_eq_zero_iff (pull_isLB hM _), cls_pull hM]
  refine ⟨fun H Z f hf => ?_, fun H => H _ _ fun z => z.2⟩
  have hr : Set.range f ⊆ Set.range (π ⁻¹ᵁ V).ι := by
    rintro _ ⟨z, rfl⟩
    rw [Scheme.Opens.range_ι]
    exact hf z
  rw [← IsOpenImmersion.lift_fac (π ⁻¹ᵁ V).ι f hr, pull_comp, H, map_zero]

end Local

section Group

variable {S : Scheme.{0}} {A T : Over S} [GrpObj A]

theorem translDiff_iff {L : LB A.left} (hL : L.IsLB) (x : T ⟶ A) :
    (∀ p : T.left, ∃ V : T.left.Opens, p ∈ V ∧
      ∃ c : LB.Gen ((Out.translDiff A L x).pull ((fst T A).left ⁻¹ᵁ V).ι), c.IsGen) ↔
      LocZero (fst T A).left (lam (cls L hL) (fst T A ≫ x) (snd T A)) := by
  have hD : (Out.translDiff A L x).IsLB := LB.isLB_linComb hL _ _
  rw [locZero_iff _ hD]
  have e : lam (cls L hL) (fst T A ≫ x) (snd T A) = cls _ hD +
      pull (fst T A).left (pull (1 : T ⟶ A).left (cls L hL) - pull x.left (cls L hL)) := by
    have e₁ : cls _ hD = pull ((fst T A ≫ x) * snd T A).left (cls L hL) - pull (snd T A).left (cls L hL) := by
      refine (cls_linComb hL _ _ hD).trans ?_
      rw [Fin.sum_univ_two]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, one_smul, neg_smul, ← sub_eq_add_neg]
      rfl
    rw [e₁, map_sub, ← pull_comp, ← pull_comp, ← Over.comp_left, ← Over.comp_left, MonObj.comp_one, lam]
    abel
  refine ⟨fun H => e ▸ H.add (locZero_base _ _), fun H => ?_⟩
  have := H.add (locZero_base _ (-(pull (1 : T ⟶ A).left (cls L hL) - pull x.left (cls L hL))))
  rwa [e, map_neg, add_neg_cancel_right] at this

theorem lam_mul_of_right [IsCommMonObj A] (c : Pic A.left) (u v y : T ⟶ A)
    (H : lam c u (v * y) = lam c u v + lam c u y) : lam c (u * v) y = lam c u y + lam c v y := by
  simp only [lam, _root_.mul_assoc] at H ⊢
  rw [← sub_eq_zero] at H ⊢
  rw [← H]
  abel

end Group

theorem kTriv_of_unimodular : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (L : LB G.left) (O : Type) [CommRing O] (bar : O →+* O) (M : Type) [AddCommGroup M] [Module O M] (h : M → M → O) [Module.Finite O M] [Module.Projective O M] (A : Over S) [GrpObj A] [IsCommMonObj A] (a : OAct O G) (b : OAct O A) (t : IsTensor A b G a M) (N : LB A.left), L.IsLB → N.IsLB → (∃ tθ : LB.Gen (Theta A N), tθ.IsGen) → (∀ m n, LBIso (cubeLB A ![fst G G ≫ t.tmul m, snd G G ≫ t.tmul n] N) (cubeLB G ![fst G G ≫ a.act (h m n), snd G G] L)) → ((∀ c, bar (bar c) = c) ∧ (∀ m m' n, h (m + m') n = h m n + h m' n) ∧ (∀ (c : O) m n, h (c • m) n = c * h m n) ∧ ∀ m n, h n m = bar (h m n)) → (∀ l : M →ₗ[O] O, ∃! n, ∀ m, l m = h m n) → Out.KTriv G L → Out.KTriv A N := by
  intro S G _ _ L O _ bar M _ _ h _ _ A _ _ a b t N hL hN hΘ hiso ⟨_, hadd, hsmul, _⟩ huni hK R _ s x hx
  have am := a.hom
  let l : M → (M →ₗ[O] O) := fun n => ⟨⟨fun m => h m n, fun m m' => hadd m m' n⟩, fun c m => hsmul c m n⟩
  let q : M → (A ⟶ G) := fun n => t.mapLeft (IsTensor.self a) (l n)
  have qm : ∀ n, IsMonHom (q n) := fun n => IsTensor.isMonHom_mapLeft _ _ _
  have hq : ∀ m n, t.tmul m ≫ q n = a.act (h m n) := fun m n => by
    simp only [q, IsTensor.tmul_mapLeft, IsTensor.self_tmul]
    rfl
  have basic : ∀ {T : Over S} (g y : T ⟶ G) (m n : M),
      lam (cls N hN) (g ≫ t.tmul m) (y ≫ t.tmul n) = lam (cls L hL) (g ≫ a.act (h m n)) y := by
    intro T g y m n
    have h₀ := (cls_eq_iff (LB.isLB_linComb hN _ _) (LB.isLB_linComb hL _ _)).2 (hiso m n)
    have h' := congrArg (pull (lift g y).left)
      ((cls_cube_two hN _ _ _).symm.trans (h₀.trans (cls_cube_two hL _ _ _)))
    simpa only [pull_lam, lift_fst, lift_snd, lift_fst_assoc, lift_snd_assoc] using h'
  have right : ∀ {T : Over S} (u v w : T ⟶ A),
      lam (cls N hN) u (v * w) = lam (cls N hN) u v + lam (cls N hN) u w := fun u v w => by
    rw [lam_comm, lam_mul_left hN hΘ, lam_comm _ v, lam_comm _ w]
  have key : ∀ {T : Over S} (n : M) (u : T ⟶ A) (y : T ⟶ G),
      lam (cls N hN) u (y ≫ t.tmul n) = lam (cls L hL) (u ≫ q n) y := by
    intro T n u
    refine t.induction_on (P := fun u => ∀ y : T ⟶ G,
      lam (cls N hN) u (y ≫ t.tmul n) = lam (cls L hL) (u ≫ q n) y) u (fun y => ?_) (fun m g y => ?_)
      fun u v hu hv y => ?_
    · rw [MonObj.one_comp, lam_one_left, lam_one_left]
    · rw [Category.assoc, hq, basic]
    · rw [lam_mul_left hN hΘ, hu, hv, MonObj.mul_comp, lam_mul_of_right]
      rw [← hu, ← hu, ← hu, MonObj.mul_comp, right]
  have H := (translDiff_iff hN x).1 hx
  have z : ∀ n, x ≫ q n = 1 := fun n => by
    refine hK R s _ ((translDiff_iff hL (x ≫ q n)).2 ?_)
    have H' := H.pull (Over.mk s ◁ t.tmul n).left
    rwa [pull_lam, ← Over.comp_left, whiskerLeft_fst, whiskerLeft_fst_assoc, whiskerLeft_snd, key,
      Category.assoc] at H'
  let P := Summand.choose O M
  let p : Fin P.n → (A ⟶ G) := fun i => t.mapLeft (IsTensor.self a) (LinearMap.proj i ∘ₗ P.incl)
  have pm : ∀ i, IsMonHom (p i) := fun i => IsTensor.isMonHom_mapLeft _ _ _
  have zp : ∀ i, x ≫ p i = 1 := fun i => by
    obtain ⟨n, hn, -⟩ := huni (LinearMap.proj i ∘ₗ P.incl)
    have e : LinearMap.proj i ∘ₗ P.incl = l n := LinearMap.ext hn
    simpa only [p, e] using z n
  have dec : ∀ u : Over.mk s ⟶ A, u = ∏ i, (u ≫ p i) ≫ t.tmul (P.proj (Pi.single i 1)) := by
    intro u
    refine t.induction_on (P := fun u => u = ∏ i, (u ≫ p i) ≫ t.tmul (P.proj (Pi.single i 1))) u ?_
      (fun m g => ?_) fun u v hu hv => ?_
    · simp only [MonObj.one_comp, Finset.prod_const_one]
    · have hx : m = ∑ i, P.incl m i • P.proj (Pi.single i 1) := by
        have e : P.proj (P.incl m) = m := congr($(P.proj_incl) m)
        simp only [← map_smul, ← map_sum]
        rw [← pi_eq_sum_univ', e]
      have hp : ∀ i, t.tmul m ≫ p i = a.act (P.incl m i) := fun i => by simp [p]
      simp only [Category.assoc, reassoc_of% hp, ← t.tmul_smul']
      refine Eq.trans ?_ (map_prod (preHom g) _ _)
      rw [← t.tmul_sum, ← hx]
      rfl
    · simp only [MonObj.mul_comp, Finset.prod_mul_distrib, ← hu, ← hv]
  rw [dec x]
  simp only [zp, MonObj.one_comp, Finset.prod_const_one]
  rfl

end GlobalTheory.HermTensorKernel
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.MultiplierIffExistsHom
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory
open scoped CategoryTheory.Obj UpperHalfPlane

namespace GlobalTheory.EllipticHom

theorem exists_coord {g : ℕ} (hg : g = 1) {w : Fin g → ℂ} (hw : w ≠ 0) :
    ∃ c : (Fin g → ℂ) →ₗ[ℂ] ℂ, (∀ x, c x • w = x) ∧ c w = 1 := by
  subst hg
  have hw0 : w 0 ≠ 0 := fun h => hw (funext fun i => by rw [Subsingleton.elim i 0, h]; rfl)
  refine ⟨(w 0)⁻¹ • LinearMap.proj 0, fun x => ?_, by simp [hw0]⟩
  funext i
  rw [Subsingleton.elim i 0]
  simp only [LinearMap.smul_apply, LinearMap.proj_apply, Pi.smul_apply, smul_eq_mul]
  field_simp

theorem exists_index {L L' : PeriodPair} {α : ℂ} (h : ∀ z ∈ L.lattice, α * z ∈ L'.lattice) :
    ∃ n : ℕ, Complex.normSq α * |(L.ω₁ * starRingEnd ℂ L.ω₂).im| = n * |(L'.ω₁ * starRingEnd ℂ L'.ω₂).im| := by
  obtain ⟨p, q, h1⟩ := PeriodPair.mem_lattice.1 (h _ L.ω₁_mem_lattice)
  obtain ⟨r, s, h2⟩ := PeriodPair.mem_lattice.1 (h _ L.ω₂_mem_lattice)
  refine ⟨(p * s - q * r).natAbs, ?_⟩
  have e : Complex.normSq α * (L.ω₁ * starRingEnd ℂ L.ω₂).im =
      ((p * s - q * r : ℤ) : ℝ) * (L'.ω₁ * starRingEnd ℂ L'.ω₂).im := by
    have e1 : Complex.normSq α * (L.ω₁ * starRingEnd ℂ L.ω₂).im = ((α * L.ω₁) * starRingEnd ℂ (α * L.ω₂)).im := by
      simp [Complex.normSq_apply]
      ring
    rw [e1, ← h1, ← h2]
    simp
    ring
  rw [Nat.cast_natAbs, Int.cast_abs, ← abs_mul, ← e, abs_mul, abs_of_nonneg (Complex.normSq_nonneg α)]

theorem covolume_ne_zero (L : PeriodPair) : (L.ω₁ * starRingEnd ℂ L.ω₂).im ≠ 0 := by
  intro h
  have hi := LinearIndependent.pair_iff.1 L.indep
  simp at h
  have h1 := hi L.ω₂.re (-L.ω₁.re) (by
    apply Complex.ext <;> simp <;> linarith)
  have h2 := hi L.ω₂.im (-L.ω₁.im) (by
    apply Complex.ext <;> simp <;> linarith)
  have h3 := hi 0 1 (by
    apply Complex.ext <;> simp [h1.1, h2.1])
  exact one_ne_zero h3.2

theorem multiplier_iff_exists_hom : ThetaUnifAV → Out.PolBaseChangeSt → ∀ (R : Type) [CommRing R] (P Q : Out.PolAV (Sp R)) (v : epsR R ⟶ P.A) (t : epsR R ⟶ Q.A) (s : R →+* ℂ) (L L' : PeriodPair) (α : ℂ), P.g = 1 → Q.g = 1 → IsTangent v → IsTangent t → (∀ (P' : Out.PolAV (Sp ℂ)) (φ' : P'.A.left ⟶ P.A.left) (v' : epsR ℂ ⟶ P'.A) (u' : HolUnif P'.A P'.L P'.g) (w' : Fin P'.g → ℂ), IsPolFibre s P P' φ' → IsVecOver s φ' v v' → u'.IsDiff w' v' → w' ≠ 0 ∧ ∀ z : ℂ, z ∈ L.lattice ↔ z • w' ∈ u'.Λ) → (∀ (P' : Out.PolAV (Sp ℂ)) (φ' : P'.A.left ⟶ Q.A.left) (v' : epsR ℂ ⟶ P'.A) (u' : HolUnif P'.A P'.L P'.g) (w' : Fin P'.g → ℂ), IsPolFibre s Q P' φ' → IsVecOver s φ' t v' → u'.IsDiff w' v' → w' ≠ 0 ∧ ∀ z : ℂ, z ∈ L'.lattice ↔ z • w' ∈ u'.Λ) → ((∀ z ∈ L.lattice, α * z ∈ L'.lattice) ↔ (∀ (P₁ Q₁ : Out.PolAV (Sp ℂ)) (φ₁ : P₁.A.left ⟶ P.A.left) (ψ₁ : Q₁.A.left ⟶ Q.A.left) (v₁ : epsR ℂ ⟶ P₁.A) (t₁ : epsR ℂ ⟶ Q₁.A), IsPolFibre s P P₁ φ₁ → IsPolFibre s Q Q₁ ψ₁ → IsVecOver s φ₁ v v₁ → IsVecOver s ψ₁ t t₁ → ∃ f₁ : P₁.A ⟶ Q₁.A, IsMonHom f₁ ∧ IsLieComb ![α] ![t₁] (v₁ ≫ f₁))) := by
  intro hU hB R _ P Q v t s L L' α hP hQ hv ht hL hL'
  constructor
  · intro hα P₁ Q₁ φ₁ ψ₁ v₁ t₁ hφ hψ hv₁ ht₁
    obtain ⟨rig, hrig⟩ := P₁.rigid
    obtain ⟨rig', hrig'⟩ := Q₁.rigid
    obtain ⟨u, Hm, χ, Ef, hA, -, hd, -, -, hθ, hE, hEb, -⟩ := hU P₁ rig hrig
    obtain ⟨u', Hm', χ', Ef', hA', -, hd', he', -, hθ', hE', hEb', -⟩ := hU Q₁ rig' hrig'
    have tv := hv₁.isTangent hφ.2.1 hv
    have tt := ht₁.isTangent hψ.2.1 ht
    obtain ⟨w, hw, -⟩ := hd v₁ tv
    obtain ⟨w', hw', -⟩ := hd' t₁ tt
    obtain ⟨w0, hΛ⟩ := hL P₁ φ₁ v₁ u w hφ hv₁ hw
    obtain ⟨w0', hΛ'⟩ := hL' Q₁ ψ₁ t₁ u' w' hψ ht₁ hw'
    have g1 : P₁.g = 1 := hφ.1.trans hP
    have g2 : Q₁.g = 1 := hψ.1.trans hQ
    have hH := hermForm_principal_dim_one _ u.Λ w L Hm Ef g1 w0 hΛ hA.1 (hA.2.1 w w0) hE hEb
    have hH' := hermForm_principal_dim_one _ u'.Λ w' L' Hm' Ef' g2 w0' hΛ' hA'.1 (hA'.2.1 w' w0') hE' hEb'
    obtain ⟨c, hc, hc1⟩ := exists_coord g1 w0
    obtain ⟨n, hn⟩ := exists_index hα
    let F : (Fin P₁.g → ℂ) →ₗ[ℂ] (Fin Q₁.g → ℂ) := (α • c).smulRight w'
    have hF : ∀ x, F x = (α * c x) • w' := fun x => rfl
    obtain ⟨f, hf, hFf⟩ := exists_hom_of_linear_scaling_hermForm P₁ Q₁ u u' Hm χ Hm' χ' hA hA'
      (fun k => (hθ k).2) (fun k => (hθ' k).1) F n
      (fun l hl => by
        rw [hF, ← hΛ']
        exact hα _ ((hΛ _).2 (by rwa [hc])))
      (fun x y => by
        have e := hH (c x) (c y)
        rw [hc, hc] at e
        have a1 : ((|(L.ω₁ * starRingEnd ℂ L.ω₂).im| : ℝ) : ℂ) ≠ 0 := by
          exact_mod_cast abs_ne_zero.2 (covolume_ne_zero L)
        have a2 : ((|(L'.ω₁ * starRingEnd ℂ L'.ω₂).im| : ℝ) : ℂ) ≠ 0 := by
          exact_mod_cast abs_ne_zero.2 (covolume_ne_zero L')
        have hn' := congrArg (fun r : ℝ => (r : ℂ)) hn
        simp only [Complex.ofReal_mul, Complex.ofReal_natCast, ← Complex.mul_conj] at hn'
        rw [hF, hF, hH', e, map_mul, ← mul_div_assoc, div_eq_div_iff a2 a1]
        linear_combination (c x * starRingEnd ℂ (c y)) * hn')
    refine ⟨f, hf, ?_⟩
    have h1 := HomLinear.isDiff_comp u u' f F hFf tv hw
    rw [hF, hc1, _root_.mul_one] at h1
    have hx := (LieMultiple.isLieComb_one_iff_comp α t₁ _).2 rfl
    have hxt : IsTangent (Chart.spMap (Chart.scaleD α) ≫ t₁) :=
      (Chart.isTan_iff _).1 (Chart.isTan_scale α ((Chart.isTan_iff _).2 tt))
    have := (he' (α • w')).unique ⟨HomLinear.isTangent_comp f tv, h1⟩
      ⟨hxt, CMNormIdentity.isDiff_of_isLieComb u' hw' α hx⟩
    rw [this]
    exact hx
  · intro h z hz
    obtain ⟨P₁, φ₁, hφ⟩ := exists_isPolFibre hB s P
    obtain ⟨Q₁, ψ₁, hψ⟩ := exists_isPolFibre hB s Q
    obtain ⟨v₁, hv₁, -⟩ := existsUnique_isVecOver hφ.2.1.1 v
    obtain ⟨t₁, ht₁, -⟩ := existsUnique_isVecOver hψ.2.1.1 t
    obtain ⟨f, hf, hl⟩ := h P₁ Q₁ φ₁ ψ₁ v₁ t₁ hφ hψ hv₁ ht₁
    obtain ⟨rig, hrig⟩ := P₁.rigid
    obtain ⟨rig', hrig'⟩ := Q₁.rigid
    obtain ⟨u, -, -, -, -, -, hd, -⟩ := hU P₁ rig hrig
    obtain ⟨u', -, -, -, -, -, hd', he', -⟩ := hU Q₁ rig' hrig'
    have tv := hv₁.isTangent hφ.2.1 hv
    have tt := ht₁.isTangent hψ.2.1 ht
    obtain ⟨w, hw, -⟩ := hd v₁ tv
    obtain ⟨w', hw', -⟩ := hd' t₁ tt
    obtain ⟨-, hΛ⟩ := hL P₁ φ₁ v₁ u w hφ hv₁ hw
    obtain ⟨-, hΛ'⟩ := hL' Q₁ ψ₁ t₁ u' w' hψ ht₁ hw'
    obtain ⟨F, -, hF, hT, -⟩ := HomLinear.exists_linear_of_isMonHom P₁.A Q₁.A P₁.isAb Q₁.isAb P₁.L Q₁.L _ _ u u'
      hd' he' f hf
    obtain ⟨tf, df⟩ := hT w v₁ tv hw
    have e : F w = α • w' := (hd' _ tf).unique df (CMNormIdentity.isDiff_of_isLieComb u' hw' α hl)
    have := hF _ ((hΛ z).1 hz)
    rw [map_smul, e, smul_smul, _root_.mul_comm] at this
    exact (hΛ' _).2 this

end GlobalTheory.EllipticHom
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.OriginLineBundlePolarisation
section
set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.WeierstrassCurve GlobalTheory.AddLaw

namespace GlobalTheory.WeierstrassCurve

theorem appLE_top_eq_zero_iff {X T : Scheme.{0}} (t : T ⟶ X) {U : X.Opens} (h : ⊤ ≤ t ⁻¹ᵁ U)
    (a : Γ(X, U)) : (t.appLE U ⊤ h).hom a = 0 ↔ (t.app U).hom a = 0 := by
  have e : (t.appLE U ⊤ h).hom a = resG _ h ((t.app U).hom a) := rfl
  rw [e]
  refine ⟨fun h0 => ?_, fun h0 => by rw [h0, map_zero]⟩
  have := congrArg (resG _ (le_top : t ⁻¹ᵁ U ≤ ⊤)) h0
  rwa [Cartier.resG_resG, Cartier.resG_self, map_zero] at this

theorem appLE_originSec_eq_zero_iff {R : Type} [CommRing R] (W : WeierstrassCurve R) {T : Scheme.{0}}
    (t : T ⟶ scheme W) (i : (originLB W).ι) (h : ⊤ ≤ t ⁻¹ᵁ (originLB W).U i) :
    (t.appLE ((originLB W).U i) ⊤ h).hom ((originSec W).f i) = 0 ↔ t = t ≫ toSpec W ≫ zero W := by
  rw [appLE_top_eq_zero_iff]
  constructor
  · intro h0
    rcases i with _ | _
    · have h1 : (1 : Γ(T, t ⁻¹ᵁ coordOpen W 2)) = 0 := (map_one _).symm.trans h0
      have hT : IsEmpty T := ⟨fun p => by
        have := congrArg (T.presheaf.germ (t ⁻¹ᵁ coordOpen W 2) p (h (Set.mem_univ p))).hom h1
        rw [map_one, map_zero] at this
        exact absurd this one_ne_zero⟩
      refine (eq_comp_zero_iff W t).2 ⟨fun p _ => (hT.false p).elim, Cartier.ext_germ fun p _ => (hT.false p).elim⟩
    · exact (eq_comp_zero_iff W t).2 ⟨h, h0⟩
  · intro e
    have h0 := (secPull_originSec_eq_zero_iff W t).2 e (fun _ => i)
    have := congrArg (resG T (Cartier.pull_U (originLB W) t (fun _ => i)).ge) h0
    rw [map_zero] at this
    exact ((Cartier.resG_resG _ _ _).trans (Cartier.resG_self _ _)).symm.trans this

theorem appLE_sec_pull_originLB_eq_zero {R : Type} [CommRing R] (W : WeierstrassCurve R)
    {R' : Type} [CommRing R'] {f : Sp R' ⟶ Sp R} {Y : Scheme.{0}} {φ : Y ⟶ scheme W} {q : Y ⟶ Sp R'}
    (H : IsPullback φ q (toSpec W) f) (s : ((originLB W).pull φ).Sec) {T : Scheme.{0}} (t : T ⟶ Y)
    (j : ((originLB W).pull φ).ι) (h : ⊤ ≤ t ⁻¹ᵁ ((originLB W).pull φ).U j)
    (e : t ≫ φ = t ≫ φ ≫ toSpec W ≫ zero W) :
    (t.appLE (((originLB W).pull φ).U j) ⊤ h).hom (s.f j) = 0 := by
  obtain ⟨c, hc, -⟩ := existsUnique_eq_appLE_mul_secPull W H s
  have h' : ⊤ ≤ (t ≫ φ) ⁻¹ᵁ (originLB W).U (j ⟨⟩) :=
    fun p hp => (Cartier.pull_U (originLB W) φ j).le (h hp)
  have h0 := (appLE_originSec_eq_zero_iff W (t ≫ φ) (j ⟨⟩) h').2 (e.trans (Category.assoc _ _ _).symm)
  have h1 : (t.appLE (((originLB W).pull φ).U j) ⊤ h).hom
      ((Cartier.secPull (originSec W) φ).f j) = 0 := by
    refine Eq.trans ?_ h0
    have := Scheme.Hom.appLE_comp_appLE t φ ((originLB W).U (j ⟨⟩)) _ ⊤
      (Cartier.pull_U (originLB W) φ j).le h
    exact congrArg (fun g => g.hom ((originSec W).f (j ⟨⟩))) this
  rw [hc j, map_mul, h1, mul_zero]

theorem originLB_polarisation (R : Type) [CommRing R] (W : WeierstrassCurve R) [GrpObj (schemeOver W)]
    (_hc : IsCommMonObj (schemeOver W)) (he : η[schemeOver W].left = zero W) :
    Out.Rigidified (schemeOver W) (originLB W) ∧ Out.Sym (schemeOver W) (originLB W) ∧
      Out.RelAmple (schemeOver W) (originLB W) ∧ Out.KTriv (schemeOver W) (originLB W) := by
  have he' : eSec (schemeOver W) = zero W := he
  have hz : ∀ (T : Scheme.{0}) (t : T ⟶ (schemeOver W).left) (i : (originLB W).ι)
      (h : ⊤ ≤ t ⁻¹ᵁ (originLB W).U i),
      (t.appLE ((originLB W).U i) ⊤ h).hom ((originSec W).f i) = 0 ↔
        t = t ≫ (schemeOver W).hom ≫ eSec (schemeOver W) := fun T t i h => by
    rw [he']
    exact appLE_originSec_eq_zero_iff W t i h
  refine ⟨?_, ?_, relAmple_originLB W, ?_⟩
  · unfold Out.Rigidified
    rw [he']
    exact ⟨_, isGen_one_pull_zero W⟩
  · exact GlobalTheory.T.symmetric_lineBundle_of_regular_section _ (schemeOver W) (originLB W) (originSec W) (originLB_isLB W)
      (fun i V h => ((isRegularSec_originSec W i).resG h).mem) hz
  · refine GlobalTheory.T.kernelPolarisation_trivial_of_sections_vanish_zero _ (schemeOver W) (originLB W) (originSec W) (originLB_isLB W) hz ?_
    intro R' _ f Y φ q H s T t j h e
    rw [he'] at e
    exact appLE_sec_pull_originLB_eq_zero W H s t j h e

end GlobalTheory.WeierstrassCurve
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ThetaLineDualDegreeOfKeyFormulaPowerForm
section
noncomputable section

open NumberField IsDedekindDomain MeasureTheory IsLocalRing Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.LamCM
open scoped nonZeroDivisors ComplexOrder

namespace GlobalTheory

theorem isLocGen_pow_div_pow {K : Type} [Field K] [NumberField K] {p : HeightOneSpectrum (𝓞 K)} {ca cd : K}
    {A B : FractionalIdeal (𝓞 K)⁰ K} (m n : ℕ) (hA : A ≠ 0) (hB : B ≠ 0) (ha : IsLocGen p ca A) (hb : IsLocGen p cd B) :
    IsLocGen p (ca ^ m / cd ^ n) (A ^ m * (B ^ n)⁻¹) := by
  refine ⟨div_ne_zero (pow_ne_zero _ ha.1) (pow_ne_zero _ hb.1), ?_⟩
  have hsa : FractionalIdeal.spanSingleton (𝓞 K)⁰ ca ≠ 0 := by
    rw [Ne, FractionalIdeal.spanSingleton_eq_zero_iff]; exact ha.1
  have hsb : FractionalIdeal.spanSingleton (𝓞 K)⁰ cd ≠ 0 := by
    rw [Ne, FractionalIdeal.spanSingleton_eq_zero_iff]; exact hb.1
  have hs : FractionalIdeal.spanSingleton (𝓞 K)⁰ (ca ^ m / cd ^ n) =
      FractionalIdeal.spanSingleton (𝓞 K)⁰ ca ^ m * (FractionalIdeal.spanSingleton (𝓞 K)⁰ cd ^ n)⁻¹ := by
    rw [FractionalIdeal.spanSingleton_pow, FractionalIdeal.spanSingleton_pow, FractionalIdeal.spanSingleton_inv,
      FractionalIdeal.spanSingleton_mul_spanSingleton, div_eq_mul_inv]
  rw [hs, FractionalIdeal.count_mul K p (pow_ne_zero _ hsa) (inv_ne_zero (pow_ne_zero _ hsb)),
    FractionalIdeal.count_mul K p (pow_ne_zero _ hA) (inv_ne_zero (pow_ne_zero _ hB)),
    FractionalIdeal.count_inv, FractionalIdeal.count_inv, FractionalIdeal.count_pow, FractionalIdeal.count_pow,
    FractionalIdeal.count_pow, FractionalIdeal.count_pow, ha.2, hb.2]

theorem thetaLine_dual_deg_of_keyFormulaPow : GlobalTheory.KeyFormulaPow → ∀ (K : Type) [Field K] [NumberField K] (x : KeyIn K)
    (T abelian₂ : MLine K), T.Good → abelian₂.Good → (∀ p, KeyLocAt x T abelian₂ p) → (∀ σ, KeyArchAt x T abelian₂ σ) →
    T.dual.deg = (1 / 2) * abelian₂.dual.deg + (x.P.g : ℝ) / 4 * (Module.finrank ℚ K : ℝ) * Real.log (2 * Real.pi) := by
  intro hKF K _ _ x T abelian₂ hT hL hloc harch
  obtain ⟨N, hN, κ, hH, hF, hU1, -, hU2⟩ := hKF
  obtain ⟨n, hn⟩ : ∃ n, n = N x.P.g := ⟨_, rfl⟩
  have hn1 : 1 ≤ n := hn ▸ hN _
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
  set k : K := (κ K x : K) with hkdef
  have hk : k ≠ 0 := (κ K x).ne_zero
  have hloc' : ∀ p : HeightOneSpectrum (𝓞 K), ∃ ca cd : K, IsLocGen p ca T.I ∧ IsLocGen p cd abelian₂.I ∧
      p.valuation K k ≤ p.valuation K (ca ^ (8 * n) / cd ^ (4 * n)) ∧
      p.valuation K k⁻¹ ≤ p.valuation K (ca ^ (8 * n) / cd ^ (4 * n))⁻¹ := by
    intro p
    obtain ⟨K', _, _, R, _, _, _, _, _, f, x', a, d, ca, cd, ua, ud, hPB, hInt, hval, ha, hd, hca, hcd⟩ := hloc p
    obtain ⟨th', hth', v', hv', M, xR, hth'eq, hv'eq, hMdet, hPBR⟩ := hInt
    have hFx : (κ K' x' : K') = f k := hF K K' f x x' hPB
    have hg : x'.P.g = x.P.g := by obtain ⟨-, -, -, hg, -⟩ := hPB; exact hg
    have hn2 : N x'.P.g = n := by rw [hg, hn]
    have hHx : a ^ (8 * N x'.P.g) * (κ K' ⟨x'.P, x'.g_pos, x'.rig, x'.rig_gen, th', hth', v', hv'⟩ : K') =
        M.det ^ (4 * N x'.P.g) * (κ K' x' : K') :=
      hH K' x'.P x'.g_pos x'.rig x'.rig_gen x'.th x'.th_ne x'.v x'.basis th' hth' v' hv' a M hth'eq hv'eq
    obtain ⟨u, hu, -⟩ := hU1 R K' xR _ hPBR
    rw [hn2, hu, hFx, hMdet, ha, hd] at hHx
    generalize 8 * n = r at hHx ⊢
    generalize 4 * n = s at hHx ⊢
    have hfa : f ca ≠ 0 := (map_ne_zero f).2 hca.1
    have hfd : f cd ≠ 0 := (map_ne_zero f).2 hcd.1
    have hD : algebraMap R K' (ud : R) ≠ 0 := (ud.isUnit.map (algebraMap R K')).ne_zero
    have hc : ca ^ r / cd ^ s ≠ 0 := div_ne_zero (pow_ne_zero _ hca.1) (pow_ne_zero _ hcd.1)
    have hfk : f k = (f ca * algebraMap R K' (ua : R)) ^ r * algebraMap R K' (u : R) /
        (f cd * algebraMap R K' (ud : R)) ^ s := by
      rw [eq_div_iff (pow_ne_zero _ (mul_ne_zero hfd hD)), hHx]; ring
    have hw : f (k / (ca ^ r / cd ^ s)) = algebraMap R K' ((ua ^ r * u * ud⁻¹ ^ s : Rˣ) : R) := by
      rw [Units.val_mul, Units.val_mul, Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val, map_mul, map_mul,
        map_pow, map_pow, map_units_inv, map_div₀, map_div₀, map_pow, map_pow, hfk, mul_pow, mul_pow, inv_pow]
      field_simp
    have hw' : f (k⁻¹ / (ca ^ r / cd ^ s)⁻¹) = algebraMap R K' (((ua ^ r * u * ud⁻¹ ^ s)⁻¹ : Rˣ) : R) := by
      rw [inv_div_inv, ← inv_div, map_inv₀, hw, map_units_inv]
    exact ⟨ca, cd, hca, hcd, valuation_le_of_eq_algebraMap p f hval hc _ hw,
      valuation_le_of_eq_algebraMap p f hval (inv_ne_zero hc) _ hw'⟩
  have hJ : T.I ^ (8 * n) * (abelian₂.I ^ (4 * n))⁻¹ ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ hT.1) (inv_ne_zero (pow_ne_zero _ hL.1))
  have hspan : FractionalIdeal.spanSingleton (𝓞 K)⁰ k = T.I ^ (8 * n) * (abelian₂.I ^ (4 * n))⁻¹ := by
    have hsk : FractionalIdeal.spanSingleton (𝓞 K)⁰ k ≠ 0 := by
      rw [Ne, FractionalIdeal.spanSingleton_eq_zero_iff]; exact hk
    refine eq_of_count_eq hsk hJ (fun p => ?_)
    obtain ⟨ca, cd, h1, h2, h3, h4⟩ := hloc' p
    have h5 := isLocGen_pow_div_pow (8 * n) (4 * n) hT.1 hL.1 h1 h2
    rw [count_eq_of_valuation_le p hk h5.1 h3 h4, h5.2]
  have hNT : ((FractionalIdeal.absNorm T.I : ℚ) : ℝ) ≠ 0 := by
    exact_mod_cast (FractionalIdeal.absNorm_eq_zero_iff.not.2 hT.1)
  have hNL : ((FractionalIdeal.absNorm abelian₂.I : ℚ) : ℝ) ≠ 0 := by
    exact_mod_cast (FractionalIdeal.absNorm_eq_zero_iff.not.2 hL.1)
  have hNk : Real.log ((FractionalIdeal.absNorm (FractionalIdeal.spanSingleton (𝓞 K)⁰ k) : ℚ) : ℝ) =
      n * (8 * Real.log ((FractionalIdeal.absNorm T.I : ℚ) : ℝ) -
        4 * Real.log ((FractionalIdeal.absNorm abelian₂.I : ℚ) : ℝ)) := by
    rw [hspan, map_mul, map_inv₀, map_pow, map_pow]
    push_cast
    rw [Real.log_mul (pow_ne_zero _ hNT) (inv_ne_zero (pow_ne_zero _ hNL)), Real.log_inv, Real.log_pow,
      Real.log_pow]
    push_cast
    ring
  have harch' : ∀ σ : K →+* ℂ, Real.log ‖σ k‖ + 8 * n * Real.log (T.n σ) - 4 * n * Real.log (abelian₂.n σ) =
      2 * (x.P.g : ℝ) * n * Real.log (2 * Real.pi) := by
    intro σ
    obtain ⟨xσ, u, Hm, W, χ, θ, Fd, hPB, hAH, hRig, hFn, hDiff, hFD, hTn, hLn⟩ := harch σ
    have hFσ : (κ ℂ xσ : ℂ) = σ k := hF K ℂ σ x xσ hPB
    obtain ⟨_, _, _, hg, _⟩ := hPB
    have he : (volume Fd).toReal / (Real.pi ^ xσ.P.g * ‖W.det‖ ^ 2) = (abelian₂.n σ ^ 2)⁻¹ := by
      rw [hLn, inv_div]
    have hU := hU2 xσ u Hm W χ θ Fd _ _ hAH hRig hFn hDiff hFD hTn rfl
    rw [he, hFσ, hg, ← hn] at hU
    have hsk0 : 0 < ‖σ k‖ := norm_pos_iff.2 ((map_ne_zero σ).2 hk)
    have ht := hT.2 σ
    have hl := hL.2 σ
    have := congrArg Real.log hU
    rw [Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity)] at this
    simp only [Real.log_pow, Real.log_inv] at this
    push_cast at this
    linarith
  have hsum := Finset.sum_congr (s₁ := (Finset.univ : Finset (K →+* ℂ))) rfl (fun σ _ => harch' σ)
  rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, Finset.sum_const,
    Finset.card_univ, NumberField.Embeddings.card K ℂ, nsmul_eq_mul, sum_log_norm_embeddings hk, hNk] at hsum
  simp only [MLine.deg, MLine.dual, map_inv₀, Rat.cast_inv, Real.log_inv, Finset.sum_neg_distrib]
  refine mul_left_cancel₀ hn' ?_
  linarith

end GlobalTheory
end
end

