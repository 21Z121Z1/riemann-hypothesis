import Mathlib
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ReductionSurjectiveOfIsNilpotent
import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.JetPointAddSqZeroEqProdMulTangent
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0035
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0033
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0028
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.UnivFrame
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.NormConst
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0011
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0008
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0010
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0003
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Development.AbelianVarietyTheory.PublishedTheorems.Landherr₂.Bundle0001
import Development.AbelianVarietyTheory.Statements.HyperbolicHypotheses.HypothesesInhabitedHyperbolic
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0002
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0037
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0038

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsUniqueCoord
section
set_option autoImplicit false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Chart
open scoped CategoryTheory.MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp epsR IsTangent IsLieComb IsLieBasis)
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.NilChart

open SqZero

variable {R : Type} [CommRing R] {B : Type} [CommRing B] [Algebra R B]

def augAlg (R : Type) [CommRing R] {B : Type} [CommRing B] [Algebra R B] (I : Ideal B) : Subalgebra R (R × B) :=
  AlgHom.equalizer ((Ideal.Quotient.mkₐ R I).comp (AlgHom.snd R R B))
    ((Ideal.Quotient.mkₐ R I).comp ((Algebra.ofId R B).comp (AlgHom.fst R R B)))

theorem mem_augAlg {I : Ideal B} {b : R × B} : b ∈ augAlg R I ↔ b.2 - algebraMap R B b.1 ∈ I :=
  Ideal.Quotient.eq

theorem mk_comp_eq {κ : Type} {m : ℕ} {I : Ideal B} (ψ : JetR R κ m →ₐ[R] B) (h : ∀ j, ψ (zR m j) ∈ I) :
    (Ideal.Quotient.mkₐ R I).comp ψ = (Algebra.ofId R _).comp (jetAug R κ m) :=
  jet_ext fun j => by
    rw [AlgHom.comp_apply, AlgHom.comp_apply, jetAug_zR, map_zero]
    exact Ideal.Quotient.eq_zero_iff_mem.2 (h j)

variable {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G] (hG : Smooth G.hom) {d : ℕ}
  {v : Fin d → (epsR R ⟶ G)} (hv : IsLieBasis v) {x : ∀ m : ℕ, sp (R₀ := R) (JetR R (Fin d) m) ⟶ G}
  (hx₁ : ∀ m, spMap (jetTruncR R (Fin d) m) ≫ x (m + 1) = x m)
  (hx₂ : ∀ m, spMap (jetZeroR R (Fin d) m) ≫ x m = 1)
  (hx₃ : ∀ j, spMap (dualLift (Pi.single j (1 : R))) ≫ x 1 = v j)

include hG hv hx₁ hx₂ hx₃

theorem move {I J : Ideal B} (hJ : J * I = ⊥) (hle : J ≤ I) {m : ℕ} (ψ ψ' : JetR R (Fin d) m →ₐ[R] B)
    (hψ : ∀ j, ψ (zR m j) ∈ I) (c : Fin d → B) (hcJ : ∀ j, c j ∈ J) (hc : ∀ j, c j * c j = 0)
    (h : ∀ j, ψ' (zR m j) = ψ (zR m j) + c j) : spMap ψ' ≫ x m = lieExp v c hc * (spMap ψ ≫ x m) := by
  have hψ' : ∀ j, ψ' (zR m j) ∈ I := fun j => by rw [h]; exact add_mem (hψ j) (hle (hcJ j))
  let aug : augAlg R I →ₐ[R] R := (AlgHom.fst R R B).comp (augAlg R I).val
  let p : augAlg R I →ₐ[R] B := (AlgHom.snd R R B).comp (augAlg R I).val
  let up : ∀ φ : JetR R (Fin d) m →ₐ[R] B, (∀ j, φ (zR m j) ∈ I) → (JetR R (Fin d) m →ₐ[R] augAlg R I) :=
    fun φ hφ => ((jetAug R (Fin d) m).prod φ).codRestrict _ fun a => by
      have := AlgHom.congr_fun (mk_comp_eq φ hφ) a
      exact this
  let J' : Ideal (augAlg R I) := J.comap p ⊓ RingHom.ker aug
  have hker : ∀ a : augAlg R I, a ∈ RingHom.ker aug → p a ∈ I := fun a ha => by
    have h1 : a.1.1 = 0 := ha
    have h2 := mem_augAlg.1 a.2
    rw [h1, map_zero, sub_zero] at h2
    exact h2
  have hJ' : J' * RingHom.ker aug = ⊥ := by
    rw [← le_bot_iff, Ideal.mul_le]
    intro a ha b hb
    have h1 : a.1.1 = 0 := ha.2
    have h2 : p a * p b ∈ J * I := Ideal.mul_mem_mul ha.1 (hker b hb)
    rw [hJ] at h2
    exact Subtype.ext (Prod.ext (show a.1.1 * b.1.1 = 0 by rw [h1, zero_mul]) h2)
  let c' : Fin d → augAlg R I := fun j => ⟨(0, c j), mem_augAlg.2 (by simpa using hle (hcJ j))⟩
  have hc' : ∀ j, c' j * c' j = 0 := fun j => Subtype.ext (Prod.ext (mul_zero _) (hc j))
  have he : ∀ j, epsTo R (c' j) (hc' j) (TrivSqZeroExt.inr 1) = c' j := fun j => epsTo_eps _ _
  have key := jet_add_sqZero_eq_prod_mul R G hG d v hv x hx₁ hx₂ hx₃ _ aug J' hJ' inf_le_right m
    (up ψ hψ) (up ψ' hψ') rfl rfl (fun j => epsTo R (c' j) (hc' j))
    (fun j => by rw [he]; exact ⟨hcJ j, rfl⟩)
    (fun j => by
      rw [he]
      exact Subtype.ext (Prod.ext (add_zero _).symm (h j)))
  have fin := congrArg (spMap p ≫ ·) key
  change spMap p ≫ spMap _ ≫ x m = spMap p ≫ (lieExp v c' hc' * (spMap _ ≫ x m)) at fin
  rw [MonObj.comp_mul, comp_lieExp, ← Category.assoc, ← Category.assoc, spMap_comp, spMap_comp] at fin
  exact fin

theorem eq_of_sub_mem {I J : Ideal B} (hJ : J * I = ⊥) (hle : J ≤ I) {m : ℕ} (ψ ψ' : JetR R (Fin d) m →ₐ[R] B)
    (hψ : ∀ j, ψ (zR m j) ∈ I) (hδ : ∀ j, ψ' (zR m j) - ψ (zR m j) ∈ J)
    (h : spMap ψ ≫ x m = spMap ψ' ≫ x m) : ψ = ψ' := by
  have hJ2 : J ^ 2 = ⊥ := by
    rw [← le_bot_iff, pow_two, ← hJ]
    exact Ideal.mul_mono_right hle
  let c : Fin d → J := fun j => ⟨_, hδ j⟩
  have hc : ∀ j, (c j : B) * (c j : B) = 0 := fun j => mul_eq_zero_of_sq hJ2 (c j).2 (c j).2
  have key := move hG hv hx₁ hx₂ hx₃ hJ hle ψ ψ' hψ (fun j => c j) (fun j => (c j).2) hc
    (fun j => (add_sub_cancel _ _).symm)
  rw [← h] at key
  have h1 : lieExp v (fun j => (c j : B)) hc = 1 := mul_eq_right.1 key.symm
  have h0 : c = 0 := by
    apply (expHom_bijective hv hJ2).1
    rw [map_zero]
    exact congrArg Additive.ofMul (Subtype.ext h1)
  refine jet_ext fun j => ?_
  have : ψ' (zR m j) - ψ (zR m j) = 0 := congrArg Subtype.val (congrFun h0 j)
  exact (sub_eq_zero.1 this).symm

theorem eq_of_nil {N : Ideal B} (hN : IsNilpotent N) {m : ℕ} (ψ ψ' : JetR R (Fin d) m →ₐ[R] B)
    (hψ : ∀ j, ψ (zR m j) ∈ N) (hψ' : ∀ j, ψ' (zR m j) ∈ N)
    (h : spMap ψ ≫ x m = spMap ψ' ≫ x m) : ψ = ψ' := by
  have main : ∀ k j, ψ' (zR m j) - ψ (zR m j) ∈ N ^ (k + 1) := by
    intro k
    induction k with
    | zero =>
      intro j
      rw [zero_add, pow_one]
      exact sub_mem (hψ' j) (hψ j)
    | succ k ih =>
      let q : B →ₐ[R] B ⧸ N ^ (k + 1 + 1) := Ideal.Quotient.mkₐ R _
      have e := eq_of_sub_mem hG hv hx₁ hx₂ hx₃ (I := N.map q) (J := (N ^ (k + 1)).map q)
        (by rw [← Ideal.map_mul, ← pow_succ]; exact Ideal.map_quotient_self _)
        (Ideal.map_mono (Ideal.pow_le_self (by omega)))
        (q.comp ψ) (q.comp ψ') (fun j => Ideal.mem_map_of_mem _ (hψ j))
        (fun j => by
          rw [AlgHom.comp_apply, AlgHom.comp_apply, ← map_sub]
          exact Ideal.mem_map_of_mem _ (ih j))
        (by rw [← spMap_comp, ← spMap_comp, Category.assoc, Category.assoc, h])
      intro j
      exact Ideal.Quotient.eq.1 (AlgHom.congr_fun e (zR m j)).symm
  obtain ⟨n, hn⟩ := hN
  refine jet_ext fun j => ?_
  have := main n j
  rw [pow_succ, hn, zero_mul, Ideal.zero_eq_bot, Ideal.mem_bot] at this
  exact (sub_eq_zero.1 this).symm

theorem coord_unique {m : ℕ} (ψ ψ' : JetR R (Fin d) m →ₐ[R] B) (h : spMap ψ ≫ x m = spMap ψ' ≫ x m) : ψ = ψ' := by
  have nil : ∀ φ : JetR R (Fin d) m →ₐ[R] B, IsNilpotent ((RingHom.ker (jetAug R (Fin d) m)).map φ) := fun φ =>
    ⟨m + 1, by rw [← Ideal.map_pow, ker_jetAug_pow, Ideal.map_bot, Ideal.zero_eq_bot]⟩
  refine eq_of_nil hG hv hx₁ hx₂ hx₃ (N := (RingHom.ker (jetAug R (Fin d) m)).map ψ +
    (RingHom.ker (jetAug R (Fin d) m)).map ψ') ((Commute.all _ _).isNilpotent_add (nil ψ) (nil ψ')) ψ ψ'
    (fun j => Ideal.mem_sup_left (Ideal.mem_map_of_mem _ (zR_mem_ker m j)))
    (fun j => Ideal.mem_sup_right (Ideal.mem_map_of_mem _ (zR_mem_ker m j))) h

theorem coord_exists {m : ℕ} {N : Ideal B} (hN : N ^ (m + 1) = ⊥) (y : sp (R₀ := R) B ⟶ G)
    (hy : spMap (Ideal.Quotient.mkₐ R N) ≫ y = 1) : ∃ ψ : JetR R (Fin d) m →ₐ[R] B, spMap ψ ≫ x m = y := by
  have haug : spMap (jetAug R (Fin d) m) ≫ x m = 1 := by
    have e : jetAug R (Fin d) m = (jetAug R (Fin d) 0).comp (jetZeroR R (Fin d) m) :=
      (jet_ext fun j => by rw [AlgHom.comp_apply, jetAug_zR]; exact (jetAug_zR (R := R) 0 j).symm)
    rw [e, ← spMap_comp, Category.assoc, hx₂ m, comp_one']
  have fac : ∀ {A₁ A₂ : Type} [CommRing A₁] [Algebra R A₁] [CommRing A₂] [Algebra R A₂] (p : B →ₐ[R] A₁)
      (q : A₁ →ₐ[R] A₂) {y y' : sp (R₀ := R) B ⟶ G}, spMap p ≫ y = spMap p ≫ y' →
      spMap (q.comp p) ≫ y = spMap (q.comp p) ≫ y' := fun p q y y' h => by
    rw [← spMap_comp, Category.assoc, Category.assoc, h]
  have key : ∀ k : ℕ, ∃ (b : Fin d → B) (hb : ∀ j, b j ∈ N),
      spMap (Ideal.Quotient.mkₐ R (N ^ (k + 1))) ≫ y =
        spMap (Ideal.Quotient.mkₐ R (N ^ (k + 1))) ≫ spMap (jetLift R _ hN b hb) ≫ x m := by
    intro k
    induction k with
    | zero =>
      refine ⟨fun _ => 0, fun _ => zero_mem _, ?_⟩
      have e : Ideal.Quotient.mkₐ R (N ^ (0 + 1)) =
          (Ideal.Quotient.factorₐ R (show N ≤ N ^ (0 + 1) by rw [zero_add, pow_one])).comp
            (Ideal.Quotient.mkₐ R N) := by
        ext a; rfl
      rw [e]
      refine fac _ _ ?_
      rw [hy, ← Category.assoc, spMap_comp, mk_comp_eq _ (fun j => by rw [jetLift_zR]; exact zero_mem _),
        ← spMap_comp, Category.assoc, haug, comp_one']
    | succ k ih =>
      obtain ⟨b, hb, ih⟩ := ih
      let B' := B ⧸ N ^ (k + 1 + 1)
      let π : B →ₐ[R] B' := Ideal.Quotient.mkₐ R (N ^ (k + 1 + 1))
      have hπ : Function.Surjective π := Ideal.Quotient.mk_surjective
      let J : Ideal B' := (N ^ (k + 1)).map π
      have hJN : J * N.map π = ⊥ := by
        rw [← Ideal.map_mul, ← pow_succ]
        exact Ideal.map_quotient_self _
      have hJle : J ≤ N.map π := Ideal.map_mono (Ideal.pow_le_self (by omega))
      have hJ : J ^ 2 = ⊥ := by
        rw [← le_bot_iff, pow_two, ← hJN]
        exact Ideal.mul_mono_right hJle
      let q : (B ⧸ N ^ (k + 1)) →ₐ[R] B' ⧸ J := Ideal.Quotient.liftₐ _
        ((Ideal.Quotient.mkₐ R J).comp π)
        (fun a ha => Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_map_of_mem _ ha))
      have hq : q.comp (Ideal.Quotient.mkₐ R (N ^ (k + 1))) = (Ideal.Quotient.mkₐ R J).comp π := by
        ext a; rfl
      have h2 := fac _ q ih
      rw [hq, ← spMap_comp, Category.assoc, Category.assoc] at h2
      haveI := hG
      obtain ⟨c, hc, -⟩ := SqZero.existsUnique_eq_lieExp_mul hv hJ h2.symm
      choose δ hδ hδc using fun j => (Ideal.mem_map_iff_of_surjective π hπ).1 (c j).2
      have hb' : ∀ j, b j + δ j ∈ N := fun j =>
        add_mem (hb j) (Ideal.pow_le_self (by omega) (hδ j))
      refine ⟨fun j => b j + δ j, hb', ?_⟩
      have h3 := move hG hv hx₁ hx₂ hx₃ hJN hJle
        (π.comp (jetLift R _ hN b hb)) (π.comp (jetLift R _ hN (fun j => b j + δ j) hb'))
        (fun j => by rw [AlgHom.comp_apply, jetLift_zR]; exact Ideal.mem_map_of_mem _ (hb j))
        (fun j => (c j : B')) (fun j => (c j).2) (fun j => SqZero.mul_eq_zero_of_sq hJ (c j).2 (c j).2)
        (fun j => by
          rw [AlgHom.comp_apply, AlgHom.comp_apply, jetLift_zR, jetLift_zR, map_add, hδc])
      change spMap π ≫ y = spMap π ≫ _
      rw [hc, ← Category.assoc, spMap_comp, ← Category.assoc, spMap_comp, h3]
  obtain ⟨b, hb, h⟩ := key m
  refine ⟨jetLift R _ hN b hb, ?_⟩
  let q : (B ⧸ N ^ (m + 1)) →ₐ[R] B := Ideal.Quotient.liftₐ _ (AlgHom.id R B)
    (fun a ha => by rw [hN] at ha; exact ha)
  have hq : q.comp (Ideal.Quotient.mkₐ R (N ^ (m + 1))) = AlgHom.id R B := by
    ext a; rfl
  have h2 := fac _ q h
  rw [hq, spMap_id, Category.id_comp, Category.id_comp] at h2
  exact h2.symm

theorem existsUnique_coord {m : ℕ} {N : Ideal B} (hN : N ^ (m + 1) = ⊥) (y : sp (R₀ := R) B ⟶ G)
    (hy : spMap (Ideal.Quotient.mkₐ R N) ≫ y = 1) : ∃! ψ : JetR R (Fin d) m →ₐ[R] B, spMap ψ ≫ x m = y := by
  obtain ⟨ψ, h⟩ := coord_exists hG hv hx₁ hx₂ hx₃ hN y hy
  exact ⟨ψ, h, fun ψ' h' => coord_unique hG hv hx₁ hx₂ hx₃ _ _ (h'.trans h.symm)⟩

end GlobalTheory.NilChart
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsCombAtIffIsDerivAt0
section
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Frames GlobalTheory.FrameUnif
open scoped Matrix nonZeroDivisors

namespace GlobalTheory.DerLin

theorem surj_fst (S : Type) [CommRing S] :
    Function.Surjective (spMap (TrivSqZeroExt.fstHom S S S).toRingHom : Sp S ⟶ Sp (DualNumber S)) := by
  intro p
  have hs : Function.Surjective (TrivSqZeroExt.fstHom S S S).toRingHom := fun a => ⟨TrivSqZeroExt.inl a, rfl⟩
  have hr := range_comap_of_surjective _ _ hs
  have hp : (show PrimeSpectrum (DualNumber S) from p) ∈
      PrimeSpectrum.zeroLocus (RingHom.ker (TrivSqZeroExt.fstHom S S S).toRingHom : Set (DualNumber S)) := by
    intro x hx
    have hx0 : x.fst = 0 := hx
    have : x * x = 0 := by
      ext <;> simp [hx0]
    have hP := (show PrimeSpectrum (DualNumber S) from p).isPrime
    have h0 : x * x ∈ (show PrimeSpectrum (DualNumber S) from p).asIdeal := by
      rw [this]; exact Ideal.zero_mem _
    exact (hP.mem_or_mem h0).elim id id
  rw [← hr] at hp
  obtain ⟨q, hq⟩ := hp
  exact ⟨q, hq⟩

theorem le_of_fst_eq {S : Type} [CommRing S] {X : Scheme.{0}} {v v' : Sp (DualNumber S) ⟶ X}
    (hh : spMap (TrivSqZeroExt.fstHom S S S).toRingHom ≫ v = spMap (TrivSqZeroExt.fstHom S S S).toRingHom ≫ v')
    {U : X.Opens} (h : ⊤ ≤ v' ⁻¹ᵁ U) : ⊤ ≤ v ⁻¹ᵁ U := by
  intro p _
  obtain ⟨q, rfl⟩ := surj_fst S p
  have h1 := h (Set.mem_univ ((spMap (TrivSqZeroExt.fstHom S S S).toRingHom : Sp S ⟶ Sp (DualNumber S)) q))
  change v' _ ∈ U at h1
  change v _ ∈ U
  rw [← Scheme.Hom.comp_apply] at h1 ⊢
  rw [hh]; exact h1

theorem isCombAt_iff_isDerivAt0 : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (σ' : KA l →+* ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (F : FamilyUnif Xo σ' ty) (k : Fin F.n) (P : (F.Di k).La →+ (Fin g → ℂ)), IsPeriod (F.Di k) ty P → ∀ (m : ℕ) (v : Fin m → (Sp (DualNumber ℂ) ⟶ Xo.univ.t.G.left)) (w : Fin m → (Fin g → ℂ)), (∀ i, IsDerivAt0 (fun z => (F.ex k P z).left) (w i) (v i)) → ∀ (a : Fin m → ℂ) (v' : (Sp (DualNumber ℂ) ⟶ Xo.univ.t.G.left)), IsCombAt (F.u k P) v a v' ↔ IsDerivAt0 (fun z => (F.ex k P z).left) (∑ i, a i • w i) v' := by
  intro E _ _ _ H Dw l Xo σ' g ty F k P hP m v w hvw a
  obtain ⟨h1, h2, -⟩ := GlobalTheory.T.exponential_derivative_at_zero_isTangent E H Dw l Xo σ' g ty F k P hP
  obtain ⟨N, _, _, ν, ρ, -, hr, hc, -⟩ := GlobalTheory.T.exists_tangent_module_universal_group E H Dw l Xo ℂ (F.u k P)
  have htan : ∀ i, IsTanAt (F.u k P) (v i) := fun i => h1 _ _ (hvw i)
  choose b hb using fun i => (hr (v i)).1 (htan i)
  have hv : v = fun i => ν (b i) := funext fun i => (hb i).symm
  have fwd : ∀ v', IsCombAt (F.u k P) v a v' →
      IsDerivAt0 (fun z => (F.ex k P z).left) (∑ i, a i • w i) v' := by
    intro v' hv'
    have ht' : IsTanAt (F.u k P) v' := by
      rw [hv, hc] at hv'
      exact (hr v').2 ⟨_, hv'.symm⟩
    obtain ⟨v0, hv0, -⟩ := h2 0
    refine ⟨ht'.2.trans ((h1 _ _ hv0).2.symm.trans hv0.1), fun U h f => ?_⟩
    have hU : ∀ i, ⊤ ≤ v i ⁻¹ᵁ U := fun i => le_of_fst_eq ((htan i).2.trans ht'.2.symm) h
    refine (GlobalTheory.T.derivative_along_tangent_combination_moduli E H Dw l Xo ℂ (F.u k P) m v a v' htan hv' U h hU f).trans ?_
    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul, smul_eq_mul]
    exact congrArg (a i * ·) ((hvw i).2 U (hU i) f)
  intro v'
  refine ⟨fwd v', fun hd => ?_⟩
  have hex : IsCombAt (F.u k P) v a (ν (∑ i, a i • b i)) := by
    rw [hv, hc]
  rw [(h2 _).unique hd (fwd _ hex)]
  exact hex

end GlobalTheory.DerLin
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LieBasisIffTangentBasisPullbackUniversal
section
noncomputable section

namespace GlobalTheory.Frames

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Frames

theorem spMap_epsScaleR_comp {S : Type} [CommRing S] (c : S) :
    spMap (epsScaleR c) ≫ spMap (algebraMap S (DualNumber S)) = spMap (algebraMap S (DualNumber S)) := by
  have e : (epsScaleR c).comp (algebraMap S (DualNumber S)) = algebraMap S (DualNumber S) := by
    ext s <;> simp [epsScaleR, TrivSqZeroExt.algebraMap_eq_inl]
  conv_rhs => rw [← e]
  simp only [spMap, CommRingCat.ofHom_comp, Spec.map_comp]

theorem lieBasis_iff_tanBasis : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (S : Type) [CommRing S] (x : Sp S ⟶ Xo.X) (G' : Over (Sp S)) [GrpObj G'] (φ : G'.left ⟶ Xo.univ.t.G.left), IsGrpPullback G' Xo.univ.t.G x φ → (∀ w : (Sp (DualNumber S) ⟶ Xo.univ.t.G.left), IsTanAt x w → ∃ v : epsR S ⟶ G', v.left ≫ φ = w) ∧ ∀ (n : ℕ) (v : Fin n → (epsR S ⟶ G')), IsLieBasis v ↔ TanBasis x (fun i => (v i).left ≫ φ) := by
  intro E _ _ _ H Dw l Xo S _ x G' _ φ hp
  let up : ∀ w : Sp (DualNumber S) ⟶ Xo.univ.t.G.left,
      w ≫ Xo.univ.t.G.hom = spMap (algebraMap S (DualNumber S)) ≫ x → (epsR S ⟶ G') :=
    fun w h => Over.homMk (hp.1.lift w _ h) (hp.1.lift_snd _ _ _)
  have hup : ∀ w h, (up w h).left ≫ φ = w := fun w h => hp.1.lift_fst _ _ _
  have inj : ∀ {T : Over (Sp S)} {u v : T ⟶ G'}, u.left ≫ φ = v.left ≫ φ → u = v := fun h =>
    Over.OverMorphism.ext (hp.1.hom_ext h ((Over.w _).trans (Over.w _).symm))
  have one : ∀ T : Over (Sp S), (1 : T ⟶ G').left ≫ φ = (1 : Over.mk (T.hom ≫ x) ⟶ Xo.univ.t.G).left :=
    fun T => congrArg (fun q => q.left) (map_one (pushHom hp T))
  have e : η[G'].left ≫ φ = (1 : Over.mk x ⟶ Xo.univ.t.G).left := by
    have e₁ : (1 : 𝟙_ (Over (Sp S)) ⟶ G') = η[G'] := by rw [Hom.one_def]; simp
    rw [← e₁, one]
    exact congrArg (· ≫ (η[Xo.univ.t.G]).left) (Category.id_comp x)
  have zs : spMap (TrivSqZeroExt.fstHom S S S).toRingHom ≫ spMap (algebraMap S (DualNumber S)) = 𝟙 _ := by
    have e : (TrivSqZeroExt.fstHom S S S).toRingHom.comp (algebraMap S (DualNumber S)) = RingHom.id S := by
      ext s; simp
    simp only [spMap]
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, e]
    simp
  have tan : ∀ w : epsR S ⟶ G', IsTangent w ↔ IsTanAt x (w.left ≫ φ) := fun w => by
    refine ⟨fun h => ⟨Over.w (pushPt hp.1.w w), ?_⟩, fun h => hp.1.hom_ext ?_ ?_⟩
    · exact (Category.assoc _ _ _).symm.trans ((congrArg (fun q => q ≫ φ) h).trans e)
    · exact (Category.assoc _ _ _).trans (h.2.trans e.symm)
    · refine (Category.assoc _ _ _).trans ?_
      rw [Over.w w, Over.w η[G']]
      exact zs
  have pr : ∀ {n} (u : Fin n → (epsR S ⟶ G')), (List.ofFn u).prod.left ≫ φ =
      (List.ofFn fun i => (pushPt hp.1.w (u i) : tEps x ⟶ Xo.univ.t.G)).prod.left := fun u =>
    congrArg (fun q => q.left) ((map_list_prod (pushHom hp (epsR S)) _).trans (by rw [List.map_ofFn]; rfl))
  have comb : ∀ {n} (c : Fin n → S) (v : Fin n → (epsR S ⟶ G')) w,
      IsLieComb c v w ↔ IsCombAt x (fun i => (v i).left ≫ φ) c (w.left ≫ φ) := fun c v w => by
    constructor
    · rintro ⟨u, hu, rfl⟩
      exact ⟨fun i => pushPt hp.1.w (u i), fun i => (congrArg (· ≫ φ) (hu i)).trans (Category.assoc _ _ _), (pr u).symm⟩
    · rintro ⟨u, hu, hw⟩
      refine ⟨fun i => up (u i).left (Over.w _), fun i => hp.1.hom_ext ?_ ?_,
        inj (hw.symm.trans (Eq.trans ?_ (pr _).symm))⟩
      · exact (hup _ _).trans ((hu i).trans (Category.assoc _ _ _).symm)
      · refine (Over.w (up (u i).left (Over.w _))).trans (Eq.trans ?_ (Category.assoc _ _ _).symm)
        refine Eq.trans ?_ (congrArg (spMap (epsScaleR (c i)) ≫ ·) (Over.w (v i))).symm
        exact (spMap_epsScaleR_comp (c i)).symm
      · have : u = fun i => (pushPt hp.1.w (up (u i).left (Over.w _)) : tEps x ⟶ Xo.univ.t.G) :=
          funext fun i => Over.OverMorphism.ext (hup (u i).left (Over.w _)).symm
        exact congrArg (fun q : _ → (tEps x ⟶ Xo.univ.t.G) => (List.ofFn q).prod.left) this
  refine ⟨fun w hw => ⟨up w hw.1, hup _ _⟩, fun n v => ⟨fun hB => ⟨fun i => (tan _).1 (hB.1 i), fun w hw => ?_⟩,
    fun hB => ⟨fun i => (tan _).2 (hB.1 i), fun w hw => ?_⟩⟩⟩
  · have h := hB.2 (up w hw.1) ((tan _).2 (by rw [hup]; exact hw))
    simp only [comb, hup] at h
    exact h
  · have h := hB.2 _ ((tan _).1 hw)
    simp only [comb]
    exact h

end GlobalTheory.Frames
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LineBundleTrivialBasicOpenOfTrivialFibreProductStatement
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap)
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
theorem _root_.GlobalTheory.T.lineBundle_trivial_basicOpen_of_trivial_fibre_product : ∀ (R : Type) [CommRing R] (X Y : Over (Sp R)) (x₀ : 𝟙_ (Over (Sp R)) ⟶ X) (y₀ : 𝟙_ (Over (Sp R)) ⟶ Y), Flat X.hom → Flat Y.hom → IsProper X.hom → IsProper Y.hom → (∀ (R' : Type) [CommRing R'] (g : R →+* R') (X' : Scheme.{0}) (π : X' ⟶ (X).left) (f' : X' ⟶ Spec (CommRingCat.of R')), IsPullback π f' (X).hom (Spec.map (CommRingCat.ofHom g)) → Function.Bijective f'.appTop.hom) → (∀ (R' : Type) [CommRing R'] (g : R →+* R') (X' : Scheme.{0}) (π : X' ⟶ (Y).left) (f' : X' ⟶ Spec (CommRingCat.of R')), IsPullback π f' (Y).hom (Spec.map (CommRingCat.ofHom g)) → Function.Bijective f'.appTop.hom) → (∀ (R' : Type) [CommRing R'] (g : R →+* R') (X' : Scheme.{0}) (π : X' ⟶ (X ⊗ Y).left) (f' : X' ⟶ Spec (CommRingCat.of R')), IsPullback π f' (X ⊗ Y).hom (Spec.map (CommRingCat.ofHom g)) → Function.Bijective f'.appTop.hom) → ∀ M : LB (X ⊗ Y).left, M.IsLB → Nonempty (Perf (X ⊗ Y).hom M) → Triv (M.pull (lift (𝟙 X) (toUnit X ≫ y₀)).left) → Triv (M.pull (lift (toUnit Y ≫ x₀) (𝟙 Y)).left) → ∀ (K : Type) [Field K] (g₀ : R →+* K) (X₀ : Scheme.{0}) (π₀ : X₀ ⟶ (X ⊗ Y).left) (f₀ : X₀ ⟶ Spec (CommRingCat.of K)), IsPullback π₀ f₀ (X ⊗ Y).hom (Spec.map (CommRingCat.ofHom g₀)) → Triv (M.pull π₀) → ∃ r : R, g₀ r ≠ 0 ∧ Triv (M.pull ((X ⊗ Y).hom ⁻¹ᵁ (PrimeSpectrum.basicOpen r)).ι) := by
  first | exact @GlobalTheory.Exist.ProdOpen.triv_basicOpen_of_triv_fibre_prod | exact GlobalTheory.Exist.ProdOpen.triv_basicOpen_of_triv_fibre_prod | (intros; apply GlobalTheory.Exist.ProdOpen.triv_basicOpen_of_triv_fibre_prod <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.SkewMatrixMultipleInLatticeStatement
section
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Frames GlobalTheory.FrameUnif
open scoped Matrix nonZeroDivisors
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.skew_matrix_multiple_in_lattice : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r ρ : ℕ) (X : Data E r) (cu : FJ.CuspFD X ρ) (β : Matrix (Fin ρ) (Fin ρ) E), FJ.IsSkew β → ∃ n : ℕ, 0 < n ∧ n • β ∈ FJ.zGam X cu := by
  first | exact @GlobalTheory.CuspCentre.exists_nsmul_mem_zGam | exact GlobalTheory.CuspCentre.exists_nsmul_mem_zGam | (intros; apply GlobalTheory.CuspCentre.exists_nsmul_mem_zGam <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.SpanCuspCentreArithmeticGroupFgStatement
section
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Frames GlobalTheory.FrameUnif
open scoped Matrix nonZeroDivisors
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.span_cuspCentre_arithmeticGroup_fg : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r ρ : ℕ) (X : Data E r) (cu : FJ.CuspFD X ρ), (Submodule.span ℤ (FJ.zGam X cu)).FG := by
  first | exact @GlobalTheory.CuspCentre.span_zGam_fg | exact GlobalTheory.CuspCentre.span_zGam_fg | (intros; apply GlobalTheory.CuspCentre.span_zGam_fg <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.TransvectionMemPrincipalCongruenceGroupStatement
section
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Frames GlobalTheory.FrameUnif
open scoped Matrix nonZeroDivisors
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.transvection_mem_principalCongruenceGroup : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (l : Level H) (Di : Datum H) (r : ℕ) (ξ₀ : E) (Gm : Matrix (Fin r) (Fin r) E) (φ0 : Di.La →ₗ[𝓞 E] (Fin r → E)), cc ξ₀ = -ξ₀ → (Function.Injective φ0 ∧ Submodule.span E (Set.range φ0) = ⊤ ∧ (∀ a b, cc (Gm a b) = Gm b a) ∧ Gm.det ≠ 0 ∧ ∀ x y, ((Di.EF x y : ℤ) : ℚ) = Algebra.trace ℚ E (-ξ₀ * herm Gm (φ0 x) (φ0 y))) → ∃ m : ℕ, 0 < m ∧ ∀ κ0 : E, (κ0 = 2 * ξ₀ ∨ κ0 = -(2 * ξ₀)) → ∀ ξ ∈ LinearMap.range φ0, herm Gm ξ ξ = 0 → ∀ s : E, cc s = s → IsIntegral ℤ s → ∃ γ ∈ princ l Gm Di φ0, (γ : Matrix (Fin r) (Fin r) E) = transvMat Gm ξ ((m : E) * s * κ0) := by
  first | exact @GlobalTheory.PrincTransv.transv_mem_princ | exact GlobalTheory.PrincTransv.transv_mem_princ | (intros; apply GlobalTheory.PrincTransv.transv_mem_princ <;> assumption)
end

