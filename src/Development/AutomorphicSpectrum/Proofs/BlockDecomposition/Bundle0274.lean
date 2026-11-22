import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ConeSectionRestriction.Bundle0006
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.GlobalSerreRelations.GlobSerreSt
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RepUnique
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.StCocycle
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConeCocycleClassIndependent
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.PlaneSupports.PlaneSupp
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousSingleV
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LubinTateSeriesCommuteLinear
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0255
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0262
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0264
import GroundTheory.ArithmeticGeometry.SchemeCohomology.ProperCohomology.FormalFunctions
import GroundTheory.ArithmeticGeometry.SchemeCohomology.ProperCohomology.RelSerreSections

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalFrameTaylorClassEq
section
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.Pb GlobalTheory.CompanionTheory.ConeLocal
open GlobalTheory.CatH (face toLast)

noncomputable section
namespace GlobalTheory.CompanionTheory.ConeLocal.DlogApprox

theorem alg_core {B : Type} [CommRing B] (J F : Ideal B) (hJF : ∀ a ∈ J, ∀ b ∈ J, a * b ∈ F)
    {H H0 D Y0 I0 W : B} (hH : H ∈ J) (hH0 : H0 ∈ J) (hD : D ∈ J) (hI : Y0 * I0 = 1)
    (hW : W * ((1 + H0) * Y0) = 1) :
    (1 + H) * (Y0 + D) * W - 1 - (D * I0 + H - H0) ∈ F := by
  set C := W * Y0 with hCdef
  have hC : C * (1 + H0) = 1 := by rw [hCdef]; linear_combination hW
  have hWC : W = C * I0 := by rw [hCdef]; linear_combination (-W) * hI
  set A := H + D * I0 + H * (D * I0) with hA
  have hAJ : A ∈ J := J.add_mem (J.add_mem hH (J.mul_mem_right _ hD)) (J.mul_mem_left _ (J.mul_mem_right _ hD))
  have e : (1 + H) * (Y0 + D) * W - 1 - (D * I0 + H - H0) =
      (C * H0) * H0 - (A * C) * H0 + H * (D * I0) := by
    rw [hWC, hA]
    linear_combination (1 + H) * C * hI + (1 - H0 + (H + D * I0 + H * (D * I0))) * hC
  rw [e]
  exact F.add_mem (F.sub_mem (hJF _ (J.mul_mem_left _ hH0) _ hH0) (hJF _ (J.mul_mem_right _ hAJ) _ hH0))
    (hJF _ hH _ (J.mul_mem_right _ hD))

theorem plogK_sub_mem {B : Type} [CommRing B] {J : Ideal B} (δ : DividedPowers J) (F : Ideal B) {s : ℕ} (hs : 1 ≤ s)
    {x : B} (hx : x ∈ J) (h : ∀ k, 2 ≤ k → δ.dpow k x ∈ F) : plogK δ s x - x ∈ F := by
  obtain ⟨n, rfl⟩ : ∃ n, s = n + 1 := ⟨s - 1, by omega⟩
  unfold plogK
  rw [Finset.sum_range_succ']
  have e : (-1 : B) ^ 0 * ((Nat.factorial 0 : ℕ) : B) * δ.dpow (0 + 1) x = x := by
    simp [δ.dpow_one hx]
  rw [e, add_sub_cancel_right]
  exact F.sum_mem fun k _ => F.mul_mem_left _ (h _ (by omega))

section Fr
variable {R : Type} [CommRing R] {C : Type 1} [Category.{0} C] {Φ : PDF R C}

theorem form_one {d : ℕ} (E : Frame Φ d) (σ : ∀ T : C, E.D ⟶ T) (i : Fin d) (x : Φ.A.obj E.D)
    (u : ComposableArrows C 1) :
    E.form σ ![i] x u = E.a σ i (u.map (homOfLE (Fin.zero_le (Fin.last 1)))) * (Φ.A.map (σ _)).hom x := by
  unfold Frame.form
  rw [Fin.prod_univ_one]
  congr 1
  have e : ∀ (h : (Fin.succ (0 : Fin 1)) ⟶ Fin.last 1) (z : Φ.A.obj (u.obj (Fin.last 1))),
      (Φ.A.map (u.map h)).hom z = z := by
    intro h z
    have : h = 𝟙 (Fin.last 1) := Subsingleton.elim _ _
    have e2 : u.map h = 𝟙 (u.obj (Fin.last 1)) := (congrArg u.map this).trans (u.map_id _)
    have e3 : Φ.A.map (u.map h) = 𝟙 (Φ.A.obj (u.obj (Fin.last 1))) := (congrArg Φ.A.map e2).trans (Φ.A.map_id _)
    rw [e3]
    rfl
  exact e _ _

theorem mul2 {Fil : ℤ → IdF Φ.A} (hF : IsFil Φ Fil) (T : C) : ∀ a ∈ Φ.J.S T, ∀ b ∈ Φ.J.S T, a * b ∈ (Fil 2).S T := by
  intro a ha b hb
  have h1 : ∀ z ∈ Φ.J.S T, z ∈ (Fil ((1 : ℕ) : ℤ)).S T := fun z hz => by
    rw [Nat.cast_one, hF.one]; exact hz
  exact hF.mul 1 1 T (h1 a ha) (h1 b hb)

theorem const1 {Fil : ℤ → IdF Φ.A} (hF : IsFil Φ Fil) {d : ℕ} {E : Frame Φ d} (hc : E.GrConst Fil) {T : C}
    (a b : E.D ⟶ T) (x : Φ.A.obj E.D) : (Φ.A.map a).hom x - (Φ.A.map b).hom x ∈ Φ.J.S T := by
  have h := hc 0 a b (x := x) (by rw [Nat.cast_zero, hF.top 0 le_rfl E.D]; trivial)
  rw [Nat.cast_zero, zero_add, hF.one] at h
  exact h

theorem frame_core {Fil : ℤ → IdF Φ.A} (hF : IsFil Φ Fil) {d : ℕ} (E : Frame Φ d) (hc : E.GrConst Fil)
    (p : Fin d → Φ.A.obj E.D → Φ.A.obj E.D) (ht : Taylor Fil E p) (σ : ∀ T : C, E.D ⟶ T)
    (G : Φ.A.obj E.D) (hG : IsUnit G) {T T' : C} (φ : T ⟶ T') {H H0 W : Φ.A.obj T'}
    (hH : H ∈ Φ.J.S T') (hH0 : H0 ∈ Φ.J.S T')
    (hW : W * ((1 + H0) * (Φ.A.map (σ T ≫ φ)).hom G) = 1) :
    (1 + H) * (Φ.A.map (σ T')).hom G * W - 1 -
      (∑ i, E.a σ i φ * (Φ.A.map (σ T')).hom (Ring.inverse G * p i G) + (H - H0)) ∈ (Fil 2).S T' := by
  set v := (Φ.A.map (σ T ≫ φ)).hom with hv
  set w := (Φ.A.map (σ T')).hom with hw
  have hI : v G * v (Ring.inverse G) = 1 := by
    rw [← map_mul, Ring.mul_inverse_cancel _ hG, map_one]
  have hD : w G - v G ∈ Φ.J.S T' := const1 hF hc _ _ G
  have h1 := alg_core (Φ.J.S T') ((Fil 2).S T') (mul2 hF T') hH hH0 hD hI hW
  have h2 := ((Fil 2).S T').mul_mem_left (v (Ring.inverse G)) (ht T' (σ T') (σ T ≫ φ) G)
  have h3 : ∑ i, E.a σ i φ * (v (Ring.inverse G * p i G) - w (Ring.inverse G * p i G)) ∈ (Fil 2).S T' :=
    ((Fil 2).S T').sum_mem fun i _ => mul2 hF T' _ (E.mem i _ _) _ (const1 hF hc _ _ _)
  have h4 : ∑ i, E.a σ i φ * (v (Ring.inverse G * p i G) - w (Ring.inverse G * p i G)) =
      v (Ring.inverse G) * ∑ i, E.a σ i φ * v (p i G) - ∑ i, E.a σ i φ * w (Ring.inverse G * p i G) := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_mul v]
    ring
  have h5 : (∑ k, E.τ k (σ T ≫ φ) (σ T') * v (p k G)) = ∑ i, E.a σ i φ * v (p i G) := rfl
  rw [h4] at h3
  change v (Ring.inverse G) * (w G - v G - ∑ k, E.τ k (σ T ≫ φ) (σ T') * v (p k G)) ∈ _ at h2
  rw [h5] at h2
  have e : (1 + H) * w G * W - 1 - (∑ i, E.a σ i φ * w (Ring.inverse G * p i G) + (H - H0)) =
      ((1 + H) * (v G + (w G - v G)) * W - 1 - ((w G - v G) * v (Ring.inverse G) + H - H0)) +
      v (Ring.inverse G) * (w G - v G - ∑ i, E.a σ i φ * v (p i G)) +
      (v (Ring.inverse G) * (∑ i, E.a σ i φ * v (p i G)) - ∑ i, E.a σ i φ * w (Ring.inverse G * p i G)) := by
    ring
  rw [e]
  exact ((Fil 2).S T').add_mem (((Fil 2).S T').add_mem h1 h2) h3

end Fr

section Fr2
variable {R : Type} [CommRing R] {C : Type 1} [Category.{0} C] {Φ : PDF R C}

theorem frame_main {Fil : ℤ → IdF Φ.A} (hF : IsFil Φ Fil) {d : ℕ} (E : Frame Φ d) (hc : E.GrConst Fil)
    (p : Fin d → Φ.A.obj E.D → Φ.A.obj E.D) (ht : Taylor Fil E p) (σ : ∀ T : C, E.D ⟶ T)
    (G : Φ.A.obj E.D) (hG : IsUnit G) (gh : ∀ T, Φ.A.obj T)
    (hg : ∀ T, gh T - (Φ.A.map (σ T)).hom G ∈ Φ.J.S T)
    (hun : ∀ T, ∀ x ∈ Φ.J.S T, IsUnit (1 + x)) :
    (∀ T, gh T * Ring.inverse ((Φ.A.map (σ T)).hom G) - 1 ∈ Φ.J.S T) ∧
    ∀ {T T' : C} (φ : T ⟶ T'),
      (gh T' * Ring.inverse ((Φ.A.map φ).hom (gh T)) - 1 ∈ Φ.J.S T') ∧
      gh T' * Ring.inverse ((Φ.A.map φ).hom (gh T)) - 1 -
        (∑ i, E.a σ i φ * (Φ.A.map (σ T')).hom (Ring.inverse G * p i G) +
          ((gh T' * Ring.inverse ((Φ.A.map (σ T')).hom G) - 1) -
            (Φ.A.map φ).hom (gh T * Ring.inverse ((Φ.A.map (σ T)).hom G) - 1))) ∈ (Fil 2).S T' := by
  have hy : ∀ T, IsUnit ((Φ.A.map (σ T)).hom G) := fun T => hG.map (Φ.A.map (σ T)).hom
  have hyi : ∀ T, (Φ.A.map (σ T)).hom G * Ring.inverse ((Φ.A.map (σ T)).hom G) = 1 :=
    fun T => Ring.mul_inverse_cancel _ (hy T)
  have hh : ∀ T, gh T * Ring.inverse ((Φ.A.map (σ T)).hom G) - 1 ∈ Φ.J.S T := by
    intro T
    have e : gh T * Ring.inverse ((Φ.A.map (σ T)).hom G) - 1 =
        (gh T - (Φ.A.map (σ T)).hom G) * Ring.inverse ((Φ.A.map (σ T)).hom G) := by
      linear_combination hyi T
    rw [e]
    exact (Φ.J.S T).mul_mem_right _ (hg T)
  refine ⟨hh, ?_⟩
  intro T T' φ
  set H := gh T' * Ring.inverse ((Φ.A.map (σ T')).hom G) - 1 with hHd
  set h0 := gh T * Ring.inverse ((Φ.A.map (σ T)).hom G) - 1 with hh0
  set H0 := (Φ.A.map φ).hom h0 with hH0d
  have hHm : H ∈ Φ.J.S T' := hh T'
  have hH0m : H0 ∈ Φ.J.S T' := Φ.J.map_mem φ (hh T)
  have e1 : gh T = (1 + h0) * (Φ.A.map (σ T)).hom G := by
    rw [hh0]; linear_combination (-gh T) * hyi T
  have e2 : gh T' = (1 + H) * (Φ.A.map (σ T')).hom G := by
    rw [hHd]; linear_combination (-gh T') * hyi T'
  have hU : IsUnit (gh T) := by
    rw [e1]; exact (hun T _ (hh T)).mul (hy T)
  have e3 : (Φ.A.map φ).hom (gh T) = (1 + H0) * (Φ.A.map (σ T ≫ φ)).hom G := by
    rw [e1, map_mul, map_add, map_one, Φ.A.map_comp]
    rfl
  have hW : Ring.inverse ((Φ.A.map φ).hom (gh T)) * ((1 + H0) * (Φ.A.map (σ T ≫ φ)).hom G) = 1 := by
    rw [← e3]
    exact Ring.inverse_mul_cancel _ (hU.map (Φ.A.map φ).hom)
  have key := frame_core hF E hc p ht σ G hG φ hHm hH0m hW
  rw [← e2] at key
  refine ⟨?_, key⟩
  have hle : (Fil 2).S T' ≤ Φ.J.S T' := by
    rw [← hF.one]; exact hF.anti (by norm_num) T'
  have hs : ∑ i, E.a σ i φ * (Φ.A.map (σ T')).hom (Ring.inverse G * p i G) + (H - H0) ∈ Φ.J.S T' :=
    (Φ.J.S T').add_mem ((Φ.J.S T').sum_mem fun i _ => (Φ.J.S T').mul_mem_right
      ((Φ.A.map (σ T')).hom (Ring.inverse G * p i G)) (E.mem i (σ T ≫ φ) (σ T'))) ((Φ.J.S T').sub_mem hHm hH0m)
  have h6 := (Φ.J.S T').add_mem (hle key) hs
  rw [sub_add_cancel] at h6
  exact h6

end Fr2

theorem main : ∀ {K : Type} [Field K] [CharZero K] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K)) (s : ℕ), 2 ≤ s → ∀ {V V' : X.Opens} (hVV : V ≤ V') {d : ℕ} (t : Fin d → Γ(X, V)) (E : Frame (sP (KS q s {V})) d)
    (ε : Γ(X, V) ≃+* (sP (KS q s {V})).A.obj E.D), IsLoc q s t E ε →
    ∀ (p : Fin d → (sP (KS q s {V})).A.obj E.D → (sP (KS q s {V})).A.obj E.D), Taylor (sFil (KS q s {V})) E p →
    ∀ (σ : ∀ T, E.D ⟶ T) (g : Γ(X, V')), IsUnit g → ∀ (ĝ : ∀ T : (KS q s {V'}).FullSubcategory, T.obj.B),
      (∀ T, Ideal.Quotient.mk T.obj.J (ĝ T) = ev T.obj (ks_in q s V' _ T.property) g) →
      ∃ h : ∀ T, (sP (KS q s {V})).A.obj T, (∀ T, h T ∈ (sP (KS q s {V})).J.S T) ∧ ∀ u : ComposableArrows (KS q s {V}).FullSubcategory 1,
        (show (sP (KS q s {V})).A.obj (u.obj (Fin.last 1)) from resQ (ks_le q s hVV) (dlogC (KS q s {V'}) s ĝ) u) -
          (∑ i, E.form σ ![i] (Ring.inverse (ε (rs hVV g)) * p i (ε (rs hVV g))) u +
            (h (u.obj (Fin.last 1)) - ((sP (KS q s {V})).A.map (u.map (homOfLE (Fin.zero_le (Fin.last 1))))).hom (h (u.obj 0)))) ∈
          (sFil (KS q s {V}) 2).S _ := by
  intro K _ _ X q s hs V V' hVV d t E ε hL p ht σ g hg ĝ hĝ
  have hF := GlobalTheory.CompanionTheory.DPFil.isFil_sFil (KS q s {V})
  obtain ⟨hc, -, -, h4, -⟩ := hL
  have hG : IsUnit (ε (rs hVV g)) := (hg.map (rs hVV)).map ε
  let gh : ∀ T : (KS q s {V}).FullSubcategory, (sP (KS q s {V})).A.obj T :=
    fun T => ĝ ((ObjectProperty.ιOfLE (ks_le q s hVV)).obj T)
  have hgl : ∀ T, gh T - ((sP (KS q s {V})).A.map (σ T)).hom (ε (rs hVV g)) ∈ (sP (KS q s {V})).J.S T := by
    intro T
    have a1 := hĝ ((ObjectProperty.ιOfLE (ks_le q s hVV)).obj T)
    have a2 := h4 T (σ T) (rs hVV g)
    have a3 := GlobalTheory.CompanionTheory.GrForm.ev_res hVV T.obj (ks_in q s V' _ ((ObjectProperty.ιOfLE (ks_le q s hVV)).obj T).property)
      (ks_in q s V _ T.property) g
    exact Ideal.Quotient.eq.1 (a1.trans (a3.symm.trans a2))
  have hun : ∀ T, ∀ x ∈ (sP (KS q s {V})).J.S T, IsUnit (1 + x) := by
    intro T x hx
    have hn : IsNilpotent (show T.obj.B from x) := by
      obtain ⟨n, hn⟩ := GlobalTheory.CompanionTheory.ConeZcls.J_nil T.obj
      refine ⟨n, ?_⟩
      have h1 : (show T.obj.B from x) ^ n ∈ T.obj.J ^ n := Ideal.pow_mem_pow hx n
      rw [hn] at h1
      simpa using h1
    exact hn.isUnit_one_add
  obtain ⟨m1, m2⟩ := frame_main hF E hc p ht σ (ε (rs hVV g)) hG gh hgl hun
  refine ⟨fun T => gh T * Ring.inverse (((sP (KS q s {V})).A.map (σ T)).hom (ε (rs hVV g))) - 1, m1, fun u => ?_⟩
  obtain ⟨b1, b2⟩ := m2 (u.map (homOfLE (Fin.zero_le (Fin.last 1))))
  have b3 := plogK_sub_mem (u.obj (Fin.last 1)).obj.δ
    (show Ideal (u.obj (Fin.last 1)).obj.B from (sFil (KS q s {V}) 2).S (u.obj (Fin.last 1)))
    (s := s) (by omega) b1 (fun k hk => hF.anti (by exact_mod_cast hk) _ (hF.dp_mem k _ b1))
  have b4 := ((sFil (KS q s {V}) 2).S (u.obj (Fin.last 1))).add_mem b3 b2
  rw [sub_add_sub_cancel] at b4
  simp only [form_one]
  exact b4

end GlobalTheory.CompanionTheory.ConeLocal.DlogApprox
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalLiftSpecialSupport
section
noncomputable section

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes IsDedekindDomain NumberField GlobalTheory.Published Sa2 GlobalTheory.CompanionTheory.SaGen
open scoped TensorProduct Topology

namespace GlobalTheory.CompanionTheory.SaGen.LiftSupp

section Ring

variable {R : Type} [CommRing R] {n : Type} [Fintype n] [DecidableEq n]

theorem mul_det_eq_of_mul_entries (d : R) {A B : Matrix n n R} (h : ∀ i j, d * A i j = d * B i j) :
    d * A.det = d * B.det := by
  let I : Ideal R := LinearMap.ker (LinearMap.mulLeft R d)
  have hI : ∀ x y : R, d * x = d * y → Ideal.Quotient.mk I x = Ideal.Quotient.mk I y := by
    intro x y hxy
    refine Ideal.Quotient.eq.2 ?_
    change d * (x - y) = 0
    rw [mul_sub, hxy, sub_self]
  have hmap : (Ideal.Quotient.mk I).mapMatrix A = (Ideal.Quotient.mk I).mapMatrix B := by
    ext i j
    exact hI _ _ (h i j)
  have h2 : Ideal.Quotient.mk I A.det = Ideal.Quotient.mk I B.det := by
    rw [RingHom.map_det, RingHom.map_det, hmap]
  have h3 : A.det - B.det ∈ I := Ideal.Quotient.eq.1 h2
  have h4 : d * (A.det - B.det) = 0 := h3
  rw [mul_sub] at h4
  exact sub_eq_zero.1 h4

end Ring

section Tensor

variable {F E K : Type} [Field F] [NumberField F] [Field E] [Algebra F E] [Field K] [Algebra F K]
  [TopologicalSpace K]

def pB (P : PlaceMap F K) : AF F ⊗[F] E →ₐ[F] K ⊗[F] E :=
  Algebra.TensorProduct.map P.proj (AlgHom.id F E)

theorem iB_tmul (P : PlaceMap F K) (a : K) (b : E) : iB P (a ⊗ₜ[F] b) = P.inj a ⊗ₜ[F] b := rfl

theorem pB_tmul (P : PlaceMap F K) (a : AF F) (b : E) : pB P (a ⊗ₜ[F] b) = P.proj a ⊗ₜ[F] b := rfl

theorem algebraMap_inj_one (P : PlaceMap F K) :
    algebraMap (AF F) (AF F ⊗[F] E) (P.inj 1) = iB P (1 : K ⊗[F] E) := by
  rw [Algebra.TensorProduct.one_def, iB_tmul, Algebra.TensorProduct.algebraMap_apply]
  rfl

theorem eB_mul_iB (P : PlaceMap F K) (y : K ⊗[F] E) :
    algebraMap (AF F) (AF F ⊗[F] E) (P.inj 1) * iB P y = iB P y := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul a b =>
    rw [iB_tmul, Algebra.TensorProduct.algebraMap_apply, Algebra.TensorProduct.tmul_mul_tmul, one_mul]
    change (P.inj 1 * P.inj a) ⊗ₜ[F] b = _
    rw [← map_mul, one_mul]
  | add x y hx hy => rw [map_add, mul_add, hx, hy]

theorem pB_iB (P : PlaceMap F K) (y : K ⊗[F] E) : pB P (iB P y) = y := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul a b => rw [iB_tmul, pB_tmul, P.proj_inj]
  | add x y hx hy => rw [map_add, map_add, hx, hy]

theorem iB_pB (P : PlaceMap F K) (y : AF F ⊗[F] E) :
    iB P (pB P y) = algebraMap (AF F) (AF F ⊗[F] E) (P.inj 1) * y := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul a b =>
    rw [pB_tmul, iB_tmul, P.inj_proj, Algebra.TensorProduct.algebraMap_apply,
      Algebra.TensorProduct.tmul_mul_tmul, one_mul]
    rfl
  | add x y hx hy => rw [map_add, map_add, hx, hy, mul_add]

theorem det_eq_one_of_lift (P : PlaceMap F K) {M : ℕ} {G : Matrix (Fin M) (Fin M) (AF F ⊗[F] E)}
    {X : Matrix (Fin M) (Fin M) (K ⊗[F] E)} (hG : ∀ i j, (G - 1) i j = iB P ((X - 1) i j)) (hX : X.det = 1) :
    G.det = 1 := by
  set e := algebraMap (AF F) (AF F ⊗[F] E) (P.inj 1) with he
  have hGij : ∀ i j, G i j = iB P ((X - 1) i j) + (1 : Matrix (Fin M) (Fin M) (AF F ⊗[F] E)) i j := by
    intro i j
    rw [← hG]
    simp
  have hmap : (pB (E := E) P).toRingHom.mapMatrix G = X := by
    ext i j
    rw [RingHom.mapMatrix_apply, Matrix.map_apply, hGij]
    change pB P _ = _
    rw [map_add, pB_iB]
    by_cases h : i = j
    · subst h
      simp
    · simp [Matrix.one_apply_ne h]
  have hp : pB P G.det = 1 := by
    have h := RingHom.map_det (pB (E := E) P).toRingHom G
    rw [hmap, hX] at h
    exact h
  have h1 : e * G.det = e := by
    rw [he, ← iB_pB, hp, algebraMap_inj_one]
  have h2 : (1 - e) * G.det = (1 - e) * (1 : Matrix (Fin M) (Fin M) (AF F ⊗[F] E)).det := by
    refine mul_det_eq_of_mul_entries (1 - e) fun i j => ?_
    rw [hGij, mul_add, sub_mul, one_mul, he, eB_mul_iB, sub_self, zero_add]
  rw [Matrix.det_one] at h2
  linear_combination h1 + h2

end Tensor

theorem lift_det_one_mem_supp : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ {M : ℕ} (J : Matrix (Fin M) (Fin M) E), ∀ {K : Type}
    [NontriviallyNormedField K] [Algebra F K] (P : PlaceMap F K) (L : HA K σ J →* HA (AF F) σ J), IsLift P σ J L →
    ∀ x : HA K σ J, ((HA.mat K σ J x).1 : Matrix (Fin M) (Fin M) (K ⊗[F] E)).det = 1 → L x ∈ SUSupp σ J (P.inj 1) := by
  intro F E _ _ _ _ _ σ _ M J K _ _ P L hL x hx
  refine ⟨StrongApprox.mem_SUAdelic.2 (det_eq_one_of_lift P (hL x) hx), fun i j => ?_⟩
  rw [hL x i j]
  exact eB_mul_iB P _

end GlobalTheory.CompanionTheory.SaGen.LiftSupp
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LubinTateSeriesCommuteLinearStatement
section
noncomputable section
open NumberField IsDedekindDomain Neutral.B1 Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations
open GlobalTheory.HeckeGal GlobalTheory.Pst GlobalTheory.TripleGal GlobalTheory.CompanionTheory.LTHodge GlobalTheory.CompanionTheory.LTPer
open scoped Classical

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lubin_tate_series_commute_linear : ∀ {B : Type} [CommRing B] {S : Subring B} {F : ℕ → Ideal B} {ϖ : B} {R : Type} [CommRing R], PerEnv S F ϖ → ∀ (ϖ' : B), ϖ * ϖ' = 1 →
    ∀ (h : R →+* B), (∀ c, h c ∈ S) → ∀ (π : R), h π = ϖ → ∀ (q : ℕ), 2 ≤ q → (∃ s ∈ S, (q : B) = ϖ * s) →
    ∀ (φ : PowerSeries R), PowerSeries.constantCoeff φ = 0 →
      PowerSeries.subst φ (PowerSeries.C π * PowerSeries.X + PowerSeries.X ^ q : PowerSeries R) = PowerSeries.subst (PowerSeries.C π * PowerSeries.X + PowerSeries.X ^ q : PowerSeries R) φ →
    ∀ (σ : B →+* B), (∀ s ∈ S, σ s ∈ S) → (∀ k, ∀ x ∈ F k, σ x ∈ F k) → σ ϖ = ϖ →
    ∀ Q ∈ S, (∃ M : ℕ, 0 < M ∧ Near S ϖ (F 1) 1 (Q ^ M)) →
      (∀ m, EvalMod S F ϖ h φ Q (σ Q) m) →
    ∀ t, Tends S F ϖ (fun n => ϖ' ^ n * ltIter ϖ q n Q) t → σ t = h (PowerSeries.coeff 1 φ) * t := by
  first | exact @GlobalTheory.CompanionTheory.LTPer.galois_log | exact GlobalTheory.CompanionTheory.LTPer.galois_log | (intros; apply GlobalTheory.CompanionTheory.LTPer.galois_log <;> assumption)
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NonemptyOpenIdealNotNilpotent
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh GlobalTheory.CompanionTheory.GE TensorProduct

set_option autoImplicit false

namespace GlobalTheory.CompanionTheory.GE.NonIso

theorem exists_ideal_not_pow_le {X : Scheme.{0}} (J : X.IdealSheafData) (W : J.subscheme.Opens)
    (hW : (W : Set J.subscheme).Nonempty) :
    ∃ J₀ : X.IdealSheafData, (∀ (V : X.affineOpens) (f : Γ(X, V)), f ∈ J₀.ideal V →
      J.subschemeι ⁻¹ᵁ X.basicOpen f ≤ W) ∧ ∀ m, ¬ powIdeal J₀ m ≤ J := by
  have hC : IsClosed (J.subschemeι '' (W : Set J.subscheme)ᶜ) :=
    J.subschemeι.isClosedEmbedding.isClosedMap _ W.isOpen.isClosed_compl
  let C : TopologicalSpace.Closeds X := ⟨_, hC⟩
  have hsupp : ∀ x : X, x ∈ (Scheme.IdealSheafData.vanishingIdeal C).support ↔
      x ∈ J.subschemeι '' (W : Set J.subscheme)ᶜ := by
    intro x
    rw [← SetLike.mem_coe, Scheme.IdealSheafData.coe_support_vanishingIdeal]
    rfl
  refine ⟨Scheme.IdealSheafData.vanishingIdeal C, ?_, ?_⟩
  · intro V f hf y hy
    have hyV : J.subschemeι y ∈ (V : X.Opens) := X.basicOpen_le f hy
    by_contra hyW
    have h1 : J.subschemeι y ∈ (Scheme.IdealSheafData.vanishingIdeal C).support :=
      (hsupp _).2 ⟨y, hyW, rfl⟩
    rw [Scheme.IdealSheafData.mem_support_iff_of_mem hyV, Scheme.mem_zeroLocus_iff] at h1
    exact h1 f hf hy
  · intro m hm
    obtain ⟨w, hw⟩ := hW
    obtain ⟨V, hV, hxV, -⟩ := (TopologicalSpace.Opens.isBasis_iff_nbhd.1 X.isBasis_affineOpens)
      (show J.subschemeι w ∈ (⊤ : X.Opens) from trivial)
    let V' : X.affineOpens := ⟨V, hV⟩
    have hxV' : J.subschemeι w ∈ (V' : X.Opens) := hxV
    have hnC : J.subschemeι w ∉ (Scheme.IdealSheafData.vanishingIdeal C).support := by
      rw [hsupp]
      rintro ⟨w', hw', he⟩
      exact hw' (J.subschemeι.isClosedEmbedding.injective he ▸ hw)
    rw [Scheme.IdealSheafData.mem_support_iff_of_mem hxV', Scheme.mem_zeroLocus_iff] at hnC
    push_neg at hnC
    obtain ⟨f, hf, hxf⟩ := hnC
    have hfm : f ^ m ∈ J.ideal V' := Scheme.IdealSheafData.le_def.1 hm V' (Ideal.pow_mem_pow hf m)
    have hxJ : J.subschemeι w ∈ J.support := by
      rw [← SetLike.mem_coe, ← J.range_subschemeι]; exact ⟨w, rfl⟩
    rw [Scheme.IdealSheafData.mem_support_iff_of_mem hxV', Scheme.mem_zeroLocus_iff] at hxJ
    refine hxJ (f ^ m) hfm ?_
    rcases Nat.eq_zero_or_pos m with rfl | hm0
    · rw [pow_zero, Scheme.basicOpen_of_isUnit _ isUnit_one]; trivial
    · rwa [Scheme.basicOpen_pow _ _ hm0]

end GlobalTheory.CompanionTheory.GE.NonIso
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OpenRestrictionFunctionsCompatible
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh GlobalTheory.CompanionTheory.GE TensorProduct Opposite

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CompanionTheory.GE.RingCompat

attribute [local instance] algebraOfOver

lemma topIso_inv_res_hom {X : Scheme.{0}} (V : X.Opens) :
    X.presheaf.map (homOfLE le_top : V ⟶ ⊤).op ≫ V.topIso.inv = V.ι.appTop := by
  rw [Scheme.Opens.topIso_inv, Scheme.Hom.appTop, Scheme.Opens.ι_app]
  exact (X.presheaf.map_comp _ _).symm.trans (congrArg X.presheaf.map (Subsingleton.elim _ _))

lemma topIso_inv_res {X : Scheme.{0}} (V : X.Opens) (c : Γ(X, ⊤)) :
    V.topIso.inv (X.presheaf.map (homOfLE le_top : V ⟶ ⊤).op c) = V.ι.appTop c :=
  ConcreteCategory.congr_hom (topIso_inv_res_hom V) c

lemma appIso_hom_res {Z : Scheme.{0}} (O : Z.Opens) (W : (O : Scheme.{0}).Opens) (d : Γ(Z, ⊤)) :
    (O.ι.appIso W).hom (Z.presheaf.map (homOfLE le_top : O.ι ''ᵁ W ⟶ ⊤).op d) =
      (O : Scheme.{0}).presheaf.map (homOfLE le_top : W ⟶ ⊤).op (O.ι.appTop d) := by
  rw [← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply, Scheme.Hom.appIso_hom',
    Scheme.Hom.map_appLE]
  rfl

lemma morphismRestrict_appTop_ι {X Z : Scheme.{0}} (φ : Z ⟶ X) (V : X.Opens) (c : Γ(X, ⊤)) :
    (φ ∣_ V).appTop (V.ι.appTop c) = (φ ⁻¹ᵁ V).ι.appTop (φ.appTop c) := by
  have h := congrArg Scheme.Hom.appTop (morphismRestrict_ι φ V)
  rw [Scheme.Hom.comp_appTop, Scheme.Hom.comp_appTop] at h
  exact ConcreteCategory.congr_hom h c

lemma overBase_appTop {X Z : Scheme.{0}} (φ : Z ⟶ X) (V : X.Opens) (hV : IsAffineOpen V)
    (b : Γ(X, V)) :
    (φ ∣_ V ≫ hV.isoSpec.hom).appTop ((Scheme.ΓSpecIso (.of Γ(X, V))).inv b) =
      (φ ∣_ V).appTop (V.topIso.inv b) := by
  rw [Scheme.Hom.comp_appTop, CommRingCat.comp_apply, IsAffineOpen.isoSpec_hom_appTop,
    CommRingCat.comp_apply]
  erw [Iso.inv_hom_id_apply]

theorem toFunctions_preimage : ∀ {A : Type} [CommRing A] [IsNoetherianRing A] {X Z : Scheme.{0}} [X.Over (Spec (.of A))] [Z.Over (Spec (.of A))] (φ : Z ⟶ X), φ ≫ (X ↘ Spec (.of A)) = (Z ↘ Spec (.of A)) → ∀ (V : X.Opens) (hV : IsAffineOpen V) [IsNoetherianRing Γ(X, V)], letI : (φ ⁻¹ᵁ V).toScheme.Over (Spec (.of Γ(X, V))) := ⟨φ ∣_ V ≫ hV.isoSpec.hom⟩; ∀ (W : (φ ⁻¹ᵁ V).toScheme.Opens) (a : A), ((φ ⁻¹ᵁ V).ι.appIso W).hom (toFunctions (A := A) ((φ ⁻¹ᵁ V).ι ''ᵁ W) a) = toFunctions (A := Γ(X, V)) W (toFunctions (A := A) V a) := by
  intro A _ _ X Z _ _ φ hφ V hV _ W a
  have hZ : (Z ↘ Spec (.of A)).appTop ((Scheme.ΓSpecIso (.of A)).inv a) =
      φ.appTop ((X ↘ Spec (.of A)).appTop ((Scheme.ΓSpecIso (.of A)).inv a)) := by
    rw [← hφ, Scheme.Hom.comp_appTop]
    rfl
  change ((φ ⁻¹ᵁ V).ι.appIso W).hom (Z.presheaf.map (homOfLE le_top).op
      ((Z ↘ Spec (.of A)).appTop ((Scheme.ΓSpecIso (.of A)).inv a))) =
    (φ ⁻¹ᵁ V).toScheme.presheaf.map (homOfLE le_top).op
      ((φ ∣_ V ≫ hV.isoSpec.hom).appTop ((Scheme.ΓSpecIso (.of Γ(X, V))).inv
        (X.presheaf.map (homOfLE le_top).op
          ((X ↘ Spec (.of A)).appTop ((Scheme.ΓSpecIso (.of A)).inv a)))))
  rw [overBase_appTop, topIso_inv_res, morphismRestrict_appTop_ι, hZ, appIso_hom_res]

end GlobalTheory.CompanionTheory.GE.RingCompat
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PlacesIdempotentMulAbsorb
section
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes IsDedekindDomain NumberField GlobalTheory.Published Sa2 GlobalTheory.CompanionTheory.SaGen
open scoped TensorProduct Topology

namespace GlobalTheory.CompanionTheory.SaGen

theorem idem_mul_eq_of_subset : ∀ {F : Type} [Field F] [NumberField F] {A₁ B₁ : Finset (InfinitePlace F)}
    {A₂ B₂ : Finset (HeightOneSpectrum (𝓞 F))} {a b : AF F}, IsPlacesIdem A₁ A₂ a → IsPlacesIdem B₁ B₂ b →
    A₁ ⊆ B₁ → A₂ ⊆ B₂ → b * a = a := by
  intro F _ _ A₁ B₁ A₂ B₂ a b ha hb h1 h2
  obtain ⟨ha1, ha2, ha3, ha4⟩ := ha
  obtain ⟨hb1, -, hb3, -⟩ := hb
  refine adele_ext ?_ (finAdele_ext fun v => ?_)
  · rw [map_mul]
    refine ainf_ext fun w => ?_
    change fstA F b w * fstA F a w = fstA F a w
    by_cases hw : w ∈ A₁
    · rw [hb1 w (h1 hw), one_mul]
    · rw [ha2 w hw, mul_zero]
  · rw [map_mul, map_mul]
    by_cases hv : v ∈ A₂
    · rw [hb3 v (h2 hv), one_mul]
    · rw [ha4 v hv, mul_zero]

end GlobalTheory.CompanionTheory.SaGen
end

