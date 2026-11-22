import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0012
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsPrincipalIdealRingOfHenselian
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsFinEmb
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0213
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0190
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0010
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CanonicalFlagExistsUniqueSemistable
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0209
import Formalism.SharpRestriction.GlobalSchurBounds.ThickPlacesCorollaryOfAnyTranslate
import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0215
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0011
import Formalism.SharpRestriction.CuspSpanNormBounds.CongruenceAtSplitFrobeniusHolds

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsDualFamilyInSelfDualLattice
section
open ValuativeRel Formalism.MainNotions.S Formalism.MainNotions.S.Loc Formalism.MainNotions.S.LocNG GlobalTheory.LocOver
open scoped Classical

noncomputable section

namespace GlobalTheory.SelfDualFrame

section Algebra

variable {E : Type} [CommRing E] (O : Subring E)

def consZero (n : ℕ) : (Fin n → O) →ₗ[O] (Fin (n + 1) → O) where
  toFun v := Fin.cons 0 v
  map_add' v w := by
    ext i
    refine Fin.cases ?_ (fun j => ?_) i <;> simp
  map_smul' k v := by
    ext i
    refine Fin.cases ?_ (fun j => ?_) i <;> simp

theorem eq_top_of_dual
    (hQ : ∀ J : Ideal O, (∀ d : E, (∀ j ∈ J, d * (j : E) ∈ O) → d ∈ O) → J = ⊤) :
    ∀ (n : ℕ) (I : Submodule O (Fin n → O)),
      (∀ c : Fin n → E, (∀ x ∈ I, ∑ i, c i * (x i : E) ∈ O) → ∀ i, c i ∈ O) → I = ⊤ := by
  intro n
  induction n with
  | zero =>
    intro I _
    rw [eq_top_iff]
    intro x _
    rw [Subsingleton.elim x 0]
    exact I.zero_mem
  | succ n ih =>
    intro I hI
    have hJ : I.map (LinearMap.proj 0 : (Fin (n + 1) → O) →ₗ[O] O) = ⊤ := by
      refine hQ _ (fun d hd => ?_)
      have h := hI (Pi.single 0 d) (fun x hx => by
        have h1 : ∑ i, (Pi.single 0 d : Fin (n + 1) → E) i * (x i : E) = d * (x 0 : E) := by
          rw [Finset.sum_eq_single 0]
          · simp
          · intro b _ hb; simp [Pi.single_apply, hb]
          · simp
        rw [h1]
        exact hd (x 0) ⟨x, hx, rfl⟩)
      simpa using h 0
    obtain ⟨x₁, hx₁, h1⟩ : ∃ x ∈ I, x 0 = 1 := by
      have : (1 : O) ∈ I.map (LinearMap.proj 0 : (Fin (n + 1) → O) →ₗ[O] O) := by
        rw [hJ]; exact Submodule.mem_top
      obtain ⟨x, hx, e⟩ := this
      exact ⟨x, hx, e⟩
    have hret : ∀ w : Fin (n + 1) → O, consZero O n (Fin.tail (w - w 0 • x₁)) = w - w 0 • x₁ := by
      intro w
      ext i
      refine Fin.cases ?_ (fun j => ?_) i
      · simp [consZero, h1]
      · simp [consZero, Fin.tail]
    have hI₀ : I.comap (consZero O n) = ⊤ := by
      refine ih _ (fun c hc => ?_)
      have h := hI (Fin.cons (-∑ i, c i * (x₁ i.succ : E)) c) (fun w hw => by
        have hm : Fin.tail (w - w 0 • x₁) ∈ I.comap (consZero O n) := by
          rw [Submodule.mem_comap, hret]
          exact I.sub_mem hw (I.smul_mem _ hx₁)
        have h2 := hc _ hm
        rw [Fin.sum_univ_succ]
        simp only [Fin.cons_zero, Fin.cons_succ]
        convert h2 using 1
        simp only [Fin.tail, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
        push_cast
        rw [neg_mul, Finset.sum_mul]
        simp only [mul_sub, Finset.sum_sub_distrib]
        have e3 : ∀ i, c i * ((w 0 : E) * (x₁ i.succ : E)) = c i * (x₁ i.succ : E) * (w 0 : E) :=
          fun i => by ring
        simp only [e3]
        ring)
      intro i
      simpa using h i.succ
    rw [eq_top_iff]
    intro w _
    have e : w = consZero O n (Fin.tail (w - w 0 • x₁)) + w 0 • x₁ := by rw [hret]; abel
    rw [e]
    refine I.add_mem ?_ (I.smul_mem _ hx₁)
    have : Fin.tail (w - w 0 • x₁) ∈ I.comap (consZero O n) := by rw [hI₀]; exact Submodule.mem_top
    exact this

end Algebra

section Local

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
  {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]

theorem ideal_eq_top_of_inv [IsNonarchimedeanLocalField F] [CharZero F] (L : LocE F E) :
    ∀ J : Ideal L.O, (∀ d : E, (∀ j ∈ J, d * (j : E) ∈ L.O) → d ∈ L.O) → J = ⊤ := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[F]
  obtain ⟨-, hO2, -, hPIR, hmem, -⟩ := GlobalTheory.UnramOrder.order_facts L ϖ hϖ
  have hcj : ∀ x ∈ L.O, L.cj x ∈ L.O := fun x hx => (hO2 x hx).1
  have hz : ∀ u : F, (∀ t : F, algebraMap F E (t * u) ∈ L.O) → u = 0 := by
    intro u hu
    by_contra h0
    have h3 := (hmem _).1 (hu ((ϖ : F)⁻¹ * u⁻¹))
    rw [mul_assoc, inv_mul_cancel₀ h0, mul_one] at h3
    have hϖ0 : (ϖ : F) ≠ 0 := fun h => hϖ.ne_zero (Subtype.ext h)
    exact hϖ.not_isUnit (IsUnit.of_mul_eq_one (a := ϖ) ⟨_, h3⟩ (Subtype.ext (by simp [hϖ0])))
  intro J hJ
  obtain ⟨a, rfl⟩ := (hPIR.principal J).principal
  by_cases hu : IsUnit (a : E)
  · obtain ⟨b, hb⟩ := hu.exists_right_inv
    have hbO : b ∈ L.O := hJ b (fun j hj => by
      obtain ⟨k, rfl⟩ := Ideal.mem_span_singleton'.1 hj
      push_cast
      rw [show b * ((k : E) * a) = k by linear_combination (k : E) * hb]
      exact k.2)
    exact Ideal.span_singleton_eq_top.2 (IsUnit.of_mul_eq_one (a := a) ⟨b, hbO⟩ (Subtype.ext hb))
  · exfalso
    haveI : Module.Finite F E := Module.finite_of_finrank_eq_succ L.rank
    have hns : ¬ Function.Surjective (LinearMap.mulLeft F (a : E)) := fun h => hu (by
      obtain ⟨b, hb⟩ := h 1
      exact IsUnit.of_mul_eq_one b hb)
    have hni : ¬ Function.Injective (LinearMap.mulLeft F (a : E)) :=
      fun h => hns (LinearMap.injective_iff_surjective.1 h)
    obtain ⟨s, hs, hs0⟩ : ∃ s : E, (a : E) * s = 0 ∧ s ≠ 0 := by
      by_contra hc
      push_neg at hc
      exact hni ((injective_iff_map_eq_zero _).2 (fun s h => hc s h))
    have hts : ∀ t : F, algebraMap F E t * s ∈ L.O := fun t => hJ _ (fun j hj => by
      obtain ⟨k, rfl⟩ := Ideal.mem_span_singleton'.1 hj
      push_cast
      rw [show algebraMap F E t * s * ((k : E) * a) = 0 by
        linear_combination (algebraMap F E t * k) * hs]
      exact L.O.zero_mem)
    have hs1 : s ∈ L.O := by simpa using hts 1
    obtain ⟨u, hu'⟩ := (L.cj_fix (s + L.cj s)).1 (by rw [map_add, L.cj_cj, add_comm])
    obtain ⟨m, hm⟩ := (L.cj_fix (s * L.cj s)).1 (by rw [map_mul, L.cj_cj, mul_comm])
    have hu0 : u = 0 := hz u (fun t => by
      have h4 := L.O.add_mem (hts t) (hcj _ (hts t))
      convert h4 using 1
      rw [map_mul, hu', map_mul, AlgEquiv.commutes]
      ring)
    have hm0 : m = 0 := hz m (fun t => by
      have h4 := L.O.mul_mem (hts t) (hcj _ hs1)
      convert h4 using 1
      rw [map_mul, hm]
      ring)
    rw [hu0, map_zero] at hu'
    rw [hm0, map_zero] at hm
    have hss : s ^ 2 = 0 := by linear_combination (-s) * hu' + hm
    have := L.reduced
    exact hs0 (IsReduced.eq_zero s ⟨2, hss⟩)

end Local

theorem exists_dual_family : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E] (M : Model F E), M.OK → ∀ {V : Type} [AddCommGroup V] [Module E V] (H : HermSp M V) (r : ℕ) (Fr : FrameD H r) (Λ : Submodule M.L.O V), H.IsSelfDual Λ → H.IsFrame Λ r Fr.f Fr.T → ∃ y : Fin (r + 1) → V, (∀ b, y b ∈ Λ) ∧ ∀ a b, H.h (y b) (Fr.f a) = if a = b then 1 else 0 := by
  intro F _ _ _ E _ _ _ _ M hM V _ _ H r Fr Λ hsd hfr
  letI := hM.loc
  haveI := hM.char0
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[F]
  obtain ⟨-, hO2, -⟩ := GlobalTheory.UnramOrder.order_facts M.L ϖ hϖ
  have hcj : ∀ x ∈ M.L.O, M.L.cj x ∈ M.L.O := fun x hx => (hO2 x hx).1
  obtain ⟨-, -, hd⟩ := hsd
  obtain ⟨⟨hfΛ, hli, hprim⟩, -⟩ := hfr
  have hval : ∀ y ∈ Λ, ∀ a, H.h y (Fr.f a) ∈ M.L.O := fun y hy a => (hd y).1 hy _ (hfΛ a)
  have hsum : ∀ (y : V) (g : Fin (r + 1) → V), H.h (∑ a, g a) y = ∑ a, H.h (g a) y := fun y g =>
    map_sum (AddMonoidHom.mk' (fun x => H.h x y) (fun x x' => H.h_add_left x x' y)) g Finset.univ
  have hh2 : ∀ (y : V) (k : Fin (r + 1) → E),
      H.h y (∑ a, k a • Fr.f a) = ∑ a, M.L.cj (k a) * H.h y (Fr.f a) := by
    intro y k
    rw [H.h_herm, hsum, map_sum]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    rw [H.h_smul_left, map_mul, ← H.h_herm]
  let I : Submodule M.L.O (Fin (r + 1) → M.L.O) :=
    { carrier := {x | ∃ y ∈ Λ, ∀ a, (x a : E) = H.h y (Fr.f a)}
      add_mem' := by
        rintro x x' ⟨y, hy, e⟩ ⟨y', hy', e'⟩
        refine ⟨y + y', Λ.add_mem hy hy', fun a => ?_⟩
        simp only [Pi.add_apply, Subring.coe_add, H.h_add_left, e, e']
      zero_mem' := ⟨0, Λ.zero_mem, fun a => by simp [H.h_zero_left]⟩
      smul_mem' := by
        rintro k x ⟨y, hy, e⟩
        refine ⟨k • y, Λ.smul_mem k hy, fun a => ?_⟩
        simp only [Pi.smul_apply, smul_eq_mul, Subring.coe_mul, e]
        rw [Subring.smul_def, H.h_smul_left] }
  have hItop : I = ⊤ := by
    refine eq_top_of_dual M.L.O (ideal_eq_top_of_inv M.L) (r + 1) I (fun c hc => ?_)
    set w := ∑ a, M.L.cj (c a) • Fr.f a with hwdef
    have hw : ∀ y ∈ Λ, H.h y w ∈ M.L.O := fun y hy => by
      have h1 := hc (fun a => ⟨H.h y (Fr.f a), hval y hy a⟩) ⟨y, hy, fun a => rfl⟩
      rw [hwdef, hh2]
      simpa [M.L.cj_cj] using h1
    have hwΛ : w ∈ Λ := (hd w).2 (fun y hy => by
      rw [H.h_herm y w]
      exact hcj _ (hw y hy))
    have hwE : w ∈ Submodule.span E (Set.range Fr.f) :=
      Submodule.sum_mem _ (fun a _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, rfl⟩))
    obtain ⟨d, hdw⟩ := (Submodule.mem_span_range_iff_exists_fun M.L.O).1 (hprim w hwΛ hwE)
    have heq : ∀ a, M.L.cj (c a) = d a := by
      have h2 := Fintype.linearIndependent_iff.1 hli (fun a => M.L.cj (c a) - (d a : E)) (by
        simp only [sub_smul, Finset.sum_sub_distrib]
        rw [← hwdef, ← hdw]
        simp [Subring.smul_def])
      intro a
      exact sub_eq_zero.1 (h2 a)
    intro a
    have h3 := hcj _ (show M.L.cj (c a) ∈ M.L.O by rw [heq a]; exact (d a).2)
    rwa [M.L.cj_cj] at h3
  have hmemb : ∀ b, ∃ y ∈ Λ, ∀ a, ((Pi.single b 1 : Fin (r + 1) → M.L.O) a : E) = H.h y (Fr.f a) :=
    fun b => by
      have h4 : (Pi.single b 1 : Fin (r + 1) → M.L.O) ∈ I := by rw [hItop]; exact Submodule.mem_top
      exact h4
  choose y hyΛ hy using hmemb
  refine ⟨y, hyΛ, fun a b => ?_⟩
  rw [← hy b a, Pi.single_apply]
  split_ifs <;> simp

end GlobalTheory.SelfDualFrame
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsDualVectorsLocalHermitianFrame
section
noncomputable section

open ValuativeRel Formalism.MainNotions.S Formalism.MainNotions.S.Loc Formalism.MainNotions.S.LocNG GlobalTheory.LocOver
open scoped Classical

namespace GlobalTheory.LocDual

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
  {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
  {M : Model F E} {V : Type} [AddCommGroup V] [Module E V]

private lemma h_add_right (H : HermSp M V) (x y y' : V) : H.h x (y + y') = H.h x y + H.h x y' := by
  rw [H.h_herm (y + y') x, H.h_add_left, map_add, ← H.h_herm y x, ← H.h_herm y' x]

private lemma h_smul_right (H : HermSp M V) (a : E) (x y : V) : H.h x (a • y) = M.L.cj a * H.h x y := by
  rw [H.h_herm (a • y) x, H.h_smul_left, map_mul, ← H.h_herm y x]

private lemma h_neg_left (H : HermSp M V) (x y : V) : H.h (-x) y = - H.h x y := by
  have := H.h_smul_left (-1) x y
  simpa using this

private lemma h_sub_left (H : HermSp M V) (x x' y : V) : H.h (x - x') y = H.h x y - H.h x' y := by
  rw [sub_eq_add_neg, H.h_add_left, h_neg_left, ← sub_eq_add_neg]

private lemma h_sub_right (H : HermSp M V) (x y y' : V) : H.h x (y - y') = H.h x y - H.h x y' := by
  rw [H.h_herm (y - y') x, h_sub_left, map_sub, ← H.h_herm y x, ← H.h_herm y' x]

private lemma h_sum_left (H : HermSp M V) {ι : Type} (s : Finset ι) (v : ι → V) (y : V) :
    H.h (∑ i ∈ s, v i) y = ∑ i ∈ s, H.h (v i) y := by
  let φ : V →+ E := AddMonoidHom.mk' (fun x => H.h x y) (fun a b => H.h_add_left a b y)
  exact map_sum φ v s

private lemma h_sum_right (H : HermSp M V) {ι : Type} (s : Finset ι) (v : ι → V) (x : V) :
    H.h x (∑ i ∈ s, v i) = ∑ i ∈ s, H.h x (v i) := by
  let φ : V →+ E := AddMonoidHom.mk' (fun y => H.h x y) (fun a b => h_add_right H x a b)
  exact map_sum φ v s

end GlobalTheory.LocDual

open GlobalTheory.LocDual in

theorem GlobalTheory.LocDual.frameD_exists : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E] (M : Model F E), M.OK → ∀ {V : Type} [AddCommGroup V] [Module E V] (H : HermSp M V) (r : ℕ), ∀ (f : Fin (r + 1) → V) (T : F), T ≠ 0 → (∀ a b : Fin (r + 1), (a ≠ Fin.last r ∨ b ≠ Fin.last r) → H.h (f a) (f b) = 0) → H.h (f (Fin.last r)) (f (Fin.last r)) = -(algebraMap F E T) → (∃ y : Fin r → V, ∀ i j : Fin r, H.h (f i.castSucc) (y j) = if i = j then 1 else 0) → ∃ Fr : FrameD H r, Fr.f = f ∧ Fr.T = T := by
  intro F _ _ _ E _ _ _ _ M hM V _ _ H r f T hT hiso hzz hy
  obtain ⟨y, hy⟩ := hy
  haveI := hM.char0
  set z := f (Fin.last r) with hz
  set e : Fin r → V := fun i => f i.castSucc with he
  have hez : ∀ k, H.h (e k) z = 0 := fun k => hiso _ _ (Or.inl (Fin.castSucc_ne_last k))
  have hze : ∀ k, H.h z (e k) = 0 := fun k => hiso _ _ (Or.inr (Fin.castSucc_ne_last k))
  have hee : ∀ k l, H.h (e k) (e l) = 0 := fun k l => hiso _ _ (Or.inl (Fin.castSucc_ne_last k))
  let y' : Fin r → V := fun j => y j + (H.h (y j) z * algebraMap F E T⁻¹) • z
  have hy'z : ∀ j, H.h (y' j) z = 0 := by
    intro j
    simp only [y', H.h_add_left, H.h_smul_left, hzz]
    rw [show H.h (y j) z * algebraMap F E T⁻¹ * -algebraMap F E T
        = - (H.h (y j) z * algebraMap F E (T⁻¹ * T)) by rw [map_mul]; ring]
    rw [inv_mul_cancel₀ hT, map_one, mul_one, add_neg_cancel]
  have hey' : ∀ k j, H.h (e k) (y' j) = if k = j then 1 else 0 := by
    intro k j
    simp only [y', h_add_right, h_smul_right, hez, mul_zero, add_zero, e]
    exact hy k j
  let half : E := algebraMap F E (1 / 2)
  have hhalf : M.L.cj half = half := M.L.cj.commutes _
  have hhalf2 : half + half = 1 := by
    simp only [half, ← map_add, add_halves, map_one]
  let b : Fin r → Fin r → E := fun j k => half * H.h (y' j) (y' k)
  let es : Fin r → V := fun j => y' j - ∑ k, b j k • e k
  have hesL : ∀ i v, H.h (es i) v = H.h (y' i) v - ∑ k, b i k * H.h (e k) v := by
    intro i v
    simp only [es, h_sub_left, h_sum_left, H.h_smul_left]
  have hesR : ∀ v j, H.h v (es j) = H.h v (y' j) - ∑ k, M.L.cj (b j k) * H.h v (e k) := by
    intro v j
    simp only [es, h_sub_right, h_sum_right, h_smul_right]
  have hy'e : ∀ i k, H.h (y' i) (e k) = if k = i then 1 else 0 := by
    intro i k
    rw [H.h_herm, hey' k i]
    split_ifs <;> simp
  refine ⟨⟨f, es, T, hiso, hzz, ?_, ?_, ?_⟩, rfl, rfl⟩
  · intro i j
    rw [hesR]
    simp only [hesL, hey', hy'e, hee, mul_zero, Finset.sum_const_zero, sub_zero, mul_ite, mul_one,
      Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    simp only [b, map_mul, hhalf]
    rw [← H.h_herm (y' j) (y' i)]
    linear_combination (-H.h (y' i) (y' j)) * hhalf2
  · intro i j
    show H.h (e i) (es j) = _
    rw [hesR]
    simp only [hey', hee, mul_zero, Finset.sum_const_zero, sub_zero]
  · intro i
    show H.h (es i) z = 0
    rw [hesL]
    simp only [hy'z, hez, mul_zero, Finset.sum_const_zero, sub_zero]
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsFiniteAdelicOrthogonalStabilizerEmbedding
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.GaussMean GlobalTheory.StabUnfold
open scoped TensorProduct

namespace GlobalTheory.StabUnfold

theorem exists_stab_emb_baseChange {E R : Type} [Field E] [StarRing E] [CommRing R] (φ : E →+* R)
    (σ : R →+* R) (hσ : ∀ a, σ (φ a) = φ (star a)) {n m : ℕ} (J : Matrix (Fin n) (Fin n) E)
    (J' : Matrix (Fin m) (Fin m) E) (x : Fin n → E) (A : Matrix (Fin n) (Fin m) E)
    (hn : m + 1 = n) (hJ : Jᴴ = J) (hd : J'.det ≠ 0) (hx : star x ⬝ᵥ (J *ᵥ x) ≠ 0)
    (hxA : star x ᵥ* (J * A) = 0) (hA : Aᴴ * J * A = J') :
    ∃ j : Formalism.UG.UJ σ (J'.map φ) →* Formalism.UG.UJ σ (J.map φ),
      (∀ g, ((j g : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) *ᵥ (fun i => φ (x i)) = (fun i => φ (x i)) ∧
        ((j g : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) * A.map φ =
          A.map φ * ((g : GL (Fin m) R) : Matrix (Fin m) (Fin m) R)) ∧
      ∀ h : Formalism.UG.UJ σ (J.map φ),
        ((h : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) *ᵥ (fun i => φ (x i)) = (fun i => φ (x i)) →
          h ∈ j.range := by
  obtain ⟨u, A', h1, h2, h3, h4, h5, h6⟩ := exists_dual_of_anisotropic_orthogonal E n m J J' x A hn hJ hd hx hxA hA
  have hsx : (fun i => σ (φ (x i))) = φ ∘ star x := by
    funext i; simp [hσ]
  have hcT : Formalism.UG.cT σ (A.map φ) = (Aᴴ).map φ := by
    ext i j; simp [Formalism.UG.cT, hσ]
  have mv : ∀ {a b : ℕ} (M : Matrix (Fin a) (Fin b) E) (v : Fin b → E),
      M.map φ *ᵥ (φ ∘ v) = φ ∘ (M *ᵥ v) := by
    intro a b M v; funext i; exact (RingHom.map_mulVec φ M v i).symm
  have vm : ∀ {a b : ℕ} (M : Matrix (Fin a) (Fin b) E) (v : Fin a → E),
      (φ ∘ v) ᵥ* M.map φ = φ ∘ (v ᵥ* M) := by
    intro a b M v; funext i; exact (RingHom.map_vecMul φ M v i).symm
  have z : ∀ {a : ℕ}, φ ∘ (0 : Fin a → E) = 0 := by
    intro a; funext i; simp
  have k1 : A'.map φ * A.map φ = 1 := by
    rw [← Matrix.map_mul, h1, Matrix.map_one φ (map_zero φ) (map_one φ)]
  have k2 : A'.map φ *ᵥ (φ ∘ x) = 0 := by rw [mv, h2, z]
  have k3 : (φ ∘ u) ᵥ* A.map φ = 0 := by rw [vm, h3, z]
  have k4 : (φ ∘ u) ⬝ᵥ (φ ∘ x) = 1 := by rw [← RingHom.map_dotProduct, h4, map_one]
  have k5 : vecMulVec (φ ∘ x) (φ ∘ u) + A.map φ * A'.map φ = 1 := by
    rw [← Matrix.map_one φ (map_zero φ) (map_one φ), ← h5, ← Matrix.map_mul]
    ext i j; simp [vecMulVec_apply, Matrix.mul_apply]
  obtain ⟨j, hj, hr⟩ := GlobalTheory.T.exists_unitary_orthogonal_embedding_stabilizer R σ n m (J.map φ) (J'.map φ) (φ ∘ x) (φ ∘ u) (A.map φ) (A'.map φ)
    (by
      change IsUnit ((fun i => σ (φ (x i))) ⬝ᵥ _)
      rw [hsx, mv, ← RingHom.map_dotProduct]
      exact (IsUnit.mk0 _ hx).map φ)
    (by
      change (fun i => σ (φ (x i))) ᵥ* _ = 0
      rw [hsx, ← Matrix.map_mul, vm, hxA, z])
    (by rw [hcT, mv, mv, h6, z])
    (by rw [hcT, ← Matrix.map_mul, ← Matrix.map_mul, hA])
    k1 k2 k3 k4 k5
  refine ⟨j, fun g => ⟨?_, ?_⟩, hr⟩
  · change _ *ᵥ (φ ∘ x) = φ ∘ x
    rw [hj, Matrix.add_mulVec, ← Matrix.mulVec_mulVec, k2, Matrix.mulVec_zero, add_zero,
      Matrix.vecMulVec_mulVec, k4]
    simp
  · rw [hj, Matrix.add_mul, Matrix.mul_assoc, k1, Matrix.mul_one, Matrix.vecMulVec_mul, k3]
    ext a b; simp [vecMulVec_apply]

theorem exists_finEmb : ∀ (I : AutInst) (D : Sib I) (s : Bool) (x : Fin I.n → I.E) (A : Matrix (Fin I.n) (Fin D.n) I.E) (xf : I.Gf), IsPerp D s x A xf → ∃ jf : D.inst.Gf →* I.Gf, IsFinEmb D x A jf ∧ ∀ h : I.Gf, I.fmat h *ᵥ afVec I x = afVec I x → h ∈ jf.range := by
  intro I D s x A xf h
  obtain ⟨hn, hx, hxA, hA, -, -⟩ := h
  have hσ : ∀ a : I.E, Formalism.UG.sigR I.cm.sig (Af I.F) (Formalism.UG.inclE (F := I.F) (Af I.F) a) =
      Formalism.UG.inclE (F := I.F) (Af I.F) (star a) := by
    intro a
    have : I.cm.sig a = star a := rfl
    simp [Formalism.UG.sigR, Formalism.UG.inclE, this]
  have hx' : star x ⬝ᵥ (I.J *ᵥ x) ≠ 0 := by
    rw [hx]; cases s <;> simp [sgn]
  exact exists_stab_emb_baseChange (Formalism.UG.inclE (F := I.F) (Af I.F)) (Formalism.UG.sigR I.cm.sig (Af I.F)) hσ
    I.J D.J x A hn I.J_herm D.J_det hx' hxA hA

end GlobalTheory.StabUnfold
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsIsSatFlag
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase

noncomputable section

namespace GlobalTheory.FlagSat

theorem mem_of_isSat (I : AutInst) (x : I.GA) {N : Submodule (𝓞 I.E) (Fin I.n → I.E)}
    (hN : Formalism.HN.IsSat (Formalism.HermitianLatticesTheory.realize (bas I) (frm I x)) (lamX I x) N) {y : Fin I.n → I.E}
    (hy : y ∈ lamX I x) (hy' : y ∈ Submodule.span I.E (N : Set (Fin I.n → I.E))) : y ∈ N := by
  set A : Submodule (𝓞 I.E) (Fin I.n → I.E) :=
    lamX I x ⊓ (Submodule.span I.E (N : Set (Fin I.n → I.E))).restrictScalars (𝓞 I.E) with hA
  have hle : N ≤ A := fun z hz => ⟨hN.1 hz, Submodule.subset_span hz⟩
  have hAL : A ≤ lamX I x := inf_le_left
  have e : N = A := by
    by_contra hne
    have h1 := GlobalTheory.PointFlag.rkK_lt _ _ (GlobalTheory.PointFlag.frm_unit I x) (GlobalTheory.PointFlag.fg_of_le I x hAL)
      (GlobalTheory.PointFlag.isSat_of_le _ _ hN hle hAL) hne
    have h2 : Submodule.span I.E (A : Set (Fin I.n → I.E)) ≤ Submodule.span I.E (N : Set (Fin I.n → I.E)) :=
      Submodule.span_le.2 fun z hz => hz.2
    exact absurd h1 (not_lt.2 (Submodule.finrank_mono h2))
  rw [e]
  exact ⟨hy, hy'⟩

theorem exists_isSatFlag : ∀ (I : AutInst) (a : ℕ) (j : Fin a → ℕ) (B : Set (Fin a → ℝ)) (x : I.GA), x ∈ typeSet I j B → ∃ S, IsSatFlag I (lamX I (1, x.2)) j S ∧ sizesAt I x.2 S x.1 ∈ B := by
  rintro I a j B x ⟨τ, hτ, S, hS, hj⟩
  refine ⟨S, ⟨hS.1, hS.2.1.monotone, hj, fun i y => ?_, ?_⟩, ?_⟩
  · have h := GlobalTheory.PointFlag.flag_sat hS i
    exact ⟨fun hy => ⟨h.1 hy, Submodule.subset_span hy⟩, fun hy => mem_of_isSat I x h hy.1 hy.2⟩
  · rw [hS.2.2.1]
    exact (GlobalTheory.FlagIso.flag_isotropic I x).1
  · have e : sizesAt I x.2 S x.1 = τ := funext fun i => (hS.2.2.2.2.1 i).2.2.2
    rw [e]
    exact hτ

end GlobalTheory.FlagSat
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.FinprodPlacesOverTypePrimesSplit
section
open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain

namespace GlobalTheory.TypedPlacesProduct

theorem finite_over {K : Type*} [Field K] [NumberField K] {n : ℕ} (hn : n ≠ 0) :
    {v : HeightOneSpectrum (𝓞 K) | ((n : ℕ) : 𝓞 K) ∈ v.asIdeal}.Finite := by
  have hI : Ideal.span {((n : ℕ) : 𝓞 K)} ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact Nat.cast_ne_zero.mpr hn
  refine (Ideal.finite_factors hI).subset ?_
  intro v hv
  simp only [Set.mem_setOf_eq] at hv ⊢
  rw [Ideal.dvd_iff_le, Ideal.span_singleton_le_iff_mem]
  exact hv

theorem finprod_over {K : Type*} [Field K] [NumberField K] {n f : ℕ} (hn : n ≠ 0) (φ : ℝ → ℝ)
    (hc : Nat.card {v : HeightOneSpectrum (𝓞 K) // ((n : ℕ) : 𝓞 K) ∈ v.asIdeal} = f)
    (hq : ∀ v : HeightOneSpectrum (𝓞 K), ((n : ℕ) : 𝓞 K) ∈ v.asIdeal →
      Nat.card (𝓞 K ⧸ v.asIdeal) = n) :
    (∏ᶠ p ∈ {p : HeightOneSpectrum (𝓞 K) | ((n : ℕ) : 𝓞 K) ∈ p.asIdeal},
      φ (Ideal.absNorm p.asIdeal : ℝ)) = φ n ^ f := by
  have hs := finite_over (K := K) hn
  have hnorm : ∀ p ∈ {p : HeightOneSpectrum (𝓞 K) | ((n : ℕ) : 𝓞 K) ∈ p.asIdeal},
      φ (Ideal.absNorm p.asIdeal : ℝ) = φ n := by
    intro p hp
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply, hq p hp]
  rw [finprod_mem_congr rfl hnorm, finprod_mem_eq_finite_toFinset_prod _ hs, Finset.prod_const,
    ← Nat.card_eq_card_finite_toFinset hs]
  exact congrArg _ hc

private lemma disjoint_primes_dvd_of_coprime {K : Type*} [Field K] [NumberField K] {a b : ℕ} (hab : Nat.Coprime a b) :
    Disjoint {p : HeightOneSpectrum (𝓞 K) | ((a : ℕ) : 𝓞 K) ∈ p.asIdeal}
      {p : HeightOneSpectrum (𝓞 K) | ((b : ℕ) : 𝓞 K) ∈ p.asIdeal} := by
  rw [Set.disjoint_left]
  intro p ha hb
  obtain ⟨u, w, huw⟩ := (Nat.isCoprime_iff_coprime.mpr hab).map (Int.castRingHom (𝓞 K))
  have h1 : (1 : 𝓞 K) ∈ p.asIdeal := by
    rw [← huw]
    simp only [eq_intCast, Int.cast_natCast]
    exact p.asIdeal.add_mem (p.asIdeal.mul_mem_left _ ha) (p.asIdeal.mul_mem_left _ hb)
  exact p.isPrime.ne_top ((Ideal.eq_top_iff_one _).mpr h1)

theorem finprod_typed_places : ∀ (D : D7) (φ : ℝ → ℝ), (∀ i, StandardLattice.SplitsF D (D.host.g i)) → (∏ᶠ p ∈ {p : HeightOneSpectrum (𝓞 D.host.F) | ((D.host.g 0 : ℕ) : 𝓞 D.host.F) ∈ p.asIdeal ∨ ((D.host.g 1 : ℕ) : 𝓞 D.host.F) ∈ p.asIdeal}, φ (Ideal.absNorm p.asIdeal : ℝ)) = φ (D.host.g 0) ^ D.R.f * φ (D.host.g 1) ^ D.R.f := by
  intro D φ hs
  have hp := D.host.g_prime
  have hne : D.host.g 0 ≠ D.host.g 1 := D.host.g_ne
  have hcop : Nat.Coprime (D.host.g 0) (D.host.g 1) := (Nat.coprime_primes (hp 0) (hp 1)).mpr hne
  rw [Set.setOf_or, finprod_mem_union (disjoint_primes_dvd_of_coprime hcop) (finite_over (hp 0).ne_zero)
    (finite_over (hp 1).ne_zero), finprod_over (hp 0).ne_zero φ (hs 0).1 (hs 0).2,
    finprod_over (hp 1).ne_zero φ (hs 1).1 (hs 1).2]

end GlobalTheory.TypedPlacesProduct
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsPairMoveByIntegralUnipotentStatement
section
open NumberField Module Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.Cnt GlobalTheory.LoopC
open scoped ENNReal Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isPair_move_by_integralUnipotent : ∀ (D : D7) (T T' : D.host.E) (Λ : LatV D) (g : ℕ) (F : Fg D T) (F' F'' A B : Fg D T') (β n' n'' : (hS D).V ≃ₗ[D.host.E] (hS D).V), IsPair Λ F F' F'' β g → n' ∈ NLam Λ F → n'' ∈ NLam Λ F → FrameEqv D n' F' A → FrameEqv D n'' F'' B → IsAutLam (hS D) Λ (n'' * β * n'⁻¹) ∧ (Xsp A).map ((n'' * β * n'⁻¹ : (hS D).V ≃ₗ[D.host.E] (hS D).V) : (hS D).V →ₗ[D.host.E] (hS D).V) = Xsp B ∧ (n'' * β * n'⁻¹) A.fl.z - B.fl.z ∈ Xsp B ∧ IotaCompat Λ F A B (n'' * β * n'⁻¹) g := by
  first | exact @GlobalTheory.LoopC.PairMove.pair_move | exact GlobalTheory.LoopC.PairMove.pair_move | (intros; apply GlobalTheory.LoopC.PairMove.pair_move <;> assumption)
end

