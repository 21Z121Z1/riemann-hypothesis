import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.FormUniq
import Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.NLeA
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.Imports
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.Bundle0002
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HodgeXD
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0063
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FormConsMul
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LevelChainValuations.Bundle0001
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0317
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0172
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0178
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0157
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0160
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0181
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LatticeIsAdicComplete
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0185
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0318

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.KuennethProductLocalCoords
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false

noncomputable section

open CategoryTheory AlgebraicGeometry TensorProduct DirectSum GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.Onto CrystallineSemistableComparison.Pb CrystallineSemistableComparison.HT GlobalTheory.CompanionTheory.KunGlue

namespace GlobalTheory.CompanionTheory.KunGlue.Aff

universe u w

section Algebra

variable {R : Type} [CommRing R]

theorem tensor_sub_left (M N : Type u) [AddCommMonoid M] [AddCommMonoid N] [Module R M] [Module R N] [Subsingleton M] :
    Subsingleton (M ⊗[R] N) := by
  have key : ∀ z : M ⊗[R] N, z = 0 := fun z => by
    induction z using TensorProduct.induction_on with
    | zero => rfl
    | tmul x y => rw [Subsingleton.elim x 0, TensorProduct.zero_tmul]
    | add x y hx hy => rw [hx, hy, add_zero]
  exact ⟨fun a b => by rw [key a, key b]⟩

theorem tensor_sub_right (M N : Type u) [AddCommMonoid M] [AddCommMonoid N] [Module R M] [Module R N] [Subsingleton N] :
    Subsingleton (M ⊗[R] N) :=
  _root_.UpperTheory.Reformulated.B.Qn17.tensor_sub_right M N

variable {I A : Type} [DecidableEq I] [Fintype A] [DecidableEq A] (M : I → Type u) [∀ t, AddCommMonoid (M t)]
  [∀ t, Module R (M t)] (ι : A → I)

theorem component_lof_ne {i j : I} (h : j ≠ i) (x : M i) : DirectSum.component R I M j (DirectSum.lof R I M i x) = 0 := by
  rw [DirectSum.component.of]
  simp [h.symm]

def sumPi (hι : Function.Injective ι) (hz : ∀ t, t ∉ Set.range ι → Subsingleton (M t)) :
    (⨁ t, M t) ≃ₗ[R] ∀ a, M (ι a) :=
  LinearEquiv.ofLinear (LinearMap.pi fun a => DirectSum.component R I M (ι a))
    (∑ a, (DirectSum.lof R I M (ι a)).comp (LinearMap.proj a))
    (by
      refine LinearMap.ext fun f => funext fun b => ?_
      simp only [LinearMap.comp_apply, LinearMap.pi_apply, LinearMap.sum_apply, LinearMap.proj_apply, LinearMap.id_apply, map_sum]
      rw [Finset.sum_eq_single b]
      · exact DirectSum.component.lof_self R _ _
      · intro a _ hab
        exact component_lof_ne M (fun e => hab (hι e).symm) _
      · intro h
        exact absurd (Finset.mem_univ b) h)
    (by
      refine DirectSum.linearMap_ext R fun t => LinearMap.ext fun x => ?_
      by_cases ht : t ∈ Set.range ι
      · obtain ⟨b, rfl⟩ := ht
        simp only [LinearMap.comp_apply, LinearMap.pi_apply, LinearMap.sum_apply, LinearMap.proj_apply, LinearMap.id_apply]
        rw [Finset.sum_eq_single b]
        · rw [DirectSum.component.lof_self]
        · intro a _ hab
          rw [component_lof_ne M (fun e => hab (hι e)) x, map_zero]
        · intro h
          exact absurd (Finset.mem_univ b) h
      · have := hz t ht
        rw [Subsingleton.elim x 0, map_zero, map_zero])

theorem sumPi_lof (hι : Function.Injective ι) (hz : ∀ t, t ∉ Set.range ι → Subsingleton (M t)) (b : A) (x : M (ι b)) :
    sumPi (R := R) M ι hι hz (DirectSum.lof R I M (ι b) x) = Pi.single b x := by
  refine funext fun a => ?_
  change DirectSum.component R I M (ι a) (DirectSum.lof R I M (ι b) x) = _
  by_cases h : a = b
  · subst h
    rw [DirectSum.component.lof_self, Pi.single_eq_same]
  · rw [component_lof_ne M (fun e => h (hι e)) x, Pi.single_eq_of_ne h]

end Algebra

variable {K : Type} [Field K]

def diag (c : ℕ) (a : Fin (c + 1)) : Idx c c :=
  ⟨a, a, c - a, c - a, by omega, by omega⟩

theorem diag_inj (c : ℕ) : Function.Injective (diag c) := by
  intro a b h
  exact Fin.ext (congrArg Idx.a h)

theorem kunE_of_diag {P Q T : ℕ → Cx.{w} K} (pr : ∀ {a a' c : ℕ}, a + a' = c → CxPairing (P a) (Q a') (T c))
    (hP : ∀ a j, j ≠ a → Subsingleton ((P a).H j)) (hQ : ∀ a j, j ≠ a → Subsingleton ((Q a).H j))
    (hT : ∀ a j, j ≠ a → Subsingleton ((T a).H j))
    (hE : ∀ c : ℕ, ∃ e : (∀ a : Fin (c + 1), TensorProduct K ((P a).H a) ((Q (c - a)).H (c - a))) ≃ₗ[K] (T c).H c,
      ∀ (a : Fin (c + 1)) (hc : (a : ℕ) + (c - a) = c) (x : (P a).X a) (y : (Q (c - a)).X (c - a))
        (hx : (P a).d a x = 0) (hy : (Q (c - a)).d (c - a) y = 0) (hz : (T c).d c ((pr hc).μ hc x y) = 0),
        e (Pi.single a ((P a).cls x hx ⊗ₜ (Q (c - a)).cls y hy)) = (T c).cls ((pr hc).μ hc x y) hz) :
    KunE pr := by
  intro c n
  have offL : ∀ t : Idx c n, t.i ≠ t.a → Subsingleton ((P t.a).H t.i ⊗[K] (Q t.a').H t.j) := fun t h => by
    have := hP t.a t.i h
    exact tensor_sub_left _ _
  have offR : ∀ t : Idx c n, t.j ≠ t.a' → Subsingleton ((P t.a).H t.i ⊗[K] (Q t.a').H t.j) := fun t h => by
    have := hQ t.a' t.j h
    exact tensor_sub_right _ _
  by_cases hn : n = c
  · subst hn
    obtain ⟨e, he⟩ := hE n
    have hz : ∀ t, t ∉ Set.range (diag n) → Subsingleton ((P t.a).H t.i ⊗[K] (Q t.a').H t.j) := fun t ht => by
      refine offL t fun hi => ht ?_
      obtain ⟨a, i, a', j, ha, h⟩ := t
      simp only at hi
      subst hi
      obtain rfl : j = a' := by omega
      obtain rfl : j = n - i := by omega
      exact ⟨⟨i, by omega⟩, rfl⟩
    refine ⟨(sumPi (R := K) (fun t : Idx n n => (P t.a).H t.i ⊗[K] (Q t.a').H t.j) (diag n) (diag_inj n) hz).trans e, ?_⟩
    intro t x y hx hy hw
    by_cases ht : t ∈ Set.range (diag n)
    · obtain ⟨b, rfl⟩ := ht
      rw [LinearEquiv.trans_apply, sumPi_lof]
      exact he b (by omega) x y hx hy hw
    · have := hz t ht
      have hi : t.i ≠ t.a := fun hi => ht (by
        obtain ⟨a, i, a', j, ha, h⟩ := t
        simp only at hi
        subst hi
        obtain rfl : j = a' := by omega
        obtain rfl : j = n - i := by omega
        exact ⟨⟨i, by omega⟩, rfl⟩)
      have hB : x ∈ (P t.a).B t.i := by
        have := hP t.a t.i hi
        exact ((CrystallineSemistableComparison.P.cls_surj _ _).2.1 x hx).1 (Subsingleton.elim _ _)
      rw [Subsingleton.elim ((P t.a).cls x hx ⊗ₜ[K] (Q t.a').cls y hy) 0, map_zero, map_zero]
      exact (((CrystallineSemistableComparison.P.cls_surj _ _).2.1 _ hw).2 (CrystallineSemistableComparison.Auxff.memB_left (pr t.ha) t.h x hB y hy)).symm
  · have : Subsingleton ((T c).H n) := hT c n hn
    have hs : ∀ t : Idx c n, Subsingleton ((P t.a).H t.i ⊗[K] (Q t.a').H t.j) := fun t => by
      by_cases hi : t.i = t.a
      · refine offR t fun hj => hn ?_
        have := t.ha
        have := t.h
        omega
      · exact offL t hi
    have : Subsingleton (⨁ t : Idx c n, (P t.a).H t.i ⊗[K] (Q t.a').H t.j) := inferInstance
    exact ⟨LinearEquiv.ofSubsingleton _ _, fun _ _ _ _ _ _ => Subsingleton.elim _ _⟩

theorem xd_kun (E : XD K) (U₁ : ObjectProperty E.C₁) (U₂ : ObjectProperty E.C₂) (U₃ : ObjectProperty E.D)
    (h₁ : ∀ T, U₃ T → U₁ (E.L₁.obj T)) (h₂ : ∀ T, U₃ T → U₂ (E.L₂.obj T))
    (hP : ∀ a j, j ≠ a → Subsingleton ((CH.cx (U₁.ι ⋙ E.F₁ a)).H j))
    (hQ : ∀ a j, j ≠ a → Subsingleton ((CH.cx (U₂.ι ⋙ E.F₂ a)).H j))
    (hT : ∀ a j, j ≠ a → Subsingleton ((CH.cx (U₃.ι ⋙ E.F₃ a)).H j))
    (hE : ∀ c : ℕ, ∃ e : (∀ a : Fin (c + 1), TensorProduct K ((CH.cx (U₁.ι ⋙ E.F₁ a)).H a) ((CH.cx (U₂.ι ⋙ E.F₂ (c - a))).H (c - a))) ≃ₗ[K] (CH.cx (U₃.ι ⋙ E.F₃ c)).H c,
      ∀ (a : Fin (c + 1)) (hc : (a : ℕ) + (c - a) = c) (x : (CH.cx (U₁.ι ⋙ E.F₁ a)).X a) (y : (CH.cx (U₂.ι ⋙ E.F₂ (c - a))).X (c - a))
        (hx : (CH.cx (U₁.ι ⋙ E.F₁ a)).d a x = 0) (hy : (CH.cx (U₂.ι ⋙ E.F₂ (c - a))).d (c - a) y = 0)
        (hz : (CH.cx (U₃.ι ⋙ E.F₃ c)).d c ((E.pr U₁ U₂ U₃ h₁ h₂ hc).μ hc x y) = 0),
        e (Pi.single a ((CH.cx (U₁.ι ⋙ E.F₁ a)).cls x hx ⊗ₜ (CH.cx (U₂.ι ⋙ E.F₂ (c - a))).cls y hy)) =
          (CH.cx (U₃.ι ⋙ E.F₃ c)).cls ((E.pr U₁ U₂ U₃ h₁ h₂ hc).μ hc x y) hz) :
    E.Kun U₁ U₂ U₃ h₁ h₂ :=
  kunE_of_diag (P := fun a => CH.cx (U₁.ι ⋙ E.F₁ a)) (Q := fun a => CH.cx (U₂.ι ⋙ E.F₂ a)) (T := fun a => CH.cx (U₃.ι ⋙ E.F₃ a))
    (fun {a a' c} ha => E.pr U₁ U₂ U₃ h₁ h₂ ha) hP hQ hT hE

theorem cls_eq {R : Type} [CommRing R] (L : Cx.{w} R) {n : ℕ} {x y : L.X n} (e : x = y) (hx : L.d n x = 0) (hy : L.d n y = 0) :
    L.cls x hx = L.cls y hy := by
  subst e
  rfl

section
variable {X X' P : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K)) (q' : X' ⟶ Spec (CommRingCat.of K)) (p₁ : P ⟶ X) (p₂ : P ⟶ X')
    (hw : p₂ ≫ q' = p₁ ≫ q)

theorem hodge_pr_eq (U₁ : ObjectProperty (Thick (smFun X q))) (U₂ : ObjectProperty (Thick (smFun X' q')))
    (U₃ : ObjectProperty (Thick (smFun P (p₁ ≫ q))))
    (h₁ : ∀ T, U₃ T → U₁ ((smS p₁ rfl).G.obj T)) (h₂ : ∀ T, U₃ T → U₂ ((smS p₂ hw).G.obj T)) {a a' c i j n : ℕ}
    (ha : a + a' = c) (h : i + j = n) (x : CH.Cn (U₁.ι ⋙ G q a) i) (y : CH.Cn (U₂.ι ⋙ G q' a') j) :
    ((hodgeXD q q' p₁ p₂ hw).pr U₁ U₂ U₃ h₁ h₂ ha).μ h x y =
      cupU (p₁ ≫ q) U₃ ha h ((morV p₁ rfl a h₁).pullC i x) ((morV p₂ hw a' h₂).pullC j y) := rfl

end

set_option maxHeartbeats 400000 in

theorem kun_aff : SiteLaws → AffOm → KunAff → ∀ (K : Type) [Field K] [CharZero K] (X X' P : Scheme.{0}) (q : X ⟶ Spec (CommRingCat.of K)) (q' : X' ⟶ Spec (CommRingCat.of K)) (p₁ : P ⟶ X) (p₂ : P ⟶ X') (hP : IsPullback p₁ p₂ q q') (V : X.Opens) (V' : X'.Opens) (d d' : ℕ), Nonempty (Coord q V d) → Nonempty (Coord q' V' d') → ∀ (h₁ : ∀ T, inU (p₁ ≫ q) (p₁ ⁻¹ᵁ V ⊓ p₂ ⁻¹ᵁ V') T → inU q V ((hodgeXD q q' p₁ p₂ hP.w.symm).L₁.obj T)) (h₂ : ∀ T, inU (p₁ ≫ q) (p₁ ⁻¹ᵁ V ⊓ p₂ ⁻¹ᵁ V') T → inU q' V' ((hodgeXD q q' p₁ p₂ hP.w.symm).L₂.obj T)), (hodgeXD q q' p₁ p₂ hP.w.symm).Kun (inU q V) (inU q' V') (inU (p₁ ≫ q) (p₁ ⁻¹ᵁ V ⊓ p₂ ⁻¹ᵁ V')) h₁ h₂  := by
  intro _ hA hK K _ _ X X' P q q' p₁ p₂ hP V V' d d' hc hc' h₁ h₂
  obtain ⟨hZ, hE⟩ := hK K X X' P q q' p₁ p₂ hP V V' d d' hc hc'
  refine xd_kun (hodgeXD q q' p₁ p₂ hP.w.symm) _ _ _ h₁ h₂ ?_ ?_ ?_ ?_
  · exact fun a j hj => (hA K X q V d hc a).1 j hj
  · exact fun a j hj => (hA K X' q' V' d' hc' a).1 j hj
  · exact fun a j hj => (hA K P (p₁ ≫ q) _ (d + d') hZ a).1 j hj
  · intro c
    obtain ⟨e, he⟩ := hE c h₁ h₂
    refine ⟨e, fun a hc x y hx hy hz => ?_⟩
    have eq := hodge_pr_eq q q' p₁ p₂ hP.w.symm (inU q V) (inU q' V') (inU (p₁ ≫ q) (p₁ ⁻¹ᵁ V ⊓ p₂ ⁻¹ᵁ V')) h₁ h₂ hc hc x y
    have hz' : (CH.cx ((inU (p₁ ≫ q) (p₁ ⁻¹ᵁ V ⊓ p₂ ⁻¹ᵁ V')).ι ⋙ G (p₁ ≫ q) c)).d c (cupU (p₁ ≫ q) _ hc hc ((morV p₁ rfl a h₁).pullC a x) ((morV p₂ hP.w.symm (c - a) h₂).pullC (c - a) y)) = 0 := by
      rw [← eq]
      exact hz
    exact (he a hc x y hx hy hz').trans (cls_eq _ eq.symm _ _)

end GlobalTheory.CompanionTheory.KunGlue.Aff
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.KuennethSwap
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct DirectSum GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.Onto CrystallineSemistableComparison.Pb CrystallineSemistableComparison.HT GlobalTheory.CompanionTheory.KunGlue

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CompanionTheory.KunGlue

universe w

variable {K : Type} [Field K]

abbrev Idx.swap {c n : ℕ} (t : Idx c n) : Idx c n :=
  ⟨t.a', t.j, t.a, t.i, by have := t.ha; omega, by have := t.h; omega⟩

def swapSum (P Q : ℕ → Cx.{w} K) (c n : ℕ) :
    (⨁ t : Idx c n, (P t.a).H t.i ⊗[K] (Q t.a').H t.j) →ₗ[K]
      (⨁ t : Idx c n, (Q t.a).H t.i ⊗[K] (P t.a').H t.j) :=
  DirectSum.toModule K _ _ fun t =>
    ((-1 : ℤ) ^ (t.i * t.j)) •
      ((DirectSum.lof K _ (fun t : Idx c n => (Q t.a).H t.i ⊗[K] (P t.a').H t.j) t.swap).comp
        (TensorProduct.comm K ((P t.a).H t.i) ((Q t.a').H t.j)).toLinearMap)

theorem swapSum_lof (P Q : ℕ → Cx.{w} K) (c n : ℕ) (t : Idx c n) (u : (P t.a).H t.i) (v : (Q t.a').H t.j) :
    swapSum P Q c n (DirectSum.lof K _ (fun t : Idx c n => (P t.a).H t.i ⊗[K] (Q t.a').H t.j) t (u ⊗ₜ v)) =
      ((-1 : ℤ) ^ (t.i * t.j)) •
        DirectSum.lof K _ (fun t : Idx c n => (Q t.a).H t.i ⊗[K] (P t.a').H t.j) t.swap (v ⊗ₜ u) := by
  unfold swapSum
  rw [DirectSum.toModule_lof]
  rfl

theorem swapSum_swapSum (P Q : ℕ → Cx.{w} K) (c n : ℕ) (z) :
    swapSum Q P c n (swapSum P Q c n z) = z := by
  have key : (swapSum Q P c n).comp (swapSum P Q c n) = LinearMap.id := by
    refine DirectSum.linearMap_ext K fun t => TensorProduct.ext' fun u v => ?_
    simp only [LinearMap.comp_apply, LinearMap.id_apply, swapSum_lof, map_zsmul]
    have hs : ((-1 : ℤ) ^ (t.i * t.j)) * ((-1 : ℤ) ^ (t.swap.i * t.swap.j)) = 1 := by
      change ((-1 : ℤ) ^ (t.i * t.j)) * ((-1 : ℤ) ^ (t.j * t.i)) = 1
      rw [Nat.mul_comm t.j t.i, ← mul_pow]
      simp
    refine (congrArg (fun w => ((-1 : ℤ) ^ (t.i * t.j)) • w) (swapSum_lof Q P c n t.swap v u)).trans ?_
    dsimp only
    rw [smul_smul, hs, one_smul]
  exact LinearMap.congr_fun key z

theorem kunE_swap {P Q T : ℕ → Cx.{1} K} (pr : ∀ {a a' c : ℕ}, a + a' = c → CxPairing (P a) (Q a') (T c)) (h : KunE pr) :
    KunE (P := Q) (Q := P) (T := T) (fun {a a' c} ha => swapPr pr ha) := by
  intro c n
  obtain ⟨e, he⟩ := h c n
  let σ : (⨁ t : Idx c n, (Q t.a).H t.i ⊗[K] (P t.a').H t.j) ≃ₗ[K]
      (⨁ t : Idx c n, (P t.a).H t.i ⊗[K] (Q t.a').H t.j) :=
    LinearEquiv.ofLinear (swapSum Q P c n) (swapSum P Q c n)
      (LinearMap.ext fun z => swapSum_swapSum P Q c n z) (LinearMap.ext fun z => swapSum_swapSum Q P c n z)
  refine ⟨σ.trans e, fun t x y hx hy hz => ?_⟩
  have hz' : (T c).d n ((pr (show t.a' + t.a = c by have := t.ha; omega)).μ (show t.j + t.i = n by have := t.h; omega) y x) = 0 := by
    have e0 := (pr (show t.a' + t.a = c by have := t.ha; omega)).leib (show t.j + t.i = n by have := t.h; omega) y x
    rw [e0, hx, hy]
    simp
  have e1 := he t.swap y x hy hx hz'
  change e (swapSum Q P c n (DirectSum.lof K _ (fun t : Idx c n => (Q t.a).H t.i ⊗[K] (P t.a').H t.j) t
    ((Q t.a).cls x hx ⊗ₜ (P t.a').cls y hy))) = _
  rw [swapSum_lof, map_zsmul]
  refine (congrArg _ e1).trans ?_
  rfl

end GlobalTheory.CompanionTheory.KunGlue
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LamFamily
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false

open CategoryTheory Limits AlgebraicGeometry GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.Pb CrystallineSemistableComparison.HT CrystallineSemistableComparison.Onto

noncomputable section

namespace GlobalTheory.CompanionTheory.RelKill

section Fam
variable {K : Type} [CommRing K] {ι : Type} {a : ℕ}

theorem lam_family (hDW : DWedge) (hDL : DLog) (hFL : FormLaws) (A : Finset ι → Type) [∀ S, CommRing (A S)] [∀ S, Algebra K (A S)]
    {H₂ X₂ H₃ X₃ : Finset ι → Type*} [∀ S, AddCommGroup (H₂ S)] [∀ S, Module K (H₂ S)]
    [∀ S, AddCommGroup (X₂ S)] [∀ S, Module K (X₂ S)] [∀ S, AddCommGroup (H₃ S)] [∀ S, Module K (H₃ S)]
    [∀ S, AddCommGroup (X₃ S)] [∀ S, Module K (X₃ S)]
    (i₂ : ∀ S, H₂ S →ₗ[K] X₂ S) (i₃ : ∀ S, H₃ S →ₗ[K] X₃ S)
    (e₂ : ∀ S, S.Nonempty → (Om K (A S) a →ₗ[K] X₂ S)) (e₃ : ∀ S, S.Nonempty → (Om K (A S) (a + 1) →ₗ[K] X₃ S))
    (he₂ : ∀ S hS, Function.Bijective (e₂ S hS)) (hi₃ : ∀ S, S.Nonempty → Function.Injective (i₃ S))
    (I : ∀ S, Ideal (A S))
    (hr₂ : ∀ S hS ω, e₂ S hS ω ∈ LinearMap.range (i₂ S) ↔ ω ∈ relOm K (I S) a)
    (hr₃ : ∀ S hS ω, e₃ S hS ω ∈ LinearMap.range (i₃ S) ↔ ω ∈ relOm K (I S) (a + 1))
    (f : ∀ (α : ι) (S : Finset ι), α ∈ S → A S) (hI : ∀ α S hα, I S = Ideal.span {f α S hα})
    (hnz : ∀ α S hα (ω : Om K (A S) (a + 1)), f α S hα • ω = 0 → ω = 0) (c : ℤ)
    (φ : ∀ {S T : Finset ι}, S ⊆ T → (A S →ₐ[K] A T))
    (hφ : ∀ α {S T : Finset ι} (h : S ⊆ T) hα, φ h (f α S hα) = f α T (h hα))
    (ρ₂ : ∀ {S T : Finset ι}, S ⊆ T → (H₂ S →ₗ[K] H₂ T)) (ρ₃ : ∀ {S T : Finset ι}, S ⊆ T → (H₃ S →ₗ[K] H₃ T))
    (x₂ : ∀ {S T : Finset ι}, S ⊆ T → (X₂ S →ₗ[K] X₂ T)) (x₃ : ∀ {S T : Finset ι}, S ⊆ T → (X₃ S →ₗ[K] X₃ T))
    (hρ₂ : ∀ {S T : Finset ι} (h : S ⊆ T) y, i₂ T (ρ₂ h y) = x₂ h (i₂ S y))
    (hρ₃ : ∀ {S T : Finset ι} (h : S ⊆ T) y, i₃ T (ρ₃ h y) = x₃ h (i₃ S y))
    (hx₂ : ∀ {S T : Finset ι} (h : S ⊆ T) hS hT ω, x₂ h (e₂ S hS ω) = e₂ T hT (omMap (φ h) a ω))
    (hx₃ : ∀ {S T : Finset ι} (h : S ⊆ T) hS hT ω, x₃ h (e₃ S hS ω) = e₃ T hT (omMap (φ h) (a + 1) ω)) :
    ∃ lam : ∀ (α : ι) (S : Finset ι), α ∈ S → (H₂ S →ₗ[K] H₃ S),
      (∀ α {S T : Finset ι} (h : S ⊆ T) hS y, lam α T (h hS) (ρ₂ h y) = ρ₃ h (lam α S hS y)) ∧
      ∀ α S hα y ω η (w : Om K (A S) a →ₗ[A S] Om K (A S) (a + 1)),
        (∀ g₀ (g : Fin a → A S), w (form K g₀ g) = form K g₀ (Fin.cons (f α S hα) g)) →
        i₂ S y = e₂ S ⟨α, hα⟩ ω → f α S hα • η = w ω → i₃ S (lam α S hα y) = e₃ S ⟨α, hα⟩ (c • η) := by
  have key := fun (α : ι) (S : Finset ι) (hα : α ∈ S) =>
    lam_one hDW hDL hFL (i₂ S) (i₃ S) (e₂ S ⟨α, hα⟩) (e₃ S ⟨α, hα⟩) (he₂ S _) (hi₃ S ⟨α, hα⟩) (I S) (hr₂ S _)
      (hr₃ S _) (f α S hα) (hI α S hα) (hnz α S hα) c
  choose lam hlam using key
  refine ⟨lam, fun α S T h hα y => ?_, hlam⟩
  have hS : S.Nonempty := ⟨α, hα⟩
  have hT : T.Nonempty := ⟨α, h hα⟩
  refine hi₃ T hT ?_
  obtain ⟨ω, hω⟩ := (he₂ S hS).2 (i₂ S y)
  have hm : ω ∈ relOm K (Ideal.span {f α S hα}) a := by
    rw [← hI α S hα]
    exact (hr₂ S hS ω).1 ⟨y, hω.symm⟩
  obtain ⟨w, hw⟩ := hDW K (A S) a (f α S hα)
  obtain ⟨η, ⟨-, hη⟩, -⟩ := hDL K (A S) a (f α S hα) (hnz α S hα) w hw ω hm
  obtain ⟨w', hw'⟩ := hDW K (A T) a (f α T (h hα))
  have wm := wedge_map hFL (φ h) (f α S hα) w w' hw (by rw [hφ]; exact hw') ω
  have s1 := hlam α S hα y ω η w hw hω.symm hη
  have s2 := hlam α T (h hα) (ρ₂ h y) (omMap (φ h) a ω) (omMap (φ h) (a + 1) η) w' hw'
    (by rw [hρ₂, ← hω, hx₂ h hS hT]) (by
      rw [← wm, ← hη, ((hFL K (A S) (A T) (a + 1)).2 (φ h)).2.1, hφ])
  rw [s2, hρ₃, s1, hx₃ h hS hT, map_zsmul (omMap (φ h) (a + 1))]

end Fam

section Kill
variable {K : Type} [CommRing K] {C : Type 1} [Category.{0} C]
  {F₁ F₂ F₃ : C ⥤ ModuleCat.{0} K} {ι : Type} [DecidableEq ι]

theorem cov_kill (hCK : ConeKill) (hCD : CovDesc) (hDW : DWedge) (hDL : DLog) (hFL : FormLaws)
    (P : CH.Pairing F₁ F₂ F₃) (U : ι → ObjectProperty C)
    (hU : ∀ α, Cosieve (U α)) {Q : ObjectProperty C} (hQ : Cosieve Q) (a : ℕ)
    (h1 : (covSy F₂ U hQ).One a) (h2 : (covSy F₃ U hQ).One (a + 1))
    (r : CH.Cn F₁ 2) (hr : CH.d F₁ 2 r = 0) (β : ∀ α, CH.Cn ((U α).ι ⋙ F₁) 1)
    (hβ : ∀ α, CH.d _ 1 (β α) = (CH.Mor.restrict F₁ (U α).ι).pullC 2 r)
    (A : Finset ι → Type) [∀ S, CommRing (A S)] [∀ S, Algebra K (A S)]
    (e₂ : ∀ S, S.Nonempty → (Om K (A S) a →ₗ[K] HU F₂ (capU U S) a))
    (e₃ : ∀ S, S.Nonempty → (Om K (A S) (a + 1) →ₗ[K] HU F₃ (capU U S) (a + 1)))
    (he₂ : ∀ S hS, Function.Bijective (e₂ S hS))
    (hi₃ : ∀ S, S.Nonempty → Function.Injective ((incl F₃ (capU U S) hQ).mapH (a + 1)))
    (I : ∀ S, Ideal (A S))
    (hr₂ : ∀ S hS ω, e₂ S hS ω ∈ LinearMap.range ((incl F₂ (capU U S) hQ).mapH a) ↔ ω ∈ relOm K (I S) a)
    (hr₃ : ∀ S hS ω, e₃ S hS ω ∈ LinearMap.range ((incl F₃ (capU U S) hQ).mapH (a + 1)) ↔ ω ∈ relOm K (I S) (a + 1))
    (f : ∀ (α : ι) (S : Finset ι), α ∈ S → A S) (hI : ∀ α S hα, I S = Ideal.span {f α S hα})
    (hnz : ∀ α S hα (ω : Om K (A S) (a + 1)), f α S hα • ω = 0 → ω = 0) (c : ℤ)
    (φ : ∀ {S T : Finset ι}, S ⊆ T → (A S →ₐ[K] A T))
    (hφ : ∀ α {S T : Finset ι} (h : S ⊆ T) hα, φ h (f α S hα) = f α T (h hα))
    (k : ∀ {S T : Finset ι}, S ⊆ T → capU U T ≤ capU U S)
    (hx₂ : ∀ {S T : Finset ι} (h : S ⊆ T) hS hT ω,
      (resU F₂ (k h)).pull a (e₂ S hS ω) = e₂ T hT (omMap (φ h) a ω))
    (hx₃ : ∀ {S T : Finset ι} (h : S ⊆ T) hS hT ω,
      (resU F₃ (k h)).pull (a + 1) (e₃ S hS ω) = e₃ T hT (omMap (φ h) (a + 1) ω))
    (u : ∀ (α α' : ι) (S : Finset ι), α ∈ S → α' ∈ S → (A S)ˣ)
    (huf : ∀ α α' S hα hα', f α S hα = u α α' S hα hα' * f α' S hα')
    (hcup : ∀ α α' S hα hα' (y : CH.Cn ((capU U S).ι ⋙ F₂) a) (hy : CH.d _ a y = 0) (ω : Om K (A S) a)
      (w : Om K (A S) a →ₗ[A S] Om K (A S) (a + 1)),
      (∀ g₀ (g : Fin a → A S), w (form K g₀ g) = form K g₀ (Fin.cons (u α α' S hα hα' : A S) g)) →
      (CH.cx _).cls y hy = e₂ S ⟨α, hα⟩ ω → ∀ hz,
      (CH.cx ((capU U S).ι ⋙ F₃)).cls ((pairU P (capU U S)).cupC (Nat.add_comm 1 a)
        ((resU F₁ (capU_le U S hα)).pullC 1 (β α) - (resU F₁ (capU_le U S hα')).pullC 1 (β α')) y) hz =
        e₃ S ⟨α, hα⟩ (c • ((↑(u α α' S hα hα')⁻¹ : A S) • w ω)))
    (n : ℕ) (x : ((covSy F₂ U hQ).K ∅).X n) (hx : ((covSy F₂ U hQ).K ∅).d n x = 0) :
    rhoS P U hQ r ∅ n x ∈ ((covSy F₃ U hQ).K ∅).B (n + 2) := by
  obtain ⟨lam, lam_nat, lam_spec⟩ := lam_family (K := K) (a := a) hDW hDL hFL A
    (H₂ := fun S => ((covSy F₂ U hQ).K S).H a) (X₂ := fun S => HU F₂ (capU U S) a)
    (H₃ := fun S => ((covSy F₃ U hQ).K S).H (a + 1)) (X₃ := fun S => HU F₃ (capU U S) (a + 1))
    (fun S => (incl F₂ (capU U S) hQ).mapH a) (fun S => (incl F₃ (capU U S) hQ).mapH (a + 1))
    e₂ e₃ he₂ hi₃ I hr₂ hr₃ f hI hnz c φ hφ
    (fun h => ((covSy F₂ U hQ).res h).mapH a) (fun h => ((covSy F₃ U hQ).res h).mapH (a + 1))
    (fun h => (resU F₂ (k h)).pull a) (fun h => (resU F₃ (k h)).pull (a + 1))
    (fun h y => by
      obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ y
      rfl)
    (fun h y => by
      obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ y
      rfl)
    hx₂ hx₃
  refine cone_apply hCK hCD P U hU hQ a h1 h2 r hr β hβ lam (fun α S T h hS x => lam_nat α h hS x) ?_ n x hx
  intro α α' S hα hα' x hx hz
  have hS : S.Nonempty := ⟨α, hα⟩
  refine hi₃ S hS ?_
  have hy : CH.d _ a x.1 = 0 := congrArg Subtype.val hx
  obtain ⟨ω, hω⟩ := (he₂ S hS).2 ((CH.cx _).cls x.1 hy)
  have hi : (incl F₂ (capU U S) hQ).mapH a (((covSy F₂ U hQ).K S).cls x hx) = e₂ S hS ω := hω.symm
  have hm : ω ∈ relOm K (I S) a := (hr₂ S hS ω).1 ⟨_, hi⟩
  have hm₁ : ω ∈ relOm K (Ideal.span {f α S hα}) a := hI α S hα ▸ hm
  have hm₂ : ω ∈ relOm K (Ideal.span {f α' S hα'}) a := hI α' S hα' ▸ hm
  obtain ⟨w, hw⟩ := hDW K (A S) a (f α S hα)
  obtain ⟨w', hw'⟩ := hDW K (A S) a (f α' S hα')
  obtain ⟨wu, hwu⟩ := hDW K (A S) a (u α α' S hα hα' : A S)
  obtain ⟨η, ⟨-, hη⟩, -⟩ := hDL K (A S) a (f α S hα) (hnz α S hα) w hw ω hm₁
  obtain ⟨η', ⟨-, hη'⟩, -⟩ := hDL K (A S) a (f α' S hα') (hnz α' S hα') w' hw' ω hm₂
  have d := eta_diff hFL (u α α' S hα hα') (f α S hα) (f α' S hα') (huf α α' S hα hα') (hnz α S hα) w w' wu hw hw' hwu
    ω η η' hη hη'
  have s1 := lam_spec α S hα _ ω η w hw hi hη
  have s2 := lam_spec α' S hα' _ ω η' w' hw' hi hη'
  have hz' : CH.d ((capU U S).ι ⋙ F₃) (a + 1) ((pairU P (capU U S)).cupC (Nat.add_comm 1 a)
      ((resU F₁ (capU_le U S hα)).pullC 1 (β α) - (resU F₁ (capU_le U S hα')).pullC 1 (β α')) x.1) = 0 := by
    rw [map_sub, LinearMap.sub_apply]
    exact congrArg Subtype.val hz
  have s3 := hcup α α' S hα hα' x.1 hy ω wu hwu hω.symm hz'
  have e1 : (incl F₃ (capU U S) hQ).mapH (a + 1) (((covSy F₃ U hQ).K S).cls
      (etaS P U hQ β α S hα a x - etaS P U hQ β α' S hα' a x) hz) = (CH.cx ((capU U S).ι ⋙ F₃)).cls
      ((pairU P (capU U S)).cupC (Nat.add_comm 1 a)
        ((resU F₁ (capU_le U S hα)).pullC 1 (β α) - (resU F₁ (capU_le U S hα')).pullC 1 (β α')) x.1) hz' := by
    refine congrArg Submodule.Quotient.mk (Subtype.ext ?_)
    exact (LinearMap.congr_fun (map_sub ((pairU P (capU U S)).cupC (Nat.add_comm 1 a)) _ _) x.1).symm
  have e2 := (map_sub ((incl F₃ (capU U S) hQ).mapH (a + 1)) (lam α S hα (((covSy F₂ U hQ).K S).cls x hx))
    (lam α' S hα' (((covSy F₂ U hQ).K S).cls x hx))).trans (congrArg₂ (· - ·) s1 s2)
  refine (e1.trans s3).trans (Eq.trans ?_ e2.symm)
  have e3 : (e₃ S ⟨α', hα'⟩ : _) = e₃ S ⟨α, hα⟩ := rfl
  rw [e3, ← map_sub, ← smul_sub, d]

end Kill

end GlobalTheory.CompanionTheory.RelKill
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LevelLatticeBase
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open GroundTheory.PAdicHodge Formalism.Per6 DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb CrystallineSemistableComparison.Pb.Lat

namespace GlobalTheory.CompanionTheory.LatCBase

theorem dividedPowerFiltration_anti {B : Type} [CommRing B] {J : Ideal B} (δ : DividedPowers J) {k s : ℕ} (h : k ≤ s) :
    pdP δ s ≤ pdP δ k := by
  unfold CrystallineSemistableComparison.Pb.pdP
  refine Ideal.span_mono ?_
  rintro z ⟨L, hL, hs, rfl⟩
  exact ⟨L, hL, h.trans hs, rfl⟩

theorem latBase_lev : ∀ {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)} {M : ℕ}
    (h : LevHyp l K M) (k : ℕ), 1 ≤ k → ∀ s, k ≤ s → LatBase (lev h k).γ l s := by
  intro l hl K M h k hk s hks
  have H := GlobalTheory.CompanionTheory.LatCHyp.hyp_k l k hk
  show CrystallineSemistableComparison.Pb.LatBase (CrystallineSemistableComparison.Pb.Lat.γ (CrystallineSemistableComparison.Pb.Lat.fk l k) (CrystallineSemistableComparison.xi0 l) l M (h.hc k)) l s
  refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact le_bot_iff.mp ((dividedPowerFiltration_anti _ hks).trans
      (GlobalTheory.CompanionTheory.LatNil.dividedPowerFiltration_eq_bot _ _ l M k H (h.hc k)).le)
  · exact GlobalTheory.CompanionTheory.Lat.quot_pdP_no_torsion _ _ l M k H (h.hc k)
  · exact GlobalTheory.CompanionTheory.LatticeUnit.natCast_dvd_pow _ _ l M k H
  · exact GlobalTheory.CompanionTheory.LatFG.dividedPowerFiltration_fg _ _ l M k H (h.hc k)
  · exact GlobalTheory.CompanionTheory.LatPrime.I_isPrime _ _ l M k H
  · exact GlobalTheory.CompanionTheory.LatVal.val _ _ l M k H
  · exact GlobalTheory.CompanionTheory.Lat.pow_mem_span_sup_I _ _ l M k H
  · exact GlobalTheory.CompanionTheory.LatCpl.isAdicComplete_A M H
  · exact GlobalTheory.CompanionTheory.LatClosed.closed _ _ l M k H (h.hc k)

end GlobalTheory.CompanionTheory.LatCBase
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LevelToBEqZeroIffTPowDvdStatement
section
open GroundTheory.PAdicHodge Formalism.Per6 DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb CrystallineSemistableComparison.Pb.Lat
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.level_toB_eq_zero_iff_t_pow_dvd : ∀ {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)} {M : ℕ} (h : LevHyp l K M) (k : ℕ), ∀ x : (per l K).P, (lev h k).toB x = 0 ↔ ∃ y : (per l K).P, (x : (per l K).B) = (per l K).tB ^ k * y := by
  first | exact @GlobalTheory.CompanionTheory.LatC.lev_toB_ker | exact GlobalTheory.CompanionTheory.LatC.lev_toB_ker | (intros; apply GlobalTheory.CompanionTheory.LatC.lev_toB_ker <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LevelToBGaloisEquivariantStatement
section
open GroundTheory.PAdicHodge Formalism.Per6 DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb CrystallineSemistableComparison.Pb.Lat
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.level_toB_galois_equivariant : ∀ {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)} {M : ℕ} (h : LevHyp l K M) (k : ℕ), ∀ (g : K.fixingSubgroup) (x y : (per l K).P), (per l K).σ g x = y → (lev h k).σB g ((lev h k).toB x) = (lev h k).toB y := by
  first | exact @GlobalTheory.CompanionTheory.LatC.sigmaB_toB | exact GlobalTheory.CompanionTheory.LatC.sigmaB_toB | (intros; apply GlobalTheory.CompanionTheory.LatC.sigmaB_toB <;> assumption)
end

