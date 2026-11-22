import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.DiagonalPullbacks.ProjectiveBundleFormulaTorsion
import Development.EtaleCohomology.EtaleTrace.LRingPf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0628
import Development.EtaleCohomology.EtaleTrace.Bundle0007

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.DiagonalPullbacks.PPBLim
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC LateralTheory.EtaleTrace CrystallineSemistableComparison CrystallineSemistableComparison.Onto UpperTheory.Gal.KunnethLefschetz UpperTheory.Gal.KunnethLefschetz.Di
open scoped TensorProduct

namespace UpperTheory.Gal.KunnethLefschetz.Di.PBLimPf

open LRingPf

private theorem pi_bc {R A P : Type*} [CommRing R] [CommRing A] [Algebra R A] {ι : Type*} [Fintype ι] [DecidableEq ι]
    {M : ι → Type*} [∀ j, AddCommGroup (M j)] [∀ j, Module R (M j)] [AddCommGroup P] [Module R P]
    (Ψ : (∀ j, M j) →ₗ[R] P) (hΨ : Function.Bijective Ψ) (φ : (∀ j, A ⊗[R] M j) →ₗ[A] A ⊗[R] P)
    (h : ∀ a : ∀ j, M j, φ (fun j => (1 : A) ⊗ₜ a j) = (1 : A) ⊗ₜ Ψ a) : Function.Bijective φ := by
  let e : (∀ j, M j) ≃ₗ[R] P := LinearEquiv.ofBijective Ψ hΨ
  let b : A ⊗[R] (∀ j, M j) ≃ₗ[A] A ⊗[R] P := LinearEquiv.baseChange R A _ _ e
  let p : A ⊗[R] (∀ j, M j) ≃ₗ[A] ∀ j, A ⊗[R] M j := TensorProduct.piRight R A A M
  have key : φ ∘ₗ p.toLinearMap = b.toLinearMap := by
    apply ext1
    intro x
    have hp : p ((1 : A) ⊗ₜ x) = fun j => (1 : A) ⊗ₜ x j := by
      funext j
      simp [p, TensorProduct.piRight_apply]
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, hp, h]
    simp [b, e]
  have hφ : ∀ u, φ u = b (p.symm u) := by
    intro u
    have := LinearMap.congr_fun key (p.symm u)
    simpa using this
  have : (φ : (∀ j, A ⊗[R] M j) → A ⊗[R] P) = b ∘ p.symm := funext hφ
  rw [this]
  exact b.bijective.comp p.symm.bijective

variable {l : ℕ} [Fact l.Prime]

private def powL (hB : A11) {E : Scheme.{0}} (hl : IsUnit (l : Γ(E, ⊤))) (v : Hl l (sch.obj E) 2 0) :
    ∀ j : ℕ, Hl l (sch.obj E) (2 * (j : ℤ)) 0
  | 0 => z0 l hB E hl
  | j + 1 => cupL l (sch.obj E) (by push_cast; ring) hB (powL hB hl v j) v

private theorem powL_lvl (hB : A11) {E : Scheme.{0}} (hl : IsUnit (l : Γ(E, ⊤))) (v : Hl l (sch.obj E) 2 0) (j k : ℕ) :
    (powL hB hl v j).1 k = pow0 (l ^ k) (v.1 k) j := by
  induction j with
  | zero => rfl
  | succ j ih =>
    have h : 2 * (j : ℤ) + 2 = 2 * ((j + 1 : ℕ) : ℤ) := by push_cast; ring
    exact congrArg (fun t => cup0 (l ^ k) h t (v.1 k)) ih

private theorem power_zero_reduction_compat (hB : A11) {E : Scheme.{0}} (hl : IsUnit (l : Γ(E, ⊤))) (v : Hl l (sch.obj E) 2 0) (j k : ℕ) :
    red (l ^ (k + 1)) (l ^ k) _ _ 0 (pow0 (l ^ (k + 1)) (v.1 (k + 1)) j) = pow0 (l ^ k) (v.1 k) j := by
  rw [← powL_lvl hB hl, ← powL_lvl hB hl]
  exact (powL hB hl v j).2 k

private def Psi (hB : A11) {E Z : Scheme.{0}} (r : E ⟶ Z) (hl : IsUnit (l : Γ(E, ⊤))) (v : Hl l (sch.obj E) 2 0) (N : ℕ) (n : ℤ) :
    (∀ j : Fin N, Hl l (sch.obj Z) (n - 2 * ((j : ℕ) : ℤ)) 0) →ₗ[ℤ_[l]] Hl l (sch.obj E) n 0 :=
  ∑ j : Fin N, ((cupL l (sch.obj E) (sub_add_cancel n (2 * ((j : ℕ) : ℤ))) hB).flip (powL hB hl v j)).comp
    ((pullHl l (sch.map r) _ 0).comp (LinearMap.proj j))

private theorem Psi_apply (hB : A11) {E Z : Scheme.{0}} (r : E ⟶ Z) (hl : IsUnit (l : Γ(E, ⊤))) (v : Hl l (sch.obj E) 2 0)
    (N : ℕ) (n : ℤ) (a : ∀ j : Fin N, Hl l (sch.obj Z) (n - 2 * ((j : ℕ) : ℤ)) 0) :
    Psi hB r hl v N n a = ∑ j : Fin N, cupL l (sch.obj E) (sub_add_cancel n (2 * ((j : ℕ) : ℤ))) hB
      (pullHl l (sch.map r) _ 0 (a j)) (powL hB hl v j) := by
  simp [Psi, LinearMap.sum_apply]

private theorem Psi_lvl (hB : A11) {E Z : Scheme.{0}} (r : E ⟶ Z) (hl : IsUnit (l : Γ(E, ⊤))) (v : Hl l (sch.obj E) 2 0)
    (N : ℕ) (n : ℤ) (a : ∀ j : Fin N, Hl l (sch.obj Z) (n - 2 * ((j : ℕ) : ℤ)) 0) (k : ℕ) :
    (Psi hB r hl v N n a).1 k = ∑ j : Fin N, (cup0 (l ^ k) (sub_add_cancel n _)
      (pull _ (sch.map r) _ _ (show Ht (l ^ k) _ _ 0 from (a j).1 k)) (pow0 (l ^ k) (v.1 k) j) : Ht (l ^ k) _ n 0) := by
  rw [Psi_apply, Submodule.coe_sum, Finset.sum_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← powL_lvl hB hl]
  rfl

private theorem lvl_red (hB : A11) {E Z : Scheme.{0}} (r : E ⟶ Z) (hl : IsUnit (l : Γ(E, ⊤))) (v : Hl l (sch.obj E) 2 0)
    {m n : ℤ} (j : ℕ) (h : m + 2 * (j : ℤ) = n) (k : ℕ) (a : Ht (l ^ (k + 1)) (sch.obj Z) m 0) :
    red (l ^ (k + 1)) (l ^ k) _ n 0 (cup0 (l ^ (k + 1)) h (pull _ (sch.map r) _ _ a) (pow0 (l ^ (k + 1)) (v.1 (k + 1)) j)) =
      cup0 (l ^ k) h (pull _ (sch.map r) _ _ (red (l ^ (k + 1)) (l ^ k) _ m 0 a)) (pow0 (l ^ k) (v.1 k) j) := by
  have e := red_cc h hB (l ^ (k + 1)) (dvd_succ l k) (pull _ (sch.map r) _ _ a) (pow0 (l ^ (k + 1)) (v.1 (k + 1)) j)
  rw [power_zero_reduction_compat hB hl, ← pull_red] at e
  exact e

private theorem Psi_bij (hB : A11) {E Z : Scheme.{0}} (r : E ⟶ Z) (hl : IsUnit (l : Γ(E, ⊤))) (v : Hl l (sch.obj E) 2 0)
    (N : ℕ) (n : ℤ) (hv : ∀ k, ProjectiveBundleFormulaTorsion (l ^ k) N r (v.1 k)) : Function.Bijective (Psi hB r hl v N n) := by
  constructor
  · intro a b hab
    funext j
    refine Subtype.ext (funext fun k => ?_)
    have h := congrArg (fun y : Hl l (sch.obj E) n 0 => y.1 k) hab
    simp only [Psi_lvl] at h
    exact congrFun ((hv k n).1 h) j
  · intro y
    choose c hc using fun k => (hv k n).2 (y.1 k)
    have compat : ∀ k j, red (l ^ (k + 1)) (l ^ k) _ _ 0 (c (k + 1) j) = c k j := by
      intro k
      refine congrFun ((hv k n).1 ?_)
      refine Eq.trans ?_ (hc k).symm
      refine Eq.trans ?_ (y.2 k)
      rw [← hc (k + 1), map_sum]
      exact Finset.sum_congr rfl fun j _ => (lvl_red hB r hl v j _ k (c (k + 1) j)).symm
    refine ⟨fun j => ⟨fun k => c k j, fun k => compat k j⟩, Subtype.ext (funext fun k => ?_)⟩
    rw [Psi_lvl]
    exact hc k

private theorem powV_eq (hB : A11) {E : Scheme.{0}} (hl : IsUnit (l : Γ(E, ⊤))) (v : Hl l (sch.obj E) 2 0) (j : ℕ) :
    powV l (toV v) j = toV (powL hB hl v j) := by
  induction j with
  | zero => exact oneV_eq l hB E hl
  | succ j ih =>
    change cupV l E _ (powV l (toV v) j) (toV v) = _
    rw [ih, cupV_eq l hB, cupQ_tmul]
    rfl

end UpperTheory.Gal.KunnethLefschetz.Di.PBLimPf

open UpperTheory.Gal.KunnethLefschetz.Di.PBLimPf LRingPf in
theorem UpperTheory.Gal.KunnethLefschetz.Di.pBLim_holds :
    UpperTheory.Gal.KunnethLefschetz.Di.PBLim := by
  intro hI l _ _ N E Z r hl v hv n
  have hB := hI.a11
  have hE : IsUnit (l : Γ(E, ⊤)) := unit_pull l r hl
  let φ : (∀ j : Fin N, V l Z (n - 2 * ((j : ℕ) : ℤ))) →ₗ[ℚ_[l]] V l E n :=
    ∑ j : Fin N, ((cupV l E (sub_add_cancel n (2 * ((j : ℕ) : ℤ)))).flip (powV l (toV v) j)).comp
      ((pb l r _).comp (LinearMap.proj j))
  have hφ : ∀ a, φ a = ∑ j : Fin N, cupV l E (sub_add_cancel n _) (pb l r _ (a j)) (powV l (toV v) j) := by
    intro a
    simp [φ, LinearMap.sum_apply]
  have hb : Function.Bijective φ := by
    refine pi_bc (Psi hB r hE v N n) (Psi_bij hB r hE v N n hv) φ fun a => ?_
    rw [hφ, Psi_apply, TensorProduct.tmul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [powV_eq hB hE, pb_tmul, cupV_eq l hB, cupQ_tmul]
  have : (fun a : ∀ j : Fin N, V l Z (n - 2 * ((j : ℕ) : ℤ)) =>
      ∑ j : Fin N, cupV l E (sub_add_cancel n _) (pb l r _ (a j)) (powV l (toV v) j)) = φ :=
    funext fun a => (hφ a).symm
  rw [this]
  exact hb
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.DiagonalPullbacks.PPBQOf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC LateralTheory.EtaleTrace CrystallineSemistableComparison CrystallineSemistableComparison.Onto UpperTheory.Gal.KunnethLefschetz UpperTheory.Gal.KunnethLefschetz.Di
open scoped TensorProduct

namespace UpperTheory.Gal.KunnethLefschetz.Di.PPBQOf

variable {l : ℕ} [Fact l.Prime]

private def tr {X : Scheme.{0}} {a b : ℤ} (h : a = b) (x : V l X a) : V l X b := h ▸ x

private lemma tr_tr {X : Scheme.{0}} {a b c : ℤ} (h : a = b) (h' : b = c) (x : V l X a) :
    tr h' (tr h x) = tr (h.trans h') x := by
  subst h; subst h'; rfl

private lemma tr_self {X : Scheme.{0}} {a : ℤ} (h : a = a) (x : V l X a) : tr h x = x := rfl

private lemma tr_eq_zero {X : Scheme.{0}} {a b : ℤ} (h : a = b) (x : V l X a) (hx : tr h x = 0) : x = 0 := by
  subst h; exact hx

private lemma t0 (hR : Ring l) {E Z : Scheme.{0}} (r : E ⟶ Z) (hE : IsUnit (l : Γ(E, ⊤))) (ξ : V l E 2)
    {a n : ℤ} {j : ℕ} (hj : j = 0) (h : a + 2 * (j : ℤ) = n) (ha : a = n) (u : V l Z a) :
    cupV l E h (pb l r a u) (powV l ξ j) = pb l r n (tr ha u) := by
  subst hj; subst ha
  exact hR.mul_one E hE _ _

private lemma pow_one (hR : Ring l) {E : Scheme.{0}} (hE : IsUnit (l : Γ(E, ⊤))) (ξ : V l E 2) :
    (powV l ξ 1 : V l E 2) = ξ :=
  hR.one_mul E hE 2 ξ

private lemma t1 (hR : Ring l) {E Z : Scheme.{0}} (r : E ⟶ Z) (hE : IsUnit (l : Γ(E, ⊤))) (ξ : V l E 2)
    {a : ℤ} {j : ℕ} (hj : j = 1) (h : a + 2 * (j : ℤ) = 2) (ha : a = 0) (u : V l Z a) :
    cupV l E h (pb l r a u) (powV l ξ j) = cupV l E (zero_add 2) (pb l r 0 (tr ha u)) ξ := by
  subst hj; subst ha
  exact congrArg (cupV l E (zero_add 2) (pb l r 0 u)) (pow_one hR hE ξ)

private lemma tneg (hneg : ∀ (X : Scheme.{0}) (n : ℤ), n < 0 → Subsingleton (V l X n)) {E Z : Scheme.{0}} (r : E ⟶ Z)
    {a m n : ℤ} (ha : a < 0) (h : a + m = n) (u : V l Z a) (w : V l E m) :
    cupV l E h (pb l r a u) w = 0 := by
  haveI := hneg Z a ha
  rw [Subsingleton.elim u 0, map_zero, map_zero, LinearMap.zero_apply]

private lemma sum2 {A : Type*} [AddCommMonoid A] (M : ℕ) (f : Fin (M + 2) → A)
    (h : ∀ j : Fin (M + 2), 2 ≤ (j : ℕ) → f j = 0) : ∑ j, f j = f 0 + f 1 := by
  rw [Fin.sum_univ_succ, Fin.sum_univ_succ, Fin.succ_zero_eq_one]
  have hz : ∑ i : Fin M, f i.succ.succ = 0 := Finset.sum_eq_zero fun i _ => h _ (by simp)
  rw [hz, add_zero]

end UpperTheory.Gal.KunnethLefschetz.Di.PPBQOf

open UpperTheory.Gal.KunnethLefschetz.Di.PPBQOf in
theorem UpperTheory.Gal.KunnethLefschetz.Di.pBQOf_holds :
    UpperTheory.Gal.KunnethLefschetz.Di.PBQOf := by
  intro l _ hR hneg N hN E Z r hZ ξ hPBV
  have hE := LateralTheory.EtaleTrace.LRingPf.unit_pull l r hZ
  obtain ⟨M, rfl⟩ : ∃ M, N = M + 2 := ⟨N - 2, by omega⟩
  have key : ∀ (n : ℤ) (a : ∀ j : Fin (M + 2), V l Z (n - 2 * ((j : ℕ) : ℤ))), n ≤ 3 →
      (∑ j : Fin (M + 2), cupV l E (sub_add_cancel n (2 * ((j : ℕ) : ℤ)))
          (pb l r (n - 2 * ((j : ℕ) : ℤ)) (a j)) (powV l ξ (j : ℕ))) =
        cupV l E (sub_add_cancel n (2 * (((0 : Fin (M + 2)) : ℕ) : ℤ)))
          (pb l r (n - 2 * (((0 : Fin (M + 2)) : ℕ) : ℤ)) (a 0)) (powV l ξ ((0 : Fin (M + 2)) : ℕ)) +
        cupV l E (sub_add_cancel n (2 * (((1 : Fin (M + 2)) : ℕ) : ℤ)))
          (pb l r (n - 2 * (((1 : Fin (M + 2)) : ℕ) : ℤ)) (a 1)) (powV l ξ ((1 : Fin (M + 2)) : ℕ)) :=
    fun n a hn => sum2 M _ fun j hj => tneg hneg r (by omega) _ _ _
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro n
    rw [eq_top_iff]
    rintro z -
    obtain ⟨a, ha⟩ := (hPBV n).2 z
    rw [← ha]
    exact Submodule.sum_mem _ fun j _ =>
      Submodule.subset_span ⟨(j : ℕ), n - 2 * ((j : ℕ) : ℤ), sub_add_cancel _ _, a j, rfl⟩
  · intro z
    obtain ⟨a, ha⟩ := (hPBV 0).2 z
    have hz := ha.symm.trans (key 0 a (by norm_num))
    rw [tneg (a := 0 - 2 * (((1 : Fin (M + 2)) : ℕ) : ℤ)) hneg r (by norm_num [Fin.val_one]) _ _ _, add_zero,
      t0 (j := ((0 : Fin (M + 2)) : ℕ)) (a := 0 - 2 * (((0 : Fin (M + 2)) : ℕ) : ℤ)) (n := 0)
        hR r hE ξ (by simp) _ (by simp)] at hz
    exact ⟨_, hz⟩
  · intro z
    obtain ⟨a, ha⟩ := (hPBV 2).2 z
    have hz := ha.symm.trans (key 2 a (by norm_num))
    rw [t0 (j := ((0 : Fin (M + 2)) : ℕ)) (a := 2 - 2 * (((0 : Fin (M + 2)) : ℕ) : ℤ)) (n := 2)
        hR r hE ξ (by simp) _ (by simp),
      t1 (j := ((1 : Fin (M + 2)) : ℕ)) (a := 2 - 2 * (((1 : Fin (M + 2)) : ℕ) : ℤ))
        hR r hE ξ (by simp [Fin.val_one]) _ (by norm_num [Fin.val_one])] at hz
    exact ⟨_, _, hz⟩
  · intro u v huv
    let a : ∀ j : Fin (M + 2), V l Z (2 - 2 * ((j : ℕ) : ℤ)) := fun j =>
      if h0 : (j : ℕ) = 0 then tr (by rw [h0]; norm_num) u
      else if h1 : (j : ℕ) = 1 then tr (by rw [h1]; norm_num) v else 0
    have ha0 : a 0 = tr (by simp) u := by simp [a]
    have ha1 : a 1 = tr (by norm_num [Fin.val_one]) v := by simp [a, Fin.val_one]
    have hzero : a = 0 := by
      apply (hPBV 2).1
      beta_reduce
      rw [key 2 a (by norm_num), key 2 0 (by norm_num)]
      simp only [Pi.zero_apply, map_zero, LinearMap.zero_apply, add_zero]
      rw [ha0, ha1,
        t0 (j := ((0 : Fin (M + 2)) : ℕ)) (a := 2 - 2 * (((0 : Fin (M + 2)) : ℕ) : ℤ)) (n := 2)
          hR r hE ξ (by simp) _ (by simp),
        t1 (j := ((1 : Fin (M + 2)) : ℕ)) (a := 2 - 2 * (((1 : Fin (M + 2)) : ℕ) : ℤ))
          hR r hE ξ (by simp [Fin.val_one]) _ (by norm_num [Fin.val_one]),
        tr_tr, tr_tr, tr_self, tr_self]
      exact huv
    have h1 := congrFun hzero 1
    rw [ha1] at h1
    exact tr_eq_zero _ v h1
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.DiagonalPullbacks.PPowRoot
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC LateralTheory.EtaleTrace LateralTheory.EtaleTrace.LRingPf

namespace UpperTheory.Gal.KunnethLefschetz.Di

private theorem inv_root {q : ℕ} {E : Scheme.{0}} (ζ : Prim q Γ(E, ⊤)) : Inv q (sch.obj E) := by
  intro U hU
  obtain ⟨y⟩ := hU
  let y' : U ⟶ E := y
  simpa using ζ.2.1.map y'.appTop.hom

private theorem cast_eq_iff {q : ℕ} {E : Spc} {n i n' i' : ℤ} (h1 : n = n') (h2 : i = i') (x : Ht q E n i) (y : Ht q E n' i') :
    Ht.cast h1 h2 x = y ↔ x = Ht.cast h1.symm h2.symm y := by
  subst h1 h2; rfl

private theorem rootClass_cast {q : ℕ} {E : Scheme.{0}} (ζ : Prim q Γ(E, ⊤)) {i i' : ℤ} (h : i = i') (h0 : (0 : ℤ) = 0) :
    rootClass i' ζ = Ht.cast h0 h (rootClass i ζ) := by
  subst h; rfl

private theorem swap0 (h6 : DivisorRingCompatibility) {q : ℕ} [NeZero q] {E : Spc} {m k s : ℤ} (r : Ht q E 0 s) (b : Ht q E m k) :
    cup q r b = Ht.cast (by ring) (by ring) (cup q b r) := by
  rw [(h6 q E).2.2 r b]
  simp

private theorem four (h6 : DivisorRingCompatibility) {q : ℕ} [NeZero q] {E : Spc} {n m i k s t : ℤ} (a : Ht q E n i) (r : Ht q E 0 s)
    (b : Ht q E m k) (c : Ht q E 0 t) :
    cup q (cup q a r) (cup q b c) = Ht.cast (by ring) (by ring) (cup q (cup q a b) (cup q r c)) := by
  have e1 : cup q r (cup q b c) = Ht.cast (by ring) (by ring) (cup q b (cup q r c)) := by
    have e2 := (cast_eq_iff _ _ _ _).1 ((h6 q E).2.1 r b c).symm
    rw [e2, swap0 h6 r b, cup_cast_left, (h6 q E).2.1 b r c, LRingPf.cast_cast, LRingPf.cast_cast]
  rw [(h6 q E).2.1 a r (cup q b c), e1, cup_cast_right, LRingPf.cast_cast, (h6 q E).2.1 a b (cup q r c),
    LRingPf.cast_cast]

private theorem base (h6 : DivisorRingCompatibility) {q : ℕ} [NeZero q] {E : Scheme.{0}} (ζ : Prim q Γ(E, ⊤)) {n i : ℤ} (hn : 0 = n) (hi : 0 = i)
    (h0 : (0 : ℤ) = 0) (h1 : n + 0 = n) (h2 : i + -i = 0) :
    Ht.cast hn h0 (one q (sch.obj E)) = Ht.cast h1 h2 (cup q (Ht.cast hn hi (one q (sch.obj E))) (rootClass (-i) ζ)) := by
  subst hn hi
  have hr : rootClass (-(0 : ℤ)) ζ = Ht.cast h0 (neg_zero.symm : (0 : ℤ) = -0) (one q (sch.obj E)) := by
    rw [rootClass_cast ζ (neg_zero.symm : (0 : ℤ) = -0) h0, ((GlobalTheory.T.tateTwistCup_unit_and_primitiveRoot_classes q).2 E ζ 0 0).2]
  rw [hr, cup_cast_left, cup_cast_right, LRingPf.cast_cast, LRingPf.cast_cast, (h6 q _).1 (inv_root ζ) (one q (sch.obj E)),
    LRingPf.cast_cast]

theorem powRoot_holds : PowRoot := by
  intro hI q _ E ζ x j
  have h6 := hI.a6ring
  induction j with
  | zero =>
    exact base h6 ζ (n := 2 * ((0 : ℕ) : ℤ)) (i := ((0 : ℕ) : ℤ)) (by simp) (by simp) (Eq.refl 0) _ _
  | succ j ih =>
    have e : pow0 q (untw q x (rootClass (-1) ζ)) (j + 1) =
      cup0 q (by push_cast; ring) (pow0 q (untw q x (rootClass (-1) ζ)) j) (untw q x (rootClass (-1) ζ)) := rfl
    rw [e, ih]
    unfold cup0 untw
    rw [cup_cast_left, cup_cast_right, LRingPf.cast_cast, LRingPf.cast_cast, four h6, ((GlobalTheory.T.tateTwistCup_unit_and_primitiveRoot_classes q).2 E ζ _ _).1,
      cup_cast_right, LRingPf.cast_cast, cpow_succ, cup_cast_left,
      rootClass_cast ζ (show -(j : ℤ) + -1 = -((j + 1 : ℕ) : ℤ) by push_cast; ring) (Eq.refl 0), cup_cast_right,
      LRingPf.cast_cast, LRingPf.cast_cast, LRingPf.cast_cast]

end UpperTheory.Gal.KunnethLefschetz.Di
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.DiagonalPullbacks.UntwZero
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC LateralTheory.EtaleTrace CrystallineSemistableComparison CrystallineSemistableComparison.Onto
open scoped TensorProduct

namespace UpperTheory.Gal.KunnethLefschetz.Di

structure Steps : Prop where
  ring : RingL
  geoPB : GeoPB
  geoM : GeoM
  c1BC : FirstChernClassBaseChange
  rootNat : RootNat
  powRoot : PowRoot
  untw : Untw
  lim : PBLim
  pbq : PBQOf
  sq : DiagSq
  clear : Clear
  blowBC : G.BlowBC
  blowE : G.BlowE
  pbe : G.PBE

theorem neg_sub (hI : In) (l : ℕ) [Fact l.Prime] (X : Scheme.{0}) (n : ℤ) (hn : n < 0) : Subsingleton (V l X n) := by
  have h : Subsingleton (Hl l (sch.obj X) n 0) :=
    ⟨fun a b => Subtype.ext (funext fun j => ((hI.a9 (ZMod (l ^ j)) (tw (l ^ j) 0)).1 (sch.obj X) n hn).elim _ _)⟩
  refine subsingleton_of_forall_eq 0 fun z => ?_
  induction z using TensorProduct.induction_on with
  | zero => rfl
  | add a b ha hb => rw [ha, hb, add_zero]
  | tmul a x => rw [Subsingleton.elim x 0, TensorProduct.tmul_zero]

theorem pull_untw (hI : In) (q : ℕ) [NeZero q] {E X : Scheme.{0}} (j : E ⟶ X) (x : Ht q (sch.obj X) 2 1)
    (ρ : Ht q (sch.obj X) 0 (-1)) :
    pull _ (sch.map j) _ 2 (untw q x ρ) = untw q (pull _ (sch.map j) _ 2 x) (pull _ (sch.map j) _ 0 ρ) := by
  have key : ∀ (n i : ℤ) (hn : 2 + 0 = n) (hi : 1 + -1 = i), pull _ (sch.map j) (tw q i) n ((cup q x ρ).cast hn hi) =
      (cup q (pull _ (sch.map j) _ 2 x) (pull _ (sch.map j) _ 0 ρ)).cast hn hi := by
    rintro _ _ rfl rfl
    exact (hI.a6nat q).1 (sch.map j) x ρ
  exact key _ _ _ _

theorem untw_zero (q : ℕ) {X : Scheme.{0}} (ρ : Ht q (sch.obj X) 0 (-1)) : untw q 0 ρ = 0 := by
  have key : ∀ (n i : ℤ) (hn : 2 + 0 = n) (hi : 1 + -1 = i),
      (cup q (0 : Ht q (sch.obj X) 2 1) ρ).cast hn hi = 0 := by
    rintro _ _ rfl rfl
    rw [map_zero]
    rfl
  exact key _ _ _ _

theorem Steps.core (H : Steps) (hI : In) (hQ : QDiag) (l : ℕ) [Fact l.Prime] (k : Type) [Field k] [IsAlgClosed k]
    (hl : (l : k) ≠ 0) (d : ℕ) (hd : 1 ≤ d) {X P W : Scheme.{0}} (p : X ⟶ S k) (p₁ p₂ : P ⟶ X) (Δ : X ⟶ P)
    (hP : IsPullback p₁ p₂ p p) (h₁ : Δ ≫ p₁ = 𝟙 _) (h₂ : Δ ≫ p₂ = 𝟙 _) (hp : SP (d + 1) p) (hpr : IsProj p) (π : W ⟶ P)
    (hπ : IsProper π) (D : CrystallineSemistableComparison.E.LineData W) (hB : Nonempty (Blow (p₁ ≫ p) Δ π D (d + 1)))
    (ζ : ∀ n, Prim (l ^ n) Γ(S k, ⊤)) (x : ∀ n, Ht (l ^ n) (sch.obj W) 2 1) (hx : ∀ n, IsFirstChernClassOfLineBundle (l ^ n) D (x n))
    (v : Hl l (sch.obj W) 2 0)
    (hv : ∀ n, v.1 n = Di.untw (l ^ n) (x n) (rootClass (-1) ((ζ n).map (π ≫ p₁ ≫ p).appTop.hom))) :
    DiagL l d p₁ p₂ π v := by
  have hR := H.ring hI l
  have hlX : IsUnit (l : Γ(X, ⊤)) := LPdCut.unit_of p (isUnit_iff_ne_zero.2 hl)
  have hs := hp.2
  have hs1 : SmoothOfRelativeDimension (d + 1) p₁ :=
    haveI := smoothOfRelativeDimension_isStableUnderBaseChange.{0} (d + 1)
    MorphismProperty.of_isPullback (P := @SmoothOfRelativeDimension (d + 1)) hP.flip hs
  have hpb := IsPullback.of_hasPullback π Δ
  obtain ⟨hi, hr⟩ := H.blowE k (p₁ ≫ p) Δ π D d (d + 1) hB inferInstance hπ _ _ hpb
  have hcl := hi.cl
  let U : W.Opens := ⟨(Set.range (pullback.fst π Δ))ᶜ, (pullback.fst π Δ).isClosedEmbedding.isClosed_range.isOpen_compl⟩
  have hU : Off (pullback.fst π Δ) U := rfl
  have hE : ∀ n, PBT (l ^ n) (d + 1) (pullback.snd π Δ) (pull _ (sch.map (pullback.fst π Δ)) _ 2 (x n)) ∧
      pull _ (sch.map U.ι) _ 2 (x n) = 0 := fun n => by
    have : NeZero (l ^ n) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
    obtain ⟨L, hL, hxL⟩ := hx n
    have h := H.pbe hI (l ^ n) k (by rw [Nat.cast_pow]; exact (IsUnit.mk0 _ hl).pow _) (p₁ ≫ p) Δ π D (d + 1) hB _ _ hpb
      L hL (x n) hxL
    exact ⟨h.1, h.2 U hU⟩
  have hcomp : pullback.fst π Δ ≫ π ≫ p₁ ≫ p = pullback.snd π Δ ≫ p := by
    rw [pullback.condition_assoc, reassoc_of% h₁]
  have h0 : pb l U.ι 2 (toV v) = 0 := by
    have : pullHl l (sch.map U.ι) 2 0 v = 0 := Subtype.ext (funext fun n => by
      have : NeZero (l ^ n) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
      change pull _ (sch.map U.ι) _ 2 (v.1 n) = 0
      rw [hv n, pull_untw hI, (hE n).2, untw_zero])
    rw [LRingPf.pb_tmul, this, TensorProduct.tmul_zero]
  have hPB : PBQ l (pullback.snd π Δ) (pb l (pullback.fst π Δ) 2 (toV v)) := by
    rw [LRingPf.pb_tmul]
    refine H.pbq l hR (neg_sub hI l) (d + 1) (by omega) _ hlX _ (H.lim hI l hR (d + 1) _ hlX _ fun n => ?_)
    have : NeZero (l ^ n) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
    have h := H.untw hI H.rootNat H.powRoot (l ^ n) (d + 1) _ ((ζ n).map p.appTop.hom) _ (hE n).1
    have e : ((ζ n).map p.appTop.hom).map (pullback.snd π Δ).appTop.hom =
        ((ζ n).map (π ≫ p₁ ≫ p).appTop.hom).map (pullback.fst π Δ).appTop.hom := Subtype.ext (by
      change (p.appTop ≫ (pullback.snd π Δ).appTop).hom (ζ n).1 = ((π ≫ p₁ ≫ p).appTop ≫ (pullback.fst π Δ).appTop).hom (ζ n).1
      rw [← Scheme.Hom.comp_appTop, ← Scheme.Hom.comp_appTop, hcomp])
    rw [e, ← H.rootNat, ← pull_untw hI, ← hv n] at h
    exact h
  exact H.clear hI l hR d p₁ p₂ π hlX v
    (H.sq hQ l k hl hR d p p₁ p₂ Δ hP h₁ h₂ hp hpr π _ _ _ hpb hi hr U hU _ h0 hPB)

set_option maxHeartbeats 1000000 in
theorem Steps.diagEt2 (H : Steps) (hI : In) (hQ : QDiag) : DiagEt2 := by
  intro l _ K _ M d hd hM hs T r v hv
  obtain ⟨D', τ, L, x, hBC, hL, hx, hvx⟩ := hv
  have hl : (l : PadicAlgCl l) ≠ 0 := Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero
  obtain ⟨g1, g2⟩ := H.geoPB K (PadicAlgCl l)
  obtain ⟨m1, m2, m3⟩ := H.geoM l K
  obtain ⟨hp, hpr⟩ := m1 M (d + 1) hM hs
  have hP := g2 M.q T.P.q _ _ (Model.genMap_q T.p₁ T.h₁) (Model.genMap_q T.p₂ T.h₂) (m3 M T.P T.p₁ T.p₂ T.h₁ T.h₂ T.prod)
  have hΔ := g1 M.q T.P.q _ (Model.genMap_q T.Δ T.hΔ)
  have hπ := g1 T.Y.q T.P.q _ (Model.genMap_q T.π T.hπ)
  have hB := H.blowBC K (PadicAlgCl l) (algebraMap K _) _ _ _ _ _ _ _ _ _ _ _ (IsPullback.of_hasPullback T.P.q _) hΔ hπ T.blow
  have e1 : GlobalTheory.Et.geomMap (PadicAlgCl l) T.P.q _ (Model.genMap_q T.p₁ T.h₁) ≫ pullback.snd M.q _ = pullback.snd T.P.q _ :=
    pullback.lift_snd _ _ _
  have e2 : GlobalTheory.Et.geomMap (PadicAlgCl l) T.Y.q _ (Model.genMap_q T.π T.hπ) ≫ pullback.snd T.P.q _ = pullback.snd T.Y.q _ :=
    pullback.lift_snd _ _ _
  have hsec : ∀ (u : T.P.X ⟶ M.X) (hu : u ≫ M.p = T.P.p), T.Δ ≫ u = 𝟙 _ →
      GlobalTheory.Et.geomMap (PadicAlgCl l) M.q _ (Model.genMap_q T.Δ T.hΔ) ≫
        GlobalTheory.Et.geomMap (PadicAlgCl l) T.P.q _ (Model.genMap_q u hu) = 𝟙 _ := fun u hu h => by
    have h' : Model.genMap T.Δ T.hΔ ≫ Model.genMap u hu = 𝟙 _ := by
      apply pullback.hom_ext
      · simp only [Model.genMap, Category.assoc, pullback.lift_fst, pullback.lift_fst_assoc, h, Category.comp_id, Category.id_comp]
      · simp only [Model.genMap, Category.assoc, pullback.lift_snd, Category.id_comp]
    apply pullback.hom_ext
    · simp only [GlobalTheory.Et.geomMap, Category.assoc, pullback.lift_fst, pullback.lift_fst_assoc, h', Category.comp_id, Category.id_comp]
    · simp only [GlobalTheory.Et.geomMap, Category.assoc, pullback.lift_snd, Category.id_comp]
  have hpro : IsProper (GlobalTheory.Et.geomMap (PadicAlgCl l) T.Y.q _ (Model.genMap_q T.π T.hπ)) :=
    MorphismProperty.of_isPullback (P := @IsProper) hπ (m2 T.Y T.P T.π T.hπ T.smY T.smP)
  rw [← e1] at hB
  exact H.core hI hQ l (PadicAlgCl l) hl d hd _ _ _ _ hP (hsec _ _ T.Δ₁) (hsec _ _ T.Δ₂) hp hpr _ hpro _ hB
    (fun n => (r.ρ n).map (CrystallineSemistableComparison.E.toΓ _)) x
    (fun n => by
      have : NeZero (l ^ n) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
      exact H.c1BC hI (l ^ n) T.D _ _ D' τ hBC
        (LPdCut.unit_of (pullback.snd T.Y.q _) (by rw [Nat.cast_pow]; exact (IsUnit.mk0 _ hl).pow _)) (x n) ⟨L, hL, hx n⟩)
    v (fun n => by rw [e1, e2]; exact hvx n)

end UpperTheory.Gal.KunnethLefschetz.Di
end
end

