import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.NLeA
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AlgebraMapConeRing
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ToConeSurjective
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.InclStd
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.MapHComp
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.MemBoundariesZeroIff
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ConeSectionRestriction.GeoDefs

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ChartSingletonBaseChange
section
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.CompanionTheory.SurjectionOntoH4.ThetaOne
open CrystallineSemistableComparison.Onto GlobalTheory.CompanionTheory.SurjectionOntoH4

open TensorProduct in

theorem isBaseChange_of_presentation {B A P Q ι : Type} [CommRing B] [CommRing A] [CommRing P] [CommRing Q]
    [Algebra B A] [Algebra B P] [Algebra A Q] [Algebra B Q] [IsScalarTower B A Q]
    (θ : P →ₐ[B] Q) (u : ι → Q) (v : ι → P) (k : ι) (b : ι → B)
    (hv : ∀ j, θ (v j) = u j)
    (hsurj : Function.Surjective (MvPolynomial.aeval (R := A) (S₁ := Q) u))
    (hker : RingHom.ker (MvPolynomial.aeval (R := A) (S₁ := Q) u).toRingHom =
      Ideal.span (insert (MvPolynomial.X k - 1) (Set.range fun j =>
        MvPolynomial.C (algebraMap B A (b j)) - MvPolynomial.C (algebraMap B A (b k)) * MvPolynomial.X j)))
    (hvk : v k = 1) (hb : ∀ j, algebraMap B P (b j) = algebraMap B P (b k) * v j)
    (hadj : Algebra.adjoin B (Set.range v) = ⊤) :
    IsBaseChange A θ.toLinearMap := by
  let f : MvPolynomial ι A →ₐ[A] Q := MvPolynomial.aeval u
  let g : MvPolynomial ι A →ₐ[A] A ⊗[B] P := MvPolynomial.aeval fun j => (1 : A) ⊗ₜ[B] v j
  have key : ∀ c : B, (algebraMap B A c) ⊗ₜ[B] (1 : P) = (1 : A) ⊗ₜ[B] algebraMap B P c := by
    intro c
    rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]
  have hle : RingHom.ker f.toRingHom ≤ RingHom.ker g.toRingHom := by
    change RingHom.ker (MvPolynomial.aeval (R := A) (S₁ := Q) u).toRingHom ≤ _
    rw [hker]
    refine Ideal.span_le.2 ?_
    rintro _ (rfl | ⟨j, rfl⟩)
    · change g _ = 0
      simp [g, hvk, Algebra.TensorProduct.one_def]
    · change g _ = 0
      have e : g (MvPolynomial.C (algebraMap B A (b j)) - MvPolynomial.C (algebraMap B A (b k)) * MvPolynomial.X j) =
          (algebraMap B A (b j)) ⊗ₜ[B] (1 : P) - ((algebraMap B A (b k)) ⊗ₜ[B] (1 : P)) * ((1 : A) ⊗ₜ[B] v j) := by
        simp [g, Algebra.TensorProduct.algebraMap_apply]
      rw [e, key, key, Algebra.TensorProduct.tmul_mul_tmul, one_mul, ← hb, sub_self]
  have hmem : ∀ p ∈ RingHom.ker f, g p = 0 := fun p hp => hle hp
  let h : Q →ₐ[A] A ⊗[B] P :=
    (Ideal.Quotient.liftₐ (RingHom.ker f) g hmem).comp (Ideal.quotientKerAlgEquivOfSurjective hsurj).symm.toAlgHom
  have hh : ∀ p, h (f p) = g p := by
    intro p
    have e : (Ideal.quotientKerAlgEquivOfSurjective (f := f) hsurj).symm (f p) = Ideal.Quotient.mk _ p := by
      rw [AlgEquiv.symm_apply_eq]
      rfl
    change Ideal.Quotient.liftₐ (RingHom.ker f) g hmem ((Ideal.quotientKerAlgEquivOfSurjective (f := f) hsurj).symm (f p)) = _
    rw [e]
    rfl
  let L : A ⊗[B] P →ₐ[A] Q := Algebra.TensorProduct.lift (Algebra.ofId A Q) θ fun _ _ => Commute.all _ _
  have hL1 : ∀ y, L ((1 : A) ⊗ₜ[B] y) = θ y := by
    intro y
    simp [L]
  have hLg : L.comp g = f := by
    apply MvPolynomial.algHom_ext
    intro j
    simp [g, f, hL1, hv]
  have hLh : L.comp h = AlgHom.id A Q := by
    refine AlgHom.ext fun r => ?_
    obtain ⟨p, rfl⟩ := hsurj r
    change L (h (f p)) = f p
    rw [hh]
    exact DFunLike.congr_fun hLg p
  have hhL : h.comp L = AlgHom.id A (A ⊗[B] P) := by
    apply Algebra.TensorProduct.ext
    · refine AlgHom.ext fun a => ?_
      have := (h.comp L).commutes a
      simpa [Algebra.TensorProduct.algebraMap_apply] using this
    · refine AlgHom.ext_of_adjoin_eq_top hadj ?_
      rintro _ ⟨j, rfl⟩
      change h (L ((1 : A) ⊗ₜ[B] v j)) = (1 : A) ⊗ₜ[B] v j
      have e : u j = f (MvPolynomial.X j) := by simp [f]
      rw [hL1, hv, e, hh]
      simp [g]
  let eq : A ⊗[B] P ≃ₐ[A] Q := AlgEquiv.ofAlgHom L h hLh hhL
  exact IsBaseChange.of_equiv eq.toLinearEquiv fun x => hL1 x

theorem mon_eq_one {K : Type} [Field K] {n d : ℕ} {M : AddSubmonoid (Gam n d)} {g : Gam n d} (hg : g ∈ M) (h : g = 0) :
    mon K g hg = 1 := by
  subst h
  rfl

theorem mon_congr {K : Type} [Field K] {n d : ℕ} {M : AddSubmonoid (Gam n d)} {g g' : Gam n d} (hg : g ∈ M) (hg' : g' ∈ M)
    (h : g = g') : mon K g hg = mon K g' hg' := by
  subst h
  rfl

theorem theta_one {K : Type} [Field K] {n d : ℕ} {A : Type} [CommRing A] [Algebra K A] (C : ChartRings K A n d) (k : Fin d) :
    ∃ (θ : R0 K n d {k} →ₐ[K] C.R {k}) (hθ : ∀ b, θ (poly n K {k} b) = toR C {k} (phi C b)),
      (∀ j, θ (mon K (ratE k j) (ratE_mem (Finset.mem_singleton_self k) j)) = C.u {k} k (Finset.mem_singleton_self k) j) ∧
        IsBaseChange (Aa C) (thetaLin C θ hθ) := by
  have hk : k ∈ ({k} : Finset (Fin d)) := Finset.mem_singleton_self k
  let u : Fin d → Rb C {k} := C.u {k} k hk
  have hphi : ∀ j, algebraMap (Bp K n d) (Aa C) (MvPolynomial.X (Sum.inr j)) = C.t j := by
    intro j
    change phi C _ = _
    simp [phi]
  have hsurj : Function.Surjective (MvPolynomial.aeval (R := Aa C) (S₁ := Rb C {k}) u) := C.chart_surj k
  have hker : RingHom.ker (MvPolynomial.aeval (R := Aa C) (S₁ := Rb C {k}) u).toRingHom =
      Ideal.span (insert (MvPolynomial.X k - 1) (Set.range fun j =>
        MvPolynomial.C (algebraMap (Bp K n d) (Aa C) (MvPolynomial.X (Sum.inr j))) -
          MvPolynomial.C (algebraMap (Bp K n d) (Aa C) (MvPolynomial.X (Sum.inr k))) * MvPolynomial.X j)) := by
    simp only [hphi]
    exact C.chart_ker k
  have huk : u k = 1 := by
    have hm : (MvPolynomial.X k - 1 : MvPolynomial (Fin d) (Aa C)) ∈
        RingHom.ker (MvPolynomial.aeval (R := Aa C) (S₁ := Rb C {k}) u).toRingHom := by
      rw [hker]
      exact Ideal.subset_span (Set.mem_insert _ _)
    have h0 : (MvPolynomial.aeval (R := Aa C) (S₁ := Rb C {k}) u) (MvPolynomial.X k - 1) = 0 := hm
    simpa [sub_eq_zero] using h0
  have htu : ∀ j, toR C {k} (C.t j) = toR C {k} (C.t k) * C.u {k} k hk j := fun j => C.t_eq {k} k hk j
  let w : E n d → C.R {k} := Sum.elim (fun l => toR C {k} (C.x l))
    (fun j => if j = k then toR C {k} (C.t k) else C.u {k} k hk j)
  let Ψ : Bp K n d ≃ₐ[K] R0 K n d {k} := AlgEquiv.ofBijective _ (ChartBij.chart_bijective (K := K) (n := n) k)
  let θ : R0 K n d {k} →ₐ[K] C.R {k} := (MvPolynomial.aeval w).comp Ψ.symm.toAlgHom
  have hθw : ∀ e, θ (mon K (wv k e) (wv_mem hk e)) = w e := by
    intro e
    have h1 : mon K (wv k e) (wv_mem hk e) = Ψ (MvPolynomial.X e) := by simp [Ψ]
    change MvPolynomial.aeval w (Ψ.symm _) = _
    rw [h1, AlgEquiv.symm_apply_apply, MvPolynomial.aeval_X]
  have hθr : ∀ j, θ (mon K (ratE k j) (ratE_mem hk j)) = C.u {k} k hk j := by
    intro j
    by_cases h : j = k
    · subst h
      rw [mon_eq_one _ (by simp [ratE]), map_one]
      exact huk.symm
    · have h1 := hθw (Sum.inr j)
      have h2 : wv k (Sum.inr j) = (ratE k j : Gam n d) := by simp [wv, h]
      rw [mon_congr _ (ratE_mem hk j) h2] at h1
      simpa [w, h] using h1
  have hθ : ∀ b, θ (poly n K {k} b) = toR C {k} (phi C b) := by
    have e : θ.comp (poly n K {k}) = (toR C {k}).comp (phi C) := by
      apply MvPolynomial.algHom_ext
      rintro (l | j)
      · have h1 := hθw (Sum.inl l)
        simpa [poly_X, phi, w, wv] using h1
      · have h1 := hθw (Sum.inr k)
        have h2 : wv k (Sum.inr k) = (oneE (Sum.inr k) : Gam n d) := by simp [wv]
        rw [mon_congr _ (oneE_mem {k} _) h2] at h1
        have h3 : mon K (oneE (Sum.inr j) : Gam n d) (oneE_mem {k} _) =
            mon K (oneE (Sum.inr k)) (oneE_mem {k} _) * mon K (ratE k j) (ratE_mem hk j) := by
          rw [mon_mul]
          exact mon_congr _ _ (by simp [ratE])
        simp only [AlgHom.comp_apply, poly_X, phi, MvPolynomial.aeval_X, Sum.elim_inr]
        rw [h3, map_mul, h1, hθr, htu j]
        simp [w]
    exact fun b => DFunLike.congr_fun e b
  refine ⟨θ, hθ, hθr, ?_⟩
  let θ' : R0 K n d {k} →ₐ[Bp K n d] Rb C {k} := { θ.toRingHom with commutes' := fun b => hθ b }
  have hadj : Algebra.adjoin (Bp K n d) (Set.range fun j => mon K (ratE k j) (ratE_mem hk j) : Set (R0 K n d {k})) = ⊤ := by
    rw [eq_top_iff]
    rintro y -
    obtain ⟨p, rfl⟩ := (ChartBij.chart_bijective (K := K) (n := n) k).2 y
    induction p using MvPolynomial.induction_on with
    | C c =>
      have : MvPolynomial.aeval (fun e : E n d => mon K (wv k e) (wv_mem hk e)) (MvPolynomial.C c : Bp K n d) =
          algebraMap (Bp K n d) (R0 K n d {k}) (MvPolynomial.C c) := by
        rw [algebraMap_cone_ring]
        simp [poly]
      rw [this]
      exact Subalgebra.algebraMap_mem _ _
    | add p q hp hq => rw [map_add]; exact Subalgebra.add_mem _ hp hq
    | mul_X p e hp =>
      rw [map_mul]
      refine Subalgebra.mul_mem _ hp ?_
      rw [MvPolynomial.aeval_X]
      have hpoly : ∀ e' : E n d, mon K (oneE e') (oneE_mem {k} e') ∈
          Algebra.adjoin (Bp K n d) (Set.range fun j => mon K (ratE k j) (ratE_mem hk j) : Set (R0 K n d {k})) := by
        intro e'
        rw [← poly_X, ← algebraMap_cone_ring]
        exact Subalgebra.algebraMap_mem _ _
      rcases e with l | j
      · exact hpoly _
      · by_cases h : j = k
        · subst h
          rw [mon_congr _ (oneE_mem {j} _) (by simp [wv] : wv j (Sum.inr j) = (oneE (Sum.inr j) : Gam n d))]
          exact hpoly _
        · rw [mon_congr _ (ratE_mem hk j) (by simp [wv, h] : wv k (Sum.inr j) = (ratE k j : Gam n d))]
          exact Algebra.subset_adjoin ⟨j, rfl⟩
  have hbase := isBaseChange_of_presentation (B := Bp K n d) (A := Aa C) (P := R0 K n d {k}) (Q := Rb C {k}) θ' u
    (fun j => mon K (ratE k j) (ratE_mem hk j)) k (fun j => MvPolynomial.X (Sum.inr j)) hθr hsurj hker
    (mon_eq_one _ (by simp [ratE]))
    (fun j => by
      simp only [algebraMap_cone_ring, poly_X]
      rw [mon_mul]
      exact mon_congr _ _ (by simp [ratE]))
    hadj
  exact hbase

end GlobalTheory.CompanionTheory.SurjectionOntoH4.ThetaOne
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CohomologyVanishingAlongIdealFiltration
section
set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb

noncomputable section

namespace GlobalTheory.CompanionTheory.TowerEnd

open GlobalTheory.CatH (face toLast)

variable {R : Type} [CommRing R] {C : Type 1} [Category.{0} C] {A : C ⥤ CommAlgCat.{0} R}

abbrev Q (A : C ⥤ CommAlgCat.{0} R) (j : ℕ) : Type 1 := CH.Cn (CH.modF A) j

abbrev dQ (A : C ⥤ CommAlgCat.{0} R) (j : ℕ) : Q A j →ₗ[R] Q A (j + 1) := CH.d (CH.modF A) j

abbrev val {j : ℕ} (x : Q A j) (s : ComposableArrows C j) : A.obj (s.obj (Fin.last j)) := x s

def Vals (a : IdF A) {j : ℕ} (x : Q A j) : Prop := ∀ s, val x s ∈ a.S (s.obj (Fin.last j))

theorem dQ_apply {j : ℕ} (x : Q A j) (s : ComposableArrows C (j + 1)) :
    val (dQ A j x) s = ∑ i : Fin (j + 2), (-1 : ℤ) ^ (i : ℕ) • (A.map (toLast i s)).hom (val x (face i s)) := rfl

theorem Vals.sub {a : IdF A} {j : ℕ} {x y : Q A j} (hx : Vals a x) (hy : Vals a y) : Vals a (x - y) :=
  fun s => (a.S _).sub_mem (hx s) (hy s)

theorem Vals.dQ {a : IdF A} {j : ℕ} {x : Q A j} (hx : Vals a x) : Vals a (dQ A j x) := fun s => by
  rw [dQ_apply]
  exact Submodule.sum_mem _ fun i _ => (a.S _).toAddSubgroup.zsmul_mem (a.map_mem _ (hx _)) _

def cl (a b : IdF A) {j : ℕ} (x : Q A j) (hx : Vals a x) : CH.Cn (sq a b) j :=
  fun s => sqMk a b (val x s) (hx s)

theorem cl_val (a b : IdF A) {j : ℕ} (x : Q A j) (hx : Vals a x) (s : ComposableArrows C j) :
    (show sqM a b _ from cl a b x hx s).1 = Ideal.Quotient.mk _ (val x s) := rfl

theorem cl_surj (a b : IdF A) {j : ℕ} (f : CH.Cn (sq a b) j) : ∃ (x : Q A j) (hx : Vals a x), cl a b x hx = f := by
  have h : ∀ s : ComposableArrows C j, ∃ x : A.obj (s.obj (Fin.last j)), ∃ hx : x ∈ a.S _, sqMk a b x hx = f s := by
    intro s
    obtain ⟨y, hy, e⟩ := (Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective).1 (show sqM a b _ from f s).2
    exact ⟨y, hy, Subtype.ext e⟩
  choose x hx e using h
  exact ⟨x, hx, funext e⟩

theorem cl_eq_zero (a b : IdF A) {j : ℕ} {x : Q A j} {hx : Vals a x} (h : cl a b x hx = 0) : Vals b x := fun s => by
  have h1 := congrArg (fun g : CH.Cn (sq a b) j => (show sqM a b _ from g s).1) h
  exact Ideal.Quotient.eq_zero_iff_mem.1 h1

theorem d_cl (a b : IdF A) {j : ℕ} (x : Q A j) (hx : Vals a x) :
    CH.d (sq a b) j (cl a b x hx) = cl a b (dQ A j x) hx.dQ := by
  funext s
  apply Subtype.ext
  change Subtype.val (∑ i : Fin (j + 2), (-1 : ℤ) ^ (i : ℕ) • (sqMap a b (toLast i s)) (sqMk a b (val x (face i s)) (hx _)) :
    sqM a b _) = Ideal.Quotient.mk _ (∑ i : Fin (j + 2), (-1 : ℤ) ^ (i : ℕ) • (A.map (toLast i s)).hom (val x (face i s)))
  rw [map_sum, Submodule.coe_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_zsmul]
  rfl

theorem cl_sub (a b : IdF A) {j : ℕ} {x y : Q A j} (hx : Vals a x) (hy : Vals a y) :
    cl a b (x - y) (hx.sub hy) = cl a b x hx - cl a b y hy := by
  funext s
  apply Subtype.ext
  exact map_sub (Ideal.Quotient.mk _) _ _

theorem d_cl_zero (a b : IdF A) {j : ℕ} {z : Q A j} (hz : Vals a z) (hd : dQ A j z = 0) :
    CH.d (sq a b) j (cl a b z hz) = 0 := by
  rw [d_cl]
  funext s
  apply Subtype.ext
  change Ideal.Quotient.mk _ (val (dQ A j z) s) = 0
  rw [hd]
  exact map_zero (Ideal.Quotient.mk _)

theorem step_zero (a b : IdF A) (h : Subsingleton (CH.H (sq a b) 0)) {z : Q A 0} (hz : Vals a z)
    (hd : dQ A 0 z = 0) : Vals b z := by
  have hc := d_cl_zero a b hz hd
  have h0 : (CH.cx (sq a b)).cls (cl a b z hz) hc = 0 := Subsingleton.elim _ _
  exact cl_eq_zero a b ((CechClassBoundaries.class_zero_eq_zero_iff _ _).1 h0)

theorem step_succ (a b : IdF A) {n : ℕ} (h : Subsingleton (CH.H (sq a b) (n + 1))) {z : Q A (n + 1)} (hz : Vals a z)
    (hd : dQ A (n + 1) z = 0) : ∃ y : Q A n, Vals a y ∧ Vals b (z - dQ A n y) := by
  have hc := d_cl_zero a b hz hd
  have h0 : (CH.cx (sq a b)).cls (cl a b z hz) hc = 0 := Subsingleton.elim _ _
  obtain ⟨f, hf⟩ := (CechClassBoundaries.mem_Bs _).1 ((CechClassBoundaries.cls_eq_zero _ _).1 h0)
  obtain ⟨y, hy, rfl⟩ := cl_surj a b f
  refine ⟨y, hy, cl_eq_zero a b (hx := hz.sub hy.dQ) ?_⟩
  rw [cl_sub a b hz hy.dQ, ← d_cl a b y hy]
  exact sub_eq_zero.2 hf.symm

abbrev St (a : ℕ → IdF A) (n k : ℕ) : Type 1 := {z : Q A (n + 1) // Vals (a k) z ∧ dQ A (n + 1) z = 0}

theorem exists_seq (a : ℕ → IdF A) {n : ℕ} (h : ∀ k, Subsingleton (CH.H (sq (a k) (a (k + 1))) (n + 1)))
    {z : Q A (n + 1)} (hz : Vals (a 0) z) (hd : dQ A (n + 1) z = 0) :
    ∃ y : ℕ → Q A n, (∀ k, Vals (a k) (y k)) ∧
      ∀ k, Vals (a k) (z - dQ A n (∑ i ∈ Finset.range k, y i)) := by
  have hs : ∀ (k : ℕ) (w : St a n k), ∃ y : Q A n, Vals (a k) y ∧ Vals (a (k + 1)) (w.1 - dQ A n y) :=
    fun k w => step_succ _ _ (h k) w.2.1 w.2.2
  choose f hf hg using hs
  let w : ∀ k, St a n k := fun k => Nat.rec ⟨z, hz, hd⟩ (fun k wk => ⟨wk.1 - dQ A n (f k wk), hg k wk, by
    have e : dQ A (n + 1) (dQ A n (f k wk)) = 0 := CH.d_d _ _ _
    rw [map_sub, wk.2.2, e, sub_zero]⟩) k
  refine ⟨fun k => f k (w k), fun k => hf k (w k), fun k => ?_⟩
  have e : ∀ k, (w k).1 = z - dQ A n (∑ i ∈ Finset.range k, f i (w i)) := by
    intro k
    induction k with
    | zero => simp [w]
    | succ k ih =>
      rw [Finset.sum_range_succ, map_add, ← sub_sub, ← ih]
  rw [← e]
  exact (w k).2.1

theorem exists_primitive (a : ℕ → IdF A) (ha : ∀ k T, (a (k + 1)).S T ≤ (a k).S T) (he : ∀ T, ∃ k, (a k).S T = ⊥)
    {n : ℕ} (h : ∀ k, Subsingleton (CH.H (sq (a k) (a (k + 1))) (n + 1)))
    {z : Q A (n + 1)} (hz : Vals (a 0) z) (hd : dQ A (n + 1) z = 0) :
    ∃ Y : Q A n, Vals (a 0) Y ∧ z = dQ A n Y := by
  classical
  have hle : ∀ {k m : ℕ}, k ≤ m → ∀ T, (a m).S T ≤ (a k).S T := by
    intro k m hkm T
    induction m, hkm using Nat.le_induction with
    | base => exact le_rfl
    | succ m _ ih => exact (ha m T).trans ih
  choose K hK using he
  have hbot : ∀ (T : C) {m : ℕ}, K T ≤ m → (a m).S T = ⊥ := fun T m hm =>
    le_bot_iff.1 ((hle hm T).trans (hK T).le)
  obtain ⟨y, hy, hz'⟩ := exists_seq a h hz hd
  let P : ℕ → Q A n := fun N => ∑ i ∈ Finset.range N, y i
  have hP : ∀ (s : ComposableArrows C n) {N : ℕ}, K (s.obj (Fin.last n)) ≤ N →
      val (P N) s = val (P (K (s.obj (Fin.last n)))) s := by
    intro s N hN
    induction N, hN using Nat.le_induction with
    | base => rfl
    | succ m hm ih =>
      have h0 : val (y m) s = 0 := by
        have := hy m s
        rwa [hbot _ hm, Ideal.mem_bot] at this
      have e : val (P (m + 1)) s = val (P m) s + val (y m) s := by
        simp only [P, Finset.sum_range_succ]
        rfl
      rw [e, h0, add_zero, ih]
  let Y : Q A n := fun s => val (P (K (s.obj (Fin.last n)))) s
  have hP0 : ∀ N, Vals (a 0) (P N) := by
    intro N
    induction N with
    | zero => intro s; simp only [P, Finset.range_zero, Finset.sum_empty]; exact (a 0 |>.S _).zero_mem
    | succ m ih =>
      intro s
      have e : val (P (m + 1)) s = val (P m) s + val (y m) s := by
        simp only [P, Finset.sum_range_succ]
        rfl
      rw [e]
      exact (a 0 |>.S _).add_mem (ih s) (hle (Nat.zero_le m) _ (hy m s))
  refine ⟨Y, fun s => hP0 _ s, ?_⟩
  funext s
  let N : ℕ := max (K (s.obj (Fin.last (n + 1)))) (Finset.univ.sup fun i : Fin (n + 2) => K ((face i s).obj (Fin.last n)))
  have h1 : val (z - dQ A n (P N)) s = 0 := by
    have := hz' N s
    rwa [hbot _ (le_max_left _ _), Ideal.mem_bot] at this
  have h2 : val (dQ A n (P N)) s = val (dQ A n Y) s := by
    rw [dQ_apply, dQ_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hP (face i s) ((Finset.le_sup (f := fun i : Fin (n + 2) => K ((face i s).obj (Fin.last n))) (Finset.mem_univ i)).trans (le_max_right _ _))]
  have h3 : val z s = val (dQ A n (P N)) s := sub_eq_zero.1 h1
  exact h3.trans h2

end GlobalTheory.CompanionTheory.TowerEnd

open GlobalTheory.CompanionTheory.TowerEnd in

theorem GlobalTheory.CompanionTheory.TowerEnd.vanish {R : Type} [CommRing R] {C : Type 1} [Category.{0} C] {A : C ⥤ CommAlgCat.{0} R} (a : ℕ → IdF A) :
    (∀ k T, (a (k + 1)).S T ≤ (a k).S T) → (∀ T, ∃ k, (a k).S T = ⊥) →
    (∀ k j, Subsingleton (CH.H (sq (a k) (a (k + 1))) j)) → ∀ j, Subsingleton (CH.H (sq (a 0) (IdF.bot A)) j) := by
  intro ha he h j
  have key : ∀ x : CH.H (sq (a 0) (IdF.bot A)) j, x = 0 := by
    intro x
    obtain ⟨f, hf, rfl⟩ := CechClassBoundaries.clsSurj x
    obtain ⟨z, hz, rfl⟩ := cl_surj _ _ f
    have hd : dQ A j z = 0 := by
      rw [d_cl] at hf
      funext s
      exact cl_eq_zero _ _ hf s
    cases j with
    | zero =>
      have hall : ∀ k, Vals (a k) z := by
        intro k
        induction k with
        | zero => exact hz
        | succ k ih => exact step_zero _ _ (h k 0) ih hd
      have h0 : cl (a 0) (IdF.bot A) z hz = 0 := by
        funext s
        obtain ⟨k, hk⟩ := he (s.obj (Fin.last 0))
        have h1 := hall k s
        rw [hk, Ideal.mem_bot] at h1
        apply Subtype.ext
        change Ideal.Quotient.mk _ (val z s) = 0
        rw [h1]
        exact map_zero (Ideal.Quotient.mk _)
      exact (CechClassBoundaries.class_zero_eq_zero_iff _ _).2 h0
    | succ n =>
      obtain ⟨Y, hY, e⟩ := exists_primitive a ha he (fun k => h k (n + 1)) hz hd
      refine (CechClassBoundaries.cls_eq_zero _ _).2 ((CechClassBoundaries.mem_Bs _).2 ⟨cl _ _ Y hY, ?_⟩)
      rw [d_cl]
      subst e
      rfl
  exact ⟨fun x y => (key x).trans (key y).symm⟩
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CoordDimEqRelativeDim
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor CrystallineSemistableComparison.Pb
attribute [local instance] MvPolynomial.gradedAlgebra

namespace GlobalTheory.CompanionTheory.CoordCard

theorem card_eq_of_etale {K L : Type} [Field K] [CommRing L] [Nontrivial L] [Algebra K L] {m n : ℕ}
    [Algebra (MvPolynomial (Fin m) K) L] [IsScalarTower K (MvPolynomial (Fin m) K) L]
    [Algebra.FormallyEtale (MvPolynomial (Fin m) K) L]
    [Algebra.IsStandardSmoothOfRelativeDimension n K L] : m = n := by
  let b := KaehlerDifferential.mvPolynomialBasis K (Fin m)
  let b' := (b.baseChange L).map (KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale K (MvPolynomial (Fin m) K) L)
  have hr := Algebra.IsStandardSmoothOfRelativeDimension.rank_kaehlerDifferential (R := K) (S := L) n
  have h1 := b'.mk_eq_rank''
  rw [hr] at h1
  simpa using h1

theorem card_eq_of_away {K A L : Type} [Field K] [CommRing A] [CommRing L] [Nontrivial L] [Algebra A L] {m n : ℕ}
    (t : A) [IsLocalization.Away t L] (g : K →+* A) (φ : MvPolynomial (Fin m) K →+* A)
    (hφ : ∀ r, φ (MvPolynomial.C r) = g r) (hE : φ.Etale)
    (hf : RingHom.IsStandardSmoothOfRelativeDimension n ((algebraMap A L).comp g)) : m = n := by
  letI iPA : Algebra (MvPolynomial (Fin m) K) A := φ.toAlgebra
  letI iKL : Algebra K L := ((algebraMap A L).comp g).toAlgebra
  letI iPL : Algebra (MvPolynomial (Fin m) K) L := ((algebraMap A L).comp φ).toAlgebra
  haveI : IsScalarTower (MvPolynomial (Fin m) K) A L := IsScalarTower.of_algebraMap_eq' rfl
  haveI : IsScalarTower K (MvPolynomial (Fin m) K) L :=
    IsScalarTower.of_algebraMap_eq fun r => by
      change algebraMap A L (g r) = algebraMap A L (φ (MvPolynomial.C r))
      rw [hφ]
  haveI : Algebra.Etale (MvPolynomial (Fin m) K) A := hE
  haveI : Algebra.FormallyEtale A L := Algebra.FormallyEtale.of_isLocalization (Submonoid.powers t)
  haveI : Algebra.FormallyEtale (MvPolynomial (Fin m) K) L := Algebra.FormallyEtale.comp _ A _
  haveI : Algebra.IsStandardSmoothOfRelativeDimension n K L := hf
  exact card_eq_of_etale (K := K) (L := L)

theorem main : ∀ {K : Type} [Field K] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K)) (n : ℕ)
    [SmoothOfRelativeDimension n q] {V : X.Opens}, (V : Set X).Nonempty → ∀ {m : ℕ} (c : Coord q V m), m = n := by
  intro K _ X q n hn V hV m c
  obtain ⟨x, hx⟩ := hV
  have hnt : Nontrivial Γ(X, V) := (X.presheaf.germ V x hx).hom.domain_nontrivial
  obtain ⟨s, hs, h'⟩ := HasRingHomProperty.appLE (@SmoothOfRelativeDimension n) q hn
    ⟨⊤, isAffineOpen_top _⟩ ⟨V, c.affine⟩ le_top
  obtain ⟨p, hp⟩ := Ideal.exists_maximal Γ(X, V)
  obtain ⟨t, ht, htp⟩ : ∃ t ∈ s, t ∉ p := by
    by_contra hc
    exact hp.ne_top (top_le_iff.1 (hs ▸ Ideal.span_le.2 fun t ht => by_contra fun h => hc ⟨t, ht, h⟩))
  have : Nontrivial (Localization.Away t) := by
    by_contra hc
    obtain ⟨k, hk⟩ := (IsLocalization.subsingleton_iff (M := Submonoid.powers t)).1 (not_nontrivial_iff_subsingleton.1 hc)
    exact htp (hp.isPrime.mem_of_pow_mem k (by rw [show t ^ k = 0 from hk]; exact p.zero_mem))
  have h₁ := h' t ht
  let e : K ≃+* Γ(Spec (CommRingCat.of K), ⊤) := (Scheme.ΓSpecIso (CommRingCat.of K)).symm.commRingCatIsoToRingEquiv
  have hf : RingHom.IsStandardSmoothOfRelativeDimension n
      ((algebraMap Γ(X, V) (Localization.Away t)).comp (strV q V)) :=
    RingHom.isStandardSmoothOfRelativeDimension_respectsIso.2 _ e h₁
  exact card_eq_of_away (L := Localization.Away t) t (strV q V) (MvPolynomial.eval₂Hom (strV q V) c.t)
    (fun r => by simp) c.etale hf

end GlobalTheory.CompanionTheory.CoordCard
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CoordinatesRestrictAffineOpen
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb

namespace GlobalTheory.CompanionTheory.CoordRes

theorem etale_rs {X : Scheme.{0}} {V W : X.Opens} (h : W ≤ V) (hV : IsAffineOpen V) (hW : IsAffineOpen W) :
    (rs h).Etale := by
  have key := HasRingHomProperty.appLE @Etale (𝟙 X) inferInstance ⟨V, hV⟩ ⟨W, hW⟩ h
  have e : Scheme.Hom.appLE (𝟙 X) V W h = X.presheaf.map (homOfLE h).op := by
    simp [Scheme.Hom.appLE] <;> rfl
  rw [e] at key
  exact key

theorem rs_comp_strV {O : Type} [CommRing O] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of O)) {V W : X.Opens}
    (h : W ≤ V) : (rs h).comp (strV q V) = strV q W := by
  simp only [rs, strV]
  rw [← CommRingCat.hom_comp, Category.assoc, Scheme.Hom.appLE_map]

theorem main : ∀ {O : Type} [CommRing O] {X : Scheme.{0}} {q : X ⟶ Spec (CommRingCat.of O)} {V W : X.Opens} {d : ℕ}
    (c : Coord q V d) (h : W ≤ V) (hW : IsAffineOpen W), ∃ c' : Coord q W d, ∀ i, c'.t i = rs h (c.t i) := by
  intro O _ X q V W d c h hW
  refine ⟨⟨hW, fun i => rs h (c.t i), ?_⟩, fun i => rfl⟩
  have e1 : MvPolynomial.eval₂Hom (strV q W) (fun i => rs h (c.t i)) =
      (rs h).comp (MvPolynomial.eval₂Hom (strV q V) c.t) := by
    rw [MvPolynomial.comp_eval₂Hom, rs_comp_strV]
  rw [e1]
  exact RingHom.Etale.stableUnderComposition _ _ c.etale (etale_rs h c.affine hW)

end GlobalTheory.CompanionTheory.CoordRes
end

