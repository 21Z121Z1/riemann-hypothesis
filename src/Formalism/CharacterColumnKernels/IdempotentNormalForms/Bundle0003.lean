import Formalism.CharacterColumnKernels.Bundle0001
import Formalism.CharacterColumnKernels.Bundle0002
import Formalism.CharacterColumnKernels.StatementX
import Formalism.CharacterColumnKernels.IdempotentNormalForms.Bundle0002
import Formalism.CharacterColumnKernels.IdempotentNormalForms.SingleEqSmul
import Formalism.CharacterColumnKernels.StatementMF
import Formalism.CharacterColumnKernels.IdempotentNormalForms.Bundle0001
import Formalism.CharacterColumnKernels.StatementN

-- bundled from Formalism.CharacterColumnKernels.IdempotentNormalForms.GenFin
section
open Finset

noncomputable section

namespace Formalism.NG

lemma genfin_det_totalDegree {ι K n : Type*} [CommRing K] [Fintype n] [DecidableEq n]
    (A : Matrix n n (MvPolynomial ι K)) (h : ∀ i j, (A i j).totalDegree ≤ 1) :
    A.det.totalDegree ≤ Fintype.card n := by
  rw [Matrix.det_apply]
  refine (MvPolynomial.totalDegree_finset_sum _ _).trans (Finset.sup_le fun σ _ => ?_)
  have hprod : (∏ i, A (σ i) i).totalDegree ≤ Fintype.card n := by
    refine (MvPolynomial.totalDegree_finset_prod _ _).trans ?_
    calc ∑ i, (A (σ i) i).totalDegree ≤ ∑ _i : n, 1 := Finset.sum_le_sum fun i _ => h _ _
      _ = Fintype.card n := by simp
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with hs | hs
  · rw [hs, one_smul]
    exact hprod
  · rw [hs, Units.neg_smul, one_smul, MvPolynomial.totalDegree_neg]
    exact hprod

theorem genericFin : StatGenericFin := by
  intro R O _ _ _ _ _ m g s _ _ _ _ d _ _ hcard ρ hρ P
  classical
  have hk := fun w => gen_key (O := O) (bigRect (ρ w) P)
  choose n U f e hC0 hgood using hk
  choose C0 hC0 using hC0
  let res := IsLocalRing.residue O
  let r : ∀ w, d w → d w → R := fun w a b => Function.surjInv (hρ w) (Matrix.single a b 1)
  let c : (Σ w : s, g × m × d w × d w) → Matrix g m R := fun j =>
    Matrix.single j.2.1 j.2.2.1 (r j.1 j.2.2.2.1 j.2.2.2.2)
  let L : ∀ w, Matrix (g × d w) (m × d w) (MvPolynomial (Σ w : s, g × m × d w × d w)
      (IsLocalRing.ResidueField O)) := fun w p q =>
    ∑ j, MvPolynomial.X j * MvPolynomial.C (res (ρ w (c j p.1 q.1) p.2 q.2))
  let Q : s → MvPolynomial (Σ w : s, g × m × d w × d w) (IsLocalRing.ResidueField O) := fun w =>
    (Matrix.of fun p q => ∑ l, L w (e w p) l * MvPolynomial.C (res (U w l (f w q)))).det
  have hevalQ : ∀ w (t : (Σ w : s, g × m × d w × d w) → O),
      MvPolynomial.eval (fun j => res (t j)) (Q w) =
        res (Matrix.of fun p q => (bigRect (ρ w) (∑ j, t j • c j) * U w) (e w p) (f w q)).det := by
    intro w t
    simp only [Q]
    rw [RingHom.map_det, RingHom.map_det]
    congr 1
    ext p q
    simp [L, Matrix.mul_apply, bigRect, Matrix.sum_apply, map_sum]

  have hsum : ∀ w (φ : g × m × d w × d w → O),
      bigRect (ρ w) (∑ j : (Σ w : s, g × m × d w × d w),
        (Pi.single (M := fun w => g × m × d w × d w → O) w φ j.1 j.2) • c j) =
        fun p q => φ (p.1, q.1, p.2, q.2) := by
    intro w φ
    funext p q
    simp only [bigRect, Matrix.sum_apply, Matrix.smul_apply, map_sum, map_smul]
    rw [Fintype.sum_sigma]
    rw [Fintype.sum_eq_single w (fun x hx => by simp [Pi.single_eq_of_ne hx])]
    simp only [Pi.single_eq_same]
    rw [Fintype.sum_eq_single (p.1, q.1, p.2, q.2)]
    · simp [c, r, Function.surjInv_eq (hρ w)]
    · rintro ⟨i', k', a', b'⟩ hy
      simp only [c, r, Matrix.single_apply]
      split_ifs with h1
      · obtain ⟨rfl, rfl⟩ := h1
        rw [Function.surjInv_eq (hρ w), Matrix.single_apply, if_neg, smul_zero]
        rintro ⟨rfl, rfl⟩
        exact hy rfl
      · simp
  have hQne : ∀ w, Q w ≠ 0 := by
    intro w hQ
    set t0 : (Σ w : s, g × m × d w × d w) → O := fun j =>
      Pi.single (M := fun w => g × m × d w × d w → O) w
        (fun x => C0 w (x.1, x.2.2.1) (x.2.1, x.2.2.2)) j.1 j.2 with ht0
    have h1 := hevalQ w t0
    rw [hQ, map_zero] at h1
    have h2 : bigRect (ρ w) (∑ j, t0 j • c j) = C0 w := by
      rw [ht0, hsum]
    rw [h2] at h1
    exact (IsLocalRing.residue_ne_zero_iff_isUnit _).2 (hC0 w) h1.symm
  have hprod : (∏ w, Q w) ≠ 0 := Finset.prod_ne_zero_iff.2 (fun w _ => hQne w)

  have hL : ∀ w p q, (L w p q).totalDegree ≤ 1 := fun w p q =>
    MvPolynomial.totalDegree_finsetSum_le fun j _ => (MvPolynomial.totalDegree_mul _ _).trans
      (by rw [MvPolynomial.totalDegree_X, MvPolynomial.totalDegree_C])
  have hQdeg : ∀ w, (Q w).totalDegree ≤ Fintype.card g * Fintype.card (d w) := by
    intro w
    simp only [Q]
    refine (genfin_det_totalDegree _ fun p q => ?_).trans ?_
    · rw [Matrix.of_apply]
      exact MvPolynomial.totalDegree_finsetSum_le fun l _ => (MvPolynomial.totalDegree_mul _ _).trans
        (by rw [MvPolynomial.totalDegree_C, add_zero]; exact hL _ _ _)
    · rw [Fintype.card_fin, ← Fintype.card_prod]
      have he := Fintype.card_le_of_embedding (e w)
      rwa [Fintype.card_fin] at he
  set D : ℕ := Fintype.card g * ∑ w, Fintype.card (d w) with hD
  have hdeg : (∏ w, Q w).totalDegree ≤ D := by
    refine (MvPolynomial.totalDegree_finsetProd _ _).trans ?_
    rw [hD, Finset.mul_sum]
    exact Finset.sum_le_sum fun w _ => hQdeg w

  obtain ⟨S, hS⟩ : ∃ S : Finset (IsLocalRing.ResidueField O), D < S.card := by
    rcases finite_or_infinite (IsLocalRing.ResidueField O) with hk | hk
    · cases nonempty_fintype (IsLocalRing.ResidueField O)
      refine ⟨Finset.univ, ?_⟩
      rw [Finset.card_univ]
      rw [Cardinal.mk_fintype, Nat.cast_lt] at hcard
      exact hcard
    · obtain ⟨S, hS⟩ := Infinite.exists_subset_card_eq (IsLocalRing.ResidueField O) (D + 1)
      exact ⟨S, by omega⟩

  obtain ⟨x, hx⟩ : ∃ x, MvPolynomial.eval x (∏ w, Q w) ≠ 0 := by
    by_contra hcon
    simp only [not_exists, not_not] at hcon
    exact hprod (MvPolynomial.eq_zero_of_eval_zero_at_prod_finset _ (fun _ => S)
      (fun i => lt_of_le_of_lt ((MvPolynomial.degreeOf_le_totalDegree _ i).trans hdeg) hS)
      (fun x _ => hcon x))
  rw [map_prod] at hx
  have hxw : ∀ w, MvPolynomial.eval x (Q w) ≠ 0 := fun w =>
    (Finset.prod_ne_zero_iff.1 hx) w (Finset.mem_univ w)
  let t : (Σ w : s, g × m × d w × d w) → O := fun j =>
    Function.surjInv (IsLocalRing.residue_surjective (R := O)) (x j)
  have htx : (fun j => res (t j)) = x := funext fun j => Function.surjInv_eq _ _
  refine ⟨∑ j, t j • c j, fun w => ?_⟩
  have hu : IsUnit (Matrix.of fun p q =>
      (bigRect (ρ w) (∑ j, t j • c j) * U w) (e w p) (f w q)).det := by
    rw [← IsLocalRing.residue_ne_zero_iff_isUnit, ← hevalQ w t, htx]
    exact hxw w
  show Module.length O (LinearMap.ker (relMap O (KO O) (bigMat (ρ w) (_ * P)))) = _
  rw [gen_bigMat_mul, hgood w _ hu]

section KerHomRectAux

variable {R : Type*} [Ring R] {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  {m g d : Type} [Fintype m] [Fintype g] [DecidableEq g] [Fintype d] [DecidableEq d]
  (ρ : R →+* Matrix d d O) [SMulCommClass R O (LatQ O d ρ)]

theorem genfin_uncurry_relMap (P : Matrix m g R) (v : g → LatQ O d ρ) :
    uncurryEquiv (g := m) ρ (relMap O (LatQ O d ρ) P v) =
      relMap O (KO O) (fun (p : m × d) (q : g × d) => ρ (P p.1 q.1) p.2 q.2)
        (uncurryEquiv ρ v) := by
  funext p
  obtain ⟨i, a⟩ := p
  show (∑ j, P i j • v j : LatQ O d ρ) a = ∑ q : g × d, ρ (P i q.1) a q.2 • v q.1 q.2
  rw [Fintype.sum_prod_type]
  have hsum : (∑ j, P i j • v j : LatQ O d ρ) a = ∑ j, ((P i j • v j : LatQ O d ρ) : d → KO O) a :=
    Finset.sum_apply (M := fun _ : d => KO O) a univ (fun j => (P i j • v j : LatQ O d ρ))
  rw [hsum]
  rfl

theorem genfin_ker_map_uncurry (P : Matrix m g R) :
    (LinearMap.ker (relMap O (LatQ O d ρ) P)).map (uncurryEquiv (g := g) ρ).toLinearMap =
      LinearMap.ker (relMap O (KO O) (fun (p : m × d) (q : g × d) => ρ (P p.1 q.1) p.2 q.2)) := by
  ext w
  rw [Submodule.mem_map_equiv, LinearMap.mem_ker, LinearMap.mem_ker]
  constructor
  · intro h
    have := genfin_uncurry_relMap ρ P ((uncurryEquiv ρ).symm w)
    rw [h, map_zero, LinearEquiv.apply_symm_apply] at this
    exact this.symm
  · intro h
    have := genfin_uncurry_relMap ρ P ((uncurryEquiv ρ).symm w)
    rw [LinearEquiv.apply_symm_apply, h] at this
    exact (uncurryEquiv ρ).map_eq_zero_iff.mp this

end KerHomRectAux

theorem kerHomRect : StatKerHomRect := by
  intro R O _ _ _ _ m g d _ _ _ _ _ ρ _ P
  rw [(homEquiv (O := O) (M := LatQ O d ρ) P).length_eq]
  exact ((LinearEquiv.ofSubmodules (uncurryEquiv ρ) _ _ (genfin_ker_map_uncurry ρ P)).length_eq).symm

end Formalism.NG
end
end

-- bundled from Formalism.CharacterColumnKernels.IdempotentNormalForms.LengthEpsImgEqAdd
section
noncomputable section

namespace Formalism.NG

universe u

section LenEpsAux

variable {O OO : Type*} [CommRing O] [Ring OO] [Algebra O OO]

lemma mem_epsImg_iff {M : Type*} [AddCommGroup M] [Module OO M] [Module O M]
    [IsScalarTower O OO M] (ε : OO) (x : M) :
    x ∈ epsImg O (M := M) ε ↔ ∃ y : M, ε • y = x := by
  simp [epsImg]

def epsMap {A B : Type*} [AddCommGroup A] [Module OO A] [Module O A] [IsScalarTower O OO A]
    [AddCommGroup B] [Module OO B] [Module O B] [IsScalarTower O OO B]
    (φ : A →ₗ[OO] B) (ε : OO) : epsImg O (M := A) ε →ₗ[O] epsImg O (M := B) ε :=
  LinearMap.restrict (φ.restrictScalars O) (fun x hx => by
    rw [mem_epsImg_iff] at hx ⊢
    obtain ⟨y, rfl⟩ := hx
    exact ⟨φ y, by simp⟩)

@[simp] lemma epsMap_apply {A B : Type*} [AddCommGroup A] [Module OO A] [Module O A]
    [IsScalarTower O OO A]
    [AddCommGroup B] [Module OO B] [Module O B] [IsScalarTower O OO B]
    (φ : A →ₗ[OO] B) (ε : OO) (x : epsImg O (M := A) ε) :
    ((epsMap (O := O) φ ε x : epsImg O (M := B) ε) : B) = φ x := rfl

end LenEpsAux

end Formalism.NG
end
end

-- bundled from Formalism.CharacterColumnKernels.IdempotentNormalForms.RightMulEpsAlgebraMap
section
open Module IsDiscreteValuationRing

noncomputable section

namespace Formalism.NG

namespace IdempotentImageSmul

section Adj

variable {O OO M Q : Type*} [CommRing O] [Ring OO] [Algebra O OO] [AddCommGroup M] [Module OO M]
    [Module O M] [IsScalarTower O OO M] [AddCommGroup Q] [Module O Q] (ε : OO)

def epsE : epsIdeal O ε := ⟨ε, LinearMap.mem_range.mpr ⟨1, by simp⟩⟩

lemma dual_smul_apply (a : OO) (φ : EpsDual O OO Q ε) (x : epsIdeal O ε) :
    (a • φ) x = φ (rightMulEps O ε a x) := rfl

lemma rightMulEps_algebraMap (c : O) (x : epsIdeal O ε) :
    rightMulEps O ε (algebraMap O OO c) x = c • x := by
  apply Subtype.ext
  show x.1 * algebraMap O OO c = c • x.1
  rw [Algebra.smul_def, Algebra.commutes]

variable {ε}

lemma eps_mul_of_mem (hε : IsIdempotentElem ε) (x : epsIdeal O ε) : ε * x.1 = x.1 := by
  obtain ⟨y, hy⟩ := x.2
  simp only [LinearMap.mulLeft_apply] at hy
  rw [← hy, ← mul_assoc, hε.eq]

lemma smul_mem_epsImg (x : epsIdeal O ε) (m : M) : x.1 • m ∈ epsImg O (M := M) ε := by
  obtain ⟨y, hy⟩ := x.2
  simp only [LinearMap.mulLeft_apply] at hy
  refine ⟨y • m, ?_⟩
  show ε • (y • m) = x.1 • m
  rw [← hy, mul_smul]

lemma eps_smul_of_mem (hε : IsIdempotentElem ε) (y : epsImg O (M := M) ε) : ε • y.1 = y.1 := by
  obtain ⟨z, hz⟩ := y.2
  rw [← hz]
  show ε • ε • z = ε • z
  rw [← mul_smul, hε.eq]

variable (ε) [SMulCommClass OO O (EpsDual O OO Q ε)]

def fwd : (M →ₗ[OO] EpsDual O OO Q ε) →ₗ[O] (epsImg O (M := M) ε →ₗ[O] Q) where
  toFun Φ :=
    { toFun := fun y => Φ y.1 (epsE ε)
      map_add' := fun y z => by simp
      map_smul' := fun c y => by
        show Φ (c • y.1) (epsE ε) = c • Φ y.1 (epsE ε)
        rw [← algebraMap_smul OO c y.1, Φ.map_smul, dual_smul_apply, rightMulEps_algebraMap,
          map_smul] }
  map_add' Φ Ψ := rfl
  map_smul' c Φ := rfl

def bwdInner (ψ : epsImg O (M := M) ε →ₗ[O] Q) (m : M) : EpsDual O OO Q ε where
  toFun x := ψ ⟨x.1 • m, smul_mem_epsImg x m⟩
  map_add' x z := by
    rw [← map_add]; congr 1; apply Subtype.ext
    show (x.1 + z.1) • m = x.1 • m + z.1 • m
    rw [add_smul]
  map_smul' c x := by
    rw [← map_smul]; congr 1; apply Subtype.ext
    show (c • x.1) • m = c • (x.1 • m)
    rw [smul_assoc]

def bwd : (epsImg O (M := M) ε →ₗ[O] Q) →ₗ[O] (M →ₗ[OO] EpsDual O OO Q ε) where
  toFun ψ :=
    { toFun := bwdInner ε ψ
      map_add' := fun m m' => by
        apply LinearMap.ext; intro x
        show ψ ⟨x.1 • (m + m'), _⟩ = ψ ⟨x.1 • m, _⟩ + ψ ⟨x.1 • m', _⟩
        rw [← map_add]; congr 1; apply Subtype.ext
        show x.1 • (m + m') = x.1 • m + x.1 • m'
        rw [smul_add]
      map_smul' := fun a m => by
        apply LinearMap.ext; intro x
        show ψ ⟨x.1 • a • m, _⟩ = ψ ⟨(x.1 * a) • m, _⟩
        congr 1; apply Subtype.ext
        show x.1 • a • m = (x.1 * a) • m
        rw [mul_smul] }
  map_add' ψ ψ' := rfl
  map_smul' c ψ := rfl

variable {ε}

lemma bwd_fwd (hε : IsIdempotentElem ε) (Φ : M →ₗ[OO] EpsDual O OO Q ε) :
    bwd ε (fwd ε Φ) = Φ := by
  apply LinearMap.ext
  intro m
  apply LinearMap.ext
  intro x
  show Φ (x.1 • m) (epsE ε) = Φ m x
  rw [Φ.map_smul, dual_smul_apply]
  congr 1
  apply Subtype.ext
  show ε * x.1 = x.1
  exact eps_mul_of_mem hε x

lemma fwd_bwd (hε : IsIdempotentElem ε) (ψ : epsImg O (M := M) ε →ₗ[O] Q) :
    fwd ε (bwd ε ψ) = ψ := by
  apply LinearMap.ext
  intro y
  show ψ ⟨ε • y.1, _⟩ = ψ y
  congr 1
  apply Subtype.ext
  exact eps_smul_of_mem hε y

end Adj

section Matlis

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

def homQuotEquiv (a : O) :
    ((O ⧸ Ideal.span ({a} : Set O)) →ₗ[O] KO O) ≃ₗ[O]
      LinearMap.ker (matQ O (fun _ _ => a : Matrix Unit Unit O)) where
  toFun φ := ⟨fun _ => φ (Submodule.Quotient.mk 1), by
    rw [LinearMap.mem_ker]; funext i
    show ∑ _j : Unit, a • φ (Submodule.Quotient.mk 1) = 0
    rw [Fintype.sum_unique, ← map_smul, ← Submodule.Quotient.mk_smul, smul_eq_mul, mul_one,
      (Submodule.Quotient.mk_eq_zero _).mpr (Ideal.mem_span_singleton_self a), map_zero]⟩
  map_add' φ ψ := rfl
  map_smul' c φ := rfl
  invFun v := (Ideal.span ({a} : Set O)).liftQ (LinearMap.toSpanSingleton O _ (v.1 ())) (by
    rw [Ideal.span, Submodule.span_le, Set.singleton_subset_iff]
    show a • v.1 () = 0
    have h : (∑ j : Unit, a • v.1 j) = 0 := congrFun (LinearMap.mem_ker.mp v.2) ()
    rwa [Fintype.sum_unique] at h)
  left_inv φ := by
    apply LinearMap.ext; intro x
    induction x using Submodule.Quotient.induction_on with
    | H x =>
      rw [Submodule.liftQ_apply, LinearMap.toSpanSingleton_apply]
      show x • φ (Submodule.Quotient.mk 1) = φ (Submodule.Quotient.mk x)
      rw [← map_smul, ← Submodule.Quotient.mk_smul, smul_eq_mul, mul_one]
  right_inv v := by
    apply Subtype.ext; funext i
    show ((Ideal.span ({a} : Set O)).liftQ _ _) (Submodule.Quotient.mk 1) = v.1 i
    rw [Submodule.liftQ_apply, LinearMap.toSpanSingleton_apply, one_smul]

lemma length_hom_quot (a : O) :
    Module.length O ((O ⧸ Ideal.span ({a} : Set O)) →ₗ[O] KO O) = addVal O a := by
  rw [(homQuotEquiv a).length_eq, lenKer O Unit (fun _ _ => a)]
  exact congrArg _ (Matrix.det_unique _)

lemma length_self_top : Module.length O O = ⊤ := by
  by_contra h
  have hfl : IsFiniteLength O O := Module.length_ne_top_iff.mp h
  rw [isFiniteLength_iff_isNoetherian_isArtinian] at hfl
  haveI : IsArtinianRing O := hfl.2
  exact IsDiscreteValuationRing.not_isField O (IsArtinianRing.isField_of_isDomain O)

end Matlis

end IdempotentImageSmul

open IdempotentImageSmul

theorem matlis : StatMatlis := by
  classical
  intro O N _ _ _ _ _ hN
  have hNA := isFiniteLength_iff_isNoetherian_isArtinian.mp hN
  have : IsNoetherian O N := hNA.1
  obtain ⟨n, ι, _, p, -, e, ⟨f⟩⟩ := Module.equiv_free_prod_directSum (R := O) (M := N)
  set A : ι → Type _ := fun i => O ⧸ O ∙ p i ^ e i with hA
  let g : (DirectSum ι A) ≃ₗ[O] (Π i, A i) := DirectSum.linearEquivFunOnFintype O ι A
  have hlenA : ∀ i, Module.length O (A i) = addVal O (p i ^ e i) := fun i =>
    IdempotentNormalFormsLenFacts.length_quot_span (p i ^ e i)
  have hlenH : ∀ i, Module.length O (A i →ₗ[O] KO O) = addVal O (p i ^ e i) := fun i =>
    length_hom_quot (p i ^ e i)
  have hN1 : Module.length O N =
      Module.length O (Fin n →₀ O) + ∑ i, addVal O (p i ^ e i) := by
    rw [f.length_eq, Module.length_prod, g.length_eq, Module.length_pi_of_fintype]
    simp only [hlenA]
  have hF : Module.length O (Fin n →₀ O) = 0 := by
    rw [Module.length_finsupp, length_self_top]
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn; simp
    · exfalso
      have : Module.length O N = ⊤ := by
        rw [hN1, Module.length_finsupp, length_self_top, ENat.card_eq_coe_fintype_card,
          Fintype.card_fin, ENat.mul_top (by exact_mod_cast hn.ne'), top_add]
      exact (Module.length_ne_top_iff.mpr hN) this
  have : Subsingleton (Fin n →₀ O) := Module.length_eq_zero_iff.mp hF
  have hFH : Module.length O ((Fin n →₀ O) →ₗ[O] KO O) = 0 := by
    rw [Module.length_eq_zero_iff]
    exact ⟨fun φ ψ => LinearMap.ext fun x => by rw [Subsingleton.elim x 0, map_zero, map_zero]⟩
  let h1 : (N →ₗ[O] KO O) ≃ₗ[O] ((Fin n →₀ O) × DirectSum ι A →ₗ[O] KO O) :=
    f.arrowCongr (LinearEquiv.refl O (KO O))
  let h2 : (DirectSum ι A →ₗ[O] KO O) ≃ₗ[O] ((Π i, A i) →ₗ[O] KO O) :=
    g.arrowCongr (LinearEquiv.refl O (KO O))
  have h3 : Module.length O ((Π i, A i) →ₗ[O] KO O) = ∑ i, addVal O (p i ^ e i) := by
    have := (LinearMap.lsum O A O : (Π i, A i →ₗ[O] KO O) ≃ₗ[O] _).length_eq
    rw [← this, Module.length_pi_of_fintype]
    simp only [hlenH]
  rw [h1.length_eq, ← (LinearMap.coprodEquiv O).length_eq, Module.length_prod, h2.length_eq,
    h3, hFH, hN1, hF]

end Formalism.NG
end
end

-- bundled from Formalism.CharacterColumnKernels.IdempotentNormalForms.VccSpan
section
open Finset

namespace Formalism.NG

theorem descent : StatDescent := by
  intro O _ X X' T T' Z p q b hexp hind f' hf' hvan π'
  obtain ⟨a, haT, rfl⟩ := hexp f' hf'
  have hker : ∀ k, (⟨a k, haT k⟩ : T) ∈ ccIdeal T Z := by
    intro k
    rw [ccIdeal, RingHom.mem_ker]
    funext x
    have hx : x.1 ∉ Z := x.2
    have h0 := hind x.1 hx (fun k => a k x.1) (fun x' hx' => by
      have e := hvan x' (by rw [hx']; exact hx)
      simpa [hx', Finset.sum_apply, Pi.mul_apply, Function.comp] using e)
    have e2 := congrFun h0 k
    simpa [resOff] using e2
  rw [Finset.sum_apply]
  refine Ideal.sum_mem _ fun k _ => ?_
  simp only [Pi.mul_apply, Function.comp_apply]
  exact Ideal.mul_mem_right _ _ (Ideal.subset_span ⟨_, hker k, rfl⟩)

theorem vccSpan : StatVccSpan := by
  intro O _ _ _ X T Z x y hy
  induction hy using Submodule.span_induction with
  | mem s hs =>
    obtain ⟨c, hc, rfl⟩ := hs
    exact iInf₂_le c hc
  | zero => simp
  | add a b _ _ ha hb =>
    exact le_trans (le_min ha hb) IsDiscreteValuationRing.addVal_add
  | smul r a _ ha =>
    rw [smul_eq_mul, IsDiscreteValuationRing.addVal_mul]
    exact le_trans ha le_add_self

end Formalism.NG
end

