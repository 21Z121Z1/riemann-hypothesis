import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0978
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1020
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExtremalLowestKtypeKilledByCompactRoots
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0046
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0182
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0013
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.HomBaseChangeBijectiveOfLeNilradical
import Development.AbelianVarietyTheory.Definitions.Divisors.HasBlockOfOccurs
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0235
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsDiscreteValuationRingIntegralClosurePadicInt
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRootSelectionUnitaryRankOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1131
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1111
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0045
import Development.AbelianVarietyTheory.Definitions.Divisors.NormSqColGrLineOfOrthogonal
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExtremalLowestKTypeKilledCompactRoots
section
open NumberField IsDedekindDomain Matrix MeasureTheory ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT GlobalTheory.HolRead
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.HolRead.KCpt

open GlobalTheory.HolDict GlobalTheory.HolDict.BorelK

variable {n : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {ε : Fin n → Bool}
  {σ : Mt n → (H →L[ℂ] H)}

theorem revNeg_lt {a b : Fin n} (ha : ε a = false) (hb : ε b = false) (h : b < a) : revNeg ε a < revNeg ε b := by
  have ma : a ∈ negS ε := by simp [negS, ha]
  have mb : b ∈ negS ε := by simp [negS, hb]
  have h1 : revNeg ε a = (revOn ε ⟨a, ma⟩ : Fin n) := Equiv.Perm.ofSubtype_apply_of_mem _ ma
  have h2 : revNeg ε b = (revOn ε ⟨b, mb⟩ : Fin n) := Equiv.Perm.ofSubtype_apply_of_mem _ mb
  rw [h1, h2]
  have h3 : (⟨b, mb⟩ : {x // x ∈ negS ε}) < ⟨a, ma⟩ := h
  have h4 := ((negS ε).orderIsoOfFin rfl).symm.strictMono h3
  exact ((negS ε).orderIsoOfFin rfl).strictMono (Fin.rev_lt_rev.2 h4)

theorem isWtOn_root (hσ : IsURepOn (UJset ε) σ) {μ : Fin n → ℝ} {v : H}
    (hs : SmoothVec (lieH (Formalism.REAL.Jm ε)) σ v) (hv : IsWtOn (Formalism.REAL.Kset ε) σ μ v) (a c : Fin n) :
    IsWtOn (Formalism.REAL.Kset ε) σ (μ + Formalism.REAL.root a c) (dRepC (Formalism.REAL.Jm ε) σ (Matrix.single a c 1) v) := by
  have hh : (Formalism.REAL.Jm ε).IsHermitian := Formalism.REAL.Jm_conjTranspose ε
  have z0 : ∀ x : H, dRepC (Formalism.REAL.Jm ε) σ 0 x = 0 := by
    intro x
    simp [dRepC, conjH, dRep]
  have l1 : ∀ (s : ℂ) Z, dRepC (Formalism.REAL.Jm ε) σ (s • Z) v = s • dRepC (Formalism.REAL.Jm ε) σ Z v := by
    intro s Z
    have := LieAct.dRepC_lin hh det_Jm hσ hs s Z 0
    rwa [add_zero, z0, add_zero] at this
  have l2 : ∀ (s : ℂ) Z, dRepC (Formalism.REAL.Jm ε) σ Z (s • v) = s • dRepC (Formalism.REAL.Jm ε) σ Z v := by
    intro s Z
    have := LieAct.dRepC_vec (π := σ) hh det_Jm hs hs (s - 1) Z
    rw [sub_smul, one_smul, sub_add_cancel, sub_smul, one_smul, sub_add_cancel] at this
    exact this
  intro θ hθ
  have hinv : (diagonal fun a => Complex.exp ((θ a : ℂ) * Complex.I))⁻¹ =
      diagonal fun a => Complex.exp (-((θ a : ℂ) * Complex.I)) := by
    apply Matrix.inv_eq_left_inv
    rw [diagonal_mul_diagonal, ← diagonal_one]
    congr 1
    funext b
    rw [← Complex.exp_add]; simp
  have e : (diagonal fun a => Complex.exp ((θ a : ℂ) * Complex.I)) * Matrix.single a c (1 : ℂ) *
      (diagonal fun a => Complex.exp ((θ a : ℂ) * Complex.I))⁻¹ =
      Complex.exp ((θ a : ℂ) * Complex.I + -((θ c : ℂ) * Complex.I)) • Matrix.single a c (1 : ℂ) := by
    rw [hinv]
    ext i j
    simp only [mul_diagonal, diagonal_mul, Matrix.smul_apply, Matrix.single_apply]
    by_cases h' : a = i ∧ c = j
    · obtain ⟨rfl, rfl⟩ := h'
      simp [Complex.exp_add]
    · simp [h']
  rw [LieAct.rep_dRepC hh det_Jm hσ hs (kset_uj hθ), e, hv θ hθ, l2, l1, smul_smul, ← Complex.exp_add]
  congr 2
  simp [Formalism.REAL.root, Pi.single_apply, add_mul, Finset.sum_add_distrib, sub_eq_add_neg]

theorem killed {lam : Fin n → ℝ} (hσ : IsURepOn (UJset ε) σ) {v : H} (hv : v ∈ lowKSub ε lam σ)
    (hs : SmoothVec (lieH (Formalism.REAL.Jm ε)) σ v)
    (hw : IsWtOn (Formalism.REAL.Kset ε) σ (fun a => Formalism.QuantumDeterminants.lowK ε lam (revNeg ε a)) v) {a c : Fin n} (hac : ε a = ε c)
    (hlt : revNeg ε a < revNeg ε c) : dRepC (Formalism.REAL.Jm ε) σ (Matrix.single a c 1) v = 0 := by
  have hε : ∀ b, ε ((revNeg ε).symm b) = ε b := fun b => by
    rw [← eps_revNeg ε ((revNeg ε).symm b), Equiv.apply_symm_apply]
  have h1 := isWtOn_perm hσ (revNeg ε).symm hε (isWtOn_root hσ hs hw a c)
  have e : (fun b => ((fun a => Formalism.QuantumDeterminants.lowK ε lam (revNeg ε a)) + Formalism.REAL.root a c) ((revNeg ε).symm b)) =
      Formalism.QuantumDeterminants.lowK ε lam + Formalism.REAL.root (revNeg ε a) (revNeg ε c) := by
    funext b
    simp [Formalism.REAL.root, Pi.single_apply, Equiv.symm_apply_eq]
  rw [e] at h1
  have h2 := orth_of_not_cdom hσ h1 (not_cdom _ hlt)
  have hK := pM_mem (revNeg ε).symm hε
  have h3 : ∀ x ∈ lowKSub ε lam σ, ⟪dRepC (Formalism.REAL.Jm ε) σ (Matrix.single a c 1) v, x⟫_ℂ = 0 := by
    intro x hx
    rw [← inner_rep hσ hK]
    exact h2 _ (stable_sSup _ hK x hx)
  exact inner_self_eq_zero.1 (inner_dRepC stable_sSup h3 hv hac)

theorem extremal_killed_compact : ∀ (n : ℕ) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] (ε : Fin n → Bool) (lam : Fin n → ℝ) (π : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)), IsURepOn (UJset ε) π → ∀ v ∈ lowKSub ε lam π, SmoothVec {X : Matrix (Fin n) (Fin n) ℂ | Xᴴ * Formalism.REAL.Jm ε + Formalism.REAL.Jm ε * X = 0} π v → IsWtOn (Formalism.REAL.Kset ε) π (fun a => Formalism.QuantumDeterminants.lowK ε lam (revNeg ε a)) v → ∀ a b : Fin n, ((ε a = true ∧ ε b = true ∧ a < b) ∨ (ε a = false ∧ ε b = false ∧ b < a)) → ∀ X ∈ {X : Matrix (Fin n) (Fin n) ℂ | Xᴴ * Formalism.REAL.Jm ε + Formalism.REAL.Jm ε * X = 0}, ∀ Y ∈ {X : Matrix (Fin n) (Fin n) ℂ | Xᴴ * Formalism.REAL.Jm ε + Formalism.REAL.Jm ε * X = 0}, X + Complex.I • Y = Matrix.single a b 1 → dRep π X v + Complex.I • dRep π Y v = 0 := by
  intro n H _ _ ε lam π hπ v hv hs hw a b hab X hX Y hY hE
  rw [← LieAct.dRepC_parts (G := Formalism.REAL.Jm ε) det_Jm hX hY, hE]
  rcases hab with ⟨ha, hb, h⟩ | ⟨ha, hb, h⟩
  · exact killed hπ hv hs hw (ha.trans hb.symm) (by rwa [revNeg_of_pos ε ha, revNeg_of_pos ε hb])
  · exact killed hπ hv hs hw (ha.trans hb.symm) (revNeg_lt ha hb h)

end GlobalTheory.HolRead.KCpt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FactorialMulCoeffCharpolyRevNegEqSum
section
open Polynomial Matrix

namespace GlobalTheory.GoodTop

theorem sum_det_submatrix_image_eq {A : Type} [CommRing A] {r : Type} [Fintype r] [DecidableEq r]
    (M : Matrix r r A) (n : ℕ) (s : Finset r) (hs : s.card = n) :
    ∑ p ∈ Finset.univ.filter (fun p : Fin n → r => Finset.univ.image p = s),
      (M.submatrix p p).det =
    (n.factorial : A) * (M.submatrix (Subtype.val : s → r) (Subtype.val : s → r)).det := by
  classical
  have hc : Fintype.card (Fin n) = Fintype.card s := by simp [hs]
  have h1 : ∑ e : Fin n ≃ s, (M.submatrix (Subtype.val ∘ e) (Subtype.val ∘ e)).det =
      (n.factorial : A) * (M.submatrix (Subtype.val : s → r) (Subtype.val : s → r)).det := by
    have : ∀ e : Fin n ≃ s, (M.submatrix (Subtype.val ∘ e) (Subtype.val ∘ e)).det =
        (M.submatrix (Subtype.val : s → r) (Subtype.val : s → r)).det := by
      intro e
      rw [← Matrix.submatrix_submatrix, Matrix.det_submatrix_equiv_self]
    simp only [this, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    rw [Fintype.card_equiv (Fintype.equivOfCardEq hc), Fintype.card_fin]
  rw [← h1]
  symm
  refine Finset.sum_bij (fun e _ => Subtype.val ∘ e) ?_ ?_ ?_ (fun _ _ => rfl)
  · intro e _
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    ext x
    simp only [Finset.mem_image, Finset.mem_univ, true_and, Function.comp]
    constructor
    · rintro ⟨a, rfl⟩
      exact (e a).2
    · intro hx
      exact ⟨e.symm ⟨x, hx⟩, by simp⟩
  · intro e _ e' _ h
    ext i
    exact congrFun h i
  · intro p hp
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp
    let f : Fin n → s := fun i => ⟨p i, hp ▸ Finset.mem_image_of_mem p (Finset.mem_univ i)⟩
    have hf : Function.Surjective f := by
      rintro ⟨x, hx⟩
      rw [← hp] at hx
      obtain ⟨a, -, rfl⟩ := Finset.mem_image.mp hx
      exact ⟨a, rfl⟩
    have hb : Function.Bijective f :=
      (Fintype.bijective_iff_surjective_and_card f).mpr ⟨hf, hc⟩
    exact ⟨Equiv.ofBijective f hb, Finset.mem_univ _, rfl⟩

theorem factorial_mul_coeff_charpolyRev_neg {A : Type} [CommRing A] {r : Type} [Fintype r]
    [DecidableEq r] (M : Matrix r r A) (n : ℕ) :
    (n.factorial : A) * (Matrix.charpolyRev (-M)).coeff n =
      ∑ p : Fin n → r, ∑ π : Equiv.Perm (Fin n),
        ((Equiv.Perm.sign π : ℤ) : A) * ∏ i, M (p i) (p (π i)) := by
  classical
  have hrev : (-M).charpolyRev = det (1 + (X : A[X]) • M.map C) := by
    simp only [charpolyRev, sub_eq_add_neg]
    congr 2
    rw [Matrix.map_neg C (map_neg C) M, smul_neg, neg_neg]
  have hdet : ∀ p : Fin n → r, ∑ π : Equiv.Perm (Fin n),
      ((Equiv.Perm.sign π : ℤ) : A) * ∏ i, M (p i) (p (π i)) = (M.submatrix p p).det := by
    intro p
    rw [← Matrix.det_transpose, Matrix.det_apply']
    rfl
  rw [hrev, coeff_det_one_add_X_smul_eq_sum_minors, Finset.mul_sum]
  simp only [hdet]
  rw [← Finset.sum_filter_of_ne (s := Finset.univ)
    (p := fun p : Fin n → r => Finset.univ.image p ∈ (Finset.univ : Finset r).powersetCard n)]
  · rw [← Finset.sum_fiberwise_of_maps_to (t := (Finset.univ : Finset r).powersetCard n)
      (g := fun p : Fin n → r => Finset.univ.image p) (fun p hp => (Finset.mem_filter.mp hp).2)]
    refine Finset.sum_congr rfl fun s hs => ?_
    rw [← sum_det_submatrix_image_eq M n s (Finset.mem_powersetCard.mp hs).2]
    refine Finset.sum_congr ?_ fun _ _ => rfl
    ext p
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨fun h => ⟨h ▸ hs, h⟩, fun h => h.2⟩
  · intro p _ hp
    have hinj : Function.Injective p := by
      intro i j hij
      by_contra hne
      exact hp (Matrix.det_zero_of_row_eq hne (by ext k; simp [hij]))
    rw [Finset.mem_powersetCard, Finset.card_image_of_injective _ hinj]
    simp

end GlobalTheory.GoodTop
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteClosedTorusSubgroupWithoutPiTorsion
section
open CategoryTheory AlgebraicGeometry NumberField MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Topology
attribute [local instance] Over.cartesianMonoidalCategory CategoryTheory.Hom.group

namespace GlobalTheory

namespace TorusPiTorsion

open ReciprocityTheory.ChartRestriction.G.Semi.Rosenlicht
attribute [local instance] zuAlgebra

variable {k : Type} [Field k] {X : Type} [AddCommGroup X]

theorem val_splitTorusPoint (t : Multiplicative X →* kˣ) (b : X) :
    SplitTorus.val (splitTorusPoint t) b =
      (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom (t (Multiplicative.ofAdd b) : k) := by
  have h : (torusIso k X).hom.appTop.hom (chi X b) =
      (Scheme.ΓSpecIso (CommRingCat.of (AddMonoidAlgebra k X))).inv.hom (AddMonoidAlgebra.single b 1) := by
    have := torusGamma_chi k X b
    rw [torusGamma, CommRingCat.comp_apply] at this
    rw [← this]
    simp
  rw [SplitTorus.val_eq, splitTorusPoint_left, Scheme.Hom.comp_appTop, CommRingCat.comp_apply, h,
    SplitTorus.specMap_appTop_apply]
  simp [torusEval_single]

theorem splitTorusPoint_comp_torusMap (t : Multiplicative X →* kˣ) (φ : X →+ X) :
    splitTorusPoint t ≫ SplitTorus.torusMap (Sp k) φ =
      splitTorusPoint (t.comp (AddMonoidHom.toMultiplicative φ)) :=
  SplitTorus.hom_ext fun b => by
    rw [SplitTorus.val_comp_torusMap, val_splitTorusPoint, val_splitTorusPoint]
    rfl

end TorusPiTorsion
end GlobalTheory

namespace GlobalTheory
namespace TorusPiTorsion

theorem finite_of_isClosed_torusZariski_of_smul {k : Type} [Field k] [IsAlgClosed k] [CharZero k]
    {O : Type} [CommRing O] {X : Type} [AddCommGroup X] [Module O X] [Module.Finite ℤ X]
    (hdiv : ∀ r : O, r ≠ 0 → ∃ m : ℤ, m ≠ 0 ∧ r ∣ (m : O)) {π : O} (hπ0 : π ≠ 0)
    (hπ : ¬ IsUnit π) {H : Subgroup (Multiplicative X →* kˣ)}
    (hH : IsClosed[torusZariski k X] (H : Set (Multiplicative X →* kˣ)))
    (hstab : ∀ (a : O), ∀ s ∈ H,
      s.comp (AddMonoidHom.toMultiplicative (DistribMulAction.toAddMonoidHom X a)) ∈ H)
    (htors : ∀ s ∈ H,
      s.comp (AddMonoidHom.toMultiplicative (DistribMulAction.toAddMonoidHom X π)) = 1 → s = 1) :
    Finite H := by
  let K : Submodule O X :=
    { carrier := {x | ∀ s ∈ H, s (Multiplicative.ofAdd x) = 1}
      add_mem' := fun {a b} ha hb s hs => by rw [ofAdd_add, map_mul, ha s hs, hb s hs, _root_.mul_one]
      zero_mem' := fun s _ => map_one s
      smul_mem' := fun a x hx s hs => hx _ (hstab a s hs) }
  have hK : ∀ x, x ∈ K ↔ ∀ s ∈ H, s (Multiplicative.ofAdd x) = 1 := fun x => Iff.rfl
  let N : Submodule O X := K ⊔ Ideal.span {π} • ⊤
  have hπN : ∀ x : X, π • x ∈ N := fun x =>
    Submodule.mem_sup_right (Submodule.smul_mem_smul (Ideal.mem_span_singleton_self _) trivial)
  haveI : Module.Finite O X := Module.Finite.of_restrictScalars_finite ℤ O X
  have hN : (⊤ : Submodule O X) ≤ N := by
    intro x _
    by_contra hx
    obtain ⟨m, hm0, c, hc⟩ := hdiv π hπ0
    have hmQ : ∀ q : X ⧸ N, m • q = 0 := fun q => by
      obtain ⟨y, rfl⟩ := N.mkQ_surjective q
      rw [← Int.cast_smul_eq_zsmul O, ← map_smul, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero,
        hc, mul_smul]
      exact hπN _
    have hmQ' : ∀ q : Multiplicative (X ⧸ N), q ^ m.natAbs = 1 := fun q => by
      have h1 : (m.natAbs : ℤ) • q.toAdd = 0 := by
        rcases Int.natAbs_eq m with h | h
        · rw [← h]; exact hmQ _
        · rw [show (m.natAbs : ℤ) = -m by omega, neg_smul, hmQ, neg_zero]
      rw [natCast_zsmul] at h1
      exact congrArg Multiplicative.ofAdd h1
    haveI : Module.Finite ℤ (X ⧸ N) :=
      Module.Finite.of_surjective N.mkQ.toAddMonoidHom.toIntLinearMap N.mkQ_surjective
    haveI : Finite (X ⧸ N) := Module.finite_of_fg_torsion _ fun q =>
      ⟨⟨m, mem_nonZeroDivisors_of_ne_zero hm0⟩, hmQ q⟩
    have hexp : Monoid.exponent (Multiplicative (X ⧸ N)) ≠ 0 := Monoid.exponent_ne_zero_of_finite
    haveI : NeZero ((Monoid.exponent (Multiplicative (X ⧸ N)) : ℕ) : k) := ⟨Nat.cast_ne_zero.2 hexp⟩
    obtain ⟨φ, hφ⟩ := CommGroup.exists_apply_ne_one_of_hasEnoughRootsOfUnity
      (Multiplicative (X ⧸ N)) k (a := Multiplicative.ofAdd (N.mkQ x))
      (by simpa using hx)
    let t : Multiplicative X →* kˣ := φ.comp (AddMonoidHom.toMultiplicative N.mkQ.toAddMonoidHom)
    have ht : ∀ y, t y = φ (Multiplicative.ofAdd (N.mkQ y.toAdd)) := fun y => rfl
    have htH : t ∈ H := mem_of_isClosed_torusZariski hH fun y hy => by
      have : N.mkQ y.toAdd = 0 := by
        rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
        exact Submodule.mem_sup_left ((hK _).2 hy)
      rw [ht, this, ofAdd_zero, map_one]
    have ht1 : t = 1 := htors t htH (MonoidHom.ext fun y => by
      have : N.mkQ (π • y.toAdd) = 0 := by
        rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
        exact hπN _
      change t (Multiplicative.ofAdd (π • y.toAdd)) = 1
      rw [ht, toAdd_ofAdd, this, ofAdd_zero, map_one])
    exact hφ (by simpa [ht] using DFunLike.congr_fun ht1 (Multiplicative.ofAdd x))
  obtain ⟨r, hr, hrK⟩ := Submodule.exists_sub_one_mem_and_smul_le_of_fg_of_le_sup
    (I := Ideal.span {π}) (N := K) (N' := ⊤) (P := ⊤) Module.Finite.fg_top le_rfl hN
  have hr0 : r ≠ 0 := by
    rintro rfl
    apply hπ
    rw [zero_sub, Ideal.mem_span_singleton] at hr
    exact isUnit_of_dvd_one ((dvd_neg).1 hr)
  obtain ⟨m, hm0, c, hc⟩ := hdiv r hr0
  have hmK : ∀ x : X, m • x ∈ K := fun x => by
    rw [← Int.cast_smul_eq_zsmul O, hc, mul_smul]
    exact hrK (Submodule.smul_mem_pointwise_smul _ r ⊤ trivial)
  have hmH : ∀ s ∈ H, s ^ m.natAbs = 1 := fun s hs => by
    have h1 : s ^ m = 1 := MonoidHom.ext fun y => by
      have := (hK _).1 (hmK y.toAdd) s hs
      rw [ofAdd_zsmul, map_zpow, ofAdd_toAdd] at this
      rw [MonoidHom.zpow_apply, this, MonoidHom.one_apply]
    exact pow_natAbs_eq_one.2 h1
  exact (finite_setOf_pow_eq_one_torus (R := k) (X := X) (Int.natAbs_ne_zero.2 hm0)).subset
    (t := (H : Set (Multiplicative X →* kˣ))) fun s hs => hmH s hs

end TorusPiTorsion
end GlobalTheory

namespace GlobalTheory
namespace TorusPiTorsion

open ReciprocityTheory.ChartRestriction.G.Semi.Rosenlicht

theorem exists_int_dvd (E : Type) [Field E] [NumberField E] (r : 𝓞 E) (hr : r ≠ 0) :
    ∃ m : ℤ, m ≠ 0 ∧ r ∣ (m : 𝓞 E) := by
  refine ⟨(Ideal.absNorm (Ideal.span {r}) : ℤ), ?_, ?_⟩
  · rw [Nat.cast_ne_zero, Ne, Ideal.absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot]
    exact hr
  · rw [Int.cast_natCast, ← Ideal.mem_span_singleton]
    exact Ideal.absNorm_mem _

theorem finite_of_isClosed_of_no_pi_torsion :
    ∀ (E : Type) [Field E] [NumberField E] (k : Type) [Field k] [IsAlgClosed k] [CharZero k]
      (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X]
      (act : OAct (𝓞 E) (splitTorus (Sp k) X)) (π : 𝓞 E), π ≠ 0 → ¬ IsUnit π →
      ∀ (C : Subgroup (𝟙_ (Over (Sp k)) ⟶ splitTorus (Sp k) X))
        (Z : Set (splitTorus (Sp k) X).left), IsClosed Z → (∀ x, x ∈ C ↔ Set.range x.left ⊆ Z) →
        (∀ (a : 𝓞 E), ∀ x ∈ C, x ≫ act.act a ∈ C) → (∀ x ∈ C, x ≫ act.act π = 1 → x = 1) →
        Finite C := by
  intro E _ _ k _ _ _ X _ _ _ act π hπ0 hπ C Z hZ hC hstab htors
  have hφ : ∀ a, ∃ φ : X →+ X, act.act a = SplitTorus.torusMap (Sp k) φ := fun a => by
    haveI := act.hom a
    exact SplitTorus.exists_eq_torusMap _
  choose φ hφ using hφ
  have hinj : ∀ {ψ ψ' : X →+ X}, SplitTorus.torusMap (Sp k) ψ = SplitTorus.torusMap (Sp k) ψ' →
      ψ = ψ' := fun h => SplitTorus.torusMap_injective h
  have hone : φ 1 = AddMonoidHom.id X := hinj (by rw [← hφ, act.one, SplitTorus.torusMap_id])
  have hmul : ∀ a b, φ (a * b) = (φ a).comp (φ b) := fun a b =>
    hinj (by rw [← hφ, SplitTorus.torusMap_comp, ← hφ, ← hφ, act.mul])
  have hadd : ∀ a b, φ (a + b) = φ a + φ b := fun a b =>
    hinj (by rw [← hφ, SplitTorus.torusMap_add, ← hφ, ← hφ, act.add])
  let ρ : 𝓞 E →+* AddMonoid.End X :=
    { toFun := φ
      map_one' := hone
      map_mul' := hmul
      map_zero' := by
        have h := hadd 0 0
        rw [add_zero] at h
        have h' : φ 0 = 0 := by simpa using h.symm
        exact h'
      map_add' := hadd }
  letI : Module (𝓞 E) X := Module.compHom X ρ
  have hsmul : ∀ (a : 𝓞 E) (x : X), a • x = φ a x := fun a x => rfl
  let e := splitTorusPointEquiv k X
  have hpt : ∀ (s : Multiplicative X →* kˣ) (a : 𝓞 E), e s ≫ act.act a =
      e (s.comp (AddMonoidHom.toMultiplicative (DistribMulAction.toAddMonoidHom X a))) := by
    intro s a
    rw [hφ a]
    exact splitTorusPoint_comp_torusMap s (φ a)
  let H := C.comap e.toMonoidHom
  have hcl : IsClosed[torusZariski k X] (H : Set (Multiplicative X →* kˣ)) := by
    refine isClosed_induced_iff.2 ⟨(torusIso k X).hom ⁻¹' Z,
      hZ.preimage (torusIso k X).hom.continuous, ?_⟩
    ext t
    change _ ↔ splitTorusPoint t ∈ C
    rw [hC, range_splitTorusPoint_left, Set.singleton_subset_iff]
    rfl
  have h := finite_of_isClosed_torusZariski_of_smul (k := k) (O := 𝓞 E) (X := X)
    (exists_int_dvd E) hπ0 hπ hcl
    (fun a s hs => by
      change e _ ∈ C
      rw [← hpt]
      exact hstab a _ hs)
    (fun s hs h1 => e.injective (by
      rw [map_one]
      refine htors _ hs ?_
      change e s ≫ act.act π = 1
      rw [hpt, h1, map_one]))
  have e' : H ≃ C := e.toEquiv.subtypeEquiv fun _ => Iff.rfl
  exact e'.finite_iff.1 h

end TorusPiTorsion
end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteFrameCoeffRingQuotientPrime
section
open GlobalTheory.ExpFrame Formalism.BasicNotions.Loc GlobalTheory.Cyc

namespace GlobalTheory.FrameQuot

theorem finite_quot_prime (l : ℕ) [Fact l.Prime] (ι : Type) (N : ℕ) (F : Frame l ι N) (hF : F.Ok) :
    Finite (F.O ⧸ Ideal.span {((l : ℕ) : F.O)}) := by
  obtain ⟨hinj, L, hL, hrange⟩ := hF.ring
  haveI := hL
  have hmem : ∀ x : F.O, F.emb x ∈ L ∧ ‖F.emb x‖ ≤ 1 := fun x => by
    have hx : F.emb x ∈ Set.range F.emb := ⟨x, rfl⟩
    rw [hrange] at hx
    exact hx
  let f : F.O →+* integralClosure ℤ_[l] L :=
    { toFun := fun x => ⟨⟨F.emb x, (hmem x).1⟩,
        (GlobalTheory.mem_integralClosure_padicInt_iff L ⟨F.emb x, (hmem x).1⟩).2 (hmem x).2⟩
      map_one' := Subtype.ext (Subtype.ext (map_one F.emb))
      map_mul' := fun x y => Subtype.ext (Subtype.ext (map_mul F.emb x y))
      map_zero' := Subtype.ext (Subtype.ext (map_zero F.emb))
      map_add' := fun x y => Subtype.ext (Subtype.ext (map_add F.emb x y)) }
  have hsurj : Function.Surjective f := by
    rintro ⟨⟨y, hyL⟩, hy⟩
    have hn := (GlobalTheory.mem_integralClosure_padicInt_iff L ⟨y, hyL⟩).1 hy
    have hy' : y ∈ Set.range F.emb := by
      rw [hrange]
      exact ⟨hyL, hn⟩
    obtain ⟨x, rfl⟩ := hy'
    exact ⟨x, rfl⟩
  have hbij : Function.Bijective f :=
    ⟨fun x y h => hinj (congrArg (fun z : integralClosure ℤ_[l] L => ((z : L) : PadicAlgCl l)) h), hsurj⟩
  let e := RingEquiv.ofBijective f hbij
  have hfin : Finite (integralClosure ℤ_[l] L ⧸
      Ideal.span {((l : ℕ) : integralClosure ℤ_[l] L) ^ 1}) :=
    GlobalTheory.LocalIntegers.finite_quotient_pow l (integralClosure ℤ_[l] L) 1
  have hIJ : Ideal.span {((l : ℕ) : integralClosure ℤ_[l] L) ^ 1} =
      (Ideal.span {((l : ℕ) : F.O)}).map (e : F.O →+* integralClosure ℤ_[l] L) := by
    rw [Ideal.map_span, Set.image_singleton, map_natCast, pow_one]
  exact Finite.of_equiv _ (Ideal.quotientEquiv _ _ e hIJ).symm.toEquiv

end GlobalTheory.FrameQuot
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteLeftCosetRepresentatives
section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount
open scoped TensorProduct Classical

noncomputable section

namespace GlobalTheory.OrbFinCmd

theorem exists_finset_mul_eq_of_relIndex {H : Type} [Group H] (K : Subgroup H) (s : H)
    (h : (K.map (MulAut.conj s).toMonoidHom).relIndex K ≠ 0) :
    ∃ S : Finset H, ∀ k ∈ K, ∃ s' ∈ S, ∃ k' ∈ K, k * s = s' * k' := by
  set L := K.map (MulAut.conj s).toMonoidHom with hL
  haveI : Finite (K ⧸ L.subgroupOf K) := by
    haveI : (L.subgroupOf K).FiniteIndex := ⟨h⟩
    exact Subgroup.finite_quotient_of_finiteIndex
  haveI : Fintype (K ⧸ L.subgroupOf K) := Fintype.ofFinite _
  refine ⟨Finset.univ.image fun q : K ⧸ L.subgroupOf K => ((Quotient.out q : K) : H) * s, ?_⟩
  intro k hk
  set q : K ⧸ L.subgroupOf K := QuotientGroup.mk ⟨k, hk⟩
  have hq : (Quotient.out q)⁻¹ * (⟨k, hk⟩ : K) ∈ L.subgroupOf K := by
    rw [← QuotientGroup.eq, QuotientGroup.out_eq']
  rw [Subgroup.mem_subgroupOf] at hq
  obtain ⟨x, hx, hxe⟩ := hq
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_inv] at hxe
  refine ⟨((Quotient.out q : K) : H) * s, Finset.mem_image_of_mem _ (Finset.mem_univ _), x, hx, ?_⟩
  have : k = ((Quotient.out q : K) : H) * (s * x * s⁻¹) := by
    rw [hxe, mul_inv_cancel_left]
  rw [this]
  group

end GlobalTheory.OrbFinCmd

open GlobalTheory.OrbFinCmd in

theorem GlobalTheory.orbFin_KHT_cmd :
    ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (r : ℕ), 0 < r → ∀ s : Gr G r, ∃ S : Finset (Gr G r),
      ∀ k ∈ KHT p G.m G.n r G.Fw, ∃ s' ∈ S, ∃ k' ∈ KHT p G.m G.n r G.Fw, k * s = s' * k' := by
  intro p _ G r hr s
  exact exists_finset_mul_eq_of_relIndex _ s ((GlobalTheory.T.unitarySimilitudeIntegralSubgroup_commensurated_frobenius p G r hr).1 s).1
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteZetaIntegralEulerProductOfPartialLStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.AdelicScalar GlobalTheory.LiftRows GlobalTheory.LowRow
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finiteZetaIntegral_eulerProduct_of_partialL : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), FiniteZetaL R F → FiniteZetaC R F := by
  first | exact @GlobalTheory.LowRow.finiteZetaC_of_finiteZetaL | exact GlobalTheory.LowRow.finiteZetaC_of_finiteZetaL | (intros; apply GlobalTheory.LowRow.finiteZetaC_of_finiteZetaL <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagOrbitMapSurjectiveStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Matrix
open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.FlagZ GlobalTheory.FlagPoly Formalism.DegreeFormula
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flag_orbit_map_surjective : ∀ (ι κ : Type) [Fintype ι] [Finite κ] (N : ℕ) (a : κ → ι) (l : κ → Fin (N + 1)), Function.Surjective (orbit a l) := by
  first | exact @GlobalTheory.FlagZ.surjective_orbit | exact GlobalTheory.FlagZ.surjective_orbit | (intros; apply GlobalTheory.FlagZ.surjective_orbit <;> assumption)
end

