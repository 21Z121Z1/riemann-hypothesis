import Mathlib
import Formalism.LocalToGlobal.CharacterGerms.Bundle0016
import Formalism.LocalToGlobal.CharacterGerms.Bundle0006
import Formalism.LocalToGlobal.CharacterGerms.CoeffIterateZero
import Formalism.FormalGroupLog.FormalGroupLogProofs.ChainRule
import Formalism.LocalToGlobal.CharacterGerms.Bundle0013
import Formalism.LocalToGlobal.CharacterGerms.RowTieSelf
import Formalism.LocalToGlobal.CharacterGerms.Bundle0011
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.StChartF
import Development.AbelianVarietyTheory.Definitions.TeichmullerDepth.HasTeich
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.FrobeniusLiftEmbeddingsUnit
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.GaugeDerivEqPairingOfIntegralGaugedLaw
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle0039
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.IntegralGaugeBilinearTermOfTypeNe
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.IsIntegralGaugedFormalGroupLawSelfConjugateSquar
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle0040
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ToricPointExtensionAbelianPartFormalGroupHom
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.StChartFH
import ReciprocityTheory.DualLattices.Bundle0026
import ReciprocityTheory.DualLattices.Bundle0015
import ReciprocityTheory.DualLattices.Bundle0033
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.UniversalCharts.LePreimageOfNil
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Clauses
import Development.AbelianVarietyTheory.Definitions.TeichmullerDepth.IsEigBasisIff

-- bundled from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.CharacterBlocksAttainBound
section
noncomputable section
open scoped BigOperators
open Classical

namespace GlobalTheory.CharBlock

open Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds MvPowerSeries

variable {C : Type} [Field C]

def IsExp {σ : Type} (y : σ → C) (F : MvPowerSeries σ C) : Prop :=
  constantCoeff F = 1 ∧ ∀ w, pderiv C w F = y w • F

theorem IsExp.one {σ : Type} : IsExp (fun _ : σ => (0 : C)) 1 := ⟨by simp, fun w => by simp⟩

theorem IsExp.mul {σ : Type} {y y' : σ → C} {F F' : MvPowerSeries σ C} (h : IsExp y F)
    (h' : IsExp y' F') : IsExp (fun w => y w + y' w) (F * F') := by
  refine ⟨by rw [map_mul, h.1, h'.1, one_mul], fun w => ?_⟩
  rw [Derivation.leibniz, h.2, h'.2]
  simp only [smul_eq_mul, add_smul, mul_smul_comm]
  rw [add_comm, mul_comm F' F]

theorem IsExp.prod {σ α : Type} (s : Finset α) {y : α → σ → C} {F : α → MvPowerSeries σ C}
    (h : ∀ i, IsExp (y i) (F i)) : IsExp (fun w => ∑ i ∈ s, y i w) (∏ i ∈ s, F i) := by
  induction s using Finset.induction_on with
  | empty => simpa using IsExp.one
  | insert a s ha ih =>
    simp only [Finset.prod_insert ha, Finset.sum_insert ha]
    exact (h a).mul ih

theorem IsExp.subst {σ τ : Type} [Fintype σ] [Finite τ] {y : σ → C} {F : MvPowerSeries σ C}
    (h : IsExp y F) (e : σ → τ) :
    IsExp (fun t => ∑ j, if e j = t then y j else 0)
      (F.subst fun j => (X (e j) : MvPowerSeries τ C)) := by
  have hs : HasSubst (fun j => (X (e j) : MvPowerSeries τ C)) :=
    hasSubst_of_constantCoeff_zero (by simp)
  constructor
  · have := rename_eq_subst (R := C) (f := e) (p := F)
    have h2 := constantCoeff_rename (R := C) (f := e) F
    rw [this, h.1] at h2
    exact h2
  · intro w
    rw [Formalism.G.LogCR.pderiv_subst (by simp), Finset.sum_smul]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [h.2, subst_smul hs]
    by_cases hj : e j = w
    · subst hj; simp
    · simp [hj, pderiv_X_of_ne hj]

theorem IsExp.coeff {σ : Type} {y : σ → C} {F : MvPowerSeries σ C} (h : IsExp y F) :
    ∀ (n : ℕ) (m : σ →₀ ℕ), m.degree = n →
      (mfact m : C) * coeff m F = m.prod fun s k => y s ^ k := by
  intro n
  induction n with
  | zero =>
    intro m hm
    rw [Finsupp.degree_eq_zero_iff] at hm
    subst hm
    simp [mfact, h.1]
  | succ n ih =>
    intro m hm
    have hne : m ≠ 0 := by rintro rfl; simp at hm
    obtain ⟨w, hw⟩ := Finsupp.ne_iff.1 hne
    obtain ⟨m', rfl⟩ : ∃ m', m = m' + Finsupp.single w 1 := by
      refine ⟨m - Finsupp.single w 1, ?_⟩
      rw [tsub_add_cancel_of_le]
      rw [Finsupp.single_le_iff]
      simp at hw; omega
    have hd : m'.degree = n := by
      rw [map_add, Finsupp.degree_single] at hm; omega
    have h1 := congrArg (MvPowerSeries.coeff m') (h.2 w)
    rw [coeff_pderiv, coeff_smul] at h1
    have h2 : mfact (m' + Finsupp.single w 1) = (m' w + 1) * mfact m' := by
      unfold mfact
      have e1 := Finsupp.mul_prod_erase' (m' + Finsupp.single w 1) w (fun _ k => k.factorial) (by simp)
      have e2 := Finsupp.mul_prod_erase' m' w (fun _ k => k.factorial) (by simp)
      rw [← e1, ← e2, Finsupp.erase_add, Finsupp.erase_single, add_zero]
      simp [Nat.factorial_succ, mul_assoc]
    rw [Finsupp.prod_add_index' (by simp) (fun _ _ _ => pow_add _ _ _), ← ih m' hd, h2,
      Finsupp.prod_single_index (by simp)]
    push_cast
    linear_combination (mfact m' : C) * h1

theorem IsExp.jet {σ : Type} {y : σ → C} {F : MvPowerSeries σ C} (h : IsExp y F)
    (P : MvPolynomial σ C) : jetAt0 P F = MvPolynomial.eval y P := by
  unfold jetAt0
  rw [MvPolynomial.eval_eq]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [mul_assoc, h.coeff _ m rfl]
  rfl

theorem coeff_mvExp {σ : Type} (h : MvPowerSeries σ C) (m : σ →₀ ℕ) :
    coeff m (mvExp h) = ∑ k ∈ Finset.range (m.degree + 1), coeff m (h ^ k) / (k.factorial : C) := rfl

theorem mvExp_zero {σ : Type} : mvExp (0 : MvPowerSeries σ C) = 1 := by
  ext m
  rw [coeff_mvExp, Finset.sum_range_succ']
  simp

theorem isExp_mvExp [CharZero C] {σ : Type} [Fintype σ] (y : σ → C) :
    IsExp y (mvExp (∑ x, y x • (X x : MvPowerSeries σ C))) := by
  constructor
  · rw [← coeff_zero_eq_constantCoeff_apply, coeff_mvExp]; simp
  · intro w
    ext m
    have hL : pderiv C w (∑ x, y x • (X x : MvPowerSeries σ C)) = MvPowerSeries.C (y w) := by
      rw [map_sum, Finset.sum_eq_single w]
      · simp [smul_eq_C_mul]
      · intro b _ hb; simp [pderiv_X_of_ne hb]
      · simp
    rw [coeff_pderiv, coeff_smul, coeff_mvExp, coeff_mvExp, map_add, Finsupp.degree_single,
      Finset.sum_range_succ', Finset.mul_sum, add_mul, Finset.sum_mul]
    have h0 : MvPowerSeries.coeff (m + Finsupp.single w 1)
        ((∑ x, y x • (X x : MvPowerSeries σ C)) ^ 0) = 0 := by
      rw [pow_zero, coeff_one, if_neg]
      intro h
      have := DFunLike.congr_fun h w
      simp at this
    rw [h0, zero_div, zero_mul, add_zero]
    refine Finset.sum_congr rfl fun k _ => ?_
    have h1 := coeff_pderiv (i := w) ((∑ x, y x • (X x : MvPowerSeries σ C)) ^ (k + 1)) m
    rw [pderiv_pow, hL, Nat.add_sub_cancel, ← map_natCast (MvPowerSeries.C (σ := σ) (R := C)),
      coeff_mul_C, coeff_C_mul] at h1
    have hk : (k.factorial : C) ≠ 0 := by exact_mod_cast k.factorial_ne_zero
    have hk1 : ((k + 1 : ℕ) : C) ≠ 0 := by exact_mod_cast k.succ_ne_zero
    rw [div_mul_eq_mul_div, ← h1, Nat.factorial_succ]
    push_cast at hk1 ⊢
    field_simp

variable {V : VF C} {d : ℕ} [NeZero d] {I J : Fin 2 → Type}
  [∀ g, Fintype (I g)] [∀ g, Fintype (J g)]

def stdSys {I J : Type} [Fintype I] [Fintype J] (X : Cart V d I J) : Sys X where
  tan := fun c => Pi.single c 1
  cur := fun c => X.std c
  curve := fun c => X.std_spec c
  unimod := by
    have : (Matrix.of fun c : I => (Pi.single c 1 : I → C)) = 1 := by
      ext a b
      simp [Matrix.one_apply, Pi.single_apply, eq_comm]
    rw [this, Matrix.det_one, AddValuation.map_one]

theorem val_eq [CharZero C] (hL : Fin 2 → ZMod d → ZMod d → MvPowerSeries (WV I) C) (g : Fin 2)
    {n r : ℕ} (hn : n ≤ r) (en : Fin r → I g) (y : Fin n → I g → C) (u : ℕ) :
    ValOf hL (MvPolynomial.rename (fun x : Fin n × Fin r => ((x.1, ⟨g, en x.2⟩) : Fin n × WV I))
        (minorK C n r n) ^ u) (fun _ => none)
      (fun ρ => upG g (mvExp (∑ x : I g, y ρ x • (X x : MvPowerSeries (I g) C)))) =
    (Matrix.of fun ρ c : Fin n => y ρ (en (Fin.castLE hn c))).det ^ u := by
  unfold ValOf
  have h0 : ∀ ρ : Fin n, mvExp (rowCopy ρ (0 : MvPowerSeries (WV I) C)) = 1 := by
    intro ρ
    have : rowCopy ρ (0 : MvPowerSeries (WV I) C) = 0 := by
      unfold rowCopy
      have hs : HasSubst (fun w : WV I => (X (ρ, w) : MvPowerSeries (Fin n × WV I) C)) :=
        hasSubst_of_constantCoeff_zero (by simp)
      rw [← coe_substAlgHom hs, map_zero]
    rw [this, mvExp_zero]
  simp only [h0, mul_one]
  have h1 := IsExp.prod Finset.univ fun ρ : Fin n =>
    ((isExp_mvExp (y ρ)).subst fun x : I g => (⟨g, x⟩ : WV I)).subst
      fun w : WV I => ((ρ, w) : Fin n × WV I)
  refine (h1.jet _).trans ?_
  rw [map_pow, MvPolynomial.eval_rename, minorK, dif_pos ⟨le_rfl, hn⟩, RingHom.map_det]
  congr 2
  ext ρ c
  simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, MvPolynomial.eval_X,
    Function.comp_apply, Fin.castLE_refl, Prod.mk.injEq]
  rw [Finset.sum_eq_single ρ, Finset.sum_eq_single (⟨g, en (Fin.castLE hn c)⟩ : WV I),
    Finset.sum_eq_single (en (Fin.castLE hn c))]
  all_goals simp +contextual

theorem core (X : RowData C V d I J) (g : Fin 2) (a : ZMod d) (ha : X.big g a) {r : ℕ}
    (hn : X.n ≤ r) (en : Fin r → I g) (hinj : Function.Injective en)
    (hty : ∀ c, (X.G g).ty (Sum.inl (en c)) = a) (u : ℕ) :
    ∃ (S : ∀ g, Sys (X.G g)) (t : ∀ g, I g → MvPowerSeries (I g) C), (∀ g, (S g).IsT (t g)) ∧
      ∃ gr : Fin X.n → MvPowerSeries (WV I) C, (∀ ρ, gr ρ ∈ IntGerm V t) ∧
        (X.Alt → V.v (ValOf X.hL (MvPolynomial.rename
          (fun x : Fin X.n × Fin r => ((x.1, ⟨g, en x.2⟩) : Fin X.n × WV I))
          (minorK C X.n r X.n) ^ u) (fun _ => none) gr) ≤
          (((u : ℝ) * (X.n * gam V.l + X.m / ((V.l : ℝ) - 1)) : ℝ) : WithTop ℝ)) ∧
        ((∀ a, X.big g a) → V.v (ValOf X.hL (MvPolynomial.rename
          (fun x : Fin X.n × Fin r => ((x.1, ⟨g, en x.2⟩) : Fin X.n × WV I))
          (minorK C X.n r X.n) ^ u) (fun _ => none) gr) ≤
          (((u : ℝ) * (X.m / ((V.l : ℝ) - 1)) : ℝ) : WithTop ℝ)) := by
  haveI := X.charZero
  choose t ht _ using fun g => tExistsUnique (X.G g) (stdSys (X.G g))
  have hint : ∀ (c x : I g), V.Ge 0 ((Pi.single c 1 : I g → C) x) := by
    intro c x
    rw [Pi.single_apply]
    split_ifs
    · exact VF.Ge.one
    · exact VF.Ge.zero 0
  obtain ⟨y, -, hy, h1, h2⟩ := X.CH g a ha (fun c => Pi.single (en (Fin.castLE hn c)) 1)
    ⟨fun c x => hint _ _, fun x c => (Pi.single (en (Fin.castLE hn c)) 1 : I g → C) x,
      fun x c => hint _ _, fun c c' => by
        simp [Pi.single_apply, hinj.eq_iff, (Fin.castLE_injective hn).eq_iff, eq_comm]⟩
    (fun c x hx => Pi.single_eq_of_ne (fun h => hx (by rw [h]; exact hty _)) _)
  have key : ∀ b : ℝ, V.v (Matrix.of fun ρ c : Fin X.n =>
        ∑ x, y ρ x * (Pi.single (en (Fin.castLE hn c)) 1 : I g → C) x).det ≤ (b : WithTop ℝ) →
      V.v ((Matrix.of fun ρ c : Fin X.n => y ρ (en (Fin.castLE hn c))).det ^ u) ≤
        (((u : ℝ) * b : ℝ) : WithTop ℝ) := by
    intro b hb
    simp only [Pi.single_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ,
      if_true] at hb
    rw [AddValuation.map_pow, ← nsmul_eq_mul, WithTop.coe_nsmul]
    exact nsmul_le_nsmul_right hb u
  refine ⟨fun g => stdSys (X.G g), t, ht, _, hy _ t ht, fun h => ?_, fun h => ?_⟩
  · rw [val_eq X.hL g hn en y u]
    simpa [RowData.m] using key _ (h1 h)
  · rw [val_eq X.hL g hn en y u]
    simpa [RowData.m] using key _ (h2 h)

theorem chSupply : CHSupply ∧ RF.CHSupply := by
  constructor
  · intro C _ V d _ I J _ _ X F g a ha u
    have hn : X.n ≤ X.rk g a := by
      unfold RowData.rk; rw [X.rk_big g a ha]; omega
    obtain ⟨S, t, ht, gr, hgr, h1, h2⟩ := core X g a ha hn (F.en g a) (F.en_inj g a) (F.en_ty g a) u
    exact ⟨fun h => ⟨S, t, ht, gr, hgr, h1 h⟩, fun h => ⟨S, t, ht, gr, hgr, h2 h⟩⟩
  · intro C _ V d _ I J _ _ X F g a ha u
    have hn : X.n ≤ X.rkF g a := by
      unfold RowData.rkF; rw [X.rk_big g a ha]; omega
    obtain ⟨S, t, ht, gr, hgr, h1, h2⟩ := core X g a ha hn (F.en g a) (F.en_inj g a) (F.en_ty g a) u
    exact ⟨fun h => ⟨S, t, ht, gr, hgr, h1 h⟩, fun h => ⟨S, t, ht, gr, hgr, h2 h⟩⟩

end GlobalTheory.CharBlock
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ExistsEmbeddingCongrIntegralCharacter
section
open scoped BigOperators
open NumberField Formalism.IncomingBounds Formalism.L2.FormalSeriesBounds Formalism.L2.Pj GlobalTheory.RowLaw ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

namespace GlobalTheory.ResidueChar

theorem exists_pow_of_finite_field {K k : Type} [Field K] [Finite K] [CommRing k] [IsDomain k]
    (l : ℕ) [Fact l.Prime] [CharP K l] (f g : K →+* k) :
    ∃ j : ℕ, ∀ y, g y = f y ^ l ^ j := by
  classical
  have := Fintype.ofFinite K
  have hmem : ∀ y, g y ∈ f.range := fun y => by
    have h1 : (Polynomial.X ^ Fintype.card K - Polynomial.X : Polynomial K) =
        ∏ a : K, (Polynomial.X - Polynomial.C a) := by
      have hm : (Polynomial.X ^ Fintype.card K - Polynomial.X : Polynomial K).Monic :=
        Polynomial.monic_X_pow_sub (by
          rw [Polynomial.degree_X]; exact_mod_cast Fintype.one_lt_card)
      have := Polynomial.prod_multiset_X_sub_C_of_monic_of_roots_card_eq hm (by
        rw [FiniteField.roots_X_pow_card_sub_X,
          FiniteField.X_pow_card_sub_X_natDegree_eq K Fintype.one_lt_card]
        rfl)
      rw [← this, FiniteField.roots_X_pow_card_sub_X]
      rfl
    have h2 := congrArg (Polynomial.eval₂RingHom f (g y)) h1
    rw [map_prod] at h2
    simp only [Polynomial.coe_eval₂RingHom, Polynomial.eval₂_sub, Polynomial.eval₂_X_pow,
      Polynomial.eval₂_X, Polynomial.eval₂_C] at h2
    rw [← map_pow, FiniteField.pow_card, sub_self] at h2
    obtain ⟨a, -, ha⟩ := Finset.prod_eq_zero_iff.1 h2.symm
    exact ⟨a, (sub_eq_zero.1 ha).symm⟩
  let e : K ≃+* f.range := RingEquiv.ofBijective f.rangeRestrict
    ⟨f.rangeRestrict.injective, f.rangeRestrict_surjective⟩
  let s : K →+* K := e.symm.toRingHom.comp (g.codRestrict f.range hmem)
  have hs : ∀ y, f (s y) = g y := fun y =>
    congrArg Subtype.val (e.apply_symm_apply (g.codRestrict f.range hmem y))
  let := ZMod.algebra K l
  let s' : K →ₐ[ZMod l] K := { s with
    commutes' := fun r => DFunLike.congr_fun
      (Subsingleton.elim (s.comp (algebraMap (ZMod l) K)) (algebraMap (ZMod l) K)) r }
  obtain ⟨j, hj⟩ := (FiniteField.bijective_frobeniusAlgHom_pow (ZMod l) K).2 s'
  refine ⟨j, fun y => ?_⟩
  have : s y = y ^ l ^ (j : ℕ) := by
    have h := DFunLike.congr_fun hj y
    simp only [AlgHom.coe_pow, FiniteField.coe_frobeniusAlgHom, pow_iterate, ZMod.card] at h
    exact h.symm
  rw [← hs, this, map_pow]

theorem exists_eq_of_ker_le {O k : Type} [CommRing O] [CommRing k] [IsDomain k] {d : ℕ} [NeZero d]
    (l : ℕ) [Fact l.Prime] [CharP k l] (φ : ZMod d → (O →+* k))
    (h : ∀ a x, φ (a + 1) x = φ a x ^ l) (g : O →+* k) (hg : ∀ x, φ 0 x = 0 → g x = 0) :
    ∃ a, ∀ x, g x = φ a x := by
  have hl : 1 < l := (Fact.out : l.Prime).one_lt
  have hq : 1 < l ^ d := Nat.one_lt_pow (NeZero.ne d) hl
  have hper : ∀ x, φ 0 x ^ l ^ d = φ 0 x := fun x => by
    rw [← TeichSeq.frob_iter l φ h]; simp
  have hfin : ((φ 0).range : Set k).Finite := by
    have hne : (Polynomial.X ^ l ^ d - Polynomial.X : Polynomial k) ≠ 0 :=
      (Polynomial.monic_X_pow_sub (by
        rw [Polynomial.degree_X]; exact_mod_cast hq)).ne_zero
    refine (Polynomial.finite_setOfPred_isRoot hne).subset ?_
    rintro _ ⟨x, rfl⟩
    simp [hper]
  have : Finite (φ 0).range := hfin
  let : Field (φ 0).range := (Finite.isField_of_domain _).toField
  let g' : (φ 0).range →+* k :=
    (φ 0).rangeRestrict.liftOfSurjective (φ 0).rangeRestrict_surjective
      ⟨g, fun x hx => hg x (congrArg Subtype.val (RingHom.mem_ker.1 hx))⟩
  have hg' : ∀ x, g' ((φ 0).rangeRestrict x) = g x := fun x =>
    RingHom.liftOfRightInverse_comp_apply _ _ _ _ x
  obtain ⟨j, hj⟩ := exists_pow_of_finite_field l (φ 0).range.subtype g'
  refine ⟨0 + (j : ZMod d), fun x => ?_⟩
  rw [TeichSeq.frob_iter l φ h, ← hg', hj]
  rfl

open TeichSeq in

theorem main : ∀ (C : Type) [Field C] (V : VF C) (O : Type) [CommRing O] (d : ℕ) [NeZero d] (em : ZMod d → (O →+* C)), (∀ a x, V.Ge 0 (em a x)) → (∀ a x, V.MM (em (a + 1) x - em a x ^ V.l)) → ∀ ψ : O →+* C, (∀ x, V.Ge 0 (ψ x)) → (∀ x, (∀ a, V.MM (em a x)) → V.MM (ψ x)) → ∃ a, ∀ x, V.MM (ψ x - em a x) := by
  intro C _ V O _ d _ em hint hfrob ψ hψ hker
  have : Fact V.l.Prime := ⟨V.l_prime⟩
  let π : intRing V →+* intRing V ⧸ maxId V := Ideal.Quotient.mk _
  let e : ZMod d → (O →+* intRing V) := fun a => (em a).codRestrict (intRing V) (hint a)
  let φ : ZMod d → (O →+* intRing V ⧸ maxId V) := fun a => π.comp (e a)
  let p : O →+* intRing V := ψ.codRestrict (intRing V) hψ
  have hπ : ∀ u w : intRing V, π u = π w ↔ V.MM ((u : C) - w) := fun u w => Ideal.Quotient.eq
  have hπ0 : ∀ u : intRing V, π u = 0 ↔ V.MM (u : C) := fun u => Ideal.Quotient.eq_zero_iff_mem
  have hφ : ∀ a x, φ (a + 1) x = φ a x ^ V.l := fun a x => by
    show π (e (a + 1) x) = π (e a x) ^ V.l
    rw [← map_pow, hπ]
    exact hfrob a x
  have : CharP (intRing V ⧸ maxId V) V.l := by
    refine (CharP.charP_iff_prime_eq_zero V.l_prime).2 ?_
    rw [← map_natCast π, hπ0]
    simpa using mm_of_ge_one V VF.ge_l
  obtain ⟨a, ha⟩ := exists_eq_of_ker_le V.l φ hφ (π.comp p) (fun x hx => by
    refine (hπ0 (p x)).2 (hker x fun a => (hπ0 (e a x)).1 ?_)
    have := frob_iter V.l φ hφ 0 x a.val
    rw [hx, zero_pow (pow_ne_zero _ V.l_prime.ne_zero)] at this
    show φ a x = 0
    simpa using this)
  exact ⟨a, fun x => (hπ (p x) (e a x)).1 (ha x)⟩

end GlobalTheory.ResidueChar
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.GaugeDerivEqPairingOfIntegralGaugedLawStatement
section
open scoped BigOperators
open NumberField Formalism.IncomingBounds Formalism.L2.FormalSeriesBounds Formalism.L2.Pj GlobalTheory.RowLaw ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gaugeDeriv_eq_pairing_of_integralGaugedLaw : ∀ (C : Type) [Field C] (V : VF C) (d : ℕ) [NeZero d] (I : Fin 2 → Type) [∀ g, Fintype (I g)] (κ : Type) [Fintype κ] (X : RawChart C d I κ), RLaw X V → ∀ H : ∀ g, X.CartHyp V g, RawChart.CEqSt H := by
  first | exact @GlobalTheory.RowLaw.cEqSt_of_rLaw | exact GlobalTheory.RowLaw.cEqSt_of_rLaw | (intros; apply GlobalTheory.RowLaw.cEqSt_of_rLaw <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.GaugedCurveLogarithmsClosedUnderTadicLimitsStatement
section
open scoped BigOperators
open NumberField Formalism.IncomingBounds Formalism.L2.FormalSeriesBounds Formalism.L2.Pj GlobalTheory.RowLaw ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gaugedCurveLogarithms_closed_under_tadicLimits : ∀ (C : Type) [Field C] (V : VF C) (d : ℕ) [NeZero d] (I : Fin 2 → Type) [∀ g, Fintype (I g)] (κ : Type) [Fintype κ] (X : RawChart C d I κ), RLaw X V → ∀ g (a : ℕ → ((κ → PowerSeries C) × (JJ I g → PowerSeries C))) (b : ((κ → PowerSeries C) × (JJ I g → PowerSeries C))), (∀ n, a n ∈ Cv X V g) → (∀ m, ∃ n0, ∀ n ≥ n0, (∀ i, PowerSeries.coeff m ((a n).1 i) = PowerSeries.coeff m (b.1 i)) ∧ ∀ q, PowerSeries.coeff m ((a n).2 q) = PowerSeries.coeff m (b.2 q)) → b ∈ Cv X V g := by
  first | exact @GlobalTheory.RowLaw.cv_closed_under_limits | exact GlobalTheory.RowLaw.cv_closed_under_limits | (intros; apply GlobalTheory.RowLaw.cv_closed_under_limits <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.IntegralGaugeBilinearTermOfTypeNeStatement
section
open scoped BigOperators
open NumberField Formalism.IncomingBounds Formalism.L2.FormalSeriesBounds Formalism.L2.Pj GlobalTheory.RowLaw ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integral_gaugeBilinearTerm_of_type_ne : ∀ (C : Type) [Field C] (V : VF C) (d : ℕ) [NeZero d] (I : Fin 2 → Type) [∀ g, Fintype (I g)] (κ : Type) [Fintype κ] (X : RawChart C d I κ), RLaw X V → ∀ g, HasTeich X V g → ∀ (c : I g) (q : JJ I g), X.ty g c ≠ X.ty (1 - g) q → V.Ge 0 (X.sg1 (X.u g c) (X.u (1 - g) q)) := by
  first | exact @GlobalTheory.RowLaw.ge_zero_sg1_of_ty_ne | exact GlobalTheory.RowLaw.ge_zero_sg1_of_ty_ne | (intros; apply GlobalTheory.RowLaw.ge_zero_sg1_of_ty_ne <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.IntegralGermsIndependentOfCurveSystem
section
open scoped BigOperators
open NumberField Formalism.IncomingBounds Formalism.L2.FormalSeriesBounds Formalism.L2.Pj GlobalTheory.RowLaw ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

namespace GlobalTheory.RowLaw

theorem intGerm_indep_of_rlaw : ∀ (C : Type) [Field C] (V : VF C) (d : ℕ) [NeZero d] (I : Fin 2 → Type)
    [∀ g, Fintype (I g)] (κ : Type) [Fintype κ] (X : RawChart C d I κ), RLaw X V →
    ∀ H : ∀ g, X.CartHyp V g, RawChart.IntegralGermIndependentOfSystem H := by
  intro C _ V d _ I _ κ _ X hX H S S₂ t t₂ ht ht₂
  rw [GlobalTheory.T.integralGerm_eq_gaugedFormalGroupLaw_expIntegral C V d I κ X hX H S t ht, GlobalTheory.T.integralGerm_eq_gaugedFormalGroupLaw_expIntegral C V d I κ X hX H S₂ t₂ ht₂]

end GlobalTheory.RowLaw
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.IsIntegralGaugedFormalGroupLawSelfConjugateSquarStatement
section
open scoped BigOperators
open NumberField Formalism.IncomingBounds Formalism.L2.FormalSeriesBounds Formalism.L2.Pj GlobalTheory.RowLaw ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isIntegralGaugedFormalGroupLaw_selfConjugateSquare : ∀ (C : Type) [Field C] [CharZero C] (V : VF C) (O : Type) [CommRing O] [StarRing O] (dd : ℕ) (Y : FBChart C V O dd) (d : ℕ) [NeZero d] (I0 : Type) [Fintype I0] (p : SelfData Y d I0), RLaw (Y.rawSelf p) V := by
  first | exact @GlobalTheory.RowLawSquare.rlaw_rawSelf | exact GlobalTheory.RowLawSquare.rlaw_rawSelf | (intros; apply GlobalTheory.RowLawSquare.rlaw_rawSelf <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.RingHomEqOfCongruentIntegralUnramifiedStatement
section
open scoped BigOperators
open NumberField Formalism.IncomingBounds Formalism.L2.FormalSeriesBounds Formalism.L2.Pj GlobalTheory.RowLaw ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ringHom_eq_of_congruent_integral_unramified : ∀ (C : Type) [Field C] (V : VF C) (O : Type) [CommRing O] (d : ℕ), 0 < d → ∀ ε : O, (∃ y, ε * ε - ε = (V.l : O) * y) → (∀ x : O, ∃ y, ε * (x ^ (V.l ^ d) - x) = (V.l : O) * y) → ∀ ψ φ : O →+* C, (∀ x, V.Ge 0 (ψ x)) → (∀ x, V.Ge 0 (φ x)) → V.MM (ψ ε - 1) → (∀ x, V.MM (ψ x - φ x)) → ψ = φ := by
  first | exact @GlobalTheory.CongruentCharacters.eq_of_congruent | exact GlobalTheory.CongruentCharacters.eq_of_congruent | (intros; apply GlobalTheory.CongruentCharacters.eq_of_congruent <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ToricPointExtensionAbelianPartFormalGroupHomStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Be2 GlobalTheory.ChF
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.toricPointExtension_abelianPart_formalGroup_hom : ∀ (R : Type) [CommRing R] (I : Ideal R) [IsAdicComplete I R] (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (B : Over (Spec (CommRingCat.of R))) [GrpObj B] [IsCommMonObj B] (X : Type) [AddCommGroup X] (E : PtExt I G B X) (d g : ℕ) (F : FGLaw R d) (FB : FGLaw R g) (x : Fam G d) (xB : Fam B g), NilChart G F.F x → NilChart B FB.F xB → ∃ Q : Fin g → PS R 1 d, IsHomF F.F FB.F Q ∧ (∀ (S : Type) [CommRing S] [Algebra R S] (h : ∃ k, Kills I k S) (a : Fin d → S), (∀ i, IsNilpotent (a i)) → E.q S h (x S a) = xB S (fun j => nv (algebraMap R S) (Q j) ![a])) := by
  first | exact @GlobalTheory.ChF.ptExt_q_series | exact GlobalTheory.ChF.ptExt_q_series | (intros; apply GlobalTheory.ChF.ptExt_q_series <;> assumption)
end

