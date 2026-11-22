import Mathlib
import Development.AutomorphicSpectrum.Statements.TowerExistence.GoodTowerExistsX
import Development.AutomorphicSpectrum.Statements.MetricStatements.ExistsFlagModelBaseMetric
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0010
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0125
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0108
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0104
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Pull1
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsPeriodOn
import Development.WeilBound.CoreStatements.PluriharmonicCharts.ExistsPenFrame
import Development.WeilBound.CoreStatements.PluriharmonicCharts.MinorElementaryColumnOp
import Development.WeilBound.CoreStatements.PluriharmonicCharts.Bundle0017

-- bundled from Development.WeilBound.CoreStatements.PluriharmonicCharts.LeMCoordIdealOfTorus
section
open AlgebraicGeometry CategoryTheory NumberField Matrix ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.BMx ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P
open ReciprocityTheory.ChartRestriction.G.Semi
open scoped ComplexOrder

namespace PositivityTheory.Xgp.c_bm_exists_boundary

section HomogIdeal

variable {K : Type} [Fintype K] {J : K → Type} [∀ k, Fintype (J k)]

theorem eval_mConeMap {Ω : Type} [Field Ω] (y : (Σ k, J k) → Ω) (c : K → Ω) (f : MRing J) :
    MvPolynomial.eval c (mConeMap y f) = MvPolynomial.aeval (fun p : Σ k, J k => y p * c p.1) f := by
  have h : (MvPolynomial.eval c).comp (mConeMap y).toRingHom =
      (MvPolynomial.aeval (fun p : Σ k, J k => y p * c p.1) : MRing J →ₐ[ℤ] Ω).toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro r; simp
    · intro p; simp [mConeMap]
  exact congrArg (fun φ : MRing J →+* Ω => φ f) h

theorem aeval_eq_eval_map (w : (Σ k, J k) → ℂ) (f : MRing J) :
    MvPolynomial.aeval w f = MvPolynomial.eval w (MvPolynomial.map (Int.castRingHom ℂ) f) := by
  rw [MvPolynomial.eval_map, MvPolynomial.aeval_def, algebraMap_int_eq]

theorem aeval_eq_zero_of_mem {w : (Σ k, J k) → ℂ} {f : MRing J} (hf : f ∈ mCoordIdeal w) :
    MvPolynomial.aeval w f = 0 := by
  have hf' : mConeMap w f = 0 := hf
  have h := eval_mConeMap w (fun _ => 1) f
  rw [hf', map_zero] at h
  simpa using h.symm

theorem aeval_ratio_eq_zero {Ω : Type} [Field Ω] {x : (Σ k, J k) → Ω} (c : (k : K) → J k) {f : MRing J}
    (hf : f ∈ mCoordIdeal x) : MvPolynomial.aeval (fun p : Σ k, J k => x p / x ⟨p.1, c p.1⟩) f = 0 := by
  have hf' : mConeMap x f = 0 := hf
  have h := eval_mConeMap x (fun k => (x ⟨k, c k⟩)⁻¹) f
  rw [hf', map_zero] at h
  simpa [div_eq_mul_inv] using h.symm

theorem eq_zero_of_eval_torus {F : MvPolynomial K ℂ}
    (h : ∀ c : K → ℂ, (∀ k, c k ≠ 0) → MvPolynomial.eval c F = 0) : F = 0 := by
  have h2 : F * ∏ k, (MvPolynomial.X k : MvPolynomial K ℂ) = 0 := by
    apply MvPolynomial.funext
    intro c
    rw [map_mul, map_zero, map_prod]
    by_cases hc : ∀ k, c k ≠ 0
    · rw [h c hc, zero_mul]
    · push_neg at hc
      obtain ⟨k, hk⟩ := hc
      rw [Finset.prod_eq_zero (Finset.mem_univ k) (by simp [hk]), mul_zero]
  rcases mul_eq_zero.1 h2 with h3 | h3
  · exact h3
  · exact absurd h3 (Finset.prod_ne_zero_iff.2 fun k _ => MvPolynomial.X_ne_zero k)

theorem le_mCoordIdeal_of_torus {bd : Ideal (MRing J)} {z : (Σ k, J k) → ℂ}
    (h : ∀ c : K → ℂ, (∀ k, c k ≠ 0) → ∀ f ∈ bd, MvPolynomial.aeval (fun p : Σ k, J k => z p * c p.1) f = 0) :
    bd ≤ mCoordIdeal z := by
  intro f hf
  show mConeMap z f = 0
  refine eq_zero_of_eval_torus fun c hc => ?_
  rw [eval_mConeMap]
  exact h c hc f hf

theorem exists_algHom_ker_eq {S : Type} [CommRing S] [Algebra ℚ S] [Algebra.FiniteType ℚ S] (m : Ideal S)
    [m.IsMaximal] : ∃ ev : S →ₐ[ℚ] ℂ, RingHom.ker ev = m := by
  let _ : Field (S ⧸ m) := Ideal.Quotient.field m
  haveI : Algebra.FiniteType ℚ (S ⧸ m) :=
    Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ ℚ m) (Ideal.Quotient.mkₐ_surjective ℚ m)
  haveI : Module.Finite ℚ (S ⧸ m) := finite_of_finite_type_of_isJacobsonRing ℚ (S ⧸ m)
  haveI : Algebra.IsAlgebraic ℚ (S ⧸ m) := Algebra.IsAlgebraic.of_finite ℚ _
  let φ : (S ⧸ m) →ₐ[ℚ] ℂ := IsAlgClosed.lift
  refine ⟨φ.comp (Ideal.Quotient.mkₐ ℚ m), ?_⟩
  ext s
  rw [RingHom.mem_ker, AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk, map_eq_zero_iff φ φ.toRingHom.injective,
    Ideal.Quotient.eq_zero_iff_mem]

theorem cond_of_bd {Ω : Type} [Field Ω] [CharZero Ω] {x : (Σ k, J k) → Ω} {bd : Ideal (MRing J)}
    {c : (k : K) → J k} (hc : ∀ k, x ⟨k, c k⟩ ≠ 0) {S : Subalgebra ℚ Ω} [Algebra.FiniteType ℚ S]
    (hρ : ∀ p : Σ k, J k, x p / x ⟨p.1, c p.1⟩ ∈ S) (q : Ideal S) (hq : q.IsPrime)
    (hbd : ∀ g ∈ bd, ∀ s : S, (s : Ω) = MvPolynomial.aeval (fun p : Σ k, J k => x p / x ⟨p.1, c p.1⟩) g → s ∈ q) :
    ∀ g ∈ (⨅ z ∈ mcPts (mCoordIdeal x) ∩ mcPts bd, mCoordIdeal z), ∀ s : S,
      (s : Ω) = MvPolynomial.aeval (fun p : Σ k, J k => x p / x ⟨p.1, c p.1⟩) g → s ∈ q := by
  intro g hg s hs
  haveI : IsJacobsonRing S := isJacobsonRing_of_finiteType (A := ℚ)
  have hjac : q.jacobson = q := isJacobsonRing_iff_prime_eq.mp inferInstance q hq
  rw [← hjac]
  refine Ideal.mem_sInf.2 ?_
  rintro m ⟨hqm, hm⟩
  obtain ⟨ev, hev⟩ := exists_algHom_ker_eq m
  let ρS : (Σ k, J k) → S := fun p => ⟨_, hρ p⟩
  let w : (Σ k, J k) → ℂ := fun p => ev (ρS p)
  have hval : ∀ f : MRing J, ev (MvPolynomial.aeval ρS f) = MvPolynomial.aeval w f := fun f => by
    rw [MvPolynomial.aeval_def, MvPolynomial.aeval_def, ← AlgHom.coe_toRingHom, MvPolynomial.eval₂_comp_left]
    congr 1 <;> first | rfl | exact RingHom.ext_int _ _
  have hsub : ∀ f : MRing J, ((MvPolynomial.aeval ρS f : S) : Ω) =
      MvPolynomial.aeval (fun p : Σ k, J k => x p / x ⟨p.1, c p.1⟩) f := fun f => by
    show S.val.toRingHom (MvPolynomial.aeval ρS f) = _
    rw [MvPolynomial.aeval_def, MvPolynomial.aeval_def, MvPolynomial.eval₂_comp_left]
    congr 1 <;> first | rfl | exact RingHom.ext_int _ _
  have hwP : w ∈ mcPts (mCoordIdeal x) := by
    refine ⟨fun k => ⟨c k, ?_⟩, fun f hf => ?_⟩
    · have h1 : ρS ⟨k, c k⟩ = 1 := Subtype.ext (div_self (hc k))
      simp only [w, h1, map_one]
      exact one_ne_zero
    · rw [← aeval_eq_eval_map, ← hval]
      have h1 : MvPolynomial.aeval ρS f = 0 := Subtype.ext (by rw [hsub]; exact aeval_ratio_eq_zero c hf)
      rw [h1, map_zero]
  have hwbd : w ∈ mcPts bd := by
    refine ⟨hwP.1, fun f hf => ?_⟩
    rw [← aeval_eq_eval_map, ← hval, ← RingHom.mem_ker, hev]
    exact hqm (hbd f hf _ (hsub f))
  have hg' : g ∈ mCoordIdeal w := (Submodule.mem_iInf _).1 ((Submodule.mem_iInf _).1 hg w) ⟨hwP, hwbd⟩
  have hs' : s = MvPolynomial.aeval ρS g := Subtype.ext (hs.trans (hsub g).symm)
  rw [← hev, RingHom.mem_ker, hs', hval]
  exact aeval_eq_zero_of_mem hg'

end HomogIdeal

theorem exists_homogIdeal {K : Type} [Fintype K] {J : K → Type} [∀ k, Fintype (J k)] {Ω : Type} [Field Ω]
    [CharZero Ω] (x : (Σ k, J k) → Ω) (n : ℕ) (bd : Ideal (MRing J)) (hs : Cmp.IsSncModel x n bd)
    (ha : IsArithVar (mCoordIdeal x) (n + 1))
    (ht : ∀ z ∈ mcPts (mCoordIdeal x) ∩ mcPts bd, ∀ c : K → ℂ, (∀ k, c k ≠ 0) →
      GroundTheory.Heights₂.Heights.LowerBoundFree.torusSmul c z ∈ mcPts (mCoordIdeal x) ∩ mcPts bd) :
    ∃ I : Ideal (MRing J), IsMultiHomogIdeal I ∧ ¬ I ≤ mCoordIdeal x ∧ Cmp.IsSncModel x n I ∧
      mcPts (mCoordIdeal x) ∩ mcPts I = mcPts (mCoordIdeal x) ∩ mcPts bd := by
  classical
  set I : Ideal (MRing J) := ⨅ z ∈ mcPts (mCoordIdeal x) ∩ mcPts bd, mCoordIdeal z with hIdef
  have hle : bd ≤ I := by
    intro f hf
    refine (Submodule.mem_iInf _).2 fun z => (Submodule.mem_iInf _).2 fun hz => ?_
    refine le_mCoordIdeal_of_torus (fun c hc g hg => ?_) hf
    have e : (fun p : Σ k, J k => z p * c p.1) = GroundTheory.Heights₂.Heights.LowerBoundFree.torusSmul c z :=
      funext fun p => mul_comm _ _
    rw [e, aeval_eq_eval_map]
    exact (ht z hz c hc).2.2 g hg
  have hhom : IsMultiHomogIdeal I := by
    refine (GroundTheory.Heights₂.Heights.Bridge.isMultiHomogIdeal_iff I).mp ?_
    intro f hf b
    refine (Submodule.mem_iInf _).2 fun z => (Submodule.mem_iInf _).2 fun hz => ?_
    exact GroundTheory.Heights₂.Heights.CoordinateConeArithVar.component_mem z f
      ((Submodule.mem_iInf _).1 ((Submodule.mem_iInf _).1 hf z) hz) b

  have hrel := ha.2.1.2.2
  have hc0 : ∀ k, ∃ i, x ⟨k, i⟩ ≠ 0 := fun k => by
    obtain ⟨i, hi⟩ := hrel k
    refine ⟨i, fun h0 => hi ?_⟩
    show mConeMap x (MvPolynomial.X ⟨k, i⟩) = 0
    simp [mConeMap, h0]
  choose c hc using hc0
  refine ⟨I, hhom, ?_, ?_, ?_⟩
  · intro hIP
    obtain ⟨m, f, a, -, -, hsum, hl⟩ := hs c hc
    obtain ⟨l, hfl⟩ : ∃ l, f l ≠ 0 := by
      by_contra h
      push_neg at h
      rw [Finset.sum_eq_zero fun l _ => by rw [h l, mul_zero]] at hsum
      exact zero_ne_one hsum
    obtain ⟨-, z, n', -, hli, -, hq⟩ := hl l hfl _ rfl
    have hbot := hq ⊥ Ideal.isPrime_bot
    have hR : ¬ ∃ i : Fin n, (i : ℕ) < n' ∧ z i ∈ (⊥ : Ideal _) := by
      rintro ⟨i, -, hzi⟩
      rw [Ideal.mem_bot] at hzi
      exact hli.ne_zero i (by rw [hzi, map_zero])
    rw [← hbot] at hR
    push_neg at hR
    obtain ⟨g, hg, s, hs1, hs2⟩ := hR
    have hs3 : (s : Ω) ≠ 0 := fun h0 => hs2 ((Ideal.mem_bot).2 (Subtype.ext h0))
    rw [hs1] at hs3
    exact hs3 (aeval_ratio_eq_zero c (hIP (hle hg)))
  · intro c' hc'
    obtain ⟨m, f, a, hf, ha', hsum, hl⟩ := hs c' hc'
    refine ⟨m, f, a, hf, ha', hsum, fun l hfl S hS => ?_⟩
    obtain ⟨hsm, z, n', hn', hli, hsp, hq⟩ := hl l hfl S hS
    refine ⟨hsm, z, n', hn', hli, hsp, fun q hqp => ?_⟩
    rw [← hq q hqp]
    constructor
    · intro h g hg s hs'
      exact h g (hle hg) s hs'
    · intro h
      have hfin : (insert (f l)⁻¹ (Set.range fun p : Σ k, J k => x p / x ⟨p.1, c' p.1⟩)).Finite :=
        (Set.finite_range _).insert _
      haveI : Algebra.FiniteType ℚ S := by
        rw [← Subalgebra.fg_iff_finiteType, hS, ← hfin.coe_toFinset]
        exact Subalgebra.fg_adjoin_finset _
      have hρ : ∀ p : Σ k, J k, x p / x ⟨p.1, c' p.1⟩ ∈ S := fun p => by
        rw [hS]
        exact Algebra.subset_adjoin (Set.mem_insert_of_mem _ (Set.mem_range_self p))
      exact cond_of_bd hc' hρ q hqp h
  · ext z
    constructor
    · rintro ⟨hzP, hzI⟩
      exact ⟨hzP, hzI.1, fun f hf => hzI.2 f (hle hf)⟩
    · rintro ⟨hzP, hzb⟩
      refine ⟨hzP, hzP.1, fun f hf => ?_⟩
      rw [← aeval_eq_eval_map]
      exact aeval_eq_zero_of_mem ((Submodule.mem_iInf _).1 ((Submodule.mem_iInf _).1 hf z) ⟨hzP, hzb⟩)

end PositivityTheory.Xgp.c_bm_exists_boundary
end

-- bundled from Development.WeilBound.CoreStatements.PluriharmonicCharts.PeriodGramConj
section
open AlgebraicGeometry CategoryTheory NumberField Matrix ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.BMx ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P
open ReciprocityTheory.ChartRestriction.G.Semi
open scoped ComplexOrder

namespace PositivityTheory.Xgp.c_bm_exists_period

theorem det_head {p q k : ℕ} {I : Type} [Fintype I] [DecidableEq I] (M : Matrix (Fin (p + q)) (Fin (p + q)) ℂ)
    (f : I → Fin q ⊕ Fin p) (hf : Function.Injective f)
    (hr : ∀ x, ((blockEquiv p q x : Fin (p + q)) : ℕ) < k ↔ ∃ i, f i = x) :
    (M.submatrix (Subtype.val : {a : Fin (p + q) // (a : ℕ) < k} → _) Subtype.val).det =
      ((M.submatrix (blockEquiv p q) (blockEquiv p q)).submatrix f f).det := by
  let e : I ≃ {a : Fin (p + q) // (a : ℕ) < k} := Equiv.ofBijective
    (fun i => ⟨blockEquiv p q (f i), (hr _).2 ⟨i, rfl⟩⟩)
    ⟨fun i j h => hf ((blockEquiv p q).injective (congrArg Subtype.val h)), fun ⟨a, ha⟩ => by
      obtain ⟨x, rfl⟩ := (blockEquiv p q).surjective a
      obtain ⟨i, rfl⟩ := (hr x).1 ha
      exact ⟨i, rfl⟩⟩
  rw [← Matrix.det_submatrix_equiv_self e]
  rfl

theorem sub_conj {m I : Type} [Fintype m] (H Y : Matrix m m ℂ) (f : I → m) :
    (Hᴴ * Y * H).submatrix f f = (H.submatrix id f)ᴴ * Y * H.submatrix id f := by
  ext a b
  simp [Matrix.mul_apply]

theorem periodGram_of {p q : ℕ} (Pi : Matrix (Fin (p + q)) (Fin (p + q)) ℂ) (Go : Matrix (Fin q) (Fin q) ℂ)
    (Gw : Matrix (Fin p) (Fin p) ℂ) (Z : Matrix (Fin q) (Fin p) ℂ) (hGo : Go.PosDef) (hdet : IsUnit Pi.det)
    (h : (gramOf (sigForm (p + q) p) Pi).submatrix (blockEquiv p q) (blockEquiv p q) =
      (fromBlocks 1 Z 0 1)ᴴ * fromBlocks (-Go) 0 0 Gw * fromBlocks 1 Z 0 1) :
    IsPeriodGram p Pi ((fromBlocks Go 0 0 Gw).submatrix (blockEquiv p q).symm (blockEquiv p q).symm) := by
  classical
  refine ⟨⟨hdet, ?_⟩, fun h' hb k => ?_⟩
  · let f : {a : Fin (p + q) // (a : ℕ) < p + q - p} → Fin q := fun a => ⟨a.1, by have := a.2; omega⟩
    have hf : Function.Injective f := fun a b e => Subtype.ext (Fin.ext (congrArg Fin.val e :))
    convert hGo.submatrix hf using 1
    ext a b
    have := congrFun (congrFun h (.inl (f a))) (.inl (f b))
    simp only [fromBlocks_conjTranspose, fromBlocks_multiply] at this
    simp at this
    simp only [gramHead, Matrix.neg_apply, Matrix.submatrix_apply]
    rw [neg_eq_iff_eq_neg]
    exact this
  have e1 : (gramOf (sigForm (p + q) p) (Pi * h')).submatrix (blockEquiv p q) (blockEquiv p q) =
      (fromBlocks (omBlock h') 0 0 (wBlock h'))ᴴ *
        ((fromBlocks 1 Z 0 1)ᴴ * fromBlocks (-Go) 0 0 Gw * fromBlocks 1 Z 0 1) *
        fromBlocks (omBlock h') 0 0 (wBlock h') := by
    rw [← h, ← hb.eq_fromBlocks, Matrix.conjTranspose_submatrix, Matrix.submatrix_mul_equiv,
      Matrix.submatrix_mul_equiv]
    simp only [gramOf, Matrix.conjTranspose_mul, Matrix.mul_assoc]
  have e2 : (h'ᴴ * (fromBlocks Go 0 0 Gw).submatrix (blockEquiv p q).symm (blockEquiv p q).symm * h').submatrix
      (blockEquiv p q) (blockEquiv p q) =
      (fromBlocks (omBlock h') 0 0 (wBlock h'))ᴴ * fromBlocks Go 0 0 Gw * fromBlocks (omBlock h') 0 0 (wBlock h') := by
    rw [← hb.eq_fromBlocks, Matrix.conjTranspose_submatrix, ← Matrix.submatrix_mul_equiv _ _ _ (blockEquiv p q),
      ← Matrix.submatrix_mul_equiv _ _ _ (blockEquiv p q)]
    simp
  unfold gramHead
  by_cases hk : q ≤ k
  · let f : Fin q ⊕ {b : Fin p // q + (b : ℕ) < k} → Fin q ⊕ Fin p := Sum.map id Subtype.val
    have hf : Function.Injective f := Sum.map_injective.2 ⟨Function.injective_id, Subtype.val_injective⟩
    have hr : ∀ x, ((blockEquiv p q x : Fin (p + q)) : ℕ) < k ↔ ∃ i, f i = x := by
      rintro (a | b)
      · exact ⟨fun _ => ⟨.inl a, rfl⟩, fun _ => by show (a : ℕ) < k; omega⟩
      · refine ⟨fun h => ⟨.inr ⟨b, h⟩, rfl⟩, ?_⟩
        rintro ⟨a | a, ha⟩
        · simp [f] at ha
        · obtain rfl : a.1 = b := by simpa [f] using ha
          exact a.2
    rw [det_head _ f hf hr, det_head _ f hf hr, e1, e2, sub_conj, sub_conj]
    set h₂ : Matrix (Fin p) {b : Fin p // q + (b : ℕ) < k} ℂ := (wBlock h').submatrix id Subtype.val
    have e3 : (fromBlocks (omBlock h') 0 0 (wBlock h')).submatrix id f = fromBlocks (omBlock h') 0 0 h₂ := by
      ext (a | a) (b | b) <;> rfl
    rw [e3]
    have e4 : (fromBlocks (omBlock h') 0 0 h₂)ᴴ *
        ((fromBlocks 1 Z 0 1)ᴴ * fromBlocks (-Go) 0 0 Gw * fromBlocks 1 Z 0 1) * fromBlocks (omBlock h') 0 0 h₂ =
        (fromBlocks (omBlock h') (Z * h₂) 0 1)ᴴ * fromBlocks (-Go) 0 0 (h₂ᴴ * Gw * h₂) *
          fromBlocks (omBlock h') (Z * h₂) 0 1 := by
      simp only [fromBlocks_conjTranspose, fromBlocks_multiply]
      simp [Matrix.mul_assoc, Matrix.mul_add, Matrix.add_mul]
    have e5 : (fromBlocks (omBlock h') 0 0 h₂)ᴴ * fromBlocks Go 0 0 Gw * fromBlocks (omBlock h') 0 0 h₂ =
        (fromBlocks (omBlock h') 0 0 1)ᴴ * fromBlocks Go 0 0 (h₂ᴴ * Gw * h₂) * fromBlocks (omBlock h') 0 0 1 := by
      simp only [fromBlocks_conjTranspose, fromBlocks_multiply]
      simp [Matrix.mul_assoc]
    rw [e4, e5]
    simp only [Matrix.det_mul, Matrix.det_conjTranspose, Matrix.det_fromBlocks_zero₂₁, Matrix.det_neg, norm_mul,
      norm_pow, norm_neg, norm_one, one_pow, one_mul]
  · let f : {a : Fin q // (a : ℕ) < k} → Fin q ⊕ Fin p := fun a => .inl a.1
    have hf : Function.Injective f := fun a b e => Subtype.ext (Sum.inl_injective e)
    have hr : ∀ x, ((blockEquiv p q x : Fin (p + q)) : ℕ) < k ↔ ∃ i, f i = x := by
      rintro (a | b)
      · refine ⟨fun h => ⟨⟨a, h⟩, rfl⟩, ?_⟩
        rintro ⟨b, hb⟩
        obtain rfl : b.1 = a := Sum.inl_injective hb
        exact b.2
      · refine ⟨fun h => absurd h (by show ¬ q + (b : ℕ) < k; omega), ?_⟩
        rintro ⟨a, ha⟩
        simp [f] at ha
    rw [det_head _ f hf hr, det_head _ f hf hr, e1, e2, sub_conj, sub_conj]
    set h₁ : Matrix (Fin q) {a : Fin q // (a : ℕ) < k} ℂ := (omBlock h').submatrix id Subtype.val
    set O : Matrix (Fin p) {a : Fin q // (a : ℕ) < k} ℂ := 0 with hO
    have e3 : (fromBlocks (omBlock h') 0 0 (wBlock h')).submatrix id f = fromRows h₁ O := by
      ext (a | a) b <;> rfl
    rw [e3]
    have e4 : (fromRows h₁ O)ᴴ * ((fromBlocks 1 Z 0 1)ᴴ * fromBlocks (-Go) 0 0 Gw * fromBlocks 1 Z 0 1) *
        fromRows h₁ O = -((fromRows h₁ O)ᴴ * fromBlocks Go 0 0 Gw * fromRows h₁ O) := by
      simp only [fromBlocks_conjTranspose, fromBlocks_multiply, conjTranspose_fromRows_eq_fromCols_conjTranspose,
        fromCols_mul_fromBlocks, fromCols_mul_fromRows]
      simp [hO]
    rw [e4, Matrix.det_neg]
    simp

theorem periodGram_conj {N j : ℕ} {Pi G : Matrix (Fin N) (Fin N) ℂ} (h : IsPeriodGram j Pi G) :
    IsPeriodGram j (Pi.map (starRingEnd ℂ)) (G.map (starRingEnd ℂ)) := by
  classical
  have g : ∀ (k : ℕ) (X : Matrix (Fin N) (Fin N) ℂ), gramHead (sigForm N j) k (X.map (starRingEnd ℂ)) =
      (gramHead (sigForm N j) k X).map (starRingEnd ℂ) := fun k X => by
    ext a b
    simp [gramHead, gramOf, Matrix.mul_apply, Matrix.diagonal_apply, apply_ite]
  have dm : ∀ {I : Type} [Fintype I] [DecidableEq I] (X : Matrix I I ℂ),
      (X.map (starRingEnd ℂ)).det = starRingEnd ℂ X.det := fun X => (RingHom.map_det _ X).symm
  refine ⟨⟨?_, ?_⟩, fun h' hb k => ?_⟩
  · rw [dm]; exact h.1.1.map _
  · rw [g]
    suffices e : -(gramHead (sigForm N j) (N - j) Pi).map (starRingEnd ℂ) = (-gramHead (sigForm N j) (N - j) Pi)ᵀ by
      rw [e]; exact h.1.2.transpose
    ext a b
    have := h.1.2.isHermitian.apply a b
    simp only [Matrix.neg_apply, star_neg, neg_inj] at this
    simp only [Matrix.neg_apply, Matrix.map_apply, Matrix.transpose_apply, neg_inj]
    rw [← this]; simp
  · have := h.2 (h'.map (starRingEnd ℂ)) (fun a b hab => by simp [hb a b hab]) k
    have e1 : Pi.map (starRingEnd ℂ) * h' = (Pi * h'.map (starRingEnd ℂ)).map (starRingEnd ℂ) := by
      ext a b; simp [Matrix.mul_apply]
    have e2 : (h'ᴴ * G.map (starRingEnd ℂ) * h').submatrix (Subtype.val : {a : Fin N // (a : ℕ) < k} → Fin N)
        (Subtype.val : {a : Fin N // (a : ℕ) < k} → Fin N) = (((h'.map (starRingEnd ℂ))ᴴ * G * h'.map (starRingEnd ℂ)).submatrix
          (Subtype.val : {a : Fin N // (a : ℕ) < k} → Fin N)
          (Subtype.val : {a : Fin N // (a : ℕ) < k} → Fin N)).map (starRingEnd ℂ) := by
      ext a b; simp [Matrix.mul_apply]
    rw [e1, g, e2, dm, dm, Complex.norm_conj, Complex.norm_conj, this]

theorem blockG_conj {p q : ℕ} (Γ : Matrix (Fin (p + q)) (Fin (p + q)) ℂ) :
    blockG (Γ.map (starRingEnd ℂ)) = (blockG Γ).map (starRingEnd ℂ) := by
  have e : (omBlock (Γ.map (starRingEnd ℂ)))ᵀ⁻¹ = ((omBlock Γ)ᵀ⁻¹).map (starRingEnd ℂ) := by
    have e1 : (omBlock (Γ.map (starRingEnd ℂ)))ᵀ = (omBlock Γ)ᴴ := rfl
    rw [e1, ← Matrix.conjTranspose_nonsing_inv, ← Matrix.transpose_nonsing_inv]
    rfl
  ext a b
  simp only [blockG, e, Matrix.submatrix_apply, Matrix.map_apply]
  rcases (blockEquiv p q).symm a with a | a <;> rcases (blockEquiv p q).symm b with b | b <;>
    simp [wBlock]

end PositivityTheory.Xgp.c_bm_exists_period
end

-- bundled from Development.WeilBound.CoreStatements.PluriharmonicCharts.XCBmExistsBlockpos
section
open AlgebraicGeometry CategoryTheory NumberField Matrix ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.BMx ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P
open ReciprocityTheory.ChartRestriction.G.Semi
open scoped ComplexOrder

namespace PositivityTheory.Xgp.c_bm_exists_blockpos

theorem posDef_fromBlocks {m n : Type} [Fintype m] [Fintype n] {A : Matrix m m ℂ} {B : Matrix n n ℂ}
    (hA : A.PosDef) (hB : B.PosDef) : (Matrix.fromBlocks A 0 0 B).PosDef := by
  rw [Matrix.posDef_iff_dotProduct_mulVec] at hA hB ⊢
  refine ⟨?_, fun x hx => ?_⟩
  · rw [Matrix.IsHermitian, Matrix.fromBlocks_conjTranspose, hA.1, hB.1]; simp
  · have e : star x ⬝ᵥ (Matrix.fromBlocks A 0 0 B *ᵥ x) =
        star (x ∘ Sum.inl) ⬝ᵥ (A *ᵥ (x ∘ Sum.inl)) + star (x ∘ Sum.inr) ⬝ᵥ (B *ᵥ (x ∘ Sum.inr)) := by
      rw [Matrix.fromBlocks_mulVec]
      simp [dotProduct, Fintype.sum_sum_type]
    rw [e]
    have h1 : 0 ≤ star (x ∘ Sum.inl) ⬝ᵥ (A *ᵥ (x ∘ Sum.inl)) := by
      by_cases h : x ∘ Sum.inl = 0
      · rw [h]; simp
      · exact (hA.2 h).le
    have h2 : 0 ≤ star (x ∘ Sum.inr) ⬝ᵥ (B *ᵥ (x ∘ Sum.inr)) := by
      by_cases h : x ∘ Sum.inr = 0
      · rw [h]; simp
      · exact (hB.2 h).le
    by_cases h : x ∘ Sum.inl = 0
    · have h' : x ∘ Sum.inr ≠ 0 := fun h' => hx (funext fun i => by
        rcases i with i | i
        · exact congrFun h i
        · exact congrFun h' i)
      exact add_pos_of_nonneg_of_pos h1 (hB.2 h')
    · exact add_pos_of_pos_of_nonneg (hA.2 h) h2

end PositivityTheory.Xgp.c_bm_exists_blockpos

theorem PositivityTheory.Xgp.t_c_bm_exists_blockpos : ∀ (p q : ℕ) (Γ : Matrix (Fin (p + q)) (Fin (p + q)) ℂ), Γ.PosDef → IsBlockDiag p (blockG Γ) ∧ (blockG Γ).PosDef := by
  intro p q Γ h
  refine ⟨fun a b hab => ?_, ?_⟩
  · obtain ⟨a, rfl⟩ := (blockEquiv p q).surjective a
    obtain ⟨b, rfl⟩ := (blockEquiv p q).surjective b
    simp only [blockG, Matrix.submatrix_apply, Equiv.symm_apply_apply]
    rcases a with a | a <;> rcases b with b | b
    · exact absurd (show (a : ℕ) < _ ↔ (b : ℕ) < _ by omega) hab
    · rfl
    · rfl
    · exact absurd (show q + (a : ℕ) < _ ↔ q + (b : ℕ) < _ by omega) hab
  · refine Matrix.PosDef.submatrix ?_ (blockEquiv p q).symm.injective
    exact PositivityTheory.Xgp.c_bm_exists_blockpos.posDef_fromBlocks
      (h.submatrix (omEmb_strictMono p q).injective).transpose.inv
      (h.submatrix (wEmb_strictMono p q).injective)
end

-- bundled from Development.WeilBound.CoreStatements.PluriharmonicCharts.XCBmExistsSumframe
section
open AlgebraicGeometry CategoryTheory NumberField Matrix ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.BMx ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P
open ReciprocityTheory.ChartRestriction.G.Semi
open scoped ComplexOrder

theorem PositivityTheory.Xgp.isFrameAt_comap_gbS : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (Xo : ∀ l : Level H, Moduli D l) (l : Level H) (c : Coeff l) (Y : Model (Xo l) c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (M : FlagModel y (CMType H) (D.p + D.q) D.p) (𝔐 : HodgeCpt Y S M.x) (tie : FlagTie M 𝔐), ∀ (F : FrameData ι (CMType H) (D.p + D.q) M.Ω M.blk), M.IsFrame F → ∀ (τ : CMType H) (q : Cpt 𝔐.ξ), M.GoodAt F (ptIdeal 𝔐.ξ M.x q) → (Lat.comap (fun p => 𝔐.V (.inl τ) p ⊔ 𝔐.V (.inr τ) p) (𝔐.Vgen (.inl τ) ⊔ 𝔐.Vgen (.inr τ)).subtype).IsFrameAt (gbS tie F τ) q := by
  intro E _ _ _ H D Xo l c Y S K _ ι _ Φ _ y M 𝔐 tie F hF τ q hq
  have hβ : Function.Injective (algebraMap (𝓞 c.F) c.F) := RingOfIntegers.coe_injective
  obtain ⟨-, -, -, -, -, -, hind, -⟩ :=
    GlobalTheory.T.hodge_cpt_interior_generic E H D l (Xo l) c (𝓞 c.F) (algebraMap (𝓞 c.F) c.F) Y S M.Ω _ _ M.x 𝔐 hβ
  have hdisj : Disjoint (𝔐.Vgen (.inr τ)) (𝔐.Vgen (.inl τ)) := hind.pairwiseDisjoint Sum.inr_ne_inl
  have hW : (𝔐.V (.inl τ)).IsFrameAt (tie.wFrame F τ) q := tie.frameW q F hF hq τ
  obtain ⟨hex, hall⟩ := omBundle_dualFrame 𝔐 τ q (tie.frameO q F hF hq τ)
  have hd : ∀ a b, tie.omFrame F τ a (dualFam tie F τ b) = if a = b then 1 else 0 := by
    have hex' : ∃ v : Fin D.q → 𝔐.Vgen (.inr τ), ∀ a b, tie.omFrame F τ a (v b) = if a = b then 1 else 0 := hex
    unfold dualFam
    rw [dif_pos hex']
    exact hex'.choose_spec
  have hO := hall _ hd
  have e : (fun i => (gbS tie F τ i : 𝔐.Li)) =
      Sum.elim (fun b => (dualFam tie F τ b : 𝔐.Li)) (tie.wFrame F τ) ∘ (blockEquiv D.p D.q).symm := by
    funext i
    simp only [gbS, Function.comp]
    rcases (blockEquiv D.p D.q).symm i with a | a <;> rfl
  constructor
  · refine LinearIndependent.of_comp (𝔐.Vgen (.inl τ) ⊔ 𝔐.Vgen (.inr τ)).subtype ?_
    show LinearIndependent M.Ω (fun i => (gbS tie F τ i : 𝔐.Li))
    rw [e]
    refine (hO.1.sum_type hW.1 (hdisj.mono ?_ ?_)).comp _ (blockEquiv D.p D.q).symm.injective
    · exact Submodule.span_le.2 (by rintro _ ⟨b, rfl⟩; exact (dualFam tie F τ b).2)
    · exact Submodule.span_le.2 (by rintro _ ⟨b, rfl⟩; exact wFrame_mem tie F τ b)
  · have h1 : 𝔐.V (.inl τ) q = Submodule.span (regAt 𝔐.ξ q) (Set.range (tie.wFrame F τ)) := hW.2
    have h2 : 𝔐.V (.inr τ) q = Submodule.span (regAt 𝔐.ξ q) (Set.range fun b => (dualFam tie F τ b : 𝔐.Li)) := hO.2
    show (𝔐.V (.inl τ) q ⊔ 𝔐.V (.inr τ) q).comap
      ((𝔐.Vgen (.inl τ) ⊔ 𝔐.Vgen (.inr τ)).subtype.restrictScalars (regAt 𝔐.ξ q)) = _
    have hinj : Function.Injective
        ((𝔐.Vgen (.inl τ) ⊔ 𝔐.Vgen (.inr τ)).subtype.restrictScalars (regAt 𝔐.ξ q)) :=
      (𝔐.Vgen (.inl τ) ⊔ 𝔐.Vgen (.inr τ)).injective_subtype
    have e' : 𝔐.V (.inl τ) q ⊔ 𝔐.V (.inr τ) q = (Submodule.span (regAt 𝔐.ξ q) (Set.range (gbS tie F τ))).map
        ((𝔐.Vgen (.inl τ) ⊔ 𝔐.Vgen (.inr τ)).subtype.restrictScalars (regAt 𝔐.ξ q)) := by
      rw [Submodule.map_span, ← Set.range_comp, h1, h2, ← Submodule.span_union, Set.union_comm, ← Set.Sum.elim_range]
      congr 1
      refine Eq.trans ?_ (congrArg Set.range e.symm)
      exact ((blockEquiv D.p D.q).symm.surjective.range_comp _).symm
    rw [e', Submodule.comap_map_eq_of_injective hinj]
end

-- bundled from Development.WeilBound.CoreStatements.PluriharmonicCharts.XCWLine
section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical

theorem PositivityTheory.Xgp.t_c_w_line : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (τ : Ψ) (a b : Fin N) (k₀ : K) (ca cb : Fin N), (b : ℕ) = a + 1 → ((b : ℕ) < j ∨ j ≤ (a : ℕ)) → M.blk (τ, a) = some k₀ → (ca : ℕ) = lastCol N j a → (cb : ℕ) = ca + 1 → ∀ G : GenFibre (fun p : (Σ k, ι k) => (⟨some p.1, p.2⟩ : Σ o : Option K, ι (o.getD k₀))) (mCoordIdeal (M.wCo (τ, a) k₀ ca cb RatFunc.X)), ∃ T : Set (MRingOver G.Φ (fibreIdx (fun o : Option K => ι (o.getD k₀)) (some : K → Option K))), (∀ f ∈ T, IsMultiHomog f fun _ => 1) ∧ fibreIdeal (some : K → Option K) G = Ideal.span T := by
  intro K _ ι _ Φ _ y Ψ _ _ N j M τ a b k₀ ca cb hb hab hk hca hcb
  choose c hc using PositivityTheory.Xgp.W.blocks_of_model M
  obtain ⟨Fr⟩ := PositivityTheory.Xgp.W.exists_penFrame M hb hab hk hca hcb (PositivityTheory.Xgp.W.isPt_self fun k => ⟨c k, hc k⟩) c hc
  rw [PositivityTheory.Xgp.W.wCo_eq M hb hab hk hca hcb]
  exact fun G => PositivityTheory.Xgp.W.line_pen Fr G
end

