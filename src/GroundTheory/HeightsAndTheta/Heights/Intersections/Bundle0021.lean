import Mathlib
import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0017
import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0020
import GroundTheory.HeightsAndTheta.Heights.Intersections.ProjLineRankTwoPushforwardHypotheses
import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0019
import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0006
import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0009
import GroundTheory.HeightsAndTheta.Heights.Intersections.PrimeComplMapLeNonZeroDivisorsQuot
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.Bundle0001
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0018

-- bundled from GroundTheory.HeightsAndTheta.Heights.Intersections.EqZeroOfEventuallyEval
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial Filter Topology ReciprocityTheory.ChartRestriction.G.Geo

theorem pointFormRank_holds.exists_surj_coords {σ : Type*} {n : ℕ} (ℓ : σ → (Fin n → ℂ) →ₗ[ℂ] ℂ)
    (hℓ : ∀ x, (∀ s, ℓ s x = 0) → x = 0) :
    ∀ m, m ≤ n → ∃ q : Fin m → σ, Function.Surjective (fun x : Fin n → ℂ => fun j => ℓ (q j) x) := by
  intro m
  induction m with
  | zero => intro _; exact ⟨Fin.elim0, fun t => ⟨0, funext fun j => j.elim0⟩⟩
  | succ m ih =>
    intro hm
    obtain ⟨q, hq⟩ := ih (by omega)
    let Φ : (Fin n → ℂ) →ₗ[ℂ] (Fin m → ℂ) := LinearMap.pi fun j => ℓ (q j)
    have hrank := LinearMap.finrank_range_add_finrank_ker Φ
    have hle : Module.finrank ℂ (LinearMap.range Φ) ≤ m := by
      simpa using Submodule.finrank_le (LinearMap.range Φ)
    have hpos : 0 < Module.finrank ℂ (LinearMap.ker Φ) := by
      rw [Module.finrank_fin_fun] at hrank; omega
    obtain ⟨⟨x, hxk⟩, hx0⟩ := Module.finrank_pos_iff_exists_ne_zero.mp hpos
    have hx : x ≠ 0 := fun h => hx0 (Subtype.ext h)
    have hΦx : ∀ j, ℓ (q j) x = 0 := fun j => congr_fun (LinearMap.mem_ker.mp hxk) j
    obtain ⟨s, hs⟩ : ∃ s, ℓ s x ≠ 0 := by
      by_contra h
      push Not at h
      exact hx (hℓ x h)
    refine ⟨Fin.snoc q s, fun t => ?_⟩
    obtain ⟨x0, hx0'⟩ := hq (Fin.init t)
    refine ⟨x0 + ((t (Fin.last m) - ℓ s x0) / ℓ s x) • x, funext fun j => ?_⟩
    refine Fin.lastCases ?_ (fun j => ?_) j
    · simp only [Fin.snoc_last, map_add, map_smul, smul_eq_mul]
      rw [div_mul_cancel₀ _ hs]
      ring
    · simp only [Fin.snoc_castSucc, map_add, map_smul, hΦx, smul_eq_mul, mul_zero, add_zero]
      exact congr_fun hx0' j

theorem pointFormRank_holds.eq_zero_of_eventually_eval {d : ℕ} (f : MvPolynomial (Fin d) ℂ) (a : Fin d → ℂ)
    (h : ∀ᶠ z in 𝓝 a, eval z f = 0) : f = 0 := by
  have han : AnalyticOnNhd ℂ (fun z => eval z f) Set.univ := AnalyticOnNhd.eval_mvPolynomial f
  have h0 := han.eqOn_zero_of_preconnected_of_eventuallyEq_zero isPreconnected_univ (Set.mem_univ a) h
  exact MvPolynomial.funext fun z => by simpa using h0 (Set.mem_univ z)

theorem pointFormRank_holds.proof (hA : RatioAlgDep.Statement) : pointFormRank_holds.Statement := by
  intro K _ ι _ Q d n F y hQ hdn hF hev
  classical
  have hy : F y ∈ mcPts Q := hev.self_of_nhds
  choose c hc using hy.1
  have hcomp : ∀ p, AnalyticAt ℂ (fun y' => F y' p) y := analyticAt_pi_iff.mp hF
  have hDy : ∀ p : Σ k, ι k, F y ⟨p.1, c p.1⟩ ≠ 0 := fun p => hc p.1
  set r : (Σ k, ι k) → (Fin n → ℂ) → ℂ := fun p y' => F y' p / F y' ⟨p.1, c p.1⟩ with hr_def
  have hr : ∀ p, AnalyticAt ℂ (r p) y := fun p => (hcomp p).div (hcomp _) (hDy p)
  have hnear : ∀ᶠ y' in 𝓝 y, ∀ k, F y' ⟨k, c k⟩ ≠ 0 :=
    Filter.eventually_all.mpr fun k => (hcomp ⟨k, c k⟩).continuousAt.eventually_ne (hc k)
  set F' := fderiv ℂ F y with hF'_def
  have hF' : HasFDerivAt F F' y := hF.differentiableAt.hasFDerivAt
  set ℓ : (Σ k, ι k) → (Fin n → ℂ) →L[ℂ] ℂ := fun p => fderiv ℂ (r p) y with hℓ_def
  have hℓ : ∀ p, HasFDerivAt (r p) (ℓ p) y := fun p => (hr p).differentiableAt.hasFDerivAt
  have hprod : ∀ p, HasFDerivAt (fun y' => r p y' * F y' ⟨p.1, c p.1⟩)
      (r p y • (ContinuousLinearMap.proj ⟨p.1, c p.1⟩).comp F' + F y ⟨p.1, c p.1⟩ • ℓ p) y :=
    fun p => (hℓ p).mul (hasFDerivAt_pi'.mp hF' _)
  have heq : ∀ p, (fun y' => F y' p) =ᶠ[𝓝 y] fun y' => r p y' * F y' ⟨p.1, c p.1⟩ :=
    fun p => hnear.mono fun y' hy' => (div_mul_cancel₀ _ (hy' p.1)).symm
  have hderiv : ∀ p, (ContinuousLinearMap.proj p).comp F' =
      r p y • (ContinuousLinearMap.proj ⟨p.1, c p.1⟩).comp F' + F y ⟨p.1, c p.1⟩ • ℓ p :=
    fun p => (hasFDerivAt_pi'.mp hF' p).unique ((hprod p).congr_of_eventuallyEq (heq p))
  by_contra hno
  push Not at hno
  have hinj : ∀ x, (∀ p, ℓ p x = 0) → x = 0 := by
    intro x hx
    by_contra hx0
    refine hno x hx0 (fun k => F' x ⟨k, c k⟩ / F y ⟨k, c k⟩) ?_
    funext p
    have h1 := congrArg (fun L => L x) (hderiv p)
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply, FunLike.coe_add, Pi.add_apply,
      FunLike.coe_smul, Pi.smul_apply, smul_eq_mul, hx p, mul_zero, add_zero] at h1
    rw [h1, bsmul, hr_def]
    ring
  obtain ⟨q, hq⟩ := pointFormRank_holds.exists_surj_coords (fun p => (ℓ p).toLinearMap)
    (fun x hx => hinj x (by simpa using hx)) d hdn
  have hg : HasStrictFDerivAt (fun y' j => r (q j) y') (ContinuousLinearMap.pi fun j => ℓ (q j)) y :=
    hasStrictFDerivAt_pi.mpr fun j => (hr (q j)).hasStrictFDerivAt
  have hrange : (ContinuousLinearMap.pi fun j => ℓ (q j) : (Fin n → ℂ) →L[ℂ] (Fin d → ℂ)).range = ⊤ := by
    refine LinearMap.range_eq_top.mpr fun t => ?_
    obtain ⟨x, hx⟩ := hq t
    exact ⟨x, hx⟩
  have hmap := hg.map_nhds_eq_of_surj hrange
  obtain ⟨f, hf0, hfz⟩ := hA K ι Q d c q hQ
  have hev' : ∀ᶠ y' in 𝓝 y, eval (fun j => r (q j) y') (map (Int.castRingHom ℂ) f) = 0 := by
    filter_upwards [hev, hnear] with y' hy' hy'c
    exact hfz (F y') hy'.2 hy'c
  have hz : ∀ᶠ z in 𝓝 ((fun y' j => r (q j) y') y), eval z (map (Int.castRingHom ℂ) f) = 0 := by
    rw [← hmap]
    exact Filter.eventually_map.mpr hev'
  have h0 := pointFormRank_holds.eq_zero_of_eventually_eval _ _ hz
  exact hf0 (MvPolynomial.map_injective _ (Int.castRingHom ℂ).injective_int (h0.trans (map_zero _).symm))

end GroundTheory.Heights₂.Heights.Inter
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.Intersections.FlagBundleSt
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4

section Gen

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem aeval_comp_X {σ A B : Type} [CommRing A] [CommRing B] {_ : Algebra ℤ B}
    (φ : MvPolynomial σ ℤ →+* A) (e : A →+* B) (f : MvPolynomial σ ℤ) :
    aeval (fun q => e (φ (X q))) f = e (φ f) := by
  induction f using MvPolynomial.induction_on with
  | C a =>
    rw [aeval_C]
    exact (eq_intCast (algebraMap ℤ B) a).trans (eq_intCast ((e.comp φ).comp C) a).symm
  | add p q hp hq => rw [map_add, hp, hq, map_add, map_add]
  | mul_X p q hp => rw [map_mul, hp, aeval_X, map_mul, map_mul]

omit [Fintype K] [∀ k, Fintype (ι k)] in

theorem aeval_genPt (P : Ideal (MRing ι)) {_ : Algebra ℤ (FnField P)} (f : MRing ι) :
    aeval (genPt P) f = algebraMap (MRing ι ⧸ P) (FnField P) (Ideal.Quotient.mk P f) :=
  aeval_comp_X (Ideal.Quotient.mk P) (algebraMap (MRing ι ⧸ P) (FnField P)) f

omit [Fintype K] [∀ k, Fintype (ι k)] in

theorem ker_algebraMap_comp_mk (P : Ideal (MRing ι)) :
    RingHom.ker ((algebraMap (MRing ι ⧸ P) (FnField P)).comp (Ideal.Quotient.mk P)) = P := by
  rw [RingHom.ker_comp_of_injective _ (IsFractionRing.injective (MRing ι ⧸ P) (FnField P)), Ideal.mk_ker]

omit [Fintype K] [∀ k, Fintype (ι k)] in

theorem flagMap_X_inl (P : Ideal (MRing ι)) {N1 n : ℕ} (B : Matrix (Fin n) (Fin N1) (FnField P))
    (p : Σ k, ι k) :
    flagMap P B (X (inlV (ι₂ := PluckerBlocks N1 n) p)) = C (genPt P p) := by
  obtain ⟨k, i⟩ := p
  simp [flagMap, inlV]

omit [Fintype K] [∀ k, Fintype (ι k)] in

theorem imageZ_flagIdeal (P : Ideal (MRing ι)) {N1 n : ℕ} (B : Matrix (Fin n) (Fin N1) (FnField P)) :
    imageZ (inlV (ι₂ := PluckerBlocks N1 n)) (flagIdeal P B) = P := by
  have h : (flagMap P B).comp (rename (inlV (ι₂ := PluckerBlocks N1 n)) : MRing ι →ₐ[ℤ] _).toRingHom =
      (C : FnField P →+* MvPolynomial (Fin n × Fin n) (FnField P)).comp
        ((algebraMap (MRing ι ⧸ P) (FnField P)).comp (Ideal.Quotient.mk P)) :=
    MvPolynomial.ringHom_ext (fun r => by
      rw [← RingHom.comp_apply _ C r, ← RingHom.comp_apply _ C r, eq_intCast, eq_intCast]) fun p => by
      simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, rename_X]
      exact flagMap_X_inl P B p
  rw [imageZ, flagIdeal, RingHom.comap_ker, h, RingHom.ker_comp_of_injective _ (C_injective _ _),
    ker_algebraMap_comp_mk]

def flagGenFibre (P : Ideal (MRing ι)) (hP : P.IsPrime) {N1 n : ℕ}
    (B : Matrix (Fin n) (Fin N1) (FnField P)) :
    GenFibre (inlV (ι := ι) (ι₂ := PluckerBlocks N1 n)) (flagIdeal P B) :=
  haveI := hP
  { Φ := FnField P
    Φ' := FractionRing (MvPolynomial (Fin n × Fin n) (FnField P))
    x := genPt P
    x' := fun q => algebraMap (MvPolynomial (Fin n × Fin n) (FnField P)) _ (flagMap P B (X q))
    ker_x := by
      rw [imageZ_flagIdeal]
      ext f
      rw [RingHom.mem_ker, aeval_genPt]
      exact SetLike.ext_iff.1 (ker_algebraMap_comp_mk P) f
    gen := fun c => by
      obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := MRing ι ⧸ P) c
      obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective a
      obtain ⟨g, rfl⟩ := Ideal.Quotient.mk_surjective b
      refine ⟨f, g, ?_, ?_⟩
      · rw [aeval_genPt]
        exact IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hb
      · rw [aeval_genPt, aeval_genPt]
    genericFibre_ker_target := by
      ext f
      rw [RingHom.mem_ker, aeval_comp_X (flagMap P B), ← RingHom.comp_apply, ← RingHom.mem_ker,
        RingHom.ker_comp_of_injective _ (IsFractionRing.injective _ _)]
      rfl
    compat := fun p => by
      show algebraMap _ _ (flagMap P B (X (inlV p))) = _
      rw [flagMap_X_inl, IsScalarTower.algebraMap_apply (FnField P) (MvPolynomial (Fin n × Fin n) (FnField P))
        (FractionRing (MvPolynomial (Fin n × Fin n) (FnField P))), algebraMap_eq] }

end Gen

def FlagArith.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (N1 t n : ℕ)
    (P : Ideal (MRing ι)) (d : ℕ) (c : Fin t → Fin N1 → MRing ι) (m : K → ℕ)
    (B : Matrix (Fin n) (Fin N1) (FnField P)),
    IsArithVar P d → IsQuotRows P c m n → IsKerBasis P c B →
    IsArithVar (flagIdeal P B) (flagDim n + d)

def FlagFibre.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (N1 t n : ℕ)
    (P : Ideal (MRing ι)) (d : ℕ) (c : Fin t → Fin N1 → MRing ι) (m : K → ℕ)
    (B : Matrix (Fin n) (Fin N1) (FnField P)) (hP : IsArithVar P d),
    IsQuotRows P c m n → IsKerBasis P c B →
    ∀ J₀ : IFamily ℚ (PluckerBlocks n n), IsFieldIntersection J₀ →
      ∃ J : IFamily (flagGenFibre P hP.2.1.1 B).Φ (fibreIdx (FlagBundleBlocks ι N1 n) Sum.inl),
        IsFieldIntersection J ∧
        ∀ a : Fin (flagDim n) → K ⊕ Fin (n - 1) → ℤ,
          J (fibreIdeal Sum.inl (flagGenFibre P hP.2.1.1 B)) (flagDim n)
              (fun j => fibreDeg Sum.inl (a j)) =
            J₀ (flagIdealQ n) (flagDim n) (fun i j => a i (Sum.inr j))

def flagGenFibre_inhabited :
    GenFibre (inlV (ι := GlobalTheory 2) (ι₂ := PluckerBlocks 3 3)) (flagIdeal (⊥ : Ideal (MRing (GlobalTheory 2))) (idRows 3)) :=
  flagGenFibre ⊥ Ideal.isPrime_bot (idRows 3)

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.Intersections.FlagDimSt
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1

def flagIdealOver (F : Type) [Field F] (n : ℕ) : Ideal (MRingOver F (PluckerBlocks n n)) :=
  RingHom.ker (aeval (fun q : Σ j, PluckerBlocks n n j => flagMinor (genMat F n) q.1 q.2) :
    MRingOver F (PluckerBlocks n n) →ₐ[F] MvPolynomial (Fin n × Fin n) F)

theorem flagIdealQ_eq (n : ℕ) : flagIdealQ n = flagIdealOver ℚ n := rfl

theorem flagIdealOver_isPrime (F : Type) [Field F] (n : ℕ) : (flagIdealOver F n).IsPrime :=
  RingHom.ker_isPrime _

def FlagDim.Statement : Prop :=
  ∀ (F : Type) [Field F] (n : ℕ), IsProjVarF (flagIdealOver F n) (flagDim n)

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.Intersections.FlagPivot
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter

open MvPolynomial

def pivotCols {n : ℕ} (a : Fin (n - 1)) (b : Fin n) : Fin (a + 1) → Fin n :=
  fun c => if h : (c : ℕ) < a then ⟨c, by have := a.2; omega⟩ else b

def pivotMinor {R : Type} [CommRing R] {n : ℕ} (M : Matrix (Fin n) (Fin n) R) (a : Fin (n - 1)) (b : Fin n) : R :=
  (M.submatrix (Fin.castLE (by have := a.2; omega)) (pivotCols a b)).det

def leadMinor {R : Type} [CommRing R] {n : ℕ} (M : Matrix (Fin n) (Fin n) R) (a : Fin (n - 1)) : R :=
  pivotMinor M a (Fin.castLE (Nat.sub_le n 1) a)

def pivotMatrix {R : Type} [CommRing R] {n : ℕ} (M : Matrix (Fin n) (Fin n) R) : Matrix (Fin n) (Fin n) R :=
  Matrix.of fun r b => if h : (r : ℕ) < n - 1 then pivotMinor M ⟨r, h⟩ b else 0

theorem pivotCols_strictMono {n : ℕ} (a : Fin (n - 1)) (b : Fin n) (hab : (a : ℕ) ≤ b) :
    StrictMono (pivotCols a b) := by
  intro c d hcd
  have hcd' : (c : ℕ) < d := hcd
  simp only [pivotCols]
  split_ifs with h1 h2 h2
  · exact Fin.mk_lt_mk.mpr hcd'
  · exact Fin.mk_lt_mk.mpr (by omega)
  · omega
  · omega

theorem card_image_pivotCols {n : ℕ} (a : Fin (n - 1)) (b : Fin n) (hab : (a : ℕ) ≤ b) :
    (Finset.univ.image (pivotCols a b)).card = a + 1 := by
  rw [Finset.card_image_of_injective _ (pivotCols_strictMono a b hab).injective, Finset.card_univ, Fintype.card_fin]

theorem pivotMinor_eq_flagMinor {R : Type} [CommRing R] {n : ℕ} (M : Matrix (Fin n) (Fin n) R) (a : Fin (n - 1))
    (b : Fin n) (hab : (a : ℕ) ≤ b) :
    pivotMinor M a b = flagMinor M a ⟨Finset.univ.image (pivotCols a b), card_image_pivotCols a b hab⟩ := by
  unfold pivotMinor flagMinor
  congr 2
  exact (Finset.orderEmbOfFin_unique (card_image_pivotCols a b hab) (fun c => Finset.mem_image_of_mem _ (Finset.mem_univ c))
    (pivotCols_strictMono a b hab))

theorem pivotMinor_eq_zero {R : Type} [CommRing R] {n : ℕ} (M : Matrix (Fin n) (Fin n) R) (a : Fin (n - 1))
    (b : Fin n) (hba : (b : ℕ) < a) : pivotMinor M a b = 0 := by
  unfold pivotMinor
  refine Matrix.det_zero_of_column_eq (i := ⟨b, by omega⟩) (j := Fin.last a) (fun h => by
    have := congrArg Fin.val h; simp at this; omega) fun k => ?_
  simp [pivotCols, hba]

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.Intersections.ImportsBisBis
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

theorem regularityLocalDimension_holds.proof (hF : LocRingFrac.Statement) (hL : LocRingLocal.Statement) (hN : LocRingNoeth.Statement)
    (hPw : LocRingPow.Statement) : regularityLocalDimension_holds.Statement := by
  intro K _ ι _ P s a W hP hs hsP hW
  have hPp : P.IsPrime := hP.2.1.1
  have := hPp
  have hWp : W.IsPrime := hW.1.1.1
  have hPW : P ≤ W := le_sup_left.trans hW.1.1.2
  have hsW : s ∈ W := hW.1.1.2 (Ideal.mem_sup_right (Ideal.mem_span_singleton_self s))
  obtain ⟨hloc, hunit⟩ := hL K ι P W hPp hWp hPW
  have hnoeth := hN K ι P W hPp hWp hPW hW.2
  have := hloc
  have := hnoeth
  refine ⟨hloc, hnoeth, ?_⟩
  choose c hc using hW.2
  have ht : IsMultiHomog (∏ k, (X ⟨k, c k⟩ : MRing ι) ^ a k) a := AvoidRing.isMultiHomog_coordProd c a
  have htW : (∏ k, (X ⟨k, c k⟩ : MRing ι) ^ a k) ∉ W := AvoidRing.coordProd_not_mem hWp c hc a
  have htP : Ideal.Quotient.mk P (∏ k, (X ⟨k, c k⟩ : MRing ι) ^ a k) ∈ nonZeroDivisors (MRing ι ⧸ P) :=
    mem_nonZeroDivisors_of_ne_zero fun h => htW (hPW (Ideal.Quotient.eq_zero_iff_mem.mp h))
  set xF := IsLocalization.mk' (FractionRing (MRing ι ⧸ P)) (Ideal.Quotient.mk P s) ⟨_, htP⟩ with hxF
  have hxmem : xF ∈ locRing P W := Subring.subset_closure ⟨s, _, a, htP, htW, hs, ht, rfl⟩
  have hxt : xF * algebraMap (MRing ι ⧸ P) (FractionRing (MRing ι ⧸ P))
      (Ideal.Quotient.mk P (∏ k, (X ⟨k, c k⟩ : MRing ι) ^ a k)) =
      algebraMap (MRing ι ⧸ P) (FractionRing (MRing ι ⧸ P)) (Ideal.Quotient.mk P s) :=
    IsLocalization.mk'_spec _ _ _
  set x : locRing P W := ⟨xF, hxmem⟩
  have hx0 : x ≠ 0 := by
    intro h
    have h' : xF = 0 := congrArg Subtype.val h
    rw [h', zero_mul, eq_comm, IsFractionRing.to_map_eq_zero_iff, Ideal.Quotient.eq_zero_iff_mem] at hxt
    exact hsP hxt
  have hxu : ¬ IsUnit x := fun h => (hunit x s _ a hs ht htW hxt).mp h hsW
  have hmin : IsLocalRing.maximalIdeal (locRing P W) ∈ (Ideal.span {x}).minimalPrimes := by
    refine ⟨⟨inferInstance, (Ideal.span_singleton_le_iff_mem _).mpr hxu⟩, fun q hq _ y hy => ?_⟩
    obtain ⟨u, v, b, hu, hv, hvW, hyuv⟩ := hF K ι P W hPp hWp hPW y y.2
    have huW : u ∈ W := by
      by_contra h
      exact hy ((hunit y u v b hu hv hvW hyuv).mpr h)
    obtain ⟨n, z, hz, hyz⟩ :=
      hPw K ι P s _ a W xF u v b y hPp hP.2.1.2.1 hs hsP hW ht htW hxt hu hv huW hvW hyuv
    have e : y ^ n = x * ⟨z, hz⟩ := Subtype.ext (by simpa using hyz)
    have hq1 := hq.1
    exact hq1.mem_of_pow_mem n (e ▸ q.mul_mem_right _ (hq.2 (Ideal.mem_span_singleton_self x)))
  have h1 := Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes _ _ hmin
  have h2 := Ideal.height_span_singleton_eq_one_of_mem_nonZeroDivisors (mem_nonZeroDivisors_of_ne_zero hx0) hxu
  have h3 := Ideal.height_mono hmin.1.2
  rw [← IsLocalRing.maximalIdeal_height_eq_ringKrullDim, le_antisymm h1 (h2 ▸ h3)]
  rfl

end

end GroundTheory.Heights₂.Heights.Inter
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.Intersections.ImportsFurtherTail
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4

def pointForm_holds.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (K' : Type) [Fintype K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)]
    (κ : K → K') (v : (Σ k, ι k) → (Σ k', ι' k')) (P' : Ideal (MRing ι')) (d n : ℕ)
    (L : Fin n → HermLine ι) (L' : Fin n → HermLine ι') (g : ((Σ k', ι' k') → ℂ) → ℝ),
    IsBlockMap κ v → IsArithVar P' (n + 1) → IsArithVar (imageZ v P') d → d < n + 1 →
    (∀ j, IsSmoothHerm (L j)) → (∀ j, IsPullHerm κ v (L j) (L' j)) →
    ptsIntegral P' (fun j z => Real.log ((L' j).h z)) g = 0

end GroundTheory.Heights₂.Heights.Inter
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.Intersections.ImportsLast
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo IsLocalRing

noncomputable section

theorem regularityDehomogenization_holds.proof (h₁ : GroundTheory.Heights₂.Heights.FieldNumbers.LocalizedQuotientLength.Statement.{0, 0})
    (h₂ : regularityLocalFlat_holds.Statement) : regularityDehomogenization_holds.Statement := by
  intro K _ ι _ P s t a W y hP hs hsP hW ht htW hy
  have hWp : W.IsPrime := hW.1.1.1
  have hPW : P ≤ W := le_sup_left.trans hW.1.1.2
  have := hP.1
  have := hWp
  have hWm : IsMultiProjPrime W := ⟨hWp, isMultiHomogIdeal_of_mem_minimalPrimes hP.2.1 hs hW.1, hW.2⟩

  have htnz : Ideal.Quotient.mk P t ∈ nonZeroDivisors (MRing ι ⧸ P) := by
    refine mem_nonZeroDivisors_of_ne_zero ?_
    rw [Ne, Ideal.Quotient.eq_zero_iff_mem]
    exact fun h => htW (hPW h)
  have hyO : y ∈ locRing P W := by
    refine Subring.subset_closure ⟨s, t, a, htnz, htW, hs, ht, ?_⟩
    rw [IsLocalization.eq_mk'_iff_mul_eq]
    exact hy
  refine ⟨hyO, ?_⟩
  obtain ⟨_, _, _, hmax⟩ := h₂ K ι P W hP hWm hPW
  have : IsLocalHom (algebraMap (locRing P W) (coneLocRing P W hPW)) :=
    ((local_hom_TFAE _).out 2 0).mp hmax.le

  have hu : IsUnit (algebraMap (MRing ι ⧸ P) (coneLocRing P W hPW) (Ideal.Quotient.mk P t)) :=
    IsLocalization.map_units (coneLocRing P W hPW)
      (⟨_, ⟨t, htW, rfl⟩⟩ : W.primeCompl.map (Ideal.Quotient.mk P))
  have hs' : algebraMap (MRing ι ⧸ P) (coneLocRing P W hPW) (Ideal.Quotient.mk P s) =
      algebraMap (locRing P W) (coneLocRing P W hPW) ⟨y, hyO⟩ *
        algebraMap (MRing ι ⧸ P) (coneLocRing P W hPW) (Ideal.Quotient.mk P t) := by
    apply Subtype.ext
    rw [Subalgebra.coe_mul, locRing.algebraMap_cone_coe, Subalgebra.coe_algebraMap,
      Subalgebra.coe_algebraMap, hy]
  have hspan : Ideal.span {algebraMap (MRing ι ⧸ P) (coneLocRing P W hPW) (Ideal.Quotient.mk P s)} =
      (Ideal.span {(⟨y, hyO⟩ : locRing P W)}).map (algebraMap (locRing P W) (coneLocRing P W hPW)) := by
    rw [Ideal.map_span, Set.image_singleton, hs', Ideal.span_singleton_mul_right_unit hu]

  have key : ∀ (A B : Type) [CommRing A] [CommRing B] [IsLocalRing A] [IsLocalRing B]
      [Algebra A B] [IsLocalHom (algebraMap A B)] [Module.Flat A B],
      (maximalIdeal A).map (algebraMap A B) = maximalIdeal B → ∀ x : A,
        Module.length B (B ⧸ (Ideal.span {x}).map (algebraMap A B)) = Module.length A (A ⧸ Ideal.span {x}) := by
    intro A B _ _ _ _ _ _ _ hm x
    have hres : Module.length B (B ⧸ maximalIdeal B) = 1 := Module.length_eq_one_iff.mpr
      (isSimpleModule_iff_quot_maximal.mpr ⟨_, maximalIdeal.isMaximal _, ⟨LinearEquiv.refl _ _⟩⟩)
    rw [(Algebra.TensorProduct.quotIdealMapEquivTensorQuot B (Ideal.span {x})).toLinearEquiv.length_eq,
      IsLocalRing.length_baseChange, hm, hres, mul_one]
  unfold multAt
  rw [dif_pos hWp, h₁ (MRing ι) P W s (coneLocRing P W hPW) inferInstance, hspan, locIdeal_eq_span hyO,
    key (locRing P W) (coneLocRing P W hPW) hmax]

end

end GroundTheory.Heights₂.Heights.Inter
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.Intersections.ImportsTerTail
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

def RegularityLocalFinite.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι))
    (s : MRing ι) (a : K → ℕ) (W : Ideal (MRing ι)) (y : FractionRing (MRing ι ⧸ P)),
    IsArithVar P 1 → IsMultiHomog s a → s ∉ P → W ∈ divSupp P s → y ∈ locRing P W → y ≠ 0 →
    Finite (locRing P W ⧸ locIdeal P W y)

end

end GroundTheory.Heights₂.Heights.Inter
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.Intersections.IsMultiHomogFirstCoordinate
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4

def ProjectivePointVertical.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (K' : Type) [Fintype K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)]
    (κ : K → K') (v : (Σ k, ι k) → (Σ k', ι' k')) (P' : Ideal (MRing ι')) (d n : ℕ)
    (L : Fin n → HermLine ι) (L' : Fin n → HermLine ι') (t : MRing ι) (a : K → ℕ),
    IsBlockMap κ v → IsArithVar P' (n + 1) → IsArithVar (imageZ v P') d → d < n + 1 →
    (∀ j, IsPullHerm κ v (L j) (L' j)) → IsMultiHomog t a → t ∉ imageZ v P' →
    vertR P' L' (rename v t) = 0

end GroundTheory.Heights₂.Heights.Inter
end
end

