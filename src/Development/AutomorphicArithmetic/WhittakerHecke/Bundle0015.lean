import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.CharacterNorms.Bundle0001
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.UnramifiedSplitting.Bundle0004
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.UnramifiedSplitting.Bundle0002
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.CmBridge
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.FoundBridge
import GroundTheory.AutomorphicForms.CuspidalDiscreteness.CuspFormsSiegel
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.UnramifiedSplitting.Bundle0001
import GroundTheory.GlobalFields.TateThesis.AdelicChar

-- bundled from Development.AutomorphicArithmetic.WhittakerHecke.DiagonalMulArchimedeanCurveEqUnipotentMul
section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.RankTwoDescent UpperTheory.ConvolutionTheory.RankTwoDescent.TA
open UpperTheory.ConvolutionTheory.R2.G (FS2 nE)
open scoped Classical

private theorem inf_const (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (c : ℝ) :
    GroundTheory.Global.InfinitePlace.infiniteAdeleRingMap (K := ℚ) (L := E) (TR.infEq ℚ fun _ => c) =
      infEq E fun _ => (c : ℂ) := by
  funext w
  let f : ℝ →+* w.Completion := (Pi.evalRingHom (fun w : InfinitePlace E => w.Completion) w).comp
    ((GroundTheory.Global.InfinitePlace.infiniteAdeleRingMap (K := ℚ) (L := E)).comp
      ((TR.infEq ℚ).toRingHom.comp (Pi.constRingHom (InfinitePlace ℚ) ℝ)))
  let g : ℝ →+* w.Completion := (Pi.evalRingHom (fun w : InfinitePlace E => w.Completion) w).comp
    ((infEq E).toRingHom.comp ((Pi.constRingHom (InfinitePlace E) ℂ).comp Complex.ofRealHom))
  have hf : Continuous f := (continuous_apply w).comp
    (GroundTheory.Global.InfinitePlace.continuous_infiniteAdeleRingMap.comp
      ((TR.continuous_infEq ℚ).comp (continuous_pi fun _ => continuous_id)))
  have hg : Continuous g := (continuous_apply w).comp
    ((continuous_infEq E).comp (continuous_pi fun _ => Complex.continuous_ofReal))
  have h := Rat.denseRange_cast (𝕜 := ℝ) |>.equalizer hf hg (funext fun q => by simp)
  exact congrFun h c

private theorem re_const (x : A ℚ) : TR.pInf ℚ x = fun _ => re x := by
  funext v
  rw [Subsingleton.elim v Rat.infinitePlace]
  rfl

private theorem pInf_adeleMap (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (x : A ℚ) :
    pInf E (AdeleBaseChange.adeleMap ℚ E x) = fun _ => (re x : ℂ) := by
  have h : x.1 = TR.infEq ℚ fun _ => re x := by
    rw [← re_const]
    exact ((TR.infEq ℚ).apply_symm_apply x.1).symm
  change (infEq E).symm (GroundTheory.Global.InfinitePlace.infiniteAdeleRingMap x.1) = _
  rw [h, inf_const, RingEquiv.symm_apply_apply]

private theorem pInf_s {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] (x : Cinf E) :
    pInf E (GlobalTheory.CuspRep.sInf E x) = x := (infEq E).symm_apply_apply x

private theorem pFin_s {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] (x : Cinf E) :
    pFin E (GlobalTheory.CuspRep.sInf E x) = 0 := rfl

private theorem re_s (c : ℝ) : re (TR.sInf ℚ fun _ => c) = c :=
  congrFun ((TR.infEq ℚ).symm_apply_apply fun _ => c) Rat.infinitePlace

private theorem map_n {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) (g : Matrix.GeneralLinearGroup (Fin 2) R) (z : R)
    (hg : g.val = !![1, z; 0, 1]) (h : Matrix.GeneralLinearGroup (Fin 2) S) (hh : h.val = !![1, f z; 0, 1]) :
    Matrix.GeneralLinearGroup.map f g = h := by
  refine Units.ext ?_
  rw [hh]
  ext i j
  change f (g.val i j) = _
  rw [hg]
  fin_cases i <;> fin_cases j <;> simp

private theorem step1 {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] (D : Dat ℚ E) (k : GL (Fin 2) (A E)) (t : ℝ) :
    k * infGL E 2 (cv D k t) = gl (nU (GlobalTheory.CuspRep.sInf E (t • thInf D))) * k := by
  refine ga_ext ?_ ?_
  · rw [map_mul, map_mul, pInf_infGL]
    have h : Matrix.GeneralLinearGroup.map (pInf E) (gl (nU (GlobalTheory.CuspRep.sInf E (t • thInf D)))) = nC (t • thInf D) :=
      map_n _ _ _ rfl _ (by rw [pInf_s]; rfl)
    rw [h]
    change kInf k * cv D k t = nC (t • thInf D) * kInf k
    simp only [cv, mul_assoc, mul_inv_cancel_left]
  · rw [map_mul, map_mul, pFin_infGL, mul_one]
    have h : Matrix.GeneralLinearGroup.map (pFin E) (gl (nU (GlobalTheory.CuspRep.sInf E (t • thInf D)))) = 1 := by
      refine map_n _ _ _ rfl _ ?_
      rw [pFin_s]
      ext i j
      fin_cases i <;> fin_cases j <;> simp
    rw [h, one_mul]

private theorem em_aE {E : Type} [Field E] [NumberField E] (y : (A ℚ)ˣ) :
    em E (aE y) = aE (Units.map (AdeleBaseChange.adeleMap ℚ E : A ℚ →* A E) y) := by
  refine Units.ext ?_
  ext i j
  change AdeleBaseChange.adeleMap ℚ E ((aE y).val i j) = _
  fin_cases i <;> fin_cases j <;> simp [aE]

private theorem step3 {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] (D : Dat ℚ E) (y : (A ℚ)ˣ) (t : ℝ) :
    AdeleBaseChange.adeleMap ℚ E (y : A ℚ) * GlobalTheory.CuspRep.sInf E (t • thInf D) =
      D.mkE 0 (TR.sInf ℚ fun _ => t * re (y : A ℚ)) := by
  refine ad_ext ?_ ?_
  · rw [Dat.mkE, map_zero, zero_add, map_mul, map_mul, pInf_s, pInf_adeleMap, pInf_adeleMap, re_s]
    change _ = _ * thInf D
    funext w
    simp [Pi.mul_apply, Pi.smul_apply]
    ring
  · rw [Dat.mkE, map_zero, zero_add, map_mul, map_mul, pFin_s, mul_zero]
    have : pFin E (AdeleBaseChange.adeleMap ℚ E (TR.sInf ℚ fun _ => t * re (y : A ℚ))) = 0 :=
      map_zero (AdeleBaseChange.finiteAdeleMap ℚ E)
    rw [this, zero_mul]

theorem UpperTheory.diagonal_mul_archimedeanCurve_eq_unipotent_mul :
    ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (D : Dat ℚ E) (y : (A ℚ)ˣ) (k : GL (Fin 2) (A E)) (t : ℝ),
        em E (aE y) * k * infGL E 2 (cv D k t) = nE D ![0, TR.sInf ℚ fun _ => t * re (y : A ℚ)] * (em E (aE y) * k) := by
  intro E _ _ _ D y k t
  have h3 := step3 D y t
  have hn : nE D ![0, TR.sInf ℚ fun _ => t * re (y : A ℚ)] =
      gl (nU (AdeleBaseChange.adeleMap ℚ E (y : A ℚ) * GlobalTheory.CuspRep.sInf E (t • thInf D))) := by
    rw [h3]
    rfl
  rw [mul_assoc, step1, hn, ← mul_assoc, ← mul_assoc, em_aE, Pp.a_n]
  rfl
end

-- bundled from Development.AutomorphicArithmetic.WhittakerHecke.EigenformShintaniFormulaAtPlace
section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.RankTwoDescent
open scoped Classical
open UpperTheory.ConvolutionTheory.R2.G (FS2 Rw nE row)
open UpperTheory.V.Af.Smo (EigAt)
open scoped ComplexOrder

private lemma dL_mul {K : Type} [Field K] [NumberField K] {v : H.P K} (a d a' d' : (H.Kv v)ˣ) :
    H.dL a d * H.dL a' d' = H.dL (a * a') (d * d') := by
  refine Units.ext ?_
  ext i j
  fin_cases i <;> fin_cases j <;> simp [H.dL, Matrix.mul_apply, Fin.sum_univ_two]

private lemma dL_one {K : Type} [Field K] [NumberField K] {v : H.P K} : (H.dL (1 : (H.Kv v)ˣ) 1) = 1 := by
  refine Units.ext ?_
  ext i j
  fin_cases i <;> fin_cases j <;> simp [H.dL]

private lemma dL_nL {K : Type} [Field K] [NumberField K] {v : H.P K} (a : (H.Kv v)ˣ) (b : H.Kv v) :
    H.dL a 1 * H.nL b = H.nL ((a : H.Kv v) * b) * H.dL a 1 := by
  refine Units.ext ?_
  ext i j
  fin_cases i <;> fin_cases j <;> simp [H.dL, H.nL, Matrix.mul_apply, Fin.sum_univ_two]

private lemma hs_succ (a b : ℂ) (k : ℕ) :
    ∑ i ∈ Finset.range (k + 1 + 1), a ^ i * b ^ (k + 1 - i) =
      b * ∑ i ∈ Finset.range (k + 1), a ^ i * b ^ (k - i) + a ^ (k + 1) := by
  rw [Finset.sum_range_succ, Finset.mul_sum, Nat.sub_self, pow_zero, mul_one]
  congr 1
  refine Finset.sum_congr rfl fun i hi => ?_
  have : k + 1 - i = (k - i) + 1 := by
    have := Finset.mem_range.1 hi
    omega
  rw [this]
  ring

private lemma tor_loc (K : Type) [Field K] [NumberField K] (v : H.P K) (ϖ : (H.Kv v)ˣ) (hϖ : H.IsU ϖ)
    (χ : H.Kv v → ℂ) (hχ : H.Good χ) (α β : ℂˣ) (W : GL (Fin 2) (H.Kv v) → ℂ)
    (hW : UpperTheory.V.Af.Smo.Eig v {α, β} W) (hn : ∀ b y, W (H.nL b * y) = χ b * W y) (k : ℕ) :
    (H.q v ^ (1 / 2 : ℂ)) ^ k * W (H.dL (ϖ ^ k) 1) =
      (∑ i ∈ Finset.range (k + 1), ((α : ℂ)) ^ i * ((β : ℂ)) ^ (k - i)) * W 1 := by
  obtain ⟨R, hcard, hRint, hR⟩ := UpperTheory.ConvolutionTheory.R2.H.heckeExpl K v ϖ hϖ
  have hsum := fun g => (hR α β W hW g).1
  have hcen := fun g => (hR α β W hW g).2
  obtain ⟨t1, -⟩ := UpperTheory.ConvolutionTheory.R2.H.whTorus K v ϖ hϖ χ hχ α β W hW hn
  have hint : ∀ c : H.Kv v, H.IsInt c → ∀ y, W (H.nL c * y) = W y := fun c hc y => by
    rw [hn, hχ.2.1 c hc, one_mul]
  have hϖint : H.IsInt (ϖ : H.Kv v) := by
    have h' : Valued.v (ϖ : H.Kv v) = _ := hϖ
    show Valued.v (ϖ : H.Kv v) ≤ 1
    rw [h']
    exact_mod_cast (by decide : (Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) ≤ 1)
  have hq0 : H.q v ≠ 0 := by
    have : Ideal.absNorm v.asIdeal ≠ 0 := fun h => v.ne_bot (Ideal.absNorm_eq_zero_iff.1 h)
    exact Nat.cast_ne_zero.2 this
  set s : ℂ := H.q v ^ (1 / 2 : ℂ) with hs
  have hss : s * s = H.q v := by
    rw [hs, ← Complex.cpow_add _ _ hq0]
    norm_num
  have hs0 : s ≠ 0 := fun h => hq0 (by rw [← hss, h, zero_mul])
  have hconst : ∀ x : ℂ, ∑ _b ∈ R, x = H.q v * x := fun x => by
    rw [Finset.sum_const, hcard, nsmul_eq_mul]
    rfl
  have hrec : ∀ k : ℕ, s * ((α : ℂ) + β) * W (H.dL (ϖ ^ (k + 1)) 1) =
      H.q v * W (H.dL (ϖ ^ (k + 1 + 1)) 1) + (α : ℂ) * β * W (H.dL (ϖ ^ k) 1) := fun k => by
    have h2 := hsum (H.dL (ϖ ^ (k + 1)) 1)
    have t3 : ∀ b ∈ R, W (H.dL (ϖ ^ (k + 1)) 1 * H.nL b * H.dL ϖ 1) = W (H.dL (ϖ ^ (k + 1 + 1)) 1) := fun b hb => by
      rw [dL_nL, mul_assoc, hint _ ?_, dL_mul, mul_one, ← pow_succ]
      have hb' : ((ϖ : H.Kv v) ^ (k + 1)) * b ∈ v.adicCompletionIntegers K :=
        mul_mem (pow_mem (show (ϖ : H.Kv v) ∈ v.adicCompletionIntegers K from hϖint) _)
          (show b ∈ v.adicCompletionIntegers K from hRint b hb)
      rw [Units.val_pow_eq_pow_val]
      exact hb'
    rw [Finset.sum_congr rfl t3, hconst] at h2
    have t4 : W (H.dL (ϖ ^ (k + 1)) 1 * H.dL 1 ϖ) = (α : ℂ) * β * W (H.dL (ϖ ^ k) 1) := by
      have := hcen (H.dL (ϖ ^ k) 1)
      rw [dL_mul, one_mul, ← pow_succ] at this
      rw [dL_mul, mul_one, one_mul]
      exact this
    rw [t4] at h2
    exact h2
  have h3 : s * W (H.dL ϖ 1) = ((α : ℂ) + β) * W 1 := by
    refine mul_left_cancel₀ hs0 ?_
    rw [← mul_assoc, hss, ← mul_assoc]
    exact t1
  have key : ∀ k : ℕ, s ^ (k + 1) * W (H.dL (ϖ ^ (k + 1)) 1) =
      β * (s ^ k * W (H.dL (ϖ ^ k) 1)) + (α : ℂ) ^ (k + 1) * W 1 := by
    intro k
    induction k with
    | zero =>
      simp only [zero_add, pow_one, pow_zero, one_mul, dL_one]
      rw [h3]
      ring
    | succ k ih =>
      have h := hrec k
      rw [← hss] at h
      linear_combination (α : ℂ) * ih - s ^ k * h
  induction k with
  | zero => simp [dL_one]
  | succ k ih =>
    rw [key, ih, hs_succ]
    ring

theorem UpperTheory.eigenform_shintani_formula_at_place :
    ∀ (K : Type) [Field K] [NumberField K] (v : H.P K) (ϖ : (H.Kv v)ˣ), H.IsU ϖ → ∀ (χ : H.Kv v → ℂ), H.Good χ → ∀ (α β : ℂˣ) (f : GL (Fin 2) (A K) → ℂ),
          EigAt v {α, β} f → (∀ b h, f (H.lc v (H.nL b) * h) = χ b * f h) → ∀ g, H.KAt v g → ∀ k : ℕ,
          (H.q v ^ (1 / 2 : ℂ)) ^ k * f (aE (H.idl v ϖ ^ k) * g) = (∑ i ∈ Finset.range (k + 1), ((α : ℂ)) ^ i * ((β : ℂ)) ^ (k - i)) * f g := by
  intro K _ _ v ϖ hϖ χ hχ α β f hB hn g hg k
  have hE1 : UpperTheory.V.Af.Smo.Eig v {α, β} fun x => f (H.lc v x * g) := by
    have := (H.fixTr K v f g hg).2 _ hB 1
    simpa [H.lc] using this
  have hnl : ∀ b x, f (H.lc v (H.nL b * x) * g) = χ b * f (H.lc v x * g) := fun b x => by
    rw [map_mul, mul_assoc, hn]
  have h := tor_loc K v ϖ hϖ χ hχ α β _ hE1 hnl k
  have e : H.idl v (ϖ ^ k) = H.idl v ϖ ^ k := map_pow _ _ _
  beta_reduce at h
  rw [(H.lcLaws K v).2.2.2.1, e, map_one, one_mul] at h
  exact h
end

-- bundled from Development.AutomorphicArithmetic.WhittakerHecke.EqConvolutionSquareIndicatorOfEulerFactors
section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.RankTwoDescent
open scoped Classical
open UpperTheory.ConvolutionTheory.R2.G (FS2 Rw nE row)
open UpperTheory.V.Af.Smo (EigAt)
open scoped ComplexOrder

private theorem sqN_eq (N n : ℕ) : sqN N n = if IsSquare n ∧ n.Coprime N then 1 else 0 := by
  unfold sqN
  refine if_congr ?_ rfl rfl
  constructor
  · rintro ⟨m, rfl, hm⟩
    exact ⟨⟨m, rfl⟩, Nat.Coprime.mul_left hm hm⟩
  · rintro ⟨⟨m, rfl⟩, hm⟩
    exact ⟨m, rfl, Nat.Coprime.coprime_mul_right hm⟩

private theorem isSquare_left {m n : ℕ} (h : m.Coprime n) (hs : IsSquare (m * n)) : IsSquare m := by
  obtain ⟨c, hc⟩ := hs
  have hu : IsUnit (gcd m n) := by
    rw [gcd_eq_nat_gcd, h.gcd_eq_one]; exact isUnit_one
  obtain ⟨d, hd⟩ := exists_eq_pow_of_mul_eq_pow (c := c) (k := 2) hu (by rw [hc, sq])
  exact ⟨d, by rw [hd, sq]⟩

private theorem sqN_mul (N : ℕ) {m n : ℕ} (h : m.Coprime n) :
    sqN N (m * n) = sqN N m * sqN N n := by
  have e : (IsSquare (m * n) ∧ (m * n).Coprime N) ↔
      ((IsSquare m ∧ m.Coprime N) ∧ (IsSquare n ∧ n.Coprime N)) := by
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨⟨isSquare_left h h1, Nat.Coprime.coprime_mul_right h2⟩,
        ⟨isSquare_left h.symm (by rwa [mul_comm]), Nat.Coprime.coprime_mul_left h2⟩⟩
    · rintro ⟨⟨h1, h2⟩, h3, h4⟩
      exact ⟨h1.mul h3, Nat.Coprime.mul_left h2 h4⟩
  rw [sqN_eq, sqN_eq, sqN_eq]
  by_cases h1 : IsSquare m ∧ m.Coprime N
  · by_cases h2 : IsSquare n ∧ n.Coprime N
    · rw [if_pos h1, if_pos h2, if_pos (e.2 ⟨h1, h2⟩), mul_one]
    · rw [if_neg h2, if_neg (fun x => h2 (e.1 x).2), mul_zero]
  · rw [if_neg h1, if_neg (fun x => h1 (e.1 x).1), zero_mul]

private theorem sqN_one (N : ℕ) : sqN N 1 = 1 := by
  rw [sqN_eq, if_pos ⟨⟨1, rfl⟩, Nat.coprime_one_left N⟩]

private theorem isSquare_pow_iff {p : ℕ} (hp : p.Prime) (j : ℕ) : IsSquare (p ^ j) ↔ Even j := by
  constructor
  · rintro ⟨m, hm⟩
    have hd : m ∣ p ^ j := ⟨m, hm⟩
    obtain ⟨i, -, rfl⟩ := (Nat.dvd_prime_pow hp).1 hd
    rw [← pow_add] at hm
    exact ⟨i, Nat.pow_right_injective hp.two_le hm⟩
  · rintro ⟨i, rfl⟩
    exact ⟨p ^ i, pow_add p i i⟩

private theorem conv_pow (f g : ℕ → ℂ) {p : ℕ} (hp : p.Prime) (k : ℕ) :
    LSeries.convolution f g (p ^ k) =
      PowerSeries.coeff k ((PowerSeries.mk fun i => f (p ^ i)) * PowerSeries.mk fun i => g (p ^ i)) := by
  rw [LSeries.convolution_def, PowerSeries.coeff_mul]
  simp only [PowerSeries.coeff_mk]
  rw [Nat.sum_divisorsAntidiagonal (fun x y => f x * g y), Nat.sum_divisors_prime_pow hp,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun i j => f (p ^ i) * g (p ^ j))]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [Nat.pow_div (Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)) hp.pos]

private theorem sq_series (N : ℕ) {p : ℕ} (hp : p.Prime) (h : ¬ p ∣ N) :
    (1 - PowerSeries.X ^ 2) * (PowerSeries.mk fun i => sqN N (p ^ i)) = (1 : PowerSeries ℂ) := by
  have hc : p.Coprime N := (Nat.Prime.coprime_iff_not_dvd hp).2 h
  have hs : ∀ j, sqN N (p ^ j) = if Even j then 1 else 0 := by
    intro j
    rw [sqN_eq]
    refine if_congr ?_ rfl rfl
    rw [isSquare_pow_iff hp]
    exact ⟨fun x => x.1, fun x => ⟨x, Nat.Coprime.pow_left j hc⟩⟩
  ext k
  rw [sub_mul, one_mul, map_sub, PowerSeries.coeff_X_pow_mul', PowerSeries.coeff_one]
  simp only [PowerSeries.coeff_mk, hs]
  rcases k with _ | _ | k
  · simp
  · simp
  · have e : Even (k + 1 + 1) ↔ Even k := by
      rw [Nat.even_add_one, Nat.even_add_one, not_not]
    have e2 : k + 1 + 1 - 2 = k := by omega
    rw [if_pos (show 2 ≤ k + 1 + 1 by omega), e2, if_neg (show ¬ (k + 1 + 1 = 0) by omega)]
    simp only [e, sub_self]

private theorem isMul_of (f : ℕ → ℂ) (h1 : f 1 = 1)
    (h : ∀ m n, 0 < m → 0 < n → m.Coprime n → f (m * n) = f m * f n) :
    (toArithmeticFunction f).IsMultiplicative := by
  have key : ∀ n, toArithmeticFunction f n = if n = 0 then 0 else f n := fun _ => rfl
  refine ⟨by rw [key, if_neg one_ne_zero, h1], ?_⟩
  intro m n hmn
  rw [key, key, key]
  by_cases hm : m = 0
  · simp [hm]
  by_cases hn : n = 0
  · simp [hn]
  rw [if_neg hm, if_neg hn, if_neg (mul_ne_zero hm hn),
    h m n (Nat.pos_of_ne_zero hm) (Nat.pos_of_ne_zero hn) hmn]

theorem UpperTheory.eq_convolution_squareIndicator_of_euler_factors :
    ∀ (N : ℕ) (a b : ℕ → ℂ), 0 < N → a 1 = 1 → (∀ m n, m.Coprime n → a (m * n) = a m * a n) →
          (∀ p k : ℕ, p.Prime → p ∣ N → a (p ^ (k + 1)) = 0) → b 1 = 1 →
          (∀ m n, 0 < m → 0 < n → m.Coprime n → b (m * n) = b m * b n) → (∀ n, ¬ n.Coprime N → b n = 0) →
          (∀ p : ℕ, p.Prime → ¬ p ∣ N → (PowerSeries.mk fun k => a (p ^ k)) * (1 - PowerSeries.X ^ 2) = PowerSeries.mk fun k => b (p ^ k)) →
          ∀ n, n ≠ 0 → a n = LSeries.convolution b (sqN N) n := by
  intro N a b _ ha1 ham hap hb1 hbm hb0 hps n hn
  have hA := isMul_of a ha1 (fun m n _ _ h => ham m n h)
  have hB := isMul_of b hb1 hbm
  have hS := isMul_of (sqN N) (sqN_one N) (fun m n _ _ h => sqN_mul N h)
  have hE : toArithmeticFunction a = toArithmeticFunction b * toArithmeticFunction (sqN N) := by
    rw [ArithmeticFunction.IsMultiplicative.eq_iff_eq_on_prime_powers _ hA _ (hB.mul hS)]
    intro p i hp
    have e1 : toArithmeticFunction a (p ^ i) = a (p ^ i) := if_neg (pow_ne_zero i hp.ne_zero)
    rw [e1]
    change a (p ^ i) = LSeries.convolution b (sqN N) (p ^ i)
    rw [conv_pow _ _ hp]
    by_cases hd : p ∣ N
    · have hnc : ∀ j, ¬ (p ^ (j + 1)).Coprime N := fun j hc =>
        (Nat.Prime.coprime_iff_not_dvd hp).1
          (Nat.Coprime.coprime_dvd_left (dvd_pow_self p (Nat.succ_ne_zero j)) hc) hd
      have eb : (PowerSeries.mk fun i => b (p ^ i)) = 1 := by
        ext j
        rcases j with _ | j
        · simp [hb1]
        · rw [PowerSeries.coeff_mk, hb0 _ (hnc j), PowerSeries.coeff_one,
            if_neg (Nat.succ_ne_zero j)]
      rw [eb, one_mul, PowerSeries.coeff_mk]
      rcases i with _ | i
      · rw [pow_zero, ha1, sqN_one]
      · rw [hap p i hp hd, sqN_eq, if_neg (fun x => hnc i x.2)]
    · rw [← hps p hp hd, mul_assoc, sq_series N hp hd, mul_one, PowerSeries.coeff_mk]
  have e1 : toArithmeticFunction a n = a n := if_neg hn
  rw [← e1, hE]
  rfl
end

-- bundled from Development.AutomorphicArithmetic.WhittakerHecke.ExistsBoundCuspFormOfUnitaryCentralCharacter
section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.RankTwoDescent UpperTheory.ConvolutionTheory.RankTwoDescent.TA
open UpperTheory.ConvolutionTheory.R2.G (FS2 nE)
open scoped Classical

open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction in
theorem UpperTheory.exists_bound_cuspForm_of_unitary_centralCharacter :
    ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (P : CuspSub E 2) (ω : HChar ℚ), CenN P ω → Unit1 ω →
        ∀ f ∈ P.V, ∃ B : ℝ, ∀ g, ‖f.1 g‖ ≤ B := by
  intro E _ _ _ P ω hc hu f hf
  obtain ⟨φ, rfl⟩ := UpperTheory.V.Cm.mem_range_ofCusp.2 (P.cusp f hf)
  obtain ⟨B₀, hB₀⟩ := CuspidalSpectrum.exists_norm_le_of_mem_cuspForms φ.2
  refine ⟨B₀, fun g => ?_⟩
  let u : (A E)ˣ := posIdeleHom E (rpowHom ((((2 : ℕ) : ℝ) * Module.finrank ℚ E))⁻¹ (detModule E 2 g))
  have e : Matrix.GeneralLinearGroup.scalar (Fin 2) u = centralSection E 2 (detModule E 2 g) := Units.ext rfl
  have h2 : (centralSection E 2 (detModule E 2 g))⁻¹ * g ∈ normOneGL E 2 := by
    rw [mem_normOneGL_iff_detModule, map_mul, map_inv, detModule_centralSection two_pos, inv_mul_cancel]
  have h3 := hc _ hf u ((centralSection E 2 (detModule E 2 g))⁻¹ * g)
  rw [e, mul_inv_cancel_left] at h3
  rw [show (UpperTheory.V.Cm.ofCusp E 2 φ).1 g = _ from h3, norm_mul, hu, one_mul]
  exact hB₀ _ h2
end

-- bundled from Development.AutomorphicArithmetic.WhittakerHecke.ExistsGoodCharacterOfInertCMDatum
section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.RankTwoDescent
open scoped Classical
open UpperTheory.ConvolutionTheory.R2.G (FS2 Rw nE row)
open UpperTheory.V.Af.Smo (EigAt)
open scoped ComplexOrder

theorem UpperTheory.exists_good_character_of_inert_CMDatum :
    ∀ (E : Type) [Field E] [NumberField E] (D : Dat ℚ E) (v : H.P ℚ) (w : H.P E), H.Gd D.δ v → H.Inert D v w →
          ∃ χ : H.Kv w → ℂ, H.Good χ ∧ ∀ x, ∃ u t, H.sg w x = D.mkE u t ∧ ψ (-t) = χ x := by
  intro E _ _ D v w hG hI
  obtain ⟨e, h1, h2, h3, -⟩ := hI.coord
  obtain ⟨sa, sm, sc, -⟩ := H.sgLaws ℚ v
  obtain ⟨-, tm, tc, -⟩ := H.sgLaws E w
  obtain ⟨ga, gi, gm⟩ := hG.psi
  have hs : ∀ u, -(H.sg v u) = H.sg v (-u) := fun u => by
    rw [← neg_one_mul, sm, map_neg, map_one, neg_one_mul]
  have s0 : H.sg v (0 : H.Kv v) = 0 := by simpa using (sm 0 0).symm
  have h4 : ∀ c u t, e (0, c) * e (u, t) = e (H.cp v (rt D.δ) * (c * t), c * u) := fun c u t => by
    have a1 : ∀ x y, H.sg v (x * y) = H.sg v x * H.sg v y := fun x y => by rw [sm, sc]
    have a2 : ∀ x, H.sg v (H.cp v (rt D.δ) * x) = rt D.δ * H.sg v x := fun x => (sm (rt D.δ) x).symm
    have a3 : (rt D.θ : A E) ^ 2 = AdeleBaseChange.adeleMap ℚ E (rt D.δ) := by
      rw [← map_pow, D.sq]
      exact (AdeleBaseChange.adeleMap_algebraMap _).symm
    have : H.sg w (e (0, c) * e (u, t)) = H.sg w (e (H.cp v (rt D.δ) * (c * t), c * u)) := by
      rw [← tc (e (0, c)), ← tm, h1, h1, h1, s0, a2, a1, a1]
      simp only [Dat.mkE, map_mul, map_zero, ← a3]
      ring
    simpa only [tc] using congrArg (H.cp w) this
  have key : ∀ y : H.Kv v, (∀ c, H.IsInt c → ψ (H.sg v (-(c * y))) = 1) → H.IsInt y := fun y hy => by
    have : Valued.v (-y) ≤ 1 := gm _ fun c hc => by
      have := hy c hc
      rwa [show -(c * y) = c * -y by ring] at this
    rwa [Valuation.map_neg] at this
  refine ⟨fun x => ψ (H.sg v (-(e.symm x).2)), ⟨fun x y => ?_, fun x hx => ?_, fun x hx => ?_⟩, fun x => ?_⟩
  · beta_reduce
    rw [map_add, Prod.snd_add, neg_add]
    exact ga _ _
  · obtain ⟨⟨u, t⟩, rfl⟩ := e.surjective x
    have ht : Valued.v t ≤ 1 := (le_max_right _ _).trans ((h2 u t).symm.le.trans hx)
    beta_reduce
    rw [e.symm_apply_apply]
    refine gi _ ?_
    show Valued.v _ ≤ 1
    rwa [Valuation.map_neg]
  · obtain ⟨⟨u, t⟩, rfl⟩ := e.surjective x
    have ht : H.IsInt t := key t fun c hc => by
      have := hx (e (c, 0)) ((h2 c 0).le.trans (max_le hc (by simp)))
      beta_reduce at this
      rwa [h3, e.symm_apply_apply] at this
    have hu : H.IsInt u := key u fun c hc => by
      have := hx (e (0, c)) ((h2 0 c).le.trans (max_le (by simp) hc))
      beta_reduce at this
      rwa [h4, e.symm_apply_apply] at this
    exact (h2 u t).le.trans (max_le hu ht)
  · obtain ⟨⟨u, t⟩, rfl⟩ := e.surjective x
    exact ⟨_, _, h1 u t, by beta_reduce; rw [hs, e.symm_apply_apply]⟩
end

-- bundled from Development.AutomorphicArithmetic.WhittakerHecke.ExistsNatMulIntegralAtAllFinitePlaces
section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.RankTwoDescent UpperTheory.ConvolutionTheory.RankTwoDescent.Xg
open scoped Classical
open UpperTheory.ConvolutionTheory.R2.G (FS2 Rw nE row)
open UpperTheory.V.Af.Smo (EigAt)
open scoped ComplexOrder

theorem UpperTheory.exists_nat_mul_integral_at_all_finite_places :
    ∀ (E : Type) [Field E] [NumberField E] (θ : E), ∃ d : ℕ, 0 < d ∧ ∀ e : ℕ, d ∣ e → ∀ w : H.P E, Valued.v (H.cp w (rt ((e : E) * θ))) ≤ 1 := by
  intro E _ _ θ
  obtain ⟨y, hy0, hy⟩ := ((IsFractionRing.isAlgebraic_iff ℤ ℚ E).2 (Algebra.IsAlgebraic.isAlgebraic (R := ℚ) θ)).exists_integral_multiple
  have hy' : IsIntegral ℤ ((y : E) * θ) := by
    simpa [zsmul_eq_mul] using hy
  have h1 : IsIntegral ℤ ((y.natAbs : E) * θ) := by
    rcases Int.natAbs_eq y with h | h
    · have hc : ((y.natAbs : E)) = (y : E) := by
        conv_rhs => rw [h]
        simp
      rw [hc]
      exact hy'
    · have hc : ((y.natAbs : E)) = -(y : E) := by
        conv_rhs => rw [h]
        simp
      rw [hc, neg_mul]
      exact hy'.neg
  refine ⟨y.natAbs, Int.natAbs_pos.2 hy0, ?_⟩
  rintro e ⟨k, rfl⟩ w
  have hint : IsIntegral ℤ (((y.natAbs * k : ℕ) : E) * θ) := by
    have he : (((y.natAbs * k : ℕ) : E) * θ) = (k : E) * ((y.natAbs : E) * θ) := by
      push_cast
      ring
    rw [he]
    have hk : IsIntegral ℤ (k : E) := by
      simpa using isIntegral_algebraMap (R := ℤ) (A := E) (x := (k : ℤ))
    exact hk.mul h1
  have hm := coe_algebraMap_mem_adicCompletionIntegers w (⟨_, hint⟩ : 𝓞 E)
  exact (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mp hm
end

