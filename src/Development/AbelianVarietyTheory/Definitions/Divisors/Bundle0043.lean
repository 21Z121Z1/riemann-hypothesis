import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0042
import Development.AbelianVarietyTheory.Definitions.Divisors.FirstChernLeviEqConstant
import Development.AbelianVarietyTheory.Definitions.Divisors.PointsNonemptyUnitaryRankOne
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0047
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.UniformisationComponentLatticesMarkings
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0043
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0045
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0021
import Development.AbelianVarietyTheory.Definitions.Divisors.SimpleTwistedTraceFormulaStable

-- bundled from Development.AbelianVarietyTheory.Definitions.Divisors.CharZeroFunctionField
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.CxPts GlobalTheory.Cartier

namespace GlobalTheory.VolBr

structure IsBallFam {G : Type} [AddCommGroup G] (Λ : AddSubgroup G) (B : ℝ → Set G) : Prop where

  subset : ∀ r, B r ⊆ Λ

  zero_mem : ∀ r, 0 ≤ r → (0 : G) ∈ B r

  sub_mem : ∀ r r' x y, x ∈ B r → y ∈ B r' → x - y ∈ B (r + r')

  nsmul_iff : ∀ (n : ℕ) (r : ℝ) (x : G), 0 < n → x ∈ Λ → (n • x ∈ B (n * r) ↔ x ∈ B r)

theorem isBallFam_int : IsBallFam (⊤ : AddSubgroup ℤ) fun r => {x | |(x : ℝ)| ≤ r} where
  subset _ _ _ := AddSubgroup.mem_top _
  zero_mem r hr := by simpa using hr
  sub_mem r r' x y hx hy := by
    simp only [Set.mem_setOf_eq, Int.cast_sub] at hx hy ⊢
    exact (abs_sub _ _).trans (add_le_add hx hy)
  nsmul_iff n r x hn _ := by
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    simp only [Set.mem_setOf_eq, nsmul_eq_mul, Int.cast_mul, Int.cast_natCast, abs_mul, Nat.abs_cast]
    exact ⟨fun h => le_of_mul_le_mul_left h hn', fun h => mul_le_mul_of_nonneg_left h hn'.le⟩

variable {k : Type} [CommRing k] {X : Scheme.{0}} [IsIntegral X] {p : X ⟶ Sp k}

structure Pair (p : X ⟶ Sp k) where

  L : HermLB p

  A : HermLB p

  r : L.B.ι → X.functionFieldˣ

  r' : A.B.ι → X.functionFieldˣ

  hr : IsRatSec L.B r

  hr' : IsRatSec A.B r'

theorem exists_pair (L A : HermLB p) : ∃ P : Pair p, P.L = L ∧ P.A = A := by
  obtain ⟨r, hr⟩ := exists_isRatSec L.isLB
  obtain ⟨r', hr'⟩ := exists_isRatSec A.isLB
  exact ⟨⟨L, A, r, r', hr, hr'⟩, rfl, rfl⟩

namespace Pair

variable (P : Pair p)

def loc (a b : ℤ) (f : X.functionField) (i : P.L.B.ι) (j : P.A.B.ι) : X.functionField :=
  f * (P.r i : X.functionField) ^ a * (P.r' j : X.functionField) ^ b

def H (a b : ℤ) : AddSubgroup X.functionField where
  carrier := {f | ∀ (x : X) i j, x ∈ P.L.B.U i → x ∈ P.A.B.U j → RegAt x (P.loc a b f i j)}
  zero_mem' x i j _ _ := ⟨0, by simp [loc]⟩
  add_mem' {f g} hf hg x i j hi hj := by
    obtain ⟨u, hu⟩ := hf x i j hi hj
    obtain ⟨v, hv⟩ := hg x i j hi hj
    exact ⟨u + v, by rw [map_add, hu, hv]; simp only [loc]; ring⟩
  neg_mem' {f} hf x i j hi hj := by
    obtain ⟨u, hu⟩ := hf x i j hi hj
    exact ⟨-u, by rw [map_neg, hu]; simp only [loc]; ring⟩

def nu (a b : ℤ) (σ : k →+* ℂ) (y : CxPts p σ) (f : X.functionField) : ℝ :=
  ‖ratVal (P.loc a b f (pick (P.L.φ σ).isLB y) (pick (P.A.φ σ).isLB y)) y‖ *
    Real.exp (-(a * (P.L.φ σ).φ (pick (P.L.φ σ).isLB y) y + b * (P.A.φ σ).φ (pick (P.A.φ σ).isLB y) y) / 2)

def Bl (a b : ℤ) (R : ℝ) : Set X.functionField :=
  {f | f ∈ P.H a b ∧ ∀ (σ : k →+* ℂ) (y : CxPts p σ), P.nu a b σ y f ≤ R}

def lc (a b : ℤ) (R : ℝ) : ℝ := Real.log ((P.Bl a b R).ncard : ℝ)

def Rep (a b : ℤ) (M : HermLB p) : Prop :=
  ∃ ρ : M.B.ι → X.functionFieldˣ, IsRatSec M.B ρ ∧
    (∀ (x : X) c i j, x ∈ M.B.U c → x ∈ P.L.B.U i → x ∈ P.A.B.U j →
      UnitAt x ((ρ c : X.functionField) / P.loc a b 1 i j)) ∧
    ∀ (σ : k →+* ℂ) (y : CxPts p σ) c i j, y ∈ ptsIn p σ (M.B.U c) → y ∈ ptsIn p σ (P.L.B.U i) →
      y ∈ ptsIn p σ (P.A.B.U j) →
      Real.log ‖ratVal ((ρ c : X.functionField) / P.loc a b 1 i j) y‖ - (M.φ σ).φ c y / 2 =
        -(a * (P.L.φ σ).φ i y + b * (P.A.φ σ).φ j y) / 2

structure Good (D : ℕ) (b : ℕ) (s t : X.functionField) : Prop where

  ample : IsAmpleLB P.A.B

  nef : P.A.IsNef D

  pos : 0 < b

  s_mem : s ∈ P.Bl 0 1 1

  s_ne : s ≠ 0

  t_mem : t ∈ P.Bl (-1) b 1

  t_ne : t ≠ 0

  reg : ∀ (x : X) i j, x ∈ P.L.B.U i → x ∈ P.A.B.U j → ∀ g : X.functionField, RegAt x g →
    RegAt x (g * P.loc (-1) b t i j / P.loc 0 1 s i j) → RegAt x (g / P.loc 0 1 s i j)

end Pair

namespace IntExample

open GlobalTheory.Points GlobalTheory.CechPic

theorem ratVal_nat {σ : k →+* ℂ} (y : CxPts p σ) (n : ℕ) : ratVal (n : X.functionField) y = n := by
  have h : genericPoint X ∈ (⊤ : X.Opens) := trivial
  have e : (n : X.functionField) = fnOf ⊤ h (n : Γ(X, ⊤)) := (map_natCast _ n).symm
  rw [e, ratVal_fnOf mem_ptsIn_top h, ev_eq mem_ptsIn_top, map_natCast]

theorem isRatSec_one : IsRatSec (LB.triv X) fun _ => 1 := by
  intro i j h
  simp [LB.triv]

def pair : Pair (𝟙 (Sp ℤ)) :=
  ⟨ArithBase.trivShift 0, ArithBase.trivShift (Real.log 3), fun _ => 1, fun _ => 1, isRatSec_one, isRatSec_one⟩

theorem isNef_trivShift (t : ℝ) (ht : 0 ≤ t) : (ArithBase.trivShift t).IsNef 0 := by
  classical
  refine (HermLB.IsArithHeight.isNef_iff ArithBase.isArithVar_int
    (ArithBase.isArithHeight_trivShift t)).2 ⟨?_, ?_⟩
  · exact (HermLB.isNef_triv (𝟙 (Sp ℤ)) 0).semiPos.shift (fun _ => t) (fun _ => rfl)
  · intro Z i _ _ _
    dsimp only
    split_ifs
    · exact ht
    · exact Real.log_natCast_nonneg _

theorem loc_eq (a b : ℤ) (f) (i j) : pair.loc a b f i j = f := by
  show f * (((1 : (Sp ℤ).functionFieldˣ)) : (Sp ℤ).functionField) ^ a *
    (((1 : (Sp ℤ).functionFieldˣ)) : (Sp ℤ).functionField) ^ b = f
  simp

private theorem pair_L_phi_apply_eq_zero (σ : ℤ →+* ℂ) (i) (y : CxPts (𝟙 (Sp ℤ)) σ) :
    (pair.L.φ σ).φ i y = 0 + 2 * 0 := rfl

private theorem pair_A_phi_apply_eq_two_log_three (σ : ℤ →+* ℂ) (i) (y : CxPts (𝟙 (Sp ℤ)) σ) :
    (pair.A.φ σ).φ i y = 0 + 2 * Real.log 3 := rfl

theorem nu_nat (a b : ℤ) (σ) (y) (n : ℕ) : pair.nu a b σ y n = n * Real.exp (-(b * Real.log 3)) := by
  simp only [Pair.nu, loc_eq, ratVal_nat, Complex.norm_natCast, pair_L_phi_apply_eq_zero, pair_A_phi_apply_eq_two_log_three]
  congr 2
  ring

theorem regAt_nat (x : Sp ℤ) (n : ℕ) : RegAt x (n : (Sp ℤ).functionField) :=
  ⟨n, map_natCast _ n⟩

theorem charZero_functionField : CharZero (Sp ℤ).functionField := by
  have h : genericPoint (Sp ℤ) ∈ (⊤ : (Sp ℤ).Opens) := trivial
  let f : ℤ →+* (Sp ℤ).functionField :=
    (fnOf ⊤ h).comp (Scheme.ΓSpecIso (CommRingCat.of ℤ)).inv.hom
  have hf : Function.Injective f := by
    intro a b hab
    have h1 := fnOf_injective ⊤ h hab
    simpa using congrArg (Scheme.ΓSpecIso (CommRingCat.of ℤ)).hom.hom h1
  exact charZero_of_injective_ringHom hf

private theorem nonempty_cxPts_spec_int : Nonempty (CxPts (𝟙 (Sp ℤ)) (Int.castRingHom ℂ)) :=
  ⟨CxPts.ofHom (p := 𝟙 (Sp ℤ)) (U := ⊤) (isAffineOpen_top (Sp ℤ))
    ((Int.castRingHom ℂ).comp (Scheme.ΓSpecIso (CommRingCat.of ℤ)).hom.hom)
    (fun a => by simp only [eq_intCast, map_intCast])⟩

theorem nat_mem_Bl_iff (a : ℤ) (n : ℕ) : (n : (Sp ℤ).functionField) ∈ pair.Bl a 1 1 ↔ n ≤ 3 := by
  have key : ∀ σ y, pair.nu a 1 σ y n = n / 3 := by
    intro σ y
    rw [nu_nat, Int.cast_one, one_mul, Real.exp_neg, Real.exp_log (by norm_num), div_eq_mul_inv]
  have hH : (n : (Sp ℤ).functionField) ∈ pair.H a 1 := fun x i j _ _ => by
    rw [loc_eq]
    exact regAt_nat x n
  constructor
  · rintro ⟨-, h⟩
    obtain ⟨y⟩ := nonempty_cxPts_spec_int
    have h1 := h (Int.castRingHom ℂ) y
    rw [key, div_le_one (by norm_num)] at h1
    exact_mod_cast h1
  · intro hn
    refine ⟨hH, fun σ y => ?_⟩
    rw [key, div_le_one (by norm_num)]
    exact_mod_cast hn

theorem good : pair.Good 0 1 (2 : ℕ) (3 : ℕ) where
  ample :=
    { isLB := LB.isLB_triv _
      compactSpace := inferInstance
      exists_affine := fun x => by
        refine ⟨1, le_rfl, powSecMk (L := LB.triv (Sp ℤ)) 1 (fun _ => 1) (fun i j => by simp [LB.triv]),
          ?_, isAffineOpen_nonzeroLocus (isLB_lbPow (LB.isLB_triv _) 1) _⟩
        erw [nonzeroLocus_powSecMk]
        simp [LB.triv, Scheme.basicOpen_of_isUnit] }
  nef := isNef_trivShift _ (Real.log_nonneg (by norm_num))
  pos := one_pos
  s_mem := (nat_mem_Bl_iff 0 2).2 (by norm_num)
  s_ne := by
    haveI := charZero_functionField
    exact Nat.cast_ne_zero.2 two_ne_zero
  t_mem := (nat_mem_Bl_iff (-1) 3).2 le_rfl
  t_ne := by
    haveI := charZero_functionField
    exact Nat.cast_ne_zero.2 (by norm_num)
  reg := by
    intro x i j _ _ g hg h
    haveI := charZero_functionField
    simp only [loc_eq] at h ⊢
    obtain ⟨u, hu⟩ := h
    obtain ⟨v, hv⟩ := hg
    refine ⟨u - v, ?_⟩
    rw [map_sub, hu, hv]
    push_cast
    ring

theorem not_good : ¬ pair.Good 0 1 (2 : ℕ) (4 : ℕ) := fun h => by
  have h1 := (nat_mem_Bl_iff (-1) 4).1 h.t_mem
  omega

private theorem trivShift_phi_apply_eq_two_mul (t : ℝ) (σ : ℤ →+* ℂ) (c) (y : CxPts (𝟙 (Sp ℤ)) σ) :
    ((ArithBase.trivShift t).φ σ).φ c y = 0 + 2 * t := rfl

theorem rep (a b : ℤ) : pair.Rep a b (ArithBase.trivShift (b * Real.log 3)) := by
  refine ⟨fun _ => 1, isRatSec_one, fun x c i j _ _ _ => ?_, fun σ y c i j _ _ _ => ?_⟩
  · rw [loc_eq]
    simpa using unitAt_one x
  · rw [loc_eq, trivShift_phi_apply_eq_two_mul, pair_L_phi_apply_eq_zero, pair_A_phi_apply_eq_two_log_three]
    have h1 : ratVal (((1 : (Sp ℤ).functionFieldˣ) : (Sp ℤ).functionField) / 1) y = 1 := by
      rw [Units.val_one, div_one, ← Nat.cast_one, ratVal_nat, Nat.cast_one]
    rw [h1, norm_one, Real.log_one]
    ring

end IntExample

end GlobalTheory.VolBr
end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.Divisors.ChernOn
section
open MvPolynomial Formalism.DegreeFormula Formalism.BasicNotions Formalism.BasicNotions.DV Formalism.MainNotions Formalism.MainNotions.WeightThresholdDefs Filter Topology Classical
open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M GlobalTheory.FlagPoly GlobalTheory.FlagAr GlobalTheory.Mean4

noncomputable section

namespace GlobalTheory.Mean4O

section Model

open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ArInt

variable {e : ℕ} {M : Man e} {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k}

def Man.pull (M : Man e) (ε : (k →+* ℂ) → Fin (M.n + 1)) (π : ∀ σ, CxPts p σ → M.X (ε σ)) (u : M.Fun) :
    ∀ σ : k →+* ℂ, CxPts p σ → ℝ := fun σ z => u (ε σ) (π σ z)

variable (K : Calc M) (ε : (k →+* ℂ) → Fin (M.n + 1)) (π : ∀ σ, CxPts p σ → M.X (ε σ)) (ν : ℝ)
  {ι : Type} [Fintype ι] (L : ι → HermLB p) (v : ι → K.V)

def Calc.ChernOn : Prop := ∀ u, M.Smooth u → ∀ hu hc (n : Option ι → ℤ) (f : M.Fun), M.Smooth f →
  chInt (ArInt.comb (fun o : Option ι => o.elim (fnB (M.pull ε π ((2 : ℝ) • u)) hu hc) L) n) e (M.pull ε π f) =
    ν * M.int (fun _ => K.c1 (∑ i, (n (some i) : ℝ) • v i + (n none : ℝ) • K.ar u)) f

def Calc.NumOn [IsIntegral X] : Prop := ∀ u, M.Smooth u → ∀ hu hc (Φ : MvPolynomial (Option ι) ℝ →ₗ[ℝ] ℝ),
  IsArFun (fun o : Option ι => o.elim (fnB (M.pull ε π ((2 : ℝ) • u)) hu hc) L) e Φ → ∀ a : Option ι → ℝ,
    Φ (lin a ^ (e + 1)) = ν * K.top (∑ i, a (some i) • v i + a none • K.ar u)

def Calc.Reads [IsIntegral X] : Prop :=
  IsArithVar p e ∧ 0 < ν ∧ (∀ σ, Continuous (π σ) ∧ Function.Surjective (π σ)) ∧ Function.Surjective ε ∧
  (∀ u, M.Smooth u → ∀ σ z, CxPts.CInfAt (M.pull ε π u σ) z) ∧ K.ChernOn ε π ν L v ∧ K.NumOn ε π ν L v

omit [Fintype ι] in

example : (∀ σ z, CxPts.CInfAt (M.pull ε π ((2 : ℝ) • 0) σ) z) ∧ ∀ σ σ',
    (Weight.ofFun (M.pull ε π ((2 : ℝ) • 0) σ)).IsConj (Weight.ofFun (M.pull ε π ((2 : ℝ) • 0) σ')) := by
  rw [smul_zero]
  exact ⟨fun _ z => CxPts.cInfAt_const 0 z, fun _ _ _ _ _ _ _ => rfl⟩

end Model

variable {D : D7} {Y : ShimX D.what₂.Tau} {T : Real0 Y} (P : T.Pts)

open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ArInt in

def Real0.Pts.OnModel : Prop := ∀ B : ℝ, 2 ≤ B → ∀ c, ∃ (k : Type) (_ : CommRing k) (X : Scheme.{0}) (_ : IsIntegral X)
    (p : X ⟶ Sp k) (ε : (k →+* ℂ) → Fin ((T.M c).n + 1)) (π : ∀ σ, CxPts p σ → (T.M c).X (ε σ)) (ν : ℝ) (m : ℕ)
    (L : Option (D.what₂.Tau × Fin Y.N) → HermLB p) (q : X → Y.Pt → Prop),
  0 < m ∧ (T.K B c).Reads ε π ν L (T.gen B c m) ∧ (∀ x, IsAlgPt x → ∃ y, q x y) ∧ (∀ y, Y.compPt y = c → ∃ x, q x y) ∧
  ∀ x y, q x y → IsAlgPt x ∧ Y.compPt y = c ∧
    (∀ g, P.mean c y g * Nat.card (X.residueField x →+* ℂ) =
      ∑ᶠ σ, ∑ᶠ z ∈ {z : CxPts p σ | z.1 (IsLocalRing.closedPoint ℂ) = x}, (T.M c).pull ε π g σ z) ∧
    ∀ n : Option (D.what₂.Tau × Fin Y.N) → ℤ,
      IsPtHt (ArInt.comb L n) x (P.ht B c y (∑ o, (n o : ℝ) • T.gen B c m o))

end GlobalTheory.Mean4O
end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.Divisors.CxTotalEqFullSumIrrOfCxCountReg
section
noncomputable section

open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount
open scoped TensorProduct Classical

namespace GlobalTheory.LKCx

variable {p : ℕ} [Fact p.Prime]

def CxCountReg : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p), G.a = 1 → ∀ v : InfinitePlace G.F, sigPosH (G.gram_herm v) = 1 →
    ∀ (wt : Polynomial G.F → ℂ) (L : G.Level) (f : G.GAf → ℂ), IsTest (MonoidHom.id _) L.K.toSubgroup L.K.toSubgroup f →
    (∀ g, f g ≠ 0 → RegAf G g) →
    ∀ (K' : Subgroup (Gr G 1)) (f' : Gr G 1 → ℂ), IsTest (sigG G 1) (KHT p G.m G.n 1 G.Fw) K' f' →
      cxTotal G v wt L.K.toSubgroup f K' f' = fullSum G wt L.K.toSubgroup f 1 K' f'

theorem fullSum_eq_fullSumIrr_of_term_zero (G : HTGroup p) (wt : Polynomial G.F → ℂ) (Kf : Subgroup G.GAf)
    (f : G.GAf → ℂ) (r : ℕ) (K : Subgroup (Gr G r)) (φ : Gr G r → ℂ)
    (h : ∀ P : Pair G, (∃ μ, P.Mark μ) → ¬ Irreducible P.pol → wt P.pol * P.term Kf f r K φ = 0) :
    fullSum G wt Kf f r K φ = fullSumIrr G wt Kf f r K φ := by
  unfold fullSum fullSumIrr
  refine finsum_congr fun q => ?_
  by_cases hm : ∃ μ, (Quot.out q).Mark μ
  · by_cases hi : Irreducible (Quot.out q).pol
    · rw [if_pos hm, if_pos ⟨hi, hm⟩]
    · rw [if_pos hm, if_neg (fun h' => hi h'.1)]
      exact h _ hm hi
  · rw [if_neg hm, if_neg (fun h' => hm h'.2)]

example (G : HTGroup p) (v wt Kf K' f') :
    cxTotal G v wt Kf (fun _ => 0) K' f' = fullSum G wt Kf (fun _ => 0) 1 K' f' := by
  simp [cxTotal, cxSum, cxSumAt, fullSum, Pair.term, Pair.termAt, pointSum]

example (G : HTGroup p) (Kf : Subgroup G.GAf) (f : G.GAf → ℂ) (K' : Subgroup (Gr G 1)) (f' : Gr G 1 → ℂ) :
    fullSum G (fun _ => 0) Kf f 1 K' f' = fullSumIrr G (fun _ => 0) Kf f 1 K' f' :=
  fullSum_eq_fullSumIrr_of_term_zero G _ Kf f 1 K' f' fun _ _ _ => zero_mul _

end GlobalTheory.LKCx
end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.Divisors.ExistsGenReads
section
open NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.L2.Pj
open scoped TensorProduct Classical

namespace GlobalTheory.AdTh.CcModel

noncomputable section

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

theorem realM_mt {θ : InfFam D} (hθ : IsInfFam θ) (W : HSp D) (h : GA D W) (τ : D.host.E →+* ℂ)
    (hτ : ∃ ρ, τ = tauE D ρ) (th : Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ) (hth : IsInfEmb τ th) :
    realM θ (Formalism.L2.Theta.mt W h) τ = archM W th h := by
  have e : θ hτ.choose = th :=
    GlobalTheory.SmoothForms.RealPts.infEmb_unique τ _ _ (by have := hθ hτ.choose; rwa [← hτ.choose_spec] at this) hth
  rw [realM, dif_pos hτ, compAt, e]
  rfl

theorem exists_atComp {θ : InfFam D} (hθ : IsInfFam θ) {W : HSp D} {r : ℕ} (hr : W.rank = r)
    {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E} {Dw : Datum H} {l : Geo.Tor.Level H} {Xo : Moduli Dw l} {c : Coeff l}
    {σ : c.F →+* ℂ} (U : Unf Xo c σ r) (dict : GA D W → Σ k, Frame (U.X k).Ψ r)
    (ι : Dw.La →ₗ[𝓞 D.host.E] (Fin W.rank → D.host.E)) {g : ℕ} (e : Fin g ≃ Σ τ : D.host.E →+* ℂ, Fin (Dw.mult τ))
    (F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (fun j => relab c σ (e j).1))
    (ik : U.Comp → Fin F.n) (φ : ∀ k, (F.Di (ik k)).La ≃ₗ[𝓞 D.host.E] (U.X k).Λ)
    (th : ∀ k, (U.X k).Ψ → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ))
    (x₀ : (D.host.E →+* ℂ) → Matrix (Fin r) (Fin r) ℂ) (hΨ : ∀ k, ∀ τ ∈ (U.X k).Ψ, ∃ ρ, τ = tauE D ρ)
    (hth : ∀ k τ, IsInfEmb τ.1 (th k τ)) (hD : DictLat U W hr dict ι e F ik φ th x₀) (h : GA D W) :
    ∃ γ, AtComp θ W hr U.X dict x₀ h γ := by
  obtain ⟨γ, hγ, h1, -, h3⟩ := hD.2 h
  refine ⟨γ, hγ, ?_, ?_⟩
  · apply SetLike.coe_injective
    rw [h1, latR, Submodule.map_coe]
    rfl
  · funext τ
    have := h3 τ
    rw [← realM_mt hθ W (γ * h) τ.1 (hΨ _ _ τ.2) _ (hth _ τ)] at this
    exact this

theorem exists_genReads {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    {Dw : Datum H} {l : Geo.Tor.Level H} {Xo : Moduli Dw l} {c : Coeff l} {σ : c.F →+* ℂ} {r : ℕ} (U : Unf Xo c σ r)
    (hσ : GoodEmb c σ) (hU : IsUnf U) (h1 : 1 ≤ r) (k : U.Comp) (x : (U.X k).dom) (hx : IsUnitFr (U.X k) x.1) :
    ∃ (g : ℕ) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] (U.X k).Λ) (idx : Fin g ≃ (U.X k).Ψ × Fin r) (e : Fin g ≃ Lt1 Dw)
      (ϑ : (Fin g → ℂ) → ℂ), IsSympl (U.X k) bas ∧ IdxIs c σ (U.X k) idx e ∧ GenReads U k bas idx e x ϑ ∧
        MeanOne (U.X k) bas idx x.1 (U.X k).Λ ϑ := by
  have hU' : Formalism.L2.PjFree.IsUnf (Formalism.L2.PjFree.Unf.ofPj U) := hU
  obtain ⟨Wt⟩ := nonempty_uw hU'
  have huw := GlobalTheory.Dict.uw_lattice E H Dw l Xo c σ _ _ hσ hU' h1 Wt k
  have hdom : Formalism.L2.Pj.Dom (fun _ : (E →+* ℂ) × ℕ => 0) 0 := ⟨fun _ => antitone_const, by simp⟩
  obtain ⟨Dc, hDe, -⟩ := GlobalTheory.Dict.exists_dic E H Dw l c σ _ Wt.g 0 (U.X k) (fun _ => 0) Wt.e hσ hU.1
    (hU.2.1 k).1 (hU.2.1 k).2 huw.2.1 hdom
  have hper : ∀ x v j, pv (U.X k) Dc.idx x v j =
      Formalism.L2.PjFree.perFr (U.X k) x v (Formalism.L2.PjFree.relab c σ (Wt.e j).1) (Wt.e j).2 := fun x v j => by
    rw [Dc.per_eq, hDe]
  have hty : ∀ j, rowType (U.X k) (Dc.idx j) = Formalism.L2.PjFree.relab c σ (Wt.e j).1 := fun j => by
    rw [Dc.ty_eq, hDe]
  obtain ⟨A, -, ϑ, hA, hm⟩ := GlobalTheory.Dict.uw_anFib E H Dw l Xo c σ _ _ hσ hU' h1 Wt k Dc.bas Dc.idx Dc.sympl hper hty x hx
  exact ⟨Wt.g, Dc.bas, Dc.idx, Wt.e, ϑ, Dc.sympl, ⟨hper, hty⟩, ⟨A, hA⟩, hm⟩

variable {θ : InfFam D} {V W : HSp D} {r : ℕ} {hr : W.rank = r} {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E}
    {Dw : Datum H} {l : Geo.Tor.Level H} {Xo : Moduli Dw l} {c : Coeff l} {σ : c.F →+* ℂ} {U : Unf Xo c σ r}
    {dict : GA D W → Σ k, Frame (U.X k).Ψ r} {mu : GA D W → ℂ} {x₀ : (D.host.E →+* ℂ) → Matrix (Fin r) (Fin r) ℂ}
    {om : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)} {f₀ : WO V W → ℂ} {cc cc' : U.Comp → ℂ}

theorem ccIs_smul (h : CcIs θ V W hr U dict mu x₀ om f₀ cc) (a : ℂ) (ha : ‖a‖ = 1) :
    CcIs θ V W hr U dict mu x₀ om (a • f₀) (fun k => a * cc k) := by
  refine ⟨fun k => by rw [norm_mul, ha, h.1 k, mul_one], fun g γ hg hx' n bas idx e hs hi ϑ hϑ w hw => ?_⟩
  rw [map_smul, Pi.smul_apply, h.2 g γ hg hx' n bas idx e hs hi ϑ hϑ w hw, smul_eq_mul]
  ring

theorem ccIs_unique (hσ : GoodEmb c σ) (hU : IsUnf U) (h1 : 1 ≤ r) (h : CcIs θ V W hr U dict mu x₀ om f₀ cc)
    (h' : CcIs θ V W hr U dict mu x₀ om f₀ cc') (g γ : GA D W) (hg : AtComp θ W hr U.X dict x₀ g γ)
    (hd : (dict g).2 ∈ (U.X (dict g).1).dom) (hu : IsUnitFr (U.X (dict g).1) (dict g).2) (w : WO V W)
    (hw : w.map (finPart D) = 0) (hne : om (1, γ * g) f₀ w ≠ 0) : cc (dict g).1 = cc' (dict g).1 := by
  obtain ⟨n, bas, idx, e, ϑ, hs, hi, hϑ, -⟩ := exists_genReads U hσ hU h1 (dict g).1 ⟨_, hd⟩ hu
  have e1 := h.2 g γ hg hd n bas idx e hs hi ϑ hϑ w hw
  have e2 := h'.2 g γ hg hd n bas idx e hs hi ϑ hϑ w hw
  rw [mul_assoc, mul_assoc] at e1 e2
  have hB := right_ne_zero_of_mul (e1 ▸ hne)
  exact mul_right_cancel₀ hB (e1.symm.trans e2)

end

end GlobalTheory.AdTh.CcModel
end

-- bundled from Development.AbelianVarietyTheory.Definitions.Divisors.IntersectionFamilySymmetric
section
noncomputable section
open ValuativeRel Matrix Polynomial
open scoped Classical

namespace GlobalTheory.DZA

def KO (k : Type) [Field k] [ValuativeRel k] (n : ℕ) : Subgroup (GL (Fin n) k) :=
  (GeneralLinearGroup.map (algebraMap 𝒪[k] k)).range

def K1 {k : Type} [Field k] [ValuativeRel k] {F : Type} [Field F] (rd : 𝒪[k] →+* F) (n : ℕ) : Subgroup (GL (Fin n) k) :=
  (GeneralLinearGroup.map rd).ker.map (GeneralLinearGroup.map (algebraMap 𝒪[k] k))

def infl {k : Type} [Field k] [ValuativeRel k] {F : Type} [Field F] (rd : 𝒪[k] →+* F) {n : ℕ}
    (fb : GL (Fin n) F → ℂ) (x : GL (Fin n) k) : ℂ :=
  if h : ∃ y : GL (Fin n) 𝒪[k], GeneralLinearGroup.map (algebraMap 𝒪[k] k) y = x then
    fb (GeneralLinearGroup.map rd h.choose) else 0

def IsFinNorm {F F' : Type} [Field F] [Field F'] [Algebra F F'] (s : F' ≃ₐ[F] F') {n : ℕ}
    (δ : GL (Fin n) F') (γ : GL (Fin n) F) : Prop :=
  IsConj (GlobalTheory.LBC.incl F' n γ) (GlobalTheory.LBC.norm F s δ)

def normLift {F F' : Type} [Field F] [Field F'] [Algebra F F'] (s : F' ≃ₐ[F] F') {n : ℕ}
    (fb : GL (Fin n) F → ℂ) (δ : GL (Fin n) F') : ℂ :=
  if h : ∃ γ, IsFinNorm s δ γ then fb h.choose else 0

def InflMatching : Prop :=
  ∀ (k K : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] [Algebra k K],
    Continuous (algebraMap k K) → CharZero k →
    ∀ (F F' : Type) [Field F] [Fintype F] [Field F'] [Fintype F'] [Algebra F F'],
      Module.finrank F F' = Module.finrank k K →
    ∀ (rk : 𝒪[k] →+* F) (rK : 𝒪[K] →+* F'), Function.Surjective rk → Function.Surjective rK →
      (∀ (x : 𝒪[k]) (y : 𝒪[K]), (y : K) = algebraMap k K x → rK y = algebraMap F F' (rk x)) →
    ∀ (s : K ≃ₐ[k] K) (sb : F' ≃ₐ[F] F'),
      (∀ x y : 𝒪[K], (y : K) = s x → rK y = sb (rK x)) →
      (∀ z : F', sb z = z ^ Fintype.card F) →
    ∀ (n : ℕ) (fb : GL (Fin n) F → ℂ), (∀ a b, fb (b⁻¹ * a * b) = fb a) →
      (∀ δ : GL (Fin n) K, (GlobalTheory.LBC.norm k s δ : Matrix (Fin n) (Fin n) K).charpoly.Separable →
        ∀ γ : GL (Fin n) k, (γ : Matrix (Fin n) (Fin n) k).charpoly.map (algebraMap k K) =
            (GlobalTheory.LBC.norm k s δ : Matrix (Fin n) (Fin n) K).charpoly →
          GlobalTheory.BCT.twOrb (GlobalTheory.LBC.galAct s n) (KO K n) δ (infl rK (normLift sb fb)) =
            GlobalTheory.BCT.twOrb (MonoidHom.id _) (KO k n) γ (infl rk fb)) ∧
      (∀ γ : GL (Fin n) k, (γ : Matrix (Fin n) (Fin n) k).charpoly.Separable →
        GlobalTheory.BCT.twOrb (MonoidHom.id _) (KO k n) γ (infl rk fb) ≠ 0 →
          ∃ δ : GL (Fin n) K, (γ : Matrix (Fin n) (Fin n) k).charpoly.map (algebraMap k K) =
            (GlobalTheory.LBC.norm k s δ : Matrix (Fin n) (Fin n) K).charpoly)

end GlobalTheory.DZA
end
end

