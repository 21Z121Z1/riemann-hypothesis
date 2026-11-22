import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.Bundle0025
import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.LThCoefB

-- bundled from Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.LLatBoundC
section
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open IsDedekindDomain NumberField
open GlobalTheory.RegSch (ikS projS Lvl)

namespace PositivityTheory.Rg.Rsw.L.LLatBound

variable {D : D7}

theorem mtL_mul (V : HSp D) (g h : GA D V) : mt V (g * h) = mt V g * mt V h := rfl

theorem mtL_one (V : HSp D) : mt V 1 = 1 := rfl

theorem finPart_mtL {V : HSp D} {a : GA D V} (ha : a ∈ GinfC V) : (mt V a).map (finPart D) = 1 := by
  have h0 : finHom V a = 1 := ha
  have h1 : (finHom V a).1 = 1 := by rw [h0]; rfl
  exact h1

theorem den_finL {ι : Type} [Fintype ι] (z : ι → Af D.host.F ⊗[D.host.F] D.host.E) :
    ∃ N : ℕ, 0 < N ∧ ∀ i, N • z i ∈ intAE D := by
  classical
  choose N hN hNz using fun i => GlobalTheory.CompanionTheory.Ipf.Bdd.den_one (D := D) (z i)
  refine ⟨∏ i, N i, Finset.prod_pos fun i _ => hN i, fun i => ?_⟩
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i), mul_comm, mul_smul]
  exact AddSubgroup.nsmul_mem _ (hNz i) _

theorem compAt_mt_GfC (θ : InfFam D) (V : HSp D) {k : GA D V} (hk : k ∈ GfC V) (τ : D.what₂.Tau) :
    compAt θ τ (mt V k) = 1 := by
  have h0 : infHom V k = 1 := hk
  have h : (mt V k).map (infPart D) = 1 := by
    have h1 : (infHom V k).1 = 1 := by rw [h0]; rfl
    exact h1
  ext i j
  have hij := congrFun (congrFun h i) j
  simp only [Matrix.map_apply] at hij
  simp only [compAt, Matrix.map_apply, hij, Matrix.one_apply]
  split_ifs <;> simp

set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 400000 in
theorem gen_bound_col {θ : InfFam D} (hθ : IsInfFam θ) (V : HSp D) (n : ℕ) (y : GA D V)
    (f : SchwartzMap (D.what₂.Tau → Fin V.rank → Fin n → ℂ) ℂ)
    (g : (Fin V.rank → Fin n → Af D.host.F ⊗[D.host.F] D.host.E) → ℂ)
    (hg : g ∈ GlobalTheory.WeilM.SB (Fin V.rank → Fin n → Af D.host.F ⊗[D.host.F] D.host.E)) :
    ∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ a ∈ GinfC V, ∀ k ∈ GfC V, (∀ i j, finPart D (mt V k⁻¹ i j) ∈ intAE D) →
      ∑' x : {x : Matrix (Fin V.rank) (Fin n) D.host.E // x.rank = V.rank},
        ‖f (fun τ i j => compAt θ τ (mm (mt V (k * a * y)) (rat x.1)) i j) *
          g (fun i j => finPart D ((mm (mt V (k * a * y)) (rat x.1)) i j))‖ₑ ≤ C := by
  obtain ⟨Mg, hMg⟩ := hg.1.continuous.bounded_above_of_compact_support hg.2
  obtain ⟨N, hN, hNK⟩ := GlobalTheory.CompanionTheory.Ipf.Bdd.exists_den_matrix (D := D) (a := V.rank) (b := n) (K := tsupport g) hg.2
  obtain ⟨M, hM, hMy⟩ := den_finL (D := D)
    (fun p : Fin V.rank × Fin V.rank => finPart D (mt V y⁻¹ p.1 p.2))
  obtain ⟨C₀, hC₀⟩ := fullRank_col D V.rank n (N * M) (Nat.mul_pos hN hM) f
  refine ⟨ENNReal.ofReal C₀ * ENNReal.ofReal Mg, ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top,
    fun a ha k hk hki => ?_⟩
  set B : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ := fun τ => compAt θ τ (mt V (a * y)) with hBdef
  have hB : ∀ τ, ‖(B τ).det‖ = 1 := fun τ => GlobalTheory.CompanionTheory.Ipf.Bdd.norm_det_compAt hθ τ V (a * y)
  have hmt : mt V (k * a * y) = mt V k * mt V (a * y) := by
    rw [mul_assoc, mtL_mul]

  have hinf : ∀ x : Matrix (Fin V.rank) (Fin n) D.host.E,
      (fun τ i j => compAt θ τ (mm (mt V (k * a * y)) (rat x)) i j) = fun τ => B τ * x.map (tauE D τ) := by
    intro x
    funext τ i j
    have e1 := GlobalTheory.CompanionTheory.Ipf.Bdd.compAt_mulM θ τ (mt V (k * a * y)) (rat x)
    have e2 := GlobalTheory.CompanionTheory.Ipf.Bdd.compAt_mulM θ τ (mt V k) (mt V (a * y))
    have e0 : compAt θ τ (rat x) = x.map (tauE D τ) := GlobalTheory.CompanionTheory.Ipf.Bdd.compAt_rat hθ τ x
    rw [e0] at e1
    rw [compAt_mt_GfC θ V hk τ, Matrix.one_mul] at e2
    have e4 : compAt θ τ (mt V (k * a * y)) = B τ := by
      rw [hmt]; exact e2
    have e3 : compAt θ τ (mm (mt V (k * a * y)) (rat x)) = B τ * x.map (tauE D τ) := by
      rw [← e4]; exact e1
    rw [e3]

  set Yf : Matrix (Fin V.rank) (Fin V.rank) (Af D.host.F ⊗[D.host.F] D.host.E) := (mt V y).map (finPart D) with hYf
  set Yi : Matrix (Fin V.rank) (Fin V.rank) (Af D.host.F ⊗[D.host.F] D.host.E) := (mt V y⁻¹).map (finPart D) with hYi
  set Kf : Matrix (Fin V.rank) (Fin V.rank) (Af D.host.F ⊗[D.host.F] D.host.E) := (mt V k).map (finPart D) with hKf
  set Ki : Matrix (Fin V.rank) (Fin V.rank) (Af D.host.F ⊗[D.host.F] D.host.E) := (mt V k⁻¹).map (finPart D) with hKi
  have hYY : Yi * Yf = 1 := by
    rw [hYi, hYf, ← Matrix.map_mul, ← mtL_mul, inv_mul_cancel, mtL_one]
    exact Matrix.map_one _ (map_zero _) (map_one _)
  have hKK : Ki * Kf = 1 := by
    rw [hKi, hKf, ← Matrix.map_mul, ← mtL_mul, inv_mul_cancel, mtL_one]
    exact Matrix.map_one _ (map_zero _) (map_one _)
  have hfin : ∀ x : Matrix (Fin V.rank) (Fin n) D.host.E,
      (mm (mt V (k * a * y)) (rat x)).map (finPart D) = Kf * Yf * x.map (fun c => finPart D (incA D c)) := by
    intro x
    have : (mt V (a * y)).map (finPart D) = Yf := by
      rw [mtL_mul, Matrix.map_mul, finPart_mtL ha, Matrix.one_mul]
    show (mt V (k * a * y) * rat x).map (finPart D) = _
    rw [Matrix.map_mul, hmt, Matrix.map_mul, this]
    rfl

  have hden : ∀ x : Matrix (Fin V.rank) (Fin n) D.host.E,
      g (fun i j => finPart D ((mm (mt V (k * a * y)) (rat x)) i j)) ≠ 0 →
        ∀ i j, ((N * M : ℕ) : D.host.E) * x i j ∈ GlobalTheory.CompanionTheory.Ipf.Bdd.intR D := by
    intro x hx i j
    set Z : Matrix (Fin V.rank) (Fin n) (Af D.host.F ⊗[D.host.F] D.host.E) :=
      (mm (mt V (k * a * y)) (rat x)).map (finPart D) with hZ
    have hZK : Z ∈ tsupport g := subset_tsupport _ hx
    have hxZ : x.map (fun c => finPart D (incA D c)) = Yi * (Ki * Z) := by
      rw [hZ, hfin x, ← Matrix.mul_assoc Ki, ← Matrix.mul_assoc Ki, hKK, Matrix.one_mul, ← Matrix.mul_assoc,
        hYY, Matrix.one_mul]
    refine GlobalTheory.CompanionTheory.Ipf.Bdd.mem_intR_of_finPart ?_
    have e : finPart D (incA D (((N * M : ℕ) : D.host.E) * x i j)) =
        ∑ l, ∑ m, (M • Yi i l) * (Ki l m * (N • Z m j)) := by
      have hij : finPart D (incA D (x i j)) = (Yi * (Ki * Z)) i j := by
        rw [← hxZ]; rfl
      rw [map_mul, map_mul, hij, Matrix.mul_apply, Finset.mul_sum]
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [Matrix.mul_apply, Finset.mul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun m _ => ?_
      simp only [map_natCast, nsmul_eq_mul]
      push_cast
      ring
    rw [e]
    refine sum_mem fun l _ => sum_mem fun m _ => ?_
    exact GlobalTheory.CompanionTheory.Ipf.Bdd.mul_mem_int (hMy (i, l)) (GlobalTheory.CompanionTheory.Ipf.Bdd.mul_mem_int (hki l m) (hNK Z hZK m j))

  set S₁ : Set (Matrix (Fin V.rank) (Fin n) D.host.E) := {x | x.rank = V.rank} with hS₁
  set S₂ : Set (Matrix (Fin V.rank) (Fin n) D.host.E) :=
    {x | x.rank = V.rank ∧ ∀ i j, ((N * M : ℕ) : D.host.E) * x i j ∈ GlobalTheory.CompanionTheory.Ipf.Bdd.intR D} with hS₂
  set F : Matrix (Fin V.rank) (Fin n) D.host.E → ℝ≥0∞ := fun x =>
    ‖f (fun τ i j => compAt θ τ (mm (mt V (k * a * y)) (rat x)) i j) *
      g (fun i j => finPart D ((mm (mt V (k * a * y)) (rat x)) i j))‖ₑ with hF
  set G : Matrix (Fin V.rank) (Fin n) D.host.E → ℝ≥0∞ := fun x =>
    ‖f (fun τ => B τ * x.map (tauE D τ))‖ₑ * ENNReal.ofReal Mg with hG
  have e1 : ∑' x : {x : Matrix (Fin V.rank) (Fin n) D.host.E // x.rank = V.rank}, F x.1 = ∑' x, S₁.indicator F x :=
    tsum_subtype S₁ F
  have e2 : ∑' x : S₂, G x.1 = ∑' x, S₂.indicator G x := tsum_subtype S₂ G
  have hle : ∀ x, S₁.indicator F x ≤ S₂.indicator G x := by
    intro x
    by_cases h1 : x ∈ S₁
    · rw [Set.indicator_of_mem h1]
      by_cases h0 : g (fun i j => finPart D ((mm (mt V (k * a * y)) (rat x)) i j)) = 0
      · have : F x = 0 := by simp only [hF, h0, mul_zero, enorm_zero]
        rw [this]; exact zero_le
      · have h2 : x ∈ S₂ := ⟨h1, hden x h0⟩
        rw [Set.indicator_of_mem h2]
        simp only [hF, hG]
        rw [hinf x, enorm_mul]
        gcongr
        rw [← ofReal_norm]
        exact ENNReal.ofReal_le_ofReal (hMg _)
    · rw [Set.indicator_of_notMem h1]; exact zero_le
  show ∑' x : {x : Matrix (Fin V.rank) (Fin n) D.host.E // x.rank = V.rank}, F x.1 ≤ _
  rw [e1]
  calc ∑' x, S₁.indicator F x ≤ ∑' x, S₂.indicator G x := ENNReal.tsum_le_tsum hle
    _ = ∑' x : S₂, G x.1 := e2.symm
    _ = (∑' x : S₂, ‖f (fun τ => B τ * x.1.map (tauE D τ))‖ₑ) * ENNReal.ofReal Mg := ENNReal.tsum_mul_right
    _ ≤ ENNReal.ofReal C₀ * ENNReal.ofReal Mg := by
        gcongr
        exact hC₀ B hB

end PositivityTheory.Rg.Rsw.L.LLatBound

end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.LThCoef
section
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open IsDedekindDomain NumberField
open GlobalTheory.RegSch (ikS projS Lvl)

namespace PositivityTheory.Rg.Rsw.L.LThCoef

open GlobalTheory.CompanionTheory.SiegelND (pairH)
open GlobalTheory.CompanionTheory.ThetaCoefND (gramOf continuous_pairH pairH_ne_zero setIntegral_pairH)
open GlobalTheory.CompanionTheory.HermPoisson (ofHermE)

variable {D : D7}

theorem thS_eq (ψ : AddChar (AF D.host.F) ℂ) (hψ : IsCharAF D.host.F ψ) {W : HSp D} {n : ℕ} {m : Measure (GA D W)}
    {𝓕 : Set (GA D W)} {Ψ : Mx D W.rank n → ℂ} (hvol : m 𝓕 < ⊤) (hΨ : Continuous Ψ) {C : ℝ≥0}
    (hC : ∀ h : GA D W, ∑' x : Sp W n, ‖Ψ (mm (mt W h⁻¹) (rat x.1))‖ₑ ≤ C) (x : hermA D n) :
    thS W m 𝓕 (fun X => pch ψ x.1 (ip W X X) * Ψ X) =
      ∑' y : Sp W n, pairH ψ (ofHermE (gramOf W y.1)).1 x * co W m 𝓕 Ψ y.1 := by
  obtain ⟨-, hψn, -, -⟩ := hψ
  have hnorm : ∀ y : Sp W n, ‖pairH ψ (ofHermE (gramOf W y.1)).1 x‖ = 1 := fun y => hψn _
  have key : ∀ (h : GA D W) (y : Sp W n),
      pch ψ x.1 (ip W (mm (mt W h⁻¹) (rat y.1)) (mm (mt W h⁻¹) (rat y.1))) * Ψ (mm (mt W h⁻¹) (rat y.1)) =
        pairH ψ (ofHermE (gramOf W y.1)).1 x * Ψ (mm (mt W h⁻¹) (rat y.1)) := by
    intro h y
    rw [ip_inv]
    exact congrArg (· * Ψ (mm (mt W h⁻¹) (rat y.1))) (pch_rat ψ x (gramOf W y.1))
  calc thS W m 𝓕 (fun X => pch ψ x.1 (ip W X X) * Ψ X)
      = ∫ h in 𝓕, ∑' y : Sp W n, pch ψ x.1 (ip W (mm (mt W h⁻¹) (rat y.1)) (mm (mt W h⁻¹) (rat y.1))) *
          Ψ (mm (mt W h⁻¹) (rat y.1)) ∂m := rfl
    _ = ∫ h in 𝓕, ∑' y : Sp W n, pairH ψ (ofHermE (gramOf W y.1)).1 x * Ψ (mm (mt W h⁻¹) (rat y.1)) ∂m := by
        congr 1
        funext h
        congr 1
        funext y
        exact key h y
    _ = _ := exch hvol hΨ hC (fun y : Sp W n => pairH ψ (ofHermE (gramOf W y.1)).1 x) hnorm

theorem _root_.PositivityTheory.Rg.Rsw.L.thCoef : LatBound → ThCoef := by
  classical
  intro hLB D n W ψ hψ θ hθ m 𝓕 hm h𝓕 lam 𝓖 hl Ψ hΨ
  obtain ⟨C, hC⟩ := hLB D θ hθ W n Ψ hΨ
  have hvol : m 𝓕 < ⊤ := GlobalTheory.Cmp.RallisRange.vol_lt_top W hm h𝓕
  have hΨc : Continuous Ψ := (GlobalTheory.CompanionTheory.WeilTheta.schwartzA_continuous_and_dominated D θ hθ _ _ Ψ hΨ).1
  have hth := fun x => thS_eq ψ hψ hvol hΨc hC x
  have hsum := summable_co hvol hΨc hC
  have hpn : ∀ (S x : hermA D n), ‖pairH ψ S x‖ = 1 := fun S x => hψ.2.1 _
  refine ⟨hvol.ne, ?_, fun β => ?_⟩
  · refine (continuous_tsum (f := fun (y : Sp W n) (x : hermA D n) => pairH ψ (ofHermE (gramOf W y.1)).1 x * co W m 𝓕 Ψ y.1)
      (fun y => (continuous_pairH hψ _).mul continuous_const) hsum
      (fun y x => by rw [norm_mul, hpn, one_mul])).congr fun x => (hth x).symm
  obtain ⟨i1, -, i3, -, -, -⟩ := lattice_Mx D n n
  have : IsTopologicalAddGroup (Mx D n n) := i1
  have : SecondCountableTopology (Mx D n n) := i3
  have : BorelSpace (Mx D n n) := ⟨rfl⟩
  have : SecondCountableTopology (hermA D n) := Topology.IsInducing.subtypeVal.secondCountableTopology
  have : BorelSpace (hermA D n) := Subtype.borelSpace _
  have hcoef : ∫ x in 𝓖, thS W m 𝓕 (fun X => pch ψ x.1 (ip W X X) * Ψ X) * conj (pch ψ x.1 (rat β.1)) ∂lam =
      ∑' y : Sp W n, if gramOf W y.1 = β then co W m 𝓕 Ψ y.1 else 0 := by
    have e1 : ∀ x : hermA D n, thS W m 𝓕 (fun X => pch ψ x.1 (ip W X X) * Ψ X) * conj (pch ψ x.1 (rat β.1)) =
        ∑' y : Sp W n, co W m 𝓕 Ψ y.1 * (pairH ψ (ofHermE (gramOf W y.1)).1 x * (pairH ψ (ofHermE β).1 x)⁻¹) :=
      fun x => by
        rw [hth x, pch_rat ψ x β, conj_eq_inv (hpn _ _), ← tsum_mul_right]
        exact tsum_congr fun y => by ring
    rw [integral_congr_ae (ae_of_all _ e1), integral_tsum]
    · refine tsum_congr fun y => ?_
      rw [integral_const_mul]
      split_ifs with h
      · rw [h]
        have e3 : ∀ x, pairH ψ (ofHermE β).1 x * (pairH ψ (ofHermE β).1 x)⁻¹ = 1 := fun x =>
          mul_inv_cancel₀ (pairH_ne_zero hψ _ _)
        simp only [e3, integral_const, measureReal_def, Measure.restrict_apply_univ, hl.2.2]
        simp
      · rw [setIntegral_pairH hψ hl h, mul_zero]
    · intro y
      exact (continuous_const.mul ((continuous_pairH hψ _).mul
        ((continuous_pairH hψ _).inv₀ (pairH_ne_zero hψ _)))).aestronglyMeasurable
    · have e2 : ∀ y : Sp W n, ∫⁻ x in 𝓖, ‖co W m 𝓕 Ψ y.1 * (pairH ψ (ofHermE (gramOf W y.1)).1 x *
          (pairH ψ (ofHermE β).1 x)⁻¹)‖ₑ ∂lam = ‖co W m 𝓕 Ψ y.1‖ₑ := fun y => by
        have e4 : ∀ x, ‖co W m 𝓕 Ψ y.1 * (pairH ψ (ofHermE (gramOf W y.1)).1 x *
            (pairH ψ (ofHermE β).1 x)⁻¹)‖ₑ = ‖co W m 𝓕 Ψ y.1‖ₑ := fun x => by
          have h5 : ‖co W m 𝓕 Ψ y.1 * (pairH ψ (ofHermE (gramOf W y.1)).1 x *
              (pairH ψ (ofHermE β).1 x)⁻¹)‖ = ‖co W m 𝓕 Ψ y.1‖ := by
            rw [norm_mul, norm_mul, norm_inv, hpn, hpn]
            simp
          exact (ofReal_norm _).symm.trans ((congrArg ENNReal.ofReal h5).trans (ofReal_norm _))
        simp only [e4, setLIntegral_const, hl.2.2, mul_one]
      simp only [e2]
      exact tsum_co_ne_top hvol hΨc hC
  refine ⟨fun hno => ?_, fun x₀ hr hg => ?_⟩
  · rw [hcoef]
    exact (tsum_congr fun y => if_neg fun h => hno ⟨y.1, y.2, congrArg Subtype.val h⟩).trans tsum_zero
  rw [hcoef]
  obtain ⟨-, -, -, hB, hTG, -, hcount⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D W
  have : MeasurableConstSMul (GQ W) (GA D W) := ⟨fun γ => measurable_const_mul (γ : GA D W)⟩
  have : SMulInvariantMeasure (GQ W) (GA D W) m := ⟨fun γ s _ => measure_preimage_mul m (γ : GA D W) s⟩
  obtain ⟨e, he⟩ := orbit_equiv W x₀ hr
  let T := {y : Matrix (Fin W.rank) (Fin n) D.host.E // y.rank = W.rank ∧ gramQ W y = gramQ W x₀}
  let s : Set (Sp W n) := {y | gramOf W y.1 = β}
  let q : s ≃ T :=
    { toFun := fun y => ⟨y.1.1, y.1.2, (congrArg Subtype.val y.2 : gramQ W y.1.1 = β.1).trans hg.symm⟩
      invFun := fun t => ⟨⟨t.1, t.2.1⟩, Subtype.ext (t.2.2.trans hg)⟩
      left_inv := fun y => rfl
      right_inv := fun t => rfl }
  have hpt : ∀ (γ : GQ W) (h : GA D W), Ψ (mm (mt W h⁻¹) (rat (e γ).1)) = Ψ (mm (mt W (γ⁻¹ • h)⁻¹) (rat x₀)) :=
    fun γ h => by
      rw [he]
      show Ψ (mm (mt W h⁻¹) (mm (mt W γ) (rat x₀))) = Ψ (mm (mt W (((γ : GA D W))⁻¹ * h)⁻¹) (rat x₀))
      rw [mul_inv_rev, inv_inv, mt_mul]
      exact congrArg Ψ (Matrix.mul_assoc _ _ _).symm
  have hint : Integrable (fun h : GA D W => Ψ (mm (mt W h⁻¹) (rat x₀))) m := by
    refine ⟨(cont_term hΨc x₀).aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_enorm, h𝓕.lintegral_eq_tsum']
    let g : T → ℝ≥0∞ := fun t => ∫⁻ h in 𝓕, ‖Ψ (mm (mt W h⁻¹) (rat t.1))‖ₑ ∂m
    have hinj : Function.Injective fun t : T => (⟨t.1, t.2.1⟩ : Sp W n) := fun t t' h =>
      Subtype.ext (by simpa using congrArg Subtype.val h)
    calc ∑' γ : GQ W, ∫⁻ h in 𝓕, ‖Ψ (mm (mt W (γ⁻¹ • h)⁻¹) (rat x₀))‖ₑ ∂m = ∑' γ, g (e γ) :=
          tsum_congr fun γ => by simp only [g, hpt]
      _ = ∑' t, g t := e.tsum_eq g
      _ ≤ ∑' y : Sp W n, ∫⁻ h in 𝓕, ‖Ψ (mm (mt W h⁻¹) (rat y.1))‖ₑ ∂m :=
          ENNReal.tsum_comp_le_tsum_of_injective hinj (fun y : Sp W n => ∫⁻ h in 𝓕, ‖Ψ (mm (mt W h⁻¹) (rat y.1))‖ₑ ∂m)
      _ < ⊤ := lint_fin hvol hΨc hC
  calc (∑' y : Sp W n, if gramOf W y.1 = β then co W m 𝓕 Ψ y.1 else 0)
      = ∑' y : Sp W n, s.indicator (fun y => co W m 𝓕 Ψ y.1) y := tsum_congr fun y => by
        simp only [Set.indicator_apply, s, Set.mem_ofPred_eq]
    _ = ∑' y : s, co W m 𝓕 Ψ y.1.1 := (tsum_subtype s _).symm
    _ = ∑' t : T, co W m 𝓕 Ψ t.1 := q.tsum_eq (fun t => co W m 𝓕 Ψ t.1)
    _ = ∑' γ : GQ W, co W m 𝓕 Ψ (e γ).1 := (e.tsum_eq (fun t => co W m 𝓕 Ψ t.1)).symm
    _ = ∑' γ : GQ W, ∫ h in 𝓕, Ψ (mm (mt W (γ⁻¹ • h)⁻¹) (rat x₀)) ∂m :=
        tsum_congr fun γ => integral_congr_ae (ae_of_all _ fun h => hpt γ h)
    _ = orb W m Ψ x₀ := (h𝓕.integral_eq_tsum' _ hint).symm

end PositivityTheory.Rg.Rsw.L.LThCoef

end
end

