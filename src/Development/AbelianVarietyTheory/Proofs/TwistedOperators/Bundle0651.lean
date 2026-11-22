import Mathlib
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.FormulaAt
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumOKEx
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0318
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValuationLeOneOfMem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnderMemAndPlaceAboveEqOfMem
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0575
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0641
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0614
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0624
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0617
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.DepthPays
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0535
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0643
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0020
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0022
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0315
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0558
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0318
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0322
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0645
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.TwistPlacesOffPrimeQZero
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0533
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0004
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0006
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0019
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ToricSymbols
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0078
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0576

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.OppositePathLocalTotalTensorMemCoefficientField
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest Formalism.IndefR.WeilFull GlobalTheory.RowClaim
open MeasureTheory GlobalTheory.SplitFlip GlobalTheory.SplitWeil

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.TflipField

section Generic

open ValuativeRel

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  [MeasurableSpace k] [BorelSpace k]

omit [MeasurableSpace k] [BorelSpace k] in

theorem apow_nat_half_mem (F : Subfield ℂ) (habs : ∀ u : kˣ, apow u (1 / 2) ∈ F) (x : kˣ) (n : ℕ) :
    apow x ((n : ℂ) / 2) ∈ F := by
  have : apow x ((n : ℂ) / 2) = apow x (1 / 2) ^ n := by
    rw [apow, apow, ← Complex.cpow_nat_mul]; congr 1; ring
  rw [this]; exact F.pow_mem (habs x) n

omit [MeasurableSpace k] [BorelSpace k] in

theorem fourierSum_mem {A D : Type} [Fintype A] [DecidableEq A] [DecidableEq D] (F : Subfield ℂ) (ψ : AddChar k Circle)
    (ϖ : kˣ) (e : ℕ) (P : Finset D) (hψ : ∀ x : k, valuation k (((ϖ ^ e : kˣ) : k) * x) ≤ 1 → (ψ x : ℂ) ∈ F)
    {Φ : Matrix A D k → ℂ} (hΦ : ∀ X, Φ X ∈ F) (Y : Matrix A D k) : fourierSum ψ ϖ e P Φ Y ∈ F := by
  classical
  rw [fourierSum_apply]
  split_ifs with h
  · refine F.mul_mem (F.inv_mem (F.pow_mem (natCast_mem F _) _)) (F.sum_mem fun T _ => F.mul_mem (hΦ _) (hψ _ ?_))
    rw [← Valuation.mem_integer_iff]
    change _ ∈ 𝒪[k]
    rw [pairCols, Finset.mul_sum]
    refine Subring.sum_mem _ fun i _ => ?_
    rw [Finset.mul_sum]
    refine Subring.sum_mem _ fun j _ => ?_
    rw [mul_left_comm]
    exact Subring.mul_mem _ (liftRes_mem T i j) (h i j j.2)
  · exact F.zero_mem

omit [MeasurableSpace k] [BorelSpace k] in

theorem invFourierSum_inv_mem {A D : Type} [Fintype A] [DecidableEq A] [DecidableEq D] (F : Subfield ℂ) (ψ : AddChar k Circle)
    (ϖ : kˣ) (e : ℕ) (P : Finset D) (hψ : ∀ x : k, valuation k (((ϖ ^ e : kˣ) : k) * x) ≤ 1 → (ψ x : ℂ) ∈ F)
    {Φ : Matrix A D k → ℂ} (hΦ : ∀ X, Φ X ∈ F) (T : Matrix A D k) : invFourierSum ψ⁻¹ ϖ e P Φ T ∈ F := by
  classical
  rw [invFourierSum_inv_apply]
  split_ifs with h
  · refine F.sum_mem fun S _ => F.mul_mem (hΦ _) (hψ _ ?_)
    rw [← Valuation.mem_integer_iff]
    change _ ∈ 𝒪[k]
    have e1 : ((ϖ ^ e : kˣ) : k) * pairCols P T ((ϖ ^ e)⁻¹ • liftRes S) = ∑ i, ∑ j : P, liftRes S i j * T i j := by
      rw [pairCols, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Matrix.smul_apply, Units.smul_def, smul_eq_mul, ← mul_assoc, ← mul_assoc, ← Units.val_mul, mul_inv_cancel,
        Units.val_one, one_mul]
    rw [e1]
    exact Subring.sum_mem _ fun i _ => Subring.sum_mem _ fun j _ => Subring.mul_mem _ (liftRes_mem S i j) (h i j j.2)
  · exact F.zero_mem

theorem smallF_mem {A A' D : Type} [Fintype A] [DecidableEq A] [Fintype A'] [DecidableEq A'] [Fintype D] [DecidableEq D]
    (F : Subfield ℂ) {J : Subgroup (GL A' k)} (hJo : IsOpen (J : Set (GL A' k))) (hJK : J ≤ KO k A')
    (σ : A ⊕ A' ≃ D) (ν : kˣ →* ℂˣ) {ϖ : kˣ} {e : ℕ} (hϖ : IsUnif ϖ) (he : 1 ≤ e) (hν : CondLE ϖ e ν) (hram : ¬ IsUnram ν)
    (hνF : ∀ u, (ν u : ℂ) ∈ F) (habs : ∀ u : kˣ, apow u (1 / 2) ∈ F) (c : D → kˣ) {Ψ : Matrix A' D k → ℂ}
    (hΨ : HasDepth ϖ e (diagLat c) Ψ) (hΨF : ∀ X, Ψ X ∈ F) (h : GL D k) :
    smallF (haarVol J) ν Ψ (Y0 k σ * h.val) ∈ F :=
  GlobalTheory.T.glOrbitIntegral_depthDatum_mem_subfield F hJo hJK σ ν hϖ he hν hram hνF habs c hΨ hΨF h

theorem phiA_mem {A A' D : Type} [Fintype A] [DecidableEq A] [Fintype A'] [DecidableEq A'] [Fintype D] [DecidableEq D]
    (F : Subfield ℂ) {J : Subgroup (GL A' k)} (hJo : IsOpen (J : Set (GL A' k))) (hJK : J ≤ KO k A')
    (σ : A ⊕ A' ≃ D) (ν : kˣ →* ℂˣ) {ϖ : kˣ} {e : ℕ} (hϖ : IsUnif ϖ) (he : 1 ≤ e) (hν : CondLE ϖ e ν) (hram : ¬ IsUnram ν)
    (hνF : ∀ u, (ν u : ℂ) ∈ F) (habs : ∀ u : kˣ, apow u (1 / 2) ∈ F) (c : D → kˣ) (Λ' : Submodule 𝒪[k] (D → k))
    {Ψ : Matrix A' D k → ℂ} (hΨ : HasDepth ϖ e (diagLat c) Ψ) (hΨF : ∀ X, Ψ X ∈ F) (X : Matrix A D k) :
    phiA (haarVol J) σ ν ϖ e Λ' Ψ X ∈ F := by
  classical
  unfold phiA
  split_ifs
  · unfold fFun
    split_ifs with hX
    · exact F.mul_mem (F.mul_mem (hνF _) (apow_nat_half_mem F habs _ _))
        (smallF_mem F hJo hJK σ ν hϖ he hν hram hνF habs c hΨ hΨF _)
    · exact F.zero_mem
  · exact F.zero_mem

theorem flipTensor_mem {G : Grid k} (F : Subfield ℂ) {ψ : AddChar k Circle} {ϖ : kˣ} {e : ℕ} (hϖ : IsUnif ϖ)
    (hψc : HasConductor ψ 1) (he : 1 ≤ e) (habs : ∀ u : kˣ, apow u (1 / 2) ∈ F)
    (hψ : ∀ x : k, valuation k (((ϖ ^ e : kˣ) : k) * x) ≤ 1 → (ψ x : ℂ) ∈ F) {i j : ℕ}
    (hν : CondLE ϖ e (G.nu i j)) (hram : ¬ IsUnram (G.nu i j)) (hνF : ∀ u, (G.nu i j u : ℂ) ∈ F) {J : G.Level}
    (hJ : IsOpen (J (i, j) : Set (GL (Fin (G.rank (i, j))) k))) (hK : J (i, j) ≤ KO k _) {γ : List Edge}
    (h1 : Edge.theta i j ∈ γ) (h2 : Edge.ex i j ∈ γ) {T : G.Args → ℂ} (hT : G.IsTensor ϖ e γ T) (hTF : ∀ x, T x ∈ F)
    (x : G.Args) : G.flipTensor .one ψ ϖ e i j J T x ∈ F := by
  have hJ' := isOpen_map_invT hJ hK
  unfold Grid.flipTensor squareFlip
  exact invFourierSum_inv_mem F ψ ϖ e _ hψ (fun X => phiA_mem F hJ'.1 hJ'.2 _ _ hϖ he hν hram hνF habs
    (blockUnits ϖ e _) _ ((FourierDepth.fourier_exchange k _ _ ψ ϖ e _ hϖ hψc).1 _ (isNatDatum_sliceB hT h1 h2 x))
    (fun Y => fourierSum_mem F ψ ϖ e _ hψ (fun Z => hTF _) Y) X) _

theorem flips_mem {G : Grid k} (F : Subfield ℂ) {ψ : AddChar k Circle} {ϖ : kˣ} {e : ℕ} (hϖ : IsUnif ϖ)
    (hψc : HasConductor ψ 1) (he : 1 ≤ e) (habs : ∀ u : kˣ, apow u (1 / 2) ∈ F)
    (hψ : ∀ x : k, valuation k (((ϖ ^ e : kˣ) : k) * x) ≤ 1 → (ψ x : ℂ) ∈ F) :
    ∀ (l : List (ℕ × ℕ)) (S : G.PiLocalization₂),
      (∀ x ∈ l, CondLE ϖ e (G.nu x.1 x.2) ∧ ¬ IsUnram (G.nu x.1 x.2) ∧ ∀ u, (G.nu x.1 x.2 u : ℂ) ∈ F) →
      CanFlip S.path l → (∀ X, IsOpen (S.level X : Set (GL (Fin (G.rank X)) k)) ∧ S.level X ≤ KO k _) →
      G.IsTensor ϖ e S.path S.tensor → (∀ z, S.tensor z ∈ F) → ∀ z, (S.flips .one ψ ϖ e l).tensor z ∈ F := by
  intro l
  induction l with
  | nil => intro S _ _ _ _ hF; exact hF
  | cons x l ih =>
    intro S hν hc hJ hT hF
    obtain _ | ⟨hp, hc'⟩ := hc
    have hsub := hp.subset
    have hx := hν x List.mem_cons_self
    refine ih (S.flip .one ψ ϖ e x) (fun y hy => hν y (List.mem_cons_of_mem _ hy)) hc' (fun X => ?_)
      (isTensor_flipTensor hϖ hψc he hx.1 (hJ _).1 (hJ _).2 (hsub (by simp)) (hsub (by simp)) hT)
      (flipTensor_mem F hϖ hψc he habs hψ hx.1 hx.2.1 hx.2.2 (hJ _).1 (hJ _).2 (hsub (by simp)) (hsub (by simp)) hT hF)
    change IsOpen (G.flipLevel x.1 x.2 S.level X : Set (GL (Fin (G.rank X)) k)) ∧ G.flipLevel x.1 x.2 S.level X ≤ _
    by_cases hX : X = (x.1 + 1, x.2 + 1)
    · subst hX; simp only [Grid.flipLevel, Function.update_self]; exact ⟨isOpen_KO, le_rfl⟩
    · simp only [Grid.flipLevel, Function.update_of_ne hX]; exact hJ X

end Generic

end GlobalTheory.TflipField

namespace GlobalTheory.TflipField

section Concrete

open ValuativeRel Formalism.L2.Host

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc}

theorem givenStage_mem (F : Subfield ℂ) (B : Frames G) (t : T) (Φ : G.Datum) (w : Pl D.host.E)
    (hmu : ∀ j x, ((L.C.mu0 j).loc w x : ℂ) ∈ F) (hxi : ∀ x, ((L.xiH t).loc w x : ℂ) ∈ F)
    (z : (locGrid G t w).Args) : (givenStage t w B Φ).tensor z ∈ F :=
  GlobalTheory.T.gridGivenPathTensor_mem_subfield F B t Φ w hmu hxi z

theorem nu_mem (F : Subfield ℂ) (t : T) (w : Pl D.host.E) (hmu : ∀ j x, ((L.C.mu0 j).loc w x : ℂ) ∈ F)
    (hxi : ∀ x, ((L.xiH t).loc w x : ℂ) ∈ F) (hchi : ∀ i, 1 ≤ i → i ≤ D.R.m → ∀ x, ((G.ch.chiH i).loc w x : ℂ) ∈ F)
    {i j : ℕ} (hi : i < D.R.m) (hj : j < D.R.m) (u : (Kw w)ˣ) : ((locGrid G t w).nu i j u : ℂ) ∈ F := by
  have e1 : (((locGrid G t w).nu i j u : ℂˣ) : ℂ) =
      ((L.C.mu0 ⟨j, hj⟩).loc w u : ℂ) * ((L.xiH t).loc w u : ℂ) * (((G.ch.chiH (D.R.m - i)).loc w u : ℂ))⁻¹ := by
    simp only [Grid.nu, locGrid, muBase, dif_pos hj, MonoidHom.div_apply, Units.val_div_eq_div_val, div_eq_mul_inv]
    simp [HChar.loc]
  rw [e1]
  exact F.mul_mem (F.mul_mem (hmu _ _) (hxi _)) (F.inv_mem (hchi _ (by omega) (by omega) _))

theorem psiAt_mem (F : Subfield ℂ) {W : G.Weil} {w : Pl D.host.E}
    (hroots : ∀ z : ℂ, z ^ (Ideal.absNorm w.asIdeal ^ depthAt G w) = 1 → z ∈ F) (hcond : HasConductor (psiAt W w) 1)
    (x : Kw w) (hx : valuation (Kw w) ((((unifAt w) ^ depthAt G w : (Kw w)ˣ) : Kw w) * x) ≤ 1) :
    (psiAt W w x : ℂ) ∈ F :=
  GlobalTheory.T.weilTraceAddCharAtPlace_mem_subfield_of_roots F hroots hcond x hx

theorem apow_half_mem (F : Subfield ℂ) (w : Pl D.host.E)
    (hsq : ((Real.sqrt (Ideal.absNorm w.asIdeal) : ℝ) : ℂ) ∈ F) (u : (Kw w)ˣ) : apow u (1 / 2) ∈ F :=
  GlobalTheory.T.normalisedAbsComplexPow_half_mem_subfield_of_sqrt_norm F w hsq u

end Concrete

end GlobalTheory.TflipField

namespace GlobalTheory.RowTest

theorem Tflip_mem_range : ∀ {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} (ch : Choice R) (large₂ : SizeData₂ D)
    (F : Face D A) (CF b : ℝ), HidaSetting large₂ R F → ch.Is → ch.AtScale CF b → ch.FieldOK → ∀ (t : T) (Φ : ch.G.Datum),
    ch.S.SumOK t Φ → ∀ w ∈ locPl ch.G t, ∀ z, Tflip ch.W ch.S.B t Φ w z ∈ Set.range D.what₂.embLL := by
  intro D Γ _ _ Pl0 T A Ks _ _ _ R ch large₂ F CF b hS hch _ hF t Φ _ w hw z
  have hL : R.toLevCh.Is A.μ0 := hS.core.lev
  have hde := GlobalTheory.FlipIntegrand.pde_ne_q_of_setting hS
  have hc : ∀ P ∈ R.toLevCh.Q t, ((Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal := hch.guard t
  have hg := (Good.locGrid_isGood hL ch.G ch.W t hde hc).1 w hw
  have hadm := GivenAdm.givenStage_isAdmissible hL ch.S.B t Φ hw
  have hm : 0 < D.R.m := by have := D.R.two_le_m; omega
  have h00 := hg.square 0 hm 0 hm
  let K : Subfield ℂ := D.what₂.embLL.fieldRange
  have hK : ∀ y, y ∈ Set.range D.what₂.embLL → y ∈ K := fun y hy => RingHom.mem_fieldRange.2 hy
  have hmu : ∀ j x, ((R.toLevCh.C.mu0 j).loc w x : ℂ) ∈ K := fun j x => hK _ (hF.chars.mu0 j w x)
  have hxi : ∀ x, ((R.toLevCh.xiH t).loc w x : ℂ) ∈ K := fun x => hK _ (hF.chars.xi t w x)
  have hchi : ∀ i, 1 ≤ i → i ≤ D.R.m → ∀ x, ((ch.G.ch.chiH i).loc w x : ℂ) ∈ K :=
    fun i a b x => hK _ (hF.chars.chi i a b w x)
  have habs : ∀ u : (Kw w)ˣ, apow u (1 / 2) ∈ K :=
    GlobalTheory.TflipField.apow_half_mem K w (hK _ (hF.sqrt w (.inr ⟨t, hw⟩)))
  have hψ := GlobalTheory.TflipField.psiAt_mem (W := ch.W) K (fun z hz => hK _ (hF.roots t w hw z hz)) h00.cond
  have hν : ∀ x ∈ flipOrder D.R.m, CondLE (unifAt w) (depthAt ch.G w) ((locGrid ch.G t w).nu x.1 x.2) ∧
      ¬ IsUnram ((locGrid ch.G t w).nu x.1 x.2) ∧ ∀ u, ((locGrid ch.G t w).nu x.1 x.2 u : ℂ) ∈ K := by
    intro x hx
    simp only [flipOrder, List.mem_flatMap, List.mem_map, List.mem_range] at hx
    obtain ⟨i, hi, j, hj, rfl⟩ := hx
    have hs := hg.square i hi j hj
    have e := (locGrid ch.G t w).alpha_div_beta i j
    refine ⟨by rw [← e]; exact hs.condν, by rw [← e]; exact hs.ram, GlobalTheory.TflipField.nu_mem K t w hmu hxi hchi hi hj⟩
  have key := GlobalTheory.TflipField.flips_mem K h00.unif h00.cond h00.one_le habs hψ (flipOrder D.R.m)
    (givenStage t w ch.S.B Φ) hν (canFlip_flipOrder _).1 (fun X => GivenAdm.givenLevel_open hL hw X) hadm.tensor
    (GlobalTheory.TflipField.givenStage_mem K ch.S.B t Φ w hmu hxi) z
  exact RingHom.mem_fieldRange.1 key

end GlobalTheory.RowTest
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.PoincareSeriesIdentityTermDominates
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.ChainFr GlobalTheory.SepRows GlobalTheory.SepPer Matrix
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.IdDom

theorem eu_sub_le {n : ℕ} (u u' : Fin n → ℂ) : eu (u - u') ≤ eu u + eu u' := by
  have h : ∀ y : Fin n → ℂ, eu y = ‖(WithLp.toLp 2 y : EuclideanSpace ℂ (Fin n))‖ := fun y => by
    rw [EuclideanSpace.norm_eq]; rfl
  rw [h, h, h, WithLp.toLp_sub]; exact norm_sub_le _ _

theorem nrm_sub_le {D : D7} (θ : InfFam D) {V : HSp D} (B : Fr V) (g : GA D V) (τ : D.what₂.Tau)
    (y y' : Fin V.rank → D.host.E) : nrm θ B g τ (y - y') ≤ nrm θ B g τ y + nrm θ B g τ y' := by
  unfold nrm
  have e : (fun i => tauE D τ ((y - y') i)) = (fun i => tauE D τ (y i)) - fun i => tauE D τ (y' i) := by
    funext i; simp
  rw [e, mulVec_sub, mulVec_sub]; exact eu_sub_le _ _

theorem nrm_nonneg' {D : D7} (θ : InfFam D) {V : HSp D} (B : Fr V) (g : GA D V) (τ : D.what₂.Tau)
    (y : Fin V.rank → D.host.E) : 0 ≤ nrm θ B g τ y := Real.sqrt_nonneg _

set_option maxHeartbeats 1600000 in

theorem identity_dominates : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (Y V : HSp D) (d : HermitianOrthogonalExtensionData Y V 1 1) (S S' : D.what₂.Tau → SPar) (M₀ : DSModel Y S') (M : DSModel V S) (p : Pack M₀ M) (Q : ℝ), p.Base d → ∀ (Λ : Lat Y) (𝔪 : Ideal (𝓞 D.host.E)), IsSelfDualC Y Λ → 𝔪 ≠ ⊥ → ∀ (v : GlobalTheory.Unf.Vol Y) (φ : GA D Y → ℂ) (c : ℂ) (b s : ℝ) (x : GA D Y), GlobalTheory.Unf.IsContAut Y φ → (∀ h, ‖φ h‖ ≤ b) → b / 2 < ‖φ x‖ → 0 ≤ s → s ≤ 1 → Long θ p.A Λ x s → p.AdelicAt θ d Q (d.lat Λ fun _ => 1) 𝔪 v.μ φ c → 2 * Real.exp (Q + (6 * (V.rank : ℝ) + 9) * Fintype.card D.what₂.Tau) ≤ s ^ Fintype.card D.what₂.Tau * Real.sqrt (Ideal.absNorm 𝔪) → 1 < s ^ Fintype.card D.what₂.Tau * Real.sqrt (Ideal.absNorm 𝔪) → ∫ h in v.𝓕, poin θ M (congLev D.sp.cm V.gram (d.lat Λ fun _ => 1) 𝔪) (p.v θ) (stabilizerEmbedding d x⁻¹) (p.v θ) (stabilizerEmbedding d h) * φ h ∂v.μ ≠ 0 := by
  intro D θ hθ Y V d S S' M₀ M p Q hbase Λ 𝔪 hΛ h𝔪 v φ c b s x hφ hbnd hx hs0 hs1 hlong had hR2 hR1
  classical
  obtain ⟨ι, hι, hιc, hιi, hιQ, -, -, hιr, -, -⟩ := GlobalTheory.T.exists_unitary_embedding_stabilizer D θ hθ Y V 1 1 one_ne_zero d
  haveI : Countable (GQ V) := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.countableGamma D.sp.cm.sig V.gram
  haveI := v.haar
  set K := congLev D.sp.cm V.gram (d.lat Λ fun _ => 1) 𝔪 with hK
  set f : GA D V → ℂ := fun g => coef θ M K (p.v θ) (p.v θ) (stabilizerEmbedding d x⁻¹ * g) with hf
  have hcoef : Measurable (coef θ M K (p.v θ) (p.v θ)) := by
    have h1 := GlobalTheory.T.continuous_realPlacesMatrixCoefficientProduct D θ hθ V S M (p.v θ) (p.v θ)
    have h2 := GlobalTheory.T.isOpen_congruence_embedding D Y V d Λ 𝔪 hΛ h𝔪
    unfold coef
    exact Measurable.ite h2.measurableSet h1.measurable measurable_const
  have hfm : ∀ γ : GA D V, Measurable fun h => f (γ * ι h) := fun γ =>
    hcoef.comp (continuous_const.mul (continuous_const.mul hιc)).measurable
  have hcomap : (GQ V).comap ι = GQ Y := by ext h; simp [Subgroup.mem_comap, hιQ]
  have hfund : IsFundamentalDomain ((GQ V).comap ι) v.𝓕 v.μ := by rw [hcomap]; exact v.fund
  have hinv : ∀ γ ∈ (GQ V).comap ι, ∀ h, φ (γ * h) = φ h := fun γ hγ h =>
    hφ.1 γ (by rw [← hcomap]; exact hγ) h
  have hb0 : 0 ≤ b := (norm_nonneg _).trans (hbnd x)
  have hV1 : 1 ≤ V.rank := by have := d.rank; omega
  obtain ⟨hlongV, hz₀, hz1⟩ := GlobalTheory.T.long_element_embedding_norm D θ hθ Y V d p.A p.B hbase.adapted Λ x s hΛ hs0 hs1 hlong
  choose z hz using fun q : GQ V ⧸ ι.range.subgroupOf (GQ V) => GlobalTheory.T.exists_rational_image_rationalPoint_mulVec D V _ (q.out).2 (zv d)
  have hterm : ∀ q : GQ V ⧸ ι.range.subgroupOf (GQ V),
      Integrable (fun h => f ((q.out : GA D V) * ι h)) v.μ ∧
      (∫ h, ‖f ((q.out : GA D V) * ι h)‖ ∂v.μ) * (∏ τ, nrm θ p.B (stabilizerEmbedding d x) τ (z q)) ^ (2 * V.rank + 5) ≤
        Real.exp Q * ‖c‖ ∧
      (z q - zv d ∉ 𝔪 • latAt (d.lat Λ fun _ => 1) (stabilizerEmbedding d x) → ∀ h, f ((q.out : GA D V) * ι h) = 0) := by
    intro q
    have := had.term x _ (z q) (q.out).2 (hz q)
    simpa only [hf, hι, mul_assoc] using this
  have hmtm : ∀ a a' : GA D V, mt V (a * a') = mt V a * mt V a' := fun a a' => by simp [Formalism.L2.Theta.mt]
  have hmt1 : mt V 1 = 1 := by simp [Formalism.L2.Theta.mt]
  have hfix : ∀ g : GA D V, mt V g *ᵥ ratV (zv d) = ratV (zv d) → g ∈ ι.range := by
    intro g hg
    rw [hιr]
    ext i j
    have hj : j = 0 := Subsingleton.elim _ _
    subst hj
    have := congrFun hg i
    simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct, ratV, zv] using this
  have hcos : ∀ q q' : GQ V ⧸ ι.range.subgroupOf (GQ V),
      ((q.out : GA D V))⁻¹ * (q'.out : GA D V) ∈ ι.range → q = q' := by
    intro q q' h
    rw [← QuotientGroup.out_eq' q, ← QuotientGroup.out_eq' q', QuotientGroup.eq, Subgroup.mem_subgroupOf]
    simpa using h
  have hinj : ∀ q q', z q = z q' → q = q' := by
    intro q q' h
    refine hcos q q' (hfix _ ?_)
    rw [hmtm, ← Matrix.mulVec_mulVec, hz q', ← h, ← hz q, Matrix.mulVec_mulVec, ← hmtm, inv_mul_cancel, hmt1,
      Matrix.one_mulVec]
  set q₁ : GQ V ⧸ ι.range.subgroupOf (GQ V) := ((1 : GQ V) : GQ V ⧸ ι.range.subgroupOf (GQ V)) with hq₁
  have hq1 : ∀ q, z q = zv d → q = q₁ := by
    intro q h
    rw [← QuotientGroup.out_eq' q, hq₁, QuotientGroup.eq, Subgroup.mem_subgroupOf]
    simpa using hfix _ (by rw [hz, h])

  have hTle : ∀ q : GQ V ⧸ ι.range.subgroupOf (GQ V), ‖∫ h, f ((q.out : GA D V) * ι h) * φ h ∂v.μ‖ ≤
      b * ∫ h, ‖f ((q.out : GA D V) * ι h)‖ ∂v.μ := by
    intro q
    refine (norm_integral_le_integral_norm _).trans ?_
    rw [← integral_const_mul]
    refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun h => norm_nonneg _)
      ((hterm q).1.norm.const_mul b) (Filter.Eventually.of_forall fun h => ?_)
    dsimp only
    rw [norm_mul, mul_comm b]
    exact mul_le_mul_of_nonneg_left (hbnd h) (norm_nonneg _)
  have hLle : ∀ q : GQ V ⧸ ι.range.subgroupOf (GQ V), ∫⁻ h, ‖f ((q.out : GA D V) * ι h) * φ h‖ₑ ∂v.μ ≤
      ENNReal.ofReal (b * ∫ h, ‖f ((q.out : GA D V) * ι h)‖ ∂v.μ) := by
    intro q
    rw [← integral_const_mul, ofReal_integral_eq_lintegral_ofReal ((hterm q).1.norm.const_mul b)
      (Filter.Eventually.of_forall fun h => mul_nonneg hb0 (norm_nonneg _))]
    refine lintegral_mono fun h => ?_
    rw [← ofReal_norm_eq_enorm]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [norm_mul, mul_comm b]
    exact mul_le_mul_of_nonneg_left (hbnd h) (norm_nonneg _)
  set β : (GQ V ⧸ ι.range.subgroupOf (GQ V)) → ℝ := fun q => b * ∫ h, ‖f ((q.out : GA D V) * ι h)‖ ∂v.μ with hβ
  have hβ0 : ∀ q, 0 ≤ β q := fun q => mul_nonneg hb0 (integral_nonneg fun _ => norm_nonneg _)
  have hβle : ∀ q, β q ≤ b * (Real.exp Q * ‖c‖) := by
    intro q
    refine mul_le_mul_of_nonneg_left ?_ hb0
    have hP : 1 ≤ ∏ τ, nrm θ p.B (stabilizerEmbedding d x) τ (z q) := by
      simpa using Finset.prod_le_prod (s := Finset.univ) (f := fun _ => (1 : ℝ)) (fun _ _ => zero_le_one)
        (fun τ _ => hz1 _ (z q) (q.out).2 (hz q) τ)
    exact (le_mul_of_one_le_right (integral_nonneg fun _ => norm_nonneg _) (one_le_pow₀ hP)).trans (hterm q).2.1

  obtain ⟨R, hRdef⟩ : ∃ R : ℝ, R = s ^ Fintype.card D.what₂.Tau * Real.sqrt (Ideal.absNorm 𝔪) := ⟨_, rfl⟩
  obtain ⟨Kx, hKx⟩ : ∃ Kx : ℝ, Kx = (6 * (V.rank : ℝ) + 9) * Fintype.card D.what₂.Tau := ⟨_, rfl⟩
  obtain ⟨Bt, hBt⟩ : ∃ Bt : ℝ, Bt = b * (Real.exp Q * ‖c‖) * (Real.exp Kx / R) := ⟨_, rfl⟩
  rw [← hRdef] at hR1 hR2
  rw [← hKx] at hR2
  have htail : ∀ t : Finset (GQ V ⧸ ι.range.subgroupOf (GQ V)), ∑ q ∈ t.erase q₁, β q ≤ Bt := by
    intro t
    obtain ⟨L, hL⟩ : ∃ L : Lat V, L = 𝔪 • latAt (d.lat Λ fun _ => 1) (stabilizerEmbedding d x) := ⟨_, rfl⟩
    obtain ⟨w, hw⟩ : ∃ w : (GQ V ⧸ ι.range.subgroupOf (GQ V)) → (Fin V.rank → D.host.E), w = fun q => z q - zv d :=
      ⟨_, rfl⟩
    have hwq : ∀ q, w q = z q - zv d := fun q => by rw [hw]
    obtain ⟨t', ht'⟩ : ∃ t' : Finset (GQ V ⧸ ι.range.subgroupOf (GQ V)), t' = (t.erase q₁).filter (fun q => w q ∈ L) :=
      ⟨_, rfl⟩
    have h1 : ∑ q ∈ t.erase q₁, β q = ∑ q ∈ t', β q := by
      rw [ht']
      refine (Finset.sum_filter_of_ne fun q _ hq => ?_).symm
      by_contra hL'
      apply hq
      have h0 := (hterm q).2.2 (fun h => hL' (by rw [hwq, hL]; exact h))
      simp [hβ, h0]
    have h2 : ∀ q ∈ t', β q ≤ b * (Real.exp Q * ‖c‖) *
        ∏ τ, (((1 + nrm θ p.B (stabilizerEmbedding d x) τ (w q)) / 3) ^ (2 * V.rank + 5))⁻¹ := by
      intro q _
      have hτ : ∀ τ, (1 + nrm θ p.B (stabilizerEmbedding d x) τ (w q)) / 3 ≤ nrm θ p.B (stabilizerEmbedding d x) τ (z q) := by
        intro τ
        have a1 := nrm_sub_le θ p.B (stabilizerEmbedding d x) τ (z q) (zv d)
        have a2 := hz1 _ (z q) (q.out).2 (hz q) τ
        rw [hz₀ τ] at a1
        rw [hwq]
        linarith
      have hP' : 0 < ∏ τ, (1 + nrm θ p.B (stabilizerEmbedding d x) τ (w q)) / 3 :=
        Finset.prod_pos fun τ _ => by have := nrm_nonneg' θ p.B (stabilizerEmbedding d x) τ (w q); positivity
      have hPP : ∏ τ, (1 + nrm θ p.B (stabilizerEmbedding d x) τ (w q)) / 3 ≤ ∏ τ, nrm θ p.B (stabilizerEmbedding d x) τ (z q) :=
        Finset.prod_le_prod (fun τ _ => by have := nrm_nonneg' θ p.B (stabilizerEmbedding d x) τ (w q); positivity) fun τ _ => hτ τ
      have ha := (hterm q).2.1
      have ha0 : 0 ≤ ∫ h, ‖f ((q.out : GA D V) * ι h)‖ ∂v.μ := integral_nonneg fun _ => norm_nonneg _
      rw [Finset.prod_inv_distrib, Finset.prod_pow, mul_assoc]
      refine mul_le_mul_of_nonneg_left ?_ hb0
      rw [← div_eq_mul_inv, le_div_iff₀ (pow_pos hP' _)]
      exact (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hP'.le hPP _) ha0).trans ha
    have hw_inj : Set.InjOn w t' := by
      intro q _ q' _ h
      exact hinj q q' (sub_left_inj.1 (by rwa [hwq, hwq] at h))
    have hws : ∀ y ∈ t'.image w, y ∈ L ∧ y ≠ 0 := by
      intro y hy
      obtain ⟨q, hq, rfl⟩ := Finset.mem_image.1 hy
      rw [ht', Finset.mem_filter, Finset.mem_erase] at hq
      exact ⟨hq.2, fun h0 => hq.1.1 (hq1 q (sub_eq_zero.1 (by rwa [hwq] at h0)))⟩
    have hsum := GlobalTheory.T.latticeSum_longVectors_decayWeight_le D θ V p.B (stabilizerEmbedding d x) L R hV1 hR1 (fun y hy hy0 => hRdef ▸ hlongV 𝔪 h𝔪 y (hL ▸ hy) hy0) (t'.image w) hws
    rw [← hKx] at hsum
    calc ∑ q ∈ t.erase q₁, β q = ∑ q ∈ t', β q := h1
      _ ≤ ∑ q ∈ t', b * (Real.exp Q * ‖c‖) * ∏ τ, (((1 + nrm θ p.B (stabilizerEmbedding d x) τ (w q)) / 3) ^ (2 * V.rank + 5))⁻¹ :=
        Finset.sum_le_sum h2
      _ = b * (Real.exp Q * ‖c‖) * ∑ y ∈ t'.image w, ∏ τ, (((1 + nrm θ p.B (stabilizerEmbedding d x) τ y) / 3) ^ (2 * V.rank + 5))⁻¹ := by
        rw [Finset.sum_image hw_inj, Finset.mul_sum]
      _ ≤ Bt := by rw [hBt]; exact mul_le_mul_of_nonneg_left hsum (by positivity)

  have hall : ∀ t : Finset (GQ V ⧸ ι.range.subgroupOf (GQ V)), ∑ q ∈ t, β q ≤ b * (Real.exp Q * ‖c‖) + Bt := by
    intro t
    calc ∑ q ∈ t, β q ≤ ∑ q ∈ insert q₁ t, β q :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_insert _ _) fun q _ _ => hβ0 q
      _ = β q₁ + ∑ q ∈ (insert q₁ t).erase q₁, β q := (Finset.add_sum_erase _ _ (Finset.mem_insert_self _ _)).symm
      _ ≤ _ := add_le_add (hβle q₁) (htail _)
  have hβs : Summable β := summable_of_sum_le hβ0 hall
  have hfin : (∑' q : GQ V ⧸ ι.range.subgroupOf (GQ V), ∫⁻ h, ‖f ((q.out : GQ V) * ι h) * φ h‖ₑ ∂v.μ) ≠ ⊤ := by
    have h1 : (∑' q : GQ V ⧸ ι.range.subgroupOf (GQ V), ∫⁻ h, ‖f ((q.out : GQ V) * ι h) * φ h‖ₑ ∂v.μ) ≤
        ∑' q, ENNReal.ofReal (β q) := ENNReal.tsum_le_tsum hLle
    have h2 : (∑' q, ENNReal.ofReal (β q)) = ENNReal.ofReal (∑' q, β q) := (ENNReal.ofReal_tsum_of_nonneg hβ0 hβs).symm
    exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top (h1.trans h2.le)
  have hU := GlobalTheory.T.integrableOn_and_hasSum_tsum_subgroup (GA D V) (GA D Y) v.μ ι hιi (GQ V) v.𝓕 hfund f φ hfm hφ.2.measurable hinv hfin
  have htarget : (∫ h in v.𝓕, poin θ M K (p.v θ) (stabilizerEmbedding d x⁻¹) (p.v θ) (stabilizerEmbedding d h) * φ h ∂v.μ) =
      ∫ h in v.𝓕, (∑' γ : GQ V, f (γ * ι h)) * φ h ∂v.μ := by
    congr 1; funext h; simp only [poin, hf, hι, mul_assoc]
  have h1r : ((q₁.out : GQ V) : GA D V) ∈ ι.range := by
    have := QuotientGroup.out_eq' q₁
    rw [hq₁, QuotientGroup.eq, Subgroup.mem_subgroupOf] at this
    simpa using this
  obtain ⟨h₀, hh₀⟩ := h1r
  have hh₀Q : h₀ ∈ GQ Y := (hιQ h₀).1 (hh₀ ▸ (q₁.out).2)
  have hT1 : ∫ h, f ((q₁.out : GA D V) * ι h) * φ h ∂v.μ = c * φ x := by
    rw [← hh₀, ← had.one x]
    have e : (fun h => f (ι h₀ * ι h) * φ h) = fun h =>
        (fun h' => coef θ M K (p.v θ) (p.v θ) (stabilizerEmbedding d x⁻¹ * stabilizerEmbedding d h') * φ h') (h₀ * h) := by
      funext h
      show f (ι h₀ * ι h) * φ h = coef θ M K (p.v θ) (p.v θ) (stabilizerEmbedding d x⁻¹ * stabilizerEmbedding d (h₀ * h)) * φ (h₀ * h)
      rw [← map_mul, hφ.1 h₀ hh₀Q h]
      simp only [hf, hι]
    rw [e]
    exact integral_mul_left_eq_self (μ := v.μ)
      (fun h' => coef θ M K (p.v θ) (p.v θ) (stabilizerEmbedding d x⁻¹ * stabilizerEmbedding d h') * φ h') h₀
  rw [htarget]
  intro hI0
  have hH' := hU.2.update q₁ 0
  have hβ's : Summable (Function.update β q₁ 0) := hβs.update q₁ 0
  have hnorm := hH'.norm_le_of_bounded hβ's.hasSum (fun q => by
    by_cases hq : q = q₁
    · subst hq; simp
    · simp only [Function.update_apply, hq, if_false]; exact hTle q)
  have hts : ∑' q, Function.update β q₁ 0 q ≤ Bt := by
    refine hβ's.tsum_le_of_sum_le fun t => ?_
    rw [← Finset.sum_erase t (a := q₁) (by simp)]
    calc _ = ∑ q ∈ t.erase q₁, β q := Finset.sum_congr rfl fun q hq => by
            simp [Function.update_apply, Finset.ne_of_mem_erase hq]
      _ ≤ Bt := htail t
  rw [hI0, add_zero, zero_sub, norm_neg, hT1, norm_mul] at hnorm
  have hRpos : 0 < R := by linarith
  have hq' : Real.exp Q * Real.exp Kx / R ≤ 1 / 2 := by
    rw [div_le_iff₀ hRpos, ← Real.exp_add]; linarith
  have hBt : Bt ≤ b * ‖c‖ / 2 := by
    calc Bt = (b * ‖c‖) * (Real.exp Q * Real.exp Kx / R) := by rw [hBt]; ring
      _ ≤ (b * ‖c‖) * (1 / 2) := mul_le_mul_of_nonneg_left hq' (by positivity)
      _ = _ := by ring
  have hc0 : 0 < ‖c‖ := norm_pos_iff.2 had.ne
  have := mul_lt_mul_of_pos_left hx hc0
  nlinarith

end GlobalTheory.IdDom

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaLocalSupportIdempotentStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.theta_local_support_idempotent : ∀ {D : D7} {T : Type} [Finite T] {L : LevCh D T} {μ₀ : T} {sc : Consts} {G : GridData L sc} {W : G.Weil}
    {i j : Fin D.R.m} {A A' WW : HSp D} {X : Tri T A A' WW}, GlobalTheory.FunPr.Hypotheses₂ → (∀ D, GlobalTheory.NormSum.Inp D) → L.Is μ₀ →
    IsBottomTri W i j X → ∀ (t : T) (N : ℕ) (e : AE D) (P : Pl D.host.E), Formalism.L2.NTheta.IsIdemAt e P → ((N : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal →
    ∀ h ∈ GfC WW, Formalism.L2.Theta.SuppAt e WW h →
      GlobalTheory.MovedAlg.IsAlgComb W.ψ (GlobalTheory.Grid.neg A) WW X.vac (X.ω t (1, h) X.vac) := by
  first | exact @GlobalTheory.SplitVacAlg.split_algComb | exact GlobalTheory.SplitVacAlg.split_algComb | (intros; apply GlobalTheory.SplitVacAlg.split_algComb <;> assumption)
end

