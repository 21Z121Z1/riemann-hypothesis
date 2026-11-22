import Mathlib
import Formalism.LocalToGlobal.CharacterGerms.Bundle0006
import Formalism.LocalToGlobal.CharacterGerms.CartesianBoundOnCurves
import Formalism.LocalToGlobal.CharacterGerms.CoeffIterateZero
import Formalism.FrobeniusBaseCase.FrobeniusBaseCaseProofs.Bundle0001
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.TwoMulChainStartIndexAddOneOfOdd
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle0026
import ReciprocityTheory.DualLattices.Bundle0026
import ReciprocityTheory.DualLattices.Bundle0015
import ReciprocityTheory.DualLattices.SubMemOfCompat
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.UniversalCharts.LePreimageOfNil
import ReciprocityTheory.DualLattices.Bundle0031
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle0020
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ModPToValuationResidueFieldSurjective
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle0018
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle0025
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle0024
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle0019
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle0023
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ExistsTateMatricesLink
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle0022
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ExistsFormalChart
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle0021
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.FinOfLocalAlgebraMap
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle0013
import Formalism.LocalToGlobal.CharacterGerms.RowTieFB

-- bundled from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.CoeffCoordinatesGoodTangentsLtSq
section
open Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds GlobalTheory.MainTerm Classical
open Formalism.BaseCaseIdentities (OrdGE)

noncomputable section

namespace GlobalTheory.MainTerm

theorem sum_pow_trunc_lt_sq {C : Type} [Field C] {I ι : Type} [Fintype I] {l : ℕ} (hl : 2 ≤ l)
    (T : I → MvPowerSeries ι C) (hT : ∀ c, OrdGE 1 (T c)) (f : I → ℕ → C) (μ : ι →₀ ℕ)
    (hμ : μ.degree < l ^ 2) :
    ∑ s ∈ Finset.range (μ.degree + 1), ∑ c, f c s * MvPowerSeries.coeff μ (T c ^ (l ^ s)) =
      ∑ c, f c 0 * MvPowerSeries.coeff μ (T c) + ∑ c, f c 1 * MvPowerSeries.coeff μ (T c ^ l) := by
  have h1 : ∑ s ∈ Finset.range (μ.degree + 1), ∑ c, f c s * MvPowerSeries.coeff μ (T c ^ (l ^ s)) =
      ∑ s ∈ Finset.range (μ.degree + 1 + 1), ∑ c, f c s * MvPowerSeries.coeff μ (T c ^ (l ^ s)) := by
    rw [Finset.sum_range_succ _ (μ.degree + 1), Finset.sum_eq_zero (s := Finset.univ), add_zero]
    intro c _
    rw [(hT c).pow _ μ ((Nat.lt_succ_self _).trans (Nat.lt_pow_self (by omega))), mul_zero]
  rw [h1, Finset.sum_range_succ', Finset.sum_range_succ', Finset.sum_eq_zero, zero_add, add_comm]
  · simp
  · intro s _
    refine Finset.sum_eq_zero fun c _ => ?_
    rw [(hT c).pow _ μ (hμ.trans_le (Nat.pow_le_pow_right (by omega) (by omega))), mul_zero]

theorem ordGE_one_of_constantCoeff {C : Type} [Field C] {ι : Type} {F : MvPowerSeries ι C}
    (h : MvPowerSeries.constantCoeff F = 0) : OrdGE 1 F := by
  intro A hA
  have : A = 0 := (Finsupp.degree_eq_zero_iff A).1 (by omega)
  subst this
  simpa using h

theorem sum_coeff_pow_ite {C : Type} [Field C] {I : Type} [Fintype I] {N : ℕ} (em : Fin N ↪ I)
    (g : I → C) {n : ℕ} (hn : n ≠ 0) (μ : Fin N →₀ ℕ) :
    ∑ c, g c * MvPowerSeries.coeff μ
        ((∑ δ : Fin N, if em δ = c then (MvPowerSeries.X δ : MvPowerSeries (Fin N) C) else 0) ^ n) =
      ∑ δ : Fin N, g (em δ) * MvPowerSeries.coeff μ ((MvPowerSeries.X δ : MvPowerSeries (Fin N) C) ^ n) := by
  rw [← Finset.sum_subset (Finset.subset_univ (Finset.univ.map em)), Finset.sum_map]
  · refine Finset.sum_congr rfl fun δ _ => ?_
    simp
  · intro c _ hc
    have h : ∀ δ, em δ ≠ c := fun δ h => hc (Finset.mem_map.2 ⟨δ, Finset.mem_univ _, h⟩)
    simp [h, hn]

theorem coeff_low_good : ∀ (C : Type) [Field C] (V : VF C) (d : ℕ) (I J : Type) [Fintype I] [Fintype J] (G : Cart V d I J) (S : Sys G) (t : I → MvPowerSeries I C), S.IsT t → ∀ (N : ℕ) (em : Fin N ↪ I), (∀ δ x, S.al (em δ) 1 x = 0) → ∀ μ : Fin N →₀ ℕ, μ.degree < V.l ^ 2 → (∀ c, MvPowerSeries.coeff μ (linPull (fun δ => S.tan (em δ)) (t c)) = MvPowerSeries.coeff μ (∑ δ : Fin N, if em δ = c then (MvPowerSeries.X δ : MvPowerSeries (Fin N) C) else 0)) ∧ ∀ κ : J, MvPowerSeries.coeff μ (linPull (fun δ => S.tan (em δ)) (S.ze t κ)) = MvPowerSeries.coeff μ (-∑ δ : Fin N, S.be (em δ) 1 κ • (MvPowerSeries.X δ : MvPowerSeries (Fin N) C) ^ V.l) := by
  intro C _ V d I J _ _ G S t ht N em hem
  have hl : 2 ≤ V.l := V.l_prime.two_le
  let al : I → ℕ → I → C := fun c k b =>
    if k = 0 then (if c = b then 1 else 0) else S.co (S.cur c k) b
  obtain ⟨h0, h1, h2⟩ := GlobalTheory.T.formalGroupCoordinates_pullback_linear_tangentBasis C V d I J G S t ht (Fin N) (fun δ => S.tan (em δ))
    (fun b j => if em j = b then 1 else 0) al
    (by intro j x; simp)
    (by intro c b; simp [al])
    (by
      intro c k x hk
      have hk' : k ≠ 0 := by omega
      simp only [al, hk', if_false, Sys.al, S.cur_zero_inl]
      exact (S.co_spec (S.cur c k) x).symm)
  set T : I → MvPowerSeries (Fin N) C := fun c => linPull (fun δ => S.tan (em δ)) (t c) with hTdef
  set z : I → MvPowerSeries (Fin N) C := fun c =>
    ∑ δ : Fin N, if em δ = c then (MvPowerSeries.X δ : MvPowerSeries (Fin N) C) else 0 with hz
  have hT : ∀ c, OrdGE 1 (T c) := fun c => ordGE_one_of_constantCoeff (h0 c)
  have hz1 : ∀ c, OrdGE 1 (z c) := fun c => by
    refine OrdGE.sum _ fun δ _ => ?_
    split_ifs
    · exact OrdGE.X δ
    · exact OrdGE.zero
  have hal1 : ∀ δ b, al (em δ) 1 b = 0 := fun δ b => by
    have : ∀ x, S.cur (em δ) 1 (Sum.inl x) = 0 := hem δ
    simp [al, Sys.co, this]
  have key : ∀ D, D + 1 ≤ V.l ^ 2 → ∀ c, OrdGE (D + 1) (T c - z c) := by
    intro D
    induction D with
    | zero => exact fun _ c => (hT c).sub (hz1 c)
    | succ D ih =>
      intro hD b A hA
      have e := h1 b A
      have e2 := sum_pow_trunc_lt_sq hl T hT (fun c s => al c s b) A (by omega)
      rw [e2] at e
      have e3 : ∀ c, MvPowerSeries.coeff A (T c ^ V.l) = MvPowerSeries.coeff A (z c ^ V.l) := fun c => by
        have := OrdGE.pow_sub_pow (hT c) (hz1 c) (ih (by omega) c) (N := V.l) (by omega) A (by omega)
        rwa [map_sub, sub_eq_zero] at this
      have e4 : ∑ c, al c 1 b * MvPowerSeries.coeff A (T c ^ V.l) = 0 := by
        simp only [e3, hz]
        rw [sum_coeff_pow_ite em (fun c => al c 1 b) (by omega)]
        simp [hal1]
      rw [e4, add_zero] at e
      rw [map_sub, sub_eq_zero]
      have e5 : ∑ c, al c 0 b * MvPowerSeries.coeff A (T c) = MvPowerSeries.coeff A (T b) := by
        simp [al]
      rw [← e5, e]
      congr 1
      refine Finset.sum_congr rfl fun δ _ => ?_
      split_ifs <;> simp
  intro μ hμ
  refine ⟨fun c => ?_, fun κ => ?_⟩
  · have := key μ.degree hμ c μ (Nat.lt_succ_self _)
    rwa [map_sub, sub_eq_zero] at this
  · have e2 := sum_pow_trunc_lt_sq hl T hT (fun c s => S.be c s κ) μ hμ
    have e3 : ∀ c, MvPowerSeries.coeff μ (T c ^ V.l) = MvPowerSeries.coeff μ (z c ^ V.l) := fun c => by
      have := OrdGE.pow_sub_pow (hT c) (hz1 c) (key μ.degree hμ c) (N := V.l) (by omega) μ (by omega)
      rwa [map_sub, sub_eq_zero] at this
    rw [h2 κ μ, e2]
    simp only [e3, hz]
    rw [sum_coeff_pow_ite em (fun c => S.be c 1 κ) (by omega)]
    simp [Sys.be, S.be_zero]

end GlobalTheory.MainTerm
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ExistsCompatibleBasis
section
open TensorProduct IsLocalRing Matrix CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Be2 ReciprocityTheory.ChartRestriction.G.Chart
open scoped CategoryTheory.Obj CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.PeriodDatum

theorem exists_basis_of_card (p : ℕ) [hp : Fact p.Prime] (g : ℕ) (V : Type) [AddCommGroup V]
    [Module (ZMod p) V] (hcV : Nat.card V = p ^ (2 * g)) :
    ∃ f : Ix g → V, ∀ x : V, ∃! t : Ix g → ZMod p, x = ∑ j, (t j).val • f j := by
  haveI : Finite V := Nat.finite_of_card_ne_zero (by rw [hcV]; exact pow_ne_zero _ hp.out.ne_zero)
  haveI : Module.Finite (ZMod p) V := Module.Finite.of_finite
  have hrk : Module.finrank (ZMod p) V = Fintype.card (Ix g) := by
    have h := Module.natCard_eq_pow_finrank (K := ZMod p) (V := V)
    rw [hcV, Nat.card_zmod] at h
    have h2 := Nat.pow_right_injective hp.out.two_le h
    rw [← h2, Fintype.card_sum, Fintype.card_fin, two_mul]
  let b : Module.Basis (Ix g) (ZMod p) V :=
    (Module.finBasisOfFinrankEq (ZMod p) V hrk).reindex (Fintype.equivFin (Ix g)).symm
  have hsm : ∀ (t : ZMod p) (y : V), t.val • y = t • y := fun t y => by
    rw [← Nat.cast_smul_eq_nsmul (ZMod p), ZMod.natCast_zmod_val]
  refine ⟨b, fun x => ⟨b.equivFun x, ?_, fun t ht => ?_⟩⟩
  · simp only [hsm]
    rw [← b.equivFun_symm_apply, LinearEquiv.symm_apply_apply]
  · simp only [hsm] at ht
    rw [← b.equivFun_symm_apply] at ht
    rw [ht, LinearEquiv.apply_symm_apply]

theorem exists_compatible_basis (p : ℕ) [hp : Fact p.Prime] (g : ℕ) (Γ : Type) [AddCommGroup Γ]
    (hdiv : ∀ x : Γ, ∃ y, p • y = x) (hcard : Nat.card {x : Γ // p • x = 0} = p ^ (2 * g)) :
    ∃ τ : Ix g → ℕ → Γ, (∀ i n, (p ^ (n + 1)) • τ i n = 0) ∧ (∀ i n, τ i n = p • τ i (n + 1)) ∧
      ∀ x : Γ, p • x = 0 → ∃! t : Ix g → ZMod p, x = ∑ j, (t j).val • τ j 0 := by
  obtain ⟨V, hV⟩ : ∃ V : AddSubgroup Γ, ∀ x : Γ, x ∈ V ↔ p • x = 0 :=
    ⟨(nsmulAddMonoidHom p : Γ →+ Γ).ker, fun x => Iff.rfl⟩
  have hcV : Nat.card V = p ^ (2 * g) :=
    (Nat.card_congr (Equiv.subtypeEquivRight hV)).trans hcard
  obtain ⟨b, hb⟩ := @exists_basis_of_card p _ g V _
    (AddCommGroup.zmodModule (fun x => Subtype.ext ((hV _).1 x.2))) hcV
  choose d hd using hdiv
  let τ : Ix g → ℕ → Γ := fun i n => d^[n] (b i : Γ)
  have hτp : ∀ i n, τ i n = p • τ i (n + 1) := fun i n => by
    simp only [τ, Function.iterate_succ_apply', hd]
  have hsum : ∀ t : Ix g → ZMod p, ((∑ j, (t j).val • b j : V) : Γ) = ∑ j, (t j).val • τ j 0 :=
    fun t => by
      rw [AddSubmonoidClass.coe_finset_sum]
      rfl
  refine ⟨τ, fun i n => ?_, hτp, fun x hx => ?_⟩
  · induction n with
    | zero => rw [zero_add, pow_one]; exact (hV _).1 (b i).2
    | succ n ih => rw [pow_succ, mul_smul, ← hτp i n, ih]
  · obtain ⟨t, ht, hu⟩ := hb ⟨x, (hV x).2 hx⟩
    refine ⟨t, ?_, fun t' ht' => hu t' (Subtype.ext ?_)⟩
    · exact (congrArg Subtype.val ht).trans (hsum t)
    · exact ht'.trans (hsum t').symm

theorem main :
  (∀ (p : ℕ) [Fact p.Prime] {C : Type} [Field C] [IsAlgClosed C] [CharZero C] {v : Valuation C NNReal} (O : Type) [CommRing O] [Algebra O C]
    [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] (hv : v.Integers O) (ε : PreTilt O p)
    (hε : IsPrimitiveRoot (((frobeniusEquiv (PreTilt O p) p).symm ε).untilt) p) (g : ℕ)
    (G : Over (Spec (CommRingCat.of (Ainf.R0 p O ε)))) [GrpObj G] [IsCommMonObj G] (B : BX (Ainf.R0 p O ε))
    (e : ∀ R : LAlg (Ainf.R0 p O ε), B.G R → (sp (R₀ := (Ainf.R0 p O ε)) (R : Type) ⟶ G)), (∀ R, Function.Bijective (e R)) → (∀ R x y, e R (x + y) = e R x * e R y) →
    (∀ {R S : LAlg (Ainf.R0 p O ε)} (f : LHom R S) (x : B.G R), e S (B.map f x) = spMap f.1 ≫ e R x) →
    SmoothOfRelativeDimension g G.hom → IsFinite ((𝟙 G) ^ p : G ⟶ G).left → Flat ((𝟙 G) ^ p : G ⟶ G).left →
    (∀ x : B.G (Ainf.ainfTowerL p O hv ε hε).O, ∃ y, p • y = x) → Nat.card {x : B.G (Ainf.ainfTowerL p O hv ε hε).O // p • x = 0} = p ^ (2 * g) →
    (∀ x : B.G (Ainf.ainfTowerL p O hv ε hε).O, p • x = 0 → (∀ y : B.G (Ainf.ainfTowerL p O hv ε hε).O, p • y = 0 → B.IsPairing p x y 1) → x = 0) →
    ∀ [Algebra ℤ_[p] ((Ainf.ainfTowerL p O hv ε hε).O : Type)] (O₀ : Type) [CommRing O₀] (cj : O₀ ≃ₐ[ℤ] O₀) (Ad : O₀ → OAdj B (Ainf.ainfTowerL p O hv ε hε).O),
    (∀ a, (Ad a).ab = (Ad (cj a)).a) → (∀ a, cj (cj a) = a) →
    (∀ {R : LAlg (Ainf.R0 p O ε)} (s : LHom (Ainf.ainfTowerL p O hv ε hε).O R) (x : B.G R), (Ad 1).a.f s x = x ∧ ∀ a b, (Ad (a + b)).a.f s x = (Ad a).a.f s x + (Ad b).a.f s x ∧
      (Ad (a * b)).a.f s x = (Ad a).a.f s ((Ad b).a.f s x)) →
    ∃ (Dt : DualTower (Ainf.ainfTowerL p O hv ε hε)) (D : Dat p g B (Ainf.ainfTowerL p O hv ε hε) Dt (ℤ_[p] ⊗[ℤ] O₀) (Algebra.TensorProduct.congr (AlgEquiv.refl : ℤ_[p] ≃ₐ[ℤ_[p]] ℤ_[p]) cj) (Ainf.ainfTowerL p O hv ε hε).c),
      D.H.P = 0 ∧ D.H.PL = 0 ∧
      (∀ a {R S : LAlg (Ainf.R0 p O ε)} (s : LHom (Ainf.ainfTowerL p O hv ε hε).O R) (π : LHom R S) (hπ : π.SqZero) (l : Fin g) (i : π.ker) (m : Fin g → π.ker),
      (∀ k, (m k : (R : Type)) = s.1 (D.H.ρL (1 ⊗ₜ[ℤ] a) k l) * i) →
      (Ad a).a.f s (B.tg π hπ (D.ch.gb l ⊗ₜ[(Ainf.R0 p O ε)] i)) = B.tg π hπ (∑ k, D.ch.gb k ⊗ₜ[(Ainf.R0 p O ε)] m k)) ∧
      ∀ a j n, (Ad a).a.f (LHom.id (Ainf.ainfTowerL p O hv ε hε).O) (D.L.τ j n) = ∑ k, (PadicInt.toZModPow (n + 1) (D.H.ρ (1 ⊗ₜ[ℤ] a) k j)).val • D.L.τ k n) := by
  intro p _ C _ _ _ v O _ _ _ _ hv ε hε g G _ _ B e hbij hadd hnat hsm hfin hflat hdiv hcard hperf
    _ O₀ _ cj Ad hab hcj hAd
  haveI : IsLocalRing (Ainf.R0 p O ε) := WdAinf.ainf_thetaQuotRing_isLocalRing p O hv ε hε
  haveI : IsDomain ((Ainf.ainfTowerL p O hv ε hε).O : Type) := Ainf.ainfTower_isDomain p O hv ε hε
  have hsm' : Smooth G.hom := SmoothOfRelativeDimension.smooth g G.hom
  obtain ⟨K, wd, hnil, hK, hKl⟩ :=
    GlobalTheory.wData_ainfTower_exists GlobalTheory.WittQuot.teichmuller_quot p O hv ε hε
  obtain ⟨ch⟩ := GlobalTheory.FormalChartOf.exists_formalChart GlobalTheory.NilCoord.nilpotent_coordinates
    (GlobalTheory.ChLaw.groupLaw_powerSeries GlobalTheory.nEval_basic
      (GlobalTheory.exists_series_of_natural_on_nilpotent GlobalTheory.nEval_basic))
    G g B e hbij hadd hnat hsm K hK hKl
  have sm := GlobalTheory.SmoothNilLift.main G B e hbij hadd hnat hsm' K wd.W wd.ρW hnil
  obtain ⟨fin⟩ := @GlobalTheory.FinOf.main GlobalTheory.finRep_kernel_mul_finite_free GlobalTheory.finite_algebra_split_local
    GlobalTheory.finEtale_main _ _ G _ _ (Ainf.ainfTowerL p O hv ε hε).O p B e hbij hadd hnat hfin hflat hsm'
    C _ _ _ v (inferInstanceAs (Algebra O C)) hv (Fact.out : p.Prime).ne_zero
  obtain ⟨Dt⟩ := GlobalTheory.exists_dualTower (Ainf.ainfTowerL p O hv ε hε)
  obtain ⟨τ, hτ, hτp, hbas⟩ := exists_compatible_basis p g _ hdiv hcard
  obtain ⟨dL, hdL⟩ := GlobalTheory.exists_endDifferential_ringHom B _ ch.gb O₀ (fun a => (Ad a).a) hAd
  obtain ⟨A, H, L, hP, hPL, hL, hρL, hρ⟩ := GlobalTheory.exists_tateMatrices_link GlobalTheory.tate_basis_matrix
    GlobalTheory.tateBasis_gram GlobalTheory.PadicOrderAction.main B (Ainf.ainfTowerL p O hv ε hε) Dt ch.gb O₀ cj Ad dL
    (WdAinf.thetaBar_surj p O hv ε hε) hab hcj hAd hdL
    (fun n => Ideal.mk_ker (I := Ideal.span {(p : O) ^ (n + 1)}))
    (fun n => IsPrimitiveRoot.coe_units_iff.1 (Ainf.zeta_primitive p O hv ε hε n))
    (fun n => Units.ext (Ainf.zeta_succ_pow p O ε n))
    τ hτ hτp hbas hperf
  refine ⟨Dt,
    { K := K
      ρO := wd.ρ1.comp ((Ainf.ainfTowerL p O hv ε hε).q 0)
      ch := ch
      wd := wd
      ρO_eq := rfl
      sm := sm
      fin := fin
      A := A
      H := H
      L := L
      tower_zero_surjective := surjective_ainfTower_zero p O hv ε hε
      tower_zero_ker := ker_ainfTower_zero p O hv ε hε
      zeta0 := ainf_zeta0 p O hv ε hε }, hP, hPL, ?_, ?_⟩
  · intro a R S s π hπ l i m hm
    exact hdL a s π hπ l i m (fun k => by rw [hm k]; exact congrArg (fun M => s.1 (M k l) * (i : (R : Type))) (hρL a))
  · intro a j n
    subst hL
    exact hρ a j n

end GlobalTheory.PeriodDatum
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.FormalGroupActionLimitsIntegralEndomorphisms
section
noncomputable section

open Filter Formalism.L2.FormalSeriesBounds ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

namespace GlobalTheory.ActLimit

variable {C : Type} [Field C] {V : VF C}

def Tends (V : VF C) (s : ℕ → C) (x : C) : Prop := ∀ w : ℝ, ∀ᶠ n in atTop, V.Ge w (x - s n)

theorem exists_ge (x : C) : ∃ w : ℝ, w ≤ 0 ∧ V.Ge w x := by
  unfold VF.Ge
  induction V.v x using WithTop.recTopCoe with
  | top => exact ⟨0, le_rfl, le_top⟩
  | coe t => exact ⟨min t 0, min_le_right _ _, by exact_mod_cast min_le_left _ _⟩

theorem eq_zero_of_ge {x : C} (h : ∀ w : ℝ, V.Ge w x) : x = 0 := by
  by_contra hx
  have hv : V.v x ≠ ⊤ := by rwa [Ne, AddValuation.top_iff]
  obtain ⟨t, ht⟩ := WithTop.ne_top_iff_exists.1 hv
  have h1 := h (t + 1)
  unfold VF.Ge at h1
  rw [← ht] at h1
  have : t + 1 ≤ t := by exact_mod_cast h1
  linarith

theorem Tends.const (x : C) : Tends V (fun _ => x) x := fun w =>
  Eventually.of_forall fun _ => by simpa using VF.Ge.zero (V := V) w

theorem Tends.add {s t : ℕ → C} {x y : C} (hs : Tends V s x) (ht : Tends V t y) :
    Tends V (fun n => s n + t n) (x + y) := fun w => by
  filter_upwards [hs w, ht w] with n h1 h2
  have := h1.add h2
  rwa [show x - s n + (y - t n) = x + y - (s n + t n) by ring] at this

theorem Tends.neg {s : ℕ → C} {x : C} (hs : Tends V s x) : Tends V (fun n => -s n) (-x) := fun w => by
  filter_upwards [hs w] with n h1
  have := h1.neg
  rwa [show -(x - s n) = -x - -s n by ring] at this

theorem Tends.mul {s t : ℕ → C} {x y : C} (hs : Tends V s x) (ht : Tends V t y) :
    Tends V (fun n => s n * t n) (x * y) := fun w => by
  obtain ⟨a, -, ha⟩ := exists_ge (V := V) x
  obtain ⟨b, -, hb⟩ := exists_ge (V := V) y
  filter_upwards [hs (w - b), ht (w - a), ht b] with n h1 h2 h3
  have h4 : V.Ge b (t n) := by simpa using hb.sub h3
  have h5 : V.Ge w (x * (y - t n)) := by simpa using ha.mul h2
  have h6 : V.Ge w ((x - s n) * t n) := by simpa using h1.mul h4
  have := h5.add h6
  rwa [show x * (y - t n) + (x - s n) * t n = x * y - s n * t n by ring] at this

theorem Tends.unique {s : ℕ → C} {x y : C} (hx : Tends V s x) (hy : Tends V s y) : x = y := by
  apply sub_eq_zero.1
  refine eq_zero_of_ge (V := V) fun w => ?_
  obtain ⟨n, h1, h2⟩ := ((hx w).and (hy w)).exists
  simpa using h1.sub h2

theorem Tends.ge {s : ℕ → C} {x : C} {w : ℝ} (hx : Tends V s x) (hs : ∀ n, V.Ge w (s n)) : V.Ge w x := by
  obtain ⟨n, h1⟩ := (hx w).exists
  simpa using h1.add (hs n)

def convRing (V : VF C) : Subring ((ℕ → C) × C) where
  carrier := {p | Tends V p.1 p.2}
  mul_mem' := fun ha hb => Tends.mul ha hb
  one_mem' := Tends.const 1
  add_mem' := fun ha hb => Tends.add ha hb
  zero_mem' := Tends.const 0
  neg_mem' := fun ha => Tends.neg ha

def TendsS (V : VF C) {τ : Type} (f : ℕ → MvPowerSeries τ C) (g : MvPowerSeries τ C) : Prop :=
  ∀ μ, Tends V (fun n => MvPowerSeries.coeff μ (f n)) (MvPowerSeries.coeff μ g)

theorem TendsS.const {τ : Type} (g : MvPowerSeries τ C) : TendsS V (fun _ => g) g := fun _ => Tends.const _

theorem TendsS.sub {τ : Type} {f f' : ℕ → MvPowerSeries τ C} {g g' : MvPowerSeries τ C}
    (h : TendsS V f g) (h' : TendsS V f' g') : TendsS V (fun n => f n - f' n) (g - g') := fun μ => by
  simpa [sub_eq_add_neg] using (h μ).add (h' μ).neg

theorem TendsS.unique {τ : Type} {f : ℕ → MvPowerSeries τ C} {g g' : MvPowerSeries τ C}
    (h : TendsS V f g) (h' : TendsS V f g') : g = g' := by
  ext μ; exact (h μ).unique (h' μ)

theorem TendsS.const_zero {τ : Type} {f : ℕ → MvPowerSeries τ C} {g : MvPowerSeries τ C}
    (h : TendsS V f g) (hf : ∀ n, MvPowerSeries.constantCoeff (f n) = 0) : MvPowerSeries.constantCoeff g = 0 := by
  have h0 := h 0
  simp only [MvPowerSeries.coeff_zero_eq_constantCoeff_apply, hf] at h0
  exact h0.unique (Tends.const 0)

def TendsS.lift {τ : Type} {f : ℕ → MvPowerSeries τ C} {g : MvPowerSeries τ C} (h : TendsS V f g) :
    MvPowerSeries τ (convRing V) :=
  fun μ => ⟨(fun n => MvPowerSeries.coeff μ (f n), MvPowerSeries.coeff μ g), h μ⟩

def term (V : VF C) (n : ℕ) : convRing V →+* C :=
  ((Pi.evalRingHom (fun _ : ℕ => C) n).comp (RingHom.fst _ _)).comp (convRing V).subtype

def lim (V : VF C) : convRing V →+* C := (RingHom.snd _ _).comp (convRing V).subtype

theorem TendsS.subst {σ τ : Type} [Finite σ] {a : ℕ → σ → MvPowerSeries τ C} {b : σ → MvPowerSeries τ C}
    (ha : ∀ n s, MvPowerSeries.constantCoeff (a n s) = 0) (hab : ∀ s, TendsS V (fun n => a n s) (b s))
    {f : ℕ → MvPowerSeries σ C} {g : MvPowerSeries σ C} (h : TendsS V f g) :
    TendsS V (fun n => MvPowerSeries.subst (a n) (f n)) (MvPowerSeries.subst b g) := by
  have hA : MvPowerSeries.HasSubst fun s => (hab s).lift := by
    refine MvPowerSeries.hasSubst_of_constantCoeff_zero fun s => ?_
    apply Subtype.ext
    refine Prod.ext (funext fun n => ha n s) ((hab s).const_zero fun n => ha n s)
  have h1 : ∀ n, MvPowerSeries.map (term V n) (MvPowerSeries.subst (fun s => (hab s).lift) h.lift) =
      MvPowerSeries.subst (a n) (f n) := fun n => MvPowerSeries.map_subst hA _
  have h2 : MvPowerSeries.map (lim V) (MvPowerSeries.subst (fun s => (hab s).lift) h.lift) =
      MvPowerSeries.subst b g := MvPowerSeries.map_subst hA _
  intro μ
  simp only [← h1, ← h2, MvPowerSeries.coeff_map]
  exact (MvPowerSeries.coeff μ (MvPowerSeries.subst (fun s => (hab s).lift) h.lift)).2

theorem exists_tends (cpl : ∀ s : ℕ → C, (∀ n : ℕ, V.Ge n (s (n + 1) - s n)) → ∃ x, ∀ n : ℕ, V.Ge n (x - s n))
    {s : ℕ → C} (hs : ∀ N : ℕ, ∃ n0 : ℕ, ∀ n ≥ n0, V.Ge N (s (n + 1) - s n)) : ∃ x, Tends V s x := by
  choose k hk using hs
  have hd : ∀ N m n, k N ≤ m → m ≤ n → V.Ge N (s n - s m) := by
    intro N m n hm hn
    induction n, hn using Nat.le_induction with
    | base => simpa using VF.Ge.zero (V := V) N
    | succ n hn ih => simpa using (hk N n (hm.trans hn)).add ih
  let φ : ℕ → ℕ := fun N => (Finset.range (N + 1)).sup k
  have h1 : ∀ N, k N ≤ φ N := fun N => Finset.le_sup (f := k) (Finset.self_mem_range_succ N)
  have h2 : ∀ N, φ N ≤ φ (N + 1) := fun N => Finset.sup_mono (Finset.range_mono (by omega))
  obtain ⟨x, hx⟩ := cpl (fun N => s (φ N)) fun N => hd N _ _ (h1 N) (h2 N)
  refine ⟨x, fun w => ?_⟩
  filter_upwards [eventually_ge_atTop (φ ⌈w⌉₊)] with n hn
  have := (hx ⌈w⌉₊).sub (hd ⌈w⌉₊ _ _ (h1 _) hn)
  simpa using this.mono (Nat.le_ceil w)

variable {dd : ℕ}

theorem const_ev {m n : ℕ} {a : Fin m → Pt C n dd} (ha : ∀ j i, MvPowerSeries.constantCoeff (a j i) = 0)
    {f : PS C m dd} (hf : MvPowerSeries.constantCoeff f = 0) : MvPowerSeries.constantCoeff (ev a f) = 0 :=
  MvPowerSeries.constantCoeff_subst_eq_zero (a := fun p : Fin m × Fin dd => a p.1 p.2)
    (MvPowerSeries.hasSubst_of_constantCoeff_zero fun p => ha p.1 p.2) (fun p => ha p.1 p.2) hf

theorem const_of_ev {m n : ℕ} {a : Fin m → Pt C n dd} (ha : ∀ j i, MvPowerSeries.constantCoeff (a j i) = 0)
    {f : PS C m dd} (hf : ev a f = 0) : MvPowerSeries.constantCoeff f = 0 := by
  have h := const_ev ha (f := f - MvPowerSeries.C (MvPowerSeries.constantCoeff f)) (by simp)
  unfold ev at h hf
  rw [MvPowerSeries.subst_sub (a := fun p : Fin m × Fin dd => a p.1 p.2)
    (MvPowerSeries.hasSubst_of_constantCoeff_zero fun p => ha p.1 p.2), hf,
    MvPowerSeries.subst_C] at h
  simpa using h

theorem const_pt {n : ℕ} (j : Fin n) (i : Fin dd) : MvPowerSeries.constantCoeff (pt C dd j i) = 0 := by
  simp [pt]

theorem const_comp1 {n : ℕ} {φ : Pt C 1 dd} (hφ : ∀ i, MvPowerSeries.constantCoeff (φ i) = 0) {a : Pt C n dd}
    (ha : ∀ i, MvPowerSeries.constantCoeff (a i) = 0) (i : Fin dd) :
    MvPowerSeries.constantCoeff (comp1 φ a i) = 0 :=
  const_ev (fun j i => by fin_cases j; exact ha i) (hφ i)

theorem tends_comp1 {n : ℕ} {φ : ℕ → Pt C 1 dd} {e : Pt C 1 dd} (h : ∀ i, TendsS V (fun k => φ k i) (e i))
    {a : Pt C n dd} (ha : ∀ i, MvPowerSeries.constantCoeff (a i) = 0) (i : Fin dd) :
    TendsS V (fun k => comp1 (φ k) a i) (comp1 e a i) :=
  TendsS.subst (a := fun _ (p : Fin 1 × Fin dd) => ![a] p.1 p.2)
    (fun _ p => by obtain ⟨j, i⟩ := p; fin_cases j; exact ha i) (fun _ => TendsS.const _) (h i)

theorem constantCoeff_germEvalTwo_eq_zero {n : ℕ} {a b : Pt C n dd} (ha : ∀ i, MvPowerSeries.constantCoeff (a i) = 0)
    (hb : ∀ i, MvPowerSeries.constantCoeff (b i) = 0) {f : PS C 2 dd} (hf : MvPowerSeries.constantCoeff f = 0) :
    MvPowerSeries.constantCoeff (ev ![a, b] f) = 0 :=
  const_ev (fun j i => by fin_cases j; exacts [ha i, hb i]) hf

theorem tendsToCoeffwise_germEvalTwo {n : ℕ} {a b : ℕ → Pt C n dd} {a' b' : Pt C n dd}
    (ha : ∀ k i, MvPowerSeries.constantCoeff (a k i) = 0) (hb : ∀ k i, MvPowerSeries.constantCoeff (b k i) = 0)
    (ha' : ∀ i, TendsS V (fun k => a k i) (a' i)) (hb' : ∀ i, TendsS V (fun k => b k i) (b' i)) (f : PS C 2 dd) :
    TendsS V (fun k => ev ![a k, b k] f) (ev ![a', b'] f) :=
  TendsS.subst (a := fun k (p : Fin 2 × Fin dd) => ![a k, b k] p.1 p.2)
    (fun k p => by obtain ⟨j, i⟩ := p; fin_cases j; exacts [ha k i, hb k i])
    (fun p => by obtain ⟨j, i⟩ := p; fin_cases j; exacts [ha' i, hb' i]) (TendsS.const f)

theorem exists_lim [CharZero C] {O : Type} [CommRing O] [StarRing O] (Y : FBChart C V O dd) {a : ℕ → O}
    (ha : ActCv Y a) : ∃ e : Pt C 1 dd, ∀ i, TendsS V (fun n => Y.B.A.act (a n) i) (e i) := by
  choose e he using fun i μ => exists_tends Y.cpl (s := fun n => MvPowerSeries.coeff μ (Y.B.A.act (a n) i))
    fun N => ha N i μ
  exact ⟨fun i μ => e i μ, he⟩

theorem limit_endomorphisms : ∀ (C : Type) [Field C] [CharZero C] (V : VF C) (O : Type) [CommRing O] [StarRing O]
    (dd : ℕ) (Y : FBChart C V O dd), EndomorphismLimitIntegral Y := by
  intro C _ _ V O _ _ dd Y a ha hb
  obtain ⟨e, he⟩ := exists_lim Y ha
  obtain ⟨eb, heb⟩ := exists_lim Y hb
  have hc := Y.B.A.const
  refine ⟨e, eb, fun i μ => (he i μ).ge fun n => Y.intAct _ i μ, fun i μ => (heb i μ).ge fun n => Y.intAct _ i μ,
    fun N i μ => eventually_atTop.1 (he i μ N), fun N i μ => eventually_atTop.1 (heb i μ N), ?_, ?_⟩
  · funext i
    have h1 := tends_comp1 he (a := addOf Y.B.G.F (pt C (n := 2) dd 0) (pt C (n := 2) dd 1))
      (fun i => constantCoeff_germEvalTwo_eq_zero (const_pt 0) (const_pt 1) (Y.B.G.const i)) i
    have h2 := tendsToCoeffwise_germEvalTwo (V := V) (fun k => const_comp1 (hc (a k)) (const_pt (n := 2) 0))
      (fun k => const_comp1 (hc (a k)) (const_pt 1)) (tends_comp1 he (const_pt 0))
      (tends_comp1 he (const_pt 1)) (Y.B.G.F i)
    refine h1.unique ?_
    simp only [Y.B.A.hom]
    exact h2
  · have hh : MvPowerSeries.constantCoeff Y.h = 0 :=
      const_of_ev (fun j i => by fin_cases j; exacts [map_zero _, const_pt 0 i]) Y.gauge.ax0
    have hid : ∀ {τ : Type} (f : MvPowerSeries τ C), MvPowerSeries.map (algebraMap C C) f = f := fun f => by
      ext μ; simp
    have hK : ∀ x, Y.B.actK C x = Y.B.A.act x := fun x => funext fun i => hid _
    have h1 := (tendsToCoeffwise_germEvalTwo (V := V) (fun k => const_comp1 (hc (a k)) (const_pt (n := 2) 0))
      (fun _ => const_pt 1) (tends_comp1 he (const_pt 0)) (fun i => TendsS.const _) Y.h).sub
      (tendsToCoeffwise_germEvalTwo (V := V) (fun _ => const_pt (n := 2) 0) (fun k => const_comp1 (hc (star (a k))) (const_pt 1))
        (fun i => TendsS.const _) (tends_comp1 heb (const_pt 1)) Y.h)
    have h2 := TendsS.subst (σ := Unit) (fun k _ => by
      rw [map_sub, constantCoeff_germEvalTwo_eq_zero (const_comp1 (hc (a k)) (const_pt (n := 2) 0)) (const_pt 1) hh,
        constantCoeff_germEvalTwo_eq_zero (const_pt (n := 2) 0) (const_comp1 (hc (star (a k))) (const_pt 1)) hh, sub_zero])
      (fun _ => h1) (TendsS.const (PowerSeries.exp C))
    intro μ
    refine (h2 μ).ge fun n => ?_
    have h3 := Y.gauge.ad (a n)
    rw [hK, hK] at h3
    have h4 := Y.intAd (a n) μ
    rw [(hid (Y.B.ad (a n))).symm.trans h3] at h4
    exact h4

end GlobalTheory.ActLimit
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.LeafCoordinateWeightNonnegOfAdaptedChainDataStatement
section
open Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds GlobalTheory.MainTerm Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.leafCoordinate_weight_nonneg_of_adaptedChainData : ∀ (C : Type) [Field C] [CharZero C] (V : VF C) (d : ℕ) [NeZero d] (I J : Type) [Fintype I] [Fintype J] (G : Cart V d I J) (S : Sys G) (Z : Type) (D : Formalism.BaseCaseIdentities.Data C Z I) (a : ZMod d) (i : ℕ), Adapted S D a i → ∀ t : I → MvPowerSeries I C, S.IsT t → ∀ (N : ℕ) (em : Fin N → I), (∀ δ, D.lev (em δ) = 0) → ∀ c, WtGe1 V i 0 (linPull (fun δ => S.tan (em δ)) (t c)) := by
  first | exact @GlobalTheory.LeafCoordWeight.weight_nonneg | exact GlobalTheory.LeafCoordWeight.weight_nonneg | (intros; apply GlobalTheory.LeafCoordWeight.weight_nonneg <;> assumption)
end

