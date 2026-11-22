import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.InvVolConjLevelOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0318
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTranslatesEqPrimFrameLat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1703
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1832
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1823
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsINeZeroKind
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1824
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0259
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.HasDerivAtZeroAndIsTheta
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0068
import GroundTheory.GlobalFields.Adele.Bundle0001
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0061

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatIntegrableAaVacOfConductor
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField Matrix MeasureTheory
open scoped TensorProduct nonZeroDivisors

namespace GlobalTheory.FunObj

open GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StepData GlobalTheory.StdFrames Formalism.L2.Host Formalism.L2.DIV ValuativeRel

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

section Gen
variable {k : Type*} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem apow_zpow (x : kˣ) (n : ℤ) (z : ℂ) : apow (x ^ n) z = apow x (n * z) := by
  induction n using Int.induction_on with
  | zero => simp [apow, nabs_one]
  | succ n ih =>
    rw [_root_.zpow_add_one, apow_mul, ih, ← apow_add]
    congr 1; push_cast; ring
  | pred n ih =>
    rw [_root_.zpow_sub_one, apow_mul, ih, apow_inv, ← apow_add]
    congr 1; push_cast; ring

theorem prod_apow {α : Type*} (x : kˣ) (f : α → ℂ) (l : List α) :
    (l.map fun b => apow x (f b)).prod = apow x (l.map f).sum := by
  induction l with
  | nil => simp [apow]
  | cons b l ih => rw [List.map_cons, List.prod_cons, ih, List.map_cons, List.sum_cons, apow_add]

end Gen

theorem even_mul_add_odd (a d : ℕ) (hd : Odd d) : Even (a * (a + d)) := by
  rcases Nat.even_or_odd a with h | h
  · exact h.mul_right _
  · exact (h.add_odd hd).mul_left _

theorem even_sum_of_even {α : Type*} (P : α → ℕ) : ∀ l : List α, (∀ b ∈ l, Even (P b)) → Even (l.map P).sum
  | [], _ => by simp
  | b :: l, h => by
    rw [List.map_cons, List.sum_cons]
    exact (h b List.mem_cons_self).add (even_sum_of_even P l fun c hc => h c (List.mem_cons_of_mem _ hc))

variable {D : D7}

theorem mem_oppositePath {m : ℕ} {b : Edge} : b ∈ oppositePath m ↔ (∃ i < m, b = .ex i m) ∨ ∃ j < m, b = .theta m j := by
  simp only [oppositePath, List.mem_append, List.mem_map, List.mem_range, List.mem_reverse]
  constructor
  · rintro (⟨i, hi, rfl⟩ | ⟨j, hj, rfl⟩)
    · exact Or.inl ⟨i, hi, rfl⟩
    · exact Or.inr ⟨j, hj, rfl⟩
  · rintro (⟨i, hi, rfl⟩ | ⟨j, hj, rfl⟩)
    · exact Or.inl ⟨i, hi, rfl⟩
    · exact Or.inr ⟨j, hj, rfl⟩

theorem even_rank_mul_path (w : Pl D.host.E) {b : Edge} (hb : b ∈ oppositePath (bareGrid w).m) :
    Even ((bareGrid w).rank b.src * (bareGrid w).rank b.tgt) := by
  rcases mem_oppositePath.1 hb with ⟨i, -, rfl⟩ | ⟨j, -, rfl⟩
  · have := even_mul_add_odd ((bareGrid w).rank (i, (bareGrid w).m)) (sLen D) (odd_sLen D)
    convert this using 2
    simp only [Grid.rank, bareGrid]; ring
  · have := even_mul_add_odd ((bareGrid w).rank ((bareGrid w).m, j)) D.R.t D.R.t_odd
    rw [mul_comm]
    convert this using 2
    simp only [Grid.rank, bareGrid]; ring

theorem rank_path_le (w : Pl D.host.E) {b : Edge} (hb : b ∈ oppositePath (bareGrid w).m) :
    (bareGrid w).rank b.src ≤ bigN D ∧ (bareGrid w).rank b.tgt ≤ bigN D := by
  have hr : D.R.r + 1 = D.R.k + D.R.m := by unfold Ranks.r; have := D.R.two_le_m; omega
  have key : ∀ i j, i ≤ D.R.m → j ≤ D.R.m → (bareGrid w).rank (i, j) ≤ bigN D := fun i j hi hj => by
    simp only [Grid.rank, bareGrid, bigN]
    have h1 := Nat.mul_le_mul_right D.R.t hj
    have h2 := Nat.mul_le_mul_right (sLen D) hi
    nlinarith
  rcases mem_oppositePath.1 hb with ⟨i, hi, rfl⟩ | ⟨j, hj, rfl⟩
  · exact ⟨key _ _ hi.le le_rfl, key _ _ hi le_rfl⟩
  · exact ⟨key _ _ le_rfl hj, key _ _ le_rfl hj.le⟩

theorem path_apow_pow (w : Pl D.host.E) : ∃ n : ℤ, ((oppositePath D.R.m).map fun b =>
    apow (genAt w D.host.AAbar / genAt w D.host.AA)
      (((bareGrid w).rank b.src * (bareGrid w).rank b.tgt : ℕ) / 4)).prod =
      (resCard (Kw w) : ℂ) ^ ((n : ℂ) / 2) ∧
    |n| ≤ (D.R.m : ℤ) ^ 3 * (bigN D : ℤ) ^ 2 *
      (|FractionalIdeal.count D.host.E w D.host.AA| + |FractionalIdeal.count D.host.E w D.host.AAbar|) := by
  set a := FractionalIdeal.count D.host.E w D.host.AA
  set a' := FractionalIdeal.count D.host.E w D.host.AAbar
  set P : Edge → ℕ := fun b => (bareGrid w).rank b.src * (bareGrid w).rank b.tgt
  have hm : (bareGrid w).m = D.R.m := rfl
  have hev : Even ((oppositePath D.R.m).map P).sum := even_sum_of_even P _ fun b hb => even_rank_mul_path w (hm ▸ hb)
  obtain ⟨S, hS⟩ := hev
  have hsum : ((oppositePath D.R.m).map fun b => ((P b : ℕ) : ℂ) / 4).sum = ((((oppositePath D.R.m).map P).sum : ℕ) : ℂ) / 4 := by
    induction (oppositePath D.R.m) with
    | nil => simp
    | cons b l ih => simp only [List.map_cons, List.sum_cons, ih]; push_cast; ring
  refine ⟨(a - a') * S, ?_, ?_⟩
  · rw [prod_apow, hsum, genAt, genAt, div_eq_mul_inv, ← _root_.zpow_sub, apow_zpow, (isUnif_unifAt w).apow_eq, hS]
    congr 1; push_cast; ring
  · have hle : ((oppositePath D.R.m).map P).sum ≤ ((oppositePath D.R.m).map P).length • (bigN D ^ 2) := by
      refine List.sum_le_card_nsmul ((oppositePath D.R.m).map P) _ fun x hx => ?_
      obtain ⟨b, hb, rfl⟩ := List.mem_map.1 hx
      obtain ⟨h1, h2⟩ := rank_path_le w (hm ▸ hb)
      simpa [P, sq] using Nat.mul_le_mul h1 h2
    have hlen : (oppositePath D.R.m).length = 2 * D.R.m := by simp [oppositePath]; ring
    rw [List.length_map, hlen, smul_eq_mul] at hle
    have hS' : (S : ℤ) ≤ D.R.m * bigN D ^ 2 := by
      have : S + S ≤ 2 * D.R.m * bigN D ^ 2 := hS ▸ hle
      have : S ≤ D.R.m * bigN D ^ 2 := by nlinarith
      exact_mod_cast this
    have hm1 : (1 : ℤ) ≤ D.R.m := by have := D.R.two_le_m; omega
    have hN : (0 : ℤ) ≤ bigN D := by positivity
    rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℤ) ≤ S)]
    have h3 : |a - a'| ≤ |a| + |a'| := abs_sub _ _
    have h4 : (D.R.m : ℤ) * bigN D ^ 2 ≤ D.R.m ^ 3 * bigN D ^ 2 := by
      have : (D.R.m : ℤ) ≤ D.R.m ^ 3 := by nlinarith [mul_le_mul hm1 hm1 zero_le_one (by linarith)]
      exact mul_le_mul_of_nonneg_right this (by positivity)
    calc |a - a'| * (S : ℤ) ≤ (|a| + |a'|) * (D.R.m * bigN D ^ 2) :=
          mul_le_mul h3 hS' (by positivity) (by positivity)
      _ ≤ (|a| + |a'|) * (D.R.m ^ 3 * bigN D ^ 2) := mul_le_mul_of_nonneg_left h4 (by positivity)
      _ = _ := by ring

theorem isLocallyConstant_aaVac (w : Pl D.host.E) : IsLocallyConstant (aaVac w) := by
  classical
  refine (IsLocallyConstant.iff_eventually_eq _).2 fun x => ?_
  set c : Kw w := (((genAt w D.host.AA)⁻¹ : (Kw w)ˣ) : Kw w)
  have h : ∀ᶠ y in nhds x, ∀ b ∈ (oppositePath (bareGrid w).m).toFinset, ∀ i j, c * (y b i j - x b i j) ∈ 𝒪[Kw w] := by
    refine (Filter.eventually_all_finset _).2 fun b _ => Filter.eventually_all.2 fun i =>
      Filter.eventually_all.2 fun j => ?_
    have hc : Continuous fun y : (bareGrid w).Args => c * (y b i j - x b i j) :=
      continuous_const.mul (((continuous_apply b).matrix_elem i j).sub continuous_const)
    exact (Model.isOpen_int.preimage hc).mem_nhds (by simp)
  filter_upwards [h] with y hy
  have key : ∀ b ∈ oppositePath (bareGrid w).m, ∀ i j, (c * y b i j ∈ 𝒪[Kw w] ↔ c * x b i j ∈ 𝒪[Kw w]) :=
    fun b hb i j => by
      have hd := hy b (List.mem_toFinset.2 hb) i j
      have e : c * y b i j = c * x b i j + c * (y b i j - x b i j) := by ring
      rw [e]
      exact ⟨fun h1 => by simpa using sub_mem h1 hd, fun h1 => add_mem h1 hd⟩
  have hs : (y ∈ {z : (bareGrid w).Args | ∀ b ∈ oppositePath (bareGrid w).m, ∀ i j, c * z b i j ∈ 𝒪[Kw w]}) ↔
      (x ∈ {z : (bareGrid w).Args | ∀ b ∈ oppositePath (bareGrid w).m, ∀ i j, c * z b i j ∈ 𝒪[Kw w]}) := by
    exact forall₂_congr fun b hb => forall₂_congr fun i j => key b hb i j
  unfold aaVac
  by_cases hx : x ∈ {z : (bareGrid w).Args | ∀ b ∈ oppositePath (bareGrid w).m, ∀ i j, c * z b i j ∈ 𝒪[Kw w]}
  · rw [Set.indicator_of_mem hx, Set.indicator_of_mem (hs.2 hx)]; rfl
  · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem (mt hs.1 hx)]

theorem hasCompactSupport_aaVac (w : Pl D.host.E) (ψ : AddChar (Kw w) Circle) (keep : Bool) (g : (bareGrid w).VertexGroup)
    (x : ColArgs (bareGrid w)) (y : RowArgs (bareGrid w)) :
    HasCompactSupport (flatIntegrand one_le_sLen ψ (moved (bareGrid w) keep g (aaVac w)) x y) := by
  classical
  obtain ⟨_, _⟩ := Model.secondCountable_and_t2_local_field (k := Kw w)
  choose a b c h using exists_fill_entry (G := bareGrid w) one_le_sLen x y
  set u : (Kw w)ˣ := (genAt w D.host.AA)⁻¹
  choose K hK hK' using fun j : Fin ((bareGrid w).m - 1) => exists_isCompact_of_mul_mem
    (SplitFlip.diagGL (fun _ => u) * (Assignment.one.read (g (Edge.theta (bareGrid w).m j).tgt))⁻¹)
    (Assignment.one.read (g (Edge.theta (bareGrid w).m j).src))
  refine HasCompactSupport.intro (K := Set.univ.pi fun j => Set.univ.pi fun rs =>
    (fun M => M (a j rs) (b j rs) - c j rs) '' K j) (isCompact_univ_pi fun j => isCompact_univ_pi fun rs =>
      (hK j).image ((continuous_id.matrix_elem _ _).sub continuous_const)) fun v hv => ?_
  have h0 : aaVac w ((bareGrid w).moveArgs .one g (fill one_le_sLen x y v)) = 0 := by
    by_contra hne
    have hmem := Set.mem_of_indicator_ne_zero hne
    refine hv fun j _ rs _ => ⟨_, hK' j _ ?_, (h j rs v).symm⟩
    refine mem_matLat_stdLat.2 fun r s => ?_
    have hb : Edge.theta (bareGrid w).m j ∈ oppositePath (bareGrid w).m := by
      have := j.2; simp [oppositePath]; omega
    have := hmem _ hb r s
    simp only [Grid.moveArgs] at this
    simpa [Units.val_mul, diagGL_val, Matrix.mul_assoc, Matrix.diagonal_mul, u] using this
  simp [flatIntegrand, moved, Grid.pathAct, h0]

theorem flatIntegrable_aaVac (w : Pl D.host.E) {ψ : AddChar (Kw w) Circle} (hψ : Continuous ψ) :
    FlatIntegrable (G := bareGrid w) one_le_sLen ψ (unitVol w) (aaVac w) := by
  classical
  obtain ⟨_, _⟩ := Model.secondCountable_and_t2_local_field (k := Kw w)
  have := (isUnitVol_unitVol w).1
  intro g x y
  unfold varsVol
  have hm : Continuous ((bareGrid w).moveArgs .one g) := continuous_pi fun b =>
    (continuous_const.matrix_mul (continuous_apply b)).matrix_mul continuous_const
  have hc : Continuous (flatIntegrand one_le_sLen ψ (moved (bareGrid w) true g (aaVac w)) x y) :=
    (continuous_const.mul (continuous_const.mul
      ((isLocallyConstant_aaVac w).continuous.comp (hm.comp (continuous_fill one_le_sLen x y))))).mul
      (continuous_subtype_val.comp (hψ.comp (continuous_phase x).neg))
  exact hc.integrable_of_hasCompactSupport (hasCompactSupport_aaVac w ψ true g x y)

variable {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (W : G.Weil)

theorem aaScalar_eq_pow (w : Pl D.host.E) (hψ : HasConductor (psiAt W w) (genAt w D.host.AA * genAt w D.host.AAbar)) :
    ∃ n : ℤ, aaScalar W w = (resCard (Kw w) : ℂ) ^ ((n : ℂ) / 2) ∧
    |n| ≤ 16 * ((D.R.m : ℤ) ^ 3 * (bigN D : ℤ) ^ 2 *
      (|FractionalIdeal.count D.host.E w D.host.AA| + |FractionalIdeal.count D.host.E w D.host.AAbar|)) := by
  obtain ⟨n1, h1, b1⟩ := GlobalTheory.T.unfoldingTerm_coef_eq_residueCard_zpow W w
  obtain ⟨n2, h2, b2⟩ := GlobalTheory.T.originDatum_value_halfIntegerPow_placeAA W w fun a ha => hψ.eq_one ha
  obtain ⟨n3, h3, b3⟩ := path_apow_pow w
  have hq : (resCard (Kw w) : ℂ) ≠ 0 := by
    have : 1 < resCard (Kw w) := Finite.one_lt_card; exact_mod_cast (show resCard (Kw w) ≠ 0 by omega)
  refine ⟨2 * n1 + n2 + n3, ?_, ?_⟩
  · have e1 : (((resCard (Kw w) : ℚ) ^ n1 : ℚ) : ℂ) = (resCard (Kw w) : ℂ) ^ (((2 * n1 : ℤ) : ℂ) / 2) := by
      rw [Rat.cast_zpow, Rat.cast_natCast, ← Complex.cpow_intCast]; congr 1; push_cast; ring
    rw [aaScalar, h1, h2, h3, e1, ← Complex.cpow_add _ _ hq, ← Complex.cpow_add _ _ hq]
    congr 1; push_cast; ring
  · have hB : 0 ≤ (D.R.m : ℤ) ^ 3 * (bigN D : ℤ) ^ 2 *
        (|FractionalIdeal.count D.host.E w D.host.AA| + |FractionalIdeal.count D.host.E w D.host.AAbar|) := by positivity
    calc |2 * n1 + n2 + n3| ≤ 2 * |n1| + |n2| + |n3| := by
          have := abs_add_le (2 * n1 + n2) n3; have := abs_add_le (2 * n1) n2
          rw [abs_mul, abs_two] at *; linarith
      _ ≤ _ := by linarith

theorem sAA_facts {U : Set T} (S : GridChoice W U)
    (hψ : ∀ w ∈ S.PA, HasConductor (psiAt W w) (genAt w D.host.AA * genAt w D.host.AAbar)) :
    S.sAA ≠ 0 ∧ (∃ r : ℝ, 0 < r ∧ S.sAA = r) ∧ ∃ Q : ℚ, S.sAA ^ 2 = Q := by
  classical
  have hw : ∀ w ∈ S.PA, ∃ n : ℤ, aaScalar W w = (resCard (Kw w) : ℂ) ^ ((n : ℂ) / 2) :=
    fun w hw => (aaScalar_eq_pow W w (hψ w hw)).imp fun _ h => h.1
  choose! n hn using hw
  have e : ∀ w ∈ S.PA, aaScalar W w = (((resCard (Kw w) : ℝ) ^ ((n w : ℝ) / 2) : ℝ) : ℂ) := fun w hw => by
    rw [hn w hw, Complex.ofReal_cpow (Nat.cast_nonneg _)]; push_cast; rfl
  have hr : S.sAA = ((∏ w ∈ S.PA, (resCard (Kw w) : ℝ) ^ ((n w : ℝ) / 2) : ℝ) : ℂ) := by
    rw [GridChoice.sAA, Complex.ofReal_prod]; exact Finset.prod_congr rfl e
  have hpos : 0 < ∏ w ∈ S.PA, (resCard (Kw w) : ℝ) ^ ((n w : ℝ) / 2) :=
    Finset.prod_pos fun w _ => Real.rpow_pos_of_pos (by have : 1 < resCard (Kw w) := Finite.one_lt_card; positivity) _
  have hsq : (∏ w ∈ S.PA, (resCard (Kw w) : ℝ) ^ ((n w : ℝ) / 2)) ^ 2 =
      ((∏ w ∈ S.PA, (resCard (Kw w) : ℚ) ^ n w : ℚ) : ℝ) := by
    rw [← Finset.prod_pow, Rat.cast_prod]
    refine Finset.prod_congr rfl fun w _ => ?_
    rw [← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg _), Rat.cast_zpow, Rat.cast_natCast, ← Real.rpow_intCast]
    congr 1; push_cast; ring
  refine ⟨by rw [hr]; exact_mod_cast hpos.ne', ⟨_, hpos, hr⟩, ∏ w ∈ S.PA, (resCard (Kw w) : ℚ) ^ n w, ?_⟩
  rw [hr, ← Complex.ofReal_pow, hsq, Complex.ofReal_ratCast]

theorem flatIntegrable_aaVac_of_conductor (w : Pl D.host.E)
    (hψ : HasConductor (psiAt W w) (genAt w D.host.AA * genAt w D.host.AAbar)) :
    FlatIntegrable (G := bareGrid w) one_le_sLen (psiAt W w) (unitVol w) (aaVac w) :=
  flatIntegrable_aaVac w hψ.continuous

end GlobalTheory.FunObj
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockVacuaTripleProportionalToNonzeroStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames GlobalTheory.BigNZ GlobalTheory.AdelicU
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ Num IsTripleOf IsDatumA skewGram blkU conjU UB)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chars Rep IsTriple UAt ratU mat Acts SInf)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fockVacua_triple_proportional_to_nonzero : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {a a' : ℕ}
    (B : Base F E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo σ a a') (X : Chars F E) (om : Rep σ Γ.V Γ.W) (om' : Rep σ Γ.V' Γ.W),
    IsTriple B Γ X om om' → ∀ f₀, f₀ ≠ 0 → Γ.M.IsGauss B.ψ B.emb f₀ → ∀ g, Γ.M.IsGauss B.ψ B.emb g → ∃ c : ℂ, g = c • f₀ := by
  first | exact @GlobalTheory.GaussLine.gauss_eq_smul | exact GlobalTheory.GaussLine.gauss_eq_smul | (intros; apply GlobalTheory.GaussLine.gauss_eq_smul <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockVacuumThetaFunctionDerivativeComplexStructur
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.VacAny
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames GlobalTheory.BigNZ GlobalTheory.AdelicU GlobalTheory.WeilM
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ Num IsTripleOf IsDatumA skewGram mulG colV adjV₁)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chars Rep IsTriple Acts SInf At latAtV realAd evI)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.BigDat

noncomputable section
namespace GlobalTheory.FockLineJ

variable {D : D7}

theorem theta_realAd {θ : InfFam D} (hθ : IsInfFam θ) (τ : D.what₂.Tau) (t : ℝ) :
    θ τ (fstA D.host.F (realAd D.host.F t) ⊗ₜ[D.host.F] (1 : D.host.E)) = t := by
  have h2 : Continuous (InfiniteAdeleRing.ringEquiv_mixedSpace D.host.F).symm := by
    have : ⇑(InfiniteAdeleRing.ringEquiv_mixedSpace D.host.F).symm = ⇑(GroundTheory.Global.homeomorphMixedSpace D.host.F).symm :=
      funext fun y => by
        rw [Homeomorph.eq_symm_apply]
        exact (InfiniteAdeleRing.ringEquiv_mixedSpace D.host.F).apply_symm_apply y
    rw [this]
    exact (GroundTheory.Global.homeomorphMixedSpace D.host.F).symm.continuous
  let φ : ℝ →+* ℂ := ((θ τ).comp Algebra.TensorProduct.includeLeftRingHom).comp
    ((InfiniteAdeleRing.ringEquiv_mixedSpace D.host.F).symm.toRingHom.comp
      (algebraMap ℝ (mixedEmbedding.mixedSpace D.host.F)))
  have hφ : Continuous φ :=
    (hθ τ).2.comp (h2.comp (continuous_algebraMap ℝ (mixedEmbedding.mixedSpace D.host.F)))
  have e : ∀ s, φ s = θ τ (fstA D.host.F (realAd D.host.F s) ⊗ₜ[D.host.F] (1 : D.host.E)) := fun s => rfl
  rw [← e]
  have h1 : φ t = t * φ 1 := GlobalTheory.WeilVacMove.additive_real φ.toAddMonoidHom hφ t
  rw [h1, map_one, mul_one]

theorem realAd_smul_eq (t : ℝ) (a : AE D) :
    realAd D.host.F t • a = (realAd D.host.F t ⊗ₜ[D.host.F] (1 : D.host.E)) * a := by
  rw [Algebra.smul_def]; rfl

theorem finPart_realAd_smul (t : ℝ) (a : AE D) : finPart D (realAd D.host.F t • a) = 0 := by
  rw [realAd_smul_eq, map_mul]
  have : finPart D (realAd D.host.F t ⊗ₜ[D.host.F] (1 : D.host.E)) = 0 := by
    show sndA D.host.F (realAd D.host.F t) ⊗ₜ[D.host.F] (AlgHom.id D.host.F D.host.E 1) = 0
    rw [show sndA D.host.F (realAd D.host.F t) = 0 from rfl, TensorProduct.zero_tmul]
  rw [this, zero_mul]

theorem theta_realAd_smul {θ : InfFam D} (hθ : IsInfFam θ) (τ : D.what₂.Tau) (t : ℝ) (a : AE D) :
    θ τ (infPart D (realAd D.host.F t • a)) = t * θ τ (infPart D a) := by
  rw [realAd_smul_eq, map_mul, map_mul]
  have : infPart D (realAd D.host.F t ⊗ₜ[D.host.F] (1 : D.host.E)) =
      fstA D.host.F (realAd D.host.F t) ⊗ₜ[D.host.F] (1 : D.host.E) := rfl
  rw [this, theta_realAd hθ]

set_option synthInstance.maxHeartbeats 400000 in

theorem realAd_smul_eq_sum {m n : ℕ} {θ : InfFam D} (hθ : IsInfFam θ) {σ : (D.what₂.Tau → ℂ) →+ AE D}
    (hσ : GlobalTheory.FockCompare.Chart θ σ) (z : D.what₂.Tau → Matrix (Fin m) (Fin n) ℂ) (y : Mx D m n)
    (hy : ∀ τ, compAt θ τ y = z τ) (t : ℝ) :
    realAd D.host.F t • y = (∑ τ, lineAt θ τ (z τ)) t := by
  classical
  ext i j
  rw [← sub_eq_zero]
  have hl := fun τ => GlobalTheory.WeilVacMove.isLineAt_lineAt hθ τ (z τ)
  have hs : ((∑ τ, lineAt θ τ (z τ)) t) i j = ∑ τ, lineAt θ τ (z τ) t i j := by
    rw [AddMonoidHom.finset_sum_apply, Matrix.sum_apply]
  refine hσ.ext _ ?_ fun τ' => ?_
  · rw [map_sub, hs, map_sum, Matrix.smul_apply, finPart_realAd_smul, zero_sub, neg_eq_zero]
    exact Finset.sum_eq_zero fun τ _ => congrFun (congrFun ((hl τ).2.1 t) i) j
  · rw [map_sub, map_sub, hs, map_sum, map_sum, Matrix.smul_apply, theta_realAd_smul hθ, sub_eq_zero]
    have e1 : θ τ' (infPart D (y i j)) = z τ' i j := congrFun (congrFun (hy τ') i) j
    have e2 : ∀ τ, θ τ' (infPart D (lineAt θ τ (z τ) t i j)) = if τ' = τ then (t : ℂ) * z τ i j else 0 := by
      intro τ
      have h := congrFun (congrFun ((hl τ).2.2 t τ') i) j
      rw [compAt, Matrix.map_apply] at h
      rw [h]
      split_ifs <;> simp
    rw [e1, Finset.sum_congr rfl fun τ _ => e2 τ, Finset.sum_ite_eq]
    simp

theorem dLine_sum {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) {S T : HSp D} {ι : Type} (s : Finset ι)
    (N : ι → ℝ →+ WO S T) (hN : ∀ i, Continuous (N i)) (hN0 : ∀ i t, (N i t).map (finPart D) = 0)
    {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) :
    Continuous (⇑(∑ i ∈ s, N i) : ℝ → WO S T) ∧ (∀ t, ((∑ i ∈ s, N i) t).map (finPart D) = 0) ∧
      GlobalTheory.WeilVacMove.dLine ψ S T (∑ i ∈ s, N i) f = ∑ i ∈ s, GlobalTheory.WeilVacMove.dLine ψ S T (N i) f := by
  classical
  refine Finset.induction_on s ?_ ?_
  · refine ⟨?_, fun t => ?_, ?_⟩
    · rw [Finset.sum_empty]
      show Continuous fun _ : ℝ => (0 : WO S T)
      exact continuous_const
    · rw [Finset.sum_empty, AddMonoidHom.zero_apply]; ext i j; simp
    · rw [Finset.sum_empty, Finset.sum_empty]
      funext w
      simp [GlobalTheory.WeilVacMove.dLine]
  · intro a s ha ih
    obtain ⟨h1, h2, h3⟩ := ih
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    refine ⟨?_, fun t => ?_, ?_⟩
    · show Continuous fun t => N a t + (∑ x ∈ s, N x) t
      exact (hN a).add h1
    · rw [AddMonoidHom.add_apply, Matrix.map_add _ (finPart D).map_add, hN0 a t, h2 t, add_zero]
    · rw [GlobalTheory.BiJoinDeriv.dLine_add_line hψ (hN a) (hN0 a) h1 h2 hf, h3]

theorem fock_line_J : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D)
    (sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) (f : WO S T → ℂ),
    IsStdChar D ψ (-1) → IsInfFam θ → IsThetaFunO ψ S T f → (∀ τ, IsFockVacAt (heisO ψ S T) θ τ (cplxO (sS τ) (sT τ)) f) →
    ∀ x x' : WO S T, (∀ τ, compAt θ τ x' = cplxO (sS τ) (sT τ) (compAt θ τ x)) → ∀ w : WO S T, ∃ a : ℂ,
      HasDerivAt (fun t : ℝ => heisO ψ S T (realAd D.host.F t • x) f w) a 0 ∧
      HasDerivAt (fun t : ℝ => heisO ψ S T (realAd D.host.F t • x') f w) (Complex.I * a) 0 := by
  intro D ψ θ S T sS sT f hψ hθ hf hvac x x' hx' w
  obtain ⟨σ, hσ⟩ := GlobalTheory.RealLineAt.exists_inverse_chart hθ
  have hl := fun τ (z : Matrix (Fin T.rank) (Fin S.rank) ℂ) => GlobalTheory.WeilVacMove.isLineAt_lineAt hθ τ z
  let c : D.what₂.Tau → Matrix (Fin T.rank) (Fin S.rank) ℂ := fun τ => compAt θ τ x
  let c' : D.what₂.Tau → Matrix (Fin T.rank) (Fin S.rank) ℂ := fun τ => cplxO (sS τ) (sT τ) (c τ)
  obtain ⟨L1, L2, L3⟩ := dLine_sum hψ Finset.univ (fun τ => lineAt θ τ (c τ)) (fun τ => (hl τ _).1)
    (fun τ => (hl τ _).2.1) hf
  obtain ⟨M1, M2, M3⟩ := dLine_sum hψ Finset.univ (fun τ => lineAt θ τ (c' τ)) (fun τ => (hl τ _).1)
    (fun τ => (hl τ _).2.1) hf
  have e : ∀ t, realAd D.host.F t • x = (∑ τ, lineAt θ τ (c τ)) t :=
    realAd_smul_eq_sum hθ hσ c x (fun τ => rfl)
  have e' : ∀ t, realAd D.host.F t • x' = (∑ τ, lineAt θ τ (c' τ)) t :=
    realAd_smul_eq_sum hθ hσ c' x' hx'
  have hd := (GlobalTheory.WeilVacMove.hasDerivAt_zero_and_isTheta hψ L1 L2 hf).1 w
  have hd' := (GlobalTheory.WeilVacMove.hasDerivAt_zero_and_isTheta hψ M1 M2 hf).1 w
  refine ⟨GlobalTheory.WeilVacMove.dLine ψ S T (∑ τ, lineAt θ τ (c τ)) f w, ?_, ?_⟩
  · simp only [e]
    exact hd
  · have key : GlobalTheory.WeilVacMove.dLine ψ S T (∑ τ, lineAt θ τ (c' τ)) f w =
        Complex.I * GlobalTheory.WeilVacMove.dLine ψ S T (∑ τ, lineAt θ τ (c τ)) f w := by
      rw [L3, M3, Finset.sum_apply, Finset.sum_apply, Finset.mul_sum]
      refine Finset.sum_congr rfl fun τ _ => ?_
      have h : GlobalTheory.WeilVacMove.dLine ψ S T (lineAt θ τ (c τ)) f w +
          Complex.I * GlobalTheory.WeilVacMove.dLine ψ S T (lineAt θ τ (c' τ)) f w = 0 := congrFun (hvac τ (c τ)) w
      linear_combination (-Complex.I) * h + GlobalTheory.WeilVacMove.dLine ψ S T (lineAt θ τ (c' τ)) f w * Complex.I_sq
    simp only [e']
    rw [← key]
    exact hd'

end GlobalTheory.FockLineJ
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormalSquaringPathUniqueOfAgreeLowDegreesStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.VB GlobalTheory.LieVB GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.NeronCurve GlobalTheory.Nef
open GlobalTheory.Twist (resM)
open scoped CategoryTheory.Obj RatFunc

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.formalSquaringPath_unique_of_agree_low_degrees : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] (R : Type) [CommRing R], ∀ [IsLocalRing R], QuasiSeparated G.hom → ∀ (c : R) (n : ℕ), 0 < n → (∀ j, n ≤ j → IsUnit (c ^ j - 2)) → ∀ (b : Sp R ⟶ S) (ξ ξ' : Sp (PowerSeries R) ⟶ G.left), IsPath G c b ξ → IsPath G c b ξ' → (∀ (U : G.left.Opens) (h : ⊤ ≤ ξ ⁻¹ᵁ U) (h' : ⊤ ≤ ξ' ⁻¹ᵁ U) (f : Γ(G.left, U)) (j : ℕ), 0 < j → j < n → PowerSeries.coeff j (evAt ξ h f) = PowerSeries.coeff j (evAt ξ' h' f)) → ξ = ξ' := by
  first | exact @GlobalTheory.Nef.path_unique | exact GlobalTheory.Nef.path_unique | (intros; apply GlobalTheory.Nef.path_unique <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrameMulVecCompletedIdealMemCompletedIdealLattic
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.TestLat GlobalTheory.SumSize GlobalTheory.RowClaim GlobalTheory.ClassCount
open GlobalTheory.FrameTransport
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace GlobalTheory.FrameColSmul

theorem colMul_mem_of_span {A : Type} [CommRing A] (S : Subring A) {ι : Type} (M : Submodule S (ι → A))
    (c : ι → A) (G : Set A) (hG : ∀ y ∈ G, (fun i => c i * y) ∈ M) (x : A)
    (hx : x ∈ Submodule.span S G) : (fun i => c i * x) ∈ M := by
  induction hx using Submodule.span_induction with
  | mem y hy => exact hG y hy
  | zero =>
    have : (fun i => c i * (0 : A)) = 0 := by funext i; simp
    rw [this]; exact M.zero_mem
  | add a b _ _ ha hb =>
    have : (fun i => c i * (a + b)) = (fun i => c i * a) + (fun i => c i * b) := by
      funext i; simp [mul_add]
    rw [this]; exact M.add_mem ha hb
  | smul r a _ ha =>
    have : (fun i => c i * (r • a)) = r • (fun i => c i * a) := by
      funext i
      show c i * ((r : A) * a) = (r : A) * (c i * a)
      exact mul_left_comm _ _ _
    rw [this]; exact M.smul_mem r ha

theorem mulVec_eq_sum_col {A : Type} [CommRing A] {n : ℕ} (P : Matrix (Fin n) (Fin n) A) (w : Fin n → A) :
    P *ᵥ w = ∑ j, (fun i => P i j * w j) := by
  funext i
  simp [Matrix.mulVec, dotProduct, Finset.sum_apply]

theorem map_col_mul {E A : Type} [Field E] [NumberField E] [CommRing A] (φ : E →+* A) {n : ℕ}
    (c : Fin n → E) (b : 𝓞 E) :
    (fun i => φ (c i) * φ (b : E)) = fun i => φ ((b • c) i) := by
  funext i
  show _ = φ ((b : E) * c i)
  rw [map_mul, mul_comm]

theorem gen_mem {D : D7} {n : ℕ} (fr : GL (Fin n) D.host.E) (𝔪 : Ideal (𝓞 D.host.E)) (j : Fin n)
    (b : 𝓞 D.host.E) (hb : b ∈ 𝔪) :
    (fun i => GlobalTheory.FrameTransport.inclEAf D ((fr : Matrix (Fin n) (Fin n) D.host.E) i j) *
        GlobalTheory.FrameTransport.inclEAf D (b : D.host.E)) ∈
      Formalism.L2.Herm.hatL (F := D.host.F) (𝔪 • colLat fr) := by
  have hcol : (fun i => (fr : Matrix (Fin n) (Fin n) D.host.E) i j) ∈ colLat fr :=
    Submodule.subset_span ⟨j, rfl⟩
  have hm : b • (fun i => (fr : Matrix (Fin n) (Fin n) D.host.E) i j) ∈ 𝔪 • colLat fr :=
    Submodule.smul_mem_smul hb hcol
  rw [map_col_mul]
  exact Submodule.subset_span ⟨_, hm, rfl⟩

theorem mulVec_mem : ∀ {D : D7} {n : ℕ} (fr : GL (Fin n) D.host.E) (𝔪 : Ideal (𝓞 D.host.E)) (w : Fin n → Lev.EAf D), (∀ i, w i ∈ Submodule.span (Formalism.L2.Herm.intAf D.host.F D.host.E) ((fun b : 𝓞 D.host.E => GlobalTheory.FrameTransport.inclEAf D (b : D.host.E)) '' (𝔪 : Set (𝓞 D.host.E)))) → (Formalism.UG.bc (GlobalTheory.FrameTransport.inclEAf D) fr).val *ᵥ w ∈ Formalism.L2.Herm.hatL (F := D.host.F) (𝔪 • colLat fr) := by
  intro D n fr 𝔪 w hw
  rw [mulVec_eq_sum_col]
  refine Submodule.sum_mem _ fun j _ => ?_
  exact colMul_mem_of_span (Formalism.L2.Herm.intAf D.host.F D.host.E) _
    (fun i => GlobalTheory.FrameTransport.inclEAf D ((fr : Matrix (Fin n) (Fin n) D.host.E) i j)) _
    (by
      rintro _ ⟨b, hb, rfl⟩
      exact gen_mem fr 𝔪 j b hb) (w j) (hw j)

end GlobalTheory.FrameColSmul
end
end

