import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.DiscreteSpectrumResidualClassification
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2010
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle0001
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0575
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0593
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0618
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0633
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0591
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0613
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0598
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0617
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0597

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.LocalCharacterPowerConductorBound
section
section
open GlobalTheory.SumSize GlobalTheory.RowClaim GlobalTheory.ArchTens
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.ConjSize ValuativeRel
open Formalism.L2.Host GlobalTheory.StepData
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc}
private theorem additive_character_pow_conductor {W : G.Weil} {w : Pl D.host.E} (hc : HasConductor (psiAt W w) 1) (n : ℕ) (x : Kw w)
    (hx : valuation (Kw w) ((((unifAt w) ^ n : (Kw w)ˣ) : Kw w) * x) ≤ 1) :
    (psiAt W w x : ℂ) ^ (Ideal.absNorm w.asIdeal ^ n) = 1 := by
  have e := GivenAdm.isEquiv_val w
  set q := Ideal.absNorm w.asIdeal
  have hq : Valued.v ((q : ℕ) : Kw w) ≤ WithZero.exp (-1 : ℤ) := by
    have hmem : ((q : ℕ) : 𝓞 D.host.E) ∈ w.asIdeal ^ 1 := by rw [pow_one]; exact Ideal.absNorm_mem w.asIdeal
    have h2 : Valued.v ((q : ℕ) : Kw w) = w.intValuation ((q:ℕ) : 𝓞 D.host.E) := by
      rw [← map_natCast (algebraMap (𝓞 D.host.E) (Kw w))]
      exact (IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation (K := D.host.E) w _).trans
        (IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap _ _)
    rw [h2]
    have := (w.intValuation_le_pow_iff_mem ((q:ℕ) : 𝓞 D.host.E) 1).2 hmem
    simpa using this
  have hu : Valued.v ((unifAt w : (Kw w)ˣ) : Kw w) = WithZero.exp (-1 : ℤ) := unif_spec w
  have hx' : Valued.v ((((unifAt w) ^ n : (Kw w)ˣ) : Kw w) * x) ≤ 1 := by
    have := (e ((((unifAt w) ^ n : (Kw w)ˣ) : Kw w) * x) 1).1 (by rw [map_one]; exact hx)
    rwa [map_one] at this
  have hNx : Valued.v (((q ^ n : ℕ) : Kw w) * x) ≤ 1 := by
    refine le_trans ?_ hx'
    rw [map_mul, map_mul, Units.val_pow_eq_pow_val, map_pow, Nat.cast_pow, map_pow, hu]
    gcongr
  have hNx2 : valuation (Kw w) (((q ^ n : ℕ) : Kw w) * x) ≤ valuation (Kw w) 1 :=
    (e (((q ^ n : ℕ) : Kw w) * x) 1).2 (by rw [map_one]; exact hNx)
  have h1 : psiAt W w ((q ^ n) • x) = 1 := by
    rw [nsmul_eq_mul]
    exact (hc 1).2 (by simp) _ hNx2
  rw [← Circle.coe_pow, ← AddChar.map_nsmul_eq_pow, h1, Circle.coe_one]
private theorem congruence_le_given_level {μ₀ : T} (hL : L.Is μ₀) {t : T} {w : Pl D.host.E} (hw : w ∈ locPl G t)
    (he : depthAt G w = cosExp G w) (X : ℕ × ℕ) :
    glLatCong (unifAt w ^ depthAt G w) (GlobalTheory.SplitFlip.stdLat (Kw w) _) ≤ givenLevel G t w X := by
  obtain ⟨i, _ | j⟩ := X
  · rw [givenLevel, he]
  · rcases i with _ | i
    · obtain ⟨P, hP, -⟩ := GivenAdm.exists_types hL hw
      rw [GivenAdm.givenLevel_succ (hP _)]
      refine le_trans (fun g hg => mem_KOne.2 fun a b => ((GivenAdm.mem_glLatCong.1 hg).2 a b).trans_lt ?_)
        (TypeDatum.KOne_le _)
      rw [Units.val_pow_eq_pow_val, map_pow]
      exact pow_lt_one₀ zero_le' (isUnif_unifAt w ▸ uniformizer_lt_one) (by rw [depthAt]; omega)
    · exact fun g hg => (GivenAdm.mem_glLatCong.1 hg).1
private theorem local_grid_entries_unitary {K : Type} [Field K] {ι τ : K →+* ℂ} (t : T) (w : Pl D.host.E)
    (hmu : ∀ j x, Un ι τ ((L.C.mu0 j).loc w x : ℂ)) (hxi : ∀ x, Un ι τ ((L.xiH t).loc w x : ℂ))
    (hchi : ∀ i, 1 ≤ i → i ≤ D.R.m → ∀ x, Un ι τ ((G.ch.chiH i).loc w x : ℂ))
    {i j : ℕ} (hi : i < D.R.m) (hj : j < D.R.m) (u : (Kw w)ˣ) : Un ι τ ((locGrid G t w).nu i j u : ℂ) := by
  have e1 : (((locGrid G t w).nu i j u : ℂˣ) : ℂ) =
      ((L.C.mu0 ⟨j, hj⟩).loc w u : ℂ) * ((L.xiH t).loc w u : ℂ) * (((G.ch.chiH (D.R.m - i)).loc w u : ℂ))⁻¹ := by
    simp only [Grid.nu, locGrid, muBase, dif_pos hj, MonoidHom.div_apply, Units.val_div_eq_div_val, div_eq_mul_inv]
    simp [HChar.loc]
  rw [e1]
  exact ((hmu _ _).mul (hxi _)).mul (hchi _ (by omega) (by omega) _).inv
private theorem local_grid_rank_le (t : T) (w : Pl D.host.E) {i j : ℕ} (hi : i < D.R.m) (hj : j < D.R.m) :
    (locGrid G t w).rank (i + 1, j + 1) ≤ 2 * bigN D := by
  change D.R.r + (j + 1) * D.R.t + (i + 1) * sLen D ≤ 2 * bigN D
  have h1 : (j + 1) * D.R.t ≤ D.R.m * D.R.t := Nat.mul_le_mul_right _ hj
  have h2 : (i + 1) * sLen D ≤ D.R.m * sLen D := Nat.mul_le_mul_right _ hi
  have h3 : 1 * sLen D ≤ D.R.m * sLen D := Nat.mul_le_mul_right _ (by omega)
  have h4 : D.R.r ≤ sLen D := Nat.le_add_right _ _
  unfold bigN
  rw [mul_add D.R.m, mul_add D.R.m]
  omega
end
open Formalism.BasicNotions Formalism.IndefR.Links Formalism.L2.DIV NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.ConjSize in
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw in
theorem _root_.GlobalTheory.T.local_character_power_conductor_bound : _root_.GlobalTheory.FunPr.ThetaLocalInputs → BigC fun _ ch C _ => FlipAt ch C := by
  refine fun _ => ⟨0, fun CF _ => ⟨48, fun ε C hC => ⟨0, ?_⟩⟩⟩
  intro D large₂ _ _ Γ _ _ Pl0 T A Ks _ _ _ R F hS ch hch _ hF σ Φ w₀ z
  obtain ⟨w, hw⟩ := w₀
  haveI : IsCMField D.host.E := D.host.isCMField_hostE
  have hL : R.toLevCh.Is A.μ0 := hS.core.lev
  have hde := GlobalTheory.FlipIntegrand.pde_ne_q_of_setting hS
  have hc : ∀ P ∈ R.toLevCh.Q A.μ0, ((Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal := hch.guard A.μ0
  have hg := (Good.locGrid_isGood hL ch.G ch.W A.μ0 hde hc).1 w hw
  have hadm := GivenAdm.givenStage_isAdmissible hL ch.S.B A.μ0 Φ hw
  have hm : 0 < D.R.m := by have := D.R.two_le_m; omega
  have h00 := hg.square 0 hm 0 hm
  have hW : w ∈ ch.G.pl.W0 := (GivenAdm.mem_locPl.1 hw).resolve_right fun h =>
    (hL.Q_ram A.μ0 w).2 (.inl h) (by rw [hL.xi_base]; exact fun _ _ => rfl)
  have he : depthAt ch.G w = cosExp ch.G w := by
    obtain ⟨h1, h2⟩ := GivenAdm.under_mem_and_place_above_eq_of_mem hW
    have := depthAt_w ch.G h1
    rw [h2] at this
    rw [this.1, this.2]
  have hmu : ∀ j x, Un D.what₂.embLL σ ((R.toLevCh.C.mu0 j).loc w x : ℂ) := fun j x => by
    obtain ⟨n, -, hn⟩ := (R.toLevCh.C.isMu0 j).inf
    exact UpperTheory.conjSize_heckeChar_local_of_mem_range_embedding _ _ _ _ hn _ _ _ _ (hF.chars.mu0 j w x)
  have hxi : ∀ x, Un D.what₂.embLL σ ((R.toLevCh.xiH A.μ0).loc w x : ℂ) := fun x => by
    rw [hL.xi_base]; exact Un.one
  have hchi : ∀ i, 1 ≤ i → i ≤ D.R.m → ∀ x, Un D.what₂.embLL σ ((ch.G.ch.chiH i).loc w x : ℂ) :=
    fun i a b x => UpperTheory.conjSize_heckeChar_local_of_mem_range_embedding _ _ _ _ (ch.G.ch.inf i a b) _ _ _ _ (hF.chars.chi i a b w x)
  have habs : ∀ u : (Kw w)ˣ, apow u (1 / 2) ∈ Set.range D.what₂.embLL := fun u =>
    RingHom.mem_fieldRange.1 (GlobalTheory.TflipField.apow_half_mem D.what₂.embLL.fieldRange w
      (RingHom.mem_fieldRange.2 (hF.sqrt w (.inr ⟨A.μ0, hw⟩))) u)
  have hq0 : Ideal.absNorm w.asIdeal ≠ 0 := fun h => w.ne_bot (Ideal.absNorm_eq_zero_iff.1 h)
  have hψ := fun x hx => (fun h => Un.of_pow_eq_one (τ := σ) (hF.roots A.μ0 w hw _ h) (pow_ne_zero _ hq0) h)
    (additive_character_pow_conductor (W := ch.W) h00.cond (depthAt ch.G w) x hx)
  have hν : ∀ x ∈ flipOrder D.R.m, (locGrid ch.G A.μ0 w).rank (x.1 + 1, x.2 + 1) ≤ 2 * bigN D ∧
      CondLE (unifAt w) (depthAt ch.G w) ((locGrid ch.G A.μ0 w).nu x.1 x.2) ∧
      ¬ IsUnram ((locGrid ch.G A.μ0 w).nu x.1 x.2) ∧ ∀ u, Un D.what₂.embLL σ ((locGrid ch.G A.μ0 w).nu x.1 x.2 u : ℂ) := by
    intro x hx
    simp only [flipOrder, List.mem_flatMap, List.mem_map, List.mem_range] at hx
    obtain ⟨i, hi, j, hj, rfl⟩ := hx
    have hs := hg.square i hi j hj
    have e := (locGrid ch.G A.μ0 w).alpha_div_beta i j
    exact ⟨local_grid_rank_le _ _ hi hj, by rw [← e]; exact hs.condν, by rw [← e]; exact hs.ram, local_grid_entries_unitary _ w hmu hxi hchi hi hj⟩
  have key := sz_flips h00.unif h00.cond h00.one_le habs hψ (2 * bigN D) (flipOrder D.R.m)
    (givenStage A.μ0 w ch.S.B Φ) 1 hν (canFlip_flipOrder _).1
    (fun X => ⟨(GivenAdm.givenLevel_open hL hw X).1, (GivenAdm.givenLevel_open hL hw X).2, congruence_le_given_level hL hw he X⟩)
    hadm.tensor (UpperTheory.localGrid_tensor_size_le_one_of_unimodular _ _ ch.S.B A.μ0 Φ w hmu hxi) z
  refine key.mono ?_
  rw [mul_one, (canFlip_flipOrder _).2.1, ResidueCardinalityNilpotence.GlobalTheory.CompanionTheory.ResCardPlace.resCard_Kw, he,
    ← Real.exp_log (pow_pos (by exact_mod_cast Nat.pos_of_ne_zero hq0) _), Real.log_pow, Real.exp_le_exp]
  have h1 := ResidueCardinalityNilpotence.GlobalTheory.CompanionTheory.VolVal.log_absNorm_le w
  have h2 := placeSz_nonneg ch.G w
  calc _ ≤ ((6 * cosExp ch.G w * (2 * bigN D) ^ 2 * D.R.m ^ 2 : ℕ) : ℝ) *
        (2 * Real.log (Ideal.absNorm (w.under (𝓞 D.host.F)).asIdeal)) := mul_le_mul_of_nonneg_left h1 (Nat.cast_nonneg _)
    _ = 48 * (D.R.m : ℝ) ^ 2 * (bigN D : ℝ) ^ 2 * placeSz ch.G w := by rw [placeSz]; push_cast; ring
    _ ≤ _ := by gcongr
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.MovedVacuumJetAlgebraicCombination
section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx MeasureTheory
noncomputable section
namespace GlobalTheory.MovedJet
open GlobalTheory.Grid (neg sgn ofSgn)
open MvPolynomial
end GlobalTheory.MovedJet
namespace GlobalTheory.MovedJet
open GlobalTheory.Grid (neg sgn ofSgn)
open MvPolynomial
end GlobalTheory.MovedJet
namespace GlobalTheory.MovedJet
open GlobalTheory.Grid (neg sgn ofSgn)
open MvPolynomial
theorem jet_moved_vacuum_algebraic : ∀ {D : D7} {T : Type} [Finite T] {L : LevCh D T} {μ₀ : T} {sc : Consts} {G : GridData L sc} {W : G.Weil}
    {i j : Fin D.R.m} {A A' WW : HSp D} {X : Tri T A A' WW}, _root_.GlobalTheory.FunPr.ThetaLocalInputs → (∀ D, GlobalTheory.NormSum.Inp D) → L.Is μ₀ →
    IsBottomTri W i j X → ∀ (t : T), ∀ γ ∈ Formalism.L2.Theta.GQ A, ∀ a ∈ GinfC A, ∀ γ' ∈ Formalism.L2.Theta.GQ WW, ∀ a' ∈ GinfC WW,
      γ * a ∈ GfC A → γ' * a' ∈ GfC WW →
      ∀ k : FVar D WW.rank A.rank →₀ ℕ, ∃ (n : ℕ) (c : Fin n → ℂ) (k' : Fin n → FVar D WW.rank A.rank →₀ ℕ),
        (∀ p, IsAlgebraic ℚ (c p)) ∧ (∀ p, Finsupp.mapDomain Prod.fst (k' p) = Finsupp.mapDomain Prod.fst k) ∧
        pureTensorO W.ψ W.θ (GlobalTheory.Grid.neg A) WW (fun τ => -X.rA.s τ) X.rW.s X.rA.B X.rW.B (X.ω t (γ, γ') X.vac) (MvPolynomial.monomial k 1) 0 = ∑ p, c p * pureTensorO W.ψ W.θ (GlobalTheory.Grid.neg A) WW (fun τ => -X.rA.s τ) X.rW.s X.rA.B X.rW.B (X.vac) (MvPolynomial.monomial (k' p) 1) 0 := by
  intro D T _ L μ₀ sc G W i j A A' WW X _ _ _ hX t γ hγ a _ γ' hγ' a' _ _ _ k
  have hI := hX.is
  have hθ : IsInfFam W.θ := hI.isVac.2.inf
  have hom := hI.weil t
  set u : D.what₂.Tau → Matrix (Fin A.rank) (Fin A.rank) ℂ := fun τ => compAt W.θ τ (Formalism.L2.Theta.mt A γ) with hu
  set hm : D.what₂.Tau → Matrix (Fin WW.rank) (Fin WW.rank) ℂ :=
    fun τ => (compAt W.θ τ (Formalism.L2.Theta.mt WW γ')).map (starRingEnd ℂ) with hhm
  set H : D.what₂.Tau → Matrix (Fin WW.rank) (Fin WW.rank) ℂ := fun τ => Matrix.conjTranspose (hm τ) with hH
  set U : D.what₂.Tau → Matrix (Fin A.rank) (Fin A.rank) ℂ := fun τ => Matrix.conjTranspose (u τ) with hU
  set Q := GlobalTheory.CompactHowe.substF H U (MvPolynomial.monomial k 1) with hQdef
  have hHm : hm * H = fun _ => 1 := funext fun τ =>
    map_conj_mul_conjT (mul_conjT_of_unitary (conjT_mul_compAt hθ hX.stdW.1 γ' τ))
  have hUm : u * U = fun _ => 1 := funext fun τ => mul_conjT_of_unitary (conjT_mul_compAt hθ hX.std.1 γ τ)
  have hQ : GlobalTheory.CompactHowe.substF hm u Q = MvPolynomial.monomial k 1 := by
    rw [hQdef, GlobalTheory.CompactHowe.substF_mul, hHm, hUm, substF_one]
  have hact := om_pureTensorO_vac hX t γ γ' Q
  have hjet : pureTensorO W.ψ W.θ (neg A) WW (fun τ => -X.rA.s τ) X.rW.s X.rA.B X.rW.B (X.ω t (γ, γ') X.vac)
        (MvPolynomial.monomial k 1) 0 =
      pureTensorO W.ψ W.θ (neg A) WW (fun τ => -X.rA.s τ) X.rW.s X.rA.B X.rW.B X.vac Q 0 := by
    rw [← hQ]
    change pureTensorO W.ψ W.θ (neg A) WW (fun τ => -X.rA.s τ) X.rW.s X.rA.B X.rW.B
      ((X.ω t).toSgn true ((ofSgn true A).symm γ, γ') X.vac) _ 0 = _
    rw [← hact.2]
    exact hom.om_aut _ (GlobalTheory.SquareComm.ofSgn_symm_mem_GQ true hγ) γ' hγ' _ hact.1
  have hHalg : ∀ τ a b, IsAlgebraic ℚ (H τ a b) := by
    intro τ a b
    have e : H τ a b = compAt W.θ τ (Formalism.L2.Theta.mt WW γ') b a := by
      simp [hH, hhm, Matrix.conjTranspose_apply]
    rw [e]
    exact isAlgebraic_compAt_of_mem_GQ hθ hγ' τ b a
  have hUalg : ∀ τ a b, IsAlgebraic ℚ (U τ a b) := by
    intro τ a b
    have e : U τ a b = starRingEnd ℂ (compAt W.θ τ (Formalism.L2.Theta.mt A γ) b a) := by
      simp [hU, hu, Matrix.conjTranspose_apply]
    rw [e]
    exact isAlgebraic_conj (isAlgebraic_compAt_of_mem_GQ hθ hγ τ b a)
  let e := Q.support.equivFin
  refine ⟨Q.support.card, fun p => MvPolynomial.coeff (e.symm p).1 Q, fun p => (e.symm p).1, fun p => ?_, fun p => ?_, ?_⟩
  · exact (GlobalTheory.SubstCoeff.coeff_substF_monomial_continuous_algebraic k (e.symm p).1).2 H U hHalg hUalg
  · exact GlobalTheory.CompactHowe.mapDomain_fst_eq_of_coeff_substF_ne_zero H U k (e.symm p).1
      (MvPolynomial.mem_support_iff.1 (e.symm p).2)
  · rw [hjet]
    calc pureTensorO W.ψ W.θ (neg A) WW (fun τ => -X.rA.s τ) X.rW.s X.rA.B X.rW.B X.vac Q 0
        = ∑ x ∈ Q.support, MvPolynomial.coeff x Q *
            pureTensorO W.ψ W.θ (neg A) WW (fun τ => -X.rA.s τ) X.rW.s X.rA.B X.rW.B X.vac (MvPolynomial.monomial x 1) 0 := by
          conv_lhs => rw [Q.as_sum]
          rw [map_sum, Finset.sum_apply]
          refine Finset.sum_congr rfl fun x _ => ?_
          rw [show MvPolynomial.monomial x (MvPolynomial.coeff x Q) = MvPolynomial.coeff x Q • MvPolynomial.monomial x 1 by
            rw [MvPolynomial.smul_monomial, smul_eq_mul, mul_one], map_smul, Pi.smul_apply, smul_eq_mul]
      _ = _ := by
          rw [← Finset.sum_coe_sort]
          exact (Equiv.sum_comp e.symm (fun x : Q.support => MvPolynomial.coeff x.1 Q *
            pureTensorO W.ψ W.θ (neg A) WW (fun τ => -X.rA.s τ) X.rW.s X.rA.B X.rW.B X.vac (MvPolynomial.monomial x.1 1) 0)).symm
end GlobalTheory.MovedJet
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.moved_vacuum_jet_algebraic_combination : ∀ {D : D7} {T : Type} [Finite T] {L : LevCh D T} {μ₀ : T} {sc : Consts} {G : GridData L sc} {W : G.Weil}
    {i j : Fin D.R.m} {A A' WW : HSp D} {X : Tri T A A' WW}, _root_.GlobalTheory.FunPr.ThetaLocalInputs → (∀ D, GlobalTheory.NormSum.Inp D) → L.Is μ₀ →
    IsBottomTri W i j X → ∀ (t : T), ∀ γ ∈ Formalism.L2.Theta.GQ A, ∀ a ∈ GinfC A, ∀ γ' ∈ Formalism.L2.Theta.GQ WW, ∀ a' ∈ GinfC WW,
      γ * a ∈ GfC A → γ' * a' ∈ GfC WW →
      ∀ k : FVar D WW.rank A.rank →₀ ℕ, ∃ (n : ℕ) (c : Fin n → ℂ) (k' : Fin n → FVar D WW.rank A.rank →₀ ℕ),
        (∀ p, IsAlgebraic ℚ (c p)) ∧ (∀ p, Finsupp.mapDomain Prod.fst (k' p) = Finsupp.mapDomain Prod.fst k) ∧
        pureTensorO W.ψ W.θ (GlobalTheory.Grid.neg A) WW (fun τ => -X.rA.s τ) X.rW.s X.rA.B X.rW.B (X.ω t (γ, γ') X.vac) (MvPolynomial.monomial k 1) 0 = ∑ p, c p * pureTensorO W.ψ W.θ (GlobalTheory.Grid.neg A) WW (fun τ => -X.rA.s τ) X.rW.s X.rA.B X.rW.B (X.vac) (MvPolynomial.monomial (k' p) 1) 0 := by
  first | exact @_root_.GlobalTheory.MovedJet.jet_moved_vacuum_algebraic | exact _root_.GlobalTheory.MovedJet.jet_moved_vacuum_algebraic | (intros; apply _root_.GlobalTheory.MovedJet.jet_moved_vacuum_algebraic <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.NormSumCoefficientsIsAlgebraic
section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx MeasureTheory
noncomputable section
namespace GlobalTheory.NormSum.CoordAlg
open Classical Formalism.UG Formalism.UG.P Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.NormSum.IntOver GlobalTheory.NormSum.RepAt GlobalTheory.NormSum.PtsMem
theorem normSum_coordinate_isAlgebraic : _root_.GlobalTheory.FunPr.ThetaLocalInputs → (∀ D, GlobalTheory.NormSum.Inp D) → ∀ (D : D7) (δ t0 : ℂ) (Q : ℕ) (P : GlobalTheory.NormSum.Pair D ⊤ δ t0 Q)
    (h : Formalism.MainNotions.StandardLatticesGL3.GA D P.d) (U : GlobalTheory.NormSum.Tup D P.a P.d P.n), IsAlgebraic ℚ (P.coord h U) := by
  intro _hPr hI D δ t0 Q P h U
  obtain ⟨S, dl, hL⟩ := GlobalTheory.NormSum.Denom.exists_letters D
  obtain ⟨p, hpQ, hp, k', hk', htr⟩ := exists_prime_integralOver_gt D P.d h Q
  haveI : Fact p.Prime := ⟨hp⟩
  have hQ0 := P.level_pos
  have hsp : p ∣ Q → SplitIn D p := fun hd => absurd (Nat.le_of_dvd hQ0 hd) (by omega)
  obtain ⟨hterm, -, -⟩ := GlobalTheory.T.definiteThetaPair_terms_norms_independent_representatives D (hI D) ⊤ δ t0 Q P.crv P.pt0 P hQ0
  have hmem : P.coord h U ∈ Qbar := by
    unfold Pair.coord
    refine finsum_induction (· ∈ Qbar) (zero_mem _) (fun x y => add_mem) (fun x => ?_)
    refine mul_mem (inv_mem (natCast_mem _ _)) ?_
    obtain ⟨γ, k, γ', h1, h2, h3⟩ := (hI D).rep P.a p hp x.out
    rw [← hterm γ (Subgroup.subset_closure ⟨γ', h1⟩) k (Subgroup.subset_closure h2)]
    exact (CoordBound.term_bound_of_jets GlobalTheory.T.jets_torsion_translates_cm_theta_product D (hI D) S dl hL δ t0 Q P p hsp
      (CoordBound.nonempty_place p).some _ h k' hk' h3 htr U).1
  exact mem_algebraicClosure_iff.1 hmem
end GlobalTheory.NormSum.CoordAlg
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.normSum_coefficients_isAlgebraic : _root_.GlobalTheory.FunPr.ThetaLocalInputs → (∀ D, GlobalTheory.NormSum.Inp D) → ∀ (D : D7) (δ t0 : ℂ) (Q : ℕ) (P : GlobalTheory.NormSum.Pair D ⊤ δ t0 Q)
    (h : Formalism.MainNotions.StandardLatticesGL3.GA D P.d) (U : GlobalTheory.NormSum.Tup D P.a P.d P.n), IsAlgebraic ℚ (P.coord h U) := by
  first | exact @_root_.GlobalTheory.NormSum.CoordAlg.normSum_coordinate_isAlgebraic | exact _root_.GlobalTheory.NormSum.CoordAlg.normSum_coordinate_isAlgebraic | (intros; apply _root_.GlobalTheory.NormSum.CoordAlg.normSum_coordinate_isAlgebraic <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.PlaceDecompositionExistsExponentialModel
section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.Grow GlobalTheory.Size
open Formalism.REAL Formalism.MainNotions.S GlobalTheory.SmoothGlob GlobalTheory.LowTypeDetermined GlobalTheory.TypeSum GlobalTheory.SeriesToClosure GlobalTheory.PlaceDecomp GlobalTheory.KFinDecomp Matrix
open scoped InnerProductSpace
noncomputable section
namespace GlobalTheory.PlaceDecomp
theorem placeDecomposition_exists_exponential_model : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (N : GlobalTheory.Grid.Node D) (τ : D.what₂.Tau) (f : GA D N.V → ℂ), IsAutFunSm θ N.V f → IsTypeAt θ N.V τ (N.S τ) f → ∀ x : GA D N.V, ∃ (S : List (List (Mx N.V.rank))) (v : ℕ → N.M.H τ) (ℓ : ℕ → (N.M.H τ →ₗ[ℂ] ℂ)) (C : ℕ → ℝ), Words (lieSet (N.M.ε τ)) S ∧ Ctrl (lieSet (N.M.ε τ)) (UJset (N.M.ε τ)) (N.M.σ τ) S ∧ Expn (N.M.ε τ) (N.M.σ τ) S v ℓ C (res θ N.V τ (N.M.fr τ) f x) := by
  intro D θ hθ hPr N τ f hf hty x
  obtain ⟨H', i1, i2, σ', lam', ε', P', hE', hD', hP', hJ', hx⟩ := hty
  obtain ⟨hl, he⟩ := GlobalTheory.SignedParTest.isEnum_unique (N.M.enum τ) hE'
  subst hl he
  obtain ⟨U, hU⟩ := hPr.discreteSeriesHermitianUnique _ (N.M.ε τ) (N.M.lam τ)
    (GlobalTheory.Published.HermitianUnique.isHCParam_of_isDS (N.M.enum τ).1 (N.M.ds τ)) _ (N.M.fr τ) P'
    (N.M.fr_unit τ) hP' (N.M.fr_gram τ) hJ' _ _ (N.M.σ τ) σ' (N.M.ds τ) hD'
  have t := GlobalTheory.TypeSum.hasTypeAll_transport _ H' (N.M.H τ) (fun g => σ' (P' * g * P'⁻¹)) (N.M.σ τ)
    (gramAt D N.V τ) (Formalism.REAL.Jm (N.M.ε τ)) (N.M.fr τ) (isUnit_gram (N.M.fr_unit τ) (N.M.fr_gram τ))
    (N.M.fr_unit τ) (N.M.fr_gram τ) U hU (fun g => f (x * atTau θ N.V τ g))
    (GlobalTheory.TypeSum.hasTypeAll_iff.2 (hx x))
  obtain ⟨S, hS, hc, v, ℓ, C, h⟩ := t
  exact ⟨S, v, ℓ, C, hS, hc, h⟩
end GlobalTheory.PlaceDecomp
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.Grow GlobalTheory.Size
open Formalism.REAL Formalism.MainNotions.S GlobalTheory.SmoothGlob GlobalTheory.LowTypeDetermined GlobalTheory.TypeSum GlobalTheory.SeriesToClosure GlobalTheory.PlaceDecomp GlobalTheory.KFinDecomp Matrix
open scoped InnerProductSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twist_exists_exponential_model : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (N : GlobalTheory.Grid.Node D) (τ : D.what₂.Tau) (f : GA D N.V → ℂ), IsAutFunSm θ N.V f → IsTypeAt θ N.V τ (N.S τ) f → ∀ x : GA D N.V, ∃ (S : List (List (Mx N.V.rank))) (v : ℕ → N.M.H τ) (ℓ : ℕ → (N.M.H τ →ₗ[ℂ] ℂ)) (C : ℕ → ℝ), Words (lieSet (N.M.ε τ)) S ∧ Ctrl (lieSet (N.M.ε τ)) (UJset (N.M.ε τ)) (N.M.σ τ) S ∧ Expn (N.M.ε τ) (N.M.σ τ) S v ℓ C (res θ N.V τ (N.M.fr τ) f x) := by
  first | exact @_root_.GlobalTheory.PlaceDecomp.placeDecomposition_exists_exponential_model | exact _root_.GlobalTheory.PlaceDecomp.placeDecomposition_exists_exponential_model | (intros; apply _root_.GlobalTheory.PlaceDecomp.placeDecomposition_exists_exponential_model <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.PlaceDecompositionGkMapRankOneValues
section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.Grow GlobalTheory.Size
open Formalism.REAL Formalism.MainNotions.S GlobalTheory.SmoothGlob GlobalTheory.LowTypeDetermined GlobalTheory.TypeSum GlobalTheory.SeriesToClosure GlobalTheory.PlaceDecomp GlobalTheory.KFinDecomp Matrix
open scoped InnerProductSpace
namespace GlobalTheory.PlaceDecomp
theorem placeDecomposition_gkMap_rankOne_values : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (N : GlobalTheory.Grid.Node D) (τ : D.what₂.Tau) (φ : GA D N.V → ℂ) (S : GA D N.V → List (List (Mx N.V.rank))) (v : GA D N.V → ℕ → N.M.H τ) (ℓ : GA D N.V → ℕ → (N.M.H τ →ₗ[ℂ] ℂ)) (C : GA D N.V → ℕ → ℝ), (∀ x, Words (lieSet (N.M.ε τ)) (S x)) → (∀ x, Ctrl (lieSet (N.M.ε τ)) (UJset (N.M.ε τ)) (N.M.σ τ) (S x)) → (∀ x, Expn (N.M.ε τ) (N.M.σ τ) (S x) (v x) (ℓ x) (C x) (res θ N.V τ (N.M.fr τ) φ x)) → ∀ (c : N.M.H τ) (ψ : GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.kFin N.M τ → GA D N.V → ℂ), (∀ u : GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.kFin N.M τ, Moves θ N.V τ (N.M.ε τ) (N.M.σ τ) (N.M.fr τ) (fun w => ⟪c, w⟫_ℂ • (u : N.M.H τ)) φ (ψ u)) → (∀ u x, ψ u x = ∑' i, ⟪c, v x i⟫_ℂ * ℓ x i u) ∧ (∀ u u', ψ (u + u') = ψ u + ψ u') ∧ (∀ (z : ℂ) u, ψ (z • u) = z • ψ u) ∧ (∀ k ∈ GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.maxCpt N.M τ, ∀ u w : GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.kFin N.M τ, (w : N.M.H τ) = N.M.rep τ k u → ψ w = rTr N.V (atTau θ N.V τ k) (ψ u)) ∧ (∀ X ∈ lieAt N.V τ, ∀ u w : GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.kFin N.M τ, (w : N.M.H τ) = dRep (N.M.rep τ) X u → ψ w = Rder θ N.V τ X (ψ u)) := by
  intro D θ hθ hp N τ φ S v ℓ C hS hc h c ψ hψ
  have hσ : Std (N.M.ε τ) (N.M.σ τ) := std_of_isDS hp.harishChandraModules (N.M.ds τ)
  have hP := N.M.fr_unit τ
  haveI : CompleteSpace (N.M.H τ) := (N.M.ds τ).1
  have hJ := N.M.fr_gram τ
  have hb := fun x => (h x).sobFun (hS x) c
  have hsm : ∀ u : GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.kFin N.M τ, Sm (N.M.ε τ) (N.M.σ τ) u := fun u => hσ.2.2.1 _ u.2
  have key : ∀ u x, ∀ y ∈ UJset (N.M.ε τ),
      res θ N.V τ (N.M.fr τ) (ψ u) x y = ∑' i, ⟪c, v x i⟫_ℂ * ℓ x i (N.M.σ τ y u) := by
    intro u x y hy
    have := (hψ u x _ _ _ _ (hS x) (hc x) (h x)).1.2.2.2.2 y hy
    simp only [map_smul, smul_eq_mul] at this
    exact this.tsum_eq.symm
  have hval : ∀ u x, ψ u x = ∑' i, ⟪c, v x i⟫_ℂ * ℓ x i u := by
    intro u x
    have := key u x 1 (one_mem_UJ _)
    rwa [res_one hθ hP, sigma_one hσ.1] at this
  refine ⟨hval, fun u u' => funext fun x => ?_, fun z u => funext fun x => ?_, ?_, ?_⟩
  · rw [Pi.add_apply, hval, hval, hval, Submodule.coe_add]
    exact (hb x).1 _ _ (hsm u) (hsm u')
  · rw [Pi.smul_apply, hval, hval, Submodule.coe_smul, smul_eq_mul]
    exact (hb x).2.1 z _ (hsm u)
  · intro k hk u w hw
    funext x
    rw [rTr, ← res_conj hP (ψ u) x k, key u x _ (K_le_UJ hk), hval, hw]
    rfl
  · intro X hX u w hw
    funext x
    have hd := (isUnit_iff_isUnit_det _).1 hP
    have hY : N.M.fr τ * X * (N.M.fr τ)⁻¹ ∈ lieSet (N.M.ε τ) := by
      refine Transport.conj_lie (G := gramAt D N.V τ) (Matrix.nonsing_inv_mul _ hd) ?_ hX
      rw [← hJ]
      calc _ = (N.M.fr τ * (N.M.fr τ)⁻¹)ᴴ * Jm (N.M.ε τ) * (N.M.fr τ * (N.M.fr τ)⁻¹) := by
            simp only [conjTranspose_mul, Matrix.mul_assoc]
        _ = _ := by rw [Matrix.mul_nonsing_inv _ hd]; simp
    have e : (w : N.M.H τ) = dRep (N.M.σ τ) (N.M.fr τ * X * (N.M.fr τ)⁻¹) u := by
      rw [hw]
      unfold dRep
      congr 1
      funext t
      rw [Transport.exp_smul_conj hP]
      rfl
    have h1 := (hσ.hasDerivAt_sobFun (hb x) (hsm u) hY).deriv
    rw [← e] at h1
    rw [hval]
    refine h1.symm.trans ?_
    unfold Rder oneP
    congr 1
    funext t
    rw [← res_conj hP (ψ u) x, ← Transport.exp_smul_conj hP, key u x _ (exp_mem_UJ hY t)]
end GlobalTheory.PlaceDecomp
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.Grow GlobalTheory.Size
open Formalism.REAL Formalism.MainNotions.S GlobalTheory.SmoothGlob GlobalTheory.LowTypeDetermined GlobalTheory.TypeSum GlobalTheory.SeriesToClosure GlobalTheory.PlaceDecomp GlobalTheory.KFinDecomp Matrix
open scoped InnerProductSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twist_gkMap_rankOne_values : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (N : GlobalTheory.Grid.Node D) (τ : D.what₂.Tau) (φ : GA D N.V → ℂ) (S : GA D N.V → List (List (Mx N.V.rank))) (v : GA D N.V → ℕ → N.M.H τ) (ℓ : GA D N.V → ℕ → (N.M.H τ →ₗ[ℂ] ℂ)) (C : GA D N.V → ℕ → ℝ), (∀ x, Words (lieSet (N.M.ε τ)) (S x)) → (∀ x, Ctrl (lieSet (N.M.ε τ)) (UJset (N.M.ε τ)) (N.M.σ τ) (S x)) → (∀ x, Expn (N.M.ε τ) (N.M.σ τ) (S x) (v x) (ℓ x) (C x) (res θ N.V τ (N.M.fr τ) φ x)) → ∀ (c : N.M.H τ) (ψ : GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.kFin N.M τ → GA D N.V → ℂ), (∀ u : GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.kFin N.M τ, Moves θ N.V τ (N.M.ε τ) (N.M.σ τ) (N.M.fr τ) (fun w => ⟪c, w⟫_ℂ • (u : N.M.H τ)) φ (ψ u)) → (∀ u x, ψ u x = ∑' i, ⟪c, v x i⟫_ℂ * ℓ x i u) ∧ (∀ u u', ψ (u + u') = ψ u + ψ u') ∧ (∀ (z : ℂ) u, ψ (z • u) = z • ψ u) ∧ (∀ k ∈ GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.maxCpt N.M τ, ∀ u w : GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.kFin N.M τ, (w : N.M.H τ) = N.M.rep τ k u → ψ w = rTr N.V (atTau θ N.V τ k) (ψ u)) ∧ (∀ X ∈ lieAt N.V τ, ∀ u w : GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.kFin N.M τ, (w : N.M.H τ) = dRep (N.M.rep τ) X u → ψ w = Rder θ N.V τ X (ψ u)) := by
  first | exact @_root_.GlobalTheory.PlaceDecomp.placeDecomposition_gkMap_rankOne_values | exact _root_.GlobalTheory.PlaceDecomp.placeDecomposition_gkMap_rankOne_values | (intros; apply _root_.GlobalTheory.PlaceDecomp.placeDecomposition_gkMap_rankOne_values <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.PlaceDecompositionHasCtpOfIsClosed
section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.Grow GlobalTheory.Size
open Formalism.REAL Formalism.MainNotions.S GlobalTheory.SmoothGlob GlobalTheory.LowTypeDetermined GlobalTheory.TypeSum GlobalTheory.SeriesToClosure GlobalTheory.PlaceDecomp GlobalTheory.KFinDecomp Matrix
open scoped InnerProductSpace
noncomputable section
namespace GlobalTheory.PlaceDecomp
theorem placeDecomposition_hasCtp_of_isClosed : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (N : GlobalTheory.Grid.Node D) (U : Subgroup (GA D N.V)) (W : D.what₂.Tau → Type) [∀ τ, AddCommGroup (W τ)] [∀ τ, Module ℂ (W τ)] (ρ : ∀ τ, Representation ℂ (Formalism.REAL.KG (N.M.ε τ)) (W τ)) (τ : D.what₂.Tau), (∀ f f' : GA D N.V → ℂ, f ∈ Cls θ N U → f' ∈ Cls θ N U → f + f' ∈ Cls θ N U) → (0 : GA D N.V → ℂ) ∈ Cls θ N U → (∀ (c : ℂ) (f : GA D N.V → ℂ), f ∈ Cls θ N U → c • f ∈ Cls θ N U) → (∀ T T' : N.M.H τ → N.M.H τ, HasCtp θ N U (TyOf θ N ρ) τ T → HasCtp θ N U (TyOf θ N ρ) τ T' → HasCtp θ N U (TyOf θ N ρ) τ (fun w => T w + T' w) ∧ HasCtp θ N U (TyOf θ N ρ) τ (fun w => T (T' w))) ∧ (∀ (c : ℂ) (T : N.M.H τ → N.M.H τ), HasCtp θ N U (TyOf θ N ρ) τ T → HasCtp θ N U (TyOf θ N ρ) τ (fun w => c • T w)) ∧ HasCtp θ N U (TyOf θ N ρ) τ (fun _ => 0) := by
  intro D θ _ hp N U W _ _ ρ τ hadd _ hsmul
  haveI : CompleteSpace (N.M.H τ) := (N.M.ds τ).1
  have hσ := (std_of_isDS hp.harishChandraModules (N.M.ds τ)).1
  have hs : ∀ (c : ℂ) (T : N.M.H τ → N.M.H τ), HasCtp θ N U (TyOf θ N ρ) τ T →
      HasCtp θ N U (TyOf θ N ρ) τ (fun w => c • T w) := by
    rintro c T ⟨A, hA, hm⟩
    refine ⟨fun φ => c • A φ, ⟨fun f hf => (hA.cont f hf).const_smul c, fun f f' hf hf' => ?_, fun a f hf => ?_,
      fun f hf => hsmul c _ (hA.maps f hf), fun τ' h f hf ht x => ?_, fun τ' h g hg f hf => ?_,
      fun τ' h X hX f hf => ?_⟩, fun φ hφ x S v ℓ C hS hc h => (hm φ hφ x S v ℓ C hS hc h).smul hσ hS c⟩
    · simp only [hA.add f f' hf hf', smul_add]
    · simp only [hA.smul a f hf, smul_comm c a]
    · exact Submodule.smul_mem _ c (hA.keep τ' h f hf ht x)
    · simp only [hA.tr τ' h g hg f hf]
      rfl
    · simp only [hA.lie τ' h X hX f hf, GlobalTheory.Mem.AutSpace.Rder_smul]
  refine ⟨?_, hs, ?_⟩
  · rintro T T' ⟨A, hA, hm⟩ ⟨A', hA', hm'⟩
    refine ⟨⟨fun φ => A φ + A' φ, ⟨fun f hf => (hA.cont f hf).add (hA'.cont f hf), fun f f' hf hf' => ?_,
      fun a f hf => ?_, fun f hf => hadd _ _ (hA.maps f hf) (hA'.maps f hf), fun τ' h f hf ht x => ?_,
      fun τ' h g hg f hf => ?_, fun τ' h X hX f hf => ?_⟩,
      fun φ hφ x S v ℓ C hS hc h => (hm φ hφ x S v ℓ C hS hc h).add hσ (hm' φ hφ x S v ℓ C hS hc h) hS⟩,
      ⟨fun φ => A (A' φ), ⟨fun f hf => hA.cont _ (hA'.cont f hf), fun f f' hf hf' => ?_, fun a f hf => ?_,
      fun f hf => hA.maps _ (hA'.maps f hf), fun τ' h f hf ht => hA.keep τ' h _ (hA'.maps f hf) (hA'.keep τ' h f hf ht),
      fun τ' h g hg f hf => ?_, fun τ' h X hX f hf => ?_⟩,
      fun φ hφ x S v ℓ C hS hc h => hm _ (hA'.maps φ hφ) x S _ ℓ C hS hc (hm' φ hφ x S v ℓ C hS hc h)⟩⟩
    · simp only [hA.add f f' hf hf', hA'.add f f' hf hf']
      abel
    · simp only [hA.smul a f hf, hA'.smul a f hf, smul_add]
    · exact Submodule.add_mem _ (hA.keep τ' h f hf ht x) (hA'.keep τ' h f hf ht x)
    · simp only [hA.tr τ' h g hg f hf, hA'.tr τ' h g hg f hf]
      rfl
    · simp only [hA.lie τ' h X hX f hf, hA'.lie τ' h X hX f hf]
      exact (GlobalTheory.Mem.AutSpace.Rder_add (hA.maps f hf).1.1.smooth (hA'.maps f hf).1.1.smooth hX).symm
    · simp only [hA'.add f f' hf hf', hA.add _ _ (hA'.cont f hf) (hA'.cont f' hf')]
    · simp only [hA'.smul a f hf, hA.smul a _ (hA'.cont f hf)]
    · simp only [hA'.tr τ' h g hg f hf, hA.tr τ' h g hg _ (hA'.maps f hf)]
    · simp only [hA'.lie τ' h X hX f hf, hA.lie τ' h X hX _ (hA'.maps f hf)]
  · simpa using hs 0 _ (hasCtp_id θ N U _ τ)
end GlobalTheory.PlaceDecomp
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.Grow GlobalTheory.Size
open Formalism.REAL Formalism.MainNotions.S GlobalTheory.SmoothGlob GlobalTheory.LowTypeDetermined GlobalTheory.TypeSum GlobalTheory.SeriesToClosure GlobalTheory.PlaceDecomp GlobalTheory.KFinDecomp Matrix
open scoped InnerProductSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twist_placeDecomposition_hasCtp : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (N : GlobalTheory.Grid.Node D) (U : Subgroup (GA D N.V)) (W : D.what₂.Tau → Type) [∀ τ, AddCommGroup (W τ)] [∀ τ, Module ℂ (W τ)] (ρ : ∀ τ, Representation ℂ (Formalism.REAL.KG (N.M.ε τ)) (W τ)) (τ : D.what₂.Tau), (∀ f f' : GA D N.V → ℂ, f ∈ Cls θ N U → f' ∈ Cls θ N U → f + f' ∈ Cls θ N U) → (0 : GA D N.V → ℂ) ∈ Cls θ N U → (∀ (c : ℂ) (f : GA D N.V → ℂ), f ∈ Cls θ N U → c • f ∈ Cls θ N U) → (∀ T T' : N.M.H τ → N.M.H τ, HasCtp θ N U (TyOf θ N ρ) τ T → HasCtp θ N U (TyOf θ N ρ) τ T' → HasCtp θ N U (TyOf θ N ρ) τ (fun w => T w + T' w) ∧ HasCtp θ N U (TyOf θ N ρ) τ (fun w => T (T' w))) ∧ (∀ (c : ℂ) (T : N.M.H τ → N.M.H τ), HasCtp θ N U (TyOf θ N ρ) τ T → HasCtp θ N U (TyOf θ N ρ) τ (fun w => c • T w)) ∧ HasCtp θ N U (TyOf θ N ρ) τ (fun _ => 0) := by
  first | exact @_root_.GlobalTheory.PlaceDecomp.placeDecomposition_hasCtp_of_isClosed | exact _root_.GlobalTheory.PlaceDecomp.placeDecomposition_hasCtp_of_isClosed | (intros; apply _root_.GlobalTheory.PlaceDecomp.placeDecomposition_hasCtp_of_isClosed <;> assumption)
end
end

