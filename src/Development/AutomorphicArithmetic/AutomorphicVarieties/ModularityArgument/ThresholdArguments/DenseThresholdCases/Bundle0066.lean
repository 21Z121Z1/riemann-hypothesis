import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.DiscreteSeriesCoefficientsCuspidal
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.AutomorphyDescent.AutEnd2
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0012
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0006
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.AutQN
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0040
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0059
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Across2
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TAlgOfCyc
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.WeakOfAtt
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.AutomorphyDescent.AutNewformW
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.Bundle0020
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0007
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.LitAut
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0008
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0047
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0044
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0063
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TDenseU
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0009
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TCoreDet
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TWtBridge
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.ArithmeticPointPurity
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0005
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.WeilDeligneUnramified.MemOfUnder
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0033
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0051
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0046
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0064
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0036
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0065
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CuspidalTwists.Sp4In
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0034

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.AutEnd2
section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open private kills_pow pairing2 from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.BaseChangeUnits.RankTwoDescentImagQuadratic
open private kills_open exists_two flag det_one sq_of_trace norm_lt' cont_val cont_of_open irr_sub comm_mem isIrr_of tw_tw det_star conj_mat from Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.AutEnd2OfAutPt
open UpperTheory.GalN.V
open NumberField IsLocalRing Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.GalOfCusp UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Aut UpperTheory.V.Pr UpperTheory.V
open UpperTheory.V.Z.Win UpperTheory.V.Z
private theorem detAlg (H : _root_.UpperTheory.V.Af.HypothesesH') {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {ι : Qbar l ≃+* ℂ}
    {W : G ℚ Ω →* GL (Fin 2) (Qbar l)} (hW : Continuous W) {M : ℕ} (hM : 1 ≤ M) (hχ : Af.KillsMu M (Matrix.GeneralLinearGroup.det.comp W)) :
    Af.IsAlgChar ι (Matrix.GeneralLinearGroup.det.comp W) := by
  obtain ⟨k, hk, hpow⟩ := kills_pow hM hχ
  refine (_root_.UpperTheory.V.Af.algOfCyc_s H ℚ Ω l ι).1 _ (Matrix.GeneralLinearGroup.continuous_det.comp hW) fun w _ => ?_
  obtain ⟨A, hA⟩ : ∃ A : ValuationSubring Ω, IsPlaceOver A w := exists_isPlaceOver Ω w
  exact ⟨A, hA, 0, k, hk, fun s _ => by rw [neg_zero, zpow_zero, mul_one, hpow]⟩
private theorem polTwo {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (K : Type) [Field K] [NumberField K] [Algebra K Ω] {l : ℕ} [Fact l.Prime]
    {ι : Qbar l ≃+* ℂ} (W : G ℚ Ω →* GL (Fin 2) (Qbar l)) (h : Af.IsAlgChar ι (Matrix.GeneralLinearGroup.det.comp W)) (c : G ℚ Ω)
    (hc : Sd.IsCC c) : Af.Sol.Pol ι (W.comp (Base.galEmb ℚ K Ω)) := by
  obtain ⟨Q, hQ⟩ := pairing2 W c
  exact ⟨ℚ, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, _, c, Q, h,
    Ws.auSign _, hc, fun s s' h => by
      have h' : Base.galEmb ℚ K Ω s' = c * Base.galEmb ℚ K Ω s * c⁻¹ := h
      rw [MonoidHom.comp_apply, MonoidHom.comp_apply, h']
      exact hQ _ _ rfl⟩
open UpperTheory.V.Pr.LkAut2 in
theorem UpperTheory.V.Z.Win.Dn.autEnd2_alt (H : _root_.UpperTheory.V.Af.HypothesesH') (hPot : Dn.PotTwo) (hIne : Dn.Ine2) :
    RankTwoAutomorphyDescendsFromAbelianCMToRat → _root_.UpperTheory.V.Z.Win.RR.AutNewformA → Sd.TwC → Sd.AlgCyc → ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {K : Type} [Field K] [NumberField K] [Algebra K Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} {N : ℕ} [NeZero N] {e : ℕ} {ψ : DirichletCharacter c.O N} (D : Dat Ω K c e ψ) {g₁ : G ℚ Ω} {B : ValuationSubring Ω} {M : ℕ}
      {L : Type} [Field L] [NumberField L] [IsCMField L] [Algebra L Ω] {Φ : Fr.Frame l (ResidueField c.O)} (k : GalLink D.η D.Ψ D.cc g₁ B M L Φ) [CharP (ResidueField c.O) l] {C₀ : ℕ}, Φ.Ok C₀ → l ∣ M → B.valuation (l : Ω) < 1 → LinkHyp c N e D.η D.cc B M →
      ∀ (ι : Qbar l ≃+* ℂ) (ka : G L Ω →* (Qbar l)ˣ), Sd.IsAlgChar ι ka → _root_.UpperTheory.V.Pr.AutPtAlt k 2 ι ka → _root_.UpperTheory.V.Z.Win.Dn.AutEnd2A c D.η D.Ψ D.cc g₁ B e ι := by
  intro hDown hNew hTw hAlg Ω _ _ _ K _ _ _ l hl c N _ e ψ D g₁ B M L _ _ _ _ Φ k _ C₀ hok hM hB hLk ι ka hka hA
  intro A _ _ r hr hII h11 W hW _
  obtain ⟨hcc, hηc, -, hηl, -, -, h2, hcm, -⟩ := dat_facts D
  obtain ⟨hk1, hk2, hk3, -⟩ := eta_killsMu D
  haveI := k.ab
  haveI := hcm
  haveI : IsAlgClosure K Ω := Th.Db.algClo K Ω
  haveI : Module.IsTorsionFree L Ω := DivisionSemiring.to_moduleIsTorsionFree
  haveI : IsAlgClosure L Ω := ⟨IsAlgClosure.isAlgClosed ℚ, Algebra.IsAlgebraic.tower_top (K := ℚ) L⟩
  haveI : FaithfulSMul c.O A := (faithfulSMul_iff_algebraMap_injective _ _).2 fun x y h =>
    Subtype.ext (congrArg A.val h)
  haveI : IsLocalHom (algebraMap c.O A) := Algebra.IsIntegral.isLocalHom _ _
  haveI : IsNoetherianRing A := PrincipalIdealRing.isNoetherianRing
  have hW' : ∀ g ∈ D.η.ker, (W g).val = (corner (r g).mat).map A.val := hW
  have hblk : Block D.η r := fun g hg a b h => Subtype.ext (hII.1 g hg a b h)
  have hirr : MatIrr D.η.ker fun g => (W g).val := fun V hV => hII.2 V fun g hg v hv => by
    have : (W g).val.mulVec v ∈ V := hV g hg v hv
    rwa [hW g hg] at this
  have hopen : IsOpen (D.η.ker : Set (G ℚ Ω)) := hηl.isOpen_fiber 1
  have hcont : Continuous W := by
    refine cont_of_open W D.η.ker hopen _ (continuous_matrix fun i j => ?_) hW
    exact cont_val (A.val : A →+* PadicAlgCl l) (norm_lt' c A) (fun g => (r g).mat (![0, 2] i) (![0, 2] j)) fun n =>
      (hr.cont n).comp fun X => X (![0, 2] i) (![0, 2] j)
  have hdW : ∀ g ∈ D.η.ker, (W g).val.det = A.val (corner (r g).mat).det := fun g hg => by
    rw [hW' g hg, AlgHom.map_det]
    rfl
  have hdet : ∀ g ∈ D.η.ker, (W g).val.det = 1 := fun g hg => by
    obtain ⟨s1, s2⟩ := mat_gstar r D.cc g hr.norm.atc ((hr.red.mult _).trans hηc) ((hr.red.mult _).trans hg)
    have e1 := hdW _ (show gstar D.cc g ∈ D.η.ker from (hr.red.mult _).symm.trans s2)
    rw [s1, det_star, ← hdW g hg] at e1
    have e2 : Matrix.GeneralLinearGroup.det (W (gstar D.cc g)) * Matrix.GeneralLinearGroup.det (W g) = 1 := by
      have := congrArg (Matrix.GeneralLinearGroup.det.comp W) hcc
      rw [map_mul, map_one] at this
      show (Matrix.GeneralLinearGroup.det.comp W) (D.cc * g⁻¹ * D.cc) * (Matrix.GeneralLinearGroup.det.comp W) g = 1
      rw [map_mul, map_mul, map_inv, mul_right_comm _ _⁻¹, this, one_mul, inv_mul_cancel]
    have e3 : (W (gstar D.cc g)).val.det * (W g).val.det = 1 := congrArg Units.val e2
    rw [e1, hdW g hg, ← map_mul] at e3
    rw [hdW g hg, det_one hr.red h2 g ((sq _).trans (Subtype.ext e3)), map_one]
  have hcyc : Af.IsCycWt l 0 (Matrix.GeneralLinearGroup.det.comp W) :=
    ⟨_, Matrix.GeneralLinearGroup.det.comp W, hk2, fun s hs => Units.ext (hdet s (hk1 s hs)), by simp⟩
  obtain ⟨hg, eg⟩ := k.g0
  have hηg : D.η g₁ = 1 := by
    have h := k.del ⟨g₁, hg⟩
    rw [eg] at h
    exact h.symm.trans Φ.g0.2
  have hirrL : Af.IsIrr (W.comp (Base.galEmb ℚ L Ω)) := by
    refine isIrr_of W _ _ (Base.range_galEmb ℚ L Ω).ge (irr_sub W D.η.ker (Base.galOf ℚ L Ω) (comm_mem L Ω) hirr
      (barChar c.O D.Ψ) (fun g hg ht => sq_of_trace hr.red g (Subtype.ext ?_)) g₁ (k.gal ▸ ⟨hg, hηg⟩) hηg ?_)
    · rw [hW g hg, Matrix.trace_fin_two] at ht
      exact ht
    · have h := k.psi ⟨g₁, hg⟩
      rw [eg] at h
      exact h ▸ hok.baseSubgroup_spec
  obtain ⟨ρ, r1, r2, r3⟩ := exists_nrep2 k hok hM hcc r hr hblk
  obtain ⟨⟨π, p1, -, p3⟩, hWit⟩ := _root_.UpperTheory.GalN.V.csdN'_alt H.toClassicalTheorems (by norm_num) <| hA A ρ r1 r3 (W.comp (Base.galEmb ℚ L Ω)) (fun s => by
    rw [r2]
    exact hW' _ (k.gal.le (Base.galEmb_mem ℚ L Ω s)).2) hirrL
  have hC := hTw L Ω l ι 2 _ ka⁻¹ ((hAlg L Ω l ι).2.2 ka hka) ⟨π, p1, p3⟩
  rw [tw_tw] at hC
  have hR := hDown L Ω l ι W hcont hcyc hirrL
    ⟨D.η, D.cc, D.conj, hηc, fun s => (k.gal.le (Base.galEmb_mem ℚ L Ω s)).2⟩ hC
  have hΨ : ∀ g, Chr.dirG ℚ Ω ψ g = 1 → D.ΨQ g = cycBar ℚ Ω l g ^ (e : ℤ) := fun g hg => by
    show Units.map (algebraMap c.O (PadicAlgCl l)).toMonoidHom (Base.chiO ℚ Ω l c.O g ^ (e : ℤ) * Chr.dirG ℚ Ω ψ g) = _
    rw [hg, mul_one, map_zpow]
    rfl
  suffices hfl : Af.IsFlagOn W ((D.η.ker ⊓ (Chr.dirG ℚ Ω ψ).ker) ⊓ Ine (F := ℚ) B)
      (fun i => ((cycBar ℚ Ω l) ^ (![(e : ℤ), -(e : ℤ)] i)).comp ((D.η.ker ⊓ (Chr.dirG ℚ Ω ψ).ker) ⊓ Ine (F := ℚ) B).subtype) by
    have hop := hopen.inter (kills_open (NeZero.pos N) hk3)
    have hWL := hWit (Af.Bc.irrBasic.2 _ _ _ _ _ (hcont.comp (Af.continuous_restrictScalarsHom ℚ L Ω)) hka.1)
    have hirrQ := isIrr_of W (MonoidHom.id _) _ (fun g _ => ⟨g, rfl⟩) hirr
    obtain ⟨f, hf⟩ := _root_.UpperTheory.V.Z.Win.Dn.nw' hNew Ω l ι e D.gd.e_pos W hcont hirrQ hR
      ⟨hcyc, L, _, _, _, inferInstance, _, hirrL, ⟨D.η, D.cc, D.conj, hηc, fun s => (k.gal.le (Base.galEmb_mem ℚ L Ω s)).2⟩, ka, hka, hWL⟩
      B hB _ hop hfl
    refine ⟨⟨f, hf⟩, ?_⟩
    have hQ0 : IsAutomorphicOverImagQuad ι W := _root_.UpperTheory.GalN.V.newformAut0_alt H.toClassicalTheorems _ (by have := D.gd.e_pos; omega) f l Ω ι W _ hf
    have hP := hPot Ω l e D.gd.e_pos W B hB _ hop inferInstance hfl
    have hFl : Flagged W := fun v hv A' hA' => (hP v hv A' hA').imp fun _ x => x.1
    have hI : IneAb W := hIne Ω l c N e ψ D.η D.cc g₁ B M hLk L Φ C₀ k hok A r hr hblk h11 K D.η_ker hopen W hW
    obtain ⟨hc', art, χ, a, h'⟩ := (hAlg L Ω l ι).2.2 ka hka
    have h1 := _root_.UpperTheory.V.Z.Win.Dn.twist'_alt H.toClassicalTheorems ⟨χ, hc', art, a, h'⟩ hc' hWL
    rw [tw_tw] at h1
    obtain ⟨_, _⟩ := Th.Db.algKL K L Ω (D.η_ker ▸ (k.gal ▸ inf_le_right : Base.galOf ℚ L Ω ≤ D.η.ker))
    obtain ⟨_, hsol⟩ := Th.Db.galKL K L k.ab
    have i2 : Af.IsIrr ((W.comp (Base.galEmb ℚ K Ω)).comp (Base.galEmb K L Ω)) := hirrL
    have i1 : Af.IsIrr (W.comp (Base.galEmb ℚ K Ω)) := (Af.Bc.irrBasic.1 _ _ _ 2 _).1 _ i2
    have hcK : Continuous (W.comp (Base.galEmb ℚ K Ω)) := hcont.comp (Af.continuous_restrictScalarsHom ℚ K Ω)
    have halg : Af.IsAlgChar ι (Matrix.GeneralLinearGroup.det.comp W) := detAlg H hcont hk2 fun s hs => Units.ext (hdet s (hk1 s hs))
    have fl := (flagLaws ℚ Ω l 2 W).2.2.2 K
    have hWK : _root_.UpperTheory.V.Z.Win.WitA ι (W.comp (Base.galEmb ℚ K Ω)) :=
      _root_.UpperTheory.V.Z.Win.Dn.down'_alt L H hsol (by norm_num) hcK i2 (polTwo K W halg D.cc D.conj) (hQ0 hcont K D.gd.quad i1) (fl.2.1 hFl) (fl.1 hI)
        (Keep.keeps2 Ω l c N e ψ D.η D.cc g₁ B M hLk L Φ C₀ k hok A r hr hblk h11 K D.η_ker _
          fun s => hW _ (D.η_ker.ge (Base.galEmb_mem ℚ K Ω s))) h1
    exact _root_.UpperTheory.V.Z.Win.Dn.across2'_alt H K Ω D.gd.quad (by norm_num) hP hcont hQ0 ⟨_, halg, dual_two W⟩ hI hFl i1 hWK
  obtain ⟨h, -, hT⟩ := hr.ord
  obtain ⟨s₀, hs₀, hn⟩ := exists_two D.gd.l_odd B hB
  have hID : ∀ s ∈ Ine (F := ℚ) B, s ∈ Dec (F := ℚ) B := fun s hs => Ine_le_Dec B hs
  have hf := flag (D.η.ker ⊓ (Chr.dirG ℚ Ω ψ).ker ⊓ Ine (F := ℚ) B) W (cycBar ℚ Ω l ^ (e : ℤ))
    (fun g => (UnitaryThreeInertia.push A.val r g).mat) (Matrix.GeneralLinearGroup.map (A.val : A →+* PadicAlgCl l) h)
    (fun s hs => hW s hs.1.1) (fun s hs => hII.1 s hs.1.1) (fun s hs => congrArg Subtype.val (h11 s hs.1.1))
    (fun s hs => hdet s hs.1.1) (fun s hs => ?_) (fun s hs i j hij => ?_) ?_
  · convert hf using 1
    funext i
    fin_cases i
    · rfl
    · simp
  · refine (conj_mat _ r h s ((hr.red.mult _).trans hs.1.1) 0 0).trans ?_
    have := hT.ine ⟨s, hID s hs.2⟩ hs.2 hs.1.1 0
    refine (congrArg A.val this).trans ?_
    rw [MonoidHom.zpow_apply, ← hΨ s hs.1.2]
    simp [UnitaryThreeInertia.psi, wt1]
    rfl
  · refine (conj_mat _ r h s ((hr.red.mult _).trans hs.1.1) i j).trans ?_
    exact (congrArg A.val (hT.tri ⟨s, hID s hs.2⟩ hs.1.1 i j hij)).trans (map_zero _)
  · refine ⟨s₀ ^ (2 * Nat.card (ZMod N)ˣ), ⟨⟨?_, ?_⟩, pow_mem hs₀ _⟩, fun h0 => ?_⟩
    · show D.η _ = 1
      rw [map_pow, pow_mul, Int.units_sq, one_pow]
    · show ψ.toUnitHom (Chr.cls ℚ Ω N _) = 1
      rw [map_pow, pow_mul', pow_card_eq_one', one_pow, map_one]
    · have := hn (((2 * Nat.card (ZMod N)ˣ : ℕ) : ℤ) * e * 2) (Units.ext (by
        rw [_root_.zpow_mul, _root_.zpow_mul, zpow_two, ← sq, Units.val_pow_eq_pow_val, _root_.zpow_natCast _ (2 * _), ← map_pow]
        exact h0))
      have h3 : 0 < 2 * Nat.card (ZMod N)ˣ * e * 2 := by
        have := D.gd.e_pos
        have := Nat.card_pos (α := (ZMod N)ˣ)
        positivity
      exact h3.ne' (by exact_mod_cast this)
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.ExistsHeckeIdeal
section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Polynomial ValuativeRel IsLocalRing GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.UnitaryBC UpperTheory.V UpperTheory.V.Hi UpperTheory.V.Hi.CaseU
open UpperTheory.V.W (Plc Lp HidaSetting Vl Resid LamObj UniversalOrdinaryDeterminantRing Pair)
open UpperTheory.V.HV (Coef)
open scoped TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 1000000 in
private theorem absH (hN : _root_.GlobalTheory.Mem.LiteralAutomorphy.LiteratureRankNHypothesis) {L Ω : Type} [Field L] [NumberField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω]
    {l : ℕ} [Fact l.Prime] {n : ℕ} {c : Coef l} (H : HSet L Ω l n c) (hA : H.Ax)
    (A : Type) [CommRing A] [Algebra c.O A] [Alg.IsCO c.O A] (θ : H.X.I.T →* Aˣ) (hθ : H.IsWt θ)
    (ι : Qbar l ≃+* ℂ) (P : Wt L l n → (H.Gq →* GL (Fin n) (Qbar l)) → Prop) (hAut : H.AutomorphicHeckeSet ι P)
    (lam : Wt L l n) (hl : lam ∈ H.admitted) (hd : H.DenseWt θ lam) (a : H.Op → c.O) (K : H.Lev)
    {B : Type} [CommRing B] [Algebra c.O B] (D₀ : W.GDet n B H.Gq) (ψ₀ : ∀ v, Fin n → Dec (F := L) (H.pl v) →* Bˣ)
    (j : A →ₐ[c.O] B)
    (key : ∀ (T : Type) [CommRing T] [Algebra c.O T] [Alg.IsCO c.O T] (φ : A →ₐ[c.O] T) (gen : H.Op → T),
      (∀ i, gen i - algebraMap c.O T (a i) ∈ maximalIdeal T) →
      ∀ (D : W.GDet n T H.Gq) (ψ : ∀ v, Fin n → Dec (F := L) (H.pl v) →* Tˣ), D.IsCont (maximalIdeal T) →
      (∀ v i, Alg.AdicCont (maximalIdeal T) fun g => (ψ v i g : T)) →
      (∀ (w : H.Wp) (B : ValuationSubring Ω) (σ : G L Ω), IsPlaceOver B w.1 → IsFrob B (normV w.1) σ →
        D.chi (MonoidAlgebra.single (H.prj σ⁻¹) 1) =
          heckePol n (normV w.1) fun j => if h : 0 < j ∧ j - 1 < n then gen (.inl (w, ⟨j - 1, h.2⟩)) else 1) →
      (∀ v i (s : Weil (H.ovr v)) (g : Dec (F := L) (H.pl v)) (y : Uo ((H.Sl v).adicCompletion L)),
        (g : G L Ω) = (s : G L Ω) → H.art v s = y →
        (ψ v i g * H.epsV T v g ^ (i : ℕ) : Tˣ) * φ (θ (eV n H.Sl v i y)) = 1) →
      (∀ v (j : Fin n) (s : Weil (H.ovr v)) (g : Dec (F := L) (H.pl v)), (g : G L Ω) = (s : G L Ω) → H.art v s = Hi.unif _ →
        ((∏ i with i ≤ j, ψ v i g * H.epsV T v g ^ (i : ℕ) : Tˣ) : T) = gen (.inr (v, j))) →
      ∀ Gd : (T →ₐ[c.O] Qbar l) → Prop, (∀ t : T, (∀ x, Gd x → x t = 0) → t = 0) →
      (∀ x, Gd x → ∃ ρ : H.Gq →* GL (Fin n) (Qbar l), P lam ρ ∧ D.map x.toRingHom = W.GDet.ofRep (W.mat ρ) ∧
        ∀ v, W.HasFlag (ρ.comp (H.dec v)) fun i => W.pushCh x.toRingHom (ψ v i)) →
      ∃ f : B →ₐ[c.O] T, D₀.map f.toRingHom = D ∧ (∀ v i, W.pushCh f.toRingHom (ψ₀ v i) = ψ v i) ∧ ∀ b, f (j b) = φ b) :
    ∃ J : Ideal B, H.IsJ θ a K D₀ ψ₀ j J := by
  by_cases hne : H.MK θ a K = ⊥
  · exact ⟨⊤, Or.inl ⟨hne, rfl⟩⟩
  haveI hF : Fact (CommOn (H.MK θ a K) (H.op A)) := ⟨((hiComm L Ω l n c _ hA A θ hθ K).2.2.2 a).1⟩
  obtain ⟨hCO, -, -, hres, -, hgen⟩ := hiAlg L Ω l n c _ hA A θ hθ a K hne
  obtain ⟨D, ψ, hU⟩ := _root_.UpperTheory.V.Hi.coreDet_alt hN L Ω l n c _ hA A θ hθ ι _ hAut lam hl hd a K
  have hO := _root_.UpperTheory.V.Z.Ord.core_hecke_of_automorphic_hecke_dense_weight hN L Ω l n c _ hA A θ hθ ι _ hAut lam hl hd a K D ψ hU
  obtain ⟨f, h1, h2, h3⟩ := key (H.TK θ a K) (IsScalarTower.toAlgHom c.O A _) (H.gen θ a K) hres D ψ hU.cont hU.ψ_cont
    hU.frob hU.ψ_unit hU.ψ_unif (fun x => H.Good θ (x.toRingHom.comp (algebraMap A _)) lam) (hO.sep lam hl hd)
    fun x hx => by
      obtain ⟨ρ, -, -, e1, e2, e3⟩ := hO.pt lam hl x hx.2.1
      exact ⟨ρ, e1, e2, fun v => (e3 hx v).1⟩
  have h2' : (fun v i => W.pushCh f.toRingHom (ψ₀ v i)) = ψ := funext fun v => funext fun i => h2 v i
  have hU' : H.IsMap θ a K D₀ ψ₀ f := by
    unfold HSet.IsMap
    rw [h1, h2']
    exact hU
  exact ⟨RingHom.ker f, Or.inr ⟨hF, hCO, f, hne, hU',
    deformationRing_to_heckeAlgebra_surjective L Ω l n c _ hA A _ B (H.gen θ a K) D₀ ψ₀ f hU'.frob hU'.ψ_unif _ h3 hgen, h3, rfl⟩⟩
theorem UpperTheory.V.Hi.exists_hecke_ideal :
    _root_.UpperTheory.V.Af.HypothesesH' → ∀ (l : ℕ) [Fact l.Prime] (L Ω : Type) [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (s : HidaSetting l L Ω) (n : ℕ), 1 ≤ n →
    ∀ (V : s.Lev) (Q : QData V) (c : Coef l), ∀ (r : Resid V.frame c.O n) (ι : Qbar l ≃+* ℂ), ∀ (B : UniversalOrdinaryDeterminantRing r) (Λ : LamObj r) (R : _root_.UpperTheory.V.Hi.CaseU.UnitaryHeckeData Q ι Λ) (K : (hset Q R.τ₀).Lev), ∃ J : Ideal B.B, R.IsJ B K J := by
  intro hP l _ L Ω _ _ _ _ _ _ s n hn V Q c r ι B Λ R K
  have hN : _root_.GlobalTheory.Mem.LiteralAutomorphy.LiteratureRankNHypothesis := hP.litN
  have hA : (hset Q R.τ₀).Ax := _root_.UpperTheory.V.Hi.axU_s hN l L Ω s n hn V Q c R.m R.τ₀
  have hAut := _root_.UpperTheory.V.Hi.automorphicHeckeSet_unitaryPointProperties_of_typeFor hP l L Ω s n hn V Q c r ι R.m R.τ₀ R.type
  let lam : Wt L l n := fun _ => ⟨0, fun _ _ _ => le_rfl⟩
  have hd : (hset Q R.τ₀).DenseWt R.θ lam := (_root_.UpperTheory.V.Hi.isDomain_and_denseWt_of_isTheta hN l L Ω s n hn V Q c R.m R.τ₀ r Λ R.θ R.theta).2 lam
  refine absH hN (hset Q R.τ₀) hA Λ.Λ R.θ R.isWt ι _ hAut lam (Set.mem_univ _) hd R.a K B.u.D B.u.ψ (Λ.toPair B.u) ?_
  intro T _ _ _ φ gen hres D ψ hc hψ hfr hun huf Gd hsep hpt
  exact JEx.map_of_rel B Λ φ D ψ hc (_root_.UpperTheory.V.Hi.heckeDeterminant_reduction_eq_residual_alt l L Ω s n V Q c r ι Λ R hA T gen hres D hc hfr)
    (_root_.UpperTheory.V.Hi.exists_ordinaryCharacters_heckeAlgebra' l L Ω s n V Q c r ι Λ R hA T φ gen hres ψ hψ hun huf)
    (_root_.UpperTheory.V.Hi.heckeDeterminant_satisfies_deformation_relations_alt l L Ω s n hn V c r ι lam T D ψ Gd hsep hpt)
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.HeckeIdealEnd
section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Polynomial ValuativeRel IsLocalRing GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.UnitaryBC UpperTheory.V UpperTheory.V.Hi UpperTheory.V.Hi.CaseU
open UpperTheory.V.W (Plc Lp HidaSetting Vl Resid LamObj UniversalOrdinaryDeterminantRing Pair)
open UpperTheory.V.HV (Coef)
open scoped TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option synthInstance.maxHeartbeats 200000
section SlopeTestRemainingChoices
open Formalism.MainNotions.N
variable {Γ Γ' k : Type} [Group Γ] [Group Γ'] [Field k] {n : ℕ}
private theorem factor {O A T K : Type} [CommRing O] [CommRing A] [CommRing T] [CommRing K] [Algebra O A] [Algebra O T]
    [Algebra O K] (f : A →ₐ[O] T) (hf : Function.Surjective f) (x : A →ₐ[O] K) (hx : RingHom.ker f ≤ RingHom.ker x) :
    ∃ y : T →ₐ[O] K, ∀ b, y (f b) = x b :=
  ⟨(Ideal.Quotient.liftₐ (RingHom.ker f) x fun _ hb => hx hb).comp (Ideal.quotientKerAlgEquivOfSurjective hf).symm.toAlgHom,
    fun b => by
      have : (Ideal.quotientKerAlgEquivOfSurjective hf).symm (f b) = Ideal.Quotient.mk _ b := by
        rw [AlgEquiv.symm_apply_eq]; rfl
      exact (congrArg (Ideal.Quotient.liftₐ (RingHom.ker f) x fun _ hb => hx hb) this).trans rfl⟩
private theorem map_comp {n : ℕ} {A T K Γ : Type} [CommRing A] [CommRing T] [CommRing K] [Group Γ] (D : W.GDet n A Γ)
    (f : A →+* T) (y : T →+* K) (x : A →+* K) (h : ∀ b, y (f b) = x b) : (D.map f).map y = D.map x := by
  obtain rfl : x = y.comp f := RingHom.ext fun b => (h b).symm
  rfl
end SlopeTestRemainingChoices
private theorem absPt {L Ω : Type} [Field L] [NumberField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] {l : ℕ} [Fact l.Prime]
    {n : ℕ} {c : Coef l} (H : HSet L Ω l n c) {A : Type} [CommRing A] [Algebra c.O A] [IsLocalRing A] (θ : H.X.I.T →* Aˣ)
    (a : H.Op → c.O) (K : H.Lev) [Fact (CommOn (H.MK θ a K) (H.op A))] {R : Type} [CommRing R] [Algebra c.O R]
    (D₀ : W.GDet n R H.Gq) (j : A →ₐ[c.O] R) (f : R →ₐ[c.O] H.TK θ a K) (hf : Function.Surjective f)
    (hj : ∀ b, f (j b) = algebraMap A _ b) {P : Wt L l n → (H.Gq →* GL (Fin n) (Qbar l)) → Prop} {I : Ideal (H.TK θ a K)}
    {ψ : ∀ v, Fin n → Dec (F := L) (H.pl v) →* (H.TK θ a K)ˣ} (out : H.Out θ a K P I (D₀.map f.toRingHom) ψ)
    (x : R →ₐ[c.O] Qbar l) (hx : RingHom.ker f ≤ RingHom.ker x) (lam : Wt L l n) (hl : lam ∈ H.admitted)
    (har : H.Arith θ (x.comp j).toRingHom lam) :
    ∃ ρ : H.Gq →* GL (Fin n) (Qbar l), Continuous ρ ∧ Formalism.MainNotions.N.IsSSRep ρ ∧ P lam ρ ∧
      D₀.map (x : R →+* Qbar l) = W.GDet.ofRep (W.mat ρ) := by
  obtain ⟨y, hy⟩ := factor f hf x hx
  have e1 : y.toRingHom.comp (algebraMap A _) = (x.comp j).toRingHom := RingHom.ext fun b =>
    (congrArg y (hj b)).symm.trans (hy _)
  obtain ⟨ρ, hc, hs, hP, hD, -⟩ := out.pt lam hl y (e1 ▸ har)
  exact ⟨ρ, hc, hs, hP, (map_comp D₀ f.toRingHom y.toRingHom x hy).symm.trans hD⟩
theorem hecke_ideal_end (H : _root_.UpperTheory.V.Af.HypothesesH') {l : ℕ} [Fact l.Prime] {L Ω : Type} [Field L] [NumberField L] [IsCMField L] [Field Ω]
    [Algebra L Ω] [IsAlgClosure L Ω] {s : HidaSetting l L Ω} {n : ℕ} (hn : 1 ≤ n) {V : s.Lev} {Q : QData V} {c : Coef l}
    {r : Resid V.frame c.O n} {ι : Qbar l ≃+* ℂ} {B : UniversalOrdinaryDeterminantRing r} {Λ : LamObj r} {R : _root_.UpperTheory.V.Hi.CaseU.UnitaryHeckeData Q ι Λ} {K : (hset Q R.τ₀).Lev}
    {J : Ideal B.B} (hJ : R.IsJ B K J) (x : B.Pt) (h : s.Wt n) (hx : J ≤ RingHom.ker x) (ha : x.Arith h) :
    ∃ (lam : Wt L l n) (ρ : V.frame.G₀ →* GL (Fin n) (Qbar l)), Continuous ρ ∧ Formalism.MainNotions.N.IsSSRep ρ ∧ _root_.UpperTheory.V.Hi.CaseU.UnitaryPointProperties r ι lam ρ ∧
      x.IsRep (ρ.comp V.pr) := by
  rcases hJ with ⟨_, rfl⟩ | ⟨i1, i2, f, -, hmap, hsurj, hlam, rfl⟩
  · exact absurd (hx (Submodule.mem_top (x := 1))) (by simp)
  obtain ⟨⟨lam, hl⟩, hb⟩ := _root_.UpperTheory.V.Hi.arith_good_iff_hset_of_theta_incr_weight H.litN l L Ω s n hn V Q c R.m R.τ₀ r B Λ R.θ R.theta h ha.1
  have har := (hb lam hl x).1.1 ha
  have out := _root_.UpperTheory.V.Z.Ord.core_hecke_of_automorphic_hecke_dense_weight H.litN L Ω l n c (hset Q R.τ₀) (_root_.UpperTheory.V.Hi.axU_s H.litN l L Ω s n hn V Q c R.m R.τ₀) Λ.Λ R.θ R.isWt ι (_root_.UpperTheory.V.Hi.CaseU.UnitaryPointProperties r ι)
    (_root_.UpperTheory.V.Hi.automorphicHeckeSet_unitaryPointProperties_of_typeFor H l L Ω s n hn V Q c r ι R.m R.τ₀ R.type) lam (Set.mem_univ _)
    ((_root_.UpperTheory.V.Hi.isDomain_and_denseWt_of_isTheta H.litN l L Ω s n hn V Q c R.m R.τ₀ r Λ R.θ R.theta).2 lam) R.a K _ _ hmap
  obtain ⟨ρ, hc, hs, hP, e3⟩ := absPt (hset Q R.τ₀) R.θ R.a K B.u.D (Λ.toPair B.u) f hsurj hlam out x hx lam (Set.mem_univ _) har
  refine ⟨lam, ρ, hc, hs, hP, ?_⟩
  replace e3 : x.D = W.GDet.ofRep (W.mat ρ) := e3
  change x.D.comap V.pr = _
  rw [e3]
  exact (AlgebraTools.Det.repApi (W.mat ρ)).2.2.2.2.2.2.1 V.pr
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.MemOfUnder
section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open NumberField IsDedekindDomain ValuativeRel Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.SplitWeil
open UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Dict
open UpperTheory.V.W (Plc Lp)
open scoped Matrix
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
namespace UpperTheory.V.Z.Sym.W
private theorem val_iff {L Ω : Type} [Field L] [NumberField L] [Field Ω] [Algebra L Ω] {A : ValuationSubring Ω} {w : Plc L}
    (h : IsPlaceOver A w) (M : ℕ) : A.valuation (M : Ω) < 1 ↔ (M : 𝓞 L) ∈ w.asIdeal := by
  have := h (M : 𝓞 L)
  simpa using this
private theorem mem_of_under {L : Type} [Field L] [NumberField L] [IsCMField L] {w w' : Plc L}
    (e : w'.under (𝓞 (Lp L)) = w.under (𝓞 (Lp L))) (M : ℕ) : (M : 𝓞 L) ∈ w'.asIdeal ↔ (M : 𝓞 L) ∈ w.asIdeal := by
  have hl : ∀ w : Plc L, (M : 𝓞 L) ∈ w.asIdeal ↔ (M : 𝓞 (Lp L)) ∈ (w.under (𝓞 (Lp L))).asIdeal := fun w => by
    rw [← map_natCast (algebraMap (𝓞 (Lp L)) (𝓞 L))]
    rfl
  rw [hl, hl, e]
private theorem core (P : _root_.UpperTheory.V.Z.Sym.W.PureWeightCompatibility) (hA : AdLiftW) (L Ω : Type) [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω]
    (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (hl : l ≠ 2) (M m : ℕ) (hM : M ≠ 0) (h2 : 2 * l ∣ M) (hU : UnrSplit L M)
    (r : G L Ω →* GL (Fin 2) (Qbar l)) (hr : AdInW ι M m r) (w₀ : Plc L) (hw₀ : (M : 𝓞 L) ∈ w₀.asIdeal) :
    ∃ π : CuspSub L 3, (CG.mk π).IsRegAlg ∧ GlobalTheory.ContraPair.DualIsConj π ∧ AttC ι (tw (ad0 r) (cycBar L Ω l)⁻¹) π ∧
      (∀ w : Plc L, (M : 𝓞 L) ∉ w.asIdeal → ∃ B, (CG.mk π).HasSat w B) ∧ ∀ τ, π.IsLocComp w₀ τ → PT τ := by
  have hlM : l ∣ M := (Dvd.intro_left 2 rfl).trans h2
  have h2M : 2 ∣ M := (Dvd.intro l rfl).trans h2
  have hdv : ∀ {a : ℕ} {w : Plc L}, a ∣ M → (a : 𝓞 L) ∈ w.asIdeal → (M : 𝓞 L) ∈ w.asIdeal := by
    rintro a w ⟨b, rfl⟩ h
    rw [Nat.cast_mul]
    exact Ideal.mul_mem_right _ _ h
  obtain ⟨σ, HT, hσ, hg, hpt, hunr, hwt⟩ := _root_.UpperTheory.V.Z.Sym.W.aboveWeight P L Ω l ι hl M m hM hlM hU r hr
  obtain ⟨S, hS, h0S, hSi, hSm⟩ := selectW L {w | (M : 𝓞 L) ∈ w.asIdeal} w₀ hw₀
  obtain ⟨Q, hQ, hQi, hQm⟩ := Ga.select L {w | IsSplitAt w ∧ (M : 𝓞 L) ∉ w.asIdeal ∧ ∃ s, Ga.FrobAt w s ∧ s ∉ Ga.Bad r}
  have hfin : S.Finite := by
    have h0 : Ideal.span {(M : 𝓞 L)} ≠ 0 := by
      rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
      exact_mod_cast hM
    exact (Ideal.finite_factors h0).subset fun v hv => Ideal.dvd_span_singleton.mpr (hS hv)
  have key : ∀ w : Plc L, ∃ ψ : Fin 2 → (Kw w)ˣ →* ℂˣ, (w ∈ S ∪ Q → CompEq σ w ψ) ∧ (w ∈ S → NoLk (ψ 0 / ψ 1)) ∧
      (w ∈ Q → (∀ i, ∀ u ∈ Hi.Uo (Kw w), ψ i u = 1) ∧ Reg (ψ 0 / ψ 1)) := fun w => by
    by_cases hq : w ∈ Q
    · obtain ⟨h1, h3, h4⟩ := hQ hq
      obtain ⟨τ, hτ⟩ := hg.comp w h1
      obtain ⟨ψ, a1, a2, a3, a4⟩ := _root_.UpperTheory.V.Z.Sym.W.good_w_statement P.af L Ω l ι r w (mt (hdv hlM) h3)
        (fun A hA => hr.unr A (mt (val_iff hA M).1 h3)) h4 τ (hg.loc w h1 τ hτ) (hpt w h1 τ hτ).1
      exact ⟨ψ, fun _ => ⟨a1, τ, hτ, a2⟩, fun h => absurd (hS h) h3, fun _ => ⟨a3, a4⟩⟩
    by_cases hs : w ∈ S
    · have h1 := hU.split w (hS hs)
      obtain ⟨τ, hτ⟩ := hg.comp w h1
      by_cases hw : ((l : ℕ) : 𝓞 L) ∈ w.asIdeal
      · obtain ⟨A, hA⟩ : ∃ A : ValuationSubring Ω, IsPlaceOver A w := exists_isPlaceOver Ω w
        obtain ⟨⟨ψ, a1, a2, a3⟩, -⟩ := _root_.UpperTheory.V.Z.Sym.W.above_w_statement P.af L Ω l ι hl r hr.cont m hr.gap w hw HT (hpt w h1 τ hτ).2 A hA
          (hr.above A ((val_iff hA l).2 hw)) τ (hg.loc w h1 τ hτ) (hpt w h1 τ hτ).1
        exact ⟨ψ, fun _ => ⟨a1, τ, hτ, a2⟩, fun _ => a3, fun h => absurd h hq⟩
      · obtain ⟨ψ, a1, a2, a3⟩ := _root_.UpperTheory.V.Z.Sym.W.away_w_statement P.af L Ω l ι r hr.cont hr.unl w hw τ (hg.loc w h1 τ hτ) (hpt w h1 τ hτ).1
        exact ⟨ψ, fun _ => ⟨a1, τ, hτ, a2⟩, fun _ => a3, fun h => absurd h hq⟩
    · exact ⟨1, fun h => (h.elim hs hq).elim, fun h => absurd h hs, fun h => absurd h hq⟩
  choose ψ hψ hnl hψ' using key
  have hgood : Ga.GoodSet ι M r σ Q ψ :=
    ⟨fun w hw => ⟨(hQ hw).1, mt (hdv hlM) (hQ hw).2.1, hψ w (Or.inr hw)⟩, fun w a b c => hQm w ⟨a, b, c⟩⟩
  have hgap := hr.gap
  have := hA L hU.unr hfin.toFinset Q ?_ ?_ ?_ σ hσ (m - 1) (by omega) hwt ?_ ψ ?_ hψ'
  · rcases this with ⟨σ₃, h1, hu, h4, h3⟩ | ⟨σ', h1, h3⟩
    · obtain ⟨π, a, b, c, d⟩ := _root_.UpperTheory.V.Z.Sym.W.branch1W_alt P L Ω l ι hl hU.unr M m hM r σ hr hg Q ψ hgood (fun w hw => (hψ' w hw).2) σ₃ h1 h3
      exact ⟨π, a, b, c, fun w hw => d.unr w (hu w fun w' hw' e => hw ((mem_of_under e M).1 (hS (hfin.mem_toFinset.1 hw')))),
        _root_.UpperTheory.V.Z.Sym.W.plain_at_w_statement P.af.litN L σ₃ π h1 d w₀ (hU.split w₀ hw₀) _ (hnl w₀ h0S) (h4 w₀ (hfin.mem_toFinset.2 h0S))⟩
    · exact (_root_.UpperTheory.V.Z.Sym.W.branch_two_w_statement P L Ω l ι hl hU.unr M m hM r σ hr hg Q ψ hgood (fun w hw => (hψ' w hw).2) σ' h1 h3).elim
  · rw [hfin.coe_toFinset, Set.disjoint_left]
    exact fun w a b => (hQ b).2.1 (hS a)
  · rw [hfin.coe_toFinset]
    refine ⟨fun w hw => hw.elim (fun h => hU.split w (hS h)) fun h => (hQ h).1, ?_⟩
    rintro a (ha | ha) b (hb | hb) e
    · exact hSi ha hb e
    · exact absurd ((mem_of_under e M).1 (hS ha)) (hQ hb).2.1
    · exact absurd ((mem_of_under e M).2 (hS hb)) (hQ ha).2.1
    · exact hQi ha hb e
  · intro w hw
    obtain ⟨w', a, b⟩ := hSm w (hdv h2M (by exact_mod_cast hw))
    exact ⟨w', hfin.mem_toFinset.2 a, b⟩
  · intro w hw
    refine hunr w fun h => ?_
    obtain ⟨w', a, b⟩ := hSm w h
    exact hw w' (hfin.mem_toFinset.2 a) b
  · rw [hfin.coe_toFinset]
    exact hψ
theorem adjoint_automorphy_w_of_pure_weight_adjoint_lift (P : _root_.UpperTheory.V.Z.Sym.W.PureWeightCompatibility) (hA : AdLiftW) : AdAutW := by
  intro L Ω _ _ _ _ _ _ l _ ι hl M m hM h2 hU r hr
  obtain ⟨w₁, hw₁⟩ : ∃ w : Plc L, (M : 𝓞 L) ∈ w.asIdeal := by
    have hl1 : ((l : ℕ) : 𝓞 L) ∈ (GlobalTheory.EvExtend.placeOf (IsAlgClosed.lift (R := ℚ) (M := Qbar l) (S := L)).toRingHom).asIdeal := by
      rw [GlobalTheory.EvExtend.mem_placeOf]
      simpa using GlobalTheory.EvExtend.norm_natCast_lt_one (l := l)
    obtain ⟨b, rfl⟩ := (Dvd.intro_left 2 rfl).trans h2
    exact ⟨_, by rw [Nat.cast_mul]; exact Ideal.mul_mem_right _ _ hl1⟩
  obtain ⟨π, a, b, c, d, -⟩ := core P hA L Ω l ι hl M m hM h2 hU r hr w₁ hw₁
  refine ⟨⟨π, a, b, c⟩, glueW L Ω l ι _ fun w => ?_⟩
  by_cases hw : (M : 𝓞 L) ∈ w.asIdeal
  · obtain ⟨π', -, -, c', -, e⟩ := core P hA L Ω l ι hl M m hM h2 hU r hr w hw
    exact ⟨π', c', Or.inr e⟩
  · exact ⟨π, c, Or.inl (d w hw)⟩
end UpperTheory.V.Z.Sym.W
end
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Sp4In
section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
namespace UpperTheory.V.Cu
theorem sp4In_alt (hC : GradeZeroInterpolatingElement.CohomologyHyp) (hF : Published.FerreroWashington) (s2 : _root_.UpperTheory.V.Ws.SeedIIAlt) (s4 : _root_.UpperTheory.V.Cu.SeedIVAlt) (hP : _root_.UpperTheory.V.Ws.PMExAlt) : _root_.UpperTheory.V.Aut.SymplecticFourImageDense :=
  _root_.UpperTheory.V.Cu.main4_alt hC hF hFit s2 s4 hP
end UpperTheory.V.Cu
end
end

