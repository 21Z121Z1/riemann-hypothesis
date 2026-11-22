import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.TamagawaNumberSpecialUnitary
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3121
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3162
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3169
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3138
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.Hypotheses2
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3178
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3126
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3185
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3142
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3182

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.BergmanKernelThickPartEstimate
section
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.CovHt
namespace GlobalTheory.ThickBerg
open ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Inst MeasureTheory
set_option maxHeartbeats 4000000 in
theorem bergman_kernel_bound_thick_part : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → HypothesesH → DeepGood → Size → FlatDeg → Covers fun Fm x _ ι p i Y PP C => ∀ u1, Quo p i PP u1 → ∃ B : ℝ, 0 ≤ B ∧ lenT p i PP * B ≤ C * unitE p ∧ ∀ (Z : Comp Y.d.Xo₂ Y.d.c₂) (σ : Y.d.c₂.F →+* ℂ), GoodEmb Y.d.c₂ σ → ∀ y : FPt (Y.U σ).X, (⟨y.1, y.2.1⟩ : Σ k, Frame ((Y.U σ).X k).Ψ (Fm.D x ι).R.r) ∈ framesOn (Y.U σ) Z → (Fm.L x ι).sc.b ≤ (Y.d.l₂.M : ℝ) * ((Y.U σ).X y.1).firstMinimumSq y.2.1 → ENNReal.ofReal (Real.exp (-B)) ≤ bergOn (Y.U σ) ((Fm.D x ι).sp.W ((i : ℕ) + 1)) (Y.dict σ) Z (wtOf (dat p i) u1 0) y := by
  intro _ _ _ hS _
  obtain ⟨C0, hC0, hpeak⟩ := GlobalTheory.T.exists_cusp_form_peak_at_injective_chart_frame
  have hnum := GlobalTheory.T.torus_length_lower_bound_quotient hS
  refine (((hnum.and (GlobalTheory.CovTop.Sizes.hostN (max 10 C0))).and GlobalTheory.CovTop.WtShape.wtN).and hS).imp
    fun Fm CH _ h => ?_
  obtain ⟨⟨⟨⟨C2, hC2, hN⟩, ⟨A, -, hH⟩⟩, ⟨C3, -, hW⟩⟩, ⟨C4, -, hSz⟩⟩ := h
  refine ⟨C0 * (C2 + 1), by positivity, ?_⟩
  obtain ⟨x0, hall⟩ := ((hN.and hH).and hW).and hSz
  refine ⟨x0, fun x hx hle ι p hp i hi Y hY u1 hu1 => ?_⟩
  obtain ⟨⟨⟨hN, hH⟩, hW⟩, hSz⟩ := hall x hx hle ι p hp
  obtain ⟨hZ24, hu⟩ := hN i hi
  obtain ⟨hTl1, hgap⟩ := hu u1 hu1
  have hHi := hH i
  have hWi := hW i
  have hSi := hSz i
  have hsig := hWi.sig
  have hm3 := (Fm.D x ι).R.m_add_three_le_k
  simp only [Ranks.sigW] at hsig
  have hp1 : 1 ≤ (dat p i).p := by omega
  have hq1 : 1 ≤ (dat p i).q := by omega
  have hf1 : (1 : ℝ) ≤ (Fm.D x ι).R.f := by exact_mod_cast (by have := hHi.f8; omega : 1 ≤ (Fm.D x ι).R.f)
  have hr1 : (1 : ℝ) ≤ (Fm.D x ι).R.r := by exact_mod_cast (by omega : 1 ≤ (Fm.D x ι).R.r)
  have hD1 : (1 : ℝ) ≤ (dimFlag (dat p i) : ℝ) := by
    rw [hWi.dim]
    have h2 : 1 ≤ (Fm.D x ι).R.r.choose 2 := Nat.choose_pos (by omega)
    have h8 := hHi.f8
    exact_mod_cast (Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (by omega) (by omega)))
  have hzb : zBase (Fm.L x ι) = ((Fm.D x ι).R.f * (Fm.D x ι).R.r) * (Fm.L x ι).sc.L := rfl
  obtain ⟨hA8, hC08, h100⟩ := nums ((Fm.D x ι).R.f * (Fm.D x ι).R.r) (Fm.L x ι).sc.L C0 _ _ _ _ _
    (one_le_mul_of_one_le_of_one_le hf1 hr1) hHi.big.2.1 ((le_max_right _ _).trans hHi.big.1)
    (hzb ▸ hHi.ppLow) (hzb ▸ hZ24) hD1 hWi.what₂.2 hSi.2.1
  have hl10 : 0 ≤ l1 u1 := by unfold l1; positivity
  refine ⟨C0 * (l1 u1 + ((Fm.D x ι).R.f * (Fm.D x ι).R.r) ^ 8), by positivity, ?_, fun Z σ hσ y hy hb => ?_⟩
  · have e : (lenT p i (Fm.parT x hx ι).PP : ℝ) * (C0 * (l1 u1 + ((Fm.D x ι).R.f * (Fm.D x ι).R.r) ^ 8)) =
        C0 * ((lenT p i (Fm.parT x hx ι).PP : ℝ) * l1 u1 + (lenT p i (Fm.parT x hx ι).PP : ℝ) * ((Fm.D x ι).R.f * (Fm.D x ι).R.r) ^ 8) := by ring
    rw [e, mul_add C0 C2 1, mul_one]
    nlinarith [mul_le_mul_of_nonneg_left (add_le_add hTl1 hA8) hC0]
  · have hL := GlobalTheory.LawsDeep.levLaws _ p.T _ Y _ _ p.fw.laws ⟨Nat.le_add_left _ _, i.2⟩ hY.1
    have hg0 : ∀ q : ℕ, q.Prime → p.T.Q.l.GoodAt q :=
      Formalism.L2.Pj.goodAt_of_two_primes p.fw.laws.pins.2.1.1 ((Fm.D x ι).host.g_prime 0) ((Fm.D x ι).host.g_prime 1)
        (Fm.D x ι).host.g_ne
    have hg : ∀ q : ℕ, q.Prime → Y.d.l₂.GoodAt q := GlobalTheory.LawsDeep.goodAt_of_mul _ _ _ hY.1.lev.1.2.1 hg0
    have hU := hL.unf σ hσ
    have hM' : Y.d.l₂.M' = Y.d.l₂.M := by rw [Level.M', hY.1.lev.2, Nat.lcm_one_right]
    refine GlobalTheory.T.cuspForm_lower_bound_bergmanFunction_on_component (Fm.D x ι) ((i : ℕ) + 1) _ _ _ Y.d.Xo₂ Y.d.c₂ Y.U Y.dict hL σ hσ _ Z y hy _
      (fun x0 FF hx0 hFF => ?_)
    obtain ⟨x1, hx1, hla, htr⟩ := orth_transfer _ _ ((Y.U σ).X y.1)
      (modelWt (Y.U σ) (wtOf (dat p i) u1 0) y.1) y.2.1 y.2.2
    obtain ⟨hg1, hg2, hl1, hcard⟩ := modelWt_shape _ _ _ _ _ _ σ _ (Y.U σ) hσ hU hp1 hq1 u1
      (lenT p i (Fm.parT x hx ι).PP) (fun τ a b hab => by exact_mod_cast hgap τ a b hab) y.1
    have hcf : (((Y.U σ).X y.1).Ψ.card : ℝ) = (Fm.D x ι).R.f := by
      rw [hcard]; exact_mod_cast hWi.card
    have hball := ball_injects _ _ _ _ _ _ σ _ (Y.U σ) hσ hU hg hp1 hq1 y.1 x1 hx1 (by
      rw [hcf, hM', hla]; exact h100.trans hb)
    have hp0 := (hU.2.1 y.1).1
    have hr := hU.1
    obtain ⟨P, hP, hPx, hle⟩ := hpeak _ _ ((Y.U σ).X y.1) (modelWt (Y.U σ) (wtOf (dat p i) u1 0) y.1) x1
      (by rw [hp0]; exact hq1) (by rw [hp0, hr]; exact Nat.lt_add_of_pos_left hp1) hx1
      (fun τ a b hab hb0 => by rw [hcf]; exact hC08.trans (hg1 τ a b hab hb0))
      (fun τ a b ha hb' => by rw [hcf]; exact hC08.trans (hg2 τ a b ha hb')) hball x0 FF hx0 hFF
    obtain ⟨hPy, hpn⟩ := htr P hP hPx
    refine ⟨P, hP, hPy, ?_⟩
    rw [hpn]
    rw [hl1, hcf] at hle
    exact hle
end GlobalTheory.ThickBerg
end

section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.CovHt
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.bergman_kernel_thick_part_estimate : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → HypothesesH → DeepGood → Size → FlatDeg → Covers fun Fm x _ ι p i Y PP C => ∀ u1, Quo p i PP u1 → ∃ B : ℝ, 0 ≤ B ∧ lenT p i PP * B ≤ C * unitE p ∧ ∀ (Z : Comp Y.d.Xo₂ Y.d.c₂) (σ : Y.d.c₂.F →+* ℂ), GoodEmb Y.d.c₂ σ → ∀ y : FPt (Y.U σ).X, (⟨y.1, y.2.1⟩ : Σ k, Frame ((Y.U σ).X k).Ψ (Fm.D x ι).R.r) ∈ framesOn (Y.U σ) Z → (Fm.L x ι).sc.b ≤ (Y.d.l₂.M : ℝ) * ((Y.U σ).X y.1).firstMinimumSq y.2.1 → ENNReal.ofReal (Real.exp (-B)) ≤ bergOn (Y.U σ) ((Fm.D x ι).sp.W ((i : ℕ) + 1)) (Y.dict σ) Z (wtOf (dat p i) u1 0) y := by
  first | exact @_root_.GlobalTheory.ThickBerg.bergman_kernel_bound_thick_part | exact _root_.GlobalTheory.ThickBerg.bergman_kernel_bound_thick_part | (intros; apply _root_.GlobalTheory.ThickBerg.bergman_kernel_bound_thick_part <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.CoverTypeLatticeComparison
section
section
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cover_type_lattice_comparison : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → Gram → DeepGood → Covers fun Fm x _ ι p i Y _ _ => ∃ (fr : TypeFrame (dat p i) Y.d.l₂) (π : (LevelAut (dat p i) Y.d.l₂) →* G0g (Fm.D x ι).nd) (s : G0g (Fm.D x ι).nd →* (LevelAut (dat p i) Y.d.l₂)) (ρ : Representation ℂ (LevelAut (dat p i) Y.d.l₂) (ℂ ⊗[Y.d.c₂.F] Y.V (Gk p i))) (χ : (LevelAut (dat p i) Y.d.l₂) →* ℂˣ) (Pb : Subgroup (G0g (Fm.D x ι).nd)) (lam : Pb →* ℂˣ) (ψ : ∀ kv : (Σ k : Fin 2, (Fm.D x ι).nd.PlG k), AddChar (ZMod ((Fm.D x ι).host.g kv.1)) ℂ) (lamb : Pb.comap π →* ℂˣ) (H : Fin 2 → Subgroup (G0g (Fm.D x ι).nd)), IsSplit π s ∧ IsWhit (Fm.D x ι) Pb lam ψ ∧ (∀ γ : Pb.comap π, lamb γ = lam ⟨π γ, γ.2⟩) ∧ (∀ k, IsHalf (Fm.D x ι) k (H k)) ∧ Pb.comap π = grpHR fr ∧ (∀ k, (H k).comap π = grpGHR fr k) ∧ (∀ (g : (LevelAut (dat p i) Y.d.l₂)) (v w : Y.V (Gk p i)), (w : Rul Y.d.Xo₂ Y.d.c₂) = transl Y.d.Xo₂ Y.d.c₂ g v → ρ g ((1 : ℂ) ⊗ₜ[Y.d.c₂.F] v) = ((χ g : ℂˣ) : ℂ) • ((1 : ℂ) ⊗ₜ[Y.d.c₂.F] w)) ∧ Formalism.HN.rkK (latType p.R.toRealDat p.F.lv2 i) = Module.finrank ℂ (eig ρ (Pb.comap π) lamb) ∧ Formalism.HN.rkK (CovTop.latBad p.R.toRealDat p.F.lv2 i) = Module.finrank ℂ (eig ρ (Pb.comap π) lamb ⊓ LinearMap.ker (Representation.asAlgebraHom (ρ.comp s : Representation ℂ (G0g (Fm.D x ι).nd) (ℂ ⊗[Y.d.c₂.F] Y.V (Gk p i))) (Fm.D x ι).ntypes.e0) : Submodule ℂ (ℂ ⊗[Y.d.c₂.F] Y.V (Gk p i))) := by
  intro _ _ _
  refine GlobalTheory.CovTop.CovSz.covers_of_lifts (GlobalTheory.CovTop.Sizes.hostN 0) ?_
  intro eps Fm x hx ι p i C _ hN _ Y hY
  exact GlobalTheory.CovTop.BadRep.badRep_at p i Y hY
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.IsNefHodgeBundleTailWeight
section
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open GlobalTheory GlobalTheory.CechPic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi)
open GlobalTheory.HSApp
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.NefStep
theorem isNef_hodgeBundle_tailWeight : GlobalTheory.Published.SemiAbelianLieSeminegative → _root_.GlobalTheory.CovTop.Hypotheses'' → GlobalTheory.Published.NefNumerics → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (TF : TorFlag Xo c) (Z : Comp Xo c), FnAlgClosed Xo c → ∀ (τ : Psi H) (k : ℕ), Dw.p ≤ k → k + 1 < Dw.p + Dw.q → letI := algebraΓOfHom (str₀ TF.X Z); IsNef c.F (L₀ TF.X Z (GlobalTheory.NefWt.tailWt τ k)) := by
  intro h _ hN E _ _ _ H Dw l Xo c TF Z _ τ k hk _
  letI := algebraΓOfHom (str₀ TF.X Z)
  rw [L₀_tailWt TF.X Z τ k hk]
  have hq := FlagMod.mult_conj (Dw := Dw) τ
  exact isNef_pull_LL_stepEx TF.X.F h hN.1 c.F (inc₀ TF.X Z) _ (by omega)
end GlobalTheory.NefStep
end
end

section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open GlobalTheory GlobalTheory.CechPic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi)
open GlobalTheory.HSApp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hodgeBundle_tailWeight_nef : GlobalTheory.Published.SemiAbelianLieSeminegative → _root_.GlobalTheory.CovTop.Hypotheses'' → GlobalTheory.Published.NefNumerics → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (TF : TorFlag Xo c) (Z : Comp Xo c), FnAlgClosed Xo c → ∀ (τ : Psi H) (k : ℕ), Dw.p ≤ k → k + 1 < Dw.p + Dw.q → letI := algebraΓOfHom (str₀ TF.X Z); IsNef c.F (L₀ TF.X Z (GlobalTheory.NefWt.tailWt τ k)) := by
  first | exact @_root_.GlobalTheory.NefStep.isNef_hodgeBundle_tailWeight | exact _root_.GlobalTheory.NefStep.isNef_hodgeBundle_tailWeight | (intros; apply _root_.GlobalTheory.NefStep.isNef_hodgeBundle_tailWeight <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.ShiftedWeightLatticeFg
section
section
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct
open GlobalTheory.LamT (CMPt)
set_option synthInstance.maxHeartbeats 400000
noncomputable section
namespace GlobalTheory.CovTop.ShiftFG
set_option maxHeartbeats 1000000 in
theorem weight_lattice_pow_fg : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → ∀ (D : D7) (T : CoreJ D), LawsJ T → ∀ j : ℕ, 1 ≤ (T.Q.Dw j).p → 1 ≤ (T.Q.Dw j).q →
    2 < Module.finrank ℚ D.host.E / 2 → InR D j → ∀ (Y : Deep T.toCore j) (e : ℕ) (o : ℝ), Y.Good e o →
    ∀ (la : GlobalTheory.AllWt.Weight (T.Q.Dw j)), (∀ τ, Antitone (la τ)) → (∀ τ, 1 ≤ gap (la τ) ((T.Q.Dw j).p - 1)) →
    (∀ k : ℕ, Y.GoodAt (wtOf _ ((k + 1) • la) 0)) → ∀ m : ℕ, (GlobalTheory.AllWt.latW Y.U (wtOf _ la m)).FG := by
  intro _ D T _ j hp hq _ _ Y e o hY la hA hb _ m
  letI := T.Q.H.starRing
  haveI := GlobalTheory.Deep.finiteDimensional_V_of_good D T.toCore j Y e o hY (wtOf _ la m)
  refine GlobalTheory.fg_of_integral_functionals Y.d.c₂.F (Y.V (wtOf _ la m)) _ fun x hx => ?_
  obtain ⟨z, La, y, hz, hyx, hne⟩ := exists_good_cmPt_frame_ne_zero Y hY (fun _ => rfl) _ x.1 x.2
    (fun h => hx (Subtype.ext h))
  obtain ⟨N, hN, hint⟩ := GlobalTheory.T.exists_frame_denominator_dominant_weight_power_cm _ _ _ _ _ _ z _ La hz y hyx hp hq la hA hb m
  refine ⟨z.K, inferInstance, inferInstance, inferInstance,
    { toFun := fun F => N * evR Y.d.Xo₂ Y.d.c₂ F.1 y
      map_add' := fun F G => ?_
      map_smul' := fun s F => ?_ }, mul_ne_zero hN hne, fun F hF => hint F.1 (GlobalTheory.AllWt.cuspW_le_secZ _ F.2) hF⟩
  · rw [← mul_add]
    exact congrArg _ (evalAt_add _ _ F.1 G.1 y)
  · have e1 : evR Y.d.Xo₂ Y.d.c₂ (s • F).1 y = algebraMap Y.d.c₂.F z.K s * evR Y.d.Xo₂ Y.d.c₂ F.1 y :=
      evalAt_smul _ _ s F.1 y
    rw [e1, RingHom.id_apply, Algebra.smul_def, mul_left_comm]
end GlobalTheory.CovTop.ShiftFG
end
end

section
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.shifted_weight_lattice_fg : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → ∀ (D : D7) (T : CoreJ D), LawsJ T → ∀ j : ℕ, 1 ≤ (T.Q.Dw j).p → 1 ≤ (T.Q.Dw j).q → 2 < Module.finrank ℚ D.host.E / 2 → InR D j → ∀ (Y : Deep T.toCore j) (e : ℕ) (o : ℝ), Y.Good e o → ∀ (la : GlobalTheory.AllWt.Weight (T.Q.Dw j)), (∀ τ, Antitone (la τ)) → (∀ τ, 1 ≤ gap (la τ) ((T.Q.Dw j).p - 1)) → (∀ k : ℕ, Y.GoodAt (wtOf _ ((k + 1) • la) 0)) → ∀ m : ℕ, (GlobalTheory.AllWt.latW Y.U (wtOf _ la m)).FG := by
  first | exact @_root_.GlobalTheory.CovTop.ShiftFG.weight_lattice_pow_fg | exact _root_.GlobalTheory.CovTop.ShiftFG.weight_lattice_pow_fg | (intros; apply _root_.GlobalTheory.CovTop.ShiftFG.weight_lattice_pow_fg <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.ToroidalFlagNonempty
section
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
namespace GlobalTheory.CompHS.TorFlagEx
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}
theorem nonempty_torFlag_alt (hP : _root_.GlobalTheory.CovTop.Hypotheses'') :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H)
      (Xo : Moduli Dw l) (c : Coeff l), 1 ≤ dimFlag Dw → Nonempty (TorFlag Xo c) := by
  intro E _ _ _ H Dw l Xo c hd
  obtain ⟨Y, hs, hb, hk⟩ := hP.p1 E H Dw (one_le_of_dimFlag hd) l Xo c
  exact torFlag_of_model Y hs hb hk
    (pushInvertible_of_hasTheta Y (GlobalTheory.ThetaNormal.hasTheta_of_smooth E H Dw (one_le_of_dimFlag hd) l Xo c Y hs))
end GlobalTheory.CompHS.TorFlagEx
end

section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.torFlag_nonempty_of_one_le_dimFlag : _root_.GlobalTheory.CovTop.Hypotheses'' → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), 1 ≤ dimFlag Dw → Nonempty (TorFlag Xo c) := by
  first | exact @_root_.GlobalTheory.CompHS.TorFlagEx.nonempty_torFlag_alt | exact _root_.GlobalTheory.CompHS.TorFlagEx.nonempty_torFlag_alt | (intros; apply _root_.GlobalTheory.CompHS.TorFlagEx.nonempty_torFlag_alt <;> assumption)
end
end

