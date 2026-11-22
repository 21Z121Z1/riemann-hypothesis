import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsTjCorrDiagModel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2982
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3269
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1594
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0008
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.MemNonzeroLocusIffPowFn
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFramedChartSnc
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2546
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactification
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2412
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2423
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2389
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2380
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2391
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2386
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2502
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2381
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2544
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2406
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2398
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3244
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2474
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2471
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3265
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2712
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2822
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2405
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2506
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusHomOfIff
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0141
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0142
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UniformisationAdjointEndomorphismsCommute
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0047
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0076
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0135
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2963
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2961
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3271
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2968
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3258
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0084
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissiblePadicIntMaximalIdeal
import Development.AbelianVarietyTheory.Definitions.Divisors.IsRatioOfWeight
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0005
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3259
import Development.AbelianVarietyTheory.Definitions.Divisors.DivPowerCompatTwoFormDerivativeCompOneForm
import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CobOneEqZeroOfConnecting

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DescendedBundleKernelKilledPrimeToP
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES

namespace GlobalTheory.UPel.HT.ES.KerPowDescent

theorem pow_eq_one_of_lift {p : ℕ} [Fact p.Prime] {D : Datum p} {R : Type} [CommRing R] {b : Base D R} {N : ℕ}
    {S : Scheme.{0}} {s : S ⟶ Sp R} (o : Obj b N s) {A' : Over S} [GrpObj A'] [IsCommMonObj A'] (ψ : o.A ⟶ A')
    [IsMonHom ψ] (m : ℕ) {P' : LB (G2 A').left} (hP' : P'.IsLB)
    (hiso : LBIso (Hecke.lbPow o.P m) (P'.pull (sq2 ψ))) {e₀ : ℕ}
    (hker : ∀ (T : Over S) (x : T ⟶ o.A),
      (∃ t : (o.P.pull (lift (snd o.A T ≫ x) (fst o.A T)).left).Gen, t.IsGen) → x ^ e₀ = 1)
    {T T' : Over S} (π' : T' ⟶ T) (y : T' ⟶ o.A) (x : T ⟶ A') (hy : y ≫ ψ = π' ≫ x)
    (h0 : GlobalTheory.AbDual.evc hP' (snd A' T ≫ x) (fst A' T) = 0) : y ^ (m * e₀) = 1 := by
  have hP := o.isLB
  have hPm : (Hecke.lbPow o.P m).IsLB := LB.isLB_linComb hP _ _
  have hc : GlobalTheory.CechPic.cls _ hPm = m • GlobalTheory.CechPic.cls o.P hP := by
    refine (GlobalTheory.CechPic.cls_linComb hP (K := Fin m) (fun _ => 𝟙 _) (fun _ => 1) hPm).trans ?_
    simp only [GlobalTheory.CechPic.pull_id, one_smul, Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  have hc' : GlobalTheory.CechPic.cls _ hPm = GlobalTheory.CechPic.pull (sq2 ψ) (GlobalTheory.CechPic.cls P' hP') :=
    (GlobalTheory.CechPic.cls_eq_iff hPm (pull_isLB hP' _)).2 hiso
  have h1 := congrArg (GlobalTheory.CechPic.pull (lift (fst o.A T' ≫ ψ) (snd o.A T' ≫ π')).left) h0
  rw [GlobalTheory.AbDual.pull_evc, map_zero, lift_snd_assoc, lift_fst, Category.assoc, ← hy] at h1
  have e2 : GlobalTheory.AbDual.evc hP' (snd o.A T' ≫ y ≫ ψ) (fst o.A T' ≫ ψ) =
      GlobalTheory.CechPic.pull (lift (snd o.A T' ≫ y) (fst o.A T')).left
        (GlobalTheory.CechPic.pull (sq2 ψ) (GlobalTheory.CechPic.cls P' hP')) := by
    rw [← GlobalTheory.CechPic.pull_comp, GlobalTheory.AbDual.evc, sq2, ← Over.comp_left, comp_lift, lift_fst_assoc, lift_snd_assoc,
      Category.assoc]
  rw [e2, ← hc', hc, map_nsmul] at h1
  have h3 : GlobalTheory.AbDual.evc hP (snd o.A T' ≫ y ^ m) (fst o.A T') = 0 := by
    rw [comp_pow, Hecke.evc_pow_left o.ab hP o.rig₁ o.rig₂]
    exact h1
  have h4 := hker T' (y ^ m) ((GlobalTheory.AbDual.triv_ev_iff hP _ _).2 h3)
  rwa [← pow_mul] at h4

theorem kernel_primePower_descent : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ) (S : Scheme.{0}) (s : S ⟶ Sp R) (o : Obj b N s) (c : ℕ), (∃ e : ℕ, c = p ^ e) → IsUnit ((p : ℕ) : R) → ∀ (H : Subgroup (𝟙_ (Over S) ⟶ o.A)) (A' : Over S) [GrpObj A'] [IsCommMonObj A'] (ψ : o.A ⟶ A'), IsAbelianScheme A' → IsMonHom ψ → GlobalTheory.ZM.IsGaloisCover H (fun h => (transl h.1).left) ψ.left → (∀ (κ : Type) [Field κ] [IsAlgClosed κ] (x : Sp κ ⟶ S) (g : Over.mk x ⟶ o.A), g ^ c = 1 → (∀ h ∈ H, Out.WeilIs (G2 o.A) (Hecke.lbPow o.P c) 1 (lift g 1 : Over.mk x ⟶ G2 o.A) (lift 1 (toUnit (Over.mk x) ≫ h)) 1) → ∃ h ∈ H, g = toUnit (Over.mk x) ≫ h) → ∀ P' : LB (G2 A').left, P'.IsLB → (∃ t : (P'.pull (lift (1 : A' ⟶ A') (𝟙 A')).left).Gen, t.IsGen) → (∃ t : (P'.pull (lift (𝟙 A') (1 : A' ⟶ A')).left).Gen, t.IsGen) → LBIso (Hecke.lbPow o.P c) (P'.pull (sq2 ψ)) → ∃ e : ℕ, e.Coprime p ∧ ∀ (T : Over S) (x : T ⟶ A'), (∃ t : (P'.pull (lift (snd A' T ≫ x) (fst A' T)).left).Gen, t.IsGen) → x ^ e = 1 := by
  intro p _ D R _ b N S s o c hc hpu H A' _ _ ψ hA' hψ hG hH P' hP' r₁ r₂ hiso
  haveI := hψ
  obtain ⟨e₀, he₀, hker⟩ := o.kerP
  obtain ⟨e, rfl⟩ := hc
  refine ⟨e₀, he₀, ?_⟩
  intro T x hx
  have h0 : GlobalTheory.AbDual.evc hP' (snd A' T ≫ x) (fst A' T) = 0 := (GlobalTheory.AbDual.triv_ev_iff hP' _ _).1 hx
  have := hG.etale
  have := hG.fin
  have := hG.onto

  have hxc : x ^ (p ^ e * e₀) = 1 := by
    let T' : Over S := Over.mk (pullback.fst x.left ψ.left ≫ T.hom)
    let π' : T' ⟶ T := Over.homMk (pullback.fst x.left ψ.left) rfl
    let y : T' ⟶ o.A := Over.homMk (pullback.snd x.left ψ.left) (by
      show pullback.snd x.left ψ.left ≫ o.A.hom = pullback.fst x.left ψ.left ≫ T.hom
      rw [← Over.w ψ, ← Category.assoc, ← pullback.condition, Category.assoc, Over.w x])
    have hy : y ≫ ψ = π' ≫ x := Over.OverMorphism.ext (by
      show pullback.snd x.left ψ.left ≫ ψ.left = pullback.fst x.left ψ.left ≫ x.left
      exact pullback.condition.symm)
    have h4 := pow_eq_one_of_lift o ψ (p ^ e) hP' hiso hker π' y x hy h0
    have h5 : π' ≫ x ^ (p ^ e * e₀) = π' ≫ 1 := by
      rw [comp_pow, ← hy, ← GlobalTheory.SS.FrobTorsion.pow_comp' ψ y, h4, MonObj.one_comp, MonObj.comp_one]
    apply Over.OverMorphism.ext
    have h6 := congrArg (fun f => f.left) h5
    simp only [Over.comp_left] at h6
    exact (cancel_epi (pullback.fst x.left ψ.left)).1 h6
  have hu : IsUnit (((p ^ e : ℕ) : Γ(S, ⊤))) := by
    have := (hpu.pow e).map ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ s.appTop).hom
    simpa using this
  refine GlobalTheory.TorsionRigid.eq_one_of_pow_eq_one_of_geometric S A' hA' (p ^ e)
    (pow_pos (Fact.out : p.Prime).pos e) hu T (x ^ e₀) (by rw [← pow_mul, mul_comm]; exact hxc) ?_
  intro κ _ _ q
  let Tq : Over S := Over.mk (q ≫ T.hom)
  let πq : Tq ⟶ T := Over.homMk q rfl
  obtain ⟨pt, hpt⟩ := GlobalTheory.GeomSurj.exists_lift_of_surjective ψ.left (q ≫ x.left)
  let y : Tq ⟶ o.A := Over.homMk pt (by
    show pt ≫ o.A.hom = q ≫ T.hom
    rw [← Over.w ψ, ← Category.assoc, ← hpt, Category.assoc, Over.w x])
  have hy : y ≫ ψ = πq ≫ x := Over.OverMorphism.ext (by
    show pt ≫ ψ.left = q ≫ x.left
    exact hpt.symm)
  have h4 := pow_eq_one_of_lift o ψ (p ^ e) hP' hiso hker πq y x hy h0
  have hg : (y ^ e₀) ^ (p ^ e) = 1 := by rw [← pow_mul, mul_comm]; exact h4
  have hgψ : (y ^ e₀) ≫ ψ = (πq ≫ x) ^ e₀ := by rw [GlobalTheory.SS.FrobTorsion.pow_comp', hy]

  have hz : GlobalTheory.AbDual.evc hP' (snd A' Tq ≫ (y ^ e₀) ≫ ψ) (fst A' Tq) = 0 := by
    have h1 := congrArg (GlobalTheory.CechPic.pull (lift (fst A' Tq) (snd A' Tq ≫ πq)).left) h0
    rw [GlobalTheory.AbDual.pull_evc, map_zero, lift_snd_assoc, lift_fst] at h1
    simp only [Category.assoc] at h1
    rw [hgψ, comp_pow, Hecke.evc_pow_left hA' hP' r₁ r₂, h1, smul_zero]
  have hG0 := GlobalTheory.globalFns_holds
  have hA2 : IsAbelianScheme (G2 A') := AbelianSchemeGerms.isAbelianScheme_tensor A' A' hA' hA'
  have hAo2 : IsAbelianScheme (G2 o.A) := AbelianSchemeGerms.isAbelianScheme_tensor o.A o.A o.ab o.ab
  have s₁ : GlobalTheory.CechPic.pull (lift (1 : A' ⟶ A') (𝟙 A')).left (GlobalTheory.CechPic.cls P' hP') = 0 :=
    (GlobalTheory.CechPic.cls_eq_zero_iff (pull_isLB hP' _)).2 r₁
  have s₂ : GlobalTheory.CechPic.pull (lift (𝟙 A') (1 : A' ⟶ A')).left (GlobalTheory.CechPic.cls P' hP') = 0 :=
    (GlobalTheory.CechPic.cls_eq_zero_iff (pull_isLB hP' _)).2 r₂
  have hK : GlobalTheory.MemKL (G2 A') P' (lift ((y ^ e₀) ≫ ψ) 1 : Tq ⟶ G2 A') :=
    GlobalTheory.DualCon.TwistDescent.memKL_of_lam_eq_zero hP' _
      (GlobalTheory.KernelPointPairing.lam_eq_zero hP' hA' s₁ s₂ ((y ^ e₀) ≫ ψ) hz)
  have w₀ : Out.WeilIs (G2 A') P' 1 (lift ((y ^ e₀) ≫ ψ) 1 : Tq ⟶ G2 A') 1 1 :=
    GlobalTheory.DescendedPrincipal.weilIs_one_right hG0 hA2 hP' fun pp => by
      obtain ⟨V, hV, c, hc⟩ := hK pp
      exact ⟨V, hV, GlobalTheory.DescendedPrincipal.exists_theta_of_translDiff hP' _ V c hc⟩
  have hPc : (Hecke.lbPow o.P (p ^ e)).IsLB := LB.isLB_linComb o.isLB _ _
  let ψ2 : G2 o.A ⟶ G2 A' := lift (fst o.A o.A ≫ ψ) (snd o.A o.A ≫ ψ)
  haveI : IsMonHom ψ2 := inferInstance
  have hw : LBIso (Geo.Tor.lbPow (Hecke.lbPow o.P (p ^ e)) 1) (P'.pull ψ2.left) :=
    LBIso.trans (GlobalTheory.isLB_lbPow hPc 1) hPc (pull_isLB hP' _) (GlobalTheory.lbIso_lbPow_one hPc) hiso
  have hHψ : ∀ h ∈ H, h ≫ ψ = 1 := fun h hh => comp_eq_one_of_transl ψ h (hG.inv ⟨h, hh⟩)
  obtain ⟨h, hh, hgh⟩ := hH κ (q ≫ T.hom) (y ^ e₀) hg fun h hh => by
    have e1 : (lift (y ^ e₀) 1 : Tq ⟶ G2 o.A) ≫ ψ2 = lift ((y ^ e₀) ≫ ψ) 1 := by
      rw [comp_lift, lift_fst_assoc, lift_snd_assoc, MonObj.one_comp]
    have e2 : (lift 1 (toUnit Tq ≫ h) : Tq ⟶ G2 o.A) ≫ ψ2 = 1 := by
      rw [comp_lift, lift_fst_assoc, lift_snd_assoc, MonObj.one_comp, Category.assoc, hHψ h hh, MonObj.comp_one]
      apply CartesianMonoidalCategory.hom_ext <;> simp
    have := GlobalTheory.WeilIsogeny.weilIs_pull_hom hG0 hAo2 hPc hP' ψ2 hw (n := 1) (x := lift (y ^ e₀) 1)
      (y := lift 1 (toUnit Tq ≫ h)) (c := 1) (by rw [e1, e2]; exact w₀)
    simpa using this
  show πq ≫ x ^ e₀ = 1
  rw [comp_pow, ← hgψ, hgh, Category.assoc, hHψ h hh, MonObj.comp_one]

end GlobalTheory.UPel.HT.ES.KerPowDescent
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DetLineTrivialOfToroidal
section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.HermitianCompactForm GlobalTheory.Toroidal GlobalTheory.ShFam
  GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor

namespace GlobalTheory.DetLine

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Geo.Tor.Host E} {D : Datum H} {l : Level H}

theorem good_or (c : Coeff l) (e : c.F →+* ℂ) :
    Formalism.L2.PjFree.GoodEmb c e ∨ Formalism.L2.PjFree.GoodEmb c ((starRingEnd ℂ).comp e) := by
  set z := (e.comp (IntermediateField.inclusion c.le).toRingHom) (baseKA l).ρ with hz
  have h1 : z ^ 2 = H.rt0 ^ 2 := by rw [hz, ← map_pow, (baseKA l).ρ_sq, H.sqrt_neg_disc_sq]; simp
  rcases sq_eq_sq_iff_eq_or_eq_neg.1 h1 with h | h
  · exact .inl h
  · refine .inr (show starRingEnd ℂ z = H.rt0 from ?_)
    have h4 := H.sqrt_neg_disc_sq
    have h5 := congrArg Complex.im h4
    have h6 := congrArg Complex.re h4
    have h7 : (0 : ℝ) < H.d := Nat.cast_pos.2 H.d_prime.pos
    simp [pow_two] at h5 h6
    have h8 : H.rt0.re = 0 := by
      by_contra h0
      have : H.rt0.im = 0 := by
        have : H.rt0.re * H.rt0.im = 0 := by linarith
        exact (mul_eq_zero.1 this).resolve_left h0
      rw [this] at h6
      nlinarith [mul_self_nonneg H.rt0.re]
    rw [h]
    exact Complex.ext (by simp [h8]) (by simp)

section Unique

variable {S X : Scheme.{0}} {c : Coeff l} {t : SAB H S} {π : X ⟶ S} {s : X ⟶ Sp c.F} {τ : E →+* ℂ} {p q : ℕ}

theorem existsUnique_multiple {V : X.Opens} (hne : (V : Set X).Nonempty)
    (hc : FrameCover t π s V (HermitianCompactForm.chi c τ) p q) {σ σ' : Rule t π p q} (hz : NowhereZero t π s V (HermitianCompactForm.chi c τ) σ)
    (a : c.F) (h : ∀ (R : Type) [CommRing R] (j : c.F →+* R) (x : Sp R ⟶ X) v w,
      IsFrame t π s V (HermitianCompactForm.chi c τ) j x v w → σ' R x v w = valR x V (Geo.Tor.constFn s V a) * σ R x v w) :
    ∃! a : c.F, IsMultiple t π s V (HermitianCompactForm.chi c τ) σ' a σ := by
  have h1 : IsMultiple t π s V (HermitianCompactForm.chi c τ) σ' a σ := fun R _ j x v w hf => by
    rw [h R j x v w hf, GlobalTheory.Points.valR_constFn_of_over s j x hf.1 V (fun z _ => hf.2.1 ⟨z, rfl⟩)]
  refine ⟨a, h1, fun b hb => ?_⟩
  obtain ⟨z, hzV⟩ := hne
  obtain ⟨W, hW, j, v, w, hzW, hf⟩ := hc z hzV
  have : Nonempty W := ⟨⟨z, hzW⟩⟩
  have : Nontrivial Γ(X, W) := Scheme.component_nontrivial X W
  exact j.injective ((hz _ j _ v w hf).mul_right_cancel ((hb _ j _ v w hf).symm.trans (h1 _ j _ v w hf)))

end Unique

variable {Xo : Moduli D l} {c : Coeff l}

theorem nonempty_of_geomConn {U : (Xo.XF c).Opens} (hG : GeometricallyConnected (U.ι ≫ toF Xo c)) :
    (U : Set (Xo.XF c)).Nonempty := by
  have := GlobalTheory.T.isIntegral_geometricallyConnected_open_moduli E H D l Xo c U hG
  exact ⟨_, (genericPoint U.toScheme).2⟩

theorem flat_unique {U : (Xo.XF c).Opens} (hG : GeometricallyConnected (U.ι ≫ toF Xo c)) {τ : E →+* ℂ}
    (hτ : τ (H.rt : E) = H.rt0) (e : c.F →+* ℂ) (hT : HasTransport Xo c U e) {σ σ' : RuleU Xo c}
    (hs : SecU Xo c U τ σ) (hz : NzU Xo c U τ σ) (hf : IsFlatAt Xo c U τ σ e) (hs' : SecU Xo c U τ σ')
    (hf' : IsFlatAt Xo c U τ σ' e) :
    ∃! a : c.F, IsMultiple Xo.univ.t (toX Xo c) (toF Xo c) U (HermitianCompactForm.chi c τ) σ' a σ := by
  have hc := GlobalTheory.T.moduliScheme_affineFrameCover_two_eigenParts E H D l Xo c U τ hτ
  obtain ⟨f, hr⟩ := GlobalTheory.T.exists_lieDeterminantLine_ratio_function E H l c _ _ _ _ _ τ _ _ U σ σ' hc hs hz hs'
  have fr : ∀ y : Sp ℂ ⟶ Xo.XF c, y ≫ toF Xo c = spMap e → Set.range y ⊆ U → ∃ v w, FrU Xo c U τ e y v w :=
    fun y hy hU => by
      obtain ⟨W, hW, j, v, w, hzW, h⟩ := hc _ (hU ⟨IsLocalRing.closedPoint ℂ, rfl⟩)
      have hle : ⊤ ≤ y ⁻¹ᵁ W := (GlobalTheory.Points.le_preimage_iff y W).2 hzW
      have hy' := (GlobalTheory.Points.specMap_valMap_fromSpec hW y hle).symm
      obtain ⟨v', w', h', -⟩ := exists_pull (GlobalTheory.Points.valMap y W hle).hom h hy'
      obtain rfl : e = (GlobalTheory.Points.valMap y W hle).hom.comp j :=
        congrArg CommRingCat.Hom.hom (Spec.map_injective (hy.symm.trans h'.1))
      exact ⟨v', w', h'⟩
  obtain ⟨a, rfl⟩ := GlobalTheory.T.exists_constant_component_function_complexValues E H D l Xo c U e f hG fun y y' hy hy' hU hU' => by
    obtain ⟨v, w, h⟩ := fr y hy hU
    obtain ⟨v', w', h'⟩ := fr y' hy' hU'
    obtain ⟨o, m, g, u, Hm, κ, V, W, hA, hV, hW, iV, iW⟩ := GlobalTheory.T.exists_uniformised_fibre_of_framed_complex_point E H D l Xo c U τ e y v w h
    obtain ⟨o', m', g', u', Hm', κ', V', W', hA', hV', hW', -⟩ := GlobalTheory.T.exists_uniformised_fibre_of_framed_complex_point E H D l Xo c U τ e y' v' w' h'
    obtain ⟨φ, hφ⟩ := hT y y' hy hy' hU hU' o o' ⟨m⟩ ⟨m'⟩ g g' u u' Hm Hm' κ κ' hA hA'
    obtain ⟨x, Δ, hΔ, hx⟩ := (GlobalTheory.T.exists_homologyWedgeCoordinate_nonzero g _ _ Hm V W hA.1 hA.2.1).2 iV iW
    obtain ⟨Δ', hx'⟩ := (GlobalTheory.T.exists_homologyWedgeCoordinate_nonzero g' _ _ Hm' V' W' hA'.1 hA'.2.1).1 fun k => φ (x k)
    have e1 := hf y y' v w v' w' h h' o o' m m' g g' u u' Hm Hm' κ κ' φ V W V' W' x Δ Δ' hA hA' hφ hV hW hV' hW' hx hx'
    have e2 := hf' y y' v w v' w' h h' o o' m m' g g' u u' Hm Hm' κ κ' φ V W V' W' x Δ Δ' hA hA' hφ hV hW hV' hW' hx hx'
    rw [hr ℂ e y v w h, hr ℂ e y' v' w' h', _root_.mul_assoc, _root_.mul_assoc, e1] at e2
    exact mul_right_cancel₀ (mul_ne_zero (hz ℂ e y' v' w' h').ne_zero hΔ) e2
  exact existsUnique_multiple (nonempty_of_geomConn hG) hc hz a hr

theorem cpt_unique {O : Type} [CommRing O] {β : O →+* c.F} (Y : Model Xo c β) {U : (Xo.XF c).Opens}
    (hN : Geo.Tor.IsNormalScheme (gen Y)) (hU : IsClosed (U : Set (Xo.XF c)))
    (hG : GeometricallyConnected (U.ι ≫ toF Xo c)) {τ : E →+* ℂ} (hτ : τ (H.rt : E) = H.rt0) {σ σ' : RuleY Y}
    (hs : SecY Y (compactOf Y U) τ σ) (hz : NzY Y (compactOf Y U) τ σ) (hs' : SecY Y (compactOf Y U) τ σ') :
    ∃! a : c.F, IsMultiple Y.t (genι Y) (genStr Y) (compactOf Y U) (HermitianCompactForm.chi c τ) σ' a σ := by
  obtain ⟨V, hV, -⟩ := GlobalTheory.T.genericFibre_componentClosure_open_isIntegral E H D l Xo c O β Y U hN hU hG
  have hne : (V : Set (gen Y)).Nonempty := hV ▸ ((nonempty_of_geomConn hG).image _).closure
  have hk := GlobalTheory.T.exists_constant_function_normal_compactification E H D l Xo c O β Y U V hN hU hG hV
  rw [← hV] at hs hz hs' ⊢
  have hc := GlobalTheory.T.toroidalGenericFibre_affineFrameCover E H D l Xo c O β Y V τ hτ
  obtain ⟨f, hr⟩ := GlobalTheory.T.exists_lieDeterminantLine_ratio_function E H l c _ _ _ _ _ τ _ _ V σ σ' hc hs hz hs'
  obtain ⟨a, rfl⟩ := hk f
  exact existsUnique_multiple hne hc hz a hr

def HasFlatSection (Xo : Moduli D l) (c : Coeff l) (U : (Xo.XF c).Opens) (τ : E →+* ℂ) : Prop :=
  (∀ e : c.F →+* ℂ, HasTransport Xo c U e) ∧ ∃ σ : RuleU Xo c, SecU Xo c U τ σ ∧ NzU Xo c U τ σ ∧
    (∀ e : c.F →+* ℂ, IsFlatAt Xo c U τ σ e) ∧
    ∀ (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β), Geo.Tor.IsNormalScheme (gen Y) →
      ∃ σb : RuleY Y, SecY Y (compactOf Y U) τ σb ∧ NzY Y (compactOf Y U) τ σb ∧ Restricts Y U τ σb σ

theorem exists_of_rank_zero (U : (Xo.XF c).Opens) (τ : E →+* ℂ) (h : D.p + D.q = 0) : HasFlatSection Xo c U τ := by
  have : IsEmpty (Fin D.p) := ⟨fun i => by have := i.2; omega⟩
  have : IsEmpty (Fin D.q) := ⟨fun i => by have := i.2; omega⟩
  refine ⟨fun e => GlobalTheory.T.hasMarkingPreservingTransport_of_rank_zero E H D l Xo c U e h, fun _ _ _ _ _ => 1,
    isSection_of_chg fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => by simp [Matrix.det_isEmpty],
    fun _ _ _ _ _ _ _ => isUnit_one, fun e => ?_, fun O _ β Y _ => ⟨fun _ _ _ _ _ => 1,
    isSection_of_chg fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => by simp [Matrix.det_isEmpty],
    fun _ _ _ _ _ _ _ => isUnit_one, fun _ _ _ _ _ _ _ _ _ _ _ _ => rfl⟩⟩
  intro y y' v w v' w' _ _ o o' m m' g g' u u' Hm Hm' κ κ' φ V W V' W' x Δ Δ' _ _ _ _ _ _ _ ⟨a, _, ha⟩ ⟨a', _, ha'⟩
  rw [ha, ha', Matrix.det_isEmpty, Matrix.det_isEmpty]

theorem exists_of_snc {O : Type} [CommRing O] {β : O →+* c.F} (Z : Model Xo c β)
    (hsm : SmoothOfRelativeDimension D.dim (genStr Z)) (hsnc : ReciprocityTheory.AnForm.R.FinalTheorems.Snc (genBdIdeal Z))
    {U : (Xo.XF c).Opens} (hU : IsClosed (U : Set (Xo.XF c))) (hG : GeometricallyConnected (U.ι ≫ toF Xo c))
    {τ : E →+* ℂ} (hτ : τ (H.rt : E) = H.rt0) (hr : 1 ≤ D.p + D.q) : HasFlatSection Xo c U τ := by
  obtain ⟨B, io, h1, h2, h3⟩ := GlobalTheory.T.exists_variety_compactifying_connected_component E H D l Xo c O β Z U hsm hU hG
  have fam : ∀ e : c.F →+* ℂ, Formalism.L2.PjFree.GoodEmb c e → ∃ (g : ℕ) (en : Fin g ≃ Pad.Letter D) (Fu : Fam Xo c e en)
      (x : ∀ i, Idx D τ → (Fu.Di i).La) (hm : Fin Fu.n → Matrix (Idx D τ) (Idx D τ) E),
      ∀ i, IsPerBasis (Fu.Di i) (x i) (hm i) := fun e he => by
    let en : Fin (Fintype.card (Pad.Letter D)) ≃ Pad.Letter D := (Fintype.equivFin _).symm
    obtain ⟨Fu⟩ := GlobalTheory.closing_of_abelianSchemeLaws E H D l Xo (e.comp (IntermediateField.inclusion c.le).toRingHom) _
      (fun j => Formalism.L2.PjFree.relab c e (en j).1) hr he ((GlobalTheory.Relab.relab_good E H l c e he).2.2.2 D _ en)
    choose x hm hx using fun i : Fin Fu.n => GlobalTheory.T.exists_hermitianPeriodLatticeBasis_same_signature _ H D (Fu.Di i) τ (Fu.sig i)
    exact ⟨_, en, Fu, x, hm, hx⟩
  obtain ⟨e₀, he₀⟩ : ∃ e₀, Formalism.L2.PjFree.GoodEmb c e₀ := (good_or c c.F.val.toRingHom).elim (⟨_, ·⟩) (⟨_, ·⟩)
  obtain ⟨g₀, en₀, Fu₀, x₀, hm₀, hx₀⟩ := fam e₀ he₀
  obtain ⟨σZ, hsZ, hzZ⟩ := GlobalTheory.T.exists_nonvanishing_detLine_section_of_horizontal E H D l Xo c O β Z τ e₀ _ B io _ h1 h2 h3 hτ (horFn_horOf_snc hsm hsnc he₀ hr hx₀)
  obtain ⟨σ, hs, hres, hz⟩ := GlobalTheory.T.exists_determinantLine_section_restriction E H D l Xo c O β Z U τ σZ hsZ
  have hflat : ∀ e, Formalism.L2.PjFree.GoodEmb c e → IsFlatAt Xo c U τ σ e := fun e he => by
    obtain ⟨g, en, Fu, x, hm, hx⟩ := fam e he
    obtain ⟨κ, hκ⟩ := GlobalTheory.T.exists_const_mul_horizontalDetLieCoordinate E H D l Xo c O β Z τ e _ B io _ h1 h2 h3 hτ (horFn_horOf_snc hsm hsnc he hr hx) σZ hsZ
    refine GlobalTheory.T.isFlat_of_const_mul_periodDeterminant E H D l Xo c O β Z U τ e g en Fu x hm σZ σ κ B io hU h1 h2 h3 hτ hx hres
      fun a v w i Q hP hf hM => ?_
    rw [← horOf_eq_perVal hx a i Q hP]
    refine hκ a v w ?_ hf hM
    obtain ⟨P, W, y, -, -, hy, -⟩ := hP
    exact fun h => h ⟨y (IsLocalRing.closedPoint ℂ), by rw [← hy]; exact (Scheme.Hom.comp_apply _ _ _).symm⟩
  refine ⟨fun e => ?_, σ, hs, hz hzZ, fun e => ?_, fun O' _ β' Y hN =>
    GlobalTheory.T.exists_nonvanishing_extension_normal_compactification E H D l Xo c O' β' Y O β Z U τ σZ σ hN hU hG hτ hsZ hzZ hs hres⟩
  · rcases good_or c e with he | he
    · exact GlobalTheory.T.hasMarkingTransport_of_cmType_embedding E H D l Xo c O β Z U e B io hU h1 h2 h3 hr he
    · exact GlobalTheory.T.hasMarkingPreservingTransport_of_conj_embedding E H D l Xo c U e (GlobalTheory.T.hasMarkingTransport_of_cmType_embedding E H D l Xo c O β Z U _ B io hU h1 h2 h3 hr he)
  · rcases good_or c e with he | he
    · exact hflat e he
    · exact GlobalTheory.T.isHorizontalLieDeterminantSection_of_conj E H D l Xo c U τ σ e hs (hflat _ he)

theorem detLineTrivial_of_toroidal (hT : GlobalTheory.Published.ToroidalCompactification) : DetLineTrivial := by
  intro E _ _ _ H D l Xo c U hU hG τ hτ
  have hex : HasFlatSection Xo c U τ := by
    rcases Nat.eq_zero_or_pos (D.p + D.q) with h | h
    · exact exists_of_rank_zero U τ h
    · obtain ⟨Z, hsm, hsnc, -⟩ := hT E H D h l Xo c
      exact exists_of_snc Z
        ((smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback (IsPullback.of_hasPullback _ _) hsm)
        (GlobalTheory.VarFlag.snc_genBdIdeal_of_snc_boundary hsnc) hU hG hτ h
  obtain ⟨htr, σ, hs, hz, hf, hY⟩ := hex
  refine ⟨htr, σ, hs, hz, hf, fun σ' hs' hf' => ?_, fun O _ β Y hN => ?_⟩
  · exact flat_unique hG hτ c.F.val.toRingHom (htr _) hs hz (hf _) hs' (hf' _)
  · obtain ⟨σb, h1, h2, h3⟩ := hY O β Y hN
    exact ⟨σb, h1, h2, h3, fun σ' h' => cpt_unique Y hN hU hG hτ h1 h2 h'⟩

end GlobalTheory.DetLine
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAlgClosedFieldTorsionMapsCommuteHom
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.Mum GlobalTheory.Mum.Two

noncomputable section
namespace GlobalTheory.Mum.Two

open GlobalTheory.Balanced

section Gen
variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D₁ D₂ : DegData R I}
  {A₁ A₂ : PolAV (Sp (FractionRing R))} {G₁ G₂ : Over (Sp R)} [GrpObj G₁] [IsCommMonObj G₁] [GrpObj G₂]
  [IsCommMonObj G₂] {U₁ : UnifPre I D₁ A₁ G₁} {U₂ : UnifPre I D₂ A₂ G₂}

theorem toG_gen₀ {a : G₁ ⟶ G₂} {c : A₁.A ⟶ A₂.A} (hc : Gen₀ U₁ U₂ a c) {F : Type} [Field F]
    [Algebra (FractionRing R) F] (x : TFK (R := R) F ⟶ A₁.A) : toG U₂ (x ≫ c) = toG U₁ x ≫ a.left := by
  have e : c ≫ U₂.gen.inv = U₁.gen.inv ≫ (Over.pullback (jK R)).map a := by
    rw [Iso.eq_inv_comp, ← Category.assoc, ← hc, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  have e' : c.left ≫ U₂.gen.inv.left = U₁.gen.inv.left ≫ ((Over.pullback (jK R)).map a).left :=
    congrArg (fun q => q.left) e
  have e₂ : ((Over.pullback (jK R)).map a).left ≫ pullback.fst G₂.hom (jK R) = pullback.fst G₁.hom (jK R) ≫ a.left :=
    pullback.lift_fst _ _ _
  calc toG U₂ (x ≫ c) = x.left ≫ (c.left ≫ U₂.gen.inv.left) ≫ pullback.fst G₂.hom (jK R) := by
        simp only [toG, Over.comp_left, Category.assoc]
    _ = _ := by rw [e', Category.assoc, e₂, toG, Category.assoc, Category.assoc]

end Gen

theorem exists_toG_pull {R V : Type} [CommRing R] [IsDomain R] [CommRing V] [IsDomain V] {I : Ideal R} {I' : Ideal V}
    (φ : R →+* V) {D : DegData R I} {D' : DegData V I'} {A : PolAV (Sp (FractionRing R))}
    {A' : PolAV (Sp (FractionRing V))} {G : Over (Sp R)} [GrpObj G] [IsCommMonObj G]
    (U : UnifPre I D A G) (U' : UnifPre I' D' A' ((Over.pullback (specOf φ)).obj G))
    {F : Type} [Field F] [Algebra (FractionRing R) F] [Algebra (FractionRing V) F]
    (hF : ∀ r : R, algebraMap (FractionRing R) F (algebraMap R _ r) =
      algebraMap (FractionRing V) F (algebraMap V _ (φ r))) (z : TFK (R := R) F ⟶ A.A) :
    ∃ z' : TFK (R := V) F ⟶ A'.A, toG U' z' ≫ pullback.fst G.hom (specOf φ) = toG U z := by
  have w : toG U z ≫ G.hom = (jFK (R := V) F ≫ jK V) ≫ specOf φ := by
    rw [toG_over]
    simp only [jFK, jK, specOf, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    exact RingHom.ext hF
  obtain ⟨z', hz'⟩ := exists_toG U' (pullback.lift _ _ w) (pullback.lift_snd _ _ _)
  exact ⟨z', by rw [hz']; exact pullback.lift_fst _ _ _⟩

set_option maxHeartbeats 2000000 in

theorem exists_key : ∀ (R : Type) [CommRing R] [IsDomain R] [CharZero R] (I : Ideal R), AdmBase R I → ∀ (D₁ D₂ : DegData R I) (A₁ A₂ : PolAV (Sp (FractionRing R))) (G₁ G₂ : Over (Sp R)) [GrpObj G₁] [IsCommMonObj G₁] [GrpObj G₂] [IsCommMonObj G₂], IsSemiAbelian G₁ → IsSemiAbelian G₂ → ∀ (U₁ : Unif I D₁ A₁ G₁) (U₂ : Unif I D₂ A₂ G₂) (a : G₁ ⟶ G₂) (c : A₁.A ⟶ A₂.A) (b : D₁.toPre.P.A ⟶ D₂.toPre.P.A) (h : D₂.toPre.X →+ D₁.toPre.X), IsMonHom c → Gen₀ U₁.toUnifPre U₂.toUnifPre a c → Lin U₁.toUnifPre U₂.toUnifPre a b h → Coord U₁.toUnifPre U₂.toUnifPre a b h → Function.Injective h → ∃ (F : Type) (_ : Field F) (_ : IsAlgClosed F) (_ : Algebra (FractionRing R) F), Key U₁.toUnifPre U₂.toUnifPre c b h F := by
  intro R _ _ _ I hR D₁ D₂ A₁ A₂ G₁ G₂ _ _ _ _ hG₁ hG₂ U₁ U₂ a c b h _ hgen hlin hcoord hinj
  have hL := GlobalTheory.firstFiveLaws
  obtain ⟨V, _, _, _, φ, hV, hφ, hI⟩ := GlobalTheory.adic_base_embeds_valuation_algebraic_closure.1 R I hR
  have : CharZero V := charZero_of_injective_ringHom hφ
  have hR' : AdmBase V (maximalIdeal V) := ⟨inferInstance, inferInstance, inferInstance, hV⟩
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible V
  obtain ⟨v, hv⟩ := GlobalTheory.adic_base_embeds_valuation_algebraic_closure.2 V ϖ hϖ
  obtain ⟨D₁', hD₁, A₁', U₁', hG₁', hU₁, hpt₁, -⟩ := GlobalTheory.T.uniformisation_endomorphisms_to_complete_dvr hL R I hR D₁ A₁ G₁ hG₁ U₁ V φ hV hφ hI
  obtain ⟨D₂', hD₂, A₂', U₂', hG₂', hU₂, hpt₂, -⟩ := GlobalTheory.T.uniformisation_endomorphisms_to_complete_dvr hL R I hR D₂ A₂ G₂ hG₂ U₂ V φ hV hφ hI
  let Ω := AlgebraicClosure (FractionRing V)
  let ψ : R →+* Ω := ((algebraMap (FractionRing V) Ω).comp (algebraMap V (FractionRing V))).comp φ
  have hψ : Function.Injective ψ :=
    ((algebraMap (FractionRing V) Ω).injective.comp (IsFractionRing.injective V (FractionRing V))).comp hφ
  let _ : Algebra (FractionRing R) Ω := (IsFractionRing.lift hψ).toAlgebra
  have hF : ∀ r : R, algebraMap (FractionRing R) Ω (algebraMap R _ r) =
      algebraMap (FractionRing V) Ω (algebraMap V _ (φ r)) := fun r => IsFractionRing.lift_algebraMap hψ r
  obtain ⟨ex₁, -, io₁, ns₁⟩ := hpt₁ Ω hF
  obtain ⟨ex₂, sur₂, io₂, ns₂⟩ := hpt₂ Ω hF
  obtain ⟨b', h', hlin', hb', hh'⟩ := GlobalTheory.T.uniformisedGroupHom_pullback_maps R V I (maximalIdeal V) φ D₁ D₂ A₁ A₂ G₁ G₂ U₁ U₂ D₁' D₂' A₁' A₂'
    hD₁ hD₂ U₁' U₂' hU₁ hU₂ a b h hlin
  have hcoord' := GlobalTheory.T.torusCoordinates_compare_normalisedGenerators V (maximalIdeal V) hR' D₁' D₂' A₁' A₂' _ _ U₁'.toUnifPre U₂'.toUnifPre
    ((Over.pullback (specOf φ)).map a) b' h' hlin'
  let c' : A₁'.A ⟶ A₂'.A := U₁'.gen.inv ≫ (Over.pullback (jK V)).map ((Over.pullback (specOf φ)).map a) ≫ U₂'.gen.hom
  have hgen' : Gen₀ U₁'.toUnifPre U₂'.toUnifPre ((Over.pullback (specOf φ)).map a) c' := by
    simp only [Gen₀, c', Iso.hom_inv_id_assoc]
  have hc' : IsMonHom c' := by
    have := U₁'.gen_hom
    have := U₂'.gen_hom
    have := hlin'.1
    dsimp only [c']
    infer_instance
  have hinj' : Function.Injective h' := fun x y hxy => hD₂.xe.injective (hinj (by rw [← hh', ← hh', hxy]))
  have key' := GlobalTheory.T.trait_torsion_point_map_commutes_char_injective_hom V hV ϖ hϖ Ω v hv D₁' D₂' A₁' A₂' _ _ hG₁' hG₂' U₁' U₂' ((Over.pullback (specOf φ)).map a)
    c' b' h' hc' hgen' hlin' hcoord' hinj'
  choose π₁ hπ₁ _ using ex₁
  choose π₂ hπ₂ _ using ex₂
  refine ⟨Ω, inferInstance, inferInstance, inferInstance, fun k hk p x hx g' hact => ?_⟩
  have hact' : Act D₁'.toPre D₂'.toPre b' h' (π₁ p.g) (π₂ g') :=
    (GlobalTheory.T.torusExtensionPointAction_pullback_data R V φ D₁.toPre D₂.toPre D₁'.toPre D₂'.toPre hD₁ hD₂ b h b' h' hlin.2.1 hlin'.2.1 hb' hh'
      (fun χ => (hcoord χ).imp fun _ hu => hu.1) Ω p.g g' (π₁ p.g) (π₂ g') (hπ₁ _) (hπ₂ _)).1 hact
  let ρp : QkPt D₁'.toPre Ω k := ⟨hD₁.xe.symm p.y, π₁ p.g, by
    obtain ⟨s, h1, h2⟩ := p.eq
    exact ⟨π₁ s, (ns₁ k _ _ _ _ (hπ₁ _) (hπ₁ _)).1 h1, (io₁ _ _ _ (hπ₁ _)).1 (by rwa [AddEquiv.apply_symm_apply])⟩⟩
  obtain ⟨x', hx'e⟩ := exists_toG_pull φ U₁.toUnifPre U₁'.toUnifPre hF x
  have hx' : QkToAkU U₁'.toUnifPre Ω k ρp x' :=
    hL.2.2.2.2.qkBaseChange R V I _ hR hR' φ D₁ A₁ G₁ U₁ _ (Iso.refl _) (inferInstanceAs (IsMonHom (𝟙 _))) A₁' D₁'
      hD₁ U₁' hU₁ Ω hF k hk p x ρp x' rfl (hπ₁ _)
      (by simpa only [toG, Category.assoc, Iso.refl_hom, Over.id_left, Category.id_comp] using hx'e) hx
  obtain ⟨r, rg, hr⟩ := key' k hk ρp x' hx' (π₂ g') hact'
  let p' : QkPt D₂.toPre Ω k := ⟨hD₂.xe r.y, g', by
    obtain ⟨s', h1, h2⟩ := r.eq
    obtain ⟨s, hs, -⟩ := sur₂ s'
    exact ⟨s, (ns₂ k _ _ _ _ (hπ₂ g') hs).2 (rg ▸ h1), (io₂ _ _ _ hs).2 h2⟩⟩
  refine ⟨p', rfl, ?_⟩
  obtain ⟨f₂, hf₂, -⟩ := GlobalTheory.T.uniformisation_torsion_identification_with_pairing hL R I hR D₂ A₂ G₂ hG₂ U₂ Ω k hk
  obtain ⟨f₂', hf₂', -⟩ := GlobalTheory.T.uniformisation_torsion_identification_with_pairing hL V _ hR' D₂' A₂' _ hG₂' U₂' Ω k hk
  obtain ⟨z', hz'e⟩ := exists_toG_pull φ U₂.toUnifPre U₂'.toUnifPre hF (f₂ p')
  have hz' : QkToAkU U₂'.toUnifPre Ω k r z' :=
    hL.2.2.2.2.qkBaseChange R V I _ hR hR' φ D₂ A₂ G₂ U₂ _ (Iso.refl _) (inferInstanceAs (IsMonHom (𝟙 _))) A₂' D₂'
      hD₂ U₂' hU₂ Ω hF k hk p' (f₂ p') r z' (hD₂.xe.symm_apply_apply r.y).symm (rg ▸ hπ₂ g')
      (by simpa only [toG, Category.assoc, Iso.refl_hom, Over.id_left, Category.id_comp] using hz'e) ((hf₂ _ _).2 rfl)
  have ez : z' = x' ≫ c' := ((hf₂' _ _).1 hz').trans ((hf₂' _ _).1 hr).symm
  have hpa : ((Over.pullback (specOf φ)).map a).left ≫ pullback.fst G₂.hom (specOf φ) =
      pullback.fst G₁.hom (specOf φ) ≫ a.left := pullback.lift_fst _ _ _
  refine (hf₂ _ _).2 (toG_injective U₂.toUnifPre ?_).symm
  rw [← hz'e, ez, toG_gen₀ hgen', toG_gen₀ hgen, ← hx'e, Category.assoc, Category.assoc, hpa]

end GlobalTheory.Mum.Two
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCommonScaleThetaConstantsAtTraitStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.SiegTh Classical
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_common_scale_thetaConstants_at_trait : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (m N : ℕ) (e : Fin N → Ω), Odd m → 3 ≤ m → IsUnit (m : o) → N = m ^ (4 * S.g) → SymE ρ m e → ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], GlobalTheory.LN.CDvr V → ∀ (emb : Ω →+* FractionRing V), (∀ a : o, emb (algebraMap o Ω a) ∈ Set.range (algebraMap V (FractionRing V))) → ∃ (K : Type) (_ : Field K) (io : FractionRing V →+* K) (N' : ℕ) (c : Fin N → K) (c' : Fin N' → K) (a : K), a ≠ 0 ∧ Prim (io.comp (algebraMap V (FractionRing V))) (fun b => c b / a) ∧ Prim (io.comp (algebraMap V (FractionRing V))) (fun b => c' b / a) ∧ (∀ j, io (emb (e j)) = symTup c j) ∧ (∀ x, ∃ b, c' x ^ ((S.r * S.N) ^ 2) = io (emb (S.th b)) ^ ((S.r * S.N) ^ 2)) ∧ ∀ b, ∃ x, c' x ^ ((S.r * S.N) ^ 2) = io (emb (S.th b)) ^ ((S.r * S.N) ^ 2) := by
  first | exact @GlobalTheory.SiegTh.TraitScale.exists_scale | exact GlobalTheory.SiegTh.TraitScale.exists_scale | (intros; apply GlobalTheory.SiegTh.TraitScale.exists_scale <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCommonZeroAmpleSectionsVerticalStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSAmp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_common_zero_ample_sections_vertical : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (P : Pair p), IsAmpleLB P.L.B → ∀ (ℓ d : ℕ) (C : Set X) (e : Fin d → ℕ) (g : Fin d → X.functionField), ℓ.Prime → IsIrreducible C → IsClosed C → C ⊆ fib X ℓ → (d : WithBot ℕ∞) ≤ topologicalKrullDim C → (∀ j, 0 < e j ∧ g j ∈ P.H (e j) 0) → (C \ ⋃ j, NV P (e j) 0 (g j)).Nonempty := by
  first | exact @GlobalTheory.HSAmp.common_zero_of_le_dim | exact GlobalTheory.HSAmp.common_zero_of_le_dim | (intros; apply GlobalTheory.HSAmp.common_zero_of_le_dim <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCoproductThickeningQuotientFreeThickeningStatement
section
open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.CxCoh GlobalTheory.PDA GlobalTheory.PDForm GlobalTheory.SmoothLift
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_coproductThickening_quotient_freeThickening : ∀ (D : Data) (Λ : Lift D) (n : ℕ) (U : AffOp D.X) (T : Thick D.κ D.t), IsLev T.δ (n + 1) → ⊤ ≤ (T.x ≫ D.i) ⁻¹ᵁ U.unop.1 → ∃ (F G : Thick D.κ D.t) (u : T ⟶ F) (q : F ⟶ G) (r : Λ.L.obj U ⟶ G), (KK D.κ D.t).QAt u ∧ IsLev F.δ (n + 1) ∧ Function.Surjective q.φ ∧ (∀ b, q.φ b ∈ G.J → b ∈ F.J) ∧ IsCop (n + 1) (u ≫ q) r := by
  first | exact @GlobalTheory.CopEx.exists_cop | exact GlobalTheory.CopEx.exists_cop | (intros; apply GlobalTheory.CopEx.exists_cop <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFormalChartQuotientByIdealWithPrimePowStatement
section
open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_formalChart_quotient_by_ideal_with_primePow : ∀ (p : ℕ) [Fact p.Prime] (O : Type) [CommRing O] (G : PDivGroup p O) (d : ℕ) (c : QLog.Chart G d), ∀ (I : Ideal O) (m : ℕ), (p : O) ^ m ∈ I → ∃ c' : Katz.Chart (G.baseChange (O ⧸ I)) d, c'.IsLawOf (fun i => map (Ideal.Quotient.mk I) (c.μ i)) ∧ (∀ n f, c'.ev n (map (Ideal.Quotient.mk I) f) = (G.toBase (O ⧸ I)).app n (c.ev n f)) ∧ ∀ n s, c'.ev₂ n (map (Ideal.Quotient.mk I) s) = ((G.toBase (O ⧸ I)).app n).two (c.ev₂ n s) := by
  first | exact @GlobalTheory.QLog.ChartRed.exists_chart | exact GlobalTheory.QLog.ChartRed.exists_chart | (intros; apply GlobalTheory.QLog.ChartRed.exists_chart <;> assumption)
end

