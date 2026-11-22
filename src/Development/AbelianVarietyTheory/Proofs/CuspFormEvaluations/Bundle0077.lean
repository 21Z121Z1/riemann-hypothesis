import Mathlib
import Development.AbelianVarietyTheory.Definitions.ThetaValues.Bundle0003
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.Bundle0011
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.Bundle0007
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle0006
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0006
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0074
import Formalism.LocalToGlobal.ProjectiveLattices.ThShort
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0010
import Formalism.LocalToGlobal.ProjectiveLattices.FrameCharts
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0006
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0005
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0038
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0033
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0043
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ThetaValueWeightTriangularFrame
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0013
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0064
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0038
import Development.AbelianVarietyTheory.Definitions.ThetaValues.Bundle0002
import Development.AbelianVarietyTheory.Definitions.ThetaValues.GamAt
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.AdmissibleModuleIffLatticeQuotients
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle0003
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0075

-- bundled from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ShareRhoROfAnFacts
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.Gaps.EtaleWeightGaps GlobalTheory.Shares

namespace GlobalTheory.Shares

theorem finite_sum_le (D a : ℕ) : {α : Fin D → ℕ | ∑ i, α i ≤ a}.Finite := by
  refine (Set.Finite.pi' (fun _ : Fin D => Set.finite_Iic a)).subset ?_
  intro α hα i
  exact (Finset.single_le_sum (f := α) (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)).trans hα

theorem graded_prod_pow_mul {A ι : Type} [CommRing A] (Q : ℕ → A → Prop) (s : ι → A)
    (h : ∀ n i x, Q n x → Q (n + 1) (s i * x)) (α : ι → ℕ) (F : Finset ι) (n : ℕ) (x : A) (hx : Q n x) :
    Q (n + ∑ i ∈ F, α i) ((∏ i ∈ F, s i ^ α i) * x) := by
  classical
  have hp : ∀ i m n x, Q n x → Q (n + m) (s i ^ m * x) := by
    intro i m
    induction m with
    | zero => intro n x hx; simpa using hx
    | succ m ih => intro n x hx; rw [pow_succ', mul_assoc, ← add_assoc]; exact h _ _ _ (ih n x hx)
  induction F using Finset.induction_on with
  | empty => simpa using hx
  | insert i F hi ih =>
    rw [Finset.sum_insert hi, Finset.prod_insert hi, mul_assoc, add_comm (α i), ← add_assoc]
    exact hp _ _ _ _ ih

theorem addL_zero' {D : D7} {j : ℕ} (u wL : WeightFamilies.Wt D j) : addL u wL 0 = u := by
  cases u
  unfold addL wadd wsmul
  simp

theorem shareRhoR_of_anFacts : ∀ (D : D7) (B : WeightFamilies.Prov D) (P : ModuliIntegralCharts.Prov D) (j : ℕ) (X : PJ D B P j) (ka wL wF : WeightFamilies.Wt D j) (G : GlobalFamilyData X ka wL wF) (R : Rdg X) (t : Idx D j G.N → ℂ) (T : ℕ) (Mg : Submodule B.KO (B.Cusp j ka)) (δ : ℕ) (xs : Fin δ → R.Y), R.Generic t → AnFacts R G.w t ka wF T Mg xs → addL wF wL T = ka → 2 ≤ WeightFamilies.dimY D j → 11 * WeightFamilies.dimY D j ^ 2 ≤ T → LatAt B j ka → ∀ S : Scal B, ShareRhoR G S T (X.rk ka (B.Mlat j ka)) := by
  intro D B P j X ka wL wF G R t T Mg δ xs hgen hA hka hD hT hLat S la
  classical
  obtain ⟨d1, d2, d3, d4, d5, d6, d7, d8⟩ := GlobalTheory.T.genericSections_polynomial_dictionary D B P j X R la G.N wL G.w t
  have hDT : WeightFamilies.dimY D j < T := by nlinarith
  obtain ⟨b1, b2⟩ := GlobalTheory.T.card_exponents_and_choose_ratio_bounds_pair (WeightFamilies.dimY D j) T
  obtain ⟨θ, -, hθ⟩ := GlobalTheory.T.exists_valueBasis_in_spanning_forms D B P j X ka wL wF G.N G.w R t T Mg δ xs hA Set.univ Submodule.span_univ

  have hd : X.rk ka (B.Mlat j ka) = Module.finrank ℂ (R.sp ka Set.univ) := by
    have h1 := (d8 ka ⊤).2
    rw [Submodule.top_coe] at h1
    rw [h1]
    unfold PJ.rk
    have : Submodule.span B.KO (B.Mlat j ka : Set (B.Cusp j ka)) = ⊤ := Submodule.IsLattice.span_eq_top (self := hLat)
    rw [this]
  haveI hfin : FiniteDimensional ℂ (R.sp ka Set.univ) := by
    have h1 := (d8 ka ⊤).1
    rwa [Submodule.top_coe] at h1

  set a := a0 D j T with ha
  have haD : WeightFamilies.dimY D j + a = T := by rw [ha]; unfold a0; omega
  let p1 : Fin (WeightFamilies.dimY D j + 1) → MvPolynomial (Idx D j G.N) X.Forms := fun i =>
    ∑ k, MvPolynomial.X (i, k) * MvPolynomial.C (X.inc wL (G.w k))
  let pm : (Fin (WeightFamilies.dimY D j) → ℕ) → MvPolynomial (Idx D j G.N) X.Forms := fun α => ∏ i, p1 i.succ ^ α i
  have pmK : ∀ α, toRp X la G.N (pm α) = secPow X la G.w α := by
    intro α
    simp only [pm, map_prod, map_pow, secPow]
    exact Finset.prod_congr rfl fun i _ => by rw [(d1 i.succ).1]
  have pmC : ∀ α, R.toFn t (pm α) = R.mon G.w t α := by
    intro α
    simp only [pm, map_prod, map_pow, Rdg.mon]
    exact Finset.prod_congr rfl fun i _ => by rw [(d1 i.succ).2.1]
  have hstep : ∀ n i x, OfWt X (addL wF wL n) x → OfWt X (addL wF wL (n + 1)) (p1 i * x) := by
    intro n i x hx
    rw [← wadd_addL]
    exact d4 _ _ _ _ (d1 i).2.2 hx
  have hpm : ∀ α n x, OfWt X (addL wF wL n) x → OfWt X (addL wF wL (n + ∑ i, α i)) (pm α * x) := fun α n x hx =>
    graded_prod_pow_mul (fun n x => OfWt X (addL wF wL n) x) (fun i : Fin (WeightFamilies.dimY D j) => p1 i.succ)
      (fun n i x hx => hstep n i.succ x hx) α Finset.univ n x hx
  have hp0 : ∀ m n x, OfWt X (addL wF wL n) x → OfWt X (addL wF wL (n + m)) (p1 0 ^ m * x) := fun m n x hx => by
    simpa using graded_prod_pow_mul (fun n x => OfWt X (addL wF wL n) x) (fun _ : Unit => p1 0)
      (fun n _ x hx => hstep n 0 x hx) (fun _ => m) Finset.univ n x hx
  obtain ⟨n, b, hb⟩ := Module.Finite.exists_fin (R := B.KO) (M := B.Cusp j (X.wF0 wL wF))
  haveI : Finite {α : Fin (WeightFamilies.dimY D j) → ℕ // ∑ i, α i = a} :=
    ((finite_sum_le (WeightFamilies.dimY D j) a).subset (t := {α | ∑ i, α i = a}) fun α (h : ∑ i, α i = a) => h.le).to_subtype
  haveI : Finite {α : Fin (WeightFamilies.dimY D j) → ℕ // ∑ i, α i < a} :=
    ((finite_sum_le (WeightFamilies.dimY D j) a).subset (t := {α | ∑ i, α i < a}) fun α (h : ∑ i, α i < a) => h.le).to_subtype
  letI := Fintype.ofFinite {α : Fin (WeightFamilies.dimY D j) → ℕ // ∑ i, α i = a}
  letI := Fintype.ofFinite {α : Fin (WeightFamilies.dimY D j) → ℕ // ∑ i, α i < a}
  let q : {α : Fin (WeightFamilies.dimY D j) → ℕ // ∑ i, α i = a} × Fin n → MvPolynomial (Idx D j G.N) X.Forms := fun p =>
    pm p.1.1 * MvPolynomial.C (X.inc (X.wF0 wL wF) (b p.2))
  have hq : ∀ p, OfWt X ka (q p) := by
    intro p
    have := hpm p.1.1 (WeightFamilies.dimY D j) _ (d3 (X.wF0 wL wF) (b p.2))
    rwa [p.1.2, haD, hka] at this
  have htr := (GlobalTheory.T.indep_span_rank_transfer_largeField_complex D B P j X R la G.N t hgen ka _ q hq).2.2

  have hK : Submodule.span (Kp X la G.N) (zAll G la S T) ≤
      Submodule.span (Kp X la G.N) (Set.range fun p => toRp X la G.N (q p)) := by
    rw [Submodule.span_le]
    rintro _ ⟨α, F, hα, -, rfl⟩
    have hF := emb_mem_Vw X la G.N _ F
    rw [Vw_eq_span_image X la G.N _ hb] at hF
    have := Submodule.mem_map_of_mem (f := LinearMap.mulLeft (Kp X la G.N) (secPow X la G.w α)) hF
    rw [Submodule.map_span] at this
    refine Submodule.span_mono ?_ this
    rintro _ ⟨_, ⟨_, ⟨k, rfl⟩, rfl⟩, rfl⟩
    refine ⟨(⟨α, hα⟩, k), ?_⟩
    simp only [q, map_mul, pmK, (d2 _).1, LinearMap.mulLeft_apply]

  have hC : Submodule.span ℂ (Set.range fun p => R.toFn t (q p)) ≤ R.deep G.w t (X.wF0 wL wF) a := by
    refine Submodule.span_mono ?_
    rintro _ ⟨p, rfl⟩
    refine ⟨p.1.1, R.ev (X.inc _ (b p.2)), p.1.2, Submodule.subset_span ⟨b p.2, trivial, rfl⟩, ?_⟩
    simp only [q, map_mul, pmC, (d2 _).2]
  have hCk : Submodule.span ℂ (Set.range fun p => R.toFn t (q p)) ≤ R.sp ka Set.univ := by
    rw [Submodule.span_le]
    rintro _ ⟨p, rfl⟩
    exact (d5 ka _ (hq p)).2
  obtain ⟨hli, hdis⟩ := hA.indep δ (fun i => R.ev (X.inc wF (θ i)))
    (fun i => Submodule.subset_span ⟨θ i, trivial, rfl⟩) hθ
  rw [← ha] at hli hdis
  have hLk : Submodule.span ℂ (Set.range (R.lead G.w t T a fun i => R.ev (X.inc wF (θ i)))) ≤ R.sp ka Set.univ := by
    rw [Submodule.span_le]
    rintro _ ⟨p, rfl⟩
    have h0 : OfWt X (addL wF wL 0) (MvPolynomial.C (X.inc wF (θ p.2)) : MvPolynomial (Idx D j G.N) X.Forms) := by
      rw [addL_zero']; exact d3 _ _
    have h1 := hpm p.1.1 _ _ (hp0 (T - ∑ i, p.1.1 i) _ _ h0)
    have h2 := p.1.2
    rw [show 0 + (T - ∑ i, p.1.1 i) + ∑ i, p.1.1 i = T by omega, hka] at h1
    have h3 := (d5 ka _ h1).2
    rw [map_mul, map_mul, map_pow, pmC, (d1 0).2.1, (d2 _).2, ← mul_assoc] at h3
    exact h3
  have hrk := finrank_span_eq_card hli
  rw [Fintype.card_prod, Fintype.card_fin, ← Nat.card_eq_fintype_card] at hrk
  have hcard : Nat.card {α : Fin (WeightFamilies.dimY D j) → ℕ // ∑ i, α i < a} = (T - 1).choose (WeightFamilies.dimY D j) :=
    b1 (by omega) hDT
  rw [hcard] at hrk
  haveI := Submodule.finiteDimensional_of_le hLk
  haveI := Submodule.finiteDimensional_of_le hCk
  have hsum := Submodule.finrank_sup_add_finrank_inf_eq
    (Submodule.span ℂ (Set.range (R.lead G.w t T a fun i => R.ev (X.inc wF (θ i)))))
    (Submodule.span ℂ (Set.range fun p => R.toFn t (q p)))
  rw [(hdis.mono_right hC).eq_bot, finrank_bot, add_zero, hrk] at hsum
  have hle := Submodule.finrank_mono (sup_le hLk hCk)
  haveI : FiniteDimensional (Kp X la G.N)
      (Submodule.span (Kp X la G.N) (Set.range fun p => toRp X la G.N (q p))) :=
    FiniteDimensional.span_of_finite _ (Set.finite_range _)
  have hKle := Submodule.finrank_mono hK
  rw [hd]
  refine (b2 δ _ _ hD hT hA.upper).1 ?_
  rw [mul_comm δ]
  omega

end GlobalTheory.Shares
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ShortValTotOfPinned
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ShortDescent

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}

def oneSim (D : Datum H) : Sim D where
  f _ := LinearMap.id
  ν _ := 1
  tower _ _ _ _ _ := ⟨0, by simp⟩
  inv _ _ := ⟨LinearMap.id, fun _ => ⟨⟨0, by simp⟩, ⟨0, by simp⟩⟩⟩
  mult _ _ _ _ := by simp

variable {Xo : Moduli Dw l} {c : Coeff l} {n : ℕ}

theorem evR_eq_of_point_eq (d : DeltaDat Xo c n) {ψ : (LaI Xo c d ≃ₗ[𝓞 E] LaI Xo c d) →* c.Fˣ} (hψ : d.PsiTie ψ)
    {k : Type} [Field k] [IsAlgClosed k] [Algebra d.c₂.F k] (y y' : FrPt d.Xo₂ d.c₂ k) (h : y'.x = y.x) :
    evR d.Xo₂ d.c₂ d.cδ y' = evR d.Xo₂ d.c₂ d.cδ y := by
  have e := hψ 1 (oneSim Dw) (Iso.refl _)
    ⟨by simp [oneSim], fun a => by simp [oneSim], fun a => ⟨0, by simp [oneSim]⟩⟩
    (fun a => ⟨0, by simp [oneSim]⟩)
    ⟨Category.id_comp _, GlobalTheory.LevelTwist.sabMapId _,
      fun _ => (Category.comp_id _).trans (Category.id_comp _).symm,
      fun _ => (Category.comp_id _).trans (Category.id_comp _).symm⟩
    (fun _ => rfl) k y y' (h.trans (Category.comp_id _).symm)
  simpa using e

theorem map_wchar {J : Type} [Fintype J] {K S T : Type} [Field K] [CommRing S] [Algebra K S] [CommRing T] [Algebra K T]
    (χ : S →ₐ[K] T) (e : J → ℕ) (t : J → Sˣ) :
    χ (wchar e t) = wchar e (fun i => Units.map (χ : S →* T) (t i)) := by
  simp [wchar, map_prod, map_pow]

end GlobalTheory.ShortDescent

namespace GlobalTheory

open ShortDescent in

theorem shortValTot_of_pinned : Laws → ChartIndepSt2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (n : ℕ) (d : DeltaDat Xo c n), @ToroidalLevelCompatibility E _ _ _ H Dw → EvalWD (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) → AllTest Xo c → EvalWD (K := d.c₂.F) (fun S _ _ => FrPt d.Xo₂ d.c₂ S) (fun φ y z => FrMap φ y z) → AllTest d.Xo₂ d.c₂ → d.IsLev → d.l₂.A = l.A → (∃ _ : StarRing (𝓞 E), IsNab d.Xo₂ d.c₂ d.nab₂) → (Dw.p + Dw.q ≤ n → ∃ ph ψ x₀, d.PhiPin ph ψ x₀ ∧ d.PsiTie ψ) → ∀ (nab : NabV Xo c) (bad nV : ℕ) (a : (E →+* ℂ) × ℕ → ℕ), ShortValTot Xo c nab bad nV a n d := by
  intro hL hC E _ _ _ H Dw l Xo c n d hN _ hAll hW₂ hAll₂ hLev hA hnab hpin nab bad nV a Λ N x0 P hU _ hT hO hX hP
  obtain ⟨_, hnab⟩ := hnab
  obtain ⟨hle, hmap⟩ := GlobalTheory.admissible_columns_le_and_harmonic_map_cover E H Dw l Xo c n d
  have hpin' := hpin (hle _ _ hX)
  have hP₂ := hmap a P hP.1
  obtain ⟨hex, -⟩ := GlobalTheory.T.shortThetaValue_existsUnique_natural_of_laws hL hC E H Dw d.l₂ d.Xo₂ d.c₂ d.nab₂ hnab n Λ N hU hT hO a _ hP₂ (d.w x0)
    (d.eF (betaH (Dw := Dw) c Λ))
  have hd := GlobalTheory.T.evaluation_lemma_for_nabla_levels hL hC E H Dw l Xo c n d hW₂ hAll₂ hN hLev hA hnab hpin' Λ N hU hT hO a _ hP₂ x0
    (d.eF (betaH (Dw := Dw) c Λ))
  obtain ⟨hlift, -, hbor⟩ := GlobalTheory.T.framedPoints_lift_to_levelCover hL E H Dw l Xo c n d
  obtain ⟨_, ψ, _, -, hψ⟩ := hpin'
  refine ⟨hex, fun p y => (hd p y).exists.choose, ⟨fun p q φ y z h => ?_, fun p t y y' h => ?_⟩, ?_⟩
  · refine (hd q z).unique (hd q z).exists.choose_spec ?_
    intro k _ _ _ _ hk χ w w₂ hw ho v hv
    exact (hd p y).exists.choose_spec k hk (χ.comp φ) w w₂ (GlobalTheory.FramedBaseChange.trans φ χ h hw) ho v hv
  · refine (hd p y').unique (hd p y').exists.choose_spec ?_
    intro k _ _ _ _ hk χ w' w₂' hw' ho' v' hv'
    obtain ⟨w, hw⟩ := GlobalTheory.FramedBaseChange.exists_frMap hL E H Dw l Xo c p.R k χ y
    have hb := frBorBC _ _ χ t y y' w w' h hw hw'
    obtain ⟨w₂, hx₂, ho⟩ := hlift k hk w w₂'.x (ho'.1.trans hb.1) w₂'.x_over
    have hb₂ := hbor k hk _ w w' w₂ w₂' ho ho' hx₂.symm hb
    obtain ⟨v, hv, -⟩ := hex k w₂
    have hv₂ := (GlobalTheory.thetaValue_weight hL hC E H Dw d.l₂ d.Xo₂ d.c₂ d.nab₂ hnab k w₂ w₂' _ hb₂ n a _).2 hP₂
      _ Λ _ N v hv
    have e := (hd p y).exists.choose_spec k hk χ w w₂ hw ho v hv
    rw [(hex k w₂').unique hv' hv₂, map_mul, map_wchar, evR_eq_of_point_eq d hψ w₂ w₂' hx₂.symm]
    refine (congrArg (_ * ·) e).trans ?_
    ring
  · intro k _ _ _ _ hk y y₂ ho
    obtain ⟨v, hv, -⟩ := hex k y₂
    refine ⟨v, hv, ?_⟩
    have hy := hAll k y
    unfold evR evalAt
    rw [dif_pos hy]
    exact (hd _ _).exists.choose_spec k hk _ y y₂ hy.choose_spec.choose_spec.choose_spec ho v hv

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ThetaLatticeWeightScalarNeZeroAndLogBounds
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.DIV.Cons Formalism.MainNotions.Gaps Formalism.L2.Pj GlobalTheory.RunIn

namespace GlobalTheory.RunIn

private theorem log_norm_sOf_eq_DF_log_add_log_pPow (D : D7) (B : WeightFamilies.Prov D) (hinj : Function.Injective D.what₂.OtoLL) (EX : ErrX D)
    (j : ℕ) (w : WeightFamilies.Wt D j) (σ : B.KO →+* ℂ) :
    Real.log ‖σ (sOf B hinj EX w : B.KO)‖ =
      (WeightAlgebra.DF w : ℝ) / 2 * Real.log ((D.host.g 0 : ℝ) * (D.host.g 1 : ℝ)) +
        Real.log (pPow D (c2 D w) (Formalism.MainNotions.DIV.Cons.cHalf w) (Formalism.MainNotions.DIV.Cons.cHalf w) : ℝ) := by
  obtain ⟨hnn, hlog⟩ := GlobalTheory.T.log_norm_normaliser_eq_half_degree_log D B hinj EX j w σ
  have hp := ((GlobalTheory.T.ramifiedPrimePowers_size_bounds D j w).2.2.2.2.2 (c2 D w) (Formalism.MainNotions.DIV.Cons.cHalf w) (Formalism.MainNotions.DIV.Cons.cHalf w)).1
  have hσ : σ (sOf B hinj EX w : B.KO) = σ (nnW B hinj EX w : B.KO) *
      (pPow D (c2 D w) (Formalism.MainNotions.DIV.Cons.cHalf w) (Formalism.MainNotions.DIV.Cons.cHalf w) : ℂ) := by
    unfold sOf
    push_cast
    rw [map_mul, map_natCast]
  have hne : σ (nnW B hinj EX w : B.KO) ≠ 0 := by
    rw [map_ne_zero]
    exact_mod_cast hnn
  have hpne : ((pPow D (c2 D w) (Formalism.MainNotions.DIV.Cons.cHalf w) (Formalism.MainNotions.DIV.Cons.cHalf w) : ℕ) : ℝ) ≠ 0 := by
    have : 0 < pPow D (c2 D w) (Formalism.MainNotions.DIV.Cons.cHalf w) (Formalism.MainNotions.DIV.Cons.cHalf w) := hp
    positivity
  rw [hσ, norm_mul, Complex.norm_natCast, Real.log_mul (norm_ne_zero_iff.mpr hne) hpne, hlog]

theorem sOf_ne_zero_and_log_bounds : ∀ (D : D7) (B : WeightFamilies.Prov D) (hinj : Function.Injective D.what₂.OtoLL) (EX : ErrX D) (j : ℕ) (w : WeightFamilies.Wt D j), sOf B hinj EX w ≠ 0 ∧ ∀ σ : B.KO →+* ℂ, 0 ≤ Real.log ‖σ (sOf B hinj EX w : B.KO)‖ ∧ (WeightAlgebra.DF w : ℝ) / 2 * Real.log (qq D) ≤ Real.log ‖σ (sOf B hinj EX w : B.KO)‖ ∧ (WeightAlgebra.DF w : ℝ) / 2 * Real.log ((D.host.g 0 : ℝ) * (D.host.g 1 : ℝ)) ≤ Real.log ‖σ (sOf B hinj EX w : B.KO)‖ ∧ Real.log ‖σ (sOf B hinj EX w : B.KO)‖ ≤ lamStar D * w.size := by
  intro D B hinj EX j w
  obtain ⟨_, _, hB0, hA0, hP, hpp⟩ := GlobalTheory.T.ramifiedPrimePowers_size_bounds D j w
  obtain ⟨hp1, hplog⟩ := hpp (c2 D w) (Formalism.MainNotions.DIV.Cons.cHalf w) (Formalism.MainNotions.DIV.Cons.cHalf w)
  have hlp0 : 0 ≤ Real.log (pPow D (c2 D w) (Formalism.MainNotions.DIV.Cons.cHalf w) (Formalism.MainNotions.DIV.Cons.cHalf w) : ℝ) :=
    Real.log_nonneg (by exact_mod_cast hp1)
  have hlpB : Real.log (pPow D (c2 D w) (Formalism.MainNotions.DIV.Cons.cHalf w) (Formalism.MainNotions.DIV.Cons.cHalf w) : ℝ) ≤
      ((WeightAlgebra.DF w : ℝ) + 1) * Real.log (4 * ((D.R.f : ℝ) / 2) ^ 2 * D.host.q * D.host.d) := by
    rw [hplog]; exact hP
  have hDF : (0 : ℝ) ≤ WeightAlgebra.DF w := Nat.cast_nonneg _

  have hsz : (WeightAlgebra.DF w : ℝ) + 1 ≤ w.size := by
    have key : w.size = (WeightAlgebra.DF w : ℝ) +
        (D.R.f : ℝ) * ((max (D.R.sigW j).2 1 : ℕ) : ℝ) * (D.R.r : ℝ) * (w.n : ℝ) + 1 := by
      unfold WeightFamilies.Wt.size WeightAlgebra.DF WeightAlgebra.degP
      push_cast
      ring
    have : (0 : ℝ) ≤ (D.R.f : ℝ) * ((max (D.R.sigW j).2 1 : ℕ) : ℝ) * (D.R.r : ℝ) * (w.n : ℝ) := by
      positivity
    linarith

  have hqq : Real.log (qq D : ℝ) ≤ Real.log ((D.host.g 0 : ℝ) * (D.host.g 1 : ℝ)) := by
    rcases Nat.eq_zero_or_pos (qq D) with h | h
    · rw [h, Nat.cast_zero, Real.log_zero]; exact hA0
    · have h0 : qq D ≤ D.host.g 0 := min_le_left _ _
      have h1 : qq D ≤ D.host.g 1 := min_le_right _ _
      have hle : qq D ≤ D.host.g 0 * D.host.g 1 :=
        h0.trans (Nat.le_mul_of_pos_right _ (lt_of_lt_of_le h h1))
      have hcast : (qq D : ℝ) ≤ (D.host.g 0 : ℝ) * (D.host.g 1 : ℝ) := by exact_mod_cast hle
      exact Real.log_le_log (by exact_mod_cast h) hcast
  refine ⟨?_, fun σ => ?_⟩
  · unfold sOf
    refine mul_ne_zero ?_ ?_
    · obtain ⟨σ⟩ : Nonempty (B.KO →+* ℂ) := inferInstance
      exact (GlobalTheory.T.log_norm_normaliser_eq_half_degree_log D B hinj EX j w σ).1
    · have : pPow D (c2 D w) (Formalism.MainNotions.DIV.Cons.cHalf w) (Formalism.MainNotions.DIV.Cons.cHalf w) ≠ 0 := by omega
      exact_mod_cast this
  · rw [log_norm_sOf_eq_DF_log_add_log_pPow D B hinj EX j w σ]
    have hA : (WeightAlgebra.DF w : ℝ) / 2 * Real.log (qq D : ℝ) ≤
        (WeightAlgebra.DF w : ℝ) / 2 * Real.log ((D.host.g 0 : ℝ) * (D.host.g 1 : ℝ)) :=
      mul_le_mul_of_nonneg_left hqq (by positivity)
    have hA1 : 0 ≤ (WeightAlgebra.DF w : ℝ) / 2 * Real.log ((D.host.g 0 : ℝ) * (D.host.g 1 : ℝ)) := by positivity
    have hL : lamStar D = Real.log ((D.host.g 0 : ℝ) * (D.host.g 1 : ℝ)) +
        Real.log (4 * ((D.R.f : ℝ) / 2) ^ 2 * D.host.q * D.host.d) := rfl
    refine ⟨by linarith, by linarith, by linarith, ?_⟩
    calc (WeightAlgebra.DF w : ℝ) / 2 * Real.log ((D.host.g 0 : ℝ) * (D.host.g 1 : ℝ)) +
          Real.log (pPow D (c2 D w) (Formalism.MainNotions.DIV.Cons.cHalf w) (Formalism.MainNotions.DIV.Cons.cHalf w) : ℝ)
        ≤ ((WeightAlgebra.DF w : ℝ) + 1) * (Real.log ((D.host.g 0 : ℝ) * (D.host.g 1 : ℝ)) +
            Real.log (4 * ((D.R.f : ℝ) / 2) ^ 2 * D.host.q * D.host.d)) := by
          nlinarith [mul_nonneg hDF hA0]
      _ ≤ w.size * (Real.log ((D.host.g 0 : ℝ) * (D.host.g 1 : ℝ)) +
            Real.log (4 * ((D.R.f : ℝ) / 2) ^ 2 * D.host.q * D.host.d)) :=
          mul_le_mul_of_nonneg_right hsz (by linarith)
      _ = lamStar D * w.size := by rw [hL]; ring

end GlobalTheory.RunIn
end

