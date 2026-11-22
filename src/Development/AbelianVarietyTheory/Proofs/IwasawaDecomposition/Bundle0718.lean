import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0045
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0031
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsRhoPtOfSplitting
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsComp
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.WeakCharInertPartRealAdelicDataTransport
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0041
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0606
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0673
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0664
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0707
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0675
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0699
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0701
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MonoSpMapRingOfIntegersAlt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsEqAddOfRedVEq
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0655
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0705
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0700
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0692
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NonnegSumSmulIntBilinFormToRealMemPsdCone
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FirstIndexEqOfUnfolded
import Formalism.DegreeFormula.Statement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0672

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DomCongrSymmEq
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

open GlobalTheory.Mem.Top.TypesTrue GlobalTheory.Mem.R3.Tr

namespace GlobalTheory.Mem.R3.Rw.CopySide

theorem mem_center_map {G G' : Type} [Monoid G] [Monoid G'] (φ : MonoidAlgebra ℂ G ≃ₐ[ℂ] MonoidAlgebra ℂ G')
    {a : MonoidAlgebra ℂ G} (ha : a ∈ Subalgebra.center ℂ (MonoidAlgebra ℂ G)) :
    φ a ∈ Subalgebra.center ℂ (MonoidAlgebra ℂ G') := by
  rw [Subalgebra.mem_center_iff] at ha ⊢
  intro b
  obtain ⟨b, rfl⟩ := φ.surjective b
  rw [← map_mul, ← map_mul, ha b]

def cenMap {G H : Type} [Group G] [Group H] (e : G ≃* H) :
    Subalgebra.center ℂ (MonoidAlgebra ℂ G) →ₐ[ℂ] Subalgebra.center ℂ (MonoidAlgebra ℂ H) :=
  ((MonoidAlgebra.domCongr ℂ ℂ e).toAlgHom.comp (Subalgebra.center ℂ (MonoidAlgebra ℂ G)).val).codRestrict _ fun z =>
    mem_center_map (MonoidAlgebra.domCongr ℂ ℂ e) z.2

theorem cenMap_coeff {G H : Type} [Group G] [Group H] (e : G ≃* H) (z : Subalgebra.center ℂ (MonoidAlgebra ℂ G)) (h : H) :
    ((cenMap e z : Subalgebra.center ℂ (MonoidAlgebra ℂ H)) : MonoidAlgebra ℂ H).coeff h =
      (z : MonoidAlgebra ℂ G).coeff (e.symm h) := by
  show (MonoidAlgebra.domCongr ℂ ℂ e (z : MonoidAlgebra ℂ G)).coeff h = _
  rw [MonoidAlgebra.coeff_domCongr]

theorem domCongr_symm_eq {G H : Type} [Group G] [Group H] (e : G ≃* H) (a : MonoidAlgebra ℂ H) (b : MonoidAlgebra ℂ G)
    (h : ∀ g, a.coeff (e g) = b.coeff g) : MonoidAlgebra.domCongr ℂ ℂ e.symm a = b := by
  apply MonoidAlgebra.coeff_injective
  refine Finsupp.ext fun g => ?_
  rw [MonoidAlgebra.coeff_domCongr, MulEquiv.symm_symm]
  exact h g

theorem domCongr_eq {G H : Type} [Group G] [Group H] (e : G ≃* H) (a : MonoidAlgebra ℂ H) (b : MonoidAlgebra ℂ G)
    (h : ∀ g, a.coeff (e g) = b.coeff g) : MonoidAlgebra.domCongr ℂ ℂ e b = a := by
  apply MonoidAlgebra.coeff_injective
  refine Finsupp.ext fun g => ?_
  rw [MonoidAlgebra.coeff_domCongr, ← h, MulEquiv.apply_symm_apply]

open Classical in

theorem tie_tr {G H E : Type} [Group G] [Group H] [AddCommGroup E] [Module ℂ E] (e : G ≃* H)
    (cen : Subalgebra.center ℂ (MonoidAlgebra ℂ G) →ₐ[ℂ] Module.End ℂ E) (a : MonoidAlgebra ℂ G) (b : MonoidAlgebra ℂ H)
    (h : ∀ g, b.coeff (e g) = a.coeff g) :
    (if ha : a ∈ Subalgebra.center ℂ (MonoidAlgebra ℂ G) then cen ⟨a, ha⟩ else 0) =
      (if hb : b ∈ Subalgebra.center ℂ (MonoidAlgebra ℂ H) then (cen.comp (cenMap e.symm)) ⟨b, hb⟩ else 0) := by
  have h1 := domCongr_symm_eq e b a h
  have h2 := domCongr_eq e b a h
  by_cases hb : b ∈ Subalgebra.center ℂ (MonoidAlgebra ℂ H)
  · have ha : a ∈ Subalgebra.center ℂ (MonoidAlgebra ℂ G) := by
      rw [← h1]; exact mem_center_map _ hb
    rw [dif_pos ha, dif_pos hb, AlgHom.comp_apply]
    congr 1
    exact Subtype.ext h1.symm
  · have ha : a ∉ Subalgebra.center ℂ (MonoidAlgebra ℂ G) := by
      intro ha; apply hb; rw [← h2]; exact mem_center_map _ ha
    rw [dif_neg ha, dif_neg hb]

set_option maxHeartbeats 1000000 in

theorem side_copy : ∀ {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T} {P : Pre2 K w} (x : St P) (N : NStage B w.C (P.q.W x.o.η x.o.hη)), GrpTrue N f → ∃ (sg : SameGrp (B := B) (C := w.C) x.o.Z (RowPk.Over.Z (⟨x.o.η, x.o.hη, x.o.V, x.o.S, N, x.o.G⟩ : P.q.Over))) (s : Side0 (⟨x.o.η, x.o.hη, x.o.V, x.o.S, N, x.o.G⟩ : P.q.Over)), s.RR = x.s.RR ∧ HEq s.jEE x.s.jEE ∧ ∀ μ (c : Subalgebra.center ℂ (MonoidAlgebra ℂ (G0g (w.D (RowPk.Over.Z (⟨x.o.η, x.o.hη, x.o.V, x.o.S, N, x.o.G⟩ : P.q.Over))).nd))) (c0 : Subalgebra.center ℂ (MonoidAlgebra ℂ (G0g (w.D x.o.Z).nd))), (∀ g, (c0 : MonoidAlgebra ℂ (G0g (w.D x.o.Z).nd)).coeff g = (c : MonoidAlgebra ℂ (G0g (w.D (RowPk.Over.Z (⟨x.o.η, x.o.hη, x.o.V, x.o.S, N, x.o.G⟩ : P.q.Over))).nd)).coeff (sg.iso g)) → s.cen μ c = x.s.cen μ c0 := by
  intro K B f T w P x N hN
  let sg : SameGrp (B := B) (C := w.C) x.o.Z (RowPk.Over.Z (⟨x.o.η, x.o.hη, x.o.V, x.o.S, N, x.o.G⟩ : P.q.Over)) :=
    { e := (by with_unfolding_all exact ((plEquiv x.o.N.naut N.naut) :))
      pl := (by with_unfolding_all exact ((TypesTrue.plGw_plEquiv x.fits.grp hN) :))
      e0 := (by with_unfolding_all exact ((x.fits.grp.typeIdempotent_coeff_across_layers hN) :)) }
  let φ := cenMap sg.iso.symm
  have hφ : ∀ c g, (φ c).val.coeff g = c.val.coeff (sg.iso g) := by
    intro c g
    rw [cenMap_coeff, MulEquiv.symm_symm]

  have hstd : ∀ eR, StdIso (w.st (RowPk.Over.Z (⟨x.o.η, x.o.hη, x.o.V, x.o.S, N, x.o.G⟩ : P.q.Over))) w.px eR →
      StdIso (w.st x.o.Z) w.px (eR.trans sg.iso.symm) := by
    rintro eR ⟨plg1, iso1, hpl1, hact1⟩
    refine ⟨(Equiv.sigmaCongrRight fun k => sg.e k).trans plg1, fun kv => iso1 ⟨kv.1, sg.e kv.1 kv.2⟩, fun kv => ?_, fun g kv => ?_⟩
    · exact (hpl1 _).trans (sg.pl kv.1 kv.2)
    · exact hact1 g _
  refine ⟨sg, { cen := fun μ => (x.s.cen μ).comp φ
                tie := fun μ => (x.s.tie μ).trans ((by with_unfolding_all exact ((tie_tr sg.iso (x.s.cen μ) _ _ sg.e0) :)))
                is := fun eR h μ c c' hc xx => ?_
                RR := x.s.RR
                frames := x.s.frames
                jEE := x.s.jEE
                basis := x.s.basis
                norm := x.s.norm }, rfl, HEq.rfl, fun μ c c0 hc => ?_⟩
  · show x.s.cen μ (φ c) xx = _
    refine x.s.is (eR.trans sg.iso.symm) (hstd eR h) μ (φ c) c' (fun g => ?_) xx
    exact (hc g).trans ((congrArg c.val.coeff (sg.iso.apply_symm_apply (eR g))).symm.trans (hφ c _).symm)
  · show x.s.cen μ (φ c) = _
    congr 1
    apply Subtype.ext
    apply MonoidAlgebra.coeff_injective
    refine Finsupp.ext fun g => ?_
    exact (hφ c g).trans (hc g).symm

end GlobalTheory.Mem.R3.Rw.CopySide

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EigenframeGramNearPoint
section
open AlgebraicGeometry CategoryTheory Limits NumberField Matrix
open ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory GlobalTheory.CxPts GlobalTheory.Toroidal GlobalTheory.LieMet GlobalTheory.GradedNorm GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.ShFam GlobalTheory.ShFam.Pad
open GlobalTheory.ArcQ
open scoped ContDiff

set_option autoImplicit false

theorem GlobalTheory.ShFam.ToroidalCompactificationData.hodge_gram_smooth_near : ∀ (D : D7) (A : Amb D) (N j : ℕ) (S : Sig A N j) (κ : Lv A) (s : FinalTheorems S κ) (x : ToroidalCompactificationData s) (σ : κ.c.F →+* ℂ), Formalism.L2.PjFree.GoodEmb κ.c σ → ∀ (V : (gen s.T.Z).affineOpens) (φ : κ.c.F →+* Γ(gen s.T.Z, V.1)) (F : EigFrame s.T.Z φ (LogKS.chart V ≫ genι s.T.Z)) (τ : D.host.E →+* ℂ) (a b : Fin (S.Dw.mult τ)), LogKS.chart V ≫ genStr s.T.Z = spMap φ → ∀ y₀ : CxPts (genStr s.T.Z) σ, ¬ LiesIn y₀ (genBd s.T.Z) → y₀ ∈ ptsIn (genStr s.T.Z) σ V.1 → ∃ (T : Set (CxPts (genStr s.T.Z) σ)) (g : CxPts (genStr s.T.Z) σ → ℂ), IsOpen T ∧ y₀ ∈ T ∧ (manifold s.T.Z σ).SmoothOn T (fun y => (g y).re) ∧ (manifold s.T.Z σ).SmoothOn T (fun y => (g y).im) ∧ ∀ y ∈ T, ∀ (hy : y ∈ ptsIn (genStr s.T.Z) σ V.1) (f : EigFrame s.T.Z σ (y.1 ≫ genι s.T.Z)), F.IsMap (evHom hy) f → (x.hodge σ).gram y f τ a b = g y := by
  intro D A N j S κ s x σ hσ V φ F τ a b hstr y₀ hbd hV
  obtain ⟨ch, hch⟩ := AlgChart.exists_mem_source (p := genStr s.T.Z) (σ := σ) (D := S.Dw.dim) y₀
  obtain ⟨W⟩ := nonempty_unfWit_of_isUnf _ _ _ _ _ _ σ _ _ (s.unf σ hσ).1
  obtain ⟨f₀, -⟩ := (FinalTheorems.exists_isHodgeFrame_iff (s := s) (y := y₀)).2 hbd
  obtain ⟨q₀, hq₀, -⟩ := GlobalTheory.T.exists_framedComplexPoint_of_eigenFrame_off_boundary _ _ _ _ _ _ _ _ s.T.Z σ y₀ hbd f₀
  obtain ⟨i, B, P, hB, hb₀, hBt, hPer, hPhol, hPu⟩ :=
    GlobalTheory.ShFam.chart_lift_periods _ _ _ _ _ _ _ _ s.T.Z σ S.Dw.dim W.g _ W.F ch q₀ (hq₀ ▸ hch)
  rw [hq₀] at hb₀
  obtain ⟨Hm, hHm, hHs⟩ := GlobalTheory.T.period_family_chart_domain _ _ _ _ _ _ σ W.g _ W.F i S.Dw.dim B P hB hPer hPhol
  have hmono : Mono (genι s.T.Z) := by
    have : Epi (CommRingCat.ofHom (algebraMap (𝓞 κ.c.F) κ.c.F)) := IsLocalization.epi (nonZeroDivisors (𝓞 κ.c.F)) κ.c.F
    have : Mono (spMap (algebraMap (𝓞 κ.c.F) κ.c.F)) := Scheme.Spec.map_mono (CommRingCat.ofHom _).op
    infer_instance
  obtain ⟨z, hz, hzl⟩ := GlobalTheory.T.period_family_chart_holomorphic _ _ _ _ _ _ _ _ s.T.Z σ S.Dw.dim W.g _ W.F ch i B P hB hBt hPer hPhol hPu hmono V φ F hstr
  set B' : Set (ReciprocityTheory.L2DbarEstimates.V S.Dw.dim) := {c ∈ B | ch.e.symm c ∈ ptsIn (genStr s.T.Z) σ V.1 ∧
    ¬ LiesIn (ch.e.symm c) (genBd s.T.Z)} with hB'
  have hB'o : IsOpen B' := by
    have h1 := ch.e.continuousOn_symm.isOpen_inter_preimage ch.e.open_target
      ((isOpen_ptsIn (p := genStr s.T.Z) (σ := σ) V.1).inter (isOpen_not_liesIn (p := genStr s.T.Z) (σ := σ) (genBd s.T.Z)))
    have e : B' = B ∩ (ch.e.target ∩ ch.e.symm ⁻¹' (ptsIn (genStr s.T.Z) σ V.1 ∩ {y | ¬ LiesIn y (genBd s.T.Z)})) := by
      ext c
      constructor
      · rintro ⟨h1, h2, h3⟩
        exact ⟨h1, hBt h1, h2, h3⟩
      · rintro ⟨h1, -, h2, h3⟩
        exact ⟨h1, h2, h3⟩
    rw [e]
    exact hB.inter h1
  have hz' : ∀ τ k p, ContDiffOn ℝ ∞ (fun c => z c τ k p) B' := fun τ k p =>
    GlobalTheory.ChartGlue.contDiffOn_real hB'o ((differentiableOn_pi.1 (hz τ k)) p)
  let G : ReciprocityTheory.L2DbarEstimates.V S.Dw.dim → ℂ := fun c => (Real.pi : ℂ) * hermForm (Hm c) (z c τ b) (z c τ a)
  have hG : ContDiffOn ℝ ∞ G B' := by
    have hc : ∀ p, ContDiffOn ℝ ∞ (fun c => star (z c τ a p)) B' := fun p =>
      Complex.conjCLE.contDiff.comp_contDiffOn (hz' τ a p)
    have e : G = fun c => (Real.pi : ℂ) * ∑ p, z c τ b p * ∑ q, Hm c p q * star (z c τ a q) := by
      funext c
      simp only [G, hermForm, dotProduct, Matrix.mulVec, Pi.star_apply]
    rw [e]
    exact contDiffOn_const.mul (ContDiffOn.sum fun p _ => (hz' τ b p).mul
      (ContDiffOn.sum fun q _ => ((hHs p q).mono fun c hc => hc.1).mul (hc q)))
  refine ⟨ch.e.source ∩ ch.e ⁻¹' B', fun y => G (ch.e y), ch.e.isOpen_inter_preimage hB'o,
    ⟨hch, hb₀, by rw [ch.e.left_inv hch]; exact hV, by rw [ch.e.left_inv hch]; exact hbd⟩, ?_, ?_, ?_⟩
  · intro c'
    have ht : ContDiffOn ℝ ∞ (ch.e ∘ c'.e.symm) (c'.e.target ∩ c'.e.symm ⁻¹' ch.e.source) :=
      (contDiffOn_piLp 2).2 fun a => GlobalTheory.ChartGlue.contDiffOn_real (GlobalTheory.ChartGlue.isOpen_over c'.e ch.e.open_source)
        (differentiableOn_euclidean.1 (AlgChart.holo_trans c' ch) a)
    exact (Complex.reCLM.contDiff.comp_contDiffOn hG).comp (ht.mono fun v hv => ⟨hv.1, hv.2.1⟩) fun v hv => hv.2.2
  · intro c'
    have ht : ContDiffOn ℝ ∞ (ch.e ∘ c'.e.symm) (c'.e.target ∩ c'.e.symm ⁻¹' ch.e.source) :=
      (contDiffOn_piLp 2).2 fun a => GlobalTheory.ChartGlue.contDiffOn_real (GlobalTheory.ChartGlue.isOpen_over c'.e ch.e.open_source)
        (differentiableOn_euclidean.1 (AlgChart.holo_trans c' ch) a)
    exact (Complex.imCLM.contDiff.comp_contDiffOn hG).comp (ht.mono fun v hv => ⟨hv.1, hv.2.1⟩) fun v hv => hv.2.2
  · rintro y ⟨hys, hyB⟩ hy f hf
    show _ = G (ch.e y)
    obtain ⟨c0, hc0, rfl⟩ : ∃ c0 ∈ B', ch.e.symm c0 = y := ⟨ch.e y, hyB, ch.e.left_inv hys⟩
    rw [ch.e.right_inv (hBt hc0.1)]
    obtain ⟨q, hq, hw⟩ := GlobalTheory.T.exists_framedComplexPoint_of_eigenFrame_off_boundary _ _ _ _ _ _ _ _ s.T.Z σ _ hc0.2.2 f
    have hd := hzl c0 hc0.1 hy f hf q hq hw
    have hu := hPu c0 hc0.1 q hq.symm
    exact GlobalTheory.T.riemann_form_frame_point D A N j S κ s x σ hσ W i (P c0) (hPer c0 hc0.1) (Hm c0) (hHm c0 hc0.1) q (z c0) ⟨hu.symm, hd⟩ _ hq f hw τ a b
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EvalPullSemilinearOfIsTwInv
section
noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan

namespace GlobalTheory.PolFan

namespace OrbMark

theorem eval_pull_semilinear_of_isTwInv : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (φ : InvFun (𝓞 E)),
    IsTwInv H φ →
    ∀ {X Y : Type} [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X] [AddCommGroup Y] [Module (𝓞 E) Y]
      [Module.Finite (𝓞 E) Y] (τ : 𝓞 E ≃+* 𝓞 E), τ H.w0 = H.w0 → ∀ (f : X →+ Y), Function.Surjective f →
      (∀ (a : 𝓞 E) (x : X), f (a • x) = τ a • f x) →
      ∀ B : Y → Y → ℝ, φ.eval X (fun x y => B (f x) (f y)) = φ.eval Y B := by
  intro E _ _ _ H φ htw X Y _ _ _ _ _ _ τ hτ f hf hsm B
  obtain ⟨n, r, hr⟩ := Module.Finite.exists_fin' (𝓞 E) X
  let r₁ : (Fin n → 𝓞 E) →ₗ[𝓞 E] Y :=
    { toFun := fun a => f (r (twv τ.symm a))
      map_add' := fun a b => by
        have e : twv τ.symm (a + b) = twv τ.symm a + twv τ.symm b := funext fun _ => map_add τ.symm _ _
        rw [e, map_add, map_add]
      map_smul' := fun c a => by
        rw [twv_smul, map_smul, hsm, RingEquiv.apply_symm_apply]
        rfl }
  have hr₁ : ∀ a, r₁ (twv τ a) = f (r a) := fun a => by
    show f (r (twv τ.symm (twv τ a))) = f (r a)
    rw [twv_symm_twv]
  have hs₁ : Function.Surjective r₁ := fun y => by
    obtain ⟨x, rfl⟩ := hf y
    obtain ⟨a, rfl⟩ := hr x
    exact ⟨twv τ a, hr₁ a⟩
  rw [φ.eval_eq hr, φ.eval_eq hs₁]
  have h := htw τ hτ n fun a b => B (r₁ a) (r₁ b)
  have e : (fun a b : Fin n → 𝓞 E => B (f (r a)) (f (r b))) = fun a b => B (r₁ (fun i => τ (a i))) (r₁ (fun i => τ (b i))) := by
    funext a b
    exact congrArg₂ B (hr₁ a).symm (hr₁ b).symm
  rw [e]
  exact h

end OrbMark

end GlobalTheory.PolFan
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsArcLiftPeriodsTendstoSpanStatement
section
open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ShFam GlobalTheory.ShFam.BdArc Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (Data Frame Bor rmul lact mat col dmin Wt)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_arcLift_periods_tendsto_span : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) (σ : c.F →+* ℂ) (N : ℕ) (U : Unf Xo c σ N) (A : Type) [CommRing A] (φ : c.F →+* A) (x : Sp A ⟶ gen Z) (fr : EigFrame Z φ (x ≫ genι Z)) (ψ : ℂ → (A →+* ℂ)) (r : ℝ) (y : ℂ → FrPt Xo c (CAt σ)) (k : U.Comp) (T : ℝ) (M : ℕ) (γ : GL (Fin N) E) (xx : ℂ → Frame (U.X k).Ψ N), GoodEmb c σ → IsUnf U → IsArc Z σ φ x ψ r → (∀ u ∈ Metric.ball (0 : ℂ) r, u ≠ 0 → Matches fr (ψ u) (y u)) → IsOrbit (U.X k) T M γ xx → IsLift U k y T xx → ∃ (n : ℕ) (v : Fin n → Fin N → E) (Lp : Fin n → (U.X k).Ψ → Fin (N - (U.X k).p0) → ℂ) (Lm : Fin n → (U.X k).Ψ → Fin (U.X k).p0 → ℂ), (∀ j (τ : (U.X k).Ψ) (i : Fin (N - (U.X k).p0)), Tendsto (fun w => perFr (U.X k) (xx w) (v j) τ.1 i) imTop (𝓝 (Lp j τ i))) ∧ (∀ j (τ : (U.X k).Ψ) (i : Fin (U.X k).p0), Tendsto (fun w => perFr (U.X k) (xx w) (v j) (conjEmb τ.1) i) imTop (𝓝 (Lm j τ i))) ∧ ∀ τ : (U.X k).Ψ, Submodule.span ℂ (Set.range fun j => Lp j τ) = ⊤ ∧ Submodule.span ℂ (Set.range fun j => Lm j τ) = ⊤ := by
  first | exact @GlobalTheory.ShFam.PerLim.exists_periods_tendsto_span | exact GlobalTheory.ShFam.PerLim.exists_periods_tendsto_span | (intros; apply GlobalTheory.ShFam.PerLim.exists_periods_tendsto_span <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCellOfContactSetIntInequalities
section
noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolCell

namespace GlobalTheory.PolCell

section Contact

variable {X : Type} [AddCommGroup X] {m : ℕ}

theorem sum_smul_toReal_apply' (t : Fin m → ℝ) (u : Fin m → LinearMap.BilinForm ℤ X) (y z : X) :
    (∑ i, t i • toReal (u i)) y z = ∑ i, t i * (u i y z : ℝ) := by
  simp [LinearMap.sum_apply]

theorem toReal_sum_nsmul (n : Fin m → ℕ) (u : Fin m → LinearMap.BilinForm ℤ X) :
    toReal (∑ i, n i • u i) = ∑ i, (n i : ℝ) • toReal (u i) := by
  ext y z
  rw [sum_smul_toReal_apply']
  simp [LinearMap.sum_apply]

theorem sum_smul_toReal_comb {r : ℕ} (v : Fin r → Fin m → ℕ) (u : Fin m → LinearMap.BilinForm ℤ X) (c : Fin r → ℝ) :
    ∑ k, c k • toReal (∑ i, v k i • u i) = ∑ i, (∑ k, c k • fun i => (v k i : ℝ)) i • toReal (u i) := by
  ext y z
  rw [sum_smul_toReal_apply', sum_smul_toReal_apply']
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
    toReal_apply, Int.cast_sum, Int.cast_mul, Int.cast_natCast, nsmul_eq_mul]
  simp only [Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => by ring

variable {O : Type} [CommRing O] [Module O X]

theorem sum_mem_realForms_iff (bar : O → O) (u : Fin m → LinearMap.BilinForm ℤ X) (hu : ∀ i y z, u i y z = u i z y)
    (t : Fin m → ℝ) : ∑ i, t i • toReal (u i) ∈ realForms bar X ↔
      ∀ b ∈ {b : Fin m → ℤ | ∃ (a : O) (y z : X), b = fun i => u i (a • y) z - u i y (bar a • z)},
        ∑ i, (b i : ℝ) * t i = 0 := by
  rw [mem_realForms]
  constructor
  · rintro ⟨-, h⟩ b ⟨a, y, z, rfl⟩
    have := h a y z
    rw [sum_smul_toReal_apply', sum_smul_toReal_apply'] at this
    simp only [Int.cast_sub, sub_mul, Finset.sum_sub_distrib, sub_eq_zero]
    simpa only [mul_comm] using this
  · intro h
    refine ⟨fun y z => ?_, fun a y z => ?_⟩
    · rw [sum_smul_toReal_apply', sum_smul_toReal_apply']
      exact Finset.sum_congr rfl fun i _ => by rw [hu i y z]
    · have := h _ ⟨a, y, z, rfl⟩
      rw [sum_smul_toReal_apply', sum_smul_toReal_apply']
      simp only [Int.cast_sub, sub_mul, Finset.sum_sub_distrib, sub_eq_zero] at this
      simpa only [mul_comm] using this

end Contact

theorem exists_isCell_of_contact (O : Type) [CommRing O] [IsDedekindDomain O] [CharZero O] [Module.Finite ℤ O] (bar : O → O)
    (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X] (ψ : InvFun O) (K : ℕ) (Λ : (X × X) →₀ ℤ) (m : ℕ)
    (u : Fin m → LinearMap.BilinForm ℤ X) (A : Set (Fin m → ℤ)) (hA : A.Finite) (hK : 0 < K)
    (hsym : ∀ i y z, u i y z = u i z y) (hnn : ∀ i y, 0 ≤ u i y y)
    (hint : ∀ (β : LinearMap.BilinForm ℤ X) (t : Fin m → ℝ), toReal β = ∑ i, t i • toReal (u i) → ∀ i, ∃ z : ℤ, t i = z)
    (hle : ∀ β ∈ balForms bar X, (∀ y, 0 ≤ β y y) → (K : ℝ) * ψ.evalZ β ≤ evalW Λ (toReal β))
    (hcon : ∀ B ∈ psdCone bar X, (K : ℝ) * evalR ψ B = evalW Λ B → ∃ t : Fin m → ℝ, (∀ i, 0 ≤ t i) ∧
      (∀ v ∈ A, ∑ i, (v i : ℝ) * t i ≤ 0) ∧ B = ∑ i, t i • toReal (u i))
    (hlin : ∀ t : Fin m → ℝ, (∀ i, 0 ≤ t i) → (∀ v ∈ A, ∑ i, (v i : ℝ) * t i ≤ 0) →
      ∑ i, t i • toReal (u i) ∈ realForms bar X →
      (K : ℝ) * evalR ψ (∑ i, t i • toReal (u i)) = evalW Λ (∑ i, t i • toReal (u i))) :
    ∃ (s : ℕ) (γ : Fin s → LinearMap.BilinForm ℤ X), IsCell bar ψ γ ∧
      ∀ B ∈ psdCone bar X, (K : ℝ) * evalR ψ B = evalW Λ B → B ∈ rcone γ := by
  obtain ⟨r, v, hiff, hZ⟩ := GlobalTheory.T.minkowskiWeyl_orthant_cone_integral_constraints m A
    {b | ∃ (a : O) (y z : X), b = fun i => u i (a • y) z - u i y (bar a • z)} hA
  have hbal := sum_mem_realForms_iff bar u hsym
  have hKr : (0 : ℝ) < K := by exact_mod_cast hK
  have hvk : ∀ k, (∀ i, (0 : ℝ) ≤ (v k i : ℝ)) ∧ (∀ a ∈ A, ∑ i, (a i : ℝ) * (v k i : ℝ) ≤ 0) ∧
      (∀ b ∈ {b : Fin m → ℤ | ∃ (a : O) (y z : X), b = fun i => u i (a • y) z - u i y (bar a • z)},
        ∑ i, (b i : ℝ) * (v k i : ℝ) = 0) := by
    intro k
    refine (hiff _).2 ⟨Pi.single k 1, fun j => ?_, ?_⟩
    · by_cases h : j = k
      · subst h; simp
      · simp [h]
    · funext i
      rw [Finset.sum_apply, Finset.sum_eq_single k (fun j _ hj => by simp [Pi.single_apply, hj]) (by simp)]
      simp
  have hγR : ∀ k, toReal (∑ i, v k i • u i) = ∑ i, (v k i : ℝ) • toReal (u i) := fun k => toReal_sum_nsmul _ _
  have hγbal : ∀ k, (∑ i, v k i • u i) ∈ balForms bar X := by
    intro k
    refine ⟨fun y z => ?_, fun a y z => ?_⟩
    · simp only [LinearMap.sum_apply, LinearMap.smul_apply]
      exact Finset.sum_congr rfl fun i _ => by rw [hsym i y z]
    · have h := ((hbal _).2 (hvk k).2.2).2 a y z
      rw [← hγR] at h
      simp only [toReal_apply] at h
      exact_mod_cast h
  have hγval : ∀ k, ((linW Λ (∑ i, v k i • u i) : ℤ) : ℝ) = K * ψ.evalZ (∑ i, v k i • u i) := by
    intro k
    have h := hlin _ (hvk k).1 (hvk k).2.1 ((hbal _).2 (hvk k).2.2)
    rw [← hγR, evalR_toReal, evalW_toReal] at h
    exact h.symm
  have hcomb := sum_smul_toReal_comb v u
  refine ⟨r, fun k => ∑ i, v k i • u i, ⟨hγbal, fun k y => ?_, ?_, ?_⟩, ?_⟩
  · simp only [LinearMap.sum_apply, LinearMap.smul_apply]
    exact Finset.sum_nonneg fun i _ => nsmul_nonneg (hnn i y) _
  · rw [linearOn_iff]
    intro c hc
    obtain ⟨hnt, hAt, hVt⟩ := (hiff _).2 ⟨c, hc, rfl⟩
    have h := hlin _ hnt hAt ((hbal _).2 hVt)
    rw [← hcomb, evalW_sum] at h
    have : (K : ℝ) * evalR ψ (∑ k, c k • toReal (∑ i, v k i • u i)) = K * ∑ k, c k * ψ.evalZ (∑ i, v k i • u i) := by
      rw [h, Finset.mul_sum]
      exact Finset.sum_congr rfl fun k _ => by rw [hγval]; ring
    exact mul_left_cancel₀ hKr.ne' this
  · refine ⟨K, linW Λ, hK, hγval, fun β hβ hp => ?_, fun β hβ hp heq => ?_⟩
    · rw [← evalW_toReal]; exact hle β hβ hp
    · have hpsd : toReal β ∈ psdCone bar X := by
        have := GlobalTheory.T.nonneg_sum_smul_intBilinFormToReal_mem_psdCone O bar X 1 ![β] ![1] (fun i => by fin_cases i; exact hβ)
          (fun i y => by fin_cases i; exact hp y) (fun i => by fin_cases i; norm_num)
        simpa using this
      obtain ⟨t, ht0, htA, htB⟩ := hcon _ hpsd (by rw [evalR_toReal, evalW_toReal]; exact heq)
      have hVt := (hbal t).1 (htB ▸ toReal_mem hβ)
      choose z hz using hint β t htB
      have hz0 : ∀ i, 0 ≤ z i := fun i => by
        have := ht0 i; rw [hz i] at this; exact_mod_cast this
      have htn : ∀ i, (((z i).toNat : ℤ) : ℝ) = t i := fun i => by
        rw [Int.toNat_of_nonneg (hz0 i), hz i]
      obtain ⟨k, c, hk, hkc⟩ := hZ (fun i => (z i).toNat)
        (fun a ha => by
          have := htA a ha
          simp only [← htn] at this
          exact_mod_cast this)
        (fun b hb => by
          have := hVt b hb
          simp only [← htn] at this
          exact_mod_cast this)
      refine ⟨k, c, hk, LinearMap.ext₂ fun y w => ?_⟩
      have hβz : β y w = ∑ i, ((z i).toNat : ℤ) * u i y w := by
        have h1 : (β y w : ℝ) = ∑ i, t i * (u i y w : ℝ) := by
          rw [← toReal_apply, htB, sum_smul_toReal_apply']
        have h2 : (β y w : ℝ) = ((∑ i, ((z i).toNat : ℤ) * u i y w : ℤ) : ℝ) := by
          rw [h1]; push_cast
          exact Finset.sum_congr rfl fun i _ => by rw [← htn i]; push_cast; ring
        exact_mod_cast h2
      have hcoord : ∀ i, (k : ℤ) * ((z i).toNat : ℤ) = ∑ j, (c j : ℤ) * (v j i : ℤ) := fun i => by
        have := congrFun hkc i
        simp only [Pi.smul_apply, smul_eq_mul, Finset.sum_apply] at this
        exact_mod_cast this
      calc (k • β) y w = (k : ℤ) * β y w := by simp
        _ = ∑ i, ((k : ℤ) * ((z i).toNat : ℤ)) * u i y w := by
          rw [hβz, Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring
        _ = ∑ i, ∑ j, (c j : ℤ) * ((v j i : ℤ) * u i y w) := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [hcoord, Finset.sum_mul]; exact Finset.sum_congr rfl fun j _ => by ring
        _ = ∑ j, (c j : ℤ) * ∑ i, (v j i : ℤ) * u i y w := by
          rw [Finset.sum_comm]; simp only [Finset.mul_sum]
        _ = (∑ j, c j • ∑ i, v j i • u i) y w := by
          simp [LinearMap.sum_apply, nsmul_eq_mul]
  · intro B hB hBe
    obtain ⟨t, ht0, htA, rfl⟩ := hcon B hB hBe
    obtain ⟨c, hc, rfl⟩ := (hiff _).1 ⟨ht0, htA, (hbal _).1 (mem_realForms_of_mem_psdCone hB)⟩
    exact ⟨c, hc, (hcomb c).symm⟩

end GlobalTheory.PolCell
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCellQuotientByRadicalOfMemConeStatement
section
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolFan.CarDim
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_cell_quotient_by_radical_of_mem_cone : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (ψ : InvFun (𝓞 E)) (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X], (∀ (m m' : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ X) (s : Fin m' ↪ Fin m) (h : LinearMap.BilinForm ℤ X →ₗ[ℤ] ℤ), IsCell H.bar ψ γ → IsFaceCut γ s h → IsCell H.bar ψ (fun i => γ (s i))) → ∀ β ∈ balForms H.bar X, (∀ y, 0 ≤ β y y) → ∀ (m : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ X), IsCell H.bar ψ γ → InRCone γ β → ∃ (m' : ℕ) (δ : Fin m' → LinearMap.BilinForm ℤ (X ⧸ (orad β : Submodule (𝓞 E) X))), IsCell H.bar ψ δ ∧ InRCone (fun i => pull (orad β : Submodule (𝓞 E) X).mkQ (δ i)) β ∧ genRank δ ≤ genRank γ := by
  first | exact @GlobalTheory.PolFan.CarDim.exists_cell_quot_orad_of_inRCone | exact GlobalTheory.PolFan.CarDim.exists_cell_quot_orad_of_inRCone | (intros; apply GlobalTheory.PolFan.CarDim.exists_cell_quot_orad_of_inRCone <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCommonDenominatorStrictnessSmoothFanStatement
section
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolCell
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_common_denominator_strictness_smooth_fan : ∀ (X : Type) [AddCommGroup X] [Module.Finite ℤ X] (φ : InvFun ℤ), IsPolFanOn (id : ℤ → ℤ) φ X → ∃ N : ℕ, 0 < N ∧ ∀ B ∈ psdCone (id : ℤ → ℤ) X, ∃ (m : ℕ) (u : Fin m → LinearMap.BilinForm ℤ X) (w : (X × X) →₀ ℤ), IsCone (id : ℤ → ℤ) φ u ∧ StrictWith (id : ℤ → ℤ) φ N (linW w) u ∧ B ∈ rcone u := by
  first | exact @GlobalTheory.PolCell.exists_common_den | exact GlobalTheory.PolCell.exists_common_den | (intros; apply GlobalTheory.PolCell.exists_common_den <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsComponentUniformisationBoundedDomainComple
section
open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame
open MeasureTheory Formalism.DegreeFormula GlobalTheory.TrueCx

namespace GlobalTheory.LieBase.UnifExists

open Formalism.MJ ReciprocityTheory.ChartRestriction.G.AR.Up

theorem flat_inj {ι : Type} {p q : ℕ} {z z' : ι → Matrix (Fin p) (Fin q) ℂ} (h : flat z = flat z') : z = z' := by
  funext t a b
  exact congrFun h (t, a, b)

theorem exists_unif : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (T : TorModel Y) (F : Type) [Field F] (e : F ≃+* c.F) (σ : c.F →+* ℂ) (U : Formalism.L2.PjFree.Unf Xo c σ (Dw.p + Dw.q)), Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf U → ∀ (Φ : FlagTor T.Z e U) (k : U.Comp), ∀ (X : Var F) (j : X.X ⟶ gen T.Z) (f : (Φ.C k).Y.X ⟶ X.X) (f₀ : EigFrame T.Z (constF e X) (genericPt X ≫ j ≫ genι T.Z)) (Eb : Fr (ratOf X) Dw.mult 0) (A₀ : Mat Dw.mult X.Fn) (hj : j ≫ genStr T.Z ≫ spMap e.toRingHom = X.str), IsLieBase e (Φ.C k) X j f f₀ Eb A₀ → ∃ ψ : ((U.X k).Ψ × Fin Dw.p × Fin (Dw.p + Dw.q - Dw.p) → ℂ) → CxPts X.str (σ.comp e.toRingHom), (∀ x : (U.X k).dom, cxOf e σ hj (ψ (flat (domPt (U.X k) (Nat.le_add_right Dw.p Dw.q) (Equiv.refl (U.X k).Ψ) x.1))) = cxPt T.Z (U.un k x)) := by
  intro E _ _ _ H Dw l Xo c O _ β Y T F _ e σ U hσ hU Φ k X j f f₀ Eb A₀ hj hL
  obtain ⟨hoi, hfj, -⟩ := hL
  haveI := hoi
  have hp : (U.X k).p0 = Dw.p + Dw.q - Dw.p := first_index_eq_of_unfolded U hU rfl k
  have hle : Dw.p ≤ Dw.p + Dw.q := Nat.le_add_right Dw.p Dw.q
  have hrange : ∀ x : (U.X k).dom, Set.range (cxPt T.Z (U.un k x)).1 ⊆ Set.range j := by
    rintro x _ ⟨s, rfl⟩
    obtain ⟨y, hy⟩ := Φ.label k x s
    refine ⟨f y, ?_⟩
    show (f ≫ j) y = _
    rw [hfj]
    exact hy
  let lf : (U.X k).dom → CxPts X.str (σ.comp e.toRingHom) := fun x =>
    ⟨IsOpenImmersion.lift j (cxPt T.Z (U.un k x)).1 (hrange x), by
      rw [← hj, ← Category.assoc, IsOpenImmersion.lift_fac, ← Category.assoc, (cxPt T.Z (U.un k x)).2,
        ← Spec.map_comp]
      rfl⟩
  have hlf : ∀ x, cxOf e σ hj (lf x) = cxPt T.Z (U.un k x) := fun x =>
    Subtype.ext (IsOpenImmersion.lift_fac _ _ _)
  have hwell : ∀ x x' : (U.X k).dom,
      domPt (U.X k) hle (Equiv.refl (U.X k).Ψ) x.1 = domPt (U.X k) hle (Equiv.refl (U.X k).Ψ) x'.1 →
      cxPt T.Z (U.un k x) = cxPt T.Z (U.un k x') := by
    intro x x' h
    have h5 : ∀ τ, moeb (frameCo (U.X k) hle x.1 τ) 0 = moeb (frameCo (U.X k) hle x'.1 τ) 0 :=
      fun τ => congrFun h τ
    exact cxPt_congr (PointWell.pt_eq_of_block hU hσ k x x'
      (fun τ => PointWell.block_of_moeb_eq _ hle hp x.2 x'.2 τ (h5 τ))
      (fun τ => PointWell.block_of_moeb_eq _ hle hp x'.2 x.2 τ (h5 τ).symm))
  let x0 : (U.X k).dom := ⟨x0F (U.X k), IW.orth_mem_dom (U.X k) _ (isOrth_x0F (U.X k))⟩
  refine ⟨fun v => if h : ∃ x : (U.X k).dom,
      flat (domPt (U.X k) (Nat.le_add_right Dw.p Dw.q) (Equiv.refl (U.X k).Ψ) x.1) = v then lf h.choose else lf x0,
    fun x => ?_⟩
  have h : ∃ x' : (U.X k).dom, flat (domPt (U.X k) (Nat.le_add_right Dw.p Dw.q) (Equiv.refl (U.X k).Ψ) x'.1) =
      flat (domPt (U.X k) (Nat.le_add_right Dw.p Dw.q) (Equiv.refl (U.X k).Ψ) x.1) := ⟨x, rfl⟩
  simp only [dif_pos h]
  rw [hlf]
  exact hwell _ _ (flat_inj h.choose_spec)

end GlobalTheory.LieBase.UnifExists
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsDvrLiftFiniteCoverStatement
section
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.ShFam GlobalTheory.Models GlobalTheory.SiegLoc GlobalTheory.LN GlobalTheory
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_dvr_lift_finite_cover : ∀ (R R' : Type) [CommRing R] [IsLocalRing R] [CommRing R'] [IsLocalRing R'] (ρ : R →+* R'), Function.Injective ρ → ρ.Finite → ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], CDvr V → ∀ ψ : R →+* V, IsLocalHom ψ → ∃ (V' : Type) (_ : CommRing V') (_ : IsDomain V') (_ : IsLocalRing V') (f : V →+* V') (ψ' : R' →+* V'), CDvr V' ∧ Function.Injective f ∧ IsLocalHom f ∧ IsLocalHom ψ' ∧ ψ'.comp ρ = f.comp ψ := by
  first | exact @GlobalTheory.LocExt.exists_cDvr_ext_of_finite | exact GlobalTheory.LocExt.exists_cDvr_ext_of_finite | (intros; apply GlobalTheory.LocExt.exists_cDvr_ext_of_finite <;> assumption)
end

