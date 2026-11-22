import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1545
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoverReadingEqPowMulMovedFrameReading
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormGenEqOneOfFrOver
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0034
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0625
import Development.AbelianVarietyTheory.Counterexamples.HeightSurvey.ExistsNotIntegralLie
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0123
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2087
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SupportedSubgroupSplitCommutePrimeIdempotents
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2097

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelCoverComponentOverBaseRationalIsometry
section
open NumberField MeasureTheory Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.L2.Theta Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.AllWt GlobalTheory.LevGeo GlobalTheory.LevPull GlobalTheory.FieldBC
open scoped ENNReal

noncomputable section

namespace GlobalTheory.LevModel

section Mark

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {g : ℕ}

theorem mark_of_exp {D : Datum H} {l l₂ : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H} {Xo : Moduli D l} {Xo₂ : Moduli D l₂}
    {r : Xo₂.X ⟶ Xo.X} (m : SABMap Xo₂.univ.t Xo.univ.t r) (pd : ℕ) (hM : l₂.M = l.M * pd) (hle : l₂.Mb ≤ l.Mb)
    (heta : ∀ a, (Xo₂.univ.eta a ^ pd).left ≫ m.φ = r ≫ (Xo.univ.eta a).left)
    {σ : KA l →+* ℂ} {σ₂ : KA l₂ →+* ℂ} {ty ty₂ : Fin g → (E →+* ℂ)} (F : FamilyUnif Xo σ ty)
    (F₂ : FamilyUnif Xo₂ σ₂ ty₂) (k : Fin F.n) (k₂ : Fin F₂.n) {P : (F.Di k).La →+ (Fin g → ℂ)}
    {P₂ : (F₂.Di k₂).La →+ (Fin g → ℂ)} (hP : IsPeriod (F.Di k) ty P) (hP₂ : IsPeriod (F₂.Di k₂) ty₂ P₂)
    (hu : F₂.u k₂ P₂ ≫ r = F.u k P)
    (gam : (F₂.Di k₂).La ≃ₗ[𝓞 E] (F.Di k).La) (h : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ))
    (hh : ∀ a, P (gam a) = h (P₂ a))
    (hx : ∀ z, (F.ex k P (h z)).left = (F₂.ex k₂ P₂ z).left ≫ m.φ) :
    ∀ a ∈ l₂.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) D.La),
      ∃ x, gam (F₂.t k₂ a) = F.t k a + l.M • x := by
  have hM0 : 0 < l.M := lt_of_lt_of_le (by norm_num) l.three_le
  have hp0 : pd ≠ 0 := fun h0 => by
    have := l₂.three_le
    rw [hM, h0] at this
    omega
  have hmap : l₂.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) ≤ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) := Ideal.map_mono hle
  intro a ha
  have j₂ := F.ex_eta k P hP a (Submodule.smul_mono_left hmap ha)
  have j₁ : toUnit _ ≫ Xo₂.univ.eta a ^ pd = F₂.ex k₂ P₂ ((l.M : ℂ)⁻¹ • P₂ (F₂.t k₂ a)) := by
    rw [MonObj.comp_pow, F₂.ex_eta k₂ P₂ hP₂ a ha, ← GlobalTheory.CoverExp.pow_of_add (F₂.ex_add k₂ P₂ hP₂), hM,
      ← Nat.cast_smul_eq_nsmul ℂ, smul_smul, Nat.cast_mul, mul_inv, mul_left_comm,
      mul_inv_cancel₀ (Nat.cast_ne_zero.2 hp0), _root_.mul_one]
  have e : F.ex k P ((l.M : ℂ)⁻¹ • P (gam (F₂.t k₂ a))) = F.ex k P ((l.M : ℂ)⁻¹ • P (F.t k a)) := by
    apply Over.OverMorphism.ext
    rw [hh, ← map_smul h, hx, ← j₁, ← j₂, Over.comp_left, Over.comp_left, Category.assoc, heta]
    have w₂ : (toUnit (Over.mk (F₂.u k₂ P₂))).left = F₂.u k₂ P₂ := by
      simpa using Over.w (toUnit (Over.mk (F₂.u k₂ P₂)))
    have w₁ : (toUnit (Over.mk (F.u k P))).left = F.u k P := by
      simpa using Over.w (toUnit (Over.mk (F.u k P)))
    rw [w₂, w₁, ← Category.assoc, hu]
  exact (GlobalTheory.UnifPoint.div_eq_iff hP.2.1 (F.ex_add k P hP) (F.ex_ker k P hP) hM0 _ _).1 e

end Mark

section Down

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.FrameLift

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H} {Xo : Moduli Dw l} {c : Coeff l} {n : ℕ}

theorem exists_frOver_down (d : DeltaDat Xo c n) {S : Type} [CommRing S] [Algebra c.F S] [Algebra d.c₂.F S]
    (y₂ : FrPt d.Xo₂ d.c₂ S) (y₀ : FrPt Xo c S) (e : y₂.x ≫ d.r = y₀.x) (hu : ∀ τ i, y₂.u τ i ≫ d.m.φ = y₀.u τ i) :
    ∃ y : FrPt Xo c S, y.x = y₀.x ∧ y.u = y₀.u ∧ FrOver d y₂ y := by
  obtain ⟨w, hw, hw', -⟩ := d.m.lin
  obtain ⟨p, k, p₁, p₂, hk, hk'⟩ := exists_pm_iso d.m e
  have hL := Xo.univ.t.PP.isLB
  have hL₂ := d.Xo₂.univ.t.PP.isLB
  obtain ⟨s, hs⟩ := exists_up hL hL₂ hw p₁ hk hk' y₂.s
  refine ⟨⟨y₀.x, y₀.x_over, y₀.u, y₀.tan, y₀.eig, y₀.basis, s, fun s' => ?_⟩, rfl, rfl,
    (frOver_iff d _ _).2 ⟨e, hu, w, p, ⟨hw, hw'⟩, p₁, p₂, hs⟩⟩
  obtain ⟨s₂', hs'⟩ := exists_down hL hL₂ hw p₁ s'
  refine (existsUnique_congr fun a => ?_).1 (y₂.gen s₂')
  exact (scal_iff (fst (Over.mk y₂.x) d.Xo₂.univ.t.G).left (toΓ S a) y₂.s s₂').trans
    ((rel_scal_iff hL hL₂ p₁ hk p₂ (toΓ S a) hs hs').trans
      (scal_iff (fst (Over.mk y₀.x) Xo.univ.t.G).left (toΓ S a) s s').symm)

end Down

section Emb

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H} {Xo : Moduli Dw l} {c : Coeff l} {n : ℕ}

theorem good_comp (d : DeltaDat Xo c n) (σ₂ : d.c₂.F →+* ℂ) (h : GoodEmb d.c₂ σ₂) :
    GoodEmb c (σ₂.comp (d.eF : c.F →+* d.c₂.F)) :=
  (congrArg σ₂ (Subtype.ext rfl)).trans h

theorem genScal_eq {S : Type} [CommRing S] (t : Sˣ) :
    genScal (Dw := Dw) t = fun i => Option.elim i t (fun _ => 1) := by
  funext i
  cases i <;> simp [genScal]

end Emb

open AlgebraicGeometry CategoryTheory in
set_option maxHeartbeats 1600000 in

theorem over_comp : ∀ (D : D7) (j : ℕ) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ D.R.r) (dict : ∀ σ : c.F →+* ℂ, GA D (D.sp.W j) → Σ k, Frame ((U σ).X k).Ψ D.R.r) (d : DeltaDat Xo c 0) (U₂ : ∀ σ : d.c₂.F →+* ℂ, Unf d.Xo₂ d.c₂ σ D.R.r) (dict₂ : ∀ σ : d.c₂.F →+* ℂ, GA D (D.sp.W j) → Σ k, Frame ((U₂ σ).X k).Ψ D.R.r), Laws D j Xo c U dict → Laws D j d.Xo₂ d.c₂ U₂ dict₂ → d.IsLev → ∀ σ₂, GoodEmb d.c₂ σ₂ → ∀ k₂ : (U₂ σ₂).Comp, ∃ (k : (U (σ₂.comp (d.eF : c.F →+* d.c₂.F))).Comp) (δ : GL (Fin D.R.r) D.host.E), ((U₂ σ₂).X k₂).Gm = ((U (σ₂.comp (d.eF : c.F →+* d.c₂.F))).X k).Gm ∧ (∀ v w, herm ((U₂ σ₂).X k₂).Gm ((δ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).mulVec v) ((δ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).mulVec w) = herm ((U₂ σ₂).X k₂).Gm v w) ∧ GlobalTheory.LevModel.Over d σ₂ (U (σ₂.comp (d.eF : c.F →+* d.c₂.F))) (U₂ σ₂) k₂ k δ := by
  intro D j H Dw l Xo c U dict d U₂ dict₂ hL hL₂ hd σ₂ hσ₂ k₂
  have hσ : GoodEmb c (σ₂.comp (d.eF : c.F →+* d.c₂.F)) := good_comp d σ₂ hσ₂
  set σ := σ₂.comp (d.eF : c.F →+* d.c₂.F) with hσe
  have hA : l.A = 1 := hL.levA
  have hA₂ : d.l₂.A = 1 := hL₂.levA
  have hU := hL.unf σ hσ
  have hU₂ := hL₂.unf σ₂ hσ₂
  obtain ⟨hr₀, hW⟩ := hL.modelW σ hσ
  obtain ⟨hr₂, hW₂⟩ := hL₂.modelW σ₂ hσ₂
  have hpq : Dw.p ≠ Dw.q := by
    obtain ⟨hp, hq, -⟩ := hL.dat
    obtain ⟨h1, h2⟩ := hL.inR
    have hk := D.R.m_add_three_le_k
    rw [hp, hq]
    simp only [Ranks.sigW, Ranks.r]
    omega
  have hle : KA l ≤ KA d.l₂ := by rw [KA, KA, hA, hA₂]
  have hinc : (σ₂.comp (IntermediateField.inclusion d.c₂.le).toRingHom).comp
      (IntermediateField.inclusion hle).toRingHom = σ.comp (IntermediateField.inclusion c.le).toRingHom :=
    RingHom.ext fun a => congrArg σ₂ (Subtype.ext rfl)
  have hrel : ∀ τ : D.host.E →+* ℂ, relab c σ τ = relab d.c₂ σ₂ τ := fun τ => by
    ext a
    exact congrArg σ₂ (Subtype.ext rfl)
  obtain ⟨-, -, -, -, -, g, e, F, ik, φ, hEF, hper⟩ := id hU
  obtain ⟨-, -, -, -, -, g₂, e₂, F₂, ik₂, φ₂, hEF₂, hper₂⟩ := id hU₂
  obtain rfl : g₂ = g := by simpa using Fintype.card_congr (e₂.trans e.symm)
  obtain ⟨x₀, hx₀⟩ := GlobalTheory.UnifFamily.dom_nonempty ((U₂ σ₂).X k₂)
  obtain ⟨P₀, hP₀, hp₀, hu₀, -⟩ := hper₂ k₂ ⟨x₀, hx₀⟩
  letI : Field (CAt σ) := inferInstanceAs (Field ℂ)
  have hy : (F₂.u (ik₂ k₂) P₀ ≫ d.r) ≫ Xo.s = spMap (σ.comp (IntermediateField.inclusion c.le).toRingHom) := by
    rw [CategoryTheory.Category.assoc, GlobalTheory.ClsVal.Cmp.point_over_of_ne hpq hA d hle,
      ← CategoryTheory.Category.assoc, F₂.over_σ _ P₀ hp₀, GlobalTheory.ClsVal.Cmp.spMap_comp', hinc]
  obtain ⟨y, hyx⟩ := GlobalTheory.NonIntegralFrameExample.exists_framed (c := c) (S := CAt σ) (F₂.u (ik₂ k₂) P₀ ≫ d.r) hy
  obtain ⟨k, x₁, t₁, hb⟩ := hU.2.2.1 y
  obtain ⟨P₁, hP₁, hp₁, hu₁, -⟩ := hper k x₁
  have hu : F₂.u (ik₂ k₂) P₀ ≫ d.r = F.u (ik k) P₁ := by
    rw [← hu₁, ← hb.1]
    exact hyx.symm
  obtain ⟨gam, hl, hg, hh, hx⟩ := GlobalTheory.CoverFrameMod.exists_isometry_of_cover F₂ F d.m hp₀ hp₁ hu
  have gM := mark_of_exp d.m d.pd hd.2.1 hd.1.2.1 hd.2.2.2.2.2.1.1 F F₂ (ik k) (ik₂ k₂) hp₁ hp₀ hu gam hl hh hx
  obtain ⟨a, ε, hε, hξ, hmul, -, hiso⟩ := GlobalTheory.TraceIsometry.exists_gl_of_trace_isometry D.host.E D.R.r
    ((U₂ σ₂).X k₂) ((U σ).X k) (fun τ => (hL₂.xiAbs σ₂ hσ₂ k₂ τ).trans (hL.xiAbs σ hσ k τ).symm)
    ((φ₂ k₂).symm.trans (gam.trans (φ k))) (fun u v => by
      have e₁ := hEF k (gam ((φ₂ k₂).symm u)) (gam ((φ₂ k₂).symm v))
      have e₂ := hEF₂ k₂ ((φ₂ k₂).symm u) ((φ₂ k₂).symm v)
      rw [hg] at e₁
      rw [LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply] at e₂
      exact e₁.symm.trans e₂)
  have hξ₀ : ((U σ).X k).ξ0 = ((U₂ σ₂).X k₂).ξ0 := (hW k).2.trans (hW₂ k₂).2.symm
  obtain rfl : ε = 1 := mul_right_cancel₀ ((U₂ σ₂).X k₂).ξ0_ne (by rw [← hξ, one_mul, hξ₀])
  have hG : ((U σ).X k).Gm = ((U₂ σ₂).X k₂).Gm := (hW k).1.trans (hW₂ k₂).1.symm
  have hΨ : ∀ τ, τ ∈ ((U σ).X k).Ψ ↔ τ ∈ ((U₂ σ₂).X k₂).Ψ := fun τ =>
    ((hU.2.1 k).2 τ).trans ((hU₂.2.1 k₂).2 τ).symm
  have hp0 : ((U σ).X k).p0 = ((U₂ σ₂).X k₂).p0 := (hU.2.1 k).1.trans (hU₂.2.1 k₂).1.symm
  have hiso' : ∀ v w, herm ((U σ).X k).Gm ((a : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).mulVec v)
      ((a : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).mulVec w) = herm ((U₂ σ₂).X k₂).Gm v w := fun v w => by
    rw [hiso, one_mul]
  have hgam : ∀ b, (φ k (gam b) : Fin D.R.r → D.host.E) =
      (a : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).mulVec (φ₂ k₂ b : Fin D.R.r → D.host.E) := fun b => by
    rw [hmul (φ₂ k₂ b)]
    simp
  refine ⟨k, a, hG.symm, fun v w => ?_, ?_⟩
  · have h' := hiso' v w
    rwa [hG] at h'
  intro x hx x' hmv
  have hx' : x' ∈ ((U σ).X k).dom :=
    GlobalTheory.FrameDom.mem_dom_of_isometry _ _ _ _ a hp0 hΨ hiso' x x' hx hmv
  refine ⟨hx', ?_⟩
  obtain ⟨Q₁, hQ₁, hq₁, hqu₁, hqv₁, hqn₁⟩ := hper k ⟨x', hx'⟩
  obtain ⟨Q₂, hQ₂, hq₂, hqu₂, hqv₂, hqn₂⟩ := hper₂ k₂ ⟨x, hx⟩
  obtain ⟨c₁, c₂⟩ := GlobalTheory.CoverFrameRead.point_over d hd hpq hA hle hinc e e₂ F F₂ (ik k) (ik₂ k₂) hq₁ hq₂ gam hg gM
    (fun b i => by
      rw [hQ₁, hQ₂, hgam, Equiv.apply_symm_apply, hrel]
      exact GlobalTheory.CoverFrameRead.perFr_move _ _ hΨ hp0 hG a hiso' x x' hmv _ _ _)
  have hx₂ : ((U₂ σ₂).un k₂ ⟨x, hx⟩).x ≫ d.r = ((U σ).un k ⟨x', hx'⟩).x := by
    rw [hqu₁, hqu₂]
    exact c₁
  have hu₂ : ∀ τ i, ((U₂ σ₂).un k₂ ⟨x, hx⟩).u τ i ≫ d.m.φ = ((U σ).un k ⟨x', hx'⟩).u τ i :=
    fun τ i => c₂ ⟨τ, i⟩ _ _ (hqv₁ τ i) (hqv₂ τ i)
  letI : Algebra c.F (CAt σ₂) := σ.toAlgebra
  obtain ⟨z, hzx, hzu, ho⟩ := exists_frOver_down (S := CAt σ₂) d ((U₂ σ₂).un k₂ ⟨x, hx⟩) ((U σ).un k ⟨x', hx'⟩) hx₂ hu₂
  obtain ⟨t, ht⟩ := GlobalTheory.GeoLevel.exists_frBor_gen (σ := σ) ((U σ).un k ⟨x', hx'⟩) z hzx hzu
  have hn' : (∀ τ i, ‖dmin ((U₂ σ₂).X k₂).Gm x τ i‖ = 1) → ∀ τ i, ‖dmin ((U σ).X k).Gm x' τ i‖ = 1 := by
    intro hn τ i
    obtain ⟨τ, h₁⟩ := τ
    have h₂ := (hΨ τ).1 h₁
    have e' : dmin ((U σ).X k).Gm x' ⟨τ, h₁⟩ i = dmin ((U₂ σ₂).X k₂).Gm x ⟨τ, h₂⟩ i := by
      unfold dmin
      rw [hmv τ h₂ h₁, GlobalTheory.FrameDom.gram_mul _ _ _ hiso' τ]
    rw [e']
    exact hn _ _
  refine ⟨t, fun hn => ?_, z, ?_, ho⟩
  · exact GlobalTheory.CoverFrameMod.norm_gen_eq_one_of_frOver d F₂ F (ik₂ k₂) (ik k) Q₂ Q₁ ((U₂ σ₂).un k₂ ⟨x, hx⟩)
      ((U σ).un k ⟨x', hx'⟩) z (fun i => Option.elim i t (fun _ => 1)) hq₂ hq₁ hqu₂ hqu₁ (hqn₂ hn) (hqn₁ (hn' hn)) ho ht
  · have e' : genScal (Dw := Dw) (S := CAt σ₂) t = fun i => Option.elim i t (fun _ => 1) := genScal_eq _
    exact e'.symm ▸ ht

end GlobalTheory.LevModel
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelElementLocalCoprimeActsTrivially
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.L2.Pj GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.ExpFrame GlobalTheory.ExpTie GlobalTheory.FrameOf
open scoped TensorProduct

namespace GlobalTheory.FrameTriv

theorem map_eq_one_of_isLocEnv {D : D7} (V : Formalism.BasicNotions.TH.HSp D) {Pl0 : Type} (pl : Pl0 → HeightOneSpectrum (𝓞 D.host.E)) (ok : Set Pl0)
    (i : ok × ℕ) (x : Bridge.Gf V) (hloc : isLocEnv V pl ok i x) (l : ℕ) (hl : (l : 𝓞 D.host.E) ∉ (pl i.1).asIdeal)
    {R : Type} [CommRing R] (ev : (FiniteAdeleRing (𝓞 D.host.F) D.host.F) ⊗[D.host.F] D.host.E →+* R)
    (hev : ∀ a : FiniteAdeleRing (𝓞 D.host.F) D.host.F,
      (∀ v : HeightOneSpectrum (𝓞 D.host.F), (l : 𝓞 D.host.F) ∈ v.asIdeal → a v = 0) → ev (a ⊗ₜ[D.host.F] 1) = 0) :
    (x.1.val : Matrix (Fin V.rank) (Fin V.rank) ((FiniteAdeleRing (𝓞 D.host.F) D.host.F) ⊗[D.host.F] D.host.E)).map ev = 1 := by
  obtain ⟨e, α, he, -, hS, hx⟩ := hloc
  obtain ⟨Φ, hΦ⟩ := GlobalTheory.IdemSupport.exists_comp D
  obtain ⟨-, ε, hε, hf⟩ := GlobalTheory.IdemSupport.of_isPrimeIdem hΦ (Or.inl ⟨he, rfl⟩)
  obtain ⟨εf, hεf, -, h0⟩ := hε
  have hvan : ev (εf ⊗ₜ[D.host.F] (1 : D.host.E)) = 0 := by
    refine hev εf fun v' hv' => h0 v' ?_
    rintro rfl
    apply hl
    have h2 : algebraMap (𝓞 D.host.F) (𝓞 D.host.E) (l : 𝓞 D.host.F) ∈ (pl i.1).asIdeal := hv'
    rwa [map_natCast] at h2
  let φ : Formalism.L2.Theta.AE D →+* (FiniteAdeleRing (𝓞 D.host.F) D.host.F) ⊗[D.host.F] D.host.E :=
    (Algebra.TensorProduct.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sndA D.host.F) (AlgHom.id D.host.F D.host.E)).toRingHom
  have hmat : ∀ a c, x.1.val a c = φ ((Formalism.L2.Theta.mt V α) a c) := by
    intro a c
    rw [hx]
    rfl
  have hφε : φ (algebraMap _ (Formalism.L2.Theta.AE D) ε) = εf ⊗ₜ[D.host.F] (1 : D.host.E) := by
    rw [hεf]
    rfl
  let ψ : Formalism.L2.Theta.AE D →+* R := ev.comp φ
  have hψ : ψ (algebraMap _ (Formalism.L2.Theta.AE D) ε) = 0 := (congrArg ev hφε).trans hvan
  ext a c
  have hsplit : Formalism.L2.Theta.mt V α a c =
      algebraMap _ (Formalism.L2.Theta.AE D) ε * (Formalism.L2.Theta.mt V α - 1) a c + (1 : Matrix _ _ (Formalism.L2.Theta.AE D)) a c := by
    rw [← hf, hS a c, Matrix.sub_apply, sub_add_cancel]
  refine (congrArg ev (hmat a c)).trans ?_
  show ψ _ = _
  rw [hsplit, ψ.map_add, ψ.map_mul, hψ, zero_mul, zero_add, Matrix.one_apply, Matrix.one_apply]
  split_ifs
  · exact ψ.map_one
  · exact ψ.map_zero

theorem intEmb_injective {l : ℕ} [Fact l.Prime] (Lf : IntermediateField ℚ_[l] (PadicAlgCl l)) : Function.Injective (intEmb Lf) :=
  fun _ _ h => Subtype.ext (Subtype.ext h)

theorem kap_eq_one {O K : Type} [CommRing O] [CommRing K] {f : O →+* K} (hf : Function.Injective f) {N n : ℕ} (g : GL (Fin N) O)
    (b : GL (Fin N) K) (M : Matrix (Fin n) (Fin n) K) (rk : Fin N → Fin n) (hrk : Function.Injective rk) (hM : M = 1)
    (h : (Matrix.GeneralLinearGroup.map f g).val = (b⁻¹).val * M.submatrix rk rk * b.val) : g = 1 := by
  rw [hM, Matrix.submatrix_one _ hrk, mul_one, Units.inv_mul] at h
  refine Units.ext (Matrix.ext fun a c => hf ?_)
  have h3 : f (g.val a c) = (1 : Matrix (Fin N) (Fin N) K) a c := congrFun (congrFun h a) c
  rw [h3, Units.val_one, Matrix.one_apply, Matrix.one_apply]
  split_ifs
  · exact f.map_one.symm
  · exact f.map_zero.symm

theorem chi_eq_one {O K ι : Type} [CommRing O] [Field K] [Fintype ι] {f : O →+* K} (hf : Function.Injective f) {N : ℕ}
    (io : K ≃+* ℂ) (g : ι → GL (Fin N) O) (sh : ι → ℤ) (x : Oˣ) (y : ℂˣ) (hg : g = 1) (hy : y = 1)
    (h : io (f x * ∏ τ, f (g τ).val.det ^ sh τ) * (y : ℂ) = 1) : x = 1 := by
  subst hg hy
  simp only [Pi.one_apply, Units.val_one, Matrix.det_one, map_one, one_zpow, Finset.prod_const_one, mul_one] at h
  refine Units.ext (hf (io.injective ?_))
  rw [h, Units.val_one, map_one, map_one]

set_option maxHeartbeats 1000000 in

theorem triv_of_isLocEnv : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ} (p : PtAt ex Csz) (j : Fin D.R.m) (w : HeightOneSpectrum (𝓞 D.what₂.LL)) [Fact (Formalism.EigenvalueLevelCeiling.plc w).Prime] {N : ℕ} (e0 : D.what₂.LL →+* PadicAlgCl (Formalism.EigenvalueLevelCeiling.plc w)) (b : Bool) (io : PadicAlgCl (Formalism.EigenvalueLevelCeiling.plc w) ≃+* ℂ) (ev : D.what₂.Tau → ((FiniteAdeleRing (𝓞 D.host.F) D.host.F) ⊗[D.host.F] D.host.E →+* PadicAlgCl (Formalism.EigenvalueLevelCeiling.plc w))) (bs : D.what₂.Tau → GL (Fin N) (PadicAlgCl (Formalism.EigenvalueLevelCeiling.plc w))) (rk : Fin N ≃o Fin (Vc D j).rank) (sh : D.what₂.Tau → ℤ) (Lf : IntermediateField ℚ_[Formalism.EigenvalueLevelCeiling.plc w] (PadicAlgCl (Formalism.EigenvalueLevelCeiling.plc w))) [FiniteDimensional ℚ_[Formalism.EigenvalueLevelCeiling.plc w] Lf] (kap : levJ p j (p.R.mu w) →* (D.what₂.Tau → GL (Fin N) (intR Lf))) (chi : levJ p j (p.R.mu w) →* (intR Lf)ˣ), ChoiceOk p j w e0 b io ev bs rk sh kap chi → ∀ (i : (blk p j (p.R.mu w)).Pl × ℕ), 1 ≤ i.2 → i.2 ≤ (Vc D j).rank → ((Formalism.EigenvalueLevelCeiling.plc w : ℕ) : 𝓞 D.host.E) ∉ (plOf p j (p.R.mu w) i.1).asIdeal → ∀ u : Bridge.Gf (Vc D j), u ∈ levJ p j (p.R.mu w) → isLocEnv (Vc D j) p.R.pl (p.P.A3.A.ok (p.R.mu w)) i u → (frameOf p j (p.R.mu w) (Formalism.EigenvalueLevelCeiling.plc w) N Lf kap chi).Triv u := by
  intro D L hT Gi Gl Kc Y cX ex Csz p j w _ N e0 b io ev bs rk sh Lf _ kap chi hC i hi1 hi2 hl u hu hloc
  obtain ⟨-, -, -, hEv, hKap, hChi⟩ := hC
  have hc : levChi p j (p.R.mu w) ⟨u, hu⟩ = 1 := (p.R.B.L j (p.R.mu w)).hecke.chi_loc i ⟨hi1, hi2⟩ ⟨u, hu⟩ hloc
  have hone : ∀ τ, (matOf j u).map (ev τ) = 1 := fun τ =>
    map_eq_one_of_isLocEnv (Vc D j) p.R.pl (p.P.A3.A.ok (p.R.mu w)) i u hloc (Formalism.EigenvalueLevelCeiling.plc w) hl (ev τ) (hEv τ).2.2.1
  have hk : kap ⟨u, hu⟩ = 1 := funext fun τ =>
    kap_eq_one (intEmb_injective Lf) (kap ⟨u, hu⟩ τ) (bs τ) ((matOf j u).map (ev τ)) rk rk.injective (hone τ) (hKap ⟨u, hu⟩ τ)
  have hx : chi ⟨u, hu⟩ = 1 :=
    chi_eq_one (intEmb_injective Lf) io (kap ⟨u, hu⟩) sh (chi ⟨u, hu⟩) (levChi p j (p.R.mu w) ⟨u, hu⟩) hk hc (hChi ⟨u, hu⟩)
  exact ⟨hu, hk, hx⟩

end GlobalTheory.FrameTriv
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftWeightRhoBlockConstantCentred
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links GlobalTheory.ExpTie GlobalTheory.ExpTie.Lift

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ExpTie.Lift

theorem block_centre : ∀ {D : Formalism.BasicNotions.D7} (L : Formalism.BasicNotions.SizeData₂ D) (j : Fin D.R.m) (τ : D.what₂.Tau), GlobalTheory.ExpTie.Lift.ValsAt L j τ → (∀ a, Formalism.CohomologicalDescent.ShortWeightBounds.kc (GlobalTheory.ExpTie.parOf L j) + (GlobalTheory.ExpTie.Lift.wts L j).j τ ≤ a → a < Formalism.CohomologicalDescent.ShortWeightBounds.kc (GlobalTheory.ExpTie.parOf L j) + (GlobalTheory.ExpTie.Lift.wts L j).j τ + (GlobalTheory.ExpTie.parOf L j).t → (GlobalTheory.ExpTie.Lift.wts L j).lam τ a = (GlobalTheory.ExpTie.Lift.wts L j).lam τ (Formalism.CohomologicalDescent.ShortWeightBounds.kc (GlobalTheory.ExpTie.parOf L j) + (GlobalTheory.ExpTie.Lift.wts L j).j τ)) ∧ (((GlobalTheory.ExpTie.Lift.wts L j).bot (GlobalTheory.ExpTie.parOf L j) τ : ℝ) + (((GlobalTheory.ExpTie.parOf L j).t : ℝ) - 1) / 2 - (GlobalTheory.ExpTie.Lift.wts L j).c τ = -(GlobalTheory.ExpTie.Lift.wts L j).e τ) := by
  intro D L j τ hv
  have hk := D.R.m_add_three_le_k
  have ht0 := D.R.t_odd.pos
  have hkc : Formalism.CohomologicalDescent.ShortWeightBounds.kc (parOf L j) + (wts L j).j τ = D.R.k + (j : ℕ) := by
    simp only [Formalism.CohomologicalDescent.ShortWeightBounds.kc, parOf, wts]; omega
  have htt : (parOf L j).t = D.R.t := rfl
  have he : (wts L j).e τ = wj D ((j : ℕ) + 1) τ := rfl
  constructor
  · intro a ha1 ha2
    rw [hkc] at ha1 ⊢
    rw [hkc, htt] at ha2
    obtain ⟨s, rfl⟩ := Nat.exists_eq_add_of_le ha1
    have h1 := hv.2.2.1 s (by omega)
    have h0 := hv.2.2.1 0 ht0
    simp only [add_zero, Nat.cast_zero, sub_zero] at h0
    have hU : ((wts L j).U (parOf L j) τ (D.R.k + j + s) : ℝ) = (((wts L j).U (parOf L j) τ (D.R.k + j) - s : ℤ) : ℝ) := by
      push_cast; linarith
    have hU' := Int.cast_injective (α := ℝ) hU
    change Formalism.CohomologicalDescent.UnitNormBounds.UN _ _ _ = Formalism.CohomologicalDescent.UnitNormBounds.UN _ _ _ - _ at hU'
    unfold Formalism.CohomologicalDescent.UnitNormBounds.UN at hU'
    push_cast at hU'
    omega
  · have hrow : Formalism.CohomologicalDescent.ShortWeightBounds.kc (parOf L j) + (wts L j).j τ + (parOf L j).t - 1 = D.R.k + (j : ℕ) + (D.R.t - 1) := by
      rw [hkc, htt]; omega
    have h := hv.2.2.1 (D.R.t - 1) (by omega)
    have hts : ((D.R.t - 1 : ℕ) : ℝ) = (D.R.t : ℝ) - 1 := by
      rw [Nat.cast_sub (by omega)]; simp
    rw [hts] at h
    rw [Formalism.CohomologicalDescent.ShortWeightBounds.Wts.bot, hrow, htt, he]
    linarith

end GlobalTheory.ExpTie.Lift

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftWeightRhoEntriesLeFloorHeight
section
set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links GlobalTheory.ExpTie GlobalTheory.ExpTie.Lift

namespace GlobalTheory.ExpTie.Lift

theorem wts_U_le_h0_of_large : ∀ {D : Formalism.BasicNotions.D7} (L : Formalism.BasicNotions.SizeData₂ D) (P5 : Formalism.BasicNotions.ParameterChoice' D L) (j : Fin D.R.m) (τ : D.what₂.Tau), (GlobalTheory.ExpTie.parOf L j).Large → GlobalTheory.ExpTie.Lift.ValsAt L j τ → ∀ a, a < (GlobalTheory.ExpTie.parOf L j).Nr → (GlobalTheory.ExpTie.Lift.wts L j).U (GlobalTheory.ExpTie.parOf L j) τ a ≤ (Formalism.CohomologicalDescent.ShortWeightBounds.h0 (GlobalTheory.ExpTie.parOf L j) : ℤ) := by
  intro D L P5 j τ hL hv a ha
  have hk := D.R.m_add_three_le_k
  have hm2 := D.R.two_le_m
  have ht1 : (1 : ℝ) ≤ D.R.t := L.t_win.1
  have hk1 : (1 : ℝ) ≤ D.R.k := by exact_mod_cast (by omega : 1 ≤ D.R.k)
  have hS := L.Sc_pos
  have hη := L.etaSz_pos
  have x1 := L.sc.one_lt_alt
  have x0 : 0 < L.sc.x := by linarith
  have hb0 : 0 < L.sc.b' := by
    unfold Scale.b' Scale.a Scale.X' Scale.b
    exact div_pos (mul_pos x0 (Real.exp_pos _)) (Real.exp_pos _)
  have hn : (1 : ℝ) ≤ D.R.n := by unfold Ranks.n; exact_mod_cast (Nat.succ_le_of_lt (Formalism.HC.Frame.ord_pos _) : 1 ≤ _)
  have hU0 := U_nonneg L j τ 0 (by have := rank_eq j; omega)
  have hUa := liftWeightCombinatorialData_U_le_U_zero L j τ a ha
  have hv0 := hv.1 0 (by omega)
  have hcl := L.cloud_v τ ⟨0, by omega⟩
  have hc := c_le L j τ hv

  have ePb : (parOf L j).b = L.sc.b := rfl
  have eh : (parOf L j).h = L.sc.b + L.Sc + L.etaSz + (D.R.t : ℝ) + 1 := rfl
  have hbb' := hL.bb'
  have htop := hL.top_le
  simp only [parOf] at hbb' htop
  change 12 * (D.R.k : ℝ) * (D.R.t : ℝ) * L.sc.b' < L.sc.b at hbb'

  have hm1 : 1 ≤ D.R.m := by omega
  have key : wj D D.R.m τ ≤ L.sc.b + L.etaSz + 1 ∨
      wj D D.R.m τ ≤ L.sc.b' * (1 + 1 / L.sc.x + 1 / L.sc.x ^ 2) + L.etaSz := by
    by_cases h1 : (D.eTau τ : D.R.GG) ∈ D.host.topPlaces
    · classical
      obtain ⟨t, ht1, ht2⟩ : ∃ t ∈ D.host.TT, D.R.tau1 t = (D.eTau τ : D.R.GG) := by
        unfold Host.topPlaces at h1
        simpa using h1
      have hw := (L.win_top D.R.m hm1 le_rfl τ ⟨t, ht1⟩ ht2.symm).2
      have hbt := P5.bT_le ⟨t, ht1⟩
      have hr := P5.rho_le
      unfold LevelStarExponents.rhoP at hr
      have hLa : 0 < L.LaG := by
        have h := P5.S_le
        by_contra hc'
        push_neg at hc'
        have : L.LaG * L.sc.b' / D.R.k ≤ 0 :=
          div_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonpos_of_nonneg hc' hb0.le) (by positivity)
        linarith
      have hNs : 0 ≤ LevelStarExponents.Nstar L := by
        unfold LevelStarExponents.Nstar Scale.delta1; positivity
      have hx2 : L.sc.x ^ (-2 : ℝ) = 1 / L.sc.x ^ 2 := by
        rw [Real.rpow_neg x0.le, one_div]; norm_cast
      have h4 : 0 ≤ P5.Crho * Real.log L.sc.x * L.LaG / D.R.k := by
        have := P5.Crho_pos; have := Real.log_nonneg x1.le; positivity
      have h5 : LevelStarExponents.Nstar L * L.sc.x ^ L.sc.eps * L.LaG / D.R.k ≤ 1 / L.sc.x ^ 2 := by
        have h6 : 0 ≤ LevelStarExponents.Nstar L * L.sc.x ^ L.sc.eps * L.LaG / D.R.k := by positivity
        have : 4 * LevelStarExponents.Nstar L * L.sc.x ^ L.sc.eps * L.LaG / D.R.k = 4 * (LevelStarExponents.Nstar L * L.sc.x ^ L.sc.eps * L.LaG / D.R.k) := by ring
        rw [hx2] at hr
        linarith
      have h7 : LevelStarExponents.Nstar L * L.sc.x ^ L.sc.eps * L.LaG * L.sc.b' / D.R.k =
          (LevelStarExponents.Nstar L * L.sc.x ^ L.sc.eps * L.LaG / D.R.k) * L.sc.b' := by ring
      have h8 : (LevelStarExponents.Nstar L * L.sc.x ^ L.sc.eps * L.LaG / D.R.k) * L.sc.b' ≤ 1 / L.sc.x ^ 2 * L.sc.b' :=
        mul_le_mul_of_nonneg_right h5 hb0.le
      right
      have : L.sc.b' * (1 + 1 / L.sc.x + 1 / L.sc.x ^ 2) = L.sc.b' + L.sc.b' / L.sc.x + 1 / L.sc.x ^ 2 * L.sc.b' := by ring
      rw [this]
      linarith
    · by_cases h2 : (D.eTau τ : D.R.GG) ∈ D.host.thickPlaces
      · exact Or.inl (L.win_thick D.R.m hm1 le_rfl τ h2).2
      · have hw := (L.win_thin D.R.m hm1 le_rfl τ ⟨(D.eTau τ).2, h1, h2⟩).2
        right
        have hw1 : L.sc.w'' D.R.n ≤ L.sc.b' := by
          unfold Scale.w''
          rw [div_le_iff₀ (by positivity)]
          have hxn : 1 ≤ L.sc.x * (D.R.n : ℝ) := by nlinarith
          have := mul_le_mul_of_nonneg_left hxn hb0.le
          linarith
        have hpos : 0 ≤ L.sc.b' * (1 / L.sc.x + 1 / L.sc.x ^ 2) := by positivity
        nlinarith
  have hU0h : ((wts L j).U (parOf L j) τ 0 : ℝ) ≤ (parOf L j).h := by
    rw [eh]
    rcases key with h | h
    · nlinarith
    · have h2b : 2 * L.sc.b' < L.sc.b := by
        have : 2 * L.sc.b' ≤ 12 * (D.R.k : ℝ) * (D.R.t : ℝ) * L.sc.b' := by
          have : (1 : ℝ) ≤ (D.R.k : ℝ) * (D.R.t : ℝ) := by nlinarith
          nlinarith
        linarith
      linarith
  have hfl : ((wts L j).U (parOf L j) τ 0).toNat ≤ Formalism.CohomologicalDescent.ShortWeightBounds.h0 (parOf L j) := by
    unfold Formalism.CohomologicalDescent.ShortWeightBounds.h0
    apply Nat.le_floor
    have : (((wts L j).U (parOf L j) τ 0).toNat : ℝ) = ((wts L j).U (parOf L j) τ 0 : ℝ) := by
      exact_mod_cast Int.toNat_of_nonneg hU0
    rw [this]; exact hU0h
  omega

end GlobalTheory.ExpTie.Lift
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftWeightRhoLowsDistanceBounds
section
set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links GlobalTheory.ExpTie GlobalTheory.ExpTie.Lift

namespace GlobalTheory.ExpTie.Lift

theorem low_dist : ∀ {D : Formalism.BasicNotions.D7} (L : Formalism.BasicNotions.SizeData₂ D) (P5 : Formalism.BasicNotions.ParameterChoice' D L) (j : Fin D.R.m) (τ : D.what₂.Tau), GlobalTheory.ExpTie.Lift.ValsAt L j τ → ∀ a, a < (GlobalTheory.ExpTie.parOf L j).Nr → ((Formalism.CohomologicalDescent.ShortWeightBounds.kc (GlobalTheory.ExpTie.parOf L j) ≤ a ∧ a < Formalism.CohomologicalDescent.ShortWeightBounds.kc (GlobalTheory.ExpTie.parOf L j) + (GlobalTheory.ExpTie.Lift.wts L j).j τ) ∨ Formalism.CohomologicalDescent.ShortWeightBounds.kc (GlobalTheory.ExpTie.parOf L j) + (GlobalTheory.ExpTie.Lift.wts L j).j τ + (GlobalTheory.ExpTie.parOf L j).t ≤ a) → 2 * (GlobalTheory.ExpTie.parOf L j).b / (GlobalTheory.ExpTie.parOf L j).lstar + ((GlobalTheory.ExpTie.parOf L j).t : ℝ) / 2 + 3 ≤ |((GlobalTheory.ExpTie.Lift.wts L j).U (GlobalTheory.ExpTie.parOf L j) τ a : ℝ) - (GlobalTheory.ExpTie.Lift.wts L j).c τ + (GlobalTheory.ExpTie.Lift.wts L j).e τ| ∧ |((GlobalTheory.ExpTie.Lift.wts L j).U (GlobalTheory.ExpTie.parOf L j) τ a : ℝ) - (GlobalTheory.ExpTie.Lift.wts L j).c τ + (GlobalTheory.ExpTie.Lift.wts L j).e τ| ≤ (GlobalTheory.ExpTie.parOf L j).η := by
  intro D L P5 j τ hv a ha hcase
  have hn := rank_eq j
  have hk := D.R.m_add_three_le_k
  have hjm := j.2
  change a < (Vc D j).rank at ha
  change (D.R.k - 1 ≤ a ∧ a < D.R.k - 1 + ((j : ℕ) + 1)) ∨ D.R.k - 1 + ((j : ℕ) + 1) + D.R.t ≤ a at hcase
  obtain ⟨i, hval⟩ : ∃ i : Fin D.R.m,
      ((wts L j).U (parOf L j) τ a : ℝ) - (wts L j).c τ = -(((D.hc τ).b i : ℚ) : ℝ) := by
    rcases hcase with ⟨h1, h2⟩ | h1
    · refine ⟨⟨a - (D.R.k - 1), by omega⟩, ?_⟩
      have h := hv.2.1 ⟨a - (D.R.k - 1), by omega⟩ (by simp only [Fin.le_def]; omega)
      have ha' : D.R.k - 1 + (a - (D.R.k - 1)) = a := by omega
      simp only [ha'] at h
      exact h
    · refine ⟨⟨a - (D.R.k - 1) - D.R.t, by omega⟩, ?_⟩
      have h := hv.2.2.2 ⟨a - (D.R.k - 1) - D.R.t, by omega⟩ (by simp only [Fin.lt_def]; omega)
      have ha' : D.R.k - 1 + (a - (D.R.k - 1) - D.R.t) + D.R.t = a := by omega
      simp only [ha'] at h
      exact h
  have he : (wts L j).e τ = (((D.hc τ).e j : ℚ) : ℝ) := by
    show wj D ((j : ℕ) + 1) τ = _
    unfold wj
    rw [dif_pos (by omega)]
    congr 3
  have habs : |((wts L j).U (parOf L j) τ a : ℝ) - (wts L j).c τ + (wts L j).e τ| =
      |(((D.hc τ).b i - (D.hc τ).e j : ℚ) : ℝ)| := by
    rw [hval, he, ← abs_neg]
    push_cast
    ring_nf
  rw [habs]
  refine ⟨?_, L.be_close τ i j⟩
  have hN : ((D.R.N D.R.m : ℕ) : ℝ) = (D.R.k : ℝ) + (D.R.m : ℝ) * ((D.R.t : ℝ) + 1) := by
    unfold Ranks.N
    push_cast
    ring
  have hls : (parOf L j).lstar = LevelStarExponents.lStar L := by
    unfold Formalism.CohomologicalDescent.LogSmallConstantBounds.Par.lstar LevelStarExponents.lStar
    rw [hN]
    rfl
  have hb : (parOf L j).b = L.sc.b := rfl
  rw [hls, hb]
  exact P5.lows_far τ i j

end GlobalTheory.ExpTie.Lift

end
end

