import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle0011
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle0010
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.Bundle0006
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0003
import ReciprocityTheory.L2DbarEstimates.LeviForms.Bundle0001
import ReciprocityTheory.L2DbarEstimates.ChartDerivatives.HoloSmooth
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.InterpStatementPfH
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0033
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0040
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.Bundle0018
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.NormalisedThetaNormInvariant
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0012
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.PointwiseNormCanonicalThetaEqSqThetaConstant
import Formalism.LocalToGlobal.ProjectiveLattices.ThShort
import Formalism.LocalToGlobal.ProjectiveLattices.ThGerm
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.VtUniq
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0038

-- bundled from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.LogThetaSumInvariantSmooth
section
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.I2 ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Inst
open scoped ContDiff

namespace GlobalTheory.ThetaLogSum

open GlobalTheory.LevelTupleSum

variable {E : Type} [Field E] [NumberField E] {r : ℕ}

theorem gen_map {Λ : Submodule (𝓞 E) (Fin r → E)} (e : (Fin r → E) ≃ₗ[E] (Fin r → E))
    (he : ∀ v, v ∈ Λ ↔ e v ∈ Λ) {t : Fin r → Fin r → E} (h : Gen Λ t) :
    Gen Λ fun j => e (t j) := by
  refine ⟨fun j => ?_, fun u hu => ?_⟩
  · rw [← map_smul]
    exact (he _).1 (h.1 j)
  · obtain ⟨c, y, hy, h2⟩ := h.2 (e.symm u) ((he _).2 (by simpa using hu))
    refine ⟨c, e y, (he _).1 hy, ?_⟩
    have := congrArg e h2
    simpa only [LinearEquiv.apply_symm_apply, map_add, map_sum, map_smul] using this

theorem exists_reps_map {Λ : Submodule (𝓞 E) (Fin r → E)} (e : (Fin r → E) ≃ₗ[E] (Fin r → E))
    (he : ∀ v, v ∈ Λ ↔ e v ∈ Λ) (𝒯 : Finset (Fin r → Fin r → E)) (h1 : ∀ t ∈ 𝒯, Gen Λ t)
    (h2 : ∀ t, Gen Λ t → ∃! t', t' ∈ 𝒯 ∧ ∀ j, t j - t' j ∈ Λ) :
    ∃ 𝒯' : Finset (Fin r → Fin r → E), (∀ t ∈ 𝒯', Gen Λ t) ∧
      (∀ t, Gen Λ t → ∃! t', t' ∈ 𝒯' ∧ ∀ j, t j - t' j ∈ Λ) ∧
      ∀ f : (Fin r → Fin r → E) → ℝ, ∑ t ∈ 𝒯', f t = ∑ t ∈ 𝒯, f fun j => e (t j) := by
  let ι : (Fin r → Fin r → E) ↪ (Fin r → Fin r → E) :=
    ⟨fun t j => e (t j), fun t t' h => funext fun j => e.injective (congrFun h j)⟩
  refine ⟨𝒯.map ι, fun t ht => ?_, fun t ht => ?_, fun f => Finset.sum_map _ _ _⟩
  · obtain ⟨s, hs, rfl⟩ := Finset.mem_map.1 ht
    exact gen_map e he (h1 s hs)
  · have he' : ∀ v, v ∈ Λ ↔ e.symm v ∈ Λ := fun v => by
      rw [he (e.symm v), LinearEquiv.apply_symm_apply]
    obtain ⟨s, ⟨hs, hs2⟩, hu⟩ := h2 _ (gen_map e.symm he' ht)
    refine ⟨ι s, ⟨Finset.mem_map_of_mem _ hs, fun j => ?_⟩, ?_⟩
    · have := (he _).1 (hs2 j)
      rwa [map_sub, LinearEquiv.apply_symm_apply] at this
    · rintro _ ⟨ht', h3⟩
      obtain ⟨s', hs', rfl⟩ := Finset.mem_map.1 ht'
      rw [hu s' ⟨hs', fun j => ?_⟩]
      rw [he, map_sub, LinearEquiv.apply_symm_apply]
      exact h3 j

variable [IsCMField E]

theorem contDiffOn_cpt (X : Data E r) (x0 : Frame X.Ψ r) {F : Frame X.Ψ r → ℂ}
    (hF : DifferentiableOn ℂ F X.dom) : ContDiffOn ℝ ∞ (fun z => F (cpt X x0 z)) (OmF X x0) := by
  have hc : Differentiable ℂ (cpt X x0) :=
    differentiable_pi.2 fun τ => differentiable_pi.2 fun a => differentiable_pi.2 fun b =>
      (IW.cpt_entry_cd X x0 τ a b).differentiable (by simp)
  exact (ReciprocityTheory.L2DbarEstimates.contDiffOn_of_differentiableOn _ _ _ (ExF.isOpen_OmF X x0)
    (hF.comp hc.differentiableOn fun z hz => hz)).restrict_scalars ℝ

theorem contDiffOn_nfac (X : Data E r) (x0 : Frame X.Ψ r) (la : Wt X.Ψ r) :
    ContDiffOn ℝ ∞ (fun z => X.nfac la (cpt X x0 z)) (OmF X x0) := by
  have h : ContDiffOn ℝ ∞ (fun z => Real.exp (phla X la (cpt X x0 z) / (-2))) (OmF X x0) :=
    fun z hz => ((IW.phla_cpt_cdAt X x0 hz la).div_const _).exp.contDiffWithinAt
  refine h.congr fun z hz => ?_
  rw [phla, mul_div_cancel_left₀ _ (by norm_num), Real.exp_log (flowTermNormDecay.nfac_pos X la hz)]

theorem log_theta_sum_invariant_smooth : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : DataX E r), (∃ ξ : Fin r → E, X.toData.IsIso ξ) → (∃ w0 : 𝓞 E, ∀ u ∈ X.Λ, ∀ v ∈ X.Λ, ∃ k : ℤ, Algebra.trace ℚ E (X.ξ0 * herm X.Gm u (((w0 : E) - cc (w0 : E)) • v)) - Algebra.trace ℚ E (X.ξ0 * herm X.Gm u v) = 2 * k) → ∀ ps : Frame X.Ψ r → ℝ, (∀ x ∈ X.dom, ∃ A : TorusAt X.toData x, ps x = Real.log (∑ᶠ (a : Fin A.T.r → Vsp A.T.dim) (_ : a ∈ {a : Fin A.T.r → Vsp A.T.dim | (∀ j, a j ∈ ZSpan.fundamentalDomain A.T.b) ∧ (∀ j, ((5 : ℂ) ^ 2) • a j ∈ A.T.L) ∧ ∀ x ∈ A.T.L, ∃ c : Fin A.T.r → 𝓞 E, ∃ y ∈ A.T.L, x = ∑ j, act (c j) (((5 : ℂ) ^ 2) • a j) + (5 : ℂ) • y}), ∏ b, A.T.ptN2 1 A.s (fun _ => a b) / A.T.l2 1 A.s)) → IsInvFn X.toData ps ∧ ∀ x0 ∈ X.dom, ContDiffOn ℝ ∞ (fun z => ps (cpt X.toData x0 z)) {z | cpt X.toData x0 z ∈ X.dom} := by
  intro E _ _ _ r X _ hw ps hps
  obtain ⟨𝒯, h1, h2⟩ := exists_reps X.Λ X.Λ_fg
  refine ⟨fun γ hγ x hx b hb => ?_, fun x0 _ => ?_⟩
  · have hs := X.Γ_stab γ hγ
    have hy := MajInv.lact_mem_dom X.toData hs (OrthogonalFrameDomain.rmul_mem_dom X.toData hx hb)
    obtain ⟨A, hA⟩ := hps x hx
    obtain ⟨A', hA'⟩ := hps _ hy
    obtain ⟨𝒯', h1', h2', h3⟩ := exists_reps_map (Matrix.GeneralLinearGroup.toLin γ).toLinearEquiv
      hs.2 𝒯 h1 h2
    rw [hA, hA', sum_eq hx A 𝒯 h1 h2 _ (torus_r A), sum_eq hy A' 𝒯' h1' h2' _ (torus_r A'), h3]
    congr 1
    refine Finset.sum_congr rfl fun t _ => Finset.prod_congr rfl fun j _ => ?_
    exact (ThetaRho.normalised_theta_norm_invariant E r X hw x hx b hb γ hs A A' (t j)).1
  · obtain ⟨Θ, D, κ, -, hΘ, hD, hD0, hf⟩ := ThetaHol.normalised_theta_norm_holomorphic E r X hw
    have key : ∀ x ∈ X.dom, 0 < ∑ t ∈ 𝒯, ∏ j, κ * ‖Θ (t j) x‖ ^ 2 * ‖D x‖ *
          X.nfac (fun _ j => if X.p0 ≤ (j : ℕ) then 1 else -1) x ∧
        ps x = Real.log (∑ t ∈ 𝒯, ∏ j, κ * ‖Θ (t j) x‖ ^ 2 * ‖D x‖ *
          X.nfac (fun _ j => if X.p0 ≤ (j : ℕ) then 1 else -1) x) := by
      intro x hx
      obtain ⟨A, hA⟩ := hps x hx
      have hp := TupleSumPos.tuple_sum_pos E r X x A
      rw [sum_eq hx A 𝒯 h1 h2 _ (torus_r A)] at hA hp
      simp only [hf x hx A] at hA hp
      exact ⟨hp, hA⟩
    refine ContDiffOn.congr (ContDiffOn.log ?_ fun z hz => (key _ hz).1.ne') fun z hz => (key _ hz).2
    refine ContDiffOn.sum fun t _ => contDiffOn_prod fun j _ => ?_
    exact ((contDiffOn_const.mul ((contDiffOn_cpt X.toData x0 (hΘ _)).norm_sq ℂ)).mul
      ((contDiffOn_cpt X.toData x0 hD).norm ℂ fun z hz => hD0 _ hz)).mul
      (contDiffOn_nfac X.toData x0 _)

end GlobalTheory.ThetaLogSum
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.TorsionIsotropicCommutatorPairing
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

namespace ThetaIsotropy

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}

section Tate

variable {k : Type} [Field k] {Q : Type} [CommGroup Q] {act : 𝓞 E → Q → Q} {e : ℕ → Q → Q → kˣ → Prop}

theorem ev_sum (I : TateIso Dw k Q act e) (m : ℕ) (hm : 0 < m) {n : ℕ} (a : Fin n → Dw.La) :
    I.ev m (∑ j, a j) = ∏ j, I.ev m (a j) := by
  have h0 : I.ev m 0 = 1 := (I.ker m hm 0).2 ⟨0, (smul_zero _).symm⟩
  let f : Multiplicative Dw.La →* Q :=
    { toFun := fun x => I.ev m x.toAdd, map_one' := h0, map_mul' := fun x y => I.add m _ _ }
  exact map_prod f (fun j => Multiplicative.ofAdd (a j)) Finset.univ

theorem dvd_EF_of_killed (m j : ℕ) (a b : Dw.La) (ha : ∀ c ∈ l.Mb ^ j, Dw.ModN m (c • a))
    (hb : ∀ c ∈ l.Mb ^ j, Dw.ModN m (c • b)) : (m : ℤ) ∣ Dw.EF a b := by
  have cop : l.Mb ^ j ⊔ (l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E)) ^ j = ⊤ :=
    Ideal.sup_pow_eq_top' (Ideal.pow_sup_eq_top l.coprime)
  obtain ⟨p, hp, q, hq, hpq⟩ := Submodule.mem_sup.1 (cop.ge (Submodule.mem_top : (1 : 𝓞 E) ∈ ⊤))
  rw [← Ideal.map_pow, Ideal.mem_map_iff_of_surjective (H.bar : 𝓞 E →+* 𝓞 E) H.bar.surjective] at hq
  obtain ⟨r, hr, rfl⟩ := hq
  obtain ⟨a', ha'⟩ := ha r hr
  obtain ⟨b', hb'⟩ := hb p hp
  have e₁ : Dw.EF a b = Dw.EF a (p • b) + Dw.EF (r • a) b := by
    rw [Dw.adj, ← map_add, ← add_smul]
    have : p + H.bar r = 1 := hpq
    rw [this, one_smul]
  rw [e₁, ha', hb', map_nsmul, map_nsmul, LinearMap.smul_apply, nsmul_eq_mul, nsmul_eq_mul]
  exact dvd_add (dvd_mul_right _ _) (dvd_mul_right _ _)

end Tate

variable (Xo : Moduli Dw l) {B : Type} [CommRing B] (x0 : Sp B ⟶ Xo.X)

noncomputable def bc {K : Type} [CommRing K] (χ : B →+* K) : ptO Xo (spMap χ ≫ x0) ⟶ ptO Xo x0 :=
  Over.homMk (spMap χ) rfl

theorem unit_eq_one (hL : Laws) (N : ℕ) (hN : 0 < N) (u : Γ((ptO Xo x0).left, ⊤)ˣ) (hu : u ^ (N ^ 2) = 1)
    (h : ∀ (K : Type) [Field K] [IsAlgClosed K] (χ : B →+* K),
      Units.map (bc Xo x0 χ).left.appTop.hom.toMonoidHom u = 1) : u = 1 := by
  let i₀ := (Scheme.ΓSpecIso (CommRingCat.of B)).hom
  have hi : Function.Injective i₀.hom := (ConcreteCategory.bijective_of_isIso i₀).1
  have hU : IsUnit ((N ^ 2 : ℕ) : B) := by
    have := ((baseKA l).unit (N ^ 2) (pow_pos hN 2)).map (Spec.preimage (x0 ≫ Xo.s)).hom
    rwa [map_natCast] at this
  have key := (T.universal_weilPairing_pullback_exists_unique hL E H Dw l Xo N hN).2.2 B (i₀.hom u.val) (N ^ 2) hU
    (by rw [← map_pow, ← Units.val_pow_eq_pow_val, hu, Units.val_one, map_one]) (fun K _ _ χ => by
      have nat := Scheme.ΓSpecIso_naturality (CommRingCat.ofHom χ)
      have e := congrArg (fun φ => φ.hom u.val) nat
      have h1 : (spMap χ).appTop.hom u.val = 1 := congrArg Units.val (h K χ)
      simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at e
      rw [← e]
      exact (congrArg _ h1).trans (map_one _))
  exact Units.ext (hi (key.trans (map_one _).symm))

theorem exists_tate (hL : Laws) (N : ℕ) (hN : 0 < N) (K : Type) [Field K] [IsAlgClosed K] (χ : B →+* K) :
    ∃ I : TateIso Dw K (ptO Xo (spMap χ ≫ x0) ⟶ Xo.univ.t.G) (fun a g => g ≫ Xo.univ.t.act.act a)
        (fun n g g' c => WeilIs Xo.univ.t.G Xo.univ.t.PP.L n g g' (unitOn c)),
      ∀ (x y : ptO Xo x0 ⟶ Xo.univ.t.G) (e : Γ((ptO Xo x0).left, ⊤)ˣ), x ^ (N ^ 2) = 1 → y ^ (N ^ 2) = 1 →
        WeilIs Xo.univ.t.G Xo.univ.t.PP.L ((N : ℤ) ^ 2) x y e → ∀ a b, I.ev (N ^ 2) a = bc Xo x0 χ ≫ x →
        I.ev (N ^ 2) b = bc Xo x0 χ ≫ y →
        Units.map (bc Xo x0 χ).left.appTop.hom.toMonoidHom e = unitOn (I.ζ (N ^ 2) ^ Dw.EF a b) := by
  obtain ⟨-, I, -⟩ := Xo.univ.geom K (spMap χ ≫ x0) (Spec.preimage ((spMap χ ≫ x0) ≫ Xo.s)).hom
    (Spec.map_preimage _).symm
  refine ⟨I, fun x y e hx hy he a b ha hb => ?_⟩
  obtain ⟨W₁, W₂, -⟩ := T.universal_weilPairing_pullback_exists_unique hL E H Dw l Xo N hN
  have h₁ := W₁ _ _ (bc Xo x0 χ) x y e hx hy he
  have h₂ := I.isom (N ^ 2) (pow_pos hN 2) a b
  rw [ha, hb, Nat.cast_pow] at h₂
  obtain ⟨e₀, -, -, hu⟩ := W₂ _ (bc Xo x0 χ ≫ x) (bc Xo x0 χ ≫ y)
    (by rw [← MonObj.comp_pow, hx, MonObj.comp_one]) (by rw [← MonObj.comp_pow, hy, MonObj.comp_one])
  exact (hu _ h₁).trans (hu _ h₂).symm

theorem unitOn_prod {K : Type} [CommRing K] {n : ℕ} (c : Fin n → Kˣ) : ∏ b, unitOn (c b) = unitOn (∏ b, c b) :=
  (map_prod (Units.map (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom.toMonoidHom) c Finset.univ).symm

theorem prod_zpow_eq {U : Type} [CommGroup U] (z : U) {n : ℕ} (c : Fin n → ℤ) : ∏ b, z ^ c b = z ^ ∑ b, c b :=
  (map_prod (zpowersHom U z) (fun b => Multiplicative.ofAdd (c b)) Finset.univ).symm

theorem unitOn_one {K : Type} [CommRing K] : unitOn (1 : Kˣ) = 1 :=
  map_one (Units.map (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom.toMonoidHom)

theorem comp_prod {S : Scheme.{0}} {G T T' : Over S} [GrpObj G] [IsCommMonObj G] (h : T' ⟶ T) {n : ℕ}
    (x : Fin n → (T ⟶ G)) : h ≫ (List.ofFn x).prod = ∏ j, h ≫ x j := by
  rw [List.prod_ofFn]
  let f : (T ⟶ G) →* (T' ⟶ G) :=
    { toFun := fun g => h ≫ g, map_one' := MonObj.comp_one _, map_mul' := fun a b => MonObj.comp_mul _ _ _ }
  exact map_prod f x Finset.univ

end ThetaIsotropy

open ThetaIsotropy in

theorem zh_isotropic_and_half_isotropic : Laws → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (B : Type) [CommRing B] (x0 : Sp B ⟶ Xo.X) (n : ℕ) (Λ : GenLat E n) (N : ℕ), Λ.Unimod → 0 < N → Ideal.span {(N : 𝓞 E)} • stdLat E n ≤ Λ.La → (∀ (a a' : Fin n → (ptO Xo x0 ⟶ Xo.univ.t.G)) (e : Fin n → Γ((ptO Xo x0).left, ⊤)ˣ), InZh Xo Λ N a → InZh Xo Λ N a' → (∀ b, WeilIs Xo.univ.t.G Xo.univ.t.PP.L ((N : ℤ) ^ 2) (a b) (a' b) (e b)) → ∏ b, e b = 1) ∧ ∀ (x y : ptO Xo x0 ⟶ Xo.univ.t.G) (j : ℕ), x ^ (N ^ 2) = 1 → y ^ (N ^ 2) = 1 → KilledBy Xo (l.Mb ^ j) x → KilledBy Xo (l.Mb ^ j) y → WeilIs Xo.univ.t.G Xo.univ.t.PP.L ((N : ℤ) ^ 2) x y 1 := by
  intro hL E _ _ _ H Dw l Xo B _ x0 n Λ N hΛ hN hle
  have hN2 : 0 < N ^ 2 := pow_pos hN 2
  obtain ⟨-, W₂, -⟩ := T.universal_weilPairing_pullback_exists_unique hL E H Dw l Xo N hN
  have tors : ∀ {K : Type} [CommRing K] (χ : B →+* K) {x : ptO Xo x0 ⟶ Xo.univ.t.G}, x ^ (N ^ 2) = 1 →
      (bc Xo x0 χ ≫ x) ^ (N ^ 2) = 1 := fun χ x hx => by rw [← MonObj.comp_pow, hx, MonObj.comp_one]
  refine ⟨fun a a' e ha ha' he => ?_, fun x y j hx hy kx ky => ?_⟩
  · refine unit_eq_one Xo x0 hL N hN _ ?_ fun K _ _ χ => ?_
    · rw [← Finset.prod_pow]
      refine Finset.prod_eq_one fun b _ => ?_
      obtain ⟨e₀, -, h₀, hu⟩ := W₂ _ (a b) (a' b) (ha.1 b) (ha'.1 b)
      rw [hu _ (he b), h₀]
    · obtain ⟨I, hI⟩ := exists_tate Xo x0 hL N hN K χ
      choose v hv using fun b => (I.onto _ hN2 _).1 (tors χ (ha.1 b))
      choose v' hv' using fun b => (I.onto _ hN2 _).1 (tors χ (ha'.1 b))
      have lat : ∀ {a : Fin n → (ptO Xo x0 ⟶ Xo.univ.t.G)} {v : Fin n → Dw.La}, InZh Xo Λ N a →
          (∀ b, I.ev (N ^ 2) (v b) = bc Xo x0 χ ≫ a b) →
          ∀ (mu : Matrix (Fin n) (Fin n) E), (∀ v ∈ Λ.La, mu.mulVec v ∈ stdLat E n) →
            ∀ cm : Fin n → Fin n → 𝓞 E, (∀ i j, (cm i j : E) = (N : E) * mu i j) →
              ∀ i, Dw.ModN (N ^ 2) (∑ j, cm i j • v j) := fun {a v} ha hv mu hmu cm hcm i => by
        refine (I.ker _ hN2 _).1 ?_
        have h₁ := congrArg (bc Xo x0 χ ≫ ·) (ha.2 mu hmu cm hcm i)
        simp only [MonObj.comp_one] at h₁
        rw [comp_prod] at h₁
        rw [ev_sum I _ hN2, ← h₁]
        refine Finset.prod_congr rfl fun j _ => ?_
        rw [I.lin, hv, Category.assoc]
      have hd := T.sq_dvd_sum_alternating_forms_of_killed_lattice E H Dw n Λ N hΛ hN hle v v' (lat ha hv) (lat ha' hv')
      rw [map_prod, Finset.prod_congr rfl fun b _ => hI _ _ _ (ha.1 b) (ha'.1 b) (he b) _ _ (hv b) (hv' b)]
      refine (unitOn_prod _).trans ?_
      rw [prod_zpow_eq,
        ((I.ζ_prim _ hN2).zpow_eq_one_iff_dvd _).2 (by rwa [Nat.cast_pow]), unitOn_one]
  · obtain ⟨e, he, h₀, -⟩ := W₂ _ x y hx hy
    suffices e = 1 by rwa [this] at he
    refine unit_eq_one Xo x0 hL N hN _ h₀ fun K _ _ χ => ?_
    obtain ⟨I, hI⟩ := exists_tate Xo x0 hL N hN K χ
    obtain ⟨v, hv⟩ := (I.onto _ hN2 _).1 (tors χ hx)
    obtain ⟨v', hv'⟩ := (I.onto _ hN2 _).1 (tors χ hy)
    have lat : ∀ {x : ptO Xo x0 ⟶ Xo.univ.t.G} {v : Dw.La}, KilledBy Xo (l.Mb ^ j) x →
        I.ev (N ^ 2) v = bc Xo x0 χ ≫ x → ∀ c ∈ l.Mb ^ j, Dw.ModN (N ^ 2) (c • v) := fun {x v} kx hv c hc => by
      refine (I.ker _ hN2 _).1 ?_
      rw [I.lin, hv, Category.assoc, kx c hc, MonObj.comp_one]
    have hd := dvd_EF_of_killed (N ^ 2) j v v' (lat kx hv) (lat ky hv')
    rw [hI _ _ _ hx hy he _ _ hv hv', ((I.ζ_prim _ hN2).zpow_eq_one_iff_dvd _).2 hd]
    exact unitOn_one

end GlobalTheory
end

