import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0013
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0287
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0348
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.ConcreteLevelAdelicSubset
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.Measures
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0282
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0292
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0323

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.FrameClassTermCountLeCardAut
section
noncomputable section
open scoped Classical ENNReal Pointwise
open MeasureTheory Matrix NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full
  Formalism.L2.SG.LocWSOf Formalism.MainNotions.S.Cnt Formalism.L2.SG.KappaOffDiagonal Formalism.MainNotions.LatticeGluingRadicals

namespace GlobalTheory.TypeAsm.FibCard
attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Main
variable {D : D7} {X : HidaSetting D}

theorem stab_of_fix' (u : D.what₂.Word) {a : (VS D).V ≃ₗ[D.host.E] (VS D).V} (hi : a ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT)
    (hfix : ∀ c, a ((F0 X u).e c) = (F0 X u).e c) : a ∈ stabF D (X.Fu u) := by
  refine ⟨hi, fun j => ?_, ?_⟩
  · unfold FlagG.Xa
    rw [Submodule.map_span, Set.image_image]
    congr 1
    apply Set.image_congr
    intro i _
    have h' : (F0 X u).e i.castSucc = (X.Fu u).e i := fv_cast (lf D (X.Fu u)).fl i
    have := hfix i.castSucc
    rw [h'] at this
    exact this
  · have h' : (F0 X u).e (Fin.last _) = (X.Fu u).z := fv_last (lf D (X.Fu u)).fl
    have := hfix (Fin.last _)
    rw [h'] at this
    exact this

theorem fix_X (u : D.what₂.Word) {a : (VS D).V ≃ₗ[D.host.E] (VS D).V}
    (hfix : ∀ c, a ((F0 X u).e c) = (F0 X u).e c) : ∀ x ∈ (X.Fu u).X, a x = x := by
  intro x hx
  have h : Set.EqOn (⇑(a : (VS D).V →ₗ[D.host.E] (VS D).V)) (⇑(LinearMap.id : (VS D).V →ₗ[D.host.E] (VS D).V))
      (Set.range (X.Fu u).e) := by
    rintro _ ⟨i, rfl⟩
    have h' : (F0 X u).e i.castSucc = (X.Fu u).e i := fv_cast (lf D (X.Fu u)).fl i
    have := hfix i.castSucc
    rw [h'] at this
    exact this
  simpa using LinearMap.eqOn_span h hx

theorem perp_pres (u : D.what₂.Word) {a : (VS D).V ≃ₗ[D.host.E] (VS D).V} (hi : a ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT)
    (hfix : ∀ c, a ((F0 X u).e c) = (F0 X u).e c) :
    ∀ y ∈ perpS (VS D) (X.Fu u).X, a y ∈ perpS (VS D) (X.Fu u).X := by
  intro y hy x hx
  rw [← fix_X u hfix x hx, hi x y]
  exact hy x hx

theorem ind_exists (u : D.what₂.Word) {a : (VS D).V ≃ₗ[D.host.E] (VS D).V} (hi : a ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT)
    (hfix : ∀ c, a ((F0 X u).e c) = (F0 X u).e c) :
    ∃ φ : WbQ D (X.Fu u) → WbQ D (X.Fu u), ∀ (x : perpS (VS D) (X.Fu u).X) (hx : a x.1 ∈ perpS (VS D) (X.Fu u).X),
      φ (Submodule.Quotient.mk x) = Submodule.Quotient.mk ⟨a x.1, hx⟩ := by
  let f : perpS (VS D) (X.Fu u).X →ₗ[D.host.E] perpS (VS D) (X.Fu u).X :=
    (a : (VS D).V →ₗ[D.host.E] (VS D).V).restrict (perp_pres u hi hfix)
  let q := (X.Fu u).X.comap (perpS (VS D) (X.Fu u).X).subtype
  have hq : q ≤ q.comap f := by
    intro x hx
    simp only [q, Submodule.mem_comap, Submodule.subtype_apply] at hx ⊢
    show a x.1 ∈ (X.Fu u).X
    rw [fix_X u hfix x.1 hx]; exact hx
  refine ⟨Submodule.mapQ q q f hq, fun x hx => ?_⟩
  rw [Submodule.mapQ_apply]
  rfl

end Main
end GlobalTheory.TypeAsm.FibCard

namespace GlobalTheory.TypeAsm.FibCard
attribute [local instance] Formalism.BasicNotions.Host.cmStar
section Main2
variable {D : D7} {X : HidaSetting D}

theorem symm_fix (u : D.what₂.Word) {a : (VS D).V ≃ₗ[D.host.E] (VS D).V}
    (hfix : ∀ c, a ((F0 X u).e c) = (F0 X u).e c) : ∀ x ∈ (X.Fu u).X, a.symm x = x :=
  fun x hx => a.symm_apply_eq.2 (fix_X u hfix x hx).symm

theorem aut_iff {Λ : Submodule (𝓞 D.host.E) (VS D).V} {a : (VS D).V ≃ₗ[D.host.E] (VS D).V}
    (hga : Formalism.HermitianLatticesTheory.gmap a Λ = Λ) (y : (VS D).V) : a.symm y ∈ Λ ↔ y ∈ Λ := by
  rw [← GlobalTheory.LoopC.FrEqv.mem_gmap (Λ := Λ) a y, hga]

theorem nlam_of_same (u : D.what₂.Word) {Λ : Submodule (𝓞 D.host.E) (VS D).V} {a b : (VS D).V ≃ₗ[D.host.E] (VS D).V}
    (hia : a ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT) (hib : b ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT)
    (hga : Formalism.HermitianLatticesTheory.gmap a Λ = Λ) (hgb : Formalism.HermitianLatticesTheory.gmap b Λ = Λ)
    (hfa : ∀ c, a ((F0 X u).e c) = (F0 X u).e c) (hfb : ∀ c, b ((F0 X u).e c) = (F0 X u).e c)
    (hsame : ∀ x ∈ perpS (VS D) (X.Fu u).X, b x - a x ∈ (X.Fu u).X) :
    a⁻¹ * b ∈ NLam Λ (lf D (X.Fu u)) := by
  have happ : ∀ x, (a⁻¹ * b) x = a.symm (b x) := fun x => rfl
  refine ⟨⟨(Formalism.HermitianLatticesTheory.isom (VS D).hT).mul_mem ((Formalism.HermitianLatticesTheory.isom (VS D).hT).inv_mem hia) hib, ?_⟩,
    fun j x hx => ?_, fun x hx => ?_⟩
  · ext y
    rw [GlobalTheory.LoopC.FrEqv.mem_gmap]
    have : (a⁻¹ * b).symm y = b.symm (a y) := by
      apply (a⁻¹ * b).injective
      rw [LinearEquiv.apply_symm_apply, happ, LinearEquiv.apply_symm_apply, LinearEquiv.symm_apply_apply]
    rw [this, aut_iff hgb]
    have h2 := aut_iff hga (a y)
    rw [LinearEquiv.symm_apply_apply] at h2
    exact h2.symm
  · have hX : x ∈ (X.Fu u).X := by
      have hle : Xflag (lf D (X.Fu u)) (j + 1) ≤ (X.Fu u).X :=
        Submodule.span_mono (by rintro _ ⟨i, -, rfl⟩; exact ⟨i, rfl⟩)
      exact hle hx
    rw [happ, fix_X u hfb x hX, symm_fix u hfa x hX, sub_self]
    exact zero_mem _
  · have hp : x ∈ perpS (VS D) (X.Fu u).X := by
      simp only [orth, Submodule.mem_iInf, LinearMap.mem_ker] at hx
      exact fun y hy => hx y hy
    have e : (a⁻¹ * b) x - x = a.symm (b x - a x) := by
      rw [happ, map_sub, LinearEquiv.symm_apply_apply]
    rw [e, symm_fix u hfa _ (hsame x hp)]
    exact hsame x hp

end Main2
end GlobalTheory.TypeAsm.FibCard

namespace GlobalTheory.TypeAsm.FibCard
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem fibCardC : FibCardC := by
  intro D large₂ X Y u hStd t₀ s hs
  show (s.card : ℝ) * ((Nat.card (autLz D (X.Fu u) t₀.lam') : ℝ))⁻¹ ≤ 1
  by_cases hfin : Finite (autLz D (X.Fu u) t₀.lam')
  swap
  · have : Infinite (autLz D (X.Fu u) t₀.lam') := not_finite_iff_infinite.1 hfin
    rw [Nat.card_eq_zero_of_infinite]; simp
  have H : ∀ t : s, ∃ a : (VS D).V ≃ₗ[D.host.E] (VS D).V, a ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT ∧
      Formalism.HermitianLatticesTheory.gmap a t₀.lam' = t₀.lam' ∧ (∀ c, a ((F0 X u).e c) = (F0 X u).e c) ∧ t₀.lam' = t.1.lam' ∧
      ∃ n ∈ NLam t₀.lam (lf D (X.Fu u)), ∃ n' ∈ NLam t₀.lam' (lf D (X.Fu u)), t.1.lin = n * t₀.lin * a * n' := by
    intro t
    obtain ⟨hl, n, a, hn, ha, hga, hfa, n', hn', he⟩ :=
      GlobalTheory.T.equivFramesSameSecondLatticeFiber_proof D large₂ X Y u hStd t₀ t.1 (hs t.1 t.2).1 (hs t.1 t.2).2
    exact ⟨a, ha, hga, hfa, hl, n, hn, n', hn', he⟩
  choose A hA using H
  have Hφ : ∀ t : s, ∃ φ : WbQ D (X.Fu u) → WbQ D (X.Fu u), ∀ (x : perpS (VS D) (X.Fu u).X)
      (hx : A t x.1 ∈ perpS (VS D) (X.Fu u).X), φ (Submodule.Quotient.mk x) = Submodule.Quotient.mk ⟨A t x.1, hx⟩ :=
    fun t => ind_exists u (hA t).1 (hA t).2.2.1
  choose Φ hΦ using Hφ
  have hmem : ∀ t, Φ t ∈ autLz D (X.Fu u) t₀.lam' :=
    fun t => ⟨A t, stab_of_fix' u (hA t).1 (hA t).2.2.1, (hA t).2.1, hΦ t⟩
  let f : s → autLz D (X.Fu u) t₀.lam' := fun t => ⟨Φ t, hmem t⟩
  have hinj : Function.Injective f := by
    intro t₁ t₂ h12
    have hΦe : Φ t₁ = Φ t₂ := congrArg Subtype.val h12
    obtain ⟨hi1, hg1, hf1, hl1, n₁, hn₁, n₁', hn₁', he1⟩ := hA t₁
    obtain ⟨hi2, hg2, hf2, hl2, n₂, hn₂, n₂', hn₂', he2⟩ := hA t₂
    have hsame : ∀ x ∈ perpS (VS D) (X.Fu u).X, A t₂ x - A t₁ x ∈ (X.Fu u).X := by
      intro x hx
      have p1 := perp_pres u hi1 hf1 x hx
      have p2 := perp_pres u hi2 hf2 x hx
      have k1 := hΦ t₁ ⟨x, hx⟩ p1
      have k2 := hΦ t₂ ⟨x, hx⟩ p2
      rw [hΦe, k2] at k1
      have := (Submodule.Quotient.eq _).1 k1
      rw [Submodule.mem_comap] at this
      simpa using this
    have hm := nlam_of_same u hi1 hi2 hg1 hg2 hf1 hf2 hsame
    apply Subtype.ext
    apply GlobalTheory.TypeAsm.eqC_holds D X Y u t₁.1 t₂.1
    · rw [← (hs t₁.1 t₁.2).1, ← (hs t₂.1 t₂.2).1]
    · rw [← hl1, ← hl2]
    · refine ⟨n₂ * n₁⁻¹, ?_, n₁'⁻¹ * ((A t₁)⁻¹ * A t₂) * n₂', ?_, ?_⟩
      · rw [← (hs t₁.1 t₁.2).1]; exact Formalism.L2.SG.Pf.nlam_mul hn₂ (Formalism.L2.SG.Pf.nlam_inv hn₁)
      · rw [← hl1]; exact Formalism.L2.SG.Pf.nlam_mul (Formalism.L2.SG.Pf.nlam_mul (Formalism.L2.SG.Pf.nlam_inv hn₁') hm) hn₂'
      · rw [he1, he2]; group
  have hcard : Nat.card s ≤ Nat.card (autLz D (X.Fu u) t₀.lam') := Nat.card_le_card_of_injective f hinj
  have hs' : Nat.card s = s.card := by simp
  rw [hs'] at hcard
  rcases Nat.eq_zero_or_pos (Nat.card (autLz D (X.Fu u) t₀.lam')) with h0 | hpos
  · rw [h0]; simp
  · have hp : (0 : ℝ) < Nat.card (autLz D (X.Fu u) t₀.lam') := by exact_mod_cast hpos
    rw [← div_eq_mul_inv, div_le_one hp]; exact_mod_cast hcard

end GlobalTheory.TypeAsm.FibCard
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.GramMapFibreMeasureLocalUnitaryInvariant
section
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures
open scoped TensorProduct ENNReal

namespace GlobalTheory.LocalFibreInvariant

theorem fibre_invariant : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (v : HeightOneSpectrum (𝓞 F)), ∀ a : ℕ, ∀ (μ : Measure (Fin a → Fin n → Fv F v ⊗[F] E)) (ν : Measure (HermR (Fv F v) σ a)), μ.IsAddHaarMeasure → ν.IsAddHaarMeasure → ∀ fib : HermR (Fv F v) σ a → Measure (Fin a → Fin n → Fv F v ⊗[F] E), IsFibreFamily μ (gramR (Fv F v) σ J) Subtype.val {X | LinearIndependent (Fv F v ⊗[F] E) X} ν Set.univ fib → ∀ (S : HermR (Fv F v) σ a) (g : HA (Fv F v) σ J), (fib S).map (fun X => g • X) = fib S := by
  intro F E _ _ _ _ _ σ hCM n J hJ v a μ ν hμ hν fib hfib S g
  obtain ⟨-, -, -, h4, -, -, -, -, ha⟩ := GlobalTheory.LocalUnitaryTop.top_facts F E σ hCM n J hJ v
  obtain ⟨-, hact⟩ := ha a
  haveI := h4
  haveI : BorelSpace (Fv F v ⊗[F] E) := ⟨rfl⟩
  have hc : ∀ k : HA (Fv F v) σ J,
      Continuous (fun X : Fin a → Fin n → Fv F v ⊗[F] E => k • X) :=
    fun k => hact.comp (Continuous.prodMk continuous_const continuous_id)
  let T : (Fin a → Fin n → Fv F v ⊗[F] E) ≃ₜ (Fin a → Fin n → Fv F v ⊗[F] E) :=
    { toFun := fun X => g • X
      invFun := fun X => g⁻¹ • X
      left_inv := fun X => inv_smul_smul g X
      right_inv := fun X => smul_inv_smul g X
      continuous_toFun := hc g
      continuous_invFun := hc g⁻¹ }
  let Tm := T.toMeasurableEquiv
  have hTm : ∀ X, Tm X = g • X := fun X => rfl
  have hgram : ∀ X : Fin a → Fin n → Fv F v ⊗[F] E,
      gramR (Fv F v) σ J (g • X) = gramR (Fv F v) σ J X := by
    intro X
    funext i j
    exact hR_lin g (X i) (X j)
  have hli : ∀ (k : HA (Fv F v) σ J) (X : Fin a → Fin n → Fv F v ⊗[F] E),
      LinearIndependent (Fv F v ⊗[F] E) X → LinearIndependent (Fv F v ⊗[F] E) (k • X) := by
    intro k X hX
    have hinj : Function.Injective (lin (Fv F v) σ J k) :=
      Function.LeftInverse.injective (g := lin (Fv F v) σ J k⁻¹) (fun x => lin_inv_lin (g := k) (x := x))
    exact hX.map' (lin (Fv F v) σ J k) (LinearMap.ker_eq_bot.mpr hinj)
  have hpre : ∀ b : HermR (Fv F v) σ a,
      Tm ⁻¹' (gramR (Fv F v) σ J ⁻¹' {Subtype.val b} ∩ {X | LinearIndependent (Fv F v ⊗[F] E) X}) =
        gramR (Fv F v) σ J ⁻¹' {Subtype.val b} ∩ {X | LinearIndependent (Fv F v ⊗[F] E) X} := by
    intro b
    ext X
    simp only [Set.mem_preimage, Set.mem_inter_iff, Set.mem_singleton_iff, Set.mem_setOf_eq, hTm, hgram]
    refine and_congr_right fun _ => ⟨fun h => ?_, hli g X⟩
    have := hli g⁻¹ _ h
    rwa [inv_smul_smul] at this
  have hU : Tm ⁻¹' {X | LinearIndependent (Fv F v ⊗[F] E) X} =
      {X | LinearIndependent (Fv F v ⊗[F] E) X} := by
    ext X
    simp only [Set.mem_preimage, Set.mem_setOf_eq, hTm]
    refine ⟨fun h => ?_, hli g X⟩
    have := hli g⁻¹ _ h
    rwa [inv_smul_smul] at this
  have hμT : μ.map Tm = μ := GlobalTheory.T.localUnitaryGroup_tuple_haar_invariant F E σ hCM n J hJ v a μ hμ g
  let fib' : HermR (Fv F v) σ a → Measure (Fin a → Fin n → Fv F v ⊗[F] E) := fun b => (fib b).map Tm
  have hfib' : IsFibreFamily μ (gramR (Fv F v) σ J) Subtype.val
      {X | LinearIndependent (Fv F v ⊗[F] E) X} ν Set.univ fib' := by
    refine ⟨fun b => ?_, fun φ hφ => ?_, fun φ hφc hφs hφU => ?_⟩
    · show (fib b).map Tm _ = 0
      rw [Tm.map_apply, Set.preimage_compl, hpre]
      exact hfib.1 b
    · have e1 : ∀ b, ∫⁻ x, φ x ∂(fib' b) = ∫⁻ x, φ (Tm x) ∂(fib b) := fun b =>
        lintegral_map_equiv φ Tm (μ := fib b)
      simp only [e1]
      rw [← hfib.2.1 (fun x => φ (Tm x)) (hφ.comp Tm.measurable)]
      conv_lhs => rw [← hμT]
      rw [Tm.restrict_map, lintegral_map_equiv, hU]
    · have h3 := hfib.2.2 (φ ∘ Tm) (hφc.comp T.continuous) (hφs.comp_homeomorph T) (by
        show tsupport (φ ∘ T) ⊆ _
        rw [tsupport_comp_eq_preimage φ T]
        intro X hX
        have : Tm X ∈ {X | LinearIndependent (Fv F v ⊗[F] E) X} := hφU hX
        rw [← Set.mem_preimage, hU] at this
        exact this)
      refine ⟨fun b hb => (integrable_map_equiv Tm φ).mpr (h3.1 b hb), ?_⟩
      refine h3.2.congr fun b _ => ?_
      exact MeasureTheory.integral_map_equiv Tm φ
  have hu := GlobalTheory.LocalFibreUnique.fibre_family_unique F E σ hCM n J hJ v a μ ν hμ hν fib hfib fib' hfib'
  show (fib S).map Tm = fib S
  exact (congrFun hu S).symm

end GlobalTheory.LocalFibreInvariant
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.GramMapFibreMeasureUnitriangularInvariant
section
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures
open scoped TensorProduct ENNReal

namespace GlobalTheory.FibreUnitri
open Matrix

section Alg
variable {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]
  (σ : E →ₐ[F] E)

theorem sigR_invol (hσ : ∀ x, σ (σ x) = x) (z : R ⊗[F] E) : sigR R σ (sigR R σ z) = z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a b => simp [sigR, hσ]
  | add x y hx hy => simp only [map_add, hx, hy]

theorem gramR_comb {M a : ℕ} (J : Matrix (Fin M) (Fin M) E) (u : Matrix (Fin a) (Fin a) (R ⊗[F] E))
    (X : Fin a → Fin M → R ⊗[F] E) :
    gramR R σ J (fun b => ∑ c, u c b • X c) = (u.map (sigR R σ)).transpose * gramR R σ J X * u := by
  ext i j
  simp only [gramR, hR, Formalism.UG.hform, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply,
    Finset.sum_apply, Pi.smul_apply, smul_eq_mul, map_sum, map_mul, Finset.mul_sum, Finset.sum_mul]
  conv_lhs => enter [2, k]; rw [Finset.sum_comm]
  conv_lhs => rw [Finset.sum_comm]
  conv_lhs => enter [2, d, 2, k]; rw [Finset.sum_comm]
  conv_lhs => enter [2, d]; rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun d _ => Finset.sum_congr rfl fun c _ =>
    Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => by ring

def cgr {a : ℕ} (m A : Matrix (Fin a) (Fin a) (R ⊗[F] E)) : Matrix (Fin a) (Fin a) (R ⊗[F] E) :=
  (m.map (sigR R σ)).transpose * A * m

theorem cgr_cgr {a : ℕ} (u w A : Matrix (Fin a) (Fin a) (R ⊗[F] E)) (huw : u * w = 1) :
    cgr R σ w (cgr R σ u A) = A := by
  have e1 : (w.map (sigR R σ)).transpose * (u.map (sigR R σ)).transpose = 1 := by
    rw [← Matrix.transpose_mul, ← RingHom.mapMatrix_apply, ← RingHom.mapMatrix_apply, ← map_mul, huw,
      map_one, Matrix.transpose_one]
  unfold cgr
  calc (w.map (sigR R σ)).transpose * ((u.map (sigR R σ)).transpose * A * u) * w
      = ((w.map (sigR R σ)).transpose * (u.map (sigR R σ)).transpose) * A * (u * w) := by
        simp only [Matrix.mul_assoc]
    _ = A := by rw [e1, huw, Matrix.one_mul, Matrix.mul_one]

theorem cgr_mem (hσ : ∀ x, σ (σ x) = x) {a : ℕ} (m : Matrix (Fin a) (Fin a) (R ⊗[F] E))
    (S : HermR R σ a) : cgr R σ m (S : Matrix (Fin a) (Fin a) (R ⊗[F] E)) ∈ HermR R σ a := by
  have hS : ∀ p q, sigR R σ ((S : Matrix (Fin a) (Fin a) (R ⊗[F] E)) q p) =
      (S : Matrix (Fin a) (Fin a) (R ⊗[F] E)) p q := S.2
  intro p q
  simp only [cgr, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, map_sum, map_mul,
    sigR_invol R σ hσ, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun l _ => ?_
  rw [hS]
  ring

def cgrH (hσ : ∀ x, σ (σ x) = x) {a : ℕ} (m : Matrix (Fin a) (Fin a) (R ⊗[F] E)) (S : HermR R σ a) :
    HermR R σ a :=
  ⟨cgr R σ m S, cgr_mem R σ hσ m S⟩

theorem comb_comb {M a : ℕ} (u w : Matrix (Fin a) (Fin a) (R ⊗[F] E)) (X : Fin a → Fin M → R ⊗[F] E) :
    (fun b => ∑ c, w c b • ∑ d, u d c • X d) = fun b => ∑ d, (u * w) d b • X d := by
  funext b
  simp only [Finset.smul_sum, smul_smul, Matrix.mul_apply, Finset.sum_smul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun d _ => Finset.sum_congr rfl fun c _ => by rw [mul_comm]

theorem comb_one {M a : ℕ} (X : Fin a → Fin M → R ⊗[F] E) :
    (fun b => ∑ d, (1 : Matrix (Fin a) (Fin a) (R ⊗[F] E)) d b • X d) = X := by
  funext b
  simp [Matrix.one_apply]

theorem linIndep_comb {M a : ℕ} (m m' : Matrix (Fin a) (Fin a) (R ⊗[F] E)) (h : m' * m = 1)
    (X : Fin a → Fin M → R ⊗[F] E) (hX : LinearIndependent (R ⊗[F] E) X) :
    LinearIndependent (R ⊗[F] E) (fun b => ∑ c, m c b • X c) := by
  rw [Fintype.linearIndependent_iff] at hX ⊢
  intro g hg
  have h0 : ∑ c, (m *ᵥ g) c • X c = 0 := by
    rw [← hg]
    simp only [Matrix.mulVec, dotProduct, Finset.smul_sum, smul_smul, Finset.sum_smul]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun c _ => by rw [mul_comm]
  have hv : m *ᵥ g = 0 := funext (hX _ h0)
  have : g = m' *ᵥ (m *ᵥ g) := by rw [Matrix.mulVec_mulVec, h, Matrix.one_mulVec]
  intro i
  rw [this, hv, Matrix.mulVec_zero]
  rfl

end Alg

section Abstract

variable {V Y X : Type} [TopologicalSpace V] [MeasurableSpace V] [BorelSpace V]
  [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]

theorem isFibreFamily_transport (e : V ≃ₜ V) (r : X ≃ₜ X) {μ : Measure V} {f : V → Y} {ι : X → Y}
    {U : Set V} {ν : Measure X} {fib : X → Measure V} (hfib : IsFibreFamily μ f ι U ν Set.univ fib)
    (hμ : μ.map e.toMeasurableEquiv = μ) (hν : ν.map r.toMeasurableEquiv = ν)
    (hf : ∀ x b, f (e x) = ι (r b) ↔ f x = ι b) (hU : e ⁻¹' U = U) :
    IsFibreFamily μ f ι U ν Set.univ
      (fun b => (fib (r.symm b)).map e.toMeasurableEquiv) := by
  set em := e.toMeasurableEquiv with hem
  set rm := r.toMeasurableEquiv with hrm
  have hU' : em ⁻¹' U = U := hU
  refine ⟨fun b => ?_, fun φ hφ => ?_, fun φ hc hcs hts => ?_⟩
  · rw [MeasurableEquiv.map_apply]
    have : em ⁻¹' (f ⁻¹' {ι b} ∩ U)ᶜ = (f ⁻¹' {ι (r.symm b)} ∩ U)ᶜ := by
      ext x
      have hx : e x ∈ U ↔ x ∈ U := Set.ext_iff.1 hU x
      have hb := hf x (r.symm b)
      rw [r.apply_symm_apply] at hb
      simp only [Set.mem_preimage, Set.mem_compl_iff, Set.mem_inter_iff, Set.mem_singleton_iff]
      change ¬ (f (e x) = ι b ∧ e x ∈ U) ↔ ¬ (f x = ι (r.symm b) ∧ x ∈ U)
      rw [hb, hx]
    rw [this]
    exact hfib.1 _
  · have key : ∫⁻ x in U, φ (em x) ∂μ = ∫⁻ x in U, φ x ∂μ := by
      calc ∫⁻ x in U, φ (em x) ∂μ = ∫⁻ x, φ (em x) ∂(μ.restrict (em ⁻¹' U)) := by rw [hU']
        _ = ∫⁻ x, φ x ∂((μ.restrict (em ⁻¹' U)).map em) := (lintegral_map_equiv _ _).symm
        _ = ∫⁻ x, φ x ∂((μ.map em).restrict U) := by rw [MeasurableEquiv.restrict_map]
        _ = ∫⁻ x in U, φ x ∂μ := by rw [hμ]
    rw [← key, hfib.2.1 (fun x => φ (em x)) (hφ.comp em.measurable)]
    have h2 : ∀ c, ∫⁻ x, φ (em x) ∂(fib c) = ∫⁻ x, φ x ∂((fib (r.symm (rm c))).map em) := by
      intro c
      rw [lintegral_map_equiv]
      change _ = ∫⁻ x, φ (em x) ∂(fib (r.symm (r c)))
      rw [r.symm_apply_apply]
    simp_rw [h2]
    conv_rhs => rw [← hν]
    exact (lintegral_map_equiv (fun b => ∫⁻ x, φ x ∂((fib (r.symm b)).map em)) rm).symm
  · have hts' : tsupport (φ ∘ e) ⊆ U := by
      rw [tsupport, Function.support_comp_eq_preimage, ← e.preimage_closure, ← hU]
      exact Set.preimage_mono hts
    obtain ⟨h1, h2⟩ := hfib.2.2 (φ ∘ e) (hc.comp e.continuous) (hcs.comp_homeomorph e) hts'
    refine ⟨fun b _ => (integrable_map_equiv em φ).2 (h1 _ (Set.mem_univ _)), ?_⟩
    have e2 : (fun b => ∫ x, φ x ∂((fib (r.symm b)).map em)) =
        (fun c => ∫ x, (φ ∘ e) x ∂(fib c)) ∘ r.symm :=
      funext fun b => integral_map_equiv _ _
    rw [e2]
    have h3 : Continuous fun c => ∫ x, (φ ∘ e) x ∂(fib c) := continuousOn_univ.1 h2
    exact (h3.comp r.symm.continuous).continuousOn

end Abstract
end GlobalTheory.FibreUnitri

namespace GlobalTheory.FibreUnitri
open Matrix

theorem fibre_unitri_invariant : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (v : HeightOneSpectrum (𝓞 F)), ∀ a : ℕ, ∀ (μ : Measure (Fin a → Fin n → Fv F v ⊗[F] E)) (ν : Measure (HermR (Fv F v) σ a)), μ.IsAddHaarMeasure → ν.IsAddHaarMeasure → ∀ fib : HermR (Fv F v) σ a → Measure (Fin a → Fin n → Fv F v ⊗[F] E), IsFibreFamily μ (gramR (Fv F v) σ J) Subtype.val {X | LinearIndependent (Fv F v ⊗[F] E) X} ν Set.univ fib → ∀ (S : HermR (Fv F v) σ a) (u : Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)), (∀ i, u i i = 1) → (∀ i j, j < i → u i j = 0) → (u.map (sigR (Fv F v) σ)).transpose * (S : Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)) * u = (S : Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)) → (fib S).map (fun X b => ∑ c, u c b • X c) = fib S := by
  intro F E _ _ _ _ _ σ hE n J hJ v a μ ν hμ hν fib hfib S u hdiag htri hS
  have hσ : ∀ x, σ (σ x) = x := PI.VolStabS.sigma_invol σ hE.2.2.2
  obtain ⟨hring, -, -, hsc, -⟩ := GlobalTheory.LocalUnitaryTop.top_facts F E σ hE n J hJ v
  have : BorelSpace (Fv F v ⊗[F] E) := ⟨rfl⟩
  have : BorelSpace (HermR (Fv F v) σ a) := ⟨rfl⟩

  have hdet : u.det = 1 := by
    rw [Matrix.det_of_upperTriangular (fun i j hij => htri i j hij)]
    simp [hdiag]
  have hu : IsUnit u.det := by rw [hdet]; exact isUnit_one
  set w := u⁻¹ with hw
  have huw : u * w = 1 := Matrix.mul_nonsing_inv u hu
  have hwu : w * u = 1 := Matrix.nonsing_inv_mul u hu

  have hcont : ∀ m : Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E),
      Continuous (fun (X : Fin a → Fin n → Fv F v ⊗[F] E) b => ∑ c, m c b • X c) := by
    intro m
    refine continuous_pi fun b => continuous_finset_sum _ fun c _ => ?_
    exact (continuous_apply c).const_smul (m c b)
  let e : (Fin a → Fin n → Fv F v ⊗[F] E) ≃ₜ (Fin a → Fin n → Fv F v ⊗[F] E) :=
    { toFun := fun X b => ∑ c, u c b • X c
      invFun := fun X b => ∑ c, w c b • X c
      left_inv := fun X => by
        show (fun b => ∑ c, w c b • ∑ d, u d c • X d) = X
        rw [comb_comb, huw, comb_one]
      right_inv := fun X => by
        show (fun b => ∑ c, u c b • ∑ d, w d c • X d) = X
        rw [comb_comb, hwu, comb_one]
      continuous_toFun := hcont u
      continuous_invFun := hcont w }

  have hcontH : ∀ m : Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E), Continuous (cgrH (Fv F v) σ hσ m) := by
    intro m
    refine Continuous.subtype_mk ?_ _
    exact (continuous_const.matrix_mul continuous_subtype_val).matrix_mul continuous_const
  let r : HermR (Fv F v) σ a ≃ₜ HermR (Fv F v) σ a :=
    { toFun := cgrH (Fv F v) σ hσ u
      invFun := cgrH (Fv F v) σ hσ w
      left_inv := fun T => Subtype.ext (cgr_cgr (Fv F v) σ u w _ huw)
      right_inv := fun T => Subtype.ext (cgr_cgr (Fv F v) σ w u _ hwu)
      continuous_toFun := hcontH u
      continuous_invFun := hcontH w }
  obtain ⟨hμu, hνu⟩ := GlobalTheory.T.unitriangular_column_ops_preserve_haar_tuples_hermitian F E σ hE n J hJ v a u hdiag htri
  have hμe : μ.map e.toMeasurableEquiv = μ := hμu μ hμ
  have hνr : ν.map r.toMeasurableEquiv = ν := hνu ν hν r (fun T => rfl)
  have hf : ∀ X T, gramR (Fv F v) σ J (e X) = ((r T : HermR (Fv F v) σ a) :
      Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)) ↔
      gramR (Fv F v) σ J X = (T : Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)) := by
    intro X T
    have h1 : gramR (Fv F v) σ J (e X) = cgr (Fv F v) σ u (gramR (Fv F v) σ J X) :=
      gramR_comb (Fv F v) σ J u X
    have h2 : ((r T : HermR (Fv F v) σ a) : Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)) =
        cgr (Fv F v) σ u T := rfl
    rw [h1, h2]
    constructor
    · intro h
      have := congrArg (cgr (Fv F v) σ w) h
      rwa [cgr_cgr _ _ _ _ _ huw, cgr_cgr _ _ _ _ _ huw] at this
    · intro h
      rw [h]
  have hU : e ⁻¹' {X | LinearIndependent (Fv F v ⊗[F] E) X} =
      {X | LinearIndependent (Fv F v ⊗[F] E) X} := by
    ext X
    constructor
    · intro h
      have h' := linIndep_comb (Fv F v) w u huw _ h
      have e2 : (fun b => ∑ c, w c b • (e X) c) = X := e.left_inv X
      rw [e2] at h'
      exact h'
    · intro h
      exact linIndep_comb (Fv F v) u w hwu X h
  have hfam := isFibreFamily_transport e r hfib hμe hνr hf hU
  have heq := GlobalTheory.LocalFibreUnique.fibre_family_unique F E σ hE n J hJ v a μ ν hμ hν fib hfib _ hfam
  have hrS : r.symm S = S := by
    rw [Homeomorph.symm_apply_eq]
    exact Subtype.ext hS.symm
  have := congrFun heq S
  simp only [hrS] at this
  exact this.symm

end GlobalTheory.FibreUnitri
end

