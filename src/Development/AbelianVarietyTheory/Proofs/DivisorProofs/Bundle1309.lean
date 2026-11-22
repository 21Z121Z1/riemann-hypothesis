import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1286
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsSubquotientDetRepParInd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0855
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VecMulMapEqZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1280
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1276
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1235
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1257
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0046
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0005
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0016
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0015
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1277
import Development.AbelianVarietyTheory.Definitions.Divisors.IsSquareIntegrableIffMemL2
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1241
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1248
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1249
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0049
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnitLemmaGroup
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0162
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1237
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1278
import CompanionTheory.HarishChandraModules.LowKTypeMultiplicity.EigenspaceCyclicDensity.LowKMultOneP
import CompanionTheory.HarishChandraModules.LowKTypeMultiplicity.DiscreteSeriesCharacters.DiscreteSeriesInfinitesimalCharacter
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HolomorphicDiscreteSeries
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0048
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1203
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1208
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1253
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1256

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModulusHalfLeviAbsDet
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.AbsHalfLevi

theorem absHalf_det_div_eq_deltaHalf : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a b : ℕ) (w : Pl E) (m : GLw a w × GLw b w), absHalf w (m.1.val.det ^ b / m.2.val.det ^ a) = (GlobalTheory.SmGL.deltaHalf (w.adicCompletion E) (GlobalTheory.SmGL.Two (Fin a) (Fin b)) (GlobalTheory.SmGL.leviTwo (w.adicCompletion E) (Fin a) (Fin b) m) : ℂ) := by
  intro E _ _ _ a b w m
  rw [GlobalTheory.SmGL.deltaHalf_two, Units.val_mul]
  have e1 : m.1.val.det = ((GeneralLinearGroup.det m.1 : (w.adicCompletion E)ˣ) : w.adicCompletion E) := by
    simp [GeneralLinearGroup.val_det_apply]
  have e2 : m.2.val.det = ((GeneralLinearGroup.det m.2 : (w.adicCompletion E)ˣ) : w.adicCompletion E) := by
    simp [GeneralLinearGroup.val_det_apply]
  rw [e1, e2]
  generalize GeneralLinearGroup.det m.1 = d1
  generalize GeneralLinearGroup.det m.2 = d2
  have n1 := GlobalTheory.LGrp.BorelCompletion.nabs_completion w d1
  have n2 := GlobalTheory.LGrp.BorelCompletion.nabs_completion w d2
  have hb : ((Fintype.card (Fin b) : ℂ) / 2) = (((b : ℝ) / 2 : ℝ) : ℂ) := by simp
  have ha : (-(Fintype.card (Fin a) : ℂ) / 2) = ((-(a : ℝ) / 2 : ℝ) : ℂ) := by simp
  rw [hb, ha, GlobalTheory.SmGL.val_absPow_ofReal, GlobalTheory.SmGL.val_absPow_ofReal, n1, n2, ← Complex.ofReal_mul]
  unfold absHalf
  congr 1
  have hd1 : ((d1 : w.adicCompletion E)) ≠ 0 := d1.ne_zero
  have hd2 : ((d2 : w.adicCompletion E)) ≠ 0 := d2.ne_zero
  have hx : ((d1 : w.adicCompletion E) ^ b / (d2 : w.adicCompletion E) ^ a) ≠ 0 := by
    exact div_ne_zero (pow_ne_zero _ hd1) (pow_ne_zero _ hd2)
  have hv1 : Valued.v (d1 : w.adicCompletion E) ≠ 0 := (Valuation.ne_zero_iff _).mpr hd1
  have hv2 : Valued.v (d2 : w.adicCompletion E) ≠ 0 := (Valuation.ne_zero_iff _).mpr hd2
  have hord : ordL ((d1 : w.adicCompletion E) ^ b / (d2 : w.adicCompletion E) ^ a) =
      -((b : ℤ) * WithZero.log (Valued.v (d1 : w.adicCompletion E)) - (a : ℤ) * WithZero.log (Valued.v (d2 : w.adicCompletion E))) := by
    have hv : Valued.v ((d1 : w.adicCompletion E) ^ b / (d2 : w.adicCompletion E) ^ a) ≠ 0 := (Valuation.ne_zero_iff _).mpr hx
    unfold ordL
    rw [dif_neg hv, WithZero.toAdd_unzero_eq_log, map_div₀, map_pow, map_pow,
      WithZero.log_div (pow_ne_zero _ hv1) (pow_ne_zero _ hv2), WithZero.log_pow, WithZero.log_pow]
    simp
  rw [hord, neg_neg]
  have hq : (0 : ℝ) < (qV E w : ℝ) := by
    have : qV E w ≠ 0 := by
      unfold qV; exact (Ideal.absNorm_eq_zero_iff).not.mpr w.ne_bot
    exact_mod_cast Nat.pos_of_ne_zero this
  generalize WithZero.log (Valued.v (d1 : w.adicCompletion E)) = l1
  generalize WithZero.log (Valued.v (d2 : w.adicCompletion E)) = l2
  generalize (qV E w : ℝ) = q at hq ⊢
  rw [Real.sqrt_eq_rpow, ← Real.rpow_intCast, ← Real.rpow_intCast, ← Real.rpow_intCast,
    ← Real.rpow_mul hq.le, ← Real.rpow_mul hq.le, ← Real.rpow_mul hq.le, ← Real.rpow_add hq]
  congr 1
  push_cast
  ring

end GlobalTheory.AbsHalfLevi
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonarchimedeanNormBaseChange
section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.CM GlobalTheory.FlatDegreeCompare Matrix

namespace GlobalTheory.LocOrdUp

theorem exists_rightInverse {V K : Type} [CommRing V] [IsDomain V] [IsPrincipalIdealRing V] [Field K] [Algebra V K]
    [IsFractionRing V K] {m n : ℕ} (U : Matrix (Fin m) (Fin n) V)
    (h : ∀ (a : Fin n → V) (c : Fin m → K), c ᵥ* U.map (algebraMap V K) = (fun j => algebraMap V K (a j)) →
      ∃! b, b ᵥ* U = a) : ∃ R : Matrix (Fin n) (Fin m) V, U * R = 1 := by
  have inj : Function.Injective (Matrix.vecMulLinear U) := by
    refine LinearMap.ker_eq_bot.1 (LinearMap.ker_eq_bot'.2 fun b hb => ?_)
    exact (h 0 0 (by ext j; simp)).unique hb (Matrix.zero_vecMul _)
  have tf : Module.IsTorsionFree V ((Fin n → V) ⧸ LinearMap.range (Matrix.vecMulLinear U)) := by
    refine Module.IsTorsionFree.of_smul_eq_zero fun r y hy => ?_
    obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ y
    rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero] at hy
    obtain ⟨b, hb⟩ := hy
    rw [or_iff_not_imp_left]
    intro hr
    rw [Submodule.Quotient.mk_eq_zero]
    have hr' : algebraMap V K r ≠ 0 := fun e => hr (IsFractionRing.injective V K (e.trans (map_zero _).symm))
    obtain ⟨b', hb', -⟩ := h a ((algebraMap V K r)⁻¹ • fun i => algebraMap V K (b i)) (by
      rw [Matrix.smul_vecMul]
      ext j
      have e : ((fun i => algebraMap V K (b i)) ᵥ* U.map (algebraMap V K)) j = algebraMap V K ((b ᵥ* U) j) :=
        (RingHom.map_vecMul (algebraMap V K) U b j).symm
      have e' : b ᵥ* U = r • a := hb
      rw [Pi.smul_apply, e, e', Pi.smul_apply, smul_eq_mul, smul_eq_mul, map_mul, inv_mul_cancel_left₀ hr'])
    exact ⟨b', hb'⟩
  obtain ⟨s, hs⟩ := Module.projective_lifting_property (LinearMap.range (Matrix.vecMulLinear U)).mkQ LinearMap.id
    (Submodule.mkQ_surjective _)
  have ex : Function.Exact (Matrix.vecMulLinear U) (LinearMap.range (Matrix.vecMulLinear U)).mkQ :=
    LinearMap.exact_map_mkQ_range _
  have hs' : ∃ l, (LinearMap.range (Matrix.vecMulLinear U)).mkQ ∘ₗ l = LinearMap.id := ⟨s, hs⟩
  have hg' : ∃ l, l ∘ₗ Matrix.vecMulLinear U = LinearMap.id :=
    ((ex.split_tfae inj (Submodule.mkQ_surjective _)).out 0 1).1 hs'
  obtain ⟨g, hg⟩ := hg'
  refine ⟨LinearMap.toMatrixRight' g, ?_⟩
  apply Matrix.toLinearMapRight'.injective
  rw [Matrix.toLinearMapRight'_mul, Matrix.toLinearMapRight'_one]
  change Matrix.toLinearMapRight' (LinearMap.toMatrixRight' g) ∘ₗ Matrix.vecMulLinear U = _
  simpa using hg

theorem existsUnique_of_rightInverse {W L : Type} [CommRing W] [CommRing L] (φ : W →+* L) (hφ : Function.Injective φ)
    {m n : ℕ} {U : Matrix (Fin m) (Fin n) W} {R : Matrix (Fin n) (Fin m) W} (h : U * R = 1)
    (a : Fin n → W) (c : Fin m → L) (hc : c ᵥ* U.map φ = fun j => φ (a j)) : ∃! b, b ᵥ* U = a := by
  have h2 : U.map φ * R.map φ = 1 := by
    rw [← Matrix.map_mul, h, Matrix.map_one _ (map_zero _) (map_one _)]
  have h3 : c = fun i => φ ((a ᵥ* R) i) := by
    rw [← Matrix.vecMul_one c, ← h2, ← Matrix.vecMul_vecMul, hc]
    exact funext fun i => (RingHom.map_vecMul φ R a i).symm
  refine ⟨a ᵥ* R, funext fun j => hφ ?_, fun b hb => ?_⟩
  · rw [RingHom.map_vecMul, ← congrFun hc j, h3]; rfl
  · rw [← hb, Matrix.vecMul_vecMul, h, Matrix.vecMul_one]

theorem isLocOrd_up : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (k k' : Type) [Field k] [NumberField k] [Field k'] [NumberField k'] (i : k →+* k') (t : SAB H (Sp k)) (t' : SAB H (Sp k')) (n : SABMap t' t (spMap i)) (m : ℕ) (x : Fin m → (epsR k ⟶ t.G)) (x' : Fin m → (epsR k' ⟶ t'.G)) (𝔭 : HeightOneSpectrum (𝓞 k)) (𝔓 : HeightOneSpectrum (𝓞 k')) (ε : ℕ) (r : ℝ), Indep x → (∀ a, IsVecOver i n.φ (x a) (x' a)) → (∀ z : k, 𝔓.valuation k' (i z) = 𝔭.valuation k z ^ ε) → EigenvectorLieDegree.IsLocOrd t.G x 𝔭 r → EigenvectorLieDegree.IsLocOrd t'.G x' 𝔓 (ε * r) := by
  intro E _ _ _ H k k' _ _ _ _ i t t' n m x x' 𝔭 𝔓 ε r hx hxx hval hr
  obtain ⟨V, K, _, _, _, _, _, _, em, e₀, G, _, A, _, φ, ψ, v, u, u', M, ν, he₀, hv, hG, hφ, hψ, hxv, hu, hb, hM, hν,
    rfl⟩ := hr
  obtain ⟨W, L, _, _, _, _, _, _, f, g, em', e₂, d, hfg, hem, he₂, hd, hv', hvg⟩ :=
    GlobalTheory.T.ramification_index_valuation_compat k k' i 𝔭 𝔓 ε V K em e₀ hval he₀ hv
  have hf' : (algebraMap W L).comp f = g.comp (algebraMap V K) := RingHom.ext hfg
  obtain ⟨G₁, _, χ, h', hG₁⟩ : ∃ (G₁ : Over (Sp W)) (_ : GrpObj G₁) (χ : G₁.left ⟶ G.left),
      IsGrpPullback G₁ G (spMap f) χ ∧ IsSemiAbelian G₁ :=
    ⟨_, _, _, isGrpPullback_pullback G (spMap f), IsSemiAbelian.pullback _ G hG⟩
  obtain ⟨A₁, _, ω, hω⟩ : ∃ (A₁ : Over (Sp L)) (_ : GrpObj A₁) (ω : A₁.left ⟶ A.left),
      IsGrpPullback A₁ A (spMap g) ω := ⟨_, _, _, isGrpPullback_pullback A (spMap g)⟩
  have := hG.comm
  have := hG₁.comm
  have := hG.smooth
  have := hG₁.smooth
  have := PolPull.isCommMonObj_of_isGrpPullback hφ
  have := PolPull.isCommMonObj_of_isGrpPullback hω
  have n' : IsGrpPullback A₁ G (spMap (algebraMap W L) ≫ spMap f) (ω ≫ φ) :=
    (hω.comp hφ).congr (by rw [spMap_comp_spMap, spMap_comp_spMap, hf']) rfl
  have w : (ω ≫ φ) ≫ G.hom = (A₁.hom ≫ spMap (algebraMap W L)) ≫ spMap f :=
    n'.1.w.trans (Category.assoc _ _ _).symm
  have q := h'.1.lift_fst _ _ w
  have hφ₁ := h'.cancel (n'.congr rfl q.symm) (h'.1.lift_snd _ _ w)
  have n'' : IsGrpPullback A₁ t.G (spMap em' ≫ spMap i) (ω ≫ ψ) :=
    (hω.comp hψ).congr (by rw [spMap_comp_spMap, spMap_comp_spMap, hem]) rfl
  have w' : (ω ≫ ψ) ≫ t.G.hom = (A₁.hom ≫ spMap em') ≫ spMap i :=
    n''.1.w.trans (Category.assoc _ _ _).symm
  have q' := n.cart.1.lift_fst _ _ w'
  have hψ₁ := n.cart.cancel (n''.congr rfl q'.symm) (n.cart.1.lift_snd _ _ w')
  have tv : ∀ a, IsTangent (v a) := fun a => (hxv a).isTangent hψ (hx.1 a)
  obtain ⟨N, e, e', -, he, he', h, -⟩ := exists_frame hG hφ tv
  choose e₁ h₁ _ using fun j => existsUnique_isVecOver h'.1 (e j)
  have he₁ := Chart.isLieBasis_baseChange f h' he h₁
  choose e₁' h₂ _ using fun j => existsUnique_isVecOver hω.1 (e' j)
  have h₃ := fun j => EllComp.isVecOver_cancel h'.1 hφ₁.1 (h₁ j)
    (by rw [q, hf']; exact EllComp.isVecOver_comp (h j) (h₂ j))
  have he₁' := Chart.isLieBasis_baseChange _ hφ₁ he₁ h₃
  choose u₁ k₁ _ using fun j => existsUnique_isVecOver h'.1 (u j)
  choose u₁' k₂ _ using fun j => existsUnique_isVecOver hω.1 (u' j)
  have k₃ := fun j => EllComp.isVecOver_cancel h'.1 hφ₁.1 (k₁ j)
    (by rw [q, hf']; exact EllComp.isVecOver_comp (hu j).2.1 (k₂ j))
  choose v₁ l₂ _ using fun j => existsUnique_isVecOver hω.1 (v j)
  have l₃ := fun j => EllComp.isVecOver_cancel n.cart.1 hψ₁.1 (hxx j)
    (by rw [q', hem]; exact EllComp.isVecOver_comp (hxv j) (l₂ j))
  choose U₀ hU₀ _ using fun a => he.2 _ (hu a).1
  let U : Matrix (Fin m) (Fin N) V := U₀
  have hU : ∀ a, IsLieComb (U a) e (u a) := hU₀
  have hU' : ∀ a, IsLieComb (U.map (algebraMap V K) a) e' (u' a) := fun a =>
    (lieComb_baseChange _ _ _ G A φ hφ N e (u a) (U a) e' (u' a) h (hU a)).1 (hu a).2.1
  have hU₁ : ∀ a, IsLieComb (U.map f a) e₁ (u₁ a) := fun a =>
    (lieComb_baseChange _ _ _ G G₁ χ h' N e (u a) (U a) e₁ (u₁ a) h₁ (hU a)).1 (k₁ a)
  have hU₁' : ∀ a, IsLieComb ((U.map f).map (algebraMap W L) a) e₁' (u₁' a) := fun a =>
    (lieComb_baseChange _ _ _ G₁ A₁ _ hφ₁ N e₁ (u₁ a) (U.map f a) e₁' (u₁' a) h₃ (hU₁ a)).1 (k₃ a)
  choose C₀ hC₀ using fun a => (hu a).2.2
  let C : Matrix (Fin m) (Fin m) K := C₀
  have hC : ∀ a, IsLieComb (C a) v (u' a) := hC₀
  have hM₁ : ∀ a, IsLieComb (M.map g a) u₁' (v₁ a) := fun a =>
    (lieComb_baseChange _ _ g A A₁ ω hω m u' (v a) (M a) u₁' (v₁ a) k₂ (hM a)).1 (l₂ a)
  have tu₁ : ∀ a, IsTangent (u₁ a) := fun a => (k₁ a).isTangent h' (hu a).1
  have tu₁' : ∀ a, IsTangent (u₁' a) := fun a => (k₃ a).isTangent hφ₁ (tu₁ a)
  obtain ⟨R, hR⟩ := exists_rightInverse (K := K) U fun a c hc => by
    obtain ⟨a₁, a₂, -⟩ := LieComb.lieComb_algebra _ G N e he.1
    obtain ⟨y, hy⟩ := (a₁ a).exists
    obtain ⟨z, hz, -⟩ := existsUnique_isVecOver hφ.1 y
    have hz' := (lieComb_baseChange _ _ _ G A φ hφ N e y a e' z h hy).1 hz
    rw [← hc, ← comb_comb he'.1 hU', comb_comb tv hC] at hz'
    refine (existsUnique_congr fun b => ?_).1 (hb y z (a₂ _ _ hy) hz ⟨_, hz'⟩)
    rw [comb_comb he.1 hU]
    exact ⟨fun hb => (Indep.of_basis he).2 _ _ y hb hy, fun hb => hb ▸ hy⟩
  have hR₁ : U.map f * R.map f = 1 := by
    rw [← Matrix.map_mul, hR, Matrix.map_one _ (map_zero _) (map_one _)]
  refine ⟨W, L, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, em', _,
    G₁, inferInstance, A₁, inferInstance, _, _, v₁, u₁, u₁', M.map g, d * ν, he₂, hv', hG₁, hφ₁, hψ₁, l₃,
    fun a => ⟨tu₁ a, k₃ a, _, (lieComb_baseChange _ _ g A A₁ ω hω m v (u' a) (C a) v₁ (u₁' a) l₂ (hC a)).1 (k₂ a)⟩,
    fun y z hy hz ⟨c, hc⟩ => ?_, hM₁, ?_, ?_⟩
  · obtain ⟨a, ha, -⟩ := he₁.2 y hy
    have hz' := (lieComb_baseChange _ _ _ G₁ A₁ _ hφ₁ N e₁ y a e₁' z h₃ ha).1 hz
    rw [comb_comb tu₁' hM₁, comb_comb he₁'.1 hU₁'] at hc
    refine (existsUnique_congr fun b => ?_).1 (existsUnique_of_rightInverse (algebraMap W L)
      (IsFractionRing.injective W L) hR₁ a _ ((Indep.of_basis he₁').2 _ _ z hc hz'))
    rw [comb_comb he₁.1 hU₁]
    exact ⟨fun hb => hb ▸ ha, fun hb => (Indep.of_basis he₁).2 _ _ y hb ha⟩
  · have : (M.map g).det = g M.det := (RingHom.map_det g M).symm
    rw [this, hvg, hν, ← WithZero.exp_nsmul]
    congr 1
    simp
  · have a₁ : (e₀ : ℝ) ≠ 0 := Nat.cast_ne_zero.2 he₀.ne'
    have a₃ := congrArg (Nat.cast : ℕ → ℝ) hd
    have a₂ : (e₂ : ℝ) ≠ 0 := Nat.cast_ne_zero.2 he₂.ne'
    push_cast at a₃ ⊢
    rw [← mul_div_assoc, div_eq_div_iff a₁ a₂]
    linear_combination (ν : ℝ) * a₃

end GlobalTheory.LocOrdUp
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormComplexEmbeddingEntryDefiniteUnitaryRationalStatement
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.norm_complexEmbedding_entry_definiteUnitaryRational_le_one : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (γ : UE E n) (τ : E →+* ℂ) (i j : Fin n), ‖τ (γ.1.val i j)‖ ≤ 1 := by
  first | exact @GlobalTheory.BCT.SuppFin.norm_emb_entry_le_one | exact GlobalTheory.BCT.SuppFin.norm_emb_entry_le_one | (intros; apply GlobalTheory.BCT.SuppFin.norm_emb_entry_le_one <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormEmbeddingEntryDefiniteUnitaryRationalPointLe
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.BCT.FinPart

theorem norm_emb_entry_le_one (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (γ : UE E n)
    (τ : E →+* ℂ) (i j : Fin n) : ‖τ ((γ : GL (Fin n) E).val i j)‖ ≤ 1 := by
  set M : Matrix (Fin n) (Fin n) E := (γ : GL (Fin n) E).val with hM
  have h : Formalism.UG.cT (IsCMField.complexConj E).toRingEquiv.toRingHom M * 1 * M = 1 := γ.2
  rw [Matrix.mul_one] at h
  have hjj : ∑ k, IsCMField.complexConj E (M k j) * M k j = 1 := by
    have := congrFun₂ h j j
    simpa [Formalism.UG.cT, Matrix.mul_apply] using this
  have hτ : ∑ k, ((Complex.normSq (τ (M k j)) : ℝ) : ℂ) = 1 := by
    have := congrArg τ hjj
    rw [map_sum, map_one] at this
    rw [← this]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_mul, IsCMField.complexEmbedding_complexConj, Complex.normSq_eq_conj_mul_self]
  have hR : ∑ k, Complex.normSq (τ (M k j)) = 1 := by exact_mod_cast hτ
  have hle : Complex.normSq (τ (M i j)) ≤ 1 := by
    rw [← hR]
    exact Finset.single_le_sum (f := fun k => Complex.normSq (τ (M k j))) (fun k _ => Complex.normSq_nonneg _)
      (Finset.mem_univ i)
  have hsq : ‖τ (M i j)‖ ^ 2 ≤ 1 := by rw [Complex.sq_norm]; exact hle
  exact (pow_le_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).1 hsq

end GlobalTheory.BCT.FinPart
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NotKltAtSubOfNotLcAtStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_not_kltAt_sub_of_not_lcAt : ∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] [GlobalTheory.IsNormalScheme X] (p : X ⟶ Sp ℂ) (n : ℕ), IsProjOver p → topologicalKrullDim X = n → ∀ (Δ D : X → ℚ) (x : X), IsQCart D → KltAt p n Δ x → ¬ LcAt p n (Δ + D) x → ∃ δ₀ : ℚ, 0 < δ₀ ∧ ∀ δ : ℚ, 0 ≤ δ → δ ≤ δ₀ → ¬ KltAt p n (Δ + (1 - δ) • D) x := by
  first | exact @GlobalTheory.PairStep.not_kltAt_sub_of_not_lcAt | exact GlobalTheory.PairStep.not_kltAt_sub_of_not_lcAt | (intros; apply GlobalTheory.PairStep.not_kltAt_sub_of_not_lcAt <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NotLcAtAddOfIsNkltCentreStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.not_lcAt_add_of_isNkltCentre' : ∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] [GlobalTheory.IsNormalScheme X] (p : X ⟶ Sp ℂ) (n : ℕ), IsProjOver p → topologicalKrullDim X = n → ∀ (Γ A : X → ℚ) (z x : X), IsNkltCentre p n Γ z → IsQCart A → ¬ Off A z → z ⤳ x → ¬ LcAt p n (Γ + A) x := by
  first | exact @GlobalTheory.PairStep.not_lcAt_add_of_isNkltCentre | exact GlobalTheory.PairStep.not_lcAt_add_of_isNkltCentre | (intros; apply GlobalTheory.PairStep.not_lcAt_add_of_isNkltCentre <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.OppositeIsotropicFlagStabilizerNotRaiseWeight
section
open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut
open scoped TensorProduct
open GlobalTheory.Mem.UnipCocompact

namespace GlobalTheory.UAut.OppFlagWeight

theorem weight_of_triangular {A : Type} [CommRing A] {n r : ℕ} {X Y : Matrix (Fin n) (Fin r) A}
    {L T : Matrix (Fin r) (Fin n) A} {x : Matrix (Fin n) (Fin n) A} {B B' : Matrix (Fin r) (Fin r) A}
    {d : Fin r → ℕ} {M : ℕ} (hd : ∀ j, d j < M)
    (hLX : L * X = 1) (hTY : T * Y = 1) (hLY : L * Y = 0)
    (hB : x * Y = Y * B) (hB' : L * x = B' * L) (tB : ∀ i j, d j < d i → B i j = 0) (tB' : ∀ i j, d i < d j → B' i j = 0)
    (ε : Option (Fin r ⊕ Fin r) → Matrix (Fin n) (Fin n) A)
    (e0 : ε none = 1 - (X * L + Y * T)) (e1 : ∀ j, ε (some (.inl j)) = X * single j j (1 : A) * L)
    (e2 : ∀ j, ε (some (.inr j)) = Y * single j j (1 : A) * T) :
    ∀ a b, wt d M b < wt d M a → ε a * x * ε b = 0 := by
  have k0 : ε none * Y = 0 := by
    rw [e0, Matrix.sub_mul, Matrix.add_mul, Matrix.mul_assoc, Matrix.mul_assoc, hLY, hTY]; simp
  have k1 : L * ε none = 0 := by
    rw [e0, Matrix.mul_sub, Matrix.mul_add, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hLY, hLX]; simp
  have k2 : ∀ (m : Matrix (Fin n) (Fin n) A) j, m * Y = 0 → m * x * ε (some (.inr j)) = 0 := fun m j h => by
    rw [e2, Matrix.mul_assoc Y, ← Matrix.mul_assoc, Matrix.mul_assoc m, hB, ← Matrix.mul_assoc m, h]; simp
  rintro (_ | i | i) (_ | j | j) hab
  · simp [wt] at hab
  · have := hd j; simp [wt] at hab; omega
  · exact k2 _ j k0
  · rw [e1, Matrix.mul_assoc _ L, hB', ← Matrix.mul_assoc, Matrix.mul_assoc _ L, k1, Matrix.mul_zero]
  · rw [e1, e1, sandwich_eq_zero hLX, hB', Matrix.mul_assoc, hLX, Matrix.mul_one]
    exact tB' i j (by simp [wt] at hab; omega)
  · exact k2 _ j (by rw [e1, Matrix.mul_assoc, hLY, Matrix.mul_zero])
  · have := hd i; simp [wt] at hab; omega
  · have := hd i; have := hd j; simp [wt] at hab; omega
  · rw [e2, e2, sandwich_eq_zero hTY, Matrix.mul_assoc, hB, ← Matrix.mul_assoc, hTY, Matrix.one_mul]
    exact tB i j (by simp [wt] at hab; omega)

theorem not_raise_of_mem_parFlag : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (r : ℕ) (X Y : Matrix (Fin n) (Fin r) E) (d : Fin r → ℕ) (M : ℕ), (∀ j, d j < M) → Formalism.UG.cT (σ : E →+* E) X * J * X = 0 → Formalism.UG.cT (σ : E →+* E) Y * J * Y = 0 → Formalism.UG.cT (σ : E →+* E) X * J * Y = 1 → ∀ p ∈ parFlag σ J Y d, ∀ a b, wt d M b < wt d M a → fam (adjA σ J) (idemA X (Formalism.UG.cT (σ : E →+* E) Y * J)) a * (matHom (AF F) σ J p).1 * fam (adjA σ J) (idemA X (Formalism.UG.cT (σ : E →+* E) Y * J)) b = 0 := by
  intro F E _ _ _ _ _ σ h n J hJ r X Y d M hd _ hY hXY p hp
  obtain ⟨⟨B, hB, eB⟩, B', hB', eB'⟩ := hp
  have cc : ∀ {m p : Type} (A : Matrix m p E), Formalism.UG.cT (σ : E →+* E) (Formalism.UG.cT (σ : E →+* E) A) = A := fun A =>
    Matrix.ext fun i j => sigma_sigma h _
  have hYX : Formalism.UG.cT (σ : E →+* E) Y * J * X = 1 := by
    have := congrArg (Formalism.UG.cT (σ : E →+* E)) hXY
    rwa [Formalism.UG.cT_mul, Formalism.UG.cT_mul, cc, cT_form hJ, Formalism.UG.cT_one, ← Matrix.mul_assoc] at this
  have f := form_mul_of_mul_cols eB'
  rw [inv_inv] at f
  set φ := inclR (F := F) (E := E) (AF F) with hφ
  have adj : ∀ Z : Matrix (Fin r) (Fin r) E, adjA σ J ((X * Z * (Formalism.UG.cT (σ : E →+* E) Y * J)).map φ) =
      Y.map φ * (Formalism.UG.cT (σ : E →+* E) Z).map φ * (Formalism.UG.cT (σ : E →+* E) X * J).map φ := fun Z => by
    rw [adjA_map, ← Matrix.map_mul, ← Matrix.map_mul, Formalism.UG.cT_mul, Formalism.UG.cT_mul, Formalism.UG.cT_mul, cc, cT_form hJ]
    congr 1
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc J⁻¹, Matrix.nonsing_inv_mul _ (det_isUnit hJ), Matrix.one_mul]
  refine weight_of_triangular (X := X.map φ) (Y := Y.map φ) (L := (Formalism.UG.cT (σ : E →+* E) Y * J).map φ)
    (T := (Formalism.UG.cT (σ : E →+* E) X * J).map φ) hd ?_ ?_ ?_ eB f (fun i j hij => hB hij) (fun i j hij => ?_) _ ?_
    (fun j => idemA_eq _ _ j) (fun j => ?_)
  · rw [← Matrix.map_mul, hYX, Matrix.map_one _ (map_zero _) (map_one _)]
  · rw [← Matrix.map_mul, hXY, Matrix.map_one _ (map_zero _) (map_one _)]
  · rw [← Matrix.map_mul, hY, Matrix.map_zero _ (map_zero _)]
  · show sigR (AF F) σ (B' j i) = 0
    rw [hB' hij, map_zero]
  · have := adj 1
    rw [Matrix.mul_one, Formalism.UG.cT_one, Matrix.map_one _ (map_zero _) (map_one _), Matrix.mul_one] at this
    simp only [fam, Option.elim, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr]
    rw [← map_sum, sum_idemA, this, Matrix.map_mul]
  · refine (adj (single j j 1)).trans ?_
    congr 2
    ext a b
    by_cases h1 : j = a <;> by_cases h2 : j = b <;> simp [Formalism.UG.cT, single, h1, h2]

end GlobalTheory.UAut.OppFlagWeight
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.OrbitalIntegralEqClosedSubgroupConjAverageStatement
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.orbitalIntegral_eq_closedSubgroup_conjAverage : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (K P : Subgroup G), IsOpen (K : Set G) → IsCompact (K : Set G) → IsClosed (P : Set G) → (∀ g : G, ∃ p ∈ P, ∃ k ∈ K, g = p * k) → ∀ (δ : G) (hδ : δ ∈ P), twCent (MonoidHom.id G) δ ≤ P → ∀ f : G → ℂ, (∃ K' : Subgroup G, IsOpen (K' : Set G) ∧ IsHecke K' f) → twOrb (MonoidHom.id G) K δ f = twOrb (MonoidHom.id P) (K.subgroupOf P) ⟨δ, hδ⟩ (fun p => GlobalTheory.LeviDesc.cavg K f (p : G)) := by
  first | exact @GlobalTheory.IwRed.twOrb_sub | exact GlobalTheory.IwRed.twOrb_sub | (intros; apply GlobalTheory.IwRed.twOrb_sub <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.OrbitalIntegralEqWeightedLatticeOrbitCountStatement
section
open NumberField GlobalTheory.UnitaryBC IsDedekindDomain Matrix Polynomial GlobalTheory.CuspRep Formalism.UG GlobalTheory.BCT GlobalTheory.KapLat GlobalTheory.KapOrb
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.orbitalIntegral_eq_weighted_lattice_orbit_count : ∀ {G : Type} [Group G] [TopologicalSpace G] (Kg : Subgroup G) (δ : G) (f : G → ℂ) {O A : Type} [CommRing O] [CommRing A] [Algebra O A] (Tb : Subgroup Aˣ) (X : Set (Submodule O A)) (M : G → Submodule O A) (τ : G → Aˣ), (∀ g k : G, k ∈ Kg → M (g * k) = M g) → (∀ g g' : G, M g = M g' → g⁻¹ * g' ∈ Kg) → (∀ L ∈ X, ∃ g, M g = L) → (∀ h ∈ twCent (MonoidHom.id G) δ, τ h ∈ Tb ∧ ∀ g : G, M (h * g) = GlobalTheory.UnitLemma.mulLat O (τ h : A) (M g)) → (∀ s ∈ Tb, ∃ h ∈ twCent (MonoidHom.id G) δ, τ h = s) → (∀ g : G, avg (fun k : Kg => f ((g * k)⁻¹ * δ * (MonoidHom.id G) (g * k))) = if M g ∈ X then 1 else 0) → (∀ g : G, (twCent (MonoidHom.id G) δ ⊓ Kg.map (MulAut.conj g).toMonoidHom).relIndex (cptPart (twCent (MonoidHom.id G) δ)) = (GlobalTheory.UnitLemma.stabLat O (M g) ⊓ Tb).relIndex (GlobalTheory.UnitLemma.intUnits O A ⊓ Tb)) → twOrb (MonoidHom.id G) Kg δ f = ((GlobalTheory.UnitLemma.orbSum O Tb X fun _ => 1 : ℚ) : ℂ) := by
  first | exact @GlobalTheory.OrbReindex.twOrb_eq_orbSum | exact GlobalTheory.OrbReindex.twOrb_eq_orbSum | (intros; apply GlobalTheory.OrbReindex.twOrb_eq_orbSum <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.OrbitalIntegralIndicatorEqFinsumRelIndexStatement
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.UnitLemma GlobalTheory.InertUnitOrb
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.orbitalIntegral_indicator_eq_finsum_relIndex : ∀ (G : Type) [Group G] [TopologicalSpace G] (K : Subgroup G) (γ : G), twOrb (MonoidHom.id G) K γ ((K : Set G).indicator 1) = ∑ᶠ q : DoubleCoset.Quotient (twCent (MonoidHom.id G) γ : Set G) (K : Set G), if (Quotient.out q)⁻¹ * γ * Quotient.out q ∈ K then (((twCent (MonoidHom.id G) γ ⊓ K.map (MulAut.conj (Quotient.out q)).toMonoidHom).relIndex (cptPart (twCent (MonoidHom.id G) γ)) : ℕ) : ℂ) else 0 := by
  first | exact @GlobalTheory.OrbIndUnit.twOrb_id_indicator | exact GlobalTheory.OrbIndUnit.twOrb_id_indicator | (intros; apply GlobalTheory.OrbIndUnit.twOrb_id_indicator <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PMinusAnnihilatesLowestKTypeHolomorphicChamberStatement
section
open Matrix GlobalTheory.HolDS
open Formalism.REAL (GlRel IsUnitary IsWeight KHighest root Jm inG)
open Formalism.QuantumDeterminants (lowK IsHCParam)
open Formalism.MainNotions.S (IsURepOn IsIrredOn UJset IsKFin IsKTypeOf IsKStableOn IsDS lowKSub vNormSq)
open CompanionTheory.D.DSIC (KRel KUnit KStab IsSmMod)
open CompanionTheory.D.LK (IsKMod IsMin)
open scoped InnerProductSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pMinus_annihilates_lowestKType_holomorphicChamber : ∀ (n : ℕ) (ε : Fin n → Bool) (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] (E : Fin n → Fin n → Module.End ℂ V) (lam : Fin n → ℝ), GlRel E → IsUnitary ε E → StrictAnti lam → IsHolChamber ε lam → IsMin ε E lam → ∀ L : Submodule ℂ V, FiniteDimensional ℂ L → KStab ε E L → (∀ ν : Fin n → ℝ, ∀ x ∈ L, x ≠ 0 → KHighest ε E ν x → ν = lowK ε lam) → ∀ a b : Fin n, ε a = true → ε b = false → ∀ x ∈ L, E b a x = 0 := by
  first | exact @GlobalTheory.HolDS.pMinus_kills_lowest | exact GlobalTheory.HolDS.pMinus_kills_lowest | (intros; apply GlobalTheory.HolDS.pMinus_kills_lowest <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ParabolicBlockDecompositionEmbed
section
open ValuativeRel Matrix MeasureTheory
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.Whittaker GlobalTheory.LocLanglands GlobalTheory.GamMul DiscreteGroups.sglob.LConv

namespace GlobalTheory.GamMul.BlockId

theorem dg_dg {R : Type} [CommRing R] (n m o p : ℕ) (hm : m ≤ n) (hp : o + p ≤ m) (g : GL (Fin p) R) :
    dg n 0 (dg m o g) = dg n o g := by
  apply Units.ext
  obtain ⟨-, h2, -⟩ := GlobalTheory.T.block_matrix_values_unipotent_diagonal R n 0 0 m m
  obtain ⟨-, h2', -⟩ := GlobalTheory.T.block_matrix_values_unipotent_diagonal R m o o p p
  obtain ⟨-, h2'', -⟩ := GlobalTheory.T.block_matrix_values_unipotent_diagonal R n o o p p
  rw [(h2 _ (by omega)).1, (h2' g hp).1, (h2'' g (by omega)).1]
  obtain ⟨hadd, hneg, -, -, -, -, -, -⟩ := put_lin_pack R n 0 0 m m
  have hsub : ∀ X Y : Matrix (Fin m) (Fin m) R, put n 0 0 (X - Y) = put n 0 0 X - put n 0 0 Y := by
    intro X Y; rw [sub_eq_add_neg, hadd, hneg, ← sub_eq_add_neg]
  have hn1 := (PutNest.main R n m 0 0 o o p p 0 0).1
  have he1 : put n 0 0 (1 : Matrix (Fin m) (Fin m) R) = eye R n 0 0 m := rfl
  have he2 : put n 0 0 (eye R m o o p) = eye R n o o p := by
    simp only [eye]; rw [hn1 _ hp hp, zero_add]
  rw [hadd, hsub, he1, he2, hn1 _ hp hp, zero_add]
  abel

theorem dg_uni {R : Type} [CommRing R] (n m o₁ o₂ p q : ℕ) (hm : m ≤ n) (h1 : o₁ + p ≤ m) (h2 : o₂ + q ≤ m)
    (hd : o₁ + p ≤ o₂ ∨ o₂ + q ≤ o₁) (X : Matrix (Fin p) (Fin q) R) :
    dg n 0 (uni m o₁ o₂ X) = uni n o₁ o₂ X := by
  apply Units.ext
  obtain ⟨-, h2d, -⟩ := GlobalTheory.T.block_matrix_values_unipotent_diagonal R n 0 0 m m
  obtain ⟨h1u, -, -⟩ := GlobalTheory.T.block_matrix_values_unipotent_diagonal R m o₁ o₂ p q
  obtain ⟨h1u', -, -⟩ := GlobalTheory.T.block_matrix_values_unipotent_diagonal R n o₁ o₂ p q
  rw [(h2d _ (by omega)).1, (h1u X hd).1, (h1u' X hd).1]
  obtain ⟨hadd, -, -, -, -, -, -, -⟩ := put_lin_pack R n 0 0 m m
  have hn1 := (PutNest.main R n m 0 0 o₁ o₂ p q 0 0).1
  have he1 : put n 0 0 (1 : Matrix (Fin m) (Fin m) R) = eye R n 0 0 m := rfl
  rw [hadd, hn1 _ h1 h2, he1, zero_add, zero_add]
  abel

theorem main : ∀ (R : Type) [CommRing R] (n m m₁ m₂ : ℕ), m₁ + m₂ = m → m ≤ n → ∀ (a : GL (Fin m₁) R) (b : GL (Fin m₂) R) (x : Matrix (Fin m₂) (Fin m₁) R), dg n 0 (dg m 0 a * dg m m₁ b * uni m m₁ 0 x) = dg n 0 a * uni n m₁ 0 (b.val * x) * dg n m₁ b := by
  intro R _ n m m₁ m₂ hm hmn a b x
  have hmul := ((GlobalTheory.T.block_unipotent_det_one_and_trivial R n 0 0 m m).2.2.2.2.1 (by omega)).1
  rw [hmul, hmul, dg_dg n m 0 m₁ hmn (by omega), dg_dg n m m₁ m₂ hmn (by omega),
    dg_uni n m m₁ 0 m₂ m₁ hmn (by omega) (by omega) (Or.inr (by omega))]
  have hc := ((GlobalTheory.T.diagonal_block_conj_unipotent R n m₁ 0 m₂ m₁ (Or.inr (by omega)) (by omega) (by omega)).1 b x)
  rw [mul_assoc, hc, ← mul_assoc]

end GlobalTheory.GamMul.BlockId
end

