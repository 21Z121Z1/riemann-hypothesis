import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1326
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1647
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0176
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0120
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0171
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsUniqueFramedPointMoveUniversalTriple
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FramedPointMoveCalculus
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2127
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1595
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1697
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1384
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1347
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1991
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1359
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1527
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1409
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1572
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0004
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.AuxiliaryPrimeNeTypePrime
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0062
import Formalism.LocalRingCardinality.CoeNeZeroOfNotMem
import Formalism.LocalToGlobal.ProjectiveLattices.HostSize
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0223
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2113
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatTranslateOfPrime
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2087
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2116
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.DcOpCommOfCommute
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2114
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2086
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1183
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.SingleIndexPlacesAreTwisted
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1078
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsModTopEv
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2115

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GeoActMemCusp
section
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.GeoLevel

section Free

open NumberField AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
  ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj GlobalTheory.LevelCusp
open GlobalTheory.Dict (castFr)
open GlobalTheory.FrameNorm (IsUnitFr)
open scoped Matrix

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H} {Xo : Moduli Dw l} {c : Coeff l} {σ : c.F →+* ℂ} {r : ℕ}

theorem isMatch_div {X X' : Data E r} {a b : GL (Fin r) E} (ha : IsMatch X X' a) (hb : IsMatch X X' b) :
    IsMatch X' X' (b * a⁻¹) := by
  have hri : ∀ v, (a : Matrix (Fin r) (Fin r) E) *ᵥ (((a⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) *ᵥ v) = v :=
    fun v => by rw [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]
  refine ⟨rfl, rfl, rfl, fun u v => ?_, fun v => ?_⟩
  · rw [Units.val_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hb.iso, ← ha.iso, hri, hri]
  · rw [Units.val_mul, ← Matrix.mulVec_mulVec, ← hb.lat, ha.lat, hri]

omit [NumberField E] [IsCMField E] in
theorem lact_div {Ψ : Finset (E →+* ℂ)} (a b : GL (Fin r) E) (z : Frame Ψ r) :
    lact (b * a⁻¹) (castFr rfl (lact a z)) = lact b z := by
  funext τ
  change ((b * a⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E).map τ.1 *
    ((a : Matrix (Fin r) (Fin r) E).map τ.1 * mat z τ) = (b : Matrix (Fin r) (Fin r) E).map τ.1 * mat z τ
  rw [← Matrix.mul_assoc, ← Matrix.map_mul, ← Units.val_mul, inv_mul_cancel_right]

variable {U : Formalism.L2.PjFree.Unf Xo c σ r} {g : ℕ} {e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ)}
  {F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (fun j => Formalism.L2.PjFree.relab c σ (e j).1)}
  {ik : U.Comp → Fin F.n} {φ : ∀ k, (F.Di (ik k)).La ≃ₗ[𝓞 E] (U.X k).Λ}

theorem comp_unique (hσ : Formalism.L2.PjFree.GoodEmb c σ) (hU : Formalism.L2.PjFree.IsUnf U) (hpq : 1 ≤ Dw.p + Dw.q)
    (hA : l.A = 1) (hP : Pinned U e F ik φ) {k k₁ k₂ : U.Comp} {δ₁ δ₂ : GL (Fin r) E}
    (h₁ : IsMatch (U.X k) (U.X k₁) δ₁) (h₂ : IsMatch (U.X k) (U.X k₂) δ₂) {γ : Dw.La →ₗ[𝓞 E] Dw.La}
    {ρ : Xo.X ⟶ Xo.X} {ν : SABMap Xo.univ.t Xo.univ.t ρ} (hm : IsLevMove ρ ν γ LinearMap.id)
    (m₁ : MarkRel l (φ k) (φ k₁) (F.t (ik k)) (F.t (ik k₁)) γ δ₁)
    (m₂ : MarkRel l (φ k) (φ k₂) (F.t (ik k)) (F.t (ik k₂)) γ δ₂) (x : (U.X k).dom) : k₁ = k₂ := by
  obtain ⟨y', hy⟩ := (GlobalTheory.exists_unique_frMove E H Dw l Xo c ρ ν hm.1 _ (U.un k x)).1
  obtain ⟨a₁, b₁⟩ := GlobalTheory.T.moveMatch_of_markRel_of_isLevMove E H Dw l Xo c σ r U g e F ik φ hσ hpq hA hP k k₁ δ₁ h₁ γ ρ ν m₁ hm x y' hy
  obtain ⟨a₂, b₂⟩ := GlobalTheory.T.moveMatch_of_markRel_of_isLevMove E H Dw l Xo c σ r U g e F ik φ hσ hpq hA hP k k₂ δ₂ h₂ γ ρ ν m₂ hm x y' hy
  obtain ⟨t₀, ht⟩ := exists_frBor_gen _ _ (a₂.symm.trans a₁) (b₂.symm.trans b₁)
  obtain ⟨_, -, _, -, he⟩ := (hU.2.2.2.1 k₁ k₂ _ _).1 ⟨_, ht⟩
  exact (congrArg Sigma.fst he).symm

theorem exists_const (hσ : Formalism.L2.PjFree.GoodEmb c σ) (hU : Formalism.L2.PjFree.IsUnf U) (hpq : 1 ≤ Dw.p + Dw.q)
    (hA : l.A = 1) (hP : Pinned U e F ik φ)
    (hex : ∀ (k : U.Comp) (δ : GL (Fin r) E) (h : IsMatch (U.X k) (U.X k) δ) (ρ : Xo.X ⟶ Xo.X)
      (ν : SABMap Xo.univ.t Xo.univ.t ρ), ρ ≫ Xo.s = Xo.s → MoveMatch U U k k h ρ ν → ∀ w n, Dom w n →
      ∀ f ∈ sec Xo c w n, ∀ f' ∈ sec Xo c w n,
      (∀ y y' : FrPt Xo c (CAt σ), FrMove ρ ν y y' → evR Xo c f' y = evR Xo c f y') → ∀ x ∈ (U.X k).dom,
      Formalism.L2.PjFree.rdU U f' k x = Formalism.L2.PjFree.rdU U f k (lact δ (castFr h.psi x)))
    {k k' : U.Comp} {δ₀ : GL (Fin r) E} (h₀ : IsMatch (U.X k) (U.X k') δ₀) {γ : Dw.La →ₗ[𝓞 E] Dw.La}
    {ρ : Xo.X ⟶ Xo.X} {ν : SABMap Xo.univ.t Xo.univ.t ρ} (hm : IsLevMove ρ ν γ LinearMap.id)
    (m₀ : MarkRel l (φ k) (φ k') (F.t (ik k)) (F.t (ik k')) γ δ₀) (n : ℕ) :
    ∃ ε : ℂ, ‖ε‖ = 1 ∧ ∀ w, Dom w n → ∀ f ∈ sec Xo c w n, ∀ f' ∈ sec Xo c w n,
      (∀ y y' : FrPt Xo c (CAt σ), FrMove ρ ν y y' → evR Xo c f' y = evR Xo c f y') →
      ∀ (k₁ k₁' : U.Comp) (δ : GL (Fin r) E) (h : IsMatch (U.X k₁) (U.X k₁') δ), k₁ = k →
      MarkRel l (φ k₁) (φ k₁') (F.t (ik k₁)) (F.t (ik k₁')) γ δ → ∀ x ∈ (U.X k₁).dom,
      Formalism.L2.PjFree.rdU U f' k₁ x = ε * Formalism.L2.PjFree.rdU U f k₁' (lact δ (castFr h.psi x)) := by
  obtain ⟨ε, hε, hc⟩ := GlobalTheory.T.exists_const_mul_reading_of_moved_section_at_frame E H Dw l Xo c σ r U U hσ hU hU k k' δ₀ h₀ ρ ν hm.1
    (GlobalTheory.T.moveMatch_of_markRel_of_isLevMove E H Dw l Xo c σ r U g e F ik φ hσ hpq hA hP k k' δ₀ h₀ γ ρ ν m₀ hm)
    (fun x y' t hx hy ht => GlobalTheory.LevelCusp.cabs_gen_eq_one_of_move E H Dw l Xo c σ r U hσ hU ρ ν k k' x _ y' t hy ht hx
      (fun τ i => by rw [h₀.dmin_eq]; exact hx _ i)) n
  refine ⟨ε, hε, fun w hw f hf f' hf' hv k₁ k₁' δ h hk m x hx => ?_⟩
  subst hk
  obtain rfl : k₁' = k' := comp_unique hσ hU hpq hA hP h h₀ hm m m₀ ⟨x, hx⟩
  obtain ⟨ν₀, hν₀, hy₀⟩ := (GlobalTheory.MoveCalc.frMove_calculus E H Dw l Xo c).1
  have hm₀ : IsLevMove (𝟙 Xo.X) ν₀ LinearMap.id LinearMap.id :=
    ⟨Category.id_comp _, fun a => by rw [hν₀]; exact (Category.comp_id _).trans (Category.id_comp _).symm,
      fun a => by rw [hν₀]; exact (Category.comp_id _).trans (Category.id_comp _).symm⟩
  have := hex k₁' _ (isMatch_div h₀ h) _ ν₀ hm₀.1
    (GlobalTheory.T.moveMatch_of_markRel_of_isLevMove E H Dw l Xo c σ r U g e F ik φ hσ hpq hA hP _ _ _ _ _ _ _ (m₀.div m) hm₀) w n hw f hf f hf
    (fun y y' hy => by
      rw [(GlobalTheory.exists_unique_frMove E H Dw l Xo c _ ν₀ hm₀.1 _ y).2 y y' ν₀ rfl (hy₀ _ y) hy]) _ (h₀.mem_dom hx)
  rw [hc w hw f hf f' hf' hv x hx, this, lact_div]

end Free

section Record

open NumberField IsDedekindDomain CategoryTheory ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.BasicNotions.TH
  Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj Formalism.IndefR.Lev GlobalTheory.IndefiniteRowSideFullHecke.LatticeBasisLifts
open GlobalTheory.Member (FinCong)
open GlobalTheory.LevelCusp (IsMatch)
open GlobalTheory.Dict (castFr)
open scoped TensorProduct Matrix

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

def liftGrp (V : HSp D) {r : ℕ} (hr : V.rank = r) (β : GL (Fin r) (EAf D)) (Pg : Finset (Formalism.L2.DIV.Pl D.host.E)) :
    Subgroup (Formalism.L2.DIV.G0 Pg r × GA D V) where
  carrier := {p | IsLift V hr β Pg p.1 p.2}
  one_mem' := isLift_one V hr β Pg
  mul_mem' := by
    rintro ⟨g, κ⟩ ⟨g', κ'⟩ ⟨a, h, b⟩ ⟨a', h', b'⟩
    refine ⟨mul_mem a a', by rw [Prod.snd_mul, map_mul]; exact mul_mem h h', fun w => ?_⟩
    have := map_mul (Formalism.L2.DIV.redAt β w.1) ⟨_, h⟩ ⟨_, h'⟩
    rw [b, b'] at this
    refine Eq.trans (congrArg _ (Subtype.ext ?_)) this
    exact map_mul (finR V hr) κ κ'
  inv_mem' := by
    rintro ⟨g, κ⟩ ⟨a, h, b⟩
    refine ⟨inv_mem a, by rw [Prod.snd_inv, map_inv]; exact inv_mem h, fun w => ?_⟩
    have := map_inv (Formalism.L2.DIV.redAt β w.1) ⟨_, h⟩
    rw [b] at this
    refine Eq.trans (congrArg _ (Subtype.ext ?_)) this
    exact map_inv (finR V hr) κ

variable {G : Type} [Group G]

end Record

end GlobalTheory.GeoLevel
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GridSizesLogBound
section
noncomputable section

open NumberField IsDedekindDomain GlobalTheory.SqTop GlobalTheory.FunObj.SqNum Formalism.BasicNotions GlobalTheory.ChiGrid

namespace GlobalTheory.SqTop.SizesBound

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {T : Type} {L : Formalism.IndefR.Links.LevCh D T}

theorem auxiliaryProduct_mem_place_of_exceptionalSet (P : Places L) {v : HeightOneSpectrum (𝓞 D.host.F)} (hv : v ∈ P.S0) :
    ((D.host.g 0 * D.host.g 1 * D.host.pde * D.host.pde' * q0 D : ℕ) : 𝓞 D.host.F) ∈ v.asIdeal := by
  have hp := v.isPrime
  simp only [Nat.cast_mul, hp.mul_mem_iff_mem_or_mem]
  rcases P.mem_S0_of_sum_eq.1 hv with rfl | h
  · exact Or.inr P.basePlace_over_qZero
  · rcases (S1_mem_OmF D).1 h with h | h | h | h
    · exact Or.inl (Or.inl (Or.inl (Or.inl h)))
    · exact Or.inl (Or.inl (Or.inl (Or.inr h)))
    · exact Or.inl (Or.inl (Or.inr h))
    · exact Or.inl (Or.inr h)

theorem levQ_le (P : Places L) :
    levQ P ≤ ((D.host.g 0 * D.host.g 1 * D.host.pde * D.host.pde' * q0 D) ^ Module.finrank ℤ (𝓞 D.host.F)) ^ 2 := by
  classical
  set M := D.host.g 0 * D.host.g 1 * D.host.pde * D.host.pde' * q0 D with hM
  have hmem : ((M : ℕ) : 𝓞 D.host.F) ∈ ∏ v ∈ P.S0, v.asIdeal := by
    rw [← Ideal.dvd_span_singleton]
    exact Finset.prod_dvd_of_coprime (fun v _ w _ hne => HeightOneSpectrum.isCoprime_of_ne v w hne)
      fun v hv => Ideal.dvd_span_singleton.2 (auxiliaryProduct_mem_place_of_exceptionalSet P hv)
  have hdvd := Ideal.absNorm_dvd_absNorm_of_le ((Ideal.span_singleton_le_iff_mem _).2 hmem)
  rw [Ideal.absNorm_span_natCast, map_prod] at hdvd
  have hM0 : 0 < M := by
    have := (leastSplitAuxiliaryPrimeThetaChain_spec D).1.pos
    have := (D.host.g_prime 0).pos
    have := (D.host.g_prime 1).pos
    have := D.host.pde_prime.pos
    have := D.host.pde'_prime.pos
    positivity
  have hle := Nat.le_of_dvd (pow_pos hM0 _) hdvd
  calc levQ P = ∏ v ∈ P.S0, Ideal.absNorm v.asIdeal ^ condExp P v := rfl
    _ ≤ ∏ v ∈ P.S0, Ideal.absNorm v.asIdeal ^ 2 := by
      refine Finset.prod_le_prod' fun v _ => Nat.pow_le_pow_right ?_ ?_
      · exact Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.2 v.ne_bot)
      · unfold condExp; split_ifs <;> norm_num
    _ = (∏ v ∈ P.S0, Ideal.absNorm v.asIdeal) ^ 2 := Finset.prod_pow _ _ _
    _ ≤ _ := Nat.pow_le_pow_left hle 2

theorem kap_add_le (large₂ : SizeData₂ D) (h : GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup.SizeRows large₂) (i j : Fin D.R.m) {s : ℕ}
    (hs : s ≤ halfRank D i j) (τ : D.what₂.Tau) : (kap D 1 i j s τ : ℝ) + s ≤ 5 * large₂.sc.b := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hSc, hhc, -⟩ := h
  have e := (Model.kap_add D 1 i j τ hs).1
  have e' := congrArg (Int.cast : ℤ → ℝ) e
  push_cast at e'
  rw [e']

  have he : (((num D 1 τ).e (j + 1) : ℤ) : ℝ) ≤ 4 * large₂.sc.b := by
    have s1 := ((GlobalTheory.SignedHC.GridData.ofHCParam_spec (D.hc τ) (sLen D) (gap D 1) (cen D 1 τ)).2.2 j)
    have s2 : (((D.hc τ).e j : ℚ) : ℝ) = (((num D 1 τ).e (j + 1) : ℤ) : ℝ) := by
      rw [s1]; push_cast; rfl
    rw [← s2]; exact (hhc τ j).2

  set G0 := GlobalTheory.SignedHC.GridData.ofHCParam (D.hc τ) (sLen D) (gap D 1) 0 with hG0
  have hk := D.R.m_add_three_le_k
  have hv0 : 0 < D.R.k - 1 := by omega
  have hv : (G0.v 2 : ℚ) ≤ large₂.Sc := by
    have s1 := (GlobalTheory.SignedHC.GridData.ofHCParam_spec (D.hc τ) (sLen D) (gap D 1) 0).1 ⟨0, hv0⟩
    have := (large₂.cloud_v τ ⟨0, hv0⟩).2
    rw [s1] at this
    exact_mod_cast this
  have hmid : ((G0.mid (D.R.m - i) : ℚ) : ℝ) ≤ large₂.Sc + ((D.R.m : ℝ) + 1) * gap D 1 + 1 / 2 := by
    have hi := i.2
    have hm : G0.m = D.R.m := rfl
    have hg : G0.ga = gap D 1 := rfl
    simp only [GlobalTheory.SignedHC.GridData.mid, GlobalTheory.SignedHC.GridData.a, hm, hg]
    have hg0 : (0 : ℝ) ≤ gap D 1 := by positivity
    have hi' : ((i : ℕ) : ℝ) + 1 ≤ D.R.m := by exact_mod_cast hi
    have hv' : ((G0.v 2 : ℚ) : ℝ) ≤ large₂.Sc := by exact_mod_cast hv
    have c1 : ((D.R.m - (i : ℕ) - 1 : ℕ) : ℝ) = D.R.m - (i : ℕ) - 1 := by
      rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]; simp
    have c2 : ((D.R.m - (i : ℕ) : ℕ) : ℝ) = D.R.m - (i : ℕ) := by
      rw [Nat.cast_sub (by omega)]
    push_cast
    rw [c1, c2]
    have hv'' : ((G0.v 2 : ℤ) : ℝ) ≤ large₂.Sc := by exact_mod_cast hv
    nlinarith [mul_le_mul_of_nonneg_right hi' hg0]
  have hc : ((cen D 1 τ (D.R.m - i) : ℤ) : ℝ) ≤ large₂.sc.b := by
    have h1 : ((cen D 1 τ (D.R.m - i) : ℤ) : ℚ) ≤ G0.mid (D.R.m - i) := Int.floor_le _
    have h2 : ((cen D 1 τ (D.R.m - i) : ℤ) : ℝ) ≤ ((G0.mid (D.R.m - i) : ℚ) : ℝ) := by exact_mod_cast h1
    linarith
  linarith

end GlobalTheory.SqTop.SizesBound

namespace GlobalTheory.SqTop.SizesBound

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem sizes (c : ℝ) : GBig fun {D} _ _ {sc} G _ C x b => ∀ (i j : Fin D.R.m) (s : ℕ), 1 ≤ s → s ≤ halfRank D i j →
    c * (Module.finrank ℚ D.host.E : ℝ) + Real.log |((discr D.host.E : ℤ) : ℝ)| + 2 * Real.log (levQ G.pl) +
      ∑ τ, Real.log (1 + ((kap D sc.cGap i j s τ : ℝ) + s)) ≤ bTH D C x b := by
  refine ⟨0, fun ε CF _ => ⟨2 * |c| + 100, 3, fun C hC D large₂ _ hx hR T Lc μ₀ _ G i j s _ hs => ?_⟩⟩
  have hS := hR.size
  obtain ⟨-, hSA, -, -, -, -, -, hgL, hqL, hrd, hcd, -, -, -⟩ := hR.size
  have hpde : Real.log (D.host.pde : ℝ) ≤ large₂.sc.L ∧ Real.log (D.host.pde' : ℝ) ≤ large₂.sc.L :=
    hSA.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

  have hx1 : 1 < large₂.sc.x := by linarith
  have hLpos : 0 < large₂.sc.L := Real.rpow_pos_of_pos (by linarith) _
  have hlogb : Real.log large₂.sc.b = large₂.sc.L := Real.log_exp _
  have hb1 : 1 ≤ large₂.sc.b := Real.one_le_exp hLpos.le
  have hlx : 1 ≤ Real.log large₂.sc.x := by
    rw [Real.le_log_iff_exp_le (by linarith)]
    have := Real.exp_one_lt_d9
    linarith
  have hf0 : (0 : ℝ) ≤ D.R.f := Nat.cast_nonneg _

  have h1 : c * (Module.finrank ℚ D.host.E : ℝ) ≤ 2 * |c| * D.R.f := by
    rw [Formalism.L2.Pj.hostSize_finrank D]; push_cast
    nlinarith [le_abs_self c]

  have h2 : Real.log |((discr D.host.E : ℤ) : ℝ)| ≤ 2 * D.R.f * large₂.sc.L := by
    have e : Real.log |((discr D.host.E : ℤ) : ℝ)| = logdE D := rfl
    rw [e, Formalism.BasicNotions.logdE_eq_rd]
    have : Real.log D.host.rdE ≤ large₂.sc.L := by linarith
    nlinarith

  have h3 : Real.log (levQ G.pl) ≤ 2 * D.R.f * (21 * large₂.sc.L + 2) := by
    have hle := levQ_le G.pl
    rw [NumberField.RingOfIntegers.rank, GlobalTheory.ColClassCompare.finrank_F] at hle
    have hpos : 0 < levQ G.pl := Finset.prod_pos fun v _ =>
      pow_pos (Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.2 v.ne_bot)) _
    have hle' : (levQ G.pl : ℝ) ≤ ((((D.host.g 0 : ℕ) : ℝ) * (D.host.g 1 : ℕ) * (D.host.pde : ℕ) * (D.host.pde' : ℕ) *
        (q0 D : ℕ)) ^ D.R.f) ^ 2 := by exact_mod_cast hle
    have hl := Real.log_le_log (by exact_mod_cast hpos) hle'
    have p0 := (D.host.g_prime 0).pos
    have p1 := (D.host.g_prime 1).pos
    have p2 := D.host.pde_prime.pos
    have p3 := D.host.pde'_prime.pos
    have p4 := (leastSplitAuxiliaryPrimeThetaChain_spec D).1.pos
    push_cast at hl
    rw [Real.log_pow, Real.log_pow, Real.log_mul (by positivity) (by positivity),
      Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
      Real.log_mul (by positivity) (by positivity)] at hl
    have g0 := hgL 0
    have g1 := hgL 1
    push_cast at hl
    nlinarith

  have h4 : ∑ τ, Real.log (1 + ((kap D (⟨1, CF, large₂.sc.b⟩ : Consts).cGap i j s τ : ℝ) + s)) ≤
      D.R.f * (5 + large₂.sc.L) := by
    have hk : ∀ τ, Real.log (1 + ((kap D 1 i j s τ : ℝ) + s)) ≤ 5 + large₂.sc.L := by
      intro τ
      have k1 := kap_add_le large₂ hS i j hs τ
      have k0 : (0 : ℝ) ≤ (kap D 1 i j s τ : ℝ) + s := by positivity
      calc Real.log (1 + ((kap D 1 i j s τ : ℝ) + s)) ≤ Real.log (6 * large₂.sc.b) :=
            Real.log_le_log (by linarith) (by linarith)
        _ = Real.log 6 + large₂.sc.L := by rw [Real.log_mul (by norm_num) (by linarith), hlogb]
        _ ≤ 5 + large₂.sc.L := by
          have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 6 by norm_num)
          linarith
    calc _ ≤ ∑ _τ : D.what₂.Tau, (5 + large₂.sc.L) := Finset.sum_le_sum fun τ _ => hk τ
      _ = D.R.f * (5 + large₂.sc.L) := by
        rw [Finset.sum_const, Finset.card_univ, D.what₂.card_Tau, nsmul_eq_mul]

  show _ ≤ C * D.R.f * large₂.sc.b * (Real.log large₂.sc.b + Real.log large₂.sc.x)
  rw [hlogb]
  have hC0 : 0 ≤ C := by have := abs_nonneg c; linarith
  have t1 : (2 * |c| + 100) * D.R.f * (large₂.sc.L + 1) ≤ C * D.R.f * (large₂.sc.L + 1) := by
    have : 0 ≤ (D.R.f : ℝ) * (large₂.sc.L + 1) := by positivity
    nlinarith
  have t2 : large₂.sc.L + 1 ≤ large₂.sc.b * (large₂.sc.L + Real.log large₂.sc.x) := by nlinarith
  have t3 : C * D.R.f * (large₂.sc.L + 1) ≤ C * D.R.f * (large₂.sc.b * (large₂.sc.L + Real.log large₂.sc.x)) :=
    mul_le_mul_of_nonneg_left t2 (by positivity)
  have t4 : 0 ≤ (D.R.f : ℝ) * large₂.sc.L := by positivity
  have t5 : 0 ≤ |c| * D.R.f := by positivity
  nlinarith

end GlobalTheory.SqTop.SizesBound

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarmonicPolynomialLatticesStatement
section
open GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.BigOn.Exp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.small_bound_tuple : GlobalTheory.BigOn.Exp.TupLe.SmallSt := by
  first | exact @GlobalTheory.SmallSpan.smallSt | exact GlobalTheory.SmallSpan.smallSt | (intros; apply GlobalTheory.SmallSpan.smallSt <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeCosetProductsCommuteSplitPlace
section
set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.L2.Pj GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.ExpFrame GlobalTheory.ExpTie GlobalTheory.FrameOf
open scoped TensorProduct
open Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.HeckePairCount

theorem card_pairs_eq {G : Type} [Group G] (J L : Subgroup G) (x y : G) (A B : Finset G)
    (hθ : ∃ θ : G → G, (∀ g ∈ L, θ g ∈ L) ∧ (∀ x ∈ L, ∀ y ∈ L, θ (x * y) = θ y * θ x) ∧ (∀ x ∈ L, θ (θ x) = x) ∧
      (∀ k ∈ J ⊓ L, θ k ∈ J) ∧ ∀ g ∈ L, ∃ a ∈ J ⊓ L, ∃ b ∈ J ⊓ L, θ g = a * g * b)
    (hAL : ∀ a ∈ A, a ∈ L) (hBL : ∀ a ∈ B, a ∈ L) (hA : Bridge.IsDC J x A) (hB : Bridge.IsDC J y B) (c : G ⧸ J) :
    ((A ×ˢ B).filter (fun p => ((p.1 * p.2 : G) : G ⧸ J) = c)).card =
      ((B ×ˢ A).filter (fun p => ((p.1 * p.2 : G) : G ⧸ J) = c)).card := by
  obtain ⟨θ, hL, hm, hi, hK, hdc⟩ := hθ
  by_cases hc : ∃ z ∈ L, (z : G ⧸ J) = c
  · obtain ⟨z, hz, rfl⟩ := hc
    have key : ∀ C E : Finset G, (∀ a ∈ C, a ∈ L) → (∀ a ∈ E, a ∈ L) →
        (C ×ˢ E).filter (fun p => ((p.1 * p.2 : G) : G ⧸ J) = (z : G ⧸ J)) =
          (C ×ˢ E).filter (fun p => (z : G ⧸ (J ⊓ L)) = ((p.1 * p.2 : G) : G ⧸ (J ⊓ L))) := by
      intro C E hC hE
      refine Finset.filter_congr fun p hp => ?_
      rw [Finset.mem_product] at hp
      rw [eq_comm, QuotientGroup.eq, QuotientGroup.eq]
      exact ⟨fun h => ⟨h, L.mul_mem (L.inv_mem hz) (L.mul_mem (hC _ hp.1) (hE _ hp.2))⟩, fun h => h.1⟩
    rw [key A B hAL hBL, key B A hBL hAL]
    have e1 := GlobalTheory.DoubleCosetComm.card_pairs (A := A) hB hAL hBL hz
    have e2 := GlobalTheory.DoubleCosetComm.card_pairs (A := B) hA hBL hAL hz
    have e3 := le_antisymm (GlobalTheory.DoubleCosetComm.card_conv_le hm hi hK hL hdc hA hB hAL hz)
      (GlobalTheory.DoubleCosetComm.card_conv_le hm hi hK hL hdc hB hA hBL hz)
    exact e1.trans (e3.trans e2.symm)
  · have key : ∀ C E : Finset G, (∀ a ∈ C, a ∈ L) → (∀ a ∈ E, a ∈ L) →
        (C ×ˢ E).filter (fun p => ((p.1 * p.2 : G) : G ⧸ J) = c) = ∅ := by
      intro C E hC hE
      refine Finset.filter_eq_empty_iff.2 fun p hp h => hc ?_
      rw [Finset.mem_product] at hp
      exact ⟨_, L.mul_mem (hC _ hp.1) (hE _ hp.2), h⟩
    rw [key A B hAL hBL, key B A hBL hAL]

set_option maxHeartbeats 1600000 in

theorem side_count {D : D7} (V : Formalism.BasicNotions.TH.HSp D) (β : GL (Fin V.rank) (Formalism.IndefR.Lev.EAf D))
    (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E))
    (L : Formalism.L2.DIV.LevDat D.host.E ℂ V.rank) (hβ : Formalism.IndefR.Lev.IsBaseFrame V β Λ 1) {Pl0 : Type}
    (pl : Pl0 → Formalism.L2.DIV.Pl D.host.E) (ok : Set Pl0) (Sp : Set (Formalism.L2.DIV.Pl D.host.E))
    (hok : ∀ P, P ∈ ok ↔ Bridge.SplitOff (pl P) Sp) (hS : ∀ PP, PP ∈ L.Pg ∨ PP ∈ L.Q → PP ∈ Sp) (i i' : ok × ℕ)
    (hv : (pl i.1).under (𝓞 D.host.F) = (pl i'.1).under (𝓞 D.host.F)) (hi : i.2 ≤ V.rank)
    (x y : Bridge.Gf V) (A B : Finset (Bridge.Gf V)) (hx : isTEnv V pl ok i x)
    (hA : ∀ a ∈ A, isLocEnv V pl ok i a) (hB : ∀ a ∈ B, isLocEnv V pl ok i' a)
    (dA : Bridge.IsDC (levEnv V β L).J x A) (dB : Bridge.IsDC (levEnv V β L).J y B)
    (c : Bridge.Gf V ⧸ (levEnv V β L).J) :
    ((A ×ˢ B).filter (fun p => ((p.1 * p.2 : Bridge.Gf V) : Bridge.Gf V ⧸ (levEnv V β L).J) = c)).card =
      ((B ×ˢ A).filter (fun p => ((p.1 * p.2 : Bridge.Gf V) : Bridge.Gf V ⧸ (levEnv V β L).J) = c)).card := by
  refine (hx hi).elim fun α h0 => h0.1.elim fun e h1 => h1.elim fun ϖ h2 => ?_
  have he := h2.1
  have hsp := (hok _).1 i.1.2
  have hl := GlobalTheory.SplitHeckeAdj.local_group V β Λ L hβ (pl i.1) e he
    fun PP h => GlobalTheory.SplitHeckeAdj.off_of_splitOff hsp PP (hS PP h)
  refine hl.elim fun Lc hl => ?_
  have l1 := hl.1
  have l4 := hl.2.2.2.1
  have hm : ∀ x, isLocEnv V pl ok i x → x ∈ Lc := fun x hx => by
    refine (GlobalTheory.SplitHeckeAdj.loc_supp V hx he).elim fun g hg => ?_
    rw [← hg.2]
    exact l1 g hg.1
  have hm' : ∀ x, isLocEnv V pl ok i' x → x ∈ Lc := fun x hx => by
    refine hm x (GlobalTheory.FrameProdLoc.isLocEnv_of_mem V pl ok i x e he ?_)
    rw [hv]
    exact GlobalTheory.FrameProdLoc.mem_locGrp_of_isLocEnv V pl ok i' x hx
  exact card_pairs_eq (levEnv V β L).J Lc x y A B l4 (fun a ha => hm a (hA a ha)) (fun a ha => hm' a (hB a ha)) dA dB c

set_option maxHeartbeats 1600000 in

theorem card_pairs_comm : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ} (p : PtAt ex Csz) (j : Fin D.R.m) (t : p.P.T) (i i' : (blk p j t).Pl × ℕ), 1 ≤ i.2 → i.2 ≤ (Vc D j).rank → 1 ≤ i'.2 → i'.2 ≤ (Vc D j).rank → (plOf p j t i.1).under (𝓞 D.host.F) = (plOf p j t i'.1).under (𝓞 D.host.F) → ∀ c : Bridge.Gf (Vc D j) ⧸ levJ p j t, ((hkA p j t i ×ˢ hkA p j t i').filter (fun x => ((x.1 * x.2 : Bridge.Gf (Vc D j)) : Bridge.Gf (Vc D j) ⧸ levJ p j t) = c)).card = ((hkA p j t i' ×ˢ hkA p j t i).filter (fun x => ((x.1 * x.2 : Bridge.Gf (Vc D j)) : Bridge.Gf (Vc D j) ⧸ levJ p j t) = c)).card := by
  intro D L hT Gi Gl Kc Y cX ex Csz p j t i i' h1 h2 h1' h2' hv c
  have hb := p.charW.base
  refine hb.fam.tie.elim fun gramR h3 => h3.elim fun c0R h4 => h4.elim fun c0L tie => ?_
  refine (hb.lev.βV j).elim fun c' hc => ?_
  rw [one_pow] at hc
  have main := side_count (Vc D j) (p.R.βV j) (p.R.ΛV j) (p.R.datVt j t) hc p.R.pl (p.P.A3.A.ok t) _ (tie.ok t)
    (fun PP hP => hP.elim (fun h1 => Or.inl (hb.fam.Sb h1)) Or.inr) i i' hv h2
    ((p.R.B.L j t).hecke.hx i) ((p.R.B.L j t).hecke.hx i') (hkA p j t i) (hkA p j t i')
    ((p.R.B.L j t).hecke.hx_ok i ⟨h1, h2⟩) ((p.R.B.L j t).hecke.hA_loc i ⟨h1, h2⟩) ((p.R.B.L j t).hecke.hA_loc i' ⟨h1', h2'⟩)
    ((p.R.B.L j t).hecke.hDC i ⟨h1, h2⟩) ((p.R.B.L j t).hecke.hDC i' ⟨h1', h2'⟩) c
  exact main

end GlobalTheory.HeckePairCount

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HighestWeightBaseChangeStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Pj GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.ExpTie GlobalTheory.ExpFrame Formalism.CohomologicalDescent.DepthNonnegative Formalism.CohomologicalDescent.LogSmallConstantBounds Formalism.CohomologicalDescent.ShortWeightBounds Formalism.CohomologicalDescent.LD Formalism.RankGapBounds.FormsTensorLocalization
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.highest_weight_base_change : GlobalTheory.HighWt.BaseChange := by
  first | exact @GlobalTheory.HighWt.baseChange_holds | exact GlobalTheory.HighWt.baseChange_holds | (intros; apply GlobalTheory.HighWt.baseChange_holds <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HodgeLineMultipleLeFamilyThresholdStatement
section
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.BigTop GlobalTheory.BigOn
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hodgeLineMultiple_le_familyThreshold : Closed FamHyp fun Fm _ => ∃ x0 : ℝ, ∀ (x : ℝ) (hx : Fm.x1 < x), x0 ≤ x → ∀ ι : Fm.Ix x, 2 * (Fm.D x ι).R.r + 50 * (Fm.D x ι).R.r ^ 2 * ((Fm.D x ι).R.f * ((Fm.D x ι).R.r * (Fm.D x ι).R.r / 4)) + 2 ≤ (Fm.parT x hx ι).TO := by
  first | exact @GlobalTheory.HodgeMultNum.hodgeMult_le_TO | exact GlobalTheory.HodgeMultNum.hodgeMult_le_TO | (intros; apply GlobalTheory.HodgeMultNum.hodgeMult_le_TO <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HorizontalGeneratorZpowMulCuspFormMemSpanStatement
section
open NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.horizontalGenerator_zpow_mul_cuspForm_mem_span : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (x : ℝ), Laws U x → ∀ (Z : Comp Xo c) (σ : c.F →+* ℂ), GoodEmb c σ → ∀ (k0 : (U σ).Comp), framesOn (U σ) Z = {z | z.1 = k0 ∧ z.2 ∈ ((U σ).X z.1).dom} → ∀ (τ' : ((U σ).X k0).Ψ) (m : ℤ) (b b' : (E →+* ℂ) × ℕ → ℕ) (n : ℕ), Dom b n → Dom b' n → (∀ ρ i, i < Dw.mult ρ → 1 ≤ b' (ρ, i)) → 4 * (finrank ℚ E * r) + 4 ≤ n → modelWt (U σ) (wtZ b' n) k0 = modelWt (U σ) (wtZ b n) k0 + m • modelFlat r τ' → ∀ f ∈ cuspOn U Z (wtZ b n), (fun y : ↥((U σ).X k0).dom => horizGen τ' y.1 ^ m * rdU (U σ) f k0 y.1) ∈ Submodule.span ℂ ((fun g : Rul Xo c => fun y : ↥((U σ).X k0).dom => rdU (U σ) g k0 y.1) '' (cuspOn U Z (wtZ b' n) : Set (Rul Xo c))) := by
  first | exact @GlobalTheory.FlatCore.MulSpan.horizGen_zpow_mul_rdU_mem_span | exact GlobalTheory.FlatCore.MulSpan.horizGen_zpow_mul_rdU_mem_span | (intros; apply GlobalTheory.FlatCore.MulSpan.horizGen_zpow_mul_rdU_mem_span <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HoweDualityForLocOps
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.HoweAdelic

noncomputable section

namespace GlobalTheory.HoweNonsplit

theorem howeDualityFor_locOps : GlobalTheory.FunPr.Hypotheses₂ → GlobalTheory.Published.HoweDualityUnitary → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
    ∀ (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (ψ : AddChar (AF F) ℂ) (χX χW : Chr F E) (om : Rep σ X W),
      IsStd ψ → (∀ i j, σ (X.J j i) = X.J i j) → X.J.det ≠ 0 → (∀ i j, σ (W.J j i) = -W.J i j) → W.J.det ≠ 0 →
      ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range χX n →
      ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range χW d → IsHecke F E χX → IsHecke F E χW →
      M.IsWeil ψ χX χW om →
      ∀ v : Pl F, IsEmpty (E →ₐ[F] Fv F v) →
      ∀ om' : UAtGrp σ X (evFin F v) × UAtGrp σ W (evFin F v) →* Module.End ℂ ((Fin n × Fin d → Fv F v) → ℂ),
        (∀ g h, ∀ φ ∈ SB (Fin n × Fin d → Fv F v), om' (g, h) φ ∈ SB (Fin n × Fin d → Fv F v) ∧
          Acts (evFin F v) (om (g.1, h.1)) φ (om' (g, h) φ)) → GlobalTheory.Published.HoweDualityFor om' := by
  intro hP hHD F E _ _ _ _ _ σ hCM n d X W M ψ χX χW om hψ hX hXd hW hWd hrX hrW hhX hhW hom v hv
  have key := GlobalTheory.HoweLocal.howeDualityFor_closure hP hHD F E σ hCM n d X W M ψ χX χW om hψ hX hXd hW hWd hrX hrW hhX hhW hom v hv
  rw [show Subgroup.closure (UAt σ X (evFin F v)) = GlobalTheory.HoweAdelic.UAtGrp σ X (evFin F v) from
      Subgroup.closure_eq (GlobalTheory.HoweAdelic.UAtGrp σ X (evFin F v)),
    show Subgroup.closure (UAt σ W (evFin F v)) = GlobalTheory.HoweAdelic.UAtGrp σ W (evFin F v) from
      Subgroup.closure_eq (GlobalTheory.HoweAdelic.UAtGrp σ W (evFin F v))] at key
  exact key

end GlobalTheory.HoweNonsplit
end
end

