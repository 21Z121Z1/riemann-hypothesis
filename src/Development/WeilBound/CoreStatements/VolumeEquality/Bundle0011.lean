import Development.WeilBound.CoreStatements.VolumeEquality.Bundle0006
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0201
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.Bundle0022

-- bundled from Development.WeilBound.CoreStatements.VolumeEquality.DegPushMuLinkA
section
noncomputable section

namespace SheetDecomposition

open AlgebraicGeometry CategoryTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp

section Lin

variable {Ω₃ : Type} [Field Ω₃] (O : ValuationSubring Ω₃) {r : ℕ}

theorem mu_det_le (T T' : Matrix (Fin r) (Fin r) Ω₃)
    (h : ∀ k, (fun m => T m k) ∈ Submodule.span O (Set.range fun k m => T' m k)) :
    O.valuation T.det ≤ O.valuation T'.det := by
  choose N hN using fun k => (Submodule.mem_span_range_iff_exists_fun O).1 (h k)
  have e : T = T' * (Matrix.of fun a b => N b a).map O.subtype := by
    ext m k
    have := congrFun (hN k) m
    simp only [Finset.sum_apply, Pi.smul_apply] at this
    rw [← this, Matrix.mul_apply]
    exact Finset.sum_congr rfl fun a _ => mul_comm _ _
  have e2 : ((Matrix.of fun a b => N b a).map O.subtype).det = ((Matrix.of fun a b => N b a).det : O) :=
    (RingHom.map_det O.subtype _).symm
  rw [e, Matrix.det_mul, map_mul, e2]
  exact mul_le_of_le_one_right' (O.valuation_le_one _)

theorem mu_det_eq (T T' : Matrix (Fin r) (Fin r) Ω₃)
    (h : Submodule.span O (Set.range fun k m => T m k) = Submodule.span O (Set.range fun k m => T' m k)) :
    O.valuation T.det = O.valuation T'.det :=
  le_antisymm (mu_det_le O T T' fun k => h ▸ Submodule.subset_span ⟨k, rfl⟩)
    (mu_det_le O T' T fun k => h ▸ Submodule.subset_span ⟨k, rfl⟩)

theorem mu_coord {Ω V : Type} [Field Ω] [AddCommGroup V] [Module Ω V] (R : Subring Ω) (i : Ω →+* Ω₃) (hi : ∀ a ∈ R, i a ∈ O)
    (c : Fin r → V) (hc : LinearIndependent Ω c) (Z : Set V) (Λ : Submodule O (Fin r → Ω₃))
    (hZ : ∀ w ∈ Z, ∃ x : Fin r → Ω, w = ∑ m, x m • c m ∧ (fun m => i (x m)) ∈ Λ) (x : Fin r → Ω)
    (hx : ∑ m, x m • c m ∈ Submodule.span R Z) : (fun m => i (x m)) ∈ Λ := by
  have key : ∀ w ∈ Submodule.span R Z, ∃ x : Fin r → Ω, w = ∑ m, x m • c m ∧ (fun m => i (x m)) ∈ Λ := by
    intro w hw
    induction hw using Submodule.span_induction with
    | mem w hw => exact hZ w hw
    | zero => exact ⟨0, by simp, by simp only [Pi.zero_apply, map_zero]; exact Λ.zero_mem⟩
    | add a b _ _ ha hb =>
      obtain ⟨x, rfl, hx⟩ := ha
      obtain ⟨y, rfl, hy⟩ := hb
      refine ⟨x + y, by simp [add_smul, Finset.sum_add_distrib], ?_⟩
      convert Λ.add_mem hx hy using 1
      ext m; simp
    | smul a w _ hw =>
      obtain ⟨x, rfl, hx⟩ := hw
      refine ⟨fun m => (a : Ω) * x m, ?_, ?_⟩
      · rw [Subring.smul_def]
        simp [Finset.smul_sum, mul_smul]
      · convert Λ.smul_mem ⟨i a, hi a a.2⟩ hx using 1
        ext m
        show i (a * x m) = i a * i (x m)
        exact map_mul _ _ _
  obtain ⟨x', e, hx'⟩ := key _ hx
  have : x = x' := funext (Fintype.linearIndependent_iffₛ.1 hc x x' e)
  exact this ▸ hx'

theorem mu_alg {G : Type} [CommGroupWithZero G] {m₁ m₂ e₁ e₂ t₁ t₂ r₁ r₂ : G} (h₁ : m₁ * e₁ * t₁ = 1) (h₂ : m₂ * e₂ * t₂ = 1)
    (h : r₁ * t₁ = r₂ * t₂) (hr : r₁ ≠ 0) : m₂ = e₁ * r₂ / (r₁ * e₂) * m₁ := by
  have he : e₂ ≠ 0 := by rintro rfl; simp at h₂
  rw [div_mul_eq_mul_div, eq_div_iff (mul_ne_zero hr he)]
  calc m₂ * (r₁ * e₂) = m₂ * (r₁ * e₂) * (m₁ * e₁ * t₁) := by rw [h₁, mul_one]
    _ = m₂ * e₂ * (r₁ * t₁) * (m₁ * e₁) := by ac_rfl
    _ = m₂ * e₂ * t₂ * (e₁ * r₂ * m₁) := by rw [h]; ac_rfl
    _ = _ := by rw [h₂, one_mul]

end Lin

section Lats

variable {X : Scheme.{0}} {Ω Ω₃ : Type} [Field Ω] [Field Ω₃] {ξ : Sp Ω ⟶ X} {q : Cpt ξ}

theorem mu_gen_ratio {Λ : Lat ξ Ω} {t t' : Ω} (h : Λ.IsGenAt q t) (h' : Λ.IsGenAt q t') : t' / t ∈ regAt ξ q := by
  have : t' ∈ Submodule.span (regAt ξ q) {t} := h.2 ▸ h'.2 ▸ Submodule.mem_span_singleton_self _
  obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.1 this
  have e : (a : Ω) * t = t' := ha
  rw [← e, mul_div_cancel_right₀ _ h.1]
  exact a.2

theorem mu_gen_val {O : ValuationSubring Ω₃} {i : Ω →+* Ω₃} (hD : Dom O i ξ q) {Λ : Lat ξ Ω} {t t' : Ω} (h : Λ.IsGenAt q t)
    (h' : Λ.IsGenAt q t') : O.valuation (i t) = O.valuation (i t') := by
  have k : ∀ {t t' : Ω}, Λ.IsGenAt q t → Λ.IsGenAt q t' → O.valuation (i t') ≤ O.valuation (i t) := fun {t t'} h h' => by
    have h1 := (O.valuation_le_one_iff _).2 (hD.1 _ (mu_gen_ratio h h'))
    have e : t' = t * (t' / t) := (mul_div_cancel₀ _ h.1).symm
    rw [e, map_mul, map_mul]
    exact mul_le_of_le_one_right' h1
  exact le_antisymm (k h' h) (k h h')

theorem mu_tens_gen {I : Type} [Fintype I] {Λ : I → Lat ξ Ω} (a : I → ℤ) {t : I → Ω} (h : ∀ j, (Λ j).IsGenAt q (t j)) :
    (Lat.tens Λ a).IsGenAt q (∏ j, t j ^ a j) := by
  refine ⟨Finset.prod_ne_zero_iff.2 fun j _ => zpow_ne_zero _ (h j).1, le_antisymm (Submodule.span_le.2 ?_)
    (Submodule.span_le.2 ?_)⟩
  · rintro _ ⟨s, hs, rfl⟩
    have hm : ∏ j, (s j / t j) ^ a j ∈ regAt ξ q := prod_mem fun j _ => by
      obtain ⟨n, e | e⟩ := (a j).eq_nat_or_neg
      · rw [e, zpow_natCast]; exact pow_mem (mu_gen_ratio (h j) (hs j)) _
      · rw [e, zpow_neg, zpow_natCast, ← inv_pow, inv_div]; exact pow_mem (mu_gen_ratio (hs j) (h j)) _
    refine Submodule.mem_span_singleton.2 ⟨⟨_, hm⟩, ?_⟩
    show (∏ j, (s j / t j) ^ a j) * ∏ j, t j ^ a j = _
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun j _ => by rw [← mul_zpow, div_mul_cancel₀ _ (h j).1]
  · rintro _ rfl
    exact Submodule.subset_span ⟨t, h, rfl⟩

theorem mu_tens_ex {I : Type} [Fintype I] {Λ : I → Lat ξ Ω} {a : I → ℤ} {w : Ω} (h : (Lat.tens Λ a).IsGenAt q w) :
    ∃ t : I → Ω, ∀ j, (Λ j).IsGenAt q (t j) := by
  by_contra hn
  have e : (Lat.tens Λ a) q = ⊥ := by
    refine le_bot_iff.1 (Submodule.span_le.2 ?_)
    rintro _ ⟨s, hs, rfl⟩
    exact absurd ⟨s, hs⟩ hn
  have : w ∈ (Lat.tens Λ a) q := h.2 ▸ Submodule.mem_span_singleton_self _
  rw [e] at this
  exact h.1 this

theorem mu_deg_gen {K : Type} [Fintype K] {J : K → Type} {y : (Σ k, J k) → Ω} {Λ : Lat ξ Ω} {a : K → ℤ} {e : Ω}
    (h : Λ.IsDegOn Set.univ y a e) {ch : ∀ k, J k} (hc : InChart ξ (fun c' : (k : K) → J k => ∏ k, y ⟨k, c' k⟩) ch q) :
    Λ.IsGenAt q ((∏ k, y ⟨k, ch k⟩ ^ a k) * e) :=
  ⟨mul_ne_zero (Finset.prod_ne_zero_iff.2 fun k _ => zpow_ne_zero _ (Finset.prod_ne_zero_iff.1 hc.1 k (Finset.mem_univ _))) h.1,
    h.2 q trivial ch hc⟩

theorem mu_char0 [Algebra ℚ Ω₃] {O : ValuationSubring Ω₃} {i : Ω →+* Ω₃} (hD : Dom O i ξ q)
    (hO : ∀ x : ℚ, algebraMap ℚ Ω₃ x ∈ O) (p : ℕ) (hp : p.Prime) : ¬ InFibre ξ p q := by
  have : CharZero Ω₃ := algebraRat.charZero Ω₃
  have h0 : (p : Ω) ≠ 0 := fun h => by
    have := congrArg i h
    rw [map_natCast, map_zero] at this
    exact hp.ne_zero (Nat.cast_eq_zero.1 this)
  refine not_not.2 ⟨h0, natCast_mem _ _, hD.2 _ (natCast_mem _ _) h0 ?_⟩
  simpa using hO (p : ℚ)⁻¹

theorem mu_side {V : Type} [AddCommGroup V] [Module Ω V] (L : Lat ξ V) {r r' : ℕ} (hr : r = r') (W : Submodule Ω V)
    (hL : L.IsVB r W) (c : Fin r → V) (hc : LinearIndependent Ω c) (hW : Submodule.span Ω (Set.range c) = W)
    (s : Fin r' → V) (hs : LinearIndependent Ω s) (hsW : ∀ k, s k ∈ W) :
    ∃ ρ : Ω, ρ ≠ 0 ∧ ∀ (q : Cpt ξ) (O : ValuationSubring Ω₃) (i : Ω →+* Ω₃) (Ω₀ : Type) (ψ : Ω₀ → Ω) (B : Set (Fin r → Ω₀)),
      Dom O i ξ q → L q = Submodule.span (regAt ξ q) {w | ∃ a ∈ B, w = ∑ m, ψ (a m) • c m} →
      ∃ (t : Ω) (T : Matrix (Fin r) (Fin r) Ω₃), (detLat L s).IsGenAt q t ∧ T.det = i (ρ * t) ∧
        Submodule.span O (Set.range fun k m => T m k) = Submodule.span O {x | ∃ a ∈ B, x = fun m => i (ψ (a m))} := by
  subst hr
  subst hW
  choose P hP using fun k => (Submodule.mem_span_range_iff_exists_fun Ω).1 (hsW k)
  have hPi : LinearIndependent Ω P := by
    refine LinearIndependent.of_comp (Fintype.linearCombination Ω c) ?_
    convert hs using 1
    funext k
    simpa [Fintype.linearCombination_apply] using hP k
  set Pm : Matrix (Fin r) (Fin r) Ω := (Matrix.of P).transpose with hPm
  have hd : Pm.det ≠ 0 := by
    rw [hPm, Matrix.det_transpose]
    exact ((Matrix.isUnit_iff_isUnit_det _).1 (Matrix.linearIndependent_rows_iff_isUnit.1 hPi)).ne_zero
  refine ⟨Pm.det, hd, fun q O i Ω₀ ψ B hD hq => ?_⟩
  obtain ⟨U, hU, b, hb, hf⟩ := hL q trivial
  have hf := hf q trivial hU
  choose T₀ hT using fun k => (Submodule.mem_span_range_iff_exists_fun Ω).1
    (show b k ∈ Submodule.span Ω (Set.range c) from hb ▸ Submodule.subset_span ⟨k, rfl⟩)
  set Tm : Matrix (Fin r) (Fin r) Ω := (Matrix.of T₀).transpose with hTm
  have hPT : Pm * (Pm⁻¹ * Tm) = Tm := by
    rw [← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ (Ne.isUnit hd), Matrix.one_mul]
  have hbs : ∀ k, b k = ∑ k', (Pm⁻¹ * Tm) k' k • s k' := fun k => by
    rw [← hT k]
    simp only [← hP, Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [← Finset.sum_smul]
    congr 1
    have := congrFun (congrFun hPT m) k
    rw [Matrix.mul_apply] at this
    rw [show T₀ k m = Tm m k from rfl, ← this]
    exact Finset.sum_congr rfl fun a _ => mul_comm _ _
  refine ⟨(Pm⁻¹ * Tm).det, Tm.map i, GlobalTheory.T.det_lattice_frame_gen X Ω ξ V L r s b _ q hs hf hbs, ?_, le_antisymm (Submodule.span_le.2 ?_)
    (Submodule.span_le.2 ?_)⟩
  · rw [← Matrix.det_mul, hPT]
    exact (RingHom.map_det i _).symm
  · rintro _ ⟨k, rfl⟩
    refine mu_coord O (regAt ξ q) i hD.1 c hc {w | ∃ a ∈ B, w = ∑ m, ψ (a m) • c m} _ ?_ (T₀ k) ?_
    · rintro _ ⟨a, ha, rfl⟩
      exact ⟨_, rfl, Submodule.subset_span ⟨a, ha, rfl⟩⟩
    · rw [← hq, hT k, hf.2]
      exact Submodule.subset_span ⟨k, rfl⟩
  · rintro _ ⟨a, ha, rfl⟩
    refine mu_coord O (regAt ξ q) i hD.1 c hc (Set.range b) _ ?_ (fun m => ψ (a m)) ?_
    · rintro _ ⟨k, rfl⟩
      exact ⟨T₀ k, (hT k).symm, Submodule.subset_span ⟨k, rfl⟩⟩
    · rw [← hf.2, hq]
      exact Submodule.subset_span ⟨a, ha, rfl⟩

end Lats

end SheetDecomposition
end
end

-- bundled from Development.WeilBound.CoreStatements.VolumeEquality.DegPushPFa
section
noncomputable section

namespace SheetDecomposition.PF

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I4 GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree

variable {K : Type} [Fintype K] {ι : K → Type} [∀ b, Fintype (ι b)] {K' : Type} [Fintype K'] {ι' : K' → Type}
  [∀ b, Fintype (ι' b)]

theorem ne_of_arith {Ω : Type} [Field Ω] {y : (Σ b, ι b) → Ω} {d : ℕ} (h : IsArithVar (mCoordIdeal y) d) (k : K) :
    ∃ i, y ⟨k, i⟩ ≠ 0 := by
  obtain ⟨i, hi⟩ := h.2.1.2.2 k
  refine ⟨i, fun h0 => hi ?_⟩
  rw [mCoordIdeal, RingHom.mem_ker, mConeMap, aeval_X, h0, map_zero, zero_mul]

theorem arith_of_isPt [Nonempty K] {Ω : Type} [Field Ω] [Algebra ℚ Ω] {y : (Σ b, ι b) → Ω} {d : ℕ} (h : IsPt ℚ y d) :
    IsArithVar (mCoordIdeal y) (d + 1) := by
  obtain ⟨h1, h2, h3⟩ := h
  have : CharZero Ω := algebraRat.charZero Ω
  obtain rfl : ‹Algebra ℚ Ω› = DivisionRing.toRatAlgebra := Subsingleton.elim _ _
  choose c hc using h1
  have hF : fnField ℚ y ≤ IntermediateField.adjoin ℚ (coneRatios y c) := by
    refine IntermediateField.adjoin_le_iff.2 ?_
    rintro _ ⟨⟨k, i⟩, ⟨k', j⟩, e, rfl⟩
    obtain rfl : k = k' := e
    have : y ⟨k, i⟩ / y ⟨k, j⟩ = (y ⟨k, i⟩ / y ⟨k, c k⟩) / (y ⟨k, j⟩ / y ⟨k, c k⟩) := by
      rw [div_div_div_cancel_right₀ (hc k)]
    rw [SetLike.mem_coe, this]
    exact div_mem (IntermediateField.subset_adjoin _ _ ⟨⟨k, i⟩, rfl⟩) (IntermediateField.subset_adjoin _ _ ⟨⟨k, j⟩, rfl⟩)
  have hA : Algebra.IsAlgebraic (Algebra.adjoin ℚ (fnField ℚ y : Set Ω)) Ω := by
    have e : Algebra.adjoin ℚ (fnField ℚ y : Set Ω) = (fnField ℚ y).toSubalgebra := Algebra.adjoin_eq (fnField ℚ y).toSubalgebra
    rw [e]
    exact inferInstanceAs (Algebra.IsAlgebraic (fnField ℚ y) Ω)
  obtain ⟨t, ht, hb⟩ := exists_isTranscendenceBasis_subset (R := ℚ) (fnField ℚ y : Set Ω)
  have hc' : Cardinal.mk t = d := hb.cardinalMk_eq_trdeg.trans h3
  obtain ⟨e⟩ : Nonempty (Fin d ≃ t) := Cardinal.eq.1 (by simp [hc'])
  have hb' := hb.comp_equiv e
  have := hb'.isAlgebraic_field
  exact CoordConeArithVar.proof IntDomainDim.full K ι Ω y c d _ inferInstance hc hb'.1 (fun i => hF (ht (e i).2))
    fun r _ => Algebra.IsAlgebraic.isAlgebraic r

theorem mem_of_birational {Ω₁ Ω : Type} [Field Ω₁] [Field Ω] (i : Ω₁ →+* Ω) {y : (Σ b, ι b) → Ω₁} (hb : Birational y)
    (hne : ∀ k, ∃ j, y ⟨k, j⟩ ≠ 0) (F : Subfield Ω) (hF : ∀ k j j', i (y ⟨k, j⟩) / i (y ⟨k, j'⟩) ∈ F) (s : Ω₁) : i s ∈ F := by
  choose c hc using hne
  have key : ∀ (g : MRing ι) (d : K → ℕ), IsMultiHomog g d → i (aeval y g / ∏ k, y ⟨k, c k⟩ ^ d k) ∈ F := by
    intro g d hg
    have h1 : aeval y g / ∏ k, y ⟨k, c k⟩ ^ d k = aeval (fun p : Σ k, ι k => y p / y ⟨p.1, c p.1⟩) g := by
      have h := congrArg (eval fun k => (y ⟨k, c k⟩)⁻¹) (mConeMap_of_isMultiHomog y hg)
      have h' : (eval fun k => (y ⟨k, c k⟩)⁻¹).comp (mConeMap y : MRing ι →+* MvPolynomial K Ω₁) =
          ((aeval (fun p : Σ k, ι k => y p / y ⟨p.1, c p.1⟩) : MRing ι →ₐ[ℤ] Ω₁) : MRing ι →+* Ω₁) := by
        refine ringHom_ext (fun c => by simp) fun p => ?_
        simp [mConeMap, div_eq_mul_inv]
      have h'' := DFunLike.congr_fun h' g
      simp only [RingHom.comp_apply, RingHom.coe_coe] at h''
      rw [← h'', h, map_mul, eval_C]
      simp [div_eq_mul_inv]
    rw [h1]
    clear h1 hg
    induction g using MvPolynomial.induction_on with
    | C a => simp
    | add f g hf hg => simpa using add_mem hf hg
    | mul_X f p hf => simpa using mul_mem hf (hF p.1 p.2 (c p.1))
  obtain ⟨d, g, h, hg, hh, h0, e⟩ := hb s
  have hp : ∏ k, y ⟨k, c k⟩ ^ d k ≠ 0 := Finset.prod_ne_zero_iff.2 fun k _ => pow_ne_zero _ (hc k)
  have : s = (aeval y g / ∏ k, y ⟨k, c k⟩ ^ d k) / (aeval y h / ∏ k, y ⟨k, c k⟩ ^ d k) := by
    rw [div_div_div_cancel_right₀ hp, e, mul_div_cancel_right₀ _ h0]
  rw [this, map_div₀]
  exact div_mem (key g d hg) (key h d hh)

variable {Ω₁ : Type} [Field Ω₁] [Algebra ℚ Ω₁] {Ω : Type} [Field Ω] [Algebra ℚ Ω] [Algebra Ω₁ Ω]

theorem fnField_join {y : (Σ b, ι b) → Ω₁} (y' : (Σ b, ι' b) → Ω) (hb : Birational y) (hne : ∀ k, ∃ j, y ⟨k, j⟩ ≠ 0) :
    (fnField ℚ (joinPt (fun x => algebraMap Ω₁ Ω (y x)) y')).toSubfield = (fnField Ω₁ y').toSubfield := by
  apply le_antisymm
  · rw [fnField, IntermediateField.adjoin_toSubfield, Subfield.closure_le]
    rintro _ (⟨q, rfl⟩ | ⟨⟨k | k, j⟩, ⟨k', j'⟩, e, rfl⟩)
    · simp
    · obtain rfl : Sum.inl k = k' := e
      exact div_mem ((fnField Ω₁ y').algebraMap_mem _) ((fnField Ω₁ y').algebraMap_mem _)
    · obtain rfl : Sum.inr k = k' := e
      exact IntermediateField.subset_adjoin _ _ ⟨⟨k, j⟩, ⟨k, j'⟩, rfl, rfl⟩
  · rw [fnField, IntermediateField.adjoin_toSubfield, Subfield.closure_le]
    rintro _ (⟨s, rfl⟩ | ⟨⟨k, j⟩, ⟨k', j'⟩, e, rfl⟩)
    · refine mem_of_birational _ hb hne _ (fun k j j' => ?_) s
      exact IntermediateField.subset_adjoin ℚ _ ⟨⟨.inl k, j⟩, ⟨.inl k, j'⟩, rfl, rfl⟩
    · obtain rfl : k = k' := e
      exact IntermediateField.subset_adjoin _ _ ⟨⟨.inr k, j⟩, ⟨.inr k, j'⟩, rfl, rfl⟩

theorem finrank_join {y : (Σ b, ι b) → Ω₁} (y' : (Σ b, ι' b) → Ω) (hb : Birational y) (hne : ∀ k, ∃ j, y ⟨k, j⟩ ≠ 0) :
    Module.finrank (fnField ℚ (joinPt (fun x => algebraMap Ω₁ Ω (y x)) y')) Ω = Module.finrank (fnField Ω₁ y') Ω := by
  show Module.finrank (fnField ℚ (joinPt (fun x => algebraMap Ω₁ Ω (y x)) y')).toSubfield Ω =
    Module.finrank (fnField Ω₁ y').toSubfield Ω
  rw [fnField_join y' hb hne]

theorem isPt_join {y : (Σ b, ι b) → Ω₁} {y' : (Σ b, ι' b) → Ω} {n r : ℕ} (hb : Birational y)
    (ha : IsArithVar (mCoordIdeal y) (n + 1)) (h : IsPt Ω₁ y' r) :
    IsPt ℚ (joinPt (fun x => algebraMap Ω₁ Ω (y x)) y') (n + r) := by
  have hne := ne_of_arith ha
  refine ⟨?_, ?_, ?_⟩
  · rintro (k | k)
    · obtain ⟨j, hj⟩ := hne k
      exact ⟨j, (map_ne_zero (algebraMap Ω₁ Ω)).2 hj⟩
    · exact h.1 k
  · have := h.2.1
    exact Module.finite_of_finrank_pos (by rw [finrank_join y' hb hne]; exact Module.finrank_pos)
  · have h1 := FnFieldTrdeg.full K ι Ω₁ y n hb ha
    have : CharZero Ω₁ := algebraRat.charZero Ω₁
    have : IsScalarTower ℤ ℚ Ω₁ := IsScalarTower.of_algebraMap_eq' (Subsingleton.elim _ _)
    have : IsScalarTower ℚ Ω₁ Ω := IsScalarTower.of_algebraMap_eq' (Subsingleton.elim _ _)
    have : Algebra.IsAlgebraic ℤ ℚ := IsLocalization.isAlgebraic ℚ (nonZeroDivisors ℤ)
    have h2 := trdeg_add_eq ℤ ℚ (A := Ω₁)
    rw [trdeg_eq_zero, zero_add, h1] at h2
    rw [← trdeg_add_eq ℚ Ω₁ (A := Ω), h2, h.2.2, Nat.cast_add]

end SheetDecomposition.PF
end
end

-- bundled from Development.WeilBound.CoreStatements.VolumeEquality.DegPushPFb
section
noncomputable section

namespace SheetDecomposition.PF

open MvPolynomial

theorem ker_baseChange {k B K σ Φ Φ' : Type} [Field k] [CommRing B] [Algebra k B] [Field Φ] [Field Φ']
    [Algebra (MvPolynomial K k) Φ] [IsFractionRing (MvPolynomial K k) Φ] (a : k →+* Φ)
    (ha : ∀ c, a c = algebraMap (MvPolynomial K k) Φ (C c)) (ν : MvPolynomial K B →+* Φ') (hν : Function.Injective ν)
    (L : Φ →+* Φ') (hL : ∀ r, L (algebraMap (MvPolynomial K k) Φ r) = ν (map (algebraMap k B) r))
    (ψ : MvPolynomial σ k →ₐ[k] B) :
    RingHom.ker (eval₂Hom L fun s => ν (C (ψ (X s)))) = (RingHom.ker ψ).map (map a) := by
  classical
  obtain ⟨Θ, hΘ⟩ : ∃ f : MvPolynomial σ Φ →+* Φ', f = eval₂Hom L fun s => ν (C (ψ (X s))) :=
    ⟨_, rfl⟩
  suffices main : RingHom.ker Θ = (RingHom.ker ψ).map (map a) by
    subst hΘ
    exact main
  have hΘC : ∀ f : Φ, Θ (C f) = L f := fun f => by rw [hΘ, eval₂Hom_C]
  have hΘX : ∀ s : σ, Θ (X s) = ν (C (ψ (X s))) := fun s => by rw [hΘ, eval₂Hom_X']
  obtain ⟨α, hα⟩ : ∃ f : MvPolynomial K (MvPolynomial σ k) →+* MvPolynomial σ Φ,
      f = eval₂Hom (map a) fun i => C (algebraMap (MvPolynomial K k) Φ (X i)) := ⟨_, rfl⟩
  have hαC : ∀ p : MvPolynomial σ k, α (C p) = map a p := fun p => by rw [hα, eval₂Hom_C]
  have hαX : ∀ i : K, α (X i) = C (algebraMap (MvPolynomial K k) Φ (X i)) := fun i => by
    rw [hα, eval₂Hom_X']
  have hΘa : ∀ p : MvPolynomial σ k, Θ (map a p) = ν (C (ψ p)) := by
    have h : Θ.comp (map a) =
        ν.comp ((C : B →+* MvPolynomial K B).comp (ψ : MvPolynomial σ k →+* B)) := by
      apply MvPolynomial.ringHom_ext
      · intro c
        simp only [RingHom.comp_apply, map_C, hΘC, ha, hL, RingHom.coe_coe, algHom_C]
      · intro s
        simp only [RingHom.comp_apply, map_X, hΘX, RingHom.coe_coe]
    intro p
    exact DFunLike.congr_fun h p
  have hΘα : ∀ Q, Θ (α Q) = ν (map (ψ : MvPolynomial σ k →+* B) Q) := by
    have h : Θ.comp α = ν.comp (map (ψ : MvPolynomial σ k →+* B)) := by
      apply MvPolynomial.ringHom_ext
      · intro p
        simp only [RingHom.comp_apply, hαC, hΘa, map_C, RingHom.coe_coe]
      · intro i
        simp only [RingHom.comp_apply, hαX, hΘC, hL, map_X]
    intro Q
    exact DFunLike.congr_fun h Q
  have hαmapC : ∀ p : MvPolynomial K k, α (map (C : k →+* MvPolynomial σ k) p) =
      C (algebraMap (MvPolynomial K k) Φ p) := by
    have h : α.comp (map (C : k →+* MvPolynomial σ k)) =
        (C : Φ →+* MvPolynomial σ Φ).comp (algebraMap (MvPolynomial K k) Φ) := by
      apply MvPolynomial.ringHom_ext
      · intro c
        simp only [RingHom.comp_apply, map_C, hαC, ha]
      · intro i
        simp only [RingHom.comp_apply, map_X, hαX]
    intro p
    exact DFunLike.congr_fun h p
  have hCmem : ∀ q : MvPolynomial K k, C (algebraMap (MvPolynomial K k) Φ q) ∈ α.range :=
    fun q => RingHom.mem_range.mpr ⟨_, hαmapC q⟩
  have hXmem : ∀ s : σ, (X s : MvPolynomial σ Φ) ∈ α.range := fun s =>
    RingHom.mem_range.mpr ⟨C (X s), by rw [hαC, map_X]⟩
  have hden : ∀ P : MvPolynomial σ Φ, ∃ q : MvPolynomial K k, q ≠ 0 ∧
      C (algebraMap (MvPolynomial K k) Φ q) * P ∈ α.range := by
    intro P
    refine MvPolynomial.induction_on (motive := fun P => ∃ q : MvPolynomial K k, q ≠ 0 ∧
      C (algebraMap (MvPolynomial K k) Φ q) * P ∈ α.range) P ?_ ?_ ?_
    · intro f
      try dsimp only
      obtain ⟨p, q, hq, rfl⟩ := IsFractionRing.div_surjective (MvPolynomial K k) f
      refine ⟨q, nonZeroDivisors.ne_zero hq, ?_⟩
      rw [← C_mul, mul_div_cancel₀ _ (IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hq)]
      exact hCmem p
    · intro P₁ P₂ h₁ h₂
      try dsimp only at h₁ h₂ ⊢
      obtain ⟨q₁, hq₁, h₁⟩ := h₁
      obtain ⟨q₂, hq₂, h₂⟩ := h₂
      refine ⟨q₁ * q₂, mul_ne_zero hq₁ hq₂, ?_⟩
      have e : C (algebraMap (MvPolynomial K k) Φ (q₁ * q₂)) * (P₁ + P₂) =
          C (algebraMap (MvPolynomial K k) Φ q₂) * (C (algebraMap (MvPolynomial K k) Φ q₁) * P₁) +
            C (algebraMap (MvPolynomial K k) Φ q₁) * (C (algebraMap (MvPolynomial K k) Φ q₂) * P₂) := by
        rw [map_mul, C_mul]
        ring
      rw [e]
      exact add_mem (mul_mem (hCmem q₂) h₁) (mul_mem (hCmem q₁) h₂)
    · intro P s h
      try dsimp only at h ⊢
      obtain ⟨q, hq, h⟩ := h
      refine ⟨q, hq, ?_⟩
      rw [← mul_assoc]
      exact mul_mem h (hXmem s)
  apply le_antisymm
  · intro P hP
    rw [RingHom.mem_ker] at hP
    obtain ⟨q, hq, hmem⟩ := hden P
    obtain ⟨Q, hQ⟩ := RingHom.mem_range.mp hmem
    have hQ0 : map (ψ : MvPolynomial σ k →+* B) Q = 0 := by
      apply hν
      rw [map_zero, ← hΘα, hQ, map_mul, hP, mul_zero]
    have hJ : α Q ∈ (RingHom.ker ψ).map (map a) := by
      rw [Q.as_sum, map_sum]
      refine Ideal.sum_mem _ fun v _ => ?_
      rw [monomial_eq, map_mul, hαC]
      refine Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ ?_)
      rw [RingHom.mem_ker]
      have hv := congrArg (coeff v) hQ0
      rw [coeff_map, coeff_zero] at hv
      exact hv
    have hqne : algebraMap (MvPolynomial K k) Φ q ≠ 0 :=
      IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors (mem_nonZeroDivisors_of_ne_zero hq)
    have hP' : P = C (algebraMap (MvPolynomial K k) Φ q)⁻¹ * α Q := by
      rw [hQ, ← mul_assoc, ← C_mul, inv_mul_cancel₀ hqne, C_1, one_mul]
    rw [hP']
    exact Ideal.mul_mem_left _ _ hJ
  · rw [Ideal.map_le_iff_le_comap]
    intro p hp
    rw [RingHom.mem_ker] at hp
    rw [Ideal.mem_comap, RingHom.mem_ker, hΘa, hp, map_zero, map_zero]

end SheetDecomposition.PF
end
end

