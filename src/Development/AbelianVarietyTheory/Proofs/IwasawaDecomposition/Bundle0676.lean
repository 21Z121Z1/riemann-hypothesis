import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0601
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0659
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsFrameCover
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0621
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0628
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0637
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0649
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PullbackModelArcPeriod
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0613
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0121
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0658
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0630
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0657
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0041

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PolynomialGrowthOfSpanningCombinations
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor GlobalTheory.ShFam.Hor.LogCh
open scoped Matrix CategoryTheory.Obj Topology
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem growth_bound_of_spanning_combinations : ∀ (n g r : ℕ) (J : Type) [Fintype J] (R : Set (Fin n → ℂ)) (x : (Fin n → ℂ) → Fin r → Fin g → ℂ) (u : J → Fin r → ℝ), Submodule.span ℝ (Set.range u) = ⊤ → (∀ i, ∃ (C : ℝ) (k : ℕ), ∀ s ∈ R, ‖∑ m, (u i m : ℂ) • x s m‖ ≤ C * (1 + ‖s‖) ^ k) → ∃ (C : ℝ) (k : ℕ), ∀ s ∈ R, ‖x s‖ ≤ C * (1 + ‖s‖) ^ k := by
  intro n g r J _ R x u hspan hb
  choose C k hC using hb
  have hsingle : ∀ m : Fin r, ∃ a : J → ℝ, ∑ i, a i • u i = Pi.single m 1 := by
    intro m
    have hmem : (Pi.single m (1:ℝ) : Fin r → ℝ) ∈ Submodule.span ℝ (Set.range u) := by
      rw [hspan]; trivial
    exact (Submodule.mem_span_range_iff_exists_fun ℝ).1 hmem
  choose a ha using hsingle
  refine ⟨∑ m, ∑ i, |a m i| * max (C i) 0, ∑ i, k i, ?_⟩
  intro s hs
  have h1 : (1:ℝ) ≤ 1 + ‖s‖ := by linarith [norm_nonneg s]
  have hpow : ∀ i, (1 + ‖s‖) ^ (k i) ≤ (1 + ‖s‖) ^ (∑ j, k j) := fun i =>
    pow_le_pow_right₀ h1 (Finset.single_le_sum (fun j _ => Nat.zero_le (k j)) (Finset.mem_univ i))
  have hm : ∀ m, ‖x s m‖ ≤ (∑ i, |a m i| * max (C i) 0) * (1 + ‖s‖) ^ (∑ j, k j) := by
    intro m
    have hid : x s m = ∑ i, (a m i : ℂ) • ∑ m', (u i m' : ℂ) • x s m' := by
      have e := congrFun (ha m)
      simp only [Finset.smul_sum, smul_smul]
      rw [Finset.sum_comm]
      have hc : ∀ m', ∑ i, ((a m i : ℂ) * (u i m' : ℂ)) • x s m'
          = (((Pi.single m (1:ℝ) : Fin r → ℝ) m' : ℝ) : ℂ) • x s m' := by
        intro m'
        rw [← Finset.sum_smul]
        congr 1
        have h2 := e m'
        simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at h2
        rw [← h2]; push_cast; rfl
      rw [Finset.sum_congr rfl (fun m' _ => hc m')]
      rw [Finset.sum_eq_single m]
      · simp
      · intro b _ hb; simp [Pi.single_apply, hb]
      · intro h; exact absurd (Finset.mem_univ m) h
    rw [hid]
    calc ‖∑ i, (a m i : ℂ) • ∑ m', (u i m' : ℂ) • x s m'‖
        ≤ ∑ i, ‖(a m i : ℂ) • ∑ m', (u i m' : ℂ) • x s m'‖ := norm_sum_le _ _
      _ ≤ ∑ i, |a m i| * (max (C i) 0 * (1 + ‖s‖) ^ (∑ j, k j)) := by
        apply Finset.sum_le_sum; intro i _
        rw [norm_smul, Complex.norm_real, Real.norm_eq_abs]
        apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
        calc _ ≤ C i * (1 + ‖s‖) ^ (k i) := hC i s hs
          _ ≤ max (C i) 0 * (1 + ‖s‖) ^ (k i) :=
              mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
          _ ≤ max (C i) 0 * (1 + ‖s‖) ^ (∑ j, k j) :=
              mul_le_mul_of_nonneg_left (hpow i) (le_max_right _ _)
      _ = _ := by
        rw [Finset.sum_mul]; exact Finset.sum_congr rfl fun i _ => (_root_.mul_assoc _ _ _).symm
  have hnn : ∀ m, 0 ≤ ∑ i, |a m i| * max (C i) 0 := fun m =>
    Finset.sum_nonneg fun i _ => mul_nonneg (abs_nonneg _) (le_max_right _ _)
  refine (pi_norm_le_iff_of_nonneg (mul_nonneg (Finset.sum_nonneg fun m _ => hnn m) (by positivity))).2 fun m => ?_
  calc ‖x s m‖ ≤ _ := hm m
    _ ≤ (∑ m, ∑ i, |a m i| * max (C i) 0) * (1 + ‖s‖) ^ (∑ j, k j) := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact Finset.single_le_sum (f := fun m => ∑ i, |a m i| * max (C i) 0)
        (fun j _ => hnn j) (Finset.mem_univ m)

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PreModelChartTransition
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LocM GlobalTheory.ShFam.Pad GlobalTheory.ProjSpace GlobalTheory.FlagEmb
open Formalism.MainNotions.DIV.Cons (intO)

namespace GlobalTheory.FlagEmb.Uniq

theorem spMap_comp_eq {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap (g.comp f) = spMap g ≫ spMap f := by
  rw [← Spec.map_comp]
  rfl

theorem spMap_injective {A B : Type} [CommRing A] [CommRing B] {f g : A →+* B} (h : spMap f = spMap g) : f = g :=
  congrArg CommRingCat.Hom.hom (Spec.map_injective h)

theorem pt_congr {R A : Type} [CommRing R] [CommRing A] {N : ℕ} {c c' : R →+* A} (h : c = c') (v : Fin (N + 1) → A)
    (hv hv' : Ideal.span (Set.range v) = ⊤) : pt c v hv = pt c' v hv' := by
  subst h
  rfl

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {Xo : ∀ l : Level H, Moduli Dw l} {p : ℕ} {W : ValuationSubring ℂ} {Y : LocalSystem Xo p W} {i₀ : Idx H p}
  {Z : Pre Y i₀} {L : FinLB (Y Z.i).X} {aff : ∀ i, IsAffineOpen (L.U i)} {M : ℕ} {crd : Crd (Y Z.i).t L M}
  {ι : Fin Z.m → Fin L.n} {ρ : ∀ a, Γ((Y Z.i).X, L.U (ι a)) →+* Γ(Z.X, (Z.U a).1)}
  {g : ∀ en : En Dw.mult, Z.X ⟶ PSpace (Z.i.c.V W) (plN M en.1)}

theorem plk_adapted (h : Comparison₂ Z L aff crd ι ρ g) {k : Type} [Field k] (a : Fin Z.m) (i : Fin L.n)
    (φ : Γ(Z.X, (Z.U a).1) →+* k) (ψ : Γ((Y Z.i).X, L.U i) →+* k) (u : Vecs Dw (Y Z.i).t k)
    (hψ : spMap ψ ≫ (aff i).fromSpec = (spMap φ ≫ Z.chart a) ≫ Z.π)
    (hf : IsFrame (Y Z.i).t (φ.comp (Z.alg a)) ((spMap φ ≫ Z.chart a) ≫ Z.π) u)
    (hs : SameFlag Z.ty (Y Z.i).t ((spMap φ ≫ Z.chart a) ≫ Z.π) ((Z.fr a).bc φ) u) (en : En Dw.mult) :
    ∃ hu, (spMap φ ≫ Z.chart a) ≫ g en = pt (φ.comp ((Z.alg a).comp (Z.i.c.V W).subtype))
      (plk (fun z : Let Dw.mult => crd i k ψ (u z.1 z.2)) en.2.1) hu := by
  rw [Category.assoc] at hψ hf hs
  rw [h.ty] at hs
  obtain ⟨hu, e⟩ := GlobalTheory.T.pre_model_chart_gluing E H Dw Xo p W Y i₀ Z L aff M crd ι ρ g h k a i φ ψ hψ en
  have hfr := h.frame a k φ
  obtain ⟨d, hd⟩ := (GlobalTheory.T.frames_agree_on_lie_embedding_chart E H Dw _ _ _ _ L aff M crd h.emb i k ψ _ _ _ _ _ hψ hfr hf).1.1 hs
  have hli := (GlobalTheory.T.frames_agree_on_lie_embedding_chart E H Dw _ _ _ _ L aff M crd h.emb i k ψ _ _ _ _ _ hψ hf hf).2.1
  have hne := GlobalTheory.T.diag_ne_zero_of_triangular_independent _ _ k _ _ _ d hli hd
  have hp := GlobalTheory.FlagEmb.plk_tri _ _ k M _ _ d _ _ hd en.2.2
  have h0 : (∏ l, d (en.2.1 l)) ≠ 0 := Finset.prod_ne_zero_iff.2 fun l _ => hne _
  have hp' : plk (fun z : Let Dw.mult => crd i k ψ (u z.1 z.2)) en.2.1 = Units.mk0 _ h0 • _ := hp
  refine ⟨hp' ▸ span_range_units_smul hu _, ?_⟩
  rw [Category.assoc, e]
  exact (pt_eq_pt_iff _ _ _).2 ⟨_, hp'⟩

theorem spMap_alg (h : Comparison₂ Z L aff crd ι ρ g) {k : Type} [Field k] (a : Fin Z.m) (φ : Γ(Z.X, (Z.U a).1) →+* k) :
    spMap (φ.comp ((Z.alg a).comp (Z.i.c.V W).subtype)) = ((spMap φ ≫ Z.chart a) ≫ Z.π) ≫ (Y Z.i).s := by
  rw [spMap_comp_eq, ← h.alg_s a]
  simp only [Category.assoc]

end GlobalTheory.FlagEmb.Uniq

namespace GlobalTheory.FlagEmb

open Uniq in

theorem flagAt_unique : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (Xo : ∀ l : Level H, Moduli Dw l) (p : ℕ) (W : ValuationSubring ℂ) (Y : LocalSystem Xo p W) (i₀ : Idx H p) (Z : Pre Y i₀) (L : FinLB (Y Z.i).X) (aff : ∀ i, IsAffineOpen (L.U i)) (M : ℕ) (crd : Crd (Y Z.i).t L M) (ι : Fin Z.m → Fin L.n) (ρ : ∀ a, Γ((Y Z.i).X, L.U (ι a)) →+* Γ(Z.X, (Z.U a).1)) (g : ∀ en : En Dw.mult, Z.X ⟶ PSpace (Z.i.c.V W) (plN M en.1)), Comparison₂ Z L aff crd ι ρ g → ∀ (k : Type) [Field k] (w w' : Sp k ⟶ Z.X) (u : Vecs Dw (Y Z.i).t k), w ≫ Z.π = w' ≫ Z.π → Z.FlagAt w u → Z.FlagAt w' u → w = w' := by
  intro E _ _ _ H Dw Xo p W Y i₀ Z L aff M crd ι ρ g h k _ w w' u hπ ⟨a, φ, hw, hf, hs⟩ ⟨a', φ', hw', hf', hs'⟩
  subst hw hw'
  have hψ : spMap (φ.comp (ρ a)) ≫ (aff (ι a)).fromSpec = (spMap φ ≫ Z.chart a) ≫ Z.π := by
    rw [spMap_comp_eq, Category.assoc, h.res, Category.assoc]
  refine h.inj k _ _ ?_ hπ fun en => ?_
  · rintro _ ⟨y, rfl⟩
    rw [← h.cover]
    refine Set.mem_iUnion.2 ⟨a, ?_⟩
    rw [← (Z.U a).2.range_fromSpec]
    exact ⟨spMap φ y, by simp [Pre.chart]⟩
  · obtain ⟨hu, e⟩ := plk_adapted h a _ φ _ u hψ hf hs en
    obtain ⟨hu', e'⟩ := plk_adapted h a' _ φ' _ u (hψ.trans hπ) hf' hs' en
    rw [e, e']
    refine pt_congr (spMap_injective ?_) _ _ _
    rw [spMap_alg h, spMap_alg h, hπ]

end GlobalTheory.FlagEmb
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PullbackAnalytic
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor GlobalTheory.ShFam.Hor.LogCh
open scoped Matrix CategoryTheory.Obj Topology
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

namespace GlobalTheory.ShFam.Hor.LogCh

theorem IsLatFam.pullback_analytic : ∀ (m n g : ℕ) (B : Set (Fin n → ℂ)) (B' : Set (Fin m → ℂ))
    (K : (Fin n → ℂ) → Set (Fin g → ℂ)) (φ : (Fin m → ℂ) → Fin n → ℂ),
    GlobalTheory.ShFam.Hor.LogCh.IsLatFam B K → IsOpen B' → AnalyticOnNhd ℂ φ B' → Set.MapsTo φ B' B →
      GlobalTheory.ShFam.Hor.LogCh.IsLatFam B' (fun b => K (φ b)) := by
  intro m n g B B' K φ hK hB' hφ hmaps
  obtain ⟨_, h2, h3, h4⟩ := hK
  let Ψ : (Fin m → ℂ) × (Fin g → ℂ) → (Fin n → ℂ) × (Fin g → ℂ) := fun q => (φ q.1, q.2)
  refine ⟨hB', fun b hb => h2 (φ b) (hmaps hb), ?_, ?_⟩
  · have hcont : ContinuousOn Ψ (B' ×ˢ (Set.univ : Set (Fin g → ℂ))) :=
      (hφ.continuousOn.comp continuousOn_fst (fun q hq => hq.1)).prodMk continuousOn_snd
    have hopen := hcont.isOpen_inter_preimage (hB'.prod isOpen_univ) h3
    convert hopen using 1
    ext q
    simp only [Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_prod, Set.mem_univ, and_true, Set.mem_preimage, Ψ]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨h1, hmaps h1, h2⟩
    · rintro ⟨h1, _, h2⟩
      exact ⟨h1, h2⟩
  · intro b₀ hb₀ w₀ hw₀
    obtain ⟨ζ, hζ0, hζa, hev⟩ := h4 (φ b₀) (hmaps hb₀) w₀ hw₀
    refine ⟨fun b => ζ (φ b), hζ0, hζa.comp (hφ b₀ hb₀), ?_⟩
    have hΨ : ContinuousAt Ψ (b₀, w₀) :=
      ((hφ b₀ hb₀).continuousAt.comp continuousAt_fst).prodMk continuousAt_snd
    exact hΨ.tendsto.eventually hev

end GlobalTheory.ShFam.Hor.LogCh
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PullbackModelArcPeriodStatement
section
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.TorRef

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pullback_model_arc_period : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l)
    (c : Coeff l) (p : ℕ) (W : ValuationSubring ℂ), p.Prime → (p : ℂ) ∈ W.nonunits →
    ∀ (Z : Model Xo c (algebraMap (𝓞 c.F) c.F)) (Y : Model Xo c (c.V W).subtype) (bV : 𝓞 c.F →+* c.V W)
    (hbV : ∀ x, ((bV x : c.V W) : c.F) = (x : c.F))
    (f : pullback Z.s (spMap bV) ⟶ Y.X) (t : SAB H (pullback Z.s (spMap bV)))
    (m₁ : SABMap t Z.t (pullback.fst Z.s (spMap bV))) (m₂ : SABMap t Y.t f),
    f ≫ Y.s = pullback.snd Z.s (spMap bV) →
    (∀ a : Xo.XF c ⟶ pullback Z.s (spMap bV), a ≫ pullback.fst Z.s (spMap bV) = Z.j → a ≫ f = Y.j) →
    (∀ (T : Scheme.{0}) (g : T ⟶ t.G.left) (g₁ : T ⟶ Z.oF.t.G.left) (g₂ : T ⟶ Y.oF.t.G.left),
      g ≫ m₁.φ = g₁ ≫ Z.m.φ → g₁ ≫ Z.m0.toSABMap.φ = g₂ ≫ Y.m0.toSABMap.φ → g₁ ≫ Z.oF.t.G.hom = g₂ ≫ Y.oF.t.G.hom →
      g ≫ m₂.φ = g₂ ≫ Y.m.φ) →
    ∀ (φ : InvFun (𝓞 E)) (m : ℕ) (BD : GlobalTheory.EffCartierData Z.X),
      (∀ (n : ℕ) (k : ℕ) (B : (Fin n → 𝓞 E) → (Fin n → 𝓞 E) → ℝ), φ.toFun n (fun a b => k * B a b) = k * φ.toFun n B) →
      IsPol φ m Z BD →
      ∀ (O' : Type) [CommRing O'] [IsDomain O'] [CharZero O'] (b' : c.V W →+* O') (ϖ : O')
        (a : ArcIn D l (algebraMap (𝓞 c.F) c.F) O' (b'.comp bV)) (χ₀ : Sp (PowerSeries O') ⟶ Y.X),
        IsArcBase O' ϖ → IsArcChart Y (GlobalTheory.PolArc.moveV bV hbV b' a) ϖ χ₀ →
        ∀ x₀ : Sp (FractionRing (PowerSeries O')) ⟶ Xo.XF c, Out.jK (PowerSeries O') ≫ χ₀ = x₀ ≫ Y.j →
        ∃ n : ℕ, ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], CDvr V →
    ∀ (ψ : PowerSeries O' →+* V) (gam : FractionRing (PowerSeries O') →+* FractionRing V),
    (∀ r, gam (algebraMap (PowerSeries O') _ r) = algebraMap V _ (ψ r)) →
    ∀ χ : Sp V ⟶ Z.X, spMap gam ≫ x₀ ≫ Z.j = Out.jK V ≫ χ → GlobalTheory.LocM.idlAlong BD.idealSheaf χ = Ideal.span {ψ PowerSeries.X ^ n} := by
  first | exact @GlobalTheory.ArcOrder.main | exact GlobalTheory.ArcOrder.main | (intros; apply GlobalTheory.ArcOrder.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PullbackModelArcPolarizationStatement
section
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.TorRef

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pullback_model_arc_polarization : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l)
    (c : Coeff l) (p : ℕ) (W : ValuationSubring ℂ), p.Prime → (p : ℂ) ∈ W.nonunits →
    ∀ (Z : Model Xo c (algebraMap (𝓞 c.F) c.F)) (Y : Model Xo c (c.V W).subtype) (bV : 𝓞 c.F →+* c.V W)
    (hbV : ∀ x, ((bV x : c.V W) : c.F) = (x : c.F))
    (f : pullback Z.s (spMap bV) ⟶ Y.X) (t : SAB H (pullback Z.s (spMap bV)))
    (m₁ : SABMap t Z.t (pullback.fst Z.s (spMap bV))) (m₂ : SABMap t Y.t f),
    f ≫ Y.s = pullback.snd Z.s (spMap bV) →
    (∀ a : Xo.XF c ⟶ pullback Z.s (spMap bV), a ≫ pullback.fst Z.s (spMap bV) = Z.j → a ≫ f = Y.j) →
    (∀ (T : Scheme.{0}) (g : T ⟶ t.G.left) (g₁ : T ⟶ Z.oF.t.G.left) (g₂ : T ⟶ Y.oF.t.G.left),
      g ≫ m₁.φ = g₁ ≫ Z.m.φ → g₁ ≫ Z.m0.toSABMap.φ = g₂ ≫ Y.m0.toSABMap.φ → g₁ ≫ Z.oF.t.G.hom = g₂ ≫ Y.oF.t.G.hom →
      g ≫ m₂.φ = g₂ ≫ Y.m.φ) →
      ∀ (O' : Type) [CommRing O'] [IsDomain O'] [CharZero O'] (b' : c.V W →+* O') (ϖ : O')
        (a : ArcIn D l (algebraMap (𝓞 c.F) c.F) O' (b'.comp bV)) (χ₀ : Sp (PowerSeries O') ⟶ Y.X),
        IsArcBase O' ϖ → IsArcChart Y (GlobalTheory.PolArc.moveV bV hbV b' a) ϖ χ₀ →
        ∀ x₀ : Sp (FractionRing (PowerSeries O')) ⟶ Xo.XF c, Out.jK (PowerSeries O') ≫ χ₀ = x₀ ≫ Y.j →
        ∃ e : LB.Gen ((GlobalTheory.FlagMod.detOm Z).pull (x₀ ≫ Z.j)), e.IsGen ∧ GlobalTheory.TraitGen.ExtAt (GlobalTheory.FlagMod.detOm Z) (x₀ ≫ Z.j) e := by
  first | exact @GlobalTheory.TraitGen.exists_detOm_gen_extends | exact GlobalTheory.TraitGen.exists_detOm_gen_extends | (intros; apply GlobalTheory.TraitGen.exists_detOm_gen_extends <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PullbackModelArcSection
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.TorRef

namespace GlobalTheory.PolArc

section SlopeTestRemainingChoices

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {Xo : Moduli D l} {c : Coeff l} {W : ValuationSubring ℂ}

theorem mono_j_of_valuationSubring (V : ValuationSubring c.F) (Y : Model Xo c V.subtype) : Mono Y.j := by
  have : IsPreimmersion (spMap V.subtype) := IsPreimmersion.of_isLocalization (nonZeroDivisors V) (S := c.F)
  have h1 : IsPreimmersion (pullback.fst Y.s (spMap V.subtype)) :=
    MorphismProperty.of_isPullback (P := @IsPreimmersion) (IsPullback.of_hasPullback _ _).flip this
  have := Y.jQ_open
  unfold Model.j
  infer_instance

theorem exists_factor (Z : Model Xo c (algebraMap (𝓞 c.F) c.F)) (bV : 𝓞 c.F →+* c.V W)
    (hbV : ∀ x, ((bV x : c.V W) : c.F) = (x : c.F)) {K : Type} [Field K] (x : Sp K ⟶ pullback Z.s (spMap bV))
    (hx : (x ≫ pullback.fst Z.s (spMap bV)) (default : PrimeSpectrum K) ∈ Set.range Z.j) :
    ∃ y : Sp K ⟶ Xo.XF c, y ≫ Z.j = x ≫ pullback.fst Z.s (spMap bV) ∧
      (y ≫ pullback.snd _ _) ≫ spMap (c.V W).subtype = x ≫ pullback.snd Z.s (spMap bV) := by
  haveI : NumberField c.F := { to_finiteDimensional := c.fin }
  have hβ : (c.V W).subtype.comp bV = algebraMap (𝓞 c.F) c.F := RingHom.ext hbV
  have hsp : spMap (c.V W).subtype ≫ spMap bV = spMap (algebraMap (𝓞 c.F) c.F) := by
    rw [← hβ]; exact (Geo.Tor.spMap_comp _ _).symm
  obtain ⟨φ, hφ⟩ : ∃ φ : c.V W →+* K, x ≫ pullback.snd Z.s (spMap bV) = spMap φ :=
    ⟨(Spec.preimage (x ≫ pullback.snd Z.s (spMap bV))).hom,
      (Spec.map_preimage (x ≫ pullback.snd Z.s (spMap bV))).symm⟩
  obtain ⟨q, hq⟩ := hx
  have e0 : (x ≫ pullback.fst Z.s (spMap bV)) ≫ Z.s = spMap (φ.comp bV) := by
    rw [Category.assoc, pullback.condition, ← Category.assoc, hφ, Geo.Tor.spMap_comp]
  have hinj : Function.Injective (φ.comp bV) := by
    obtain ⟨r, e1⟩ : ∃ r : PrimeSpectrum c.F, PrimeSpectrum.comap (φ.comp bV) default =
        PrimeSpectrum.comap (algebraMap (𝓞 c.F) c.F) r := by
      have e2 : ((x ≫ pullback.fst Z.s (spMap bV)) ≫ Z.s) (default : PrimeSpectrum K) = (Z.j ≫ Z.s) q :=
        (congrArg Z.s hq).symm
      rw [e0, Model.j_s] at e2
      exact ⟨_, e2⟩
    refine (injective_iff_map_eq_zero _).2 fun v hv => ?_
    have h1 : v ∈ (PrimeSpectrum.comap (φ.comp bV) default).asIdeal := by
      rw [PrimeSpectrum.comap_asIdeal, Ideal.mem_comap, hv]; exact zero_mem _
    rw [e1, PrimeSpectrum.comap_asIdeal, Ideal.mem_comap, Ideal.eq_bot_of_prime r.asIdeal] at h1
    exact RingOfIntegers.ext h1
  let ψ : c.F →+* K := IsFractionRing.lift hinj
  have hψ : ∀ a, ψ (algebraMap (𝓞 c.F) c.F a) = φ (bV a) := fun a => IsFractionRing.lift_algebraMap hinj a
  have hψφ : ψ.comp (c.V W).subtype = φ := by
    ext v
    obtain ⟨a, b, hb, e⟩ := IsFractionRing.div_surjective (A := 𝓞 c.F) (v : c.F)
    have hb0 : algebraMap (𝓞 c.F) c.F b ≠ 0 :=
      IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hb
    have h2 : (v : c.F) * algebraMap (𝓞 c.F) c.F b = algebraMap (𝓞 c.F) c.F a := by
      rw [← e]; field_simp
    have e' : v * bV b = bV a := Subtype.ext (by
      have := h2
      simpa [hbV] using this)
    have h1 : φ v * φ (bV b) = φ (bV a) := by rw [← map_mul, e']
    have h3 : ψ (v : c.F) * φ (bV b) = φ (bV a) := by rw [← hψ, ← hψ, ← map_mul, h2]
    have hne : φ (bV b) ≠ 0 := fun h => hb0 (by
      have : b = 0 := hinj (by simpa using h)
      simp [this])
    exact mul_right_cancel₀ hne (h3.trans h1.symm)
  have hs : (x ≫ pullback.fst Z.s (spMap bV)) ≫ Z.s = spMap ψ ≫ spMap (algebraMap (𝓞 c.F) c.F) := by
    rw [e0, ← hsp, ← Category.assoc, ← Geo.Tor.spMap_comp, hψφ, Geo.Tor.spMap_comp]
  let z' : Sp K ⟶ pullback Z.s (spMap (algebraMap (𝓞 c.F) c.F)) := pullback.lift _ _ hs
  have hz₁ : z' ≫ pullback.fst _ _ = x ≫ pullback.fst Z.s (spMap bV) := pullback.lift_fst _ _ _
  have hz₂ : z' ≫ pullback.snd _ _ = spMap ψ := pullback.lift_snd _ _ _
  have := Z.jQ_open
  have hr : Set.range z' ⊆ Set.range Z.jQ := by
    rintro _ ⟨p, rfl⟩
    obtain rfl : p = (default : PrimeSpectrum K) := Subsingleton.elim (α := PrimeSpectrum K) _ _
    rw [← Z.ab_gen]
    have h₁ : Z.jQ q ∈ pullback.fst Z.s (spMap (algebraMap (𝓞 c.F) c.F)) ⁻¹' abLocus Z.t.G :=
      Z.ab_gen ▸ ⟨q, rfl⟩
    have h₂ : Z.j q ∈ abLocus Z.t.G := h₁
    rw [hq, ← hz₁] at h₂
    exact h₂
  refine ⟨IsOpenImmersion.lift Z.jQ z' hr, ?_, ?_⟩
  · rw [Model.j, ← Category.assoc, IsOpenImmersion.lift_fac, hz₁]
  · rw [← Z.jQ_over, ← Category.assoc, IsOpenImmersion.lift_fac, hz₂, hφ, ← Geo.Tor.spMap_comp, hψφ]

end SlopeTestRemainingChoices

theorem eq_of_comp_eq_of_generic : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l)
    (c : Coeff l) (p : ℕ) (W : ValuationSubring ℂ), p.Prime → (p : ℂ) ∈ W.nonunits →
    ∀ (Z : Model Xo c (algebraMap (𝓞 c.F) c.F)) (Y : Model Xo c (c.V W).subtype) (bV : 𝓞 c.F →+* c.V W)
    (hbV : ∀ x, ((bV x : c.V W) : c.F) = (x : c.F))
    (f : pullback Z.s (spMap bV) ⟶ Y.X) (t : SAB H (pullback Z.s (spMap bV)))
    (m₁ : SABMap t Z.t (pullback.fst Z.s (spMap bV))) (m₂ : SABMap t Y.t f),
    f ≫ Y.s = pullback.snd Z.s (spMap bV) →
    (∀ a : Xo.XF c ⟶ pullback Z.s (spMap bV), a ≫ pullback.fst Z.s (spMap bV) = Z.j → a ≫ f = Y.j) →
    (∀ (T : Scheme.{0}) (g : T ⟶ t.G.left) (g₁ : T ⟶ Z.oF.t.G.left) (g₂ : T ⟶ Y.oF.t.G.left),
      g ≫ m₁.φ = g₁ ≫ Z.m.φ → g₁ ≫ Z.m0.toSABMap.φ = g₂ ≫ Y.m0.toSABMap.φ → g₁ ≫ Z.oF.t.G.hom = g₂ ≫ Y.oF.t.G.hom →
      g ≫ m₂.φ = g₂ ≫ Y.m.φ) →
    ∀ (R : Type) [CommRing R] [IsDomain R] (g₁ g₂ : Sp R ⟶ pullback Z.s (spMap bV)),
      (∀ x : Sp R, x.asIdeal = ⊥ → pullback.fst Z.s (spMap bV) (g₁ x) ∈ Set.range Z.j) → g₁ ≫ f = g₂ ≫ f → g₁ = g₂ := by
  intro E _ _ _ H D l Xo c p W hp hW Z Y bV hbV f t m₁ m₂ hover hj hc R _ _ g₁ g₂ hgen hgf
  have hrange := GlobalTheory.T.pullback_model_arc_comparison E H D l Xo c p W hp hW Z Y bV hbV f t m₁ m₂ hover hj hc
  have hη : (jK R (default : PrimeSpectrum (FractionRing R))).asIdeal = ⊥ :=
    by
    rw [Subsingleton.elim (default : PrimeSpectrum (FractionRing R)) ⊥]
    exact (RingHom.injective_iff_ker_eq_bot _).1 (IsFractionRing.injective R (FractionRing R))
  have h₁ : ((jK R ≫ g₁) ≫ pullback.fst Z.s (spMap bV)) (default : PrimeSpectrum (FractionRing R)) ∈
      Set.range Z.j := hgen _ hη
  have hf : f ((jK R ≫ g₂) (default : PrimeSpectrum (FractionRing R))) =
      f ((jK R ≫ g₁) (default : PrimeSpectrum (FractionRing R))) :=
    congrArg (fun u : Sp R ⟶ Y.X => u (jK R (default : PrimeSpectrum (FractionRing R)))) hgf.symm
  have h₂ : ((jK R ≫ g₂) ≫ pullback.fst Z.s (spMap bV)) (default : PrimeSpectrum (FractionRing R)) ∈
      Set.range Z.j := (hrange _).2 (hf ▸ (hrange _).1 h₁)
  obtain ⟨y₁, a₁, b₁⟩ := exists_factor Z bV hbV (jK R ≫ g₁) h₁
  obtain ⟨y₂, a₂, b₂⟩ := exists_factor Z bV hbV (jK R ≫ g₂) h₂
  have hβ : (c.V W).subtype.comp bV = algebraMap (𝓞 c.F) c.F := RingHom.ext hbV
  have hsp : spMap (c.V W).subtype ≫ spMap bV = spMap (algebraMap (𝓞 c.F) c.F) := by
    rw [← hβ]; exact (Geo.Tor.spMap_comp _ _).symm
  let a : Xo.XF c ⟶ pullback Z.s (spMap bV) :=
    pullback.lift Z.j (pullback.snd _ _ ≫ spMap (c.V W).subtype) (by
      rw [Model.j_s, Category.assoc, hsp])
  have ha : a ≫ f = Y.j := hj a (pullback.lift_fst _ _ _)
  have key : ∀ (y : Sp (FractionRing R) ⟶ Xo.XF c) (x : Sp (FractionRing R) ⟶ pullback Z.s (spMap bV)),
      y ≫ Z.j = x ≫ pullback.fst Z.s (spMap bV) →
      (y ≫ pullback.snd _ _) ≫ spMap (c.V W).subtype = x ≫ pullback.snd Z.s (spMap bV) → y ≫ a = x := by
    intro y x e₁ e₂
    refine pullback.hom_ext ?_ ?_
    · rw [Category.assoc, pullback.lift_fst, e₁]
    · rw [Category.assoc, pullback.lift_snd, ← Category.assoc, e₂]
  have k₁ := key y₁ _ a₁ b₁
  have k₂ := key y₂ _ a₂ b₂
  have := mono_j_of_valuationSubring (c.V W) Y
  have hy : y₁ = y₂ := by
    rw [← cancel_mono Y.j, ← ha, ← Category.assoc, ← Category.assoc, k₁, k₂, Category.assoc, Category.assoc, hgf]
  have := isProper_toroidalModel_structureMap Z
  have : IsDominant (jK R) := ⟨(PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical _).2
    (((RingHom.injective_iff_ker_eq_bot _).1 (IsFractionRing.injective R (FractionRing R))).le.trans bot_le)⟩
  refine ext_of_isDominant_of_isSeparated (pullback.snd Z.s (spMap bV)) ?_ (jK R) ?_
  · rw [← hover, ← Category.assoc, ← Category.assoc, hgf]
  · rw [← k₁, ← k₂, hy]

end GlobalTheory.PolArc
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PunctPolydiscUniversalCoverOpenConvexExpAnalytic
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor GlobalTheory.ShFam.Hor.LogCh
open scoped Matrix CategoryTheory.Obj Topology
attribute [local instance] Over.cartesianMonoidalCategory

theorem GlobalTheory.logDom_chart_props : ∀ (n a : ℕ), IsOpen (GlobalTheory.ShFam.Hor.logDom n a) ∧ Convex ℝ (GlobalTheory.ShFam.Hor.logDom n a) ∧ (∀ s, AnalyticAt ℂ (GlobalTheory.ShFam.Hor.logExp a : (Fin n → ℂ) → Fin n → ℂ) s) ∧ Set.MapsTo (GlobalTheory.ShFam.Hor.logExp a) (GlobalTheory.ShFam.Hor.logDom n a) (Metric.ball (0 : Fin n → ℂ) 1) := by
  intro n a
  have hEq : GlobalTheory.ShFam.Hor.logDom n a = ⋂ k : Fin n, (fun s : Fin n → ℂ => s k) ⁻¹' (if (k : ℕ) < a then {z : ℂ | z.re < 0} else Metric.ball (0 : ℂ) 1) := by
    ext s
    simp only [GlobalTheory.ShFam.Hor.logDom, Set.mem_setOf_eq, Set.mem_iInter, Set.mem_preimage]
    refine forall_congr' fun k => ?_
    split_ifs <;> simp [Metric.mem_ball, dist_zero_right]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hEq]
    refine isOpen_iInter_of_finite fun k => ?_
    refine IsOpen.preimage (continuous_apply k) ?_
    split_ifs
    · exact isOpen_lt Complex.continuous_re continuous_const
    · exact Metric.isOpen_ball
  · rw [hEq]
    refine convex_iInter fun k => ?_
    have hc : Convex ℝ (if (k : ℕ) < a then {z : ℂ | z.re < 0} else Metric.ball (0 : ℂ) 1) := by
      split_ifs
      · exact convex_halfSpace_lt (f := Complex.re) Complex.reLm.isLinear 0
      · exact convex_ball 0 1
    exact hc.linear_preimage (LinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℂ) k)
  · intro s
    rw [analyticAt_pi_iff]
    intro k
    show AnalyticAt ℂ (fun s : Fin n → ℂ => if (k : ℕ) < a then Complex.exp (s k) else s k) s
    have hp : AnalyticAt ℂ (fun s : Fin n → ℂ => s k) s :=
      (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin n => ℂ) k).analyticAt s
    split_ifs
    · exact analyticAt_cexp.comp hp
    · exact hp
  · intro s hs
    rw [Metric.mem_ball, dist_zero_right, pi_norm_lt_iff one_pos]
    intro k
    have hk := hs k
    simp only [GlobalTheory.ShFam.Hor.logExp]
    split_ifs at hk ⊢ with h
    · rw [Complex.norm_exp]
      exact Real.exp_lt_one_iff.mpr hk
    · exact hk
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RatLinearIndependentCoordsOfRealIndependent
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor GlobalTheory.ShFam.Hor.LogCh
open scoped Matrix CategoryTheory.Obj Topology
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem rowsInd_rat_of_real : ∀ (g r r₀ : ℕ) (lam : Fin r → Fin g → ℂ) (u : Fin r₀ → Fin g → ℂ) (A : Fin r₀ → Fin r → ℤ), LinearIndependent ℝ u → (∀ i, u i = ∑ m, A i m • lam m) → LinearIndependent ℚ (fun i j => (A i j : ℚ)) := by
  intro g r r₀ lam u A hu hA
  rw [Fintype.linearIndependent_iff] at hu ⊢
  intro c hc i
  have hc' : ∀ m, ∑ i, (c i : ℝ) * (A i m : ℝ) = 0 := by
    intro m
    have h1 := congrFun hc m
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at h1
    have h2 := congrArg (Rat.cast : ℚ → ℝ) h1
    push_cast at h2
    exact h2
  have hsum : ∑ i, (c i : ℝ) • u i = 0 := by
    have e : ∀ i, (c i : ℝ) • u i = ∑ m, ((c i : ℝ) * (A i m : ℝ)) • lam m := by
      intro i
      rw [hA i, Finset.smul_sum]
      refine Finset.sum_congr rfl (fun m _ => ?_)
      rw [← Int.cast_smul_eq_zsmul ℝ, smul_smul]
    simp_rw [e]
    rw [Finset.sum_comm]
    simp_rw [← Finset.sum_smul, hc', zero_smul, Finset.sum_const_zero]
  have h3 := hu (fun i => (c i : ℝ)) hsum i
  exact_mod_cast h3

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SabMapExtendsDenseStatement
section
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.TorRef
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sabMap_extends_dense : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (X Z : GMod Xo c) (π : Z.X ⟶ X.X), Z.j ≫ π = X.j → ∀ (R' : Type) [CommRing R'] [IsDomain R'] [IsLocalRing R'] (ξ' : Sp R' ⟶ Z.X) (t' : SAB H (Sp R')), IsCN R' → Dense (ξ' ⁻¹' Set.range Z.j) → SABMap t' X.t (ξ' ≫ π) → Nonempty (SABMap t' Z.t ξ') := by
  first | exact @GlobalTheory.TorRef.TriplePull.sab_of_chart | exact GlobalTheory.TorRef.TriplePull.sab_of_chart | (intros; apply GlobalTheory.TorRef.TriplePull.sab_of_chart <;> assumption)
end

