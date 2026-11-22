import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3612
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2811
import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle0001
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0046
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0005
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0016
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0015
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1203
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1226
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3599
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0079
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2600
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2922
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3608
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3448

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedThetaSumZetaExponentIndependentMemberStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.Poinc.Sep

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twistedThetaSum_zeta_exponent_independent_member : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (Z : Scheme.{0}) (i : F.X ⟶ Z) (X₁ : Setup F W i) (z₁ : X₁.M.Z) (act : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)) (x₀ : X₁.S.Gam), X₁.M.Div X₁.S.th x₀ z₁ → ∀ sg : ℤˣ, TwistAtEach X₁ z₁ act x₀ sg → (∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (ev : X₁.M.Z.presheaf.stalk z₁ →+* V) (X : Type) [AddCommGroup X] (m : ℕ) (t : Fin m → V) (δ : Fin m → LinearMap.BilinForm ℤ X) (𝔪 : UMem X₁ z₁ act V ev X t δ) (τ : X₁.S.Gam) (χ : Multiplicative 𝔪.D.toPre.X →* (FractionRing V)ˣ), χ ^ (X₁.S.r * X₁.S.N) = 1 → (∀ g₀ : GtPtF 𝔪.D.toPre (FractionRing V), IsTor χ g₀ → ∃ (p : QkPt 𝔪.D.toPre (FractionRing V) (X₁.S.r * X₁.S.N)) (x : TFK (R := V) (FractionRing V) ⟶ 𝔪.A.A), p.y = 0 ∧ p.g = g₀ ∧ QkToAkU 𝔪.U.toUnifPre (FractionRing V) (X₁.S.r * X₁.S.N) p x ∧ x.left ≫ 𝔪.φ = spMap 𝔪.yK ≫ (X₁.ρ.pt τ).left) → (∀ a mu, 𝔪.YY a mu → ((χ (Multiplicative.ofAdd (𝔪.e₈ mu)) : (FractionRing V)ˣ) : FractionRing V) = 𝔪.yK (algebraMap X₁.o₁ X₁.S.R (X₁.S.ζ ^ (X₁.S.r * X₁.S.N * (((sg : ℤˣ) : ℤ) • eStd X₁.S.g _ τ a).val))))) → ∀ (V₁ : Type) [CommRing V₁] [IsDomain V₁] [IsLocalRing V₁] (ev₁ : X₁.M.Z.presheaf.stalk z₁ →+* V₁) (Y₁ : Type) [AddCommGroup Y₁] (m₁ : ℕ) (t₁ : Fin m₁ → V₁) (δ₁ : Fin m₁ → LinearMap.BilinForm ℤ Y₁) (𝔪₁ : UMem X₁ z₁ act V₁ ev₁ Y₁ t₁ δ₁) (C₁ : Type) (lab₁ : C₁ → X₁.S.Gam), (∀ c, lab₁ c ∈ X₁.S.HH X₁.M z₁) → ∀ T₁ : (Fin 8 → Y₁) → C₁ → V₁, 𝔪₁.Terms x₀ lab₁ T₁ → ∀ c₁ : C₁, ∀ (V₂ : Type) [CommRing V₂] [IsDomain V₂] [IsLocalRing V₂] (ev₂ : X₁.M.Z.presheaf.stalk z₁ →+* V₂) (Y₂ : Type) [AddCommGroup Y₂] (m₂ : ℕ) (t₂ : Fin m₂ → V₂) (δ₂ : Fin m₂ → LinearMap.BilinForm ℤ Y₂) (𝔪₂ : UMem X₁ z₁ act V₂ ev₂ Y₂ t₂ δ₂) (C₂ : Type) (lab₂ : C₂ → X₁.S.Gam), (∀ c, lab₂ c ∈ X₁.S.HH X₁.M z₁) → ∀ T₂ : (Fin 8 → Y₂) → C₂ → V₂, 𝔪₂.Terms x₀ lab₂ T₂ → ∀ c₂ : C₂, lab₁ c₁ = lab₂ c₂ → ∀ τ ∈ X₁.S.TT X₁.M z₁, ∀ e₁ e₂ : ℕ, TwistSum X₁ z₁ act x₀ 𝔪₁ lab₁ T₁ sg c₁ τ e₁ → TwistSum X₁ z₁ act x₀ 𝔪₂ lab₂ T₂ sg c₂ τ e₂ → (∃ r : X₁.M.Z.presheaf.stalk z₁, X₁.M.stalkHom z₁ r = X₁.S.th (lab₁ c₁ + τ) / X₁.S.th x₀ ∧ ev₁ r ≠ 0) → TwistSum X₁ z₁ act x₀ 𝔪₂ lab₂ T₂ sg c₂ τ e₁ := by
  first | exact @GlobalTheory.Poinc.Sep.twistSum_indep | exact GlobalTheory.Poinc.Sep.twistSum_indep | (intros; apply GlobalTheory.Poinc.Sep.twistSum_indep <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwoPointInductionKltPairSeparation
section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep

namespace GlobalTheory.PairStep

theorem add_le_sum_Icc_of_lt (h : ℕ → ℚ) (ε : ℚ) (hpos : ∀ e, 0 < h e + ε) {n i j : ℕ}
    (hij : i < j) (hjn : j ≤ n) {d : ℚ} (hd : d ≤ ∑ e ∈ Finset.Icc (j + 1) n, (h e + ε)) :
    d + (h (i + 1) + ε) ≤ ∑ e ∈ Finset.Icc (i + 1) n, (h e + ε) := by
  rw [Finset.Icc_eq_cons_Ioc (by omega : i + 1 ≤ n), Finset.sum_cons]
  have : ∑ e ∈ Finset.Icc (j + 1) n, (h e + ε) ≤ ∑ e ∈ Finset.Ioc (i + 1) n, (h e + ε) :=
    Finset.sum_le_sum_of_subset_of_nonneg
      (fun e he => by simp only [Finset.mem_Icc, Finset.mem_Ioc] at he ⊢; omega)
      fun e _ _ => (hpos e).le
  linarith

theorem sum_Icc_le_sum_Icc_one (h : ℕ → ℚ) (ε : ℚ) (hpos : ∀ e, 0 < h e + ε) (n j : ℕ) :
    ∑ e ∈ Finset.Icc (j + 1) n, (h e + ε) ≤ ∑ e ∈ Finset.Icc 1 n, (h e + ε) :=
  Finset.sum_le_sum_of_subset_of_nonneg (Finset.Icc_subset_Icc (by omega) le_rfl)
    fun e _ _ => (hpos e).le

end GlobalTheory.PairStep

namespace GlobalTheory.PairStep

theorem two_point_induction : GlobalTheory.Published.Principalisation → GlobalTheory.Published.NadelVanishingPair →
    GlobalTheory.Published.NefNumerics → ∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X]
    [GlobalTheory.IsNormalScheme X] (p : X ⟶ Sp ℂ) (n : ℕ), IsProjOver p → topologicalKrullDim X = n →
    letI := algebraΓOfHom p; ∀ (Δ : X → ℚ) (m : ℕ) (G : CartierDiv X) (N : LB X) (ε : ℚ)
    (h : ℕ → ℚ) (x₁ x₂ : X), IsEffQDiv Δ → (∀ y, KltAt p n Δ y) → 0 < m →
    IsLogCanonicalMultiple p n Δ m G → IsAmpleLB N → IsClosed ({x₁} : Set X) →
    IsClosed ({x₂} : Set X) → x₁ ≠ x₂ → (∀ e, 0 < h e) →
    (∀ (z : X) (e : ℕ), z ⤳ x₁ ∨ z ⤳ x₂ → 1 ≤ e →
      topologicalKrullDim (closure ({z} : Set X)) = e →
      2 * (e : ℚ) ^ e < h e ^ e * (interNumRed ℂ (Closeds.closure ({z} : Set X))
        fun _ : Fin e => N : ℤ)) → 0 < ε →
    ∃ (D : X → ℚ) (d : ℚ), d ≤ ∑ e ∈ Finset.Icc 1 n, (h e + ε) ∧ QNum p N d D ∧
      ((LcCut p n (Δ + D) x₁ 0 ∧ ¬ KltAt p n (Δ + D) x₂) ∨
        (LcCut p n (Δ + D) x₂ 0 ∧ ¬ KltAt p n (Δ + D) x₁)) := by
  intro hP hNV hNef X _ _ _ p n hproj hdim
  letI := algebraΓOfHom p
  intro Δ m G N ε h x₁ x₂ hΔ hklt hm hG hNa hc₁ hc₂ hne hh hint hε
  have hpos : ∀ e, 0 < h e + ε := fun e => add_pos (hh e) hε

  have hξ : ∀ x : X, genericPoint X ⤳ x := fun x => (genericPoint_spec X).specializes trivial
  have hdimξ : topologicalKrullDim (closure ({genericPoint X} : Set X)) = n := by
    rw [genericPoint_closure,
      IsHomeomorph.topologicalKrullDim_eq _ (Homeomorph.Set.univ X).isHomeomorph, hdim]

  have hn : 1 ≤ n := by
    obtain ⟨e, -, he, he1⟩ := GlobalTheory.T.exists_topologicalKrullDim_closure_point_le X n (genericPoint X) hdim
    have hen : e = n := by
      rw [hdimξ] at he; exact_mod_cast he.symm
    subst hen
    by_cases h₁ : x₁ = genericPoint X
    · exact he1 x₂ (hξ x₂) fun h₂ => hne (h₁.trans h₂.symm)
    · exact he1 x₁ (hξ x₁) h₁
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩

  have key : ∀ j, j ≤ k → ∀ (D : X → ℚ) (d : ℚ), 0 ≤ d →
      d ≤ ∑ e ∈ Finset.Icc (j + 1) (k + 1), (h e + ε) → QNum p N d D →
      ((LcCut p (k + 1) (Δ + D) x₁ j ∧ ¬ KltAt p (k + 1) (Δ + D) x₂) ∨
        (LcCut p (k + 1) (Δ + D) x₂ j ∧ ¬ KltAt p (k + 1) (Δ + D) x₁)) →
      ∃ (D : X → ℚ) (d : ℚ), d ≤ ∑ e ∈ Finset.Icc 1 (k + 1), (h e + ε) ∧ QNum p N d D ∧
        ((LcCut p (k + 1) (Δ + D) x₁ 0 ∧ ¬ KltAt p (k + 1) (Δ + D) x₂) ∨
          (LcCut p (k + 1) (Δ + D) x₂ 0 ∧ ¬ KltAt p (k + 1) (Δ + D) x₁)) := by
    intro j
    induction j using Nat.strong_induction_on with
    | _ j ih =>
    intro hjk D d hd0 hd hQ hcut
    have hd1 := hd.trans (sum_Icc_le_sum_Icc_one h ε hpos (k + 1) j)
    rcases hcut with ⟨hc, hnk⟩ | ⟨hc, hnk⟩
    · rcases GlobalTheory.T.twoPoint_induction_step_logCanonical hP hNV hNef X p (k + 1) hproj hdim Δ m G N D d ε h x₁ x₂ j hΔ hklt hm
          hG hNa hc₁ hc₂ hne hh hint hε hQ hd0 hc hnk with h0 | ⟨i, D', d', hij, hd'0, hd', hQ', hc'⟩
      · exact ⟨D, d, hd1, hQ, Or.inl ⟨h0, hnk⟩⟩
      · exact ih i hij (by omega) D' d' hd'0
          (hd'.trans (add_le_sum_Icc_of_lt h ε hpos hij (by omega) hd)) hQ' hc'
    · rcases GlobalTheory.T.twoPoint_induction_step_logCanonical hP hNV hNef X p (k + 1) hproj hdim Δ m G N D d ε h x₂ x₁ j hΔ hklt hm
          hG hNa hc₂ hc₁ hne.symm hh (fun z e hz => hint z e hz.symm) hε hQ hd0 hc hnk with
        h0 | ⟨i, D', d', hij, hd'0, hd', hQ', hc'⟩
      · exact ⟨D, d, hd1, hQ, Or.inr ⟨h0, hnk⟩⟩
      · exact ih i hij (by omega) D' d' hd'0
          (hd'.trans (add_le_sum_Icc_of_lt h ε hpos hij (by omega) hd)) hQ' hc'.symm

  have hlc : ∀ x, LcAt p (k + 1) (Δ + 0) x := fun x => by rw [add_zero]; exact (hklt x).lcAt
  have hdimξ' : topologicalKrullDim (closure ({genericPoint X} : Set X)) = ((k + 1 : ℕ) : WithBot ℕ∞) :=
    hdimξ
  obtain ⟨D', d', hd'0, hd', hQ', hc'⟩ := GlobalTheory.T.lc_cut_two_closed_points_one_centre hP hNV hNef X p (k + 1) hproj hdim Δ m G N 0
    0 (h (k + 1)) x₁ x₂ (genericPoint X) k hΔ hklt hm hG hNa (qNum_zero_zero X p hproj N) le_rfl
    hc₁ hc₂ (hlc x₁) (hlc x₂) (hξ x₁) (hξ x₂) (Or.inl rfl) hdimξ' (hh _)
    (hint (genericPoint X) (k + 1) (Or.inl (hξ x₁)) (by omega) hdimξ')
  refine key k le_rfl D' d' hd'0 ?_ hQ' hc'
  rw [Finset.Icc_self, Finset.sum_singleton]
  linarith [hε]

end GlobalTheory.PairStep
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisationLineBundleDescendsGalois
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
open TopologicalSpace

namespace GlobalTheory.Mum.LBGal
open GlobalTheory.Mum.LBDesc

theorem lemD : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (R' : Type) [CommRing R'] [IsDomain R'] [IsLocalRing R'] (ρ : R →+* R'), FinExt ρ → IsGal ρ → ∀ (G' : Over (Sp R')) [GrpObj G'] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (β : G'.left ⟶ G.left) (act : Gal ρ → (G'.left ⟶ G'.left)), IsSemiAbelian G → IsGrpPullback G' G (spMap ρ) β → (∀ σ, IsGrpPullback G' G' (spMap (Gal.hom σ)) (act σ)) → (∀ σ, act σ ≫ β = β) → ∀ O : G.left.Opens, Function.Injective (β.app O).hom ∧ ∀ u : Γ(G'.left, β ⁻¹ᵁ O)ˣ, (∀ σ (h : β ⁻¹ᵁ O ≤ act σ ⁻¹ᵁ (β ⁻¹ᵁ O)), ((act σ).appLE _ _ h).hom u.val = u.val) → ∃ g : Γ(G.left, O)ˣ, pullU β O g = u := GlobalTheory.T.galoisBaseChange_semiAbelian_invariant_units_descend

theorem lemF : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (R' : Type) [CommRing R'] [IsDomain R'] [IsLocalRing R'] (ρ : R →+* R'), FinExt ρ → IsGal ρ → ∀ (D : DegData R (maximalIdeal R)) (D' : DegData R' (maximalIdeal R')) (hD : IsPullDeg ρ D.toPre D'.toPre) (A' : PolAV (Sp (FractionRing R'))) (G' : Over (Sp R')) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ∀ (U' : Unif (maximalIdeal R') D' A' G'), ∀ (a : GalAct ρ hD U') (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (β : G'.left ⟶ G.left), IsSemiAbelian G → IsGrpPullback G' G (spMap ρ) β → (∀ σ, a.act σ ≫ β = β) → ∃ (V : G.left → G.left.Opens) (T : ∀ (y : G.left) (k : U'.LG.L.ι), Γ(G'.left, β ⁻¹ᵁ V y ⊓ U'.LG.L.U k)ˣ), (∀ y, y ∈ V y) ∧ (∀ y k k', res (inf_le_left : β ⁻¹ᵁ V y ⊓ U'.LG.L.U k ⊓ (β ⁻¹ᵁ V y ⊓ U'.LG.L.U k') ≤ β ⁻¹ᵁ V y ⊓ U'.LG.L.U k) (T y k) = res (le_inf (inf_le_left.trans inf_le_right) (inf_le_right.trans inf_le_right) : β ⁻¹ᵁ V y ⊓ U'.LG.L.U k ⊓ (β ⁻¹ᵁ V y ⊓ U'.LG.L.U k') ≤ U'.LG.L.U k ⊓ U'.LG.L.U k') (U'.LG.L.g k k') * res (inf_le_right : β ⁻¹ᵁ V y ⊓ U'.LG.L.U k ⊓ (β ⁻¹ᵁ V y ⊓ U'.LG.L.U k') ≤ β ⁻¹ᵁ V y ⊓ U'.LG.L.U k') (T y k')) ∧ ∀ (y y' : G.left) (r : Γ(G'.left, β ⁻¹ᵁ (V y ⊓ V y'))ˣ), (∀ (z : G'.left) (k : U'.LG.L.ι), z ∈ β ⁻¹ᵁ (V y ⊓ V y') → z ∈ U'.LG.L.U k → gm (𝟙 G'.left) z _ r = gm (𝟙 G'.left) z _ (T y' k) * (gm (𝟙 G'.left) z _ (T y k))⁻¹) → ∀ σ (h : β ⁻¹ᵁ (V y ⊓ V y') ≤ a.act σ ⁻¹ᵁ (β ⁻¹ᵁ (V y ⊓ V y'))), ((a.act σ).appLE _ _ h).hom r.val = r.val := GlobalTheory.T.exists_galoisInvariant_local_frames_uniformisation

theorem eq_of_gm_inj {Z Y : Scheme.{0}} (p : Z ⟶ Y) (hp : ∀ V : Y.Opens, Function.Injective (p.app V).hom) {O : Y.Opens}
    {a b : Γ(Y, O)ˣ} (h : ∀ z : Z, p z ∈ O → gm (𝟙 Z ≫ p) z O a = gm (𝟙 Z ≫ p) z O b) : a = b := by
  have e : pullU p O a = pullU p O b := unit_ext fun z hz => by
    rw [gm_pull (𝟙 Z) p z O hz a, gm_pull (𝟙 Z) p z O hz b]
    exact h z hz
  exact Units.ext ((hp O) (congrArg Units.val e))

theorem isLB_descLB_inj {Z Y : Scheme.{0}} (p : Z ⟶ Y) (hp : ∀ V : Y.Opens, Function.Injective (p.app V).hom)
    (L' : LB Z) (hL' : L'.IsLB)
    (V : Y → Y.Opens) (hyV : ∀ y, y ∈ V y) (T : ∀ (y : Y) (k : L'.ι), Γ(Z, p ⁻¹ᵁ V y ⊓ L'.U k)ˣ)
    (g : ∀ y y', Γ(Y, V y ⊓ V y')ˣ)
    (key : ∀ {W : Scheme.{0}} (f : W ⟶ Z) (w : W) (y y' : Y) (k : L'.ι), p (f w) ∈ V y → p (f w) ∈ V y' →
      f w ∈ L'.U k → gm (f ≫ p) w ((descLB V g).U y ⊓ (descLB V g).U y') ((descLB V g).g y y') =
        gm f w _ (T y' k) * (gm f w _ (T y k))⁻¹) :
    (descLB V g).IsLB where
  cover := eq_top_iff.2 fun y _ => Opens.mem_iSup.2 ⟨y, hyV y⟩
  g_self := fun y => eq_of_gm_inj p hp fun z hz => by
    obtain ⟨k, hk⟩ := exists_chart hL' z
    rw [gm_res (𝟙 Z ≫ p) z _ hz, map_one]
    exact (key (𝟙 Z) z y y k hz hz hk).trans (mul_inv_cancel _)
  cocycle := fun a b c => eq_of_gm_inj p hp fun z hz => by
    obtain ⟨k, hk⟩ := exists_chart hL' z
    rw [map_mul, gm_res (𝟙 Z ≫ p) z _ hz, gm_res (𝟙 Z ≫ p) z _ hz, gm_res (𝟙 Z ≫ p) z _ hz,
      key (𝟙 Z) z a b k hz.1.1 hz.1.2 hk, key (𝟙 Z) z b c k hz.1.2 hz.2 hk,
      key (𝟙 Z) z a c k hz.1.1 hz.2 hk]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv]
    abel

end GlobalTheory.Mum.LBGal

namespace GlobalTheory.Mum
open GlobalTheory.Mum.LBDesc GlobalTheory.Mum.LBGal

theorem unif_lb_descend_gal : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (R' : Type) [CommRing R'] [IsDomain R'] [IsLocalRing R'] (ρ : R →+* R'), FinExt ρ → IsGal ρ → ∀ (D : DegData R (maximalIdeal R)) (D' : DegData R' (maximalIdeal R')) (hD : IsPullDeg ρ D.toPre D'.toPre) (A' : PolAV (Sp (FractionRing R'))) (G' : Over (Sp R')) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ∀ (U' : Unif (maximalIdeal R') D' A' G'), ∀ (a : GalAct ρ hD U') (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (β : G'.left ⟶ G.left), IsSemiAbelian G → IsGrpPullback G' G (spMap ρ) β → (∀ σ, a.act σ ≫ β = β) → ∃ L : LB G.left, L.IsLB ∧ LBIso U'.LG.L (L.pull β) := by
  intro R _ _ _ hR R' _ _ _ ρ hρ hG D D' hD A' G' _ _ hG' U' a G _ _ β hGs hβ hact
  have hDl := lemD R hR R' ρ hρ hG G' G β a.act hGs hβ a.cart hact
  obtain ⟨V, T, hyV, hT, hinv⟩ := lemF R hR R' ρ hρ hG D D' hD A' G' hG' U' a G β hGs hβ hact
  have hL' : U'.LG.L.IsLB := U'.LG.isLB
  have hc : ∀ (y : G.left) {W : Scheme.{0}} (f : W ⟶ G'.left) (w : W) (k k' : U'.LG.L.ι), f w ∈ β ⁻¹ᵁ V y →
      f w ∈ U'.LG.L.U k → f w ∈ U'.LG.L.U k' →
      gm f w _ (T y k) = gm f w (U'.LG.L.U k ⊓ U'.LG.L.U k') (U'.LG.L.g k k') * gm f w _ (T y k') :=
    fun y _ f w k k' h hk hk' => gm_compat U'.LG.L _ (T y) (hT y) f w k k' h hk hk'
  choose r hr using fun y y' => ratio β U'.LG.L hL' (T y) (T y') (hc y) (hc y')
  have hri : ∀ y y' σ (h : β ⁻¹ᵁ (V y ⊓ V y') ≤ a.act σ ⁻¹ᵁ (β ⁻¹ᵁ (V y ⊓ V y'))),
      ((a.act σ).appLE _ _ h).hom (r y y').val = (r y y').val :=
    fun y y' => hinv y y' (r y y') (fun z k hz hk => hr y y' (𝟙 _) z k hz hk)
  choose g hg using fun y y' => (hDl (V y ⊓ V y')).2 (r y y') (hri y y')
  have key : ∀ {W : Scheme.{0}} (f : W ⟶ G'.left) (w : W) (y y' : G.left) (k : U'.LG.L.ι), β (f w) ∈ V y →
      β (f w) ∈ V y' → f w ∈ U'.LG.L.U k →
      gm (f ≫ β) w ((descLB V g).U y ⊓ (descLB V g).U y') ((descLB V g).g y y') =
        gm f w _ (T y' k) * (gm f w _ (T y k))⁻¹ := by
    intro W f w y y' k h1 h2 hk
    exact (gm_pull f β w (V y ⊓ V y') ⟨h1, h2⟩ (g y y')).symm.trans
      ((congrArg _ (hg y y')).trans (hr y y' f w k ⟨h1, h2⟩ hk))
  exact ⟨descLB V g, isLB_descLB_inj β (fun O => (hDl O).1) U'.LG.L hL' V hyV T g key, descIso β U'.LG.L V T g,
    isGen_descIso β U'.LG.L V T g hc key⟩

end GlobalTheory.Mum
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryExistsNormalModelEffCartierAlongTraitsStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc
open GlobalTheory
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitary_exists_normalModel_effCartier_along_traits : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H), 1 ≤ Dw.p + Dw.q → ∀ φ : InvFun (𝓞 E), IsPolFan H.bar (min Dw.p Dw.q) φ → ∀ (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (C : UCompact Xo c) (X₁ : USetup C), IsProjOver X₁.M.s → ∃ (ι : ℕ) (Y : RatModel X₁.o₁ X₁.Ω₁) (πY : Y.Z ⟶ X₁.M.Z) (D : GlobalTheory.EffCartierData Y.Z), 1 ≤ ι ∧ X₁.M.IsHom Y (AlgHom.id X₁.o₁ X₁.Ω₁) πY ∧ IsProper πY ∧ ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme Y.Z ∧ (∀ y ∈ D.idealSheaf.support, X₁.π (πY y) ∉ Set.range C.i) ∧ UValThru Xo c C.i (πY ≫ X₁.π) Set.univ φ D.idealSheaf ι := by
  first | exact @GlobalTheory.UPoinc.exists_zhModel_effCartier_orders | exact GlobalTheory.UPoinc.exists_zhModel_effCartier_orders | (intros; apply GlobalTheory.UPoinc.exists_zhModel_effCartier_orders <;> assumption)
end

