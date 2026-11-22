import Mathlib
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0033
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.UnivFrame
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.NormConst
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0011
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0008
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0010
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0003
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Development.AbelianVarietyTheory.PublishedTheorems.Landherr₂.Bundle0001
import Development.AbelianVarietyTheory.Statements.HyperbolicHypotheses.HypothesesInhabitedHyperbolic
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0002
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0034
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0028
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0023
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.IsLocalizedModuleResBasicOpenOfQcqs
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FiniteOfIsClosedTorusExtensionOfPowEqOne
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0035
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0036
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.FlagBasis
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0006
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.Biextensions.CubicalExtendsSt

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.CmTypeLetterFrameColumnDictionaryStatement
section
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Frames GlobalTheory.FrameUnif
open scoped Matrix nonZeroDivisors
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cmType_letter_frame_column_dictionary : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (g : ℕ) (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ)) (F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (fun j => relab c σ (e j).1)) (r : ℕ) (M : ModelsOf F r), GoodEmb c σ → ModelBase M → NegXi M → ∀ k, (∃ idx : Fin g ≃ (M.X k).Ψ × Fin r, (∀ j, relab c σ (e j).1 = if ((idx j).2 : ℕ) < (F.Di k).q then ComplexEmbedding.conjugate (idx j).1.1 else (idx j).1.1) ∧ (∀ j, ((idx j).2 : ℕ) = if ((idx j).2 : ℕ) < (F.Di k).q then (F.Di k).q - 1 - (e j).2 else (F.Di k).q + (e j).2) ∧ ∀ (x : Frame (M.X k).Ψ r) (v : Fin r → E) j, perFr (M.X k) x v (relab c σ (e j).1) (e j).2 = if ((idx j).2 : ℕ) < (F.Di k).q then hermC (idx j).1.1 (M.X k).Gm (col (mat x (idx j).1) (idx j).2) (Data.emb (idx j).1.1 v) else ((mat x (idx j).1)⁻¹ *ᵥ Data.emb (idx j).1.1 v) (idx j).2) ∧ (M.X k).p0 = (F.Di k).q ∧ r = (F.Di k).p + (F.Di k).q ∧ cc (-(M.X k).ξ0) = -(-(M.X k).ξ0) ∧ (∀ τ ∈ (M.X k).Ψ, 0 < (τ (-(M.X k).ξ0)).im) ∧ ∀ φ : (F.Di k).La →ₗ[𝓞 E] (Fin r → E), (∀ a, φ a = (M.φ k a : Fin r → E)) → LinearMap.range φ = (M.X k).Λ ∧ (Function.Injective φ ∧ Submodule.span E (Set.range φ) = ⊤ ∧ (∀ a b, cc ((M.X k).Gm a b) = (M.X k).Gm b a) ∧ (M.X k).Gm.det ≠ 0 ∧ ∀ x y, (((F.Di k).EF x y : ℤ) : ℚ) = Algebra.trace ℚ E (-(M.X k).ξ0 * herm (M.X k).Gm (φ x) (φ y))) := by
  first | exact @GlobalTheory.FrameUnif.letter_column_dictionary | exact GlobalTheory.FrameUnif.letter_column_dictionary | (intros; apply GlobalTheory.FrameUnif.letter_column_dictionary <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.CuspPairingIntIffHermitianExponentIntegralStatement
section
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Frames GlobalTheory.FrameUnif
open scoped Matrix nonZeroDivisors
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cuspPairing_int_iff_hermitianExponent_integral : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (r ρ : ℕ) (X : Data E r) (N : ℕ) (cc' : Fin ρ → FractionalIdeal (𝓞 E)⁰ E) (χ : Matrix (Fin ρ) (Fin ρ) E), 0 < N → (∀ b, cc' b ≠ 0) → FJ.IsHermE χ → ((∀ β, FJ.IsSkew β → (∀ a b (y : E), (∀ a' ∈ cc' b, ∃ n : ℤ, Algebra.trace ℚ E (y * cc a') = n) → ∃ z ∈ cc' a, β a b / X.ξ0 * y = (N : E) * z) → ∃ n : ℤ, FJ.prE X χ β = n) ↔ ∀ u m : Fin ρ → E, (∀ a (y : E), (∀ a' ∈ cc' a, ∃ n : ℤ, Algebra.trace ℚ E (y * a') = n) → u a * y ∈ Set.range (algebraMap (𝓞 E) E)) → (∀ a (y : E), (∀ a' ∈ cc' a, ∃ n : ℤ, Algebra.trace ℚ E (y * a') = n) → m a * y ∈ Set.range (algebraMap (𝓞 E) E)) → (N : E) * ∑ i, ∑ k, u i * χ i k * cc (m k) ∈ Set.range (algebraMap (𝓞 E) E)) := by
  first | exact @GlobalTheory.ExponentTrace.prE_int_iff_values_integral | exact GlobalTheory.ExponentTrace.prE_int_iff_values_integral | (intros; apply GlobalTheory.ExponentTrace.prE_int_iff_values_integral <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.EigenBasisIffTangentBasis
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Frames

namespace GlobalTheory.Frames

theorem basis_iff_of_split {S N J : Type} [CommRing S] [AddCommGroup N] [Module S N] [Fintype J]
    (m : J → ℕ) (M : J → Submodule S N)
    (hs : ∀ n : N, ∃! f : J → N, (∀ τ, f τ ∈ M τ) ∧ ∑ τ, f τ = n)
    (b : ∀ τ, Fin (m τ) → N) (hb : ∀ τ i, b τ i ∈ M τ) (g : ℕ) (e : Fin g ≃ Σ τ : J, Fin (m τ)) :
    (∀ τ n, n ∈ M τ → ∃! a : Fin (m τ) → S, n = ∑ i, a i • b τ i) ↔
      ∀ n : N, ∃! a : Fin g → S, n = ∑ j, a j • b (e j).1 (e j).2 := by
  classical
  have key : ∀ a : ∀ τ, Fin (m τ) → S,
      ∑ j, a (e j).1 (e j).2 • b (e j).1 (e j).2 = ∑ τ, ∑ i, a τ i • b τ i := by
    intro a
    rw [e.sum_comp (fun p : Σ τ : J, Fin (m τ) => a p.1 p.2 • b p.1 p.2), Fintype.sum_sigma]
  have key' : ∀ a : Fin g → S,
      ∑ j, a j • b (e j).1 (e j).2 = ∑ τ, ∑ i, a (e.symm ⟨τ, i⟩) • b τ i := by
    intro a
    rw [← key (fun τ i => a (e.symm ⟨τ, i⟩))]
    simp
  have hmem : ∀ τ (a : Fin (m τ) → S), ∑ i, a i • b τ i ∈ M τ := fun τ a =>
    Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (hb τ i)
  constructor
  · intro h n
    obtain ⟨f, ⟨hf, hfn⟩, hu⟩ := hs n
    choose a ha hau using fun τ => h τ (f τ) (hf τ)
    refine ⟨fun j => a (e j).1 (e j).2, ?_, ?_⟩
    · change n = ∑ j, a (e j).1 (e j).2 • b (e j).1 (e j).2
      rw [key, ← hfn]
      exact Finset.sum_congr rfl fun τ _ => ha τ
    · intro a' ha'
      rw [key'] at ha'
      have h1 := hu (fun τ => ∑ i, a' (e.symm ⟨τ, i⟩) • b τ i) ⟨fun τ => hmem τ _, ha'.symm⟩
      funext j
      have h2 := hau (e j).1 (fun i => a' (e.symm ⟨(e j).1, i⟩)) (congrFun h1 (e j).1).symm
      have h3 := congrFun h2 (e j).2
      simpa using h3
  · intro h τ n hn
    obtain ⟨a', ha', hu'⟩ := h n
    have hA : ∀ a : Fin (m τ) → S, n = ∑ i, a i • b τ i →
        (fun j => (Pi.single τ a : ∀ σ, Fin (m σ) → S) (e j).1 (e j).2) = a' := by
      intro a ha
      apply hu'
      change n = ∑ j, (Pi.single τ a : ∀ σ, Fin (m σ) → S) (e j).1 (e j).2 • b (e j).1 (e j).2
      rw [key, Finset.sum_eq_single τ]
      · simpa using ha
      · intro σ _ hσ
        simp [Pi.single_eq_of_ne hσ]
      · simp
    refine ⟨fun i => a' (e.symm ⟨τ, i⟩), ?_, ?_⟩
    · have ha2 : n = ∑ j, a' j • b (e j).1 (e j).2 := ha'
      rw [key'] at ha2
      have h1 := (hs n).unique (y₁ := fun τ => ∑ i, a' (e.symm ⟨τ, i⟩) • b τ i)
        (y₂ := Pi.single τ n) ⟨fun τ => hmem τ _, ha2.symm⟩ ⟨fun σ => by
          by_cases hσ : σ = τ
          · subst hσ; simpa using hn
          · simp [Pi.single_eq_of_ne hσ], by simp⟩
      have h2 := congrFun h1 τ
      simpa using h2.symm
    · intro a ha
      funext i
      have h1 := congrFun (hA a ha) (e.symm ⟨τ, i⟩)
      rw [← h1, Equiv.apply_symm_apply]
      simp

theorem eigBasis_iff_tanBasis : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (S : Type) [CommRing S] [Algebra c.F S] (x : Sp S ⟶ Xo.X) (u : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → (Sp (DualNumber S) ⟶ Xo.univ.t.G.left)) (g : ℕ) (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ)), (∀ τ i, IsTanAt x (u τ i)) → (∀ τ i, IsEigAt c τ (u τ i)) → ((∀ τ w, IsTanAt x w → IsEigAt c τ w → ∃! a : Fin (Dw.mult τ) → S, IsCombAt x (u τ) a w) ↔ TanBasis x (fun j => u (e j).1 (e j).2)) := by
  intro E _ _ _ H Dw l Xo c S _ _ x u g e ht he
  obtain ⟨N, _, _, v, ρ, hinj, htan, hcomb, hρ, hsm⟩ := GlobalTheory.T.exists_tangent_module_universal_group E H Dw l Xo S x
  choose b hb using fun τ i => (htan (u τ i)).1 (ht τ i)
  obtain rfl : u = fun τ i => v (b τ i) := by funext τ i; exact (hb τ i).symm
  let M : (E →+* ℂ) → Submodule S N := fun τ =>
    ⨅ a : 𝓞 E, Module.End.eigenspace (ρ a) (algebraMap c.F S (embK c τ a))
  have hM : ∀ τ n, n ∈ M τ ↔ ∀ a, ρ a n = algebraMap c.F S (embK c τ a) • n := by
    intro τ n
    simp only [M, Submodule.mem_iInf, Module.End.mem_eigenspace_iff]
  have hE : ∀ τ n, IsEigAt c τ (v n) ↔ n ∈ M τ := by
    intro τ n
    rw [hM]
    refine forall_congr' fun a => ?_
    rw [← hρ, ← hsm, hinj.eq_iff]
  have hs : ∀ n : N, ∃! f : (E →+* ℂ) → N, (∀ τ, f τ ∈ M τ) ∧ ∑ τ, f τ = n := by
    intro n
    simp only [hM]
    exact GlobalTheory.T.existsUnique_cmEmbedding_eigenvector_sum E H l c S N ρ n
  have hmain := basis_iff_of_split (fun τ => Dw.mult τ) M hs b (fun τ i => (hE τ _).1 (he τ i)) g e
  have hT : ∀ n, IsTanAt x (v n) := fun n => (htan _).2 ⟨n, rfl⟩
  have hC : ∀ (k : ℕ) (b : Fin k → N) (a : Fin k → S) (n : N),
      IsCombAt x (fun i => v (b i)) a (v n) ↔ n = ∑ i, a i • b i := by
    intro k b a n
    rw [hcomb, hinj.eq_iff]
  constructor
  · intro h
    refine ⟨fun j => hT _, fun w hw => ?_⟩
    obtain ⟨n, rfl⟩ := (htan w).1 hw
    have h1 := hmain.1 (fun τ n hn => by
      have h2 := h τ (v n) (hT n) ((hE τ n).2 hn)
      simpa only [hC] using h2) n
    simpa only [hC] using h1
  · rintro ⟨-, h⟩ τ w hw hew
    obtain ⟨n, rfl⟩ := (htan w).1 hw
    have h1 := hmain.2 (fun n => by
      have h2 := h (v n) (hT n)
      simpa only [hC] using h2) τ n ((hE τ n).1 hew)
    simpa only [hC] using h1

end GlobalTheory.Frames
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsFibreSectionPowMulBaseChangeAway
section
noncomputable section

namespace GlobalTheory.Frames.SecLoc

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Frames

theorem appLE_bijective {Y Z : Scheme.{0}} (π : Z ⟶ Y) [IsOpenImmersion π] {V : Y.Opens} (hV : V ≤ π.opensRange)
    {V' : Z.Opens} (h : V' ≤ π ⁻¹ᵁ V) (h' : π ⁻¹ᵁ V ≤ V') : Function.Bijective (π.appLE V V' h).hom := by
  obtain rfl : V' = π ⁻¹ᵁ V := le_antisymm h h'
  rw [← Scheme.Hom.app_eq_appLE]
  haveI := π.isIso_app V hV
  exact ConcreteCategory.bijective_of_isIso (π.app V)

theorem exists_pow_mul_eq {Y Z : Scheme.{0}} [CompactSpace Y] [QuasiSeparatedSpace Y] (π : Z ⟶ Y)
    [IsOpenImmersion π] (a : Γ(Y, ⊤)) (ha : π.opensRange = Y.basicOpen a) {M : LB Y} (hM : M.IsLB)
    (U' : M.ι → Z.Opens) (h : ∀ i, U' i ≤ π ⁻¹ᵁ M.U i) (h' : ∀ i, π ⁻¹ᵁ M.U i ≤ U' i) (f : ∀ i, Γ(Z, U' i))
    (hf : ∀ i j, resG Z (inf_le_left : U' i ⊓ U' j ≤ U' i) (f i) =
      (π.appLE (M.U i ⊓ M.U j) (U' i ⊓ U' j) (inf_le_inf (h i) (h j))).hom (M.g i j).val *
        resG Z (inf_le_right : U' i ⊓ U' j ≤ U' j) (f j)) :
    ∃ (N : ℕ) (s : LB.Sec M), ∀ i, (π.appLE _ _ (h i)).hom (s.f i) =
      (π.appLE ⊤ (U' i) le_top).hom a ^ N * f i := by
  have k : ∀ i, U' i ≤ π ⁻¹ᵁ (π.opensRange ⊓ M.U i) := fun i z hz => ⟨⟨z, rfl⟩, h i hz⟩
  have hb : ∀ i, Function.Bijective (π.appLE _ _ (k i)).hom := fun i =>
    appLE_bijective π inf_le_left (k i) (fun z hz => h' i hz.2)
  choose t ht using fun i => (hb i).2 (f i)
  have hmem : t ∈ secOn M π.opensRange := fun i j => by
    have k₂ : U' i ⊓ U' j ≤ π ⁻¹ᵁ (π.opensRange ⊓ M.U i ⊓ M.U j) := fun z hz => ⟨k i hz.1, h j hz.2⟩
    apply (appLE_bijective π (inf_le_left.trans inf_le_left) k₂
      (fun z hz => ⟨h' i hz.1.2, h' j hz.2⟩)).1
    rw [map_mul, GlobalTheory.LB.appLE_resG, GlobalTheory.LB.appLE_resG, GlobalTheory.LB.appLE_resG]
    have := hf i j
    rw [← ht i, ← ht j, GlobalTheory.LB.resG_appLE, GlobalTheory.LB.resG_appLE] at this
    exact this
  obtain ⟨N, u, hu⟩ := AbLaw.SecOn.exists_pow_smul_eq_restrict hM (V := ⊤) isCompact_univ isQuasiSeparated_univ a
    le_top ha (GlobalTheory.LB.mkSec t hmem)
  refine ⟨N, AbLaw.SecOn.topEquiv M u, fun i => ?_⟩
  have e : resG Y inf_le_left (resG Y le_top a ^ N) * t i =
      resG Y (inf_le_inf_right _ le_top) (GlobalTheory.LB.coord u i) := congrArg (fun w => GlobalTheory.LB.coord w i) hu
  have e₂ := congrArg (π.appLE _ _ (k i)).hom e
  rw [map_mul, ht, map_pow, map_pow, GlobalTheory.LB.resG_resG, GlobalTheory.LB.appLE_resG, GlobalTheory.LB.appLE_resG] at e₂
  exact (GlobalTheory.LB.appLE_resG _ _ _ _).trans e₂.symm

theorem exists_pow_mul_eq_linComb {X Y Z : Scheme.{0}} [CompactSpace Y] [QuasiSeparatedSpace Y] (π : Z ⟶ Y)
    [IsOpenImmersion π] (a : Γ(Y, ⊤)) (ha : π.opensRange = Y.basicOpen a) {L : LB X} (hL : L.IsLB)
    {K : Type} [Fintype K] (φ : K → (Y ⟶ X)) (φ' : K → (Z ⟶ X)) (ε : K → ℤ) (e : (fun k => π ≫ φ k) = φ')
    (s' : LB.Sec (LB.LinComb L φ' ε)) :
    ∃ (N : ℕ) (s : LB.Sec (LB.LinComb L φ ε)), ∀ (j : K → L.ι)
      (hle : (LB.LinComb L φ' ε).U j ≤ π ⁻¹ᵁ (LB.LinComb L φ ε).U j), (π.appLE _ _ hle).hom (s.f j) =
        (π.appLE ⊤ _ le_top).hom a ^ N * s'.f j := by
  subst e
  obtain ⟨N, s, hs⟩ := exists_pow_mul_eq π a ha (LB.isLB_linComb hL φ ε)
    (LB.LinComb L (fun k => π ≫ φ k) ε).U
    (fun _ _ hy => Set.mem_iInter.2 fun k => Set.mem_iInter.1 hy k)
    (fun _ _ hy => Set.mem_iInter.2 fun k => Set.mem_iInter.1 hy k) s'.f (fun i j => by
      refine (s'.compat i j).trans (congrArg (· * _) ?_)
      exact congrArg Units.val (DVR.linComb_g_comp φ ε π i j))
  exact ⟨N, s, fun j _ => hs j⟩

theorem opensRange_of_isPullback {S : Type} [CommRing S] (g : S) {Y Z : Scheme.{0}} {π : Z ⟶ Y} {p : Y ⟶ Sp S}
    {p' : Z ⟶ Sp (Localization.Away g)} (h : IsPullback π p' p (spMap (algebraMap S (Localization.Away g))))
    [IsOpenImmersion π] : π.opensRange = Y.basicOpen (p.appTop.hom (toΓ S g)) := by
  have e : Y.basicOpen (p.appTop.hom (toΓ S g)) = p ⁻¹ᵁ PrimeSpectrum.basicOpen g :=
    (Scheme.preimage_basicOpen_top p _).symm.trans (congrArg (p ⁻¹ᵁ ·) (basicOpen_eq_of_affine (R := .of S) g))
  rw [e]
  ext y
  have r : Set.range (spMap (algebraMap S (Localization.Away g))) = (PrimeSpectrum.basicOpen g).1 :=
    PrimeSpectrum.localization_away_comap_range (Localization.Away g) g
  have r' := Scheme.Pullback.range_fst p (spMap (algebraMap S (Localization.Away g)))
  rw [r] at r'
  constructor
  · rintro ⟨z, rfl⟩
    have : π z ∈ Set.range (pullback.fst p (spMap (algebraMap S (Localization.Away g)))) :=
      ⟨h.isoPullback.hom z, by rw [← Scheme.Hom.comp_apply, h.isoPullback_hom_fst]⟩
    rw [r'] at this
    exact this
  · intro hy
    have : y ∈ Set.range (pullback.fst p (spMap (algebraMap S (Localization.Away g)))) := by
      rw [r']; exact hy
    obtain ⟨w, rfl⟩ := this
    exact ⟨h.isoPullback.inv w, by rw [← Scheme.Hom.comp_apply, h.isoPullback_inv_fst]⟩

theorem appLE_const {S T : Type} [CommRing S] [CommRing T] (φ : S →+* T) {Y Z : Scheme.{0}} {π : Z ⟶ Y}
    {p : Y ⟶ Sp S} {p' : Z ⟶ Sp T} (w : π ≫ p = p' ≫ spMap φ) (U : Z.Opens) (a : S) :
    (π.appLE ⊤ U le_top).hom (p.appTop.hom (toΓ S a)) = resG Z le_top (p'.appTop.hom (toΓ T (φ a))) := by
  have e₁ : π.appTop.hom (p.appTop.hom (toΓ S a)) = p'.appTop.hom ((spMap φ).appTop.hom (toΓ S a)) := by
    rw [← CommRingCat.comp_apply, ← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop, ← Scheme.Hom.comp_appTop, w]
  have e₂ : (spMap φ).appTop.hom (toΓ S a) = toΓ T (φ a) :=
    (congrArg (fun f => f.hom a) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom φ))).symm
  rw [← e₂, ← e₁]
  rfl

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l}

theorem isPullback_gx {S : Type} [CommRing S] (x : Sp S ⟶ Xo.X) :
    IsPullback (snd (Over.mk x) Xo.univ.t.G).left (fst (Over.mk x) Xo.univ.t.G).left Xo.univ.t.G.hom x :=
  (IsPullback.of_hasPullback x Xo.univ.t.G.hom).flip

theorem isPullback_gxMap {S T : Type} [CommRing S] [CommRing T] (φ : S →+* T) (x : Sp S ⟶ Xo.X) :
    IsPullback (SecPull.gxMap φ x _ rfl) (fst (Over.mk (spMap φ ≫ x)) Xo.univ.t.G).left
      (fst (Over.mk x) Xo.univ.t.G).left (spMap φ) :=
  IsPullback.of_right (by rw [SecPull.gxMap_snd]; exact isPullback_gx _) (SecPull.gxMap_fst φ x _ rfl)
    (isPullback_gx x)

theorem exists_secBC_pow_mul : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (S : Type) [CommRing S] (x : Sp S ⟶ Xo.X) (g : S) (s' : LB.Sec (PPx (spMap (algebraMap S (Localization.Away g)) ≫ x))), ∃ (N : ℕ) (s : LB.Sec (PPx x)) (s₁ : LB.Sec (PPx (spMap (algebraMap S (Localization.Away g)) ≫ x))), SecBC (algebraMap S (Localization.Away g)) 1 x _ s s₁ ∧ ∀ i, s₁.f i = scal _ ((algebraMap S (Localization.Away g)) g ^ N) i * s'.f i := by
  intro E _ _ _ H Dw l Xo S _ x g s'
  have hP := isPullback_gxMap (algebraMap S (Localization.Away g)) x
  have hpr : IsProper (fst (Over.mk x) Xo.univ.t.G).left :=
    MorphismProperty.of_isPullback (P := @IsProper) (isPullback_gx x) Xo.univ.proper
  have : CompactSpace (Over.mk x).left := inferInstanceAs (CompactSpace (Sp S))
  have : QuasiSeparatedSpace (Over.mk x).left := inferInstanceAs (QuasiSeparatedSpace (Sp S))
  have : CompactSpace (Gx x) :=
    QuasiCompact.compactSpace_of_compactSpace (fst (Over.mk x) Xo.univ.t.G).left
  have : QuasiSeparatedSpace (Gx x) :=
    quasiSeparatedSpace_of_quasiSeparated (fst (Over.mk x) Xo.univ.t.G).left
  have hoi : IsOpenImmersion (spMap (algebraMap S (Localization.Away g))) :=
    IsOpenImmersion.of_isLocalization g
  have : IsOpenImmersion (SecPull.gxMap (algebraMap S (Localization.Away g)) x _ rfl) :=
    MorphismProperty.of_isPullback (P := @IsOpenImmersion) hP.flip hoi
  obtain ⟨N, s, hs⟩ := exists_pow_mul_eq_linComb _ _ (opensRange_of_isPullback g hP) Xo.univ.t.PP.isLB
    (K := Fin 1) (fun _ => (snd (Over.mk x) Xo.univ.t.G).left)
    (fun _ => (snd (Over.mk (spMap (algebraMap S (Localization.Away g)) ≫ x)) Xo.univ.t.G).left) (fun _ => 1)
    (funext fun _ => SecPull.gxMap_snd _ x _ rfl) s'
  refine ⟨N, s, SecPull.scalSec _ (algebraMap S (Localization.Away g) g ^ N) s',
    ⟨_, SecPull.gxMap_snd _ x _ rfl, SecPull.gxMap_fst _ x _ rfl, fun i h => ?_⟩, fun _ => rfl⟩
  have e₁ : scal x 1 i = 1 := by simp only [scal, Out.liftFun, map_one]
  rw [e₁, _root_.one_mul]
  refine (hs i h).trans (congrArg (· * s'.f i) ?_)
  rw [appLE_const _ hP.w]
  simp only [scal, Out.liftFun, map_pow]
  rfl

end GlobalTheory.Frames.SecLoc
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsLiftOfIsReducedOfRangeSubset
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory

theorem exists_lift_of_isReduced_of_range_subset {Y X Z : Scheme.{0}} [IsReduced Y] (i : Z ⟶ X)
    [IsClosedImmersion i] (a : Y ⟶ X) (h : Set.range a ⊆ Set.range i) :
    ∃ b : Y ⟶ Z, b ≫ i = a := by
  haveI : Surjective (pullback.snd i a) := ⟨by
    rw [← Set.range_eq_univ, Scheme.Pullback.range_snd]
    exact Set.eq_univ_of_forall fun y => h ⟨y, rfl⟩⟩
  haveI := isIso_of_isClosedImmersion_of_surjective (pullback.snd i a)
  exact ⟨inv (pullback.snd i a) ≫ pullback.fst i a, by
    rw [Category.assoc, pullback.condition, IsIso.inv_hom_id_assoc]⟩

theorem natCast_ne_zero_of_isUnit_of_fieldPoint {S : Scheme.{0}} {n : ℕ}
    (hn : IsUnit (n : Γ(S, ⊤))) (Ω : Type) [Field Ω] (t : Sp Ω ⟶ S) : (n : Ω) ≠ 0 := by
  have h := hn.map ((Scheme.ΓSpecIso (.of Ω)).hom.hom.comp t.appTop.hom)
  rw [map_natCast] at h
  exact h.ne_zero

theorem finite_geometric_kernel_of_pow_eq_one :
    (∀ (k : Type) [Field k] [IsAlgClosed k] (B : Over (Sp k)) [GrpObj B] (n : ℕ), IsAbelianScheme B → n.Prime → (n : k) ≠ 0 → ∀ (C : Subgroup (𝟙_ (Over (Sp k)) ⟶ B)) (Z : Set B.left), IsClosed Z → (∀ x, x ∈ C ↔ Set.range x.left ⊆ Z) → (∀ x ∈ C, x ^ n = 1 → x = 1) → Finite C) → ∀ (S : Scheme.{0}) (G G' Ga : Over S) [GrpObj G] [GrpObj G'] [GrpObj Ga] (io : Ga ⟶ G ⊗ G') (n : ℕ), IsSemiAbelian G' → IsMonHom io → IsClosedImmersion io.left → n.Prime → IsUnit (n : Γ(S, ⊤)) → (∀ (Y : Over S) (x : Y ⟶ Ga), x ^ n = 1 → x ≫ io ≫ fst G G' = 1 → x = 1) → ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (t : Sp Ω ⟶ S), Finite {x : Over.mk t ⟶ Ga // x ≫ io ≫ fst G G' = 1} := by
  intro hab S G G' Ga _ _ _ io n hG' hio hcl hp hn htors Ω _ _ t
  suffices H : Finite {x : Over.mk ((𝟙_ (Over (Sp Ω))).hom ≫ t) ⟶ Ga //
      x ≫ io ≫ fst G G' = 1} by
    have e : (𝟙_ (Over (Sp Ω))).hom ≫ t = t := Category.id_comp t
    rwa [e] at H
  haveI := hG'.comm
  haveI := hG'.smooth
  haveI := hG'.quasiCompact
  have h := isGrpPullback_pullback G' t
  let T : Over S := Over.mk ((𝟙_ (Over (Sp Ω))).hom ≫ t)
  let ρ : (𝟙_ (Over (Sp Ω)) ⟶ (Over.pullback t).obj G') →* (T ⟶ G') := pushHom h _
  have hρ : ∀ y, (ρ y).left = y.left ≫ pullback.fst G'.hom t := fun y => rfl
  have hinj : Function.Injective ρ := fun y z hyz => by
    ext1
    refine pullback.hom_ext ?_ ((Over.w y).trans (Over.w z).symm)
    rw [← hρ, ← hρ, hyz]
  have hsurj : Function.Surjective ρ := fun x =>
    ⟨Over.homMk (pullback.lift x.left (𝟙_ (Over (Sp Ω))).hom (Over.w x)) (pullback.lift_snd _ _ _),
      Over.OverMorphism.ext (pullback.lift_fst _ _ _)⟩
  let s : G' ⟶ G ⊗ G' := lift 1 (𝟙 G')
  have hs₁ : ∀ y : T ⟶ G', (y ≫ s) ≫ fst G G' = 1 := fun y => by
    rw [Category.assoc, lift_fst, MonObj.comp_one]
  have hs₂ : ∀ y : T ⟶ G', (y ≫ s) ≫ snd G G' = y := fun y => by
    rw [Category.assoc, lift_snd, Category.comp_id]
  let σ : (T ⟶ G') →* (T ⟶ G ⊗ G') := MonoidHom.mk' (fun y => y ≫ s) fun y z => by
    refine CartesianMonoidalCategory.hom_ext _ _ ?_ ?_
    · rw [hs₁, MonObj.mul_comp, hs₁, hs₁, _root_.mul_one]
    · rw [hs₂, MonObj.mul_comp, hs₂, hs₂]
  let κ : (T ⟶ Ga) →* (T ⟶ G ⊗ G') :=
    MonoidHom.mk' (fun x => x ≫ io) fun x y => MonObj.mul_comp x y io
  haveI : Mono io := (Over.forget S).mono_of_mono_map (inferInstanceAs (Mono io.left))
  have hκ : Function.Injective κ := fun x y hxy => (cancel_mono io).1 hxy
  let C := κ.range.comap (σ.comp ρ)
  have hC : Finite C := by
    refine finite_of_isClosed_torusExtension_of_pow_eq_one hab Ω ((Over.pullback t).obj G') n
      (inferInstanceAs (LocallyOfFiniteType (pullback.snd G'.hom t)))
      (inferInstanceAs (QuasiCompact (pullback.snd G'.hom t))) (hG'.fibres Ω t) hp
      (natCast_ne_zero_of_isUnit_of_fieldPoint hn Ω t) C
      ((pullback.fst G'.hom t ≫ s.left) ⁻¹' Set.range io.left)
      (io.left.isClosedEmbedding.isClosed_range.preimage
        (pullback.fst G'.hom t ≫ s.left).continuous) (fun y => ⟨?_, fun hy => ?_⟩) ?_
    · rintro ⟨x, hx⟩ _ ⟨p, rfl⟩
      have e : x.left ≫ io.left = y.left ≫ pullback.fst G'.hom t ≫ s.left :=
        (congrArg (fun z => z.left) hx).trans (Category.assoc _ _ _)
      exact ⟨x.left p, by rw [← Scheme.Hom.comp_apply, e, Scheme.Hom.comp_apply]⟩
    · haveI : IsReduced T.left := inferInstanceAs (IsReduced (Sp Ω))
      obtain ⟨b, hb⟩ := exists_lift_of_isReduced_of_range_subset io.left (ρ y ≫ s).left (by
        rintro _ ⟨p, rfl⟩
        have e : (ρ y ≫ s).left = y.left ≫ pullback.fst G'.hom t ≫ s.left := Category.assoc _ _ _
        rw [e, Scheme.Hom.comp_apply]
        exact hy ⟨p, rfl⟩)
      exact ⟨Over.homMk b (by rw [← Over.w io, ← Category.assoc, hb, Over.w]),
        Over.OverMorphism.ext hb⟩
    · rintro y ⟨x, hx⟩ hy
      have hx1 : x = 1 := by
        refine htors T x (hκ ?_) ?_
        · rw [map_pow, hx, ← map_pow, hy, map_one, map_one]
        · rw [← Category.assoc]
          exact (congrArg (· ≫ fst G G') hx).trans (hs₁ _)
      refine hinj ?_
      rw [map_one, ← hs₂ (ρ y)]
      have e : ρ y ≫ s = 1 := hx.symm.trans (by rw [hx1, map_one])
      rw [e, MonObj.one_comp]
  choose r hr using hsurj
  have key : ∀ x : {x : T ⟶ Ga // x ≫ io ≫ fst G G' = 1},
      κ x.1 = σ (ρ (r (x.1 ≫ io ≫ snd G G'))) := fun x => by
    rw [hr]
    refine CartesianMonoidalCategory.hom_ext _ _ ?_ ?_
    · exact ((Category.assoc _ _ _).trans x.2).trans (hs₁ _).symm
    · exact (Category.assoc _ _ _).trans (hs₂ _).symm
  refine Finite.of_injective (fun x : {x : T ⟶ Ga // x ≫ io ≫ fst G G' = 1} =>
    (⟨r (x.1 ≫ io ≫ snd G G'), x.1, key x⟩ : C)) fun x y hxy => Subtype.ext (hκ ?_)
  rw [key x, key y, show r (x.1 ≫ io ≫ snd G G') = r (y.1 ≫ io ≫ snd G G') from
    congrArg Subtype.val hxy]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsUniqueFrameChangeByMatricesStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Frames
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.existsUnique_frameChangeByMatrices : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (S : Type) [CommRing S] [Algebra c.F S] (y : FrPt Xo c S) (g : (∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) S)) (a : Sˣ), (∀ τ, IsUnit (g τ).det) → ∃! y' : FrPt Xo c S, FrChg g (a : S) y y' := by
  first | exact @GlobalTheory.Frames.existsUnique_frChg | exact GlobalTheory.Frames.existsUnique_frChg | (intros; apply GlobalTheory.Frames.existsUnique_frChg <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExponentMatchingIndependentOfCuspBasisStatement
section
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Frames GlobalTheory.FrameUnif
open scoped Matrix nonZeroDivisors
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exponentMatching_independent_of_cuspBasis : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r ρ N : ℕ) (X : Data E r) (cu₀ cu : FJ.CuspFD X ρ) (P : Matrix (Fin ρ) (Fin ρ) E), IsUnit P.det → (∀ a, cu₀.e a = ∑ b, P a b • cu.e b) → (∀ χ, FJ.IsHermE χ → ((∀ β ∈ FJ.zGam X cu, ∃ n : ℤ, FJ.prE X χ β = n) ↔ ∀ u ∈ FJ.dualOE (FJ.XcFD 1 cu), ∀ m ∈ FJ.dualOE (FJ.XcFD 1 cu), (N : E) * ∑ i, ∑ k, u i * χ i k * cc (m k) ∈ Set.range (algebraMap (𝓞 E) E))) → ∀ χ, FJ.IsHermE χ → ((∀ β ∈ FJ.zGam X cu₀, ∃ n : ℤ, FJ.prE X χ β = n) ↔ ∀ u ∈ FJ.dualOE (FJ.XcFD 1 cu₀), ∀ m ∈ FJ.dualOE (FJ.XcFD 1 cu₀), (N : E) * ∑ i, ∑ k, u i * χ i k * cc (m k) ∈ Set.range (algebraMap (𝓞 E) E)) := by
  first | exact @GlobalTheory.CuspBasis.expoMatch_of_basis_change | exact GlobalTheory.CuspBasis.expoMatch_of_basis_change | (intros; apply GlobalTheory.CuspBasis.expoMatch_of_basis_change <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FrameChangeByMatricesReflAndCompStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Frames
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.frameChangeByMatrices_refl_and_comp : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (S : Type) [CommRing S] [Algebra c.F S] (y y' y'' : FrPt Xo c S), FrChg (fun _ => 1) 1 y y ∧ ∀ (g g' : (∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) S)) (a a' : S), FrChg g a y y' → FrChg g' a' y' y'' → FrChg (fun τ => g' τ * g τ) (a' * a) y y'' := by
  first | exact @GlobalTheory.Frames.frChg_refl_and_comp | exact GlobalTheory.Frames.frChg_refl_and_comp | (intros; apply GlobalTheory.Frames.frChg_refl_and_comp <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FrameChangeExistsUniqueOfSamePointStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Frames
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.frameChange_exists_unique_of_same_point : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (S : Type) [CommRing S] [Algebra c.F S] (y y' : FrPt Xo c S), (y'.x = y.x → ∃ (g : (∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) S)) (a : Sˣ), (∀ τ, IsUnit (g τ).det) ∧ FrChg g (a : S) y y') ∧ ∀ (g g' : (∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) S)) (a a' : S), FrChg g a y y' → FrChg g' a' y y' → g = g' ∧ a = a' := by
  first | exact @GlobalTheory.Frames.frChg_exists_unique | exact GlobalTheory.Frames.frChg_exists_unique | (intros; apply GlobalTheory.Frames.frChg_exists_unique <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsHolToFibPtAndCompFibreStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
theorem _root_.GlobalTheory.T.isHolTo_fibPt_and_comp_fibre : ∀ (X : Scheme.{0}) (G : Over X) (y : Sp ℂ ⟶ X) (g : ℕ) (e : (Fin g → ℂ) → (Over.mk y ⟶ G)), IsHolTo Set.univ (fun z => (e z).left) → IsHolTo Set.univ (fun z => fibPt G (e z)) ∧ ∀ (Y : Scheme.{0}) (ψ : pullback G.hom y ⟶ Y), IsHolTo Set.univ (fun z => fibPt G (e z) ≫ ψ) := by
  first | exact @GlobalTheory.HolFibre.isHolTo_fibPt_and_comp | exact GlobalTheory.HolFibre.isHolTo_fibPt_and_comp | (intros; apply GlobalTheory.HolFibre.isHolTo_fibPt_and_comp <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsHolToOfComponents
section
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Frames GlobalTheory.FrameUnif
open scoped Matrix nonZeroDivisors

namespace GlobalTheory.HolPullback

theorem isHolTo_of_components :
    ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] (B : Set V) (Y Y' S S' : Scheme.{0}) (φ : Y' ⟶ Y) (p' : Y' ⟶ S') (p : Y ⟶ S) (f : S' ⟶ S) (a : V → (Sp ℂ ⟶ Y')), IsPullback φ p' p f → IsOpen B → IsHolTo B (fun b => a b ≫ φ) → IsHolTo B (fun b => a b ≫ p') → IsHolTo B a :=
  fun _ _ _ _ _ _ _ _ _ _ _ _ _ H _ h₁ h₂ => GlobalTheory.HolFibre.isHolTo_of_isPullback H h₁ h₂

end GlobalTheory.HolPullback
end

