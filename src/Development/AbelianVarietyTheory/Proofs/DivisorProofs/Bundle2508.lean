import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0002
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PartialZetaFunctionalEquation
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0508
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0221
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0351
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0156
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.IsE8ThetaStructure
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2419
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0015
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0006
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0075
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0006
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2212
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2243
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsUniqueLbIsoPullEqOfCoheightLeOne
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsGloballyGeneratedIffGeneratingSections
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0630
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2410
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0016
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0001
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0076
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0072
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsImageHeightUnique
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MeasurePreservingRotBlock
import Development.AbelianVarietyTheory.Definitions.Divisors.LabRange
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1038
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1387

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HilbertEisensteinExpansionOfLipschitzHeckeZeta
section
noncomputable section

open NumberField GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.LatVal GlobalTheory.LatJet
open scoped nonZeroDivisors

namespace GlobalTheory.HilbertEis

theorem eisClass_summable_of_hecke (hH : HeckeWeightTwo) {F : Type} [Field F] [NumberField F] [IsTotallyReal F]
    (hf : 2 ≤ Module.finrank ℚ F) (𝔞 𝔟 : Frac F) {s : ℕ} (hs : 2 ≤ s) {z : Emb F → ℂ} (hz : z ∈ upperHalf F) :
    Summable (eisClass 𝔞 𝔟 (2 * s) 0 z) := by
  obtain ⟨G, hG, -, -⟩ := hH F hf 𝔞 𝔟
  have hre : 0 < ((s : ℂ) - 1).re := by
    simp only [Complex.sub_re, Complex.natCast_re, Complex.one_re, sub_pos]
    exact_mod_cast (by omega : 1 < s)
  have h1 := (hG.1 ((s : ℂ) - 1) hre z hz).1
  have h2 : Summable fun c => ‖eisClass 𝔞 𝔟 2 ((s : ℂ) - 1) z c‖ := summable_norm_iff.mpr h1
  refine Summable.of_norm (h2.congr fun c => ?_)
  have hP : ∏ τ, latPt z c.out.1 τ ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun τ _ => latPt_ne_zero hz c.out.2.2.2 τ
  have hn : 0 < ‖∏ τ, latPt z c.out.1 τ‖ := norm_pos_iff.2 hP
  have hr : (-2 * ((s : ℂ) - 1)).re = -((2 * (s - 1) : ℕ) : ℝ) := by
    rw [Nat.cast_mul, Nat.cast_sub (by omega : 1 ≤ s)]
    simp
  simp only [eisClass, eisTerm, norm_mul, norm_pow, norm_inv, Complex.norm_cpow_eq_rpow_re_of_pos hn, hr,
    mul_zero, Complex.zero_re, Real.rpow_zero, mul_one, Real.rpow_neg hn.le, Real.rpow_natCast, ← inv_pow, ← pow_add]
  congr 1
  omega

theorem dF_pos (F : Type) [Field F] [NumberField F] : 0 < dF F :=
  abs_pos.2 (by exact_mod_cast discr_ne_zero F)

theorem nrm_pos {F : Type} [Field F] [NumberField F] (𝔞 : Frac F) : 0 < nrm 𝔞 := by
  have h2 : FractionalIdeal.absNorm (𝔞 : FractionalIdeal (𝓞 F)⁰ F) ≠ 0 := by
    rw [Ne, FractionalIdeal.absNorm_eq_zero_iff]; exact 𝔞.ne_zero
  unfold nrm
  exact_mod_cast lt_of_le_of_ne (FractionalIdeal.absNorm_nonneg _) h2.symm

theorem const_eq (F : Type) [Field F] [NumberField F] (𝔞 : Frac F) (k : ℕ) :
    cK F k * (dF F * nrm 𝔞) ^ k / omegaFactor 𝔞 ^ k =
      ((k - 1).factorial : ℝ) ^ Module.finrank ℚ F * dF F ^ ((k : ℝ) - 1 / 2) := by
  have hd := dF_pos F
  have hn := nrm_pos 𝔞
  unfold cK omegaFactor
  rw [mul_pow, mul_pow, ← Real.rpow_natCast (dF F ^ _), ← Real.rpow_mul hd.le, ← Real.rpow_natCast (dF F) k]
  have h1 : dF F ^ ((1 : ℝ) / 2 * k) ≠ 0 := (Real.rpow_pos_of_pos hd _).ne'
  have h2 : nrm 𝔞 ^ k ≠ 0 := pow_ne_zero _ hn.ne'
  field_simp
  rw [← Real.rpow_add hd, ← Real.rpow_add hd]
  congr 1
  ring

theorem eisExp : GlobalTheory.IndefiniteRowSideFullHecke.TraceDualDifferent.Lipschitz → HeckeWeightTwo → GlobalTheory.Published.PartialZetaFunctionalEquation → EisExp := by
  intro hL hH hP F _ _ _ hf 𝔞 𝔟 s hs
  rcases Nat.lt_or_ge s 2 with h1 | h2
  · obtain rfl : s = 1 := by omega
    obtain ⟨G, hG, hd, he⟩ := hH F hf 𝔞 𝔟
    exact ⟨G 0, ⟨fun h => absurd rfl h, fun _ => ⟨G, hG, rfl⟩⟩, hd, he⟩
  have hsum : ∀ z ∈ upperHalf F, Summable (eisClass 𝔞 𝔟 (2 * s) 0 z) := fun z hz =>
    eisClass_summable_of_hecke hH hf 𝔞 𝔟 h2 hz
  refine ⟨eisSum 𝔞 𝔟 (2 * s) 0, ⟨fun _ z hz => (hsum z hz).hasSum, fun h => by omega⟩,
    GlobalTheory.T.hilbertEisensteinSeriesLattice_differentiableOn F 𝔞 𝔟 _ hsum, ?_⟩
  let D : (Ideal (𝓞 F))⁰ := ⟨differentIdeal ℤ (𝓞 F), mem_nonZeroDivisors_of_ne_zero (differentIdeal_ne_bot (A := ℤ))⟩
  obtain ⟨Z, Z', hZ, hZ', hfe⟩ := hP F (ClassGroup.mk0 D * ClassGroup.mk F 𝔞) (ClassGroup.mk F 𝔞)⁻¹ D rfl
    (by rw [mul_assoc, mul_inv_cancel, mul_one])
  refine ⟨Z', hZ', fun z hz => ?_⟩
  obtain ⟨hq, h3⟩ := GlobalTheory.T.hilbertEisenstein_nonconstant_terms_hasSum F hL 𝔞 𝔟 (2 * s) (by omega) (even_two_mul s) hsum z hz
  have h0 := GlobalTheory.T.hasSum_hilbertEisenstein_constantTerm_partialZeta F 𝔞 𝔟 s (by omega) D rfl Z hZ z hz
  have hfe' := hfe ((2 * s : ℕ) : ℂ) (fun n h => by
      have h' : ((2 * s : ℕ) : ℤ) = -2 * n := by exact_mod_cast h
      omega) (fun n h => by
      have h' : (1 - ((2 * s : ℕ) : ℤ)) = -2 * n := by exact_mod_cast h
      omega)
  have hc := GlobalTheory.T.gammaReal_functionalEquation_constant_even_integer (dF F) (dF_pos F) (Module.finrank ℚ F) s (by omega) _ _ hfe'
  refine ⟨hq, ?_⟩
  have hG := (HasSum.add_compl (f := eisClass 𝔞 𝔟 (2 * s) 0 z) (s := {c : Quotient (latRel 𝔞 𝔟) | c.out.1.2 = 0}) h0 h3).tsum_eq
  rw [show eisSum 𝔞 𝔟 (2 * s) 0 z = ∑' c, eisClass 𝔞 𝔟 (2 * s) 0 z c from rfl, hG]
  have hk := const_eq F 𝔞 (2 * s)
  have hω : (omegaFactor 𝔞 : ℂ) ≠ 0 := by
    unfold omegaFactor
    exact_mod_cast (mul_pos (Real.rpow_pos_of_pos (dF_pos F) _) (nrm_pos 𝔞)).ne'
  have hcK : (cK F (2 * s) : ℂ) ≠ 0 := by
    have : 0 < cK F (2 * s) := by
      unfold cK
      exact mul_pos (pow_pos (Nat.cast_pos.2 (Nat.factorial_pos _)) _) (Real.rpow_pos_of_pos (dF_pos F) _)
    exact_mod_cast this.ne'
  have hk' : (cK F (2 * s) : ℂ) * ((dF F * nrm 𝔞 : ℝ) : ℂ) ^ (2 * s) / (omegaFactor 𝔞 : ℂ) ^ (2 * s) =
      (((2 * s - 1).factorial : ℕ) : ℂ) ^ Module.finrank ℚ F * ((dF F ^ (((2 * s : ℕ) : ℝ) - 1 / 2) : ℝ) : ℂ) := by
    exact_mod_cast hk
  rw [← hc, ← hk']
  field_simp

end GlobalTheory.HilbertEis
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HodgeLineBundleEighthPowerIsoPow
section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM
open scoped CategoryTheory.Obj

namespace GlobalTheory.HodgePow

open GlobalTheory.VB GlobalTheory.LieVB GlobalTheory.CechPic

theorem lbIso_hodge_of_iso {S : Scheme.{0}} {A B : Over S} [GrpObj A] [GrpObj B] (e : A ≅ B)
    (he : η[A] ≫ e.hom = η[B]) (r : ℕ) (hA : IsVB (omega A) r) :
    IsVB (omega B) r ∧ LBIso (GlobalTheory.SiegelTor.hodge A r) (GlobalTheory.SiegelTor.hodge B r) := by
  have he' : η[B] ≫ e.inv = η[A] := by rw [← he, Category.assoc, e.hom_inv_id, Category.comp_id]
  let φ : omega A ≅ omega B :=
    { hom := cotMap e.inv he'
      inv := cotMap e.hom he
      hom_inv_id := (cotMap_comp he' he e.hom_inv_id (Category.comp_id _)).trans (cotMap_id rfl _)
      inv_hom_id := (cotMap_comp he he' e.inv_hom_id (Category.comp_id _)).trans (cotMap_id rfl _) }
  exact ⟨hA.of_iso φ, hA.lbIso_det_of_iso φ⟩

def prodUnitIso {S : Scheme.{0}} (G : Over S) : G ⊗ 𝟙_ (Over S) ≅ G where
  hom := fst _ _
  inv := lift (𝟙 G) (toUnit G)
  hom_inv_id := by ext1 <;> simp <;> exact toUnit_unique _ _
  inv_hom_id := by simp

section Pow

variable {S : Scheme.{0}} (G : Over S) [GrpObj G] [QuasiSeparated G.hom] (g : ℕ)

theorem cls_hodge_powObj [Smooth G.hom] [IsSeparated G.hom] [QuasiCompact G.hom]
    (hs : SmoothOfRelativeDimension g G.hom) (hG : IsVB (omega G) g) (n : ℕ) :
    ∃ h : IsVB (omega (powObj G (n + 1))) ((n + 1) * g),
      cls _ h.isLB_det = (n + 1) • cls _ hG.isLB_det := by
  have hV : ∀ m, IsVB (omega (powObj G m)) (m * g) := fun m => by
    haveI := (GlobalFunctionsDvrGeneric.powObj_props G m).2.1
    haveI := smoothOfRelativeDimension_powObj G g hs m
    exact isVB_omega _ _
  refine ⟨hV (n + 1), ?_⟩
  induction n with
  | zero =>
    have hE : η[G ⊗ 𝟙_ (Over S)] ≫ (prodUnitIso G).hom = η[G] := by simp [prodUnitIso]
    have h1 := hV 1
    rw [Nat.one_mul] at h1
    have := (lbIso_hodge_of_iso (prodUnitIso G) hE g h1).2
    rw [Nat.zero_add, one_smul]
    have hh : ∀ (r : ℕ) (hr : r = 1 * g) (h₁ : IsVB (omega (powObj G 1)) r),
        cls _ h₁.isLB_det = cls _ hG.isLB_det := by
      intro r hr h₁
      rw [Nat.one_mul] at hr
      subst hr
      exact (cls_eq_iff _ _).2 this
    exact hh _ rfl (hV 1)
  | succ n ih =>
    haveI := (GlobalFunctionsDvrGeneric.powObj_props G (n + 1)).2.1
    have key := GlobalTheory.HodgeProd.lbIso_det_conormal_prod G (powObj G (n + 1)) g ((n + 1) * g) hG (hV (n + 1))
      η[G ⊗ powObj G (n + 1)] (by ext1 <;> simp)
    have hT := isLB_tens hG.isLB_det (hV (n + 1)).isLB_det
    have hh : ∀ (r : ℕ) (hr : r = g + (n + 1) * g) (h₁ : IsVB (omega (powObj G (n + 1 + 1))) r),
        cls _ h₁.isLB_det = cls _ hG.isLB_det + cls _ (hV (n + 1)).isLB_det := by
      intro r hr h₁
      subst hr
      rw [← cls_tens _ _ hT]
      exact (cls_eq_iff _ _).2 key
    rw [hh _ (by ring) (hV _), ih, succ_nsmul' _ (n + 1)]

theorem one_powPr {n : ℕ} (i : Fin n) : η[powObj G n] ≫ powPr G i = η[G] := by
  haveI := powPr.isMonHom G i
  exact IsMonHom.one_hom _

end Pow

theorem hodge_eight_mul_iso_hodge_pow_eight : ∀ (S : Scheme.{0}) (G H : Over S) [GrpObj G] [GrpObj H] (g : ℕ) (pr : Fin 8 → (H ⟶ G)),
    (∀ u, IsMonHom (pr u)) → (∀ (T : Over S) (y : Fin 8 → (T ⟶ G)), ∃! x : T ⟶ H, ∀ u, x ≫ pr u = y u) →
    IsSemiAbelian G → SmoothOfRelativeDimension g G.hom →
    LBIso (GlobalTheory.SiegelTor.hodge H (8 * g)) (lbPow (GlobalTheory.SiegelTor.hodge G g) 8) := by
  intro S G H _ _ g pr hpr hU hG hs
  haveI := hG.smooth
  haveI := hG.separated
  haveI := hG.quasiCompact
  haveI : SmoothOfRelativeDimension g G.hom := hs
  have hVG : IsVB (omega G) g := isVB_omega G g
  obtain ⟨hP, hc⟩ := cls_hodge_powObj G g hs hVG 7
  let lim : IsLimit (Fan.mk H pr) := mkFanLimit _ (fun s => (hU s.pt s.proj).exists.choose)
    (fun s i => (hU s.pt s.proj).exists.choose_spec i)
    (fun s m hm => (hU s.pt s.proj).unique hm (hU s.pt s.proj).exists.choose_spec)
  let e : H ≅ powObj G 8 := lim.conePointUniqueUpToIso (powIsLimit G 8)
  have he : ∀ i, e.hom ≫ powPr G i = pr i := fun i =>
    lim.conePointUniqueUpToIso_hom_comp (powIsLimit G 8) ⟨i⟩
  have hη : η[powObj G 8] ≫ e.inv = η[H] := by
    refine lim.hom_ext fun ⟨i⟩ => ?_
    have h1 : e.inv ≫ pr i = powPr G i := by rw [← he, Iso.inv_hom_id_assoc]
    haveI := hpr i
    simp only [Fan.mk_π_app, Category.assoc, h1]
    exact (one_powPr G i).trans (IsMonHom.one_hom (pr i)).symm
  obtain ⟨hH, hiso⟩ := lbIso_hodge_of_iso e.symm hη (8 * g) hP
  have hL := hVG.isLB_det
  refine (cls_eq_iff hH.isLB_det (isLB_lbPow hL 8)).1 ?_
  rw [cls_lbPow hL, ← (cls_eq_iff hP.isLB_det hH.isLB_det).2 hiso]
  exact hc

end GlobalTheory.HodgePow
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdealPullbackLocallyGenerated
section
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.LogPair

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.IdealPull

theorem germ_appLE {X Y : Scheme.{0}} (t : Y ⟶ X) (U : X.Opens) (V : Y.Opens) (hV : V ≤ t ⁻¹ᵁ U)
    (y : Y) (hy : y ∈ V) (a : Γ(X, U)) :
    (Y.presheaf.germ V y hy).hom ((t.appLE U V hV).hom a) =
      (t.stalkMap y).hom ((X.presheaf.germ U (t y) (show t y ∈ U from hV hy)).hom a) := by
  show (Y.presheaf.germ V y hy).hom (resG Y hV ((t.app U).hom a)) = _
  rw [germ_resG]
  exact (Scheme.Hom.germ_stalkMap_apply t U y _ a).symm

theorem regAt_and_unitAt_div_gen : ∀ (Y₀ Y₁ : Scheme.{0}) [IsIntegral Y₁] (t : Y₁ ⟶ Y₀) (I : Y₀.IdealSheafData) (y : Y₁) (U : Y₀.Opens) (hx : t y ∈ U) (n : ℕ) (b : Fin n → Γ(Y₀, U)), (∀ (k : Fin n) (W : Y₀.affineOpens) (h : W.1 ≤ U), resG Y₀ h (b k) ∈ I.ideal W) → (∀ (W : Y₀.affineOpens) (hxW : t y ∈ W.1) (a : Γ(Y₀, W.1)), a ∈ I.ideal W → Y₀.presheaf.germ W.1 (t y) hxW a ∈ Ideal.span (Set.range fun k => Y₀.presheaf.germ U (t y) hx (b k))) → ∀ (U' : Y₁.affineOpens) (f : Γ(Y₁, U'.1)) (hyU' : y ∈ U'.1), fnOf U'.1 (gen_mem hyU') f ≠ 0 → (I.comap t).ideal U' = Ideal.span {f} → ∀ (V : Y₁.Opens) (hV : V ≤ t ⁻¹ᵁ U) (hyV : y ∈ V), (∀ k, RegAt y (fnOf V (gen_mem hyV) (t.appLE U V hV (b k)) / fnOf U'.1 (gen_mem hyU') f)) ∧ ∃ k, UnitAt y (fnOf V (gen_mem hyV) (t.appLE U V hV (b k)) / fnOf U'.1 (gen_mem hyU') f) := by
  intro Y₀ Y₁ _ t I y U hx n b hb hgerm U' f hyU' hf0 hU' V hV hyV
  obtain ⟨_, ⟨W, hWa, rfl⟩, hxW, hWU⟩ := Y₀.isBasis_affineOpens.exists_subset_of_mem_open hx U.isOpen
  have hWU' : W ≤ U := hWU
  obtain ⟨_, ⟨V₀, hV₀a, rfl⟩, hyV₀, hV₀le⟩ := Y₁.isBasis_affineOpens.exists_subset_of_mem_open
    (show y ∈ U'.1 ⊓ t ⁻¹ᵁ W from ⟨hyU', hxW⟩) (U'.1 ⊓ t ⁻¹ᵁ W).isOpen
  have hV₀U' : V₀ ≤ U'.1 := fun z hz => (hV₀le hz).1
  have hV₀W : V₀ ≤ t ⁻¹ᵁ W := fun z hz => (hV₀le hz).2
  let R := Y₁.presheaf.stalk y
  let g : R := (Y₁.presheaf.germ U'.1 y hyU').hom f
  let β : Fin n → R := fun k => (t.stalkMap y).hom ((Y₀.presheaf.germ U (t y) hx).hom (b k))
  have hI1 : (I.comap t).ideal ⟨V₀, hV₀a⟩ = Ideal.span {resG Y₁ hV₀U' f} := by
    rw [← (I.comap t).map_ideal (U := ⟨V₀, hV₀a⟩) (V := U') hV₀U', hU', Ideal.map_span,
      Set.image_singleton]
    rfl
  have hI2 := GlobalTheory.Principalise.comapIdealAffine I t ⟨W, hWa⟩ ⟨V₀, hV₀a⟩ hV₀W
  have hgf : (Y₁.presheaf.germ V₀ y hyV₀).hom (resG Y₁ hV₀U' f) = g := germ_resG _ _ _ _
  have hc : ∀ k, ∃ c : R, β k = c * g := by
    intro k
    have hmem : (t.appLE W V₀ hV₀W).hom (resG Y₀ hWU' (b k)) ∈ (I.comap t).ideal ⟨V₀, hV₀a⟩ := by
      rw [hI2]; exact Ideal.mem_map_of_mem _ (hb k ⟨W, hWa⟩ hWU')
    rw [hI1, Ideal.mem_span_singleton'] at hmem
    obtain ⟨c, hc⟩ := hmem
    refine ⟨(Y₁.presheaf.germ V₀ y hyV₀).hom c, ?_⟩
    have := congrArg (Y₁.presheaf.germ V₀ y hyV₀).hom hc
    rw [map_mul, hgf, germ_appLE, germ_resG] at this
    exact this.symm
  choose c hcβ using hc
  have hgmem : g ∈ Ideal.span (Set.range β) := by
    have hmem : resG Y₁ hV₀U' f ∈ (I.comap t).ideal ⟨V₀, hV₀a⟩ := by
      rw [hI1]; exact Ideal.mem_span_singleton_self _
    rw [hI2] at hmem
    have h2 := Ideal.mem_map_of_mem (Y₁.presheaf.germ V₀ y hyV₀).hom hmem
    rw [hgf, Ideal.map_map] at h2
    refine (Ideal.map_le_iff_le_comap.2 ?_) h2
    intro a ha
    rw [Ideal.mem_comap, RingHom.comp_apply, germ_appLE]
    have h3 := Ideal.mem_map_of_mem (t.stalkMap y).hom (hgerm ⟨W, hWa⟩ hxW a ha)
    rw [Ideal.map_span, ← Set.range_comp] at h3
    exact h3
  have hfK : algebraMap R Y₁.functionField g = fnOf U'.1 (gen_mem hyU') f := algebraMap_germ hyU' f
  have hg0 : g ≠ 0 := fun h => hf0 (by rw [← hfK, h, map_zero])
  have hFk : ∀ k, fnOf V (gen_mem hyV) (t.appLE U V hV (b k)) / fnOf U'.1 (gen_mem hyU') f =
      algebraMap R Y₁.functionField (c k) := by
    intro k
    rw [← algebraMap_germ hyV, ← hfK, germ_appLE]
    change algebraMap R _ (β k) / _ = _
    rw [hcβ k, map_mul, mul_div_assoc, div_self (hfK ▸ hf0), mul_one]
  refine ⟨fun k => hFk k ▸ ⟨c k, rfl⟩, ?_⟩
  obtain ⟨e, he⟩ := (Submodule.mem_span_range_iff_exists_fun R).1 hgmem
  have hsum : ∑ k, e k * c k = 1 := by
    have : (∑ k, e k * c k) * g = 1 * g := by
      rw [one_mul, Finset.sum_mul]
      conv_rhs => rw [← he]
      exact Finset.sum_congr rfl fun k _ => by rw [hcβ k, smul_eq_mul, mul_assoc]
    exact mul_right_cancel₀ hg0 this
  obtain ⟨k, hk⟩ : ∃ k, IsUnit (c k) := by
    by_contra hcon
    push_neg at hcon
    have : (1 : R) ∈ IsLocalRing.maximalIdeal R := hsum ▸ Ideal.sum_mem _ fun k _ =>
      Ideal.mul_mem_left _ _ ((IsLocalRing.mem_maximalIdeal _).2 (hcon k))
    exact (Ideal.ne_top_iff_one _).1 (IsLocalRing.maximalIdeal.isMaximal R).ne_top this
  exact ⟨k, c k, hk, (hFk k).symm⟩

end GlobalTheory.IdealPull
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdealSectionsLocallyGenerated
section
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.LogPair

namespace GlobalTheory

theorem Twist.exists_secs_generating_ideal : ∀ (X : Scheme.{0}) (M : LB X), M.IsLB → ∀ (I : X.IdealSheafData), IsGloballyGenerated (twist (idealModule I) M) → ∃ (n : ℕ) (σ : Fin n → M.Sec), (∀ (k : Fin n) (i : M.ι) (W : X.affineOpens) (h : W.1 ≤ M.U i), resG X h ((σ k).f i) ∈ I.ideal W) ∧ ∀ (x : X) (i : M.ι) (hx : x ∈ M.U i) (W : X.affineOpens) (hxW : x ∈ W.1) (a : Γ(X, W.1)), a ∈ I.ideal W → X.presheaf.germ W.1 x hxW a ∈ Ideal.span (Set.range fun k => X.presheaf.germ (M.U i) x hx ((σ k).f i)) := by
  intro X M hM I hg
  obtain ⟨n, a, ha⟩ := isGloballyGenerated_iff_spanStalks.1 hg
  refine ⟨n, fun k => Twist.secOfTwist (idealModuleι I) (a k), ?_, ?_⟩
  · intro k i W h
    have hW : W.1 ≤ ⊤ ⊓ M.U i := le_inf le_top h
    rw [Twist.secOfTwist_f, LB.resG_resG]
    refine (exists_idealModuleι_app_eq_iff_mem I W _).1
      ⟨Twist.resM _ hW (Twist.coord (a k) i), ?_⟩
    rw [Twist.app_resM]
    exact structureModuleSectionsEquiv_res hW _
  · intro x i hx W hxW f hf
    obtain ⟨t, rfl⟩ := (exists_idealModuleι_app_eq_iff_mem I W f).2 hf
    let l := (structureModuleStalkEquiv x).toLinearMap ∘ₗ stalkLinear (idealModuleι I) x ∘ₗ
      (Twist.stalkEquiv (idealModule I) hM i hx).toLinearMap
    have hm : x ∈ ⊤ ⊓ M.U i := ⟨trivial, hx⟩
    have e : (l ∘ fun k => ((twist (idealModule I) M).presheaf.germ ⊤ x trivial (a k) :
        ((twist (idealModule I) M).presheaf.stalk x :))) =
        fun k => X.presheaf.germ (M.U i) x hx ((Twist.secOfTwist (idealModuleι I) (a k)).f i) := by
      funext k
      rw [Twist.secOfTwist_f, X.presheaf.germ_res_apply (homOfLE _) x hx]
      rw [Function.comp_apply, ← structureModuleStalkEquiv_germ, ← stalkLinear_germ]
      exact congrArg (fun u => structureModuleStalkEquiv x (stalkLinear (idealModuleι I) x u))
        (Twist.stalkEquiv_germ hM i hx (V := ⊤) trivial (a k))
    have hu : X.presheaf.germ W.1 x hxW
        (structureModuleSectionsEquiv W.1 ((idealModuleι I).app W t)) =
        l ((Twist.stalkEquiv (idealModule I) hM i hx).symm
          ((idealModule I).presheaf.germ W.1 x hxW t)) := by
      simp only [l, LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply,
        stalkLinear_germ, structureModuleStalkEquiv_germ]
    have hmem : (Twist.stalkEquiv (idealModule I) hM i hx).symm
        ((idealModule I).presheaf.germ W.1 x hxW t) ∈ Submodule.span (X.presheaf.stalk x)
          (Set.range fun k => ((twist (idealModule I) M).presheaf.germ ⊤ x trivial (a k) :
            ((twist (idealModule I) M).presheaf.stalk x :))) := by
      rw [ha x]; exact Submodule.mem_top
    have h2 := Submodule.apply_mem_span_image_of_mem_span l hmem
    rw [← Set.range_comp, e] at h2
    rw [hu]
    exact h2

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdealSheafLeOfLeOnReductionsJacobsonStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.AbLaw GlobalTheory.FormalAlg
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.idealSheaf_le_of_le_on_reductions_jacobson : ∀ (R : Type) [CommRing R] (I : Ideal R), I ≤ Ideal.jacobson ⊥ → ∀ (V : Scheme.{0}) [IsLocallyNoetherian V] (p : V ⟶ Spec (CommRingCat.of R)) (a a' : V.IdealSheafData), UniversallyClosed (a'.subschemeι ≫ p) → (∀ e : ℕ, a ≤ a' ⊔ baseIdeal p (I ^ (e + 1))) → a ≤ a' := by
  first | exact @GlobalTheory.FormalAlg.le_of_le_reductions | exact GlobalTheory.FormalAlg.le_of_le_reductions | (intros; apply GlobalTheory.FormalAlg.le_of_le_reductions <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ImageHeightAddLogNonneg
section
set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O
open scoped ENNReal Classical

namespace GlobalTheory.ImageHeightNonneg

theorem IsImageHeight.neg_log_le {K V Ω : Type} [Field K] [NumberField K] [AddCommGroup V] [Module K V] [Module (𝓞 K) V]
    [IsScalarTower (𝓞 K) K V] [Field Ω] [Algebra K Ω] {Nm : (K →+* ℂ) → V → ℝ} {L : Submodule (𝓞 K) V}
    {ev : V →ₗ[K] Ω} {d n : ℕ} {w : Fin n → V} {abelian₂ h : ℝ} (hs : Submodule.span K (L : Set V) = ⊤)
    (hw : Submodule.span (𝓞 K) (Set.range w) = L) (hle : ∀ i σ, Nm σ (w i) ≤ abelian₂) (hh : IsImageHeight Nm L ev d h) :
    0 ≤ h + Real.log abelian₂ := by
  obtain ⟨N, n', b, w', A, δ, f, hF, hf, e⟩ := hh
  have hF' : IsFrame Nm L b (Matrix.of fun j k => b.repr (w k) j) A := by
    refine ⟨?_, ?_, hF.herm, hF.conj, hF.norm⟩
    · simp only [Matrix.of_apply, Module.Basis.sum_repr]; exact hw
    · have h1 : Submodule.span K (Set.range w) = ⊤ := by rw [← hs, ← hw, Submodule.span_span_of_tower]
      have h2 := congrArg (Submodule.map b.equivFun.toLinearMap) h1
      rw [Submodule.map_span, ← Set.range_comp, Submodule.map_top, LinearEquiv.range] at h2
      exact h2
  have h1 := GlobalTheory.ImageHeightUnique.formHeight_linSubst hF hF' δ f
  rw [Module.Basis.toMatrix_self, GlobalTheory.HeightUnique.linSubst_one] at h1
  obtain ⟨y, hy, -⟩ := hf.exists_point
  obtain ⟨j, -⟩ := Function.ne_iff.1 hy
  have h2 := GlobalTheory.FormHtLower.formHeight_ge (Λ := abelian₂) (Fin.pos j) hF'.full hF'.herm
    (fun k σ => (hF.norm σ (w k)).trans_le (hle k σ)) hf.ne_zero hf.homog
  rw [h1, ← e] at h2
  have hpos : (0 : ℝ) < ((d : ℝ) + 1) * δ := mul_pos (by positivity) (Nat.cast_pos.2 hf.pos)
  refine nonneg_of_mul_nonneg_right (a := ((d : ℝ) + 1) * δ) ?_ hpos
  push_cast at h2
  linarith

theorem imageHeight_add_log_nonneg (K V Ω : Type) [Field K] [NumberField K] [IsTotallyComplex K] [AddCommGroup V]
    [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [Field Ω] [Algebra K Ω] (Nm : (K →+* ℂ) → V → ℝ)
    (L : Submodule (𝓞 K) V) (ev : V →ₗ[K] Ω) (d n : ℕ) (w : Fin n → V) (abelian₂ : ℝ) (hG : HasGram Nm)
    (hc : ∀ σ x, Nm ((starRingEnd ℂ).comp σ) x = Nm σ x) (hs : Submodule.span K (L : Set V) = ⊤)
    (hw : IsShortGen Nm L w abelian₂) (hd : 0 < imageDeg ev d) : 0 ≤ imageHeight Nm L ev d + Real.log abelian₂ := by
  have hL : Submodule.span (𝓞 K) (Set.range w) = L :=
    le_antisymm (Submodule.span_le.2 fun x hx => (hw.gen x).2 (Submodule.subset_span hx))
      fun x hx => Submodule.span_le_restrictScalars ℤ (𝓞 K) _ ((hw.gen x).1 hx)
  have hK : ∀ σ : K →+* ℂ, (starRingEnd ℂ).comp σ ≠ σ := fun σ h =>
    IsTotallyComplex.complexEmbedding_not_isReal σ h
  exact IsImageHeight.neg_log_le hs hL hw.le (isImageHeight_imageHeight (exists_isImageHeight_iff.2
    ⟨exists_isFrame hK hc hG (hL ▸ Submodule.fg_span (Set.finite_range _)) hs, hd⟩))

theorem imageHeight_nonneg : Hypotheses2 → ∀ (K V Ω : Type) [Field K] [NumberField K] [IsTotallyComplex K] [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [Field Ω] [Algebra K Ω] (Nm : (K →+* ℂ) → V → ℝ) (L : Submodule (𝓞 K) V) (ev : V →ₗ[K] Ω) (d n : ℕ) (w : Fin n → V) (abelian₂ : ℝ), HasGram Nm → (∀ σ x, Nm ((starRingEnd ℂ).comp σ) x = Nm σ x) → Submodule.span K (L : Set V) = ⊤ → IsShortGen Nm L w abelian₂ → 0 < imageDeg ev d → 0 ≤ imageHeight Nm L ev d + Real.log abelian₂ :=
  fun _ => imageHeight_add_log_nonneg

end GlobalTheory.ImageHeightNonneg
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ImportsExtraTail
section
noncomputable section

open AlgebraicGeometry CategoryTheory

namespace GlobalTheory.FactorAndSection

theorem exists_factor {R K A : Type} [CommRing R] [IsDomain R] [IsIntegrallyClosed R] [Field K] [Algebra R K]
    [IsFractionRing R K] [CommRing A] (φ : R →+* A) (hφ : φ.IsIntegral) (ψ : A →+* K)
    (h : ψ.comp φ = algebraMap R K) : ∃ χ : A →+* R, (algebraMap R K).comp χ = ψ ∧ χ.comp φ = RingHom.id R := by
  have hinj : Function.Injective (algebraMap R K) := IsFractionRing.injective R K
  have hmem : ∀ a : A, ψ a ∈ (algebraMap R K).range := by
    intro a
    have h1 : (ψ.comp φ).IsIntegralElem (ψ a) := (hφ a).map ψ
    rw [h] at h1
    exact (IsIntegrallyClosed.isIntegral_iff (R := R) (K := K)).1 h1
  let e : R ≃+* (algebraMap R K).range := RingEquiv.ofBijective (algebraMap R K).rangeRestrict
    ⟨fun a b hab => hinj (congrArg Subtype.val hab), (algebraMap R K).rangeRestrict_surjective⟩
  have he : ∀ z : (algebraMap R K).range, algebraMap R K (e.symm z) = z.1 := fun z =>
    congrArg Subtype.val (e.apply_symm_apply z)
  have h1 : (algebraMap R K).comp (e.symm.toRingHom.comp (ψ.codRestrict _ hmem)) = ψ := by
    ext a
    exact he _
  refine ⟨e.symm.toRingHom.comp (ψ.codRestrict _ hmem), h1, ?_⟩
  ext r
  apply hinj
  have h2 := congrArg (fun f : A →+* K => f (φ r)) h1
  have h3 := congrArg (fun f : R →+* K => f r) h
  exact h2.trans h3

theorem exists_section {R K : Type} [CommRing R] [IsDomain R] [IsIntegrallyClosed R] [Field K] [Algebra R K]
    [IsFractionRing R K] {Z : Scheme.{0}} (p : Z ⟶ ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp R) [IsFinite p]
    (y : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp K ⟶ Z) (hy : y ≫ p = ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (algebraMap R K)) :
    ∃ x : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp R ⟶ Z,
      ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (algebraMap R K) ≫ x = y ∧ x ≫ p = 𝟙 (ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp R) := by
  haveI : IsAffine Z := isAffine_of_isAffineHom p
  obtain ⟨φ, hφ⟩ := Spec.map_surjective (Z.isoSpec.inv ≫ p)
  obtain ⟨ψ, hψ⟩ := Spec.map_surjective (y ≫ Z.isoSpec.hom)
  have hfin : IsFinite (Spec.map φ) := by rw [hφ]; infer_instance
  have hint : φ.hom.IsIntegral := ((IsFinite.SpecMap_iff φ).1 hfin).to_isIntegral
  have hc : φ ≫ ψ = CommRingCat.ofHom (algebraMap R K) := by
    apply Spec.map_injective
    rw [Spec.map_comp, hφ, hψ, Category.assoc, Iso.hom_inv_id_assoc, hy]
  obtain ⟨χ, h1, h2⟩ := exists_factor (R := R) (K := K) φ.hom hint ψ.hom (congrArg CommRingCat.Hom.hom hc)
  have h1' : CommRingCat.ofHom χ ≫ CommRingCat.ofHom (algebraMap R K) = ψ := CommRingCat.hom_ext h1
  have h2' : φ ≫ CommRingCat.ofHom χ = 𝟙 _ := CommRingCat.hom_ext h2
  refine ⟨Spec.map (CommRingCat.ofHom χ) ≫ Z.isoSpec.inv, ?_, ?_⟩
  · rw [← Category.assoc, ← Spec.map_comp, h1', hψ, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  · rw [Category.assoc, ← hφ, ← Spec.map_comp, h2', Spec.map_id]

end GlobalTheory.FactorAndSection
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InertPlaceStabilizerFixesVacuumLeftStatement
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.KFinLoc
open scoped TensorProduct Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.inertPlace_stabilizer_fixes_vacuum_left : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl F) (w : HeightOneSpectrum (𝓞 E)), Formalism.UG.IsInertAt F E v w → v ∉ X.T →
    ∀ k ∈ GlobalTheory.InertSph.KAt σ G.V' v, Acts (evFin F v) (om' (k, 1)) (G.M'.vac v) (G.M'.vac v) := by
  first | exact @GlobalTheory.InertSphLeft.vac_fixed_left | exact GlobalTheory.InertSphLeft.vac_fixed_left | (intros; apply GlobalTheory.InertSphLeft.vac_fixed_left <;> assumption)
end

