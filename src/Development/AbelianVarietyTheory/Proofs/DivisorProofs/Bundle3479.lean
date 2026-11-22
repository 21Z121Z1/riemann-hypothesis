import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3462
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3463
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3452
import Development.AbelianVarietyTheory.Definitions.Divisors.IsRatioOfWeight
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0005
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3187
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3201
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3200
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3289
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3457
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3208
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NontrivialIsomClassInt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3439
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsToricRankOne
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0226
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2875
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TranslateUnique
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3468
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2979
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0101
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DerivativeCechCocycleInvariantVectorFieldIsCobou
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.MemRangeCompIffOfIsClosedImmersion
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3459
import Development.AbelianVarietyTheory.Definitions.Divisors.NormNegCmConstantEqAtAllEmbeddings
import Formalism.LocalRingCardinality.Bundle0003
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0072
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0066
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0051
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Development.AbelianVarietyTheory.Definitions.Divisors.WedgeNrmLeOfWedgeNormLe
import Development.AbelianVarietyTheory.Definitions.Divisors.IsHomWeightHomWeight
import Development.AbelianVarietyTheory.Definitions.Divisors.MemLevEigenIffTransl
import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.RealCubicMeans.LogMeanShares.LogMeanStatements.Bundle0001
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0058
import Development.AbelianVarietyTheory.Definitions.Divisors.BadElt
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0073
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0089
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactificationBis
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3461
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3409
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3401
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3434
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3443

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsZarhinSymplecticTransfer
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor GlobalTheory.EndLoc
open Matrix

namespace GlobalTheory.ZarhinFam.KappaEx

def omegaB (h : ℕ) : (Fin h ⊕ Fin h → ℤ) →ₗ[ℤ] (Fin h ⊕ Fin h → ℤ) →ₗ[ℤ] ℤ :=
  LinearMap.mk₂ ℤ omegaStd
    (fun a a' b => by
      simp only [omegaStd, Pi.add_apply, ← Finset.sum_add_distrib]; congr 1; funext i; ring)
    (fun c a b => by
      simp only [omegaStd, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]; congr 1; funext i; ring)
    (fun a b b' => by
      simp only [omegaStd, Pi.add_apply, ← Finset.sum_add_distrib]; congr 1; funext i; ring)
    (fun c a b => by
      simp only [omegaStd, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]; congr 1; funext i; ring)

theorem omegaB_apply (h : ℕ) (a b : Fin h ⊕ Fin h → ℤ) : omegaB h a b = omegaStd a b := rfl

def emb (h : ℕ) (l : Fin 8) : Fin h ⊕ Fin h → Fin (8 * h) ⊕ Fin (8 * h) :=
  Sum.map (fun i => finProdFinEquiv (l, i)) (fun i => finProdFinEquiv (l, i))

def blk (h : ℕ) (l : Fin 8) : (Fin (8 * h) ⊕ Fin (8 * h) → ℤ) →+ (Fin h ⊕ Fin h → ℤ) where
  toFun a := a ∘ emb h l
  map_zero' := rfl
  map_add' _ _ := rfl

theorem omegaStd_eq_sum_blk (h : ℕ) (a b : Fin (8 * h) ⊕ Fin (8 * h) → ℤ) :
    omegaStd a b = ∑ l, omegaStd (blk h l a) (blk h l b) := by
  simp only [omegaStd]
  rw [← (finProdFinEquiv (m := 8) (n := h)).sum_comp, Fintype.sum_prod_type]
  rfl

def vMat (d : ℕ) : Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) ℤ := fromBlocks 1 (-(quat d)ᵀ) 0 1

theorem vMat_transpose_mul_form_mul {d : ℕ} (hd : 0 < d) : (vMat d)ᵀ * form d * vMat d = 1 := by
  have h1 : ((d - 1 : ℕ) : ℤ) = (d : ℤ) - 1 := by omega
  rw [vMat, form, fromBlocks_transpose, fromBlocks_multiply, fromBlocks_multiply, ← fromBlocks_one]
  congr 1 <;> simp [Matrix.mul_neg, Matrix.neg_mul, quat_mul_transpose, h1, sub_smul]

theorem sum_sig {β : Type} [AddCommMonoid β] (g : Fin 4 ⊕ Fin 4 → β) : ∑ k, g (sig k) = ∑ s, g s := by
  simp [Fin.sum_univ_succ, Fintype.sum_sum_type, sig, add_assoc]

theorem sig_injective : Function.Injective sig := by
  intro k l hkl
  fin_cases k <;> fin_cases l <;> simp_all [sig]

def kap (h d : ℕ) (k : Fin 8) : (Fin (8 * h) ⊕ Fin (8 * h) → ℤ) →+ (Fin h ⊕ Fin h → ℤ) :=
  ∑ l, vMat d (sig k) (sig l) • blk h l

theorem kap_apply (h d : ℕ) (k : Fin 8) (a : Fin (8 * h) ⊕ Fin (8 * h) → ℤ) :
    kap h d k a = ∑ l, vMat d (sig k) (sig l) • blk h l a := by
  unfold kap
  rw [AddMonoidHom.finset_sum_apply]
  rfl

theorem inner_sum (d : ℕ) (m n : Fin 8) :
    ∑ k, ∑ l, vMat d (sig k) (sig m) * form d (sig k) (sig l) * vMat d (sig l) (sig n) =
      ((vMat d)ᵀ * form d * vMat d) (sig m) (sig n) := by
  have e1 : ∑ k, ∑ l, vMat d (sig k) (sig m) * form d (sig k) (sig l) * vMat d (sig l) (sig n) =
      ∑ p, ∑ l, vMat d p (sig m) * form d p (sig l) * vMat d (sig l) (sig n) :=
    sum_sig (fun p => ∑ l, vMat d p (sig m) * form d p (sig l) * vMat d (sig l) (sig n))
  have e2 : ∀ p, ∑ l, vMat d p (sig m) * form d p (sig l) * vMat d (sig l) (sig n) =
      ∑ q, vMat d p (sig m) * form d p q * vMat d q (sig n) :=
    fun p => sum_sig (fun q => vMat d p (sig m) * form d p q * vMat d q (sig n))
  rw [e1, Finset.sum_congr rfl fun p _ => e2 p]
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Finset.sum_mul]
  rw [Finset.sum_comm]

theorem formZ_kap {h d : ℕ} (hd : 0 < d) (a b : Fin (8 * h) ⊕ Fin (8 * h) → ℤ) :
    formZ d h (fun k => kap h d k a) (fun k => kap h d k b) = omegaStd a b := by
  have e2 : ∀ k l, omegaStd (kap h d k a) (kap h d l b) =
      ∑ m, ∑ n, vMat d (sig k) (sig m) * vMat d (sig l) (sig n) * omegaStd (blk h m a) (blk h n b) := by
    intro k l
    rw [← omegaB_apply, kap_apply, kap_apply]
    simp only [map_sum, map_zsmul, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul,
      omegaB_apply, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun n _ => ?_
    ring
  simp only [formZ, e2, Finset.mul_sum]
  have e3 : ∀ m n, ∑ k, ∑ l, form d (sig k) (sig l) *
      (vMat d (sig k) (sig m) * vMat d (sig l) (sig n) * omegaStd (blk h m a) (blk h n b)) =
      ((vMat d)ᵀ * form d * vMat d) (sig m) (sig n) * omegaStd (blk h m a) (blk h n b) := by
    intro m n
    rw [← inner_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun l _ => ?_
    ring
  calc ∑ k, ∑ l, ∑ m, ∑ n, form d (sig k) (sig l) *
        (vMat d (sig k) (sig m) * vMat d (sig l) (sig n) * omegaStd (blk h m a) (blk h n b))
      = ∑ k, ∑ m, ∑ n, ∑ l, form d (sig k) (sig l) *
        (vMat d (sig k) (sig m) * vMat d (sig l) (sig n) * omegaStd (blk h m a) (blk h n b)) := by
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun m _ => Finset.sum_comm
    _ = ∑ m, ∑ n, ∑ k, ∑ l, form d (sig k) (sig l) *
        (vMat d (sig k) (sig m) * vMat d (sig l) (sig n) * omegaStd (blk h m a) (blk h n b)) := by
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun m _ => Finset.sum_comm
    _ = ∑ m, ∑ n, ((vMat d)ᵀ * form d * vMat d) (sig m) (sig n) * omegaStd (blk h m a) (blk h n b) := by
        simp only [e3]
    _ = omegaStd a b := by
        rw [vMat_transpose_mul_form_mul hd, omegaStd_eq_sum_blk]
        simp [Matrix.one_apply, sig_injective.eq_iff]

theorem blk_jlMap (h : ℕ) (l : Fin 8) (a : Fin h ⊕ Fin h → ℤ) :
    blk h l (jlMap h a) = if l = 0 then a else 0 := by
  funext x
  split_ifs with hl
  · subst hl
    rcases x with i | i <;> simp [blk, emb, jlMap]
  · have hl1 : 1 ≤ (l : ℕ) := Nat.one_le_iff_ne_zero.mpr fun h0 => hl (Fin.ext h0)
    rcases x with i | i <;> simp only [blk, emb, jlMap, AddMonoidHom.coe_mk, ZeroHom.coe_mk, Function.comp_apply,
      Sum.map_inl, Sum.map_inr, Pi.zero_apply] <;> rw [dif_neg] <;> simp only [finProdFinEquiv_apply_val, not_lt] <;>
      nlinarith [i.2]

theorem kap_jlMap (h d : ℕ) (k : Fin 8) (a : Fin h ⊕ Fin h → ℤ) :
    kap h d k (jlMap h a) = if k = 0 then a else 0 := by
  rw [kap_apply]
  simp only [blk_jlMap, smul_ite, smul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  fin_cases k <;> simp [vMat, sig]

end GlobalTheory.ZarhinFam.KappaEx

namespace GlobalTheory.ZarhinFam

open KappaEx in

theorem exists_kappaOK : ∀ (h M d : ℕ), 1 ≤ h → 3 ≤ M → Odd M → 0 < d → M.Coprime d →
    ∃ κ : Fin 8 → (Fin (8 * h) ⊕ Fin (8 * h) → ℤ) →+ (Fin h ⊕ Fin h → ℤ), GlobalTheory.ZarhinFam.KappaOK h M d κ := by
  intro h M d _ _ _ hd _
  refine ⟨kap h d, fun a b => ?_, fun a => ?_, fun k hk a => ?_⟩
  · rw [formZ_kap hd]
  · rw [kap_jlMap, if_pos rfl]
  · rw [kap_jlMap, if_neg hk]

end GlobalTheory.ZarhinFam
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FibreKilled
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor GlobalTheory.EndLoc
open scoped CategoryTheory.Obj

namespace GlobalTheory.KerKilledNear

def FibreKilled (d : ℕ) {S' : Scheme.{0}} (G : Over S') [GrpObj G] (P : LB (G2 G).left) (s : S') : Prop :=
  ∀ (T' : Over S') (x : T' ⟶ G),
    (∃ f : T'.left ⟶ Spec (S'.residueField s), T'.hom = f ≫ S'.fromSpecResidueField s) →
    (∃ c : (P.pull (lift (snd G T' ≫ x) (fst G T')).left).Gen, c.IsGen) → x ^ d = 1

end GlobalTheory.KerKilledNear
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteMaximalIdealsContainingNatCast
section
noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LowDat GlobalTheory.LowFilt

namespace GlobalTheory.LowDat

theorem finite_maximal_ideals_containing_natCast :
    ∀ {E : Type} [Field E] [NumberField E] (n : ℕ) (hn : 0 < n),
    {𝔮 : Ideal (𝓞 E) | 𝔮.IsMaximal ∧ (n : 𝓞 E) ∈ 𝔮}.Finite := by
  intro E _ _ n hn
  have hn0 : (n : 𝓞 E) ≠ 0 := by exact_mod_cast hn.ne'
  have hI : Ideal.span {(n : 𝓞 E)} ≠ 0 := by
    simpa [Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot] using hn0
  refine ((Ideal.finite_factors hI).image
    (fun v : IsDedekindDomain.HeightOneSpectrum (𝓞 E) => v.asIdeal)).subset ?_
  rintro 𝔮 ⟨hmax, hmem⟩
  have hne : 𝔮 ≠ ⊥ := by
    intro h
    rw [h, Ideal.mem_bot] at hmem
    exact hn0 hmem
  refine ⟨⟨𝔮, hmax.isPrime, hne⟩, ?_, rfl⟩
  show 𝔮 ∣ Ideal.span {(n : 𝓞 E)}
  rw [Ideal.dvd_iff_le, Ideal.span_singleton_le_iff_mem]
  exact hmem

end GlobalTheory.LowDat
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankFunctionFieldQuotientSubfieldEqDegree
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSAmp

namespace GlobalTheory.HSAmp

theorem finrank_ratF_eq_gdeg : GlobalTheory.Published.ArCalc → ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (P : Pair p), IsAmpleLB P.L.B → ∀ (e : ℕ) (x : Fin (D + 1) → X.functionField), Gens P D e x → (Module.finrank (ratF x) X.functionField : ℝ) = (e : ℝ) ^ D * gdeg P.L D := by
  intro hA k _ X _ p D hX P hamp e x hg
  haveI := hX.isDomain
  haveI := hX.finite
  haveI := hX.charZero_base
  obtain ⟨hI, π, hπ, hgen, hr0, hr, hiso⟩ := GlobalTheory.T.exists_projectiveSpace_morphism_of_generating_sections k X p D hX P hamp e x hg
  obtain ⟨B, -, hB⟩ := GlobalTheory.T.exists_fubiniStudyWeights_bounded_difference k X p D hX P e x hg
  obtain ⟨u, hu, -⟩ := hB 1 le_rfl
  have h1 := (hiso u hu).gdeg_eq D
  obtain ⟨hPV, hdeg, hcard⟩ := GlobalTheory.T.projectiveSpace_order_arithVariety_fubiniStudyDegree k D
  have h2 := (GlobalTheory.T.geometricDegree_projectionFormula_selfInter_pow hA k (PSpace k D) (PSpace.str k D) D hPV).1 X p hX π hπ hgen hr0 (ProjSpace.hermitianTwistingSheaf k D)
  have h3 : gdeg ((up P.L u).pow e) D = (e : ℝ) ^ D * gdeg (up P.L u) D :=
    GlobalTheory.T.chernFormPowerIntegral_hermLineBundle_pow k X p D hX (up P.L u) e fun _ _ => 1
  have h4 := GlobalTheory.T.hermLineBundleGeometricDegree_raiseWeight hA k X p D hX P.L u
  rw [← hr]
  push_cast
  rw [← hcard, ← hdeg, ← h2, ← h1, h3, h4]

end GlobalTheory.HSAmp
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankLeMin
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.LowDat GlobalTheory.LowFilt
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.UChart.Fam

open Classical

theorem finrank_le_min : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
    (Xo : Moduli Dw l) (c : Coeff l) (R : Type) [CommRing R] [IsDomain R]
    [IsLocalRing R], GlobalTheory.Mum.Base R → ∀ C : GlobalTheory.UChart.Fam Xo c R,
    Module.finrank (𝓞 E) C.P.D.toPre.X ≤ min Dw.p Dw.q := by
  intro E _ _ _ H Dw l Xo c R _ _ _ hB C
  obtain ⟨hadm, hch⟩ := hB
  haveI : IsNoetherianRing R := hadm.1
  haveI : CharZero R := hch
  obtain ⟨tK, ⟨m₁⟩, ⟨m₂⟩⟩ := C.gen
  let K := AlgebraicClosure (FractionRing R)
  let g : FractionRing R →+* K := algebraMap (FractionRing R) K
  let f : R →+* K := g.comp (algebraMap R (FractionRing R))
  have hf : Function.Injective f :=
    (algebraMap (FractionRing R) K).injective.comp (IsFractionRing.injective R (FractionRing R))
  haveI : CharZero K := ⟨fun a b h => Nat.cast_injective (R := R) (hf (by simpa using h))⟩
  let x' : Sp K ⟶ Xo.X := spMap g ≫ C.y ≫ pullback.fst _ _
  obtain ⟨β₀, hβ₀⟩ := Spec.map_surjective (x' ≫ Xo.s)
  have hβ : x' ≫ Xo.s = spMap β₀.hom := hβ₀.symm
  have hdet := (Xo.univ.geom K x' β₀.hom hβ).1
  have hr : (β₀.hom (baseKA l).ρ) ^ 2 = -(H.d : K) := by
    rw [← map_pow, (baseKA l).ρ_sq, map_neg, map_natCast]
  have hjK : spMap g ≫ jK R = spMap f := by
    show Spec.map _ ≫ Spec.map _ = _
    rw [← Spec.map_comp]
    rfl
  have bound : ∀ (τ : 𝓞 E →+* K) (N : ℕ), LieMult Xo.univ.t.act x' τ N →
      Module.finrank (𝓞 E) C.P.D.toPre.X ≤ N := by
    intro τ N hN
    have h₅ := (GlobalTheory.lieMult_iff_of_isGrpPullback m₂.cart tK.act Xo.univ.t.act m₂.act (spMap g) τ N).2 hN
    have h₆ := (GlobalTheory.lieMult_iff_of_isGrpPullback m₁.cart tK.act C.t.act m₁.act (spMap g) τ N).1 h₅
    rw [hjK] at h₆
    obtain ⟨n, -, hn⟩ := GlobalTheory.CharRank.lieMult_unif_loc H R C.t C.P K f hf τ N h₆
    omega
  obtain ⟨τ₁, τ₂, h₁, h₂⟩ := GlobalTheory.CharRank.exists_chars H K _ hr
  exact le_min (bound τ₁ _ ((hdet τ₁).1 h₁)) (bound τ₂ _ ((hdet τ₂).2 h₂))

end GlobalTheory.UChart.Fam
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FirstOrderTranslationFormulaGerms
section
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LogKS Formalism.L2.Pj
open MonoidalCategory CartesianMonoidalCategory MonObj
attribute [local instance] Over.cartesianMonoidalCategory
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.TranslGerm

open GlobalTheory.Points (valR_eq valR_add valR_mul valR_res valR_comp)

theorem point_formula {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X : Scheme.{0}} {t : SAB H X}
    {U : X.affineOpens} {n : ℕ} {v : Fin n → (Sp (DualNumber Γ(X, U.1)) ⟶ t.G.left)}
    (hv : ∀ a, IsTanAtG t (chart U) (v a))
    {δ : Fin n → ∀ O : t.G.left.Opens, Γ(t.G.left, O) → Γ(t.G.left, O)}
    (hδv : ∀ a (O : t.G.left.Opens), O ≤ t.G.hom ⁻¹ᵁ U.1 → ∀ (f : Γ(t.G.left, O)) (S : Type) [CommRing S]
      (φ : Γ(X, U.1) →+* S) (g₀ : Sp S ⟶ t.G.left) (w : Sp (DualNumber S) ⟶ t.G.left),
      g₀ ≫ t.G.hom = spMap φ ≫ chart U → ⊤ ≤ g₀ ⁻¹ᵁ O → IsTranslate t φ g₀ (v a) w →
      valR g₀ O (δ a O f) = (valR w O f).snd)
    {r : Fin n → Γ(X, U.1)} {x : tEpsG (chart U) ⟶ t.G} (hx : IsCombAtG t (chart U) v r x.left)
    {S : Type} [CommRing S] {φ : Γ(X, U.1) →+* S} {P : tEpsG (spMap φ ≫ chart U) ⟶ t.G}
    (hP : P.left = spMap (dualMap φ) ≫ x.left) {O : t.G.left.Opens} (hO : O ≤ t.G.hom ⁻¹ᵁ U.1)
    (f : Γ(t.G.left, O)) {C : Type} [CommRing C] (z : Sp C ⟶ (tEpsG (spMap φ ≫ chart U) ⊗ t.G).left)
    (hz : ⊤ ≤ z ⁻¹ᵁ ((snd (tEpsG (spMap φ ≫ chart U)) t.G).left ⁻¹ᵁ O)) :
    ⊤ ≤ (z ≫ (lift (fst (tEpsG (spMap φ ≫ chart U)) t.G ≫ P) (snd (tEpsG (spMap φ ≫ chart U)) t.G) ≫
        μ[t.G]).left) ⁻¹ᵁ O ∧
    valR (z ≫ (lift (fst (tEpsG (spMap φ ≫ chart U)) t.G ≫ P) (snd (tEpsG (spMap φ ≫ chart U)) t.G) ≫
        μ[t.G]).left) O f =
      valR (z ≫ (snd (tEpsG (spMap φ ≫ chart U)) t.G).left) O f +
      valR (z ≫ (fst (tEpsG (spMap φ ≫ chart U)) t.G).left) ⊤
          ((Scheme.ΓSpecIso (CommRingCat.of (DualNumber S))).inv.hom DualNumber.eps) *
        valR (z ≫ (snd (tEpsG (spMap φ ≫ chart U)) t.G).left) O
          (∑ b, (t.G.hom.appLE U.1 O hO).hom (r b) * δ b O f) := by

  obtain ⟨g₀, hg₀⟩ : ∃ g₀, g₀ = z ≫ (snd (tEpsG (spMap φ ≫ chart U)) t.G).left := ⟨_, rfl⟩
  have hg₀O : ⊤ ≤ g₀ ⁻¹ᵁ O := by rw [hg₀]; exact hz
  obtain ⟨ψ₀, hψ₀⟩ : ∃ ψ₀ : DualNumber S →+* C, z ≫ (fst (tEpsG (spMap φ ≫ chart U)) t.G).left = spMap ψ₀ :=
    ⟨(Spec.preimage (z ≫ (fst (tEpsG (spMap φ ≫ chart U)) t.G).left)).hom, (Spec.map_preimage _).symm⟩
  let ψ : DualNumber Γ(X, U.1) →+* C := ψ₀.comp (dualMap φ)
  have hd : (dualMap φ).comp (algebraMap Γ(X, U.1) (DualNumber Γ(X, U.1))) = (algebraMap S (DualNumber S)).comp φ := by
    apply RingHom.ext; intro s; ext <;> simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl]
  have hbase : g₀ ≫ t.G.hom = spMap (ψ.comp (algebraMap Γ(X, U.1) (DualNumber Γ(X, U.1)))) ≫ chart U := by
    have e1 : (snd (tEpsG (spMap φ ≫ chart U)) t.G).left ≫ t.G.hom =
        (fst (tEpsG (spMap φ ≫ chart U)) t.G).left ≫ (tEpsG (spMap φ ≫ chart U)).hom :=
      (Over.w _).trans (Over.w _).symm
    rw [hg₀, Category.assoc, e1, ← Category.assoc, hψ₀]
    show spMap ψ₀ ≫ spMap (algebraMap S (DualNumber S)) ≫ spMap φ ≫ chart U = _
    rw [← Category.assoc, ← Category.assoc, GlobalTheory.KSLin.spMap_comp_spMap, GlobalTheory.KSLin.spMap_comp_spMap]
    congr 2
    simp only [ψ, RingHom.comp_assoc, hd]
  let a : Over.mk (g₀ ≫ t.G.hom) ⟶ tEpsG (chart U) := Over.homMk (spMap ψ) (by
    show spMap ψ ≫ spMap (algebraMap Γ(X, U.1) (DualNumber Γ(X, U.1))) ≫ chart U = g₀ ≫ t.G.hom
    rw [hbase, ← Category.assoc, GlobalTheory.KSLin.spMap_comp_spMap])
  choose w hw using fun b => (existsUnique_isTranslate t (ψ.comp (algebraMap Γ(X, U.1) (DualNumber Γ(X, U.1))))
    hbase (hv b)).exists
  obtain ⟨h1, h2⟩ := GlobalTheory.FirstOrderValue.valR_mul_comb E H X t U n v hv r x hx C ψ g₀ a w rfl hw O f hg₀O

  let zO : Over.mk (g₀ ≫ t.G.hom) ⟶ tEpsG (spMap φ ≫ chart U) ⊗ t.G := Over.homMk z (by
    show z ≫ (tEpsG (spMap φ ≫ chart U) ⊗ t.G).hom = g₀ ≫ t.G.hom
    rw [hg₀, ← Over.w (snd (tEpsG (spMap φ ≫ chart U)) t.G), Category.assoc])
  have hzs : zO ≫ snd (tEpsG (spMap φ ≫ chart U)) t.G = (Over.homMk g₀ rfl : Over.mk (g₀ ≫ t.G.hom) ⟶ t.G) :=
    Over.OverMorphism.ext hg₀.symm
  have hzf : zO ≫ fst (tEpsG (spMap φ ≫ chart U)) t.G ≫ P = a ≫ x := by
    apply Over.OverMorphism.ext
    show z ≫ (fst (tEpsG (spMap φ ≫ chart U)) t.G).left ≫ P.left = spMap ψ ≫ x.left
    rw [hP, ← Category.assoc, hψ₀, ← Category.assoc, GlobalTheory.KSLin.spMap_comp_spMap]
  have hτ : zO ≫ lift (fst (tEpsG (spMap φ ≫ chart U)) t.G ≫ P) (snd (tEpsG (spMap φ ≫ chart U)) t.G) ≫ μ[t.G] =
      (a ≫ x) * (Over.homMk g₀ rfl : Over.mk (g₀ ≫ t.G.hom) ⟶ t.G) := by
    rw [← Category.assoc, comp_lift, hzs, hzf]
    rfl
  have hτl : z ≫ (lift (fst (tEpsG (spMap φ ≫ chart U)) t.G ≫ P) (snd (tEpsG (spMap φ ≫ chart U)) t.G) ≫
      μ[t.G]).left = ((a ≫ x) * (Over.homMk g₀ rfl : Over.mk (g₀ ≫ t.G.hom) ⟶ t.G)).left :=
    congrArg Over.Hom.left hτ
  rw [hτl, ← hg₀]
  refine ⟨h1, ?_⟩
  rw [h2, hψ₀]
  congr 1
  have hε : ψ DualNumber.eps = ψ₀ DualNumber.eps := by simp [ψ, dualMap]
  have hsp : valR (spMap ψ₀) ⊤ ((Scheme.ΓSpecIso (CommRingCat.of (DualNumber S))).inv.hom DualNumber.eps) =
      ψ₀ DualNumber.eps := GlobalTheory.Points.valR_specMap (CommRingCat.ofHom ψ₀) _
  rw [hsp, ← hε, valR_eq _ _ hg₀O, map_sum]
  congr 1
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [map_mul, ← valR_eq _ _ hg₀O, ← valR_eq _ _ hg₀O, GlobalTheory.LogKSLin.valR_base U hO hbase hg₀O,
    hδv b O hO f C _ g₀ (w b) hbase hg₀O (hw b)]
  rfl

theorem transl_germ : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X : Scheme.{0}) (t : SAB H X) (U : X.affineOpens) (n : ℕ) (v : Fin n → (Sp (DualNumber Γ(X, U.1)) ⟶ t.G.left)), (∀ a, IsTanAtG t (chart U) (v a)) → ∀ (δ : Fin n → ∀ O : t.G.left.Opens, Γ(t.G.left, O) → Γ(t.G.left, O)), (∀ a, IsField (t.G.hom ⁻¹ᵁ U.1) (δ a)) → (∀ a (O : t.G.left.Opens) (h : O ≤ t.G.hom ⁻¹ᵁ U.1) (r : Γ(X, U.1)), δ a O ((t.G.hom.appLE U.1 O h).hom r) = 0) → (∀ a (O : t.G.left.Opens), O ≤ t.G.hom ⁻¹ᵁ U.1 → ∀ (f : Γ(t.G.left, O)) (S : Type) [CommRing S] (φ : Γ(X, U.1) →+* S) (g₀ : Sp S ⟶ t.G.left) (w : Sp (DualNumber S) ⟶ t.G.left), g₀ ≫ t.G.hom = spMap φ ≫ chart U → ⊤ ≤ g₀ ⁻¹ᵁ O → IsTranslate t φ g₀ (v a) w → valR g₀ O (δ a O f) = (valR w O f).snd) → ∀ (r : Fin n → Γ(X, U.1)) (x : tEpsG (chart U) ⟶ t.G), IsCombAtG t (chart U) v r x.left → ∀ (S : Type) [CommRing S] (φ : Γ(X, U.1) →+* S) (P : tEpsG (spMap φ ≫ chart U) ⟶ t.G), P.left = spMap (dualMap φ) ≫ x.left → ∀ (O : t.G.left.Opens) (hO : O ≤ t.G.hom ⁻¹ᵁ U.1) (f : Γ(t.G.left, O)) (y : (tEpsG (spMap φ ≫ chart U) ⊗ t.G).left), (snd (tEpsG (spMap φ ≫ chart U)) t.G).left.base y ∈ O → gs (lift (fst (tEpsG (spMap φ ≫ chart U)) t.G ≫ P) (snd (tEpsG (spMap φ ≫ chart U)) t.G) ≫ μ[t.G]).left y O f = gs (snd (tEpsG (spMap φ ≫ chart U)) t.G).left y O f + gs (fst (tEpsG (spMap φ ≫ chart U)) t.G).left y ⊤ ((Scheme.ΓSpecIso (CommRingCat.of (DualNumber S))).inv.hom DualNumber.eps) * gs (snd (tEpsG (spMap φ ≫ chart U)) t.G).left y O (∑ b, (t.G.hom.appLE U.1 O hO).hom (r b) * δ b O f) := by
  intro E _ _ _ H X t U n v hv δ _ _ hδv r x hx S _ φ P hP O hO f y hy
  have key := fun (C : Type) [CommRing C] z hz => point_formula hv hδv hx hP hO f (C := C) z hz

  have hVτ : (snd (tEpsG (spMap φ ≫ chart U)) t.G).left ⁻¹ᵁ O ≤
      (lift (fst (tEpsG (spMap φ ≫ chart U)) t.G ≫ P) (snd (tEpsG (spMap φ ≫ chart U)) t.G) ≫ μ[t.G]).left ⁻¹ᵁ O := by
    intro y' hy'
    obtain ⟨W, hW, hyW, hWV⟩ := exists_isAffineOpen_mem_and_subset hy'
    have hz : ⊤ ≤ hW.fromSpec ⁻¹ᵁ ((snd (tEpsG (spMap φ ≫ chart U)) t.G).left ⁻¹ᵁ O) :=
      GlobalTheory.Points.le_preimage_mono _ hWV hW.fromSpec_preimage_self.ge
    obtain ⟨p, rfl⟩ : y' ∈ Set.range hW.fromSpec := by rw [hW.range_fromSpec]; exact hyW
    have := (key Γ((tEpsG (spMap φ ≫ chart U) ⊗ t.G).left, W) hW.fromSpec hz).1 (Set.mem_univ p)
    exact this
  have hVπ : (snd (tEpsG (spMap φ ≫ chart U)) t.G).left ⁻¹ᵁ O ≤ (fst (tEpsG (spMap φ ≫ chart U)) t.G).left ⁻¹ᵁ ⊤ :=
    fun _ _ => trivial

  have hAB : ((tEpsG (spMap φ ≫ chart U) ⊗ t.G).left.presheaf.map (homOfLE hVτ).op).hom
      (((lift (fst (tEpsG (spMap φ ≫ chart U)) t.G ≫ P) (snd (tEpsG (spMap φ ≫ chart U)) t.G) ≫ μ[t.G]).left.app O).hom f) =
      ((snd (tEpsG (spMap φ ≫ chart U)) t.G).left.app O).hom f +
      ((tEpsG (spMap φ ≫ chart U) ⊗ t.G).left.presheaf.map (homOfLE hVπ).op).hom
        (((fst (tEpsG (spMap φ ≫ chart U)) t.G).left.app ⊤).hom
          ((Scheme.ΓSpecIso (CommRingCat.of (DualNumber S))).inv.hom DualNumber.eps)) *
      ((snd (tEpsG (spMap φ ≫ chart U)) t.G).left.app O).hom (∑ b, (t.G.hom.appLE U.1 O hO).hom (r b) * δ b O f) := by
    refine GlobalTheory.CechInv.ext_of_valR _ _ _ fun C _ z hz => ?_
    rw [valR_res _ hVτ hz, ← valR_comp, (key C z hz).2, valR_add _ _ hz, valR_mul _ _ hz, valR_res _ hVπ hz,
      ← valR_comp, ← valR_comp, ← valR_comp]
  have hτy := hVτ hy
  rw [gs_eq _ y O hτy, gs_eq _ y O hy, gs_eq _ y ⊤ trivial, gs_eq _ y O hy,
    ← TopCat.Presheaf.germ_res_apply _ (homOfLE hVτ) y hy, hAB, map_add, map_mul,
    TopCat.Presheaf.germ_res_apply _ (homOfLE hVπ) y hy]

end GlobalTheory.TranslGerm
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatConstantAbsLeNineExplicitStatement
section
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flat_constant_abs_le_nine_explicit : Hypotheses2 → ∃ C : ℝ, 0 ≤ C ∧ ∀ (D : D7) (T : CoreJ D), LawsJ T → ∀ j : ℕ, 1 ≤ (T.Q.Dw j).p → 1 ≤ (T.Q.Dw j).q → 2 < Module.finrank ℚ D.host.E / 2 → InR D j → ∀ (Y : Deep T.toCore j) (e : ℕ) (o : ℝ), Y.Good e o → ∀ Lb : ℝ, 1 ≤ Lb → Real.log Y.d.l₂.M ≤ 30 * Lb → fieldSz D.host.E ≤ 3 * Lb → Real.log (D.R.f * D.R.r) ≤ Lb → o ≤ 391 * (D.R.f * D.R.r * Lb) ^ 2 → ∀ c₁ : ℝ, GlobalTheory.FlatLine.FlatExistsAt Y.U (xiR D) c₁ → |c₁| ≤ 9 * D.R.r * Lb → ∀ la : AllWt.Weight (T.Q.Dw j), (∀ τ, Antitone (la τ)) → (∀ τ, ((8 * D.R.f * D.R.r + 10 : ℕ) : ℤ) ≤ gap (la τ) ((T.Q.Dw j).p - 1)) → Real.log (∑ τ, ∑ k, |(la τ k : ℝ)|) ≤ 10 * Lb → ∀ Z, ∃ (n : ℕ) (w : Fin n → cuspOn Y.U Z (wtOf (T.Q.Dw j) la 0)) (abelian₂ : ℝ), CompHt.IsShortGen (normOn Y.U (xiR D) (fun _ => D.sp.W j) Y.dict Z (wtOf (T.Q.Dw j) la 0)) (latOn Y.U Z (wtOf (T.Q.Dw j) la 0)) w abelian₂ ∧ Real.log abelian₂ ≤ C * (((D.R.f : ℝ) * D.R.r * Lb) ^ 3 * (∑ τ, ∑ k, |(la τ k : ℝ)|) + ((D.R.f : ℝ) * D.R.r * Lb) ^ 5) ∧ Real.log n ≤ C * ((D.R.f : ℝ) * D.R.r * Lb) ^ 3 := by
  first | exact @GlobalTheory.ShortGenComp.short_gen_comp | exact GlobalTheory.ShortGenComp.short_gen_comp | (intros; apply GlobalTheory.ShortGenComp.short_gen_comp <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FourierTermIdentityDescendsGenericFibre
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.TermDescend

theorem main : ∀ (R : Type) [CommRing R] [IsDomain R] (Q : DegPre R) (O : Type) [CommRing O] [StarRing O] [Module O Q.X] (oa : Q.OAct O) (Y : Ray oa) (k : ℕ) (α : Q.X) (σ₀ σ₁ σ₂ : Q.SecB k α) (τ₀ τ₁ τ₂ : SecM Y.q.left Q.P.L k) (a b : R), IsTerm Y k α σ₀ τ₀ → IsTerm Y k α σ₁ τ₁ → IsTerm Y k α σ₂ τ₂ → (∀ (Z : Scheme.{0}) (r : Z ⟶ Y.H.left) (z : Z) (J : (Z ⟶ Q.P.A.left) → Q.P.L.ι), Good Q.P.L z J → sval τ₀ r z J = gs (r ≫ Y.H.hom) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom a) * sval τ₁ r z J + gs (r ≫ Y.H.hom) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom b) * sval τ₂ r z J) → ∀ (z : (DegPre.BF Q (FractionRing R)).left) (J : ((DegPre.BF Q (FractionRing R)).left ⟶ Q.P.A.left) → Q.P.L.ι), Good Q.P.L z J → sval σ₀ (DegPre.prB Q (FractionRing R)).left z J = gs ((DegPre.prB Q (FractionRing R)).left ≫ Q.P.A.hom) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom a) * sval σ₁ (DegPre.prB Q (FractionRing R)).left z J + gs ((DegPre.prB Q (FractionRing R)).left ≫ Q.P.A.hom) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom b) * sval σ₂ (DegPre.prB Q (FractionRing R)).left z J := by
  intro R _ _ Q O _ _ _ oa Y k α σ₀ σ₁ σ₂ τ₀ τ₁ τ₂ a b h₀ h₁ h₂ H z J hJ
  obtain ⟨Z, p, w, y, hw, hp, hinj, hy⟩ := GlobalTheory.RayLift.exists_flat_lift R Q O oa Y z
  subst hw
  obtain ⟨J', hJ', hJJ⟩ := exists_good Q.P.L Q.P.isLB w (K := (DegPre.BF Q (FractionRing R)).left ⟶ Q.P.A.left)
    (fun ψ => p ≫ ψ) J (fun ψ ψ' e => by rw [(cancel_epi p).1 e]) (fun ψ => by
      rw [Scheme.Hom.comp_apply]; exact hJ ψ)
  have hfun : (fun ψ => J' (p ≫ ψ)) = J := funext hJJ
  let T : Over (Sp R) := Over.mk (y ≫ Y.H.hom)
  let x : T ⟶ Y.H := Over.homMk y rfl
  let v : (Z.presheaf.stalk w)ˣ := val ((Y.Φ T x).s α) (𝟙 _) w J'
  have e₀ : sval τ₀ y w J' = sval σ₀ (y ≫ Y.q.left) w J' * v.val := h₀ T x w J' hJ'
  have e₁ : sval τ₁ y w J' = sval σ₁ (y ≫ Y.q.left) w J' * v.val := h₁ T x w J' hJ'
  have e₂ : sval τ₂ y w J' = sval σ₂ (y ≫ Y.q.left) w J' * v.val := h₂ T x w J' hJ'
  have E := H Z y w J' hJ'
  have hH : y ≫ Y.H.hom = p ≫ ((DegPre.prB Q (FractionRing R)).left ≫ Q.P.A.hom) := by
    rw [← Category.assoc, ← hy, Category.assoc, Over.w Y.q]
  rw [e₀, e₁, e₂, ← _root_.mul_assoc, ← _root_.mul_assoc, ← add_mul] at E
  have E' := (Units.mul_left_inj _).1 E
  rw [hH, hy, GlobalTheory.HeatDefect.sval_comp_stalk _ _ _ _ hJ', GlobalTheory.HeatDefect.sval_comp_stalk _ _ _ _ hJ',
    GlobalTheory.HeatDefect.sval_comp_stalk _ _ _ _ hJ', GlobalTheory.HeatDefect.gs_comp_stalk p _ w ⊤ trivial,
    GlobalTheory.HeatDefect.gs_comp_stalk p _ w ⊤ trivial, hfun, ← map_mul, ← map_mul, ← map_add] at E'
  exact hinj E'

end GlobalTheory.TermDescend
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdempotentImageRelationOfPullbackStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor GlobalTheory.EndLoc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.idempotent_image_relation_of_pullback : ∀ (h h' M : ℕ) (B : Type) [CommRing B] (ζ : B) (O : Type) [Ring O] (e : O) (jl : (Fin h ⊕ Fin h → ℤ) →+ (Fin h' ⊕ Fin h' → ℤ)) (n : ℕ) (o : Fin n → O) (κ : Fin n → (Fin h' ⊕ Fin h' → ℤ) →+ (Fin h ⊕ Fin h → ℤ)) (S₁ S₂ : Scheme.{0}) (s₁ : S₁ ⟶ Sp B) (s₂ : S₂ ⟶ Sp B) (y : S₂ ⟶ S₁) (c₁ : SiegPre h M ζ s₁) (w₁ : SiegPre h' M ζ s₁) (act₁ : O → (w₁.A ⟶ w₁.A)) (c₂ : SiegPre h M ζ s₂) (w₂ : SiegPre h' M ζ s₂) (act₂ : O → (w₂.A ⟶ w₂.A)), ActPB w₂ act₂ w₁ act₁ y → SiegPB c₂ c₁ y → ZRel e jl o κ c₁ w₁ act₁ → ZRel e jl o κ c₂ w₂ act₂ := by
  first | (exact @GlobalTheory.UPel.HT.zRel_of_pullback) | (exact GlobalTheory.UPel.HT.zRel_of_pullback) | (intros; apply GlobalTheory.UPel.HT.zRel_of_pullback  <;> assumption)
end

