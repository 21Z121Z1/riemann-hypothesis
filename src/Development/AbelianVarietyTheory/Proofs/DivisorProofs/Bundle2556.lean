import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0075
import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle0001
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.GoodClass
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.ExistsArBaseAway
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0006
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0015
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0525
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0596
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0002
import Development.AbelianVarietyTheory.Definitions.Divisors.MulSmulIdemMem
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0022
import Development.AbelianVarietyTheory.Definitions.Divisors.IsHomogeneousCompIdeal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2305
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2375
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2220
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2314
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2190
import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0175
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0121
import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.IsOpenOfMemIrreducibleComponentsOfFinite
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GeometricallyIntegralIffGeometricallyConnectedOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2446
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0032
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0029
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0027
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2351

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TsumNatCastEq
section
set_option autoImplicit false

noncomputable section

open NumberField
open scoped nonZeroDivisors
open GlobalTheory.LatVal GlobalTheory.LatJet

namespace GlobalTheory.PairFourier

open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization

theorem tsum_natCast_eq {ι : Type} (n : ι → ℕ) (h : Summable (fun i ↦ (n i : ℂ))) :
    ∃ m : ℕ, ∑' i, (n i : ℂ) = m := by
  have hfin : (Function.support n).Finite := by
    have ht := h.tendsto_cofinite_zero
    have hev : ∀ᶠ i in Filter.cofinite, ‖(n i : ℂ)‖ < 1 := by
      have := ht.norm
      simp only [norm_zero] at this
      exact this.eventually (gt_mem_nhds (by norm_num))
    refine (Filter.eventually_cofinite.1 hev).subset ?_
    intro i hi
    simp only [Function.mem_support] at hi
    simp only [Set.mem_setOf_eq, not_lt]
    have : (1 : ℝ) ≤ n i := by exact_mod_cast Nat.one_le_iff_ne_zero.2 hi
    simpa [Complex.norm_natCast] using this
  refine ⟨∑ i ∈ hfin.toFinset, n i, ?_⟩
  rw [tsum_eq_sum (s := hfin.toFinset)]
  · push_cast; rfl
  · intro i hi
    simp only [Set.Finite.mem_toFinset, Function.mem_support, not_not] at hi
    simp [hi]

variable {F : Type} [Field F] [NumberField F]

theorem norm_div_eq_nat (𝔞 : Frac F) {ν : F} (hν : ν ∈ (𝔞 : FractionalIdeal (𝓞 F)⁰ F)) :
    ∃ m : ℕ, |((Algebra.norm ℚ ν : ℚ) : ℝ)| / nrm 𝔞 = m := by
  set J : FractionalIdeal (𝓞 F)⁰ F :=
    FractionalIdeal.spanSingleton (𝓞 F)⁰ ν * ((𝔞⁻¹ : Frac F) : FractionalIdeal (𝓞 F)⁰ F) with hJdef
  have hle : J ≤ 1 := by
    have h1 : FractionalIdeal.spanSingleton (𝓞 F)⁰ ν ≤ (𝔞 : FractionalIdeal (𝓞 F)⁰ F) :=
      FractionalIdeal.spanSingleton_le_iff_mem.2 hν
    calc J ≤ (𝔞 : FractionalIdeal (𝓞 F)⁰ F) * ((𝔞⁻¹ : Frac F) : FractionalIdeal (𝓞 F)⁰ F) :=
          mul_le_mul_left h1 _
      _ = 1 := by rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  obtain ⟨I, hI⟩ := FractionalIdeal.le_one_iff_exists_coeIdeal.1 hle
  have hJa : J * (𝔞 : FractionalIdeal (𝓞 F)⁰ F) = FractionalIdeal.spanSingleton (𝓞 F)⁰ ν := by
    rw [hJdef, mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, mul_one]
  have hn := congrArg FractionalIdeal.absNorm hJa
  rw [map_mul, FractionalIdeal.absNorm_span_singleton, ← hI, FractionalIdeal.coeIdeal_absNorm] at hn
  have h0 : (FractionalIdeal.absNorm (𝔞 : FractionalIdeal (𝓞 F)⁰ F) : ℚ) ≠ 0 := by
    rw [Ne, FractionalIdeal.absNorm_eq_zero_iff]
    exact Units.ne_zero 𝔞
  refine ⟨Ideal.absNorm I, ?_⟩
  unfold nrm
  rw [div_eq_iff (by exact_mod_cast h0)]
  have := congrArg (fun q : ℚ ↦ (q : ℝ)) hn
  simp only [Rat.cast_mul, Rat.cast_natCast, Rat.cast_abs] at this
  rw [← this]

variable [IsTotallyReal F]

def pairPt (𝔞 𝔟 : Frac F) (c : Quotient (qRel 𝔞 𝔟)) : GlobalTheory.RealMult.FracId.elt (𝔞 * 𝔟) :=
  ⟨c.out.1.1 * c.out.1.2, by
    show _ ∈ ((𝔞 * 𝔟 : Frac F) : FractionalIdeal (𝓞 F)⁰ F)
    rw [Units.val_mul]
    exact FractionalIdeal.mul_mem_mul c.out.2.1 c.out.2.2.1⟩

def pairCoef (𝔞 𝔟 : Frac F) (k : ℕ) (c : Quotient (qRel 𝔞 𝔟)) : ℕ :=
  (norm_div_eq_nat 𝔞 c.out.2.1).choose ^ (k - 1)

theorem qClass_eq (𝔞 𝔟 : Frac F) (k : ℕ) (z : Emb F → ℂ) (c : Quotient (qRel 𝔞 𝔟)) :
    qClass 𝔞 𝔟 k z c = (pairCoef 𝔞 𝔟 k c : ℂ) * GlobalTheory.RealMult.qPower ((pairPt 𝔞 𝔟 c : F)) z := by
  unfold qClass qTerm pairCoef pairPt
  have hs := (norm_div_eq_nat 𝔞 c.out.2.1).choose_spec
  generalize (norm_div_eq_nat 𝔞 c.out.2.1).choose = m at hs ⊢
  rw [hs]
  push_cast
  rfl

theorem pairPt_ne_zero (𝔞 𝔟 : Frac F) (c : Quotient (qRel 𝔞 𝔟)) : pairPt 𝔞 𝔟 c ≠ 0 := by
  intro h
  have h' : c.out.1.1 * c.out.1.2 = 0 := congrArg Subtype.val h
  obtain ⟨φ⟩ : Nonempty (F →+* ℂ) := inferInstance
  have hr : NumberField.ComplexEmbedding.IsReal φ := IsTotallyReal.complexEmbedding_isReal φ
  have := c.out.2.2.2 hr.embedding
  rw [h', map_zero] at this
  exact lt_irrefl _ this

theorem eisFourier : EisFourier := by
  classical
  intro F _ _ _ 𝔞 𝔟 k _ G hG
  obtain ⟨Z, hZ, hE⟩ := hG
  set C : ℂ := (2 : ℂ)⁻¹ ^ Module.finrank ℚ F * Z (1 - (k : ℂ)) with hC
  set a' : GlobalTheory.RealMult.FracId.elt (𝔞 * 𝔟) → ℂ :=
    fun ξ ↦ ∑' c : pairPt 𝔞 𝔟 ⁻¹' {ξ}, (pairCoef 𝔞 𝔟 k c : ℂ) with ha'
  have hfib : ∀ (z : Emb F → ℂ) (ξ : GlobalTheory.RealMult.FracId.elt (𝔞 * 𝔟)) (c : pairPt 𝔞 𝔟 ⁻¹' {ξ}),
      qClass 𝔞 𝔟 k z c = (pairCoef 𝔞 𝔟 k c : ℂ) * GlobalTheory.RealMult.qPower (ξ : F) z := by
    rintro z ξ ⟨c, hc⟩
    rw [Set.mem_preimage, Set.mem_singleton_iff] at hc
    rw [qClass_eq, hc]
  refine ⟨Z, fun ξ ↦ a' ξ + if ξ = 0 then C else 0, hZ, ?_, ?_, ?_⟩
  · intro z hz
    obtain ⟨hs, heq⟩ := hE z hz
    have h1 := hs.hasSum.tsum_fiberwise (pairPt 𝔞 𝔟)
    have h2 : (fun ξ ↦ ∑' c : pairPt 𝔞 𝔟 ⁻¹' {ξ}, qClass 𝔞 𝔟 k z c) =
        fun ξ ↦ a' ξ * GlobalTheory.RealMult.qPower (ξ : F) z := by
      funext ξ
      rw [ha', ← tsum_mul_right]
      exact tsum_congr (hfib z ξ)
    rw [h2] at h1
    have h3 : HasSum (fun ξ : GlobalTheory.RealMult.FracId.elt (𝔞 * 𝔟) ↦
        (if ξ = 0 then C else 0) * GlobalTheory.RealMult.qPower (ξ : F) z) C := by
      convert hasSum_ite_eq (0 : GlobalTheory.RealMult.FracId.elt (𝔞 * 𝔟)) C using 1
      funext ξ
      split_ifs with h
      · subst h; simp [GlobalTheory.RealMult.qPower]
      · simp
    have hv : (cK F k : ℂ) * G z / (omegaFactor 𝔞 : ℂ) ^ k =
        (∑' c, qClass 𝔞 𝔟 k z c) + C := by rw [heq]; ring
    show HasSum (fun ξ : GlobalTheory.RealMult.FracId.elt (𝔞 * 𝔟) ↦
      (a' ξ + if ξ = 0 then C else 0) * GlobalTheory.RealMult.qPower (ξ : F) z) ((cK F k : ℂ) * G z / (omegaFactor 𝔞 : ℂ) ^ k)
    rw [hv]
    simp only [add_mul]
    exact h1.add h3
  · show a' 0 + (if (0 : GlobalTheory.RealMult.FracId.elt (𝔞 * 𝔟)) = 0 then C else 0) = C
    rw [if_pos rfl]
    have : IsEmpty (pairPt 𝔞 𝔟 ⁻¹' {0}) :=
      ⟨fun ⟨c, hc⟩ ↦ pairPt_ne_zero 𝔞 𝔟 c (Set.mem_singleton_iff.1 (Set.mem_preimage.1 hc))⟩
    rw [ha']
    simp only [tsum_empty, zero_add]
  · intro ξ hξ
    set z₀ : Emb F → ℂ := fun _ ↦ Complex.I
    have hz₀ : z₀ ∈ upperHalf F := fun _ ↦ by simp [z₀]
    have hq : GlobalTheory.RealMult.qPower (ξ : F) z₀ ≠ 0 := Complex.exp_ne_zero _
    have hsum : Summable (fun c : pairPt 𝔞 𝔟 ⁻¹' {ξ} ↦ (pairCoef 𝔞 𝔟 k c : ℂ)) := by
      have := ((hE z₀ hz₀).1.subtype (pairPt 𝔞 𝔟 ⁻¹' {ξ})).mul_right (GlobalTheory.RealMult.qPower (ξ : F) z₀)⁻¹
      refine this.congr fun c ↦ ?_
      simp only [Function.comp_apply]
      rw [hfib z₀ ξ c, mul_assoc, mul_inv_cancel₀ hq, mul_one]
    obtain ⟨m, hm⟩ := tsum_natCast_eq _ hsum
    refine ⟨m, ?_⟩
    show a' ξ + (if ξ = 0 then C else 0) = _
    rw [if_neg hξ, add_zero, ha']
    simp only [hm]
    simp

end GlobalTheory.PairFourier
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistFibreIso
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Poinc.Sep.Twist

theorem spMap_comp_spMap {R R' R'' : Type} [CommRing R] [CommRing R'] [CommRing R''] (b : R →+* R') (a : R' →+* R'') :
    spMap a ≫ spMap b = spMap (a.comp b) := by
  rw [← Spec.map_comp]; rfl

theorem twist_fibre_iso : ∀ (V₁ : Type) [CommRing V₁] (X : Over (Sp V₁)) [GrpObj X] (L : LB X.left), L.IsLB →
  ∀ (K : Type) [Field K]
  (ev : V₁ →+* K) (σ : K ≃+* K) (K₀ : Type) [Field K₀] (e : K₀ →+* K), σ.toRingHom.comp e = e →
  ∀ (Z : Over (Sp K)) [GrpObj Z] (LZ : LB Z.left), LZ.IsLB → ∀ (ψ : ((Over.pullback (spMap ev)).obj X).left ⟶ Z.left),
  IsGrpPullback ((Over.pullback (spMap ev)).obj X) Z (𝟙 _) ψ →
  LBIso (L.pull (pullback.fst X.hom (spMap ev))) (LZ.pull ψ) →
  ∀ (Y : Over (Sp K₀)) [GrpObj Y] (L₀ : LB Y.left), L₀.IsLB → ∀ (φ : Z.left ⟶ Y.left), IsGrpPullback Z Y (spMap e) φ →
  LBIso LZ (L₀.pull φ) →
  ∃ f : ((Over.pullback (spMap ev)).obj X).left ⟶ ((Over.pullback (spMap (σ.toRingHom.comp ev))).obj X).left,
    IsGrpPullback ((Over.pullback (spMap ev)).obj X) ((Over.pullback (spMap (σ.toRingHom.comp ev))).obj X) (𝟙 _) f ∧
    LBIso (L.pull (pullback.fst X.hom (spMap ev))) (L.pull (f ≫ pullback.fst X.hom (spMap (σ.toRingHom.comp ev)))) ∧
    ∀ (q : Sp K ⟶ ((Over.pullback (spMap ev)).obj X).left) (y₀ : Sp K₀ ⟶ Y.left), q ≫ ψ ≫ φ = spMap e ≫ y₀ →
      q ≫ pullback.snd X.hom (spMap ev) = 𝟙 _ →
      q ≫ f ≫ pullback.fst X.hom (spMap (σ.toRingHom.comp ev)) = spMap σ.toRingHom ≫ q ≫ pullback.fst X.hom (spMap ev) := by
  intro V₁ _ X _ L hL K _ ev σ K₀ _ e hσe Z _ LZ hLZ ψ hψ H1 Y _ L₀ hL₀ φ hφ H2
  have hs : spMap σ.toRingHom ≫ spMap e = spMap e := by rw [spMap_comp_spMap, hσe]
  have hev : spMap σ.toRingHom ≫ spMap ev = spMap (σ.toRingHom.comp ev) := spMap_comp_spMap _ _
  have hX := isGrpPullback_pullback X (spMap ev)
  have hXσ := isGrpPullback_pullback X (spMap (σ.toRingHom.comp ev))
  have hχ := hψ.comp hφ
  obtain ⟨ρ, hρ1, hρ2⟩ : ∃ ρ : pullback X.hom (spMap (σ.toRingHom.comp ev)) ⟶ pullback X.hom (spMap ev),
      ρ ≫ pullback.fst X.hom (spMap ev) = pullback.fst X.hom (spMap (σ.toRingHom.comp ev)) ∧
      ρ ≫ pullback.snd X.hom (spMap ev) = pullback.snd X.hom (spMap (σ.toRingHom.comp ev)) ≫ spMap σ.toRingHom :=
    ⟨pullback.lift (pullback.fst _ _) (pullback.snd _ _ ≫ spMap σ.toRingHom)
      (by rw [pullback.condition, Category.assoc, hev]), pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩
  have hρ : IsGrpPullback ((Over.pullback (spMap (σ.toRingHom.comp ev))).obj X) ((Over.pullback (spMap ev)).obj X)
      (spMap σ.toRingHom) ρ := hX.cancel (hXσ.congr hev.symm hρ1.symm) hρ2
  have hσχ := hρ.comp hχ
  obtain ⟨f, hf1, hf2⟩ : ∃ f : pullback X.hom (spMap ev) ⟶ pullback X.hom (spMap (σ.toRingHom.comp ev)),
      f ≫ ρ ≫ ψ ≫ φ = ψ ≫ φ ∧
      f ≫ pullback.snd X.hom (spMap (σ.toRingHom.comp ev)) = pullback.snd X.hom (spMap ev) :=
    ⟨hσχ.1.lift (ψ ≫ φ) (pullback.snd X.hom (spMap ev))
      (by rw [hχ.1.w]; simp only [Category.id_comp, hs]; try rfl), hσχ.1.lift_fst _ _ _, hσχ.1.lift_snd _ _ _⟩
  have hfg : IsGrpPullback ((Over.pullback (spMap ev)).obj X) ((Over.pullback (spMap (σ.toRingHom.comp ev))).obj X)
      (𝟙 _) f :=
    hσχ.cancel (hχ.congr (by simp only [Category.id_comp, hs]) hf1.symm)
      (by rw [Category.comp_id]; exact hf2)
  have hτ1 : f ≫ pullback.fst X.hom (spMap (σ.toRingHom.comp ev)) = (f ≫ ρ) ≫ pullback.fst X.hom (spMap ev) := by
    rw [Category.assoc, hρ1]
  have hτχ : (f ≫ ρ) ≫ ψ ≫ φ = ψ ≫ φ := by rw [Category.assoc, hf1]
  have hτ2 : (f ≫ ρ) ≫ pullback.snd X.hom (spMap ev) = pullback.snd X.hom (spMap ev) ≫ spMap σ.toRingHom := by
    rw [Category.assoc, hρ2, ← Category.assoc, hf2]
  refine ⟨f, hfg, ?_, ?_⟩
  · have K1 : LBIso (LZ.pull ψ) (L₀.pull (ψ ≫ φ)) :=
      LBIso.chartPull (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull LZ ψ ψ rfl) (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullSame L₀ _ (fun _ => φ) _ ψ fun _ => rfl) H2
    have hA := pull_isLB hL (pullback.fst X.hom (spMap ev))
    have hC := pull_isLB hL₀ (ψ ≫ φ)
    have AC := LBIso.trans hA (pull_isLB hLZ ψ) hC H1 K1
    have D : LBIso (L.pull (f ≫ pullback.fst X.hom (spMap (σ.toRingHom.comp ev)))) (L₀.pull (ψ ≫ φ)) :=
      LBIso.chartPull (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullSame L _ (fun _ => pullback.fst X.hom (spMap ev)) _ (f ≫ ρ) fun _ => hτ1)
        (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullSame L₀ _ (fun _ => ψ ≫ φ) _ (f ≫ ρ) fun _ => hτχ.symm) AC
    exact LBIso.trans hA hC (pull_isLB hL _) AC D.symm
  · intro q y₀ hq hq'
    have hqτ : q ≫ f ≫ ρ = spMap σ.toRingHom ≫ q := by
      apply hχ.1.hom_ext
      · rw [Category.assoc, hτχ, hq, Category.assoc, hq, ← Category.assoc, hs]
      · show (q ≫ f ≫ ρ) ≫ pullback.snd X.hom (spMap ev) = (spMap σ.toRingHom ≫ q) ≫ pullback.snd X.hom (spMap ev)
        rw [Category.assoc, hτ2, ← Category.assoc, hq', Category.assoc, hq', Category.id_comp, Category.comp_id]
    rw [hτ1, ← Category.assoc, hqτ, Category.assoc]

end GlobalTheory.Poinc.Sep.Twist
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedHilbertLatticeContainsAndCoordinateSize
section
open NumberField UpperHalfPlane GlobalTheory.HilbFam GlobalTheory.QFam
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization (Emb Frac latM qPow upperHalf cK omegaFactor IsPartialZeta HasExpansion)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (iterD partialD)
open scoped Classical MatrixGroups nonZeroDivisors
open GlobalTheory.LatVal (Sz)
open GlobalTheory.LatJet (EisExp IsEis FR)

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HilbFam.TwistSize

theorem intVec_mem_std {F : Type} [Field F] [NumberField F] (z : Fin 2 → ℤ) :
    (fun j ↦ ((z j : ℤ) : F)) ∈ stdLat F := by
  rw [stdLat, Submodule.mem_pi]
  intro j _
  exact Submodule.mem_one.2 ⟨(z j : 𝓞 F), by simp⟩

theorem main : ∀ (l : ℕ) [Fact l.Prime] (lam : algebraicClosure ℚ ℂ →+* ℂ_[l]), ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (N n : ℕ) (L : Lat F) (α : GL (Fin 2) (ZMod N)) (ρ₀ : ℝ), L ≤ stdLat F → (∀ x ∈ stdLat F, (n : 𝓞 F) • x ∈ L) → (∀ v ∈ L, ∀ (j : Fin 2) (i : Emb F), Sz l lam ρ₀ ((i (v j) : ℝ) : ℂ)) → Sz l lam ρ₀ (N : ℂ) → ![0, (n : F)] ∈ twist N L (α : Matrix (Fin 2) (Fin 2) (ZMod N)) ∧ ∀ v ∈ twist N L (α : Matrix (Fin 2) (Fin 2) (ZMod N)), ∀ i : Emb F, Sz l lam ρ₀ ((i (v 0) : ℝ) : ℂ) := by
  intro l _ lam F _ _ _ N n L α ρ₀ hLs hnL hL hN
  have hR := GlobalTheory.T.algebraicValuationAtLeastAtEmbedding_ring_ops l lam
  have hZ := GlobalTheory.T.algebraicValuationAtLeast_basic_properties l lam
  let A : Matrix (Fin 2) (Fin 2) ℤ := (α : Matrix (Fin 2) (Fin 2) (ZMod N)).map (ZMod.cast : ZMod N → ℤ)
  have hAα : A.map (Int.cast : ℤ → ZMod N) = (α : Matrix (Fin 2) (Fin 2) (ZMod N)) := by
    ext i j; simp [A, ZMod.intCast_cast, ZMod.cast_id']
  have hI := (GlobalTheory.T.mem_hilbertLatticeTwist_iff_lift F N L A · hLs)
  rw [← hAα]
  refine ⟨?_, ?_⟩
  · let B : Matrix (Fin 2) (Fin 2) ℤ :=
      ((α⁻¹ : GL (Fin 2) (ZMod N)) : Matrix (Fin 2) (Fin 2) (ZMod N)).map (ZMod.cast : ZMod N → ℤ)
    have h1 : ((α⁻¹ : GL (Fin 2) (ZMod N)) : Matrix (Fin 2) (Fin 2) (ZMod N)) * (α : Matrix (Fin 2) (Fin 2) (ZMod N)) = 1 := by
      rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
    have hmod : ∀ i j, (((B * A) i j - (1 : Matrix (Fin 2) (Fin 2) ℤ) i j : ℤ) : ZMod N) = 0 := by
      intro i j
      have h2 := congrFun (congrFun h1 i) j
      rw [Matrix.mul_apply] at h2
      rw [Int.cast_sub, Matrix.mul_apply, Int.cast_sum, Matrix.one_apply]
      rw [Matrix.one_apply] at h2
      simp only [Int.cast_mul, B, A, Matrix.map_apply, ZMod.intCast_cast, ZMod.cast_id', id_eq]
      rw [h2]; split_ifs <;> simp
    have hdv : ∀ i j, (N : ℤ) ∣ (B * A) i j - (1 : Matrix (Fin 2) (Fin 2) ℤ) i j :=
      fun i j ↦ (ZMod.intCast_zmod_eq_zero_iff_dvd _ N).1 (hmod i j)
    choose D hD using hdv
    have hy : (fun j ↦ (n : F) * (B 1 j : F)) ∈ L := by
      have := hnL _ (intVec_mem_std (fun j ↦ B 1 j))
      convert this using 1
      ext j
      simp [Nat.cast_smul_eq_nsmul]
    have hw : (fun j ↦ -((n : F) * (D 1 j : F))) ∈ stdLat F := by
      have := Submodule.smul_mem (stdLat F) (-(n : 𝓞 F)) (intVec_mem_std (fun j ↦ D 1 j))
      convert this using 1
      ext j
      simp [Nat.cast_smul_eq_nsmul]
    refine (hI _).2 ⟨_, hy, _, hw, ?_⟩
    have hBA : ∀ j, (B 1 0 : F) * (A 0 j : F) + (B 1 1 : F) * (A 1 j : F) = (if (1 : Fin 2) = j then 1 else 0) + (N : F) * (D 1 j : F) := by
      intro j
      have := congrArg (Int.cast : ℤ → F) (hD 1 j)
      rw [Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply] at this
      split_ifs at this ⊢ <;> push_cast at this ⊢ <;> linear_combination this
    ext j
    fin_cases j
    · have := hBA 0
      simp [Matrix.vecMul, dotProduct, Fin.sum_univ_two] at this ⊢
      linear_combination -(n : F) * this
    · have := hBA 1
      simp [Matrix.vecMul, dotProduct, Fin.sum_univ_two] at this ⊢
      linear_combination -(n : F) * this
  · intro v hv i
    obtain ⟨y, hy, w, hw, rfl⟩ := (hI v).1 hv
    have hw0 : w 0 ∈ (1 : Submodule (𝓞 F) F) := by
      rw [stdLat, Submodule.mem_pi] at hw; exact hw 0 (Set.mem_univ _)
    obtain ⟨r, hr⟩ := Submodule.mem_one.1 hw0
    have hint : Sz l lam 0 ((i (w 0) : ℝ) : ℂ) := by
      refine hZ.1 1 _ (Nat.Prime.not_dvd_one (Fact.out)) ?_
      rw [Nat.cast_one, one_mul, ← hr]
      exact map_isIntegral_int ((Complex.ofRealHom.comp i).comp (algebraMap (𝓞 F) F)) (RingOfIntegers.isIntegral r)
    have heq : ((i ((Matrix.vecMul y (A.map (Int.cast : ℤ → F)) + (N : F) • w) 0) : ℝ) : ℂ) =
        ((i (y 0) : ℝ) : ℂ) * ((A 0 0 : ℤ) : ℂ) + ((i (y 1) : ℝ) : ℂ) * ((A 1 0 : ℤ) : ℂ) + (N : ℂ) * ((i (w 0) : ℝ) : ℂ) := by
      simp [Matrix.vecMul, dotProduct, Fin.sum_univ_two]
    rw [heq]
    have p1 := hR.2.2.1 ρ₀ 0 _ _ (hL y hy 0 i) (hR.2.2.2.2.1 (A 0 0))
    have p2 := hR.2.2.1 ρ₀ 0 _ _ (hL y hy 1 i) (hR.2.2.2.2.1 (A 1 0))
    have p3 := hR.2.2.1 ρ₀ 0 _ _ hN hint
    rw [add_zero] at p1 p2 p3
    exact (hR.2.1 _ _ _ (hR.2.1 _ _ _ p1 p2).1 p3).1

end GlobalTheory.HilbFam.TwistSize
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedWeightDegree
section
open NumberField IsDedekindDomain MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.FlatTw GlobalTheory.IndefiniteRowSideFullHecke.ComponentMassSum

set_option synthInstance.maxHeartbeats 400000

namespace GlobalTheory.Proof.TwistedWeightDegree

theorem degW_twist : ∀ (D : D7) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (V : (c.F →+* ℂ) → HSp D) (dict : ∀ σ, GA D (V σ) → Σ k, Frame ((U σ).X k).Ψ r), IsComplexData U V dict → ∀ (G₀ G : WTZ D.host.E) (s : ∀ Z : Comp Xo c, TwSec U (xiR D) Z G₀) (B : Finset ℕ) (τ : ℝ), Even G.2 → (∀ p ∈ B, p.Prime) → (∀ Z, IntOff B (s Z).lo) → (∀ Z, τ ≤ (s Z).degLo) → GoodW U (xiR D) V dict G → GoodW U (xiR D) V dict (G + G₀) ∧ rankW U (G + G₀) = rankW U G ∧ degW U (xiR D) V dict G + (rankW U G : ℝ) * (τ - logSum B) ≤ degW U (xiR D) V dict (G + G₀) := by
  intro D H Dw l Xo c r U V dict hC G₀ G s B τ hev hB hint hτ hG
  have hU : ∀ σ, GoodEmb c σ → IsUnf (U σ) := fun σ hσ => (hC.2 σ hσ).1
  have hA : ∀ G' : WTZ D.host.E, Adds U V dict G' := fun G' =>
    GlobalTheory.T.component_ranks_degrees_add_with_masses D H Dw l Xo c r U V dict G' (GlobalTheory.T.cuspForms_supLattice_split_over_components D H Dw l Xo c r U V dict hU G')
      ((GlobalTheory.T.components_peterssonOrthogonal_and_masses D H Dw l Xo c r U V dict hC G').1)
  have hOn : ∀ Z, GoodOn U (xiR D) V dict Z G := (hA G).1.1 hG
  have hgr : ∀ Z, GoodOn U (xiR D) V dict Z (G + G₀) ∧ rankOn U Z (G + G₀) = rankOn U Z G := fun Z =>
    GlobalTheory.T.twistingSection_preserves_hermitianLattices_ranks D.host.E H Dw l Xo c r U (xiR D) D V dict Z G₀ (s Z) G hU hev (hOn Z)
  have hG' : GoodW U (xiR D) V dict (G + G₀) := (hA (G + G₀)).1.2 (fun Z => (hgr Z).1)
  obtain ⟨-, hr1, -, -, hd1⟩ := (hA G).2 hG
  obtain ⟨-, hr2, -, -, hd2⟩ := (hA (G + G₀)).2 hG'
  have hrank : rankW U (G + G₀) = rankW U G := by
    rw [hr1, hr2]; exact finsum_congr fun Z => (hgr Z).2
  refine ⟨hG', hrank, ?_⟩
  haveI : Finite (Comp Xo c) := finite_comp
  letI := Fintype.ofFinite (Comp Xo c)
  have hZ : ∀ Z, degOn U (xiR D) V dict Z G + (rankOn U Z G : ℝ) * (τ - logSum B) ≤
      degOn U (xiR D) V dict Z (G + G₀) := fun Z => by
    have h1 := GlobalTheory.T.cuspForm_supLattice_degree_twist_lower_bound D.host.E H Dw l Xo c r U (xiR D) D V dict Z G₀ (s Z) G B hU hev hB (hint Z) (hOn Z)
    have h2 : (rankOn U Z G : ℝ) * (τ - logSum B) ≤ (rankOn U Z G : ℝ) * ((s Z).degLo - logSum B) :=
      mul_le_mul_of_nonneg_left (by linarith [hτ Z]) (Nat.cast_nonneg _)
    linarith
  rw [hd1, hd2, hr1]
  simp only [finsum_eq_sum_of_fintype, Nat.cast_sum, Finset.sum_mul, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro Z _
  rw [(hgr Z).2]
  linarith [hZ Z]

end GlobalTheory.Proof.TwistedWeightDegree
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisationRingActionAdjointCubeBundle
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum.UnifAdjoint

open GlobalTheory.CechPic GlobalTheory.ZH.EndoExtend

theorem lbIso_cubeLB_star : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ U : Unif (maximalIdeal R) D A G, ∀ (O : Type) [CommRing O] [StarRing O] [Module O D.toPre.X] (o : D.toPre.OAct O) (oA : A.OAct O) (oG : RingAct G O), U.toUnifPre.OLinear O o oA oG → ∀ a : O, LBIso (cubeLB G ![fst G G ≫ oG.act a, snd G G] U.LG.L) (cubeLB G ![fst G G, snd G G ≫ oG.act (star a)] U.LG.L) := by
  intro R _ _ _ hR D A G _ _ hG U O _ _ _ o oA oG hlin a
  obtain ⟨hno, -, hic, -⟩ := hR
  have hS : IsSemiAbelian G := hG
  have := hS.smooth
  have := hS.geomConnected
  have := geometricallyIntegral_of_smooth G.hom
  have := smooth_tensorObj_hom G G
  have := geometricallyIntegral_tensorObj_hom G G
  have ha := oG.hom a
  have hsa := oG.hom (star a)
  have hgen := U.gen_hom
  have hL := U.LG.isLB
  have hA := A.isLB
  have h₁ : IsPreimmersion (jK R) := IsPreimmersion.of_isLocalization (nonZeroDivisors R)
  have h₂ : Flat (jK R) := by
    rw [HasRingHomProperty.Spec_iff (P := @Flat)]
    exact RingHom.flat_algebraMap_iff.2 (IsLocalization.flat _ (nonZeroDivisors R))
  have h₃ : IsDominant (jK R) := ⟨(PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical _).2
    (((RingHom.injective_iff_ker_eq_bot _).1 (IsFractionRing.injective R (FractionRing R))).le.trans bot_le)⟩
  have hn : Geo.Tor.IsNormalScheme (Sp R) := (GlobalTheory.isNormalScheme_iff_pred _).1 inferInstance
  have h0 : CechPic.pull (eSec G) (cls U.LG.L hL) = 0 :=
    (cls_eq_zero_iff (pull_isLB hL _)).2 ⟨U.LG.rig, U.LG.rigGen⟩

  have eA : cubeCls A.A ![fst A.A A.A ≫ oA.act a, snd A.A A.A] (cls A.L hA) =
      cubeCls A.A ![fst A.A A.A, snd A.A A.A ≫ oA.act (star a)] (cls A.L hA) :=
    (cls_cubeLB A.A _ hA).symm.trans (((cls_eq_iff (LB.isLB_linComb hA _ _) (LB.isLB_linComb hA _ _)).2
      (GlobalTheory.FullPoint.lbIso_of_rosatiAdj hA (oA.rosati a))).trans (cls_cubeLB A.A _ hA))
  have hc' : CechPic.pull (pullback.fst G.hom (jK R)) (cls U.LG.L hL) =
      CechPic.pull U.gen.hom.left (cls A.L hA) := by
    obtain ⟨w, hw⟩ := U.ext
    rw [← cls_pull hL _ (pull_isLB hL _), ← cls_pull hA _ (pull_isLB hA _)]
    exact ((cls_eq_iff _ _).2 ⟨w, hw⟩).symm

  have hgK : cubeCls ((Over.pullback (jK R)).obj G)
        ![fst ((Over.pullback (jK R)).obj G) ((Over.pullback (jK R)).obj G) ≫ (Over.pullback (jK R)).map (oG.act a),
          snd ((Over.pullback (jK R)).obj G) ((Over.pullback (jK R)).obj G)]
        (CechPic.pull (pullback.fst G.hom (jK R)) (cls U.LG.L hL)) =
      cubeCls ((Over.pullback (jK R)).obj G)
        ![fst ((Over.pullback (jK R)).obj G) ((Over.pullback (jK R)).obj G),
          snd ((Over.pullback (jK R)).obj G) ((Over.pullback (jK R)).obj G) ≫ (Over.pullback (jK R)).map (oG.act (star a))]
        (CechPic.pull (pullback.fst G.hom (jK R)) (cls U.LG.L hL)) := by
    rw [hc']
    let u := lift (fst ((Over.pullback (jK R)).obj G) ((Over.pullback (jK R)).obj G) ≫ U.gen.hom)
      (snd ((Over.pullback (jK R)).obj G) ((Over.pullback (jK R)).obj G) ≫ U.gen.hom)
    have hu : u.left ≫ (A.A ⊗ A.A).hom = ((Over.pullback (jK R)).obj G ⊗ (Over.pullback (jK R)).obj G).hom ≫ 𝟙 _ := by
      rw [Category.comp_id]; exact Over.w u
    have e₁ := hlin.ext a
    have e₂ := hlin.ext (star a)
    rw [← push_cubeCls (isGrpPullback_of_iso U.gen) _ ![fst A.A A.A ≫ oA.act a, snd A.A A.A] u.left hu (fun i => ?_),
      ← push_cubeCls (isGrpPullback_of_iso U.gen) _ ![fst A.A A.A, snd A.A A.A ≫ oA.act (star a)] u.left hu
        (fun i => ?_), eA]
    · fin_cases i
      · show (fst _ _ ≫ U.gen.hom).left = (u ≫ fst A.A A.A).left
        congr 1; simp [u]
      · show ((snd _ _ ≫ (Over.pullback (jK R)).map (oG.act (star a))) ≫ U.gen.hom).left = (u ≫ snd A.A A.A ≫ oA.act (star a)).left
        congr 1; simp [u, e₂]
    · fin_cases i
      · show ((fst _ _ ≫ (Over.pullback (jK R)).map (oG.act a)) ≫ U.gen.hom).left = (u ≫ fst A.A A.A ≫ oA.act a).left
        congr 1; simp [u, e₁]
      · show (snd _ _ ≫ U.gen.hom).left = (u ≫ snd A.A A.A).left
        congr 1; simp [u]
  refine (cls_eq_iff (LB.isLB_linComb hL _ _) (LB.isLB_linComb hL _ _)).1
    ((cls_cubeLB G _ hL).trans (Eq.trans ?_ (cls_cubeLB G _ hL).symm))
  refine pic_ext (jK R) hn (G ⊗ G) (lift η[G] η[G]).left (Over.w _) ?_ ?_
  · refine (pull_cubeCls G _ (fun _ => η[G]) (lift η[G] η[G]) (fun i => ?_) _).trans
      (pull_cubeCls G _ (fun _ => η[G]) (lift η[G] η[G]) (fun i => ?_) _).symm <;>
    fin_cases i <;> simp
  · have hGp := isGrpPullback_pullback G (jK R)
    have Aw : ∀ {Y Z : Over (Sp R)} (q : Y ⟶ Z),
        ((Over.pullback (jK R)).map q).left ≫ pullback.fst Z.hom (jK R) = pullback.fst Y.hom (jK R) ≫ q.left :=
      fun q => pullback.lift_fst _ _ _
    let δ := lift ((Over.pullback (jK R)).map (fst G G)) ((Over.pullback (jK R)).map (snd G G))
    have e := congrArg (CechPic.pull δ.left) hgK
    have e' := fun x : Fin 2 → (G ⊗ G ⟶ G) => push_cubeCls hGp (T' := (Over.pullback (jK R)).obj (G ⊗ G)) (T := G ⊗ G)
      (fun i => (Over.pullback (jK R)).map (x i)) x (pullback.fst (G ⊗ G).hom (jK R)) pullback.condition
      (fun i => Aw _) (cls U.LG.L hL)
    rw [pull_cubeCls _ _ (fun i => (Over.pullback (jK R)).map (![fst G G ≫ oG.act a, snd G G] i)) δ
        (fun i => by fin_cases i <;> simp [δ]),
      pull_cubeCls _ _ (fun i => (Over.pullback (jK R)).map (![fst G G, snd G G ≫ oG.act (star a)] i)) δ
        (fun i => by fin_cases i <;> simp [δ])] at e
    exact (e' _).trans (e.trans (e' _).symm)

end GlobalTheory.Mum.UnifAdjoint
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitEqOfGermsPinchingSquareStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unit_eq_of_germs_pinching_square : ∀ (X X' Z Z' : Scheme.{0}) (p : X' ⟶ X) (i : Z ⟶ X) (i' : Z' ⟶ X') (p' : Z' ⟶ Z), i' ≫ p = p' ≫ i → GlobalTheory.PinchLift.Glues p i i' p' → ∀ (V : X.Opens) (u v : Γ(X, V)ˣ), (∀ x' : X', p x' ∈ V → gm p x' V u = gm p x' V v) → (∀ z : Z, i z ∈ V → gm i z V u = gm i z V v) → u = v := by
  first | exact @GlobalTheory.PinchLift.unit_eq_of_germs_glues | exact GlobalTheory.PinchLift.unit_eq_of_germs_glues | (intros; apply GlobalTheory.PinchLift.unit_eq_of_germs_glues <;> assumption)
end

