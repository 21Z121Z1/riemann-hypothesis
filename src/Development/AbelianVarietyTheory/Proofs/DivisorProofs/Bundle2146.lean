import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0167
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0268
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0195
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0264
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnramifiedDoublingIntegralInertPlace
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RamificationIdxEqOneOfIsSquare
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilDatumAtPlaceEqLatticeIntertwinerMulDetChar
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0672
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.AuxiliaryPrimeNeTypePrime
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0070
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.StChartF
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2112
import Development.AbelianVarietyTheory.Definitions.Divisors.LevelOfOfSameBut
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2124
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.NonemptyAlgHomOfIsRayOfDvd
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.CountsIrreducibilityConstants
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0069
import Formalism.LocalToGlobal.Bundle0003
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2123
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.SingleIndexPlacesAreTwisted
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2082
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2125
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2095
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2126
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2091

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProdEulerFactorOfRamified
section
open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP
open Formalism.IndefR.Links (ChrEq)

noncomputable section

namespace GlobalTheory.UnrCharZeta

open GlobalTheory.LFun GlobalTheory.PRep GlobalTheory.Core.Rk.TrivCoef
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open Formalism.L2.Host (HChar aboveF)
open GlobalTheory.CMVal (eulerFactor IsHeckeL)

section Seg

variable {E : Type} [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) (n : ℕ)

end Seg

variable {D : D7}

section Char

variable {E : Type} [Field E] [NumberField E]

theorem loc_inv (ν : HChar E) (w : HeightOneSpectrum (𝓞 E)) (x : (w.adicCompletion E)ˣ) :
    (ν⁻¹).loc w x = (ν.loc w x)⁻¹ := by
  rw [← GlobalTheory.CMVal.finPart_single, ← GlobalTheory.CMVal.finPart_single, GlobalTheory.CMVal.finPart_inv]

theorem unrAt_inv (ν : HChar E) (w : HeightOneSpectrum (𝓞 E)) : (ν⁻¹).UnrAt w ↔ ν.UnrAt w := by
  refine forall_congr' fun x => imp_congr_right fun _ => ?_
  rw [loc_inv, inv_eq_one]

theorem val_inv (ν : HChar E) (w : HeightOneSpectrum (𝓞 E)) : (ν⁻¹).val w = (ν.val w)⁻¹ := by
  rw [← GlobalTheory.CMVal.finPart_unifAt, ← GlobalTheory.CMVal.finPart_unifAt, GlobalTheory.CMVal.finPart_inv]

end Char

section Global

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

end Global

section Bottom

open GlobalTheory.FunObj.SqNum (botBig botSmall)

end Bottom

end GlobalTheory.UnrCharZeta

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProductDepthSumRoundingOscillation
section
set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain Formalism.L2.Pj ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.FGDepth GlobalTheory.CharDepth GlobalTheory.FactorDepth GlobalTheory.RefSum
open GlobalTheory.IndefiniteRowSideFullHecke.TypedPartSplitPrimes (IsIntHom IsOrbit FrobOnType embX primeBelow SplitInK InertInK)
open GlobalTheory.IndefiniteRowSideFullHecke.BigBlockCharacters (HasChars)
open GlobalTheory.IndefiniteRowSideFullHecke.FactorDepthInertBounds (boundAll boundInert boundFine)
namespace GlobalTheory.RefSum

theorem nuBetween_sum_and_eLoc_le : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), ∀ (p : ℕ) [Fact p.Prime] (la : PointsOfFlagModel.abelian₂ p c), ∀ (cx : Lt1 Dw → ℕ), (∀ A B : Lt1 Dw → ℝ, (∀ f, FacBetween Xo la f (cx f) (A f) (B f)) → NuBetween Xo la cx (∑ f, A f) (∑ f, B f) ∧ ∃ n : ℕ, NuBetween Xo la cx n (n + (∑ f, (B f - A f) + 1))) ∧ ∀ b : ℝ, OscLe Xo c p cx b → ∀ (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (Z : Comp Xo c), (letI := H.starRing; eLoc Y Z la cx ≤ (b : EReal)) := by
  intro E _ _ _ H Dw l Xo c p _ la cx
  letI := H.starRing
  have hcs : ∀ g : Lt1 Dw → ℝ, (((∑ f, g f : ℝ)) : EReal) = ∑ f, ((g f : ℝ) : EReal) := fun g =>
    map_sum (⟨⟨((↑) : ℝ → EReal), EReal.coe_zero⟩, EReal.coe_add⟩ : ℝ →+ EReal) g Finset.univ
  refine ⟨fun A B hAB => ⟨fun T io e ho y => ⟨?_, fun ha => ?_⟩, ?_⟩, ?_⟩
  · rw [hcs]; exact Finset.sum_le_sum fun f _ => (hAB f T io e ho y).1
  · rw [hcs]; exact Finset.sum_le_sum fun f _ => (hAB f T io e ho y).2 ha
  · set s : ℝ := ∑ f, A f with hs
    refine ⟨⌊max 0 s⌋₊, fun T io e ho y => ⟨?_, fun ha => ?_⟩⟩
    · have h0 : (0 : EReal) ≤ nuP p y cx := Finset.sum_nonneg fun f _ =>
        (GlobalTheory.T.factorDepth_between_zero_and_bound E H Dw l Xo c p la f (cx f)).1 T io e ho y |>.1 |> fun h => by simpa using h
      have h1 : ((s : ℝ) : EReal) ≤ nuP p y cx := by
        rw [hs, hcs]; exact Finset.sum_le_sum fun f _ => (hAB f T io e ho y).1
      have hn : ((⌊max 0 s⌋₊ : ℕ) : ℝ) ≤ max 0 s := Nat.floor_le (le_max_left _ _)
      rcases le_total 0 s with h | h
      · exact (EReal.coe_le_coe_iff.2 (hn.trans (max_eq_right h).le)).trans h1
      · exact (EReal.coe_le_coe_iff.2 (hn.trans (max_eq_left h).le)).trans (by simpa using h0)
    · have hu : nuP p y cx ≤ ((∑ f, B f : ℝ) : EReal) := by
        rw [hcs]; exact Finset.sum_le_sum fun f _ => (hAB f T io e ho y).2 ha
      refine hu.trans (EReal.coe_le_coe_iff.2 ?_)
      have hlt : max 0 s < ((⌊max 0 s⌋₊ : ℕ) : ℝ) + 1 := Nat.lt_floor_add_one _
      have hsd : ∑ f, (B f - A f) = ∑ f, B f - s := by rw [Finset.sum_sub_distrib]
      have hm : s ≤ max 0 s := le_max_right _ _
      linarith
  · intro b hb O _ β Y Z
    obtain ⟨A, hA⟩ := hb la
    calc eLoc Y Z la cx ≤ ((((A : ℝ) + b : ℝ)) : EReal) - (((A : ℝ)) : EReal) :=
          EReal.sub_le_sub (nuPSup_le fun T io e ho y hy => (hA T io e ho y).2 hy.2)
            (le_nuPInf fun T io e ho y _ => (hA T io e ho y).1)
      _ = (b : EReal) := by rw [← EReal.coe_sub]; congr 1; ring

end GlobalTheory.RefSum

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ReadingScalarsIntegral
section
open GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.BigOn.Exp
open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx
open Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open Formalism.IndefR.FWT GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies GlobalTheory.SeriesTie
open GlobalTheory.IndefiniteRowSideFullHecke.ToricLatticeDenominators (FmExt eExt incl)
open scoped TensorProduct
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.BigOn.Exp

section ScalarGeneric

variable {O : Type} [CommRing O] [IsDomain O] {M : Type} [AddCommGroup M] [Module (FractionRing O) M] [Module O M]
  [IsScalarTower O (FractionRing O) M] [FiniteDimensional (FractionRing O) M]
  {L : Type} [Field L] [Algebra O L] {eK : FractionRing O →+* ℂ} {G : Type}

theorem exists_smul_eq_sum_tmul_finBasis (x : L ⊗[O] M) : ∃ d : O, d ≠ 0 ∧
    ∃ c : _ → L, d • x = ∑ a, c a ⊗ₜ Module.finBasis (FractionRing O) M a := by
  induction x using TensorProduct.induction_on with
  | zero => exact ⟨1, one_ne_zero, 0, by simp⟩
  | add x y hx hy =>
    obtain ⟨d, hd, c, e⟩ := hx
    obtain ⟨d', hd', c', e'⟩ := hy
    refine ⟨d * d', mul_ne_zero hd hd', d' • c + d • c', ?_⟩
    rw [smul_add, mul_smul d d' y, mul_comm, mul_smul, e, e']
    simp [Finset.smul_sum, TensorProduct.add_tmul, Finset.sum_add_distrib, TensorProduct.smul_tmul']
  | tmul a f =>
    obtain ⟨d, hd⟩ := IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors O)
      fun c => (Module.finBasis (FractionRing O) M).repr f c
    choose y hy using hd
    refine ⟨d, nonZeroDivisors.coe_ne_zero d, fun c => y c • a, ?_⟩
    rw [← TensorProduct.tmul_smul]
    conv_lhs => rw [← (Module.finBasis (FractionRing O) M).sum_repr f]
    rw [Finset.smul_sum, TensorProduct.tmul_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [TensorProduct.smul_tmul, ← algebraMap_smul (FractionRing O) (y c), hy, smul_assoc]

variable (rd : M →ₛₗ[eK] (G → ℂ)) (eL : L →+* ℂ)
  (hL : ∀ c : O, eL (algebraMap O L c) = eK (algebraMap O (FractionRing O) c))

theorem readExt_scalar_mem_range
    (hF : ∀ (n : ℕ) (v : Fin n → M), LinearIndependent (FractionRing O) v → LinearIndependent ℂ fun c => rd (v c))
    (x₁ x₂ : L ⊗[O] M) (κ : ℂ) (h : readExt rd eL hL x₁ = κ • readExt rd eL hL x₂) (h₂ : readExt rd eL hL x₂ ≠ 0) :
    ∃ b : L, eL b = κ := by
  set v := Module.finBasis (FractionRing O) M
  have hδ : ∀ d : O, d ≠ 0 → eL (algebraMap O L d) ≠ 0 := fun d hd => by
    rw [hL]
    exact (map_ne_zero eK).2 ((map_ne_zero_iff _ (IsFractionRing.injective O (FractionRing O))).2 hd)
  have hsum : ∀ x : L ⊗[O] M, ∀ (d : O) (c : _ → L), d • x = ∑ a, c a ⊗ₜ v a →
      ∑ a, eL (c a) • rd (v a) = eL (algebraMap O L d) • readExt rd eL hL x := fun x d c e => by
    have := congrArg (readExt rd eL hL) e
    rw [← algebraMap_smul L d x, readExt_smul, map_sum] at this
    rw [this]
    rfl
  obtain ⟨d₁, hd₁, c₁, e₁⟩ := exists_smul_eq_sum_tmul_finBasis x₁
  obtain ⟨d₂, hd₂, c₂, e₂⟩ := exists_smul_eq_sum_tmul_finBasis x₂
  have r₁ := hsum _ _ _ e₁
  have r₂ := hsum _ _ _ e₂
  set δ₁ := eL (algebraMap O L d₁)
  set δ₂ := eL (algebraMap O L d₂)
  have h0 : ∑ a, (eL (c₁ a) - δ₁ * κ * δ₂⁻¹ * eL (c₂ a)) • rd (v a) = 0 := by
    have e3 : ∑ a, (eL (c₁ a) - δ₁ * κ * δ₂⁻¹ * eL (c₂ a)) • rd (v a) =
        ∑ a, eL (c₁ a) • rd (v a) - (δ₁ * κ * δ₂⁻¹) • ∑ a, eL (c₂ a) • rd (v a) := by
      simp only [sub_smul, Finset.sum_sub_distrib, Finset.smul_sum, mul_smul]
    rw [e3, r₁, r₂, h, smul_smul, smul_smul, inv_mul_cancel_right₀ (hδ _ hd₂), sub_self]
  have hc := Fintype.linearIndependent_iff.1 (hF _ v v.linearIndependent) _ h0
  obtain ⟨a, ha⟩ : ∃ a, c₂ a ≠ 0 := by
    by_contra hne
    push_neg at hne
    apply h₂
    have : δ₂ • readExt rd eL hL x₂ = 0 := by rw [← r₂]; simp [hne]
    exact (smul_eq_zero.1 this).resolve_left (hδ _ hd₂)
  have hca : eL (c₂ a) ≠ 0 := (map_ne_zero eL).2 ha
  refine ⟨c₁ a * algebraMap O L d₂ / (algebraMap O L d₁ * c₂ a), ?_⟩
  have e := sub_eq_zero.1 (hc a)
  rw [map_div₀, map_mul, map_mul, e]
  have h1 : δ₁ ≠ 0 := hδ _ hd₁
  have h2 : δ₂ ≠ 0 := hδ _ hd₂
  change δ₁ * κ * δ₂⁻¹ * eL (c₂ a) * δ₂ / (δ₁ * eL (c₂ a)) = κ
  rw [div_eq_iff (mul_ne_zero h1 hca)]
  calc δ₁ * κ * δ₂⁻¹ * eL (c₂ a) * δ₂ = δ₁ * κ * eL (c₂ a) * (δ₂⁻¹ * δ₂) := by ring
    _ = κ * (δ₁ * eL (c₂ a)) := by rw [inv_mul_cancel₀ h2]; ring

end ScalarGeneric

theorem exists_algebraMap_eq_of_isIntegral {R : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (e : FractionRing R →+* ℂ) (b₀ : FractionRing R) (N : ℕ) (hN : IsUnit (N : R)) (m : ℕ)
    (h : IsIntegral ℤ ((N : ℂ) ^ m * e b₀)) : ∃ b : R, algebraMap R (FractionRing R) b = b₀ := by
  let f : FractionRing R →ₐ[ℤ] ℂ := { e with commutes' := fun r => by simp }
  have e1 : (N : ℂ) ^ m * e b₀ = f ((N : FractionRing R) ^ m * b₀) := by
    simp [f, map_mul, map_pow, map_natCast]
  rw [e1] at h
  have h' : IsIntegral ℤ ((N : FractionRing R) ^ m * b₀) := (isIntegral_algHom_iff f e.injective).1 h
  obtain ⟨c, hc⟩ := IsIntegrallyClosed.isIntegral_iff.1 (h'.tower_top (A := R))
  refine ⟨(↑hN.unit⁻¹ : R) ^ m * c, ?_⟩
  have hu : algebraMap R (FractionRing R) (↑hN.unit⁻¹ : R) * (N : FractionRing R) = 1 := by
    rw [← map_natCast (algebraMap R (FractionRing R)) N, ← map_mul, hN.val_inv_mul, map_one]
  rw [map_mul, map_pow, hc, ← mul_assoc, ← mul_pow, hu, one_pow, one_mul]
set_option maxHeartbeats 4000000 in

theorem scalar_of_reading : AtFit fun Fm x hx i p w j ρ hρ ν _ => ∀ e : FractionRing ((Fm.ex x hx i).nch.Oe w) →+* ℂ, (∀ y, e ((Fm.ex x hx i).nch.embW w y) = (Fm.D x i).what₂.embLL y) → (∀ a : (Fm.D x i).ntw.Ok ((Fm.ex x hx i).nch.twI w) ((Fm.ex x hx i).nch.k' w), e (algebraMap ((Fm.ex x hx i).nch.Oe w) _ (algebraMap _ ((Fm.ex x hx i).nch.Oe w) a)) = ρ.eOk ((Fm.ex x hx i).nch.twI w) ((Fm.ex x hx i).nch.sd w) ((Fm.ex x hx i).nch.k' w) a) →
  ∀ (z : (Fm.D x i).ntw.Ok ((Fm.ex x hx i).nch.twI w) ((Fm.ex x hx i).nch.k' w) ⊗[(Fm.D x i).ntw.O ((Fm.ex x hx i).nch.twI w)] (Fm.D x i).nexp.Fm ((Fm.ex x hx i).nch.twI w) ((j : ℕ) + 1) ((Fm.ex x hx i).nch.sd w)) (n : ℕ) (a : Fin n → (Fm.ex x hx i).nch.Oe w) (y : Fin n → Fin ((R2 p).nW j) → (Fm.D x i).what₂.LL) (κ : ℂ) (N : ℕ),
    (∀ k, y k ∈ Submodule.span (Fm.D x i).what₂.LL ((p.nexp.fi j).e '' ((p.Sx.A ((j : ℕ) + 1)).WK : Set _))) → IsUnit ((N : ℕ) : (Fm.ex x hx i).nch.Oe w) → (∃ m : ℕ, IsIntegral ℤ ((N : ℂ) ^ m * κ)) →
    rdK (rdAt p w j hρ ν) hρ ((Fm.ex x hx i).nch.k' w) z = κ • ∑ k, (e (algebraMap ((Fm.ex x hx i).nch.Oe w) (FractionRing ((Fm.ex x hx i).nch.Oe w)) (a k)) * ν⁻¹) • adForm (R2 p) j (y k) (p.v₀ j (sg0 (Fm.D x i) p.P.A3.A)) →
    ∃ b : (Fm.ex x hx i).nch.Oe w, rdK (rdAt p w j hρ ν) hρ ((Fm.ex x hx i).nch.k' w) z = ∑ k, (e (algebraMap ((Fm.ex x hx i).nch.Oe w) (FractionRing ((Fm.ex x hx i).nch.Oe w)) (b * a k)) * ν⁻¹) • adForm (R2 p) j (y k) (p.v₀ j (sg0 (Fm.D x i) p.P.A3.A)) := by
  unfold AtFit AtTw AtPts
  refine ⟨1, one_pos, fun _ _ _ => ⟨⟨0, fun _ => 0, fun _ => 0, fun _ => 0⟩, fun Fm CH _ _ =>
    ⟨0, fun x hx _ i p hr hm w _ j ρ hρ ν rd hfit hcan => ?_⟩⟩⟩
  intro e he1 he2 z n a y κ N hy hN hint hz
  have hν : ν ≠ 0 := hfit.2.1.1
  obtain ⟨Z⟩ := hm.2.2.series
  have hU : p.R.toRealDat.LUnif := hr.prim.unif
  have hW : p.R.toRealDat.models_HW := p.charW.base.models.HW
  have hK : (p.Sx.A ((j : ℕ) + 1)).IsKsForm := GlobalTheory.isKsForm_of_formsIso _ _ (p.nexp.fi j) (p.fw.ks j)
  have hF : Faithful (rdAt p w j hρ ν) := GlobalTheory.SeriesTie.realRd_faithful _ _ _ _ _ _ _ p.R p.cG p.Sx p.nexp p.v₀ ρ hρ
    ((Fm.ex x hx i).nch.twI w) j ((Fm.ex x hx i).nch.sd w) ν hν hU hW (Z.vec j) hK
  have hL : ∀ c : (Fm.D x i).ntw.O ((Fm.ex x hx i).nch.twI w),
      e (algebraMap _ (FractionRing ((Fm.ex x hx i).nch.Oe w)) c) =
        ρ.e ((Fm.ex x hx i).nch.twI w) ((Fm.ex x hx i).nch.sd w) (algebraMap _ (FractionRing _) c) := fun c => by
    rw [IsScalarTower.algebraMap_apply _ ((Fm.ex x hx i).nch.Oe w) (FractionRing ((Fm.ex x hx i).nch.Oe w)),
      IsScalarTower.algebraMap_apply _ ((Fm.D x i).ntw.Ok ((Fm.ex x hx i).nch.twI w) ((Fm.ex x hx i).nch.k' w)) ((Fm.ex x hx i).nch.Oe w),
      he2, hρ.ek_e]
    rfl
  set R := readExt (rdAt p w j hρ ν) e hL with hRdef
  have hRinj : Function.Injective R := readExt_injective _ e hL hF
  have hinc : ∀ z, R (incl (Fm.D x i).nexp ((Fm.ex x hx i).nch.twI w) _ ((Fm.ex x hx i).nch.sd w) ((Fm.ex x hx i).nch.Oe w)
      ((Fm.ex x hx i).nch.k' w) z) = rdK (rdAt p w j hρ ν) hρ ((Fm.ex x hx i).nch.k' w) z := fun z => by
    induction z using TensorProduct.induction_on with
    | zero => rw [map_zero, map_zero, map_zero]
    | add u v hu hv => rw [map_add, map_add, map_add, hu, hv]
    | tmul c f =>
      rw [rdK_tmul, ← he2]
      rfl
  have hgen : ∀ f : NX.FmK p.Sx ((j : ℕ) + 1), R (rd ((p.nexp.fi j).e (Subtype.val f))) =
      ν⁻¹ • adForm (R2 p) j ((p.nexp.fi j).e (Subtype.val f)) (p.v₀ j (sg0 (Fm.D x i) p.P.A3.A)) := fun f => by
    rw [hcan f, hRdef, readExt_tmul, map_one, one_smul]
    erw [realRd_tmul]
    erw [map_one, mul_one]
    rfl
  have hA0 : adForm (R2 p) j 0 (p.v₀ j (sg0 (Fm.D x i) p.P.A3.A)) = 0 := by
    change ((R2 p).HW j _).e (((R2 p).FW j).j _ 0) (p.v₀ j _) = 0
    rw [map_zero, map_zero]
    rfl
  have hAadd : ∀ u v, adForm (R2 p) j (u + v) (p.v₀ j (sg0 (Fm.D x i) p.P.A3.A)) =
      adForm (R2 p) j u (p.v₀ j (sg0 (Fm.D x i) p.P.A3.A)) + adForm (R2 p) j v (p.v₀ j (sg0 (Fm.D x i) p.P.A3.A)) := fun u v => by
    change ((R2 p).HW j _).e (((R2 p).FW j).j _ (u + v)) (p.v₀ j _) = _
    rw [map_add, map_add]
    rfl
  have hs : sg0 (Fm.D x i) p.P.A3.A = (Fm.D x i).what₂.embLL := sgAt_mk _ (R2 p).hv0
  have hAsmul : ∀ (c : (Fm.D x i).what₂.LL) u, adForm (R2 p) j (c • u) (p.v₀ j (sg0 (Fm.D x i) p.P.A3.A)) =
      (Fm.D x i).what₂.embLL c • adForm (R2 p) j u (p.v₀ j (sg0 (Fm.D x i) p.P.A3.A)) := fun c u => by
    change ((R2 p).HW j _).e (((R2 p).FW j).j _ (c • u)) (p.v₀ j _) = _
    rw [LinearMap.map_smulₛₗ, map_smul]
    exact congrArg (fun s : ℂ => s • adForm (R2 p) j u (p.v₀ j (sg0 (Fm.D x i) p.P.A3.A))) (DFunLike.congr_fun hs c)
  have hrd : ∀ u ∈ Submodule.span (Fm.D x i).what₂.LL ((p.nexp.fi j).e '' ((p.Sx.A ((j : ℕ) + 1)).WK : Set _)),
      R (rd u) = ν⁻¹ • adForm (R2 p) j u (p.v₀ j (sg0 (Fm.D x i) p.P.A3.A)) := fun u hu => by
    induction hu using Submodule.span_induction with
    | mem u hu =>
      obtain ⟨f, hf, rfl⟩ := hu
      exact hgen ⟨f, hf⟩
    | zero =>
      erw [LinearMap.map_zero rd]
      rw [AddMonoidHom.map_zero R]
      erw [hA0]
      rw [smul_zero]
    | add u v _ _ hu hv =>
      erw [LinearMap.map_add rd]
      rw [AddMonoidHom.map_add R, hu, hv]
      erw [hAadd]
      rw [smul_add]
    | smul c u _ hu =>
      erw [LinearMap.map_smulₛₗ rd]
      rw [hRdef, readExt_smul, ← hRdef, hu, he1]
      erw [hAsmul]
      rw [smul_comm]
  have hS : R (∑ k, a k • rd (y k)) = ∑ k, (e (algebraMap ((Fm.ex x hx i).nch.Oe w) (FractionRing ((Fm.ex x hx i).nch.Oe w)) (a k)) * ν⁻¹) •
      adForm (R2 p) j (y k) (p.v₀ j (sg0 (Fm.D x i) p.P.A3.A)) := by
    rw [map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [← algebraMap_smul (FractionRing ((Fm.ex x hx i).nch.Oe w)) (a k) (rd (y k)), hRdef, readExt_smul, ← hRdef,
      hrd _ (hy k), mul_smul]
  have hRHS : ∀ b : ((Fm.ex x hx i).nch.Oe w), ∑ k, (e (algebraMap ((Fm.ex x hx i).nch.Oe w) (FractionRing ((Fm.ex x hx i).nch.Oe w)) (b * a k)) * ν⁻¹) •
      adForm (R2 p) j (y k) (p.v₀ j (sg0 (Fm.D x i) p.P.A3.A)) = e (algebraMap ((Fm.ex x hx i).nch.Oe w) (FractionRing ((Fm.ex x hx i).nch.Oe w)) b) •
      ∑ k, (e (algebraMap ((Fm.ex x hx i).nch.Oe w) (FractionRing ((Fm.ex x hx i).nch.Oe w)) (a k)) * ν⁻¹) •
      adForm (R2 p) j (y k) (p.v₀ j (sg0 (Fm.D x i) p.P.A3.A)) := fun b => by
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_mul, map_mul, smul_smul, mul_assoc]
  by_cases hT0 : ∑ k, (e (algebraMap ((Fm.ex x hx i).nch.Oe w) (FractionRing ((Fm.ex x hx i).nch.Oe w)) (a k)) * ν⁻¹) •
      adForm (R2 p) j (y k) (p.v₀ j (sg0 (Fm.D x i) p.P.A3.A)) = 0
  · exact ⟨0, by rw [hRHS, hz, hT0, smul_zero, smul_zero]⟩
  · obtain ⟨b₀, hb₀⟩ := readExt_scalar_mem_range _ e hL hF
      (incl (Fm.D x i).nexp ((Fm.ex x hx i).nch.twI w) _ ((Fm.ex x hx i).nch.sd w) ((Fm.ex x hx i).nch.Oe w) ((Fm.ex x hx i).nch.k' w) z)
      (∑ k, a k • rd (y k)) κ (by rw [hinc, hS, hz]) (by rwa [hS])
    obtain ⟨m, hmI⟩ := hint
    obtain ⟨b, hb⟩ := exists_algebraMap_eq_of_isIntegral e b₀ N hN m (by rwa [hb₀])
    exact ⟨b, by rw [hRHS, hz, hb, hb₀]⟩

end GlobalTheory.BigOn.Exp
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RealizationEmbeddingCompatibleStatement
section
open GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.BigOn.Exp
open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx
open Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open Formalism.IndefR.FWT GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies GlobalTheory.SeriesTie
open GlobalTheory.IndefiniteRowSideFullHecke.ToricLatticeDenominators (FmExt eExt incl)
open scoped TensorProduct
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.realization_embedding_compatible : AtFit fun Fm x hx i p w j ρ hρ ν rd => ∀ e : FractionRing ((Fm.ex x hx i).nch.Oe w) →+* ℂ, (∀ y, e ((Fm.ex x hx i).nch.embW w y) = (Fm.D x i).what₂.embLL y) → (∀ a : (Fm.D x i).ntw.Ok ((Fm.ex x hx i).nch.twI w) ((Fm.ex x hx i).nch.k' w), e (algebraMap ((Fm.ex x hx i).nch.Oe w) _ (algebraMap _ ((Fm.ex x hx i).nch.Oe w) a)) = ρ.eOk ((Fm.ex x hx i).nch.twI w) ((Fm.ex x hx i).nch.sd w) ((Fm.ex x hx i).nch.k' w) a) →
  ∀ (z : (Fm.D x i).ntw.Ok ((Fm.ex x hx i).nch.twI w) ((Fm.ex x hx i).nch.k' w) ⊗[(Fm.D x i).ntw.O ((Fm.ex x hx i).nch.twI w)] (Fm.D x i).nexp.Fm ((Fm.ex x hx i).nch.twI w) ((j : ℕ) + 1) ((Fm.ex x hx i).nch.sd w))
    (n : ℕ) (a : Fin n → (Fm.ex x hx i).nch.Oe w) (y : Fin n → Fin ((R2 p).nW j) → (Fm.D x i).what₂.LL), (∀ k, y k ∈ Submodule.span (Fm.D x i).what₂.LL ((p.nexp.fi j).e '' ((p.Sx.A ((j : ℕ) + 1)).WK : Set _))) →
    rdK (rdAt p w j hρ ν) hρ ((Fm.ex x hx i).nch.k' w) z = ∑ k, (e (algebraMap ((Fm.ex x hx i).nch.Oe w) (FractionRing ((Fm.ex x hx i).nch.Oe w)) (a k)) * ν⁻¹) • adForm (R2 p) j (y k) (p.v₀ j (sg0 (Fm.D x i) p.P.A3.A)) →
    incl (Fm.D x i).nexp ((Fm.ex x hx i).nch.twI w) _ ((Fm.ex x hx i).nch.sd w) ((Fm.ex x hx i).nch.Oe w) ((Fm.ex x hx i).nch.k' w) z = ∑ k, a k • rd (y k) := by
  first | exact @GlobalTheory.BigOn.Exp.descent_of_reading | exact GlobalTheory.BigOn.Exp.descent_of_reading | (intros; apply GlobalTheory.BigOn.Exp.descent_of_reading <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RowHTwOfTie
section
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem.Top GlobalTheory.Fc

namespace GlobalTheory.Fc

theorem row_hTw_of_tie : ∀ (Q : V4.Slot) (Lk : LkT Bundle), Row Q Lk (AtAll HasTie) → R1.TwistConditionAtBundlePoints Q Lk := by
  intro Q Lk h
  refine h.imp fun 𝒜 σ _ hT => ?_
  intro eps Fm hc x hx i
  obtain ⟨t⟩ := hT Fm hc x hx i
  exact Formalism.L2.Top4.tieTwRec_of (Q := (σ Fm hc x hx i).B.Q) t.1 (Fm.tw_supp x hx i)

end GlobalTheory.Fc
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RowSubstDualWeylExpressibleMatrixMulClosed
section
open MvPolynomial Formalism.GradedWeylDivisibility GlobalTheory.GenCoef

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.GenCoef

theorem rowSubst_mul_comp (O : Type) [CommRing O] (N : ℕ) (R : Type) [CommRing R] [Algebra O R]
    (Y Y' : Matrix (Fin N) (Fin N) R) (f : MvPolynomial (Fin N × Fin N) O) :
    rowSubst O N R (Y * Y') f = rowSubst R N R Y' (rowSubst O N R Y f) := by
  have h : (rowSubst O N R (Y * Y')) = ((rowSubst R N R Y').restrictScalars O).comp (rowSubst O N R Y) := by
    apply MvPolynomial.algHom_ext
    intro v
    simp only [rowSubst, AlgHom.comp_apply, AlgHom.restrictScalars_apply, aeval_X, map_sum, map_mul,
      algHom_C, Algebra.algebraMap_self, RingHom.id_apply, Matrix.mul_apply]
    simp only [Finset.mul_sum, Finset.sum_mul, mul_assoc]
    exact Finset.sum_comm
  rw [h]; rfl

theorem rowSubst_self_map (O : Type) [CommRing O] (N : ℕ) (R : Type) [CommRing R] [Algebra O R]
    (Y' : Matrix (Fin N) (Fin N) R) (q : MvPolynomial (Fin N × Fin N) O) :
    rowSubst R N R Y' (MvPolynomial.map (algebraMap O R) q) = rowSubst O N R Y' q := by
  have h : ((rowSubst R N R Y').restrictScalars O).comp (MvPolynomial.mapAlgHom (Algebra.ofId O R)) = rowSubst O N R Y' := by
    apply MvPolynomial.algHom_ext
    intro v
    simp [rowSubst]
  have := congrArg (fun φ => φ q) h
  simpa using this

theorem expr_mul (O : Type) [CommRing O] (N : ℕ) (ν : Fin N → ℕ) (R : Type) [CommRing R] [Algebra O R]
    (Y Y' : Matrix (Fin N) (Fin N) R) (hY : Expr O N ν R Y) (hY' : Expr O N ν R Y') :
    Expr O N ν R (Y * Y') := by
  obtain ⟨n, r, p, hp, hf⟩ := hY
  obtain ⟨n', r', p', hp', hf'⟩ := hY'
  refine ⟨n * n', fun k => r (finProdFinEquiv.symm k).1 * r' (finProdFinEquiv.symm k).2,
    fun k => p' (finProdFinEquiv.symm k).2 * p (finProdFinEquiv.symm k).1, fun k => Subalgebra.mul_mem _ (hp' _) (hp _), ?_⟩
  intro f
  rw [rowSubst_mul_comp, hf f, map_sum]
  have e := (finProdFinEquiv (m := n) (n := n')).symm.sum_comp
    (fun x : Fin n × Fin n' => (r x.1 * r' x.2) • MvPolynomial.map (algebraMap O R)
      (((p' x.2 * p x.1) f : dualWeyl O N N ν) : MvPolynomial (Fin N × Fin N) O))
  rw [e, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smul, rowSubst_self_map, hf' (p i f), Finset.smul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [smul_smul, Module.End.mul_apply]

end GlobalTheory.GenCoef
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SecondLinkOfWeightRows
section
open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.IndefR.FWT
open GlobalTheory.BigTop GlobalTheory.BigOn

namespace GlobalTheory.BigOn

theorem links2_of_rows : ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : Formalism.MainNotions.G.Inst D L) (Gl : Formalism.MainNotions.G.LatInst D)
    (Kc : Formalism.MainNotions.G.Consts) (Y : DivX D) (cX : ExtraC) (ex : Extra D L hT Gi Gl Kc Y cX) (Csz : ℝ) (p : PtAt ex Csz),
    p.Rows → SingleIndexPlacesAreTwisted p → Links2 p := by
  intro D L hT Gi Gl Kc Y cX ex Csz p hr hw
  obtain ⟨hU, hB, hR⟩ := GlobalTheory.T.split_rows_uniform_links_rank D L hT Gi Gl Kc Y cX ex Csz p hr
  obtain ⟨hBar, hPin, hPh⟩ := GlobalTheory.T.split_rows_bar_phase_compatibility D L hT Gi Gl Kc Y cX ex Csz p hr
  exact ⟨GlobalTheory.T.char_R2_of_exAt_of_singleIndexPlacesTwisted D L hT Gi Gl Kc Y cX ex Csz p hr.exAt hw, hr.ok.ok2, hU, hB, hR, hBar, hPin, hPh⟩

end GlobalTheory.BigOn
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmallPlaceBlockBoundStatement
section
open NumberField IsDedekindDomain TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.L2.Pj GlobalTheory.BigTop GlobalTheory.BigOn
open Formalism.CohomologicalDescent.LogSmallConstantBounds (Par)
open Formalism.CohomologicalDescent.ShortWeightBounds (Wts)
open GlobalTheory.ExpFrame GlobalTheory.ExpTie GlobalTheory.UnitaryBC GlobalTheory.CuspRep GlobalTheory.SmGL GlobalTheory.FrameAut
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.small_place_block_bound : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
    {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ} (p : PtAt ex Csz), PtAt.Rows p → More p →
    ∀ (j : Fin D.R.m) (P : Par) (W : Wts D.what₂.Tau), Dict L j P W → NumOk P W →
    ∀ w ∈ p.R.twPl, W.WRange P (Formalism.EigenvalueLevelCeiling.plc w) → SmallAt p j P w →
    ∀ ν ∈ (blk p j (p.R.mu w)).bl, ∀ Q, ‖D.what₂.embLL (ν Q)‖ ^ 2 = ((blk p j (p.R.mu w)).q Q : ℝ) ^ ((blk p j (p.R.mu w)).n - (blk p j (p.R.mu w)).t) := by
  first | exact @GlobalTheory.FrameAut.norm_sq_blockValue | exact GlobalTheory.FrameAut.norm_sq_blockValue | (intros; apply GlobalTheory.FrameAut.norm_sq_blockValue <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmallPlaceBlockDecompositionStatement
section
open NumberField IsDedekindDomain TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.L2.Pj GlobalTheory.BigTop GlobalTheory.BigOn
open Formalism.CohomologicalDescent.LogSmallConstantBounds (Par)
open Formalism.CohomologicalDescent.ShortWeightBounds (Wts)
open GlobalTheory.ExpFrame GlobalTheory.ExpTie GlobalTheory.UnitaryBC GlobalTheory.CuspRep GlobalTheory.SmGL GlobalTheory.FrameAut
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.small_place_block_decomposition : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
    {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ} (p : PtAt ex Csz), PtAt.Rows p → More p →
    ∀ (j : Fin D.R.m) (P : Par) (W : Wts D.what₂.Tau), Dict L j P W → NumOk P W →
    ∀ w ∈ p.R.twPl, W.WRange P (Formalism.EigenvalueLevelCeiling.plc w) → SmallAt p j P w →
    ∀ Q : (blk p j (p.R.mu w)).Pl, IsSplitAt (labOf p j (p.R.mu w) Q) ∧
      (labOf p j (p.R.mu w) Q).under (𝓞 (maximalRealSubfield D.host.E)) = (plOf p j (p.R.mu w) Q).under (𝓞 (maximalRealSubfield D.host.E)) ∧
      Ideal.absNorm (labOf p j (p.R.mu w) Q).asIdeal = (blk p j (p.R.mu w)).q Q ∧
      (((Formalism.EigenvalueLevelCeiling.plc w : ℕ) : 𝓞 D.host.E) ∈ (labOf p j (p.R.mu w) Q).asIdeal ↔ ((Formalism.EigenvalueLevelCeiling.plc w : ℕ) : 𝓞 D.host.E) ∈ (plOf p j (p.R.mu w) Q).asIdeal) := by
  first | exact @GlobalTheory.FrameLab.labels_ok | exact GlobalTheory.FrameLab.labels_ok | (intros; apply GlobalTheory.FrameLab.labels_ok <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwoLevelFlagDomainTransporterMemDomainStatement
section
open NumberField IsDedekindDomain Module ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.IndefiniteRowSideFullHecke.FrameWeightGapBounds Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.CovTop Formalism.L2.Pj GlobalTheory.FormTies GlobalTheory.Shares GlobalTheory.ShareOn GlobalTheory.ShareOn.Reading
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twoLevelFlagDomain_transporter_mem_domain : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {rr : ℕ} {U C : Type} [Group U] [MulAction U C] (M : TwoLevels E rr U C) (g : U) (c : C) (x : Frame M.Ψ rr), x ∈ M.dom → lact (M.tr g c) x ∈ M.dom := by
  first | exact @GlobalTheory.TwoLevelsDom.lact_tr_mem_dom | exact GlobalTheory.TwoLevelsDom.lact_tr_mem_dom | (intros; apply GlobalTheory.TwoLevelsDom.lact_tr_mem_dom <;> assumption)
end

