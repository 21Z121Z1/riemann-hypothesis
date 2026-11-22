import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0602
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsSmoothHermCombLine
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.CoheightEqOneOfDimClosure
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0180
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2455
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0878
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0548
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.LeviMatchingWords.SplitPlaceGeneratorPowers
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0550
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SpecializesIffPointIdealLe
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0539
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0540
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0875
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1437

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EulerCharacteristicDimensionZero
section
set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry Limits TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.ProjSpace GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt
open GroundTheory.Arith.SchemeCoh GroundTheory.Arith.SchemeCoh.ProjSpace
open ReciprocityTheory.ChartRestriction.G.Geo (MRing IsMultiHomog IsRelevant IsMultiProjPrime divSupp multAt geoNum charOf)
open GlobalTheory.CompanionTheory.MPDict GlobalTheory.CompanionTheory.MixZ GlobalTheory GlobalTheory.ProjBlowup

namespace GlobalTheory.CompanionTheory.MixZ.VertBase

theorem isField_of_subsingleton_primeSpectrum {R : Type} [CommRing R] [IsDomain R]
    (h : Subsingleton (PrimeSpectrum R)) : IsField R := by
  obtain ⟨M, hM⟩ := Ideal.exists_maximal R
  have hP : (⟨M, hM.isPrime⟩ : PrimeSpectrum R) = ⟨⊥, Ideal.isPrime_bot⟩ := Subsingleton.elim _ _
  have hMb : M = ⊥ := congrArg PrimeSpectrum.asIdeal hP
  exact Ring.isField_iff_maximal_bot.mpr (hMb ▸ hM)

variable (Z : Scheme.{0}) [IsIntegral Z]

theorem eq_genericPoint (hd : topologicalKrullDim Z = (0 : ℕ)) (x : Z) : x = genericPoint Z := by
  have hle : Order.krullDim (IrreducibleCloseds Z) ≤ 0 := by
    have h0 := hd
    simp only [topologicalKrullDim] at h0
    rw [h0]
    simp
  have hmax := Order.krullDim_nonpos_iff_forall_isMax.mp hle
  let C : IrreducibleCloseds Z := ⟨closure {x}, isIrreducible_singleton.closure, isClosed_closure⟩
  let U : IrreducibleCloseds Z := ⟨Set.univ, IrreducibleSpace.isIrreducible_univ _, isClosed_univ⟩
  have h1 : C ≤ U := fun _ _ => Set.mem_univ _
  have h2 : U ≤ C := hmax C h1
  have hg : genericPoint Z ∈ closure ({x} : Set Z) := h2 (Set.mem_univ _)
  have hs1 : x ⤳ genericPoint Z := specializes_iff_mem_closure.mpr hg
  have hs2 : genericPoint Z ⤳ x := (genericPoint_spec Z).specializes (Set.mem_univ x)
  exact (hs1.antisymm hs2).eq

theorem isAffineOpen_top (hd : topologicalKrullDim Z = (0 : ℕ)) : IsAffineOpen (⊤ : Z.Opens) := by
  obtain ⟨U, hU, hxU, -⟩ := exists_isAffineOpen_mem_and_subset
    (show genericPoint Z ∈ (⊤ : Z.Opens) from Set.mem_univ _)
  have hUt : U = ⊤ := eq_top_iff.mpr fun y _ => by rw [eq_genericPoint Z hd y]; exact hxU
  exact hUt ▸ hU

theorem isField_top (hd : topologicalKrullDim Z = (0 : ℕ)) : IsField Γ(Z, ⊤) := by
  have hA := isAffineOpen_top Z hd
  have hsub : Subsingleton (PrimeSpectrum Γ(Z, ⊤)) := by
    constructor
    intro p q
    exact hA.fromSpec.isOpenEmbedding.injective
      ((eq_genericPoint Z hd _).trans (eq_genericPoint Z hd _).symm)
  exact isField_of_subsingleton_primeSpectrum hsub

theorem bijective_top (hd : topologicalKrullDim Z = (0 : ℕ)) :
    Function.Bijective ((IsLocalRing.residue (Z.presheaf.stalk (genericPoint Z))).comp
      (algebraMap Γ(Z, ⊤) Z.functionField)) := by
  have hF := isField_top Z hd
  constructor
  · rw [injective_iff_map_eq_zero]
    intro a ha
    by_contra h
    obtain ⟨b, hb⟩ := hF.mul_inv_cancel h
    have h1 := congrArg ((IsLocalRing.residue (Z.presheaf.stalk (genericPoint Z))).comp
      (algebraMap Γ(Z, ⊤) Z.functionField)) hb
    rw [map_mul, ha, zero_mul, map_one] at h1
    exact zero_ne_one h1
  · intro y
    obtain ⟨t, rfl⟩ := IsLocalRing.residue_surjective y
    obtain ⟨U, hm, s, hs⟩ := Z.presheaf.exists_germ_eq t
    have hU : U = ⊤ := eq_top_iff.mpr fun x _ => by rw [eq_genericPoint Z hd x]; exact hm
    subst hU
    exact ⟨s, by rw [RingHom.comp_apply, ← hs]; rfl⟩

theorem chi_eq_geoNum : ∀ (m : ℕ) (n : Fin (m + 1) → ℕ) (Z : Scheme.{0}) [IsIntegral Z] (f : Z ⟶ MP ℤ m n)
    [IsClosedImmersion f] (p : ℕ) [Fact p.Prime] [Algebra (ZMod p) Γ(Z, ⊤)],
    topologicalKrullDim Z = (0 : ℕ) → ∀ a : Fin 0 → Fin (m + 1) → ℤ,
      chi (ZMod p) (structureModule Z) = geoNum 0 (ptIdeal (f (genericPoint Z))) a := by
  intro m n Z _ f _ p _ _ hd a
  have hp : p.Prime := Fact.out
  have hA := isAffineOpen_top Z hd
  haveI : IsAffine (⊤ : Z.Opens) := hA
  haveI : IsAffine Z := by
    first
      | exact IsAffine.of_isIso Z.topIso.inv
      | exact isAffine_of_isIso Z.topIso.inv
      | exact AlgebraicGeometry.isAffineOpen_top_iff.mp hA
      | exact (AlgebraicGeometry.isAffineOpen_top_iff Z).mp hA
      | exact IsAffine.of_isIso (Scheme.topIso Z).inv
      | exact hA.isAffine_of_top
  rw [GlobalTheory.chi_structureModule_of_isAffine Z (ZMod p)]
  have hb := bijective_top Z hd
  have hRes : CharP (Z.residueField (genericPoint Z)) p :=
    (RingHom.charP_iff_charP (((IsLocalRing.residue (Z.presheaf.stalk (genericPoint Z))).comp
      (algebraMap Γ(Z, ⊤) Z.functionField)).comp (algebraMap (ZMod p) Γ(Z, ⊤))) p).mp inferInstance
  haveI hΩ : CharP ((MP ℤ m n).residueField (f (genericPoint Z))) p :=
    (RingHom.charP_iff_charP (f.residueFieldMap (genericPoint Z)).hom p).mpr hRes
  have hcomap : (ptIdeal (f (genericPoint Z))).comap (C : ℤ →+* MRing (Bk n)) =
      Ideal.span {(p : ℤ)} := by
    ext z
    rw [Ideal.mem_comap, Ideal.mem_span_singleton,
      ← CharP.intCast_eq_zero_iff ((MP ℤ m n).residueField (f (genericPoint Z))) p]
    simp only [ptIdeal, ReciprocityTheory.ChartRestriction.G.Geo.mCoordIdeal, RingHom.mem_ker, ReciprocityTheory.ChartRestriction.G.Geo.mConeMap,
      MvPolynomial.aeval_C, MvPolynomial.algebraMap_apply, MvPolynomial.C_eq_zero, eq_intCast]
    rw [map_intCast, ← map_intCast (MvPolynomial.C : (MP ℤ m n).residueField (f (genericPoint Z)) →+*
      MvPolynomial (Fin (m + 1)) ((MP ℤ m n).residueField (f (genericPoint Z)))), MvPolynomial.C_eq_zero]
  have hchar : charOf (ptIdeal (f (genericPoint Z))) = p := by
    have key : ∀ I : Ideal ℤ, I = Ideal.span {(p : ℤ)} →
        (Submodule.IsPrincipal.generator I).natAbs = p := by
      rintro I rfl
      have hg := Submodule.IsPrincipal.span_singleton_generator (Ideal.span {(p : ℤ)})
      have hass : Associated (Submodule.IsPrincipal.generator (Ideal.span {(p : ℤ)})) (p : ℤ) :=
        Ideal.span_singleton_eq_span_singleton.mp hg
      rw [Int.natAbs_eq_iff_associated.mpr hass]
      simp
    exact key _ hcomap
  have hcl : topologicalKrullDim (closure ({genericPoint Z} : Set Z)) = (0 : ℕ) :=
    (dim_closure_generic Z).trans hd
  have hL := GlobalTheory.T.mixed_point_length_formula m n Z f (genericPoint Z) hcl a
  rw [hchar] at hL
  have hcard : Nat.card (Z.residueField (genericPoint Z)) = Nat.card Γ(Z, ⊤) :=
    (Nat.card_eq_of_bijective _ hb).symm
  rw [hcard] at hL
  have hlogp : Real.log p ≠ 0 := (Real.log_pos (by exact_mod_cast hp.one_lt)).ne'
  by_cases hfin : Module.Finite (ZMod p) Γ(Z, ⊤)
  · rw [Module.natCard_eq_pow_finrank (K := ZMod p), Nat.card_zmod, Nat.cast_pow, Real.log_pow] at hL
    have hg : (geoNum 0 (ptIdeal (f (genericPoint Z))) a : ℝ) =
        (Module.finrank (ZMod p) Γ(Z, ⊤) : ℝ) := mul_right_cancel₀ hlogp hL
    exact_mod_cast hg.symm
  · rw [Module.finrank_of_not_finite hfin]
    haveI : Infinite Γ(Z, ⊤) := by
      by_contra hinf
      rw [not_infinite_iff_finite] at hinf
      exact hfin Module.Finite.of_finite
    rw [Nat.card_eq_zero_of_infinite, Nat.cast_zero, Real.log_zero] at hL
    have hg : (geoNum 0 (ptIdeal (f (genericPoint Z))) a : ℝ) = 0 := by
      rcases mul_eq_zero.mp hL with h | h
      · exact h
      · exact absurd h hlogp
    exact_mod_cast hg.symm

end GlobalTheory.CompanionTheory.MixZ.VertBase
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GeneratorPowSplitPlacesIdempotentStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.generator_pow_split_places_idempotent : PositivityTheory.Rg.BcB.F.MLM.SplitPowersOfIdempotents := by
  first | exact @GlobalTheory.CompanionTheory.SplitPlacePowers.generator_pow_split_places_of_idempotent | exact GlobalTheory.CompanionTheory.SplitPlacePowers.generator_pow_split_places_of_idempotent | (intros; apply GlobalTheory.CompanionTheory.SplitPlacePowers.generator_pow_split_places_of_idempotent <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GenericPointNonvanishingCoordinateSection
section
set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry Limits TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.ProjSpace GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt
open GroundTheory.Arith.SchemeCoh GroundTheory.Arith.SchemeCoh.ProjSpace
open ReciprocityTheory.ChartRestriction.G.Geo (MRing IsMultiHomog IsRelevant IsMultiProjPrime divSupp multAt geoNum charOf)
open GlobalTheory.CompanionTheory.MPDict GlobalTheory.CompanionTheory.MixZ GlobalTheory GlobalTheory.ProjBlowup

namespace GlobalTheory.CompanionTheory.MixZ.VertGen

private theorem pullForm_X_eq_pullRatio {N : ℕ} {Y : Scheme.{0}} (φ : Y ⟶ PSpace ℤ N) (W : Y.Opens)
    (i : Fin (N + 1)) (hi : W ≤ (Opens.map φ.base).obj (GlobalTheory.ProjSpace.chart ℤ N i)) (l : Fin (N + 1))
    (h : (MvPolynomial.X l : MvPolynomial (Fin (N + 1)) ℤ).IsHomogeneous 1) :
    GlobalTheory.ProjBlowup.pullForm φ W i hi 1 (MvPolynomial.X l) h = GlobalTheory.ProjSpace.pullRatio φ W i hi l := by
  unfold GlobalTheory.ProjBlowup.pullForm GlobalTheory.ProjSpace.pullRatio GlobalTheory.ProjSpace.formOn GlobalTheory.ProjSpace.ratio
    GlobalTheory.ProjSpace.ratioOn
  congr 1
  congr 1
  exact pow_one _

theorem genericPoint_mem_nonzeroLocus : ∀ (m : ℕ) (n : Fin (m + 1) → ℕ) (Z : Scheme.{0}) [IsIntegral Z] (f : Z ⟶ MP ℤ m n) [IsClosedImmersion f] (k : Fin (m + 1)) (l : Bk n k), (X ⟨k, l⟩ : Pol n) ∉ ptIdeal (f (genericPoint Z)) → genericPoint Z ∈ Out.nonzeroLocus (pullFormSec (f ≫ prB n k) (X l) (isHomogeneous_X ℤ l)) := by
  intro m n Z _ f _ k l hX
  have hxj := GlobalTheory.CompanionTheory.MPDict.mem_ptChart (f (genericPoint Z)) k
  have hne : GlobalTheory.CompanionTheory.MPDict.ptCoord (f (genericPoint Z)) ⟨k, l⟩ ≠ 0 := by
    intro h0
    apply hX
    show (MvPolynomial.X ⟨k, l⟩ : Pol n) ∈
      RingHom.ker (ReciprocityTheory.ChartRestriction.G.Geo.mConeMap (GlobalTheory.CompanionTheory.MPDict.ptCoord (f (genericPoint Z))))
    rw [RingHom.mem_ker]
    simp [ReciprocityTheory.ChartRestriction.G.Geo.mConeMap, h0]
  let j : (pullO (f ≫ prB n k) 1).ι := (GlobalTheory.CompanionTheory.MPDict.ptChart (f (genericPoint Z)) k : Fin (n k + 1))
  have hξ : genericPoint Z ∈ (pullO (f ≫ prB n k) 1).U j := hxj
  apply GlobalTheory.basicOpen_le_nonzeroLocus _ j
  refine (Scheme.evaluation_ne_zero_iff_mem_basicOpen Z (genericPoint Z) hξ _).mp ?_
  dsimp only [GlobalTheory.ProjBlowup.pullFormSec]
  have hle : (pullO (f ≫ prB n k) 1).U j ≤
      (Opens.map (f ≫ prB n k).base).obj (GlobalTheory.ProjSpace.chart ℤ (n k) (GlobalTheory.CompanionTheory.MPDict.ptChart (f (genericPoint Z)) k)) :=
    le_rfl
  have e := pullForm_X_eq_pullRatio (f ≫ prB n k) ((pullO (f ≫ prB n k) 1).U j)
    (GlobalTheory.CompanionTheory.MPDict.ptChart (f (genericPoint Z)) k) hle l (isHomogeneous_X ℤ l)
  have key := GlobalTheory.CompanionTheory.MPDict.FnDeg.eval_pullRatio_comp f (prB n k) (genericPoint Z)
    (GlobalTheory.CompanionTheory.MPDict.ptChart (f (genericPoint Z)) k) hxj l
  have h2 : (CommRingCat.Hom.hom (Scheme.Hom.residueFieldMap f (genericPoint Z)))
      (GlobalTheory.CompanionTheory.MPDict.ptCoord (f (genericPoint Z)) ⟨k, l⟩) ≠ 0 := (map_ne_zero _).mpr hne
  convert h2 using 1
  refine Eq.trans ?_ key.symm
  exact congrArg (ConcreteCategory.hom (Z.evaluation _ (genericPoint Z) hξ)) e

end GlobalTheory.CompanionTheory.MixZ.VertGen
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermRepClassDecomposition
section
set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry Limits TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.ProjSpace GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt
open GroundTheory.Arith.SchemeCoh GroundTheory.Arith.SchemeCoh.ProjSpace
open ReciprocityTheory.ChartRestriction.G.Geo (MRing IsMultiHomog IsRelevant IsMultiProjPrime divSupp multAt geoNum charOf)
open GlobalTheory.CompanionTheory.MPDict GlobalTheory.CompanionTheory.MixZ GlobalTheory GlobalTheory.ProjBlowup

namespace GlobalTheory.CompanionTheory.MPDict.ClsRep

open GlobalTheory.CompanionTheory.MPDict.IsomT GlobalTheory.CompanionTheory.MPDict.TensRep

variable {m : ℕ} {n : Fin (m + 1) → ℕ}

def HasFrame (L : LB (MP ℤ m n)) (a : Fin (m + 1) → ℤ) : Prop :=
  ∃ u : ∀ (i : L.ι) (c : ∀ k, Bk n k), Γ(MP ℤ m n, L.U i ⊓ mchart c)ˣ,
    (∀ i j c,
      Semi.res (le_inf (inf_le_left.trans inf_le_right) inf_le_right :
          L.U i ⊓ L.U j ⊓ mchart c ≤ L.U j ⊓ mchart c) (u j c) =
        Semi.res (inf_le_left : L.U i ⊓ L.U j ⊓ mchart c ≤ L.U i ⊓ L.U j) (L.g i j) *
          Semi.res (le_inf (inf_le_left.trans inf_le_left) inf_le_right :
            L.U i ⊓ L.U j ⊓ mchart c ≤ L.U i ⊓ mchart c) (u i c)) ∧
    (∀ i c c',
      Semi.res (le_inf inf_le_left (inf_le_right.trans inf_le_left) :
          L.U i ⊓ (mchart c ⊓ mchart c') ≤ L.U i ⊓ mchart c) (u i c) =
        Semi.res (le_inf inf_le_left (inf_le_right.trans inf_le_right) :
          L.U i ⊓ (mchart c ⊓ mchart c') ≤ L.U i ⊓ mchart c') (u i c') *
        ∏ k, blockUnit (c k) (c' k) (fun _ hx =>
          ⟨mchart_le c k hx.2.1, mchart_le c' k hx.2.2⟩ :
            L.U i ⊓ (mchart c ⊓ mchart c') ≤ prB n k ⁻¹ᵁ (chart ℤ (n k) (c k) ⊓ chart ℤ (n k) (c' k))) ^ a k)

theorem hasFrame_of_isHermRep {M : HermLB (mpStr ℤ m n)} {A : Geo.HermLine (Bk n)} (h : IsHermRep M A) :
    HasFrame M.B A.a := by
  obtain ⟨u, h₁, h₂, -⟩ := h
  exact ⟨u, h₁, h₂⟩

theorem iSup_mchart : ⨆ c : (∀ k, Bk n k), mchart c = (⊤ : (MP ℤ m n).Opens) := by
  refine top_le_iff.1 fun x _ => Opens.mem_iSup.2 ⟨fun k => ptChart x k, ?_⟩
  exact Set.mem_iInter.2 fun k => mem_ptChart x k

theorem cg₃ {G : Type*} [CommGroup G] {x x' y y' P : G} (h : x = x' * P) (h' : y = y' * P) :
    x * y⁻¹ = x' * y'⁻¹ := by
  subst h h'
  rw [mul_inv, mul_mul_mul_comm, mul_inv_cancel, mul_one]

theorem cg₄ {G : Type*} [CommGroup G] {x x' y y' g g' : G} (h : x' = g' * x) (h' : y' = g * y) :
    x * y⁻¹ = g * g'⁻¹ * (x' * y'⁻¹) := by
  subst h h'
  simp only [mul_inv]
  rw [show g * g'⁻¹ * (g' * x * (g⁻¹ * y⁻¹)) = (g * g⁻¹) * (g'⁻¹ * g') * (x * y⁻¹) by ac_rfl]
  simp

theorem lbIso_of_hasFrame {L N : LB (MP ℤ m n)} {a : Fin (m + 1) → ℤ} (hL : HasFrame L a) (hN : HasFrame N a) :
    LBIso L N := by
  obtain ⟨u, u₁, u₂⟩ := hL
  obtain ⟨v, v₁, v₂⟩ := hN
  have hglue (p : N.ι × L.ι) : ∃ t : Γ(MP ℤ m n, N.U p.1 ⊓ L.U p.2)ˣ, ∀ c,
      Semi.res inf_le_left t =
        Semi.res (ofMem fun _ hx => ⟨hx.1.2, hx.2⟩ : (N.U p.1 ⊓ L.U p.2) ⊓ mchart c ≤ L.U p.2 ⊓ mchart c) (u p.2 c) *
        (Semi.res (ofMem fun _ hx => ⟨hx.1.1, hx.2⟩ : (N.U p.1 ⊓ L.U p.2) ⊓ mchart c ≤ N.U p.1 ⊓ mchart c) (v p.1 c))⁻¹ := by
    refine exists_glue mchart iSup_mchart _ _ fun c c' => ?_
    have e₁ := (congrArg (Semi.res (ofMem fun _ hx => ⟨hx.1.1.2, hx.1.2, hx.2.2⟩ :
      ((N.U p.1 ⊓ L.U p.2) ⊓ mchart c) ⊓ ((N.U p.1 ⊓ L.U p.2) ⊓ mchart c') ≤ L.U p.2 ⊓ (mchart c ⊓ mchart c'))) (u₂ p.2 c c')).trans
      (res_mul_prod c c' a _ _ _)
    have e₂ := (congrArg (Semi.res (ofMem fun _ hx => ⟨hx.1.1.1, hx.1.2, hx.2.2⟩ :
      ((N.U p.1 ⊓ L.U p.2) ⊓ mchart c) ⊓ ((N.U p.1 ⊓ L.U p.2) ⊓ mchart c') ≤ N.U p.1 ⊓ (mchart c ⊓ mchart c'))) (v₂ p.1 c c')).trans
      (res_mul_prod c c' a _ _ _)
    simp only [map_mul, map_inv, res_twice] at e₁ e₂ ⊢
    exact cg₃ e₁ e₂
  choose t ht using hglue
  have htT (p : N.ι × L.ι) (c : ∀ k, Bk n k) {T : (MP ℤ m n).Opens} (hT : T ≤ (N.U p.1 ⊓ L.U p.2) ⊓ mchart c) :
      Semi.res (hT.trans inf_le_left) (t p) =
        Semi.res (ofMem fun _ hx => ⟨(hT hx).1.2, (hT hx).2⟩ : T ≤ L.U p.2 ⊓ mchart c) (u p.2 c) *
        (Semi.res (ofMem fun _ hx => ⟨(hT hx).1.1, (hT hx).2⟩ : T ≤ N.U p.1 ⊓ mchart c) (v p.1 c))⁻¹ := by
    have e := congrArg (Semi.res hT) (ht p c)
    simpa only [map_mul, map_inv, res_twice] using e
  refine ⟨⟨t⟩, fun (p q : N.ι × L.ι) => units_ext_cover mchart iSup_mchart fun c => ?_⟩
  change Semi.res (inf_le_left : (N.U p.1 ⊓ L.U p.2) ⊓ (N.U q.1 ⊓ L.U q.2) ⊓ mchart c ≤ (N.U p.1 ⊓ L.U p.2) ⊓ (N.U q.1 ⊓ L.U q.2))
      (Semi.res (inf_le_left : (N.U p.1 ⊓ L.U p.2) ⊓ (N.U q.1 ⊓ L.U q.2) ≤ N.U p.1 ⊓ L.U p.2) (t p)) =
    Semi.res (inf_le_left : (N.U p.1 ⊓ L.U p.2) ⊓ (N.U q.1 ⊓ L.U q.2) ⊓ mchart c ≤ (N.U p.1 ⊓ L.U p.2) ⊓ (N.U q.1 ⊓ L.U q.2))
      ((Semi.res (le_inf (inf_le_left.trans inf_le_left) (inf_le_right.trans inf_le_left) :
          (N.U p.1 ⊓ L.U p.2) ⊓ (N.U q.1 ⊓ L.U q.2) ≤ N.U p.1 ⊓ N.U q.1) (N.g p.1 q.1) *
        (Semi.res (le_inf (inf_le_left.trans inf_le_right) (inf_le_right.trans inf_le_right) :
          (N.U p.1 ⊓ L.U p.2) ⊓ (N.U q.1 ⊓ L.U q.2) ≤ L.U p.2 ⊓ L.U q.2) (L.g p.2 q.2))⁻¹) *
        Semi.res (inf_le_right : (N.U p.1 ⊓ L.U p.2) ⊓ (N.U q.1 ⊓ L.U q.2) ≤ N.U q.1 ⊓ L.U q.2) (t q))
  simp only [map_mul, map_inv, res_twice]
  rw [htT p c (T := (N.U p.1 ⊓ L.U p.2) ⊓ (N.U q.1 ⊓ L.U q.2) ⊓ mchart c) (ofMem fun _ hx => ⟨hx.1.1, hx.2⟩),
    htT q c (T := (N.U p.1 ⊓ L.U p.2) ⊓ (N.U q.1 ⊓ L.U q.2) ⊓ mchart c) (ofMem fun _ hx => ⟨hx.1.2, hx.2⟩)]
  have hU : (N.U p.1 ⊓ L.U p.2) ⊓ (N.U q.1 ⊓ L.U q.2) ⊓ mchart c ≤ L.U p.2 ⊓ L.U q.2 ⊓ mchart c :=
    ofMem fun _ hx => ⟨⟨hx.1.1.2, hx.1.2.2⟩, hx.2⟩
  have hV : (N.U p.1 ⊓ L.U p.2) ⊓ (N.U q.1 ⊓ L.U q.2) ⊓ mchart c ≤ N.U p.1 ⊓ N.U q.1 ⊓ mchart c :=
    ofMem fun _ hx => ⟨⟨hx.1.1.1, hx.1.2.1⟩, hx.2⟩
  have e₁ := congrArg (Semi.res hU) (u₁ p.2 q.2 c)
  have e₂ := congrArg (Semi.res hV) (v₁ p.1 q.1 c)
  simp only [map_mul, res_twice] at e₁ e₂
  exact cg₄ e₁ e₂

theorem hasFrame_tens {L N : LB (MP ℤ m n)} {a b : Fin (m + 1) → ℤ} (hL : HasFrame L a) (hN : HasFrame N b) :
    HasFrame (GlobalTheory.CechPic.tens L N) (a + b) := by
  obtain ⟨u, hu₁, hu₂⟩ := hL
  obtain ⟨v, hv₁, hv₂⟩ := hN
  refine ⟨fun p c => mulUnit (u p.1 c) (v p.2 c), ?_, ?_⟩
  · rintro ⟨i, i'⟩ ⟨j, j'⟩ c
    exact frame_mulUnit _ _ _ _ _ _ _ _ _ _ _ _ (hu₁ i j c) (hv₁ i' j' c) _ _ _ _ _
  · rintro ⟨i, i'⟩ c c'
    exact mono_mulUnit a b _ _ _ _ _ _ _ _ _ _ (hu₂ i c c') (hv₂ i' c c') _ _ _

theorem hasFrame_dual {L : LB (MP ℤ m n)} {a : Fin (m + 1) → ℤ} (hL : HasFrame L a) :
    HasFrame (GlobalTheory.CechPic.dual L) (-a) := by
  obtain ⟨u, h1, h2⟩ := hL
  refine ⟨fun i c => (u i c)⁻¹, ?_, ?_⟩
  · intro i j c
    have e := h1 i j c
    change Semi.res _ (u j c)⁻¹ = Semi.res _ (L.g i j)⁻¹ * Semi.res _ (u i c)⁻¹
    rw [map_inv, map_inv, map_inv]
    exact (congrArg (·⁻¹) e).trans (mul_inv _ _)
  · intro i c c'
    have e := h2 i c c'
    change Semi.res _ (u i c)⁻¹ = Semi.res _ (u i c')⁻¹ * ∏ k, blockUnit (c k) (c' k) _ ^ (-a k)
    simp only [zpow_neg, Finset.prod_inv_distrib, map_inv]
    exact (congrArg (·⁻¹) e).trans (mul_inv _ _)

theorem hasFrame_triv : HasFrame (LB.triv (MP ℤ m n)) 0 := by
  refine ⟨fun _ _ => 1, ?_, ?_⟩
  · intro i j c
    simp only [map_one, mul_one]
  · intro i c c'
    simp

theorem res_pullO_g (k : Fin (m + 1)) (i j : Bk n k) {V : (MP ℤ m n).Opens}
    (h : V ≤ (pullO (prB n k) 1).U i ⊓ (pullO (prB n k) 1).U j) :
    Semi.res h ((pullO (prB n k) 1).g i j) = blockUnit i j h := by
  refine Units.ext ((val_res_pullO_g (prB n k) 1 i j h).trans ?_)
  rw [pow_one]
  exact (GlobalTheory.CompanionTheory.MPDict.Inhab.val_blockUnit i j h).symm

theorem hasFrame_pullO (k : Fin (m + 1)) : HasFrame (pullO (prB n k) 1) (Pi.single k 1) := by
  refine ⟨fun i c => blockUnit (c k) i (le_inf (inf_le_right.trans (mchart_le c k)) inf_le_left), ?_, ?_⟩
  · intro i j c
    refine (GlobalTheory.CompanionTheory.MPDict.res_blockUnit _ _ _ _).trans (Eq.trans ?_
      (congrArg₂ (· * ·) (res_pullO_g k i j _) (GlobalTheory.CompanionTheory.MPDict.res_blockUnit _ _ _ _)).symm)
    rw [mul_comm]
    exact (GlobalTheory.CompanionTheory.MPDict.Inhab.blockUnit_mul _ _ _ _ _ _).symm
  · intro i c c'
    refine (GlobalTheory.CompanionTheory.MPDict.res_blockUnit _ _ _ _).trans (Eq.trans ?_
      (congrArg₂ (· * ·) (GlobalTheory.CompanionTheory.MPDict.res_blockUnit _ _ _ _)
        (GlobalTheory.CompanionTheory.MPDict.Inhab.prod_blockUnit_single k c c' _)).symm)
    rw [mul_comm]
    exact (GlobalTheory.CompanionTheory.MPDict.Inhab.blockUnit_mul _ _ _ _ _ _).symm

theorem exists_hasFrame_cls (a : Fin (m + 1) → ℤ) : ∃ (L : LB (MP ℤ m n)) (hL : L.IsLB), HasFrame L a ∧
    cls L hL = ∑ k, a k • cls (pullO (prB n k) 1) (isLB_pullO _ 1) := by
  classical
  let H : AddSubgroup (Fin (m + 1) → ℤ) :=
    { carrier := {a | ∃ (L : LB (MP ℤ m n)) (hL : L.IsLB), HasFrame L a ∧
        cls L hL = ∑ k, a k • cls (pullO (prB n k) 1) (isLB_pullO _ 1)}
      add_mem' := by
        rintro a b ⟨L, hL, fL, eL⟩ ⟨N, hN, fN, eN⟩
        refine ⟨_, isLB_tens hL hN, hasFrame_tens fL fN, ?_⟩
        rw [cls_tens hL hN, eL, eN, ← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun k _ => (add_smul _ _ _).symm
      zero_mem' := ⟨_, LB.isLB_triv _, hasFrame_triv, by simp; rfl⟩
      neg_mem' := by
        rintro a ⟨L, hL, fL, eL⟩
        refine ⟨_, isLB_dual hL, hasFrame_dual fL, ?_⟩
        rw [cls_dual hL, eL, ← Finset.sum_neg_distrib]
        exact Finset.sum_congr rfl fun k _ => (neg_smul _ _).symm }
  have hs (k : Fin (m + 1)) : (Pi.single k 1 : Fin (m + 1) → ℤ) ∈ H := by
    refine ⟨_, isLB_pullO _ 1, hasFrame_pullO k, ?_⟩
    rw [Finset.sum_eq_single k (fun b _ hb => by rw [Pi.single_eq_of_ne hb, zero_smul]) (by simp),
      Pi.single_eq_same, one_smul]
  have e : a = ∑ k, a k • (Pi.single k 1 : Fin (m + 1) → ℤ) := by
    ext i
    simp [Finset.sum_apply, Pi.single_apply]
  have : a ∈ H := e ▸ H.sum_mem fun k _ => H.zsmul_mem (hs k) _
  exact this

end GlobalTheory.CompanionTheory.MPDict.ClsRep

theorem GlobalTheory.CompanionTheory.MPDict.ClsRep.cls_eq_of_isHermRep : ∀ (m : ℕ) (n : Fin (m + 1) → ℕ) (M : HermLB (mpStr ℤ m n)) (A : Geo.HermLine (Bk n)), IsHermRep M A → cls M.B M.isLB = ∑ k, A.a k • cls (pullO (prB n k) 1) (isLB_pullO _ 1) := by
  intro m n M A h
  obtain ⟨L, hL, fL, eL⟩ := GlobalTheory.CompanionTheory.MPDict.ClsRep.exists_hasFrame_cls (m := m) (n := n) A.a
  exact ((cls_eq_iff M.isLB hL).2 (GlobalTheory.CompanionTheory.MPDict.ClsRep.lbIso_of_hasFrame
    (GlobalTheory.CompanionTheory.MPDict.ClsRep.hasFrame_of_isHermRep h) fL)).trans eL
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MatchLeviWordsOfStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.match_levi_words_of : PositivityTheory.Rg.BcB.F.MLM.MatchLMWordSOf := by
  first | exact @GlobalTheory.CompanionTheory.LeviMatchingWords.matchLMWordSOf | exact GlobalTheory.CompanionTheory.LeviMatchingWords.matchLMWordSOf | (intros; apply GlobalTheory.CompanionTheory.LeviMatchingWords.matchLMWordSOf <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.O1ClassPullbackNaturality
section
set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry Limits TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.ProjSpace GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt
open GroundTheory.Arith.SchemeCoh GroundTheory.Arith.SchemeCoh.ProjSpace
open ReciprocityTheory.ChartRestriction.G.Geo (MRing IsMultiHomog IsRelevant IsMultiProjPrime divSupp multAt geoNum charOf)
open GlobalTheory.CompanionTheory.MPDict GlobalTheory.CompanionTheory.MixZ GlobalTheory GlobalTheory.ProjBlowup

namespace GlobalTheory.CompanionTheory.MixZ

def chartPullPullO {R : Type} [CommRing R] {N : ℕ} {S T : Scheme.{0}} (r : T ⟶ S) (φ : S ⟶ PSpace R N) :
    ChartPull (pullO (r ≫ φ) 1) (pullO φ 1) r where
  idx i := i
  le _ _ h := h
  g y i j hi hj := by
    have hle : (pullO (r ≫ φ) 1).U i ⊓ (pullO (r ≫ φ) 1).U j ≤
        r ⁻¹ᵁ ((pullO φ 1).U i ⊓ (pullO φ 1).U j) := fun _ h => h
    have hm : r y ∈ (pullO φ 1).U i ⊓ (pullO φ 1).U j := ⟨hi, hj⟩
    have ev : (((pullO φ 1).g i j : Γ(S, (pullO φ 1).U i ⊓ (pullO φ 1).U j)ˣ) :
        Γ(S, (pullO φ 1).U i ⊓ (pullO φ 1).U j)) = pullRatio φ _ i inf_le_left j :=
      (Units.val_pow_eq_pow_val _ _).trans (pow_one _)
    have ev' : (((pullO (r ≫ φ) 1).g i j : Γ(T, (pullO (r ≫ φ) 1).U i ⊓ (pullO (r ≫ φ) 1).U j)ˣ) :
        Γ(T, (pullO (r ≫ φ) 1).U i ⊓ (pullO (r ≫ φ) 1).U j)) = pullRatio (r ≫ φ) _ i inf_le_left j :=
      (Units.val_pow_eq_pow_val _ _).trans (pow_one _)
    have e : (pullO (r ≫ φ) 1).g i j = res hle (pullU r _ ((pullO φ 1).g i j)) := by
      apply Units.ext
      refine ev'.trans (Eq.trans ?_ (congrArg (r.appLE _ _ hle).hom ev).symm)
      exact (appLE_pullRatio (hi := inf_le_left) r hle).symm
    rw [e, gm_res (𝟙 T) y hle ⟨hi, hj⟩, gm_pull (𝟙 T) r y _ hm, Category.id_comp]

theorem cls_pullO_comp {R : Type} [CommRing R] {N : ℕ} {S T : Scheme.{0}} (r : T ⟶ S) (φ : S ⟶ PSpace R N) :
    cls (pullO (r ≫ φ) 1) (isLB_pullO _ 1) = CechPic.pull r (cls (pullO φ 1) (isLB_pullO _ 1)) := by
  rw [← cls_pull (isLB_pullO φ 1) r (pull_isLB (isLB_pullO φ 1) r)]
  exact (cls_eq_iff _ _).2 (LBIso.chartPull (chartPullPullO r φ)
    (chartPullPull (pullO φ 1) r) (PolBaseChange.lbIso_refl (isLB_pullO φ 1)))

end GlobalTheory.CompanionTheory.MixZ
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RegularPowerTorusStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.regular_power_torus : PositivityTheory.Rg.BcB.F.MLM.RegPowT := by
  first | exact @GlobalTheory.CompanionTheory.RegPow.regPowT | exact GlobalTheory.CompanionTheory.RegPow.regPowT | (intros; apply GlobalTheory.CompanionTheory.RegPow.regPowT <;> assumption)
end

