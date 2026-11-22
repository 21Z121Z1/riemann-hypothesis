import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TateUnramifiedOfTorsionUnramified
import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1621
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsPositiveDefiniteQuadraticFormEndomorphisms
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsAbelianSchemeAndExtendOfGenericHoms
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1596
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1610
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1682
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0139
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3043
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0179
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0077
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2665
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3064
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemberBaseChangeInjectiveLocalCompleteNormal
import Development.AbelianVarietyTheory.Definitions.Divisors.IsActIffIsDiagEnd
import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle0001
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.ImmersedBy
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2870
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3081
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0009
import Development.AbelianVarietyTheory.Definitions.Divisors.CovolXOfCovol
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
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3080
import Development.AbelianVarietyTheory.Definitions.Divisors.IsAmbOfIsArithVar
import Development.AbelianVarietyTheory.Definitions.Divisors.DensConst
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0049
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0005
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2950
import ReciprocityTheory.AnalyticForms.PotentialTheory.ProjectiveLineFubiniStudyFacts
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3082

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinearIndependentNumberFieldEndomorphismsTateMod
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.CMFaithful

theorem linearIndependent_actTate : ∀ (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω] [IsSepClosure K Ω] (A : Over (Sp K)) [GrpObj A] [IsCommMonObj A], IsAbelianScheme A → (∃ d : ℕ, 0 < d ∧ SmoothOfRelativeDimension d A.hom) → ∀ (F : Type) [Field F] [NumberField F] (O : Type) [CommRing O] [Algebra O F] [IsFractionRing O F] (α : OAct O A) (l : ℕ) [Fact l.Prime], (l : K) ≠ 0 → ∀ (n : ℕ) (a : Fin n → O), LinearIndependent ℚ (fun i => algebraMap O F (a i)) → LinearIndependent ℤ_[l] (fun i => actTate α.toRingAct l (ptOver K Ω) (a i)) := by
  intro K Ω _ _ _ _ A _ _ hA hd F _ _ O _ _ _ α l _ hl n a ha
  obtain ⟨d, hd0, hdim⟩ := hd
  haveI : IsSepClosed Ω := IsSepClosure.sep_closed K
  let t := spMap (algebraMap K (AlgebraicClosure Ω))
  let B := (Over.pullback t).obj A
  let β := OAct.pullback t A α
  have hB : IsAbelianScheme B := GlobalTheory.isAbelianScheme_pullback_obj t A hA
  haveI : IsCommMonObj B := hB.comm
  obtain ⟨L, hL⟩ := GlobalTheory.T.exists_symmetric_ample_cubical_lineBundle_abelianVariety (AlgebraicClosure Ω) B hB
  obtain ⟨Q, hQ1, hQ2, hQ3, -⟩ := GlobalTheory.SS.exists_quadraticForm_end (AlgebraicClosure Ω) B hB L hL
  let ψ : O →+ Additive (B ⟶ B) := AddMonoidHom.mk' (fun x => Additive.ofMul (β.act x))
    (fun x y => by rw [β.add]; rfl)
  let H : AddSubgroup (Additive (B ⟶ B)) :=
    { carrier := {f | IsMonHom (Additive.toMul f)}
      add_mem' := fun {f g} hf hg => by
        change IsMonHom (Additive.toMul f * Additive.toMul g)
        haveI : IsMonHom (Additive.toMul f) := hf
        haveI : IsMonHom (Additive.toMul g) := hg
        rw [Hom.mul_def]; infer_instance
      zero_mem' := by
        change IsMonHom (1 : B ⟶ B)
        rw [Hom.one_def]; infer_instance
      neg_mem' := fun {f} hf => by
        change IsMonHom (Additive.toMul f)⁻¹
        haveI : IsMonHom (Additive.toMul f) := hf
        infer_instance }
  have hu : ∀ i, ψ (a i) ∈ H := fun i => β.hom (a i)
  have hinj : Function.Injective ψ := (injective_iff_map_eq_zero ψ).2 fun x hx =>
    GlobalTheory.T.eq_zero_of_acts_trivially_abelianVariety_algClosure K Ω A hA ⟨d, hd0, hdim⟩ l hl F O α x (by
      have : Additive.toMul (ψ x) = Additive.toMul 0 := congrArg _ hx
      exact this)
  have hindep : LinearIndependent ℤ (fun i => ψ (a i)) := by
    have h1 : LinearIndependent ℤ (fun i => algebraMap O F (a i)) := ha.restrict_scalars' ℤ
    have h2 : LinearIndependent ℤ a := by
      refine LinearIndependent.of_comp (algebraMap O F).toAddMonoidHom.toIntLinearMap ?_
      exact h1
    exact h2.map' ψ.toIntLinearMap (LinearMap.ker_eq_bot.2 hinj)
  obtain ⟨e, he, hE⟩ := GlobalTheory.T.exists_dvd_coords_of_definite_parallelogram_form (Additive (B ⟶ B)) H (fun f => Q (Additive.toMul f))
    (fun f g => by
      have := hQ1 (Additive.toMul f) (Additive.toMul g)
      simpa [div_eq_mul_inv] using this)
    (fun f => hQ2 _) (fun f hf h0 => by
      have := hQ3 (Additive.toMul f) hf h0
      exact this) n (fun i => ψ (a i)) hu hindep
  rw [Fintype.linearIndependent_iff]
  intro c hc
  by_contra hne
  push_neg at hne
  obtain ⟨j, hj⟩ := hne
  obtain ⟨N, hN⟩ := GlobalTheory.T.padicInt_exists_level_not_dvd_mul_lift l (c j) hj e he
  haveI : NeZero (l ^ N) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
  let m : Fin n → ℤ := fun i => ((PadicInt.toZModPow N (c i)).val : ℤ)
  have hm : ∀ i, PadicInt.toZModPow N (c i) = (m i : ZMod (l ^ N)) := fun i => by
    simp [m]
  let φ : Fin n → ((ptOver K Ω ⟶ A) →* (ptOver K Ω ⟶ A)) := fun i => actPts α.toRingAct (ptOver K Ω) (a i)
  have kill := GlobalTheory.T.prod_endomorphism_pow_levelComponent_eq_one_of_relation (ptOver K Ω ⟶ A) l n φ c hc N m hm
  let x : O := ∑ i, m i • a i
  have hcomp : ∀ y : ptOver K Ω ⟶ A, y ≫ α.act x = ∏ i, (y ≫ α.act (a i)) ^ m i := by
    intro y
    let χ : O →+ Additive (ptOver K Ω ⟶ A) := AddMonoidHom.mk' (fun z => Additive.ofMul (y ≫ α.act z))
      (fun z w => by rw [α.add, MonObj.comp_mul]; rfl)
    have e1 : χ x = ∑ i, m i • χ (a i) := by simp only [x, map_sum, map_zsmul]
    have e2 := congrArg Additive.toMul e1
    rw [toMul_sum] at e2
    simp only [toMul_zsmul] at e2
    exact e2
  have hcard : ∀ k : ℕ, Nat.card {y : ptOver K Ω ⟶ A // y ^ (l ^ k) = 1} = l ^ (2 * d * k) := fun k => by
    rw [GlobalTheory.T.card_abelianVariety_torsion_sepClosed K Ω A hA d hdim (l ^ k) (by rw [Nat.cast_pow]; exact pow_ne_zero _ hl), ← pow_mul, mul_comm k]
  have hx : ∀ y : ptOver K Ω ⟶ A, y ^ (l ^ N) = 1 → y ≫ α.act x = 1 := by
    intro y hy
    obtain ⟨tt, rfl⟩ := GlobalTheory.T.exists_tateModule_levelComponent_eq_of_card_torsion (ptOver K Ω ⟶ A) l (2 * d) hcard N y hy
    rw [hcomp, ← kill tt]
    rfl
  obtain ⟨h, hh, hfh⟩ := GlobalTheory.T.divisible_algClosure_of_kills_torsion_sepClosed K Ω A hA (l ^ N) (by rw [Nat.cast_pow]; exact pow_ne_zero _ hl) (α.act x) (α.hom x) hx
  have hsum : (l ^ N) • Additive.ofMul h = ∑ i, m i • ψ (a i) := by
    rw [← ofMul_pow, ← hfh]
    change ψ x = _
    simp only [x, map_sum, map_zsmul]
  have := hE (l ^ N) m (Additive.ofMul h) hh hsum j
  exact hN (m j) (hm j) (by exact_mod_cast this)

end GlobalTheory.CMFaithful
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemBasicOpenOfSectionRatioEqBasePoint
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem thick_apply_eq_closedPoint {R : Type} [CommRing R] [IsLocalRing R] (e : ℕ)
    (p : Spec (CommRingCat.of (R ⧸ maximalIdeal R ^ (e + 1)))) :
    thick R (maximalIdeal R) e p = closedPoint R := by
  haveI : p.asIdeal.IsPrime := p.isPrime
  apply PrimeSpectrum.ext
  show Ideal.comap (Ideal.Quotient.mk (maximalIdeal R ^ (e + 1))) p.asIdeal = maximalIdeal R
  have hle : maximalIdeal R ^ (e + 1) ≤ Ideal.comap (Ideal.Quotient.mk (maximalIdeal R ^ (e + 1))) p.asIdeal := by
    intro a ha
    simp [Ideal.Quotient.eq_zero_iff_mem.2 ha]
  have hm : maximalIdeal R ≤ Ideal.comap (Ideal.Quotient.mk (maximalIdeal R ^ (e + 1))) p.asIdeal :=
    (Ideal.IsPrime.comap _).le_of_pow_le hle
  exact ((maximalIdeal.isMaximal R).eq_of_le (Ideal.IsPrime.comap _).ne_top hm).symm

theorem exists_thick_zero {R : Type} [CommRing R] [IsLocalRing R] (e : ℕ) (G : Over (Sp R))
    (y : (thickObj R (maximalIdeal R) e G).left) :
    ∃ y₀ : (thickObj R (maximalIdeal R) 0 G).left,
      (fstG (maximalIdeal R) 0 G).left y₀ = (fstG (maximalIdeal R) e G).left y := by
  have hne : maximalIdeal R ^ (0 + 1) ≠ ⊤ := by
    rw [zero_add, pow_one]; exact (maximalIdeal.isMaximal R).ne_top
  haveI : Nontrivial (R ⧸ maximalIdeal R ^ (0 + 1)) := Ideal.Quotient.nontrivial_iff.2 hne
  haveI : IsLocalRing (R ⧸ maximalIdeal R ^ (0 + 1)) :=
    IsLocalRing.of_surjective' _ Ideal.Quotient.mk_surjective
  have h1 : G.hom (pullback.fst G.hom (thick R (maximalIdeal R) e) y) = closedPoint R := by
    rw [← Scheme.Hom.comp_apply, pullback.condition, Scheme.Hom.comp_apply, thick_apply_eq_closedPoint]
  obtain ⟨z, hz, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := G.hom) (g := thick R (maximalIdeal R) 0)
    (pullback.fst G.hom (thick R (maximalIdeal R) e) y) (closedPoint _)
    (h1.trans (thick_apply_eq_closedPoint 0 _).symm)
  exact ⟨z, hz⟩

end GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem mem_basicOpen_of_secRatioEq : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ U : Unif (maximalIdeal R) D A G, ∀ (e k k' : ℕ), 3 ≤ k → ∀ (x : thickObj R (maximalIdeal R) e G ⟶ thickObj R (maximalIdeal R) e G) (T : H0 U.LG.L k → H0 U.LG.L k'), (∀ s₁ s₂ : H0 U.LG.L k, SecRatioEq U.LG.L (x.left ≫ (fstG (maximalIdeal R) e G).left) (fstG (maximalIdeal R) e G).left s₁ s₂ (T s₁) (T s₂)) → ∀ (y : (thickObj R (maximalIdeal R) e G).left) (s₀ : H0 U.LG.L k) (i' : Fin 1 → U.LG.L.ι), y ∈ (thickObj R (maximalIdeal R) e G).left.basicOpen (((fstG (maximalIdeal R) e G).left.app (secChart U.LG.L i')).hom ((T s₀).f i')) → ∃ i : Fin 1 → U.LG.L.ι, y ∈ (thickObj R (maximalIdeal R) e G).left.basicOpen ((((x).left ≫ (fstG (maximalIdeal R) e G).left).app (secChart U.LG.L i)).hom (s₀.f i)) := by
  intro R _ _ _ hB D A G _ _ hG U e k k' hk x T hT y s₀ i' hy
  obtain ⟨y₀, hy₀⟩ := exists_thick_zero e G (x.left y)
  obtain ⟨s₁, j, hs₁⟩ := GlobalTheory.T.exists_section_nonvanishing_closedFibre_of_three_le R hB D A G hG U k hk y₀
  refine ⟨j, ?_⟩
  have hs₁' : (fstG (maximalIdeal R) 0 G).left y₀ ∈ G.left.basicOpen (s₁.f j) :=
    (Scheme.preimage_basicOpen (fstG (maximalIdeal R) 0 G).left (s₁.f j)).ge hs₁
  have hu : y ∈ (thickObj R (maximalIdeal R) e G).left.basicOpen
      (((x.left ≫ (fstG (maximalIdeal R) e G).left).app (secChart U.LG.L j)).hom (s₁.f j)) := by
    refine (Scheme.preimage_basicOpen (x.left ≫ (fstG (maximalIdeal R) e G).left) (s₁.f j)).le ?_
    show (x.left ≫ (fstG (maximalIdeal R) e G).left) y ∈ G.left.basicOpen (s₁.f j)
    rw [Scheme.Hom.comp_apply, ← hy₀]
    exact hs₁'
  by_contra hn
  have hE := congrArg (thickObj R (maximalIdeal R) e G).left.basicOpen (hT s₁ s₀ j i')
  simp only [Scheme.basicOpen_mul, Scheme.basicOpen_res] at hE
  have hmem : y ∈ ((x.left ≫ (fstG (maximalIdeal R) e G).left) ⁻¹ᵁ secChart U.LG.L j ⊓
      (fstG (maximalIdeal R) e G).left ⁻¹ᵁ secChart U.LG.L i') := by
    rw [TopologicalSpace.Opens.mem_inf]
    exact ⟨Scheme.basicOpen_le _ _ hu, Scheme.basicOpen_le _ _ hy⟩
  have h2 := hE.le (by
    simp only [TopologicalSpace.Opens.mem_inf] at hmem ⊢
    exact ⟨⟨hmem, hu⟩, ⟨hmem, hy⟩⟩)
  simp only [TopologicalSpace.Opens.mem_inf] at h2
  exact hn h2.1.2

end GlobalTheory.Mum
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemberBaseChangeInjectiveLocalCompleteNormalStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.member_baseChange_injective_local_complete_normal : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (Z : Scheme.{0}) (i : F.X ⟶ Z) (X₁ : Setup F W i) (z₁ : X₁.M.Z) (act : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)), IsAct X₁ act → ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (ev : X₁.M.Z.presheaf.stalk z₁ →+* V) (X : Type) [AddCommGroup X] (m : ℕ) (t : Fin m → V) (δ : Fin m → LinearMap.BilinForm ℤ X) (𝔪 : UMem X₁ z₁ act V ev X t δ) (V' : Type) [CommRing V'] [IsDomain V'] [IsLocalRing V'] (j : V →+* V'), IsCN V' → Function.Injective j → IsLocalHom j → ∃ (m' : ℕ) (t' : Fin m' → V') (δ' : Fin m' → LinearMap.BilinForm ℤ X) (𝔫 : UMem X₁ z₁ act V' (j.comp ev) X t' δ'), ∀ a mu, 𝔪.YY a mu → 𝔫.YY a mu := by
  first | exact @GlobalTheory.Poinc.Sep.MemBC.uMem_baseChange | exact GlobalTheory.Poinc.Sep.MemBC.uMem_baseChange | (intros; apply GlobalTheory.Poinc.Sep.MemBC.uMem_baseChange <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MinimalGenusBoundStatement
section
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.minimal_genus_bound : Hypotheses2 → Gram → DeepGood → Size → Gmin := by
  first | exact @GlobalTheory.CovGminTop.gmin | exact GlobalTheory.CovGminTop.gmin | (intros; apply GlobalTheory.CovGminTop.gmin <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MixedArchLogNormIntegralIsometrySymmCongrStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.MixHt
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mixedArchLogNormIntegral_isometry_symm_congr : ∀ (k : Type) [CommRing k] (Y : Scheme.{0}) [IsIntegral Y] (q : Y ⟶ Sp k) (e : ℕ) (L : Fin e → HermLB q) (M : HermLB q) (r : M.B.ι → Y.functionFieldˣ) (hr : IsRatSec M.B r), (∀ L' : Fin e → HermLB q, (∀ a, (L a).Isometric (L' a)) → mixArch L M hr = mixArch L' M hr) ∧ (∀ τ : Equiv.Perm (Fin e), mixArch (fun a => L (τ a)) M hr = mixArch L M hr) ∧ ∀ (M' : HermLB q) (r' : M'.B.ι → Y.functionFieldˣ) (hr' : IsRatSec M'.B r'), M'.div hr' = M.div hr → (∀ σ, Set.EqOn (logNorm (M'.φ σ) r') (logNorm (M.φ σ) r) (offSupp q σ (M.div hr))) → mixArch L M' hr' = mixArch L M hr := by
  first | exact @GlobalTheory.MixHt.mixArch_iso_symm_congr | exact GlobalTheory.MixHt.mixArch_iso_symm_congr | (intros; apply GlobalTheory.MixHt.mixArch_iso_symm_congr <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MixedArchRestrictedEqZeroOfNoComplexPointsStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.MixHt
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mixedArch_restricted_eq_zero_of_no_complexPoints : ∀ (k : Type) [CommRing k] (Y : Scheme.{0}) [IsIntegral Y] (q : Y ⟶ Sp k), (∀ σ : k →+* ℂ, IsEmpty (CxPts q σ)) → ∀ (e : ℕ) (L : Fin e → HermLB q) (M : HermLB q), (∀ (r : M.B.ι → Y.functionFieldˣ) (hr : IsRatSec M.B r), mixArch L M hr = 0) ∧ ∀ (t : M.B.Sec) (z : Y), resArch L M t z = 0 := by
  first | exact @GlobalTheory.MixHt.mixArch_resArch_eq_zero_of_noCxPts | exact GlobalTheory.MixHt.mixArch_resArch_eq_zero_of_noCxPts | (intros; apply GlobalTheory.MixHt.mixArch_resArch_eq_zero_of_noCxPts <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MixedChernFormDensityChangeOfChartStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ChartGlue GlobalTheory.Mix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mixedChernFormDensity_change_of_chart : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k) (σ : k →+* ℂ) (D : ℕ) (L : Fin D → MLine p σ) (c c' : AlgChart p σ D) (y : CxPts p σ), y ∈ c.e.source → y ∈ c'.e.source → dens L c y = ‖transDet c.e c'.e y‖ ^ 2 * dens L c' y := by
  first | exact @GlobalTheory.Mix.ChartChange.dens_change_chart | exact GlobalTheory.Mix.ChartChange.dens_change_chart | (intros; apply GlobalTheory.Mix.ChartChange.dens_change_chart <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MixedChernFormDensityPullbackMatchingChartsStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ChartGlue GlobalTheory.Mix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mixedChernFormDensity_pullback_matching_charts : ∀ (k : Type) [CommRing k] (X Y : Scheme.{0}) (p : X ⟶ Sp k) (q : Y ⟶ Sp k) (σ : k →+* ℂ) (D : ℕ) (π : Y ⟶ X) (hπ : π ≫ p = q) (L : Fin D → MLine p σ) (c : AlgChart p σ D) (c' : AlgChart q σ D), (∀ w ∈ c'.e.source, ptMap π hπ σ w ∈ c.e.source ∧ c'.e w = c.e (ptMap π hπ σ w)) → ∀ w ∈ c'.e.source, dens (fun i => (L i).pull π hπ) c' w = dens L c (ptMap π hπ σ w) := by
  first | exact @GlobalTheory.MixPull.dens_pull | exact GlobalTheory.MixPull.dens_pull | (intros; apply GlobalTheory.MixPull.dens_pull <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MixedChernFormDensityUpdateTensorAddStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ChartGlue GlobalTheory.Mix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mixedChernFormDensity_update_tensor_add : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k) (σ : k →+* ℂ) (D : ℕ) (L : Fin D → MLine p σ) (i : Fin D) (A B : MLine p σ) (c : AlgChart p σ D), ∀ y ∈ c.e.source, dens (Function.update L i (A.tens B)) c y = dens (Function.update L i A) c y + dens (Function.update L i B) c y := by
  first | exact @GlobalTheory.Mix.dens_update_tens | exact GlobalTheory.Mix.dens_update_tens | (intros; apply GlobalTheory.Mix.dens_update_tens <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MixedChernFormSignedPartMeasureChartApplyStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ChartGlue GlobalTheory.Mix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mixedChernFormSignedPartMeasure_chart_apply : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k) (σ : k →+* ℂ) [SecondCountableTopology (CxPts p σ)] (D : ℕ) (L : Fin D → MLine p σ) (ε : ℤˣ) (c : AlgChart p σ D) (S : Set (CxPts p σ)), MeasurableSet S → S ⊆ c.e.source → part L ε S = ∫⁻ v in c.e '' S, ENNReal.ofReal ((ε : ℤ) * dens L c (c.e.symm v)) := by
  first | exact @GlobalTheory.Mix.part_apply | exact GlobalTheory.Mix.part_apply | (intros; apply GlobalTheory.Mix.part_apply <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MixedChernFormSignedPartMeasureComplOpenGenericPStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ChartGlue GlobalTheory.Mix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mixedChernFormSignedPartMeasure_compl_open_genericPoint_eq_zero : ∀ (k : Type) [CommRing k] [IsDomain k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (σ : k →+* ℂ), Function.Injective σ → IsProjOver p → ∀ (D : ℕ) (L : Fin D → MLine p σ) (ε : ℤˣ) (U : X.Opens), genericPoint X ∈ U → part L ε (ptsIn p σ U)ᶜ = 0 := by
  first | exact @GlobalTheory.MixNull.part_compl_null | exact GlobalTheory.MixNull.part_compl_null | (intros; apply GlobalTheory.MixNull.part_compl_null <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MixedChernFormSignedPartMeasureEqOfIsometricProjStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ChartGlue GlobalTheory.Mix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mixedChernFormSignedPartMeasure_eq_of_isometric_projOver : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k) (σ : k →+* ℂ), IsProjOver p → ∀ (D : ℕ) (L M : Fin D → MLine p σ), (∀ i, (L i).Isom (M i)) → ∀ ε : ℤˣ, part L ε = part M ε := by
  first | exact @GlobalTheory.Mix.part_eq_of_isom | exact GlobalTheory.Mix.part_eq_of_isom | (intros; apply GlobalTheory.Mix.part_eq_of_isom <;> assumption)
end

